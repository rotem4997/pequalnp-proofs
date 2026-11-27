import Mathlib.Tactic.Tauto
import Mathlib.Tactic.IntervalCases
import PEqualNP.Defs

-- Binary gate elimination from L-meta-244 (Apache-2.0).
namespace PEqualNP.Outside.L_meta_10930.Cut

open PEqualNP.MetaComplexity

def bWires (gs : List BinaryGate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op (w.getD g.left false) (w.getD g.right false)]) w

lemma bWires_nil (w : List Bool) : bWires [] w = w := rfl

lemma bWires_cons (g : BinaryGate) (gs : List BinaryGate) (w : List Bool) :
    bWires (g :: gs) w =
      bWires gs (w ++ [g.op (w.getD g.left false) (w.getD g.right false)]) := rfl

lemma bWires_append (gs₁ gs₂ : List BinaryGate) (w : List Bool) :
    bWires (gs₁ ++ gs₂) w = bWires gs₂ (bWires gs₁ w) := by
  induction gs₁ generalizing w with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, bWires_cons, ih]

lemma bWires_length (gs : List BinaryGate) (w : List Bool) :
    (bWires gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [bWires]
  | cons g gs ih =>
    rw [bWires_cons, ih]
    simp
    omega

lemma getD_snoc_lt {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

lemma getD_snoc_eq {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
    (l ++ [x]).getD i d = x := by
  subst hi
  simp [List.getD]

lemma getD_snoc_ne {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i ≠ l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  by_cases hlt : i < l.length
  · exact getD_snoc_lt l x d i hlt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma bWires_getD_lt (gs : List BinaryGate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (bWires gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [bWires_cons, ih _ (by simp; omega)]
    exact getD_snoc_lt _ _ _ _ hi

lemma ofFn_getD_lt {α : Type*} {m : ℕ} (f : Fin m → α) (d : α) (i : ℕ) (hi : i < m) :
    (List.ofFn f).getD i d = f ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simp; exact hi), List.getElem_ofFn]

abbrev Stat := Bool ⊕ (ℕ × Bool)

def statVal (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr (j, neg) => xor (w.getD j false) neg

def statValid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr (j, _) => j < m

def simplifyUnary (f : Bool → Bool) (j : ℕ) : Option BinaryGate × Stat :=
  if f false == f true then (none, Sum.inl (f false))
  else (none, Sum.inr (j, f false))

lemma simplifyUnary_none (f : Bool → Bool) (j : ℕ) : (simplifyUnary f j).1 = none := by
  unfold simplifyUnary; split_ifs <;> rfl

lemma simplifyUnary_sound (f : Bool → Bool) (w : List Bool) (j : ℕ) (hj : j < w.length) :
    statValid w.length (simplifyUnary f j).2 ∧
    statVal w (simplifyUnary f j).2 = f (w.getD j false) := by
  unfold simplifyUnary
  by_cases h : (f false == f true) = true
  · rw [if_pos h]
    have heq : f false = f true := beq_iff_eq.mp h
    refine ⟨trivial, ?_⟩
    simp only [statVal]
    cases hb : w.getD j false
    · rfl
    · exact heq
  · rw [if_neg h]
    have hne : f false ≠ f true := fun e => h (beq_iff_eq.mpr e)
    refine ⟨hj, ?_⟩
    simp only [statVal]
    cases hb : w.getD j false <;> cases hf0 : f false <;> cases hf1 : f true <;>
      simp_all

def simplifyBGate (op : Bool → Bool → Bool) (m : ℕ) (sL sR : Stat) :
    Option BinaryGate × Stat :=
  match sL, sR with
  | Sum.inl cL, Sum.inl cR => (none, Sum.inl (op cL cR))
  | Sum.inl cL, Sum.inr (j, negR) => simplifyUnary (fun b => op cL (xor b negR)) j
  | Sum.inr (i, negL), Sum.inl cR => simplifyUnary (fun a => op (xor a negL) cR) i
  | Sum.inr (i, negL), Sum.inr (j, negR) =>
    (some ⟨fun a b => op (xor a negL) (xor b negR), i, j⟩, Sum.inr (m, false))

lemma simplifyBGate_none_left (op : Bool → Bool → Bool) (m : ℕ) (c : Bool) (sR : Stat) :
    (simplifyBGate op m (Sum.inl c) sR).1 = none := by
  cases sR with
  | inl cR => rfl
  | inr p => exact simplifyUnary_none _ _

lemma simplifyBGate_none_right (op : Bool → Bool → Bool) (m : ℕ) (sL : Stat) (c : Bool) :
    (simplifyBGate op m sL (Sum.inl c)).1 = none := by
  cases sL with
  | inl cL => rfl
  | inr p => exact simplifyUnary_none _ _

lemma simplifyBGate_const_left (op : Bool → Bool → Bool) (m : ℕ) (c : Bool) (sR : Stat)
    (hconst : op c false = op c true) :
    simplifyBGate op m (Sum.inl c) sR = (none, Sum.inl (op c false)) := by
  cases sR with
  | inl cR =>
    cases cR
    · rfl
    · simp [simplifyBGate, hconst]
  | inr p =>
    obtain ⟨j, negR⟩ := p
    simp only [simplifyBGate, simplifyUnary]
    cases negR
    · simp [hconst]
    · simp [hconst]

lemma simplifyBGate_const_right (op : Bool → Bool → Bool) (m : ℕ) (sL : Stat) (c : Bool)
    (hconst : op false c = op true c) :
    simplifyBGate op m sL (Sum.inl c) = (none, Sum.inl (op false c)) := by
  cases sL with
  | inl cL =>
    cases cL
    · rfl
    · simp [simplifyBGate, hconst]
  | inr p =>
    obtain ⟨i, negL⟩ := p
    simp only [simplifyBGate, simplifyUnary]
    cases negL
    · simp [hconst]
    · simp [hconst]

lemma simplifyBGate_const_both (op : Bool → Bool → Bool) (m : ℕ) (cL cR : Bool) :
    simplifyBGate op m (Sum.inl cL) (Sum.inl cR) = (none, Sum.inl (op cL cR)) := rfl

lemma simplifyBGate_sound (op : Bool → Bool → Bool) (w : List Bool) (sL sR : Stat)
    (hL : statValid w.length sL) (hR : statValid w.length sR) :
    statValid (w.length + (simplifyBGate op w.length sL sR).1.toList.length)
      (simplifyBGate op w.length sL sR).2 ∧
    statVal (bWires (simplifyBGate op w.length sL sR).1.toList w)
      (simplifyBGate op w.length sL sR).2 = op (statVal w sL) (statVal w sR) := by
  cases sL with
  | inl cL =>
    cases sR with
    | inl cR =>
      simp [simplifyBGate, statValid, statVal]
    | inr pR =>
      obtain ⟨j, negR⟩ := pR
      have hu := simplifyUnary_sound (fun b => op cL (xor b negR)) w j hR
      simp only [simplifyBGate, simplifyUnary_none, Option.toList_none, List.length_nil,
        Nat.add_zero, bWires_nil, statVal]
      exact hu
  | inr pL =>
    obtain ⟨i, negL⟩ := pL
    cases sR with
    | inl cR =>
      have hu := simplifyUnary_sound (fun a => op (xor a negL) cR) w i hL
      simp only [simplifyBGate, simplifyUnary_none, Option.toList_none, List.length_nil,
        Nat.add_zero, bWires_nil, statVal]
      exact hu
    | inr pR =>
      obtain ⟨j, negR⟩ := pR
      simp only [simplifyBGate, Option.toList_some, List.length_singleton, statValid, statVal,
        bWires_cons, bWires_nil, getD_snoc_eq _ _ _ _ rfl, Bool.xor_false]
      exact ⟨by omega, trivial⟩

def elimStep (m : ℕ) (acc : List Stat × List BinaryGate) (g : BinaryGate) :
    List Stat × List BinaryGate :=
  let r := simplifyBGate g.op (m + acc.2.length)
    (acc.1.getD g.left (Sum.inl false)) (acc.1.getD g.right (Sum.inl false))
  (acc.1 ++ [r.2], acc.2 ++ r.1.toList)

def elimPass (m : ℕ) (gs : List BinaryGate) (acc : List Stat × List BinaryGate) :
    List Stat × List BinaryGate :=
  gs.foldl (elimStep m) acc

lemma elimPass_nil (m : ℕ) (acc : List Stat × List BinaryGate) :
    elimPass m [] acc = acc := rfl

lemma elimPass_cons (m : ℕ) (g : BinaryGate) (gs : List BinaryGate)
    (acc : List Stat × List BinaryGate) :
    elimPass m (g :: gs) acc = elimPass m gs (elimStep m acc g) := rfl

lemma elimPass_append (m : ℕ) (gs₁ gs₂ : List BinaryGate)
    (acc : List Stat × List BinaryGate) :
    elimPass m (gs₁ ++ gs₂) acc = elimPass m gs₂ (elimPass m gs₁ acc) := by
  induction gs₁ generalizing acc with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, elimPass_cons, ih]

lemma elimPass_fst_len (m : ℕ) (gs : List BinaryGate) (acc : List Stat × List BinaryGate) :
    (elimPass m gs acc).1.length = acc.1.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
    rw [elimPass_cons, ih]
    simp [elimStep]
    omega

lemma elimPass_getD_lt (m k : ℕ) (d : Stat) (gs : List BinaryGate)
    (acc : List Stat × List BinaryGate) (hk : k < acc.1.length) :
    (elimPass m gs acc).1.getD k d = acc.1.getD k d := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    rw [elimPass_cons, ih _ (by simp [elimStep]; omega)]
    exact getD_snoc_lt _ _ _ _ hk

lemma toList_opt_len_le {α : Type*} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

lemma elimPass_len (m : ℕ) (gs : List BinaryGate) (acc : List Stat × List BinaryGate) :
    (elimPass m gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
    rw [elimPass_cons, List.length_cons]
    have h1 := ih (elimStep m acc g)
    have h2 : (elimStep m acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_opt_len_le (simplifyBGate g.op (m + acc.2.length)
        (acc.1.getD g.left (Sum.inl false)) (acc.1.getD g.right (Sum.inl false))).1
      omega
    omega

def readsWire (k : ℕ) (g : BinaryGate) : Bool :=
  decide (g.left = k ∨ g.right = k)

lemma elimStep_none_of_reads (m k : ℕ) (acc : List Stat × List BinaryGate) (g : BinaryGate)
    (hc : ∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) (hr : readsWire k g = true) :
    (elimStep m acc g).2.length = acc.2.length := by
  obtain ⟨c, hc⟩ := hc
  simp only [readsWire, decide_eq_true_eq] at hr
  rcases hr with hl | hr
  · have hnone : (simplifyBGate g.op (m + acc.2.length)
        (acc.1.getD g.left (Sum.inl false)) (acc.1.getD g.right (Sum.inl false))).1 = none := by
      rw [hl, hc]; exact simplifyBGate_none_left _ _ _ _
    simp only [elimStep, hnone, Option.toList_none, List.append_nil]
  · have hnone : (simplifyBGate g.op (m + acc.2.length)
        (acc.1.getD g.left (Sum.inl false)) (acc.1.getD g.right (Sum.inl false))).1 = none := by
      rw [hr, hc]; exact simplifyBGate_none_right _ _ _ _
    simp only [elimStep, hnone, Option.toList_none, List.append_nil]

lemma elimPass_len_lt (m k : ℕ) (gs : List BinaryGate) (acc : List Stat × List BinaryGate)
    (hk : k < acc.1.length) (hc : ∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c)
    (hex : ∃ g ∈ gs, readsWire k g = true) :
    (elimPass m gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => obtain ⟨g, hg, _⟩ := hex; simp at hg
  | cons g gs ih =>
    rw [elimPass_cons, List.length_cons]
    by_cases hkg : readsWire k g = true
    · have h2 := elimStep_none_of_reads m k acc g hc hkg
      have := elimPass_len m gs (elimStep m acc g)
      omega
    · have hex' : ∃ g' ∈ gs, readsWire k g' = true := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep m acc g) (by simp [elimStep]; omega)
        (by obtain ⟨c, hc⟩ := hc; exact ⟨c, by simp only [elimStep]; rw [getD_snoc_lt _ _ _ _ hk]; exact hc⟩)
        hex'
      have h2 : (elimStep m acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_opt_len_le (simplifyBGate g.op (m + acc.2.length)
          (acc.1.getD g.left (Sum.inl false)) (acc.1.getD g.right (Sum.inl false))).1
        omega
      omega

lemma elimPass_len_two_pred (m : ℕ) (P : BinaryGate → Bool) (gs : List BinaryGate)
    (acc : List Stat × List BinaryGate)
    (hP : ∀ g ∈ gs, P g = true → ∀ acc' : List Stat × List BinaryGate,
      (∀ i < acc.1.length, acc'.1.getD i (Sum.inl false) = acc.1.getD i (Sum.inl false)) →
      (elimStep m acc' g).2.length = acc'.2.length)
    (htwo : 2 ≤ (gs.filter P).length) :
    (elimPass m gs acc).2.length + 2 ≤ acc.2.length + gs.length := by
  have h1 : ∀ (gs' : List BinaryGate) (acc' : List Stat × List BinaryGate),
      (∀ g ∈ gs', P g = true → ∀ acc'' : List Stat × List BinaryGate,
        (∀ i < acc'.1.length, acc''.1.getD i (Sum.inl false) = acc'.1.getD i (Sum.inl false)) →
        (elimStep m acc'' g).2.length = acc''.2.length) →
      1 ≤ (gs'.filter P).length →
      (elimPass m gs' acc').2.length + 1 ≤ acc'.2.length + gs'.length := by
    intro gs'
    induction gs' with
    | nil => intro acc' _ h; simp at h
    | cons g gs' ih =>
      intro acc' hP' hcnt
      rw [elimPass_cons, List.length_cons]
      cases hPg : P g with
      | true =>
        have hstep := hP' g List.mem_cons_self hPg acc' (fun _ _ => rfl)
        have := elimPass_len m gs' (elimStep m acc' g)
        omega
      | false =>
        have hcnt' : 1 ≤ (gs'.filter P).length := by simpa [hPg] using hcnt
        have hih := ih (elimStep m acc' g) (fun g' hg' hPg' acc'' hacc'' =>
          hP' g' (List.mem_cons_of_mem _ hg') hPg' acc'' (fun i hi => by
            rw [hacc'' i (by simp [elimStep]; omega)]
            exact getD_snoc_lt _ _ _ _ hi)) hcnt'
        have h2 : (elimStep m acc' g).2.length ≤ acc'.2.length + 1 := by
          simp only [elimStep, List.length_append]
          have := toList_opt_len_le (simplifyBGate g.op (m + acc'.2.length)
            (acc'.1.getD g.left (Sum.inl false)) (acc'.1.getD g.right (Sum.inl false))).1
          omega
        omega
  induction gs generalizing acc with
  | nil => simp at htwo
  | cons g gs ih =>
    rw [elimPass_cons, List.length_cons]
    cases hPg : P g with
    | true =>
      have hstep := hP g List.mem_cons_self hPg acc (fun _ _ => rfl)
      have hcnt' : 1 ≤ (gs.filter P).length := by
        simp only [List.filter_cons, hPg, ↓reduceIte, List.length_cons] at htwo
        omega
      have hrest := h1 gs (elimStep m acc g) (fun g' hg' hPg' acc'' hacc'' =>
        hP g' (List.mem_cons_of_mem _ hg') hPg' acc'' (fun i hi => by
          rw [hacc'' i (by simp [elimStep]; omega)]
          exact getD_snoc_lt _ _ _ _ hi)) hcnt'
      omega
    | false =>
      have htwo' : 2 ≤ (gs.filter P).length := by simpa [hPg] using htwo
      have hih := ih (elimStep m acc g) (fun g' hg' hPg' acc'' hacc'' =>
        hP g' (List.mem_cons_of_mem _ hg') hPg' acc'' (fun i hi => by
          rw [hacc'' i (by simp [elimStep]; omega)]
          exact getD_snoc_lt _ _ _ _ hi)) htwo'
      have h2 : (elimStep m acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_opt_len_le (simplifyBGate g.op (m + acc.2.length)
          (acc.1.getD g.left (Sum.inl false)) (acc.1.getD g.right (Sum.inl false))).1
        omega
      omega

def ElimInvOn (B : Set ℕ) (m : ℕ) (w_in w_old : List Bool)
    (acc : List Stat × List BinaryGate) : Prop :=
  w_in.length = m ∧
  acc.1.length = w_old.length ∧
  ∀ i : ℕ, i ∉ B →
    statValid (m + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (bWires acc.2 w_in) (acc.1.getD i (Sum.inl false)) = w_old.getD i false

lemma elimInvOn_step (B : Set ℕ) (m : ℕ) (w_in w_old : List Bool)
    (acc : List Stat × List BinaryGate) (g : BinaryGate)
    (hLnot : g.left ∉ B) (hRnot : g.right ∉ B)
    (hinv : ElimInvOn B m w_in w_old acc) :
    ElimInvOn B m w_in (w_old ++ [g.op (w_old.getD g.left false) (w_old.getD g.right false)])
      (elimStep m acc g) := by
  obtain ⟨hwin, hlen, hi⟩ := hinv
  set w_new := bWires acc.2 w_in with hw_new
  have hw_len : w_new.length = m + acc.2.length := by
    rw [hw_new, bWires_length, hwin]
  have hsound := simplifyBGate_sound g.op w_new
    (acc.1.getD g.left (Sum.inl false)) (acc.1.getD g.right (Sum.inl false))
    (by rw [hw_len]; exact (hi g.left hLnot).1) (by rw [hw_len]; exact (hi g.right hRnot).1)
  rw [hw_len] at hsound
  refine ⟨hwin, by simp [elimStep, hlen], ?_⟩
  intro i hiB
  simp only [elimStep]
  by_cases hieq : i = acc.1.length
  · rw [getD_snoc_eq _ _ _ _ hieq, getD_snoc_eq _ _ _ _ (by omega)]
    refine ⟨?_, ?_⟩
    · rw [List.length_append, ← Nat.add_assoc]; exact hsound.1
    · rw [bWires_append, ← hw_new, hsound.2, (hi g.left hLnot).2, (hi g.right hRnot).2]
  · rw [getD_snoc_ne _ _ _ _ hieq, getD_snoc_ne _ _ _ _ (by omega)]
    have ⟨hv, hval⟩ := hi i hiB
    refine ⟨?_, ?_⟩
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c => trivial
      | inr p =>
        obtain ⟨j, neg⟩ := p
        rw [hst] at hv
        simp only [statValid, List.length_append] at hv ⊢
        omega
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c => rw [hst] at hval; exact hval
      | inr p =>
        obtain ⟨j, neg⟩ := p
        rw [hst] at hv hval
        simp only [statValid] at hv
        simp only [statVal] at hval ⊢
        rw [bWires_append, ← hw_new, bWires_getD_lt _ _ _ (by omega)]
        exact hval

lemma elimInvOn_pass (B : Set ℕ) (m : ℕ) (w_in : List Bool) (gs : List BinaryGate)
    (w_old : List Bool) (acc : List Stat × List BinaryGate)
    (hread : ∀ g ∈ gs, g.left ∉ B ∧ g.right ∉ B)
    (hinv : ElimInvOn B m w_in w_old acc) :
    ElimInvOn B m w_in (bWires gs w_old) (elimPass m gs acc) := by
  induction gs generalizing w_old acc with
  | nil => exact hinv
  | cons g gs ih =>
    rw [bWires_cons, elimPass_cons]
    have h0 := hread g List.mem_cons_self
    exact ih _ _ (fun g' hg' => hread g' (List.mem_cons_of_mem _ hg'))
      (elimInvOn_step B m w_in w_old acc g h0.1 h0.2 hinv)

lemma bWires_agree (gs : List BinaryGate) (B : Set ℕ) (w₁ w₂ : List Bool)
    (hlen : w₁.length = w₂.length) (hB : ∀ b ∈ B, b < w₁.length)
    (hagree : ∀ i ∉ B, w₁.getD i false = w₂.getD i false)
    (hread : ∀ g ∈ gs, g.left ∉ B ∧ g.right ∉ B) :
    (bWires gs w₁).length = (bWires gs w₂).length ∧
    ∀ i ∉ B, (bWires gs w₁).getD i false = (bWires gs w₂).getD i false := by
  induction gs generalizing w₁ w₂ with
  | nil => exact ⟨hlen, hagree⟩
  | cons g gs ih =>
    rw [bWires_cons, bWires_cons]
    have h0 := hread g List.mem_cons_self
    rw [hagree g.left h0.1, hagree g.right h0.2]
    apply ih
    · simp [hlen]
    · intro b hb; simp; have := hB b hb; omega
    · intro i hi
      by_cases hlt : i < w₁.length
      · rw [getD_snoc_lt _ _ _ _ hlt, getD_snoc_lt _ _ _ _ (by omega)]
        exact hagree i hi
      · by_cases heq : i = w₁.length
        · rw [getD_snoc_eq _ _ _ _ heq, getD_snoc_eq _ _ _ _ (by omega)]
        · rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp; omega)]
    · intro g' hg'; exact hread g' (List.mem_cons_of_mem _ hg')

def flipGate (target : ℕ) (g : BinaryGate) : BinaryGate :=
  ⟨fun a b => g.op (if g.left = target then !a else a) (if g.right = target then !b else b),
   g.left, g.right⟩

lemma bWires_flip_tail (gs : List BinaryGate) (target : ℕ) (w₁ w₂ : List Bool)
    (hlen : w₁.length = w₂.length) (ht : target < w₁.length)
    (hdiff : w₂.getD target false = !(w₁.getD target false))
    (hsame : ∀ i, i ≠ target → w₂.getD i false = w₁.getD i false) :
    ∀ i, (bWires (gs.map (flipGate target)) w₂).getD i false =
      if i = target then !(bWires gs w₁).getD i false else (bWires gs w₁).getD i false := by
  induction gs generalizing w₁ w₂ with
  | nil =>
    intro i
    by_cases hi : i = target
    · subst hi; simp only [bWires_nil, ↓reduceIte]; exact hdiff
    · simp only [bWires_nil, hi, ↓reduceIte]; exact hsame i hi
  | cons g gs ih =>
    rw [List.map_cons, bWires_cons, bWires_cons]
    have hval : (flipGate target g).op (w₂.getD (flipGate target g).left false)
          (w₂.getD (flipGate target g).right false) =
        g.op (w₁.getD g.left false) (w₁.getD g.right false) := by
      simp only [flipGate]
      congr 1
      · by_cases hl : g.left = target
        · simp only [hl, ↓reduceIte]; rw [hdiff, Bool.not_not]
        · simp only [hl, ↓reduceIte]; exact hsame _ hl
      · by_cases hr : g.right = target
        · simp only [hr, ↓reduceIte]; rw [hdiff, Bool.not_not]
        · simp only [hr, ↓reduceIte]; exact hsame _ hr
    rw [hval]
    apply ih
    · simp [hlen]
    · simp; omega
    · rw [getD_snoc_lt _ _ _ _ (by omega), getD_snoc_lt _ _ _ _ ht]; exact hdiff
    · intro i hi
      by_cases hlt : i < w₁.length
      · rw [getD_snoc_lt _ _ _ _ (by omega), getD_snoc_lt _ _ _ _ hlt]; exact hsame i hi
      · by_cases heq : i = w₁.length
        · rw [getD_snoc_eq _ _ _ _ (by omega), getD_snoc_eq _ _ _ _ heq]
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma negate_wire {m : ℕ} (gs : List BinaryGate) (j : ℕ) (hj1 : m ≤ j) (hj2 : j < m + gs.length) :
    ∃ gs' : List BinaryGate, gs'.length = gs.length ∧
      ∀ x : Fin m → Bool, (bWires gs' (List.ofFn x)).getD j false =
        !((bWires gs (List.ofFn x)).getD j false) := by
  set k := j - m with hk
  have hkl : k < gs.length := by omega
  have hsplit : gs = gs.take k ++ [gs[k]] ++ gs.drop (k + 1) := by simp
  set g0 : BinaryGate := ⟨fun a b => !(gs[k].op a b), gs[k].left, gs[k].right⟩ with hg0
  refine ⟨gs.take k ++ [g0] ++ (gs.drop (k + 1)).map (flipGate j), ?_, ?_⟩
  · simp [List.length_take, Nat.min_eq_left hkl.le]
    omega
  · intro x
    set w0 := bWires (gs.take k) (List.ofFn x) with hw0
    have hw0_len : w0.length = j := by
      rw [hw0, bWires_length, List.length_ofFn, List.length_take, Nat.min_eq_left hkl.le]
      omega
    have h1 : bWires (gs.take k ++ [g0] ++ (gs.drop (k + 1)).map (flipGate j)) (List.ofFn x) =
        bWires ((gs.drop (k + 1)).map (flipGate j))
          (w0 ++ [g0.op (w0.getD g0.left false) (w0.getD g0.right false)]) := by
      rw [bWires_append, bWires_append, ← hw0, bWires_cons, bWires_nil]
    have h2 : bWires gs (List.ofFn x) =
        bWires (gs.drop (k + 1))
          (w0 ++ [gs[k].op (w0.getD gs[k].left false) (w0.getD gs[k].right false)]) := by
      conv_lhs => rw [hsplit]
      rw [bWires_append, bWires_append, ← hw0, bWires_cons, bWires_nil]
    rw [h1, h2]
    have hfl := bWires_flip_tail (gs.drop (k + 1)) j
      (w0 ++ [gs[k].op (w0.getD gs[k].left false) (w0.getD gs[k].right false)])
      (w0 ++ [g0.op (w0.getD g0.left false) (w0.getD g0.right false)])
      (by simp) (by simp [hw0_len])
      (by rw [getD_snoc_eq _ _ _ _ hw0_len.symm, getD_snoc_eq _ _ _ _ hw0_len.symm])
      (fun i hi => by
        rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)])
      j
    simpa using hfl

lemma circuit_from_stat {m s : ℕ} {F : (Fin m → Bool) → Bool}
    (gs : List BinaryGate) (st : Stat) (hlen : gs.length ≤ s) (hval_st : statValid (m + gs.length) st)
    (heval : ∀ x : Fin m → Bool, statVal (bWires gs (List.ofFn x)) st = F x)
    (hnc : ∃ x x' : Fin m → Bool, F x ≠ F x')
    (hF0 : F (fun _ => false) = false) :
    HasBinarySize m F s := by
  cases st with
  | inl c =>
    obtain ⟨x, x', hne⟩ := hnc
    have hx := heval x; have hx' := heval x'
    exact absurd (hx.symm.trans hx') hne
  | inr p =>
    obtain ⟨j, neg⟩ := p
    cases neg with
    | false =>
      refine ⟨⟨gs, j⟩, hlen, ?_⟩
      intro x
      have hx := heval x
      simpa [BinaryCircuit.eval, BinaryCircuit.wires, bWires, statVal] using hx
    | true =>
      by_cases hj : j < m
      · exfalso
        have h0 := heval (fun _ => false)
        rw [hF0] at h0
        simp only [statVal] at h0
        rw [bWires_getD_lt _ _ _ (by simp; exact hj), ofFn_getD_lt _ _ _ hj] at h0
        simp at h0
      · obtain ⟨gs', hlen', hev'⟩ := negate_wire gs j (by omega) hval_st
        refine ⟨⟨gs', j⟩, by simp [BinaryCircuit.size, hlen', hlen], ?_⟩
        intro x
        have hx := heval x
        simp only [statVal, Bool.xor_true] at hx
        show (bWires gs' (List.ofFn x)).getD j false = F x
        rw [hev' x]
        exact hx

def initVar (m : ℕ) (v : Fin m) (b : Bool) : List Stat :=
  List.ofFn fun i : Fin m => if i = v then Sum.inl b else Sum.inr (i, false)

lemma elimInvOn_initVar (B : Set ℕ) (m : ℕ) (v : Fin m) (b : Bool) (x : Fin m → Bool) :
    ElimInvOn B m (List.ofFn x) (List.ofFn (Function.update x v b)) (initVar m v b, []) := by
  refine ⟨by simp, by simp [initVar], ?_⟩
  intro i _
  by_cases hi : i < m
  · have hget : (initVar m v b).getD i (Sum.inl false) =
        if (⟨i, hi⟩ : Fin m) = v then Sum.inl b else Sum.inr (i, false) := by
      rw [initVar, ofFn_getD_lt _ _ _ hi]
    rw [hget]
    by_cases heq : (⟨i, hi⟩ : Fin m) = v
    · simp only [heq, ↓reduceIte, statValid, statVal]
      rw [ofFn_getD_lt _ _ _ hi, heq, Function.update_self]
      exact ⟨trivial, rfl⟩
    · simp only [heq, ↓reduceIte, statValid, statVal, bWires_nil, Bool.xor_false]
      refine ⟨by omega, ?_⟩
      rw [ofFn_getD_lt _ _ _ hi, ofFn_getD_lt _ _ _ hi, Function.update_of_ne heq]
  · rw [List.getD_eq_default _ _ (by simp [initVar]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

lemma elim_one_var {m s : ℕ} {F : (Fin m → Bool) → Bool} (v : Fin m) (b : Bool)
    (hC : HasBinarySize m F s)
    (hdep : ∃ x : Fin m → Bool, F (Function.update x v false) ≠ F (Function.update x v true))
    (hnc : ∃ x x' : Fin m → Bool, F (Function.update x v b) ≠ F (Function.update x' v b))
    (hF0 : F (Function.update (fun _ => false) v b) = false) :
    1 ≤ s ∧ HasBinarySize m (fun x => F (Function.update x v b)) (s - 1) := by
  obtain ⟨C, hsz, hev⟩ := hC
  have hsz' : C.gates.length ≤ s := hsz
  have hout_ne : C.output ≠ (v : ℕ) := by
    intro heq
    obtain ⟨x, x', hne⟩ := hnc
    have h1 := hev (Function.update x v b)
    have h2 := hev (Function.update x' v b)
    have hw : ∀ y : Fin m → Bool,
        (bWires C.gates (List.ofFn (Function.update y v b))).getD (v : ℕ) false = b := by
      intro y
      rw [bWires_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ v.isLt]; simp
    have e1 : F (Function.update x v b) = b := by
      rw [← h1]; show (bWires C.gates _).getD C.output false = b; rw [heq]; exact hw x
    have e2 : F (Function.update x' v b) = b := by
      rw [← h2]; show (bWires C.gates _).getD C.output false = b; rw [heq]; exact hw x'
    exact hne (e1.trans e2.symm)
  have hex : ∃ g ∈ C.gates, readsWire (v : ℕ) g = true := by
    by_contra hno
    push_neg at hno
    obtain ⟨x, hne⟩ := hdep
    have hag := bWires_agree C.gates {(v : ℕ)}
      (List.ofFn (Function.update x v false))
      (List.ofFn (Function.update x v true))
      (by simp) (by intro u hu; simp at hu; subst hu; simp)
      (by
        intro i hi; simp at hi
        by_cases hlt : i < m
        · have hne' : (⟨i, hlt⟩ : Fin m) ≠ v := fun h => hi (congrArg Fin.val h)
          rw [ofFn_getD_lt _ _ _ hlt, ofFn_getD_lt _ _ _ hlt,
              Function.update_of_ne hne', Function.update_of_ne hne']
        · rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp; omega)])
      (by
        intro g hg
        have hr := hno g hg
        simp only [readsWire, ne_eq, decide_eq_true_eq, not_or] at hr
        exact ⟨by simpa using hr.1, by simpa using hr.2⟩)
    have hEq := hag.2 C.output (by simpa using hout_ne)
    exact hne ((hev _).symm.trans (hEq.trans (hev _)))
  set acc := elimPass m C.gates (initVar m v b, []) with hacc
  have hlen : acc.2.length + 1 ≤ C.gates.length := by
    have := elimPass_len_lt m (v : ℕ) C.gates (initVar m v b, [])
      (by simp [initVar])
      ⟨b, by rw [initVar, ofFn_getD_lt _ _ _ v.isLt]; simp⟩
      hex
    rw [← hacc] at this
    simpa using this
  have hinv : ∀ x : Fin m → Bool,
      ElimInvOn ∅ m (List.ofFn x) (bWires C.gates (List.ofFn (Function.update x v b))) acc :=
    fun x => elimInvOn_pass ∅ m (List.ofFn x) C.gates _ (initVar m v b, [])
      (fun _ _ => ⟨by simp, by simp⟩) (elimInvOn_initVar ∅ m v b x)
  have hst_val : statValid (m + acc.2.length) (acc.1.getD C.output (Sum.inl false)) :=
    ((hinv (fun _ => false)).2.2 C.output (by simp)).1
  have heval_acc : ∀ x : Fin m → Bool,
      statVal (bWires acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) =
        F (Function.update x v b) := by
    intro x
    rw [((hinv x).2.2 C.output (by simp)).2]
    exact hev (Function.update x v b)
  exact ⟨by omega, circuit_from_stat acc.2 (acc.1.getD C.output (Sum.inl false)) (by omega)
    hst_val heval_acc hnc hF0⟩

lemma list_split_unique_filter {α : Type*} (p : α → Bool) (l : List α)
    (h : (l.filter p).length = 1) :
    ∃ l₁ a l₂, l = l₁ ++ [a] ++ l₂ ∧ p a = true ∧
      (∀ x ∈ l₁, p x = false) ∧ (∀ x ∈ l₂, p x = false) := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    cases hpx : p x with
    | true =>
      have h0 : (xs.filter p).length = 0 := by
        simp only [List.filter_cons, hpx, ↓reduceIte, List.length_cons] at h
        omega
      have hnil : xs.filter p = [] := List.eq_nil_of_length_eq_zero h0
      refine ⟨[], x, xs, rfl, hpx, by simp, ?_⟩
      intro y hy
      by_contra hpy
      have hpyt : p y = true := by cases hp : p y <;> simp_all
      have : y ∈ xs.filter p := List.mem_filter.2 ⟨hy, hpyt⟩
      rw [hnil] at this; simp at this
    | false =>
      have h1 : (xs.filter p).length = 1 := by simpa [hpx] using h
      obtain ⟨l₁, a, l₂, rfl, hpa, hl₁, hl₂⟩ := ih h1
      refine ⟨x :: l₁, a, l₂, by simp, hpa, ?_, hl₂⟩
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy'
      · exact hpx
      · exact hl₁ y hy'

lemma xor_diag_const (op : Bool → Bool → Bool)
    (hL0 : op false false ≠ op false true) (hL1 : op true false ≠ op true true)
    (hR0 : op false false ≠ op true false) (hR1 : op false true ≠ op true true) :
    ∀ a : Bool, op a a = op false false := by
  intro a
  cases a
  · rfl
  · cases h00 : op false false <;> cases h01 : op false true <;>
      cases h10 : op true false <;> cases h11 : op true true <;> simp_all

lemma op_xor_of_nonconst_left (op : Bool → Bool → Bool)
    (hL0 : op false false ≠ op false true) (hL1 : op true false ≠ op true true)
    (hdepL : ¬ ∀ b : Bool, op false b = op true b) :
    op false false ≠ op true false ∧ op false true ≠ op true true := by
  cases h00 : op false false <;> cases h01 : op false true <;>
    cases h10 : op true false <;> cases h11 : op true true <;>
    simp_all [Bool.forall_bool]

lemma op_xor_of_nonconst_right (op : Bool → Bool → Bool)
    (hR0 : op false false ≠ op true false) (hR1 : op false true ≠ op true true)
    (hdepR : ¬ ∀ a : Bool, op a false = op a true) :
    op false false ≠ op false true ∧ op true false ≠ op true true := by
  cases h00 : op false false <;> cases h01 : op false true <;>
    cases h10 : op true false <;> cases h11 : op true true <;>
    simp_all [Bool.forall_bool]

lemma bWires_pair_factor {m : ℕ} (gs₁ gs₂ : List BinaryGate) (g₁ : BinaryGate)
    (ℓ p : Fin m) (hgs₁ : ∀ g ∈ gs₁, readsWire ℓ g = false ∧ readsWire p g = false)
    (hgs₂ : ∀ g ∈ gs₂, readsWire ℓ g = false ∧ readsWire p g = false)
    (x y : Fin m → Bool)
    (hxy : ∀ i : Fin m, i ≠ ℓ → i ≠ p → x i = y i)
    (hw1 : (bWires (gs₁ ++ [g₁]) (List.ofFn x)).getD (m + gs₁.length) false =
           (bWires (gs₁ ++ [g₁]) (List.ofFn y)).getD (m + gs₁.length) false)
    (o : ℕ) (hoℓ : o ≠ ℓ) (hop : o ≠ p) :
    (bWires (gs₁ ++ [g₁] ++ gs₂) (List.ofFn x)).getD o false =
    (bWires (gs₁ ++ [g₁] ++ gs₂) (List.ofFn y)).getD o false := by
  have hag1 := bWires_agree gs₁ {(ℓ : ℕ), (p : ℕ)} (List.ofFn x) (List.ofFn y)
    (by simp)
    (by intro b hb; rcases hb with rfl | rfl <;> simp)
    (by
      intro i hi
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hi
      by_cases hlt : i < m
      · have h1 : (⟨i, hlt⟩ : Fin m) ≠ ℓ := fun h => hi.1 (congrArg Fin.val h)
        have h2 : (⟨i, hlt⟩ : Fin m) ≠ p := fun h => hi.2 (congrArg Fin.val h)
        rw [ofFn_getD_lt _ _ _ hlt, ofFn_getD_lt _ _ _ hlt, hxy _ h1 h2]
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)])
    (by
      intro g hg
      have ⟨h1, h2⟩ := hgs₁ g hg
      simp only [readsWire, decide_eq_false_iff_not, not_or] at h1 h2
      exact ⟨by simp [h1.1, h2.1], by simp [h1.2, h2.2]⟩)
  have hlen1 : (bWires (gs₁ ++ [g₁]) (List.ofFn x)).length =
      (bWires (gs₁ ++ [g₁]) (List.ofFn y)).length := by
    simp [bWires_length]
  have hag2 := bWires_agree gs₂ {(ℓ : ℕ), (p : ℕ)}
    (bWires (gs₁ ++ [g₁]) (List.ofFn x))
    (bWires (gs₁ ++ [g₁]) (List.ofFn y))
    hlen1
    (by intro b hb; rw [bWires_length, List.length_ofFn]; rcases hb with rfl | rfl <;> omega)
    (by
      intro i hi
      by_cases hieq : i = m + gs₁.length
      · subst hieq; exact hw1
      · have hlen_g1x : (bWires gs₁ (List.ofFn x)).length = m + gs₁.length := by
          rw [bWires_length, List.length_ofFn]
        have hlen_g1y : (bWires gs₁ (List.ofFn y)).length = m + gs₁.length := by
          rw [bWires_length, List.length_ofFn]
        rw [bWires_append, bWires_cons, bWires_nil, bWires_append, bWires_cons, bWires_nil,
            getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
        exact hag1.2 i hi)
    (by
      intro g hg
      have ⟨h1, h2⟩ := hgs₂ g hg
      simp only [readsWire, decide_eq_false_iff_not, not_or] at h1 h2
      exact ⟨by simp [h1.1, h2.1], by simp [h1.2, h2.2]⟩)
  rw [bWires_append (gs₁ ++ [g₁]) gs₂, bWires_append (gs₁ ++ [g₁]) gs₂]
  exact hag2.2 o (by simp [hoℓ, hop])

lemma elim_leaf_parent {m s : ℕ} {F : (Fin m → Bool) → Bool} (ℓ p q : Fin m)
    (hℓp : ℓ ≠ p) (hqℓ : q ≠ ℓ) (hqp : q ≠ p)
    (hC : HasBinarySize m F s)
    (hdep : ∃ x : Fin m → Bool, F (Function.update x ℓ false) ≠ F (Function.update x ℓ true))
    (hnc0 : ∃ x x' : Fin m → Bool, F (Function.update x ℓ false) ≠ F (Function.update x' ℓ false))
    (hnc1 : ∃ x x' : Fin m → Bool, F (Function.update x ℓ true) ≠ F (Function.update x' ℓ true))
    (hncp : ∃ x x' : Fin m → Bool, F (Function.update x p false) ≠ F (Function.update x' p false))
    (hF0_0 : F (Function.update (fun _ => false) ℓ false) = false)
    (hF0_1 : F (Function.update (fun _ => false) ℓ true) = false)
    (hF0_p : F (Function.update (fun _ => false) p false) = false)
    (hkill : ∀ x : Fin m → Bool, ∀ b : Bool,
      F (Function.update (Function.update x p false) ℓ b) = F (Function.update x p false))
    (h3sub : ∀ (x₀ : Fin m → Bool), (∀ i, i ≠ ℓ → i ≠ p → i ≠ q → x₀ i = false) →
      F (Function.update (Function.update (Function.update x₀ p false) ℓ false) q false) = false ∧
      F (Function.update (Function.update (Function.update x₀ p false) ℓ false) q true) = false ∧
      F (Function.update (Function.update (Function.update x₀ p true) ℓ false) q false) = false ∧
      F (Function.update (Function.update (Function.update x₀ p true) ℓ false) q true) = true ∧
      F (Function.update (Function.update (Function.update x₀ p true) ℓ true) q false) = true ∧
      F (Function.update (Function.update (Function.update x₀ p true) ℓ true) q true) = true) :
    (2 ≤ s ∧ HasBinarySize m (fun x => F (Function.update x ℓ false)) (s - 2)) ∨
    (2 ≤ s ∧ HasBinarySize m (fun x => F (Function.update x ℓ true)) (s - 2)) ∨
    (3 ≤ s ∧ HasBinarySize m (fun x => F (Function.update x p false)) (s - 3)) := by
  obtain ⟨C, hsz, hev⟩ := hC
  have hsz' : C.gates.length ≤ s := hsz
  have hout_ne_ℓ : C.output ≠ (ℓ : ℕ) := by
    intro heq
    obtain ⟨x, x', hne⟩ := hnc0
    have hw : ∀ y : Fin m → Bool,
        (bWires C.gates (List.ofFn (Function.update y ℓ false))).getD (ℓ : ℕ) false = false := by
      intro y; rw [bWires_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ ℓ.isLt]; simp
    have e1 : F (Function.update x ℓ false) = false := by
      rw [← hev]; show (bWires C.gates _).getD C.output false = false; rw [heq]; exact hw x
    have e2 : F (Function.update x' ℓ false) = false := by
      rw [← hev]; show (bWires C.gates _).getD C.output false = false; rw [heq]; exact hw x'
    exact hne (e1.trans e2.symm)
  have hout_ne_p : C.output ≠ (p : ℕ) := by
    intro heq
    obtain ⟨x, x', hne⟩ := hncp
    have hw : ∀ y : Fin m → Bool,
        (bWires C.gates (List.ofFn (Function.update y p false))).getD (p : ℕ) false = false := by
      intro y; rw [bWires_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ p.isLt]; simp
    have e1 : F (Function.update x p false) = false := by
      rw [← hev]; show (bWires C.gates _).getD C.output false = false; rw [heq]; exact hw x
    have e2 : F (Function.update x' p false) = false := by
      rw [← hev]; show (bWires C.gates _).getD C.output false = false; rw [heq]; exact hw x'
    exact hne (e1.trans e2.symm)
  set cnt := (C.gates.filter (readsWire (ℓ : ℕ))).length with hcnt
  by_cases hge2 : 2 ≤ cnt
  · set acc := elimPass m C.gates (initVar m ℓ false, []) with hacc
    have hlen : acc.2.length + 2 ≤ C.gates.length := by
      have := elimPass_len_two_pred m (readsWire (ℓ : ℕ)) C.gates (initVar m ℓ false, [])
        (fun g _ hr acc' hacc' =>
          elimStep_none_of_reads m (ℓ : ℕ) acc' g
            ⟨false, by rw [hacc' (ℓ : ℕ) (by simp [initVar]), initVar, ofFn_getD_lt _ _ _ ℓ.isLt]; simp⟩ hr)
        (by rw [← hcnt]; exact hge2)
      rw [← hacc] at this
      simpa using this
    have hinv : ∀ x : Fin m → Bool,
        ElimInvOn ∅ m (List.ofFn x) (bWires C.gates (List.ofFn (Function.update x ℓ false))) acc :=
      fun x => elimInvOn_pass ∅ m (List.ofFn x) C.gates _ (initVar m ℓ false, [])
        (fun _ _ => ⟨by simp, by simp⟩) (elimInvOn_initVar ∅ m ℓ false x)
    exact Or.inl ⟨by omega, circuit_from_stat acc.2 (acc.1.getD C.output (Sum.inl false)) (by omega)
      ((hinv (fun _ => false)).2.2 C.output (by simp)).1
      (fun x => by rw [((hinv x).2.2 C.output (by simp)).2]; exact hev _) hnc0 hF0_0⟩
  · by_cases hzero : cnt = 0
    · exfalso
      have hnil : C.gates.filter (readsWire (ℓ : ℕ)) = [] :=
        List.eq_nil_of_length_eq_zero (by rw [← hcnt]; exact hzero)
      obtain ⟨x, hne⟩ := hdep
      have hag := bWires_agree C.gates {(ℓ : ℕ)}
        (List.ofFn (Function.update x ℓ false)) (List.ofFn (Function.update x ℓ true))
        (by simp) (by intro u hu; simp at hu; subst hu; simp)
        (by
          intro i hi; simp at hi
          by_cases hlt : i < m
          · have hne' : (⟨i, hlt⟩ : Fin m) ≠ ℓ := fun h => hi (congrArg Fin.val h)
            rw [ofFn_getD_lt _ _ _ hlt, ofFn_getD_lt _ _ _ hlt,
                Function.update_of_ne hne', Function.update_of_ne hne']
          · rw [List.getD_eq_default _ _ (by simp; omega),
                List.getD_eq_default _ _ (by simp; omega)])
        (by
          intro g hg
          have hno : readsWire (ℓ : ℕ) g = false := by
            by_contra hr
            have hrt : readsWire (ℓ : ℕ) g = true := by cases h : readsWire (ℓ : ℕ) g <;> simp_all
            have : g ∈ C.gates.filter (readsWire (ℓ : ℕ)) := List.mem_filter.2 ⟨hg, hrt⟩
            rw [hnil] at this; simp at this
          simp only [readsWire, decide_eq_false_iff_not, not_or] at hno
          exact ⟨by simpa using hno.1, by simpa using hno.2⟩)
      exact hne ((hev _).symm.trans ((hag.2 C.output (by simpa using hout_ne_ℓ)).trans (hev _)))
    · have hone : (C.gates.filter (readsWire (ℓ : ℕ))).length = 1 := by rw [← hcnt]; omega
      obtain ⟨gs₁, g₁, gs₂, hsplit, hg₁in, hgs₁no, hgs₂no⟩ :=
        list_split_unique_filter (readsWire (ℓ : ℕ)) C.gates hone
      set w₁ := m + gs₁.length with hw₁
      have hex₂_w₁ : C.output ≠ w₁ → ∃ g ∈ gs₂, readsWire w₁ g = true := by
        intro hout_ne_w1
        by_contra hno₂
        push_neg at hno₂
        obtain ⟨x, hne⟩ := hdep
        have hag1 := bWires_agree gs₁ {(ℓ : ℕ)}
          (List.ofFn (Function.update x ℓ false)) (List.ofFn (Function.update x ℓ true))
          (by simp) (by intro u hu; simp at hu; subst hu; simp)
          (by
            intro i hi; simp at hi
            by_cases hlt : i < m
            · have hne' : (⟨i, hlt⟩ : Fin m) ≠ ℓ := fun h => hi (congrArg Fin.val h)
              rw [ofFn_getD_lt _ _ _ hlt, ofFn_getD_lt _ _ _ hlt,
                  Function.update_of_ne hne', Function.update_of_ne hne']
            · rw [List.getD_eq_default _ _ (by simp; omega),
                  List.getD_eq_default _ _ (by simp; omega)])
          (by
            intro g hg
            have hr := hgs₁no g hg
            simp only [readsWire, decide_eq_false_iff_not, not_or] at hr
            exact ⟨by simpa using hr.1, by simpa using hr.2⟩)
        have hag2 := bWires_agree gs₂ {(ℓ : ℕ), w₁}
          (bWires (gs₁ ++ [g₁]) (List.ofFn (Function.update x ℓ false)))
          (bWires (gs₁ ++ [g₁]) (List.ofFn (Function.update x ℓ true)))
          (by simp [bWires_length])
          (by intro b hb; rw [bWires_length, List.length_ofFn, List.length_append, List.length_singleton]; rcases hb with rfl | rfl <;> omega)
          (by
            intro i hi
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hi
            rw [bWires_append, bWires_cons, bWires_nil, bWires_append, bWires_cons, bWires_nil]
            have hl1 : (bWires gs₁ (List.ofFn (Function.update x ℓ false))).length = w₁ := by
              rw [bWires_length, List.length_ofFn]
            have hl2 : (bWires gs₁ (List.ofFn (Function.update x ℓ true))).length = w₁ := by
              rw [bWires_length, List.length_ofFn]
            rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
            exact hag1.2 i (by simpa using hi.1))
          (by
            intro g hg
            have hr1 := hgs₂no g hg
            have hr2 := hno₂ g hg
            simp only [readsWire, ne_eq, decide_eq_false_iff_not, decide_eq_true_eq, not_or] at hr1 hr2
            exact ⟨by simp [hr1.1, hr2.1], by simp [hr1.2, hr2.2]⟩)
        have hEq : (bWires C.gates (List.ofFn (Function.update x ℓ false))).getD C.output false =
            (bWires C.gates (List.ofFn (Function.update x ℓ true))).getD C.output false := by
          rw [hsplit, bWires_append (gs₁ ++ [g₁]) gs₂, bWires_append (gs₁ ++ [g₁]) gs₂]
          exact hag2.2 C.output (by simp [hout_ne_ℓ, hout_ne_w1])
        exact hne ((hev _).symm.trans (hEq.trans (hev _)))
      have hconst_finish : ∀ (b : Bool),
          (∃ c : Bool,
            let acc₁ := elimPass m gs₁ (initVar m ℓ b, [])
            simplifyBGate g₁.op (m + acc₁.2.length)
              (acc₁.1.getD g₁.left (Sum.inl false)) (acc₁.1.getD g₁.right (Sum.inl false)) =
              (none, Sum.inl c)) →
          (2 ≤ s ∧ HasBinarySize m (fun x => F (Function.update x ℓ false)) (s - 2)) ∨
          (2 ≤ s ∧ HasBinarySize m (fun x => F (Function.update x ℓ true)) (s - 2)) := by
        intro b ⟨c, hc⟩
        set acc₁ := elimPass m gs₁ (initVar m ℓ b, []) with hacc₁
        set accM := elimStep m acc₁ g₁ with haccM
        set acc := elimPass m gs₂ accM with hacc
        have hacc_eq : acc = elimPass m C.gates (initVar m ℓ b, []) := by
          rw [hsplit, elimPass_append, elimPass_append, ← hacc₁, elimPass_cons, elimPass_nil, ← haccM]
        have hacc₁_len : acc₁.1.length = w₁ := by rw [hacc₁, elimPass_fst_len]; simp [initVar, hw₁]
        have hmid_len : accM.2.length = acc₁.2.length := by
          simp only [haccM, elimStep, hc, Option.toList_none, List.append_nil]
        have hmid_w₁ : accM.1.getD w₁ (Sum.inl false) = Sum.inl c := by
          simp only [haccM, elimStep, hc]
          exact getD_snoc_eq _ _ _ _ hacc₁_len.symm
        have hinv : ∀ x : Fin m → Bool,
            ElimInvOn ∅ m (List.ofFn x) (bWires C.gates (List.ofFn (Function.update x ℓ b))) acc := by
          intro x; rw [hacc_eq]
          exact elimInvOn_pass ∅ m (List.ofFn x) C.gates _ (initVar m ℓ b, [])
            (fun _ _ => ⟨by simp, by simp⟩) (elimInvOn_initVar ∅ m ℓ b x)
        have hncb : ∃ x x' : Fin m → Bool,
            F (Function.update x ℓ b) ≠ F (Function.update x' ℓ b) := by
          cases b; exact hnc0; exact hnc1
        have hF0b : F (Function.update (fun _ => false) ℓ b) = false := by
          cases b; exact hF0_0; exact hF0_1
        have hout_ne_w1 : C.output ≠ w₁ := by
          intro heq
          have hw1acc : acc.1.getD C.output (Sum.inl false) = Sum.inl c := by
            rw [heq, hacc, elimPass_getD_lt _ _ _ _ _ (by simp [haccM, elimStep, hacc₁_len])]
            exact hmid_w₁
          obtain ⟨x, x', hne⟩ := hncb
          have hx := ((hinv x).2.2 C.output (by simp)).2.trans (hev _)
          have hx' := ((hinv x').2.2 C.output (by simp)).2.trans (hev _)
          rw [hw1acc] at hx hx'
          exact hne (hx.symm.trans hx')
        have hex₂ := hex₂_w₁ hout_ne_w1
        have hlen1 : acc₁.2.length ≤ gs₁.length := by
          have := elimPass_len m gs₁ (initVar m ℓ b, [])
          rw [← hacc₁] at this; simpa using this
        have hlen2 : acc.2.length + 1 ≤ accM.2.length + gs₂.length :=
          elimPass_len_lt m w₁ gs₂ accM (by simp [haccM, elimStep, hacc₁_len]) ⟨c, hmid_w₁⟩ hex₂
        have htot : C.gates.length = gs₁.length + 1 + gs₂.length := by rw [hsplit]; simp; omega
        have hres : HasBinarySize m (fun x => F (Function.update x ℓ b)) (s - 2) :=
          circuit_from_stat acc.2 (acc.1.getD C.output (Sum.inl false)) (by omega)
            ((hinv (fun _ => false)).2.2 C.output (by simp)).1
            (fun x => by rw [((hinv x).2.2 C.output (by simp)).2]; exact hev _) hncb hF0b
        cases b
        · exact Or.inl ⟨by omega, hres⟩
        · exact Or.inr ⟨by omega, hres⟩
      have hg₁reads : g₁.left = (ℓ : ℕ) ∨ g₁.right = (ℓ : ℕ) := by
        simpa [readsWire] using hg₁in
      have hacc₁_ℓ : ∀ b : Bool,
          (elimPass m gs₁ (initVar m ℓ b, [])).1.getD (ℓ : ℕ) (Sum.inl false) = Sum.inl b := by
        intro b
        rw [elimPass_getD_lt _ _ _ _ _ (by simp [initVar]), initVar, ofFn_getD_lt _ _ _ ℓ.isLt]
        simp
      by_cases hctrl :
          (g₁.left = (ℓ : ℕ) ∧ g₁.right = (ℓ : ℕ)) ∨
          (g₁.left = (ℓ : ℕ) ∧ (g₁.op false false = g₁.op false true ∨ g₁.op true false = g₁.op true true)) ∨
          (g₁.right = (ℓ : ℕ) ∧ (g₁.op false false = g₁.op true false ∨ g₁.op false true = g₁.op true true))
      · rcases hctrl with ⟨hl, hr⟩ | ⟨hl, h0 | h1⟩ | ⟨hr, h0 | h1⟩
        · refine (hconst_finish false ⟨g₁.op false false, ?_⟩).imp id Or.inl
          dsimp only; rw [hl, hr, hacc₁_ℓ false]; rfl
        · refine (hconst_finish false ⟨g₁.op false false, ?_⟩).imp id Or.inl
          dsimp only; rw [hl, hacc₁_ℓ false]; exact simplifyBGate_const_left _ _ _ _ h0
        · refine (hconst_finish true ⟨g₁.op true false, ?_⟩).imp id Or.inl
          dsimp only; rw [hl, hacc₁_ℓ true]; exact simplifyBGate_const_left _ _ _ _ h1
        · refine (hconst_finish false ⟨g₁.op false false, ?_⟩).imp id Or.inl
          dsimp only; rw [hr, hacc₁_ℓ false]; exact simplifyBGate_const_right _ _ _ _ h0
        · refine (hconst_finish true ⟨g₁.op false true, ?_⟩).imp id Or.inl
          dsimp only; rw [hr, hacc₁_ℓ true]; exact simplifyBGate_const_right _ _ _ _ h1
      · push Not at hctrl
        obtain ⟨hnotboth, hnotL, hnotR⟩ := hctrl
        set u : ℕ := if g₁.left = (ℓ : ℕ) then g₁.right else g₁.left with hu
        have hu_ne_ℓ : u ≠ (ℓ : ℕ) := by
          rcases hg₁reads with hl | hr
          · simp only [hu, hl, ↓reduceIte]; exact hnotboth hl
          · by_cases hl : g₁.left = (ℓ : ℕ)
            · exact absurd hr (hnotboth hl)
            · simp only [hu, hl, ↓reduceIte]; exact hl
        by_cases hu_ge : w₁ ≤ u
        · refine (hconst_finish false ⟨g₁.op false false, ?_⟩).imp id Or.inl
          have hgetu : (elimPass m gs₁ (initVar m ℓ false, [])).1.getD u (Sum.inl false) = Sum.inl false :=
            List.getD_eq_default _ _ (by rw [elimPass_fst_len]; simp [initVar]; omega)
          rcases hg₁reads with hl | hr
          · have hru : g₁.right = u := by simp [hu, hl]
            dsimp only; rw [hl, hru, hacc₁_ℓ false, hgetu]; rfl
          · have hlne : g₁.left ≠ (ℓ : ℕ) := fun hl => hnotboth hl hr
            have hlu : g₁.left = u := by simp [hu, hlne]
            dsimp only; rw [hr, hlu, hacc₁_ℓ false, hgetu]; rfl
        · have hu_lt : u < w₁ := by omega
          have hnotindep :
              (g₁.left = (ℓ : ℕ) → ¬ ∀ b : Bool, g₁.op false b = g₁.op true b) ∧
              (g₁.right = (ℓ : ℕ) → ¬ ∀ a : Bool, g₁.op a false = g₁.op a true) := by
            have hcontra :
                (∀ x : Fin m → Bool,
                  (bWires (gs₁ ++ [g₁]) (List.ofFn (Function.update x ℓ false))).getD w₁ false =
                  (bWires (gs₁ ++ [g₁]) (List.ofFn (Function.update x ℓ true))).getD w₁ false) →
                False := by
              intro hsame_w1
              obtain ⟨x, hne⟩ := hdep
              have hag1 := bWires_agree gs₁ {(ℓ : ℕ)}
                (List.ofFn (Function.update x ℓ false)) (List.ofFn (Function.update x ℓ true))
                (by simp) (by intro b hb; simp at hb; subst hb; simp)
                (by
                  intro i hi; simp at hi
                  by_cases hlt : i < m
                  · have hne' : (⟨i, hlt⟩ : Fin m) ≠ ℓ := fun h => hi (congrArg Fin.val h)
                    rw [ofFn_getD_lt _ _ _ hlt, ofFn_getD_lt _ _ _ hlt,
                        Function.update_of_ne hne', Function.update_of_ne hne']
                  · rw [List.getD_eq_default _ _ (by simp; omega),
                        List.getD_eq_default _ _ (by simp; omega)])
                (by
                  intro g hg
                  have hr := hgs₁no g hg
                  simp only [readsWire, decide_eq_false_iff_not, not_or] at hr
                  exact ⟨by simpa using hr.1, by simpa using hr.2⟩)
              have hag2 := bWires_agree gs₂ {(ℓ : ℕ)}
                (bWires (gs₁ ++ [g₁]) (List.ofFn (Function.update x ℓ false)))
                (bWires (gs₁ ++ [g₁]) (List.ofFn (Function.update x ℓ true)))
                (by simp [bWires_length])
                (by intro b hb; simp at hb; subst hb; rw [bWires_length, List.length_ofFn, List.length_append, List.length_singleton]; omega)
                (by
                  intro i hi
                  by_cases hiw : i = w₁
                  · subst hiw; exact hsame_w1 x
                  · rw [bWires_append, bWires_cons, bWires_nil, bWires_append, bWires_cons, bWires_nil]
                    have hl1 : (bWires gs₁ (List.ofFn (Function.update x ℓ false))).length = w₁ := by
                      rw [bWires_length, List.length_ofFn]
                    have hl2 : (bWires gs₁ (List.ofFn (Function.update x ℓ true))).length = w₁ := by
                      rw [bWires_length, List.length_ofFn]
                    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
                    exact hag1.2 i hi)
                (by
                  intro g hg
                  have hr := hgs₂no g hg
                  simp only [readsWire, decide_eq_false_iff_not, not_or] at hr
                  exact ⟨by simpa using hr.1, by simpa using hr.2⟩)
              have hEq : (bWires C.gates (List.ofFn (Function.update x ℓ false))).getD C.output false =
                  (bWires C.gates (List.ofFn (Function.update x ℓ true))).getD C.output false := by
                rw [hsplit, bWires_append (gs₁ ++ [g₁]) gs₂, bWires_append (gs₁ ++ [g₁]) gs₂]
                exact hag2.2 C.output (by simpa using hout_ne_ℓ)
              exact hne ((hev _).symm.trans (hEq.trans (hev _)))
            constructor
            · intro hl hind
              apply hcontra; intro x
              have hru : g₁.right = u := by simp [hu, hl]
              have hag1 := bWires_agree gs₁ {(ℓ : ℕ)}
                (List.ofFn (Function.update x ℓ false)) (List.ofFn (Function.update x ℓ true))
                (by simp) (by intro b hb; simp at hb; subst hb; simp)
                (by
                  intro i hi; simp at hi
                  by_cases hlt : i < m
                  · have hne' : (⟨i, hlt⟩ : Fin m) ≠ ℓ := fun h => hi (congrArg Fin.val h)
                    rw [ofFn_getD_lt _ _ _ hlt, ofFn_getD_lt _ _ _ hlt,
                        Function.update_of_ne hne', Function.update_of_ne hne']
                  · rw [List.getD_eq_default _ _ (by simp; omega),
                        List.getD_eq_default _ _ (by simp; omega)])
                (by
                  intro g hg
                  have hr := hgs₁no g hg
                  simp only [readsWire, decide_eq_false_iff_not, not_or] at hr
                  exact ⟨by simpa using hr.1, by simpa using hr.2⟩)
              rw [bWires_append, bWires_cons, bWires_nil, bWires_append, bWires_cons, bWires_nil,
                  getD_snoc_eq _ _ _ _ (by rw [bWires_length, List.length_ofFn]),
                  getD_snoc_eq _ _ _ _ (by rw [bWires_length, List.length_ofFn]),
                  hru, hag1.2 u (by simpa using hu_ne_ℓ)]
              cases (bWires gs₁ (List.ofFn (Function.update x ℓ false))).getD g₁.left false <;>
                cases (bWires gs₁ (List.ofFn (Function.update x ℓ true))).getD g₁.left false
              · rfl
              · exact hind _
              · exact (hind _).symm
              · rfl
            · intro hr hind
              apply hcontra; intro x
              have hlne : g₁.left ≠ (ℓ : ℕ) := fun hl => hnotboth hl hr
              have hlu : g₁.left = u := by simp [hu, hlne]
              have hag1 := bWires_agree gs₁ {(ℓ : ℕ)}
                (List.ofFn (Function.update x ℓ false)) (List.ofFn (Function.update x ℓ true))
                (by simp) (by intro b hb; simp at hb; subst hb; simp)
                (by
                  intro i hi; simp at hi
                  by_cases hlt : i < m
                  · have hne' : (⟨i, hlt⟩ : Fin m) ≠ ℓ := fun h => hi (congrArg Fin.val h)
                    rw [ofFn_getD_lt _ _ _ hlt, ofFn_getD_lt _ _ _ hlt,
                        Function.update_of_ne hne', Function.update_of_ne hne']
                  · rw [List.getD_eq_default _ _ (by simp; omega),
                        List.getD_eq_default _ _ (by simp; omega)])
                (by
                  intro g hg
                  have hr' := hgs₁no g hg
                  simp only [readsWire, decide_eq_false_iff_not, not_or] at hr'
                  exact ⟨by simpa using hr'.1, by simpa using hr'.2⟩)
              rw [bWires_append, bWires_cons, bWires_nil, bWires_append, bWires_cons, bWires_nil,
                  getD_snoc_eq _ _ _ _ (by rw [bWires_length, List.length_ofFn]),
                  getD_snoc_eq _ _ _ _ (by rw [bWires_length, List.length_ofFn]),
                  hlu, hag1.2 u (by simpa using hu_ne_ℓ)]
              cases (bWires gs₁ (List.ofFn (Function.update x ℓ false))).getD g₁.right false <;>
                cases (bWires gs₁ (List.ofFn (Function.update x ℓ true))).getD g₁.right false
              · rfl
              · exact hind _
              · exact (hind _).symm
              · rfl
          have hL0L1R0R1 :
              (g₁.op false false ≠ g₁.op false true ∧ g₁.op true false ≠ g₁.op true true) ∧
              (g₁.op false false ≠ g₁.op true false ∧ g₁.op false true ≠ g₁.op true true) := by
            rcases hg₁reads with hl | hr
            · have hL := hnotL hl
              exact ⟨hL, op_xor_of_nonconst_left g₁.op hL.1 hL.2 (hnotindep.1 hl)⟩
            · have hR := hnotR hr
              exact ⟨op_xor_of_nonconst_right g₁.op hR.1 hR.2 (hnotindep.2 hr), hR⟩
          have hL0 := hL0L1R0R1.1.1
          have hL1 := hL0L1R0R1.1.2
          have hR0 := hL0L1R0R1.2.1
          have hR1 := hL0L1R0R1.2.2
          set c₁ := g₁.op false false with hc₁
          have hdiag : ∀ a : Bool, g₁.op a a = c₁ := xor_diag_const g₁.op hL0 hL1 hR0 hR1
          set acc₁ := elimPass m gs₁ (initVar m p false, []) with hacc₁
          set accM : List Stat × List BinaryGate := (acc₁.1 ++ [Sum.inl c₁], acc₁.2) with haccM
          set acc := elimPass m gs₂ accM with hacc
          have hacc₁_len : acc₁.1.length = w₁ := by
            rw [hacc₁, elimPass_fst_len]; simp [initVar, hw₁]
          have hacc₁_p : acc₁.1.getD (p : ℕ) (Sum.inl false) = Sum.inl false := by
            rw [hacc₁, elimPass_getD_lt _ _ _ _ _ (by simp [initVar]), initVar, ofFn_getD_lt _ _ _ p.isLt]
            simp
          have haccM_p : accM.1.getD (p : ℕ) (Sum.inl false) = Sum.inl false := by
            simp only [haccM]
            rw [getD_snoc_lt _ _ _ _ (by rw [hacc₁_len]; omega)]
            exact hacc₁_p
          have haccM_w₁ : accM.1.getD w₁ (Sum.inl false) = Sum.inl c₁ := by
            simp only [haccM]
            exact getD_snoc_eq _ _ _ _ hacc₁_len.symm
          have hinv_all : ∀ x : Fin m → Bool,
              let x' := Function.update x p false
              let σ := Function.update x' ℓ ((bWires gs₁ (List.ofFn x')).getD u false)
              ElimInvOn {(ℓ : ℕ)} m (List.ofFn x) (bWires C.gates (List.ofFn σ)) acc := by
            intro x
            set x' := Function.update x p false with hx'
            set bval := (bWires gs₁ (List.ofFn x')).getD u false with hbval
            set σ := Function.update x' ℓ bval with hσ
            have hinv0 : ElimInvOn {(ℓ : ℕ)} m (List.ofFn x) (List.ofFn σ) (initVar m p false, []) := by
              refine ⟨by simp, by simp [initVar], ?_⟩
              intro i hi
              simp only [Set.mem_singleton_iff] at hi
              by_cases him : i < m
              · have hiℓ : (⟨i, him⟩ : Fin m) ≠ ℓ := fun h => hi (congrArg Fin.val h)
                have hget : (initVar m p false).getD i (Sum.inl false) =
                    if (⟨i, him⟩ : Fin m) = p then Sum.inl false else Sum.inr (i, false) := by
                  rw [initVar, ofFn_getD_lt _ _ _ him]
                rw [hget]
                by_cases hip : (⟨i, him⟩ : Fin m) = p
                · simp only [hip, ↓reduceIte, statValid, statVal]
                  rw [ofFn_getD_lt _ _ _ him, hσ, Function.update_of_ne hiℓ, hx', hip, Function.update_self]
                  exact ⟨trivial, rfl⟩
                · simp only [hip, ↓reduceIte, statValid, statVal, bWires_nil, Bool.xor_false]
                  refine ⟨by omega, ?_⟩
                  rw [ofFn_getD_lt _ _ _ him, ofFn_getD_lt _ _ _ him, hσ, Function.update_of_ne hiℓ,
                      hx', Function.update_of_ne hip]
              · rw [List.getD_eq_default _ _ (by simp [initVar]; omega),
                    List.getD_eq_default _ _ (by simp; omega)]
                exact ⟨trivial, rfl⟩
            have hgs₁_notℓ : ∀ g ∈ gs₁, g.left ∉ ({(ℓ : ℕ)} : Set ℕ) ∧ g.right ∉ ({(ℓ : ℕ)} : Set ℕ) := by
              intro g hg
              have hr := hgs₁no g hg
              simp only [readsWire, decide_eq_false_iff_not, not_or] at hr
              exact ⟨by simpa using hr.1, by simpa using hr.2⟩
            have hgs₂_notℓ : ∀ g ∈ gs₂, g.left ∉ ({(ℓ : ℕ)} : Set ℕ) ∧ g.right ∉ ({(ℓ : ℕ)} : Set ℕ) := by
              intro g hg
              have hr := hgs₂no g hg
              simp only [readsWire, decide_eq_false_iff_not, not_or] at hr
              exact ⟨by simpa using hr.1, by simpa using hr.2⟩
            have hinv1 := elimInvOn_pass {(ℓ : ℕ)} m (List.ofFn x) gs₁ (List.ofFn σ)
              (initVar m p false, []) hgs₁_notℓ hinv0
            have hag_u : (bWires gs₁ (List.ofFn σ)).getD u false = bval := by
              have hag := bWires_agree gs₁ {(ℓ : ℕ)} (List.ofFn σ) (List.ofFn x')
                (by simp) (by intro b hb; simp at hb; subst hb; simp)
                (by
                  intro i hi; simp at hi
                  by_cases him : i < m
                  · have hiℓ : (⟨i, him⟩ : Fin m) ≠ ℓ := fun h => hi (congrArg Fin.val h)
                    rw [ofFn_getD_lt _ _ _ him, ofFn_getD_lt _ _ _ him, hσ, Function.update_of_ne hiℓ]
                  · rw [List.getD_eq_default _ _ (by simp; omega),
                        List.getD_eq_default _ _ (by simp; omega)])
                hgs₁_notℓ
              exact hag.2 u (by simpa using hu_ne_ℓ)
            have hval_ℓ : (bWires gs₁ (List.ofFn σ)).getD (ℓ : ℕ) false = bval := by
              rw [bWires_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ ℓ.isLt, hσ, Function.update_self]
            have hg₁_eval : g₁.op ((bWires gs₁ (List.ofFn σ)).getD g₁.left false)
                ((bWires gs₁ (List.ofFn σ)).getD g₁.right false) = c₁ := by
              rcases hg₁reads with hl | hr
              · have hru : g₁.right = u := by simp [hu, hl]
                rw [hl, hru, hval_ℓ, hag_u]; exact hdiag bval
              · have hlne : g₁.left ≠ (ℓ : ℕ) := fun hl => hnotboth hl hr
                have hlu : g₁.left = u := by simp [hu, hlne]
                rw [hr, hlu, hval_ℓ, hag_u]; exact hdiag bval
            have hinvM : ElimInvOn {(ℓ : ℕ)} m (List.ofFn x)
                (bWires (gs₁ ++ [g₁]) (List.ofFn σ)) accM := by
              rw [bWires_append, bWires_cons, bWires_nil, hg₁_eval]
              refine ⟨hinv1.1, by
                simp only [haccM, List.length_append, List.length_singleton]
                rw [hacc₁_len, bWires_length, List.length_ofFn], ?_⟩
              intro i hi
              by_cases hieq : i = w₁
              · subst hieq
                have hlen_w : (bWires gs₁ (List.ofFn σ)).length = w₁ := by
                  rw [bWires_length, List.length_ofFn]
                rw [haccM_w₁, getD_snoc_eq _ _ _ _ hlen_w.symm]
                exact ⟨trivial, rfl⟩
              · have hlen_w : (bWires gs₁ (List.ofFn σ)).length = w₁ := by
                  rw [bWires_length, List.length_ofFn]
                simp only [haccM]
                rw [getD_snoc_ne _ _ _ _ (by rw [hacc₁_len]; exact hieq),
                    getD_snoc_ne _ _ _ _ (by rw [hlen_w]; exact hieq)]
                exact hinv1.2.2 i hi
            have hinv2 := elimInvOn_pass {(ℓ : ℕ)} m (List.ofFn x) gs₂ _ accM hgs₂_notℓ hinvM
            dsimp only
            rw [hsplit, bWires_append (gs₁ ++ [g₁]) gs₂]
            exact hinv2
          have heval_acc : ∀ x : Fin m → Bool,
              statVal (bWires acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) =
                F (Function.update x p false) := by
            intro x
            have h := ((hinv_all x).2.2 C.output (by simpa using hout_ne_ℓ)).2
            rw [h]
            exact (hev _).trans (hkill x _)
          have hst_val : statValid (m + acc.2.length) (acc.1.getD C.output (Sum.inl false)) :=
            ((hinv_all (fun _ => false)).2.2 C.output (by simpa using hout_ne_ℓ)).1
          have hout_ne_w1 : C.output ≠ w₁ := by
            intro heq
            have hw1acc : acc.1.getD C.output (Sum.inl false) = Sum.inl c₁ := by
              rw [heq, hacc, elimPass_getD_lt _ _ _ _ _ (by simp [haccM, hacc₁_len])]
              exact haccM_w₁
            obtain ⟨x, x', hne⟩ := hncp
            have hx := heval_acc x; have hx' := heval_acc x'
            rw [hw1acc] at hx hx'
            exact hne (hx.symm.trans hx')
          have hex₂ := hex₂_w₁ hout_ne_w1
          have htot : C.gates.length = gs₁.length + 1 + gs₂.length := by rw [hsplit]; simp; omega
          have hlen3 : acc.2.length + 3 ≤ C.gates.length := by
            by_cases hp1 : ∃ g ∈ gs₁, readsWire (p : ℕ) g = true
            · have h1 : acc₁.2.length + 1 ≤ gs₁.length := by
                have := elimPass_len_lt m (p : ℕ) gs₁ (initVar m p false, [])
                  (by simp [initVar])
                  ⟨false, by rw [initVar, ofFn_getD_lt _ _ _ p.isLt]; simp⟩ hp1
                rw [← hacc₁] at this; simpa using this
              have h2 : acc.2.length + 1 ≤ accM.2.length + gs₂.length :=
                elimPass_len_lt m w₁ gs₂ accM (by simp [haccM, hacc₁_len]) ⟨c₁, haccM_w₁⟩ hex₂
              have hM : accM.2.length = acc₁.2.length := rfl
              omega
            · push Not at hp1
              have hgs₁_nop : ∀ g ∈ gs₁, readsWire (p : ℕ) g = false := fun g hg =>
                Bool.eq_false_iff.2 (hp1 g hg)
              have hp2 : ∃ g ∈ gs₂, readsWire (p : ℕ) g = true := by
                by_contra hnop2
                push Not at hnop2
                have hgs₂_nop : ∀ g ∈ gs₂, readsWire (p : ℕ) g = false := fun g hg =>
                  Bool.eq_false_iff.2 (hnop2 g hg)
                set x0 : Fin m → Bool := fun _ => false
                have h3 := h3sub x0 (fun _ _ _ _ => rfl)
                set f00 := Function.update (Function.update x0 p false) ℓ false
                set f10 := Function.update (Function.update x0 p true) ℓ false
                set f11 := Function.update (Function.update x0 p true) ℓ true
                have hw1_indep : ∀ y : Fin m → Bool,
                    (bWires (gs₁ ++ [g₁]) (List.ofFn (Function.update y q false))).getD w₁ false =
                    (bWires (gs₁ ++ [g₁]) (List.ofFn (Function.update y q true))).getD w₁ false →
                    False → False := fun _ _ h => h
                have hpig : ∀ a b c : Bool, a = b ∨ a = c ∨ b = c := by decide
                set v00 := (bWires (gs₁ ++ [g₁]) (List.ofFn (Function.update f00 q false))).getD w₁ false
                set v10 := (bWires (gs₁ ++ [g₁]) (List.ofFn (Function.update f10 q false))).getD w₁ false
                set v11 := (bWires (gs₁ ++ [g₁]) (List.ofFn (Function.update f11 q false))).getD w₁ false
                set w00 := (bWires (gs₁ ++ [g₁]) (List.ofFn (Function.update f00 q true))).getD w₁ false
                set w10 := (bWires (gs₁ ++ [g₁]) (List.ofFn (Function.update f10 q true))).getD w₁ false
                set w11 := (bWires (gs₁ ++ [g₁]) (List.ofFn (Function.update f11 q true))).getD w₁ false
                have hsub_eq : ∀ (y₁ y₂ : Fin m → Bool) (bq : Bool),
                    (∀ i, i ≠ ℓ → i ≠ p → y₁ i = y₂ i) →
                    (bWires (gs₁ ++ [g₁]) (List.ofFn (Function.update y₁ q bq))).getD w₁ false =
                    (bWires (gs₁ ++ [g₁]) (List.ofFn (Function.update y₂ q bq))).getD w₁ false →
                    F (Function.update y₁ q bq) = F (Function.update y₂ q bq) := by
                  intro y₁ y₂ bq hy hw1eq
                  rw [← hev, ← hev]
                  show (bWires C.gates _).getD C.output false = (bWires C.gates _).getD C.output false
                  rw [hsplit]
                  exact bWires_pair_factor gs₁ gs₂ g₁ ℓ p
                    (fun g hg => ⟨hgs₁no g hg, hgs₁_nop g hg⟩)
                    (fun g hg => ⟨hgs₂no g hg, hgs₂_nop g hg⟩)
                    (Function.update y₁ q bq) (Function.update y₂ q bq)
                    (fun i hiℓ hip => by
                      by_cases hiq : i = q
                      · subst hiq; simp
                      · rw [Function.update_of_ne hiq, Function.update_of_ne hiq]; exact hy i hiℓ hip)
                    hw1eq C.output hout_ne_ℓ hout_ne_p
                have hf00_10 : ∀ i, i ≠ ℓ → i ≠ p → f00 i = f10 i := by
                  intro i hiℓ hip; simp [f00, f10, Function.update_of_ne hiℓ, Function.update_of_ne hip]
                have hf00_11 : ∀ i, i ≠ ℓ → i ≠ p → f00 i = f11 i := by
                  intro i hiℓ hip; simp [f00, f11, Function.update_of_ne hiℓ, Function.update_of_ne hip]
                have hf10_11 : ∀ i, i ≠ ℓ → i ≠ p → f10 i = f11 i := by
                  intro i hiℓ hip; simp [f10, f11, Function.update_of_ne hiℓ, Function.update_of_ne hip]
                have hne_00_11_f : v00 ≠ v11 := fun heq => by
                  have := hsub_eq f00 f11 false hf00_11 heq
                  rw [h3.1, h3.2.2.2.2.1] at this; exact Bool.false_ne_true this
                have hne_10_11_f : v10 ≠ v11 := fun heq => by
                  have := hsub_eq f10 f11 false hf10_11 heq
                  rw [h3.2.2.1, h3.2.2.2.2.1] at this; exact Bool.false_ne_true this
                have hne_00_10_t : w00 ≠ w10 := fun heq => by
                  have := hsub_eq f00 f10 true hf00_10 heq
                  rw [h3.2.1, h3.2.2.2.1] at this; exact Bool.false_ne_true this
                have hne_00_11_t : w00 ≠ w11 := fun heq => by
                  have := hsub_eq f00 f11 true hf00_11 heq
                  rw [h3.2.1, h3.2.2.2.2.2] at this; exact Bool.false_ne_true this
                have h00_10_f : v00 = v10 := by
                  rcases hpig v00 v10 v11 with h | h | h
                  · exact h
                  · exact absurd h hne_00_11_f
                  · exact absurd h hne_10_11_f
                have h10_11_t : w10 = w11 := by
                  rcases hpig w00 w10 w11 with h | h | h
                  · exact absurd h hne_00_10_t
                  · exact absurd h hne_00_11_t
                  · exact h
                have h_g1_eq : ∀ (y₁ y₂ : Fin m → Bool) (bq : Bool),
                    (bWires (gs₁ ++ [g₁]) (List.ofFn (Function.update y₁ q bq))).getD w₁ false =
                    g₁.op ((bWires gs₁ (List.ofFn (Function.update y₁ q bq))).getD g₁.left false)
                          ((bWires gs₁ (List.ofFn (Function.update y₁ q bq))).getD g₁.right false) := by
                  intro y₁ _ bq
                  rw [bWires_append, bWires_cons, bWires_nil,
                      getD_snoc_eq _ _ _ _ (by rw [bWires_length, List.length_ofFn])]
                have hag_gs1 : ∀ (y₁ y₂ : Fin m → Bool) (bq : Bool),
                    (∀ i, i ≠ ℓ → i ≠ p → y₁ i = y₂ i) →
                    (bWires gs₁ (List.ofFn (Function.update y₁ q bq))).getD u false =
                    (bWires gs₁ (List.ofFn (Function.update y₂ q bq))).getD u false := by
                  intro y₁ y₂ bq hy
                  have h := bWires_agree gs₁ {(ℓ : ℕ), (p : ℕ)}
                    (List.ofFn (Function.update y₁ q bq)) (List.ofFn (Function.update y₂ q bq))
                    (by simp) (by intro b hb; rcases hb with rfl | rfl <;> simp)
                    (by
                      intro i hi
                      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hi
                      by_cases him : i < m
                      · have h1 : (⟨i, him⟩ : Fin m) ≠ ℓ := fun e => hi.1 (congrArg Fin.val e)
                        have h2 : (⟨i, him⟩ : Fin m) ≠ p := fun e => hi.2 (congrArg Fin.val e)
                        rw [ofFn_getD_lt _ _ _ him, ofFn_getD_lt _ _ _ him]
                        by_cases hiq : (⟨i, him⟩ : Fin m) = q
                        · subst hiq; simp
                        · rw [Function.update_of_ne hiq, Function.update_of_ne hiq]; exact hy _ h1 h2
                      · rw [List.getD_eq_default _ _ (by simp; omega),
                            List.getD_eq_default _ _ (by simp; omega)])
                    (by
                      intro g hg
                      have h1 := hgs₁no g hg; have h2 := hgs₁_nop g hg
                      simp only [readsWire, decide_eq_false_iff_not, not_or] at h1 h2
                      exact ⟨by simp [h1.1, h2.1], by simp [h1.2, h2.2]⟩)
                  by_cases hup : u = (p : ℕ)
                  · exfalso
                    have hval_u : ∀ y : Fin m → Bool,
                        (bWires gs₁ (List.ofFn (Function.update y q true))).getD u false = y p := by
                      intro y
                      rw [hup, bWires_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ p.isLt,
                          Function.update_of_ne hqp.symm]
                    have hval_ℓ' : ∀ y : Fin m → Bool,
                        (bWires gs₁ (List.ofFn (Function.update y q true))).getD (ℓ : ℕ) false = y ℓ := by
                      intro y
                      rw [bWires_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ ℓ.isLt,
                          Function.update_of_ne hqℓ.symm]
                    have hw10_e : w10 = g₁.op (if g₁.left = (ℓ : ℕ) then f10 ℓ else f10 p)
                        (if g₁.left = (ℓ : ℕ) then f10 p else f10 ℓ) := by
                      dsimp only [w10]
                      rw [h_g1_eq f10 f10 true]
                      rcases hg₁reads with hl | hr
                      · have hru : g₁.right = u := by simp [hu, hl]
                        simp only [hl, hru, hval_ℓ', hval_u, ↓reduceIte]
                      · have hlne : g₁.left ≠ (ℓ : ℕ) := fun hl => hnotboth hl hr
                        have hlu : g₁.left = u := by simp [hu, hlne]
                        simp only [hr, hlu, hval_ℓ', hval_u, hu_ne_ℓ, ↓reduceIte]
                    have hw11_e : w11 = g₁.op (if g₁.left = (ℓ : ℕ) then f11 ℓ else f11 p)
                        (if g₁.left = (ℓ : ℕ) then f11 p else f11 ℓ) := by
                      dsimp only [w11]
                      rw [h_g1_eq f11 f11 true]
                      rcases hg₁reads with hl | hr
                      · have hru : g₁.right = u := by simp [hu, hl]
                        simp only [hl, hru, hval_ℓ', hval_u, ↓reduceIte]
                      · have hlne : g₁.left ≠ (ℓ : ℕ) := fun hl => hnotboth hl hr
                        have hlu : g₁.left = u := by simp [hu, hlne]
                        simp only [hr, hlu, hval_ℓ', hval_u, hu_ne_ℓ, ↓reduceIte]
                    have hf10_l : f10 ℓ = false := by simp [f10]
                    have hf10_p : f10 p = true := by simp [f10, hℓp.symm]
                    have hf11_l : f11 ℓ = true := by simp [f11]
                    have hf11_p : f11 p = true := by simp [f11, hℓp.symm]
                    rw [hw10_e, hw11_e, hf10_l, hf10_p, hf11_l, hf11_p] at h10_11_t
                    by_cases hl : g₁.left = (ℓ : ℕ)
                    · simp only [hl, ↓reduceIte] at h10_11_t; exact hR1 h10_11_t
                    · simp only [hl, ↓reduceIte] at h10_11_t; exact hL1 h10_11_t
                  · exact h.2 u (by simp [hu_ne_ℓ, hup])
                have heq_w00_w10 : w00 = w10 := by
                  dsimp only [w00, w10]
                  rw [h_g1_eq f00 f00 true, h_g1_eq f10 f10 true]
                  have hℓ00 : (bWires gs₁ (List.ofFn (Function.update f00 q true))).getD (ℓ : ℕ) false = false := by
                    rw [bWires_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ ℓ.isLt,
                        Function.update_of_ne hqℓ.symm]; simp [f00]
                  have hℓ10 : (bWires gs₁ (List.ofFn (Function.update f10 q true))).getD (ℓ : ℕ) false = false := by
                    rw [bWires_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ ℓ.isLt,
                        Function.update_of_ne hqℓ.symm]; simp [f10]
                  have hu01 := hag_gs1 f00 f10 true hf00_10
                  rcases hg₁reads with hl | hr
                  · have hru : g₁.right = u := by simp [hu, hl]
                    rw [hl, hru, hℓ00, hℓ10, hu01]
                  · have hlne : g₁.left ≠ (ℓ : ℕ) := fun hl => hnotboth hl hr
                    have hlu : g₁.left = u := by simp [hu, hlne]
                    rw [hr, hlu, hℓ00, hℓ10, hu01]
                exact hne_00_10_t heq_w00_w10
              set P2 : BinaryGate → Bool := fun g => readsWire (p : ℕ) g || readsWire w₁ g with hP2
              have hlen1 : acc₁.2.length ≤ gs₁.length := by
                have := elimPass_len m gs₁ (initVar m p false, [])
                rw [← hacc₁] at this; simpa using this
              have hM_len : accM.2.length = acc₁.2.length := rfl
              by_cases h2ge2 : 2 ≤ (gs₂.filter P2).length
              · have h2 := elimPass_len_two_pred m P2 gs₂ accM
                  (fun g _ hPg acc' hacc' => by
                    simp only [hP2, Bool.or_eq_true] at hPg
                    rcases hPg with hrp | hrw
                    · exact elimStep_none_of_reads m (p : ℕ) acc' g
                        ⟨false, by rw [hacc' (p : ℕ) (by simp [haccM, hacc₁_len]; omega)]; exact haccM_p⟩ hrp
                    · exact elimStep_none_of_reads m w₁ acc' g
                        ⟨c₁, by rw [hacc' w₁ (by simp [haccM, hacc₁_len])]; exact haccM_w₁⟩ hrw)
                  h2ge2
                rw [← hacc] at h2
                omega
              · have h2pos : 1 ≤ (gs₂.filter P2).length := by
                  obtain ⟨g, hg, hrg⟩ := hex₂
                  have hmem : g ∈ gs₂.filter P2 := List.mem_filter.2 ⟨hg, by simp [hP2, hrg]⟩
                  exact List.length_pos_of_mem hmem
                have h2one : (gs₂.filter P2).length = 1 := by omega
                obtain ⟨gs₂a, g₂, gs₂b, hsplit2, hg₂P, hgs₂a_no, hgs₂b_no⟩ :=
                  list_split_unique_filter P2 gs₂ h2one
                have hg₂_p : readsWire (p : ℕ) g₂ = true := by
                  obtain ⟨g, hg, hrp⟩ := hp2
                  rw [hsplit2] at hg
                  simp only [List.mem_append, List.mem_singleton] at hg
                  rcases hg with (hg | rfl) | hg
                  · have := hgs₂a_no g hg; simp [hP2, hrp] at this
                  · exact hrp
                  · have := hgs₂b_no g hg; simp [hP2, hrp] at this
                have hg₂_w₁ : readsWire w₁ g₂ = true := by
                  obtain ⟨g, hg, hrw⟩ := hex₂
                  rw [hsplit2] at hg
                  simp only [List.mem_append, List.mem_singleton] at hg
                  rcases hg with (hg | rfl) | hg
                  · have := hgs₂a_no g hg; simp [hP2, hrw] at this
                  · exact hrw
                  · have := hgs₂b_no g hg; simp [hP2, hrw] at this
                set acc2a := elimPass m gs₂a accM with hacc2a
                set acc2M := elimStep m acc2a g₂ with hacc2M
                have hacc_eq2 : acc = elimPass m gs₂b acc2M := by
                  rw [hacc, hsplit2, elimPass_append, elimPass_append, ← hacc2a,
                      elimPass_cons, elimPass_nil, ← hacc2M]
                set w₂ := w₁ + 1 + gs₂a.length with hw₂
                have hacc2a_len : acc2a.1.length = w₂ := by
                  rw [hacc2a, elimPass_fst_len]; simp [haccM, hacc₁_len, hw₂]
                have hacc2a_p : acc2a.1.getD (p : ℕ) (Sum.inl false) = Sum.inl false := by
                  rw [hacc2a, elimPass_getD_lt _ _ _ _ _ (by simp [haccM, hacc₁_len]; omega)]
                  exact haccM_p
                have hacc2a_w₁ : acc2a.1.getD w₁ (Sum.inl false) = Sum.inl c₁ := by
                  rw [hacc2a, elimPass_getD_lt _ _ _ _ _ (by simp [haccM, hacc₁_len])]
                  exact haccM_w₁
                have hp_ne_w1 : (p : ℕ) ≠ w₁ := by omega
                have hg₂_both : (g₂.left = (p : ℕ) ∧ g₂.right = w₁) ∨ (g₂.left = w₁ ∧ g₂.right = (p : ℕ)) := by
                  simp only [readsWire, decide_eq_true_eq] at hg₂_p hg₂_w₁
                  rcases hg₂_p with h1 | h1 <;> rcases hg₂_w₁ with h2 | h2
                  · exact absurd (h1.symm.trans h2) hp_ne_w1
                  · exact Or.inl ⟨h1, h2⟩
                  · exact Or.inr ⟨h2, h1⟩
                  · exact absurd (h1.symm.trans h2) hp_ne_w1
                obtain ⟨c₂, hc₂⟩ : ∃ c₂ : Bool,
                    simplifyBGate g₂.op (m + acc2a.2.length)
                      (acc2a.1.getD g₂.left (Sum.inl false)) (acc2a.1.getD g₂.right (Sum.inl false)) =
                      (none, Sum.inl c₂) := by
                  rcases hg₂_both with ⟨hl, hr⟩ | ⟨hl, hr⟩
                  · exact ⟨g₂.op false c₁, by rw [hl, hr, hacc2a_p, hacc2a_w₁]; rfl⟩
                  · exact ⟨g₂.op c₁ false, by rw [hl, hr, hacc2a_w₁, hacc2a_p]; rfl⟩
                have hacc2M_len : acc2M.2.length = acc2a.2.length := by
                  simp only [hacc2M, elimStep, hc₂, Option.toList_none, List.append_nil]
                have hacc2M_w₂ : acc2M.1.getD w₂ (Sum.inl false) = Sum.inl c₂ := by
                  simp only [hacc2M, elimStep, hc₂]
                  exact getD_snoc_eq _ _ _ _ hacc2a_len.symm
                have hout_ne_w2 : C.output ≠ w₂ := by
                  intro heq
                  have hw2acc : acc.1.getD C.output (Sum.inl false) = Sum.inl c₂ := by
                    rw [heq, hacc_eq2, elimPass_getD_lt _ _ _ _ _ (by simp [hacc2M, elimStep, hacc2a_len])]
                    exact hacc2M_w₂
                  obtain ⟨x, x', hne⟩ := hncp
                  have hx := heval_acc x; have hx' := heval_acc x'
                  rw [hw2acc] at hx hx'
                  exact hne (hx.symm.trans hx')
                have hex2b : ∃ g ∈ gs₂b, readsWire w₂ g = true := by
                  by_contra hnob
                  push_neg at hnob
                  obtain ⟨x, hne⟩ := hdep
                  have hag1 := bWires_agree gs₁ {(ℓ : ℕ)}
                    (List.ofFn (Function.update x ℓ false)) (List.ofFn (Function.update x ℓ true))
                    (by simp) (by intro u hu; simp at hu; subst hu; simp)
                    (by
                      intro i hi; simp at hi
                      by_cases hlt : i < m
                      · have hne' : (⟨i, hlt⟩ : Fin m) ≠ ℓ := fun h => hi (congrArg Fin.val h)
                        rw [ofFn_getD_lt _ _ _ hlt, ofFn_getD_lt _ _ _ hlt,
                            Function.update_of_ne hne', Function.update_of_ne hne']
                      · rw [List.getD_eq_default _ _ (by simp; omega),
                            List.getD_eq_default _ _ (by simp; omega)])
                    (by
                      intro g hg
                      have hr := hgs₁no g hg
                      simp only [readsWire, decide_eq_false_iff_not, not_or] at hr
                      exact ⟨by simpa using hr.1, by simpa using hr.2⟩)
                  have hag2a := bWires_agree gs₂a {(ℓ : ℕ), w₁}
                    (bWires (gs₁ ++ [g₁]) (List.ofFn (Function.update x ℓ false)))
                    (bWires (gs₁ ++ [g₁]) (List.ofFn (Function.update x ℓ true)))
                    (by simp [bWires_length])
                    (by intro b hb; rw [bWires_length, List.length_ofFn, List.length_append, List.length_singleton]; rcases hb with rfl | rfl <;> omega)
                    (by
                      intro i hi
                      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hi
                      rw [bWires_append, bWires_cons, bWires_nil, bWires_append, bWires_cons, bWires_nil]
                      have hl1 : (bWires gs₁ (List.ofFn (Function.update x ℓ false))).length = w₁ := by
                        rw [bWires_length, List.length_ofFn]
                      have hl2 : (bWires gs₁ (List.ofFn (Function.update x ℓ true))).length = w₁ := by
                        rw [bWires_length, List.length_ofFn]
                      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
                      exact hag1.2 i (by simpa using hi.1))
                    (by
                      intro g hg
                      have hr1 := hgs₂no g (by rw [hsplit2]; simp [hg])
                      have hr2 := hgs₂a_no g hg
                      simp only [hP2, Bool.or_eq_false_iff, readsWire, decide_eq_false_iff_not, not_or] at hr1 hr2
                      exact ⟨by simp [hr1.1, hr2.2.1], by simp [hr1.2, hr2.2.2]⟩)
                  have hag2b := bWires_agree gs₂b {(ℓ : ℕ), w₁, w₂}
                    (bWires (gs₁ ++ [g₁] ++ gs₂a ++ [g₂]) (List.ofFn (Function.update x ℓ false)))
                    (bWires (gs₁ ++ [g₁] ++ gs₂a ++ [g₂]) (List.ofFn (Function.update x ℓ true)))
                    (by simp [bWires_length])
                    (by intro b hb; rw [bWires_length, List.length_ofFn]; rcases hb with rfl | rfl | rfl <;> simp <;> omega)
                    (by
                      intro i hi
                      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hi
                      rw [bWires_append (gs₁ ++ [g₁] ++ gs₂a) [g₂], bWires_cons, bWires_nil,
                          bWires_append (gs₁ ++ [g₁] ++ gs₂a) [g₂], bWires_cons, bWires_nil]
                      have hl1 : (bWires (gs₁ ++ [g₁] ++ gs₂a) (List.ofFn (Function.update x ℓ false))).length = w₂ := by
                        simp [bWires_length, hw₂, hw₁]; omega
                      have hl2 : (bWires (gs₁ ++ [g₁] ++ gs₂a) (List.ofFn (Function.update x ℓ true))).length = w₂ := by
                        simp [bWires_length, hw₂, hw₁]; omega
                      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega),
                          bWires_append (gs₁ ++ [g₁]) gs₂a, bWires_append (gs₁ ++ [g₁]) gs₂a]
                      exact hag2a.2 i (by simp [hi.1, hi.2.1]))
                    (by
                      intro g hg
                      have hr1 := hgs₂no g (by rw [hsplit2]; simp [hg])
                      have hr2 := hgs₂b_no g hg
                      have hr3 := hnob g hg
                      simp only [hP2, ne_eq, Bool.or_eq_false_iff, readsWire, decide_eq_false_iff_not,
                        decide_eq_true_eq, not_or] at hr1 hr2 hr3
                      exact ⟨by simp [hr1.1, hr2.2.1, hr3.1], by simp [hr1.2, hr2.2.2, hr3.2]⟩)
                  have hEq : (bWires C.gates (List.ofFn (Function.update x ℓ false))).getD C.output false =
                      (bWires C.gates (List.ofFn (Function.update x ℓ true))).getD C.output false := by
                    have hcat : C.gates = (gs₁ ++ [g₁] ++ gs₂a ++ [g₂]) ++ gs₂b := by
                      rw [hsplit, hsplit2]; simp [List.append_assoc]
                    rw [hcat, bWires_append (gs₁ ++ [g₁] ++ gs₂a ++ [g₂]) gs₂b,
                        bWires_append (gs₁ ++ [g₁] ++ gs₂a ++ [g₂]) gs₂b]
                    exact hag2b.2 C.output (by simp [hout_ne_ℓ, hout_ne_w1, hout_ne_w2])
                  exact hne ((hev _).symm.trans (hEq.trans (hev _)))
                have h2a_len : acc2a.2.length ≤ accM.2.length + gs₂a.length :=
                  elimPass_len m gs₂a accM
                have h2b_len : acc.2.length + 1 ≤ acc2M.2.length + gs₂b.length := by
                  rw [hacc_eq2]
                  exact elimPass_len_lt m w₂ gs₂b acc2M (by simp [hacc2M, elimStep, hacc2a_len])
                    ⟨c₂, hacc2M_w₂⟩ hex2b
                have hgs2_len : gs₂.length = gs₂a.length + 1 + gs₂b.length := by rw [hsplit2]; simp; omega
                omega
          exact Or.inr (Or.inr ⟨by omega,
            circuit_from_stat acc.2 (acc.1.getD C.output (Sum.inl false)) (by omega)
              hst_val heval_acc hncp hF0_p⟩)

open PEqualNP.CircuitLowerBounds

-- Without a separate unary gate, a binary gate can read a complemented wire directly.
-- This variant of the encoding in L-meta-237 uses one out-of-range wire for constants.
def encode (dummy : ℕ) (g : Gate) : BinaryGate :=
  match g.inputs with
  | [] => ⟨fun _ _ => g.op.eval [], dummy, dummy⟩
  | [i] => ⟨fun a _ => g.op.eval [a], i, dummy⟩
  | i :: j :: _ => match g.op with
    | .not => ⟨fun a _ => !a, i, dummy⟩
    | _ => ⟨fun a b => g.op.eval [a, b], i, j⟩

theorem encode_value (dummy : ℕ) (g : Gate) (h : g.inputs.length ≤ 2) (w : List Bool) :
    (encode dummy g).op (w.getD (encode dummy g).left false) (w.getD (encode dummy g).right false) =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
  rcases g with ⟨op, _ | ⟨i, _ | ⟨j, _ | ⟨k, ks⟩⟩⟩⟩
  · rfl
  · rfl
  · cases op <;> rfl
  · simp at h

theorem encode_not_right (d : ℕ) (g : Gate) (hn : g.op = .not) : (encode d g).right = d := by
  cases g with
  | mk op inputs =>
    change op = .not at hn
    subst op
    rcases inputs with _ | ⟨a, _ | ⟨b,l⟩⟩ <;> rfl

theorem encode_run (d : ℕ) (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2) (w : List Bool) :
    bWires (gs.map (encode d)) w = (Circuit.mk gs 0).wires w := by
  unfold Circuit.wires
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons, bWires_cons]
    rw [encode_value d g (h g List.mem_cons_self)]
    exact ih (fun a ha => h a (List.mem_cons_of_mem _ ha)) _

def nonNot (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true

def binaryCount (gs : List Gate) : ℕ := (gs.filter nonNot).length

theorem omit_not (m d : ℕ) (acc : List Stat × List BinaryGate) (gs : List Gate)
    (room : acc.1.length + gs.length ≤ d) :
    (elimPass m (gs.map (encode d)) acc).2.length ≤ acc.2.length + binaryCount gs := by
  induction gs generalizing acc with
  | nil => simp [binaryCount, elimPass_nil]
  | cons g gs ih =>
    let acc' := elimStep m acc (encode d g)
    have hr : acc'.1.length + gs.length ≤ d := by
      have h₁ : acc'.1.length = acc.1.length + 1 := by simp [acc', elimStep]
      simp only [List.length_cons] at room
      omega
    have hs := ih acc' hr
    change (elimPass m (gs.map (encode d)) acc').2.length ≤ _
    by_cases h : g.op = .not
    · have hi : (acc.1.getD d (Sum.inl false) : Stat) = .inl false :=
        List.getD_eq_default _ _ (by simp only [List.length_cons] at room; omega)
      have hn : acc'.2.length = acc.2.length := by
        simp only [acc', elimStep, encode_not_right d g h, hi, simplifyBGate_none_right, Option.toList_none, List.append_nil]
      simpa [hn, binaryCount, nonNot, h] using hs
    · have hb : nonNot g = true := by
        obtain ⟨op, l⟩ := g
        change op ≠ .not at h
        cases op <;> simp_all [nonNot]
      have hn : acc'.2.length ≤ acc.2.length + 1 := by
        simp only [acc', elimStep, List.length_append]
        cases (simplifyBGate (encode d g).op (m + acc.2.length)
          (acc.1.getD (encode d g).left (.inl false))
          (acc.1.getD (encode d g).right (.inl false))).1 <;> simp
      have hlen : binaryCount (g::gs) = binaryCount gs + 1 := by simp [binaryCount, hb]
      omega

def identityStats (m : ℕ) : List Stat :=
  List.ofFn fun i : Fin m => Sum.inr (i.val, false)

theorem identityStats_correct {m : ℕ} (x : Fin m → Bool) :
    ElimInvOn ∅ m (List.ofFn x) (List.ofFn x) (identityStats m, []) := by
  refine ⟨by simp, by simp [identityStats], ?_⟩
  intro i _
  by_cases hi : i < m
  · have ei : (identityStats m).getD i (.inl false) = .inr (i,false) := by
      unfold identityStats
      rw [ofFn_getD_lt _ _ _ hi]
    rw [ei, bWires_nil]
    exact ⟨hi, by simp only [statVal, Bool.xor_false]⟩
  · have e : (identityStats m).getD i (.inl false) = .inl false :=
      List.getD_eq_default _ _ (by simpa [identityStats] using Nat.le_of_not_gt hi)
    have ex : (List.ofFn x).getD i false = false :=
      List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)
    rw [e, ex]
    exact ⟨trivial, rfl⟩

set_option maxRecDepth 100000 in
theorem freeNot {m : ℕ} {f : (Fin m → Bool) → Bool} (gs : List Gate) (o : ℕ)
    (harg : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (h : ∀ x : Fin m → Bool, (⟨gs,o⟩ : Circuit).eval (List.ofFn x) = f x)
    (nonconstant : ∃ x y, f x ≠ f y) (zero : f (fun _ => false) = false) :
    HasBinarySize m f (binaryCount gs) := by
  let d := m + gs.length
  let bs := gs.map (encode d)
  let p : List Stat × List BinaryGate := (identityStats m, [])
  let a := elimPass m bs p
  let st := a.1.getD o (Sum.inl false)
  have cap : a.2.length ≤ binaryCount gs := by
    have hr := omit_not m d p gs (by simp [d, p, identityStats])
    simpa [a, bs, p] using hr
  have inv (x : Fin m → Bool) :
      ElimInvOn ∅ m (List.ofFn x) (bWires bs (List.ofFn x)) a :=
    elimInvOn_pass ∅ m _ bs _ p (by simp) (identityStats_correct x)
  have v := ((inv (fun _ => false)).2.2 o (by simp)).1
  have e (x : Fin m → Bool) : statVal (bWires a.2 (List.ofFn x)) st = f x := by
    have e' := ((inv x).2.2 o (by simp)).2
    change statVal (bWires a.2 (List.ofFn x)) st = (bWires bs (List.ofFn x)).getD o false at e'
    rw [show bWires bs (List.ofFn x) = (⟨gs,o⟩ : Circuit).wires (List.ofFn x) from
      encode_run d gs harg (List.ofFn x)] at e'
    exact e'.trans (h x)
  exact circuit_from_stat _ _ cap v e nonconstant zero

def graph (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 3 && x 4) ||
  (x 0 && x 5) || (x 2 && x 5) || (x 3 && x 5) || (x 0 && x 6) ||
  (x 1 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)

def G1 (x : Fin 7 → Bool) : Bool := graph (Function.update x 1 false)

def G12 (b : Bool) (x : Fin 7 → Bool) : Bool := G1 (Function.update x 2 b)

def core (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 6) ||
  (x 3 && x 4) || (x 3 && x 6) || (x 4 && x 6)

theorem core_eq (b : Bool) : (fun x => G12 b (Function.update x 5 false)) = core := by
  funext x
  simp [G12, G1, graph, core, Function.update_apply, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

theorem core_eq' : (fun x => G1 (Function.update x 5 false)) = core := by
  funext x
  simp [G1, graph, core, Function.update_apply, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

set_option maxRecDepth 100000 in
theorem graphLower (coreBound : ∀ t, HasBinarySize 7 core t → 7 ≤ t)
    (s : ℕ) (fit : HasBinarySize 7 graph s) : 11 ≤ s := by
  have dep1 : ∃ x : Fin 7 → Bool, graph (Function.update x 1 false) ≠ graph (Function.update x 1 true) :=
    ⟨fun i => decide (i = 4), by decide +kernel⟩
  have nc1 : ∃ x y : Fin 7 → Bool, graph (Function.update x 1 false) ≠ graph (Function.update y 1 false) :=
    ⟨fun _ => false, fun _ => true, by decide +kernel⟩
  obtain ⟨s1, fit1⟩ := elim_one_var 1 false fit dep1 nc1 (by decide +kernel)
  change HasBinarySize 7 G1 (s-1) at fit1
  have dep2 : ∃ x : Fin 7 → Bool, G1 (Function.update x 2 false) ≠ G1 (Function.update x 2 true) :=
    ⟨fun i => decide (i = 5), by decide +kernel⟩
  have nc2 (b : Bool) : ∃ x y : Fin 7 → Bool, G1 (Function.update x 2 b) ≠ G1 (Function.update y 2 b) := by
    refine ⟨fun _ => false, fun _ => true, ?_⟩
    cases b <;> decide +kernel
  have nc5 : ∃ x y : Fin 7 → Bool, G1 (Function.update x 5 false) ≠ G1 (Function.update y 5 false) :=
    ⟨fun _ => false, fun _ => true, by decide +kernel⟩
  have independent (x : Fin 7 → Bool) (b : Bool) :
      G1 (Function.update (Function.update x 5 false) 2 b) = G1 (Function.update x 5 false) := by
    simp [G1, graph, Function.update_apply]
  have shape (x : Fin 7 → Bool) (hx : ∀ i, i ≠ 2 → i ≠ 5 → i ≠ 0 → x i = false) :
      G1 (Function.update (Function.update (Function.update x 5 false) 2 false) 0 false) = false ∧
      G1 (Function.update (Function.update (Function.update x 5 false) 2 false) 0 true) = false ∧
      G1 (Function.update (Function.update (Function.update x 5 true) 2 false) 0 false) = false ∧
      G1 (Function.update (Function.update (Function.update x 5 true) 2 false) 0 true) = true ∧
      G1 (Function.update (Function.update (Function.update x 5 true) 2 true) 0 false) = true ∧
      G1 (Function.update (Function.update (Function.update x 5 true) 2 true) 0 true) = true := by
    have h3 := hx 3 (by decide) (by decide) (by decide)
    have h4 := hx 4 (by decide) (by decide) (by decide)
    have h6 := hx 6 (by decide) (by decide) (by decide)
    simp [G1, graph, Function.update_apply, h3, h4, h6]
  have branches := elim_leaf_parent (ℓ := 2) (p := 5) (q := 0)
    (by decide) (by decide) (by decide) fit1 dep2 (nc2 false) (nc2 true) nc5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) independent shape
  have cutParent (b : Bool) (h : HasBinarySize 7 (G12 b) ((s-1)-2)) : 11 ≤ s := by
    have dep5 : ∃ x : Fin 7 → Bool, G12 b (Function.update x 5 false) ≠ G12 b (Function.update x 5 true) := by
      refine ⟨fun i => decide (i = 0), ?_⟩
      cases b <;> decide +kernel
    have nc : ∃ x y : Fin 7 → Bool, G12 b (Function.update x 5 false) ≠ G12 b (Function.update y 5 false) := by
      refine ⟨fun _ => false, fun _ => true, ?_⟩
      cases b <;> decide +kernel
    have z : G12 b (Function.update (fun _ => false) 5 false) = false := by
      cases b <;> decide +kernel
    obtain ⟨hsmall, hc⟩ := elim_one_var 5 false h dep5 nc z
    rw [core_eq b] at hc
    have lb := coreBound _ hc
    omega
  rcases branches with ⟨_, fit2⟩ | ⟨_, fit2⟩ | ⟨_, rest⟩
  · exact cutParent false fit2
  · exact cutParent true fit2
  · rw [core_eq'] at rest
    have lb := coreBound _ rest
    omega

end PEqualNP.Outside.L_meta_10930.Cut


-- The live-wire search adapts L-meta-9564 and its referenced sources (Apache-2.0).

namespace PEqualNP.Outside.L_meta_10930.Small

-- The signed live-wire search follows L-meta-8463 and L-meta-1449, Apache-2.0.

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

set_option maxRecDepth 100000 in
theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

set_option maxRecDepth 100000 in
theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

set_option maxRecDepth 100000 in
theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

set_option maxRecDepth 100000 in
theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

-- Oppositely labeled assignments are paired across the upper and lower halves.
abbrev W := BitVec 110
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x, x ^^^ y]
def sep (x : W) : BitVec 55 := ((x >>> 55) ^^^ x).setWidth 55
def cuts (ws : List W) : BitVec 55 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 55) ++ (0 : BitVec 55)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

set_option maxRecDepth 100000 in
theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

set_option maxRecDepth 100000 in
theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 55) (w : W) : Prop :=
  w.getLsbD (55+i.val) ≠ w.getLsbD i.val

set_option maxRecDepth 100000 in
theorem ops_differs (i : Fin 55) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 55+i.val < 110 := by omega
  have hi' : i.val < 110 := by omega
  rcases hz with rfl | rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

set_option maxRecDepth 100000 in
theorem cuts_spec (ws : List W) (i : Fin 55) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

set_option maxRecDepth 100000 in
theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 55)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

set_option maxRecDepth 100000 in
theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b, BitVec.xor_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

set_option maxRecDepth 100000 in
theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

set_option maxRecDepth 100000 in
theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

set_option maxRecDepth 100000 in
theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

set_option maxRecDepth 100000 in
theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hg hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) ws

set_option maxRecDepth 100000 in
theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', optimized_complete hg n ws _ hnd (by omega : n+1-ws.length+ws.length=n+1) hl']⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

set_option maxRecDepth 100000 in
theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

set_option maxRecDepth 100000 in
theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

set_option maxRecDepth 100000 in
theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 100000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 110 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 110)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

set_option maxRecDepth 100000 in
theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 110) (z : W) : Bool := z[k.val]
set_option maxRecDepth 100000 in
private theorem read_bit (w : List W) (i : ℕ) (k : Fin 110) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

theorem xor_flip_left (a b : W) : (~~~a) ^^^ b = ~~~(a ^^^ b) := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  simp only [BitVec.getElem_xor, BitVec.getElem_not]
  cases a[j] <;> cases b[j] <;> rfl

theorem xor_flip_right (a b : W) : a ^^^ (~~~b) = ~~~(a ^^^ b) := by
  rw [BitVec.xor_comm, xor_flip_left, BitVec.xor_comm a b]

theorem xor_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ^^^ y) := by
  rcases hx with rfl | rfl | ⟨a, ha, ea⟩
  · rw [show (0 : W) ^^^ y = y by simp]
    exact .inl hy
  · rw [xor_flip_left]
    rw [show (0 : W) ^^^ y = y by simp]
    exact .inl (holds_not hy)
  rcases hy with rfl | rfl | ⟨b, hb, eb⟩
  · rw [show x ^^^ (0 : W) = x by simp]
    exact .inl (.inr (.inr ⟨a,ha,ea⟩))
  · rw [xor_flip_right]
    rw [show x ^^^ (0 : W) = x by simp]
    exact .inl (holds_not (.inr (.inr ⟨a,ha,ea⟩)))
  have combine : reachable av (a ^^^ b) := by
    by_cases e : a=b
    · subst b
      rw [show a ^^^ a = (0 : W) by simp]
      exact .inl (.inl rfl)
    · exact .inr ⟨a,ha,b,hb,e,a ^^^ b,by simp [basicOps,ops],.inr (.inr ⟨a ^^^ b,
        Finset.mem_insert_self .., .inl rfl⟩)⟩
  rcases ea with e | e <;> rcases eb with f | f <;> rw [e,f]
  · exact combine
  · rw [xor_flip_right]; exact reachable_not combine
  · rw [xor_flip_left]; exact reachable_not combine
  · rw [xor_flip_left, xor_flip_right, BitVec.not_not]; exact combine

-- All sixteen Boolean functions of two arguments, grouped by output polarity.
def allFns : List (Bool → Bool → Bool) :=
  [fun _ _ => false, fun _ _ => true, fun a _ => a, fun a _ => !a, fun _ b => b, fun _ b => !b,
   fun a b => a && b, fun a b => !(a && b), fun a b => a || b, fun a b => !(a || b),
   fun a b => a && !b, fun a b => !(a && !b), fun a b => b && !a, fun a b => !(b && !a),
   fun a b => xor a b, fun a b => !(xor a b)]

theorem allFns_full : ∀ f : Bool → Bool → Bool, f ∈ allFns := by decide +kernel

theorem opWord (f : Bool → Bool → Bool) {av : Finset W} {x y : W}
    (hx : holds av x) (hy : holds av y) :
    ∃ z, reachable av z ∧ ∀ k : Fin 110, bit k z = f (bit k x) (bit k y) := by
  have hf := allFns_full f
  simp only [allFns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with f0 | f1 | f2 | f3 | f4 | f5 | f6 | f7 | f8 | f9 | f10 | f11 | f12 | f13 | f14 | f15
  · refine ⟨0, .inl (.inl rfl), ?_⟩; intro k; simp [f0, bit]
  · refine ⟨~~~0, .inl (.inr (.inl rfl)), ?_⟩
    intro k
    rw [f1]
    change (BitVec.allOnes 110)[k.val] = true
    rw [BitVec.getElem_allOnes]
  · exact ⟨x, .inl hx, fun k => by rw [f2]⟩
  · refine ⟨~~~x, .inl (holds_not hx), ?_⟩; intro k; simp [f3, bit]
  · exact ⟨y, .inl hy, fun k => by rw [f4]⟩
  · refine ⟨~~~y, .inl (holds_not hy), ?_⟩; intro k; simp [f5, bit]
  · refine ⟨x &&& y, and_reach hx hy, ?_⟩; intro k; simp [f6, bit]
  · refine ⟨~~~(x &&& y), reachable_not (and_reach hx hy), ?_⟩; intro k; simp [f7, bit]
  · refine ⟨x ||| y, or_reach hx hy, ?_⟩; intro k; simp [f8, bit]
  · refine ⟨~~~(x ||| y), reachable_not (or_reach hx hy), ?_⟩; intro k; simp [f9, bit]
  · refine ⟨x &&& ~~~y, and_reach hx (holds_not hy), ?_⟩; intro k; simp [f10, bit]
  · refine ⟨~~~(x &&& ~~~y), reachable_not (and_reach hx (holds_not hy)), ?_⟩; intro k; simp [f11, bit]
  · refine ⟨y &&& ~~~x, and_reach hy (holds_not hx), ?_⟩; intro k; simp [f12, bit]
  · refine ⟨~~~(y &&& ~~~x), reachable_not (and_reach hy (holds_not hx)), ?_⟩; intro k; simp [f13, bit]
  · refine ⟨x ^^^ y, xor_reach hx hy, ?_⟩; intro k; simp [f14, bit]
  · refine ⟨~~~(x ^^^ y), reachable_not (xor_reach hx hy), ?_⟩; intro k; simp [f15, bit]

private def binaryStep (w : List Bool) (g : BinaryGate) : List Bool :=
  w ++ [g.op (w.getD g.left false) (w.getD g.right false)]

set_option maxRecDepth 100000 in
theorem compileBinary (gs : List BinaryGate) (out : ℕ)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl binaryStep (w.map (bit k))).getD out false = bit k (~~~goal)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t gs.length av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    obtain ⟨z, hz, hspec⟩ := opWord g.op (available_read hw g.left) (available_read hw g.right)
    have he' : ∀ k, (gs.foldl binaryStep ((w ++ [z]).map (bit k))).getD out false = bit k (~~~goal) := by
      intro k
      simpa only [List.map_append, List.map_cons, List.map_nil, List.foldl_cons, binaryStep, read_bit,
        hspec] using he k
    have cont (A : Finset W) (old : ∀ u ∈ w, holds A u) (new : holds A z) :=
      ih (w ++ [z]) A (by
        intro u hu
        rcases List.mem_append.mp hu with h | h
        · exact old u h
        · exact (List.mem_singleton.mp h) ▸ new) he'
    rcases hz with h | ⟨a,ha,b,hb,ne,new,op,rep⟩
    · obtain ⟨t,ht,run⟩ := cont av hw h
      exact ⟨t,ht,Or.inl run⟩
    · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
      exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩

def rows : List W := [0x1ffc0055bab756eadd5b, 0xffe0000066dcdb9b736e6d, 0x7ff0000000078ef1de3bc778e, 0x3ff800000000007f0fe1fc3f87f0]
def inputRows : List W := [rows.getD 0 0,0,0,rows.getD 1 0,rows.getD 2 0,0,rows.getD 3 0]
def coreform (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 6) ||
  (x 3 && x 4) || (x 3 && x 6) || (x 4 && x 6)
def outWord : W :=
  (inputRows.getD 0 0 &&& inputRows.getD 3 0) |||
  (inputRows.getD 0 0 &&& inputRows.getD 4 0) |||
  (inputRows.getD 0 0 &&& inputRows.getD 6 0) |||
  (inputRows.getD 3 0 &&& inputRows.getD 4 0) |||
  (inputRows.getD 3 0 &&& inputRows.getD 6 0) |||
  (inputRows.getD 4 0 &&& inputRows.getD 6 0)
theorem outWord_eq : outWord = ~~~goal := by decide +kernel
theorem spec (k : Fin 110) :
    coreform (fun i => bit k (inputRows.getD i.val 0)) = bit k (~~~goal) := by
  rw [← outWord_eq]
  simp only [outWord, coreform, bit, BitVec.getElem_and, BitVec.getElem_or]
  rfl

def selectState (p : Bool) (e : ℕ × List W) : List (ℕ × List W) :=
  if p then [e] else []

theorem select_any (p : Bool) (e : ℕ × List W) (f : (ℕ × List W) → Bool) :
    (selectState p e).any f = (p && f e) := by
  cases p <;> simp [selectState]

def transitions (extra : ℕ) (a b : W) (r : List W) : List (ℕ × List W) :=
  (ops a b).flatMap fun z =>
    let v := sep z ||| cuts r
    selectState (v == -1) (extra,z :: r) ++
      selectState (extra != 0 && ((v ||| sep a) == -1)) (extra-1,z :: a :: r) ++
      selectState (extra != 0 && ((v ||| sep b) == -1)) (extra-1,z :: b :: r) ++
      selectState (decide (extra ≥ 2) && ((v ||| sep a ||| sep b) == -1)) (extra-2,z :: a :: b :: r)

theorem dispatch_any (next : ℕ → List W → Bool) (extra : ℕ) (a b : W) (r : List W) :
    (transitions extra a b r).any (fun w => next w.1 w.2) = dispatch extra next a b r := by
  unfold transitions dispatch
  simp only [List.any_flatMap, List.any_append, select_any]
  apply congrArg ((ops a b).any)
  funext z
  cases h : extra != 0 <;> simp [h, Bool.or_assoc, Bool.and_assoc]

def expand (extra : ℕ) (ws : List W) : List (ℕ × List W) :=
  (pairs ws).flatMap fun (a,b,r) => transitions extra a b r

theorem expand_eq (k extra : ℕ) (ws : List W) :
    optimized (k+1) extra ws =
    ((ws == [goal] || ws == [~~~goal]) || (expand extra ws).any (fun w => optimized k w.1 w.2)) := by
  simp only [optimized, expand, List.any_flatMap]
  congr 1
  apply congrArg ((pairs ws).any)
  funext tuple
  obtain ⟨a,b,r⟩ := tuple
  exact (dispatch_any (optimized k) extra a b r).symm

def work : List (ℕ × List W) := expand 3 rows
def workEval (p : ℕ × List W) : Bool := optimized 5 p.1 p.2
def piece (i : ℕ) : Bool := workEval (work.getD i (0,[]))
theorem work_len : work.length = 42 := by decide +kernel

theorem onlyFull : rows.sublists.all (fun ws => !(cuts ws == -1) || (ws == rows)) = true := by
  decide +kernel

theorem impossible_of_pieces (every : ∀ i < work.length, piece i = false) : search 6 rows = false := by
  have hbad : work.any workEval = false := by
    apply List.any_eq_false.2
    intro w hw
    obtain ⟨i,hi,e⟩ := List.mem_iff_getElem.1 hw
    have h := every i hi
    unfold piece at h
    rw [List.getD_eq_getElem _ _ hi, e] at h
    simp [h]
  have check : optimized 6 3 rows = false := by
    rw [expand_eq 5 3 rows]
    change ((rows == [goal] || rows == [~~~goal]) || work.any workEval) = false
    have no : (rows == [goal] || rows == [~~~goal]) = false := by decide +kernel
    simp only [hbad,no]
    rfl
  unfold search
  apply List.any_eq_false.2
  intro ws hw
  cases h : (cuts ws == -1)
  · simp [h]
  · have e := List.all_eq_true.1 onlyFull ws hw
    simp only [h, Bool.not_true, Bool.false_or, beq_iff_eq] at e
    subst ws
    have step : 6 + 1 - rows.length = 3 := rfl
    simp only [step, check, Bool.and_false, Bool.false_eq_true, not_false_eq_true]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check0 : piece 0 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check1 : piece 1 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check2 : piece 2 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check3 : piece 3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check4 : piece 4 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check5 : piece 5 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check6 : piece 6 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check7 : piece 7 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check8 : piece 8 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check9 : piece 9 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check10 : piece 10 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check11 : piece 11 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check12 : piece 12 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check13 : piece 13 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check14 : piece 14 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check15 : piece 15 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check16 : piece 16 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check17 : piece 17 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check18 : piece 18 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check19 : piece 19 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check20 : piece 20 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check21 : piece 21 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check22 : piece 22 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check23 : piece 23 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check24 : piece 24 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check25 : piece 25 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check26 : piece 26 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check27 : piece 27 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check28 : piece 28 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check29 : piece 29 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check30 : piece 30 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check31 : piece 31 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check32 : piece 32 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check33 : piece 33 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check34 : piece 34 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check35 : piece 35 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check36 : piece 36 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check37 : piece 37 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check38 : piece 38 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check39 : piece 39 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check40 : piece 40 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check41 : piece 41 = false := by decide +kernel

set_option maxHeartbeats 6000000 in
theorem impossible : search 6 rows = false := by
  apply impossible_of_pieces
  intro i hi
  rw [work_len] at hi
  interval_cases i
  · exact check0
  · exact check1
  · exact check2
  · exact check3
  · exact check4
  · exact check5
  · exact check6
  · exact check7
  · exact check8
  · exact check9
  · exact check10
  · exact check11
  · exact check12
  · exact check13
  · exact check14
  · exact check15
  · exact check16
  · exact check17
  · exact check18
  · exact check19
  · exact check20
  · exact check21
  · exact check22
  · exact check23
  · exact check24
  · exact check25
  · exact check26
  · exact check27
  · exact check28
  · exact check29
  · exact check30
  · exact check31
  · exact check32
  · exact check33
  · exact check34
  · exact check35
  · exact check36
  · exact check37
  · exact check38
  · exact check39
  · exact check40
  · exact check41


set_option maxRecDepth 100000 in
theorem coreBound (s : ℕ) (fit : HasBinarySize 7 coreform s) : 7 ≤ s := by
  by_contra! small
  obtain ⟨C,hsize,hfits⟩ := fit
  have subset : ∀ v ∈ inputRows, v = 0 ∨ v ∈ rows := by
    have readMem (i : ℕ) (hi : i < rows.length) : rows.getD i 0 ∈ rows := by
      rw [List.getD_eq_getElem _ _ hi]
      exact List.getElem_mem hi
    intro v hv
    simp only [inputRows, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with h | h | h | h | h | h | h
    · right; rw [h]; exact readMem 0 (by decide)
    · exact .inl h
    · exact .inl h
    · right; rw [h]; exact readMem 1 (by decide)
    · right; rw [h]; exact readMem 2 (by decide)
    · exact .inl h
    · right; rw [h]; exact readMem 3 (by decide)

  have hi : ∀ u ∈ inputRows, holds rows.toFinset u := by
    intro u hu
    rcases subset u hu with z | r
    · exact .inl z
    · exact .inr (.inr ⟨u, List.mem_toFinset.mpr r, .inl rfl⟩)
  have ev (k : Fin 110) :
      (C.gates.foldl binaryStep (inputRows.map (bit k))).getD C.output false = bit k (~~~goal) := by
    let x (i : Fin 7) := bit k (inputRows.getD i.val 0)
    have same : List.ofFn x = inputRows.map (bit k) := by
      apply List.ext_getElem
      · rfl
      · intro i hi hj
        have hlt : i < inputRows.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some, x]
    change C.eval (inputRows.map (bit k)) = bit k (~~~goal)
    rw [← same, hfits x]
    exact spec k
  obtain ⟨t, ht, run⟩ := compileBinary C.gates C.output inputRows rows.toFinset hi ev
  have lift {a c : ℕ} (h : a ≤ c) (hr : build basicOps t a rows.toFinset) :
      build basicOps t c rows.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  have lb : C.gates.length ≤ 6 := by change C.gates.length ≤ s at hsize; omega
  exact Bool.noConfusion (impossible.symm.trans (search_complete ht 6 rows (by decide) (lift lb run)))

end PEqualNP.Outside.L_meta_10930.Small


namespace PEqualNP.Outside.L_meta_10930

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A circuit with a NOT uses at most one fewer binary operation than its length.
-- Fixing input 1 and eliminating the leaf 2 with its neighbour 5 reduce the
-- signed lower bound to the two-of-four function on the remaining four vertices.
private def witness : List Gate :=
  [⟨.or, [0, 3]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [7, 1]⟩, ⟨.and, [9, 8]⟩,
   ⟨.or, [7, 2]⟩, ⟨.or, [11, 6]⟩, ⟨.and, [12, 5]⟩, ⟨.and, [4, 6]⟩,
   ⟨.and, [0, 3]⟩, ⟨.or, [10, 13]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [16, 17]⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem graph_spec : ∀ x : Fin 7 → Bool, Cut.graph x = decide (∃ i < ([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem witness_eq : ∀ x : Fin 7 → Bool, Circuit.eval ⟨witness, 18⟩ (List.ofFn x) = Cut.graph x := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem replacement : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o allowed _ realizes
  by_cases anyNot : ∃ g ∈ gates, g.op = .not
  · have fit : HasBinarySize 7 Cut.graph (Cut.binaryCount gates) := by
      refine Cut.freeNot gates o (fun g hg => (allowed g hg).2)
        (fun x => (realizes x).trans (graph_spec x).symm) ?_ (by decide +kernel)
      exact ⟨fun _ => false, fun _ => true, by decide +kernel⟩
    have lower := Cut.graphLower Small.coreBound _ fit
    obtain ⟨g, hg, hn⟩ := anyNot
    have comparison : Cut.binaryCount gates < gates.length := by
      exact List.length_filter_lt_length_iff_exists.2 ⟨g, hg, by simp [Cut.nonNot, hn]⟩
    refine ⟨witness, 18, by simp [witness], ?_, fun x => (witness_eq x).trans (graph_spec x)⟩
    change 12 ≤ gates.length
    omega
  · refine ⟨gates, o, ?_, le_rfl, realizes⟩
    intro g hg
    refine ⟨?_, (allowed g hg).2⟩
    rcases (allowed g hg).1 with ha | ho | hn
    · exact Or.inl ha
    · exact Or.inr ho
    · exact (anyNot ⟨g, hg, hn⟩).elim

end PEqualNP.Outside.L_meta_10930

theorem PEqualNP.Outside.L_meta_10930 :
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  PEqualNP.Outside.L_meta_10930.replacement
