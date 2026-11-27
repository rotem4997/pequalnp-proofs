import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

private lemma wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

private lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

private lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  induction gs₁ generalizing w with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, wiresFrom_cons, ih]

private lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    simp
    omega

private lemma getD_snoc_lt {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

private lemma getD_snoc_eq {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
    (l ++ [x]).getD i d = x := by
  subst hi
  simp [List.getD]

private lemma getD_snoc_ne {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i ≠ l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  by_cases hlt : i < l.length
  · exact getD_snoc_lt l x d i hlt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresFrom_cons, ih _ (by simp; omega)]
    exact getD_snoc_lt _ _ _ _ hi

private lemma wiresFrom_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (wiresFrom gs w).getD (w.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (wiresFrom (gs.take j) w).getD i false) := by
  have hsplit : gs = gs.take j ++ [gs[j]] ++ gs.drop (j + 1) := by
    have h1 := List.take_append_drop j gs
    have h2 : gs.drop j = gs[j] :: gs.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simpa only [List.append_assoc, List.singleton_append] using h1.symm
  conv_lhs => rw [hsplit, wiresFrom_append, wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
  have hlen : (wiresFrom (gs.take j) w).length = w.length + j := by
    rw [wiresFrom_length, List.length_take, Nat.min_eq_left (by omega)]
  rw [wiresFrom_getD_lt _ _ _ (by simp [hlen])]
  exact getD_snoc_eq _ _ _ _ hlen.symm

private def OkGate (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private def NOkGate (g : Gate) : Prop :=
  OkGate g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

private def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

private lemma normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

private lemma normGate_nok (g : Gate) (h : OkGate g) : NOkGate (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this
    exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this
    exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩
    · simp [normGate]
    · simp [normGate]

private lemma wiresFrom_norm (gs : List Gate) (w : List Bool) :
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, wiresFrom_cons, wiresFrom_cons, normGate_eval, ih]

private def statVal (w : List Bool) : Bool ⊕ ℕ → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

private def statValid (m : ℕ) : Bool ⊕ ℕ → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

private def simpNot (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

private def simpAnd (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

private def simpOr (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

private def simplifyGate (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    Option Gate × (Bool ⊕ ℕ) :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

private lemma simplifyGate_ok (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    ∀ g ∈ (simplifyGate op m ins).1, OkGate g := by
  intro g hg
  cases op <;> simp only [simplifyGate] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg; simp [OkGate]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg; simp [OkGate]
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg
    subst hg; simp [OkGate]
  · simp at hg
  · simp at hg

private lemma simplifyGate_nok (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    ∀ g ∈ (simplifyGate op m ins).1, NOkGate g := by
  intro g hg
  cases op <;> simp only [simplifyGate] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg; exact ⟨⟨Or.inl rfl, by simp⟩, by simp⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg; exact ⟨⟨Or.inr (Or.inl rfl), by simp⟩, by simp⟩
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg
    subst hg; exact ⟨⟨Or.inr (Or.inr rfl), by simp⟩, by simp⟩
  · simp at hg
  · simp at hg

private lemma simplifyGate_none_of_const (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplifyGate op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplifyGate, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplifyGate, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplifyGate, simpNot]

private lemma simplifyGate_and_false (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hlen : ins.length ≤ 2) (hf : Sum.inl false ∈ ins) :
    simplifyGate GateOp.and m ins = (none, Sum.inl false) := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
  · simp at hf
  · cases a <;> simp_all [simplifyGate, simpAnd]
  · cases a with
    | inl c =>
      cases b with
      | inl d => cases c <;> cases d <;> simp_all [simplifyGate, simpAnd]
      | inr j => cases c <;> simp_all [simplifyGate, simpAnd]
    | inr i =>
      cases b with
      | inl d => cases d <;> simp_all [simplifyGate, simpAnd]
      | inr j => simp at hf
  · simp at hlen

private lemma simplifyGate_or_true (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hlen : ins.length ≤ 2) (ht : Sum.inl true ∈ ins) :
    simplifyGate GateOp.or m ins = (none, Sum.inl true) := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
  · simp at ht
  · cases a <;> simp_all [simplifyGate, simpOr]
  · cases a with
    | inl c =>
      cases b with
      | inl d => cases c <;> cases d <;> simp_all [simplifyGate, simpOr]
      | inr j => cases c <;> simp_all [simplifyGate, simpOr]
    | inr i =>
      cases b with
      | inl d => cases d <;> simp_all [simplifyGate, simpOr]
      | inr j => simp at ht
  · simp at hlen

private lemma simplifyGate_not_const (m : ℕ) (c : Bool) :
    simplifyGate GateOp.not m [Sum.inl c] = (none, Sum.inl (!c)) := rfl

private lemma simplifyGate_both_const (op : GateOp) (m : ℕ) (c d : Bool)
    (hop : op = GateOp.and ∨ op = GateOp.or) :
    ∃ e : Bool, simplifyGate op m [Sum.inl c, Sum.inl d] = (none, Sum.inl e) := by
  rcases hop with rfl | rfl
  · exact ⟨c && d, rfl⟩
  · exact ⟨c || d, rfl⟩

private lemma simplifyGate_sound (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List (Bool ⊕ ℕ)) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplifyGate op w.length ins).1.toList.length)
      (simplifyGate op w.length ins).2 ∧
    statVal (wiresFrom (simplifyGate op w.length ins).1.toList w)
      (simplifyGate op w.length ins).2 = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplifyGate, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval]
        | inr j => cases c <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
      | inr i =>
        cases b with
        | inl d => cases d <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
        | inr j => simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplifyGate, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval]
        | inr j => cases c <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
      | inr i =>
        cases b with
        | inl d => cases d <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
        | inr j => simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplifyGate, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

private lemma simplifyGate_mem_inputs_of_some (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (g : Gate) (hg : (simplifyGate op m ins).1 = some g) (w : ℕ) (hw : w ∈ g.inputs) :
    Sum.inr w ∈ ins := by
  cases op <;> simp only [simplifyGate] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg; simp at hw; rcases hw with rfl | rfl <;> simp
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg; simp at hw; rcases hw with rfl | rfl <;> simp
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg
    subst hg; simp at hw; subst hw; simp
  · simp at hg
  · simp at hg

private lemma simplifyGate_out_wire_mem (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (w : ℕ) (hw : (simplifyGate op m ins).2 = Sum.inr w) :
    w = m ∨ Sum.inr w ∈ ins := by
  cases op <;> simp only [simplifyGate] at hw
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hw
    · right; simp [hw]
    · split_ifs at hw <;> simp at hw; right; simp [hw]
    · split_ifs at hw <;> simp at hw; right; simp [hw]
    · left; exact hw.symm
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hw
    · right; simp [hw]
    · split_ifs at hw <;> simp at hw; right; simp [hw]
    · split_ifs at hw <;> simp at hw; right; simp [hw]
    · left; exact hw.symm
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hw
    left; exact hw.symm
  · simp at hw
  · simp at hw

private lemma simplifyGate_some_snd (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (g : Gate) (hg : (simplifyGate op m ins).1 = some g) :
    (simplifyGate op m ins).2 = Sum.inr m := by
  cases op <;> simp only [simplifyGate] at hg ⊢
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg ⊢
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg ⊢
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg ⊢
  · simp at hg
  · simp at hg

private def elimStep (m : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  let r := simplifyGate g.op (m + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
  (acc.1 ++ [r.2], acc.2 ++ r.1.toList)

private def elimPass (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  gs.foldl (elimStep m) acc

private lemma elimPass_nil (m : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m [] acc = acc := rfl

private lemma elimPass_cons (m : ℕ) (g : Gate) (gs : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m (g :: gs) acc = elimPass m gs (elimStep m acc g) := rfl

private lemma elimPass_append (m : ℕ) (gs₁ gs₂ : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m (gs₁ ++ gs₂) acc = elimPass m gs₂ (elimPass m gs₁ acc) := by
  induction gs₁ generalizing acc with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, elimPass_cons, ih]

private lemma elimPass_fst_len (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    (elimPass m gs acc).1.length = acc.1.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
    rw [elimPass_cons, ih]
    simp [elimStep]
    omega

private lemma elimPass_getD_lt (m k : ℕ) (d : Bool ⊕ ℕ) (gs : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) (hk : k < acc.1.length) :
    (elimPass m gs acc).1.getD k d = acc.1.getD k d := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    rw [elimPass_cons, ih _ (by simp [elimStep]; omega)]
    exact getD_snoc_lt _ _ _ _ hk

private lemma toList_opt_len_le {α : Type*} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

private lemma elimPass_ok (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (h : ∀ g ∈ acc.2, OkGate g) : ∀ g ∈ (elimPass m gs acc).2, OkGate g := by
  induction gs generalizing acc with
  | nil => exact h
  | cons g gs ih =>
    rw [elimPass_cons]
    apply ih
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplifyGate_ok _ _ _ g' (by simpa using h1)

private lemma elimPass_len (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    (elimPass m gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
    rw [elimPass_cons, List.length_cons]
    have h1 := ih (elimStep m acc g)
    have h2 : (elimStep m acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_opt_len_le (simplifyGate g.op (m + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    omega

private def elimState (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) (j : ℕ) :
    List (Bool ⊕ ℕ) × List Gate :=
  elimPass m (gs.take j) acc

private lemma elimState_zero (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimState m gs acc 0 = acc := rfl

private lemma elimState_end (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimState m gs acc gs.length = elimPass m gs acc := by
  simp [elimState]

private lemma elimState_succ (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (j : ℕ) (hj : j < gs.length) :
    elimState m gs acc (j + 1) = elimStep m (elimState m gs acc j) gs[j] := by
  unfold elimState
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, elimPass_append,
    elimPass_cons, elimPass_nil]

private lemma elimState_fst_len (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (j : ℕ) (hj : j ≤ gs.length) :
    (elimState m gs acc j).1.length = acc.1.length + j := by
  rw [elimState, elimPass_fst_len, List.length_take, Nat.min_eq_left hj]

private lemma elimState_getD_mono (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (j k i : ℕ) (d : Bool ⊕ ℕ) (hjk : j ≤ k) (hk : k ≤ gs.length) (hi : i < acc.1.length + j) :
    (elimState m gs acc k).1.getD i d = (elimState m gs acc j).1.getD i d := by
  have htake : gs.take k = gs.take j ++ (gs.drop j).take (k - j) := by
    have h1 := List.take_add (l := gs) (i := j) (j := k - j)
    rw [show j + (k - j) = k by omega] at h1
    exact h1
  rw [elimState, htake, elimPass_append]
  exact elimPass_getD_lt m i d _ _ (by rw [elimPass_fst_len, List.length_take, Nat.min_eq_left (by omega)]; exact hi)

private lemma elimState_snd_mono (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (j k : ℕ) (hjk : j ≤ k) :
    (elimState m gs acc j).2.length ≤ (elimState m gs acc k).2.length := by
  induction k with
  | zero =>
    have hj0 : j = 0 := by omega
    subst hj0; exact le_rfl
  | succ k ih =>
    by_cases h : j = k + 1
    · subst h; exact le_rfl
    · have h1 := ih (by omega)
      by_cases hk : k < gs.length
      · rw [elimState_succ m gs acc k hk]
        simp only [elimStep, List.length_append]
        omega
      · have htk : gs.take (k + 1) = gs.take k := by
          rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
        change (elimState m gs acc j).2.length ≤ (elimPass m (gs.take (k + 1)) acc).2.length
        rw [htk]
        exact h1

private lemma elimState_getD_at (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (j : ℕ) (hj : j < gs.length) :
    (elimState m gs acc (j + 1)).1.getD (acc.1.length + j) (Sum.inl false) =
      (simplifyGate gs[j].op (m + (elimState m gs acc j).2.length)
        (gs[j].inputs.map fun i => (elimState m gs acc j).1.getD i (Sum.inl false))).2 := by
  rw [elimState_succ m gs acc j hj]
  simp only [elimStep]
  exact getD_snoc_eq _ _ _ _ (elimState_fst_len m gs acc j (by omega)).symm

private def elimDropped (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) : Finset ℕ :=
  (Finset.range gs.length).filter (fun j =>
    if hj : j < gs.length then
      (simplifyGate gs[j].op (m + (elimState m gs acc j).2.length)
        (gs[j].inputs.map fun i => (elimState m gs acc j).1.getD i (Sum.inl false))).1.isNone
    else false)

private lemma elimPass_card_dropped (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    (elimPass m gs acc).2.length + (elimDropped m gs acc).card = acc.2.length + gs.length := by
  suffices ∀ k ≤ gs.length,
      (elimState m gs acc k).2.length +
        ((Finset.range k).filter (fun j =>
          if hj : j < gs.length then
            (simplifyGate gs[j].op (m + (elimState m gs acc j).2.length)
              (gs[j].inputs.map fun i => (elimState m gs acc j).1.getD i (Sum.inl false))).1.isNone
          else false)).card = acc.2.length + k by
    simpa [elimState_end, elimDropped] using this gs.length le_rfl
  intro k
  induction k with
  | zero =>
    intro _
    simp [elimState_zero]
  | succ k ih =>
    intro hk
    have hklt : k < gs.length := by omega
    have hih := ih (by omega)
    rw [Finset.range_add_one, Finset.filter_insert]
    have hnot : k ∉ (Finset.range k).filter (fun j =>
        if hj : j < gs.length then
          (simplifyGate gs[j].op (m + (elimState m gs acc j).2.length)
            (gs[j].inputs.map fun i => (elimState m gs acc j).1.getD i (Sum.inl false))).1.isNone
        else false) := by
      simp
    rw [elimState_succ m gs acc k hklt]
    simp only [elimStep, List.length_append, hklt, ↓reduceDIte]
    cases hopt : (simplifyGate gs[k].op (m + (elimState m gs acc k).2.length)
        (gs[k].inputs.map fun i => (elimState m gs acc k).1.getD i (Sum.inl false))).1 with
    | none =>
      simp only [Option.toList_none, List.length_nil, Option.isNone_none, ↓reduceIte,
        Finset.card_insert_of_notMem hnot]
      omega
    | some g =>
      simp only [Option.toList_some, List.length_singleton, Option.isNone_some, Bool.false_eq_true,
        ↓reduceIte]
      omega

private lemma mem_elimDropped_of_const (m : ℕ) (gs : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) (j : ℕ) (hj : j < gs.length)
    (hnok : NOkGate gs[j]) (i : ℕ) (hi : i ∈ gs[j].inputs)
    (hc : ∃ c, (elimState m gs acc j).1.getD i (Sum.inl false) = Sum.inl c) :
    j ∈ elimDropped m gs acc := by
  rw [elimDropped, Finset.mem_filter, Finset.mem_range]
  refine ⟨hj, ?_⟩
  simp only [hj, ↓reduceDIte]
  obtain ⟨c, hc⟩ := hc
  have hnone : (simplifyGate gs[j].op (m + (elimState m gs acc j).2.length)
      (gs[j].inputs.map fun i => (elimState m gs acc j).1.getD i (Sum.inl false))).1 = none := by
    apply simplifyGate_none_of_const
    · exact hnok.1.1
    · simpa using hnok.1.2
    · intro h; simpa using hnok.2 h
    · exact ⟨c, List.mem_map.2 ⟨i, hi, hc⟩⟩
  rw [hnone]
  rfl

private lemma elimPass_len_lt (m k : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, NOkGate g) (hk : k < acc.1.length)
    (hc : ∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c)
    (hex : ∃ g ∈ gs, k ∈ g.inputs) :
    (elimPass m gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  obtain ⟨g, hg, hkg⟩ := hex
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
  have hmem : j ∈ elimDropped m gs acc := by
    apply mem_elimDropped_of_const m gs acc j hj (hok _ (List.getElem_mem hj)) k hkg
    obtain ⟨c, hc⟩ := hc
    exact ⟨c, by rw [elimState_getD_mono m gs acc 0 j k _ (Nat.zero_le _) (by omega) (by omega), elimState_zero]; exact hc⟩
  have hcard : 1 ≤ (elimDropped m gs acc).card := Finset.one_le_card.2 ⟨j, hmem⟩
  have htot := elimPass_card_dropped m gs acc
  omega

private lemma elimPass_len_two (m k : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, NOkGate g) (hk : k < acc.1.length)
    (hc : ∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c)
    (htwo : 2 ≤ (gs.filter (fun g => decide (k ∈ g.inputs))).length) :
    (elimPass m gs acc).2.length + 2 ≤ acc.2.length + gs.length := by
  have hsub : (Finset.range gs.length).filter (fun j => if hj : j < gs.length then k ∈ gs[j].inputs else false)
      ⊆ elimDropped m gs acc := by
    intro j hj'
    rw [Finset.mem_filter, Finset.mem_range] at hj'
    obtain ⟨hj, hkin⟩ := hj'
    simp only [hj, ↓reduceDIte] at hkin
    apply mem_elimDropped_of_const m gs acc j hj (hok _ (List.getElem_mem hj)) k hkin
    obtain ⟨c, hc⟩ := hc
    exact ⟨c, by rw [elimState_getD_mono m gs acc 0 j k _ (Nat.zero_le _) (by omega) (by omega), elimState_zero]; exact hc⟩
  have hcnt : ((Finset.range gs.length).filter
      (fun j => if hj : j < gs.length then k ∈ gs[j].inputs else false)).card =
      (gs.filter (fun g => decide (k ∈ g.inputs))).length := by
    clear hsub htwo hc hk hok acc m
    induction gs with
    | nil => simp
    | cons g gs ih =>
      rw [List.filter_cons]
      have hbij : ((Finset.range (g :: gs).length).filter
          (fun j => if hj : j < (g :: gs).length then k ∈ (g :: gs)[j].inputs else false)).card =
          (if k ∈ g.inputs then 1 else 0) +
          ((Finset.range gs.length).filter
            (fun j => if hj : j < gs.length then k ∈ gs[j].inputs else false)).card := by
        have hsplit : (Finset.range (g :: gs).length).filter
            (fun j => if hj : j < (g :: gs).length then k ∈ (g :: gs)[j].inputs else false) =
            (if k ∈ g.inputs then {0} else ∅) ∪
            ((Finset.range gs.length).filter
              (fun j => if hj : j < gs.length then k ∈ gs[j].inputs else false)).image (· + 1) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_image,
            List.length_cons]
          cases j with
          | zero =>
            by_cases hk0 : k ∈ g.inputs <;> simp [hk0]
          | succ j =>
            by_cases hk0 : k ∈ g.inputs <;> by_cases hlt : j < gs.length <;> simp [hk0, hlt]
        rw [hsplit, Finset.card_union_of_disjoint]
        · rw [Finset.card_image_of_injective _ (fun _ _ h => by omega)]
          split_ifs <;> simp
        · rw [Finset.disjoint_left]
          intro x hx1 hx2
          simp only [Finset.mem_image] at hx2
          obtain ⟨y, _, rfl⟩ := hx2
          split_ifs at hx1 <;> simp at hx1
      rw [hbij, ih]
      by_cases hkg : k ∈ g.inputs <;> simp [hkg] <;> omega
  have hle := Finset.card_le_card hsub
  have htot := elimPass_card_dropped m gs acc
  omega

private def ElimInv (m : ℕ) (w_in w_old : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) : Prop :=
  w_in.length = m ∧
  acc.1.length = w_old.length ∧
  ∀ i : ℕ,
    statValid (m + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 w_in) (acc.1.getD i (Sum.inl false)) = w_old.getD i false

private lemma elimInv_step (m : ℕ) (w_in w_old : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) (hok : OkGate g)
    (hinv : ElimInv m w_in w_old acc) :
    ElimInv m w_in (w_old ++ [g.op.eval (g.inputs.map fun i => w_old.getD i false)])
      (elimStep m acc g) := by
  obtain ⟨hwin, hlen, hi⟩ := hinv
  set w_new := wiresFrom acc.2 w_in with hw_new
  have hw_len : w_new.length = m + acc.2.length := by
    rw [hw_new, wiresFrom_length, hwin]
  set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
  have hins_len : ins.length ≤ 2 := by simp [hins]; exact hok.2
  have hins_val : ∀ s ∈ ins, statValid w_new.length s := by
    intro s hs
    obtain ⟨idx, _, rfl⟩ := List.mem_map.1 hs
    rw [hw_len]
    exact (hi idx).1
  have hsound := simplifyGate_sound g.op hok.1 w_new ins hins_len hins_val
  rw [hw_len] at hsound
  refine ⟨hwin, by simp [elimStep, hlen], ?_⟩
  intro i
  simp only [elimStep]
  by_cases hieq : i = acc.1.length
  · rw [getD_snoc_eq _ _ _ _ hieq, getD_snoc_eq _ _ _ _ (by omega)]
    refine ⟨?_, ?_⟩
    · rw [List.length_append, ← Nat.add_assoc]
      exact hsound.1
    · rw [wiresFrom_append, ← hw_new, hsound.2]
      congr 1
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro idx _
      exact (hi idx).2
  · rw [getD_snoc_ne _ _ _ _ hieq, getD_snoc_ne _ _ _ _ (by omega)]
    have ⟨hv, hval⟩ := hi i
    refine ⟨?_, ?_⟩
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c => trivial
      | inr j =>
        rw [hst] at hv
        simp only [statValid, List.length_append] at hv ⊢
        omega
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c =>
        rw [hst] at hval
        exact hval
      | inr j =>
        rw [hst] at hv hval
        simp only [statValid] at hv
        simp only [statVal] at hval ⊢
        rw [wiresFrom_append, ← hw_new, wiresFrom_getD_lt _ _ _ (by omega)]
        exact hval

private lemma elimInv_pass (m : ℕ) (w_in : List Bool) (gs : List Gate)
    (w_old : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, OkGate g) (hinv : ElimInv m w_in w_old acc) :
    ElimInv m w_in (wiresFrom gs w_old) (elimPass m gs acc) := by
  induction gs generalizing w_old acc with
  | nil => exact hinv
  | cons g gs ih =>
    rw [wiresFrom_cons, elimPass_cons]
    exact ih _ _ (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (elimInv_step m w_in w_old acc g (hok g List.mem_cons_self) hinv)

private lemma wiresFrom_agree (gs : List Gate) (B : Set ℕ) (w₁ w₂ : List Bool)
    (hlen : w₁.length = w₂.length) (hB : ∀ b ∈ B, b < w₁.length)
    (hagree : ∀ i ∉ B, w₁.getD i false = w₂.getD i false)
    (hread : ∀ g ∈ gs, ∀ i ∈ g.inputs, i ∉ B) :
    (wiresFrom gs w₁).length = (wiresFrom gs w₂).length ∧
    ∀ i ∉ B, (wiresFrom gs w₁).getD i false = (wiresFrom gs w₂).getD i false := by
  induction gs generalizing w₁ w₂ with
  | nil => exact ⟨hlen, hagree⟩
  | cons g gs ih =>
    rw [wiresFrom_cons, wiresFrom_cons]
    have hmap : (g.inputs.map fun i => w₁.getD i false) =
        (g.inputs.map fun i => w₂.getD i false) := by
      apply List.map_congr_left
      intro i hi
      exact hagree i (hread g List.mem_cons_self i hi)
    rw [hmap]
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
    · intro g' hg'
      exact hread g' (List.mem_cons_of_mem _ hg')

private lemma ofFn_getD_lt {α : Type*} {m : ℕ} (f : Fin m → α) (d : α) (i : ℕ) (hi : i < m) :
    (List.ofFn f).getD i d = f ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simp; exact hi), List.getElem_ofFn]

private def substWire (k a i : ℕ) : ℕ :=
  if i < k then i else if i = k then a else i - 1

private def substGate (k a : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (substWire k a)⟩

private lemma substGate_ok (k a : ℕ) (g : Gate) (h : OkGate g) : OkGate (substGate k a g) :=
  ⟨h.1, by simp [substGate]; exact h.2⟩

private lemma substGate_nok (k a : ℕ) (g : Gate) (h : NOkGate g) : NOkGate (substGate k a g) :=
  ⟨substGate_ok k a g h.1, fun hop => by simp [substGate]; exact h.2 hop⟩

private def deleteGate (m : ℕ) (C : Circuit) (j a : ℕ) : Circuit :=
  ⟨C.gates.take j ++ (C.gates.drop (j + 1)).map (substGate (m + j) a),
    substWire (m + j) a C.output⟩

private lemma deleteGate_ok (m : ℕ) (C : Circuit) (j a : ℕ)
    (hok : ∀ g ∈ C.gates, OkGate g) : ∀ g ∈ (deleteGate m C j a).gates, OkGate g := by
  intro g hg
  rcases List.mem_append.1 hg with h1 | h1
  · exact hok g (List.mem_of_mem_take h1)
  · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h1
    exact substGate_ok _ _ g0 (hok g0 (List.mem_of_mem_drop hg0))

private lemma deleteGate_nok (m : ℕ) (C : Circuit) (j a : ℕ)
    (hnok : ∀ g ∈ C.gates, NOkGate g) : ∀ g ∈ (deleteGate m C j a).gates, NOkGate g := by
  intro g hg
  rcases List.mem_append.1 hg with h1 | h1
  · exact hnok g (List.mem_of_mem_take h1)
  · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h1
    exact substGate_nok _ _ g0 (hnok g0 (List.mem_of_mem_drop hg0))

private lemma deleteGate_len (m : ℕ) (C : Circuit) (j a : ℕ) (hj : j < C.gates.length) :
    (deleteGate m C j a).gates.length = C.gates.length - 1 := by
  simp only [deleteGate, List.length_append, List.length_take, List.length_map, List.length_drop]
  omega

private lemma deleteGate_getElem_lt (m : ℕ) (C : Circuit) (j₀ a j : ℕ)
    (hj₀ : j₀ < C.gates.length) (hjj₀ : j < j₀) :
    (deleteGate m C j₀ a).gates[j]'(by rw [deleteGate_len m C j₀ a hj₀]; omega) =
      C.gates[j]'(by omega) := by
  simp only [deleteGate]
  rw [List.getElem_append_left (by rw [List.length_take, Nat.min_eq_left (by omega)]; exact hjj₀),
    List.getElem_take]

private lemma deleteGate_getElem_gt (m : ℕ) (C : Circuit) (j₀ a j : ℕ)
    (hj₀ : j₀ < C.gates.length) (hj : j < C.gates.length) (hjj₀ : j₀ < j) :
    (deleteGate m C j₀ a).gates[j - 1]'(by rw [deleteGate_len m C j₀ a hj₀]; omega) =
      substGate (m + j₀) a (C.gates[j]'hj) := by
  simp only [deleteGate]
  rw [List.getElem_append_right (by rw [List.length_take, Nat.min_eq_left (by omega)]; omega),
    List.getElem_map, List.getElem_drop]
  congr 1
  have hidx : j₀ + 1 + (j - 1 - (C.gates.take j₀).length) = j := by
    rw [List.length_take, Nat.min_eq_left (by omega)]
    omega
  exact congrArg (fun p : Fin C.gates.length => C.gates[p.1]'p.2)
    (Fin.ext (a := ⟨j₀ + 1 + (j - 1 - (C.gates.take j₀).length), by omega⟩) (b := ⟨j, hj⟩) hidx)

private lemma wiresFrom_subst_aux (k a : ℕ) (hka : a < k) :
    ∀ (gs : List Gate) (w₁ w₂ : List Bool),
      w₁.length = w₂.length + 1 → k ≤ w₂.length →
      (∀ i < w₁.length, w₂.getD (substWire k a i) false = w₁.getD i false) →
      ∀ i < (wiresFrom gs w₁).length,
        (wiresFrom (gs.map (substGate k a)) w₂).getD (substWire k a i) false =
          (wiresFrom gs w₁).getD i false := by
  intro gs
  induction gs with
  | nil =>
    intro w₁ w₂ _ _ hag i hi
    exact hag i hi
  | cons g rest ih =>
    intro w₁ w₂ hlen hk hag
    rw [List.map_cons, wiresFrom_cons, wiresFrom_cons]
    have hmap : ((substGate k a g).inputs.map fun i => w₂.getD i false) =
        (g.inputs.map fun i => w₁.getD i false) := by
      simp only [substGate, List.map_map]
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply]
      by_cases hi : i < w₁.length
      · exact hag i hi
      · have hge : w₂.length ≤ substWire k a i := by
          unfold substWire
          split_ifs <;> omega
        rw [List.getD_eq_default _ _ hge, List.getD_eq_default _ _ (by omega)]
    rw [hmap]
    show ∀ i < (wiresFrom rest _).length,
        (wiresFrom (rest.map (substGate k a)) (w₂ ++ [g.op.eval (g.inputs.map fun i => w₁.getD i false)])).getD
          (substWire k a i) false = _
    apply ih _ _ (by simp [hlen]) (by simp; omega)
    intro i hi
    simp only [List.length_append, List.length_singleton] at hi
    by_cases hlt : i < w₁.length
    · have hsublt : substWire k a i < w₂.length := by
        unfold substWire
        split_ifs <;> omega
      rw [getD_snoc_lt _ _ _ _ hsublt, getD_snoc_lt _ _ _ _ hlt]
      exact hag i hlt
    · have hieq : i = w₁.length := by omega
      have hsubeq : substWire k a i = w₂.length := by
        unfold substWire
        split_ifs <;> omega
      rw [getD_snoc_eq _ _ _ _ hsubeq, getD_snoc_eq _ _ _ _ hieq]

private lemma deleteGate_wires_eq (m : ℕ) (C : Circuit) (j a : ℕ) (hj : j < C.gates.length)
    (ha : a < m + j) (x : List Bool) (hx : x.length = m)
    (heq : (C.wires x).getD (m + j) false = (C.wires x).getD a false) :
    ∀ i < m + C.gates.length,
      ((deleteGate m C j a).wires x).getD (substWire (m + j) a i) false =
        (C.wires x).getD i false := by
  have hsplit : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simpa only [List.append_assoc, List.singleton_append] using h1.symm
  show ∀ i < m + C.gates.length,
      (wiresFrom (C.gates.take j ++ (C.gates.drop (j + 1)).map (substGate (m + j) a)) x).getD
          (substWire (m + j) a i) false =
        (wiresFrom C.gates x).getD i false
  set w₂ := wiresFrom (C.gates.take j) x with hw₂
  set w₁ := wiresFrom [C.gates[j]] w₂ with hw₁
  have hw₂_len : w₂.length = m + j := by
    rw [hw₂, wiresFrom_length, hx, List.length_take, Nat.min_eq_left (by omega)]
  have hw₁_len : w₁.length = m + j + 1 := by
    rw [hw₁, wiresFrom_length, hw₂_len]; simp
  have hag0 : ∀ i < w₁.length, w₂.getD (substWire (m + j) a i) false = w₁.getD i false := by
    intro i hi
    by_cases hlt : i < m + j
    · simp only [substWire, hlt, ↓reduceIte]
      rw [hw₁, wiresFrom_cons, wiresFrom_nil, getD_snoc_lt _ _ _ _ (by omega)]
    · have hieq : i = m + j := by omega
      subst hieq
      simp only [substWire, lt_irrefl, ↓reduceIte]
      have h1 : (C.wires x).getD (m + j) false = w₁.getD (m + j) false := by
        show (wiresFrom C.gates x).getD (m + j) false = _
        conv_lhs => rw [hsplit, wiresFrom_append, wiresFrom_append, ← hw₂, ← hw₁]
        exact wiresFrom_getD_lt _ _ _ (by omega)
      have h2 : (C.wires x).getD a false = w₂.getD a false := by
        show (wiresFrom C.gates x).getD a false = _
        conv_lhs => rw [hsplit, wiresFrom_append, wiresFrom_append, ← hw₂, ← hw₁]
        rw [wiresFrom_getD_lt _ _ _ (by omega), hw₁, wiresFrom_cons, wiresFrom_nil,
          getD_snoc_lt _ _ _ _ (by omega)]
      rw [← h2, ← heq, h1]
  intro i hi
  rw [wiresFrom_append, ← hw₂]
  conv_rhs => rw [hsplit, wiresFrom_append, wiresFrom_append, ← hw₂, ← hw₁]
  have hlen_rhs : (wiresFrom (C.gates.drop (j + 1)) w₁).length = m + C.gates.length := by
    rw [wiresFrom_length, hw₁_len, List.length_drop]; omega
  exact wiresFrom_subst_aux (m + j) a ha (C.gates.drop (j + 1)) w₁ w₂ (by omega) (by omega) hag0
    i (by omega)

private lemma deleteGate_dead_wires (m : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (hno : ∀ j' : ℕ, (hj' : j' < C.gates.length) → j < j' → (m + j) ∉ C.gates[j'].inputs)
    (x : List Bool) (hx : x.length = m) :
    ∀ i < m + C.gates.length, i ≠ m + j →
      ((deleteGate m C j 0).wires x).getD (substWire (m + j) 0 i) false =
        (C.wires x).getD i false := by
  have hsplit : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simpa only [List.append_assoc, List.singleton_append] using h1.symm
  show ∀ i < m + C.gates.length, i ≠ m + j →
      (wiresFrom (C.gates.take j ++ (C.gates.drop (j + 1)).map (substGate (m + j) 0)) x).getD
          (substWire (m + j) 0 i) false =
        (wiresFrom C.gates x).getD i false
  set w₂ := wiresFrom (C.gates.take j) x with hw₂
  set w₁ := wiresFrom [C.gates[j]] w₂ with hw₁
  have hw₂_len : w₂.length = m + j := by
    rw [hw₂, wiresFrom_length, hx, List.length_take, Nat.min_eq_left (by omega)]
  have hw₁_len : w₁.length = m + j + 1 := by
    rw [hw₁, wiresFrom_length, hw₂_len]; simp
  have hno_drop : ∀ g ∈ C.gates.drop (j + 1), (m + j) ∉ g.inputs := by
    intro g hg
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hg
    rw [List.getElem_drop]
    exact hno (j + 1 + t) (by rw [List.length_drop] at ht; omega) (by omega)
  have haux : ∀ (gs : List Gate) (w₁' w₂' : List Bool),
      w₁'.length = w₂'.length + 1 → m + j ≤ w₂'.length →
      (∀ g ∈ gs, (m + j) ∉ g.inputs) →
      (∀ i < w₁'.length, i ≠ m + j → w₂'.getD (substWire (m + j) 0 i) false = w₁'.getD i false) →
      ∀ i < (wiresFrom gs w₁').length, i ≠ m + j →
        (wiresFrom (gs.map (substGate (m + j) 0)) w₂').getD (substWire (m + j) 0 i) false =
          (wiresFrom gs w₁').getD i false := by
    intro gs
    induction gs with
    | nil =>
      intro w₁' w₂' _ _ _ hag i hi hne
      exact hag i hi hne
    | cons g rest ih =>
      intro w₁' w₂' hlen' hk' hnod hag'
      rw [List.map_cons, wiresFrom_cons, wiresFrom_cons]
      have hmap : ((substGate (m + j) 0 g).inputs.map fun i => w₂'.getD i false) =
          (g.inputs.map fun i => w₁'.getD i false) := by
        simp only [substGate, List.map_map]
        apply List.map_congr_left
        intro i hi
        simp only [Function.comp_apply]
        have hne : i ≠ m + j := fun h => hnod g List.mem_cons_self (h ▸ hi)
        by_cases hlt : i < w₁'.length
        · exact hag' i hlt hne
        · have hge : w₂'.length ≤ substWire (m + j) 0 i := by
            unfold substWire; split_ifs <;> omega
          rw [List.getD_eq_default _ _ hge, List.getD_eq_default _ _ (by omega)]
      rw [hmap]
      apply ih _ _ (by simp [hlen']) (by simp; omega)
        (fun g' hg' => hnod g' (List.mem_cons_of_mem _ hg'))
      intro i hi hne
      simp only [List.length_append, List.length_singleton] at hi
      by_cases hlt : i < w₁'.length
      · have hsublt : substWire (m + j) 0 i < w₂'.length := by
          unfold substWire; split_ifs <;> omega
        rw [getD_snoc_lt _ _ _ _ hsublt, getD_snoc_lt _ _ _ _ hlt]
        exact hag' i hlt hne
      · have hieq : i = w₁'.length := by omega
        have hsubeq : substWire (m + j) 0 i = w₂'.length := by
          unfold substWire; split_ifs <;> omega
        rw [getD_snoc_eq _ _ _ _ hsubeq, getD_snoc_eq _ _ _ _ hieq]
        rfl
  intro i hi hne
  rw [wiresFrom_append, ← hw₂]
  conv_rhs => rw [hsplit, wiresFrom_append, wiresFrom_append, ← hw₂, ← hw₁]
  have hlen_rhs : (wiresFrom (C.gates.drop (j + 1)) w₁).length = m + C.gates.length := by
    rw [wiresFrom_length, hw₁_len, List.length_drop]; omega
  apply haux (C.gates.drop (j + 1)) w₁ w₂ (by omega) (by omega) hno_drop _ i (by omega) hne
  intro u hu hune
  have hlt : u < m + j := by omega
  simp only [substWire, hlt, ↓reduceIte]
  rw [hw₁, wiresFrom_cons, wiresFrom_nil, getD_snoc_lt _ _ _ _ (by omega)]

private lemma deleteDeadGate {m : ℕ} (C : Circuit) (hok : ∀ g ∈ C.gates, OkGate g)
    (j : ℕ) (hj : j < C.gates.length)
    (hout : C.output ≠ m + j)
    (hno : ∀ j' : ℕ, (hj' : j' < C.gates.length) → j < j' → (m + j) ∉ C.gates[j'].inputs) :
    HasCircuitSize m (circuitFun m C) (C.gates.length - 1) := by
  refine ⟨deleteGate m C j 0, deleteGate_ok m C j 0 hok,
    by show (deleteGate m C j 0).gates.length ≤ C.gates.length - 1; rw [deleteGate_len m C j 0 hj], ?_⟩
  intro x
  show ((deleteGate m C j 0).wires (List.ofFn x)).getD (substWire (m + j) 0 C.output) false =
    (C.wires (List.ofFn x)).getD C.output false
  by_cases hlt : C.output < m + C.gates.length
  · exact deleteGate_dead_wires m C j hj hno (List.ofFn x) (by simp) C.output hlt hout
  · have hge1 : (deleteGate m C j 0).gates.length + m ≤ substWire (m + j) 0 C.output := by
      rw [deleteGate_len m C j 0 hj]
      unfold substWire
      split_ifs <;> omega
    have h1 : ((deleteGate m C j 0).wires (List.ofFn x)).length =
        m + (deleteGate m C j 0).gates.length := by
      show (wiresFrom _ _).length = _; rw [wiresFrom_length]; simp
    have h2 : (C.wires (List.ofFn x)).length = m + C.gates.length := by
      show (wiresFrom _ _).length = _; rw [wiresFrom_length]; simp
    rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

private lemma deleteConstGate {m : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (j : ℕ) (hj : j < C.gates.length) (c : Bool)
    (hconst : ∀ x : Fin m → Bool, (C.wires (List.ofFn x)).getD (m + j) false = c)
    (hnc : ∃ x x' : Fin m → Bool, circuitFun m C x ≠ circuitFun m C x') :
    HasCircuitSize m (circuitFun m C) (C.gates.length - 1) := by
  set gs₁ := C.gates.take j with hgs₁
  set gs₂ := C.gates.drop (j + 1) with hgs₂
  have hsplit : C.gates = gs₁ ++ [C.gates[j]] ++ gs₂ := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = C.gates[j] :: gs₂ := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simpa only [hgs₁, List.append_assoc, List.singleton_append] using h1.symm
  set init : List (Bool ⊕ ℕ) :=
    List.ofFn (fun i : Fin (m + j) => Sum.inr (i : ℕ)) ++ [Sum.inl c] with hinit
  set acc := elimPass m gs₂ (init, gs₁) with hacc
  have hinv : ∀ x : Fin m → Bool,
      ElimInv m (List.ofFn x) (wiresFrom C.gates (List.ofFn x)) acc := by
    intro x
    rw [hsplit, wiresFrom_append, hacc]
    apply elimInv_pass m (List.ofFn x) gs₂ _ (init, gs₁)
      (fun g hg => (hnok g (List.mem_of_mem_drop hg)).1)
    have hlen1 : (wiresFrom gs₁ (List.ofFn x)).length = m + j := by
      rw [wiresFrom_length, List.length_ofFn, hgs₁, List.length_take, Nat.min_eq_left (by omega)]
    have hlen2 : (wiresFrom (gs₁ ++ [C.gates[j]]) (List.ofFn x)).length = m + j + 1 := by
      rw [wiresFrom_append, wiresFrom_length, hlen1]; simp
    refine ⟨by simp, by simp [hinit, hlen2], ?_⟩
    intro i
    by_cases h1 : i < m + j
    · have hget : init.getD i (Sum.inl false) = Sum.inr i := by
        rw [hinit, getD_snoc_lt _ _ _ _ (by simp; exact h1), ofFn_getD_lt _ _ _ h1]
      rw [hget]
      refine ⟨by simp [statValid, hgs₁, List.length_take]; omega, ?_⟩
      simp only [statVal]
      rw [wiresFrom_append]
      exact (wiresFrom_getD_lt _ _ _ (by omega)).symm
    · by_cases h2 : i = m + j
      · have hget : init.getD i (Sum.inl false) = Sum.inl c := by
          rw [hinit, getD_snoc_eq _ _ _ _ (by simp; exact h2)]
        rw [hget]
        refine ⟨trivial, ?_⟩
        simp only [statVal]
        have hcx := hconst x
        rw [h2]
        have hEq : (wiresFrom (gs₁ ++ [C.gates[j]]) (List.ofFn x)).getD (m + j) false =
            (C.wires (List.ofFn x)).getD (m + j) false := by
          show _ = (wiresFrom C.gates (List.ofFn x)).getD (m + j) false
          conv_rhs => rw [hsplit, wiresFrom_append]
          exact (wiresFrom_getD_lt _ _ _ (by omega)).symm
        rw [hEq, hcx]
      · rw [List.getD_eq_default _ _ (by simp [hinit]; omega),
            List.getD_eq_default _ _ (by omega)]
        exact ⟨trivial, rfl⟩
  have hval : ∀ x : Fin m → Bool,
      statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) =
        circuitFun m C x := by
    intro x
    exact ((hinv x).2.2 C.output).2
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl b =>
    obtain ⟨x, x', hne⟩ := hnc
    have hx := hval x; have hx' := hval x'
    rw [hst] at hx hx'
    exact absurd (hx.symm.trans hx') hne
  | inr out' =>
    refine ⟨⟨acc.2, out'⟩, elimPass_ok m gs₂ _ (fun g hg => (hnok g (List.mem_of_mem_take hg)).1), ?_, ?_⟩
    · show acc.2.length ≤ C.gates.length - 1
      have hlen := elimPass_len m gs₂ (init, gs₁)
      rw [← hacc] at hlen
      simp only [Prod.snd] at hlen
      have hl1 : gs₁.length = j := by rw [hgs₁, List.length_take, Nat.min_eq_left (by omega)]
      have hl2 : gs₂.length = C.gates.length - (j + 1) := by rw [hgs₂, List.length_drop]
      omega
    · intro x
      have := hval x
      rw [hst] at this
      exact this

private lemma deleteAliasGate {m : ℕ} (C : Circuit) (hok : ∀ g ∈ C.gates, OkGate g)
    (j a : ℕ) (hj : j < C.gates.length) (ha : a < m + j)
    (heq : ∀ x : Fin m → Bool, (C.wires (List.ofFn x)).getD (m + j) false =
      (C.wires (List.ofFn x)).getD a false) :
    HasCircuitSize m (circuitFun m C) (C.gates.length - 1) := by
  refine ⟨deleteGate m C j a, deleteGate_ok m C j a hok,
    by show (deleteGate m C j a).gates.length ≤ C.gates.length - 1; rw [deleteGate_len m C j a hj], ?_⟩
  intro x
  show ((deleteGate m C j a).wires (List.ofFn x)).getD (substWire (m + j) a C.output) false =
    (C.wires (List.ofFn x)).getD C.output false
  by_cases hlt : C.output < m + C.gates.length
  · exact deleteGate_wires_eq m C j a hj ha (List.ofFn x) (by simp) (heq x) C.output hlt
  · have hge1 : (deleteGate m C j a).gates.length + m ≤ substWire (m + j) a C.output := by
      rw [deleteGate_len m C j a hj]
      unfold substWire
      split_ifs <;> omega
    have h1 : ((deleteGate m C j a).wires (List.ofFn x)).length =
        m + (deleteGate m C j a).gates.length := by
      show (wiresFrom _ _).length = _; rw [wiresFrom_length]; simp
    have h2 : (C.wires (List.ofFn x)).length = m + C.gates.length := by
      show (wiresFrom _ _).length = _; rw [wiresFrom_length]; simp
    rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

private def OrStep (m : ℕ) (gs : List Gate) (u v : ℕ) : Prop :=
  ∃ j : ℕ, ∃ hj : j < gs.length, u = m + j ∧ gs[j].op = GateOp.or ∧ v ∈ gs[j].inputs ∧ v < m + j

private def OrReach (m : ℕ) (gs : List Gate) (u v : ℕ) : Prop :=
  Relation.ReflTransGen (OrStep m gs) u v

private lemma orReach_sound (m : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = m)
    (u v : ℕ) (hr : OrReach m C.gates u v)
    (hv : (C.wires x).getD v false = true) :
    (C.wires x).getD u false = true := by
  induction hr with
  | refl => exact hv
  | @tail b c _ hstep ih =>
    apply ih
    obtain ⟨j, hj, rfl, hop, hcin, hclt⟩ := hstep
    show (wiresFrom C.gates x).getD (m + j) false = true
    have h1 := wiresFrom_getD_gate C.gates x j hj
    rw [hx] at h1
    rw [h1, hop]
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    refine ⟨c, hcin, ?_⟩
    have hpref : (wiresFrom (C.gates.take j) x).getD c false = (wiresFrom C.gates x).getD c false := by
      have hsp : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
      conv_rhs => rw [hsp, wiresFrom_append]
      exact (wiresFrom_getD_lt _ _ _ (by rw [wiresFrom_length, hx, List.length_take, Nat.min_eq_left (by omega)]; exact hclt)).symm
    rw [hpref]
    exact hv

private lemma orReach_le (m : ℕ) (gs : List Gate) (u v : ℕ) (hr : OrReach m gs u v) : v ≤ u := by
  induction hr with
  | refl => exact le_rfl
  | @tail b c _ hstep ih =>
    obtain ⟨j, _, rfl, _, _, hlt⟩ := hstep
    omega

private lemma orReach_deleteGate (m : ℕ) (C : Circuit) (j₀ a : ℕ) (hj₀ : j₀ < C.gates.length)
    (ha : a < m + j₀) (u v : ℕ) (hr : OrReach m C.gates u v)
    (havoid : ∀ w, OrReach m C.gates u w → OrReach m C.gates w v → w ≠ m + j₀) :
    OrReach m (deleteGate m C j₀ a).gates (substWire (m + j₀) a u) (substWire (m + j₀) a v) := by
  induction hr with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hrb hstep ih =>
    have hb_ne : b ≠ m + j₀ := havoid b hrb (Relation.ReflTransGen.single hstep)
    have hc_ne : c ≠ m + j₀ := havoid c (Relation.ReflTransGen.tail hrb hstep) Relation.ReflTransGen.refl
    have hprev := ih (fun w hw1 hw2 => havoid w hw1 (Relation.ReflTransGen.tail hw2 hstep))
    refine Relation.ReflTransGen.tail hprev ?_
    obtain ⟨j, hj, rfl, hop, hcin, hclt⟩ := hstep
    have hjj₀ : j ≠ j₀ := fun h => hb_ne (by omega)
    have hlen' : (deleteGate m C j₀ a).gates.length = C.gates.length - 1 :=
      deleteGate_len m C j₀ a hj₀
    by_cases hlt : j < j₀
    · have hsub_b : substWire (m + j₀) a (m + j) = m + j := by
        unfold substWire; simp [hlt]
      have hsub_c : substWire (m + j₀) a c = c := by
        unfold substWire; simp [show c < m + j₀ by omega]
      rw [hsub_b, hsub_c]
      refine ⟨j, by omega, rfl, ?_, ?_, hclt⟩
      · have hget : (deleteGate m C j₀ a).gates[j]'(by omega) = C.gates[j] := by
          simp only [deleteGate]
          rw [List.getElem_append_left (by rw [List.length_take, Nat.min_eq_left (by omega)]; exact hlt),
            List.getElem_take]
        rw [hget]; exact hop
      · have hget : (deleteGate m C j₀ a).gates[j]'(by omega) = C.gates[j] := by
          simp only [deleteGate]
          rw [List.getElem_append_left (by rw [List.length_take, Nat.min_eq_left (by omega)]; exact hlt),
            List.getElem_take]
        rw [hget]; exact hcin
    · have hgt : j₀ < j := by omega
      have hsub_b : substWire (m + j₀) a (m + j) = m + (j - 1) := by
        unfold substWire; split_ifs <;> omega
      rw [hsub_b]
      have hget : (deleteGate m C j₀ a).gates[j - 1]'(by omega) = substGate (m + j₀) a C.gates[j] :=
        deleteGate_getElem_gt m C j₀ a j hj₀ hj hgt
      refine ⟨j - 1, by omega, rfl, ?_, ?_, ?_⟩
      · rw [hget]; exact hop
      · rw [hget]; simp only [substGate]; exact List.mem_map.2 ⟨c, hcin, rfl⟩
      · unfold substWire; split_ifs <;> omega

private lemma orReach_append (m : ℕ) (gs₁ gs₂ : List Gate) (u v : ℕ)
    (hr : OrReach m gs₁ u v) : OrReach m (gs₁ ++ gs₂) u v := by
  induction hr with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hstep ih =>
    refine Relation.ReflTransGen.tail ih ?_
    obtain ⟨j, hj, rfl, hop, hcin, hclt⟩ := hstep
    refine ⟨j, by simp; omega, rfl, ?_, ?_, hclt⟩
    · rw [List.getElem_append_left hj]; exact hop
    · rw [List.getElem_append_left hj]; exact hcin

private noncomputable def orAncSet (m : ℕ) (C : Circuit) : Finset ℕ :=
  by
    classical
    exact (Finset.range C.gates.length).filter (fun j =>
      ∃ hj : j < C.gates.length, C.gates[j].op = GateOp.or ∧ OrReach m C.gates C.output (m + j))

private noncomputable def orAncCount (m : ℕ) (C : Circuit) : ℕ :=
  (orAncSet m C).card

private lemma mem_orAncSet (m : ℕ) (C : Circuit) (j : ℕ) :
    j ∈ orAncSet m C ↔
      ∃ hj : j < C.gates.length, C.gates[j].op = GateOp.or ∧ OrReach m C.gates C.output (m + j) := by
  classical
  simp only [orAncSet, Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

private lemma orAncCount_le (m : ℕ) (C : Circuit) : orAncCount m C ≤ C.gates.length := by
  classical
  unfold orAncCount orAncSet
  exact (Finset.card_filter_le _ _).trans (by simp)

private lemma orAncCount_rewrite1 (m : ℕ) (C : Circuit) (j₀ a z : ℕ)
    (hj₀ : j₀ < C.gates.length) (ha : a < m + j₀)
    (hout_lt : C.output < m + C.gates.length)
    (hnot : ¬ OrReach m C.gates C.output (m + j₀)) :
    let C1 := deleteGate m C j₀ a
    let C2 : Circuit := ⟨C1.gates ++ [⟨GateOp.or, [C1.output, z]⟩], m + C1.gates.length⟩
    orAncCount m C + 1 ≤ orAncCount m C2 := by
  intro C1 C2
  have hlen1 : C1.gates.length = C.gates.length - 1 := deleteGate_len m C j₀ a hj₀
  have hout1_lt : C1.output < m + C1.gates.length := by
    have hne : C.output ≠ m + j₀ := fun h => hnot (h ▸ Relation.ReflTransGen.refl)
    show substWire (m + j₀) a C.output < m + C1.gates.length
    unfold substWire
    split_ifs <;> omega
  let f : ℕ → ℕ := fun j => if j < j₀ then j else j - 1
  have htop : C1.gates.length ∈ orAncSet m C2 := by
    rw [mem_orAncSet]
    refine ⟨by simp [C2], ?_, Relation.ReflTransGen.refl⟩
    simp [C2]
  have himg : (orAncSet m C).image f ⊆ (orAncSet m C2).erase C1.gates.length := by
    intro k hk
    obtain ⟨j, hjmem, rfl⟩ := Finset.mem_image.1 hk
    obtain ⟨hj, hop, hreach⟩ := (mem_orAncSet m C j).1 hjmem
    have hjj₀ : j ≠ j₀ := fun h => hnot (h ▸ hreach)
    have hfk_lt : f j < C1.gates.length := by dsimp [f]; split_ifs <;> omega
    rw [Finset.mem_erase]
    refine ⟨by omega, (mem_orAncSet m C2 (f j)).2 ⟨by simp [C2]; omega, ?_, ?_⟩⟩
    · have hget1 : C1.gates[f j]'hfk_lt = if j < j₀ then C.gates[j] else substGate (m + j₀) a C.gates[j] := by
        by_cases h : j < j₀
        · have hfj : f j = j := by dsimp [f]; simp [h]
          simp only [h, ↓reduceIte]
          simpa only [hfj] using deleteGate_getElem_lt m C j₀ a j hj₀ h
        · have hgt : j₀ < j := by omega
          have hfj : f j = j - 1 := by dsimp [f]; simp [h]
          simp only [h, ↓reduceIte]
          simpa only [hfj] using deleteGate_getElem_gt m C j₀ a j hj₀ hj hgt
      have hget2 : C2.gates[f j]'(by simp [C2]; omega) = C1.gates[f j]'hfk_lt :=
        List.getElem_append_left hfk_lt
      rw [hget2, hget1]
      split_ifs <;> simpa [substGate] using hop
    · have hstep_top : OrStep m C2.gates (m + C1.gates.length) C1.output := by
        refine ⟨C1.gates.length, by simp [C2], rfl, by simp [C2], by simp [C2], hout1_lt⟩
      have hreach1 : OrReach m C1.gates C1.output (substWire (m + j₀) a (m + j)) :=
        orReach_deleteGate m C j₀ a hj₀ ha C.output (m + j) hreach
          (fun w hw1 _ hweq => hnot (hweq ▸ hw1))
      have hsub_j : substWire (m + j₀) a (m + j) = m + f j := by
        dsimp [substWire, f]
        split_ifs <;> omega
      rw [hsub_j] at hreach1
      exact Relation.ReflTransGen.head hstep_top (orReach_append m C1.gates _ _ _ hreach1)
  have hinj : Set.InjOn f (orAncSet m C : Set ℕ) := by
    intro j₁ hj₁ j₂ hj₂ heq
    have h1 := (mem_orAncSet m C j₁).1 hj₁
    have h2 := (mem_orAncSet m C j₂).1 hj₂
    have hne1 : j₁ ≠ j₀ := fun h => hnot (h ▸ h1.2.2)
    have hne2 : j₂ ≠ j₀ := fun h => hnot (h ▸ h2.2.2)
    dsimp [f] at heq
    split_ifs at heq <;> omega
  have hcard_img : ((orAncSet m C).image f).card = (orAncSet m C).card :=
    Finset.card_image_of_injOn hinj
  have hle := Finset.card_le_card himg
  rw [hcard_img, Finset.card_erase_of_mem htop] at hle
  have hpos : 1 ≤ (orAncSet m C2).card := Finset.one_le_card.2 ⟨_, htop⟩
  unfold orAncCount
  omega

private lemma orAncCount_rewrite2 (m : ℕ) (C : Circuit) (j₁ j₂ a₁ a₂ z : ℕ)
    (hj₁ : j₁ < C.gates.length) (hj₂ : j₂ < C.gates.length) (hj12 : j₁ < j₂)
    (ha₁ : a₁ < m + j₁) (ha₂ : a₂ < m + (j₂ - 1))
    (hop₁ : C.gates[j₁].op ≠ GateOp.or) (hop₂ : C.gates[j₂].op ≠ GateOp.or)
    (hout_lt : C.output < m + C.gates.length) :
    let C1 := deleteGate m C j₁ a₁
    let C2 := deleteGate m C1 (j₂ - 1) a₂
    let C3 : Circuit := ⟨C2.gates ++ [⟨GateOp.not, [z]⟩, ⟨GateOp.or, [C2.output, m + C2.gates.length]⟩],
      m + (C2.gates.length + 1)⟩
    orAncCount m C + 1 ≤ orAncCount m C3 := by
  intro C1 C2 C3
  have hlen1 : C1.gates.length = C.gates.length - 1 := deleteGate_len m C j₁ a₁ hj₁
  have hj₂' : j₂ - 1 < C1.gates.length := by omega
  have hlen2 : C2.gates.length = C.gates.length - 2 := by
    rw [deleteGate_len m C1 (j₂ - 1) a₂ hj₂', hlen1]; omega
  have htop : C2.gates.length + 1 ∈ orAncSet m C3 := by
    rw [mem_orAncSet]
    refine ⟨by simp [C3], ?_, Relation.ReflTransGen.refl⟩
    have hidx : C3.gates[C2.gates.length + 1]'(by simp [C3]) =
        ⟨GateOp.or, [C2.output, m + C2.gates.length]⟩ := by
      simp only [C3]
      rw [List.getElem_append_right (by omega)]
      have : C2.gates.length + 1 - C2.gates.length = 1 := by omega
      simp [this]
    rw [hidx]
  by_cases hout_eq : C.output = m + j₁ ∨ C.output = m + j₂
  · have hemp : orAncSet m C = ∅ := by
      ext j
      simp only [Finset.notMem_empty, iff_false]
      intro hmem
      obtain ⟨hj, hop, hr⟩ := (mem_orAncSet m C j).1 hmem
      rcases Relation.ReflTransGen.cases_head hr with heq | ⟨w, hstep, _⟩
      · rcases hout_eq with h1 | h1
        · rw [h1] at heq; have : j = j₁ := by omega
          subst this; exact hop₁ hop
        · rw [h1] at heq; have : j = j₂ := by omega
          subst this; exact hop₂ hop
      · obtain ⟨j', _, hj'eq, hj'op, _, _⟩ := hstep
        rcases hout_eq with h1 | h1
        · rw [h1] at hj'eq; have : j' = j₁ := by omega
          subst this; exact hop₁ hj'op
        · rw [h1] at hj'eq; have : j' = j₂ := by omega
          subst this; exact hop₂ hj'op
    unfold orAncCount
    rw [hemp, Finset.card_empty, zero_add]
    exact Finset.one_le_card.2 ⟨_, htop⟩
  · have hout_ne1 : C.output ≠ m + j₁ := fun h => hout_eq (Or.inl h)
    have hout_ne2 : C.output ≠ m + j₂ := fun h => hout_eq (Or.inr h)
    have hout1_lt : C1.output < m + C1.gates.length := by
      show substWire (m + j₁) a₁ C.output < m + C1.gates.length
      unfold substWire; split_ifs <;> omega
    have hout1_ne : C1.output ≠ m + (j₂ - 1) := by
      show substWire (m + j₁) a₁ C.output ≠ m + (j₂ - 1)
      unfold substWire; split_ifs <;> omega
    have hout2_lt : C2.output < m + C2.gates.length := by
      show substWire (m + (j₂ - 1)) a₂ C1.output < m + C2.gates.length
      unfold substWire; split_ifs <;> omega
    have hop₂' : (C1.gates[j₂ - 1]'hj₂').op ≠ GateOp.or := by
      have hget : C1.gates[j₂ - 1]'hj₂' = substGate (m + j₁) a₁ C.gates[j₂] :=
        deleteGate_getElem_gt m C j₁ a₁ j₂ hj₁ hj₂ hj12
      rw [hget]; exact hop₂
    let f1 : ℕ → ℕ := fun j => if j < j₁ then j else j - 1
    let f2 : ℕ → ℕ := fun j => if j < j₂ - 1 then j else j - 1
    let f : ℕ → ℕ := fun j => f2 (f1 j)
    have himg : (orAncSet m C).image f ⊆ (orAncSet m C3).erase (C2.gates.length + 1) := by
      intro k hk
      obtain ⟨j, hjmem, rfl⟩ := Finset.mem_image.1 hk
      obtain ⟨hj, hop, hreach⟩ := (mem_orAncSet m C j).1 hjmem
      have hne1 : j ≠ j₁ := fun h => hop₁ (h ▸ hop)
      have hne2 : j ≠ j₂ := fun h => hop₂ (h ▸ hop)
      have hf1_lt : f1 j < C1.gates.length := by dsimp [f1]; split_ifs <;> omega
      have hf1_ne : f1 j ≠ j₂ - 1 := by dsimp [f1]; split_ifs <;> omega
      have hf_lt : f j < C2.gates.length := by dsimp [f, f2]; split_ifs <;> omega
      rw [Finset.mem_erase]
      refine ⟨by omega, (mem_orAncSet m C3 (f j)).2 ⟨by simp [C3]; omega, ?_, ?_⟩⟩
      · have hget1 : C1.gates[f1 j]'hf1_lt = if j < j₁ then C.gates[j] else substGate (m + j₁) a₁ C.gates[j] := by
          by_cases h : j < j₁
          · have hfj : f1 j = j := by dsimp [f1]; simp [h]
            simp only [h, ↓reduceIte]
            simpa only [hfj] using deleteGate_getElem_lt m C j₁ a₁ j hj₁ h
          · have hgt : j₁ < j := by omega
            have hfj : f1 j = j - 1 := by dsimp [f1]; simp [h]
            simp only [h, ↓reduceIte]
            simpa only [hfj] using deleteGate_getElem_gt m C j₁ a₁ j hj₁ hj hgt
        have hop1_j : (C1.gates[f1 j]'hf1_lt).op = GateOp.or := by
          rw [hget1]; split_ifs <;> simpa [substGate] using hop
        have hget2 : C2.gates[f j]'hf_lt =
            if f1 j < j₂ - 1 then C1.gates[f1 j]'hf1_lt else substGate (m + (j₂ - 1)) a₂ (C1.gates[f1 j]'hf1_lt) := by
          by_cases h : f1 j < j₂ - 1
          · have hfj : f j = f1 j := by dsimp [f, f2]; simp [h]
            simp only [h, ↓reduceIte]
            simpa only [hfj] using deleteGate_getElem_lt m C1 (j₂ - 1) a₂ (f1 j) hj₂' h
          · have hgt : j₂ - 1 < f1 j := by omega
            have hfj : f j = f1 j - 1 := by dsimp [f, f2]; simp [h]
            simp only [h, ↓reduceIte]
            simpa only [hfj] using deleteGate_getElem_gt m C1 (j₂ - 1) a₂ (f1 j) hj₂' hf1_lt hgt
        have hget3 : C3.gates[f j]'(by simp [C3]; omega) = C2.gates[f j]'hf_lt :=
          List.getElem_append_left hf_lt
        rw [hget3, hget2]
        split_ifs <;> simpa [substGate] using hop1_j
      · have havoid1 : ∀ w, OrReach m C.gates C.output w → OrReach m C.gates w (m + j) → w ≠ m + j₁ := by
          intro w _ hw2 hweq
          subst hweq
          rcases Relation.ReflTransGen.cases_head hw2 with heq | ⟨_, hstep, _⟩
          · exact hne1 (by omega)
          · obtain ⟨j', _, hj'eq, hj'op, _, _⟩ := hstep
            have : j' = j₁ := by omega
            subst this; exact hop₁ hj'op
        have hreach1 : OrReach m C1.gates C1.output (m + f1 j) := by
          have h := orReach_deleteGate m C j₁ a₁ hj₁ ha₁ C.output (m + j) hreach havoid1
          have hsub : substWire (m + j₁) a₁ (m + j) = m + f1 j := by
            dsimp [substWire, f1]; split_ifs <;> omega
          rwa [hsub] at h
        have havoid2 : ∀ w, OrReach m C1.gates C1.output w → OrReach m C1.gates w (m + f1 j) → w ≠ m + (j₂ - 1) := by
          intro w _ hw2 hweq
          subst hweq
          rcases Relation.ReflTransGen.cases_head hw2 with heq | ⟨_, hstep, _⟩
          · exact hf1_ne (by omega)
          · obtain ⟨j', _, hj'eq, hj'op, _, _⟩ := hstep
            have : j' = j₂ - 1 := by omega
            subst this; exact hop₂' hj'op
        have hreach2 : OrReach m C2.gates C2.output (m + f j) := by
          have h := orReach_deleteGate m C1 (j₂ - 1) a₂ hj₂' ha₂ C1.output (m + f1 j) hreach1 havoid2
          have hsub : substWire (m + (j₂ - 1)) a₂ (m + f1 j) = m + f j := by
            dsimp [substWire, f, f2]; split_ifs <;> omega
          rwa [hsub] at h
        have hstep_top : OrStep m C3.gates (m + (C2.gates.length + 1)) C2.output := by
          refine ⟨C2.gates.length + 1, by simp [C3], rfl, ?_, ?_, by omega⟩
          · have hidx : C3.gates[C2.gates.length + 1]'(by simp [C3]) =
                ⟨GateOp.or, [C2.output, m + C2.gates.length]⟩ := by
              simp only [C3]
              rw [List.getElem_append_right (by omega)]
              have : C2.gates.length + 1 - C2.gates.length = 1 := by omega
              simp [this]
            rw [hidx]
          · have hidx : C3.gates[C2.gates.length + 1]'(by simp [C3]) =
                ⟨GateOp.or, [C2.output, m + C2.gates.length]⟩ := by
              simp only [C3]
              rw [List.getElem_append_right (by omega)]
              have : C2.gates.length + 1 - C2.gates.length = 1 := by omega
              simp [this]
            rw [hidx]; simp
        exact Relation.ReflTransGen.head hstep_top (orReach_append m C2.gates _ _ _ hreach2)
    have hinj : Set.InjOn f (orAncSet m C : Set ℕ) := by
      intro x₁ hx₁ x₂ hx₂ heq
      have h1 := (mem_orAncSet m C x₁).1 hx₁
      have h2 := (mem_orAncSet m C x₂).1 hx₂
      have hne11 : x₁ ≠ j₁ := fun h => hop₁ (h ▸ h1.2.1)
      have hne12 : x₁ ≠ j₂ := fun h => hop₂ (h ▸ h1.2.1)
      have hne21 : x₂ ≠ j₁ := fun h => hop₁ (h ▸ h2.2.1)
      have hne22 : x₂ ≠ j₂ := fun h => hop₂ (h ▸ h2.2.1)
      dsimp [f, f1, f2] at heq
      split_ifs at heq <;> omega
    have hcard_img : ((orAncSet m C).image f).card = (orAncSet m C).card :=
      Finset.card_image_of_injOn hinj
    have hle := Finset.card_le_card himg
    rw [hcard_img, Finset.card_erase_of_mem htop] at hle
    have hpos : 1 ≤ (orAncSet m C3).card := Finset.one_le_card.2 ⟨_, htop⟩
    unfold orAncCount
    omega

private def walkPrefix {n : ℕ} {G : SimpleGraph (Fin n)} :
    ∀ {u v : Fin n} (w : G.Walk u v) (i : ℕ), G.Walk u (w.getVert i)
  | _, _, SimpleGraph.Walk.nil, _ => SimpleGraph.Walk.nil
  | _, _, SimpleGraph.Walk.cons _ _, 0 => SimpleGraph.Walk.nil
  | _, _, SimpleGraph.Walk.cons h w', i + 1 => SimpleGraph.Walk.cons h (walkPrefix w' i)

private lemma walkPrefix_length {n : ℕ} {G : SimpleGraph (Fin n)} :
    ∀ {u v : Fin n} (w : G.Walk u v) (i : ℕ), i ≤ w.length → (walkPrefix w i).length = i
  | _, _, SimpleGraph.Walk.nil, 0, _ => rfl
  | _, _, SimpleGraph.Walk.nil, i + 1, hi => by simp at hi
  | _, _, SimpleGraph.Walk.cons _ _, 0, _ => rfl
  | _, _, SimpleGraph.Walk.cons h w', i + 1, hi => by
    have hi' : i ≤ w'.length := by simp at hi; omega
    change (SimpleGraph.Walk.cons h (walkPrefix w' i)).length = i + 1
    rw [SimpleGraph.Walk.length_cons, walkPrefix_length w' i hi']

private def Girth7 {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length

private def Branch7 {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ u v : Fin n, u ≠ v → 3 ≤ (G.neighborSet u).ncard → 3 ≤ (G.neighborSet v).ncard →
    ∀ p : G.Walk u v, 7 ≤ p.length

private lemma girth7_anti {n : ℕ} {G₁ G₂ : SimpleGraph (Fin n)} (hle : G₁ ≤ G₂)
    (h : Girth7 G₂) : Girth7 G₁ := by
  intro v w hw
  have hmap : (w.map (SimpleGraph.Hom.ofLE hle)).IsCycle :=
    hw.map (fun _ _ heq => heq)
  have := h v (w.map (SimpleGraph.Hom.ofLE hle)) hmap
  simpa using this

private lemma branch7_anti {n : ℕ} {G₁ G₂ : SimpleGraph (Fin n)} (hle : G₁ ≤ G₂)
    (h : Branch7 G₂) : Branch7 G₁ := by
  intro u v huv hu hv p
  have hsub_u : G₁.neighborSet u ⊆ G₂.neighborSet u := fun _ hw => hle hw
  have hsub_v : G₁.neighborSet v ⊆ G₂.neighborSet v := fun _ hw => hle hw
  have hu' : 3 ≤ (G₂.neighborSet u).ncard := hu.trans (Set.ncard_le_ncard hsub_u (Set.toFinite _))
  have hv' : 3 ≤ (G₂.neighborSet v).ncard := hv.trans (Set.ncard_le_ncard hsub_v (Set.toFinite _))
  have := h u v huv hu' hv' (p.map (SimpleGraph.Hom.ofLE hle))
  simpa using this

private lemma deg2_exact {n : ℕ} (G : SimpleGraph (Fin n)) (v a b : Fin n)
    (hab : a ≠ b) (hva : G.Adj v a) (hvb : G.Adj v b)
    (hdeg : (G.neighborSet v).ncard ≤ 2) :
    ∀ w : Fin n, G.Adj v w ↔ w = a ∨ w = b := by
  intro w
  constructor
  · intro hvw
    by_contra hnot
    have hwa : w ≠ a := fun h => hnot (Or.inl h)
    have hwb : w ≠ b := fun h => hnot (Or.inr h)
    have hsub : ({a, b, w} : Set (Fin n)) ⊆ G.neighborSet v := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl <;> simpa [SimpleGraph.mem_neighborSet]
    have hcard : ({a, b, w} : Set (Fin n)).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem (by simp [hab, hwa.symm]),
          Set.ncard_insert_of_notMem (by simp [hwb.symm]), Set.ncard_singleton]
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    omega
  · rintro (rfl | rfl)
    · exact hva
    · exact hvb

private lemma cycle_getVert_inj {n : ℕ} {G : SimpleGraph (Fin n)} {v : Fin n}
    (w : G.Walk v v) (hw : w.IsCycle) (i j : ℕ) (hi : i < w.length) (hj : j < w.length)
    (heq : w.getVert i = w.getVert j) : i = j := by
  have hnd : w.support.tail.Nodup := hw.support_nodup
  have hlen_t : w.support.tail.length = w.length := by simp [SimpleGraph.Walk.length_support]
  have hget : ∀ k (hk : k < w.length), w.support.tail[k]'(by omega) = w.getVert (k + 1) := by
    intro k hk
    rw [List.getElem_tail, SimpleGraph.Walk.getVert_eq_support_getElem w (by omega)]
  by_cases hi0 : i = 0
  · subst hi0
    by_cases hj0 : j = 0
    · exact hj0.symm
    · exfalso
      have h1 : w.getVert 0 = w.getVert w.length := by simp
      have h2 : w.support.tail[w.length - 1]'(by omega) = w.support.tail[j - 1]'(by omega) := by
        rw [hget (w.length - 1) (by omega), hget (j - 1) (by omega)]
        rw [show w.length - 1 + 1 = w.length by omega, show j - 1 + 1 = j by omega]
        exact h1.symm.trans heq
      have hidx := (List.Nodup.getElem_inj_iff hnd).1 h2
      omega
  · by_cases hj0 : j = 0
    · subst hj0
      exfalso
      have h1 : w.getVert 0 = w.getVert w.length := by simp
      have h2 : w.support.tail[i - 1]'(by omega) = w.support.tail[w.length - 1]'(by omega) := by
        rw [hget (i - 1) (by omega), hget (w.length - 1) (by omega)]
        rw [show i - 1 + 1 = i by omega, show w.length - 1 + 1 = w.length by omega]
        exact heq.trans h1
      have hidx := (List.Nodup.getElem_inj_iff hnd).1 h2
      omega
    · have h2 : w.support.tail[i - 1]'(by omega) = w.support.tail[j - 1]'(by omega) := by
        rw [hget (i - 1) (by omega), hget (j - 1) (by omega)]
        rw [show i - 1 + 1 = i by omega, show j - 1 + 1 = j by omega]
        exact heq
      have hidx := (List.Nodup.getElem_inj_iff hnd).1 h2
      omega

private lemma cycle_deg2_path {n : ℕ} (G : SimpleGraph (Fin n))
    (hNotAcyc : ¬ G.IsAcyclic) (hG : Girth7 G) (hB : Branch7 G) :
    ∃ (p₀ p₁ p₂ p₃ p₄ p₅ p₆ p₇ : Fin n),
      (p₀ ≠ p₁ ∧ p₀ ≠ p₂ ∧ p₀ ≠ p₃ ∧ p₀ ≠ p₄ ∧ p₀ ≠ p₅ ∧ p₀ ≠ p₆) ∧
      (p₇ ≠ p₁ ∧ p₇ ≠ p₂ ∧ p₇ ≠ p₃ ∧ p₇ ≠ p₄ ∧ p₇ ≠ p₅ ∧ p₇ ≠ p₆) ∧
      (p₁ ≠ p₂ ∧ p₁ ≠ p₃ ∧ p₁ ≠ p₄ ∧ p₁ ≠ p₅ ∧ p₁ ≠ p₆ ∧
       p₂ ≠ p₃ ∧ p₂ ≠ p₄ ∧ p₂ ≠ p₅ ∧ p₂ ≠ p₆ ∧
       p₃ ≠ p₄ ∧ p₃ ≠ p₅ ∧ p₃ ≠ p₆ ∧
       p₄ ≠ p₅ ∧ p₄ ≠ p₆ ∧
       p₅ ≠ p₆) ∧
      (∀ w, G.Adj p₁ w ↔ w = p₀ ∨ w = p₂) ∧
      (∀ w, G.Adj p₂ w ↔ w = p₁ ∨ w = p₃) ∧
      (∀ w, G.Adj p₃ w ↔ w = p₂ ∨ w = p₄) ∧
      (∀ w, G.Adj p₄ w ↔ w = p₃ ∨ w = p₅) ∧
      (∀ w, G.Adj p₅ w ↔ w = p₄ ∨ w = p₆) ∧
      (∀ w, G.Adj p₆ w ↔ w = p₅ ∨ w = p₇) := by
  have hex_cyc : ∃ (v₀ : Fin n) (w₀ : G.Walk v₀ v₀), w₀.IsCycle := by
    by_contra hno
    exact hNotAcyc (fun v w hw => hno ⟨v, w, hw⟩)
  obtain ⟨v₀, w₀, hw₀⟩ := hex_cyc
  have hex_rot : ∃ (v : Fin n) (w : G.Walk v v), w.IsCycle ∧
      ∀ i : ℕ, 1 ≤ i → i ≤ 6 → (G.neighborSet (w.getVert i)).ncard ≤ 2 := by
    by_cases hbr : ∃ u ∈ w₀.support, 3 ≤ (G.neighborSet u).ncard
    · obtain ⟨u, hu, hdu⟩ := hbr
      refine ⟨u, w₀.rotate u hu, hw₀.rotate hu, ?_⟩
      intro i hi1 hi6
      have hlen : 7 ≤ (w₀.rotate u hu).length := hG u (w₀.rotate u hu) (hw₀.rotate hu)
      have hne : u ≠ (w₀.rotate u hu).getVert i := by
        intro heq
        have h0 : (w₀.rotate u hu).getVert 0 = (w₀.rotate u hu).getVert i := by simpa using heq
        have := cycle_getVert_inj (w₀.rotate u hu) (hw₀.rotate hu) 0 i (by omega) (by omega) h0
        omega
      by_contra hge
      have h3 : 3 ≤ (G.neighborSet ((w₀.rotate u hu).getVert i)).ncard := by omega
      have hwalk := hB u ((w₀.rotate u hu).getVert i) hne hdu h3 (walkPrefix (w₀.rotate u hu) i)
      rw [walkPrefix_length (w₀.rotate u hu) i (by omega)] at hwalk
      omega
    · refine ⟨v₀, w₀, hw₀, ?_⟩
      intro i hi1 hi6
      have hlen : 7 ≤ w₀.length := hG v₀ w₀ hw₀
      have hmem : w₀.getVert i ∈ w₀.support := SimpleGraph.Walk.getVert_mem_support w₀ (by omega)
      have hlt : ¬ (3 ≤ (G.neighborSet (w₀.getVert i)).ncard) := fun h3 => hbr ⟨_, hmem, h3⟩
      omega
  obtain ⟨v, w, hw, hdeg⟩ := hex_rot
  have hlen : 7 ≤ w.length := hG v w hw
  have hinj : ∀ i j, i < 7 → j < 7 → i ≠ j → w.getVert i ≠ w.getVert j :=
    fun i j hi hj hne heq => hne (cycle_getVert_inj w hw i j (by omega) (by omega) heq)
  have hne7 : ∀ i, 1 ≤ i → i ≤ 6 → w.getVert 7 ≠ w.getVert i := by
    intro i hi1 hi6 heq
    by_cases h7 : 7 < w.length
    · have := cycle_getVert_inj w hw 7 i h7 (by omega) heq
      omega
    · have hl7 : w.length = 7 := by omega
      have h0 : w.getVert 7 = w.getVert 0 := by rw [← hl7]; simp
      rw [h0] at heq
      exact hinj 0 i (by omega) (by omega) (by omega) heq
  have hadj : ∀ i, i < 7 → G.Adj (w.getVert i) (w.getVert (i + 1)) :=
    fun i hi => SimpleGraph.Walk.adj_getVert_succ w (by omega)
  refine ⟨w.getVert 0, w.getVert 1, w.getVert 2, w.getVert 3, w.getVert 4, w.getVert 5, w.getVert 6, w.getVert 7,
    ⟨hinj 0 1 (by omega) (by omega) (by omega), hinj 0 2 (by omega) (by omega) (by omega),
     hinj 0 3 (by omega) (by omega) (by omega), hinj 0 4 (by omega) (by omega) (by omega),
     hinj 0 5 (by omega) (by omega) (by omega), hinj 0 6 (by omega) (by omega) (by omega)⟩,
    ⟨hne7 1 (by omega) (by omega), hne7 2 (by omega) (by omega), hne7 3 (by omega) (by omega),
     hne7 4 (by omega) (by omega), hne7 5 (by omega) (by omega), hne7 6 (by omega) (by omega)⟩,
    ⟨hinj 1 2 (by omega) (by omega) (by omega), hinj 1 3 (by omega) (by omega) (by omega),
     hinj 1 4 (by omega) (by omega) (by omega), hinj 1 5 (by omega) (by omega) (by omega),
     hinj 1 6 (by omega) (by omega) (by omega), hinj 2 3 (by omega) (by omega) (by omega),
     hinj 2 4 (by omega) (by omega) (by omega), hinj 2 5 (by omega) (by omega) (by omega),
     hinj 2 6 (by omega) (by omega) (by omega), hinj 3 4 (by omega) (by omega) (by omega),
     hinj 3 5 (by omega) (by omega) (by omega), hinj 3 6 (by omega) (by omega) (by omega),
     hinj 4 5 (by omega) (by omega) (by omega), hinj 4 6 (by omega) (by omega) (by omega),
     hinj 5 6 (by omega) (by omega) (by omega)⟩,
    deg2_exact G _ _ _ (hinj 0 2 (by omega) (by omega) (by omega)) (hadj 0 (by omega)).symm (hadj 1 (by omega)) (hdeg 1 (by omega) (by omega)),
    deg2_exact G _ _ _ (hinj 1 3 (by omega) (by omega) (by omega)) (hadj 1 (by omega)).symm (hadj 2 (by omega)) (hdeg 2 (by omega) (by omega)),
    deg2_exact G _ _ _ (hinj 2 4 (by omega) (by omega) (by omega)) (hadj 2 (by omega)).symm (hadj 3 (by omega)) (hdeg 3 (by omega) (by omega)),
    deg2_exact G _ _ _ (hinj 3 5 (by omega) (by omega) (by omega)) (hadj 3 (by omega)).symm (hadj 4 (by omega)) (hdeg 4 (by omega) (by omega)),
    deg2_exact G _ _ _ (hinj 4 6 (by omega) (by omega) (by omega)) (hadj 4 (by omega)).symm (hadj 5 (by omega)) (hdeg 5 (by omega) (by omega)),
    deg2_exact G _ _ _ (hne7 5 (by omega) (by omega)).symm (hadj 5 (by omega)).symm (hadj 6 (by omega)) (hdeg 6 (by omega) (by omega))⟩

private lemma hardwire_prefix_nonconst {n k s : ℕ}
    {F : (Fin (n + k) → Bool) → Bool} {g : (Fin k → Bool) → Bool}
    (hC : HasCircuitSize (n + k) F s)
    (hFg : ∀ x : Fin (n + k) → Bool, F x = g (fun j : Fin k => x (Fin.natAdd n j)))
    (hg_nc : ∃ y y' : Fin k → Bool, g y ≠ g y') :
    HasCircuitSize k g s := by
  obtain ⟨C, hok, hsz, hev⟩ := hC
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOkGate g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hok g0 hg0)
  set init : List (Bool ⊕ ℕ) :=
    List.replicate n (Sum.inl false) ++ List.ofFn (fun j : Fin k => Sum.inr (j : ℕ)) with hinit
  set acc := elimPass k gs (init, []) with hacc
  have hinv : ∀ y : Fin k → Bool,
      ElimInv k (List.ofFn y)
        (wiresFrom gs (List.ofFn (Fin.append (fun _ : Fin n => false) y : Fin (n + k) → Bool)))
        acc := by
    intro y
    apply elimInv_pass k (List.ofFn y) gs _ (init, []) (fun g hg => (hnok g hg).1)
    refine ⟨by simp, by simp [hinit], ?_⟩
    intro i
    by_cases h1 : i < n
    · have hi' : i < n + k := by omega
      have hget : init.getD i (Sum.inl false) = Sum.inl false := by
        rw [hinit, List.getD_eq_getElem _ _ (by simp; omega),
            List.getElem_append_left (by simp; exact h1)]
        simp
      rw [hget]
      refine ⟨trivial, ?_⟩
      simp only [statVal]
      rw [ofFn_getD_lt _ _ _ hi']
      have hcast : (⟨i, hi'⟩ : Fin (n + k)) = Fin.castAdd k ⟨i, h1⟩ := rfl
      rw [hcast, Fin.append_left]
    · by_cases h2 : i < n + k
      · have hsub : i - n < k := by omega
        have hget : init.getD i (Sum.inl false) = Sum.inr (i - n) := by
          rw [hinit, List.getD_eq_getElem _ _ (by simp; omega),
              List.getElem_append_right (by simp; omega)]
          simp [List.getElem_ofFn]
        rw [hget]
        refine ⟨by simp [statValid]; exact hsub, ?_⟩
        simp only [statVal, wiresFrom_nil]
        rw [ofFn_getD_lt _ _ _ hsub, ofFn_getD_lt _ _ _ h2]
        have hnat : (⟨i, h2⟩ : Fin (n + k)) = Fin.natAdd n ⟨i - n, hsub⟩ := by
          ext; simp [Fin.natAdd]; omega
        rw [hnat, Fin.append_right]
      · rw [List.getD_eq_default _ _ (by simp [hinit]; omega),
            List.getD_eq_default _ _ (by simp; omega)]
        exact ⟨trivial, rfl⟩
  have hval : ∀ y : Fin k → Bool,
      statVal (wiresFrom acc.2 (List.ofFn y)) (acc.1.getD C.output (Sum.inl false)) = g y := by
    intro y
    rw [((hinv y).2.2 C.output).2, hgs, wiresFrom_norm]
    have h1 := hev (Fin.append (fun _ : Fin n => false) y)
    have h2 := hFg (Fin.append (fun _ : Fin n => false) y)
    have heq : (fun j : Fin k => (Fin.append (fun _ : Fin n => false) y : Fin (n + k) → Bool)
        (Fin.natAdd n j)) = y := by
      funext j; exact Fin.append_right _ _ j
    rw [heq] at h2
    exact h1.trans h2
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    obtain ⟨y, y', hne⟩ := hg_nc
    have hy := hval y; have hy' := hval y'
    rw [hst] at hy hy'
    exact absurd (hy.symm.trans hy') hne
  | inr j =>
    refine ⟨⟨acc.2, j⟩, elimPass_ok k gs _ (by simp), ?_, ?_⟩
    · show acc.2.length ≤ s
      have := elimPass_len k gs (init, [])
      rw [← hacc] at this
      have hlen : gs.length = C.gates.length := by simp [hgs]
      have hsz' : C.gates.length ≤ s := hsz
      simp only [List.length_nil, zero_add] at this
      omega
    · intro y
      have := hval y
      rw [hst] at this
      exact this

private def initVar (m : ℕ) (v : Fin m) (b : Bool) : List (Bool ⊕ ℕ) :=
  List.ofFn fun i : Fin m => if i = v then Sum.inl b else Sum.inr (i : ℕ)

private lemma elimInv_initVar (m : ℕ) (v : Fin m) (b : Bool) (x : Fin m → Bool) :
    ElimInv m (List.ofFn x) (List.ofFn (Function.update x v b)) (initVar m v b, []) := by
  refine ⟨by simp, by simp [initVar], ?_⟩
  intro i
  by_cases hi : i < m
  · have hget : (initVar m v b).getD i (Sum.inl false) =
        if (⟨i, hi⟩ : Fin m) = v then Sum.inl b else Sum.inr i := by
      rw [initVar, ofFn_getD_lt _ _ _ hi]
    rw [hget]
    by_cases heq : (⟨i, hi⟩ : Fin m) = v
    · simp only [heq, ↓reduceIte, statValid, statVal]
      rw [ofFn_getD_lt _ _ _ hi, heq, Function.update_self]
      exact ⟨trivial, rfl⟩
    · simp only [heq, ↓reduceIte, statValid, statVal, wiresFrom_nil]
      refine ⟨by omega, ?_⟩
      rw [ofFn_getD_lt _ _ _ hi, ofFn_getD_lt _ _ _ hi, Function.update_of_ne heq]
  · rw [List.getD_eq_default _ _ (by simp [initVar]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

private lemma elim_one_var {m s : ℕ} {F : (Fin m → Bool) → Bool} (v : Fin m) (b : Bool)
    (hC : HasCircuitSize m F s)
    (hdep : ∃ x : Fin m → Bool, F (Function.update x v false) ≠ F (Function.update x v true))
    (hnc : ∃ x x' : Fin m → Bool, F (Function.update x v b) ≠ F (Function.update x' v b)) :
    1 ≤ s ∧ HasCircuitSize m (fun x => F (Function.update x v b)) (s - 1) := by
  obtain ⟨C, hok, hsz, hev⟩ := hC
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOkGate g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hok g0 hg0)
  have hout_ne : C.output ≠ (v : ℕ) := by
    intro heq
    obtain ⟨x, x', hne⟩ := hnc
    have h1 := hev (Function.update x v b)
    have h2 := hev (Function.update x' v b)
    have hw1 : (C.wires (List.ofFn (Function.update x v b))).getD (v : ℕ) false = b := by
      show (wiresFrom C.gates (List.ofFn (Function.update x v b))).getD (v : ℕ) false = b
      rw [wiresFrom_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ v.isLt]
      simp
    have hw2 : (C.wires (List.ofFn (Function.update x' v b))).getD (v : ℕ) false = b := by
      show (wiresFrom C.gates (List.ofFn (Function.update x' v b))).getD (v : ℕ) false = b
      rw [wiresFrom_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ v.isLt]
      simp
    have e1 : F (Function.update x v b) = b := by
      rw [← h1]; show (C.wires _).getD C.output false = b; rw [heq]; exact hw1
    have e2 : F (Function.update x' v b) = b := by
      rw [← h2]; show (C.wires _).getD C.output false = b; rw [heq]; exact hw2
    exact hne (e1.trans e2.symm)
  have hex : ∃ g ∈ gs, (v : ℕ) ∈ g.inputs := by
    by_contra hno
    have hno' : ∀ g ∈ gs, (v : ℕ) ∉ g.inputs := fun g hg hv => hno ⟨g, hg, hv⟩
    obtain ⟨x, hne⟩ := hdep
    have hag := wiresFrom_agree gs {(v : ℕ)}
      (List.ofFn (Function.update x v false))
      (List.ofFn (Function.update x v true))
      (by simp)
      (by intro u hu; simp at hu; subst hu; simp)
      (by
        intro i hi
        simp at hi
        by_cases hlt : i < m
        · have hne' : (⟨i, hlt⟩ : Fin m) ≠ v := by
            intro h; apply hi; exact congrArg Fin.val h
          rw [ofFn_getD_lt _ _ _ hlt, ofFn_getD_lt _ _ _ hlt,
              Function.update_of_ne hne', Function.update_of_ne hne']
        · rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp; omega)])
      (by
        intro g hg i hi hmem
        simp at hmem
        subst hmem
        exact hno' g hg hi)
    have hco : C.output ∉ ({(v : ℕ)} : Set ℕ) := by simpa using hout_ne
    have hEq := hag.2 C.output hco
    rw [hgs, wiresFrom_norm, wiresFrom_norm] at hEq
    exact hne ((hev _).symm.trans (hEq.trans (hev _)))
  set acc := elimPass m gs (initVar m v b, []) with hacc
  have hlen : acc.2.length + 1 ≤ gs.length := by
    have := elimPass_len_lt m (v : ℕ) gs (initVar m v b, []) hnok
      (by simp [initVar])
      ⟨b, by rw [initVar, ofFn_getD_lt _ _ _ v.isLt]; simp⟩
      hex
    rw [← hacc] at this
    simpa using this
  have hgs_len : gs.length = C.gates.length := by simp [hgs]
  have hsz' : C.gates.length ≤ s := hsz
  have hval : ∀ x : Fin m → Bool,
      statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) =
        F (Function.update x v b) := by
    intro x
    have hinv := elimInv_pass m (List.ofFn x) gs _ (initVar m v b, [])
      (fun g hg => (hnok g hg).1) (elimInv_initVar m v b x)
    rw [← hacc] at hinv
    rw [(hinv.2.2 C.output).2, hgs, wiresFrom_norm]
    exact hev (Function.update x v b)
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    obtain ⟨x, x', hne⟩ := hnc
    have hx := hval x; have hx' := hval x'
    rw [hst] at hx hx'
    exact absurd (hx.symm.trans hx') hne
  | inr j =>
    refine ⟨by omega, ⟨acc.2, j⟩, elimPass_ok m gs _ (by simp), ?_, ?_⟩
    · show acc.2.length ≤ s - 1
      omega
    · intro x
      have := hval x
      rw [hst] at this
      exact this

private lemma list_split_unique_filter {α : Type*} (p : α → Bool) (l : List α)
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
      rw [hnil] at this
      simp at this
    | false =>
      have h1 : (xs.filter p).length = 1 := by
        simpa [hpx] using h
      obtain ⟨l₁, a, l₂, rfl, hpa, hl₁, hl₂⟩ := ih h1
      refine ⟨x :: l₁, a, l₂, by simp, hpa, ?_, hl₂⟩
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy'
      · exact hpx
      · exact hl₁ y hy'

private lemma elim_two_var {m s : ℕ} {F : (Fin m → Bool) → Bool} (v : Fin m)
    (hC : HasCircuitSize m F s)
    (hdep : ∃ x : Fin m → Bool, F (Function.update x v false) ≠ F (Function.update x v true))
    (hnc0 : ∃ x x' : Fin m → Bool,
      F (Function.update x v false) ≠ F (Function.update x' v false))
    (hnc1 : ∃ x x' : Fin m → Bool,
      F (Function.update x v true) ≠ F (Function.update x' v true)) :
    2 ≤ s ∧ (HasCircuitSize m (fun x => F (Function.update x v false)) (s - 2) ∨
      HasCircuitSize m (fun x => F (Function.update x v true)) (s - 2)) := by
  obtain ⟨C, hok, hsz, hev⟩ := hC
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOkGate g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hok g0 hg0)
  have hgs_len : gs.length = C.gates.length := by simp [hgs]
  have hsz' : C.gates.length ≤ s := hsz
  have hout_ne : C.output ≠ (v : ℕ) := by
    intro heq
    obtain ⟨x, x', hne⟩ := hnc0
    have h1 := hev (Function.update x v false)
    have h2 := hev (Function.update x' v false)
    have hw1 : (C.wires (List.ofFn (Function.update x v false))).getD (v : ℕ) false = false := by
      show (wiresFrom C.gates (List.ofFn (Function.update x v false))).getD (v : ℕ) false = false
      rw [wiresFrom_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ v.isLt]
      simp
    have hw2 : (C.wires (List.ofFn (Function.update x' v false))).getD (v : ℕ) false = false := by
      show (wiresFrom C.gates (List.ofFn (Function.update x' v false))).getD (v : ℕ) false = false
      rw [wiresFrom_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ v.isLt]
      simp
    have e1 : F (Function.update x v false) = false := by
      rw [← h1]; show (C.wires _).getD C.output false = false; rw [heq]; exact hw1
    have e2 : F (Function.update x' v false) = false := by
      rw [← h2]; show (C.wires _).getD C.output false = false; rw [heq]; exact hw2
    exact hne (e1.trans e2.symm)
  set cnt := (gs.filter (fun g => decide ((v : ℕ) ∈ g.inputs))).length with hcnt
  by_cases hge2 : 2 ≤ cnt
  · set acc := elimPass m gs (initVar m v false, []) with hacc
    have hlen : acc.2.length + 2 ≤ gs.length := by
      have := elimPass_len_two m (v : ℕ) gs (initVar m v false, []) hnok
        (by simp [initVar])
        ⟨false, by rw [initVar, ofFn_getD_lt _ _ _ v.isLt]; simp⟩
        (by rw [← hcnt]; exact hge2)
      rw [← hacc] at this
      simpa using this
    have hval : ∀ x : Fin m → Bool,
        statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) =
          F (Function.update x v false) := by
      intro x
      have hinv := elimInv_pass m (List.ofFn x) gs _ (initVar m v false, [])
        (fun g hg => (hnok g hg).1) (elimInv_initVar m v false x)
      rw [← hacc] at hinv
      rw [(hinv.2.2 C.output).2, hgs, wiresFrom_norm]
      exact hev (Function.update x v false)
    cases hst : acc.1.getD C.output (Sum.inl false) with
    | inl c =>
      obtain ⟨x, x', hne⟩ := hnc0
      have hx := hval x; have hx' := hval x'
      rw [hst] at hx hx'
      exact absurd (hx.symm.trans hx') hne
    | inr j =>
      refine ⟨by omega, Or.inl ⟨⟨acc.2, j⟩, elimPass_ok m gs _ (by simp), ?_, ?_⟩⟩
      · show acc.2.length ≤ s - 2; omega
      · intro x; have := hval x; rw [hst] at this; exact this
  · by_cases hzero : cnt = 0
    · exfalso
      have hnil : gs.filter (fun g => decide ((v : ℕ) ∈ g.inputs)) = [] :=
        List.eq_nil_of_length_eq_zero (by rw [← hcnt]; exact hzero)
      obtain ⟨x, hne⟩ := hdep
      have hag := wiresFrom_agree gs {(v : ℕ)}
        (List.ofFn (Function.update x v false))
        (List.ofFn (Function.update x v true))
        (by simp)
        (by intro u hu; simp at hu; subst hu; simp)
        (by
          intro i hi; simp at hi
          by_cases hlt : i < m
          · have hne' : (⟨i, hlt⟩ : Fin m) ≠ v := by
              intro h; apply hi; exact congrArg Fin.val h
            rw [ofFn_getD_lt _ _ _ hlt, ofFn_getD_lt _ _ _ hlt,
                Function.update_of_ne hne', Function.update_of_ne hne']
          · rw [List.getD_eq_default _ _ (by simp; omega),
                List.getD_eq_default _ _ (by simp; omega)])
        (by
          intro g hg i hi hmem
          simp at hmem; subst hmem
          have : g ∈ gs.filter (fun g => decide ((v : ℕ) ∈ g.inputs)) :=
            List.mem_filter.2 ⟨hg, decide_eq_true hi⟩
          rw [hnil] at this; simp at this)
      have hEq := hag.2 C.output (by simpa using hout_ne)
      rw [hgs, wiresFrom_norm, wiresFrom_norm] at hEq
      exact hne ((hev _).symm.trans (hEq.trans (hev _)))
    · have hone : (gs.filter (fun g => decide ((v : ℕ) ∈ g.inputs))).length = 1 := by
        rw [← hcnt]; omega
      have hsp := list_split_unique_filter (fun g => decide ((v : ℕ) ∈ g.inputs)) gs hone
      rcases hsp with ⟨gs₁, g₁, gs₂, hsplit, hg₁in, hgs₁no, hgs₂no⟩
      have hv_in : (v : ℕ) ∈ g₁.inputs := of_decide_eq_true hg₁in
      have hnok₁ : NOkGate g₁ := hnok g₁ (by rw [hsplit]; simp)
      set b : Bool := match g₁.op with | GateOp.or => true | _ => false with hb
      have hncb : ∃ x x' : Fin m → Bool,
          F (Function.update x v b) ≠ F (Function.update x' v b) := by
        cases hbc : b with
        | false => exact hnc0
        | true => exact hnc1
      set acc₁ := elimPass m gs₁ (initVar m v b, []) with hacc₁
      set accM := elimStep m acc₁ g₁ with haccM
      set acc := elimPass m gs₂ accM with hacc
      have hacc_eq : acc = elimPass m gs (initVar m v b, []) := by
        rw [hsplit, elimPass_append, elimPass_append, ← hacc₁, elimPass_cons, elimPass_nil, ← haccM]
      have hacc₁_len : acc₁.1.length = m + gs₁.length := by
        rw [hacc₁, elimPass_fst_len]; simp [initVar]
      have hacc₁_v : acc₁.1.getD (v : ℕ) (Sum.inl false) = Sum.inl b := by
        rw [hacc₁, elimPass_getD_lt _ _ _ _ _ (by simp [initVar])]
        rw [initVar, ofFn_getD_lt _ _ _ v.isLt]
        simp
      have hmid_props : accM.2.length = acc₁.2.length ∧
          ∃ c : Bool, accM.1.getD (m + gs₁.length) (Sum.inl false) = Sum.inl c := by
        have hmem : Sum.inl b ∈ (g₁.inputs.map fun i => acc₁.1.getD i (Sum.inl false)) :=
          List.mem_map.2 ⟨(v : ℕ), hv_in, hacc₁_v⟩
        have hres : ∃ c : Bool,
            simplifyGate g₁.op (m + acc₁.2.length)
              (g₁.inputs.map fun i => acc₁.1.getD i (Sum.inl false)) = (none, Sum.inl c) := by
          rcases hnok₁.1.1 with hop | hop | hop
          · have : g₁.op = GateOp.and := hop
            have hbf : b = false := by simp [hb, this]
            rw [this]
            rw [hbf] at hmem
            exact ⟨false, simplifyGate_and_false _ _ (by simp; exact hnok₁.1.2) hmem⟩
          · have : g₁.op = GateOp.or := hop
            have hbt : b = true := by simp [hb, this]
            rw [this]
            rw [hbt] at hmem
            exact ⟨true, simplifyGate_or_true _ _ (by simp; exact hnok₁.1.2) hmem⟩
          · have : g₁.op = GateOp.not := hop
            have hbf : b = false := by simp [hb, this]
            have hlen1 : g₁.inputs.length ≤ 1 := hnok₁.2 this
            have hsing : g₁.inputs = [(v : ℕ)] := by
              rcases hgi : g₁.inputs with _ | ⟨a, _ | ⟨d, l⟩⟩
              · rw [hgi] at hv_in; simp at hv_in
              · rw [hgi] at hv_in; simp at hv_in; subst hv_in; rfl
              · rw [hgi] at hlen1; simp at hlen1
            rw [this, hsing, List.map_singleton, hacc₁_v, hbf]
            exact ⟨true, simplifyGate_not_const _ false⟩
        obtain ⟨c, hc⟩ := hres
        refine ⟨by simp only [haccM, elimStep, hc, Option.toList_none, List.append_nil], c, ?_⟩
        simp only [haccM, elimStep, hc]
        exact getD_snoc_eq _ _ _ _ hacc₁_len.symm
      have hval : ∀ x : Fin m → Bool,
          statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) =
            F (Function.update x v b) := by
        intro x
        have hinv := elimInv_pass m (List.ofFn x) gs _ (initVar m v b, [])
          (fun g hg => (hnok g hg).1) (elimInv_initVar m v b x)
        rw [← hacc_eq] at hinv
        rw [(hinv.2.2 C.output).2, hgs, wiresFrom_norm]
        exact hev (Function.update x v b)
      have hout_ne_w1 : C.output ≠ m + gs₁.length := by
        intro heq
        obtain ⟨c, hc⟩ := hmid_props.2
        have hacc_w1 : acc.1.getD C.output (Sum.inl false) = Sum.inl c := by
          rw [heq, hacc, elimPass_getD_lt _ _ _ _ _ (by simp [haccM, elimStep, hacc₁_len])]
          exact hc
        obtain ⟨x, x', hne⟩ := hncb
        have hx := hval x; have hx' := hval x'
        rw [hacc_w1] at hx hx'
        exact hne (hx.symm.trans hx')
      have hex₂ : ∃ g ∈ gs₂, m + gs₁.length ∈ g.inputs := by
        by_contra hno
        have hno' : ∀ g ∈ gs₂, m + gs₁.length ∉ g.inputs := fun g hg hw => hno ⟨g, hg, hw⟩
        obtain ⟨x, hne⟩ := hdep
        have hag₁ := wiresFrom_agree gs₁ {(v : ℕ)}
          (List.ofFn (Function.update x v false))
          (List.ofFn (Function.update x v true))
          (by simp)
          (by intro u hu; simp at hu; subst hu; simp)
          (by
            intro i hi; simp at hi
            by_cases hlt : i < m
            · have hne' : (⟨i, hlt⟩ : Fin m) ≠ v := by
                intro h; apply hi; exact congrArg Fin.val h
              rw [ofFn_getD_lt _ _ _ hlt, ofFn_getD_lt _ _ _ hlt,
                  Function.update_of_ne hne', Function.update_of_ne hne']
            · rw [List.getD_eq_default _ _ (by simp; omega),
                  List.getD_eq_default _ _ (by simp; omega)])
          (by
            intro g hg i hi hmem
            simp at hmem; subst hmem
            have := hgs₁no g hg
            simp [hi] at this)
        set w0 := wiresFrom gs₁ (List.ofFn (Function.update x v false))
        set w1 := wiresFrom gs₁ (List.ofFn (Function.update x v true))
        have hw0_len : w0.length = m + gs₁.length := by simp [w0, wiresFrom_length]
        have hw1_len : w1.length = m + gs₁.length := by simp [w1, wiresFrom_length]
        have hag₂ := wiresFrom_agree gs₂ {(v : ℕ), m + gs₁.length}
          (wiresFrom [g₁] w0) (wiresFrom [g₁] w1)
          (by simp [wiresFrom_length, hw0_len, hw1_len])
          (by
            intro u hu
            rcases hu with rfl | rfl
            · simp [wiresFrom_length, hw0_len]; omega
            · simp [wiresFrom_length, hw0_len])
          (by
            intro i hi
            have hiv : i ≠ (v : ℕ) := fun h => hi (Or.inl h)
            have hiw : i ≠ m + gs₁.length := fun h => hi (Or.inr h)
            simp only [wiresFrom_cons, wiresFrom_nil]
            rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
            exact hag₁.2 i (by simpa using hiv))
          (by
            intro g hg i hi hmem
            rcases hmem with rfl | rfl
            · have := hgs₂no g hg; simp [hi] at this
            · exact hno' g hg hi)
        have hco : C.output ∉ ({(v : ℕ), m + gs₁.length} : Set ℕ) := by
          intro h; rcases h with h | h
          · exact hout_ne h
          · exact hout_ne_w1 h
        have hEq := hag₂.2 C.output hco
        have hrew0 : wiresFrom gs₂ (wiresFrom [g₁] w0) =
            wiresFrom gs (List.ofFn (Function.update x v false)) := by
          rw [hsplit, wiresFrom_append, wiresFrom_append]
        have hrew1 : wiresFrom gs₂ (wiresFrom [g₁] w1) =
            wiresFrom gs (List.ofFn (Function.update x v true)) := by
          rw [hsplit, wiresFrom_append, wiresFrom_append]
        rw [hrew0, hrew1, hgs, wiresFrom_norm, wiresFrom_norm] at hEq
        exact hne ((hev _).symm.trans (hEq.trans (hev _)))
      have hlen₂ := elimPass_len_lt m (m + gs₁.length) gs₂ accM
        (fun g hg => hnok g (by rw [hsplit]; simp [hg]))
        (by simp [haccM, elimStep, hacc₁_len])
        hmid_props.2
        hex₂
      rw [← hacc] at hlen₂
      have hlen₁ : acc₁.2.length ≤ gs₁.length := by
        have := elimPass_len m gs₁ (initVar m v b, [])
        rw [← hacc₁] at this; simpa using this
      have hsplit_len : gs.length = gs₁.length + 1 + gs₂.length := by
        rw [hsplit]; simp; omega
      have htot : acc.2.length + 2 ≤ gs.length := by omega
      cases hst : acc.1.getD C.output (Sum.inl false) with
      | inl c =>
        obtain ⟨x, x', hne⟩ := hncb
        have hx := hval x; have hx' := hval x'
        rw [hst] at hx hx'
        exact absurd (hx.symm.trans hx') hne
      | inr j =>
        have hres : HasCircuitSize m (fun x => F (Function.update x v b)) (s - 2) := by
          refine ⟨⟨acc.2, j⟩, ?_, ?_, ?_⟩
          · rw [hacc_eq]; exact elimPass_ok m gs _ (by simp)
          · show acc.2.length ≤ s - 2; omega
          · intro x; have := hval x; rw [hst] at this; exact this
        refine ⟨by omega, ?_⟩
        cases hbc : b with
        | false => rw [hbc] at hres; exact Or.inl hres
        | true => rw [hbc] at hres; exact Or.inr hres

private lemma min_output_lt {m : ℕ} (C : Circuit)
    (hnc : ∃ x x' : Fin m → Bool, circuitFun m C x ≠ circuitFun m C x') :
    C.output < m + C.gates.length := by
  by_contra hge
  obtain ⟨x, x', hne⟩ := hnc
  have h1 : circuitFun m C x = false := by
    show (wiresFrom C.gates (List.ofFn x)).getD C.output false = false
    exact List.getD_eq_default _ _ (by rw [wiresFrom_length]; simp; omega)
  have h2 : circuitFun m C x' = false := by
    show (wiresFrom C.gates (List.ofFn x')).getD C.output false = false
    exact List.getD_eq_default _ _ (by rw [wiresFrom_length]; simp; omega)
  exact hne (h1.trans h2.symm)

private lemma min_no_const {m : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hmin : ∀ s' < C.gates.length, ¬ HasCircuitSize m (circuitFun m C) s')
    (hnc : ∃ x x' : Fin m → Bool, circuitFun m C x ≠ circuitFun m C x')
    (j : ℕ) (hj : j < C.gates.length) (c : Bool) :
    ¬ (∀ x : Fin m → Bool, (C.wires (List.ofFn x)).getD (m + j) false = c) := by
  intro hconst
  exact hmin (C.gates.length - 1) (by omega) (deleteConstGate C hnok j hj c hconst hnc)

private lemma min_no_alias {m : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hmin : ∀ s' < C.gates.length, ¬ HasCircuitSize m (circuitFun m C) s')
    (j a : ℕ) (hj : j < C.gates.length) (ha : a < m + j) :
    ¬ (∀ x : Fin m → Bool, (C.wires (List.ofFn x)).getD (m + j) false =
      (C.wires (List.ofFn x)).getD a false) := by
  intro heq
  exact hmin (C.gates.length - 1) (by omega)
    (deleteAliasGate C (fun g hg => (hnok g hg).1) j a hj ha heq)

private lemma min_no_dead {m : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hmin : ∀ s' < C.gates.length, ¬ HasCircuitSize m (circuitFun m C) s')
    (j : ℕ) (hj : j < C.gates.length) :
    C.output = m + j ∨ ∃ j' : ℕ, ∃ hj' : j' < C.gates.length, j < j' ∧ (m + j) ∈ C.gates[j'].inputs := by
  by_contra h
  have hout : C.output ≠ m + j := fun heq => h (Or.inl heq)
  have hno : ∀ j' : ℕ, (hj' : j' < C.gates.length) → j < j' → (m + j) ∉ C.gates[j'].inputs :=
    fun j' hj' hlt hmem => h (Or.inr ⟨j', hj', hlt, hmem⟩)
  exact hmin (C.gates.length - 1) (by omega)
    (deleteDeadGate C (fun g hg => (hnok g hg).1) j hj hout hno)

private lemma wire_eval_gate {m : ℕ} (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (x : Fin m → Bool) :
    (C.wires (List.ofFn x)).getD (m + j) false =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i =>
        if i < m + j then (C.wires (List.ofFn x)).getD i false else false) := by
  show (wiresFrom C.gates (List.ofFn x)).getD (m + j) false = _
  have h1 := wiresFrom_getD_gate C.gates (List.ofFn x) j hj
  rw [List.length_ofFn] at h1
  rw [h1]
  congr 1
  apply List.map_congr_left
  intro i _
  have hlen : (wiresFrom (C.gates.take j) (List.ofFn x)).length = m + j := by
    rw [wiresFrom_length, List.length_ofFn, List.length_take, Nat.min_eq_left (by omega)]
  by_cases hi : i < m + j
  · simp only [hi, ↓reduceIte]
    have hsp : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
    conv_rhs => rw [show C.wires (List.ofFn x) = wiresFrom C.gates (List.ofFn x) from rfl, hsp, wiresFrom_append]
    exact (wiresFrom_getD_lt _ _ _ (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact List.getD_eq_default _ _ (by omega)

private lemma min_gate_wf {m : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hmin : ∀ s' < C.gates.length, ¬ HasCircuitSize m (circuitFun m C) s')
    (hnc : ∃ x x' : Fin m → Bool, circuitFun m C x ≠ circuitFun m C x')
    (j : ℕ) (hj : j < C.gates.length) :
    (C.gates[j].op = GateOp.not → ∃ a, a < m + j ∧ C.gates[j].inputs = [a]) ∧
    ((C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or) →
      ∃ a b, a < m + j ∧ b < m + j ∧ a ≠ b ∧ C.gates[j].inputs = [a, b]) := by
  have hg := hnok C.gates[j] (List.getElem_mem hj)
  constructor
  · intro hop
    have hlen1 := hg.2 hop
    rcases hins : C.gates[j].inputs with _ | ⟨a, _ | ⟨b, l⟩⟩
    · exfalso
      apply min_no_const C hnok hmin hnc j hj true
      intro x; rw [wire_eval_gate C j hj x, hop, hins]; rfl
    · by_cases ha : a < m + j
      · exact ⟨a, ha, rfl⟩
      · exfalso
        apply min_no_const C hnok hmin hnc j hj true
        intro x; rw [wire_eval_gate C j hj x, hop, hins]; simp [ha, GateOp.eval]
    · rw [hins] at hlen1; simp at hlen1
  · intro hop
    have hlen2 := hg.1.2
    rcases hins : C.gates[j].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · exfalso
      rcases hop with hop | hop
      · apply min_no_const C hnok hmin hnc j hj true
        intro x; rw [wire_eval_gate C j hj x, hop, hins]; rfl
      · apply min_no_const C hnok hmin hnc j hj false
        intro x; rw [wire_eval_gate C j hj x, hop, hins]; rfl
    · exfalso
      by_cases ha : a < m + j
      · apply min_no_alias C hnok hmin j a hj ha
        intro x; rw [wire_eval_gate C j hj x, hins]
        rcases hop with hop | hop <;> simp [hop, ha, GateOp.eval]
      · apply min_no_const C hnok hmin hnc j hj false
        intro x; rw [wire_eval_gate C j hj x, hins]
        rcases hop with hop | hop <;> simp [hop, ha, GateOp.eval]
    · by_cases ha : a < m + j
      · by_cases hb : b < m + j
        · by_cases hab : a = b
          · exfalso
            subst hab
            apply min_no_alias C hnok hmin j a hj ha
            intro x; rw [wire_eval_gate C j hj x, hins]
            rcases hop with hop | hop <;> simp [hop, ha, GateOp.eval]
          · exact ⟨a, b, ha, hb, hab, rfl⟩
        · exfalso
          rcases hop with hop | hop
          · apply min_no_const C hnok hmin hnc j hj false
            intro x; rw [wire_eval_gate C j hj x, hop, hins]; simp [ha, hb, GateOp.eval]
          · apply min_no_alias C hnok hmin j a hj ha
            intro x; rw [wire_eval_gate C j hj x, hop, hins]; simp [ha, hb, GateOp.eval]
      · exfalso
        by_cases hb : b < m + j
        · rcases hop with hop | hop
          · apply min_no_const C hnok hmin hnc j hj false
            intro x; rw [wire_eval_gate C j hj x, hop, hins]; simp [ha, hb, GateOp.eval]
          · apply min_no_alias C hnok hmin j b hj hb
            intro x; rw [wire_eval_gate C j hj x, hop, hins]; simp [ha, hb, GateOp.eval]
        · apply min_no_const C hnok hmin hnc j hj false
          intro x; rw [wire_eval_gate C j hj x, hins]
          rcases hop with hop | hop <;> simp [hop, ha, hb, GateOp.eval]
    · rw [hins] at hlen2; simp at hlen2

private lemma elim_var_circuit {m : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (v : Fin m) (b : Bool)
    (hnc : ∃ x x' : Fin m → Bool,
      circuitFun m C (Function.update x v b) ≠ circuitFun m C (Function.update x' v b)) :
    let acc := elimPass m C.gates (initVar m v b, [])
    ∃ out : ℕ, acc.1.getD C.output (Sum.inl false) = Sum.inr out ∧
      (∀ g ∈ acc.2, OkGate g) ∧
      acc.2.length + (elimDropped m C.gates (initVar m v b, [])).card = C.gates.length ∧
      circuitFun m ⟨acc.2, out⟩ = fun x => circuitFun m C (Function.update x v b) := by
  intro acc
  have hval : ∀ x : Fin m → Bool,
      statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) =
        circuitFun m C (Function.update x v b) := by
    intro x
    have hinv := elimInv_pass m (List.ofFn x) C.gates _ (initVar m v b, [])
      (fun g hg => (hnok g hg).1) (elimInv_initVar m v b x)
    exact (hinv.2.2 C.output).2
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    obtain ⟨x, x', hne⟩ := hnc
    have hx := hval x; have hx' := hval x'
    rw [hst] at hx hx'
    exact absurd (hx.symm.trans hx') hne
  | inr out =>
    refine ⟨out, rfl, elimPass_ok m C.gates _ (by simp), ?_, ?_⟩
    · have := elimPass_card_dropped m C.gates (initVar m v b, [])
      simpa using this
    · funext x
      have := hval x
      rw [hst] at this
      exact this

private lemma elim_var_dead_wire {m : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (v : Fin m) (b : Bool)
    (hnc : ∃ x x' : Fin m → Bool,
      circuitFun m C (Function.update x v b) ≠ circuitFun m C (Function.update x' v b))
    (j_z j_u : ℕ) (hj_z : j_z < C.gates.length) (hj_u : j_u < C.gates.length) (hzu : j_z < j_u)
    (hout_ne : C.output ≠ m + j_z)
    (honly : ∀ j' : ℕ, (hj' : j' < C.gates.length) → j_z < j' →
      (m + j_z) ∈ C.gates[j'].inputs → j' = j_u)
    (hwf : ∀ j : ℕ, (hj : j < C.gates.length) → ∀ i ∈ C.gates[j].inputs, i < m + j)
    (hnot_drop : j_z ∉ elimDropped m C.gates (initVar m v b, []))
    (hc_u : ∃ c : Bool, (elimState m C.gates (initVar m v b, []) (j_u + 1)).1.getD (m + j_u)
      (Sum.inl false) = Sum.inl c) :
    HasCircuitSize m (fun x => circuitFun m C (Function.update x v b))
      (C.gates.length - (elimDropped m C.gates (initVar m v b, [])).card - 1) := by
  set init := (initVar m v b, ([] : List Gate)) with hinit
  set acc := elimPass m C.gates init with hacc
  obtain ⟨out, hout_st, hok_acc, hcard_acc, hfun_acc⟩ := elim_var_circuit C hnok v b hnc
  set k_z := (elimState m C.gates init j_z).2.length with hk_z
  have hsome_z : ∃ g_z, (simplifyGate C.gates[j_z].op (m + k_z)
      (C.gates[j_z].inputs.map fun i => (elimState m C.gates init j_z).1.getD i (Sum.inl false))).1 =
        some g_z := by
    cases hopt : (simplifyGate C.gates[j_z].op (m + k_z)
        (C.gates[j_z].inputs.map fun i => (elimState m C.gates init j_z).1.getD i (Sum.inl false))).1 with
    | none =>
      exfalso
      apply hnot_drop
      rw [elimDropped, Finset.mem_filter, Finset.mem_range]
      refine ⟨hj_z, ?_⟩
      simp only [hj_z, ↓reduceDIte]
      rw [hopt]; rfl
    | some g_z => exact ⟨g_z, rfl⟩
  obtain ⟨g_z, hg_z⟩ := hsome_z
  have hk_z_lt : k_z < acc.2.length := by
    have h1 : (elimState m C.gates init (j_z + 1)).2.length = k_z + 1 := by
      rw [elimState_succ m C.gates init j_z hj_z]
      simp only [elimStep, ← hk_z, hg_z, Option.toList_some, List.length_append, List.length_singleton]
    have h2 := elimState_snd_mono m C.gates init (j_z + 1) C.gates.length (by omega)
    rw [elimState_end, ← hacc] at h2
    omega
  have hst_z : (elimState m C.gates init (j_z + 1)).1.getD (m + j_z) (Sum.inl false) =
      Sum.inr (m + k_z) := by
    have h := elimState_getD_at m C.gates init j_z hj_z
    have hinit_len : init.1.length = m := by simp [hinit, initVar]
    rw [hinit_len] at h
    rw [h, ← hk_z]
    exact simplifyGate_some_snd _ _ _ g_z hg_z
  have hvalid_before : ∀ t ≤ C.gates.length, ∀ i < m + t,
      statValid (m + (elimState m C.gates init t).2.length)
        ((elimState m C.gates init t).1.getD i (Sum.inl false)) := by
    intro t ht i _
    have hinv := elimInv_pass m (List.ofFn (fun _ : Fin m => false)) (C.gates.take t) _ init
      (fun g hg => (hnok g (List.mem_of_mem_take hg)).1)
      (elimInv_initVar m v b (fun _ : Fin m => false))
    exact (hinv.2.2 i).1
  have hno_alias_kz : ∀ t ≤ C.gates.length, ∀ i < m + t, i ≠ m + j_z →
      (elimState m C.gates init t).1.getD i (Sum.inl false) ≠ Sum.inr (m + k_z) := by
    intro t
    induction t with
    | zero =>
      intro _ i hi _
      have hv := hvalid_before 0 (Nat.zero_le _) i hi
      intro heq
      rw [heq] at hv
      simp only [statValid, elimState_zero, hinit, List.length_nil, add_zero] at hv
      omega
    | succ t ih =>
      intro ht i hi hne
      by_cases hilt : i < m + t
      · rw [elimState_getD_mono m C.gates init t (t + 1) i _ (by omega) ht (by simp [hinit, initVar]; exact hilt)]
        exact ih (by omega) i hilt hne
      · have hieq : i = m + t := by omega
        subst hieq
        have htlt : t < C.gates.length := by omega
        by_cases htlz : t < j_z
        · have hv := hvalid_before (t + 1) ht (m + t) (by omega)
          have hmono := elimState_snd_mono m C.gates init (t + 1) j_z (by omega)
          intro heq
          rw [heq] at hv
          simp only [statValid] at hv
          omega
        · have hgt : j_z < t := by omega
          by_cases htu : t = j_u
          · subst htu
            obtain ⟨c, hc⟩ := hc_u
            rw [hc]; simp
          · have hnot_in : (m + j_z) ∉ C.gates[t].inputs :=
              fun hmem => htu (honly t htlt hgt hmem)
            have hget := elimState_getD_at m C.gates init t htlt
            have hinit_len : init.1.length = m := by simp [hinit, initVar]
            rw [hinit_len] at hget
            rw [hget]
            intro heq
            rcases simplifyGate_out_wire_mem _ _ _ (m + k_z) heq with hnew | hmem
            · have h1 : (elimState m C.gates init (j_z + 1)).2.length = k_z + 1 := by
                rw [elimState_succ m C.gates init j_z hj_z]
                simp only [elimStep, ← hk_z, hg_z, Option.toList_some, List.length_append, List.length_singleton]
              have h2 := elimState_snd_mono m C.gates init (j_z + 1) t (by omega)
              omega
            · obtain ⟨idx, hidx_in, hidx_eq⟩ := List.mem_map.1 hmem
              have hidx_lt : idx < m + t := hwf t htlt idx hidx_in
              have hidx_ne : idx ≠ m + j_z := fun h => hnot_in (h ▸ hidx_in)
              exact ih (by omega) idx hidx_lt hidx_ne hidx_eq
  have hout_ne_kz : out ≠ m + k_z := by
    by_cases hlt : C.output < m + C.gates.length
    · have := hno_alias_kz C.gates.length le_rfl C.output hlt hout_ne
      rw [elimState_end] at this
      intro heq
      apply this
      rw [← hacc, hout_st, heq]
    · exfalso
      have hdef : acc.1.getD C.output (Sum.inl false) = Sum.inl false :=
        List.getD_eq_default _ _ (by rw [hacc, elimPass_fst_len]; simp [hinit, initVar]; omega)
      rw [hout_st] at hdef
      simp at hdef
  have hno_read : ∀ t ≤ C.gates.length, ∀ k' : ℕ, (hk' : k' < (elimState m C.gates init t).2.length) →
      k_z < k' → (m + k_z) ∉ ((elimState m C.gates init t).2[k']'hk').inputs := by
    intro t
    induction t with
    | zero =>
      intro _ k' hk' _
      simp [elimState_zero, hinit] at hk'
    | succ t ih =>
      intro ht k' hk' hlt_k
      have htlt : t < C.gates.length := by omega
      have hstep := elimState_succ m C.gates init t htlt
      set prev := elimState m C.gates init t with hprev
      by_cases hk'old : k' < prev.2.length
      · have hget : (elimState m C.gates init (t + 1)).2[k']'hk' = prev.2[k']'hk'old := by
          have : (elimState m C.gates init (t + 1)).2 = prev.2 ++ (simplifyGate C.gates[t].op (m + prev.2.length)
              (C.gates[t].inputs.map fun i => prev.1.getD i (Sum.inl false))).1.toList := by
            rw [hstep]; rfl
          simp only [this, List.getElem_append_left hk'old]
        rw [hget]
        exact ih (by omega) k' hk'old hlt_k
      · have hopt_some : ∃ g_new, (simplifyGate C.gates[t].op (m + prev.2.length)
            (C.gates[t].inputs.map fun i => prev.1.getD i (Sum.inl false))).1 = some g_new ∧
            (elimState m C.gates init (t + 1)).2[k']'hk' = g_new := by
          cases hopt : (simplifyGate C.gates[t].op (m + prev.2.length)
              (C.gates[t].inputs.map fun i => prev.1.getD i (Sum.inl false))).1 with
          | none =>
            exfalso
            have : (elimState m C.gates init (t + 1)).2.length = prev.2.length := by
              rw [hstep]; simp only [elimStep, hopt, Option.toList_none, List.append_nil]
            omega
          | some g_new =>
            refine ⟨g_new, rfl, ?_⟩
            have heq_l : (elimState m C.gates init (t + 1)).2 = prev.2 ++ [g_new] := by
              rw [hstep]; simp only [elimStep, hopt, Option.toList_some]
            have hk'eq : k' = prev.2.length := by
              have : (elimState m C.gates init (t + 1)).2.length = prev.2.length + 1 := by
                rw [heq_l]; simp
              omega
            simp only [heq_l, hk'eq, List.getElem_append_right le_rfl, Nat.sub_self, List.getElem_cons_zero]
        obtain ⟨g_new, hg_new, hget_new⟩ := hopt_some
        rw [hget_new]
        intro hmem
        have hsum := simplifyGate_mem_inputs_of_some _ _ _ g_new hg_new (m + k_z) hmem
        obtain ⟨idx, hidx_in, hidx_eq⟩ := List.mem_map.1 hsum
        have hidx_lt : idx < m + t := hwf t htlt idx hidx_in
        have ht_gt_z : j_z < t := by
          by_contra hle
          have hmono := elimState_snd_mono m C.gates init t j_z (by omega)
          have hlen_le : prev.2.length ≤ k_z := hmono
          have heq_l : (elimState m C.gates init (t + 1)).2.length = prev.2.length + 1 := by
            rw [hstep]; simp only [elimStep, hg_new, Option.toList_some, List.length_append, List.length_singleton]
          by_cases hteq : t = j_z
          · subst hteq; omega
          · have hmono2 := elimState_snd_mono m C.gates init (t + 1) j_z (by omega)
            omega
        by_cases hidx_eq_z : idx = m + j_z
        · subst hidx_eq_z
          have htu : t = j_u := honly t htlt ht_gt_z hidx_in
          have h1 := simplifyGate_some_snd _ _ _ g_new hg_new
          have h2 := elimState_getD_at m C.gates init t htlt
          have hinit_len : init.1.length = m := by simp [hinit, initVar]
          rw [hinit_len] at h2
          obtain ⟨c, hc⟩ := hc_u
          rw [← htu] at hc
          rw [hc] at h2
          rw [← hprev] at h2
          rw [h1] at h2
          simp at h2
        · exact hno_alias_kz t (by omega) idx hidx_lt hidx_eq_z hidx_eq
  have hdead := deleteDeadGate ⟨acc.2, out⟩ hok_acc k_z hk_z_lt hout_ne_kz
    (fun k' hk' hlt => by
      have := hno_read C.gates.length le_rfl k' (by rw [elimState_end]; exact hk') hlt
      simpa [elimState_end, ← hacc] using this)
  rw [hfun_acc] at hdead
  have hcard_acc' : acc.2.length + (elimDropped m C.gates init).card = C.gates.length := hcard_acc
  have hsz_eq : acc.2.length - 1 = C.gates.length - (elimDropped m C.gates init).card - 1 := by omega
  simpa [hsz_eq] using hdead

private lemma rewrite1_contradiction {m : ℕ} (C : Circuit)
    (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hmax : ∀ C' : Circuit, (∀ g ∈ C'.gates, NOkGate g) → C'.gates.length = C.gates.length →
      circuitFun m C' = circuitFun m C → orAncCount m C' ≤ orAncCount m C)
    (hnc : ∃ x x' : Fin m → Bool, circuitFun m C x ≠ circuitFun m C x')
    (j₀ a z : ℕ) (hj₀ : j₀ < C.gates.length) (ha : a < m + j₀) (hz : z < m + j₀)
    (hg : C.gates[j₀] = ⟨GateOp.or, [a, z]⟩ ∨ C.gates[j₀] = ⟨GateOp.or, [z, a]⟩)
    (hz_imp : ∀ x : Fin m → Bool, (C.wires (List.ofFn x)).getD z false = true → circuitFun m C x = true)
    (ha_not : ∃ x : Fin m → Bool, (C.wires (List.ofFn x)).getD a false = true ∧ circuitFun m C x = false) :
    False := by
  have hout_lt : C.output < m + C.gates.length := min_output_lt C hnc
  have hnot_reach : ¬ OrReach m C.gates C.output (m + j₀) := by
    intro hr
    obtain ⟨x, hax, hfx⟩ := ha_not
    have hstep : OrStep m C.gates (m + j₀) a := by
      refine ⟨j₀, hj₀, rfl, ?_, ?_, ha⟩
      · rcases hg with h | h <;> rw [h]
      · rcases hg with h | h <;> rw [h] <;> simp
    have hr_a : OrReach m C.gates C.output a := Relation.ReflTransGen.tail hr hstep
    have ht := orReach_sound m C (List.ofFn x) (by simp) C.output a hr_a hax
    have : circuitFun m C x = true := ht
    rw [hfx] at this; simp at this
  set C1 := deleteGate m C j₀ a with hC1
  set C2 : Circuit := ⟨C1.gates ++ [⟨GateOp.or, [C1.output, z]⟩], m + C1.gates.length⟩ with hC2
  have hlen1 : C1.gates.length = C.gates.length - 1 := deleteGate_len m C j₀ a hj₀
  have hlen2 : C2.gates.length = C.gates.length := by simp [hC2, hlen1]; omega
  have hnok2 : ∀ g ∈ C2.gates, NOkGate g := by
    intro g hg'
    rcases List.mem_append.1 hg' with h | h
    · exact deleteGate_nok m C j₀ a hnok g h
    · simp at h; subst h; exact ⟨⟨Or.inr (Or.inl rfl), by simp⟩, by simp⟩
  have hfun2 : circuitFun m C2 = circuitFun m C := by
    funext x
    show (wiresFrom (C1.gates ++ [⟨GateOp.or, [C1.output, z]⟩]) (List.ofFn x)).getD (m + C1.gates.length) false =
      circuitFun m C x
    rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil,
      getD_snoc_eq _ _ _ _ (by rw [wiresFrom_length]; simp)]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
    have hz_eq : (wiresFrom C1.gates (List.ofFn x)).getD z false = (C.wires (List.ofFn x)).getD z false := by
      have h1 : (C.wires (List.ofFn x)).getD z false =
          (wiresFrom (C.gates.take j₀) (List.ofFn x)).getD z false := by
        show (wiresFrom C.gates (List.ofFn x)).getD z false = _
        have hsp : C.gates = C.gates.take j₀ ++ C.gates.drop j₀ := (List.take_append_drop j₀ C.gates).symm
        conv_lhs => rw [hsp, wiresFrom_append]
        exact wiresFrom_getD_lt _ _ _ (by rw [wiresFrom_length, List.length_ofFn, List.length_take, Nat.min_eq_left (by omega)]; exact hz)
      have h2 : (wiresFrom C1.gates (List.ofFn x)).getD z false =
          (wiresFrom (C.gates.take j₀) (List.ofFn x)).getD z false := by
        rw [hC1]; show (wiresFrom (C.gates.take j₀ ++ _) (List.ofFn x)).getD z false = _
        rw [wiresFrom_append]
        exact wiresFrom_getD_lt _ _ _ (by rw [wiresFrom_length, List.length_ofFn, List.length_take, Nat.min_eq_left (by omega)]; exact hz)
      rw [h1, h2]
    rw [hz_eq]
    cases hzx : (C.wires (List.ofFn x)).getD z false with
    | true =>
      rw [Bool.or_true, hz_imp x hzx]
    | false =>
      rw [Bool.or_false]
      have hjeq : (C.wires (List.ofFn x)).getD (m + j₀) false = (C.wires (List.ofFn x)).getD a false := by
        rw [wire_eval_gate C j₀ hj₀ x]
        rcases hg with h | h <;>
          simp only [h, ha, hz, ↓reduceIte, hzx, GateOp.eval, List.map_cons, List.map_nil,
            List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.false_or]
      exact deleteGate_wires_eq m C j₀ a hj₀ ha (List.ofFn x) (by simp) hjeq C.output hout_lt
  have hgt : orAncCount m C + 1 ≤ orAncCount m C2 :=
    orAncCount_rewrite1 m C j₀ a z hj₀ ha hout_lt hnot_reach
  have hle := hmax C2 hnok2 hlen2 hfun2
  omega

private lemma rewrite2_contradiction {m : ℕ} (C : Circuit)
    (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hmin : ∀ s' < C.gates.length, ¬ HasCircuitSize m (circuitFun m C) s')
    (hmax : ∀ C' : Circuit, (∀ g ∈ C'.gates, NOkGate g) → C'.gates.length = C.gates.length →
      circuitFun m C' = circuitFun m C → orAncCount m C' ≤ orAncCount m C)
    (hnc : ∃ x x' : Fin m → Bool, circuitFun m C x ≠ circuitFun m C x')
    (z : ℕ) (hz_lt : z < m + C.gates.length)
    (hz_imp : ∀ x : Fin m → Bool, (C.wires (List.ofFn x)).getD z false = false → circuitFun m C x = true)
    (hz_nc : ∃ x₁ x₂ : Fin m → Bool,
      (C.wires (List.ofFn x₁)).getD z false = true ∧
      (C.wires (List.ofFn x₂)).getD z false = true ∧
      circuitFun m C x₁ ≠ circuitFun m C x₂)
    (j₁ j₂ : ℕ) (hj₁ : j₁ < C.gates.length) (hj₂ : j₂ < C.gates.length) (hj12 : j₁ < j₂)
    (hz₁ : z ∈ C.gates[j₁].inputs) (hz₂ : z ∈ C.gates[j₂].inputs) :
    False := by
  have hout_lt : C.output < m + C.gates.length := min_output_lt C hnc
  have hwf := min_gate_wf C hnok hmin hnc
  have hz_lt1 : z < m + j₁ := by
    have hg1 := hnok C.gates[j₁] (List.getElem_mem hj₁)
    rcases hg1.1.1 with hop | hop | hop
    · obtain ⟨a, b, ha, hb, _, hins⟩ := (hwf j₁ hj₁).2 (Or.inl hop)
      rw [hins] at hz₁; simp at hz₁; rcases hz₁ with rfl | rfl <;> omega
    · obtain ⟨a, b, ha, hb, _, hins⟩ := (hwf j₁ hj₁).2 (Or.inr hop)
      rw [hins] at hz₁; simp at hz₁; rcases hz₁ with rfl | rfl <;> omega
    · obtain ⟨a, ha, hins⟩ := (hwf j₁ hj₁).1 hop
      rw [hins] at hz₁; simp at hz₁; subst hz₁; omega
  have hnot_or_not : ∀ j : ℕ, (hj : j < C.gates.length) → z ∈ C.gates[j].inputs →
      C.gates[j].op = GateOp.and := by
    intro j₀ hj₀ hz₀
    by_contra hne_and
    have hgj₀ := hnok C.gates[j₀] (List.getElem_mem hj₀)
    have hop₀ : C.gates[j₀].op = GateOp.or ∨ C.gates[j₀].op = GateOp.not := by
      rcases hgj₀.1.1 with h | h | h
      · exact absurd h hne_and
      · exact Or.inl h
      · exact Or.inr h
    have hex_other : ∃ j_o, ∃ hj_o : j_o < C.gates.length, j_o ≠ j₀ ∧ z ∈ C.gates[j_o].inputs := by
      by_cases h1 : j₁ = j₀
      · exact ⟨j₂, hj₂, by omega, hz₂⟩
      · exact ⟨j₁, hj₁, h1, hz₁⟩
    obtain ⟨j_o, hj_o, hjo_ne, hz_o⟩ := hex_other
    have hsplit_idx : ∃ k : ℕ, k ≤ C.gates.length ∧ z < m + k ∧
        (∀ j, (hj : j < C.gates.length) → z ∈ C.gates[j].inputs → k ≤ j) := by
      by_cases hzm : z < m
      · exact ⟨0, Nat.zero_le _, by omega, fun _ _ _ => Nat.zero_le _⟩
      · refine ⟨z - m + 1, by omega, by omega, ?_⟩
        intro j hj hzj
        have hgj := hnok C.gates[j] (List.getElem_mem hj)
        rcases hgj.1.1 with h | h | h
        · obtain ⟨a, b, ha, hb, _, hins⟩ := (hwf j hj).2 (Or.inl h)
          rw [hins] at hzj; simp at hzj; rcases hzj with rfl | rfl <;> omega
        · obtain ⟨a, b, ha, hb, _, hins⟩ := (hwf j hj).2 (Or.inr h)
          rw [hins] at hzj; simp at hzj; rcases hzj with rfl | rfl <;> omega
        · obtain ⟨a, ha, hins⟩ := (hwf j hj).1 h
          rw [hins] at hzj; simp at hzj; subst hzj; omega
    obtain ⟨k, hk_le, hz_mk, hk_min⟩ := hsplit_idx
    have hk_j₀ : k ≤ j₀ := hk_min j₀ hj₀ hz₀
    have hk_jo : k ≤ j_o := hk_min j_o hj_o hz_o
    set gs₁ := C.gates.take k with hgs₁
    set gs₂ := C.gates.drop k with hgs₂
    have hlen1 : gs₁.length = k := by rw [hgs₁, List.length_take, Nat.min_eq_left hk_le]
    have hlen2 : gs₂.length = C.gates.length - k := by rw [hgs₂, List.length_drop]
    set init_st : List (Bool ⊕ ℕ) :=
      List.ofFn (fun i : Fin (m + k) => if (i : ℕ) = z then Sum.inl true else Sum.inr (i : ℕ)) with hinit_st
    set acc := elimPass m gs₂ (init_st, gs₁) with hacc
    have hinv_z : ∀ x : Fin m → Bool, (C.wires (List.ofFn x)).getD z false = true →
        ElimInv m (List.ofFn x) (wiresFrom C.gates (List.ofFn x)) acc := by
      intro x hzx
      have hsp : C.gates = gs₁ ++ gs₂ := (List.take_append_drop k C.gates).symm
      conv_lhs => skip
      rw [hsp, wiresFrom_append, hacc]
      apply elimInv_pass m (List.ofFn x) gs₂ _ (init_st, gs₁)
        (fun g hg => (hnok g (List.mem_of_mem_drop hg)).1)
      have hlen_w1 : (wiresFrom gs₁ (List.ofFn x)).length = m + k := by
        rw [wiresFrom_length, List.length_ofFn, hlen1]
      refine ⟨by simp, by simp [hinit_st, hlen_w1], ?_⟩
      intro i
      by_cases hi : i < m + k
      · rw [hinit_st, ofFn_getD_lt _ _ _ hi]
        by_cases hiz : i = z
        · subst hiz
          simp only [↓reduceIte, statValid, statVal]
          refine ⟨trivial, ?_⟩
          have hEq : (wiresFrom gs₁ (List.ofFn x)).getD i false = (C.wires (List.ofFn x)).getD i false := by
            show _ = (wiresFrom C.gates (List.ofFn x)).getD i false
            conv_rhs => rw [hsp, wiresFrom_append]
            exact (wiresFrom_getD_lt _ _ _ (by omega)).symm
          rw [hEq, hzx]
        · simp only [hiz, ↓reduceIte, statValid, statVal]
          exact ⟨by rw [hlen1]; exact hi, trivial⟩
      · rw [List.getD_eq_default _ _ (by simp [hinit_st]; omega),
            List.getD_eq_default _ _ (by omega)]
        exact ⟨trivial, rfl⟩
    have hval_z : ∀ x : Fin m → Bool, (C.wires (List.ofFn x)).getD z false = true →
        statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) =
          circuitFun m C x := by
      intro x hzx
      exact ((hinv_z x hzx).2.2 C.output).2
    have hinit_z : init_st.getD z (Sum.inl false) = Sum.inl true := by
      rw [hinit_st, ofFn_getD_lt _ _ _ hz_mk]; simp
    have hget_gs2 : ∀ j (hj : j < C.gates.length) (hkj : k ≤ j),
        gs₂[j - k]'(by omega) = C.gates[j] := by
      intro j hj hkj
      have hidx : k + (j - k) = j := by omega
      simp only [hgs₂, List.getElem_drop, hidx]
    have hdrop_j₀ : j₀ - k ∈ elimDropped m gs₂ (init_st, gs₁) := by
      apply mem_elimDropped_of_const m gs₂ (init_st, gs₁) (j₀ - k) (by omega)
        (by rw [hget_gs2 j₀ hj₀ hk_j₀]; exact hnok _ (List.getElem_mem hj₀)) z
        (by rw [hget_gs2 j₀ hj₀ hk_j₀]; exact hz₀)
      refine ⟨true, ?_⟩
      rw [elimState_getD_mono m gs₂ (init_st, gs₁) 0 (j₀ - k) z _ (Nat.zero_le _) (by omega) (by simp [hinit_st]; omega),
        elimState_zero]
      exact hinit_z
    have hdrop_jo : j_o - k ∈ elimDropped m gs₂ (init_st, gs₁) := by
      apply mem_elimDropped_of_const m gs₂ (init_st, gs₁) (j_o - k) (by omega)
        (by rw [hget_gs2 j_o hj_o hk_jo]; exact hnok _ (List.getElem_mem hj_o)) z
        (by rw [hget_gs2 j_o hj_o hk_jo]; exact hz_o)
      refine ⟨true, ?_⟩
      rw [elimState_getD_mono m gs₂ (init_st, gs₁) 0 (j_o - k) z _ (Nat.zero_le _) (by omega) (by simp [hinit_st]; omega),
        elimState_zero]
      exact hinit_z
    have hc_j₀ : ∃ c : Bool,
        (elimState m gs₂ (init_st, gs₁) (j₀ - k + 1)).1.getD (m + j₀) (Sum.inl false) = Sum.inl c := by
      have hget := elimState_getD_at m gs₂ (init_st, gs₁) (j₀ - k) (by omega)
      have hlen_i : init_st.length = m + k := by simp [hinit_st]
      rw [hlen_i, show m + k + (j₀ - k) = m + j₀ by omega] at hget
      rw [hget]
      have hg_eq : gs₂[j₀ - k]'(by omega) = C.gates[j₀] := hget_gs2 j₀ hj₀ hk_j₀
      have hsz_t : (elimState m gs₂ (init_st, gs₁) (j₀ - k)).1.getD z (Sum.inl false) = Sum.inl true := by
        rw [elimState_getD_mono m gs₂ (init_st, gs₁) 0 (j₀ - k) z _ (Nat.zero_le _) (by omega) (by simp [hinit_st]; omega),
          elimState_zero]
        exact hinit_z
      rcases hop₀ with hop | hop
      · rw [hg_eq, hop]
        have hmem : Sum.inl true ∈ (C.gates[j₀].inputs.map fun i =>
            (elimState m gs₂ (init_st, gs₁) (j₀ - k)).1.getD i (Sum.inl false)) :=
          List.mem_map.2 ⟨z, hz₀, hsz_t⟩
        have hsim := simplifyGate_or_true (m + (elimState m gs₂ (init_st, gs₁) (j₀ - k)).2.length)
          _ (by simp; exact hgj₀.1.2) hmem
        exact ⟨true, by rw [hsim]⟩
      · obtain ⟨a, _, hins⟩ := (hwf j₀ hj₀).1 hop
        rw [hins] at hz₀; simp at hz₀; subst hz₀
        rw [hg_eq, hop, hins, List.map_singleton, hsz_t]
        exact ⟨false, rfl⟩
    have hout_ne_j₀ : C.output ≠ m + j₀ := by
      intro heq
      obtain ⟨c, hc⟩ := hc_j₀
      have hst_out : acc.1.getD C.output (Sum.inl false) = Sum.inl c := by
        rw [heq, hacc, ← elimState_end]
        rw [elimState_getD_mono m gs₂ (init_st, gs₁) (j₀ - k + 1) gs₂.length (m + j₀) _
          (by omega) le_rfl (by simp [hinit_st]; omega)]
        exact hc
      obtain ⟨x₁, x₂, hz1, hz2, hne⟩ := hz_nc
      have h1 := hval_z x₁ hz1; have h2 := hval_z x₂ hz2
      rw [hst_out] at h1 h2
      exact hne (h1.symm.trans h2)
    obtain ⟨j₃, hj₃, hlt3, hmem3⟩ := (min_no_dead C hnok hmin j₀ hj₀).resolve_left hout_ne_j₀
    have hj₃_ne_jo : j₃ ≠ j_o := by
      intro heq
      subst heq
      have hgj₃ := hnok C.gates[j₃] (List.getElem_mem hj₃)
      have hop3 : C.gates[j₃].op = GateOp.and ∨ C.gates[j₃].op = GateOp.or := by
        rcases hgj₃.1.1 with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · obtain ⟨a, _, hins⟩ := (hwf j₃ hj₃).1 h
          rw [hins] at hz_o hmem3; simp at hz_o hmem3
          have : z = m + j₀ := hz_o.trans hmem3.symm
          have : z < m + j₀ := by omega
          omega
      obtain ⟨a, b, ha, hb, hab, hins3⟩ := (hwf j₃ hj₃).2 hop3
      have hpair : (a = z ∧ b = m + j₀) ∨ (a = m + j₀ ∧ b = z) := by
        rw [hins3] at hz_o hmem3; simp at hz_o hmem3
        rcases hz_o with rfl | rfl <;> rcases hmem3 with h1 | h1
        · exact absurd h1.symm (by omega)
        · exact Or.inl ⟨rfl, h1.symm⟩
        · exact Or.inr ⟨h1.symm, rfl⟩
        · exact absurd h1.symm (by omega)
      rcases hop₀ with hop | hop
      · obtain ⟨u, w, hu, hw, _, hins0⟩ := (hwf j₀ hj₀).2 (Or.inr hop)
        have h0_eq : ∀ x : Fin m → Bool,
            (C.wires (List.ofFn x)).getD z false = true →
            (C.wires (List.ofFn x)).getD (m + j₀) false = true := by
          intro x hzx
          rw [wire_eval_gate C j₀ hj₀ x, hop, hins0]
          rw [hins0] at hz₀; simp at hz₀
          rcases hz₀ with hzu | hzw
          · rw [← hzu]; simp only [show z < m + j₀ by omega, hw, ↓reduceIte, hzx, GateOp.eval,
              List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.true_or, Bool.or_false]
          · rw [← hzw]; simp only [hu, show z < m + j₀ by omega, ↓reduceIte, hzx, GateOp.eval,
              List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_true, Bool.true_or, Bool.or_false]
        rcases hop3 with hop3 | hop3
        · apply min_no_alias C hnok hmin j₃ z hj₃ (by omega)
          intro x
          rw [wire_eval_gate C j₃ hj₃ x, hop3, hins3]
          rcases hpair with ⟨haz, hbj⟩ | ⟨haj, hbz⟩
          · rw [haz, hbj]
            cases hzx : (C.wires (List.ofFn x)).getD z false
            · simp only [show z < m + j₃ by omega, show m + j₀ < m + j₃ by omega, ↓reduceIte,
                hzx, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                id_eq, Bool.false_and]
            · simp only [show z < m + j₃ by omega, show m + j₀ < m + j₃ by omega, ↓reduceIte,
                hzx, h0_eq x hzx, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
                List.all_nil, id_eq, Bool.and_true]
          · rw [haj, hbz]
            cases hzx : (C.wires (List.ofFn x)).getD z false
            · simp only [show z < m + j₃ by omega, show m + j₀ < m + j₃ by omega, ↓reduceIte,
                hzx, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                id_eq, Bool.false_and, Bool.and_false]
            · simp only [show z < m + j₃ by omega, show m + j₀ < m + j₃ by omega, ↓reduceIte,
                hzx, h0_eq x hzx, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
                List.all_nil, id_eq, Bool.and_true]
        · apply min_no_alias C hnok hmin j₃ (m + j₀) hj₃ (by omega)
          intro x
          rw [wire_eval_gate C j₃ hj₃ x, hop3, hins3]
          rcases hpair with ⟨haz, hbj⟩ | ⟨haj, hbz⟩
          · rw [haz, hbj]
            cases hzx : (C.wires (List.ofFn x)).getD z false
            · simp only [show z < m + j₃ by omega, show m + j₀ < m + j₃ by omega, ↓reduceIte,
                hzx, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                id_eq, Bool.false_or, Bool.or_false]
            · simp only [show z < m + j₃ by omega, show m + j₀ < m + j₃ by omega, ↓reduceIte,
                hzx, h0_eq x hzx, GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
                List.any_nil, id_eq, Bool.true_or]
          · rw [haj, hbz]
            cases hzx : (C.wires (List.ofFn x)).getD z false
            · simp only [show z < m + j₃ by omega, show m + j₀ < m + j₃ by omega, ↓reduceIte,
                hzx, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                id_eq, Bool.or_false]
            · simp only [show z < m + j₃ by omega, show m + j₀ < m + j₃ by omega, ↓reduceIte,
                hzx, h0_eq x hzx, GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
                List.any_nil, id_eq, Bool.true_or, Bool.or_true]
      · obtain ⟨u, hu, hins0⟩ := (hwf j₀ hj₀).1 hop
        rw [hins0] at hz₀; simp at hz₀
        have h0_eq : ∀ x : Fin m → Bool,
            (C.wires (List.ofFn x)).getD (m + j₀) false = !(C.wires (List.ofFn x)).getD z false := by
          intro x
          rw [wire_eval_gate C j₀ hj₀ x, hop, hins0, ← hz₀]
          simp only [show z < m + j₀ by omega, ↓reduceIte, GateOp.eval, List.map_cons,
            List.map_nil, List.headD_cons]
        rcases hop3 with hop3 | hop3
        · apply min_no_const C hnok hmin hnc j₃ hj₃ false
          intro x
          rw [wire_eval_gate C j₃ hj₃ x, hop3, hins3]
          rcases hpair with ⟨haz, hbj⟩ | ⟨haj, hbz⟩
          · rw [haz, hbj]
            simp only [show z < m + j₃ by omega, show m + j₀ < m + j₃ by omega, ↓reduceIte,
              h0_eq x, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
              id_eq, Bool.and_true, Bool.and_not_self]
          · rw [haj, hbz]
            simp only [show z < m + j₃ by omega, show m + j₀ < m + j₃ by omega, ↓reduceIte,
              h0_eq x, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
              id_eq, Bool.and_true, Bool.not_and_self]
        · apply min_no_const C hnok hmin hnc j₃ hj₃ true
          intro x
          rw [wire_eval_gate C j₃ hj₃ x, hop3, hins3]
          rcases hpair with ⟨haz, hbj⟩ | ⟨haj, hbz⟩
          · rw [haz, hbj]
            simp only [show z < m + j₃ by omega, show m + j₀ < m + j₃ by omega, ↓reduceIte,
              h0_eq x, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
              id_eq, Bool.or_false, Bool.or_not_self]
          · rw [haj, hbz]
            simp only [show z < m + j₃ by omega, show m + j₀ < m + j₃ by omega, ↓reduceIte,
              h0_eq x, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
              id_eq, Bool.or_false, Bool.not_or_self]
    have hdrop_j₃ : j₃ - k ∈ elimDropped m gs₂ (init_st, gs₁) := by
      apply mem_elimDropped_of_const m gs₂ (init_st, gs₁) (j₃ - k) (by omega)
        (by rw [hget_gs2 j₃ hj₃ (by omega)]; exact hnok _ (List.getElem_mem hj₃)) (m + j₀)
        (by rw [hget_gs2 j₃ hj₃ (by omega)]; exact hmem3)
      obtain ⟨c, hc⟩ := hc_j₀
      refine ⟨c, ?_⟩
      rw [elimState_getD_mono m gs₂ (init_st, gs₁) (j₀ - k + 1) (j₃ - k) (m + j₀) _
        (by omega) (by omega) (by simp [hinit_st]; omega)]
      exact hc
    have hcard3 : 3 ≤ (elimDropped m gs₂ (init_st, gs₁)).card := by
      have hsub : ({j₀ - k, j_o - k, j₃ - k} : Finset ℕ) ⊆ elimDropped m gs₂ (init_st, gs₁) := by
        intro x hx; simp at hx
        rcases hx with rfl | rfl | rfl
        · exact hdrop_j₀
        · exact hdrop_jo
        · exact hdrop_j₃
      have hc3 : ({j₀ - k, j_o - k, j₃ - k} : Finset ℕ).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp; omega),
            Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
      exact hc3 ▸ Finset.card_le_card hsub
    have hlen_acc : acc.2.length + 3 ≤ C.gates.length := by
      have htot := elimPass_card_dropped m gs₂ (init_st, gs₁)
      rw [← hacc] at htot
      simp only [Prod.snd] at htot
      omega
    cases hst_out : acc.1.getD C.output (Sum.inl false) with
    | inl c =>
      obtain ⟨x₁, x₂, hz1, hz2, hne⟩ := hz_nc
      have h1 := hval_z x₁ hz1; have h2 := hval_z x₂ hz2
      rw [hst_out] at h1 h2
      exact hne (h1.symm.trans h2)
    | inr out' =>
      set C_small : Circuit :=
        ⟨acc.2 ++ [⟨GateOp.not, [z]⟩, ⟨GateOp.or, [out', m + acc.2.length]⟩], m + (acc.2.length + 1)⟩ with hC_small
      have hok_small : ∀ g ∈ C_small.gates, OkGate g := by
        intro g hg'
        rcases List.mem_append.1 hg' with h | h
        · exact elimPass_ok m gs₂ (init_st, gs₁) (fun g0 hg0 => (hnok g0 (List.mem_of_mem_take hg0)).1) g h
        · simp at h
          rcases h with rfl | rfl <;> simp [OkGate]
      have hfun_small : circuitFun m C_small = circuitFun m C := by
        funext x
        have hpref_acc : ∃ rest, acc.2 = gs₁ ++ rest := by
          have : ∀ (l : List Gate) (a : List (Bool ⊕ ℕ) × List Gate),
              ∃ r, (elimPass m l a).2 = a.2 ++ r := by
            intro l; induction l with
            | nil => intro a; exact ⟨[], by simp [elimPass]⟩
            | cons g rest ih =>
              intro a
              rw [elimPass_cons]
              obtain ⟨r, hr⟩ := ih (elimStep m a g)
              exact ⟨(simplifyGate g.op (m + a.2.length)
                  (g.inputs.map fun i => a.1.getD i (Sum.inl false))).1.toList ++ r,
                by rw [hr]; simp only [elimStep, List.append_assoc]⟩
          exact this gs₂ (init_st, gs₁)
        obtain ⟨rest, hrest⟩ := hpref_acc
        have hz_wire : (wiresFrom acc.2 (List.ofFn x)).getD z false = (C.wires (List.ofFn x)).getD z false := by
          have h1 : (wiresFrom acc.2 (List.ofFn x)).getD z false = (wiresFrom gs₁ (List.ofFn x)).getD z false := by
            rw [hrest, wiresFrom_append]
            exact wiresFrom_getD_lt _ _ _ (by rw [wiresFrom_length, List.length_ofFn, hlen1]; exact hz_mk)
          have h2 : (C.wires (List.ofFn x)).getD z false = (wiresFrom gs₁ (List.ofFn x)).getD z false := by
            show (wiresFrom C.gates (List.ofFn x)).getD z false = _
            have hsp : C.gates = gs₁ ++ gs₂ := (List.take_append_drop k C.gates).symm
            conv_lhs => rw [hsp, wiresFrom_append]
            exact wiresFrom_getD_lt _ _ _ (by rw [wiresFrom_length, List.length_ofFn, hlen1]; exact hz_mk)
          rw [h1, h2]
        show (wiresFrom (acc.2 ++ [⟨GateOp.not, [z]⟩, ⟨GateOp.or, [out', m + acc.2.length]⟩]) (List.ofFn x)).getD
            (m + (acc.2.length + 1)) false = circuitFun m C x
        rw [wiresFrom_append, wiresFrom_cons, wiresFrom_cons, wiresFrom_nil]
        have hlen_w : (wiresFrom acc.2 (List.ofFn x)).length = m + acc.2.length := by
          rw [wiresFrom_length, List.length_ofFn]
        rw [getD_snoc_eq _ _ _ _ (by simp [hlen_w]; omega)]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
          List.headD_cons, id_eq, Bool.or_false]
        rw [getD_snoc_eq _ _ _ _ hlen_w.symm, hz_wire]
        cases hzx : (C.wires (List.ofFn x)).getD z false with
        | false =>
          simp only [Bool.not_false, Bool.or_true]
          exact (hz_imp x hzx).symm
        | true =>
          simp only [Bool.not_true, Bool.or_false]
          have hlt_out : out' < m + acc.2.length := by
            have hv := ((hinv_z x hzx).2.2 C.output).1
            rw [hst_out] at hv; exact hv
          rw [getD_snoc_lt _ _ _ _ (by omega)]
          have hv := hval_z x hzx
          rw [hst_out] at hv
          exact hv
      have hhas : HasCircuitSize m (circuitFun m C) (C.gates.length - 1) := by
        refine ⟨C_small, hok_small, ?_, ?_⟩
        · show C_small.gates.length ≤ C.gates.length - 1
          simp only [hC_small, List.length_append, List.length_cons, List.length_nil]
          omega
        · intro x; exact congrFun hfun_small x
      exact hmin (C.gates.length - 1) (by omega) hhas
  have hop1 : C.gates[j₁].op = GateOp.and := hnot_or_not j₁ hj₁ hz₁
  have hop2 : C.gates[j₂].op = GateOp.and := hnot_or_not j₂ hj₂ hz₂
  obtain ⟨u₁, v₁, hu₁, hv₁, huv₁, hins1⟩ := (hwf j₁ hj₁).2 (Or.inl hop1)
  obtain ⟨u₂, v₂, hu₂, hv₂, huv₂, hins2⟩ := (hwf j₂ hj₂).2 (Or.inl hop2)
  have hex_a1 : ∃ a₁, a₁ < m + j₁ ∧ a₁ ≠ z ∧
      (C.gates[j₁].inputs = [z, a₁] ∨ C.gates[j₁].inputs = [a₁, z]) := by
    rw [hins1] at hz₁; simp at hz₁
    rcases hz₁ with rfl | rfl
    · exact ⟨v₁, hv₁, huv₁.symm, Or.inl hins1⟩
    · exact ⟨u₁, hu₁, huv₁, Or.inr hins1⟩
  have hex_a2 : ∃ a₂, a₂ < m + j₂ ∧ a₂ ≠ z ∧ a₂ ≠ m + j₁ ∧
      (C.gates[j₂].inputs = [z, a₂] ∨ C.gates[j₂].inputs = [a₂, z]) := by
    have hnot_j1 : m + j₁ ∉ C.gates[j₂].inputs := by
      intro hmem
      have hpair : (u₂ = z ∧ v₂ = m + j₁) ∨ (u₂ = m + j₁ ∧ v₂ = z) := by
        rw [hins2] at hz₂ hmem; simp at hz₂ hmem
        rcases hz₂ with rfl | rfl <;> rcases hmem with h1 | h1
        · exact absurd h1.symm (by omega)
        · exact Or.inl ⟨rfl, h1.symm⟩
        · exact Or.inr ⟨h1.symm, rfl⟩
        · exact absurd h1.symm (by omega)
      apply min_no_alias C hnok hmin j₂ (m + j₁) hj₂ (by omega)
      intro x
      rw [wire_eval_gate C j₂ hj₂ x, hop2, hins2]
      have h1_imp : (C.wires (List.ofFn x)).getD z false = false →
          (C.wires (List.ofFn x)).getD (m + j₁) false = false := by
        intro hzx
        rw [wire_eval_gate C j₁ hj₁ x, hop1]
        obtain ⟨a₁, ha₁, _, h1s⟩ := hex_a1
        rcases h1s with h | h <;>
          simp only [h, hz_lt1, ha₁, ↓reduceIte, hzx, GateOp.eval, List.map_cons, List.map_nil,
            List.all_cons, List.all_nil, id_eq, Bool.false_and, Bool.and_false]
      rcases hpair with ⟨huz, hvj⟩ | ⟨huj, hvz⟩
      · rw [huz, hvj]
        cases hzx : (C.wires (List.ofFn x)).getD z false
        · simp only [show z < m + j₂ by omega, show m + j₁ < m + j₂ by omega, ↓reduceIte,
            hzx, h1_imp hzx, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
            List.all_nil, id_eq, Bool.false_and]
        · simp only [show z < m + j₂ by omega, show m + j₁ < m + j₂ by omega, ↓reduceIte,
            hzx, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
            id_eq, Bool.true_and, Bool.and_true]
      · rw [huj, hvz]
        cases hzx : (C.wires (List.ofFn x)).getD z false
        · simp only [show z < m + j₂ by omega, show m + j₁ < m + j₂ by omega, ↓reduceIte,
            hzx, h1_imp hzx, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
            List.all_nil, id_eq, Bool.false_and]
        · simp only [show z < m + j₂ by omega, show m + j₁ < m + j₂ by omega, ↓reduceIte,
            hzx, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
            id_eq, Bool.true_and, Bool.and_true]
    rw [hins2] at hz₂; simp at hz₂
    rcases hz₂ with rfl | rfl
    · exact ⟨v₂, hv₂, huv₂.symm, fun h => hnot_j1 (by rw [hins2, h]; simp), Or.inl hins2⟩
    · exact ⟨u₂, hu₂, huv₂, fun h => hnot_j1 (by rw [hins2, h]; simp), Or.inr hins2⟩
  obtain ⟨a₁, ha₁, ha₁z, h1s⟩ := hex_a1
  obtain ⟨a₂, ha₂, ha₂z, ha₂j₁, h2s⟩ := hex_a2
  set C1 := deleteGate m C j₁ a₁ with hC1
  set a₂' := substWire (m + j₁) a₁ a₂ with ha₂'
  have ha₂'_lt : a₂' < m + (j₂ - 1) := by
    dsimp [a₂', substWire]; split_ifs <;> omega
  set C2 := deleteGate m C1 (j₂ - 1) a₂' with hC2
  set C3 : Circuit := ⟨C2.gates ++ [⟨GateOp.not, [z]⟩, ⟨GateOp.or, [C2.output, m + C2.gates.length]⟩],
    m + (C2.gates.length + 1)⟩ with hC3
  have hlen1 : C1.gates.length = C.gates.length - 1 := deleteGate_len m C j₁ a₁ hj₁
  have hj₂' : j₂ - 1 < C1.gates.length := by omega
  have hlen2 : C2.gates.length = C.gates.length - 2 := by
    rw [hC2, deleteGate_len m C1 (j₂ - 1) a₂' hj₂', hlen1]; omega
  have hlen3 : C3.gates.length = C.gates.length := by simp [hC3, hlen2]; omega
  have hnok3 : ∀ g ∈ C3.gates, NOkGate g := by
    intro g hg'
    rcases List.mem_append.1 hg' with h | h
    · exact deleteGate_nok m C1 (j₂ - 1) a₂' (deleteGate_nok m C j₁ a₁ hnok) g h
    · simp at h
      rcases h with rfl | rfl
      · exact ⟨⟨Or.inr (Or.inr rfl), by simp⟩, by simp⟩
      · exact ⟨⟨Or.inr (Or.inl rfl), by simp⟩, by simp⟩
  have hfun3 : circuitFun m C3 = circuitFun m C := by
    funext x
    have hz_c1 : (C1.wires (List.ofFn x)).getD z false = (C.wires (List.ofFn x)).getD z false := by
      have h1 : (C.wires (List.ofFn x)).getD z false = (wiresFrom (C.gates.take j₁) (List.ofFn x)).getD z false := by
        show (wiresFrom C.gates (List.ofFn x)).getD z false = _
        have hsp : C.gates = C.gates.take j₁ ++ C.gates.drop j₁ := (List.take_append_drop j₁ C.gates).symm
        conv_lhs => rw [hsp, wiresFrom_append]
        exact wiresFrom_getD_lt _ _ _ (by rw [wiresFrom_length, List.length_ofFn, List.length_take, Nat.min_eq_left (by omega)]; exact hz_lt1)
      have h2 : (C1.wires (List.ofFn x)).getD z false = (wiresFrom (C.gates.take j₁) (List.ofFn x)).getD z false := by
        show (wiresFrom (C.gates.take j₁ ++ _) (List.ofFn x)).getD z false = _
        rw [wiresFrom_append]
        exact wiresFrom_getD_lt _ _ _ (by rw [wiresFrom_length, List.length_ofFn, List.length_take, Nat.min_eq_left (by omega)]; exact hz_lt1)
      rw [h1, h2]
    have hz_c2 : (C2.wires (List.ofFn x)).getD z false = (C.wires (List.ofFn x)).getD z false := by
      have h1 : (C1.wires (List.ofFn x)).getD z false = (wiresFrom (C1.gates.take (j₂ - 1)) (List.ofFn x)).getD z false := by
        show (wiresFrom C1.gates (List.ofFn x)).getD z false = _
        have hsp : C1.gates = C1.gates.take (j₂ - 1) ++ C1.gates.drop (j₂ - 1) := (List.take_append_drop (j₂ - 1) C1.gates).symm
        conv_lhs => rw [hsp, wiresFrom_append]
        exact wiresFrom_getD_lt _ _ _ (by rw [wiresFrom_length, List.length_ofFn, List.length_take, Nat.min_eq_left (by omega)]; omega)
      have h2 : (C2.wires (List.ofFn x)).getD z false = (wiresFrom (C1.gates.take (j₂ - 1)) (List.ofFn x)).getD z false := by
        show (wiresFrom (C1.gates.take (j₂ - 1) ++ _) (List.ofFn x)).getD z false = _
        rw [wiresFrom_append]
        exact wiresFrom_getD_lt _ _ _ (by rw [wiresFrom_length, List.length_ofFn, List.length_take, Nat.min_eq_left (by omega)]; omega)
      rw [← hz_c1, h1, h2]
    show (wiresFrom (C2.gates ++ [⟨GateOp.not, [z]⟩, ⟨GateOp.or, [C2.output, m + C2.gates.length]⟩]) (List.ofFn x)).getD
        (m + (C2.gates.length + 1)) false = circuitFun m C x
    rw [wiresFrom_append, wiresFrom_cons, wiresFrom_cons, wiresFrom_nil]
    have hlen_w : (wiresFrom C2.gates (List.ofFn x)).length = m + C2.gates.length := by
      rw [wiresFrom_length, List.length_ofFn]
    rw [getD_snoc_eq _ _ _ _ (by simp [hlen_w]; omega)]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      List.headD_cons, id_eq, Bool.or_false]
    rw [getD_snoc_eq _ _ _ _ hlen_w.symm]
    have hz_w2 : (wiresFrom C2.gates (List.ofFn x)).getD z false = (C.wires (List.ofFn x)).getD z false := hz_c2
    rw [hz_w2]
    cases hzx : (C.wires (List.ofFn x)).getD z false with
    | false =>
      simp only [Bool.not_false, Bool.or_true]
      exact (hz_imp x hzx).symm
    | true =>
      simp only [Bool.not_true, Bool.or_false]
      have hj1_eq : (C.wires (List.ofFn x)).getD (m + j₁) false = (C.wires (List.ofFn x)).getD a₁ false := by
        rw [wire_eval_gate C j₁ hj₁ x, hop1]
        rcases h1s with h | h <;>
          simp only [h, hz_lt1, ha₁, ↓reduceIte, hzx, GateOp.eval, List.map_cons, List.map_nil,
            List.all_cons, List.all_nil, id_eq, Bool.true_and, Bool.and_true]
      have hC1_all := deleteGate_wires_eq m C j₁ a₁ hj₁ ha₁ (List.ofFn x) (by simp) hj1_eq
      have hj2_eq_c : (C.wires (List.ofFn x)).getD (m + j₂) false = (C.wires (List.ofFn x)).getD a₂ false := by
        rw [wire_eval_gate C j₂ hj₂ x, hop2]
        rcases h2s with h | h <;>
          simp only [h, show z < m + j₂ by omega, ha₂, ↓reduceIte, hzx, GateOp.eval,
            List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.true_and, Bool.and_true]
      have hj2_eq_c1 : (C1.wires (List.ofFn x)).getD (m + (j₂ - 1)) false =
          (C1.wires (List.ofFn x)).getD a₂' false := by
        have hL := hC1_all (m + j₂) (by omega)
        have hsubL : substWire (m + j₁) a₁ (m + j₂) = m + (j₂ - 1) := by
          unfold substWire; split_ifs <;> omega
        rw [hsubL] at hL
        have hR := hC1_all a₂ (by omega)
        rw [hL, hj2_eq_c, ← hR]
      have hC2_all := deleteGate_wires_eq m C1 (j₂ - 1) a₂' hj₂' ha₂'_lt (List.ofFn x) (by simp) hj2_eq_c1
      have hC1_out_lt : C1.output < m + C1.gates.length := by
        show substWire (m + j₁) a₁ C.output < m + C1.gates.length
        unfold substWire; split_ifs <;> omega
      have hC2_out_lt : C2.output < m + C2.gates.length := by
        show substWire (m + (j₂ - 1)) a₂' C1.output < m + C2.gates.length
        unfold substWire; split_ifs <;> omega
      rw [getD_snoc_lt _ _ _ _ (by omega)]
      have hstep2 := hC2_all C1.output hC1_out_lt
      have hstep1 := hC1_all C.output hout_lt
      exact hstep2.trans hstep1
  have hgt : orAncCount m C + 1 ≤ orAncCount m C3 :=
    orAncCount_rewrite2 m C j₁ j₂ a₁ a₂' z hj₁ hj₂ hj12 ha₁ ha₂'_lt
      (by rw [hop1]; simp) (by rw [hop2]; simp) hout_lt
  have hle := hmax C3 hnok3 hlen3 hfun3
  omega

private lemma acyclic_leaf_cases {n : ℕ} (G : SimpleGraph (Fin n)) (hAcyc : G.IsAcyclic)
    (hEdge : ∃ u v : Fin n, G.Adj u v) :
    ∃ ℓ p : Fin n, G.Adj ℓ p ∧ (∀ w, G.Adj ℓ w → w = p) ∧
      ((∃ ℓ' : Fin n, ℓ' ≠ ℓ ∧ G.Adj ℓ' p ∧ ∀ w, G.Adj ℓ' w → w = p) ∨
       (∀ w, G.Adj p w → w = ℓ) ∨
       (∃ q : Fin n, q ≠ ℓ ∧ G.Adj p q ∧ ∀ w, G.Adj p w → w = ℓ ∨ w = q)) := by
  classical
  have hlen_lt : ∀ {u v : Fin n} (P : G.Walk u v), P.IsPath → P.length < n := by
    intro u v P hP
    have h1 : P.support.length ≤ Fintype.card (Fin n) := hP.support_nodup.length_le_card
    rw [P.length_support, Fintype.card_fin] at h1
    omega
  set S : Finset ℕ := (Finset.range n).filter
    (fun k => ∃ u v : Fin n, ∃ P : G.Walk u v, P.IsPath ∧ P.length = k) with hS
  have hS_ne : S.Nonempty := by
    obtain ⟨u₀, v₀, hadj⟩ := hEdge
    refine ⟨1, Finset.mem_filter.2 ⟨Finset.mem_range.2 ?_, u₀, v₀,
      SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil, ?_, rfl⟩⟩
    · have hp : (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil).IsPath :=
        SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil (by simp [hadj.ne])
      exact hlen_lt _ hp
    · exact SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil (by simp [hadj.ne])
  set m := S.max' hS_ne with hm
  have hm_mem : m ∈ S := Finset.max'_mem S hS_ne
  have hm_ge : 1 ≤ m := by
    obtain ⟨u₀, v₀, hadj⟩ := hEdge
    have hp : (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil).IsPath :=
      SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil (by simp [hadj.ne])
    have h1 : 1 ∈ S := Finset.mem_filter.2
      ⟨Finset.mem_range.2 (hlen_lt _ hp), u₀, v₀, _, hp, rfl⟩
    exact Finset.le_max' S 1 h1
  have hm_max : ∀ {u v : Fin n} (P : G.Walk u v), P.IsPath → P.length ≤ m := by
    intro u v P hP
    have hmem : P.length ∈ S := Finset.mem_filter.2
      ⟨Finset.mem_range.2 (hlen_lt P hP), u, v, P, hP, rfl⟩
    exact Finset.le_max' S P.length hmem
  obtain ⟨_, ℓ, z, P, hP, hPlen⟩ := Finset.mem_filter.1 hm_mem
  cases P with
  | nil => simp at hPlen; omega
  | @cons _ p _ hlp Q =>
    have hQ : Q.IsPath := hP.of_cons
    have hℓ_not_Q : ℓ ∉ Q.support := by
      have hnd := hP.support_nodup
      simp only [SimpleGraph.Walk.support_cons, List.nodup_cons] at hnd
      exact hnd.1
    have hℓ_leaf : ∀ w, G.Adj ℓ w → w = p := by
      intro w hlw
      by_cases hw : w ∈ (SimpleGraph.Walk.cons hlp Q).support
      · simpa using hAcyc.eq_snd_of_adj_start hP hlw hw
      · exfalso
        have hP' : (SimpleGraph.Walk.cons hlw.symm (SimpleGraph.Walk.cons hlp Q)).IsPath :=
          SimpleGraph.Walk.IsPath.cons hP hw
        have hle := hm_max _ hP'
        simp only [SimpleGraph.Walk.length_cons] at hPlen hle
        omega
    have hnotQ_leaf : ∀ w, G.Adj p w → w ∉ Q.support → ∀ u, G.Adj w u → u = p := by
      intro w hpw hwQ u hwu
      by_contra hup
      by_cases huQ : u ∈ Q.support
      · set Q' := Q.takeUntil u huQ
        have hQ' : Q'.IsPath := hQ.takeUntil huQ
        have hR : (SimpleGraph.Walk.cons hpw (SimpleGraph.Walk.cons hwu SimpleGraph.Walk.nil)).IsPath := by
          refine SimpleGraph.Walk.IsPath.cons
            (SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil (by simp [hwu.ne])) ?_
          simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
            List.not_mem_nil, or_false, not_or]
          exact ⟨hpw.ne, Ne.symm hup⟩
        have heq := (hAcyc.subsingleton_path p u).elim ⟨Q', hQ'⟩ ⟨_, hR⟩
        have hw_in_R : w ∈ (SimpleGraph.Walk.cons hpw (SimpleGraph.Walk.cons hwu SimpleGraph.Walk.nil)).support := by
          simp
        have hw_in_Q' : w ∈ Q'.support := by
          rw [Subtype.mk.inj heq]; exact hw_in_R
        exact hwQ (SimpleGraph.Walk.support_takeUntil_subset_support Q huQ hw_in_Q')
      · have hP1 : (SimpleGraph.Walk.cons hpw.symm Q).IsPath :=
          SimpleGraph.Walk.IsPath.cons hQ hwQ
        have hu_not : u ∉ (SimpleGraph.Walk.cons hpw.symm Q).support := by
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons, not_or]
          exact ⟨hwu.ne.symm, huQ⟩
        have hP2 : (SimpleGraph.Walk.cons hwu.symm (SimpleGraph.Walk.cons hpw.symm Q)).IsPath :=
          SimpleGraph.Walk.IsPath.cons hP1 hu_not
        have hle := hm_max _ hP2
        simp only [SimpleGraph.Walk.length_cons] at hPlen hle
        omega
    refine ⟨ℓ, p, hlp, hℓ_leaf, ?_⟩
    cases Q with
    | nil =>
      by_cases hother : ∃ ℓ' : Fin n, ℓ' ≠ ℓ ∧ G.Adj z ℓ'
      · obtain ⟨ℓ', hne, hadj⟩ := hother
        have hnot : ℓ' ∉ (SimpleGraph.Walk.nil : G.Walk z z).support := by
          simp [hadj.ne.symm]
        exact Or.inl ⟨ℓ', hne, hadj.symm, hnotQ_leaf ℓ' hadj hnot⟩
      · refine Or.inr (Or.inl ?_)
        intro w hpw
        by_contra hwne
        exact hother ⟨w, hwne, hpw⟩
    | @cons _ q _ hpq Q' =>
      have hq_ne_ℓ : q ≠ ℓ := by
        intro hq
        apply hℓ_not_Q
        rw [← hq]
        simp
      by_cases hother : ∃ ℓ' : Fin n, ℓ' ≠ ℓ ∧ ℓ' ≠ q ∧ G.Adj p ℓ'
      · obtain ⟨ℓ', hne1, hne2, hadj⟩ := hother
        have hnot : ℓ' ∉ (SimpleGraph.Walk.cons hpq Q').support := by
          intro hmem
          exact hne2 (by simpa using hAcyc.eq_snd_of_adj_start hQ hadj hmem)
        exact Or.inl ⟨ℓ', hne1, hadj.symm, hnotQ_leaf ℓ' hadj hnot⟩
      · refine Or.inr (Or.inr ⟨q, hq_ne_ℓ, hpq, ?_⟩)
        intro w hpw
        by_contra hnot
        exact hother ⟨w, fun h => hnot (Or.inl h), fun h => hnot (Or.inr h), hpw⟩

private def IsVC {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  ∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S

private def HasMinVC {n : ℕ} (G : SimpleGraph (Fin n)) (t : ℕ) : Prop :=
  (∃ S : Finset (Fin n), IsVC G S ∧ S.card = t) ∧
  (∀ S : Finset (Fin n), IsVC G S → t ≤ S.card)

private lemma hasMinVC_exists {n : ℕ} (G : SimpleGraph (Fin n)) : ∃ t : ℕ, HasMinVC G t := by
  classical
  have hex : ∃ k : ℕ, ∃ S : Finset (Fin n), IsVC G S ∧ S.card = k :=
    ⟨(Finset.univ : Finset (Fin n)).card, Finset.univ, fun u _ _ => Or.inl (Finset.mem_univ u), rfl⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  intro S hS
  exact Nat.find_min' hex ⟨S, hS, rfl⟩

private lemma hasMinVC_empty {n t : ℕ} (G : SimpleGraph (Fin n))
    (hempty : ∀ u v : Fin n, ¬ G.Adj u v) (hvc : HasMinVC G t) : t = 0 := by
  have hle : t ≤ (∅ : Finset (Fin n)).card := hvc.2 ∅ (fun u v h => absurd h (hempty u v))
  simpa using hle

private def deleteVertexEdges {n : ℕ} (G : SimpleGraph (Fin n)) (p : Fin n) :
    SimpleGraph (Fin n) where
  Adj u v := G.Adj u v ∧ u ≠ p ∧ v ≠ p
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun v h => G.loopless.irrefl v h.1⟩

private lemma deleteVertexEdges_le {n : ℕ} (G : SimpleGraph (Fin n)) (p : Fin n) :
    deleteVertexEdges G p ≤ G :=
  fun _ _ h => h.1

private lemma hasMinVC_deleteEdge {n t t₁ : ℕ} (G : SimpleGraph (Fin n)) (ℓ p : Fin n)
    (hvc : HasMinVC G t) (hvc₁ : HasMinVC (G.deleteEdges {s(ℓ, p)}) t₁) :
    t₁ ≤ t ∧ t ≤ t₁ + 1 := by
  obtain ⟨⟨S, hS, hSc⟩, hmin⟩ := hvc
  obtain ⟨⟨S₁, hS₁, hS₁c⟩, hmin₁⟩ := hvc₁
  constructor
  · have hS_sub : IsVC (G.deleteEdges {s(ℓ, p)}) S := fun u v h => hS u v h.1
    rw [← hSc]; exact hmin₁ S hS_sub
  · have hcov : IsVC G (insert p S₁) := by
      intro u v huv
      by_cases hmem : s(u, v) = s(ℓ, p)
      · rw [Sym2.eq_iff] at hmem
        rcases hmem with ⟨_, hvp⟩ | ⟨hup, _⟩
        · exact Or.inr (hvp ▸ Finset.mem_insert_self p S₁)
        · exact Or.inl (hup ▸ Finset.mem_insert_self p S₁)
      · have hadj : (G.deleteEdges {s(ℓ, p)}).Adj u v :=
          SimpleGraph.deleteEdges_adj.2 ⟨huv, by simpa using hmem⟩
        rcases hS₁ u v hadj with hu | hv
        · exact Or.inl (Finset.mem_insert_of_mem hu)
        · exact Or.inr (Finset.mem_insert_of_mem hv)
    have hle := hmin (insert p S₁) hcov
    have hcard : (insert p S₁).card ≤ S₁.card + 1 := Finset.card_insert_le p S₁
    omega

private lemma hasMinVC_deleteLeafEdge_eq {n t t₁ : ℕ} (G : SimpleGraph (Fin n)) (ℓ ℓ' p : Fin n)
    (hℓ'ne : ℓ' ≠ ℓ) (hℓ'p : G.Adj ℓ' p) (hℓ'leaf : ∀ w, G.Adj ℓ' w → w = p)
    (hvc : HasMinVC G t) (hvc₁ : HasMinVC (G.deleteEdges {s(ℓ, p)}) t₁) :
    t₁ = t := by
  have hle : t₁ ≤ t := (hasMinVC_deleteEdge G ℓ p hvc hvc₁).1
  obtain ⟨⟨S₁, hS₁, hS₁c⟩, _⟩ := hvc₁
  have hge : t ≤ t₁ := by
    by_cases hp : p ∈ S₁
    · have hcov : IsVC G S₁ := by
        intro u v huv
        by_cases hmem : s(u, v) = s(ℓ, p)
        · rw [Sym2.eq_iff] at hmem
          rcases hmem with ⟨_, hvp⟩ | ⟨hup, _⟩
          · exact Or.inr (hvp ▸ hp)
          · exact Or.inl (hup ▸ hp)
        · exact hS₁ u v (SimpleGraph.deleteEdges_adj.2 ⟨huv, by simpa using hmem⟩)
      rw [← hS₁c]; exact hvc.2 S₁ hcov
    · have hℓ'in : ℓ' ∈ S₁ := by
        have hne_edge : s(ℓ', p) ≠ s(ℓ, p) := by
          intro heq
          rw [Sym2.eq_iff] at heq
          rcases heq with ⟨h1, _⟩ | ⟨h1, _⟩
          · exact hℓ'ne h1
          · exact hℓ'p.ne h1
        have hadj : (G.deleteEdges {s(ℓ, p)}).Adj ℓ' p :=
          SimpleGraph.deleteEdges_adj.2 ⟨hℓ'p, by simpa using hne_edge⟩
        rcases hS₁ ℓ' p hadj with h | h
        · exact h
        · exact absurd h hp
      set S' := insert p (S₁.erase ℓ')
      have hcov : IsVC G S' := by
        intro u v huv
        by_cases hmem : s(u, v) = s(ℓ, p)
        · rw [Sym2.eq_iff] at hmem
          rcases hmem with ⟨_, hvp⟩ | ⟨hup, _⟩
          · exact Or.inr (hvp ▸ Finset.mem_insert_self p _)
          · exact Or.inl (hup ▸ Finset.mem_insert_self p _)
        · rcases hS₁ u v (SimpleGraph.deleteEdges_adj.2 ⟨huv, by simpa using hmem⟩) with hu | hv
          · by_cases huℓ : u = ℓ'
            · subst huℓ
              have hv_eq : v = p := hℓ'leaf v huv
              exact Or.inr (hv_eq ▸ Finset.mem_insert_self p _)
            · exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨huℓ, hu⟩))
          · by_cases hvℓ : v = ℓ'
            · subst hvℓ
              have hu_eq : u = p := hℓ'leaf u huv.symm
              exact Or.inl (hu_eq ▸ Finset.mem_insert_self p _)
            · exact Or.inr (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hvℓ, hv⟩))
      have hcard : S'.card = S₁.card := by
        have hp_not : p ∉ S₁.erase ℓ' := fun h => hp (Finset.mem_of_mem_erase h)
        rw [Finset.card_insert_of_notMem hp_not, Finset.card_erase_of_mem hℓ'in]
        have hpos : 1 ≤ S₁.card := Finset.one_le_card.2 ⟨ℓ', hℓ'in⟩
        omega
      have := hvc.2 S' hcov
      omega
  omega

private lemma hasMinVC_deleteVertex {n t t' : ℕ} (G : SimpleGraph (Fin n)) (ℓ p : Fin n)
    (hlp : G.Adj ℓ p) (hleaf : ∀ w, G.Adj ℓ w → w = p)
    (hvc : HasMinVC G t) (hvc' : HasMinVC (deleteVertexEdges G p) t') :
    t' + 1 = t := by
  obtain ⟨⟨S, hS, hSc⟩, hmin⟩ := hvc
  obtain ⟨⟨S', hS', hS'c⟩, hmin'⟩ := hvc'
  have hle : t ≤ t' + 1 := by
    have hcov : IsVC G (insert p S') := by
      intro u v huv
      by_cases hup : u = p
      · exact Or.inl (hup ▸ Finset.mem_insert_self p S')
      · by_cases hvp : v = p
        · exact Or.inr (hvp ▸ Finset.mem_insert_self p S')
        · rcases hS' u v ⟨huv, hup, hvp⟩ with hu | hv
          · exact Or.inl (Finset.mem_insert_of_mem hu)
          · exact Or.inr (Finset.mem_insert_of_mem hv)
    have := hmin (insert p S') hcov
    have := Finset.card_insert_le p S'
    omega
  have hge : t' + 1 ≤ t := by
    by_cases hp : p ∈ S
    · have hcov : IsVC (deleteVertexEdges G p) (S.erase p) := by
        intro u v huv
        rcases hS u v huv.1 with hu | hv
        · exact Or.inl (Finset.mem_erase.2 ⟨huv.2.1, hu⟩)
        · exact Or.inr (Finset.mem_erase.2 ⟨huv.2.2, hv⟩)
      have h1 := hmin' (S.erase p) hcov
      have h2 := Finset.card_erase_of_mem hp
      have hpos : 1 ≤ S.card := Finset.one_le_card.2 ⟨p, hp⟩
      omega
    · have hℓ : ℓ ∈ S := by
        rcases hS ℓ p hlp with h | h
        · exact h
        · exact absurd h hp
      have hcov : IsVC (deleteVertexEdges G p) (S.erase ℓ) := by
        intro u v huv
        rcases hS u v huv.1 with hu | hv
        · have huℓ : u ≠ ℓ := by
            intro h; subst h; exact huv.2.2 (hleaf v huv.1)
          exact Or.inl (Finset.mem_erase.2 ⟨huℓ, hu⟩)
        · have hvℓ : v ≠ ℓ := by
            intro h; subst h; exact huv.2.1 (hleaf u huv.1.symm)
          exact Or.inr (Finset.mem_erase.2 ⟨hvℓ, hv⟩)
      have h1 := hmin' (S.erase ℓ) hcov
      have h2 := Finset.card_erase_of_mem hℓ
      have hpos : 1 ≤ S.card := Finset.one_le_card.2 ⟨ℓ, hℓ⟩
      omega
  omega

private lemma hasMinVC_deleteVertex_le {n t t' : ℕ} (G : SimpleGraph (Fin n)) (p : Fin n)
    (hvc : HasMinVC G t) (hvc' : HasMinVC (deleteVertexEdges G p) t') :
    t ≤ t' + 1 := by
  obtain ⟨⟨S', hS', hS'c⟩, _⟩ := hvc'
  have hcov : IsVC G (insert p S') := by
    intro u v huv
    by_cases hup : u = p
    · exact Or.inl (hup ▸ Finset.mem_insert_self p S')
    · by_cases hvp : v = p
      · exact Or.inr (hvp ▸ Finset.mem_insert_self p S')
      · rcases hS' u v ⟨huv, hup, hvp⟩ with hu | hv
        · exact Or.inl (Finset.mem_insert_of_mem hu)
        · exact Or.inr (Finset.mem_insert_of_mem hv)
  have h1 := hvc.2 (insert p S') hcov
  have h2 := Finset.card_insert_le p S'
  omega

private lemma hasMinVC_deletePair_le {n t t' : ℕ} (G : SimpleGraph (Fin n)) (u w : Fin n)
    (hvc : HasMinVC G t) (hvc' : HasMinVC (deleteVertexEdges (deleteVertexEdges G u) w) t') :
    t ≤ t' + 2 := by
  obtain ⟨t₁, hvc₁⟩ := hasMinVC_exists (deleteVertexEdges G u)
  have h1 := hasMinVC_deleteVertex_le G u hvc hvc₁
  have h2 := hasMinVC_deleteVertex_le (deleteVertexEdges G u) w hvc₁ hvc'
  omega

private lemma edgeFinset_card_deleteEdge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ℓ p : Fin n) (hlp : G.Adj ℓ p) [DecidableRel (G.deleteEdges {s(ℓ, p)}).Adj] :
    (G.deleteEdges {s(ℓ, p)}).edgeFinset.card + 1 = G.edgeFinset.card := by
  have heq : (G.deleteEdges {s(ℓ, p)}).edgeFinset = G.edgeFinset.erase s(ℓ, p) := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset, Finset.mem_erase, SimpleGraph.edgeSet_deleteEdges,
      Set.mem_sdiff, Set.mem_singleton_iff]
    tauto
  rw [heq]
  have hmem : s(ℓ, p) ∈ G.edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset]; exact hlp
  have hpos : 1 ≤ G.edgeFinset.card := Finset.one_le_card.2 ⟨s(ℓ, p), hmem⟩
  rw [Finset.card_erase_of_mem hmem]
  omega

private lemma edgeFinset_card_deleteVertex_deg1 {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (ℓ p : Fin n) (hlp : G.Adj ℓ p)
    (hpdeg : ∀ w, G.Adj p w → w = ℓ) [DecidableRel (deleteVertexEdges G p).Adj] :
    (deleteVertexEdges G p).edgeFinset.card + 1 = G.edgeFinset.card := by
  have heq : (deleteVertexEdges G p).edgeFinset = G.edgeFinset.erase s(ℓ, p) := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      rw [SimpleGraph.mem_edgeFinset, Finset.mem_erase, SimpleGraph.mem_edgeFinset,
          SimpleGraph.mem_edgeSet, SimpleGraph.mem_edgeSet]
      dsimp only [deleteVertexEdges]
      constructor
      · rintro ⟨huv, hup, hvp⟩
        refine ⟨?_, huv⟩
        intro he
        rw [Sym2.eq_iff] at he
        rcases he with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact hvp h2
        · exact hup h1
      · rintro ⟨hne, huv⟩
        refine ⟨huv, ?_, ?_⟩
        · intro hup; subst hup
          exact hne (by rw [Sym2.eq_iff]; exact Or.inr ⟨rfl, hpdeg v huv⟩)
        · intro hvp; subst hvp
          exact hne (by rw [Sym2.eq_iff]; exact Or.inl ⟨hpdeg u huv.symm, rfl⟩)
  rw [heq]
  have hmem : s(ℓ, p) ∈ G.edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset]; exact hlp
  have hpos : 1 ≤ G.edgeFinset.card := Finset.one_le_card.2 ⟨s(ℓ, p), hmem⟩
  rw [Finset.card_erase_of_mem hmem]
  omega

private lemma edgeFinset_card_deleteVertex_deg2 {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (ℓ p q : Fin n) (hlp : G.Adj ℓ p) (hpq : G.Adj p q)
    (hqne : q ≠ ℓ) (hpdeg : ∀ w, G.Adj p w → w = ℓ ∨ w = q)
    [DecidableRel (deleteVertexEdges G p).Adj] :
    (deleteVertexEdges G p).edgeFinset.card + 2 = G.edgeFinset.card := by
  have heq : (deleteVertexEdges G p).edgeFinset =
      (G.edgeFinset.erase s(ℓ, p)).erase s(p, q) := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      rw [SimpleGraph.mem_edgeFinset, Finset.mem_erase, Finset.mem_erase,
          SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.mem_edgeSet]
      dsimp only [deleteVertexEdges]
      constructor
      · rintro ⟨huv, hup, hvp⟩
        refine ⟨?_, ?_, huv⟩
        · intro he; rw [Sym2.eq_iff] at he
          rcases he with ⟨h1, _⟩ | ⟨_, h2⟩
          · exact hup h1
          · exact hvp h2
        · intro he; rw [Sym2.eq_iff] at he
          rcases he with ⟨_, h2⟩ | ⟨h1, _⟩
          · exact hvp h2
          · exact hup h1
      · rintro ⟨hne2, hne1, huv⟩
        refine ⟨huv, ?_, ?_⟩
        · intro hup; subst hup
          rcases hpdeg v huv with rfl | rfl
          · exact hne1 (by rw [Sym2.eq_iff]; exact Or.inr ⟨rfl, rfl⟩)
          · exact hne2 (by rw [Sym2.eq_iff]; exact Or.inl ⟨rfl, rfl⟩)
        · intro hvp; subst hvp
          rcases hpdeg u huv.symm with rfl | rfl
          · exact hne1 (by rw [Sym2.eq_iff]; exact Or.inl ⟨rfl, rfl⟩)
          · exact hne2 (by rw [Sym2.eq_iff]; exact Or.inr ⟨rfl, rfl⟩)
  rw [heq]
  have hmem1 : s(ℓ, p) ∈ G.edgeFinset := by rw [SimpleGraph.mem_edgeFinset]; exact hlp
  have hne_edges : s(p, q) ≠ s(ℓ, p) := by
    intro h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact hlp.ne h1.symm
    · exact hqne h2
  have hmem2 : s(p, q) ∈ G.edgeFinset.erase s(ℓ, p) :=
    Finset.mem_erase.2 ⟨hne_edges, by rw [SimpleGraph.mem_edgeFinset]; exact hpq⟩
  have hpos2 : 1 ≤ (G.edgeFinset.erase s(ℓ, p)).card := Finset.one_le_card.2 ⟨s(p, q), hmem2⟩
  rw [Finset.card_erase_of_mem hmem2, Finset.card_erase_of_mem hmem1]
  rw [Finset.card_erase_of_mem hmem1] at hpos2
  omega

private lemma edgeFinset_card_deletePair_deg2 {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (u' u v w w' : Fin n)
    (hu'v : u' ≠ v) (hvw' : v ≠ w') (huw : u ≠ w) (huw' : u ≠ w')
    (hu_nbr : ∀ z, G.Adj u z ↔ z = u' ∨ z = v)
    (hw_nbr : ∀ z, G.Adj w z ↔ z = v ∨ z = w')
    [DecidableRel (deleteVertexEdges (deleteVertexEdges G u) w).Adj] :
    (deleteVertexEdges (deleteVertexEdges G u) w).edgeFinset.card + 4 = G.edgeFinset.card := by
  classical
  have h1 := edgeFinset_card_deleteVertex_deg2 G u' u v ((hu_nbr u').2 (Or.inl rfl)).symm
    ((hu_nbr v).2 (Or.inr rfl)) hu'v.symm (fun z hz => (hu_nbr z).1 hz)
  have hw_adj_v : (deleteVertexEdges G u).Adj v w :=
    ⟨((hw_nbr v).2 (Or.inl rfl)).symm, ((hu_nbr v).2 (Or.inr rfl)).ne.symm, huw.symm⟩
  have hw_adj_w' : (deleteVertexEdges G u).Adj w w' :=
    ⟨(hw_nbr w').2 (Or.inr rfl), huw.symm, huw'.symm⟩
  have hw_deg : ∀ z, (deleteVertexEdges G u).Adj w z → z = v ∨ z = w' :=
    fun z hz => (hw_nbr z).1 hz.1
  have h2 := edgeFinset_card_deleteVertex_deg2 (deleteVertexEdges G u) v w w'
    hw_adj_v hw_adj_w' hvw'.symm hw_deg
  omega

private def forestFun {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (g : (Fin k → Bool) → Bool) (x : Fin (n + k) → Bool) : Bool :=
  decide ((∃ a ∈ A, x (Fin.castAdd k a) = true) ∨
    ∃ u v : Fin n, G.Adj u v ∧ x (Fin.castAdd k u) = true ∧ x (Fin.castAdd k v) = true) ||
  g (fun j : Fin k => x (Fin.natAdd n j))

private lemma exists_false_true_of_nonconst {k : ℕ} {g : (Fin k → Bool) → Bool}
    (hg_nc : ∃ y y' : Fin k → Bool, g y ≠ g y') :
    (∃ y₀, g y₀ = false) ∧ (∃ y₁, g y₁ = true) := by
  obtain ⟨y, y', hne⟩ := hg_nc
  cases hy : g y <;> cases hy' : g y'
  · exact absurd (hy.trans hy'.symm) hne
  · exact ⟨⟨y, hy⟩, ⟨y', hy'⟩⟩
  · exact ⟨⟨y', hy'⟩, ⟨y, hy⟩⟩
  · exact absurd (hy.trans hy'.symm) hne

private lemma forestFun_nonconst {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (g : (Fin k → Bool) → Bool)
    (hg_nc : ∃ y y' : Fin k → Bool, g y ≠ g y') :
    ∃ x x' : Fin (n + k) → Bool, forestFun G A g x ≠ forestFun G A g x' := by
  obtain ⟨⟨y₀, hy₀⟩, ⟨y₁, hy₁⟩⟩ := exists_false_true_of_nonconst hg_nc
  refine ⟨Fin.append (fun _ : Fin n => false) y₀, Fin.append (fun _ : Fin n => false) y₁, ?_⟩
  have h0 : forestFun G A g (Fin.append (fun _ : Fin n => false) y₀) = false := by
    simp only [forestFun, Fin.append_left, Fin.append_right]
    simp [hy₀]
  have h1 : forestFun G A g (Fin.append (fun _ : Fin n => false) y₁) = true := by
    simp only [forestFun, Fin.append_left, Fin.append_right]
    simp [hy₁]
  rw [h0, h1]
  decide

private lemma forestFun_mono_left {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (g : (Fin k → Bool) → Bool) (x₁ x₂ : Fin (n + k) → Bool)
    (hleft : ∀ u : Fin n, x₁ (Fin.castAdd k u) = true → x₂ (Fin.castAdd k u) = true)
    (hright : ∀ j : Fin k, x₁ (Fin.natAdd n j) = x₂ (Fin.natAdd n j))
    (ht : forestFun G A g x₁ = true) :
    forestFun G A g x₂ = true := by
  simp only [forestFun, Bool.or_eq_true, decide_eq_true_eq] at ht ⊢
  rcases ht with (⟨a, ha, hax⟩ | ⟨u, v, huv, hux, hvx⟩) | hg
  · exact Or.inl (Or.inl ⟨a, ha, hleft a hax⟩)
  · exact Or.inl (Or.inr ⟨u, v, huv, hleft u hux, hleft v hvx⟩)
  · right
    have heq : (fun j : Fin k => x₂ (Fin.natAdd n j)) = (fun j : Fin k => x₁ (Fin.natAdd n j)) := by
      funext j; exact (hright j).symm
    rw [heq]; exact hg

private lemma forestFun_update_A {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (g : (Fin k → Bool) → Bool)
    (a : Fin n) (ha_iso : ∀ v : Fin n, ¬ G.Adj a v) :
    (fun x => forestFun G A g (Function.update x (Fin.castAdd k a) false)) =
      forestFun G (A.erase a) g := by
  funext x
  simp only [forestFun]
  have hnat : (fun j : Fin k => Function.update x (Fin.castAdd k a) false (Fin.natAdd n j)) =
      (fun j : Fin k => x (Fin.natAdd n j)) := by
    funext j
    apply Function.update_of_ne
    intro h
    have hval := congrArg Fin.val h
    simp [Fin.castAdd, Fin.natAdd] at hval
    omega
  rw [hnat]
  congr 1
  apply decide_eq_decide.2
  constructor
  · rintro (⟨b, hb, hbx⟩ | ⟨u, v, huv, hux, hvx⟩)
    · left
      have hba : b ≠ a := by
        intro h; subst h; simp at hbx
      refine ⟨b, Finset.mem_erase.2 ⟨hba, hb⟩, ?_⟩
      have hne : Fin.castAdd k b ≠ Fin.castAdd k a := fun h => hba (Fin.castAdd_injective n k h)
      rwa [Function.update_of_ne hne] at hbx
    · right
      have hua : u ≠ a := fun h => ha_iso v (h ▸ huv)
      have hva : v ≠ a := fun h => ha_iso u (h ▸ huv.symm)
      have hne1 : Fin.castAdd k u ≠ Fin.castAdd k a := fun h => hua (Fin.castAdd_injective n k h)
      have hne2 : Fin.castAdd k v ≠ Fin.castAdd k a := fun h => hva (Fin.castAdd_injective n k h)
      rw [Function.update_of_ne hne1] at hux
      rw [Function.update_of_ne hne2] at hvx
      exact ⟨u, v, huv, hux, hvx⟩
  · rintro (⟨b, hb, hbx⟩ | ⟨u, v, huv, hux, hvx⟩)
    · left
      obtain ⟨hba, hbA⟩ := Finset.mem_erase.1 hb
      have hne : Fin.castAdd k b ≠ Fin.castAdd k a := fun h => hba (Fin.castAdd_injective n k h)
      exact ⟨b, hbA, by rw [Function.update_of_ne hne]; exact hbx⟩
    · right
      have hua : u ≠ a := fun h => ha_iso v (h ▸ huv)
      have hva : v ≠ a := fun h => ha_iso u (h ▸ huv.symm)
      have hne1 : Fin.castAdd k u ≠ Fin.castAdd k a := fun h => hua (Fin.castAdd_injective n k h)
      have hne2 : Fin.castAdd k v ≠ Fin.castAdd k a := fun h => hva (Fin.castAdd_injective n k h)
      exact ⟨u, v, huv, by rw [Function.update_of_ne hne1]; exact hux,
        by rw [Function.update_of_ne hne2]; exact hvx⟩

private lemma forestFun_update_leaf_false {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (g : (Fin k → Bool) → Bool) (ℓ p : Fin n) (hleaf : ∀ w, G.Adj ℓ w → w = p)
    [DecidableRel (G.deleteEdges {s(ℓ, p)}).Adj] :
    (fun x => forestFun G ∅ g (Function.update x (Fin.castAdd k ℓ) false)) =
      forestFun (G.deleteEdges {s(ℓ, p)}) ∅ g := by
  funext x
  simp only [forestFun]
  have hnat : (fun j : Fin k => Function.update x (Fin.castAdd k ℓ) false (Fin.natAdd n j)) =
      (fun j : Fin k => x (Fin.natAdd n j)) := by
    funext j
    apply Function.update_of_ne
    intro h
    have hval := congrArg Fin.val h
    simp [Fin.castAdd, Fin.natAdd] at hval
    omega
  rw [hnat]
  congr 1
  apply decide_eq_decide.2
  simp only [Finset.notMem_empty, false_and, exists_false, false_or]
  constructor
  · rintro ⟨u, v, huv, hux, hvx⟩
    have huℓ : u ≠ ℓ := by intro h; subst h; simp at hux
    have hvℓ : v ≠ ℓ := by intro h; subst h; simp at hvx
    have hne1 : Fin.castAdd k u ≠ Fin.castAdd k ℓ := fun h => huℓ (Fin.castAdd_injective n k h)
    have hne2 : Fin.castAdd k v ≠ Fin.castAdd k ℓ := fun h => hvℓ (Fin.castAdd_injective n k h)
    rw [Function.update_of_ne hne1] at hux
    rw [Function.update_of_ne hne2] at hvx
    refine ⟨u, v, SimpleGraph.deleteEdges_adj.2 ⟨huv, ?_⟩, hux, hvx⟩
    intro heq
    simp only [Set.mem_singleton_iff, Sym2.eq_iff] at heq
    rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact huℓ rfl
    · exact hvℓ rfl
  · rintro ⟨u, v, hadj, hux, hvx⟩
    obtain ⟨huv, hne⟩ := SimpleGraph.deleteEdges_adj.1 hadj
    simp only [Set.mem_singleton_iff] at hne
    have huℓ : u ≠ ℓ := by
      intro h; subst h
      have hv_eq : v = p := hleaf v huv
      subst hv_eq
      exact hne rfl
    have hvℓ : v ≠ ℓ := by
      intro h; subst h
      have hu_eq : u = p := hleaf u huv.symm
      subst hu_eq
      exact hne Sym2.eq_swap
    have hne1 : Fin.castAdd k u ≠ Fin.castAdd k ℓ := fun h => huℓ (Fin.castAdd_injective n k h)
    have hne2 : Fin.castAdd k v ≠ Fin.castAdd k ℓ := fun h => hvℓ (Fin.castAdd_injective n k h)
    exact ⟨u, v, huv, by rw [Function.update_of_ne hne1]; exact hux,
      by rw [Function.update_of_ne hne2]; exact hvx⟩

private lemma forestFun_update_leaf_true {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (g : (Fin k → Bool) → Bool) (ℓ p : Fin n) (hlp : G.Adj ℓ p)
    (hleaf : ∀ w, G.Adj ℓ w → w = p) [DecidableRel (deleteVertexEdges G p).Adj] :
    (fun x => forestFun G ∅ g (Function.update x (Fin.castAdd k ℓ) true)) =
      forestFun (deleteVertexEdges G p) {p} g := by
  funext x
  simp only [forestFun]
  have hnat : (fun j : Fin k => Function.update x (Fin.castAdd k ℓ) true (Fin.natAdd n j)) =
      (fun j : Fin k => x (Fin.natAdd n j)) := by
    funext j
    apply Function.update_of_ne
    intro h
    have hval := congrArg Fin.val h
    simp [Fin.castAdd, Fin.natAdd] at hval
    omega
  rw [hnat]
  congr 1
  apply decide_eq_decide.2
  simp only [Finset.notMem_empty, false_and, exists_false, false_or, Finset.mem_singleton,
    exists_eq_left]
  have hpneℓ : Fin.castAdd k p ≠ Fin.castAdd k ℓ :=
    fun h => hlp.ne.symm (Fin.castAdd_injective n k h)
  constructor
  · rintro ⟨u, v, huv, hux, hvx⟩
    by_cases hup : u = p
    · subst hup
      rw [Function.update_of_ne hpneℓ] at hux
      exact Or.inl hux
    · by_cases hvp : v = p
      · subst hvp
        rw [Function.update_of_ne hpneℓ] at hvx
        exact Or.inl hvx
      · right
        have huℓ : u ≠ ℓ := fun h => hvp (hleaf v (h ▸ huv))
        have hvℓ : v ≠ ℓ := fun h => hup (hleaf u (h ▸ huv.symm))
        have hne1 : Fin.castAdd k u ≠ Fin.castAdd k ℓ := fun h => huℓ (Fin.castAdd_injective n k h)
        have hne2 : Fin.castAdd k v ≠ Fin.castAdd k ℓ := fun h => hvℓ (Fin.castAdd_injective n k h)
        rw [Function.update_of_ne hne1] at hux
        rw [Function.update_of_ne hne2] at hvx
        exact ⟨u, v, ⟨huv, hup, hvp⟩, hux, hvx⟩
  · rintro (hpx | ⟨u, v, ⟨huv, hup, hvp⟩, hux, hvx⟩)
    · exact ⟨ℓ, p, hlp, by simp, by rw [Function.update_of_ne hpneℓ]; exact hpx⟩
    · have huℓ : u ≠ ℓ := fun h => hvp (hleaf v (h ▸ huv))
      have hvℓ : v ≠ ℓ := fun h => hup (hleaf u (h ▸ huv.symm))
      have hne1 : Fin.castAdd k u ≠ Fin.castAdd k ℓ := fun h => huℓ (Fin.castAdd_injective n k h)
      have hne2 : Fin.castAdd k v ≠ Fin.castAdd k ℓ := fun h => hvℓ (Fin.castAdd_injective n k h)
      exact ⟨u, v, huv, by rw [Function.update_of_ne hne1]; exact hux,
        by rw [Function.update_of_ne hne2]; exact hvx⟩

private lemma forestFun_update_deg2_false {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (g : (Fin k → Bool) → Bool) (v : Fin n) [DecidableRel (deleteVertexEdges G v).Adj] :
    (fun x => forestFun G ∅ g (Function.update x (Fin.castAdd k v) false)) =
      forestFun (deleteVertexEdges G v) ∅ g := by
  funext x
  simp only [forestFun]
  have hnat : (fun j : Fin k => Function.update x (Fin.castAdd k v) false (Fin.natAdd n j)) =
      (fun j : Fin k => x (Fin.natAdd n j)) := by
    funext j
    apply Function.update_of_ne
    intro h; have hval := congrArg Fin.val h; simp [Fin.castAdd, Fin.natAdd] at hval; omega
  rw [hnat]
  congr 1
  apply decide_eq_decide.2
  simp only [Finset.notMem_empty, false_and, exists_false, false_or]
  constructor
  · rintro ⟨a, b, hab, hax, hbx⟩
    have hav : a ≠ v := by intro h; subst h; simp at hax
    have hbv : b ≠ v := by intro h; subst h; simp at hbx
    have hne1 : Fin.castAdd k a ≠ Fin.castAdd k v := fun h => hav (Fin.castAdd_injective n k h)
    have hne2 : Fin.castAdd k b ≠ Fin.castAdd k v := fun h => hbv (Fin.castAdd_injective n k h)
    rw [Function.update_of_ne hne1] at hax
    rw [Function.update_of_ne hne2] at hbx
    exact ⟨a, b, ⟨hab, hav, hbv⟩, hax, hbx⟩
  · rintro ⟨a, b, ⟨hab, hav, hbv⟩, hax, hbx⟩
    have hne1 : Fin.castAdd k a ≠ Fin.castAdd k v := fun h => hav (Fin.castAdd_injective n k h)
    have hne2 : Fin.castAdd k b ≠ Fin.castAdd k v := fun h => hbv (Fin.castAdd_injective n k h)
    exact ⟨a, b, hab, by rw [Function.update_of_ne hne1]; exact hax,
      by rw [Function.update_of_ne hne2]; exact hbx⟩

private lemma forestFun_update_deg2_true {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (g : (Fin k → Bool) → Bool) (u v w : Fin n)
    (hv_nbr : ∀ z, G.Adj v z ↔ z = u ∨ z = w)
    [DecidableRel (deleteVertexEdges (deleteVertexEdges G u) w).Adj] :
    (fun x => forestFun G ∅ g (Function.update x (Fin.castAdd k v) true)) =
      forestFun (deleteVertexEdges (deleteVertexEdges G u) w) {u, w} g := by
  funext x
  simp only [forestFun]
  have hnat : (fun j : Fin k => Function.update x (Fin.castAdd k v) true (Fin.natAdd n j)) =
      (fun j : Fin k => x (Fin.natAdd n j)) := by
    funext j
    apply Function.update_of_ne
    intro h; have hval := congrArg Fin.val h; simp [Fin.castAdd, Fin.natAdd] at hval; omega
  rw [hnat]
  congr 1
  apply decide_eq_decide.2
  have huv : G.Adj v u := (hv_nbr u).2 (Or.inl rfl)
  have hvw : G.Adj v w := (hv_nbr w).2 (Or.inr rfl)
  have hune : Fin.castAdd k u ≠ Fin.castAdd k v := fun h => huv.ne.symm (Fin.castAdd_injective n k h)
  have hwne : Fin.castAdd k w ≠ Fin.castAdd k v := fun h => hvw.ne.symm (Fin.castAdd_injective n k h)
  simp only [Finset.notMem_empty, false_and, exists_false, false_or, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨a, b, hab, hax, hbx⟩
    by_cases hau : a = u
    · rw [hau, Function.update_of_ne hune] at hax; exact Or.inl ⟨u, Or.inl rfl, hax⟩
    · by_cases hbu : b = u
      · rw [hbu, Function.update_of_ne hune] at hbx; exact Or.inl ⟨u, Or.inl rfl, hbx⟩
      · by_cases haw : a = w
        · rw [haw, Function.update_of_ne hwne] at hax; exact Or.inl ⟨w, Or.inr rfl, hax⟩
        · by_cases hbw : b = w
          · rw [hbw, Function.update_of_ne hwne] at hbx; exact Or.inl ⟨w, Or.inr rfl, hbx⟩
          · right
            have hav : a ≠ v := by
              intro h; subst h; rcases (hv_nbr b).1 hab with h1 | h1
              · exact hbu h1
              · exact hbw h1
            have hbv : b ≠ v := by
              intro h; subst h; rcases (hv_nbr a).1 hab.symm with h1 | h1
              · exact hau h1
              · exact haw h1
            have hne1 : Fin.castAdd k a ≠ Fin.castAdd k v := fun h => hav (Fin.castAdd_injective n k h)
            have hne2 : Fin.castAdd k b ≠ Fin.castAdd k v := fun h => hbv (Fin.castAdd_injective n k h)
            rw [Function.update_of_ne hne1] at hax
            rw [Function.update_of_ne hne2] at hbx
            exact ⟨a, b, ⟨⟨hab, hau, hbu⟩, haw, hbw⟩, hax, hbx⟩
  · rintro (⟨c, hcu | hcw, hcx⟩ | ⟨a, b, ⟨⟨hab, hau, hbu⟩, haw, hbw⟩, hax, hbx⟩)
    · rw [hcu] at hcx; exact ⟨v, u, huv, by simp, by rw [Function.update_of_ne hune]; exact hcx⟩
    · rw [hcw] at hcx; exact ⟨v, w, hvw, by simp, by rw [Function.update_of_ne hwne]; exact hcx⟩
    · have hav : a ≠ v := by
        intro h; subst h; rcases (hv_nbr b).1 hab with h1 | h1
        · exact hbu h1
        · exact hbw h1
      have hbv : b ≠ v := by
        intro h; subst h; rcases (hv_nbr a).1 hab.symm with h1 | h1
        · exact hau h1
        · exact haw h1
      have hne1 : Fin.castAdd k a ≠ Fin.castAdd k v := fun h => hav (Fin.castAdd_injective n k h)
      have hne2 : Fin.castAdd k b ≠ Fin.castAdd k v := fun h => hbv (Fin.castAdd_injective n k h)
      exact ⟨a, b, hab, by rw [Function.update_of_ne hne1]; exact hax,
        by rw [Function.update_of_ne hne2]; exact hbx⟩

private lemma forestFun_dep_A {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (g : (Fin k → Bool) → Bool)
    (hg_nc : ∃ y y' : Fin k → Bool, g y ≠ g y') (a : Fin n) (ha : a ∈ A) :
    ∃ x : Fin (n + k) → Bool,
      forestFun G A g (Function.update x (Fin.castAdd k a) false) ≠
      forestFun G A g (Function.update x (Fin.castAdd k a) true) := by
  obtain ⟨⟨y₀, hy₀⟩, _⟩ := exists_false_true_of_nonconst hg_nc
  refine ⟨Fin.append (fun _ : Fin n => false) y₀, ?_⟩
  have h0 : forestFun G A g
      (Function.update (Fin.append (fun _ : Fin n => false) y₀) (Fin.castAdd k a) false) = false := by
    have hupd : Function.update (Fin.append (fun _ : Fin n => false) y₀) (Fin.castAdd k a) false =
        Fin.append (fun _ : Fin n => false) y₀ := by
      funext i
      by_cases hi : i = Fin.castAdd k a
      · subst hi; simp [Fin.append_left]
      · rw [Function.update_of_ne hi]
    rw [hupd]
    simp only [forestFun, Fin.append_left, Fin.append_right]
    simp [hy₀]
  have h1 : forestFun G A g
      (Function.update (Fin.append (fun _ : Fin n => false) y₀) (Fin.castAdd k a) true) = true := by
    simp only [forestFun]
    have ht : (∃ b ∈ A, Function.update (Fin.append (fun _ : Fin n => false) y₀)
        (Fin.castAdd k a) true (Fin.castAdd k b) = true) := ⟨a, ha, by simp⟩
    simp [ht]
  rw [h0, h1]
  decide

private lemma forestFun_dep_edge {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (g : (Fin k → Bool) → Bool) (hg_nc : ∃ y y' : Fin k → Bool, g y ≠ g y')
    (ℓ p : Fin n) (hlp : G.Adj ℓ p) :
    ∃ x : Fin (n + k) → Bool,
      forestFun G ∅ g (Function.update x (Fin.castAdd k ℓ) false) ≠
      forestFun G ∅ g (Function.update x (Fin.castAdd k ℓ) true) := by
  obtain ⟨⟨y₀, hy₀⟩, _⟩ := exists_false_true_of_nonconst hg_nc
  set x0 : Fin (n + k) → Bool := Fin.append (fun i : Fin n => decide (i = p)) y₀ with hx0
  refine ⟨x0, ?_⟩
  have hpneℓ : Fin.castAdd k p ≠ Fin.castAdd k ℓ :=
    fun h => hlp.ne.symm (Fin.castAdd_injective n k h)
  have h0 : forestFun G ∅ g (Function.update x0 (Fin.castAdd k ℓ) false) = false := by
    have hupd : Function.update x0 (Fin.castAdd k ℓ) false = x0 := by
      funext i
      by_cases hi : i = Fin.castAdd k ℓ
      · subst hi; simp [hx0, Fin.append_left, hlp.ne]
      · rw [Function.update_of_ne hi]
    rw [hupd]
    simp only [forestFun, hx0, Fin.append_left, Fin.append_right]
    have hno : ¬ (∃ u v : Fin n, G.Adj u v ∧ decide (u = p) = true ∧ decide (v = p) = true) := by
      rintro ⟨u, v, huv, hu, hv⟩
      rw [decide_eq_true_eq] at hu hv
      subst hu; subst hv
      exact G.loopless.irrefl _ huv
    simp [hy₀]
  have h1 : forestFun G ∅ g (Function.update x0 (Fin.castAdd k ℓ) true) = true := by
    simp only [forestFun]
    have ht : ∃ u v : Fin n, G.Adj u v ∧
        Function.update x0 (Fin.castAdd k ℓ) true (Fin.castAdd k u) = true ∧
        Function.update x0 (Fin.castAdd k ℓ) true (Fin.castAdd k v) = true := by
      refine ⟨ℓ, p, hlp, by simp, ?_⟩
      rw [Function.update_of_ne hpneℓ]
      simp [hx0, Fin.append_left]
    simp [ht]
  rw [h0, h1]
  decide

private lemma lower_bound_acyclic {k c : ℕ} {g : (Fin k → Bool) → Bool}
    (hg_nc : ∃ y y' : Fin k → Bool, g y ≠ g y')
    (hg_sz : ∀ r : ℕ, HasCircuitSize k g r ↔ c ≤ r) :
    ∀ (s : ℕ) {n t : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)),
      G.IsAcyclic →
      (∀ a ∈ A, ∀ v : Fin n, ¬ G.Adj a v) →
      HasMinVC G t →
      HasCircuitSize (n + k) (forestFun G A g) s →
      A.card + G.edgeFinset.card + t + c ≤ s := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro n t G _ A hAcyc hA_iso hvc hC
    by_cases hAne : A.Nonempty
    · obtain ⟨a, ha⟩ := hAne
      have hdep := forestFun_dep_A G A g hg_nc a ha
      have hrew := forestFun_update_A G A g a (hA_iso a ha)
      have hnc : ∃ x x',
          forestFun G A g (Function.update x (Fin.castAdd k a) false) ≠
          forestFun G A g (Function.update x' (Fin.castAdd k a) false) := by
        simpa only [← congrFun hrew] using forestFun_nonconst G (A.erase a) g hg_nc
      obtain ⟨hs1, hC'⟩ := elim_one_var (Fin.castAdd k a) false hC hdep hnc
      rw [hrew] at hC'
      have hih := ih (s - 1) (by omega) G (A.erase a) hAcyc
        (fun b hb => hA_iso b (Finset.mem_of_mem_erase hb)) hvc hC'
      have hcard : (A.erase a).card + 1 = A.card := by
        have hpos : 1 ≤ A.card := Finset.one_le_card.2 ⟨a, ha⟩
        rw [Finset.card_erase_of_mem ha]; omega
      omega
    · have hAempty : A = ∅ := Finset.not_nonempty_iff_eq_empty.1 hAne
      subst hAempty
      by_cases hEdge : ∃ u v : Fin n, G.Adj u v
      · obtain ⟨ℓ, p, hlp, hleaf, hcases⟩ := acyclic_leaf_cases G hAcyc hEdge
        rcases hcases with ⟨ℓ', hℓ'ne, hℓ'p, hℓ'leaf⟩ | hpdeg1 | ⟨q, hqne, hpq, hpdeg2⟩
        · classical
          obtain ⟨t₁, hvc₁⟩ := hasMinVC_exists (G.deleteEdges {s(ℓ, p)})
          have ht₁ : t₁ = t := hasMinVC_deleteLeafEdge_eq G ℓ ℓ' p hℓ'ne hℓ'p hℓ'leaf hvc hvc₁
          have hdep := forestFun_dep_edge G g hg_nc ℓ p hlp
          have hrew := forestFun_update_leaf_false G g ℓ p hleaf
          have hnc : ∃ x x',
              forestFun G ∅ g (Function.update x (Fin.castAdd k ℓ) false) ≠
              forestFun G ∅ g (Function.update x' (Fin.castAdd k ℓ) false) := by
            obtain ⟨x, x', hne⟩ := forestFun_nonconst (G.deleteEdges {s(ℓ, p)}) ∅ g hg_nc
            refine ⟨x, x', ?_⟩
            rw [congrFun hrew x, congrFun hrew x']
            exact hne
          obtain ⟨hs1, hC'⟩ := elim_one_var (Fin.castAdd k ℓ) false hC hdep hnc
          rw [hrew] at hC'
          have hih := ih (s - 1) (by omega) (G.deleteEdges {s(ℓ, p)}) ∅
            (hAcyc.anti (SimpleGraph.deleteEdges_le _)) (by simp) hvc₁ hC'
          have hedge := edgeFinset_card_deleteEdge G ℓ p hlp
          simp only [Finset.card_empty, zero_add] at hih ⊢
          omega
        · classical
          obtain ⟨t', hvc'⟩ := hasMinVC_exists (deleteVertexEdges G p)
          have ht' : t' + 1 = t := hasMinVC_deleteVertex G ℓ p hlp hleaf hvc hvc'
          have hdep := forestFun_dep_edge G g hg_nc ℓ p hlp
          have hrew := forestFun_update_leaf_true G g ℓ p hlp hleaf
          have hnc : ∃ x x',
              forestFun G ∅ g (Function.update x (Fin.castAdd k ℓ) true) ≠
              forestFun G ∅ g (Function.update x' (Fin.castAdd k ℓ) true) := by
            obtain ⟨x, x', hne⟩ := forestFun_nonconst (deleteVertexEdges G p) {p} g hg_nc
            refine ⟨x, x', ?_⟩
            rw [congrFun hrew x, congrFun hrew x']
            exact hne
          obtain ⟨hs1, hC'⟩ := elim_one_var (Fin.castAdd k ℓ) true hC hdep hnc
          rw [hrew] at hC'
          have hih := ih (s - 1) (by omega) (deleteVertexEdges G p) {p}
            (hAcyc.anti (deleteVertexEdges_le G p))
            (by intro a ha v h; simp at ha; subst ha; exact h.2.1 rfl)
            hvc' hC'
          have hedge := edgeFinset_card_deleteVertex_deg1 G ℓ p hlp hpdeg1
          simp only [Finset.card_singleton, Finset.card_empty, zero_add] at hih ⊢
          omega
        · classical
          have hdep := forestFun_dep_edge G g hg_nc ℓ p hlp
          have hrew0 := forestFun_update_leaf_false G g ℓ p hleaf
          have hrew1 := forestFun_update_leaf_true G g ℓ p hlp hleaf
          have hnc0 : ∃ x x',
              forestFun G ∅ g (Function.update x (Fin.castAdd k ℓ) false) ≠
              forestFun G ∅ g (Function.update x' (Fin.castAdd k ℓ) false) := by
            obtain ⟨x, x', hne⟩ := forestFun_nonconst (G.deleteEdges {s(ℓ, p)}) ∅ g hg_nc
            refine ⟨x, x', ?_⟩
            rw [congrFun hrew0 x, congrFun hrew0 x']
            exact hne
          have hnc1 : ∃ x x',
              forestFun G ∅ g (Function.update x (Fin.castAdd k ℓ) true) ≠
              forestFun G ∅ g (Function.update x' (Fin.castAdd k ℓ) true) := by
            obtain ⟨x, x', hne⟩ := forestFun_nonconst (deleteVertexEdges G p) {p} g hg_nc
            refine ⟨x, x', ?_⟩
            rw [congrFun hrew1 x, congrFun hrew1 x']
            exact hne
          obtain ⟨hs2, hC0 | hC1⟩ := elim_two_var (Fin.castAdd k ℓ) hC hdep hnc0 hnc1
          · rw [hrew0] at hC0
            obtain ⟨t₁, hvc₁⟩ := hasMinVC_exists (G.deleteEdges {s(ℓ, p)})
            have ht₁ := (hasMinVC_deleteEdge G ℓ p hvc hvc₁).2
            have hih := ih (s - 2) (by omega) (G.deleteEdges {s(ℓ, p)}) ∅
              (hAcyc.anti (SimpleGraph.deleteEdges_le _)) (by simp) hvc₁ hC0
            have hedge := edgeFinset_card_deleteEdge G ℓ p hlp
            simp only [Finset.card_empty, zero_add] at hih ⊢
            omega
          · rw [hrew1] at hC1
            obtain ⟨t', hvc'⟩ := hasMinVC_exists (deleteVertexEdges G p)
            have ht' : t' + 1 = t := hasMinVC_deleteVertex G ℓ p hlp hleaf hvc hvc'
            have hih := ih (s - 2) (by omega) (deleteVertexEdges G p) {p}
              (hAcyc.anti (deleteVertexEdges_le G p))
              (by intro a ha v h; simp at ha; subst ha; exact h.2.1 rfl)
              hvc' hC1
            have hedge := edgeFinset_card_deleteVertex_deg2 G ℓ p q hlp hpq hqne hpdeg2
            simp only [Finset.card_singleton, Finset.card_empty, zero_add] at hih ⊢
            omega
      · have hempty : ∀ u v : Fin n, ¬ G.Adj u v := fun u v h => hEdge ⟨u, v, h⟩
        have ht0 : t = 0 := hasMinVC_empty G hempty hvc
        have he0 : G.edgeFinset.card = 0 := by
          apply Finset.card_eq_zero.2
          ext e
          induction e using Sym2.ind with
          | _ u v => simp [SimpleGraph.mem_edgeFinset, hempty u v]
        have hFg : ∀ x : Fin (n + k) → Bool,
            forestFun G ∅ g x = g (fun j : Fin k => x (Fin.natAdd n j)) := by
          intro x
          simp only [forestFun, Finset.notMem_empty, false_and, exists_false, false_or]
          have hno : ¬ ∃ u v : Fin n, G.Adj u v ∧
              x (Fin.castAdd k u) = true ∧ x (Fin.castAdd k v) = true := by
            rintro ⟨u, v, huv, _, _⟩; exact hempty u v huv
          simp [hno]
        have hCg : HasCircuitSize k g s := hardwire_prefix_nonconst hC hFg hg_nc
        have hcs : c ≤ s := (hg_sz s).1 hCg
        simp only [Finset.card_empty, zero_add, he0, ht0]
        omega

private def shiftGate (n : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (· + n)⟩

private lemma shiftGate_ok (n : ℕ) (g : Gate) (h : OkGate g) : OkGate (shiftGate n g) :=
  ⟨h.1, by simp [shiftGate]; exact h.2⟩

private lemma wiresFrom_shift (n : ℕ) (gs : List Gate) (pref w : List Bool)
    (hpref : pref.length = n) :
    wiresFrom (gs.map (shiftGate n)) (pref ++ w) = pref ++ wiresFrom gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, wiresFrom_cons, wiresFrom_cons]
    have hmap : ((shiftGate n g).inputs.map fun i => (pref ++ w).getD i false) =
        (g.inputs.map fun i => w.getD i false) := by
      simp only [shiftGate, List.map_map]
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply]
      by_cases hi : i < w.length
      · rw [List.getD_eq_getElem _ _ (by simp [hpref]; omega),
            List.getElem_append_right (by omega),
            List.getD_eq_getElem _ _ hi]
        congr 1; omega
      · rw [List.getD_eq_default _ _ (by simp [hpref]; omega),
            List.getD_eq_default _ _ (by omega)]
    rw [hmap, List.append_assoc, ih]
    rfl

private lemma list_any_congr_mem {α : Type*} {l : List α} {p q : α → Bool}
    (h : ∀ x ∈ l, p x = q x) : l.any p = l.any q := by
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨x, hx, hpx⟩; exact ⟨x, hx, by rw [← h x hx]; exact hpx⟩
  · rintro ⟨x, hx, hqx⟩; exact ⟨x, hx, by rw [h x hx]; exact hqx⟩

private def pushOrList (m : ℕ) (gs : List Gate) (acc : ℕ) : List ℕ → List Gate × ℕ
  | [] => (gs, acc)
  | w :: ws => pushOrList m (gs ++ [⟨GateOp.or, [acc, w]⟩]) (m + gs.length) ws

private lemma pushOrList_props (m : ℕ) (ws : List ℕ) :
    ∀ (gs : List Gate) (acc : ℕ),
      (∀ g ∈ gs, OkGate g) →
      acc < m + gs.length →
      (∀ w ∈ ws, w < m + gs.length) →
      (∀ g ∈ (pushOrList m gs acc ws).1, OkGate g) ∧
      (pushOrList m gs acc ws).1.length = gs.length + ws.length ∧
      (pushOrList m gs acc ws).2 < m + (pushOrList m gs acc ws).1.length ∧
      (∀ x : List Bool, x.length = m →
        (∀ i < m + gs.length,
          (wiresFrom (pushOrList m gs acc ws).1 x).getD i false = (wiresFrom gs x).getD i false) ∧
        (wiresFrom (pushOrList m gs acc ws).1 x).getD (pushOrList m gs acc ws).2 false =
          ((wiresFrom gs x).getD acc false ||
            ws.any (fun w => (wiresFrom gs x).getD w false))) := by
  induction ws with
  | nil =>
    intro gs acc hok hacc _
    refine ⟨hok, by simp [pushOrList], hacc, fun x _ => ⟨fun _ _ => rfl, by simp [pushOrList]⟩⟩
  | cons w ws ih =>
    intro gs acc hok hacc hws
    set gs' := gs ++ [⟨GateOp.or, [acc, w]⟩] with hgs'
    have hok' : ∀ g ∈ gs', OkGate g := by
      intro g hg
      rcases List.mem_append.1 hg with h | h
      · exact hok g h
      · simp at h; subst h; simp [OkGate]
    have hlen' : gs'.length = gs.length + 1 := by simp [hgs']
    have hacc' : m + gs.length < m + gs'.length := by omega
    have hws' : ∀ u ∈ ws, u < m + gs'.length := by
      intro u hu
      have := hws u (List.mem_cons_of_mem _ hu)
      omega
    obtain ⟨hok2, hlen2, hlt2, hev2⟩ := ih gs' (m + gs.length) hok' hacc' hws'
    refine ⟨hok2, ?_, hlt2, ?_⟩
    · show (pushOrList m gs' (m + gs.length) ws).1.length = gs.length + (w :: ws).length
      rw [hlen2, hlen']
      simp
      omega
    · intro x hx
      obtain ⟨hpres, hval⟩ := hev2 x hx
      have hstep_pres : ∀ i < m + gs.length,
          (wiresFrom gs' x).getD i false = (wiresFrom gs x).getD i false := by
        intro i hi
        rw [hgs', wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
        exact getD_snoc_lt _ _ _ _ (by rw [wiresFrom_length, hx]; exact hi)
      have hstep_new : (wiresFrom gs' x).getD (m + gs.length) false =
          ((wiresFrom gs x).getD acc false || (wiresFrom gs x).getD w false) := by
        rw [hgs', wiresFrom_append, wiresFrom_cons, wiresFrom_nil,
            getD_snoc_eq _ _ _ _ (by rw [wiresFrom_length, hx])]
        simp [GateOp.eval]
      refine ⟨fun i hi => (hpres i (by omega)).trans (hstep_pres i hi), ?_⟩
      show (wiresFrom (pushOrList m gs' (m + gs.length) ws).1 x).getD
          (pushOrList m gs' (m + gs.length) ws).2 false = _
      rw [hval, hstep_new]
      have hany : ws.any (fun u => (wiresFrom gs' x).getD u false) =
          ws.any (fun u => (wiresFrom gs x).getD u false) :=
        list_any_congr_mem fun u hu => hstep_pres u (hws u (List.mem_cons_of_mem _ hu))
      rw [hany]
      simp [Bool.or_assoc]

private def pushStarStep (m : ℕ) (gs : List Gate) (acc : ℕ) (u : ℕ) (vs : List ℕ) :
    List Gate × ℕ :=
  match vs with
  | [] => (gs, acc)
  | v₀ :: vs' =>
    let r1 := pushOrList m gs v₀ vs'
    let gs1 := r1.1 ++ [⟨GateOp.and, [u, r1.2]⟩]
    let w_and := m + r1.1.length
    let gs2 := gs1 ++ [⟨GateOp.or, [acc, w_and]⟩]
    (gs2, m + gs1.length)

private lemma pushStarStep_props (m : ℕ) (gs : List Gate) (acc u : ℕ) (vs : List ℕ)
    (hok : ∀ g ∈ gs, OkGate g) (hacc : acc < m + gs.length) (hu : u < m + gs.length)
    (hvs : ∀ v ∈ vs, v < m + gs.length) :
    (∀ g ∈ (pushStarStep m gs acc u vs).1, OkGate g) ∧
    (pushStarStep m gs acc u vs).1.length ≤ gs.length + vs.length + 1 ∧
    (pushStarStep m gs acc u vs).2 < m + (pushStarStep m gs acc u vs).1.length ∧
    (∀ x : List Bool, x.length = m →
      (∀ i < m + gs.length,
        (wiresFrom (pushStarStep m gs acc u vs).1 x).getD i false = (wiresFrom gs x).getD i false) ∧
      (wiresFrom (pushStarStep m gs acc u vs).1 x).getD (pushStarStep m gs acc u vs).2 false =
        ((wiresFrom gs x).getD acc false ||
          ((wiresFrom gs x).getD u false && vs.any (fun v => (wiresFrom gs x).getD v false)))) := by
  cases vs with
  | nil =>
    refine ⟨hok, by simp [pushStarStep], hacc, fun x _ => ⟨fun _ _ => rfl, by simp [pushStarStep]⟩⟩
  | cons v₀ vs' =>
    obtain ⟨hok1, hlen1, hlt1, hev1⟩ := pushOrList_props m vs' gs v₀ hok
      (hvs v₀ List.mem_cons_self) (fun v hv => hvs v (List.mem_cons_of_mem _ hv))
    set r1 := pushOrList m gs v₀ vs' with hr1
    set gs1 := r1.1 ++ [⟨GateOp.and, [u, r1.2]⟩] with hgs1
    set w_and := m + r1.1.length with hwand
    set gs2 := gs1 ++ [⟨GateOp.or, [acc, w_and]⟩] with hgs2
    have hok1' : ∀ g ∈ gs1, OkGate g := by
      intro g hg
      rcases List.mem_append.1 hg with h | h
      · exact hok1 g h
      · simp at h; subst h; simp [OkGate]
    have hok2 : ∀ g ∈ gs2, OkGate g := by
      intro g hg
      rcases List.mem_append.1 hg with h | h
      · exact hok1' g h
      · simp at h; subst h; simp [OkGate]
    have hlen_gs2 : gs2.length = gs.length + (v₀ :: vs').length + 1 := by
      simp [hgs2, hgs1, hlen1]; omega
    refine ⟨hok2, ?_, ?_, ?_⟩
    · show gs2.length ≤ gs.length + (v₀ :: vs').length + 1; omega
    · show m + gs1.length < m + gs2.length; simp [hgs2]
    · intro x hx
      obtain ⟨hpres1, hval1⟩ := hev1 x hx
      have hpres_and : ∀ i < m + r1.1.length,
          (wiresFrom gs1 x).getD i false = (wiresFrom r1.1 x).getD i false := by
        intro i hi
        rw [hgs1, wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
        exact getD_snoc_lt _ _ _ _ (by rw [wiresFrom_length, hx]; exact hi)
      have hpres_or : ∀ i < m + gs1.length,
          (wiresFrom gs2 x).getD i false = (wiresFrom gs1 x).getD i false := by
        intro i hi
        rw [hgs2, wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
        exact getD_snoc_lt _ _ _ _ (by rw [wiresFrom_length, hx]; exact hi)
      have hval_and : (wiresFrom gs1 x).getD w_and false =
          ((wiresFrom r1.1 x).getD u false && (wiresFrom r1.1 x).getD r1.2 false) := by
        rw [hgs1, wiresFrom_append, wiresFrom_cons, wiresFrom_nil,
            getD_snoc_eq _ _ _ _ (by rw [wiresFrom_length, hx])]
        simp [GateOp.eval]
      have hval_or : (wiresFrom gs2 x).getD (m + gs1.length) false =
          ((wiresFrom gs1 x).getD acc false || (wiresFrom gs1 x).getD w_and false) := by
        rw [hgs2, wiresFrom_append, wiresFrom_cons, wiresFrom_nil,
            getD_snoc_eq _ _ _ _ (by rw [wiresFrom_length, hx])]
        simp [GateOp.eval]
      refine ⟨?_, ?_⟩
      · intro i hi
        have hlen_le : gs.length ≤ r1.1.length := by omega
        have hlen_le1 : r1.1.length ≤ gs1.length := by simp [hgs1]
        exact (hpres_or i (by omega)).trans ((hpres_and i (by omega)).trans (hpres1 i hi))
      · show (wiresFrom gs2 x).getD (m + gs1.length) false = _
        rw [hval_or, hpres_and acc (by omega), hpres1 acc hacc,
            hval_and, hpres1 u hu, hval1]
        simp

private def pushStars (m : ℕ) (gs : List Gate) (acc : ℕ) : List (ℕ × List ℕ) → List Gate × ℕ
  | [] => (gs, acc)
  | (u, vs) :: rest =>
    let r := pushStarStep m gs acc u vs
    pushStars m r.1 r.2 rest

private lemma pushStars_props (m : ℕ) (stars : List (ℕ × List ℕ)) :
    ∀ (gs : List Gate) (acc : ℕ),
      (∀ g ∈ gs, OkGate g) →
      acc < m + gs.length →
      (∀ p ∈ stars, p.1 < m ∧ ∀ v ∈ p.2, v < m) →
      (∀ g ∈ (pushStars m gs acc stars).1, OkGate g) ∧
      (pushStars m gs acc stars).1.length ≤
        gs.length + (stars.map (fun p => p.2.length + 1)).sum ∧
      (pushStars m gs acc stars).2 < m + (pushStars m gs acc stars).1.length ∧
      (∀ x : List Bool, x.length = m →
        (∀ i < m + gs.length,
          (wiresFrom (pushStars m gs acc stars).1 x).getD i false = (wiresFrom gs x).getD i false) ∧
        (wiresFrom (pushStars m gs acc stars).1 x).getD (pushStars m gs acc stars).2 false =
          ((wiresFrom gs x).getD acc false ||
            stars.any (fun p => (wiresFrom gs x).getD p.1 false &&
              p.2.any (fun v => (wiresFrom gs x).getD v false)))) := by
  induction stars with
  | nil =>
    intro gs acc hok hacc _
    refine ⟨hok, by simp [pushStars], hacc, fun x _ => ⟨fun _ _ => rfl, by simp [pushStars]⟩⟩
  | cons st rest ih =>
    obtain ⟨u, vs⟩ := st
    intro gs acc hok hacc hst
    have hst0 := hst (u, vs) List.mem_cons_self
    obtain ⟨hok1, hlen1, hlt1, hev1⟩ := pushStarStep_props m gs acc u vs hok hacc
      (by omega) (fun v hv => by have := hst0.2 v hv; omega)
    set r := pushStarStep m gs acc u vs with hr
    obtain ⟨hok2, hlen2, hlt2, hev2⟩ := ih r.1 r.2 hok1 hlt1
      (fun p hp => hst p (List.mem_cons_of_mem _ hp))
    refine ⟨hok2, ?_, hlt2, ?_⟩
    · show (pushStars m r.1 r.2 rest).1.length ≤
        gs.length + (((u, vs) :: rest).map (fun p => p.2.length + 1)).sum
      simp only [List.map_cons, List.sum_cons]
      omega
    · intro x hx
      obtain ⟨hpres1, hval1⟩ := hev1 x hx
      obtain ⟨hpres2, hval2⟩ := hev2 x hx
      have hlen_le : gs.length ≤ r.1.length := by
        cases vs with
        | nil => simp [hr, pushStarStep]
        | cons v₀ vs' =>
          have := (pushOrList_props m vs' gs v₀ hok (by have := hst0.2 v₀ List.mem_cons_self; omega)
            (fun v hv => by have := hst0.2 v (List.mem_cons_of_mem _ hv); omega)).2.1
          simp [hr, pushStarStep]
          omega
      refine ⟨fun i hi => (hpres2 i (by omega)).trans (hpres1 i hi), ?_⟩
      show (wiresFrom (pushStars m r.1 r.2 rest).1 x).getD (pushStars m r.1 r.2 rest).2 false = _
      rw [hval2, hval1]
      have hany : rest.any (fun p => (wiresFrom r.1 x).getD p.1 false &&
            p.2.any (fun v => (wiresFrom r.1 x).getD v false)) =
          rest.any (fun p => (wiresFrom gs x).getD p.1 false &&
            p.2.any (fun v => (wiresFrom gs x).getD v false)) := by
        refine list_any_congr_mem fun p hp => ?_
        have hpm := hst p (List.mem_cons_of_mem _ hp)
        rw [hpres1 p.1 (by omega)]
        congr 1
        exact list_any_congr_mem fun v hv => hpres1 v (by have := hpm.2 v hv; omega)
      rw [hany]
      simp [Bool.or_assoc]

private lemma upper_bound_aux {n k c t s : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (g : (Fin k → Bool) → Bool)
    (hg_nc : ∃ y y' : Fin k → Bool, g y ≠ g y')
    (hg_sz : ∀ r : ℕ, HasCircuitSize k g r ↔ c ≤ r)
    (hvc_ex : ∃ S : Finset (Fin n), IsVC G S ∧ S.card = t)
    (hs : A.card + G.edgeFinset.card + t + c ≤ s) :
    HasCircuitSize (n + k) (forestFun G A g) s := by
  obtain ⟨Cg, hCg_ok, hCg_sz, hCg_ev⟩ := (hg_sz c).2 (le_refl c)
  obtain ⟨_, ⟨y₁, hy₁⟩⟩ := exists_false_true_of_nonconst hg_nc
  have hCg_out : Cg.output < k + Cg.gates.length := by
    by_contra hge
    have h1 : Cg.eval (List.ofFn y₁) = false := by
      show (wiresFrom Cg.gates (List.ofFn y₁)).getD Cg.output false = false
      exact List.getD_eq_default _ _ (by rw [wiresFrom_length]; simp; omega)
    have h2 := hCg_ev y₁
    rw [h1, hy₁] at h2
    exact Bool.false_ne_true h2
  set gs0 : List Gate := Cg.gates.map (shiftGate n) with hgs0
  have hgs0_ok : ∀ g ∈ gs0, OkGate g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact shiftGate_ok n g0 (hCg_ok g0 hg0)
  have hgs0_len : gs0.length = Cg.gates.length := by simp [hgs0]
  have hgs0_eval : ∀ x : Fin (n + k) → Bool,
      (wiresFrom gs0 (List.ofFn x)).getD (Cg.output + n) false =
        g (fun j : Fin k => x (Fin.natAdd n j)) := by
    intro x
    set pref := List.ofFn (fun i : Fin n => x (Fin.castAdd k i)) with hpref
    set suff := List.ofFn (fun j : Fin k => x (Fin.natAdd n j)) with hsuff
    have hsplit : List.ofFn x = pref ++ suff := by
      apply List.ext_getElem (by simp [hpref, hsuff])
      intro i h1 h2
      by_cases hi : i < n
      · rw [List.getElem_append_left (by simp [hpref]; exact hi)]
        simp [hpref, List.getElem_ofFn, Fin.castAdd]
      · rw [List.getElem_append_right (by simp [hpref]; omega)]
        simp only [hpref, hsuff, List.length_ofFn, List.getElem_ofFn]
        congr 1; ext; simp [Fin.natAdd]; omega
    rw [hsplit, hgs0, wiresFrom_shift n Cg.gates pref suff (by simp [hpref])]
    rw [List.getD_eq_getElem _ _ (by rw [List.length_append, wiresFrom_length]; simp [hpref, hsuff]; omega),
        List.getElem_append_right (by simp [hpref])]
    have heq_idx : Cg.output + n - pref.length = Cg.output := by simp [hpref]
    simp only [heq_idx]
    rw [← List.getD_eq_getElem _ false (by rw [wiresFrom_length]; simp [hsuff]; omega)]
    exact hCg_ev (fun j : Fin k => x (Fin.natAdd n j))
  obtain ⟨S, hS_vc, hS_card⟩ := hvc_ex
  set N : Fin n → Finset (Fin n) :=
    fun u => Finset.univ.filter (fun v => G.Adj u v ∧ (v ∈ S → u < v)) with hN
  have hsum_N : ∑ u ∈ S, (N u).card = G.edgeFinset.card := by
    rw [← Finset.card_sigma]
    refine Finset.card_bij (fun p _ => s(p.1, p.2)) ?_ ?_ ?_
    · intro p hp
      rw [Finset.mem_sigma] at hp
      rw [SimpleGraph.mem_edgeFinset]
      exact (Finset.mem_filter.1 hp.2).2.1
    · intro p₁ hp₁ p₂ hp₂ heq
      rw [Finset.mem_sigma] at hp₁ hp₂
      have h1 := (Finset.mem_filter.1 hp₁.2).2
      have h2 := (Finset.mem_filter.1 hp₂.2).2
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact Sigma.ext ha (by simpa using hb)
      · exfalso
        have hlt1 : p₁.1 < p₁.2 := h1.2 (hb ▸ hp₂.1)
        have hlt2 : p₂.1 < p₂.2 := h2.2 (ha ▸ hp₁.1)
        rw [ha, hb] at hlt1
        exact lt_asymm hlt1 hlt2
    · intro e he
      induction e using Sym2.ind with
      | _ a b =>
        rw [SimpleGraph.mem_edgeFinset] at he
        rcases hS_vc a b he with ha | hb
        · by_cases hba : b ∈ S ∧ b < a
          · refine ⟨⟨b, a⟩, Finset.mem_sigma.2 ⟨hba.1, Finset.mem_filter.2
              ⟨Finset.mem_univ a, he.symm, fun _ => hba.2⟩⟩, Sym2.eq_swap⟩
          · refine ⟨⟨a, b⟩, Finset.mem_sigma.2 ⟨ha, Finset.mem_filter.2
              ⟨Finset.mem_univ b, he, fun hb' => ?_⟩⟩, rfl⟩
            rcases lt_trichotomy a b with h | h | h
            · exact h
            · exact absurd h he.ne
            · exact absurd ⟨hb', h⟩ hba
        · by_cases hab : a ∈ S ∧ a < b
          · refine ⟨⟨a, b⟩, Finset.mem_sigma.2 ⟨hab.1, Finset.mem_filter.2
              ⟨Finset.mem_univ b, he, fun _ => hab.2⟩⟩, rfl⟩
          · refine ⟨⟨b, a⟩, Finset.mem_sigma.2 ⟨hb, Finset.mem_filter.2
              ⟨Finset.mem_univ a, he.symm, fun ha' => ?_⟩⟩, Sym2.eq_swap⟩
            rcases lt_trichotomy b a with h | h | h
            · exact h
            · exact absurd h he.ne.symm
            · exact absurd ⟨ha', h⟩ hab
  set stars : List (ℕ × List ℕ) :=
    S.toList.map (fun u : Fin n => ((u : ℕ), (N u).toList.map Fin.val)) with hstars
  obtain ⟨hok1, hlen1, hlt1, hev1⟩ := pushStars_props (n + k) stars gs0 (Cg.output + n)
    hgs0_ok (by rw [hgs0_len]; omega)
    (by
      intro p hp
      obtain ⟨u, _, rfl⟩ := List.mem_map.1 hp
      refine ⟨by omega, ?_⟩
      intro v hv
      obtain ⟨v', _, rfl⟩ := List.mem_map.1 hv
      omega)
  set r1 := pushStars (n + k) gs0 (Cg.output + n) stars with hr1
  set wsA : List ℕ := A.toList.map Fin.val with hwsA
  obtain ⟨hok2, hlen2, _, hev2⟩ := pushOrList_props (n + k) wsA r1.1 r1.2
    hok1 hlt1 (by
      intro w hw
      obtain ⟨a, _, rfl⟩ := List.mem_map.1 hw
      omega)
  set r2 := pushOrList (n + k) r1.1 r1.2 wsA with hr2
  have hstars_sum : (stars.map (fun p => p.2.length + 1)).sum = G.edgeFinset.card + t := by
    have hmap : stars.map (fun p => p.2.length + 1) =
        S.toList.map (fun u : Fin n => (N u).card + 1) := by
      simp [hstars, List.map_map, Function.comp_def]
    have hsum_list : (S.toList.map (fun u : Fin n => (N u).card + 1)).sum =
        ∑ u ∈ S, ((N u).card + 1) := by
      rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
      rfl
    rw [hmap, hsum_list, Finset.sum_add_distrib,
        hsum_N, Finset.sum_const, smul_eq_mul, mul_one, hS_card]
  have hlen_tot : r2.1.length ≤ s := by
    have hwsA_len : wsA.length = A.card := by simp [hwsA]
    have hCg_sz' : Cg.gates.length ≤ c := hCg_sz
    omega
  refine ⟨⟨r2.1, r2.2⟩, hok2, hlen_tot, ?_⟩
  intro x
  obtain ⟨hpres1, hval1⟩ := hev1 (List.ofFn x) (by simp)
  obtain ⟨_, hval2⟩ := hev2 (List.ofFn x) (by simp)
  show (wiresFrom r2.1 (List.ofFn x)).getD r2.2 false = forestFun G A g x
  rw [hval2, hval1, hgs0_eval x]
  have hwire_in : ∀ u : Fin n, (wiresFrom gs0 (List.ofFn x)).getD (u : ℕ) false =
      x (Fin.castAdd k u) := by
    intro u
    rw [wiresFrom_getD_lt _ _ _ (by simp; omega), ofFn_getD_lt _ _ _ (by omega)]
    rfl
  have hwire_r1 : ∀ u : Fin n, (wiresFrom r1.1 (List.ofFn x)).getD (u : ℕ) false =
      x (Fin.castAdd k u) := by
    intro u
    rw [hpres1 (u : ℕ) (by omega), hwire_in u]
  have hA_eq : wsA.any (fun w => (wiresFrom r1.1 (List.ofFn x)).getD w false) =
      decide (∃ a ∈ A, x (Fin.castAdd k a) = true) := by
    apply Bool.eq_iff_iff.2
    simp only [hwsA, List.any_map, List.any_eq_true, Function.comp_apply, Finset.mem_toList,
      decide_eq_true_eq]
    constructor
    · rintro ⟨a, ha, h⟩; rw [hwire_r1 a] at h; exact ⟨a, ha, h⟩
    · rintro ⟨a, ha, h⟩; exact ⟨a, ha, by rw [hwire_r1 a]; exact h⟩
  have hS_eq : stars.any (fun p => (wiresFrom gs0 (List.ofFn x)).getD p.1 false &&
        p.2.any (fun v => (wiresFrom gs0 (List.ofFn x)).getD v false)) =
      decide (∃ u v : Fin n, G.Adj u v ∧ x (Fin.castAdd k u) = true ∧ x (Fin.castAdd k v) = true) := by
    apply Bool.eq_iff_iff.2
    simp only [hstars, List.any_map, List.any_eq_true, Function.comp_apply, Bool.and_eq_true,
      Finset.mem_toList, decide_eq_true_eq]
    constructor
    · rintro ⟨u, hu, hux, v, hv, hvx⟩
      rw [hwire_in u] at hux
      rw [hwire_in v] at hvx
      exact ⟨u, v, (Finset.mem_filter.1 hv).2.1, hux, hvx⟩
    · rintro ⟨u, v, huv, hux, hvx⟩
      rcases hS_vc u v huv with hu | hv
      · by_cases hvu : v ∈ S ∧ v < u
        · exact ⟨v, hvu.1, by rw [hwire_in v]; exact hvx,
            u, Finset.mem_filter.2 ⟨Finset.mem_univ u, huv.symm, fun _ => hvu.2⟩,
            by rw [hwire_in u]; exact hux⟩
        · refine ⟨u, hu, by rw [hwire_in u]; exact hux,
            v, Finset.mem_filter.2 ⟨Finset.mem_univ v, huv, fun hv' => ?_⟩,
            by rw [hwire_in v]; exact hvx⟩
          rcases lt_trichotomy u v with h | h | h
          · exact h
          · exact absurd h huv.ne
          · exact absurd ⟨hv', h⟩ hvu
      · by_cases huv_lt : u ∈ S ∧ u < v
        · exact ⟨u, huv_lt.1, by rw [hwire_in u]; exact hux,
            v, Finset.mem_filter.2 ⟨Finset.mem_univ v, huv, fun _ => huv_lt.2⟩,
            by rw [hwire_in v]; exact hvx⟩
        · refine ⟨v, hv, by rw [hwire_in v]; exact hvx,
            u, Finset.mem_filter.2 ⟨Finset.mem_univ u, huv.symm, fun hu' => ?_⟩,
            by rw [hwire_in u]; exact hux⟩
          rcases lt_trichotomy v u with h | h | h
          · exact h
          · exact absurd h huv.ne.symm
          · exact absurd ⟨hu', h⟩ huv_lt
  rw [hA_eq, hS_eq]
  apply Bool.eq_iff_iff.2
  simp only [forestFun, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro ((h | h) | h)
    · exact Or.inr h
    · exact Or.inl (Or.inr h)
    · exact Or.inl (Or.inl h)
  · rintro ((h | h) | h)
    · exact Or.inr h
    · exact Or.inl (Or.inr h)
    · exact Or.inl (Or.inl h)

private lemma fanout_ge2_elim {m : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hmin : ∀ s' < C.gates.length, ¬ HasCircuitSize m (circuitFun m C) s')
    (v : Fin m)
    (hnc0 : ∃ x x' : Fin m → Bool,
      circuitFun m C (Function.update x v false) ≠ circuitFun m C (Function.update x' v false))
    (hnc1 : ∃ x x' : Fin m → Bool,
      circuitFun m C (Function.update x v true) ≠ circuitFun m C (Function.update x' v true))
    (h2 : ∃ j₁ j₂ : ℕ, ∃ hj₁ : j₁ < C.gates.length, ∃ hj₂ : j₂ < C.gates.length, j₁ < j₂ ∧
      (v : ℕ) ∈ C.gates[j₁].inputs ∧ (v : ℕ) ∈ C.gates[j₂].inputs) :
    (3 ≤ C.gates.length ∧ HasCircuitSize m (fun x => circuitFun m C (Function.update x v false))
      (C.gates.length - 3)) ∨
    (4 ≤ C.gates.length ∧ HasCircuitSize m (fun x => circuitFun m C (Function.update x v true))
      (C.gates.length - 4)) := by
  have hnc : ∃ x x' : Fin m → Bool, circuitFun m C x ≠ circuitFun m C x' := by
    obtain ⟨x, x', hne⟩ := hnc0
    exact ⟨Function.update x v false, Function.update x' v false, hne⟩
  have hwf := min_gate_wf C hnok hmin hnc
  obtain ⟨j₁, j₂, hj₁, hj₂, hj12, hv₁, hv₂⟩ := h2
  by_cases h3 : ∃ j₃ : ℕ, ∃ hj₃ : j₃ < C.gates.length, j₃ ≠ j₁ ∧ j₃ ≠ j₂ ∧ (v : ℕ) ∈ C.gates[j₃].inputs
  · obtain ⟨j₃, hj₃, h31, h32, hv₃⟩ := h3
    obtain ⟨out, _, hok_acc, hcard, hfun⟩ := elim_var_circuit C hnok v false hnc0
    have hv_st : ∀ j ≤ C.gates.length,
        (elimState m C.gates (initVar m v false, []) j).1.getD (v : ℕ) (Sum.inl false) = Sum.inl false := by
      intro j hj
      rw [elimState_getD_mono m C.gates (initVar m v false, []) 0 j (v : ℕ) _ (Nat.zero_le _) hj (by simp [initVar]),
        elimState_zero, initVar, ofFn_getD_lt _ _ _ v.isLt]
      simp
    have hdrop : ∀ j (hj : j < C.gates.length), (v : ℕ) ∈ C.gates[j].inputs →
        j ∈ elimDropped m C.gates (initVar m v false, []) := fun j hj hvj =>
      mem_elimDropped_of_const m C.gates _ j hj (hnok _ (List.getElem_mem hj)) (v : ℕ) hvj ⟨false, hv_st j (by omega)⟩
    have hsub : ({j₁, j₂, j₃} : Finset ℕ) ⊆ elimDropped m C.gates (initVar m v false, []) := by
      intro x hx; simp at hx
      rcases hx with hx | hx | hx
      · rw [hx]; exact hdrop j₁ hj₁ hv₁
      · rw [hx]; exact hdrop j₂ hj₂ hv₂
      · rw [hx]; exact hdrop j₃ hj₃ hv₃
    have hc3 : ({j₁, j₂, j₃} : Finset ℕ).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp; omega),
          Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
    have hge3 : 3 ≤ (elimDropped m C.gates (initVar m v false, [])).card :=
      hc3 ▸ Finset.card_le_card hsub
    left
    refine ⟨by omega, ⟨_, out⟩, hok_acc, ?_, ?_⟩
    · show (elimPass m C.gates (initVar m v false, [])).2.length ≤ C.gates.length - 3; omega
    · intro x; exact congrFun hfun x
  · by_cases hnot_both_or : C.gates[j₁].op ≠ GateOp.or ∨ C.gates[j₂].op ≠ GateOp.or
    · have hex0 : ∃ j₀ j_o : ℕ, ∃ hj₀ : j₀ < C.gates.length, ∃ hj_o : j_o < C.gates.length,
          j₀ ≠ j_o ∧ (v : ℕ) ∈ C.gates[j₀].inputs ∧ (v : ℕ) ∈ C.gates[j_o].inputs ∧
          (C.gates[j₀].op = GateOp.and ∨ C.gates[j₀].op = GateOp.not) := by
        rcases hnot_both_or with hne | hne
        · have hg1 := (hnok _ (List.getElem_mem hj₁)).1.1
          rcases hg1 with h | h | h
          · exact ⟨j₁, j₂, hj₁, hj₂, by omega, hv₁, hv₂, Or.inl h⟩
          · exact absurd h hne
          · exact ⟨j₁, j₂, hj₁, hj₂, by omega, hv₁, hv₂, Or.inr h⟩
        · have hg2 := (hnok _ (List.getElem_mem hj₂)).1.1
          rcases hg2 with h | h | h
          · exact ⟨j₂, j₁, hj₂, hj₁, by omega, hv₂, hv₁, Or.inl h⟩
          · exact absurd h hne
          · exact ⟨j₂, j₁, hj₂, hj₁, by omega, hv₂, hv₁, Or.inr h⟩
      obtain ⟨j₀, j_o, hj₀, hj_o, hne0, hv₀, hv_o, hop₀⟩ := hex0
      obtain ⟨out, _, hok_acc, hcard, hfun⟩ := elim_var_circuit C hnok v false hnc0
      have hv_st : ∀ j ≤ C.gates.length,
          (elimState m C.gates (initVar m v false, []) j).1.getD (v : ℕ) (Sum.inl false) = Sum.inl false := by
        intro j hj
        rw [elimState_getD_mono m C.gates (initVar m v false, []) 0 j (v : ℕ) _ (Nat.zero_le _) hj (by simp [initVar]),
          elimState_zero, initVar, ofFn_getD_lt _ _ _ v.isLt]
        simp
      have hdrop_v : ∀ j (hj : j < C.gates.length), (v : ℕ) ∈ C.gates[j].inputs →
          j ∈ elimDropped m C.gates (initVar m v false, []) := fun j hj hvj =>
        mem_elimDropped_of_const m C.gates _ j hj (hnok _ (List.getElem_mem hj)) (v : ℕ) hvj ⟨false, hv_st j (by omega)⟩
      have hc_j₀ : ∃ c : Bool,
          (elimState m C.gates (initVar m v false, []) (j₀ + 1)).1.getD (m + j₀) (Sum.inl false) = Sum.inl c := by
        have hget := elimState_getD_at m C.gates (initVar m v false, []) j₀ hj₀
        have hlen_i : (initVar m v false).length = m := by simp [initVar]
        rw [hlen_i] at hget; rw [hget]
        rcases hop₀ with hop | hop
        · rw [hop]
          have hmem : Sum.inl false ∈ (C.gates[j₀].inputs.map fun i =>
              (elimState m C.gates (initVar m v false, []) j₀).1.getD i (Sum.inl false)) :=
            List.mem_map.2 ⟨(v : ℕ), hv₀, hv_st j₀ (by omega)⟩
          have hsim := simplifyGate_and_false (m + (elimState m C.gates (initVar m v false, []) j₀).2.length)
            _ (by simp; exact (hnok _ (List.getElem_mem hj₀)).1.2) hmem
          exact ⟨false, by rw [hsim]⟩
        · obtain ⟨a, _, hins⟩ := (hwf j₀ hj₀).1 hop
          rw [hins] at hv₀; simp at hv₀; subst hv₀
          rw [hop, hins, List.map_singleton, hv_st j₀ (by omega)]
          exact ⟨true, rfl⟩
      have hout_ne : C.output ≠ m + j₀ := by
        intro heq
        obtain ⟨c, hc⟩ := hc_j₀
        have hst : (elimPass m C.gates (initVar m v false, [])).1.getD C.output (Sum.inl false) = Sum.inl c := by
          rw [heq, ← elimState_end,
            elimState_getD_mono m C.gates _ (j₀ + 1) C.gates.length (m + j₀) _ (by omega) le_rfl (by simp [initVar])]
          exact hc
        obtain ⟨x, x', hne⟩ := hnc0
        have hinv1 := elimInv_pass m (List.ofFn x) C.gates _ (initVar m v false, [])
          (fun g hg => (hnok g hg).1) (elimInv_initVar m v false x)
        have hinv2 := elimInv_pass m (List.ofFn x') C.gates _ (initVar m v false, [])
          (fun g hg => (hnok g hg).1) (elimInv_initVar m v false x')
        have e1 := (hinv1.2.2 C.output).2
        have e2 := (hinv2.2.2 C.output).2
        rw [hst] at e1 e2
        exact hne (e1.symm.trans e2)
      obtain ⟨j_c, hj_c, hlt_c, hmem_c⟩ := (min_no_dead C hnok hmin j₀ hj₀).resolve_left hout_ne
      have hjc_ne_jo : j_c ≠ j_o := by
        intro heq; subst heq
        have hgjc := hnok C.gates[j_c] (List.getElem_mem hj_c)
        have hopc : C.gates[j_c].op = GateOp.and ∨ C.gates[j_c].op = GateOp.or := by
          rcases hgjc.1.1 with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · obtain ⟨a, _, hins⟩ := (hwf j_c hj_c).1 h
            rw [hins] at hv_o hmem_c; simp at hv_o hmem_c
            have : (v : ℕ) = m + j₀ := hv_o.trans hmem_c.symm
            omega
        obtain ⟨a, b, ha, hb, _, hinsc⟩ := (hwf j_c hj_c).2 hopc
        have hpair : (a = (v : ℕ) ∧ b = m + j₀) ∨ (a = m + j₀ ∧ b = (v : ℕ)) := by
          rw [hinsc] at hv_o hmem_c; simp at hv_o hmem_c
          rcases hv_o with rfl | rfl <;> rcases hmem_c with h1 | h1
          · exact absurd h1.symm (by omega)
          · exact Or.inl ⟨rfl, h1.symm⟩
          · exact Or.inr ⟨h1.symm, rfl⟩
          · exact absurd h1.symm (by omega)
        rcases hop₀ with hop | hop
        · obtain ⟨u, w, hu, hw, _, hins0⟩ := (hwf j₀ hj₀).2 (Or.inl hop)
          have h0_imp : ∀ x : Fin m → Bool,
              (C.wires (List.ofFn x)).getD (v : ℕ) false = false →
              (C.wires (List.ofFn x)).getD (m + j₀) false = false := by
            intro x hvx
            rw [wire_eval_gate C j₀ hj₀ x, hop, hins0]
            rw [hins0] at hv₀; simp at hv₀
            rcases hv₀ with hvu | hvw
            · rw [← hvu]; simp only [show (v : ℕ) < m + j₀ by omega, hw, ↓reduceIte, hvx, GateOp.eval,
                List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.false_and, Bool.and_true]
            · rw [← hvw]; simp only [hu, show (v : ℕ) < m + j₀ by omega, ↓reduceIte, hvx, GateOp.eval,
                List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.false_and, Bool.and_false, Bool.and_true]
          rcases hopc with hopc | hopc
          · apply min_no_alias C hnok hmin j_c (m + j₀) hj_c (by omega)
            intro x
            rw [wire_eval_gate C j_c hj_c x, hopc, hinsc]
            rcases hpair with ⟨hav, hbj⟩ | ⟨haj, hbv⟩
            · rw [hav, hbj]
              cases hvx : (C.wires (List.ofFn x)).getD (v : ℕ) false
              · simp only [show (v : ℕ) < m + j_c by omega, show m + j₀ < m + j_c by omega,
                  ↓reduceIte, hvx, h0_imp x hvx, GateOp.eval, List.map_cons, List.map_nil,
                  List.all_cons, List.all_nil, id_eq, Bool.false_and]
              · simp only [show (v : ℕ) < m + j_c by omega, show m + j₀ < m + j_c by omega,
                  ↓reduceIte, hvx, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
                  List.all_nil, id_eq, Bool.true_and, Bool.and_true]
            · rw [haj, hbv]
              cases hvx : (C.wires (List.ofFn x)).getD (v : ℕ) false
              · simp only [show (v : ℕ) < m + j_c by omega, show m + j₀ < m + j_c by omega,
                  ↓reduceIte, hvx, h0_imp x hvx, GateOp.eval, List.map_cons, List.map_nil,
                  List.all_cons, List.all_nil, id_eq, Bool.false_and]
              · simp only [show (v : ℕ) < m + j_c by omega, show m + j₀ < m + j_c by omega,
                  ↓reduceIte, hvx, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
                  List.all_nil, id_eq, Bool.true_and, Bool.and_true]
          · apply min_no_alias C hnok hmin j_c (v : ℕ) hj_c (by omega)
            intro x
            rw [wire_eval_gate C j_c hj_c x, hopc, hinsc]
            rcases hpair with ⟨hav, hbj⟩ | ⟨haj, hbv⟩
            · rw [hav, hbj]
              cases hvx : (C.wires (List.ofFn x)).getD (v : ℕ) false
              · simp only [show (v : ℕ) < m + j_c by omega, show m + j₀ < m + j_c by omega,
                  ↓reduceIte, hvx, h0_imp x hvx, GateOp.eval, List.map_cons, List.map_nil,
                  List.any_cons, List.any_nil, id_eq, Bool.false_or]
              · simp only [show (v : ℕ) < m + j_c by omega, show m + j₀ < m + j_c by omega,
                  ↓reduceIte, hvx, GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
                  List.any_nil, id_eq, Bool.true_or]
            · rw [haj, hbv]
              cases hvx : (C.wires (List.ofFn x)).getD (v : ℕ) false
              · simp only [show (v : ℕ) < m + j_c by omega, show m + j₀ < m + j_c by omega,
                  ↓reduceIte, hvx, h0_imp x hvx, GateOp.eval, List.map_cons, List.map_nil,
                  List.any_cons, List.any_nil, id_eq, Bool.false_or]
              · simp only [show (v : ℕ) < m + j_c by omega, show m + j₀ < m + j_c by omega,
                  ↓reduceIte, hvx, GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
                  List.any_nil, id_eq, Bool.true_or, Bool.or_true]
        · obtain ⟨u, _, hins0⟩ := (hwf j₀ hj₀).1 hop
          rw [hins0] at hv₀; simp at hv₀
          have h0_eq : ∀ x : Fin m → Bool,
              (C.wires (List.ofFn x)).getD (m + j₀) false = !(C.wires (List.ofFn x)).getD (v : ℕ) false := by
            intro x
            rw [wire_eval_gate C j₀ hj₀ x, hop, hins0, ← hv₀]
            simp only [show (v : ℕ) < m + j₀ by omega, ↓reduceIte, GateOp.eval, List.map_cons,
              List.map_nil, List.headD_cons]
          rcases hopc with hopc | hopc
          · apply min_no_const C hnok hmin hnc j_c hj_c false
            intro x
            rw [wire_eval_gate C j_c hj_c x, hopc, hinsc]
            rcases hpair with ⟨hav, hbj⟩ | ⟨haj, hbv⟩
            · rw [hav, hbj]; simp only [show (v : ℕ) < m + j_c by omega, show m + j₀ < m + j_c by omega,
                ↓reduceIte, h0_eq x, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
                List.all_nil, id_eq, Bool.and_true, Bool.and_not_self]
            · rw [haj, hbv]; simp only [show (v : ℕ) < m + j_c by omega, show m + j₀ < m + j_c by omega,
                ↓reduceIte, h0_eq x, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
                List.all_nil, id_eq, Bool.and_true, Bool.not_and_self]
          · apply min_no_const C hnok hmin hnc j_c hj_c true
            intro x
            rw [wire_eval_gate C j_c hj_c x, hopc, hinsc]
            rcases hpair with ⟨hav, hbj⟩ | ⟨haj, hbv⟩
            · rw [hav, hbj]; simp only [show (v : ℕ) < m + j_c by omega, show m + j₀ < m + j_c by omega,
                ↓reduceIte, h0_eq x, GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
                List.any_nil, id_eq, Bool.or_false, Bool.or_not_self]
            · rw [haj, hbv]; simp only [show (v : ℕ) < m + j_c by omega, show m + j₀ < m + j_c by omega,
                ↓reduceIte, h0_eq x, GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
                List.any_nil, id_eq, Bool.or_false, Bool.not_or_self]
      have hdrop_c : j_c ∈ elimDropped m C.gates (initVar m v false, []) := by
        apply mem_elimDropped_of_const m C.gates _ j_c hj_c (hnok _ (List.getElem_mem hj_c)) (m + j₀) hmem_c
        obtain ⟨c, hc⟩ := hc_j₀
        refine ⟨c, ?_⟩
        rw [elimState_getD_mono m C.gates _ (j₀ + 1) j_c (m + j₀) _ (by omega) (by omega) (by simp [initVar])]
        exact hc
      have hsub : ({j₀, j_o, j_c} : Finset ℕ) ⊆ elimDropped m C.gates (initVar m v false, []) := by
        intro x hx; simp at hx
        rcases hx with hx | hx | hx
        · rw [hx]; exact hdrop_v j₀ hj₀ hv₀
        · rw [hx]; exact hdrop_v j_o hj_o hv_o
        · rw [hx]; exact hdrop_c
      have hc3 : ({j₀, j_o, j_c} : Finset ℕ).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp; omega),
            Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
      have hge3 : 3 ≤ (elimDropped m C.gates (initVar m v false, [])).card :=
        hc3 ▸ Finset.card_le_card hsub
      left
      refine ⟨by omega, ⟨_, out⟩, hok_acc, ?_, ?_⟩
      · show (elimPass m C.gates (initVar m v false, [])).2.length ≤ C.gates.length - 3; omega
      · intro x; exact congrFun hfun x
    · have hop1 : C.gates[j₁].op = GateOp.or := by
        by_contra h; exact hnot_both_or (Or.inl h)
      have hop2 : C.gates[j₂].op = GateOp.or := by
        by_contra h; exact hnot_both_or (Or.inr h)
      obtain ⟨out, _, hok_acc, hcard, hfun⟩ := elim_var_circuit C hnok v true hnc1
      have hv_st : ∀ j ≤ C.gates.length,
          (elimState m C.gates (initVar m v true, []) j).1.getD (v : ℕ) (Sum.inl false) = Sum.inl true := by
        intro j hj
        rw [elimState_getD_mono m C.gates (initVar m v true, []) 0 j (v : ℕ) _ (Nat.zero_le _) hj (by simp [initVar]),
          elimState_zero, initVar, ofFn_getD_lt _ _ _ v.isLt]
        simp
      have hdrop_v : ∀ j (hj : j < C.gates.length), (v : ℕ) ∈ C.gates[j].inputs →
          j ∈ elimDropped m C.gates (initVar m v true, []) := fun j hj hvj =>
        mem_elimDropped_of_const m C.gates _ j hj (hnok _ (List.getElem_mem hj)) (v : ℕ) hvj ⟨true, hv_st j (by omega)⟩
      have hst_or : ∀ j (hj : j < C.gates.length), C.gates[j].op = GateOp.or → (v : ℕ) ∈ C.gates[j].inputs →
          (elimState m C.gates (initVar m v true, []) (j + 1)).1.getD (m + j) (Sum.inl false) = Sum.inl true := by
        intro j hj hop hvj
        have hget := elimState_getD_at m C.gates (initVar m v true, []) j hj
        have hlen_i : (initVar m v true).length = m := by simp [initVar]
        rw [hlen_i] at hget; rw [hget, hop]
        have hmem : Sum.inl true ∈ (C.gates[j].inputs.map fun i =>
            (elimState m C.gates (initVar m v true, []) j).1.getD i (Sum.inl false)) :=
          List.mem_map.2 ⟨(v : ℕ), hvj, hv_st j (by omega)⟩
        have hsim := simplifyGate_or_true (m + (elimState m C.gates (initVar m v true, []) j).2.length)
          _ (by simp; exact (hnok _ (List.getElem_mem hj)).1.2) hmem
        rw [hsim]
      have hst1 := hst_or j₁ hj₁ hop1 hv₁
      have hst2 := hst_or j₂ hj₂ hop2 hv₂
      have hout_ne_const : ∀ j (hj : j < C.gates.length) (c : Bool),
          (elimState m C.gates (initVar m v true, []) (j + 1)).1.getD (m + j) (Sum.inl false) = Sum.inl c →
          C.output ≠ m + j := by
        intro j hj c hc heq
        have hst : (elimPass m C.gates (initVar m v true, [])).1.getD C.output (Sum.inl false) = Sum.inl c := by
          rw [heq, ← elimState_end,
            elimState_getD_mono m C.gates _ (j + 1) C.gates.length (m + j) _ (by omega) le_rfl (by simp [initVar])]
          exact hc
        obtain ⟨x, x', hne⟩ := hnc1
        have hinv1 := elimInv_pass m (List.ofFn x) C.gates _ (initVar m v true, [])
          (fun g hg => (hnok g hg).1) (elimInv_initVar m v true x)
        have hinv2 := elimInv_pass m (List.ofFn x') C.gates _ (initVar m v true, [])
          (fun g hg => (hnok g hg).1) (elimInv_initVar m v true x')
        have e1 := (hinv1.2.2 C.output).2
        have e2 := (hinv2.2.2 C.output).2
        rw [hst] at e1 e2
        exact hne (e1.symm.trans e2)
      obtain ⟨h₁, hh₁, hlt1, hmem1⟩ := (min_no_dead C hnok hmin j₁ hj₁).resolve_left (hout_ne_const j₁ hj₁ true hst1)
      obtain ⟨h₂, hh₂, hlt2, hmem2⟩ := (min_no_dead C hnok hmin j₂ hj₂).resolve_left (hout_ne_const j₂ hj₂ true hst2)
      have hh1_ne_j2 : h₁ ≠ j₂ := by
        intro heq; subst heq
        obtain ⟨u₁, w₁, hu₁, hw₁, _, hins1⟩ := (hwf j₁ hj₁).2 (Or.inr hop1)
        obtain ⟨u₂, w₂, hu₂, hw₂, _, hins2⟩ := (hwf h₁ hh₁).2 (Or.inr hop2)
        have hpair : (u₂ = (v : ℕ) ∧ w₂ = m + j₁) ∨ (u₂ = m + j₁ ∧ w₂ = (v : ℕ)) := by
          rw [hins2] at hv₂ hmem1; simp at hv₂ hmem1
          rcases hv₂ with rfl | rfl <;> rcases hmem1 with h1 | h1
          · exact absurd h1.symm (by omega)
          · exact Or.inl ⟨rfl, h1.symm⟩
          · exact Or.inr ⟨h1.symm, rfl⟩
          · exact absurd h1.symm (by omega)
        have h1_imp : ∀ x : Fin m → Bool,
            (C.wires (List.ofFn x)).getD (v : ℕ) false = true →
            (C.wires (List.ofFn x)).getD (m + j₁) false = true := by
          intro x hvx
          rw [wire_eval_gate C j₁ hj₁ x, hop1, hins1]
          rw [hins1] at hv₁; simp at hv₁
          rcases hv₁ with hvu | hvw
          · rw [← hvu]; simp only [show (v : ℕ) < m + j₁ by omega, hw₁, ↓reduceIte, hvx, GateOp.eval,
              List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.true_or, Bool.or_false]
          · rw [← hvw]; simp only [hu₁, show (v : ℕ) < m + j₁ by omega, ↓reduceIte, hvx, GateOp.eval,
              List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_true, Bool.true_or, Bool.or_false]
        apply min_no_alias C hnok hmin h₁ (m + j₁) hh₁ (by omega)
        intro x
        rw [wire_eval_gate C h₁ hh₁ x, hop2, hins2]
        rcases hpair with ⟨huv, hwj⟩ | ⟨huj, hwv⟩
        · rw [huv, hwj]
          cases hvx : (C.wires (List.ofFn x)).getD (v : ℕ) false
          · simp only [show (v : ℕ) < m + h₁ by omega, show m + j₁ < m + h₁ by omega,
              ↓reduceIte, hvx, GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
              List.any_nil, id_eq, Bool.false_or, Bool.or_false]
          · simp only [show (v : ℕ) < m + h₁ by omega, show m + j₁ < m + h₁ by omega,
              ↓reduceIte, hvx, h1_imp x hvx, GateOp.eval, List.map_cons, List.map_nil,
              List.any_cons, List.any_nil, id_eq, Bool.true_or]
        · rw [huj, hwv]
          cases hvx : (C.wires (List.ofFn x)).getD (v : ℕ) false
          · simp only [show (v : ℕ) < m + h₁ by omega, show m + j₁ < m + h₁ by omega,
              ↓reduceIte, hvx, GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
              List.any_nil, id_eq, Bool.or_false]
          · simp only [show (v : ℕ) < m + h₁ by omega, show m + j₁ < m + h₁ by omega,
              ↓reduceIte, hvx, h1_imp x hvx, GateOp.eval, List.map_cons, List.map_nil,
              List.any_cons, List.any_nil, id_eq, Bool.true_or, Bool.or_true]
      have hdrop_h1 : h₁ ∈ elimDropped m C.gates (initVar m v true, []) := by
        apply mem_elimDropped_of_const m C.gates _ h₁ hh₁ (hnok _ (List.getElem_mem hh₁)) (m + j₁) hmem1
        refine ⟨true, ?_⟩
        rw [elimState_getD_mono m C.gates _ (j₁ + 1) h₁ (m + j₁) _ (by omega) (by omega) (by simp [initVar])]
        exact hst1
      have hdrop_h2 : h₂ ∈ elimDropped m C.gates (initVar m v true, []) := by
        apply mem_elimDropped_of_const m C.gates _ h₂ hh₂ (hnok _ (List.getElem_mem hh₂)) (m + j₂) hmem2
        refine ⟨true, ?_⟩
        rw [elimState_getD_mono m C.gates _ (j₂ + 1) h₂ (m + j₂) _ (by omega) (by omega) (by simp [initVar])]
        exact hst2
      by_cases hh12 : h₁ ≠ h₂
      · have hsub : ({j₁, j₂, h₁, h₂} : Finset ℕ) ⊆ elimDropped m C.gates (initVar m v true, []) := by
          intro x hx; simp at hx
          rcases hx with hx | hx | hx | hx
          · rw [hx]; exact hdrop_v j₁ hj₁ hv₁
          · rw [hx]; exact hdrop_v j₂ hj₂ hv₂
          · rw [hx]; exact hdrop_h1
          · rw [hx]; exact hdrop_h2
        have hc4 : ({j₁, j₂, h₁, h₂} : Finset ℕ).card = 4 := by
          rw [Finset.card_insert_of_notMem (by simp; omega),
              Finset.card_insert_of_notMem (by simp; omega),
              Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
        have hge4 : 4 ≤ (elimDropped m C.gates (initVar m v true, [])).card :=
          hc4 ▸ Finset.card_le_card hsub
        right
        refine ⟨by omega, ⟨_, out⟩, hok_acc, ?_, ?_⟩
        · show (elimPass m C.gates (initVar m v true, [])).2.length ≤ C.gates.length - 4; omega
        · intro x; exact congrFun hfun x
      · have heq_h : h₁ = h₂ := by omega
        subst heq_h
        have hgh1 := hnok C.gates[h₁] (List.getElem_mem hh₁)
        have hoph : C.gates[h₁].op = GateOp.and ∨ C.gates[h₁].op = GateOp.or := by
          rcases hgh1.1.1 with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · obtain ⟨a, _, hins⟩ := (hwf h₁ hh₁).1 h
            rw [hins] at hmem1 hmem2; simp at hmem1 hmem2
            have : m + j₁ = m + j₂ := hmem1.trans hmem2.symm
            omega
        obtain ⟨a, b, _, _, _, hinsh⟩ := (hwf h₁ hh₁).2 hoph
        have hpair : (a = m + j₁ ∧ b = m + j₂) ∨ (a = m + j₂ ∧ b = m + j₁) := by
          rw [hinsh] at hmem1 hmem2; simp at hmem1 hmem2
          rcases hmem1 with rfl | rfl <;> rcases hmem2 with h1 | h1
          · exact absurd h1.symm (by omega)
          · exact Or.inl ⟨rfl, h1.symm⟩
          · exact Or.inr ⟨h1.symm, rfl⟩
          · exact absurd h1.symm (by omega)
        have hst_h1 : ∃ e : Bool,
            (elimState m C.gates (initVar m v true, []) (h₁ + 1)).1.getD (m + h₁) (Sum.inl false) = Sum.inl e := by
          have hget := elimState_getD_at m C.gates (initVar m v true, []) h₁ hh₁
          have hlen_i : (initVar m v true).length = m := by simp [initVar]
          rw [hlen_i] at hget; rw [hget, hinsh]
          have hs1 : (elimState m C.gates (initVar m v true, []) h₁).1.getD (m + j₁) (Sum.inl false) = Sum.inl true := by
            rw [elimState_getD_mono m C.gates _ (j₁ + 1) h₁ (m + j₁) _ (by omega) (by omega) (by simp [initVar])]
            exact hst1
          have hs2 : (elimState m C.gates (initVar m v true, []) h₁).1.getD (m + j₂) (Sum.inl false) = Sum.inl true := by
            rw [elimState_getD_mono m C.gates _ (j₂ + 1) h₁ (m + j₂) _ (by omega) (by omega) (by simp [initVar])]
            exact hst2
          obtain ⟨e, he⟩ := simplifyGate_both_const C.gates[h₁].op
            (m + (elimState m C.gates (initVar m v true, []) h₁).2.length) true true hoph
          refine ⟨e, ?_⟩
          rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
            simp only [List.map_cons, List.map_nil, hs1, hs2, he]
        obtain ⟨e, he⟩ := hst_h1
        obtain ⟨h₃, hh₃, hlt3, hmem3⟩ := (min_no_dead C hnok hmin h₁ hh₁).resolve_left (hout_ne_const h₁ hh₁ e he)
        have hdrop_h3 : h₃ ∈ elimDropped m C.gates (initVar m v true, []) := by
          apply mem_elimDropped_of_const m C.gates _ h₃ hh₃ (hnok _ (List.getElem_mem hh₃)) (m + h₁) hmem3
          refine ⟨e, ?_⟩
          rw [elimState_getD_mono m C.gates _ (h₁ + 1) h₃ (m + h₁) _ (by omega) (by omega) (by simp [initVar])]
          exact he
        have hsub : ({j₁, j₂, h₁, h₃} : Finset ℕ) ⊆ elimDropped m C.gates (initVar m v true, []) := by
          intro x hx; simp at hx
          rcases hx with hx | hx | hx | hx
          · rw [hx]; exact hdrop_v j₁ hj₁ hv₁
          · rw [hx]; exact hdrop_v j₂ hj₂ hv₂
          · rw [hx]; exact hdrop_h1
          · rw [hx]; exact hdrop_h3
        have hc4 : ({j₁, j₂, h₁, h₃} : Finset ℕ).card = 4 := by
          rw [Finset.card_insert_of_notMem (by simp; omega),
              Finset.card_insert_of_notMem (by simp; omega),
              Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
        have hge4 : 4 ≤ (elimDropped m C.gates (initVar m v true, [])).card :=
          hc4 ▸ Finset.card_le_card hsub
        right
        refine ⟨by omega, ⟨_, out⟩, hok_acc, ?_, ?_⟩
        · show (elimPass m C.gates (initVar m v true, [])).2.length ≤ C.gates.length - 4; omega
        · intro x; exact congrFun hfun x

private lemma not_gate_elim {m : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hmin : ∀ s' < C.gates.length, ¬ HasCircuitSize m (circuitFun m C) s')
    (v : Fin m)
    (hnc0 : ∃ x x' : Fin m → Bool,
      circuitFun m C (Function.update x v false) ≠ circuitFun m C (Function.update x' v false))
    (j_v : ℕ) (hj_v : j_v < C.gates.length)
    (hnot : C.gates[j_v] = ⟨GateOp.not, [(v : ℕ)]⟩) :
    (3 ≤ C.gates.length ∧ HasCircuitSize m (fun x => circuitFun m C (Function.update x v false))
      (C.gates.length - 3)) ∨
    (∃ j_h : ℕ, ∃ hj_h : j_h < C.gates.length, j_v < j_h ∧ C.gates[j_h].op = GateOp.and ∧
      (m + j_v) ∈ C.gates[j_h].inputs ∧
      ∀ j' : ℕ, (hj' : j' < C.gates.length) → (m + j_v) ∈ C.gates[j'].inputs → j' = j_h) := by
  have hnc : ∃ x x' : Fin m → Bool, circuitFun m C x ≠ circuitFun m C x' := by
    obtain ⟨x, x', hne⟩ := hnc0
    exact ⟨Function.update x v false, Function.update x' v false, hne⟩
  have hwf := min_gate_wf C hnok hmin hnc
  obtain ⟨out, _, hok_acc, hcard, hfun⟩ := elim_var_circuit C hnok v false hnc0
  have hv_st : ∀ j ≤ C.gates.length,
      (elimState m C.gates (initVar m v false, []) j).1.getD (v : ℕ) (Sum.inl false) = Sum.inl false := by
    intro j hj
    rw [elimState_getD_mono m C.gates (initVar m v false, []) 0 j (v : ℕ) _ (Nat.zero_le _) hj (by simp [initVar]),
      elimState_zero, initVar, ofFn_getD_lt _ _ _ v.isLt]
    simp
  have hst_jv : (elimState m C.gates (initVar m v false, []) (j_v + 1)).1.getD (m + j_v) (Sum.inl false) = Sum.inl true := by
    have hget := elimState_getD_at m C.gates (initVar m v false, []) j_v hj_v
    have hlen_i : (initVar m v false).length = m := by simp [initVar]
    rw [hlen_i] at hget; rw [hget, hnot]
    simp only [List.map_cons, List.map_nil, hv_st j_v (by omega)]
    rfl
  have hdrop_jv : j_v ∈ elimDropped m C.gates (initVar m v false, []) :=
    mem_elimDropped_of_const m C.gates _ j_v hj_v (hnok _ (List.getElem_mem hj_v)) (v : ℕ)
      (by rw [hnot]; simp) ⟨false, hv_st j_v (by omega)⟩
  have hout_ne_const : ∀ j (hj : j < C.gates.length) (c : Bool),
      (elimState m C.gates (initVar m v false, []) (j + 1)).1.getD (m + j) (Sum.inl false) = Sum.inl c →
      C.output ≠ m + j := by
    intro j hj c hc heq
    have hst : (elimPass m C.gates (initVar m v false, [])).1.getD C.output (Sum.inl false) = Sum.inl c := by
      rw [heq, ← elimState_end,
        elimState_getD_mono m C.gates _ (j + 1) C.gates.length (m + j) _ (by omega) le_rfl (by simp [initVar])]
      exact hc
    obtain ⟨x, x', hne⟩ := hnc0
    have hinv1 := elimInv_pass m (List.ofFn x) C.gates _ (initVar m v false, [])
      (fun g hg => (hnok g hg).1) (elimInv_initVar m v false x)
    have hinv2 := elimInv_pass m (List.ofFn x') C.gates _ (initVar m v false, [])
      (fun g hg => (hnok g hg).1) (elimInv_initVar m v false x')
    have e1 := (hinv1.2.2 C.output).2
    have e2 := (hinv2.2.2 C.output).2
    rw [hst] at e1 e2
    exact hne (e1.symm.trans e2)
  obtain ⟨j_h, hj_h, hlt_h, hmem_h⟩ := (min_no_dead C hnok hmin j_v hj_v).resolve_left (hout_ne_const j_v hj_v true hst_jv)
  have hdrop_h : ∀ j' (hj' : j' < C.gates.length), j_v < j' → (m + j_v) ∈ C.gates[j'].inputs →
      j' ∈ elimDropped m C.gates (initVar m v false, []) := by
    intro j' hj' hlt hmem
    apply mem_elimDropped_of_const m C.gates _ j' hj' (hnok _ (List.getElem_mem hj')) (m + j_v) hmem
    refine ⟨true, ?_⟩
    rw [elimState_getD_mono m C.gates _ (j_v + 1) j' (m + j_v) _ (by omega) (by omega) (by simp [initVar])]
    exact hst_jv
  by_cases h2 : ∃ j_h2 : ℕ, ∃ hj_h2 : j_h2 < C.gates.length, j_h2 ≠ j_h ∧ (m + j_v) ∈ C.gates[j_h2].inputs
  · obtain ⟨j_h2, hj_h2, hne2, hmem2⟩ := h2
    have hlt2 : j_v < j_h2 := by
      have hg2 := (hnok _ (List.getElem_mem hj_h2)).1.1
      rcases hg2 with h | h | h
      · obtain ⟨a, b, ha, hb, _, hins⟩ := (hwf j_h2 hj_h2).2 (Or.inl h)
        rw [hins] at hmem2; simp at hmem2; rcases hmem2 with rfl | rfl <;> omega
      · obtain ⟨a, b, ha, hb, _, hins⟩ := (hwf j_h2 hj_h2).2 (Or.inr h)
        rw [hins] at hmem2; simp at hmem2; rcases hmem2 with rfl | rfl <;> omega
      · obtain ⟨a, ha, hins⟩ := (hwf j_h2 hj_h2).1 h
        rw [hins] at hmem2; simp at hmem2; subst hmem2; omega
    have hsub : ({j_v, j_h, j_h2} : Finset ℕ) ⊆ elimDropped m C.gates (initVar m v false, []) := by
      intro x hx; simp at hx
      rcases hx with hx | hx | hx
      · rw [hx]; exact hdrop_jv
      · rw [hx]; exact hdrop_h j_h hj_h hlt_h hmem_h
      · rw [hx]; exact hdrop_h j_h2 hj_h2 hlt2 hmem2
    have hc3 : ({j_v, j_h, j_h2} : Finset ℕ).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp; omega),
          Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
    have hge3 : 3 ≤ (elimDropped m C.gates (initVar m v false, [])).card :=
      hc3 ▸ Finset.card_le_card hsub
    left
    refine ⟨by omega, ⟨_, out⟩, hok_acc, ?_, ?_⟩
    · show (elimPass m C.gates (initVar m v false, [])).2.length ≤ C.gates.length - 3; omega
    · intro x; exact congrFun hfun x
  · have huniq : ∀ j' : ℕ, (hj' : j' < C.gates.length) → (m + j_v) ∈ C.gates[j'].inputs → j' = j_h := by
      intro j' hj' hmem
      by_contra hne
      exact h2 ⟨j', hj', hne, hmem⟩
    rcases (hnok _ (List.getElem_mem hj_h)).1.1 with hop | hop | hop
    · exact Or.inr ⟨j_h, hj_h, hlt_h, hop, hmem_h, huniq⟩
    · have hst_jh : (elimState m C.gates (initVar m v false, []) (j_h + 1)).1.getD (m + j_h) (Sum.inl false) = Sum.inl true := by
        have hget := elimState_getD_at m C.gates (initVar m v false, []) j_h hj_h
        have hlen_i : (initVar m v false).length = m := by simp [initVar]
        rw [hlen_i] at hget; rw [hget, hop]
        have hs : (elimState m C.gates (initVar m v false, []) j_h).1.getD (m + j_v) (Sum.inl false) = Sum.inl true := by
          rw [elimState_getD_mono m C.gates _ (j_v + 1) j_h (m + j_v) _ (by omega) (by omega) (by simp [initVar])]
          exact hst_jv
        have hmem : Sum.inl true ∈ (C.gates[j_h].inputs.map fun i =>
            (elimState m C.gates (initVar m v false, []) j_h).1.getD i (Sum.inl false)) :=
          List.mem_map.2 ⟨m + j_v, hmem_h, hs⟩
        have hsim := simplifyGate_or_true (m + (elimState m C.gates (initVar m v false, []) j_h).2.length)
          _ (by simp; exact (hnok _ (List.getElem_mem hj_h)).1.2) hmem
        rw [hsim]
      obtain ⟨j_k, hj_k, hlt_k, hmem_k⟩ := (min_no_dead C hnok hmin j_h hj_h).resolve_left (hout_ne_const j_h hj_h true hst_jh)
      have hdrop_k : j_k ∈ elimDropped m C.gates (initVar m v false, []) := by
        apply mem_elimDropped_of_const m C.gates _ j_k hj_k (hnok _ (List.getElem_mem hj_k)) (m + j_h) hmem_k
        refine ⟨true, ?_⟩
        rw [elimState_getD_mono m C.gates _ (j_h + 1) j_k (m + j_h) _ (by omega) (by omega) (by simp [initVar])]
        exact hst_jh
      have hsub : ({j_v, j_h, j_k} : Finset ℕ) ⊆ elimDropped m C.gates (initVar m v false, []) := by
        intro x hx; simp at hx
        rcases hx with hx | hx | hx
        · rw [hx]; exact hdrop_jv
        · rw [hx]; exact hdrop_h j_h hj_h hlt_h hmem_h
        · rw [hx]; exact hdrop_k
      have hc3 : ({j_v, j_h, j_k} : Finset ℕ).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp; omega),
            Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
      have hge3 : 3 ≤ (elimDropped m C.gates (initVar m v false, [])).card :=
        hc3 ▸ Finset.card_le_card hsub
      left
      refine ⟨by omega, ⟨_, out⟩, hok_acc, ?_, ?_⟩
      · show (elimPass m C.gates (initVar m v false, [])).2.length ≤ C.gates.length - 3; omega
      · intro x; exact congrFun hfun x
    · exfalso
      obtain ⟨a, _, hins⟩ := (hwf j_h hj_h).1 hop
      rw [hins] at hmem_h; simp at hmem_h
      apply min_no_alias C hnok hmin j_h (v : ℕ) hj_h (by omega)
      intro x
      have hv_eval : (C.wires (List.ofFn x)).getD (m + j_v) false = !(C.wires (List.ofFn x)).getD (v : ℕ) false := by
        rw [wire_eval_gate C j_v hj_v x, hnot]
        simp only [show (v : ℕ) < m + j_v by omega, ↓reduceIte, GateOp.eval, List.map_cons,
          List.map_nil, List.headD_cons]
      rw [wire_eval_gate C j_h hj_h x, hop, hins, ← hmem_h]
      simp only [show m + j_v < m + j_h by omega, ↓reduceIte, hv_eval, GateOp.eval,
        List.map_cons, List.map_nil, List.headD_cons, Bool.not_not]

set_option maxHeartbeats 1600000 in
private lemma cycle_elim_step {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (g : (Fin k → Bool) → Bool)
    (hg_nc : ∃ y y' : Fin k → Bool, g y ≠ g y')
    (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hfun : circuitFun (n + k) C = forestFun G ∅ g)
    (hmin : ∀ s' < C.gates.length, ¬ HasCircuitSize (n + k) (forestFun G ∅ g) s')
    (hmax : ∀ C' : Circuit, (∀ g ∈ C'.gates, NOkGate g) → C'.gates.length = C.gates.length →
      circuitFun (n + k) C' = forestFun G ∅ g → orAncCount (n + k) C' ≤ orAncCount (n + k) C)
    (p₀ p₁ p₂ p₃ p₄ p₅ p₆ p₇ : Fin n)
    (hne0 : p₀ ≠ p₁ ∧ p₀ ≠ p₂ ∧ p₀ ≠ p₃ ∧ p₀ ≠ p₄ ∧ p₀ ≠ p₅ ∧ p₀ ≠ p₆)
    (hne7 : p₇ ≠ p₁ ∧ p₇ ≠ p₂ ∧ p₇ ≠ p₃ ∧ p₇ ≠ p₄ ∧ p₇ ≠ p₅ ∧ p₇ ≠ p₆)
    (hne16 : p₁ ≠ p₂ ∧ p₁ ≠ p₃ ∧ p₁ ≠ p₄ ∧ p₁ ≠ p₅ ∧ p₁ ≠ p₆ ∧
      p₂ ≠ p₃ ∧ p₂ ≠ p₄ ∧ p₂ ≠ p₅ ∧ p₂ ≠ p₆ ∧
      p₃ ≠ p₄ ∧ p₃ ≠ p₅ ∧ p₃ ≠ p₆ ∧
      p₄ ≠ p₅ ∧ p₄ ≠ p₆ ∧
      p₅ ≠ p₆)
    (hn1 : ∀ w, G.Adj p₁ w ↔ w = p₀ ∨ w = p₂)
    (hn2 : ∀ w, G.Adj p₂ w ↔ w = p₁ ∨ w = p₃)
    (hn3 : ∀ w, G.Adj p₃ w ↔ w = p₂ ∨ w = p₄)
    (hn4 : ∀ w, G.Adj p₄ w ↔ w = p₃ ∨ w = p₅)
    (hn5 : ∀ w, G.Adj p₅ w ↔ w = p₄ ∨ w = p₆)
    (hn6 : ∀ w, G.Adj p₆ w ↔ w = p₅ ∨ w = p₇) :
    ∃ v ∈ ({p₂, p₃, p₄, p₅} : Finset (Fin n)),
      (3 ≤ C.gates.length ∧ HasCircuitSize (n + k)
        (fun x => forestFun G ∅ g (Function.update x (Fin.castAdd k v) false)) (C.gates.length - 3)) ∨
      (4 ≤ C.gates.length ∧ HasCircuitSize (n + k)
        (fun x => forestFun G ∅ g (Function.update x (Fin.castAdd k v) true)) (C.gates.length - 4)) := by
  classical
  set m := n + k with hm
  set U : Finset (Fin n) := {p₂, p₃, p₄, p₅} with hU
  have hminC : ∀ s' < C.gates.length, ¬ HasCircuitSize m (circuitFun m C) s' := by
    rw [hfun]; exact hmin
  have hmaxC : ∀ C' : Circuit, (∀ g ∈ C'.gates, NOkGate g) → C'.gates.length = C.gates.length →
      circuitFun m C' = circuitFun m C → orAncCount m C' ≤ orAncCount m C := by
    rw [hfun]; exact hmax
  have hnc : ∃ x x' : Fin m → Bool, circuitFun m C x ≠ circuitFun m C x' := by
    rw [hfun]; exact forestFun_nonconst G ∅ g hg_nc
  have hwf := min_gate_wf C hnok hminC hnc
  have hwf_lt : ∀ j (hj : j < C.gates.length), ∀ i ∈ C.gates[j].inputs, i < m + j := by
    intro j hj i hi
    rcases (hnok _ (List.getElem_mem hj)).1.1 with hop | hop | hop
    · obtain ⟨a, b, ha, hb, _, hins⟩ := (hwf j hj).2 (Or.inl hop)
      rw [hins] at hi; simp at hi; rcases hi with rfl | rfl <;> omega
    · obtain ⟨a, b, ha, hb, _, hins⟩ := (hwf j hj).2 (Or.inr hop)
      rw [hins] at hi; simp at hi; rcases hi with rfl | rfl <;> omega
    · obtain ⟨a, ha, hins⟩ := (hwf j hj).1 hop
      rw [hins] at hi; simp at hi; subst hi; omega
  have hnc_upd : ∀ (v : Fin n) (b : Bool),
      ∃ x x' : Fin m → Bool,
        circuitFun m C (Function.update x (Fin.castAdd k v) b) ≠
        circuitFun m C (Function.update x' (Fin.castAdd k v) b) := by
    intro v b
    obtain ⟨⟨y₀, hy₀⟩, ⟨y₁, hy₁⟩⟩ := exists_false_true_of_nonconst hg_nc
    refine ⟨Fin.append (fun _ : Fin n => false) y₀, Fin.append (fun _ : Fin n => false) y₁, ?_⟩
    rw [hfun]
    have h0 : forestFun G ∅ g (Function.update (Fin.append (fun _ : Fin n => false) y₀) (Fin.castAdd k v) b) = false := by
      simp only [forestFun, Finset.notMem_empty, false_and, exists_false, false_or]
      have hnat : (fun j : Fin k => Function.update (Fin.append (fun _ : Fin n => false) y₀)
          (Fin.castAdd k v) b (Fin.natAdd n j)) = y₀ := by
        funext j
        rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; simp [Fin.castAdd, Fin.natAdd] at this; omega)]
        exact Fin.append_right _ _ j
      rw [hnat, hy₀]
      have hno : ¬ ∃ a d : Fin n, G.Adj a d ∧
          Function.update (Fin.append (fun _ : Fin n => false) y₀) (Fin.castAdd k v) b (Fin.castAdd k a) = true ∧
          Function.update (Fin.append (fun _ : Fin n => false) y₀) (Fin.castAdd k v) b (Fin.castAdd k d) = true := by
        rintro ⟨a, d, had, ha, hd⟩
        have hav : a = v := by
          by_contra hne
          rw [Function.update_of_ne (fun h => hne (Fin.castAdd_injective n k h)), Fin.append_left] at ha
          simp at ha
        have hdv : d = v := by
          by_contra hne
          rw [Function.update_of_ne (fun h => hne (Fin.castAdd_injective n k h)), Fin.append_left] at hd
          simp at hd
        subst hav; subst hdv; exact G.loopless.irrefl _ had
      simp [hno]
    have h1 : forestFun G ∅ g (Function.update (Fin.append (fun _ : Fin n => false) y₁) (Fin.castAdd k v) b) = true := by
      simp only [forestFun]
      have hnat : (fun j : Fin k => Function.update (Fin.append (fun _ : Fin n => false) y₁)
          (Fin.castAdd k v) b (Fin.natAdd n j)) = y₁ := by
        funext j
        rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; simp [Fin.castAdd, Fin.natAdd] at this; omega)]
        exact Fin.append_right _ _ j
      rw [hnat, hy₁]; simp
    rw [h0, h1]; decide
  have hU_nbr : ∀ v ∈ U, ∃ u ∈ U, G.Adj v u ∧ ∀ w, G.Adj u w → w ∈ U := by
    intro v hv
    simp only [hU, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact ⟨p₃, by simp [hU], (hn2 p₃).2 (Or.inr rfl), fun w hw => by rcases (hn3 w).1 hw with rfl | rfl <;> simp [hU]⟩
    · exact ⟨p₄, by simp [hU], (hn3 p₄).2 (Or.inr rfl), fun w hw => by rcases (hn4 w).1 hw with rfl | rfl <;> simp [hU]⟩
    · exact ⟨p₃, by simp [hU], (hn4 p₃).2 (Or.inl rfl), fun w hw => by rcases (hn3 w).1 hw with rfl | rfl <;> simp [hU]⟩
    · exact ⟨p₄, by simp [hU], (hn5 p₄).2 (Or.inl rfl), fun w hw => by rcases (hn4 w).1 hw with rfl | rfl <;> simp [hU]⟩
  have hU_has_read : ∀ v ∈ U, ∃ j : ℕ, ∃ hj : j < C.gates.length, (v : ℕ) ∈ C.gates[j].inputs := by
    intro v hv
    obtain ⟨u, _, hvu, _⟩ := hU_nbr v hv
    by_contra hno
    have hno' : ∀ g ∈ C.gates, (v : ℕ) ∉ g.inputs := by
      intro g hg hmem
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
      exact hno ⟨j, hj, hmem⟩
    have hout_ne : C.output ≠ (v : ℕ) := by
      intro heq
      obtain ⟨x, x', hne⟩ := hnc_upd v false
      have e1 : circuitFun m C (Function.update x (Fin.castAdd k v) false) = false := by
        show (wiresFrom C.gates (List.ofFn (Function.update x (Fin.castAdd k v) false))).getD C.output false = false
        rw [heq, wiresFrom_getD_lt _ _ _ (by simp; omega), ofFn_getD_lt _ _ _ (by omega)]
        have : (⟨(v : ℕ), by omega⟩ : Fin m) = Fin.castAdd k v := rfl
        rw [this, Function.update_self]
      have e2 : circuitFun m C (Function.update x' (Fin.castAdd k v) false) = false := by
        show (wiresFrom C.gates (List.ofFn (Function.update x' (Fin.castAdd k v) false))).getD C.output false = false
        rw [heq, wiresFrom_getD_lt _ _ _ (by simp; omega), ofFn_getD_lt _ _ _ (by omega)]
        have : (⟨(v : ℕ), by omega⟩ : Fin m) = Fin.castAdd k v := rfl
        rw [this, Function.update_self]
      exact hne (e1.trans e2.symm)
    obtain ⟨x, hdep⟩ := forestFun_dep_edge G g hg_nc v u hvu
    have hag := wiresFrom_agree C.gates {(v : ℕ)}
      (List.ofFn (Function.update x (Fin.castAdd k v) false))
      (List.ofFn (Function.update x (Fin.castAdd k v) true))
      (by simp)
      (by intro w hw; simp at hw; subst hw; simp; omega)
      (by
        intro i hi; simp at hi
        by_cases hlt : i < m
        · have hne' : (⟨i, hlt⟩ : Fin m) ≠ Fin.castAdd k v := by
            intro h; apply hi; exact congrArg Fin.val h
          rw [ofFn_getD_lt _ _ _ hlt, ofFn_getD_lt _ _ _ hlt,
            Function.update_of_ne hne', Function.update_of_ne hne']
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)])
      (by intro g hg i hi hmem; simp at hmem; subst hmem; exact hno' g hg hi)
    have hEq := hag.2 C.output (by simpa using hout_ne)
    have h1 := congrFun hfun (Function.update x (Fin.castAdd k v) false)
    have h2 := congrFun hfun (Function.update x (Fin.castAdd k v) true)
    exact hdep (h1.symm.trans (hEq.trans h2))
  by_cases hge2 : ∃ v ∈ U, ∃ j₁ j₂ : ℕ, ∃ hj₁ : j₁ < C.gates.length, ∃ hj₂ : j₂ < C.gates.length,
      j₁ < j₂ ∧ (v : ℕ) ∈ C.gates[j₁].inputs ∧ (v : ℕ) ∈ C.gates[j₂].inputs
  · obtain ⟨v, hv, j₁, j₂, hj₁, hj₂, hj12, hv₁, hv₂⟩ := hge2
    have hres := fanout_ge2_elim C hnok hminC (Fin.castAdd k v)
      (hnc_upd v false) (hnc_upd v true) ⟨j₁, j₂, hj₁, hj₂, hj12, hv₁, hv₂⟩
    rw [hfun] at hres
    exact ⟨v, hv, hres⟩
  · have hfo1 : ∀ v ∈ U, ∃ j : ℕ, ∃ hj : j < C.gates.length, (v : ℕ) ∈ C.gates[j].inputs ∧
        ∀ j' : ℕ, (hj' : j' < C.gates.length) → (v : ℕ) ∈ C.gates[j'].inputs → j' = j := by
      intro v hv
      obtain ⟨j, hj, hvj⟩ := hU_has_read v hv
      refine ⟨j, hj, hvj, fun j' hj' hvj' => ?_⟩
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact hge2 ⟨v, hv, j', j, hj', hj, hlt, hvj', hvj⟩
      · exact hge2 ⟨v, hv, j, j', hj, hj', hgt, hvj, hvj'⟩
    by_cases hnot_elim : ∃ v ∈ U, 3 ≤ C.gates.length ∧
        HasCircuitSize m (fun x => forestFun G ∅ g (Function.update x (Fin.castAdd k v) false)) (C.gates.length - 3)
    · obtain ⟨v, hv, hs3, hC3⟩ := hnot_elim
      exact ⟨v, hv, Or.inl ⟨hs3, hC3⟩⟩
    · have hlit_spec : ∀ v ∈ U, ∃ (isNot : Bool) (lit b : ℕ) (hb : b < C.gates.length),
          (isNot = false → lit = (v : ℕ) ∧ (C.gates[b].op = GateOp.and ∨ C.gates[b].op = GateOp.or) ∧
            (v : ℕ) ∈ C.gates[b].inputs ∧
            ∀ j' : ℕ, (hj' : j' < C.gates.length) → (v : ℕ) ∈ C.gates[j'].inputs → j' = b) ∧
          (isNot = true → ∃ j_v : ℕ, ∃ hj_v : j_v < C.gates.length, j_v < b ∧
            C.gates[j_v] = ⟨GateOp.not, [(v : ℕ)]⟩ ∧
            (∀ j' : ℕ, (hj' : j' < C.gates.length) → (v : ℕ) ∈ C.gates[j'].inputs → j' = j_v) ∧
            lit = m + j_v ∧ C.gates[b].op = GateOp.and ∧ (m + j_v) ∈ C.gates[b].inputs ∧
            ∀ j' : ℕ, (hj' : j' < C.gates.length) → (m + j_v) ∈ C.gates[j'].inputs → j' = b) := by
        intro v hv
        obtain ⟨j_v, hj_v, hvj, huniq_v⟩ := hfo1 v hv
        rcases (hnok _ (List.getElem_mem hj_v)).1.1 with hop | hop | hop
        · exact ⟨false, (v : ℕ), j_v, hj_v,
            fun _ => ⟨rfl, Or.inl hop, hvj, huniq_v⟩, fun h => by simp at h⟩
        · exact ⟨false, (v : ℕ), j_v, hj_v,
            fun _ => ⟨rfl, Or.inr hop, hvj, huniq_v⟩, fun h => by simp at h⟩
        · obtain ⟨a, _, hins⟩ := (hwf j_v hj_v).1 hop
          rw [hins] at hvj; simp at hvj; subst hvj
          have hg_not : C.gates[j_v] = ⟨GateOp.not, [(v : ℕ)]⟩ := by
            cases hg : C.gates[j_v] with
            | mk op ins =>
              rw [hg] at hop hins; simp at hop hins; subst hop; subst hins; rfl
          rcases not_gate_elim C hnok hminC (Fin.castAdd k v) (hnc_upd v false) j_v hj_v hg_not with hdone | hcont
          · rw [hfun] at hdone
            exact absurd ⟨v, hv, hdone⟩ hnot_elim
          · obtain ⟨j_h, hj_h, hlt_h, hop_h, hmem_h, huniq_h⟩ := hcont
            exact ⟨true, m + j_v, j_h, hj_h, fun h => by simp at h,
              fun _ => ⟨j_v, hj_v, hlt_h, hg_not, huniq_v, rfl, hop_h, hmem_h, huniq_h⟩⟩
      choose isNot lit b hb hspec0 hspec1 using fun v (hv : v ∈ U) => hlit_spec v hv
      have hU_ne : U.Nonempty := ⟨p₂, by simp [hU]⟩
      set Bset : Finset ℕ := U.attach.image (fun v => b v.1 v.2) with hBset
      have hBset_ne : Bset.Nonempty := by
        refine ⟨b p₂ (by simp [hU]), Finset.mem_image.2 ⟨⟨p₂, by simp [hU]⟩, Finset.mem_attach _ _, rfl⟩⟩
      set bmin := Bset.min' hBset_ne with hbmin
      have hbmin_mem : bmin ∈ Bset := Finset.min'_mem Bset hBset_ne
      obtain ⟨⟨v, hv⟩, _, hbv_eq⟩ := Finset.mem_image.1 hbmin_mem
      have hb_min : ∀ w (hw : w ∈ U), b v hv ≤ b w hw := by
        intro w hw
        rw [hbv_eq]
        exact Finset.min'_le Bset (b w hw) (Finset.mem_image.2 ⟨⟨w, hw⟩, Finset.mem_attach _ _, rfl⟩)
      set j_star := b v hv with hj_star
      have hj_star_lt : j_star < C.gates.length := hb v hv
      have hhop_star : C.gates[j_star].op = GateOp.and ∨ C.gates[j_star].op = GateOp.or := by
        cases hni : isNot v hv
        · exact (hspec0 v hv hni).2.1
        · obtain ⟨_, _, _, _, _, _, hop, _, _⟩ := hspec1 v hv hni
          exact Or.inl hop
      have hlit_in_star : lit v hv ∈ C.gates[j_star].inputs := by
        cases hni : isNot v hv
        · rw [(hspec0 v hv hni).1]; exact (hspec0 v hv hni).2.2.1
        · obtain ⟨_, _, _, _, _, hlit, _, hmem, _⟩ := hspec1 v hv hni
          rw [hlit]; exact hmem
      obtain ⟨i₁, i₂, hi₁, hi₂, hi12, hins_star⟩ := (hwf j_star hj_star_lt).2 hhop_star
      have hex_z : ∃ z, z < m + j_star ∧ z ≠ lit v hv ∧
          (C.gates[j_star].inputs = [lit v hv, z] ∨ C.gates[j_star].inputs = [z, lit v hv]) := by
        rw [hins_star] at hlit_in_star; simp at hlit_in_star
        rcases hlit_in_star with h1 | h2
        · exact ⟨i₂, hi₂, by omega, Or.inl (by rw [hins_star, h1])⟩
        · exact ⟨i₁, hi₁, by omega, Or.inr (by rw [hins_star, h2])⟩
      obtain ⟨z, hz_lt, hz_ne_lit, hz_ins⟩ := hex_z
      have hlit_eval : ∀ w (hw : w ∈ U) (x : Fin m → Bool),
          (C.wires (List.ofFn x)).getD (lit w hw) false =
            if isNot w hw then !x (Fin.castAdd k w) else x (Fin.castAdd k w) := by
        intro w hw x
        cases hni : isNot w hw
        · rw [(hspec0 w hw hni).1]
          show (wiresFrom C.gates (List.ofFn x)).getD (w : ℕ) false = x (Fin.castAdd k w)
          rw [wiresFrom_getD_lt _ _ _ (by simp; omega), ofFn_getD_lt _ _ _ (by omega)]; rfl
        · obtain ⟨j_w, hj_w, _, hg_w, _, hlit_w, _, _, _⟩ := hspec1 w hw hni
          rw [hlit_w, wire_eval_gate C j_w hj_w x, hg_w]
          simp only [show (w : ℕ) < m + j_w by omega, ↓reduceIte, GateOp.eval, List.map_cons,
            List.map_nil, List.headD_cons]
          congr 1
          show (wiresFrom C.gates (List.ofFn x)).getD (w : ℕ) false = x (Fin.castAdd k w)
          rw [wiresFrom_getD_lt _ _ _ (by simp; omega), ofFn_getD_lt _ _ _ (by omega)]; rfl
      have hlit_lt_b : ∀ w (hw : w ∈ U), lit w hw < m + b w hw := by
        intro w hw
        cases hni : isNot w hw
        · rw [(hspec0 w hw hni).1]; omega
        · obtain ⟨j_w, _, hlt_w, _, _, hlit_w, _, _, _⟩ := hspec1 w hw hni
          rw [hlit_w]; omega
      have hnot_out_lit : ∀ w (hw : w ∈ U), C.output ≠ (w : ℕ) ∧ C.output ≠ lit w hw := by
        intro w hw
        have hne_w : C.output ≠ (w : ℕ) := by
          intro heq
          obtain ⟨x, x', hne⟩ := hnc_upd w false
          have e1 : circuitFun m C (Function.update x (Fin.castAdd k w) false) = false := by
            show (wiresFrom C.gates (List.ofFn _)).getD C.output false = false
            rw [heq, wiresFrom_getD_lt _ _ _ (by simp; omega), ofFn_getD_lt _ _ _ (by omega)]
            have : (⟨(w : ℕ), by omega⟩ : Fin m) = Fin.castAdd k w := rfl
            rw [this, Function.update_self]
          have e2 : circuitFun m C (Function.update x' (Fin.castAdd k w) false) = false := by
            show (wiresFrom C.gates (List.ofFn _)).getD C.output false = false
            rw [heq, wiresFrom_getD_lt _ _ _ (by simp; omega), ofFn_getD_lt _ _ _ (by omega)]
            have : (⟨(w : ℕ), by omega⟩ : Fin m) = Fin.castAdd k w := rfl
            rw [this, Function.update_self]
          exact hne (e1.trans e2.symm)
        refine ⟨hne_w, ?_⟩
        intro heq
        obtain ⟨x, x', hne⟩ := hnc_upd w false
        have e1 : circuitFun m C (Function.update x (Fin.castAdd k w) false) =
            (if isNot w hw then true else false) := by
          show (C.wires (List.ofFn _)).getD C.output false = _
          rw [heq, hlit_eval w hw, Function.update_self]; simp
        have e2 : circuitFun m C (Function.update x' (Fin.castAdd k w) false) =
            (if isNot w hw then true else false) := by
          show (C.wires (List.ofFn _)).getD C.output false = _
          rw [heq, hlit_eval w hw, Function.update_self]; simp
        exact hne (e1.trans e2.symm)
      have hz_ne_all_lit : ∀ w (hw : w ∈ U), z ≠ (w : ℕ) ∧ z ≠ lit w hw := by
        intro w hw
        have hnot_eq_lit : z ≠ lit w hw := by
          intro heq_z
          have hwv : w ≠ v := by intro h; subst h; exact hz_ne_lit heq_z
          have hbw_eq : b w hw = j_star := by
            cases hni : isNot w hw
            · have hw_in : (w : ℕ) ∈ C.gates[j_star].inputs := by
                rw [← (hspec0 w hw hni).1, ← heq_z]
                rcases hz_ins with h | h <;> rw [h] <;> simp
              exact ((hspec0 w hw hni).2.2.2 j_star hj_star_lt hw_in).symm
            · obtain ⟨j_w, _, _, _, _, hlit_w, _, _, huniq_w⟩ := hspec1 w hw hni
              have hw_in : (m + j_w) ∈ C.gates[j_star].inputs := by
                rw [← hlit_w, ← heq_z]
                rcases hz_ins with h | h <;> rw [h] <;> simp
              exact (huniq_w j_star hj_star_lt hw_in).symm
          have hagree_two : ∀ x₁ x₂ : Fin m → Bool,
              (∀ i : Fin m, i ≠ Fin.castAdd k v → i ≠ Fin.castAdd k w → x₁ i = x₂ i) →
              (C.wires (List.ofFn x₁)).getD (m + j_star) false =
              (C.wires (List.ofFn x₂)).getD (m + j_star) false →
              forestFun G ∅ g x₁ = forestFun G ∅ g x₂ := by
            intro x₁ x₂ hx hjeq
            set B : Set ℕ := {(v : ℕ), (w : ℕ), lit v hv, lit w hw} with hB
            have hB_lt : ∀ u ∈ B, u < m + j_star := by
              intro u hu
              rcases hu with rfl | rfl | rfl | rfl
              · omega
              · omega
              · exact hlit_lt_b v hv
              · rw [← hbw_eq]; exact hlit_lt_b w hw
            have hread_not_B : ∀ j (hj : j < C.gates.length), j ≠ j_star →
                (∀ hni : isNot v hv = true, j ≠ (hspec1 v hv hni).choose) →
                (∀ hni : isNot w hw = true, j ≠ (hspec1 w hw hni).choose) →
                ∀ i ∈ C.gates[j].inputs, i ∉ B := by
              intro j hj hjne hnv hnw i hi hmem
              rcases hmem with rfl | rfl | rfl | rfl
              · cases hni : isNot v hv
                · exact hjne ((hspec0 v hv hni).2.2.2 j hj hi)
                · exact hnv hni ((hspec1 v hv hni).choose_spec.2.2.2.1 j hj hi)
              · cases hni : isNot w hw
                · exact hjne (hbw_eq ▸ (hspec0 w hw hni).2.2.2 j hj hi)
                · exact hnw hni ((hspec1 w hw hni).choose_spec.2.2.2.1 j hj hi)
              · cases hni : isNot v hv
                · rw [(hspec0 v hv hni).1] at hi
                  exact hjne ((hspec0 v hv hni).2.2.2 j hj hi)
                · have hspec := (hspec1 v hv hni).choose_spec
                  rw [hspec.2.2.2.2.1] at hi
                  exact hjne (hspec.2.2.2.2.2.2.2 j hj hi)
              · cases hni : isNot w hw
                · rw [(hspec0 w hw hni).1] at hi
                  exact hjne (hbw_eq ▸ (hspec0 w hw hni).2.2.2 j hj hi)
                · have hspec := (hspec1 w hw hni).choose_spec
                  rw [hspec.2.2.2.2.1] at hi
                  exact hjne (hbw_eq ▸ hspec.2.2.2.2.2.2.2 j hj hi)
            have hstep_all : ∀ t ≤ C.gates.length, ∀ i < m + t, i ∉ B →
                (wiresFrom (C.gates.take t) (List.ofFn x₁)).getD i false =
                (wiresFrom (C.gates.take t) (List.ofFn x₂)).getD i false := by
              intro t
              induction t with
              | zero =>
                intro _ i hi hiB
                simp only [List.take_zero, wiresFrom_nil]
                rw [ofFn_getD_lt _ _ _ hi, ofFn_getD_lt _ _ _ hi]
                apply hx ⟨i, hi⟩
                · intro h; apply hiB; left; exact congrArg Fin.val h
                · intro h; apply hiB; right; left; exact congrArg Fin.val h
              | succ t ih =>
                intro ht i hi hiB
                have htlt : t < C.gates.length := by omega
                have htake : C.gates.take (t + 1) = C.gates.take t ++ [C.gates[t]] := by
                  rw [List.take_add_one, List.getElem?_eq_getElem htlt, Option.toList_some]
                rw [htake, wiresFrom_append, wiresFrom_cons, wiresFrom_nil,
                  wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
                have hl1 : (wiresFrom (C.gates.take t) (List.ofFn x₁)).length = m + t := by
                  rw [wiresFrom_length, List.length_ofFn, List.length_take, Nat.min_eq_left (by omega)]
                have hl2 : (wiresFrom (C.gates.take t) (List.ofFn x₂)).length = m + t := by
                  rw [wiresFrom_length, List.length_ofFn, List.length_take, Nat.min_eq_left (by omega)]
                by_cases hilt : i < m + t
                · rw [getD_snoc_lt _ _ _ _ (by omega), getD_snoc_lt _ _ _ _ (by omega)]
                  exact ih (by omega) i hilt hiB
                · have hieq : i = m + t := by omega
                  subst hieq
                  rw [getD_snoc_eq _ _ _ _ hl1.symm, getD_snoc_eq _ _ _ _ hl2.symm]
                  by_cases hts : t = j_star
                  · have he1 : (C.wires (List.ofFn x₁)).getD (m + t) false =
                        C.gates[t].op.eval (C.gates[t].inputs.map fun idx =>
                          (wiresFrom (C.gates.take t) (List.ofFn x₁)).getD idx false) := by
                      have h := wiresFrom_getD_gate C.gates (List.ofFn x₁) t htlt
                      rw [List.length_ofFn] at h; exact h
                    have he2 : (C.wires (List.ofFn x₂)).getD (m + t) false =
                        C.gates[t].op.eval (C.gates[t].inputs.map fun idx =>
                          (wiresFrom (C.gates.take t) (List.ofFn x₂)).getD idx false) := by
                      have h := wiresFrom_getD_gate C.gates (List.ofFn x₂) t htlt
                      rw [List.length_ofFn] at h; exact h
                    rw [← he1, ← he2, hts]; exact hjeq
                  · have hnv : ∀ hni : isNot v hv = true, t ≠ (hspec1 v hv hni).choose := by
                      intro hni hteq
                      apply hiB; right; right; left
                      rw [hteq, ← (hspec1 v hv hni).choose_spec.2.2.2.2.1]
                    have hnw : ∀ hni : isNot w hw = true, t ≠ (hspec1 w hw hni).choose := by
                      intro hni hteq
                      apply hiB; right; right; right
                      rw [hteq, ← (hspec1 w hw hni).choose_spec.2.2.2.2.1]; rfl
                    congr 1
                    apply List.map_congr_left
                    intro idx hidx
                    exact ih (by omega) idx (hwf_lt t htlt idx hidx)
                      (hread_not_B t htlt hts hnv hnw idx hidx)
            have hout_not_B : C.output ∉ B := by
              rintro (h | h | h | h)
              · exact (hnot_out_lit v hv).1 h
              · exact (hnot_out_lit w hw).1 h
              · exact (hnot_out_lit v hv).2 h
              · exact (hnot_out_lit w hw).2 h
            have hout_lt : C.output < m + C.gates.length := min_output_lt C hnc
            have hEq := hstep_all C.gates.length le_rfl C.output hout_lt hout_not_B
            rw [List.take_length] at hEq
            have h1 := congrFun hfun x₁
            have h2 := congrFun hfun x₂
            exact h1.symm.trans (hEq.trans h2)
          have hjeval : ∀ x : Fin m → Bool,
              (C.wires (List.ofFn x)).getD (m + j_star) false =
                let lv := if isNot v hv then !x (Fin.castAdd k v) else x (Fin.castAdd k v)
                let lw := if isNot w hw then !x (Fin.castAdd k w) else x (Fin.castAdd k w)
                match C.gates[j_star].op with
                | GateOp.and => lv && lw
                | _ => lv || lw := by
            intro x
            rw [wire_eval_gate C j_star hj_star_lt x]
            have hl1 : lit v hv < m + j_star := hlit_lt_b v hv
            have hl2 : lit w hw < m + j_star := by rw [← heq_z]; exact hz_lt
            rcases hhop_star with hop | hop
            · rw [hop]
              rcases hz_ins with h | h <;> rw [h, heq_z]
              · simp only [hl1, hl2, ↓reduceIte, hlit_eval v hv x, hlit_eval w hw x,
                  GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
              · simp only [hl1, hl2, ↓reduceIte, hlit_eval v hv x, hlit_eval w hw x,
                  GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                exact Bool.and_comm _ _
            · rw [hop]
              rcases hz_ins with h | h <;> rw [h, heq_z]
              · simp only [hl1, hl2, ↓reduceIte, hlit_eval v hv x, hlit_eval w hw x,
                  GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
              · simp only [hl1, hl2, ↓reduceIte, hlit_eval v hv x, hlit_eval w hw x,
                  GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                exact Bool.or_comm _ _
          obtain ⟨h12, h13, h14, h15, h16, h23, h24, h25, h26, h34, h35, h36, h45, h46, h56⟩ := hne16
          have hex_priv_w : ∃ w' : Fin n, G.Adj w w' ∧ w' ≠ v ∧ ¬ G.Adj v w' := by
            simp only [hU, Finset.mem_insert, Finset.mem_singleton] at hv hw
            rcases hv with rfl | rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl | rfl
            · exact absurd rfl hwv
            · exact ⟨p₄, (hn3 p₄).2 (Or.inr rfl), h24.symm, by rw [hn2]; push Not; exact ⟨h14.symm, h34.symm⟩⟩
            · exact ⟨p₅, (hn4 p₅).2 (Or.inr rfl), h25.symm, by rw [hn2]; push Not; exact ⟨h15.symm, h35.symm⟩⟩
            · exact ⟨p₆, (hn5 p₆).2 (Or.inr rfl), h26.symm, by rw [hn2]; push Not; exact ⟨h16.symm, h36.symm⟩⟩
            · exact ⟨p₁, (hn2 p₁).2 (Or.inl rfl), h13, by rw [hn3]; push Not; exact ⟨h12, h14⟩⟩
            · exact absurd rfl hwv
            · exact ⟨p₅, (hn4 p₅).2 (Or.inr rfl), h35.symm, by rw [hn3]; push Not; exact ⟨h25.symm, h45.symm⟩⟩
            · exact ⟨p₆, (hn5 p₆).2 (Or.inr rfl), h36.symm, by rw [hn3]; push Not; exact ⟨h26.symm, h46.symm⟩⟩
            · exact ⟨p₁, (hn2 p₁).2 (Or.inl rfl), h14, by rw [hn4]; push Not; exact ⟨h13, h15⟩⟩
            · exact ⟨p₂, (hn3 p₂).2 (Or.inl rfl), h24, by rw [hn4]; push Not; exact ⟨h23, h25⟩⟩
            · exact absurd rfl hwv
            · exact ⟨p₆, (hn5 p₆).2 (Or.inr rfl), h46.symm, by rw [hn4]; push Not; exact ⟨h36.symm, h56.symm⟩⟩
            · exact ⟨p₁, (hn2 p₁).2 (Or.inl rfl), h15, by rw [hn5]; push Not; exact ⟨h14, h16⟩⟩
            · exact ⟨p₂, (hn3 p₂).2 (Or.inl rfl), h25, by rw [hn5]; push Not; exact ⟨h24, h26⟩⟩
            · exact ⟨p₃, (hn4 p₃).2 (Or.inl rfl), h35, by rw [hn5]; push Not; exact ⟨h34, h36⟩⟩
            · exact absurd rfl hwv
          have hex_priv_v : ∃ v' : Fin n, G.Adj v v' ∧ v' ≠ w ∧ ¬ G.Adj w v' := by
            simp only [hU, Finset.mem_insert, Finset.mem_singleton] at hv hw
            rcases hv with rfl | rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl | rfl
            · exact absurd rfl hwv
            · exact ⟨p₁, (hn2 p₁).2 (Or.inl rfl), h13, by rw [hn3]; push Not; exact ⟨h12, h14⟩⟩
            · exact ⟨p₁, (hn2 p₁).2 (Or.inl rfl), h14, by rw [hn4]; push Not; exact ⟨h13, h15⟩⟩
            · exact ⟨p₁, (hn2 p₁).2 (Or.inl rfl), h15, by rw [hn5]; push Not; exact ⟨h14, h16⟩⟩
            · exact ⟨p₄, (hn3 p₄).2 (Or.inr rfl), h24.symm, by rw [hn2]; push Not; exact ⟨h14.symm, h34.symm⟩⟩
            · exact absurd rfl hwv
            · exact ⟨p₂, (hn3 p₂).2 (Or.inl rfl), h24, by rw [hn4]; push Not; exact ⟨h23, h25⟩⟩
            · exact ⟨p₂, (hn3 p₂).2 (Or.inl rfl), h25, by rw [hn5]; push Not; exact ⟨h24, h26⟩⟩
            · exact ⟨p₅, (hn4 p₅).2 (Or.inr rfl), h25.symm, by rw [hn2]; push Not; exact ⟨h15.symm, h35.symm⟩⟩
            · exact ⟨p₅, (hn4 p₅).2 (Or.inr rfl), h35.symm, by rw [hn3]; push Not; exact ⟨h25.symm, h45.symm⟩⟩
            · exact absurd rfl hwv
            · exact ⟨p₃, (hn4 p₃).2 (Or.inl rfl), h35, by rw [hn5]; push Not; exact ⟨h34, h36⟩⟩
            · exact ⟨p₆, (hn5 p₆).2 (Or.inr rfl), h26.symm, by rw [hn2]; push Not; exact ⟨h16.symm, h36.symm⟩⟩
            · exact ⟨p₆, (hn5 p₆).2 (Or.inr rfl), h36.symm, by rw [hn3]; push Not; exact ⟨h26.symm, h46.symm⟩⟩
            · exact ⟨p₆, (hn5 p₆).2 (Or.inr rfl), h46.symm, by rw [hn4]; push Not; exact ⟨h36.symm, h56.symm⟩⟩
            · exact absurd rfl hwv
          obtain ⟨⟨y₀, hy₀⟩, _⟩ := exists_false_true_of_nonconst hg_nc
          obtain ⟨w', hww', hw'v, hvw'⟩ := hex_priv_w
          obtain ⟨v', hvv', hv'w, hwv'⟩ := hex_priv_v
          let mkX (q : Fin n) (bv bw : Bool) : Fin m → Bool :=
            Function.update (Function.update (Fin.append (fun i : Fin n => decide (i = q)) y₀)
              (Fin.castAdd k v) bv) (Fin.castAdd k w) bw
          have hmk_v : ∀ q bv bw, mkX q bv bw (Fin.castAdd k v) = bv := by
            intro q bv bw; dsimp [mkX]
            rw [Function.update_of_ne (fun h => hwv.symm (Fin.castAdd_injective n k h)), Function.update_self]
          have hmk_w : ∀ q bv bw, mkX q bv bw (Fin.castAdd k w) = bw := by
            intro q bv bw; dsimp [mkX]; rw [Function.update_self]
          have hmk_out : ∀ q bv₁ bw₁ bv₂ bw₂ i, i ≠ Fin.castAdd k v → i ≠ Fin.castAdd k w →
              mkX q bv₁ bw₁ i = mkX q bv₂ bw₂ i := by
            intro q bv₁ bw₁ bv₂ bw₂ i hiv hiw; dsimp [mkX]
            rw [Function.update_of_ne hiw, Function.update_of_ne hiv,
              Function.update_of_ne hiw, Function.update_of_ne hiv]
          have hmk_f : ∀ (q : Fin n) (hqv : q ≠ v) (hqw : q ≠ w) (bv bw : Bool),
              forestFun G ∅ g (mkX q bv bw) =
                ((bv && bw && decide (G.Adj v w)) || (bv && decide (G.Adj v q)) || (bw && decide (G.Adj w q))) := by
            intro q hqv hqw bv bw
            simp only [forestFun, Finset.notMem_empty, false_and, exists_false, false_or]
            have hnat : (fun j : Fin k => mkX q bv bw (Fin.natAdd n j)) = y₀ := by
              funext j; dsimp [mkX]
              rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; simp [Fin.castAdd, Fin.natAdd] at this; omega),
                Function.update_of_ne (by intro h; have := congrArg Fin.val h; simp [Fin.castAdd, Fin.natAdd] at this; omega),
                Fin.append_right]
            rw [hnat, hy₀, Bool.or_false]
            apply Bool.eq_iff_iff.2
            simp only [decide_eq_true_eq, Bool.or_eq_true, Bool.and_eq_true]
            have hval : ∀ a : Fin n, mkX q bv bw (Fin.castAdd k a) = true ↔
                (a = v ∧ bv = true) ∨ (a = w ∧ bw = true) ∨ (a = q) := by
              intro a; dsimp [mkX]
              by_cases haw : a = w
              · subst haw; simp [hwv, hqw.symm]
              · rw [Function.update_of_ne (fun h => haw (Fin.castAdd_injective n k h))]
                by_cases hav : a = v
                · subst hav; simp [haw, hqv.symm]
                · rw [Function.update_of_ne (fun h => hav (Fin.castAdd_injective n k h)), Fin.append_left]
                  simp [hav, haw]
            constructor
            · rintro ⟨a, d, had, ha, hd⟩
              rw [hval] at ha hd
              rcases ha with ⟨rfl, hbv⟩ | ⟨rfl, hbw⟩ | rfl <;>
                rcases hd with ⟨rfl, hbv'⟩ | ⟨rfl, hbw'⟩ | rfl
              · exact absurd had (G.loopless.irrefl _)
              · exact Or.inl (Or.inl ⟨⟨hbv, hbw'⟩, had⟩)
              · exact Or.inl (Or.inr ⟨hbv, had⟩)
              · exact Or.inl (Or.inl ⟨⟨hbv', hbw⟩, had.symm⟩)
              · exact absurd had (G.loopless.irrefl _)
              · exact Or.inr ⟨hbw, had⟩
              · exact Or.inl (Or.inr ⟨hbv', had.symm⟩)
              · exact Or.inr ⟨hbw', had.symm⟩
              · exact absurd had (G.loopless.irrefl _)
            · rintro ((⟨⟨hbv, hbw⟩, had⟩ | ⟨hbv, had⟩) | ⟨hbw, had⟩)
              · exact ⟨v, w, had, (hval v).2 (Or.inl ⟨rfl, hbv⟩), (hval w).2 (Or.inr (Or.inl ⟨rfl, hbw⟩))⟩
              · exact ⟨v, q, had, (hval v).2 (Or.inl ⟨rfl, hbv⟩), (hval q).2 (Or.inr (Or.inr rfl))⟩
              · exact ⟨w, q, had, (hval w).2 (Or.inr (Or.inl ⟨rfl, hbw⟩)), (hval q).2 (Or.inr (Or.inr rfl))⟩
          have hcontra_pair : ∀ (q : Fin n) (hqv : q ≠ v) (hqw : q ≠ w) (bv₁ bw₁ bv₂ bw₂ : Bool),
              (C.wires (List.ofFn (mkX q bv₁ bw₁))).getD (m + j_star) false =
              (C.wires (List.ofFn (mkX q bv₂ bw₂))).getD (m + j_star) false →
              forestFun G ∅ g (mkX q bv₁ bw₁) ≠ forestFun G ∅ g (mkX q bv₂ bw₂) → False := by
            intro q hqv hqw bv₁ bw₁ bv₂ bw₂ hjeq hne
            exact hne (hagree_two _ _ (hmk_out q bv₁ bw₁ bv₂ bw₂) hjeq)
          rcases hhop_star with hop | hop
          · cases hnv : isNot v hv <;> cases hnw : isNot w hw
            · apply hcontra_pair w' hw'v hww'.ne.symm false false false true
              · simp only [hjeval, hop, hnv, hnw, hmk_v, hmk_w]; decide
              · rw [hmk_f w' hw'v hww'.ne.symm, hmk_f w' hw'v hww'.ne.symm]; simp [hww', hvw']
            · apply hcontra_pair w' hw'v hww'.ne.symm false false false true
              · simp only [hjeval, hop, hnv, hnw, hmk_v, hmk_w]; decide
              · rw [hmk_f w' hw'v hww'.ne.symm, hmk_f w' hw'v hww'.ne.symm]; simp [hww', hvw']
            · apply hcontra_pair v' hvv'.ne.symm hv'w false false true false
              · simp only [hjeval, hop, hnv, hnw, hmk_v, hmk_w]; decide
              · rw [hmk_f v' hvv'.ne.symm hv'w, hmk_f v' hvv'.ne.symm hv'w]; simp [hvv', hwv']
            · apply hcontra_pair w' hw'v hww'.ne.symm false true true false
              · simp only [hjeval, hop, hnv, hnw, hmk_v, hmk_w]; decide
              · rw [hmk_f w' hw'v hww'.ne.symm, hmk_f w' hw'v hww'.ne.symm]; simp [hww', hvw']
          · cases hnv : isNot v hv <;> cases hnw : isNot w hw
            · apply hcontra_pair w' hw'v hww'.ne.symm false true true false
              · simp only [hjeval, hop, hnv, hnw, hmk_v, hmk_w]; decide
              · rw [hmk_f w' hw'v hww'.ne.symm, hmk_f w' hw'v hww'.ne.symm]; simp [hww', hvw']
            · apply hcontra_pair v' hvv'.ne.symm hv'w false false true false
              · simp only [hjeval, hop, hnv, hnw, hmk_v, hmk_w]; decide
              · rw [hmk_f v' hvv'.ne.symm hv'w, hmk_f v' hvv'.ne.symm hv'w]; simp [hvv', hwv']
            · apply hcontra_pair w' hw'v hww'.ne.symm false false false true
              · simp only [hjeval, hop, hnv, hnw, hmk_v, hmk_w]; decide
              · rw [hmk_f w' hw'v hww'.ne.symm, hmk_f w' hw'v hww'.ne.symm]; simp [hww', hvw']
            · apply hcontra_pair w' hw'v hww'.ne.symm false false false true
              · simp only [hjeval, hop, hnv, hnw, hmk_v, hmk_w]; decide
              · rw [hmk_f w' hw'v hww'.ne.symm, hmk_f w' hw'v hww'.ne.symm]; simp [hww', hvw']
        refine ⟨?_, hnot_eq_lit⟩
        intro heq_w
        cases hni : isNot w hw
        · exact hnot_eq_lit (heq_w.trans (hspec0 w hw hni).1.symm)
        · obtain ⟨j_w, hj_w, _, hg_not_w, huniq_w, _, _, _, _⟩ := hspec1 w hw hni
          have hw_in : (w : ℕ) ∈ C.gates[j_star].inputs := by
            rw [← heq_w]; rcases hz_ins with h | h <;> rw [h] <;> simp
          have hjs_eq : j_star = j_w := huniq_w j_star hj_star_lt hw_in
          have hop_not : C.gates[j_star].op = GateOp.not := by
            have : C.gates[j_star] = C.gates[j_w] := congrArg (fun p : Fin C.gates.length => C.gates[p.1]'p.2)
              (Fin.ext (a := ⟨j_star, hj_star_lt⟩) (b := ⟨j_w, hj_w⟩) hjs_eq)
            rw [this, hg_not_w]
          rcases hhop_star with h | h <;> rw [h] at hop_not <;> simp at hop_not
      have hz_indep : ∀ x₁ x₂ : Fin m → Bool,
          (∀ i : Fin m, (∀ w ∈ U, i ≠ Fin.castAdd k w) → x₁ i = x₂ i) →
          (C.wires (List.ofFn x₁)).getD z false = (C.wires (List.ofFn x₂)).getD z false := by
        intro x₁ x₂ hx
        set BU : Set ℕ := {idx : ℕ | ∃ w ∈ U, idx = (w : ℕ) ∨ ∃ hw : w ∈ U, idx = lit w hw} with hBU
        have hz_not_BU : z ∉ BU := by
          rintro ⟨w, hw, rfl | ⟨hw', rfl⟩⟩
          · exact (hz_ne_all_lit w hw).1 rfl
          · exact (hz_ne_all_lit w hw').2 rfl
        have hstep_pref : ∀ t ≤ j_star, ∀ i < m + t, i ∉ BU →
            (wiresFrom (C.gates.take t) (List.ofFn x₁)).getD i false =
            (wiresFrom (C.gates.take t) (List.ofFn x₂)).getD i false := by
          intro t
          induction t with
          | zero =>
            intro _ i hi hiB
            simp only [List.take_zero, wiresFrom_nil]
            rw [ofFn_getD_lt _ _ _ hi, ofFn_getD_lt _ _ _ hi]
            apply hx ⟨i, hi⟩
            intro w hw hEq
            apply hiB
            exact ⟨w, hw, Or.inl (congrArg Fin.val hEq)⟩
          | succ t ih =>
            intro ht i hi hiB
            have htlt : t < C.gates.length := by omega
            have htake : C.gates.take (t + 1) = C.gates.take t ++ [C.gates[t]] := by
              rw [List.take_add_one, List.getElem?_eq_getElem htlt, Option.toList_some]
            rw [htake, wiresFrom_append, wiresFrom_cons, wiresFrom_nil,
              wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
            have hl1 : (wiresFrom (C.gates.take t) (List.ofFn x₁)).length = m + t := by
              rw [wiresFrom_length, List.length_ofFn, List.length_take, Nat.min_eq_left (by omega)]
            have hl2 : (wiresFrom (C.gates.take t) (List.ofFn x₂)).length = m + t := by
              rw [wiresFrom_length, List.length_ofFn, List.length_take, Nat.min_eq_left (by omega)]
            by_cases hilt : i < m + t
            · rw [getD_snoc_lt _ _ _ _ (by omega), getD_snoc_lt _ _ _ _ (by omega)]
              exact ih (by omega) i hilt hiB
            · have hieq : i = m + t := by omega
              subst hieq
              rw [getD_snoc_eq _ _ _ _ hl1.symm, getD_snoc_eq _ _ _ _ hl2.symm]
              congr 1
              apply List.map_congr_left
              intro idx hidx
              have hidx_not_BU : idx ∉ BU := by
                rintro ⟨w, hw, rfl | ⟨hw', rfl⟩⟩
                · cases hni : isNot w hw
                  · have ht_eq := (hspec0 w hw hni).2.2.2 t htlt hidx
                    have hle := hb_min w hw
                    omega
                  · obtain ⟨j_w, _, _, _, huniq_w, hlit_w, _, _, _⟩ := hspec1 w hw hni
                    have ht_eq := huniq_w t htlt hidx
                    apply hiB
                    exact ⟨w, hw, Or.inr ⟨hw, by rw [hlit_w, ht_eq]⟩⟩
                · cases hni : isNot w hw'
                  · rw [(hspec0 w hw' hni).1] at hidx
                    have ht_eq := (hspec0 w hw' hni).2.2.2 t htlt hidx
                    have hle := hb_min w hw'
                    omega
                  · obtain ⟨j_w, _, _, _, _, hlit_w, _, _, huniq_w⟩ := hspec1 w hw' hni
                    rw [hlit_w] at hidx
                    have ht_eq := huniq_w t htlt hidx
                    have hle := hb_min w hw'
                    omega
              exact ih (by omega) idx (hwf_lt t htlt idx hidx) hidx_not_BU
        have hpref_eq : ∀ x : Fin m → Bool,
            (C.wires (List.ofFn x)).getD z false = (wiresFrom (C.gates.take j_star) (List.ofFn x)).getD z false := by
          intro x
          show (wiresFrom C.gates (List.ofFn x)).getD z false = _
          have hsp : C.gates = C.gates.take j_star ++ C.gates.drop j_star := (List.take_append_drop j_star C.gates).symm
          conv_lhs => rw [hsp, wiresFrom_append]
          exact wiresFrom_getD_lt _ _ _ (by rw [wiresFrom_length, List.length_ofFn, List.length_take, Nat.min_eq_left (by omega)]; exact hz_lt)
        rw [hpref_eq x₁, hpref_eq x₂]
        exact hstep_pref j_star le_rfl z hz_lt hz_not_BU
      have hdep_one_v : ∀ x : Fin m → Bool,
          forestFun G ∅ g (Function.update x (Fin.castAdd k v) false) ≠
          forestFun G ∅ g (Function.update x (Fin.castAdd k v) true) →
          (C.wires (List.ofFn (Function.update x (Fin.castAdd k v) false))).getD (m + j_star) false ≠
          (C.wires (List.ofFn (Function.update x (Fin.castAdd k v) true))).getD (m + j_star) false := by
        intro x hne heqj
        set x₁ := Function.update x (Fin.castAdd k v) false
        set x₂ := Function.update x (Fin.castAdd k v) true
        set Bv : Set ℕ := {(v : ℕ), lit v hv}
        have hstep_v : ∀ t ≤ C.gates.length, ∀ i < m + t, i ∉ Bv →
            (wiresFrom (C.gates.take t) (List.ofFn x₁)).getD i false =
            (wiresFrom (C.gates.take t) (List.ofFn x₂)).getD i false := by
          intro t
          induction t with
          | zero =>
            intro _ i hi hiB
            simp only [List.take_zero, wiresFrom_nil]
            rw [ofFn_getD_lt _ _ _ hi, ofFn_getD_lt _ _ _ hi]
            have hne' : (⟨i, hi⟩ : Fin m) ≠ Fin.castAdd k v := by
              intro h; apply hiB; left; exact congrArg Fin.val h
            dsimp [x₁, x₂]
            rw [Function.update_of_ne hne', Function.update_of_ne hne']
          | succ t ih =>
            intro ht i hi hiB
            have htlt : t < C.gates.length := by omega
            have htake : C.gates.take (t + 1) = C.gates.take t ++ [C.gates[t]] := by
              rw [List.take_add_one, List.getElem?_eq_getElem htlt, Option.toList_some]
            rw [htake, wiresFrom_append, wiresFrom_cons, wiresFrom_nil,
              wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
            have hl1 : (wiresFrom (C.gates.take t) (List.ofFn x₁)).length = m + t := by
              rw [wiresFrom_length, List.length_ofFn, List.length_take, Nat.min_eq_left (by omega)]
            have hl2 : (wiresFrom (C.gates.take t) (List.ofFn x₂)).length = m + t := by
              rw [wiresFrom_length, List.length_ofFn, List.length_take, Nat.min_eq_left (by omega)]
            by_cases hilt : i < m + t
            · rw [getD_snoc_lt _ _ _ _ (by omega), getD_snoc_lt _ _ _ _ (by omega)]
              exact ih (by omega) i hilt hiB
            · have hieq : i = m + t := by omega
              subst hieq
              rw [getD_snoc_eq _ _ _ _ hl1.symm, getD_snoc_eq _ _ _ _ hl2.symm]
              by_cases hts : t = j_star
              · have he1 := wiresFrom_getD_gate C.gates (List.ofFn x₁) t htlt
                have he2 := wiresFrom_getD_gate C.gates (List.ofFn x₂) t htlt
                rw [List.length_ofFn] at he1 he2
                rw [← he1, ← he2, hts]; exact heqj
              · congr 1
                apply List.map_congr_left
                intro idx hidx
                have hidx_not_B : idx ∉ Bv := by
                  rintro (rfl | rfl)
                  · cases hni : isNot v hv
                    · exact hts ((hspec0 v hv hni).2.2.2 t htlt hidx)
                    · obtain ⟨j_v, _, _, _, huniq_v, hlit_v, _, _, _⟩ := hspec1 v hv hni
                      have hteq := huniq_v t htlt hidx
                      apply hiB; right; rw [hlit_v, hteq]; rfl
                  · cases hni : isNot v hv
                    · rw [(hspec0 v hv hni).1] at hidx
                      exact hts ((hspec0 v hv hni).2.2.2 t htlt hidx)
                    · obtain ⟨j_v, _, _, _, _, hlit_v, _, _, huniq_v⟩ := hspec1 v hv hni
                      rw [hlit_v] at hidx
                      exact hts (huniq_v t htlt hidx)
                exact ih (by omega) idx (hwf_lt t htlt idx hidx) hidx_not_B
        have hout_not_B : C.output ∉ Bv := by
          rintro (h | h)
          · exact (hnot_out_lit v hv).1 h
          · exact (hnot_out_lit v hv).2 h
        have hEq := hstep_v C.gates.length le_rfl C.output (min_output_lt C hnc) hout_not_B
        rw [List.take_length] at hEq
        exact hne ((congrFun hfun x₁).symm.trans (hEq.trans (congrFun hfun x₂)))
      obtain ⟨u_star, hu_star, hvu_star, hu_nbr_U⟩ := hU_nbr v hv
      have hzero_U_val : ∀ x : Fin m → Bool,
          let x₀ : Fin m → Bool := fun i =>
            if ∃ w ∈ U, i = Fin.castAdd k w then false else x i
          forestFun G ∅ g x₀ = false →
          (C.gates[j_star].op = GateOp.or → (C.wires (List.ofFn x)).getD z false = false) ∧
          (C.gates[j_star].op = GateOp.and → (C.wires (List.ofFn x)).getD z false = true) := by
        intro x x₀ hx0
        set x' := Function.update x₀ (Fin.castAdd k u_star) true with hx'
        have hvu_ne : u_star ≠ v := hvu_star.ne.symm
        have hf0 : forestFun G ∅ g (Function.update x' (Fin.castAdd k v) false) = false := by
          have hupd_eq : Function.update x' (Fin.castAdd k v) false = x' := by
            funext i
            by_cases hi : i = Fin.castAdd k v
            · subst hi; rw [Function.update_self, hx', Function.update_of_ne (fun h => hvu_ne.symm (Fin.castAdd_injective n k h))]
              simp only [x₀, show ∃ w ∈ U, Fin.castAdd k v = Fin.castAdd k w from ⟨v, hv, rfl⟩, ↓reduceIte]
            · rw [Function.update_of_ne hi]
          rw [hupd_eq]
          simp only [forestFun, Finset.notMem_empty, false_and, exists_false, false_or] at hx0 ⊢
          rw [Bool.or_eq_false_iff] at hx0
          have hnat : (fun j : Fin k => x' (Fin.natAdd n j)) = (fun j : Fin k => x₀ (Fin.natAdd n j)) := by
            funext j; rw [hx', Function.update_of_ne (by intro h; have := congrArg Fin.val h; simp [Fin.castAdd, Fin.natAdd] at this; omega)]
          rw [hnat, hx0.2, Bool.or_false]
          apply decide_eq_false
          rintro ⟨a, d, had, ha, hd⟩
          by_cases hau : a = u_star
          · have had' : G.Adj u_star d := hau ▸ had
            have hdU : d ∈ U := hu_nbr_U d had'
            have hdu : d ≠ u_star := had'.ne.symm
            rw [hx', Function.update_of_ne (fun h => hdu (Fin.castAdd_injective n k h))] at hd
            simp only [x₀, show ∃ w ∈ U, Fin.castAdd k d = Fin.castAdd k w from ⟨d, hdU, rfl⟩, ↓reduceIte] at hd
            simp at hd
          · by_cases hdu : d = u_star
            · have had' : G.Adj u_star a := hdu ▸ had.symm
              have haU : a ∈ U := hu_nbr_U a had'
              rw [hx', Function.update_of_ne (fun h => hau (Fin.castAdd_injective n k h))] at ha
              simp only [x₀, show ∃ w ∈ U, Fin.castAdd k a = Fin.castAdd k w from ⟨a, haU, rfl⟩, ↓reduceIte] at ha
              simp at ha
            · rw [hx', Function.update_of_ne (fun h => hau (Fin.castAdd_injective n k h))] at ha
              rw [hx', Function.update_of_ne (fun h => hdu (Fin.castAdd_injective n k h))] at hd
              have hfalse := of_decide_eq_false hx0.1
              exact hfalse ⟨a, d, had, ha, hd⟩
        have hf1 : forestFun G ∅ g (Function.update x' (Fin.castAdd k v) true) = true := by
          simp only [forestFun, Bool.or_eq_true, decide_eq_true_eq]
          left; right
          refine ⟨v, u_star, hvu_star, by simp, ?_⟩
          rw [Function.update_of_ne (fun h => hvu_ne (Fin.castAdd_injective n k h)), hx', Function.update_self]
        have hdiff := hdep_one_v x' (by rw [hf0, hf1]; decide)
        have hz_eq1 : (C.wires (List.ofFn (Function.update x' (Fin.castAdd k v) false))).getD z false =
            (C.wires (List.ofFn x)).getD z false := by
          apply hz_indep
          intro i hi
          rw [Function.update_of_ne (hi v hv), hx', Function.update_of_ne (hi u_star hu_star)]
          dsimp [x₀]
          exact ite_eq_right_iff.2 (fun h => by rcases h with ⟨w, hw, hEq⟩; exact absurd hEq (hi w hw))
        have hz_eq2 : (C.wires (List.ofFn (Function.update x' (Fin.castAdd k v) true))).getD z false =
            (C.wires (List.ofFn x)).getD z false := by
          apply hz_indep
          intro i hi
          rw [Function.update_of_ne (hi v hv), hx', Function.update_of_ne (hi u_star hu_star)]
          dsimp [x₀]
          exact ite_eq_right_iff.2 (fun h => by rcases h with ⟨w, hw, hEq⟩; exact absurd hEq (hi w hw))
        constructor
        · intro hop
          by_contra hnt
          have hzt : (C.wires (List.ofFn x)).getD z false = true :=
            Bool.eq_true_of_not_eq_false hnt
          apply hdiff
          rw [wire_eval_gate C j_star hj_star_lt, wire_eval_gate C j_star hj_star_lt, hop]
          rcases hz_ins with h | h <;> rw [h]
          · simp only [hlit_lt_b v hv, hz_lt, ↓reduceIte, hz_eq1, hz_eq2, hzt, GateOp.eval,
              List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_true, Bool.true_or, Bool.or_false]
          · simp only [hlit_lt_b v hv, hz_lt, ↓reduceIte, hz_eq1, hz_eq2, hzt, GateOp.eval,
              List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.true_or, Bool.or_false]
        · intro hop
          by_contra hnf
          have hzf : (C.wires (List.ofFn x)).getD z false = false :=
            Bool.eq_false_of_not_eq_true hnf
          apply hdiff
          rw [wire_eval_gate C j_star hj_star_lt, wire_eval_gate C j_star hj_star_lt, hop]
          rcases hz_ins with h | h <;> rw [h]
          · simp only [hlit_lt_b v hv, hz_lt, ↓reduceIte, hz_eq1, hz_eq2, hzf, GateOp.eval,
              List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.false_and, Bool.and_false, Bool.and_true]
          · simp only [hlit_lt_b v hv, hz_lt, ↓reduceIte, hz_eq1, hz_eq2, hzf, GateOp.eval,
              List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.false_and, Bool.and_true]
      rcases hhop_star with hop_and | hop_or
      · have hz_imp : ∀ x : Fin m → Bool,
            (C.wires (List.ofFn x)).getD z false = false → circuitFun m C x = true := by
          intro x hzf
          rw [hfun]
          set x₀ : Fin m → Bool := fun i =>
            if ∃ w ∈ U, i = Fin.castAdd k w then false else x i
          have hx0_t : forestFun G ∅ g x₀ = true := by
            by_contra hnt
            have hx0_f : forestFun G ∅ g x₀ = false := Bool.eq_false_of_not_eq_true hnt
            have hzt := (hzero_U_val x hx0_f).2 hop_and
            rw [hzf] at hzt; simp at hzt
          apply forestFun_mono_left G ∅ g x₀ x _ _ hx0_t
          · intro w hw
            dsimp [x₀] at hw
            by_cases h : ∃ u ∈ U, Fin.castAdd k w = Fin.castAdd k u
            · simp [h] at hw
            · simpa [h] using hw
          · intro j
            dsimp [x₀]
            exact ite_eq_right_iff.2 (fun h => by rcases h with ⟨w, _, h⟩; have := congrArg Fin.val h; simp [Fin.castAdd, Fin.natAdd] at this; omega)
        obtain ⟨⟨y₀, hy₀⟩, _⟩ := exists_false_true_of_nonconst hg_nc
        have hz_nc : ∃ x₁ x₂ : Fin m → Bool,
            (C.wires (List.ofFn x₁)).getD z false = true ∧
            (C.wires (List.ofFn x₂)).getD z false = true ∧
            circuitFun m C x₁ ≠ circuitFun m C x₂ := by
          set x₀ : Fin m → Bool := Fin.append (fun _ : Fin n => false) y₀
          have hx0_f : forestFun G ∅ g x₀ = false := by
            simp only [forestFun, x₀, Fin.append_left, Fin.append_right]; simp [hy₀]
          have hx0_zero : (fun i : Fin m => if ∃ w ∈ U, i = Fin.castAdd k w then false else x₀ i) = x₀ := by
            funext i; split_ifs with h
            · obtain ⟨w, _, rfl⟩ := h; simp [x₀, Fin.append_left]
            · rfl
          have hzt0 : (C.wires (List.ofFn x₀)).getD z false = true :=
            (hzero_U_val x₀ (by rw [hx0_zero]; exact hx0_f)).2 hop_and
          set x₁ : Fin m → Bool := Function.update x₀ (Fin.castAdd k u_star) true
          set x₂ : Fin m → Bool := Function.update x₁ (Fin.castAdd k v) true
          have hzt1 : (C.wires (List.ofFn x₁)).getD z false = true := by
            rw [hz_indep x₁ x₀ (fun i hi => by dsimp [x₁]; rw [Function.update_of_ne (hi u_star hu_star)])]
            exact hzt0
          have hzt2 : (C.wires (List.ofFn x₂)).getD z false = true := by
            rw [hz_indep x₂ x₀ (fun i hi => by dsimp [x₂, x₁]; rw [Function.update_of_ne (hi v hv), Function.update_of_ne (hi u_star hu_star)])]
            exact hzt0
          have hf1 : forestFun G ∅ g x₁ = false := by
            simp only [forestFun, Finset.notMem_empty, false_and, exists_false, false_or]
            have hnat : (fun j : Fin k => x₁ (Fin.natAdd n j)) = y₀ := by
              funext j; dsimp [x₁, x₀]
              rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; simp [Fin.castAdd, Fin.natAdd] at this; omega), Fin.append_right]
            rw [hnat, hy₀, Bool.or_false]
            apply decide_eq_false
            rintro ⟨a, d, had, ha, hd⟩
            have hau : a = u_star := by
              by_contra hne; dsimp [x₁, x₀] at ha
              rw [Function.update_of_ne (fun h => hne (Fin.castAdd_injective n k h)), Fin.append_left] at ha; simp at ha
            have hdu : d = u_star := by
              by_contra hne; dsimp [x₁, x₀] at hd
              rw [Function.update_of_ne (fun h => hne (Fin.castAdd_injective n k h)), Fin.append_left] at hd; simp at hd
            subst hau; subst hdu; exact G.loopless.irrefl _ had
          have hf2 : forestFun G ∅ g x₂ = true := by
            simp only [forestFun, Bool.or_eq_true, decide_eq_true_eq]
            left; right
            refine ⟨v, u_star, hvu_star, by simp [x₂], ?_⟩
            dsimp [x₂, x₁]
            rw [Function.update_of_ne (fun h => hvu_star.ne.symm (Fin.castAdd_injective n k h)), Function.update_self]
          exact ⟨x₁, x₂, hzt1, hzt2, by rw [hfun, hf1, hf2]; decide⟩
        by_cases hz_fo2 : ∃ j' : ℕ, ∃ hj' : j' < C.gates.length, j' ≠ j_star ∧ z ∈ C.gates[j'].inputs
        · obtain ⟨j', hj', hjne, hzj'⟩ := hz_fo2
          have hz_in_star : z ∈ C.gates[j_star].inputs := by
            rcases hz_ins with h | h <;> rw [h] <;> simp
          exfalso
          rcases lt_or_gt_of_ne hjne with hlt | hgt
          · exact rewrite2_contradiction C hnok hminC hmaxC hnc z (by omega) hz_imp hz_nc
              j' j_star hj' hj_star_lt hlt hzj' hz_in_star
          · exact rewrite2_contradiction C hnok hminC hmaxC hnc z (by omega) hz_imp hz_nc
              j_star j' hj_star_lt hj' hgt hz_in_star hzj'
        · have hz_uniq : ∀ j' : ℕ, (hj' : j' < C.gates.length) → z ∈ C.gates[j'].inputs → j' = j_star := by
            intro j' hj' hmem; by_contra hne; exact hz_fo2 ⟨j', hj', hne, hmem⟩
          by_cases hzm : z < m
          · exfalso
            by_cases hzn : z < n
            · set x₀ : Fin m → Bool := Fin.append (fun _ : Fin n => false) y₀
              have hzf : (C.wires (List.ofFn x₀)).getD z false = false := by
                show (wiresFrom C.gates (List.ofFn x₀)).getD z false = false
                rw [wiresFrom_getD_lt _ _ _ (by simp; omega), ofFn_getD_lt _ _ _ hzm]
                have : (⟨z, hzm⟩ : Fin m) = Fin.castAdd k ⟨z, hzn⟩ := rfl
                rw [this]; exact Fin.append_left _ _ _
              have ht := hz_imp x₀ hzf
              rw [hfun] at ht
              simp only [forestFun, x₀, Fin.append_left, Fin.append_right, Finset.notMem_empty,
                false_and, exists_false, false_or, hy₀, Bool.or_false, decide_eq_true_eq] at ht
              obtain ⟨_, _, _, h, _⟩ := ht; simp at h
            · set idx : Fin k := ⟨z - n, by omega⟩
              have hidx_val : (Fin.natAdd n idx : Fin m) = ⟨z, hzm⟩ := by
                ext; simp [idx, Fin.natAdd]; omega
              set x1 : Fin m → Bool :=
                Function.update (Fin.append (fun _ : Fin n => false) y₀) (Fin.castAdd k v) (isNot v hv) with hx1
              have hf1 : forestFun G ∅ g x1 = false := by
                simp only [forestFun, Finset.notMem_empty, false_and, exists_false, false_or]
                have hnat : (fun j : Fin k => x1 (Fin.natAdd n j)) = y₀ := by
                  funext j; dsimp [x1]
                  rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; simp [Fin.castAdd, Fin.natAdd] at this; omega), Fin.append_right]
                rw [hnat, hy₀, Bool.or_false]
                apply decide_eq_false
                rintro ⟨a, d, had, ha, hd⟩
                have hav : a = v := by
                  by_contra hne; dsimp [x1] at ha
                  rw [Function.update_of_ne (fun h => hne (Fin.castAdd_injective n k h)), Fin.append_left] at ha; simp at ha
                have hdv : d = v := by
                  by_contra hne; dsimp [x1] at hd
                  rw [Function.update_of_ne (fun h => hne (Fin.castAdd_injective n k h)), Fin.append_left] at hd; simp at hd
                subst hav; subst hdv; exact G.loopless.irrefl _ had
              set x2 : Fin m → Bool := Function.update x1 (Fin.natAdd n idx) false with hx2
              have hzf2 : (C.wires (List.ofFn x2)).getD z false = false := by
                show (wiresFrom C.gates (List.ofFn x2)).getD z false = false
                rw [wiresFrom_getD_lt _ _ _ (by simp; omega), ofFn_getD_lt _ _ _ hzm, ← hidx_val, hx2, Function.update_self]
              have hf2 : forestFun G ∅ g x2 = true := by
                rw [← hfun]; exact hz_imp x2 hzf2
              have hlit_f : ∀ x : Fin m → Bool, x (Fin.castAdd k v) = isNot v hv →
                  (C.wires (List.ofFn x)).getD (lit v hv) false = false := by
                intro x hxv
                rw [hlit_eval v hv x, hxv]
                cases isNot v hv <;> simp
              have hxv1 : x1 (Fin.castAdd k v) = isNot v hv := by simp [x1]
              have hxv2 : x2 (Fin.castAdd k v) = isNot v hv := by
                rw [hx2, Function.update_of_ne (by intro h; have := congrArg Fin.val h; simp [Fin.castAdd, Fin.natAdd] at this; omega)]
                exact hxv1
              have hjeq : (C.wires (List.ofFn x1)).getD (m + j_star) false =
                  (C.wires (List.ofFn x2)).getD (m + j_star) false := by
                rw [wire_eval_gate C j_star hj_star_lt x1, wire_eval_gate C j_star hj_star_lt x2, hop_and]
                rcases hz_ins with h | h <;>
                  simp only [h, show lit v hv < m + j_star from hlit_lt_b v hv, hz_lt, ↓reduceIte,
                    hlit_f x1 hxv1, hlit_f x2 hxv2, GateOp.eval, List.map_cons, List.map_nil,
                    List.all_cons, List.all_nil, id_eq, Bool.false_and, Bool.and_false, Bool.and_true]
              have hout_ne_z : C.output ≠ z := by
                intro heq
                obtain ⟨a1, a2, hz1, hz2, hne⟩ := hz_nc
                have e1 : circuitFun m C a1 = true := by show (C.wires _).getD C.output false = true; rw [heq]; exact hz1
                have e2 : circuitFun m C a2 = true := by show (C.wires _).getD C.output false = true; rw [heq]; exact hz2
                exact hne (e1.trans e2.symm)
              have hstep_z : ∀ t ≤ C.gates.length, ∀ i < m + t, i ≠ z →
                  (wiresFrom (C.gates.take t) (List.ofFn x1)).getD i false =
                  (wiresFrom (C.gates.take t) (List.ofFn x2)).getD i false := by
                intro t
                induction t with
                | zero =>
                  intro _ i hi hiz
                  simp only [List.take_zero, wiresFrom_nil]
                  rw [ofFn_getD_lt _ _ _ hi, ofFn_getD_lt _ _ _ hi]
                  have hne' : (⟨i, hi⟩ : Fin m) ≠ Fin.natAdd n idx := by
                    intro h; apply hiz; have := congrArg Fin.val h; rw [hidx_val] at this; exact this
                  rw [hx2, Function.update_of_ne hne']
                | succ t ih =>
                  intro ht i hi hiz
                  have htlt : t < C.gates.length := by omega
                  have htake : C.gates.take (t + 1) = C.gates.take t ++ [C.gates[t]] := by
                    rw [List.take_add_one, List.getElem?_eq_getElem htlt, Option.toList_some]
                  rw [htake, wiresFrom_append, wiresFrom_cons, wiresFrom_nil,
                    wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
                  have hl1 : (wiresFrom (C.gates.take t) (List.ofFn x1)).length = m + t := by
                    rw [wiresFrom_length, List.length_ofFn, List.length_take, Nat.min_eq_left (by omega)]
                  have hl2 : (wiresFrom (C.gates.take t) (List.ofFn x2)).length = m + t := by
                    rw [wiresFrom_length, List.length_ofFn, List.length_take, Nat.min_eq_left (by omega)]
                  by_cases hilt : i < m + t
                  · rw [getD_snoc_lt _ _ _ _ (by omega), getD_snoc_lt _ _ _ _ (by omega)]
                    exact ih (by omega) i hilt hiz
                  · have hieq : i = m + t := by omega
                    subst hieq
                    rw [getD_snoc_eq _ _ _ _ hl1.symm, getD_snoc_eq _ _ _ _ hl2.symm]
                    by_cases hts : t = j_star
                    · have he1 := wiresFrom_getD_gate C.gates (List.ofFn x1) t htlt
                      have he2 := wiresFrom_getD_gate C.gates (List.ofFn x2) t htlt
                      rw [List.length_ofFn] at he1 he2
                      rw [← he1, ← he2, hts]; exact hjeq
                    · congr 1
                      apply List.map_congr_left
                      intro idx' hidx'
                      have hne' : idx' ≠ z := fun h => hts (hz_uniq t htlt (h ▸ hidx'))
                      exact ih (by omega) idx' (hwf_lt t htlt idx' hidx') hne'
              have hEq := hstep_z C.gates.length le_rfl C.output (min_output_lt C hnc) hout_ne_z
              rw [List.take_length] at hEq
              have h1 := congrFun hfun x1
              have h2 := congrFun hfun x2
              rw [hf1] at h1; rw [hf2] at h2
              have : false = true := h1.symm.trans (hEq.trans h2)
              simp at this
          · set j_z := z - m with hj_z
            have hz_eq : z = m + j_z := by omega
            have hj_z_lt : j_z < j_star := by omega
            have hout_ne_jz : C.output ≠ m + j_z := by
              intro heq
              obtain ⟨a1, a2, hz1, hz2, hne⟩ := hz_nc
              have e1 : circuitFun m C a1 = true := by show (C.wires _).getD C.output false = true; rw [heq, ← hz_eq]; exact hz1
              have e2 : circuitFun m C a2 = true := by show (C.wires _).getD C.output false = true; rw [heq, ← hz_eq]; exact hz2
              exact hne (e1.trans e2.symm)
            cases hni : isNot v hv
            · obtain ⟨hlit_v, _, hv_in_star, _⟩ := hspec0 v hv hni
              obtain ⟨out, _, hok_acc, hcard, hfun_acc⟩ := elim_var_circuit C hnok (Fin.castAdd k v) false (hnc_upd v false)
              have hv_st : ∀ j ≤ C.gates.length,
                  (elimState m C.gates (initVar m (Fin.castAdd k v) false, []) j).1.getD (v : ℕ) (Sum.inl false) = Sum.inl false := by
                intro j hj
                rw [elimState_getD_mono m C.gates _ 0 j (v : ℕ) _ (Nat.zero_le _) hj (by simp [initVar]; omega),
                  elimState_zero, initVar, ofFn_getD_lt _ _ _ (by omega)]
                have : (⟨(v : ℕ), by omega⟩ : Fin m) = Fin.castAdd k v := rfl
                simp [this]
              have hst_star : (elimState m C.gates (initVar m (Fin.castAdd k v) false, []) (j_star + 1)).1.getD (m + j_star) (Sum.inl false) = Sum.inl false := by
                have hget := elimState_getD_at m C.gates (initVar m (Fin.castAdd k v) false, []) j_star hj_star_lt
                have hlen_i : (initVar m (Fin.castAdd k v) false).length = m := by simp [initVar]
                rw [hlen_i] at hget; rw [hget, hop_and]
                have hmem : Sum.inl false ∈ (C.gates[j_star].inputs.map fun i =>
                    (elimState m C.gates (initVar m (Fin.castAdd k v) false, []) j_star).1.getD i (Sum.inl false)) :=
                  List.mem_map.2 ⟨(v : ℕ), hv_in_star, hv_st j_star (by omega)⟩
                have hsim := simplifyGate_and_false (m + (elimState m C.gates (initVar m (Fin.castAdd k v) false, []) j_star).2.length)
                  _ (by simp; exact (hnok _ (List.getElem_mem hj_star_lt)).1.2) hmem
                rw [hsim]
              have hout_ne_star : C.output ≠ m + j_star := by
                intro heq
                have hst : (elimPass m C.gates (initVar m (Fin.castAdd k v) false, [])).1.getD C.output (Sum.inl false) = Sum.inl false := by
                  rw [heq, ← elimState_end,
                    elimState_getD_mono m C.gates _ (j_star + 1) C.gates.length (m + j_star) _ (by omega) le_rfl (by simp [initVar])]
                  exact hst_star
                obtain ⟨x, x', hne⟩ := hnc_upd v false
                have hinv1 := elimInv_pass m (List.ofFn x) C.gates _ (initVar m (Fin.castAdd k v) false, [])
                  (fun g hg => (hnok g hg).1) (elimInv_initVar m (Fin.castAdd k v) false x)
                have hinv2 := elimInv_pass m (List.ofFn x') C.gates _ (initVar m (Fin.castAdd k v) false, [])
                  (fun g hg => (hnok g hg).1) (elimInv_initVar m (Fin.castAdd k v) false x')
                have e1 := (hinv1.2.2 C.output).2; have e2 := (hinv2.2.2 C.output).2
                rw [hst] at e1 e2; exact hne (e1.symm.trans e2)
              obtain ⟨j_h, hj_h, hlt_h, hmem_h⟩ := (min_no_dead C hnok hminC j_star hj_star_lt).resolve_left hout_ne_star
              have hdrop_star : j_star ∈ elimDropped m C.gates (initVar m (Fin.castAdd k v) false, []) :=
                mem_elimDropped_of_const m C.gates _ j_star hj_star_lt (hnok _ (List.getElem_mem hj_star_lt)) (v : ℕ) hv_in_star ⟨false, hv_st j_star (by omega)⟩
              have hdrop_h : j_h ∈ elimDropped m C.gates (initVar m (Fin.castAdd k v) false, []) := by
                apply mem_elimDropped_of_const m C.gates _ j_h hj_h (hnok _ (List.getElem_mem hj_h)) (m + j_star) hmem_h
                refine ⟨false, ?_⟩
                rw [elimState_getD_mono m C.gates _ (j_star + 1) j_h (m + j_star) _ (by omega) (by omega) (by simp [initVar])]
                exact hst_star
              by_cases hjz_drop : j_z ∈ elimDropped m C.gates (initVar m (Fin.castAdd k v) false, [])
              · have hsub : ({j_z, j_star, j_h} : Finset ℕ) ⊆ elimDropped m C.gates (initVar m (Fin.castAdd k v) false, []) := by
                  intro x hx; simp at hx
                  rcases hx with hx | hx | hx
                  · rw [hx]; exact hjz_drop
                  · rw [hx]; exact hdrop_star
                  · rw [hx]; exact hdrop_h
                have hc3 : ({j_z, j_star, j_h} : Finset ℕ).card = 3 := by
                  rw [Finset.card_insert_of_notMem (by simp; omega),
                      Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
                have hge3 : 3 ≤ (elimDropped m C.gates (initVar m (Fin.castAdd k v) false, [])).card :=
                  hc3 ▸ Finset.card_le_card hsub
                have hcard' : (elimPass m C.gates (initVar m (Fin.castAdd k v) false, [])).2.length +
                    (elimDropped m C.gates (initVar m (Fin.castAdd k v) false, [])).card = C.gates.length := hcard
                refine ⟨v, hv, Or.inl ⟨by omega, ⟨_, out⟩, hok_acc, ?_, ?_⟩⟩
                · show (elimPass m C.gates (initVar m (Fin.castAdd k v) false, [])).2.length ≤ C.gates.length - 3; omega
                · intro x; rw [← hfun]; exact congrFun hfun_acc x
              · have hdead := elim_var_dead_wire C hnok (Fin.castAdd k v) false (hnc_upd v false)
                  j_z j_star (by omega) hj_star_lt hj_z_lt hout_ne_jz
                  (fun j' hj' _ hmem => hz_uniq j' hj' (by rw [hz_eq]; exact hmem))
                  hwf_lt hjz_drop ⟨false, hst_star⟩
                have hsub : ({j_star, j_h} : Finset ℕ) ⊆ elimDropped m C.gates (initVar m (Fin.castAdd k v) false, []) := by
                  intro x hx; simp at hx; rcases hx with hx | hx; (rw [hx]; exact hdrop_star); (rw [hx]; exact hdrop_h)
                have hc2 : ({j_star, j_h} : Finset ℕ).card = 2 := by
                  rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
                have hge2 : 2 ≤ (elimDropped m C.gates (initVar m (Fin.castAdd k v) false, [])).card :=
                  hc2 ▸ Finset.card_le_card hsub
                have h3le : 3 ≤ C.gates.length := by
                  have hkz_lt : 1 ≤ (elimPass m C.gates (initVar m (Fin.castAdd k v) false, [])).2.length := by
                    by_contra h0
                    have heq0 : (elimPass m C.gates (initVar m (Fin.castAdd k v) false, [])).2.length = 0 := by omega
                    have htot := elimPass_card_dropped m C.gates (initVar m (Fin.castAdd k v) false, [])
                    have hsub_all : elimDropped m C.gates (initVar m (Fin.castAdd k v) false, []) ⊆
                        (Finset.range C.gates.length).erase j_z := by
                      intro x hx
                      rw [Finset.mem_erase]
                      refine ⟨fun h => hjz_drop (h ▸ hx), ?_⟩
                      rw [elimDropped, Finset.mem_filter] at hx; exact hx.1
                    have hle := Finset.card_le_card hsub_all
                    rw [Finset.card_erase_of_mem (Finset.mem_range.2 (by omega)), Finset.card_range] at hle
                    simp only [List.length_nil, zero_add] at htot
                    omega
                  have hcard' : (elimPass m C.gates (initVar m (Fin.castAdd k v) false, [])).2.length +
                      (elimDropped m C.gates (initVar m (Fin.castAdd k v) false, [])).card = C.gates.length := hcard
                  omega
                refine ⟨v, hv, Or.inl ⟨h3le, ?_⟩⟩
                rw [hfun] at hdead
                obtain ⟨D, hDok, hDsz, hDev⟩ := hdead
                have hDsz' : D.gates.length ≤ C.gates.length - (elimDropped m C.gates (initVar m (Fin.castAdd k v) false, [])).card - 1 := hDsz
                exact ⟨D, hDok, by show D.gates.length ≤ C.gates.length - 3; omega, hDev⟩
            · obtain ⟨j_v, hj_v, hlt_v, hg_not, _, hlit_v, _, hmem_jv, _⟩ := hspec1 v hv hni
              obtain ⟨out, _, hok_acc, hcard, hfun_acc⟩ := elim_var_circuit C hnok (Fin.castAdd k v) true (hnc_upd v true)
              have hv_st : ∀ j ≤ C.gates.length,
                  (elimState m C.gates (initVar m (Fin.castAdd k v) true, []) j).1.getD (v : ℕ) (Sum.inl false) = Sum.inl true := by
                intro j hj
                rw [elimState_getD_mono m C.gates _ 0 j (v : ℕ) _ (Nat.zero_le _) hj (by simp [initVar]; omega),
                  elimState_zero, initVar, ofFn_getD_lt _ _ _ (by omega)]
                have : (⟨(v : ℕ), by omega⟩ : Fin m) = Fin.castAdd k v := rfl
                simp [this]
              have hst_jv : (elimState m C.gates (initVar m (Fin.castAdd k v) true, []) (j_v + 1)).1.getD (m + j_v) (Sum.inl false) = Sum.inl false := by
                have hget := elimState_getD_at m C.gates (initVar m (Fin.castAdd k v) true, []) j_v hj_v
                have hlen_i : (initVar m (Fin.castAdd k v) true).length = m := by simp [initVar]
                rw [hlen_i] at hget; rw [hget, hg_not]
                simp only [List.map_cons, List.map_nil, hv_st j_v (by omega)]; rfl
              have hst_star : (elimState m C.gates (initVar m (Fin.castAdd k v) true, []) (j_star + 1)).1.getD (m + j_star) (Sum.inl false) = Sum.inl false := by
                have hget := elimState_getD_at m C.gates (initVar m (Fin.castAdd k v) true, []) j_star hj_star_lt
                have hlen_i : (initVar m (Fin.castAdd k v) true).length = m := by simp [initVar]
                rw [hlen_i] at hget; rw [hget, hop_and]
                have hs_jv : (elimState m C.gates (initVar m (Fin.castAdd k v) true, []) j_star).1.getD (m + j_v) (Sum.inl false) = Sum.inl false := by
                  rw [elimState_getD_mono m C.gates _ (j_v + 1) j_star (m + j_v) _ (by omega) (by omega) (by simp [initVar])]
                  exact hst_jv
                have hmem : Sum.inl false ∈ (C.gates[j_star].inputs.map fun i =>
                    (elimState m C.gates (initVar m (Fin.castAdd k v) true, []) j_star).1.getD i (Sum.inl false)) :=
                  List.mem_map.2 ⟨m + j_v, hmem_jv, hs_jv⟩
                have hsim := simplifyGate_and_false (m + (elimState m C.gates (initVar m (Fin.castAdd k v) true, []) j_star).2.length)
                  _ (by simp; exact (hnok _ (List.getElem_mem hj_star_lt)).1.2) hmem
                rw [hsim]
              have hout_ne_star : C.output ≠ m + j_star := by
                intro heq
                have hst : (elimPass m C.gates (initVar m (Fin.castAdd k v) true, [])).1.getD C.output (Sum.inl false) = Sum.inl false := by
                  rw [heq, ← elimState_end,
                    elimState_getD_mono m C.gates _ (j_star + 1) C.gates.length (m + j_star) _ (by omega) le_rfl (by simp [initVar])]
                  exact hst_star
                obtain ⟨x, x', hne⟩ := hnc_upd v true
                have hinv1 := elimInv_pass m (List.ofFn x) C.gates _ (initVar m (Fin.castAdd k v) true, [])
                  (fun g hg => (hnok g hg).1) (elimInv_initVar m (Fin.castAdd k v) true x)
                have hinv2 := elimInv_pass m (List.ofFn x') C.gates _ (initVar m (Fin.castAdd k v) true, [])
                  (fun g hg => (hnok g hg).1) (elimInv_initVar m (Fin.castAdd k v) true x')
                have e1 := (hinv1.2.2 C.output).2; have e2 := (hinv2.2.2 C.output).2
                rw [hst] at e1 e2; exact hne (e1.symm.trans e2)
              obtain ⟨j_h, hj_h, hlt_h, hmem_h⟩ := (min_no_dead C hnok hminC j_star hj_star_lt).resolve_left hout_ne_star
              have hdrop_jv : j_v ∈ elimDropped m C.gates (initVar m (Fin.castAdd k v) true, []) :=
                mem_elimDropped_of_const m C.gates _ j_v hj_v (hnok _ (List.getElem_mem hj_v)) (v : ℕ)
                  (by rw [hg_not]; simp) ⟨true, hv_st j_v (by omega)⟩
              have hdrop_star : j_star ∈ elimDropped m C.gates (initVar m (Fin.castAdd k v) true, []) := by
                apply mem_elimDropped_of_const m C.gates _ j_star hj_star_lt (hnok _ (List.getElem_mem hj_star_lt)) (m + j_v) hmem_jv
                refine ⟨false, ?_⟩
                rw [elimState_getD_mono m C.gates _ (j_v + 1) j_star (m + j_v) _ (by omega) (by omega) (by simp [initVar])]
                exact hst_jv
              have hdrop_h : j_h ∈ elimDropped m C.gates (initVar m (Fin.castAdd k v) true, []) := by
                apply mem_elimDropped_of_const m C.gates _ j_h hj_h (hnok _ (List.getElem_mem hj_h)) (m + j_star) hmem_h
                refine ⟨false, ?_⟩
                rw [elimState_getD_mono m C.gates _ (j_star + 1) j_h (m + j_star) _ (by omega) (by omega) (by simp [initVar])]
                exact hst_star
              have hjz_ne_jv : j_z ≠ j_v := by
                intro h; apply hz_ne_lit; rw [hz_eq, h, hlit_v]
              by_cases hjz_drop : j_z ∈ elimDropped m C.gates (initVar m (Fin.castAdd k v) true, [])
              · have hsub : ({j_z, j_v, j_star, j_h} : Finset ℕ) ⊆ elimDropped m C.gates (initVar m (Fin.castAdd k v) true, []) := by
                  intro x hx; simp at hx
                  rcases hx with hx | hx | hx | hx
                  · rw [hx]; exact hjz_drop
                  · rw [hx]; exact hdrop_jv
                  · rw [hx]; exact hdrop_star
                  · rw [hx]; exact hdrop_h
                have hc4 : ({j_z, j_v, j_star, j_h} : Finset ℕ).card = 4 := by
                  rw [Finset.card_insert_of_notMem (by simp; omega),
                      Finset.card_insert_of_notMem (by simp; omega),
                      Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
                have hge4 : 4 ≤ (elimDropped m C.gates (initVar m (Fin.castAdd k v) true, [])).card :=
                  hc4 ▸ Finset.card_le_card hsub
                have hcard' : (elimPass m C.gates (initVar m (Fin.castAdd k v) true, [])).2.length +
                    (elimDropped m C.gates (initVar m (Fin.castAdd k v) true, [])).card = C.gates.length := hcard
                refine ⟨v, hv, Or.inr ⟨by omega, ⟨_, out⟩, hok_acc, ?_, ?_⟩⟩
                · show (elimPass m C.gates (initVar m (Fin.castAdd k v) true, [])).2.length ≤ C.gates.length - 4; omega
                · intro x; rw [← hfun]; exact congrFun hfun_acc x
              · have hdead := elim_var_dead_wire C hnok (Fin.castAdd k v) true (hnc_upd v true)
                  j_z j_star (by omega) hj_star_lt hj_z_lt hout_ne_jz
                  (fun j' hj' _ hmem => hz_uniq j' hj' (by rw [hz_eq]; exact hmem))
                  hwf_lt hjz_drop ⟨false, hst_star⟩
                have hsub : ({j_v, j_star, j_h} : Finset ℕ) ⊆ elimDropped m C.gates (initVar m (Fin.castAdd k v) true, []) := by
                  intro x hx; simp at hx
                  rcases hx with hx | hx | hx
                  · rw [hx]; exact hdrop_jv
                  · rw [hx]; exact hdrop_star
                  · rw [hx]; exact hdrop_h
                have hc3 : ({j_v, j_star, j_h} : Finset ℕ).card = 3 := by
                  rw [Finset.card_insert_of_notMem (by simp; omega),
                      Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
                have hge3 : 3 ≤ (elimDropped m C.gates (initVar m (Fin.castAdd k v) true, [])).card :=
                  hc3 ▸ Finset.card_le_card hsub
                have h4le : 4 ≤ C.gates.length := by
                  have hkz_lt : 1 ≤ (elimPass m C.gates (initVar m (Fin.castAdd k v) true, [])).2.length := by
                    by_contra h0
                    have heq0 : (elimPass m C.gates (initVar m (Fin.castAdd k v) true, [])).2.length = 0 := by omega
                    have htot := elimPass_card_dropped m C.gates (initVar m (Fin.castAdd k v) true, [])
                    have hsub_all : elimDropped m C.gates (initVar m (Fin.castAdd k v) true, []) ⊆
                        (Finset.range C.gates.length).erase j_z := by
                      intro x hx
                      rw [Finset.mem_erase]
                      refine ⟨fun h => hjz_drop (h ▸ hx), ?_⟩
                      rw [elimDropped, Finset.mem_filter] at hx; exact hx.1
                    have hle := Finset.card_le_card hsub_all
                    rw [Finset.card_erase_of_mem (Finset.mem_range.2 (by omega)), Finset.card_range] at hle
                    simp only [List.length_nil, zero_add] at htot
                    omega
                  have hcard' : (elimPass m C.gates (initVar m (Fin.castAdd k v) true, [])).2.length +
                      (elimDropped m C.gates (initVar m (Fin.castAdd k v) true, [])).card = C.gates.length := hcard
                  omega
                refine ⟨v, hv, Or.inr ⟨h4le, ?_⟩⟩
                rw [hfun] at hdead
                obtain ⟨D, hDok, hDsz, hDev⟩ := hdead
                have hDsz' : D.gates.length ≤ C.gates.length - (elimDropped m C.gates (initVar m (Fin.castAdd k v) true, [])).card - 1 := hDsz
                exact ⟨D, hDok, by show D.gates.length ≤ C.gates.length - 4; omega, hDev⟩
      · exfalso
        have hnot_isNot : isNot v hv = false := by
          cases hni : isNot v hv
          · rfl
          · obtain ⟨_, _, _, _, _, _, hop, _, _⟩ := hspec1 v hv hni
            rw [hop] at hop_or; simp at hop_or
        have hlit_v : lit v hv = (v : ℕ) := (hspec0 v hv hnot_isNot).1
        have hz_imp : ∀ x : Fin m → Bool,
            (C.wires (List.ofFn x)).getD z false = true → circuitFun m C x = true := by
          intro x hzt
          rw [hfun]
          set x₀ : Fin m → Bool := fun i =>
            if ∃ w ∈ U, i = Fin.castAdd k w then false else x i
          have hx0_t : forestFun G ∅ g x₀ = true := by
            by_contra hnt
            have hx0_f : forestFun G ∅ g x₀ = false := Bool.eq_false_of_not_eq_true hnt
            have hzf := (hzero_U_val x hx0_f).1 hop_or
            rw [hzt] at hzf; simp at hzf
          apply forestFun_mono_left G ∅ g x₀ x _ _ hx0_t
          · intro w hw
            dsimp [x₀] at hw
            by_cases h : ∃ u ∈ U, Fin.castAdd k w = Fin.castAdd k u
            · simp [h] at hw
            · simpa [h] using hw
          · intro j
            dsimp [x₀]
            exact ite_eq_right_iff.2 (fun h => by rcases h with ⟨w, _, h⟩; have := congrArg Fin.val h; simp [Fin.castAdd, Fin.natAdd] at this; omega)
        obtain ⟨⟨y₀, hy₀⟩, _⟩ := exists_false_true_of_nonconst hg_nc
        have ha_not : ∃ x : Fin m → Bool, (C.wires (List.ofFn x)).getD (v : ℕ) false = true ∧ circuitFun m C x = false := by
          set x1 : Fin m → Bool := Function.update (Fin.append (fun _ : Fin n => false) y₀) (Fin.castAdd k v) true
          refine ⟨x1, ?_, ?_⟩
          · show (wiresFrom C.gates (List.ofFn x1)).getD (v : ℕ) false = true
            rw [wiresFrom_getD_lt _ _ _ (by simp; omega), ofFn_getD_lt _ _ _ (by omega)]
            have : (⟨(v : ℕ), by omega⟩ : Fin m) = Fin.castAdd k v := rfl
            rw [this]; simp [x1]
          · rw [hfun]
            simp only [forestFun, Finset.notMem_empty, false_and, exists_false, false_or]
            have hnat : (fun j : Fin k => x1 (Fin.natAdd n j)) = y₀ := by
              funext j; dsimp [x1]
              rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; simp [Fin.castAdd, Fin.natAdd] at this; omega), Fin.append_right]
            rw [hnat, hy₀, Bool.or_false]
            apply decide_eq_false
            rintro ⟨a, d, had, ha, hd⟩
            have hav : a = v := by
              by_contra hne; dsimp [x1] at ha
              rw [Function.update_of_ne (fun h => hne (Fin.castAdd_injective n k h)), Fin.append_left] at ha; simp at ha
            have hdv : d = v := by
              by_contra hne; dsimp [x1] at hd
              rw [Function.update_of_ne (fun h => hne (Fin.castAdd_injective n k h)), Fin.append_left] at hd; simp at hd
            subst hav; subst hdv; exact G.loopless.irrefl _ had
        have hg_or : C.gates[j_star] = ⟨GateOp.or, [(v : ℕ), z]⟩ ∨ C.gates[j_star] = ⟨GateOp.or, [z, (v : ℕ)]⟩ := by
          rw [hlit_v] at hz_ins
          cases hg : C.gates[j_star] with
          | mk op ins =>
            rw [hg] at hop_or hz_ins; simp at hop_or hz_ins; subst hop_or
            rcases hz_ins with rfl | rfl
            · exact Or.inl rfl
            · exact Or.inr rfl
        exact rewrite1_contradiction C hnok hmaxC hnc j_star (v : ℕ) z hj_star_lt (by omega) hz_lt
          hg_or hz_imp ha_not

private lemma lower_bound_aux {k c : ℕ} {g : (Fin k → Bool) → Bool}
    (hg_nc : ∃ y y' : Fin k → Bool, g y ≠ g y')
    (hg_sz : ∀ r : ℕ, HasCircuitSize k g r ↔ c ≤ r) :
    ∀ (s : ℕ) {n t : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)),
      Girth7 G →
      Branch7 G →
      (∀ a ∈ A, ∀ v : Fin n, ¬ G.Adj a v) →
      HasMinVC G t →
      HasCircuitSize (n + k) (forestFun G A g) s →
      A.card + G.edgeFinset.card + t + c ≤ s := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro n t G _ A hG hB hA_iso hvc hC
    by_cases hAne : A.Nonempty
    · obtain ⟨a, ha⟩ := hAne
      have hdep := forestFun_dep_A G A g hg_nc a ha
      have hrew := forestFun_update_A G A g a (hA_iso a ha)
      have hnc : ∃ x x',
          forestFun G A g (Function.update x (Fin.castAdd k a) false) ≠
          forestFun G A g (Function.update x' (Fin.castAdd k a) false) := by
        simpa only [← congrFun hrew] using forestFun_nonconst G (A.erase a) g hg_nc
      obtain ⟨hs1, hC'⟩ := elim_one_var (Fin.castAdd k a) false hC hdep hnc
      rw [hrew] at hC'
      have hih := ih (s - 1) (by omega) G (A.erase a) hG hB
        (fun b hb => hA_iso b (Finset.mem_of_mem_erase hb)) hvc hC'
      have hcard : (A.erase a).card + 1 = A.card := by
        have hpos : 1 ≤ A.card := Finset.one_le_card.2 ⟨a, ha⟩
        rw [Finset.card_erase_of_mem ha]; omega
      omega
    · have hAempty : A = ∅ := Finset.not_nonempty_iff_eq_empty.1 hAne
      subst hAempty
      by_cases hAcyc : G.IsAcyclic
      · exact lower_bound_acyclic hg_nc hg_sz s G ∅ hAcyc (by simp) hvc hC
      · by_cases hsmaller : ∃ s' < s, HasCircuitSize (n + k) (forestFun G ∅ g) s'
        · obtain ⟨s', hlt, hC'⟩ := hsmaller
          have hih := ih s' hlt G ∅ hG hB (by simp) hvc hC'
          omega
        · have hmin : ∀ s' < s, ¬ HasCircuitSize (n + k) (forestFun G ∅ g) s' :=
            fun s' hlt h => hsmaller ⟨s', hlt, h⟩
          classical
          have hex_norm : ∃ C : Circuit, (∀ g ∈ C.gates, NOkGate g) ∧ C.gates.length = s ∧
              circuitFun (n + k) C = forestFun G ∅ g := by
            obtain ⟨C0, hok0, hsz0, hev0⟩ := hC
            have hlen0 : C0.gates.length = s := by
              by_contra hne
              have hlt : C0.gates.length < s := by
                have : C0.gates.length ≤ s := hsz0; omega
              exact hmin C0.gates.length hlt ⟨C0, hok0, le_rfl, hev0⟩
            refine ⟨⟨C0.gates.map normGate, C0.output⟩, ?_, by simp [hlen0], ?_⟩
            · intro g hg
              obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
              exact normGate_nok g0 (hok0 g0 hg0)
            · funext x
              show (wiresFrom (C0.gates.map normGate) (List.ofFn x)).getD C0.output false = _
              rw [wiresFrom_norm]
              exact hev0 x
          set R : Finset ℕ := (Finset.range (s + 1)).filter (fun r =>
            ∃ C : Circuit, (∀ g ∈ C.gates, NOkGate g) ∧ C.gates.length = s ∧
              circuitFun (n + k) C = forestFun G ∅ g ∧ orAncCount (n + k) C = r) with hR
          have hR_ne : R.Nonempty := by
            obtain ⟨C0, hnok0, hlen0, hfun0⟩ := hex_norm
            refine ⟨orAncCount (n + k) C0, Finset.mem_filter.2 ⟨Finset.mem_range.2 ?_, C0, hnok0, hlen0, hfun0, rfl⟩⟩
            have := orAncCount_le (n + k) C0
            omega
          set rmax := R.max' hR_ne with hrmax
          obtain ⟨_, C, hnok, hlenC, hfunC, hrc⟩ := Finset.mem_filter.1 (Finset.max'_mem R hR_ne)
          have hmax : ∀ C' : Circuit, (∀ g ∈ C'.gates, NOkGate g) → C'.gates.length = C.gates.length →
              circuitFun (n + k) C' = forestFun G ∅ g → orAncCount (n + k) C' ≤ orAncCount (n + k) C := by
            intro C' hnok' hlen' hfun'
            have hmem : orAncCount (n + k) C' ∈ R := by
              rw [hR, Finset.mem_filter, Finset.mem_range]
              have hle := orAncCount_le (n + k) C'
              exact ⟨by omega, C', hnok', by omega, hfun', rfl⟩
            rw [hrc]
            exact Finset.le_max' R _ hmem
          obtain ⟨p₀, p₁, p₂, p₃, p₄, p₅, p₆, p₇, hne0, hne7, hne16, hn1, hn2, hn3, hn4, hn5, hn6⟩ :=
            cycle_deg2_path G hAcyc hG hB
          have hminC : ∀ s' < C.gates.length, ¬ HasCircuitSize (n + k) (forestFun G ∅ g) s' := by
            rw [hlenC]; exact hmin
          obtain ⟨v, hv, hstep⟩ := cycle_elim_step G g hg_nc C hnok hfunC hminC hmax
            p₀ p₁ p₂ p₃ p₄ p₅ p₆ p₇ hne0 hne7 hne16 hn1 hn2 hn3 hn4 hn5 hn6
          obtain ⟨h12, h13, h14, h15, h16, h23, h24, h25, h26, h34, h35, h36, h45, h46, h56⟩ := hne16
          have hv_local : ∃ u' u w w' : Fin n,
              u' ≠ v ∧ v ≠ w' ∧ u ≠ w ∧ u ≠ w' ∧
              (∀ z, G.Adj v z ↔ z = u ∨ z = w) ∧
              (∀ z, G.Adj u z ↔ z = u' ∨ z = v) ∧
              (∀ z, G.Adj w z ↔ z = v ∨ z = w') := by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hv
            rcases hv with rfl | rfl | rfl | rfl
            · exact ⟨p₀, p₁, p₃, p₄, hne0.2.1, h24, h13, h14, hn2, hn1, hn3⟩
            · exact ⟨p₁, p₂, p₄, p₅, h13, h35, h24, h25, hn3, hn2, hn4⟩
            · exact ⟨p₂, p₃, p₅, p₆, h24, h46, h35, h36, hn4, hn3, hn5⟩
            · exact ⟨p₃, p₄, p₆, p₇, h35, hne7.2.2.2.2.1.symm, h46, hne7.2.2.2.1.symm, hn5, hn4, hn6⟩
          obtain ⟨u', u, w, w', hu'v, hvw', huw, huw', hv_nbr, hu_nbr, hw_nbr⟩ := hv_local
          rcases hstep with ⟨hs3, hC0⟩ | ⟨hs4, hC1⟩
          · rw [hlenC] at hs3 hC0
            rw [forestFun_update_deg2_false G g v] at hC0
            obtain ⟨t₀, hvc₀⟩ := hasMinVC_exists (deleteVertexEdges G v)
            have ht₀ := hasMinVC_deleteVertex_le G v hvc hvc₀
            have hedge := edgeFinset_card_deleteVertex_deg2 G u v w
              ((hv_nbr u).2 (Or.inl rfl)).symm ((hv_nbr w).2 (Or.inr rfl)) huw.symm (fun z hz => (hv_nbr z).1 hz)
            have hih := ih (s - 3) (by omega) (deleteVertexEdges G v) ∅
              (girth7_anti (deleteVertexEdges_le G v) hG)
              (branch7_anti (deleteVertexEdges_le G v) hB)
              (by simp) hvc₀ hC0
            simp only [Finset.card_empty, zero_add] at hih ⊢
            omega
          · rw [hlenC] at hs4 hC1
            rw [forestFun_update_deg2_true G g u v w hv_nbr] at hC1
            set G₁ := deleteVertexEdges (deleteVertexEdges G u) w with hG₁
            have hG₁_le : G₁ ≤ G := le_trans (deleteVertexEdges_le _ w) (deleteVertexEdges_le G u)
            obtain ⟨t₁, hvc₁⟩ := hasMinVC_exists G₁
            have ht₁ := hasMinVC_deletePair_le G u w hvc hvc₁
            have hedge := edgeFinset_card_deletePair_deg2 G u' u v w w' hu'v hvw' huw huw' hu_nbr hw_nbr
            rw [← hG₁] at hedge
            have hA1_iso : ∀ a ∈ ({u, w} : Finset (Fin n)), ∀ z : Fin n, ¬ G₁.Adj a z := by
              intro a ha z h
              simp only [Finset.mem_insert, Finset.mem_singleton] at ha
              rcases ha with rfl | rfl
              · exact h.1.2.1 rfl
              · exact h.2.1 rfl
            have hih := ih (s - 4) (by omega) G₁ {u, w}
              (girth7_anti hG₁_le hG) (branch7_anti hG₁_le hB) hA1_iso hvc₁ hC1
            have hcardA : ({u, w} : Finset (Fin n)).card = 2 := by
              rw [Finset.card_insert_of_notMem (by simp [huw]), Finset.card_singleton]
            rw [hcardA] at hih
            simp only [Finset.card_empty, zero_add]
            omega

theorem PEqualNP.Outside.L_meta_522 :
    ∀ (n k c t s : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (g : (Fin k → Bool) → Bool), (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) → (∀ u v : Fin n, u ≠ v → 3 ≤ (G.neighborSet u).ncard → 3 ≤ (G.neighborSet v).ncard → ∀ p : G.Walk u v, 7 ≤ p.length) → (∀ a ∈ A, ∀ v : Fin n, ¬ G.Adj a v) → (A.Nonempty ∨ ∃ u v : Fin n, G.Adj u v) → (∃ y y' : Fin k → Bool, g y ≠ g y') → (∀ r : ℕ, PEqualNP.MetaComplexity.HasCircuitSize k g r ↔ c ≤ r) → (∃ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S) ∧ S.card = t) → (∀ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S) → t ≤ S.card) → (PEqualNP.MetaComplexity.HasCircuitSize (n + k) (fun x : Fin (n + k) → Bool => decide ((∃ a ∈ A, x (Fin.castAdd k a) = true) ∨ ∃ u v : Fin n, G.Adj u v ∧ x (Fin.castAdd k u) = true ∧ x (Fin.castAdd k v) = true) || g (fun j : Fin k => x (Fin.natAdd n j))) s ↔ A.card + G.edgeFinset.card + t + c ≤ s) := by
  intro n k c t s G _ A g hG hB hA_iso _ hg_nc hg_sz hvc_ex hvc_min
  exact ⟨lower_bound_aux hg_nc hg_sz s G A hG hB hA_iso ⟨hvc_ex, hvc_min⟩,
    upper_bound_aux G A g hg_nc hg_sz hvc_ex⟩
