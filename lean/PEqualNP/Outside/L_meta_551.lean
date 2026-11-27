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


/-! ### Section 2: Forest Function and Exact Lower Bound -/

private def forestFun0 {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (A : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide ((∃ a ∈ A, x a = true) ∨ ∃ u v : Fin n, K.Adj u v ∧ x u = true ∧ x v = true)

private lemma isVertexCover_iff_isVC {n : ℕ} (K : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    K.IsVertexCover (S : Set (Fin n)) ↔ IsVC K S := by
  constructor
  · intro h u v huv
    exact h huv
  · intro h u v huv
    exact h u v huv

private lemma forestFun0_false {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (A : Finset (Fin n)) :
    forestFun0 K A (fun _ => false) = false := by
  simp [forestFun0]

private lemma forestFun0_true {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (A : Finset (Fin n)) (hne : A.Nonempty ∨ ∃ u v : Fin n, K.Adj u v) :
    forestFun0 K A (fun _ => true) = true := by
  simp only [forestFun0, decide_eq_true_eq]
  rcases hne with ⟨a, ha⟩ | ⟨u, v, huv⟩
  · exact Or.inl ⟨a, ha, trivial⟩
  · exact Or.inr ⟨u, v, huv, trivial, trivial⟩

private lemma forestFun0_nonconst {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (A : Finset (Fin n)) (hne : A.Nonempty ∨ ∃ u v : Fin n, K.Adj u v) :
    ∃ x y : Fin n → Bool, forestFun0 K A x ≠ forestFun0 K A y := by
  refine ⟨fun _ => false, fun _ => true, ?_⟩
  rw [forestFun0_false, forestFun0_true K A hne]
  decide

private lemma forestFun0_inc_A {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (A : Finset (Fin n)) (a : Fin n) (ha : a ∈ A) :
    ∃ x : Fin n → Bool,
      forestFun0 K A (Function.update x a false) = false ∧
      forestFun0 K A (Function.update x a true) = true := by
  refine ⟨fun _ => false, ?_, ?_⟩
  · have h0 : Function.update (fun _ : Fin n => false) a false = fun _ => false := by
      funext i; by_cases h : i = a <;> simp [h]
    rw [h0, forestFun0_false]
  · simp only [forestFun0, decide_eq_true_eq]
    exact Or.inl ⟨a, ha, by simp⟩

private lemma forestFun0_inc_edge {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (A : Finset (Fin n)) (hA_iso : ∀ a ∈ A, ∀ v : Fin n, ¬ K.Adj a v)
    (ℓ p : Fin n) (hlp : K.Adj ℓ p) :
    ∃ x : Fin n → Bool,
      forestFun0 K A (Function.update x ℓ false) = false ∧
      forestFun0 K A (Function.update x ℓ true) = true := by
  classical
  let x0 : Fin n → Bool := fun i => decide (i = p)
  refine ⟨x0, ?_, ?_⟩
  · simp only [forestFun0, decide_eq_false_iff_not, not_or]
    constructor
    · rintro ⟨a, ha, hxa⟩
      by_cases hal : a = ℓ
      · subst hal; simp at hxa
      · simp only [Function.update_of_ne hal, x0, decide_eq_true_eq] at hxa
        exact hA_iso a ha ℓ (hxa ▸ hlp.symm)
    · rintro ⟨u, v, huv, hxu, hxv⟩
      have hu : u = p := by
        by_cases hul : u = ℓ
        · subst hul; simp at hxu
        · simpa [Function.update_of_ne hul, x0] using hxu
      have hv : v = p := by
        by_cases hvl : v = ℓ
        · subst hvl; simp at hxv
        · simpa [Function.update_of_ne hvl, x0] using hxv
      subst hu; subst hv; exact huv.ne rfl
  · simp only [forestFun0, decide_eq_true_eq]
    refine Or.inr ⟨ℓ, p, hlp, by simp, ?_⟩
    simp [Function.update_of_ne hlp.ne.symm, x0]

private lemma forestFun0_dep_A {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (A : Finset (Fin n)) (a : Fin n) (ha : a ∈ A) :
    ∃ x : Fin n → Bool,
      forestFun0 K A (Function.update x a false) ≠ forestFun0 K A (Function.update x a true) := by
  obtain ⟨x, h0, h1⟩ := forestFun0_inc_A K A a ha
  exact ⟨x, by rw [h0, h1]; decide⟩

private lemma forestFun0_dep_edge {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (A : Finset (Fin n)) (hA_iso : ∀ a ∈ A, ∀ v : Fin n, ¬ K.Adj a v)
    (ℓ p : Fin n) (hlp : K.Adj ℓ p) :
    ∃ x : Fin n → Bool,
      forestFun0 K A (Function.update x ℓ false) ≠ forestFun0 K A (Function.update x ℓ true) := by
  obtain ⟨x, h0, h1⟩ := forestFun0_inc_edge K A hA_iso ℓ p hlp
  exact ⟨x, by rw [h0, h1]; decide⟩

private lemma forestFun0_update_A {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (A : Finset (Fin n)) (a : Fin n) (ha_iso : ∀ v : Fin n, ¬ K.Adj a v) :
    (fun x : Fin n → Bool => forestFun0 K A (Function.update x a false)) =
      forestFun0 K (A.erase a) := by
  funext x
  simp only [forestFun0]
  apply decide_eq_decide.2
  constructor
  · rintro (⟨b, hb, hxb⟩ | ⟨u, v, huv, hxu, hxv⟩)
    · by_cases hba : b = a
      · subst hba; simp at hxb
      · left; exact ⟨b, Finset.mem_erase.2 ⟨hba, hb⟩, by rwa [Function.update_of_ne hba] at hxb⟩
    · right
      have hua : u ≠ a := fun h => ha_iso v (h ▸ huv)
      have hva : v ≠ a := fun h => ha_iso u (h ▸ huv.symm)
      rw [Function.update_of_ne hua] at hxu
      rw [Function.update_of_ne hva] at hxv
      exact ⟨u, v, huv, hxu, hxv⟩
  · rintro (⟨b, hb, hxb⟩ | ⟨u, v, huv, hxu, hxv⟩)
    · obtain ⟨hba, hbA⟩ := Finset.mem_erase.1 hb
      left; exact ⟨b, hbA, by rwa [Function.update_of_ne hba]⟩
    · right
      have hua : u ≠ a := fun h => ha_iso v (h ▸ huv)
      have hva : v ≠ a := fun h => ha_iso u (h ▸ huv.symm)
      exact ⟨u, v, huv, by rwa [Function.update_of_ne hua], by rwa [Function.update_of_ne hva]⟩

private lemma forestFun0_update_leaf_false {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (ℓ p : Fin n) (hleaf : ∀ w, K.Adj ℓ w → w = p)
    [DecidableRel (K.deleteEdges {s(ℓ, p)}).Adj] :
    (fun x : Fin n → Bool => forestFun0 K ∅ (Function.update x ℓ false)) =
      forestFun0 (K.deleteEdges {s(ℓ, p)}) ∅ := by
  funext x
  simp only [forestFun0, Finset.notMem_empty, false_and, exists_false, false_or]
  apply decide_eq_decide.2
  constructor
  · rintro ⟨u, v, huv, hxu, hxv⟩
    have hu : u ≠ ℓ := by intro h; subst h; simp at hxu
    have hv : v ≠ ℓ := by intro h; subst h; simp at hxv
    rw [Function.update_of_ne hu] at hxu
    rw [Function.update_of_ne hv] at hxv
    refine ⟨u, v, SimpleGraph.deleteEdges_adj.2 ⟨huv, ?_⟩, hxu, hxv⟩
    intro hmem
    simp only [Set.mem_singleton_iff, Sym2.eq_iff] at hmem
    rcases hmem with ⟨rfl, _⟩ | ⟨_, rfl⟩
    · exact hu rfl
    · exact hv rfl
  · rintro ⟨u, v, hadj, hxu, hxv⟩
    obtain ⟨huv, hne⟩ := SimpleGraph.deleteEdges_adj.1 hadj
    have hu : u ≠ ℓ := by
      intro h; subst h
      have hp : v = p := hleaf v huv
      subst hp; exact hne rfl
    have hv : v ≠ ℓ := by
      intro h; subst h
      have hp : u = p := hleaf u huv.symm
      subst hp; exact hne Sym2.eq_swap
    exact ⟨u, v, huv, by rwa [Function.update_of_ne hu], by rwa [Function.update_of_ne hv]⟩

private lemma forestFun0_update_leaf_true {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (ℓ p : Fin n) (hlp : K.Adj ℓ p) (hleaf : ∀ w, K.Adj ℓ w → w = p)
    [DecidableRel (deleteVertexEdges K p).Adj] :
    (fun x : Fin n → Bool => forestFun0 K ∅ (Function.update x ℓ true)) =
      forestFun0 (deleteVertexEdges K p) {p} := by
  funext x
  simp only [forestFun0, Finset.notMem_empty, false_and, exists_false, false_or,
    Finset.mem_singleton, exists_eq_left]
  apply decide_eq_decide.2
  constructor
  · rintro ⟨u, v, huv, hxu, hxv⟩
    by_cases hup : u = p
    · subst hup
      left
      rwa [Function.update_of_ne hlp.ne.symm] at hxu
    · by_cases hvp : v = p
      · subst hvp
        left
        rwa [Function.update_of_ne hlp.ne.symm] at hxv
      · have huℓ : u ≠ ℓ := fun h => hvp (hleaf v (h ▸ huv))
        have hvℓ : v ≠ ℓ := fun h => hup (hleaf u (h ▸ huv.symm))
        rw [Function.update_of_ne huℓ] at hxu
        rw [Function.update_of_ne hvℓ] at hxv
        exact Or.inr ⟨u, v, ⟨huv, hup, hvp⟩, hxu, hxv⟩
  · rintro (hxp | ⟨u, v, ⟨huv, hup, hvp⟩, hxu, hxv⟩)
    · exact ⟨ℓ, p, hlp, by simp, by rwa [Function.update_of_ne hlp.ne.symm]⟩
    · have huℓ : u ≠ ℓ := fun h => hvp (hleaf v (h ▸ huv))
      have hvℓ : v ≠ ℓ := fun h => hup (hleaf u (h ▸ huv.symm))
      exact ⟨u, v, huv, by rwa [Function.update_of_ne huℓ], by rwa [Function.update_of_ne hvℓ]⟩

private lemma forest_lower_bound :
    ∀ (s : ℕ) {n t : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj] (A : Finset (Fin n)),
      K.IsAcyclic →
      (∀ a ∈ A, ∀ v : Fin n, ¬ K.Adj a v) →
      (A.Nonempty ∨ ∃ u v : Fin n, K.Adj u v) →
      HasMinVC K t →
      HasCircuitSize n (forestFun0 K A) s →
      A.card + K.edgeFinset.card + t - 1 ≤ s := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro n t K _ A hAcyc hA_iso hne hvc hC
    by_cases hcard1 : A.card + K.edgeFinset.card ≤ 1
    · by_cases hAne : A.Nonempty
      · have hApos : 1 ≤ A.card := Finset.one_le_card.2 hAne
        have hE0 : K.edgeFinset.card = 0 := by omega
        have hnoE : ∀ u v : Fin n, ¬ K.Adj u v := by
          intro u v huv
          have hmem : s(u, v) ∈ K.edgeFinset := SimpleGraph.mem_edgeFinset.2 huv
          have := Finset.one_le_card.2 ⟨s(u, v), hmem⟩
          omega
        have ht0 : t = 0 := hasMinVC_empty K hnoE hvc
        omega
      · have hA0 : A = ∅ := Finset.not_nonempty_iff_eq_empty.1 hAne
        subst hA0
        rcases hne with ⟨a, ha⟩ | ⟨u, v, huv⟩
        · exact absurd ha (Finset.notMem_empty a)
        · have hE1 : K.edgeFinset.card = 1 := by
            have h1 : 1 ≤ K.edgeFinset.card :=
              Finset.one_le_card.2 ⟨s(u, v), SimpleGraph.mem_edgeFinset.2 huv⟩
            simp at hcard1; omega
          have ht1 : t = 1 := by
            have hge1 : 1 ≤ t := by
              obtain ⟨⟨S, hS, hSc⟩, _⟩ := hvc
              rcases hS u v huv with hu | hv
              · have := Finset.one_le_card.2 ⟨u, hu⟩; omega
              · have := Finset.one_le_card.2 ⟨v, hv⟩; omega
            have hle1 : t ≤ 1 := by
              have hvc_u : IsVC K {u} := by
                intro a b hab
                have hmem1 : s(a, b) ∈ K.edgeFinset := SimpleGraph.mem_edgeFinset.2 hab
                have hmem2 : s(u, v) ∈ K.edgeFinset := SimpleGraph.mem_edgeFinset.2 huv
                have hle_e : K.edgeFinset.card ≤ 1 := by omega
                have heq : s(a, b) = s(u, v) := Finset.card_le_one.1 hle_e s(a, b) hmem1 s(u, v) hmem2
                rw [Sym2.eq_iff] at heq
                rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                · left; simp
                · right; simp
              have := hvc.2 {u} hvc_u
              simpa using this
            omega
          suffices hs1 : 1 ≤ s by simp [hE1, ht1]; omega
          by_contra hs0
          have hs_eq : s = 0 := by omega
          subst hs_eq
          obtain ⟨C, _, hsz, hev⟩ := hC
          have hnil : C.gates = [] := List.eq_nil_of_length_eq_zero (by simpa [Circuit.size] using hsz)
          have heval : ∀ x : Fin n → Bool, forestFun0 K ∅ x = (List.ofFn x).getD C.output false := by
            intro x; rw [← hev x]; simp [Circuit.eval, Circuit.wires, hnil]
          by_cases ho : C.output < n
          · set w : Fin n := ⟨C.output, ho⟩
            have hvalw : ∀ x : Fin n → Bool, forestFun0 K ∅ x = x w := by
              intro x; rw [heval x, ofFn_getD_lt x false C.output ho]
            let x1 : Fin n → Bool := fun i => decide (i = w)
            have hx1 : forestFun0 K ∅ x1 = true := by rw [hvalw x1]; simp [x1]
            simp only [forestFun0, Finset.notMem_empty, false_and, exists_false, false_or,
              decide_eq_true_eq] at hx1
            obtain ⟨a, b, hab, ha1, hb1⟩ := hx1
            simp [x1] at ha1 hb1
            subst ha1; subst hb1; exact hab.ne rfl
          · have hfalse : forestFun0 K ∅ (fun _ => true) = false := by
              rw [heval _, List.getD_eq_default _ _ (by simp; omega)]
            rw [forestFun0_true K ∅ (Or.inr ⟨u, v, huv⟩)] at hfalse
            exact Bool.noConfusion hfalse
    · by_cases hAne : A.Nonempty
      · obtain ⟨a, ha⟩ := hAne
        have hne' : (A.erase a).Nonempty ∨ ∃ u v : Fin n, K.Adj u v := by
          by_cases hA1 : 2 ≤ A.card
          · left
            have : 0 < (A.erase a).card := by rw [Finset.card_erase_of_mem ha]; omega
            exact Finset.card_pos.1 this
          · right
            have hAeq : A.card = 1 := by
              have := Finset.one_le_card.2 ⟨a, ha⟩; omega
            have hEpos : 0 < K.edgeFinset.card := by omega
            obtain ⟨e, he⟩ := Finset.card_pos.1 hEpos
            induction e using Sym2.ind with
            | _ u v => exact ⟨u, v, SimpleGraph.mem_edgeFinset.1 he⟩
        have hdep := forestFun0_dep_A K A a ha
        have hrew := forestFun0_update_A K A a (hA_iso a ha)
        have hnc : ∃ x x', forestFun0 K A (Function.update x a false) ≠
            forestFun0 K A (Function.update x' a false) := by
          simpa only [← congrFun hrew] using forestFun0_nonconst K (A.erase a) hne'
        obtain ⟨hs1, hC'⟩ := elim_one_var a false hC hdep hnc
        rw [hrew] at hC'
        have hih := ih (s - 1) (by omega) K (A.erase a) hAcyc
          (fun b hb => hA_iso b (Finset.mem_of_mem_erase hb)) hne' hvc hC'
        have hcard : (A.erase a).card + 1 = A.card := by
          have := Finset.one_le_card.2 ⟨a, ha⟩
          rw [Finset.card_erase_of_mem ha]; omega
        omega
      · have hA0 : A = ∅ := Finset.not_nonempty_iff_eq_empty.1 hAne
        subst hA0
        have hEdge : ∃ u v : Fin n, K.Adj u v := hne.resolve_left (by simp)
        obtain ⟨ℓ, p, hlp, hleaf, hcases⟩ := acyclic_leaf_cases K hAcyc hEdge
        rcases hcases with ⟨ℓ', hℓ'ne, hℓ'p, hℓ'leaf⟩ | hpdeg1 | ⟨q, hqne, hpq, hpdeg2⟩
        · classical
          obtain ⟨t₁, hvc₁⟩ := hasMinVC_exists (K.deleteEdges {s(ℓ, p)})
          have ht₁ : t₁ = t := hasMinVC_deleteLeafEdge_eq K ℓ ℓ' p hℓ'ne hℓ'p hℓ'leaf hvc hvc₁
          have hne' : (∅ : Finset (Fin n)).Nonempty ∨ ∃ u v, (K.deleteEdges {s(ℓ, p)}).Adj u v := by
            right; refine ⟨ℓ', p, SimpleGraph.deleteEdges_adj.2 ⟨hℓ'p, ?_⟩⟩
            simp only [Set.mem_singleton_iff, Sym2.eq_iff]
            rintro (⟨h1, _⟩ | ⟨h1, h2⟩)
            · exact hℓ'ne h1
            · exact hlp.ne h2.symm
          have hdep := forestFun0_dep_edge K ∅ (by simp) ℓ p hlp
          have hrew := forestFun0_update_leaf_false K ℓ p hleaf
          have hnc : ∃ x x', forestFun0 K ∅ (Function.update x ℓ false) ≠
              forestFun0 K ∅ (Function.update x' ℓ false) := by
            obtain ⟨x, x', hne1⟩ := forestFun0_nonconst (K.deleteEdges {s(ℓ, p)}) ∅ hne'
            exact ⟨x, x', by rw [congrFun hrew x, congrFun hrew x']; exact hne1⟩
          obtain ⟨hs1, hC'⟩ := elim_one_var ℓ false hC hdep hnc
          rw [hrew] at hC'
          have hih := ih (s - 1) (by omega) (K.deleteEdges {s(ℓ, p)}) ∅
            (hAcyc.anti (SimpleGraph.deleteEdges_le _)) (by simp) hne' hvc₁ hC'
          have hedge := edgeFinset_card_deleteEdge K ℓ p hlp
          simp only [Finset.card_empty, zero_add] at hih ⊢
          omega
        · classical
          obtain ⟨t', hvc'⟩ := hasMinVC_exists (deleteVertexEdges K p)
          have ht' : t' + 1 = t := hasMinVC_deleteVertex K ℓ p hlp hleaf hvc hvc'
          have hne' : ({p} : Finset (Fin n)).Nonempty ∨ ∃ u v, (deleteVertexEdges K p).Adj u v :=
            Or.inl (Finset.singleton_nonempty p)
          have hdep := forestFun0_dep_edge K ∅ (by simp) ℓ p hlp
          have hrew := forestFun0_update_leaf_true K ℓ p hlp hleaf
          have hnc : ∃ x x', forestFun0 K ∅ (Function.update x ℓ true) ≠
              forestFun0 K ∅ (Function.update x' ℓ true) := by
            obtain ⟨x, x', hne1⟩ := forestFun0_nonconst (deleteVertexEdges K p) {p} hne'
            exact ⟨x, x', by rw [congrFun hrew x, congrFun hrew x']; exact hne1⟩
          obtain ⟨hs1, hC'⟩ := elim_one_var ℓ true hC hdep hnc
          rw [hrew] at hC'
          have hih := ih (s - 1) (by omega) (deleteVertexEdges K p) {p}
            (hAcyc.anti (deleteVertexEdges_le K p))
            (by intro a ha v h; simp at ha; subst ha; exact h.2.1 rfl) hne' hvc' hC'
          have hedge := edgeFinset_card_deleteVertex_deg1 K ℓ p hlp hpdeg1
          simp only [Finset.card_singleton, Finset.card_empty, zero_add] at hih ⊢
          omega
        · classical
          have hne0 : (∅ : Finset (Fin n)).Nonempty ∨ ∃ u v, (K.deleteEdges {s(ℓ, p)}).Adj u v := by
            right; refine ⟨p, q, SimpleGraph.deleteEdges_adj.2 ⟨hpq, ?_⟩⟩
            simp only [Set.mem_singleton_iff, Sym2.eq_iff]
            rintro (⟨h1, _⟩ | ⟨_, h2⟩)
            · exact hlp.ne h1.symm
            · exact hqne h2
          have hne1 : ({p} : Finset (Fin n)).Nonempty ∨ ∃ u v, (deleteVertexEdges K p).Adj u v :=
            Or.inl (Finset.singleton_nonempty p)
          have hdep := forestFun0_dep_edge K ∅ (by simp) ℓ p hlp
          have hrew0 := forestFun0_update_leaf_false K ℓ p hleaf
          have hrew1 := forestFun0_update_leaf_true K ℓ p hlp hleaf
          have hnc0 : ∃ x x', forestFun0 K ∅ (Function.update x ℓ false) ≠
              forestFun0 K ∅ (Function.update x' ℓ false) := by
            obtain ⟨x, x', h⟩ := forestFun0_nonconst (K.deleteEdges {s(ℓ, p)}) ∅ hne0
            exact ⟨x, x', by rw [congrFun hrew0 x, congrFun hrew0 x']; exact h⟩
          have hnc1 : ∃ x x', forestFun0 K ∅ (Function.update x ℓ true) ≠
              forestFun0 K ∅ (Function.update x' ℓ true) := by
            obtain ⟨x, x', h⟩ := forestFun0_nonconst (deleteVertexEdges K p) {p} hne1
            exact ⟨x, x', by rw [congrFun hrew1 x, congrFun hrew1 x']; exact h⟩
          obtain ⟨hs2, hC0 | hC1⟩ := elim_two_var ℓ hC hdep hnc0 hnc1
          · rw [hrew0] at hC0
            obtain ⟨t₁, hvc₁⟩ := hasMinVC_exists (K.deleteEdges {s(ℓ, p)})
            have ht₁ := (hasMinVC_deleteEdge K ℓ p hvc hvc₁).2
            have hih := ih (s - 2) (by omega) (K.deleteEdges {s(ℓ, p)}) ∅
              (hAcyc.anti (SimpleGraph.deleteEdges_le _)) (by simp) hne0 hvc₁ hC0
            have hedge := edgeFinset_card_deleteEdge K ℓ p hlp
            simp only [Finset.card_empty, zero_add] at hih ⊢
            omega
          · rw [hrew1] at hC1
            obtain ⟨t', hvc'⟩ := hasMinVC_exists (deleteVertexEdges K p)
            have ht' : t' + 1 = t := hasMinVC_deleteVertex K ℓ p hlp hleaf hvc hvc'
            have hih := ih (s - 2) (by omega) (deleteVertexEdges K p) {p}
              (hAcyc.anti (deleteVertexEdges_le K p))
              (by intro a ha v h; simp at ha; subst ha; exact h.2.1 rfl) hne1 hvc' hC1
            have hedge := edgeFinset_card_deleteVertex_deg2 K ℓ p q hlp hpq hqne hpdeg2
            simp only [Finset.card_singleton, Finset.card_empty, zero_add] at hih ⊢
            omega

/-! ### Section 3: Two Distinct Leaves with Degree-2 Parents -/

private lemma max_path_end_cases {n m : ℕ} (G : SimpleGraph (Fin n)) (hAcyc : G.IsAcyclic)
    (hm_ge : 1 ≤ m)
    (hm_max : ∀ {u v : Fin n} (P : G.Walk u v), P.IsPath → P.length ≤ m)
    {ℓ z : Fin n} (P : G.Walk ℓ z) (hP : P.IsPath) (hPlen : P.length = m) :
    ∃ p : Fin n, G.Adj ℓ p ∧ (∀ w, G.Adj ℓ w → w = p) ∧
      ((∃ ℓ' : Fin n, ℓ' ≠ ℓ ∧ G.Adj ℓ' p ∧ ∀ w, G.Adj ℓ' w → w = p) ∨
       (∀ w, G.Adj p w → w = ℓ) ∨
       (∃ q : Fin n, q ≠ ℓ ∧ G.Adj p q ∧ ∀ w, G.Adj p w → w = ℓ ∨ w = q)) := by
  classical
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
    refine ⟨p, hlp, hℓ_leaf, ?_⟩
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
        intro hq; apply hℓ_not_Q; rw [← hq]; simp
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

private lemma acyclic_two_deg2_leaves {n : ℕ} (G : SimpleGraph (Fin n)) (hAcyc : G.IsAcyclic)
    (hEdge : ∃ u v : Fin n, G.Adj u v)
    (hno_sib : ¬ ∃ ℓ ℓ' p : Fin n, ℓ' ≠ ℓ ∧ G.Adj ℓ p ∧ (∀ w, G.Adj ℓ w → w = p) ∧
      G.Adj ℓ' p ∧ (∀ w, G.Adj ℓ' w → w = p))
    (hno_iso : ¬ ∃ ℓ p : Fin n, G.Adj ℓ p ∧ (∀ w, G.Adj ℓ w → w = p) ∧ (∀ w, G.Adj p w → w = ℓ)) :
    ∃ ℓ₁ p₁ q₁ ℓ₂ p₂ q₂ : Fin n, ℓ₁ ≠ ℓ₂ ∧
      G.Adj ℓ₁ p₁ ∧ (∀ w, G.Adj ℓ₁ w → w = p₁) ∧ q₁ ≠ ℓ₁ ∧ G.Adj p₁ q₁ ∧
        (∀ w, G.Adj p₁ w → w = ℓ₁ ∨ w = q₁) ∧
      G.Adj ℓ₂ p₂ ∧ (∀ w, G.Adj ℓ₂ w → w = p₂) ∧ q₂ ≠ ℓ₂ ∧ G.Adj p₂ q₂ ∧
        (∀ w, G.Adj p₂ w → w = ℓ₂ ∨ w = q₂) := by
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
    have hp : (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil).IsPath :=
      SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil (by simp [hadj.ne])
    exact ⟨1, Finset.mem_filter.2 ⟨Finset.mem_range.2 (hlen_lt _ hp), u₀, v₀, _, hp, rfl⟩⟩
  set m := S.max' hS_ne with hm
  have hm_mem : m ∈ S := Finset.max'_mem S hS_ne
  have hm_ge : 1 ≤ m := by
    obtain ⟨u₀, v₀, hadj⟩ := hEdge
    have hp : (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil).IsPath :=
      SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil (by simp [hadj.ne])
    exact Finset.le_max' S 1 (Finset.mem_filter.2 ⟨Finset.mem_range.2 (hlen_lt _ hp), u₀, v₀, _, hp, rfl⟩)
  have hm_max : ∀ {u v : Fin n} (P : G.Walk u v), P.IsPath → P.length ≤ m := by
    intro u v P hP
    exact Finset.le_max' S P.length (Finset.mem_filter.2 ⟨Finset.mem_range.2 (hlen_lt P hP), u, v, P, hP, rfl⟩)
  obtain ⟨_, ℓ₁, ℓ₂, P, hP, hPlen⟩ := Finset.mem_filter.1 hm_mem
  have hne : ℓ₁ ≠ ℓ₂ := by
    intro heq; subst heq
    cases P with
    | nil => simp at hPlen; omega
    | cons hadj Q =>
      have hnd := hP.support_nodup
      simp only [SimpleGraph.Walk.support_cons, List.nodup_cons] at hnd
      exact hnd.1 Q.end_mem_support
  obtain ⟨p₁, h1p, h1leaf, hc1⟩ := max_path_end_cases G hAcyc hm_ge hm_max P hP hPlen
  obtain ⟨q₁, hq1ne, hp1q1, hp1deg2⟩ : ∃ q₁ : Fin n, q₁ ≠ ℓ₁ ∧ G.Adj p₁ q₁ ∧
      ∀ w, G.Adj p₁ w → w = ℓ₁ ∨ w = q₁ := by
    rcases hc1 with ⟨ℓ', hℓ'ne, hℓ'p, hℓ'leaf⟩ | hpdeg1 | hres
    · exact absurd ⟨ℓ₁, ℓ', p₁, hℓ'ne, h1p, h1leaf, hℓ'p, hℓ'leaf⟩ hno_sib
    · exact absurd ⟨ℓ₁, p₁, h1p, h1leaf, hpdeg1⟩ hno_iso
    · exact hres
  have hPrev : P.reverse.IsPath := hP.reverse
  have hPrevLen : P.reverse.length = m := by rw [SimpleGraph.Walk.length_reverse, hPlen]
  obtain ⟨p₂, h2p, h2leaf, hc2⟩ := max_path_end_cases G hAcyc hm_ge hm_max P.reverse hPrev hPrevLen
  obtain ⟨q₂, hq2ne, hp2q2, hp2deg2⟩ : ∃ q₂ : Fin n, q₂ ≠ ℓ₂ ∧ G.Adj p₂ q₂ ∧
      ∀ w, G.Adj p₂ w → w = ℓ₂ ∨ w = q₂ := by
    rcases hc2 with ⟨ℓ', hℓ'ne, hℓ'p, hℓ'leaf⟩ | hpdeg1 | hres
    · exact absurd ⟨ℓ₂, ℓ', p₂, hℓ'ne, h2p, h2leaf, hℓ'p, hℓ'leaf⟩ hno_sib
    · exact absurd ⟨ℓ₂, p₂, h2p, h2leaf, hpdeg1⟩ hno_iso
    · exact hres
  exact ⟨ℓ₁, p₁, q₁, ℓ₂, p₂, q₂, hne, h1p, h1leaf, hq1ne, hp1q1, hp1deg2,
    h2p, h2leaf, hq2ne, hp2q2, hp2deg2⟩

/-! ### Section 4: Reduced Circuits, Constant-2 Drop, and Single-NOT Anti-Monotonicity -/

private def Reduced (n : ℕ) (C : Circuit) : Prop :=
  (∀ j : ℕ, j < C.gates.length → ∃ x y : Fin n → Bool,
    (C.wires (List.ofFn x)).getD (n + j) false ≠ (C.wires (List.ofFn y)).getD (n + j) false) ∧
  (∀ i j : ℕ, i < n + j → j < C.gates.length → ∃ x : Fin n → Bool,
    (C.wires (List.ofFn x)).getD i false ≠ (C.wires (List.ofFn x)).getD (n + j) false) ∧
  (C.gates ≠ [] → C.output + 1 = n + C.gates.length) ∧
  (∀ j : ℕ, j + 1 < C.gates.length → ∃ p ∈ C.gates.zipIdx, n + j < n + p.2 ∧
    (GateOp.casesOn (motive := fun _ => List ℕ) p.1.op
      p.1.inputs p.1.inputs (p.1.inputs.take 1) (fun _ => p.1.inputs) p.1.inputs).contains (n + j) = true)

private lemma effInputs_eq_inputs_of_nok (g : Gate) (h : NOkGate g) :
    (GateOp.casesOn (motive := fun _ => List ℕ) g.op
      g.inputs g.inputs (g.inputs.take 1) (fun _ => g.inputs) g.inputs) = g.inputs := by
  rcases g with ⟨op, ins⟩
  rcases h.1.1 with rfl | rfl | rfl
  · rfl
  · rfl
  · exact List.take_of_length_le (h.2 rfl)

private lemma effInputs_normGate (g : Gate) :
    (GateOp.casesOn (motive := fun _ => List ℕ) (normGate g).op
      (normGate g).inputs (normGate g).inputs ((normGate g).inputs.take 1)
      (fun _ => (normGate g).inputs) (normGate g).inputs) =
    (GateOp.casesOn (motive := fun _ => List ℕ) g.op
      g.inputs g.inputs (g.inputs.take 1) (fun _ => g.inputs) g.inputs) := by
  rcases g with ⟨op, ins⟩
  cases op <;> simp [normGate]

private lemma reduced_norm (n : ℕ) (C : Circuit) (hred : Reduced n C) :
    Reduced n ⟨C.gates.map normGate, C.output⟩ := by
  have hwires : ∀ x : Fin n → Bool,
      (Circuit.wires ⟨C.gates.map normGate, C.output⟩ (List.ofFn x)) = C.wires (List.ofFn x) :=
    fun x => wiresFrom_norm C.gates (List.ofFn x)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj
    rw [List.length_map] at hj
    simpa only [hwires] using hred.1 j hj
  · intro i j hij hj
    rw [List.length_map] at hj
    simpa only [hwires] using hred.2.1 i j hij hj
  · intro hne
    have hne' : C.gates ≠ [] := fun h => hne (by simp [h])
    simpa [List.length_map] using hred.2.2.1 hne'
  · intro j hj
    rw [List.length_map] at hj
    obtain ⟨p, hp, hlt, hcont⟩ := hred.2.2.2 j hj
    rw [List.mem_iff_getElem] at hp
    obtain ⟨k, hk, hpk⟩ := hp
    have hk' : k < C.gates.length := by simpa [List.length_zipIdx] using hk
    have hpk' : p = (C.gates[k]'hk', k) := by
      rw [← hpk]; simp [List.getElem_zipIdx]
    refine ⟨(normGate (C.gates[k]'hk'), k), ?_, ?_, ?_⟩
    · rw [List.mem_iff_getElem]
      refine ⟨k, by simp [List.length_zipIdx, hk'], ?_⟩
      simp [List.getElem_zipIdx]
    · rw [hpk'] at hlt; exact hlt
    · rw [hpk'] at hcont
      simpa only [effInputs_normGate] using hcont

private lemma reduced_no_dead {m : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hred : Reduced m C) (j : ℕ) (hj : j < C.gates.length) :
    C.output = m + j ∨ ∃ j' : ℕ, ∃ hj' : j' < C.gates.length, j < j' ∧ (m + j) ∈ C.gates[j'].inputs := by
  by_cases hlast : j + 1 < C.gates.length
  · right
    obtain ⟨p, hp, hlt, hcont⟩ := hred.2.2.2 j hlast
    rw [List.mem_iff_getElem] at hp
    obtain ⟨k, hk, hpk⟩ := hp
    have hk' : k < C.gates.length := by simpa [List.length_zipIdx] using hk
    have hpk' : p = (C.gates[k]'hk', k) := by
      rw [← hpk]; simp [List.getElem_zipIdx]
    rw [hpk'] at hlt hcont
    rw [effInputs_eq_inputs_of_nok _ (hnok _ (List.getElem_mem hk'))] at hcont
    exact ⟨k, hk', by omega, List.contains_iff_mem.1 hcont⟩
  · left
    have hne : C.gates ≠ [] := List.ne_nil_of_length_pos (by omega)
    have ho := hred.2.2.1 hne
    omega

private lemma reduced_gate_wf {m : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hred : Reduced m C) (j : ℕ) (hj : j < C.gates.length) :
    (C.gates[j].op = GateOp.not → ∃ a, a < m + j ∧ C.gates[j].inputs = [a]) ∧
    ((C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or) →
      ∃ a b, a < m + j ∧ b < m + j ∧ a ≠ b ∧ C.gates[j].inputs = [a, b]) := by
  have hnc_j : ∀ c : Bool, ¬ (∀ x : Fin m → Bool, (C.wires (List.ofFn x)).getD (m + j) false = c) := by
    intro c hc
    obtain ⟨x, y, hne⟩ := hred.1 j hj
    exact hne ((hc x).trans (hc y).symm)
  have hna_j : ∀ a < m + j, ¬ (∀ x : Fin m → Bool,
      (C.wires (List.ofFn x)).getD (m + j) false = (C.wires (List.ofFn x)).getD a false) := by
    intro a ha heq
    obtain ⟨x, hne⟩ := hred.2.1 a j ha hj
    exact hne (heq x).symm
  have hg := hnok C.gates[j] (List.getElem_mem hj)
  constructor
  · intro hop
    have hlen1 := hg.2 hop
    rcases hins : C.gates[j].inputs with _ | ⟨a, _ | ⟨b, l⟩⟩
    · exfalso; apply hnc_j true
      intro x; rw [wire_eval_gate C j hj x, hop, hins]; rfl
    · by_cases ha : a < m + j
      · exact ⟨a, ha, rfl⟩
      · exfalso; apply hnc_j true
        intro x; rw [wire_eval_gate C j hj x, hop, hins]; simp [ha, GateOp.eval]
    · rw [hins] at hlen1; simp at hlen1
  · intro hop
    have hlen2 := hg.1.2
    rcases hins : C.gates[j].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · exfalso
      rcases hop with hop | hop
      · apply hnc_j true; intro x; rw [wire_eval_gate C j hj x, hop, hins]; rfl
      · apply hnc_j false; intro x; rw [wire_eval_gate C j hj x, hop, hins]; rfl
    · exfalso
      by_cases ha : a < m + j
      · apply hna_j a ha; intro x; rw [wire_eval_gate C j hj x, hins]
        rcases hop with hop | hop <;> simp [hop, ha, GateOp.eval]
      · apply hnc_j false; intro x; rw [wire_eval_gate C j hj x, hins]
        rcases hop with hop | hop <;> simp [hop, ha, GateOp.eval]
    · by_cases ha : a < m + j
      · by_cases hb : b < m + j
        · by_cases hab : a = b
          · exfalso; subst hab; apply hna_j a ha
            intro x; rw [wire_eval_gate C j hj x, hins]
            rcases hop with hop | hop <;> simp [hop, ha, GateOp.eval]
          · exact ⟨a, b, ha, hb, hab, rfl⟩
        · exfalso
          rcases hop with hop | hop
          · apply hnc_j false; intro x; rw [wire_eval_gate C j hj x, hop, hins]; simp [ha, hb, GateOp.eval]
          · apply hna_j a ha; intro x; rw [wire_eval_gate C j hj x, hop, hins]; simp [ha, hb, GateOp.eval]
      · exfalso
        by_cases hb : b < m + j
        · rcases hop with hop | hop
          · apply hnc_j false; intro x; rw [wire_eval_gate C j hj x, hop, hins]; simp [ha, hb, GateOp.eval]
          · apply hna_j b hb; intro x; rw [wire_eval_gate C j hj x, hop, hins]; simp [ha, hb, GateOp.eval]
        · apply hnc_j false; intro x; rw [wire_eval_gate C j hj x, hins]
          rcases hop with hop | hop <;> simp [hop, ha, hb, GateOp.eval]
    · rw [hins] at hlen2; simp at hlen2

private lemma reduced_inputs_lt {m : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hred : Reduced m C) (j : ℕ) (hj : j < C.gates.length) :
    ∀ i ∈ C.gates[j].inputs, i < m + j := by
  intro i hi
  rcases (hnok _ (List.getElem_mem hj)).1.1 with hop | hop | hop
  · obtain ⟨a, b, ha, hb, _, hins⟩ := (reduced_gate_wf C hnok hred j hj).2 (Or.inl hop)
    rw [hins] at hi; simp at hi; rcases hi with rfl | rfl <;> assumption
  · obtain ⟨a, b, ha, hb, _, hins⟩ := (reduced_gate_wf C hnok hred j hj).2 (Or.inr hop)
    rw [hins] at hi; simp at hi; rcases hi with rfl | rfl <;> assumption
  · obtain ⟨a, ha, hins⟩ := (reduced_gate_wf C hnok hred j hj).1 hop
    rw [hins] at hi; simp at hi; subst hi; exact ha

private lemma min_reduced {m : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hmin : ∀ s' < C.gates.length, ¬ HasCircuitSize m (circuitFun m C) s')
    (hnc : ∃ x y : Fin m → Bool, circuitFun m C x ≠ circuitFun m C y) :
    Reduced m C := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj
    by_contra hall
    push Not at hall
    exact min_no_const C hnok hmin hnc j hj ((C.wires (List.ofFn (fun _ : Fin m => false))).getD (m + j) false)
      (fun x => hall x (fun _ => false))
  · intro i j hij hj
    by_contra hall
    push Not at hall
    exact min_no_alias C hnok hmin j i hj hij (fun x => (hall x).symm)
  · intro hne
    have hpos : 0 < C.gates.length := List.length_pos_of_ne_nil hne
    have hlt := min_output_lt C hnc
    rcases min_no_dead C hnok hmin (C.gates.length - 1) (by omega) with ho | ⟨j', hj', hgt, _⟩
    · omega
    · omega
  · intro j hj
    have hne : C.gates ≠ [] := List.ne_nil_of_length_pos (by omega)
    have ho : C.output + 1 = m + C.gates.length := by
      have hlt := min_output_lt C hnc
      rcases min_no_dead C hnok hmin (C.gates.length - 1) (by omega) with ho | ⟨j', hj', hgt, _⟩
      · omega
      · omega
    rcases min_no_dead C hnok hmin j (by omega) with heq | ⟨j', hj', hlt, hmem⟩
    · omega
    · refine ⟨(C.gates[j']'hj', j'), ?_, by omega, ?_⟩
      · rw [List.mem_iff_getElem]
        refine ⟨j', by simp [List.length_zipIdx, hj'], ?_⟩
        simp [List.getElem_zipIdx]
      · rw [effInputs_eq_inputs_of_nok _ (hnok _ (List.getElem_mem hj'))]
        exact List.contains_iff_mem.2 hmem

private lemma elimPass_nok (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hacc : ∀ g ∈ acc.2, NOkGate g) :
    ∀ g ∈ (elimPass m gs acc).2, NOkGate g := by
  induction gs generalizing acc with
  | nil => exact hacc
  | cons g rest ih =>
    rw [elimPass_cons]
    apply ih
    intro g' hg'
    simp only [elimStep, List.mem_append, Option.mem_toList] at hg'
    rcases hg' with h1 | h2
    · exact hacc g' h1
    · exact simplifyGate_nok _ _ _ g' h2

private lemma no_not_eval_false {m : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hred : Reduced m C) (hnoNot : ∀ g ∈ C.gates, g.op ≠ GateOp.not) :
    ∀ i < m + C.gates.length, (C.wires (List.ofFn (fun _ : Fin m => false))).getD i false = false := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases hlt : i < m
    · show (wiresFrom C.gates (List.ofFn (fun _ : Fin m => false))).getD i false = false
      rw [wiresFrom_getD_lt _ _ _ (by simp; exact hlt), ofFn_getD_lt _ _ _ hlt]
    · set j := i - m
      have hij : i = m + j := by omega
      have hj : j < C.gates.length := by omega
      rw [hij, wire_eval_gate C j hj]
      have hop := (hnok _ (List.getElem_mem hj)).1.1
      have hne := hnoNot _ (List.getElem_mem hj)
      have hbin : C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or := by
        rcases hop with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h hne
      obtain ⟨a, b, ha, hb, _, hins⟩ := (reduced_gate_wf C hnok hred j hj).2 hbin
      have hva : (C.wires (List.ofFn (fun _ : Fin m => false))).getD a false = false :=
        ih a (by omega) (by omega)
      have hvb : (C.wires (List.ofFn (fun _ : Fin m => false))).getD b false = false :=
        ih b (by omega) (by omega)
      rw [hins]
      rcases hbin with h | h <;>
        simp only [h, ha, hb, ↓reduceIte, hva, hvb, GateOp.eval, List.map_cons, List.map_nil,
          List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq,
          Bool.false_and, Bool.or_false]

private lemma deleteConstGate_two {m : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (j k : ℕ) (hj : j < C.gates.length) (hk : k < C.gates.length) (hjk : j < k)
    (hmem : (m + j) ∈ C.gates[k].inputs) (c : Bool)
    (hconst : ∀ x : Fin m → Bool, (C.wires (List.ofFn x)).getD (m + j) false = c)
    (hnc : ∃ x x' : Fin m → Bool, circuitFun m C x ≠ circuitFun m C x') :
    HasCircuitSize m (circuitFun m C) (C.gates.length - 2) := by
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
        rw [h2]
        have hEq : (wiresFrom (gs₁ ++ [C.gates[j]]) (List.ofFn x)).getD (m + j) false =
            (C.wires (List.ofFn x)).getD (m + j) false := by
          show _ = (wiresFrom C.gates (List.ofFn x)).getD (m + j) false
          conv_rhs => rw [hsplit, wiresFrom_append]
          exact (wiresFrom_getD_lt _ _ _ (by omega)).symm
        rw [hEq, hconst x]
      · rw [List.getD_eq_default _ _ (by simp [hinit]; omega),
            List.getD_eq_default _ _ (by omega)]
        exact ⟨trivial, rfl⟩
  have hval : ∀ x : Fin m → Bool,
      statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) =
        circuitFun m C x := fun x => ((hinv x).2.2 C.output).2
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl b =>
    obtain ⟨x, x', hne⟩ := hnc
    have hx := hval x; have hx' := hval x'
    rw [hst] at hx hx'
    exact absurd (hx.symm.trans hx') hne
  | inr out' =>
    have ht_lt : k - (j + 1) < gs₂.length := by rw [hgs₂, List.length_drop]; omega
    have hgk_eq : gs₂[k - (j + 1)]'ht_lt = C.gates[k]'hk := by
      simp only [hgs₂, List.getElem_drop]
      congr 1; omega
    have hdrop_t : (k - (j + 1)) ∈ elimDropped m gs₂ (init, gs₁) := by
      apply mem_elimDropped_of_const m gs₂ (init, gs₁) (k - (j + 1)) ht_lt
        (by rw [hgk_eq]; exact hnok _ (List.getElem_mem hk)) (m + j) (by rw [hgk_eq]; exact hmem)
      refine ⟨c, ?_⟩
      rw [elimState_getD_mono m gs₂ (init, gs₁) 0 (k - (j + 1)) (m + j) _ (Nat.zero_le _) (by omega)
        (by simp [hinit]), elimState_zero, hinit, getD_snoc_eq _ _ _ _ (by simp)]
    have hcard_ge : 1 ≤ (elimDropped m gs₂ (init, gs₁)).card :=
      Finset.one_le_card.2 ⟨k - (j + 1), hdrop_t⟩
    have hcard_eq := elimPass_card_dropped m gs₂ (init, gs₁)
    rw [← hacc] at hcard_eq
    dsimp only at hcard_eq
    have hl1 : gs₁.length = j := by rw [hgs₁, List.length_take, Nat.min_eq_left (by omega)]
    have hl2 : gs₂.length = C.gates.length - (j + 1) := by rw [hgs₂, List.length_drop]
    refine ⟨⟨acc.2, out'⟩, elimPass_ok m gs₂ _ (fun g hg => (hnok g (List.mem_of_mem_take hg)).1),
      by show acc.2.length ≤ C.gates.length - 2; omega, ?_⟩
    intro x; have := hval x; rw [hst] at this; exact this

private lemma single_not_antimono {m : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hred : Reduced m C) (v : Fin m)
    (Pos : ℕ → Prop)
    (hPos_in : ∀ i < m, Pos i ↔ i = (v : ℕ))
    (j₀ : ℕ) (hj₀ : j₀ < C.gates.length)
    (hj₀_op : C.gates[j₀].op = GateOp.not)
    (hnot_uniq : ∀ j : ℕ, (hj : j < C.gates.length) → C.gates[j].op = GateOp.not → j = j₀)
    (hPos_j₀ : ¬ Pos (m + j₀))
    (hj₀_in : ∀ a, C.gates[j₀].inputs = [a] → Pos a)
    (hPos_gate : ∀ j : ℕ, (hj : j < C.gates.length) → j ≠ j₀ →
      (Pos (m + j) → ∀ i ∈ C.gates[j].inputs, Pos i ∨ ∀ x : Fin m → Bool,
        (C.wires (List.ofFn (Function.update x v false))).getD i false =
        (C.wires (List.ofFn (Function.update x v true))).getD i false) ∧
      (¬ Pos (m + j) → ∀ i ∈ C.gates[j].inputs, ¬ Pos i))
    (hPos_out : ¬ Pos C.output) :
    ∀ x : Fin m → Bool,
      circuitFun m C (Function.update x v true) = true →
      circuitFun m C (Function.update x v false) = true := by
  intro x
  have hwire : ∀ i < m + C.gates.length,
      (Pos i → (C.wires (List.ofFn (Function.update x v false))).getD i false = true →
        (C.wires (List.ofFn (Function.update x v true))).getD i false = true) ∧
      (¬ Pos i → (C.wires (List.ofFn (Function.update x v true))).getD i false = true →
        (C.wires (List.ofFn (Function.update x v false))).getD i false = true) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      by_cases hlt : i < m
      · have h0 : (C.wires (List.ofFn (Function.update x v false))).getD i false =
            (Function.update x v false) ⟨i, hlt⟩ := by
          show (wiresFrom C.gates _).getD i false = _
          rw [wiresFrom_getD_lt _ _ _ (by simp; exact hlt), ofFn_getD_lt _ _ _ hlt]
        have h1 : (C.wires (List.ofFn (Function.update x v true))).getD i false =
            (Function.update x v true) ⟨i, hlt⟩ := by
          show (wiresFrom C.gates _).getD i false = _
          rw [wiresFrom_getD_lt _ _ _ (by simp; exact hlt), ofFn_getD_lt _ _ _ hlt]
        constructor
        · intro hpi hval
          have heq : i = (v : ℕ) := (hPos_in i hlt).1 hpi
          have hfin : (⟨i, hlt⟩ : Fin m) = v := Fin.ext heq
          rw [h1, hfin, Function.update_self]
        · intro hnpi hval
          have hne : i ≠ (v : ℕ) := fun h => hnpi ((hPos_in i hlt).2 h)
          have hfin : (⟨i, hlt⟩ : Fin m) ≠ v := fun h => hne (congrArg Fin.val h)
          rw [h0, Function.update_of_ne hfin]
          rwa [h1, Function.update_of_ne hfin] at hval
      · set j := i - m
        have hij : i = m + j := by omega
        have hj : j < C.gates.length := by omega
        rw [hij]
        by_cases hjeq : j = j₀
        · subst hjeq
          constructor
          · intro hp; exact absurd hp hPos_j₀
          · intro _ hval
            obtain ⟨a, ha, hins⟩ := (reduced_gate_wf C hnok hred j hj).1 hj₀_op
            have hpa : Pos a := hj₀_in a hins
            have hiha := (ih a (by omega) (by omega)).1 hpa
            rw [wire_eval_gate C j hj, hj₀_op, hins] at hval ⊢
            simp only [ha, ↓reduceIte, GateOp.eval, List.map_cons, List.map_nil,
              List.headD_cons, Bool.not_eq_true'] at hval ⊢
            cases h0a : (C.wires (List.ofFn (Function.update x v false))).getD a false
            · rfl
            · exact absurd (hiha h0a) (by rw [hval]; decide)
        · have hbin : C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or := by
            rcases (hnok _ (List.getElem_mem hj)).1.1 with h | h | h
            · exact Or.inl h
            · exact Or.inr h
            · exact absurd (hnot_uniq j hj h) hjeq
          obtain ⟨a, b, ha, hb, _, hins⟩ := (reduced_gate_wf C hnok hred j hj).2 hbin
          constructor
          · intro hpj hval
            have hpa_or := (hPos_gate j hj hjeq).1 hpj a (by rw [hins]; simp)
            have hpb_or := (hPos_gate j hj hjeq).1 hpj b (by rw [hins]; simp)
            have hma : (C.wires (List.ofFn (Function.update x v false))).getD a false = true →
                (C.wires (List.ofFn (Function.update x v true))).getD a false = true := by
              rcases hpa_or with hpa | heqa
              · exact (ih a (by omega) (by omega)).1 hpa
              · intro h; rw [← heqa x]; exact h
            have hmb : (C.wires (List.ofFn (Function.update x v false))).getD b false = true →
                (C.wires (List.ofFn (Function.update x v true))).getD b false = true := by
              rcases hpb_or with hpb | heqb
              · exact (ih b (by omega) (by omega)).1 hpb
              · intro h; rw [← heqb x]; exact h
            rw [wire_eval_gate C j hj, hins] at hval ⊢
            rcases hbin with hop | hop <;>
              simp only [hop, ha, hb, ↓reduceIte, GateOp.eval, List.map_cons, List.map_nil,
                List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq,
                Bool.and_true, Bool.or_false, Bool.and_eq_true, Bool.or_eq_true] at hval ⊢
            · exact ⟨hma hval.1, hmb hval.2⟩
            · rcases hval with h1 | h2
              · exact Or.inl (hma h1)
              · exact Or.inr (hmb h2)
          · intro hnpj hval
            have hnpa := (hPos_gate j hj hjeq).2 hnpj a (by rw [hins]; simp)
            have hnpb := (hPos_gate j hj hjeq).2 hnpj b (by rw [hins]; simp)
            have hma := (ih a (by omega) (by omega)).2 hnpa
            have hmb := (ih b (by omega) (by omega)).2 hnpb
            rw [wire_eval_gate C j hj, hins] at hval ⊢
            rcases hbin with hop | hop <;>
              simp only [hop, ha, hb, ↓reduceIte, GateOp.eval, List.map_cons, List.map_nil,
                List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq,
                Bool.and_true, Bool.or_false, Bool.and_eq_true, Bool.or_eq_true] at hval ⊢
            · exact ⟨hma hval.1, hmb hval.2⟩
            · rcases hval with h1 | h2
              · exact Or.inl (hma h1)
              · exact Or.inr (hmb h2)
  have hne : C.gates ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hout_lt : C.output < m + C.gates.length := by have := hred.2.2.1 hne; omega
  exact (hwire C.output hout_lt).2 hPos_out

private lemma wire_indep_of_not_read {m : ℕ} (C : Circuit) (v : Fin m)
    (hno : ∀ j : ℕ, (hj : j < C.gates.length) → (v : ℕ) ∉ C.gates[j].inputs) :
    ∀ k ≤ C.gates.length, ∀ i < m + k, i ≠ (v : ℕ) → ∀ x : Fin m → Bool,
      (C.wires (List.ofFn (Function.update x v false))).getD i false =
      (C.wires (List.ofFn (Function.update x v true))).getD i false := by
  intro k hk
  induction k with
  | zero =>
    intro i hi hne x
    show (wiresFrom C.gates _).getD i false = (wiresFrom C.gates _).getD i false
    rw [wiresFrom_getD_lt _ _ _ (by simp; omega), wiresFrom_getD_lt _ _ _ (by simp; omega),
      ofFn_getD_lt _ _ _ (by omega), ofFn_getD_lt _ _ _ (by omega)]
    have hfin : (⟨i, by omega⟩ : Fin m) ≠ v := fun h => hne (congrArg Fin.val h)
    rw [Function.update_of_ne hfin, Function.update_of_ne hfin]
  | succ k ih =>
    intro i hi hne x
    by_cases hlt : i < m + k
    · exact ih (by omega) i hlt hne x
    · have hieq : i = m + k := by omega
      subst hieq
      have hkt : k < C.gates.length := by omega
      rw [wire_eval_gate C k hkt, wire_eval_gate C k hkt]
      congr 1
      apply List.map_congr_left
      intro u hu
      by_cases hult : u < m + k
      · simp only [hult, ↓reduceIte]
        have hune : u ≠ (v : ℕ) := fun heq => hno k hkt (heq ▸ hu)
        exact ih (by omega) u hult hune x
      · simp only [hult, ↓reduceIte]

private lemma single_not_antimono_direct {m : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hred : Reduced m C) (v : Fin m)
    (j₀ : ℕ) (hj₀ : j₀ < C.gates.length)
    (hnot_eq : C.gates[j₀] = ⟨GateOp.not, [(v : ℕ)]⟩)
    (hnot_uniq : ∀ j : ℕ, (hj : j < C.gates.length) → C.gates[j].op = GateOp.not → j = j₀)
    (hv_uniq : ∀ j : ℕ, (hj : j < C.gates.length) → (v : ℕ) ∈ C.gates[j].inputs → j = j₀) :
    ∀ x : Fin m → Bool,
      circuitFun m C (Function.update x v true) = true →
      circuitFun m C (Function.update x v false) = true := by
  have hne : C.gates ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hout := hred.2.2.1 hne
  apply single_not_antimono C hnok hred v (fun i => i = (v : ℕ)) (fun _ _ => Iff.rfl)
    j₀ hj₀ (by rw [hnot_eq]) hnot_uniq (by omega)
    (by intro a ha; rw [hnot_eq] at ha; simp at ha; exact ha.symm)
    (by
      intro j hj hjne
      refine ⟨fun hp => by omega, fun _ i hi heq => hjne (hv_uniq j hj (heq ▸ hi))⟩)
    (by omega)

private lemma single_not_antimono_one {m : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hred : Reduced m C) (v : Fin m)
    (j₁ j₀ : ℕ) (hj₁ : j₁ < C.gates.length) (hj₀ : j₀ < C.gates.length) (h10 : j₁ < j₀)
    (hv_uniq : ∀ j : ℕ, (hj : j < C.gates.length) → (v : ℕ) ∈ C.gates[j].inputs → j = j₁)
    (hnot_eq : C.gates[j₀] = ⟨GateOp.not, [m + j₁]⟩)
    (hnot_uniq : ∀ j : ℕ, (hj : j < C.gates.length) → C.gates[j].op = GateOp.not → j = j₀)
    (hj₁_uniq : ∀ j : ℕ, (hj : j < C.gates.length) → (m + j₁) ∈ C.gates[j].inputs → j = j₀) :
    ∀ x : Fin m → Bool,
      circuitFun m C (Function.update x v true) = true →
      circuitFun m C (Function.update x v false) = true := by
  have hne : C.gates ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hout := hred.2.2.1 hne
  have hindep_lt : ∀ i < m + j₁, i ≠ (v : ℕ) → ∀ x : Fin m → Bool,
      (C.wires (List.ofFn (Function.update x v false))).getD i false =
      (C.wires (List.ofFn (Function.update x v true))).getD i false := by
    let Cpre : Circuit := ⟨C.gates.take j₁, 0⟩
    have hpre_no : ∀ j : ℕ, (hj : j < Cpre.gates.length) → (v : ℕ) ∉ Cpre.gates[j].inputs := by
      intro j hj hmem
      have hjl : j < j₁ := by simp [Cpre, List.length_take] at hj; omega
      have hj' : j < C.gates.length := by omega
      simp only [Cpre, List.getElem_take] at hmem
      exact absurd (hv_uniq j hj' hmem) (by omega)
    have hlen_pre : Cpre.gates.length = j₁ := by
      simp [Cpre, List.length_take, Nat.min_eq_left (le_of_lt hj₁)]
    intro i hi hne_v x
    have heq_f : (C.wires (List.ofFn (Function.update x v false))).getD i false =
        (Cpre.wires (List.ofFn (Function.update x v false))).getD i false := by
      show (wiresFrom C.gates _).getD i false = (wiresFrom (C.gates.take j₁) _).getD i false
      conv_lhs => rw [← List.take_append_drop j₁ C.gates, wiresFrom_append]
      exact wiresFrom_getD_lt _ _ _ (by rw [wiresFrom_length, List.length_ofFn, List.length_take]; omega)
    have heq_t : (C.wires (List.ofFn (Function.update x v true))).getD i false =
        (Cpre.wires (List.ofFn (Function.update x v true))).getD i false := by
      show (wiresFrom C.gates _).getD i false = (wiresFrom (C.gates.take j₁) _).getD i false
      conv_lhs => rw [← List.take_append_drop j₁ C.gates, wiresFrom_append]
      exact wiresFrom_getD_lt _ _ _ (by rw [wiresFrom_length, List.length_ofFn, List.length_take]; omega)
    rw [heq_f, heq_t]
    exact wire_indep_of_not_read Cpre v hpre_no j₁ (by omega) i hi hne_v x
  apply single_not_antimono C hnok hred v (fun i => i = (v : ℕ) ∨ i = m + j₁)
    (fun i hi => ⟨fun h => h.resolve_right (by omega), fun h => Or.inl h⟩)
    j₀ hj₀ (by rw [hnot_eq]) hnot_uniq (by omega)
    (by intro a ha; rw [hnot_eq] at ha; simp at ha; exact Or.inr ha.symm)
    (by
      intro j hj hjne
      constructor
      · intro hp i hi
        have hjeq : j = j₁ := by rcases hp with h | h <;> omega
        subst hjeq
        by_cases hiv : i = (v : ℕ)
        · exact Or.inl (Or.inl hiv)
        · right
          have hilt := reduced_inputs_lt C hnok hred j hj i hi
          exact hindep_lt i hilt hiv
      · intro hnp i hi hpi
        rcases hpi with heq | heq
        · have := hv_uniq j hj (heq ▸ hi)
          exact hnp (Or.inr (by omega))
        · exact hjne (hj₁_uniq j hj (heq ▸ hi)))
    (by intro h; rcases h with h | h <;> omega)

/-! ### Section 5: Structural NOT-Elimination Lemmas for `elimPass` -/

private lemma simplifyGate_some_op (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (g' : Gate) (hg : (simplifyGate op m ins).1 = some g') :
    g'.op = op := by
  cases op <;> simp only [simplifyGate] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg; rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg; rfl
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg; rfl
  · simp at hg
  · simp at hg

private lemma simplifyGate_some_mem_inputs (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hnot : op = GateOp.not → ins.length ≤ 1)
    (g' : Gate) (hg : (simplifyGate op m ins).1 = some g')
    (w : ℕ) (hw : Sum.inr w ∈ ins) :
    w ∈ g'.inputs := by
  cases op <;> simp only [simplifyGate] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg; simp at hw ⊢; exact hw
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg; simp at hw ⊢; exact hw
  · have hlen := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp at hw
    · cases a <;> simp [simpNot] at hg
      subst hg; simp at hw ⊢; exact hw
    · simp at hlen
  · simp at hg
  · simp at hg

private lemma simplifyGate_none_of_inr_mem (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (hlen : ins.length ≤ 2) (hnot : op = GateOp.not → ins.length ≤ 1)
    (hnone : (simplifyGate op m ins).1 = none)
    (w w' : ℕ) (hw : Sum.inr w ∈ ins) (hout : (simplifyGate op m ins).2 = Sum.inr w') :
    w' = w := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp at hw
    · cases a <;> simp [simplifyGate, simpAnd] at hw hout ⊢
      exact hout.symm.trans hw.symm
    · cases a with
      | inl ca =>
        cases b with
        | inl cb => simp at hw
        | inr vb =>
          cases ca <;> simp [simplifyGate, simpAnd] at hw hout
          exact hout.symm.trans hw.symm
      | inr va =>
        cases b with
        | inl cb =>
          cases cb <;> simp [simplifyGate, simpAnd] at hw hout
          exact hout.symm.trans hw.symm
        | inr vb => simp [simplifyGate, simpAnd] at hnone
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp at hw
    · cases a <;> simp [simplifyGate, simpOr] at hw hout ⊢
      exact hout.symm.trans hw.symm
    · cases a with
      | inl ca =>
        cases b with
        | inl cb => simp at hw
        | inr vb =>
          cases ca <;> simp [simplifyGate, simpOr] at hw hout
          exact hout.symm.trans hw.symm
      | inr va =>
        cases b with
        | inl cb =>
          cases cb <;> simp [simplifyGate, simpOr] at hw hout
          exact hout.symm.trans hw.symm
        | inr vb => simp [simplifyGate, simpOr] at hnone
    · simp at hlen
  · have hlen1 := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp at hw
    · cases a <;> simp [simplifyGate, simpNot] at hw hnone
    · simp at hlen1

private lemma elimState_snd_append (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (t₁ t₂ : ℕ) (hle : t₁ ≤ t₂) (ht₂ : t₂ ≤ gs.length) :
    ∃ suf : List Gate, (elimState m gs acc t₂).2 = (elimState m gs acc t₁).2 ++ suf := by
  induction t₂ with
  | zero =>
    have : t₁ = 0 := by omega
    subst this; exact ⟨[], by simp⟩
  | succ t₂ ih =>
    by_cases heq : t₁ = t₂ + 1
    · subst heq; exact ⟨[], by simp⟩
    · obtain ⟨suf, hsuf⟩ := ih (by omega) (by omega)
      rw [elimState_succ m gs acc t₂ (by omega), elimStep]
      dsimp only
      rw [hsuf, List.append_assoc]
      exact ⟨_, rfl⟩

private lemma elim_emit_at (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (j : ℕ) (hj : j < gs.length) (hnd : j ∉ elimDropped m gs acc) :
    let k := (elimState m gs acc j).2.length
    ∃ g' : Gate,
      (simplifyGate gs[j].op (m + k) (gs[j].inputs.map fun i =>
        (elimState m gs acc j).1.getD i (Sum.inl false))).1 = some g' ∧
      g'.op = gs[j].op ∧
      k < (elimPass m gs acc).2.length ∧
      (elimPass m gs acc).2[k]'(by
        have h1 : (elimState m gs acc (j + 1)).2.length = k + 1 := by
          rw [elimState_succ m gs acc j hj, elimStep]
          cases hopt : (simplifyGate gs[j].op (m + k) (gs[j].inputs.map fun i =>
              (elimState m gs acc j).1.getD i (Sum.inl false))).1 with
          | none =>
            exfalso; apply hnd
            rw [elimDropped, Finset.mem_filter, Finset.mem_range]
            dsimp only [k] at hopt
            exact ⟨hj, by simp only [hj, ↓reduceDIte, hopt]; rfl⟩
          | some g0 => simp [k]
        have h2 := elimState_snd_mono m gs acc (j + 1) gs.length (by omega)
        rw [elimState_end] at h2; omega) = g' ∧
      (elimState m gs acc (j + 1)).1.getD (acc.1.length + j) (Sum.inl false) = Sum.inr (m + k) := by
  intro k
  have hopt_ne : (simplifyGate gs[j].op (m + k) (gs[j].inputs.map fun i =>
      (elimState m gs acc j).1.getD i (Sum.inl false))).1 ≠ none := by
    intro hnone
    apply hnd
    rw [elimDropped, Finset.mem_filter, Finset.mem_range]
    dsimp only [k] at hnone
    exact ⟨hj, by simp only [hj, ↓reduceDIte, hnone]; rfl⟩
  obtain ⟨g', hopt⟩ := Option.ne_none_iff_exists'.1 hopt_ne
  have hstep : (elimState m gs acc (j + 1)).2 = (elimState m gs acc j).2 ++ [g'] := by
    dsimp only [k] at hopt
    rw [elimState_succ m gs acc j hj, elimStep, hopt]
    simp only [Option.toList_some]
  obtain ⟨suf, hsuf⟩ := elimState_snd_append m gs acc (j + 1) gs.length (by omega) le_rfl
  rw [elimState_end, hstep] at hsuf
  have hklt : k < (elimPass m gs acc).2.length := by rw [hsuf]; simp [k]
  refine ⟨g', hopt, simplifyGate_some_op _ _ _ g' hopt, hklt, ?_, ?_⟩
  · have hklt' : k < ((elimState m gs acc j).2 ++ ([g'] ++ suf)).length := by
      rw [← List.append_assoc, ← hsuf]; exact hklt
    have hcongr : (elimPass m gs acc).2[k]'hklt =
        ((elimState m gs acc j).2 ++ ([g'] ++ suf))[k]'hklt' := by
      simp only [hsuf, List.append_assoc]
    rw [hcongr, List.getElem_append_right (le_refl k)]
    simp [k]
  · rw [elimState_getD_at m gs acc j hj]
    exact simplifyGate_some_snd _ _ _ g' hopt

private lemma elim_emit_inj (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (j₁ j₂ : ℕ) (hj₁ : j₁ < gs.length) (hj₂ : j₂ < gs.length)
    (hnd₁ : j₁ ∉ elimDropped m gs acc) (hnd₂ : j₂ ∉ elimDropped m gs acc)
    (heq : (elimState m gs acc j₁).2.length = (elimState m gs acc j₂).2.length) :
    j₁ = j₂ := by
  by_contra hne
  wlog hlt : j₁ < j₂ generalizing j₁ j₂
  · exact this j₂ j₁ hj₂ hj₁ hnd₂ hnd₁ heq.symm (Ne.symm hne) (by omega)
  obtain ⟨g', hg', _, _, _, _⟩ := elim_emit_at m gs acc j₁ hj₁ hnd₁
  have h1 : (elimState m gs acc (j₁ + 1)).2.length = (elimState m gs acc j₁).2.length + 1 := by
    rw [elimState_succ m gs acc j₁ hj₁, elimStep, hg']; simp
  have h2 := elimState_snd_mono m gs acc (j₁ + 1) j₂ (by omega)
  omega

private lemma elim_emit_wf (m : ℕ) (gs : List Gate) (v : Fin m) (b : Bool)
    (hnok : ∀ g ∈ gs, NOkGate g) :
    ∀ k : ℕ, (hk : k < (elimPass m gs (initVar m v b, [])).2.length) →
      ∀ w ∈ (elimPass m gs (initVar m v b, [])).2[k].inputs, w < m + k := by
  have hstep : ∀ t ≤ gs.length, ∀ k : ℕ, (hk : k < (elimState m gs (initVar m v b, []) t).2.length) →
      ∀ w ∈ (elimState m gs (initVar m v b, []) t).2[k].inputs, w < m + k := by
    intro t
    induction t with
    | zero => intro _ k hk; simp [elimState_zero] at hk
    | succ t ih =>
      intro ht k hk w hw
      have htlt : t < gs.length := by omega
      have hst_eq := elimState_succ m gs (initVar m v b, []) t htlt
      revert hk hw
      rw [hst_eq]
      intro hk hw
      let st := elimState m gs (initVar m v b, []) t
      have hst_def : elimState m gs (initVar m v b, []) t = st := rfl
      cases hopt : (simplifyGate gs[t].op (m + st.2.length)
          (gs[t].inputs.map fun i => st.1.getD i (Sum.inl false))).1 with
      | none =>
        have hstep_snd : (elimStep m st gs[t]).2 = st.2 := by
          simp only [elimStep, hopt, Option.toList_none, List.append_nil]
        have hk' : k < st.2.length := by rw [← hstep_snd]; exact hk
        have hw' : w ∈ (st.2[k]'hk').inputs := by
          have : (elimStep m st gs[t]).2[k]'hk = st.2[k]'hk' := by simp only [hstep_snd]
          rwa [← this]
        exact ih (by omega) k hk' w hw'
      | some g' =>
        have hstep_snd : (elimStep m st gs[t]).2 = st.2 ++ [g'] := by
          simp only [elimStep, hopt, Option.toList_some]
        by_cases hkt : k < st.2.length
        · have hw' : w ∈ (st.2[k]'hkt).inputs := by
            have : (elimStep m st gs[t]).2[k]'hk = st.2[k]'hkt := by
              simp only [hstep_snd, List.getElem_append_left hkt]
            rwa [← this]
          exact ih (by omega) k hkt w hw'
        · have hkeq : k = st.2.length := by
            have hlen_s : (elimStep m st gs[t]).2.length = st.2.length + 1 := by
              rw [hstep_snd]; simp
            have hk_lt : k < st.2.length + 1 := by rw [← hlen_s]; exact hk
            omega
          have hgw : w ∈ g'.inputs := by
            have : (elimStep m st gs[t]).2[k]'hk = g' := by
              simp only [hstep_snd, hkeq, List.getElem_append_right (le_refl st.2.length)]
              simp
            rwa [← this]
          have hmem := simplifyGate_mem_inputs_of_some _ _ _ g' hopt w hgw
          obtain ⟨i, _, hi⟩ := List.mem_map.1 hmem
          have hinv := elimInv_pass m (List.ofFn (fun _ : Fin m => false)) (gs.take t) _
            (initVar m v b, []) (fun g hg => (hnok g (List.mem_of_mem_take hg)).1)
            (elimInv_initVar m v b (fun _ => false))
          have hv := (hinv.2.2 i).1
          rw [← elimState, hst_def, hi] at hv
          simpa [statValid, hkeq] using hv
  simpa only [elimState_end] using hstep gs.length le_rfl

private lemma elim_dropped_not_const {m : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hred : Reduced m C) (v : Fin m) (b : Bool)
    (j : ℕ) (hj : j < C.gates.length)
    (hdrop : j ∈ elimDropped m C.gates (initVar m v b, []))
    (hop : C.gates[j].op = GateOp.not) :
    ∃ a c, a < m + j ∧ C.gates[j].inputs = [a] ∧
      (elimState m C.gates (initVar m v b, []) j).1.getD a (Sum.inl false) = Sum.inl c ∧
      (elimState m C.gates (initVar m v b, []) (j + 1)).1.getD (m + j) (Sum.inl false) = Sum.inl (!c) ∧
      (a ≠ (v : ℕ) → m ≤ a ∧ a - m ∈ elimDropped m C.gates (initVar m v b, []) ∧
        (elimState m C.gates (initVar m v b, []) (a - m + 1)).1.getD a (Sum.inl false) = Sum.inl c) := by
  obtain ⟨a, ha, hins⟩ := (reduced_gate_wf C hnok hred j hj).1 hop
  have hnone : (simplifyGate GateOp.not (m + (elimState m C.gates (initVar m v b, []) j).2.length)
      [(elimState m C.gates (initVar m v b, []) j).1.getD a (Sum.inl false)]).1 = none := by
    rw [elimDropped, Finset.mem_filter, Finset.mem_range] at hdrop
    have h2 := hdrop.2
    simp only [hj, ↓reduceDIte, hop, hins, List.map_cons, List.map_nil] at h2
    exact Option.isNone_iff_eq_none.1 h2
  cases hsta : (elimState m C.gates (initVar m v b, []) j).1.getD a (Sum.inl false) with
  | inr w => rw [hsta] at hnone; simp [simplifyGate, simpNot] at hnone
  | inl c =>
    have hst_j : (elimState m C.gates (initVar m v b, []) (j + 1)).1.getD (m + j) (Sum.inl false) =
        Sum.inl (!c) := by
      have hget := elimState_getD_at m C.gates (initVar m v b, []) j hj
      have hlen : (initVar m v b).length = m := by simp [initVar]
      rw [hlen] at hget
      rw [hget, hop, hins]
      simp only [List.map_cons, List.map_nil, hsta, simplifyGate, simpNot]
    refine ⟨a, c, ha, hins, hsta, hst_j, ?_⟩
    intro hne
    have hge : m ≤ a := by
      by_contra hlt
      have hlt' : a < m := by omega
      have h0 : (elimState m C.gates (initVar m v b, []) j).1.getD a (Sum.inl false) = Sum.inr a := by
        rw [elimState_getD_mono m C.gates (initVar m v b, []) 0 j a _ (Nat.zero_le _) (by omega)
          (by simp [initVar]; exact hlt'), elimState_zero, initVar, ofFn_getD_lt _ _ _ hlt']
        have hfin : (⟨a, hlt'⟩ : Fin m) ≠ v := fun h => hne (congrArg Fin.val h)
        simp [hfin]
      rw [h0] at hsta; cases hsta
    have hst_am : (elimState m C.gates (initVar m v b, []) (a - m + 1)).1.getD a (Sum.inl false) = Sum.inl c := by
      have hmono := elimState_getD_mono m C.gates (initVar m v b, []) (a - m + 1) j a (Sum.inl false)
        (by omega) (by omega) (by simp [initVar]; omega)
      rw [← hmono, hsta]
    have hdrop_am : a - m ∈ elimDropped m C.gates (initVar m v b, []) := by
      by_contra hnd
      obtain ⟨_, _, _, _, _, hst_inr⟩ := elim_emit_at m C.gates (initVar m v b, []) (a - m) (by omega) hnd
      have hlen : (initVar m v b).length = m := by simp [initVar]
      rw [hlen, show m + (a - m) = a by omega] at hst_inr
      rw [hst_inr] at hst_am
      cases hst_am
    exact ⟨hge, hdrop_am, hst_am⟩

private lemma elim_const_not_output_and_consumer {m : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hred : Reduced m C) (v : Fin m) (b : Bool)
    (hnc : ∃ x x' : Fin m → Bool,
      circuitFun m C (Function.update x v b) ≠ circuitFun m C (Function.update x' v b))
    (j : ℕ) (hj : j < C.gates.length) (c : Bool)
    (hc : (elimState m C.gates (initVar m v b, []) (j + 1)).1.getD (m + j) (Sum.inl false) = Sum.inl c) :
    C.output ≠ m + j ∧
    ∃ k : ℕ, ∃ hk : k < C.gates.length, j < k ∧ (m + j) ∈ C.gates[k].inputs ∧
      k ∈ elimDropped m C.gates (initVar m v b, []) := by
  have hout_ne : C.output ≠ m + j := by
    intro heq
    have hst : (elimPass m C.gates (initVar m v b, [])).1.getD C.output (Sum.inl false) = Sum.inl c := by
      rw [heq, ← elimState_end,
        elimState_getD_mono m C.gates _ (j + 1) C.gates.length (m + j) _ (by omega) le_rfl (by simp [initVar])]
      exact hc
    obtain ⟨x, x', hne⟩ := hnc
    have hinv1 := elimInv_pass m (List.ofFn x) C.gates _ (initVar m v b, [])
      (fun g hg => (hnok g hg).1) (elimInv_initVar m v b x)
    have hinv2 := elimInv_pass m (List.ofFn x') C.gates _ (initVar m v b, [])
      (fun g hg => (hnok g hg).1) (elimInv_initVar m v b x')
    have e1 := (hinv1.2.2 C.output).2
    have e2 := (hinv2.2.2 C.output).2
    rw [hst] at e1 e2
    exact hne (e1.symm.trans e2)
  obtain ⟨k, hk, hjk, hmem⟩ := (reduced_no_dead C hnok hred j hj).resolve_left hout_ne
  have hdrop_k : k ∈ elimDropped m C.gates (initVar m v b, []) := by
    apply mem_elimDropped_of_const m C.gates _ k hk (hnok _ (List.getElem_mem hk)) (m + j) hmem
    refine ⟨c, ?_⟩
    rw [elimState_getD_mono m C.gates _ (j + 1) k (m + j) _ (by omega) (by omega) (by simp [initVar])]
    exact hc
  exact ⟨hout_ne, k, hk, hjk, hmem, hdrop_k⟩

private lemma elim_not_consumer_ne_not {m : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hred : Reduced m C) (j₀ k a : ℕ) (hj₀ : j₀ < C.gates.length) (hk : k < C.gates.length)
    (hjk : j₀ < k) (ha : a < m + j₀) (hnot : C.gates[j₀] = ⟨GateOp.not, [a]⟩)
    (hmem : (m + j₀) ∈ C.gates[k].inputs) :
    C.gates[k].op ≠ GateOp.not := by
  intro hop
  obtain ⟨u, _, hins⟩ := (reduced_gate_wf C hnok hred k hk).1 hop
  rw [hins] at hmem; simp at hmem; subst hmem
  obtain ⟨x, hne⟩ := hred.2.1 a k (by omega) hk
  apply hne
  have hv0 : (C.wires (List.ofFn x)).getD (m + j₀) false = !(C.wires (List.ofFn x)).getD a false := by
    rw [wire_eval_gate C j₀ hj₀ x, hnot]
    simp only [ha, ↓reduceIte, GateOp.eval, List.map_cons, List.map_nil, List.headD_cons]
  rw [wire_eval_gate C k hk x, hop, hins]
  simp only [show m + j₀ < m + k by omega, ↓reduceIte, hv0, GateOp.eval, List.map_cons,
    List.map_nil, List.headD_cons, Bool.not_not]

private lemma elim_gate_not_both_a_and_not_a {m : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hred : Reduced m C) (j₀ k a : ℕ) (hj₀ : j₀ < C.gates.length) (hk : k < C.gates.length)
    (hjk : j₀ < k) (ha : a < m + j₀) (hnot : C.gates[j₀] = ⟨GateOp.not, [a]⟩)
    (hmem : (m + j₀) ∈ C.gates[k].inputs) :
    a ∉ C.gates[k].inputs := by
  classical
  intro ha_mem
  have hne_not := elim_not_consumer_ne_not C hnok hred j₀ k a hj₀ hk hjk ha hnot hmem
  have hbin : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or := by
    rcases (hnok _ (List.getElem_mem hk)).1.1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hne_not
  obtain ⟨u, w, hu, hw, huw, hins⟩ := (reduced_gate_wf C hnok hred k hk).2 hbin
  rw [hins] at hmem ha_mem; simp at hmem ha_mem
  have hv0 : ∀ x : Fin m → Bool,
      (C.wires (List.ofFn x)).getD (m + j₀) false = !(C.wires (List.ofFn x)).getD a false := by
    intro x; rw [wire_eval_gate C j₀ hj₀ x, hnot]
    simp only [ha, ↓reduceIte, GateOp.eval, List.map_cons, List.map_nil, List.headD_cons]
  have hconst_val : ∀ x : Fin m → Bool,
      (C.wires (List.ofFn x)).getD (m + k) false =
        (if C.gates[k].op = GateOp.and then false else true) := by
    intro x
    rw [wire_eval_gate C k hk x, hins]
    rcases hmem with h1 | h1 <;> rcases ha_mem with h2 | h2
    · exact absurd (h1.trans h2.symm) (by omega)
    · rw [← h1, ← h2]
      rcases hbin with hop | hop <;>
        (simp only [hop, show m + j₀ < m + k by omega, show a < m + k by omega, ↓reduceIte,
          hv0 x, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.or_false];
         cases (C.wires (List.ofFn x)).getD a false <;> simp)
    · rw [← h1, ← h2]
      rcases hbin with hop | hop <;>
        (simp only [hop, show m + j₀ < m + k by omega, show a < m + k by omega, ↓reduceIte,
          hv0 x, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.or_false];
         cases (C.wires (List.ofFn x)).getD a false <;> simp)
    · exact absurd (h1.trans h2.symm) (by omega)
  obtain ⟨x, y, hne⟩ := hred.1 k hk
  exact hne ((hconst_val x).trans (hconst_val y).symm)

private lemma elim_not_survives_or_dead {m opt' : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (v : Fin m) (b : Bool)
    (f' : (Fin m → Bool) → Bool)
    (hf'_eq : f' = fun x => circuitFun m C (Function.update x v b))
    (hnc' : ∃ x y : Fin m → Bool, f' x ≠ f' y)
    (hlb' : ∀ s' < opt', ¬ HasCircuitSize m f' s')
    (hIH' : ∀ D : Circuit, (∀ g ∈ D.gates, NOkGate g) → circuitFun m D = f' →
      D.size ≤ opt' + 1 → Reduced m D → ∀ g ∈ D.gates, g.op ≠ GateOp.not)
    (hsz_le : (elimPass m C.gates (initVar m v b, [])).2.length ≤ opt' + 1)
    (j₀ : ℕ) (hj₀ : j₀ < C.gates.length) (hnd : j₀ ∉ elimDropped m C.gates (initVar m v b, []))
    (hj₀_op : C.gates[j₀].op = GateOp.not) :
    let acc := elimPass m C.gates (initVar m v b, [])
    let k₀ := (elimState m C.gates (initVar m v b, []) j₀).2.length
    ∃ out : ℕ, acc.1.getD C.output (Sum.inl false) = Sum.inr out ∧
      acc.2.length = opt' + 1 ∧
      out ≠ m + k₀ ∧
      (∀ r : ℕ, (hr : r < acc.2.length) → k₀ < r → (m + k₀) ∉ acc.2[r].inputs) ∧
      (∀ r : ℕ, (hr : r < acc.2.length) → r ≠ k₀ → acc.2[r].op ≠ GateOp.not) := by
  intro acc k₀
  have hnc_upd : ∃ x x' : Fin m → Bool,
      circuitFun m C (Function.update x v b) ≠ circuitFun m C (Function.update x' v b) := by
    obtain ⟨x, x', hne⟩ := hnc'
    exact ⟨x, x', by simpa [hf'_eq] using hne⟩
  obtain ⟨out, hout_st, _, _, hfun_acc⟩ := elim_var_circuit C hnok v b hnc_upd
  set C' : Circuit := ⟨acc.2, out⟩ with hC'
  have hnok' : ∀ g ∈ C'.gates, NOkGate g :=
    elimPass_nok m C.gates (initVar m v b, []) (by simp)
  have hfun' : circuitFun m C' = f' := hfun_acc.trans hf'_eq.symm
  have hge_opt : opt' ≤ C'.gates.length := by
    by_contra hlt
    exact hlb' C'.gates.length (by omega)
      ⟨C', fun g hg => (hnok' g hg).1, le_rfl, fun x => congrFun hfun' x⟩
  obtain ⟨g₀, hg₀_some, hg₀_op, hk₀_lt, hk₀_eq, _⟩ :=
    elim_emit_at m C.gates (initVar m v b, []) j₀ hj₀ hnd
  have hk₀_not : (C'.gates[k₀]'hk₀_lt).op = GateOp.not := by
    change acc.2[k₀].op = GateOp.not
    rw [hk₀_eq, hg₀_op, hj₀_op]
  have hC'_le : C'.gates.length ≤ opt' + 1 := hsz_le
  have hlen_eq : C'.gates.length = opt' + 1 := by
    by_contra hne
    have hmin_eq : C'.gates.length = opt' := by omega
    have hmin' : ∀ s' < C'.gates.length, ¬ HasCircuitSize m (circuitFun m C') s' := by
      intro s' hs'; rw [hfun']; exact hlb' s' (by omega)
    have hred' := min_reduced C' hnok' hmin' (by rwa [hfun'])
    exact hIH' C' hnok' hfun' (by simpa [Circuit.size] using hsz_le) hred'
      (C'.gates[k₀]'hk₀_lt) (List.getElem_mem hk₀_lt) hk₀_not
  have hdead_kill : ∀ j : ℕ, (hj : j < C'.gates.length) →
      C'.output ≠ m + j →
      (∀ r : ℕ, (hr : r < C'.gates.length) → j < r → (m + j) ∉ C'.gates[r].inputs) →
      j = k₀ ∧ ∀ r : ℕ, (hr : r < C'.gates.length) → r ≠ k₀ → C'.gates[r].op ≠ GateOp.not := by
    intro j hj hout_ne hno_read
    set D := deleteGate m C' j 0 with hD
    have hDnok : ∀ g ∈ D.gates, NOkGate g := deleteGate_nok m C' j 0 hnok'
    have hDlen : D.gates.length = opt' := by rw [hD, deleteGate_len m C' j 0 hj, hlen_eq]; omega
    have hDfun : circuitFun m D = f' := by
      funext x
      rw [← hfun']
      show ((deleteGate m C' j 0).wires (List.ofFn x)).getD (substWire (m + j) 0 C'.output) false =
        (C'.wires (List.ofFn x)).getD C'.output false
      by_cases hlt : C'.output < m + C'.gates.length
      · exact deleteGate_dead_wires m C' j hj hno_read (List.ofFn x) (by simp) C'.output hlt hout_ne
      · have h1 : ((deleteGate m C' j 0).wires (List.ofFn x)).length =
            m + (deleteGate m C' j 0).gates.length := by
          show (wiresFrom _ _).length = _; rw [wiresFrom_length]; simp
        have h2 : (C'.wires (List.ofFn x)).length = m + C'.gates.length := by
          show (wiresFrom _ _).length = _; rw [wiresFrom_length]; simp
        have hge1 : m + (deleteGate m C' j 0).gates.length ≤ substWire (m + j) 0 C'.output := by
          rw [deleteGate_len m C' j 0 hj]; unfold substWire; split_ifs <;> omega
        rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
    have hDmin : ∀ s' < D.gates.length, ¬ HasCircuitSize m (circuitFun m D) s' := by
      intro s' hs'; rw [hDfun]; exact hlb' s' (by omega)
    have hDred := min_reduced D hDnok hDmin (by rwa [hDfun])
    have hDnoNot : ∀ g ∈ D.gates, g.op ≠ GateOp.not :=
      hIH' D hDnok hDfun (by show D.gates.length ≤ opt' + 1; omega) hDred
    have hother_noNot : ∀ r : ℕ, (hr : r < C'.gates.length) → r ≠ j → C'.gates[r].op ≠ GateOp.not := by
      intro r hr hrne
      by_cases hlt : r < j
      · have hrD : r < D.gates.length := by omega
        have hget := deleteGate_getElem_lt m C' j 0 r hj hlt
        have hne := hDnoNot (D.gates[r]'hrD) (List.getElem_mem hrD)
        change ((deleteGate m C' j 0).gates[r]'(by rw [← hD]; exact hrD)).op ≠ GateOp.not at hne
        rwa [hget] at hne
      · have hgt : j < r := by omega
        have hrD : r - 1 < D.gates.length := by omega
        have hget := deleteGate_getElem_gt m C' j 0 r hj hr hgt
        have hne := hDnoNot (D.gates[r - 1]'hrD) (List.getElem_mem hrD)
        change ((deleteGate m C' j 0).gates[r - 1]'(by rw [← hD]; exact hrD)).op ≠ GateOp.not at hne
        rw [hget] at hne
        exact hne
    have hjeq : j = k₀ := by
      by_contra hne
      exact hother_noNot k₀ hk₀_lt (Ne.symm hne) hk₀_not
    subst hjeq
    exact ⟨rfl, hother_noNot⟩
  -- Since C' has a NOT gate and size opt' + 1, C' cannot be Reduced (else hIH' gives contradiction)
  have hnot_red : ¬ Reduced m C' := fun hred' =>
    hIH' C' hnok' hfun' (by show C'.gates.length ≤ opt' + 1; omega) hred'
      (C'.gates[k₀]'hk₀_lt) (List.getElem_mem hk₀_lt) hk₀_not
  -- Check which of the 4 reducedness conditions fails in C'
  by_cases h1 : ∀ j : ℕ, j < C'.gates.length → ∃ x y : Fin m → Bool,
      (C'.wires (List.ofFn x)).getD (m + j) false ≠ (C'.wires (List.ofFn y)).getD (m + j) false
  · by_cases h2 : ∀ i j : ℕ, i < m + j → j < C'.gates.length → ∃ x : Fin m → Bool,
        (C'.wires (List.ofFn x)).getD i false ≠ (C'.wires (List.ofFn x)).getD (m + j) false
    · by_cases h3 : C'.gates ≠ [] → C'.output + 1 = m + C'.gates.length
      · -- Violation 4: some gate j with j + 1 < len is not read by any later gate
        have h4 : ¬ ∀ j : ℕ, j + 1 < C'.gates.length → ∃ p ∈ C'.gates.zipIdx, m + j < m + p.2 ∧
            (GateOp.casesOn (motive := fun _ => List ℕ) p.1.op
              p.1.inputs p.1.inputs (p.1.inputs.take 1) (fun _ => p.1.inputs) p.1.inputs).contains (m + j) = true :=
          fun h4 => hnot_red ⟨h1, h2, h3, h4⟩
        push Not at h4
        obtain ⟨j, hj1, hno4⟩ := h4
        have hne_nil : C'.gates ≠ [] := List.ne_nil_of_length_pos (by omega)
        have hout_eq := h3 hne_nil
        have hno_read : ∀ r : ℕ, (hr : r < C'.gates.length) → j < r → (m + j) ∉ C'.gates[r].inputs := by
          intro r hr hlt hmem
          have hmem_z : (C'.gates[r]'hr, r) ∈ C'.gates.zipIdx := by
            rw [List.mem_iff_getElem]
            exact ⟨r, by simp [List.length_zipIdx, hr], by simp [List.getElem_zipIdx]⟩
          have hcont := hno4 (C'.gates[r]'hr, r) hmem_z (by omega)
          change (GateOp.casesOn (motive := fun _ => List ℕ) (C'.gates[r]'hr).op
            (C'.gates[r]'hr).inputs (C'.gates[r]'hr).inputs ((C'.gates[r]'hr).inputs.take 1)
            (fun _ => (C'.gates[r]'hr).inputs) (C'.gates[r]'hr).inputs).contains (m + j) ≠ true at hcont
          rw [effInputs_eq_inputs_of_nok _ (hnok' _ (List.getElem_mem hr))] at hcont
          exact hcont (List.contains_iff_mem.2 hmem)
        obtain ⟨hjk, huniq⟩ := hdead_kill j (by omega) (by omega) hno_read
        subst hjk
        exact ⟨out, hout_st, hlen_eq, by change C'.output ≠ m + k₀; omega, hno_read, huniq⟩
      · -- Violation 3: output not last → last gate is dead
        push Not at h3
        obtain ⟨hne_nil, hout_ne_last⟩ := h3
        have hpos : 0 < C'.gates.length := List.length_pos_of_ne_nil hne_nil
        have hout_lt := min_output_lt C' (by rwa [hfun'])
        have hno_read : ∀ r : ℕ, (hr : r < C'.gates.length) → C'.gates.length - 1 < r →
            (m + (C'.gates.length - 1)) ∉ C'.gates[r].inputs :=
          fun r hr hlt => by omega
        obtain ⟨hjk, huniq⟩ := hdead_kill (C'.gates.length - 1) (by omega) (by omega) hno_read
        exact ⟨out, hout_st, hlen_eq, by rw [← hjk]; change C'.output ≠ m + (C'.gates.length - 1); omega,
          by rw [← hjk]; exact hno_read, huniq⟩
    · -- Violation 2: duplicate wire j aliases u < m + j
      exfalso
      push Not at h2
      obtain ⟨u, j, huj, hj, heq⟩ := h2
      set D := deleteGate m C' j u with hD
      have hDnok : ∀ g ∈ D.gates, NOkGate g := deleteGate_nok m C' j u hnok'
      have hDlen : D.gates.length = opt' := by rw [hD, deleteGate_len m C' j u hj, hlen_eq]; omega
      have hDfun : circuitFun m D = f' := by
        funext x
        rw [← hfun']
        show ((deleteGate m C' j u).wires (List.ofFn x)).getD (substWire (m + j) u C'.output) false =
          (C'.wires (List.ofFn x)).getD C'.output false
        by_cases hlt : C'.output < m + C'.gates.length
        · exact deleteGate_wires_eq m C' j u hj huj (List.ofFn x) (by simp) (heq x).symm C'.output hlt
        · have h1' : ((deleteGate m C' j u).wires (List.ofFn x)).length =
              m + (deleteGate m C' j u).gates.length := by
            show (wiresFrom _ _).length = _; rw [wiresFrom_length]; simp
          have h2' : (C'.wires (List.ofFn x)).length = m + C'.gates.length := by
            show (wiresFrom _ _).length = _; rw [wiresFrom_length]; simp
          have hge1 : m + (deleteGate m C' j u).gates.length ≤ substWire (m + j) u C'.output := by
            rw [deleteGate_len m C' j u hj]; unfold substWire; split_ifs <;> omega
          rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      have hDmin : ∀ s' < D.gates.length, ¬ HasCircuitSize m (circuitFun m D) s' := by
        intro s' hs'; rw [hDfun]; exact hlb' s' (by omega)
      have hDred := min_reduced D hDnok hDmin (by rwa [hDfun])
      have hDnoNot : ∀ g ∈ D.gates, g.op ≠ GateOp.not :=
        hIH' D hDnok hDfun (by show D.gates.length ≤ opt' + 1; omega) hDred
      have hjeq : j = k₀ := by
        by_contra hne
        by_cases hlt : k₀ < j
        · have hkD : k₀ < D.gates.length := by omega
          have hget := deleteGate_getElem_lt m C' j u k₀ hj hlt
          have hnotD := hDnoNot (D.gates[k₀]'hkD) (List.getElem_mem hkD)
          change ((deleteGate m C' j u).gates[k₀]'(by rw [← hD]; exact hkD)).op ≠ GateOp.not at hnotD
          rw [hget] at hnotD; exact hnotD hk₀_not
        · have hgt : j < k₀ := by omega
          have hkD : k₀ - 1 < D.gates.length := by omega
          have hget := deleteGate_getElem_gt m C' j u k₀ hj hk₀_lt hgt
          have hnotD := hDnoNot (D.gates[k₀ - 1]'hkD) (List.getElem_mem hkD)
          change ((deleteGate m C' j u).gates[k₀ - 1]'(by rw [← hD]; exact hkD)).op ≠ GateOp.not at hnotD
          rw [hget] at hnotD; exact hnotD hk₀_not
      subst hjeq
      have hins_k₀ : ∃ a', a' < m + k₀ ∧ (C'.gates[k₀]'hk₀_lt).inputs = [a'] := by
        have hlen1 := (hnok' _ (List.getElem_mem hk₀_lt)).2 hk₀_not
        rcases hins : (C'.gates[k₀]'hk₀_lt).inputs with _ | ⟨a', _ | ⟨b', l⟩⟩
        · exfalso
          have hconst : ∀ x y : Fin m → Bool,
              (C'.wires (List.ofFn x)).getD (m + k₀) false = (C'.wires (List.ofFn y)).getD (m + k₀) false := by
            intro x y; rw [wire_eval_gate C' k₀ hk₀_lt x, wire_eval_gate C' k₀ hk₀_lt y, hk₀_not, hins]; rfl
          obtain ⟨x, y, hne⟩ := h1 k₀ hk₀_lt
          exact hne (hconst x y)
        · have hmem_a' : a' ∈ ((elimPass m C.gates (initVar m v b, [])).2[k₀]'hk₀_lt).inputs := by
            change a' ∈ (C'.gates[k₀]'hk₀_lt).inputs; rw [hins]; simp
          have ha'lt : a' < m + k₀ := elim_emit_wf m C.gates v b hnok k₀ hk₀_lt a' hmem_a'
          exact ⟨a', ha'lt, rfl⟩
        · rw [hins] at hlen1; simp at hlen1
      obtain ⟨a', ha'lt, hins'⟩ := hins_k₀
      let x0 : Fin m → Bool := fun _ => false
      have hwD_a' : (D.wires (List.ofFn x0)).getD a' false = false :=
        no_not_eval_false D hDnok hDred hDnoNot a' (by omega)
      have hwD_u : (D.wires (List.ofFn x0)).getD u false = false :=
        no_not_eval_false D hDnok hDred hDnoNot u (by omega)
      have hwC_a' : (C'.wires (List.ofFn x0)).getD a' false = false := by
        have h := deleteGate_wires_eq m C' k₀ u hk₀_lt huj (List.ofFn x0) (by simp) (heq x0).symm a' (by omega)
        have hsub : substWire (m + k₀) u a' = a' := by simp [substWire, ha'lt]
        rw [hsub, ← hD, hwD_a'] at h; exact h.symm
      have hwC_u : (C'.wires (List.ofFn x0)).getD u false = false := by
        have h := deleteGate_wires_eq m C' k₀ u hk₀_lt huj (List.ofFn x0) (by simp) (heq x0).symm u (by omega)
        have hsub : substWire (m + k₀) u u = u := by simp [substWire, huj]
        rw [hsub, ← hD, hwD_u] at h; exact h.symm
      have hwC_k₀ : (C'.wires (List.ofFn x0)).getD (m + k₀) false = true := by
        rw [wire_eval_gate C' k₀ hk₀_lt x0, hk₀_not, hins']
        simp only [ha'lt, ↓reduceIte, hwC_a', GateOp.eval, List.map_cons, List.map_nil,
          List.headD_cons, Bool.not_false]
      have hcontr := heq x0
      rw [hwC_u, hwC_k₀] at hcontr
      exact Bool.noConfusion hcontr
  · -- Violation 1: constant gate j in C'
    push Not at h1
    obtain ⟨j, hj, hconst_all⟩ := h1
    set c := (C'.wires (List.ofFn (fun _ : Fin m => false))).getD (m + j) false
    have hconst : ∀ x : Fin m → Bool, (C'.wires (List.ofFn x)).getD (m + j) false = c :=
      fun x => hconst_all x (fun _ => false)
    have hout_ne : C'.output ≠ m + j := by
      intro heq
      obtain ⟨x, y, hne⟩ := hnc'
      rw [← hfun'] at hne
      have hx : circuitFun m C' x = c := by show (C'.wires _).getD C'.output false = c; rw [heq]; exact hconst x
      have hy : circuitFun m C' y = c := by show (C'.wires _).getD C'.output false = c; rw [heq]; exact hconst y
      exact hne (hx.trans hy.symm)
    by_cases hread : ∃ r : ℕ, ∃ hr : r < C'.gates.length, j < r ∧ (m + j) ∈ C'.gates[r].inputs
    · exfalso
      obtain ⟨r, hr, hjr, hmem⟩ := hread
      have h2 := deleteConstGate_two C' hnok' j r hj hr hjr hmem c hconst (by rwa [hfun'])
      rw [hfun', hlen_eq] at h2
      exact hlb' (opt' + 1 - 2) (by omega) h2
    · have hno_read : ∀ r : ℕ, (hr : r < C'.gates.length) → j < r → (m + j) ∉ C'.gates[r].inputs :=
        fun r hr hjr hmem => hread ⟨r, hr, hjr, hmem⟩
      obtain ⟨hjk, huniq⟩ := hdead_kill j hj hout_ne hno_read
      subst hjk
      exact ⟨out, hout_st, hlen_eq, hout_ne, hno_read, huniq⟩

private lemma dead_wire_in_elim {m : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hred : Reduced m C) (v : Fin m) (b : Bool)
    (hnc : ∃ x x' : Fin m → Bool,
      circuitFun m C (Function.update x v b) ≠ circuitFun m C (Function.update x' v b))
    (j₀ : ℕ) (hj₀ : j₀ < C.gates.length) (hnd : j₀ ∉ elimDropped m C.gates (initVar m v b, []))
    (out : ℕ)
    (hout_st : (elimPass m C.gates (initVar m v b, [])).1.getD C.output (Sum.inl false) = Sum.inr out)
    (hout_ne : out ≠ m + (elimState m C.gates (initVar m v b, []) j₀).2.length)
    (hdead : ∀ r : ℕ, (hr : r < (elimPass m C.gates (initVar m v b, [])).2.length) →
      (elimState m C.gates (initVar m v b, []) j₀).2.length < r →
      (m + (elimState m C.gates (initVar m v b, []) j₀).2.length) ∉
        (elimPass m C.gates (initVar m v b, [])).2[r].inputs) :
    let k₀ := (elimState m C.gates (initVar m v b, []) j₀).2.length
    ∃ k r : ℕ, ∃ (hk : k < C.gates.length) (hr : r < C.gates.length) (c : Bool),
      j₀ < k ∧ k < r ∧
      k ∈ elimDropped m C.gates (initVar m v b, []) ∧
      r ∈ elimDropped m C.gates (initVar m v b, []) ∧
      (elimState m C.gates (initVar m v b, []) (k + 1)).1.getD (m + k) (Sum.inl false) = Sum.inl c ∧
      (∃ u < m + k, u ∈ C.gates[k].inputs ∧
        (elimState m C.gates (initVar m v b, []) k).1.getD u (Sum.inl false) = Sum.inr (m + k₀)) ∧
      (m + k) ∈ C.gates[r].inputs := by
  classical
  intro k₀
  set init := (initVar m v b, ([] : List Gate)) with hinit
  set acc := elimPass m C.gates init with hacc
  have hlen_init : init.1.length = m := by simp [hinit, initVar]
  obtain ⟨_, _, _, _, _, hst_j₀⟩ := elim_emit_at m C.gates init j₀ hj₀ hnd
  rw [hlen_init] at hst_j₀
  have hacc_j₀ : acc.1.getD (m + j₀) (Sum.inl false) = Sum.inr (m + k₀) := by
    rw [hacc, ← elimState_end,
      elimState_getD_mono m C.gates init (j₀ + 1) C.gates.length (m + j₀) _ (by omega) le_rfl (by omega)]
    exact hst_j₀
  set S : Finset ℕ := (Finset.range (m + C.gates.length)).filter
    (fun u => acc.1.getD u (Sum.inl false) = Sum.inr (m + k₀)) with hS
  have hS_ne : S.Nonempty :=
    ⟨m + j₀, Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hacc_j₀⟩⟩
  set u := S.max' hS_ne with hu
  have hu_mem : u ∈ S := Finset.max'_mem S hS_ne
  have hu_le : m + j₀ ≤ u := Finset.le_max' S (m + j₀)
    (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hacc_j₀⟩)
  obtain ⟨hu_lt, hu_st⟩ := Finset.mem_filter.1 hu_mem
  rw [Finset.mem_range] at hu_lt
  set ju := u - m with hju
  have hu_eq : u = m + ju := by omega
  have hju_lt : ju < C.gates.length := by omega
  have hout_ne_u : C.output ≠ m + ju := by
    intro heq
    rw [heq, ← hu_eq, hu_st] at hout_st
    exact hout_ne (Sum.inr.inj hout_st).symm
  obtain ⟨k, hk, hjuk, hmem_uk⟩ := (reduced_no_dead C hnok hred ju hju_lt).resolve_left hout_ne_u
  have hst_uk : (elimState m C.gates init k).1.getD (m + ju) (Sum.inl false) = Sum.inr (m + k₀) := by
    have hmono := elimState_getD_mono m C.gates init k C.gates.length (m + ju) (Sum.inl false)
      (by omega) le_rfl (by rw [hlen_init]; omega)
    rw [elimState_end, ← hacc] at hmono
    rw [← hmono, ← hu_eq, hu_st]
  have hdrop_k : k ∈ elimDropped m C.gates init := by
    by_contra hnd_k
    obtain ⟨g_k, hg_k, _, hk'_lt, hk'_eq, _⟩ := elim_emit_at m C.gates init k hk hnd_k
    set k' := (elimState m C.gates init k).2.length
    have hlt_k' : k₀ < k' := by
      have h1 : (elimState m C.gates init (j₀ + 1)).2.length = k₀ + 1 := by
        obtain ⟨g0, hg0, _, _, _, _⟩ := elim_emit_at m C.gates init j₀ hj₀ hnd
        rw [elimState_succ m C.gates init j₀ hj₀, elimStep, hg0]; simp [k₀, hinit]
      have h2 := elimState_snd_mono m C.gates init (j₀ + 1) k (by omega)
      omega
    have hmem_ins : Sum.inr (m + k₀) ∈ (C.gates[k].inputs.map fun i =>
        (elimState m C.gates init k).1.getD i (Sum.inl false)) :=
      List.mem_map.2 ⟨m + ju, hmem_uk, hst_uk⟩
    have hmem_gk := simplifyGate_some_mem_inputs C.gates[k].op (m + k') _
      (fun hop => by simp [(hnok _ (List.getElem_mem hk)).2 hop]) g_k hg_k (m + k₀) hmem_ins
    have hmem_acc : (m + k₀) ∈ acc.2[k'].inputs := by rw [hk'_eq]; exact hmem_gk
    exact hdead k' hk'_lt hlt_k' hmem_acc
  have hst_k_const : ∃ c : Bool,
      (elimState m C.gates init (k + 1)).1.getD (m + k) (Sum.inl false) = Sum.inl c := by
    cases hstk : (elimState m C.gates init (k + 1)).1.getD (m + k) (Sum.inl false) with
    | inl c => exact ⟨c, rfl⟩
    | inr w' =>
      exfalso
      have hget := elimState_getD_at m C.gates init k hk
      rw [hlen_init] at hget
      rw [hget] at hstk
      have hnone_k : (simplifyGate C.gates[k].op (m + (elimState m C.gates init k).2.length)
          (C.gates[k].inputs.map fun i => (elimState m C.gates init k).1.getD i (Sum.inl false))).1 = none := by
        rw [elimDropped, Finset.mem_filter, Finset.mem_range] at hdrop_k
        have h2 := hdrop_k.2
        simp only [hk, ↓reduceDIte] at h2
        exact Option.isNone_iff_eq_none.1 h2
      have hmem_ins : Sum.inr (m + k₀) ∈ (C.gates[k].inputs.map fun i =>
          (elimState m C.gates init k).1.getD i (Sum.inl false)) :=
        List.mem_map.2 ⟨m + ju, hmem_uk, hst_uk⟩
      have hw'_eq := simplifyGate_none_of_inr_mem C.gates[k].op _ _
        (hnok _ (List.getElem_mem hk)).1.1 (by simp [(hnok _ (List.getElem_mem hk)).1.2])
        (fun hop => by simp [(hnok _ (List.getElem_mem hk)).2 hop]) hnone_k (m + k₀) w' hmem_ins hstk
      have hacc_k : acc.1.getD (m + k) (Sum.inl false) = Sum.inr (m + k₀) := by
        rw [hacc, ← elimState_end,
          elimState_getD_mono m C.gates init (k + 1) C.gates.length (m + k) _ (by omega) le_rfl (by omega),
          hget, hstk, hw'_eq]
      have hk_in_S : m + k ∈ S := Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hacc_k⟩
      have hle_u := Finset.le_max' S (m + k) hk_in_S
      omega
  obtain ⟨c, hc⟩ := hst_k_const
  obtain ⟨_, r, hr, hkr, hmem_kr, hdrop_r⟩ :=
    elim_const_not_output_and_consumer C hnok hred v b hnc k hk c hc
  exact ⟨k, r, hk, hr, c, by omega, hkr, hdrop_k, hdrop_r, hc,
    ⟨m + ju, by omega, hmem_uk, hst_uk⟩, hmem_kr⟩

private lemma elim_delta1_contra {m opt : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hred : Reduced m C) (hsz : C.gates.length ≤ opt + 1)
    (v : Fin m) (b : Bool)
    (hinc : ∃ x : Fin m → Bool,
      circuitFun m C (Function.update x v false) = false ∧
      circuitFun m C (Function.update x v true) = true)
    (f' : (Fin m → Bool) → Bool)
    (hf'_eq : f' = fun x => circuitFun m C (Function.update x v b))
    (hnc' : ∃ x y : Fin m → Bool, f' x ≠ f' y)
    (hlb' : ∀ s' < opt - 1, ¬ HasCircuitSize m f' s')
    (hopt_pos : 1 ≤ opt)
    (hIH' : ∀ D : Circuit, (∀ g ∈ D.gates, NOkGate g) → circuitFun m D = f' →
      D.size ≤ (opt - 1) + 1 → Reduced m D → ∀ g ∈ D.gates, g.op ≠ GateOp.not)
    (j₀ : ℕ) (hj₀ : j₀ < C.gates.length) (hj₀_op : C.gates[j₀].op = GateOp.not) :
    False := by
  let init := (initVar m v b, ([] : List Gate))
  let D := elimDropped m C.gates init
  have hnc_upd : ∃ x x' : Fin m → Bool,
      circuitFun m C (Function.update x v b) ≠ circuitFun m C (Function.update x' v b) := by
    obtain ⟨x, x', hne⟩ := hnc'
    exact ⟨x, x', by simpa [hf'_eq] using hne⟩
  obtain ⟨out, hout_st, _, hcard, hfun_acc⟩ := elim_var_circuit C hnok v b hnc_upd
  have hcard' : (elimPass m C.gates init).2.length + D.card = C.gates.length := hcard
  have hlb_len : opt - 1 ≤ (elimPass m C.gates init).2.length := by
    by_contra hlt
    exact hlb' (elimPass m C.gates init).2.length (by omega)
      ⟨⟨(elimPass m C.gates init).2, out⟩, elimPass_ok m C.gates init (by simp [init]), le_rfl,
        fun x => by rw [hf'_eq]; exact congrFun hfun_acc x⟩
  -- Since f depends on v, at least 1 gate reads v, so D.card ≥ 1
  have hD_pos : 1 ≤ D.card := by
    by_contra h0
    have hD0 : D = ∅ := Finset.card_eq_zero.1 (by omega)
    have hno_v : ∀ j : ℕ, (hj : j < C.gates.length) → (v : ℕ) ∉ C.gates[j].inputs := by
      intro j hj hmem
      have hdrop_j : j ∈ D := by
        apply mem_elimDropped_of_const m C.gates init j hj (hnok _ (List.getElem_mem hj)) (v : ℕ) hmem
        refine ⟨b, ?_⟩
        rw [elimState_getD_mono m C.gates init 0 j (v : ℕ) _ (Nat.zero_le _) (by omega)
          (by simp [init, initVar]), elimState_zero]; dsimp only [init]; rw [initVar, ofFn_getD_lt _ _ _ v.isLt]
        simp
      rw [hD0] at hdrop_j; exact Finset.notMem_empty j hdrop_j
    obtain ⟨x, hx0, hx1⟩ := hinc
    have hne : C.gates ≠ [] := List.ne_nil_of_length_pos (by omega)
    have hout := hred.2.2.1 hne
    have heq := wire_indep_of_not_read C v hno_v C.gates.length le_rfl C.output (by omega) (by omega) x
    change circuitFun m C (Function.update x v false) = circuitFun m C (Function.update x v true) at heq
    rw [hx0, hx1] at heq; exact Bool.noConfusion heq
  -- D.card ≤ 2 (else acc.2.length ≤ opt - 2 < opt - 1)
  have hD_le2 : D.card ≤ 2 := by omega
  by_cases hD1 : D.card = 1
  · -- Case d = 1: no NOT gate can be dropped (else its consumer drops too → D.card ≥ 2)
    have hnd : j₀ ∉ D := by
      intro hdrop
      obtain ⟨a, c, _, _, _, hst, _⟩ := elim_dropped_not_const C hnok hred v b j₀ hj₀ hdrop hj₀_op
      obtain ⟨_, k, hk, hjk, _, hdrop_k⟩ := elim_const_not_output_and_consumer C hnok hred v b hnc_upd j₀ hj₀ (!c) hst
      have hsub : ({j₀, k} : Finset ℕ) ⊆ D := by
        intro u hu; simp at hu; rcases hu with rfl | rfl <;> assumption
      have hc2 : ({j₀, k} : Finset ℕ).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
      have := Finset.card_le_card hsub
      omega
    obtain ⟨out', hout_st', _, hout_ne, hdead, _⟩ :=
      elim_not_survives_or_dead C hnok v b f' hf'_eq hnc' hlb' hIH' (by change (elimPass m C.gates init).2.length ≤ opt - 1 + 1; omega) j₀ hj₀ hnd hj₀_op
    obtain ⟨k, r, _, _, _, _, hkr, hdk, hdr, _, _, _⟩ :=
      dead_wire_in_elim C hnok hred v b hnc_upd j₀ hj₀ hnd out' hout_st' hout_ne hdead
    have hsub : ({k, r} : Finset ℕ) ⊆ D := by
      intro u hu; simp at hu; rcases hu with rfl | rfl <;> assumption
    have hc2 : ({k, r} : Finset ℕ).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
    have := Finset.card_le_card hsub
    omega
  · -- Case d = 2: acc.2.length = opt - 1 (minimal, hence NO NOT gates in acc.2!)
    have hD2 : D.card = 2 := by omega
    have hacc_len : (elimPass m C.gates init).2.length = opt - 1 := by omega
    set C' : Circuit := ⟨(elimPass m C.gates init).2, out⟩ with hC'
    have hC'_len : C'.gates.length = (elimPass m C.gates init).2.length := rfl
    have hnok' : ∀ g ∈ C'.gates, NOkGate g := elimPass_nok m C.gates init (by simp [init])
    have hfun' : circuitFun m C' = f' := hfun_acc.trans hf'_eq.symm
    have hmin' : ∀ s' < C'.gates.length, ¬ HasCircuitSize m (circuitFun m C') s' := by
      intro s' hs'; rw [hfun']; exact hlb' s' (by omega)
    have hred' := min_reduced C' hnok' hmin' (by rwa [hfun'])
    have hnoNot' : ∀ g ∈ C'.gates, g.op ≠ GateOp.not :=
      hIH' C' hnok' hfun' (by show C'.gates.length ≤ (opt - 1) + 1; omega) hred'
    have hdrop_all_not : ∀ j : ℕ, (hj : j < C.gates.length) → C.gates[j].op = GateOp.not → j ∈ D := by
      intro j hj hop
      by_contra hnd
      obtain ⟨g', _, hg'op, hklt, hkeq, _⟩ := elim_emit_at m C.gates init j hj hnd
      have hne := hnoNot' (C'.gates[(elimState m C.gates init j).2.length]'hklt) (List.getElem_mem hklt)
      change ((elimPass m C.gates init).2[(elimState m C.gates init j).2.length]'hklt).op ≠ GateOp.not at hne
      rw [hkeq, hg'op, hop] at hne; exact hne rfl
    have hdrop_j₀ : j₀ ∈ D := hdrop_all_not j₀ hj₀ hj₀_op
    obtain ⟨a, c, ha, hins, _, hst_j₀, hne_v⟩ :=
      elim_dropped_not_const C hnok hred v b j₀ hj₀ hdrop_j₀ hj₀_op
    obtain ⟨_, k, hk, hjk, hmem_k, hdrop_k⟩ :=
      elim_const_not_output_and_consumer C hnok hred v b hnc_upd j₀ hj₀ (!c) hst_j₀
    have ha_eq_v : a = (v : ℕ) := by
      by_contra hne
      obtain ⟨hge, hdrop_am, _⟩ := hne_v hne
      have hsub : ({a - m, j₀, k} : Finset ℕ) ⊆ D := by
        intro u hu; simp at hu; rcases hu with rfl | rfl | rfl <;> assumption
      have hc3 : ({a - m, j₀, k} : Finset ℕ).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp; omega),
            Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
      have := Finset.card_le_card hsub
      omega
    have hD_eq : D = {j₀, k} := by
      have hsub : ({j₀, k} : Finset ℕ) ⊆ D := by
        intro u hu; simp at hu; rcases hu with rfl | rfl <;> assumption
      have hc2 : ({j₀, k} : Finset ℕ).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
      exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
    have hnot_eq : C.gates[j₀] = ⟨GateOp.not, [(v : ℕ)]⟩ := by
      cases hg : C.gates[j₀] with
      | mk op ins =>
        rw [hg] at hj₀_op hins
        simp only at hj₀_op hins
        subst hj₀_op; subst hins; subst ha_eq_v; rfl
    have hk_ne_not : C.gates[k].op ≠ GateOp.not :=
      elim_not_consumer_ne_not C hnok hred j₀ k (v : ℕ) hj₀ hk hjk (by omega) hnot_eq hmem_k
    have hnot_uniq : ∀ j : ℕ, (hj : j < C.gates.length) → C.gates[j].op = GateOp.not → j = j₀ := by
      intro j hj hop
      have hmem : j ∈ D := hdrop_all_not j hj hop
      rw [hD_eq] at hmem; simp at hmem
      rcases hmem with hjeq | hjeq
      · exact hjeq
      · subst hjeq; exact absurd hop hk_ne_not
    have hv_uniq : ∀ j : ℕ, (hj : j < C.gates.length) → (v : ℕ) ∈ C.gates[j].inputs → j = j₀ := by
      intro j hj hmem_v
      have hdrop_j : j ∈ D := by
        apply mem_elimDropped_of_const m C.gates init j hj (hnok _ (List.getElem_mem hj)) (v : ℕ) hmem_v
        refine ⟨b, ?_⟩
        rw [elimState_getD_mono m C.gates init 0 j (v : ℕ) _ (Nat.zero_le _) (by omega)
          (by simp [init, initVar]), elimState_zero]; dsimp only [init]; rw [initVar, ofFn_getD_lt _ _ _ v.isLt]
        simp
      rw [hD_eq] at hdrop_j; simp at hdrop_j
      rcases hdrop_j with hjeq | hjeq
      · exact hjeq
      · subst hjeq
        exact absurd hmem_v
          (elim_gate_not_both_a_and_not_a C hnok hred j₀ j (v : ℕ) hj₀ hj hjk (by omega) hnot_eq hmem_k)
    obtain ⟨x, hx0, hx1⟩ := hinc
    have hanti := single_not_antimono_direct C hnok hred v j₀ hj₀ hnot_eq hnot_uniq hv_uniq x hx1
    rw [hx0] at hanti; exact Bool.noConfusion hanti

/-- When `d = 3` and `acc.2.length = opt - 2` (minimal, no NOT gates), and `C` has a NOT gate,
    we derive a contradiction directly! -/
private lemma elim_delta2_d3_contra {m opt : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hred : Reduced m C) (hsz : C.gates.length ≤ opt + 1)
    (v : Fin m) (b : Bool)
    (hinc : ∃ x : Fin m → Bool,
      circuitFun m C (Function.update x v false) = false ∧
      circuitFun m C (Function.update x v true) = true)
    (hopt_ge2 : 2 ≤ opt)
    (f0 f1 : (Fin m → Bool) → Bool)
    (hf0_eq : f0 = fun x => circuitFun m C (Function.update x v false))
    (hf1_eq : f1 = fun x => circuitFun m C (Function.update x v true))
    (hnc0 : ∃ x y : Fin m → Bool, f0 x ≠ f0 y)
    (hnc1 : ∃ x y : Fin m → Bool, f1 x ≠ f1 y)
    (hlb0 : ∀ s' < opt - 2, ¬ HasCircuitSize m f0 s')
    (hlb1 : ∀ s' < opt - 2, ¬ HasCircuitSize m f1 s')
    (hIHb : ∀ D : Circuit, (∀ g ∈ D.gates, NOkGate g) →
      circuitFun m D = (if b then f1 else f0) →
      D.size ≤ (opt - 2) + 1 → Reduced m D → ∀ g ∈ D.gates, g.op ≠ GateOp.not)
    (hd3 : (elimDropped m C.gates (initVar m v b, [])).card = 3)
    (j₀ : ℕ) (hj₀ : j₀ < C.gates.length) (hj₀_op : C.gates[j₀].op = GateOp.not) :
    False := by
  classical
  let init := (initVar m v b, ([] : List Gate))
  let D := elimDropped m C.gates init
  have hnc_b : ∃ x x' : Fin m → Bool,
      circuitFun m C (Function.update x v b) ≠ circuitFun m C (Function.update x' v b) := by
    cases b
    · obtain ⟨x, x', hne⟩ := hnc0; exact ⟨x, x', by simpa [hf0_eq] using hne⟩
    · obtain ⟨x, x', hne⟩ := hnc1; exact ⟨x, x', by simpa [hf1_eq] using hne⟩
  have hlb_b : ∀ s' < opt - 2, ¬ HasCircuitSize m (if b then f1 else f0) s' := by
    cases b <;> assumption
  have hfb_eq : (if b then f1 else f0) = fun x => circuitFun m C (Function.update x v b) := by
    cases b <;> simp [hf0_eq, hf1_eq]
  obtain ⟨out, _, _, hcard, hfun_acc⟩ := elim_var_circuit C hnok v b hnc_b
  have hcard' : (elimPass m C.gates init).2.length + D.card = C.gates.length := hcard
  have hacc_ge : opt - 2 ≤ (elimPass m C.gates init).2.length := by
    by_contra hlt
    exact hlb_b (elimPass m C.gates init).2.length (by omega)
      ⟨⟨(elimPass m C.gates init).2, out⟩, elimPass_ok m C.gates init (by simp [init]), le_rfl,
        fun x => by rw [hfb_eq]; exact congrFun hfun_acc x⟩
  have hD3 : D.card = 3 := hd3
  have hacc_len : (elimPass m C.gates init).2.length = opt - 2 := by omega
  set C' : Circuit := ⟨(elimPass m C.gates init).2, out⟩ with hC'
  have hC'_len : C'.gates.length = (elimPass m C.gates init).2.length := rfl
  have hnok' : ∀ g ∈ C'.gates, NOkGate g := elimPass_nok m C.gates init (by simp [init])
  have hfun' : circuitFun m C' = (if b then f1 else f0) := hfun_acc.trans hfb_eq.symm
  have hmin' : ∀ s' < C'.gates.length, ¬ HasCircuitSize m (circuitFun m C') s' := by
    intro s' hs'; rw [hfun']; exact hlb_b s' (by omega)
  have hred' := min_reduced C' hnok' hmin' (by rw [hfun', hfb_eq]; exact hnc_b)
  have hnoNot' : ∀ g ∈ C'.gates, g.op ≠ GateOp.not :=
    hIHb C' hnok' hfun' (by show C'.gates.length ≤ (opt - 2) + 1; omega) hred'
  have hdrop_all_not : ∀ j : ℕ, (hj : j < C.gates.length) → C.gates[j].op = GateOp.not → j ∈ D := by
    intro j hj hop
    by_contra hnd
    obtain ⟨g', _, hg'op, hklt, hkeq, _⟩ := elim_emit_at m C.gates init j hj hnd
    have hne := hnoNot' (C'.gates[(elimState m C.gates init j).2.length]'hklt) (List.getElem_mem hklt)
    change ((elimPass m C.gates init).2[(elimState m C.gates init j).2.length]'hklt).op ≠ GateOp.not at hne
    rw [hkeq, hg'op, hop] at hne; exact hne rfl
  have hdrop_v : ∀ j : ℕ, (hj : j < C.gates.length) → (v : ℕ) ∈ C.gates[j].inputs → j ∈ D := by
    intro j hj hmem
    apply mem_elimDropped_of_const m C.gates init j hj (hnok _ (List.getElem_mem hj)) (v : ℕ) hmem
    refine ⟨b, ?_⟩
    rw [elimState_getD_mono m C.gates init 0 j (v : ℕ) _ (Nat.zero_le _) (by omega)
      (by simp [init, initVar]), elimState_zero]; dsimp only [init]; rw [initVar, ofFn_getD_lt _ _ _ v.isLt]
    simp
  have hdrop_j₀ : j₀ ∈ D := hdrop_all_not j₀ hj₀ hj₀_op
  obtain ⟨a, c, ha, hins, hsta, hst_j₀, hne_v⟩ :=
    elim_dropped_not_const C hnok hred v b j₀ hj₀ hdrop_j₀ hj₀_op
  obtain ⟨_, k, hk, hjk, hmem_k, hdrop_k⟩ :=
    elim_const_not_output_and_consumer C hnok hred v b hnc_b j₀ hj₀ (!c) hst_j₀
  by_cases hav : a = (v : ℕ)
  · -- Subcase A: j₀ = NOT(v)
    have hnot_eq : C.gates[j₀] = ⟨GateOp.not, [(v : ℕ)]⟩ := by
      cases hg : C.gates[j₀] with
      | mk op ins =>
        rw [hg] at hj₀_op hins; simp only at hj₀_op hins
        subst hj₀_op; subst hins; subst hav; rfl
    by_cases hother_v : ∃ g₂ : ℕ, ∃ hg₂ : g₂ < C.gates.length, g₂ ≠ j₀ ∧ (v : ℕ) ∈ C.gates[g₂].inputs
    · -- At least 2 gates read v: switch to b' where g₂ becomes constant → ≥ 4 dropped gates!
      obtain ⟨g₂, hg₂, hg₂_ne, hg₂_v⟩ := hother_v
      have hg₂_ne_not : C.gates[g₂].op ≠ GateOp.not := by
        intro hop
        obtain ⟨u, _, hu_ins⟩ := (reduced_gate_wf C hnok hred g₂ hg₂).1 hop
        rw [hu_ins] at hg₂_v; simp at hg₂_v; subst hg₂_v
        have hsame : ∀ x : Fin m → Bool,
            (C.wires (List.ofFn x)).getD (m + j₀) false = (C.wires (List.ofFn x)).getD (m + g₂) false := by
          intro x
          rw [wire_eval_gate C j₀ hj₀ x, hnot_eq, wire_eval_gate C g₂ hg₂ x, hop, hu_ins]
          simp [show (v : ℕ) < m + j₀ by omega, show (v : ℕ) < m + g₂ by omega, GateOp.eval]
        by_cases hlt : j₀ < g₂
        · obtain ⟨x, hne⟩ := hred.2.1 (m + j₀) g₂ (by omega) hg₂
          exact hne (hsame x)
        · obtain ⟨x, hne⟩ := hred.2.1 (m + g₂) j₀ (by omega) hj₀
          exact hne (hsame x).symm
      have hg₂_bin : C.gates[g₂].op = GateOp.and ∨ C.gates[g₂].op = GateOp.or := by
        rcases (hnok _ (List.getElem_mem hg₂)).1.1 with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h hg₂_ne_not
      -- Pick b' = false if g₂ is AND, true if g₂ is OR
      set b' : Bool := if C.gates[g₂].op = GateOp.and then false else true with hb'
      let init' := (initVar m v b', ([] : List Gate))
      let D' := elimDropped m C.gates init'
      have hnc_b' : ∃ x x' : Fin m → Bool,
          circuitFun m C (Function.update x v b') ≠ circuitFun m C (Function.update x' v b') := by
        cases b'
        · obtain ⟨x, x', hne⟩ := hnc0; exact ⟨x, x', by simpa [hf0_eq] using hne⟩
        · obtain ⟨x, x', hne⟩ := hnc1; exact ⟨x, x', by simpa [hf1_eq] using hne⟩
      have hlb_b' : ∀ s' < opt - 2, ¬ HasCircuitSize m (fun x => circuitFun m C (Function.update x v b')) s' := by
        cases b'
        · simpa [← hf0_eq] using hlb0
        · simpa [← hf1_eq] using hlb1
      have hv_st' : ∀ t ≤ C.gates.length,
          (elimState m C.gates init' t).1.getD (v : ℕ) (Sum.inl false) = Sum.inl b' := by
        intro t ht
        rw [elimState_getD_mono m C.gates init' 0 t (v : ℕ) _ (Nat.zero_le _) ht (by simp [init', initVar]),
          elimState_zero]; dsimp only [init']; rw [initVar, ofFn_getD_lt _ _ _ v.isLt]; simp
      have hdrop_j₀' : j₀ ∈ D' :=
        mem_elimDropped_of_const m C.gates init' j₀ hj₀ (hnok _ (List.getElem_mem hj₀)) (v : ℕ)
          (by rw [hnot_eq]; simp) ⟨b', hv_st' j₀ (by omega)⟩
      have hst_j₀' : (elimState m C.gates init' (j₀ + 1)).1.getD (m + j₀) (Sum.inl false) = Sum.inl (!b') := by
        have hget := elimState_getD_at m C.gates init' j₀ hj₀
        have hlen : init'.1.length = m := by simp [init', initVar]
        rw [hlen] at hget; rw [hget, hnot_eq]
        simp only [List.map_cons, List.map_nil, hv_st' j₀ (by omega), simplifyGate, simpNot]
      obtain ⟨_, k', hk', hjk', hmem_k', hdrop_k'⟩ :=
        elim_const_not_output_and_consumer C hnok hred v b' hnc_b' j₀ hj₀ (!b') hst_j₀'
      have hdrop_g₂' : g₂ ∈ D' :=
        mem_elimDropped_of_const m C.gates init' g₂ hg₂ (hnok _ (List.getElem_mem hg₂)) (v : ℕ)
          hg₂_v ⟨b', hv_st' g₂ (by omega)⟩
      have hst_g₂' : (elimState m C.gates init' (g₂ + 1)).1.getD (m + g₂) (Sum.inl false) = Sum.inl b' := by
        have hget := elimState_getD_at m C.gates init' g₂ hg₂
        have hlen : init'.1.length = m := by simp [init', initVar]
        rw [hlen] at hget; rw [hget]
        have hmem_v' : Sum.inl b' ∈ (C.gates[g₂].inputs.map fun i =>
            (elimState m C.gates init' g₂).1.getD i (Sum.inl false)) :=
          List.mem_map.2 ⟨(v : ℕ), hg₂_v, hv_st' g₂ (by omega)⟩
        rcases hg₂_bin with hop | hop
        · have hb'f : b' = false := by simp [hb', hop]
          rw [hb'f] at hmem_v' ⊢; rw [hop]
          rw [simplifyGate_and_false _ _ (by simp [(hnok _ (List.getElem_mem hg₂)).1.2]) hmem_v']
        · have hb't : b' = true := by simp [hb', hop]
          rw [hb't] at hmem_v' ⊢; rw [hop]
          rw [simplifyGate_or_true _ _ (by simp [(hnok _ (List.getElem_mem hg₂)).1.2]) hmem_v']
      obtain ⟨_, r', hr', hg₂r', hmem_r', hdrop_r'⟩ :=
        elim_const_not_output_and_consumer C hnok hred v b' hnc_b' g₂ hg₂ b' hst_g₂'
      have hg₂_ne_k' : g₂ ≠ k' := fun heq =>
        elim_gate_not_both_a_and_not_a C hnok hred j₀ k' (v : ℕ) hj₀ hk' hjk' (by omega) hnot_eq hmem_k'
          (heq ▸ hg₂_v)
      have hr'_ne_j₀ : r' ≠ j₀ := by
        intro heq; subst heq; rw [hnot_eq] at hmem_r'; simp at hmem_r'; omega
      have hD'_ge4 : 4 ≤ D'.card := by
        by_cases hrk : r' = k'
        · subst hrk
          -- k' reads BOTH m + j₀ (const !b') AND m + g₂ (const b') → k' is const!
          have hk'_ne_not := elim_not_consumer_ne_not C hnok hred j₀ r' (v : ℕ) hj₀ hk' hjk' (by omega) hnot_eq hmem_k'
          have hk'_bin : C.gates[r'].op = GateOp.and ∨ C.gates[r'].op = GateOp.or := by
            rcases (hnok _ (List.getElem_mem hk')).1.1 with h | h | h
            · exact Or.inl h
            · exact Or.inr h
            · exact absurd h hk'_ne_not
          obtain ⟨u₁, u₂, _, _, hu12, hins_r'⟩ := (reduced_gate_wf C hnok hred r' hr').2 hk'_bin
          have hst_r'_const : ∃ e : Bool,
              (elimState m C.gates init' (r' + 1)).1.getD (m + r') (Sum.inl false) = Sum.inl e := by
            have hget := elimState_getD_at m C.gates init' r' hr'
            have hlen : init'.1.length = m := by simp [init', initVar]
            rw [hlen] at hget; rw [hget, hins_r']
            have h1 : (elimState m C.gates init' r').1.getD (m + j₀) (Sum.inl false) = Sum.inl (!b') := by
              rw [elimState_getD_mono m C.gates init' (j₀ + 1) r' (m + j₀) _ (by omega) (by omega)
                (by simp [init', initVar])]; exact hst_j₀'
            have h2 : (elimState m C.gates init' r').1.getD (m + g₂) (Sum.inl false) = Sum.inl b' := by
              rw [elimState_getD_mono m C.gates init' (g₂ + 1) r' (m + g₂) _ (by omega) (by omega)
                (by simp [init', initVar])]; exact hst_g₂'
            rw [hins_r'] at hmem_k' hmem_r'; simp at hmem_k' hmem_r'
            rcases hmem_k' with hk1 | hk1 <;> rcases hmem_r' with hr1 | hr1
            · exact absurd (hk1.trans hr1.symm) (by omega)
            · rw [← hk1, ← hr1]; simp only [List.map_cons, List.map_nil, h1, h2]
              obtain ⟨e, he⟩ := simplifyGate_both_const C.gates[r'].op _ (!b') b' hk'_bin
              exact ⟨e, by rw [he]⟩
            · rw [← hk1, ← hr1]; simp only [List.map_cons, List.map_nil, h1, h2]
              obtain ⟨e, he⟩ := simplifyGate_both_const C.gates[r'].op _ b' (!b') hk'_bin
              exact ⟨e, by rw [he]⟩
            · exact absurd (hk1.trans hr1.symm) (by omega)
          obtain ⟨e, he⟩ := hst_r'_const
          obtain ⟨_, s', hs', hr's', _, hdrop_s'⟩ :=
            elim_const_not_output_and_consumer C hnok hred v b' hnc_b' r' hr' e he
          have hsub : ({j₀, g₂, r', s'} : Finset ℕ) ⊆ D' := by
            intro u hu; simp at hu; rcases hu with rfl | rfl | rfl | rfl <;> assumption
          have hc4 : ({j₀, g₂, r', s'} : Finset ℕ).card = 4 := by
            rw [Finset.card_insert_of_notMem (by simp; omega),
                Finset.card_insert_of_notMem (by simp; omega),
                Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
          exact hc4 ▸ Finset.card_le_card hsub
        · have hsub : ({j₀, g₂, k', r'} : Finset ℕ) ⊆ D' := by
            intro u hu; simp at hu; rcases hu with rfl | rfl | rfl | rfl <;> assumption
          have hc4 : ({j₀, g₂, k', r'} : Finset ℕ).card = 4 := by
            rw [Finset.card_insert_of_notMem (by simp; omega),
                Finset.card_insert_of_notMem (by simp; omega),
                Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
          exact hc4 ▸ Finset.card_le_card hsub
      obtain ⟨out', _, _, hcard', hfun'⟩ := elim_var_circuit C hnok v b' hnc_b'
      exact hlb_b' (elimPass m C.gates init').2.length (by
        change (elimPass m C.gates (initVar m v b', [])).2.length < opt - 2
        have : (elimPass m C.gates (initVar m v b', [])).2.length + D'.card = C.gates.length := hcard'
        omega)
        ⟨⟨(elimPass m C.gates init').2, out'⟩, elimPass_ok m C.gates init' (by simp [init']), le_rfl,
          fun x => congrFun hfun' x⟩
    · -- Only j₀ reads v! Show j₀ is ALSO the unique NOT gate in C, then anti-monotone!
      have hv_uniq : ∀ j : ℕ, (hj : j < C.gates.length) → (v : ℕ) ∈ C.gates[j].inputs → j = j₀ := by
        intro j hj hmem; by_contra hne; exact hother_v ⟨j, hj, hne, hmem⟩
      have hnot_uniq : ∀ j : ℕ, (hj : j < C.gates.length) → C.gates[j].op = GateOp.not → j = j₀ := by
        intro j hj hop
        by_contra hne
        have hdj : j ∈ D := hdrop_all_not j hj hop
        obtain ⟨aj, cj, haj, hinsj, _, hstj, hnej⟩ :=
          elim_dropped_not_const C hnok hred v b j hj hdj hop
        have haj_ne_v : aj ≠ (v : ℕ) := fun heq =>
          hne (hv_uniq j hj (by rw [hinsj, heq]; simp))
        obtain ⟨hge_aj, hdrop_aj, _⟩ := hnej haj_ne_v
        have haj_ne_j₀ : aj - m ≠ j₀ := by
          intro heq
          have haj_eq : aj = m + j₀ := by omega
          exact elim_not_consumer_ne_not C hnok hred j₀ j (v : ℕ) hj₀ hj (by omega) (by omega) hnot_eq
            (by rw [hinsj, haj_eq]; simp) hop
        obtain ⟨_, kj, hkj, hjkj, hmem_kj, hdrop_kj⟩ :=
          elim_const_not_output_and_consumer C hnok hred v b hnc_b j hj (!cj) hstj
        have hkj_ne_j₀ : kj ≠ j₀ := by
          intro heq; subst heq; rw [hnot_eq] at hmem_kj; simp at hmem_kj; omega
        have hsub : ({j₀, aj - m, j, kj} : Finset ℕ) ⊆ D := by
          intro u hu; simp at hu; rcases hu with rfl | rfl | rfl | rfl <;> assumption
        have hc4 : ({j₀, aj - m, j, kj} : Finset ℕ).card = 4 := by
          rw [Finset.card_insert_of_notMem (by simp; omega),
              Finset.card_insert_of_notMem (by simp; omega),
              Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
        have := Finset.card_le_card hsub
        omega
      obtain ⟨x, hx0, hx1⟩ := hinc
      have hanti := single_not_antimono_direct C hnok hred v j₀ hj₀ hnot_eq hnot_uniq hv_uniq x hx1
      rw [hx0] at hanti; exact Bool.noConfusion hanti
  · -- Subcase B: a ≠ v, so a = m + j₁ with j₁ < j₀ < k, D = {j₁, j₀, k}
    obtain ⟨hge, hdrop_j₁, hst_j₁⟩ := hne_v hav
    set j₁ := a - m with hj₁_def
    have ha_eq : a = m + j₁ := by omega
    have hj₁ : j₁ < C.gates.length := by omega
    have hD_eq : D = {j₁, j₀, k} := by
      have hsub : ({j₁, j₀, k} : Finset ℕ) ⊆ D := by
        intro u hu; simp at hu; rcases hu with rfl | rfl | rfl <;> assumption
      have hc3 : ({j₁, j₀, k} : Finset ℕ).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp; omega),
            Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
      exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
    have hnot_eq : C.gates[j₀] = ⟨GateOp.not, [m + j₁]⟩ := by
      cases hg : C.gates[j₀] with
      | mk op ins =>
        rw [hg] at hj₀_op hins; simp only at hj₀_op hins
        subst hj₀_op; subst hins; rw [ha_eq]
    -- Neither j₁ nor k can be a NOT gate
    have hk_ne_not : C.gates[k].op ≠ GateOp.not :=
      elim_not_consumer_ne_not C hnok hred j₀ k (m + j₁) hj₀ hk hjk (by omega) hnot_eq hmem_k
    have hj₁_ne_not : C.gates[j₁].op ≠ GateOp.not := by
      intro hop
      obtain ⟨u, hu, hins1⟩ := (reduced_gate_wf C hnok hred j₁ hj₁).1 hop
      have h1_eq : C.gates[j₁] = ⟨GateOp.not, [u]⟩ := by
        cases hg : C.gates[j₁] with
        | mk op ins =>
          rw [hg] at hop hins1; simp only at hop hins1; subst hop; subst hins1; rfl
      exact elim_not_consumer_ne_not C hnok hred j₁ j₀ u hj₁ hj₀ (by omega) hu h1_eq
        (by rw [hnot_eq]; simp) hj₀_op
    have hnot_uniq : ∀ j : ℕ, (hj : j < C.gates.length) → C.gates[j].op = GateOp.not → j = j₀ := by
      intro j hj hop
      have hmem := hdrop_all_not j hj hop
      rw [hD_eq] at hmem; simp at hmem
      rcases hmem with hjeq | hjeq | hjeq
      · subst hjeq; exact absurd hop hj₁_ne_not
      · exact hjeq
      · subst hjeq; exact absurd hop hk_ne_not
    -- k cannot read v (else k has both inputs constant → k constant → consumer drops → D.card ≥ 4)
    have hk_no_v : (v : ℕ) ∉ C.gates[k].inputs := by
      intro hv_k
      have hk_bin : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or := by
        rcases (hnok _ (List.getElem_mem hk)).1.1 with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h hk_ne_not
      obtain ⟨u₁, u₂, _, _, _, hins_k⟩ := (reduced_gate_wf C hnok hred k hk).2 hk_bin
      have hst_k_const : ∃ e : Bool,
          (elimState m C.gates init (k + 1)).1.getD (m + k) (Sum.inl false) = Sum.inl e := by
        have hget := elimState_getD_at m C.gates init k hk
        have hlen : init.1.length = m := by simp [init, initVar]
        rw [hlen] at hget; rw [hget, hins_k]
        have h1 : (elimState m C.gates init k).1.getD (m + j₀) (Sum.inl false) = Sum.inl (!c) := by
          rw [elimState_getD_mono m C.gates init (j₀ + 1) k (m + j₀) _ (by omega) (by omega)
            (by simp [init, initVar])]; exact hst_j₀
        have h2 : (elimState m C.gates init k).1.getD (v : ℕ) (Sum.inl false) = Sum.inl b := by
          rw [elimState_getD_mono m C.gates init 0 k (v : ℕ) _ (Nat.zero_le _) (by omega)
            (by simp [init, initVar]), elimState_zero]; dsimp only [init]; rw [initVar, ofFn_getD_lt _ _ _ v.isLt]; simp
        rw [hins_k] at hmem_k hv_k; simp at hmem_k hv_k
        rcases hmem_k with hk1 | hk1 <;> rcases hv_k with hv1 | hv1
        · exact absurd (hk1.trans hv1.symm) (by omega)
        · rw [← hk1, ← hv1]; simp only [List.map_cons, List.map_nil, h1, h2]
          obtain ⟨e, he⟩ := simplifyGate_both_const C.gates[k].op _ (!c) b hk_bin
          exact ⟨e, by rw [he]⟩
        · rw [← hk1, ← hv1]; simp only [List.map_cons, List.map_nil, h1, h2]
          obtain ⟨e, he⟩ := simplifyGate_both_const C.gates[k].op _ b (!c) hk_bin
          exact ⟨e, by rw [he]⟩
        · exact absurd (hk1.trans hv1.symm) (by omega)
      obtain ⟨e, he⟩ := hst_k_const
      obtain ⟨_, s', hs', hks', _, hdrop_s'⟩ :=
        elim_const_not_output_and_consumer C hnok hred v b hnc_b k hk e he
      have hds' : s' ∈ D := hdrop_s'
      rw [hD_eq] at hds'; simp at hds'; omega
    -- Every gate reading v is j₁
    have hv_uniq : ∀ j : ℕ, (hj : j < C.gates.length) → (v : ℕ) ∈ C.gates[j].inputs → j = j₁ := by
      intro j hj hmem
      have hdj := hdrop_v j hj hmem
      rw [hD_eq] at hdj; simp at hdj
      rcases hdj with hjeq | hjeq | hjeq
      · exact hjeq
      · subst hjeq; rw [hnot_eq] at hmem; simp at hmem; omega
      · subst hjeq; exact absurd hmem hk_no_v
    -- Every gate reading m + j₁ is j₀
    have hj₁_uniq : ∀ j : ℕ, (hj : j < C.gates.length) → (m + j₁) ∈ C.gates[j].inputs → j = j₀ := by
      intro j hj hmem
      have hlt : j₁ < j := by
        have := reduced_inputs_lt C hnok hred j hj (m + j₁) hmem; omega
      have hdj : j ∈ D := by
        apply mem_elimDropped_of_const m C.gates init j hj (hnok _ (List.getElem_mem hj)) (m + j₁) hmem
        refine ⟨c, ?_⟩
        rw [elimState_getD_mono m C.gates init (j₁ + 1) j (m + j₁) _ (by omega) (by omega)
          (by simp [init, initVar]), ← ha_eq]; exact hst_j₁
      rw [hD_eq] at hdj; simp at hdj
      rcases hdj with hjeq | hjeq | hjeq
      · omega
      · exact hjeq
      · subst hjeq
        exact absurd hmem
          (elim_gate_not_both_a_and_not_a C hnok hred j₀ j (m + j₁) hj₀ hj hjk (by omega) hnot_eq hmem_k)
    obtain ⟨x, hx0, hx1⟩ := hinc
    have hanti := single_not_antimono_one C hnok hred v j₁ j₀ hj₁ hj₀ (by omega)
      hv_uniq hnot_eq hnot_uniq hj₁_uniq x hx1
    rw [hx0] at hanti; exact Bool.noConfusion hanti

/-- When `d = 2` and `acc.2.length = opt - 1 = (opt - 2) + 1`, the ONLY surviving configuration
    is a unique NOT gate `j₀` whose unique consumer `j₁` reads both `v` and `m + j₀`! -/
private lemma elim_delta2_d2_extract {m opt : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hred : Reduced m C) (hsz : C.gates.length ≤ opt + 1)
    (v : Fin m) (b : Bool)
    (hopt_ge2 : 2 ≤ opt)
    (f' : (Fin m → Bool) → Bool)
    (hf'_eq : f' = fun x => circuitFun m C (Function.update x v b))
    (hnc' : ∃ x y : Fin m → Bool, f' x ≠ f' y)
    (hlb' : ∀ s' < opt - 2, ¬ HasCircuitSize m f' s')
    (hIH' : ∀ D : Circuit, (∀ g ∈ D.gates, NOkGate g) → circuitFun m D = f' →
      D.size ≤ (opt - 2) + 1 → Reduced m D → ∀ g ∈ D.gates, g.op ≠ GateOp.not)
    (hd2 : (elimDropped m C.gates (initVar m v b, [])).card = 2)
    (j₀ : ℕ) (hj₀ : j₀ < C.gates.length) (hj₀_op : C.gates[j₀].op = GateOp.not)
    (hnd_j₀ : j₀ ∉ elimDropped m C.gates (initVar m v b, [])) :
    ∃ j₁ : ℕ, ∃ hj₁ : j₁ < C.gates.length,
      (∀ j : ℕ, (hj : j < C.gates.length) → C.gates[j].op = GateOp.not → j = j₀) ∧
      (v : ℕ) ∈ (C.gates[j₁]'hj₁).inputs ∧
      (m + j₀) ∈ (C.gates[j₁]'hj₁).inputs ∧
      (∀ j : ℕ, (hj : j < C.gates.length) → (m + j₀) ∈ C.gates[j].inputs → j = j₁) ∧
      (∀ j : ℕ, (hj : j < C.gates.length) → (v : ℕ) ∈ C.gates[j].inputs → j = j₁) := by
  let init := (initVar m v b, ([] : List Gate))
  let D := elimDropped m C.gates init
  have hnc_upd : ∃ x x' : Fin m → Bool,
      circuitFun m C (Function.update x v b) ≠ circuitFun m C (Function.update x' v b) := by
    obtain ⟨x, x', hne⟩ := hnc'; exact ⟨x, x', by simpa [hf'_eq] using hne⟩
  obtain ⟨_, _, _, hcard, _⟩ := elim_var_circuit C hnok v b hnc_upd
  obtain ⟨out, hout_st, _, hout_ne, hdead, huniq_acc⟩ :=
    elim_not_survives_or_dead C hnok v b f' hf'_eq hnc' hlb' hIH' (by change (elimPass m C.gates (initVar m v b, [])).2.length ≤ opt - 2 + 1; omega) j₀ hj₀ hnd_j₀ hj₀_op
  obtain ⟨k, r, hk, hr, c, hj₀k, hkr, hdk, hdr, hst_k, ⟨u, hu_lt, hmem_uk, hst_uk⟩, hmem_kr⟩ :=
    dead_wire_in_elim C hnok hred v b hnc_upd j₀ hj₀ hnd_j₀ out hout_st hout_ne hdead
  change (elimState m C.gates init k).1.getD u (Sum.inl false) =
    Sum.inr (m + (elimState m C.gates init j₀).2.length) at hst_uk
  have hD2 : D.card = 2 := hd2
  have hD_eq : D = {k, r} := by
    have hsub : ({k, r} : Finset ℕ) ⊆ D := by
      intro w hw; simp at hw; rcases hw with rfl | rfl <;> assumption
    have hc2 : ({k, r} : Finset ℕ).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
    exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  -- u must equal m + j₀!
  have hu_eq : u = m + j₀ := by
    by_contra hne
    have hge_m : m ≤ u := by
      by_contra hlt
      have hlt' : u < m := by omega
      have h0 := elimState_getD_mono m C.gates init 0 k u (Sum.inl false) (Nat.zero_le _) (by omega)
        (by simp [init, initVar]; exact hlt')
      rw [h0, elimState_zero] at hst_uk; dsimp only [init] at hst_uk; rw [initVar, ofFn_getD_lt _ _ _ hlt'] at hst_uk
      by_cases hfv : (⟨u, hlt'⟩ : Fin m) = v
      · simp only [hfv, ↓reduceIte] at hst_uk; cases hst_uk
      · simp only [hfv, ↓reduceIte] at hst_uk; have := Sum.inr.inj hst_uk; omega
    set ju := u - m
    have hju_lt : ju < k := by omega
    have hju_ne : ju ≠ j₀ := by omega
    by_cases hnd_u : ju ∉ D
    · obtain ⟨_, _, _, _, _, hst_ju⟩ := elim_emit_at m C.gates init ju (by omega) hnd_u
      have hlen : init.1.length = m := by simp [init, initVar]
      rw [hlen] at hst_ju
      have hmono := elimState_getD_mono m C.gates init (ju + 1) k (m + ju) (Sum.inl false)
        (by omega) (by omega) (by rw [hlen]; omega)
      rw [show m + ju = u by omega] at hmono hst_ju
      rw [← hmono] at hst_ju
      rw [hst_ju] at hst_uk
      have heq_len : (elimState m C.gates init ju).2.length = (elimState m C.gates init j₀).2.length := by
        have h1 := Sum.inr.inj hst_uk
        omega
      exact hju_ne (elim_emit_inj m C.gates init ju j₀ (by omega) hj₀ hnd_u hnd_j₀ heq_len)
    · push Not at hnd_u
      rw [hD_eq] at hnd_u; simp at hnd_u; omega
  subst hu_eq
  -- k cannot be a NOT gate (since st[m + j₀] = inr, NOT of inr is NOT dropped!)
  have hk_ne_not : C.gates[k].op ≠ GateOp.not := by
    intro hop
    obtain ⟨w, _, hins⟩ := (reduced_gate_wf C hnok hred k hk).1 hop
    rw [hins] at hmem_uk; simp at hmem_uk; subst hmem_uk
    rw [elimDropped, Finset.mem_filter, Finset.mem_range] at hdk
    have h2 := hdk.2
    have hst_uk' : (elimState m C.gates (initVar m v b, []) k).1.getD (m + j₀) (Sum.inl false) =
        Sum.inr (m + (elimState m C.gates (initVar m v b, []) j₀).2.length) := hst_uk
    simp only [hk, ↓reduceDIte, hop, hins, List.map_cons, List.map_nil, hst_uk',
      simplifyGate, simpNot] at h2
    exact Bool.noConfusion h2
  have hk_bin : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or := by
    rcases (hnok _ (List.getElem_mem hk)).1.1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hk_ne_not
  -- k's other input must be constant, hence MUST be v (since no gate < k is in D = {k, r}!)
  obtain ⟨u₁, u₂, hu₁, hu₂, hu12, hins_k⟩ := (reduced_gate_wf C hnok hred k hk).2 hk_bin
  have hv_in_k : (v : ℕ) ∈ C.gates[k].inputs := by
    have hnone_k : (simplifyGate C.gates[k].op (m + (elimState m C.gates init k).2.length)
        [(elimState m C.gates init k).1.getD u₁ (Sum.inl false),
         (elimState m C.gates init k).1.getD u₂ (Sum.inl false)]).1 = none := by
      rw [elimDropped, Finset.mem_filter, Finset.mem_range] at hdk
      have h2 := hdk.2
      simp only [hk, ↓reduceDIte, hins_k, List.map_cons, List.map_nil] at h2
      exact Option.isNone_iff_eq_none.1 h2
    have hother_const : ∃ w, w ∈ C.gates[k].inputs ∧ w ≠ m + j₀ ∧
        ∃ c', (elimState m C.gates init k).1.getD w (Sum.inl false) = Sum.inl c' := by
      rw [hins_k] at hmem_uk ⊢; simp at hmem_uk
      rcases hmem_uk with hm1 | hm1
      · rw [← hm1, hst_uk] at hnone_k
        cases hs2 : (elimState m C.gates init k).1.getD u₂ (Sum.inl false) with
        | inl c' => exact ⟨u₂, by simp, fun h => hu12 (hm1.symm.trans h.symm), c', hs2⟩
        | inr _ => rw [hs2] at hnone_k; rcases hk_bin with h | h <;> simp [h, simplifyGate, simpAnd, simpOr] at hnone_k
      · rw [← hm1, hst_uk] at hnone_k
        cases hs1 : (elimState m C.gates init k).1.getD u₁ (Sum.inl false) with
        | inl c' => exact ⟨u₁, by simp, fun h => hu12 (h.trans hm1), c', hs1⟩
        | inr _ => rw [hs1] at hnone_k; rcases hk_bin with h | h <;> simp [h, simplifyGate, simpAnd, simpOr] at hnone_k
    obtain ⟨w, hw_mem, _, c', hst_w⟩ := hother_const
    have hw_lt : w < m + k := reduced_inputs_lt C hnok hred k hk w hw_mem
    have hw_eq_v : w = (v : ℕ) := by
      by_contra hne_v
      by_cases hlt_m : w < m
      · have h0 := elimState_getD_mono m C.gates init 0 k w (Sum.inl false) (Nat.zero_le _) (by omega)
          (by simp [init, initVar]; exact hlt_m)
        rw [h0, elimState_zero] at hst_w; dsimp only [init] at hst_w; rw [initVar, ofFn_getD_lt _ _ _ hlt_m] at hst_w
        have hfin : (⟨w, hlt_m⟩ : Fin m) ≠ v := fun h => hne_v (congrArg Fin.val h)
        simp [hfin] at hst_w
      · set jw := w - m
        have hjw_lt : jw < k := by omega
        have hnd_w : jw ∉ D := by rw [hD_eq]; simp; omega
        obtain ⟨_, _, _, _, _, hst_jw⟩ := elim_emit_at m C.gates init jw (by omega) hnd_w
        have hlen : init.1.length = m := by simp [init, initVar]
        rw [hlen, show m + jw = w by omega] at hst_jw
        have hmono := elimState_getD_mono m C.gates init (jw + 1) k w (Sum.inl false)
          (by omega) (by omega) (by rw [hlen]; omega)
        rw [← hmono] at hst_jw
        rw [hst_jw] at hst_w; cases hst_w
    rwa [← hw_eq_v]
  -- r cannot be a NOT gate (else r = NOT(m + k) becomes constant → r's consumer drops → D.card ≥ 3!)
  have hr_ne_not : C.gates[r].op ≠ GateOp.not := by
    intro hop
    obtain ⟨w, _, hins_r⟩ := (reduced_gate_wf C hnok hred r hr).1 hop
    rw [hins_r] at hmem_kr; simp at hmem_kr; subst hmem_kr
    have hst_r : (elimState m C.gates init (r + 1)).1.getD (m + r) (Sum.inl false) = Sum.inl (!c) := by
      have hget := elimState_getD_at m C.gates init r hr
      have hlen : init.1.length = m := by simp [init, initVar]
      rw [hlen] at hget; rw [hget, hop, hins_r]
      have h1 : (elimState m C.gates init r).1.getD (m + k) (Sum.inl false) = Sum.inl c := by
        rw [elimState_getD_mono m C.gates init (k + 1) r (m + k) _ (by omega) (by omega)
          (by rw [hlen]; omega)]; exact hst_k
      simp only [List.map_cons, List.map_nil, h1, simplifyGate, simpNot]
    obtain ⟨_, s', hs', hrs', _, hds'⟩ :=
      elim_const_not_output_and_consumer C hnok hred v b hnc_upd r hr (!c) hst_r
    have hds : s' ∈ D := hds'
    rw [hD_eq] at hds; simp at hds; omega
  -- Unique NOT gate in C is j₀!
  have hnot_uniq : ∀ j : ℕ, (hj : j < C.gates.length) → C.gates[j].op = GateOp.not → j = j₀ := by
    intro j hj hop
    by_cases hdj : j ∈ D
    · rw [hD_eq] at hdj; simp at hdj
      rcases hdj with hjeq | hjeq
      · subst hjeq; exact absurd hop hk_ne_not
      · subst hjeq; exact absurd hop hr_ne_not
    · obtain ⟨g', _, hg'op, hklt, hkeq, _⟩ := elim_emit_at m C.gates init j hj hdj
      by_contra hne
      have hne_k : (elimState m C.gates init j).2.length ≠ (elimState m C.gates init j₀).2.length :=
        fun heq => hne (elim_emit_inj m C.gates init j j₀ hj hj₀ hdj hnd_j₀ heq)
      have hne_op := huniq_acc (elimState m C.gates init j).2.length hklt hne_k
      rw [hkeq, hg'op, hop] at hne_op; exact hne_op rfl
  -- Unique consumer of m + j₀ is k!
  have hj₀_cons_uniq : ∀ j : ℕ, (hj : j < C.gates.length) → (m + j₀) ∈ C.gates[j].inputs → j = k := by
    intro j hj hmem_j
    have hj_gt : j₀ < j := by
      have := reduced_inputs_lt C hnok hred j hj (m + j₀) hmem_j; omega
    by_cases hdj : j ∈ D
    · rw [hD_eq] at hdj; simp at hdj
      rcases hdj with hjeq | hjeq
      · exact hjeq
      · exfalso
        subst hjeq
        have hst_j₀_r : (elimState m C.gates init j).1.getD (m + j₀) (Sum.inl false) =
            Sum.inr (m + (elimState m C.gates init j₀).2.length) := by
          obtain ⟨_, _, _, _, _, hst0⟩ := elim_emit_at m C.gates init j₀ hj₀ hnd_j₀
          have hlen : init.1.length = m := by simp [init, initVar]
          rw [hlen] at hst0
          rw [elimState_getD_mono m C.gates init (j₀ + 1) j (m + j₀) _ (by omega) (by omega)
            (by rw [hlen]; omega), hst0]
        cases hstr : (elimState m C.gates init (j + 1)).1.getD (m + j) (Sum.inl false) with
        | inl e =>
          obtain ⟨_, s', hs', hrs', _, hds'⟩ :=
            elim_const_not_output_and_consumer C hnok hred v b hnc_upd j hj e hstr
          have hds : s' ∈ D := hds'
          rw [hD_eq] at hds; simp at hds; omega
        | inr w' =>
          have hget := elimState_getD_at m C.gates init j hj
          have hlen : init.1.length = m := by simp [init, initVar]
          rw [hlen] at hget; rw [hget] at hstr
          have hnone_r : (simplifyGate C.gates[j].op (m + (elimState m C.gates init j).2.length)
              (C.gates[j].inputs.map fun i => (elimState m C.gates init j).1.getD i (Sum.inl false))).1 = none := by
            rw [elimDropped, Finset.mem_filter, Finset.mem_range] at hdr
            have h2 := hdr.2; simp only [hj, ↓reduceDIte] at h2
            exact Option.isNone_iff_eq_none.1 h2
          have hmem_ins : Sum.inr (m + (elimState m C.gates init j₀).2.length) ∈
              (C.gates[j].inputs.map fun i => (elimState m C.gates init j).1.getD i (Sum.inl false)) :=
            List.mem_map.2 ⟨m + j₀, hmem_j, hst_j₀_r⟩
          have hw'_eq := simplifyGate_none_of_inr_mem C.gates[j].op _ _
            (hnok _ (List.getElem_mem hj)).1.1 (by simp [(hnok _ (List.getElem_mem hj)).1.2])
            (fun hop => by simp [(hnok _ (List.getElem_mem hj)).2 hop]) hnone_r _ w' hmem_ins hstr
          have hout_ne_r : C.output ≠ m + j := by
            intro heq
            have hacc_r : (elimPass m C.gates init).1.getD (m + j) (Sum.inl false) =
                Sum.inr (m + (elimState m C.gates init j₀).2.length) := by
              rw [← elimState_end,
                elimState_getD_mono m C.gates init (j + 1) C.gates.length (m + j) _ (by omega) le_rfl (by omega),
                hget, hstr, hw'_eq]
            rw [heq, hacc_r] at hout_st
            exact hout_ne (Sum.inr.inj hout_st).symm
          obtain ⟨s', hs', hrs', hmem_rs'⟩ := (reduced_no_dead C hnok hred j hj).resolve_left hout_ne_r
          have hnd_s' : s' ∉ D := by rw [hD_eq]; simp; omega
          obtain ⟨g_s, hg_s, _, hs'_lt, hs'_eq, _⟩ := elim_emit_at m C.gates init s' hs' hnd_s'
          have hlt_s' : (elimState m C.gates init j₀).2.length < (elimState m C.gates init s').2.length := by
            obtain ⟨g0, hg0, _, _, _, _⟩ := elim_emit_at m C.gates init j₀ hj₀ hnd_j₀
            have h1 : (elimState m C.gates init (j₀ + 1)).2.length =
                (elimState m C.gates init j₀).2.length + 1 := by
              rw [elimState_succ m C.gates init j₀ hj₀, elimStep, hg0]; simp
            have h2 := elimState_snd_mono m C.gates init (j₀ + 1) s' (by omega)
            omega
          have hst_rs' : (elimState m C.gates init s').1.getD (m + j) (Sum.inl false) =
              Sum.inr (m + (elimState m C.gates init j₀).2.length) := by
            rw [elimState_getD_mono m C.gates init (j + 1) s' (m + j) _ (by omega) (by omega)
              (by rw [hlen]; omega), hget, hstr, hw'_eq]
          have hmem_ins_s : Sum.inr (m + (elimState m C.gates init j₀).2.length) ∈
              (C.gates[s'].inputs.map fun i => (elimState m C.gates init s').1.getD i (Sum.inl false)) :=
            List.mem_map.2 ⟨m + j, hmem_rs', hst_rs'⟩
          have hmem_gs := simplifyGate_some_mem_inputs C.gates[s'].op _ _
            (fun hop => by simp [(hnok _ (List.getElem_mem hs')).2 hop]) g_s hg_s _ hmem_ins_s
          rw [← hs'_eq] at hmem_gs
          exact hdead _ hs'_lt hlt_s' hmem_gs
    · -- j ∉ D, so j emits a gate reading m + k₀ → contradicts hdead!
      exfalso
      obtain ⟨g_j, hg_j, _, hj'_lt, hj'_eq, _⟩ := elim_emit_at m C.gates init j hj hdj
      have hlt_j' : (elimState m C.gates init j₀).2.length < (elimState m C.gates init j).2.length := by
        obtain ⟨g0, hg0, _, _, _, _⟩ := elim_emit_at m C.gates init j₀ hj₀ hnd_j₀
        have h1 : (elimState m C.gates init (j₀ + 1)).2.length =
            (elimState m C.gates init j₀).2.length + 1 := by
          rw [elimState_succ m C.gates init j₀ hj₀, elimStep, hg0]; simp
        have h2 := elimState_snd_mono m C.gates init (j₀ + 1) j (by omega)
        omega
      have hst_j₀_j : (elimState m C.gates init j).1.getD (m + j₀) (Sum.inl false) =
          Sum.inr (m + (elimState m C.gates init j₀).2.length) := by
        obtain ⟨_, _, _, _, _, hst0⟩ := elim_emit_at m C.gates init j₀ hj₀ hnd_j₀
        have hlen : init.1.length = m := by simp [init, initVar]
        rw [hlen] at hst0
        rw [elimState_getD_mono m C.gates init (j₀ + 1) j (m + j₀) _ (by omega) (by omega)
          (by rw [hlen]; omega), hst0]
      have hmem_ins_j : Sum.inr (m + (elimState m C.gates init j₀).2.length) ∈
          (C.gates[j].inputs.map fun i => (elimState m C.gates init j).1.getD i (Sum.inl false)) :=
        List.mem_map.2 ⟨m + j₀, hmem_j, hst_j₀_j⟩
      have hmem_gj := simplifyGate_some_mem_inputs C.gates[j].op _ _
        (fun hop => by simp [(hnok _ (List.getElem_mem hj)).2 hop]) g_j hg_j _ hmem_ins_j
      rw [← hj'_eq] at hmem_gj
      exact hdead _ hj'_lt hlt_j' hmem_gj
  -- Unique gate reading v is k!
  have hv_uniq : ∀ j : ℕ, (hj : j < C.gates.length) → (v : ℕ) ∈ C.gates[j].inputs → j = k := by
    intro j hj hmem_v
    have hdj : j ∈ D := by
      apply mem_elimDropped_of_const m C.gates init j hj (hnok _ (List.getElem_mem hj)) (v : ℕ) hmem_v
      refine ⟨b, ?_⟩
      rw [elimState_getD_mono m C.gates init 0 j (v : ℕ) _ (Nat.zero_le _) (by omega)
        (by simp [init, initVar]), elimState_zero]; dsimp only [init]; rw [initVar, ofFn_getD_lt _ _ _ v.isLt]; simp
    rw [hD_eq] at hdj; simp at hdj
    rcases hdj with hjeq | hjeq
    · exact hjeq
    · exfalso
      subst hjeq
      have hr_bin : C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or := by
        rcases (hnok _ (List.getElem_mem hj)).1.1 with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h hr_ne_not
      obtain ⟨w₁, w₂, _, _, _, hins_r⟩ := (reduced_gate_wf C hnok hred j hj).2 hr_bin
      have hst_r_const : ∃ e : Bool,
          (elimState m C.gates init (j + 1)).1.getD (m + j) (Sum.inl false) = Sum.inl e := by
        have hget := elimState_getD_at m C.gates init j hj
        have hlen : init.1.length = m := by simp [init, initVar]
        rw [hlen] at hget; rw [hget, hins_r]
        have h1 : (elimState m C.gates init j).1.getD (m + k) (Sum.inl false) = Sum.inl c := by
          rw [elimState_getD_mono m C.gates init (k + 1) j (m + k) _ (by omega) (by omega)
            (by rw [hlen]; omega)]; exact hst_k
        have h2 : (elimState m C.gates init j).1.getD (v : ℕ) (Sum.inl false) = Sum.inl b := by
          rw [elimState_getD_mono m C.gates init 0 j (v : ℕ) _ (Nat.zero_le _) (by omega)
            (by simp [init, initVar]), elimState_zero]; dsimp only [init]; rw [initVar, ofFn_getD_lt _ _ _ v.isLt]; simp
        rw [hins_r] at hmem_kr hmem_v; simp at hmem_kr hmem_v
        rcases hmem_kr with hk1 | hk1 <;> rcases hmem_v with hv1 | hv1
        · exact absurd (hk1.trans hv1.symm) (by omega)
        · rw [← hk1, ← hv1]; simp only [List.map_cons, List.map_nil, h1, h2]
          obtain ⟨e, he⟩ := simplifyGate_both_const C.gates[j].op _ c b hr_bin
          exact ⟨e, by rw [he]⟩
        · rw [← hk1, ← hv1]; simp only [List.map_cons, List.map_nil, h1, h2]
          obtain ⟨e, he⟩ := simplifyGate_both_const C.gates[j].op _ b c hr_bin
          exact ⟨e, by rw [he]⟩
        · exact absurd (hk1.trans hv1.symm) (by omega)
      obtain ⟨e, he⟩ := hst_r_const
      obtain ⟨_, s', hs', hrs', _, hds'⟩ :=
        elim_const_not_output_and_consumer C hnok hred v b hnc_upd j hj e he
      have hds : s' ∈ D := hds'
      rw [hD_eq] at hds; simp at hds; omega
  exact ⟨k, hk, hnot_uniq, hv_in_k, hmem_uk, hj₀_cons_uniq, hv_uniq⟩

private lemma elim_delta2_leaf {m opt : ℕ} (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hred : Reduced m C) (hsz : C.gates.length ≤ opt + 1)
    (v : Fin m)
    (hinc : ∃ x : Fin m → Bool,
      circuitFun m C (Function.update x v false) = false ∧
      circuitFun m C (Function.update x v true) = true)
    (hopt_ge2 : 2 ≤ opt)
    (f0 f1 : (Fin m → Bool) → Bool)
    (hf0_eq : f0 = fun x => circuitFun m C (Function.update x v false))
    (hf1_eq : f1 = fun x => circuitFun m C (Function.update x v true))
    (hnc0 : ∃ x y : Fin m → Bool, f0 x ≠ f0 y)
    (hnc1 : ∃ x y : Fin m → Bool, f1 x ≠ f1 y)
    (hlb0 : ∀ s' < opt - 2, ¬ HasCircuitSize m f0 s')
    (hlb1 : ∀ s' < opt - 2, ¬ HasCircuitSize m f1 s')
    (hIH0 : ∀ D : Circuit, (∀ g ∈ D.gates, NOkGate g) → circuitFun m D = f0 →
      D.size ≤ (opt - 2) + 1 → Reduced m D → ∀ g ∈ D.gates, g.op ≠ GateOp.not)
    (hIH1 : ∀ D : Circuit, (∀ g ∈ D.gates, NOkGate g) → circuitFun m D = f1 →
      D.size ≤ (opt - 2) + 1 → Reduced m D → ∀ g ∈ D.gates, g.op ≠ GateOp.not)
    (j₀ : ℕ) (hj₀ : j₀ < C.gates.length) (hj₀_op : C.gates[j₀].op = GateOp.not) :
    ∃ j_n j₁ : ℕ, ∃ (_hjn : j_n < C.gates.length) (hj₁ : j₁ < C.gates.length),
      (∀ j : ℕ, (hj : j < C.gates.length) → C.gates[j].op = GateOp.not → j = j_n) ∧
      (v : ℕ) ∈ (C.gates[j₁]'hj₁).inputs ∧
      (m + j_n) ∈ (C.gates[j₁]'hj₁).inputs ∧
      (∀ j : ℕ, (hj : j < C.gates.length) → (m + j_n) ∈ C.gates[j].inputs → j = j₁) := by
  classical
  have hnc_upd0 : ∃ x x', circuitFun m C (Function.update x v false) ≠ circuitFun m C (Function.update x' v false) := by
    obtain ⟨x, x', hne⟩ := hnc0; exact ⟨x, x', by simpa [hf0_eq] using hne⟩
  have hnc_upd1 : ∃ x x', circuitFun m C (Function.update x v true) ≠ circuitFun m C (Function.update x' v true) := by
    obtain ⟨x, x', hne⟩ := hnc1; exact ⟨x, x', by simpa [hf1_eq] using hne⟩
  have hdrop_bound : ∀ b : Bool, (elimDropped m C.gates (initVar m v b, [])).card ≤ 2 := by
    intro b
    have hncb : ∃ x x', circuitFun m C (Function.update x v b) ≠ circuitFun m C (Function.update x' v b) := by
      cases b <;> assumption
    obtain ⟨out, _, _, hcard, hfun⟩ := elim_var_circuit C hnok v b hncb
    have hge : opt - 2 ≤ (elimPass m C.gates (initVar m v b, [])).2.length := by
      by_contra hlt
      have hcs : HasCircuitSize m (if b then f1 else f0) (elimPass m C.gates (initVar m v b, [])).2.length :=
        ⟨⟨(elimPass m C.gates (initVar m v b, [])).2, out⟩, elimPass_ok m C.gates _ (by simp), le_rfl,
          fun x => by cases b <;> simp [hf0_eq, hf1_eq] <;> exact congrFun hfun x⟩
      cases b
      · exact hlb0 _ (by omega) hcs
      · exact hlb1 _ (by omega) hcs
    have hle3 : (elimDropped m C.gates (initVar m v b, [])).card ≤ 3 := by omega
    by_contra hgt2
    have hd3 : (elimDropped m C.gates (initVar m v b, [])).card = 3 := by omega
    exact elim_delta2_d3_contra C hnok hred hsz v b hinc hopt_ge2 f0 f1 hf0_eq hf1_eq
      hnc0 hnc1 hlb0 hlb1 (by cases b <;> assumption) hd3 j₀ hj₀ hj₀_op
  have hfrom_d2 : ∀ b : Bool, (elimDropped m C.gates (initVar m v b, [])).card = 2 →
      ∃ j_n j₁ : ℕ, ∃ (_hjn : j_n < C.gates.length) (hj₁ : j₁ < C.gates.length),
        (∀ j : ℕ, (hj : j < C.gates.length) → C.gates[j].op = GateOp.not → j = j_n) ∧
        (v : ℕ) ∈ (C.gates[j₁]'hj₁).inputs ∧
        (m + j_n) ∈ (C.gates[j₁]'hj₁).inputs ∧
        (∀ j : ℕ, (hj : j < C.gates.length) → (m + j_n) ∈ C.gates[j].inputs → j = j₁) := by
    intro b hd2
    let init := (initVar m v b, ([] : List Gate))
    let D := elimDropped m C.gates init
    have hncb : ∃ x x', circuitFun m C (Function.update x v b) ≠ circuitFun m C (Function.update x' v b) := by
      cases b <;> assumption
    by_cases hnd : j₀ ∉ D
    · obtain ⟨j₁, hj₁, huniq, hv1, hj01, hcons1, _⟩ :=
        elim_delta2_d2_extract C hnok hred hsz v b hopt_ge2 (if b then f1 else f0)
          (by cases b <;> simp [hf0_eq, hf1_eq]) (by cases b <;> assumption)
          (by cases b <;> assumption) (by cases b <;> assumption) hd2 j₀ hj₀ hj₀_op hnd
      exact ⟨j₀, j₁, hj₀, hj₁, huniq, hv1, hj01, hcons1⟩
    · exfalso
      push Not at hnd
      obtain ⟨a, c, ha, hins, _, hst_j₀, hne_v⟩ :=
        elim_dropped_not_const C hnok hred v b j₀ hj₀ hnd hj₀_op
      obtain ⟨_, k, hk, hjk, hmem_k, hdrop_k⟩ :=
        elim_const_not_output_and_consumer C hnok hred v b hncb j₀ hj₀ (!c) hst_j₀
      have ha_eq_v : a = (v : ℕ) := by
        by_contra hne
        obtain ⟨_, hdrop_am, _⟩ := hne_v hne
        have hsub : ({a - m, j₀, k} : Finset ℕ) ⊆ D := by
          intro u hu; simp at hu; rcases hu with rfl | rfl | rfl <;> assumption
        have hc3 : ({a - m, j₀, k} : Finset ℕ).card = 3 := by
          rw [Finset.card_insert_of_notMem (by simp; omega),
              Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
        have : ({a - m, j₀, k} : Finset ℕ).card ≤ D.card := Finset.card_le_card hsub
        have hd2' : D.card = 2 := hd2
        omega
      have hnot_eq : C.gates[j₀] = ⟨GateOp.not, [(v : ℕ)]⟩ := by
        cases hg : C.gates[j₀] with
        | mk op ins =>
          rw [hg] at hj₀_op hins; simp only at hj₀_op hins
          subst hj₀_op; subst hins; subst ha_eq_v; rfl
      have hk_ne_not := elim_not_consumer_ne_not C hnok hred j₀ k (v : ℕ) hj₀ hk hjk (by omega) hnot_eq hmem_k
      have hk_bin : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or := by
        rcases (hnok _ (List.getElem_mem hk)).1.1 with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h hk_ne_not
      set b' : Bool := if C.gates[k].op = GateOp.and then true else false with hb'
      let init' := (initVar m v b', ([] : List Gate))
      let D' := elimDropped m C.gates init'
      have hncb' : ∃ x x', circuitFun m C (Function.update x v b') ≠ circuitFun m C (Function.update x' v b') := by
        cases b' <;> assumption
      have hv_st' : (elimState m C.gates init' j₀).1.getD (v : ℕ) (Sum.inl false) = Sum.inl b' := by
        rw [elimState_getD_mono m C.gates init' 0 j₀ (v : ℕ) _ (Nat.zero_le _) (by omega)
          (by simp [init', initVar]), elimState_zero]; dsimp only [init']; rw [initVar, ofFn_getD_lt _ _ _ v.isLt]; simp
      have hdrop_j₀' : j₀ ∈ D' :=
        mem_elimDropped_of_const m C.gates init' j₀ hj₀ (hnok _ (List.getElem_mem hj₀)) (v : ℕ)
          (by rw [hnot_eq]; simp) ⟨b', hv_st'⟩
      have hst_j₀' : (elimState m C.gates init' (j₀ + 1)).1.getD (m + j₀) (Sum.inl false) = Sum.inl (!b') := by
        have hget := elimState_getD_at m C.gates init' j₀ hj₀
        have hlen : init'.1.length = m := by simp [init', initVar]
        rw [hlen] at hget; rw [hget, hnot_eq]
        simp only [List.map_cons, List.map_nil, hv_st', simplifyGate, simpNot]
      have hdrop_k' : k ∈ D' := by
        apply mem_elimDropped_of_const m C.gates init' k hk (hnok _ (List.getElem_mem hk)) (m + j₀) hmem_k
        refine ⟨!b', ?_⟩
        rw [elimState_getD_mono m C.gates init' (j₀ + 1) k (m + j₀) _ (by omega) (by omega)
          (by simp [init', initVar])]; exact hst_j₀'
      have hst_k' : (elimState m C.gates init' (k + 1)).1.getD (m + k) (Sum.inl false) = Sum.inl (!b') := by
        have hget := elimState_getD_at m C.gates init' k hk
        have hlen : init'.1.length = m := by simp [init', initVar]
        rw [hlen] at hget; rw [hget]
        have h1 : (elimState m C.gates init' k).1.getD (m + j₀) (Sum.inl false) = Sum.inl (!b') := by
          rw [elimState_getD_mono m C.gates init' (j₀ + 1) k (m + j₀) _ (by omega) (by omega)
            (by simp [init', initVar])]; exact hst_j₀'
        have hmem_ins : Sum.inl (!b') ∈ (C.gates[k].inputs.map fun i =>
            (elimState m C.gates init' k).1.getD i (Sum.inl false)) :=
          List.mem_map.2 ⟨m + j₀, hmem_k, h1⟩
        rcases hk_bin with hop | hop
        · have hb't : b' = true := by simp [hb', hop]
          rw [hb't] at hmem_ins ⊢; simp only [Bool.not_true] at hmem_ins ⊢; rw [hop]
          rw [simplifyGate_and_false _ _ (by simp [(hnok _ (List.getElem_mem hk)).1.2]) hmem_ins]
        · have hb'f : b' = false := by simp [hb', hop]
          rw [hb'f] at hmem_ins ⊢; simp only [Bool.not_false] at hmem_ins ⊢; rw [hop]
          rw [simplifyGate_or_true _ _ (by simp [(hnok _ (List.getElem_mem hk)).1.2]) hmem_ins]
      obtain ⟨_, r', hr', hkr', _, hdrop_r'⟩ :=
        elim_const_not_output_and_consumer C hnok hred v b' hncb' k hk (!b') hst_k'
      have hsub : ({j₀, k, r'} : Finset ℕ) ⊆ D' := by
        intro u hu; simp at hu; rcases hu with rfl | rfl | rfl <;> assumption
      have hc3 : ({j₀, k, r'} : Finset ℕ).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp; omega),
            Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
      have hge3 : 3 ≤ D'.card := hc3 ▸ Finset.card_le_card hsub
      have hle2 : D'.card ≤ 2 := hdrop_bound b'
      omega
  have hex_v : ∃ g₁ : ℕ, ∃ hg₁ : g₁ < C.gates.length, (v : ℕ) ∈ C.gates[g₁].inputs := by
    by_contra hno
    push Not at hno
    obtain ⟨x, hx0, hx1⟩ := hinc
    have hne : C.gates ≠ [] := List.ne_nil_of_length_pos (by omega)
    have hout := hred.2.2.1 hne
    have heq := wire_indep_of_not_read C v hno C.gates.length le_rfl C.output (by omega) (by omega) x
    change circuitFun m C (Function.update x v false) = circuitFun m C (Function.update x v true) at heq
    rw [hx0, hx1] at heq; exact Bool.noConfusion heq
  obtain ⟨g₁, hg₁, hg₁_v⟩ := hex_v
  set b : Bool := if C.gates[g₁].op = GateOp.or then true else false with hb
  let init := (initVar m v b, ([] : List Gate))
  let D := elimDropped m C.gates init
  have hncb : ∃ x x', circuitFun m C (Function.update x v b) ≠ circuitFun m C (Function.update x' v b) := by
    cases b <;> assumption
  have hv_st : (elimState m C.gates init g₁).1.getD (v : ℕ) (Sum.inl false) = Sum.inl b := by
    rw [elimState_getD_mono m C.gates init 0 g₁ (v : ℕ) _ (Nat.zero_le _) (by omega)
      (by simp [init, initVar]), elimState_zero]; dsimp only [init]; rw [initVar, ofFn_getD_lt _ _ _ v.isLt]; simp
  have hdrop_g₁ : g₁ ∈ D :=
    mem_elimDropped_of_const m C.gates init g₁ hg₁ (hnok _ (List.getElem_mem hg₁)) (v : ℕ) hg₁_v ⟨b, hv_st⟩
  have hst_g₁_const : ∃ c : Bool,
      (elimState m C.gates init (g₁ + 1)).1.getD (m + g₁) (Sum.inl false) = Sum.inl c := by
    have hget := elimState_getD_at m C.gates init g₁ hg₁
    have hlen : init.1.length = m := by simp [init, initVar]
    rw [hlen] at hget; rw [hget]
    have hmem_ins : Sum.inl b ∈ (C.gates[g₁].inputs.map fun i =>
        (elimState m C.gates init g₁).1.getD i (Sum.inl false)) :=
      List.mem_map.2 ⟨(v : ℕ), hg₁_v, hv_st⟩
    rcases (hnok _ (List.getElem_mem hg₁)).1.1 with hop | hop | hop
    · have hbf : b = false := by simp [hb, hop]
      rw [hbf] at hmem_ins; rw [hop]
      exact ⟨false, by rw [simplifyGate_and_false _ _ (by simp [(hnok _ (List.getElem_mem hg₁)).1.2]) hmem_ins]⟩
    · have hbt : b = true := by simp [hb, hop]
      rw [hbt] at hmem_ins; rw [hop]
      exact ⟨true, by rw [simplifyGate_or_true _ _ (by simp [(hnok _ (List.getElem_mem hg₁)).1.2]) hmem_ins]⟩
    · obtain ⟨u, _, hins⟩ := (reduced_gate_wf C hnok hred g₁ hg₁).1 hop
      rw [hins] at hg₁_v; simp at hg₁_v; subst hg₁_v
      rw [hop, hins]; exact ⟨!b, by simp only [List.map_cons, List.map_nil, hv_st, simplifyGate, simpNot]⟩
  obtain ⟨c, hc⟩ := hst_g₁_const
  obtain ⟨_, k, hk, hg₁k, _, hdrop_k⟩ :=
    elim_const_not_output_and_consumer C hnok hred v b hncb g₁ hg₁ c hc
  have hsub : ({g₁, k} : Finset ℕ) ⊆ D := by
    intro u hu; simp at hu; rcases hu with rfl | rfl <;> assumption
  have hc2 : ({g₁, k} : Finset ℕ).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
  have hge2 : 2 ≤ D.card := hc2 ▸ Finset.card_le_card hsub
  have hle2 : D.card ≤ 2 := hdrop_bound b
  exact hfrom_d2 b (by change D.card = 2; omega)

/-! ### Section 6: Main Induction and Theorem `L_meta_551` -/

private lemma base_single_A {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (A : Finset (Fin n)) (a : Fin n) (hA : A = {a}) (hnoE : ∀ u v : Fin n, ¬ K.Adj u v)
    (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hfun : circuitFun n C = forestFun0 K A) (hsz : C.gates.length ≤ 1)
    (hred : Reduced n C) :
    ∀ g ∈ C.gates, g.op ≠ GateOp.not := by
  intro g hg hop
  have hlen1 : C.gates.length = 1 := by
    have hpos : 0 < C.gates.length := List.length_pos_of_mem hg
    omega
  have hg0 : C.gates[0]'(by omega) = g := by
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    have : j = 0 := by omega
    subst this; rfl
  have hout : C.output = n + 0 := by
    have := hred.2.2.1 (List.ne_nil_of_length_pos (by omega)); omega
  obtain ⟨u, hu, hins⟩ := (reduced_gate_wf C hnok hred 0 (by omega)).1 (by rw [hg0]; exact hop)
  have h0 : circuitFun n C (fun _ => false) = true := by
    show (C.wires (List.ofFn (fun _ : Fin n => false))).getD C.output false = true
    rw [hout, wire_eval_gate C 0 (by omega), hins, hg0, hop]
    have hwu : (C.wires (List.ofFn (fun _ : Fin n => false))).getD u false = false := by
      show (wiresFrom C.gates _).getD u false = false
      rw [wiresFrom_getD_lt _ _ _ (by simp; omega), ofFn_getD_lt _ _ _ (by omega)]
    simp only [hu, ↓reduceIte, hwu, GateOp.eval, List.map_cons, List.map_nil, List.headD_cons, Bool.not_false]
  rw [hfun, forestFun0_false] at h0
  exact Bool.noConfusion h0

private lemma base_single_edge {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (u v : Fin n) (huv : K.Adj u v) (hE1 : K.edgeFinset.card = 1)
    (C : Circuit) (hnok : ∀ g ∈ C.gates, NOkGate g)
    (hfun : circuitFun n C = forestFun0 K ∅) (hsz : C.gates.length ≤ 2)
    (hred : Reduced n C) :
    ∀ g ∈ C.gates, g.op ≠ GateOp.not := by
  have hfun_uv : ∀ x : Fin n → Bool, forestFun0 K ∅ x = (x u && x v) := by
    intro x
    simp only [forestFun0, Finset.notMem_empty, false_and, exists_false, false_or]
    cases hxu : x u <;> cases hxv : x v <;> simp only [Bool.and_false, Bool.false_and, Bool.and_true]
    · simp only [decide_eq_false_iff_not]; rintro ⟨a, b, hab, hxa, hxb⟩
      have heq : s(a, b) = s(u, v) := Finset.card_le_one.1 (show K.edgeFinset.card ≤ 1 by omega) s(a, b)
        (SimpleGraph.mem_edgeFinset.2 hab) s(u, v) (SimpleGraph.mem_edgeFinset.2 huv)
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hxu, hxv] at hxa hxb
    · simp only [decide_eq_false_iff_not]; rintro ⟨a, b, hab, hxa, hxb⟩
      have heq : s(a, b) = s(u, v) := Finset.card_le_one.1 (show K.edgeFinset.card ≤ 1 by omega) s(a, b)
        (SimpleGraph.mem_edgeFinset.2 hab) s(u, v) (SimpleGraph.mem_edgeFinset.2 huv)
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hxu, hxv] at hxa hxb
    · simp only [decide_eq_false_iff_not]; rintro ⟨a, b, hab, hxa, hxb⟩
      have heq : s(a, b) = s(u, v) := Finset.card_le_one.1 (show K.edgeFinset.card ≤ 1 by omega) s(a, b)
        (SimpleGraph.mem_edgeFinset.2 hab) s(u, v) (SimpleGraph.mem_edgeFinset.2 huv)
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hxu, hxv] at hxa hxb
    · simp only [decide_eq_true_eq]; exact ⟨u, v, huv, hxu, hxv⟩
  intro g hg hop
  obtain ⟨j₀, hj₀, rfl⟩ := List.getElem_of_mem hg
  have hne : C.gates ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hout := hred.2.2.1 hne
  have hin_val : ∀ (x : Fin n → Bool) (i : ℕ) (hi : i < n),
      (C.wires (List.ofFn x)).getD i false = x ⟨i, hi⟩ := by
    intro x i hi
    show (wiresFrom C.gates _).getD i false = _
    rw [wiresFrom_getD_lt _ _ _ (by simp; exact hi), ofFn_getD_lt _ _ _ hi]
  by_cases hlen1 : C.gates.length = 1
  · have hj0 : j₀ = 0 := by omega
    subst hj0
    obtain ⟨a, ha, hins⟩ := (reduced_gate_wf C hnok hred 0 hj₀).1 hop
    have h0 : circuitFun n C (fun _ => false) = true := by
      show (C.wires _).getD C.output false = true
      rw [show C.output = n + 0 by omega, wire_eval_gate C 0 hj₀, hop, hins]
      simp only [ha, ↓reduceIte, hin_val _ a (by omega), GateOp.eval, List.map_cons, List.map_nil, List.headD_cons, Bool.not_false]
    rw [hfun, forestFun0_false] at h0; exact Bool.noConfusion h0
  · have hlen2 : C.gates.length = 2 := by omega
    have hout2 : C.output = n + 1 := by omega
    by_cases hj1 : j₀ = 1
    · subst hj1
      obtain ⟨a, ha, hins1⟩ := (reduced_gate_wf C hnok hred 1 hj₀).1 hop
      -- Gate 1 = NOT(a) = output, and gate 0 must be read by gate 1 (reduced!), so a = n + 0!
      have ha_eq : a = n + 0 := by
        obtain ⟨k, hk, h0k, hmem⟩ := (reduced_no_dead C hnok hred 0 (by omega)).resolve_left (by omega)
        have : k = 1 := by omega
        subst this; rw [hins1] at hmem; simp at hmem; exact hmem.symm
      -- So wire (n + 0) = !(x u && x v)!
      have hw0 : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + 0) false = !(x u && x v) := by
        intro x
        have hev := congrFun hfun x
        rw [hfun_uv x] at hev
        change (C.wires (List.ofFn x)).getD C.output false = (x u && x v) at hev
        rw [hout2, wire_eval_gate C 1 hj₀ x, hop, hins1, ha_eq] at hev
        simp only [show n + 0 < n + 1 by omega, ↓reduceIte, GateOp.eval, List.map_cons, List.map_nil,
          List.headD_cons] at hev
        rw [← hev, Bool.not_not]
      -- Gate 0 only reads inputs < n; check its op!
      rcases (hnok _ (List.getElem_mem (show 0 < C.gates.length by omega))).1.1 with hop0 | hop0 | hop0
      · obtain ⟨p, q, hp, hq, _, hins0⟩ := (reduced_gate_wf C hnok hred 0 (by omega)).2 (Or.inl hop0)
        have h0 := hw0 (fun _ => false)
        rw [wire_eval_gate C 0 (by omega), hop0, hins0] at h0
        simp only [hp, hq, ↓reduceIte, hin_val _ p (by omega), hin_val _ q (by omega), GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_false, Bool.false_and, Bool.or_false, Bool.not_false] at h0; exact Bool.noConfusion h0
      · obtain ⟨p, q, hp, hq, _, hins0⟩ := (reduced_gate_wf C hnok hred 0 (by omega)).2 (Or.inr hop0)
        have h0 := hw0 (fun _ => false)
        rw [wire_eval_gate C 0 (by omega), hop0, hins0] at h0
        simp only [hp, hq, ↓reduceIte, hin_val _ p (by omega), hin_val _ q (by omega), GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_false, Bool.false_and, Bool.or_false, Bool.not_false] at h0; exact Bool.noConfusion h0
      · obtain ⟨p, hp, hins0⟩ := (reduced_gate_wf C hnok hred 0 (by omega)).1 hop0
        let fp : Fin n := ⟨p, by omega⟩
        have hval0 : ∀ x : Fin n → Bool, (!(x fp)) = !(x u && x v) := by
          intro x
          have h := hw0 x
          rw [wire_eval_gate C 0 (by omega) x, hop0, hins0] at h
          simpa only [hp, ↓reduceIte, hin_val x p (by omega), GateOp.eval, List.map_cons, List.map_nil, List.headD_cons] using h
        by_cases hpu : fp = u
        · have h := hval0 (fun i => decide (i = u))
          simp [hpu, huv.ne.symm] at h
        · have h := hval0 (fun i => decide (i = fp))
          have hufp : u ≠ fp := Ne.symm hpu
          simp [hufp] at h
    · -- j₀ = 0: Gate 0 = NOT(p) with p < n; Gate 1 reads n + 0 and is NOT a NOT gate!
      have hj0 : j₀ = 0 := by omega
      subst hj0
      obtain ⟨p, hp, hins0⟩ := (reduced_gate_wf C hnok hred 0 hj₀).1 hop
      have h0_eq : C.gates[0] = ⟨GateOp.not, [p]⟩ := by
        cases hg0 : C.gates[0] with
        | mk op ins => rw [hg0] at hop hins0; simp only at hop hins0; subst hop; subst hins0; rfl
      obtain ⟨k, hk, h0k, hmem1⟩ := (reduced_no_dead C hnok hred 0 hj₀).resolve_left (by omega)
      have hk1 : k = 1 := by omega
      subst hk1
      have h1_ne_not := elim_not_consumer_ne_not C hnok hred 0 1 p hj₀ hk (by omega) hp h0_eq hmem1
      have h1_bin : C.gates[1].op = GateOp.and ∨ C.gates[1].op = GateOp.or := by
        rcases (hnok _ (List.getElem_mem hk)).1.1 with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h h1_ne_not
      obtain ⟨a, b, ha, hb, hab, hins1⟩ := (reduced_gate_wf C hnok hred 1 hk).2 h1_bin
      have hval : ∀ x : Fin n → Bool,
          (C.wires (List.ofFn x)).getD n false = !(x ⟨p, by omega⟩) := by
        intro x
        have h := wire_eval_gate C 0 hj₀ x
        rw [Nat.add_zero, h0_eq] at h
        rw [h]
        simp only [show p < n by omega, ↓reduceIte, hin_val x p (by omega), GateOp.eval,
          List.map_cons, List.map_nil, List.headD_cons]
      rcases h1_bin with hop1 | hop1
      · have ht := congrFun hfun (fun _ => true)
        rw [hfun_uv] at ht
        change (C.wires _).getD C.output false = true at ht
        rw [hout2, wire_eval_gate C 1 hk, hop1, hins1] at ht
        rw [hins1] at hmem1; simp only [Nat.add_zero, List.mem_cons, List.not_mem_nil, or_false] at hmem1
        rcases hmem1 with hm | hm
        · rw [← hm] at ht
          simp only [show n < n + 1 by omega, hb, ↓reduceIte, hval, GateOp.eval, List.map_cons,
            List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.not_true, Bool.false_and] at ht
          exact Bool.noConfusion ht
        · rw [← hm] at ht
          simp only [ha, show n < n + 1 by omega, ↓reduceIte, hval, GateOp.eval, List.map_cons,
            List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.not_true, Bool.false_and,
            Bool.and_false] at ht
          exact Bool.noConfusion ht
      · have hf := congrFun hfun (fun _ => false)
        rw [hfun_uv] at hf
        change (C.wires _).getD C.output false = false at hf
        rw [hout2, wire_eval_gate C 1 hk, hop1, hins1] at hf
        rw [hins1] at hmem1; simp only [Nat.add_zero, List.mem_cons, List.not_mem_nil, or_false] at hmem1
        rcases hmem1 with hm | hm
        · rw [← hm] at hf
          simp only [show n < n + 1 by omega, hb, ↓reduceIte, hval, GateOp.eval, List.map_cons,
            List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.not_false, Bool.true_or] at hf
          exact Bool.noConfusion hf
        · rw [← hm] at hf
          simp only [ha, show n < n + 1 by omega, ↓reduceIte, hval, GateOp.eval, List.map_cons,
            List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.not_false, Bool.true_or,
            Bool.or_true] at hf
          exact Bool.noConfusion hf

private lemma no_not_in_forest :
    ∀ (sz : ℕ) {n t : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj] (A : Finset (Fin n))
      (C : Circuit),
      A.card + 2 * K.edgeFinset.card = sz →
      K.IsAcyclic →
      (∀ a ∈ A, ∀ v : Fin n, ¬ K.Adj a v) →
      (A.Nonempty ∨ ∃ u v : Fin n, K.Adj u v) →
      HasMinVC K t →
      (∀ g ∈ C.gates, NOkGate g) →
      circuitFun n C = forestFun0 K A →
      C.size ≤ A.card + K.edgeFinset.card + t →
      Reduced n C →
      ∀ g ∈ C.gates, g.op ≠ GateOp.not := by
  intro sz
  induction sz using Nat.strong_induction_on with
  | _ sz ih =>
    intro n t K _ A C hsz_eq hAcyc hA_iso hne hvc hnok hfun hCsz hred
    have hsz_pos : 1 ≤ A.card + K.edgeFinset.card := by
      rcases hne with ⟨a, ha⟩ | ⟨u, v, huv⟩
      · have := Finset.one_le_card.2 ⟨a, ha⟩; omega
      · have := Finset.one_le_card.2 ⟨s(u, v), SimpleGraph.mem_edgeFinset.2 huv⟩; omega
    by_cases hbase : A.card + K.edgeFinset.card = 1
    · by_cases hAne : A.Nonempty
      · obtain ⟨a, ha⟩ := hAne
        have hA1 : A.card = 1 := by
          have := Finset.one_le_card.2 ⟨a, ha⟩; omega
        have hAeq : A = {a} := Finset.card_eq_one.1 hA1 |> fun ⟨a', ha'⟩ => by
          rw [ha'] at ha; simp at ha; subst ha; exact ha'
        have hE0 : K.edgeFinset.card = 0 := by omega
        have hnoE : ∀ u v : Fin n, ¬ K.Adj u v := by
          intro u v huv
          have := Finset.one_le_card.2 ⟨s(u, v), SimpleGraph.mem_edgeFinset.2 huv⟩; omega
        have ht0 : t = 0 := hasMinVC_empty K hnoE hvc
        exact base_single_A K A a hAeq hnoE C hnok hfun (by simpa [Circuit.size, hA1, hE0, ht0] using hCsz) hred
      · have hA0 : A = ∅ := Finset.not_nonempty_iff_eq_empty.1 hAne
        subst hA0
        obtain ⟨u, v, huv⟩ := hne.resolve_left (by simp)
        have hE1 : K.edgeFinset.card = 1 := by simp at hbase; exact hbase
        have ht1 : t = 1 := by
          have hge1 : 1 ≤ t := by
            obtain ⟨⟨S, hS, hSc⟩, _⟩ := hvc
            rcases hS u v huv with hu | hv
            · have := Finset.one_le_card.2 ⟨u, hu⟩; omega
            · have := Finset.one_le_card.2 ⟨v, hv⟩; omega
          have hle1 : t ≤ 1 := by
            have hvc_u : IsVC K {u} := by
              intro a b hab
              have heq : s(a, b) = s(u, v) := Finset.card_le_one.1 (show K.edgeFinset.card ≤ 1 by omega) s(a, b)
                (SimpleGraph.mem_edgeFinset.2 hab) s(u, v) (SimpleGraph.mem_edgeFinset.2 huv)
              rw [Sym2.eq_iff] at heq
              rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
            simpa using hvc.2 {u} hvc_u
          omega
        exact base_single_edge K u v huv hE1 C hnok hfun
          (by simpa [Circuit.size, hE1, ht1] using hCsz) hred
    · -- Inductive case: A.card + K.edgeFinset.card ≥ 2
      have hge2 : 2 ≤ A.card + K.edgeFinset.card := by omega
      set opt := A.card + K.edgeFinset.card + t - 1 with hopt_def
      have hopt_pos : 1 ≤ opt := by omega
      have hCsz' : C.gates.length ≤ opt + 1 := by
        show C.size ≤ opt + 1; omega
      intro g hg hop
      obtain ⟨j₀, hj₀, rfl⟩ := List.getElem_of_mem hg
      by_cases hAne : A.Nonempty
      · -- Case 1: a ∈ A
        obtain ⟨a, ha⟩ := hAne
        have hcardA : (A.erase a).card + 1 = A.card := by
          have := Finset.one_le_card.2 ⟨a, ha⟩
          rw [Finset.card_erase_of_mem ha]; omega
        have hne' : (A.erase a).Nonempty ∨ ∃ u v : Fin n, K.Adj u v := by
          by_cases hA2 : 2 ≤ A.card
          · left; exact Finset.card_pos.1 (by omega)
          · right
            have hEpos : 0 < K.edgeFinset.card := by omega
            obtain ⟨e, he⟩ := Finset.card_pos.1 hEpos
            induction e using Sym2.ind with
            | _ u v => exact ⟨u, v, SimpleGraph.mem_edgeFinset.1 he⟩
        have hA'_iso : ∀ b ∈ A.erase a, ∀ v : Fin n, ¬ K.Adj b v :=
          fun b hb => hA_iso b (Finset.mem_of_mem_erase hb)
        have hrew := forestFun0_update_A K A a (hA_iso a ha)
        have hinc : ∃ x, circuitFun n C (Function.update x a false) = false ∧
            circuitFun n C (Function.update x a true) = true := by
          rw [hfun]; exact forestFun0_inc_A K A a ha
        have hlb' : ∀ s' < opt - 1, ¬ HasCircuitSize n (forestFun0 K (A.erase a)) s' := by
          intro s' hs' hcs
          have := forest_lower_bound s' K (A.erase a) hAcyc hA'_iso hne' hvc hcs
          omega
        have hIH' : ∀ D : Circuit, (∀ g ∈ D.gates, NOkGate g) →
            circuitFun n D = forestFun0 K (A.erase a) →
            D.size ≤ (opt - 1) + 1 → Reduced n D → ∀ g ∈ D.gates, g.op ≠ GateOp.not := by
          intro D hDnok hDfun hDsz hDred
          exact ih ((A.erase a).card + 2 * K.edgeFinset.card) (by omega) K (A.erase a) D rfl
            hAcyc hA'_iso hne' hvc hDnok hDfun (by omega) hDred
        exact elim_delta1_contra C hnok hred hCsz' a false hinc (forestFun0 K (A.erase a))
          (by rw [hfun]; exact hrew.symm) (forestFun0_nonconst K (A.erase a) hne')
          hlb' hopt_pos hIH' j₀ hj₀ hop
      · -- A = ∅, so 2 ≤ K.edgeFinset.card
        have hA0 : A = ∅ := Finset.not_nonempty_iff_eq_empty.1 hAne
        subst hA0
        have hEge2 : 2 ≤ K.edgeFinset.card := by simp at hge2; exact hge2
        have hEdge : ∃ u v : Fin n, K.Adj u v := hne.resolve_left (by simp)
        by_cases hsib : ∃ ℓ ℓ' p : Fin n, ℓ' ≠ ℓ ∧ K.Adj ℓ p ∧ (∀ w, K.Adj ℓ w → w = p) ∧
            K.Adj ℓ' p ∧ (∀ w, K.Adj ℓ' w → w = p)
        · -- Case 2: sibling leaves ℓ, ℓ' at p
          classical
          obtain ⟨ℓ, ℓ', p, hℓ'ne, hlp, hleaf, hℓ'p, hℓ'leaf⟩ := hsib
          obtain ⟨t₁, hvc₁⟩ := hasMinVC_exists (K.deleteEdges {s(ℓ, p)})
          have ht₁ : t₁ = t := hasMinVC_deleteLeafEdge_eq K ℓ ℓ' p hℓ'ne hℓ'p hℓ'leaf hvc hvc₁
          have hedge := edgeFinset_card_deleteEdge K ℓ p hlp
          have hne' : (∅ : Finset (Fin n)).Nonempty ∨ ∃ u v, (K.deleteEdges {s(ℓ, p)}).Adj u v := by
            right; refine ⟨ℓ', p, SimpleGraph.deleteEdges_adj.2 ⟨hℓ'p, ?_⟩⟩
            simp only [Set.mem_singleton_iff, Sym2.eq_iff]
            rintro (⟨h1, _⟩ | ⟨_, h2⟩)
            · exact hℓ'ne h1
            · exact hlp.ne h2.symm
          have hrew := forestFun0_update_leaf_false K ℓ p hleaf
          have hinc : ∃ x, circuitFun n C (Function.update x ℓ false) = false ∧
              circuitFun n C (Function.update x ℓ true) = true := by
            rw [hfun]; exact forestFun0_inc_edge K ∅ (by simp) ℓ p hlp
          have hlb' : ∀ s' < opt - 1, ¬ HasCircuitSize n (forestFun0 (K.deleteEdges {s(ℓ, p)}) ∅) s' := by
            intro s' hs' hcs
            have := forest_lower_bound s' (K.deleteEdges {s(ℓ, p)}) ∅
              (hAcyc.anti (SimpleGraph.deleteEdges_le _)) (by simp) hne' hvc₁ hcs
            simp only [Finset.card_empty, zero_add] at this hopt_def; omega
          have hIH' : ∀ D : Circuit, (∀ g ∈ D.gates, NOkGate g) →
              circuitFun n D = forestFun0 (K.deleteEdges {s(ℓ, p)}) ∅ →
              D.size ≤ (opt - 1) + 1 → Reduced n D → ∀ g ∈ D.gates, g.op ≠ GateOp.not := by
            intro D hDnok hDfun hDsz hDred
            exact ih ((∅ : Finset (Fin n)).card + 2 * (K.deleteEdges {s(ℓ, p)}).edgeFinset.card)
              (by simp at hsz_eq ⊢; omega) (K.deleteEdges {s(ℓ, p)}) ∅ D rfl
              (hAcyc.anti (SimpleGraph.deleteEdges_le _)) (by simp) hne' hvc₁ hDnok hDfun
              (by simp only [Finset.card_empty, zero_add] at hopt_def ⊢; omega) hDred
          exact elim_delta1_contra C hnok hred hCsz' ℓ false hinc
            (forestFun0 (K.deleteEdges {s(ℓ, p)}) ∅) (by rw [hfun]; exact hrew.symm)
            (forestFun0_nonconst (K.deleteEdges {s(ℓ, p)}) ∅ hne') hlb' hopt_pos hIH' j₀ hj₀ hop
        · by_cases hiso : ∃ ℓ p : Fin n, K.Adj ℓ p ∧ (∀ w, K.Adj ℓ w → w = p) ∧ (∀ w, K.Adj p w → w = ℓ)
          · -- Case 3: isolated edge {ℓ, p}
            classical
            obtain ⟨ℓ, p, hlp, hleaf, hpdeg1⟩ := hiso
            obtain ⟨t', hvc'⟩ := hasMinVC_exists (deleteVertexEdges K p)
            have ht' : t' + 1 = t := hasMinVC_deleteVertex K ℓ p hlp hleaf hvc hvc'
            have hedge := edgeFinset_card_deleteVertex_deg1 K ℓ p hlp hpdeg1
            have hne' : ({p} : Finset (Fin n)).Nonempty ∨ ∃ u v, (deleteVertexEdges K p).Adj u v :=
              Or.inl (Finset.singleton_nonempty p)
            have hp_iso : ∀ a ∈ ({p} : Finset (Fin n)), ∀ v : Fin n, ¬ (deleteVertexEdges K p).Adj a v := by
              intro a ha v h; simp at ha; subst ha; exact h.2.1 rfl
            have hrew := forestFun0_update_leaf_true K ℓ p hlp hleaf
            have hinc : ∃ x, circuitFun n C (Function.update x ℓ false) = false ∧
                circuitFun n C (Function.update x ℓ true) = true := by
              rw [hfun]; exact forestFun0_inc_edge K ∅ (by simp) ℓ p hlp
            have hlb' : ∀ s' < opt - 1, ¬ HasCircuitSize n (forestFun0 (deleteVertexEdges K p) {p}) s' := by
              intro s' hs' hcs
              have := forest_lower_bound s' (deleteVertexEdges K p) {p}
                (hAcyc.anti (deleteVertexEdges_le K p)) hp_iso hne' hvc' hcs
              simp only [Finset.card_singleton, Finset.card_empty, zero_add] at this hopt_def; omega
            have hIH' : ∀ D : Circuit, (∀ g ∈ D.gates, NOkGate g) →
                circuitFun n D = forestFun0 (deleteVertexEdges K p) {p} →
                D.size ≤ (opt - 1) + 1 → Reduced n D → ∀ g ∈ D.gates, g.op ≠ GateOp.not := by
              intro D hDnok hDfun hDsz hDred
              exact ih (({p} : Finset (Fin n)).card + 2 * (deleteVertexEdges K p).edgeFinset.card)
                (by simp only [Finset.card_singleton, Finset.card_empty, zero_add] at hsz_eq ⊢; omega)
                (deleteVertexEdges K p) {p} D rfl
                (hAcyc.anti (deleteVertexEdges_le K p)) hp_iso hne' hvc' hDnok hDfun
                (by simp only [Finset.card_singleton, Finset.card_empty, zero_add] at hopt_def ⊢; omega) hDred
            exact elim_delta1_contra C hnok hred hCsz' ℓ true hinc
              (forestFun0 (deleteVertexEdges K p) {p}) (by rw [hfun]; exact hrew.symm)
              (forestFun0_nonconst (deleteVertexEdges K p) {p} hne') hlb' hopt_pos hIH' j₀ hj₀ hop
          · -- Case 4: two distinct leaves ℓ₁ ≠ ℓ₂ with deg-2 parents!
            classical
            obtain ⟨ℓ₁, p₁, q₁, ℓ₂, p₂, q₂, h12ne,
              h1p, h1leaf, hq1ne, hp1q1, hp1deg2,
              h2p, h2leaf, hq2ne, hp2q2, hp2deg2⟩ :=
              acyclic_two_deg2_leaves K hAcyc hEdge hsib hiso
            have hopt_ge2 : 2 ≤ opt := by
              have ht_pos : 1 ≤ t := by
                obtain ⟨⟨S, hS, hSc⟩, _⟩ := hvc
                rcases hS ℓ₁ p₁ h1p with h1 | h2
                · have := Finset.one_le_card.2 ⟨ℓ₁, h1⟩; omega
                · have := Finset.one_le_card.2 ⟨p₁, h2⟩; omega
              simp only [Finset.card_empty, zero_add] at hopt_def; omega
            have hleaf_res : ∀ (ℓ p q : Fin n),
                K.Adj ℓ p → (∀ w, K.Adj ℓ w → w = p) → q ≠ ℓ → K.Adj p q →
                (∀ w, K.Adj p w → w = ℓ ∨ w = q) →
                ∃ j_n j₁ : ℕ, ∃ (_hjn : j_n < C.gates.length) (hj₁ : j₁ < C.gates.length),
                  (∀ j : ℕ, (hj : j < C.gates.length) → C.gates[j].op = GateOp.not → j = j_n) ∧
                  (ℓ : ℕ) ∈ (C.gates[j₁]'hj₁).inputs ∧
                  (n + j_n) ∈ (C.gates[j₁]'hj₁).inputs ∧
                  (∀ j : ℕ, (hj : j < C.gates.length) → (n + j_n) ∈ C.gates[j].inputs → j = j₁) := by
              intro ℓ p q hlp hleaf hqne hpq hpdeg2
              obtain ⟨t₀, hvc₀⟩ := hasMinVC_exists (K.deleteEdges {s(ℓ, p)})
              have ht₀ := hasMinVC_deleteEdge K ℓ p hvc hvc₀
              have hedge₀ := edgeFinset_card_deleteEdge K ℓ p hlp
              obtain ⟨t₁, hvc₁⟩ := hasMinVC_exists (deleteVertexEdges K p)
              have ht₁ : t₁ + 1 = t := hasMinVC_deleteVertex K ℓ p hlp hleaf hvc hvc₁
              have hedge₁ := edgeFinset_card_deleteVertex_deg2 K ℓ p q hlp hpq hqne hpdeg2
              have hne₀ : (∅ : Finset (Fin n)).Nonempty ∨ ∃ u v, (K.deleteEdges {s(ℓ, p)}).Adj u v := by
                right; refine ⟨p, q, SimpleGraph.deleteEdges_adj.2 ⟨hpq, ?_⟩⟩
                simp only [Set.mem_singleton_iff, Sym2.eq_iff]
                rintro (⟨h1, _⟩ | ⟨_, h2⟩)
                · exact hlp.ne h1.symm
                · exact hqne h2
              have hne₁ : ({p} : Finset (Fin n)).Nonempty ∨ ∃ u v, (deleteVertexEdges K p).Adj u v :=
                Or.inl (Finset.singleton_nonempty p)
              have hp_iso : ∀ a ∈ ({p} : Finset (Fin n)), ∀ v : Fin n, ¬ (deleteVertexEdges K p).Adj a v := by
                intro a ha v h; simp at ha; subst ha; exact h.2.1 rfl
              have hrew0 := forestFun0_update_leaf_false K ℓ p hleaf
              have hrew1 := forestFun0_update_leaf_true K ℓ p hlp hleaf
              have hinc : ∃ x, circuitFun n C (Function.update x ℓ false) = false ∧
                  circuitFun n C (Function.update x ℓ true) = true := by
                rw [hfun]; exact forestFun0_inc_edge K ∅ (by simp) ℓ p hlp
              have hlb0 : ∀ s' < opt - 2, ¬ HasCircuitSize n (forestFun0 (K.deleteEdges {s(ℓ, p)}) ∅) s' := by
                intro s' hs' hcs
                have := forest_lower_bound s' (K.deleteEdges {s(ℓ, p)}) ∅
                  (hAcyc.anti (SimpleGraph.deleteEdges_le _)) (by simp) hne₀ hvc₀ hcs
                simp only [Finset.card_empty, zero_add] at this hopt_def; omega
              have hlb1 : ∀ s' < opt - 2, ¬ HasCircuitSize n (forestFun0 (deleteVertexEdges K p) {p}) s' := by
                intro s' hs' hcs
                have := forest_lower_bound s' (deleteVertexEdges K p) {p}
                  (hAcyc.anti (deleteVertexEdges_le K p)) hp_iso hne₁ hvc₁ hcs
                simp only [Finset.card_singleton, Finset.card_empty, zero_add] at this hopt_def; omega
              have hIH0 : ∀ D : Circuit, (∀ g ∈ D.gates, NOkGate g) →
                  circuitFun n D = forestFun0 (K.deleteEdges {s(ℓ, p)}) ∅ →
                  D.size ≤ (opt - 2) + 1 → Reduced n D → ∀ g ∈ D.gates, g.op ≠ GateOp.not := by
                intro D hDnok hDfun hDsz hDred
                exact ih ((∅ : Finset (Fin n)).card + 2 * (K.deleteEdges {s(ℓ, p)}).edgeFinset.card)
                  (by simp only [Finset.card_empty, zero_add] at hsz_eq ⊢; omega)
                  (K.deleteEdges {s(ℓ, p)}) ∅ D rfl
                  (hAcyc.anti (SimpleGraph.deleteEdges_le _)) (by simp) hne₀ hvc₀ hDnok hDfun
                  (by simp only [Finset.card_empty, zero_add] at hopt_def ⊢; omega) hDred
              have hIH1 : ∀ D : Circuit, (∀ g ∈ D.gates, NOkGate g) →
                  circuitFun n D = forestFun0 (deleteVertexEdges K p) {p} →
                  D.size ≤ (opt - 2) + 1 → Reduced n D → ∀ g ∈ D.gates, g.op ≠ GateOp.not := by
                intro D hDnok hDfun hDsz hDred
                exact ih (({p} : Finset (Fin n)).card + 2 * (deleteVertexEdges K p).edgeFinset.card)
                  (by simp only [Finset.card_singleton, Finset.card_empty, zero_add] at hsz_eq ⊢; omega)
                  (deleteVertexEdges K p) {p} D rfl
                  (hAcyc.anti (deleteVertexEdges_le K p)) hp_iso hne₁ hvc₁ hDnok hDfun
                  (by simp only [Finset.card_singleton, Finset.card_empty, zero_add] at hopt_def ⊢; omega) hDred
              exact elim_delta2_leaf C hnok hred hCsz' ℓ hinc hopt_ge2
                (forestFun0 (K.deleteEdges {s(ℓ, p)}) ∅) (forestFun0 (deleteVertexEdges K p) {p})
                (by rw [hfun]; exact hrew0.symm) (by rw [hfun]; exact hrew1.symm)
                (forestFun0_nonconst _ _ hne₀) (forestFun0_nonconst _ _ hne₁)
                hlb0 hlb1 hIH0 hIH1 j₀ hj₀ hop
            obtain ⟨jn₁, j₁, hjn₁, hj₁, huniq₁, hℓ1_in, hjn1_in, hcons₁⟩ :=
              hleaf_res ℓ₁ p₁ q₁ h1p h1leaf hq1ne hp1q1 hp1deg2
            obtain ⟨jn₂, j₂, hjn₂, hj₂, huniq₂, hℓ2_in, hjn2_in, hcons₂⟩ :=
              hleaf_res ℓ₂ p₂ q₂ h2p h2leaf hq2ne hp2q2 hp2deg2
            have hjneq : jn₁ = jn₂ := (huniq₂ j₀ hj₀ hop).symm.trans (huniq₁ j₀ hj₀ hop) |> Eq.symm
            subst hjneq
            have hj12 : j₁ = j₂ := (hcons₂ j₁ hj₁ hjn1_in)
            subst hj12
            -- Gate j₁ has inputs of length ≤ 2 containing n + jn₁, ℓ₁, ℓ₂!
            have hlen2 := (hnok _ (List.getElem_mem hj₁)).1.2
            rcases hins : C.gates[j₁].inputs with _ | ⟨w₁, _ | ⟨w₂, _ | ⟨w₃, l⟩⟩⟩
            · rw [hins] at hℓ1_in; simp at hℓ1_in
            · rw [hins] at hℓ1_in hjn1_in; simp at hℓ1_in hjn1_in; omega
            · rw [hins] at hℓ1_in hℓ2_in hjn1_in; simp at hℓ1_in hℓ2_in hjn1_in
              rcases hjn1_in with rfl | rfl
              · have h1 : (ℓ₁ : ℕ) = w₂ := hℓ1_in.resolve_left (by omega)
                have h2 : (ℓ₂ : ℕ) = w₂ := hℓ2_in.resolve_left (by omega)
                exact h12ne (Fin.ext (h1.trans h2.symm))
              · have h1 : (ℓ₁ : ℕ) = w₁ := hℓ1_in.resolve_right (by omega)
                have h2 : (ℓ₂ : ℕ) = w₁ := hℓ2_in.resolve_right (by omega)
                exact h12ne (Fin.ext (h1.trans h2.symm))
            · rw [hins] at hlen2; simp at hlen2

theorem PEqualNP.Outside.L_meta_551 : ∀ (n t : ℕ) (K : SimpleGraph (Fin n)) [DecidableRel K.Adj] (A : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), K.IsAcyclic → (∀ a ∈ A, ∀ v : Fin n, ¬ K.Adj a v) → (A.Nonempty ∨ ∃ u v : Fin n, K.Adj u v) → (∀ i : Fin n, i ∈ A ∨ ∃ v : Fin n, K.Adj i v) → (∃ S : Finset (Fin n), K.IsVertexCover (S : Set (Fin n)) ∧ S.card = t) → (∀ S : Finset (Fin n), K.IsVertexCover (S : Set (Fin n)) → t ≤ S.card) → PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.circuitFun n C = (fun x : Fin n → Bool => decide ((∃ a ∈ A, x a = true) ∨ ∃ u v : Fin n, K.Adj u v ∧ x u = true ∧ x v = true)) → C.size ≤ A.card + K.edgeFinset.card + t → (∀ j : ℕ, j < C.gates.length → ∃ x y : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j) false ≠ (C.wires (List.ofFn y)).getD (n + j) false) ∧ (∀ i j : ℕ, i < n + j → j < C.gates.length → ∃ x : Fin n → Bool, (C.wires (List.ofFn x)).getD i false ≠ (C.wires (List.ofFn x)).getD (n + j) false) ∧ (C.gates ≠ [] → C.output + 1 = n + C.gates.length) ∧ (∀ j : ℕ, j + 1 < C.gates.length → ∃ p ∈ C.gates.zipIdx, n + j < n + p.2 ∧ (PEqualNP.CircuitLowerBounds.GateOp.casesOn (motive := fun _ => List ℕ) p.1.op p.1.inputs p.1.inputs (p.1.inputs.take 1) (fun _ => p.1.inputs) p.1.inputs).contains (n + j) = true) → ∀ g ∈ C.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not := by
  intro n t K _ A C hAcyc hA_iso hne _ hex_vc hmin_vc hfan hfun hCsz hred g hg
  set C' : Circuit := ⟨C.gates.map normGate, C.output⟩ with hC'
  have hnok' : ∀ g' ∈ C'.gates, NOkGate g' := by
    intro g' hg'
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg'
    exact normGate_nok g0 (hfan g0 hg0)
  have hfun' : circuitFun n C' = forestFun0 K A := by
    have hfeq : forestFun0 K A = circuitFun n C := hfun.symm
    rw [hfeq]; funext x
    show (wiresFrom (C.gates.map normGate) (List.ofFn x)).getD C.output false =
      (wiresFrom C.gates (List.ofFn x)).getD C.output false
    rw [wiresFrom_norm]
  have hsz' : C'.size ≤ A.card + K.edgeFinset.card + t := by
    simpa [Circuit.size, hC'] using hCsz
  have hred' : Reduced n C' := reduced_norm n C hred
  have hvc : HasMinVC K t := by
    refine ⟨?_, ?_⟩
    · obtain ⟨S, hS, hSc⟩ := hex_vc
      exact ⟨S, (isVertexCover_iff_isVC K S).1 hS, hSc⟩
    · intro S hS
      exact hmin_vc S ((isVertexCover_iff_isVC K S).2 hS)
  have hnoNot := no_not_in_forest (A.card + 2 * K.edgeFinset.card) K A C' rfl
    hAcyc hA_iso hne hvc hnok' hfun' hsz' hred'
  have hg' : normGate g ∈ C'.gates := List.mem_map.2 ⟨g, hg, rfl⟩
  have hne_not := hnoNot (normGate g) hg'
  intro hop
  apply hne_not
  rcases g with ⟨op, ins⟩
  simp only at hop
  subst hop
  rfl
