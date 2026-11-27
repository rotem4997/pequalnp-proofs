import PEqualNP.Defs

namespace PEqualNP.Outside.Meta525

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The circuit restriction argument through elim_two_var is taken from L_meta_468.
-- Normalizing NOT to one operand lets the elimination pass count actual reads.
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

private lemma elimPass_len_lt (m k : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, NOkGate g) (hk : k < acc.1.length)
    (hc : ∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c)
    (hex : ∃ g ∈ gs, k ∈ g.inputs) :
    (elimPass m gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => obtain ⟨g, hg, _⟩ := hex; simp at hg
  | cons g gs ih =>
    rw [elimPass_cons, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplifyGate g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplifyGate_none_of_const
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep m acc g).2.length = acc.2.length := by
        simp only [elimStep, hnone, Option.toList_none, List.append_nil]
      have := elimPass_len m gs (elimStep m acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep m acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          exact ⟨c, by simp only [elimStep]; rw [getD_snoc_lt _ _ _ _ hk]; exact hc⟩)
        hex'
      have h2 : (elimStep m acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_opt_len_le (simplifyGate g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

private lemma elimPass_len_two (m k : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, NOkGate g) (hk : k < acc.1.length)
    (hc : ∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c)
    (htwo : 2 ≤ (gs.filter (fun g => decide (k ∈ g.inputs))).length) :
    (elimPass m gs acc).2.length + 2 ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp at htwo
  | cons g gs ih =>
    rw [elimPass_cons, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplifyGate g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplifyGate_none_of_const
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep m acc g).2.length = acc.2.length := by
        simp only [elimStep, hnone, Option.toList_none, List.append_nil]
      have hfilt : 1 ≤ (gs.filter (fun g => decide (k ∈ g.inputs))).length := by
        simp [hkg] at htwo
        omega
      have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        have hne : gs.filter (fun g => decide (k ∈ g.inputs)) ≠ [] := by
          intro hnil; rw [hnil] at hfilt; simp at hfilt
        obtain ⟨g', hg'⟩ := List.exists_mem_of_ne_nil _ hne
        rw [List.mem_filter] at hg'
        exact ⟨g', hg'.1, of_decide_eq_true hg'.2⟩
      have h1 := elimPass_len_lt m k gs (elimStep m acc g)
        (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        ⟨c, by simp only [elimStep]; rw [getD_snoc_lt _ _ _ _ hk]; exact hc⟩
        hex'
      omega
    · have htwo' : 2 ≤ (gs.filter (fun g => decide (k ∈ g.inputs))).length := by
        simpa [hkg] using htwo
      have h1 := ih (elimStep m acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          exact ⟨c, by simp only [elimStep]; rw [getD_snoc_lt _ _ _ _ hk]; exact hc⟩)
        htwo'
      have h2 : (elimStep m acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_opt_len_le (simplifyGate g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
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

-- A natural number stores one wire column, with one bit per input assignment.
-- On the rows selected by P, the output must match the target column T.
-- Extra columns record values computed by the first gates. The remaining
-- circuit can act arbitrarily on assignments outside these sample rows.
private def sample (W : List ℕ) (r : ℕ) (i : Fin W.length) : Bool :=
  W[(i : ℕ)].testBit r

private def fits (W : List ℕ) (T P : ℕ) (F : (Fin W.length → Bool) → Bool) : Prop :=
  ∀ r, P.testBit r = true → F (sample W r) = T.testBit r

private def lower (W : List ℕ) (T P n : ℕ) : Prop :=
  ∀ F s, fits W T P F → HasCircuitSize W.length F s → n ≤ s

private def cut (P w : ℕ) (b : Bool) := if b then P &&& w else P ^^^ (P &&& w)

private lemma bit_cut (P w r : ℕ) (b : Bool) :
    (cut P w b).testBit r = true ↔ P.testBit r = true ∧ w.testBit r = b := by
  cases b <;> simp only [cut, Nat.testBit_and, Nat.testBit_xor, Bool.false_eq_true,
    ↓reduceIte] <;> cases P.testBit r <;> cases w.testBit r <;> decide

private lemma bit_exists {w : ℕ} (h : w ≠ 0) : ∃ r, w.testBit r = true := by
  by_contra! hn
  apply h
  apply Nat.eq_of_testBit_eq
  intro r
  simp [hn]

private def mixed (T P : ℕ) : Bool := (P &&& T != 0) && (P ^^^ (P &&& T) != 0)

private lemma mix_witness {T P : ℕ} (h : mixed T P = true) :
    ∃ a b, P.testBit a = true ∧ P.testBit b = true ∧ T.testBit a ≠ T.testBit b := by
  simp only [mixed, Bool.and_eq_true, bne_iff_ne] at h
  obtain ⟨a, ha⟩ := bit_exists h.1
  obtain ⟨b, hb⟩ := bit_exists h.2
  have ha' := (bit_cut P T a true).1 ha
  have hb' := (bit_cut P T b false).1 hb
  exact ⟨a,b,ha'.1,hb'.1,by simp [ha'.2,hb'.2]⟩

private def noOutput (W : List ℕ) (T P : ℕ) :=
  (0 :: W).all fun w => ((T ^^^ w) &&& P) != 0

private lemma noOutput_sound {W : List ℕ} {T P : ℕ} (h : noOutput W T P = true) :
    lower W T P 1 := by
  intro F s hf hc
  obtain ⟨C, _, hsz, he⟩ := hc
  by_contra! hn
  have hem : C.gates = [] := List.eq_nil_of_length_eq_zero (by change C.gates.length ≤ s at hsz; omega)
  let w := W.getD C.output 0
  have hw : w ∈ 0 :: W := by
    by_cases h : C.output < W.length
    · rw [show w = W[C.output] from List.getD_eq_getElem _ _ h]; exact List.mem_cons_of_mem _ (List.getElem_mem _)
    · rw [show w = 0 from List.getD_eq_default _ _ (by omega)]; exact List.mem_cons_self
  obtain ⟨r,hr⟩ := bit_exists (show (T ^^^ w) &&& P ≠ 0 from by
    simpa using List.all_eq_true.mp h w hw)
  simp only [Nat.testBit_and, Nat.testBit_xor, Bool.and_eq_true] at hr
  have heq := (he (sample W r)).trans (hf r hr.2)
  have hout : C.eval (List.ofFn (sample W r)) = w.testBit r := by
    simp only [Circuit.eval, Circuit.wires, hem, List.foldl_nil]
    by_cases hi : C.output < W.length
    · rw [ofFn_getD_lt _ _ _ hi]; rw [show w = W[C.output] from List.getD_eq_getElem _ _ hi]; rfl
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)]
      rw [show w = 0 from List.getD_eq_default _ _ (Nat.le_of_not_gt hi)]; simp
  rw [← heq, hout] at hr
  simpa using hr.1

-- Two rows that differ only at wire i but have distinct target values certify
-- that every total function fitting these rows depends on wire i.
private def depTest (W : List ℕ) (T P : ℕ) (i : Fin W.length) (a b : ℕ) :=
  P.testBit a && P.testBit b && (T.testBit a != T.testBit b) &&
  !((W[i]).testBit a) && (W[i]).testBit b &&
  (List.finRange W.length).all fun j => decide (j = i) || (W[j].testBit a == W[j].testBit b)

private lemma dep_sound {W : List ℕ} {T P a b : ℕ} {F} (i : Fin W.length)
    (hf : fits W T P F) (h : depTest W T P i a b = true) :
    ∃ x, F (Function.update x i false) ≠ F (Function.update x i true) := by
  simp only [depTest, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne,
    List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨ha,hb⟩,hne⟩,hia⟩,hib⟩,hall⟩ := h
  refine ⟨sample W a, ?_⟩
  have h0 : Function.update (sample W a) i false = sample W a := by
    funext j; by_cases hj : j = i
    · subst j; simpa [sample] using hia.symm
    · simp [hj]
  have h1 : Function.update (sample W a) i true = sample W b := by
    funext j; by_cases hj : j = i
    · subst j; simpa [sample] using hib.symm
    · rw [Function.update_of_ne hj]; exact (hall j (by simp)).resolve_left hj
  simpa [h0,h1,hf a ha,hf b hb] using hne

private lemma fits_cut {W : List ℕ} {F T P} (hf : fits W T P F) (i : Fin W.length) (b : Bool) :
    fits W T (cut P W[i] b) (fun x => F (Function.update x i b)) := by
  intro r hr
  obtain ⟨hp, hi⟩ := (bit_cut _ _ _ _).1 hr
  have he : Function.update (sample W r) i b = sample W r := by
    funext j; by_cases hj : j = i
    · subst j; simpa [sample] using hi.symm
    · simp [hj]
  simpa [he] using hf r hp

private lemma nc_cut {W : List ℕ} {F T P} (hf : fits W T P F) (i : Fin W.length) (b : Bool)
    (h : mixed T (cut P W[i] b) = true) :
    ∃ x y, F (Function.update x i b) ≠ F (Function.update y i b) := by
  obtain ⟨a,c,ha,hc,hne⟩ := mix_witness h
  refine ⟨sample W a, sample W c, ?_⟩
  exact fun eq => hne (((fits_cut hf i b a ha).symm.trans eq).trans (fits_cut hf i b c hc))

private lemma cut_one {W : List ℕ} {T P n a b} (i : Fin W.length) (v : Bool)
    (hd : depTest W T P i a b = true) (hm : mixed T (cut P W[i] v) = true)
    (hl : lower W T (cut P W[i] v) (n-1)) : lower W T P n := by
  intro F s hf hc
  obtain ⟨hs,hc'⟩ := elim_one_var i v hc (dep_sound i hf hd) (nc_cut hf i v hm)
  have := hl _ _ (fits_cut hf i v) hc'
  omega

private lemma cut_two {W : List ℕ} {T P n a b} (i : Fin W.length)
    (hd : depTest W T P i a b = true)
    (hm : ∀ v, mixed T (cut P W[i] v) = true)
    (hl : ∀ v, lower W T (cut P W[i] v) (n-2)) : lower W T P n := by
  intro F s hf hc
  obtain ⟨hs,hc'|hc'⟩ := elim_two_var i hc (dep_sound i hf hd)
    (nc_cut hf i false (hm false)) (nc_cut hf i true (hm true))
  · have := hl false _ _ (fits_cut hf i false) hc'; omega
  · have := hl true _ _ (fits_cut hf i true) hc'; omega

private lemma cut_free {W : List ℕ} {T P n} (i : Fin W.length) (v : Bool)
    (hl : lower W T (cut P W[i] v) n) : lower W T P n := by
  intro F s hf hc
  exact hl F s (fun r hr => hf r ((bit_cut _ _ _ _).1 hr).1) hc

-- Certificate nodes are packed in preorder, low word first, 32 bits per node.
-- Bits 0 to 3 select the wire. Bits 4 to 5 select its restriction rule.
-- Rules 0 and 1 save one gate by fixing the wire to false or true. Rule 2
-- saves two gates for at least one value, so both children must pass.
-- Rule 3 narrows the sample using bit 24 and claims no gate saving.
-- Bits 6 to 14 and 15 to 23 name the two dependency witnesses. For rule 2,
-- bits 25 to 31 give the left subtree length in words. Bounds zero and one
-- terminate without consuming a word.
private def verify (W : List ℕ) (T : ℕ) : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, _, _ => false
  | fuel+1, P, n, c =>
    if n = 0 then true else if n = 1 then noOutput W T P else
    if hi : c % 16 < W.length then
      let i : Fin W.length := ⟨_,hi⟩
      let k := (c >>> 4) % 4
      let b := c.testBit 4
      let d := depTest W T P i ((c >>> 6) % 512) ((c >>> 15) % 512)
      let rest := c >>> 32
      let side := fun b => cut P W[i] b
      if k = 3 then verify W T fuel (side (c.testBit 24)) n rest
      else if k = 2 then d && mixed T (side false) && mixed T (side true) &&
        verify W T fuel (side false) (n-2) rest &&
        verify W T fuel (side true) (n-2) (rest >>> (32 * ((c >>> 25) % 128)))
      else d && mixed T (side b) && verify W T fuel (side b) (n-1) rest
    else false

private lemma verify_sound {W : List ℕ} {T fuel P n c : ℕ}
    (h : verify W T fuel P n c = true) : lower W T P n := by
  induction fuel generalizing P n c with
  | zero => contradiction
  | succ f ih =>
    rw [verify] at h
    split at h
    · subst n; exact fun _ _ _ _ => Nat.zero_le _
    split at h
    · subst n; exact noOutput_sound h
    split at h
    · dsimp only at h
      split at h
      · exact cut_free _ _ (ih h)
      split at h
      · simp only [Bool.and_eq_true] at h
        exact cut_two _ h.1.1.1.1 (fun | false => h.1.1.1.2 | true => h.1.1.2)
          (fun | false => ih h.1.2 | true => ih h.2)
      · simp only [Bool.and_eq_true] at h
        exact cut_one _ _ h.1.1 h.1.2 (ih h.2)
    · contradiction

-- Every possible next gate produces one of these columns on the selected rows.
-- Including zero among the reads also covers out-of-range wire indices.
private def nextCols (W : List ℕ) (P : ℕ) :=
  let R := 0 :: W
  [P] ++ R ++ R.map (fun a => P ^^^ a) ++
    R.flatMap (fun a => R.flatMap (fun b => [a &&& b, a ||| b]))

private lemma next_spec {W : List ℕ} {P : ℕ} {g : Gate} (hg : OkGate g) :
    ∃ w ∈ nextCols W P, ∀ r, P.testBit r = true →
      g.op.eval (g.inputs.map fun i => (List.ofFn (sample W r)).getD i false) = w.testBit r := by
  let R := 0 :: W
  have hmem (i : ℕ) : W.getD i 0 ∈ R := by
    by_cases hi : i < W.length
    · rw [List.getD_eq_getElem _ _ hi]; exact List.mem_cons_of_mem _ (List.getElem_mem _)
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi)]; exact List.mem_cons_self
  have hread (i r : ℕ) :
      (List.ofFn (sample W r)).getD i false = (W.getD i 0).testBit r := by
    rw [show List.ofFn (sample W r) = W.map (fun a => a.testBit r) from
      List.ofFn_getElem_eq_map W (fun a => a.testBit r)]
    simpa only [Nat.zero_testBit] using List.getD_map W 0 (n := i) (fun a : ℕ => a.testBit r)
  have memP : P ∈ nextCols W P := by simp [nextCols]
  have memR {a} (ha : a ∈ R) : a ∈ nextCols W P := by
    simp only [nextCols, List.mem_append]; exact Or.inl (Or.inl (Or.inr ha))
  have memN {a} (ha : a ∈ R) : P ^^^ a ∈ nextCols W P := by
    simp only [nextCols,List.mem_append]; exact Or.inl (Or.inr (List.mem_map.mpr ⟨_,ha,rfl⟩))
  have memB {a b} (ha : a ∈ R) (hb : b ∈ R) {w} (hw : w ∈ [a &&& b, a ||| b]) :
      w ∈ nextCols W P := by
    apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨a,ha,List.mem_flatMap.mpr ⟨b,hb,hw⟩⟩
  obtain ⟨hop,hlen⟩ := hg
  rcases hop with hop|hop|hop
  · change g.op = GateOp.and at hop
    rcases he : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨k,l⟩⟩⟩
    · exact ⟨P,memP,fun r hr => by simp [hop,GateOp.eval,hr]⟩
    · exact ⟨_,memR (hmem i),fun r _ => by simp only [List.map_cons, List.map_nil, hread]; simp [hop,GateOp.eval]⟩
    · exact ⟨_,memB (hmem i) (hmem j) (List.mem_cons_self),fun r _ => by
        simp only [List.map_cons, List.map_nil, hread]; simp [hop,GateOp.eval,Nat.testBit_and]⟩
    · simp [he] at hlen
  · change g.op = GateOp.or at hop
    rcases he : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨k,l⟩⟩⟩
    · exact ⟨0,memR List.mem_cons_self,fun r _ => by simp [hop,GateOp.eval]⟩
    · exact ⟨_,memR (hmem i),fun r _ => by simp only [List.map_cons, List.map_nil, hread]; simp [hop,GateOp.eval]⟩
    · exact ⟨_,memB (hmem i) (hmem j) (List.mem_cons_of_mem _ List.mem_cons_self),fun r _ => by
        simp only [List.map_cons, List.map_nil, hread]; simp [hop,GateOp.eval,Nat.testBit_or]⟩
    · simp [he] at hlen
  · change g.op = GateOp.not at hop
    cases he : g.inputs with
    | nil => exact ⟨P,memP,fun r hr => by simp [hop,GateOp.eval,hr]⟩
    | cons i l => exact ⟨_,memN (hmem i),fun r hr => by
        simp only [List.map_cons, hread]; simp [hop,GateOp.eval,Nat.testBit_xor,hr]⟩

private lemma split_lower {W : List ℕ} {T P n : ℕ} (h0 : noOutput W T P = true)
    (hn : ∀ w ∈ nextCols W P, lower (W ++ [w]) T P n) : lower W T P (n+1) := by
  intro F s hf hc
  obtain ⟨C,hok,hs,he⟩ := hc
  cases hgs : C.gates with
  | nil =>
    have hz : HasCircuitSize W.length F 0 := ⟨C,hok,by simp [Circuit.size,hgs],he⟩
    have := noOutput_sound h0 F 0 hf hz
    omega
  | cons g gs =>
    obtain ⟨w,hw,hg⟩ := next_spec (W := W) (P := P) (hok g (by simp [hgs]))
    let D : Circuit := ⟨gs,C.output⟩
    let f := fun x : Fin (W ++ [w]).length → Bool => D.eval (List.ofFn x)
    have hd : HasCircuitSize (W ++ [w]).length f gs.length := by
      refine ⟨D,fun g' hg' => hok g' (by rw [hgs]; exact List.mem_cons_of_mem _ hg'),le_rfl,fun _ => rfl⟩
    have hfit : fits (W ++ [w]) T P f := by
      intro r hr
      have hgate := hg r hr
      have hrow (V : List ℕ) : List.ofFn (sample V r) = V.map (fun a => a.testBit r) :=
        List.ofFn_getElem_eq_map V (fun a => a.testBit r)
      have hv := (he (sample W r)).trans (hf r hr)
      change (wiresFrom C.gates _).getD C.output false = _ at hv
      rw [hgs,wiresFrom_cons,hgate,hrow] at hv
      change (wiresFrom gs (List.ofFn (sample (W ++ [w]) r))).getD C.output false = _
      simpa only [hrow,List.map_append,List.map_cons,List.map_nil] using hv
    have hn' := hn w hw f _ hfit hd
    simp only [Circuit.size,hgs,List.length_cons] at hs
    omega

private lemma certified_split {W : List ℕ} {T P n : ℕ} (cases : List (ℕ × ℕ)) (more : List ℕ)
    (h0 : noOutput W T P = true)
    (hcover : (nextCols W P).all (fun w => more.contains w || cases.any (fun p => p.1 == w)) = true)
    (hcheck : cases.all (fun p => verify (W ++ [p.1]) T 16 P n p.2) = true)
    (hextra : ∀ w ∈ more, lower (W ++ [w]) T P n) : lower W T P (n+1) := by
  apply split_lower h0
  intro w hw
  have h := List.all_eq_true.mp hcover w hw
  simp only [Bool.or_eq_true,List.contains_iff_mem,List.any_eq_true,beq_iff_eq] at h
  rcases h with h | ⟨p,hp,h⟩
  · exact hextra w h
  · subst w
    exact verify_sound (List.all_eq_true.mp hcheck p hp)

-- In the 512-row table, row r assigns bit i of r to input i.
private def x0 : ℕ := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
private def x1 : ℕ := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
private def x2 : ℕ := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
private def x3 : ℕ := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00
private def x4 : ℕ := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
private def x5 : ℕ := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000
private def x6 : ℕ := 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
private def x7 : ℕ := 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000
private def x8 : ℕ := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000
private def rows : ℕ := 2^512-1
private def initial := [x0, x1, x2, x3, x4, x5, x6, x7, x8]
private def target := (x0 &&& x1) ||| (x1 &&& x2) ||| (x2 &&& x3) ||| (x3 &&& x4) ||| (x4 &&& x5) ||| (x5 &&& x6) ||| (x6 &&& x7) ||| (x0 &&& x7) ||| (x0 &&& x8)
-- Only the leaf edge requires a second split. Its two exceptional successors
-- are exchanged by the reflection of the cycle fixing vertices zero and four.
private def leafEdge := x0 &&& x8
private def leafOrOne := leafEdge ||| x1
private def leafOrSeven := leafEdge ||| x7
private def prefix1 := initial ++ [leafEdge]
private def prefix2 := prefix1 ++ [leafOrOne]
private def prefix3 := prefix1 ++ [leafOrSeven]

-- Each pair gives a possible gate output and a certificate for the suffix.
-- The four applications of certified_split also check coverage of all outputs.
private def certificates3 : List (ℕ × ℕ) := [
  (0, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080),
  (rows ^^^ x8, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080),
  (rows ^^^ leafOrSeven, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080),
  (rows ^^^ x7, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080),
  (rows ^^^ x6, 0x34926500188864020c84630034122500180824020c04230640a0200006020200018041),
  (rows ^^^ x5, 0x348a6600188864020c8463006824160030081602180824000c04030840a0200006020200018041),
  (rows ^^^ x4, 0x34926500308866020c84630034122500180425020c04230640a0200006020200018041),
  (rows ^^^ x3, 0x2c9264001884650230886600068242006a252600321125021a0924000602120840a02000018041),
  (rows ^^^ x2, 0x6522a60044a22002058261002190a0000180a0026020260606012300301005000c0204),
  (rows ^^^ x1, 0x329165003211250242a12000219090000180900260202600301005080300a20018080400060103),
  (rows ^^^ x0, 0x6924a6003110a5021908a400682426003010250218082406018061000c040300030082),
  (rows ^^^ leafEdge, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080),
  (x1 &&& leafEdge, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080),
  (x0 &&& x1, 0x6a252600321125021a09240034122500180824020c042306060222000301010040a000),
  (x2 &&& leafEdge, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080),
  (x0 &&& x2, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080),
  (x3 &&& leafEdge, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080),
  (x0 &&& x3, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080),
  (x4 &&& leafEdge, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080),
  (x0 &&& x4, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080),
  (x5 &&& leafEdge, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080),
  (x0 &&& x5, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080),
  (x6 &&& leafEdge, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080),
  (x0 &&& x6, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080),
  (x7 &&& leafEdge, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080),
  (x0 &&& x7, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080),
  (x0 &&& x8, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080),
  (x0 &&& leafOrSeven, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080),
  (x0, 0x6924a6003110a5021908a400682426003010250218082406018061000c040300030082),
  (x1 &&& x2, 0x6a252600321125021a09240034122500180824020c0423060602220040a00000018041),
  (x1 &&& x3, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080),
  (x1 &&& x4, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080),
  (x1 &&& x5, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080),
  (x1 &&& x6, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080),
  (x1 &&& x7, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080),
  (x1 &&& leafOrSeven, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080),
  (x1 &&& x8, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080),
  (x1, 0x329165003211250242a12000219090000180900260202600301005080300a20018080400060103),
  (x1 ||| leafEdge, 0x329165003211250242a12000219090000180900260202600301005080300a20018080400060103),
  (x0 ||| x1, 0x6924a6003110a5021908a400682426003010250218082406018061000c040300030082),
  (x2 &&& x3, 0x34926500188864020c84630034122500180824020c04230640a0200001804100030082),
  (x2 &&& x4, 0x34926500188864020c84630034122500180824020c04230640a0200006020200018041),
  (x2 &&& x5, 0x34926500188864020c84630034122500180824020c04230640a0200006020200018041),
  (x2 &&& x6, 0x34926500188864020c84630034122500180824020c04230640a0200006020200018041),
  (x2 &&& x7, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080),
  (x2 &&& leafOrSeven, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080),
  (x2 &&& x8, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080),
  (x2, 0x6522a60044a22002058261002190a0000180a0026020260606012300301005000c0204),
  (x2 ||| leafEdge, 0x6522a60044a22002058261002190a0000180a0026020260606012300301005000c0204),
  (x0 ||| x2, 0x6924a6003110a5021908a400682426003010250218082406018061000c040300068242),
  (x1 ||| x2, 0x329165003211250242a12000219090000180900260202600301005080300a20018080400060103),
  (x3 &&& x4, 0x6924a6003110a5021908a400188864001808240240a020060180610003008200060103),
  (x3 &&& x5, 0x6924a6003110a5021908a400188864001808240240a02006018061000c040300030082),
  (x3 &&& x6, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080),
  (x3 &&& x7, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080),
  (x3 &&& leafOrSeven, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080),
  (x3 &&& x8, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080),
  (x3, 0x2c9264001884650230886600068242006a252600321125021a0924000602120840a02000018041),
  (x3 ||| leafEdge, 0x2c9264001884650230886600068242006a252600321125021a0924000602120840a02000018041),
  (x0 ||| x3, 0x349265003412250244a220006824260030102502180824060c84630006020200018041),
  (x1 ||| x3, 0x2c9264001884650230886600068242006a252600321125021a0924000602120840a02000058241),
  (x2 ||| x3, 0x6522a60044a22002058261002190a0000180a0026020260606012300301005000c0204),
  (x4 &&& x5, 0x34926500308866020c84630034122500301025020c04230640a0200006020200018041),
  (x4 &&& x6, 0x34926500188864020c84630034122500180824020c04230640a0200006020200018041),
  (x4 &&& x7, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080),
  (x4 &&& leafOrSeven, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080),
  (x4 &&& x8, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080),
  (x4, 0x34926500308866020c84630034122500180425020c04230640a0200006020200018041),
  (x4 ||| leafEdge, 0x34926500308866020c84630034122500180425020c04230640a0200006020200018041),
  (x0 ||| x4, 0x34926500188864020c84630034122500180425020c04230648a4200006020200018041),
  (x1 ||| x4, 0x34926500308866020c84630034122500180425020c04230640a0200006020200098441),
  (x2 ||| x4, 0x34926500308866020c84630034122500180425020c04230640a02000018041000b0482),
  (x3 ||| x4, 0x34926500308866020c84630034122500180425020c04230640a0200006020200018041),
  (x5 &&& x6, 0x6522a60044a220020582610042a120000180a0020300a206060123000c020400180405),
  (x5 &&& x7, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080),
  (x5 &&& leafOrSeven, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080),
  (x5 &&& x8, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080),
  (x5, 0x348a6600188864020c8463006824160030081602180824000c04030840a0200006020200018041),
  (x5 ||| leafEdge, 0x348a6600188864020c8463006824160030081602180824000c04030840a0200006020200018041),
  (x0 ||| x5, 0x54aa20006422260234926500188864001808240250a820060c04230006020200018041),
  (x1 ||| x5, 0x6924a6003110a5021908a400188864001808240240a02006118861000c040300030082),
  (x2 ||| x5, 0x52a92000118861021308a2002190a0000180a002602026063211250018080400060103),
  (x3 ||| x5, 0x69249600310896021908a40001808000188864001808240240a020060180610003008200160903),
  (x4 ||| x5, 0x348a6600188864020c8463001804050030081602180824000c04030840a0200006020200018041),
  (x6 &&& x7, 0x34926500188864020c84630034122500180824020c04230640a0200006020200018041),
  (x6 &&& leafOrSeven, 0x34926500188864020c84630034122500180824020c04230640a0200006020200018041),
  (x6 &&& x8, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080),
  (x6, 0x34926500188864020c84630034122500180824020c04230640a0200006020200018041),
  (x6 ||| leafEdge, 0x34926500188864020c84630034122500180824020c04230640a0200006020200018041),
  (x0 ||| x6, 0x1a050500321105021a0924000601030034122500180824020c0423060602220003010100219080),
  (x1 ||| x6, 0x34926500188864020c84630034122500180824020c04230640a0200006020200219041),
  (x2 ||| x6, 0x6a252600321125021a09240034122500180824020c0423062612220003010100018080),
  (x3 ||| x6, 0x34926500188864022c94630034122500180824022c14230640a0200006020200018041),
  (x4 ||| x6, 0x329165003211250242a120003110a50040a02002018061060300a200060103002c1204),
  (x5 ||| x6, 0x34926500188864020c84630034122500180824020c04230640a0200006020200018041),
  (x7 &&& x8, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080),
  (x7, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080),
  (x8 &&& leafOrSeven, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080),
  (x7 ||| leafEdge, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080),
  (x0 ||| x7, 0x6a252600321125021a09240034122500180824020c042306060222000301010040a000),
  (x1 ||| x7, 0x6a252600321125021a09240034122500180824020c0423060602220043210100018080),
  (x1 ||| leafOrSeven, 0x6a252600321125021a09240034122500180824020c0423060602220043210100018080),
  (x2 ||| x7, 0x6a252600321125021a09240034122500180824020c0423064622220003010100018080),
  (x2 ||| leafOrSeven, 0x6a252600321125021a09240034122500180824020c0423064622220003010100018080),
  (x3 ||| x7, 0x6a252600321125021a09240034122500180824024c2423060602220003010100018080),
  (x3 ||| leafOrSeven, 0x6a252600321125021a09240034122500180824024c2423060602220003010100018080),
  (x4 ||| x7, 0x6a252600321125025a29240034122500582824020c0423060602220003010100018080),
  (x4 ||| leafOrSeven, 0x6a252600321125025a29240034122500582824020c0423060602220003010100018080),
  (x5 ||| x7, 0x6522a60044a220020582610042a120000180a0020300a206060123000c020400582405),
  (x5 ||| leafOrSeven, 0x6522a60044a220020582610042a120000180a0020300a206060123000c020400582405),
  (x6 ||| x7, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080),
  (x6 ||| leafOrSeven, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080),
  (x8, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080),
  (x0 ||| x8, 0x6924a6003110a5021908a400682426003010250218082406018061000c040300030082),
  (x1 ||| x8, 0x6a252600321125021a09240034122500180824020c0423060602220083410100018080),
  (x2 ||| x8, 0x6a252600321125021a09240034122500180824020c0423068642220003010100018080),
  (x3 ||| x8, 0x6a252600321125021a09240034122500180824028c4423060602220003010100018080),
  (x4 ||| x8, 0x6a252600321125029a49240034122500984824020c0423060602220003010100018080),
  (x5 ||| x8, 0x6a252600b25125021a092400b4522500180824020c0423060602220003010100018080),
  (x6 ||| x8, 0xea652600321125021a09240034122500180824020c0423060602220003010100018080),
  (x7 ||| x8, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080),
  (rows, 0x6a252600321125021a09240034122500180824020c0423060602220003010100018080)]

set_option maxRecDepth 32768 in
private lemma bound3 : lower prefix3 target rows 10 := by
  apply certified_split certificates3 [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp

private def certificates2 : List (ℕ × ℕ) := [
  (0, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080),
  (rows ^^^ x8, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080),
  (rows ^^^ x7, 0x329165003211250242a12000219090000180900260202600301005080300a20018080400060103),
  (rows ^^^ x6, 0x329165003211250242a12000508867000180a002301025060300a20018080400060103),
  (rows ^^^ x5, 0x6a252600621127021a09240042a100002994a0004884670268242600180814080300a200060103),
  (rows ^^^ x4, 0x1a8565000c84630206826200160923000300a202180425060180a00040804700300806),
  (rows ^^^ x3, 0x4aa52000488467020b04a20006825200030092020180a000408047080c02240060200600180405),
  (rows ^^^ x2, 0x2592a00044826702642226002190a0000180a0026020260606012300301005000c0204),
  (rows ^^^ leafOrOne, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080),
  (rows ^^^ x1, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080),
  (rows ^^^ x0, 0x5289670062212602321125005088670060202602301025060300a20018080400060103),
  (rows ^^^ leafEdge, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080),
  (x1 &&& leafEdge, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080),
  (x0 &&& x1, 0x2b14a200261123022c122400160923000300a20218042506300826006010070040a000),
  (x2 &&& leafEdge, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080),
  (x0 &&& x2, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080),
  (x3 &&& leafEdge, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080),
  (x0 &&& x3, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080),
  (x4 &&& leafEdge, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080),
  (x0 &&& x4, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080),
  (x5 &&& leafEdge, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080),
  (x0 &&& x5, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080),
  (x6 &&& leafEdge, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080),
  (x0 &&& x6, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080),
  (x7 &&& leafEdge, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080),
  (x0 &&& x7, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080),
  (x0 &&& x8, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080),
  (x0 &&& leafOrOne, 0x2b14a200261123022c122400160923000300a20218042506300826006010070040a000),
  (x0, 0x5289670062212602321125005088670060202602301025060300a20018080400060103),
  (x1 &&& x2, 0x2994a0004884670268242600508867000180a00230102506180824000c040300060202),
  (x1 &&& x3, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080),
  (x1 &&& x4, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080),
  (x1 &&& x5, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080),
  (x1 &&& x6, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080),
  (x1 &&& x7, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080),
  (x1 &&& x8, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080),
  (x1, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080),
  (x2 &&& leafOrOne, 0x2994a0004884670268242600508867000180a00230102506180824000c040300060202),
  (x3 &&& leafOrOne, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080),
  (x4 &&& leafOrOne, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080),
  (x5 &&& leafOrOne, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080),
  (x6 &&& leafOrOne, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080),
  (x7 &&& leafOrOne, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080),
  (x8 &&& leafOrOne, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080),
  (x1 ||| leafEdge, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080),
  (x0 ||| x1, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080),
  (x2 &&& x3, 0x2994a0004884670268242600508867000180a00230102506180824000c040300030082),
  (x2 &&& x4, 0x2994a0004884670268242600508867000180a00230102506180824000c040300030082),
  (x2 &&& x5, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080),
  (x2 &&& x6, 0x2994a0004884670268242600508867000180a00230102506180824000c040300030082),
  (x2 &&& x7, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080),
  (x2 &&& x8, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080),
  (x2, 0x2592a00044826702642226002190a0000180a0026020260606012300301005000c0204),
  (x2 ||| leafEdge, 0x2592a00044826702642226002190a0000180a0026020260606012300301005000c0204),
  (x0 ||| x2, 0x381405002c140300261123022c122400160923000601230218042506300826006010070042a100),
  (x1 ||| x2, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080),
  (x2 ||| leafOrOne, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080),
  (x3 &&& x4, 0x2994a0004884670268242600508867000180a002301025061808240003008200060103),
  (x3 &&& x5, 0x2994a0004884670268242600508867000180a00230102506180824000c040300030082),
  (x3 &&& x6, 0x2994a0004884670268242600508867000180a00230102506180824000c040300030082),
  (x3 &&& x7, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080),
  (x3 &&& x8, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080),
  (x3, 0x4aa52000488467020b04a20006825200030092020180a000408047080c02240060200600180405),
  (x3 ||| leafEdge, 0x4aa52000488467020b04a20006825200030092020180a000408047080c02240060200600180405),
  (x0 ||| x3, 0x5289670062212602321125005088670060202602301025060300a20018080400068143),
  (x1 ||| x3, 0x2994a0004884670268242600508867000180a00230102506180824000d048300030082),
  (x3 ||| leafOrOne, 0x2994a0004884670268242600508867000180a00230102506180824000d048300030082),
  (x2 ||| x3, 0x2592a00044826702642226002190a0000180a0026020260606012300301005000c0204),
  (x4 &&& x5, 0x329165003211250242a12000508867000180a002301025060300a200060103000c0204),
  (x4 &&& x6, 0x329165003211250242a12000508867000180a002301025060300a20018080400060103),
  (x4 &&& x7, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080),
  (x4 &&& x8, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080),
  (x4, 0x1a8565000c84630206826200160923000300a202180425060180a00040804700300806),
  (x4 ||| leafEdge, 0x1a8565000c84630206826200160923000300a202180425060180a00040804700300806),
  (x0 ||| x4, 0x2994a0004884670268242600508867006020260230102506188864000c040300030082),
  (x1 ||| x4, 0x2b14a200261123022d12a400160923000300a202180425063008260060100700018080),
  (x4 ||| leafOrOne, 0x2b14a200261123022d12a400160923000300a202180425063008260060100700018080),
  (x2 ||| x4, 0x2592a00044826702642226002190a0000180a0026020260606012300301005001a0904),
  (x3 ||| x4, 0x4aa52000488467020b04a20006825200030092020180a000408047080c02240060200600180405),
  (x5 &&& x6, 0x2592a000448267026422260042a120000180a0020300a206060123000c020400180405),
  (x5 &&& x7, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080),
  (x5 &&& x8, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080),
  (x5, 0x6a252600621127021a09240042a100002994a0004884670268242600180814080300a200060103),
  (x5 ||| leafEdge, 0x6a252600621127021a09240042a100002994a0004884670268242600180814080300a200060103),
  (x0 ||| x5, 0x329165006211270252a920005088670060202602309065060300a20018080400060103),
  (x1 ||| x5, 0x2b14a200261123022c122400160923000300a2021904a5063008260060100700018080),
  (x5 ||| leafOrOne, 0x2b14a200261123022c122400160923000300a2021904a5063008260060100700018080),
  (x2 ||| x5, 0x52a92000508867021308a2002190a0000180a002602026063211250018080400060103),
  (x3 ||| x5, 0x6a252600621127021a09240042a100002994a0004884670268242600180814080300a200160903),
  (x4 ||| x5, 0x1a8964000c84630206826200160923000300a202180425060180a00040804700300806),
  (x6 &&& x7, 0x329165003211250242a120005088670040806702301025060300a20018080400060103),
  (x6 &&& x8, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080),
  (x6, 0x329165003211250242a12000508867000180a002301025060300a20018080400060103),
  (x6 ||| leafEdge, 0x329165003211250242a12000508867000180a002301025060300a20018080400060103),
  (x0 ||| x6, 0x4a856700488467020b04a200448267000300a202060123060c02240018040500308846),
  (x1 ||| x6, 0x2b14a200261123022c122400160923000300a202180425063108a60060100700018080),
  (x6 ||| leafOrOne, 0x2b14a200261123022c122400160923000300a202180425063108a60060100700018080),
  (x2 ||| x6, 0x2b14a200261123022c1224001609230006012302180425063209260060100700018080),
  (x3 ||| x6, 0x329165003211250242a12000508867000180a002301025060300a20018080400261103),
  (x4 ||| x6, 0x329165003211250242a12000508867000180a002301025060300a200060103002c1204),
  (x5 ||| x6, 0x329165003211250242a12000508867000180a002301025060300a20018080400060103),
  (x7 &&& x8, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080),
  (x7, 0x329165003211250242a12000219090000180900260202600301005080300a20018080400060103),
  (x7 ||| leafEdge, 0x329165003211250242a12000219090000180900260202600301005080300a20018080400060103),
  (x0 ||| x7, 0x329165003211250242a120005088670040a02002301025060300a20018080400060103),
  (x1 ||| x7, 0x2b14a200261123022c122400160923000300a202180425063008260061108700018080),
  (x7 ||| leafOrOne, 0x2b14a200261123022c122400160923000300a202180425063008260061108700018080),
  (x2 ||| x7, 0x5328a2001188a0025289670042a120000180a0024320a2063010250018080400060103),
  (x3 ||| x7, 0x2592a000448267026422260042a120000180a0020300a20646212300301005000c0204),
  (x4 ||| x7, 0x4b24a200462123024c222400068262000300a2020180a0064884670060200600180405),
  (x5 ||| x7, 0x2592900005829002642226000602020042a120000180a0020300a206060123000c020400582405),
  (x6 ||| x7, 0x329165003211250242a12000219090000180900260202600301005080300a20018080400060103),
  (x8, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080),
  (x0 ||| x8, 0x5289670062212602321125005088670060202602301025060300a20018080400060103),
  (x1 ||| x8, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080),
  (x2 ||| x8, 0xab54a200261123022c122400160923008340a202180425063008260060100700018080),
  (x3 ||| x8, 0x2b14a200a65123022c122400964923000300a202180425063008260060100700018080),
  (x4 ||| x8, 0x2b14a20026112302ac522400160923000300a202180425063008260060100700018080),
  (x5 ||| x8, 0x2b14a200261123022c122400160923000300a202984425063008260060100700018080),
  (x6 ||| x8, 0x2b14a200261123022c122400160923000300a20218042506b048260060100700018080),
  (x7 ||| x8, 0x2b14a200261123022c122400160923000300a2021804250630082600e0500700018080),
  (rows, 0x2b14a200261123022c122400160923000300a202180425063008260060100700018080)]

set_option maxRecDepth 32768 in
private lemma bound2 : lower prefix2 target rows 10 := by
  apply certified_split certificates2 [] (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp

private def certificates1 : List (ℕ × ℕ) := [
  (0, 0x548a670044a22002341225000c0204005088670040a0200230102500180804080c04230006020200018041),
  (rows ^^^ x8, 0x548a670044a22002341225000c0204005088670040a0200230102500180804080c04230006020200018041),
  (rows ^^^ x7, 0x348a460054aa100044a22002341225000c0204003088460050a8100040a02002301025001808040a0c04230006020200018041),
  (rows ^^^ x6, 0x548a670044a22002341225000c0204005088670040a0200230102500180804080c04230006020200018041),
  (rows ^^^ x5, 0x4a8567006a2506003289660042a110041a09240006010300348a6600188864020c8463004080470040a0100a06022200018041),
  (rows ^^^ x4, 0x34926500308866020c84630040804700068242005a252500320926026211270034122500180425020c0423060602220e40a02000018041),
  (rows ^^^ x3, 0x52896700320906004281670062210604321125001a0904002c92640018846502308866004080470040a0100a06022200018041),
  (rows ^^^ x2, 0x259261002190a0022611230060100700058261000180a002060123004080470860202600301005000c0204),
  (rows ^^^ x1, 0x5289670050884700118890041308a200300806004281670040804700018090040300a2006020060a3010250018080400060103),
  (rows ^^^ x0, 0x548a670064222602341225000c020400508867006020260230102500180804080c04230006020200018041),
  (rows ^^^ leafEdge, 0x548a670044a22002341225000c0204005088670040a0200230102500180804080c04230006020200018041),
  (x1 &&& leafEdge, 0x548a670044a22002341225000c0204005088670040a0200230102500180804080c04230006020200018041),
  (x0 &&& x1, 0x548a670044a22002341225000c0204005088670040a0200230102500180804080c04230006020200030101),
  (x2 &&& leafEdge, 0x548a670044a22002341225000c0204005088670040a0200230102500180804080c04230006020200018041),
  (x0 &&& x2, 0x548a670044a22002341225000c0204005088670040a0200230102500180804080c04230006020200018041),
  (x3 &&& leafEdge, 0x548a670044a22002341225000c0204005088670040a0200230102500180804080c04230006020200018041),
  (x0 &&& x3, 0x548a670064222602341225000c0204005088670040a0200230102500180804080c04230006020200018041),
  (x4 &&& leafEdge, 0x548a670044a22002341225000c0204005088670040a0200230102500180804080c04230006020200018041),
  (x0 &&& x4, 0x548a670044a22002341225000c0204005088670040a0200230102500180804080c04230006020200018041),
  (x5 &&& leafEdge, 0x548a670044a22002341225000c0204005088670040a0200230102500180804080c04230006020200018041),
  (x0 &&& x5, 0x548a670044a22002341225000c0204005088670040a0200230102500180804080c04230006020200018041),
  (x6 &&& leafEdge, 0x548a670044a22002341225000c0204005088670040a0200230102500180804080c04230006020200018041),
  (x0 &&& x6, 0x548a670044a22002341225000c0204005088670040a0200230102500180804080c04230006020200018041),
  (x7 &&& leafEdge, 0x548a670044a22002341225000c0204005088670040a0200230102500180804080c04230006020200018041),
  (x0 &&& x7, 0x158a61001188a0021609230018080400058261000180a002060123000c0204081804250030080600601007),
  (x0 &&& x8, 0x548a670044a22002341225000c0204005088670040a0200230102500180804080c04230006020200018041),
  (x0, 0x548a670064222602341225000c020400508867006020260230102500180804080c04230006020200018041),
  (x1 &&& x2, 0x548a670044a22002341225000c0204005088670040a0200230102500180804080c04230006020200018041),
  (x1 &&& x3, 0x548a670044a22002341225000c0204005088670040a0200230102500180804080c04230006020200018041),
  (x1 &&& x4, 0x548a670044a22002341225000c0204005088670040a0200230102500180804080c04230006020200018041),
  (x1 &&& x5, 0x548a670044a22002341225000c0204005088670040a0200230102500180804080c04230006020200018041),
  (x1 &&& x6, 0x548a670044a22002341225000c0204005088670040a0200230102500180804080c04230006020200018041),
  (x1 &&& x7, 0x548a670044a22002341225000c0204005088670040a0200230102500180804080c04230006020200018041),
  (x1 &&& x8, 0x548a670044a22002341225000c0204005088670040a0200230102500180804080c04230006020200018041),
  (x1, 0x5289670050884700118890041308a200300806004281670040804700018090040300a2006020060a3010250018080400060103),
  (x0 ||| x1, 0x548a670064222602341225000c020400508867006020260230102500180804080c04230006020200018041),
  (x2 &&& x3, 0x548a670044a22002341225000c0204005088670040a0200230102500180804080c04230001804100030082),
  (x2 &&& x4, 0x548a670044a22002341225000c0204005088670040a0200230102500180804080c04230006020200018041),
  (x2 &&& x5, 0x548a670044a22002341225000c0204005088670040a0200230102500180804080c04230006020200018041),
  (x2 &&& x6, 0x548a670044a22002341225000c0204005088670040a0200230102500180804080c04230006020200018041),
  (x2 &&& x7, 0x548a670044a22002341225000c0204005088670040a0200230102500180804080c04230006020200018041),
  (x2 &&& x8, 0x548a670044a22002341225000c0204005088670040a0200230102500180804080c04230006020200018041),
  (x2, 0x259261002190a0022611230060100700058261000180a002060123004080470860202600301005000c0204),
  (x2 ||| leafEdge, 0x2994a0002c14030026916300219090042c12240030100500168963000c82640218846500018041000180900a30082600408047),
  (x0 ||| x2, 0x548a670064222602341225000c020400508867006020260230102500180804080c04230006824200018041),
  (x1 ||| x2, 0x5289670042a12002321125000301010060904700219090004080470001809004602026003010050c0300a20018080400060103),
  (x3 &&& x4, 0x5289670042a1200232112500030101005088670040a0200230102500018041080300a20018080400060103),
  (x3 &&& x5, 0x5289670042a1200232112500030101005088670040a0200230102500018041080300a20018080400060103),
  (x3 &&& x6, 0x548a670044a22002341225000c0204005088670040a0200230102500180804080c04230006020200018041),
  (x3 &&& x7, 0x5289670042a1200232112500030101005088670040a0200230102500018041080300a20018080400060103),
  (x3 &&& x8, 0x548a670044a22002341225000c0204005088670040a0200230102500180804080c04230006020200018041),
  (x3, 0x52896700320906004281670062210604321125001a0904002c92640018846502308866004080470040a0100a06022200018041),
  (x3 ||| leafEdge, 0x2c926400188465023088660040804700068242006a252600321125021a092400582425000c022402601027060602220e40a02000018041),
  (x0 ||| x3, 0x548a670044a22002341225000c020400508867006020260230102500180804080c84630006020200018041),
  (x1 ||| x3, 0x52896700320906004281670062210604321125001a0904002c92640018846502308866004080470040a0100a06022200058241),
  (x2 ||| x3, 0x259261002190a0022611230060100700058261000180a002060123004080470860202600301005000c0204),
  (x4 &&& x5, 0x5289670042a1200232112500030101005088670040a0200230102500018041080300a200060103000c0204),
  (x4 &&& x6, 0x548a670044a22002341225000c0204005088670040a0200230102500180804080c04230006020200018041),
  (x4 &&& x7, 0x548a670044a22002341225000c0204005088670040a0200230102500180804080c04230006020200018041),
  (x4 &&& x8, 0x548a670044a22002341225000c0204005088670040a0200230102500180804080c04230006020200018041),
  (x4, 0x34926500308866020c84630040804700068242005a252500320926026211270034122500180425020c0423060602220e40a02000018041),
  (x4 ||| leafEdge, 0x2c94630030904500188465000c84430430886600068242005a252500320926026211270034122500180425020c0423060602220e40a02000018041),
  (x0 ||| x4, 0x548a670064222602341225000c824400508867006020260230102500188844080c04230006020200018041),
  (x1 ||| x4, 0x5289670050884700118890041308a200300806004281670040804700018090040300a2006020060a3010250019088400060103),
  (x2 ||| x4, 0x259261002190a0022611230060100700058261000180a002060123004080470860202600301005001a0904),
  (x3 ||| x4, 0x548a670044a22002341225000c020400188465003088460058241500180415026010270640a0200c0c04230006020200018041),
  (x5 &&& x6, 0x259261002190a0022611230060100700058261000180a0020601230040804708602026000c020400180405),
  (x5 &&& x7, 0x259261002190a0022611230060100700058261000180a002060123004080470860202600301005000c0204),
  (x5 &&& x8, 0x548a670044a22002341225000c0204005088670040a0200230102500180804080c04230006020200018041),
  (x5, 0x4a8567006a2506003289660042a110041a09240006010300348a6600188864020c8463004080470040a0100a06022200018041),
  (x5 ||| leafEdge, 0x1a8964000c8463020682620040804700308846006a252600621127021a09240064122700180824020c0423060602220e40a02000018041),
  (x0 ||| x5, 0x548a670064222602349265000c020400508867006020260230906500180804080c04230006020200018041),
  (x1 ||| x5, 0x158a61001188a002160923001808040006824200058290000180a002060123000c02040a1904a50040804700300806),
  (x2 ||| x5, 0x259261002190a0022611230060100700058261000180a002060123004080470860202600321105000c0204),
  (x3 ||| x5, 0x4a8567006a2506003289660042a110041a0924000301010048846700682406003088660040a01004180824000180410c0300a200160903),
  (x4 ||| x5, 0x4aa520001a0505003289660042a110041a09240006010300348a6600188864020c8463004080470040a0100a06022200018041),
  (x6 &&& x7, 0x158a61001188a0021609230018080400058261000180a002060123000c0204081804250040804700300806),
  (x6 &&& x8, 0x548a670044a22002341225000c0204005088670040a0200230102500180804080c04230006020200018041),
  (x6, 0x548a670044a22002341225000c0204005088670040a0200230102500180804080c04230006020200018041),
  (x6 ||| leafEdge, 0x4aa520001a0505003291650042a110041a0924000601030034926500188864020c8463004080470040a0100a06022200018041),
  (x0 ||| x6, 0x158a61001308a2021609230018080400058261000300a202060123000c0204081804250040804700308846),
  (x1 ||| x6, 0x548a670044a22002341225000c0204005088670040a0200230102500180804080c04230006020200219041),
  (x2 ||| x6, 0x548a670044a22002341225000c0204005088670040a0200230102500180804080c04230026120200018041),
  (x3 ||| x6, 0x548a670044a22002341225000c0204005088670040a0200230102500180804082c14230006020200018041),
  (x4 ||| x6, 0x5289670042a1200232112500030101005088670040a0200230102500018041080300a200060103002c1204),
  (x5 ||| x6, 0x548a670044a22002341225000c0204005088670040a0200230102500180804080c04230006020200018041),
  (x7 &&& x8, 0x548a670044a22002341225000c0204005088670040a0200230102500180804080c04230006020200018041),
  (x7, 0x348a460054aa100044a22002341225000c0204003088460050a8100040a02002301025001808040a0c04230006020200018041),
  (x0 ||| x7, 0x548a670044a22002341225000c0204005088670040a0200230102500180804080c04230006020200018041),
  (x1 ||| x7, 0x348a460054aa100044a22002341225000c0204003088460050a8100040a02002301025001808040a0c04230006020200432101),
  (x2 ||| x7, 0x259261002190a0022611230062110700058261000180a002060123004281470860202600301005000c0204),
  (x3 ||| x7, 0x548a670044a22002341225000c0204003088460050a8100040a02002301025001808040a4c24230006020200018041),
  (x4 ||| x7, 0x348a460054aa100044a22002341225004c2204003088460050a8100040a02002301025005828040a0c04230006020200018041),
  (x5 ||| x7, 0x4aa520005a2505003289660042a110041a09240006010300348a6600188864020c8463005088470040a0100a06022200018041),
  (x6 ||| x7, 0x54aa1000742a060044a22002341225000c02040050a810007028060040a02002301025001808040a0c04230006020200018041),
  (x8, 0x548a670044a22002341225000c0204005088670040a0200230102500180804080c04230006020200018041),
  (x0 ||| x8, 0x548a670064222602341225000c020400508867006020260230102500180804080c04230006020200018041),
  (x1 ||| x8, 0x548a670044a22002341225000c0204005088670040a0200230102500180804080c04230006020200834101),
  (x2 ||| x8, 0x548a670044a22002341225000c0204005088670040a0200230102500180804080c04230086420200018041),
  (x3 ||| x8, 0x548a670044a22002341225000c0204005088670040a0200230102500180804088c44230006020200018041),
  (x4 ||| x8, 0x548a670044a22002341225008c4204005088670040a0200230102500984804080c04230006020200018041),
  (x5 ||| x8, 0x548a670044a22002b45225000c0204005088670040a02002b0502500180804080c04230006020200018041),
  (x6 ||| x8, 0x548a670044a22002341225000c0204005088670040a0200230102500180804080c04230006020200018041),
  (x7 ||| x8, 0x158a61001188a0021609230018080400058261000180a002060123000c0204081804250030080600e05007),
  (rows, 0x548a670044a22002341225000c0204005088670040a0200230102500180804080c04230006020200018041)]

set_option maxRecDepth 32768 in
private lemma bound1 : lower prefix1 target rows 11 := by
  apply certified_split certificates1 [leafOrOne, leafOrSeven] (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with h | h <;> subst w
  · exact bound2
  · exact bound3

private def certificates0 : List (ℕ × ℕ) := [
  (0, 0xaad520004a8567026a2526005289670042a12002321125061a09240006010300a8d4200048846702682426005088670040a0200230102506180824000c04031006022200018041),
  (rows ^^^ x8, 0xaad520004a8567026a2526005289670042a12002321125061a09240006010300a8d4200048846702682426005088670040a0200230102506180824000c04031006022200018041),
  (rows ^^^ x7, 0xaad520008a8568026a2526009289680042a12002321125061a09240006010300a8d4200088846802682426009088680040a0200230102506180824000c04031006022200018041),
  (rows ^^^ x6, 0xea5527004aa520028a8568005289670042a12002321125061a09240006010300e854270048a42002888468005088670040a0200230102506180824000c04031006022200018041),
  (rows ^^^ x5, 0xaad520004a8567026a252600e251270042a12002828168061a09240006010300a8d420004884670268242600e050270040a0200280806806180824000c04031006022200018041),
  (rows ^^^ x4, 0xda652500b2492602e2512700328966001a05250242a120068281680006010300d8642500b0482602e0502700308866001804250240a02006808068000c04031006022200018041),
  (rows ^^^ x3, 0xea652600b25125029a492400d86425008c422402e05027068642220080c000006a252600321125021a092400582425000c022402601027060602220040a0001080806800018041),
  (rows ^^^ x2, 0xd6692300cc622402d8642500ac52240086412302b0482606e050270080c00000562923004c222402582425002c12240006012302300826066010270040a0001080806800018041),
  (rows ^^^ x1, 0xaad52000a89468022b14a200a49268002190a002261123062c122400601007008ac52000888468020b04a200848268000180a002060123060c0224004080471060202600180405),
  (rows ^^^ x0, 0xaa9568004a8567026a2526005289670062212602321125061a09240006010300a89468004884670268242600508867006020260230102506180824000c04031006022200018041),
  (x0 &&& x1, 0xaad520004a8567026a2526005289670042a12002321125061a09240006010300a8d4200048846702682426005088670040a0200230102506180824000c04031006022200030101),
  (x0 &&& x2, 0xaa9568004a8567026a2526005289670062212602321125061a09240006010300a8d4200048846702682426005088670040a0200230102506180824000c04031006022200018041),
  (x0 &&& x3, 0xaad520004a8567026a2526005289670042a12002321125061a09240006010300a8d4200048846702682426005088670040a0200230102506180824000c04031006022200018041),
  (x0 &&& x4, 0xaa9568004a8567026a2526005289670042a12002321125061a09240006010300a894680048846702682426005088670040a0200230102506180824000c04031006022200018041),
  (x0 &&& x5, 0xaad520004a8567026a2526005289670042a12002321125061a09240006010300a8d4200048846702682426005088670040a0200230102506180824000c04031006022200018041),
  (x0 &&& x6, 0xaa9568004a8567026a2526005289670042a12002321125061a09240006010300a894680048846702682426005088670040a0200230102506180824000c04031006022200018041),
  (x0 &&& x7, 0xaad520008a8568026a2526009289680082c12002321125061a09240006010300a8d4200088846802682426009088680080c0200230102506180824000c04031006022200018041),
  (x0, 0xaa9568004a8567026a2526005289670062212602321125061a09240006010300a89468004884670268242600508867006020260230102506180824000c04031006022200018041),
  (x1 &&& x2, 0xaad520004a8567026a2526005289670042a12002321125061a09240006010300a8d4200048846702682426005088670040a0200230102506180824000c04031006022200018041),
  (x1 &&& x3, 0xaad520004a8567026a2526005289670042a12002321125061a09240006010300a8d4200048846702682426005088670040a0200230102506180824000c04031006022200018041),
  (x1 &&& x4, 0xaad520004a8567026a2526005289670042a12002321125061a09240006010300a8d4200048846702682426005088670040a0200230102506180824000c04031006022200018041),
  (x1 &&& x5, 0xaad520004a8567026a2526005289670042a12002321125061a09240006010300a8d4200048846702682426005088670040a0200230102506180824000c04031006022200018041),
  (x1 &&& x6, 0xaad520004a8567026a2526005289670042a12002321125061a09240006010300a8d4200048846702682426005088670040a0200230102506180824000c04031006022200018041),
  (x1 &&& x7, 0xaad520004a8567026a2526005289670042a12002321125061a09240006010300a8d4200048846702682426005088670040a0200230102506180824000c04031006022200018041),
  (x1 &&& x8, 0xaad520004a8567026a2526005289670042a12002321125061a09240006010300a8d4200048846702682426005088670040a0200230102506180824000c04031006022200018041),
  (x1, 0xaad52000a89468022b14a200a49268002190a002261123062c122400601007008ac52000888468020b04a200848268000180a002060123060c0224004080471060202600180405),
  (x0 ||| x1, 0xaa9568004a8567026a2526005289670062212602321125061a09240006010300a89468004884670268242600508867006020260230102506180824000c04031006022200018041),
  (x2 &&& x3, 0xaad520004a8567026a2526005289670042a12002321125061a09240003010100a8d4200048846702682426005088670040a020023010250618082400018041100300a2000c0403),
  (x2 &&& x4, 0xda652500b2492602e2512700328966001a05250242a120068281680006010300a8d4200048846702682426005088670040a0200230102506180824000c04031006022200018041),
  (x2 &&& x5, 0xaad520004a8567026a252600e251270042a12002828168061a09240006010300a8d4200048846702682426005088670040a0200230102506180824000c04031006022200018041),
  (x2 &&& x6, 0xea5527004aa520028a8568005289670042a12002321125061a09240006010300a8d4200048846702682426005088670040a0200230102506180824000c04031006022200018041),
  (x2 &&& x7, 0xaad520008a8568026a2526009289680042a12002321125061a09240006010300a8d4200048846702682426005088670040a0200230102506180824000c04031006022200018041),
  (x2 &&& x8, 0xaad520004a8567026a2526005289670042a12002321125061a09240006010300a8d4200048846702682426005088670040a0200230102506180824000c04031006022200018041),
  (x2, 0xd6692300cc622402d8642500ac52240086412302b0482606e050270080c00000562923004c222402582425002c12240006012302300826066010270040a0001080806800018041),
  (x0 ||| x2, 0xaad520004a8567026a2526005289670042a12002321125061a09240006010300a89468004884670268242600508867006020260230102506180824000c04031006826200018041),
  (x1 ||| x2, 0xd6692300cc622402d8642500ac52240086412302b0482606e050270080c00000562923004c222402582425002c12240006012302300826066010270040a0001080806800030101),
  (x3 &&& x4, 0xea652600b25125029a492400d864250098482402e05027068642220080c000006a252600321125021a0924005824250018082402601027060602220040a0001080806800018041),
  (x3 &&& x5, 0xaad520004a8567026a2526005289670042a12002321125061a09240006010300a8d4200048846702682426005088670040a0200230102506180824000c04031006022200018041),
  (x3 &&& x6, 0xaad520004a8567026a2526005289670042a12002321125061a09240006010300a8d4200048846702682426005088670040a0200230102506180824000c04031006022200018041),
  (x3 &&& x7, 0xaad520004a8567026a2526005289670042a12002321125061a09240006010300a8d4200048846702682426005088670040a0200230102506180824000c04031006022200018041),
  (x3 &&& x8, 0xaad520004a8567026a2526005289670042a12002321125061a09240006010300a8d4200048846702682426005088670040a0200230102506180824000c04031006022200018041),
  (x3, 0xea652600b25125029a492400d86425008c422402e05027068642220080c000006a252600321125021a092400582425000c022402601027060602220040a0001080806800018041),
  (x0 ||| x3, 0xaa9568004a8567026a2526005289670062212602321125061a09240006814300a89468004884670268242600508867006020260230102506180824000c84431006022200018041),
  (x1 ||| x3, 0xea652600b25125029a492400d86425008c422402e05027068642220080c000006a252600321125021a092400582425000c022402601027060602220040a0001080806800058241),
  (x2 ||| x3, 0xaad520004a8567026a2526005289670042a12002321125061a092400060103002c9264001884650230886600582425000c0224026010270640a020008080481006022200018041),
  (x4 &&& x5, 0xaad52000299461022b14a200259261002190a002261123062c122400601007008ac52000098461020b04a200058261000180a002060123060c0224004080471060202600301005),
  (x4 &&& x6, 0xea5527004aa520028a8568005289670042a12002321125061a09240006010300e854270048a42002888468005088670040a0200230102506180824000c04031006022200018041),
  (x4 &&& x7, 0xaad520008a8568026a2526005289670042a12002321125061a09240006010300a8d4200088846802682426005088670040a0200230102506180824000c04031006022200018041),
  (x4 &&& x8, 0xaad520004a8567026a2526005289670042a12002321125061a09240006010300a8d4200048846702682426005088670040a0200230102506180824000c04031006022200018041),
  (x4, 0xda652500b2492602e2512700328966001a05250242a120068281680006010300d8642500b0482602e0502700308866001804250240a02006808068000c04031006022200018041),
  (x0 ||| x4, 0xaad520004a8567026a2526005289670062212602321125061a89640006010300a8d420004884670268242600508867006020260230102506188864000c04031006022200018041),
  (x1 ||| x4, 0xda652500b2492602e2512700328966001a05250242a120068281680006010300d8642500b0482602e0502700308866001804250240a02006808068000c04031006022200098441),
  (x2 ||| x4, 0xaad520004a8567026a2526005289670042a12002321125061a09240003010100d8642500b0482602e0502700308866001804250240a0200680806800018041100b04a200060103),
  (x3 ||| x4, 0xda652500b2492602e2512700328966001a05250242a12006828168000e050300d8642500b0482602e0502700308866001804250240a02006808068000c04031006022200018041),
  (x5 &&& x6, 0xaad520004a8567026a252600e251270042a12002828168061a09240006010300a8d420004884670268242600e050270040a0200280806806180824000c04031006022200018041),
  (x5 &&& x7, 0xaad520004a8567026a2526009289680042a12002321125061a09240006010300a8d4200048846702682426009088680040a0200230102506180824000c04031006022200018041),
  (x5 &&& x8, 0xaad520004a8567026a2526005289670042a12002321125061a09240006010300a8d4200048846702682426005088670040a0200230102506180824000c04031006022200018041),
  (x5, 0xaad520004a8567026a252600e251270042a12002828168061a09240006010300a8d420004884670268242600e050270040a0200280806806180824000c04031006022200018041),
  (x0 ||| x5, 0xea652600e25127029a492400e4522700984824028c4423068642220090c800006a252600621127021a09240064122700180824020c0423060602220050a8001080806800018041),
  (x1 ||| x5, 0xaad520004a8567026a252600e251270042a12002828168061a09240006010300a8d420004884670268242600e050270040a0200280806806180824000c04031006022200118841),
  (x2 ||| x5, 0xaad520004a8567026a2526005289670042a12002321125061a09240006010300a8d420004884670268242600e050270040a0200280806806180824000c040310160a2200018041),
  (x3 ||| x5, 0xaad520004a8567026a252600e251270042a12002828168061a09240003010100a8d420004884670268242600e050270040a020028080680618082400018041100300a200160903),
  (x4 ||| x5, 0xaad520004a8567026a252600e251270042a12002828168061a09240006010300a8d420004884670268242600e050270040a0200280806806180824000c04031006022200018041),
  (x6 &&& x7, 0xaad52000299461022b14a200259261002190a002261123062c122400301005008ac52000098461020b04a200058261000180a002060123060c0224001804051030082600408047),
  (x6 &&& x8, 0xaad520004a8567026a2526005289670042a12002321125061a09240006010300a8d4200048846702682426005088670040a0200230102506180824000c04031006022200018041),
  (x6, 0xea5527004aa520028a8568005289670042a12002321125061a09240006010300e854270048a42002888468005088670040a0200230102506180824000c04031006022200018041),
  (x0 ||| x6, 0xaad52000299461022b14a200259261002190a002261123062c122400301005008a856800098461020b04a2000582610001806102060123060c0224001804051030886600408047),
  (x1 ||| x6, 0xea5527004aa520028a8568005289670042a12002321125061a09240006010300e854270048a42002888468005088670040a0200230102506180824000c04031006022200219041),
  (x2 ||| x6, 0xaad520004a8567026a2526005289670042a12002321125061a09240006010300e854270048a42002888468005088670040a0200230102506180824000c04031026122200018041),
  (x3 ||| x6, 0xea5527004aa520028a8568005289670042a12002321125061a09240026110300e854270048a42002888468005088670040a0200230102506180824002c14031006022200018041),
  (x4 ||| x6, 0xaad52000299461022b14a200259261002190a002261123062c122400601007008d44a300864222028341210006826200030121020180a006808068004080471068242600180405),
  (x5 ||| x6, 0xea5527004aa520028a8568005289670042a12002321125061a09240006010300e854270048a42002888468005088670040a0200230102506180824000c04031006022200018041),
  (x7 &&& x8, 0xaad520004a8567026a2526005289670042a12002321125061a09240006010300a8d4200048846702682426005088670040a0200230102506180824000c04031006022200018041),
  (x7, 0xaad520008a8568026a2526009289680042a12002321125061a09240006010300a8d4200088846802682426009088680040a0200230102506180824000c04031006022200018041),
  (x0 ||| x7, 0xaa9568004a8567026a2526005289670042a12002321125061a09240006010300a894680048846702682426005088670040a0200230102506180824000c04031006022200018041),
  (x1 ||| x7, 0xaad520008a8568026a2526009289680042a12002321125061a09240006010300a8d4200088846802682426009088680040a0200230102506180824000c04031006022200432101),
  (x2 ||| x7, 0xaad520004a8567026a2526005289670042a12002321125061a09240006010300a8d4200088846802682426009088680040a0200230102506180824000c04031046222200018041),
  (x3 ||| x7, 0xaad520008a8568026a2526009289680042a12002321125061a09240046210300a8d4200088846802682426009088680040a0200230102506180824004c24031006022200018041),
  (x4 ||| x7, 0xaad520004a8567026a2526009289680042a12002321125065a29240006010300a8d4200048846702682426009088680040a0200230102506582824000c04031006022200018041),
  (x5 ||| x7, 0xb54aa6009948a4028d44a3009a4924008c442302864222068341210080c00000350aa6001908a4020d04a3001a0924000c04230206022206030121000180801080806800508847),
  (x6 ||| x7, 0xaad520008a8568026a2526009289680042a12002321125061a09240006010300a8d4200088846802682426009088680040a0200230102506180824000c04031006022200018041),
  (x8, 0xaad520004a8567026a2526005289670042a12002321125061a09240006010300a8d4200048846702682426005088670040a0200230102506180824000c04031006022200018041),
  (x0 ||| x8, 0xaad520004a8567026a2526005289670082c12002321125061a09240006010300a8d4200048846702682426005088670080c0200230102506180824000c04031006022200018041),
  (x1 ||| x8, 0xaad520004a8567026a2526005289670042a12002321125061a09240006010300a8d4200048846702682426005088670040a0200230102506180824000c04031006022200834101),
  (x2 ||| x8, 0xaad520004a8567026a2526005289670042a12002321125061a09240006010300a8d4200048846702682426005088670040a0200230102506180824000c04031086422200018041),
  (x3 ||| x8, 0xaad520004a8567026a2526005289670042a12002321125061a09240086410300a8d4200048846702682426005088670040a0200230102506180824008c44031006022200018041),
  (x4 ||| x8, 0xaad520004a8567026a2526005289670042a12002321125069a49240006010300a8d4200048846702682426005088670040a0200230102506984824000c04031006022200018041),
  (x5 ||| x8, 0xaad520004a8567026a2526005289670042a12002b25125061a09240006010300a8d4200048846702682426005088670040a02002b0502506180824000c04031006022200018041),
  (x6 ||| x8, 0xaad520004a856702ea6526005289670042a12002321125061a09240006010300a8d4200048846702e86426005088670040a0200230102506180824000c04031006022200018041),
  (x7 ||| x8, 0xaad52000299461022b14a200259261002190a002261123062c122400301005008ac52000098461020b04a200058261000180a002060123060c0224001804051030082600e05007),
  (rows, 0xaad520004a8567026a2526005289670042a12002321125061a09240006010300a8d4200048846702682426005088670040a0200230102506180824000c04031006022200018041)]

set_option maxRecDepth 32768 in
private lemma bound0 : lower initial target rows 12 := by
  apply certified_split certificates0 [leafEdge] (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  subst w
  exact bound1

end PEqualNP.Outside.Meta525

open PEqualNP.Outside.Meta525 in
theorem PEqualNP.Outside.L_meta_525 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 0 && x 7) || (x 0 && x 8)) s → 12 ≤ s := by
  intro s hc
  apply bound0 _ s _ hc
  intro r _
  simp only [target, Nat.testBit_or, Nat.testBit_and]
  rfl
