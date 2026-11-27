import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite

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

private def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m


private def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩


private def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩


private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]


private def WireRel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

private theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : WireRel n m π W W') : WireRel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq] <;> rfl
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

private theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, WireRel n m π W W' →
      WireRel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

private theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    WireRel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]


private theorem relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasCircuitSize n h s) : HasCircuitSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨relabel n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [relabel, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    have := (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output
    exact this

private lemma rooted_leaf_cases {n : ℕ} (G : SimpleGraph (Fin n)) (hAcyc : G.IsAcyclic)
    (r : Fin n) (hEdge : ∃ u v : Fin n, G.Adj u v ∧ u ≠ r ∧ v ≠ r) :
    ∃ ℓ p : Fin n, ℓ ≠ r ∧ p ≠ r ∧ G.Adj ℓ p ∧ (∀ w, G.Adj ℓ w → w = p) ∧
      ((∃ ℓ' : Fin n, ℓ' ≠ ℓ ∧ ℓ' ≠ r ∧ G.Adj ℓ' p ∧ ∀ w, G.Adj ℓ' w → w = p) ∨
       (∀ w, G.Adj p w → w = ℓ) ∨
       (∃ q : Fin n, q ≠ ℓ ∧ G.Adj p q ∧ ∀ w, G.Adj p w → w = ℓ ∨ w = q)) := by
  classical
  have hlen_lt : ∀ {u v : Fin n} (P : G.Walk u v), P.IsPath → P.length < n := by
    intro u v P hP
    have h1 : P.support.length ≤ Fintype.card (Fin n) := hP.support_nodup.length_le_card
    rw [P.length_support, Fintype.card_fin] at h1
    omega
  obtain ⟨u, v, huv, hur, hvr⟩ := hEdge
  have seed : ∃ z u₀ : Fin n, ∃ P : G.Walk u₀ z, P.IsPath ∧
      1 ≤ P.length ∧ (z = r → 2 ≤ P.length) ∧ (z ≠ r → ¬ G.Reachable r z) := by
    by_cases hreach : G.Reachable u r
    · obtain ⟨R, hR⟩ := hreach.exists_isPath
      by_cases hlong : 2 ≤ R.length
      · exact ⟨r, u, R, hR, by omega, fun _ => hlong, by simp⟩
      · cases R with
        | nil => exact False.elim (hur rfl)
        | cons h R =>
          cases R with
          | nil =>
            refine ⟨_, v, .cons huv.symm (.cons h .nil), ?_, by simp, by simp, by simp⟩
            exact SimpleGraph.Walk.IsPath.cons hR (by simp [huv.ne.symm, hvr])
          | cons h' R' => simp at hlong
    · exact ⟨u, v, .cons huv.symm .nil,
        SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil (by simp [huv.ne.symm]),
        by simp, fun he => False.elim (hur he), fun _ hr => hreach hr.symm⟩
  obtain ⟨z, u₀, R, hR, hRpos, hRroot, hRaway⟩ := seed
  set S : Finset ℕ := (Finset.range n).filter
    (fun k => ∃ u : Fin n, ∃ P : G.Walk u z, P.IsPath ∧ P.length = k)
  have hmem : ∀ {u : Fin n} (P : G.Walk u z), P.IsPath → P.length ∈ S := by
    intro u P hP
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (hlen_lt P hP), u, P, hP, rfl⟩
  have hS_ne : S.Nonempty := ⟨_, hmem R hR⟩
  set m := S.max' hS_ne
  have hm_mem : m ∈ S := Finset.max'_mem S hS_ne
  have hm_max : ∀ {u : Fin n} (P : G.Walk u z), P.IsPath → P.length ≤ m :=
    fun P hP => Finset.le_max' S _ (hmem P hP)
  have hRm := hm_max R hR
  obtain ⟨_, ℓ, P, hP, hPlen⟩ := Finset.mem_filter.1 hm_mem
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
    have away {w : Fin n} (hw : G.Reachable w z) (hn : w ∉ Q.support) : w ≠ r := by
      intro he
      by_cases hz : z = r
      · exact hn (by simpa [he, hz] using Q.end_mem_support)
      · exact hRaway hz (he ▸ hw)
    have hpr : p ≠ r := by
      intro he
      by_cases hz : z = r
      · have h2 := hRroot hz
        have hn : Q.Nil := hQ.nil_iff_eq.2 (he.trans hz.symm)
        have h0 : Q.length = 0 := by cases hn; rfl
        simp [h0] at hPlen
        omega
      · exact hRaway hz (he ▸ Q.reachable)
    refine ⟨ℓ, p, away (hlp.reachable.trans Q.reachable) hℓ_not_Q, hpr, hlp, hℓ_leaf, ?_⟩
    cases Q with
    | nil =>
      by_cases hother : ∃ ℓ' : Fin n, ℓ' ≠ ℓ ∧ G.Adj z ℓ'
      · obtain ⟨ℓ', hne, hadj⟩ := hother
        have hnot : ℓ' ∉ (SimpleGraph.Walk.nil : G.Walk z z).support := by
          simp [hadj.ne.symm]
        exact Or.inl ⟨ℓ', hne, away hadj.symm.reachable hnot, hadj.symm, hnotQ_leaf ℓ' hadj hnot⟩
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
        exact Or.inl ⟨ℓ', hne1, away (hadj.symm.reachable.trans (SimpleGraph.Walk.cons hpq Q').reachable) hnot, hadj.symm, hnotQ_leaf ℓ' hadj hnot⟩
      · refine Or.inr (Or.inr ⟨q, hq_ne_ℓ, hpq, ?_⟩)
        intro w hpw
        by_contra hnot
        exact hother ⟨w, fun h => hnot (Or.inl h), fun h => hnot (Or.inr h), hpw⟩


private def IsVC {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  ∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S

private def deleteVertexEdges {n : ℕ} (G : SimpleGraph (Fin n)) (p : Fin n) :
    SimpleGraph (Fin n) where
  Adj u v := G.Adj u v ∧ u ≠ p ∧ v ≠ p
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun v h => G.loopless.irrefl v h.1⟩

private lemma deleteVertexEdges_le {n : ℕ} (G : SimpleGraph (Fin n)) (p : Fin n) :
    deleteVertexEdges G p ≤ G :=
  fun _ _ h => h.1

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

private lemma cover_edge {n : ℕ} (G : SimpleGraph (Fin n)) (ℓ p : Fin n)
    (S₁ : Finset (Fin n)) (hS₁ : IsVC (G.deleteEdges {s(ℓ,p)}) S₁) :
    IsVC G (insert p S₁) := by
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

private lemma cover_parent {n : ℕ} (G : SimpleGraph (Fin n)) (p : Fin n)
    (S : Finset (Fin n)) (hc : IsVC (deleteVertexEdges G p) S) : IsVC G (insert p S) := by
  intro u v huv
  by_cases hu : u = p
  · simp [hu]
  by_cases hv : v = p
  · simp [hv]
  exact (hc u v ⟨huv, hu,hv⟩).imp Finset.mem_insert_of_mem Finset.mem_insert_of_mem

private lemma cover_sibling {n : ℕ} (G : SimpleGraph (Fin n)) (r ℓ ℓ' p : Fin n)
    (hℓ'ne : ℓ' ≠ ℓ) (hℓ'p : G.Adj ℓ' p) (hℓ'leaf : ∀ w, G.Adj ℓ' w → w = p)
    (hpr : p ≠ r) (hℓ'r : ℓ' ≠ r)
    (S₁ : Finset (Fin n)) (hS₁ : IsVC (G.deleteEdges {s(ℓ,p)}) S₁) :
    ∃ S, IsVC G S ∧ (r ∈ S ↔ r ∈ S₁) ∧ S.card = S₁.card := by
  by_cases hp : p ∈ S₁
  · have hcov : IsVC G S₁ := by
      intro u v huv
      by_cases hmem : s(u, v) = s(ℓ, p)
      · rw [Sym2.eq_iff] at hmem
        rcases hmem with ⟨_, hvp⟩ | ⟨hup, _⟩
        · exact Or.inr (hvp ▸ hp)
        · exact Or.inl (hup ▸ hp)
      · exact hS₁ u v (SimpleGraph.deleteEdges_adj.2 ⟨huv, by simpa using hmem⟩)
    exact ⟨S₁, hcov, Iff.rfl, rfl⟩
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
    exact ⟨S', hcov, by simp [S', Ne.symm hpr, Ne.symm hℓ'r], hcard⟩


private noncomputable def edges {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ := by
  classical exact G.edgeFinset.card

private def budget {n : ℕ} (G : SimpleGraph (Fin n)) (r : Fin n) (B : Bool → ℕ → Prop)
    (s : ℕ) : Prop :=
  ∃ S : Finset (Fin n), IsVC G S ∧ ∃ b : ℕ,
    B (decide (r ∈ S)) b ∧ edges G + S.card + b ≤ s + 2

private lemma budget_lift {n : ℕ} {G H : SimpleGraph (Fin n)} {r : Fin n}
    {B : Bool → ℕ → Prop} {s t k : ℕ} (ih : budget H r B t)
    (cover : ∀ S, IsVC H S → ∃ T, IsVC G T ∧ (r ∈ T ↔ r ∈ S) ∧ T.card ≤ S.card + k)
    (hs : edges G + k + t ≤ edges H + s) : budget G r B s := by
  obtain ⟨S, hS, b, hb, hle⟩ := ih
  obtain ⟨T, hT, hr, hc⟩ := cover S hS
  exact ⟨T, hT, b, by simpa only [propext hr] using hb, by omega⟩

private lemma rooted_induction {n : ℕ} (r : Fin n)
    (C : SimpleGraph (Fin n) → ℕ → Prop) (B : Bool → ℕ → Prop)
    (star : ∀ G t, C G t → (∀ u v, G.Adj u v → u = r ∨ v = r) → budget G r B t)
    (cut : ∀ G t ℓ p, C G t → ℓ ≠ r → p ≠ r → G.Adj ℓ p →
      (∀ w, G.Adj ℓ w → w = p) →
      (1 ≤ t ∧ C (G.deleteEdges {s(ℓ,p)}) (t-1)) ∧
      (2 ≤ t ∧ C (deleteVertexEdges G p) (t-2)) ∧
      ((2 ≤ t ∧ C (G.deleteEdges {s(ℓ,p)}) (t-2)) ∨
       (3 ≤ t ∧ C (deleteVertexEdges G p) (t-3)))) :
    ∀ t G, G.IsAcyclic → C G t → budget G r B t := by
  classical
  intro t
  induction t using Nat.strong_induction_on with
  | ind t ih =>
    intro G hG hc
    by_cases ho : ∃ u v, G.Adj u v ∧ u ≠ r ∧ v ≠ r
    · obtain ⟨ℓ,p,hlr,hpr,hlp,hl,hsib | hone | htwo⟩ := rooted_leaf_cases G hG r ho
      all_goals
        have cuts := cut G t ℓ p hc hlr hpr hlp hl
        have e0 : edges (G.deleteEdges {s(ℓ,p)}) + 1 = edges G := by
          unfold edges
          convert! edgeFinset_card_deleteEdge G ℓ p hlp using 1 <;> congr!
        have a0 := hG.anti (SimpleGraph.deleteEdges_le _ : G.deleteEdges {s(ℓ,p)} ≤ G)
        have a1 := hG.anti (deleteVertexEdges_le G p)
      · obtain ⟨ℓ', hne, hr', ha, hleaf⟩ := hsib
        obtain ⟨ht, hcut⟩ := cuts.1
        apply budget_lift (k := 0) (ih (t-1) (by omega) _ a0 hcut) _ (by omega)
        intro S hS
        obtain ⟨T,hT,hmem,hcard⟩ := cover_sibling G r ℓ ℓ' p hne ha hleaf hpr hr' S hS
        exact ⟨T,hT,hmem,by omega⟩
      · obtain ⟨ht, hcut⟩ := cuts.2.1
        have e1 : edges (deleteVertexEdges G p) + 1 = edges G := by
          unfold edges
          convert! edgeFinset_card_deleteVertex_deg1 G ℓ p hlp hone using 1 <;> congr!
        apply budget_lift (k := 1) (ih (t-2) (by omega) _ a1 hcut) _ (by omega)
        intro S hS
        exact ⟨insert p S, cover_parent G p S hS, by simp [Ne.symm hpr], Finset.card_insert_le p S⟩
      · obtain ⟨z,hz,hpz,hd⟩ := htwo
        rcases cuts.2.2 with ⟨ht,hcut⟩ | ⟨ht,hcut⟩
        · apply budget_lift (k := 1) (ih (t-2) (by omega) _ a0 hcut) _ (by omega)
          intro S hS
          exact ⟨insert p S, cover_edge G ℓ p S hS, by simp [Ne.symm hpr], Finset.card_insert_le p S⟩
        · have e1 : edges (deleteVertexEdges G p) + 2 = edges G := by
            unfold edges
            convert! edgeFinset_card_deleteVertex_deg2 G ℓ p z hlp hpz hz hd using 1 <;> congr!
          apply budget_lift (k := 1) (ih (t-3) (by omega) _ a1 hcut) _ (by omega)
          intro S hS
          exact ⟨insert p S, cover_parent G p S hS, by simp [Ne.symm hpr], Finset.card_insert_le p S⟩
    · apply star G t hc
      intro u v huv
      by_contra! h
      exact ho ⟨u,v,huv,h⟩

private noncomputable def active {d m : ℕ} (G : SimpleGraph (Fin d))
    (e : Fin d ↪ Fin m) (H : (Fin m → Bool) → Bool) (x : Fin m → Bool) : Bool := by
  classical exact H x || decide (∃ u v, G.Adj u v ∧ x (e u) = true ∧ x (e v) = true)

private lemma active_leaf_false {d m : ℕ} (G : SimpleGraph (Fin d))
    (e : Fin d ↪ Fin m) (H : (Fin m → Bool) → Bool) (ℓ p : Fin d)
     (hleaf : ∀ w, G.Adj ℓ w → w = p)
    (hH : ∀ x, H (Function.update x (e ℓ) false) = H x) (x : Fin m → Bool) :
    active G e H (Function.update x (e ℓ) false) = active (G.deleteEdges {s(ℓ,p)}) e H x := by
  classical
  rw [active, active, hH]
  congr 1
  apply decide_eq_decide.2
  constructor
  · rintro ⟨u, v, huv, hux, hvx⟩
    have huℓ : u ≠ ℓ := by intro h; subst h; simp at hux
    have hvℓ : v ≠ ℓ := by intro h; subst h; simp at hvx
    have hne1 : e u ≠ e ℓ := fun h => huℓ (e.injective h)
    have hne2 : e v ≠ e ℓ := fun h => hvℓ (e.injective h)
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
    have hne1 : e u ≠ e ℓ := fun h => huℓ (e.injective h)
    have hne2 : e v ≠ e ℓ := fun h => hvℓ (e.injective h)
    exact ⟨u, v, huv, by rw [Function.update_of_ne hne1]; exact hux,
      by rw [Function.update_of_ne hne2]; exact hvx⟩


private lemma active_leaf_true {d m : ℕ} (G : SimpleGraph (Fin d))
    (e : Fin d ↪ Fin m) (H : (Fin m → Bool) → Bool) (ℓ p : Fin d)
    (hlp : G.Adj ℓ p) (hleaf : ∀ w, G.Adj ℓ w → w = p)
    (hH : ∀ x, H (Function.update x (e ℓ) true) = H x) (x : Fin m → Bool) :
    active G e H (Function.update x (e ℓ) true) = (active (deleteVertexEdges G p) e H x || x (e p)) := by
  classical
  rw [active, active, hH, Bool.or_assoc, Bool.or_comm (decide _) (x (e p))]
  congr 1
  apply Bool.eq_iff_iff.2
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  have hpneℓ : e p ≠ e ℓ :=
    fun h => hlp.ne.symm (e.injective h)
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
        have hne1 : e u ≠ e ℓ := fun h => huℓ (e.injective h)
        have hne2 : e v ≠ e ℓ := fun h => hvℓ (e.injective h)
        rw [Function.update_of_ne hne1] at hux
        rw [Function.update_of_ne hne2] at hvx
        exact ⟨u, v, ⟨huv, hup, hvp⟩, hux, hvx⟩
  · rintro (hpx | ⟨u, v, ⟨huv, hup, hvp⟩, hux, hvx⟩)
    · exact ⟨ℓ, p, hlp, by simp, by rw [Function.update_of_ne hpneℓ]; exact hpx⟩
    · have huℓ : u ≠ ℓ := fun h => hvp (hleaf v (h ▸ huv))
      have hvℓ : v ≠ ℓ := fun h => hup (hleaf u (h ▸ huv.symm))
      have hne1 : e u ≠ e ℓ := fun h => huℓ (e.injective h)
      have hne2 : e v ≠ e ℓ := fun h => hvℓ (e.injective h)
      exact ⟨u, v, huv, by rw [Function.update_of_ne hne1]; exact hux,
        by rw [Function.update_of_ne hne2]; exact hvx⟩



private lemma active_of_single {d m : ℕ} (G : SimpleGraph (Fin d)) (e : Fin d ↪ Fin m)
    (H : (Fin m → Bool) → Bool) (x : Fin m → Bool) (p : Fin d)
    (h : ∀ i, x (e i) = true → i = p) : active G e H x = H x := by
  classical
  have hno : ¬ ∃ u v, G.Adj u v ∧ x (e u) = true ∧ x (e v) = true := by
    rintro ⟨u,v, huv, hu, hv⟩
    exact huv.ne ((h u hu).trans (h v hv).symm)
  simp [active,hno]

private lemma active_dep {d m : ℕ} (G : SimpleGraph (Fin d)) (e : Fin d ↪ Fin m)
    (H : (Fin m → Bool) → Bool) (ℓ p : Fin d) (ha : G.Adj ℓ p)
    (hfalse : ∀ z : Fin d → Bool, ∃ x, (∀ i, x (e i) = z i) ∧ H x = false)
    (hH : ∀ x b, H (Function.update x (e ℓ) b) = H x) :
    ∃ x, active G e H (Function.update x (e ℓ) false) ≠
         active G e H (Function.update x (e ℓ) true) := by
  obtain ⟨x,hx,hf⟩ := hfalse (fun i => decide (i=p))
  have h0 : ∀ i, Function.update x (e ℓ) false (e i) = true → i = p := by
    intro i ht
    by_cases hi : i = ℓ
    · subst i; simp at ht
    · simpa [Function.update_of_ne (e.injective.ne hi), hx] using ht
  have h1 : ∃ u v, G.Adj u v ∧ Function.update x (e ℓ) true (e u) = true ∧
      Function.update x (e ℓ) true (e v) = true :=
    ⟨ℓ,p,ha,by simp,by simp [Function.update_of_ne (e.injective.ne ha.ne.symm),hx]⟩
  refine ⟨x, ?_⟩
  rw [active_of_single G e H _ p h0, hH, hf]
  simp [active,h1]

private lemma active_nc {d m : ℕ} (G : SimpleGraph (Fin d)) (e : Fin d ↪ Fin m)
    (H : (Fin m → Bool) → Bool) (r : Fin d)
    (hfalse : ∀ z : Fin d → Bool, ∃ x, (∀ i, x (e i) = z i) ∧ H x = false)
    (htrue : ∃ x, H x = true) :
    ∃ x y, active G e H x = false ∧ active G e H y = true ∧ ∀ i, x (e i) = false := by
  obtain ⟨x,hx,hf⟩ := hfalse (fun _ => false)
  obtain ⟨y,hy⟩ := htrue
  refine ⟨x,y,?_,by simp [active,hy],hx⟩
  rw [active_of_single G e H _ r (by simp [hx]),hf]

private lemma active_isolated {d m : ℕ} (G : SimpleGraph (Fin d)) (e : Fin d ↪ Fin m)
    (H : (Fin m → Bool) → Bool) (p : Fin d) (hH : ∀ x b, H (Function.update x (e p) b) = H x)
    (x : Fin m → Bool) (b : Bool) :
    active (deleteVertexEdges G p) e H (Function.update x (e p) b) =
      active (deleteVertexEdges G p) e H x := by
  classical
  rw [active,active,hH]
  congr 1
  apply decide_eq_decide.2
  constructor <;> rintro ⟨u,v,ha,hu,hv⟩
  · exact ⟨u,v,ha,by simpa [Function.update_of_ne (e.injective.ne ha.2.1)] using hu,
      by simpa [Function.update_of_ne (e.injective.ne ha.2.2)] using hv⟩
  · exact ⟨u,v,ha,by simpa [Function.update_of_ne (e.injective.ne ha.2.1)] using hu,
      by simpa [Function.update_of_ne (e.injective.ne ha.2.2)] using hv⟩

private lemma active_cuts {d m : ℕ} (r : Fin d) (e : Fin d ↪ Fin m)
    (H : (Fin m → Bool) → Bool)
    (hfalse : ∀ z : Fin d → Bool, ∃ x, (∀ i, x (e i) = z i) ∧ H x = false)
    (htrue : ∃ x, H x = true)
    (hi : ∀ i, i ≠ r → ∀ x b, H (Function.update x (e i) b) = H x)
    (G : SimpleGraph (Fin d)) (t : ℕ) (ℓ p : Fin d)
    (hc : HasCircuitSize m (active G e H) t) (hlr : ℓ ≠ r) (hpr : p ≠ r)
    (ha : G.Adj ℓ p) (hl : ∀ w, G.Adj ℓ w → w = p) :
      (1 ≤ t ∧ HasCircuitSize m (active (G.deleteEdges {s(ℓ,p)}) e H) (t-1)) ∧
      (2 ≤ t ∧ HasCircuitSize m (active (deleteVertexEdges G p) e H) (t-2)) ∧
      ((2 ≤ t ∧ HasCircuitSize m (active (G.deleteEdges {s(ℓ,p)}) e H) (t-2)) ∨
       (3 ≤ t ∧ HasCircuitSize m (active (deleteVertexEdges G p) e H) (t-3))) := by
  classical
  let F := active G e H
  let F₀ := active (G.deleteEdges {s(ℓ,p)}) e H
  let D := active (deleteVertexEdges G p) e H
  let F₁ := fun x => D x || x (e p)
  have eq0 : (fun x => F (Function.update x (e ℓ) false)) = F₀ :=
    funext (active_leaf_false G e H ℓ p hl (fun x => hi ℓ hlr x false))
  have eq1 : (fun x => F (Function.update x (e ℓ) true)) = F₁ :=
    funext (active_leaf_true G e H ℓ p ha hl (fun x => hi ℓ hlr x true))
  obtain ⟨x₀,y₀,hx₀,hy₀,_⟩ := active_nc (G.deleteEdges {s(ℓ,p)}) e H r hfalse htrue
  obtain ⟨x,y,hx,hy,hzeros⟩ := active_nc (deleteVertexEdges G p) e H r hfalse htrue
  have nc0 : ∃ x y, F (Function.update x (e ℓ) false) ≠ F (Function.update y (e ℓ) false) :=
    ⟨x₀,y₀,by rw [congrFun eq0 x₀,congrFun eq0 y₀]; simpa [F₀,hx₀,hy₀]⟩
  have nc1 : ∃ x y, F (Function.update x (e ℓ) true) ≠ F (Function.update y (e ℓ) true) :=
    ⟨x,y,by rw [congrFun eq1 x,congrFun eq1 y]; simp [F₁,D,hx,hy,hzeros]⟩
  have peq : (fun x => F₁ (Function.update x (e p) false)) = D := by
    funext u; simp [F₁,D,active_isolated G e H p (hi p hpr)]
  have pd : ∃ u, F₁ (Function.update u (e p) false) ≠ F₁ (Function.update u (e p) true) :=
    ⟨x,by rw [congrFun peq x]; simp [F₁,D,hx]⟩
  have pnc : ∃ u v, F₁ (Function.update u (e p) false) ≠ F₁ (Function.update v (e p) false) :=
    ⟨x,y,by rw [congrFun peq x,congrFun peq y]; simp [D,hx,hy]⟩
  have cutp : ∀ j, HasCircuitSize m F₁ j → 1 ≤ j ∧ HasCircuitSize m D (j-1) := by
    intro j hj
    simpa only [peq] using elim_one_var (e p) false hj pd pnc
  have dep := active_dep G e H ℓ p ha hfalse (hi ℓ hlr)
  obtain ⟨ht,hf⟩ := elim_one_var (e ℓ) false hc dep nc0
  obtain ⟨_,hg⟩ := elim_one_var (e ℓ) true hc dep nc1
  change HasCircuitSize m (fun x => F (Function.update x (e ℓ) false)) _ at hf
  change HasCircuitSize m (fun x => F (Function.update x (e ℓ) true)) _ at hg
  rw [eq0] at hf
  rw [eq1] at hg
  obtain ⟨hp,hd⟩ := cutp _ hg
  refine ⟨⟨ht,hf⟩,⟨by omega,hd⟩,?_⟩
  obtain ⟨ht2,h2 | h2⟩ := elim_two_var (e ℓ) hc dep nc0 nc1
  · exact Or.inl ⟨ht2, by change HasCircuitSize m F₀ _; rw [←eq0]; exact h2⟩
  · have hsize : HasCircuitSize m F₁ (t-2) := by simpa only [←eq1] using h2
    obtain ⟨hx',hh⟩ := cutp _ hsize
    exact Or.inr ⟨by omega, hh⟩


private lemma star_reduce {d m : ℕ} (r a : Fin d) (e : Fin d ↪ Fin m)
    (H : (Fin m → Bool) → Bool)
    (hfalse : ∀ z : Fin d → Bool, ∃ x, (∀ i, x (e i) = z i) ∧ H x = false)
    (htrue : ∃ x, H x = true)
    (hi : ∀ i, i ≠ r → ∀ x b, H (Function.update x (e i) b) = H x) :
    ∀ t (G : SimpleGraph (Fin d)), G.Adj r a →
    (∀ u v, G.Adj u v → u = r ∨ v = r) → HasCircuitSize m (active G e H) t →
    ∃ q, HasCircuitSize m (fun x => H x || (x (e r) && x (e a))) q ∧ edges G + q ≤ t+1 := by
  classical
  intro t
  induction t using Nat.strong_induction_on with
  | ind t ih =>
    intro G hra star hc
    by_cases ho : ∃ l, G.Adj r l ∧ l ≠ a
    · obtain ⟨l,hrl,hla⟩ := ho
      have hlr := hrl.ne.symm
      have hl : ∀ w, G.Adj l w → w = r := fun w h => (star l w h).resolve_left hlr
      let D := G.deleteEdges {s(l,r)}
      have hD : D.Adj r a := by
        refine SimpleGraph.deleteEdges_adj.2 ⟨hra, ?_⟩
        simp [Sym2.eq_iff, Ne.symm hla,hrl.ne]
      have eq0 : (fun x => active G e H (Function.update x (e l) false)) = active D e H :=
        funext (active_leaf_false G e H l r hl (fun x => hi l hlr x false))
      obtain ⟨x,y,hx,hy,_⟩ := active_nc D e H r hfalse htrue
      have nc : ∃ x y, active G e H (Function.update x (e l) false) ≠
          active G e H (Function.update y (e l) false) :=
        ⟨x,y,by rw [congrFun eq0 x,congrFun eq0 y,hx,hy]; decide⟩
      obtain ⟨ht,hcut⟩ := elim_one_var (e l) false hc
        (active_dep G e H l r hrl.symm hfalse (hi l hlr)) nc
      rw [eq0] at hcut
      obtain ⟨q,hq,hcost⟩ := ih (t-1) (by omega) D hD (fun u v h => star u v h.1) hcut
      have he : edges D + 1 = edges G := by
        unfold D edges
        convert! edgeFinset_card_deleteEdge G l r hrl.symm using 1 <;> congr!
      exact ⟨q,hq,by omega⟩
    · have onlyA : ∀ v, G.Adj r v → v = a := by
        intro v hv
        by_contra hn
        exact ho ⟨v,hv,hn⟩
      have onlyEdge : ∀ u v, G.Adj u v → (u=r ∧ v=a) ∨ (u=a ∧ v=r) := by
        intro u v h
        rcases star u v h with rfl | rfl
        · exact Or.inl ⟨rfl,onlyA v h⟩
        · exact Or.inr ⟨onlyA u h.symm,rfl⟩
      have he : G.edgeFinset = {s(r,a)} := by
        ext z
        induction z using Sym2.ind with
        | _ u v =>
          simp only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet,Finset.mem_singleton,Sym2.eq_iff]
          exact ⟨onlyEdge u v, fun h => by rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩; exact hra; exact hra.symm⟩
      have hcount : edges G = 1 := by
        unfold edges
        convert! congrArg Finset.card he using 1 <;> simp
      have hfun : active G e H = (fun x => H x || (x (e r) && x (e a))) := by
        funext x
        unfold active
        congr 1
        apply Bool.eq_iff_iff.2
        simp only [decide_eq_true_eq, Bool.and_eq_true]
        constructor
        · rintro ⟨u,v,huv,hu,hv⟩
          rcases onlyEdge u v huv with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
          · exact ⟨hu,hv⟩
          · exact ⟨hv,hu⟩
        · rintro ⟨hr,ha⟩
          exact ⟨r,a,hra,hr,ha⟩
      exact ⟨t,hfun ▸ hc,by omega⟩

private def baseCost {d m : ℕ} (r : Fin d) (e : Fin d ↪ Fin m)
    (H : (Fin m → Bool) → Bool) : Bool → ℕ → Prop
  | false,b => ∃ c, HasCircuitSize m H c ∧ b = c+2
  | true,b => ∃ l : Fin d, l ≠ r ∧ HasCircuitSize m (fun x => H x || (x (e r) && x (e l))) b

private lemma shared_lower {d m : ℕ} (r : Fin d) (e : Fin d ↪ Fin m)
    (H : (Fin m → Bool) → Bool)
    (hfalse : ∀ z : Fin d → Bool, ∃ x, (∀ i, x (e i) = z i) ∧ H x = false)
    (htrue : ∃ x, H x = true)
    (hi : ∀ i, i ≠ r → ∀ x b, H (Function.update x (e i) b) = H x) (t : ℕ)
    (G : SimpleGraph (Fin d)) (ha : G.IsAcyclic) (hc : HasCircuitSize m (active G e H) t) :
    budget G r (baseCost r e H) t := by
  classical
  apply rooted_induction r (fun G t => HasCircuitSize m (active G e H) t) _ _
    (active_cuts r e H hfalse htrue hi) t G ha hc
  intro D j hcir star
  by_cases had : ∃ l, D.Adj r l
  · obtain ⟨l,hl⟩ := had
    obtain ⟨q,hq,hcost⟩ := star_reduce r l e H hfalse htrue hi j D hl star hcir
    refine ⟨{r},fun u v h => ?_,q,?_,by simp; omega⟩
    · simpa using star u v h
    · simpa [baseCost] using (show ∃ l : Fin d, l ≠ r ∧
        HasCircuitSize m (fun x => H x || (x (e r) && x (e l))) q from ⟨l,hl.ne.symm,hq⟩)
  · have none : ∀ u v, ¬ D.Adj u v := by
      intro u v h
      rcases star u v h with rfl | rfl
      · exact had ⟨v,h⟩
      · exact had ⟨u,h.symm⟩
    have eqf : active D e H = H := by funext x; simp [active,none]
    have he : edges D = 0 := by
      unfold edges
      apply Finset.card_eq_zero.2
      ext z
      induction z using Sym2.ind with
      | _ u v => simp [SimpleGraph.mem_edgeFinset, none]
    exact ⟨∅,fun u v h => (none u v h).elim,j+2,by simpa [baseCost] using
      (show ∃ c, HasCircuitSize m H c ∧ j+2 = c+2 from ⟨j,eqf ▸ hcir,rfl⟩),by simp [he]⟩


private def withOr {a m : ℕ} (j : Fin a ↪ Fin m) (F : (Fin m → Bool) → Bool)
    (A : Finset (Fin a)) (x : Fin m → Bool) : Bool :=
  F x || decide (∃ i ∈ A, x (j i) = true)

private lemma strip_or {a m : ℕ} (j : Fin a ↪ Fin m) (F : (Fin m → Bool) → Bool)
    (hi : ∀ i x b, F (Function.update x (j i) b) = F x)
    (hzero : ∃ x, F x = false ∧ ∀ i, x (j i) = false) (hone : ∃ x, F x = true)
    (A : Finset (Fin a)) :
    ∀ s, HasCircuitSize m (withOr j F A) s → ∃ t, HasCircuitSize m F t ∧ t+A.card ≤ s := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    intro s hc
    have hf : withOr j F ∅ = F := by funext x; simp [withOr]
    exact ⟨s,hf ▸ hc,by simp⟩
  | @insert i A hiA ih =>
    intro s hc
    obtain ⟨x,hx,hz⟩ := hzero
    obtain ⟨y,hy⟩ := hone
    have cut : (fun u => withOr j F (insert i A) (Function.update u (j i) false)) = withOr j F A := by
      funext u
      simp only [withOr,hi]
      congr 1
      apply decide_eq_decide.2
      constructor
      · rintro ⟨v,hv,hvv⟩
        rcases Finset.mem_insert.1 hv with rfl | hA
        · simp at hvv
        · have hvn : v ≠ i := fun h => hiA (h ▸ hA)
          exact ⟨v,hA,by simpa [Function.update_of_ne (j.injective.ne hvn)] using hvv⟩
      · rintro ⟨v,hv,hvv⟩
        have hvn : v ≠ i := fun h => hiA (h ▸ hv)
        exact ⟨v,Finset.mem_insert_of_mem hv,by simpa [Function.update_of_ne (j.injective.ne hvn)] using hvv⟩
    have eqx : withOr j F A x = false := by simp [withOr,hx,hz]
    have eqy : withOr j F A y = true := by simp [withOr,hy]
    have eq1 : withOr j F (insert i A) (Function.update x (j i) true) = true := by
      have he : ∃ v ∈ insert i A, Function.update x (j i) true (j v) = true :=
        ⟨i,Finset.mem_insert_self _ _,by simp⟩
      simp [withOr,he]
    obtain ⟨hs,hc'⟩ := elim_one_var (j i) false hc
      ⟨x,by rw [congrFun cut x,eqx,eq1]; decide⟩
      ⟨x,y,by rw [congrFun cut x,congrFun cut y,eqx,eqy]; decide⟩
    rw [cut] at hc'
    obtain ⟨t,ht,hle⟩ := ih _ hc'
    exact ⟨t,ht,by rw [Finset.card_insert_of_notMem hiA]; omega⟩


theorem PEqualNP.Outside.L_meta_549 :
    ∀ (n k a : ℕ) (K : SimpleGraph (Fin (k + 1))) [DecidableRel K.Adj] (g : (Fin n → Bool) → Bool → Bool), K.IsAcyclic → (∃ (y y' : Fin n → Bool) (b b' : Bool), g y b ≠ g y' b') → (∃ y : Fin n → Bool, g y false = false) → (∃ y : Fin n → Bool, g y true = false) → ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize (n + ((k + 1) + a)) (fun x : Fin (n + ((k + 1) + a)) → Bool => g (fun i : Fin n => x (Fin.castAdd ((k + 1) + a) i)) (x (Fin.natAdd n (Fin.castAdd a (0 : Fin (k + 1))))) || decide (∃ u w : Fin (k + 1), K.Adj u w ∧ x (Fin.natAdd n (Fin.castAdd a u)) = true ∧ x (Fin.natAdd n (Fin.castAdd a w)) = true) || decide (∃ i : Fin a, x (Fin.natAdd n (Fin.natAdd (k + 1) i)) = true)) s → (∃ (S : Finset (Fin (k + 1))) (c : ℕ), (∀ u w : Fin (k + 1), K.Adj u w → u ∈ S ∨ w ∈ S) ∧ (0 : Fin (k + 1)) ∉ S ∧ PEqualNP.MetaComplexity.HasCircuitSize (n + 1) (fun z : Fin (n + 1) → Bool => g (fun i : Fin n => z i.castSucc) (z (Fin.last n))) c ∧ a + K.edgeFinset.card + c + S.card ≤ s) ∨ (∃ (S : Finset (Fin (k + 1))) (q : ℕ), (∀ u w : Fin (k + 1), K.Adj u w → u ∈ S ∨ w ∈ S) ∧ (0 : Fin (k + 1)) ∈ S ∧ PEqualNP.MetaComplexity.HasCircuitSize (n + 1 + 1) (fun z : Fin (n + 1 + 1) → Bool => g (fun i : Fin n => z i.castSucc.castSucc) (z (Fin.last n).castSucc) || (z (Fin.last n).castSucc && z (Fin.last (n + 1)))) q ∧ a + K.edgeFinset.card + q + S.card ≤ s + 2) := by
  classical
  intro n k a K inst g hacy hnon hf0 hf1 s hc
  let m := n + ((k+1)+a)
  let e : Fin (k+1) ↪ Fin m :=
    ⟨fun i => Fin.natAdd n (Fin.castAdd a i),
      fun _ _ h => Fin.castAdd_injective _ _ (Fin.natAdd_injective _ _ h)⟩
  let j : Fin a ↪ Fin m :=
    ⟨fun i => Fin.natAdd n (Fin.natAdd (k+1) i),
      fun _ _ h => Fin.natAdd_injective _ _ (Fin.natAdd_injective _ _ h)⟩
  let Y : Fin n → Fin m := Fin.castAdd ((k+1)+a)
  have eA (v : Fin (k+1)) : e v = Fin.natAdd n (Fin.castAdd a v) := rfl
  have jA (v : Fin a) : j v = Fin.natAdd n (Fin.natAdd (k+1) v) := rfl
  let H := fun x : Fin m → Bool => g (fun i => x (Y i)) (x (e 0))
  have hYe : ∀ i v, Y i ≠ e v := by
    intro i v h
    have := congrArg Fin.val h
    simp [Y,e,Fin.castAdd,Fin.natAdd] at this
    omega
  have hYj : ∀ i b, Y i ≠ j b := by
    intro i b h
    have := congrArg Fin.val h
    simp [Y,j,Fin.castAdd,Fin.natAdd] at this
    omega
  have hej : ∀ v b, e v ≠ j b := by
    intro v b h
    have := congrArg Fin.val h
    simp [e,j,Fin.castAdd,Fin.natAdd] at this
    omega
  have hfalse : ∀ z : Fin (k+1) → Bool, ∃ x, (∀ i, x (e i) = z i) ∧ H x = false := by
    intro z
    have hex : ∃ y, g y (z 0) = false := by cases z 0 <;> assumption
    obtain ⟨y,hy⟩ := hex
    refine ⟨Fin.append y (Fin.append z (fun _ => false)), ?_, ?_⟩
    · intro i; simp [eA]
    · simpa [H,eA,Y] using hy
  obtain ⟨y₀,y₁,b₀,b₁,hne⟩ := hnon
  have hval : ∃ y b, g y b = true := by
    cases h0 : g y₀ b₀
    · exact ⟨y₁,b₁,by cases h1 : g y₁ b₁ <;> simp_all⟩
    · exact ⟨y₀,b₀,h0⟩
  have htrue : ∃ x, H x = true := by
    obtain ⟨y,b,hy⟩ := hval
    exact ⟨Fin.append y (fun _ => b), by simpa [H,eA,Y] using hy⟩
  have hi : ∀ i : Fin (k+1), i ≠ 0 → ∀ x b, H (Function.update x (e i) b) = H x := by
    intro i h x b
    simp [H,Function.update_of_ne (e.injective.ne h.symm),Function.update_of_ne (hYe _ i)]
  let F := active K e H
  have Fi : ∀ i x b, F (Function.update x (j i) b) = F x := by
    intro i x b
    simp [F,active,H,Function.update_of_ne (hYj _ i),Function.update_of_ne (hej _ i)] <;> congr!
  have fzero : ∃ x, F x = false ∧ ∀ i, x (j i) = false := by
    obtain ⟨y,hy⟩ := hf0
    let x : Fin m → Bool := Fin.append y (fun _ => false)
    refine ⟨x,?_,by simp [x,jA]⟩
    simp [F,active,H,x,eA,Y,hy]
  have fone : ∃ x, F x = true := by
    obtain ⟨x,hx⟩ := htrue
    exact ⟨x,by simp [F,active,hx]⟩
  have hfull : HasCircuitSize m (withOr j F Finset.univ) s := by
    convert hc using 1
    funext x
    simp [withOr,F,active,H,Y,eA,jA] <;> congr!
  obtain ⟨t,ht,hcost⟩ := strip_or j F Fi fzero fone Finset.univ s hfull
  simp only [Finset.card_univ,Fintype.card_fin] at hcost
  obtain ⟨S,hS,b,hb,hle⟩ := shared_lower 0 e H hfalse htrue hi t K hacy ht
  have heq : edges K = K.edgeFinset.card := by unfold edges; congr!
  rw [heq] at hle
  by_cases hroot : (0 : Fin (k+1)) ∈ S
  · simp only [hroot,decide_true,baseCost] at hb
    obtain ⟨l,hl, hcc⟩ := hb
    let π : Fin m → Fin (n+1+1) := Fin.addCases (fun i => i.castSucc.castSucc)
      (Fin.addCases (fun v : Fin (k+1) => if v = 0 then (Fin.last n).castSucc else Fin.last (n+1))
        (fun _ => Fin.last (n+1)))
    refine Or.inr ⟨S,b,hS,hroot,?_,by omega⟩
    have hrel := relabel_size π _ b hcc
    simpa [π,H,Y,eA,Function.comp_def,hl] using hrel
  · simp only [hroot,decide_false,baseCost] at hb
    obtain ⟨c,hcc,rfl⟩ := hb
    let π : Fin m → Fin (n+1) := Fin.addCases (fun i => i.castSucc) (fun _ => Fin.last n)
    refine Or.inl ⟨S,c,hS,hroot,?_,by omega⟩
    simpa [π,H,Y,eA,Function.comp_def] using relabel_size π _ c hcc
