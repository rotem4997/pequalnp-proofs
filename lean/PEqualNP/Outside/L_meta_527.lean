import Mathlib
import PEqualNP.Defs

-- The one-variable restriction argument is adapted from L_meta_468.

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

private lemma elimPass_cons (m : ℕ) (g : Gate) (gs : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m (g :: gs) acc = elimPass m gs (elimStep m acc g) := rfl

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

-- Each bit records the value of a wire on one of the 32 inputs of the five-cycle.

namespace PEqualNP.Outside.L_meta_527_aux

def Next527 (w : Finset (BitVec 32)) (z : BitVec 32) : Prop :=
  (∃ a ∈ w, z = ~~~a) ∨
    (∃ a ∈ w, ∃ b ∈ w, a ≠ b ∧ (z = a &&& b ∨ z = a ||| b))

def Reach527 : Finset (BitVec 32) → ℕ → BitVec 32 → Prop
  | w, 0, t => t ∈ w
  | w, j + 1, t => t ∈ w ∨ ∃ z, z ∉ w ∧ z ≠ 0 ∧
      z ≠ ~~~(0 : BitVec 32) ∧ Next527 w z ∧ Reach527 (insert z w) j t

end PEqualNP.Outside.L_meta_527_aux

namespace PEqualNP.Outside.L_meta_527_aux

def cand527 (ws : List (BitVec 32)) : List (BitVec 32) :=
  let raw := ws.map (fun a => ~~~a) ++
    ws.flatMap (fun a => ws.flatMap fun b => [a &&& b, a ||| b])
  raw.eraseDups.filter fun z => !(ws.contains z) && z != 0 && z != ~~~(0 : BitVec 32)

theorem cand_complete527 {ws : List (BitVec 32)} {z : BitVec 32}
    (h : Next527 ws.toFinset z) (hn : z ∉ ws)
    (h0 : z ≠ 0) (h1 : z ≠ ~~~(0 : BitVec 32)) : z ∈ cand527 ws := by
  simp only [cand527, List.mem_filter, List.mem_eraseDups, List.mem_append,
    List.mem_map, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
  refine ⟨?_, by simp [hn]; exact ⟨h0, h1⟩⟩
  rcases h with ⟨a, ha, rfl⟩ | ⟨a, ha, b, hb, _, hab | hab⟩
  · exact Or.inl ⟨a, List.mem_toFinset.mp ha, rfl⟩
  · exact Or.inr ⟨a, List.mem_toFinset.mp ha, b, List.mem_toFinset.mp hb, Or.inl hab⟩
  · exact Or.inr ⟨a, List.mem_toFinset.mp ha, b, List.mem_toFinset.mp hb, Or.inr hab⟩

end PEqualNP.Outside.L_meta_527_aux

namespace PEqualNP.Outside.L_meta_527_aux

theorem next_mono527 {w v : Finset (BitVec 32)} {z : BitVec 32}
    (hw : w ⊆ v) (h : Next527 w z) : Next527 v z := by
  rcases h with ⟨a, ha, hz⟩ | ⟨a, ha, b, hb, hab, hz⟩
  · exact Or.inl ⟨a, hw ha, hz⟩
  · exact Or.inr ⟨a, hw ha, b, hw hb, hab, hz⟩

theorem reach_succ527 {w : Finset (BitVec 32)} {j : ℕ} {t : BitVec 32}
    (h : Reach527 w j t) : Reach527 w (j+1) t := by
  induction j generalizing w with
  | zero => exact Or.inl h
  | succ j ih =>
    rcases h with ht | ⟨z, hzw, hz0, hz1, hnext, hr⟩
    · exact Or.inl ht
    · exact Or.inr ⟨z, hzw, hz0, hz1, hnext, ih hr⟩

theorem reach_mono527 {w v : Finset (BitVec 32)} {j : ℕ} {t : BitVec 32}
    (hw : w ⊆ v) (h : Reach527 w j t) : Reach527 v j t := by
  induction j generalizing w v with
  | zero => exact hw h
  | succ j ih =>
    rcases h with ht | ⟨z, hzw, hz0, hz1, hnext, hr⟩
    · exact Or.inl (hw ht)
    · by_cases hzv : z ∈ v
      · exact reach_succ527 (ih (Finset.insert_subset hzv hw) hr)
      · exact Or.inr ⟨z, hzv, hz0, hz1, next_mono527 hw hnext,
          ih (Finset.insert_subset_insert _ hw) hr⟩

private theorem next_small527 {w : Finset (BitVec 32)} {z : BitVec 32}
    (h : Next527 w z) : ∃ p ⊆ w, p.card ≤ 2 ∧ Next527 p z := by
  rcases h with ⟨a, ha, hz⟩ | ⟨a, ha, b, hb, hab, hz⟩
  · exact ⟨{a}, by simpa, by simp, Or.inl ⟨a, by simp, hz⟩⟩
  · refine ⟨{a,b}, ?_, ?_, Or.inr ⟨a, by simp, b, by simp, hab, hz⟩⟩
    · exact Finset.insert_subset ha (Finset.singleton_subset_iff.mpr hb)
    · simp [hab]

theorem reach_support527 {w : Finset (BitVec 32)} {k : ℕ} {t : BitVec 32}
    (h : Reach527 w k t) : ∃ u ⊆ w, u.card ≤ k+1 ∧ Reach527 u k t := by
  induction k generalizing w with
  | zero => exact ⟨{t}, Finset.singleton_subset_iff.mpr h, by simp, Finset.mem_singleton_self _⟩
  | succ j ih =>
    rcases h with ht | ⟨z, hzw, hz0, hz1, hn, hr⟩
    · exact ⟨{t}, Finset.singleton_subset_iff.mpr ht, by simp, Or.inl (Finset.mem_singleton_self _)⟩
    · obtain ⟨u, hus, hcard, hu⟩ := ih hr
      by_cases hzu : z ∈ u
      · obtain ⟨p, hpw, hpcard, hpnext⟩ := next_small527 hn
        let v := u.erase z ∪ p
        have hvw : v ⊆ w := by
          intro x hx
          rcases Finset.mem_union.mp hx with he | hp
          · obtain ⟨hne,hxu⟩ := Finset.mem_erase.mp he
            exact (Finset.mem_insert.mp (hus hxu)).resolve_left hne
          · exact hpw hp
        have huv : u ⊆ insert z v := by
          intro x hx
          by_cases he : x = z
          · exact Finset.mem_insert.mpr (Or.inl he)
          · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨he,hx⟩)))
        have hvsize := Finset.card_union_le (u.erase z) p
        have herase := Finset.card_erase_of_mem hzu
        have hpositive : 0 < u.card := Finset.card_pos.mpr ⟨z,hzu⟩
        refine ⟨v, hvw, ?_, Or.inr ⟨z, fun hz => hzw (hvw hz), hz0, hz1,
            next_mono527 (Finset.subset_union_right : p ⊆ v) hpnext, reach_mono527 huv hu⟩⟩
        dsimp [v]
        omega
      · refine ⟨u, ?_, by omega, reach_succ527 hu⟩
        intro x hx
        rcases Finset.mem_insert.mp (hus hx) with he | hw
        · exact False.elim (hzu (he ▸ hx))
        · exact hw

end PEqualNP.Outside.L_meta_527_aux

namespace PEqualNP.Outside.L_meta_527_aux

def sepBlock527 : List (BitVec 32) → BitVec 32 → BitVec 32 → Bool
  | [], b, t => (b &&& t == 0) || (b &&& ~~~t == 0)
  | w :: ws, b, t =>
    if (b &&& t == 0) || (b &&& ~~~t == 0) then true
    else sepBlock527 ws (b &&& w) t && sepBlock527 ws (b &&& ~~~w) t

def sep527 (ws : List (BitVec 32)) (t : BitVec 32) : Bool :=
  sepBlock527 ws (~~~(0 : BitVec 32)) t

theorem reach_row527 {w : Finset (BitVec 32)} {k : ℕ} {t : BitVec 32}
    (h : Reach527 w k t) (i j : Fin 32)
    (eqw : ∀ a ∈ w, a.getLsbD i.val = a.getLsbD j.val) :
    t.getLsbD i.val = t.getLsbD j.val := by
  induction k generalizing w with
  | zero => exact eqw t h
  | succ k ih =>
    rcases h with ht | ⟨z, _, _, _, hn, hr⟩
    · exact eqw t ht
    · apply ih hr
      intro wire hwire
      rcases Finset.mem_insert.mp hwire with rfl | hw
      · rcases hn with ⟨a, ha, hz⟩ | ⟨a, ha, b, hb, _, hz | hz⟩
        · simp only [hz, BitVec.getLsbD_not, i.isLt, j.isLt, eqw a ha]
        · simp only [hz, BitVec.getLsbD_and, eqw a ha, eqw b hb]
        · simp only [hz, BitVec.getLsbD_or, eqw a ha, eqw b hb]
      · exact eqw wire hw

private def sameBlock527 (ws : List (BitVec 32)) (b t : BitVec 32) : Prop :=
  ∀ i j : Fin 32, b.getLsbD i = true → b.getLsbD j = true →
    (∀ a ∈ ws, a.getLsbD i = a.getLsbD j) → t.getLsbD i = t.getLsbD j

private theorem sepBlock_complete527 {ws : List (BitVec 32)} {b t : BitVec 32}
    (h : sameBlock527 ws b t) : sepBlock527 ws b t = true := by
  induction ws generalizing b with
  | nil =>
    by_cases hpos : ∃ i : Fin 32, b.getLsbD i = true ∧ t.getLsbD i = true
    · obtain ⟨i, hbi, hti⟩ := hpos
      have hz : b &&& ~~~t = 0 := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        by_cases hbj : b.getLsbD j = true
        · have hsame := h i ⟨j,hj⟩ hbi hbj (by simp)
          have htj : t.getLsbD j = true := hsame.symm.trans hti
          simp [hj, htj]
        · simp [Bool.eq_false_iff.mpr hbj]
      simp [sepBlock527, hz]
    · have hz : b &&& t = 0 := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        by_cases hbj : b.getLsbD j = true
        · have htj : t.getLsbD j ≠ true := fun ht => hpos ⟨⟨j,hj⟩, hbj, ht⟩
          simp [Bool.eq_false_iff.mpr htj]
        · simp [Bool.eq_false_iff.mpr hbj]
      simp [sepBlock527, hz]
  | cons a ws ih =>
    simp only [sepBlock527]
    split
    · rfl
    · rw [Bool.and_eq_true]
      constructor
      · apply ih
        intro i j hi hj hrest
        have hi' : b.getLsbD i = true ∧ a.getLsbD i = true := by simpa using hi
        have hj' : b.getLsbD j = true ∧ a.getLsbD j = true := by simpa using hj
        apply h i j hi'.1 hj'.1
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hi'.2.trans hj'.2.symm
        · exact hrest z hz
      · apply ih
        intro i j hi hj hrest
        have hi' : b.getLsbD i = true ∧ a.getLsbD i = false := by simpa [i.isLt] using hi
        have hj' : b.getLsbD j = true ∧ a.getLsbD j = false := by simpa [j.isLt] using hj
        apply h i j hi'.1 hj'.1
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hi'.2.trans hj'.2.symm
        · exact hrest z hz

theorem reach_sep527 {ws : List (BitVec 32)} {k : ℕ} {t : BitVec 32}
    (h : Reach527 ws.toFinset k t) : sep527 ws t = true := by
  apply sepBlock_complete527
  intro i j _ _ hrow
  exact reach_row527 h i j fun a ha => hrow a (List.mem_toFinset.mp ha)

end PEqualNP.Outside.L_meta_527_aux

namespace PEqualNP.Outside.L_meta_527_aux

theorem reach_advance527 {ws : List (BitVec 32)} {k : ℕ} {t : BitVec 32}
    (h : Reach527 ws.toFinset (k+1) t) (hw : ws.Nodup) (ht : t ∉ ws) :
    ∃ z ∈ cand527 ws, ∃ us ∈ List.sublistsLen (min (k+1) (z::ws).length) (z::ws),
      us.Nodup ∧ Reach527 us.toFinset k t ∧ sep527 us t = true := by
  rcases h with hnow | ⟨z, hzw, hz0, hz1, hn, hr⟩
  · exact False.elim (ht (List.mem_toFinset.mp hnow))
  · have hz : z ∉ ws := by simpa using hzw
    have hw' : (z :: ws).Nodup := List.nodup_cons.mpr ⟨hz,hw⟩
    have hr' : Reach527 (z :: ws).toFinset k t := by simpa using hr
    obtain ⟨u, hsub, hsmall, hur⟩ := reach_support527 hr'
    let size := min (k+1) (z::ws).length
    have hle : u.card ≤ size :=
      le_min hsmall ((Finset.card_le_card hsub).trans_eq (List.toFinset_card_of_nodup hw'))
    have hlen : size ≤ (z::ws).toFinset.card := by
      rw [List.toFinset_card_of_nodup hw']
      exact min_le_right _ _
    obtain ⟨v, huv, hvw, hvcard⟩ := Finset.exists_subsuperset_card_eq hsub hle hlen
    let us := (z::ws).filter (fun a => a ∈ v)
    have hsubl : List.Sublist us (z::ws) := List.filter_sublist
    have hus : us.toFinset = v := by
      ext a
      simp only [us, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
      exact ⟨And.right, fun ha => ⟨List.mem_toFinset.mp (hvw ha),ha⟩⟩
    have hd : us.Nodup := hsubl.nodup hw'
    have huslen : us.length = size := by
      rw [← List.toFinset_card_of_nodup hd, hus]
      exact hvcard
    have husreach : Reach527 us.toFinset k t := by
      rw [hus]
      exact reach_mono527 huv hur
    exact ⟨z, cand_complete527 hn hz hz0 hz1, us,
      List.mem_sublistsLen.mpr ⟨hsubl,huslen⟩, hd, husreach, reach_sep527 husreach⟩

end PEqualNP.Outside.L_meta_527_aux

-- A circuit with k gates can depend on at most k + 1 wires already present.
-- Each layer lists wire sets covering the possibilities that still distinguish
-- inputs with different outputs. The last layer has no successor.

namespace PEqualNP.Outside.L_meta_527_aux

def root527 : List (BitVec 32) := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]
def goal527 : BitVec 32 := 0xffeaf8c8

def layer1527 : List (List (BitVec 32)) :=
  [[0x0000ffff, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],
   [0x00ff00ff, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],
   [0x0f0f0f0f, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],
   [0x33333333, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],
   [0x55555555, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],
   [0x88888888, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],
   [0xa0a0a0a0, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],
   [0xaa00aa00, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],
   [0xaaaa0000, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],
   [0xaaaaaaaa, 0xc0c0c0c0, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],
   [0xaaaaaaaa, 0xcc00cc00, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],
   [0xaaaaaaaa, 0xcccc0000, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],
   [0xaaaaaaaa, 0xcccccccc, 0xeeeeeeee, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],
   [0xaaaaaaaa, 0xcccccccc, 0xf000f000, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],
   [0xaaaaaaaa, 0xcccccccc, 0xf0f00000, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],
   [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xfafafafa, 0xff00ff00, 0xffff0000],
   [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xfcfcfcfc, 0xff00ff00, 0xffff0000],
   [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff000000, 0xff00ff00, 0xffff0000],
   [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffaaffaa, 0xffff0000],
   [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffccffcc, 0xffff0000],
   [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xfff0fff0, 0xffff0000],
   [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000, 0xffffaaaa],
   [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000, 0xffffcccc],
   [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000, 0xfffff0f0],
   [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000, 0xffffff00]]

def layer2527 : List (List (BitVec 32)) :=
  [[0x0000ffff, 0x00ff00ff, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0],
   [0x0000ffff, 0x0f0f0f0f, 0xaaaaaaaa, 0xcccccccc, 0xff00ff00],
   [0x0000ffff, 0x33333333, 0xaaaaaaaa, 0xf0f0f0f0, 0xff00ff00],
   [0x0000ffff, 0x55555555, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00],
   [0x0000ffff, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00],
   [0x00ff00ff, 0x0f0f0f0f, 0xaaaaaaaa, 0xcccccccc, 0xffff0000],
   [0x00ff00ff, 0x33333333, 0xaaaaaaaa, 0xf0f0f0f0, 0xffff0000],
   [0x00ff00ff, 0x55555555, 0xcccccccc, 0xf0f0f0f0, 0xffff0000],
   [0x00ff00ff, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xffff0000],
   [0x0f0f0f0f, 0x33333333, 0xaaaaaaaa, 0xff00ff00, 0xffff0000],
   [0x0f0f0f0f, 0x55555555, 0xcccccccc, 0xff00ff00, 0xffff0000],
   [0x0f0f0f0f, 0xaaaaaaaa, 0xcccccccc, 0xff00ff00, 0xffff0000],
   [0x33333333, 0x55555555, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],
   [0x33333333, 0xaaaaaaaa, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],
   [0x55555555, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],
   [0xaaaa8888, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],
   [0xaaaaaaaa, 0xc8c8c8c8, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],
   [0xaaaaaaaa, 0xcccccccc, 0xf0c0f0c0, 0xff00ff00, 0xffff0000],
   [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00f000, 0xffff0000],
   [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffaa0000],
   [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],
   [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff8888],
   [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffffc0c0],
   [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xfffff000],
   [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff88ff88, 0xffff0000],
   [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xffaaff00, 0xffff0000],
   [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xffc0ffc0, 0xffff0000],
   [0xaaaaaaaa, 0xcccccccc, 0xf8f8f8f8, 0xff00ff00, 0xffff0000],
   [0xaaaaaaaa, 0xcccccccc, 0xfafaf0f0, 0xff00ff00, 0xffff0000],
   [0xaaaaaaaa, 0xcccccccc, 0xff00ff00, 0xfff0f0f0, 0xffff0000],
   [0xaaaaaaaa, 0xeeeecccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],
   [0xaaaaaaaa, 0xf0f0f0f0, 0xfcccfccc, 0xff00ff00, 0xffff0000],
   [0xaaaaaaaa, 0xf0f0f0f0, 0xff00ff00, 0xffcccccc, 0xffff0000],
   [0xcccccccc, 0xeaeaeaea, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],
   [0xcccccccc, 0xf0f0f0f0, 0xfaaafaaa, 0xff00ff00, 0xffff0000],
   [0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffaaaaaa, 0xffff0000]]

def checkLayer527 (w : List (BitVec 32)) (k : ℕ) (layers : List (List (BitVec 32))) : Bool :=
  !w.contains goal527 && (cand527 w).all fun z =>
    ((z :: w).sublistsLen (min (k+1) (z :: w).length)).all fun u =>
      !sep527 u goal527 || layers.any (fun v => u.all (fun a => v.contains a))

end PEqualNP.Outside.L_meta_527_aux

namespace PEqualNP.Outside.L_meta_527_aux

theorem close527 {w : List (BitVec 32)} {k : ℕ} {layer : List (List (BitVec 32))}
    (hn : w.Nodup) (hc : checkLayer527 w k layer = true)
    (hL : ∀ v ∈ layer, ¬ Reach527 v.toFinset k goal527) :
    ¬ Reach527 w.toFinset (k+1) goal527 := by
  intro h
  obtain ⟨hnow, hall⟩ := Bool.and_eq_true_iff.mp hc
  have ht : goal527 ∉ w := by simpa using hnow
  obtain ⟨z,hz,u,hu,_,hr,hsep⟩ := reach_advance527 h hn ht
  have ha := List.all_eq_true.mp (List.all_eq_true.mp hall z hz) u hu
  rw [hsep] at ha
  have hb : layer.any (fun v => u.all (fun a => v.contains a)) = true := ha
  obtain ⟨v,hv,hinc⟩ := List.any_eq_true.mp hb
  apply hL v hv
  apply reach_mono527 _ hr
  intro a ha
  exact List.mem_toFinset.mpr (by simpa using List.all_eq_true.mp hinc a (List.mem_toFinset.mp ha))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem lastChecks527 :
    layer2527.all (fun w => decide w.Nodup && checkLayer527 w 3 []) = true := by rfl

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem middleChecks527 :
    layer1527.all (fun w => decide w.Nodup && checkLayer527 w 4 layer2527) = true := by rfl

set_option maxRecDepth 32768 in
private theorem firstCheck527 : checkLayer527 root527 5 layer1527 = true := by rfl

theorem cycleExcluded527 : ¬ Reach527 root527.toFinset 6 goal527 := by
  apply close527 (by decide) firstCheck527
  intro v hv
  obtain ⟨hn,hc⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp middleChecks527 v hv)
  apply close527 (of_decide_eq_true hn) hc
  intro u hu
  obtain ⟨hn',hc'⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp lastChecks527 u hu)
  apply close527 (of_decide_eq_true hn') hc'
  simp

end PEqualNP.Outside.L_meta_527_aux

namespace PEqualNP.Outside.L_meta_527_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private abbrev Word527 := BitVec 32

private def Known527 (w : Finset Word527) (a : Word527) : Prop :=
  a = 0 ∨ a = BitVec.allOnes 32 ∨ a ∈ w

private def inputCols527 : List Word527 :=
  [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000, 0]

def inputSet527 : Finset Word527 :=
  {0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000}

private def wordOp527 (op : GateOp) (as : List Word527) : Word527 :=
  match op, as with
  | .and, [] => BitVec.allOnes 32
  | .and, [a] => a
  | .and, a :: b :: _ => a &&& b
  | .or, [] => 0
  | .or, [a] => a
  | .or, a :: b :: _ => a ||| b
  | .not, [] => BitVec.allOnes 32
  | .not, a :: _ => ~~~a
  | _, _ => 0

private def wordStep527 (w : List Word527) (g : Gate) : Word527 :=
  wordOp527 g.op (g.inputs.map fun i => w.getD i 0)

private def wordRun527 (w : List Word527) (gs : List Gate) : List Word527 :=
  gs.foldl (fun ws g => ws ++ [wordStep527 ws g]) w

private def bits527 (w : List Word527) (j : ℕ) : List Bool :=
  w.map (fun a => a.getLsbD j)

private lemma bits_get527 (w : List Word527) (j i : ℕ) :
    (bits527 w j).getD i false = (w.getD i 0).getLsbD j := by
  simpa [bits527] using (List.getD_map (l := w) (d := 0) (n := i)
    (fun a : Word527 => a.getLsbD j))

private def Allowed527 (op : GateOp) : Prop := op = .and ∨ op = .or ∨ op = .not

private theorem wordOp_bits527 (op : GateOp) (as : List Word527) (j : ℕ) (hj : j < 32)
    (h : Allowed527 op) (hlen : as.length ≤ 2) :
    (wordOp527 op as).getLsbD j = op.eval (bits527 as j) := by
  rcases h with rfl | rfl | rfl <;>
    cases as with
    | nil =>
      simp only [wordOp527, GateOp.eval, bits527, List.map_nil, List.all_nil,
        List.any_nil, List.headD_nil, BitVec.getLsbD_allOnes,
        hj, decide_true, Bool.not_false]
      all_goals exact BitVec.getLsbD_zero
    | cons a rest =>
      cases rest with
      | nil => simp only [wordOp527, GateOp.eval, bits527, List.map_cons, List.map_nil,
          List.all_cons, List.any_cons, List.headD_cons, id_eq, List.all_nil, List.any_nil,
          Bool.and_true, Bool.or_false, BitVec.getLsbD_not, hj, decide_true, Bool.true_and]
      | cons b tail =>
        have ht : tail = [] := by simpa using hlen
        subst tail
        simp only [wordOp527, GateOp.eval, bits527, List.map_cons, List.map_nil, List.all_cons,
          List.any_cons, List.headD_cons, id_eq, List.all_nil, List.any_nil, Bool.and_true,
          Bool.or_false, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hj,
          decide_true, Bool.true_and]

private theorem wordStep_bits527 (g : Gate) (w : List Word527) (j : ℕ) (hj : j < 32)
    (h : Allowed527 g.op) (hlen : g.inputs.length ≤ 2) :
    (wordStep527 w g).getLsbD j = g.op.eval (g.inputs.map fun i => (bits527 w j).getD i false) := by
  rw [wordStep527, wordOp_bits527 _ _ _ hj h (by simpa)]
  simp only [bits527, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact (bits_get527 w j i).symm

private theorem wordRun_bits527 (gs : List Gate) (ws : List Word527) (j : ℕ) (hj : j < 32)
    (hok : ∀ g ∈ gs, Allowed527 g.op ∧ g.inputs.length ≤ 2) :
    bits527 (wordRun527 ws gs) j =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (bits527 ws j) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    change bits527 (wordRun527 (ws ++ [wordStep527 ws g]) gs) j = _
    rw [ih _ (fun g hg => hok g (List.mem_cons_of_mem _ hg))]
    simp only [List.foldl_cons]
    congr 1
    have hg := hok g List.mem_cons_self
    unfold bits527
    rw [List.map_append]
    exact congrArg (fun a => (ws.map (fun b => b.getLsbD j)) ++ [a])
      (wordStep_bits527 g ws j hj hg.1 hg.2)

private theorem known_get527 {ws : List Word527} {w : Finset Word527}
    (hknown : ∀ a ∈ ws, Known527 w a) (i : ℕ) : Known527 w (ws.getD i 0) := by
  by_cases h : i < ws.length
  · rw [List.getD_eq_getElem _ _ h]
    exact hknown _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact Or.inl rfl

private theorem andGate527 {w : Finset Word527} {a b : Word527}
    (ha : Known527 w a) (hb : Known527 w b) : Known527 w (a &&& b) ∨ Next527 w (a &&& b) := by
  rcases ha with rfl | rfl | ha
  · exact Or.inl (Or.inl BitVec.zero_and)
  · simpa only [BitVec.allOnes_and] using Or.inl (b := Next527 w b) hb
  rcases hb with rfl | rfl | hb
  · exact Or.inl (Or.inl BitVec.and_zero)
  · exact Or.inl (Or.inr (Or.inr (by simpa only [BitVec.and_allOnes] using ha)))
  by_cases he : a = b
  · subst b
    exact Or.inl (Or.inr (Or.inr (by simpa only [BitVec.and_self] using ha)))
  · exact Or.inr (Or.inr ⟨a, ha, b, hb, he, Or.inl rfl⟩)

private theorem orGate527 {w : Finset Word527} {a b : Word527}
    (ha : Known527 w a) (hb : Known527 w b) : Known527 w (a ||| b) ∨ Next527 w (a ||| b) := by
  rcases ha with rfl | rfl | ha
  · rw [show (0 : Word527) ||| b = b from BitVec.zero_or]
    exact Or.inl hb
  · exact Or.inl (Or.inr (Or.inl BitVec.allOnes_or))
  rcases hb with rfl | rfl | hb
  · rw [show a ||| (0 : Word527) = a from BitVec.or_zero]
    exact Or.inl (Or.inr (Or.inr ha))
  · exact Or.inl (Or.inr (Or.inl BitVec.or_allOnes))
  by_cases he : a = b
  · subst b
    exact Or.inl (Or.inr (Or.inr (by simpa only [BitVec.or_self] using ha)))
  · exact Or.inr (Or.inr ⟨a, ha, b, hb, he, Or.inr rfl⟩)

private theorem notGate527 {w : Finset Word527} {a : Word527} (ha : Known527 w a) :
    Known527 w (~~~a) ∨ Next527 w (~~~a) := by
  rcases ha with rfl | rfl | ha
  · exact Or.inl (Or.inr (Or.inl rfl))
  · exact Or.inl (Or.inl rfl)
  · exact Or.inr (Or.inl ⟨a, ha, rfl⟩)

private theorem wordOp_next527 (w : Finset Word527) (op : GateOp) (as : List Word527)
    (hknown : ∀ a ∈ as, Known527 w a) (hop : Allowed527 op) :
    Known527 w (wordOp527 op as) ∨ Next527 w (wordOp527 op as) := by
  rcases hop with rfl | rfl | rfl <;>
    cases as with
    | nil => first | exact Or.inl (Or.inl rfl) | exact Or.inl (Or.inr (Or.inl rfl))
    | cons a rest =>
      have ha := hknown a List.mem_cons_self
      cases rest with
      | nil => first | exact Or.inl ha | exact notGate527 ha
      | cons b tail =>
        have hb := hknown b (List.mem_cons_of_mem a List.mem_cons_self)
        first | exact andGate527 ha hb | exact orGate527 ha hb | exact notGate527 ha

private theorem reachable527 (w : Finset Word527) (ws : List Word527) (gs : List Gate)
    (k : ℕ) (o : ℕ) (t : Word527) (hk : gs.length ≤ k)
    (hknown : ∀ a ∈ ws, Known527 w a)
    (hok : ∀ g ∈ gs, Allowed527 g.op) (hzero : t ≠ 0) (hone : t ≠ BitVec.allOnes 32)
    (ht : (wordRun527 ws gs).getD o 0 = t) : Reach527 w k t := by
  induction gs generalizing ws w k with
  | nil =>
    change ws.getD o 0 = t at ht
    have h := known_get527 hknown o
    rw [ht] at h
    have hmem := (h.resolve_left hzero).resolve_left hone
    cases k with
    | zero => exact hmem
    | succ k => exact Or.inl hmem
  | cons g gs ih =>
    let z := wordStep527 ws g
    change (wordRun527 (ws ++ [z]) gs).getD o 0 = t at ht
    have hrest := fun g' (hg' : g' ∈ gs) => hok g' (List.mem_cons_of_mem g hg')
    cases k with
    | zero => simp at hk
    | succ k =>
      have hlen : gs.length ≤ k := by simpa using hk
      by_cases h : Known527 w z
      · apply ih w (ws ++ [z]) (k+1) (by omega) _ hrest ht
        intro a ha
        simp only [List.mem_append, List.mem_singleton] at ha
        rcases ha with ha | rfl
        · exact hknown a ha
        · exact h
      · have hz : Known527 w z ∨ Next527 w z :=
          wordOp_next527 w g.op _ (by
            intro a ha
            obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
            exact known_get527 hknown i) (hok g List.mem_cons_self)
        refine Or.inr ⟨z, fun hm => h (Or.inr (Or.inr hm)), fun h0 => h (Or.inl h0),
          fun h1 => h (Or.inr (Or.inl h1)), hz.resolve_left h, ?_⟩
        apply ih (insert z w) (ws ++ [z]) k hlen _ hrest ht
        intro a ha
        simp only [List.mem_append, List.mem_singleton] at ha
        rcases ha with ha | rfl
        · rcases hknown a ha with h0 | h1 | hm
          · exact Or.inl h0
          · exact Or.inr (Or.inl h1)
          · exact Or.inr (Or.inr (Finset.mem_insert_of_mem hm))
        · exact Or.inr (Or.inr (Finset.mem_insert_self _ _))

private def row527 (j : ℕ) (i : Fin 6) : Bool := (inputCols527.getD i.val 0).getLsbD j

private theorem table_reach527 {f : (Fin 6 → Bool) → Bool} {k : ℕ} {t : Word527}
    (hf : HasCircuitSize 6 f k) (h0 : t ≠ 0) (h1 : t ≠ BitVec.allOnes 32)
    (hb : ∀ j : Fin 32, f (row527 j.val) = t.getLsbD j.val) : Reach527 inputSet527 k t := by
  obtain ⟨C, hok, hs, hev⟩ := hf
  have hok' : ∀ g ∈ C.gates, Allowed527 g.op ∧ g.inputs.length ≤ 2 := hok
  refine reachable527 inputSet527 inputCols527 C.gates k C.output t hs ?_ (fun g hg => (hok' g hg).1) h0 h1 ?_
  · intro a ha
    simp only [inputCols527, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> unfold Known527 <;> decide
  · apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [← bits_get527, wordRun_bits527 _ _ _ hj hok']
    have hinput : bits527 inputCols527 j = List.ofFn (row527 j) := by rfl
    rw [hinput]
    exact (hev (row527 j)).trans (hb ⟨j, hj⟩)

theorem cycle_lower527 (hn : ¬ Reach527 inputSet527 6 0xffeaf8c8) :
    ¬ HasCircuitSize 6 (fun x : Fin 6 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 0 && x 4)) 6 := by
  intro hf
  apply hn
  exact table_reach527 hf (by decide) (by decide) (by decide)

end PEqualNP.Outside.L_meta_527_aux

namespace PEqualNP.Outside.L_meta_527_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def leafFun527 (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 0 && x 4) || (x 0 && x 5)

theorem leaf_reach527 {s : ℕ} (hs : s < 8) (h : HasCircuitSize 6 leafFun527 s) :
    Reach527 inputSet527 6 0xffeaf8c8 := by
  obtain ⟨_, D, hd, hdsize, heval⟩ := elim_one_var (5 : Fin 6) false h
    ⟨fun i => decide (i = 0), by decide⟩
    ⟨fun _ => false, fun i => decide (i = 0 ∨ i = 1), by decide⟩
  apply table_reach527 (f := fun x => leafFun527 (Function.update x 5 false))
    (hf := ⟨D, hd, hdsize.trans (by omega), heval⟩) (by decide) (by decide)
  decide

end PEqualNP.Outside.L_meta_527_aux

open PEqualNP.Outside.L_meta_527_aux

theorem PEqualNP.Outside.L_meta_527 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 0 && x 4) || (x 0 && x 5)) s → 8 ≤ s := by
  intro s h
  by_contra! hs
  have hr := leaf_reach527 hs h
  have hinputs : root527.toFinset = inputSet527 := by decide
  exact cycleExcluded527 (hinputs.symm ▸ hr)
