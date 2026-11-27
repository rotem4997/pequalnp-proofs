import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6607_aux


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

namespace Five

def Next527 (w : Finset (BitVec 32)) (z : BitVec 32) : Prop :=
  (∃ a ∈ w, z = ~~~a) ∨
    (∃ a ∈ w, ∃ b ∈ w, a ≠ b ∧ (z = a &&& b ∨ z = a ||| b))

def Reach527 : Finset (BitVec 32) → ℕ → BitVec 32 → Prop
  | w, 0, t => t ∈ w
  | w, j + 1, t => t ∈ w ∨ ∃ z, z ∉ w ∧ z ≠ 0 ∧
      z ≠ ~~~(0 : BitVec 32) ∧ Next527 w z ∧ Reach527 (insert z w) j t

end Five

namespace Five

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

end Five

namespace Five

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

end Five

namespace Five

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

end Five

namespace Five

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

end Five

-- A circuit with k gates can depend on at most k + 1 wires already present.
-- Each layer lists wire sets covering the possibilities that still distinguish
-- inputs with different outputs. The last layer has no successor.

namespace Five

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

end Five

namespace Five

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

end Five

namespace Five

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

end Five

namespace Five

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

end Five

open Five

theorem lower527 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 0 && x 4) || (x 0 && x 5)) s → 8 ≤ s := by
  intro s h
  by_contra! hs
  have hr := leaf_reach527 hs h
  have hinputs : root527.toFinset = inputSet527 := by decide
  exact cycleExcluded527 (hinputs.symm ▸ hr)


namespace Live514
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

theorem dep_lower (n : ℕ) (f : (Fin n → Bool) → Bool)
    (hdep : ∀ i : Fin n, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : n ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : ∀ i : Fin n, i ∈ S := by
    intro i
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hcard : S.card = n := by
    rw [Finset.eq_univ_of_forall hall]; simp
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS, hcard] at hc
  omega

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

inductive Stat : Type
  | const (c : Bool)
  | wire (j : ℕ)

def Stat.val (w : List Bool) : Stat → Bool
  | Stat.const c => c
  | Stat.wire j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Stat.const _ => True
  | Stat.wire j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | Stat.const c :: _ => (none, Stat.const (!c))
  | Stat.wire j :: _ => (some ⟨GateOp.not, [j]⟩, Stat.wire m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c && d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.and, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const false)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c || d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.or, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Stat.const false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Stat.const c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Stat.const false) = Stat.const c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
        omega
      omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Stat.const _, _ => trivial
  | Stat.wire _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Stat.const _, _ => rfl
  | Stat.wire _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Stat.const false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Stat.const false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Stat.const false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_start r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Stat.const false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Stat.const false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Stat.wire i) ++ [Stat.const b]

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => Stat.wire i)).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, Stat.Valid, Stat.val, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

theorem supp_noread (n : ℕ) (gs : List Gate) : ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, n ∉ g.inputs) → (∀ j : ℕ, j ≠ n → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, j ≠ n → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (fun e => hno g List.mem_cons_self (e ▸ ha)) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem inputSupps_getD (m j : ℕ) (h : j < m) :
    (inputSupps m).getD j ∅ = {⟨j, h⟩} := by
  simp [inputSupps, h]

theorem inputSupps_noread (n : ℕ) : ∀ j : ℕ, j ≠ n →
    Fin.last n ∉ (inputSupps (n + 1)).getD j ∅ := by
  intro j hj
  by_cases hlt : j < n + 1
  · have e : (inputSupps (n + 1)).getD j ∅ = {⟨j, hlt⟩} := inputSupps_getD (n + 1) j hlt
    rw [e, Finset.mem_singleton]
    intro e'
    exact hj (by have := congrArg Fin.val e'; simpa using this.symm)
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem gate_elim (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f (s + 1)) :
    HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s + 1 := hsz
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  have hvalid : (acc.1.getD C.output (Stat.const false)).Valid (n + acc.2.length) := by
    obtain ⟨y, _, _⟩ := hnc
    exact ((hinv y).2 C.output).1
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    have hlen : acc.2.length ≤ s := by
      by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
      · have := elim_len_lt n n gs (initStats n b, []) hnok (by simp [initStats])
          ⟨b, getD_snoc_len _ _ _ _ (by simp)⟩ hread
        rw [← hacc] at this
        have hl : gs.length = C.gates.length := by simp [hgs]
        simp only [List.length_nil, zero_add] at this
        omega
      · exfalso
        push Not at hread
        have hout : C.output ≠ n := by
          intro e
          rw [e, hacc, elim_getD n n _ gs _ (by simp [initStats])] at hst
          have hb : (initStats n b).getD n (Stat.const false) = Stat.const b :=
            getD_snoc_len _ _ _ _ (by simp)
          rw [show ((initStats n b, ([] : List Gate))).1 = initStats n b from rfl, hb] at hst
          cases hst
        obtain ⟨x, hx⟩ := hdep
        apply hx
        have hns := supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) C.output hout
        have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
          (agree_inputs _ _)).2.2 C.output (by
            intro k hk
            have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
            simp [Function.update_of_ne this])
        rw [← hevg, ← hevg]
        exact hag
    refine ⟨⟨acc.2, j⟩, elim_ok n gs _ (by simp), hlen, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Stat.const false) = Stat.const b :=
  getD_snoc_len _ _ _ _ (by simp)

theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Stat.const b ∈ ins) : ∃ c, (simplify op m ins).2 = Stat.const c := by
  rcases hop with rfl | rfl | rfl
  · have := hand rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpAnd]
  · have := hor rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Stat.const false) = Stat.const c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
  rw [hnone]; simp

def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Stat.const false) = Stat.const (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Stat.const false) = Stat.const c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Stat.const false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩

theorem suppsFrom_append {n : ℕ} (pre post : List Gate) (L : List (Finset (Fin n))) :
    suppsFrom (pre ++ post) L = suppsFrom post (suppsFrom pre L) := by
  simp [suppsFrom, List.foldl_append]

theorem length_suppsFrom {n : ℕ} (gs : List Gate) : ∀ L : List (Finset (Fin n)),
    (suppsFrom gs L).length = L.length + gs.length := by
  induction gs with
  | nil => intro L; rfl
  | cons g gs ih =>
    intro L
    have h : suppsFrom (g :: gs) L = suppsFrom gs (L ++ [gateSupp L g]) := rfl
    rw [h, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate), gs[p]? = some g → CleanGate (m + p) g

theorem CleanGate.nok {m : ℕ} {g : Gate} (h : CleanGate m g) : NOk g := by
  rcases h with ⟨h1, j, _, h2⟩ | ⟨h1 | h1, j, k, _, _, h2⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inr rfl)
    · rw [h2]; simp
    · intro _; rw [h2]; simp
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inl rfl
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inl rfl)
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h

theorem CleanGate.lt {m : ℕ} {g : Gate} (h : CleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  intro a ha
  rcases h with ⟨_, j, hj, h2⟩ | ⟨_, j, k, hj, hk, h2⟩
  · rw [h2] at ha
    simp at ha
    subst ha; exact hj
  · rw [h2] at ha
    simp at ha
    rcases ha with rfl | rfl
    · exact hj
    · exact hk

theorem clean_nok (m : ℕ) (gs : List Gate) (h : CleanL m gs) : ∀ g ∈ gs, NOk g := by
  intro g hg
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hg
  exact (h p g hp).nok

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins, s.Valid m) :
    ∀ g ∈ (simplify op m ins).1, CleanGate m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    refine Or.inr ⟨Or.inl rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    refine Or.inr ⟨Or.inr rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    refine Or.inl ⟨rfl, _, ?_, rfl⟩
    exact hv _ List.mem_cons_self
  · simp at hg
  · simp at hg

theorem toList_getElem? {α : Type} (o : Option α) (k : ℕ) (a : α)
    (h : o.toList[k]? = some a) : k = 0 ∧ a ∈ o := by
  cases o with
  | none => simp at h
  | some b =>
    cases k with
    | zero => simp at h; simp [h]
    | succ k => simp at h

theorem clean_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro w acc _ _ h; exact h
  | cons g gs ih =>
    intro w acc hok hinv hcl
    have hinv' : Inv n y (wiresFrom [g] w) (elimStep n acc g) :=
      inv_elim n y hy [g] w acc (fun g' hg' => hok g' (by simp at hg'; simp [hg'])) hinv
    refine ih _ (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hinv' ?_
    intro p g' hp
    have hp' : (acc.2 ++ (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)[p]? = some g' := hp
    by_cases hlt : p < acc.2.length
    · rw [List.getElem?_append_left hlt] at hp'
      exact hcl p g' hp'
    · rw [List.getElem?_append_right (by omega)] at hp'
      obtain ⟨h0, hmem⟩ := toList_getElem? _ _ _ hp'
      have hpl : p = acc.2.length := by omega
      rw [hpl]
      exact simplify_clean _ _ _ (fun s hs => by
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        exact (hinv.2 a).1) g' hmem

def HasClean (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ (gs : List Gate) (o : ℕ), CleanL n gs ∧ gs.length ≤ s ∧
    ∀ x : Fin n → Bool, (wiresFrom gs (List.ofFn x)).getD o false = f x

def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => Stat.wire i)

theorem inv_id (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (idStats n, []) := by
  refine ⟨by simp [idStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idStats, hlt, Stat.Valid, Stat.val, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [idStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem clean_of (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (h : HasCircuitSize n f s) : HasClean n f s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  have hok : ∀ g ∈ C.gates, Ok g := ok
  set acc := elim n C.gates (idStats n, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ hok (inv_id n y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y)) = f y := by
    intro y
    rw [((hinv y).2 C.output).2, ← hev y]; rfl
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    refine ⟨acc.2, j, ?_, ?_, ?_⟩
    · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
        (inv_id n _) (by intro p g hp; simp at hp)
    · have := elim_len n C.gates (idStats n, [])
      rw [← hacc] at this
      simp only [List.length_nil, zero_add] at this
      omega
    · intro y
      have := hval y
      rw [hst] at this
      exact this

theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp
theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩

end Live514

namespace Relabel
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Live514
/-- The renaming of wires: input wire `w < n` goes to `π w`, gate wire `w ≥ n` to
`w - n + m`. -/
def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

/-- A gate with its wires renamed. -/
def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

/-- A circuit with its wires renamed. -/
def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

/-- One gate evaluated on a wire list. -/
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

/-- The invariant: the wire lists match along the renaming. -/
def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
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

theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

/-- Renaming inputs along any map keeps the circuit size. -/
theorem relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
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


end Relabel

open PEqualNP.MetaComplexity

def F : (Fin 8 → Bool) → Bool := (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 6) || (x 6 && x 7))
def pi1 : Fin 8 → Fin 8 := ![0, 1, 2, 7, 4, 5, 6, 3]
def H1 (x : Fin 8 → Bool) : Bool := F (x ∘ pi1)
def K1 (y : Fin 7 → Bool) : Bool := H1 (Fin.snoc y false)
def pi2 : Fin 7 → Fin 7 := ![0, 1, 2, 3, 4, 6, 5]
def H2 (x : Fin 7 → Bool) : Bool := K1 (x ∘ pi2)
def K2 (y : Fin 6 → Bool) : Bool := H2 (Fin.snoc y false)
def pi3 : Fin 6 → Fin 6 := ![3, 2, 4, 5, 1, 0]
def f527 : (Fin 6 → Bool) → Bool := fun x : Fin 6 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 0 && x 4) || (x 0 && x 5)

theorem dep1 : ∃ x : Fin 8 → Bool, H1 (Function.update x (Fin.last 7) (!x (Fin.last 7))) ≠ H1 x := by
  decide +kernel
theorem nc1 : ∃ y y' : Fin 7 → Bool, H1 (Fin.snoc y false) ≠ H1 (Fin.snoc y' false) := by
  decide +kernel
theorem dep2 : ∃ x : Fin 7 → Bool, H2 (Function.update x (Fin.last 6) (!x (Fin.last 6))) ≠ H2 x := by
  decide +kernel
theorem nc2 : ∃ y y' : Fin 6 → Bool, H2 (Fin.snoc y false) ≠ H2 (Fin.snoc y' false) := by
  decide +kernel
theorem last_eq : (fun x : Fin 6 → Bool => K2 (x ∘ pi3)) = f527 := by
  funext x
  revert x
  decide +kernel

theorem main : ∀ t : ℕ, HasCircuitSize 8 F t → 10 ≤ t := by
  intro t h
  by_contra! ht
  obtain ⟨C, ok, hsz, hev⟩ := h
  have h9 : HasCircuitSize 8 F (8 + 1) := ⟨C, ok, by omega, hev⟩
  have a1 : HasCircuitSize 8 H1 (8 + 1) := Relabel.relabel_size pi1 F (8 + 1) h9
  have b1 : HasCircuitSize 7 K1 (7 + 1) := Live514.gate_elim 7 H1 false (7 + 1) dep1 nc1 a1
  have a2 : HasCircuitSize 7 H2 (7 + 1) := Relabel.relabel_size pi2 K1 (7 + 1) b1
  have b2 : HasCircuitSize 6 K2 7 := Live514.gate_elim 6 H2 false 7 dep2 nc2 a2
  have a3 := Relabel.relabel_size pi3 K2 7 b2
  rw [last_eq] at a3
  have := lower527 7 a3
  omega

end PEqualNP.Outside.L_meta_6607_aux

theorem PEqualNP.Outside.L_meta_6607 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 6) || (x 6 && x 7)) t → 10 ≤ t :=
  PEqualNP.Outside.L_meta_6607_aux.main
