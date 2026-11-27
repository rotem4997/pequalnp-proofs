import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_2507_aux

-- Wire tables and constant propagation are adapted from L-meta-2038 and L-meta-551.
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  induction gs₁ generalizing w with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, wiresFrom_cons, ih]

lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
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

lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresFrom_cons, ih _ (by simp; omega)]
    exact getD_snoc_lt _ _ _ _ hi

def OkGate (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def NOkGate (g : Gate) : Prop :=
  OkGate g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

lemma normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

lemma normGate_nok (g : Gate) (h : OkGate g) : NOkGate (normGate g) := by
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

lemma wiresFrom_norm (gs : List Gate) (w : List Bool) :
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, wiresFrom_cons, wiresFrom_cons, normGate_eval, ih]

def statVal (w : List Bool) : Bool ⊕ ℕ → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def statValid (m : ℕ) : Bool ⊕ ℕ → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplifyGate (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    Option Gate × (Bool ⊕ ℕ) :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

lemma simplifyGate_ok (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
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

lemma simplifyGate_nok (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
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

lemma simplifyGate_sound (op : GateOp)
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

def elimStep (m : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  let r := simplifyGate g.op (m + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
  (acc.1 ++ [r.2], acc.2 ++ r.1.toList)

def elimPass (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  gs.foldl (elimStep m) acc

lemma elimPass_nil (m : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m [] acc = acc := rfl

lemma elimPass_cons (m : ℕ) (g : Gate) (gs : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m (g :: gs) acc = elimPass m gs (elimStep m acc g) := rfl

lemma toList_opt_len_le {α : Type*} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

lemma elimPass_ok (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
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

def ElimInv (m : ℕ) (w_in w_old : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) : Prop :=
  w_in.length = m ∧
  acc.1.length = w_old.length ∧
  ∀ i : ℕ,
    statValid (m + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 w_in) (acc.1.getD i (Sum.inl false)) = w_old.getD i false

lemma elimInv_step (m : ℕ) (w_in w_old : List Bool)
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

lemma elimInv_pass (m : ℕ) (w_in : List Bool) (gs : List Gate)
    (w_old : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, OkGate g) (hinv : ElimInv m w_in w_old acc) :
    ElimInv m w_in (wiresFrom gs w_old) (elimPass m gs acc) := by
  induction gs generalizing w_old acc with
  | nil => exact hinv
  | cons g gs ih =>
    rw [wiresFrom_cons, elimPass_cons]
    exact ih _ _ (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (elimInv_step m w_in w_old acc g (hok g List.mem_cons_self) hinv)


def touches (g : Gate) : Bool :=
  g.inputs.any (fun i => i == 4 || i == 9)

def effectiveTouches (g : Gate) : Bool :=
  (if g.op.eval [false, false] = true then g.inputs.take 1 else g.inputs).any
    (fun i => i == 4 || i == 9)

lemma touches_norm (g : Gate) (hg : OkGate g) :
    touches (normGate g) = effectiveTouches g := by
  obtain ⟨op, ins⟩ := g
  cases op <;> simp_all [touches, effectiveTouches, normGate, GateOp.eval, OkGate]

lemma simplifyGate_none_of_const (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
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

lemma count_norm (gs : List Gate) (h : ∀ g ∈ gs, OkGate g) :
    (gs.map normGate).countP touches = gs.countP effectiveTouches := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.countP_cons, touches_norm g (h g List.mem_cons_self),
      ih (fun a ha => h a (List.mem_cons_of_mem _ ha))]

def controls (b : Bool) (x : Fin 8 → Bool) : List Bool :=
  [x 0,x 1,x 2,x 3,b,x 4,x 5,x 6,x 7,!b]

def compactIndex (j : ℕ) : ℕ := if j < 4 then j else if j < 9 then j-1 else j-2

def compactGate (g : Gate) : Gate := ⟨g.op, g.inputs.map compactIndex⟩

def Compatible (old new : List Bool) : Prop :=
  8 ≤ new.length ∧ old.length = new.length+2 ∧
  ∀ j : ℕ, j ≠ 4 → j ≠ 9 → new.getD (compactIndex j) false = old.getD j false

lemma compatible_input (b : Bool) (x : Fin 8 → Bool) : Compatible (controls b x) (List.ofFn x) := by
  refine ⟨by simp, by simp [controls], ?_⟩
  intro j h4 h9
  by_cases h : j < 10
  · interval_cases j <;> first | contradiction | rfl
  · have far : (List.ofFn x).length ≤ compactIndex j := by simp only [List.length_ofFn, compactIndex]; split_ifs <;> omega
    rw [List.getD_eq_default _ _ far, List.getD_eq_default _ _ (by simp [controls]; omega)]

lemma compatible_snoc {a b : List Bool} (h : Compatible a b) (v : Bool) :
    Compatible (a ++ [v]) (b ++ [v]) := by
  obtain ⟨h8,hl,he⟩ := h
  refine ⟨by simp; omega, by simp; omega, ?_⟩
  intro j h4 h9
  by_cases e : j = a.length
  · have e' : compactIndex j = b.length := by unfold compactIndex; split_ifs <;> omega
    rw [getD_snoc_eq _ _ _ _ e',getD_snoc_eq _ _ _ _ e]
  · have e' : compactIndex j ≠ b.length := by unfold compactIndex; split_ifs <;> omega
    rw [getD_snoc_ne _ _ _ _ e',getD_snoc_ne _ _ _ _ e]
    exact he _ h4 h9

lemma compact_ok (g : Gate) (h : OkGate g) : OkGate (compactGate g) :=
  ⟨h.1, by simpa [compactGate] using h.2⟩

lemma compact_run (gs : List Gate) (hgs : ∀ g ∈ gs, touches g = false)
    {a b : List Bool} (h : Compatible a b) :
    Compatible (wiresFrom gs a) (wiresFrom (gs.map compactGate) b) := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    have eval : (compactGate g).op.eval ((compactGate g).inputs.map (fun j => b.getD j false)) =
        g.op.eval (g.inputs.map (fun j => a.getD j false)) := by
      change g.op.eval ((g.inputs.map compactIndex).map _) = _
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro j hj
      have hn := hgs g List.mem_cons_self
      simp only [touches, List.any_eq_false] at hn
      exact h.2.2 j (fun e => hn j hj (by simp [e])) (fun e => hn j hj (by simp [e]))
    rw [List.map_cons, wiresFrom_cons, wiresFrom_cons, eval]
    exact ih (fun z hz => hgs z (List.mem_cons_of_mem _ hz)) (compatible_snoc h _)

lemma split_touch (gs : List Gate) (hc : gs.countP touches ≤ 1) :
    (∀ g ∈ gs, touches g = false) ∨
    ∃ pre g post, gs = pre ++ g :: post ∧ (∀ a ∈ pre, touches a = false) ∧
      touches g = true ∧ ∀ a ∈ post, touches a = false := by
  induction gs with
  | nil => simp
  | cons a gs ih =>
    cases h : touches a with
    | true =>
      have h0 : gs.countP touches = 0 := by
        simp only [List.countP_cons, h, ite_true] at hc
        omega
      exact Or.inr ⟨[],a,gs,rfl,by simp,h,fun x hx => Bool.eq_false_iff.mpr (List.countP_eq_zero.mp h0 x hx)⟩
    | false =>
      have h1 : gs.countP touches ≤ 1 := by simpa [List.countP_cons, h] using hc
      rcases ih h1 with ht | ⟨pre,g,post,e,hpre,hg,hpost⟩
      · exact Or.inl (by simpa only [List.forall_mem_cons] using And.intro h ht)
      · exact Or.inr ⟨a::pre,g,post,by simp [e],by simpa only [List.forall_mem_cons] using And.intro h hpre,hg,hpost⟩

inductive Atom (n : ℕ) where
  | pos
  | neg
  | z
  | wire (j : Fin n)

def Atom.reads {n : ℕ} : Atom n → Bool
  | .pos | .neg => true
  | _ => false

def Atom.value {n : ℕ} (b : Bool) (v : Fin n → Bool) : Atom n → Bool
  | .pos => b
  | .neg => !b
  | .z => false
  | .wire j => v j

def atomAt (n j : ℕ) : Atom n :=
  if j = 4 then .pos else if j = 9 then .neg else
    if h : compactIndex j < n then .wire ⟨compactIndex j,h⟩ else .z

lemma atomAt_reads (n j : Nat) : (atomAt n j).reads = (j == 4 || j == 9) := by
  unfold atomAt
  split_ifs <;> simp_all [Atom.reads]

lemma atomAt_value {a z : List Bool} (b : Bool) (h : Compatible a z)
    (h4 : a.getD 4 false = b) (h9 : a.getD 9 false = !b) (n : Nat) (hlen : z.length = n) (j : Nat) :
    Atom.value b (fun i : Fin n => z.getD i.val false) (atomAt n j) = a.getD j false := by
  unfold atomAt
  split_ifs with hc hd hv
  · subst j; exact h4.symm
  · subst j; exact h9.symm
  · exact h.2.2 j hc hd
  · rw [← h.2.2 j hc hd]
    exact (List.getD_eq_default _ _ (by omega)).symm

lemma classify_atoms {n : Nat} (op : GateOp) (args : List (Atom n))
    (hop : op = .and ∨ op = .or ∨ op = .not)
    (hlen : args.length ≤ 2)
    (hnot : op = .not → args.length ≤ 1)
    (hread : args.any Atom.reads = true) :
    (∃ c : Bool, ∀ v : Fin n → Bool, op.eval (args.map (Atom.value false v)) = c) ∨
    ∃ (i : Fin n) (c : Bool), ∀ (b : Bool) (v : Fin n → Bool),
      op.eval (args.map (Atom.value b v)) = if b then c else v i := by
  rcases hop with rfl|rfl|rfl <;>
    rcases args with _|⟨a,_|⟨d,_|⟨e,es⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
    simp_all [Atom.reads, Atom.value, GateOp.eval]
  all_goals exact Or.inr ⟨_, fun _ => rfl⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def cutRead (n : Nat) (g : Gate) : Bool := g.inputs.contains n

lemma cut_count (m n : Nat) (c : Bool) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (ok : ∀ g ∈ gs, NOkGate g) (inside : n < acc.1.length)
    (marker : acc.1.getD n (.inl false) = .inl c) :
    (elimPass m gs acc).2.length + gs.countP (cutRead n) ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
    let ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false)
    let part := simplifyGate g.op (m + acc.2.length) ins
    have hn : n < (elimStep m acc g).1.length := by simp [elimStep]; omega
    have hm : (elimStep m acc g).1.getD n (.inl false) = .inl c := by
      unfold elimStep; rw [getD_snoc_lt _ _ _ _ inside,marker]
    have ht := ih (elimStep m acc g) (fun a ha => ok a (List.mem_cons_of_mem _ ha)) hn hm
    have add : (elimStep m acc g).2.length ≤ acc.2.length + 1 := by
      change (acc.2 ++ part.1.toList).length ≤ _
      rw [List.length_append]; exact Nat.add_le_add_left (toList_opt_len_le _) _
    rw [elimPass_cons,List.countP_cons,List.length_cons]
    cases e : cutRead n g with
    | false => simp only [Bool.false_eq_true,↓reduceIte]; omega
    | true =>
      have hit : n ∈ g.inputs := by simpa [cutRead] using e
      have og := ok g List.mem_cons_self
      have epart : part.1 = none := by
        apply simplifyGate_none_of_const _ _ _ og.1.1
        · simpa [ins] using og.1.2
        · intro he; simpa [ins] using og.2 he
        · exact ⟨c,List.mem_map.mpr ⟨n,hit,marker⟩⟩
      have eLen : (elimStep m acc g).2.length = acc.2.length := by
        change (acc.2 ++ part.1.toList).length = _; simp [epart]
      simp only [↓reduceIte]; omega

lemma cut_agree (n : Nat) (gs : List Gate) (no : ∀g∈gs, n∉g.inputs) (v w : List Bool)
    (len : v.length=w.length) (agree : ∀ i, i≠n → v.getD i false = w.getD i false) :
    ∀ i, i≠n → (wiresFrom gs v).getD i false = (wiresFrom gs w).getD i false := by
  induction gs generalizing v w with
  | nil => exact agree
  | cons g gs ih =>
    rw [wiresFrom_cons,wiresFrom_cons]
    have val : g.inputs.map (fun i => v.getD i false) = g.inputs.map (fun i => w.getD i false) := by
      exact List.map_congr_left (fun i hi => agree i (fun h => no g List.mem_cons_self (h ▸ hi)))
    rw [val]
    apply ih (fun g hg => no g (List.mem_cons_of_mem _ hg)) _ _ (by simp [len])
    intro i hn
    by_cases h : i=v.length
    · rw [getD_snoc_eq _ _ _ _ h,getD_snoc_eq _ _ _ _ (h.trans len)]
    · rw [getD_snoc_ne _ _ _ _ h,getD_snoc_ne _ _ _ _ (by omega)]
      exact agree i hn

def cutInit (P : Circuit) (c : Bool) : List (Bool ⊕ ℕ) × List Gate :=
  (((List.range (8 + P.size)).map (Sum.inr : Nat → Bool ⊕ Nat)) ++ [Sum.inl c], P.gates)

lemma cut_inv (P : Circuit) (c : Bool) (x : Fin 8 → Bool) :
    ElimInv 8 (List.ofFn x) (P.wires (List.ofFn x) ++ [c]) (cutInit P c) := by
  let n := 8 + P.size
  let w := P.wires (List.ofFn x)
  have len : w.length = n := by
    change (wiresFrom P.gates (List.ofFn x)).length = _
    simp [wiresFrom_length,n,Circuit.size]
  have l2 : ((List.range n).map (Sum.inr : Nat → Bool ⊕ Nat)).length = n := by simp
  refine ⟨by simp,?_,?_⟩
  · change (((List.range n).map (Sum.inr : Nat → Bool ⊕ Nat)) ++ [Sum.inl c]).length = (w++[c]).length
    simp only [List.length_append,List.length_singleton,l2,len]
  intro i
  change statValid n ((((List.range n).map (Sum.inr : Nat → Bool ⊕ Nat)) ++ [Sum.inl c]).getD i (.inl false)) ∧
    statVal w ((((List.range n).map (Sum.inr : Nat → Bool ⊕ Nat)) ++ [Sum.inl c]).getD i (.inl false)) = (w++[c]).getD i false
  rcases Nat.lt_trichotomy i n with h|h|h
  · rw [getD_snoc_lt _ _ _ _ (by omega),getD_snoc_lt _ _ _ _ (by omega)]
    simp [List.getD_eq_getElem?_getD,h,statValid,statVal]
  · rw [getD_snoc_eq _ _ _ _ (by omega),getD_snoc_eq _ _ _ _ (by omega)]
    exact ⟨trivial,rfl⟩
  · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial,rfl⟩

theorem constantCut (P Q : Circuit) (c : Bool) (hP : FanInTwo P) (hQ : FanInTwo Q)
    (hn : Q.eval (P.wires (List.ofFn (fun _ : Fin 8 => false)) ++ [c]) ≠
      Q.eval (P.wires (List.ofFn (fun _ : Fin 8 => true)) ++ [c]))
    (hd : ∃ (x : Fin 8 → Bool) (b : Bool), Q.eval (P.wires (List.ofFn x) ++ [c]) ≠
      Q.eval (P.wires (List.ofFn x) ++ [b])) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + 1 ≤ P.size + Q.size ∧
      ∀ x : Fin 8 → Bool, D.eval (List.ofFn x) = Q.eval (P.wires (List.ofFn x) ++ [c]) := by
  let n := 8 + P.size
  let gs := Q.gates.map normGate
  let acc := elimPass 8 gs (cutInit P c)
  have ok (g) (hg : g∈gs) : NOkGate g := by
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg; exact normGate_nok _ (hQ _ ha)
  have len (x : Fin 8 → Bool) : (P.wires (List.ofFn x)).length = n := by
    change (wiresFrom P.gates _).length = _; simp [wiresFrom_length,n,Circuit.size]
  have eval (v : List Bool) : Q.eval v = (wiresFrom gs v).getD Q.output false :=
    (congrArg (fun w => w.getD Q.output false) (wiresFrom_norm Q.gates v)).symm
  have neq : Q.output ≠ n := by
    intro h; apply hn
    rw [eval,eval,h,wiresFrom_getD_lt _ _ _ (by simp only [List.length_append,List.length_singleton,len]; omega),wiresFrom_getD_lt _ _ _ (by simp only [List.length_append,List.length_singleton,len]; omega)]
    rw [getD_snoc_eq _ _ _ _ (len _).symm,getD_snoc_eq _ _ _ _ (len _).symm]
  have hit : ∃ g ∈ gs, n ∈ g.inputs := by
    by_contra! miss
    obtain ⟨x,b,ne⟩ := hd
    apply ne
    rw [eval,eval]
    apply cut_agree n gs miss _ _ (by simp) _ _ neq
    intro i hi
    rw [getD_snoc_ne _ _ _ _ (by rw [len]; exact hi),getD_snoc_ne _ _ _ _ (by rw [len]; exact hi)]
  obtain ⟨g,hg,ht⟩ := hit
  have cnt : 0 < gs.countP (cutRead n) := List.countP_pos_iff.mpr ⟨g,hg,by simpa [cutRead] using ht⟩
  have sz : acc.2.length + 1 ≤ P.size+Q.size := by
    have size := cut_count 8 n c gs (cutInit P c) ok (by simp [cutInit,n])
      (getD_snoc_eq _ _ _ _ (by simp [n]))
    change acc.2.length + gs.countP (cutRead n) ≤ P.size + gs.length at size
    have sl : gs.length = Q.size := List.length_map _
    omega
  have result (x : Fin 8 → Bool) : statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD Q.output (.inl false)) =
      Q.eval (P.wires (List.ofFn x) ++ [c]) := by
    rw [eval]; exact ((elimInv_pass _ _ _ _ _ (fun g hg => (ok g hg).1) (cut_inv P c x)).2.2 Q.output).2
  cases e : acc.1.getD Q.output (.inl false) with
  | inl b =>
    have h0 := result (fun _ => false)
    have h1 := result (fun _ => true)
    rw [e] at h0 h1
    exact (hn (h0.symm.trans h1)).elim
  | inr j =>
    refine ⟨⟨acc.2,j⟩,elimPass_ok _ _ _ hP,sz,?_⟩
    intro x; have hx := result x; rwa [e] at hx

def CutOutcome (C : Circuit) : Prop :=
  (∃ D : Circuit, FanInTwo D ∧ D.size + 2 ≤ C.size ∧
    ∀ x : Fin 8 → Bool, D.eval (List.ofFn x) = C.eval (controls false x)) ∨
  ∃ (P Q : Circuit) (j : Nat) (c : Bool), FanInTwo P ∧ FanInTwo Q ∧
    P.size + Q.size + 1 ≤ C.size ∧ j < 8 + P.size ∧
    ∀ (x : Fin 8 → Bool) (b : Bool), Q.eval (P.wires (List.ofFn x) ++
      [if b then c else (P.wires (List.ofFn x)).getD j false]) = C.eval (controls b x)

def ConstPrinciple : Prop := ∀ (P Q : Circuit) (c : Bool), FanInTwo P → FanInTwo Q →
    Q.eval (P.wires (List.ofFn (fun _ : Fin 8 => false)) ++ [c]) ≠
      Q.eval (P.wires (List.ofFn (fun _ : Fin 8 => true)) ++ [c]) →
    (∃ (x : Fin 8 → Bool) (b : Bool), Q.eval (P.wires (List.ofFn x) ++ [c]) ≠
      Q.eval (P.wires (List.ofFn x) ++ [b])) →
    ∃ D : Circuit, FanInTwo D ∧ D.size + 1 ≤ P.size + Q.size ∧
      ∀ x : Fin 8 → Bool, D.eval (List.ofFn x) = Q.eval (P.wires (List.ofFn x) ++ [c])

lemma split_circuit (small : ConstPrinciple) (C : Circuit) (hf : FanInTwo C)
    (hc : C.gates.countP effectiveTouches ≤ 1)
    (hz : C.eval (controls false (fun _ => false)) = false)
    (ho : C.eval (controls false (fun _ => true)) = true)
    (hd : ∃ x : Fin 8 → Bool, C.eval (controls false x) ≠ C.eval (controls true x)) :
    CutOutcome C := by
  let gs := C.gates.map normGate
  have hlen : gs.length = C.size := by simp [gs,Circuit.size]
  have hnorm (b : Bool) (x : Fin 8 → Bool) : (wiresFrom gs (controls b x)).getD C.output false =
      C.eval (controls b x) := congrArg (fun w => List.getD w C.output false)
        (wiresFrom_norm C.gates (controls b x))
  have nok (g : Gate) (hg : g ∈ gs) : NOkGate g := by
    change g ∈ C.gates.map normGate at hg
    obtain ⟨r,hr,e⟩ := List.mem_map.mp hg
    rw [← e]
    exact normGate_nok r (hf r hr)
  have out4 : C.output ≠ 4 := by
    intro e
    have h := hnorm false (fun _ => true)
    rw [e,wiresFrom_getD_lt _ _ _ (by simp [controls]),ho] at h
    contradiction
  have out9 : C.output ≠ 9 := by
    intro e
    have h := hnorm false (fun _ => false)
    rw [e,wiresFrom_getD_lt _ _ _ (by simp [controls]),hz] at h
    contradiction
  have hc' : gs.countP touches ≤ 1 := (count_norm C.gates hf).symm ▸ hc
  obtain hnone | ⟨pre,g,post,splitGs,preNo,reads,postNo⟩ := split_touch gs hc'
  · obtain ⟨x,hx⟩ := hd
    have both (b : Bool) := (compact_run gs hnone (compatible_input b x)).2.2 C.output out4 out9
    apply False.elim <| hx _
    exact (hnorm false x).symm.trans ((both false).symm.trans ((both true).trans (hnorm true x)))
  · let P : Circuit := ⟨pre.map compactGate, 0⟩
    let Q : Circuit := ⟨post.map compactGate, compactIndex C.output⟩
    let n := 8+P.size
    have counts : P.size + Q.size + 1 = C.size := by
      rw [← hlen, splitGs]; simp [P,Q,Circuit.size]; omega
    have hP : FanInTwo P := by
      intro a ha
      obtain ⟨r,hr,rfl⟩ := List.mem_map.mp ha
      exact compact_ok r (nok r (splitGs ▸ List.mem_append_left _ hr)).1
    have hQ : FanInTwo Q := by
      intro a ha
      obtain ⟨r,hr,rfl⟩ := List.mem_map.mp ha
      exact compact_ok r (nok r (splitGs ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hr))).1
    have hg := nok g (splitGs ▸ List.mem_append_right _ List.mem_cons_self)
    let old (b : Bool) (x : Fin 8 → Bool) := wiresFrom pre (controls b x)
    let prefixWires (x : Fin 8 → Bool) := P.wires (List.ofFn x)
    have plen (x : Fin 8 → Bool) : (prefixWires x).length = n := by
      change (wiresFrom (pre.map compactGate) (List.ofFn x)).length = _
      simp [wiresFrom_length,n,P,Circuit.size]
    have rel (b : Bool) (x : Fin 8 → Bool) : Compatible (old b x) (prefixWires x) :=
      compact_run pre preNo (compatible_input b x)
    let mid (b : Bool) (x : Fin 8 → Bool) := g.op.eval (g.inputs.map (fun j => (old b x).getD j false))
    have adapter (b : Bool) (x : Fin 8 → Bool) : Q.eval (prefixWires x ++ [mid b x]) = C.eval (controls b x) := by
      rw [← hnorm, splitGs, wiresFrom_append, wiresFrom_cons]
      exact (compact_run post postNo (compatible_snoc (rel b x) (mid b x))).2.2 C.output out4 out9
    let args := g.inputs.map (atomAt n)
    have aread : args.any Atom.reads = true := by
      obtain ⟨j,hj,hc⟩ := List.any_eq_true.mp reads
      exact List.any_eq_true.mpr ⟨atomAt n j,List.mem_map.mpr ⟨j,hj,rfl⟩,(atomAt_reads n j).trans hc⟩
    have av (b : Bool) (x : Fin 8 → Bool) : g.op.eval
        (args.map (Atom.value b (fun i : Fin n => (prefixWires x).getD i.val false))) = mid b x := by
      unfold mid args; rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro j _
      apply atomAt_value b (rel b x) _ _ n (plen x)
      · exact (wiresFrom_getD_lt pre (controls b x) 4 (by simp [controls])).trans rfl
      · exact (wiresFrom_getD_lt pre (controls b x) 9 (by simp [controls])).trans rfl
    rcases classify_atoms g.op args hg.1.1 (by simpa [args] using hg.1.2)
        (fun hn => by simpa [args] using hg.2 hn) aread with ⟨c,hc⟩ | ⟨i,c,hc⟩
    · left
      have fix (x : Fin 8 → Bool) : Q.eval (prefixWires x ++ [c]) = C.eval (controls false x) := by
        have e := (av false x).symm.trans (hc (fun i => (prefixWires x).getD i.val false))
        simpa only [e] using adapter false x
      obtain ⟨x,hx⟩ := hd
      obtain ⟨D,hD,hs,correct⟩ := small P Q c hP hQ (by rw [fix,fix,hz,ho]; decide)
        ⟨x,mid true x,by rw [fix,adapter]; exact hx⟩
      exact ⟨D,hD,by omega,fun x => (correct x).trans (fix x)⟩
    · right
      refine ⟨P,Q,i.val,c,hP,hQ,counts.le,i.isLt,?_⟩
      intro x b
      have e := (av b x).symm.trans (hc b (fun i => (prefixWires x).getD i.val false))
      exact e ▸ adapter b x

end PEqualNP.Outside.L_meta_2507_aux

theorem PEqualNP.Outside.L_meta_2507 :
  have x1 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) => (if x1.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x1.inputs else x1.inputs).any fun (x2 : ℕ) => x2 == (4 : ℕ) || x2 == (9 : ℕ); have x2 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x2 : Bool) (x3 : Fin (8 : ℕ) → Bool) => [x3 (0 : Fin (8 : ℕ)), x3 (1 : Fin (8 : ℕ)), x3 (2 : Fin (8 : ℕ)), x3 (3 : Fin (8 : ℕ)), x2, x3 (4 : Fin (8 : ℕ)), x3 (5 : Fin (8 : ℕ)), x3 (6 : Fin (8 : ℕ)), x3 (7 : Fin (8 : ℕ)), !x2]; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x3 →     List.countP x1 x3.gates ≤ (1 : ℕ) →       x3.eval (x2 Bool.false fun (x6 : Fin (8 : ℕ)) => Bool.false) = Bool.false →         x3.eval (x2 Bool.false fun (x7 : Fin (8 : ℕ)) => Bool.true) = Bool.true →           (∃ (x8 : Fin (8 : ℕ) → Bool), x3.eval (x2 Bool.false x8) ≠ x3.eval (x2 Bool.true x8)) →             (∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x9 ∧ x9.size + (2 : ℕ) ≤ x3.size ∧ ∀ (x10 : Fin (8 : ℕ) → Bool), x9.eval (List.ofFn x10) = x3.eval (x2 Bool.false x10)) ∨               ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : PEqualNP.CircuitLowerBounds.Circuit) (x11 : ℕ) (x12 : Bool),                 PEqualNP.MetaComplexity.FanInTwo x9 ∧                   PEqualNP.MetaComplexity.FanInTwo x10 ∧                     x9.size + x10.size + (1 : ℕ) ≤ x3.size ∧                       x11 < (8 : ℕ) + x9.size ∧                         ∀ (x13 : Fin (8 : ℕ) → Bool) (x14 : Bool),                           have x15 : List Bool := x9.wires (List.ofFn x13);                           x10.eval (x15 ++ [if x14 = Bool.true then x12 else x15.getD x11 Bool.false]) = x3.eval (x2 x14 x13) := by
  exact PEqualNP.Outside.L_meta_2507_aux.split_circuit PEqualNP.Outside.L_meta_2507_aux.constantCut
