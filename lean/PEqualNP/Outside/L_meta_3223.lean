import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_3223

-- The following constant-propagation lemmas are reused from L-meta-2507.
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

def tag {n : Nat} : Option (Fin n) → Bool ⊕ Nat
  | none => .inl false
  | some j => .inr j.val

def proj {n : Nat} (p : List (Option (Fin n))) (x : Fin n → Bool) :=
  p.map fun j => j.elim false x

def start {n : Nat} (p : List (Option (Fin n))) : List (Bool ⊕ Nat) × List Gate :=
  (p.map tag, [])

lemma startInv {n} (p : List (Option (Fin n))) (x : Fin n → Bool) :
    ElimInv n (List.ofFn x) (proj p x) (start p) := by
  refine ⟨by simp, by simp [start,proj], ?_⟩
  intro i
  change statValid (n+0) ((p.map tag).getD i (.inl false)) ∧
    statVal (List.ofFn x) ((p.map tag).getD i (.inl false)) = (proj p x).getD i false
  induction p generalizing i with
  | nil => simp [proj,statValid,statVal]
  | cons a p ih =>
    cases i with
    | succ j => simpa [proj,List.getD] using ih j
    | zero => cases a with
      | none => simp [tag,proj,statValid,statVal,List.getD]
      | some j => simp [tag,proj,statValid,statVal,List.getD,j.isLt]

def run {n} (C : Circuit) (p : List (Option (Fin n))) :=
  elimPass n (C.gates.map normGate) (start p)

lemma run_eval {n} (C : Circuit) (p : List (Option (Fin n))) (hC : FanInTwo C)
    (x : Fin n → Bool) : statVal (wiresFrom (run C p).2 (List.ofFn x))
      ((run C p).1.getD C.output (.inl false)) = C.eval (proj p x) := by
  have ok : ∀ g ∈ C.gates.map normGate, OkGate g := by
    intro g hg; obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg; exact (normGate_nok a (hC a ha)).1
  have spec := ((elimInv_pass _ _ _ _ _ ok (startInv p x)).2.2 C.output).2
  rw [wiresFrom_norm] at spec
  exact spec

lemma extract {n} (C : Circuit) (p : List (Option (Fin n))) (hC : FanInTwo C)
    (hnc : ∃ x y, C.eval (proj p x) ≠ C.eval (proj p y)) :
    ∃ D : Circuit, FanInTwo D ∧ D.size = (run C p).2.length ∧
      ∀ x, D.eval (List.ofFn x) = C.eval (proj p x) := by
  cases e : (run C p).1.getD C.output (.inl false) with
  | inl b =>
    obtain ⟨x,y,h⟩ := hnc
    have hx := run_eval C p hC x; have hy := run_eval C p hC y
    rw [e] at hx hy
    exact (h (hx.symm.trans hy)).elim
  | inr j =>
    refine ⟨⟨(run C p).2,j⟩,elimPass_ok _ _ _ (by simp [start]),rfl,?_⟩
    intro x; have h := run_eval C p hC x; rwa [e] at h

lemma falseControl (op : GateOp) (m : Nat) (ins : List (Bool ⊕ Nat))
    (hop : op = GateOp.and ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hn : op = GateOp.not → ins.length ≤ 1) (pin : Sum.inl false ∈ ins) :
    ∃ c, (simplifyGate op m ins).2 = Sum.inl c := by
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplifyGate,simpAnd] <;> aesop
  · have := hn rfl
    rcases ins with _ | ⟨a, _ | ⟨b,l⟩⟩ <;> (try cases a) <;> simp_all [simplifyGate,simpNot]

def Tracks (k bonus saved : Nat) (v w : List Bool) (tags : List (Bool ⊕ Nat)) :=
  ∀ i, v.getD i false ≠ w.getD i false → (saved = 0 → i = k) ∧
    (saved ≤ bonus → ∃ c, tags.getD i (.inl false) = .inl c)

lemma trackGate {k bonus saved m : Nat} {g : Gate} {v w : List Bool}
    {tags : List (Bool ⊕ Nat)} (tr : Tracks k bonus saved v w tags)
    (og : NOkGate g) (small : bonus ≤ 1)
    (noOr : bonus = 1 → g.op = GateOp.or → k ∉ g.inputs)
    (marker : tags.getD k (.inl false) = .inl false)
    (different : g.op.eval (g.inputs.map fun i => v.getD i false) ≠
      g.op.eval (g.inputs.map fun i => w.getD i false)) :
    let ins := g.inputs.map fun i => tags.getD i (.inl false)
    let part := simplifyGate g.op m ins
    (saved ≤ bonus → part.1 = none) ∧
    (saved = 0 → bonus = 1 → ∃ c, part.2 = .inl c) := by
  classical
  obtain ⟨i,hi,ne⟩ : ∃ i ∈ g.inputs, v.getD i false ≠ w.getD i false := by
    by_contra! h; exact different (congrArg g.op.eval (List.map_congr_left h))
  obtain ⟨origin,constant⟩ := tr i ne
  constructor
  · intro hs
    obtain ⟨c,hc⟩ := constant hs
    apply simplifyGate_none_of_const _ _ _ og.1.1
    · simpa using og.1.2
    · intro h; simpa using og.2 h
    · exact ⟨c,List.mem_map.mpr ⟨i,hi,hc⟩⟩
  · intro hs hb
    have ik := origin hs; subst i
    apply falseControl
    · have h : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := og.1.1
      rcases h with h | h | h
      · exact Or.inl h
      · exact (noOr hb h hi).elim
      · exact Or.inr h
    · simpa using og.1.2
    · intro h; simpa using og.2 h
    · exact List.mem_map.mpr ⟨k,hi,marker⟩

def omitCost (out : Option Gate) : Nat := if out.isNone then 1 else 0

lemma trackSnoc {k bonus saved m : Nat} {g : Gate} {v w : List Bool}
    {tags : List (Bool ⊕ Nat)} (tr : Tracks k bonus saved v w tags)
    (og : NOkGate g) (small : bonus ≤ 1)
    (noOr : bonus = 1 → g.op = GateOp.or → k ∉ g.inputs)
    (marker : tags.getD k (.inl false) = .inl false)
    (vw : v.length = w.length) (vt : v.length = tags.length) :
    let val := fun z : List Bool => g.op.eval (g.inputs.map fun i => z.getD i false)
    let part := simplifyGate g.op m (g.inputs.map fun i => tags.getD i (.inl false))
    Tracks k bonus (saved + omitCost part.1) (v ++ [val v]) (w ++ [val w])
      (tags ++ [part.2]) := by
  dsimp only
  let part := simplifyGate g.op m (g.inputs.map fun i => tags.getD i (.inl false))
  intro i diff
  by_cases hi : i = v.length
  · rw [getD_snoc_eq _ _ _ _ hi,getD_snoc_eq _ _ _ _ (hi.trans vw)] at diff
    obtain ⟨gone,ct⟩ := trackGate (m:=m) tr og small noOr marker diff
    change (saved ≤ bonus → part.1 = none) at gone
    change (saved = 0 → bonus = 1 → ∃ c, part.2 = .inl c) at ct
    change (saved + omitCost part.1 = 0 → _) ∧ (saved + omitCost part.1 ≤ bonus → _)
    constructor
    · intro h
      have hg := gone (by omega)
      simp [omitCost,hg] at h
    · intro h
      have hg := gone (by omega)
      simp [omitCost,hg] at h
      obtain ⟨c,hc⟩ := ct (by omega) (by omega)
      exact ⟨c,(getD_snoc_eq _ _ _ _ (hi.trans vt)).trans hc⟩
  · rw [getD_snoc_ne _ _ _ _ hi,getD_snoc_ne _ _ _ _ (by omega)] at diff
    obtain ⟨a,b⟩ := tr i diff
    constructor
    · intro h; exact a (by omega)
    · intro h; rw [getD_snoc_ne _ _ _ _ (by omega)]; exact b (by omega)

lemma trackPass {k bonus m : Nat} (gs : List Gate) (saved : Nat)
    (acc : List (Bool ⊕ Nat) × List Gate) (v w : List Bool)
    (og : ∀ g ∈ gs, NOkGate g) (small : bonus ≤ 1)
    (noOr : bonus = 1 → ∀ g ∈ gs, g.op = GateOp.or → k ∉ g.inputs)
    (inside : k < acc.1.length) (marker : acc.1.getD k (.inl false) = .inl false)
    (vw : v.length = w.length) (vt : v.length = acc.1.length)
    (tr : Tracks k bonus saved v w acc.1) :
    ∃ total, (elimPass m gs acc).2.length + total = acc.2.length + gs.length + saved ∧
      Tracks k bonus total (wiresFrom gs v) (wiresFrom gs w) (elimPass m gs acc).1 := by
  induction gs generalizing saved acc v w with
  | nil => exact ⟨saved,by simp [elimPass],tr⟩
  | cons g gs ih =>
    let part := simplifyGate g.op (m + acc.2.length) (g.inputs.map fun i => acc.1.getD i (.inl false))
    let val := fun z : List Bool => g.op.eval (g.inputs.map fun i => z.getD i false)
    let next := elimStep m acc g
    have ht : Tracks k bonus (saved+omitCost part.1) (v++[val v]) (w++[val w]) next.1 :=
      trackSnoc tr (og _ List.mem_cons_self) small (fun h => noOr h _ List.mem_cons_self) marker vw vt
    have hn : k < next.1.length := by simp [next,elimStep]; omega
    have hm : next.1.getD k (.inl false) = .inl false := (getD_snoc_lt _ _ _ _ inside).trans marker
    obtain ⟨total,he,hr⟩ := ih _ next _ _ (fun a ha => og a (by simp [ha]))
      (fun h a ha => noOr h a (by simp [ha])) hn hm (by simp [vw])
      (by simp [next,elimStep,vt]) ht
    have cost : next.2.length + omitCost part.1 = acc.2.length + 1 := by
      change (acc.2 ++ part.1.toList).length + _ = _
      cases h : part.1 <;> simp [h,omitCost]
    refine ⟨total,?_,hr⟩
    change (elimPass m gs next).2.length + total = _
    rw [List.length_cons]; omega

lemma savedBound {n} (C : Circuit) (p : List (Option (Fin n))) (k bonus : Nat)
    (hC : FanInTwo C) (atK : p[k]? = some none) (small : bonus ≤ 1)
    (noOr : bonus = 1 → ∀ g ∈ C.gates, g.op = GateOp.or → k ∉ g.inputs)
    (sense : ∃ v w : List Bool, v.length = p.length ∧ w.length = p.length ∧
      (∀ j, j ≠ k → v.getD j false = w.getD j false) ∧ C.eval v ≠ C.eval w)
    (hnc : ∃ x y, C.eval (proj p x) ≠ C.eval (proj p y)) :
    (run C p).2.length + (bonus + 1) ≤ C.size := by
  obtain ⟨v,w,hv,hw,hvw,diff⟩ := sense
  have inside : k < p.length := by
    by_contra! h; rw [List.getElem?_eq_none h] at atK; contradiction
  have mk : (start p).1.getD k (.inl false) = .inl false := by
    simp [start,List.getD,List.getElem?_map,atK,tag]
  have tr : Tracks k bonus 0 v w (start p).1 := by
    intro i h
    have hi : i=k := by by_contra H; exact h (hvw i H)
    subst i; exact ⟨fun _ => rfl,fun _ => ⟨false,mk⟩⟩
  let gs := C.gates.map normGate
  have ok : ∀ g ∈ gs, NOkGate g := by
    intro g hg; obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg; exact normGate_nok a (hC a ha)
  have nor : bonus=1 → ∀ g ∈ gs, g.op = GateOp.or → k ∉ g.inputs := by
    intro hb g hg hgo
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    cases a with | mk op ins =>
      cases op <;> simp [normGate] at hgo
      exact noOr hb _ ha rfl
  obtain ⟨total,he,ht⟩ := trackPass (m:=n) gs 0 (start p) v w ok small nor
    (by simpa [start] using inside) mk (hv.trans hw.symm) (by simpa [start] using hv) tr
  have out : (wiresFrom gs v).getD C.output false ≠ (wiresFrom gs w).getD C.output false := by
    simpa [gs,wiresFrom_norm] using (show (wiresFrom C.gates v).getD C.output false ≠ (wiresFrom C.gates w).getD C.output false from diff)
  have enough : bonus < total := by
    by_contra! h
    obtain ⟨c,hc⟩ := (ht C.output out).2 h
    obtain ⟨x,y,ne⟩ := hnc
    have hx := run_eval C p hC x; have hy := run_eval C p hC y
    change (run C p).1.getD C.output (.inl false) = .inl c at hc
    rw [hc] at hx hy; exact ne (hx.symm.trans hy)
  change (run C p).2.length + total = (start p).2.length + gs.length + 0 at he
  simp [start,gs] at he; unfold Circuit.size; omega

end PEqualNP.Outside.L_meta_3223




theorem PEqualNP.Outside.L_meta_3223 :
∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : List (Option (Fin x1))) (x4 x5 : ℕ), PEqualNP.MetaComplexity.FanInTwo x2 → x3[x4]? = Option.some Option.none → x5 ≤ (1 : ℕ) → (x5 = (1 : ℕ) → ∀ x10 ∈ x2.gates, x10.op = PEqualNP.CircuitLowerBounds.GateOp.or → x4 ∉ x10.inputs) → (∃ (x10 : List Bool) (x11 : List Bool), x10.length = x3.length ∧ x11.length = x3.length ∧ (∀ (x12 : ℕ), x12 ≠ x4 → x10.getD x12 Bool.false = x11.getD x12 Bool.false) ∧ x2.eval x10 ≠ x2.eval x11) → (∃ (x11 : Fin x1 → Bool) (x12 : Fin x1 → Bool), x2.eval (List.map (fun (x13 : Option (Fin x1)) => x13.elim Bool.false x11) x3) ≠ x2.eval (List.map (fun (x13 : Option (Fin x1)) => x13.elim Bool.false x12) x3)) → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x12 ∧ x12.size + (x5 + (1 : ℕ)) ≤ x2.size ∧ ∀ (x13 : Fin x1 → Bool), x12.eval (List.ofFn x13) = x2.eval (List.map (fun (x14 : Option (Fin x1)) => x14.elim Bool.false x13) x3) := by
  intro n C p k b hC hp hb hor hs hn
  obtain ⟨D,hD,sz,he⟩ := PEqualNP.Outside.L_meta_3223.extract C p hC hn
  exact ⟨D,hD,by rw [sz]; exact PEqualNP.Outside.L_meta_3223.savedBound C p k b hC hp hb hor hs hn,he⟩
