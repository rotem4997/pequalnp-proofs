import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7328

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The normalizer and wire-evaluation lemmas are adapted from L_meta_1411
-- in open-goat/pequalnp-proofs under the Apache 2.0 license.
abbrev Stat := Bool ⊕ ℕ

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
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
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]
def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg; subst hg; simp [Ok]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg; subst hg; simp [Ok]
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg; subst hg; simp [Ok]
  · simp at hg
  · simp at hg

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
    · cases a <;> cases b <;> (rename_i c e; cases c) <;> cases e <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (rename_i c e; cases c) <;> cases e <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

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
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

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
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
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
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2
def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

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
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)[p]? = some g' := hp
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

def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => Sum.inr i)

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
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y)) = f y := by
    intro y
    rw [((hinv y).2 C.output).2, ← hev y]; rfl
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | inr j =>
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

def vl {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) : Bool :=
  (wiresFrom gs (List.ofFn u)).getD j false

theorem vl_input {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) (h : j < k) :
    vl gs u j = u ⟨j, h⟩ := by
  unfold vl
  rw [getD_wiresFrom gs _ j (by simpa using h)]
  exact getD_ofFn k u false ⟨j, h⟩

theorem vl_gate {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) :
    vl gs u (k + p) = g.op.eval (g.inputs.map (vl gs u)) := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hwl : (wiresFrom pre (List.ofFn u)).length = k + pre.length := by
    rw [length_wiresFrom]; simp
  have e : wiresFrom (pre ++ g :: post) (List.ofFn u)
      = wiresFrom post (wiresFrom pre (List.ofFn u) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have full : ∀ j, j < k + pre.length →
      (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false
        = (wiresFrom pre (List.ofFn u)).getD j false := by
    intro j hj
    rw [e, getD_wiresFrom _ _ j (by simp [hwl]; omega), getD_snoc_ne _ _ _ _ (by omega)]
  have top : (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
      = g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false) := by
    rw [e, getD_wiresFrom _ _ _ (by simp [hwl]), getD_snoc_len _ _ _ _ hwl]
  show (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
    = g.op.eval (g.inputs.map fun j => (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false)
  rw [top]
  congr 1
  apply List.map_congr_left
  intro a ha
  exact (full a (hlt a ha)).symm

theorem vl_congr {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) (h : ∀ a ∈ g.inputs, vl gs u a = vl gs u' a) :
    vl gs u (k + p) = vl gs u' (k + p) := by
  rw [vl_gate gs hcl u p g hp, vl_gate gs hcl u' p g hp]
  congr 1
  exact List.map_congr_left h
theorem drop_core (k : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (hcl : CleanL k (pre ++ g :: post)) (o : ℕ) (S : Stat)
    (hS : ∀ y : Fin k → Bool, S.Valid (k + (elim k pre (idStats k, [])).2.length) ∧
      S.val (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y))
        = vl (pre ++ g :: post) y (k + pre.length))
    (hnc : ∃ y y' : Fin k → Bool, vl (pre ++ g :: post) y o ≠ vl (pre ++ g :: post) y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ (pre ++ g :: post).length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl (pre ++ g :: post) y o := by
  have hok : ∀ g' ∈ pre ++ g :: post, Ok g' := fun g' hg' => (clean_nok _ _ hcl g' hg').1
  have hokpre : ∀ g' ∈ pre, Ok g' := fun g' h => hok g' (List.mem_append_left _ h)
  have hokpost : ∀ g' ∈ post, Ok g' :=
    fun g' h => hok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have inv1 : ∀ y : Fin k → Bool, Inv k (List.ofFn y) (wiresFrom pre (List.ofFn y))
      (elim k pre (idStats k, [])) :=
    fun y => inv_elim k _ (by simp) pre _ _ hokpre (inv_id k y)
  have hwl : ∀ y : Fin k → Bool, (wiresFrom pre (List.ofFn y)).length = k + pre.length := by
    intro y; rw [length_wiresFrom]; simp
  have hfull : ∀ y : Fin k → Bool, wiresFrom (pre ++ g :: post) (List.ofFn y)
      = wiresFrom post (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)]) := by
    intro y; rw [wiresFrom_append]; rfl
  have hgv : ∀ y : Fin k → Bool, vl (pre ++ g :: post) y (k + pre.length)
      = g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false) := by
    intro y
    show (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD (k + pre.length) false = _
    rw [hfull, getD_wiresFrom _ _ _ (by simp [hwl y]), getD_snoc_len _ _ _ _ (hwl y)]
  have inv2 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)])
      ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2) := by
    intro y
    obtain ⟨hl, hi⟩ := inv1 y
    refine ⟨by simp [hl], ?_⟩
    intro a
    show (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Sum.inl false)).Valid
        (k + (elim k pre (idStats k, [])).2.length) ∧
      (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Sum.inl false)).val
        (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y)) = _
    by_cases hal : a = (elim k pre (idStats k, [])).1.length
    · rw [hal, getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨(hS y).1, by rw [(hS y).2, hgv]⟩
    · rw [getD_snoc_ne _ _ _ _ hal, getD_snoc_ne _ _ _ _ (by omega)]
      exact hi a
  have inv3 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom (pre ++ g :: post) (List.ofFn y))
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)) := by
    intro y
    rw [hfull]
    exact inv_elim k _ (by simp) post _ _ hokpost (inv2 y)
  have hc1 : CleanL k (elim k pre (idStats k, [])).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) pre _ _ hokpre (inv_id k _)
      (by intro p g' hp; simp at hp)
  have hc3 : CleanL k
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) post _ _ hokpost (inv2 _) hc1
  have hlen : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).2.length + 1 ≤ (pre ++ g :: post).length := by
    have h1 : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
        (elim k pre (idStats k, [])).2)).2.length
        ≤ (elim k pre (idStats k, [])).2.length + post.length := elim_len k post _
    have h2 : (elim k pre (idStats k, [])).2.length ≤ 0 + pre.length :=
      elim_len k pre (idStats k, [])
    simp only [List.length_append, List.length_cons]
    omega
  have hval : ∀ y : Fin k → Bool,
      ((elim k post ((elim k pre (idStats k, [])).1 ++ [S],
        (elim k pre (idStats k, [])).2)).1.getD o (Sum.inl false)).val
        (wiresFrom (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
          (elim k pre (idStats k, [])).2)).2 (List.ofFn y))
      = vl (pre ++ g :: post) y o := fun y => ((inv3 y).2 o).2
  cases hst : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).1.getD o (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]
    rfl
  | inr j =>
    refine ⟨_, j, hc3, hlen, ?_⟩
    intro y
    have h := hval y
    rw [hst] at h
    exact h

theorem drop_alias (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p j : ℕ) (hp : p < gs.length)
    (hj : j < k + p) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = vl gs y j)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  apply drop_core k pre g post hcl o ((elim k pre (idStats k, [])).1.getD j (Sum.inl false))
    ?_ hnc
  intro y
  have hokpre : ∀ g' ∈ pre, Ok g' :=
    fun g' h => (clean_nok _ _ hcl g' (List.mem_append_left _ h)).1
  have inv1 := inv_elim k (List.ofFn y) (by simp) pre _ _ hokpre (inv_id k y)
  refine ⟨(inv1.2 j).1, ?_⟩
  rw [(inv1.2 j).2, heq y]
  show (wiresFrom pre (List.ofFn y)).getD j false
    = (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD j false
  rw [wiresFrom_append, getD_wiresFrom (g :: post) (wiresFrom pre (List.ofFn y)) j
    (by rw [length_wiresFrom]; simp; omega)]
def Reads (gs : List Gate) (p w : ℕ) : Prop := ∃ g, gs[p]? = some g ∧ w ∈ g.inputs
theorem reads_lt {k : ℕ} {gs : List Gate} (hcl : CleanL k gs) {q w : ℕ} (h : Reads gs q w) :
    w < k + q := by
  obtain ⟨g, hg, hw⟩ := h
  exact (hcl q g hg).lt w hw

theorem reads_len {gs : List Gate} {q w : ℕ} (h : Reads gs q w) : q < gs.length := by
  obtain ⟨g, hg, _⟩ := h
  exact (List.getElem?_eq_some_iff.1 hg).1

theorem vl_beyond {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (w : ℕ) (h : k + gs.length ≤ w) :
    vl gs u w = false := by
  unfold vl
  exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)
theorem drop_dead (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ) (hp : p < gs.length)
    (ho : o ≠ k + p) (hno : ∀ q, ¬ Reads gs q (k + p))
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  have hpos : 0 < k + p := by
    rcases hcl p g hg with ⟨_, j, hj, _⟩ | ⟨_, j, _, hj, _, _⟩ <;> omega
  let g0 : Gate := ⟨GateOp.and, [0, 0]⟩
  let gs' := gs.set p g0
  have hlen : gs'.length = gs.length := by simp [gs']
  have hget_p : gs'[p]? = some g0 := by simp [gs', hp]
  have hget_ne : ∀ r, r ≠ p → gs'[r]? = gs[r]? := by
    intro r hr
    simp [gs', Ne.symm hr]
  have hcl' : CleanL k gs' := by
    intro r g' hr'
    by_cases hrp : r = p
    · subst hrp
      rw [hget_p] at hr'
      cases hr'
      exact Or.inr ⟨Or.inl rfl, 0, 0, hpos, hpos, rfl⟩
    · rw [hget_ne r hrp] at hr'
      exact hcl r g' hr'
  have hagree : ∀ y : Fin k → Bool, ∀ w, w ≠ k + p → vl gs' y w = vl gs y w := by
    intro y w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases hwk : w < k
      · rw [vl_input gs' y w hwk, vl_input gs y w hwk]
      · obtain ⟨r, rfl⟩ : ∃ r, w = k + r := ⟨w - k, by omega⟩
        have hrp : r ≠ p := fun e => hw (by rw [e])
        cases hr : gs[r]? with
        | none =>
          have hl : gs.length ≤ r := List.getElem?_eq_none_iff.1 hr
          rw [vl_beyond gs' y _ (by omega), vl_beyond gs y _ (by omega)]
        | some g' =>
          have hr' : gs'[r]? = some g' := by rw [hget_ne r hrp]; exact hr
          rw [vl_gate gs' hcl' y r g' hr', vl_gate gs hcl y r g' hr]
          congr 1
          apply List.map_congr_left
          intro a ha
          have hlt := (hcl r g' hr).lt a ha
          exact ih a hlt (fun e => hno r ⟨g', hr, e ▸ ha⟩)
  have halias : ∀ y : Fin k → Bool, vl gs' y (k + p) = vl gs' y 0 := by
    intro y
    rw [vl_gate gs' hcl' y p g0 hget_p]
    simp [g0, GateOp.eval]
  have hnc' : ∃ y y' : Fin k → Bool, vl gs' y o ≠ vl gs' y' o := by
    obtain ⟨y, y', h⟩ := hnc
    exact ⟨y, y', by rw [hagree y o ho, hagree y' o ho]; exact h⟩
  obtain ⟨gs'', o'', hc'', hl'', he''⟩ :=
    drop_alias k gs' hcl' o p 0 (by omega) hpos halias hnc'
  exact ⟨gs'', o'', hc'', by omega, fun y => by rw [he'' y, hagree y o ho]⟩

abbrev Vertex := Fin 9

def target (x : Vertex → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
    x 5 && x 7 || x 6 && x 8 || x 8 && x 5

def adj (a b : Vertex) : Bool :=
  ([(0,1), (1,2), (2,3), (3,4), (4,0), (0,5), (1,6), (2,7), (3,8),
    (5,7), (6,8), (8,5)] : List (Vertex × Vertex)).contains (a,b) ||
    ([(0,1), (1,2), (2,3), (3,4), (4,0), (0,5), (1,6), (2,7), (3,8),
    (5,7), (6,8), (8,5)] : List (Vertex × Vertex)).contains (b,a)

def bits (l : List Vertex) (u : Vertex) : Bool := l.contains u

lemma target_nil : target (bits []) = false := rfl

lemma target_single : ∀ u : Vertex, target (bits [u]) = false := by decide +kernel

lemma target_pair : ∀ u v : Vertex, target (bits [u,v]) = adj u v := by decide +kernel

lemma has_neighbor : ∀ u : Vertex, ∃ v : Vertex, u ≠ v ∧ adj u v = true := by
  decide +kernel

lemma adj_symm (u v : Vertex) : adj u v = adj v u := by
  simp only [adj, Bool.or_comm]

lemma adj_ne : ∀ u v : Vertex, adj u v = true → u ≠ v := by decide +kernel

lemma essential (u : Vertex) :
    ∃ x y : Vertex → Bool, (∀ v, v ≠ u → x v = y v) ∧ target x ≠ target y := by
  obtain ⟨v, _, h⟩ := has_neighbor u
  refine ⟨bits [v], bits [u,v], ?_, ?_⟩
  · intro i hi
    simp [bits, hi]
  · rw [target_single, target_pair, h]
    decide

def ports (gs : List Gate) : List ℕ := gs.flatMap Gate.inputs

lemma mem_ports {gs : List Gate} {w : ℕ} :
    w ∈ ports gs ↔ ∃ p, Reads gs p w := by
  simp only [ports, List.mem_flatMap, Reads]
  constructor
  · rintro ⟨g, hg, hw⟩
    obtain ⟨p, hp⟩ := List.mem_iff_getElem?.mp hg
    exact ⟨p,g,hp,hw⟩
  · rintro ⟨p,g,hp,hw⟩
    exact ⟨g,List.mem_iff_getElem?.mpr ⟨p,hp⟩,hw⟩

lemma agreement_without_read {gs : List Gate} (hc : CleanL 9 gs) (u : Vertex)
    (hn : (u : ℕ) ∉ ports gs) (x y : Vertex → Bool) (hxy : ∀ v, v ≠ u → x v = y v) :
    ∀ w, w ≠ (u : ℕ) → vl gs x w = vl gs y w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hi : w < 9
    · rw [vl_input gs x w hi, vl_input gs y w hi]
      exact hxy _ (fun e => hw (congrArg Fin.val e))
    by_cases hb : 9 + gs.length ≤ w
    · rw [vl_beyond gs x w hb, vl_beyond gs y w hb]
    let p := w - 9
    have hp : p < gs.length := by dsimp [p]; omega
    have hwp : w = 9 + p := by dsimp [p]; omega
    have hg : gs[p]? = some gs[p] := List.getElem?_eq_getElem hp
    rw [hwp]
    apply vl_congr gs hc x y p _ hg
    intro t ht
    exact ih _ (by rw [hwp]; exact (hc p _ hg).lt t ht)
      (fun e => hn (mem_ports.mpr ⟨p,_,hg,e ▸ ht⟩))

lemma output_is_gate {gs : List Gate} {o : ℕ} (h : ∀ x, vl gs x o = target x) :
    9 ≤ o ∧ o < 9 + gs.length := by
  constructor
  · by_contra! ho
    let v : Vertex := ⟨o,ho⟩
    let u : Vertex := v + 1
    have huv : v ≠ u := by
      exact (show ∀ x : Vertex, x ≠ x + 1 by decide +kernel) v
    obtain ⟨x,y,hxy,hn⟩ := essential u
    apply hn
    rw [← h, ← h, vl_input gs x o ho, vl_input gs y o ho]
    exact hxy v huv
  · by_contra! ho
    have ht := h (bits [0,1])
    rw [vl_beyond gs _ _ ho, target_pair] at ht
    contradiction

lemma arity_count {gs : List Gate} (hc : CleanL 9 gs) :
    (ports gs).length + (gs.countP fun g => g.inputs.length == 1) = 2 * gs.length := by
  have all : ∀ g ∈ gs, g.inputs.length = 1 ∨ g.inputs.length = 2 := by
    intro g hg
    obtain ⟨p,hp⟩ := List.mem_iff_getElem?.mp hg
    rcases hc p g hp with ⟨_,_,_,hh⟩ | ⟨_,_,_,_,_,hh⟩ <;> simp [hh]
  clear hc
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have tail := ih (fun g' h => all g' (List.mem_cons_of_mem _ h))
    rcases all g List.mem_cons_self with h | h <;>
      simp [ports, h] at tail ⊢ <;> omega

lemma repeat_le_extra (l : List ℕ) :
    (l.toFinset.filter fun w => 2 ≤ l.count w).card ≤ l.length - l.toFinset.card := by
  classical
  have h := List.sum_toFinset_count_eq_length l
  have hle : ∑ w ∈ l.toFinset, (1 + if 2 ≤ l.count w then 1 else 0) ≤
      ∑ w ∈ l.toFinset, l.count w := by
    apply Finset.sum_le_sum
    intro w hw
    have hp : 0 < l.count w := List.count_pos_iff.mpr (List.mem_toFinset.mp hw)
    split_ifs <;> omega
  rw [h, Finset.sum_add_distrib] at hle
  rw [← Finset.sum_filter] at hle
  simp at hle
  omega

-- A smallest normalized circuit has a gate at its output and no unused gates.
lemma normalized (C : Circuit) (hf : FanInTwo C) (hs : circuitFun 9 C = target) :
    ∃ gs : List Gate, ∃ o : ℕ, CleanL 9 gs ∧ gs.length ≤ C.size ∧
      (∀ x, vl gs x o = target x) ∧ o = 8 + gs.length ∧
      (ports gs).toFinset = Finset.range (8 + gs.length) := by
  classical
  have hn : ∃ x y : Vertex → Bool, target x ≠ target y := by
    obtain ⟨x,y,_,h⟩ := essential 0
    exact ⟨x,y,h⟩
  have hC : HasClean 9 target C.size := clean_of _ _ _ hn
    ⟨C,hf,le_rfl,fun x => congrFun hs x⟩
  have ex : ∃ s, HasClean 9 target s := ⟨_,hC⟩
  obtain ⟨gs,o,hc,hsize,hval⟩ := Nat.find_spec ex
  change ∀ x : Vertex → Bool, vl gs x o = target x at hval
  have hbudget := Nat.find_min' ex hC
  have houtput := output_is_gate hval
  have hfull : ∀ p < gs.length, o ≠ 9 + p → (9 + p) ∈ ports gs := by
    intro p hp hne
    by_contra hm
    have hnc : ∃ x y : Vertex → Bool, vl gs x o ≠ vl gs y o := by
      obtain ⟨x,y,h⟩ := hn
      exact ⟨x,y,by rw [hval, hval]; exact h⟩
    obtain ⟨gs',o',hc',hlt,he⟩ := drop_dead 9 gs hc o p hp hne
      (fun q hq => hm (mem_ports.mpr ⟨q,hq⟩)) hnc
    have hm' := Nat.find_min' ex (show HasClean 9 target gs'.length from
      ⟨gs',o',hc',le_rfl,fun x => (he x).trans (hval x)⟩)
    omega
  have hlast : o = 8 + gs.length := by
    by_contra hn'
    have hpos : 0 < gs.length := by omega
    obtain ⟨q,hq⟩ := mem_ports.mp (hfull (gs.length-1) (by omega) (by omega))
    have hlt := reads_lt hc hq
    have hq' := reads_len hq
    omega
  refine ⟨gs,o,hc,by omega,hval,hlast,?_⟩
  ext w
  simp only [List.mem_toFinset, Finset.mem_range]
  constructor
  · intro hw
    obtain ⟨q,hq⟩ := mem_ports.mp hw
    have hlt := reads_lt hc hq
    have hq' := reads_len hq
    omega
  · intro hw
    by_cases hi : w < 9
    · let u : Vertex := ⟨w,hi⟩
      by_contra hn'
      obtain ⟨x,y,hxy,hne⟩ := essential u
      exact hne (by
        rw [← hval, ← hval]
        exact agreement_without_read hc u hn' x y hxy o (by dsimp [u]; omega))
    · let p := w - 9
      have hp : p < gs.length := by dsimp [p]; omega
      have hw' : w = 9 + p := by dsimp [p]; omega
      rw [hw']
      exact hfull p hp (by omega)

abbrev Use (gs : List Gate) (w t : ℕ) : Prop :=
  ∃ p, t = 9 + p ∧ Reads gs p w

-- A wire with one read has a unique next gate, so its path can be followed until it branches.
def Link (gs : List Gate) (w t : ℕ) : Prop :=
  (ports gs).count w = 1 ∧ Use gs w t

abbrev Path (gs : List Gate) := Relation.ReflTransGen (Link gs)

lemma reads_count {gs : List Gate} {p w : ℕ} (h : Reads gs p w) :
    0 < (ports gs).count w :=
  List.count_pos_iff.mpr (mem_ports.mpr ⟨_,h⟩)

lemma read_unique {gs : List Gate} {p q w : ℕ} (h : (ports gs).count w = 1)
    (hp : Reads gs p w) (hq : Reads gs q w) : p = q := by
  induction gs generalizing p q with
  | nil => obtain ⟨g,hg,_⟩ := hp; simp at hg
  | cons g gs ih =>
    have hs : (ports (g :: gs)).count w = g.inputs.count w + (ports gs).count w := by
      simp [ports, List.count_append]
    cases p <;> cases q
    · rfl
    · obtain ⟨a,ha,hw⟩ := hp
      obtain ⟨b,hb,hw'⟩ := hq
      simp at ha hb
      subst a
      have h1 := List.count_pos_iff.mpr hw
      have h2 := reads_count (show Reads gs _ w from ⟨b,hb,hw'⟩)
      omega
    · obtain ⟨a,ha,hw⟩ := hp
      obtain ⟨b,hb,hw'⟩ := hq
      simp at ha hb
      subst b
      have h1 := reads_count (show Reads gs _ w from ⟨a,ha,hw⟩)
      have h2 := List.count_pos_iff.mpr hw'
      omega
    · obtain ⟨a,ha,hw⟩ := hp
      obtain ⟨b,hb,hw'⟩ := hq
      simp at ha hb
      have hp' : Reads gs _ w := ⟨a,ha,hw⟩
      have hq' : Reads gs _ w := ⟨b,hb,hw'⟩
      have hc := reads_count hp'
      exact congrArg Nat.succ (ih (by omega) hp' hq')

lemma link_unique {gs : List Gate} {w a b : ℕ} (ha : Link gs w a) (hb : Use gs w b) :
    a = b := by
  obtain ⟨h, p, rfl, hp⟩ := ha
  obtain ⟨q,rfl,hq⟩ := hb
  rw [read_unique h hp hq]

lemma use_lt {gs : List Gate} (hc : CleanL 9 gs) {a b : ℕ} (h : Use gs a b) : a < b := by
  obtain ⟨p,rfl,hp⟩ := h
  exact reads_lt hc hp

lemma path_le {gs : List Gate} (hc : CleanL 9 gs) {a b : ℕ} (h : Path gs a b) : a ≤ b := by
  induction h with
  | refl => rfl
  | tail _ he ih => exact ih.trans (use_lt hc he.2).le

lemma path_from_input {gs : List Gate} {a b : ℕ} (h : Path gs a b) (hb : b < 9) :
    a = b := by
  rcases h.cases_tail with h | ⟨_,_,_,p,e,_⟩
  · exact h.symm
  · omega

lemma path_compare {gs : List Gate} {a b c : ℕ} (hab : Path gs a b) (hac : Path gs a c) :
    Path gs b c ∨ Path gs c b := by
  induction hab using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl hac
  | head hstep htail ih =>
    rcases hac.cases_head with rfl | ⟨_,hstep',htail'⟩
    · exact Or.inr (Relation.ReflTransGen.head hstep htail)
    · have e := link_unique hstep hstep'.2
      cases e
      exact ih htail'

lemma path_source_single {gs : List Gate} {a b : ℕ} (h : Path gs a b) (hne : a ≠ b) :
    (ports gs).count a = 1 := by
  rcases h.cases_head with he | ⟨_,hs,_⟩
  · exact (hne he).elim
  · exact hs.1

lemma path_cut {gs : List Gate} {v r w : ℕ} (hv : Path gs v r) (hne : v ≠ r)
    (hw : Use gs v w) : Path gs w r := by
  rcases hv.cases_head with e | ⟨t,ht,hr⟩
  · exact (hne e).elim
  · rwa [← link_unique ht hw]

lemma path_before {gs : List Gate} (hc : CleanL 9 gs) {a b t : ℕ}
    (hab : Path gs a b) (hat : Path gs a t) (hbt : b < t) : Path gs b t := by
  rcases path_compare hab hat with h | h
  · exact h
  · exact (Nat.not_le_of_gt hbt (path_le hc h)).elim

-- Once two runs agree at the cut wire, differences inside its path group cannot reach other wires.
lemma cut_agree {gs : List Gate} (hc : CleanL 9 gs) (r : ℕ) (x y : Vertex → Bool)
    (hi : ∀ u : Vertex, ¬ Path gs u.val r → x u = y u) (hr : vl gs x r = vl gs y r) :
    ∀ w, ¬ Path gs w r → vl gs x w = vl gs y w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases wi : w < 9
    · rw [vl_input gs x w wi, vl_input gs y w wi]
      exact hi ⟨w,wi⟩ hw
    by_cases wb : 9 + gs.length ≤ w
    · rw [vl_beyond gs x w wb, vl_beyond gs y w wb]
    let p := w - 9
    have hp : p < gs.length := by dsimp [p]; omega
    have wp : w = 9 + p := by dsimp [p]; omega
    have hg : gs[p]? = some gs[p] := List.getElem?_eq_getElem hp
    rw [wp]
    apply vl_congr gs hc x y _ _ hg
    intro z hz
    by_cases eq : z = r
    · rwa [eq]
    · apply ih z (by rw [wp]; exact (hc p _ hg).lt _ hz)
      intro h
      exact hw (path_cut h eq ⟨p,wp,_,hg,hz⟩)

lemma path_terminal {gs : List Gate} {o : ℕ} (hc : CleanL 9 gs)
    (ho : o = 8 + gs.length) (hpins : (ports gs).toFinset = Finset.range o) :
    ∀ w ≤ o, ∃ r, Path gs w r ∧ r ≤ o ∧ (o = r ∨ 2 ≤ (ports gs).count r) := by
  have claim : ∀ d w, o - w = d → w ≤ o →
      ∃ r, Path gs w r ∧ r ≤ o ∧ (o = r ∨ 2 ≤ (ports gs).count r) := by
    intro d
    induction d using Nat.strong_induction_on with
    | ind d ih =>
      intro w hd hw
      by_cases e : w = o
      · exact ⟨w,.refl,hw,Or.inl e.symm⟩
      by_cases h : 2 ≤ (ports gs).count w
      · exact ⟨w,.refl,hw,Or.inr h⟩
      have hm : w ∈ ports gs := by
        apply List.mem_toFinset.mp
        rw [hpins, Finset.mem_range]
        omega
      obtain ⟨p,hp⟩ := mem_ports.mp hm
      have hu : Use gs w (9+p) := ⟨p,rfl,hp⟩
      have hl := use_lt hc hu
      have hpl := reads_len hp
      have hob : 9 + p ≤ o := by omega
      obtain ⟨r,hpr,hr,ht⟩ := ih (o-(9+p)) (by omega) _ rfl hob
      exact ⟨r,.head ⟨by have := reads_count hp; omega,hu⟩ hpr,hr,ht⟩
  intro w hw
  exact claim _ _ rfl hw

def Only (u : Vertex) (x y : Vertex → Bool) : Prop := ∀ v, v ≠ u → x v = y v

lemma no_dep_early {gs : List Gate} (hc : CleanL 9 gs) {u : Vertex} {m : ℕ}
    (hm : Path gs u.val m) {x y : Vertex → Bool} (hxy : Only u x y) :
    ∀ w < m, ¬ Path gs u.val w → vl gs x w = vl gs y w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwm hw
    by_cases wi : w < 9
    · rw [vl_input gs x w wi, vl_input gs y w wi]
      apply hxy
      intro e
      have ev := congrArg Fin.val e
      change w = u.val at ev
      exact hw (by rw [ev])
    by_cases wb : 9 + gs.length ≤ w
    · rw [vl_beyond gs x w wb, vl_beyond gs y w wb]
    let p := w - 9
    have hp : p < gs.length := by dsimp [p]; omega
    have wp : w = 9 + p := by dsimp [p]; omega
    have hg : gs[p]? = some gs[p] := List.getElem?_eq_getElem hp
    rw [wp]
    apply vl_congr gs hc x y _ _ hg
    intro z hz
    have hzlt : z < w := by rw [wp]; exact (hc p _ hg).lt _ hz
    apply ih z hzlt (hzlt.trans hwm)
    intro hr
    have hzm := hzlt.trans hwm
    have h1 := path_source_single (path_before hc hr hm hzm) hzm.ne
    exact hw (.tail hr ⟨h1,p,wp,_,hg,hz⟩)

lemma predecessor_unique {gs : List Gate} (hc : CleanL 9 gs) {u a b w : ℕ}
    (ha : Path gs u a) (hb : Path gs u b) (hwa : Use gs a w) (hwb : Use gs b w) :
    a = b := by
  have conflict (i j : ℕ) (hp : Path gs i j) (hu : Use gs i w) (hj : j < w) : i = j := by
    rcases hp.cases_head with e | ⟨t,ht,hj'⟩
    · exact e
    · have e := link_unique ht hu
      have := path_le hc hj'
      omega
  rcases path_compare ha hb with h | h
  · exact conflict a b h hwa (use_lt hc hwb)
  · exact (conflict b a h hwb (use_lt hc hwa)).symm

def bin (isAnd a b : Bool) : Bool := if isAnd then a && b else a || b

lemma bin_comm (k a b : Bool) : bin k a b = bin k b a := by
  cases k <;> simp [bin, Bool.and_comm, Bool.or_comm]

lemma bin_change : ∀ (k a a' b : Bool), bin k a b ≠ bin k a' b →
    a ≠ a' ∧ bin k a b = a := by decide +kernel

lemma same_pin (k a : Bool) : bin k a a = a := by cases k <;> simp [bin]

lemma binary_op {g : Gate} (h : g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∃ k : Bool, ∀ a b, g.op.eval [a,b] = bin k a b := by
  rcases h with h | h
  · exact ⟨true,fun a b => by rw [h]; simp [GateOp.eval, bin]⟩
  · exact ⟨false,fun a b => by rw [h]; simp [GateOp.eval, bin]⟩

-- A change propagated before a merge has a fixed polarity. Other inputs can mask the change.
def Sign (gs : List Gate) (u : Vertex) (w : ℕ) (e : Bool) : Prop :=
  ∀ x y : Vertex → Bool, Only u x y → x u = false → y u = true →
    vl gs x w ≠ vl gs y w → vl gs x w = e

lemma path_sign {gs : List Gate} (hc : CleanL 9 gs) {u : Vertex} {m : ℕ}
    (hm : Path gs u.val m) : ∀ w < m, Path gs u.val w → ∃ e, Sign gs u w e := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwm hw
    rcases hw.cases_tail with eq | ⟨z,hz,hzw⟩
    · refine ⟨false,fun x y _ hx _ _ => ?_⟩
      subst w
      rw [vl_input gs x _ u.isLt]
      exact hx
    obtain ⟨_,p,wp,g,hg,hzg⟩ := hzw
    have hzlt : z < w := by rw [wp]; exact (hc p g hg).lt z hzg
    obtain ⟨e,he⟩ := ih z hzlt (hzlt.trans hwm) hz
    rcases hc p g hg with ⟨hop,a,ha,hin⟩ | ⟨hop,a,b,ha,hb,hin⟩
    · have hza : z = a := by simpa [hin] using hzg
      refine ⟨!e,fun x y hxy hx hy hd => ?_⟩
      have form (v : Vertex → Bool) : vl gs v w = !vl gs v z := by
        rw [wp,vl_gate gs hc v p g hg,hin,hop,hza]
        rfl
      rw [form,form] at hd
      rw [form,he x y hxy hx hy (fun hr => hd (by rw [hr]))]
    · obtain ⟨k,hk⟩ := binary_op hop
      have form (v : Vertex → Bool) : vl gs v w = bin k (vl gs v a) (vl gs v b) := by
        rw [wp,vl_gate gs hc v p g hg,hin]
        exact hk _ _
      have pair (a' b' : ℕ) (hza : z = a') (hba : b' < w) (hp' : Use gs b' w)
          (hform : ∀ v : Vertex → Bool, vl gs v w = bin k (vl gs v a') (vl gs v b')) :
          Sign gs u w e := by
        intro x y hxy hx hy hd
        by_cases eq : b' = a'
        · have copied (v : Vertex → Bool) : vl gs v w = vl gs v z := by
            rw [hform,eq,same_pin,hza]
          rw [copied,copied] at hd
          exact (copied x).trans (he x y hxy hx hy hd)
        have hn : ¬ Path gs u.val b' := by
          intro hr
          exact eq ((predecessor_unique hc hz hr ⟨p,wp,g,hg,hzg⟩ hp').symm.trans hza)
        have hs := no_dep_early hc hm hxy b' (hba.trans hwm) hn
        rw [hform,hform,← hza,← hs] at hd
        obtain ⟨hd',hv⟩ := bin_change k _ _ _ hd
        rw [hform,← hza,hv,he x y hxy hx hy hd']
      have hzab : z = a ∨ z = b := by simpa [hin] using hzg
      refine ⟨e,?_⟩
      rcases hzab with hza | hzb
      · exact pair a b hza (by omega) ⟨p,wp,g,hg,by simp [hin]⟩ form
      · exact pair b a hzb (by omega) ⟨p,wp,g,hg,by simp [hin]⟩
          (fun v => (form v).trans (bin_comm _ _ _))

def grid (x : Vertex → Bool) (u v : Vertex) (a b : Bool) (i : Vertex) : Bool :=
  if i = u then a else if i = v then b else x i

lemma grid_left (x : Vertex → Bool) (u v : Vertex) (a a' b : Bool) :
    Only u (grid x u v a b) (grid x u v a' b) := by
  intro i hi
  simp [grid,hi]

lemma grid_right (x : Vertex → Bool) (u v : Vertex) (a b b' : Bool) :
    Only v (grid x u v a b) (grid x u v a b') := by
  intro i hi
  simp [grid,hi]

def Factors (f g : Bool → Bool → Bool) : Prop :=
  ∀ a b c d, f a b = f c d → g a b = g c d

def signed (e a : Bool) : Bool := if a then !e else e

lemma signed_of {f : Bool → Bool} {e : Bool} (h : f false ≠ f true)
    (h' : f false = e) : ∀ a, f a = signed e a := by
  intro a
  cases a
  · exact h'
  · cases e <;> cases htrue : f true <;> simp_all [signed]

lemma opposite_tables : ∀ (k e d : Bool),
    Factors (fun a b => bin k (signed e a) (signed d b)) (· && ·) →
    ¬ Factors (fun a b => bin k (signed e a) (signed d b)) (· || ·) := by
  unfold Factors
  decide +kernel

lemma grid_and : ∀ u v : Vertex, adj u v = true →
    ∀ a b, target (grid (bits []) u v a b) = (a && b) := by decide +kernel

def orWitness (u v : Vertex) : Vertex × Vertex :=
  ([
    (0,0), (4,2), (0,0), (0,0), (1,3), (1,7), (0,0), (0,0), (0,0),
    (2,4), (0,0), (0,3), (0,0), (0,0), (0,0), (0,8), (0,0), (0,0),
    (0,0), (3,0), (0,0), (1,4), (0,0), (0,0), (0,0), (1,5), (0,0),
    (0,0), (0,0), (4,1), (0,0), (2,0), (0,0), (0,0), (0,0), (2,5),
    (3,1), (0,0), (0,0), (0,2), (0,0), (0,0), (0,0), (0,0), (0,0),
    (7,1), (0,0), (0,0), (0,0), (0,0), (0,0), (0,0), (0,2), (0,3),
    (0,0), (8,0), (0,0), (0,0), (0,0), (0,0), (0,0), (0,0), (1,3),
    (0,0), (0,0), (5,1), (0,0), (0,0), (2,0), (0,0), (0,0), (0,0),
    (0,0), (0,0), (0,0), (5,2), (0,0), (3,0), (3,1), (0,0), (0,0)] : List (Vertex × Vertex)).getD (9 * u.val + v.val) (0,0)

lemma grid_or : ∀ u v : Vertex, adj u v = true →
    ∀ a b, target (grid (bits [(orWitness u v).1,(orWitness u v).2]) u v a b) = (a || b) := by
  decide +kernel

lemma meeting_inputs {gs : List Gate} (hc : CleanL 9 gs) {u v : Vertex} {m : ℕ}
    (hne : u ≠ v) (hu : Path gs u.val m) (hv : Path gs v.val m)
    (hfirst : ∀ w < m, Path gs u.val w → ¬ Path gs v.val w) :
    ∃ a b k, a < m ∧ b < m ∧ Path gs u.val a ∧ Path gs v.val b ∧
      ∀ x : Vertex → Bool, vl gs x m = bin k (vl gs x a) (vl gs x b) := by
  have hm : 9 ≤ m := by
    by_contra! hm
    exact hne (Fin.ext ((path_from_input hu hm).trans (path_from_input hv hm).symm))
  obtain e | ⟨a,ha,ha'⟩ := hu.cases_tail
  · have := u.isLt
    omega
  obtain e | ⟨b,hb,hb'⟩ := hv.cases_tail
  · have := v.isLt
    omega
  obtain ⟨_,p,ep,g,hg,hag⟩ := ha'
  obtain ⟨_,q,eq,g',hg',hbg⟩ := hb'
  have hpq : p = q := by omega
  subst q
  rw [hg] at hg'
  cases hg'
  have hal : a < m := by rw [ep]; exact (hc p g hg).lt a hag
  have hbl : b < m := by rw [ep]; exact (hc p g hg).lt b hbg
  have hab : a ≠ b := fun e => hfirst a hal ha (e ▸ hb)
  rcases hc p g hg with ⟨_,i,_,hin⟩ | ⟨hop,i,j,_,_,hin⟩
  · rw [hin] at hag hbg
    simp at hag hbg
    omega
  · obtain ⟨k,hk⟩ := binary_op hop
    refine ⟨a,b,k,hal,hbl,ha,hb,?_⟩
    intro x
    rw [ep,vl_gate gs hc x p g hg,hin]
    change g.op.eval [vl gs x i,vl gs x j] = _
    rw [hk]
    rw [hin] at hag hbg
    simp at hag hbg
    rcases hag with h | h <;> rcases hbg with h' | h'
    · omega
    · rw [h,h']
    · rw [h,h',bin_comm]
    · omega

lemma grid_factor {gs : List Gate} (hc : CleanL 9 gs) {o m : ℕ} (hmo : m ≤ o)
    {u v : Vertex} (hu : Path gs u.val m) (hv : Path gs v.val m)
    (correct : ∀ x, vl gs x o = target x) (x : Vertex → Bool) :
    Factors (fun a b => vl gs (grid x u v a b) m) (fun a b => target (grid x u v a b)) := by
  intro a b c d he
  dsimp only at he ⊢
  rw [← correct, ← correct]
  by_cases e : o = m
  · rwa [e]
  refine cut_agree hc m _ _ ?_ he o ?_
  · intro i hi
    have hiu : i ≠ u := fun e => hi (e ▸ hu)
    have hiv : i ≠ v := fun e => hi (e ▸ hv)
    simp [grid,hiu,hiv]
  · intro h
    exact e (Nat.le_antisymm (path_le hc h) hmo)

lemma grid_read {gs : List Gate} (hc : CleanL 9 gs) {o m : ℕ} {u v : Vertex}
    {a b : ℕ} {k e d : Bool} (hne : u ≠ v) (hu : Path gs u.val m) (hv : Path gs v.val m)
    (ha : a < m) (hb : b < m) (hna : ¬ Path gs v.val a) (hnb : ¬ Path gs u.val b)
    (he : Sign gs u a e) (hd : Sign gs v b d)
    (form : ∀ x : Vertex → Bool, vl gs x m = bin k (vl gs x a) (vl gs x b))
    (hmo : m ≤ o) (correct : ∀ x, vl gs x o = target x)
    (x : Vertex → Bool) (op : Bool)
    (hx : ∀ s t, target (grid x u v s t) = bin op s t) :
    Factors (fun s t => bin k (signed e s) (signed d t)) (bin op) := by
  let A : Bool → Bool := fun s => vl gs (grid x u v s false) a
  let B : Bool → Bool := fun t => vl gs (grid x u v false t) b
  have fmt (s t : Bool) :
      vl gs (grid x u v s t) m = bin k (A s) (B t) := by
    rw [form]
    rw [no_dep_early hc hv (grid_right x u v s t false) a ha hna,
      no_dep_early hc hu (grid_left x u v s false t) b hb hnb]
  have fac := grid_factor hc hmo hu hv correct x
  have f (s t s' t' : Bool) (h : bin k (A s) (B t) = bin k (A s') (B t')) :
      bin op s t = bin op s' t' := by
    simpa only [hx] using fac s t s' t' (by simpa only [fmt] using h)
  let live := op
  have dA : A false ≠ A true := by
    intro h
    have e := f false live true live (by rw [h])
    cases op <;> simp [live,bin] at e
  have dB : B false ≠ B true := by
    intro h
    have e := f live false live true (by rw [h])
    cases op <;> simp [live,bin] at e
  have sA := signed_of dA
    (he _ _ (grid_left x u v false true false) (by simp [grid]) (by simp [grid]) dA)
  have sB := signed_of dB
    (hd _ _ (grid_right x u v false false true) (by simp [grid,Ne.symm hne])
      (by simp [grid,Ne.symm hne]) dB)
  intro s t s' t' h
  apply f
  simpa only [sA,sB] using h

-- For an edge, the two restricted tables AND and OR cannot both pass through the first merge.
lemma commonRootHasNoEdge {gs : List Gate} (hc : CleanL 9 gs) {o r : ℕ} (hro : r ≤ o)
    (correct : ∀ x, vl gs x o = target x) {u v : Vertex} (hu : Path gs u.val r)
    (hv : Path gs v.val r) : adj u v = false := by
  cases hedge : adj u v
  · rfl
  exfalso
  classical
  have ex : ∃ m, Path gs u.val m ∧ Path gs v.val m := ⟨r,hu,hv⟩
  let m := Nat.find ex
  have hm := Nat.find_spec ex
  have hmr := Nat.find_min' ex ⟨hu,hv⟩
  have hfirst : ∀ w < m, Path gs u.val w → ¬ Path gs v.val w := by
    intro w hw hu' hv'
    exact Nat.find_min ex hw ⟨hu',hv'⟩
  have hne := adj_ne u v hedge
  obtain ⟨a,b,k,ha,hb,hua,hvb,form⟩ :=
    meeting_inputs hc hne hm.1 hm.2 hfirst
  obtain ⟨e,he⟩ := path_sign hc hm.1 a ha hua
  obtain ⟨d,hd⟩ := path_sign hc hm.2 b hb hvb
  have read := grid_read hc hne hm.1 hm.2 ha hb (hfirst a ha hua)
    (fun h => hfirst b hb h hvb) he hd form (hmr.trans hro) correct
  exact opposite_tables k e d
    (read (bits []) true (grid_and u v hedge))
    (read (bits [(orWitness u v).1,(orWitness u v).2]) false (grid_or u v hedge))

lemma agree_after_later_input {gs : List Gate} (hc : CleanL 9 gs) {o : ℕ} (R : Vertex → ℕ)
    (path : ∀ u, Path gs u.val (R u)) (correct : ∀ x, vl gs x o = target x) {r : ℕ}
    (hro : r < o) (hr : 2 ≤ (ports gs).count r) {e : Vertex} (he : r < R e)
    (l₁ l₂ : List Vertex) (hl : ∀ u ∈ l₁ ++ l₂, R u = r)
    (h : vl gs (bits l₁) r = vl gs (bits l₂) r) :
    target (bits (e :: l₁)) = target (bits (e :: l₂)) := by
  have noPath : ¬ Path gs e.val r := by
    intro hp
    have hsingle := path_source_single (path_before hc hp (path e) he) he.ne
    omega
  have keep (l : List Vertex) :
      vl gs (bits (e :: l)) r = vl gs (bits l) r := by
    apply no_dep_early hc (path e) _ r he noPath
    intro v hv
    simp [bits,hv]
  rw [← correct, ← correct]
  refine cut_agree hc r _ _ ?_ (by rw [keep, keep]; exact h) o ?_
  · intro u hu
    have hn₁ : u ∉ l₁ := fun hm => hu (by
      rw [← hl u (List.mem_append_left _ hm)]
      exact path u)
    have hn₂ : u ∉ l₂ := fun hm => hu (by
      rw [← hl u (List.mem_append_right _ hm)]
      exact path u)
    simp [bits,hn₁,hn₂]
  · intro h
    exact hro.not_ge (path_le hc h)

-- Three distinct residual functions cannot be transmitted through one Boolean wire.
lemma equal_later_neighbors {gs : List Gate} (hc : CleanL 9 gs) {o : ℕ} (R : Vertex → ℕ)
    (path : ∀ u, Path gs u.val (R u)) (correct : ∀ x, vl gs x o = target x) {r : ℕ}
    (hro : r < o) (hr : 2 ≤ (ports gs).count r)
    {a b c d : Vertex} (ha : R a = r) (hb : R b = r)
    (hc' : r < R c) (hd : r < R d) (hac : adj a c = true) (hbd : adj b d = true) :
    ∀ e, r < R e → adj a e = adj b e := by
  let value (l : List Vertex) := vl gs (bits l) r
  have distinguish (u v : Vertex) (hu : R u = r) (hv : r < R v)
      (huv : adj u v = true) : value [] ≠ value [u] := by
    intro h
    have hcontr := agree_after_later_input hc R path correct hro hr hv [] [u] (by simpa using hu) h
    rw [target_single, target_pair, adj_symm v u, huv] at hcontr
    contradiction
  have ha' := distinguish a c ha hc' hac
  have hb' := distinguish b d hb hd hbd
  have eq : value [a] = value [b] := by
    generalize value [] = x at ha' hb'
    generalize value [a] = y at ha' ⊢
    generalize value [b] = z at hb' ⊢
    cases x <;> cases y <;> cases z <;> simp_all
  intro e he
  have hh : ∀ u ∈ [a] ++ [b], R u = r := by
    intro u hu
    simp at hu
    rcases hu with rfl | rfl <;> assumption
  have h := agree_after_later_input hc R path correct hro hr he [a] [b] hh eq
  rw [target_pair, target_pair, adj_symm e a, adj_symm e b] at h
  exact h

set_option maxHeartbeats 2000000 in
lemma square_free : ∀ a b c d : Vertex, a ≠ b → c ≠ d →
    adj a c = true → adj b c = true → adj a d = true → adj b d = true → False := by
  decide +kernel

-- Equal nonempty neighborhoods with two distinct sources share at most one later vertex.
lemma later_star {gs : List Gate} (hc : CleanL 9 gs) {o : ℕ} (R : Vertex → ℕ)
    (path : ∀ u, Path gs u.val (R u)) (correct : ∀ x, vl gs x o = target x) {r : ℕ}
    (hro : r < o) (hr : 2 ≤ (ports gs).count r) :
    ∃ v : Vertex, ∀ a b : Vertex, R a = r → r < R b → adj a b = true → a = v ∨ b = v := by
  classical
  by_cases first : ∃ a b : Vertex, R a = r ∧ r < R b ∧ adj a b = true
  · obtain ⟨a,b,ha,hb,hab⟩ := first
    by_cases second : ∃ c d : Vertex, R c = r ∧ r < R d ∧ adj c d = true ∧ c ≠ a
    · obtain ⟨c,d,hc',hd,hcd,hca⟩ := second
      have same := equal_later_neighbors hc R path correct hro hr ha hc' hb hd hab hcd
      refine ⟨b,fun u v hu hv huv => Or.inr ?_⟩
      have h1 := equal_later_neighbors hc R path correct hro hr hu ha hv hb huv hab v hv
      rw [huv] at h1
      have h2 := same b hb
      have h3 := same v hv
      by_contra hne
      exact square_free a c b v (Ne.symm hca) (Ne.symm hne) hab (h2.symm.trans hab)
        h1.symm (h3.symm.trans h1.symm)
    · refine ⟨a,fun u v hu hv huv => Or.inl ?_⟩
      by_contra hne
      exact second ⟨u,v,hu,hv,huv,hne⟩
  · exact ⟨0,fun a b ha hb hab => (first ⟨a,b,ha,hb,hab⟩).elim⟩

set_option maxHeartbeats 2000000 in
lemma cover_lower : ∀ V : Finset Vertex,
    (∀ a b : Vertex, adj a b = true → a ∈ V ∨ b ∈ V) → 5 ≤ V.card := by
  have h : ∀ V : Finset Vertex,
      ((0 ∈ V ∨ 1 ∈ V) ∧ (1 ∈ V ∨ 2 ∈ V) ∧ (2 ∈ V ∨ 3 ∈ V) ∧
       (3 ∈ V ∨ 4 ∈ V) ∧ (4 ∈ V ∨ 0 ∈ V) ∧ (5 ∈ V ∨ 7 ∈ V) ∧ (6 ∈ V ∨ 8 ∈ V)) →
      5 ≤ V.card := by decide +kernel
  intro V hV
  exact h V ⟨hV 0 1 rfl,hV 1 2 rfl,hV 2 3 rfl,hV 3 4 rfl,hV 4 0 rfl,
    hV 5 7 rfl,hV 6 8 rfl⟩

-- Each edge goes between two path endpoints. Its earlier endpoint pays for one cover vertex.
lemma five_repeated {gs : List Gate} (hc : CleanL 9 gs) {o : ℕ}
    (hval : ∀ x, vl gs x o = target x) (ho : o = 8 + gs.length)
    (hpins : (ports gs).toFinset = Finset.range o) :
    5 ≤ ((ports gs).toFinset.filter fun w => 2 ≤ (ports gs).count w).card := by
  classical
  have hbound := (output_is_gate hval).1
  choose R path ro term using fun u : Vertex =>
    path_terminal hc ho hpins u.val (by have := u.isLt; omega)
  let forks := (ports gs).toFinset.filter fun w => 2 ≤ (ports gs).count w
  have stars : ∀ r : ℕ, ∃ v : Vertex, ∀ a b : Vertex,
      R a = r → r < R b → adj a b = true → a = v ∨ b = v := by
    intro r
    by_cases h : r < o ∧ 2 ≤ (ports gs).count r
    · exact later_star hc R path hval h.1 h.2
    · refine ⟨0,fun a b ha hb _ => ?_⟩
      have rr : r < o := hb.trans_le (ro b)
      have count : 2 ≤ (ports gs).count r := by
        rcases term a with hout | hcount
        · omega
        · simpa [ha] using hcount
      exact (h ⟨rr,count⟩).elim
  choose center picked using stars
  have cover : ∀ u v : Vertex, adj u v = true → u ∈ forks.image center ∨ v ∈ forks.image center := by
    have goes (a b : Vertex) (h : adj a b = true) (hlt : R a < R b) :
        a ∈ forks.image center ∨ b ∈ forks.image center := by
      have hm : R a ∈ forks := by
        have hh : R a < o := hlt.trans_le (ro b)
        have hc' : 2 ≤ (ports gs).count (R a) := by
          rcases term a with eq | hr
          · omega
          · exact hr
        exact Finset.mem_filter.mpr ⟨by rw [hpins,Finset.mem_range]; exact hh,hc'⟩
      rcases picked (R a) a b rfl hlt h with e | e
      · exact Or.inl (Finset.mem_image.mpr ⟨_,hm,e.symm⟩)
      · exact Or.inr (Finset.mem_image.mpr ⟨_,hm,e.symm⟩)
    intro u v h
    rcases lt_trichotomy (R u) (R v) with hlt | heq | hgt
    · exact goes u v h hlt
    · have pv := path v
      rw [← heq] at pv
      rw [commonRootHasNoEdge hc (ro u) hval (path u) pv] at h
      contradiction
    · exact (goes v u ((adj_symm v u).trans h) hgt).symm
  exact (cover_lower (forks.image center) cover).trans Finset.card_image_le

lemma finish (C : Circuit) (hf : FanInTwo C) (hs : circuitFun 9 C = target) :
    ∃ D : Circuit, FanInTwo D ∧ D.size ≤ C.size ∧ circuitFun 9 D = circuitFun 9 C ∧
      NestedCover.ReadsBack 9 D ∧
      (∀ g ∈ D.gates, g.op = GateOp.not ∧ g.inputs.length = 1 ∨
        g.op ≠ GateOp.not ∧ g.inputs.length = 2) ∧
      let l := D.gates.flatMap Gate.inputs
      let repeated := (l.toFinset.filter fun w => 2 ≤ l.count w).card
      let extra := l.length - l.toFinset.card
      let unary := D.gates.countP fun g => g.inputs.length == 1
      D.output = 8 + D.size ∧ l.toFinset = Finset.range (8 + D.size) ∧
        5 ≤ repeated ∧ repeated ≤ extra ∧ extra + unary + 8 = D.size := by
  obtain ⟨gs,o,hc,hsize,hval,ho,hpins⟩ := normalized C hf hs
  have hread : NestedCover.ReadsBack 9 ⟨gs,o⟩ := by
    intro j hj i hi
    change j < gs.length at hj
    have hg : gs[j]? = some gs[j] := List.getElem?_eq_getElem hj
    have he : NestedCover.gateAt (⟨gs,o⟩ : Circuit) j = gs[j] := by
      simp [NestedCover.gateAt,List.getD_eq_getElem?_getD,hg]
    rw [he] at hi
    exact (hc j _ hg).lt i hi
  have pins : (ports gs).toFinset = Finset.range o := by rwa [ho]
  refine ⟨⟨gs,o⟩,fun g hg => (clean_nok _ _ hc g hg).1,hsize,?_,hread,?_,
    ho,hpins,five_repeated hc hval ho pins,repeat_le_extra (ports gs),?_⟩
  · rw [hs]
    exact funext hval
  · intro g hg
    obtain ⟨p,hp⟩ := List.mem_iff_getElem?.mp hg
    rcases hc p g hp with ⟨hop,_,_,hin⟩ | ⟨hop,_,_,_,_,hin⟩
    · exact Or.inl ⟨hop,by simp [hin]⟩
    · refine Or.inr ⟨?_, by simp [hin]⟩
      rcases hop with h | h <;> simp [h]
  · change (ports gs).length - (ports gs).toFinset.card +
      gs.countP (fun g => g.inputs.length == 1) + 8 = gs.length
    have hlen := arity_count hc
    have hle := List.toFinset_card_le (ports gs)
    rw [hpins,Finset.card_range] at hle ⊢
    omega

end PEqualNP.Outside.L_meta_7328

theorem PEqualNP.Outside.L_meta_7328 :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x3 : Fin (9 : ℕ) → Bool) => x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ))) →       ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit),         PEqualNP.MetaComplexity.FanInTwo x4 ∧           x4.size ≤ x1.size ∧             PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x4 = PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 ∧               PEqualNP.MetaComplexity.NestedCover.ReadsBack (9 : ℕ) x4 ∧                 (∀ x5 ∈ x4.gates, x5.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (1 : ℕ) ∨ x5.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (2 : ℕ)) ∧                   have x5 : List ℕ := List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates;                   have x6 : ℕ := {x6 ∈ x5.toFinset | (2 : ℕ) ≤ List.count x6 x5}.card;                   have x7 : ℕ := x5.length - x5.toFinset.card;                   have x8 : ℕ := List.countP (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => x8.inputs.length == (1 : ℕ)) x4.gates;                   x4.output = (8 : ℕ) + x4.size ∧ x5.toFinset = Finset.range ((8 : ℕ) + x4.size) ∧ (5 : ℕ) ≤ x6 ∧ x6 ≤ x7 ∧ x7 + x8 + (8 : ℕ) = x4.size := by
  exact PEqualNP.Outside.L_meta_7328.finish
