import Mathlib
import PEqualNP.Defs

-- The gate-run and barrier soundness lemmas are adapted from L_meta_4354 and
-- the earlier L_meta_927 proof by sanchan. The finite certificate is for this step.
namespace PEqualNP.Outside.L_meta_8485

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool

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

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

abbrev Stat := Sum Bool ℕ

def statVal (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def statValid (m : ℕ) : Stat → Prop
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

def CleanG (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

theorem cleanG_lt {m : ℕ} {g : Gate} (h : CleanG m g) : ∀ a ∈ g.inputs, a < m := by
  rcases h with ⟨_, j, hj, hin⟩ | ⟨_, j, k, hj, hk, hin⟩
  · intro a ha; simp [hin] at ha; omega
  · intro a ha; simp [hin] at ha; rcases ha with rfl | rfl <;> omega

def CleanL (n : ℕ) (gs : List Gate) : Prop :=
  ∀ p g, gs[p]? = some g → CleanG (n + p) g

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat)
    (hv : ∀ s ∈ ins, statValid m s) :
    ∀ g ∈ (simplify op m ins).1, CleanG m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    exact Or.inr ⟨Or.inl rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    exact Or.inr ⟨Or.inr rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    exact Or.inl ⟨rfl, _, hv (Sum.inr _) (by simp), rfl⟩
  · simp at hg
  · simp at hg

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

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
    rw [elim_cons, List.length_cons]; omega

theorem statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem statVal_append (w t : List Bool) : ∀ s : Stat, statValid w.length s →
    statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

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
    have hvals : ins.map (statVal w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show statValid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      statVal (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨statValid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, statVal_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

theorem elim_clean (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, Ok g) → (∀ i, statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false))) →
    CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro acc _ _ hc; exact hc
  | cons g gs ih =>
    intro acc hok hv hc
    have hstep := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    apply hstep
    · intro i
      set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
      have hgok := hok g List.mem_cons_self
      have hs := simplify_sound g.op hgok.1 (List.replicate (n + acc.2.length) false) ins
        (by simpa [hins] using hgok.2)
        (by
          intro s hs
          obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
          simpa using hv a)
      simp only [List.length_replicate] at hs
      show statValid (n + (acc.2 ++ _).length) ((acc.1 ++ [_]).getD i (Sum.inl false))
      rw [List.length_append, ← Nat.add_assoc]
      by_cases hil : i = acc.1.length
      · subst hil; rw [getD_snoc_eq]; exact hs.1
      · rw [getD_snoc_ne _ _ _ _ hil]; exact statValid_mono (by omega) _ (hv i)
    · intro p g' hp
      simp only [elimStep] at hp
      by_cases hlt : p < acc.2.length
      · rw [List.getElem?_append_left hlt] at hp
        exact hc p g' hp
      · rw [List.getElem?_append_right (by omega)] at hp
        set r := simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false)) with hr
        cases ho : r.1 with
        | none => simp [ho] at hp
        | some g0 =>
          rw [ho] at hp
          have hp0 : p - acc.2.length = 0 := by
            have := (List.getElem?_eq_some_iff.1 hp).1
            simp at this; omega
          have hpeq : p = acc.2.length := by omega
          rw [hp0] at hp
          simp at hp
          subst hp
          rw [hpeq]
          exact simplify_clean g.op (n + acc.2.length) _ (by
            intro s hs
            obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
            exact hv a) g0 (by rw [← hr, ho]; rfl)

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

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
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
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

def val (gs : List Gate) (n : ℕ) (a : ℕ) : BFn n :=
  fun x => (wiresFrom gs (List.ofFn x)).getD a false

theorem val_input (gs : List Gate) (n : ℕ) (i : Fin n) : val gs n i = fun x => x i := by
  funext x
  unfold val
  rw [getD_wiresFrom _ _ _ (by simp)]
  simp

theorem split_at {α : Type} (gs : List α) (p : ℕ) (g : α) (hp : gs[p]? = some g) :
    ∃ pre post, gs = pre ++ g :: post ∧ pre.length = p := by
  have hlt : p < gs.length := (List.getElem?_eq_some_iff.1 hp).1
  have hget : gs[p] = g := (List.getElem?_eq_some_iff.1 hp).2
  refine ⟨gs.take p, gs.drop (p + 1), ?_, by simp; omega⟩
  have h1 : gs = gs.take p ++ gs.drop p := (List.take_append_drop p gs).symm
  have h2 : gs.drop p = gs[p] :: gs.drop (p + 1) := List.drop_eq_getElem_cons hlt
  exact h1.trans (by rw [h2, hget])

theorem val_gate (n : ℕ) (gs : List Gate) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (hlt : ∀ a ∈ g.inputs, a < n + p) (x : Fin n → Bool) :
    val gs n (n + p) x = g.op.eval (g.inputs.map fun a => val gs n a x) := by
  obtain ⟨pre, post, rfl, hlen⟩ := split_at gs p g hp
  unfold val
  have h1 : wiresFrom (pre ++ g :: post) (List.ofFn x) = wiresFrom post
      (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have hl : (wiresFrom pre (List.ofFn x)).length = n + p := by
    rw [length_wiresFrom]; simp [hlen]
  rw [h1, getD_wiresFrom _ _ _ (by simp [hl]), getD_snoc_len _ _ _ _ hl]
  congr 1
  apply List.map_congr_left
  intro a ha
  have hal := hlt a ha
  have e1 := getD_wiresFrom post (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) a
        (by simp [hl]; omega)
  rw [e1, List.getD_append _ _ _ _ (by omega)]

def initId (n : ℕ) : List Stat := List.ofFn fun i : Fin n => Sum.inr (i : ℕ)

theorem inv_initId (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (initId n, []) := by
  refine ⟨by simp [initId], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [initId, hlt, statValid, statVal, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [initId]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem exists_clean (n : ℕ) (f : BFn n) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (h : HasCircuitSize n f s) :
    ∃ gs o, CleanL n gs ∧ gs.length ≤ s ∧ o < n + gs.length ∧ ∀ x, val gs n o x = f x := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set acc := elim n C.gates (initId n, []) with hacc
  have hinv : ∀ y : Fin n → Bool, Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ ok (inv_initId n y)
  have hcl : CleanL n acc.2 := by
    apply elim_clean n C.gates (initId n, []) ok
    · intro i
      by_cases hlt : i < n
      · simp [initId, hlt, statValid]
      · rw [List.getD_eq_default _ _ (by simp [initId]; omega)]; trivial
    · intro p g hp; simp at hp
  have hlen : acc.2.length ≤ s := by
    have := elim_len n C.gates (initId n, [])
    rw [← hacc] at this
    simp only [List.length_nil, zero_add] at this
    omega
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    have e1 := ((hinv y).2 C.output).2
    have e2 := ((hinv y').2 C.output).2
    rw [hst] at e1 e2
    have h1 : (wiresFrom C.gates (List.ofFn y)).getD C.output false = f y := hev y
    have h2 : (wiresFrom C.gates (List.ofFn y')).getD C.output false = f y' := hev y'
    rw [← h1, ← h2, ← e1, ← e2]; rfl
  | inr j =>
    have hj : j < n + acc.2.length := by
      obtain ⟨y, _, _⟩ := hnc
      have := ((hinv y).2 C.output).1
      rw [hst] at this
      exact this
    refine ⟨acc.2, j, hcl, hlen, hj, ?_⟩
    intro x
    have e1 := ((hinv x).2 C.output).2
    rw [hst] at e1
    exact e1.trans (hev x)

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

def Run {α : Type} (inv : α → α) (meet join : α → α → α) (y : α) (t : ℕ) (ws : List α) : Prop :=
  ∀ P : ℕ → List α → Prop, P 0 [y] →
    (∀ {s xs zs}, List.Perm xs zs → P s xs → P s zs) →
    (∀ {s a r} (neg save : Bool), P s ((if neg then inv a else a) :: kept save a r) →
      P (s+1) (a :: r)) →
    (∀ {s a b r} (c ka kb : Bool),
      P s ((if c then meet a b else join a b) :: kept ka a (kept kb b r)) →
      P (s+1) (a :: b :: r)) → P t ws

theorem Run.done {α inv meet join y} : @Run α inv meet join y 0 [y] := fun _ d _ _ _ => d

theorem Run.perm {α inv meet join y s xs zs} (p : List.Perm xs zs)
    (h : @Run α inv meet join y s xs) : Run inv meet join y s zs :=
  fun P d q u b => q p (h P d q u b)

theorem Run.one {α inv meet join y s a r} (neg save : Bool)
    (h : @Run α inv meet join y s ((if neg then inv a else a) :: kept save a r)) :
    Run inv meet join y (s+1) (a :: r) := fun P d q u b => u neg save (h P d q u b)

theorem Run.two {α inv meet join y s a b r} (c ka kb : Bool)
    (h : @Run α inv meet join y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))) :
    Run inv meet join y (s+1) (a :: b :: r) := fun P d q u v => v c ka kb (h P d q u v)

theorem Run.fold {α inv meet join y} {P : ∀ t ws, @Run α inv meet join y t ws → Prop}
    (done : P 0 [y] Run.done)
    (perm : ∀ {s xs zs} (hp : List.Perm xs zs) (h : Run inv meet join y s xs),
      P s xs h → P s zs (Run.perm hp h))
    (one : ∀ {s a r} (neg save : Bool)
      (h : Run inv meet join y s ((if neg then inv a else a) :: kept save a r)),
      P _ _ h → P _ _ (Run.one neg save h))
    (two : ∀ {s a b r} (c ka kb : Bool)
      (h : Run inv meet join y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))),
      P _ _ h → P _ _ (Run.two c ka kb h))
    {t ws} (h : Run inv meet join y t ws) : P t ws h := by
  have hex := h (fun s xs => ∃ h' : Run inv meet join y s xs, P s xs h')
    ⟨Run.done, done⟩
    (fun hp ⟨h', ih⟩ => ⟨Run.perm hp h', perm hp h' ih⟩)
    (fun n k ⟨h', ih⟩ => ⟨Run.one n k h', one n k h' ih⟩)
    (fun c a b ⟨h', ih⟩ => ⟨Run.two c a b h', two c a b h' ih⟩)
  exact hex.elim fun _ hp => hp

theorem kept_map {α β : Type} (e : α → β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e) := by cases b <;> simp [kept]

theorem mem_kept {α : Type} (b : Bool) (x a : α) (xs : List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs := by cases b <;> simp [kept]

theorem nodup_kept {α : Type} (b : Bool) (x : α) (xs : List α) (h : xs.Nodup) (hx : x ∉ xs) :
    (kept b x xs).Nodup := by
  cases b
  · simpa [kept] using h
  · simpa [kept] using And.intro hx h

theorem Run.map {α β : Type} (e : α → β) {inv : α → α} {meet join : α → α → α}
    {inv' : β → β} {meet' join' : β → β → β}
    (hi : ∀ a, e (inv a) = inv' (e a)) (hm : ∀ a b, e (meet a b) = meet' (e a) (e b))
    (hj : ∀ a b, e (join a b) = join' (e a) (e b))
    {y : α} {s : ℕ} {ws : List α} (h : Run inv meet join y s ws) :
    Run inv' meet' join' (e y) s (ws.map e) := by
  induction h using Run.fold with
  | done => exact Run.done
  | perm hp _ ih => exact Run.perm (hp.map e) ih
  | @one s a rest neg save _ ih =>
    have e1 : ((if neg then inv a else a) :: kept save a rest).map e
        = (if neg then inv' (e a) else e a) :: kept save (e a) (rest.map e) := by
      cases neg <;> simp [kept_map, hi]
    rw [e1] at ih
    exact Run.one neg save ih
  | @two s a b rest conj ka kb _ ih =>
    have e1 : ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)).map e
        = (if conj then meet' (e a) (e b) else join' (e a) (e b))
            :: kept ka (e a) (kept kb (e b) (rest.map e)) := by
      cases conj <;> simp [kept_map, hm, hj]
    rw [e1] at ih
    exact Run.two conj ka kb ih

def Reach (n : ℕ) (gs : List Gate) (o a : ℕ) : Prop :=
  ∀ P : ℕ → Prop, P o →
    (∀ q g, gs[q]? = some g → P (n + q) → ∀ u ∈ g.inputs, P u) → P a

theorem reach_self (n : ℕ) (gs : List Gate) (o : ℕ) : Reach n gs o o :=
  fun _ ho _ => ho

theorem reach_step {n : ℕ} {gs : List Gate} {o q u : ℕ} {g : Gate}
    (hq : gs[q]? = some g) (hr : Reach n gs o (n + q)) (hu : u ∈ g.inputs) :
    Reach n gs o u :=
  fun P ho hs => hs q g hq (hr P ho hs) u hu

theorem reach_cases {n : ℕ} {gs : List Gate} {o a : ℕ} (h : Reach n gs o a) :
    a = o ∨ ∃ q g, gs[q]? = some g ∧ a ∈ g.inputs ∧ Reach n gs o (n + q) := by
  apply h (fun x => x = o ∨ ∃ q g, gs[q]? = some g ∧ x ∈ g.inputs ∧ Reach n gs o (n + q))
  · exact Or.inl rfl
  · intro q g hq hP u hu
    refine Or.inr ⟨q, g, hq, hu, ?_⟩
    rcases hP with rfl | ⟨q', g', hq', hin', hr'⟩
    · exact reach_self n gs (n + q)
    · exact reach_step hq' hr' hin'

def Live (n : ℕ) (gs : List Gate) (o p a : ℕ) : Prop :=
  a = o ∨ ∃ q, p ≤ q ∧ ∃ g, gs[q]? = some g ∧ a ∈ g.inputs ∧ Reach n gs o (n + q)

open Classical in
noncomputable def liveList (gs : List Gate) (n o p : ℕ) : List ℕ :=
  (List.range (n + p)).filter (fun a => decide (Live n gs o p a))

theorem mem_liveList (gs : List Gate) (n o p a : ℕ) :
    a ∈ liveList gs n o p ↔ a < n + p ∧ Live n gs o p a := by
  simp [liveList]

theorem nodup_liveList (gs : List Gate) (n o p : ℕ) : (liveList gs n o p).Nodup :=
  List.Nodup.filter _ List.nodup_range

abbrev invF {n : ℕ} : BFn n → BFn n := fun a x => !a x

abbrev meetF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x && b x

abbrev joinF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x || b x

theorem live_succ_reach (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs)
    (p : ℕ) (g : Gate) (hg : gs[p]? = some g) (hr : Reach n gs o (n + p)) (a : ℕ) :
    a ∈ liveList gs n o (p + 1) ↔
      a = n + p ∨ (a ∈ liveList gs n o p ∧ (a ∈ g.inputs → Live n gs o (p + 1) a)) := by
  rw [mem_liveList, mem_liveList]
  constructor
  · rintro ⟨hlt, hl⟩
    by_cases ha : a = n + p
    · exact Or.inl ha
    · refine Or.inr ⟨⟨by omega, ?_⟩, fun _ => hl⟩
      rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
      · exact Or.inl h
      · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩
  · rintro (rfl | ⟨⟨hlt, hl⟩, himp⟩)
    · refine ⟨by omega, ?_⟩
      rcases reach_cases hr with h | ⟨q, g', hg', hin, hrq⟩
      · exact Or.inl h
      · refine Or.inr ⟨q, ?_, g', hg', hin, hrq⟩
        have := cleanG_lt (hcl q g' hg') _ hin
        omega
    · refine ⟨by omega, ?_⟩
      rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
      · exact Or.inl h
      · by_cases hqp : q = p
        · subst hqp
          rw [hg] at hg'
          cases hg'
          exact himp hin
        · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩

theorem live_succ_dead (n : ℕ) (gs : List Gate) (o : ℕ)
    (p : ℕ) (hnr : ¬ Reach n gs o (n + p)) (a : ℕ) :
    a ∈ liveList gs n o (p + 1) ↔ a ∈ liveList gs n o p := by
  rw [mem_liveList, mem_liveList]
  constructor
  · rintro ⟨hlt, hl⟩
    have hne : a ≠ n + p := by
      rintro rfl
      rcases hl with rfl | ⟨q, _, g', hg', hin, hrq⟩
      · exact hnr (reach_self n gs _)
      · exact hnr (reach_step hg' hrq hin)
    refine ⟨by omega, ?_⟩
    rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
    · exact Or.inl h
    · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩
  · rintro ⟨hlt, hl⟩
    refine ⟨by omega, ?_⟩
    rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
    · exact Or.inl h
    · by_cases hqp : q = p
      · subst hqp; exact absurd hrq hnr
      · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩

open Classical in
theorem run_live (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs) (ho : o < n + gs.length) :
    ∀ d p, p + d = gs.length →
      ∃ d', d' ≤ d ∧
        Run (invF (n := n)) meetF joinF (val gs n o) d' ((liveList gs n o p).map (val gs n)) := by
  intro d
  induction d with
  | zero =>
    intro p hp
    have hperm : [o].Perm (liveList gs n o p) := by
      refine (List.perm_ext_iff_of_nodup (List.nodup_singleton o) (nodup_liveList _ _ _ _)).2 ?_
      intro a
      rw [mem_liveList, List.mem_singleton]
      constructor
      · rintro rfl; exact ⟨by omega, Or.inl rfl⟩
      · rintro ⟨_, h | ⟨q, hq, g', hg', _, _⟩⟩
        · exact h
        · have := (List.getElem?_eq_some_iff.1 hg').1; omega
    exact ⟨0, le_rfl, Run.perm (hperm.map (val gs n)) Run.done⟩
  | succ d ih =>
    intro p hp
    have hplt : p < gs.length := by omega
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hplt⟩
    obtain ⟨d', hd', IH⟩ := ih (p + 1) (by omega)
    by_cases hr : Reach n gs o (n + p)
    · have hstep := live_succ_reach n gs o hcl p g hg hr
      have hin : ∀ a ∈ g.inputs, a ∈ liveList gs n o p := fun a ha =>
        (mem_liveList _ _ _ _ _).2 ⟨cleanG_lt (hcl p g hg) a ha, Or.inr ⟨p, le_rfl, g, hg, ha, hr⟩⟩
      have hnew : ∀ a ∈ liveList gs n o p, a ≠ n + p := fun a ha =>
        Nat.ne_of_lt ((mem_liveList _ _ _ _ _).1 ha).1
      have hvg := val_gate n gs p g hg (cleanG_lt (hcl p g hg))
      have hnd0 := nodup_liveList gs n o p
      have single : ∀ (j : ℕ) (neg : Bool), (∀ a, a ∈ g.inputs ↔ a = j) →
          val gs n (n + p) = (if neg then invF (val gs n j) else val gs n j) →
          Run (invF (n := n)) meetF joinF (val gs n o) (d' + 1)
            ((liveList gs n o p).map (val gs n)) := by
        intro j neg hmem hval
        have hj := hin j ((hmem j).2 rfl)
        have hp1 : (liveList gs n o p).Perm (j :: (liveList gs n o p).erase j) :=
          List.perm_cons_erase hj
        have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
        have hp2 : (liveList gs n o (p + 1)).Perm
            ((n + p) :: kept (decide (Live n gs o (p + 1) j)) j ((liveList gs n o p).erase j)) := by
          refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
          · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ hnr (by simp [hnd0.mem_erase_iff])⟩
            rw [mem_kept]
            rintro (⟨_, h⟩ | h)
            · exact hnew j hj h.symm
            · exact hnew _ (List.mem_of_mem_erase h) rfl
          · intro a
            rw [hstep a, List.mem_cons, mem_kept, hnd0.mem_erase_iff, hmem a]
            simp only [decide_eq_true_eq]
            constructor
            · rintro (h | ⟨h1, h2⟩)
              · exact Or.inl h
              · by_cases haj : a = j
                · exact Or.inr (Or.inl ⟨haj ▸ h2 haj, haj⟩)
                · exact Or.inr (Or.inr ⟨haj, h1⟩)
            · rintro (h | ⟨h1, rfl⟩ | ⟨h1, h2⟩)
              · exact Or.inl h
              · exact Or.inr ⟨hj, fun _ => h1⟩
              · exact Or.inr ⟨h2, fun h => absurd h h1⟩
        have IH' := Run.perm (hp2.map (val gs n)) IH
        rw [List.map_cons, kept_map, hval] at IH'
        exact Run.perm (hp1.map (val gs n)).symm (Run.one neg _ IH')
      refine ⟨d' + 1, by omega, ?_⟩
      rcases hcl p g hg with ⟨hop, j, hj, hinp⟩ | ⟨hop, j, k, hj, hk, hinp⟩
      · apply single j true
        · intro a; simp [hinp]
        · funext x; rw [hvg x, hop, hinp]; simp [GateOp.eval]
      · by_cases hjk : j = k
        · subst hjk
          apply single j false
          · intro a; simp [hinp]
          · funext x; rw [hvg x, hinp]; rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
        · have hjm := hin j (by simp [hinp])
          have hkm := hin k (by simp [hinp])
          have hke : k ∈ (liveList gs n o p).erase j :=
            (hnd0.mem_erase_iff).2 ⟨fun e => hjk e.symm, hkm⟩
          have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
          have hnr2 : (((liveList gs n o p).erase j).erase k).Nodup := hnr.erase k
          have hp1 : (liveList gs n o p).Perm
              (j :: k :: ((liveList gs n o p).erase j).erase k) :=
            (List.perm_cons_erase hjm).trans ((List.perm_cons_erase hke).cons j)
          have hmr : ∀ a, a ∈ ((liveList gs n o p).erase j).erase k ↔
              a ≠ k ∧ a ≠ j ∧ a ∈ liveList gs n o p := by
            intro a; rw [hnr.mem_erase_iff, hnd0.mem_erase_iff]
          have hp2 : (liveList gs n o (p + 1)).Perm
              ((n + p) :: kept (decide (Live n gs o (p + 1) j)) j
                (kept (decide (Live n gs o (p + 1) k)) k
                  (((liveList gs n o p).erase j).erase k))) := by
            refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
            · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ (nodup_kept _ _ _ hnr2 ?_) ?_⟩
              · rw [mem_kept, mem_kept]
                rintro (⟨_, h⟩ | ⟨_, h⟩ | h)
                · exact hnew j hjm h.symm
                · exact hnew k hkm h.symm
                · exact hnew _ ((hmr _).1 h).2.2 rfl
              · rw [hmr]; simp
              · rw [mem_kept, hmr]
                rintro (⟨_, h⟩ | h)
                · exact hjk h
                · exact h.2.1 rfl
            · intro a
              rw [hstep a, List.mem_cons, mem_kept, mem_kept, hmr a]
              simp only [decide_eq_true_eq, hinp, List.mem_cons, List.not_mem_nil, or_false]
              constructor
              · rintro (h | ⟨h1, h2⟩)
                · exact Or.inl h
                · by_cases haj : a = j
                  · exact Or.inr (Or.inl ⟨haj ▸ h2 (Or.inl haj), haj⟩)
                  · by_cases hak : a = k
                    · exact Or.inr (Or.inr (Or.inl ⟨hak ▸ h2 (Or.inr hak), hak⟩))
                    · exact Or.inr (Or.inr (Or.inr ⟨hak, haj, h1⟩))
              · rintro (h | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, h2, h3⟩)
                · exact Or.inl h
                · exact Or.inr ⟨hjm, fun _ => h1⟩
                · exact Or.inr ⟨hkm, fun _ => h1⟩
                · exact Or.inr ⟨h3, fun h => by rcases h with h | h <;> contradiction⟩
          have IH' := Run.perm (hp2.map (val gs n)) IH
          have hval : val gs n (n + p) = (if decide (g.op = GateOp.and)
              then meetF (val gs n j) (val gs n k) else joinF (val gs n j) (val gs n k)) := by
            funext x; rw [hvg x, hinp]
            rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
          rw [List.map_cons, kept_map, kept_map, hval] at IH'
          exact Run.perm (hp1.map (val gs n)).symm (Run.two _ _ _ IH')
    · have hp : (liveList gs n o (p + 1)).Perm (liveList gs n o p) :=
        (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) (nodup_liveList _ _ _ _)).2
          (live_succ_dead n gs o p hr)
      exact ⟨d', by omega, Run.perm (hp.map (val gs n)) IH⟩

theorem exists_run {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : HasCircuitSize n f s) :
    ∃ s', s' ≤ s ∧ ∃ ws : List (BFn n),
      ws.Sublist (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)) ∧
      Run (invF (n := n)) meetF joinF f s' ws := by
  obtain ⟨gs, o, hcl, hlen, ho, hev⟩ := exists_clean n f s hnc h
  obtain ⟨d', hd', hrun⟩ := run_live n gs o hcl ho gs.length 0 (by omega)
  refine ⟨d', by omega, (liveList gs n o 0).map (val gs n), ?_, ?_⟩
  · have e : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i))
        = (List.range n).map (val gs n) := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
        exact (val_input gs n ⟨i, by simpa using h1⟩).symm
    rw [e]
    exact (List.filter_sublist).map _
  · have hf : val gs n o = f := funext hev
    rw [← hf]
    exact hrun

theorem run_len {α inv meet join y s xs} (h : @Run α inv meet join y s xs) :
    xs.length ≤ s + 1 := by
  induction h using Run.fold with
  | done => simp
  | perm hp _ ih => rwa [← hp.length_eq]
  | one neg save h ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb h ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

abbrev NatRun (m : Nat) := Run (· ^^^ m) (· &&& ·) (· ||| ·)

theorem run_bits {m y s xs} (h : NatRun m y s xs) (i j : Nat)
    (hm : m.testBit i = m.testBit j)
    (hw : ∀ w ∈ xs, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one neg save h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    intro w hmem
    cases neg <;> cases save <;> simp only [Bool.false_eq_true, ite_false, ite_true,
      kept, List.mem_cons] at hmem <;>
      first | (rcases hmem with rfl | hr; exact ha; exact hw _ (by simp [hr]))
            | (rcases hmem with rfl | hr; simp [ha, hm]; exact hw _ (by simp [hr]))
  | two conj ka kb h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hmem
    cases conj <;> cases ka <;> cases kb <;> simp only [Bool.false_eq_true,
      ite_false, ite_true, kept, List.mem_cons] at hmem <;>
      rcases hmem with rfl | hr <;> first | simp [ha, hb] | exact hw _ (by simp only [List.mem_cons]; tauto)

def diff (k w : Nat) : Nat := w ^^^ (w >>> k)

def cov (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diff k a ||| cov k t

theorem cov_bit (k i : Nat) (ws : List Nat) : (cov k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i ≠ a.testBit (k+i) := by
  induction ws with
  | nil => simp [cov]
  | cons a t ih =>
    simp only [cov, Nat.testBit_or, Bool.or_eq_true, ih, diff, Nat.testBit_xor,
      Nat.testBit_shiftRight, List.mem_cons]
    cases hx : a.testBit i <;> cases hy : a.testBit (k+i) <;> simp_all

def lo (k : Nat) := 2^k - 1

def mask (k : Nat) := lo (k+k)

def goal (k : Nat) := lo k <<< k

theorem required {k s ws} (h : NatRun (mask k) (goal k) s ws) :
    (cov k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hm : (mask k).testBit i = (mask k).testBit (k+i) := by
      simp [mask, lo, Nat.testBit_two_pow_sub_one, show i < k+k by omega, show k+i < k+k by omega]
    have hy : (goal k).testBit i ≠ (goal k).testBit (k+i) := by
      simp [goal, lo, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, hi, show ¬ k ≤ i by omega]
    have hc : (cov k ws).testBit i = true := by
      apply (cov_bit k i ws).2
      by_contra! hh
      exact hy (run_bits h i (k+i) hm hh)
    simp [hc]
  · simp [lo, Nat.testBit_two_pow_sub_one, hi]

theorem keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p

def tagU (ws : List Nat) (a : Nat) (neg ka : Bool) :=
  4 * ws.idxOf a + 2 * neg.toNat + ka.toNat

def tagB (ws : List Nat) (a b : Nat) (conj ka kb : Bool) :=
  let j := ws.idxOf b
  48 + 8 * (j*(j+1)/2 + ws.idxOf a) + 4 * conj.toNat + 2 * ka.toNat + kb.toNat

def next (m : Nat) (slack : Nat) (ws : List Nat) (f : Nat → List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    (slack ≥ 1 && ([false,true].any fun neg =>
      let w := if neg then a ^^^ m else a
      f (tagU ws a neg false) (w :: ra) || (slack ≥ 2 && f (tagU ws a neg true) (w :: a :: ra)))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false,true].any fun conj =>
          let w := if conj then a &&& b else a ||| b
          f (tagB ws a b conj false false) (w :: r) || (slack ≥ 1 && (f (tagB ws a b conj true false) (w :: a :: r) || f (tagB ws a b conj false true) (w :: b :: r))) ||
            (slack ≥ 2 && f (tagB ws a b conj true true) (w :: a :: b :: r)))

theorem next_one {k a rest} {neg save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s ((if neg then a ^^^ mask k else a) :: kept save a rest))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s+2-ws.length := by cases save <;> simp [kept] at hh <;> omega
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; left
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl, ?_⟩
  apply List.any_eq_true.2 ⟨neg, by cases neg <;> simp, ?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at ht; simp [ht]
  | true =>
    simp [kept] at ht hh
    have hsl2 : 2 ≤ s+2-ws.length := by omega
    simp [ht, hsl2]

theorem next_two_sorted {k a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pp := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hb := pp.mem_iff.1 List.mem_cons_self
  have pr := (pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; right
  apply List.any_eq_true.2 ⟨b, hb, ?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab, ?_⟩
  apply List.any_eq_true.2 ⟨conj, by cases conj <;> simp, ?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true, Bool.true_and] <;>
    first | (simp [show 2 ≤ s+2-ws.length by omega]) | (simp [show 1 ≤ s+2-ws.length by omega])

theorem next_two {k a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  rcases le_total a b with hab | hba
  · exact next_two_sorted hab p h f hf
  · apply next_two_sorted (conj := conj) (ka := kb) (kb := ka) hba ((List.Perm.swap _ _ _).trans p) _ f hf
    have he : (if conj then a &&& b else a ||| b) = (if conj then b &&& a else b ||| a) := by
      cases conj <;> simp [Nat.and_comm, Nat.or_comm]
    rw [he] at h
    apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]
    exact List.Perm.swap _ _ _

theorem zero_done {α inv meet join y t ws} (h : @Run α inv meet join y t ws) :
    t = 0 → ws = [y] := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih => intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one => simp
  | two => simp

theorem next_complete {k t ws} (h : NatRun (mask k) (goal k) t ws) :
    ∀ s, t = s+1 → ∀ zs, ws.Perm zs → ∀ f : Nat → List Nat → Bool,
      (∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) →
      next (mask k) (s+2-zs.length) zs f = true := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one neg save h ih => intro s he zs p f hf; cases he; exact next_one p h f hf
  | two conj ka kb h ih => intro s he zs p f hf; cases he; exact next_two p h f hf

def pt (n : ℕ) (v : ℕ) : Fin n → Bool := fun i => v.testBit i

def encL {n : ℕ} (a : BFn n) : List ℕ → ℕ
  | [] => 0
  | v :: t => Nat.bit (a (pt n v)) (encL a t)

theorem encL_testBit {n : ℕ} (a : BFn n) : ∀ (l : List ℕ) (j : ℕ),
    (encL a l).testBit j = (l.map fun v => a (pt n v)).getD j false
  | [], j => by simp [encL]
  | v :: t, 0 => by simp [encL, Nat.testBit_bit_zero]
  | v :: t, j + 1 => by simp [encL, Nat.testBit_bit_succ, encL_testBit a t j]

theorem encL_inv {n : ℕ} (a : BFn n) (l : List ℕ) :
    encL (invF a) l = encL a l ^^^ (2 ^ l.length - 1) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    simp [h]

theorem encL_and {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (meetF a b) l = encL a l &&& encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

theorem encL_or {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (joinF a b) l = encL a l ||| encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

theorem bits_le {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1) (i j : Nat)
    (hw : ∀ a ∈ ws, a.testBit i ≤ a.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih =>
    exact ih (hp.length_eq.trans hl) (fun a ha => hw a (hp.mem_iff.1 ha))
  | one neg save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    apply ih (by simp [kept]; omega)
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro a had
    simp only [kept, Bool.false_eq_true, ite_false, List.mem_cons] at had
    rcases had with rfl | ht
    · cases conj <;> simp only [ite_true, Bool.false_eq_true, ite_false, Nat.testBit_or, Nat.testBit_and] <;>
        first | exact Bool.or_le_or ha hb | exact Bool.and_le_and ha hb | grind
    · exact hw _ (by simp [ht])

def diffUp (k w : Nat) : Nat := (w >>> k) &&& (w ^^^ lo k)

def covUp (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diffUp k a ||| covUp k t

theorem covUp_bit (k i : Nat) (hi : i < k) (ws : List Nat) : (covUp k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i = false ∧ a.testBit (k+i) = true := by
  induction ws with
  | nil => simp [covUp]
  | cons a t ih => simp [covUp, diffUp, lo, hi, ih, and_comm]

theorem required_up {k s ws} (h : NatRun (mask k) (goal k) s ws) (hl : ws.length = s+1) :
    (covUp k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hy : ¬ (goal k).testBit (k+i) ≤ (goal k).testBit i := by
      simp [goal, lo, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, hi, show ¬ k ≤ i by omega]
    have hc : (covUp k ws).testBit i = true := by
      apply (covUp_bit k i hi ws).2
      by_contra! hh
      apply hy
      apply bits_le h hl
      intro a ha
      specialize hh a ha
      cases hx : a.testBit i <;> cases hy : a.testBit (k+i) <;> simp_all
    simp [hc]
  · simp [lo, Nat.testBit_two_pow_sub_one, hi]

def covers (k s : Nat) (ws : List Nat) : Bool :=
  if ws.length == s+1 then covUp k ws &&& lo k == lo k else cov k ws &&& lo k == lo k

theorem covers_ok {k s ws} (h : NatRun (mask k) (goal k) s ws) : covers k s ws = true := by
  by_cases he : ws.length = s+1
  · simp [covers, he, required_up h he]
  · simp [covers, he, required h]

def value6 (a b c d e f : Bool) : Nat :=
  let x := b.toNat+c.toNat
  let y := (!e).toNat+(!f).toNat
  if a then (if d then y else max x (max y (x+y-1))) else (if d then 0 else x)

theorem value6_and : ∀ a b c d e f g h i j l m : Bool,
    value6 (a && g) (b && h) (c && i) (d && j) (e && l) (f && m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem value6_or : ∀ a b c d e f g h i j l m : Bool,
    value6 (a || g) (b || h) (c || i) (d || j) (e || l) (f || m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem score_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1)
    (v : Nat → Nat) (hand : ∀ a b, v (a &&& b) ≤ v a + v b)
    (hor : ∀ a b, v (a ||| b) ≤ v a + v b) :
    v y ≤ (ws.map v).sum := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih =>
    rw [← (p.map v).sum_eq]
    exact ih (p.length_eq.trans hl)
  | one neg save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih' := ih (by simp [kept]; omega)
    cases conj <;> simp [kept] at ih' ⊢ <;>
      first | (grw [← Nat.add_assoc, ← hand]; exact ih')
            | (grw [← Nat.add_assoc, ← hor]; exact ih')

def eval6 (a b c d e f v : Nat) := value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)

theorem eval6_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1)
    (a b c d e f : Nat) : eval6 a b c d e f y ≤ (ws.map (eval6 a b c d e f)).sum := by
  apply score_bound h hl
  · intro v w
    simpa only [eval6, Nat.testBit_and] using value6_and
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
  · intro v w
    simpa only [eval6, Nat.testBit_or] using value6_or
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)

def scoreCheck (k s : Nat) (ws : List Nat) (code : Nat) : Bool :=
  if code = 0 then false else
    let a := code &&& 1023
    let b := (code >>> 10) &&& 1023
    let c := (code >>> 20) &&& 1023
    let d := (code >>> 30) &&& 1023
    let e := (code >>> 40) &&& 1023
    let f := (code >>> 50) &&& 1023
    ws.length == s+1 && (ws.map (eval6 a b c d e f)).sum < eval6 a b c d e f (goal k)

theorem scoreCheck_no {k s ws} (h : NatRun (mask k) (goal k) s ws) (code : Nat) :
    scoreCheck k s ws code = false := by
  unfold scoreCheck
  split
  · rfl
  · dsimp only
    by_cases hl : ws.length = s+1
    · simp [hl, Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _)]
    · simp [hl]

def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n+1, i => f i && span f n (i+1)

theorem span_ok {f n o} (h : span f n o = true) : ∀ i, o ≤ i → i < o+n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h
    intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)

theorem extend_run {α inv meet join y s t a r} (h : @Run α inv meet join y s (a::r))
    (hle : s ≤ t) : Run inv meet join y t (a::r) := by
  induction t, hle using Nat.le_induction with
  | base => exact h
  | succ t hle ih => exact Run.one false false ih

def fld (T w i : Nat) : Nat := (T >>> (w * i)) &&& (2 ^ w - 1)

def bsr (T w h : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if lo + 1 < hi then
      (if fld T w ((lo + hi) / 2) ≤ h then bsr T w h f ((lo + hi) / 2) hi
       else bsr T w h f lo ((lo + hi) / 2))
    else lo

def hw (w : Nat) : Nat := (w % 11400714819323198549 + 317) ^ 3 % 11400714819323198549 + 1

def hz : List Nat → Nat
  | [] => 0
  | w :: t => hw w + hz t

def hk (zs : List Nat) : Nat := hz zs % 4294967291

def found (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (s : Nat) (zs : List Nat) : Bool :=
  decide (idx s zs < N s) && zs.isPerm (S s (idx s zs))

def scr (k s : Nat) (pool : List Nat) (zs : List Nat) : Bool :=
  zs.length == s + 1 && pool.any (scoreCheck k s zs)

theorem scr_no {k s : Nat} (pool : List Nat) {zs : List Nat}
    (h : NatRun (mask k) (goal k) s zs) : scr k s pool zs = false := by
  unfold scr
  rw [Bool.and_eq_false_iff]
  right
  rw [List.any_eq_false]
  intro x _
  rw [scoreCheck_no h x]
  simp

def bar (k : Nat) (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (ori : List Nat → List Nat) (pool : List Nat) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [goal k])
  | s + 1, i =>
    let ws := S (s + 1) i
    !(next (mask k) (s + 2 - ws.length) ws fun _ zs =>
        covers k s zs && !(scr k s pool zs) && !(found S N idx s (ori zs)))

theorem bar_sound {k S N idx ori pool} {s i : Nat} (hb : bar k S N idx ori pool s i = true)
    (hr : ∀ {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (ori ys))
    (h : NatRun (mask k) (goal k) s (S s i)) :
    ∃ q < s, ∃ j < N q, NatRun (mask k) (goal k) q (S q j) := by
  cases s with
  | zero => simp [bar, zero_done h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (_ : Nat) (zs : List Nat) :=
      covers k s zs && !(scr k s pool zs) && !(found S N idx s (ori zs))
    have hF (tag : Nat) (zs) (hz : NatRun (mask k) (goal k) s zs) : F tag zs = true := by
      simp only [F, covers_ok hz, scr_no pool hz, Bool.not_false, Bool.true_and, found]
      simp only [Bool.not_eq_true', Bool.and_eq_false_imp, decide_eq_true_eq]
      intro hj
      by_contra! hp
      have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
      exact hn s (by omega) _ hj (Run.perm p (hr hz))
    have hN := next_complete h s rfl _ (List.Perm.refl _) F hF
    change !(next _ _ _ F) = true at hb
    rw [hN] at hb
    contradiction

theorem bar_all {k S N idx ori pool} {cap : Nat}
    (hr : ∀ {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (ori ys))
    (hc : ∀ s ≤ cap, ∀ i < N s, bar k S N idx ori pool s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ NatRun (mask k) (goal k) s (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q, hq, j, hj, h⟩ := bar_sound (hc s hs i hi) hr hh
    exact ih q hq (by omega) j hj h

def mv (m c : Nat) (ws : List Nat) : List Nat :=
  let a := ws.getD (c % 16) 0
  let b := ws.getD (c / 16 % 16) 0
  let op := c / 256 % 4
  let r := if op < 2 then ws.erase a else (ws.erase a).erase b
  (if op = 0 then a else if op = 1 then a ^^^ m else if op = 2 then a &&& b else a ||| b) ::
    kept (decide (c / 1024 % 2 = 1)) a (kept (decide (2 ≤ op ∧ c / 2048 % 2 = 1)) b r)

def StGen (k : Nat) (xs : List Nat) (PT : Nat → Nat) : Nat → Nat → Nat → List Nat
  | 0, _, _ => xs
  | d + 1, s, j =>
    let e := fld (PT s) 32 j
    mv (mask k) (e % 4096) (StGen k xs PT d (s + 1) (e / 4096))

def Sgen (k cap : Nat) (xs : List Nat) (PT : Nat → Nat) (s j : Nat) : List Nat :=
  StGen k xs PT (cap - s) s j

def idxGen (NN HT : Nat → Nat) (s : Nat) (zs : List Nat) : Nat :=
  bsr (HT s) 32 (hk zs) 16 0 (NN s)

theorem prove_base (n k cap : ℕ) (f : BFn n) (rows xs pool : List ℕ)
    (NN HT PT : ℕ → ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y')
    (hlen : rows.length = k + k)
    (hxs : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)).map (fun a => encL a rows) = xs)
    (hgoal : encL f rows = goal k)
    (hprop : ∀ zs ∈ xs.sublists, zs ≠ xs → (cov k zs &&& lo k) ≠ lo k)
    (hNcap : 0 < NN cap)
    (hchk : ∀ s ≤ cap, ∀ i < NN s,
      bar k (Sgen k cap xs PT) NN (idxGen NN HT) id pool s i = true) :
    ∀ s : ℕ, HasCircuitSize n f s → cap + 1 ≤ s := by
  intro s h
  by_contra hlt
  obtain ⟨s', hs', ws, hsub, hrun⟩ := exists_run f hnc s h
  have hmask : mask k = 2 ^ rows.length - 1 := by rw [hlen]; rfl
  have hr : NatRun (mask k) (encL f rows) s' (ws.map fun a => encL a rows) :=
    Run.map (fun a : BFn n => encL a rows)
      (fun a => by rw [hmask]; exact encL_inv a rows)
      (fun a b => encL_and a b rows) (fun a b => encL_or a b rows) hrun
  rw [hgoal] at hr
  have hsub' : (ws.map fun a => encL a rows).Sublist xs := by
    rw [← hxs]; exact hsub.map _
  by_cases he : (ws.map fun a => encL a rows) = xs
  · rw [he] at hr
    cases hxs_nil : xs with
    | nil =>
      rw [hxs_nil] at hr
      have hc := required hr
      have hne : cov k [] = 0 := rfl
      rw [hne] at hc
      have hlo : lo k ≠ 0 := by
        cases k with
        | zero =>
          simp [goal, lo] at hgoal
          obtain ⟨y, y', hne'⟩ := hnc
          have h0 : rows.length = 0 := hlen
          have hnil : rows = [] := List.eq_nil_of_length_eq_zero h0
          rw [hnil] at hxs
          have hxs0 : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)).map (fun _ => 0) = [] := by
            simpa [encL, hxs_nil] using hxs
          have hn0 : n = 0 := by simpa using congrArg List.length hxs0
          subst hn0
          exact absurd (Subsingleton.elim y y') (fun e => hne' (e ▸ rfl))
        | succ k' =>
          simp only [lo]
          have : 1 ≤ 2 ^ k' := Nat.one_le_two_pow
          rw [pow_succ]; omega
      simp at hc
      exact hlo hc.symm
    | cons a r =>
      rw [hxs_nil] at hr
      have hcap : NatRun (mask k) (goal k) cap (a :: r) := extend_run hr (by omega)
      rw [← hxs_nil] at hcap
      have hS0 : Sgen k cap xs PT cap 0 = xs := by simp [Sgen, StGen]
      rw [← hS0] at hcap
      exact bar_all (fun h => h) hchk cap le_rfl 0 hNcap hcap
  · exact hprop _ (List.mem_sublists.2 hsub') he (required hr)


def target (x : Fin 8 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 7) || (x 6 && x 7)

def rows : List ℕ := [1, 1, 1, 2, 2, 2, 4, 4, 6, 6, 6, 6, 8, 10, 10, 10, 12, 12, 14, 14, 14, 14, 16, 16, 17, 17, 17, 17, 20, 20, 20, 20, 24, 24, 24, 28, 28, 28, 28, 32, 33, 33, 33, 36, 36, 36, 40, 40, 44, 44, 44, 48, 48, 49, 49, 49, 49, 52, 52, 52, 52, 56, 56, 56, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 64, 64, 65, 65, 65, 65, 66, 66, 66, 66, 66, 72, 72, 72, 74, 74, 74, 74, 74, 74, 74, 74, 74, 74, 74, 74, 74, 80, 80, 80, 81, 81, 81, 81, 88, 88, 88, 88, 96, 96, 96, 97, 97, 97, 97, 104, 104, 104, 104, 112, 112, 112, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 113, 120, 120, 120, 120, 120, 120, 120, 120, 120, 120, 120, 120, 128, 128, 129, 129, 129, 129, 129, 130, 130, 130, 130, 132, 132, 132, 134, 134, 134, 134, 136, 136, 136, 138, 138, 138, 138, 140, 140, 140, 142, 142, 142, 142, 142, 142, 142, 142, 142, 142, 142, 142, 160, 160, 160, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 164, 164, 164, 164, 168, 168, 168, 168, 172, 172, 172, 172, 172, 172, 172, 172, 172, 172, 172, 172, 3, 5, 9, 3, 18, 34, 5, 68, 7, 22, 38, 70, 9, 11, 26, 42, 13, 76, 15, 30, 46, 78, 18, 144, 19, 21, 25, 145, 21, 22, 84, 148, 25, 26, 152, 29, 30, 92, 156, 34, 35, 37, 41, 37, 38, 100, 41, 42, 45, 46, 108, 50, 176, 51, 53, 57, 177, 53, 54, 116, 180, 57, 58, 184, 3, 5, 9, 18, 34, 61, 62, 68, 124, 144, 188, 192, 68, 192, 67, 69, 73, 193, 67, 70, 82, 98, 194, 73, 76, 200, 3, 5, 9, 18, 34, 68, 75, 78, 90, 106, 144, 192, 202, 82, 84, 208, 83, 85, 89, 209, 89, 90, 92, 216, 98, 100, 224, 99, 101, 105, 225, 105, 106, 108, 232, 114, 116, 240, 3, 5, 9, 18, 34, 68, 115, 117, 121, 144, 192, 241, 3, 5, 9, 18, 34, 68, 121, 122, 124, 144, 192, 248, 144, 192, 131, 133, 137, 145, 193, 131, 146, 162, 194, 133, 148, 196, 135, 150, 166, 198, 137, 152, 200, 139, 154, 170, 202, 141, 156, 204, 3, 5, 9, 18, 34, 68, 143, 144, 158, 174, 192, 206, 162, 176, 224, 3, 5, 9, 18, 34, 68, 144, 163, 165, 169, 177, 192, 225, 165, 166, 180, 228, 169, 170, 184, 232, 3, 5, 9, 18, 34, 68, 144, 173, 174, 188, 192, 236]

def xs : List ℕ := [0x8711bc3804722448fc0479c703e07c011c87c02723e14f091f05314f00000fff8000000007c000fff01e03c000003c00001e007000f000007, 0x1192204c9b591e3c784099059242484cf647c4059442a9192217cef39000000000fff1e3c7800000000000007ffc7c000000000000003cef38, 0xba20f0910b62e03f8081220a248490902890895e21e473a78f23f0fc2fff0f0000fffe03f8000000000000000000000fff1e073878f03f0fc0, 0xb84f01020b44ffc00109c41041e83d04f13810564e087c47f043ff004ffff00000fffffc0000fff0001e03c07fff800fffe007c07f003ff000, 0x2484422421884489121bc8bc8e003ff9420100768fff8007fffc842100000000000000000000ffffffe003ff8000000ffffff8007fffc00000, 0xb90ffbc8721008102009d09d0fffc000840200570ffffff8000108420fffffffff0000000000fffffffffc000000000fffffffff8000000000, 0xc2088c104c209122442de0de0ffffffef83fff98008042020402208800000000000000000000fffffffffffffffffff0000000000000000000, 0xfc0fffe07fc0fffffffe00e009112227002422e009110004488800000fffffffffffffffffff00000000000000000000000000000000000000]

def NN : ℕ → ℕ

  | 4 => 18

  | 5 => 210

  | 6 => 1081

  | 7 => 2425

  | 8 => 1600

  | 9 => 87

  | 10 => 1

  | _ => 0

def HT : ℕ → ℕ

  | 4 => 0xf652c6d7f07223adee6f1705cc98353acc84386ccc128dd3c5a367c8c48e9f11bc2d30b4abb53251ab066027a088cb3f9507074e931398378b2b88cf788e2934784b989749563e02

  | 5 => 0xff528c68fe4fbd1bfe498c9afdaff3c7fbb9e6b1fb3c5b65fb19793af9eb581ff8fe0aa2f84e9e1cf84c9fc9f838a2fbf7ff0b40f777804ff68a5333f64b335bf5d75040f547a77bf2fa37bbf256600cf0e41128f0c72038f02081f8ee5febceea3a182ae9cb3b5ee6045516e159e628dfc9d016dc45ae3edbda24e1db48afaddb05ea3cd93e284cd8b75ba3d6914ac3d5f39e25d5110e6ed2f4da91ce4dd195cddadec4cd866802cd337e94ccacb1ebcb13b9bfcaa35e37c9928ce3c9660967c71d2c28c4534c92c10a227dc08841ddbe9fd6c3be5fa75cbcf8b15ebb479d43bb45d472baceca31ba1be385b9aff85ab9ab19f4b9a074c3b8fe31fab644062fb5ee40fbb5c558d1b4e616c9b39bad16b0d4452eada851a5ad9cc4a1ace31226accb6607a8f364cba89b9cf0a5873d7ba499aa80a40388e7a1c29f62a17162a7a01717269f89f72b9deda9b19d9667379d5dea039ce40a2d9a743f6f962e9ede948b4d9d9192b7158fbddaaf8ed814f28c9324388b1a27da8ae5dedb8a9a399389fa6de78902dbe08880a3e5886748de87a70c3b87473bfb83ff429b80b671b67fdec1ff7f0301d57eb66c827e5682b87d178fa97c5c9f267c31350f7a7d7fb177ccd01376cd1963763e3e587638dcce74331814741f1b467336de727220d9c671b31d96702307846ed7c76c6d939ffd6bfc424a6b60af486ae323fc6aa072a5673294ca6675f7096395aaec63550acd634e11ff6124e9e85ea709035ddf9f705b6cf12d59c67fcd565c43b3551a403054f1bc6e54ac840054430e5a530a008f52e4c79a52d756a5507130a84a5a184b46e8438046477869463820414469c39a43cffaae43b7705241697f8f414ecc5b3f5bb1113edffe9c3e7fe5fd3e69b9d13ca1ea283aaf79ca3a4a26ce395fe96638c8998637eb22d835e074e9334ede573283bb4d300742e72fe32e992fcac3ad2f00151a2db080a829ed7a1c2956c0f124e4850b2207316b21a4db2e1ed3417b1e58269b1d438d381b5656b61abe7d8d1a837d341a23819918d9db5318c0804c1842658715e2920015c509c71443cb851351ccf612f8148f12dba2f60e5540850cb5d6940c8224ec0a1e1e2a0a095a9c09a7c8f90816d45605d5677505059f1804ef5ecf04cec8fe0435266802c91fae01397fac0033aa2e

  | 6 => 0xffa3bc5fff68ee4efec2c275fe7e0db7fe2665d4fe03b58dfdeac84afdc0f92bfceed96ffcea7a09fcc2fd7bfc443bd3fc371872fb559fddfb4655a6fb25bf9dfacf69e1fac65025fab5781cfa858823f9ef97b2f9882202f9773007f9015559f88c286af7d266ddf716394cf688e814f5ee6fcaf59e4428f55ba9bff55677c2f547a77bf5367109f52ae3a4f4fa507df4caf06af4b7a0b8f4a8a489f4942027f45d343af444c9dcf42962c5f40902bff4083825f3833383f3707a6cf356bbe8f352c9ddf34203eaf1c32ae7f1af217ff1a6e622f183287af0f243edf0b76d26f0a7f000f02a6e42efe92c0eef9f222aef97f69feed24b2ceed1c747ee89cdd8ee3155bbedb6e97aedabc6e6ed312f62ecc5094decbe8d0cec9e1a63ec3ab766eb751b51eb20ad74eb0f88a8eb0666efea98e7cbea62dce2e9e2c4dce98a2cdae97b8478e96fd20be924f7a0e9046264e8fb7750e8be0321e893104ee88e8f86e86615c3e83d9736e83a2024e82a06c9e820c51de8199415e7e589dae79b9b0ce78034e0e759c953e6fa3f01e6e650ffe6738520e638517ee5f828a3e5f3e220e5d04e14e5b0b4b3e5a6a35ce508cb12e4f9fafee4945917e478eaf5e45582e3e45068ffe4066983e3d96293e3bd8fd8e39ae9ede2d42b18e24a5c9fe24424b8e242e469e231b9fae2281f15e1f27119e1a63574e1659185e1576388e1511fa7e11fcc3ee0da8813e0ba5f95e0a1048ee09a0213e02ca7a2dfabe33fdf71a136dec2b014de3fbc10dddd97d9dd9bdb6ddd51202cdd28e89cdcf118b9dc5b738ddc45ae3edc161b65dba98e2cdb85f17edb858ed4db575024db534deadb46da2adae9c12cda7eda88da45a1ced9f6638ed9f1680fd9de2656d946fd75d936d91bd8ef4e60d82fd773d7b10722d7a225bcd77e116ed6ce1bb5d66796e6d663bd78d6528a02d5a0500fd59d817fd57bbf7ad5499515d520dc0bd4bc9151d4ad09c6d4a7cf5ad4965ad6d3b315d5d3b2537bd32a5e03d30a79a5d2e29278d23781a6d1cb51efd1cb2db1d1a14140d142d52ad1187e41d07bec32d0582c55d051ac03d01378e9cfbb69a0cfb7f376ced395eacea41e1fce5ca256ce1a13decdffcd59cd9bc64fcd76af7ccd4265d8cd04e4f4cc55304ecc528b92cc46bb36cc2eca29cc0254a5cbfe8274cbf64abbcbf45d0ccbed823bcbeb4049cb93fe3fcb8c76b8cb7abdaecb1a2b87cab1eb62caa35e37ca532fbdca1cd409c9a21440c91e0a4ac9125492c8fea5a8c8c31811c8c29089c8bcfa34c8b3fa35c8463f12c8139528c7f36168c7e9a7fdc7ce2012c7cd57adc73695ebc6ffcfedc69d3793c6786f21c62572c6c60dd3a8c5f1b98dc5d4a419c596da17c56d6798c495adc1c48a6cbac466c09ac4068abbc3d3ee7dc3b9a3e9c39a6af8c2e38f06c2dd7188c26b07a0c26018cdc232be2dc1ac16bfc16e6072c0f1b271c0c3fd71c0b81327c04a8696c04874d7c0463858c0460968bf7f64f2bf7b2f69bec3714ebe841d50bd9976ddbd7cd7f7bd0b681abc530a12bc3d1fdebbdeae5abacc6bdbbac59abdbaa43ae2ba059846b9f03ee4b9d35547b90c3931b8f3aed5b8f26de1b8f261bbb8d9ef0db8b76da4b8b283c5b88a8b8db87525e4b842fb7fb7cb731ab7ad91a9b7a67030b713962ab6cc0bb4b6abb9e5b6a68429b691a796b68780bdb5b7aff0b5216085b50af2b6b4e68741b4d54753b44e8052b3bff539b35b76cab34d5079b2f5f519b2a5487fb2a10c09b27f850ab245f8bbb1f5bfcdb18a3670b12ed109b11ba785b0f8c13cb0941dfab07015e6afeeeb0faf7f102caf7c8adfaf63cbffaf3d214caee6f207aee6e8a5aea069b6ae1a6d59ad9cc4a1ad443119ac97f6eeac6686ceac54df85abd41441abc2c902aba4e5efaa939530aa8283a9a9c24947a9a78d9da9672168a908b968a8f09966a8cbfa38a8b14294a8939780a885d87da87371b9a86802cfa83433f2a7f1267fa787459aa6cf4fc8a631ea40a60ec92ca5ff06dba4841188a46c3d94a4609fb1a3fd44dfa24677eaa1f2a8e7a17a5089a16422fca162dfaaa1152deca110bb4fa100ad78a0753790a0384a6da02f25c99fe782a39fe3c25c9fd385d59f4f102c9f0ac1389eddd1f99cfefeb09cd94b4b9c7b01f49c41a9249bffab619bebc8259ba3df869b9c62a49b92e0b59b739efa9b6a96f09b451d4f9b1374ff9b0894529aeb31c49a03a30d99e8436b9940a6769935de2998feb51498ad3c309855f5f99802eb0397dc0b4b97bb64d297b552b697a9f2c19742d4349730221b97292bce971f351296f5161396cb2dc6969545d396806fb9967246ba9661c81b9654dd3496423a2896241e3f95ef5b8395e1358f9592a90b958542f694f2506694e0527b94b0f89b94958bac93fa14a393f227a693987fac9394651e936558ce934bee96931d57cd928cca549283e27e927d8ef29278769692620caa9216264e9141c764912f4890911d3c5290fbec169086103c906453d49014cb71900bb7909006c75a8fb02e5a8faadfdb8fa145ff8f915d588f8575dc8f5fed388f5086528df5c2588db819008d84f3728d4810dd8d3ed3ef8d1c36548d199b0c8cfd7d1d8cd972a08cd740518cc529958c9d73418c904fe08c31fa3c8c0571418c05294a8c021fd28baaa8fe8ba40a5a8b559a348b2cf85c8b28a14f8a9a39938a80ac0489d0677589c8b632899fc768896cf3c9895ad8958952a3c88917af41890d990989082f9688d2a7ed8897caf38844b6988824d822875a061b861b233b85cde9b685a06289855e2cb78551b68a84ed579584ab9acc846f7e2d840e9456840a21b983f8ee6683f0c6b283b11ab7832dd2e383288c3382cf015c829323b5828cbddd82569989823acea3820858ed820427a282001d9081b1b2008187f2a0816ee39e8110a4948101276e80d6c4f280ce66438039066e801b9f317f3b39437f0a11bb7ee77a657ee305467eaa2b217e8e5adc7e5ceead7e42a8287e3e83b97e1020e87dc7d3807d8015ed7d7011017d2bd09d7d2ac16c7cfd09777c8d7cac7c44fc8e7c3a0ce07c2a85557c21c9527bf761ac7bcff9e57bbcc9257bb02ab57b541bdb7b36015c7b30db147a9193037a3bfc4a7a2cb3137a2988857a0b078179be3e3b795ca34478e7c6f47896cea47858855577f1c77577e61cfa779a69fe778a579277357a0876d0f63876aebbb9768f12597675be2f76468f35760e82da7604606175c728b575a1bb94757d48e87518c38f750f8cb874ed908574ead7b6743cb7aa73f4215b73f18df27347d052734678c6733e898873051dfa7303697d72f7b5fd72ae9c9972a68d2a729c1bd771ea228071548eaf713c592e712c9368711f6d676fe07d2d6fbe8fff6f5a16e86f4a84f66f0fb6e56ed792256ebca2746e9d70c46e5e4ec76e37bb3b6e36cf476e163afb6df512db6db489336d9d31d46d57bd8e6d4a50276d1dea1e6cbb55556c75fa696bef749c6bb5720c6ba011986b2e95776af215f66ae4c7cb6a9f7cdc6a2db73069cd10cb69966049698634086953541268b0b492686a291a684b1cf467e94aff67e1924167792f746768e49766ea2d1c66aa8121666985c665c867c665c7e127657a137965769cbc6538e68964e3d4ec64d97df1644a3c38643fc64663d02b5c63aec3466206d5de61ff74dd613b29aa60d523a060879995603274f55fd136d95fbeb9c95fb586b95f23ebbf5f22c9635eb62f8f5e95f29f5df0cfe65ddf9f705dc8dabb5d8decad5d7497f85d0d09335d0041995cd42a235c9fc2575bcb7d925bbbad765b368ff05b31e3af5990d74e598878c3591631a258ea66c558dbd1c65850b9a158416bba57d7db8257a40a105702fb49569e280d568d1996567e8c15564af0fb56437da155df1a15559e94dd5586988d54e388ea54af93a95449d8c05422e31653f7319653ad321a5381c80352cf1876522da2cd522bdf1051eaed4f51d8829151c9e21a5181ecc65132952750ffab47508e47a55051d976505123f8504637515040caaa4fb4bbbf4eea90b24ed64e734e6dfd9f4dde2e354dbf64264d98e3464d681f034d5945bd4d4d74e04c96574c4c4cba7c4c0451bb4bff27d54b638f844b5056c34b4c9b414afe18bb4afd72504ab06e844aacca094a449b234a19d2c149ec6a6549bce29b499830a6497beed54971545e495676ce494a2dcb4933267b4910a51248edc60c48e9aa2b4842b029481e3cac47fcdb2f4724da05470bccf246ffbb9746ebfa3a468391ca4610e75e45eeab0e45478dc3452e7ec144fc8fa344f8ccdd44e432f143ec691243838b82434cd53e42d1269a42b1423c42b074f942aeed23429f3029420c661541f1059941811e9c417b81624174def341721a8640bd467a4088f30b3ff9a8033fea20783fe04cfc3fbd036d3f876a623f03cb943ec794b43e7a5e813e4a88273e4781993e35185e3e036aed3de938423cc1c3463c8a3db83c2a77223c03c7fe3bd592c03ba54b0b3b3ac6d63aec498b3adef1493acd72ff3a58b3f93a4a26ce3a3482063a09ab1439ecda2839b91b8b3966f46d393ce40b392ba99039238904390a7a0238cb97e338c3d115384bd9bd38368f7b3825d8bc380b8c313774204436a6988435db6cd235d3a4a235bbc39135b36ef235718f6d3514302f34313551340d893133dc88bc33d5a34433cd1fa43382281833799e7c33050a1e3271b2bc31ff6f3731d387f7319550c1318387c03174fda83154d6f7313b7589311712c130e0868130ba09a730b8ca9030987b0830852ebe2fa8479a2f739e0b2f6f9c3a2f5673672f3709672f21670d2f0226602eee309a2eea87822e4601ab2ddc9f372dbd30122db739d12daa63d62d579d952d403f742d3282b92d2ae29a2d18df4c2cd439622c9a6c6b2c6ad3242bfd16f42ba028872b47dc1c2b3c16932af641992aa4608e2a93cfa12a7f4bf229e560a42913b28828a3bf9c28993678288a1d9628876834283542b9282643a7280e8a2427f5f60d278959892779a4d927545a40274555e22724085b270e98d726d9a727265b7dbe2652e61d264e0f9025de7a64254b87d4253989e924fbc93724eec31a24b27283249bb9f9247a85062474e7cc2465551824534c1123d61e3b23d1722c23bca4e12308b07f22e386e222d9b36622ca2bdb229fd6ce22614dcf2218628b21aaab3f219150c7215523842140e80320e29eac20d599a0205ffec820400adb202676a91ffc912a1efd2e681ec5d7031e5a9d5a1e0c682d1deefb271dee02861de5aff51dde2ae01dc4af201db42d5c1d980b5d1d438d381cb281f51c987bbc1c5ea8af1c3872f41c1cef6e1c03e06c1be831d01bd447981b9f64221b809e881b5587601a52670f1a1ece071a04b14c19cec9b819abdb3619800c3d196781e119406ad919368dfc18f5d2d118f1026118d4d33c18cd0b0c189761fd1870caee1866443e17cce9c017c9ccc4178c21be1732372f171bc7bd170aa95b16feddea16bf82231647fb6115c4f6bd15b76425156388ce152294c1151a2f141504d23a14f0fccd14bee08e1475bc431434dbf3141cd2e713cbe35b135a73cf1334328012d2a5bf12afd0f7126d0475126902a41262435a121acd7711fb8cca11ed408111b8bfaa1139dec4112ffc6010d8ed7210a7760f107ded33107bc66c1062a34f105d5583101c00270f8a8af30f7a2e0e0f3bb5cc0ee8b8da0e93d0210e81ab940e10d9e30dfc53510dd94d5b0da973280d8d360b0cc715fc0be3a1520bd8e4c70b39a94c0b3334eb0b308dc60b2710b90af44dac0af030c40aefeda70ada16f30a82bff30a37c8fd0a1d6ec50a07ff41094c4c87085d6542083f136e07f52fa1078eb1760769767d06cef59d06c5fda9069fc6a3069690eb065d97cf06281a7405c39245054606f90540b9bf051bbeb404e771e5048ab731044ac56003e3446e035ca0eb033f48430307d40702f5f79402b086f402ad3cf70270b2700248419801812be3017f84900166537c012b35f600e768f000dffc2e00d8da0600cfe6c000c404e90039b49b003633d9

  | 7 => 0xfffe42acfffcef2afffcd8d9fffb6e0affa71480ff6aebcfff66be0aff51b844ff4688fcff3bad19ff3735e6feed2c02fee030eafedbab45fed4dbfefe9dde1efe609470fe541330fe482474fe390ae2fe1fd11ffe0788e5fe020717fdde7c2afdc6a61afdc2bbeffd5921acfd4a94b8fd1380fffcd06e0afccc6fe2fc945ba7fc6b501afc456c89fc23eddafc0c96e4fbfb55f0fbcb17f5fbc57abbfb9f2159fb9e0ca2fb6092cafb1f1a5cfb073fd3fb0686d3fafa4659faa8aa86fa9c0a0ffa8f258dfa8d8aaafa7a8aa7fa7922bcfa6eb74cfa67f706fa5470c7fa4a2ab3fa3419d1fa2a4655fa297912fa1f5c3bf9e161daf9b2d007f9aa062df9736566f9562616f955de18f9499350f930a963f92608bef9257695f8917af2f87f831ff833319bf80ea49df809d766f7e11a26f7dde79cf7cdb9a7f7c09646f7a8c79bf79faad8f76ecef5f74030fdf71b830bf708cfcdf6f83b45f6e99e5af6a7d32bf64dc157f61f4e2ff614cc35f60b28b3f60a39f6f5f3629af5bfd1d9f5b42250f5ac7c4af590822df57c6f06f54e32f3f5488ff8f53642e4f4bde3e8f4bc3aa6f4942027f4571408f44f07ebf44804d6f40b3e23f40314e4f3db1160f3ce9d53f3b0edc6f3968033f38d66bbf37d3eaaf374dc5ff36d825df36cb51af354735bf34f7ccaf32dae55f303d0ddf2f4efeaf2b3caeff282757ef27ffec8f27f6dfbf2702fc6f2680f20f230a0a8f22e5aa7f21e6492f2106c61f1c32ae7f1b96237f1b4b596f1874d3af17dc44df17c2cdff17b86f9f161fb32f155722ef14b69a1f135c86ef1258948f11a101af0f159a3f0effc8ef0a7f000f04a1850f04233cbf041fd0df039cfc9f0359954f02891ebf025662bf01d9dfbefef0e66efad86a3ef820b84ef3c698aef369ea2eeed245deecb285deebfab0eeebf5d72eebc1782eeae17cbee9d8ad7ee91f233ee7d1c96ee5dcfcaee5a148eee51bf2aee512395ee35e061ee1f9c9dee101512edefc724edd8ec20edbfdd1eedb208ddedab7c5ded9f5e9ded975374ed68bcabed60814eed4b9590ed389f53ed3063f6ecdde4eaeccf475cecb750b5ecb41bbdecac1966eca97c67ec9f2a04ec91d2e1ec9071a0ec8de869ec786800ec618b2cec4dd047ec4422ccec40eafaec3b6589ec316dd4ec21d009ebfbc0bdebf80cebebf706f7ebeb537aebd57f2eebbef701eb868d4aeb856ee2eb7f5cc7eb7be0aaeb756fd3eb6f3d14eb64253deb5b59aceb38d952eb1c2c3eeb14f41aeb0eeefaeb0666efead19913eaba9187eaa3ada2ea86b80aea6c096fea6b7fa9ea43404fea3715abea2a08fae9d51f7ce9d287f6e9c99c1ae9bd9764e9bceb04e9b99593e96d3b44e96b6066e94c1fb9e940674ee8c17dbbe88a71b3e882b749e8306065e7fda181e7e8ad96e78291b0e762d8a5e758d31ce716f96ce713d395e7108e73e6ea621fe6e0711be6dc1031e6d38107e6cf7780e6bffb3ae683a38be67e9510e653a7e9e638517ee61d80c5e5fc0d3ee5ef6f38e5e33c65e5dd2105e5d1673de5d07050e5b339bbe5a4a973e588cb5ee560fbb3e55961fae50c98abe4ed7572e4d4ed76e4c9c952e4b137f0e4979eede44f4d5de43b6cc7e41fc593e4180d5ae3fb139ee3e464aee3c7150ae3a9f092e3a57ec4e39a0167e37f3c37e3683998e350a904e3011e88e3005d53e2dc242be2b332a7e2a82cd0e2923136e290f510e2807643e2602474e242e469e22e5584e218af75e2013c9ee1f8500be1d352e2e1ce4268e1b9f9d6e187bcfde16e01b4e159fadae1589230e154bb29e10965b2e09cdf76e08a0fc4e05fcc12e0528816e041de85e0344b9ee02323ede012b388dfe56b86dfdf1d44dfdaf42adfc235a8dfb7b907df9d1b68df97c7fddf8dc211df7fde41df6cfe10df45c290df4434f5df2467c1df1d5444df0a2fa4df006697dee5eb9ededff6b5decd5e59debae30bdeb6bb0dde749be1de10c10cddfc7f95dde722bbddd13aaeddd0ab9dddcc623ddd9bdb6ddd616c39dd4e51c7dd340992dd28e89cdd1a663add142534dcc4b954dcbd66a8dcab4728dca6658cdc79c4f5dbe8fce7dbe105f0dbdb9418dbdb4a20dbd4fd7edbc8e60adb54a600db46da2adb3b8c13db2fbe5cdb2a5611db2229d0db19cb21db085c20dad0ee56daa9f39fda586883da55cfa7da468a83da3d7f5fda28d3dfda203c60da072d5ed9f1a1afd9f1680fd9f0f6f3d9e4966ad9e304c4d9c378e7d9beea99d99c54e7d993e143d966f6e5d9635227d9557699d9255941d90cf779d8debe73d8dd4179d8c0209cd8664de5d84e9db9d837fbdfd8263ae0d8109a61d7f2c5a9d7c2fe26d76cf71fd759507ed70ddef7d6e8a2a1d6d8202ed6d057fed6c23b2ed69d91b5d6978071d685d01ed63875b8d62714bfd60b2803d6082e03d5c70ba1d59da9ced57fccbdd536d313d517cafcd4fdcdbad4ec5fe0d4e4e3efd4bc9151d4bb96f1d4ad09c6d4941440d480e460d3fe11b6d3b47e69d396d4d6d394b706d3752922d366d5c0d3549493d2eeb277d271b104d23828e5d23371fdd22faa50d216e319d1d7033cd1d61b17d1b106c3d1a7c917d191d9c1d14f2415d12d63bed113adc4d1097b7cd10601aed0fca211d0e358c5d0da7737d0caa319d0aa59dfd081dce2d0705167d06c4f96d0582c55d01e1a69d0106616cffed9bccff05be1cfd74b54cfcd1b91cf821724cf771327cf32fb32cf2f1b74ceb09617ce941849ce8b08e8ce7e51aece706c29ce6ed63dce66cc40ce3f13e6ce3d77dcce1592a8cdffcd59cdd378b6cdcc8c8fcdbffd57cdb13b91cda1bc2dcd9675b8cd594f75cd19d4d9cd0430cfccfdd445ccde2243ccce85e6ccc9987bccc12c4accbbacbdccac3cb3cca7c15fcc8d66e4cc35875ecc2eca29cc11b4aecc056a06cb9082fdcb7abdaecb79f5b9cb751504cb2c9e1bcb244508cafb5e00caf707ebcaf69de8cadb0e28cad91744cac7e68ccaa8956ecaa74edcca8c854cca798cf6ca73f5a1ca530fc9ca447f02ca1fbc65ca1cd409ca08bd26c9f5ab48c9f244bac9cf9c9ac9901accc97baae8c966449ac9569145c953a21ec9479f13c928f175c8fea5a8c8f65072c8c31811c88cbfb8c8860ce5c87f6328c86217efc85a4122c8406b93c820bbb7c80b4c33c7ffee11c7ef2dd6c7daedb0c7da4800c7a3226cc7950440c78dc592c7719291c74f9979c73a11dfc71524c7c706ba33c7038f0cc6fd63c9c6a21b05c62d9aabc622de20c5fe1678c58a8197c589ddfcc55f91f5c54a595fc4f51105c4e22eeac4aa9967c481d8d6c481c256c4624babc461a6bfc44635dbc4015290c3e101a8c3819187c37f1560c3134547c2fc1970c2b58df8c2b2ad65c2a980a2c29a4a71c285d077c2613b76c244ab36c243fef1c2324d00c1e661dfc1e53fbec1b73d38c1b36fd6c1b02177c1a37091c18ab9acc17b3761c163b630c125c193c114eba4c0f94486c0dabfcec0d84048c0ca1207c094e3b1c04ef9f0c046cb14c021a113bfe9088cbfa01874bf8ab318bf84df59bf38b772bf38228bbf374ad3bf19c35dbeeab5e2becd1a04bec89ddabead5317bea58c30be73280dbe4e0c6abe4b4ed4be3f01c2be2665cbbdecfe0cbdc20062bd9fae7bbd944364bd92136abd4a43a6bcfb2c31bcf73650bcbd7796bc59c363bc5694d5bc35ac1cbc2396afbbf5e96dbbef31efbbe600c6bbd6747dbbc97de9bbb4999bbbb490a6bba529c0bba2e95dbb814a70bb6d9b8dbb67d79dbb58d208bb387c98bb29f587bafcb5cebae85d68bacc6bdbba503a93ba31e244ba00eb97b9f05071b97d9d18b96c838fb96c1899b928b9fbb9188e61b901af2fb8e05fdcb8d90955b8ce34f5b8caaab1b896ecd7b88c51c2b888d51ab8705f32b856c340b8509ddcb832a033b80af289b8060ff8b8017202b7ff4c6cb7f69b15b7b993d9b7af9c26b7a67030b79e4931b7989650b792d391b78d7aaab7823dcab77489d9b75b288eb71b27c3b7161539b712debbb6dd1893b6d54f72b6b388b9b67c2db9b672b06db64695d5b62db8b6b61d59a0b6114693b594c77db5904f04b55cd304b5198643b5158f08b4f42c9eb4d84430b4d006b5b4b2055bb48c350bb481b0ffb462d01cb461f8d1b455a79db440eb78b43d67bfb3fb8864b3f92127b3dc3c2cb3c8faa9b3c84b32b3bd3ff1b3b01c90b3aea989b36cd9f6b366ae59b31f5dfeb31bd277b2fa44f5b2e907cbb2d621c8b2c51562b2b03c9db25fbf10b253c8acb22cafbcb20b851cb1f5bfcdb1f4d93ab1eeb5b7b1c32dc4b1c077a1b1841b34b17aa08fb1565d77b1412dc4b0be092ab0900e64b08ee27fb06337c4b06123b4b05ec527b00e4566b0078bacaffd9739afebc656afd9f643afc2fee5afaea977af806a67af7fe4d1af7d2fa1af60f8d9af0b1b18af019a16aec6d546aebff5b3aebb92bfaeb3d1e8ae67e813ae58cb10ae31ea46adfeb5d5addb3ce0adcf768fadc2fd49adab1995ada31cf6ad9800d3ad977fccad72f360ad666346ad3f178dad3aefebad007bf9acfe97e7acf7230cacf35898acae5d28ac894448ac860b6dac74f5f2ac58e7fcac502379ac41057dac3fa741ac0d2445abe6edcaabc3eaabab8baa07ab1f6e7eab0a5907aa932727aa8001f7aa7ee31faa33702daa33256ca9ed6deba9ec771ba9c1f064a9b5f1aea996fd99a9747884a96e2754a951ace5a928259da91fea40a91bc0a5a88eb04ea885d87da884918ba873bcdba833fb1ea8307144a820f41ea80ac904a7ee776fa7e253a6a7a3ffd1a78aa4caa77d05e1a77b3f40a73e9f39a739ff3da72afbc4a708866aa6ec7322a6d09127a6987278a67e2bf3a659e579a6540e07a5c039b9a5a5b720a59c8c44a57200eaa56aa6d2a550604da54c8ce9a53d363ba52fed98a4dda077a4c14b6da46addc0a45cdbcca4553feba43bddfda43ac068a42d0da3a3c91e25a3bb07d5a38e4a1ba2e4cb2fa2dd09aca2d51feba2cff765a2c07a54a2bf0022a299f86ea28fa18ea28c48e4a28647a5a270f199a26b61a5a26abe7ba2632648a217bc5ba1e943dea1d1ec56a1c7eb10a1a3c2b1a17e76aba17a2bb7a173ad4ca16b2578a1643026a15d1637a1375f18a128e0a1a0d0eec1a0a16df5a08e4fd2a08e1bfea0835b3ca07bf249a0785cbfa00793a49ffd55fa9fb69b549fa2db879f9e41fb9f93f40d9f7446269f6a2c609f59c1689f5726819f4b81809f460dfe9f43f45c9ef7d51f9ed52efd9e9189099e8fb5b09e8eb13c9e7329a09dd5295a9dd3d7eb9dc3a6b79da9fda89da22b3b9d7fd3d29d795aaa9d6017589d39a1289cd4d4c69ca89ac69c91a4de9c90400d9c75d29d9c6db7639c6bb8399c65e0ec9c55db0a9c1954169c185bf39c13336d9b8ac6719b7ffb129b5c845a9b2481719b13ee0b9b08ab589afad86c9af214329aeafdec9ae19bb49ad88e009ac68c049a9f05029a908f1a9a6ade699a674fcd9a55042b9a16ad239a1541469a123ff89a03a30d99ffe04699f98e5599bbe88799bb9a9499aafa63999060939988dbcb9987c001994acfac98f9d75c98f6876e98edc2cd98c2e86c9892e677988a881d9866988a9862c91f985f79a498594e4e9841a5e0983cf87f98349d2098047fc897ff6de797d3ba1797c96d1f97a9703497a3df2b979b198a9794c8359751bc6c9733fef0972d9c839724e75d9722589e96f5161396df2a1d96dd5dd896c074a096bfe2d996b0f4cd96a71ed09699fb6f966014c3965bef9b9633246a96303e019560c85b955e23ed9550993d9537ae6995324cde9514df8b94c507f494c4daa2949fc06294958bac9477d99094572a139455d6f9940df7d593da130493bd880593953266936eede29367e8b3936508239355dee0933ed08a9339d95593196b14930d9c1b930bd01e92ff248f92f5838892bfde4892b99fef92add8d692a0150a9283e27e9281a0809275a091924235f5921d0b3491ffffde914f8400913ca6f6910ec0ca90fcc0b890e5df6f90b7631c90aa9fd89086103c9068236590562698903c1d219031955d902a2a499026d1b09024ceca901f0980901c701b9003b0a88fd13dc48fce7aa88fce5bfe8fc5b8d88f9dc04e8f938e738f8392778f7997418ef703248ef604778ee054348ed79ccd8ec22a888ebc4ac08ea3c0648ea322158e9ac3f38e99d7ff8e93fa528e7262188e6d3e058e64291e8e581b938e471fd38e4443878e2905f68dfc4cd98dd813b18dbb406d8db929348db609f38dad58df8d25a7508d0266ea8cd764498cb587428caa787e8c99e0298c8569ea8c6ddeee8c61b2758c1d60d58c12047c8c09c91f8c031a508bee74818bda3fbd8bd387e68bc062868b90452e8b87c7828b86da678b788f2d8b7248228b56bd0f8b40be448b1a50238b0ad2fd8af6260a8aef5b2a8ae342f08ad0d62f8a9ac5928a8d8f188a840b348a6c3b718a30f11a8a1f223289f8657e89cc9cd489c4940089bf02e989bb011889a0abff898fc3af898ae3c0897d454a896ccbeb895846ff894d8b3e89469f64893cae93892f2004891ac83c891369db890e714688ecb0d588d1798d88bcdea0889de7fc88567cb48850489c8819cc7787f4f05087eedb9687cade5087c38a9187c0a8da87bfbbe587914406878a5bdb8786c4c48764442a874b57538739d3f7873616f7873426d2870121c386ec3d4d86e2663386ca9a9586c8cd2186914e0f86888bf88673edb086377b9986296d18861b233b860d59be85f8078485f6ae5f85dd1c3185c8a47a85b9d644859d4e04859952f58565e68a8550e9858515c0bd84ff678884ed579584df347f84de079984ac9156849930c184903c5584648be28445a7d98430a69383f6e66e83c794c183c7540f83ba9bae8364f941835f709b83527cf1834e2758830c89e782f1728382e1bd0482d8a56982a07a33825f248381e843ba81e084a881d4be6781a4a10f8187f2a0817bedd481764b6e816f6d39816252bd8159fdb581382c588129e05d8101276e80dd902c809e4afb808a6306808a313a806e5497806a7245800bd9967fee4eeb7fe0d3757fd74da57f95a0f87f8e76827f85d21b7f5cd8d67ef73c147eeca4697e837bfa7e5bb3c77e4663397e3f1f497e3b214a7e18145e7dfdccea7ddb021e7d9fc8967d7bc5137d6abdab7d3864597d0ba6627d02930b7d006f627cfe82427cfd09777cd866c97ccb39637cbddbd67ca5c7667c74378b7c63e3877c42b2347c38004c7c27e6cc7c095f2d7be17cee7bcff9e57bc158eb7b9a32f07b93d1577b4df8af7b3dfe137b2c31f67b19a8ec7b034f1c7ad322cd7ac540dd7a9ff3777a795a0b7a77a2c87a47f6087a3704ea7a353c397a32d1a37a2bbf647a1bbf087a17d8b079ed86b479dba38579b2576979793a5a794fb2db790993c178f2436578de79d778bfeb7c78b8479f78a16e4a78a15dea788639ff786ba91d7867fa567863a909784166ca78407ad6783967647805b6bf77febe6a77e9962877b832f27787e6557753fbb67742ba8a76f43ec976e13b1f76aebbb976adf9b376a509617687d301767872db763658737619237775eee9f275d0924375cdbafe75b3065975a9bd2775a65b817584b6f2757d48e8757b60f6756c4804755a3f4e7551502675050b2474e4237074ca967074af06dc749fc7ce74681d81744f91a47430e2ac742d21ec73cd967a73a707ea73a4064273912d95733c5b197323cf7973099c5172b236ac729c1bd772867069725297a6721d3f0071ff3c0371d7869c71bfde5971a29d43718dde35717a740b7171bd467170aff9716c01d570ad376c70367602703071c2702d2a9f7019e2dd6fd5faaf6fbab9616fa688ed6fa3a1706f83bf086f5f27476f4d996a6f4280f96f0390916ef149a36ed3a6276e920bf86e7362dd6e6837c56e3a24ae6e381a6d6e35f6426e0c69056df512db6dc8af086dc047bc6da8cfae6da570286d96ad7e6d9104c76d3fee776d30b40e6d2a57846d06fd956cf960046cea359c6c97621a6c5635736c4e4b716c0a92a86bddfe6f6bd42fce6ba011986b7b613e6b63e1966b607b086b45e9f06b42ba9a6b3803cb6b1c38226b1264c46adecf2f6acfd39d6ac952116ab836236a9934b96a35ee246a157fe369d9737369c9098a69bf43ea69befcd969bcdd9869962f3369882a7169855eb4697437436973adca694cc3d7694476ad693cf7a168eee52168dee12668be467068adf4c66881456468264bb6680771d867e11b3267caeccf67c2ff426792972b67723f7d6762c44f67279b8c6721780966f1d8f366f0b7df66e1f04c66b0802c669ed8e366943cb9668edb656681dd8e6673f01666626baa66615cd865e54b4165dae5ab65c7102e65918779658e339c6585af1a651fde1d651464c964e73ed364b57e9364a0f3c7647497156460eda564574924645031f6644f71ca643fc64663f00c4463ec5d3163e6943a63affe51639d9949637010d16352b2c6631fdd31630238e162fb3bf262896644627fa4db627e2d50623710fd6216f85d61f7257961f19b8661d13ef861cb2f2d61c632db61b7b4306199cd58618fd7616119492660df89a660cb900260c7a30060ab2b3560a626c16058c28a60549c8a602a46b260200c25600c9b9e5fbf51d85f90f34b5f559b455f3d29f95f009e935ed10aca5eb714a55eaa990f5e9710d35e8cc0bb5e66ee8e5e3fc8a05df887c15dec99bc5d66a5b55d466ca25d0d6dfe5cf25e275c992d9f5c624a515beaeb635be3e0345bddc97e5b5f274a5b5ab4ad5b4d31ad5b41fa015b26255e5b1335de5b024ba75aff1d295aec48525ab5b7915a81ff085a791f275a6d152b5a4ee2b65a4b7c285a3dcb615a3150615a0523255a01f1e159e0457159daa189599e6fcb59989e795990437d596d82ba5954ba96594fd7a65919073b58f43c4158b695f95871ed455865ae6e57fe718e5790ba01575fb6d057392b2057176db95716ab9c570aab8f56c8144a56a002db5656d61756437da1563a0412561b8fde561941f2560df6fc55ee04a455df1a1555b55033558f16ad558a04fc55667bcc5511055555071ddf54c72171549f6d49549a8612548d944c547df78854582a2b5457c44454524f69544d9c6b544a997b5442919e54249e0653f4061253c7f94353bffbce53b7d32a53b67cf3538a9fd4533cd20a533ac0ae53398b7b53232cd2531a50a152d78d4d529fef575286e9d152869450526435e25236a629523690af5227e83b521db54c5216976a51f5749d51a1b01a5197b215519540a75181ecc6517a1b79516897e95109672650cf287450c98b3a50b02e4950ab2c44509bf733507bc38d507ad8815066dd12504637515039117d501a92ed500b50524feaabdd4fca6ee54fbb19104f9a121f4f81d5ec4f80af6a4f382a504f36afee4f2e56d44f262d194ead4ddb4ea926394e9d23e74e94020e4e6cce354e5d48004e59e1724e0f40dc4dcccd1a4dc762004da492f64da4887b4d958b714d94aa4f4d8deb524d746b234d67512b4d6200654d5f15ce4d53d3494d4d74e04d3a69214d37421a4d1ba4714cfe47144ccddbdc4ca8dbb84c601fac4c3826c64c23801f4c1a4e174c0e8fca4c0744b14beb0ab64bab69714ba771ea4b96327c4b8d65654b7e8a824b7318c14b6faea14b51d1d64b21afcb4ae6ced24abdd7ef4aabb3444a55b0ee4a51ce0c4a44e39b4a3a53634a3490f149ea870d49c6aefc49adf5f549ad6e9d499830a6497fe8ed497919af495bd2144930e753491d2c2a4915c4294907256348f8c70e48f0244548edb02c48a9d54a48984b71489365da488edd7a48879a064883f8fb4874f03448738653487192dc4866e933485883da481feed34810411547ec624147afc6bb4788b227477fcb78476c162947464359473f1a49473cafdf471f0bbe471bcf5e471ba43d470f22f34709f1ef46e19cc746d9d49746c22d8e46ab6c89469dd67d468f6b38467bea984641831c45ee03b845d08c0a45ae908c459c92a1457a6a0a4575e839456d38c1456c12574566cdef4551cbd245478dc3453f1203452c34dd452976aa4521ae7a4501ce6c44fec2b144fdf79044e89cd844e64c2a44b654c944893dcb447c3c3b447743e04455e1d3442e046e43fc785f43a5c70f4378956c4323ad1c431e4cd0431425914308800142de753142ae57d942a61bae42a4d32742a3772c4273d196421e02714211e14d42051f3e41c3054041b82c3c41a52e36412bd92a40c30780409997ee40897f614058153240544a0f403d338740279702400d42cd400774994004236a3f9bafe83f9567913f455fe13f44d59b3f420e393f3821a13f28dfbb3f0cda493ed9d84a3ec1a7e33ec0499f3ebda6123eb9778b3eb1489c3eaf5f583e9c78783e6f70e53e5aa46e3e5030383e4133983e3ac0103dfb14153de408eb3db7d08f3d984efb3d9427593d8e82323d7f44923d57cf553d4884c43d1966a73d18faba3cfe898f3cf3b2353cc1b1673cae75e33c66e9243c6275543c5b53023c41d0b03c2569f83bdd33863b84e3713b7b59cd3b372ad43b29a0d13b20be503b00566e3afb06ff3af122303a9f385d3a95e5f43a81d6bf3a4ba42d3a45ae893a0ee3ee3a03dc5539eb656b39e1d97939bd061939b1f329398ce8c139540b1939493fd03940b4f6393ce40b39238904392308ad391ab94938f9297d38ea4004388a1de9382cd57c381fcd8e37ffd4ab37af866c37a22b413786fab63765c173373c2e4837348e29372a33dc370304b136f1a9e636e11f9236dde4f136d8737b36d7636136c444aa36747eb336721233365ca2af36368d4c361a6cdd3619ade436075efa3606c28335d3a4a235a0eff535966da9357ffaba3578b6993567daf2354c5f71351aa0bd3503509834f91a0b34f6855b34f4b9a834e5fff534c079d034a4a3c63488b4a03449d30f34395cd6341a0b2e3411cfd133efd6ce33aca2fe338ef23c33822818338095df3325ddf73321284c3312d9af32fd9e1832e2ae8432b8e56d32a28cdc328791d43268b7f53250e07f324fd3e6323eee4832301658321835b3320b291b3208360131af57a731a6b44531a28ca3319305183176e2b83166349f313c924c30e352b630df5a9f30d90bb7306f1b02300e8a0e2fe825f32fc7245d2f9707052f5533632f4a9b022f44bd7c2f4335782f13db982ef86ea92eaf95252ea565882e9d50c42e7ca6bd2e5cf7a02e459a972e3c56132e2d0f592e1e5d662e1b447d2e03ba9e2e0101c62dfdb85e2deec24d2dc1dcf62da519ae2d7d647f2d776d0c2d3e27a72d3c0c5e2d18df4c2cf7bf972cf5fdd02ce8a94d2ccf0a0b2cc4efa72ca0bdbb2c341bde2c2c1fd62bec0e082bea9e682bab2eaa2b95fa862b8952e52b86528c2b5ecf132b5b62322b5b1ac92b123e2c2ae5c8ab2adc784f2aca6ba82ac8b5bd2aa4608e2aa37e652aa2a1bc2a88f3932a6fe4912a69aa572a32784b2a3022382a27a0b729edda6d29a4d2f3299760b1299691c7293387a6292dac452914c57b28f3703f28dfec9628cf829228b78427286448e92845115028331a59281613bc27f1ba2e27e7d66f27d968ca27c2145f27c132d127a1b6ec277e49762731fe552725e449271fd1b0271af39827054eb32702cf5b26da2b9626c0a0872688bb03267502522673b17d2668543e265d8471264e69eb2638e71e261cb224260d8bfb2608c9c625ff367225facfb525a9136325a717dc259edce1258ab549256c318e255b16e1252ec12924eec31a24e9763a24bde2b324adce18246177a4244ff352243906f82428799623cbb4bd23cb635123bfa9a323b586c5239d4d7023988f54238035dd236adcbf233f86e3233b72f423191e8c2313a28d230df56c22faadf022ddd81422dd8b8722dad7ee22d1f14022d0890b22b42278229fd6ce225c78f6223b74a32210bc2621d3785321b04d3221674038210f6467210ae25620fcacd020f7861e20dd6f5520d7997420cc81c920b023cb20aebb1120a00818207e0638206ea1ae205cdb98203720602027936c2006c51c200345861fcbf70b1fc6e8731fc148d81fc10fb41fab5f5b1fa6d6931f53cdfe1f52bc391f26ad681f1d3d8d1f0e7dc91e7e49db1e5593961e51ef9e1df46d691dec0d821d958e271d77957b1d4fb33c1d3764701d309bb71d03b8901d0207a51cb97c861c71856a1c5f17741c1cef6e1c1bbe891c03d4021be1c87e1be0fef01bd7b3981bd350761b4ebe0f1b353a091b31ab2a1b26ee9f1a9298d71a5db7261a52a06f19ff801719f49d7919a7593a199b21b9198fafbb1981e47d19742c0919699e211958469b1927d09618f13dd918d67f4518cd0b0c189982e418356f9a1830e42b1816f3221813fc681800707a17ffb5d317f9d39c17ef21fa17ea7b7417e2f8ea17b26ae817b2672d178bc5ba174a3af7173608be1732372f171a816f16e93d3816e567d016c3f33c16b969a216b7805516b0b33816b0436f16933bb916440264162e1345161827a815ded04d15c3db9b15acd9df15a7951c156da652153f36f2153571761528254815153e3815089c5214b8ccf814b412f5148ec397148c6b821489de011456c9b41450fd291435f8b61420dfd113dad0ac13c08db11361d06c1348e912133af4721310d39112e6d5e112ddf69712bb68521272e59e11fb46cf11f769d011d98b9c11bb8a2b11b9357111985d051189ce9011844c2611771e9d1166d35611651f47113f01011136c79a1135f9121116a2861111d7be1103074010e209f710d8a12c10d59cfa10a97232108eb645108d76ff1067435e1064bfcf102e06061021a12a100d09f90fef643a0fe7adf00fdc78130fa18f3e0f9cfca00f4dbab30f1705fc0ef25d590edb268a0e9c238b0e5470ef0e31ef690e1a67cb0e061db40db808b60da6dbad0da3e0fc0d9a0ba90d76be550d746fb10d7275630d664c7a0d581e330d117f960d0f03080cc7df220cb4203e0c62969b0c3ab45c0c2897c70c2261310bf87fad0bed08c50bd59b530ba57dfb0ba424720b83b6310b7035b40b5c868a0b44261f0b2636380b1cc7a40b1408c70b109bf60b0643090af660bf0a945f830a5e4d4c0a43602a0a414f960a2fe3cf09ca750f09ad67f3099a57b709948204097299e20966dc7b0963f16d095186af094c38dc0934c04e0930e91408e014880898434b086abed808095d840806423b07da324707b5fb4e0769767d0750ad56074959bc073a5c12071d676f06f3447806e35bd106c3272006b5a0c006aa5ac3069b5a3b067bd9ae0677f5bd064921330630d5790627ec0b05f1fcf905c9ef7505a8d91c059b327f0596949f056bd3cf052e6e42051f1a5c04c9649404b371bc04847ae6046972400405aa9504003f5803f9434603f6133a03852eab036974630366606c0359be3603569050033bfafd02fca77702eebc9f02e0a1ec02c95ae102a72d750294c2b7028ca987027f98d5024f7b7d0248320b0242e2d5023c3f98022af80701fbd4b101dc127101d2aa7d01c89a4201a28d2501656e830135f398012c26d7011134c400fd0ad000eafe4900d51c1c00b23a1a008c09020070fbe50066ca2a004919a6

  | 8 => 0xffdfed4cff72f2bfff4399d7ff3735e6feb6429efe862546fe1fd11ffe086f51fdf8bb53fde8612ffde414dffd5e1eeafd0d1414fcb7694dfc79db55fc3a826dfc2beec2fc0c96e4fbb8db50fbb68a56fb866cfefb252653fb11ca05fb01d681fac379abfaa8aa86fa6eb74cfa6a3616fa5470c7fa21cca6f9e5d851f9b89821f9aa062df992b633f98c0792f9232954f8ce3f68f8a85928f88202caf85b6ab9f82e0244f8096889f7e11a26f7d80f7ff7c988adf7c31c66f755411ff74bab59f6ce8624f6a7d32bf64dce5bf5cedccaf5cb3182f58a47a8f5890856f570bc8af5450058f52d0092f51c42e0f5189a89f4fce33af4e9381df4d17136f4c5e7c9f4c188ddf487a8d8f45da4d6f44804d6f4305272f3db796df38d66bbf36d825df35e5481f35484b2f2a8c365f2a14d59f25ca5a4f258740ef249b9aaf23d05c0f17bdef3f16dbd7cf16291c2f13da024f113fc84f0cbca28f0a38352f09c8df9f0972909f0451676f044c5f7f041fd0df01ff4d1f01d9dfbf00e6928efece7f4efaa0137efa5d995ef698191ef5b5010ef369ea2ef030681eedaa09deecfa836eebfab0eee3a3b06ee39d027ee06e09aee04c4e5ed889a93ed511f3ced40e866ed1eb575ed10cb0eed0aca17ed0504cdecd4e775ecc3a2d4eca5715dec751ee0ec225b04ebf706f7ebdcfe71ebb8c775eb975b34eb868ba5eb131141eb0666efeaf604b6eac5e75eeaa2afd8ea9ee210ea87d604e9ffb963e9d723dfe949c283e9467df9e922694fe8fb14b0e8e9159de89e8c18e897b46ce88f93f0e8306065e7f0ce4ae7a81fe5e780142ae762d8a5e73ff729e734cc0ae72d5700e6ae2f91e625a49be6036933e5f58743e5d29199e5a2d68ee58c2322e55c05cae5532e75e5151579e4ff2315e4fd0438e4e9eed6e4c9c952e4be537ce4bdb1e7e4576a1ce429ee84e410d8ede3fb139ee3e21e18e3473e20e3230050e3180d35e30efe9fe3005d53e2d4664be2c9cc2be28c0505e231fbbfe21e780ee21c827ee200e350e1bce19fe1b6286ce196bc31e1669ed9e15be744e0f24e30e0e48892e0c9f997e09d11a3e03ec195e0068875dfe8d63adfe4d55fdf83aac9df82d105df526ce3df4f7e40df4a6941dee0bc47dec1cfafde99ecabde6b9a6fde64184cde018f84de0167b8ddc8e77fdd1a8264dcc4b954dc8196cddc523aa7dc26a88adc17a253dc061041dbb4ee03db75df26db64b3a6db631406db5fbe86db46a629db3b8c13db119242dafdc8a6da9e68abda8ca6a6da59eeb4da53c842da4ac7bfd9f1680fd9c796ced9958af5d98bc2b3d8fe0ecfd8ef5a7ad8e04451d89cb841d895a8ebd892ba48d880db99d874059fd8274606d82002c1d8109a61d7dfc440d7daca93d7dac990d7ce72e0d7c18ed4d7ab67bcd799ac95d74c00fed744a6a1d71edc6dd6f2df0bd6d057fed6c5584cd6bb7ec3d69fb181d60fa16dd4ff4610d4ec8a2ad4e4b9b7d4db0bdcd4da9e33d4b3b8fbd49e2e3fd4431addd4097a3bd3e9cf0ad3e865add3cfe2aed394c2a2d37a76c9d36c177ad359b3d7d346117fd2942e34d28fb874d2511b9dd23945a8d2238059d220fe45d191d9c1d16954a7d14cd66ad10362fbd100f778d0f06e3fd0c050e7d08edf47d04c1b9ecfe2ed89cfb7ace2cfaf2007cf878f8acf5f3791cf507002cf424df3cf2500ffcf2052aacf1abaebcedc8313ceb8538ace8461f4ce76ad63ce0fe527ce0c3fd2cdffcd59cdf86746cdf36794cdf2b12ccdd856c0cd9e5eeecd8b51e2cd88c0efcd5acceacd2f3acccd1213bacd073e59ccd7feaacccaa537cc97b515cc81a06bcc8170a2cc816597cc64d96bcc63fa6fcc019405cbe98bdecbd8fc3dcb5bd117cb2cc81ccb2b2019cb28b0b5caf5780dcadad485ca76eea8ca431bcbc9e845f7c9cf393cc97ee937c960ff55c953a21ec88aefddc83fd7c8c809850dc7a1a7f1c74f7bdac710eee9c6fe1997c69e28dac69b903dc5f8dd7ec5ee1dcbc5cdaf8ac5c4dc73c5be452ac5af4674c5abdfe6c57f291cc57bc28ec575a847c5702fefc54ca6aec5405a18c506615dc4b32e7ac47c96f8c43cd7f8c41e108dc3de7b5dc3cd3c67c3c3eb72c37cab53c33857d9c2b4b831c2a980a2c295fd51c243a970c23c4bc2c2257a2fc2124050c203d998c1f9602cc1e73bc4c1b2f891c1a77770c196b7ccc182a476c13f9262c0d84048c088a911c046cb14c0382f05bf7f4654bf57e0edbee593febecd1a04beb36b99be7448d7be4c6698be012de5bdfebb01bdcf2804bdb206dfbda2c445bd768585bd7276ffbd70dc02bd6e38c6bd5b6eb4bcd3acdebcabd453bca7a3debc6ee73abc280d05bc1c9ec5bbf5e96dbbe600c6bbdb3c3fbbca2330bbbf5857bbab1ee7bb9019f6bb34f7a2bafe3ab7ba75ab90ba4a99fdb9f3694bb9b0b768b9899060b91ed55cb8c2825cb8c24e61b8bccf09b8aa8dceb7bc83ffb7a31b0ab7a057afb7a0578db789f104b7823dcab775f348b764f0fdb737df75b70cdc2eb6de5505b6d54f72b67ea181b66de738b611f194b5c0a6bdb5a0260db5799e8bb55b591bb5249250b51ac6cdb4fbb803b4ac97e3b4a89ee2b46ee564b4508803b4206aabb41af872b40d86edb3f83b1eb3cad82eb3b8e798b3b3573fb39ce20db388ca40b371b793b31fff5fb31d708fb30bf7c2b2d87e21b20e8b1ab20d04ffb1e840a2b1a3af08b1879136b17993efb1484ac8b14234a3b13397b8b125e71cb0f61eb1b0ec6984b0bfb013b0b92f50b06337c4b03fbbeab013b958b00fddb5b00c49fcaffe62dcaf7d6251af7d2fa1af526b4daed8f92aaea8dbd2aea0da36ae67ce58ae60d9e4ae58cb10ade30bd5adc86f22adc4b364adb0d39aad8cdfcead88b008ad7a15bbad77a7b3ad3c2adbad2d266ead007bf9acf35898aca84f5eaca0d7ceac80698dac685df0ac644769ac2853b2ac0d2445abf3141bab146abdaad60e24aaa37edcaa932727aa913560aa2fa58ca96e079ba96049d0a951ace5a924a58da9005158a8f8b2b9a8f48b17a8d91e67a8c89561a8c46dbfa8b83313a896c2eca894897da891e43ca88815bba78a93bca757f72da74b7771a727de48a7204eb0a6de4549a6d52789a6bd51c3a6b56da8a67e2bf3a6706276a6578462a618084da5c5f7dca5bf6931a59decf9a566259ca550604da507ec91a5052bd9a4c94fa9a4a70e3ca48848e9a481e207a46cb22ea45374fba44e29e8a41f18daa3b13010a3a03229a34b5282a33bae21a26b61a5a2692533a2632648a2479adfa2438d60a237c71fa20f71f7a207a9c7a1e50d8da1d5e9d6a1d1ec56a1cc5a9da1c6cad3a1adbfcba19057d7a173ad4ca164b9dea1643026a14b8c14a0f6d167a0c6b40fa063716ba01f14b19ff8a9b09fe02ca89fde6fdd9fd18f5f9f5d47d19efb3acf9ed83a089ec0a8919eaef6e69e8b29839e7329a09e55d50d9e437b459d9eddf59d910f089d5f8a6f9d5625239d4384e49d2b66fa9d20a13b9cc6aa7b9ca371d99c99e4ac9c6a35f29c13336d9ba7a3309b362b859b2849959af214329a962d469a907aba9a8ec81c9a66ad789a5fd22799bda6b3998d7317997efaf2995d55bf994acfac99456f5699249d099918a7279900b46b98f9d75c98b4f2f4987e092598575b60984bcca9982fd6ee982f6dc9981aa4fb97ff507197f4eea69751a7af9742e320972f52df9699612b95f097fb95db397e95d0484f95ccf4ae95a02af7959e9f5e95991a1b9527bc4d94f6b83694a924ce949fc062947446d19472b0ff94572a13943fab78942a61b69429e0b193e73a9993d6486393d3b66393bd880593909bbd937f575e93580d80932f70f6931b17f3931239f092ff248f92bfde489293d2789286eb42921d0b34921ce11591fda7fb91b27a6e90ab6cd49094e3b79024ceca901f09809017054d8fe399658fa2d5438f75fd308ef703248ede0d9e8eaac5908e6a8a988e581b938e48d7028e3b3bac8e3072c78e1a5a9f8e14206e8e10848f8e0b1e548de2c1b18dda984b8dcf9c7b8dc492708d57d2e78ce250f88cd117da8cafd7318c72acfe8c18df9f8c031a508bea30378bde69f68bae4c9e8ba3df798b87f72a8b7715d48b57d9d28b4343788b3b8c7d8b0fd8f48b0ad2fd8adee1fb8ad1d2dd8a6e023b8a2207ab8a1b591d89bfcd9f89b65df5899f4c878954dcb088fa54e288e28b9488d2381b88b9bc358890ff758860e21d87c3381c87bcf71d87b49a2c878d70c88753c097874e2a2d874162ae873a3a12871919b9871391d98711455686843cfd865bae0c864e840886366997862f44f7861d991785f3133985ef5c3f85dd1c31856e62448548a89f84f3f17384ceec6c84c3865484ba51dc84806ad5845314fc84356af3842b57bd842657d483e44bb783c026e3839198718365c94e835eb1fb8301418982ea4dcb8268f23d8200bd8481c3b6b9819357be8190a751817b4e978175dc1b816eaf66816b48d881382c58812f596280cd84fb804004028024e55b7ffb2c2e7fea41bf7fba24677fb36e6e7f3f0a637ef492c57ecd5efe7ecbd2347eabb55b7e9b58307e6b3ad87db9c2dc7d8f81737d6770fe7d6401857d427a3f7d1bede97d04869e7cebd0917ca5c7667c35f84c7c146cf57c095f2d7be3d7b37b850b1d7b4811ae7b17f4567adedd0f7ad67aa77ab1eb6e7aae84e07aa86a997a3398947a0c93de79f3d01a7945871c793f7cf278c67428784af1b6783e9c587825abd977febe6a77d3ee3077c2fa5977b832f2779b181a779aa5317792dd01776afac2774d6c83773c9f50771d4f2b77022a0e76f77de276bcea4876adf9b3768cccf076712cd575b0758275ada26c75a9bd277590c7a1755aeb65753ad3ff7513d7227502760174e8807674dc3d7474c8d5c474c81f2274492aa774023ba273e7c06c73e44dea73b4cd0573701392731a8d8272faade872d08e0672b0137672960756724b6b6071b43cd9712ed49970fbde7d70fa636e70e09f6c70dde139700ff0f57000dfb16ff16a306fd7d1286f99b6106f78508a6f60a3166f3085be6f1a00136f0390916ef7db076ec4a7486e6870bd6e60f4b36e3348ef6e32206c6e00e4306df9b7d36dd9b8ee6dc64bdc6d5c386f6d2c1b176d0e680f6cf31fd86cac722f6c939f2a6c8d50cd6c35016b6c2ec52e6c10295d6b607b086b5d3c9c6b2d1f446b0da8a96a98621c6a4452746973adca69626ada69532cfd69324d82691cef0e690fc651690cde026909d25268e0428b68dee12668bb8c92682a566b681121f867cf1ee1675d4571672260f966ff851c66f7944866dab7f666cf67c466c812af66ade1e46673f01666315e2465ef895065e1a6ec65cf1b0f65bf6bf8659efdb765918779657e8c37654ede506541c59d6511a845650107d664c02d9464b81bab64b3f40964aeefe4649a1e696487ae5c64779c056463a76e64588e45645527b763dfe6e263db9e2463be71e263afc98a639939c66317fe30630238e162540a906236f37d621fc6bc61f4828661d8dfe161d49e2861ce187361afaafd61919712616a76336100fc1960b6aba160a6379960586b60601a6bfc5fee18335fa0f2d25f5122905f3743285f066ef25ecb8f465eb4d71e5ea918d85e86a8335e84b9c65e33b45a5dfb57b35df730115dd093895dc222cb5dbad80d5dadb7b35da076315d9dba6d5d0d6dfe5cfd8bf55cc94c255cc7017a5cb63a595c355a945c1d31385c169d355c02d1ac5bc2f49d5bb51ed65b8a684b5b05cc715a8484105a5e22c25a3aaee359f9bd1c59e4dd8759d7492a59b222ed59820595597b647e596d82ba592040e15915836958fe256358f0238958abf953587bdbfb5876c0aa5876a11c587235df582af13e57eeebc257a9284057a4868f5786a930577469375754b29e573a6c1957312d8156dfc08a56d9f1ec56afa33256977c30566f52bd563f3565563a0412562b214c55f9766155ccba1655c9f470557d1e2b5578969c5551d703554cdc09552b951254fdd3c754eabdbf54dc256254c7b896546beeb6546023d8545c3956544d9c6b53fdfe1953eed6bb53df9fca53a1a218538dce7d536856995313102b52f9cfd452bc950c52b380d952622f69523488a251f166ed518fb1415175c1b8516c51fc514fac4c5143a02851346ca6512e0028511382d050f244c85046415450296b9a500b50524fc7ea3f4fb6b7514f9a121f4f0ec0154e9018114e63189b4dc731664dc06f564d958b714d8240fb4d7913384d5c179c4d48f5e04d3f7ce64d37421a4d3212c34d27f85f4d03994d4ccddbdc4c69c9754c39ac1d4c0e8fca4bffc88d4bc935064b65280c4b17e0fd4b0f1e954affd1224af499364ad2ed494a712be54a4910d74a3a53634a054ec149faa49e49ccdd38499830a6495d8fcf491d46bf487192dc47a1fa8a479dd2e8479b7f214777aa1a47617ae4475e0b3b4747601c472949cd46f92c7546af5ab84641831c4624391b45e0218445a53a34458ab7a2456791214551e0e44551cbd2453773c9452976aa4521ae7a44dc3b2544c68f1044b654c9449096a6448ae9d4447aea78445068674420845f440d86a044089a3d43f0670743ca474143c51eb2433de0a6433b5c01431584034300cba042ea0af64267d8d9424906644218e90c41f23ebb41c9081c41b82c3c41b76c5641b31d9441a52e36419c1dc0419550b1410a2be04106faa640fb557540e10ef040c30780408a9c2440897f6140351b3840101b173ff8f58c3fe658a53fa019383f91de203f8f5f1a3f6e9cf13f412fba3ee32a1f3ec1a7e33ebda6123e6f70e53e5030383e4133983dd6fd3b3dc137ec3db89db03da61e703d93a46f3d3de0b63c66e9243c4ffd863c4407a83c10b49e3bde4f153bc964d43ba9aab13b5894d53b0ef3593b0c05f33a93cae93a7045cb3a5ac1223a508e1a3a03221239cfabd839ac840639aab4a639aa536d3974771039021ff038db56db38d2029838cd30573868204e384d842c3836bae8381f0bff381c108037ebf32837d03fb33717899d37077aa036dc465936d8b59a36d763613688dfe536721233365ca2af365738df361fc2463612b7db35e514d735b46ff835a0eff53596ae6734feec4234ece6b934811c5934799020340ed8d133f236e933b65350339dfd2a3382634b335c6954335a810c330cd57532fd9e1832d1682632b1fae9327c533a326a56f8324fb01d321e92e331a753393199d052315d43ab315726f8314adda5312b347d30ef02bf30752324304ab6a83007e2e52fb99f782fb641622f7cc7402f4f04822f4a9b022ef86ea92edf79232eaf5bcb2e822c872e3c56132e3b143a2e2958592dc92d792d84a6f12d42d1ce2d41ad032d3c0c5e2ce4837d2cd6f31e2cc59f532c9dbd142c8ee7832c83661f2c50117d2c3d71a52c01384b2bead14f2bbf8f422b91c9482b69bb2a2b6236e92b41233a2b200c082a87b1c72a7ee9f32a313efb29eb3e10298dcac9291ba1612916ea3d2905869228fcdb8028e78f5728480ab427bd3ae4274f95b22747c3a4273a47462731fe55271f785a271ca58e2714fd5e26e4e00626da2b9626c0a087266c3728265d1991262cfc39261098152607737a25eaaa7f25b3250d25addaf425aa74662521d3cc2481630c2463481024358d71239303f6237b6e39236adcbf2362e69e231949ec22f9d81d22d8249b22beee0e22bd3a61225edd692238039d21fcf36f21f4270321b21b9521aef242218e840121735021213aede221354885210ee16a21012e8f20ac650820a98626207e063820795cb1205fe19620230e51201944b71fdc9d3d1fd82cfa1fcbf70b1f9f4fd41f88c0101f83e4ec1efb66341ecd3db91e9d20611e9389901e650fd41e5be0b31e3274301dd392481d71654e1d6ac33f1d5672a91d44a0011cf0be0c1c66afb21c022a161bd9d0bf1bc535ba1b6797c41b5a74631b4073291b3e5c691b0cf0381afc1a051af22e4a1ae048941ad1c0091ab02b3c1a7440101a70c1931a52a06f1a446a9719ff376319f1597f198ffc7b19864022191fd94519026a2018e28bdc18cbfc1818c86eab17d559b517a53c5d17a1bcc2175f2b37173a168a17062c791701bfb91700e1e016e0779d166c422a1668fb6516445feb1601be8515f6b45415e95d9a15c16e891595559d15718bdf15663219155e871a14dfa9d314d5f97a146b6245144f1c83140b2cc113e8f94813b77c181363ef811359b555133c8e2f131cfc0a12d3388312d04a1b129f297c124cd6e5122ebbaf121cb98d116f25a2115a26c4110dcc8e10c1033f10b55ee9108d76ff107af96c0fdac9170fce550b0f7a3d330f6718890f6104670f1b6b980eeb4e400ed9ee240ed78daa0eb4c7e70e6daefd0e3a00760e2fc6590e22e5db0e1379980e09eae70dcd8d700daeb7d60dae9e4d0d75c8850d4933160d34c8b20d03091a0d004d620cda456b0cd491e70cb4fccd0ca72b890c632af30c6094f70c5d2e690c26e2b50c0580400be265840b71f7b70b67e0650b59a72a0b2dc6460b2949310a86b6ef0a06846d09fb7376097e962d09387c2a08fbd04208fbab9f08f7473908f31f9708b6c79308a01a01087f4492086c0ef30836527808293267081fd65e080bb2ab07e6b8b607da324707c9c3e307b1eb7707951215077922790760f327075e7d51074959bc069b5a3b067c224f067a3d4f066a2854064645220637a8370617904505f72b1305be683805a8cced056786d50534448304f5aca204cb3c5604c07f1b04b371bc04996c010498d12104847ae6047862e00469724004341079042b64af03fd2d2b03eb0d6e03bfdd67038fc00f036d1d46030dc09902e8b2bf02be45de02a72d750294c2b7028c8ac202892eb3027bb832025ad19d02365b9f01da19e101b08d0301af4afb016c6e6f013237d5012b26570126fa13011134c400f565e700e0536a00dab2d200c0eadd001821d8

  | 9 => 0xfc2beec2fa6a3616fa5470c7f9232954f74bab59ee04c4e5ed1eb575e3fb139ee3e21e18dc523aa7dc17a253db5fbe86d895a8ebd3cfe2aed2238059cfe2ed89ccd7feaac74f7bdac41e108db8c2825cb3b8e798b0b92f50aa2fa58ca96049d0a6706276a550604da2438d60a207a9c79ff8a9b09b2849959a8ec81c9699612b8c031a508753c09785f3133984ba51dc845314fc7ab1eb6e7aae84e070dde13969532cfd68bb8c9263db9e245dfb57b35df730115dbad80d573a6c1955f976614e9018114d3212c34ad2ed494551cbd24521ae7a433de0a640e10ef0408a9c243d93a46f3c4407a834ece6b9339dfd2a321e92e3304ab6a82cc59f532c9dbd142c50117d2bbf8f4224634810225edd69205fe1961e650fd41c022a161af22e4a1ad1c0091a446a9718e28bdc13b77c1812d338830eb4c7e70e22e5db0dae9e4d0ca72b890be265840b71f7b706464522027bb832016c6e6f011134c4

  | 10 => 0xfa5470c7

  | _ => 0

def PT : ℕ → ℕ

  | 4 => 0x203520003334100018341000372530002833200036341000233410000234000073330000cb330000363210001334000012320000613100008535200010210000023100009a320

  | 5 => 0x133510011932100103331000602200001a34000019321003a86100010134100142351001e2361001cd261001923310024d3610000a341001ae3510004c340001e534100060310002eb3210016b33000000342001c23510001b351000a234200178320000003200004a352002113430020a34200061310001582520010a36200043352001333200017e3410002f340002eb34200130220001cf343001be343001cf36300116340000fe3200014e3410017226000021320000d7351003bd240000133310019e353000fd2630039d3610010436100137341000c93410012f26000287350001be363002a7350001c63300016f24000052331000eb210000ef3410016b353002023410010e2210001b3610016b3630010131000020332000d8231000723610008826300204350001263400039d3530006e2630006334000332331000523610010c360000aa26200052341000c134200031341000c93610006f321000da35000020321000b6240001003610021e3400021436100418a10000133100001b3410003c330000a03500009e3400012e353000c9351000fb3300006332000004330001c63500018734000013341000253420006234000177342000883610025a24000048332002cb352000743610016d3520009b23100282331000cc33100048352001493400016134000138341001353500001a350000193420012e3630003135100004350000303620002c36200048362000cc35300048342000a333000010363000e73430003f310000cc3430003e330000cb351002543520031733100137361000be351001473200009a35300072351000863510007e352001003510007435300073342000883510006336100137351000012410014233000171240003243100005d3500010f000001d83530003c3400003e350001263300014c351000d5350001923620010c350001c233100155340002b7351000d73300033d340000da3400019234100000352000d6330001ff332000850000007b320002fd2400024d351002cb310000a03400009e33000300351001e2321002af242002ae260000db3300016f342000133610010d352000623300007d35200274351002033410003133100235361001ab3200009a331001ea351001ff3520000c3210007a240001fa321002e0351

  | 6 => 0x5434100051330000dc3700017b352000c927000496341000e834200401341001fb36100702341004113420046225200579361005e2310002ba33100043740005703410078c3710025d341007ad360000253400038d3300021d33100431340000823520000f3410047f270002ef33100397754002413700042b7410012336200181341000a9352008643100011c361001f2330004fa3600018e351000ae342001eb3300036d361006b873100313360002d23310003d230006d5321003b7361006ab3400008134100060332000ac3400011d3200067f610000852300010b25000135310004ba7620014c242003f233100810340002a1371001eab210016f3610005533000134351003ce341001c03210036d351003802720062db6200031372002f5a4200043b20000ca352000233320067e33100654251001403510070c3610038a3300013c371003f7232000b73510057e2600031b3400050e372003ee3520078b320004672620030e361001143100030c351008d03500044d3410025d37100398340003a53310011c340004bab420036f3510003b3210016433000263340001233310009a351006ec32100215230002e735200488351006e236000319261008ac3500011e330006d83210031736100480341000dc363006eb352008ad3410001b310003deb53002e537100079361003e0340004aa3400079134000132330006c3361005b53410030e3510030c341003f17400009d240000b835200082362003983500019d3410044434100089310002ea3430013c3100043d351003033410030133100285351002f727200040342006863300022f321005477410007a31000339351002d2361004a2353000dc3420001032000317331004c6352005ab2500049337100669360003e83610001f36100460372000b8330001193700009036100657370000ae3210036127200539331000ed221003603600000235000110330002ae272002853410046636200412331003dea63004ba75200049250003cb2500051c350000dfb31008103700025c341003dd3430022e3700001a331004c037000547610005de3600026e272007783610027c230007dd33100612353000003100012b642004db3310003f3310015934200237351004c036000218350000a6321004ad360003dd363003de73000031342000be3200044c35200604352003f9370001c7220001e73610029434000043320004d6250000213100001f3400086a34000321342000143100014e332004a93310038f3210024b3100019f330002d6241001c036200725341003722410019033000589330004ba742002d627200260351004e9360008fa370001342500003f351000c9250002a52500079c740000983510048c3720025d331005b536100351251001e73510020234200317341005a0331002d37500023c360008bd352008fa34000564360003eb352001d3730001c5353008fa350003ba3710003d220007253610050e3200004434000773740003dd373001c822100043b3000181743000cb3500025e271001903200017235000327340004203310035d3310062d7600023a24200301741003dd353003a334000314321003103420019f352003af3710041b37200476a31004643400045835200092342003b73410004e231005223520001e350000b4330003e8341002f3351002cd2400054e2200060e230002eb3500012b74300723340003ed353003c4350000c9240004a5360003bb3400076f750001803500008232000122262006d93510022634000082372005743400041b352002b8331003cd34100339372002b3321003977510011e342004c9353005e6270000ce751004ba34200537340000fb3420011e320003ae341002283310007d3400033f342000813310010d27200218370003ad360002d3730003903410048c362001d734200264340000b8360000373100019e232004813520038a3530040536000385351000c9230002ae370000c926000487362001f2320000a63500030c3710011e340006473500009a2620022234100879360004ad3400035d353002ea373004aa360000872520013232000235340000b7270006393310001f3200020f36100344350001883600041b362000ac370000ac3600005232000773760002a1351001eb35300092321004c0330008c9360003af3610032b3430023a37000155341000b835000028341000c834000060331003c3351002543710058061000285371003123400001e37000339341001c43500021a37200406350001be34000773b40005e83500007f3310009d25000218360001ba34100460352002f4251003ed3730003f3410002f262003ea3510057e2500005e262000c5350001b2351001af351001ae3410001d320001a8350003d9330000d5370000dfa2100439a62000a0331002d7331004cf35000028331001d3750003cd32100193341001be3600003c2520031b3600021525000189351002b42310047033000237371002b93410017c361002bc34000043760003b2330000dfb4000154241003af351003c33710058c340005b63700016835000193361001643530065d2200009232000575370002b4251008703400028d33100062252004603620062534100157351003bf370002a1361001523500028333000181b310028a331002a52700004333000385331000a63200037f3510074234100478220004803100013c3510007d370004bd3600037936100773750001323530031536200164373001e73710011a331000dc32000114351001103420024b33100047321001093510023f3310035d363001c5373008d037000209742001be37000159372001203500005b352000242300004e272000fc3610062d730005123400034436000511340007ba340002ce36100508330005043400011a3610021d3320074d331001393710097135000461341001be3500017634000193371002ff220000e1330008b5350008b23500032b3530000933100181640000d4350004e4340002d2351002b73500031e351001dd350002e535100315352000a724100043750006d334100018270001eb3400048c3320061d363001e7341004fb3500041a2500019335100310350000b4350002ef3620035e34000121372004a833100068262000a6342002d374000198742001d3b62002d23520009f34100461361000e2331001b83300009235000090351002d53630008d340002ef37100181741002ce35100132373000b43600009836100083341001e8242001942520007e36100398370002d2371000a6362002b935100073341000ee372000713600011e3720011a371001913400076f7600018a341000903710034b342000583520028d3510031735100054351000513400007e37100181b620028335000147a3100445341002943600027b3510011a3410074d3710012b741001643400043d341000b73630015e3400018e3210029f34100340350000aa352001f2363003e32600006033000146321008d03400076f730000253500025d3610013b341001323400012c35000177252007cc350008d03600000f3510023f332000f9752000b4370003a83500022c360004c0350003ff340000713730017a3100064a251000a637200870360001173300021d35300181b410052037300053362004d9331003d53300079f351000a63520091076000398360000eb330001f235300461331001eb36000035362004c034000773340004f035100005371000be3500044b34000060373007ba370001c7352000213610001f373000ee341003f8240000ae330001b8340000d5340005253520003135200228341000e8240003d8240001d3a31002f57650021a352008e43500094e34000378330000283710032d000007913500011e36200191360006382300046e340003eb37200360350008c6340003b0240003f6330004d83510040b340003bc321007feb510007633100162351001d3b41000e13200046f3630073b3600016436000269220008117410015e350002a523000312350007a83500014835200009220001463610067f640001233410003b210003353410013b371000d0373000363210012c360007062720002f3400064f3210032733000301a30001183510047e22000159352007feb410001e3400001b2100011e3520053c3300046a740003fa270000d53600027c2310084d341000582500001734100098341000f22500083b361000cea10002fe3410000a350002bc350000872620023f3300008e371002eb330004fa3700036a371007153400004372000461351006c8261007fea610080b352000b8340000eb35000147b420076fb510035d37100643341004b6340002c134300801351002e336100899340000d0363007cf25100060363000d53500003d3310033f372000c235100226360005613510069d37000302241003ee3620069d3600075c751000ae3500065a230002ba3610061a251007c9351000ac350000b934000271321003ab352006ae341007be330002da2500061d310002f5663002ba341000823510008e3610065f3420002836100218330000a03510062d7500076f740002963510064e272002d3760007ae342007a63520038035300064340001816100070d341003c3341006c1251004963510078d3410033f352000603530026335000104230000402400076224000260320006b63400022232100659341003d8341000523720026c220000823420021d3410007d320002d5330000473500001e360005b03510020f35100288252000a9342000b83700020b35000052352006a723000279653001f73400002436100439a10001eaa200012b6100016a310004fb34000741351001fc340001fb34100028351001f6340001d3740001f2340001eb331000e434000773720000173610096625000170320000f2230000ac3300000a370007443400025b37100722351000e9360005cb340001c634100741371001c4330003e837100172320004603200071635100262331006bd35100052321001ba331004ad35000581241003f2341001b535000098371001af341007ff34000147000002f6351001ab34100532351003b73510011f360001a8330000ae320003de620003873410086b3400020a653000f9754006d02520012b000003a3350002df363002d5351007ff350001893410058a3710058a361003bc3720017c351005bf3500017a3310077a3410019d3610016f341000103420016a351000ce7540050e3620091335000168340002ae363004e934000164331006b83410019d3510018e341001573410063c310000f900000152330002ef35100296362001ee350008f26200028c36100201360001403410057a310003403400013c3410052f342002d2341001d3760005fb25100218340001323310026e363000df00000688341008fa360005ad321007af34100127351007ad3300008a221007ca331006f93710046aa42006542520065a240001d3b300003b220003f9340000cea6200722371001093410019c230006be372002f0321008a0330005af2710075075100081351003f237100301761000fc35100177262008863600055473000884370000dfa300018837000123351006f7330000a6330004da3610063f3510054835200190340002e5341004b63500048b252003ee3720006723100397653000612310076b250002f03410062b3510015a230000d4340000e43700096623000670372004fa350003a3370003ee321007737300007132000147620004dc34000081371001213510003f371000b4340002e7321005b23500083837000457251001d73610066c362006f73400009f33100043000000923300018835000090341006a53400008d3300046a730000f965300110350004013510011d34000107370006f73500007e3510004373000073321004d9371000713500066b341002d7330006ec3410062d7400085a340001f6361006e23400049f741004ad370003f9360006d8341000ce6530090034000638250000583420018e352

  | 7 => 0x1b3b4200304b610004b34000509f510022038000509f31002a4b3100297260001ac3800029e73000034101005473600047f2600054838000232b72003f2380004893500004727000509f2000226341000c5310000ea3500003c330006223700035eb710008d320002a4a510018c380002633600030526000385a71002a4b71001a92610007f36100232721002c32800025f350001dc7410018435000029350000dd340000fa36100153a3000043370002bf280004ee37000145310005113400002134000295754003b23500046b3400001f3200018c340000012100038ea710007565300431760004fa350005091000001a3300051f36100083320001caf530022d3620061e370006122800027c2500022c352002f7360001e666300010350001e066300178a42004b93400006032000508360002e22620043876400135341000783810026536100281b6200187380000e1352004593400001eb4100094320000263700019a76000295730002a536000501370005db765002b8371001ca5020009c36100164350000ed3700009836100240360001cea4200216330004f1280001ca642001e8341002553520003e220004f2370000263500005f380000137700029b261001063600011b210004fc380000ff350001c7621004d935000625a510003aa300043c330004f62500036f351004ed360000ea360005c0e200036e35100155a42000fd7500018c3600043e3600043435000033a21004313400010f3700025a361001caf32003ba381001a837000367352003a0750001ca100003663420015d32000159370003b7382000e7740000336530035e3410062e74000632350000326210036d2500057a26000627350000b83630013ea200026535100033b410049e260001cae210005622000420260002b83610007f310002563700024875400509e60004db37000635350004da360005403400002365100558f210025e270000ca3300043175000336252004d0370001c7b7200558f6400373270000f87400039f350000e33500006e360000e137100155a720006d350000f93500041734200255342002a63500019a663006256500062a240002523520022226000177360004ca38000078361003673720001032100558e31000ad26000012663003663720029e7700013eb320026ba30001d4330004b5360004b936000190674004123800018e65100558f61002713200001ea610036f350002153610013eb500049b64000232b5200291350006043300001e3100008c350002f1b71002f175000060380001cae63005a63500055c230000e7b71000f7b50003ff342001cae510061e360000042620022636100182661002963500018167400180652000c53620034e370003a5340000fd7700002d230003f733100219776001e0620000d43200006f270001c76200034e380003cb75100123382003cb732001fe220004bd220004fa380001eca400003f36000033a510041c350000d2351005c0500000aaa400023525200155102001ca10300183720002982600023b282003453300053f350001c23210007835200077351001363600014e380000283100030122000427a30002deb430063cb30003d63400029b3620001033200215351002e7272003093500040136000180740000dc24000399340003833620030c34100005b21003bf340004e03500033c380000223700034626000012a510048f3600030734100396b4000558102005a6370004ed3400022226100178b7200012a200033738200153654004893700021e2810046b37000155b720014c651004c23500010135000033a31001ba3600001435000081230004d93800038035000357260001e837100197b3000278380003a0761002762600047e37000277361003a0743003a5350001e67650039d742001787210000336000307b71001e076500445270003e8360000f5260003b9343004e037000565370003673820030c3710007d330003b135300366382002f13410021e28000129b52002dea73003073710027e3620037f7620016731000183b30000cc3600061934000520260001ceb52004123300020a360003a5360003ac360005584050001ea51001ca74300187330001807600025d36000128740000e3340000de3500026d2600004723000426350000de380001ee271005d023000012b40001c7b6200558f4300459360000d2310005d1240000d738100458361001c82400026c2600038836000012b3200154261003b13300036736200366352003c32510018c3500053d370005585050003c372000ca3800011d6640056e3600007931000509f40001c9260002ab38000078341003603800055810500011373001443200050425000075b31002c5342001caf50001922600043c350003b876000128760002326200044136200589230001ca102004343700011db3100041260000f226000431350001f9350002a42410037e35300600260002b534200522a40001cae610005f340000572600011b34000547370002f6350002f93810018e75200493250001b3a700040c38000366260000f866300281620001cd360000a23800054836000558500001827400037f752001ad3500016a270002dc370002253720012525000223372003a07300018376500182765001b3270001817760041237000180754001ca50000417372004c63600030c381001fe260004ea3400058b26000219a30000b43600010336000567340003563820040c371000e7674000c8360004b9350000ff330000333100059138000113381003ee360002a6360005443310052f250001c6320000ca241003493530013536100407361003ff37200345353001bb3200053d353001dc740000d27310061a3600016438000558640002a4b51001623800026c2400026b23000192262003e2280000e7b31005c0f60003d6370003f7361003c93800030c351003e4260000cb6520028526000184360001a03700001e71000295321005a6340004de36000097340002f1371004b9380001caf54001ca4010029eb5000295b4100113341004c475100404370002b831000232b42003e4270003b8360000cf380003843310029e7200015575400199361005e93600062e750002d73500015375200152776000e338000438a40001a8350002957600012877000158260000d2761001d96200014c7540032838100509e2000128b40000ed3800049a63000635360001ac360000cc380001c3370003a4360003f2360001b3a51000912500001eb3100441342002cc381001f032000045321004b6760004c462000254351002e3b5000288b300018073000155b42001cea3000128750000fa360000ed3500016b330000cf34000206230000012500009c351000f2250002a136000098351004c62400033236200336250003b9363004c4b4100199351000c5260003fe3700032e350000f6360001297650040c3400012f26000033a61002ff34200309360000c33800023b330001b42400044336000075751000f8720000de3600055d370001e7360003f8a720011b3700025a310001232700026738200181a62000e1370000d422100244341004837510029634000468270000472400059737000120260003f2340001f12600039e350003a5370003ba3500025a3810054135000033b3000148360000c333000155b6200005b30001e738000133271004d835000634320003a43800062737000346240000c13400008f360004fc37000010382003a5380004cf340002ae32100384220001e3360002957500006e3500038924000336371004e0380004f1240000d2771004a5350004763700055435000622350000f8b30004f1250001caf63000d2b31000f87650051f280002d7370001fe34100155b52000757410025a372002c9353001ca404002022800039e380002a53500037f35200381360005dba4000452b7000033b510038d22000318220004152700018eb6200185270001f934100509f300010f3200057627000483b41001caf30000d4361002a4742000f2240005fca30002b338000026340000f2270000e777100089321003bb37000517380002a4a310007f381000ff370000d27410052c38000226381000ea3400029e741006362600015f38000316371001d9621002b8381000ef3520013b260003f237000265381001543300001e741001ca5060003f350003563720007b3300003a651001de3510000b2500012e25000201360000d2754000ff340000fd3300013eb3000117360002df37000498330005fe38000137340002cb250002887510026b650002283710025538200005a610007f341002523820022637200219b310034937300224371003373200034537300321240000206610048e3400000e310002e433100033b31001ac370000d43510013634000438b30005a6360000fdb51000613500049b7500014c75000093320000f4360000e7730001de37100013673001b62600037d25000336361002f2240001c6330001c5321000b6210001c2360001b3a32000b53100007835100338380001a92400047c320000fda31004c465300178b5200612240000056530001e731002b835100298280003d13800036f37000036310001e8381000a7262005c53200057c2520003c382001caf200013eb41000373500032b2500026f321003903500002d310003fa742003f8741000c5261000ac3400049a230001b1370003373520007e340003eb754001c5372000c62500031636100180750002153810026534100248b3000313363000d2b41002df34000487320000b82820045635000113361001923410018a220005f4380001e7370001ba370004f12700003c321004433700037fb30000042320021134000189350001d9b410044d26000540380000e3330000f423000185240002e53600023274100612260005e83600044134000033101001a2270001bb3820043d360004123400042ca300014e350005473500026b6300007225000426380006373600000333000208761000e13100029e32100295b5100085340006362800025525000192371003d1340000732100023e35300031330003f8b31002197730048365300159360001caf6000563360005b0b50002f03510033736200098381000ed360005f43400013f270001a0382003c9350000cf3500035f3400001a320003bf35000196280004a3220001de3810004536200309340004763800016b3600020a370004eb3510005b332000623400015e36000012a4200326270000dd380004b9370004fc34000234220002c9330003fa75000259371005f4350002a53400015634000012a700038575100495350003d13600006d3300041336000062220005b236000215341002442400040c35000206260001efb3100033a410006a240001dc76100210353001ef76400197b32001de36100190b31002d7340000f9370002473610014733000540350002093310001e3410010f3600041c380001c5382004e737200010320001556200003a752004763400003831000035210005f43600031b3700034e3600006e380001ceb40000b43400006d380003f9340000012800021832000181b310006e3700006d37000444a3100186371002ba363000c42200019ab42001dc742000033700035e761003c937000427620001d9a21001f833200452370004ea37000558f60000c926000592280000f8b400008d2620033737200208751003b437000020765004ca3200021d220000dc26000136370001ceb32001fe280001c5352005c42800060eb30000e122000128340005403700001421000013776002a73610037f720002d6210000d2a51001c7b32001527500003f282003d4340001c7751000d2b7100192381000ba2600055b2700001c330001e134000005754001dd340000c1360002d13700001e3310011c340002df3500020e361000a935000396b300003f3800011db400007b360005d6340004dd2620041e270001d23300029e35000423240003c23500009a371001f332100152b31001b37630010c340001b275200547340000a12600008c260002803620010a350001d2382003b537000208a30001af75100197b400001f2620027f250001dc75100223321005f7360000fda72000fd740002183500046b350002913700023727000192351000ab2700018434000191350004fa3400003137000295a3100431b43001ac34000011282005173400007f371003fe380000d2a7100548370000fe360004bf37100020b40000843700019a75300178a3200461360002deb40003fa641000e125100011232002df380001bb350003c7b300019077300190764000f13600018e753003f06430054e3400018e741001b8330003eb6520010c3700025e351004c2370005b53600020a3400011db50002cf342002153710019a6500001ea31004a82600059137000398350002b3360001837610018276300558e500011b380001827410052f2800018177300081260001807510062234000181754002a538000129660001907700017f753003077610034627000558e600044b650001b7262004c3361000c62510031f7420062a26000470360002a4640001d23520006d231000dd321004d9340000c835000178b3200195330003b4360002c125000178751005fb25000288b6000509e30004b462000178620001f135000199381000bd250002ba340005c0e60000d23310038333000544330005df3720001b220005913500035634200558e300026735200381370004af61000439b50005302700037f330000ba24000247371001a83400001ea71000783710023e373002f1751000c433000111371005e1360000112210056e350001cae50001dcb61002a7341000d2a61001b83720003c362000bc350000d2b6100092272000173610057d381003683300015575100155720001dc3610016f3400022b3500007d360000b733000152773002d83100021e361000d2361000b43510014c75200399370001863800045037200346230002122600045b2700051f260003bc38100356330000a7350003c9340004b6740000b43700029eb71001993410021227000189252004703700014b370002802300015626200033b61003cb73000461361002e37430001b280002093510054738000560730003a074000208351006163500020e3710003c3200010c380004922300014ca20005eb282002eea30002f22500008e2300009435000012270002ba330006223600009235000226351002b3340004af660005b93500008d3400018072000337350005f0370001f03530020e351000fa3500039d74000129740000ac33000332340001f8362000f9340002383800053a360002243700015f350004433800012475300509f60000d1321003a076000402362000e1250003993800013c3600012a3200006e251005fe370003d6350001f93700011d763001393400010c3500032425000104330000ef3820036f380000e5350001803210001eb71003f8341001d7230001313210046a250001373800031c3300001834000033b210023264000160350001dd36000055262004a036000185250001dc351005095000012c330000fd321003d13700012a3300049ab31000af2200038eb430050b3410034e340001d237200384620005581000059227000064330001d236000558f30000cc35000040320001e73400038c360000d237100075b61001cae40002a4743000fd751000f8761005e835000053350000f77420034126000020a300043a220001e83510035938000495340001d9a400017fa30005b535000346280002a63400001e7710004b3500033b6510001c37000298240003d13500007133000509f5000033a710057235100137360000e7773001b8370000e776400509e400029e750000d234100244230002013500003c3500034538000342240003bc3620051f25000158270001ac3610029d23000032b5000216350003b436100558f50000ac380004d8320001bca40004b6661002de340000d2752000ef342000c623000029330004b4661000f9331000f2230001993710031f64300346250000cb75100330381000cb742000213500001f340000e7710001bb32100079371001d9b50003ebb200015f3700001a35000495380001e8361000e3210005c6a30000fd720001c9270001ecb6000005a200013f240000c728000136350000103600038ba3000326280001ab34200023a30001843710004d3500046b360005b0b30005863600049b65100222231004317210037fb200040c370005c0e40001a0342003f87600012f2700001eb510039da200013238100060381000e3251000853800001ea4100245270000aab41003892800023726000476350004c0270002da2600027e321001557210034e350005c0e30000f8340002b1340004be350003c93600004d3600030e36000443340000cc370000dd35000055320001cae42000b635000384a2000345370005f437000411a420029574000106370001bb36200396750003a43500004726000081240000b83500051f240004433500039a350002b724000298230001613610051f270002e3641000ac3500015f360004fa3700051a27000330361000ba261004a2381002df360000f43410007035000075771001a0352000d7361003593610020a350001caf100012b250001caf64001863700015421000411a720001d32100012b31001cae310053ea20005e625000345361000757520023836000291340001caf610041c3400013737000139360004a2341001caf42001583420044b652003b8b3000273350000d2b210041c3600005e27000088350002cf3800027c260001323710013135100031360000073710005b22000444664004d93700016f350001fe2400011da30003303520012c3600012a3700062736000219b40000ff360000e7750004e03600018e740001ef765002de720001ec7510001e371000a2360001233720039db50002363700004a36000385351004af750003b935000411102000d437100180b30002a464100185260000d2b51000ab2800006b340003f0620002af38000480370001e674200208000003bf38000352360001ee270001e07420012335200047250003a07700033836000316352000dd370002e9220000136500023725000128a320003a75300075761004bd2210001e761004fa3600024b25000291380000b4350005f9b70000337520045038200439b30000ff3620049a650000fd3510041165300032b32003d6360004943510039935000411b72004953600054d3600011b3500023b35000359340005f93700026d240000a7272001ef00000161341004b6730000fd760001353100002076300023753002816530001e742000ac370004fc350000453500004435000295770001ecb4100043342000ef372000ee36000113351005eb3800054835000450342002713210009c3100038eb52005af35100013753002ba3600001276400345350000ff3800037f320000fd7300004c220002a6370001bc751001dc00000128b52003e9663004d2361000cf370001873400000575200633270002e5370000ea370004d9360003e9b72001082600053d340001af754001ca4050023837000295b300032a26000558f4000026321001ac350001fe230001cae30000eb35000319252000e3360000dd360001caf430000c260001ca0000000e2610001124100033710002af340000c6352000d7371002383500025f3800020035000118351000d21010046b380000cf3600032f250000cc3610011b3600019a7540015d23000035330001ca505001fd34000081270005212600000d3400057a2500062e770000ca37000192221000ed340003892500029827000075b71003c77200047d750001d234200499280001b367000496280000d73510000433000338340001ca1050001e75100082310003c76530063538000136380003fe360001073400053eb31003fe34000128b30000cc3400000021000075371000f9330000ca34000005b710000c210004563200043e3500017f754001f934000548340001af000000b83700060eb40005ec360003a93500044d25000012b710004e350001e5340000ac360001de34100557251004bf260005a7380005a5380000e7770002f93800001b2520029e760004b6750002af371000793700054036000186320001970000044b754000a237000622380000b1220004c234000612270003de3800018161000233381003df372004aa2200000425200509e5000424360003b734100232a720009c37100555351001cae60000983710004b32000558e2000070330003422600057f370000d7341001b8320000a23500053ea71001800000017f000005e27600038f663002a41010012e260001c635000155b32005bd3400026a260001c235000304a31000ca3600038b66100033b71005913600043e380003a071000085360001cae530014cb300031736000341270001f938000232b320001634000546250006052500037f7400040a3620001eb610058c3720008128000558e4000537351001afb3000558f20005553810015b370002a5370005212400029d372001c23720029b3720037b6530016a350001ec653000753610001e3610020a380000242500049e250002b33700037bb7200411754000fdb41004cd2700057637200183b400006b37000035370001e66410035e7410005b351005c0f30000d271000370250001e0641003a2382001550000006d360001dc64300017310000a2340004e034000032a300007e342001297410035e663005c07310004610000189340005ac7610047636000537371000973800020f25000185230001247540040d2510007f351002333610062d2600049f340000de340005bd3500029225000216340002af350005c0106000912600061f640001d9221003f0b5200411b4200064320003e97650013e0000063627000012b4100338370003a23420061223000181750000fdb30003d6380005ac752001c76530043b35000597360002d73600004537000044360002a4a41002d83510004337200232102001fe270005bd3600033b663004a93200023f351001bc6530059b7610059b742000b438000078310005032700036f3600036f3400012800000592260003ac350005752200009c341001af653005b13500006c3300015e35000098341004ea35000387350001a8360001d9731000fd7540013735000026361000f7743002d5381003f42800011d0000001e351003cc27100232a520023d28000156330000d2751003c77540031f6610013ea31000aab300062e7300001267000411b620018c370001843700033732100304a61001e9370004f12300000d36000534260005d9380003b737100295330001caf3100016260001c7b420014735000010372006353400003c352000e7765003a93800000437000177250000632600063a2300007a26000155650004ea3600049aa30003077410020b3510005335200133270001ca40000010362002982500017f65100411b520056c7510037b620003076630020225000033a20005083500014d24000627380003046530053738100052250000f7000000cb7430050b3720030d280003ac38000508373003a07650006e34000483760001786530006d340004fc360004ec2600023c3610043e3400057c340003b0320002ac260001b136000208b400012833000026380002b33500038f7650004d3800057334000495370002f17410038b765002e42200029136000307771001843800026a2700033c342000e7000003e6230003093800035eb41001caf210054a761002f16530054a753003a43700011c330003b02300056d350002ee664001803300004728000178a7200081250002de750003f0740001ca104000a63620062e76000561340000e772000509502005c0e500001e640003f864000190a510015c330000d2000001cae20003a43400007e2300010a340004e236100010352000cb000002333410054a760005e4a30003993600038fb520003f34000635370001ca50300530240002f176100178b42002b9a62000e3370005acb61004cc3500014e3700054534000232a420014d280000fe3500018528000542340002de7600053c3400026e382005ac361001ca101000d5330000a3321000f1350001f536100347360005c0f4000535270003bf360002d7380000e776000208b310005c330002b96530038022100124a3000180b61001a838000517350004c238000152670002d0360001b135300129643001ad35100509741001593800043e37000295a620038fb720041c3700025938100013b320059134000135381000d2a3100124651003c1250005cc2300033b76200075754000de370004af361001613510050910600385b41003402620001e10100557250003c62600061225000304a410011e370000023700051f23000627340005a63800024738100560650001e7350004c2360004397400014e36000232a32001cae10004afb4200307b410031536100509e42000c434000306370004e676100178102004e6742002956530016434000304a2100338350000bc3400050134000317380001dcb31000d265000352370005bd3700015f34000392280000b73400029e740001fe250004f1260005c0f500014e340000ea3800034028000509f65000b43410035b37100144230004f2350005fb240000f3260000fd6530003ab40002f17710061a35000075000000f764100530250005bd38000488371002f1b41002e0231000a7330003a2372000cb75000391221003ac340004e734000180770003583700016b361002de770000e7a410020226000033754002deb50000fa380005ad2400020e381000f9380000f2280005b2240001f936000032b42000e76630031535100135371004df3500009634000094340000c92400016d370002f4371000923300030127200300262004db3400001eb21000237540008d3300029d3820001e7430036b2800029b3820006c37000309370004d0340002383400014f32100128b610035b3610004d370004af763002de73000576361004ca350000cb641002af3700001375400012765004ba350004ea38000328361002a638000509503002cc35100248652001cae410003a00000053320005c0630001caf4000033000005c0f20004b677000177361001d9b420029b34200192361005c010000032000002773810008d221000263600025a341004783600043f37100509e43001353620039034000300271000a12400049f3600041e2600031734000023000000200000001e000003bf37000064350000aaa3100509f61004a93500004d34000307b510050e370000e7a5200385a51001caf410003262000385b71002ec28000013000000120000040c360000fa370000f9360003b8b600030f350003283510027734100053330003ac3700047d763003fe3500047d7540038eb510021967400154362000050000037b750002cc3410033c3720021636000549370005094030043a36000178a52

  | 8 => 0x506000021060001fb700001c2400002340000022f5200022b210000010600014a6000025b800002fa800000b6530005010000053a500000aa3100003a100000cb100002f28000044b3000023f6300022f630001cb3000003a400002e7710000ba7000036b310004fb200001bb600000121000019a6000007b6000039b800003e36000049a500000ba82000525000000ca5100008a4000025a20000096410002566200022e700003938000009a40000086630000c10000007a31000520000001966000042250000066510000bb420001fb300002c7760000565100022f500003df6000023f650003eb500000465300022f64000052210002fb810000a10000000e3100005a80000231040002b3500001310000000e6400036a710003d76000036e4000014b4000042a800003aa3000001b320004aa60000211040002ca700000ab300002350200033a80000225010002fa620004cb600004ba500002ea4000011b7000013b30000276400004f7500000c780000226510003ea5000003a210002b7760002a76500029b7100000f20000503700000db500002f10000012b700001137000025a3000021662000203210000ea300000ab700001574000023f520001ba7000022f410002074000023f420002240000006b800003c66000032b6000002631000443600002066300031b700001eb710000b10200001a310003d32000023e2100022e210000ba600002ab520001ab8000009b7100005a4000003a8000039b500002bb700004ba400002876500009b400003eb200001e6840003b26000020770000277760003eb300003d7500000ba620002566000005b810003110000023e7500022e2000022e740004f4060000db8000023e6100022e6200007b3000049a600004110000012b8000045b700003a38000000f4000015b31000117800003ea700004ff54000202200001bb500004cb8000015b800004ba300002ab7200000b2100000e610004f5060003973000050b300001db4000000f42000507700003e6400003ba50000231050002210400001b300004f10600011b8000007b5000010a7000026b71000117300001c6630002eb810003cb30000211050002ab6200000e7000039b40000257650004ea600001b6630001566000016a5000010b500004aa8000015a500001a6640003a34000024b6200028b700002e10000018a700001ca3000044b500000aa7000035b8000031a500001bb20000196710004433000015a7200055a7000019a3000000f320001fb8000016b62000021050004f3200000bb300004aa400002078000027a3000020b40000001050003a32100028b600002aa800000910000010a8000013b7000053b700003836000016a6000014a3000042a3000023f30000186630004fe320000ba52000166710001fa4000038a4000019a40000227540004fe64000156610000050400041a8000002101000217650002075000019a7000019b6000023f700004cb500000bb400001432100016b3000005b400000eb20000001020001ea300002cb50000082210004068000050b800002076500023e420001fb6100048000000357210000c38000042b600000ab400003d50000026b50000231020002210100026a3000032b300001b10000023f4100053a3000033b320000ba4200023e710001e78700032b5000022e72000481060002110200012a700003ab30000387700003976000000e410003d3500003ca8000001b600001d72100001b800001fb2000047b8000020b52000136710001eb700004e10000036e20000460000000da600000110000000e200001ab50000152210003a7600002bb300002210000044b4000050b5000012674000111000003ab7000032b400001667000000e2100025b2000053b4000013a300004610600036e70000116610003a37000036f40000327700001ca8000020b5000018a5000027a400001066400040a400001c76500020b720000f6730000e6600002aa300004c65300031b3100023e1000022f650002240200022e600003a7500001b7600000d6710004b65100009a6000012b4000023e3000018a200000c6840001a76500010b3200035b50000151000000b7500004c3800004ff300001da8000020b6200050b4000039b3000015a7000019776000431000000775000004a4000011a4000008b80000346300001926000047a200001138000023e5000000e520004ea500000aa60000393400000b6200001876500017b620004cb70000167760000a66400033b3000003b80000496410002ca3000027a7000015765000117600004da7000019a800003ea3000047b2000014b8000041a700001133000000b3000023f73000486410000810000022f7300006a800000b74000023f2000000f5200051b6000049a40000096630004765200008a410002da2000004a7000026b700000767400019b61000066630003d10000033a600003ea600004c36000000f6100017b6000001a600003bb500000567300039350000252410000462100014b620004476000003a500000db4000007a6000000f5000033b600002cb4000031a7000045b6000016a3000023f7500022f7400053a800001377600017a3000009b500002db2000047b7000020b8000022405000297700000cb600003ca6000001a800003ea20000127760000d75000007a50000353210000210300025b700004ff40000036630003df4000004b400004565300000f640000ab8000018b7000000a610002e22100011762000171000004265000023f600002fa500002534000009640000235070002250700004a6000024b50000321000000735000007a8000049a70000446410001076200012b6000007a3000000e40000026520003ba8000000503000152600003937000032b700000f7760000e7650000167400051b5000055100000006530000d7760000ab5000016b7200004b50000513400000c7870001bb7000035b700003f0000000b35000047a4000000f4300023e7300023f430001ab6000022e730002ab4200029b310000610000035b400000ca7000022e6500006b5000043b500002ca800003d40600014b5000015b7000047a800002aa5000000e32000203400000e1000003f10600017b300003e7600003de600001fa800000bb620000b22000022e300004473000000100000461050002ea300000a7620004c7800004da8000017b800003d50600012a300001232100003b2000020b7000044350000436510004c3300003d1060000eb50000234040002ab810000eb4000000e7400051b800000b34000007b700002ea5000008b7000038b800004726000022e500002037000000e6200023f6100022f620000976500022f700000ea2000008b5000036f3000008b710000777600008a8000003b400000210400036e5000023e4000023b2100006762000517400004fe500000577600042651000001040004ff7000015a3000004b620002310000038b7000043b70000196700003a33000027a500003ba300000fa60000092400001ab4000007b8000030a7000027650000416530000db3000026b310000ba4000022e75000113600004c76000027a600000ca720003de3100016270000397800001ca700004da6000040a5000006770000235010003de65000225020000376500000f60000012210004fe70000370000000422100010a4000024b3200048b5000022f530003de5000055a400003ab6000011b720001d3210002724000013a4000016a400002526000001a40000027540002fa400000ba800004066300003a600004b250000371060001eb5200045b5000000f700000177600025a80000203800000075400010b720003ea400000d35000053a700003eb700004ea8000041a400002ab700004f730000227520003e6420003b6600003ca300001fa300003d6420003df540000d1000001ab300002035000017b700002176100003b500000210200001b610002aa420002174200022f600003640600004b7000053b200004fe600004ff6000009b600000010300001b50000364000001b3600003c6530002076100020b320004bb520001fb210002ab320001f75300029b500001aa4000000e720004f76000035100000365060003a78000039b6000040a5200053a2000005b700003a64100029b700003610600003b100001ca500000ab600001e7830001e76400014a7000024a8000006b700004a1000000ea400003df640001db3200009a50000391000003de630001d76400001b810003df520003810000019b420000bb8000016b320003400000011a820000637000004a800003475000045a70000396630003df2000028b2000032b800000fa200003865100026b600004c73000014b3000005a500000bb52000422210001cb800000cb30000341060003a7400004673000016b600000da50000071000001ab700002b32100000f6500000402000513800003f1050003ca50000376410004ba800001fa500001c7620001c74300036e430003df300000b78000036e610003df2100019b620001b7620001b75300025a7000003a2000036f6000020730000102210001a7630000ca800001ab420004f7700002fa3000029b300004fb300003f10100008a6000019773000197510003d50500047b600002db7000005a100003ba7000014b600000cb7000053b500003c10000042a4000040a70000387600002cb700002cb200004f7400003d102000187620004c35000017b3200000f710001874300017b410001677300047a7000016751000476600004ea300001576300049260000157410004ab600000bb600000ca400003665200036f510002ca6000042a600001db3000020b60000517800000ba500004b6500000c760000147500002722100026b4000029a300002250000044a7200006b6000011b400000b7300000cb310002f6800003de530004aa5000013b4000040b7100020a320000cb500000fb4000000f7400004b3000010a6000015b82000346310000040500014b32000147540003de32000443400003a7700001cb20000371050002072100044b8000011a8000036f65000326510002932100036e64000137730001375100036f210002ea8000036e6000005b61000113210004475000012a5000006a400003db200001277300012b4100031a40000005070004ab6200023a20000117630000fb6000011751000371010003cb620002010000026b3000005a3000000a2000004a2000017b500003eb6000020a3000033a3000043b600001076300053b600004665000010754000137400001fa60000192700000a3210000f77200003b300000e7620000f7530000e7400000b38000036f3200003b700000d7730000d75100027b7000011b5000000e7100000400000401000001174000006b3000000e650001d10000031663000306400000c7830000f1000000ba320000c76400022f3000036f2000023b5000047b4000001b700001fb5000039b71000402210000b77000005b4200055a500003650100013b5000051b7000024a4000038b300000aa5000010b8100029b60000397400000c77000048b1000008a30000161000000bb320004ff50000361020000b751000412210000fa4000018b400000a763000341050002900000027b500000ab4100050b70000492400000c75000024b7200004b8000000f6200000e500001ca400001da700001ca2000038b400003df6300010b700003bb310002f65300044b600003ba400000ba3000005b3000023e6000009761000097430004c7500000b33000008b310003ab5000036e41000087640000777300007b4100007a40000341010002fa700002cb600002b750000397500000676100053a600000675300020b3000001a1000027a80000057710000cb40000057530003ba6000004b32000047510000c360000235000002700000036e420000b7600001ea800002aa6000001b4000000e750003df6500045b300000c74000031a8000043b8000043b400000aa400003d1040003d74000003b600000050200012b5000003a7000042a5000027b6000025a500002e66300029b400004f5000002d6520001db6000040b3100000f510004fe200003d5010001cb400000376200035b300002bb5000003b310004aa300004b10000049660000293700004cb40000331000004c37000044b700000fa7000040a30000397700002ba60000443800002c652000027510001ea40000027320003c6610004437000025000000207600003b6610003d7300000177300001b41000007520002cb8000043b300000210700045b8000024a3000001a500003a66200018b6000043b620000bb70000143500003cb320000010700015b620004f33000053b3000051b300000b3700002b65300020b4200031a3000024a700002966300009a8000000505000234060002240600024a50000453600003967400041a30000371040003867300042b6200047b500002300000022f5400000b710000e34000009a7000031a600003c2600001eb500002ca400003de3000000f76000235060004b76000040a80000225060002610000049a800002100000038b5000016b5000000e5400039b3100036f6400023106000221060003fb3000016b81000393300003a7300001e1000002364000040b600003765200014b7000033a700004ff20000200000000c3700001f00000011340000211070000ca500000cb8000009b42000276510001732100049a3000005a600003a1000003de7000027250000133400000c35000022a200003237000036500000361000003765000023e700000fb8000015b710000b36000011b300001ba600004da4000036f610001db700000050100055a3000036105000271000001ea6000006a70000004040001ea500002bb400001c6400000c3210003ab400004ba600002410000023e320001a72100022e3100044740000056500001aa30000266630003650300023e6500022e6400055a800002ca2000000f7300010b60000256410002033000049640000453500000c34000004a3000027b520004da500000da40000511000003e24000006a60000341030000250000049b51000246530000632100036f3100036f5300006b2000000e1000036f7000017b5100000f63000226500000a76000007a7000000f3100033b500003566100018a4000036e3200006a500004c77000053b8000007b400003df700003d10100014a500000eb800004510000000e60000336630001cb70000326730004c3400002364100023f540003bb520001cb60000383700000cb42000121000001fa2000045b4000004a500004ba70000393600002164100036e7100009a20000170000001375000022e400000eb7000036e6200019a50000117500000eb300000db600004ea700002fa600002ea6000000e51000206200002bb800001f6520000d32100010b4000000e730001910000041a500002aa700003b100000361010003ca4000023f6400036e300001e66300036a300003bb7200012b5100023e6300022e63000052500003a36000014a8000023f5100022f4200047b300000b1000001d663000092210000bb720003066200000e4300003a300001400000006a3000042b5200008b42000402800003bb62000051000004ea4000023e2000000f410004cb300000ea80000341040000da300004fe3000009b3000000407000004030004aa7000005b320000c73000048a2000000e630003df500003fa100004f72000008a70000120000002ba3000008b8100000e300003de400003a35000000e7600000f3000016a8000010b8000023f2100022f210001c6420000ea500002ea700004910000001a7000024a6000031b600003eb800001b6520002210500023f50000100000002f6740001aa3200015a6000039b700004fe4000005a700002110600010b4100001a200002350500004a100002250400000e5300016b800000a3600000d0000001a100000196530000ab510002bb600002aa40000357650000c00000015b400004d10000023101000221020003475400044780000133210000676000047a500004477000009a30000186420003376500017a31000327760001665300005b800002110100033a5000000f210001564300047a3000000f750003ca7000007b510002e6740000db7000012b300000b00000000e4200004100000457600004c1000000a0000001177000000f7200023e5300000f5300022e4300025b5000038b600004c74000006b400001fb400003d7700003eb4000047a6000009b7000033a4000015a800002cb3000023e3100022e3200042a700002c6730000900000015a4000024b7000004b600000800000029b800001465300005b6000009b32000070000001ea700002aa710002910000003b4100055a6000042b310001db5000025b600000600000025b4000031b71000307650004f10000013653000050000000400000040a6000050b60000421000000ca3000027b4200012a3100008a5000017b4000000101000441000003fb200002b6740002a6640000ba720002ca5000022f20000005000002fa3100001b5100036f500001165300010100000113500001fa7000011b6000053a4000051b4000016a70000026300003db50000203600004da3000035b600001a321000030000000bb5000026b800001ca600001db80000106530003ab8000010a500003de2000025a4000014100000063600003ea800000f652000133500000e6420003d7200001fb6000001a3000027b620000d6530004262100022e520004575000025b300000040600025a600000c33000036b610002f7760000c66300002000000257400002866300022f400002b1000002a1000000100000013b8000013b6000000f54000000000002767300010a3000041a600001cb5000023f40

  | 9 => 0x40600000f5400000000000005060000010600000e2100000e640000063000000f4300000f6300000e6200000f4000000f5300000f1000000105000005040000010000000e4200000e2000000e5000000f5000000f6200000f6400000103000005010000065100000f4100000f3100000e1000000e7400000e60000001040000075400000e310000010100000f3000000e7000000f650000040000000f7200000f74000004050000050700000e7200000f3200000e650000040300000f6000000e750000050000000f5200000750000007310000010700000e300000050500000f7600000e54000005020000040400000e3200000f710000040200000e5300000f6100000f2100000e5200000e7100000e6300000e4100000f42000004070000040100000e6100000e7600000e5100000e4300000f2000000f7500000e7300000e4000000f7000000f51000005030000010200000f7300000732

  | _ => 0

def Z (s : ℕ) := bar 228 (Sgen 228 10 xs PT) NN (idxGen NN HT) id [] s

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_4_0 : span (Z 4) 16 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_4_1 : span (Z 4) 2 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_5_0 : span (Z 5) 16 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_5_1 : span (Z 5) 16 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_5_2 : span (Z 5) 16 32 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_5_3 : span (Z 5) 16 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_5_4 : span (Z 5) 16 64 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_5_5 : span (Z 5) 16 80 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_5_6 : span (Z 5) 16 96 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_5_7 : span (Z 5) 16 112 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_5_8 : span (Z 5) 16 128 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_5_9 : span (Z 5) 16 144 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_5_10 : span (Z 5) 16 160 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_5_11 : span (Z 5) 16 176 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_5_12 : span (Z 5) 16 192 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_5_13 : span (Z 5) 2 208 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_0 : span (Z 6) 16 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_1 : span (Z 6) 16 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_2 : span (Z 6) 16 32 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_3 : span (Z 6) 16 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_4 : span (Z 6) 16 64 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_5 : span (Z 6) 16 80 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_6 : span (Z 6) 16 96 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_7 : span (Z 6) 16 112 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_8 : span (Z 6) 16 128 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_9 : span (Z 6) 16 144 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_10 : span (Z 6) 16 160 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_11 : span (Z 6) 16 176 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_12 : span (Z 6) 16 192 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_13 : span (Z 6) 16 208 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_14 : span (Z 6) 16 224 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_15 : span (Z 6) 16 240 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_16 : span (Z 6) 16 256 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_17 : span (Z 6) 16 272 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_18 : span (Z 6) 16 288 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_19 : span (Z 6) 16 304 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_20 : span (Z 6) 16 320 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_21 : span (Z 6) 16 336 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_22 : span (Z 6) 16 352 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_23 : span (Z 6) 16 368 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_24 : span (Z 6) 16 384 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_25 : span (Z 6) 16 400 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_26 : span (Z 6) 16 416 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_27 : span (Z 6) 16 432 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_28 : span (Z 6) 16 448 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_29 : span (Z 6) 16 464 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_30 : span (Z 6) 16 480 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_31 : span (Z 6) 16 496 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_32 : span (Z 6) 16 512 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_33 : span (Z 6) 16 528 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_34 : span (Z 6) 16 544 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_35 : span (Z 6) 16 560 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_36 : span (Z 6) 16 576 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_37 : span (Z 6) 16 592 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_38 : span (Z 6) 16 608 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_39 : span (Z 6) 16 624 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_40 : span (Z 6) 16 640 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_41 : span (Z 6) 16 656 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_42 : span (Z 6) 16 672 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_43 : span (Z 6) 16 688 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_44 : span (Z 6) 16 704 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_45 : span (Z 6) 16 720 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_46 : span (Z 6) 16 736 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_47 : span (Z 6) 16 752 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_48 : span (Z 6) 16 768 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_49 : span (Z 6) 16 784 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_50 : span (Z 6) 16 800 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_51 : span (Z 6) 16 816 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_52 : span (Z 6) 16 832 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_53 : span (Z 6) 16 848 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_54 : span (Z 6) 16 864 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_55 : span (Z 6) 16 880 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_56 : span (Z 6) 16 896 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_57 : span (Z 6) 16 912 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_58 : span (Z 6) 16 928 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_59 : span (Z 6) 16 944 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_60 : span (Z 6) 16 960 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_61 : span (Z 6) 16 976 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_62 : span (Z 6) 16 992 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_63 : span (Z 6) 16 1008 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_64 : span (Z 6) 16 1024 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_65 : span (Z 6) 16 1040 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_66 : span (Z 6) 16 1056 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_6_67 : span (Z 6) 9 1072 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_0 : span (Z 7) 16 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_1 : span (Z 7) 16 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_2 : span (Z 7) 16 32 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_3 : span (Z 7) 16 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_4 : span (Z 7) 16 64 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_5 : span (Z 7) 16 80 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_6 : span (Z 7) 16 96 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_7 : span (Z 7) 16 112 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_8 : span (Z 7) 16 128 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_9 : span (Z 7) 16 144 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_10 : span (Z 7) 16 160 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_11 : span (Z 7) 16 176 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_12 : span (Z 7) 16 192 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_13 : span (Z 7) 16 208 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_14 : span (Z 7) 16 224 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_15 : span (Z 7) 16 240 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_16 : span (Z 7) 16 256 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_17 : span (Z 7) 16 272 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_18 : span (Z 7) 16 288 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_19 : span (Z 7) 16 304 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_20 : span (Z 7) 16 320 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_21 : span (Z 7) 16 336 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_22 : span (Z 7) 16 352 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_23 : span (Z 7) 16 368 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_24 : span (Z 7) 16 384 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_25 : span (Z 7) 16 400 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_26 : span (Z 7) 16 416 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_27 : span (Z 7) 16 432 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_28 : span (Z 7) 16 448 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_29 : span (Z 7) 16 464 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_30 : span (Z 7) 16 480 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_31 : span (Z 7) 16 496 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_32 : span (Z 7) 16 512 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_33 : span (Z 7) 16 528 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_34 : span (Z 7) 16 544 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_35 : span (Z 7) 16 560 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_36 : span (Z 7) 16 576 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_37 : span (Z 7) 16 592 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_38 : span (Z 7) 16 608 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_39 : span (Z 7) 16 624 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_40 : span (Z 7) 16 640 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_41 : span (Z 7) 16 656 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_42 : span (Z 7) 16 672 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_43 : span (Z 7) 16 688 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_44 : span (Z 7) 16 704 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_45 : span (Z 7) 16 720 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_46 : span (Z 7) 16 736 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_47 : span (Z 7) 16 752 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_48 : span (Z 7) 16 768 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_49 : span (Z 7) 16 784 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_50 : span (Z 7) 16 800 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_51 : span (Z 7) 16 816 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_52 : span (Z 7) 16 832 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_53 : span (Z 7) 16 848 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_54 : span (Z 7) 16 864 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_55 : span (Z 7) 16 880 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_56 : span (Z 7) 16 896 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_57 : span (Z 7) 16 912 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_58 : span (Z 7) 16 928 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_59 : span (Z 7) 16 944 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_60 : span (Z 7) 16 960 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_61 : span (Z 7) 16 976 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_62 : span (Z 7) 16 992 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_63 : span (Z 7) 16 1008 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_64 : span (Z 7) 16 1024 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_65 : span (Z 7) 16 1040 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_66 : span (Z 7) 16 1056 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_67 : span (Z 7) 16 1072 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_68 : span (Z 7) 16 1088 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_69 : span (Z 7) 16 1104 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_70 : span (Z 7) 16 1120 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_71 : span (Z 7) 16 1136 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_72 : span (Z 7) 16 1152 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_73 : span (Z 7) 16 1168 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_74 : span (Z 7) 16 1184 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_75 : span (Z 7) 16 1200 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_76 : span (Z 7) 16 1216 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_77 : span (Z 7) 16 1232 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_78 : span (Z 7) 16 1248 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_79 : span (Z 7) 16 1264 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_80 : span (Z 7) 16 1280 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_81 : span (Z 7) 16 1296 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_82 : span (Z 7) 16 1312 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_83 : span (Z 7) 16 1328 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_84 : span (Z 7) 16 1344 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_85 : span (Z 7) 16 1360 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_86 : span (Z 7) 16 1376 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_87 : span (Z 7) 16 1392 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_88 : span (Z 7) 16 1408 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_89 : span (Z 7) 16 1424 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_90 : span (Z 7) 16 1440 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_91 : span (Z 7) 16 1456 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_92 : span (Z 7) 16 1472 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_93 : span (Z 7) 16 1488 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_94 : span (Z 7) 16 1504 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_95 : span (Z 7) 16 1520 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_96 : span (Z 7) 16 1536 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_97 : span (Z 7) 16 1552 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_98 : span (Z 7) 16 1568 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_99 : span (Z 7) 16 1584 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_100 : span (Z 7) 16 1600 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_101 : span (Z 7) 16 1616 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_102 : span (Z 7) 16 1632 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_103 : span (Z 7) 16 1648 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_104 : span (Z 7) 16 1664 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_105 : span (Z 7) 16 1680 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_106 : span (Z 7) 16 1696 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_107 : span (Z 7) 16 1712 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_108 : span (Z 7) 16 1728 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_109 : span (Z 7) 16 1744 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_110 : span (Z 7) 16 1760 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_111 : span (Z 7) 16 1776 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_112 : span (Z 7) 16 1792 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_113 : span (Z 7) 16 1808 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_114 : span (Z 7) 16 1824 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_115 : span (Z 7) 16 1840 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_116 : span (Z 7) 16 1856 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_117 : span (Z 7) 16 1872 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_118 : span (Z 7) 16 1888 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_119 : span (Z 7) 16 1904 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_120 : span (Z 7) 16 1920 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_121 : span (Z 7) 16 1936 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_122 : span (Z 7) 16 1952 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_123 : span (Z 7) 16 1968 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_124 : span (Z 7) 16 1984 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_125 : span (Z 7) 16 2000 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_126 : span (Z 7) 16 2016 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_127 : span (Z 7) 16 2032 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_128 : span (Z 7) 16 2048 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_129 : span (Z 7) 16 2064 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_130 : span (Z 7) 16 2080 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_131 : span (Z 7) 16 2096 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_132 : span (Z 7) 16 2112 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_133 : span (Z 7) 16 2128 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_134 : span (Z 7) 16 2144 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_135 : span (Z 7) 16 2160 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_136 : span (Z 7) 16 2176 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_137 : span (Z 7) 16 2192 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_138 : span (Z 7) 16 2208 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_139 : span (Z 7) 16 2224 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_140 : span (Z 7) 16 2240 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_141 : span (Z 7) 16 2256 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_142 : span (Z 7) 16 2272 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_143 : span (Z 7) 16 2288 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_144 : span (Z 7) 16 2304 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_145 : span (Z 7) 16 2320 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_146 : span (Z 7) 16 2336 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_147 : span (Z 7) 16 2352 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_148 : span (Z 7) 16 2368 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_149 : span (Z 7) 16 2384 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_150 : span (Z 7) 16 2400 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_7_151 : span (Z 7) 9 2416 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_0 : span (Z 8) 16 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_1 : span (Z 8) 16 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_2 : span (Z 8) 16 32 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_3 : span (Z 8) 16 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_4 : span (Z 8) 16 64 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_5 : span (Z 8) 16 80 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_6 : span (Z 8) 16 96 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_7 : span (Z 8) 16 112 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_8 : span (Z 8) 16 128 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_9 : span (Z 8) 16 144 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_10 : span (Z 8) 16 160 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_11 : span (Z 8) 16 176 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_12 : span (Z 8) 16 192 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_13 : span (Z 8) 16 208 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_14 : span (Z 8) 16 224 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_15 : span (Z 8) 16 240 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_16 : span (Z 8) 16 256 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_17 : span (Z 8) 16 272 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_18 : span (Z 8) 16 288 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_19 : span (Z 8) 16 304 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_20 : span (Z 8) 16 320 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_21 : span (Z 8) 16 336 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_22 : span (Z 8) 16 352 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_23 : span (Z 8) 16 368 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_24 : span (Z 8) 16 384 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_25 : span (Z 8) 16 400 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_26 : span (Z 8) 16 416 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_27 : span (Z 8) 16 432 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_28 : span (Z 8) 16 448 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_29 : span (Z 8) 16 464 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_30 : span (Z 8) 16 480 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_31 : span (Z 8) 16 496 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_32 : span (Z 8) 16 512 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_33 : span (Z 8) 16 528 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_34 : span (Z 8) 16 544 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_35 : span (Z 8) 16 560 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_36 : span (Z 8) 16 576 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_37 : span (Z 8) 16 592 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_38 : span (Z 8) 16 608 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_39 : span (Z 8) 16 624 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_40 : span (Z 8) 16 640 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_41 : span (Z 8) 16 656 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_42 : span (Z 8) 16 672 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_43 : span (Z 8) 16 688 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_44 : span (Z 8) 16 704 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_45 : span (Z 8) 16 720 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_46 : span (Z 8) 16 736 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_47 : span (Z 8) 16 752 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_48 : span (Z 8) 16 768 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_49 : span (Z 8) 16 784 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_50 : span (Z 8) 16 800 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_51 : span (Z 8) 16 816 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_52 : span (Z 8) 16 832 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_53 : span (Z 8) 16 848 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_54 : span (Z 8) 16 864 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_55 : span (Z 8) 16 880 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_56 : span (Z 8) 16 896 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_57 : span (Z 8) 16 912 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_58 : span (Z 8) 16 928 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_59 : span (Z 8) 16 944 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_60 : span (Z 8) 16 960 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_61 : span (Z 8) 16 976 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_62 : span (Z 8) 16 992 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_63 : span (Z 8) 16 1008 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_64 : span (Z 8) 16 1024 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_65 : span (Z 8) 16 1040 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_66 : span (Z 8) 16 1056 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_67 : span (Z 8) 16 1072 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_68 : span (Z 8) 16 1088 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_69 : span (Z 8) 16 1104 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_70 : span (Z 8) 16 1120 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_71 : span (Z 8) 16 1136 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_72 : span (Z 8) 16 1152 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_73 : span (Z 8) 16 1168 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_74 : span (Z 8) 16 1184 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_75 : span (Z 8) 16 1200 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_76 : span (Z 8) 16 1216 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_77 : span (Z 8) 16 1232 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_78 : span (Z 8) 16 1248 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_79 : span (Z 8) 16 1264 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_80 : span (Z 8) 16 1280 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_81 : span (Z 8) 16 1296 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_82 : span (Z 8) 16 1312 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_83 : span (Z 8) 16 1328 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_84 : span (Z 8) 16 1344 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_85 : span (Z 8) 16 1360 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_86 : span (Z 8) 16 1376 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_87 : span (Z 8) 16 1392 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_88 : span (Z 8) 16 1408 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_89 : span (Z 8) 16 1424 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_90 : span (Z 8) 16 1440 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_91 : span (Z 8) 16 1456 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_92 : span (Z 8) 16 1472 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_93 : span (Z 8) 16 1488 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_94 : span (Z 8) 16 1504 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_95 : span (Z 8) 16 1520 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_96 : span (Z 8) 16 1536 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_97 : span (Z 8) 16 1552 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_98 : span (Z 8) 16 1568 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_8_99 : span (Z 8) 16 1584 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_9_0 : span (Z 9) 16 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_9_1 : span (Z 9) 16 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_9_2 : span (Z 9) 16 32 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_9_3 : span (Z 9) 16 48 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_9_4 : span (Z 9) 16 64 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_9_5 : span (Z 9) 7 80 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma check_10_0 : span (Z 10) 1 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma all_checks : ∀ s ≤ 10, ∀ i < NN s, Z s i = true := by
  intro s hs
  interval_cases s

  · intro i hi
    simp [NN] at hi

  · intro i hi
    simp [NN] at hi

  · intro i hi
    simp [NN] at hi

  · intro i hi
    simp [NN] at hi

  · intro i hi
    have hn : i < 18 := hi
    have hd : i / 16 < 2 := by omega
    interval_cases h : i / 16

    · exact span_ok check_4_0 i (by omega) (by omega)

    · exact span_ok check_4_1 i (by omega) (by omega)

  · intro i hi
    have hn : i < 210 := hi
    have hd : i / 16 < 14 := by omega
    interval_cases h : i / 16

    · exact span_ok check_5_0 i (by omega) (by omega)

    · exact span_ok check_5_1 i (by omega) (by omega)

    · exact span_ok check_5_2 i (by omega) (by omega)

    · exact span_ok check_5_3 i (by omega) (by omega)

    · exact span_ok check_5_4 i (by omega) (by omega)

    · exact span_ok check_5_5 i (by omega) (by omega)

    · exact span_ok check_5_6 i (by omega) (by omega)

    · exact span_ok check_5_7 i (by omega) (by omega)

    · exact span_ok check_5_8 i (by omega) (by omega)

    · exact span_ok check_5_9 i (by omega) (by omega)

    · exact span_ok check_5_10 i (by omega) (by omega)

    · exact span_ok check_5_11 i (by omega) (by omega)

    · exact span_ok check_5_12 i (by omega) (by omega)

    · exact span_ok check_5_13 i (by omega) (by omega)

  · intro i hi
    have hn : i < 1081 := hi
    have hd : i / 16 < 68 := by omega
    interval_cases h : i / 16

    · exact span_ok check_6_0 i (by omega) (by omega)

    · exact span_ok check_6_1 i (by omega) (by omega)

    · exact span_ok check_6_2 i (by omega) (by omega)

    · exact span_ok check_6_3 i (by omega) (by omega)

    · exact span_ok check_6_4 i (by omega) (by omega)

    · exact span_ok check_6_5 i (by omega) (by omega)

    · exact span_ok check_6_6 i (by omega) (by omega)

    · exact span_ok check_6_7 i (by omega) (by omega)

    · exact span_ok check_6_8 i (by omega) (by omega)

    · exact span_ok check_6_9 i (by omega) (by omega)

    · exact span_ok check_6_10 i (by omega) (by omega)

    · exact span_ok check_6_11 i (by omega) (by omega)

    · exact span_ok check_6_12 i (by omega) (by omega)

    · exact span_ok check_6_13 i (by omega) (by omega)

    · exact span_ok check_6_14 i (by omega) (by omega)

    · exact span_ok check_6_15 i (by omega) (by omega)

    · exact span_ok check_6_16 i (by omega) (by omega)

    · exact span_ok check_6_17 i (by omega) (by omega)

    · exact span_ok check_6_18 i (by omega) (by omega)

    · exact span_ok check_6_19 i (by omega) (by omega)

    · exact span_ok check_6_20 i (by omega) (by omega)

    · exact span_ok check_6_21 i (by omega) (by omega)

    · exact span_ok check_6_22 i (by omega) (by omega)

    · exact span_ok check_6_23 i (by omega) (by omega)

    · exact span_ok check_6_24 i (by omega) (by omega)

    · exact span_ok check_6_25 i (by omega) (by omega)

    · exact span_ok check_6_26 i (by omega) (by omega)

    · exact span_ok check_6_27 i (by omega) (by omega)

    · exact span_ok check_6_28 i (by omega) (by omega)

    · exact span_ok check_6_29 i (by omega) (by omega)

    · exact span_ok check_6_30 i (by omega) (by omega)

    · exact span_ok check_6_31 i (by omega) (by omega)

    · exact span_ok check_6_32 i (by omega) (by omega)

    · exact span_ok check_6_33 i (by omega) (by omega)

    · exact span_ok check_6_34 i (by omega) (by omega)

    · exact span_ok check_6_35 i (by omega) (by omega)

    · exact span_ok check_6_36 i (by omega) (by omega)

    · exact span_ok check_6_37 i (by omega) (by omega)

    · exact span_ok check_6_38 i (by omega) (by omega)

    · exact span_ok check_6_39 i (by omega) (by omega)

    · exact span_ok check_6_40 i (by omega) (by omega)

    · exact span_ok check_6_41 i (by omega) (by omega)

    · exact span_ok check_6_42 i (by omega) (by omega)

    · exact span_ok check_6_43 i (by omega) (by omega)

    · exact span_ok check_6_44 i (by omega) (by omega)

    · exact span_ok check_6_45 i (by omega) (by omega)

    · exact span_ok check_6_46 i (by omega) (by omega)

    · exact span_ok check_6_47 i (by omega) (by omega)

    · exact span_ok check_6_48 i (by omega) (by omega)

    · exact span_ok check_6_49 i (by omega) (by omega)

    · exact span_ok check_6_50 i (by omega) (by omega)

    · exact span_ok check_6_51 i (by omega) (by omega)

    · exact span_ok check_6_52 i (by omega) (by omega)

    · exact span_ok check_6_53 i (by omega) (by omega)

    · exact span_ok check_6_54 i (by omega) (by omega)

    · exact span_ok check_6_55 i (by omega) (by omega)

    · exact span_ok check_6_56 i (by omega) (by omega)

    · exact span_ok check_6_57 i (by omega) (by omega)

    · exact span_ok check_6_58 i (by omega) (by omega)

    · exact span_ok check_6_59 i (by omega) (by omega)

    · exact span_ok check_6_60 i (by omega) (by omega)

    · exact span_ok check_6_61 i (by omega) (by omega)

    · exact span_ok check_6_62 i (by omega) (by omega)

    · exact span_ok check_6_63 i (by omega) (by omega)

    · exact span_ok check_6_64 i (by omega) (by omega)

    · exact span_ok check_6_65 i (by omega) (by omega)

    · exact span_ok check_6_66 i (by omega) (by omega)

    · exact span_ok check_6_67 i (by omega) (by omega)

  · intro i hi
    have hn : i < 2425 := hi
    have hd : i / 16 < 152 := by omega
    interval_cases h : i / 16

    · exact span_ok check_7_0 i (by omega) (by omega)

    · exact span_ok check_7_1 i (by omega) (by omega)

    · exact span_ok check_7_2 i (by omega) (by omega)

    · exact span_ok check_7_3 i (by omega) (by omega)

    · exact span_ok check_7_4 i (by omega) (by omega)

    · exact span_ok check_7_5 i (by omega) (by omega)

    · exact span_ok check_7_6 i (by omega) (by omega)

    · exact span_ok check_7_7 i (by omega) (by omega)

    · exact span_ok check_7_8 i (by omega) (by omega)

    · exact span_ok check_7_9 i (by omega) (by omega)

    · exact span_ok check_7_10 i (by omega) (by omega)

    · exact span_ok check_7_11 i (by omega) (by omega)

    · exact span_ok check_7_12 i (by omega) (by omega)

    · exact span_ok check_7_13 i (by omega) (by omega)

    · exact span_ok check_7_14 i (by omega) (by omega)

    · exact span_ok check_7_15 i (by omega) (by omega)

    · exact span_ok check_7_16 i (by omega) (by omega)

    · exact span_ok check_7_17 i (by omega) (by omega)

    · exact span_ok check_7_18 i (by omega) (by omega)

    · exact span_ok check_7_19 i (by omega) (by omega)

    · exact span_ok check_7_20 i (by omega) (by omega)

    · exact span_ok check_7_21 i (by omega) (by omega)

    · exact span_ok check_7_22 i (by omega) (by omega)

    · exact span_ok check_7_23 i (by omega) (by omega)

    · exact span_ok check_7_24 i (by omega) (by omega)

    · exact span_ok check_7_25 i (by omega) (by omega)

    · exact span_ok check_7_26 i (by omega) (by omega)

    · exact span_ok check_7_27 i (by omega) (by omega)

    · exact span_ok check_7_28 i (by omega) (by omega)

    · exact span_ok check_7_29 i (by omega) (by omega)

    · exact span_ok check_7_30 i (by omega) (by omega)

    · exact span_ok check_7_31 i (by omega) (by omega)

    · exact span_ok check_7_32 i (by omega) (by omega)

    · exact span_ok check_7_33 i (by omega) (by omega)

    · exact span_ok check_7_34 i (by omega) (by omega)

    · exact span_ok check_7_35 i (by omega) (by omega)

    · exact span_ok check_7_36 i (by omega) (by omega)

    · exact span_ok check_7_37 i (by omega) (by omega)

    · exact span_ok check_7_38 i (by omega) (by omega)

    · exact span_ok check_7_39 i (by omega) (by omega)

    · exact span_ok check_7_40 i (by omega) (by omega)

    · exact span_ok check_7_41 i (by omega) (by omega)

    · exact span_ok check_7_42 i (by omega) (by omega)

    · exact span_ok check_7_43 i (by omega) (by omega)

    · exact span_ok check_7_44 i (by omega) (by omega)

    · exact span_ok check_7_45 i (by omega) (by omega)

    · exact span_ok check_7_46 i (by omega) (by omega)

    · exact span_ok check_7_47 i (by omega) (by omega)

    · exact span_ok check_7_48 i (by omega) (by omega)

    · exact span_ok check_7_49 i (by omega) (by omega)

    · exact span_ok check_7_50 i (by omega) (by omega)

    · exact span_ok check_7_51 i (by omega) (by omega)

    · exact span_ok check_7_52 i (by omega) (by omega)

    · exact span_ok check_7_53 i (by omega) (by omega)

    · exact span_ok check_7_54 i (by omega) (by omega)

    · exact span_ok check_7_55 i (by omega) (by omega)

    · exact span_ok check_7_56 i (by omega) (by omega)

    · exact span_ok check_7_57 i (by omega) (by omega)

    · exact span_ok check_7_58 i (by omega) (by omega)

    · exact span_ok check_7_59 i (by omega) (by omega)

    · exact span_ok check_7_60 i (by omega) (by omega)

    · exact span_ok check_7_61 i (by omega) (by omega)

    · exact span_ok check_7_62 i (by omega) (by omega)

    · exact span_ok check_7_63 i (by omega) (by omega)

    · exact span_ok check_7_64 i (by omega) (by omega)

    · exact span_ok check_7_65 i (by omega) (by omega)

    · exact span_ok check_7_66 i (by omega) (by omega)

    · exact span_ok check_7_67 i (by omega) (by omega)

    · exact span_ok check_7_68 i (by omega) (by omega)

    · exact span_ok check_7_69 i (by omega) (by omega)

    · exact span_ok check_7_70 i (by omega) (by omega)

    · exact span_ok check_7_71 i (by omega) (by omega)

    · exact span_ok check_7_72 i (by omega) (by omega)

    · exact span_ok check_7_73 i (by omega) (by omega)

    · exact span_ok check_7_74 i (by omega) (by omega)

    · exact span_ok check_7_75 i (by omega) (by omega)

    · exact span_ok check_7_76 i (by omega) (by omega)

    · exact span_ok check_7_77 i (by omega) (by omega)

    · exact span_ok check_7_78 i (by omega) (by omega)

    · exact span_ok check_7_79 i (by omega) (by omega)

    · exact span_ok check_7_80 i (by omega) (by omega)

    · exact span_ok check_7_81 i (by omega) (by omega)

    · exact span_ok check_7_82 i (by omega) (by omega)

    · exact span_ok check_7_83 i (by omega) (by omega)

    · exact span_ok check_7_84 i (by omega) (by omega)

    · exact span_ok check_7_85 i (by omega) (by omega)

    · exact span_ok check_7_86 i (by omega) (by omega)

    · exact span_ok check_7_87 i (by omega) (by omega)

    · exact span_ok check_7_88 i (by omega) (by omega)

    · exact span_ok check_7_89 i (by omega) (by omega)

    · exact span_ok check_7_90 i (by omega) (by omega)

    · exact span_ok check_7_91 i (by omega) (by omega)

    · exact span_ok check_7_92 i (by omega) (by omega)

    · exact span_ok check_7_93 i (by omega) (by omega)

    · exact span_ok check_7_94 i (by omega) (by omega)

    · exact span_ok check_7_95 i (by omega) (by omega)

    · exact span_ok check_7_96 i (by omega) (by omega)

    · exact span_ok check_7_97 i (by omega) (by omega)

    · exact span_ok check_7_98 i (by omega) (by omega)

    · exact span_ok check_7_99 i (by omega) (by omega)

    · exact span_ok check_7_100 i (by omega) (by omega)

    · exact span_ok check_7_101 i (by omega) (by omega)

    · exact span_ok check_7_102 i (by omega) (by omega)

    · exact span_ok check_7_103 i (by omega) (by omega)

    · exact span_ok check_7_104 i (by omega) (by omega)

    · exact span_ok check_7_105 i (by omega) (by omega)

    · exact span_ok check_7_106 i (by omega) (by omega)

    · exact span_ok check_7_107 i (by omega) (by omega)

    · exact span_ok check_7_108 i (by omega) (by omega)

    · exact span_ok check_7_109 i (by omega) (by omega)

    · exact span_ok check_7_110 i (by omega) (by omega)

    · exact span_ok check_7_111 i (by omega) (by omega)

    · exact span_ok check_7_112 i (by omega) (by omega)

    · exact span_ok check_7_113 i (by omega) (by omega)

    · exact span_ok check_7_114 i (by omega) (by omega)

    · exact span_ok check_7_115 i (by omega) (by omega)

    · exact span_ok check_7_116 i (by omega) (by omega)

    · exact span_ok check_7_117 i (by omega) (by omega)

    · exact span_ok check_7_118 i (by omega) (by omega)

    · exact span_ok check_7_119 i (by omega) (by omega)

    · exact span_ok check_7_120 i (by omega) (by omega)

    · exact span_ok check_7_121 i (by omega) (by omega)

    · exact span_ok check_7_122 i (by omega) (by omega)

    · exact span_ok check_7_123 i (by omega) (by omega)

    · exact span_ok check_7_124 i (by omega) (by omega)

    · exact span_ok check_7_125 i (by omega) (by omega)

    · exact span_ok check_7_126 i (by omega) (by omega)

    · exact span_ok check_7_127 i (by omega) (by omega)

    · exact span_ok check_7_128 i (by omega) (by omega)

    · exact span_ok check_7_129 i (by omega) (by omega)

    · exact span_ok check_7_130 i (by omega) (by omega)

    · exact span_ok check_7_131 i (by omega) (by omega)

    · exact span_ok check_7_132 i (by omega) (by omega)

    · exact span_ok check_7_133 i (by omega) (by omega)

    · exact span_ok check_7_134 i (by omega) (by omega)

    · exact span_ok check_7_135 i (by omega) (by omega)

    · exact span_ok check_7_136 i (by omega) (by omega)

    · exact span_ok check_7_137 i (by omega) (by omega)

    · exact span_ok check_7_138 i (by omega) (by omega)

    · exact span_ok check_7_139 i (by omega) (by omega)

    · exact span_ok check_7_140 i (by omega) (by omega)

    · exact span_ok check_7_141 i (by omega) (by omega)

    · exact span_ok check_7_142 i (by omega) (by omega)

    · exact span_ok check_7_143 i (by omega) (by omega)

    · exact span_ok check_7_144 i (by omega) (by omega)

    · exact span_ok check_7_145 i (by omega) (by omega)

    · exact span_ok check_7_146 i (by omega) (by omega)

    · exact span_ok check_7_147 i (by omega) (by omega)

    · exact span_ok check_7_148 i (by omega) (by omega)

    · exact span_ok check_7_149 i (by omega) (by omega)

    · exact span_ok check_7_150 i (by omega) (by omega)

    · exact span_ok check_7_151 i (by omega) (by omega)

  · intro i hi
    have hn : i < 1600 := hi
    have hd : i / 16 < 100 := by omega
    interval_cases h : i / 16

    · exact span_ok check_8_0 i (by omega) (by omega)

    · exact span_ok check_8_1 i (by omega) (by omega)

    · exact span_ok check_8_2 i (by omega) (by omega)

    · exact span_ok check_8_3 i (by omega) (by omega)

    · exact span_ok check_8_4 i (by omega) (by omega)

    · exact span_ok check_8_5 i (by omega) (by omega)

    · exact span_ok check_8_6 i (by omega) (by omega)

    · exact span_ok check_8_7 i (by omega) (by omega)

    · exact span_ok check_8_8 i (by omega) (by omega)

    · exact span_ok check_8_9 i (by omega) (by omega)

    · exact span_ok check_8_10 i (by omega) (by omega)

    · exact span_ok check_8_11 i (by omega) (by omega)

    · exact span_ok check_8_12 i (by omega) (by omega)

    · exact span_ok check_8_13 i (by omega) (by omega)

    · exact span_ok check_8_14 i (by omega) (by omega)

    · exact span_ok check_8_15 i (by omega) (by omega)

    · exact span_ok check_8_16 i (by omega) (by omega)

    · exact span_ok check_8_17 i (by omega) (by omega)

    · exact span_ok check_8_18 i (by omega) (by omega)

    · exact span_ok check_8_19 i (by omega) (by omega)

    · exact span_ok check_8_20 i (by omega) (by omega)

    · exact span_ok check_8_21 i (by omega) (by omega)

    · exact span_ok check_8_22 i (by omega) (by omega)

    · exact span_ok check_8_23 i (by omega) (by omega)

    · exact span_ok check_8_24 i (by omega) (by omega)

    · exact span_ok check_8_25 i (by omega) (by omega)

    · exact span_ok check_8_26 i (by omega) (by omega)

    · exact span_ok check_8_27 i (by omega) (by omega)

    · exact span_ok check_8_28 i (by omega) (by omega)

    · exact span_ok check_8_29 i (by omega) (by omega)

    · exact span_ok check_8_30 i (by omega) (by omega)

    · exact span_ok check_8_31 i (by omega) (by omega)

    · exact span_ok check_8_32 i (by omega) (by omega)

    · exact span_ok check_8_33 i (by omega) (by omega)

    · exact span_ok check_8_34 i (by omega) (by omega)

    · exact span_ok check_8_35 i (by omega) (by omega)

    · exact span_ok check_8_36 i (by omega) (by omega)

    · exact span_ok check_8_37 i (by omega) (by omega)

    · exact span_ok check_8_38 i (by omega) (by omega)

    · exact span_ok check_8_39 i (by omega) (by omega)

    · exact span_ok check_8_40 i (by omega) (by omega)

    · exact span_ok check_8_41 i (by omega) (by omega)

    · exact span_ok check_8_42 i (by omega) (by omega)

    · exact span_ok check_8_43 i (by omega) (by omega)

    · exact span_ok check_8_44 i (by omega) (by omega)

    · exact span_ok check_8_45 i (by omega) (by omega)

    · exact span_ok check_8_46 i (by omega) (by omega)

    · exact span_ok check_8_47 i (by omega) (by omega)

    · exact span_ok check_8_48 i (by omega) (by omega)

    · exact span_ok check_8_49 i (by omega) (by omega)

    · exact span_ok check_8_50 i (by omega) (by omega)

    · exact span_ok check_8_51 i (by omega) (by omega)

    · exact span_ok check_8_52 i (by omega) (by omega)

    · exact span_ok check_8_53 i (by omega) (by omega)

    · exact span_ok check_8_54 i (by omega) (by omega)

    · exact span_ok check_8_55 i (by omega) (by omega)

    · exact span_ok check_8_56 i (by omega) (by omega)

    · exact span_ok check_8_57 i (by omega) (by omega)

    · exact span_ok check_8_58 i (by omega) (by omega)

    · exact span_ok check_8_59 i (by omega) (by omega)

    · exact span_ok check_8_60 i (by omega) (by omega)

    · exact span_ok check_8_61 i (by omega) (by omega)

    · exact span_ok check_8_62 i (by omega) (by omega)

    · exact span_ok check_8_63 i (by omega) (by omega)

    · exact span_ok check_8_64 i (by omega) (by omega)

    · exact span_ok check_8_65 i (by omega) (by omega)

    · exact span_ok check_8_66 i (by omega) (by omega)

    · exact span_ok check_8_67 i (by omega) (by omega)

    · exact span_ok check_8_68 i (by omega) (by omega)

    · exact span_ok check_8_69 i (by omega) (by omega)

    · exact span_ok check_8_70 i (by omega) (by omega)

    · exact span_ok check_8_71 i (by omega) (by omega)

    · exact span_ok check_8_72 i (by omega) (by omega)

    · exact span_ok check_8_73 i (by omega) (by omega)

    · exact span_ok check_8_74 i (by omega) (by omega)

    · exact span_ok check_8_75 i (by omega) (by omega)

    · exact span_ok check_8_76 i (by omega) (by omega)

    · exact span_ok check_8_77 i (by omega) (by omega)

    · exact span_ok check_8_78 i (by omega) (by omega)

    · exact span_ok check_8_79 i (by omega) (by omega)

    · exact span_ok check_8_80 i (by omega) (by omega)

    · exact span_ok check_8_81 i (by omega) (by omega)

    · exact span_ok check_8_82 i (by omega) (by omega)

    · exact span_ok check_8_83 i (by omega) (by omega)

    · exact span_ok check_8_84 i (by omega) (by omega)

    · exact span_ok check_8_85 i (by omega) (by omega)

    · exact span_ok check_8_86 i (by omega) (by omega)

    · exact span_ok check_8_87 i (by omega) (by omega)

    · exact span_ok check_8_88 i (by omega) (by omega)

    · exact span_ok check_8_89 i (by omega) (by omega)

    · exact span_ok check_8_90 i (by omega) (by omega)

    · exact span_ok check_8_91 i (by omega) (by omega)

    · exact span_ok check_8_92 i (by omega) (by omega)

    · exact span_ok check_8_93 i (by omega) (by omega)

    · exact span_ok check_8_94 i (by omega) (by omega)

    · exact span_ok check_8_95 i (by omega) (by omega)

    · exact span_ok check_8_96 i (by omega) (by omega)

    · exact span_ok check_8_97 i (by omega) (by omega)

    · exact span_ok check_8_98 i (by omega) (by omega)

    · exact span_ok check_8_99 i (by omega) (by omega)

  · intro i hi
    have hn : i < 87 := hi
    have hd : i / 16 < 6 := by omega
    interval_cases h : i / 16

    · exact span_ok check_9_0 i (by omega) (by omega)

    · exact span_ok check_9_1 i (by omega) (by omega)

    · exact span_ok check_9_2 i (by omega) (by omega)

    · exact span_ok check_9_3 i (by omega) (by omega)

    · exact span_ok check_9_4 i (by omega) (by omega)

    · exact span_ok check_9_5 i (by omega) (by omega)

  · intro i hi
    have hn : i < 1 := hi
    have hd : i / 16 < 1 := by omega
    interval_cases h : i / 16

    · exact span_ok check_10_0 i (by omega) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma checked : ∀ s : ℕ, HasCircuitSize 8 target s → 11 ≤ s := by
  exact prove_base 8 228 10 target rows xs [] NN HT PT
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) all_checks

end PEqualNP.Outside.L_meta_8485

theorem PEqualNP.Outside.L_meta_8485 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 7) || (x 6 && x 7)) t → 11 ≤ t :=
  PEqualNP.Outside.L_meta_8485.checked
