import PEqualNP.Defs

-- The input restriction uses the constant-propagation construction from L_meta_1908.

namespace PEqualNP.Outside.L_meta_9410.Restriction

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover

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

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2


theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

abbrev Stat : Type := Bool ⊕ ℕ

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

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
  | _ => (none, Sum.inl false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or) (hlen : ins.length ≤ 2)
    (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl
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

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

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
    obtain ⟨t, ht, htl⟩ := wiresFrom_start r.1.toList w'
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


theorem elim_count (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, Ok g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (elim n gs acc).2.length + gs.countP (fun g => decide (k ∈ g.inputs))
      ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _; simp [elim]
  | cons g gs ih =>
    intro acc hok hk hc
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (by simp [elimStep]; omega)
      (by
        obtain ⟨c, hc⟩ := hc
        refine ⟨c, ?_⟩
        simp only [elimStep]
        rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
    rw [h3, List.length_cons, List.countP_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1
        · simpa using hnok.2
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      simp only [hkg, decide_true, ite_true]
      omega
    · have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      simp only [hkg, decide_false, Bool.false_eq_true, ite_false]
      omega

theorem getD_ofFn' {α : Type} (m : ℕ) (f : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn f).getD j.val d = f j := by
  simp [List.getD_eq_getElem?_getD]

end PEqualNP.Outside.L_meta_9410.Restriction

namespace PEqualNP.Outside.L_meta_9410.WireEval

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt2 (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt2 gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt2 gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt2 _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma mono_ops {C : Circuit} (hM : Monotone2 C) :
    ∀ k < C.gates.length, (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or := by
  intro k hk
  exact (hM _ (gateAt_mem hk)).1

end PEqualNP.Outside.L_meta_9410.WireEval

namespace PEqualNP.Outside.L_meta_9410.DeleteInput

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open PEqualNP.Outside.L_meta_9410.Restriction PEqualNP.Outside.L_meta_9410.WireEval

def pull {n m : ℕ} (source : Fin n → Option (Fin m)) (y : Fin m → Bool) (i : Fin n) : Bool :=
  ((source i).map y).getD false

def code {n m : ℕ} (source : Fin n → Option (Fin m)) (i : Fin n) : Stat :=
  match source i with
  | none => Sum.inl false
  | some j => Sum.inr j.val

theorem deleteInput {n m : ℕ} (C : Circuit) (mono : Monotone2 C) (source : Fin n → Option (Fin m))
    (p : Fin n) (removed : source p = none) (reader : ∃ g ∈ C.gates, p.val ∈ g.inputs)
    (rejects : ∃ y, circuitFun n C (pull source y) = false) :
    ∃ D : Circuit, Monotone2 D ∧ circuitFun m D = (fun y => circuitFun n C (pull source y)) ∧
      D.size < C.size := by
  let start : List Stat × List Gate := (List.ofFn (code source),[])
  let finish := elim m C.gates start
  have seed (y : Fin m → Bool) : Inv m (List.ofFn y) (List.ofFn (pull source y)) start := by
    refine ⟨by simp [start],?_⟩
    intro i
    by_cases inside : i < n
    · let t : Fin n := ⟨i,inside⟩
      change ((List.ofFn (code source)).getD t.val _).Valid (m+0) ∧
        ((List.ofFn (code source)).getD t.val _).val (List.ofFn y) = (List.ofFn (pull source y)).getD t.val _
      rw [getD_ofFn',getD_ofFn']
      cases h : source t with
      | none => simp [code,h,pull,Stat.Valid,Stat.val]
      | some u => simp [code,h,pull,Stat.Valid,Stat.val,u.isLt]
    · have a : start.1.getD i (Sum.inl false) = Sum.inl false :=
        List.getD_eq_default _ _ (by simp [start]; omega)
      have b : (List.ofFn (pull source y)).getD i false = false :=
        List.getD_eq_default _ _ (by simp; omega)
      rw [a,b]; exact ⟨trivial,rfl⟩
  have known : start.1.getD p.val (Sum.inl false) = Sum.inl false := by
    change (List.ofFn (code source)).getD p.val _ = _
    rw [getD_ofFn']; simp [code,removed]
  have limit := elim_count m p.val C.gates start mono (by simp [start]) ⟨false,known⟩
  have cost : finish.2.length + C.gates.countP (fun g => decide (p.val ∈ g.inputs)) ≤ C.size := by
    simpa [start,finish,Circuit.size] using limit
  obtain ⟨g,hg,read⟩ := reader
  have charge : 0 < C.gates.countP (fun h => decide (p.val ∈ h.inputs)) := by
    by_contra! zero
    exact (List.countP_eq_zero.mp (Nat.le_zero.mp zero) g hg) (decide_eq_true read)
  have short : finish.2.length < C.size := by omega
  let out := finish.1.getD C.output (Sum.inl false)
  have eval (y : Fin m → Bool) :
      out.val (wiresFrom finish.2 (List.ofFn y)) = circuitFun n C (pull source y) :=
    ((inv_elim m (List.ofFn y) (by simp) C.gates _ start mono (seed y)).2 C.output).2
  have legal : ∀ h ∈ finish.2, Ok h := elim_ok m C.gates start (by simp [start])
  cases result : out with
  | inr i =>
    refine ⟨⟨finish.2,i⟩,legal,?_,short⟩
    funext y
    have h := eval y
    rw [result] at h
    exact h
  | inl b =>
    have const (y : Fin m → Bool) : b = circuitFun n C (pull source y) := by
      have h := eval y
      rw [result] at h
      exact h
    obtain ⟨y,hy⟩ := rejects
    have off : b = false := (const y).trans hy
    refine ⟨⟨[],m⟩,by intro h mem; simp at mem,?_,by change 0 < C.size; omega⟩
    funext z
    change (List.ofFn z).getD m false = _
    rw [List.getD_eq_default _ _ (by simp)]
    exact off.symm.trans (const z)

theorem read_of_separation {n : ℕ} (C : Circuit) (mono : Monotone2 C) (p : Fin n)
    (out : C.output ≠ p.val) (x y : Fin n → Bool)
    (ordered : ∀ t, t ≠ p → x t = true → y t = true)
    (on : circuitFun n C x = true) (off : circuitFun n C y = false) :
    ∃ g ∈ C.gates, p.val ∈ g.inputs := by
  by_contra! unread
  have wires (w : ℕ) : w ≠ p.val → val C (List.ofFn x) w = true → val C (List.ofFn y) w = true := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro ne
      by_cases raw : w < n
      · let t : Fin n := ⟨w,raw⟩
        rw [val_input List.length_ofFn raw,val_input List.length_ofFn raw]
        simpa [t,raw] using ordered t (fun eq => ne (congrArg Fin.val eq))
      by_cases past : n+C.gates.length ≤ w
      · rw [val_ge List.length_ofFn past]; simp
      obtain ⟨k,rfl⟩ : ∃ k, w=n+k := ⟨w-n,by omega⟩
      have valid : k < C.gates.length := by omega
      rw [val_gate List.length_ofFn valid,val_gate List.length_ofFn valid]
      apply opMono_imp _ (mono_ops mono k valid)
      intro i hi
      by_cases earlier : i < n+k
      · simp only [earlier,ite_true]
        exact ih i earlier (fun eq => unread _ (gateAt_mem valid) (eq ▸ hi))
      · simp [earlier]
  have contradiction := wires C.output out on
  change circuitFun n C y = true at contradiction
  simp [off] at contradiction

end PEqualNP.Outside.L_meta_9410.DeleteInput

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.Outside.L_meta_9410.WireEval

namespace PEqualNP.Outside.L_meta_9410

private def selected {n : ℕ} (a b : ℕ) (i : Fin n) : Bool := decide (i.val = a ∨ i.val = b)

theorem row_reader (C : Circuit) (hm : Monotone2 C)
    (hr : Represents (fun u v : Fin 5 => (7571262 : ℕ).testBit (5*u.val+v.val)) C) :
    ∃ g ∈ C.gates, 2 ∈ g.inputs := by
  have out : C.output ≠ 2 := by
    intro eq
    have off := hr 2 1
    change val C (oneEach (2 : Fin 5) (1 : Fin 5)) C.output = false at off
    rw [eq,val_input (n := 10) (by decide) (by decide)] at off
    exact Bool.noConfusion (show true = false from off)
  apply DeleteInput.read_of_separation C hm (2 : Fin 10) out (selected 2 5) (selected 0 5)
  · decide
  · change C.eval (List.ofFn (selected 2 5 : Fin 10 → Bool)) = true
    rw [show List.ofFn (selected 2 5 : Fin 10 → Bool) = oneEach (2 : Fin 5) (0 : Fin 5) by decide]
    exact hr 2 0
  · change C.eval (List.ofFn (selected 0 5 : Fin 10 → Bool)) = false
    rw [show List.ofFn (selected 0 5 : Fin 10 → Bool) = oneEach (0 : Fin 5) (0 : Fin 5) by decide]
    exact hr 0 0

theorem col_reader (C : Circuit) (hm : Monotone2 C)
    (hr : Represents (fun (u : Fin 4) (v : Fin 5) => (237374 : ℕ).testBit (5*u.val+v.val)) C) :
    ∃ g ∈ C.gates, 6 ∈ g.inputs := by
  have out : C.output ≠ 6 := by
    intro eq
    have off := hr 1 2
    change val C (oneEach (1 : Fin 4) (2 : Fin 5)) C.output = false at off
    rw [eq,val_input (n := 9) (by decide) (by decide)] at off
    exact Bool.noConfusion (show true = false from off)
  apply DeleteInput.read_of_separation C hm (6 : Fin 9) out (selected 0 6) (selected 0 4)
  · decide
  · change C.eval (List.ofFn (selected 0 6 : Fin 9 → Bool)) = true
    rw [show List.ofFn (selected 0 6 : Fin 9 → Bool) = oneEach (0 : Fin 4) (2 : Fin 5) by decide]
    exact hr 0 2
  · change C.eval (List.ofFn (selected 0 4 : Fin 9 → Bool)) = false
    rw [show List.ofFn (selected 0 4 : Fin 9 → Bool) = oneEach (0 : Fin 4) (0 : Fin 5) by decide]
    exact hr 0 0

end PEqualNP.Outside.L_meta_9410

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

namespace PEqualNP.Outside.L_meta_9410.Applications

def cell {n m : ℕ} (u : Fin n) (v : Fin m) (w : Fin (n + m)) : Bool :=
  (oneEach u v).getD w.val false

def skip : Fin 4 → Fin 5 := fun i => ([0, 1, 3, 4] : List (Fin 5)).getD i.val 0

def rowMap (i : Fin 10) : Option (Fin 9) :=
  ([some 0, some 1, none, some 2, some 3, some 4, some 5, some 6, some 7, some 8] : List (Option (Fin 9))).getD i.val none

theorem rowStep (C : Circuit) (hm : Monotone2 C) (hr : Represents (fun (u : Fin 5) (v : Fin 5) => (7571262 : ℕ).testBit (5 * u.val + v.val)) C)
    (reads : ∃ g ∈ C.gates, 2 ∈ g.inputs) :
    ∃ D : Circuit, Monotone2 D ∧ Represents (fun (u : Fin 4) (v : Fin 5) => (237374 : ℕ).testBit (5 * u.val + v.val)) D ∧ D.size < C.size := by
  have embed : ∀ (u : Fin 4) (v : Fin 5),
      List.ofFn (DeleteInput.pull rowMap (cell u v)) = oneEach (skip u) v := by decide
  have table : ∀ (u : Fin 4) (v : Fin 5),
      (7571262 : ℕ).testBit (5 * (skip u).val + v.val) = (237374 : ℕ).testBit (5 * u.val + v.val) := by decide
  have compute (u : Fin 4) (v : Fin 5) :
      circuitFun 10 C (DeleteInput.pull rowMap (cell u v)) = (237374 : ℕ).testBit (5 * u.val + v.val) := by
    change C.eval (List.ofFn _) = _
    rw [embed u v, hr (skip u) v]
    exact table u v
  have reject : ∃ y, circuitFun 10 C (DeleteInput.pull rowMap y) = false :=
    ⟨cell (0 : Fin 4) (0 : Fin 5), (compute 0 0).trans (by decide)⟩
  obtain ⟨D, hD, heq, hsize⟩ := DeleteInput.deleteInput C hm rowMap 2 (by decide) reads reject
  refine ⟨D, hD, ?_, hsize⟩
  intro u v
  have cells : ∀ (a : Fin 4) (b : Fin 5), List.ofFn (cell a b) = oneEach a b := by decide
  rw [← cells u v]
  change circuitFun 9 D (cell u v) = _
  rw [heq]
  exact compute u v

def colMap (i : Fin 9) : Option (Fin 8) :=
  ([some 0, some 1, some 2, some 3, some 4, some 5, none, some 6, some 7] : List (Option (Fin 8))).getD i.val none

theorem colStep (C : Circuit) (hm : Monotone2 C) (hr : Represents (fun (u : Fin 4) (v : Fin 5) => (237374 : ℕ).testBit (5 * u.val + v.val)) C)
    (reads : ∃ g ∈ C.gates, 6 ∈ g.inputs) :
    ∃ D : Circuit, Monotone2 D ∧ Represents (fun (u : Fin 4) (v : Fin 4) => (13278 : ℕ).testBit (4 * u.val + v.val)) D ∧ D.size < C.size := by
  have embed : ∀ (u : Fin 4) (v : Fin 4),
      List.ofFn (DeleteInput.pull colMap (cell u v)) = oneEach u (skip v) := by decide
  have table : ∀ (u : Fin 4) (v : Fin 4),
      (237374 : ℕ).testBit (5 * u.val + (skip v).val) = (13278 : ℕ).testBit (4 * u.val + v.val) := by decide
  have compute (u : Fin 4) (v : Fin 4) :
      circuitFun 9 C (DeleteInput.pull colMap (cell u v)) = (13278 : ℕ).testBit (4 * u.val + v.val) := by
    change C.eval (List.ofFn _) = _
    rw [embed u v, hr u (skip v)]
    exact table u v
  have reject : ∃ y, circuitFun 9 C (DeleteInput.pull colMap y) = false :=
    ⟨cell (0 : Fin 4) (0 : Fin 4), (compute 0 0).trans (by decide)⟩
  obtain ⟨D, hD, heq, hsize⟩ := DeleteInput.deleteInput C hm colMap 6 (by decide) reads reject
  refine ⟨D, hD, ?_, hsize⟩
  intro u v
  have cells : ∀ (a : Fin 4) (b : Fin 4), List.ofFn (cell a b) = oneEach a b := by decide
  rw [← cells u v]
  change circuitFun 8 D (cell u v) = _
  rw [heq]
  exact compute u v

end PEqualNP.Outside.L_meta_9410.Applications

-- Adapted from Bastian Milan's L_meta_6297 in open-goat/pequalnp-proofs
-- (commit 38d0ac39, Apache-2.0). Only the verified lower bound is needed here.
namespace PEqualNP.Outside.L_meta_9410.Certified13278

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 120

def ops (x y : W) : List W := [x &&& y, x ||| y]

def sep (x : W) : BitVec 60 := ((x >>> 60) &&& ~~~x).setWidth 60

def cuts (ws : List W) : BitVec 60 := ws.foldr (fun w v => sep w ||| v) 0

def goal : W := (-1 : BitVec 60) ++ (0 : BitVec 60)

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

def rawInputs : List W :=
  [0x3ffff041041041041041, 0xffffc0000082082082082082, 0xfff00000000030c30c30c30c30c, 0xfff000000000000c30c30c30c30c30, 0x3f03f000fc0000041041041041041, 0xfc0fc000000003f082082082082082, 0x3f000fc0514514514514514, 0xfc003f000a28a28a28a28a28]

def inputs : List W := rawInputs

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 60) (w : W) : Prop :=
  w.getLsbD (60 + i.val) = true ∧ w.getLsbD i.val = false

theorem ops_differs (i : Fin 60) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  unfold differs at hd ⊢
  rcases hz with rfl | rfl <;> revert hd <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or] <;>
    cases a.getLsbD (60 + i.val) <;> cases a.getLsbD i.val <;>
    cases b.getLsbD (60 + i.val) <;> cases b.getLsbD i.val <;> simp

theorem goal_differs : ∀ i : Fin 60, differs i goal := by
  unfold differs
  decide

theorem cuts_spec (ws : List W) (i : Fin 60) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have hi : i.val < 120 := by omega
    simp [sep, i.isLt, differs, hi, Nat.add_comm]

theorem cuts_full {k : ℕ} {ws : List W} (h : live basicOps goal k ws.toFinset) :
    cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (goal_differs ⟨j, hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 60)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp [basicOps, ops, BitVec.and_comm, BitVec.or_comm]

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def possible (w : List W) (z : W) : Bool :=
  z == 0 || z == BitVec.allOnes 120 || w.any (fun u => z == u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit (k : Fin 120) (z : W) : Bool := z[k.val]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 120) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

private theorem read_wire (w : List W) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

private theorem atom {ws : List W} {x : W} (hx : x = 0 ∨ x ∈ ws) : possible ws x := by
  rcases hx with rfl | hx
  · simp [possible]
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    exact .inr ⟨x, hx, .inl rfl⟩

private theorem pair {ws : List W} {x y : W} (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
    possible ws (x &&& y) ∧ possible ws (x ||| y) := by
  rcases hx with rfl | hx
  · simpa [possible] using atom hy
  rcases hy with rfl | hy
  · simpa [possible] using atom (.inr hx)
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    constructor
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inl rfl⟩⟩
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inr rfl⟩⟩

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

set_option maxRecDepth 2000 in
private theorem gate_table (w ws : List W) (hw : w ⊆ ws) (g : Gate) (hg : legal g) :
    ∃ z, possible ws z ∧ ∀ k, step (w.map (bit k)) g = (w ++ [z]).map (bit k) := by
  have mem (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ ws :=
    (read_wire w i).imp_right (fun h => hw h)
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl
    · exact ⟨BitVec.allOnes 120, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
    · exact ⟨0, by simp [possible], by simp [step, GateOp.eval, bit]⟩
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl
      · exact ⟨_, atom (mem i),
          by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, atom (mem i),
          by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl
        · exact ⟨_, (pair (mem i) (mem j)).1,
            by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
        · exact ⟨_, (pair (mem i) (mem j)).2,
            by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩

def represents (available : Finset W) (w : List W) : Prop :=
  ∀ u ∈ w, u = 0 ∨ u = BitVec.allOnes 120 ∨ u ∈ available

theorem classify {available : Finset W} {ws : List W} (hw : represents available ws)
    {z : W} (hz : possible ws z) :
    z = 0 ∨ z = BitVec.allOnes 120 ∨ z ∈ available ∨
      ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ z ∈ basicOps a b := by
  have lift {t : W} (h : t = 0 ∨ t = BitVec.allOnes 120 ∨ t ∈ available) :
      t = 0 ∨ t = BitVec.allOnes 120 ∨ t ∈ available ∨
        ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ t ∈ basicOps a b :=
    h.imp_right (Or.imp_right Or.inl)
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hz
  rcases hz with ((h | h) | ⟨x, hx, h | ⟨y, hy, h | h⟩⟩)
  · exact .inl h
  · exact .inr (.inl h)
  · subst z; exact lift (hw _ hx)
  · subst z
    rcases hw _ hx with rfl | rfl | hu
    · left; simp
    · rw [BitVec.allOnes_and]; exact lift (hw _ hy)
    rcases hw _ hy with rfl | rfl | hv
    · left; simp
    · rw [BitVec.and_allOnes]; exact .inr (.inr (.inl hu))
    by_cases h : x = y
    · subst h; rw [BitVec.and_self]; exact .inr (.inr (.inl hu))
    · exact .inr (.inr (.inr ⟨x, hu, y, hv, h, by simp [basicOps, ops]⟩))
  · subst z
    rcases hw _ hx with rfl | rfl | hu
    · rw [show (0 : W) ||| y = y by ext i hi; simp]; exact lift (hw _ hy)
    · right; left; exact BitVec.allOnes_or
    rcases hw _ hy with rfl | rfl | hv
    · rw [show x ||| (0 : W) = x by ext i hi; simp]; exact .inr (.inr (.inl hu))
    · right; left; exact BitVec.or_allOnes
    by_cases h : x = y
    · subst h; rw [BitVec.or_self]; exact .inr (.inr (.inl hu))
    · exact .inr (.inr (.inr ⟨x, hu, y, hv, h, by simp [basicOps, ops]⟩))

private theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : represents av w)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k goal) :
    build basicOps goal gs.length av := by
  induction gs generalizing w av with
  | nil =>
    have hval : w.getD out 0 = goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i, hi⟩
    have hr := read_wire w out
    rw [hval] at hr
    rcases hr with hz | hm
    · exact False.elim ((by decide : goal ≠ (0 : W)) hz)
    · rcases hw _ hm with h | h | h
      · exact False.elim ((by decide : goal ≠ (0 : W)) h)
      · exact False.elim ((by decide : goal ≠ BitVec.allOnes 120) h)
      · exact h
  | cons g gs ih =>
    obtain ⟨z, hz, hstep⟩ := gate_table w w (fun _ h => h) g (hg g (by simp))
    have fn := ih (fun g' h => hg g' (by simp [h])) (w ++ [z])
    have he' : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, hstep] using he k
    have appendOK (h : z = 0 ∨ z = BitVec.allOnes 120 ∨ z ∈ av) : represents av (w ++ [z]) := by
      intro u hu
      rcases List.mem_append.mp hu with old | fresh
      · exact hw _ old
      · have eq : u = z := List.mem_singleton.mp fresh
        exact eq ▸ h
    rcases classify hw hz with h | h | h | ⟨a, ha, b, hb, hab, hop⟩
    · exact Or.inl (fn av (appendOK (.inl h)) he')
    · exact Or.inl (fn av (appendOK (.inr (.inl h))) he')
    · exact Or.inl (fn av (appendOK (.inr (.inr h))) he')
    · refine Or.inr ⟨a, ha, b, hb, hab, z, hop, fn (insert z av) ?_ he'⟩
      intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · exact (hw _ hu).imp_right (Or.imp_right (Finset.mem_insert_of_mem ·))
      · simp_all

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => ws == [goal]
  | k + 1, extra, ws => ws == [goal] ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps goal n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps goal k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def A : Fin 4 → Fin 4 → Bool := fun u v : Fin 4 => (13278 : ℕ).testBit (4 * u.val + v.val)

def posL : List (Fin 4 × Fin 4) :=
  [(0, 1), (0, 2), (0, 3), (1, 0), (1, 2), (1, 3), (2, 0), (2, 1), (3, 0), (3, 1)]

def negL : List (Fin 4 × Fin 4) :=
  [(0, 0), (1, 1), (2, 2), (2, 3), (3, 2), (3, 3)]

def samp (k : Fin 120) : Fin 4 × Fin 4 :=
  if k.val < 60 then negL.getD (k.val % 6) (0, 0) else posL.getD ((k.val - 60) / 6) (0, 0)

theorem input_rows : ∀ k : Fin 120,
    rawInputs.map (bit k) = PEqualNP.Represents.oneEach (samp k).1 (samp k).2 := by
  decide +kernel

theorem goal_rows : ∀ k : Fin 120, bit k goal = A (samp k).1 (samp k).2 := by
  decide +kernel

theorem rows_eval (C : Circuit) (hr : PEqualNP.Represents.Represents A C) (k : Fin 120) :
    (C.gates.foldl step (rawInputs.map (bit k))).getD C.output false = bit k goal := by
  rw [input_rows k, goal_rows k]
  exact hr (samp k).1 (samp k).2

theorem initial_rep : represents inputs.toFinset rawInputs := by
  intro u hu
  exact .inr (.inr (List.mem_toFinset.mpr hu))

theorem get_build (C : Circuit) (hg : Monotone2 C) (hr : PEqualNP.Represents.Represents A C) :
    build basicOps goal C.gates.length inputs.toFinset :=
  compile C.gates C.output hg rawInputs inputs.toFinset initial_rep (rows_eval C hr)

theorem extend_live {m n : ℕ} {s : Finset W} (le : m ≤ n) (h : live basicOps goal m s) :
    live basicOps goal n s := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih

theorem inputs_nodup : inputs.Nodup := by decide +kernel

def tab0 : List (ℕ × List W) :=
  [(1, [0x3f03f000ffffff041041041041041, 0xffffc0000082082082082082, 0xfff00000000030c30c30c30c30c, 0xfff000000000000c30c30c30c30c30, 0xfc0fc000000003f082082082082082, 0x3f000fc0514514514514514, 0xfc003f000a28a28a28a28a28])]

def tab1 : List (ℕ × List W) :=
  [(0, [0x3f03f000ffffff041041041041041, 0x3ffff041041041041041, 0xffffc0000082082082082082, 0xfff00000000030c30c30c30c30c, 0xfff000000000000c30c30c30c30c30, 0xfc0fc000000003f082082082082082, 0x3f000fc0514514514514514, 0xfc003f000a28a28a28a28a28])]

def tab2 : List (ℕ × List W) :=
  [(0, [0x3f03f000ffffff041041041041041, 0x3f03f000fc0000041041041041041, 0xffffc0000082082082082082, 0xfff00000000030c30c30c30c30c, 0xfff000000000000c30c30c30c30c30, 0xfc0fc000000003f082082082082082, 0x3f000fc0514514514514514, 0xfc003f000a28a28a28a28a28])]

def tab3 : List (ℕ × List W) :=
  [(1, [0xfc0fc0ffffc003f082082082082082, 0x3ffff041041041041041, 0xfff00000000030c30c30c30c30c, 0xfff000000000000c30c30c30c30c30, 0x3f03f000fc0000041041041041041, 0x3f000fc0514514514514514, 0xfc003f000a28a28a28a28a28])]

def tab4 : List (ℕ × List W) :=
  [(0, [0xfc0fc0ffffc003f082082082082082, 0xffffc0000082082082082082, 0x3ffff041041041041041, 0xfff00000000030c30c30c30c30c, 0xfff000000000000c30c30c30c30c30, 0x3f03f000fc0000041041041041041, 0x3f000fc0514514514514514, 0xfc003f000a28a28a28a28a28])]

def tab5 : List (ℕ × List W) :=
  [(0, [0xfc0fc0ffffc003f082082082082082, 0xfc0fc000000003f082082082082082, 0x3ffff041041041041041, 0xfff00000000030c30c30c30c30c, 0xfff000000000000c30c30c30c30c30, 0x3f03f000fc0000041041041041041, 0x3f000fc0514514514514514, 0xfc003f000a28a28a28a28a28])]

def tab6 : List (ℕ × List W) :=
  [(1, [0xffffff000000000f3cf3cf3cf3cf3c, 0x3ffff041041041041041, 0xffffc0000082082082082082, 0x3f03f000fc0000041041041041041, 0xfc0fc000000003f082082082082082, 0x3f000fc0514514514514514, 0xfc003f000a28a28a28a28a28])]

def tab7 : List (ℕ × List W) :=
  [(0, [0xffffff000000000f3cf3cf3cf3cf3c, 0xfff00000000030c30c30c30c30c, 0x3ffff041041041041041, 0xffffc0000082082082082082, 0x3f03f000fc0000041041041041041, 0xfc0fc000000003f082082082082082, 0x3f000fc0514514514514514, 0xfc003f000a28a28a28a28a28])]

def tab8 : List (ℕ × List W) :=
  [(0, [0xffffff000000000f3cf3cf3cf3cf3c, 0xfff000000000000c30c30c30c30c30, 0x3ffff041041041041041, 0xffffc0000082082082082082, 0x3f03f000fc0000041041041041041, 0xfc0fc000000003f082082082082082, 0x3f000fc0514514514514514, 0xfc003f000a28a28a28a28a28])]

def tab9 : List (ℕ × List W) :=
  [(1, [0xfff03f000fc071c71c71c71c71c, 0x3ffff041041041041041, 0xffffc0000082082082082082, 0xfff000000000000c30c30c30c30c30, 0x3f03f000fc0000041041041041041, 0xfc0fc000000003f082082082082082, 0xfc003f000a28a28a28a28a28])]

def tab10 : List (ℕ × List W) :=
  [(0, [0xfff03f000fc071c71c71c71c71c, 0xfff00000000030c30c30c30c30c, 0x3ffff041041041041041, 0xffffc0000082082082082082, 0xfff000000000000c30c30c30c30c30, 0x3f03f000fc0000041041041041041, 0xfc0fc000000003f082082082082082, 0xfc003f000a28a28a28a28a28])]

def tab11 : List (ℕ × List W) :=
  [(0, [0xfff03f000fc071c71c71c71c71c, 0x3f000fc0514514514514514, 0x3ffff041041041041041, 0xffffc0000082082082082082, 0xfff000000000000c30c30c30c30c30, 0x3f03f000fc0000041041041041041, 0xfc0fc000000003f082082082082082, 0xfc003f000a28a28a28a28a28])]

def tab12 : List (ℕ × List W) :=
  [(1, [0xffffc003f000b2cb2cb2cb2cb2c, 0x3ffff041041041041041, 0xffffc0000082082082082082, 0xfff000000000000c30c30c30c30c30, 0x3f03f000fc0000041041041041041, 0xfc0fc000000003f082082082082082, 0x3f000fc0514514514514514])]

def tab13 : List (ℕ × List W) :=
  [(0, [0xffffc003f000b2cb2cb2cb2cb2c, 0xfff00000000030c30c30c30c30c, 0x3ffff041041041041041, 0xffffc0000082082082082082, 0xfff000000000000c30c30c30c30c30, 0x3f03f000fc0000041041041041041, 0xfc0fc000000003f082082082082082, 0x3f000fc0514514514514514])]

def tab14 : List (ℕ × List W) :=
  [(0, [0xffffc003f000b2cb2cb2cb2cb2c, 0xfc003f000a28a28a28a28a28, 0x3ffff041041041041041, 0xffffc0000082082082082082, 0xfff000000000000c30c30c30c30c30, 0x3f03f000fc0000041041041041041, 0xfc0fc000000003f082082082082082, 0x3f000fc0514514514514514])]

def tab15 : List (ℕ × List W) :=
  [(1, [0xfff00003f000fc0d34d34d34d34d34, 0x3ffff041041041041041, 0xffffc0000082082082082082, 0xfff00000000030c30c30c30c30c, 0x3f03f000fc0000041041041041041, 0xfc0fc000000003f082082082082082, 0xfc003f000a28a28a28a28a28])]

def tab16 : List (ℕ × List W) :=
  [(0, [0xfff00003f000fc0d34d34d34d34d34, 0xfff000000000000c30c30c30c30c30, 0x3ffff041041041041041, 0xffffc0000082082082082082, 0xfff00000000030c30c30c30c30c, 0x3f03f000fc0000041041041041041, 0xfc0fc000000003f082082082082082, 0xfc003f000a28a28a28a28a28])]

def tab17 : List (ℕ × List W) :=
  [(0, [0xfff00003f000fc0d34d34d34d34d34, 0x3f000fc0514514514514514, 0x3ffff041041041041041, 0xffffc0000082082082082082, 0xfff00000000030c30c30c30c30c, 0x3f03f000fc0000041041041041041, 0xfc0fc000000003f082082082082082, 0xfc003f000a28a28a28a28a28])]

def tab18 : List (ℕ × List W) :=
  [(1, [0xfff000fc003f000e38e38e38e38e38, 0x3ffff041041041041041, 0xffffc0000082082082082082, 0xfff00000000030c30c30c30c30c, 0x3f03f000fc0000041041041041041, 0xfc0fc000000003f082082082082082, 0x3f000fc0514514514514514])]

def tab19 : List (ℕ × List W) :=
  [(0, [0xfff000fc003f000e38e38e38e38e38, 0xfff000000000000c30c30c30c30c30, 0x3ffff041041041041041, 0xffffc0000082082082082082, 0xfff00000000030c30c30c30c30c, 0x3f03f000fc0000041041041041041, 0xfc0fc000000003f082082082082082, 0x3f000fc0514514514514514])]

def tab20 : List (ℕ × List W) :=
  [(0, [0xfff000fc003f000e38e38e38e38e38, 0xfc003f000a28a28a28a28a28, 0x3ffff041041041041041, 0xffffc0000082082082082082, 0xfff00000000030c30c30c30c30c, 0x3f03f000fc0000041041041041041, 0xfc0fc000000003f082082082082082, 0x3f000fc0514514514514514])]

def tab21 : List (ℕ × List W) :=
  [(1, [0xfff03ffc0f3cf3cf3cf3cf3c, 0x3ffff041041041041041, 0xffffc0000082082082082082, 0xfff00000000030c30c30c30c30c, 0xfff000000000000c30c30c30c30c30, 0x3f03f000fc0000041041041041041, 0xfc0fc000000003f082082082082082])]

def tab22 : List (ℕ × List W) :=
  [(0, [0xfff03ffc0f3cf3cf3cf3cf3c, 0x3f000fc0514514514514514, 0x3ffff041041041041041, 0xffffc0000082082082082082, 0xfff00000000030c30c30c30c30c, 0xfff000000000000c30c30c30c30c30, 0x3f03f000fc0000041041041041041, 0xfc0fc000000003f082082082082082])]

def tab23 : List (ℕ × List W) :=
  [(0, [0xfff03ffc0f3cf3cf3cf3cf3c, 0xfc003f000a28a28a28a28a28, 0x3ffff041041041041041, 0xffffc0000082082082082082, 0xfff00000000030c30c30c30c30c, 0xfff000000000000c30c30c30c30c30, 0x3f03f000fc0000041041041041041, 0xfc0fc000000003f082082082082082])]

def table : List (ℕ × List W) := tab0 ++ tab1 ++ tab2 ++ tab3 ++ tab4 ++ tab5 ++ tab6 ++ tab7 ++ tab8 ++ tab9 ++ tab10 ++ tab11 ++ tab12 ++ tab13 ++ tab14 ++ tab15 ++ tab16 ++ tab17 ++ tab18 ++ tab19 ++ tab20 ++ tab21 ++ tab22 ++ tab23

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem leaf0 : tab0.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem leaf1 : tab1.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem leaf2 : tab2.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem leaf3 : tab3.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem leaf4 : tab4.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem leaf5 : tab5.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem leaf6 : tab6.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem leaf7 : tab7.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem leaf8 : tab8.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem leaf9 : tab9.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem leaf10 : tab10.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem leaf11 : tab11.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem leaf12 : tab12.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem leaf13 : tab13.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem leaf14 : tab14.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem leaf15 : tab15.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem leaf16 : tab16.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem leaf17 : tab17.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem leaf18 : tab18.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem leaf19 : tab19.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem leaf20 : tab20.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem leaf21 : tab21.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem leaf22 : tab22.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem leaf23 : tab23.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

theorem leaf_all : table.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  simp only [table, List.all_append, leaf0, leaf1, leaf2, leaf3, leaf4, leaf5, leaf6, leaf7, leaf8, leaf9, leaf10, leaf11, leaf12, leaf13, leaf14, leaf15, leaf16, leaf17, leaf18, leaf19, leaf20, leaf21, leaf22, leaf23, Bool.and_self]

def optT (e : ℕ) (ws : List W) : Bool := if (e, ws) ∈ table then false else optimized 7 e ws

theorem optT_eq : optT = optimized 7 := by
  funext e ws
  unfold optT
  split_ifs with h
  · have hc := List.all_eq_true.mp leaf_all _ h
    dsimp only at hc
    revert hc
    cases optimized 7 e ws <;> simp
  · rfl

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem full_false : optimized 8 1 inputs = false := by
  rw [optimized, ← optT_eq]
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem front_part : (inputs.sublists.take 255).all
    (fun l => decide (9 < l.length) || !(optimized 8 (9 - l.length) l)) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem last_part : inputs.sublists.drop 255 = [inputs] := by
  decide +kernel

theorem all_front : inputs.sublists.all
    (fun l => decide (9 < l.length) || !(optimized 8 (9 - l.length) l)) = true := by
  rw [← List.take_append_drop 255 inputs.sublists, List.all_append, front_part, last_part]
  have hl : inputs.length = 8 := rfl
  simp [hl, full_false]

theorem no_small (C : Circuit) (hm : Monotone2 C) (hs : C.size ≤ 8)
    (hr : PEqualNP.Represents.Represents A C) : False := by
  obtain ⟨S, hsub, hl⟩ := compress (get_build C hm hr)
  have hl3 : live basicOps goal 8 S := extend_live hs hl
  let l := inputs.filter (fun w => decide (w ∈ S))
  have hlS : l.toFinset = S := by
    ext v
    simp only [l, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨List.mem_toFinset.mp (hsub h), h⟩
  have hnd : l.Nodup := inputs_nodup.filter _
  have hcard := live_card hl3
  rw [← hlS, List.toFinset_card_of_nodup hnd] at hcard
  have hsearch := optimized_complete 8 l (9 - l.length) hnd (by omega) (hlS ▸ hl3)
  have hmem : l ∈ inputs.sublists := List.mem_sublists.mpr List.filter_sublist
  have hrow := List.all_eq_true.mp all_front l hmem
  have h4 : decide (9 < l.length) = false := by simp; omega
  rw [h4, hsearch] at hrow
  exact Bool.noConfusion hrow


theorem bound : ¬ PEqualNP.Represents.RepSizeAtMost
    (fun u v : Fin 4 => (13278 : ℕ).testBit (4 * u.val + v.val)) 8 := by
  rintro ⟨C,hm,hs,hr⟩
  exact no_small C hm hs hr

end PEqualNP.Outside.L_meta_9410.Certified13278

open PEqualNP.Outside.L_meta_9410

theorem PEqualNP.Outside.L_meta_9410 : ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (7571262 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  rintro ⟨C, hm, hs, hr⟩
  obtain ⟨D, hmD, hrD, hD⟩ := Applications.rowStep C hm hr (row_reader C hm hr)
  obtain ⟨E, hmE, hrE, hE⟩ := Applications.colStep D hmD hrD (col_reader D hmD hrD)
  exact Certified13278.bound ⟨E, hmE, by omega, hrE⟩
