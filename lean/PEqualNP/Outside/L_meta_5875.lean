import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5875

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma run_append (gs hs : List Gate) (w : List Bool) :
    run (gs ++ hs) w = run hs (run gs w) := by
  simp [run, List.foldl_append]

lemma run_ext (gs : List Gate) (w : List Bool) :
    ∃ t : List Bool, run gs w = w ++ t ∧ t.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp [run], rfl⟩
  | cons g gs ih =>
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    change run gs (w ++ [v]) = w ++ v :: t
    simp [ht]

lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := run_ext gs w
  rw [ht, List.length_append, hl]

lemma run_input (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := run_ext gs w
  rw [ht, List.getD_append _ _ _ _ hi]

lemma prefix_read (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (run (gs.take k) w).getD i false =
      if i < w.length + k then (run gs w).getD i false else false := by
  have hlen : (run (gs.take k) w).length = w.length + k := by
    rw [run_length, List.length_take, min_eq_left hk]
  split_ifs with hi
  · conv_rhs => rw [← List.take_append_drop k gs, run_append]
    exact (run_input _ _ _ (by omega)).symm
  · exact List.getD_eq_default _ _ (by omega)

lemma run_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (run gs w).getD (w.length + k) false =
      gs[k].op.eval (gs[k].inputs.map fun i =>
        if i < w.length + k then (run gs w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h
    exact h
  have hlen : (run (gs.take k) w).length = w.length + k := by
    rw [run_length, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have heq : run gs w =
      run (gs.drop (k + 1)) (run (gs.take k) w ++
        [gs[k].op.eval (gs[k].inputs.map fun i => (run (gs.take k) w).getD i false)]) := by
    conv_lhs => rw [hsplit, run_append]
    rfl
  calc
    (run gs w).getD (w.length + k) false =
        gs[k].op.eval (gs[k].inputs.map fun i => (run (gs.take k) w).getD i false) := by
      rw [heq, run_input]
      · simp [← hlen]
      · simp [hlen]
    _ = _ := by
      congr 1
      apply List.map_congr_left
      intro i _
      exact prefix_read gs w k i (Nat.le_of_lt hk)

abbrev Input := Fin 42 → Bool

def wire (C : Circuit) (y : Input) (i : ℕ) : Bool :=
  (C.wires (List.ofFn y)).getD i false

def read (C : Circuit) (y : Input) (k i : ℕ) : Bool :=
  if i < 42 + k then wire C y i else false

lemma wire_input (C : Circuit) (y : Input) (i : Fin 42) : wire C y i.val = y i := by
  change (run C.gates (List.ofFn y)).getD i.val false = y i
  rw [run_input, List.getD_eq_getElem, List.getElem_ofFn]
  all_goals simp

lemma wire_outside (C : Circuit) (y : Input) {i : ℕ} (hi : 42 + C.gates.length ≤ i) :
    wire C y i = false := by
  change (run C.gates (List.ofFn y)).getD i false = false
  exact List.getD_eq_default _ _ (by simpa [run_length] using hi)

lemma gate_sem (C : Circuit) (y : Input) {k : ℕ} {g : Gate}
    (hg : C.gates[k]? = some g) :
    wire C y (42 + k) = g.op.eval (g.inputs.map (read C y k)) := by
  obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.mp hg
  change (run C.gates (List.ofFn y)).getD (42 + k) false = _
  have h := run_gate C.gates (List.ofFn y) k hk
  rw [List.length_ofFn] at h
  exact h

lemma and_sem (C : Circuit) (y : Input) {k : ℕ} {g : Gate}
    (hg : C.gates[k]? = some g) (ho : g.op = .and) :
    wire C y (42 + k) = true ↔ ∀ i ∈ g.inputs, read C y k i = true := by
  simp [gate_sem C y hg, ho, GateOp.eval, List.all_eq_true]

lemma or_sem (C : Circuit) (y : Input) {k : ℕ} {g : Gate}
    (hg : C.gates[k]? = some g) (ho : g.op = .or) :
    wire C y (42 + k) = true ↔ ∃ i ∈ g.inputs, read C y k i = true := by
  simp [gate_sem C y hg, ho, GateOp.eval, List.any_eq_true]

lemma gate_mono {C : Circuit} (hc : Monotone2 C) {k : ℕ} {g : Gate}
    (hg : C.gates[k]? = some g) :
    (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.mp hg
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
    hc _ (List.getElem_mem hk)

lemma inputs_cases (l : List ℕ) (hl : l.length ≤ 2) :
    l = [] ∨ (∃ a, l = [a]) ∨ ∃ a b, l = [a, b] := by
  cases l with
  | nil => exact Or.inl rfl
  | cons a l =>
    cases l with
    | nil => exact Or.inr (Or.inl ⟨a, rfl⟩)
    | cons b l =>
      cases l with
      | nil => exact Or.inr (Or.inr ⟨a, b, rfl⟩)
      | cons c l => simp at hl

def base : List (Fin 42) := [0, 1, 2, 6, 8, 18, 24, 31, 33, 37]

def masks : List ℕ :=
  [693637218693, 214750724172, 43100670213, 2201724715076, 429513539622,
    10838245382, 1718003696225, 1387274437386, 3436007392450, 214756769811,
    412337856832, 3436108316976, 154640061441, 1168315262978]

def maskInput (m : ℕ) : Input := fun i => m.testBit i.val

def baseInput : Input := fun i => decide (i.val ∈ ([0, 1, 2, 6, 8, 18, 24, 31, 33, 37] : List ℕ))

lemma base_spec (i : Fin 42) : baseInput i = true ↔ i ∈ base := by
  change decide (i.val ∈ ([0, 1, 2, 6, 8, 18, 24, 31, 33, 37] : List ℕ)) = true ↔ i ∈ base
  rw [decide_eq_true_eq]
  have h : base.map Fin.val = [0, 1, 2, 6, 8, 18, 24, 31, 33, 37] := rfl
  rw [← h, List.mem_map]
  exact ⟨fun ⟨a, ha, he⟩ => Fin.ext he ▸ ha, fun hi => ⟨i, hi, rfl⟩⟩

set_option maxRecDepth 4000 in
lemma pairs_check : base.all (fun a => base.all (fun b =>
    masks.any (fun m => maskInput m a && maskInput m b))) = true := by decide

lemma pair_mask {a b : Fin 42} (ha : a ∈ base) (hb : b ∈ base) :
    ∃ m ∈ masks, maskInput m a = true ∧ maskInput m b = true := by
  have h := List.all_eq_true.mp (List.all_eq_true.mp pairs_check a ha) b hb
  simpa only [Bool.and_eq_true] using List.any_eq_true.mp h

def hit (C : Circuit) (y : Input) : Prop :=
  ∃ k g, C.gates[k]? = some g ∧ g.op = .and ∧ wire C y (42 + k) = true

lemma before_first_and {C : Circuit} (hc : Monotone2 C) {k : ℕ} (hk : k < C.gates.length)
    (hfirst : ∀ j < k, ∀ g, C.gates[j]? = some g → g.op = .and →
      wire C baseInput (42 + j) ≠ true) :
    ∀ w < 42 + k, wire C baseInput w = true →
      ∃ i ∈ base, ∀ y : Input, y i = true → wire C y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw htrue
    by_cases hin : w < 42
    · let i : Fin 42 := ⟨w, hin⟩
      have hi := (base_spec i).mp ((wire_input C baseInput i).symm.trans htrue)
      exact ⟨i, hi, fun y hy => (wire_input C y i).trans hy⟩
    · let j := w - 42
      have he : w = 42 + j := by dsimp [j]; omega
      have hj : j < k := by omega
      have hj' : j < C.gates.length := by omega
      let g := C.gates[j]
      have hg : C.gates[j]? = some g := List.getElem?_eq_getElem hj'
      have ht : wire C baseInput (42 + j) = true := he ▸ htrue
      have ho : g.op = .or := (gate_mono hc hg).1.resolve_left
        (fun ha => hfirst j hj g hg ha ht)
      obtain ⟨a, ha, hra⟩ := (or_sem C baseInput hg ho).mp ht
      by_cases hlt : a < 42 + j
      · have hwa : wire C baseInput a = true := by simpa [read, hlt] using hra
        obtain ⟨i, hi, hiw⟩ := ih a (by omega) (by omega) hwa
        refine ⟨i, hi, fun y hy => ?_⟩
        rw [he, or_sem C y hg ho]
        exact ⟨a, ha, by simpa [read, hlt] using hiw y hy⟩
      · simp [read, hlt] at hra

lemma first_and_transfer {C : Circuit} (hc : Monotone2 C) (hh : hit C baseInput) :
    ∃ m ∈ masks, hit C (maskInput m) := by
  classical
  let P := fun k => ∃ g, C.gates[k]? = some g ∧ g.op = .and ∧ wire C baseInput (42 + k) = true
  have hex : ∃ k, P k := hh
  let k := Nat.find hex
  obtain ⟨g, hg, ho, ht⟩ := Nat.find_spec hex
  have hg' : C.gates[k]? = some g := hg
  have hk : k < C.gates.length := (List.getElem?_eq_some_iff.mp hg').choose
  have hfirst : ∀ j < k, ∀ g, C.gates[j]? = some g → g.op = .and →
      wire C baseInput (42 + j) ≠ true := by
    intro j hj gate hgate hop hwire
    exact Nat.find_min hex hj ⟨gate, hgate, hop, hwire⟩
  have hread : ∀ a ∈ g.inputs, ∃ i ∈ base, ∀ y : Input, y i = true → read C y k a = true := by
    intro a ha
    have hr := (and_sem C baseInput hg' ho).mp ht a ha
    by_cases hlt : a < 42 + k
    · simpa [read, hlt] using before_first_and hc hk hfirst a hlt (by simpa [read, hlt] using hr)
    · simp [read, hlt] at hr
  have hpair : ∃ i ∈ base, ∃ j ∈ base, ∀ y : Input, y i = true → y j = true →
      ∀ a ∈ g.inputs, read C y k a = true := by
    have hzero : (0 : Fin 42) ∈ base := by decide
    rcases inputs_cases _ (gate_mono hc hg').2 with he | ⟨a, he⟩ | ⟨a, b, he⟩
    · exact ⟨0, hzero, 0, hzero, by simp [he]⟩
    · obtain ⟨i, hi, hp⟩ := hread a (by simp [he])
      refine ⟨i, hi, i, hi, fun y hy _ c hmem => ?_⟩
      have heq : c = a := by simpa [he] using hmem
      exact heq.symm ▸ hp y hy
    · obtain ⟨i, hi, hp⟩ := hread a (by simp [he])
      obtain ⟨j, hj, hq⟩ := hread b (by simp [he])
      refine ⟨i, hi, j, hj, fun y hy hz c hmem => ?_⟩
      simp only [he, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      · exact hp y hy
      · exact hq y hz
  obtain ⟨i, hi, j, hj, hp⟩ := hpair
  obtain ⟨m, hm, hmi, hmj⟩ := pair_mask hi hj
  exact ⟨m, hm, k, g, hg', ho, (and_sem C _ hg' ho).mpr (hp _ hmi hmj)⟩


def flip (y : Input) (u : Fin 42) : Input := fun i => y i || decide (i = u)

def support (U : Finset (Fin 42)) (f : Fin 42 → Bool) : Finset (Fin 42) :=
  U.filter fun u => f u = true

def covered (M S : Finset (Fin 42)) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, v < u → u ∈ M

lemma covered_of_subset {M S T : Finset (Fin 42)} (h : S ⊆ T) (ht : covered M T) :
    covered M S := fun u hu v hv hlt => ht u (h hu) v (h hv) hlt

-- Joining two nonempty supports accounts for the larger of their two minima.
noncomputable def joinMark (S T : Finset (Fin 42)) : Fin 42 :=
  if hs : S.Nonempty then
    if ht : T.Nonempty then max (S.min' hs) (T.min' ht) else 0
  else 0

lemma covered_cross {M S T : Finset (Fin 42)} (hs : covered M S)
    {u v : Fin 42} (hu : u ∈ S) (hv : v ∈ T) (hlt : v < u) :
    u ∈ M ∨ joinMark S T = u ∧ joinMark T S = u := by
  have hS : S.Nonempty := ⟨u, hu⟩
  have hT : T.Nonempty := ⟨v, hv⟩
  have hminS := S.min'_le u hu
  have hminT := (T.min'_le v hv).trans hlt.le
  rcases hminS.lt_or_eq with hltS | he
  · exact Or.inl (hs u hu _ (S.min'_mem hS) hltS)
  · exact Or.inr ⟨by simp [joinMark, hS, hT, he, max_eq_left hminT],
      by simp [joinMark, hS, hT, he, max_eq_right hminT]⟩

lemma covered_union {M S T : Finset (Fin 42)} (hs : covered M S)
    (ht : covered M T) (hj : joinMark S T ∈ M) : covered M (S ∪ T) := by
  intro u hu v hv hlt
  rcases Finset.mem_union.mp hu with hu | hu <;>
    rcases Finset.mem_union.mp hv with hv | hv
  · exact hs u hu v hv hlt
  · rcases covered_cross hs hu hv hlt with h | ⟨h, _⟩
    · exact h
    · exact h ▸ hj
  · rcases covered_cross ht hu hv hlt with h | ⟨_, h⟩
    · exact h
    · exact h ▸ hj
  · exact ht u hu v hv hlt

noncomputable def quietOr (C : Circuit) (y : Input) : Finset ℕ :=
  (Finset.range C.size).filter fun k =>
    (((C.gates[k]?).map (fun g =>
      GateOp.rec false true false (fun _ => false) false g.op)).getD false &&
      !wire C y (42 + k)) = true

lemma quietOr_mem {C : Circuit} {y : Input} {k : ℕ} {g : Gate}
    (hg : C.gates[k]? = some g) (ho : g.op = .or)
    (hq : wire C y (42 + k) = false) : k ∈ quietOr C y := by
  have hk := (List.getElem?_eq_some_iff.mp hg).choose
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr hk, ?_⟩
  rw [hg, Option.map_some, Option.getD_some, ho, hq]
  rfl

noncomputable def gateMark (C : Circuit) (y : Input) (U : Finset (Fin 42)) (k : ℕ) :
    Fin 42 :=
  match C.gates[k]? with
  | some g =>
    match g.inputs with
    | [a, b] => joinMark (support U (fun u => read C (flip y u) k a))
        (support U (fun u => read C (flip y u) k b))
    | _ => 0
  | none => 0

lemma quiet_or_bound {C : Circuit} (hc : Monotone2 C) (y : Input)
    (U : Finset (Fin 42)) (hne : U.Nonempty) (hquiet : C.eval (List.ofFn y) = false)
    (hflip : ∀ u ∈ U, C.eval (List.ofFn (flip y u)) = true) :
    U.card ≤ (quietOr C y).card + 1 := by
  classical
  let M := (quietOr C y).image (gateMark C y U)
  have invariant : ∀ w, wire C y w = false →
      covered M (support U (fun u => wire C (flip y u) w)) := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw
      by_cases hin : w < 42
      · let i : Fin 42 := ⟨w, hin⟩
        have hy : y i = false := (wire_input C y i).symm.trans hw
        have singleton : ∀ u ∈ support U (fun u => wire C (flip y u) w), i = u := by
          intro u hu
          have ht := (wire_input C (flip y u) i).symm.trans (Finset.mem_filter.mp hu).2
          simpa [flip, hy] using ht
        intro u hu v hv hlt
        rw [← singleton u hu, ← singleton v hv] at hlt
        exact (lt_irrefl _ hlt).elim
      · by_cases hb : w < 42 + C.gates.length
        · let k := w - 42
          have he : w = 42 + k := by dsimp [k]; omega
          have hk : k < C.gates.length := by omega
          let g := C.gates[k]
          have hg : C.gates[k]? = some g := List.getElem?_eq_getElem hk
          have hq : wire C y (42 + k) = false := he ▸ hw
          let S := fun a => support U (fun u => read C (flip y u) k a)
          have hprior : ∀ a, read C y k a = false → covered M (S a) := by
            intro a ha
            by_cases hlt : a < 42 + k
            · simpa only [S, read, ite_eq_left hlt] using ih a (by omega)
                (by simpa only [read, ite_eq_left hlt] using ha)
            · simp [S, support, read, hlt, covered]
          rw [he]
          rcases (gate_mono hc hg).1 with ha | ho
          · have hn : ¬ ∀ a ∈ g.inputs, read C y k a = true :=
              fun h => Bool.false_ne_true (hq.symm.trans ((and_sem C y hg ha).mpr h))
            push Not at hn
            obtain ⟨a, ham, haf⟩ := hn
            have haf' : read C y k a = false := by
              cases h : read C y k a <;> simp_all
            apply covered_of_subset _ (hprior a haf')
            intro u hu
            obtain ⟨hum, hut⟩ := Finset.mem_filter.mp hu
            exact Finset.mem_filter.mpr ⟨hum, (and_sem C (flip y u) hg ha).mp hut a ham⟩
          · have hfalse : ∀ a ∈ g.inputs, read C y k a = false := by
              intro a ham
              cases h : read C y k a
              · rfl
              · exact (Bool.false_ne_true (hq.symm.trans
                  ((or_sem C y hg ho).mpr ⟨a, ham, h⟩))).elim
            have hact : ∀ u ∈ support U (fun u => wire C (flip y u) (42+k)),
                ∃ a ∈ g.inputs, u ∈ S a := by
              intro u hu
              obtain ⟨hum, hut⟩ := Finset.mem_filter.mp hu
              obtain ⟨a, ham, hat⟩ := (or_sem C (flip y u) hg ho).mp hut
              exact ⟨a, ham, Finset.mem_filter.mpr ⟨hum, hat⟩⟩
            rcases inputs_cases _ (gate_mono hc hg).2 with hs | ⟨a, hs⟩ | ⟨a, b, hs⟩
            · intro u hu
              have h := hact u hu
              simp [hs] at h
            · apply covered_of_subset _ (hprior a (hfalse a (by simp [hs])))
              intro u hu
              simpa [hs] using hact u hu
            · have hmark : joinMark (S a) (S b) ∈ M := by
                apply Finset.mem_image.mpr
                exact ⟨k, quietOr_mem hg ho hq, by simp [gateMark, hg, hs, S]⟩
              apply covered_of_subset _ (covered_union (hprior a (hfalse a (by simp [hs])))
                (hprior b (hfalse b (by simp [hs]))) hmark)
              intro u hu
              obtain ⟨c, hc', hcS⟩ := hact u hu
              simp only [hs, List.mem_cons, List.not_mem_nil, or_false] at hc'
              rcases hc' with rfl | rfl
              · exact Finset.mem_union_left _ hcS
              · exact Finset.mem_union_right _ hcS
        · intro u hu
          have ht := (Finset.mem_filter.mp hu).2
          exact (Bool.false_ne_true ((wire_outside C (flip y u) (by omega : 42 + C.gates.length ≤ w)).symm.trans ht)).elim
  -- Every neighbor except the minimum has a smaller neighbor in the output support.
  have hsubset : U.erase (U.min' hne) ⊆ M := by
    intro u hu
    obtain ⟨hne', hum⟩ := Finset.mem_erase.mp hu
    have hlt := (U.min'_le u hum).lt_of_ne (Ne.symm hne')
    exact invariant C.output hquiet u (Finset.mem_filter.mpr ⟨hum, hflip u hum⟩)
      (U.min' hne) (Finset.mem_filter.mpr ⟨U.min'_mem hne, hflip _ (U.min'_mem hne)⟩) hlt
  have hcard := (Finset.card_le_card hsubset).trans (Finset.card_image_le (s := quietOr C y)
    (f := gateMark C y U))
  have hmin := Finset.card_erase_add_one (U.min'_mem hne)
  omega

abbrev adjacent (p l : Fin 42) : Prop :=
  p.val < 21 ∧ 21 ≤ l.val ∧ (l.val + 21 - p.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)

def hasEdge (y : Input) : Prop :=
  ∃ p l : Fin 42, adjacent p l ∧ y p = true ∧ y l = true

def vertices (y : Input) : List (Fin 42) := (List.finRange 42).filter y

lemma mem_vertices (y : Input) (i : Fin 42) : i ∈ vertices y ↔ y i = true := by
  simp [vertices, List.mem_finRange]

def edgeTest (y : Input) : Bool :=
  (vertices y).any fun p => (vertices y).any fun l => decide (adjacent p l)

lemma edgeTest_spec (y : Input) : edgeTest y = true ↔ hasEdge y := by
  simp only [edgeTest, hasEdge, List.any_eq_true, mem_vertices, decide_eq_true_eq]
  constructor
  · rintro ⟨p, hp, l, hl, hadj⟩
    exact ⟨p, l, hadj, hp, hl⟩
  · rintro ⟨p, l, hadj, hp, hl⟩
    exact ⟨p, hp, l, hl, hadj⟩

def neighbors (y : Input) : List (Fin 42) :=
  (List.finRange 42).filter fun u =>
    !y u && (vertices y).any fun v => decide (adjacent u v ∨ adjacent v u)

lemma neighbor_edge {y : Input} {u : Fin 42} (hu : u ∈ neighbors y) :
    hasEdge (flip y u) := by
  have h := (List.mem_filter.mp hu).2
  simp only [Bool.and_eq_true] at h
  obtain ⟨v, hv, ha⟩ := List.any_eq_true.mp h.2
  have hyv : y v = true := (mem_vertices y v).mp hv
  have hv' : flip y u v = true := by simp [flip, hyv]
  have hu' : flip y u u = true := by simp [flip]
  rcases of_decide_eq_true ha with hp | hp
  · exact ⟨u, v, hp, hu', hv'⟩
  · exact ⟨v, u, hp, hv', hu'⟩

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
lemma masks_check : masks.all (fun m =>
    !edgeTest (maskInput m) && decide ((neighbors (maskInput m)).length = 34)) = true := by
  decide

lemma mask_bound {C : Circuit} (hc : Monotone2 C)
    (hcorrect : ∀ y : Input, C.eval (List.ofFn y) = true ↔ hasEdge y)
    {m : ℕ} (hm : m ∈ masks) :
    33 ≤ (quietOr C (maskInput m)).card := by
  let y := maskInput m
  let U := (neighbors y).toFinset
  have h := List.all_eq_true.mp masks_check m hm
  simp only [Bool.and_eq_true] at h
  have hlen : (neighbors y).length = 34 := of_decide_eq_true h.2
  have hcard : U.card = 34 := by
    rw [List.toFinset_card_of_nodup, hlen]
    exact (List.nodup_finRange _).filter _
  have hne : U.Nonempty := Finset.card_pos.mp (by omega)
  have hf : C.eval (List.ofFn y) = false := by
    cases he : C.eval (List.ofFn y)
    · rfl
    · have ht := (edgeTest_spec y).mpr ((hcorrect y).mp he)
      have hn : (!edgeTest y) = true := h.1
      simp [ht] at hn
  have hg : ∀ u ∈ U, C.eval (List.ofFn (flip y u)) = true := by
    intro u hu
    exact (hcorrect _).mpr (neighbor_edge (List.mem_toFinset.mp hu))
  have hbound := quiet_or_bound hc y U hne hf hg
  change 33 ≤ (quietOr C y).card
  omega

end PEqualNP.Outside.L_meta_5875

open PEqualNP.Outside.L_meta_5875 in
theorem PEqualNP.Outside.L_meta_5875 :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     (∀ (x3 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (42 : ℕ)) (x5 : Fin (42 : ℕ)), (↑x4 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x5 ∧ (↑x5 + (21 : ℕ) - ↑x4) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) →       have x4 : List ℕ := [(693637218693 : ℕ), (214750724172 : ℕ), (43100670213 : ℕ), (2201724715076 : ℕ), (429513539622 : ℕ), (10838245382 : ℕ), (1718003696225 : ℕ), (1387274437386 : ℕ), (3436007392450 : ℕ), (214756769811 : ℕ), (412337856832 : ℕ), (3436108316976 : ℕ), (154640061441 : ℕ), (1168315262978 : ℕ)];       have x5 : ℕ → Fin (42 : ℕ) → Bool := fun (x5 : ℕ) (x6 : Fin (42 : ℕ)) => x5.testBit ↑x6;       have x6 : (Fin (42 : ℕ) → Bool) → Prop := fun (x6 : Fin (42 : ℕ) → Bool) => ∃ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x7]? = Option.some x8 ∧ x8.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x1.wires (List.ofFn x6)).getD ((42 : ℕ) + x7) Bool.false = Bool.true;       have x7 : ℕ → Finset ℕ := fun (x7 : ℕ) => {x8 ∈ Finset.range x1.size | ((Option.map (fun (x9 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.true Bool.false (fun (x10 : ℕ) => Bool.false) Bool.false x9.op) x1.gates[x8]?).getD Bool.false && !(x1.wires (List.ofFn (x5 x7))).getD ((42 : ℕ) + x8) Bool.false) = Bool.true};       (x6 fun (x8 : Fin (42 : ℕ)) => Decidable.decide (↑x8 ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (6 : ℕ), (8 : ℕ), (18 : ℕ), (24 : ℕ), (31 : ℕ), (33 : ℕ), (37 : ℕ)])) → (∃ x9 ∈ x4, x6 (x5 x9)) ∧ ∀ x9 ∈ x4, (33 : ℕ) ≤ (x7 x9).card := by
  intro C hc hcorrect
  change hit C baseInput → (∃ m ∈ masks, hit C (maskInput m)) ∧
    ∀ m ∈ masks, 33 ≤ (quietOr C (maskInput m)).card
  intro hh
  exact ⟨first_and_transfer hc hh, fun _ hm => mask_bound hc hcorrect hm⟩
