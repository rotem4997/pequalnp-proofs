import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8323

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def pgRel (u v : Fin 42) : Bool :=
  decide (u.val < 21 ∧ 21 ≤ v.val ∧
    (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ))

def adj (u v : Fin 42) : Bool :=
  pgRel u v || pgRel v u

def allEdges : Finset (Fin 42 × Fin 42) :=
  Finset.univ.filter fun e => pgRel e.1 e.2 = true

lemma pgRel_irrefl (u : Fin 42) : pgRel u u = false := by
  revert u; decide

lemma adj_symm (u v : Fin 42) : adj u v = adj v u := by
  simp [adj, Bool.or_comm]

lemma adj_irrefl (u : Fin 42) : adj u u = false := by
  simp [adj, pgRel_irrefl]

lemma diff_set_sidon :
    ∀ d1 ∈ ([0, 5, 7, 17, 20] : List ℕ),
    ∀ d2 ∈ ([0, 5, 7, 17, 20] : List ℕ),
    ∀ d3 ∈ ([0, 5, 7, 17, 20] : List ℕ),
    ∀ d4 ∈ ([0, 5, 7, 17, 20] : List ℕ),
    (d1 + d4) % 21 = (d2 + d3) % 21 → d1 = d2 ∨ d1 = d3 := by
  decide

lemma pgRel_c4_aux (p1 p2 l1 l2 : Fin 42) (hp : p1 ≠ p2) (hl : l1 ≠ l2)
    (h11 : pgRel p1 l1 = true) (h12 : pgRel p1 l2 = true)
    (h21 : pgRel p2 l1 = true) (h22 : pgRel p2 l2 = true) : False := by
  unfold pgRel at h11 h12 h21 h22
  simp only [decide_eq_true_eq] at h11 h12 h21 h22
  set d1 := (l1.val + 21 - p1.val) % 21
  set d2 := (l2.val + 21 - p1.val) % 21
  set d3 := (l1.val + 21 - p2.val) % 21
  set d4 := (l2.val + 21 - p2.val) % 21
  have hmod : (d1 + d4) % 21 = (d2 + d3) % 21 := by
    have h1 : (l1.val + 21 - p1.val) + (l2.val + 21 - p2.val) =
              (l2.val + 21 - p1.val) + (l1.val + 21 - p2.val) := by omega
    calc (d1 + d4) % 21
        = ((l1.val + 21 - p1.val) + (l2.val + 21 - p2.val)) % 21 := by
          rw [Nat.add_mod, Nat.mod_mod, Nat.mod_mod, ← Nat.add_mod]
      _ = ((l2.val + 21 - p1.val) + (l1.val + 21 - p2.val)) % 21 := by rw [h1]
      _ = (d2 + d3) % 21 := by rw [Nat.add_mod]
  have hsid := diff_set_sidon d1 h11.2.2 d2 h12.2.2 d3 h21.2.2 d4 h22.2.2 hmod
  rcases hsid with h12eq | h13eq
  · apply hl
    apply Fin.ext
    have hlt1 : l1.val < 42 := l1.isLt
    have hlt2 : l2.val < 42 := l2.isLt
    omega
  · apply hp
    apply Fin.ext
    omega

lemma pgRel_c4 : ∀ (a b c d : Fin 42), a ≠ b → c ≠ d →
    adj a c = true → adj a d = true → adj b c = true → adj b d = true → False := by
  intro a b c d hab hcd hac had hbc hbd
  unfold adj at hac had hbc hbd
  simp only [Bool.or_eq_true] at hac had hbc hbd
  have hlt : ∀ u v : Fin 42, pgRel u v = true → u.val < 21 ∧ 21 ≤ v.val := by
    intro u v h; unfold pgRel at h; simp only [decide_eq_true_eq] at h; exact ⟨h.1, h.2.1⟩
  rcases hac with hac | hca
  · have ha : a.val < 21 := (hlt a c hac).1
    have hc : 21 ≤ c.val := (hlt a c hac).2
    have had' : pgRel a d = true := had.resolve_right fun h => by have := (hlt d a h).2; omega
    have hd : 21 ≤ d.val := (hlt a d had').2
    have hbc' : pgRel b c = true := hbc.resolve_right fun h => by have := (hlt c b h).1; omega
    have hbd' : pgRel b d = true := hbd.resolve_right fun h => by have := (hlt d b h).1; omega
    exact pgRel_c4_aux a b c d hab hcd hac had' hbc' hbd'
  · have hc : c.val < 21 := (hlt c a hca).1
    have ha : 21 ≤ a.val := (hlt c a hca).2
    have hda' : pgRel d a = true := had.resolve_left fun h => by have := (hlt a d h).1; omega
    have hd : d.val < 21 := (hlt d a hda').1
    have hcb' : pgRel c b = true := hbc.resolve_left fun h => by have := (hlt b c h).2; omega
    have hdb' : pgRel d b = true := hbd.resolve_left fun h => by have := (hlt b d h).2; omega
    exact pgRel_c4_aux c d a b hcd hab hca hcb' hda' hdb'

lemma allEdges_card : allEdges.card = 105 := by
  let f : Fin 21 × Fin 5 → Fin 42 × Fin 42 := fun x =>
    let d : ℕ := ([0, 5, 7, 17, 20] : List ℕ)[x.2.val]'x.2.isLt
    (⟨x.1.val, by omega⟩, ⟨21 + (x.1.val + d) % 21, by omega⟩)
  have hcard : (Finset.univ : Finset (Fin 21 × Fin 5)).card = 105 := by decide
  rw [← hcard]
  symm
  refine Finset.card_bij (fun x _ => f x) ?_ ?_ ?_
  · intro x _
    simp only [allEdges, Finset.mem_filter, Finset.mem_univ, true_and, f, pgRel, decide_eq_true_eq]
    refine ⟨by omega, by omega, ?_⟩
    rcases x with ⟨p, idx⟩
    fin_cases idx <;> simp <;> try omega
  · intro x _ y _ hxy
    rcases x with ⟨p1, i1⟩
    rcases y with ⟨p2, i2⟩
    simp only [f, Prod.mk.injEq, Fin.mk.injEq] at hxy
    have hp : p1 = p2 := Fin.ext hxy.1
    subst hp
    have h2 : (p1.val + ([0, 5, 7, 17, 20] : List ℕ)[i1.val]'i1.isLt) % 21 =
              (p1.val + ([0, 5, 7, 17, 20] : List ℕ)[i2.val]'i2.isLt) % 21 := by
      omega
    have hi : i1 = i2 := by
      fin_cases i1 <;> fin_cases i2 <;> simp_all <;> try omega
    subst hi; rfl
  · intro e he
    simp only [allEdges, Finset.mem_filter, Finset.mem_univ, true_and, pgRel, decide_eq_true_eq] at he
    obtain ⟨h1, h2, h3⟩ := he
    set p : Fin 21 := ⟨e.1.val, h1⟩
    set d := (e.2.val + 21 - e.1.val) % 21
    have hl_eq : e.2.val = 21 + (e.1.val + d) % 21 := by
      have hlt2 : e.2.val < 42 := e.2.isLt
      omega
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h3
    rcases h3 with hd | hd | hd | hd | hd
    · refine ⟨(p, 0), Finset.mem_univ _, ?_⟩
      ext <;> simp [f, p, hl_eq, hd]
    · refine ⟨(p, 1), Finset.mem_univ _, ?_⟩
      ext <;> simp [f, p, hl_eq, hd]
    · refine ⟨(p, 2), Finset.mem_univ _, ?_⟩
      ext <;> simp [f, p, hl_eq, hd]
    · refine ⟨(p, 3), Finset.mem_univ _, ?_⟩
      ext <;> simp [f, p, hl_eq, hd]
    · refine ⟨(p, 4), Finset.mem_univ _, ?_⟩
      ext <;> simp [f, p, hl_eq, hd]

lemma adj_iff_pgRel (u v : Fin 42) :
    adj u v = true ↔ pgRel u v = true ∨ pgRel v u = true := by
  simp [adj]

def isOr (g : Gate) : Bool :=
  GateOp.casesOn g.op false true false (fun _ => false) false

lemma isOr_iff (g : Gate) : isOr g = true ↔ g.op = GateOp.or := by
  cases h : g.op <;> simp [isOr, h]

def orCount (C : Circuit) : ℕ :=
  C.gates.countP isOr

def computes (C : Circuit) : Prop :=
  ∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔
    ∃ u v : Fin 42, pgRel u v = true ∧ x u = true ∧ x v = true

def clean (C : Circuit) : Prop :=
  ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.and →
    ∀ x : Fin 42 → Bool, (C.wires (List.ofFn x)).getD (42 + j) false = true →
      C.eval (List.ofFn x) = true

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma wires_eq_run (C : Circuit) (x : List Bool) : C.wires x = run C.gates x := rfl

lemma run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih =>
    rw [run_snoc, List.length_append, List.length_singleton, ih, List.length_append, List.length_singleton]
    omega

lemma getD_append_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_append_eq (l : List Bool) (b : Bool) :
    (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_append_lt _ _ _ (by rw [run_length, List.length_append]; omega), ih]

lemma run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

lemma run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i =>
        if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_append_eq]
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)

def wval (C : Circuit) (x : Fin 42 → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wval_input (C : Circuit) (x : Fin 42 → Bool) (i : Fin 42) :
    wval C x i.val = x i := by
  unfold wval
  rw [wires_eq_run, run_input _ _ _ (by simp)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some]

lemma wval_gate (C : Circuit) (x : Fin 42 → Bool) (j : ℕ) (hj : j < C.gates.length) :
    wval C x (42 + j) =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i =>
        if i < 42 + j then wval C x i else false) := by
  unfold wval
  have := run_gate C.gates (List.ofFn x) j hj
  simpa [wires_eq_run] using this

lemma wval_oob (C : Circuit) (x : Fin 42 → Bool) (w : ℕ) (hw : 42 + C.gates.length ≤ w) :
    wval C x w = false := by
  unfold wval
  rw [wires_eq_run, List.getD_eq_default]
  rw [run_length]; simp; omega

lemma eval_eq_wval (C : Circuit) (x : Fin 42 → Bool) :
    C.eval (List.ofFn x) = wval C x C.output := rfl

lemma mono_wval (C : Circuit) (hM : Monotone2 C) {x y : Fin 42 → Bool}
    (hxy : ∀ i : Fin 42, x i = true → y i = true) :
    ∀ w : ℕ, wval C x w = true → wval C y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases h1 : w < 42
    · have hw' : wval C x (⟨w, h1⟩ : Fin 42).val = true := hw
      rw [wval_input] at hw'
      change wval C y (⟨w, h1⟩ : Fin 42).val = true
      rw [wval_input]
      exact hxy ⟨w, h1⟩ hw'
    · by_cases h2 : w < 42 + C.gates.length
      · set j := w - 42
        have hwj : w = 42 + j := by omega
        have hj : j < C.gates.length := by omega
        rw [hwj] at hw ⊢
        rw [wval_gate C x j hj] at hw
        rw [wval_gate C y j hj]
        have hop := (hM C.gates[j] (List.getElem_mem hj)).1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        rcases hop with hop | hop
        · rw [hop] at hw ⊢
          simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at hw ⊢
          intro i hi
          have hwi := hw i hi
          split_ifs at hwi ⊢ with hilt
          · exact ih i (by omega) hwi
        · rw [hop] at hw ⊢
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hw ⊢
          rcases hw with ⟨i, hi, hwi⟩
          refine ⟨i, hi, ?_⟩
          split_ifs at hwi ⊢ with hilt
          · exact ih i (by omega) hwi
      · rw [wval_oob C x w (by omega)] at hw
        cases hw

def singleIn (v : Fin 42) : Fin 42 → Bool :=
  fun i => decide (i = v)

def pairIn (u v : Fin 42) : Fin 42 → Bool :=
  fun i => decide (i = u ∨ i = v)

def supp (C : Circuit) (w : ℕ) : Finset (Fin 42) :=
  Finset.univ.filter fun v => wval C (singleIn v) w = true

lemma mem_supp (C : Circuit) (w : ℕ) (v : Fin 42) :
    v ∈ supp C w ↔ wval C (singleIn v) w = true := by
  simp [supp]

lemma supp_input (C : Circuit) (u : Fin 42) : supp C u.val = {u} := by
  ext v
  simp [mem_supp, wval_input, singleIn, eq_comm]

lemma supp_oob (C : Circuit) (w : ℕ) (hw : 42 + C.gates.length ≤ w) : supp C w = ∅ := by
  ext v
  simp [mem_supp, wval_oob C _ w hw]

lemma computes_single (C : Circuit) (hcomp : computes C) (v : Fin 42) :
    C.eval (List.ofFn (singleIn v)) = false := by
  cases h : C.eval (List.ofFn (singleIn v))
  · rfl
  · obtain ⟨a, b, hab, ha, hb⟩ := (hcomp (singleIn v)).mp h
    simp only [singleIn, decide_eq_true_eq] at ha hb
    subst ha; subst hb
    rw [pgRel_irrefl] at hab
    cases hab

lemma supp_and_empty (C : Circuit) (hcomp : computes C) (hcl : clean C)
    (j : ℕ) (hj : j < C.gates.length) (hand : C.gates[j].op = GateOp.and) :
    supp C (42 + j) = ∅ := by
  ext v
  simp only [mem_supp, Finset.notMem_empty, iff_false, Bool.not_eq_true]
  by_contra h
  simp only [Bool.not_eq_false] at h
  have h1 := hcl j C.gates[j] (List.getElem?_eq_getElem hj) hand (singleIn v) h
  rw [computes_single C hcomp v] at h1
  cases h1

lemma supp_output_empty (C : Circuit) (hcomp : computes C) : supp C C.output = ∅ := by
  ext v
  simp only [mem_supp, Finset.notMem_empty, iff_false, Bool.not_eq_true]
  exact computes_single C hcomp v

def effSupp (C : Circuit) (j i : ℕ) : Finset (Fin 42) :=
  if i < 42 + j then supp C i else ∅

lemma supp_or_gate (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (hor : C.gates[j].op = GateOp.or)
    (v : Fin 42) :
    v ∈ supp C (42 + j) ↔ ∃ i ∈ C.gates[j].inputs, v ∈ effSupp C j i := by
  rw [mem_supp, wval_gate C _ j hj, hor]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq, effSupp]
  constructor
  · rintro ⟨i, hi, h⟩
    refine ⟨i, hi, ?_⟩
    split_ifs at h ⊢ with hilt
    · exact (mem_supp C i v).mpr h
  · rintro ⟨i, hi, h⟩
    refine ⟨i, hi, ?_⟩
    split_ifs at h ⊢ with hilt
    · exact (mem_supp C i v).mp h
    · simp at h

lemma sound_of_supp_empty (C : Circuit) (hM : Monotone2 C) (hcl : clean C) :
    ∀ w : ℕ, supp C w = ∅ → ∀ x : Fin 42 → Bool, wval C x w = true → C.eval (List.ofFn x) = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hsem x hwx
    by_cases h1 : w < 42
    · exfalso
      have hmem : (⟨w, h1⟩ : Fin 42) ∈ supp C (⟨w, h1⟩ : Fin 42).val := by
        rw [supp_input]; simp
      change (⟨w, h1⟩ : Fin 42) ∈ supp C w at hmem
      rw [hsem] at hmem
      exact Finset.notMem_empty _ hmem
    · by_cases h2 : w < 42 + C.gates.length
      · set j := w - 42
        have hwj : w = 42 + j := by omega
        have hj : j < C.gates.length := by omega
        rw [hwj] at hsem hwx
        have hop := (hM C.gates[j] (List.getElem_mem hj)).1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        rcases hop with hop | hop
        · exact hcl j C.gates[j] (List.getElem?_eq_getElem hj) hop x hwx
        · rw [wval_gate C x j hj, hop] at hwx
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hwx
          rcases hwx with ⟨i, hi, hwi⟩
          split_ifs at hwi with hilt
          · have his : supp C i = ∅ := by
              ext v
              simp only [Finset.notMem_empty, iff_false]
              intro hv
              have hvj : v ∈ supp C (42 + j) :=
                (supp_or_gate C j hj hop v).mpr ⟨i, hi, by simp [effSupp, hilt, hv]⟩
              rw [hsem] at hvj
              exact Finset.notMem_empty _ hvj
            exact ih i (by omega) his x hwi
      · rw [wval_oob C x w (by omega)] at hwx
        cases hwx

def isMixedOr (C : Circuit) (j : ℕ) : Prop :=
  ∃ (hj : j < C.gates.length), C.gates[j].op = GateOp.or ∧
    (∃ a ∈ C.gates[j].inputs, effSupp C j a = ∅ ∧ a < 42 + j) ∧
    (∃ b ∈ C.gates[j].inputs, (effSupp C j b).Nonempty)

noncomputable def mixedOrCount (C : Circuit) : ℕ :=
  letI := Classical.propDecidable
  ((Finset.range C.gates.length).filter fun j => isMixedOr C j).card

def deadGate (m : ℕ) : Gate :=
  ⟨GateOp.and, [42 + m]⟩

def unmixOne (C : Circuit) (j a b : ℕ) : Circuit :=
  let m := C.gates.length
  let rep := fun w => if w = 42 + j then b else w
  let gs' := C.gates.mapIdx fun k g =>
    if k < j then g else if k = j then deadGate m else ⟨g.op, g.inputs.map rep⟩
  let out' := rep C.output
  { gates := gs' ++ [⟨GateOp.or, [out', a]⟩], output := 42 + m }

lemma unmixOne_length (C : Circuit) (j a b : ℕ) :
    (unmixOne C j a b).gates.length = C.gates.length + 1 := by
  simp [unmixOne]

lemma unmixOne_monotone2 (C : Circuit) (hM : Monotone2 C) (j a b : ℕ) :
    Monotone2 (unmixOne C j a b) := by
  intro g hg
  simp only [unmixOne, List.mem_append, List.mem_singleton] at hg
  rcases hg with hg | rfl
  · rw [List.mem_iff_getElem] at hg
    rcases hg with ⟨k, hk, rfl⟩
    simp only [List.length_mapIdx] at hk
    simp only [List.getElem_mapIdx]
    split_ifs
    · exact hM C.gates[k] (List.getElem_mem hk)
    · exact ⟨by simp [deadGate], by simp [deadGate]⟩
    · have hgk := hM C.gates[k] (List.getElem_mem hk)
      exact ⟨hgk.1, by simp [hgk.2]⟩
  · exact ⟨by simp, by simp⟩

lemma countP_mapIdx_replace {α : Type} (p : α → Bool) :
    ∀ (l : List α) (f : ℕ → α → α) (j : ℕ) (hj : j < l.length),
      (∀ k (hk : k < l.length), k ≠ j → p (f k l[k]) = p l[k]) →
      p l[j] = true → p (f j l[j]) = false →
      (l.mapIdx f).countP p + 1 = l.countP p := by
  intro l
  induction l with
  | nil => intro f j hj; simp at hj
  | cons x xs ih =>
    intro f j hj heq hbefore hafter
    simp only [List.mapIdx_cons, List.countP_cons]
    cases j with
    | zero =>
      simp only [List.getElem_cons_zero] at hbefore hafter
      have htail : (xs.mapIdx fun k y => f (k + 1) y).countP p = xs.countP p := by
        have hgen : ∀ (ys : List α) (g : ℕ → α → α),
            (∀ k (hk : k < ys.length), p (g k ys[k]) = p ys[k]) →
            (ys.mapIdx g).countP p = ys.countP p := by
          intro ys
          induction ys with
          | nil => intro _ _; simp
          | cons y ys' ihy =>
            intro g hg
            simp only [List.mapIdx_cons, List.countP_cons]
            have h0 := hg 0 (by simp)
            simp only [List.getElem_cons_zero] at h0
            rw [h0, ihy (fun k z => g (k + 1) z) (fun k hk => hg (k + 1) (by simp; omega))]
        exact hgen xs (fun k y => f (k + 1) y) (fun k hk => heq (k + 1) (by simp; omega) (by omega))
      rw [hbefore, hafter, htail]
      simp
    | succ j' =>
      simp only [List.getElem_cons_succ] at hbefore hafter
      have h0 : p (f 0 x) = p x := heq 0 (by simp) (by omega)
      have hrec := ih (fun k => f (k + 1)) j' (by simp at hj; omega)
        (fun k hk hne => heq (k + 1) (by simp; omega) (by omega)) hbefore hafter
      rw [h0]
      split_ifs <;> omega

lemma unmixOne_orCount (C : Circuit) (j a b : ℕ) (hj : j < C.gates.length)
    (hor : C.gates[j].op = GateOp.or) :
    orCount (unmixOne C j a b) = orCount C := by
  unfold orCount unmixOne
  rw [List.countP_append, List.countP_singleton]
  have htop : isOr ⟨GateOp.or, [if C.output = 42 + j then b else C.output, a]⟩ = true := rfl
  simp only [htop, ↓reduceIte]
  exact countP_mapIdx_replace isOr C.gates
    (fun k g => if k < j then g else if k = j then deadGate C.gates.length
      else ⟨g.op, g.inputs.map (fun w => if w = 42 + j then b else w)⟩)
    j hj
    (fun k _ hne => by split_ifs <;> simp [isOr])
    (by simp [isOr, hor])
    (by simp [deadGate, isOr])

lemma unmixOne_get (C : Circuit) (j a b k : ℕ) (hk : k < C.gates.length) :
    (unmixOne C j a b).gates[k]'(by rw [unmixOne_length]; omega) =
      if k < j then C.gates[k]
      else if k = j then deadGate C.gates.length
      else ⟨C.gates[k].op, C.gates[k].inputs.map fun w => if w = 42 + j then b else w⟩ := by
  unfold unmixOne
  rw [List.getElem_append_left (by simp [hk]), List.getElem_mapIdx]

lemma unmixOne_wval_props (C : Circuit) (hM : Monotone2 C) (j a b : ℕ)
    (hj : j < C.gates.length) (hor : C.gates[j].op = GateOp.or)
    (hinp : C.gates[j].inputs = [a, b] ∨ C.gates[j].inputs = [b, a])
    (ha : a < 42 + j) (hb : b < 42 + j) :
    let D := unmixOne C j a b
    (∀ x : Fin 42 → Bool, ∀ w < 42 + j, wval D x w = wval C x w) ∧
    (∀ x : Fin 42 → Bool, wval D x (42 + j) = false) ∧
    (∀ x : Fin 42 → Bool, ∀ w < 42 + C.gates.length, w ≠ 42 + j →
      (wval D x w = true → wval C x w = true) ∧
      (wval C x w = true → wval D x w = true ∨ wval C x a = true)) := by
  intro D
  have hDlen : D.gates.length = C.gates.length + 1 := unmixOne_length C j a b
  have hlt : ∀ x : Fin 42 → Bool, ∀ w < 42 + j, wval D x w = wval C x w := by
    intro x w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases h1 : w < 42
      · change wval D x (⟨w, h1⟩ : Fin 42).val = wval C x (⟨w, h1⟩ : Fin 42).val
        rw [wval_input, wval_input]
      · set k := w - 42
        have hwk : w = 42 + k := by omega
        have hk : k < C.gates.length := by omega
        have hkj : k < j := by omega
        rw [hwk, wval_gate D x k (by omega), wval_gate C x k hk, unmixOne_get C j a b k hk]
        simp only [hkj, ↓reduceIte]
        congr 1
        refine List.map_congr_left fun i _ => ?_
        split_ifs with hik
        · exact ih i (by omega) (by omega)
        · rfl
  have hdead : ∀ x : Fin 42 → Bool, wval D x (42 + j) = false := by
    intro x
    rw [wval_gate D x j (by omega), unmixOne_get C j a b j hj]
    simp only [lt_irrefl, ↓reduceIte, deadGate, List.map_cons, List.map_nil, GateOp.eval]
    have hnot : ¬(42 + C.gates.length < 42 + j) := by omega
    simp [hnot]
  have hmain : ∀ x : Fin 42 → Bool, ∀ w < 42 + C.gates.length, w ≠ 42 + j →
      (wval D x w = true → wval C x w = true) ∧
      (wval C x w = true → wval D x w = true ∨ wval C x a = true) := by
    intro x w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw hne
      by_cases hltj : w < 42 + j
      · rw [hlt x w hltj]
        exact ⟨id, Or.inl⟩
      · set k := w - 42
        have hwk : w = 42 + k := by omega
        have hk : k < C.gates.length := by omega
        have hkj_not_lt : ¬(k < j) := by omega
        have hkj_ne : k ≠ j := by omega
        have hrep_prop : ∀ i : ℕ,
            ((if (if i = 42 + j then b else i) < 42 + k then wval D x (if i = 42 + j then b else i) else false) = true →
             (if i < 42 + k then wval C x i else false) = true) ∧
            ((if i < 42 + k then wval C x i else false) = true →
             (if (if i = 42 + j then b else i) < 42 + k then wval D x (if i = 42 + j then b else i) else false) = true ∨
             wval C x a = true) := by
          intro i
          by_cases hij : i = 42 + j
          · subst hij
            simp only [↓reduceIte, show b < 42 + k by omega, show 42 + j < 42 + k by omega,
              hlt x b hb, wval_gate C x j hj, hor]
            rcases hinp with hinp | hinp <;> rw [hinp] <;>
              simp [GateOp.eval, ha, hb] <;> tauto
          · simp only [hij, ↓reduceIte]
            split_ifs with hik
            · exact ih i (by omega) (by omega) hij
            · simp
        rw [hwk, wval_gate D x k (by omega), wval_gate C x k hk, unmixOne_get C j a b k hk]
        simp only [hkj_not_lt, hkj_ne, ↓reduceIte, List.map_map]
        have hop := (hM C.gates[k] (List.getElem_mem hk)).1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        rcases hop with hop | hop
        · rw [hop]
          simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
          constructor
          · intro hDall i hi
            exact (hrep_prop i).1 (hDall i hi)
          · intro hCall
            by_cases hxa : wval C x a = true
            · exact Or.inr hxa
            · left
              intro i hi
              exact ((hrep_prop i).2 (hCall i hi)).resolve_right hxa
        · rw [hop]
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
          constructor
          · rintro ⟨i, hi, hDi⟩
            exact ⟨i, hi, (hrep_prop i).1 hDi⟩
          · rintro ⟨i, hi, hCi⟩
            rcases (hrep_prop i).2 hCi with hDi | hxa
            · exact Or.inl ⟨i, hi, hDi⟩
            · exact Or.inr hxa
  exact ⟨hlt, hdead, hmain⟩

lemma unmix_step (C : Circuit) (hM : Monotone2 C) (hcomp : computes C) (hcl : clean C)
    (hmix : 0 < mixedOrCount C) :
    ∃ D : Circuit, Monotone2 D ∧ computes D ∧ clean D ∧ orCount D = orCount C ∧
      mixedOrCount D < mixedOrCount C := by
  classical
  have hne : ((Finset.range C.gates.length).filter fun j => isMixedOr C j).Nonempty :=
    Finset.card_pos.mp hmix
  obtain ⟨j, hjmem⟩ := hne
  have hj : j < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hjmem).1
  obtain ⟨_, hor, ⟨a, ha_mem, ha_emp, ha_lt⟩, ⟨b, hb_mem, hb_ne⟩⟩ := (Finset.mem_filter.mp hjmem).2
  have hb_lt : b < 42 + j := by
    by_contra hge
    simp [effSupp, hge] at hb_ne
  have hab_ne : a ≠ b := by
    intro heq; subst heq; simp [ha_emp] at hb_ne
  have hlen2 : C.gates[j].inputs.length ≤ 2 := (hM C.gates[j] (List.getElem_mem hj)).2
  have hinp : C.gates[j].inputs = [a, b] ∨ C.gates[j].inputs = [b, a] := by
    generalize hl : C.gates[j].inputs = l at ha_mem hb_mem hlen2
    rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, t⟩⟩⟩
    · simp at ha_mem
    · simp at ha_mem hb_mem; exact absurd (ha_mem.trans hb_mem.symm) hab_ne
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha_mem hb_mem
      rcases ha_mem with rfl | rfl <;> rcases hb_mem with rfl | rfl
      · exact absurd rfl hab_ne
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd rfl hab_ne
    · simp at hlen2
  have ha_supp : supp C a = ∅ := by
    simpa [effSupp, ha_lt] using ha_emp
  have ha_sound : ∀ x, wval C x a = true → C.eval (List.ofFn x) = true :=
    sound_of_supp_empty C hM hcl a ha_supp
  have hout_ne : C.output ≠ 42 + j := by
    intro heq
    obtain ⟨v, hv⟩ := hb_ne
    have hvj : v ∈ supp C (42 + j) := (supp_or_gate C j hj hor v).mpr ⟨b, hb_mem, hv⟩
    rw [← heq, supp_output_empty C hcomp] at hvj
    exact Finset.notMem_empty _ hvj
  let D := unmixOne C j a b
  have hDlen : D.gates.length = C.gates.length + 1 := unmixOne_length C j a b
  obtain ⟨hlt, hdead, hmain⟩ := unmixOne_wval_props C hM j a b hj hor hinp ha_lt hb_lt
  have hDtop : ∀ x : Fin 42 → Bool,
      D.eval (List.ofFn x) =
        ((if C.output < 42 + C.gates.length then wval D x C.output else false) || wval C x a) := by
    intro x
    rw [eval_eq_wval]
    change wval D x (42 + C.gates.length) = _
    rw [wval_gate D x C.gates.length (by omega)]
    have hlast : D.gates[C.gates.length]'(by omega) = ⟨GateOp.or, [C.output, a]⟩ := by
      simp [D, unmixOne, hout_ne]
    rw [hlast]
    simp only [List.map_cons, List.map_nil, GateOp.eval,
      List.any_cons, List.any_nil, Bool.or_false, id_eq, show a < 42 + C.gates.length by omega,
      ↓reduceIte]
    rw [show wval D x a = wval C x a from hlt x a ha_lt]
  have hDeval : ∀ x : Fin 42 → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
    intro x
    rw [hDtop x]
    by_cases hout_lt : C.output < 42 + C.gates.length
    · simp only [hout_lt, ↓reduceIte]
      have ⟨h1, h2⟩ := hmain x C.output hout_lt hout_ne
      cases hCx : C.eval (List.ofFn x)
      · rw [Bool.or_eq_false_iff]
        constructor
        · cases hDx : wval D x C.output
          · rfl
          · have := h1 hDx; rw [← eval_eq_wval, hCx] at this; cases this
        · cases hax : wval C x a
          · rfl
          · have := ha_sound x hax; rw [hCx] at this; cases this
      · rw [Bool.or_eq_true]
        exact h2 hCx
    · simp only [hout_lt, ↓reduceIte, Bool.false_or]
      have hCx : C.eval (List.ofFn x) = false := by
        rw [eval_eq_wval, wval_oob C x C.output (by omega)]
      rw [hCx]
      cases hax : wval C x a
      · rfl
      · have := ha_sound x hax; rw [hCx] at this; cases this
  have hDcomp : computes D := by
    intro x; rw [hDeval x]; exact hcomp x
  have hDcl : clean D := by
    intro k g hk hop x hwx
    rw [hDeval x]
    have hk_lt : k < D.gates.length := by
      by_contra hge
      rw [List.getElem?_eq_none (by omega)] at hk; cases hk
    have hgk : D.gates[k] = g := by
      rw [List.getElem?_eq_getElem hk_lt] at hk; exact Option.some.inj hk
    by_cases hkl : k < C.gates.length
    · by_cases hkj : k = j
      · subst hkj
        change wval D x (42 + k) = true at hwx
        rw [hdead x] at hwx; cases hwx
      · have hCgk : C.gates[k].op = GateOp.and := by
          have hg' := unmixOne_get C j a b k hkl
          change D.gates[k] = _ at hg'
          rw [hgk] at hg'
          by_cases hlt' : k < j
          · simp only [hlt', ↓reduceIte] at hg'; rw [← hop, hg']
          · simp only [hlt', hkj, ↓reduceIte] at hg'; rw [← hop, hg']
        have hCx := (hmain x (42 + k) (by omega) (by omega)).1 hwx
        exact hcl k C.gates[k] (List.getElem?_eq_getElem hkl) hCgk x hCx
    · have hkeq : k = C.gates.length := by omega
      subst hkeq
      have hlast : D.gates[C.gates.length] = ⟨GateOp.or, [C.output, a]⟩ := by simp [D, unmixOne, hout_ne]
      rw [hgk] at hlast
      rw [hlast] at hop; cases hop
  have hDsupp : ∀ w < 42 + C.gates.length, w ≠ 42 + j → supp D w = supp C w := by
    intro w hw hne'
    ext v
    simp only [mem_supp]
    have hva : wval C (singleIn v) a = false := by
      by_contra h
      simp only [Bool.not_eq_false] at h
      have hv : v ∈ supp C a := (mem_supp C a v).mpr h
      rw [ha_supp] at hv; exact Finset.notMem_empty _ hv
    have ⟨h1, h2⟩ := hmain (singleIn v) w hw hne'
    constructor
    · exact h1
    · intro hCv
      rcases h2 hCv with hDv | hCa
      · exact hDv
      · rw [hva] at hCa; cases hCa
  have hDmix : mixedOrCount D < mixedOrCount C := by
    unfold mixedOrCount
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    constructor
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
      obtain ⟨hk_lt, hk_mix⟩ := hk
      obtain ⟨_, hkor, ⟨p, hp_mem, hp_emp, hp_lt⟩, ⟨q, hq_mem, hq_ne⟩⟩ := hk_mix
      by_cases hkl : k < C.gates.length
      · have hDg := unmixOne_get C j a b k hkl
        change D.gates[k] = _ at hDg
        by_cases hkj_lt : k < j
        · simp only [hkj_lt, ↓reduceIte] at hDg
          refine ⟨hkl, hkl, ?_, ?_, ?_⟩
          · rw [hDg] at hkor; exact hkor
          · rw [hDg] at hp_mem
            have hsp : supp D p = supp C p := hDsupp p (by omega) (by omega)
            exact ⟨p, hp_mem, by simpa [effSupp, hp_lt, hsp] using hp_emp, hp_lt⟩
          · rw [hDg] at hq_mem
            have hq_lt : q < 42 + k := by by_contra hge; simp [effSupp, hge] at hq_ne
            have hsq : supp D q = supp C q := hDsupp q (by omega) (by omega)
            exact ⟨q, hq_mem, by simpa [effSupp, hq_lt, hsq] using hq_ne⟩
        · have hkj : k ≠ j := by
            intro hkj; subst hkj
            simp only [hkj_lt, ↓reduceIte] at hDg
            rw [hDg] at hkor; cases hkor
          have hjk_lt : j < k := by omega
          simp only [hkj_lt, hkj, ↓reduceIte] at hDg
          refine ⟨hkl, hkl, ?_, ?_, ?_⟩
          · rw [hDg] at hkor; exact hkor
          · rw [hDg] at hp_mem
            obtain ⟨p0, hp0_mem, hp0_eq⟩ := List.mem_map.mp hp_mem
            have hp0_ne : p0 ≠ 42 + j := by
              intro heq; subst heq
              simp only [↓reduceIte] at hp0_eq
              subst hp0_eq
              have hsb : supp D b = supp C b := hDsupp b (by omega) (by omega)
              simp only [effSupp, hp_lt, ↓reduceIte, hsb] at hp_emp
              simp only [effSupp, hb_lt, ↓reduceIte, hp_emp] at hb_ne
              exact Finset.not_nonempty_empty hb_ne
            simp only [hp0_ne, ↓reduceIte] at hp0_eq
            subst hp0_eq
            refine ⟨p0, hp0_mem, ?_, hp_lt⟩
            have hsp : supp D p0 = supp C p0 := hDsupp p0 (by omega) hp0_ne
            simpa [effSupp, hp_lt, hsp] using hp_emp
          · rw [hDg] at hq_mem
            obtain ⟨q0, hq0_mem, hq0_eq⟩ := List.mem_map.mp hq_mem
            have hq_lt : q < 42 + k := by
              by_contra hge; simp [effSupp, hge] at hq_ne
            by_cases hq0_eqj : q0 = 42 + j
            · subst hq0_eqj
              refine ⟨42 + j, hq0_mem, ?_⟩
              obtain ⟨v, hv⟩ := hb_ne
              refine ⟨v, ?_⟩
              simp only [effSupp, show 42 + j < 42 + k by omega, ↓reduceIte]
              exact (supp_or_gate C j hj hor v).mpr ⟨b, hb_mem, hv⟩
            · simp only [hq0_eqj, ↓reduceIte] at hq0_eq
              subst hq0_eq
              refine ⟨q0, hq0_mem, ?_⟩
              have hsq : supp D q0 = supp C q0 := hDsupp q0 (by omega) hq0_eqj
              simpa [effSupp, hq_lt, hsq] using hq_ne
      · exfalso
        have hkeq : k = C.gates.length := by omega
        subst hkeq
        have hlast : D.gates[C.gates.length] = ⟨GateOp.or, [C.output, a]⟩ := by
          simp [D, unmixOne, hout_ne]
        rw [hlast] at hq_mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq_mem
        rcases hq_mem with hqeq | hqeq
        · rw [hqeq] at hq_ne
          by_cases ho : C.output < 42 + C.gates.length
          · have hso : supp D C.output = supp C C.output := hDsupp C.output ho hout_ne
            simp [effSupp, ho, hso, supp_output_empty C hcomp] at hq_ne
          · simp [effSupp, ho] at hq_ne
        · rw [hqeq] at hq_ne
          have hsa : supp D a = supp C a := hDsupp a (by omega) (by omega)
          simp [effSupp, show a < 42 + C.gates.length by omega, hsa, ha_supp] at hq_ne
    · intro heq
      have hj_in : j ∈ (Finset.range D.gates.length).filter fun k => isMixedOr D k := by
        rw [heq]; exact hjmem
      obtain ⟨_, hjor, _, _⟩ := (Finset.mem_filter.mp hj_in).2
      have hDgj := unmixOne_get C j a b j hj
      change D.gates[j]'(by omega) = _ at hDgj
      simp only [lt_irrefl, ↓reduceIte] at hDgj
      rw [hDgj] at hjor; cases hjor
  exact ⟨D, unmixOne_monotone2 C hM j a b, hDcomp, hDcl, unmixOne_orCount C j a b hj hor, hDmix⟩

lemma exists_unmixed (C : Circuit) (hM : Monotone2 C) (hcomp : computes C) (hcl : clean C) :
    ∃ D : Circuit, Monotone2 D ∧ computes D ∧ clean D ∧ orCount D = orCount C ∧
      mixedOrCount D = 0 := by
  suffices ∀ n (C : Circuit), mixedOrCount C = n → Monotone2 C → computes C → clean C →
      ∃ D : Circuit, Monotone2 D ∧ computes D ∧ clean D ∧ orCount D = orCount C ∧
        mixedOrCount D = 0 from this (mixedOrCount C) C rfl hM hcomp hcl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro C hn hM hcomp hcl
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact ⟨C, hM, hcomp, hcl, rfl, hn⟩
    · obtain ⟨D, hDM, hDcomp, hDcl, hDor, hDlt⟩ := unmix_step C hM hcomp hcl (hn ▸ hpos)
      obtain ⟨E, hEM, hEcomp, hEcl, hEor, hE0⟩ := ih (mixedOrCount D) (hn ▸ hDlt) D rfl hDM hDcomp hDcl
      exact ⟨E, hEM, hEcomp, hEcl, hEor.trans hDor, hE0⟩

lemma unmixed_pure_supp (C : Circuit) (hM : Monotone2 C) (hcomp : computes C) (hcl : clean C)
    (h0 : mixedOrCount C = 0) :
    ∀ w : ℕ, (supp C w).Nonempty →
      ∀ x : Fin 42 → Bool, wval C x w = decide (∃ v ∈ supp C w, x v = true) := by
  classical
  have hnomix : ∀ j < C.gates.length, ¬ isMixedOr C j := by
    intro j hj hm
    have hmem : j ∈ (Finset.range C.gates.length).filter fun k => isMixedOr C k :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hm⟩
    have hpos : 0 < mixedOrCount C := Finset.card_pos.mpr ⟨j, hmem⟩
    omega
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hne x
    by_cases h1 : w < 42
    · change wval C x (⟨w, h1⟩ : Fin 42).val = decide (∃ v ∈ supp C (⟨w, h1⟩ : Fin 42).val, x v = true)
      rw [wval_input, supp_input]
      simp
    · by_cases h2 : w < 42 + C.gates.length
      · set j := w - 42
        have hwj : w = 42 + j := by omega
        have hj : j < C.gates.length := by omega
        rw [hwj] at hne ⊢
        have hop := (hM C.gates[j] (List.getElem_mem hj)).1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        rcases hop with hop | hop
        · rw [supp_and_empty C hcomp hcl j hj hop] at hne
          exact absurd hne Finset.not_nonempty_empty
        · have hall : ∀ i ∈ C.gates[j].inputs, i < 42 + j → (supp C i).Nonempty := by
            intro i hi hilt
            by_contra hemp
            rw [Finset.not_nonempty_iff_eq_empty] at hemp
            obtain ⟨v, hv⟩ := hne
            obtain ⟨b, hb_mem, hbv⟩ := (supp_or_gate C j hj hop v).mp hv
            exact hnomix j hj ⟨hj, hop, ⟨i, hi, by simp [effSupp, hilt, hemp], hilt⟩, ⟨b, hb_mem, ⟨v, hbv⟩⟩⟩
          rw [wval_gate C x j hj, hop]
          simp only [GateOp.eval, List.any_map]
          apply Bool.eq_iff_iff.mpr
          rw [List.any_eq_true, decide_eq_true_iff]
          constructor
          · rintro ⟨i, hi, hwi⟩
            simp only [Function.comp_apply, id_eq] at hwi
            split_ifs at hwi with hilt
            · rw [ih i (by omega) (hall i hi hilt) x, decide_eq_true_iff] at hwi
              rcases hwi with ⟨v, hv, hxv⟩
              exact ⟨v, (supp_or_gate C j hj hop v).mpr ⟨i, hi, by simp [effSupp, hilt, hv]⟩, hxv⟩
          · rintro ⟨v, hv, hxv⟩
            obtain ⟨i, hi, hvi⟩ := (supp_or_gate C j hj hop v).mp hv
            have hilt : i < 42 + j := by
              by_contra hge; simp [effSupp, hge] at hvi
            have hvi' : v ∈ supp C i := by simpa [effSupp, hilt] using hvi
            refine ⟨i, hi, ?_⟩
            simp only [Function.comp_apply, id_eq, hilt, ↓reduceIte]
            rw [ih i (by omega) (hall i hi hilt) x, decide_eq_true_iff]
            exact ⟨v, hvi', hxv⟩
      · rw [supp_oob C w (by omega)] at hne
        exact absurd hne Finset.not_nonempty_empty

lemma clean_and_biclique (C : Circuit) (hM : Monotone2 C) (hcomp : computes C) (hcl : clean C)
    (j : ℕ) (hj : j < C.gates.length) (hand : C.gates[j].op = GateOp.and)
    (a b : ℕ) (hinp : C.gates[j].inputs = [a, b]) (ha : a < 42 + j) (hb : b < 42 + j) :
    ∀ u ∈ supp C a, ∀ v ∈ supp C b, adj u v = true := by
  intro u hu v hv
  have h1 : wval C (pairIn u v) a = true :=
    mono_wval C hM (fun i hi => by simp [singleIn, pairIn] at hi ⊢; left; exact hi) a ((mem_supp C a u).mp hu)
  have h2 : wval C (pairIn u v) b = true :=
    mono_wval C hM (fun i hi => by simp [singleIn, pairIn] at hi ⊢; right; exact hi) b ((mem_supp C b v).mp hv)
  have h3 : wval C (pairIn u v) (42 + j) = true := by
    rw [wval_gate C _ j hj, hand, hinp]
    simp [GateOp.eval, ha, hb, h1, h2]
  have h4 := hcl j C.gates[j] (List.getElem?_eq_getElem hj) hand (pairIn u v) h3
  obtain ⟨p, l, hpl, hp, hl⟩ := (hcomp (pairIn u v)).mp h4
  simp only [pairIn, decide_eq_true_eq] at hp hl
  rcases hp with rfl | rfl <;> rcases hl with rfl | rfl
  · rw [pgRel_irrefl] at hpl; cases hpl
  · exact (adj_iff_pgRel _ _).mpr (Or.inl hpl)
  · exact (adj_iff_pgRel _ _).mpr (Or.inr hpl)
  · rw [pgRel_irrefl] at hpl; cases hpl

lemma biclique_star (A B : Finset (Fin 42)) (h : ∀ u ∈ A, ∀ v ∈ B, adj u v = true) :
    A.card ≤ 1 ∨ B.card ≤ 1 := by
  by_contra hnot
  push Not at hnot
  obtain ⟨u1, hu1, u2, hu2, hune⟩ := Finset.one_lt_card.mp hnot.1
  obtain ⟨v1, hv1, v2, hv2, hvne⟩ := Finset.one_lt_card.mp hnot.2
  exact pgRel_c4 u1 u2 v1 v2 hune hvne (h u1 hu1 v1 hv1) (h u1 hu1 v2 hv2)
    (h u2 hu2 v1 hv1) (h u2 hu2 v2 hv2)

lemma color_merge_step {α : Type} [DecidableEq α] (U : Finset α) (f : α → ℕ)
    (A B : Finset α) (c1 c2 : ℕ)
    (hA : ∀ x ∈ A, f x = c1) (hB : ∀ x ∈ B, f x = c2) :
    let f' : α → ℕ := fun x => if f x = c2 then c1 else f x
    (∀ x ∈ A ∪ B, f' x = c1) ∧
    (∀ S : Finset α, (∃ c, ∀ x ∈ S, f x = c) → ∃ c, ∀ x ∈ S, f' x = c) ∧
    (U.image f).card ≤ (U.image f').card + 1 := by
  intro f'
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with hxA | hxB
    · simp only [f', hA x hxA]; split_ifs <;> rfl
    · simp only [f', hB x hxB, ↓reduceIte]
  · rintro S ⟨c, hc⟩
    refine ⟨if c = c2 then c1 else c, fun x hx => ?_⟩
    simp only [f', hc x hx]
  · have hsub : U.image f ⊆ insert c2 (U.image f') := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      by_cases hfx : f x = c2
      · rw [hfx]; exact Finset.mem_insert_self c2 _
      · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨x, hx, by simp [f', hfx]⟩)
    exact (Finset.card_le_card hsub).trans (Finset.card_insert_le c2 _)

def soundLeaves (C : Circuit) (w : ℕ) : Finset ℕ :=
  if h1 : w < 42 then ∅
  else if h2 : w < 42 + C.gates.length then
    let j := w - 42
    let g := C.gates[j]'(by omega)
    if isOr g = true then
      g.inputs.foldl (fun acc i =>
        if hi : i < 42 + j then acc ∪ soundLeaves C i else acc) ∅
    else
      match g.inputs with
      | [] => ∅
      | [a] => if ha : a < 42 + j then soundLeaves C a else ∅
      | a :: b :: _ =>
        if ha : a < 42 + j then
          if hb : b < 42 + j then
            if supp C a = ∅ then soundLeaves C a
            else if supp C b = ∅ then soundLeaves C b
            else {j}
          else ∅
        else ∅
  else ∅
termination_by w
decreasing_by all_goals omega

lemma soundLeaves_lt (C : Circuit) (hM : Monotone2 C) (w : ℕ) (j : ℕ)
    (hj : j ∈ soundLeaves C w) :
    ∃ (hjlt : j < C.gates.length), C.gates[j].op = GateOp.and ∧
    ∃ a b, C.gates[j].inputs = [a, b] ∧ a < 42 + j ∧ b < 42 + j ∧
      (supp C a).Nonempty ∧ (supp C b).Nonempty := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rw [soundLeaves] at hj
    split_ifs at hj with h1 h2
    · exact absurd hj (Finset.notMem_empty _)
    · set k := w - 42
      have hk : k < C.gates.length := by omega
      dsimp only at hj
      split_ifs at hj with hor
      · have hfold : ∀ (l : List ℕ) (acc : Finset ℕ),
            j ∈ l.foldl (fun acc i => if hi : i < 42 + k then acc ∪ soundLeaves C i else acc) acc →
            j ∈ acc ∨ ∃ i ∈ l, ∃ hi : i < 42 + k, j ∈ soundLeaves C i := by
          intro l
          induction l with
          | nil => intro acc h; exact Or.inl h
          | cons i t iht =>
            intro acc h
            simp only [List.foldl_cons] at h
            rcases iht _ h with h1 | ⟨i', hi', hi'lt, h2⟩
            · split_ifs at h1 with hilt
              · rcases Finset.mem_union.mp h1 with ha | hb
                · exact Or.inl ha
                · exact Or.inr ⟨i, List.mem_cons_self, hilt, hb⟩
              · exact Or.inl h1
            · exact Or.inr ⟨i', List.mem_cons_of_mem _ hi', hi'lt, h2⟩
        rcases hfold _ ∅ hj with hemp | ⟨i, _, hilt, hji⟩
        · exact absurd hemp (Finset.notMem_empty _)
        · exact ih i (by omega) hji
      · have hhand : C.gates[k].op = GateOp.and := by
          have hop := (hM C.gates[k] (List.getElem_mem hk)).1
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
          exact hop.resolve_right (fun h => hor ((isOr_iff _).mpr h))
        have hlen2 : C.gates[k].inputs.length ≤ 2 := (hM C.gates[k] (List.getElem_mem hk)).2
        generalize hl : C.gates[k].inputs = l at hj hlen2
        rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
        · exact absurd hj (Finset.notMem_empty _)
        · dsimp only at hj
          split_ifs at hj with ha
          · exact ih a (by omega) hj
          · exact absurd hj (Finset.notMem_empty _)
        · dsimp only at hj
          split_ifs at hj with ha hb hsa hsb
          · exact ih a (by omega) hj
          · exact ih b (by omega) hj
          · rw [Finset.mem_singleton.mp hj]
            exact ⟨hk, hhand, a, b, hl, ha, hb,
              Finset.nonempty_iff_ne_empty.mpr hsa, Finset.nonempty_iff_ne_empty.mpr hsb⟩
          · exact absurd hj (Finset.notMem_empty _)
          · exact absurd hj (Finset.notMem_empty _)
        · simp at hlen2
    · exact absurd hj (Finset.notMem_empty _)

lemma soundLeaves_covers (C : Circuit) (hM : Monotone2 C) (hcomp : computes C) (hcl : clean C)
    (h0 : mixedOrCount C = 0) :
    ∀ w : ℕ, supp C w = ∅ → ∀ e : Fin 42 × Fin 42, pgRel e.1 e.2 = true →
      wval C (pairIn e.1 e.2) w = true →
      ∃ j ∈ soundLeaves C w, wval C (pairIn e.1 e.2) (42 + j) = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hsem e he hwe
    by_cases h1 : w < 42
    · exfalso
      have hm : (⟨w, h1⟩ : Fin 42) ∈ supp C (⟨w, h1⟩ : Fin 42).val := by
        rw [supp_input]; simp
      change (⟨w, h1⟩ : Fin 42) ∈ supp C w at hm
      rw [hsem] at hm; exact Finset.notMem_empty _ hm
    · by_cases h2 : w < 42 + C.gates.length
      · set k := w - 42
        have hwk : w = 42 + k := by omega
        have hk : k < C.gates.length := by omega
        rw [hwk] at hsem hwe ⊢
        rw [soundLeaves]
        simp only [show ¬(42 + k < 42) by omega, show 42 + k < 42 + C.gates.length by omega,
          ↓reduceDIte, show 42 + k - 42 = k by omega]
        rw [wval_gate C _ k hk] at hwe
        have hop := (hM C.gates[k] (List.getElem_mem hk)).1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        rcases hop with hop | hop
        · have hnotor : ¬(isOr C.gates[k] = true) := by rw [isOr_iff, hop]; intro h; cases h
          simp only [hnotor, ↓reduceIte]
          rw [hop] at hwe
          have hlen2 : C.gates[k].inputs.length ≤ 2 := (hM C.gates[k] (List.getElem_mem hk)).2
          generalize hl : C.gates[k].inputs = l at hwe hlen2
          rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
          · exfalso
            have hallf : wval C (singleIn 0) (42 + k) = true := by
              rw [wval_gate C _ k hk, hop, hl]; rfl
            have h0m : (0 : Fin 42) ∈ supp C (42 + k) := (mem_supp C _ _).mpr hallf
            rw [hsem] at h0m; exact Finset.notMem_empty _ h0m
          · simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
              Bool.and_true, id_eq] at hwe
            split_ifs at hwe with ha
            · simp only [ha, ↓reduceDIte]
              have hsa : supp C a = ∅ := by
                ext v
                simp only [Finset.notMem_empty, iff_false]
                intro hv
                have hv' : wval C (singleIn v) (42 + k) = true := by
                  rw [wval_gate C _ k hk, hop, hl]
                  simp [GateOp.eval, ha, (mem_supp C a v).mp hv]
                have hvm : v ∈ supp C (42 + k) := (mem_supp C _ _).mpr hv'
                rw [hsem] at hvm; exact Finset.notMem_empty _ hvm
              exact ih a (by omega) hsa e he hwe
          · simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
              Bool.and_true, Bool.and_eq_true, id_eq] at hwe
            obtain ⟨hwa, hwb⟩ := hwe
            split_ifs at hwa with ha
            · split_ifs at hwb with hb
              · simp only [ha, hb, ↓reduceDIte]
                by_cases hsa : supp C a = ∅
                · simp only [hsa, ↓reduceIte]
                  exact ih a (by omega) hsa e he hwa
                · by_cases hsb : supp C b = ∅
                  · simp only [hsa, hsb, ↓reduceIte]
                    exact ih b (by omega) hsb e he hwb
                  · simp only [hsa, hsb, ↓reduceIte]
                    refine ⟨k, Finset.mem_singleton_self k, ?_⟩
                    rw [wval_gate C _ k hk, hop, hl]
                    simp [GateOp.eval, ha, hb, hwa, hwb]
          · simp at hlen2
        · have hisor : isOr C.gates[k] = true := (isOr_iff _).mpr hop
          simp only [hisor, ↓reduceIte]
          rw [hop] at hwe
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hwe
          rcases hwe with ⟨i, hi, hwi⟩
          split_ifs at hwi with hilt
          · have his : supp C i = ∅ := by
              ext v
              simp only [Finset.notMem_empty, iff_false]
              intro hv
              have hvj : v ∈ supp C (42 + k) :=
                (supp_or_gate C k hk hop v).mpr ⟨i, hi, by simp [effSupp, hilt, hv]⟩
              rw [hsem] at hvj; exact Finset.notMem_empty _ hvj
            obtain ⟨j, hjmem, hjval⟩ := ih i (by omega) his e he hwi
            have hfold_mem : ∀ (l : List ℕ) (acc : Finset ℕ),
                (j ∈ acc ∨ (∃ i' ∈ l, ∃ hi' : i' < 42 + k, j ∈ soundLeaves C i')) →
                j ∈ l.foldl (fun acc i => if hi : i < 42 + k then acc ∪ soundLeaves C i else acc) acc := by
              intro l
              induction l with
              | nil => intro acc h; rcases h with h | ⟨_, h, _⟩; exact h; cases h
              | cons x xs ihx =>
                intro acc h
                simp only [List.foldl_cons]
                apply ihx
                rcases h with h | ⟨i', hi', hi'lt, hji'⟩
                · left; split_ifs; exact Finset.mem_union_left _ h; exact h
                · rcases List.mem_cons.mp hi' with rfl | hxs
                  · left; simp only [hi'lt, ↓reduceDIte]; exact Finset.mem_union_right _ hji'
                  · right; exact ⟨i', hxs, hi'lt, hji'⟩
            exact ⟨j, hfold_mem _ ∅ (Or.inr ⟨i, hi, hilt, hjmem⟩), hjval⟩
      · rw [wval_oob C _ w (by omega)] at hwe
        cases hwe

lemma soundLeaves_card_le (C : Circuit) (hM : Monotone2 C) (hcomp : computes C)
    (T : Finset ℕ) (hT : T = soundLeaves C C.output) (hTne : T.Nonempty) :
    T.card ≤ ((Finset.range C.gates.length).filter fun j =>
      C.gates[j]?.map isOr = some true ∧ supp C (42 + j) = ∅).card + 1 := by
  classical
  let oss : Finset ℕ := (Finset.range C.gates.length).filter fun j =>
    C.gates[j]?.map isOr = some true ∧ supp C (42 + j) = ∅
  have hstep : ∀ k ≤ C.gates.length, ∃ f : ℕ → ℕ,
      (∀ w < 42 + k, supp C w = ∅ → ∃ c, ∀ x ∈ soundLeaves C w ∩ T, f x = c) ∧
      T.card ≤ (T.image f).card + (oss.filter (· < k)).card := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨id, ?_, by simp⟩
      intro w hw _
      have hemp : soundLeaves C w = ∅ := by
        rw [soundLeaves]; simp [hw]
      exact ⟨0, fun x hx => by simp [hemp] at hx⟩
    | succ k ih =>
      intro hk
      obtain ⟨f, hmono, hcard⟩ := ih (by omega)
      have hk_lt : k < C.gates.length := by omega
      have hoss_split : (oss.filter (· < k + 1)).card =
          (oss.filter (· < k)).card + if k ∈ oss then 1 else 0 := by
        have h1 : oss.filter (· < k + 1) =
            if k ∈ oss then insert k (oss.filter (· < k)) else oss.filter (· < k) := by
          ext x
          split_ifs with hkoss
          · simp only [Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨hx, hlt⟩; rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hlt) with h | rfl
              · exact Or.inr ⟨hx, h⟩
              · exact Or.inl rfl
            · rintro (rfl | ⟨hx, h⟩); exact ⟨hkoss, by omega⟩; exact ⟨hx, by omega⟩
          · simp only [Finset.mem_filter]
            constructor
            · rintro ⟨hx, hlt⟩; refine ⟨hx, ?_⟩
              have hne : x ≠ k := fun h => hkoss (h ▸ hx)
              omega
            · rintro ⟨hx, h⟩; exact ⟨hx, by omega⟩
        rw [h1]
        split_ifs with hkoss
        · rw [Finset.card_insert_of_notMem (by simp)]
        · omega
      by_cases hkoss : k ∈ oss
      · have hkor_b : isOr C.gates[k] = true := by
          have hm := (Finset.mem_filter.mp hkoss).2.1
          rw [List.getElem?_eq_getElem hk_lt] at hm
          simpa using hm
        have hkor : C.gates[k].op = GateOp.or := (isOr_iff _).mp hkor_b
        have hks : supp C (42 + k) = ∅ := (Finset.mem_filter.mp hkoss).2.2
        have hlen2 : C.gates[k].inputs.length ≤ 2 := (hM C.gates[k] (List.getElem_mem hk_lt)).2
        have hchild_mono : ∀ i ∈ C.gates[k].inputs, i < 42 + k →
            ∃ c, ∀ x ∈ soundLeaves C i ∩ T, f x = c := by
          intro i hi hilt
          have his : supp C i = ∅ := by
            ext v
            simp only [Finset.notMem_empty, iff_false]
            intro hv
            have hvj := (supp_or_gate C k hk_lt hkor v).mpr ⟨i, hi, by simp [effSupp, hilt, hv]⟩
            rw [hks] at hvj; exact Finset.notMem_empty _ hvj
          exact hmono i hilt his
        have hSL : soundLeaves C (42 + k) =
            C.gates[k].inputs.foldl (fun acc i => if hi : i < 42 + k then acc ∪ soundLeaves C i else acc) ∅ := by
          rw [soundLeaves]
          simp [show ¬(42 + k < 42) by omega, show 42 + k < 42 + C.gates.length by omega, hkor_b]
        generalize hl : C.gates[k].inputs = l at hlen2 hchild_mono hSL
        rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
        · refine ⟨f, ?_, by rw [hoss_split]; simp [hkoss]; omega⟩
          intro w hw hws
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hw) with h | rfl
          · exact hmono w h hws
          · change ∃ c, ∀ x ∈ soundLeaves C (42 + k) ∩ T, f x = c
            rw [hSL]; exact ⟨0, fun x hx => by simp at hx⟩
        · refine ⟨f, ?_, by rw [hoss_split]; simp [hkoss]; omega⟩
          intro w hw hws
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hw) with h | rfl
          · exact hmono w h hws
          · change ∃ c, ∀ x ∈ soundLeaves C (42 + k) ∩ T, f x = c
            rw [hSL]; simp only [List.foldl_cons, List.foldl_nil, Finset.empty_union]
            split_ifs with ha
            · exact hchild_mono a List.mem_cons_self ha
            · exact ⟨0, fun x hx => by simp at hx⟩
        · by_cases ha : a < 42 + k
          · by_cases hb : b < 42 + k
            · obtain ⟨c1, hc1⟩ := hchild_mono a List.mem_cons_self ha
              obtain ⟨c2, hc2⟩ := hchild_mono b (List.mem_cons_of_mem _ List.mem_cons_self) hb
              obtain ⟨hun, hpres, hdrop⟩ := color_merge_step T f (soundLeaves C a ∩ T) (soundLeaves C b ∩ T) c1 c2 hc1 hc2
              refine ⟨fun x => if f x = c2 then c1 else f x, ?_, ?_⟩
              · intro w hw hws
                rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hw) with h | rfl
                · exact hpres _ (hmono w h hws)
                · change ∃ c, ∀ x ∈ soundLeaves C (42 + k) ∩ T, (if f x = c2 then c1 else f x) = c
                  rw [hSL]; simp only [List.foldl_cons, List.foldl_nil, ha, hb, ↓reduceDIte, Finset.empty_union]
                  rw [Finset.union_inter_distrib_right]
                  exact ⟨c1, hun⟩
              · rw [hoss_split]; simp only [hkoss, ↓reduceIte]; omega
            · refine ⟨f, ?_, by rw [hoss_split]; simp [hkoss]; omega⟩
              intro w hw hws
              rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hw) with h | rfl
              · exact hmono w h hws
              · change ∃ c, ∀ x ∈ soundLeaves C (42 + k) ∩ T, f x = c
                rw [hSL]; simp only [List.foldl_cons, List.foldl_nil, ha, hb, ↓reduceDIte, Finset.empty_union]
                exact hchild_mono a List.mem_cons_self ha
          · refine ⟨f, ?_, by rw [hoss_split]; simp [hkoss]; omega⟩
            intro w hw hws
            rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hw) with h | rfl
            · exact hmono w h hws
            · change ∃ c, ∀ x ∈ soundLeaves C (42 + k) ∩ T, f x = c
              rw [hSL]; simp only [List.foldl_cons, List.foldl_nil, ha, ↓reduceDIte]
              split_ifs with hb
              · simp only [Finset.empty_union]
                exact hchild_mono b (List.mem_cons_of_mem _ List.mem_cons_self) hb
              · exact ⟨0, fun x hx => by simp at hx⟩
        · simp at hlen2
      · refine ⟨f, ?_, by rw [hoss_split]; simp [hkoss]; omega⟩
        intro w hw hws
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hw) with h | rfl
        · exact hmono w h hws
        · change supp C (42 + k) = ∅ at hws
          have hhand : C.gates[k].op = GateOp.and := by
            have hop := (hM C.gates[k] (List.getElem_mem hk_lt)).1
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
            rcases hop with hop | hop
            · exact hop
            · exfalso
              apply hkoss
              refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk_lt, ?_, hws⟩
              rw [List.getElem?_eq_getElem hk_lt]; simp [(isOr_iff _).mpr hop]
          have hnotor : ¬(isOr C.gates[k] = true) := by rw [isOr_iff, hhand]; intro h; cases h
          have hSL : soundLeaves C (42 + k) =
              match C.gates[k].inputs with
              | [] => ∅
              | [a] => if a < 42 + k then soundLeaves C a else ∅
              | a :: b :: _ =>
                if a < 42 + k then
                  if b < 42 + k then
                    if supp C a = ∅ then soundLeaves C a
                    else if supp C b = ∅ then soundLeaves C b
                    else {k}
                  else ∅
                else ∅ := by
            rw [soundLeaves]
            simp [show ¬(42 + k < 42) by omega, show 42 + k < 42 + C.gates.length by omega, hnotor]
          change ∃ c, ∀ x ∈ soundLeaves C (42 + k) ∩ T, f x = c
          rw [hSL]
          have hlen2 : C.gates[k].inputs.length ≤ 2 := (hM C.gates[k] (List.getElem_mem hk_lt)).2
          generalize hl : C.gates[k].inputs = l at hlen2 ⊢
          rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
          · exact ⟨0, fun x hx => by simp at hx⟩
          · dsimp only
            split_ifs with ha
            · have hsa : supp C a = ∅ := by
                ext v
                simp only [Finset.notMem_empty, iff_false]
                intro hv
                have hvk : wval C (singleIn v) (42 + k) = true := by
                  rw [wval_gate C _ k hk_lt, hhand, hl]
                  simp [GateOp.eval, ha, (mem_supp C a v).mp hv]
                have hvm : v ∈ supp C (42 + k) := (mem_supp C _ _).mpr hvk
                rw [hws] at hvm; exact Finset.notMem_empty _ hvm
              exact hmono a ha hsa
            · exact ⟨0, fun x hx => by simp at hx⟩
          · dsimp only
            split_ifs with ha hb hsa hsb
            · exact hmono a ha hsa
            · exact hmono b hb hsb
            · exact ⟨f k, fun x hx => by
                have := (Finset.mem_inter.mp hx).1
                rw [Finset.mem_singleton.mp this]⟩
            · exact ⟨0, fun x hx => by simp at hx⟩
            · exact ⟨0, fun x hx => by simp at hx⟩
          · simp at hlen2
  obtain ⟨f, hmono, hcard⟩ := hstep C.gates.length le_rfl
  have hfilt : oss.filter (· < C.gates.length) = oss := by
    ext x; simp only [Finset.mem_filter, and_iff_left_iff_imp]
    intro hx; exact Finset.mem_range.mp (Finset.mem_filter.mp hx).1
  rw [hfilt] at hcard
  have hTout : C.output < 42 + C.gates.length := by
    by_contra hge
    have hemp : soundLeaves C C.output = ∅ := by
      rw [soundLeaves]
      simp [show ¬(C.output < 42) by omega, hge]
    rw [hemp] at hT
    exact Finset.not_nonempty_empty (hT ▸ hTne)
  obtain ⟨c, hc⟩ := hmono C.output hTout (supp_output_empty C hcomp)
  have himg : (T.image f).card ≤ 1 := by
    have hsub : T.image f ⊆ {c} := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      rw [Finset.mem_singleton]
      exact hc x (Finset.mem_inter.mpr ⟨hT ▸ hx, hx⟩)
    exact (Finset.card_le_card hsub).trans (by simp)
  change T.card ≤ oss.card + 1
  omega

def nbrs (c : Fin 42) : Finset (Fin 42) :=
  Finset.univ.filter fun v => adj c v = true

lemma star_or_component_bound (C : Circuit) (hM : Monotone2 C) (hcomp : computes C) (hcl : clean C)
    (c : Fin 42)
    (Ec : Finset (Fin 42)) (hEc_sub : Ec ⊆ nbrs c)
    (Qs : Finset (Finset (Fin 42)))
    (hQs_wire : ∀ Q ∈ Qs, ∃ w < 42 + C.gates.length, supp C w = Q)
    (hQs_sub : ∀ Q ∈ Qs, Q ⊆ Ec)
    (hQs_cov : ∀ v ∈ Ec, ∃ Q ∈ Qs, v ∈ Q) :
    Ec.card ≤
      ((Finset.range C.gates.length).filter fun j =>
        C.gates[j]?.map isOr = some true ∧
        2 ≤ (supp C (42 + j)).card ∧ supp C (42 + j) ⊆ nbrs c).card +
      Qs.card := by
  classical
  let mc : Finset ℕ := (Finset.range C.gates.length).filter fun j =>
    C.gates[j]?.map isOr = some true ∧
    2 ≤ (supp C (42 + j)).card ∧ supp C (42 + j) ⊆ nbrs c
  have hstep : ∀ k ≤ C.gates.length, ∃ f : Fin 42 → ℕ,
      (∀ w < 42 + k, supp C w ⊆ nbrs c → ∃ col, ∀ x ∈ supp C w ∩ Ec, f x = col) ∧
      Ec.card ≤ (Ec.image f).card + (mc.filter (· < k)).card := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨fun x => x.val, ?_, ?_⟩
      · intro w hw _
        have hw' : w < 42 := by omega
        change ∃ col, ∀ x ∈ supp C (⟨w, hw'⟩ : Fin 42).val ∩ Ec, x.val = col
        rw [supp_input]
        refine ⟨w, fun x hx => ?_⟩
        have := Finset.mem_singleton.mp (Finset.mem_inter.mp hx).1
        rw [this]
      · have hemp : mc.filter (· < 0) = ∅ := by
          rw [Finset.filter_eq_empty_iff]; intro x _; omega
        rw [hemp, Finset.card_empty, add_zero, Finset.card_image_of_injective _ Fin.val_injective]
    | succ k ih =>
      intro hk
      obtain ⟨f, hmono, hcard⟩ := ih (by omega)
      have hk_lt : k < C.gates.length := by omega
      have hmc_split : (mc.filter (· < k + 1)).card =
          (mc.filter (· < k)).card + if k ∈ mc then 1 else 0 := by
        have h1 : mc.filter (· < k + 1) =
            if k ∈ mc then insert k (mc.filter (· < k)) else mc.filter (· < k) := by
          ext x
          split_ifs with hkmc
          · simp only [Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨hx, hlt⟩; rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hlt) with h | rfl
              · exact Or.inr ⟨hx, h⟩
              · exact Or.inl rfl
            · rintro (rfl | ⟨hx, h⟩); exact ⟨hkmc, by omega⟩; exact ⟨hx, by omega⟩
          · simp only [Finset.mem_filter]
            constructor
            · rintro ⟨hx, hlt⟩; refine ⟨hx, ?_⟩
              have hne : x ≠ k := fun h => hkmc (h ▸ hx)
              omega
            · rintro ⟨hx, h⟩; exact ⟨hx, by omega⟩
        rw [h1]
        split_ifs with hkmc
        · rw [Finset.card_insert_of_notMem (by simp)]
        · omega
      by_cases hkmc : k ∈ mc
      · have hkor_b : isOr C.gates[k] = true := by
          have hm := (Finset.mem_filter.mp hkmc).2.1
          rw [List.getElem?_eq_getElem hk_lt] at hm
          simpa using hm
        have hkor : C.gates[k].op = GateOp.or := (isOr_iff _).mp hkor_b
        have hksub : supp C (42 + k) ⊆ nbrs c := (Finset.mem_filter.mp hkmc).2.2.2
        have hlen2 : C.gates[k].inputs.length ≤ 2 := (hM C.gates[k] (List.getElem_mem hk_lt)).2
        have hchild_mono : ∀ i ∈ C.gates[k].inputs, i < 42 + k →
            ∃ col, ∀ x ∈ supp C i ∩ Ec, f x = col := by
          intro i hi hilt
          apply hmono i hilt
          intro v hv
          exact hksub ((supp_or_gate C k hk_lt hkor v).mpr ⟨i, hi, by simp [effSupp, hilt, hv]⟩)
        have hSk : ∀ v, v ∈ supp C (42 + k) ↔ ∃ i ∈ C.gates[k].inputs, i < 42 + k ∧ v ∈ supp C i := by
          intro v
          rw [supp_or_gate C k hk_lt hkor v]
          constructor
          · rintro ⟨i, hi, hv⟩
            by_cases hilt : i < 42 + k
            · exact ⟨i, hi, hilt, by simpa [effSupp, hilt] using hv⟩
            · simp [effSupp, hilt] at hv
          · rintro ⟨i, hi, hilt, hv⟩
            exact ⟨i, hi, by simp [effSupp, hilt, hv]⟩
        generalize hl : C.gates[k].inputs = l at hlen2 hchild_mono hSk
        rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨d, t⟩⟩⟩
        · refine ⟨f, ?_, by rw [hmc_split]; simp [hkmc]; omega⟩
          intro w hw hwsub
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hw) with h | rfl
          · exact hmono w h hwsub
          · exact ⟨0, fun x hx => by have := (hSk x).mp (Finset.mem_inter.mp hx).1; simp at this⟩
        · refine ⟨f, ?_, by rw [hmc_split]; simp [hkmc]; omega⟩
          intro w hw hwsub
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hw) with h | rfl
          · exact hmono w h hwsub
          · by_cases ha : a < 42 + k
            · obtain ⟨col, hcol⟩ := hchild_mono a List.mem_cons_self ha
              refine ⟨col, fun x hx => hcol x ?_⟩
              have hxk := (hSk x).mp (Finset.mem_inter.mp hx).1
              simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_left] at hxk
              exact Finset.mem_inter.mpr ⟨hxk.2, (Finset.mem_inter.mp hx).2⟩
            · exact ⟨0, fun x hx => by
                have := (hSk x).mp (Finset.mem_inter.mp hx).1
                simp [ha] at this⟩
        · by_cases ha : a < 42 + k
          · by_cases hb : b < 42 + k
            · obtain ⟨c1, hc1⟩ := hchild_mono a List.mem_cons_self ha
              obtain ⟨c2, hc2⟩ := hchild_mono b (List.mem_cons_of_mem _ List.mem_cons_self) hb
              obtain ⟨hun, hpres, hdrop⟩ := color_merge_step Ec f (supp C a ∩ Ec) (supp C b ∩ Ec) c1 c2 hc1 hc2
              refine ⟨fun x => if f x = c2 then c1 else f x, ?_, ?_⟩
              · intro w hw hwsub
                rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hw) with h | rfl
                · exact hpres _ (hmono w h hwsub)
                · refine ⟨c1, fun x hx => hun x ?_⟩
                  have hxk := (hSk x).mp (Finset.mem_inter.mp hx).1
                  have hxE := (Finset.mem_inter.mp hx).2
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hxk
                  rcases hxk with ⟨_, rfl | rfl, _, hxab⟩
                  · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hxab, hxE⟩)
                  · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hxab, hxE⟩)
              · rw [hmc_split]; simp only [hkmc, ↓reduceIte]; omega
            · refine ⟨f, ?_, by rw [hmc_split]; simp [hkmc]; omega⟩
              intro w hw hwsub
              rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hw) with h | rfl
              · exact hmono w h hwsub
              · obtain ⟨col, hcol⟩ := hchild_mono a List.mem_cons_self ha
                refine ⟨col, fun x hx => hcol x ?_⟩
                have hxk := (hSk x).mp (Finset.mem_inter.mp hx).1
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hxk
                rcases hxk with ⟨_, rfl | rfl, hlt', hxab⟩
                · exact Finset.mem_inter.mpr ⟨hxab, (Finset.mem_inter.mp hx).2⟩
                · exact absurd hlt' hb
          · refine ⟨f, ?_, by rw [hmc_split]; simp [hkmc]; omega⟩
            intro w hw hwsub
            rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hw) with h | rfl
            · exact hmono w h hwsub
            · by_cases hb : b < 42 + k
              · obtain ⟨col, hcol⟩ := hchild_mono b (List.mem_cons_of_mem _ List.mem_cons_self) hb
                refine ⟨col, fun x hx => hcol x ?_⟩
                have hxk := (hSk x).mp (Finset.mem_inter.mp hx).1
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hxk
                rcases hxk with ⟨_, rfl | rfl, hlt', hxab⟩
                · exact absurd hlt' ha
                · exact Finset.mem_inter.mpr ⟨hxab, (Finset.mem_inter.mp hx).2⟩
              · exact ⟨0, fun x hx => by
                  have hxk := (hSk x).mp (Finset.mem_inter.mp hx).1
                  simp [ha, hb] at hxk⟩
        · simp at hlen2
      · refine ⟨f, ?_, by rw [hmc_split]; simp [hkmc]; omega⟩
        intro w hw hwsub
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hw) with h | rfl
        · exact hmono w h hwsub
        · change supp C (42 + k) ⊆ nbrs c at hwsub
          have hsmall : (supp C (42 + k)).card ≤ 1 := by
            have hop := (hM C.gates[k] (List.getElem_mem hk_lt)).1
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
            rcases hop with hop | hop
            · rw [supp_and_empty C hcomp hcl k hk_lt hop]; simp
            · by_contra hgt
              push Not at hgt
              apply hkmc
              refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk_lt, ?_, by omega, hwsub⟩
              rw [List.getElem?_eq_getElem hk_lt]; simp [(isOr_iff _).mpr hop]
          rcases Finset.card_le_one_iff_subset_singleton.mp hsmall with ⟨v0, hv0⟩
          refine ⟨f v0, fun x hx => ?_⟩
          have hx0 := Finset.mem_singleton.mp (hv0 (Finset.mem_inter.mp hx).1)
          rw [hx0]
  obtain ⟨f, hmono, hcard⟩ := hstep C.gates.length le_rfl
  have hfilt : mc.filter (· < C.gates.length) = mc := by
    ext x; simp only [Finset.mem_filter, and_iff_left_iff_imp]
    intro hx; exact Finset.mem_range.mp (Finset.mem_filter.mp hx).1
  rw [hfilt] at hcard
  have himg : (Ec.image f).card ≤ Qs.card := by
    have hQcol : ∀ Q ∈ Qs, ∃ col, ∀ x ∈ Q, f x = col := by
      intro Q hQ
      obtain ⟨w, hw, hwQ⟩ := hQs_wire Q hQ
      have hsub : supp C w ⊆ nbrs c := hwQ.symm ▸ (hQs_sub Q hQ).trans hEc_sub
      obtain ⟨col, hcol⟩ := hmono w hw hsub
      refine ⟨col, fun x hx => hcol x (Finset.mem_inter.mpr ⟨hwQ.symm ▸ hx, hQs_sub Q hQ hx⟩)⟩
    choose g hg using hQcol
    have hsub_img : Ec.image f ⊆ Qs.attach.image (fun Q => g Q.1 Q.2) := by
      intro col hcol
      obtain ⟨v, hvE, rfl⟩ := Finset.mem_image.mp hcol
      obtain ⟨Q, hQ, hvQ⟩ := hQs_cov v hvE
      refine Finset.mem_image.mpr ⟨⟨Q, hQ⟩, Finset.mem_attach _ _, (hg Q hQ v hvQ).symm⟩
    exact (Finset.card_le_card hsub_img).trans
      ((Finset.card_image_le).trans (by simp))
  change Ec.card ≤ mc.card + Qs.card
  omega

lemma count_unmixed (C : Circuit) (hM : Monotone2 C) (hcomp : computes C) (hcl : clean C)
    (h0 : mixedOrCount C = 0) : 104 ≤ orCount C := by
  classical
  let T : Finset ℕ := soundLeaves C C.output
  have hTcov : ∀ e ∈ allEdges, ∃ j ∈ T, wval C (pairIn e.1 e.2) (42 + j) = true := by
    intro e he
    have hpe : pgRel e.1 e.2 = true := (Finset.mem_filter.mp he).2
    have hCout : C.eval (List.ofFn (pairIn e.1 e.2)) = true := by
      rw [hcomp]
      exact ⟨e.1, e.2, hpe, by simp [pairIn], by simp [pairIn]⟩
    exact soundLeaves_covers C hM hcomp hcl h0 C.output (supp_output_empty C hcomp) e hpe hCout
  have hTne : T.Nonempty := by
    have hne : allEdges.Nonempty := Finset.card_pos.mp (by rw [allEdges_card]; omega)
    obtain ⟨e, he⟩ := hne
    obtain ⟨j, hj, _⟩ := hTcov e he
    exact ⟨j, hj⟩
  have hleaf_star : ∀ j ∈ T, ∃ (c : Fin 42) (w : ℕ), w < 42 + C.gates.length ∧
      supp C w ⊆ nbrs c ∧
      ∀ e ∈ allEdges, wval C (pairIn e.1 e.2) (42 + j) = true →
        (e.1 = c ∧ e.2 ∈ supp C w) ∨ (e.2 = c ∧ e.1 ∈ supp C w) := by
    intro j hj
    obtain ⟨hj_lt, hhand, a, b, hinp, ha_lt, hb_lt, ha_ne, hb_ne⟩ := soundLeaves_lt C hM C.output j hj
    have hbic := clean_and_biclique C hM hcomp hcl j hj_lt hhand a b hinp ha_lt hb_lt
    have hstar := biclique_star (supp C a) (supp C b) hbic
    have heval : ∀ e ∈ allEdges, wval C (pairIn e.1 e.2) (42 + j) = true →
        (e.1 ∈ supp C a ∧ e.2 ∈ supp C b) ∨ (e.2 ∈ supp C a ∧ e.1 ∈ supp C b) := by
      intro e he hje
      rw [wval_gate C _ j hj_lt, hhand, hinp] at hje
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
        Bool.and_true, Bool.and_eq_true, id_eq, ha_lt, hb_lt, ↓reduceIte] at hje
      rw [unmixed_pure_supp C hM hcomp hcl h0 a ha_ne,
          unmixed_pure_supp C hM hcomp hcl h0 b hb_ne] at hje
      simp only [decide_eq_true_iff] at hje
      obtain ⟨⟨u, hu, hpu⟩, ⟨v, hv, hpv⟩⟩ := hje
      simp only [pairIn, decide_eq_true_eq] at hpu hpv
      rcases hpu with rfl | rfl <;> rcases hpv with rfl | rfl
      · exfalso; have := hbic e.1 hu e.1 hv; rw [adj_irrefl] at this; cases this
      · exact Or.inl ⟨hu, hv⟩
      · exact Or.inr ⟨hu, hv⟩
      · exfalso; have := hbic e.2 hu e.2 hv; rw [adj_irrefl] at this; cases this
    rcases hstar with ha1 | hb1
    · obtain ⟨c, hc⟩ := ha_ne
      have hsub : supp C a = {c} := by
        rcases Finset.card_le_one_iff_subset_singleton.mp ha1 with ⟨c0, hc0⟩
        have hcc0 : c = c0 := Finset.mem_singleton.mp (hc0 hc)
        subst hcc0
        exact Finset.Subset.antisymm hc0 (Finset.singleton_subset_iff.mpr hc)
      refine ⟨c, b, by omega, ?_, ?_⟩
      · intro v hv
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, hbic c hc v hv⟩
      · intro e he hje
        rcases heval e he hje with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [hsub, Finset.mem_singleton] at h1; exact Or.inl ⟨h1, h2⟩
        · rw [hsub, Finset.mem_singleton] at h1; exact Or.inr ⟨h1, h2⟩
    · obtain ⟨c, hc⟩ := hb_ne
      have hsub : supp C b = {c} := by
        rcases Finset.card_le_one_iff_subset_singleton.mp hb1 with ⟨c0, hc0⟩
        have hcc0 : c = c0 := Finset.mem_singleton.mp (hc0 hc)
        subst hcc0
        exact Finset.Subset.antisymm hc0 (Finset.singleton_subset_iff.mpr hc)
      refine ⟨c, a, by omega, ?_, ?_⟩
      · intro u hu
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, by rw [adj_symm]; exact hbic u hu c hc⟩
      · intro e he hje
        rcases heval e he hje with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [hsub, Finset.mem_singleton] at h2; exact Or.inr ⟨h2, h1⟩
        · rw [hsub, Finset.mem_singleton] at h2; exact Or.inl ⟨h2, h1⟩
  choose ctr leafW hleafW_lt hleafW_sub hleafW_cov using hleaf_star
  let Tc : Fin 42 → Finset ℕ := fun c => T.filter fun j => if hj : j ∈ T then ctr j hj = c else False
  let Qsc : Fin 42 → Finset (Finset (Fin 42)) := fun c =>
    T.attach.filter (fun x => ctr x.1 x.2 = c) |>.image (fun x => supp C (leafW x.1 x.2))
  let Ec : Fin 42 → Finset (Fin 42) := fun c => (Qsc c).biUnion id
  have hQsc_card : ∀ c, (Qsc c).card ≤ (Tc c).card := by
    intro c
    have h1 : (Qsc c).card ≤ (T.attach.filter fun x => ctr x.1 x.2 = c).card := Finset.card_image_le
    have h2 : (T.attach.filter fun x => ctr x.1 x.2 = c).card = (Tc c).card := by
      refine Finset.card_bij (fun x _ => x.1) ?_ ?_ ?_
      · intro x hx
        simp only [Tc, Finset.mem_filter] at hx ⊢
        exact ⟨x.2, by simp [x.2, hx.2]⟩
      · intro x _ y _ hxy; exact Subtype.ext hxy
      · intro j hj
        simp only [Tc, Finset.mem_filter] at hj
        obtain ⟨hjT, hctr⟩ := hj
        simp only [hjT, ↓reduceDIte] at hctr
        exact ⟨⟨j, hjT⟩, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hctr⟩, rfl⟩
    omega
  have hEc_sum : 105 ≤ ∑ c : Fin 42, (Ec c).card := by
    rw [← allEdges_card]
    let pairSet : Finset (Fin 42 × Fin 42) := Finset.univ.biUnion fun c => (Ec c).map
      ⟨fun v => if c.val < 21 then (c, v) else (v, c), by
        intro x y hxy; split_ifs at hxy <;> simp_all⟩
    have hsub : allEdges ⊆ pairSet := by
      intro e he
      obtain ⟨j, hjT, hje⟩ := hTcov e he
      set c := ctr j hjT
      have hQmem : supp C (leafW j hjT) ∈ Qsc c :=
        Finset.mem_image.mpr ⟨⟨j, hjT⟩, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, rfl⟩, rfl⟩
      have hpe : pgRel e.1 e.2 = true := (Finset.mem_filter.mp he).2
      have hlt1 : e.1.val < 21 := by unfold pgRel at hpe; simp only [decide_eq_true_eq] at hpe; exact hpe.1
      have hge2 : 21 ≤ e.2.val := by unfold pgRel at hpe; simp only [decide_eq_true_eq] at hpe; exact hpe.2.1
      rcases hleafW_cov j hjT e he hje with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hvEc : e.2 ∈ Ec c := Finset.mem_biUnion.mpr ⟨_, hQmem, h2⟩
        refine Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ c, Finset.mem_map.mpr ⟨e.2, hvEc, ?_⟩⟩
        have hc1 : c.val < 21 := by change (ctr j hjT).val < 21; rw [← h1]; exact hlt1
        simp only [Function.Embedding.coeFn_mk, hc1, ↓reduceIte]
        exact Prod.ext h1.symm rfl
      · have hvEc : e.1 ∈ Ec c := Finset.mem_biUnion.mpr ⟨_, hQmem, h2⟩
        refine Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ c, Finset.mem_map.mpr ⟨e.1, hvEc, ?_⟩⟩
        have hc2 : ¬(c.val < 21) := by change ¬((ctr j hjT).val < 21); rw [← h1]; omega
        simp only [Function.Embedding.coeFn_mk, hc2, ↓reduceIte]
        exact Prod.ext rfl h1.symm
    calc allEdges.card ≤ pairSet.card := Finset.card_le_card hsub
      _ ≤ ∑ c : Fin 42, ((Ec c).map _).card := Finset.card_biUnion_le
      _ = ∑ c : Fin 42, (Ec c).card := by simp
  let mc : Fin 42 → Finset ℕ := fun c =>
    (Finset.range C.gates.length).filter fun j =>
      C.gates[j]?.map isOr = some true ∧
      2 ≤ (supp C (42 + j)).card ∧ supp C (42 + j) ⊆ nbrs c
  let oss : Finset ℕ := (Finset.range C.gates.length).filter fun j =>
    C.gates[j]?.map isOr = some true ∧ supp C (42 + j) = ∅
  have hEc_le : ∀ c : Fin 42, (Ec c).card ≤ (mc c).card + (Tc c).card := by
    intro c
    have hb := star_or_component_bound C hM hcomp hcl c (Ec c)
      (by
        intro v hv
        obtain ⟨Q, hQ, hvQ⟩ := Finset.mem_biUnion.mp hv
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hQ
        have hcx : ctr x.1 x.2 = c := (Finset.mem_filter.mp hx).2
        exact hcx ▸ hleafW_sub x.1 x.2 hvQ)
      (Qsc c)
      (by
        intro Q hQ
        obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hQ
        exact ⟨leafW x.1 x.2, hleafW_lt x.1 x.2, rfl⟩)
      (fun Q hQ v hv => Finset.mem_biUnion.mpr ⟨Q, hQ, hv⟩)
      (fun v hv => Finset.mem_biUnion.mp hv)
    change (Ec c).card ≤ (mc c).card + (Qsc c).card at hb
    have hq := hQsc_card c
    omega
  have hTc_sum : ∑ c : Fin 42, (Tc c).card = T.card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext j
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Tc, Finset.mem_filter]
      constructor
      · rintro ⟨_, hjT, _⟩; exact hjT
      · intro hjT; exact ⟨ctr j hjT, hjT, by simp [hjT]⟩
    · intro c1 _ c2 _ hne
      change Disjoint (Tc c1) (Tc c2)
      rw [Finset.disjoint_left]
      intro j h1 h2
      simp only [Tc, Finset.mem_filter] at h1 h2
      obtain ⟨hjT, hc1⟩ := h1
      obtain ⟨_, hc2⟩ := h2
      simp only [hjT, ↓reduceDIte] at hc1 hc2
      exact hne (hc1.symm.trans hc2)
  have hmc_disj : ∀ c1 c2 : Fin 42, c1 ≠ c2 → Disjoint (mc c1) (mc c2) := by
    intro c1 c2 hne
    rw [Finset.disjoint_left]
    intro j h1 h2
    have hcard2 := (Finset.mem_filter.mp h1).2.2.1
    have hsub1 := (Finset.mem_filter.mp h1).2.2.2
    have hsub2 := (Finset.mem_filter.mp h2).2.2.2
    obtain ⟨v1, hv1, v2, hv2, hvne⟩ := Finset.one_lt_card.mp (by omega : 1 < (supp C (42 + j)).card)
    exact pgRel_c4 c1 c2 v1 v2 hne hvne
      (Finset.mem_filter.mp (hsub1 hv1)).2
      (Finset.mem_filter.mp (hsub1 hv2)).2
      (Finset.mem_filter.mp (hsub2 hv1)).2
      (Finset.mem_filter.mp (hsub2 hv2)).2
  let allOrs : Finset ℕ := (Finset.range C.gates.length).filter fun j =>
    C.gates[j]?.map isOr = some true
  have hallOrs_card : allOrs.card = orCount C := by
    unfold allOrs orCount
    have h1 : ∀ (gs : List Gate),
        ((Finset.range gs.length).filter fun j => gs[j]?.map isOr = some true).card =
        gs.countP isOr := by
      intro gs
      induction gs using List.reverseRecOn with
      | nil => simp
      | append_singleton gs g ih =>
        rw [List.length_append, List.length_singleton, Finset.range_add_one,
          Finset.filter_insert, List.countP_append, List.countP_singleton]
        have hfilt : (Finset.range gs.length).filter
            (fun j => (gs ++ [g])[j]?.map isOr = some true) =
            (Finset.range gs.length).filter
            (fun j => gs[j]?.map isOr = some true) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_range]
          constructor <;> rintro ⟨hj, h⟩ <;> refine ⟨hj, ?_⟩
          · rwa [List.getElem?_append_left hj] at h
          · rwa [List.getElem?_append_left hj]
        have hlast : (gs ++ [g])[gs.length]?.map isOr = some (isOr g) := by
          simp
        rw [hfilt, hlast]
        cases hg : isOr g
        · simp only [Option.some.injEq, Bool.false_eq_true, ↓reduceIte, ih, add_zero]
        · simp only [↓reduceIte]
          rw [Finset.card_insert_of_notMem (by simp), ih]
    exact h1 C.gates
  have hmc_oss : (Finset.univ.biUnion mc).card + oss.card ≤ allOrs.card := by
    rw [← Finset.card_union_of_disjoint]
    · apply Finset.card_le_card
      intro j hj
      rcases Finset.mem_union.mp hj with hm | ho
      · obtain ⟨c, _, hjc⟩ := Finset.mem_biUnion.mp hm
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hjc).1, (Finset.mem_filter.mp hjc).2.1⟩
      · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ho).1, (Finset.mem_filter.mp ho).2.1⟩
    · rw [Finset.disjoint_left]
      intro j hm ho
      obtain ⟨c, _, hjc⟩ := Finset.mem_biUnion.mp hm
      have h2 := (Finset.mem_filter.mp hjc).2.2.1
      have h0s := (Finset.mem_filter.mp ho).2.2
      rw [h0s] at h2; simp at h2
  have hmc_sum : ∑ c : Fin 42, (mc c).card = (Finset.univ.biUnion mc).card := by
    rw [Finset.card_biUnion (fun c1 _ c2 _ hne => hmc_disj c1 c2 hne)]
  have hT_le : T.card ≤ oss.card + 1 := soundLeaves_card_le C hM hcomp T rfl hTne
  have hsum_le : ∑ c : Fin 42, (Ec c).card ≤ ∑ c : Fin 42, (mc c).card + ∑ c : Fin 42, (Tc c).card := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun c _ => hEc_le c
  omega

end PEqualNP.Outside.L_meta_8323

theorem PEqualNP.Outside.L_meta_8323 : (have x1 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x2 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (42 : ℕ)) (x4 : Fin (42 : ℕ)), (↑x3 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x4 ∧ (↑x4 + (21 : ℕ) - ↑x3) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → x4.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x7 : Fin (42 : ℕ) → Bool), (x2.wires (List.ofFn x7)).getD ((42 : ℕ) + x3) Bool.false = Bool.true → x2.eval (List.ofFn x7) = Bool.true; have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.casesOn x4.op Bool.false Bool.true Bool.false (fun (x5 : ℕ) => Bool.false) Bool.false) x3.gates; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → x1 x4 → x2 x4 → (104 : ℕ) ≤ x3 x4) := by
  dsimp only
  intro C hM hcomp hcl
  have hcomp' : PEqualNP.Outside.L_meta_8323.computes C := by
    intro x
    simpa [PEqualNP.Outside.L_meta_8323.pgRel] using hcomp x
  obtain ⟨D, hDM, hDcomp, hDcl, hDor, hD0⟩ :=
    PEqualNP.Outside.L_meta_8323.exists_unmixed C hM hcomp' hcl
  have hbound := PEqualNP.Outside.L_meta_8323.count_unmixed D hDM hDcomp hDcl hD0
  rw [hDor] at hbound
  exact hbound
