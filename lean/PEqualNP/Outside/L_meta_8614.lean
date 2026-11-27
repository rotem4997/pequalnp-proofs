import Mathlib
import PEqualNP.Defs

-- The lower bounds use the search and its soundness proof from the merged proof of L-meta-139
-- (PEqualNP/Outside/L_meta_139.lean, by Lewis Watson), copied once per table with numbered names;
-- the target tables, the bounds and the AND/OR circuits of those sizes are new.

namespace PEqualNP.Outside.L_meta_8614

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
private def graph_t0 (x : Fin 5 → Bool) : Bool :=
  Nat.testBit 0x00000000 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

private def upperC_t0 : Circuit :=
  { gates := [],
    output := 5 }

private theorem upper_mono_t0 : Monotone2 upperC_t0 := by
  intro g hg
  simp [upperC_t0] at hg
private theorem upper_eval_t0 : ∀ x : Fin 5 → Bool, upperC_t0.eval (List.ofFn x) = graph_t0 x := by
  decide +kernel

private theorem main_t0 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => Nat.testBit 0x00000000 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit 0x00000000 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) :=
  fun s _ => ⟨upperC_t0, upper_mono_t0, Nat.zero_le s, upper_eval_t0⟩

private def graph_t1 (x : Fin 5 → Bool) : Bool :=
  Nat.testBit 0xaaaaaaaa (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

private def upperC_t1 : Circuit :=
  { gates := [],
    output := 0 }

private theorem upper_mono_t1 : Monotone2 upperC_t1 := by
  intro g hg
  simp [upperC_t1] at hg
private theorem upper_eval_t1 : ∀ x : Fin 5 → Bool, upperC_t1.eval (List.ofFn x) = graph_t1 x := by
  decide +kernel

private theorem main_t1 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => Nat.testBit 0xaaaaaaaa (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit 0xaaaaaaaa (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) :=
  fun s _ => ⟨upperC_t1, upper_mono_t1, Nat.zero_le s, upper_eval_t1⟩


private abbrev T_t2 := BitVec 32
private def ins_t2 : List T_t2 := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]
private def target_t2 : T_t2 := 0x88888888
private def possible_t2 (w : List T_t2) (z : T_t2) : Bool :=
  z == 0 || z == (-1) || w.any (fun u => z == u || z == ~~~u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit_t2 (k : Fin 32) (z : T_t2) := z[k.val]

private theorem read_bit_t2 (w : List T_t2) (i : ℕ) (k : Fin 32) :
    (w.map (bit_t2 k)).getD i false = bit_t2 k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit_t2]

private theorem read_wire_t2 (w : List T_t2) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

private theorem atom_t2 {ws : List T_t2} {x : T_t2} (hx : x = 0 ∨ x ∈ ws) :
    possible_t2 ws x ∧ possible_t2 ws (~~~x) := by
  rcases hx with rfl | hx
  · simp [possible_t2]
  · simp only [possible_t2, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    grind

private theorem pair_t2 {ws : List T_t2} {x y : T_t2} (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
    possible_t2 ws (x &&& y) ∧ possible_t2 ws (x ||| y) := by
  rcases hx with rfl | hx
  · simpa [possible_t2] using (show possible_t2 ws 0 ∧ possible_t2 ws y from ⟨by simp [possible_t2], (atom_t2 hy).1⟩)
  rcases hy with rfl | hy
  · simpa [possible_t2] using (show possible_t2 ws 0 ∧ possible_t2 ws x from ⟨by simp [possible_t2], (atom_t2 (.inr hx)).1⟩)
  · simp only [possible_t2, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    constructor
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inl rfl⟩⟩
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inr rfl⟩⟩

private def step_t2 (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def legal_t2 (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private theorem gate_table_t2 (w ws : List T_t2) (hw : w ⊆ ws) (g : Gate) (hg : legal_t2 g) :
    ∃ z, possible_t2 ws z ∧ ∀ k, step_t2 (w.map (bit_t2 k)) g = (w ++ [z]).map (bit_t2 k) := by
  have mem (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ ws := (read_wire_t2 w i).imp_right (fun h => hw h)
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl | rfl
    · exact ⟨-1, by simp [possible_t2], by simp [step_t2, GateOp.eval, bit_t2]; decide⟩
    · exact ⟨0, by simp [possible_t2], by simp [step_t2, GateOp.eval, bit_t2]⟩
    · exact ⟨-1, by simp [possible_t2], by simp [step_t2, GateOp.eval, bit_t2]; decide⟩
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl | rfl
      · exact ⟨_, (atom_t2 (mem i)).1, by simp only [step_t2, List.map_cons, List.map_nil, read_bit_t2]; simp [GateOp.eval]⟩
      · exact ⟨_, (atom_t2 (mem i)).1, by simp only [step_t2, List.map_cons, List.map_nil, read_bit_t2]; simp [GateOp.eval]⟩
      · exact ⟨_, (atom_t2 (mem i)).2, by simp only [step_t2, List.map_cons, List.map_nil, read_bit_t2]; simp [GateOp.eval, bit_t2]⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl | rfl
        · exact ⟨_, (pair_t2 (mem i) (mem j)).1, by simp only [step_t2, List.map_cons, List.map_nil, read_bit_t2]; simp [GateOp.eval, bit_t2]⟩
        · exact ⟨_, (pair_t2 (mem i) (mem j)).2, by simp only [step_t2, List.map_cons, List.map_nil, read_bit_t2]; simp [GateOp.eval, bit_t2]⟩
        · exact ⟨_, (atom_t2 (mem i)).2, by simp only [step_t2, List.map_cons, List.map_nil, read_bit_t2]; simp [GateOp.eval, bit_t2]⟩

private def safe_t2 : ℕ → List T_t2 → Prop
  | 0, ws => ws.contains target_t2 = false
  | n + 1, ws => ∀ z, possible_t2 ws z → safe_t2 n (z :: ws)

private theorem absent_t2 {n : ℕ} {ws : List T_t2} (h : safe_t2 n ws) : target_t2 ∉ ws := by
  induction n generalizing ws with
  | zero => simpa [safe_t2] using h
  | succ n ih =>
    have ht := ih (h 0 (by simp [possible_t2]))
    exact fun hm => ht (List.mem_cons_of_mem _ hm)

private theorem exclude_t2 (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal_t2 g)
    (w ws : List T_t2) (hw : w ⊆ ws) (m : ℕ) (hm : gs.length ≤ m) (hs : safe_t2 m ws)
    (he : ∀ k, (gs.foldl step_t2 (w.map (bit_t2 k))).getD out false = bit_t2 k target_t2) : False := by
  induction gs generalizing w ws m with
  | nil =>
    have hval : w.getD out 0 = target_t2 := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit_t2, bit_t2] using he ⟨i, hi⟩
    have hr := read_wire_t2 w out
    rw [hval] at hr
    rcases hr with hz | ht
    · exact (by decide : target_t2 ≠ 0) hz
    · exact absent_t2 hs (hw ht)
  | cons g gs ih =>
    cases m with
    | zero => simp at hm
    | succ m =>
      obtain ⟨z, hz, hstep⟩ := gate_table_t2 w ws hw g (hg g (by simp))
      apply ih (fun g' hg' => hg g' (by simp [hg'])) (w ++ [z]) (z :: ws) _ m
        (by simpa using hm) (hs z hz)
      · intro k
        simpa only [List.foldl_cons, hstep] using he k
      · intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact List.mem_cons_of_mem _ (hw hx)
        · simp

private def choices_t2 (ws : List T_t2) : List T_t2 :=
  (0 :: -1 :: ws.flatMap (fun x => x :: ~~~x :: ws.flatMap (fun y => [x &&& y, x ||| y]))).eraseDups

private theorem choice_iff_t2 (ws : List T_t2) (z : T_t2) : z ∈ choices_t2 ws ↔ possible_t2 ws z := by
  simp [choices_t2, possible_t2, List.any_eq_true]
  grind

-- With two gates left, only an existing wire containing every true bit_t2 of
-- the target_t2 can serve as the other input to an AND. OR has the dual test.
private def lastTwo_t2 (ws : List T_t2) : Bool :=
  let above := ws.filter (fun x => (x &&& target_t2) == target_t2)
  let below := ws.filter (fun x => (x ||| target_t2) == target_t2)
  (choices_t2 ws).all fun z => !(z == target_t2 || ~~~z == target_t2 ||
    above.any (fun x => (x &&& z) == target_t2) ||
    below.any (fun x => (x ||| z) == target_t2))

private theorem lastTwo_safe_t2 {ws : List T_t2} (h : lastTwo_t2 ws) : safe_t2 2 ws := by
  intro z hz v hv
  have hz' := (choice_iff_t2 ws z).2 hz
  have ht (u : T_t2) (hu : u ∈ choices_t2 ws) := (List.all_eq_true.mp h) u hu
  have hnot (u : T_t2) (hu : u ∈ choices_t2 ws) : u ≠ target_t2 ∧ ~~~u ≠ target_t2 ∧
      (∀ x ∈ ws, x &&& u ≠ target_t2) ∧ (∀ x ∈ ws, x ||| u ≠ target_t2) := by
    have H := ht u hu
    simp at H
    obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := H
    refine ⟨h1,h2,?_,?_⟩
    · intro x hx he
      apply h3 x hx _ he
      rw [← he, ← BitVec.and_assoc, BitVec.and_self]
    · intro x hx he
      apply h4 x hx _ he
      rw [← he, ← BitVec.or_assoc, BitVec.or_self]
  have H := hnot z hz'
  have base (x : T_t2) (hx : x ∈ ws) := hnot x ((choice_iff_t2 ws x).2 (atom_t2 (.inr hx)).1)
  have unary (x : T_t2) (hx : x ∈ z :: ws) : x ≠ target_t2 ∧ ~~~x ≠ target_t2 := by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨H.1, H.2.1⟩
    · exact ⟨(base x hx).1, (base x hx).2.1⟩
  have binary (x y : T_t2) (hx : x ∈ z :: ws) (hy : y ∈ z :: ws) :
      x &&& y ≠ target_t2 ∧ x ||| y ≠ target_t2 := by
    rcases List.mem_cons.mp hx with hxe | hxm <;> rcases List.mem_cons.mp hy with hye | hym
    · simpa [hxe, hye] using H.1
    · simpa [hxe, BitVec.and_comm, BitVec.or_comm] using And.intro (H.2.2.1 y hym) (H.2.2.2 y hym)
    · simpa [hye] using And.intro (H.2.2.1 x hxm) (H.2.2.2 x hxm)
    · exact ⟨(base y hym).2.2.1 x hxm, (base y hym).2.2.2 x hxm⟩
  have hv' : v ≠ target_t2 := by
    simp only [possible_t2, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hv
    rcases hv with ((h | h) | ⟨x, hx, ((h | h) | ⟨y, hy, h | h⟩)⟩) <;> subst v
    · decide
    · decide
    · exact (unary x hx).1
    · exact (unary x hx).2
    · exact (binary x y hx hy).1
    · exact (binary x y hx hy).2
  change (v :: z :: ws).contains target_t2 = false
  suffices target_t2 ∉ v :: z :: ws by simpa using this
  intro hm
  rcases List.mem_cons.mp hm with he | hm
  · exact hv' he.symm
  · exact (unary target_t2 hm).1 rfl

private def masked_t2 (ws : List T_t2) (mask want : T_t2) : Bool :=
  let xs := ws.map (fun x => x &&& mask)
  want == 0 || want == mask || xs.any fun x =>
    x == want || (~~~x &&& mask) == want ||
    ((x &&& want) == want && xs.any (fun y => (x &&& y) == want)) ||
    ((x ||| want) == want && xs.any (fun y => (x ||| y) == want))

private def fastTwo_t2 (ws : List T_t2) : Bool :=
  !(masked_t2 ws (-1) target_t2 || masked_t2 ws (-1) (~~~target_t2) ||
    ws.any fun x =>
      ((x &&& target_t2) == target_t2 && masked_t2 ws x target_t2) ||
      ((x ||| target_t2) == target_t2 && masked_t2 ws (~~~x) (target_t2 &&& ~~~x)))

private theorem masked_of_possible_t2 {ws : List T_t2} {u : T_t2} (hu : possible_t2 ws u) (m : T_t2) :
    masked_t2 ws m (u &&& m) := by
  let xs := ws.map (fun x => x &&& m)
  have mem (x : T_t2) (hx : x ∈ ws) : x &&& m ∈ xs := List.mem_map.mpr ⟨x, hx, rfl⟩
  simp only [masked_t2, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.any_eq_true]
  simp only [possible_t2, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hu
  rcases hu with ((h | h) | ⟨x, hx, ((h | h) | ⟨y, hy, h | h⟩)⟩) <;> subst u
  · exact .inl (.inl (by simp))
  · exact .inl (.inr BitVec.allOnes_and)
  · exact .inr ⟨_, mem x hx, .inl (.inl (.inl rfl))⟩
  · refine .inr ⟨_, mem x hx, .inl (.inl (.inr ?_))⟩
    apply BitVec.eq_of_getElem_eq
    intro i hi
    simp
    cases x[i] <;> cases m[i] <;> rfl
  · refine .inr ⟨_, mem x hx, .inl (.inr ⟨?_, _, mem y hy, ?_⟩)⟩ <;>
      apply BitVec.eq_of_getElem_eq <;> intro i hi <;> simp only [BitVec.getElem_and] <;>
      cases x[i] <;> cases y[i] <;> cases m[i] <;> decide
  · refine .inr ⟨_, mem x hx, .inr ⟨?_, _, mem y hy, ?_⟩⟩ <;>
      apply BitVec.eq_of_getElem_eq <;> intro i hi <;> simp only [BitVec.getElem_and, BitVec.getElem_or] <;>
      cases x[i] <;> cases y[i] <;> cases m[i] <;> decide

private theorem fast_implies_last_t2 {ws : List T_t2} (hf : fastTwo_t2 ws) : lastTwo_t2 ws := by
  simp [fastTwo_t2] at hf
  obtain ⟨⟨hn, hc⟩, hp⟩ := hf
  apply List.all_eq_true.mpr
  intro z hz
  have hz' := (choice_iff_t2 _ _).1 hz
  simp
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro he
    have hh := masked_of_possible_t2 hz' (-1)
    rw [show z &&& (-1 : T_t2) = z from BitVec.and_allOnes, he] at hh
    simp_all
  · intro he
    have hh := masked_of_possible_t2 hz' (-1)
    have he' : z = ~~~target_t2 := by rw [← he, BitVec.not_not]
    rw [show z &&& (-1 : T_t2) = z from BitVec.and_allOnes, he'] at hh
    simp_all
  · intro x hx ha he
    have hh := masked_of_possible_t2 hz' x
    rw [BitVec.and_comm z x, he] at hh
    have hpair := hp x hx
    simp_all
  · intro x hx ha he
    have hh := masked_of_possible_t2 hz' (~~~x)
    have he' : z &&& ~~~x = target_t2 &&& ~~~x := by
      rw [← he]
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simp
      cases x[i] <;> cases z[i] <;> rfl
    rw [he'] at hh
    have hpair := hp x hx
    simp_all

private def search_t2 : ℕ → List T_t2 → Bool
  | 0, ws => fastTwo_t2 ws
  | n+1, ws => (choices_t2 ws).all (fun z => search_t2 n (z :: ws))

private theorem search_safe_t2 {n : ℕ} {ws : List T_t2} (h : search_t2 n ws) : safe_t2 (n + 2) ws := by
  induction n generalizing ws with
  | zero => exact lastTwo_safe_t2 (fast_implies_last_t2 h)
  | succ n ih =>
    intro z hz
    exact ih ((List.all_eq_true.mp h) z ((choice_iff_t2 _ _).2 hz))

set_option maxRecDepth 100000 in
private theorem top_safe_t2 : safe_t2 0 ins_t2 := by
  show ins_t2.contains target_t2 = false
  decide +kernel

private def graph_t2 (x : Fin 5 → Bool) : Bool :=
  Nat.testBit 0x88888888 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

private def assignment_t2 (k : Fin 32) (i : Fin 5) := bit_t2 k (ins_t2.getD i.val 0)

private theorem lower_t2 (s : ℕ) (h : HasCircuitSize 5 graph_t2 s) : 1 ≤ s := by
  by_contra! hs
  obtain ⟨C, hg, hsize, he⟩ := h
  have hlen : C.gates.length ≤ 0 := by change C.gates.length ≤ s at hsize; omega
  apply exclude_t2 C.gates C.output hg ins_t2 ins_t2 (fun ⦃_⦄ h => h) 0 hlen top_safe_t2
  intro k
  have hi : ∀ t, List.ofFn (assignment_t2 t) = ins_t2.map (bit_t2 t) := by decide
  have ht : ∀ t, graph_t2 (assignment_t2 t) = bit_t2 t target_t2 := by decide +kernel
  unfold step_t2
  simpa only [Circuit.eval, Circuit.wires, hi, ht] using he (assignment_t2 k)

private def upperC_t2 : Circuit :=
  { gates := [{ op := GateOp.and, inputs := [0, 1] }],
    output := 5 }

private theorem upper_mono_t2 : Monotone2 upperC_t2 := by
  intro g hg
  simp only [upperC_t2, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl <;> simp

private theorem upper_eval_t2 : ∀ x : Fin 5 → Bool, upperC_t2.eval (List.ofFn x) = graph_t2 x := by
  decide +kernel

private theorem main_t2 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => Nat.testBit 0x88888888 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit 0x88888888 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) :=
  fun s h => ⟨upperC_t2, upper_mono_t2, le_trans (by decide : upperC_t2.size ≤ 1) (lower_t2 s h), upper_eval_t2⟩


private abbrev T_t3 := BitVec 32
private def ins_t3 : List T_t3 := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]
private def target_t3 : T_t3 := 0xeeeeeeee
private def possible_t3 (w : List T_t3) (z : T_t3) : Bool :=
  z == 0 || z == (-1) || w.any (fun u => z == u || z == ~~~u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit_t3 (k : Fin 32) (z : T_t3) := z[k.val]

private theorem read_bit_t3 (w : List T_t3) (i : ℕ) (k : Fin 32) :
    (w.map (bit_t3 k)).getD i false = bit_t3 k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit_t3]

private theorem read_wire_t3 (w : List T_t3) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

private theorem atom_t3 {ws : List T_t3} {x : T_t3} (hx : x = 0 ∨ x ∈ ws) :
    possible_t3 ws x ∧ possible_t3 ws (~~~x) := by
  rcases hx with rfl | hx
  · simp [possible_t3]
  · simp only [possible_t3, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    grind

private theorem pair_t3 {ws : List T_t3} {x y : T_t3} (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
    possible_t3 ws (x &&& y) ∧ possible_t3 ws (x ||| y) := by
  rcases hx with rfl | hx
  · simpa [possible_t3] using (show possible_t3 ws 0 ∧ possible_t3 ws y from ⟨by simp [possible_t3], (atom_t3 hy).1⟩)
  rcases hy with rfl | hy
  · simpa [possible_t3] using (show possible_t3 ws 0 ∧ possible_t3 ws x from ⟨by simp [possible_t3], (atom_t3 (.inr hx)).1⟩)
  · simp only [possible_t3, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    constructor
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inl rfl⟩⟩
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inr rfl⟩⟩

private def step_t3 (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def legal_t3 (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private theorem gate_table_t3 (w ws : List T_t3) (hw : w ⊆ ws) (g : Gate) (hg : legal_t3 g) :
    ∃ z, possible_t3 ws z ∧ ∀ k, step_t3 (w.map (bit_t3 k)) g = (w ++ [z]).map (bit_t3 k) := by
  have mem (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ ws := (read_wire_t3 w i).imp_right (fun h => hw h)
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl | rfl
    · exact ⟨-1, by simp [possible_t3], by simp [step_t3, GateOp.eval, bit_t3]; decide⟩
    · exact ⟨0, by simp [possible_t3], by simp [step_t3, GateOp.eval, bit_t3]⟩
    · exact ⟨-1, by simp [possible_t3], by simp [step_t3, GateOp.eval, bit_t3]; decide⟩
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl | rfl
      · exact ⟨_, (atom_t3 (mem i)).1, by simp only [step_t3, List.map_cons, List.map_nil, read_bit_t3]; simp [GateOp.eval]⟩
      · exact ⟨_, (atom_t3 (mem i)).1, by simp only [step_t3, List.map_cons, List.map_nil, read_bit_t3]; simp [GateOp.eval]⟩
      · exact ⟨_, (atom_t3 (mem i)).2, by simp only [step_t3, List.map_cons, List.map_nil, read_bit_t3]; simp [GateOp.eval, bit_t3]⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl | rfl
        · exact ⟨_, (pair_t3 (mem i) (mem j)).1, by simp only [step_t3, List.map_cons, List.map_nil, read_bit_t3]; simp [GateOp.eval, bit_t3]⟩
        · exact ⟨_, (pair_t3 (mem i) (mem j)).2, by simp only [step_t3, List.map_cons, List.map_nil, read_bit_t3]; simp [GateOp.eval, bit_t3]⟩
        · exact ⟨_, (atom_t3 (mem i)).2, by simp only [step_t3, List.map_cons, List.map_nil, read_bit_t3]; simp [GateOp.eval, bit_t3]⟩

private def safe_t3 : ℕ → List T_t3 → Prop
  | 0, ws => ws.contains target_t3 = false
  | n + 1, ws => ∀ z, possible_t3 ws z → safe_t3 n (z :: ws)

private theorem absent_t3 {n : ℕ} {ws : List T_t3} (h : safe_t3 n ws) : target_t3 ∉ ws := by
  induction n generalizing ws with
  | zero => simpa [safe_t3] using h
  | succ n ih =>
    have ht := ih (h 0 (by simp [possible_t3]))
    exact fun hm => ht (List.mem_cons_of_mem _ hm)

private theorem exclude_t3 (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal_t3 g)
    (w ws : List T_t3) (hw : w ⊆ ws) (m : ℕ) (hm : gs.length ≤ m) (hs : safe_t3 m ws)
    (he : ∀ k, (gs.foldl step_t3 (w.map (bit_t3 k))).getD out false = bit_t3 k target_t3) : False := by
  induction gs generalizing w ws m with
  | nil =>
    have hval : w.getD out 0 = target_t3 := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit_t3, bit_t3] using he ⟨i, hi⟩
    have hr := read_wire_t3 w out
    rw [hval] at hr
    rcases hr with hz | ht
    · exact (by decide : target_t3 ≠ 0) hz
    · exact absent_t3 hs (hw ht)
  | cons g gs ih =>
    cases m with
    | zero => simp at hm
    | succ m =>
      obtain ⟨z, hz, hstep⟩ := gate_table_t3 w ws hw g (hg g (by simp))
      apply ih (fun g' hg' => hg g' (by simp [hg'])) (w ++ [z]) (z :: ws) _ m
        (by simpa using hm) (hs z hz)
      · intro k
        simpa only [List.foldl_cons, hstep] using he k
      · intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact List.mem_cons_of_mem _ (hw hx)
        · simp

private def choices_t3 (ws : List T_t3) : List T_t3 :=
  (0 :: -1 :: ws.flatMap (fun x => x :: ~~~x :: ws.flatMap (fun y => [x &&& y, x ||| y]))).eraseDups

private theorem choice_iff_t3 (ws : List T_t3) (z : T_t3) : z ∈ choices_t3 ws ↔ possible_t3 ws z := by
  simp [choices_t3, possible_t3, List.any_eq_true]
  grind

-- With two gates left, only an existing wire containing every true bit_t3 of
-- the target_t3 can serve as the other input to an AND. OR has the dual test.
private def lastTwo_t3 (ws : List T_t3) : Bool :=
  let above := ws.filter (fun x => (x &&& target_t3) == target_t3)
  let below := ws.filter (fun x => (x ||| target_t3) == target_t3)
  (choices_t3 ws).all fun z => !(z == target_t3 || ~~~z == target_t3 ||
    above.any (fun x => (x &&& z) == target_t3) ||
    below.any (fun x => (x ||| z) == target_t3))

private theorem lastTwo_safe_t3 {ws : List T_t3} (h : lastTwo_t3 ws) : safe_t3 2 ws := by
  intro z hz v hv
  have hz' := (choice_iff_t3 ws z).2 hz
  have ht (u : T_t3) (hu : u ∈ choices_t3 ws) := (List.all_eq_true.mp h) u hu
  have hnot (u : T_t3) (hu : u ∈ choices_t3 ws) : u ≠ target_t3 ∧ ~~~u ≠ target_t3 ∧
      (∀ x ∈ ws, x &&& u ≠ target_t3) ∧ (∀ x ∈ ws, x ||| u ≠ target_t3) := by
    have H := ht u hu
    simp at H
    obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := H
    refine ⟨h1,h2,?_,?_⟩
    · intro x hx he
      apply h3 x hx _ he
      rw [← he, ← BitVec.and_assoc, BitVec.and_self]
    · intro x hx he
      apply h4 x hx _ he
      rw [← he, ← BitVec.or_assoc, BitVec.or_self]
  have H := hnot z hz'
  have base (x : T_t3) (hx : x ∈ ws) := hnot x ((choice_iff_t3 ws x).2 (atom_t3 (.inr hx)).1)
  have unary (x : T_t3) (hx : x ∈ z :: ws) : x ≠ target_t3 ∧ ~~~x ≠ target_t3 := by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨H.1, H.2.1⟩
    · exact ⟨(base x hx).1, (base x hx).2.1⟩
  have binary (x y : T_t3) (hx : x ∈ z :: ws) (hy : y ∈ z :: ws) :
      x &&& y ≠ target_t3 ∧ x ||| y ≠ target_t3 := by
    rcases List.mem_cons.mp hx with hxe | hxm <;> rcases List.mem_cons.mp hy with hye | hym
    · simpa [hxe, hye] using H.1
    · simpa [hxe, BitVec.and_comm, BitVec.or_comm] using And.intro (H.2.2.1 y hym) (H.2.2.2 y hym)
    · simpa [hye] using And.intro (H.2.2.1 x hxm) (H.2.2.2 x hxm)
    · exact ⟨(base y hym).2.2.1 x hxm, (base y hym).2.2.2 x hxm⟩
  have hv' : v ≠ target_t3 := by
    simp only [possible_t3, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hv
    rcases hv with ((h | h) | ⟨x, hx, ((h | h) | ⟨y, hy, h | h⟩)⟩) <;> subst v
    · decide
    · decide
    · exact (unary x hx).1
    · exact (unary x hx).2
    · exact (binary x y hx hy).1
    · exact (binary x y hx hy).2
  change (v :: z :: ws).contains target_t3 = false
  suffices target_t3 ∉ v :: z :: ws by simpa using this
  intro hm
  rcases List.mem_cons.mp hm with he | hm
  · exact hv' he.symm
  · exact (unary target_t3 hm).1 rfl

private def masked_t3 (ws : List T_t3) (mask want : T_t3) : Bool :=
  let xs := ws.map (fun x => x &&& mask)
  want == 0 || want == mask || xs.any fun x =>
    x == want || (~~~x &&& mask) == want ||
    ((x &&& want) == want && xs.any (fun y => (x &&& y) == want)) ||
    ((x ||| want) == want && xs.any (fun y => (x ||| y) == want))

private def fastTwo_t3 (ws : List T_t3) : Bool :=
  !(masked_t3 ws (-1) target_t3 || masked_t3 ws (-1) (~~~target_t3) ||
    ws.any fun x =>
      ((x &&& target_t3) == target_t3 && masked_t3 ws x target_t3) ||
      ((x ||| target_t3) == target_t3 && masked_t3 ws (~~~x) (target_t3 &&& ~~~x)))

private theorem masked_of_possible_t3 {ws : List T_t3} {u : T_t3} (hu : possible_t3 ws u) (m : T_t3) :
    masked_t3 ws m (u &&& m) := by
  let xs := ws.map (fun x => x &&& m)
  have mem (x : T_t3) (hx : x ∈ ws) : x &&& m ∈ xs := List.mem_map.mpr ⟨x, hx, rfl⟩
  simp only [masked_t3, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.any_eq_true]
  simp only [possible_t3, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hu
  rcases hu with ((h | h) | ⟨x, hx, ((h | h) | ⟨y, hy, h | h⟩)⟩) <;> subst u
  · exact .inl (.inl (by simp))
  · exact .inl (.inr BitVec.allOnes_and)
  · exact .inr ⟨_, mem x hx, .inl (.inl (.inl rfl))⟩
  · refine .inr ⟨_, mem x hx, .inl (.inl (.inr ?_))⟩
    apply BitVec.eq_of_getElem_eq
    intro i hi
    simp
    cases x[i] <;> cases m[i] <;> rfl
  · refine .inr ⟨_, mem x hx, .inl (.inr ⟨?_, _, mem y hy, ?_⟩)⟩ <;>
      apply BitVec.eq_of_getElem_eq <;> intro i hi <;> simp only [BitVec.getElem_and] <;>
      cases x[i] <;> cases y[i] <;> cases m[i] <;> decide
  · refine .inr ⟨_, mem x hx, .inr ⟨?_, _, mem y hy, ?_⟩⟩ <;>
      apply BitVec.eq_of_getElem_eq <;> intro i hi <;> simp only [BitVec.getElem_and, BitVec.getElem_or] <;>
      cases x[i] <;> cases y[i] <;> cases m[i] <;> decide

private theorem fast_implies_last_t3 {ws : List T_t3} (hf : fastTwo_t3 ws) : lastTwo_t3 ws := by
  simp [fastTwo_t3] at hf
  obtain ⟨⟨hn, hc⟩, hp⟩ := hf
  apply List.all_eq_true.mpr
  intro z hz
  have hz' := (choice_iff_t3 _ _).1 hz
  simp
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro he
    have hh := masked_of_possible_t3 hz' (-1)
    rw [show z &&& (-1 : T_t3) = z from BitVec.and_allOnes, he] at hh
    simp_all
  · intro he
    have hh := masked_of_possible_t3 hz' (-1)
    have he' : z = ~~~target_t3 := by rw [← he, BitVec.not_not]
    rw [show z &&& (-1 : T_t3) = z from BitVec.and_allOnes, he'] at hh
    simp_all
  · intro x hx ha he
    have hh := masked_of_possible_t3 hz' x
    rw [BitVec.and_comm z x, he] at hh
    have hpair := hp x hx
    simp_all
  · intro x hx ha he
    have hh := masked_of_possible_t3 hz' (~~~x)
    have he' : z &&& ~~~x = target_t3 &&& ~~~x := by
      rw [← he]
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simp
      cases x[i] <;> cases z[i] <;> rfl
    rw [he'] at hh
    have hpair := hp x hx
    simp_all

private def search_t3 : ℕ → List T_t3 → Bool
  | 0, ws => fastTwo_t3 ws
  | n+1, ws => (choices_t3 ws).all (fun z => search_t3 n (z :: ws))

private theorem search_safe_t3 {n : ℕ} {ws : List T_t3} (h : search_t3 n ws) : safe_t3 (n + 2) ws := by
  induction n generalizing ws with
  | zero => exact lastTwo_safe_t3 (fast_implies_last_t3 h)
  | succ n ih =>
    intro z hz
    exact ih ((List.all_eq_true.mp h) z ((choice_iff_t3 _ _).2 hz))

set_option maxRecDepth 100000 in
private theorem top_safe_t3 : safe_t3 0 ins_t3 := by
  show ins_t3.contains target_t3 = false
  decide +kernel

private def graph_t3 (x : Fin 5 → Bool) : Bool :=
  Nat.testBit 0xeeeeeeee (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

private def assignment_t3 (k : Fin 32) (i : Fin 5) := bit_t3 k (ins_t3.getD i.val 0)

private theorem lower_t3 (s : ℕ) (h : HasCircuitSize 5 graph_t3 s) : 1 ≤ s := by
  by_contra! hs
  obtain ⟨C, hg, hsize, he⟩ := h
  have hlen : C.gates.length ≤ 0 := by change C.gates.length ≤ s at hsize; omega
  apply exclude_t3 C.gates C.output hg ins_t3 ins_t3 (fun ⦃_⦄ h => h) 0 hlen top_safe_t3
  intro k
  have hi : ∀ t, List.ofFn (assignment_t3 t) = ins_t3.map (bit_t3 t) := by decide
  have ht : ∀ t, graph_t3 (assignment_t3 t) = bit_t3 t target_t3 := by decide +kernel
  unfold step_t3
  simpa only [Circuit.eval, Circuit.wires, hi, ht] using he (assignment_t3 k)

private def upperC_t3 : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [0, 1] }],
    output := 5 }

private theorem upper_mono_t3 : Monotone2 upperC_t3 := by
  intro g hg
  simp only [upperC_t3, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl <;> simp

private theorem upper_eval_t3 : ∀ x : Fin 5 → Bool, upperC_t3.eval (List.ofFn x) = graph_t3 x := by
  decide +kernel

private theorem main_t3 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => Nat.testBit 0xeeeeeeee (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit 0xeeeeeeee (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) :=
  fun s h => ⟨upperC_t3, upper_mono_t3, le_trans (by decide : upperC_t3.size ≤ 1) (lower_t3 s h), upper_eval_t3⟩

private def graph_t4 (x : Fin 5 → Bool) : Bool :=
  Nat.testBit 0xffffffff (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

private theorem evalnil_t4 (o : ℕ) : Circuit.eval ⟨[], o⟩ (List.ofFn (fun _ : Fin 5 => false)) = false := by
  simp only [Circuit.eval, Circuit.wires, List.foldl_nil]
  rcases o with _ | _ | _ | _ | _ | _ <;> simp

private theorem lower_t4 (s : ℕ) (h : HasCircuitSize 5 graph_t4 s) : 1 ≤ s := by
  by_contra! hs
  obtain ⟨C, hg, hsize, he⟩ := h
  have hlen : C.gates.length = 0 := by change C.gates.length ≤ s at hsize; omega
  have h0 := he (fun _ => false)
  obtain ⟨gs, o⟩ := C
  have hnil : gs = [] := List.length_eq_zero_iff.mp hlen
  subst hnil
  rw [evalnil_t4 o] at h0
  revert h0
  decide +kernel

private def upperC_t4 : Circuit :=
  { gates := [{ op := GateOp.and, inputs := [] }],
    output := 5 }

private theorem upper_mono_t4 : Monotone2 upperC_t4 := by
  intro g hg
  simp only [upperC_t4, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl <;> simp

private theorem upper_eval_t4 : ∀ x : Fin 5 → Bool, upperC_t4.eval (List.ofFn x) = graph_t4 x := by
  decide +kernel

private theorem main_t4 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => Nat.testBit 0xffffffff (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit 0xffffffff (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) :=
  fun s h => ⟨upperC_t4, upper_mono_t4, le_trans (by decide : upperC_t4.size ≤ 1) (lower_t4 s h), upper_eval_t4⟩


private abbrev T_t5 := BitVec 32
private def ins_t5 : List T_t5 := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]
private def target_t5 : T_t5 := 0x80808080
private def possible_t5 (w : List T_t5) (z : T_t5) : Bool :=
  z == 0 || z == (-1) || w.any (fun u => z == u || z == ~~~u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit_t5 (k : Fin 32) (z : T_t5) := z[k.val]

private theorem read_bit_t5 (w : List T_t5) (i : ℕ) (k : Fin 32) :
    (w.map (bit_t5 k)).getD i false = bit_t5 k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit_t5]

private theorem read_wire_t5 (w : List T_t5) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

private theorem atom_t5 {ws : List T_t5} {x : T_t5} (hx : x = 0 ∨ x ∈ ws) :
    possible_t5 ws x ∧ possible_t5 ws (~~~x) := by
  rcases hx with rfl | hx
  · simp [possible_t5]
  · simp only [possible_t5, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    grind

private theorem pair_t5 {ws : List T_t5} {x y : T_t5} (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
    possible_t5 ws (x &&& y) ∧ possible_t5 ws (x ||| y) := by
  rcases hx with rfl | hx
  · simpa [possible_t5] using (show possible_t5 ws 0 ∧ possible_t5 ws y from ⟨by simp [possible_t5], (atom_t5 hy).1⟩)
  rcases hy with rfl | hy
  · simpa [possible_t5] using (show possible_t5 ws 0 ∧ possible_t5 ws x from ⟨by simp [possible_t5], (atom_t5 (.inr hx)).1⟩)
  · simp only [possible_t5, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    constructor
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inl rfl⟩⟩
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inr rfl⟩⟩

private def step_t5 (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def legal_t5 (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private theorem gate_table_t5 (w ws : List T_t5) (hw : w ⊆ ws) (g : Gate) (hg : legal_t5 g) :
    ∃ z, possible_t5 ws z ∧ ∀ k, step_t5 (w.map (bit_t5 k)) g = (w ++ [z]).map (bit_t5 k) := by
  have mem (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ ws := (read_wire_t5 w i).imp_right (fun h => hw h)
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl | rfl
    · exact ⟨-1, by simp [possible_t5], by simp [step_t5, GateOp.eval, bit_t5]; decide⟩
    · exact ⟨0, by simp [possible_t5], by simp [step_t5, GateOp.eval, bit_t5]⟩
    · exact ⟨-1, by simp [possible_t5], by simp [step_t5, GateOp.eval, bit_t5]; decide⟩
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl | rfl
      · exact ⟨_, (atom_t5 (mem i)).1, by simp only [step_t5, List.map_cons, List.map_nil, read_bit_t5]; simp [GateOp.eval]⟩
      · exact ⟨_, (atom_t5 (mem i)).1, by simp only [step_t5, List.map_cons, List.map_nil, read_bit_t5]; simp [GateOp.eval]⟩
      · exact ⟨_, (atom_t5 (mem i)).2, by simp only [step_t5, List.map_cons, List.map_nil, read_bit_t5]; simp [GateOp.eval, bit_t5]⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl | rfl
        · exact ⟨_, (pair_t5 (mem i) (mem j)).1, by simp only [step_t5, List.map_cons, List.map_nil, read_bit_t5]; simp [GateOp.eval, bit_t5]⟩
        · exact ⟨_, (pair_t5 (mem i) (mem j)).2, by simp only [step_t5, List.map_cons, List.map_nil, read_bit_t5]; simp [GateOp.eval, bit_t5]⟩
        · exact ⟨_, (atom_t5 (mem i)).2, by simp only [step_t5, List.map_cons, List.map_nil, read_bit_t5]; simp [GateOp.eval, bit_t5]⟩

private def safe_t5 : ℕ → List T_t5 → Prop
  | 0, ws => ws.contains target_t5 = false
  | n + 1, ws => ∀ z, possible_t5 ws z → safe_t5 n (z :: ws)

private theorem absent_t5 {n : ℕ} {ws : List T_t5} (h : safe_t5 n ws) : target_t5 ∉ ws := by
  induction n generalizing ws with
  | zero => simpa [safe_t5] using h
  | succ n ih =>
    have ht := ih (h 0 (by simp [possible_t5]))
    exact fun hm => ht (List.mem_cons_of_mem _ hm)

private theorem exclude_t5 (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal_t5 g)
    (w ws : List T_t5) (hw : w ⊆ ws) (m : ℕ) (hm : gs.length ≤ m) (hs : safe_t5 m ws)
    (he : ∀ k, (gs.foldl step_t5 (w.map (bit_t5 k))).getD out false = bit_t5 k target_t5) : False := by
  induction gs generalizing w ws m with
  | nil =>
    have hval : w.getD out 0 = target_t5 := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit_t5, bit_t5] using he ⟨i, hi⟩
    have hr := read_wire_t5 w out
    rw [hval] at hr
    rcases hr with hz | ht
    · exact (by decide : target_t5 ≠ 0) hz
    · exact absent_t5 hs (hw ht)
  | cons g gs ih =>
    cases m with
    | zero => simp at hm
    | succ m =>
      obtain ⟨z, hz, hstep⟩ := gate_table_t5 w ws hw g (hg g (by simp))
      apply ih (fun g' hg' => hg g' (by simp [hg'])) (w ++ [z]) (z :: ws) _ m
        (by simpa using hm) (hs z hz)
      · intro k
        simpa only [List.foldl_cons, hstep] using he k
      · intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact List.mem_cons_of_mem _ (hw hx)
        · simp

private def choices_t5 (ws : List T_t5) : List T_t5 :=
  (0 :: -1 :: ws.flatMap (fun x => x :: ~~~x :: ws.flatMap (fun y => [x &&& y, x ||| y]))).eraseDups

private theorem choice_iff_t5 (ws : List T_t5) (z : T_t5) : z ∈ choices_t5 ws ↔ possible_t5 ws z := by
  simp [choices_t5, possible_t5, List.any_eq_true]
  grind

-- With two gates left, only an existing wire containing every true bit_t5 of
-- the target_t5 can serve as the other input to an AND. OR has the dual test.
private def lastTwo_t5 (ws : List T_t5) : Bool :=
  let above := ws.filter (fun x => (x &&& target_t5) == target_t5)
  let below := ws.filter (fun x => (x ||| target_t5) == target_t5)
  (choices_t5 ws).all fun z => !(z == target_t5 || ~~~z == target_t5 ||
    above.any (fun x => (x &&& z) == target_t5) ||
    below.any (fun x => (x ||| z) == target_t5))

private theorem lastTwo_safe_t5 {ws : List T_t5} (h : lastTwo_t5 ws) : safe_t5 2 ws := by
  intro z hz v hv
  have hz' := (choice_iff_t5 ws z).2 hz
  have ht (u : T_t5) (hu : u ∈ choices_t5 ws) := (List.all_eq_true.mp h) u hu
  have hnot (u : T_t5) (hu : u ∈ choices_t5 ws) : u ≠ target_t5 ∧ ~~~u ≠ target_t5 ∧
      (∀ x ∈ ws, x &&& u ≠ target_t5) ∧ (∀ x ∈ ws, x ||| u ≠ target_t5) := by
    have H := ht u hu
    simp at H
    obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := H
    refine ⟨h1,h2,?_,?_⟩
    · intro x hx he
      apply h3 x hx _ he
      rw [← he, ← BitVec.and_assoc, BitVec.and_self]
    · intro x hx he
      apply h4 x hx _ he
      rw [← he, ← BitVec.or_assoc, BitVec.or_self]
  have H := hnot z hz'
  have base (x : T_t5) (hx : x ∈ ws) := hnot x ((choice_iff_t5 ws x).2 (atom_t5 (.inr hx)).1)
  have unary (x : T_t5) (hx : x ∈ z :: ws) : x ≠ target_t5 ∧ ~~~x ≠ target_t5 := by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨H.1, H.2.1⟩
    · exact ⟨(base x hx).1, (base x hx).2.1⟩
  have binary (x y : T_t5) (hx : x ∈ z :: ws) (hy : y ∈ z :: ws) :
      x &&& y ≠ target_t5 ∧ x ||| y ≠ target_t5 := by
    rcases List.mem_cons.mp hx with hxe | hxm <;> rcases List.mem_cons.mp hy with hye | hym
    · simpa [hxe, hye] using H.1
    · simpa [hxe, BitVec.and_comm, BitVec.or_comm] using And.intro (H.2.2.1 y hym) (H.2.2.2 y hym)
    · simpa [hye] using And.intro (H.2.2.1 x hxm) (H.2.2.2 x hxm)
    · exact ⟨(base y hym).2.2.1 x hxm, (base y hym).2.2.2 x hxm⟩
  have hv' : v ≠ target_t5 := by
    simp only [possible_t5, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hv
    rcases hv with ((h | h) | ⟨x, hx, ((h | h) | ⟨y, hy, h | h⟩)⟩) <;> subst v
    · decide
    · decide
    · exact (unary x hx).1
    · exact (unary x hx).2
    · exact (binary x y hx hy).1
    · exact (binary x y hx hy).2
  change (v :: z :: ws).contains target_t5 = false
  suffices target_t5 ∉ v :: z :: ws by simpa using this
  intro hm
  rcases List.mem_cons.mp hm with he | hm
  · exact hv' he.symm
  · exact (unary target_t5 hm).1 rfl

private def masked_t5 (ws : List T_t5) (mask want : T_t5) : Bool :=
  let xs := ws.map (fun x => x &&& mask)
  want == 0 || want == mask || xs.any fun x =>
    x == want || (~~~x &&& mask) == want ||
    ((x &&& want) == want && xs.any (fun y => (x &&& y) == want)) ||
    ((x ||| want) == want && xs.any (fun y => (x ||| y) == want))

private def fastTwo_t5 (ws : List T_t5) : Bool :=
  !(masked_t5 ws (-1) target_t5 || masked_t5 ws (-1) (~~~target_t5) ||
    ws.any fun x =>
      ((x &&& target_t5) == target_t5 && masked_t5 ws x target_t5) ||
      ((x ||| target_t5) == target_t5 && masked_t5 ws (~~~x) (target_t5 &&& ~~~x)))

private theorem masked_of_possible_t5 {ws : List T_t5} {u : T_t5} (hu : possible_t5 ws u) (m : T_t5) :
    masked_t5 ws m (u &&& m) := by
  let xs := ws.map (fun x => x &&& m)
  have mem (x : T_t5) (hx : x ∈ ws) : x &&& m ∈ xs := List.mem_map.mpr ⟨x, hx, rfl⟩
  simp only [masked_t5, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.any_eq_true]
  simp only [possible_t5, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hu
  rcases hu with ((h | h) | ⟨x, hx, ((h | h) | ⟨y, hy, h | h⟩)⟩) <;> subst u
  · exact .inl (.inl (by simp))
  · exact .inl (.inr BitVec.allOnes_and)
  · exact .inr ⟨_, mem x hx, .inl (.inl (.inl rfl))⟩
  · refine .inr ⟨_, mem x hx, .inl (.inl (.inr ?_))⟩
    apply BitVec.eq_of_getElem_eq
    intro i hi
    simp
    cases x[i] <;> cases m[i] <;> rfl
  · refine .inr ⟨_, mem x hx, .inl (.inr ⟨?_, _, mem y hy, ?_⟩)⟩ <;>
      apply BitVec.eq_of_getElem_eq <;> intro i hi <;> simp only [BitVec.getElem_and] <;>
      cases x[i] <;> cases y[i] <;> cases m[i] <;> decide
  · refine .inr ⟨_, mem x hx, .inr ⟨?_, _, mem y hy, ?_⟩⟩ <;>
      apply BitVec.eq_of_getElem_eq <;> intro i hi <;> simp only [BitVec.getElem_and, BitVec.getElem_or] <;>
      cases x[i] <;> cases y[i] <;> cases m[i] <;> decide

private theorem fast_implies_last_t5 {ws : List T_t5} (hf : fastTwo_t5 ws) : lastTwo_t5 ws := by
  simp [fastTwo_t5] at hf
  obtain ⟨⟨hn, hc⟩, hp⟩ := hf
  apply List.all_eq_true.mpr
  intro z hz
  have hz' := (choice_iff_t5 _ _).1 hz
  simp
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro he
    have hh := masked_of_possible_t5 hz' (-1)
    rw [show z &&& (-1 : T_t5) = z from BitVec.and_allOnes, he] at hh
    simp_all
  · intro he
    have hh := masked_of_possible_t5 hz' (-1)
    have he' : z = ~~~target_t5 := by rw [← he, BitVec.not_not]
    rw [show z &&& (-1 : T_t5) = z from BitVec.and_allOnes, he'] at hh
    simp_all
  · intro x hx ha he
    have hh := masked_of_possible_t5 hz' x
    rw [BitVec.and_comm z x, he] at hh
    have hpair := hp x hx
    simp_all
  · intro x hx ha he
    have hh := masked_of_possible_t5 hz' (~~~x)
    have he' : z &&& ~~~x = target_t5 &&& ~~~x := by
      rw [← he]
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simp
      cases x[i] <;> cases z[i] <;> rfl
    rw [he'] at hh
    have hpair := hp x hx
    simp_all

private def search_t5 : ℕ → List T_t5 → Bool
  | 0, ws => fastTwo_t5 ws
  | n+1, ws => (choices_t5 ws).all (fun z => search_t5 n (z :: ws))

private theorem search_safe_t5 {n : ℕ} {ws : List T_t5} (h : search_t5 n ws) : safe_t5 (n + 2) ws := by
  induction n generalizing ws with
  | zero => exact lastTwo_safe_t5 (fast_implies_last_t5 h)
  | succ n ih =>
    intro z hz
    exact ih ((List.all_eq_true.mp h) z ((choice_iff_t5 _ _).2 hz))

set_option maxRecDepth 100000 in
private theorem top_safe_t5 : safe_t5 1 ins_t5 := by
  have h : (choices_t5 ins_t5).all (fun z => !(z :: ins_t5).contains target_t5) = true := by decide +kernel
  intro z hz
  have := List.all_eq_true.mp h z ((choice_iff_t5 _ _).2 hz)
  simpa [safe_t5] using this

private def graph_t5 (x : Fin 5 → Bool) : Bool :=
  Nat.testBit 0x80808080 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

private def assignment_t5 (k : Fin 32) (i : Fin 5) := bit_t5 k (ins_t5.getD i.val 0)

private theorem lower_t5 (s : ℕ) (h : HasCircuitSize 5 graph_t5 s) : 2 ≤ s := by
  by_contra! hs
  obtain ⟨C, hg, hsize, he⟩ := h
  have hlen : C.gates.length ≤ 1 := by change C.gates.length ≤ s at hsize; omega
  apply exclude_t5 C.gates C.output hg ins_t5 ins_t5 (fun ⦃_⦄ h => h) 1 hlen top_safe_t5
  intro k
  have hi : ∀ t, List.ofFn (assignment_t5 t) = ins_t5.map (bit_t5 t) := by decide
  have ht : ∀ t, graph_t5 (assignment_t5 t) = bit_t5 t target_t5 := by decide +kernel
  unfold step_t5
  simpa only [Circuit.eval, Circuit.wires, hi, ht] using he (assignment_t5 k)

private def upperC_t5 : Circuit :=
  { gates := [{ op := GateOp.and, inputs := [0, 1] }, { op := GateOp.and, inputs := [2, 5] }],
    output := 6 }

private theorem upper_mono_t5 : Monotone2 upperC_t5 := by
  intro g hg
  simp only [upperC_t5, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl <;> simp

private theorem upper_eval_t5 : ∀ x : Fin 5 → Bool, upperC_t5.eval (List.ofFn x) = graph_t5 x := by
  decide +kernel

private theorem main_t5 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => Nat.testBit 0x80808080 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit 0x80808080 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) :=
  fun s h => ⟨upperC_t5, upper_mono_t5, le_trans (by decide : upperC_t5.size ≤ 2) (lower_t5 s h), upper_eval_t5⟩


private abbrev T_t6 := BitVec 32
private def ins_t6 : List T_t6 := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]
private def target_t6 : T_t6 := 0xa8a8a8a8
private def possible_t6 (w : List T_t6) (z : T_t6) : Bool :=
  z == 0 || z == (-1) || w.any (fun u => z == u || z == ~~~u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit_t6 (k : Fin 32) (z : T_t6) := z[k.val]

private theorem read_bit_t6 (w : List T_t6) (i : ℕ) (k : Fin 32) :
    (w.map (bit_t6 k)).getD i false = bit_t6 k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit_t6]

private theorem read_wire_t6 (w : List T_t6) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

private theorem atom_t6 {ws : List T_t6} {x : T_t6} (hx : x = 0 ∨ x ∈ ws) :
    possible_t6 ws x ∧ possible_t6 ws (~~~x) := by
  rcases hx with rfl | hx
  · simp [possible_t6]
  · simp only [possible_t6, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    grind

private theorem pair_t6 {ws : List T_t6} {x y : T_t6} (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
    possible_t6 ws (x &&& y) ∧ possible_t6 ws (x ||| y) := by
  rcases hx with rfl | hx
  · simpa [possible_t6] using (show possible_t6 ws 0 ∧ possible_t6 ws y from ⟨by simp [possible_t6], (atom_t6 hy).1⟩)
  rcases hy with rfl | hy
  · simpa [possible_t6] using (show possible_t6 ws 0 ∧ possible_t6 ws x from ⟨by simp [possible_t6], (atom_t6 (.inr hx)).1⟩)
  · simp only [possible_t6, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    constructor
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inl rfl⟩⟩
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inr rfl⟩⟩

private def step_t6 (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def legal_t6 (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private theorem gate_table_t6 (w ws : List T_t6) (hw : w ⊆ ws) (g : Gate) (hg : legal_t6 g) :
    ∃ z, possible_t6 ws z ∧ ∀ k, step_t6 (w.map (bit_t6 k)) g = (w ++ [z]).map (bit_t6 k) := by
  have mem (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ ws := (read_wire_t6 w i).imp_right (fun h => hw h)
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl | rfl
    · exact ⟨-1, by simp [possible_t6], by simp [step_t6, GateOp.eval, bit_t6]; decide⟩
    · exact ⟨0, by simp [possible_t6], by simp [step_t6, GateOp.eval, bit_t6]⟩
    · exact ⟨-1, by simp [possible_t6], by simp [step_t6, GateOp.eval, bit_t6]; decide⟩
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl | rfl
      · exact ⟨_, (atom_t6 (mem i)).1, by simp only [step_t6, List.map_cons, List.map_nil, read_bit_t6]; simp [GateOp.eval]⟩
      · exact ⟨_, (atom_t6 (mem i)).1, by simp only [step_t6, List.map_cons, List.map_nil, read_bit_t6]; simp [GateOp.eval]⟩
      · exact ⟨_, (atom_t6 (mem i)).2, by simp only [step_t6, List.map_cons, List.map_nil, read_bit_t6]; simp [GateOp.eval, bit_t6]⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl | rfl
        · exact ⟨_, (pair_t6 (mem i) (mem j)).1, by simp only [step_t6, List.map_cons, List.map_nil, read_bit_t6]; simp [GateOp.eval, bit_t6]⟩
        · exact ⟨_, (pair_t6 (mem i) (mem j)).2, by simp only [step_t6, List.map_cons, List.map_nil, read_bit_t6]; simp [GateOp.eval, bit_t6]⟩
        · exact ⟨_, (atom_t6 (mem i)).2, by simp only [step_t6, List.map_cons, List.map_nil, read_bit_t6]; simp [GateOp.eval, bit_t6]⟩

private def safe_t6 : ℕ → List T_t6 → Prop
  | 0, ws => ws.contains target_t6 = false
  | n + 1, ws => ∀ z, possible_t6 ws z → safe_t6 n (z :: ws)

private theorem absent_t6 {n : ℕ} {ws : List T_t6} (h : safe_t6 n ws) : target_t6 ∉ ws := by
  induction n generalizing ws with
  | zero => simpa [safe_t6] using h
  | succ n ih =>
    have ht := ih (h 0 (by simp [possible_t6]))
    exact fun hm => ht (List.mem_cons_of_mem _ hm)

private theorem exclude_t6 (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal_t6 g)
    (w ws : List T_t6) (hw : w ⊆ ws) (m : ℕ) (hm : gs.length ≤ m) (hs : safe_t6 m ws)
    (he : ∀ k, (gs.foldl step_t6 (w.map (bit_t6 k))).getD out false = bit_t6 k target_t6) : False := by
  induction gs generalizing w ws m with
  | nil =>
    have hval : w.getD out 0 = target_t6 := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit_t6, bit_t6] using he ⟨i, hi⟩
    have hr := read_wire_t6 w out
    rw [hval] at hr
    rcases hr with hz | ht
    · exact (by decide : target_t6 ≠ 0) hz
    · exact absent_t6 hs (hw ht)
  | cons g gs ih =>
    cases m with
    | zero => simp at hm
    | succ m =>
      obtain ⟨z, hz, hstep⟩ := gate_table_t6 w ws hw g (hg g (by simp))
      apply ih (fun g' hg' => hg g' (by simp [hg'])) (w ++ [z]) (z :: ws) _ m
        (by simpa using hm) (hs z hz)
      · intro k
        simpa only [List.foldl_cons, hstep] using he k
      · intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact List.mem_cons_of_mem _ (hw hx)
        · simp

private def choices_t6 (ws : List T_t6) : List T_t6 :=
  (0 :: -1 :: ws.flatMap (fun x => x :: ~~~x :: ws.flatMap (fun y => [x &&& y, x ||| y]))).eraseDups

private theorem choice_iff_t6 (ws : List T_t6) (z : T_t6) : z ∈ choices_t6 ws ↔ possible_t6 ws z := by
  simp [choices_t6, possible_t6, List.any_eq_true]
  grind

-- With two gates left, only an existing wire containing every true bit_t6 of
-- the target_t6 can serve as the other input to an AND. OR has the dual test.
private def lastTwo_t6 (ws : List T_t6) : Bool :=
  let above := ws.filter (fun x => (x &&& target_t6) == target_t6)
  let below := ws.filter (fun x => (x ||| target_t6) == target_t6)
  (choices_t6 ws).all fun z => !(z == target_t6 || ~~~z == target_t6 ||
    above.any (fun x => (x &&& z) == target_t6) ||
    below.any (fun x => (x ||| z) == target_t6))

private theorem lastTwo_safe_t6 {ws : List T_t6} (h : lastTwo_t6 ws) : safe_t6 2 ws := by
  intro z hz v hv
  have hz' := (choice_iff_t6 ws z).2 hz
  have ht (u : T_t6) (hu : u ∈ choices_t6 ws) := (List.all_eq_true.mp h) u hu
  have hnot (u : T_t6) (hu : u ∈ choices_t6 ws) : u ≠ target_t6 ∧ ~~~u ≠ target_t6 ∧
      (∀ x ∈ ws, x &&& u ≠ target_t6) ∧ (∀ x ∈ ws, x ||| u ≠ target_t6) := by
    have H := ht u hu
    simp at H
    obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := H
    refine ⟨h1,h2,?_,?_⟩
    · intro x hx he
      apply h3 x hx _ he
      rw [← he, ← BitVec.and_assoc, BitVec.and_self]
    · intro x hx he
      apply h4 x hx _ he
      rw [← he, ← BitVec.or_assoc, BitVec.or_self]
  have H := hnot z hz'
  have base (x : T_t6) (hx : x ∈ ws) := hnot x ((choice_iff_t6 ws x).2 (atom_t6 (.inr hx)).1)
  have unary (x : T_t6) (hx : x ∈ z :: ws) : x ≠ target_t6 ∧ ~~~x ≠ target_t6 := by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨H.1, H.2.1⟩
    · exact ⟨(base x hx).1, (base x hx).2.1⟩
  have binary (x y : T_t6) (hx : x ∈ z :: ws) (hy : y ∈ z :: ws) :
      x &&& y ≠ target_t6 ∧ x ||| y ≠ target_t6 := by
    rcases List.mem_cons.mp hx with hxe | hxm <;> rcases List.mem_cons.mp hy with hye | hym
    · simpa [hxe, hye] using H.1
    · simpa [hxe, BitVec.and_comm, BitVec.or_comm] using And.intro (H.2.2.1 y hym) (H.2.2.2 y hym)
    · simpa [hye] using And.intro (H.2.2.1 x hxm) (H.2.2.2 x hxm)
    · exact ⟨(base y hym).2.2.1 x hxm, (base y hym).2.2.2 x hxm⟩
  have hv' : v ≠ target_t6 := by
    simp only [possible_t6, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hv
    rcases hv with ((h | h) | ⟨x, hx, ((h | h) | ⟨y, hy, h | h⟩)⟩) <;> subst v
    · decide
    · decide
    · exact (unary x hx).1
    · exact (unary x hx).2
    · exact (binary x y hx hy).1
    · exact (binary x y hx hy).2
  change (v :: z :: ws).contains target_t6 = false
  suffices target_t6 ∉ v :: z :: ws by simpa using this
  intro hm
  rcases List.mem_cons.mp hm with he | hm
  · exact hv' he.symm
  · exact (unary target_t6 hm).1 rfl

private def masked_t6 (ws : List T_t6) (mask want : T_t6) : Bool :=
  let xs := ws.map (fun x => x &&& mask)
  want == 0 || want == mask || xs.any fun x =>
    x == want || (~~~x &&& mask) == want ||
    ((x &&& want) == want && xs.any (fun y => (x &&& y) == want)) ||
    ((x ||| want) == want && xs.any (fun y => (x ||| y) == want))

private def fastTwo_t6 (ws : List T_t6) : Bool :=
  !(masked_t6 ws (-1) target_t6 || masked_t6 ws (-1) (~~~target_t6) ||
    ws.any fun x =>
      ((x &&& target_t6) == target_t6 && masked_t6 ws x target_t6) ||
      ((x ||| target_t6) == target_t6 && masked_t6 ws (~~~x) (target_t6 &&& ~~~x)))

private theorem masked_of_possible_t6 {ws : List T_t6} {u : T_t6} (hu : possible_t6 ws u) (m : T_t6) :
    masked_t6 ws m (u &&& m) := by
  let xs := ws.map (fun x => x &&& m)
  have mem (x : T_t6) (hx : x ∈ ws) : x &&& m ∈ xs := List.mem_map.mpr ⟨x, hx, rfl⟩
  simp only [masked_t6, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.any_eq_true]
  simp only [possible_t6, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hu
  rcases hu with ((h | h) | ⟨x, hx, ((h | h) | ⟨y, hy, h | h⟩)⟩) <;> subst u
  · exact .inl (.inl (by simp))
  · exact .inl (.inr BitVec.allOnes_and)
  · exact .inr ⟨_, mem x hx, .inl (.inl (.inl rfl))⟩
  · refine .inr ⟨_, mem x hx, .inl (.inl (.inr ?_))⟩
    apply BitVec.eq_of_getElem_eq
    intro i hi
    simp
    cases x[i] <;> cases m[i] <;> rfl
  · refine .inr ⟨_, mem x hx, .inl (.inr ⟨?_, _, mem y hy, ?_⟩)⟩ <;>
      apply BitVec.eq_of_getElem_eq <;> intro i hi <;> simp only [BitVec.getElem_and] <;>
      cases x[i] <;> cases y[i] <;> cases m[i] <;> decide
  · refine .inr ⟨_, mem x hx, .inr ⟨?_, _, mem y hy, ?_⟩⟩ <;>
      apply BitVec.eq_of_getElem_eq <;> intro i hi <;> simp only [BitVec.getElem_and, BitVec.getElem_or] <;>
      cases x[i] <;> cases y[i] <;> cases m[i] <;> decide

private theorem fast_implies_last_t6 {ws : List T_t6} (hf : fastTwo_t6 ws) : lastTwo_t6 ws := by
  simp [fastTwo_t6] at hf
  obtain ⟨⟨hn, hc⟩, hp⟩ := hf
  apply List.all_eq_true.mpr
  intro z hz
  have hz' := (choice_iff_t6 _ _).1 hz
  simp
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro he
    have hh := masked_of_possible_t6 hz' (-1)
    rw [show z &&& (-1 : T_t6) = z from BitVec.and_allOnes, he] at hh
    simp_all
  · intro he
    have hh := masked_of_possible_t6 hz' (-1)
    have he' : z = ~~~target_t6 := by rw [← he, BitVec.not_not]
    rw [show z &&& (-1 : T_t6) = z from BitVec.and_allOnes, he'] at hh
    simp_all
  · intro x hx ha he
    have hh := masked_of_possible_t6 hz' x
    rw [BitVec.and_comm z x, he] at hh
    have hpair := hp x hx
    simp_all
  · intro x hx ha he
    have hh := masked_of_possible_t6 hz' (~~~x)
    have he' : z &&& ~~~x = target_t6 &&& ~~~x := by
      rw [← he]
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simp
      cases x[i] <;> cases z[i] <;> rfl
    rw [he'] at hh
    have hpair := hp x hx
    simp_all

private def search_t6 : ℕ → List T_t6 → Bool
  | 0, ws => fastTwo_t6 ws
  | n+1, ws => (choices_t6 ws).all (fun z => search_t6 n (z :: ws))

private theorem search_safe_t6 {n : ℕ} {ws : List T_t6} (h : search_t6 n ws) : safe_t6 (n + 2) ws := by
  induction n generalizing ws with
  | zero => exact lastTwo_safe_t6 (fast_implies_last_t6 h)
  | succ n ih =>
    intro z hz
    exact ih ((List.all_eq_true.mp h) z ((choice_iff_t6 _ _).2 hz))

set_option maxRecDepth 100000 in
private theorem top_safe_t6 : safe_t6 1 ins_t6 := by
  have h : (choices_t6 ins_t6).all (fun z => !(z :: ins_t6).contains target_t6) = true := by decide +kernel
  intro z hz
  have := List.all_eq_true.mp h z ((choice_iff_t6 _ _).2 hz)
  simpa [safe_t6] using this

private def graph_t6 (x : Fin 5 → Bool) : Bool :=
  Nat.testBit 0xa8a8a8a8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

private def assignment_t6 (k : Fin 32) (i : Fin 5) := bit_t6 k (ins_t6.getD i.val 0)

private theorem lower_t6 (s : ℕ) (h : HasCircuitSize 5 graph_t6 s) : 2 ≤ s := by
  by_contra! hs
  obtain ⟨C, hg, hsize, he⟩ := h
  have hlen : C.gates.length ≤ 1 := by change C.gates.length ≤ s at hsize; omega
  apply exclude_t6 C.gates C.output hg ins_t6 ins_t6 (fun ⦃_⦄ h => h) 1 hlen top_safe_t6
  intro k
  have hi : ∀ t, List.ofFn (assignment_t6 t) = ins_t6.map (bit_t6 t) := by decide
  have ht : ∀ t, graph_t6 (assignment_t6 t) = bit_t6 t target_t6 := by decide +kernel
  unfold step_t6
  simpa only [Circuit.eval, Circuit.wires, hi, ht] using he (assignment_t6 k)

private def upperC_t6 : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.and, inputs := [0, 5] }],
    output := 6 }

private theorem upper_mono_t6 : Monotone2 upperC_t6 := by
  intro g hg
  simp only [upperC_t6, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl <;> simp

private theorem upper_eval_t6 : ∀ x : Fin 5 → Bool, upperC_t6.eval (List.ofFn x) = graph_t6 x := by
  decide +kernel

private theorem main_t6 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => Nat.testBit 0xa8a8a8a8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit 0xa8a8a8a8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) :=
  fun s h => ⟨upperC_t6, upper_mono_t6, le_trans (by decide : upperC_t6.size ≤ 2) (lower_t6 s h), upper_eval_t6⟩


private abbrev T_t7 := BitVec 32
private def ins_t7 : List T_t7 := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]
private def target_t7 : T_t7 := 0xeaeaeaea
private def possible_t7 (w : List T_t7) (z : T_t7) : Bool :=
  z == 0 || z == (-1) || w.any (fun u => z == u || z == ~~~u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit_t7 (k : Fin 32) (z : T_t7) := z[k.val]

private theorem read_bit_t7 (w : List T_t7) (i : ℕ) (k : Fin 32) :
    (w.map (bit_t7 k)).getD i false = bit_t7 k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit_t7]

private theorem read_wire_t7 (w : List T_t7) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

private theorem atom_t7 {ws : List T_t7} {x : T_t7} (hx : x = 0 ∨ x ∈ ws) :
    possible_t7 ws x ∧ possible_t7 ws (~~~x) := by
  rcases hx with rfl | hx
  · simp [possible_t7]
  · simp only [possible_t7, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    grind

private theorem pair_t7 {ws : List T_t7} {x y : T_t7} (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
    possible_t7 ws (x &&& y) ∧ possible_t7 ws (x ||| y) := by
  rcases hx with rfl | hx
  · simpa [possible_t7] using (show possible_t7 ws 0 ∧ possible_t7 ws y from ⟨by simp [possible_t7], (atom_t7 hy).1⟩)
  rcases hy with rfl | hy
  · simpa [possible_t7] using (show possible_t7 ws 0 ∧ possible_t7 ws x from ⟨by simp [possible_t7], (atom_t7 (.inr hx)).1⟩)
  · simp only [possible_t7, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    constructor
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inl rfl⟩⟩
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inr rfl⟩⟩

private def step_t7 (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def legal_t7 (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private theorem gate_table_t7 (w ws : List T_t7) (hw : w ⊆ ws) (g : Gate) (hg : legal_t7 g) :
    ∃ z, possible_t7 ws z ∧ ∀ k, step_t7 (w.map (bit_t7 k)) g = (w ++ [z]).map (bit_t7 k) := by
  have mem (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ ws := (read_wire_t7 w i).imp_right (fun h => hw h)
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl | rfl
    · exact ⟨-1, by simp [possible_t7], by simp [step_t7, GateOp.eval, bit_t7]; decide⟩
    · exact ⟨0, by simp [possible_t7], by simp [step_t7, GateOp.eval, bit_t7]⟩
    · exact ⟨-1, by simp [possible_t7], by simp [step_t7, GateOp.eval, bit_t7]; decide⟩
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl | rfl
      · exact ⟨_, (atom_t7 (mem i)).1, by simp only [step_t7, List.map_cons, List.map_nil, read_bit_t7]; simp [GateOp.eval]⟩
      · exact ⟨_, (atom_t7 (mem i)).1, by simp only [step_t7, List.map_cons, List.map_nil, read_bit_t7]; simp [GateOp.eval]⟩
      · exact ⟨_, (atom_t7 (mem i)).2, by simp only [step_t7, List.map_cons, List.map_nil, read_bit_t7]; simp [GateOp.eval, bit_t7]⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl | rfl
        · exact ⟨_, (pair_t7 (mem i) (mem j)).1, by simp only [step_t7, List.map_cons, List.map_nil, read_bit_t7]; simp [GateOp.eval, bit_t7]⟩
        · exact ⟨_, (pair_t7 (mem i) (mem j)).2, by simp only [step_t7, List.map_cons, List.map_nil, read_bit_t7]; simp [GateOp.eval, bit_t7]⟩
        · exact ⟨_, (atom_t7 (mem i)).2, by simp only [step_t7, List.map_cons, List.map_nil, read_bit_t7]; simp [GateOp.eval, bit_t7]⟩

private def safe_t7 : ℕ → List T_t7 → Prop
  | 0, ws => ws.contains target_t7 = false
  | n + 1, ws => ∀ z, possible_t7 ws z → safe_t7 n (z :: ws)

private theorem absent_t7 {n : ℕ} {ws : List T_t7} (h : safe_t7 n ws) : target_t7 ∉ ws := by
  induction n generalizing ws with
  | zero => simpa [safe_t7] using h
  | succ n ih =>
    have ht := ih (h 0 (by simp [possible_t7]))
    exact fun hm => ht (List.mem_cons_of_mem _ hm)

private theorem exclude_t7 (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal_t7 g)
    (w ws : List T_t7) (hw : w ⊆ ws) (m : ℕ) (hm : gs.length ≤ m) (hs : safe_t7 m ws)
    (he : ∀ k, (gs.foldl step_t7 (w.map (bit_t7 k))).getD out false = bit_t7 k target_t7) : False := by
  induction gs generalizing w ws m with
  | nil =>
    have hval : w.getD out 0 = target_t7 := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit_t7, bit_t7] using he ⟨i, hi⟩
    have hr := read_wire_t7 w out
    rw [hval] at hr
    rcases hr with hz | ht
    · exact (by decide : target_t7 ≠ 0) hz
    · exact absent_t7 hs (hw ht)
  | cons g gs ih =>
    cases m with
    | zero => simp at hm
    | succ m =>
      obtain ⟨z, hz, hstep⟩ := gate_table_t7 w ws hw g (hg g (by simp))
      apply ih (fun g' hg' => hg g' (by simp [hg'])) (w ++ [z]) (z :: ws) _ m
        (by simpa using hm) (hs z hz)
      · intro k
        simpa only [List.foldl_cons, hstep] using he k
      · intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact List.mem_cons_of_mem _ (hw hx)
        · simp

private def choices_t7 (ws : List T_t7) : List T_t7 :=
  (0 :: -1 :: ws.flatMap (fun x => x :: ~~~x :: ws.flatMap (fun y => [x &&& y, x ||| y]))).eraseDups

private theorem choice_iff_t7 (ws : List T_t7) (z : T_t7) : z ∈ choices_t7 ws ↔ possible_t7 ws z := by
  simp [choices_t7, possible_t7, List.any_eq_true]
  grind

-- With two gates left, only an existing wire containing every true bit_t7 of
-- the target_t7 can serve as the other input to an AND. OR has the dual test.
private def lastTwo_t7 (ws : List T_t7) : Bool :=
  let above := ws.filter (fun x => (x &&& target_t7) == target_t7)
  let below := ws.filter (fun x => (x ||| target_t7) == target_t7)
  (choices_t7 ws).all fun z => !(z == target_t7 || ~~~z == target_t7 ||
    above.any (fun x => (x &&& z) == target_t7) ||
    below.any (fun x => (x ||| z) == target_t7))

private theorem lastTwo_safe_t7 {ws : List T_t7} (h : lastTwo_t7 ws) : safe_t7 2 ws := by
  intro z hz v hv
  have hz' := (choice_iff_t7 ws z).2 hz
  have ht (u : T_t7) (hu : u ∈ choices_t7 ws) := (List.all_eq_true.mp h) u hu
  have hnot (u : T_t7) (hu : u ∈ choices_t7 ws) : u ≠ target_t7 ∧ ~~~u ≠ target_t7 ∧
      (∀ x ∈ ws, x &&& u ≠ target_t7) ∧ (∀ x ∈ ws, x ||| u ≠ target_t7) := by
    have H := ht u hu
    simp at H
    obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := H
    refine ⟨h1,h2,?_,?_⟩
    · intro x hx he
      apply h3 x hx _ he
      rw [← he, ← BitVec.and_assoc, BitVec.and_self]
    · intro x hx he
      apply h4 x hx _ he
      rw [← he, ← BitVec.or_assoc, BitVec.or_self]
  have H := hnot z hz'
  have base (x : T_t7) (hx : x ∈ ws) := hnot x ((choice_iff_t7 ws x).2 (atom_t7 (.inr hx)).1)
  have unary (x : T_t7) (hx : x ∈ z :: ws) : x ≠ target_t7 ∧ ~~~x ≠ target_t7 := by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨H.1, H.2.1⟩
    · exact ⟨(base x hx).1, (base x hx).2.1⟩
  have binary (x y : T_t7) (hx : x ∈ z :: ws) (hy : y ∈ z :: ws) :
      x &&& y ≠ target_t7 ∧ x ||| y ≠ target_t7 := by
    rcases List.mem_cons.mp hx with hxe | hxm <;> rcases List.mem_cons.mp hy with hye | hym
    · simpa [hxe, hye] using H.1
    · simpa [hxe, BitVec.and_comm, BitVec.or_comm] using And.intro (H.2.2.1 y hym) (H.2.2.2 y hym)
    · simpa [hye] using And.intro (H.2.2.1 x hxm) (H.2.2.2 x hxm)
    · exact ⟨(base y hym).2.2.1 x hxm, (base y hym).2.2.2 x hxm⟩
  have hv' : v ≠ target_t7 := by
    simp only [possible_t7, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hv
    rcases hv with ((h | h) | ⟨x, hx, ((h | h) | ⟨y, hy, h | h⟩)⟩) <;> subst v
    · decide
    · decide
    · exact (unary x hx).1
    · exact (unary x hx).2
    · exact (binary x y hx hy).1
    · exact (binary x y hx hy).2
  change (v :: z :: ws).contains target_t7 = false
  suffices target_t7 ∉ v :: z :: ws by simpa using this
  intro hm
  rcases List.mem_cons.mp hm with he | hm
  · exact hv' he.symm
  · exact (unary target_t7 hm).1 rfl

private def masked_t7 (ws : List T_t7) (mask want : T_t7) : Bool :=
  let xs := ws.map (fun x => x &&& mask)
  want == 0 || want == mask || xs.any fun x =>
    x == want || (~~~x &&& mask) == want ||
    ((x &&& want) == want && xs.any (fun y => (x &&& y) == want)) ||
    ((x ||| want) == want && xs.any (fun y => (x ||| y) == want))

private def fastTwo_t7 (ws : List T_t7) : Bool :=
  !(masked_t7 ws (-1) target_t7 || masked_t7 ws (-1) (~~~target_t7) ||
    ws.any fun x =>
      ((x &&& target_t7) == target_t7 && masked_t7 ws x target_t7) ||
      ((x ||| target_t7) == target_t7 && masked_t7 ws (~~~x) (target_t7 &&& ~~~x)))

private theorem masked_of_possible_t7 {ws : List T_t7} {u : T_t7} (hu : possible_t7 ws u) (m : T_t7) :
    masked_t7 ws m (u &&& m) := by
  let xs := ws.map (fun x => x &&& m)
  have mem (x : T_t7) (hx : x ∈ ws) : x &&& m ∈ xs := List.mem_map.mpr ⟨x, hx, rfl⟩
  simp only [masked_t7, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.any_eq_true]
  simp only [possible_t7, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hu
  rcases hu with ((h | h) | ⟨x, hx, ((h | h) | ⟨y, hy, h | h⟩)⟩) <;> subst u
  · exact .inl (.inl (by simp))
  · exact .inl (.inr BitVec.allOnes_and)
  · exact .inr ⟨_, mem x hx, .inl (.inl (.inl rfl))⟩
  · refine .inr ⟨_, mem x hx, .inl (.inl (.inr ?_))⟩
    apply BitVec.eq_of_getElem_eq
    intro i hi
    simp
    cases x[i] <;> cases m[i] <;> rfl
  · refine .inr ⟨_, mem x hx, .inl (.inr ⟨?_, _, mem y hy, ?_⟩)⟩ <;>
      apply BitVec.eq_of_getElem_eq <;> intro i hi <;> simp only [BitVec.getElem_and] <;>
      cases x[i] <;> cases y[i] <;> cases m[i] <;> decide
  · refine .inr ⟨_, mem x hx, .inr ⟨?_, _, mem y hy, ?_⟩⟩ <;>
      apply BitVec.eq_of_getElem_eq <;> intro i hi <;> simp only [BitVec.getElem_and, BitVec.getElem_or] <;>
      cases x[i] <;> cases y[i] <;> cases m[i] <;> decide

private theorem fast_implies_last_t7 {ws : List T_t7} (hf : fastTwo_t7 ws) : lastTwo_t7 ws := by
  simp [fastTwo_t7] at hf
  obtain ⟨⟨hn, hc⟩, hp⟩ := hf
  apply List.all_eq_true.mpr
  intro z hz
  have hz' := (choice_iff_t7 _ _).1 hz
  simp
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro he
    have hh := masked_of_possible_t7 hz' (-1)
    rw [show z &&& (-1 : T_t7) = z from BitVec.and_allOnes, he] at hh
    simp_all
  · intro he
    have hh := masked_of_possible_t7 hz' (-1)
    have he' : z = ~~~target_t7 := by rw [← he, BitVec.not_not]
    rw [show z &&& (-1 : T_t7) = z from BitVec.and_allOnes, he'] at hh
    simp_all
  · intro x hx ha he
    have hh := masked_of_possible_t7 hz' x
    rw [BitVec.and_comm z x, he] at hh
    have hpair := hp x hx
    simp_all
  · intro x hx ha he
    have hh := masked_of_possible_t7 hz' (~~~x)
    have he' : z &&& ~~~x = target_t7 &&& ~~~x := by
      rw [← he]
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simp
      cases x[i] <;> cases z[i] <;> rfl
    rw [he'] at hh
    have hpair := hp x hx
    simp_all

private def search_t7 : ℕ → List T_t7 → Bool
  | 0, ws => fastTwo_t7 ws
  | n+1, ws => (choices_t7 ws).all (fun z => search_t7 n (z :: ws))

private theorem search_safe_t7 {n : ℕ} {ws : List T_t7} (h : search_t7 n ws) : safe_t7 (n + 2) ws := by
  induction n generalizing ws with
  | zero => exact lastTwo_safe_t7 (fast_implies_last_t7 h)
  | succ n ih =>
    intro z hz
    exact ih ((List.all_eq_true.mp h) z ((choice_iff_t7 _ _).2 hz))

set_option maxRecDepth 100000 in
private theorem top_safe_t7 : safe_t7 1 ins_t7 := by
  have h : (choices_t7 ins_t7).all (fun z => !(z :: ins_t7).contains target_t7) = true := by decide +kernel
  intro z hz
  have := List.all_eq_true.mp h z ((choice_iff_t7 _ _).2 hz)
  simpa [safe_t7] using this

private def graph_t7 (x : Fin 5 → Bool) : Bool :=
  Nat.testBit 0xeaeaeaea (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

private def assignment_t7 (k : Fin 32) (i : Fin 5) := bit_t7 k (ins_t7.getD i.val 0)

private theorem lower_t7 (s : ℕ) (h : HasCircuitSize 5 graph_t7 s) : 2 ≤ s := by
  by_contra! hs
  obtain ⟨C, hg, hsize, he⟩ := h
  have hlen : C.gates.length ≤ 1 := by change C.gates.length ≤ s at hsize; omega
  apply exclude_t7 C.gates C.output hg ins_t7 ins_t7 (fun ⦃_⦄ h => h) 1 hlen top_safe_t7
  intro k
  have hi : ∀ t, List.ofFn (assignment_t7 t) = ins_t7.map (bit_t7 t) := by decide
  have ht : ∀ t, graph_t7 (assignment_t7 t) = bit_t7 t target_t7 := by decide +kernel
  unfold step_t7
  simpa only [Circuit.eval, Circuit.wires, hi, ht] using he (assignment_t7 k)

private def upperC_t7 : Circuit :=
  { gates := [{ op := GateOp.and, inputs := [1, 2] }, { op := GateOp.or, inputs := [0, 5] }],
    output := 6 }

private theorem upper_mono_t7 : Monotone2 upperC_t7 := by
  intro g hg
  simp only [upperC_t7, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl <;> simp

private theorem upper_eval_t7 : ∀ x : Fin 5 → Bool, upperC_t7.eval (List.ofFn x) = graph_t7 x := by
  decide +kernel

private theorem main_t7 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => Nat.testBit 0xeaeaeaea (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit 0xeaeaeaea (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) :=
  fun s h => ⟨upperC_t7, upper_mono_t7, le_trans (by decide : upperC_t7.size ≤ 2) (lower_t7 s h), upper_eval_t7⟩


private abbrev T_t8 := BitVec 32
private def ins_t8 : List T_t8 := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]
private def target_t8 : T_t8 := 0xfefefefe
private def possible_t8 (w : List T_t8) (z : T_t8) : Bool :=
  z == 0 || z == (-1) || w.any (fun u => z == u || z == ~~~u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit_t8 (k : Fin 32) (z : T_t8) := z[k.val]

private theorem read_bit_t8 (w : List T_t8) (i : ℕ) (k : Fin 32) :
    (w.map (bit_t8 k)).getD i false = bit_t8 k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit_t8]

private theorem read_wire_t8 (w : List T_t8) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

private theorem atom_t8 {ws : List T_t8} {x : T_t8} (hx : x = 0 ∨ x ∈ ws) :
    possible_t8 ws x ∧ possible_t8 ws (~~~x) := by
  rcases hx with rfl | hx
  · simp [possible_t8]
  · simp only [possible_t8, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    grind

private theorem pair_t8 {ws : List T_t8} {x y : T_t8} (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
    possible_t8 ws (x &&& y) ∧ possible_t8 ws (x ||| y) := by
  rcases hx with rfl | hx
  · simpa [possible_t8] using (show possible_t8 ws 0 ∧ possible_t8 ws y from ⟨by simp [possible_t8], (atom_t8 hy).1⟩)
  rcases hy with rfl | hy
  · simpa [possible_t8] using (show possible_t8 ws 0 ∧ possible_t8 ws x from ⟨by simp [possible_t8], (atom_t8 (.inr hx)).1⟩)
  · simp only [possible_t8, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    constructor
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inl rfl⟩⟩
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inr rfl⟩⟩

private def step_t8 (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def legal_t8 (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private theorem gate_table_t8 (w ws : List T_t8) (hw : w ⊆ ws) (g : Gate) (hg : legal_t8 g) :
    ∃ z, possible_t8 ws z ∧ ∀ k, step_t8 (w.map (bit_t8 k)) g = (w ++ [z]).map (bit_t8 k) := by
  have mem (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ ws := (read_wire_t8 w i).imp_right (fun h => hw h)
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl | rfl
    · exact ⟨-1, by simp [possible_t8], by simp [step_t8, GateOp.eval, bit_t8]; decide⟩
    · exact ⟨0, by simp [possible_t8], by simp [step_t8, GateOp.eval, bit_t8]⟩
    · exact ⟨-1, by simp [possible_t8], by simp [step_t8, GateOp.eval, bit_t8]; decide⟩
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl | rfl
      · exact ⟨_, (atom_t8 (mem i)).1, by simp only [step_t8, List.map_cons, List.map_nil, read_bit_t8]; simp [GateOp.eval]⟩
      · exact ⟨_, (atom_t8 (mem i)).1, by simp only [step_t8, List.map_cons, List.map_nil, read_bit_t8]; simp [GateOp.eval]⟩
      · exact ⟨_, (atom_t8 (mem i)).2, by simp only [step_t8, List.map_cons, List.map_nil, read_bit_t8]; simp [GateOp.eval, bit_t8]⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl | rfl
        · exact ⟨_, (pair_t8 (mem i) (mem j)).1, by simp only [step_t8, List.map_cons, List.map_nil, read_bit_t8]; simp [GateOp.eval, bit_t8]⟩
        · exact ⟨_, (pair_t8 (mem i) (mem j)).2, by simp only [step_t8, List.map_cons, List.map_nil, read_bit_t8]; simp [GateOp.eval, bit_t8]⟩
        · exact ⟨_, (atom_t8 (mem i)).2, by simp only [step_t8, List.map_cons, List.map_nil, read_bit_t8]; simp [GateOp.eval, bit_t8]⟩

private def safe_t8 : ℕ → List T_t8 → Prop
  | 0, ws => ws.contains target_t8 = false
  | n + 1, ws => ∀ z, possible_t8 ws z → safe_t8 n (z :: ws)

private theorem absent_t8 {n : ℕ} {ws : List T_t8} (h : safe_t8 n ws) : target_t8 ∉ ws := by
  induction n generalizing ws with
  | zero => simpa [safe_t8] using h
  | succ n ih =>
    have ht := ih (h 0 (by simp [possible_t8]))
    exact fun hm => ht (List.mem_cons_of_mem _ hm)

private theorem exclude_t8 (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal_t8 g)
    (w ws : List T_t8) (hw : w ⊆ ws) (m : ℕ) (hm : gs.length ≤ m) (hs : safe_t8 m ws)
    (he : ∀ k, (gs.foldl step_t8 (w.map (bit_t8 k))).getD out false = bit_t8 k target_t8) : False := by
  induction gs generalizing w ws m with
  | nil =>
    have hval : w.getD out 0 = target_t8 := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit_t8, bit_t8] using he ⟨i, hi⟩
    have hr := read_wire_t8 w out
    rw [hval] at hr
    rcases hr with hz | ht
    · exact (by decide : target_t8 ≠ 0) hz
    · exact absent_t8 hs (hw ht)
  | cons g gs ih =>
    cases m with
    | zero => simp at hm
    | succ m =>
      obtain ⟨z, hz, hstep⟩ := gate_table_t8 w ws hw g (hg g (by simp))
      apply ih (fun g' hg' => hg g' (by simp [hg'])) (w ++ [z]) (z :: ws) _ m
        (by simpa using hm) (hs z hz)
      · intro k
        simpa only [List.foldl_cons, hstep] using he k
      · intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact List.mem_cons_of_mem _ (hw hx)
        · simp

private def choices_t8 (ws : List T_t8) : List T_t8 :=
  (0 :: -1 :: ws.flatMap (fun x => x :: ~~~x :: ws.flatMap (fun y => [x &&& y, x ||| y]))).eraseDups

private theorem choice_iff_t8 (ws : List T_t8) (z : T_t8) : z ∈ choices_t8 ws ↔ possible_t8 ws z := by
  simp [choices_t8, possible_t8, List.any_eq_true]
  grind

-- With two gates left, only an existing wire containing every true bit_t8 of
-- the target_t8 can serve as the other input to an AND. OR has the dual test.
private def lastTwo_t8 (ws : List T_t8) : Bool :=
  let above := ws.filter (fun x => (x &&& target_t8) == target_t8)
  let below := ws.filter (fun x => (x ||| target_t8) == target_t8)
  (choices_t8 ws).all fun z => !(z == target_t8 || ~~~z == target_t8 ||
    above.any (fun x => (x &&& z) == target_t8) ||
    below.any (fun x => (x ||| z) == target_t8))

private theorem lastTwo_safe_t8 {ws : List T_t8} (h : lastTwo_t8 ws) : safe_t8 2 ws := by
  intro z hz v hv
  have hz' := (choice_iff_t8 ws z).2 hz
  have ht (u : T_t8) (hu : u ∈ choices_t8 ws) := (List.all_eq_true.mp h) u hu
  have hnot (u : T_t8) (hu : u ∈ choices_t8 ws) : u ≠ target_t8 ∧ ~~~u ≠ target_t8 ∧
      (∀ x ∈ ws, x &&& u ≠ target_t8) ∧ (∀ x ∈ ws, x ||| u ≠ target_t8) := by
    have H := ht u hu
    simp at H
    obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := H
    refine ⟨h1,h2,?_,?_⟩
    · intro x hx he
      apply h3 x hx _ he
      rw [← he, ← BitVec.and_assoc, BitVec.and_self]
    · intro x hx he
      apply h4 x hx _ he
      rw [← he, ← BitVec.or_assoc, BitVec.or_self]
  have H := hnot z hz'
  have base (x : T_t8) (hx : x ∈ ws) := hnot x ((choice_iff_t8 ws x).2 (atom_t8 (.inr hx)).1)
  have unary (x : T_t8) (hx : x ∈ z :: ws) : x ≠ target_t8 ∧ ~~~x ≠ target_t8 := by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨H.1, H.2.1⟩
    · exact ⟨(base x hx).1, (base x hx).2.1⟩
  have binary (x y : T_t8) (hx : x ∈ z :: ws) (hy : y ∈ z :: ws) :
      x &&& y ≠ target_t8 ∧ x ||| y ≠ target_t8 := by
    rcases List.mem_cons.mp hx with hxe | hxm <;> rcases List.mem_cons.mp hy with hye | hym
    · simpa [hxe, hye] using H.1
    · simpa [hxe, BitVec.and_comm, BitVec.or_comm] using And.intro (H.2.2.1 y hym) (H.2.2.2 y hym)
    · simpa [hye] using And.intro (H.2.2.1 x hxm) (H.2.2.2 x hxm)
    · exact ⟨(base y hym).2.2.1 x hxm, (base y hym).2.2.2 x hxm⟩
  have hv' : v ≠ target_t8 := by
    simp only [possible_t8, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hv
    rcases hv with ((h | h) | ⟨x, hx, ((h | h) | ⟨y, hy, h | h⟩)⟩) <;> subst v
    · decide
    · decide
    · exact (unary x hx).1
    · exact (unary x hx).2
    · exact (binary x y hx hy).1
    · exact (binary x y hx hy).2
  change (v :: z :: ws).contains target_t8 = false
  suffices target_t8 ∉ v :: z :: ws by simpa using this
  intro hm
  rcases List.mem_cons.mp hm with he | hm
  · exact hv' he.symm
  · exact (unary target_t8 hm).1 rfl

private def masked_t8 (ws : List T_t8) (mask want : T_t8) : Bool :=
  let xs := ws.map (fun x => x &&& mask)
  want == 0 || want == mask || xs.any fun x =>
    x == want || (~~~x &&& mask) == want ||
    ((x &&& want) == want && xs.any (fun y => (x &&& y) == want)) ||
    ((x ||| want) == want && xs.any (fun y => (x ||| y) == want))

private def fastTwo_t8 (ws : List T_t8) : Bool :=
  !(masked_t8 ws (-1) target_t8 || masked_t8 ws (-1) (~~~target_t8) ||
    ws.any fun x =>
      ((x &&& target_t8) == target_t8 && masked_t8 ws x target_t8) ||
      ((x ||| target_t8) == target_t8 && masked_t8 ws (~~~x) (target_t8 &&& ~~~x)))

private theorem masked_of_possible_t8 {ws : List T_t8} {u : T_t8} (hu : possible_t8 ws u) (m : T_t8) :
    masked_t8 ws m (u &&& m) := by
  let xs := ws.map (fun x => x &&& m)
  have mem (x : T_t8) (hx : x ∈ ws) : x &&& m ∈ xs := List.mem_map.mpr ⟨x, hx, rfl⟩
  simp only [masked_t8, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.any_eq_true]
  simp only [possible_t8, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hu
  rcases hu with ((h | h) | ⟨x, hx, ((h | h) | ⟨y, hy, h | h⟩)⟩) <;> subst u
  · exact .inl (.inl (by simp))
  · exact .inl (.inr BitVec.allOnes_and)
  · exact .inr ⟨_, mem x hx, .inl (.inl (.inl rfl))⟩
  · refine .inr ⟨_, mem x hx, .inl (.inl (.inr ?_))⟩
    apply BitVec.eq_of_getElem_eq
    intro i hi
    simp
    cases x[i] <;> cases m[i] <;> rfl
  · refine .inr ⟨_, mem x hx, .inl (.inr ⟨?_, _, mem y hy, ?_⟩)⟩ <;>
      apply BitVec.eq_of_getElem_eq <;> intro i hi <;> simp only [BitVec.getElem_and] <;>
      cases x[i] <;> cases y[i] <;> cases m[i] <;> decide
  · refine .inr ⟨_, mem x hx, .inr ⟨?_, _, mem y hy, ?_⟩⟩ <;>
      apply BitVec.eq_of_getElem_eq <;> intro i hi <;> simp only [BitVec.getElem_and, BitVec.getElem_or] <;>
      cases x[i] <;> cases y[i] <;> cases m[i] <;> decide

private theorem fast_implies_last_t8 {ws : List T_t8} (hf : fastTwo_t8 ws) : lastTwo_t8 ws := by
  simp [fastTwo_t8] at hf
  obtain ⟨⟨hn, hc⟩, hp⟩ := hf
  apply List.all_eq_true.mpr
  intro z hz
  have hz' := (choice_iff_t8 _ _).1 hz
  simp
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro he
    have hh := masked_of_possible_t8 hz' (-1)
    rw [show z &&& (-1 : T_t8) = z from BitVec.and_allOnes, he] at hh
    simp_all
  · intro he
    have hh := masked_of_possible_t8 hz' (-1)
    have he' : z = ~~~target_t8 := by rw [← he, BitVec.not_not]
    rw [show z &&& (-1 : T_t8) = z from BitVec.and_allOnes, he'] at hh
    simp_all
  · intro x hx ha he
    have hh := masked_of_possible_t8 hz' x
    rw [BitVec.and_comm z x, he] at hh
    have hpair := hp x hx
    simp_all
  · intro x hx ha he
    have hh := masked_of_possible_t8 hz' (~~~x)
    have he' : z &&& ~~~x = target_t8 &&& ~~~x := by
      rw [← he]
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simp
      cases x[i] <;> cases z[i] <;> rfl
    rw [he'] at hh
    have hpair := hp x hx
    simp_all

private def search_t8 : ℕ → List T_t8 → Bool
  | 0, ws => fastTwo_t8 ws
  | n+1, ws => (choices_t8 ws).all (fun z => search_t8 n (z :: ws))

private theorem search_safe_t8 {n : ℕ} {ws : List T_t8} (h : search_t8 n ws) : safe_t8 (n + 2) ws := by
  induction n generalizing ws with
  | zero => exact lastTwo_safe_t8 (fast_implies_last_t8 h)
  | succ n ih =>
    intro z hz
    exact ih ((List.all_eq_true.mp h) z ((choice_iff_t8 _ _).2 hz))

set_option maxRecDepth 100000 in
private theorem top_safe_t8 : safe_t8 1 ins_t8 := by
  have h : (choices_t8 ins_t8).all (fun z => !(z :: ins_t8).contains target_t8) = true := by decide +kernel
  intro z hz
  have := List.all_eq_true.mp h z ((choice_iff_t8 _ _).2 hz)
  simpa [safe_t8] using this

private def graph_t8 (x : Fin 5 → Bool) : Bool :=
  Nat.testBit 0xfefefefe (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

private def assignment_t8 (k : Fin 32) (i : Fin 5) := bit_t8 k (ins_t8.getD i.val 0)

private theorem lower_t8 (s : ℕ) (h : HasCircuitSize 5 graph_t8 s) : 2 ≤ s := by
  by_contra! hs
  obtain ⟨C, hg, hsize, he⟩ := h
  have hlen : C.gates.length ≤ 1 := by change C.gates.length ≤ s at hsize; omega
  apply exclude_t8 C.gates C.output hg ins_t8 ins_t8 (fun ⦃_⦄ h => h) 1 hlen top_safe_t8
  intro k
  have hi : ∀ t, List.ofFn (assignment_t8 t) = ins_t8.map (bit_t8 t) := by decide
  have ht : ∀ t, graph_t8 (assignment_t8 t) = bit_t8 t target_t8 := by decide +kernel
  unfold step_t8
  simpa only [Circuit.eval, Circuit.wires, hi, ht] using he (assignment_t8 k)

private def upperC_t8 : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [0, 1] }, { op := GateOp.or, inputs := [2, 5] }],
    output := 6 }

private theorem upper_mono_t8 : Monotone2 upperC_t8 := by
  intro g hg
  simp only [upperC_t8, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl <;> simp

private theorem upper_eval_t8 : ∀ x : Fin 5 → Bool, upperC_t8.eval (List.ofFn x) = graph_t8 x := by
  decide +kernel

private theorem main_t8 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => Nat.testBit 0xfefefefe (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit 0xfefefefe (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) :=
  fun s h => ⟨upperC_t8, upper_mono_t8, le_trans (by decide : upperC_t8.size ≤ 2) (lower_t8 s h), upper_eval_t8⟩


private abbrev T_t9 := BitVec 32
private def ins_t9 : List T_t9 := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]
private def target_t9 : T_t9 := 0x80008000
private def possible_t9 (w : List T_t9) (z : T_t9) : Bool :=
  z == 0 || z == (-1) || w.any (fun u => z == u || z == ~~~u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit_t9 (k : Fin 32) (z : T_t9) := z[k.val]

private theorem read_bit_t9 (w : List T_t9) (i : ℕ) (k : Fin 32) :
    (w.map (bit_t9 k)).getD i false = bit_t9 k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit_t9]

private theorem read_wire_t9 (w : List T_t9) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

private theorem atom_t9 {ws : List T_t9} {x : T_t9} (hx : x = 0 ∨ x ∈ ws) :
    possible_t9 ws x ∧ possible_t9 ws (~~~x) := by
  rcases hx with rfl | hx
  · simp [possible_t9]
  · simp only [possible_t9, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    grind

private theorem pair_t9 {ws : List T_t9} {x y : T_t9} (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
    possible_t9 ws (x &&& y) ∧ possible_t9 ws (x ||| y) := by
  rcases hx with rfl | hx
  · simpa [possible_t9] using (show possible_t9 ws 0 ∧ possible_t9 ws y from ⟨by simp [possible_t9], (atom_t9 hy).1⟩)
  rcases hy with rfl | hy
  · simpa [possible_t9] using (show possible_t9 ws 0 ∧ possible_t9 ws x from ⟨by simp [possible_t9], (atom_t9 (.inr hx)).1⟩)
  · simp only [possible_t9, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    constructor
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inl rfl⟩⟩
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inr rfl⟩⟩

private def step_t9 (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def legal_t9 (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private theorem gate_table_t9 (w ws : List T_t9) (hw : w ⊆ ws) (g : Gate) (hg : legal_t9 g) :
    ∃ z, possible_t9 ws z ∧ ∀ k, step_t9 (w.map (bit_t9 k)) g = (w ++ [z]).map (bit_t9 k) := by
  have mem (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ ws := (read_wire_t9 w i).imp_right (fun h => hw h)
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl | rfl
    · exact ⟨-1, by simp [possible_t9], by simp [step_t9, GateOp.eval, bit_t9]; decide⟩
    · exact ⟨0, by simp [possible_t9], by simp [step_t9, GateOp.eval, bit_t9]⟩
    · exact ⟨-1, by simp [possible_t9], by simp [step_t9, GateOp.eval, bit_t9]; decide⟩
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl | rfl
      · exact ⟨_, (atom_t9 (mem i)).1, by simp only [step_t9, List.map_cons, List.map_nil, read_bit_t9]; simp [GateOp.eval]⟩
      · exact ⟨_, (atom_t9 (mem i)).1, by simp only [step_t9, List.map_cons, List.map_nil, read_bit_t9]; simp [GateOp.eval]⟩
      · exact ⟨_, (atom_t9 (mem i)).2, by simp only [step_t9, List.map_cons, List.map_nil, read_bit_t9]; simp [GateOp.eval, bit_t9]⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl | rfl
        · exact ⟨_, (pair_t9 (mem i) (mem j)).1, by simp only [step_t9, List.map_cons, List.map_nil, read_bit_t9]; simp [GateOp.eval, bit_t9]⟩
        · exact ⟨_, (pair_t9 (mem i) (mem j)).2, by simp only [step_t9, List.map_cons, List.map_nil, read_bit_t9]; simp [GateOp.eval, bit_t9]⟩
        · exact ⟨_, (atom_t9 (mem i)).2, by simp only [step_t9, List.map_cons, List.map_nil, read_bit_t9]; simp [GateOp.eval, bit_t9]⟩

private def safe_t9 : ℕ → List T_t9 → Prop
  | 0, ws => ws.contains target_t9 = false
  | n + 1, ws => ∀ z, possible_t9 ws z → safe_t9 n (z :: ws)

private theorem absent_t9 {n : ℕ} {ws : List T_t9} (h : safe_t9 n ws) : target_t9 ∉ ws := by
  induction n generalizing ws with
  | zero => simpa [safe_t9] using h
  | succ n ih =>
    have ht := ih (h 0 (by simp [possible_t9]))
    exact fun hm => ht (List.mem_cons_of_mem _ hm)

private theorem exclude_t9 (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal_t9 g)
    (w ws : List T_t9) (hw : w ⊆ ws) (m : ℕ) (hm : gs.length ≤ m) (hs : safe_t9 m ws)
    (he : ∀ k, (gs.foldl step_t9 (w.map (bit_t9 k))).getD out false = bit_t9 k target_t9) : False := by
  induction gs generalizing w ws m with
  | nil =>
    have hval : w.getD out 0 = target_t9 := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit_t9, bit_t9] using he ⟨i, hi⟩
    have hr := read_wire_t9 w out
    rw [hval] at hr
    rcases hr with hz | ht
    · exact (by decide : target_t9 ≠ 0) hz
    · exact absent_t9 hs (hw ht)
  | cons g gs ih =>
    cases m with
    | zero => simp at hm
    | succ m =>
      obtain ⟨z, hz, hstep⟩ := gate_table_t9 w ws hw g (hg g (by simp))
      apply ih (fun g' hg' => hg g' (by simp [hg'])) (w ++ [z]) (z :: ws) _ m
        (by simpa using hm) (hs z hz)
      · intro k
        simpa only [List.foldl_cons, hstep] using he k
      · intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact List.mem_cons_of_mem _ (hw hx)
        · simp

private def choices_t9 (ws : List T_t9) : List T_t9 :=
  (0 :: -1 :: ws.flatMap (fun x => x :: ~~~x :: ws.flatMap (fun y => [x &&& y, x ||| y]))).eraseDups

private theorem choice_iff_t9 (ws : List T_t9) (z : T_t9) : z ∈ choices_t9 ws ↔ possible_t9 ws z := by
  simp [choices_t9, possible_t9, List.any_eq_true]
  grind

-- With two gates left, only an existing wire containing every true bit_t9 of
-- the target_t9 can serve as the other input to an AND. OR has the dual test.
private def lastTwo_t9 (ws : List T_t9) : Bool :=
  let above := ws.filter (fun x => (x &&& target_t9) == target_t9)
  let below := ws.filter (fun x => (x ||| target_t9) == target_t9)
  (choices_t9 ws).all fun z => !(z == target_t9 || ~~~z == target_t9 ||
    above.any (fun x => (x &&& z) == target_t9) ||
    below.any (fun x => (x ||| z) == target_t9))

private theorem lastTwo_safe_t9 {ws : List T_t9} (h : lastTwo_t9 ws) : safe_t9 2 ws := by
  intro z hz v hv
  have hz' := (choice_iff_t9 ws z).2 hz
  have ht (u : T_t9) (hu : u ∈ choices_t9 ws) := (List.all_eq_true.mp h) u hu
  have hnot (u : T_t9) (hu : u ∈ choices_t9 ws) : u ≠ target_t9 ∧ ~~~u ≠ target_t9 ∧
      (∀ x ∈ ws, x &&& u ≠ target_t9) ∧ (∀ x ∈ ws, x ||| u ≠ target_t9) := by
    have H := ht u hu
    simp at H
    obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := H
    refine ⟨h1,h2,?_,?_⟩
    · intro x hx he
      apply h3 x hx _ he
      rw [← he, ← BitVec.and_assoc, BitVec.and_self]
    · intro x hx he
      apply h4 x hx _ he
      rw [← he, ← BitVec.or_assoc, BitVec.or_self]
  have H := hnot z hz'
  have base (x : T_t9) (hx : x ∈ ws) := hnot x ((choice_iff_t9 ws x).2 (atom_t9 (.inr hx)).1)
  have unary (x : T_t9) (hx : x ∈ z :: ws) : x ≠ target_t9 ∧ ~~~x ≠ target_t9 := by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨H.1, H.2.1⟩
    · exact ⟨(base x hx).1, (base x hx).2.1⟩
  have binary (x y : T_t9) (hx : x ∈ z :: ws) (hy : y ∈ z :: ws) :
      x &&& y ≠ target_t9 ∧ x ||| y ≠ target_t9 := by
    rcases List.mem_cons.mp hx with hxe | hxm <;> rcases List.mem_cons.mp hy with hye | hym
    · simpa [hxe, hye] using H.1
    · simpa [hxe, BitVec.and_comm, BitVec.or_comm] using And.intro (H.2.2.1 y hym) (H.2.2.2 y hym)
    · simpa [hye] using And.intro (H.2.2.1 x hxm) (H.2.2.2 x hxm)
    · exact ⟨(base y hym).2.2.1 x hxm, (base y hym).2.2.2 x hxm⟩
  have hv' : v ≠ target_t9 := by
    simp only [possible_t9, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hv
    rcases hv with ((h | h) | ⟨x, hx, ((h | h) | ⟨y, hy, h | h⟩)⟩) <;> subst v
    · decide
    · decide
    · exact (unary x hx).1
    · exact (unary x hx).2
    · exact (binary x y hx hy).1
    · exact (binary x y hx hy).2
  change (v :: z :: ws).contains target_t9 = false
  suffices target_t9 ∉ v :: z :: ws by simpa using this
  intro hm
  rcases List.mem_cons.mp hm with he | hm
  · exact hv' he.symm
  · exact (unary target_t9 hm).1 rfl

private def masked_t9 (ws : List T_t9) (mask want : T_t9) : Bool :=
  let xs := ws.map (fun x => x &&& mask)
  want == 0 || want == mask || xs.any fun x =>
    x == want || (~~~x &&& mask) == want ||
    ((x &&& want) == want && xs.any (fun y => (x &&& y) == want)) ||
    ((x ||| want) == want && xs.any (fun y => (x ||| y) == want))

private def fastTwo_t9 (ws : List T_t9) : Bool :=
  !(masked_t9 ws (-1) target_t9 || masked_t9 ws (-1) (~~~target_t9) ||
    ws.any fun x =>
      ((x &&& target_t9) == target_t9 && masked_t9 ws x target_t9) ||
      ((x ||| target_t9) == target_t9 && masked_t9 ws (~~~x) (target_t9 &&& ~~~x)))

private theorem masked_of_possible_t9 {ws : List T_t9} {u : T_t9} (hu : possible_t9 ws u) (m : T_t9) :
    masked_t9 ws m (u &&& m) := by
  let xs := ws.map (fun x => x &&& m)
  have mem (x : T_t9) (hx : x ∈ ws) : x &&& m ∈ xs := List.mem_map.mpr ⟨x, hx, rfl⟩
  simp only [masked_t9, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.any_eq_true]
  simp only [possible_t9, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hu
  rcases hu with ((h | h) | ⟨x, hx, ((h | h) | ⟨y, hy, h | h⟩)⟩) <;> subst u
  · exact .inl (.inl (by simp))
  · exact .inl (.inr BitVec.allOnes_and)
  · exact .inr ⟨_, mem x hx, .inl (.inl (.inl rfl))⟩
  · refine .inr ⟨_, mem x hx, .inl (.inl (.inr ?_))⟩
    apply BitVec.eq_of_getElem_eq
    intro i hi
    simp
    cases x[i] <;> cases m[i] <;> rfl
  · refine .inr ⟨_, mem x hx, .inl (.inr ⟨?_, _, mem y hy, ?_⟩)⟩ <;>
      apply BitVec.eq_of_getElem_eq <;> intro i hi <;> simp only [BitVec.getElem_and] <;>
      cases x[i] <;> cases y[i] <;> cases m[i] <;> decide
  · refine .inr ⟨_, mem x hx, .inr ⟨?_, _, mem y hy, ?_⟩⟩ <;>
      apply BitVec.eq_of_getElem_eq <;> intro i hi <;> simp only [BitVec.getElem_and, BitVec.getElem_or] <;>
      cases x[i] <;> cases y[i] <;> cases m[i] <;> decide

private theorem fast_implies_last_t9 {ws : List T_t9} (hf : fastTwo_t9 ws) : lastTwo_t9 ws := by
  simp [fastTwo_t9] at hf
  obtain ⟨⟨hn, hc⟩, hp⟩ := hf
  apply List.all_eq_true.mpr
  intro z hz
  have hz' := (choice_iff_t9 _ _).1 hz
  simp
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro he
    have hh := masked_of_possible_t9 hz' (-1)
    rw [show z &&& (-1 : T_t9) = z from BitVec.and_allOnes, he] at hh
    simp_all
  · intro he
    have hh := masked_of_possible_t9 hz' (-1)
    have he' : z = ~~~target_t9 := by rw [← he, BitVec.not_not]
    rw [show z &&& (-1 : T_t9) = z from BitVec.and_allOnes, he'] at hh
    simp_all
  · intro x hx ha he
    have hh := masked_of_possible_t9 hz' x
    rw [BitVec.and_comm z x, he] at hh
    have hpair := hp x hx
    simp_all
  · intro x hx ha he
    have hh := masked_of_possible_t9 hz' (~~~x)
    have he' : z &&& ~~~x = target_t9 &&& ~~~x := by
      rw [← he]
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simp
      cases x[i] <;> cases z[i] <;> rfl
    rw [he'] at hh
    have hpair := hp x hx
    simp_all

private def search_t9 : ℕ → List T_t9 → Bool
  | 0, ws => fastTwo_t9 ws
  | n+1, ws => (choices_t9 ws).all (fun z => search_t9 n (z :: ws))

private theorem search_safe_t9 {n : ℕ} {ws : List T_t9} (h : search_t9 n ws) : safe_t9 (n + 2) ws := by
  induction n generalizing ws with
  | zero => exact lastTwo_safe_t9 (fast_implies_last_t9 h)
  | succ n ih =>
    intro z hz
    exact ih ((List.all_eq_true.mp h) z ((choice_iff_t9 _ _).2 hz))

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
private theorem top_safe_t9 : safe_t9 2 ins_t9 := by
  apply search_safe_t9 (n := 0)
  decide +kernel

private def graph_t9 (x : Fin 5 → Bool) : Bool :=
  Nat.testBit 0x80008000 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

private def assignment_t9 (k : Fin 32) (i : Fin 5) := bit_t9 k (ins_t9.getD i.val 0)

private theorem lower_t9 (s : ℕ) (h : HasCircuitSize 5 graph_t9 s) : 3 ≤ s := by
  by_contra! hs
  obtain ⟨C, hg, hsize, he⟩ := h
  have hlen : C.gates.length ≤ 2 := by change C.gates.length ≤ s at hsize; omega
  apply exclude_t9 C.gates C.output hg ins_t9 ins_t9 (fun ⦃_⦄ h => h) 2 hlen top_safe_t9
  intro k
  have hi : ∀ t, List.ofFn (assignment_t9 t) = ins_t9.map (bit_t9 t) := by decide
  have ht : ∀ t, graph_t9 (assignment_t9 t) = bit_t9 t target_t9 := by decide +kernel
  unfold step_t9
  simpa only [Circuit.eval, Circuit.wires, hi, ht] using he (assignment_t9 k)

private def upperC_t9 : Circuit :=
  { gates := [{ op := GateOp.and, inputs := [0, 1] }, { op := GateOp.and, inputs := [2, 3] }, { op := GateOp.and, inputs := [5, 6] }],
    output := 7 }

private theorem upper_mono_t9 : Monotone2 upperC_t9 := by
  intro g hg
  simp only [upperC_t9, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> simp

private theorem upper_eval_t9 : ∀ x : Fin 5 → Bool, upperC_t9.eval (List.ofFn x) = graph_t9 x := by
  decide +kernel

private theorem main_t9 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => Nat.testBit 0x80008000 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit 0x80008000 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) :=
  fun s h => ⟨upperC_t9, upper_mono_t9, le_trans (by decide : upperC_t9.size ≤ 3) (lower_t9 s h), upper_eval_t9⟩

end PEqualNP.Outside.L_meta_8614

theorem PEqualNP.Outside.L_meta_8614 : ∀ T ∈ ({0x00000000, 0xaaaaaaaa, 0x88888888, 0xeeeeeeee, 0xffffffff, 0x80808080, 0xa8a8a8a8, 0xeaeaeaea, 0xfefefefe, 0x80008000} : Finset ℕ), ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  intro T hT
  simp only [Finset.mem_insert, Finset.mem_singleton] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact PEqualNP.Outside.L_meta_8614.main_t0
  · exact PEqualNP.Outside.L_meta_8614.main_t1
  · exact PEqualNP.Outside.L_meta_8614.main_t2
  · exact PEqualNP.Outside.L_meta_8614.main_t3
  · exact PEqualNP.Outside.L_meta_8614.main_t4
  · exact PEqualNP.Outside.L_meta_8614.main_t5
  · exact PEqualNP.Outside.L_meta_8614.main_t6
  · exact PEqualNP.Outside.L_meta_8614.main_t7
  · exact PEqualNP.Outside.L_meta_8614.main_t8
  · exact PEqualNP.Outside.L_meta_8614.main_t9
