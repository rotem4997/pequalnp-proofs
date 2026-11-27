import Mathlib
import PEqualNP.Defs

-- The search and its soundness proof (down to search_safe) are adapted from the merged proof of
-- L-meta-139 (PEqualNP/Outside/L_meta_139.lean, by Lewis Watson), here without NOT gates and on
-- the 16 inputs with one vertex on each side on; target, bound and final theorems differ.

namespace PEqualNP.Outside.L_meta_5890

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
private abbrev T := BitVec 16
private def ins : List T := [0x000f, 0x00f0, 0x0f00, 0xf000, 0x1111, 0x2222, 0x4444, 0x8888]
private def target : T := 0x33ff
private def possible (w : List T) (z : T) : Bool :=
  z == 0 || z == (-1) || w.any (fun u => z == u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit (k : Fin 16) (z : T) := z[k.val]

private theorem read_bit (w : List T) (i : ℕ) (k : Fin 16) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

private theorem read_wire (w : List T) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

private theorem atom {ws : List T} {x : T} (hx : x = 0 ∨ x ∈ ws) :
    possible ws x := by
  rcases hx with rfl | hx
  · simp [possible]
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    grind

private theorem pair {ws : List T} {x y : T} (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
    possible ws (x &&& y) ∧ possible ws (x ||| y) := by
  rcases hx with rfl | hx
  · simpa [possible] using (show possible ws 0 ∧ possible ws y from ⟨by simp [possible], atom hy⟩)
  rcases hy with rfl | hy
  · simpa [possible] using (show possible ws 0 ∧ possible ws x from ⟨by simp [possible], atom (.inr hx)⟩)
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    constructor
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inl rfl⟩⟩
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inr rfl⟩⟩

private def step (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

private theorem gate_table (w ws : List T) (hw : w ⊆ ws) (g : Gate) (hg : legal g) :
    ∃ z, possible ws z ∧ ∀ k, step (w.map (bit k)) g = (w ++ [z]).map (bit k) := by
  have mem (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ ws := (read_wire w i).imp_right (fun h => hw h)
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl
    · exact ⟨-1, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
    · exact ⟨0, by simp [possible], by simp [step, GateOp.eval, bit]⟩
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl
      · exact ⟨_, atom (mem i), by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, atom (mem i), by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl
        · exact ⟨_, (pair (mem i) (mem j)).1, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
        · exact ⟨_, (pair (mem i) (mem j)).2, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩

private def safe : ℕ → List T → Prop
  | 0, ws => ws.contains target = false
  | n + 1, ws => ∀ z, possible ws z → safe n (z :: ws)

private theorem absent {n : ℕ} {ws : List T} (h : safe n ws) : target ∉ ws := by
  induction n generalizing ws with
  | zero => simpa [safe] using h
  | succ n ih =>
    have ht := ih (h 0 (by simp [possible]))
    exact fun hm => ht (List.mem_cons_of_mem _ hm)

private theorem exclude (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w ws : List T) (hw : w ⊆ ws) (m : ℕ) (hm : gs.length ≤ m) (hs : safe m ws)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k target) : False := by
  induction gs generalizing w ws m with
  | nil =>
    have hval : w.getD out 0 = target := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i, hi⟩
    have hr := read_wire w out
    rw [hval] at hr
    rcases hr with hz | ht
    · exact (by decide : target ≠ 0) hz
    · exact absent hs (hw ht)
  | cons g gs ih =>
    cases m with
    | zero => simp at hm
    | succ m =>
      obtain ⟨z, hz, hstep⟩ := gate_table w ws hw g (hg g (by simp))
      apply ih (fun g' hg' => hg g' (by simp [hg'])) (w ++ [z]) (z :: ws) _ m
        (by simpa using hm) (hs z hz)
      · intro k
        simpa only [List.foldl_cons, hstep] using he k
      · intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact List.mem_cons_of_mem _ (hw hx)
        · simp

private def choices (ws : List T) : List T :=
  (0 :: -1 :: ws.flatMap (fun x => x :: ws.flatMap (fun y => [x &&& y, x ||| y]))).eraseDups

private theorem choice_iff (ws : List T) (z : T) : z ∈ choices ws ↔ possible ws z := by
  simp [choices, possible, List.any_eq_true]
  grind

-- With two gates left, only an existing wire containing every true bit of
-- the target can serve as the other input to an AND. OR has the dual test.
private def lastTwo (ws : List T) : Bool :=
  let above := ws.filter (fun x => (x &&& target) == target)
  let below := ws.filter (fun x => (x ||| target) == target)
  (choices ws).all fun z => !(z == target ||
    above.any (fun x => (x &&& z) == target) ||
    below.any (fun x => (x ||| z) == target))

private theorem lastTwo_safe {ws : List T} (h : lastTwo ws) : safe 2 ws := by
  intro z hz v hv
  have hz' := (choice_iff ws z).2 hz
  have ht (u : T) (hu : u ∈ choices ws) := (List.all_eq_true.mp h) u hu
  have hnot (u : T) (hu : u ∈ choices ws) : u ≠ target ∧
      (∀ x ∈ ws, x &&& u ≠ target) ∧ (∀ x ∈ ws, x ||| u ≠ target) := by
    have H := ht u hu
    simp at H
    obtain ⟨⟨h1,h3⟩,h4⟩ := H
    refine ⟨h1,?_,?_⟩
    · intro x hx he
      apply h3 x hx _ he
      rw [← he, ← BitVec.and_assoc, BitVec.and_self]
    · intro x hx he
      apply h4 x hx _ he
      rw [← he, ← BitVec.or_assoc, BitVec.or_self]
  have H := hnot z hz'
  have base (x : T) (hx : x ∈ ws) := hnot x ((choice_iff ws x).2 (atom (.inr hx)))
  have unary (x : T) (hx : x ∈ z :: ws) : x ≠ target := by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact H.1
    · exact (base x hx).1
  have binary (x y : T) (hx : x ∈ z :: ws) (hy : y ∈ z :: ws) :
      x &&& y ≠ target ∧ x ||| y ≠ target := by
    rcases List.mem_cons.mp hx with hxe | hxm <;> rcases List.mem_cons.mp hy with hye | hym
    · simpa [hxe, hye] using H.1
    · simpa [hxe, BitVec.and_comm, BitVec.or_comm] using And.intro (H.2.1 y hym) (H.2.2 y hym)
    · simpa [hye] using And.intro (H.2.1 x hxm) (H.2.2 x hxm)
    · exact ⟨(base y hym).2.1 x hxm, (base y hym).2.2 x hxm⟩
  have hv' : v ≠ target := by
    simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hv
    rcases hv with ((h | h) | ⟨x, hx, (h | ⟨y, hy, h | h⟩)⟩) <;> subst v
    · decide
    · decide
    · exact unary x hx
    · exact (binary x y hx hy).1
    · exact (binary x y hx hy).2
  change (v :: z :: ws).contains target = false
  suffices target ∉ v :: z :: ws by simpa using this
  intro hm
  rcases List.mem_cons.mp hm with he | hm
  · exact hv' he.symm
  · exact unary target hm rfl

private def masked (ws : List T) (mask want : T) : Bool :=
  let xs := ws.map (fun x => x &&& mask)
  want == 0 || want == mask || xs.any fun x =>
    x == want ||
    ((x &&& want) == want && xs.any (fun y => (x &&& y) == want)) ||
    ((x ||| want) == want && xs.any (fun y => (x ||| y) == want))

private def fastTwo (ws : List T) : Bool :=
  !(masked ws (-1) target ||
    ws.any fun x =>
      ((x &&& target) == target && masked ws x target) ||
      ((x ||| target) == target && masked ws (~~~x) (target &&& ~~~x)))

private theorem masked_of_possible {ws : List T} {u : T} (hu : possible ws u) (m : T) :
    masked ws m (u &&& m) := by
  let xs := ws.map (fun x => x &&& m)
  have mem (x : T) (hx : x ∈ ws) : x &&& m ∈ xs := List.mem_map.mpr ⟨x, hx, rfl⟩
  simp only [masked, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.any_eq_true]
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hu
  rcases hu with ((h | h) | ⟨x, hx, (h | ⟨y, hy, h | h⟩)⟩) <;> subst u
  · exact .inl (.inl (by simp))
  · exact .inl (.inr BitVec.allOnes_and)
  · exact .inr ⟨_, mem x hx, .inl (.inl rfl)⟩
  · refine .inr ⟨_, mem x hx, .inl (.inr ⟨?_, _, mem y hy, ?_⟩)⟩ <;>
      apply BitVec.eq_of_getElem_eq <;> intro i hi <;> simp only [BitVec.getElem_and] <;>
      cases x[i] <;> cases y[i] <;> cases m[i] <;> decide
  · refine .inr ⟨_, mem x hx, .inr ⟨?_, _, mem y hy, ?_⟩⟩ <;>
      apply BitVec.eq_of_getElem_eq <;> intro i hi <;> simp only [BitVec.getElem_and, BitVec.getElem_or] <;>
      cases x[i] <;> cases y[i] <;> cases m[i] <;> decide

private theorem fast_implies_last {ws : List T} (hf : fastTwo ws) : lastTwo ws := by
  simp [fastTwo] at hf
  obtain ⟨hn, hp⟩ := hf
  apply List.all_eq_true.mpr
  intro z hz
  have hz' := (choice_iff _ _).1 hz
  simp
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro he
    have hh := masked_of_possible hz' (-1)
    rw [show z &&& (-1 : T) = z from BitVec.and_allOnes, he] at hh
    simp_all
  · intro x hx ha he
    have hh := masked_of_possible hz' x
    rw [BitVec.and_comm z x, he] at hh
    have hpair := hp x hx
    simp_all
  · intro x hx ha he
    have hh := masked_of_possible hz' (~~~x)
    have he' : z &&& ~~~x = target &&& ~~~x := by
      rw [← he]
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simp
      cases x[i] <;> cases z[i] <;> rfl
    rw [he'] at hh
    have hpair := hp x hx
    simp_all

private def search : ℕ → List T → Bool
  | 0, ws => fastTwo ws
  | n+1, ws => (choices ws).all (fun z => search n (z :: ws))

private theorem search_safe {n : ℕ} {ws : List T} (h : search n ws) : safe (n + 2) ws := by
  induction n generalizing ws with
  | zero => exact lastTwo_safe (fast_implies_last h)
  | succ n ih =>
    intro z hz
    exact ih ((List.all_eq_true.mp h) z ((choice_iff _ _).2 hz))

set_option maxRecDepth 100000 in
private theorem top_safe : safe 2 ins := search_safe (n := 0) (by decide +kernel)

private def A (u v : Fin 4) : Bool := (13311 : ℕ).testBit (4 * u.val + v.val)

private def uu (t : Fin 16) : Fin 4 := ⟨t.val / 4, by omega⟩

private def vv (t : Fin 16) : Fin 4 := ⟨t.val % 4, by omega⟩

private theorem lower (h : PEqualNP.Represents.RepSizeAtMost A 2) : False := by
  obtain ⟨C, hg, hsize, he⟩ := h
  have hlen : C.gates.length ≤ 2 := hsize
  apply exclude C.gates C.output
    (fun g hg' => hg g hg')
    ins ins (fun ⦃_⦄ h => h) 2 hlen top_safe
  intro k
  have hi : ∀ t, PEqualNP.Represents.oneEach (uu t) (vv t) = ins.map (bit t) := by decide
  have ht : ∀ t, A (uu t) (vv t) = bit t target := by decide
  unfold step
  simpa only [Circuit.eval, Circuit.wires, hi, ht] using he (uu k) (vv k)

private theorem upper : PEqualNP.Represents.RepSizeAtMost A 3 := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 1] }], output := 10 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, ?_, ?_⟩
  · intro g hg
    fin_cases hg <;> simp
  · decide
  · decide

end PEqualNP.Outside.L_meta_5890

theorem PEqualNP.Outside.L_meta_5890 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (13311 : ℕ).testBit (4 * u.val + v.val)) 3 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (13311 : ℕ).testBit (4 * u.val + v.val)) 2 :=
  ⟨PEqualNP.Outside.L_meta_5890.upper, fun h => PEqualNP.Outside.L_meta_5890.lower h⟩
