import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9488
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

end Live


abbrev W := BitVec 484
def ops (x y : W) : List W := [x &&& y, x ||| y]
abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset
def inputs : List W := [0x3fffff, 0xfffffc00000, 0x3fffff00000000000, 0xfffffc0000000000000000, 0x3fffff0000000000000000000000, 0xfffffc000000000000000000000000000, 0x3fffff000000000000000000000000000000000, 0xfffffc00000000000000000000000000000000000000, 0x3fffff00000000000000000000000000000000000000000000, 0xfffffc0000000000000000000000000000000000000000000000000, 0x3fffff0000000000000000000000000000000000000000000000000000000, 0xfffffc000000000000000000000000000000000000000000000000000000000000, 0x3fffff000000000000000000000000000000000000000000000000000000000000000000, 0xfffffc00000000000000000000000000000000000000000000000000000000000000000000000, 0x3fffff00000000000000000000000000000000000000000000000000000000000000000000000000000, 0xfffffc0000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x3fffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0xfffffc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x3fffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0xfffffc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x3fffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x40000100000400001000004000010000040000100000400001000004000010000040000100000400001000004000010000040000100000400001, 0x80000200000800002000008000020000080000200000800002000008000020000080000200000800002000008000020000080000200000800002, 0x100000400001000004000010000040000100000400001000004000010000040000100000400001000004000010000040000100000400001000004, 0x200000800002000008000020000080000200000800002000008000020000080000200000800002000008000020000080000200000800002000008, 0x400001000004000010000040000100000400001000004000010000040000100000400001000004000010000040000100000400001000004000010, 0x800002000008000020000080000200000800002000008000020000080000200000800002000008000020000080000200000800002000008000020, 0x1000004000010000040000100000400001000004000010000040000100000400001000004000010000040000100000400001000004000010000040, 0x2000008000020000080000200000800002000008000020000080000200000800002000008000020000080000200000800002000008000020000080, 0x4000010000040000100000400001000004000010000040000100000400001000004000010000040000100000400001000004000010000040000100, 0x8000020000080000200000800002000008000020000080000200000800002000008000020000080000200000800002000008000020000080000200, 0x10000040000100000400001000004000010000040000100000400001000004000010000040000100000400001000004000010000040000100000400, 0x20000080000200000800002000008000020000080000200000800002000008000020000080000200000800002000008000020000080000200000800, 0x40000100000400001000004000010000040000100000400001000004000010000040000100000400001000004000010000040000100000400001000, 0x80000200000800002000008000020000080000200000800002000008000020000080000200000800002000008000020000080000200000800002000, 0x100000400001000004000010000040000100000400001000004000010000040000100000400001000004000010000040000100000400001000004000, 0x200000800002000008000020000080000200000800002000008000020000080000200000800002000008000020000080000200000800002000008000, 0x400001000004000010000040000100000400001000004000010000040000100000400001000004000010000040000100000400001000004000010000, 0x800002000008000020000080000200000800002000008000020000080000200000800002000008000020000080000200000800002000008000020000, 0x1000004000010000040000100000400001000004000010000040000100000400001000004000010000040000100000400001000004000010000040000, 0x2000008000020000080000200000800002000008000020000080000200000800002000008000020000080000200000800002000008000020000080000, 0x4000010000040000100000400001000004000010000040000100000400001000004000010000040000100000400001000004000010000040000100000]
def goal : W := 0x204000408000810001020002040004080008140000480040100080200100400200800401000901021202140404280808501010a02021406042
def cell (w : W) (r c : Fin 22) : Bool := w.getLsbD (22*r.val+c.val)
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
-- Evaluate the remaining gates from the given input wires.
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

theorem wiresFrom_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    wiresFrom (gs ++ [g]) x = wiresFrom gs x ++
      [g.op.eval (g.inputs.map fun i => (wiresFrom gs x).getD i false)] := by
  rw [wiresFrom_append]; rfl

theorem getD_snoc (V : List Bool) (e : Bool) (i : ℕ) :
    (V ++ [e]).getD i false = if i = V.length then e else V.getD i false := by
  split_ifs with h
  · subst h; simp
  · rcases Nat.lt_or_gt_of_ne h with h | h
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
-- AND and OR gates are monotone.
theorem op_mono (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (S T : ℕ → Bool) (h : ∀ i, S i = true → T i = true)
    (he : g.op.eval (g.inputs.map S) = true) : g.op.eval (g.inputs.map T) = true := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with hop | hop <;> rw [hop] at he ⊢
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id] at he ⊢
    exact fun i hi => h i (he i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id] at he ⊢
    obtain ⟨i, hi, hv⟩ := he
    exact ⟨i, hi, h i hv⟩

theorem mono (gs : List Gate) (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (x y : List Bool) (hl : x.length = y.length)
    (h : ∀ i, x.getD i false = true → y.getD i false = true) :
    ∀ i, (wiresFrom gs x).getD i false = true → (wiresFrom gs y).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil => exact h
  | append_singleton gs g ih =>
    have H := ih fun g' h' => hg g' (List.mem_append_left _ h')
    intro i
    rw [wiresFrom_snoc, wiresFrom_snoc, getD_snoc, getD_snoc, length_wiresFrom, length_wiresFrom,
      hl]
    split_ifs with hk
    · exact op_mono g (hg g (by simp)) _ _ H
    · exact H i

private def possible (w : List W) (z : W) : Bool :=
  z == 0 || z == BitVec.allOnes 484 || w.any (fun u => z == u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit (k : Fin 484) (z : W) : Bool := z[k.val]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 484) :
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
    · exact ⟨BitVec.allOnes 484, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
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
  ∀ u ∈ w, u = 0 ∨ u = BitVec.allOnes 484 ∨ u ∈ available

theorem classify {available : Finset W} {ws : List W} (hw : represents available ws)
    {z : W} (hz : possible ws z) :
    z = 0 ∨ z = BitVec.allOnes 484 ∨ z ∈ available ∨
      ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ z ∈ basicOps a b := by
  have lift {t : W} (h : t = 0 ∨ t = BitVec.allOnes 484 ∨ t ∈ available) :
      t = 0 ∨ t = BitVec.allOnes 484 ∨ t ∈ available ∨
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
      · exact False.elim ((by decide : goal ≠ BitVec.allOnes 484) h)
      · exact h
  | cons g gs ih =>
    obtain ⟨z, hz, hstep⟩ := gate_table w w (fun _ h => h) g (hg g (by simp))
    have fn := ih (fun g' h => hg g' (by simp [h])) (w ++ [z])
    have he' : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, hstep] using he k
    have appendOK (h : z = 0 ∨ z = BitVec.allOnes 484 ∨ z ∈ av) : represents av (w ++ [z]) := by
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


def A : Fin 21 → Fin 21 → Bool := fun a b => decide (∃ i : Fin 7, ((a.val = i.val ∨ a.val = 7 + i.val) ∧ (b.val = (i.val + 1) % 7 ∨ b.val = 14 + i.val)) ∨ ((b.val = i.val ∨ b.val = 7 + i.val) ∧ (a.val = (i.val + 1) % 7 ∨ a.val = 14 + i.val)))
def witnessPair (k : Fin 484) : Fin 21 × Fin 21 :=
  let r := k.val / 22
  let c := k.val % 22
  if hr : r < 21 then
    if hc : c < 21 then (⟨r,hr⟩, ⟨c,hc⟩) else (⟨r,hr⟩, ⟨r,hr⟩)
  else if hc : c < 21 then (⟨c,hc⟩, ⟨c,hc⟩) else (0,0)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem witness_ok : ∀ k : Fin 484,
  let u := (witnessPair k).1
  let v := (witnessPair k).2
  (inputs.map (bit k) = oneEach u v ∧ bit k goal = A u v) ∨
  (bit k goal = false ∧ A u v = false ∧
    ∀ i : Fin 42, (inputs.map (bit k)).getD i.val false = true → (oneEach u v).getD i.val false = true) := by
  decide +kernel

theorem sample_property : ∀ k : Fin 484,
  (∃ u v : Fin 21, inputs.map (bit k) = oneEach u v ∧ bit k goal = A u v) ∨
  (∃ u v : Fin 21, bit k goal = false ∧ A u v = false ∧
    ∀ i : Fin 42, (inputs.map (bit k)).getD i.val false = true → (oneEach u v).getD i.val false = true) := by
  intro k
  exact (witness_ok k).imp (fun h => ⟨_,_,h⟩) (fun h => ⟨_,_,h⟩)

theorem rows_eval (C : Circuit) (hr : Represents A C) (hm : Monotone2 C) (k : Fin 484) :
    (C.gates.foldl step (inputs.map (bit k))).getD C.output false = bit k goal := by
  rcases sample_property k with ⟨u,v,hi,hg⟩ | ⟨u,v,hg,ha,hsub⟩
  · rw [hi, hg]; exact hr u v
  · have hl : (inputs.map (bit k)).length = (oneEach u v).length := by simp [oneEach, inputs]
    have hmono := mono C.gates (fun g hg => (hm g hg).1)
      (inputs.map (bit k)) (oneEach u v) hl (fun i hi => by
        by_cases hlt : i < 42
        · exact hsub ⟨i,hlt⟩ hi
        · have hh : (inputs.map (bit k)).length ≤ i := by simp [inputs]; omega
          rw [List.getD_eq_default _ _ hh] at hi
          contradiction) C.output
    rw [hg]
    cases h : (C.gates.foldl step (inputs.map (bit k))).getD C.output false with
    | false => rfl
    | true =>
      have hx := hmono h
      change C.eval (oneEach u v) = true at hx
      rw [hr u v, ha] at hx
      contradiction

theorem get_live (C : Circuit) (hm : Monotone2 C) (hr : Represents A C) :
    ∃ S ⊆ inputs.toFinset, live basicOps goal C.size S := by
  apply compress
  apply compile C.gates C.output hm inputs inputs.toFinset
  · exact fun _ hu => Or.inr (Or.inr (List.mem_toFinset.mpr hu))
  · exact rows_eval C hr hm



-- The two rows and two columns of each path span three of the four possible edges.
namespace Packing
def edge (a b : Fin 21) : Bool :=
  decide (∃ i : Fin 7, ((a.val = i.val ∨ a.val = 7 + i.val) ∧
    (b.val = (i.val + 1) % 7 ∨ b.val = 14 + i.val)) ∨
    ((b.val = i.val ∨ b.val = 7 + i.val) ∧
    (a.val = (i.val + 1) % 7 ∨ a.val = 14 + i.val)))

def rows (i : Fin 9) (k : Fin 2) : Fin 21 :=
  (![![0, 7], ![5, 12], ![2, 15], ![4, 9], ![11, 19],
     ![10, 18], ![16, 8], ![6, 13], ![1, 14]] : Fin 9 → Fin 2 → Fin 21) i k

def cols (i : Fin 9) (k : Fin 2) : Fin 21 :=
  (![![1, 6], ![19, 11], ![8, 16], ![3, 10], ![5, 18],
     ![4, 17], ![2, 9], ![0, 12], ![7, 15]] : Fin 9 → Fin 2 → Fin 21) i k

def Compatible {m n t : ℕ} (E : Fin m → Fin n → Bool)
    (r : Fin t → Fin 2 → Fin m) (c : Fin t → Fin 2 → Fin n) : Prop :=
  (∀ i j : Fin t, i ≠ j → ∀ a b : Fin 2, ∃ k : Fin 2,
    E (r i a) (c i k) ≠ E (r j b) (c i k) ∨
    E (r i a) (c j k) ≠ E (r j b) (c j k)) ∧
  (∀ i j : Fin t, i ≠ j → ∀ a b : Fin 2, ∃ k : Fin 2,
    E (r i k) (c i a) ≠ E (r i k) (c j b) ∨
    E (r j k) (c i a) ≠ E (r j k) (c j b))

theorem paths : ∀ i, edge (rows i 0) (cols i 0) = true ∧
    edge (rows i 0) (cols i 1) = true ∧ edge (rows i 1) (cols i 0) = true ∧
    edge (rows i 1) (cols i 1) = false := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
theorem compatible : Compatible edge rows cols := by
  unfold Compatible
  decide +kernel

end Packing

abbrev Lab := Fin 9 × Fin 2

def rowId : Option Lab → Fin 22
  | none => 21
  | some (i,x) => (Packing.rows i x).castSucc

def colId : Option Lab → Fin 22
  | none => 21
  | some (i,x) => (Packing.cols i x).castSucc

def on (w : W) (r c : Option Lab) : Prop := cell w (rowId r) (colId c) = true

def ok (I : Finset (Fin 9)) (x : Option Lab) : Prop := ∀ p ∈ x, p.1 ∈ I

-- On surviving paths each active row or column has one wire that carries its input.
def clean (s : Finset W) (I : Finset (Fin 9)) (R C : Lab → W) : Prop :=
  (∀ x, x.1 ∈ I → R x ∈ s ∧ C x ∈ s) ∧
  ∀ r c, ok I r → ok I c → ∀ w ∈ s,
    on w r c ↔ r.map R = some w ∨ c.map C = some w


set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem goal_pair (i : Fin 9) (x : Fin 2) (j : Fin 9) (y : Fin 2) :
  on goal (some (i,x)) (some (j,y)) ↔ Packing.edge (Packing.rows i x) (Packing.cols j y) = true := by
  unfold on cell
  revert i x j y
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem goal_singleR (x : Option Lab) : ¬ on goal x none := by
  unfold on cell
  revert x
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem goal_singleC (x : Option Lab) : ¬ on goal none x := by
  unfold on cell
  revert x
  decide +kernel


def rowOwner (p : Lab) : W := inputs.getD (Packing.rows p.1 p.2).val 0
def colOwner (p : Lab) : W := inputs.getD (21 + (Packing.cols p.1 p.2).val) 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem owners_in_inputs : ∀ p : Lab, rowOwner p ∈ inputs ∧ colOwner p ∈ inputs := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem init_index : ∀ r c : Option Lab, ∀ j : Fin 42,
    let w := inputs.getD j.val 0
    cell w (rowId r) (colId c) = true ↔ r.map rowOwner = some w ∨ c.map colOwner = some w := by
  decide +kernel

theorem initial_on : ∀ r c : Option Lab, ∀ w ∈ inputs,
    (on w r c ↔ r.map rowOwner = some w ∨ c.map colOwner = some w) := by
  intro r c w hw
  obtain ⟨j,hj⟩ := List.get_of_mem hw
  let jj : Fin 42 := ⟨j.val, by simpa [inputs] using j.isLt⟩
  have he : inputs.getD jj.val 0 = w := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show jj.val < inputs.length from j.isLt)]
    exact hj
  simpa only [on,he] using init_index r c jj

theorem initial_clean : clean inputs.toFinset Finset.univ rowOwner colOwner := by
  constructor
  · intro x hx
    exact ⟨List.mem_toFinset.mpr (owners_in_inputs x).1,
      List.mem_toFinset.mpr (owners_in_inputs x).2⟩
  · intro r c hr hc w hw
    exact initial_on r c w (List.mem_toFinset.mp hw)

def pos : Fin 42 → Fin 484 := ![1,22,45,68,91,114,132,155,178,201,224,247,270,286,308,331,354,377,400,423,446,22,1,24,47,70,93,6,29,52,75,98,121,144,13,14,37,60,83,106,129,152]
def neg : Fin 42 → Fin 484 := ![463,462,463,464,465,466,462,463,464,465,466,467,468,462,462,463,464,465,466,467,468,43,21,43,65,87,109,21,43,65,87,109,131,153,21,21,43,65,87,109,131,153]
def differs (i : Fin 42) (w : W) : Prop := bit (pos i) w ≠ bit (neg i) w

theorem ops_differs (i : Fin 42) (a b z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  unfold differs bit at hd ⊢
  rcases hz with rfl | rfl <;> revert hd <;>
    simp only [BitVec.getElem_and, BitVec.getElem_or] <;>
    cases a[(pos i).val] <;> cases a[(neg i).val] <;>
    cases b[(pos i).val] <;> cases b[(neg i).val] <;> simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem indexed_cert : ∀ i j : Fin 42,
    differs i goal ∧ (differs i (inputs.getD j.val 0) ↔ inputs.getD j.val 0 = inputs.getD i.val 0) := by
  unfold differs
  decide +kernel

theorem certificates : ∀ i : Fin 42, differs i goal ∧
    ∀ x ∈ inputs, (differs i x ↔ x = inputs.getD i.val 0) := by
  intro i
  refine ⟨(indexed_cert i i).1, ?_⟩
  intro x hx
  obtain ⟨j,hj⟩ := List.get_of_mem hx
  let jj : Fin 42 := ⟨j.val, by simpa [inputs] using j.isLt⟩
  have hh : inputs.getD jj.val 0 = x := by
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (show jj.val < inputs.length from j.isLt)]
    exact hj
  rw [← hh]
  exact (indexed_cert i jj).2

theorem all_inputs {k : ℕ} {S : Finset W} (hs : S ⊆ inputs.toFinset)
    (hl : live basicOps goal k S) : S = inputs.toFinset := by
  apply Finset.Subset.antisymm hs
  intro x hx
  have hxm : x ∈ inputs := List.mem_toFinset.mp hx
  obtain ⟨n, hn⟩ := List.get_of_mem hxm
  let i : Fin 42 := ⟨n.val, by simpa [inputs] using n.isLt⟩
  obtain ⟨w, hw, hd⟩ := live_separates (differs i) (certificates i).1 (ops_differs i) hl
  have hwinput : w ∈ inputs := List.mem_toFinset.mp (hs hw)
  have heq := ((certificates i).2 w hwinput).mp hd
  have heqx : inputs.getD i.val 0 = x := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i.val < inputs.length from n.isLt)]
    exact hn
  rw [heq, heqx] at hw
  exact hw

theorem get_live_all (C : Circuit) (hm : Monotone2 C) (hr : Represents A C) :
    live basicOps goal C.size inputs.toFinset := by
  obtain ⟨S, hs, hl⟩ := get_live C hm hr
  rw [all_inputs hs hl] at hl
  exact hl

theorem input_card : inputs.toFinset.card = 42 := by decide +kernel

theorem okSome {I : Finset (Fin 9)} {p : Lab} (h : p.1 ∈ I) : ok I (some p) := by
  simpa [ok] using h

theorem okNone (I : Finset (Fin 9)) : ok I none := by simp [ok]

theorem sep_on {k : ℕ} {s : Finset W} (h : live basicOps goal k s) {r c t u : Option Lab}
    (hp : on goal r c) (hn : ¬ on goal t u) : ∃ w ∈ s, on w r c ∧ ¬ on w t u := by
  apply live_separates (fun w => on w r c ∧ ¬ on w t u) ⟨hp, hn⟩ _ h
  intro a b z hz
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl <;> simp [on,cell,BitVec.getLsbD_and,BitVec.getLsbD_or] <;> grind

theorem same_on {k : ℕ} {s : Finset W} (h : live basicOps goal k s) {r c t u : Option Lab}
    (he : ∀ w ∈ s, on w r c ↔ on w t u) : on goal r c ↔ on goal t u := by
  constructor
  · intro hp; by_contra hn
    obtain ⟨w,hw,hp',hn'⟩ := sep_on h hp hn
    exact hn' ((he w hw).mp hp')
  · intro hp; by_contra hn
    obtain ⟨w,hw,hp',hn'⟩ := sep_on h hp hn
    exact hn' ((he w hw).mpr hp')

theorem row_owners {k : ℕ} {s : Finset W} {I : Finset (Fin 9)} {R C : Lab → W}
    (h : live basicOps goal k s) (hc : clean s I R C) {i j : Fin 9}
    (hi : i ∈ I) (hj : j ∈ I) {x y : Fin 2} (he : R (i,x) = R (j,y)) :
    i = j ∧ x = y := by
  have same (l : Fin 9) (hl : l ∈ I) (b : Fin 2) :
      Packing.edge (Packing.rows i x) (Packing.cols l b) =
      Packing.edge (Packing.rows j y) (Packing.cols l b) := by
    apply Bool.eq_iff_iff.mpr
    rw [← goal_pair, ← goal_pair]
    apply same_on h
    intro w hw
    rw [hc.2 _ _ (okSome hi) (okSome hl) w hw, hc.2 _ _ (okSome hj) (okSome hl) w hw]
    simp [he]
  by_cases hij : i = j
  · subst j
    refine ⟨rfl, ?_⟩
    have h1 := same i hi 1
    have hp := Packing.paths i
    fin_cases x <;> fin_cases y <;> simp_all
  · obtain ⟨b,hb | hb⟩ := Packing.compatible.1 i j hij x y
    · exact False.elim (hb (same i hi b))
    · exact False.elim (hb (same j hj b))

theorem col_owners {k : ℕ} {s : Finset W} {I : Finset (Fin 9)} {R C : Lab → W}
    (h : live basicOps goal k s) (hc : clean s I R C) {i j : Fin 9}
    (hi : i ∈ I) (hj : j ∈ I) {x y : Fin 2} (he : C (i,x) = C (j,y)) :
    i = j ∧ x = y := by
  have same (l : Fin 9) (hl : l ∈ I) (b : Fin 2) :
      Packing.edge (Packing.rows l b) (Packing.cols i x) =
      Packing.edge (Packing.rows l b) (Packing.cols j y) := by
    apply Bool.eq_iff_iff.mpr
    rw [← goal_pair, ← goal_pair]
    apply same_on h
    intro w hw
    rw [hc.2 _ _ (okSome hl) (okSome hi) w hw, hc.2 _ _ (okSome hl) (okSome hj) w hw]
    simp [he]
  by_cases hij : i = j
  · subst j
    refine ⟨rfl, ?_⟩
    have h1 := same i hi 1
    have hp := Packing.paths i
    fin_cases x <;> fin_cases y <;> simp_all
  · obtain ⟨b,hb | hb⟩ := Packing.compatible.2 i j hij x y
    · exact False.elim (hb (same i hi b))
    · exact False.elim (hb (same j hj b))


theorem on_and (a b : W) (r c : Option Lab) : on (a &&& b) r c ↔ on a r c ∧ on b r c := by
  simp [on,cell,BitVec.getLsbD_and]

theorem on_or (a b : W) (r c : Option Lab) : on (a ||| b) r c ↔ on a r c ∨ on b r c := by
  simp [on,cell,BitVec.getLsbD_or]

def safe (J : Finset (Fin 9)) (R C : Lab → W) (v : W) (rest : Finset W) : Prop :=
  v ∈ rest → ∀ p, p.1 ∈ J → R p ≠ v ∧ C p ≠ v

-- On a positive edge, an AND consuming one endpoint must also read the other.
theorem and_edge {k : ℕ} {a b : W} {rest : Finset W} {J : Finset (Fin 9)} {R C : Lab → W}
    (hab : a ≠ b) (h : live basicOps goal k (insert (a &&& b) rest))
    (hc : clean (insert a (insert b rest)) J R C)
    (sa : safe J R C a rest) (sb : safe J R C b rest)
    {x y : Lab} (hx : x.1 ∈ J) (hy : y.1 ∈ J)
    (hp : on goal (some x) (some y)) :
    ((R x = a → C y = b) ∧ (R x = b → C y = a)) ∧
    ((C y = a → R x = b) ∧ (C y = b → R x = a)) := by
  have vr (w : W) (hw : w ∈ insert a (insert b rest)) :
      on w (some x) (some y) ↔ R x = w ∨ C y = w := by
    simpa using hc.2 _ _ (okSome hx) (okSome hy) w hw
  have vc (w : W) (hw : w ∈ rest) : on w none (some y) ↔ C y = w := by
    simpa using hc.2 _ _ (okNone J) (okSome hy) w (by simp [hw])
  have vv (w : W) (hw : w ∈ rest) : on w (some x) none ↔ R x = w := by
    simpa using hc.2 _ _ (okSome hx) (okNone J) w (by simp [hw])
  obtain ⟨u,hu,hu1,hu0⟩ := sep_on h hp (goal_singleC (some y))
  obtain ⟨v,hv,hv1,hv0⟩ := sep_on h hp (goal_singleR (some x))
  have caseR : (R x ∉ rest → (R x = a ∨ R x = b) →
      (R x = a → C y = b) ∧ (R x = b → C y = a)) := by
    intro hr _
    rcases Finset.mem_insert.mp hu with rfl | hmem
    · have hh := (on_and _ _ _ _).mp hu1
      have h1 := (vr a (by simp)).mp hh.1
      have h2 := (vr b (by simp)).mp hh.2
      grind
    · have h1 := (vr u (by simp [hmem])).mp hu1
      have h2 := vc u hmem
      grind
  have caseC : (C y ∉ rest → (C y = a ∨ C y = b) →
      (C y = a → R x = b) ∧ (C y = b → R x = a)) := by
    intro hr _
    rcases Finset.mem_insert.mp hv with rfl | hmem
    · have hh := (on_and _ _ _ _).mp hv1
      have h1 := (vr a (by simp)).mp hh.1
      have h2 := (vr b (by simp)).mp hh.2
      grind
    · have h1 := (vr v (by simp [hmem])).mp hv1
      have h2 := vv v hmem
      grind
  have s1 : a ∈ rest → R x ≠ a ∧ C y ≠ a := fun hh => ⟨(sa hh _ hx).1,(sa hh _ hy).2⟩
  have s2 : b ∈ rest → R x ≠ b ∧ C y ≠ b := fun hh => ⟨(sb hh _ hx).1,(sb hh _ hy).2⟩
  grind

theorem and_untouched {k : ℕ} {a b : W} {rest : Finset W} {J : Finset (Fin 9)} {R C : Lab → W}
    (hab : a ≠ b) (h : live basicOps goal k (insert (a &&& b) rest))
    (hc : clean (insert a (insert b rest)) J R C)
    (hinjR : ∀ i ∈ J, R (i,0) ≠ R (i,1)) (hinjC : ∀ i ∈ J, C (i,0) ≠ C (i,1))
    (sa : safe J R C a rest) (sb : safe J R C b rest) :
    ∀ p, p.1 ∈ J → R p ≠ a ∧ R p ≠ b ∧ C p ≠ a ∧ C p ≠ b := by
  rintro ⟨i,t⟩ hi
  have step (x y : Fin 2) (he : Packing.edge (Packing.rows i x) (Packing.cols i y) = true) :=
    and_edge hab h hc sa sb (x := (i,x)) (y := (i,y)) hi hi ((goal_pair i x i y).mpr he)
  obtain ⟨h00,h01,h10,_⟩ := Packing.paths i
  have q00 := step 0 0 h00
  have q01 := step 0 1 h01
  have q10 := step 1 0 h10
  have qR := hinjR i hi
  have qC := hinjC i hi
  fin_cases t <;> grind

def changeOwner (a b z t : W) : W := if t = a ∨ t = b then z else t

theorem map_changed (a b z w : W) (r : Option Lab) (f : Lab → W) :
    r.map (fun x => changeOwner a b z (f x)) = some w ↔
    (((r.map f = some a ∨ r.map f = some b) ∧ z = w) ∨
      (r.map f = some w ∧ w ≠ a ∧ w ≠ b)) := by
  cases r with
  | none => simp
  | some p =>
    simp only [Option.map_some, Option.some.injEq, changeOwner]
    split <;> grind

theorem map_fresh {s : Finset W} {J : Finset (Fin 9)} {r : Option Lab} {f : Lab → W} {z : W}
    (hr : ok J r) (hm : ∀ x, x.1 ∈ J → f x ∈ s) (hn : z ∉ s) : r.map f ≠ some z := by
  cases r with
  | none => simp
  | some x =>
    have hh := hm x (hr x (by simp))
    simpa using (show f x ≠ z by grind)

theorem map_avoid {J : Finset (Fin 9)} {r : Option Lab} {f : Lab → W} {v : W}
    (hr : ok J r) (hm : ∀ x, x.1 ∈ J → f x ≠ v) : r.map f ≠ some v := by
  cases r with
  | none => simp
  | some p => simpa using hm p (hr p (by simp))

set_option maxHeartbeats 1000000 in
theorem step_clean {k : ℕ} {a b z : W} {rest : Finset W} {J : Finset (Fin 9)} {R C : Lab → W}
    (hab : a ≠ b) (hz : z ∈ basicOps a b) (hn : z ∉ insert a (insert b rest))
    (h : live basicOps goal k (insert z rest))
    (hc : clean (insert a (insert b rest)) J R C)
    (hinjR : ∀ i ∈ J, R (i,0) ≠ R (i,1)) (hinjC : ∀ i ∈ J, C (i,0) ≠ C (i,1))
    (sa : safe J R C a rest) (sb : safe J R C b rest) :
    clean (insert z rest) J (fun x => changeOwner a b z (R x)) (fun x => changeOwner a b z (C x)) := by
  have change_mem (t : W) (ht : t ∈ insert a (insert b rest)) :
      changeOwner a b z t ∈ insert z rest := by
    simp only [Finset.mem_insert] at *
    unfold changeOwner
    split <;> grind
  refine ⟨fun x hx => ⟨change_mem _ (hc.1 x hx).1, change_mem _ (hc.1 x hx).2⟩, ?_⟩
  intro r c hr hc' w hw
  rw [map_changed, map_changed]
  have vold := hc.2 r c hr hc'
  have ha := vold a (by simp)
  have hb := vold b (by simp)
  have hfr := map_fresh hr (fun x hx => (hc.1 x hx).1) hn
  have hfc := map_fresh hc' (fun x hx => (hc.1 x hx).2) hn
  rcases Finset.mem_insert.mp hw with rfl | hrest
  · simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with hEq | hEq
    · subst hEq
      have hu := and_untouched hab h hc hinjR hinjC sa sb
      have h1 := map_avoid hr (fun x hx => (hu x hx).1)
      have h2 := map_avoid hr (fun x hx => (hu x hx).2.1)
      have h3 := map_avoid hc' (fun x hx => (hu x hx).2.2.1)
      have h4 := map_avoid hc' (fun x hx => (hu x hx).2.2.2)
      simp only [on_and, ha, hb, h1, h2, h3, h4, hfr, hfc, false_and, or_false]
    · subst hEq
      simp only [on_or, ha, hb, hfr, hfc, false_and, or_false, and_true]
      grind only
  · have hwz : z ≠ w := fun he => hn (by simp [he,hrest])
    have hh := vold w (by simp [hrest])
    have na : w = a → r.map R ≠ some a ∧ c.map C ≠ some a := by
      rintro rfl
      exact ⟨map_avoid hr (fun x hx => (sa hrest x hx).1),
             map_avoid hc' (fun x hx => (sa hrest x hx).2)⟩
    have nb : w = b → r.map R ≠ some b ∧ c.map C ≠ some b := by
      rintro rfl
      exact ⟨map_avoid hr (fun x hx => (sb hrest x hx).1),
             map_avoid hc' (fun x hx => (sb hrest x hx).2)⟩
    grind
def trim (I : Finset (Fin 9)) (R C : Lab → W) (w : W) : Finset (Fin 9) :=
  I.filter fun i => ∀ x : Fin 2, R (i,x) ≠ w ∧ C (i,x) ≠ w

theorem trim_subset (I : Finset (Fin 9)) (R C : Lab → W) (w : W) : trim I R C w ⊆ I :=
  Finset.filter_subset _ _

theorem trim_avoids {I : Finset (Fin 9)} {R C : Lab → W} {w : W} {i : Fin 9}
    (hi : i ∈ trim I R C w) (x : Fin 2) : R (i,x) ≠ w ∧ C (i,x) ≠ w :=
  (Finset.mem_filter.mp hi).2 x

theorem trim_card {k : ℕ} {s : Finset W} {I : Finset (Fin 9)} {R C : Lab → W}
    (h : live basicOps goal k s) (hc : clean s I R C) (w : W) :
    I.card ≤ (trim I R C w).card + 2 := by
  let rows := I.filter fun i => ∃ x : Fin 2, R (i,x) = w
  let cols := I.filter fun i => ∃ x : Fin 2, C (i,x) = w
  have hr : rows.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    obtain ⟨hi, x, hx⟩ := Finset.mem_filter.mp hi
    obtain ⟨hj, y, hy⟩ := Finset.mem_filter.mp hj
    exact (row_owners h hc hi hj (hx.trans hy.symm)).1
  have hc' : cols.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    obtain ⟨hi, x, hx⟩ := Finset.mem_filter.mp hi
    obtain ⟨hj, y, hy⟩ := Finset.mem_filter.mp hj
    exact (col_owners h hc hi hj (hx.trans hy.symm)).1
  have hall : I ⊆ trim I R C w ∪ (rows ∪ cols) := by
    intro i hi
    by_cases hx : ∃ x : Fin 2, R (i,x) = w
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi, hx⟩))
    by_cases hy : ∃ x : Fin 2, C (i,x) = w
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hi, hy⟩))
    exact Finset.mem_union_left _ (Finset.mem_filter.mpr
      ⟨hi, fun x => ⟨fun h => hx ⟨x,h⟩, fun h => hy ⟨x,h⟩⟩⟩)
  have h1 := Finset.card_le_card hall
  have h2 := Finset.card_union_le (trim I R C w) (rows ∪ cols)
  have h3 := Finset.card_union_le rows cols
  omega

theorem transition_card {α : Type} [DecidableEq α] {a b z : α} {rest : Finset α}
    (hab : a ≠ b) (hz : z ∉ insert a (insert b rest)) :
    (insert a (insert b rest)).card + (if a ∈ rest then 1 else 0) +
      (if b ∈ rest then 1 else 0) + 1 = (insert z rest).card + 2 := by
  have hzr : z ∉ rest := fun h => hz (by simp [h])
  rw [Finset.card_insert_of_notMem hzr]
  by_cases ha : a ∈ rest <;> by_cases hb : b ∈ rest
  · rw [Finset.insert_eq_of_mem hb, Finset.insert_eq_of_mem ha]
    simp [ha, hb]
  · rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem ha), Finset.card_insert_of_notMem hb]
    simp [ha, hb]
  · rw [Finset.insert_eq_of_mem hb, Finset.card_insert_of_notMem ha]
    simp [ha, hb]
  · have ha' : a ∉ insert b rest := by simp [hab, ha]
    rw [Finset.card_insert_of_notMem ha', Finset.card_insert_of_notMem hb]
    simp [ha, hb]

theorem clean_mono {s : Finset W} {I J : Finset (Fin 9)} {R C : Lab → W}
    (hc : clean s I R C) (hJI : J ⊆ I) : clean s J R C := by
  refine ⟨fun x hx => hc.1 x (hJI hx), ?_⟩
  intro r c hr hc' w hw
  exact hc.2 r c (fun p hp => hJI (hr p hp)) (fun p hp => hJI (hc' p hp)) w hw

theorem prune {k : ℕ} {s rest : Finset W} {I : Finset (Fin 9)} {R C : Lab → W}
    (h : live basicOps goal k s) (hc : clean s I R C) (v : W) :
    ∃ J ⊆ I, safe J R C v rest ∧ I.card ≤ J.card + 2*(if v ∈ rest then 1 else 0) := by
  by_cases hv : v ∈ rest
  · refine ⟨trim I R C v, trim_subset _ _ _ _, ?_, ?_⟩
    · intro _ p hp
      exact trim_avoids hp p.2
    · simpa [hv] using trim_card h hc v
  · exact ⟨I, Finset.Subset.rfl, fun h' => False.elim (hv h'), by simp [hv]⟩

-- Each additional use of a wire accounts for at most two of the surviving paths.
theorem bound {k : ℕ} {s : Finset W} {I : Finset (Fin 9)} {R C : Lab → W}
    (h : live basicOps goal k s) (hc : clean s I R C) : I.card + 2*s.card ≤ 2*k+2 := by
  induction k generalizing s I R C with
  | zero =>
    change s = {goal} at h
    subst s
    have hI : I = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have h0 := (hc.1 (i,0) hi).1
      have h1 := (hc.1 (i,1) hi).1
      simp only [Finset.mem_singleton] at h0 h1
      have eq := (row_owners (k := 0) rfl hc hi hi (h0.trans h1.symm)).2
      contradiction
    simp [hI]
  | succ k ih =>
    have orig := h
    rcases h with skip | ⟨a,ha,b,hb,hab,z,hz,hn,rest,hs,tail⟩
    · have hh := ih skip hc
      omega
    · subst s
      obtain ⟨K,hKI,sa,c1⟩ := prune (rest := rest) orig hc a
      obtain ⟨J,hJK,sb,c2⟩ := prune (rest := rest) orig (clean_mono hc hKI) b
      have hj := clean_mono hc (hJK.trans hKI)
      have ha' : safe J R C a rest := fun haa p hp => sa haa p (hJK hp)
      have hR (i) (hi : i ∈ J) : R (i,0) ≠ R (i,1) := by
        intro he
        have := (row_owners orig hj hi hi he).2
        contradiction
      have hC (i) (hi : i ∈ J) : C (i,0) ≠ C (i,1) := by
        intro he
        have := (col_owners orig hj hi hi he).2
        contradiction
      have hh := ih tail (step_clean hab hz hn tail hj hR hC ha' sb)
      have card := transition_card hab hn
      omega

theorem lower (C : Circuit) (hm : Monotone2 C) (hs : C.size ≤ 45) (hr : Represents A C) : False := by
  have h := bound (get_live_all C hm hr) initial_clean
  rw [input_card, Finset.card_univ, Fintype.card_fin] at h
  omega

end PEqualNP.Outside.L_meta_9488

theorem PEqualNP.Outside.L_meta_9488 : ¬ PEqualNP.Represents.RepSizeAtMost (fun a b : Fin 21 => decide (∃ i : Fin 7, ((a.val = i.val ∨ a.val = 7 + i.val) ∧ (b.val = (i.val + 1) % 7 ∨ b.val = 14 + i.val)) ∨ ((b.val = i.val ∨ b.val = 7 + i.val) ∧ (a.val = (i.val + 1) % 7 ∨ a.val = 14 + i.val)))) 45 := by
  rintro ⟨C,hm,hs,hr⟩
  exact PEqualNP.Outside.L_meta_9488.lower C hm hs hr
