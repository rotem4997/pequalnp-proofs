import Mathlib
import PEqualNP.Defs

-- The signed circuit compiler and restriction lemmas are adapted from
-- L_meta_10610, L_meta_8724 and L_meta_1449.
namespace PEqualNP.Outside.L_meta_11988.Signed

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Build: the goal is reached from the available wires in k binary steps. Live: the same,
-- keeping only the wires still needed, so a search may range over small sets.
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

-- The upper and lower halves represent opposite target labels on 16 pairs of assignments.
abbrev W := BitVec 32
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def goal : W := (-1 : BitVec 16) ++ (0 : BitVec 16)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

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

def differs (i : Fin 16) (w : W) : Prop :=
  w.getLsbD (16+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 16) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 16+i.val < 32 := by omega
  have hi' : i.val < 32 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

-- The search: pick two live wires, apply one of the four operations, and keep each operand
-- only if it is still needed; every live run is found, so a false search rules out a build.
-- Wires held up to complement, and what one binary gate reaches from them.
def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_mono {av av' : Finset W} (sub : av ⊆ av') {x : W} (h : holds av x) :
    holds av' x :=
  h.imp_right (Or.imp_right fun ⟨a,ha,e⟩ => ⟨a,sub ha,e⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 32 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 32)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

-- Running a circuit on the 32 rows at once, NOT gates cost nothing.
private def bit (k : Fin 32) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 32) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 32) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#32)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k goal) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : goal ≠ 0) zero)
    · exact False.elim ((by decide : goal ≠ ~~~0) ones)
    · exact ⟨t, .inl eq.symm, ht⟩
    · exact ⟨t, .inr (by rw [eq, BitVec.not_not]), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_mono (Finset.subset_insert _ _) (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩
-- A live run mapped through a bitwise homomorphism is a build of the mapped goal; a wire
-- mapped to zero saves its gate.
def SignedBuild (k : ℕ) (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ build basicOps z k av ∨ build basicOps (~~~z) k av

theorem sb_zero {av : Finset W} {z : W} (h : holds av z) : SignedBuild 0 av z := by
  rcases h with h | h | ⟨a,ha,rfl | rfl⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl ha))
  · exact .inr (.inr (.inr (by simpa only [BitVec.not_not,build] using ha)))

theorem sb_wait {av : Finset W} {z : W} {k : ℕ} (h : SignedBuild k av z) :
    SignedBuild (k+1) av z :=
  h.imp_right (Or.imp_right (Or.imp .inl .inl))

theorem sb_le {av : Finset W} {z : W} {k l : ℕ} (hkl : k ≤ l) (h : SignedBuild k av z) :
    SignedBuild l av z := by
  induction hkl with
  | refl => exact h
  | step _ ih => exact sb_wait ih

theorem sb_step {av : Finset W} {t a b z : W} {k : ℕ} (ha : a ∈ av) (hb : b ∈ av)
    (hne : a ≠ b) (hz : z ∈ basicOps a b) (h : SignedBuild k (insert z av) t) :
    SignedBuild (k+1) av t :=
  h.imp_right (Or.imp_right (Or.imp (.inr ⟨a,ha,b,hb,hne,z,hz,·⟩) (.inr ⟨a,ha,b,hb,hne,z,hz,·⟩)))

theorem sb_advance {av : Finset W} {z t : W} {k : ℕ} (hz : reachable av z)
    (next : ∀ av' : Finset W, av ⊆ av' → holds av' z → SignedBuild k av' t) :
    SignedBuild (k+1) av t := by
  rcases hz with h | ⟨a,ha,b,hb,hn,w,hw,ok⟩
  · exact sb_wait (next av (fun _ h => h) h)
  · exact sb_step ha hb hn hw (next (insert w av) (fun _ h => Finset.mem_insert_of_mem h) ok)

theorem mem_ops_reach {av : Finset W} {x y z : W} (hx : holds av x) (hy : holds av y)
    (hz : z ∈ basicOps x y) : reachable av z := by
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl
  · exact and_reach hx hy
  · exact or_reach hx hy
  · exact and_reach hx (holds_not hy)
  · exact and_reach hy (holds_not hx)

set_option maxRecDepth 5000 in
theorem mem_ops_zero {av : Finset W} {x y z : W} (hx : holds av x) (hy : holds av y)
    (hzero : x = 0 ∨ y = 0) (hz : z ∈ basicOps x y) : holds av z := by
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hz
  have hc : holds av (0 : W) := .inl rfl
  have absorb (v : W) : v &&& (~~~(0 : W)) = v := by
    exact (congrArg (fun u : W => v &&& u) (BitVec.not_zero (n := 32))).trans BitVec.and_allOnes
  rcases hzero with rfl | rfl <;> rcases hz with rfl|rfl|rfl|rfl <;>
    first | rwa [absorb] | simp_all

theorem live_transport {f : W → W} (hm : ∀ a b z, z ∈ basicOps a b → f z ∈ basicOps (f a) (f b))
    {g : W} {k : ℕ} {s av : Finset W} (run : live basicOps g k s)
    (hav : ∀ w ∈ s, holds av (f w)) : SignedBuild k av (f g) := by
  induction k generalizing s av with
  | zero =>
      change s = {g} at run
      exact sb_zero (hav g (by simp [run]))
  | succ k ih =>
      rcases run with skip | ⟨a,ha,b,hb,hn,z,hz,hout,r,he,tail⟩
      · exact sb_wait (ih skip hav)
      · apply sb_advance (mem_ops_reach (hav a ha) (hav b hb) (hm a b z hz))
        intro av' sub ok
        apply ih tail
        intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hr
        · exact ok
        · exact holds_mono sub (hav u (by simp [he,hr]))

theorem live_transport_save {f : W → W}
    (hm : ∀ a b z, z ∈ basicOps a b → f z ∈ basicOps (f a) (f b))
    {g p : W} {k : ℕ} {s av : Finset W} (run : live basicOps g k s)
    (hp : p ∈ s) (hpg : p ≠ g) (hzero : f p = 0)
    (hav : ∀ w ∈ s, holds av (f w)) : SignedBuild (k-1) av (f g) := by
  induction k generalizing s av with
  | zero =>
      change s = {g} at run
      exact False.elim (hpg (by simpa [run] using hp))
  | succ k ih =>
      simp only [Nat.add_sub_cancel] at *
      rcases run with skip | ⟨a,ha,b,hb,hn,z,hz,hout,r,he,tail⟩
      · exact sb_le (Nat.sub_le _ _) (ih skip hp hav)
      · have mapped := hm a b z hz
        have inOld : ∀ u ∈ r, holds av (f u) := fun u hu => hav u (by simp [he,hu])
        by_cases touches : p = a ∨ p = b
        · have zz : f a = 0 ∨ f b = 0 := touches.elim (fun h => .inl (h ▸ hzero)) (fun h => .inr (h ▸ hzero))
          have collapsed := mem_ops_zero (hav a ha) (hav b hb) zz mapped
          apply live_transport hm tail
          intro u hu
          rcases Finset.mem_insert.mp hu with rfl | hr
          · exact collapsed
          · exact inOld u hr
        · have pr : p ∈ r := by
            rw [he] at hp
            simpa [Finset.mem_insert, touches, not_or.mp touches |>.1, not_or.mp touches |>.2] using hp
          have pt : p ∈ insert z r := Finset.mem_insert_of_mem pr
          have pos : 0 < k := by
            by_contra! hk
            have eq : k = 0 := by omega
            subst k
            change insert z r = {g} at tail
            exact hpg (by simpa [tail] using pt)
          have cost : (k-1)+1 = k := by omega
          rw [← cost]
          apply sb_advance (mem_ops_reach (hav a ha) (hav b hb) mapped)
          intro av' sub ok
          apply ih tail pt
          intro u hu
          rcases Finset.mem_insert.mp hu with rfl | hr
          · exact ok
          · exact holds_mono sub (inOld u hr)

def changes (w : W) (r : Fin 16) : Bool := w.getLsbD (16+r.val) != w.getLsbD r.val

theorem goal_changes : ∀ k : Fin 16, differs k goal ∧ differs k (~~~goal) := by
  unfold differs
  decide +kernel
def liftBound (k : Nat) (ws : List W) := ∀ t, (t = goal ∨ t = ~~~goal) → build basicOps t k ws.toFinset → False
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem stepLift {k : Nat} {old new : List W} {p : W} {r : Fin 16} (proj : W → W)
    (hom : ∀ a b z, z ∈ basicOps a b → proj z ∈ basicOps (proj a) (proj b))
    (sign : proj goal = goal ∧ proj (~~~goal) = ~~~goal)
    (alone : ∀ w ∈ new, changes w r = true → w = p)
    (gone : proj p = 0)
    (incl : ∀ w ∈ new, proj w = 0 ∨ proj w ∈ old)
    (base : liftBound k old) : liftBound (k+1) new := by
  intro t ht h
  obtain ⟨u, sub, run⟩ := compress h
  have d : differs r t := ht.elim (fun e => e ▸ (goal_changes r).1) (fun e => e ▸ (goal_changes r).2)
  obtain ⟨w,hw,hd⟩ := live_separates (differs r) d (ops_differs r) run
  have mem (a : W) (ha : a ∈ u) := List.mem_toFinset.mp (sub ha)
  have e := alone w (mem w hw) (by simpa [changes, differs] using hd)
  have pt : proj t = t := ht.elim (fun e => e ▸ sign.1) (fun e => e ▸ sign.2)
  have nt : t ≠ 0 ∧ t ≠ ~~~0 := by rcases ht with rfl|rfl <;> decide +kernel
  have ne : p ≠ t := by intro h; exact nt.1 (pt ▸ (h ▸ gone))
  have sb := live_transport_save hom run (e ▸ hw) ne gone (av := old.toFinset) (by
    intro a ha
    rcases incl a (mem a ha) with h|h
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨_, List.mem_toFinset.mpr h, Or.inl rfl⟩))
  rw [pt] at sb
  change SignedBuild k old.toFinset t at sb
  rcases sb with h|h|h|h
  · exact nt.1 h
  · exact nt.2 h
  · exact base _ ht h
  · apply base _ _ h
    rcases ht with rfl|rfl
    · exact Or.inr rfl
    · exact Or.inl BitVec.not_not

def rowProj (i : Fin 32 → Fin 32) (w : W) : W :=
  (BitVec.ofBoolListLE (List.ofFn (fun k : Fin 32 => w[(i k).val]))).cast List.length_ofFn

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rowProj_bit (i : Fin 32 → Fin 32) (w : W) (j : ℕ) (hj : j < 32) :
    (rowProj i w)[j] = w[(i ⟨j, hj⟩).val] := by
  rw [← BitVec.getLsbD_eq_getElem hj]
  simp only [rowProj, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj, dite_true, Option.getD_some]

-- Restriction reads rows, so it commutes with the bitwise gate operations.
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rowProj_not (i : Fin 32 → Fin 32) (u : W) : rowProj i (~~~u) = ~~~rowProj i u :=
  BitVec.eq_of_getElem_eq fun j hj => by simp only [rowProj_bit, BitVec.getElem_not]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rowProj_ops (i : Fin 32 → Fin 32) (a b z : W) (hz : z ∈ basicOps a b) :
    rowProj i z ∈ basicOps (rowProj i a) (rowProj i b) := by
  have hand (u v : W) : rowProj i (u &&& v) = (rowProj i u &&& rowProj i v) :=
    BitVec.eq_of_getElem_eq fun j hj => by simp only [rowProj_bit, BitVec.getElem_and]
  have hor (u v : W) : rowProj i (u ||| v) = (rowProj i u ||| rowProj i v) :=
    BitVec.eq_of_getElem_eq fun j hj => by simp only [rowProj_bit, BitVec.getElem_or]
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
  rcases hz with rfl | rfl | rfl | rfl <;> simp [hand, hor, rowProj_not]


def vars3 : List W := [0xbbbb2222, 0xdddd4444, 0xeeee8888]

def triangleScan (t : W) : Nat → List W → Bool
  | 0, ws => ws.contains t
  | k + 1, ws => triangleScan t k ws ||
      (pairs ws).any (fun (a, b, _) =>
        (ops a b).any (fun z => triangleScan t k (z :: ws)))

theorem triangleScan_complete (t : W) (k : Nat) (ws : List W)
    (h : build basicOps t k ws.toFinset) : triangleScan t k ws = true := by
  induction k generalizing ws with
  | zero =>
    exact List.contains_iff_mem.mpr (List.mem_toFinset.mp h)
  | succ k ih =>
    simp only [triangleScan, Bool.or_eq_true]
    rcases h with h | ⟨a, ha, b, hb, hab, z, hz, run⟩
    · exact Or.inl (ih ws h)
    · obtain ⟨rest, hp, _⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have htail : triangleScan t k (z :: ws) = true :=
        ih _ (by simpa only [List.toFinset_cons] using run)
      refine Or.inr (List.any_eq_true.mpr ?_)
      rcases hp with hp | hp
      · exact ⟨(a, b, rest), hp, List.any_eq_true.mpr ⟨z, List.mem_toFinset.mp hz, htail⟩⟩
      · rw [ops_swap] at hz
        exact ⟨(b, a, rest), hp, List.any_eq_true.mpr ⟨z, List.mem_toFinset.mp hz, htail⟩⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem base : liftBound 3 vars3 := by
  intro t ht h
  have hs := triangleScan_complete t 3 vars3 h
  have ht' : triangleScan t 3 vars3 = false := by
    rcases ht with rfl | rfl <;> decide +kernel
  rw [ht'] at hs
  contradiction


def vars4 : List W := [0xbbbb2222, 0xdddd4444, 0xeeae8888, 0x400000]
def proj4 := rowProj (fun i => if i = 22 then 18 else i)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem lb4 (k : Nat) (old : liftBound k vars3) : liftBound (k+1) vars4 := by
  apply stepLift (p := 0x400000) (r := 6) proj4 _ _ _ _ _ old
  · exact rowProj_ops _
  · decide +kernel
  · intro w hw
    simp only [vars4, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl|rfl|rfl|rfl <;> decide +kernel
  · decide +kernel
  · intro w hw
    simp only [vars4, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl|rfl|rfl|rfl <;> decide +kernel

def vars5 : List W := [0xbbbb2222, 0xdddd4444, 0xeaae8888, 0x400000, 0x4000000]
def proj5 := rowProj (fun i => if i = 26 then 18 else i)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem lb5 (k : Nat) (old : liftBound k vars4) : liftBound (k+1) vars5 := by
  apply stepLift (p := 0x4000000) (r := 10) proj5 _ _ _ _ _ old
  · exact rowProj_ops _
  · decide +kernel
  · intro w hw
    simp only [vars5, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl|rfl|rfl|rfl|rfl <;> decide +kernel
  · decide +kernel
  · intro w hw
    simp only [vars5, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl|rfl|rfl|rfl|rfl <;> decide +kernel

def vars6 : List W := [0xbbbb2222, 0xdddd4444, 0xaaae8888, 0x400000, 0x4000000, 0x40000000]
def proj6 := rowProj (fun i => if i = 30 then 18 else i)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem lb6 (k : Nat) (old : liftBound k vars5) : liftBound (k+1) vars6 := by
  apply stepLift (p := 0x40000000) (r := 14) proj6 _ _ _ _ _ old
  · exact rowProj_ops _
  · decide +kernel
  · intro w hw
    simp only [vars6, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
  · decide +kernel
  · intro w hw
    simp only [vars6, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

def vars7 : List W := [0xbbbb2222, 0xdddd4444, 0x8aae8888, 0x400000, 0x4000000, 0x40000000, 0x20000000]
def proj7 := rowProj (fun i => if i = 29 then 17 else i)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem lb7 (k : Nat) (old : liftBound k vars6) : liftBound (k+1) vars7 := by
  apply stepLift (p := 0x20000000) (r := 13) proj7 _ _ _ _ _ old
  · exact rowProj_ops _
  · decide +kernel
  · intro w hw
    simp only [vars7, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
  · decide +kernel
  · intro w hw
    simp only [vars7, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

end PEqualNP.Outside.L_meta_11988.Signed

namespace PEqualNP.Outside.L_meta_11988.Witness
open PEqualNP.CircuitLowerBounds

def edge (x : Fin 7 → Bool) : Bool := decide (∃ i < ([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)
def gates : List Gate := [⟨.or,[0,1]⟩,⟨.or,[7,2]⟩,⟨.or,[5,6]⟩,⟨.or,[4,9]⟩,⟨.and,[8,10]⟩,⟨.and,[3,9]⟩,⟨.and,[5,6]⟩,⟨.or,[11,12]⟩,⟨.or,[14,13]⟩]

theorem basis : (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates.length = 9 := by
  simp [gates]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem correct : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates,15⟩ (List.ofFn x) = edge x := by
  decide +kernel

end PEqualNP.Outside.L_meta_11988.Witness

namespace PEqualNP.Outside.L_meta_11988.Signed
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_11988.Witness
def orig : List W := [0xbbbb2222, 0x400000, 0x4000000, 0x40000000, 0x20000000, 0xdddd4444, 0x8aae8888]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem samevars : orig.toFinset = vars7.toFinset := by decide +kernel
def row (k : Fin 32) (i : Fin 7) : Bool := (orig.getD i.val 0)[k.val]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rowSpec : ∀ k, edge (row k) = goal[k.val] := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem binaryLower (gs : List Gate) (o : Nat)
    (hg : ∀ g ∈ gs, legal g) (he : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = edge x) :
    8 ≤ binaryCost gs := by
  have init : ∀ u ∈ orig, holds orig.toFinset u := fun u hu => Or.inr (Or.inr ⟨u,List.mem_toFinset.mpr hu,Or.inl rfl⟩)
  have hr (k : Fin 32) : List.ofFn (row k) = orig.map (fun w => w[k.val]) := by
    apply List.ext_getElem (by rfl)
    intro i hi hj
    have hlt : i < orig.length := by simpa using hj
    simp only [row, List.getElem_ofFn, List.getElem_map, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hlt, Option.getD_some]
  obtain ⟨t,ht,run⟩ := compile gs o hg orig orig.toFinset init (by
    intro k
    change Circuit.eval ⟨gs,o⟩ (orig.map (fun w => w[k.val])) = goal[k.val]
    rw [← hr, he, rowSpec])
  by_contra! low
  have small : binaryCost gs ≤ 7 := by omega
  rw [samevars] at run
  have extend {a b : Nat} (h : a ≤ b) (r : build basicOps t a vars7.toFinset) : build basicOps t b vars7.toFinset := by
    induction h with
    | refl => exact r
    | step _ ih => exact Or.inl ih
  exact (lb7 _ (lb6 _ (lb5 _ (lb4 _ base)))) _ ht (extend small run)

end PEqualNP.Outside.L_meta_11988.Signed

open PEqualNP.Outside.L_meta_11988.Signed PEqualNP.Outside.L_meta_11988.Witness

theorem PEqualNP.Outside.L_meta_11988 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gs o legalGs _ he
  by_cases pres : ∃ g ∈ gs, g.op = .not
  · obtain ⟨g,hg,hn⟩ := pres
    have cut : binaryCost gs < gs.length := List.length_filter_lt_length_iff_exists.mpr ⟨g,hg,by simp [isBinary,hn]⟩
    have cost := PEqualNP.Outside.L_meta_11988.Signed.binaryLower gs o legalGs he
    exact ⟨gates,15,basis.1,by rw [basis.2]; omega, correct⟩
  · exact ⟨gs,o,(fun g hg => ⟨(legalGs g hg).1.imp_right (·.resolve_right fun h => pres ⟨g,hg,h⟩), (legalGs g hg).2⟩), Nat.le_refl _, he⟩
