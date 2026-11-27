import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_14714
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- ============================================================
-- 1. Polymorphic Wire / Reach / Run / Contraction (free NOT)
-- ============================================================

abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r

def comb {R} (d : Nat) (a b : Wire R) : Wire R :=
  if d = 0 then combine false a b
  else if d = 1 then combine true a b
  else if d = 2 then combine false a (inv b)
  else combine false (inv a) b

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (pool : List (Wire R)) (v : Wire R) : Prop :=
  v ∈ pool ∨ Constant v ∨ inv v ∈ pool

def supply {R} (pool xs : List (Wire R)) : Prop := ∀ a ∈ xs, Available pool a

def Reach {R} (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0, b => b = roots
  | p + 1, c => ∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R),
      Reach roots p bank ∧ Available bank a ∧ Available bank b ∧ c = combine op a b :: bank

theorem Reach.start {R} {roots : List (Wire R)} : Reach roots 0 roots := rfl

theorem Reach.two {R} {roots : List (Wire R)} {p bank a b} (op : Bool)
    (h : Reach roots p bank) (ha : Available bank a) (hb : Available bank b) :
    Reach roots (p + 1) (combine op a b :: bank) :=
  ⟨op, bank, a, b, h, ha, hb, rfl⟩

theorem Reach.ind {R} {roots : List (Wire R)} {motive : ∀ p bank, Reach roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (two : ∀ {p bank a b} (op : Bool) (h : Reach roots p bank) (ha : Available bank a)
      (hb : Available bank b), motive p bank h →
      motive (p + 1) (combine op a b :: bank) (Reach.two op h ha hb))
    {p bank} (h : Reach roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero => obtain rfl := h; exact start
  | succ p ih => obtain ⟨op, bank, a, b, h, ha, hb, rfl⟩ := h; exact two op h ha hb (ih h)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x :: xs else xs

def Run {R} (goal : Wire R) : Nat → List (Wire R) → Prop
  | 0, zs => List.Perm [goal] zs
  | s + 1, zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire R) (rest : List (Wire R)),
      op < 4 ∧ (a :: b :: rest).Perm zs ∧
      Run goal s (comb op a b :: kept ka a (kept kb b rest))

theorem Run.stop {R} {goal : Wire R} : Run goal 0 [goal] := List.Perm.refl _

theorem Run.perm {R} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run goal s xs) : Run goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op, ka, kb, a, b, rest, hd, q, h⟩ := h
    exact ⟨op, ka, kb, a, b, rest, hd, q.trans p, h⟩

theorem Run.two {R} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)}
    (op : Nat) (hd : op < 4) (ka kb : Bool)
    (h : Run goal s (comb op a b :: kept ka a (kept kb b rest))) :
    Run goal (s + 1) (a :: b :: rest) :=
  ⟨op, ka, kb, a, b, rest, hd, List.Perm.refl _, h⟩

theorem Run.ind {R} {goal : Wire R} {motive : ∀ s ws, Run goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run goal s xs),
      motive s xs h → motive s zs (Run.perm p h))
    (two : ∀ {s a b rest} (op : Nat) (hd : op < 4) (ka kb : Bool)
      (h : Run goal s (comb op a b :: kept ka a (kept kb b rest))),
      motive s _ h → motive (s + 1) (a :: b :: rest) (Run.two op hd ka kb h))
    {s ws} (h : Run goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    obtain ⟨op, ka, kb, a, b, rest, hd, p, h⟩ := h
    exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (ih h))

theorem mass_cons {R} (a : Wire R) (xs) : mass (a :: xs) = cost a + mass xs := by simp [mass]
theorem mass_append {R} (a b : List (Wire R)) : mass (a ++ b) = mass a + mass b := by simp [mass]
theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept, mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v, rfl⟩ := h; exact ⟨!v, rfl⟩

theorem inv_inv' {R} (a : Wire R) : inv (inv a) = a := by funext r; simp [inv]

theorem cost_inv {R} (a : Wire R) : cost (inv a) = cost a := by
  have hiff : Constant (inv a) ↔ Constant a := ⟨fun h => inv_inv' a ▸ inv_constant h, inv_constant⟩
  by_cases h : Constant a
  · simp only [cost, if_pos h, if_pos (hiff.mpr h)]
  · simp only [cost, if_neg h, if_neg (fun x => h (hiff.mp x))]

theorem avail_inv {R} {bank : List (Wire R)} {a} (h : Available bank a) : Available bank (inv a) := by
  rcases h with h | h | h
  · exact Or.inr (Or.inr ((inv_inv' a).symm ▸ h))
  · exact Or.inr (Or.inl (inv_constant h))
  · exact Or.inl h

theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v, rfl⟩ := h; obtain ⟨w, rfl⟩ := g; cases op <;> exact ⟨_, rfl⟩

theorem from_constant {R} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available bank a) (hb : Available bank b) :
    Available bank (combine op a b) := by
  rcases h with ⟨v, rfl⟩ | ⟨v, rfl⟩
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)

theorem available_cons {R} {bank v} (w : Wire R) (h : Available bank v) :
    Available (w :: bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (List.mem_cons_of_mem _))

theorem extend_two {R} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) :
    ∃ q next, Reach roots q next ∧ Available next (combine op a b) ∧
      (∀ v, Available bank v → Available next v) ∧
      q + cost a + cost b ≤ p + 1 + cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p, bank, hp, from_constant op c ha hb, fun _ h => h, ?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost, ca, cb, both_constant op ca cb]
    · simp [cost, ca, cb]
    · simp [cost, ca, cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p + 1, _, Reach.two op hp ha hb, Or.inl (by simp), fun _ h => available_cons _ h,
      by simp [cost, ca, cb]⟩

theorem op_four {d : Nat} (h : d < 4) : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega

theorem comb_prime {R} {bank : List (Wire R)} {d a b} (hd : d < 4)
    (ha : Available bank a) (hb : Available bank b) :
    ∃ op x y, comb d a b = combine op x y ∧ Available bank x ∧ Available bank y ∧
      cost x = cost a ∧ cost y = cost b := by
  rcases op_four hd with rfl | rfl | rfl | rfl
  · exact ⟨false, a, b, rfl, ha, hb, rfl, rfl⟩
  · exact ⟨true, a, b, rfl, ha, hb, rfl, rfl⟩
  · exact ⟨false, a, inv b, rfl, ha, avail_inv hb, rfl, cost_inv b⟩
  · exact ⟨false, inv a, b, rfl, avail_inv ha, hb, cost_inv a, rfl⟩

theorem extend_comb {R} (roots : List (Wire R)) {p bank a b} (d) (hd : d < 4)
    (hp : Reach roots p bank) (ha : Available bank a) (hb : Available bank b) :
    ∃ q next, Reach roots q next ∧ Available next (comb d a b) ∧
      (∀ v, Available bank v → Available next v) ∧
      q + cost a + cost b ≤ p + 1 + cost (comb d a b) := by
  obtain ⟨op, x, y, e, hx, hy, cx, cy⟩ := comb_prime hd ha hb
  rw [e, ← cx, ← cy]
  exact extend_two roots op hp hx hy

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x = a ∨ x ∈ xs := by cases k <;> simp_all [kept]

theorem contraction {R} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach roots p bank) (hs : supply bank ws) :
    ∃ q next, Reach roots q next ∧ Available next goal ∧ q + mass ws ≤ p + s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop => exact ⟨p, bank, hp, hs _ (by simp), by simp [mass, cost, nc]⟩
  | perm eq _ ih =>
    have hsub : supply bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q, W, hW, hv, hl⟩ := ih hp hsub
    exact ⟨q, W, hW, hv, by simpa only [mass, ← (eq.map cost).sum_eq] using hl⟩
  | @two s a b rest op hd ka kb _ ih =>
    obtain ⟨r, T, hT, hz, inc, le⟩ := extend_comb roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht : supply T (comb op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v; apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q, W, hW, hv, hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q, W, hW, hv, ?_⟩
    rw [mass_cons, mass_cons]
    omega

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S := fun r => a (rows r)

theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by cases k <;> simp [kept]

theorem restrict_comb {R S : Type} (rows : S → R) (d) (a b : Wire R) :
    restrictRows rows (comb d a b) = comb d (restrictRows rows a) (restrictRows rows b) := by
  unfold comb; split_ifs <;> rfl

theorem restrict_run {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws) :
    Run (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons, restrict_kept, restrict_comb] at ih ⊢
    exact Run.two op hd ka kb ih

theorem projected_bound {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach roots p bank) (hs : supply bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach roots q bs → Available bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p + s := by
  obtain ⟨q, bs, hq, ht, hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega

theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons, List.length_cons, cost, if_pos ha, ih (fun x hx => hc x (by simp [hx]))]
    omega

-- Circuit execution directly to Reach (for any row type R)
def isNot (g : Gate) : Bool := match g.op with | .not => true | _ => false

def evalWire {R} (w : List (Wire R)) (g : Gate) : Wire R :=
  fun r => g.op.eval (g.inputs.map fun i => (w.getD i (fun _ => false)) r)

def execWires {R} (gs : List Gate) (w : List (Wire R)) : List (Wire R) :=
  gs.foldl (fun l g => l ++ [evalWire l g]) w

theorem execWires_at {R} (gs : List Gate) (w : List (Wire R)) (r : R) :
    (execWires gs w).map (fun f => f r) =
    gs.foldl (fun (l : List Bool) g => l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)]) (w.map (fun f => f r)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execWires gs (w ++ [evalWire w g])).map _ = _
    rw [ih]
    simp only [List.foldl_cons, List.map_append, List.map_singleton]
    congr 2; congr 1; unfold evalWire; congr 1
    apply List.map_congr_left; intro i _
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases w[i]? <;> rfl

theorem avail_getD {R} {bank w : List (Wire R)} (hs : supply bank w) (i : Nat) :
    Available bank (w.getD i (fun _ => false)) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (Or.inl ⟨false, rfl⟩)
  | some f => exact hs f (List.mem_of_getElem? h)

theorem circuit_reach {R} (roots : List (Wire R)) (gs : List Gate) (w : List (Wire R))
    (p : Nat) (bank : List (Wire R))
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hr : Reach roots p bank) (hs : supply bank w) :
    ∃ q next, q ≤ p + gs.countP (fun g => !isNot g) ∧ Reach roots q next ∧ supply next (execWires gs w) := by
  induction gs generalizing w p bank with
  | nil => exact ⟨p, bank, by simp, hr, hs⟩
  | cons g gs ih =>
    obtain ⟨ho, hl⟩ := legal g (by simp)
    have hstep : ∃ p' bank', p' ≤ p + (if isNot g then 0 else 1) ∧
        Reach roots p' bank' ∧ supply bank' (w ++ [evalWire w g]) := by
      have addAvail {v : Wire R} (hv : Available bank v) :
          ∃ p' bank', p' ≤ p + (if isNot g then 0 else 1) ∧ Reach roots p' bank' ∧ supply bank' (w ++ [v]) :=
        ⟨p, bank, by omega, hr, fun a ha => by rcases List.mem_append.mp ha with h | h; exact hs a h; exact List.mem_singleton.mp h ▸ hv⟩
      obtain ⟨op, l⟩ := g
      rcases ho with rfl | rfl | rfl
      · cases l with
        | nil => exact addAvail (Or.inr (Or.inl ⟨true, by funext r; simp [evalWire, GateOp.eval]⟩))
        | cons i l =>
          cases l with
          | nil =>
            have eq : evalWire w ⟨.and, [i]⟩ = w.getD i (fun _ => false) := by
              funext r; simp [evalWire, GateOp.eval]
            rw [eq]; exact addAvail (avail_getD hs i)
          | cons j l =>
            cases l with
            | cons _ _ => simp at hl
            | nil =>
              have eq : evalWire w ⟨.and, [i, j]⟩ = combine false (w.getD i (fun _ => false)) (w.getD j (fun _ => false)) := by
                funext r; simp [evalWire, GateOp.eval, combine]
              rw [eq]
              refine ⟨p + 1, _, by simp [isNot], Reach.two false hr (avail_getD hs i) (avail_getD hs j), ?_⟩
              intro a ha; rcases List.mem_append.mp ha with h | h
              · exact available_cons _ (hs a h)
              · rw [List.mem_singleton.mp h]; exact Or.inl (by simp)
      · cases l with
        | nil => exact addAvail (Or.inr (Or.inl ⟨false, by funext r; simp [evalWire, GateOp.eval]⟩))
        | cons i l =>
          cases l with
          | nil =>
            have eq : evalWire w ⟨.or, [i]⟩ = w.getD i (fun _ => false) := by
              funext r; simp [evalWire, GateOp.eval]
            rw [eq]; exact addAvail (avail_getD hs i)
          | cons j l =>
            cases l with
            | cons _ _ => simp at hl
            | nil =>
              have eq : evalWire w ⟨.or, [i, j]⟩ = combine true (w.getD i (fun _ => false)) (w.getD j (fun _ => false)) := by
                funext r; simp [evalWire, GateOp.eval, combine]
              rw [eq]
              refine ⟨p + 1, _, by simp [isNot], Reach.two true hr (avail_getD hs i) (avail_getD hs j), ?_⟩
              intro a ha; rcases List.mem_append.mp ha with h | h
              · exact available_cons _ (hs a h)
              · rw [List.mem_singleton.mp h]; exact Or.inl (by simp)
      · cases l with
        | nil => exact addAvail (Or.inr (Or.inl ⟨true, by funext r; simp [evalWire, GateOp.eval]⟩))
        | cons i l =>
          have eq : evalWire w ⟨.not, i :: l⟩ = inv (w.getD i (fun _ => false)) := by
            funext r; simp [evalWire, GateOp.eval, inv]
          rw [eq]; exact addAvail (avail_inv (avail_getD hs i))
    obtain ⟨p', bank', hp', hr', hs'⟩ := hstep
    obtain ⟨q, next, hq, hreq, hsup⟩ := ih (w ++ [evalWire w g]) p' bank' (fun a ha => legal a (by simp [ha])) hr' hs'
    refine ⟨q, next, ?_, hreq, hsup⟩
    rw [List.countP_cons]; cases hn : isNot g <;> simp [hn] at hp' ⊢ <;> omega

-- ============================================================
-- 2. BitVec N (polymorphic for N=64 and N=128) Live & Lower
-- ============================================================

section BitVecEngine
variable {N : Nat} [NeZero N]

def zeroBV : BitVec N := 0
def oneBV : BitVec N := BitVec.allOnes N
def negBV (a : BitVec N) : BitVec N := ~~~a
def binBV (d : Nat) (a b : BitVec N) : BitVec N :=
  if d = 0 then a &&& b else if d = 1 then a ||| b else if d = 2 then a &&& ~~~b else ~~~a &&& b
def properBV (a : BitVec N) : Prop := a ≠ zeroBV ∧ a ≠ oneBV
def flipOp (d : Nat) := if d = 2 then 3 else if d = 3 then 2 else d
def bitBV (i : Fin N) (a : BitVec N) : Bool := a.getLsbD i.val

theorem bitBV_zero (i : Fin N) : bitBV i (zeroBV (N := N)) = false := by simp [bitBV, zeroBV]
theorem bitBV_one (i : Fin N) : bitBV i (oneBV (N := N)) = true := by
  unfold bitBV oneBV; rw [BitVec.getLsbD_allOnes]; simp
theorem bitBV_neg (i : Fin N) (a : BitVec N) : bitBV i (negBV a) = !(bitBV i a) := by
  simp [bitBV, negBV, i.isLt]
theorem bitBV_bin (i : Fin N) (d : Nat) (a b : BitVec N) :
    bitBV i (binBV d a b) =
      (if d = 0 then bitBV i a && bitBV i b else if d = 1 then bitBV i a || bitBV i b else
       if d = 2 then bitBV i a && !(bitBV i b) else !(bitBV i a) && bitBV i b) := by
  unfold binBV; split_ifs <;> simp [bitBV, i.isLt]
theorem bitBV_ext {a b : BitVec N} (h : ∀ i : Fin N, bitBV i a = bitBV i b) : a = b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j, hj⟩

theorem binBV_flip {d : Nat} (h : d < 4) (a b : BitVec N) :
    binBV d a b = binBV (flipOp d) b a := by
  rcases op_four h with rfl | rfl | rfl | rfl <;> simp [binBV, flipOp, BitVec.and_comm, BitVec.or_comm]
theorem flipOp_lt {d : Nat} (h : d < 4) : flipOp d < 4 := by
  rcases op_four h with rfl | rfl | rfl | rfl <;> decide

def nrmBV (a : BitVec N) : BitVec N := if a.getLsbD 0 then negBV a else a
theorem nrmBV_bit0 (a : BitVec N) : (nrmBV a).getLsbD 0 = false := by
  have hpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  cases h : a.getLsbD 0 <;>
    simp only [nrmBV, negBV, h, Bool.false_eq_true, ite_true, ite_false, BitVec.getLsbD_not, hpos, decide_true, Bool.true_and, Bool.not_true]
theorem nrmBV_id {a : BitVec N} (h : a.getLsbD 0 = false) : nrmBV a = a := by simp [nrmBV, h]
theorem nrmBV_neg (a : BitVec N) : nrmBV (negBV a) = nrmBV a := by
  have hpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  cases h : a.getLsbD 0 <;>
    simp only [nrmBV, negBV, h, Bool.false_eq_true, ite_true, ite_false, BitVec.getLsbD_not, hpos, decide_true, Bool.true_and, Bool.not_true, Bool.not_false, BitVec.not_not]
theorem properBV_neg {a : BitVec N} (h : properBV (negBV a)) : properBV a := by
  refine ⟨?_, ?_⟩
  · rintro rfl; exact h.2 (by simp [negBV, zeroBV, oneBV])
  · rintro rfl; exact h.1 (by simp [negBV, zeroBV, oneBV])
theorem properBV_nrm {a : BitVec N} (h : properBV (nrmBV a)) : properBV a := by
  unfold nrmBV at h
  split at h
  · exact properBV_neg h
  · exact h
theorem nrmBV_ne_one (a : BitVec N) : nrmBV a ≠ oneBV := by
  intro h; have hpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have h1 := nrmBV_bit0 a; rw [h] at h1; simp [oneBV, hpos] at h1

def primeBV (d : Bool) (a b : BitVec N) : BitVec N := if d then a ||| b else a &&& b
theorem bitBV_prime (i : Fin N) (d : Bool) (a b : BitVec N) :
    bitBV i (primeBV d a b) = (if d then bitBV i a || bitBV i b else bitBV i a && bitBV i b) := by
  cases d <;> simp [primeBV, bitBV]

theorem nrmBV_prime (d : Bool) (a b : BitVec N) :
    ∃ e, e < 4 ∧ nrmBV (primeBV d a b) = binBV e (nrmBV a) (nrmBV b) := by
  have hpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  refine ⟨if d then (if a.getLsbD 0 then (if b.getLsbD 0 then 0 else 2) else (if b.getLsbD 0 then 3 else 1))
    else (if a.getLsbD 0 then (if b.getLsbD 0 then 1 else 3) else (if b.getLsbD 0 then 2 else 0)), ?_, ?_⟩
  · split_ifs <;> omega
  · apply bitBV_ext; intro i
    cases d <;> cases ha : a.getLsbD 0 <;> cases hb : b.getLsbD 0 <;>
      simp only [nrmBV, primeBV, binBV, negBV, bitBV, ha, hb, BitVec.getLsbD_and, BitVec.getLsbD_or,
        BitVec.getLsbD_not, i.isLt, hpos, decide_true, Bool.true_and, Bool.false_and, Bool.and_true,
        Bool.and_false, Bool.false_or, Bool.or_false, Bool.true_or, Bool.or_true, Bool.false_eq_true,
        Bool.not_true, Bool.not_false, ite_true, ite_false, show (3 : Nat) ≠ 2 by decide,
        OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, Nat.one_ne_zero] <;>
      cases a.getLsbD i.val <;> cases b.getLsbD i.val <;> rfl

def LiveBV (target : BitVec N) : Nat → Finset (BitVec N) → Prop
  | 0, S => S = {target} ∧ properBV target
  | k + 1, S => ∃ (U : Finset (BitVec N)) (a b : BitVec N) (d : Nat),
      d < 4 ∧ S = insert a (insert b U) ∧ properBV a ∧ properBV b ∧ a ≠ b ∧
      binBV d a b ∉ insert a (insert b U) ∧ LiveBV target k (insert (binBV d a b) U)

theorem LiveBV.stop {target : BitVec N} (hp : properBV target) : LiveBV target 0 {target} := ⟨rfl, hp⟩
theorem LiveBV.binary {target : BitVec N} {k : Nat} {U : Finset (BitVec N)} {a b : BitVec N} {d : Nat}
    (hd : d < 4) (ha : properBV a) (hb : properBV b) (hab : a ≠ b)
    (hfresh : binBV d a b ∉ insert a (insert b U)) (tail : LiveBV target k (insert (binBV d a b) U)) :
    LiveBV target (k + 1) (insert a (insert b U)) :=
  ⟨U, a, b, d, hd, rfl, ha, hb, hab, hfresh, tail⟩

theorem LiveBV.ind {target : BitVec N} {motive : ∀ (k : Nat) (S : Finset (BitVec N)), LiveBV target k S → Prop}
    (stop : ∀ (hp : properBV target), motive 0 {target} (LiveBV.stop hp))
    (binary : ∀ {k : Nat} {U : Finset (BitVec N)} {a b : BitVec N} {d : Nat} (hd : d < 4)
      (ha : properBV a) (hb : properBV b) (hab : a ≠ b)
      (hfresh : binBV d a b ∉ insert a (insert b U)) (tail : LiveBV target k (insert (binBV d a b) U)),
      motive k (insert (binBV d a b) U) tail →
      motive (k + 1) (insert a (insert b U)) (LiveBV.binary hd ha hb hab hfresh tail))
    {k : Nat} {S : Finset (BitVec N)} (h : LiveBV target k S) : motive k S h := by
  induction k generalizing S with
  | zero => obtain ⟨rfl, hp⟩ := h; exact stop hp
  | succ k ih => obtain ⟨U, a, b, d, hd, rfl, ha, hb, hab, hf, tail⟩ := h; exact binary hd ha hb hab hf tail (ih tail)

theorem liveBV_proper {target : BitVec N} {k S} (h : LiveBV target k S) : ∀ a ∈ S, properBV a := by
  induction h using LiveBV.ind with
  | stop hp => simpa using hp
  | binary _ ha hb _ _ _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha, hb, fun a h => ih a (Finset.mem_insert_of_mem h)⟩

theorem liveBV_size {target : BitVec N} {k S} (h : LiveBV target k S) : S.card ≤ k + 1 := by
  induction h using LiveBV.ind with
  | stop _ => simp
  | @binary k U a b d _ _ _ _ hf _ ih =>
    have hu : binBV d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

def representedBV (w : List (BitVec N)) (v : BitVec N) : Prop := v ∈ w ∨ ¬properBV v
def ReprBV (w : List (BitVec N)) (v : BitVec N) : Prop := representedBV w (nrmBV v)
def witnessBV (w : List (BitVec N)) (z : BitVec N) : Prop :=
  ∃ d a b, d < 4 ∧ a ∈ w ∧ b ∈ w ∧ properBV a ∧ properBV b ∧ a ≠ b ∧ z = binBV d a b

private lemma binBV_laws (a : BitVec N) :
    binBV 0 a oneBV = a ∧ binBV 1 a zeroBV = a ∧
    binBV 0 a zeroBV = zeroBV ∧ binBV 1 a oneBV = oneBV ∧
    binBV 0 a a = a ∧ binBV 1 a a = a ∧ binBV 2 a a = zeroBV ∧ binBV 3 a a = zeroBV ∧
    binBV 2 a zeroBV = a ∧ binBV 3 zeroBV a = a ∧ binBV 2 zeroBV a = zeroBV ∧ binBV 3 a zeroBV = zeroBV ∧
    binBV 0 zeroBV a = zeroBV ∧ binBV 1 zeroBV a = a ∧
    binBV 0 oneBV a = a ∧ binBV 1 oneBV a = oneBV := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply bitBV_ext <;> intro i <;>
    simp [bitBV_bin, bitBV_zero, bitBV_one]

private lemma operandBV_cases {w : List (BitVec N)} {a : BitVec N} (h : representedBV w a) :
    a = zeroBV ∨ a = oneBV ∨ a ∈ w ∧ properBV a := by
  by_cases hz : a = zeroBV; · exact Or.inl hz
  by_cases ho : a = oneBV; · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz, ho⟩), hz, ho⟩)

private lemma binBV_rep {w : List (BitVec N)} {a b : BitVec N} (d : Nat) (hd : d < 4)
    (ha : representedBV w a) (hb : representedBV w b) (no : a ≠ oneBV ∧ b ≠ oneBV) :
    representedBV w (binBV d a b) ∨ witnessBV w (binBV d a b) := by
  have rz : representedBV w zeroBV := Or.inr (fun h => h.1 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := binBV_laws a
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := binBV_laws b
  by_cases he : a = b
  · subst b; left
    rcases op_four hd with rfl | rfl | rfl | rfl
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases operandBV_cases ha with rfl | rfl | ⟨ham, hap⟩
  · left; rcases op_four hd with rfl | rfl | rfl | rfl
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · exact absurd rfl no.1
  rcases operandBV_cases hb with rfl | rfl | ⟨hbm, hbp⟩
  · left; rcases op_four hd with rfl | rfl | rfl | rfl
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · exact absurd rfl no.2
  exact Or.inr ⟨d, a, b, hd, ham, hbm, hap, hbp, he, rfl⟩

theorem primeBV_rep {w : List (BitVec N)} {a b : BitVec N} (d : Bool)
    (ha : ReprBV w a) (hb : ReprBV w b) :
    ReprBV w (primeBV d a b) ∨ witnessBV w (nrmBV (primeBV d a b)) := by
  obtain ⟨e, he, eq⟩ := nrmBV_prime d a b
  unfold ReprBV; rw [eq]
  exact binBV_rep e he ha hb ⟨nrmBV_ne_one a, nrmBV_ne_one b⟩

theorem reprBV_const {w : List (BitVec N)} {v : BitVec N} (h : v = zeroBV ∨ v = oneBV) : ReprBV w v := by
  refine Or.inr fun hp => ?_
  have := properBV_nrm hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl

private lemma pullBV_gate {target : BitVec N} {w : List (BitVec N)} {z : BitVec N} {k S c}
    (h : LiveBV target k S) (hz : representedBV w z ∨ (c = 1 ∧ witnessBV w z))
    (sub : ∀ a ∈ S, a ∈ w ++ [z]) :
    ∃ k' S', k' ≤ k + c ∧ LiveBV target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k, S, by omega, h, ?_⟩
      intro a ha; rcases (by simpa using sub a ha : a ∈ w ∨ a = z) with hu | rfl
      · exact hu
      · exact hw
    · have hp := liveBV_proper h z hm
      rcases hz with hr | ⟨rfl, d, a, b, hd, ha, hb, pa, pb, hab, eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (binBV d a b)
        have ht : LiveBV target k (insert (binBV d a b) U) := by simpa [U, Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := fun v hv => by
          obtain ⟨hne, hmv⟩ := Finset.mem_erase.mp hv; simpa [hne] using sub v hmv
        have hf : binBV d a b ∉ insert a (insert b U) := by
          intro hh; rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_, _, Nat.le_refl _, LiveBV.binary hd pa pb hab hf ht, by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k, S, by omega, h, ?_⟩
    intro a ha; have hn : a ≠ z := fun hh => hm (hh ▸ ha); simpa [hn] using sub a ha

def observeBV (a : BitVec N) : Wire (Fin N) := fun r => bitBV r a
def tableBV (f : Wire (Fin N)) : BitVec N :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn

theorem bitBV_table (f : Wire (Fin N)) (r : Fin N) : bitBV r (tableBV f) = f r := by
  simp only [bitBV, tableBV, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [r.isLt]
theorem tableBV_observe (v : BitVec N) : tableBV (observeBV v) = v :=
  bitBV_ext fun r => bitBV_table (observeBV v) r
theorem observeBV_table (f : Wire (Fin N)) : observeBV (tableBV f) = f :=
  funext fun r => bitBV_table f r
theorem obsBV_neg (a : BitVec N) : observeBV (negBV a) = inv (observeBV a) :=
  funext fun r => bitBV_neg r a
theorem obsBV_bin (d : Nat) (a b : BitVec N) : observeBV (binBV d a b) = comb d (observeBV a) (observeBV b) := by
  funext r; simp only [observeBV, bitBV_bin, comb]; split_ifs <;> rfl

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl
theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α) (hn : l.Nodup) (ha : a ∉ l) :
    (kept k a l).Nodup := by cases k <;> simp [kept, hn, ha]
theorem kept_fin {α : Type} [DecidableEq α] (k : Bool) (a : α) (l : List α) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by cases k <;> simp [kept]

theorem list_runBV {T : BitVec N} {k S} (h : LiveBV T k S) (v : List (BitVec N))
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run (observeBV T) k (v.map observeBV) := by
  classical
  induction h using LiveBV.ind generalizing v with
  | stop _ =>
    have eq : [T].Perm v := List.perm_of_nodup_nodup_toFinset_eq (by simp) hv (by simpa [eqv])
    exact Run.perm (eq.map _) Run.stop
  | @binary k U a b d hd _ _ hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid, kept, h, hab, ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin, kept_fin, er]; ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j = a <;>
        by_cases bj : j = b <;> simp_all [ka, kb]
    have hf : binBV d a b ∉ tail := fun hz =>
      fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (binBV d a b :: tail) (List.nodup_cons.mpr ⟨hf, nd⟩) (by simp [ht])
    change Run _ _ ((binBV d a b :: kept ka a (kept kb b rest)).map observeBV) at progress
    rw [List.map_cons, map_kept, map_kept, obsBV_bin] at progress
    have perm : (a :: b :: rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab, ar, br, hr]) hv
      ext j; by_cases ja : j = a <;> by_cases jb : j = b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d hd ka kb progress)

theorem tableBV_inv (f : Wire (Fin N)) : tableBV (inv f) = negBV (tableBV f) := by
  rw [← tableBV_observe (negBV (tableBV f)), obsBV_neg, observeBV_table]
theorem tableBV_prime (d : Bool) (f g : Wire (Fin N)) :
    tableBV (combine d f g) = primeBV d (tableBV f) (tableBV g) := by
  apply bitBV_ext; intro r; rw [bitBV_table, bitBV_prime, bitBV_table, bitBV_table]; cases d <;> rfl

theorem availableBV_rep {bank : List (Wire (Fin N))} {a} (h : Available bank a) :
    ReprBV ((bank.map tableBV).map nrmBV) (tableBV a) := by
  rcases h with hm | ⟨b, rfl⟩ | hm
  · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hm))
  · apply reprBV_const; cases b
    · exact Or.inl (bitBV_ext fun i => (bitBV_table _ i).trans (bitBV_zero i).symm)
    · exact Or.inr (bitBV_ext fun i => (bitBV_table _ i).trans (bitBV_one i).symm)
  · refine Or.inl ?_; rw [← nrmBV_neg, ← tableBV_inv a]
    exact List.mem_map_of_mem (List.mem_map_of_mem hm)

theorem reachBV_live_sub {roots : List (Wire (Fin N))} {p bank}
    (h : Reach roots p bank) {T k S} (run : LiveBV T k S)
    (sub : ∀ a ∈ S, a ∈ (bank.map tableBV).map nrmBV) :
    ∃ l V, l ≤ p + k ∧ LiveBV T l V ∧ ∀ a ∈ V, a ∈ (roots.map tableBV).map nrmBV := by
  induction h using Reach.ind generalizing k S with
  | start => exact ⟨k, S, by omega, run, sub⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons, List.map_cons, tableBV_prime] at sub
    have rep := primeBV_rep d (availableBV_rep ha) (availableBV_rep hb)
    obtain ⟨k', S', hk, run', sub'⟩ := pullBV_gate (c := 1) run (rep.imp id (fun h => ⟨rfl, h⟩))
      (fun a hm => by simpa [or_comm] using sub a hm)
    obtain ⟨l, V, hl, hr, hs⟩ := ih run' sub'
    exact ⟨l, V, by omega, hr, hs⟩

def plainWordBV (a : BitVec N) : Bool := !(a.getLsbD 0)
theorem nrmBV_map {w : List (BitVec N)} (h : w.all plainWordBV = true) : w.map nrmBV = w := by
  have e : w.map nrmBV = w.map id := List.map_congr_left fun a ha =>
    nrmBV_id (by simpa [plainWordBV] using List.all_eq_true.mp h a ha)
  rw [e, List.map_id]

theorem reachBV_live {roots : List (BitVec N)} {p bank T}
    (hp : properBV T) (nT : plainWordBV T = true) (nR : roots.all plainWordBV = true)
    (h : Reach (roots.map observeBV) p bank) (hit : Available bank (observeBV T)) :
    ∃ k S, k ≤ p ∧ LiveBV T k S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := availableBV_rep hit
  rw [tableBV_observe] at hm
  unfold ReprBV at hm
  rw [nrmBV_id (by simpa [plainWordBV] using nT)] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l, V, hl, hr, hs⟩ := reachBV_live_sub h (LiveBV.stop hp) (by simpa using mem)
  refine ⟨l, V, by omega, hr, ?_⟩
  have e : (roots.map observeBV).map tableBV = roots := by
    simp [List.map_map, Function.comp_def, tableBV_observe]
  rw [e, nrmBV_map nR] at hs
  exact hs

theorem liveBV_row_diff {T : BitVec N} {k S} (h : LiveBV T k S) {r s : Fin N}
    (diff : bitBV r T ≠ bitBV s T) : ∃ a ∈ S, bitBV r a ≠ bitBV s a := by
  induction h using LiveBV.ind with
  | stop _ => exact ⟨_, by simp, diff⟩
  | @binary k U a b d _ _ _ _ _ _ ih =>
    obtain ⟨v, hv, hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bitBV r a = bitBV s a
      · refine ⟨b, by simp, fun beq => hd (by rw [bitBV_bin, bitBV_bin, aeq, beq])⟩
      · exact ⟨a, by simp, aeq⟩
    · exact ⟨v, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu), hd⟩

theorem rawBV_required {T : BitVec N} {k S} (h : LiveBV T k S) (roots : List (BitVec N)) (a : BitVec N)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Fin N) (diff : bitBV r T ≠ bitBV s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bitBV r v = bitBV s v) : a ∈ S := by
  obtain ⟨v, hv, hd⟩ := liveBV_row_diff h diff
  by_cases veq : v = a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def LowerBV (roots : List (BitVec N)) (T : BitVec N) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map observeBV) p bank → Available bank (observeBV T) → L ≤ p

def ImpossibleBV (T : BitVec N) (cap : Nat) (S : Finset (BitVec N)) : Prop :=
  ∀ k, k ≤ cap → ¬LiveBV T k S

def EssentialBV (T : BitVec N) (roots : List (BitVec N)) (a : BitVec N) : Prop :=
  ∃ r s : Fin N, bitBV r T ≠ bitBV s T ∧ ∀ v ∈ roots, v ≠ a → bitBV r v = bitBV s v

theorem lowerBV_impossible {roots : List (BitVec N)} {T : BitVec N} {L : Nat}
    (hp : properBV T) (nT : plainWordBV T = true) (nR : roots.all plainWordBV = true)
    (essential : ∀ a ∈ roots, EssentialBV T roots a)
    (noRun : ImpossibleBV T L roots.toFinset) : LowerBV roots T (L + 1) := by
  intro p bank h ha
  obtain ⟨k, S, hk, run, hs⟩ := reachBV_live hp nT nR h ha
  have he : roots.toFinset = S := by
    ext a; rw [List.mem_toFinset]
    refine ⟨fun hm => ?_, hs a⟩
    obtain ⟨r, s, hd, iso⟩ := essential _ hm
    exact rawBV_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k (by omega) (he.symm ▸ run)

theorem observeBV_proper {v : BitVec N} (hv : properBV v) : ¬Constant (observeBV v) := by
  rintro ⟨b, h⟩
  have hr : representedBV ([] : List (BitVec N)) v := by
    cases b
    · exact Or.inr fun hp => hp.1 (bitBV_ext fun i => (congrFun h i).trans (bitBV_zero i).symm)
    · exact Or.inr fun hp => hp.2 (bitBV_ext fun i => (congrFun h i).trans (bitBV_one i).symm)
  exact (hr.resolve_left (by simp)) hv

end BitVecEngine

theorem lowerBV_slice {N M : Nat} [NeZero N] [NeZero M]
    {roots : List (BitVec N)} {other : List (BitVec M)} {T : BitVec N} {G : BitVec M}
    (pT : properBV T) (nT : plainWordBV T = true) (nR : roots.all plainWordBV = true) (pG : properBV G)
    (r : Fin M → Fin N) (eq : restrictRows r (observeBV T) = observeBV G)
    (covered : ∀ a ∈ roots, Available (other.map observeBV) (restrictRows r (observeBV a)))
    (singles : Finset (BitVec N)) (necessary : ∀ a ∈ singles, EssentialBV T roots a)
    (constant : ∀ a ∈ singles, Constant (restrictRows r (observeBV a)))
    (L : Nat) (prior : LowerBV other G L) : LowerBV roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k, S, hk, run, sub⟩ := reachBV_live pT nT nR hh ha
  have subS : singles ⊆ S := by
    intro a hs; obtain ⟨i, j, hd, hiso⟩ := necessary a hs
    exact rawBV_required run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front, List.nodup_append]
    refine ⟨Finset.nodup_toList _, Finset.nodup_toList _, fun a ha b hb he => ?_⟩
    subst b; exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset = S := by ext a; simp [front, Finset.union_sdiff_of_subset subS]
  have run' := list_runBV run front nd fe
  have supp : supply (other.map observeBV) ((front.map observeBV).map (restrictRows r)) := by
    intro v hv
    obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv
    obtain ⟨a, hmem, rfl⟩ := List.mem_map.mp hm
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound r run' (eq ▸ observeBV_proper pG) Reach.start supp (L := L) (eq ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observeBV).map (restrictRows r)) := by
    simp only [front, List.map_append, mass_append]
    let xs := (singles.toList.map observeBV).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv
      obtain ⟨a, hmem, rfl⟩ := List.mem_map.mp hm
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := mass_constants xs only
    simp only [xs, List.length_map, Finset.length_toList] at sz
    change singles.card ≤ mass xs + _; rw [sz]; omega
  omega

-- ============================================================
-- 3. 6-variable (BitVec 64) Engine, Slices, Pools & CutCheck
-- ============================================================

abbrev Sig := BitVec 64
abbrev Row := Fin 64

def x0 : Sig := 0xaaaaaaaaaaaaaaaa#64
def x1 : Sig := 0xcccccccccccccccc#64
def x2 : Sig := 0xf0f0f0f0f0f0f0f0#64
def x3 : Sig := 0xff00ff00ff00ff00#64
def x4 : Sig := 0xffff0000ffff0000#64
def x5 : Sig := 0xffffffff00000000#64
def allVars6 : List Sig := [x0, x1, x2, x3, x4, x5]

def rawOf (vmask : Nat) : List Sig :=
  ([0, 1, 2, 3, 4, 5] : List Nat).filterMap fun i =>
    if vmask.testBit i then some (allVars6.getD i 0) else none

theorem rawOf_nodup (m : Nat) : (rawOf m).Nodup := by
  unfold rawOf
  have h : ∀ b0 b1 b2 b3 b4 b5 : Bool,
      (([0, 1, 2, 3, 4, 5] : List Nat).filterMap fun i =>
        if (match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3 | 4 => b4 | _ => b5)
        then some (allVars6.getD i 0) else none).Nodup := by decide +kernel
  exact h (m.testBit 0) (m.testBit 1) (m.testBit 2) (m.testBit 3) (m.testBit 4) (m.testBit 5)

def rename6 (f : Row → Row) (a : Sig) : Sig := tableBV fun r => bitBV (f r) a
theorem bit6_rename (f : Row → Row) (a : Sig) (r : Row) : bitBV r (rename6 f a) = bitBV (f r) a :=
  bitBV_table _ _
theorem observe6_rename (f : Row → Row) (a : Sig) : observeBV (rename6 f a) = restrictRows f (observeBV a) := by
  funext r; exact bit6_rename f a r
theorem rename6_bin (f : Row → Row) (d : Nat) (a b : Sig) :
    rename6 f (binBV d a b) = binBV d (rename6 f a) (rename6 f b) := by
  apply bitBV_ext; intro r; simp only [bit6_rename, bitBV_bin]
theorem rename6_const (f : Row → Row) : rename6 f zeroBV = zeroBV ∧ rename6 f oneBV = oneBV := by
  constructor <;> apply bitBV_ext <;> intro r
  · exact (bit6_rename f zeroBV r).trans ((bitBV_zero _).trans (bitBV_zero r).symm)
  · exact (bit6_rename f oneBV r).trans ((bitBV_one _).trans (bitBV_one r).symm)
theorem rename6_inj (f : Row → Row) (onto : Function.Surjective f) : Function.Injective (rename6 f) := by
  intro a b h; apply bitBV_ext; intro j
  obtain ⟨r, hr⟩ := onto j
  have he := congrArg (bitBV r) h
  rw [bit6_rename, bit6_rename, hr] at he; exact he

theorem live6_rename {T : Sig} {k S} (h : LiveBV T k S) (f : Row → Row) (onto : Function.Surjective f) :
    LiveBV (rename6 f T) k (S.image (rename6 f)) := by
  have inj := rename6_inj f onto
  obtain ⟨fz, fo⟩ := rename6_const f
  have pp (v : Sig) (p : properBV v) : properBV (rename6 f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)), fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using LiveBV.ind with
  | stop hp => simpa using LiveBV.stop (pp _ hp)
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have fresh : rename6 f (binBV d a b) ∉ (insert a (insert b U)).image (rename6 f) := by
      intro hm; obtain ⟨v, hv, eq⟩ := Finset.mem_image.mp hm; exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert, rename6_bin] at fresh ih ⊢
    exact LiveBV.binary hd (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

def rowPerm (p : List Nat) (r : Row) : Row :=
  let v := ([0, 1, 2, 3, 4, 5] : List Nat).foldl
    (fun acc i => if r.val.testBit (p.getD i 0) then acc ||| (1 <<< i) else acc) 0
  ⟨v % 64, Nat.mod_lt _ (by decide)⟩

def sigPerm (p : List Nat) (a : Sig) : Sig := rename6 (rowPerm p) a

def fixRow (z o : Nat) (r : Row) : Row :=
  ⟨((r.val &&& (63 ^^^ (z ||| o))) ||| (o &&& 63)) % 64, Nat.mod_lt _ (by decide)⟩

def subcube6 (z o : Nat) : Sig :=
  tableBV fun r => ((r.val &&& z) == 0) && ((r.val &&& o) == (o &&& 63))

def properB (T : Sig) : Bool := T != zeroBV && T != oneBV
theorem proper_of {T : Sig} (h : properB T = true) : properBV T := by
  simpa only [properB, properBV, Bool.and_eq_true, bne_iff_ne] using h

def Slice (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig),
    (∀ r, bitBV (f r) d = true) ∧
    (∀ a ∈ raw, Available (roots.map observeBV) (restrictRows f (observeBV a))) ∧
    ¬Constant (restrictRows f (observeBV T)) ∧
    LowerBV roots (rename6 f T) L

def masked (d a : Sig) : Sig := a &&& d
def availableB (d : Sig) (pool : List Sig) (a : Sig) : Bool :=
  let m := masked d a
  m == zeroBV || m == d || (pool.map (masked d)).any (fun v => v == m) ||
    (let c := masked d (negBV a); (pool.map (masked d)).any (fun v => v == c))

theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bitBV (f r) d = true)
    (eq : masked d a = masked d b) : restrictRows f (observeBV a) = restrictRows f (observeBV b) := by
  funext r; have h := congrArg (bitBV (f r)) eq
  change bitBV (f r) a = bitBV (f r) b
  simpa only [bitBV, masked, BitVec.getLsbD_and, show d.getLsbD (f r).val = true from dom r, Bool.and_true] using h

theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bitBV (f r) d = true)
    (eq : masked d a = zeroBV) : restrictRows f (observeBV a) = fun _ => false := by
  funext r; have h := congrArg (bitBV (f r)) eq
  change bitBV (f r) a = false; rw [bitBV_zero] at h
  simpa only [bitBV, masked, BitVec.getLsbD_and, show d.getLsbD (f r).val = true from dom r, Bool.and_true] using h

theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bitBV (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observeBV a) = fun _ => true := by
  funext r; have h := congrArg (bitBV (f r)) eq
  change bitBV (f r) a = true; rw [dom r] at h
  simpa only [bitBV, masked, BitVec.getLsbD_and, show d.getLsbD (f r).val = true from dom r, Bool.and_true] using h

def poolSupply (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) : Prop :=
  ∀ a ∈ pool, Available bank (restrictRows f (observeBV a))

theorem availableB_sound {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bitBV (f r) d = true) (sup : poolSupply f bank pool)
    (h : availableB d pool a = true) : Available bank (restrictRows f (observeBV a)) := by
  simp only [availableB, List.any_map, Function.comp_def, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at h
  rcases h with ((hz | ho) | ⟨v, hv, he⟩) | ⟨v, hv, he⟩
  · exact Or.inr (Or.inl ⟨false, masked_zero dom hz⟩)
  · exact Or.inr (Or.inl ⟨true, masked_one dom ho⟩)
  · exact masked_eq dom he ▸ sup v hv
  · have h := avail_inv (masked_eq dom he ▸ sup v hv)
    rw [obsBV_neg] at h
    have e : inv (restrictRows f (inv (observeBV a))) = restrictRows f (observeBV a) := by
      funext r; simp [inv, restrictRows]
    rwa [e] at h

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) : Sig := binBV c.1 c.2.1 c.2.2
def choiceOK (d : Sig) (pool : List Sig) (c : Choice) : Bool :=
  decide (c.1 < 4) && availableB d pool c.2.1 && availableB d pool c.2.2

theorem pay_choice {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bitBV (f r) d = true) (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (c : Choice) (valid : choiceOK d pool c = true) :
    ∃ next, Reach roots (q + 1) next ∧ poolSupply f next (choiceVal c :: pool) := by
  simp only [choiceOK, Bool.and_eq_true, decide_eq_true_eq] at valid
  obtain ⟨op, x, y, e, hx, hy, _, _⟩ := comb_prime valid.1.1 (availableB_sound dom hs valid.1.2)
    (availableB_sound dom hs valid.2)
  refine ⟨_, Reach.two op hp hx hy, ?_⟩
  intro a hm; rcases List.mem_cons.mp hm with rfl | hm
  · rw [choiceVal, obsBV_bin, restrict_comb, e]; exact Or.inl (by simp)
  · exact available_cons _ (hs _ hm)

def makePool (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c :: cs => if choiceOK d pool c then makePool d (choiceVal c :: pool) cs else none

theorem makePool_sound {d : Sig} {f : Row → Row} (dom : ∀ r, bitBV (f r) d = true)
    {roots bank q pool} (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (cs : List Choice) {result} (ok : makePool d pool cs = some result) :
    ∃ next, Reach roots (q + cs.length) next ∧ poolSupply f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_, hp, hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok; split at ok
    next h =>
      obtain ⟨next, hr, sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out, hr', sh'⟩ := ih hr sh ok
      exact ⟨out, by simpa [Nat.add_assoc, Nat.add_comm 1] using hr', sh'⟩
    next => contradiction

def isMaskedConst (d a : Sig) : Bool := masked d a == zeroBV || masked d a == d

theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r, bitBV (f r) d = true)
    (ws : List Sig) : ws.countP (isMaskedConst d) ≤ mass ((ws.map observeBV).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons, List.map_cons, mass_cons]
    cases h : isMaskedConst d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observeBV a)) := by
        have hh : masked d a = zeroBV ∨ masked d a = d := by
          simpa only [isMaskedConst, Bool.or_eq_true, beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false, masked_zero dom hz⟩
        · exact ⟨true, masked_one dom ho⟩
      simpa [cost, hc, Nat.add_comm] using Nat.succ_le_succ ih

abbrev BoundPool := Sig × Nat × Nat × List Sig

def ValidPool (raw : List Sig) (T : Sig) (c : BoundPool) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bitBV (f r) c.1 = true) ∧ ¬Constant (restrictRows f (observeBV T)) ∧
    LowerBV roots (rename6 f T) c.2.1 ∧
    Reach (roots.map observeBV) c.2.2.1 bank ∧ poolSupply f bank c.2.2.2

theorem build_valid {raw T d lb} (h : Slice raw T d lb) (cs : List Choice) {ws}
    (build : makePool d raw cs = some ws) : ValidPool raw T (d, lb, cs.length, ws) := by
  obtain ⟨f, roots, dom, sup, nc, prior⟩ := h
  obtain ⟨bank, hr, hs⟩ := makePool_sound dom (Reach.start (roots := roots.map observeBV)) sup cs build
  exact ⟨f, roots, bank, dom, nc, prior, by simpa using hr, hs⟩

theorem valid_exclude {raw T c} (valid : ValidPool raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB c.1 c.2.2.2 a = true)
    (buy : if paid then choiceOK c.1 c.2.2.2 choice = true else availableB c.1 c.2.2.2 (choiceVal choice) = true)
    (bound : k + c.2.2.1 + paid.toNat < c.2.1 + (choiceVal choice :: rest).countP (isMaskedConst c.1))
    (nd : (choiceVal choice :: rest).Nodup) :
    ImpossibleBV T k (choiceVal choice :: rest).toFinset := by
  intro t ht run
  obtain ⟨f, roots, bank, dom, nc, lo, hp, hs⟩ := valid
  let ws := choiceVal choice :: rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach (roots.map observeBV) n out)
      (zs : poolSupply f out ws) (le : n = c.2.2.1 + paid.toNat) : False := by
    have covered : supply out ((ws.map observeBV).map (restrictRows f)) := by
      intro v hv; obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm; exact zs _ ha
    have lo' : ∀ q bs, Reach (roots.map observeBV) q bs → Available bs (restrictRows f (observeBV T)) → c.2.1 ≤ q := by
      simpa only [LowerBV, observe6_rename] using lo
    have b := projected_bound f (list_runBV run ws nd rfl) nc reach covered lo'
    have cm := count_constants dom ws
    change k + c.2.2.1 + paid.toNat < c.2.1 + ws.countP (isMaskedConst c.1) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h; rcases List.mem_cons.mp h with rfl | hm
    · exact availableB_sound dom hs buy
    · exact availableB_sound dom hs (known _ hm)
  | true =>
    obtain ⟨out, hr, hc⟩ := pay_choice dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h; rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · exact availableB_sound dom (fun v hu => hc v (List.mem_cons_of_mem _ hu)) (known _ hm)

-- ============================================================
-- 4. Cut Checking (ess, K3, P4, C5, and lifts) on BitVec 64
-- ============================================================

structure CutSpec where
  z : Nat
  o : Nat
  L : Nat
  kind : Nat
  dropZ : Nat
  perm : List Nat
  dom : Sig

def essentialCheck6 (G : Sig) (roots : List Sig) (a : Sig) : Bool :=
  (List.range 64).any fun r =>
    let r1 : Row := ⟨r % 64, Nat.mod_lt _ (by decide)⟩
    (List.range 64).any fun s =>
      let r2 : Row := ⟨s % 64, Nat.mod_lt _ (by decide)⟩
      (bitBV r1 G != bitBV r2 G) && roots.all (fun w => w == a || bitBV r1 w == bitBV r2 w)

theorem essentialCheck6_sound {G : Sig} {roots : List Sig} {a : Sig}
    (h : essentialCheck6 G roots a = true) : EssentialBV G roots a := by
  simp only [essentialCheck6, List.any_eq_true, Bool.and_eq_true, bne_iff_ne,
    List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨r, _, s, _, hdiff, hiso⟩ := h
  exact ⟨⟨r % 64, _⟩, ⟨s % 64, _⟩, hdiff, fun w hw hne => (hiso w hw).resolve_left hne⟩

def freeWord6 (roots : List Sig) (w : Sig) : Bool :=
  w == zeroBV || w == oneBV || roots.contains w

theorem freeWord6_sound {roots : List Sig} {w : Sig} (h : freeWord6 roots w = true) :
    Available (roots.map observeBV) (observeBV w) := by
  simp only [freeWord6, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at h
  rcases h with (rfl | rfl) | hm
  · exact Or.inr (Or.inl ⟨false, funext bitBV_zero⟩)
  · exact Or.inr (Or.inl ⟨true, funext bitBV_one⟩)
  · exact Or.inl (List.mem_map_of_mem hm)

theorem lower6_count {roots : List Sig} {G : Sig} (pG : properBV G)
    (nG : plainWordBV G = true) (nR : roots.all plainWordBV = true)
    (es : List Sig) (nd : es.Nodup) (he : es.all (essentialCheck6 G roots) = true) :
    LowerBV roots G (es.length - 1) := by
  intro p bank hr hit
  obtain ⟨k, S, hk, run, sub⟩ := reachBV_live pG nG nR hr hit
  have le : es.toFinset.card ≤ S.card := by
    apply Finset.card_le_card; intro a ha
    have ha' := List.mem_toFinset.mp ha
    obtain ⟨r, s, hd, iso⟩ := essentialCheck6_sound (List.all_eq_true.mp he a ha')
    exact rawBV_required run roots a sub r s hd iso
  rw [List.toFinset_card_of_nodup nd] at le
  have hsz := liveBV_size run
  omega

def checkCut (vmask : Nat) (T : Sig) (c : CutSpec)
    (baseOf : Nat → List Sig × Sig × Nat) : Bool :=
  let raw := rawOf vmask
  let d := subcube6 c.z c.o
  let f := fixRow c.z c.o
  let G := rename6 f T
  let freeMask := vmask &&& (63 ^^^ (c.z ||| c.o))
  let freeRaw := rawOf freeMask
  let domOk := (List.range 64).all fun r => bitBV (f ⟨r % 64, Nat.mod_lt _ (by decide)⟩) d
  let rawOk := raw.all (fun a => freeWord6 freeRaw (rename6 f a))
  (c.dom == d) && domOk && properB G && rawOk && plainWordBV G && freeRaw.all plainWordBV &&
  (if c.kind == 0 then
     let es := freeRaw.filter (essentialCheck6 G freeRaw)
     decide (c.L ≤ es.length - 1)
   else
     let (bRoots, bT, bL) := baseOf c.kind
     let g : Row → Row := fun r => fixRow c.dropZ 0 (rowPerm c.perm r)
     properB bT &&
     (rename6 g G == bT) &&
     freeRaw.all (fun a => freeWord6 bRoots (rename6 g a)) &&
     decide (c.L ≤ bL))

theorem checkCut_sound {vmask : Nat} {T : Sig} {c : CutSpec}
    {baseOf : Nat → List Sig × Sig × Nat}
    (hb : ∀ k, k ≠ 0 → LowerBV (baseOf k).1 (baseOf k).2.1 (baseOf k).2.2)
    (ok : checkCut vmask T c baseOf = true) :
    Slice (rawOf vmask) T c.dom c.L := by
  unfold checkCut at ok
  simp only [Bool.and_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨⟨hdomEq, domOk⟩, pG⟩, rawOk⟩, nG⟩, nFR⟩, hbody⟩ := ok
  rw [beq_iff_eq.mp hdomEq]
  let f := fixRow c.z c.o
  let G := rename6 f T
  let freeMask := vmask &&& (63 ^^^ (c.z ||| c.o))
  let freeRaw := rawOf freeMask
  have hdom : ∀ r : Row, bitBV (f r) (subcube6 c.z c.o) = true := by
    intro r
    have h := List.all_eq_true.mp domOk r.val (List.mem_range.mpr r.isLt)
    have hmod : (⟨r.val % 64, Nat.mod_lt _ (by decide)⟩ : Row) = r := Fin.ext (Nat.mod_eq_of_lt r.isLt)
    simpa [hmod] using h
  have hraw : ∀ a ∈ rawOf vmask, Available (freeRaw.map observeBV) (restrictRows f (observeBV a)) := by
    intro a ha; rw [← observe6_rename]
    exact freeWord6_sound (List.all_eq_true.mp rawOk a ha)
  have hnc : ¬Constant (restrictRows f (observeBV T)) := by
    rw [← observe6_rename]; exact observeBV_proper (proper_of pG)
  refine ⟨f, freeRaw, hdom, hraw, hnc, ?_⟩
  by_cases hk : c.kind = 0
  · simp only [hk, beq_self_eq_true, ite_true, decide_eq_true_eq] at hbody
    let es := freeRaw.filter (essentialCheck6 G freeRaw)
    have hnd : es.Nodup := (rawOf_nodup freeMask).filter _
    have hes : es.all (essentialCheck6 G freeRaw) = true := by
      apply List.all_eq_true.mpr; intro a ha; exact (List.mem_filter.mp ha).2
    have hlo := lower6_count (proper_of pG) nG nFR es hnd hes
    intro p bank hr ha; exact le_trans hbody (hlo p bank hr ha)
  · have hkn : (c.kind == 0) = false := beq_false_of_ne hk
    simp only [hkn, Bool.false_eq_true, ite_false, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hbody
    obtain ⟨⟨⟨pbT, hEq⟩, hCov⟩, hLe⟩ := hbody
    let b := baseOf c.kind
    let g : Row → Row := fun r => fixRow c.dropZ 0 (rowPerm c.perm r)
    have hlo := lowerBV_slice (proper_of pG) nG nFR (proper_of pbT) g
      ((observe6_rename g G).symm.trans (congrArg observeBV hEq))
      (fun a ha => by rw [← observe6_rename]; exact freeWord6_sound (List.all_eq_true.mp hCov a ha))
      ∅ (fun _ h => absurd h (Finset.notMem_empty _)) (fun _ h => absurd h (Finset.notMem_empty _))
      b.2.2 (hb c.kind hk)
    simp only [Finset.card_empty, Nat.add_zero] at hlo
    intro p bank hr ha; exact le_trans hLe (hlo p bank hr ha)

-- ============================================================
-- 5. BTree, BST, Strict Nat Kernel Checker & Soundness
-- ============================================================

inductive BTree (α : Type) where
  | leaf (a : α)
  | node (l r : BTree α)

def BTree.get {α} : BTree α → Nat → α
  | .leaf a, _ => a
  | .node l r, p => if p &&& 1 == 0 then l.get (p >>> 1) else r.get (p >>> 1)

def BTree.all {α} (f : α → Bool) : BTree α → Bool
  | .leaf a => f a
  | .node l r => l.all f && r.all f

theorem BTree.get_all {α} {f : α → Bool} {t : BTree α} (h : t.all f = true) (p : Nat) :
    f (t.get p) = true := by
  induction t generalizing p with
  | leaf a => exact h
  | node l r ihl ihr =>
    simp only [BTree.all, Bool.and_eq_true] at h
    unfold BTree.get; split
    · exact ihl h.1 _
    · exact ihr h.2 _

inductive BST where
  | e
  | l (k v : Nat)
  | n (k v : Nat) (l r : BST)

abbrev BE := BST.e
abbrev BL := BST.l
abbrev BN := BST.n

def BST.find : BST → Nat → Option (Nat × Nat)
  | .e, _ => none
  | .l k v, x => if Nat.beq x k then some (v >>> 7, v &&& 127) else none
  | .n k v left right, x =>
    if Nat.beq x k then some (v >>> 7, v &&& 127)
    else if Nat.ble x k then left.find x else right.find x

noncomputable def force {β : Type} (n : Nat) (f : Nat → β) : β :=
  Nat.rec (f 0) (fun k _ => f (Nat.succ k)) n
theorem force_eq {β : Type} (n : Nat) (f : Nat → β) : force n f = f n := by cases n <;> rfl

noncomputable def forceMap {α β : Type} (f : α → Nat) (l : List α) : (List Nat → β) → β :=
  List.rec (fun k => k []) (fun a _ ih k => force (f a) fun x => ih fun xs => k (x :: xs)) l
theorem forceMap_eq {α β : Type} (f : α → Nat) (l : List α) (k : List Nat → β) :
    forceMap f l k = k (l.map f) := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih =>
    change force (f a) (fun x => forceMap f l fun xs => k (x :: xs)) = _
    rw [force_eq, ih]; rfl

def zN (op x y : Nat) : Nat :=
  cond (Nat.beq op 0) (Nat.land x y)
    (cond (Nat.beq op 1) (Nat.lor x y)
      (cond (Nat.beq op 2) (Nat.xor x (Nat.land x y)) (Nat.xor y (Nat.land x y))))

theorem zN_mask (op : Nat) (d a b : Sig) :
    zN op (Nat.land a.toNat d.toNat) (Nat.land b.toNat d.toNat) = Nat.land (binBV op a b).toNat d.toNat := by
  have tn (x y : Sig) : Nat.land x.toNat y.toNat = (x &&& y).toNat := (BitVec.toNat_and x y).symm
  have tx (x y : Sig) : Nat.xor x.toNat y.toNat = (x ^^^ y).toNat := (BitVec.toNat_xor x y).symm
  have tor (x y : Sig) : Nat.lor x.toNat y.toNat = (x ||| y).toNat := (BitVec.toNat_or x y).symm
  rw [tn, tn, tn]; unfold zN
  by_cases h0 : op = 0
  · subst h0; change Nat.land _ _ = _; rw [tn]; congr 1; apply bitBV_ext; intro r
    simp only [binBV, bitBV, ite_true, BitVec.getLsbD_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  by_cases h1 : op = 1
  · subst h1; change Nat.lor _ _ = _; rw [tor]; congr 1; apply bitBV_ext; intro r
    simp only [binBV, bitBV, Nat.one_ne_zero, ite_true, ite_false, BitVec.getLsbD_and, BitVec.getLsbD_or]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e0 : Nat.beq op 0 = false := Bool.eq_false_iff.mpr (fun h => h0 (Nat.eq_of_beq_eq_true h))
  have e1 : Nat.beq op 1 = false := Bool.eq_false_iff.mpr (fun h => h1 (Nat.eq_of_beq_eq_true h))
  by_cases h2 : op = 2
  · subst h2; change Nat.xor _ (Nat.land _ _) = _; rw [tn, tx]; congr 1; apply bitBV_ext; intro r
    simp only [binBV, bitBV, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, ite_true, ite_false,
      BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_not, r.isLt, decide_true, Bool.true_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e2 : Nat.beq op 2 = false := Bool.eq_false_iff.mpr (fun h => h2 (Nat.eq_of_beq_eq_true h))
  rw [e0, e1, e2]; change Nat.xor _ (Nat.land _ _) = _; rw [tn, tx]; congr 1; apply bitBV_ext; intro r
  simp only [binBV, bitBV, h0, h1, h2, ite_false, BitVec.getLsbD_and, BitVec.getLsbD_xor,
    BitVec.getLsbD_not, r.isLt, decide_true, Bool.true_and]
  cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl

theorem nat_testBit_land (a b i : Nat) : (Nat.land a b).testBit i = (a.testBit i && b.testBit i) :=
  Nat.testBit_and a b i
theorem nat_testBit_lor (a b i : Nat) : (Nat.lor a b).testBit i = (a.testBit i || b.testBit i) :=
  Nat.testBit_or a b i
theorem nat_testBit_xor (a b i : Nat) : (Nat.xor a b).testBit i = Bool.xor (a.testBit i) (b.testBit i) :=
  Nat.testBit_xor a b i

theorem zN_full (op : Nat) (a b : Sig) : zN op a.toNat b.toNat = (binBV op a b).toNat := by
  have e (v : Sig) : Nat.land v.toNat (oneBV (N := 64)).toNat = v.toNat := by
    change v.toNat &&& (oneBV (N := 64)).toNat = v.toNat
    rw [← BitVec.toNat_and]; congr 1; exact BitVec.and_allOnes
  have := zN_mask op oneBV a b; rwa [e, e, e] at this

theorem zN_testBit (op x y i : Nat) :
    (zN op x y).testBit i =
      (if op = 0 then x.testBit i && y.testBit i
       else if op = 1 then x.testBit i || y.testBit i
       else if op = 2 then x.testBit i && !(y.testBit i)
       else !(x.testBit i) && y.testBit i) := by
  unfold zN
  by_cases h0 : op = 0
  · subst h0; simp [nat_testBit_land]
  by_cases h1 : op = 1
  · subst h1; simp [nat_testBit_lor]
  have e0 : Nat.beq op 0 = false := Bool.eq_false_iff.mpr (fun h => h0 (Nat.eq_of_beq_eq_true h))
  have e1 : Nat.beq op 1 = false := Bool.eq_false_iff.mpr (fun h => h1 (Nat.eq_of_beq_eq_true h))
  by_cases h2 : op = 2
  · subst h2; simp only [e0, e1, Bool.cond_false, Bool.cond_true, Nat.beq_refl, nat_testBit_xor, nat_testBit_land,
      OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, ite_false, ite_true]
    cases x.testBit i <;> cases y.testBit i <;> rfl
  have e2 : Nat.beq op 2 = false := Bool.eq_false_iff.mpr (fun h => h2 (Nat.eq_of_beq_eq_true h))
  simp only [e0, e1, e2, Bool.cond_false, nat_testBit_xor, nat_testBit_land, h0, h1, h2, ite_false]
  cases x.testBit i <;> cases y.testBit i <;> rfl

abbrev CovN := Nat × Nat × Nat

def addCovN (z : Nat) (c : CovN) : CovN :=
  (Nat.lor z c.1,
   Nat.lor (Nat.xor z (Nat.land z c.1)) (Nat.xor c.2.1 (Nat.land c.2.1 z)),
   Nat.lor (Nat.land z c.2.1) (Nat.xor c.2.2 (Nat.land c.2.2 z)))

def covOfCols : List Nat → CovN
  | [] => (0, 0, 0)
  | z :: zs => addCovN z (covOfCols zs)

def takeOneN (c : CovN) (a : Nat) : Nat := Nat.xor c.1 (Nat.land c.1 (Nat.land c.2.1 a))
def takeTwoN (c : CovN) (a b : Nat) : Nat :=
  Nat.xor c.1 (Nat.land c.1 (Nat.lor (Nat.land c.2.1 (Nat.lor a b)) (Nat.land c.2.2 (Nat.land a b))))
def restCovN (c : CovN) (a b : Nat) (ka kb : Bool) : Nat :=
  if ka then (if kb then c.1 else takeOneN c b)
  else if kb then takeOneN c a else takeTwoN c a b

theorem addCovN_swap (c : CovN) (a b : Nat) : addCovN a (addCovN b c) = addCovN b (addCovN a c) := by
  refine Prod.ext (Nat.eq_of_testBit_eq fun i => ?_)
    (Prod.ext (Nat.eq_of_testBit_eq fun i => ?_) (Nat.eq_of_testBit_eq fun i => ?_))
  all_goals
    simp only [addCovN, nat_testBit_lor, nat_testBit_land, nat_testBit_xor]
    cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
      cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> rfl

theorem takeOneN_add (c : CovN) (a : Nat) : takeOneN (addCovN a c) a = c.1 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [takeOneN, addCovN, nat_testBit_lor, nat_testBit_land, nat_testBit_xor]
  cases a.testBit i <;> cases c.1.testBit i <;> cases c.2.1.testBit i <;> rfl

theorem takeTwoN_add (c : CovN) (a b : Nat) : takeTwoN (addCovN a (addCovN b c)) a b = c.1 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [takeTwoN, addCovN, nat_testBit_lor, nat_testBit_land, nat_testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
    cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> rfl

theorem covOfCols_perm {l r : List Nat} (h : l.Perm r) : covOfCols l = covOfCols r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCovN a) ih
  | swap a b _ => exact addCovN_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2

def orList : List Nat → Nat
  | [] => 0
  | x :: xs => Nat.lor x (orList xs)

theorem covOfCols_fst (l : List Nat) : (covOfCols l).1 = orList l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [covOfCols, addCovN, orList, ih]

theorem orList_testBit (l : List Nat) (i : Nat) :
    (orList l).testBit i = true ↔ ∃ x ∈ l, x.testBit i = true := by
  induction l with
  | nil => simp [orList]
  | cons x xs ih => simp [orList, Nat.testBit_lor, ih]

abbrev DWire := Sig × Nat × Nat
def dcol (w : DWire) : Nat := Nat.xor w.2.1 w.2.2
def dbin (op : Nat) (a b : DWire) : DWire := (binBV op a.1 b.1, zN op a.2.1 b.2.1, zN op a.2.2 b.2.2)

def Faithful (pos neg : List Row) (w : DWire) : Prop :=
  (∀ i : Nat, i < pos.length →
    w.2.1.testBit i = bitBV (pos.getD i ⟨0, by decide⟩) w.1 ∧
    w.2.2.testBit i = bitBV (neg.getD i ⟨0, by decide⟩) w.1) ∧
  w.2.1 < 2 ^ pos.length ∧ w.2.2 < 2 ^ pos.length

theorem zN_lt_pow {W op x y : Nat} (hx : x < 2 ^ W) (hy : y < 2 ^ W) : zN op x y < 2 ^ W := by
  have hi : ∀ i ≥ W, (zN op x y).testBit i = false := by
    intro i hi
    have h1 : x.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hi))
    have h2 : y.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hy (Nat.pow_le_pow_right (by decide) hi))
    rw [zN_testBit, h1, h2]; split_ifs <;> rfl
  by_contra! hge
  have hlt : W ≤ Nat.log2 (zN op x y) := by
    have hp : zN op x y ≠ 0 := by
      have : 0 < 2 ^ W := Nat.pow_pos (by decide)
      omega
    exact (Nat.le_log2 hp).mpr hge
  have htb := Nat.testBit_log2 (show zN op x y ≠ 0 by have : 0 < 2 ^ W := Nat.pow_pos (by decide); omega)
  rw [hi _ hlt] at htb; exact Bool.noConfusion htb

theorem faithful_dbin {pos neg : List Row} {a b : DWire} (op : Nat)
    (ha : Faithful pos neg a) (hb : Faithful pos neg b) : Faithful pos neg (dbin op a b) := by
  refine ⟨fun i hi => ?_, zN_lt_pow ha.2.1 hb.2.1, zN_lt_pow ha.2.2 hb.2.2⟩
  obtain ⟨ha1, ha2⟩ := ha.1 i hi
  obtain ⟨hb1, hb2⟩ := hb.1 i hi
  simp only [dbin, zN_testBit, bitBV_bin, ha1, ha2, hb1, hb2, and_self]

theorem faithful_zero (pos neg : List Row) : Faithful pos neg (zeroBV, 0, 0) :=
  ⟨fun i _ => by simp [bitBV_zero], Nat.pow_pos (by decide), Nat.pow_pos (by decide)⟩

def CritOK (T : Sig) (pos neg : List Row) : Prop :=
  ∀ i : Nat, i < pos.length →
    bitBV (pos.getD i ⟨0, by decide⟩) T ≠ bitBV (neg.getD i ⟨0, by decide⟩) T

def allOnesNat (W : Nat) : Nat := (1 <<< W) - 1

theorem dcol_lt {pos neg : List Row} {w : DWire} (h : Faithful pos neg w) : dcol w < 2 ^ pos.length := by
  have hi : ∀ i ≥ pos.length, (dcol w).testBit i = false := by
    intro i hi
    have h1 : w.2.1.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le h.2.1 (Nat.pow_le_pow_right (by decide) hi))
    have h2 : w.2.2.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le h.2.2 (Nat.pow_le_pow_right (by decide) hi))
    simp [dcol, Nat.testBit_xor, h1, h2]
  by_contra! hge
  have hp : dcol w ≠ 0 := by have : 0 < 2 ^ pos.length := Nat.pow_pos (by decide); omega
  have htb := Nat.testBit_log2 hp
  rw [hi _ ((Nat.le_log2 hp).mpr hge)] at htb; exact Bool.noConfusion htb

theorem orList_lt {W : Nat} {l : List Nat} (hl : ∀ x ∈ l, x < 2 ^ W) : orList l < 2 ^ W := by
  have hi : ∀ i ≥ W, (orList l).testBit i = false := by
    intro i hi; apply Bool.eq_false_iff.mpr; intro ht
    obtain ⟨x, hx, hxt⟩ := (orList_testBit l i).mp ht
    have hf := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (hl x hx) (Nat.pow_le_pow_right (by decide) hi))
    rw [hf] at hxt; exact Bool.noConfusion hxt
  by_contra! hge
  have hp : orList l ≠ 0 := by have : 0 < 2 ^ W := Nat.pow_pos (by decide); omega
  have htb := Nat.testBit_log2 hp
  rw [hi _ ((Nat.le_log2 hp).mpr hge)] at htb; exact Bool.noConfusion htb

theorem live6_cover_eq {T : Sig} {k} {ws : List DWire} {pos neg : List Row}
    (hcrit : CritOK T pos neg) (hf : ∀ w ∈ ws, Faithful pos neg w)
    (h : LiveBV T k (ws.map Prod.fst).toFinset) :
    orList (ws.map dcol) = allOnesNat pos.length := by
  have hlt : orList (ws.map dcol) < 2 ^ pos.length :=
    orList_lt fun x hx => by obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx; exact dcol_lt (hf w hw)
  apply Nat.eq_of_testBit_eq; intro i
  simp only [allOnesNat, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < pos.length
  · simp only [hi, decide_true]
    obtain ⟨v, hv, hdiff⟩ := liveBV_row_diff h (hcrit i hi)
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    apply (orList_testBit _ i).mpr
    refine ⟨dcol w, List.mem_map_of_mem hw, ?_⟩
    obtain ⟨h1, h2⟩ := (hf w hw).1 i hi
    simp only [dcol, Nat.testBit_xor, h1, h2]
    cases hx : bitBV (pos.getD i ⟨0, by decide⟩) w.1 <;>
      cases hy : bitBV (neg.getD i ⟨0, by decide⟩) w.1 <;> simp_all
  · simp only [hi, decide_false]
    exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) (by omega)))

def delOne {α} [BEq α] (ws : List α) (a : α) (keep : Bool) : List α :=
  if keep then ws else ws.erase a
def delTwo {α} [BEq α] (ws : List α) (a b : α) (ka kb : Bool) : List α :=
  delOne (delOne ws a ka) b kb

theorem delOne_sub {α} [BEq α] [LawfulBEq α] (ws : List α) (a : α) (k : Bool) :
    (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem delTwo_sub {α} [BEq α] [LawfulBEq α] (ws : List α) (a b : α) (ka kb : Bool) :
    (delTwo ws a b ka kb).Sublist ws := (delOne_sub _ _ _).trans (delOne_sub _ _ _)

theorem delTwo_len {α} [BEq α] [LawfulBEq α] (ws : List α) (a b : α) (ka kb : Bool)
    (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) :
    (delTwo ws a b ka kb).length = ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  cases ka <;> cases kb <;>
    simp [delTwo, delOne, List.length_erase_of_mem ha, List.length_erase_of_mem hb, List.length_erase_of_mem hm]

theorem delTwo_cov {ws : List DWire} {a b : DWire} (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) (ka kb : Bool) :
    orList ((delTwo ws a b ka kb).map dcol) = restCovN (covOfCols (ws.map dcol)) (dcol a) (dcol b) ka kb := by
  rw [← covOfCols_fst]
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  cases ka <;> cases kb
  · have hp : ws.Perm (a :: b :: (ws.erase a).erase b) :=
      (List.perm_cons_erase ha).trans (List.Perm.cons _ (List.perm_cons_erase hm))
    change (covOfCols (((ws.erase a).erase b).map dcol)).1 = takeTwoN _ _ _
    rw [covOfCols_perm (hp.map dcol)]; exact (takeTwoN_add _ _ _).symm
  · have hp : ws.Perm (a :: ws.erase a) := List.perm_cons_erase ha
    change (covOfCols ((ws.erase a).map dcol)).1 = takeOneN _ _
    rw [covOfCols_perm (hp.map dcol)]; exact (takeOneN_add _ _).symm
  · have hp : ws.Perm (b :: ws.erase b) := List.perm_cons_erase hb
    change (covOfCols ((ws.erase b).map dcol)).1 = takeOneN _ _
    rw [covOfCols_perm (hp.map dcol)]; exact (takeOneN_add _ _).symm
  · rfl

abbrev NodeData := Nat × Nat × List Nat
def lf (p0 : Nat) (hs : List Nat) : BTree NodeData := .leaf (p0, 0, hs)
def lf2 (p0 p1 : Nat) (hs : List Nat) : BTree NodeData := .leaf (p0, p1, hs)
abbrev nd := @BTree.node NodeData
def mkRows (l : List Nat) : List Row := l.map fun x => ⟨x % 64, Nat.mod_lt _ (by decide)⟩

def unpackH1 (h : Nat) : List (Nat × Nat) :=
  if Nat.beq h 0 then [] else
  let a := ((h &&& 255) - 1, (h >>> 8) &&& 255)
  let h1 := h >>> 16
  if Nat.beq h1 0 then [a] else
  let b := ((h1 &&& 255) - 1, (h1 >>> 8) &&& 255)
  let h2 := h1 >>> 16
  if Nat.beq h2 0 then [a, b] else
  [a, b, ((h2 &&& 255) - 1, (h2 >>> 8) &&& 255)]

def unpackHints (hs : List Nat) : List (Nat × Nat) := hs.flatMap unpackH1

def selectLive {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w :: ws => if bits &&& 1 == 1 then w :: selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws

theorem selectLive_sub {α : Type} (bits : Nat) (ws : List α) : (selectLive bits ws).Sublist ws := by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons _ _ ih =>
    unfold selectLive
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)

theorem selectLive_map {α β : Type} (f : α → β) (bits : Nat) (ws : List α) :
    (selectLive bits ws).map f = selectLive bits (ws.map f) := by
  induction ws generalizing bits with
  | nil => rfl
  | cons _ _ ih =>
    rw [List.map_cons, selectLive, selectLive]
    split
    · rw [List.map_cons, ih]
    · exact ih _

def decodeDBank : Nat → Nat → List DWire → List DWire
  | 0, _, ws => ws
  | n + 1, ops, ws =>
    let a := ws.getD (ops &&& 15) (zeroBV, 0, 0)
    let b := ws.getD ((ops >>> 4) &&& 15) (zeroBV, 0, 0)
    decodeDBank n (ops >>> 10) (ws ++ [dbin ((ops >>> 8) &&& 3) a b])

theorem decodeDBank_faithful {pos neg : List Row} (n ops : Nat) (ws : List DWire)
    (hb : ∀ w ∈ ws, Faithful pos neg w) :
    ∀ w ∈ decodeDBank n ops ws, Faithful pos neg w := by
  have getF {l : List DWire} (hl : ∀ w ∈ l, Faithful pos neg w) (i : Nat) :
      Faithful pos neg (l.getD i (zeroBV, 0, 0)) := by
    simp only [List.getD_eq_getElem?_getD]
    cases h : l[i]? with
    | none => exact faithful_zero pos neg
    | some v => exact hl v (List.mem_of_getElem? h)
  induction n generalizing ops ws with
  | zero => exact hb
  | succ n ih =>
    apply ih; intro w hw
    rcases List.mem_append.mp hw with h | h
    · exact hb w h
    · obtain rfl := List.mem_singleton.mp h
      exact faithful_dbin _ (getF hb _) (getF hb _)

noncomputable def decodeN : Nat → Nat → List Nat → List Nat
  | 0, _, ws => ws
  | n + 1, ops, ws =>
    force (zN ((ops >>> 8) &&& 3) (ws.getD (ops &&& 15) 0) (ws.getD ((ops >>> 4) &&& 15) 0)) fun z =>
      decodeN n (ops >>> 10) (ws ++ [z])

theorem decodeN_eq (F : Sig → Nat) (F0 : F zeroBV = 0) (Fb : ∀ op a b, F (binBV op a b) = zN op (F a) (F b))
    (n ops : Nat) (ds : List DWire) :
    (decodeDBank n ops ds).map (fun w => F w.1) = decodeN n ops (ds.map fun w => F w.1) := by
  have gd (l : List DWire) (i : Nat) :
      (l.map fun w => F w.1).getD i 0 = F (l.getD i (zeroBV, 0, 0)).1 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases l[i]? with
    | none => exact F0.symm
    | some _ => rfl
  induction n generalizing ops ds with
  | zero => rfl
  | succ n ih =>
    rw [decodeN, force_eq, decodeDBank, ih, gd, gd, ← Fb, List.map_append]; rfl

def chosenSteps (bank : List DWire) : Nat → Nat → Nat → List Choice
  | _, _, 0 => []
  | ops, paid, n + 1 =>
    if Nat.beq paid 0 then [] else
    let rest := chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then rest else
      ((ops >>> 8) &&& 3, (bank.getD (ops &&& 15) (zeroBV, 0, 0)).1,
        (bank.getD ((ops >>> 4) &&& 15) (zeroBV, 0, 0)).1) :: rest

def kwN (v : Nat) : Nat :=
  let n := v % 134217689
  (n * (n + 971)) % 134217689

noncomputable def anyEq (m : Nat) (l : List Nat) : Bool :=
  List.rec false (fun v _ ih => or (Nat.beq m v) ih) l

theorem anyEq_iff (m : Nat) (l : List Nat) : anyEq m l = true ↔ m ∈ l := by
  induction l with
  | nil => simp [anyEq]
  | cons a l ih =>
    change or (Nat.beq m a) (anyEq m l) = true ↔ _
    rw [Bool.or_eq_true, ih, Nat.beq_eq, List.mem_cons]

def nmask (d : Nat) (a : Sig) : Nat := Nat.land a.toNat d
def nconst (d m : Nat) : Bool := or (Nat.beq m 0) (Nat.beq m d)
noncomputable def navail (d : Nat) (pm : List Nat) (m : Nat) : Bool :=
  or (or (nconst d m) (anyEq m pm)) (anyEq (Nat.xor d m) pm)
def nloss (d x : Nat) (keep : Bool) : Nat := cond keep 0 (cond (nconst d x) 1 0)

theorem masked_comp (d x : Sig) : masked d (negBV x) = d ^^^ masked d x := by
  apply bitBV_ext; intro r
  simp only [masked, negBV, bitBV, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_xor,
    r.isLt, decide_true, Bool.true_and]
  cases d.getLsbD r.val <;> cases x.getLsbD r.val <;> rfl

theorem nmask_eq (d a : Sig) : nmask d.toNat a = (masked d a).toNat := (BitVec.toNat_and _ _).symm
theorem beq_toNat (a b : Sig) : Nat.beq a.toNat b.toNat = (a == b) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, beq_iff_eq]; exact BitVec.toNat_inj
theorem nconst_eq (d a : Sig) : nconst d.toNat (nmask d.toNat a) = isMaskedConst d a := by
  rw [nmask_eq]
  have e : Nat.beq (masked d a).toNat 0 = (masked d a == zeroBV) := by
    have z0 : (zeroBV (N := 64)).toNat = 0 := by simp [zeroBV]
    rw [← beq_toNat, z0]
  rw [nconst, e, beq_toNat]; rfl
theorem anyEq_masked (x d : Sig) (pool : List Sig) :
    anyEq x.toNat (pool.map (nmask d.toNat)) = (pool.map (masked d)).any (fun v => v == x) := by
  induction pool with
  | nil => rfl
  | cons a l ih =>
    change or (Nat.beq x.toNat (nmask d.toNat a)) (anyEq x.toNat (l.map (nmask d.toNat))) = _
    rw [ih, nmask_eq, beq_toNat, List.map_cons, List.any_cons, Bool.beq_comm]
theorem navail_eq (d a : Sig) (pool : List Sig) :
    navail d.toNat (pool.map (nmask d.toNat)) (nmask d.toNat a) = availableB d pool a := by
  have x : Nat.xor d.toNat (masked d a).toNat = (masked d (negBV a)).toNat := by
    rw [masked_comp]; exact (BitVec.toNat_xor _ _).symm
  rw [navail, nconst_eq, nmask_eq, x, anyEq_masked, anyEq_masked]
  simp only [availableB, isMaskedConst]

abbrev QS := Nat × Nat × Nat × Nat × Nat × List Nat × List Nat

noncomputable def quickSpec (k : Nat) (ws : List DWire) (p : BoundPool) : QS :=
  let d := p.1.toNat
  let pm := p.2.2.2.map (nmask d)
  let ms := ws.map (fun w : DWire => nmask d w.1)
  (d, ms.countP (nconst d), p.2.1, Nat.add k p.2.2.1,
    (ms.map fun m => cond (navail d pm m) 0 1).sum, ms, pm)

noncomputable def forcePool {β : Type} (k : Nat) (ws : List DWire) (p : BoundPool) (f : QS → β) : β :=
  force p.1.toNat fun d => forceMap (nmask d) p.2.2.2 fun pm =>
  forceMap (fun w : DWire => nmask d w.1) ws fun ms =>
  force (ms.countP (nconst d)) fun c => force p.2.1 fun l => force (Nat.add k p.2.2.1) fun t =>
  force (ms.map fun m => cond (navail d pm m) 0 1).sum fun v => f (d, c, l, t, v, ms, pm)

theorem forcePool_eq {β : Type} (k ws p) (f : QS → β) : forcePool k ws p f = f (quickSpec k ws p) := by
  simp only [forcePool, force_eq, forceMap_eq]; rfl

noncomputable def forcePools {β : Type} (k : Nat) (ws : List DWire) (ps : List BoundPool) : (List QS → β) → β :=
  List.rec (fun f => f []) (fun p _ ih f => forcePool k ws p fun q => ih fun qs => f (q :: qs)) ps

theorem forcePools_eq {β : Type} (k ws ps) (f : List QS → β) :
    forcePools k ws ps f = f (ps.map (quickSpec k ws)) := by
  induction ps generalizing f with
  | nil => rfl
  | cons p ps ih =>
    change forcePool k ws p (fun q => forcePools k ws ps fun qs => f (q :: qs)) = _
    rw [forcePool_eq, ih]; rfl

noncomputable def fastCost (s : QS) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (s.2.2.2.2.2.1.getD i 0) fun x => force (s.2.2.2.2.2.1.getD j 0) fun y =>
  let av := navail s.1 s.2.2.2.2.2.2
  let hi := Nat.add s.2.2.1 (Nat.sub (Nat.sub s.2.1 (nloss s.1 x ka)) (nloss s.1 y kb))
  let lo := s.2.2.2.1
  and (Nat.beq s.2.2.2.2.1 (Nat.add (cond ka 0 (cond (av x) 0 1)) (cond kb 0 (cond (av y) 0 1))))
  (cond (Nat.ble (Nat.succ lo) hi)
    (force (zN op x y) fun z => or (av z) (and (Nat.ble (Nat.add lo 2) hi) (and (av x) (av y))))
    (cond (Nat.ble lo hi) (nconst s.1 (zN op x y)) false))

theorem delTwo_sum {α} [BEq α] [LawfulBEq α] (f : α → Nat) {ws : List α} {a b : α}
    (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) (ka kb : Bool) :
    ((delTwo ws a b ka kb).map f).sum = (ws.map f).sum - (cond ka 0 (f a)) - (cond kb 0 (f b)) := by
  have er {l : List α} {x : α} (hx : x ∈ l) : (l.map f).sum = f x + ((l.erase x).map f).sum := by
    have := ((List.perm_cons_erase hx).map f).sum_eq
    rwa [List.map_cons, List.sum_cons] at this
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  have e1 := er ha; have e2 := er hb; have e3 := er hm
  cases ka <;> cases kb <;> simp only [delTwo, delOne, Bool.false_eq_true, ite_true, ite_false, cond_true, cond_false] <;> omega

theorem keptCount {α} [BEq α] [LawfulBEq α] (p : α → Bool) (ws : List α) (a b : α) (ka kb : Bool) :
    ws.countP p - (if ka then 0 else (p a).toNat) - (if kb then 0 else (p b).toNat) ≤
    (delTwo ws a b ka kb).countP p := by
  have lb (l : List α) (x : α) (k : Bool) : l.countP p ≤ (delOne l x k).countP p + (if k then 0 else (p x).toNat) := by
    cases k
    · simp only [delOne, Bool.false_eq_true, ite_false, List.countP_erase]
      split
      next h => simp [h.2]; omega
      next => omega
    · simp [delOne]
  have h1 := lb ws a ka; have h2 := lb (delOne ws a ka) b kb
  simp only [delTwo]; omega

theorem fastCost_sound {raw T} {p : BoundPool} (vp : ValidPool raw T p)
    {k : Nat} {ws : List DWire} {i j op : Nat} {ka kb : Bool}
    (hi : i < ws.length) (hj : j < ws.length) (hij : i ≠ j) (hop : op < 4)
    (nd : (ws.map Prod.fst).Nodup)
    (hfresh : binBV op (ws[i]).1 (ws[j]).1 ∉ ws.map Prod.fst)
    (hfc : fastCost (quickSpec k ws p) i j op ka kb = true) :
    ImpossibleBV T k (binBV op (ws[i]).1 (ws[j]).1 :: (delTwo ws ws[i] ws[j] ka kb).map Prod.fst).toFinset := by
  have ha : ws[i] ∈ ws := List.getElem_mem hi
  have hb : ws[j] ∈ ws := List.getElem_mem hj
  have hne1 : (ws[i]).1 ≠ (ws[j]).1 := fun e => hij ((List.Nodup.getElem_inj_iff nd (hi := by simpa using hi) (hj := by simpa using hj)).mp (by simpa using e))
  have hne : ws[i] ≠ ws[j] := fun e => hne1 (congrArg Prod.fst e)
  let a := ws[i]; let b := ws[j]; let rest := delTwo ws a b ka kb
  have hsub : rest.Sublist ws := delTwo_sub ws a b ka kb
  have ndc : (binBV op a.1 b.1 :: rest.map Prod.fst).Nodup :=
    List.nodup_cons.mpr ⟨fun hm => hfresh ((hsub.map _).subset hm), nd.sublist (hsub.map _)⟩
  have gget (t : Nat) (ht : t < ws.length) :
      (ws.map (fun w : DWire => nmask p.1.toNat w.1)).getD t 0 = nmask p.1.toNat (ws[t]).1 := by
    simp [List.getD_eq_getElem?_getD, ht]
  have su : ((ws.map (fun w : DWire => nmask p.1.toNat w.1)).map
      fun m => cond (navail p.1.toNat (p.2.2.2.map (nmask p.1.toNat)) m) 0 1).sum =
      (ws.map fun w => cond (availableB p.1 p.2.2.2 w.1) 0 1).sum := by
    rw [List.map_map]; refine congrArg List.sum (List.map_congr_left fun w _ => ?_)
    change cond (navail p.1.toNat (p.2.2.2.map (nmask p.1.toNat)) (nmask p.1.toNat w.1)) 0 1 = _
    rw [navail_eq]
  have nloss_e (w : DWire) (kp : Bool) :
      nloss p.1.toNat (nmask p.1.toNat w.1) kp = if kp then 0 else (isMaskedConst p.1 w.1).toNat := by
    rw [nloss, nconst_eq]
    cases kp
    · cases isMaskedConst p.1 w.1 <;> rfl
    · rfl
  simp only [fastCost, quickSpec, force_eq, gget i hi, gget j hj, su, List.countP_map, Function.comp_def,
    nconst_eq, nloss_e] at hfc
  change and (Nat.beq (ws.map fun w => cond (availableB p.1 p.2.2.2 w.1) 0 1).sum
    (Nat.add (cond ka 0 (cond (navail p.1.toNat (p.2.2.2.map (nmask p.1.toNat)) (nmask p.1.toNat a.1)) 0 1))
      (cond kb 0 (cond (navail p.1.toNat (p.2.2.2.map (nmask p.1.toNat)) (nmask p.1.toNat b.1)) 0 1)))) _ = true at hfc
  have zeq : zN op (nmask p.1.toNat a.1) (nmask p.1.toNat b.1) = nmask p.1.toNat (binBV op a.1 b.1) := zN_mask op p.1 a.1 b.1
  rw [zeq, nconst_eq, navail_eq, navail_eq, navail_eq] at hfc
  simp only [Nat.add_eq, Nat.sub_eq, Nat.succ_eq_add_one, Bool.and_eq_true, Nat.beq_eq] at hfc
  obtain ⟨hu, hcond⟩ := hfc
  have hsum := delTwo_sum (fun w : DWire => cond (availableB p.1 p.2.2.2 w.1) 0 1) ha hb hne ka kb
  change (rest.map fun w => cond (availableB p.1 p.2.2.2 w.1) 0 1).sum =
      (ws.map fun w => cond (availableB p.1 p.2.2.2 w.1) 0 1).sum -
      cond ka 0 (cond (availableB p.1 p.2.2.2 a.1) 0 1) -
      cond kb 0 (cond (availableB p.1 p.2.2.2 b.1) 0 1) at hsum
  rw [hu] at hsum
  have hzero : (rest.map fun w : DWire => cond (availableB p.1 p.2.2.2 w.1) 0 1).sum = 0 := by omega
  have hknown : ∀ v ∈ rest.map Prod.fst, availableB p.1 p.2.2.2 v = true := by
    intro _ hm; obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hm
    have hv := List.sum_eq_zero_iff.mp hzero _ (List.mem_map_of_mem hw)
    cases e : availableB p.1 p.2.2.2 w.1
    · simp [e] at hv
    · rfl
  have hkc := keptCount (fun w : DWire => isMaskedConst p.1 w.1) ws a b ka kb
  have hcm : (binBV op a.1 b.1 :: rest.map Prod.fst).countP (isMaskedConst p.1) =
      rest.countP (fun w : DWire => isMaskedConst p.1 w.1) + (isMaskedConst p.1 (binBV op a.1 b.1)).toNat := by
    simp only [List.countP_cons, List.countP_map, Function.comp_def]
    cases isMaskedConst p.1 (binBV op a.1 b.1) <;> simp
  have ca : isMaskedConst p.1 (binBV op a.1 b.1) = true → availableB p.1 p.2.2.2 (binBV op a.1 b.1) = true := by
    intro h; simp only [availableB, isMaskedConst, Bool.or_eq_true] at h ⊢; exact Or.inl (Or.inl h)
  let ch : Choice := (op, a.1, b.1)
  have hcv : choiceVal ch = binBV op a.1 b.1 := rfl
  generalize hC : (ws.countP (fun w => isMaskedConst p.1 w.1) - (if ka then 0 else (isMaskedConst p.1 a.1).toNat) -
      (if kb then 0 else (isMaskedConst p.1 b.1).toNat)) = C at hcond hkc
  change C ≤ rest.countP (fun w => isMaskedConst p.1 w.1) at hkc
  cases h1 : Nat.ble (k + p.2.2.1 + 1) (p.2.1 + C)
  · rw [h1] at hcond
    cases h2 : Nat.ble (k + p.2.2.1) (p.2.1 + C)
    · rw [h2] at hcond; simp at hcond
    · rw [h2] at hcond
      have hl2 := Nat.ble_eq.mp h2
      simp only [Bool.cond_true, Bool.cond_false] at hcond
      have haz := ca hcond
      exact valid_exclude vp k (rest.map Prod.fst) ch false hknown haz (by rw [hcv, hcm, hcond]; simp; omega) ndc
  · rw [h1] at hcond
    have hl1 := Nat.ble_eq.mp h1
    simp only [Bool.cond_true, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq] at hcond
    rcases hcond with haz | ⟨hl2, haa, hbb⟩
    · exact valid_exclude vp k (rest.map Prod.fst) ch false hknown haz (by rw [hcv, hcm]; simp; omega) ndc
    · have hcok : choiceOK p.1 p.2.2.2 ch = true := by simp [choiceOK, ch, hop, haa, hbb]
      exact valid_exclude vp k (rest.map Prod.fst) ch true hknown hcok (by rw [hcv, hcm]; simp; omega) ndc

-- Forest & fastNodeOK
structure Forest where
  vmask : Nat
  target : Sig
  cap : Nat
  pos : List Row
  neg : List Row
  rawCols : List (Nat × Nat)
  autos : List (List Nat)
  cuts : List CutSpec
  levels : Nat → Option (BTree NodeData)
  maps : Nat → BST

def Forest.rawD (g : Forest) : List DWire :=
  (rawOf g.vmask).zipWith (fun s c => (s, c.1, c.2)) g.rawCols

def Forest.nodeWires (g : Forest) (nd : NodeData) : List DWire :=
  let depth := nd.1 &&& 15
  let liveMask := (nd.1 >>> 4) &&& 65535
  let ops := (nd.1 >>> 20) + (nd.2.1 <<< 40)
  selectLive liveMask (decodeDBank depth ops g.rawD)

def Forest.nodeVals (g : Forest) (nd : NodeData) : List Sig :=
  (g.nodeWires nd).map Prod.fst

def rawPermN (vmask : Nat) (perm : List Nat) : List Nat :=
  ([0, 1, 2, 3, 4, 5] : List Nat).filterMap fun i =>
    if vmask.testBit i then some (allVars6.getD (perm.getD i 0) 0).toNat else none

noncomputable def fastPermState (g : Forest) (k : Nat) (tag : Nat) : Option (List Nat) :=
  ((g.maps k).find tag).bind fun (path, ai) =>
  (g.levels (k - 1)).bind fun tree =>
  (g.autos[ai]?).map fun perm =>
    let x := tree.get path
    selectLive ((x.1 >>> 4) &&& 65535) (decodeN (x.1 &&& 15) ((x.1 >>> 20) + (x.2.1 <<< 40)) (rawPermN g.vmask perm))

def rowPermSurjB (p : List Nat) : Bool :=
  (List.range 64).all fun y =>
    (List.range 64).any fun x =>
      (rowPerm p ⟨x % 64, Nat.mod_lt _ (by decide)⟩).val == y

theorem rowPermSurjB_sound {p : List Nat} (h : rowPermSurjB p = true) :
    Function.Surjective (rowPerm p) := by
  intro y
  have hy := List.all_eq_true.mp h y.val (List.mem_range.mpr y.isLt)
  obtain ⟨x, _, hx⟩ := List.any_eq_true.mp hy
  exact ⟨⟨x % 64, Nat.mod_lt _ (by decide)⟩, Fin.ext (beq_iff_eq.mp hx)⟩

def autoCheck (T : Sig) (p : List Nat) : Bool :=
  rowPermSurjB p && (sigPerm p T == T) &&
  ([0, 1, 2, 3, 4, 5] : List Nat).all (fun i => sigPerm p (allVars6.getD i 0) == allVars6.getD (p.getD i 0) 0)

theorem autoCheck_rotate {T : Sig} {p : List Nat} (hok : autoCheck T p = true)
    {k : Nat} {ws : List Sig} (himp : ImpossibleBV T k ws.toFinset) :
    ImpossibleBV T k (ws.map (sigPerm p)).toFinset := by
  simp only [autoCheck, Bool.and_eq_true, beq_iff_eq] at hok
  have hsurj := rowPermSurjB_sound hok.1.1
  have hbij : Function.Bijective (rowPerm p) := ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩
  obtain ⟨invF, hinvL, hinvR⟩ := Function.bijective_iff_has_inverse.mp hbij
  have hinvSurj : Function.Surjective invF := fun r => ⟨rowPerm p r, hinvL r⟩
  have hinvSig (a : Sig) : rename6 invF (sigPerm p a) = a := by
    apply bitBV_ext; intro r; rw [bit6_rename, sigPerm, bit6_rename, hinvR]
  have hTinv : rename6 invF T = T := by conv => lhs; rw [← hok.1.2]; exact hinvSig T
  intro t ht hlive
  have hrun := live6_rename hlive invF hinvSurj
  rw [hTinv] at hrun
  have hback : (ws.map (sigPerm p)).toFinset.image (rename6 invF) = ws.toFinset := by
    ext a; simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩; simpa only [hinvSig] using hw
    · intro ha; exact ⟨_, ⟨a, ha, rfl⟩, hinvSig a⟩
  rw [hback] at hrun
  exact himp t ht hrun

theorem zipWith_fst_map {α β γ : Type} (f : α → β → γ) (g : γ → α) (h : ∀ a b, g (f a b) = a)
    (xs : List α) (ys : List β) (hlen : xs.length = ys.length) :
    (xs.zipWith f ys).map g = xs := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons a xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons b ys => simp [h, ih ys (by simpa using hlen)]

theorem filterMap_map_eq {α β γ : Type} (l : List α) (p : α → Bool) (f : α → β) (g : β → γ) :
    (l.filterMap fun x => if p x then some (f x) else none).map g =
    l.filterMap fun x => if p x then some (g (f x)) else none := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.filterMap_cons]
    cases p a <;> simp [ih]

theorem fastPermState_sound (g : Forest) (k tag : Nat) {ys : List Nat}
    (hlen : (rawOf g.vmask).length = g.rawCols.length)
    (hauto : ∀ p ∈ g.autos, autoCheck g.target p = true)
    (hprev : ∀ tree, g.levels (k - 1) = some tree → ∀ p, ImpossibleBV g.target (k - 1) (g.nodeVals (tree.get p)).toFinset)
    (h : fastPermState g k tag = some ys) :
    ∃ xs : List Sig, ys = xs.map BitVec.toNat ∧ ImpossibleBV g.target (k - 1) xs.toFinset := by
  unfold fastPermState at h
  cases hf : (g.maps k).find tag with
  | none => simp [hf] at h
  | some pr =>
    obtain ⟨path, ai⟩ := pr
    simp only [hf, Option.bind_some] at h
    cases hl : g.levels (k - 1) with
    | none => simp [hl] at h
    | some tree =>
      simp only [hl, Option.bind_some] at h
      cases ha : g.autos[ai]? with
      | none => simp [ha] at h
      | some perm =>
        simp only [ha, Option.map_some, Option.some.injEq] at h
        have hok := hauto perm (List.mem_of_getElem? ha)
        have hok' := hok
        simp only [autoCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hok'
        rcases hnd : tree.get path with ⟨p0, p1, hpacked⟩
        rw [hnd] at h
        refine ⟨(g.nodeVals (p0, p1, hpacked)).map (sigPerm perm), ?_, ?_⟩
        · let F (a : Sig) : Nat := (sigPerm perm a).toNat
          have F0 : F zeroBV = 0 := by
            change (rename6 (rowPerm perm) zeroBV).toNat = 0
            rw [(rename6_const _).1]; simp [zeroBV]
          have Fb (op a b) : F (binBV op a b) = zN op (F a) (F b) := by
            change (sigPerm perm (binBV op a b)).toNat = zN op (sigPerm perm a).toNat (sigPerm perm b).toNat
            rw [zN_full, sigPerm, rename6_bin]; rfl
          have hrawF : g.rawD.map (fun w => F w.1) = rawPermN g.vmask perm := by
            have h1 : g.rawD.map Prod.fst = rawOf g.vmask :=
              zipWith_fst_map _ Prod.fst (fun _ _ => rfl) _ _ hlen
            rw [show g.rawD.map (fun w => F w.1) = (g.rawD.map Prod.fst).map F by rw [List.map_map]; rfl, h1]
            unfold rawOf rawPermN
            rw [filterMap_map_eq]
            apply List.filterMap_congr; intro i hi
            split; · congr 1; exact congrArg BitVec.toNat (hok'.2 i hi)
            · rfl
          rw [← h]; unfold Forest.nodeVals Forest.nodeWires
          rw [List.map_map, List.map_map, selectLive_map]
          change selectLive ((p0 >>> 4) &&& 65535) (decodeN (p0 &&& 15) ((p0 >>> 20) + (p1 <<< 40)) (rawPermN g.vmask perm)) =
            selectLive ((p0 >>> 4) &&& 65535) ((decodeDBank (p0 &&& 15) ((p0 >>> 20) + (p1 <<< 40)) g.rawD).map fun w => F w.1)
          rw [decodeN_eq F F0 Fb, hrawF]
        · exact autoCheck_rotate hok (hnd ▸ hprev tree hl path)

def buildRule (g : Forest) (ops depth : Nat) (bank : List DWire) (ci paid : Nat) : Option BoundPool :=
  (g.cuts[ci]?).bind fun c =>
    let cs := chosenSteps bank ops paid depth
    (makePool c.dom (rawOf g.vmask) cs).map fun pool => (c.dom, c.L, cs.length, pool)

theorem buildRule_sound (g : Forest)
    (hcuts : ∀ c ∈ g.cuts, Slice (rawOf g.vmask) g.target c.dom c.L)
    {ops depth bank ci paid p} (h : buildRule g ops depth bank ci paid = some p) :
    ValidPool (rawOf g.vmask) g.target p := by
  unfold buildRule at h
  cases hc : g.cuts[ci]? with
  | none => simp [hc] at h
  | some c =>
    simp only [hc, Option.bind_some] at h
    cases hm : makePool c.dom (rawOf g.vmask) (chosenSteps bank ops paid depth) with
    | none => simp [hm] at h
    | some pool =>
      simp only [hm, Option.map_some, Option.some.injEq] at h
      subst p
      exact build_valid (hcuts c (List.mem_of_getElem? hc)) _ hm

-- Fast Nat-based link check (zero allocation of child list!)
noncomputable def linkAt (fl : Nat → Option (List Nat)) (wsN : List Nat) (totH : Nat)
    (x y zVal : Nat) (ka kb : Bool) : Bool :=
  Option.rec false (fun ys => forceMap (fun v => v) ys fun ys =>
    and (anyEq zVal ys)
      (and (wsN.all fun v => or (and (not ka) (Nat.beq v x)) (or (and (not kb) (Nat.beq v y)) (anyEq v ys)))
        (ys.all fun v => or (Nat.beq v zVal) (and (and (or ka (not (Nat.beq v x))) (or kb (not (Nat.beq v y)))) (anyEq v wsN)))))
    (fl (Nat.add (kwN zVal) (Nat.sub (Nat.sub totH (cond ka 0 (kwN x))) (cond kb 0 (kwN y)))))

theorem unique_fst {ws : List DWire} (nd : (ws.map Prod.fst).Nodup) {a b : DWire}
    (ha : a ∈ ws) (hb : b ∈ ws) (eq : a.1 = b.1) : a = b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn, ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haT <;> rcases List.mem_cons.mp hb with rfl | hbT
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbT))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haT))
    · exact ih ht haT hbT

theorem mem_delOne {α} [BEq α] [LawfulBEq α] {v : List α} (nd : v.Nodup) (a w : α) (k : Bool) :
    w ∈ delOne v a k ↔ w ∈ v ∧ (w ≠ a ∨ k = true) := by
  cases k <;> simp [delOne, nd.mem_erase_iff, and_comm]

theorem kept_value {ws : List DWire} (nd : (ws.map Prod.fst).Nodup) {a b : DWire}
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v ≠ a.1 ∨ ka = true) ∧ (v ≠ b.1 ∨ kb = true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  simp only [delTwo, List.mem_map, mem_delOne wn, mem_delOne dn]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨⟨_, hw.1.1, rfl⟩, hw.1.2.imp (fun ne eq => ne (unique_fst nd hw.1.1 ha eq)) id,
      hw.2.imp (fun ne eq => ne (unique_fst nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w, hm, rfl⟩, h1, h2⟩
    exact ⟨w, ⟨⟨hm, h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
      h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩, rfl⟩

theorem linkAt_sound {T : Sig} {k : Nat} {fl : Nat → Option (List Nat)}
    {ws : List DWire} {i j op : Nat} {ka kb : Bool}
    (nd : (ws.map Prod.fst).Nodup) (hi : i < ws.length) (hj : j < ws.length) (hij : i ≠ j)
    (hfl : ∀ tag ys, fl tag = some ys → ∃ xs : List Sig, ys = xs.map BitVec.toNat ∧ ImpossibleBV T k xs.toFinset)
    (h : linkAt fl (ws.map fun w => w.1.toNat) ((ws.map fun w => kwN w.1.toNat).sum)
          (ws[i]).1.toNat (ws[j]).1.toNat (binBV op (ws[i]).1 (ws[j]).1).toNat ka kb = true) :
    ImpossibleBV T k (binBV op (ws[i]).1 (ws[j]).1 :: (delTwo ws ws[i] ws[j] ka kb).map Prod.fst).toFinset := by
  let a := ws[i]; let b := ws[j]; let z := binBV op a.1 b.1
  have ha : a ∈ ws := List.getElem_mem hi
  have hb : b ∈ ws := List.getElem_mem hj
  have hne1 : a.1 ≠ b.1 := fun e => hij ((List.Nodup.getElem_inj_iff nd (hi := by simpa using hi) (hj := by simpa using hj)).mp (by simpa using e))
  have hne : a ≠ b := fun e => hne1 (congrArg Prod.fst e)
  unfold linkAt at h
  generalize Nat.add (kwN z.toNat) _ = tag at h
  cases hf : fl tag with
  | none => simp [hf] at h
  | some ys =>
    obtain ⟨xs, rfl, himp⟩ := hfl tag ys hf
    rw [hf] at h
    simp only [forceMap_eq, List.map_id', Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
      anyEq_iff, Nat.beq_eq, Bool.not_eq_true'] at h
    obtain ⟨h1, h2, h3⟩ := h
    have back {v : Sig} (hv : v.toNat ∈ xs.map BitVec.toNat) : v ∈ xs := by
      obtain ⟨w, hw, e⟩ := List.mem_map.mp hv; exact BitVec.toNat_inj.mp e ▸ hw
    have hset : (z :: (delTwo ws a b ka kb).map Prod.fst).toFinset = xs.toFinset := by
      ext v; simp only [List.mem_toFinset, List.mem_cons]
      constructor
      · rintro (rfl | hv)
        · exact back h1
        · obtain ⟨hw, va, vb⟩ := (kept_value nd ha hb ka kb v).mp hv
          obtain ⟨w, hm, rfl⟩ := List.mem_map.mp hw
          rcases h2 _ (List.mem_map_of_mem hm) with ⟨hka, e⟩ | ⟨hkb, e⟩ | hm2
          · rcases va with va | va
            · exact absurd (BitVec.toNat_inj.mp e) va
            · simp [va] at hka
          · rcases vb with vb | vb
            · exact absurd (BitVec.toNat_inj.mp e) vb
            · simp [vb] at hkb
          · exact back hm2
      · intro hv
        rcases h3 _ (List.mem_map_of_mem hv) with e | ⟨⟨hva, hvb⟩, hm⟩
        · exact Or.inl (BitVec.toNat_inj.mp e)
        · refine Or.inr ((kept_value nd ha hb ka kb v).mpr ⟨?_, ?_, ?_⟩)
          · obtain ⟨w, hw, e⟩ := List.mem_map.mp hm
            exact BitVec.toNat_inj.mp e ▸ List.mem_map_of_mem hw
          · rcases hva with rfl | hne'
            · exact Or.inr rfl
            · exact Or.inl fun e => by subst e; rw [Nat.beq_refl] at hne'; exact Bool.noConfusion hne'
          · rcases hvb with rfl | hne'
            · exact Or.inr rfl
            · exact Or.inl fun e => by subst e; rw [Nat.beq_refl] at hne'; exact Bool.noConfusion hne'
    rwa [hset]

-- The unified fast kernel node checker!
noncomputable def checkMove (fl : Nat → Option (List Nat)) (qs : List QS)
    (k n allW totH : Nat) (cov : CovN) (wsN wsC : List Nat)
    (i j op xi yi ci cj cz : Nat) (ka kb : Bool) : Bool :=
  let len := 1 + (n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if Nat.ble (Nat.succ k) len then true else
  force (restCovN cov ci cj ka kb) fun rs =>
  if !(Nat.beq (Nat.lor rs cz) allW) then true else
  force (zN op xi yi) fun zVal =>
  if or (Nat.beq zVal 0) (or (Nat.beq zVal 18446744073709551615) (anyEq zVal wsN)) then true else
  or (qs.any fun s => fastCost s i j op ka kb)
     (linkAt fl wsN totH xi yi zVal ka kb)

noncomputable def checkPairOp (fl : Nat → Option (List Nat)) (qs : List QS)
    (k n allW totH : Nat) (cov : CovN) (wsN wsP wsQ wsC : List Nat) (i j op : Nat) : Bool :=
  force (wsP.getD i 0) fun pi => force (wsP.getD j 0) fun pj =>
  force (wsQ.getD i 0) fun qi => force (wsQ.getD j 0) fun qj =>
  force (Nat.xor (zN op pi pj) (zN op qi qj)) fun cz =>
  let xi := wsN.getD i 0; let yi := wsN.getD j 0
  let ci := wsC.getD i 0; let cj := wsC.getD j 0
  let f := checkMove fl qs k n allW totH cov wsN wsC i j op xi yi ci cj cz
  and (and (f false false) (f true false)) (and (f false true) (f true true))

noncomputable def checkPair (fl : Nat → Option (List Nat)) (qs : List QS)
    (k n allW totH : Nat) (cov : CovN) (wsN wsP wsQ wsC : List Nat) (i j : Nat) : Bool :=
  let f := checkPairOp fl qs k n allW totH cov wsN wsP wsQ wsC i j
  and (and (f 0) (f 1)) (and (f 2) (f 3))

noncomputable def checkPairsFrom (fl : Nat → Option (List Nat)) (qs : List QS)
    (k n allW totH : Nat) (cov : CovN) (wsN wsP wsQ wsC : List Nat) (i : Nat) : List Nat → Bool
  | [] => true
  | j :: js => and (checkPair fl qs k n allW totH cov wsN wsP wsQ wsC i j)
                   (checkPairsFrom fl qs k n allW totH cov wsN wsP wsQ wsC i js)

noncomputable def checkAllPairs (fl : Nat → Option (List Nat)) (qs : List QS)
    (k n allW totH : Nat) (cov : CovN) (wsN wsP wsQ wsC : List Nat) : List Nat → Bool
  | [] => true
  | i :: js => and (checkPairsFrom fl qs k n allW totH cov wsN wsP wsQ wsC i js)
                   (checkAllPairs fl qs k n allW totH cov wsN wsP wsQ wsC js)

noncomputable def fastNodeOK (g : Forest) (k : Nat) (nd : NodeData) : Bool :=
  let depth := nd.1 &&& 15
  let liveMask := (nd.1 >>> 4) &&& 65535
  let ops := (nd.1 >>> 20) + (nd.2.1 <<< 40)
  let bank := decodeDBank depth ops g.rawD
  let ws := selectLive liveMask bank
  let vals := ws.map Prod.fst
  and (decide vals.Nodup) (and (!(vals.contains g.target))
    (if Nat.beq k 0 then true else
      let hints := unpackHints nd.2.2
      let pools := hints.filterMap fun h => buildRule g ops depth bank h.1 h.2
      forceMap (fun w : DWire => w.1.toNat) ws fun wsN =>
      forceMap (fun w : DWire => w.2.1) ws fun wsP =>
      forceMap (fun w : DWire => w.2.2) ws fun wsQ =>
      forceMap dcol ws fun wsC =>
      force (wsN.map kwN).sum fun totH =>
      let cov := covOfCols wsC
      let allW := allOnesNat g.pos.length
      forcePools (k - 1) ws pools fun qs =>
      checkAllPairs (fastPermState g k) qs k ws.length allW totH cov wsN wsP wsQ wsC (List.range ws.length)))

-- Enum step & fastNodeOK soundness!
def childTwo (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  binBV d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x; simp [h.mem_erase_iff]

theorem enum_step {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, d < 4 → ∀ ka kb, a ≠ b → binBV d a b ∉ ws →
      properBV (binBV d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      ImpossibleBV T (cap - 1) (childTwo ws a b d ka kb).toFinset) :
    ImpossibleBV T cap ws.toFinset := by
  classical
  intro k hk h
  generalize he : ws.toFinset = S at h
  induction h using LiveBV.ind with
  | stop _ => exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  | @binary k U a b d hd ha hb hab hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : binBV d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := liveBV_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U); let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest = (ws.erase a).erase b by rfl, erase_fin (hn.erase _) b, erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin, kept_fin, er, he]; ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j = a <;>
        by_cases jb : j = b <;> simp_all [ka, kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => hn.not_mem_erase (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept, ar, hab]
    have nd : (childTwo ws a b d ka kb).Nodup :=
      List.nodup_cons.mpr ⟨fun h => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h))),
        kept_nd ka a _ nk ax⟩
    have eq : (childTwo ws a b d ka kb).toFinset = insert (binBV d a b) U := by
      change (binBV d a b :: kept ka a (kept kb b rest)).toFinset = _; simp [ke]
    have sc := liveBV_size tail
    have len : (childTwo ws a b d ka kb).length ≤ cap := by rw [← List.toFinset_card_of_nodup nd, eq]; omega
    exact twoStep a am b bm d hd ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)

theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w = a ∧ k = true) ∨ w ∈ v := by cases k <;> simp [kept]

theorem binary_front {ws : List DWire} (nd : (ws.map Prod.fst).Nodup) {a b : DWire}
    (ha : a ∈ ws) (hb : b ∈ ws) (ne : a.1 ≠ b.1) (d : Nat) (ka kb : Bool) :
    (binBV d a.1 b.1 :: (delTwo ws a b ka kb).map Prod.fst).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f := Prod.fst) ha
  have bv' := List.mem_map_of_mem (f := Prod.fst) hb
  simp only [childTwo, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset,
    kept_value nd ha hb, keep_mem, (nd.erase _).mem_erase_iff, nd.mem_erase_iff]
  by_cases va : v = a.1 <;> by_cases vb : v = b.1 <;> cases ka <;> cases kb <;> simp_all

theorem childTwo_swap (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : d < 4) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  ext x
  simp only [childTwo, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset,
    keep_mem, (nd.erase _).mem_erase_iff, nd.mem_erase_iff, binBV_flip hd a b]
  tauto

theorem checkAllPairs_at {fl qs k n allW totH cov wsN wsP wsQ wsC}
    {js : List Nat} (h : checkAllPairs fl qs k n allW totH cov wsN wsP wsQ wsC js = true)
    {i j : Nat} (hi : i ∈ js) (hj : j ∈ js) (hij : i ≠ j) :
    checkPair fl qs k n allW totH cov wsN wsP wsQ wsC i j = true ∨
    checkPair fl qs k n allW totH cov wsN wsP wsQ wsC j i = true := by
  have from_at {a : Nat} {l : List Nat} (hl : checkPairsFrom fl qs k n allW totH cov wsN wsP wsQ wsC a l = true)
      {b : Nat} (hb : b ∈ l) : checkPair fl qs k n allW totH cov wsN wsP wsQ wsC a b = true := by
    induction l with
    | nil => simp at hb
    | cons x l ih =>
      simp only [checkPairsFrom, Bool.and_eq_true] at hl
      rcases List.mem_cons.mp hb with rfl | hbT
      · exact hl.1
      · exact ih hl.2 hbT
  induction js with
  | nil => simp at hi
  | cons a js ih =>
    simp only [checkAllPairs, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hi with rfl | hiT
    · exact Or.inl (from_at h.1 ((List.mem_cons.mp hj).resolve_left (Ne.symm hij)))
    · rcases List.mem_cons.mp hj with rfl | hjT
      · exact Or.inr (from_at h.1 hiT)
      · exact ih h.2 hiT hjT

theorem fastNodeOK_sound (g : Forest) (k : Nat) (nd : NodeData)
    (hlen : (rawOf g.vmask).length = g.rawCols.length)
    (hcrit : CritOK g.target g.pos g.neg)
    (hrawF : ∀ w ∈ g.rawD, Faithful g.pos g.neg w)
    (hcuts : ∀ c ∈ g.cuts, Slice (rawOf g.vmask) g.target c.dom c.L)
    (hauto : ∀ p ∈ g.autos, autoCheck g.target p = true)
    (hprev : k > 0 → ∀ tree, g.levels (k - 1) = some tree →
      ∀ p, ImpossibleBV g.target (k - 1) (g.nodeVals (tree.get p)).toFinset)
    (hok : fastNodeOK g k nd = true) :
    ImpossibleBV g.target k (g.nodeVals nd).toFinset := by
  let depth := nd.1 &&& 15
  let liveMask := (nd.1 >>> 4) &&& 65535
  let ops := (nd.1 >>> 20) + (nd.2.1 <<< 40)
  let hints := unpackHints nd.2.2
  unfold fastNodeOK at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not] at hok
  obtain ⟨hnd, hout, hbody⟩ := hok
  let bank := decodeDBank depth ops g.rawD
  let ws := selectLive liveMask bank
  change ImpossibleBV g.target k (ws.map Prod.fst).toFinset
  by_cases hk0 : k = 0
  · subst hk0; intro t ht hlive
    have : t = 0 := by omega
    subst this; obtain ⟨hS, _⟩ := hlive
    exact hout (List.mem_toFinset.mp (by rw [hS]; exact Finset.mem_singleton_self _))
  have hkpos : k > 0 := by omega
  have hk0b : Nat.beq k 0 = false := Bool.eq_false_iff.mpr fun h => hk0 (Nat.eq_of_beq_eq_true h)
  simp only [hk0b, Bool.false_eq_true, ite_false, forceMap_eq, force_eq, forcePools_eq] at hbody
  let pools := hints.filterMap fun h => buildRule g ops depth bank h.1 h.2
  have hpv : ∀ p ∈ pools, ValidPool (rawOf g.vmask) g.target p := by
    intro p hp; obtain ⟨h', _, heq⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound g hcuts heq
  have hfl : ∀ tag ys, fastPermState g k tag = some ys →
      ∃ xs : List Sig, ys = xs.map BitVec.toNat ∧ ImpossibleBV g.target (k - 1) xs.toFinset :=
    fun tag ys hs => fastPermState_sound g k tag hlen hauto (hprev hkpos) hs
  have hwsF : ∀ w ∈ ws, Faithful g.pos g.neg w := fun w hw =>
    decodeDBank_faithful depth ops g.rawD hrawF w ((selectLive_sub liveMask bank).subset hw)
  -- Helper: check one ordered pair (i, j)
  have onePair (i j op : Nat) (ka kb : Bool)
      (hi : i < ws.length) (hj : j < ws.length) (hij : i ≠ j) (hop : op < 4)
      (hfr : binBV op (ws[i]).1 (ws[j]).1 ∉ ws.map Prod.fst)
      (hpr : properBV (binBV op (ws[i]).1 (ws[j]).1))
      (hcp : checkPair (fastPermState g k) (pools.map (quickSpec (k - 1) ws)) k ws.length
        (allOnesNat g.pos.length) ((ws.map fun w => w.1.toNat).map kwN).sum
        (covOfCols (ws.map dcol)) (ws.map fun w => w.1.toNat) (ws.map fun w => w.2.1)
        (ws.map fun w => w.2.2) (ws.map dcol) i j = true) :
      ImpossibleBV g.target (k - 1) (binBV op (ws[i]).1 (ws[j]).1 :: (delTwo ws ws[i] ws[j] ka kb).map Prod.fst).toFinset := by
    simp only [checkPair, Bool.and_eq_true] at hcp
    have hcop : checkPairOp (fastPermState g k) (pools.map (quickSpec (k - 1) ws)) k ws.length
        (allOnesNat g.pos.length) ((ws.map fun w => w.1.toNat).map kwN).sum
        (covOfCols (ws.map dcol)) (ws.map fun w => w.1.toNat) (ws.map fun w => w.2.1)
        (ws.map fun w => w.2.2) (ws.map dcol) i j op = true := by
      rcases op_four hop with rfl | rfl | rfl | rfl
      · exact hcp.1.1
      · exact hcp.1.2
      · exact hcp.2.1
      · exact hcp.2.2
    simp only [checkPairOp, force_eq, Bool.and_eq_true] at hcop
    have hcm : checkMove (fastPermState g k) (pools.map (quickSpec (k - 1) ws)) k ws.length
        (allOnesNat g.pos.length) ((ws.map fun w => w.1.toNat).map kwN).sum
        (covOfCols (ws.map dcol)) (ws.map fun w => w.1.toNat) (ws.map dcol) i j op
        ((ws.map fun w => w.1.toNat).getD i 0) ((ws.map fun w => w.1.toNat).getD j 0)
        ((ws.map dcol).getD i 0) ((ws.map dcol).getD j 0)
        (Nat.xor (zN op ((ws.map fun w => w.2.1).getD i 0) ((ws.map fun w => w.2.1).getD j 0))
                 (zN op ((ws.map fun w => w.2.2).getD i 0) ((ws.map fun w => w.2.2).getD j 0))) ka kb = true := by
      cases ka <;> cases kb
      · exact hcop.1.1
      · exact hcop.2.1
      · exact hcop.1.2
      · exact hcop.2.2
    have gN (t : Nat) (ht : t < ws.length) : (ws.map fun w : DWire => w.1.toNat).getD t 0 = (ws[t]).1.toNat := by
      simp [List.getD_eq_getElem?_getD, ht]
    have gP (t : Nat) (ht : t < ws.length) : (ws.map fun w : DWire => w.2.1).getD t 0 = (ws[t]).2.1 := by
      simp [List.getD_eq_getElem?_getD, ht]
    have gQ (t : Nat) (ht : t < ws.length) : (ws.map fun w : DWire => w.2.2).getD t 0 = (ws[t]).2.2 := by
      simp [List.getD_eq_getElem?_getD, ht]
    have gC (t : Nat) (ht : t < ws.length) : (ws.map dcol).getD t 0 = dcol ws[t] := by
      simp [List.getD_eq_getElem?_getD, ht]
    rw [gN i hi, gN j hj, gP i hi, gP j hj, gQ i hi, gQ j hj, gC i hi, gC j hj] at hcm
    unfold checkMove at hcm
    simp only [force_eq] at hcm
    -- Prove ImpossibleBV directly!
    intro t ht hlive
    have ha : ws[i] ∈ ws := List.getElem_mem hi
    have hb : ws[j] ∈ ws := List.getElem_mem hj
    have hne1 : (ws[i]).1 ≠ (ws[j]).1 := fun e => hij ((List.Nodup.getElem_inj_iff hnd (hi := by simpa using hi) (hj := by simpa using hj)).mp (by simpa using e))
    have hne : ws[i] ≠ ws[j] := fun e => hne1 (congrArg Prod.fst e)
    let rest := delTwo ws ws[i] ws[j] ka kb
    let zD := dbin op ws[i] ws[j]
    have hsub : rest.Sublist ws := delTwo_sub ws ws[i] ws[j] ka kb
    have hndc : (zD.1 :: rest.map Prod.fst).Nodup :=
      List.nodup_cons.mpr ⟨fun hm => hfr ((hsub.map _).subset hm), hnd.sublist (hsub.map _)⟩
    have hsz := liveBV_size hlive
    change (zD.1 :: rest.map Prod.fst).toFinset.card ≤ t + 1 at hsz
    rw [List.toFinset_card_of_nodup hndc] at hsz
    have hlenC : 1 + (ws.length - (if ka then 0 else 1) - (if kb then 0 else 1)) = (zD.1 :: rest.map Prod.fst).length := by
      rw [List.length_cons, List.length_map, delTwo_len ws ws[i] ws[j] ka kb ha hb hne, Nat.add_comm 1]
    have hbleF : Nat.ble (Nat.succ k) (1 + (ws.length - (if ka then 0 else 1) - (if kb then 0 else 1))) = false := by
      apply Bool.eq_false_iff.mpr; intro hb; have := Nat.ble_eq.mp hb; omega
    rw [hbleF] at hcm; simp only [Bool.false_eq_true, ite_false] at hcm
    -- Cover check must pass!
    have hcovAll := live6_cover_eq hcrit
      (fun w hw => by rcases List.mem_cons.mp hw with rfl | hwr; exact faithful_dbin op (hwsF _ ha) (hwsF _ hb); exact hwsF _ (hsub.subset hwr))
      (show LiveBV g.target t ((zD :: rest).map Prod.fst).toFinset from hlive)
    simp only [List.map_cons, orList] at hcovAll
    rw [delTwo_cov ha hb hne ka kb] at hcovAll
    have hcovAll' : Nat.lor (restCovN (covOfCols (ws.map dcol)) (dcol ws[i]) (dcol ws[j]) ka kb) (dcol zD) = allOnesNat g.pos.length :=
      (Nat.lor_comm _ _).trans hcovAll
    have hcovEq : Nat.beq (Nat.lor (restCovN (covOfCols (ws.map dcol)) (dcol ws[i]) (dcol ws[j]) ka kb) (dcol zD)) (allOnesNat g.pos.length) = true :=
      Nat.beq_eq.mpr hcovAll'
    change (if !(Nat.beq (Nat.lor (restCovN (covOfCols (ws.map dcol)) (dcol ws[i]) (dcol ws[j]) ka kb) (dcol zD)) (allOnesNat g.pos.length)) then true else _) = true at hcm
    rw [hcovEq] at hcm; simp only [Bool.not_true, ite_false] at hcm
    -- zVal is proper and fresh!
    rw [zN_full] at hcm
    have hz0 : Nat.beq (binBV op (ws[i]).1 (ws[j]).1).toNat 0 = false := by
      apply Bool.eq_false_iff.mpr; intro he
      exact hpr.1 (BitVec.toNat_inj.mp (by simpa [zeroBV] using Nat.eq_of_beq_eq_true he))
    have hz1 : Nat.beq (binBV op (ws[i]).1 (ws[j]).1).toNat 18446744073709551615 = false := by
      apply Bool.eq_false_iff.mpr; intro he
      have hall : (oneBV (N := 64)).toNat = 18446744073709551615 := by decide +kernel
      exact hpr.2 (BitVec.toNat_inj.mp (by rw [hall]; exact Nat.eq_of_beq_eq_true he))
    have hzFresh : anyEq (binBV op (ws[i]).1 (ws[j]).1).toNat (ws.map fun w => w.1.toNat) = false := by
      apply Bool.eq_false_iff.mpr; intro hm
      obtain ⟨w, hw, he⟩ := List.mem_map.mp ((anyEq_iff _ _).mp hm)
      exact hfr (BitVec.toNat_inj.mp he.symm ▸ List.mem_map_of_mem hw)
    rw [hz0, hz1, hzFresh] at hcm
    simp only [Bool.or_false, Bool.false_eq_true, ite_false, Bool.or_eq_true, List.any_eq_true] at hcm
    rcases hcm with ⟨_, hqm, hfc⟩ | hlk
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hqm
      exact fastCost_sound (hpv p hp) hi hj hij hop hnd hfr hfc t ht hlive
    · have hsum : ((ws.map fun w : DWire => w.1.toNat).map kwN).sum = (ws.map fun w : DWire => kwN w.1.toNat).sum := by
        rw [List.map_map]; rfl
      rw [hsum] at hlk
      exact linkAt_sound hnd hi hj hij hfl hlk t ht hlive
  -- Apply enum_step!
  apply enum_step hnd hout
  intro a ha b hb d hd ka kb hab hfr hpr _
  obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
  obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hb
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha'
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb'
  have hij : i ≠ j := fun e => hab (by subst e; rfl)
  rcases checkAllPairs_at hbody (List.mem_range.mpr hi) (List.mem_range.mpr hj) hij with hcp | hcp
  · rw [← binary_front hnd (List.getElem_mem hi) (List.getElem_mem hj) hab]
    exact onePair i j d ka kb hi hj hij hd hfr hpr hcp
  · rw [childTwo_swap _ hnd _ _ d hd ka kb, ← binary_front hnd (List.getElem_mem hj) (List.getElem_mem hi) (Ne.symm hab)]
    exact onePair j i (flipOp d) kb ka hj hi (Ne.symm hij) (flipOp_lt hd)
      (binBV_flip (N := 64) hd _ _ ▸ hfr) (binBV_flip (N := 64) hd _ _ ▸ hpr) hcp

-- Forest validity & induction over levels!
def graphValid (g : Forest) (baseOf : Nat → List Sig × Sig × Nat) : Bool :=
  ((rawOf g.vmask).length == g.rawCols.length) &&
  (List.range g.pos.length).all (fun i =>
    bitBV (g.pos.getD i ⟨0, by decide⟩) g.target != bitBV (g.neg.getD i ⟨0, by decide⟩) g.target) &&
  g.rawD.all (fun w =>
    (List.range g.pos.length).all (fun i =>
      (w.2.1.testBit i == bitBV (g.pos.getD i ⟨0, by decide⟩) w.1) &&
      (w.2.2.testBit i == bitBV (g.neg.getD i ⟨0, by decide⟩) w.1)) &&
    decide (w.2.1 < 2 ^ g.pos.length) && decide (w.2.2 < 2 ^ g.pos.length)) &&
  g.cuts.all (fun c => checkCut g.vmask g.target c baseOf) &&
  g.autos.all (fun p => autoCheck g.target p)

def levelsChecked (g : Forest) : Prop :=
  ∀ k ≤ g.cap, ∀ tree, g.levels k = some tree → tree.all (fastNodeOK g k) = true

theorem forest_all (g : Forest) (baseOf : Nat → List Sig × Sig × Nat)
    (hb : ∀ k, k ≠ 0 → LowerBV (baseOf k).1 (baseOf k).2.1 (baseOf k).2.2)
    (hg : graphValid g baseOf = true) (hl : levelsChecked g) :
    ∀ k ≤ g.cap, ∀ tree, g.levels k = some tree → ∀ p, ImpossibleBV g.target k (g.nodeVals (tree.get p)).toFinset := by
  unfold graphValid at hg
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, bne_iff_ne, decide_eq_true_eq] at hg
  obtain ⟨⟨⟨⟨hlen, hcrit⟩, hrawF⟩, hcuts⟩, hautos⟩ := hg
  have hcrit' : CritOK g.target g.pos g.neg := fun i hi => hcrit i (List.mem_range.mpr hi)
  have hrawF' : ∀ w ∈ g.rawD, Faithful g.pos g.neg w := fun w hw => by
    have := hrawF w hw; exact ⟨fun i hi => this.1.1 i (List.mem_range.mpr hi), this.1.2, this.2⟩
  have hcuts' : ∀ c ∈ g.cuts, Slice (rawOf g.vmask) g.target c.dom c.L :=
    fun c hc => checkCut_sound hb (hcuts c hc)
  intro k
  induction k with
  | zero =>
    intro hk tree htree p
    exact fastNodeOK_sound g 0 (tree.get p) hlen hcrit' hrawF' hcuts' hautos (by omega)
      (BTree.get_all (hl 0 hk tree htree) p)
  | succ k ih =>
    intro hk tree htree p
    exact fastNodeOK_sound g (k + 1) (tree.get p) hlen hcrit' hrawF' hcuts' hautos
      (fun _ t ht q => ih (by omega) t ht q)
      (BTree.get_all (hl (k + 1) hk tree htree) p)

def rootCheck (g : Forest) : Bool :=
  properB g.target && plainWordBV g.target && (rawOf g.vmask).all plainWordBV &&
  (rawOf g.vmask).all (essentialCheck6 g.target (rawOf g.vmask)) &&
  match g.levels g.cap with
  | none => false
  | some tree =>
    let vals := g.nodeVals (tree.get 0)
    vals.all (fun v => (rawOf g.vmask).contains v) && (rawOf g.vmask).all (fun v => vals.contains v)

theorem lower_forest (g : Forest) (baseOf : Nat → List Sig × Sig × Nat)
    (hb : ∀ k, k ≠ 0 → LowerBV (baseOf k).1 (baseOf k).2.1 (baseOf k).2.2)
    (hg : graphValid g baseOf = true) (hl : levelsChecked g) (hr : rootCheck g = true) :
    LowerBV (rawOf g.vmask) g.target (g.cap + 1) := by
  unfold rootCheck at hr
  simp only [Bool.and_eq_true] at hr
  obtain ⟨⟨⟨⟨hp, hpt⟩, hpr⟩, hess⟩, hroot⟩ := hr
  cases hlev : g.levels g.cap with
  | none => simp [hlev] at hroot
  | some tree =>
    simp only [hlev, Bool.and_eq_true, List.all_eq_true, List.contains_eq_mem, decide_eq_true_eq] at hroot
    have himp := forest_all g baseOf hb hg hl g.cap (Nat.le_refl _) tree hlev 0
    have heq : (g.nodeVals (tree.get 0)).toFinset = (rawOf g.vmask).toFinset := by
      ext v; simp only [List.mem_toFinset]; exact ⟨hroot.1 v, hroot.2 v⟩
    rw [heq] at himp
    exact lowerBV_impossible (proper_of hp) hpt hpr
      (fun a ha => essentialCheck6_sound (List.all_eq_true.mp hess a ha)) himp

-- ============================================================
-- 6. Certificate Data, Verification, Monotone Witness & Main
-- ============================================================

noncomputable section CertData
def tF1 : Sig := 0xe8e8e8e8e8e8e8e8#64
def F1P : List Row := mkRows [3,3,3,5,5,5,6,6,6]
def F1N : List Row := mkRows [1,2,4,1,2,4,1,2,4]
def F1R : List (Nat × Nat) := [(63,73),(455,146),(504,292)]
def F1A : List (List Nat) := [[0,1,2,3,4,5],[0,2,1,3,4,5],[1,0,2,3,4,5],[1,2,0,3,4,5],[2,0,1,3,4,5],[2,1,0,3,4,5]]
def F1C : List CutSpec := []
def F1T3 : BTree NodeData := lf 0x70 []
def F1L : Nat → Option (BTree NodeData) | 3 => some F1T3 | _ => none
def F1M : Nat → BST | _ => BE
def tF2 : Sig := 0xeac8eac8eac8eac8#64
def F2P : List Row := mkRows [3,3,3,6,6,6,9,9,9]
def F2N : List Row := mkRows [5,10,12,5,10,12,5,10,12]
def F2R : List (Nat × Nat) := [(455,73),(63,146),(56,365),(448,438)]
def F2A : List (List Nat) := [[0,1,2,3,4,5],[1,0,3,2,4,5]]
def F2C : List CutSpec := [⟨0,10,1,0,0,[0,1,2,3,4,5],0xcc00cc00cc00cc00#64⟩,⟨0,5,1,0,0,[0,1,2,3,4,5],0xa0a0a0a0a0a0a0a0#64⟩,⟨0,4,2,0,0,[0,1,2,3,4,5],0xf0f0f0f0f0f0f0f0#64⟩,⟨4,0,2,0,0,[0,1,2,3,4,5],0xf0f0f0f0f0f0f0f#64⟩,⟨0,8,2,0,0,[0,1,2,3,4,5],0xff00ff00ff00ff00#64⟩,⟨8,0,2,0,0,[0,1,2,3,4,5],0xff00ff00ff00ff#64⟩]
def F2T3 : BTree NodeData := lf 0xf0 [0x300020001,0x600050004]
def F2L : Nat → Option (BTree NodeData) | 3 => some F2T3 | _ => none
def F2M : Nat → BST | _ => BE
def tF3 : Sig := 0xeae8eae8eae8eae8#64
def F3P : List Row := mkRows [3,3,3,5,5,5,6,6,6,9,9,9]
def F3N : List Row := mkRows [1,10,12,1,10,12,1,10,12,1,10,12]
def F3R : List (Nat × Nat) := [(3647,585),(455,1170),(504,2340),(3584,3510)]
def F3A : List (List Nat) := [[0,1,2,3,4,5],[0,2,1,3,4,5]]
def F3C : List CutSpec := [⟨8,0,4,1,0,[0,1,2,3,4,5],0xff00ff00ff00ff#64⟩]
def F3T4 : BTree NodeData := lf 0xf0 [0x1]
def F3L : Nat → Option (BTree NodeData) | 4 => some F3T4 | _ => none
def F3M : Nat → BST | _ => BE
def tF4 : Sig := 0xfeeafeeafeeafeea#64
def F4P : List Row := mkRows [1,1,1,6,6,6,10,10,10,12,12,12]
def F4N : List Row := mkRows [2,4,8,2,4,8,2,4,8,2,4,8]
def F4R : List (Nat × Nat) := [(7,0),(504,585),(3640,1170),(4032,2340)]
def F4A : List (List Nat) := [[0,1,2,3,4,5],[0,1,3,2,4,5],[0,2,1,3,4,5],[0,2,3,1,4,5],[0,3,1,2,4,5],[0,3,2,1,4,5]]
def F4C : List CutSpec := [⟨1,0,4,1,0,[3,0,1,2,4,5],0x5555555555555555#64⟩]
def F4T4 : BTree NodeData := lf 0xf0 [0x1]
def F4L : Nat → Option (BTree NodeData) | 4 => some F4T4 | _ => none
def F4M : Nat → BST | _ => BE
def tF5 : Sig := 0xeeeaece0eeeaece0#64
def F5P : List Row := mkRows [5,5,5,5,6,6,6,6,10,10,10,10,17,17,17,17]
def F5N : List Row := mkRows [3,9,18,28,3,9,18,28,3,9,18,28,3,9,18,28]
def F5R : List (Nat × Nat) := [(61455,13107),(4080,21845),(255,34952),(3840,43690),(61440,52428)]
def F5A : List (List Nat) := [[0,1,2,3,4,5],[1,0,2,4,3,5]]
def F5C : List CutSpec := [⟨8,0,4,2,0,[0,2,1,4,3,5],0xff00ff00ff00ff#64⟩]
def F5T4 : BTree NodeData := lf 0x1f0 [0x1]
def F5L : Nat → Option (BTree NodeData) | 4 => some F5T4 | _ => none
def F5M : Nat → BST | _ => BE
def tF6 : Sig := 0xeeeaece8eeeaece8#64
def F6P : List Row := mkRows [3,3,3,5,5,5,6,6,6,10,10,10,17,17,17]
def F6N : List Row := mkRows [9,18,28,9,18,28,9,18,28,9,18,28,9,18,28]
def F6R : List (Nat × Nat) := [(28735,4681),(4039,9362),(504,18724),(3584,23405),(28672,28086)]
def F6A : List (List Nat) := [[0,1,2,3,4,5],[1,0,2,4,3,5]]
def F6C : List CutSpec := [⟨16,0,5,3,0,[1,0,2,3,4,5],0xffff0000ffff#64⟩]
def F6T5 : BTree NodeData := lf 0x1f0 [0x1]
def F6L : Nat → Option (BTree NodeData) | 5 => some F6T5 | _ => none
def F6M : Nat → BST | _ => BE
def tF7 : Sig := 0xfffefeeefffefeee#64
def F7P : List Row := mkRows [1,1,1,2,2,2,12,12,12,20,20,20,24,24,24]
def F7N : List Row := mkRows [4,8,16,4,8,16,4,8,16,4,8,16,4,8,16]
def F7R : List (Nat × Nat) := [(7,0),(56,0),(4032,4681),(29120,9362),(32256,18724)]
def F7A : List (List Nat) := [[0,1,2,3,4,5],[0,1,2,4,3,5],[0,1,3,2,4,5],[0,1,3,4,2,5],[0,1,4,2,3,5],[0,1,4,3,2,5],[1,0,2,3,4,5],[1,0,2,4,3,5],[1,0,3,2,4,5],[1,0,3,4,2,5],[1,0,4,2,3,5],[1,0,4,3,2,5]]
def F7C : List CutSpec := [⟨1,0,5,4,0,[4,0,1,2,3,5],0x5555555555555555#64⟩]
def F7T5 : BTree NodeData := lf 0x1f0 [0x1]
def F7L : Nat → Option (BTree NodeData) | 5 => some F7T5 | _ => none
def F7M : Nat → BST | _ => BE
def tF8 : Sig := 0xfeeafcc8feeafcc8#64
def F8P : List Row := mkRows [3,3,3,3,3,6,6,6,6,6,10,10,10,10,10,12,12,12,12,12,17,17,17,17,17]
def F8N : List Row := mkRows [5,9,18,20,24,5,9,18,20,24,5,9,18,20,24,5,9,18,20,24,5,9,18,20,24]
def F8R : List (Nat × Nat) := [(32505887,3247203),(32767,4329604),(1016800,9741609),(1047552,19483218),(32505856,30307228)]
def F8A : List (List Nat) := [[0,1,2,3,4,5],[0,1,3,2,4,5]]
def F8C : List CutSpec := [⟨0,5,2,0,0,[0,1,2,3,4,5],0xa0a0a0a0a0a0a0a0#64⟩,⟨0,16,5,4,0,[0,1,2,3,4,5],0xffff0000ffff0000#64⟩,⟨1,0,4,1,16,[3,0,1,2,4,5],0x5555555555555555#64⟩,⟨0,2,2,0,0,[0,1,2,3,4,5],0xcccccccccccccccc#64⟩,⟨2,0,3,0,0,[0,1,2,3,4,5],0x3333333333333333#64⟩,⟨0,4,3,0,0,[0,1,2,3,4,5],0xf0f0f0f0f0f0f0f0#64⟩,⟨17,2,1,0,0,[0,1,2,3,4,5],0x444400004444#64⟩,⟨0,9,2,0,0,[0,1,2,3,4,5],0xaa00aa00aa00aa00#64⟩,⟨0,1,3,0,0,[0,1,2,3,4,5],0xaaaaaaaaaaaaaaaa#64⟩,⟨4,0,4,2,0,[0,1,4,2,3,5],0xf0f0f0f0f0f0f0f#64⟩,⟨16,0,5,3,0,[3,0,1,2,4,5],0xffff0000ffff#64⟩,⟨8,0,4,2,0,[0,1,2,4,3,5],0xff00ff00ff00ff#64⟩,⟨1,16,4,1,0,[3,0,1,2,4,5],0x5555000055550000#64⟩,⟨0,8,3,0,0,[0,1,2,3,4,5],0xff00ff00ff00ff00#64⟩,⟨2,4,2,0,0,[0,1,2,3,4,5],0x3030303030303030#64⟩,⟨2,8,2,0,0,[0,1,2,3,4,5],0x3300330033003300#64⟩,⟨0,18,2,0,0,[0,1,2,3,4,5],0xcccc0000cccc0000#64⟩,⟨17,4,1,0,0,[0,1,2,3,4,5],0x505000005050#64⟩,⟨12,0,2,0,0,[0,1,2,3,4,5],0xf000f000f000f#64⟩,⟨8,18,1,0,0,[0,1,2,3,4,5],0xcc000000cc0000#64⟩,⟨4,18,1,0,0,[0,1,2,3,4,5],0xc0c00000c0c0000#64⟩,⟨6,8,1,0,0,[0,1,2,3,4,5],0x300030003000300#64⟩]
def F8T4 : BTree NodeData := nd (nd (nd (nd (nd (lf 0x4c91000722 [0x20303020001,0x50004]) (lf 0xd4910005a2 [0x603020004])) (nd (lf 0x54b1000782 [0x80007]) (lf 0x94b1000782 [0x302010a0009,0x30b]))) (nd (nd (lf 0xc871000782 [0x302010a0005,0x30b]) (lf 0x54b10005a2 [0x600080005,0x30b])) (nd (lf 0xd4520005c2 [0x40302020a,0x30b]) (nd (lf 0xd4d2000562 [0x4030b0302,0x20a0006]) (lf 0x5472000582 [0x80004030b,0x30c]))))) (nd (nd (nd (lf 0x54021005a2 [0x30200050008,0x3]) (lf 0x9442100592 [0xe0006030d])) (nd (lf 0x54c2100532 [0xe0005030d]) (nd (lf 0xd4121005c2 [0x20a00090006,0x302030b]) (lf 0xd4d2100552 [0x303020a0006,0x302])))) (nd (nd (lf 0xd4121005a2 [0x403020008,0xa]) (lf 0x8c52100712 [0xf030d])) (nd (lf 0xd4d2100532 [0x4000e030d,0xc]) (nd (lf 0xd4d2100572 [0x30d020a0006,0x30b0009]) (lf 0x5422100782 [0x303020001])))))) (nd (nd (nd (nd (lf 0x54e2100712 [0x10030d]) (lf 0x94e2100712 [0x10c0006030d])) (nd (lf 0xd4e2100512 [0x6030d]) (nd (lf 0x54221005a2 [0x30200090005,0x3]) (lf 0xcc62100712 [0x10c0005030d])))) (nd (nd (lf 0x54e2100532 [0xe0005030d]) (lf 0x54f2100512 [0x30d])) (nd (lf 0x54f2100532 [0x11000e030d,0x9]) (nd (lf 0x5443200512 [0x4030d]) (lf 0x9443200512 [0x5030d]))))) (nd (nd (nd (lf 0xd413200522 [0x1103020009]) (lf 0xd413200722 [0x130012])) (nd (lf 0x1453200712 [0x30b0013030d,0x11]) (nd (lf 0xd453200512 [0x30d]) (lf 0xd453200712 [0x13030d])))) (nd (nd (lf 0xd4132005a2 [0x11020c000e,0x9]) (lf 0xd453200592 [0x20c000e030d])) (nd (lf 0x9463200512 [0x5030d]) (nd (lf 0x9463200592 [0x20c0005030d]) (lf 0x54e3200532 [0x30b0001030d,0x500090011]))))))
def F8T5 : BTree NodeData := nd (nd (nd (nd (lf 0x110003e1 [0x10b00150014,0x30102]) (lf 0x310003c1 [0x1020001010b,0x10c0008])) (nd (lf 0x310003e1 [0x10b01020005,0x1010c010a,0x6000a0008,0xe000c]) (nd (lf 0x120003e1 [0x80102000f,0x3010b000a,0xe000c]) (lf 0x320003a1 [0x10b000a0015,0x11010c0008])))) (nd (nd (lf 0x21003b1 [0x5010d0010,0xc010b]) (lf 0x121003d1 [0xa010d0001,0xe000c010b])) (nd (lf 0x121003b1 [0x11010d0014,0xc000a010b]) (nd (lf 0x121003f1 [0x110016000f,0x10b000a0001,0xc0005]) (lf 0x22100391 [0xe0006010d,0x10b0010]))))) (nd (nd (nd (lf 0x221003d1 [0xa010d0001,0xe000c010b]) (lf 0x221003b1 [0x5010d0010,0xc010b])) (nd (lf 0x221003f1 [0x100050015,0xa010b010d,0x11]) (nd (lf 0x32100391 [0xe000a010d]) (lf 0x321003b1 [0x10b010d0014,0xc0011])))) (nd (nd (lf 0x3200331 [0x14000c010d,0xb00050011]) (nd (lf 0x13200331 [0x10b000f010d,0x1100060005]) (lf 0x132003b1 [0xc010d0008,0xa010b0010]))) (nd (lf 0x132003f1 [0xe00060013,0xa0001010d,0x10b0102000c]) (nd (lf 0x23200331 [0x15000a010d,0x50011]) (lf 0x232003b1 [0x10010d0008,0x10b000c])))))
def F8M5 : BST := BN 237610936 7297 (BN 172370448 2817 (BN 141048450 3456 (BN 110122518 7936 (BN 109997141 7680 (BL 97349541 2304) BE) (BN 134272777 2688 (BL 119333035 7296) BE)) (BN 160658070 7424 (BN 146474216 128 (BL 145484448 2944) BE) (BN 168846900 1536 (BL 167941731 1408) BE))) (BN 205551365 3200 (BN 188461828 7808 (BN 182089977 3968 (BL 177653979 1920) BE) (BN 205537505 1792 (BL 205168893 1152) BE)) (BN 216468640 3712 (BN 209070291 2176 (BL 208188384 7552) BE) (BN 237315955 1664 (BL 221251241 1280) BE)))) (BN 263701248 3840 (BN 250582461 896 (BN 241903063 640 (BN 240985809 3328 (BL 237665971 1024) BE) (BN 246146463 384 (BL 242339812 2560) BE)) (BN 260345045 2816 (BN 259809440 513 (BL 255482324 8064) BE) (BN 262247119 512 (BL 260906478 0) BE))) (BN 322996020 1025 (BN 289288965 256 (BN 285865244 768 (BL 268629473 2048) BE) (BN 313286397 2432 (BL 297104469 3072) BE)) (BN 360310223 3073 (BN 339470263 2049 (BL 327669861 2561) BE) (BL 370861851 3584))))
def F8T6 : BTree NodeData := lf 0x1f0 [0xc000a000d,0x2000b]
def F8M6 : BST := BN 262456984 1921 (BN 226895309 384 (BN 189551867 1920 (BN 169882447 1665 (BN 155513284 128 (BL 97349541 3840) BE) (BL 172320126 1664)) (BN 213189763 3841 (BN 200392719 1152 (BL 193987865 3968) BE) (BL 217625761 129))) (BN 255482324 1408 (BN 248743686 257 (BN 237825946 1024 (BL 227355858 1281) BE) (BL 253217978 1280)) (BN 258556462 640 (BL 256366285 0) (BL 259918322 3456)))) (BN 320620727 3969 (BN 298097413 768 (BN 283418012 256 (BN 275363304 3712 (BL 272925625 3713) BE) (BL 294812097 3584)) (BN 316232941 1153 (BL 313646067 3457) (BL 318082065 896))) (BN 340869124 512 (BN 330277937 1537 (BN 325963038 769 (BL 320668939 641) BE) (BL 330399036 1793)) (BN 349569355 3585 (BL 346812808 1536) (BL 356261156 1792))))
def F8L : Nat → Option (BTree NodeData) | 4 => some F8T4 | 5 => some F8T5 | 6 => some F8T6 | _ => none
def F8M : Nat → BST | 5 => F8M5 | 6 => F8M6 | _ => BE
def tF9 : Sig := 0xfeeefac0feeefac0#64
def F9P : List Row := mkRows [6,6,6,6,6,9,9,9,9,9,12,12,12,12,12,17,17,17,17,17,18,18,18,18,18]
def F9N : List Row := mkRows [3,5,10,20,24,3,5,10,20,24,3,5,10,20,24,3,5,10,20,24,3,5,10,20,24]
def F9R : List (Nat × Nat) := [(1016800,3247203),(32505887,5412005),(31775,10824010),(32736,21648020),(33521664,25977624)]
def F9A : List (List Nat) := [[0,1,2,3,4,5],[0,2,1,4,3,5],[1,0,3,2,4,5],[1,3,0,4,2,5],[2,0,4,1,3,5],[2,4,0,3,1,5],[3,1,4,0,2,5],[3,4,1,2,0,5],[4,2,3,0,1,5],[4,3,2,1,0,5]]
def F9C : List CutSpec := [⟨1,8,2,0,0,[0,1,2,3,4,5],0x5500550055005500#64⟩,⟨4,2,2,0,0,[0,1,2,3,4,5],0xc0c0c0c0c0c0c0c#64⟩,⟨0,20,2,0,0,[0,1,2,3,4,5],0xf0f00000f0f00000#64⟩,⟨2,0,4,2,0,[0,4,2,1,3,5],0x3333333333333333#64⟩,⟨0,8,3,0,0,[0,1,2,3,4,5],0xff00ff00ff00ff00#64⟩,⟨0,24,2,0,0,[0,1,2,3,4,5],0xff000000ff000000#64⟩,⟨0,16,3,0,0,[0,1,2,3,4,5],0xffff0000ffff0000#64⟩,⟨0,4,3,0,0,[0,1,2,3,4,5],0xf0f0f0f0f0f0f0f0#64⟩,⟨1,0,4,2,0,[4,0,1,2,3,5],0x5555555555555555#64⟩,⟨0,1,3,0,0,[0,1,2,3,4,5],0xaaaaaaaaaaaaaaaa#64⟩,⟨0,2,3,0,0,[0,1,2,3,4,5],0xcccccccccccccccc#64⟩,⟨16,0,4,2,0,[2,3,0,1,4,5],0xffff0000ffff#64⟩,⟨8,0,4,2,0,[2,0,3,4,1,5],0xff00ff00ff00ff#64⟩,⟨0,10,2,0,0,[0,1,2,3,4,5],0xcc00cc00cc00cc00#64⟩,⟨2,16,2,0,0,[0,1,2,3,4,5],0x3333000033330000#64⟩,⟨0,5,2,0,0,[0,1,2,3,4,5],0xa0a0a0a0a0a0a0a0#64⟩,⟨3,16,1,0,0,[0,1,2,3,4,5],0x1111000011110000#64⟩,⟨17,4,1,0,0,[0,1,2,3,4,5],0x505000005050#64⟩,⟨1,16,2,0,0,[0,1,2,3,4,5],0x5555000055550000#64⟩,⟨4,0,4,2,0,[0,2,4,3,1,5],0xf0f0f0f0f0f0f0f#64⟩,⟨2,24,1,0,0,[0,1,2,3,4,5],0x3300000033000000#64⟩,⟨8,4,2,0,0,[0,1,2,3,4,5],0xf000f000f000f0#64⟩,⟨16,10,1,0,0,[0,1,2,3,4,5],0xcc000000cc00#64⟩,⟨9,0,2,0,0,[0,1,2,3,4,5],0x55005500550055#64⟩]
def F9T3 : BTree NodeData := nd (lf 0x165d0e1000843 [0x1]) (lf 0x1658863000903 [0x2])
def F9T4 : BTree NodeData := nd (nd (nd (lf 0xd4910005a2 [0x502040003]) (lf 0xd4d1000562 [0x2040006])) (nd (lf 0xd5110004e2 [0x802040007]) (lf 0xd5110004f2 [0xb000a0209,0x50008]))) (nd (nd (lf 0xd0e1000642 [0x10c0209]) (lf 0xd4530005c2 [0x7020d000b])) (nd (lf 0xd4930005a2 [0x8000e]) (nd (lf 0xd5130004e2 [0xe0003]) (lf 0x8863000702 [0x1040209]))))
def F9M4 : BST := BN 152078959 128 (BL 110051527 0) BE
def F9T5 : BTree NodeData := nd (nd (nd (lf 0x110003e1 [0xf0002000e,0x9010c0004]) (lf 0x110003f1 [0xe00110010,0x200040009,0xc])) (nd (lf 0x210003c1 [0x100090012,0x7010d]) (lf 0x210003e1 [0x4000e0002,0x140013010c,0xc0007000d]))) (nd (nd (lf 0x130003e1 [0xd00160015,0x900140017]) (lf 0x130003f1 [0xe000a0018,0x900100006,0xd])) (nd (lf 0x23000361 [0x10400090012,0xb01140006]) (lf 0x230003e1 [0x16000d0015,0x1700040014,0xc])))
def F9M5 : BST := BN 248616042 128 (BN 216394127 640 (BN 181986157 896 (BL 141031987 1920) BE) (BL 232339042 384)) (BN 280665185 768 (BN 272222841 256 (BL 268629473 0) BE) (BL 339470263 512))
def F9T6 : BTree NodeData := lf 0x1f0 [0x1400090004,0xc000d]
def F9M6 : BST := BN 267059252 263 (BN 232206150 131 (BN 175736391 261 (BN 161765451 2 (BN 138780689 387 (BN 135306696 393 (BL 97349541 386) BE) (BL 155513284 898)) (BN 170455484 385 (BL 169882447 262) (BL 172320126 388))) (BN 213421190 256 (BN 193987865 901 (BN 189551867 389 (BL 183144852 136) BE) (BL 213189763 259)) (BN 217625761 771 (BL 215637557 899) (BL 227355858 3)))) (BN 255619936 8 (BN 248357223 264 (BN 246268290 770 (BN 238349874 905 (BL 237825946 258) BE) (BL 247312352 897)) (BN 252593259 773 (BL 251559376 129) (BL 253217978 130))) (BN 262317801 9 (BN 259918322 133 (BN 258392460 137 (BL 256366285 0) BE) (BL 260001720 641)) (BN 264643374 257 (BL 262456984 391) (BL 264808629 512))))) (BN 320620727 903 (BN 294812097 260 (BN 286136983 265 (BN 275363304 900 (BN 274313061 5 (BL 272925625 774) BE) (BL 281538764 392)) (BN 290572981 777 (BL 289981108 904) (BL 294624577 384))) (BN 306520966 776 (BN 299060575 896 (BN 298097413 132 (BL 297091409 4) BE) (BL 303254441 772)) (BN 316464368 768 (BL 313646067 135) (BL 318082065 645)))) (BN 338720281 640 (BN 332476804 517 (BN 330277937 128 (BN 325963038 6 (BL 322807117 769) BE) (BL 330399036 515)) (BN 334738671 7 (BL 334284283 134) (BL 335249328 643))) (BN 349569355 390 (BN 343916120 775 (BL 339174669 519) (BL 346812808 1)) (BN 356261156 642 (BL 355255152 513) (BL 358011699 902)))))
def F9L : Nat → Option (BTree NodeData) | 3 => some F9T3 | 4 => some F9T4 | 5 => some F9T5 | 6 => some F9T6 | _ => none
def F9M : Nat → BST | 4 => F9M4 | 5 => F9M5 | 6 => F9M6 | _ => BE
def tRt : Sig := 0xfffefffaeeeeeca0#64
def RtP : List Row := mkRows [5,5,5,5,5,5,10,10,10,10,10,10,17,17,17,17,17,17,18,18,18,18,18,18,33,33,33,33,33,33,36,36,36,36,36,36,40,40,40,40,40,40]
def RtN : List Row := mkRows [3,6,9,28,34,48,3,6,9,28,34,48,3,6,9,28,34,48,3,6,9,28,34,48,3,6,9,28,34,48,3,6,9,28,34,48,3,6,9,28,34,48]
def RtR : List (Nat × Nat) := [(1057222719,349051310405),(16519104,1326394979539),(67645734975,698102620810),(4329327038400,837723144972),(16773120,2792410483240),(4398029733888,3350892579888)]
def RtA : List (List Nat) := [[0,1,2,3,4,5],[5,1,2,4,3,0]]
def RtC : List CutSpec := [⟨0,2,6,7,0,[2,5,3,0,1,4],0xcccccccccccccccc#64⟩,⟨20,0,4,2,0,[2,3,4,0,5,1],0xf0f00000f0f#64⟩,⟨8,20,2,0,0,[0,1,2,3,4,5],0xf0000000f00000#64⟩,⟨2,0,6,6,0,[0,5,2,3,4,1],0x3333333333333333#64⟩,⟨16,0,7,8,0,[2,4,3,0,5,1],0xffff0000ffff#64⟩,⟨36,0,4,2,0,[2,0,4,3,1,5],0xf0f0f0f#64⟩,⟨0,48,3,0,0,[0,1,2,3,4,5],0xffff000000000000#64⟩,⟨8,0,7,8,0,[1,4,2,5,0,3],0xff00ff00ff00ff#64⟩,⟨0,1,4,0,0,[0,1,2,3,4,5],0xaaaaaaaaaaaaaaaa#64⟩,⟨0,9,3,0,0,[0,1,2,3,4,5],0xaa00aa00aa00aa00#64⟩,⟨1,0,5,5,0,[5,0,3,2,4,1],0x5555555555555555#64⟩,⟨48,0,3,0,0,[0,1,2,3,4,5],0xffff#64⟩,⟨16,1,3,0,0,[0,1,2,3,4,5],0xaaaa0000aaaa#64⟩,⟨4,0,7,9,0,[0,1,5,2,4,3],0xf0f0f0f0f0f0f0f#64⟩,⟨0,4,4,0,0,[0,1,2,3,4,5],0xf0f0f0f0f0f0f0f0#64⟩,⟨37,0,2,0,0,[0,1,2,3,4,5],0x5050505#64⟩,⟨10,1,2,0,0,[0,1,2,3,4,5],0x22002200220022#64⟩,⟨34,8,2,0,0,[0,1,2,3,4,5],0x33003300#64⟩,⟨5,0,4,2,0,[4,0,5,1,3,2],0x505050505050505#64⟩,⟨0,8,4,0,0,[0,1,2,3,4,5],0xff00ff00ff00ff00#64⟩,⟨0,20,2,0,0,[0,1,2,3,4,5],0xf0f00000f0f00000#64⟩,⟨0,16,4,0,0,[0,1,2,3,4,5],0xffff0000ffff0000#64⟩,⟨4,32,3,0,0,[0,1,2,3,4,5],0xf0f0f0f00000000#64⟩,⟨1,32,3,0,0,[0,1,2,3,4,5],0x5555555500000000#64⟩,⟨1,4,3,0,0,[0,1,2,3,4,5],0x5050505050505050#64⟩,⟨0,32,4,0,0,[0,1,2,3,4,5],0xffffffff00000000#64⟩,⟨4,24,2,0,0,[0,1,2,3,4,5],0xf0000000f000000#64⟩,⟨32,1,3,0,0,[0,1,2,3,4,5],0xaaaaaaaa#64⟩,⟨8,2,5,4,0,[1,4,2,5,0,3],0xcc00cc00cc00cc#64⟩,⟨32,4,3,0,0,[0,1,2,3,4,5],0xf0f0f0f0#64⟩,⟨16,2,5,4,0,[1,4,2,0,5,3],0xcccc0000cccc#64⟩,⟨32,0,5,5,0,[0,1,4,3,2,5],0xffffffff#64⟩,⟨32,2,3,0,0,[0,1,2,3,4,5],0xcccccccc#64⟩,⟨16,12,2,0,0,[0,1,2,3,4,5],0xf0000000f000#64⟩,⟨4,1,3,0,0,[0,1,2,3,4,5],0xa0a0a0a0a0a0a0a#64⟩,⟨8,48,2,0,0,[0,1,2,3,4,5],0xff000000000000#64⟩,⟨18,32,2,0,0,[0,1,2,3,4,5],0x333300000000#64⟩,⟨0,28,2,0,0,[0,1,2,3,4,5],0xf0000000f0000000#64⟩,⟨1,48,2,0,0,[0,1,2,3,4,5],0x5555000000000000#64⟩,⟨18,0,5,3,0,[1,4,2,3,5,0],0x333300003333#64⟩,⟨17,0,4,2,0,[4,2,3,1,5,0],0x555500005555#64⟩,⟨1,6,2,0,0,[0,1,2,3,4,5],0x4040404040404040#64⟩,⟨2,9,2,0,0,[0,1,2,3,4,5],0x2200220022002200#64⟩,⟨5,32,2,0,0,[0,1,2,3,4,5],0x505050500000000#64⟩,⟨10,0,5,3,0,[0,4,1,5,3,2],0x33003300330033#64⟩,⟨40,0,4,2,0,[0,2,3,4,1,5],0xff00ff#64⟩,⟨32,8,3,0,0,[0,1,2,3,4,5],0xff00ff00#64⟩,⟨8,4,3,0,0,[0,1,2,3,4,5],0xf000f000f000f0#64⟩,⟨0,34,3,0,0,[0,1,2,3,4,5],0xcccccccc00000000#64⟩,⟨8,3,2,0,0,[0,1,2,3,4,5],0x88008800880088#64⟩,⟨36,1,2,0,0,[0,1,2,3,4,5],0xa0a0a0a#64⟩,⟨12,0,4,2,0,[0,2,4,5,1,3],0xf000f000f000f#64⟩,⟨9,0,3,0,0,[0,1,2,3,4,5],0x55005500550055#64⟩,⟨2,8,3,0,0,[0,1,2,3,4,5],0x3300330033003300#64⟩,⟨16,34,2,0,0,[0,1,2,3,4,5],0xcccc00000000#64⟩,⟨1,16,3,0,0,[0,1,2,3,4,5],0x5555000055550000#64⟩,⟨8,32,3,0,0,[0,1,2,3,4,5],0xff00ff00000000#64⟩,⟨48,1,2,0,0,[0,1,2,3,4,5],0xaaaa#64⟩,⟨4,2,3,0,0,[0,1,2,3,4,5],0xc0c0c0c0c0c0c0c#64⟩,⟨0,6,3,0,0,[0,1,2,3,4,5],0xc0c0c0c0c0c0c0c0#64⟩,⟨33,4,2,0,0,[0,1,2,3,4,5],0x50505050#64⟩,⟨2,16,3,0,0,[0,1,2,3,4,5],0x3333000033330000#64⟩,⟨24,2,4,1,0,[0,3,1,4,5,2],0xcc000000cc#64⟩,⟨8,16,3,0,0,[0,1,2,3,4,5],0xff000000ff0000#64⟩,⟨33,0,2,0,0,[0,1,2,3,4,5],0x55555555#64⟩]
def RtT4 : BTree NodeData := nd (nd (nd (lf 0xe1d54d4a1002484 [0x301020e01]) (nd (lf 0x5cd521431003504 [0x1060f050e04,0x807]) (lf 0x60c7054b1002d04 [0x7080f050e04,0x2090807]))) (nd (nd (lf 0xe0d65d852002904 [0xa0d010f05]) (lf 0x61f54d8d2002024 [0xf010f04])) (nd (lf 0xddb715422003184 [0x10f050406]) (lf 0x5da31d422003304 [0xb04040b])))) (nd (nd (lf 0x219545413002864 [0xf0e000d000c,0x20f02010d04,0x10]) (nd (lf 0x61b548863002804 [0xd04]) (lf 0x61e76d523002064 [0xf0e0011]))) (nd (nd (lf 0x61f65d523002064 [0xf0e0012]) (lf 0xe0d6558a4002824 [0xf0403140813,0xf01])) (nd (lf 0xe116558650028c4 [0xd010f080f0e,0x316020d0015]) (lf 0x5ca31d425003504 [0xf050c0b0b04,0x6040f]))))
def RtT5_0 := nd (nd (nd (nd (nd (lf 0x165d481001993 [0x70807050017,0x20b]) (lf 0x176d481001393 [0x1807080705,0x19])) (nd (lf 0x3725941001393 [0x1a07080705,0xf040b]) (lf 0x3539011001c43 [0x40b070e000a]))) (nd (nd (lf 0x36590110018c3 [0x70e040b0708,0x1c001b]) (lf 0x3635491001913 [0x60b021d0705,0x60209])) (nd (lf 0x3635491001b13 [0x60b0705021d,0x6050e0209]) (lf 0x153d891001b13 [0x1e000a0705])))) (nd (nd (nd (lf 0x172d4d1001513 [0x60b06010705,0x606040609]) (lf 0x364d4d1001853 [0x205070e000a,0x21f])) (nd (lf 0x7655110012d3 [0x1c0708000c,0x70e]) (lf 0x173d951001153 [0x705001b]))) (nd (nd (lf 0x154d4a1001c83 [0x1200018]) (lf 0x174d4a1001683 [0x50e07080601,0x705])) (nd (lf 0x1644821001a83 [0x21f00130708,0x21a0520]) (nd (lf 0x1654821001983 [0x1007050708,0x21a000a0013,0x21]) (lf 0x1654821001b83 [0x708001c021a,0xa00210705])))))) (nd (nd (nd (nd (lf 0x1625421001983 [0x2207050011]) (lf 0x3725421001d83 [0x70500230011])) (nd (lf 0x3735421001543 [0x220010]) (lf 0x37654210019c3 [0x70500100011]))) (nd (nd (lf 0x1625421001b83 [0x70507080010,0x130018]) (lf 0x3725421001783 [0x70807050018,0x220019])) (nd (lf 0x1635421001b43 [0xa07050010,0x180022]) (nd (lf 0x164d4210018c3 [0x70e021f0708,0x180520]) (lf 0x176d4210019c3 [0x705070e0021,0x180708]))))) (nd (nd (nd (lf 0x164d421001ac3 [0x708021f0520,0x1a070e]) (lf 0x165d4210019c3 [0x705070e0021,0x1a0708])) (nd (lf 0x170d4a1001783 [0x70800090018,0x705]) (lf 0x164d4a1001a93 [0x21f07080520,0x16001a020b]))) (nd (nd (lf 0x165d4a1001993 [0x21001c0017,0x20b]) (lf 0x176d4a1001393 [0x70800180021,0x160705])) (nd (lf 0x3725961001993 [0x40b00210017]) (nd (lf 0x3735961001153 [0x70e000a]) (lf 0x37354b1001d03 [0x70807050604,0x7]))))))
def RtT5_1 := nd (nd (nd (nd (nd (lf 0x16454b1001883 [0x7]) (lf 0x35354b1001d03 [0x60407050106,0x7])) (nd (lf 0x172d4f1001703 [0x50806040705,0x24070e]) (lf 0x164d4f1001a43 [0x70e0024]))) (nd (nd (lf 0x1524c31001d03 [0x2507050409,0x1060026]) (lf 0x3724c31001703 [0x10f0705001c,0x25])) (nd (lf 0x1644c31001a43 [0x401001c0026]) (lf 0x3744c31001643 [0x408070e001c])))) (nd (nd (nd (lf 0x3754c31001543 [0x70e0025]) (lf 0x1528c31001d03 [0x6040027])) (nd (lf 0x1648c31001a43 [0x70e0027]) (lf 0x3539031001c43 [0x40b070e000a]))) (nd (nd (lf 0x1521431001d83 [0x60407050106,0x70708]) (lf 0x1721431001783 [0x60407050106,0x10e00030708])) (nd (lf 0x1731431001743 [0x70e01200705,0x1b01140604]) (nd (lf 0x1641431001ac3 [0x7070e0520,0x1b00030708,0x228]) (lf 0x3725431001783 [0x11a0705000a,0x6040708010f,0xb])))))) (nd (nd (nd (nd (lf 0x3735431001743 [0x7070e0025,0x114]) (lf 0x37454310016c3 [0x708070e0025,0x420])) (nd (lf 0x152d431001d83 [0x60407050018,0x701200708]) (lf 0x172d431001783 [0x70806040027,0x10e0120]))) (nd (nd (lf 0x173d431001743 [0x604070e0027]) (lf 0x154d431001cc3 [0x1a070e040a,0x2901200708])) (nd (lf 0x164d431001ac3 [0x70e05200027,0x1a0007]) (nd (lf 0x174d4310016c3 [0x708070e000a,0x1200016]) (lf 0x165d4310019c3 [0x907050708,0x70e001a]))))) (nd (nd (nd (lf 0x7054b1001d83 [0x60407050106,0x70708]) (lf 0x37054b1001d83 [0x70500190209,0x70106])) (nd (lf 0x16454b1001893 [0x7080026]) (lf 0x37654b1001193 [0x607050708,0x1c]))) (nd (nd (lf 0x172d4f1001513 [0x705002a]) (lf 0x164d4f1001853 [0x205070e000a,0x2a0228])) (nd (lf 0x37655310012d3 [0x70e0708000c,0x5001c]) (nd (lf 0x659052001e83 [0x7080320002b,0x11f002c]) (lf 0x2659052001883 [0x1f02200504]))))))
def RtT5_2 := nd (nd (nd (nd (nd (lf 0x3659052001e83 [0x206011a0003,0x13]) (lf 0x1759052001683 [0x120708002c])) (nd (lf 0x1731852001703 [0x12d00130705,0x41c002c]) (lf 0x1751852001783 [0x70507080010,0x11a]))) (nd (nd (lf 0x174d852001683 [0x11f00130003]) (lf 0x165d852001983 [0x907080705,0x501])) (nd (lf 0x265d852001983 [0x50107050003]) (lf 0x175d852001583 [0x70500100708,0x11a000a0013,0x21])))) (nd (nd (nd (lf 0x175d852001783 [0x708001c011a,0xa07050013,0x21]) (lf 0x35454d2001c23 [0x7010704012e,0x413001a])) (nd (lf 0x354d8d2001823 [0x2f]) (lf 0x174d8d2001a23 [0x70407010030,0x320]))) (nd (nd (lf 0x175d8d2001923 [0x7010705002f]) (lf 0x275d8d2001923 [0x70107050030])) (nd (lf 0x354d8d2001c23 [0x300413001c,0x701]) (nd (lf 0x164d8d2001a23 [0x70400130009,0x3200701]) (lf 0x165d8d2001b23 [0x70107050010,0x9])))))) (nd (nd (nd (nd (lf 0x265d8d2001923 [0x1300090705,0x701]) (lf 0x175d8d2001523 [0x70107050030])) (nd (lf 0x175d8d2001723 [0x705011a001c,0x10100130701,0x30]) (lf 0x37655120012a3 [0x1c0011]))) (nd (nd (lf 0x171d512001c83 [0x30101200708,0x104]) (lf 0x271d512001c83 [0x3040026])) (nd (lf 0x173d512001c23 [0x7040701012e,0x213002f]) (nd (lf 0x176d5120018a3 [0x7010708001c,0x2f]) (lf 0x276d5120018a3 [0x7010708001c,0x2f]))))) (nd (nd (nd (lf 0x173d512001623 [0x7010704012e]) (lf 0x365d5120018a3 [0x6001a0708,0x701])) (nd (lf 0x176d5120012a3 [0x600090708,0x701]) (lf 0x3735912001623 [0x7010704000a]))) (nd (nd (lf 0x37559120014a3 [0x70400090708,0x1040701011a]) (lf 0x175d9120018a3 [0x7010708000d])) (nd (lf 0x275d9120018a3 [0x7010708000d,0x704]) (nd (lf 0x265d9120018a3 [0x1300090708,0x5040701]) (lf 0x265d912001aa3 [0x32000130011,0xd03010304]))))))
def RtT5_3 := nd (nd (nd (nd (nd (lf 0x175d9120014a3 [0x7010708000d,0x7040013]) (lf 0x175d9120016a3 [0x7080013011a,0x10407040701,0xd])) (nd (lf 0x275d9120014a3 [0x12000130708,0x10407010704]) (lf 0x17419520014a3 [0x70400130708,0x701]))) (nd (nd (lf 0x27619520011a3 [0x705001a0708,0x1]) (lf 0x1731952001723 [0x130120002b,0x1080705])) (nd (lf 0x17419520016a3 [0x70800130120,0x70403050701,0x1040116]) (nd (lf 0x3735952001523 [0x70107050003]) (lf 0x37459520014a3 [0x70100090708,0x704]))))) (nd (nd (nd (lf 0x3735952001323 [0x140705001a,0x701]) (lf 0x37459520012a3 [0x701001a0708,0x704])) (nd (lf 0x3735952001723 [0x705001c0011,0x700030031,0x308]) (lf 0x37459520016a3 [0x30500100011,0x31]))) (nd (nd (lf 0x1739952001723 [0x90705012e,0x10807040701]) (lf 0x17499520016a3 [0x12003050011,0x1160021])) (nd (lf 0x36599520019a3 [0x70100130003,0x70507080704]) (nd (lf 0x174d9520018a3 [0x70107040708,0x705]) (lf 0x174d9520014a3 [0x1040708001c])))))) (nd (nd (nd (nd (lf 0x3548c12001c23 [0x701001c0413,0x32]) (lf 0x1758c12001523 [0x70100100705,0x4090704])) (nd (lf 0x1758c12001723 [0x705011a001c,0x10107040701]) (lf 0x3635012001a23 [0x70400130009,0x5200701]))) (nd (nd (lf 0x3735012001623 [0x70100090029,0x704]) (lf 0x37550120014a3 [0x70400090708,0x701])) (nd (lf 0x17590120014a3 [0x70400130708,0x701]) (nd (lf 0x17590120016a3 [0x130708011a,0x7040701]) (lf 0x27590120014a3 [0x12000130708,0x7010104]))))) (nd (nd (nd (lf 0x17414120014a3 [0x70100290708,0x1050704]) (lf 0x27614120011a3 [0x70500130708,0x1])) (nd (lf 0x2411412001e83 [0x7080520002b,0x11f]) (lf 0x1731412001723 [0x130120002b,0x1080705]))) (nd (nd (lf 0x17414120016a3 [0x70800130120,0x70403050701,0x1040116]) (lf 0x27614120013a3 [0x70800130006,0x70407010705])) (nd (lf 0x3735412001523 [0x7050011]) (nd (lf 0x37454120014a3 [0x70400090708,0x701]) (lf 0x3635412001b23 [0x70107050010,0x504]))))))
def RtT5_4 := nd (nd (nd (nd (nd (lf 0x3735412001723 [0x1c00260011,0x7050007]) (lf 0x1545412001ca3 [0x11a07080409,0x60100260701,0x10503040504])) (nd (lf 0x37454120016a3 [0x30500100011,0x1a]) (lf 0x17494120014a3 [0x70400290708,0x1050701]))) (nd (nd (lf 0x2419412001e83 [0x40907080304,0x420011a0406,0x13]) (lf 0x363d412001923 [0x1307050009,0x701])) (nd (lf 0x364d4120018a3 [0x1300090708,0x701]) (lf 0x173d412001723 [0x7010705012e,0x10806040009,0x14])))) (nd (nd (nd (lf 0x154d412001ca3 [0x70107080409,0x11a05040304,0x6010029000c]) (lf 0x364d412001aa3 [0x70800070520,0x50105040701])) (nd (lf 0x174d4120016a3 [0x7080018000d,0x907040701,0x601]) (lf 0x365d4120019a3 [0x70107050708,0x504001a0009,0x204]))) (nd (nd (lf 0x37454d2001633 [0x60e0701012e,0x604]) (lf 0x354d8d2001833 [0x320413001c])) (nd (lf 0x175d8d2001133 [0x701001a0705,0x4090704]) (nd (lf 0x3735952001333 [0x1a0705001c,0x70407010014,0x9]) (lf 0x1658c62001f03 [0x7050504020b,0x206])))))) (nd (nd (nd (nd (lf 0x2658c62001f03 [0x504020b0320,0x21a00230705]) (lf 0x1768c62001703 [0x330022])) (nd (lf 0x3735862001703 [0x11d0705040b]) (lf 0x16558e2001b23 [0x70107050023,0x504001a0030]))) (nd (nd (lf 0x37558e2001523 [0x7050030]) (lf 0x37659620019a3 [0x70107050708,0x60704])) (nd (lf 0x1654c22001b23 [0x705021a001c,0xb0504]) (nd (lf 0x3754c22001523 [0x1c0705040b,0x1a07010704]) (lf 0x3764c22001323 [0x1c07050034,0x1a07040701]))))) (nd (nd (nd (lf 0x3764c22001b23 [0x35001c0022,0x701]) (lf 0x37650220012a3 [0x70100020708,0x180704])) (nd (lf 0x715422001d83 [0x40b07080304,0x10107050009]) (lf 0x3715422001d83 [0x40b07080705,0x3010009]))) (nd (nd (lf 0x37654220011a3 [0x607050708,0x1]) (lf 0x37654220019a3 [0x907050708,0x607040701])) (nd (lf 0x2315422001f03 [0x3040705040b,0x406060e]) (nd (lf 0x1635422001b23 [0x5200705000a,0x1a000b0701]) (lf 0x176d4220019a3 [0x70107050708,0x90204]))))))
def RtT5_5 := nd (nd (nd (nd (nd (lf 0x231d422001f03 [0x304040b0520,0x21d0705]) (lf 0x165d4220019a3 [0x607050708,0x40e02010204,0x501])) (nd (lf 0x176d4220013a3 [0x7050708001e,0xb07010704]) (lf 0x37558e2001133 [0x705040b001a]))) (nd (nd (lf 0x715962001993 [0x708040b0304,0x3010705]) (lf 0x3715962001993 [0x40b07080705,0x304])) (nd (lf 0x1759013001663 [0x701001c0010,0x601]) (lf 0x3625413001b23 [0x5040705001e,0x1a0701040b])))) (nd (nd (nd (lf 0x3725413001723 [0x701001c0026,0x34001a0604]) (lf 0x1545413001c63 [0x11a070e0409,0x50406010701,0x260301])) (nd (lf 0x3745413001663 [0x701001c0026,0x42006010604,0x1a]) (lf 0x3629413001923 [0x7050035]))) (nd (nd (lf 0x2769413001563 [0x705070e0035,0x1b00220701]) (lf 0x3629413001b23 [0x705001c0035,0x7010704])) (nd (lf 0x765513001273 [0x70e0018000c,0xf0001001c]) (nd (lf 0x1721953001533 [0x70407050409,0xb0101010f,0x1a]) (lf 0x1741953001473 [0x35070e0409,0x701])))))) (nd (nd (nd (nd (lf 0x2761953001173 [0x9070e0035,0x7010705]) (lf 0x3725953001333 [0x705001a0009,0x704000f])) (nd (lf 0x3745953001273 [0x16001a070e,0x107040009]) (lf 0x3548863001c03 [0x12]))) (nd (nd (lf 0x1648863001e03 [0x3200011]) (lf 0x1658863001d03 [0x7050012])) (nd (lf 0x2658863001d03 [0x7050011]) (nd (lf 0x3725863001703 [0x7050036]) (lf 0x1749863001643 [0x70e0027]))))) (nd (nd (nd (lf 0x2659863001b43 [0x70503200027]) (lf 0x35458a3001c23 [0x7040413002f,0x320701])) (nd (lf 0x16558a3001923 [0x70100130705,0x2f0704]) (lf 0x16558a3001b23 [0x7050018002f,0x1307010704]))) (nd (nd (lf 0x176d523001063 [0x7040032070e]) (lf 0x176d523001863 [0x120037])) (nd (lf 0x276d523001863 [0x70e0012]) (nd (lf 0x172d523001623 [0x70101200019]) (lf 0x365d523001863 [0x70e0012]))))))
def RtT5_6 := nd (nd (nd (nd (nd (lf 0x176d523001263 [0x120037]) (lf 0x3745963001463 [0x70e0012])) (nd (lf 0x3765963001963 [0x705070e0011,0x18]) (lf 0x1729963001523 [0x701040b0705,0x10600380704,0xf]))) (nd (nd (lf 0x2215023001e03 [0x5200011]) (lf 0x1625423001b23 [0x1e07050018,0x5010701])) (nd (lf 0x221d423001d03 [0x7050011]) (lf 0x172d423001523 [0x701040b0705,0x10600380704,0xf])))) (nd (nd (nd (lf 0x176d423001963 [0x705070e0011,0x18]) (lf 0x165d423001963 [0x705070e0011,0x18])) (nd (lf 0x176d423001363 [0x705070e0012,0x39]) (lf 0x1648863001a13 [0x5040229]))) (nd (nd (lf 0x1658863001913 [0x7050011]) (lf 0x3638854001a13 [0x5040229])) (nd (lf 0x153d894001a33 [0x3080605]) (nd (lf 0x3535864001c43 [0x70e003a]) (lf 0x3539864001c43 [0x70e003a])))))) (nd (nd (nd (nd (lf 0x16558a40018a3 [0x7010708000d]) (lf 0x16558a4001aa3 [0x70800180010,0x701])) (nd (lf 0x26558a40018a3 [0x7010708000d]) (lf 0x16558e4001a63 [0x701003a0010,0x501]))) (nd (nd (lf 0x3735964001463 [0x114070e040b,0x7040701]) (lf 0x37659640018e3 [0x708070e000d,0x30107040701])) (nd (lf 0x1625424001aa3 [0x70107080010,0xd]) (nd (lf 0x1635424001a63 [0x701070e000a,0xb051a0520,0x108]) (lf 0x162d4240018a3 [0x7010708000d]))))) (nd (nd (nd (lf 0x176d4240018e3 [0x70e000a0018,0x2040708]) (lf 0x165d4240018e3 [0x708070e000d,0x20405010701])) (nd (lf 0x1629045001a83 [0x70805040220,0x30e]) (lf 0x1639045001a43 [0x504070e0220,0x214]))) (nd (nd (lf 0x26590450018c3 [0x504070e0220,0x708]) (lf 0x17299450011a3 [0x708000f0705,0x1])) (nd (lf 0x17298050013a3 [0x70507080420,0x7040701000f,0x1a0014]) (nd (lf 0x1638845001b13 [0x20b05040705,0x2140220]) (lf 0x1768845001393 [0x7050708001e,0x13]))))))
def RtT5_7 := nd (nd (nd (nd (nd (lf 0x1628c45001b13 [0x705020b0504,0x20f0220030e]) (lf 0x1648c45001a53 [0x70e020b0026,0x220])) (nd (lf 0x3638855001b03 [0x30807050504,0x21a06200214]) (lf 0x2768855001383 [0x3b07080705,0x6200031]))) (nd (nd (lf 0x3628c55001b03 [0x30e07050504,0x20b020f]) (lf 0x3648c55001a43 [0x70e04200026])) (nd (lf 0x362d855001b83 [0x708001a003c,0x220705]) (nd (lf 0x365d8550019c3 [0x70e07080025,0x3c]) (lf 0x365d8950019a3 [0x1907080025,0x50e]))))) (nd (nd (nd (lf 0x365d8d5001963 [0x705070e0039,0x2207010704]) (lf 0x172d9150012a3 [0x701000f0708,0x41a0704])) (nd (lf 0x365d9150018e3 [0x70e0708003d,0x30107040701,0x3]) (lf 0x172d9550015a3 [0x7050708001a,0x3c07010013,0x300220704]))) (nd (nd (lf 0x2768855001393 [0x110025]) (lf 0x3628c55001b13 [0xa030e0025])) (nd (lf 0x3648c55001a53 [0x21a06200026,0x4200009]) (nd (lf 0x173d895001333 [0x40907050014,0x1a0620041a]) (lf 0x172d8d5001333 [0x1e07050039,0xf04090701])))))) (nd (nd (nd (nd (lf 0x174d8d5001273 [0x60b070e0016,0x1041a0409]) (lf 0x1768c65001543 [0x11d0705070e,0x504060b])) (nd (lf 0x3735865001543 [0x11d0705040b]) (lf 0x16458a50018a3 [0x70400290708,0x3050701]))) (nd (nd (lf 0x37258e5001523 [0x7050039]) (lf 0x16558650019c3 [0x708070e0025])) (nd (lf 0x37358a5001323 [0x7010705002f]) (nd (lf 0x37259650013a3 [0x70404200022,0x701]) (lf 0x3735965001363 [0x1a070e0036,0x705]))))) (nd (nd (nd (lf 0x37459650012e3 [0x420070e003e,0xf001a0708]) (lf 0x37258e5001133 [0x705040b000f])) (nd (lf 0x231d425001d43 [0x7050304070e,0x420040b]) (lf 0x162d4250019a3 [0x70804200013,0x70407010705]))) (nd (nd (lf 0x1648865001a93 [0x50407080229,0x205021a]) (lf 0x1629065001a93 [0x708020b0504,0x620020f020e,0x13001a])) (nd (lf 0x37258e5001333 [0x705000f001c,0x7010704]) (nd (lf 0x37458e5001273 [0x40b0016070e,0x1041a0620]) (lf 0x37259650013b3 [0x70009030e,0x40b001a000a,0x100040420]))))))
def RtT5 : BTree NodeData := nd (nd (nd RtT5_0 RtT5_1) (nd RtT5_2 RtT5_3)) (nd (nd RtT5_4 RtT5_5) (nd RtT5_6 RtT5_7))
def RtM5 : BST := BN 229828172 768 (BN 191185517 384 (BN 112266262 0 (BN 88092798 896 (BL 50992988 640) BE) (BL 158217439 256)) (BN 204585578 1664 (BN 203214122 1280 (BL 201747600 1921) BE) (BL 213747090 513))) (BN 274756821 1408 (BN 243598556 1920 (BN 235789542 1537 (BL 231817340 1792) BE) (BL 244505505 1)) (BN 323295962 128 (BL 300144701 1536) (BL 383371652 512)))
def RtT6_0 := nd (nd (nd (nd (lf 0xd481000f92 [0x30501200018,0x2f02010308,0x38]) (nd (lf 0xd4c1000d52 [0x30e03050010,0x20]) (lf 0x58c1000b52 [0xb002d0305,0x20002f030e,0x18]))) (nd (nd (lf 0x5941000bd2 [0x30503080010,0x1a]) (lf 0x99410009d2 [0xb03050308,0x30e0020])) (nd (lf 0x9011000ec2 [0x201030e0308,0x220001c000b,0x18]) (lf 0x5491000d92 [0x3303050308,0x204020b0201,0x6000a0019])))) (nd (nd (lf 0x5491000f92 [0x3050018001c,0x20400060308,0xa]) (nd (lf 0xd891000b92 [0x1c03050308,0x20b000f0023]) (lf 0x54d1000f52 [0x305030e0018,0x204002e0201]))) (nd (nd (lf 0xd4d1000d52 [0x30e0305000a]) (lf 0xd8d1000b52 [0x1d0305030e,0x200009020b])) (nd (lf 0x5511000ed2 [0x3080018001c,0xa030e]) (lf 0xd911000ad2 [0x30e001f0308,0x1a0005001c]))))) (nd (nd (nd (lf 0xd9510009d2 [0x30e03050308,0x1a020b001c]) (nd (lf 0xd951000bd2 [0x308001c0018,0x30e0305]) (lf 0xd4a1000f82 [0x20103050120,0x308]))) (nd (nd (lf 0x5521000ec2 [0x30e03080018]) (lf 0x4821000f82 [0x30503080013,0x120001c0018])) (nd (lf 0x5421000dc2 [0x30503080010,0x90201030e]) (lf 0x5421000fc2 [0x30503080010,0x18030e])))) (nd (nd (nd (lf 0xd421000dc2 [0x30e03080305,0x1801200201]) (lf 0xd421000fc2 [0x30501200018,0x30e0308])) (nd (lf 0xd4a1000f92 [0x30501200018,0x380308]) (lf 0x58a1000b92 [0x30503080013,0x1e0018]))) (nd (nd (lf 0xd4e1000d52 [0x3050010]) (lf 0x58e1000b52 [0x30e000b0305,0x200018001d])) (nd (lf 0x5921000ad2 [0x308000b030e,0x1a001f]) (lf 0x59610009d2 [0x30503080010,0x1a000b030e])))))
def RtT6_1 := nd (nd (nd (nd (lf 0x5961000bd2 [0x30503080010,0xb001a030e]) (nd (lf 0x54b1000d82 [0x20403080025,0x305]) (lf 0x54b1000f82 [0x703080025]))) (nd (nd (lf 0x54f1000f42 [0x7030e0025]) (lf 0xd4f1000f42 [0x30e03050120,0x204])) (nd (lf 0x5931000ac2 [0x3080007030e,0x28]) (lf 0x8831000f82 [0xb03050308,0x2500180204])))) (nd (nd (nd (lf 0x4c31000f42 [0x30e0305001c,0x8]) (lf 0x8c31000f42 [0xb030e0305,0x12000180204,0x25])) (nd (lf 0x9031000ec2 [0x204030e0308,0x18001c000b,0x220]) (lf 0x1431000fc2 [0x30e03050120,0x3080204]))) (nd (nd (lf 0x5431000fc2 [0x308030e0025,0x703050020,0xb]) (lf 0x9431000dc2 [0x305030e0308,0xb0204])) (nd (lf 0x9431000fc2 [0x308030e0025,0x200007001c]) (lf 0xd431000fc2 [0x30503080120,0x10204030e]))))) (nd (nd (nd (lf 0x54b1000d92 [0x20403050308,0x25000b0019,0xa02010033,0x6]) (nd (lf 0x54b1000f92 [0x308001c0025,0xb00180006,0x7000a]) (lf 0x54f1000f52 [0x305030e0018,0x9000b0204,0x2e0007]))) (nd (nd (lf 0xd4f1000d52 [0x30e0305000a]) (lf 0x5531000ed2 [0x30e0018001c,0xa000b0308])) (nd (lf 0x5931000ad2 [0x28030e0308,0x20b001c0007,0x1a0005]) (lf 0x5971000bd2 [0x30e0018001c,0x103050308])))) (nd (nd (nd (lf 0x99710009d2 [0x2003050308,0x9020b030e]) (lf 0x9052000e82 [0x303080104,0x130220])) (nd (lf 0x1852000f82 [0x30803050013,0x1001c002c]) (lf 0xd852000f82 [0x30803050013,0x31001c002c,0x21]))) (nd (nd (lf 0x54d2000f22 [0x11a012e0305,0x10803040301,0x1a000a0013]) (lf 0xd8d2000b22 [0x301002f0305,0x1a0304])) (nd (lf 0xd8d2000f22 [0x30103050013,0x2f001c0304]) (lf 0x5512000ea2 [0x301002c0308,0x105000c0304,0x900130003,0x2001040201])))))
def RtT6_2 := nd (nd (nd (nd (lf 0xd512000ca2 [0x304001c0308,0x10400090301]) (nd (lf 0xd512000ea2 [0x3010308001c,0x10101040304,0x2f]) (lf 0x5912000ea2 [0x104001c0011,0x50101]))) (nd (nd (lf 0xd912000aa2 [0x30100070308,0x304]) (lf 0xd912000ea2 [0x30403080013,0x7002c0301,0x120])) (nd (lf 0x1952000da2 [0x30503080013,0x10403010304]) (lf 0x1952000fa2 [0x30803050013,0x30403010120,0x901010104,0x1a])))) (nd (nd (nd (lf 0x5952000da2 [0x30503010003,0x2001010304]) (lf 0x5952000ba2 [0x3050308001a,0x103040301])) (nd (lf 0x5952000fa2 [0x1c03050011,0x300310308,0x601010104,0x130007]) (lf 0x99520009a2 [0x30803050020,0x10304]))) (nd (nd (lf 0x9952000da2 [0x30503010003,0x903080304,0x104]) (lf 0x9952000fa2 [0x12003050011,0x2100030308,0x2f01010104,0x1a0013])) (nd (lf 0xd9520009a2 [0x30103050308,0x304]) (lf 0xd952000da2 [0x30503080013,0x3010304]))))) (nd (nd (nd (lf 0xd952000ba2 [0x3050308001a,0x3040301]) (nd (lf 0xd952000fa2 [0x3080013001c,0x30403010305,0x1a00090006]) (lf 0x8c12000f22 [0x30103050013,0x18001c0304]))) (nd (nd (lf 0x5012000ea2 [0x101001c0011,0x5]) (lf 0x9012000ea2 [0x30403080013,0x12000180301])) (nd (lf 0x1412000da2 [0x30503080013,0x10403010304]) (lf 0x1412000fa2 [0x30803050013,0x30403010120,0x901010104])))) (nd (nd (nd (lf 0x5412000da2 [0x20103050011,0x20000e0101]) (lf 0x5412000fa2 [0x1c03050011,0x20100200007,0xb0101])) (nd (lf 0x9412000da2 [0x30503080013,0x3010304]) (lf 0x9412000fa2 [0x3080013001c,0x30403010305,0x1a00200009,0x6]))) (nd (nd (lf 0xd412000da2 [0x20e03050011,0x10402010308]) (lf 0xd412000fa2 [0x30501200011,0x10402010308,0x20e002f0101,0x1a000b])) (nd (lf 0x9052000e92 [0x220000b0011,0x18]) (lf 0x54d2000f32 [0x1c0305000a,0x1303040301,0x108020e])))))
def RtT6_3 := nd (nd (nd (nd (lf 0xd8d2000b32 [0x30403050013,0x1a002f0301]) (nd (lf 0x5512000eb2 [0x308001c0018,0x304000b0301,0x10500200201]) (lf 0xd512000cb2 [0x3040308001c,0x10400090301]))) (nd (nd (lf 0xd912000ab2 [0x703080013,0x20e03040301]) (lf 0x19520009b2 [0x30503080020,0x903040301,0x4020e000b])) (nd (lf 0x5952000bb2 [0x308001c0018,0x403010305,0x6001a0009,0x130001]) (lf 0x99520009b2 [0x30803050011])))) (nd (nd (nd (lf 0xd9520009b2 [0x30503080013,0x20e03010304]) (lf 0xd952000bb2 [0x308001a001c,0x30103050013,0x20020e0009])) (nd (lf 0x8c62000f02 [0x20b03050104,0x25]) (lf 0x5862000f82 [0xb03050308,0x180101]))) (nd (nd (lf 0x9862000f82 [0xb03050308,0x2500180104]) (lf 0x54e2000f22 [0x30403050018,0x1080301])) (nd (lf 0x58e2000f22 [0x304000b0305,0x3000230301,0x30801040018]) (lf 0x5922000ea2 [0x30403080029,0x500180301]))))) (nd (nd (nd (lf 0x5962000da2 [0x30103080305,0x20000b0304]) (nd (lf 0x5962000ba2 [0xb03080025]) (lf 0x5962000fa2 [0x30503080018,0xb03010304,0x60025]))) (nd (nd (lf 0x99620009a2 [0x2003050308,0x1]) (lf 0x9962000da2 [0xb03050308,0x1803010304])) (nd (lf 0x9962000fa2 [0x30801200018,0xb03040305,0x1a0301]) (lf 0x4c22000f22 [0x1c000b0305,0x3503010304,0x1040018])))) (nd (nd (nd (lf 0x5022000ea2 [0x30103080029,0x180304]) (lf 0x5422000da2 [0x30103080305,0x101000b0304])) (nd (lf 0x5422000fa2 [0x30503080018,0xb03010304,0x600200101]) (lf 0xd422000da2 [0xb03050308,0x1803010304]))) (nd (nd (lf 0xd422000fa2 [0x30801200018,0xb03040305,0x301]) (lf 0x8c62000f12 [0x3050104020b,0x1d0025])) (nd (lf 0x58e2000b32 [0x2f0305000b,0x1a00350301,0x3080304]) (lf 0x5922000ab2 [0x30403080029,0x1800050301])))))
def RtT6_4 := nd (nd (nd (nd (lf 0x59620009b2 [0x308000b0305,0x2003040301]) (nd (lf 0x5962000bb2 [0x308000b0025,0x40020]) (lf 0x99620009b2 [0xb03050308,0x30103040020]))) (nd (nd (lf 0x9013000e62 [0x1c000b030e,0x350018003f,0x2010220]) (lf 0x5413000f62 [0x305030e001c,0x20400070301,0x2001040201,0xb])) (nd (lf 0x9413000d62 [0xb0305030e,0x903010304,0x350204]) (lf 0x9413000f62 [0x305030e001c,0xb03040301,0x2002010007,0x2e])))) (nd (nd (nd (lf 0x1853000f52 [0x30e001c0035,0x1010305]) (lf 0xd853000f52 [0x30e001c0035,0x2080305])) (nd (lf 0xd893000b32 [0x1e00230305,0x3010304020b,0x1a000f]) (lf 0xd893000f32 [0x305001c0035,0x10103010208]))) (nd (nd (lf 0x5513000e72 [0x30e0018001c,0x201000b0301,0x200101]) (lf 0xd913000a72 [0x1c0007030e,0x304000d020b,0x301])) (nd (lf 0xd913000e72 [0x30e0035001c,0xd0208]) (lf 0x1953000d72 [0x30e00090035,0xb03010305]))))) (nd (nd (nd (lf 0x5953000b72 [0x30e03050018,0x903040301,0x10004002e]) (nd (lf 0xd953000972 [0x1c0305030e,0x3010304001a,0x20b]) (lf 0xd953000d72 [0x30e001c0035,0x30103050208]))) (nd (nd (lf 0xd953000b72 [0x30e0018001c,0x301001a0305]) (lf 0x8863000f02 [0x2503050012,0x104])) (nd (lf 0x5863000f42 [0x18030e0305,0x1040101]) (lf 0x9863000f42 [0xb030e0305,0x2500180104])))) (nd (nd (nd (lf 0x58a3000f22 [0x30103050013,0x18002f0304]) (lf 0xd523000c62 [0x304002f030e,0x301])) (nd (lf 0xd523000e62 [0x30e0012]) (lf 0x5923000e62 [0x304030e0029,0x12000180301]))) (nd (nd (lf 0x5963000d62 [0xb030e0305,0x1803040301,0x2f]) (lf 0x5963000b62 [0x305030e0025])) (nd (lf 0x5963000f62 [0x305030e0012,0x180025]) (lf 0x9963000d62 [0xb0305030e,0x1803010304,0x120])))))
def RtT6_5 := nd (nd (nd (nd (lf 0x9963000f62 [0x30e00180012,0x1a0305]) (nd (lf 0xd963000b62 [0x4030e0025]) (lf 0x5023000e62 [0x304030e0029,0x12000180301]))) (nd (nd (lf 0x5423000f62 [0x180305003d,0x20403010304]) (lf 0xd423000d62 [0xb0305030e,0x1803010304,0x120])) (nd (lf 0xd423000f62 [0x30e00180012,0x2040305]) (lf 0x8863000f12 [0x305003d])))) (nd (nd (nd (lf 0x58a3000b32 [0x30403050013,0x1a001e0301]) (lf 0x5923000a72 [0x304030e0029,0x180301])) (nd (lf 0x5963000972 [0xb030e0305,0x30403010010,0x1a]) (lf 0x5963000b72 [0xb003d0025,0x30e]))) (nd (nd (lf 0x8854000e92 [0x2200308002b]) (lf 0xd894000ab2 [0x30103080029,0x2050304])) (nd (lf 0x54d4000e72 [0x30e0018002b,0x108001c0205,0x29]) (lf 0xd8d4000a72 [0x304030e0029,0x301]))))) (nd (nd (nd (lf 0xd9540008f2 [0x30e03080029,0x3010304]) (nd (lf 0xd954000af2 [0x30e001a001c,0x3010308]) (lf 0x5864000ec2 [0x3a030e0308,0x120000b0101,0x18]))) (nd (nd (lf 0x9864000ec2 [0x3a030e0308,0x18000b0104,0x120]) (lf 0x58a4000aa2 [0xf00130308,0x3040301])) (nd (lf 0x58a4000ea2 [0x30103080013,0x1e00180304]) (lf 0xd4e4000c62 [0x304030e0010,0x301])))) (nd (nd (nd (lf 0xd4e4000e62 [0x30403010010,0x101]) (lf 0x58e4000e62 [0x18030e003a,0xb01010040,0x3080120])) (nd (lf 0x5964000ce2 [0x30e03080010,0x3040301000b]) (lf 0x5964000ee2 [0x1803080010,0x301]))) (nd (nd (lf 0x9964000ce2 [0xb0308030e,0x30403010018]) (lf 0x9964000ee2 [0x30801200018,0x3040301030e,0x1e000b])) (nd (lf 0x5424000ee2 [0x1803080010,0x200301]) (lf 0xd424000ce2 [0xb0308030e,0x30403010018])))))
def RtT6_6 := nd (nd (nd (nd (lf 0xd424000ee2 [0x30801200018,0x3040301030e,0x1e000b]) (nd (lf 0x58a4000ab2 [0x30403080013,0x1e00180301,0x205]) (lf 0x58e4000a72 [0x2f000b030e,0x3500180301,0x308]))) (nd (nd (lf 0x59640008f2 [0xb03080010,0x3010304030e]) (lf 0x5964000af2 [0x1a03080010,0xb0301])) (nd (lf 0x99640008f2 [0x30e0308000b,0x30103040020,0x4]) (lf 0x9045000ec2 [0x104030e0220,0x308])))) (nd (nd (nd (lf 0x5885000ba2 [0x30800200305,0xf03010304,0x10e]) (lf 0x58c5000b62 [0x30e0305002e,0x3010304])) (nd (lf 0x99450009e2 [0x200305030e,0x30403010308]) (lf 0x9805000be2 [0x308030e0025,0x403050020]))) (nd (nd (lf 0x8845000f92 [0x3050308020b,0x2502200104,0x11]) (lf 0x8c45000f52 [0x104030e020b,0x2502200305,0x1d])) (nd (lf 0x5885000bb2 [0x308000b0006,0x30103040305,0x40020010e]) (lf 0x58c5000b72 [0x30e000b002e,0x30403010305,0x40108]))))) (nd (nd (nd (lf 0x8855000f82 [0x3080025]) (nd (lf 0x8c55000f42 [0x20030e0025]) (lf 0x1855000fc2 [0x30803050010,0x104001a0101]))) (nd (nd (lf 0xd855000fc2 [0x30800100025,0x101030e]) (lf 0xd895000ba2 [0x1703050308,0x10e03040301,0xf000b])) (nd (lf 0xd895000fa2 [0x1703080025,0x10e]) (lf 0xd8d5000b62 [0x390305030e,0x1a03010304,0x140220])))) (nd (nd (nd (lf 0xd8d5000f62 [0x3050039003d,0x301030e]) (lf 0xd915000ae2 [0x308030e0037,0x30400160220,0x301])) (nd (lf 0xd915000ee2 [0x30800100025]) (lf 0xd955000de2 [0x308030e0025,0x101]))) (nd (nd (lf 0x8855000f92 [0x110025003d,0x104]) (lf 0x8c55000f52 [0xa030e0025,0x1040305020b,0x1d0020])) (nd (lf 0xd895000bb2 [0x10e03050308,0x20b03040017,0x903010220,0x10004000f]) (lf 0xd895000fb2 [0x1c00180023,0x22000070041,0x20b000a010e])))))
def RtT6_7 := nd (nd (nd (nd (lf 0xd8d5000b72 [0x30403050010,0x30e01080301,0x1003d]) (nd (lf 0x8c65000d42 [0x3050104030e,0x20b]) (lf 0x5865000dc2 [0x305030e0308,0x101000b]))) (nd (nd (lf 0x9865000dc2 [0x305030e0308,0x104000b]) (lf 0x58a50009a2 [0x30103050308,0xf0304])) (nd (lf 0x58a5000da2 [0x30503080013,0x3010304]) (lf 0x58e5000d62 [0xb0305030e,0x1c03010304,0x30800390104])))) (nd (nd (nd (lf 0x5925000ce2 [0x30e03080029,0x3040301]) (lf 0x8865000f82 [0x3080025])) (nd (lf 0x8c65000f42 [0x30e0025]) (lf 0x5865000fc2 [0x308030e0025,0x104001c0101]))) (nd (nd (lf 0x9865000fc2 [0x30e001c0031,0x10103080305]) (lf 0x58a5000ba2 [0x30103050308,0x1a0304010e,0x2200013000f])) (nd (lf 0x58a5000fa2 [0x308001a001c,0x30100130305,0x10e]) (lf 0x58e5000f62 [0x30e001c0039,0x30101080305]))))) (nd (nd (nd (lf 0x5925000ee2 [0x30e03080025,0x105001c]) (nd (lf 0x5965000be2 [0x308030e0025,0x10020]) (lf 0x8c65000d52 [0x3050104020b,0x1d030e]))) (nd (nd (lf 0x58a50009b2 [0x308000b0305,0x10e03010304,0xf]) (lf 0x58e5000972 [0x305000b030e,0x30100350014,0x308])) (nd (lf 0x59250008f2 [0x30e03080029,0x3010304]) (lf 0xd425000de2 [0x3050308030e,0x3010020000b,0x304])))) (nd (nd (nd (lf 0x8865000f92 [0x3d03080025,0x110305]) (lf 0x8c65000f52 [0x20b030e0025,0x1d0104])) (nd (lf 0x9065000ed2 [0x20b030e0007,0x1102200308]) (lf 0x58a5000bb2 [0x3080013001c,0x301010e0305,0x9000b0304]))) (nd (nd (lf 0x58e5000b72 [0x305030e001c,0x3040301000b,0x10108]) (lf 0x5925000af2 [0x3080029001c,0x3040301030e,0x105])) (nd (lf 0x5965000bf2 [0x700090010,0x308030e0305,0x11000b0020,0x1a000a]) (lf 0x5823100b52 [0x30e0305001c])))))
def RtT6 : BTree NodeData := nd (nd (nd RtT6_0 RtT6_1) (nd RtT6_2 RtT6_3)) (nd (nd RtT6_4 RtT6_5) (nd RtT6_6 RtT6_7))
def RtM6 : BST := BN 276519828 26880 (BN 222778932 63873 (BN 182243223 64896 (BN 149586024 22528 (BN 116304151 9217 (BN 89356042 26240 (BN 56291116 27008 (BN 34970739 8064 (BL 30790953 32129) BE) (BN 86396516 22912 (BL 82504236 4480) BE)) (BN 99716253 897 (BN 98381898 12673 (BL 91273909 11648) BE) (BN 115727339 65024 (BL 104409560 5760) BE))) (BN 139202350 23552 (BN 124541223 10240 (BN 122111250 14336 (BL 121233288 24448) BE) (BN 125970174 4096 (BL 125648407 19328) BE)) (BN 146472587 2049 (BN 145693946 27648 (BL 144034528 26496) BE) (BL 146631175 17280)))) (BN 168617915 11776 (BN 160175571 512 (BN 154235894 12544 (BN 152724663 21376 (BL 150426206 8192) BE) (BN 158430877 9088 (BL 156437996 65025) BE)) (BN 164918628 29696 (BN 164006913 29057 (BL 161167007 15232) BE) (BL 165455565 10752))) (BN 174903199 5376 (BN 171403437 16384 (BN 170097585 4352 (BL 169907572 31232) BE) (BN 174188156 3072 (BL 174125327 896) BE)) (BN 180219942 5633 (BN 178768018 20736 (BL 175231411 22529) BE) (BL 182145846 29184))))) (BN 208271748 62720 (BN 199817890 23425 (BN 196050451 32128 (BN 190477031 3968 (BN 188616664 24576 (BL 185803190 17920) BE) (BN 191949210 2048 (BL 191243358 14721) BE)) (BN 198649986 24577 (BN 196672927 12800 (BL 196298757 20352) BE) (BN 198929233 65152 (BL 198761510 23040) BE))) (BN 204818536 10112 (BN 204003553 32256 (BN 203534308 23041 (BL 202524159 25856) BE) (BN 204585578 7808 (BL 204008342 19584) BE)) (BN 206395232 25472 (BN 205647423 13952 (BL 205568285 16256) BE) (BL 207537569 18048)))) (BN 215265927 32640 (BN 212820949 3840 (BN 209880768 11520 (BN 209717437 28160 (BL 208304369 15233) BE) (BN 212282401 15872 (BL 211556959 13824) BE)) (BN 214193801 23808 (BN 213855106 384 (BL 213416076 22272) BE) (BL 214837576 7040))) (BN 219841451 24064 (BN 217000735 24704 (BN 216606379 16640 (BL 216109900 31105) BE) (BN 219117766 31104 (BL 217530903 16897) BE)) (BN 220668635 25088 (BN 220255242 11265 (BL 220200278 23936) BE) (BL 222090477 7936)))))) (BN 246907797 4224 (BN 236456058 28672 (BN 228564529 7552 (BN 225714902 8705 (BN 224795965 26112 (BN 224525599 31744 (BL 224236729 32000) BE) (BN 225051343 26113 (BL 224952386 15744) BE)) (BN 226542086 7681 (BN 226108766 6528 (BL 225792163 29952) BE) (BN 228332154 31617 (BL 227356781 32512) BE))) (BN 233188775 14976 (BN 229766501 24192 (BN 229039255 28032 (BL 228865888 5504) BE) (BN 232498731 20992 (BL 230216880 16000) BE)) (BN 234863401 25344 (BN 233506257 64768 (BL 233204186 14208) BE) (BL 235408125 28801)))) (BN 241028649 29568 (BN 237899261 18945 (BN 237481599 17281 (BN 237321827 16129 (BL 236626309 8320) BE) (BN 237806452 21505 (BL 237637458 20224) BE)) (BN 240808751 19200 (BN 239258171 12672 (BL 239114128 19712) BE) (BL 240915204 13184))) (BN 243900461 30336 (BN 242358149 11136 (BN 242333948 12032 (BL 241139854 2816) BE) (BN 243377579 28928 (BL 242946313 21760) BE)) (BN 246237058 25857 (BN 245302006 768 (BL 244132929 13056) BE) (BL 246906986 24320))))) (BN 263119805 4736 (BN 255519344 9856 (BN 252647107 2304 (BN 249007059 6016 (BN 248170367 11264 (BL 247179909 14464) BE) (BN 249582198 30848 (BL 249251095 30849) BE)) (BN 254571534 17152 (BN 254529875 6272 (BL 254170357 26368) BE) (BL 254950916 63104))) (BN 261092769 24832 (BN 259648864 1152 (BN 257204141 22400 (BL 256728502 3329) BE) (BN 261022163 10496 (BL 260606929 26624) BE)) (BN 261378757 21120 (BN 261220965 641 (BL 261146366 24193) BE) (BL 261476441 30208)))) (BN 271648446 63872 (BN 268954852 16641 (BN 265898065 7553 (BN 265784620 4992 (BL 265669055 32385) BE) (BN 268817322 24960 (BL 267892179 16768) BE)) (BN 269569708 8832 (BN 269464507 22656 (BL 269092188 9344) BE) (BL 269845923 31616))) (BN 273819183 10880 (BN 272518949 6144 (BN 272325068 29056 (BL 271778921 15360) BE) (BN 273675342 9216 (BL 273119503 27136) BE)) (BN 274458391 21504 (BN 274227210 22144 (BL 274226964 23424) BE) (BL 276452049 7680))))))) (BN 334342810 15104 (BN 304183586 30976 (BN 290131011 18688 (BN 283671418 30720 (BN 278910176 12416 (BN 277713487 2560 (BN 277696040 5888 (BL 277279233 8704) BE) (BN 278719485 27137 (BL 278481238 17536) BE)) (BN 281512924 3328 (BN 281350924 28545 (BL 279175820 25216) BE) (BN 283082174 6145 (BL 282941622 18689) BE))) (BN 288419490 3456 (BN 285923154 64513 (BN 284959867 18432 (BL 284275611 1920) BE) (BN 288179704 18560 (BL 287383335 4609) BE)) (BN 289715175 12161 (BN 289097910 1792 (BL 289053690 27264) BE) (BL 289873410 13312)))) (BN 297424319 13568 (BN 292449956 7296 (BN 291366727 64128 (BN 290829672 1664 (BL 290790073 4864) BE) (BN 292211180 256 (BL 292154667 15616) BE)) (BN 294510220 14720 (BN 294001471 11392 (BL 292940946 63488) BE) (BL 296103430 6273))) (BN 300517933 2689 (BN 299062956 1793 (BN 298863147 64000 (BL 298323218 23168) BE) (BN 300204580 21632 (BL 299111418 32384) BE)) (BN 303536988 30592 (BN 302729513 62464 (BL 300983753 20480) BE) (BL 303635945 64001))))) (BN 313909042 28544 (BN 309004412 10881 (BN 305238255 27904 (BN 304530915 29824 (BN 304305725 64384 (BL 304199831 64256) BE) (BN 304908108 3712 (BL 304846946 13569) BE)) (BN 307254114 7168 (BN 306727321 1024 (BL 306340839 31488) BE) (BN 307821608 3585 (BL 307349626 1536) BE))) (BN 312023467 63360 (BN 310156176 11521 (BN 309840649 27776 (BL 309390167 8448) BE) (BN 311979332 65408 (BL 310253281 12288) BE)) (BN 312696757 0 (BN 312299560 10368 (BL 312122424 17921) BE) (BL 313787499 20096)))) (BN 323262872 8960 (BN 318078113 25600 (BN 315693459 21248 (BN 315022813 20097 (BL 314572601 62848) BE) (BN 316383492 14080 (BL 315996849 5120) BE)) (BN 320438507 18304 (BN 318807559 5632 (BL 318678385 62592) BE) (BL 320937712 1408))) (BN 330751400 65153 (BN 325880884 12033 (BN 325653020 30464 (BL 323501917 27520) BE) (BN 330207240 17792 (BL 328540740 63616) BE)) (BN 333435004 13696 (BN 333342153 25728 (BL 333147514 11393) BE) (BL 333860259 22016)))))) (BN 368460398 19840 (BN 346065060 18944 (BN 338349023 23296 (BN 336314203 62976 (BN 335799293 10624 (BN 335748324 19456 (BL 334386718 640) BE) (BN 336183347 29440 (BL 335852244 62208) BE)) (BN 336912809 16001 (BN 336539852 19968 (BL 336526856 14848) BE) (BN 337183167 17409 (BL 336987754 22784) BE))) (BN 344991631 29312 (BN 343050586 17664 (BN 342572669 63232 (BL 342180132 25984) BE) (BN 343979593 15488 (BL 343698256 21761) BE)) (BN 345452875 11008 (BN 345407896 30080 (BL 345121772 27392) BE) (BL 345974432 7424)))) (BN 356250845 1280 (BN 350517067 6656 (BN 348781006 31872 (BN 347126889 9600 (BL 346152003 6657) BE) (BN 348986692 27777 (BL 348903217 16128) BE)) (BN 352320114 9472 (BN 351040806 5248 (BL 350725852 9729) BE) (BL 355418106 62336))) (BN 363904585 2944 (BN 358526364 64640 (BN 358274620 29953 (BL 358172745 128) BE) (BN 362845894 12928 (BL 358868263 32513) BE)) (BN 365335184 14592 (BN 365228755 5377 (BL 364124249 12160) BE) (BL 367310607 8321))))) (BN 396487837 7937 (BN 386879140 2688 (BN 374632541 3584 (BN 369630678 28800 (BN 369327930 13440 (BL 368804705 31360) BE) (BN 373007922 17408 (BL 371535627 6400) BE)) (BN 377282422 4608 (BN 375007566 30209 (BL 374942434 17024) BE) (BL 384683378 2176))) (BN 390942722 6912 (BN 388045493 3841 (BN 387918726 22017 (BL 387349975 28416) BE) (BN 390052497 63744 (BL 389016257 26752) BE)) (BN 394276253 16512 (BN 392493644 62337 (BL 392166454 9728) BE) (BL 396029235 19969)))) (BN 426677818 9984 (BN 410924292 20608 (BN 401014686 21888 (BN 400980123 11137 (BL 400269015 23680) BE) (BN 406456535 3200 (BL 401278130 16896) BE)) (BN 424755949 2432 (BN 418211947 64512 (BL 417408290 18176) BE) (BL 425991243 20864))) (BN 442097879 11904 (BN 430195749 10369 (BN 429786695 65280 (BL 427178140 6784) BE) (BN 435874448 8576 (BL 431469127 19072) BE)) (BN 469485196 18816 (BN 451367407 28288 (BL 443106909 2177) BE) (BL 489775322 16513)))))))
def RtT7 : BTree NodeData := nd (nd (nd (nd (lf 0x10007d1 [0x1050108000b,0x10010010e,0x200018]) (nd (lf 0x110007d1 [0x10e01050108,0x1c000b0001,0x200004]) (lf 0x210007c1 [0x101080105,0x10e]))) (nd (lf 0x210007d1 [0x10e0108000b,0x1800100105,0x20]) (nd (lf 0x310007c1 [0x4010e0108,0x105]) (lf 0x310007d1 [0x105010e0108,0x1c000b0004,0x200001])))) (nd (nd (lf 0x120007a1 [0x10101080105,0x100200104]) (nd (lf 0x120007b1 [0x1301080105,0x10401010009,0x10020000e,0x1c]) (lf 0x220007a1 [0x10401050108,0x20000b0101]))) (nd (nd (lf 0x220007b1 [0x1050108000b,0xe01010104,0x2000180001]) (lf 0x13000771 [0x1c0105010e,0xb01040101,0x400200008,0x1])) (nd (lf 0x23000761 [0x1040105010e,0x4000b0101]) (lf 0x23000771 [0x105010e000b,0x1001010104,0x1800010004,0x20]))))) (nd (nd (nd (lf 0x140006f1 [0x290108010e,0x10401010009,0x400200005,0x1c0001]) (nd (lf 0x240006e1 [0xb010e0108,0x1040101]) (lf 0x240006f1 [0x10e0108000b,0x1001010104,0x2000010018]))) (nd (lf 0x50007e1 [0x10e01050020,0x10101040108,0x4]) (nd (lf 0x50007f1 [0x108010e000b,0x10400200105,0x100040101]) (lf 0x150007e1 [0x1050108010e,0x2001040101,0x1001a])))) (nd (nd (lf 0x150007f1 [0x1050108010e,0x10400090010,0x20000b0101,0x10004001a]) (nd (lf 0x250005e1 [0x1050108010e,0xb01040101]) (lf 0x250007e1 [0x1050108010e,0x2001040101,0x4001a]))) (nd (nd (lf 0x250005f1 [0x10e0108000b,0x10101040105,0x1]) (lf 0x250007f1 [0x108010e000b,0x10101040105,0x4001a0020,0x1])) (nd (lf 0x22100791 [0x401050108]) (lf 0x23100751 [0x1050004010e,0x20])))))
def RtM7 : BST := BN 286235688 3713 (BN 225615945 22144 (BN 194802900 27392 (BN 173580114 5760 (BN 114821660 7169 (BN 90548332 12288 (BN 54943124 29313 (BN 45673596 21633 (BL 38821790 6784) BE) (BL 84404316 15360)) (BN 113271022 26625 (BN 100581654 6145 (BL 93539839 8193) BE) (BL 113330775 12800))) (BN 159327371 19328 (BN 150301515 21632 (BN 121773119 13824 (BL 121049434 26240) BE) (BL 158743859 29312)) (BN 167769715 3968 (BN 163195866 6528 (BL 159776960 6785) BE) (BL 168843108 14336)))) (BN 184978670 9856 (BN 180651153 5633 (BN 179293801 14208 (BN 175709142 1664 (BL 175051171 10752) BE) (BL 179823969 20993)) (BN 184070993 4609 (BN 183298167 10240 (BL 181825960 20480) BE) (BL 184383543 31105))) (BN 190477031 19840 (BN 188563329 24448 (BN 186891535 30720 (BL 185757151 19968) BE) (BL 189953520 4352)) (BN 194190364 26881 (BN 193340521 26113 (BL 190496695 23552) BE) (BL 194199495 15616))))) (BN 210535728 25472 (BN 204845253 3969 (BN 198395864 4864 (BN 196170073 1 (BN 195575725 19329 (BL 195262031 22656) BE) (BL 196184670 29056)) (BN 203459892 29441 (BN 203435351 2432 (BL 198919375 897) BE) (BL 204627014 22913))) (BN 206456821 1024 (BN 205995784 1408 (BN 205168600 1409 (BL 205026234 6912) BE) (BL 206115623 3840)) (BN 209200863 12160 (BN 208182366 25601 (BL 207824374 5888) BE) (BL 209883706 19072)))) (BN 217879775 28672 (BN 215726349 9216 (BN 214438128 7552 (BN 211877695 14720 (BL 211024790 21248) BE) (BL 215682858 21376)) (BN 216941757 3584 (BN 216620134 27648 (BL 216266718 24704) BE) (BL 217451894 11265))) (BN 223087047 32512 (BN 220498847 5120 (BN 219805256 27520 (BL 218775235 28673) BE) (BL 222110056 32640)) (BN 224265706 28160 (BN 224192870 26624 (BL 224125202 6016) BE) (BL 224952386 23424)))))) (BN 255799891 30208 (BN 241352329 23168 (BN 234058289 8576 (BN 230121314 5376 (BN 227217579 2049 (BN 227149303 2048 (BL 225874290 21760) BE) (BL 227888781 26880)) (BN 233166443 11776 (BN 232002103 2944 (BL 230428510 13952) BE) (BL 233394730 28544))) (BN 238747081 3073 (BN 236331125 29440 (BN 236160534 11008 (BL 236096826 25216) BE) (BL 236973120 256)) (BN 239989106 31360 (BN 239259176 7681 (BL 238781364 1153) BE) (BL 241271631 1920)))) (BN 246242648 8448 (BN 245415464 25344 (BN 244434482 23297 (BN 242948632 19584 (BL 242401402 20096) BE) (BL 244602878 24320)) (BN 245964484 31744 (BN 245614916 10368 (BL 245572271 14976) BE) (BL 246031181 24960))) (BN 251974488 21121 (BN 249404291 16128 (BN 248528704 32001 (BL 247189425 19457) BE) (BL 251390976 11393)) (BN 254138957 22528 (BN 253345947 22016 (BL 252218160 11392) BE) (BL 255234012 512))))) (BN 274340409 26496 (BN 265898065 9088 (BN 260676655 4096 (BN 259874706 8832 (BN 258002150 27776 (BL 255869276 23937) BE) (BL 260416832 12929)) (BN 263067164 4224 (BN 261690433 18688 (BL 260863249 18689) BE) (BL 264410453 14337))) (BN 269239061 29184 (BN 268839996 21504 (BN 268681668 32384 (BL 267345524 24576) BE) (BL 269103311 6144)) (BN 269766560 29057 (BN 269380931 5121 (BL 269304087 19969) BE) (BL 270132777 13056)))) (BN 281127412 25984 (BN 277951196 384 (BN 276833504 13184 (BN 275167593 11136 (BL 275046779 11904) BE) (BL 277793344 30336)) (BN 279036088 22912 (BN 278676558 4480 (BL 278573615 15617) BE) (BL 280134543 24832))) (BN 285158594 128 (BN 283980348 25600 (BN 283609937 20352 (BL 283040181 14464) BE) (BL 284316307 28288)) (BN 285985778 9984 (BL 285415494 13313) (BL 286103032 15232))))))) (BN 349643041 31104 (BN 308445069 27137 (BN 298296090 11648 (BN 293857838 29697 (BN 288131704 22272 (BN 287544071 16000 (BN 287068954 8833 (BL 287062872 3712) BE) (BL 287946086 20864)) (BN 290829672 9344 (BN 290790073 14592 (BL 289575206 8705) BE) (BL 292422692 11264))) (BN 295726722 32256 (BN 294428122 8320 (BN 294266541 20736 (BL 293940270 8704) BE) (BL 294952033 31488)) (BN 297401232 14080 (BN 296966590 5504 (BL 296853460 29824) BE) (BL 298017550 25089)))) (BN 303209798 25088 (BN 300059601 1280 (BN 299220264 18944 (BN 298976592 23040 (BL 298844734 1537) BE) (BL 299232417 2816)) (BN 301235956 7808 (BN 300253365 4608 (BL 300099200 5248) BE) (BL 302382614 1536))) (BN 304865735 12672 (BN 303672271 27136 (BN 303650433 10625 (BL 303536988 21888) BE) (BL 304169066 8960)) (BN 307287078 9729 (BN 307085245 4737 (BL 306895467 12544) BE) (BL 308246120 14848))))) (BN 326614528 2688 (BN 316164995 28928 (BN 311652142 9728 (BN 310505484 24192 (BN 308695709 26112 (BL 308501945 19200) BE) (BL 311647374 3072)) (BN 312919961 27008 (BN 312023467 30080 (BL 311979332 15744) BE) (BL 313018918 31233))) (BN 320916902 19456 (BN 320465811 896 (BN 318383959 13440 (BL 317448151 18560) BE) (BL 320685475 12161)) (BN 321836006 9600 (BN 321269277 15104 (BL 321240249 13312) BE) (BL 321967636 24064)))) (BN 339948297 7040 (BN 330437626 2560 (BN 330278350 23936 (BN 329201394 7168 (BL 327070793 23296) BE) (BL 330409980 768)) (BN 332201802 6400 (BN 330678769 4992 (BL 330509777 29696) BE) (BL 333393066 26752))) (BN 344479952 22017 (BN 341361940 6272 (BN 341200697 18816 (BL 340725971 10624) BE) (BL 341471330 22784)) (BN 345321658 31232 (BL 345225862 13568) (BL 349168315 27009)))))) (BN 379701356 10880 (BN 359588374 10112 (BN 355190908 13569 (BN 351175174 0 (BN 350738901 257 (BN 350043383 25856 (BL 349799711 11520) BE) (BL 351076484 7680)) (BN 354495390 29952 (BN 354433334 20992 (BL 353606150 5632) BE) (BL 354914533 6656))) (BN 358761190 10113 (BN 357023580 1792 (BN 356733926 2304 (BL 356569319 20609) BE) (BL 357255054 30464)) (BN 359240013 31872 (BN 359181245 8449 (BL 359069239 27904) BE) (BL 359518828 32000)))) (BN 368207101 23809 (BN 363633252 29953 (BN 360008429 25345 (BN 359764757 7425 (BL 359687331 6657) BE) (BL 362869558 28416)) (BN 366293108 26368 (BN 366003454 10496 (BL 364940063 28417) BE) (BL 368030718 16256))) (BN 373382407 7937 (BN 372139086 7936 (BN 370115041 2176 (BL 368509541 640) BE) (BL 372462433 20224)) (BN 376883747 1152 (BN 374732972 3200 (BL 374081425 22400) BE) (BL 378607822 25728))))) (BN 406433170 3329 (BN 395103094 30976 (BN 386992585 12416 (BN 383350953 8064 (BN 381731961 12032 (BL 380528540 23680) BE) (BL 386875249 7424)) (BN 390398607 32257 (BN 388970884 27264 (BL 387953876 8192) BE) (BL 392850761 21120))) (BN 399668135 8961 (BN 396468124 3328 (BN 396262113 28800 (BL 396144777 23808) BE) (BL 398223159 30848)) (BN 404372622 9472 (BN 402120289 12928 (BL 401876617 30592) BE) (BL 405737652 19712)))) (BN 420050820 12033 (BN 411713164 4736 (BN 411469492 28032 (BN 411356047 13696 (BL 410988293 32385) BE) (BL 411608476 20225)) (BN 419798391 32128 (BN 419430637 385 (BL 414875514 19713) BE) (BL 419842526 3456))) (BN 437089328 15488 (BN 427819800 7296 (BN 426789727 29568 (BL 426280657 15872) BE) (BL 436059255 31616)) (BN 448545030 28033 (BL 442930526 20608) (BL 466099050 16001)))))))
def RtT8 : BTree NodeData := lf 0x3f0 [0x50008000e,0x10004]
def RtM8 : BST := BN 303650433 1408 (BN 222459291 3968 (BN 186038779 3073 (BN 174026486 1 (BN 148050217 3969 (BL 106619069 1920) (BL 171034979 1024)) (BN 181068301 1025 (BL 179725012 1152) BE)) (BN 195308307 513 (BN 192414380 128 (BL 188167356 3200) BE) (BN 208535714 3841 (BL 199266186 1793) BE))) (BN 258019788 2817 (BN 247095474 1536 (BN 231133062 512 (BL 222690718 3072) BE) (BN 255537818 3584 (BL 251868272 1537) BE)) (BN 282355246 768 (BN 273912902 3328 (BL 261137800 3585) BE) (BN 297918593 256 (BL 289885544 0) BE)))) (BN 321362305 2944 (BN 312231761 3329 (BN 307518928 641 (BN 306360937 1280 (BL 303894105 1792) (BL 307056455 257)) (BN 312092777 896 (BL 308346112 640) BE)) (BN 313369550 129 (BN 312919961 3456 (BL 312336449 3840) BE) (BN 316788456 1664 (BL 316325983 1281) BE))) (BN 358279991 1153 (BN 343553811 2816 (BN 340725971 1409 (BL 321501289 769) BE) (BN 349995499 897 (BL 349168315 3457) BE)) (BN 359588374 3712 (BN 358761190 3713 (BL 358437843 2945) BE) (BN 368030718 384 (BL 367549519 3201) BE))))
def RtL : Nat → Option (BTree NodeData) | 4 => some RtT4 | 5 => some RtT5 | 6 => some RtT6 | 7 => some RtT7 | 8 => some RtT8 | _ => none
def RtM : Nat → BST | 5 => RtM5 | 6 => RtM6 | 7 => RtM7 | 8 => RtM8 | _ => BE
end CertData

noncomputable section CertVerify
abbrev ok (f : Forest) (k : Nat) (t : BTree NodeData) := t.all (fastNodeOK f k) = true
def base0 (_ : Nat) : List Sig × Sig × Nat := ([], 0, 0)
private theorem base0_s : ∀ k, k ≠ 0 → LowerBV (base0 k).1 (base0 k).2.1 (base0 k).2.2 := fun _ _ _ _ _ _ => Nat.zero_le _
def fF1 : Forest := ⟨7,tF1,3,F1P,F1N,F1R,F1A,F1C,F1L,F1M⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F1v : graphValid fF1 base0 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F1k3 : ok fF1 3 F1T3 := by decide +kernel
private theorem F1lv : levelsChecked fF1 := by
  intro k hk tree ht; change k ≤ 3 at hk; interval_cases k
  all_goals simp [fF1,F1L] at ht
  subst ht; exact F1k3
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowF1 : LowerBV (rawOf 7) tF1 4 :=
  lower_forest fF1 base0 base0_s F1v F1lv (by decide +kernel)
def base1 : Nat → List Sig × Sig × Nat | 1 => (rawOf 7,tF1,4) | _ => ([],0,0)
private theorem base1_s : ∀ k, k ≠ 0 → LowerBV (base1 k).1 (base1 k).2.1 (base1 k).2.2 := by
  intro k _; match k with
  | 1 => exact lowF1
  | 0 | _ + 2 => exact fun _ _ _ _ => Nat.zero_le _
def fF2 : Forest := ⟨15,tF2,3,F2P,F2N,F2R,F2A,F2C,F2L,F2M⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F2v : graphValid fF2 base1 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F2k3 : ok fF2 3 F2T3 := by decide +kernel
private theorem F2lv : levelsChecked fF2 := by
  intro k hk tree ht; change k ≤ 3 at hk; interval_cases k
  all_goals simp [fF2,F2L] at ht
  subst ht; exact F2k3
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowF2 : LowerBV (rawOf 15) tF2 4 :=
  lower_forest fF2 base1 base1_s F2v F2lv (by decide +kernel)
def base2 : Nat → List Sig × Sig × Nat | 1 => (rawOf 7,tF1,4) | 2 => (rawOf 15,tF2,4) | _ => ([],0,0)
private theorem base2_s : ∀ k, k ≠ 0 → LowerBV (base2 k).1 (base2 k).2.1 (base2 k).2.2 := by
  intro k _; match k with
  | 1 => exact lowF1
  | 2 => exact lowF2
  | 0 | _ + 3 => exact fun _ _ _ _ => Nat.zero_le _
def fF3 : Forest := ⟨15,tF3,4,F3P,F3N,F3R,F3A,F3C,F3L,F3M⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F3v : graphValid fF3 base2 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F3k4 : ok fF3 4 F3T4 := by decide +kernel
private theorem F3lv : levelsChecked fF3 := by
  intro k hk tree ht; change k ≤ 4 at hk; interval_cases k
  all_goals simp [fF3,F3L] at ht
  subst ht; exact F3k4
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowF3 : LowerBV (rawOf 15) tF3 5 :=
  lower_forest fF3 base2 base2_s F3v F3lv (by decide +kernel)
def base3 : Nat → List Sig × Sig × Nat | 1 => (rawOf 7,tF1,4) | 2 => (rawOf 15,tF2,4) | 3 => (rawOf 15,tF3,5) | _ => ([],0,0)
private theorem base3_s : ∀ k, k ≠ 0 → LowerBV (base3 k).1 (base3 k).2.1 (base3 k).2.2 := by
  intro k _; match k with
  | 1 => exact lowF1
  | 2 => exact lowF2
  | 3 => exact lowF3
  | 0 | _ + 4 => exact fun _ _ _ _ => Nat.zero_le _
def fF4 : Forest := ⟨15,tF4,4,F4P,F4N,F4R,F4A,F4C,F4L,F4M⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F4v : graphValid fF4 base3 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F4k4 : ok fF4 4 F4T4 := by decide +kernel
private theorem F4lv : levelsChecked fF4 := by
  intro k hk tree ht; change k ≤ 4 at hk; interval_cases k
  all_goals simp [fF4,F4L] at ht
  subst ht; exact F4k4
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowF4 : LowerBV (rawOf 15) tF4 5 :=
  lower_forest fF4 base3 base3_s F4v F4lv (by decide +kernel)
def base4 : Nat → List Sig × Sig × Nat | 1 => (rawOf 7,tF1,4) | 2 => (rawOf 15,tF2,4) | 3 => (rawOf 15,tF3,5) | 4 => (rawOf 15,tF4,5) | _ => ([],0,0)
private theorem base4_s : ∀ k, k ≠ 0 → LowerBV (base4 k).1 (base4 k).2.1 (base4 k).2.2 := by
  intro k _; match k with
  | 1 => exact lowF1
  | 2 => exact lowF2
  | 3 => exact lowF3
  | 4 => exact lowF4
  | 0 | _ + 5 => exact fun _ _ _ _ => Nat.zero_le _
def fF5 : Forest := ⟨31,tF5,4,F5P,F5N,F5R,F5A,F5C,F5L,F5M⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F5v : graphValid fF5 base4 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F5k4 : ok fF5 4 F5T4 := by decide +kernel
private theorem F5lv : levelsChecked fF5 := by
  intro k hk tree ht; change k ≤ 4 at hk; interval_cases k
  all_goals simp [fF5,F5L] at ht
  subst ht; exact F5k4
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowF5 : LowerBV (rawOf 31) tF5 5 :=
  lower_forest fF5 base4 base4_s F5v F5lv (by decide +kernel)
def base5 : Nat → List Sig × Sig × Nat | 1 => (rawOf 7,tF1,4) | 2 => (rawOf 15,tF2,4) | 3 => (rawOf 15,tF3,5) | 4 => (rawOf 15,tF4,5) | 5 => (rawOf 31,tF5,5) | _ => ([],0,0)
private theorem base5_s : ∀ k, k ≠ 0 → LowerBV (base5 k).1 (base5 k).2.1 (base5 k).2.2 := by
  intro k _; match k with
  | 1 => exact lowF1
  | 2 => exact lowF2
  | 3 => exact lowF3
  | 4 => exact lowF4
  | 5 => exact lowF5
  | 0 | _ + 6 => exact fun _ _ _ _ => Nat.zero_le _
def fF6 : Forest := ⟨31,tF6,5,F6P,F6N,F6R,F6A,F6C,F6L,F6M⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F6v : graphValid fF6 base5 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F6k5 : ok fF6 5 F6T5 := by decide +kernel
private theorem F6lv : levelsChecked fF6 := by
  intro k hk tree ht; change k ≤ 5 at hk; interval_cases k
  all_goals simp [fF6,F6L] at ht
  subst ht; exact F6k5
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowF6 : LowerBV (rawOf 31) tF6 6 :=
  lower_forest fF6 base5 base5_s F6v F6lv (by decide +kernel)
def base6 : Nat → List Sig × Sig × Nat | 1 => (rawOf 7,tF1,4) | 2 => (rawOf 15,tF2,4) | 3 => (rawOf 15,tF3,5) | 4 => (rawOf 15,tF4,5) | 5 => (rawOf 31,tF5,5) | 6 => (rawOf 31,tF6,6) | _ => ([],0,0)
private theorem base6_s : ∀ k, k ≠ 0 → LowerBV (base6 k).1 (base6 k).2.1 (base6 k).2.2 := by
  intro k _; match k with
  | 1 => exact lowF1
  | 2 => exact lowF2
  | 3 => exact lowF3
  | 4 => exact lowF4
  | 5 => exact lowF5
  | 6 => exact lowF6
  | 0 | _ + 7 => exact fun _ _ _ _ => Nat.zero_le _
def fF7 : Forest := ⟨31,tF7,5,F7P,F7N,F7R,F7A,F7C,F7L,F7M⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7v : graphValid fF7 base6 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7k5 : ok fF7 5 F7T5 := by decide +kernel
private theorem F7lv : levelsChecked fF7 := by
  intro k hk tree ht; change k ≤ 5 at hk; interval_cases k
  all_goals simp [fF7,F7L] at ht
  subst ht; exact F7k5
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowF7 : LowerBV (rawOf 31) tF7 6 :=
  lower_forest fF7 base6 base6_s F7v F7lv (by decide +kernel)
def base7 : Nat → List Sig × Sig × Nat | 1 => (rawOf 7,tF1,4) | 2 => (rawOf 15,tF2,4) | 3 => (rawOf 15,tF3,5) | 4 => (rawOf 15,tF4,5) | 5 => (rawOf 31,tF5,5) | 6 => (rawOf 31,tF6,6) | 7 => (rawOf 31,tF7,6) | _ => ([],0,0)
private theorem base7_s : ∀ k, k ≠ 0 → LowerBV (base7 k).1 (base7 k).2.1 (base7 k).2.2 := by
  intro k _; match k with
  | 1 => exact lowF1
  | 2 => exact lowF2
  | 3 => exact lowF3
  | 4 => exact lowF4
  | 5 => exact lowF5
  | 6 => exact lowF6
  | 7 => exact lowF7
  | 0 | _ + 8 => exact fun _ _ _ _ => Nat.zero_le _
def fF8 : Forest := ⟨31,tF8,6,F8P,F8N,F8R,F8A,F8C,F8L,F8M⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F8v : graphValid fF8 base7 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F8k4 : ok fF8 4 F8T4 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F8k5 : ok fF8 5 F8T5 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F8k6 : ok fF8 6 F8T6 := by decide +kernel
private theorem F8lv : levelsChecked fF8 := by
  intro k hk tree ht; change k ≤ 6 at hk; interval_cases k
  all_goals simp [fF8,F8L] at ht
  · subst ht; exact F8k4
  · subst ht; exact F8k5
  · subst ht; exact F8k6
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowF8 : LowerBV (rawOf 31) tF8 7 :=
  lower_forest fF8 base7 base7_s F8v F8lv (by decide +kernel)
def base8 : Nat → List Sig × Sig × Nat | 1 => (rawOf 7,tF1,4) | 2 => (rawOf 15,tF2,4) | 3 => (rawOf 15,tF3,5) | 4 => (rawOf 15,tF4,5) | 5 => (rawOf 31,tF5,5) | 6 => (rawOf 31,tF6,6) | 7 => (rawOf 31,tF7,6) | 8 => (rawOf 31,tF8,7) | _ => ([],0,0)
private theorem base8_s : ∀ k, k ≠ 0 → LowerBV (base8 k).1 (base8 k).2.1 (base8 k).2.2 := by
  intro k _; match k with
  | 1 => exact lowF1
  | 2 => exact lowF2
  | 3 => exact lowF3
  | 4 => exact lowF4
  | 5 => exact lowF5
  | 6 => exact lowF6
  | 7 => exact lowF7
  | 8 => exact lowF8
  | 0 | _ + 9 => exact fun _ _ _ _ => Nat.zero_le _
def fF9 : Forest := ⟨31,tF9,6,F9P,F9N,F9R,F9A,F9C,F9L,F9M⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F9v : graphValid fF9 base8 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F9k3 : ok fF9 3 F9T3 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F9k4 : ok fF9 4 F9T4 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F9k5 : ok fF9 5 F9T5 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F9k6 : ok fF9 6 F9T6 := by decide +kernel
private theorem F9lv : levelsChecked fF9 := by
  intro k hk tree ht; change k ≤ 6 at hk; interval_cases k
  all_goals simp [fF9,F9L] at ht
  · subst ht; exact F9k3
  · subst ht; exact F9k4
  · subst ht; exact F9k5
  · subst ht; exact F9k6
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowF9 : LowerBV (rawOf 31) tF9 7 :=
  lower_forest fF9 base8 base8_s F9v F9lv (by decide +kernel)
def base9 : Nat → List Sig × Sig × Nat | 1 => (rawOf 7,tF1,4) | 2 => (rawOf 15,tF2,4) | 3 => (rawOf 15,tF3,5) | 4 => (rawOf 15,tF4,5) | 5 => (rawOf 31,tF5,5) | 6 => (rawOf 31,tF6,6) | 7 => (rawOf 31,tF7,6) | 8 => (rawOf 31,tF8,7) | 9 => (rawOf 31,tF9,7) | _ => ([],0,0)
private theorem base9_s : ∀ k, k ≠ 0 → LowerBV (base9 k).1 (base9 k).2.1 (base9 k).2.2 := by
  intro k _; match k with
  | 1 => exact lowF1
  | 2 => exact lowF2
  | 3 => exact lowF3
  | 4 => exact lowF4
  | 5 => exact lowF5
  | 6 => exact lowF6
  | 7 => exact lowF7
  | 8 => exact lowF8
  | 9 => exact lowF9
  | 0 | _ + 10 => exact fun _ _ _ _ => Nat.zero_le _
def fRt : Forest := ⟨63,tRt,8,RtP,RtN,RtR,RtA,RtC,RtL,RtM⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtv : graphValid fRt base9 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk4 : ok fRt 4 RtT4 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk5_0 : ok fRt 5 RtT5_0 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk5_1 : ok fRt 5 RtT5_1 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk5_2 : ok fRt 5 RtT5_2 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk5_3 : ok fRt 5 RtT5_3 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk5_4 : ok fRt 5 RtT5_4 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk5_5 : ok fRt 5 RtT5_5 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk5_6 : ok fRt 5 RtT5_6 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk5_7 : ok fRt 5 RtT5_7 := by decide +kernel
private theorem Rtk5 : ok fRt 5 RtT5 := by
  simp only [ok,RtT5,nd,BTree.all,Rtk5_0,Rtk5_1,Rtk5_2,Rtk5_3,Rtk5_4,Rtk5_5,Rtk5_6,Rtk5_7,Bool.and_true]
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk6_0 : ok fRt 6 RtT6_0 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk6_1 : ok fRt 6 RtT6_1 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk6_2 : ok fRt 6 RtT6_2 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk6_3 : ok fRt 6 RtT6_3 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk6_4 : ok fRt 6 RtT6_4 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk6_5 : ok fRt 6 RtT6_5 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk6_6 : ok fRt 6 RtT6_6 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk6_7 : ok fRt 6 RtT6_7 := by decide +kernel
private theorem Rtk6 : ok fRt 6 RtT6 := by
  simp only [ok,RtT6,nd,BTree.all,Rtk6_0,Rtk6_1,Rtk6_2,Rtk6_3,Rtk6_4,Rtk6_5,Rtk6_6,Rtk6_7,Bool.and_true]
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk7 : ok fRt 7 RtT7 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk8 : ok fRt 8 RtT8 := by decide +kernel
private theorem Rtlv : levelsChecked fRt := by
  intro k hk tree ht; change k ≤ 8 at hk; interval_cases k
  all_goals simp [fRt,RtL] at ht
  · subst ht; exact Rtk4
  · subst ht; exact Rtk5
  · subst ht; exact Rtk6
  · subst ht; exact Rtk7
  · subst ht; exact Rtk8
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowRt : LowerBV (rawOf 63) tRt 9 :=
  lower_forest fRt base9 base9_s Rtv Rtlv (by decide +kernel)
end CertVerify

-- ============================================================
-- 8-Variable (BitVec 256) Lifting & Target Theorem
-- ============================================================

abbrev Sig8 := BitVec 256
abbrev Row8 := Fin 256
def mk256 (w3 w2 w1 w0 : BitVec 64) : Sig8 := BitVec.append (BitVec.append w3 w2) (BitVec.append w1 w0)

def y0 : Sig8 := mk256 0xaaaaaaaaaaaaaaaa#64 0xaaaaaaaaaaaaaaaa#64 0xaaaaaaaaaaaaaaaa#64 0xaaaaaaaaaaaaaaaa#64
def y1 : Sig8 := mk256 0xcccccccccccccccc#64 0xcccccccccccccccc#64 0xcccccccccccccccc#64 0xcccccccccccccccc#64
def y2 : Sig8 := mk256 0xf0f0f0f0f0f0f0f0#64 0xf0f0f0f0f0f0f0f0#64 0xf0f0f0f0f0f0f0f0#64 0xf0f0f0f0f0f0f0f0#64
def y3 : Sig8 := mk256 0xff00ff00ff00ff00#64 0xff00ff00ff00ff00#64 0xff00ff00ff00ff00#64 0xff00ff00ff00ff00#64
def y4 : Sig8 := mk256 0xffff0000ffff0000#64 0xffff0000ffff0000#64 0xffff0000ffff0000#64 0xffff0000ffff0000#64
def y5 : Sig8 := mk256 0xffffffff00000000#64 0xffffffff00000000#64 0xffffffff00000000#64 0xffffffff00000000#64
def y6 : Sig8 := mk256 0xffffffffffffffff#64 0#64 0xffffffffffffffff#64 0#64
def y7 : Sig8 := mk256 0xffffffffffffffff#64 0xffffffffffffffff#64 0#64 0#64
def roots8 : List Sig8 := [y0, y1, y2, y3, y4, y5, y6, y7]
def t8 : Sig8 := mk256 0xfffffffefffffffa#64 0xfffffffefffffffa#64 0xfffefffefffefffa#64 0xfefefefeeeccaa00#64

def rSliceVal (r : Nat) : Nat :=
  0 + (if r.testBit 0 then 1 else 0) + (if r.testBit 1 then 2 else 0) + (if r.testBit 2 then 8 else 0) + (if r.testBit 3 then 16 else 0) + (if r.testBit 4 then 32 else 0) + (if r.testBit 5 then 128 else 0)
private theorem rSliceVal_lt (r : Row) : rSliceVal r.val < 256 := by revert r; decide +kernel
def rSlice (r : Row) : Row8 := ⟨rSliceVal r.val, rSliceVal_lt r⟩

private theorem t8_proper : properBV t8 := ⟨by decide +kernel, by decide +kernel⟩
private theorem t8_plain : plainWordBV t8 = true := by decide +kernel
private theorem roots8_plain : roots8.all plainWordBV = true := by decide +kernel
private theorem tRt_proper : properBV tRt := ⟨by decide +kernel, by decide +kernel⟩
private theorem slice_eq : restrictRows rSlice (observeBV t8) = observeBV tRt :=
  funext fun r => by revert r; decide +kernel

private theorem slice_covered : ∀ a ∈ roots8, Available ((rawOf 63).map observeBV) (restrictRows rSlice (observeBV a)) := by
  intro a ha
  simp only [roots8, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine Or.inl ?_
    have hmem : x0 ∈ rawOf 63 := by decide +kernel
    have heq : restrictRows rSlice (observeBV y0) = observeBV x0 :=
      funext fun r => by revert r; decide +kernel
    exact heq ▸ List.mem_map_of_mem hmem
  · refine Or.inl ?_
    have hmem : x1 ∈ rawOf 63 := by decide +kernel
    have heq : restrictRows rSlice (observeBV y1) = observeBV x1 :=
      funext fun r => by revert r; decide +kernel
    exact heq ▸ List.mem_map_of_mem hmem
  · exact Or.inr (Or.inl ⟨false, funext fun r => by revert r; decide +kernel⟩)
  · refine Or.inl ?_
    have hmem : x2 ∈ rawOf 63 := by decide +kernel
    have heq : restrictRows rSlice (observeBV y3) = observeBV x2 :=
      funext fun r => by revert r; decide +kernel
    exact heq ▸ List.mem_map_of_mem hmem
  · refine Or.inl ?_
    have hmem : x3 ∈ rawOf 63 := by decide +kernel
    have heq : restrictRows rSlice (observeBV y4) = observeBV x3 :=
      funext fun r => by revert r; decide +kernel
    exact heq ▸ List.mem_map_of_mem hmem
  · refine Or.inl ?_
    have hmem : x4 ∈ rawOf 63 := by decide +kernel
    have heq : restrictRows rSlice (observeBV y5) = observeBV x4 :=
      funext fun r => by revert r; decide +kernel
    exact heq ▸ List.mem_map_of_mem hmem
  · exact Or.inr (Or.inl ⟨false, funext fun r => by revert r; decide +kernel⟩)
  · refine Or.inl ?_
    have hmem : x5 ∈ rawOf 63 := by decide +kernel
    have heq : restrictRows rSlice (observeBV y7) = observeBV x5 :=
      funext fun r => by revert r; decide +kernel
    exact heq ▸ List.mem_map_of_mem hmem

def singles8 : Finset Sig8 := {y2, y6}

private theorem singles8_card : singles8.card = 2 := by decide +kernel

private theorem singles8_ess : ∀ a ∈ singles8, EssentialBV t8 roots8 a := by
  intro a ha
  simp only [singles8, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl
  · refine ⟨⟨32, by decide⟩, ⟨36, by decide⟩, by decide +kernel, ?_⟩
    intro w hw hne
    simp only [roots8, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · decide +kernel
    · exact (hne rfl).elim
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
  · refine ⟨⟨1, by decide⟩, ⟨65, by decide⟩, by decide +kernel, ?_⟩
    intro w hw hne
    simp only [roots8, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact (hne rfl).elim
    · decide +kernel

private theorem singles8_const : ∀ a ∈ singles8, Constant (restrictRows rSlice (observeBV a)) := by
  intro a ha
  simp only [singles8, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl
  · exact ⟨false, funext fun r => by revert r; decide +kernel⟩
  · exact ⟨false, funext fun r => by revert r; decide +kernel⟩

private theorem low8 : LowerBV roots8 t8 11 := by
  have h := lowerBV_slice t8_proper t8_plain roots8_plain tRt_proper rSlice slice_eq slice_covered
    singles8 singles8_ess singles8_const 9 lowRt
  rw [singles8_card] at h; exact h

def targetFun8 (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2,
    (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧
    (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)

def smallGates : List Gate :=
  [⟨.or, [0, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [5, 10]⟩, ⟨.and, [3, 11]⟩, ⟨.and, [1, 9]⟩, ⟨.and, [8, 12]⟩, ⟨.and, [4, 7]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [17, 15]⟩, ⟨.or, [18, 16]⟩]
def smallOut : ℕ := 19

private theorem witnessMono : ∀ g ∈ smallGates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg; simp only [smallGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl, by decide⟩ | exact ⟨Or.inr rfl, by decide⟩

private theorem target_eq_or (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2,
      ([b0, b1, b2, b3, b4, b5, b6, b7] : List Bool).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧
      ([b0, b1, b2, b3, b4, b5, b6, b7] : List Bool).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) =
    ((b0 && b3) || ((b1 && b4) || ((b0 && b5) || ((b1 && b5) || ((b2 && b5) || ((b0 && b6) || ((b2 && b6) || ((b3 && b6) || ((b0 && b7) || ((b2 && b7) || ((b3 && b7) || (b4 && b7)))))))))))) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  simp only [Bool.or_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨i, hi, h1, h2⟩
    have hi2 : i < 12 := hi
    match i, hi2 with
    | 0, _ => exact Or.inl ⟨h1, h2⟩
    | 1, _ => exact Or.inr (Or.inl ⟨h1, h2⟩)
    | 2, _ => exact Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))
    | 3, _ => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))
    | 4, _ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))
    | 5, _ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))))
    | 6, _ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))))
    | 7, _ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))))))
    | 8, _ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))))))
    | 9, _ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))))))))
    | 10, _ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))))))))
    | 11, _ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨h1, h2⟩)))))))))))
    | _ + 12, hlt => omega
  · intro h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨0, by decide, h1, h2⟩
    · exact ⟨1, by decide, h1, h2⟩
    · exact ⟨2, by decide, h1, h2⟩
    · exact ⟨3, by decide, h1, h2⟩
    · exact ⟨4, by decide, h1, h2⟩
    · exact ⟨5, by decide, h1, h2⟩
    · exact ⟨6, by decide, h1, h2⟩
    · exact ⟨7, by decide, h1, h2⟩
    · exact ⟨8, by decide, h1, h2⟩
    · exact ⟨9, by decide, h1, h2⟩
    · exact ⟨10, by decide, h1, h2⟩
    · exact ⟨11, by decide, h1, h2⟩

private theorem witnessCorrectFast : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    Circuit.eval ⟨smallGates, smallOut⟩ [b0, b1, b2, b3, b4, b5, b6, b7] = ((b0 && b3) || ((b1 && b4) || ((b0 && b5) || ((b1 && b5) || ((b2 && b5) || ((b0 && b6) || ((b2 && b6) || ((b3 && b6) || ((b0 && b7) || ((b2 && b7) || ((b3 && b7) || (b4 && b7)))))))))))) := by
  decide +kernel
private theorem witnessCorrect (x : Fin 8 → Bool) : Circuit.eval ⟨smallGates, smallOut⟩ (List.ofFn x) = targetFun8 x := by
  rw [targetFun8, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ,
      List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero,
      target_eq_or]
  exact witnessCorrectFast (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)

def sample8 (r : Row8) (i : Fin 8) : Bool := bitBV r (roots8.getD i.val zeroBV)
private theorem roots8_list : List.ofFn (fun i : Fin 8 => roots8.getD i.val zeroBV) = roots8 := rfl
private theorem sample8_eq (r : Row8) :
    List.ofFn (sample8 r) = (roots8.map observeBV).map (fun f => f r) := by
  rw [← roots8_list, List.map_map, List.map_ofFn]; rfl
private theorem t8_eq_expr : ((y0 &&& y3) ||| ((y1 &&& y4) ||| ((y0 &&& y5) ||| ((y1 &&& y5) ||| ((y2 &&& y5) ||| ((y0 &&& y6) ||| ((y2 &&& y6) ||| ((y3 &&& y6) ||| ((y0 &&& y7) ||| ((y2 &&& y7) ||| ((y3 &&& y7) ||| (y4 &&& y7)))))))))))) = t8 := by decide +kernel
private theorem sample8_target (r : Row8) : targetFun8 (sample8 r) = observeBV t8 r := by
  rw [targetFun8, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ,
      List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero,
      target_eq_or, ← t8_eq_expr]
  simp only [sample8, roots8, observeBV, bitBV, BitVec.getLsbD_or, BitVec.getLsbD_and]; rfl

private theorem mainProof (gates : List Gate) (o : ℕ)
    (hfit : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (_hone : ∀ i j : Fin gates.length, (gates.get i).op = GateOp.not → (gates.get j).op = GateOp.not → i = j)
    (hEval : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = targetFun8 x) :
    ∃ (gates' : List Gate) (o' : ℕ),
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧
      ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = targetFun8 x := by
  classical
  by_cases big : 12 ≤ gates.length
  · have hlen : smallGates.length = 12 := rfl
    exact ⟨smallGates, smallOut, witnessMono, by omega, witnessCorrect⟩
  by_cases mono : ∀ g ∈ gates, g.op ≠ GateOp.not
  · refine ⟨gates, o, ?_, Nat.le_refl _, hEval⟩
    intro g hg; obtain ⟨ops, ar⟩ := hfit g hg; refine ⟨?_, ar⟩
    rcases ops with a | b | c
    · exact Or.inl a
    · exact Or.inr b
    · exact (mono g hg c).elim
  push Not at mono
  obtain ⟨g, hg, hop⟩ := mono
  have hlt : gates.countP (fun q => !isNot q) < gates.length := by
    rcases Nat.lt_or_ge (gates.countP (fun q => !isNot q)) gates.length with h1 | h1
    · exact h1
    · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h1) g hg
      simp [isNot, hop] at eq
  obtain ⟨q, bank, hq, hreach, hsup⟩ := circuit_reach (roots8.map observeBV) gates (roots8.map observeBV)
    0 (roots8.map observeBV) hfit Reach.start (fun a ha => Or.inl ha)
  have hout : (execWires gates (roots8.map observeBV)).getD o (fun _ => false) = observeBV t8 := by
    funext r
    have hev := execWires_at gates (roots8.map observeBV) r
    have hr1 : ((execWires gates (roots8.map observeBV)).getD o (fun _ => false)) r =
        ((execWires gates (roots8.map observeBV)).map (fun f => f r)).getD o false := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
      cases (execWires gates (roots8.map observeBV))[o]? <;> rfl
    rw [hr1, hev, ← sample8_eq r]
    exact (hEval (sample8 r)).trans (sample8_target r)
  have havail : Available bank (observeBV t8) := hout ▸ avail_getD hsup o
  have hlb := low8 q bank hreach havail
  omega

end PEqualNP.Outside.L_meta_14714

open PEqualNP.Outside.L_meta_14714 in
theorem PEqualNP.Outside.L_meta_14714 :
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ),
      (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) →
      (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
      (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) →
      ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ),
        (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧
        gates'.length ≤ gates.length ∧
        ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  mainProof
