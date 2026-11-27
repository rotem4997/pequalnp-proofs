import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_15253
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
  let n := v % 1000000000000037
  ((((n * n) % 1000000000000037 + 971) * (n + 1)) + 7) % 1000000000000037

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
def tF1 : Sig := 0xeac8eac8eac8eac8#64
def F1P : List Row := mkRows [3,3,3,6,6,6,9,9,9]
def F1N : List Row := mkRows [5,10,12,5,10,12,5,10,12]
def F1R : List (Nat × Nat) := [(455,73),(63,146),(56,365),(448,438)]
def F1A : List (List Nat) := [[0,1,2,3,4,5],[1,0,3,2,4,5]]
def F1C : List CutSpec := [⟨0,10,1,0,0,[0,1,2,3,4,5],0xcc00cc00cc00cc00#64⟩,⟨0,5,1,0,0,[0,1,2,3,4,5],0xa0a0a0a0a0a0a0a0#64⟩,⟨0,4,2,0,0,[0,1,2,3,4,5],0xf0f0f0f0f0f0f0f0#64⟩,⟨4,0,2,0,0,[0,1,2,3,4,5],0xf0f0f0f0f0f0f0f#64⟩,⟨0,8,2,0,0,[0,1,2,3,4,5],0xff00ff00ff00ff00#64⟩,⟨8,0,2,0,0,[0,1,2,3,4,5],0xff00ff00ff00ff#64⟩]
def F1T3 : BTree NodeData := lf 0xf0 [0x300020001,0x600050004]
def F1L : Nat → Option (BTree NodeData) | 3 => some F1T3 | _ => none
def F1M : Nat → BST | _ => BE
def tF2 : Sig := 0xeaa8eaa8eaa8eaa8#64
def F2P : List Row := mkRows [3,3,3,3,5,5,5,5,9,9,9,9,14,14,14,14]
def F2N : List Row := mkRows [1,6,10,12,1,6,10,12,1,6,10,12,1,6,10,12]
def F2R : List (Nat × Nat) := [(4095,4369),(61455,26214),(61680,43690),(65280,52428)]
def F2A : List (List Nat) := [[0,1,2,3,4,5],[0,1,3,2,4,5],[0,2,1,3,4,5],[0,2,3,1,4,5],[0,3,1,2,4,5],[0,3,2,1,4,5]]
def F2C : List CutSpec := [⟨2,0,2,0,0,[0,1,2,3,4,5],0x3333333333333333#64⟩,⟨0,2,2,0,0,[0,1,2,3,4,5],0xcccccccccccccccc#64⟩,⟨0,4,2,0,0,[0,1,2,3,4,5],0xf0f0f0f0f0f0f0f0#64⟩,⟨4,0,2,0,0,[0,1,2,3,4,5],0xf0f0f0f0f0f0f0f#64⟩,⟨0,8,2,0,0,[0,1,2,3,4,5],0xff00ff00ff00ff00#64⟩,⟨8,0,2,0,0,[0,1,2,3,4,5],0xff00ff00ff00ff#64⟩,⟨0,6,1,0,0,[0,1,2,3,4,5],0xc0c0c0c0c0c0c0c0#64⟩,⟨0,10,1,0,0,[0,1,2,3,4,5],0xcc00cc00cc00cc00#64⟩,⟨6,0,1,0,0,[0,1,2,3,4,5],0x303030303030303#64⟩,⟨10,0,1,0,0,[0,1,2,3,4,5],0x33003300330033#64⟩]
def F2T2 : BTree NodeData := lf 0x3544842100493 []
def F2T3 : BTree NodeData := nd (nd (nd (lf 0x90810002a2 []) (nd (lf 0x50810002b2 [0x1]) (lf 0x90810002b2 []))) (nd (lf 0xd0910002a2 []) (nd (lf 0x10910002b2 [0x2]) (lf 0xd0910002b2 [])))) (nd (nd (lf 0xc4210003c2 []) (nd (lf 0x4842100392 [0x20001]) (lf 0x50221002e2 [0x2]))) (nd (nd (lf 0x90221002e2 [0x1]) (lf 0xc862100392 [])) (nd (lf 0x50e2100272 [0x1]) (lf 0x90e2100272 [0x3]))))
def F2M3 : BST := BL 1671469066263839 0
def F2T4 : BTree NodeData := nd (nd (nd (lf 0x10001e1 [0x400030001,0x60005]) (lf 0x10001f1 [0x20001])) (nd (lf 0x110001e1 [0x300040002,0x50006]) (nd (lf 0x110001f1 [0x10002]) (lf 0x210001e1 [0x80007])))) (nd (nd (lf 0x210001f1 [0x10002]) (nd (lf 0x310001e1 [0xa0009]) (lf 0x310001f1 [0x20001]))) (nd (lf 0x21001f1 [0x10007]) (nd (lf 0x121001f1 [0x20009]) (lf 0x221001f1 [0x30001]))))
def F2M4 : BST := BN 1695917165175473 384 (BN 1448106942864208 1920 (BN 1339726502085352 513 (BN 1168416125708215 257 (BL 1165912605495375 0) BE) (BL 1370192360971775 512)) (BN 1586197312059125 769 (BN 1527745720882674 1793 (BL 1525242200669834 1536) BE) (BL 1624448544111604 256))) (BN 1998632568957118 1408 (BN 1899437874746430 1664 (BN 1861439416453762 896 (BL 1775824409777194 1) BE) (BL 1983778139286063 1792)) (BN 2135154004951653 1537 (BN 2070756761754928 640 (BL 2013386897751135 768) BE) (BL 2153925130113838 128)))
def F2T5 : BTree NodeData := lf 0xf0 []
def F2M5 : BST := BN 2381789904821813 516 (BN 2154151244470290 260 (BN 1992785313683018 512 (BN 1913849805913882 1794 (BN 1633455718508559 0 (BL 1605382551161430 1792) BE) (BL 1964712146335889 128)) (BN 2148893483689956 258 (BN 2043601718958801 642 (BL 2022460309647354 4) BE) (BL 2149916179378004 640))) (BN 2273179401088341 130 (BN 2261906549584486 899 (BN 2251380157125254 256 (BL 2157974267111735 896) BE) (BL 2262085572387455 2)) (BN 2330847490138128 1920 (BL 2308828505441880 387) (BL 2338034232186933 1925)))) (BN 2581515705613191 1796 (BN 2509245774552463 1664 (BN 2496597451685941 1922 (BN 2432520777665644 644 (BL 2402931314133260 1666) BE) (BL 2508223078864415 770)) (BN 2541441375105068 897 (BL 2513480839644749 772) (BL 2546133938489891 1921))) (BN 2791850372840103 1668 (BN 2647010034978962 1923 (BN 2621415167561914 514 (BL 2610709752299713 768) BE) (BL 2741594867510144 384)) (BN 2909517483403947 385 (BL 2798008330942426 1924) (BL 2940845300787650 132))))
def F2L : Nat → Option (BTree NodeData) | 2 => some F2T2 | 3 => some F2T3 | 4 => some F2T4 | 5 => some F2T5 | _ => none
def F2M : Nat → BST | 3 => F2M3 | 4 => F2M4 | 5 => F2M5 | _ => BE
def tF3 : Sig := 0xeaa8c888eaa8c888#64
def F3P : List Row := mkRows [3,3,3,3,3,14,14,14,14,14,21,21,21,21,21,25,25,25,25,25]
def F3N : List Row := mkRows [13,17,22,26,28,13,17,22,26,28,13,17,22,26,28,13,17,22,26,28]
def F3R : List (Nat × Nat) := [(1047583,101475),(1023,405900),(32736,710325),(1016800,845625),(1047552,1014750)]
def F3A : List (List Nat) := [[0,1,2,3,4,5],[0,1,3,2,4,5]]
def F3C : List CutSpec := [⟨0,16,6,2,0,[0,1,2,3,4,5],0xffff0000ffff0000#64⟩]
def F3T6 : BTree NodeData := lf 0x1f0 [0x1]
def F3L : Nat → Option (BTree NodeData) | 6 => some F3T6 | _ => none
def F3M : Nat → BST | _ => BE
def tRt : Sig := 0xeaa8c888c8888888#64
def RtP : List Row := mkRows [3,3,3,3,3,3,3,30,30,30,30,30,30,30,46,46,46,46,46,46,46,53,53,53,53,53,53,53,57,57,57,57,57,57,57]
def RtN : List Row := mkRows [14,29,45,49,54,58,60,14,29,45,49,54,58,60,14,29,45,49,54,58,60,14,29,45,49,54,58,60,14,29,45,49,54,58,60]
def RtR : List (Nat × Nat) := [(34357641343,3787687694),(2097151,13256906929),(268435328,23537773527),(34093399936,27866559463),(34357657472,33006992762),(34359721984,33548091004)]
def RtA : List (List Nat) := [[0,1,2,3,4,5],[0,1,2,3,5,4],[0,1,3,2,4,5],[0,1,3,2,5,4],[1,0,4,5,2,3],[1,0,4,5,3,2],[1,0,5,4,2,3],[1,0,5,4,3,2]]
def RtC : List CutSpec := [⟨0,8,7,3,0,[1,0,4,5,2,3],0xff00ff00ff00ff00#64⟩,⟨0,32,7,3,0,[0,1,2,3,4,5],0xffffffff00000000#64⟩,⟨16,2,3,0,0,[0,1,2,3,4,5],0xcccc0000cccc#64⟩,⟨8,0,4,0,0,[0,1,2,3,4,5],0xff00ff00ff00ff#64⟩,⟨17,0,3,0,0,[0,1,2,3,4,5],0x555500005555#64⟩,⟨32,2,3,0,0,[0,1,2,3,4,5],0xcccccccc#64⟩,⟨2,1,3,0,0,[0,1,2,3,4,5],0x2222222222222222#64⟩,⟨4,0,4,0,0,[0,1,2,3,4,5],0xf0f0f0f0f0f0f0f#64⟩,⟨1,0,4,0,0,[0,1,2,3,4,5],0x5555555555555555#64⟩,⟨32,0,4,0,0,[0,1,2,3,4,5],0xffffffff#64⟩,⟨1,48,2,0,0,[0,1,2,3,4,5],0x5555000000000000#64⟩,⟨1,2,3,0,0,[0,1,2,3,4,5],0x4444444444444444#64⟩,⟨0,4,7,3,0,[1,0,5,4,2,3],0xf0f0f0f0f0f0f0f0#64⟩,⟨2,12,2,0,0,[0,1,2,3,4,5],0x3000300030003000#64⟩,⟨0,33,3,0,0,[0,1,2,3,4,5],0xaaaaaaaa00000000#64⟩,⟨0,48,6,2,0,[0,1,2,3,4,5],0xffff000000000000#64⟩,⟨0,16,7,3,0,[0,1,2,3,5,4],0xffff0000ffff0000#64⟩,⟨0,2,4,0,0,[0,1,2,3,4,5],0xcccccccccccccccc#64⟩,⟨2,0,4,0,0,[0,1,2,3,4,5],0x3333333333333333#64⟩,⟨6,0,3,0,0,[0,1,2,3,4,5],0x303030303030303#64⟩,⟨2,16,3,0,0,[0,1,2,3,4,5],0x3333000033330000#64⟩,⟨16,0,4,0,0,[0,1,2,3,4,5],0xffff0000ffff#64⟩,⟨10,0,3,0,0,[0,1,2,3,4,5],0x33003300330033#64⟩,⟨2,32,3,0,0,[0,1,2,3,4,5],0x3333333300000000#64⟩,⟨0,1,4,0,0,[0,1,2,3,4,5],0xaaaaaaaaaaaaaaaa#64⟩,⟨32,18,2,0,0,[0,1,2,3,4,5],0xcccc0000#64⟩,⟨0,13,2,0,0,[0,1,2,3,4,5],0xa000a000a000a000#64⟩,⟨0,6,3,0,0,[0,1,2,3,4,5],0xc0c0c0c0c0c0c0c0#64⟩,⟨16,32,3,0,0,[0,1,2,3,4,5],0xffff00000000#64⟩,⟨8,1,3,0,0,[0,1,2,3,4,5],0xaa00aa00aa00aa#64⟩,⟨16,4,3,0,0,[0,1,2,3,4,5],0xf0f00000f0f0#64⟩,⟨0,20,4,1,0,[0,1,4,2,5,3],0xf0f00000f0f00000#64⟩,⟨0,5,2,0,0,[0,1,2,3,4,5],0xa0a0a0a0a0a0a0a0#64⟩,⟨33,0,3,0,0,[0,1,2,3,4,5],0x55555555#64⟩,⟨4,1,3,0,0,[0,1,2,3,4,5],0xa0a0a0a0a0a0a0a#64⟩,⟨33,16,2,0,0,[0,1,2,3,4,5],0x55550000#64⟩,⟨1,4,3,0,0,[0,1,2,3,4,5],0x5050505050505050#64⟩,⟨4,8,3,0,0,[0,1,2,3,4,5],0xf000f000f000f00#64⟩]
def RtT4 : BTree NodeData := nd (nd (nd (lf 0x1d26244010032a4 [0x5020a01]) (nd (lf 0x98f21d001003a04 [0x4040f020803]) (lf 0x18c410811003a04 [0x20400060805]))) (nd (nd (lf 0x9cc62d011003224 [0xa080f020007,0x809]) (lf 0x19672d0110030a4 [0x60a00030f01])) (nd (lf 0x9d66418a1003084 [0xf01000b]) (lf 0x9d6640821003084 [0xf01000b])))) (nd (nd (nd (lf 0xa1462d021002884 [0xf01000b]) (lf 0x99272c421003284 [0xf01000c0007,0xf02])) (nd (lf 0x21176c421002ac4 [0x2020f0d]) (lf 0x99673d002003024 [0xb]))) (nd (nd (lf 0xa0e76c874002a04 [0xf02000e]) (lf 0x61e6518740020e4 [0xf0d0a10000f,0xf01])) (nd (lf 0x9ce62d874003224 [0x70f020003]) (lf 0x9d662d8740030a4 [0x50a00030f01]))))
def RtT5_0 := nd (nd (nd (nd (lf 0x261c841001b83 [0x7020711000e]) (nd (lf 0x263c841001b23 [0x412000e]) (lf 0x176c8410013a3 [0x1307020003,0xa000c0701]))) (nd (lf 0x2729841001b83 [0x711000c000e,0x702]) (nd (lf 0x2629841001b83 [0x70207110014,0x701]) (lf 0x2649841001ac3 [0x70d07020015,0x701])))) (nd (nd (lf 0x27298410013a3 [0x70100080013,0x1607020711,0xa]) (nd (lf 0x2639881001b23 [0x70207110014,0x17]) (lf 0x2649881001aa3 [0x70107020015,0x14]))) (nd (nd (lf 0x26599010018e3 [0x70d00180015,0x701]) (lf 0x2624401001ba3 [0x50100090711,0x10d05020201])) (nd (lf 0x7444010016e3 [0x6010019070d,0x10200060602,0x160211]) (lf 0x37644010013e3 [0x130711070d,0x1600010012,0x2000a]))))) (nd (nd (nd (lf 0x2618401001bc3 [0x70d0007000c,0x711]) (nd (lf 0x2628401001ba3 [0x70100070412,0x711]) (lf 0x321d001001e83 [0x70107020007,0x1b001a0003]))) (nd (nd (lf 0x262d001001aa3 [0x70107020007,0x20d0208]) (lf 0x265d0010018e3 [0x701070d0007,0x302020a])) (nd (lf 0x176d0010012e3 [0x7020007001a]) (lf 0x27498010012e3 [0x1607020012,0x701070d])))) (nd (nd (lf 0x2639881001b33 [0x301050d0007,0x71100130009]) (nd (lf 0x2649881001ab3 [0x9000c0007,0x70207010013]) (lf 0x6510510018e3 [0x70d0413001a,0x1020701]))) (nd (nd (lf 0x27610510012e3 [0x1207020007,0x701070d]) (lf 0x62d851001b83 [0x7010711001c,0x702])) (nd (lf 0x631891001b23 [0x50d07020003,0x41403010711,0x217]) (lf 0x641891001aa3 [0x30701001c,0x702])))))
def RtT5_1 := nd (nd (nd (nd (lf 0x27519110018e3 [0x70d0711001d,0x20701]) (nd (lf 0x6519110018e3 [0x701070d0003,0x5110006]) (lf 0x628411001b93 [0x70100070409,0x711]))) (nd (lf 0x410811001e83 [0x70100050007,0x6001e0702,0xb000e]) (nd (lf 0x630811001b23 [0x7110204000c,0x301010702,0x6]) (lf 0x640811001aa3 [0x70207010005,0x1600070006])))) (nd (nd (lf 0x27608110013a3 [0xc000e]) (nd (lf 0x62d011001aa3 [0x70107020003,0x208]) (lf 0x272d0110016a3 [0x70107020003,0x1f000e000b]))) (nd (nd (lf 0x65d0110018e3 [0x701070d0003,0x510020a]) (lf 0x631891001b33 [0x50d00120007,0x30107110019])) (nd (lf 0x641891001ab3 [0x120007000c,0x70207010019]) (lf 0x26418a1001a83 [0x701000b]))))) (nd (nd (nd (lf 0x27418a1001683 [0x1207020701]) (nd (lf 0x2729921001683 [0x701000b]) (lf 0x264c861001a83 [0x70207010003]))) (nd (nd (lf 0x17610610012e3 [0x70d07020007,0x701]) (lf 0x7458610012e3 [0x120702070d,0x160701])) (nd (lf 0x1719921001ac3 [0x701070d000b]) (lf 0x27599210018e3 [0x7020701070d,0x31100160711])))) (nd (nd (lf 0x2640821001a83 [0x701000b]) (nd (lf 0x2740821001683 [0x907020701]) (lf 0x62d021001a83 [0x701000b]))) (nd (nd (lf 0x272d021001683 [0x701000b]) (lf 0x176d021001ac3 [0x70d07020005,0x701])) (nd (lf 0x176d0210016c3 [0x70d07020005,0x701]) (lf 0x176d0210012d3 [0x70d07020005,0x701])))))
def RtT5_2 := nd (nd (nd (nd (lf 0x2729821001393 [0x900080701,0x7020711]) (nd (lf 0x27498210012d3 [0x90701070d,0x160702]) (lf 0x27418a1001293 [0x70207010009]))) (nd (lf 0x2709921001ac3 [0x701070d000b]) (nd (lf 0x2729921001293 [0x701000b]) (lf 0x272c421001783 [0x7110701000c,0x702])))) (nd (nd (lf 0x176c421001bc3 [0x2010711070d,0x202]) (nd (lf 0x2640821001aa3 [0x70701000b,0x200006]) (lf 0x271d0210016c3 [0x70d07020007,0x701]))) (nd (nd (lf 0x272d0210016a3 [0x70200070003]) (lf 0x176d0210012e3 [0x70d07020015,0x701])) (nd (lf 0x27298210013b3 [0x701000c0007,0x7110013]) (lf 0x264c861001a93 [0x70701001a,0x200211]))))) (nd (nd (nd (lf 0x7258610013b3 [0x7010007000c,0x711]) (nd (lf 0x27018a10013a3 [0x70100090012,0x7020711]) (lf 0x17118a1001393 [0x900120701,0x7020711]))) (nd (nd (lf 0x27418a10012b3 [0x70100090006,0x7020016]) (lf 0x27299210012b3 [0xb0007001a])) (nd (lf 0x273d002001623 [0x30007000b]) (lf 0x265d0020018a3 [0x21000b0701])))) (nd (nd (lf 0x176d0020012a3 [0x70200200701,0x7]) (nd (lf 0x176d002001aa3 [0x7010007000b,0x5]) (lf 0x176d0020016a3 [0x90702001b,0x7]))) (nd (nd (lf 0x176d0020012b3 [0x7010007000c,0x70200190009]) (lf 0x264cc42001a13 [0x702000c])) (nd (lf 0x176cc42001313 [0x7020711000c]) (lf 0x17010420016a3 [0x702000c001b,0xe])))))
def RtT5_3 := nd (nd (nd (nd (lf 0x2731042001633 [0x1a00050007,0x60d0702001e]) (nd (lf 0x17610420012b3 [0x701000c0007,0x702]) (lf 0x745842001a93 [0x1200050701,0x702]))) (nd (nd (lf 0x2635842001b13 [0x30107020005,0x220711]) (lf 0x263c874001e03 [0xb07020003,0x701])) (nd (lf 0x176c874001a83 [0x7010003]) (lf 0x276c874001a83 [0x3000e])))) (nd (nd (lf 0x275c8740014a3 [0xe07010003,0x702]) (nd (lf 0x176c8740012a3 [0x7010003]) (lf 0x27118740016c3 [0x70d07020003,0x701]))) (nd (nd (lf 0x27218740016a3 [0x70107020003,0x70d0108]) (lf 0x26518740018e3 [0x701070d0007,0xf])) (nd (lf 0x27518740014e3 [0x701070d0019,0x10a01130302]) (lf 0x2625874001a83 [0x701000b]))))) (nd (nd (nd (lf 0x3765874001ac3 [0x70d07020007,0x701]) (nd (lf 0x2625874001aa3 [0x70200070003]) (lf 0x2729874001683 [0x7020003]))) (nd (nd (lf 0x17698740016c3 [0x70d0007000b,0x701]) (lf 0x26598740018e3 [0x70d00070003,0x701])) (nd (lf 0x262d874001aa3 [0x70107020003,0x1f000e000b]) (lf 0x272d8740016a3 [0x70107020003,0x108])))) (nd (nd (lf 0x275d8740014e3 [0x701070d0003,0x702010a]) (nd (lf 0x26398b4001a23 [0x70003000b]) (lf 0x262d4340018a3 [0x2307010007]))) (nd (nd (lf 0x270c8740016a3 [0x70107020003,0x5]) (lf 0x263c874001a33 [0x70200030007,0x24050d0701])) (nd (lf 0x176c8740012b3 [0x70100030007,0x230702]) (lf 0x2729874001a93 [0x307020007,0x701])))))
def RtT5 : BTree NodeData := nd (nd RtT5_0 RtT5_1) (nd RtT5_2 RtT5_3)
def RtM5 : BST := BN 1809096800969043 1536 (BN 1388567732593248 896 (BN 1053426579748851 1664 (BN 982774121890434 258 (BN 938709927483900 128 (BL 840859506804705 768) BE) (BL 1027868281165623 1792)) (BN 1112433419301885 1920 (BL 1060854219821906 898) (BL 1321105699748437 1280))) (BN 1598640489661341 1152 (BN 1576627124615531 0 (BL 1488826032268640 1) (BL 1578219005934539 384)) (BN 1655274115423054 1922 (BL 1643143470163483 514) (BL 1705994073757967 1537)))) (BN 2197945066559110 1793 (BN 2132126743962861 1542 (BN 1863946395869606 1282 (BL 1815365688239599 512) (BL 1952804403703613 256)) (BN 2164908771422283 1153 (BL 2147428378827046 1540) (BL 2186538928897350 2))) (BN 2380972817083194 1408 (BN 2301456631454913 641 (BL 2238942008586711 769) (BL 2309412878441020 516)) (BN 2747102464646723 517 (BL 2439382270357626 129) (BL 2870441031105729 640))))
def RtT6_0 := nd (nd (nd (nd (nd (lf 0xc841000fa2 [0x3020003000e,0x60311]) (lf 0x9841000bc2 [0x30d03020311,0x130301])) (nd (lf 0x9841000fc2 [0x30203110013,0x301030d]) (lf 0x9841000be2 [0x30203110013,0x301030d]))) (nd (nd (lf 0x9881000ba2 [0x30103020311,0xd00080013,0x30d]) (lf 0x9881000fa2 [0x30203110014,0x10d0301])) (nd (lf 0x9901000ae2 [0x30d00030302,0x1500130301]) (nd (lf 0x9901000ee2 [0x30d03020015,0x1110301]) (lf 0x4401000fe2 [0x190311030d,0x10102010009,0x602020003,0x102]))))) (nd (nd (nd (lf 0x8401000fe2 [0x30d00070003,0x30203010311,0x6]) (lf 0xd001000ee2 [0x30d03020007,0x190301])) (nd (lf 0x9801000be2 [0x30203110012,0x301030d]) (nd (lf 0x9801000bf2 [0x900120007,0x190311030d]) (lf 0x9881000bb2 [0x30203110301,0x90023010d,0xc00080013,0x25])))) (nd (nd (lf 0x9881000fb2 [0x301000c0007,0x1300090311,0x23010d0302]) (lf 0x1051000ee2 [0x301030d001a,0x302])) (nd (lf 0xd851000fc2 [0x311030d0012,0x3020301]) (nd (lf 0x1891000fa2 [0x3010311001c,0x10d0302]) (lf 0x1911000ae2 [0x3010302030d,0x1100160012,0x311])))))) (nd (nd (nd (nd (lf 0x1911000ee2 [0x302030d0003,0x1110301]) (lf 0x8411000fd2 [0x30d00070009,0x30203010311])) (nd (lf 0x811000fa2 [0x3110301000c,0x300090302,0x6]) (nd (lf 0xd011000ee2 [0x30d03020003,0x1100130301]) (lf 0x1891000bb2 [0x30203110301,0x120007010d,0xc00190008,0x9001c])))) (nd (nd (lf 0x1891000fb2 [0x3010007000c,0x1900120311,0x10d0302]) (lf 0x18a1000f82 [0x31103010012,0x302])) (nd (lf 0x9921000ec2 [0x301030d000b,0x703110302]) (nd (lf 0xc861000f82 [0x31103010012,0x302]) (lf 0x1061000ee2 [0x3020007001a,0x111]))))) (nd (nd (nd (lf 0x5861000be2 [0x311030d0012,0x3020301]) (lf 0x9921000ae2 [0x301030d001a,0x700110302,0x311])) (nd (lf 0x9921000ee2 [0x3020007001a,0x111]) (nd (lf 0x821000f82 [0x31103010009,0x302]) (lf 0xd021000ec2 [0x301030d000b,0x70302])))) (nd (nd (lf 0xd021000ed2 [0x30d0019000b,0x11103020301]) (lf 0x9821000bd2 [0x301030d0009,0x3020311])) (nd (lf 0x18a1000b92 [0x31103010009,0x302]) (nd (lf 0x9921000ad2 [0x301030d000b,0x1103110302]) (lf 0x9921000ed2 [0x1110007000b,0x301030d]))))))
def RtT6_1 := nd (nd (nd (nd (nd (lf 0xc421000fc2 [0x3010311030d,0x7000c0302]) (lf 0xc421000fe2 [0x30d000c0007,0x900190311])) (nd (lf 0x821000fa2 [0x3110301000c,0x600030302]) (nd (lf 0xd021000ee2 [0x30200070003,0x301030d]) (lf 0x9821000bf2 [0xc0007030d,0x30100130311,0x190302])))) (nd (nd (lf 0xc861000f92 [0x3110301000c,0x300090302,0x6]) (lf 0x5861000bf2 [0x30d0007000c,0x30100190311,0x130302])) (nd (lf 0x18a1000bb2 [0x903010003,0x603110302]) (nd (lf 0x9921000af2 [0x30d03020007,0x110301]) (lf 0xd002000ea2 [0xb0302001b,0x700030301]))))) (nd (nd (nd (lf 0xd002000eb2 [0xc000b001b,0x20d]) (lf 0xcc42000f12 [0x3020311000c])) (nd (lf 0x1042000eb2 [0x301000c0007,0x111020d0302]) (nd (lf 0x5842000b92 [0x3020311001b,0xc00090301]) (lf 0x5842000f92 [0x3020005001b,0xc03110301])))) (nd (nd (lf 0x5842000bb2 [0x30301000c,0x31100090302,0x6]) (lf 0x9842000f92 [0x20d000c001b,0x30203110301])) (nd (lf 0x98c2000f32 [0x3020311000c,0x20d00090101,0x26001e]) (nd (lf 0x9902000ab2 [0x30302001b,0xb0301]) (lf 0x9902000eb2 [0xc000b001b,0x20d])))))) (nd (nd (nd (nd (lf 0xc874000e82 [0x303020301]) (lf 0xc874000ea2 [0x30203010003])) (nd (lf 0x1874000ee2 [0x30d03020003,0x130301]) (nd (lf 0x5874000ec2 [0x301030d000b,0x70302]) (lf 0x5874000ee2 [0x30200070003,0x130301030d])))) (nd (nd (lf 0x9874000ec2 [0x301030d000b,0x30302]) (lf 0x9874000ae2 [0x30d03020013,0x301])) (nd (lf 0x9874000ee2 [0x30200070003,0x130301030d]) (nd (lf 0xd874000ee2 [0x30d03020003,0x130301]) (lf 0x98b4000ea2 [0x3020301000b,0x30d00070003]))))) (nd (nd (nd (lf 0x9974000ce2 [0x70301030d,0x30302]) (lf 0xd434000ce2 [0x301030d0007,0x211])) (nd (lf 0xc874000eb2 [0x30100030007,0x21100230302,0x10d]) (nd (lf 0x5874000ed2 [0x2110007000b,0x301030d]) (lf 0x9874000ad2 [0x301030d000b,0x21103020019])))) (nd (nd (lf 0x9874000ed2 [0x3010023000b,0x1e030d]) (lf 0x9874000af2 [0x30d03020007,0x1302110301])) (nd (lf 0x98b4000ab2 [0x3020301000b,0x2110007001b,0x30d]) (nd (lf 0x98b4000eb2 [0x7001b000b,0x1e010d]) (lf 0x9974000cf2 [0x30d000f0007,0x30202110301]))))))
def RtT6 : BTree NodeData := nd RtT6_0 RtT6_1
def RtM6 : BST := BN 2021851704710096 13184 (BN 1727797270210042 3456 (BN 1549360332257044 15618 (BN 1360571979746687 3840 (BN 1258254561343038 1280 (BN 1126435678265329 14976 (BN 1046536244335444 6786 (BL 930050411032511 769) (BL 1117059185393429 5889)) (BN 1150252497805883 14209 (BL 1133863318338384 15232) BE)) (BN 1285371055471136 2689 (BN 1279628739890618 1664 (BL 1262528209689372 14724) (BL 1284654079050625 12417)) (BN 1359314713535617 7040 (BL 1339914678826126 12288) BE))) (BN 1453677248435486 1408 (BN 1403672588687673 5760 (BN 1378558244035821 6400 (BL 1361288956167198 3200) (BL 1386734292921634 3458)) (BN 1413336940549483 7808 (BL 1407597779291430 6016) BE)) (BN 1534568091726321 14211 (BN 1529009288687401 4608 (BL 1528292312266890 14340) BE) (BN 1542347481788295 13056 (BL 1537668805138790 2560) BE)))) (BN 1647210752936239 14082 (BN 1598623916528081 5378 (BN 1577854494856747 11905 (BN 1563818641873385 1794 (BL 1560756670991050 4864) (BL 1564535618293896 5250)) (BN 1589247423656181 11778 (BL 1586081542832601 10626) BE)) (BN 1638639151491938 7680 (BN 1637582236004822 15874 (BL 1630475002976260 4098) BE) (BN 1641951470302172 4866 (BL 1638958335065077 3712) BE))) (BN 1691232652748067 10624 (BN 1676695555115868 14084 (BN 1667882174084779 5248 (BL 1667165197664268 1792) (BL 1672996996970964 12800)) (BN 1687831393889147 14464 (BL 1683822443153313 1024) BE)) (BN 1702401273936948 6402 (BN 1699451147303165 5120 (BL 1692723496247496 6784) BE) (BN 1720867689025974 5888 (BL 1716889821893824 14593) BE))))) (BN 1916077315429675 10880 (BN 1822084265630516 12162 (BN 1802697221052376 4096 (BN 1780941589480090 13312 (BN 1751459723733598 15616 (BL 1728283213939532 1920) (BL 1761864631053575 768)) (BN 1800413643815395 7552 (BL 1785163422536803 384) BE)) (BN 1810587219126743 4992 (BN 1809870242706232 15744 (BL 1804690914240715 14592) BE) (BN 1821367289210005 1413 (BL 1813006843609945 12164) BE))) (BN 1901677076962754 15488 (BN 1874623542840897 14466 (BN 1870614592105063 1026 (BL 1849310144412793 14080) (BL 1874562402969305 14848)) (BN 1883612956705515 7296 (BL 1882895980285004 128) BE)) (BN 1903635363185787 388 (BN 1903412675867856 3842 (BL 1902155409656786 7042) BE) (BN 1915360339009164 6272 (BL 1904129652288367 3202) BE)))) (BN 1989087621730208 10757 (BN 1948577018830640 12546 (BN 1936955494386084 3328 (BN 1927235375545982 12160 (BL 1923570050778350 11009) (BL 1930642724981163 5504)) (BN 1944568068094806 642 (BL 1941057688272988 13952) BE)) (BN 1976421774384334 4 (BN 1975913813862825 4352 (BL 1956369145281824 7169) BE) (BN 1980037067993998 13058 (BL 1976970729349941 15873) BE))) (BN 2007286562131022 13568 (BN 1997968746666397 11520 (BN 1996555138320286 6274 (BL 1989571504521372 10628) (BL 1997272114740797 10882)) (BN 2004417527230895 15234 (BL 2002731720417007 4736) BE)) (BN 2016117164024741 3968 (BN 2011371143125241 11008 (BL 2011155874634937 14725) BE) (BN 2021621136963140 2432 (BL 2016437009348191 11776) BE)))))) (BN 2371757653786816 640 (BN 2175006894651225 11264 (BN 2075639081184659 2816 (BN 2053924113658406 7936 (BN 2038806595471249 14208 (BN 2028007466864266 11648 (BL 2025813502220091 5376) (BL 2032068172383349 12673)) (BN 2049915162922572 11392 (BL 2044170237628715 7168) BE)) (BN 2064771821696832 15872 (BN 2058780742477624 1536 (BL 2053969597357707 6532) BE) (BN 2073607434219731 4480 (BL 2072825940483464 6144) BE))) (BN 2124053421471276 12928 (BN 2110686583176667 12802 (BN 2093476312534760 256 (BL 2084174784427462 13186) (BL 2108615763549237 13057)) (BN 2117185275492200 2688 (BL 2116468299071689 12416) BE)) (BN 2147580609420609 2562 (BN 2140271184654549 5632 (BL 2138921092969220 4610) BE) (BN 2173242035299116 12032 (BL 2169032008198318 6656) BE)))) (BN 2289376742092009 3972 (BN 2234150455845721 5249 (BN 2206526927991452 2561 (BN 2181662998489292 11904 (BL 2176072014232675 0) (BL 2193498337504586 13313)) (BN 2233433479425210 1793 (BL 2232365022105721 2048) BE)) (BN 2281359058665948 11136 (BN 2266271018834394 13440 (BL 2260976286143366 15104) BE) (BN 2286390559569894 15360 (BL 2282899645952809 646) BE))) (BN 2339366663168457 15490 (BN 2317728005494540 15617 (BN 2290399510305728 1156 (BL 2289972320155622 8064) (BL 2305340258026390 16000)) (BN 2336300324524400 7425 (BL 2327869616664684 6912) BE)) (BN 2353427915247912 4994 (BN 2352710938827401 15746 (BL 2339523949267898 13825) BE) (BN 2370700738299700 644 (BL 2354825584132083 13824) BE))))) (BN 2555308954825009 16004 (BN 2425720037343879 2944 (BN 2404341139607256 390 (BN 2397625250520624 3584 (BN 2385588940475104 13696 (BL 2375766604522650 12544) (BL 2390853393761909 13314)) (BN 2403839771869779 7172 (BL 2399102304750536 14977) BE)) (BN 2419157171057471 2050 (BN 2409423106064703 14720 (BL 2408527781676520 16128) BE) (BN 2424101416871291 7424 (BL 2423104981921713 14468) BE))) (BN 2492807784566823 130 (BN 2467945358723696 15489 (BN 2452206227613933 16006 (BL 2440830684730247 14849) (BL 2466536981067049 6528)) (BN 2485649568187520 2176 (BL 2477232318811509 3333) BE)) (BN 2518168267265455 14081 (BN 2512295886149519 512 (BL 2493524760987334 7298) BE) (BN 2552827932679045 5633 (BL 2550127258252191 13570) BE)))) (BN 2730506513998555 2305 (BN 2671030544334615 16256 (BN 2613761600438378 2 (BN 2575015203164259 7300 (BL 2574298226743748 4224) (BL 2581647291592418 14210)) (BN 2641627799622030 10752 (BL 2620874686852508 4740) BE)) (BN 2699193483508962 14598 (BN 2694671625072753 5377 (BL 2682737744765283 6146) BE) (BN 2727066328297712 3973 (BL 2715569281793939 896) BE))) (BN 2834933138522302 1152 (BN 2784918698933044 11266 (BN 2733353624051981 16258 (BL 2733123964507559 12672) (BL 2764228186942208 14336)) (BN 2833609241209631 2304 (BL 2802296210720038 14596) BE)) (BN 2987571951188755 7302 (BN 2986854974768244 4225 (BL 2884900583963330 3072) BE) (BN 3176784934966704 14337 (BL 2989373263682655 14470) BE))))))
def RtT7 : BTree NodeData := nd (nd (nd (lf 0x10007e1 [0x10d01020111,0x130101]) (lf 0x10007f1 [0x1010111010d,0xc00070102,0x130009])) (nd (lf 0x110007e1 [0x1010111010d,0x120102]) (nd (lf 0x110007f1 [0x1010111010d,0x7000c0102,0x190012]) (lf 0x210007c1 [0x1110101010d,0x102])))) (nd (nd (lf 0x210007e1 [0x1010111010d,0x120102]) (nd (lf 0x210007d1 [0x1110101010d,0x90102]) (lf 0x210007f1 [0x1010111010d,0x900070102,0x12]))) (nd (lf 0x20007b1 [0x10201110101,0xd0009000c]) (nd (lf 0x340006e1 [0x101010d0102]) (lf 0x340006f1 [0x101010d0102,0x1100190007]))))
def RtM7 : BST := BN 2368240071471337 3204 (BN 2008910476296878 3844 (BN 1879288330125650 2816 (BN 1660328529783741 0 (BN 1638551236484850 5378 (BN 1524283361531056 1024 (BN 1480606877807908 15744 (BL 1472379829832054 7809) BE) (BN 1631538386016101 7424 (BL 1557082456034530 5120) BE)) (BN 1653009546101191 6914 (BN 1640914878888001 4480 (BL 1640197902467490 384) BE) (BL 1653726522521702 2178))) (BN 1765732594763974 15488 (BN 1756356101892074 6912 (BN 1715892624185312 3968 (BL 1662386038973091 15490) BE) (BL 1757073078312585 2176)) (BN 1874562402969305 4864 (BN 1840650627961404 5376 (BL 1839936472982367 8064) BE) (BL 1878571353705139 3328)))) (BN 1990867981190560 1152 (BN 1963036330776600 4100 (BN 1923570050778350 15873 (BN 1916412051208989 1536 (BL 1883612956705515 14848) BE) (BL 1944568068094806 14594)) (BN 1976421774384334 15104 (BN 1975164508173264 7552 (BL 1963753307197111 2560) BE) (BL 1977138750804845 6272))) (BN 1995835425280074 2052 (BN 1993154904502964 3842 (BN 1991826474544240 5892 (BL 1991509814215888 896) BE) (BL 1993871880923475 3202)) (BN 2000244474062460 2944 (BN 1999527497641949 4484 (BL 1996552401700585 512) BE) (BL 2005211918151974 4608))))) (BN 2215685607989800 3072 (BN 2098018115989444 2 (BN 2023447573929077 15746 (BN 2018941148537689 4612 (BN 2011371143125241 15872 (BL 2009244461822563 3712) BE) (BL 2021715634147550 642)) (BN 2077887488673193 386 (BN 2076188333464599 7808 (BL 2069227972221804 7426) BE) (BL 2078604465093704 4482))) (BN 2133808778214424 16001 (BN 2125062189938433 640 (BN 2124770397891787 1664 (BL 2124053421471276 6784) BE) (BL 2132954325093933 2432)) (BN 2195254295979518 3840 (BN 2166994260316349 5122 (BL 2134195165812875 1026) BE) (BL 2195971272400029 3200)))) (BN 2291906113339768 15617 (BN 2237900948879598 16128 (BN 2233891998143764 7296 (BN 2233175021723253 7936 (BL 2217151411355392 4736) BE) (BL 2235962006040516 7682)) (BN 2262262068098560 5504 (BN 2258733320306481 3970 (BL 2248484702493274 7168) BE) (BL 2282899645952809 14598))) (BN 2335751369558793 1792 (BN 2322365925951059 6148 (BN 2300565629791157 4742 (BL 2299724128485526 2306) BE) (BL 2323082902371570 6656)) (BN 2351156069718699 14464 (BN 2350839409390347 16256 (BL 2350439093298188 5888) BE) (BL 2363824536905922 4)))))) (BN 2645279897236996 15105 (BN 2508286935413685 6144 (BN 2434590717616636 15489 (BN 2395008840550844 15616 (BN 2382777169103536 8066 (BN 2371757653786816 14592 (BL 2370700738299700 14596) BE) (BN 2386305916895615 3456 (BL 2385588940475104 1408) BE)) (BN 2426437013764390 14720 (BN 2425720037343879 6528 (BL 2403070684276409 2304) BE) (BL 2428557567396263 1154))) (BN 2444839635466081 3329 (BN 2439829552473356 2689 (BN 2437934060268163 2946 (BL 2437217083847652 4485) BE) (BL 2440830684730247 4865)) (BN 2493524760987334 14850 (BN 2456630734743392 4613 (BL 2445556611886592 2817) BE) (BL 2507569958993174 4096)))) (BN 2595291601214975 1282 (BN 2526323855490808 1538 (BN 2520955402600908 7428 (BN 2513012862570030 4224 (BL 2512295886149519 128) BE) (BL 2521672379021419 1156)) (BN 2574293583898519 257 (BN 2542932279684432 2688 (BL 2540369053496648 2048) BE) (BL 2575015203164259 14852))) (BN 2621591663273019 6016 (BN 2613759863896769 3584 (BN 2609750913160935 768 (BL 2607814297667733 1540) BE) (BL 2620874686852508 15232)) (BN 2636865587154384 6404 (BN 2628242356014296 3073 (BL 2623136356768669 6400) BE) (BL 2642550007664409 15360))))) (BN 2871625481323978 4228 (BN 2744918535649563 1920 (BN 2662094676245410 256 (BN 2660219325283107 15620 (BN 2654656390108896 4992 (BL 2645996873657507 6273) BE) (BL 2661041450517770 7169)) (BN 2728606281043617 5760 (BN 2674070041004636 4609 (BL 2663151591732526 7680) BE) (BL 2737617281846969 16000))) (BN 2799443303484195 7937 (BN 2785482369853646 14976 (BN 2785049632518338 7040 (BL 2761683303030357 5636) BE) (BL 2793920312791095 641)) (BN 2866899554167633 2564 (BN 2804169230640540 16129 (BL 2800160279904706 7297) BE) (BL 2867616530588144 6660)))) (BN 3020371045692229 1542 (BN 2969080508335394 5248 (BN 2937903719303592 5633 (BN 2933623179072978 1286 (BL 2899698648671107 516) BE) (BL 2968363531914883 772)) (BN 3001162626418357 15364 (BN 2987571951188755 14854 (BL 2973089459071228 4352) BE) (BL 3004609492411455 1793))) (BN 3158293492113343 3588 (BN 3041006446514668 5632 (BN 3022481186906985 1280 (BL 3021424271419869 1284) BE) (BL 3074555173360087 6405)) (BN 3296516338057540 2310 (BN 3291994479621331 6401 (BL 3159010468533854 4356) BE) (BL 3399619065268616 2308))))))
def RtT8 : BTree NodeData := lf 0x3f0 [0x10011000d,0x2]
def RtM8 : BST := BN 2423831640239918 901 (BN 2008330190539816 386 (BN 1986142054034215 900 (BN 1963753307197111 128 (BL 1963036330776600 1792) (BL 1972412823648500 896)) (BN 1991826474544240 0 (BL 1986859030454726 1924) BE)) (BN 2331742418822959 1920 (BN 2322365925951059 640 (BL 2111676746330699 384) (BL 2323082902371570 1664)) (BN 2351156069718699 512 (BL 2350439093298188 4) BE))) (BN 2749612508568958 388 (BN 2609750913160935 256 (BN 2507569958993174 1796 (BL 2424548616660429 1925) (BL 2508286935413685 644)) (BN 2646509781357882 390 (BL 2641270946501162 897) BE)) (BN 2968363531914883 260 (BN 2867616530588144 1668 (BL 2866899554167633 132) BE) (BN 3000600541675621 1921 (BL 2969080508335394 768) BE)))
def RtL : Nat → Option (BTree NodeData) | 4 => some RtT4 | 5 => some RtT5 | 6 => some RtT6 | 7 => some RtT7 | 8 => some RtT8 | _ => none
def RtM : Nat → BST | 5 => RtM5 | 6 => RtM6 | 7 => RtM7 | 8 => RtM8 | _ => BE
end CertData
noncomputable section CertVerify
abbrev ok (f : Forest) (k : Nat) (t : BTree NodeData) := t.all (fastNodeOK f k) = true
def base0 (_ : Nat) : List Sig × Sig × Nat := ([], 0, 0)
private theorem base0_s : ∀ k, k ≠ 0 → LowerBV (base0 k).1 (base0 k).2.1 (base0 k).2.2 := fun _ _ _ _ _ _ => Nat.zero_le _
def fF1 : Forest := ⟨15,tF1,3,F1P,F1N,F1R,F1A,F1C,F1L,F1M⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F1v : graphValid fF1 base0 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F1k3 : ok fF1 3 F1T3 := by decide +kernel
private theorem F1lv : levelsChecked fF1 := by
  intro k hk tree ht; change k ≤ 3 at hk; interval_cases k
  all_goals simp [fF1,F1L] at ht
  subst ht; exact F1k3
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowF1 : LowerBV (rawOf 15) tF1 4 :=
  lower_forest fF1 base0 base0_s F1v F1lv (by decide +kernel)
def base1 : Nat → List Sig × Sig × Nat | 1 => (rawOf 15,tF1,4) | _ => ([],0,0)
private theorem base1_s : ∀ k, k ≠ 0 → LowerBV (base1 k).1 (base1 k).2.1 (base1 k).2.2 := by
  intro k _; match k with
  | 1 => exact lowF1
  | 0 | _ + 2 => exact fun _ _ _ _ => Nat.zero_le _
def fF2 : Forest := ⟨15,tF2,5,F2P,F2N,F2R,F2A,F2C,F2L,F2M⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F2v : graphValid fF2 base1 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F2k2 : ok fF2 2 F2T2 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F2k3 : ok fF2 3 F2T3 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F2k4 : ok fF2 4 F2T4 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F2k5 : ok fF2 5 F2T5 := by decide +kernel
private theorem F2lv : levelsChecked fF2 := by
  intro k hk tree ht; change k ≤ 5 at hk; interval_cases k
  all_goals simp [fF2,F2L] at ht
  · subst ht; exact F2k2
  · subst ht; exact F2k3
  · subst ht; exact F2k4
  · subst ht; exact F2k5
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowF2 : LowerBV (rawOf 15) tF2 6 :=
  lower_forest fF2 base1 base1_s F2v F2lv (by decide +kernel)
def base2 : Nat → List Sig × Sig × Nat | 1 => (rawOf 15,tF1,4) | 2 => (rawOf 15,tF2,6) | _ => ([],0,0)
private theorem base2_s : ∀ k, k ≠ 0 → LowerBV (base2 k).1 (base2 k).2.1 (base2 k).2.2 := by
  intro k _; match k with
  | 1 => exact lowF1
  | 2 => exact lowF2
  | 0 | _ + 3 => exact fun _ _ _ _ => Nat.zero_le _
def fF3 : Forest := ⟨31,tF3,6,F3P,F3N,F3R,F3A,F3C,F3L,F3M⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F3v : graphValid fF3 base2 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F3k6 : ok fF3 6 F3T6 := by decide +kernel
private theorem F3lv : levelsChecked fF3 := by
  intro k hk tree ht; change k ≤ 6 at hk; interval_cases k
  all_goals simp [fF3,F3L] at ht
  subst ht; exact F3k6
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowF3 : LowerBV (rawOf 31) tF3 7 :=
  lower_forest fF3 base2 base2_s F3v F3lv (by decide +kernel)
def base3 : Nat → List Sig × Sig × Nat | 1 => (rawOf 15,tF1,4) | 2 => (rawOf 15,tF2,6) | 3 => (rawOf 31,tF3,7) | _ => ([],0,0)
private theorem base3_s : ∀ k, k ≠ 0 → LowerBV (base3 k).1 (base3 k).2.1 (base3 k).2.2 := by
  intro k _; match k with
  | 1 => exact lowF1
  | 2 => exact lowF2
  | 3 => exact lowF3
  | 0 | _ + 4 => exact fun _ _ _ _ => Nat.zero_le _
def fRt : Forest := ⟨63,tRt,8,RtP,RtN,RtR,RtA,RtC,RtL,RtM⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtv : graphValid fRt base3 = true := by decide +kernel
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
private theorem Rtk5 : ok fRt 5 RtT5 := by
  simp only [ok,RtT5,nd,BTree.all,Rtk5_0,Rtk5_1,Rtk5_2,Rtk5_3,Bool.and_true]
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk6_0 : ok fRt 6 RtT6_0 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk6_1 : ok fRt 6 RtT6_1 := by decide +kernel
private theorem Rtk6 : ok fRt 6 RtT6 := by
  simp only [ok,RtT6,nd,BTree.all,Rtk6_0,Rtk6_1,Bool.and_true]
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
  lower_forest fRt base3 base3_s Rtv Rtlv (by decide +kernel)
end CertVerify

def targetFun (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (3936929928 * 2 ^ 32 + 3364391048) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def smallCircuit : Circuit :=
  ⟨[⟨.and, [0, 4]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [5, 6]⟩, ⟨.and, [7, 9]⟩, ⟨.or, [0, 11]⟩, ⟨.and, [1, 12]⟩, ⟨.and, [8, 10]⟩, ⟨.or, [13, 14]⟩], 15⟩

private theorem witnessMonotone : Monotone2 smallCircuit := by
  intro g hg
  simp only [smallCircuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl, by decide⟩ | exact ⟨Or.inr rfl, by decide⟩

def idx6 (x : Fin 6 → Bool) : Nat :=
  (if x 0 then 1 else 0) + (if x 1 then 2 else 0) + (if x 2 then 4 else 0) +
  (if x 3 then 8 else 0) + (if x 4 then 16 else 0) + (if x 5 then 32 else 0)
private theorem sum_fin6 (x : Fin 6 → Bool) :
    (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) = idx6 x := by
  simp [Fin.sum_univ_six, idx6]
private theorem witnessCorrectFast : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    smallCircuit.eval [b0, b1, b2, b3, b4, b5] =
    Nat.testBit (3936929928 * 2 ^ 32 + 3364391048)
      ((if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) +
       (if b3 then 8 else 0) + (if b4 then 16 else 0) + (if b5 then 32 else 0)) := by
  decide +kernel
private theorem witnessCorrect (x : Fin 6 → Bool) : smallCircuit.eval (List.ofFn x) = targetFun x := by
  rw [targetFun, sum_fin6, idx6, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ,
      List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
  exact witnessCorrectFast (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def sample6 (r : Row) (i : Fin 6) : Bool := bitBV r ((rawOf 63).getD i.val zeroBV)
private theorem raw63_list : List.ofFn (fun i : Fin 6 => (rawOf 63).getD i.val zeroBV) = rawOf 63 := rfl
private theorem sample6_eq (r : Row) :
    List.ofFn (sample6 r) = ((rawOf 63).map observeBV).map (fun f => f r) := by
  rw [← raw63_list, List.map_map, List.map_ofFn]; rfl
private theorem sample6_targetFast : ∀ r : Row, Nat.testBit (3936929928 * 2 ^ 32 + 3364391048) (idx6 (sample6 r)) = bitBV r tRt := by decide +kernel
private theorem sample6_target (r : Row) : targetFun (sample6 r) = bitBV r tRt := by
  rw [targetFun, sum_fin6]; exact sample6_targetFast r

private theorem fanInTwo_ops {C : Circuit} (h : FanInTwo C) :
    ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by
  intro g hg; obtain ⟨ho, hl⟩ := h g hg; refine ⟨?_, hl⟩
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ho

private theorem mainProof (s : ℕ) (h : HasCircuitSize 6 targetFun s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = targetFun x := by
  classical
  obtain ⟨C, hFanIn, hSize, hEval⟩ := h
  by_cases big : 10 ≤ C.size
  · have hsc : smallCircuit.size = 10 := rfl
    exact ⟨smallCircuit, witnessMonotone, by omega, witnessCorrect⟩
  have hfit := fanInTwo_ops hFanIn
  by_cases mono : ∀ g ∈ C.gates, g.op ≠ GateOp.not
  · refine ⟨C, ?_, hSize, hEval⟩
    intro g hg; obtain ⟨ops, ar⟩ := hfit g hg; refine ⟨?_, ar⟩
    rcases ops with a | b | c
    · exact Or.inl a
    · exact Or.inr b
    · exact (mono g hg c).elim
  push Not at mono
  obtain ⟨g, hg, hop⟩ := mono
  have hlt : C.gates.countP (fun q => !isNot q) < C.gates.length := by
    rcases Nat.lt_or_ge (C.gates.countP (fun q => !isNot q)) C.gates.length with h1 | h1
    · exact h1
    · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h1) g hg
      simp [isNot, hop] at eq
  obtain ⟨q, bank, hq, hreach, hsup⟩ := circuit_reach ((rawOf 63).map observeBV) C.gates ((rawOf 63).map observeBV)
    0 ((rawOf 63).map observeBV) hfit Reach.start (fun a ha => Or.inl ha)
  have hout : (execWires C.gates ((rawOf 63).map observeBV)).getD C.output (fun _ => false) = observeBV tRt := by
    funext r
    have hev := execWires_at C.gates ((rawOf 63).map observeBV) r
    have hr1 : ((execWires C.gates ((rawOf 63).map observeBV)).getD C.output (fun _ => false)) r =
        ((execWires C.gates ((rawOf 63).map observeBV)).map (fun f => f r)).getD C.output false := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
      cases (execWires C.gates ((rawOf 63).map observeBV))[C.output]? <;> rfl
    rw [hr1, hev, ← sample6_eq r]
    exact (hEval (sample6 r)).trans (sample6_target r)
  have havail : Available bank (observeBV tRt) := hout ▸ avail_getD hsup C.output
  have hlb := lowRt q bank hreach havail
  simp [Circuit.size] at big
  omega

end PEqualNP.Outside.L_meta_15253

open PEqualNP.Outside.L_meta_15253 in
theorem PEqualNP.Outside.L_meta_15253 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3936929928 * 2 ^ 32 + 3364391048) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3936929928 * 2 ^ 32 + 3364391048) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  mainProof
