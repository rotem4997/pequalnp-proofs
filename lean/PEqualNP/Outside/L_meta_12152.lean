import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12152
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
def tF1 : Sig := 0xffffff00ff000000#64
def F1P : List Row := mkRows [24,24,24,40,40,40,48,48,48]
def F1N : List Row := mkRows [8,16,32,8,16,32,8,16,32]
def F1R : List (Nat × Nat) := [(63,73),(455,146),(504,292)]
def F1A : List (List Nat) := [[0,1,2,3,4,5],[0,1,2,3,5,4],[0,1,2,4,3,5],[0,1,2,4,5,3],[0,1,2,5,3,4],[0,1,2,5,4,3]]
def F1C : List CutSpec := []
def F1T3 : BTree NodeData := lf 0x70 []
def F1L : Nat → Option (BTree NodeData) | 3 => some F1T3 | _ => none
def F1M : Nat → BST | _ => BE
def tF2 : Sig := 0xfffffff0fff0f000#64
def F2P : List Row := mkRows [12,12,12,12,20,20,20,20,24,24,24,24,36,36,36,36,40,40,40,40,48,48,48,48]
def F2N : List Row := mkRows [4,8,16,32,4,8,16,32,4,8,16,32,4,8,16,32,4,8,16,32,4,8,16,32]
def F2R : List (Nat × Nat) := [(61695,1118481),(986895,2236962),(15732720,4473924),(16773120,8947848)]
def F2A : List (List Nat) := [[0,1,2,3,4,5],[0,1,2,3,5,4],[0,1,2,4,3,5],[0,1,2,4,5,3],[0,1,2,5,3,4],[0,1,2,5,4,3],[0,1,3,2,4,5],[0,1,3,2,5,4],[0,1,3,4,2,5],[0,1,3,4,5,2],[0,1,3,5,2,4],[0,1,3,5,4,2],[0,1,4,2,3,5],[0,1,4,2,5,3],[0,1,4,3,2,5],[0,1,4,3,5,2],[0,1,4,5,2,3],[0,1,4,5,3,2],[0,1,5,2,3,4],[0,1,5,2,4,3],[0,1,5,3,2,4],[0,1,5,3,4,2],[0,1,5,4,2,3],[0,1,5,4,3,2]]
def F2C : List CutSpec := [⟨16,0,4,1,0,[0,1,3,4,2,5],0xffff0000ffff#64⟩,⟨4,0,4,1,0,[0,1,2,3,4,5],0xf0f0f0f0f0f0f0f#64⟩,⟨8,0,4,1,0,[0,1,3,2,4,5],0xff00ff00ff00ff#64⟩,⟨32,0,4,1,0,[0,1,3,4,5,2],0xffffffff#64⟩]
def F2T3 : BTree NodeData := nd (lf 0x1214811000783 [0x20001]) (lf 0x3535091000473 [])
def F2T4 : BTree NodeData := nd (lf 0x48110003e2 [0x10003]) (nd (lf 0x50910002f2 [0x4]) (lf 0xd0910002f2 []))
def F2M4 : BST := BN 246176673 0 (BL 142170705 128) BE
def F2T5 : BTree NodeData := lf 0x110001f1 [0x100030002,0x4]
def F2M5 : BST := BN 264638547 385 (BN 239237001 0 (BN 239181461 128 (BL 214627343 384) BE) (BL 253069531 129)) (BN 271980395 1 (BL 269023962 7) (BL 299662611 6))
def F2T6 : BTree NodeData := lf 0xf0 [0x100030002,0x4]
def F2M6 : BST := BN 230260810 2 (BN 215866071 0 (BL 206320026 10) (BL 223391134 16)) (BN 263004204 4 (BL 236958675 8) BE)
def F2L : Nat → Option (BTree NodeData) | 3 => some F2T3 | 4 => some F2T4 | 5 => some F2T5 | 6 => some F2T6 | _ => none
def F2M : Nat → BST | 4 => F2M4 | 5 => F2M5 | 6 => F2M6 | _ => BE
def tF3 : Sig := 0xfffcfffcffc0ffc0#64
def F3P : List Row := mkRows [6,6,6,8,8,8,34,34,34,36,36,36]
def F3N : List Row := mkRows [2,4,32,2,4,32,2,4,32,2,4,32]
def F3R : List (Nat × Nat) := [(455,585),(3591,1170),(56,0),(4032,2340)]
def F3A : List (List Nat) := [[0,1,2,3,4,5],[0,1,5,3,4,2],[0,2,1,3,4,5],[0,2,5,3,4,1],[0,5,1,3,4,2],[0,5,2,3,4,1]]
def F3C : List CutSpec := [⟨8,0,4,1,0,[0,3,4,1,2,5],0xff00ff00ff00ff#64⟩]
def F3T4 : BTree NodeData := lf 0xf0 [0x1]
def F3L : Nat → Option (BTree NodeData) | 4 => some F3T4 | _ => none
def F3M : Nat → BST | _ => BE
def tF4 : Sig := 0xfff0ff00ff000000#64
def F4P : List Row := mkRows [24,24,24,24,40,40,40,40,52,52,52,52]
def F4N : List Row := mkRows [12,20,36,48,12,20,36,48,12,20,36,48]
def F4R : List (Nat × Nat) := [(3840,1911),(255,273),(3855,2730),(4080,3276)]
def F4A : List (List Nat) := [[0,1,2,3,4,5],[0,1,2,3,5,4]]
def F4C : List CutSpec := [⟨0,4,4,1,0,[0,1,2,3,4,5],0xf0f0f0f0f0f0f0f0#64⟩]
def F4T4 : BTree NodeData := lf 0xf0 [0x1]
def F4L : Nat → Option (BTree NodeData) | 4 => some F4T4 | _ => none
def F4M : Nat → BST | _ => BE
def tF5 : Sig := 0xfcfcc0c0c0c00000#64
def F5P : List Row := mkRows [22,22,22,22,22,22,38,38,38,38,38,38,50,50,50,50,50,50,52,52,52,52,52,52]
def F5N : List Row := mkRows [6,18,20,34,36,48,6,18,20,34,36,48,6,18,20,34,36,48,6,18,20,34,36,48]
def F5R : List (Nat × Nat) := [(262143,2929355),(16519167,5592405),(16773183,10119590),(16777152,14913080)]
def F5A : List (List Nat) := [[0,1,2,3,4,5],[0,1,2,3,5,4],[0,1,4,3,2,5],[0,1,4,3,5,2],[0,1,5,3,2,4],[0,1,5,3,4,2],[0,2,1,3,4,5],[0,2,1,3,5,4],[0,2,4,3,1,5],[0,2,4,3,5,1],[0,2,5,3,1,4],[0,2,5,3,4,1],[0,4,1,3,2,5],[0,4,1,3,5,2],[0,4,2,3,1,5],[0,4,2,3,5,1],[0,4,5,3,1,2],[0,4,5,3,2,1],[0,5,1,3,2,4],[0,5,1,3,4,2],[0,5,2,3,1,4],[0,5,2,3,4,1],[0,5,4,3,1,2],[0,5,4,3,2,1]]
def F5C : List CutSpec := [⟨0,4,4,1,0,[0,3,1,2,4,5],0xf0f0f0f0f0f0f0f0#64⟩,⟨0,16,4,1,0,[0,3,4,1,2,5],0xffff0000ffff0000#64⟩,⟨0,32,4,1,0,[0,3,4,1,5,2],0xffffffff00000000#64⟩,⟨0,2,4,1,0,[0,1,3,2,4,5],0xcccccccccccccccc#64⟩]
def F5T3 : BTree NodeData := nd (lf 0x210801000783 [0x20001]) (lf 0x2531081000473 [])
def F5T4 : BTree NodeData := nd (lf 0x8010003e2 [0x20001]) (nd (lf 0x10810002f2 [0x3]) (lf 0x90810002f2 []))
def F5M4 : BST := BN 361592107 128 (BL 225791769 0) BE
def F5T5 : BTree NodeData := lf 0x10001f1 [0x200040001,0x3]
def F5M5 : BST := BN 304804510 7 (BN 300772491 129 (BN 297662232 385 (BL 251787768 1) BE) (BL 304551422 128)) (BN 322156621 6 (BL 318464957 0) (BL 338306344 384))
def F5T6 : BTree NodeData := lf 0xf0 [0x200040001,0x3]
def F5M6 : BST := BN 289680740 8 (BN 272328629 10 (BL 264191322 4) (BL 281984186 16)) (BN 337972941 0 (BL 330868511 2) BE)
def F5L : Nat → Option (BTree NodeData) | 3 => some F5T3 | 4 => some F5T4 | 5 => some F5T5 | 6 => some F5T6 | _ => none
def F5M : Nat → BST | 4 => F5M4 | 5 => F5M5 | 6 => F5M6 | _ => BE
def tF6 : Sig := 0xffc0ffc0c000c000#64
def F6P : List Row := mkRows [14,14,14,14,14,38,38,38,38,38,40,40,40,40,40]
def F6N : List Row := mkRows [6,10,12,34,36,6,10,12,34,36,6,10,12,34,36]
def F6R : List (Nat × Nat) := [(1023,11627),(1023,22197),(31775,6342),(32736,25368)]
def F6A : List (List Nat) := [[0,1,2,3,4,5],[0,1,2,5,4,3],[0,2,1,3,4,5],[0,2,1,5,4,3]]
def F6C : List CutSpec := [⟨0,2,4,1,0,[0,1,3,4,2,5],0xcccccccccccccccc#64⟩]
def F6T4 : BTree NodeData := lf 0xf0 [0x1]
def F6L : Nat → Option (BTree NodeData) | 4 => some F6T4 | _ => none
def F6M : Nat → BST | _ => BE
def tF7 : Sig := 0xfefefefe80808080#64
def F7P : List Row := mkRows [7,7,7,7,33,33,33,33,34,34,34,34,36,36,36,36]
def F7N : List Row := mkRows [3,5,6,32,3,5,6,32,3,5,6,32,3,5,6,32]
def F7R : List (Nat × Nat) := [(255,13107),(3855,21845),(61455,26214),(65520,34952)]
def F7A : List (List Nat) := [[0,1,2,3,4,5],[0,2,1,3,4,5],[1,0,2,3,4,5],[1,2,0,3,4,5],[2,0,1,3,4,5],[2,1,0,3,4,5]]
def F7C : List CutSpec := [⟨1,0,2,0,0,[0,1,2,3,4,5],0x5555555555555555#64⟩,⟨0,1,2,0,0,[0,1,2,3,4,5],0xaaaaaaaaaaaaaaaa#64⟩,⟨0,2,2,0,0,[0,1,2,3,4,5],0xcccccccccccccccc#64⟩,⟨0,3,1,0,0,[0,1,2,3,4,5],0x8888888888888888#64⟩,⟨3,0,1,0,0,[0,1,2,3,4,5],0x1111111111111111#64⟩,⟨2,0,2,0,0,[0,1,2,3,4,5],0x3333333333333333#64⟩,⟨0,4,2,0,0,[0,1,2,3,4,5],0xf0f0f0f0f0f0f0f0#64⟩,⟨4,0,2,0,0,[0,1,2,3,4,5],0xf0f0f0f0f0f0f0f#64⟩,⟨5,0,1,0,0,[0,1,2,3,4,5],0x505050505050505#64⟩,⟨0,5,1,0,0,[0,1,2,3,4,5],0xa0a0a0a0a0a0a0a0#64⟩]
def F7T2 : BTree NodeData := lf 0x35444010004c3 []
def F7T3 : BTree NodeData := nd (nd (nd (lf 0x44010003c2 [0x20001]) (nd (lf 0xc4210003c2 []) (lf 0x50a10002b2 [0x1]))) (nd (lf 0x90a10002b2 [0x3]) (nd (lf 0x50e1000272 [0x2]) (lf 0x90e1000272 [0x1])))) (nd (nd (lf 0x9043000252 []) (nd (lf 0x50430002d2 [0x1]) (lf 0x90430002d2 []))) (nd (nd (lf 0xd053000252 []) (lf 0x10530002d2 [0x2])) (nd (lf 0xd0530002d2 []) (lf 0xcc23000362 []))))
def F7M3 : BST := BL 140647539 0
def F7T4 : BTree NodeData := nd (nd (nd (lf 0x10001f1 [0x10004]) (lf 0x110001f1 [0x20005])) (nd (lf 0x210001f1 [0x30001]) (nd (lf 0x3000171 [0x600030001,0x80007]) (lf 0x30001f1 [0x20001])))) (nd (nd (lf 0x13000171 [0x300060002,0x70008]) (nd (lf 0x130001f1 [0x10002]) (lf 0x23000171 [0x90005]))) (nd (lf 0x230001f1 [0x20001]) (nd (lf 0x33000171 [0xa0004]) (lf 0x330001f1 [0x10002]))))
def F7M4 : BST := BN 199498399 1409 (BN 119141266 129 (BN 107027481 384 (BN 101328901 640 (BL 100457831 1408) BE) (BL 116297009 896)) (BN 175677306 128 (BN 130584829 641 (BL 128410794 1665) BE) (BL 184946834 1664))) (BN 230686466 897 (BN 214950321 256 (BN 214016832 0 (BL 203889354 1792) BE) (BL 221416938 385)) (BN 267714796 768 (BN 239767189 512 (BL 238370446 1536) BE) (BL 320583751 1920)))
def F7T5 : BTree NodeData := lf 0xf0 []
def F7M5 : BST := BN 261503709 261 (BN 217058619 1922 (BN 194644577 772 (BN 192785291 512 (BN 186533124 259 (BL 186507270 770) BE) (BL 193549085 130)) (BN 203914105 1796 (BN 202818613 642 (BL 195776798 1794) BE) (BL 207789091 898))) (BN 240069439 384 (BN 230799911 1664 (BN 226226062 768 (BL 219304301 1) BE) (BL 235495590 1792)) (BN 259226123 257 (BL 252883374 256) (BL 261335169 1668)))) (BN 283231814 513 (BN 277144977 1920 (BN 270604697 388 (BN 269558417 3 (BL 267875449 896) BE) (BL 273618584 1666)) (BN 277468324 128 (BL 277288130 258) (BL 282888112 386))) (BN 289394846 260 (BN 286737852 640 (BN 284237818 515 (BL 283927332 132) BE) (BL 289102638 900)) (BN 298372166 1924 (BL 293196860 644) (BL 311635856 0))))
def F7L : Nat → Option (BTree NodeData) | 2 => some F7T2 | 3 => some F7T3 | 4 => some F7T4 | 5 => some F7T5 | _ => none
def F7M : Nat → BST | 3 => F7M3 | 4 => F7M4 | 5 => F7M5 | _ => BE
def tF8 : Sig := 0xfefefefefefe8080#64
def F8P : List Row := mkRows [7,7,7,7,17,17,17,17,18,18,18,18,20,20,20,20,33,33,33,33,34,34,34,34,36,36,36,36]
def F8N : List Row := mkRows [3,5,6,48,3,5,6,48,3,5,6,48,3,5,6,48,3,5,6,48,3,5,6,48,3,5,6,48]
def F8R : List (Nat × Nat) := [(983295,53687091),(15732495,89478485),(251719695,107374182),(65520,143165576),(268369920,143165576)]
def F8A : List (List Nat) := [[0,1,2,3,4,5],[0,1,2,3,5,4],[0,2,1,3,4,5],[0,2,1,3,5,4],[1,0,2,3,4,5],[1,0,2,3,5,4],[1,2,0,3,4,5],[1,2,0,3,5,4],[2,0,1,3,4,5],[2,0,1,3,5,4],[2,1,0,3,4,5],[2,1,0,3,5,4]]
def F8C : List CutSpec := [⟨32,0,6,7,0,[0,1,2,3,5,4],0xffffffff#64⟩]
def F8T6 : BTree NodeData := lf 0x1f0 [0x1]
def F8L : Nat → Option (BTree NodeData) | 6 => some F8T6 | _ => none
def F8M : Nat → BST | _ => BE
def tF9 : Sig := 0xfee8fee8fe80fe80#64
def F9P : List Row := mkRows [7,7,7,7,7,7,7,9,9,9,9,9,9,9,10,10,10,10,10,10,10,12,12,12,12,12,12,12,35,35,35,35,35,35,35,37,37,37,37,37,37,37,38,38,38,38,38,38,38]
def F9N : List Row := mkRows [3,5,6,33,34,36,40,3,5,6,33,34,36,40,3,5,6,33,34,36,40,3,5,6,33,34,36,40,3,5,6,33,34,36,40,3,5,6,33,34,36,40,3,5,6,33,34,36,40]
def F9R : List (Nat × Nat) := [(4397778092031,48759444784523),(558586000294015,93086212770453),(562915860021375,168441718346534),(268435328,283691315109952),(562949684985856,531921215831160)]
def F9A : List (List Nat) := [[0,1,2,3,4,5],[0,2,1,3,4,5],[1,0,2,3,4,5],[1,2,0,3,4,5],[2,0,1,3,4,5],[2,1,0,3,4,5]]
def F9C : List CutSpec := [⟨32,3,1,0,0,[0,1,2,3,4,5],0x88888888#64⟩,⟨0,8,2,0,0,[0,1,2,3,4,5],0xff00ff00ff00ff00#64⟩,⟨32,0,6,7,0,[0,1,2,5,3,4],0xffffffff#64⟩,⟨2,1,2,0,0,[0,1,2,3,4,5],0x2222222222222222#64⟩,⟨4,8,1,0,0,[0,1,2,3,4,5],0xf000f000f000f00#64⟩,⟨2,5,1,0,0,[0,1,2,3,4,5],0x2020202020202020#64⟩,⟨0,32,7,2,0,[2,3,4,5,0,1],0xffffffff00000000#64⟩,⟨1,0,5,4,0,[0,4,5,3,1,2],0x5555555555555555#64⟩,⟨8,0,7,5,0,[1,2,4,0,3,5],0xff00ff00ff00ff#64⟩,⟨0,2,5,3,0,[1,0,2,3,4,5],0xcccccccccccccccc#64⟩,⟨32,5,1,0,0,[0,1,2,3,4,5],0xa0a0a0a0#64⟩,⟨37,0,1,0,0,[0,1,2,3,4,5],0x5050505#64⟩,⟨0,4,5,3,0,[1,2,0,3,4,5],0xf0f0f0f0f0f0f0f0#64⟩,⟨4,0,5,4,0,[4,5,0,3,1,2],0xf0f0f0f0f0f0f0f#64⟩,⟨8,1,4,1,0,[0,3,4,1,2,5],0xaa00aa00aa00aa#64⟩,⟨2,0,5,4,0,[4,0,5,3,1,2],0x3333333333333333#64⟩,⟨0,1,5,3,0,[0,1,2,3,4,5],0xaaaaaaaaaaaaaaaa#64⟩,⟨8,4,4,1,0,[3,4,0,1,2,5],0xf000f000f000f0#64⟩,⟨4,3,1,0,0,[0,1,2,3,4,5],0x808080808080808#64⟩,⟨8,2,4,1,0,[3,0,4,1,2,5],0xcc00cc00cc00cc#64⟩]
def F9T2 : BTree NodeData := nd (lf2 0x1cb654401004186 0xe6172 [0x20001]) (lf2 0x9cb654401006106 0x60f72 [0x22f03])
def F9T3 : BTree NodeData := nd (nd (lf2 0x1cb654401003185 0x172 [0x40001]) (lf2 0x9cb654401003185 0x372 [0xf0300050001])) (nd (lf2 0x9cb654401002945 0x183 []) (lf2 0xdcb654401002945 0x183 [0x5]))
def F9M3 : BST := BN 142309538 128 (BL 62241331 0) BE
def F9T4 : BTree NodeData := nd (nd (nd (lf 0xd95324401001944 [0xf070006]) (lf 0x1d9324401001344 [0xf070b090c08,0xa])) (nd (lf 0xd97434401001844 [0xb00010b03,0xc]) (lf 0x1cb6544010019c4 [0x10006]))) (nd (nd (lf 0x5cb6544010019c4 [0xb]) (lf 0x9cb6544010019c4 [0x7090004000c])) (nd (lf 0xdcb6544010019c4 [0x7090001070d,0x7030707]) (lf 0x5cf654401001944 [0x50f070004,0x70d])))
def F9M4 : BST := BN 181200337 384 (BN 144331428 256 (BL 62993440 0) BE) (BL 270966375 128)
def F9T5 : BTree NodeData := nd (nd (nd (nd (lf 0x1324401000f43 [0x408040a030d,0x10e0707]) (lf 0x2324401000f03 [0x408040a0707,0x10e])) (nd (lf 0x2324401000f43 [0x4080707040a,0x309010e]) (lf 0x624401000b83 [0x10e04080709,0x707]))) (nd (nd (lf 0x3434401000e43 [0x40a04080303]) (lf 0x3634401000b43 [0x7070408000f,0x10e])) (nd (lf 0x36544010009c3 [0x7070709]) (nd (lf 0x163c801000b63 [0xf010e0610,0x707]) (lf 0x3654c81000973 [0x80707010d,0x11]))))) (nd (nd (nd (lf 0x528c11000d23 [0x20a07070408]) (lf 0x3528c11000d23 [0x20a07070408])) (nd (lf 0x654c91000973 [0x707020a010d,0x6080610]) (nd (lf 0x2658c91000933 [0x61006080707,0x60a0611]) (lf 0x163d491000933 [0x411040a0707])))) (nd (nd (lf 0x132c421000f43 [0x4110707030d,0x408]) (lf 0x343c421000e43 [0x41104080303])) (nd (lf 0x3654ca1000973 [0x7070208020a,0x509]) (nd (lf 0x625463000b23 [0x10a07070408]) (lf 0x3625463000b23 [0x10a07070408])))))
def F9M5 : BST := BN 207787473 0 (BN 166391428 896 (BN 158630085 128 (BL 147804711 384) BE) (BL 180824903 768)) (BN 272988265 640 (BL 243151869 256) (BL 291202998 512))
def F9T6 : BTree NodeData := nd (nd (nd (nd (lf 0x44010007c2 [0x8000a0309,0x10e0307]) (nd (lf 0xc8010007e2 [0x3070210010e,0x309]) (lf 0x4c81000772 [0x3070208010d,0x110010020a,0xe000a0211]))) (nd (lf 0x8c81000732 [0x21003070208,0x12010e]) (nd (lf 0x8c81000772 [0x3070208010e,0x120210]) (lf 0xd0c1000672 [0x21001030208,0x20e020d])))) (nd (nd (lf 0x54c1000572 [0x10903070013,0x8000d000e,0x10]) (nd (lf 0x8c11000762 [0x3070008020a,0x20d020e]) (lf 0x4c91000772 [0x307010d020a,0xe0211]))) (nd (lf 0x8c91000732 [0x2110307020a,0x12000e]) (nd (lf 0x8c91000772 [0x307010e020a,0x20300120211]) (lf 0x14910005b2 [0x11000a0309,0x307000e]))))) (nd (nd (nd (lf 0xd4910005b2 [0xd03070309,0x11000a]) (nd (lf 0xd0d1000672 [0x1030211020a,0x20d020e]) (lf 0xd4d1000572 [0x307000a000f,0xd000e0009]))) (nd (lf 0xc4210007c2 [0x803070309,0x11]) (nd (lf 0x8c61000752 [0x30700100208,0x10e020e020d]) (lf 0x4ca1000772 [0x307010d020a,0x100208])))) (nd (nd (lf 0x8ca1000732 [0x2080307020a,0x12010e]) (nd (lf 0x8ca1000772 [0x307020a010e,0x120208]) (lf 0xd0e1000672 [0x103020a0208,0x20e020d]))) (nd (lf 0x54e1000572 [0x30700080014,0xd000e0109]) (nd (lf 0x5463000762 [0x3070008010a,0x10d010e]) (lf 0x9463000762 [0x3070110000f,0x10d010e0008])))))
def F9M6 : BST := BN 270086771 3968 (BN 215226309 512 (BN 157062566 1024 (BN 145083537 768 (BL 128777135 3712) BE) (BN 204279451 1795 (BL 171732109 1154) BE)) (BN 253166923 1152 (BN 230408860 1664 (BL 215547887 130) BE) (BN 269971457 640 (BL 263260173 1920) BE))) (BN 301556808 1280 (BN 281156766 0 (BN 274531796 1536 (BL 270118589 3840) BE) (BN 297498237 896 (BL 296982701 128) BE)) (BN 320775026 1792 (BN 316521162 256 (BL 306907123 384) BE) (BL 342271519 1408)))
def F9T7 : BTree NodeData := nd (nd (lf 0x10003f1 [0x10701090008,0xe000d0010]) (nd (lf 0x110003f1 [0x1070109000a,0xd000e0011,0x3]) (lf 0x210003f1 [0x80109000a,0xe000d0107]))) (nd (nd (lf 0x13000371 [0x1001070011,0xd000e000a]) (lf 0x23000361 [0x80107])) (nd (lf 0x23000371 [0xa01070008,0xe000d0010]) (lf 0x34300271 [0x3])))
def F9M7 : BST := BN 317676861 515 (BN 253300255 3840 (BN 218452830 0 (BN 195929108 384 (BN 159468921 1282 (BL 135831025 768) (BL 193994768 1792)) (BN 216683005 896 (BL 209484477 128) BE)) (BN 243093912 1411 (BN 234651568 387 (BL 219567004 1664) (BL 240903735 1280)) (BN 244915818 1027 (BL 244203187 640) BE))) (BN 293531834 256 (BN 274311274 3715 (BN 254681590 512 (BL 254092851 1408) (BL 259925225 3328)) (BN 289037454 3459 (BL 280325267 3200) BE)) (BN 309110531 3969 (BN 295613592 1026 (BL 295289621 1152) BE) (BN 312845333 1536 (BL 309622153 389) BE)))) (BN 356039847 1921 (BN 331350258 1281 (BN 323039770 3968 (BN 320023308 3712 (BL 318064497 1413) (BL 321808631 3585)) (BN 326119205 1539 (BL 325406574 1666) BE)) (BN 344570269 1920 (BN 337513290 1668 (BL 332356262 771) (BL 340798606 1795)) (BN 355387704 3456 (BL 349281859 3717) BE))) (BN 379792460 3458 (BN 372015968 3331 (BN 361730453 3457 (BL 357336567 3075) (BL 364008039 3461)) (BN 378775790 3072 (BL 372062747 3587) BE)) (BN 391899176 3460 (BN 386742148 1155 (BL 385736144 1153) BE) (BN 418105563 1024 (BL 414140186 3584) BE))))
def F9T8 : BTree NodeData := lf 0x1f0 [0x70009]
def F9M8 : BST := BN 258375698 130 (BN 223740299 1 (BN 180128270 388 (BN 145602423 642 (BL 121964527 644) BE) (BN 197221289 256 (BL 190969122 771) BE)) (BN 246058727 132 (BN 235479581 384 (BL 227037237 640) BE) (BN 257319372 768 (BL 248645601 386) BE))) (BN 281724128 770 (BN 266696943 128 (BN 265939707 773 (BL 263662121 769) BE) (BN 281423123 896 (BL 273994415 3) BE)) (BN 293830844 772 (BN 288673816 259 (BL 287667812 257) BE) (BL 316071854 0)))
def F9L : Nat → Option (BTree NodeData) | 2 => some F9T2 | 3 => some F9T3 | 4 => some F9T4 | 5 => some F9T5 | 6 => some F9T6 | 7 => some F9T7 | 8 => some F9T8 | _ => none
def F9M : Nat → BST | 3 => F9M3 | 4 => F9M4 | 5 => F9M5 | 6 => F9M6 | 7 => F9M7 | 8 => F9M8 | _ => BE
def tF10 : Sig := 0xfcc0fc00fc000000#64
def F10P : List Row := mkRows [26,26,26,26,26,26,28,28,28,28,28,28,42,42,42,42,42,42,44,44,44,44,44,44,54,54,54,54,54,54]
def F10N : List Row := mkRows [14,22,38,50,52,56,14,22,38,50,52,56,14,22,38,50,52,56,14,22,38,50,52,56,14,22,38,50,52,56]
def F10R : List (Nat × Nat) := [(1057222719,255652815),(1073483712,392000983),(16777215,562436193),(1056968703,988524218),(1073737728,1022611260)]
def F10A : List (List Nat) := [[0,1,2,3,4,5],[0,1,2,3,5,4],[0,2,1,3,4,5],[0,2,1,3,5,4],[0,4,5,3,1,2],[0,4,5,3,2,1],[0,5,4,3,1,2],[0,5,4,3,2,1]]
def F10C : List CutSpec := [⟨0,6,4,1,0,[0,1,2,3,4,5],0xc0c0c0c0c0c0c0c0#64⟩,⟨18,0,2,0,0,[0,1,2,3,4,5],0x333300003333#64⟩,⟨0,48,4,1,0,[0,3,4,5,1,2],0xffff000000000000#64⟩,⟨32,0,3,0,0,[0,1,2,3,4,5],0xffffffff#64⟩,⟨0,8,3,0,0,[0,1,2,3,4,5],0xff00ff00ff00ff00#64⟩,⟨34,0,2,0,0,[0,1,2,3,4,5],0x33333333#64⟩,⟨16,0,3,0,0,[0,1,2,3,4,5],0xffff0000ffff#64⟩,⟨0,16,5,4,0,[0,4,5,3,1,2],0xffff0000ffff0000#64⟩,⟨2,8,2,0,0,[0,1,2,3,4,5],0x3300330033003300#64⟩,⟨0,32,5,4,0,[0,4,5,3,2,1],0xffffffff00000000#64⟩,⟨36,0,2,0,0,[0,1,2,3,4,5],0xf0f0f0f#64⟩,⟨0,20,2,0,0,[0,1,2,3,4,5],0xf0f00000f0f00000#64⟩,⟨2,4,2,0,0,[0,1,2,3,4,5],0x3030303030303030#64⟩,⟨32,8,2,0,0,[0,1,2,3,4,5],0xff00ff00#64⟩,⟨4,0,3,0,0,[0,1,2,3,4,5],0xf0f0f0f0f0f0f0f#64⟩,⟨16,8,2,0,0,[0,1,2,3,4,5],0xff000000ff00#64⟩,⟨2,0,3,0,0,[0,1,2,3,4,5],0x3333333333333333#64⟩,⟨0,2,5,4,0,[0,1,2,3,4,5],0xcccccccccccccccc#64⟩,⟨20,0,2,0,0,[0,1,2,3,4,5],0xf0f00000f0f#64⟩,⟨0,56,1,0,0,[0,1,2,3,4,5],0xff00000000000000#64⟩,⟨36,16,1,0,0,[0,1,2,3,4,5],0xf0f0000#64⟩,⟨16,32,2,0,0,[0,1,2,3,4,5],0xffff00000000#64⟩,⟨4,8,2,0,0,[0,1,2,3,4,5],0xf000f000f000f00#64⟩,⟨0,4,5,4,0,[0,2,1,3,4,5],0xf0f0f0f0f0f0f0f0#64⟩,⟨2,48,1,0,0,[0,1,2,3,4,5],0x3333000000000000#64⟩,⟨4,10,1,0,0,[0,1,2,3,4,5],0xc000c000c000c00#64⟩,⟨0,18,2,0,0,[0,1,2,3,4,5],0xcccc0000cccc0000#64⟩]
def F10T3 : BTree NodeData := lf 0x1d13294c1001404 [0xc01]
def F10T4 : BTree NodeData := nd (nd (nd (nd (nd (lf 0x2650c81000983 [0x5030002]) (lf 0x2631481000b03 [0x1040002])) (nd (lf 0x2651481000983 [0x50703]) (lf 0x2631481000b43 [0x40100020006]))) (nd (nd (lf 0x635481000943 [0x70005]) (lf 0x26390c1000a43 [0x2])) (nd (lf 0x23214c1000d03 [0x108]) (lf 0x16214c1000b83 [0x600090002,0x10a0401])))) (nd (nd (nd (lf 0x26214c1000b83 [0x40100060002]) (lf 0x13294c1000d03 [0x108])) (nd (lf 0x16294c1000983 [0x50703]) (lf 0x2630841000b03 [0x1040002]))) (nd (nd (lf 0x2630841000b43 [0x2000b]) (lf 0x1620c41000b83 [0x204010503,0xc])) (nd (lf 0x2620c41000b83 [0x40100020503]) (lf 0x2519402000d83 [0xe000d0002]))))) (nd (nd (nd (nd (lf 0x2539402000d23 [0x401]) (lf 0x26014c20009a3 [0x7000d0006])) (nd (lf 0x26114c2000993 [0x7000f0006]) (lf 0x2540c02000ce3 [0x508]))) (nd (nd (lf 0x26114c20009d3 [0x700110010]) (lf 0x538852000d03 [0x10])) (nd (lf 0x265cc62000983 [0x503]) (lf 0x263d462000b03 [0x2])))) (nd (nd (nd (lf 0x15314e2000d23 [0x108]) (lf 0x23214e2000d23 [0x108])) (nd (lf 0x23094e2000d23 [0x108]) (lf 0x26494e20008f3 [0x6120007]))) (nd (nd (lf 0x6154830009c3 [0x50603]) (lf 0x6454830008e3 [0x406080005,0x413])) (nd (lf 0x6154830009d3 [0xf06030010]) (lf 0x2619483000993 [0xf06030612])))))
def F10T5_0 := nd (nd (nd (nd (nd (lf 0xc81000782 [0x1030002]) (lf 0xc810007c2 [0x1401030002,0x7])) (nd (lf 0xcc81000782 [0x1030002]) (nd (lf 0xcc810007c2 [0x501030002,0x7]) (lf 0x1481000782 [0x10800060002,0x10a])))) (nd (nd (lf 0x14810007c2 [0x100060002,0x5010a0108]) (nd (lf 0x54810005c2 [0x703030005,0x4]) (lf 0xd481000582 [0xe00020303]))) (nd (lf 0xd481000782 [0x60002]) (nd (lf 0xd4810005c2 [0x3080002000e,0x7]) (lf 0xd4810007c2 [0x100060002]))))) (nd (nd (nd (lf 0x10c1000642 [0x10302010002]) (lf 0x10c1000742 [0x10a0006])) (nd (lf 0x90c10006c2 [0x2]) (nd (lf 0x14c10005c2 [0x1030010]) (lf 0x14c10007c2 [0x100090015,0x2])))) (nd (nd (lf 0x94c10005c2 [0x100016]) (nd (lf 0x841000782 [0xb0013]) (lf 0x8410007c2 [0x1000b0013,0x5]))) (nd (lf 0x8841000782 [0xb0013]) (nd (lf 0x88410007c2 [0x1000b0013,0x5]) (lf 0xc410007c2 [0x1701030002,0x1])))))) (nd (nd (nd (nd (lf 0xd4810005a2 [0x2180303000f]) (lf 0xd4810005e2 [0x218000f000e,0x700020308])) (nd (lf 0x14c10005e2 [0x100015]) (nd (lf 0x8821000782 [0xe0002]) (lf 0x88210007c2 [0x500060002,0x12])))) (nd (nd (lf 0xc210007c2 [0x1001030009]) (nd (lf 0x94210005c2 [0x203030001,0x700050006,0x4]) (lf 0x54a1000592 [0xe00100212,0x30a]))) (nd (lf 0x54a10005d2 [0x212000e0010]) (nd (lf 0x94e10005d2 [0x100019]) (lf 0x94020005a2 [0xe00020001,0x308]))))) (nd (nd (nd (lf 0x94020007a2 [0xe00010002,0x30a]) (lf 0x9442000592 [0xf03030212,0xd])) (nd (lf 0x9442000792 [0xd00060002]) (nd (lf 0x14c20005b2 [0x702010006]) (lf 0x54c2000732 [0x2001a])))) (nd (nd (lf 0x94c2000532 [0x600070201,0x30a]) (nd (lf 0x94c2000732 [0x6001a]) (lf 0x94c20005b2 [0x20101030002]))) (nd (lf 0x88020007e2 [0x1000010005,0xe0017]) (nd (lf 0xc02000762 [0x1100010006,0x800050010]) (lf 0xc020007e2 [0x101080010,0x13]))))))
def F10T5_1 := nd (nd (nd (nd (nd (lf 0x94020005e2 [0x20001000e,0x70308]) (lf 0x8842000792 [0xe00020010,0x6020a0208,0x1])) (nd (lf 0x94420005d2 [0x600130001,0x30a03080002,0x5000b0017]) (nd (lf 0x94420007d2 [0x11802120011,0x17]) (lf 0xcc82000732 [0x60002001a])))) (nd (nd (lf 0x14c20005f2 [0x1400110010,0x1b00070018,0xa001a]) (nd (lf 0x94c2000572 [0x2010006001a,0x30a]) (lf 0x94c20005f2 [0x1000190007]))) (nd (lf 0x8852000782 [0xe0010]) (nd (lf 0x14520005c2 [0xe00100001,0x308]) (lf 0x14d2000562 [0x10000e0001,0x30a]))))) (nd (nd (nd (lf 0x14d20005e2 [0x101030010]) (lf 0xc62000782 [0x1030002])) (nd (lf 0xc620007a2 [0x11801030002]) (nd (lf 0xcc62000782 [0x501180103]) (lf 0x1462000782 [0xe0002])))) (nd (nd (lf 0x14620007a2 [0x1000e0002,0xf]) (nd (lf 0x94620005a2 [0x303000f]) (lf 0x94620007a2 [0xe0002000d,0x30a00130308,0xb]))) (nd (lf 0xd462000782 [0xe0002]) (nd (lf 0x14e20007a2 [0x108000d000e]) (lf 0x94e20007a2 [0x1300020019])))))) (nd (nd (nd (nd (lf 0x8862000782 [0xe0010]) (lf 0x88620007a2 [0x118000e0010,0xf])) (nd (lf 0x94620005e2 [0x1000b0013,0x5]) (nd (lf 0xcca20007a2 [0x501030017]) (lf 0x14e20005e2 [0x13000e])))) (nd (nd (lf 0x94e20005e2 [0x1000130014,0x12]) (nd (lf 0xc220007a2 [0x101030011]) (lf 0x14e20005b2 [0x1101030201,0x7]))) (nd (lf 0x94e20005b2 [0x202010019]) (nd (lf 0x8c22000762 [0x10103]) (lf 0x14e20005f2 [0x500070011,0x1b00190212]))))) (nd (nd (nd (lf 0x94e20005f2 [0x21200140002,0x501080010,0xa]) (nd (lf 0x94430005e2 [0x102030013,0x50007]) (lf 0x54830007a2 [0x1302030010]))) (nd (lf 0x54830005e2 [0x1302030005,0x12]) (nd (lf 0x94830007a2 [0x208001b0010]) (lf 0x54830005b2 [0x2030201001b])))) (nd (nd (lf 0x54830005f2 [0x20302010009,0x70010]) (nd (lf 0x94830005b2 [0x1002030201]) (lf 0x94830005f2 [0x700100009]))) (nd (lf 0x54a3000532 [0x500030201]) (nd (lf 0x54a3000572 [0x302010005]) (lf 0x9523000472 [0x500030201]))))))
def F10T5 : BTree NodeData := nd F10T5_0 F10T5_1
def F10M5 : BST := BN 205669594 3329 (BN 172777833 1024 (BN 106671043 770 (BN 91930478 3712 (BN 70348595 512 (BL 49247754 2688) (BL 91053167 3201)) (BN 102235045 3330 (BL 94404371 2689) BE)) (BN 131909399 1280 (BN 120492170 1664 (BL 113707819 896) (BL 129726491 2560)) (BN 168481901 3328 (BL 139485972 128) BE))) (BN 184727835 513 (BN 179741290 0 (BN 172917899 768 (BL 172802342 2180) (BL 175691224 2944)) (BN 184674236 4 (BL 183872357 2048) BE)) (BN 191531303 3968 (BN 188475093 2304 (BL 188308355 3072) BE) (BN 199351854 3073 (BL 194915856 2049) BE)))) (BN 254703839 1792 (BN 243144574 2822 (BN 224052804 2818 (BN 216750997 1920 (BL 210105592 769) (BL 218070616 2176)) (BN 239875638 1152 (BL 226459260 3840) BE)) (BN 245759261 3972 (BN 244311636 640 (BL 243416932 1670) BE) (BN 253737107 256 (BL 251629136 3713) BE))) (BN 287534062 2432 (BN 266453294 1408 (BN 256344548 2816 (BL 255134471 1156) (BL 259570469 644)) (BN 278734402 1924 (BL 272835372 3584) BE)) (BN 329498551 1798 (BN 323541326 129 (BL 310406781 1794) BE) (BN 347723560 3456 (BL 341785710 3200) BE))))
def F10T6 : BTree NodeData := nd (nd (nd (lf 0x10003c1 [0x10103]) (nd (lf 0x10003e1 [0x1301030001,0xb]) (lf 0x210003d1 [0x10300180002,0x60012]))) (nd (lf 0x20003b1 [0x201030001,0x6]) (nd (lf 0x20003f1 [0x2001a0001,0x10a01080006,0xa00080009]) (lf 0x120003e1 [0xe00100001,0x108])))) (nd (nd (lf 0x220003a1 [0x1180103]) (nd (lf 0x220003e1 [0xe01030010,0x1201180017]) (lf 0x220003b1 [0x201030001,0x6]))) (nd (nd (lf 0x220003f1 [0xe00100001,0x2010a0108,0xa00080006]) (lf 0x30003e1 [0x1300100003,0x120118])) (nd (lf 0x30003f1 [0x1000030001,0x9001b0007]) (lf 0x23000371 [0x900010003]))))
def F10M6 : BST := BN 239012259 2689 (BN 187494886 640 (BN 166792778 3200 (BN 155794635 15489 (BN 138996019 4608 (BN 123471245 5120 (BN 115034730 1281 (BL 110638018 15488) BE) (BN 129726491 512 (BL 129526073 2561) BE)) (BN 147780499 6656 (BN 144001568 6657 (BL 140891309 1537) BE) (BL 149744376 2564))) (BN 163467535 6400 (BN 158552167 7937 (BN 157642016 7936 (BL 157062681 384) BE) (BL 162752966 7940)) (BN 165074927 5760 (BN 165064163 641 (BL 164277172 14721) BE) (BL 166281971 1409)))) (BN 177238340 5248 (BN 172777833 13312 (BN 169510925 2432 (BN 167903533 14592 (BL 167821695 16129) BE) (BL 170871067 4738)) (BN 176800752 7296 (BN 175039895 5888 (BL 172802342 1792) BE) (BL 177213831 7168))) (BN 181535421 1536 (BN 180848516 4737 (BN 179003573 5634 (BL 177975497 3584) BE) (BL 181202018 5376)) (BN 183439571 13826 (BN 182411495 7680 (BL 181711919 1280) BE) (BL 184114523 0))))) (BN 216254500 768 (BN 202531341 4100 (BN 196012921 2944 (BN 188550521 4096 (BN 188065228 1 (BL 187890234 4612) BE) (BN 192616604 4224 (BL 192501226 4097) BE)) (BN 198658242 3968 (BN 198200627 4736 (BL 198095343 4) BE) (BL 202165311 2305))) (BN 209334681 7552 (BN 206197330 15873 (BN 205944242 2304 (BL 203094240 8064) BE) (BL 206583359 4609)) (BN 215318939 5632 (BN 215226424 4480 (BL 214016947 15616) BE) (BL 215925116 2560)))) (BN 230874952 5505 (BN 222993138 3202 (BN 220690498 3840 (BN 219754937 13824 (BL 218452945 128) BE) (BL 221365450 14468)) (BN 225316155 14470 (BN 224063943 15104 (BL 223549441 15872) BE) (BL 229567982 7809))) (BN 234498884 16128 (BN 231572781 16001 (BN 231550949 4992 (BL 230941576 256) BE) (BL 234251011 7425)) (BN 235377574 4352 (BN 234801735 13952 (BL 234641192 14849) BE) (BL 238420123 14848)))))) (BN 289201720 14464 (BN 265584598 2052 (BN 256364370 2688 (BN 249659210 14080 (BN 243678818 16256 (BN 242730247 13568 (BL 242504641 14976) BE) (BN 247166245 3328 (BL 246492828 3586) BE)) (BN 252569866 4226 (BN 250928826 7682 (BL 250823677 2306) BE) (BL 254095208 13440))) (BN 262884352 13697 (BN 260105859 4482 (BN 259775630 4864 (BL 258050822 14726) BE) (BL 262013183 2816)) (BN 264737212 15874 (BN 264211628 2176 (BL 263417457 3072) BE) (BL 264889151 3457)))) (BN 273914245 2690 (BN 267853455 15360 (BN 266449181 6272 (BN 265796144 16132 (BL 265614081 14336) BE) (BL 267320350 15745)) (BN 270050079 1024 (BN 270020596 6148 (BL 269325149 897) BE) (BL 271416941 14720))) (BN 280007556 1408 (BN 275722885 3712 (BN 275306577 6785 (BL 275112117 13184) BE) (BL 275821011 258)) (BN 288288907 6784 (BN 283828982 15878 (BL 280257009 4354) BE) (BL 288539878 2049))))) (BN 342016672 1153 (BN 300668384 1664 (BN 295689414 7424 (BN 293253738 2048 (BN 293170739 1284 (BL 292975876 6145) BE) (BL 294620101 15232)) (BN 297689736 6144 (BN 297603251 14724 (BL 297552141 5504) BE) (BL 299056099 1920))) (BN 334881229 6912 (BN 325790805 6529 (BN 325117048 2310 (BL 313152736 7553) BE) (BL 330504665 6528)) (BN 339317227 1152 (BN 337580674 6913 (BL 336707751 7808) BE) (BL 340719383 6790)))) (BN 370024121 13696 (BN 359095249 5889 (BN 356690975 6532 (BN 352075200 14465 (BL 345298366 16000) BE) (BL 356857696 1793)) (BN 366127224 14081 (BN 361466094 7040 (BL 361293694 5249) BE) (BL 367029375 15105))) (BN 380974078 6016 (BN 374460119 15744 (BN 370563222 13441 (BL 370499361 5508) BE) (BL 378614736 3456)) (BN 419564455 6534 (BN 385410076 14208 (BL 383050734 896) BE) (BL 433372841 2694))))))
def F10T7 : BTree NodeData := lf 0x1f0 [0x30001]
def F10M7 : BST := BN 259357792 1414 (BN 228183042 1792 (BN 201219903 1536 (BN 190379051 130 (BN 181202018 0 (BL 165584142 1409) (BL 186865963 1926)) (BN 200093370 1542 (BL 194815049 642) (BL 200293788 4))) (BN 217259870 1413 (BN 212990748 1924 (BL 209563316 516) (BL 214016947 128)) (BN 218600884 1411 (BL 218452945 640) BE))) (BN 249570870 256 (BN 235952995 1410 (BN 232261331 1408 (BL 231311053 1538) (BL 234727318 1922)) (BN 242651051 1920 (BL 239365761 512) (BL 248542794 1666))) (BN 258447641 1412 (BN 254006868 768 (BL 252978792 386) (BL 254681820 260)) (BN 259117818 772 (BL 258632525 262) BE)))) (BN 300093676 1798 (BN 284245196 514 (BN 267495099 1415 (BN 263068523 774 (BL 260745506 1794) (BL 263144985 1796)) (BN 276764627 899 (BL 268627320 897) (BL 277150656 518))) (BN 290322234 770 (BN 286492413 1540 (BL 285886236 258) (BL 286964167 132)) (BN 294116738 898 (BL 291400165 644) BE))) (BN 346469106 1921 (BN 326041275 1925 (BN 317060125 1664 (BL 313058945 1927) (BL 321496123 384)) (BN 335304509 896 (BL 334185691 1923) BE)) (BN 363543173 390 (BN 354273645 646 (BL 349837647 134) (BL 359107175 1670)) (BN 368257033 388 (BL 363821035 1668) BE))))
def F10L : Nat → Option (BTree NodeData) | 3 => some F10T3 | 4 => some F10T4 | 5 => some F10T5 | 6 => some F10T6 | 7 => some F10T7 | _ => none
def F10M : Nat → BST | 5 => F10M5 | 6 => F10M6 | 7 => F10M7 | _ => BE
def tF11 : Sig := 0xe8e8808080800000#64
def F11P : List Row := mkRows [23,23,23,23,23,23,23,23,23,23,39,39,39,39,39,39,39,39,39,39,51,51,51,51,51,51,51,51,51,51,53,53,53,53,53,53,53,53,53,53,54,54,54,54,54,54,54,54,54,54]
def F11N : List Row := mkRows [7,19,21,22,35,37,38,49,50,52,7,19,21,22,35,37,38,49,50,52,7,19,21,22,35,37,38,49,50,52,7,19,21,22,35,37,38,49,50,52,7,19,21,22,35,37,38,49,50,52]
def F11R : List (Nat × Nat) := [(1099511627775,201407314713783),(1124801468956671,381903487462747),(1125898834149375,683464166323821),(1125899905795071,1001533641472910),(1125899906841600,1109391110554608)]
def F11A : List (List Nat) := [[0,1,2,3,4,5],[0,1,2,3,5,4],[0,1,4,3,2,5],[0,1,4,3,5,2],[0,1,5,3,2,4],[0,1,5,3,4,2],[0,2,1,3,4,5],[0,2,1,3,5,4],[0,2,4,3,1,5],[0,2,4,3,5,1],[0,2,5,3,1,4],[0,2,5,3,4,1],[0,4,1,3,2,5],[0,4,1,3,5,2],[0,4,2,3,1,5],[0,4,2,3,5,1],[0,4,5,3,1,2],[0,4,5,3,2,1],[0,5,1,3,2,4],[0,5,1,3,4,2],[0,5,2,3,1,4],[0,5,2,3,4,1],[0,5,4,3,1,2],[0,5,4,3,2,1],[1,0,2,3,4,5],[1,0,2,3,5,4],[1,0,4,3,2,5],[1,0,4,3,5,2],[1,0,5,3,2,4],[1,0,5,3,4,2],[1,2,0,3,4,5],[1,2,0,3,5,4],[1,2,4,3,0,5],[1,2,4,3,5,0],[1,2,5,3,0,4],[1,2,5,3,4,0],[1,4,0,3,2,5],[1,4,0,3,5,2],[1,4,2,3,0,5],[1,4,2,3,5,0],[1,4,5,3,0,2],[1,4,5,3,2,0],[1,5,0,3,2,4],[1,5,0,3,4,2],[1,5,2,3,0,4],[1,5,2,3,4,0],[1,5,4,3,0,2],[1,5,4,3,2,0],[2,0,1,3,4,5],[2,0,1,3,5,4],[2,0,4,3,1,5],[2,0,4,3,5,1],[2,0,5,3,1,4],[2,0,5,3,4,1],[2,1,0,3,4,5],[2,1,0,3,5,4],[2,1,4,3,0,5],[2,1,4,3,5,0],[2,1,5,3,0,4],[2,1,5,3,4,0],[2,4,0,3,1,5],[2,4,0,3,5,1],[2,4,1,3,0,5],[2,4,1,3,5,0],[2,4,5,3,0,1],[2,4,5,3,1,0],[2,5,0,3,1,4],[2,5,0,3,4,1],[2,5,1,3,0,4],[2,5,1,3,4,0],[2,5,4,3,0,1],[2,5,4,3,1,0],[4,0,1,3,2,5],[4,0,1,3,5,2],[4,0,2,3,1,5],[4,0,2,3,5,1],[4,0,5,3,1,2],[4,0,5,3,2,1],[4,1,0,3,2,5],[4,1,0,3,5,2],[4,1,2,3,0,5],[4,1,2,3,5,0],[4,1,5,3,0,2],[4,1,5,3,2,0],[4,2,0,3,1,5],[4,2,0,3,5,1],[4,2,1,3,0,5],[4,2,1,3,5,0],[4,2,5,3,0,1],[4,2,5,3,1,0],[4,5,0,3,1,2],[4,5,0,3,2,1],[4,5,1,3,0,2],[4,5,1,3,2,0],[4,5,2,3,0,1],[4,5,2,3,1,0],[5,0,1,3,2,4],[5,0,1,3,4,2],[5,0,2,3,1,4],[5,0,2,3,4,1],[5,0,4,3,1,2],[5,0,4,3,2,1],[5,1,0,3,2,4],[5,1,0,3,4,2],[5,1,2,3,0,4],[5,1,2,3,4,0],[5,1,4,3,0,2],[5,1,4,3,2,0],[5,2,0,3,1,4],[5,2,0,3,4,1],[5,2,1,3,0,4],[5,2,1,3,4,0],[5,2,4,3,0,1],[5,2,4,3,1,0],[5,4,0,3,1,2],[5,4,0,3,2,1],[5,4,1,3,0,2],[5,4,1,3,2,0],[5,4,2,3,0,1],[5,4,2,3,1,0]]
def F11C : List CutSpec := [⟨0,18,4,1,0,[3,0,4,1,2,5],0xcccc0000cccc0000#64⟩,⟨0,4,7,5,0,[1,2,0,3,4,5],0xf0f0f0f0f0f0f0f0#64⟩,⟨0,20,4,1,0,[3,4,0,1,2,5],0xf0f00000f0f00000#64⟩,⟨0,3,4,1,0,[0,1,3,2,4,5],0x8888888888888888#64⟩,⟨0,2,7,5,0,[1,0,2,3,4,5],0xcccccccccccccccc#64⟩,⟨0,32,7,5,0,[1,2,4,0,5,3],0xffffffff00000000#64⟩,⟨0,16,7,5,0,[1,2,4,0,3,5],0xffff0000ffff0000#64⟩,⟨0,5,4,1,0,[0,3,1,2,4,5],0xa0a0a0a0a0a0a0a0#64⟩,⟨0,6,4,1,0,[3,0,1,2,4,5],0xc0c0c0c0c0c0c0c0#64⟩,⟨0,17,4,1,0,[0,3,4,1,2,5],0xaaaa0000aaaa0000#64⟩,⟨0,1,7,5,0,[0,1,2,3,4,5],0xaaaaaaaaaaaaaaaa#64⟩]
def F11T3 : BTree NodeData := nd (lf2 0x10c210801007806 0x19053 [0x1]) (nd (lf2 0xc8310801006c06 0xa1254 []) (lf2 0x990310801006246 0x9d283 []))
def F11T4 : BTree NodeData := nd (nd (nd (nd (lf2 0x10c210801003d05 0x53 []) (lf2 0x10c210801002d85 0x85 [0x2])) (nd (lf2 0x14c210801003d05 0x343 []) (nd (lf2 0x14c210801003985 0x64 [0x1]) (lf2 0x14c210801003985 0x264 [])))) (nd (nd (lf2 0x14c210801002d85 0x284 []) (lf2 0x94c210801003985 0x264 [])) (nd (lf2 0x94c210801002d85 0x284 []) (nd (lf2 0xc8310801003d05 0x54 [0x3]) (lf2 0xc8310801003d05 0x254 [0x4]))))) (nd (nd (nd (lf2 0x108310801003e05 0x43 []) (lf2 0x990310801002b45 0x283 [0x5])) (nd (lf2 0x9903108010032c5 0x274 []) (nd (lf2 0xd0c530801002d25 0x282 []) (lf2 0x1d8540c810021e5 0x280 [])))) (nd (nd (lf2 0x9ca540c810030b5 0x264 []) (nd (lf2 0x9c0650c810031c5 0x271 []) (lf2 0x9c0650c810030e5 0x174 []))) (nd (lf2 0x1933214810021b5 0x187 []) (nd (lf2 0x58c631481002875 0x84 [0xb06]) (lf2 0x9d2631481003075 0x243 [0x706])))))
def F11M4 : BST := BN 267723747 98 (BN 200782798 24 (BN 199393116 420 (BL 187155387 128) BE) (BL 217755868 396)) (BN 279724706 134 (BN 275622864 0 (BL 269887138 410) BE) (BL 349729966 384))
def F11T5_0 := nd (nd (nd (nd (lf 0x10c210801001f84 [0x80207070805,0x900080004]) (nd (lf 0x14c210801001d84 [0x100040902,0xa]) (lf 0x14c210801001f84 [0x109020004,0xa]))) (nd (lf 0x94c210801001d84 [0x807070004,0x9]) (nd (lf 0xc8310801001f04 [0x300080004,0x1]) (lf 0x108310801001f84 [])))) (nd (nd (lf 0x1c8310801001f84 [0x10009040b]) (nd (lf 0x150310801001dc4 []) (lf 0x950310801001dc4 []))) (nd (lf 0x190310801001bc4 [0x1]) (nd (lf 0x990310801001bc4 [0x8]) (lf 0x1d44308010015e4 [0x2]))))) (nd (nd (nd (lf 0xc8530801001da4 [0x2]) (nd (lf 0x9c8530801001da4 [0x20004000a]) (lf 0xd0c530801001d64 []))) (nd (lf 0x1905308010019e4 [0x1]) (nd (lf 0x9905308010019e4 []) (lf 0x9d05308010015e4 [0xd02])))) (nd (nd (lf 0x9c85308010017a4 [0x2000a]) (nd (lf 0xca530801001da4 [0x307]) (lf 0x9925308010019e4 []))) (nd (nd (lf 0x9d25308010015e4 [0x2]) (lf 0x184600c81001bc4 [0x60b0d020a05])) (nd (lf 0x1d8540c810011f4 []) (lf 0x9d8540c810011f4 [0xd02])))))
def F11T5_1 := nd (nd (nd (nd (lf 0x9ca540c810015b4 [0x7]) (nd (lf 0x992540c810018f4 []) (lf 0x9da540c810011f4 []))) (nd (lf 0x9c0650c810019e4 [0x5]) (nd (lf 0x5d0650c810018f4 []) (lf 0x9d0650c810010f4 [])))) (nd (nd (lf 0x9d0650c810018f4 [0x6]) (nd (lf 0x9d0650c810011f4 []) (lf 0x9c8650c810015b4 [0x2]))) (nd (nd (lf 0x9d0650c810014f4 [0xd02]) (lf 0x9c2650c810013e4 [0x5])) (nd (lf 0x9d6650c810011f4 [0x6]) (lf 0x1933214810019b4 [0x7]))))) (nd (nd (nd (lf 0x9933214810019b4 []) (nd (lf 0x9d33214810015b4 []) (lf 0x5db3214810015b4 [0x80009]))) (nd (lf 0x9c06314810015e4 [0x5]) (nd (lf 0x58c631481001974 [0x307]) (lf 0x9d06314810014f4 [])))) (nd (nd (lf 0x8ca631481001974 [0x2]) (nd (lf 0x9d26314810011f4 []) (lf 0xd8e631481001974 [0x307]))) (nd (nd (lf 0xd4e631481001974 []) (lf 0x8ca639481001974 [0x2])) (nd (lf 0xd0e639481001974 []) (lf 0x9d26394810011f4 [])))))
def F11T5 : BTree NodeData := nd F11T5_0 F11T5_1
def F11M5 : BST := BN 299651975 3480 (BN 247781912 1408 (BN 220290996 3615 (BN 213375966 676 (BN 208261294 3596 (BN 184974237 3736 (BL 180205894 3784) BE) (BL 209464660 3840)) (BN 217657016 3614 (BN 217180737 1304 (BL 215188062 896) BE) (BL 217832111 768))) (BN 239173521 670 (BN 236885135 1692 (BN 231738718 652 (BL 221702389 1188) BE) (BL 237782830 512)) (BN 245961449 1159 (BN 240065141 1164 (BL 239885664 3760) BE) (BL 247252776 0)))) (BN 280462030 1539 (BN 258535840 1414 (BN 252258325 1560 (BN 251505900 1420 (BL 249148066 3608) BE) (BL 253410748 386)) (BN 274241073 30 (BN 273882919 12 (BL 271714486 1280) BE) (BL 274771194 3876))) (BN 289857752 1561 (BN 283520239 646 (BN 281665396 1792 (BL 281575924 3598) BE) (BL 286265439 270)) (BN 295214971 3900 (BN 295131062 3591 (BL 290642906 6) BE) (BL 295757968 384))))) (BN 327098391 1536 (BN 306718936 446 (BN 303582595 1852 (BN 302210987 1541 (BN 300119653 444 (BL 299957593 3808) BE) (BL 303375963 3528)) (BN 304885989 1038 (BN 304408564 3456 (BL 303681815 3584) BE) (BL 304992500 1545))) (BN 321310427 1664 (BN 310405903 3504 (BN 308371330 256 (BL 307336783 1828) BE) (BL 316283946 128)) (BN 324928780 3968 (BN 322863057 46 (BL 322477756 3846) BE) (BL 326991880 1024)))) (BN 357572012 1834 (BN 345894332 1798 (BN 333910403 1054 (BN 331900625 20 (BL 330670112 3638) BE) (BL 338049482 31)) (BN 354086688 1585 (BN 348660612 1 (BL 346190161 1552) BE) (BL 355121218 1044))) (BN 387091993 1811 (BN 372397894 640 (BN 371204761 1668 (BL 370665166 1036) BE) (BL 379179208 3712)) (BN 412889548 7 (BN 396462721 1030 (BL 392483016 1152) BE) (BL 428380059 1632)))))
def F11T6 : BTree NodeData := nd (nd (nd (nd (lf 0x210801000f83 [0x40b00080004,0x907060707,0x205]) (lf 0x310801000fc3 [0x50203070004,0x10008])) (nd (lf 0x430801000fe3 [0x800040405,0x3070402]) (nd (lf 0x530801000de3 [0x4000a0502,0x1]) (lf 0x530801000fe3 [0xa05020004,0x1])))) (nd (nd (lf 0x2530801000de3 [0x30705020004,0x8]) (nd (lf 0x600c81000fe3 [0x3000a0605,0x80502]) (lf 0x540c81000df3 [0x405040b0003,0x5060502]))) (nd (lf 0x2540c81000df3 [0x50200030004,0x506]) (nd (lf 0x650c810009f3 [0x605060b0006,0x5070502]) (lf 0x650c81000df3 [0x402060502]))))) (nd (nd (nd (lf 0x2650c81000bf3 [0x605]) (lf 0x321481000df3 [0x403020007])) (nd (lf 0x3321481000db3 [0x102]) (nd (lf 0x631481000df3 [0x70306]) (lf 0x26314810009f3 [0x60b07060307,0x40605])))) (nd (nd (lf 0x2631481000df3 [0x800090307,0x4]) (nd (lf 0x3321481000fb3 [0x102]) (lf 0x531481000df3 [0x60505070302]))) (nd (lf 0x2631481000bf3 [0x60501070009,0x8]) (nd (lf 0x329481000df3 [0x102]) (lf 0x26394810009f3 [0x603070004])))))
def F11M6 : BST := BN 350201994 1054 (BN 309227121 2688 (BN 289458775 2048 (BN 259796106 7936 (BN 248642810 7730 (BN 243796175 7452 (BN 241873570 6657 (BL 235685239 3620) BE) (BL 243877595 3358)) (BN 254047991 3596 (BL 251078535 1025) (BL 257491446 1024))) (BN 275720021 130 (BN 267352884 2062 (BL 261482794 3614) (BL 273840899 2561)) (BN 285152397 7708 (BL 284830149 1820) (BL 288399408 1792)))) (BN 304562132 8064 (BN 296812917 7476 (BN 295122720 6414 (BL 294890312 3591) (BL 295471903 6786)) (BN 302137848 6656 (BL 299957593 7296) (BL 302501843 6784))) (BN 307051350 2060 (BN 305143974 1920 (BL 304626146 3334) (BL 305829512 3590)) (BN 308254716 3072 (BL 307885975 1572) (BL 308350127 6400))))) (BN 329131571 7756 (BN 318067241 128 (BN 314749253 6275 (BN 312668141 2079 (BN 309740818 2176 (BL 309557882 1055) BE) (BL 313322780 282)) (BN 316447072 2078 (BL 316078331 1305) (BL 317820073 2575))) (BN 326248727 1548 (BN 323279271 2049 (BL 318311920 3840) (BL 325431727 1480)) (BN 328809323 131 (BL 326857641 1543) (BL 329048255 1030)))) (BN 342305016 1664 (BN 333683530 1566 (BN 331685532 258 (BL 331106568 7754) (BL 332848905 2054)) (BN 338169139 7732 (BL 336505877 5844) (BL 342281783 6912))) (BN 347067495 6272 (BN 345181044 2330 (BL 344209752 256) (BL 346974268 5948)) (BN 348872708 2354 (BL 347436858 538) (BL 349398773 548)))))) (BN 378115801 7428 (BN 367062550 2944 (BN 362413569 7218 (BN 359632056 7196 (BN 358178169 7939 (BN 357591129 5888 (BL 352775300 1651) BE) (BL 358721905 7194)) (BN 361210203 2573 (BL 360965040 1432) (BL 361812868 1645))) (BN 364962401 1176 (BN 364091631 1031 (BL 363543796 2306) (BL 364404831 2304)) (BN 365721629 1408 (BL 365698359 3335) (BL 366333559 794)))) (BN 373234413 6150 (BN 368686389 1224 (BN 367748086 3456 (BL 367444382 3610) (BL 367759473 7168)) (BN 371337570 3712 (BL 369718990 1152) (BL 371718968 1456))) (BN 375196328 542 (BN 374338584 2560 (BL 374249112 3328) (BL 374676281 5784)) (BN 376826882 1281 (BL 375716329 1200) (BL 378030248 1542))))) (BN 411522141 7552 (BN 397559177 7680 (BN 387508207 2055 (BN 384519460 0 (BL 378938627 7424) (BL 384696311 770)) (BN 391270978 385 (BL 390309178 1378) (BL 392501953 270))) (BN 400009971 1562 (BN 399947447 1586 (BL 397665688 1280) (BL 399982266 512)) (BN 403307765 6175 (BL 400069947 562) (BL 407086696 6174)))) (BN 422175838 6144 (BN 419149775 1796 (BN 415150944 3584 (BL 412648798 7220) (BL 415519502 640)) (BN 419472023 7684 (BL 419227909 2581) (BL 421589053 3200))) (BN 440115770 5760 (BN 427893715 6151 (BL 424814647 768) (BL 438567520 1536)) (BN 467030018 7686 (BL 455996334 6145) (BL 483456845 2579))))))
def F11T7 : BTree NodeData := nd (nd (lf 0x8010007e2 [0x802050102,0x30603070004]) (lf 0xc810007f2 [0x20b01020205,0x300040107,0x1060206])) (nd (lf 0x14810005f2 [0x307020b0009,0x400080306]) (nd (lf 0x14810007f2 [0x30700090004,0x802050306,0x20b]) (lf 0x94810005f2 [0x30701020004,0x306])))
def F11M7 : BST := BN 400927904 1024 (BN 352838047 1036 (BN 332050091 768 (BN 302436857 647 (BN 281155036 1564 (BN 264459130 1793 (BL 258129877 3969) BE) (BN 295173145 284 (BL 293573463 1610) BE)) (BN 328561642 646 (BN 328058743 256 (BL 321645832 257) BE) (BL 329981348 3712))) (BN 342667651 1566 (BN 334475295 1060 (BN 334250715 1025 (BL 334171778 1588) BE) (BL 339279064 188)) (BN 349868591 0 (BN 347832225 1562 (BL 344654974 540) BE) (BL 351523889 1586)))) (BN 384198214 1159 (BN 366194977 1538 (BN 360272850 1054 (BN 360026072 1536 (BL 354953926 3713) BE) (BL 361850334 282)) (BN 376023678 1665 (BN 371337570 1792 (BL 371015322 3968) BE) (BL 380213086 258))) (BN 392335521 1153 (BN 388634148 600 (BN 387267457 1031 (BL 385015074 1304) BE) (BL 390130107 128)) (BN 397671716 576 (BN 397176193 3906 (BL 393846568 1537) BE) (BL 399615552 262))))) (BN 450875403 1158 (BN 426168026 3388 (BN 413684993 3840 (BN 404250827 3328 (BN 403416202 1542 (BL 401991078 3331) BE) (BN 409687632 1152 (BL 404619568 1030) BE)) (BN 416009187 771 (BN 415474662 1540 (BL 413872099 3612) BE) (BL 417800402 828))) (BN 439647456 3456 (BN 429492771 260 (BN 428629839 641 (BL 426290526 1364) BE) (BL 434658928 263)) (BN 443801710 3590 (BN 441612169 640 (BL 441545896 384) BE) (BL 445763625 1280)))) (BN 484240952 1340 (BN 466888841 1346 (BN 462698411 896 (BN 458075504 1543 (BL 455086757 512) BE) (BL 466518474 385)) (BN 480549288 3610 (BN 478974600 516 (BL 473467952 3457) BE) (BL 482902118 1664))) (BN 504054633 3900 (BN 498461012 3591 (BN 492743135 3584 (BL 487670989 897) BE) (BL 498912040 3586)) (BN 561346902 1409 (BN 548191725 3588 (BL 526563631 3585) BE) (BL 574329232 1408)))))
def F11T8 : BTree NodeData := lf 0x10003f1 [0x102000b0005,0x401060107]
def F11M8 : BST := BN 387347492 2 (BN 361903404 132 (BN 302307551 28 (BN 296115579 898 (BL 289702668 900) BE) (BL 328082908 130)) (BN 376089170 24 (BN 368984740 26 (BL 367340209 128) BE) (BL 381358318 896))) (BN 436627177 4 (BN 423143593 259 (BN 420435888 0 (BL 413488036 257) BE) (BL 430840147 256)) (BN 494620467 388 (BL 460799971 386) (BL 500057272 384)))
def F11T9 : BTree NodeData := lf 0x1f0 [0x2000b0005,0x60007]
def F11M9 : BST := BN 298123084 60 (BN 280770973 66 (BN 272633666 42 (BL 263072773 12) BE) (BN 296161169 6 (BL 290426530 90) BE)) (BN 346415285 30 (BN 339310855 36 (BL 312352458 18) BE) (BL 388492724 0))
def F11L : Nat → Option (BTree NodeData) | 3 => some F11T3 | 4 => some F11T4 | 5 => some F11T5 | 6 => some F11T6 | 7 => some F11T7 | 8 => some F11T8 | 9 => some F11T9 | _ => none
def F11M : Nat → BST | 4 => F11M4 | 5 => F11M5 | 6 => F11M6 | 7 => F11M7 | 8 => F11M8 | 9 => F11M9 | _ => BE
def tF12 : Sig := 0xfe80fe8080008000#64
def F12P : List Row := mkRows [15,15,15,15,15,15,15,15,39,39,39,39,39,39,39,39,41,41,41,41,41,41,41,41,42,42,42,42,42,42,42,42,44,44,44,44,44,44,44,44]
def F12N : List Row := mkRows [7,11,13,14,35,37,38,40,7,11,13,14,35,37,38,40,7,11,13,14,35,37,38,40,7,11,13,14,35,37,38,40,7,11,13,14,35,37,38,40]
def F12R : List (Nat × Nat) := [(16777215,237149566775),(4278255615,392374737755),(1095216726015,469987323245),(1099511562495,612277063310),(1099511627520,1034834473200)]
def F12A : List (List Nat) := [[0,1,2,3,4,5],[0,1,2,5,4,3],[0,2,1,3,4,5],[0,2,1,5,4,3],[1,0,2,3,4,5],[1,0,2,5,4,3],[1,2,0,3,4,5],[1,2,0,5,4,3],[2,0,1,3,4,5],[2,0,1,5,4,3],[2,1,0,3,4,5],[2,1,0,5,4,3]]
def F12C : List CutSpec := [⟨0,32,6,7,0,[0,1,2,5,3,4],0xffffffff00000000#64⟩,⟨0,3,4,1,0,[0,1,3,4,2,5],0x8888888888888888#64⟩,⟨0,5,4,1,0,[0,3,1,4,2,5],0xa0a0a0a0a0a0a0a0#64⟩,⟨3,0,2,0,0,[0,1,2,3,4,5],0x1111111111111111#64⟩,⟨0,8,6,7,0,[0,1,2,3,4,5],0xff00ff00ff00ff00#64⟩,⟨0,4,5,6,0,[1,2,0,3,4,5],0xf0f0f0f0f0f0f0f0#64⟩,⟨0,33,2,0,0,[0,1,2,3,4,5],0xaaaaaaaa00000000#64⟩,⟨0,9,2,0,0,[0,1,2,3,4,5],0xaa00aa00aa00aa00#64⟩,⟨2,0,3,0,0,[0,1,2,3,4,5],0x3333333333333333#64⟩,⟨5,0,2,0,0,[0,1,2,3,4,5],0x505050505050505#64⟩,⟨1,8,2,0,0,[0,1,2,3,4,5],0x5500550055005500#64⟩,⟨0,1,5,6,0,[0,1,2,3,4,5],0xaaaaaaaaaaaaaaaa#64⟩,⟨0,2,5,6,0,[1,0,2,3,4,5],0xcccccccccccccccc#64⟩,⟨4,0,3,0,0,[0,1,2,3,4,5],0xf0f0f0f0f0f0f0f#64⟩,⟨0,36,2,0,0,[0,1,2,3,4,5],0xf0f0f0f000000000#64⟩,⟨6,1,1,0,0,[0,1,2,3,4,5],0x202020202020202#64⟩,⟨0,34,2,0,0,[0,1,2,3,4,5],0xcccccccc00000000#64⟩,⟨0,10,2,0,0,[0,1,2,3,4,5],0xcc00cc00cc00cc00#64⟩,⟨0,6,4,1,0,[3,0,1,4,2,5],0xc0c0c0c0c0c0c0c0#64⟩,⟨1,0,3,0,0,[0,1,2,3,4,5],0x5555555555555555#64⟩,⟨4,32,2,0,0,[0,1,2,3,4,5],0xf0f0f0f00000000#64⟩,⟨0,35,1,0,0,[0,1,2,3,4,5],0x8888888800000000#64⟩,⟨0,11,1,0,0,[0,1,2,3,4,5],0x8800880088008800#64⟩,⟨1,32,2,0,0,[0,1,2,3,4,5],0x5555555500000000#64⟩,⟨4,3,1,0,0,[0,1,2,3,4,5],0x808080808080808#64⟩,⟨6,0,2,0,0,[0,1,2,3,4,5],0x303030303030303#64⟩,⟨4,8,2,0,0,[0,1,2,3,4,5],0xf000f000f000f00#64⟩,⟨3,4,1,0,0,[0,1,2,3,4,5],0x1010101010101010#64⟩,⟨5,2,1,0,0,[0,1,2,3,4,5],0x404040404040404#64⟩,⟨3,32,1,0,0,[0,1,2,3,4,5],0x1111111100000000#64⟩,⟨2,1,1,0,0,[0,1,2,3,4,5],0x2222222222222222#64⟩,⟨2,32,2,0,0,[0,1,2,3,4,5],0x3333333300000000#64⟩,⟨0,37,1,0,0,[0,1,2,3,4,5],0xa0a0a0a000000000#64⟩,⟨5,32,1,0,0,[0,1,2,3,4,5],0x505050500000000#64⟩,⟨0,13,1,0,0,[0,1,2,3,4,5],0xa000a000a000a000#64⟩]
def F12T3 : BTree NodeData := nd (nd (lf2 0x9d44344010021c5 0x286 [0x1b01]) (nd (lf2 0x1c9434401003005 0x365 [0xc02]) (lf2 0xd95434401002045 0x287 [0x1403]))) (nd (nd (lf2 0x1d5434401002045 0x286 [0x4]) (lf2 0x10c410c01003245 0x176 [])) (nd (lf2 0x9cc410c01003245 0x264 []) (lf2 0x584611414302045 0x387 [0x4])))
def F12T4_0 := nd (nd (nd (nd (nd (lf 0x18c434401001b44 [0x20b05]) (lf 0xd944344010019c4 [0xb050b01])) (nd (lf 0x9d44344010015c4 [0xb01]) (lf 0x1d84344010013c4 [0x800070106,0x2]))) (nd (nd (lf 0x1c9434401001604 [0xc02]) (lf 0xd95434401001844 [0x40204030b01])) (nd (lf 0x1d5434401001444 [0x90c03]) (lf 0x1d9434401001244 [0x4])))) (nd (nd (nd (lf 0xd0c634401001a44 [0x305]) (lf 0xd0c634401001b44 [0x305])) (nd (lf 0x9d06344010012c4 [0x803]) (lf 0x9d06344010013c4 []))) (nd (nd (lf 0x10c410c01001e44 []) (lf 0x9cc410c01001744 [])) (nd (lf 0x5d8410c010013c4 []) (lf 0x990520c010018e4 [0x802]))))) (nd (nd (nd (nd (lf 0x150430c01001c64 [0x5]) (lf 0x9d0650c810010f4 [0x1])) (nd (lf 0x9c06510c10011e4 [0xd01]) (lf 0x9c86510c10011b4 [0xd01]))) (nd (nd (lf 0x9866014c1001944 [0x9000a]) (lf 0x9866014c10019c4 [0xb])) (nd (lf 0x9d66010d10011e4 []) (lf 0x9c86510d10011b4 [0xd01])))) (nd (nd (nd (lf 0x1c96414d1001434 [0xe0c0d0c0c,0xf]) (lf 0x1c94314d1001434 [0x105])) (nd (lf 0x1c943c421001604 [0xc0d0c0c]) (lf 0xdd543c421001444 [0x10]))) (nd (nd (lf 0x10e520c61001d14 []) (lf 0x192520c61001994 [0x120011040c,0x106])) (nd (lf 0x992520c61001894 []) (lf 0x992520c61001994 [])))))
def F12T4_1 := nd (nd (nd (nd (nd (lf 0x950430c61001c54 [0x50a0c]) (lf 0x9c04354a10015a4 [0xb01])) (nd (lf 0x9c66010e10013c4 [0xd01]) (lf 0x94e6010e1001964 []))) (nd (nd (lf 0x9c46050e1001244 [0x60d00090e13]) (lf 0x1c16494e1001464 [0x140c13])) (nd (lf 0x1c14394e1001464 [0x105]) (lf 0x90e6494e1001874 [0x301])))) (nd (nd (nd (lf 0x59654d003001864 []) (lf 0x946609043001844 [0x90014])) (nd (lf 0x5da541443001074 [0xe00040c02]) (lf 0x552611503001854 [0x9000a0701]))) (nd (nd (lf 0x1c5659503001454 [0x1503010004]) (lf 0x10e511003001c64 [0x110002])) (nd (lf 0x952631003001874 [0x101]) (lf 0x5da540c43001074 [0xe0c020004]))))) (nd (nd (nd (nd (lf 0x594431043001874 [0x100050004,0x90d]) (lf 0x952631043001874 [0xb])) (nd (lf 0x9466090430018c4 [0x2000a]) (lf 0x9066494430018d4 []))) (nd (nd (lf 0x1c56010c3001744 []) (lf 0x5866015030019c4 [0xe05])) (nd (lf 0x98e601503001964 []) (lf 0x989611503001994 [])))) (nd (nd (nd (lf 0x98a611503001994 [0xe05]) (lf 0x98e611503001954 [0x701])) (nd (lf 0x5526115030018d4 [0x605]) (lf 0x1c55014043015c4 [0x800070003,0x2]))) (nd (nd (lf 0xdd95014043011e4 []) (lf 0x9ca6194043011b4 [])) (nd (lf 0x584611414301844 [0x30d0014]) (lf 0xd86611414301844 [0x4])))))
def F12T4 : BTree NodeData := nd F12T4_0 F12T4_1
def F12M4 : BST := BN 169670808 256 (BN 123751707 896 (BL 58443454 768) (BL 151451924 128)) (BN 224706120 640 (BL 197250884 0) (BL 326851159 384))
def F12T5_0 := nd (nd (nd (nd (nd (lf 0x434401000fc3 [0x30500020301]) (lf 0x1434401000e43 [0x40303010402])) (nd (lf 0x634401000bc3 [0x800020003]) (nd (lf 0x36544010009c3 [0x70500030002,0x701]) (lf 0x410c01000fc3 [])))) (nd (nd (lf 0x2610c01000fc3 [0xc040c0008,0xd]) (lf 0x520c01000de3 [0x300020505,0x14])) (nd (lf 0x430c01000f63 [0x105020d]) (nd (lf 0x540c01000ce3 [0x20505000a]) (lf 0x540c01000de3 [0x20505]))))) (nd (nd (nd (lf 0x640c01000be3 [0x160106000d,0x17]) (lf 0x2640c01000ae3 [0x40305050402,0xa0008])) (nd (lf 0x2640c01000be3 [0x402]) (nd (lf 0x2600c81000b63 [0x4130018]) (lf 0x650c81000973 [0x104130014,0x9000e0403])))) (nd (nd (lf 0x2650c81000973 [0x904130018]) (lf 0x2600c81000be3 [0x1900140413])) (nd (lf 0x2640c81000af3 [0x1a0403000a,0x101]) (nd (lf 0x650c810009f3 [0x10505]) (lf 0x2650c810009f3 [0x905050403,0x413])))))) (nd (nd (nd (nd (lf 0x2658c81000973 [0x104130014,0x90403]) (lf 0x1431481000c73 [0x1404130301,0x904030402,0xe])) (nd (lf 0x26314810009f3 [0xe001b]) (nd (lf 0x5310c1000d73 [0x5050001]) (lf 0x6510c10009f3 [0x1605010006,0x17])))) (nd (nd (lf 0x26510c10009f3 [0x50501]) (lf 0x6050c1000a63 [0x4000a])) (nd (lf 0x6250c1000a33 [0xa0602]) (nd (lf 0x6550c1000873 [0xe02020009]) (lf 0x26014c1000d63 [0xa00090018]))))) (nd (nd (nd (lf 0x26214c1000973 [0xe04020015]) (lf 0x16414c1000c73 [0x90301000a])) (nd (lf 0x26414c1000c73 [0xa00090018,0x1]) (nd (lf 0x26014c1000de3 [0x2000b]) (lf 0x26214c10009f3 [0x1b001c000e])))) (nd (nd (lf 0x14314c1000c73 [0x402000a000b,0x406001b0009]) (lf 0x34314c1000c73 [0x105])) (nd (lf 0x34314c1000d73 [0x105]) (nd (lf 0x26414c10008f3 [0x1000a0402,0x18]) (lf 0x26414c10009f3 [0x18]))))))
def F12T5_1 := nd (nd (nd (nd (nd (lf 0x26010d1000be3 [0x5010004]) (lf 0x5310d1000d73 [0x50500010004])) (nd (lf 0x6510d10009f3 [0x6000d000c,0x800070501]) (nd (lf 0x26510d10009f3 [0x50501]) (lf 0x6050d1000a63 [0x40613])))) (nd (nd (lf 0x6250d1000a33 [0x1d]) (lf 0x6550d1000873 [0x20300010004])) (nd (lf 0x16414d1000c73 [0x40303010004]) (nd (lf 0x26414d1000c73 [0x403040d0008,0x1]) (lf 0x14314d1000c73 [0x105]))))) (nd (nd (nd (lf 0x34314d1000c73 [0x105]) (lf 0x34314d1000d73 [0x105])) (nd (lf 0x26414d10008f3 [0x403040d0008,0x5]) (nd (lf 0x26414d10009f3 [0x1e]) (lf 0x43c421000fc3 [0x3050301])))) (nd (nd (lf 0x143c421000e43 [0x40d03010403]) (lf 0x2520c61000d93 [0x300120002,0x505])) (nd (lf 0x430c61000f53 [0x1050010]) (nd (lf 0x2540c61000cd3 [0x205050013,0x1f0012]) (lf 0x2540c61000dd3 [0x505])))))) (nd (nd (nd (nd (lf 0x640c61000bd3 [0x110106000c,0x12]) (lf 0x2640c61000ad3 [0x4020413])) (nd (lf 0x2640c61000bd3 []) (nd (lf 0x1650c61000dd3 [0x8000d0505]) (lf 0x4354a1000db3 [0x301020c])))) (nd (nd (lf 0x4394a1000db3 [0x301000d]) (lf 0x26010e1000be3 [0x501])) (nd (lf 0x25310e1000d73 [0x505040c0001]) (nd (lf 0x16510e10009f3 [0x501000d0010]) (lf 0x36510e10009f3 [0xb00110501]))))) (nd (nd (nd (lf 0x6050e1000a63 [0x10100140613]) (lf 0x6150e1000a53 [0x1a06030004])) (nd (lf 0x6250e1000a33 [0xa0602]) (nd (lf 0x36550e1000873 [0x1010010]) (lf 0x16494e1000c73 [0x3010010])))) (nd (nd (lf 0x26494e1000c73 [0x10413000b]) (nd (lf 0x26494e1000d73 [0x10000b040d,0x1]) (lf 0x14394e1000c73 [0x105]))) (nd (lf 0x34394e1000c73 [0x105]) (nd (lf 0x34394e1000d73 [0x105]) (lf 0x26494e10008f3 [0x50413000b]))))))
def F12T5_2 := nd (nd (nd (nd (nd (lf 0x26494e10009f3 [0x301]) (lf 0x2511003000d63 [0xa05010004])) (nd (lf 0x2541003000e63 [0x101000a0004]) (nd (lf 0x2609003000a63 [0x10100030002,0x605]) (lf 0x254d003000e63 [0x40304020018,0x50001])))) (nd (nd (lf 0x165d003000b63 [0x300020018,0x5]) (lf 0x1651043000873 [0xe0004])) (nd (lf 0x1651043000973 [0x5010402001c]) (nd (lf 0x2651043000973 [0x4020501000a]) (lf 0x2609043000a63 [0x10100020014]))))) (nd (nd (nd (lf 0x2519043000c53 [0x20009]) (lf 0x2601443000b63 [0xa00040018])) (nd (lf 0x1541443000c73 [0x4020301000a]) (nd (lf 0x2541443000c73 [0xa04020018]) (lf 0x2641443000a73 [0x180402000a,0x1])))) (nd (nd (lf 0x2629443000973 [0x104020015]) (lf 0x1549443000c73 [0xa03010004,0x506])) (nd (lf 0x2549443000c73 [0xa00080004]) (nd (lf 0x2601503000b63 [0x18000a0004]) (lf 0x2611503000b53 [0x4000a0018])))))) (nd (nd (nd (nd (lf 0x1541503000c73 [0x101]) (lf 0x2641503000a73 [0x60500080018,0x101])) (nd (lf 0x1659503000c73 [0x101]) (nd (lf 0x3549503000c73 [0x101]) (lf 0x2511003000de3 [0x405010002])))) (nd (nd (lf 0x431003000e63 [0x402050101,0x306000a030d,0xc]) (lf 0x2631003000f63 [0xc04010205])) (nd (lf 0x431003000e73 [0x14000c0101]) (nd (lf 0x2631003000b73 [0x4010205]) (lf 0x2609003000ae3 [0x300020605,0x14]))))) (nd (nd (nd (lf 0x165d003000be3 [0xc0605]) (lf 0x2540c43000c73 [0x1a04020004,0x18000a])) (nd (lf 0x431043000e73 [0x500010004]) (nd (lf 0x2631043000b73 [0x40102050004,0x402]) (lf 0x16510430009f3 [0x50106050402])))) (nd (nd (lf 0x26510430009f3 [0x50100140605,0xd]) (nd (lf 0x2609043000ae3 [0x6050002000a]) (lf 0x2519043000cd3 [0x2001a]))) (nd (lf 0x16590430008f3 [0x402001c]) (nd (lf 0x2601443000be3 [0x1400020605]) (lf 0x26294430009f3 [0x1c06050402]))))))
def F12T5_3 := nd (nd (nd (nd (nd (lf 0x439443000d73 [0x900020301,0x110205]) (lf 0x26494430009f3 [0x90020])) (nd (lf 0x16010c3000f63 [0x140405]) (nd (lf 0x26010c3000f63 [0x405]) (lf 0x25410c3000e73 [0x500140101])))) (nd (nd (lf 0x2601503000de3 [0x605]) (lf 0x26015030009f3 [0x6050014])) (nd (lf 0x1611503000dd3 [0x6050013]) (nd (lf 0x26115030009d3 [0x9000a0605,0x701]) (lf 0x2611503000dd3 [0xd0605]))))) (nd (nd (nd (lf 0x26115030009f3 [0x6050009]) (lf 0x2631503000973 [0x100210016])) (nd (lf 0x2631503000d73 [0x301]) (nd (lf 0x2601503000be3 [0x605]) (lf 0x2611503000bd3 [0x605])))) (nd (nd (lf 0x1541503000cf3 [0x101]) (lf 0x26195030008f3 [0x605001a0004])) (nd (lf 0x2639503000c73 [0x60502030202]) (nd (lf 0x2409503000cf3 [0x101]) (lf 0x2419503000cf3 [0x101])))))) (nd (nd (nd (nd (lf 0x26195030009f3 [0x1800170009]) (lf 0x2439503000c73 [0x101])) (nd (lf 0x3549503000cf3 [0x101]) (nd (lf 0x1649423000c73 [0x40200140301,0x403]) (lf 0x2629463000973 [0xe04020015])))) (nd (nd (lf 0x2439533000c73 [0x101]) (lf 0x1501404300de3 [0x700030002,0x8])) (nd (lf 0x1611404300bd3 [0x6010002]) (nd (lf 0x2611404300bd3 [0x6050601]) (lf 0x2631404300b73 [0x70605]))))) (nd (nd (nd (lf 0x615404300bd3 [0x601000c]) (lf 0x3615404300bd3 [0x6050601])) (nd (lf 0x26094043009f3 [0x6010006000d,0x80007]) (nd (lf 0x26194043009f3 [0x500060601,0x120011]) (lf 0x3509404300de3 [0xb00180601])))) (nd (nd (lf 0x263d404300b73 [0x180605]) (nd (lf 0x611414300c63 [0xa0004]) (lf 0x1611414300c63 [0x40313]))) (nd (lf 0x2611414300c63 [0xa03060004]) (nd (lf 0x3611414300c63 [0x140313]) (lf 0x2611414300873 [0xe04010004]))))))
def F12T5 : BTree NodeData := nd (nd F12T5_0 F12T5_1) (nd F12T5_2 F12T5_3)
def F12M5 : BST := BN 227112438 3584 (BN 186735340 1409 (BN 156517812 7424 (BN 136602470 7040 (BN 114382937 128 (BN 110977520 7552 (BL 102134744 129) BE) (BN 135230826 1793 (BL 125443904 1792) BE)) (BN 154666786 5504 (BN 153385796 6016 (BL 139441836 8064) BE) (BL 156382745 4096))) (BN 174151610 5506 (BN 171442576 2312 (BN 166672218 261 (BL 159033352 7554) BE) (BN 173335846 4736 (BL 172048533 6912) BE)) (BN 186149248 4994 (BN 183522852 3072 (BL 177771844 2432) BE) (BL 186439407 1152)))) (BN 208500202 2048 (BN 203474579 384 (BN 191009341 7168 (BN 188971900 5120 (BL 188101369 896) BE) (BN 200013584 2308 (BL 191010563 3332) BE)) (BN 206447838 6144 (BN 205260806 640 (BL 204109956 2688) BE) (BL 206590498 5888))) (BN 218067288 6272 (BN 214720256 4992 (BN 211718916 7042 (BL 210475754 6784) BE) (BL 214911752 2944)) (BN 224551376 4993 (BN 222599255 3712 (BL 219553801 0) BE) (BL 225867520 3840))))) (BN 271564830 4352 (BN 244103082 5248 (BN 239669634 3457 (BN 234249708 6400 (BN 229838514 3456 (BL 228937697 2560) BE) (BN 238207225 6656 (BL 235137048 7936) BE)) (BN 242567400 2176 (BN 241653564 3968 (BL 240102403 6273) BE) (BL 243040101 1024))) (BN 253816718 2304 (BN 247976305 1408 (BN 245982129 5637 (BL 244452947 1920) BE) (BN 253701445 768 (BL 253326459 259) BE)) (BN 265659170 7688 (BN 262756740 6916 (BL 256675333 7808) BE) (BL 268790458 2816)))) (BN 311014787 7680 (BN 293146105 5763 (BN 282932767 1280 (BN 282045537 3328 (BL 274583495 4224) BE) (BN 292557975 5762 (BL 287368765 5376) BE)) (BN 305619618 4480 (BN 300991844 257 (BL 298456987 6528) BE) (BL 310758923 512))) (BN 335593177 5760 (BN 327805068 1 (BN 323092751 1410 (BL 320028451 4608) BE) (BL 332022251 1536)) (BN 394561580 5761 (BN 391618104 256 (BL 363515485 258) BE) (BL 415297599 5632)))))
def F12T6_0 := nd (nd (nd (nd (nd (lf 0x44010007c2 [0x30500020003,0x301]) (lf 0xc010007e2 [0x301050002,0x17000a])) (nd (lf 0xc81000772 [0x30202000a,0x1a0101]) (lf 0xc810007f2 [0x3000a0202,0x1a00130105,0x101]))) (nd (nd (lf 0x8c81000772 [0x30202000a,0x101001a0105]) (lf 0x14810005f2 [0x30100020003,0x13000e0305,0x10005])) (nd (lf 0x10c10007f2 [0x10501010002]) (lf 0x50c1000672 [0x20601010202,0xa])))) (nd (nd (nd (lf 0x14c1000572 [0x301000a0002,0x1800010203]) (lf 0x14c10005f2 [0xa01050002,0x1703010203,0x1])) (nd (lf 0x10d10007f2 [0x1050101000c,0xd]) (lf 0x50d1000672 [0x20d01010203]))) (nd (nd (lf 0x14d1000572 [0x301000d0003,0x1001e]) (lf 0x14d10005f2 [0x301000d0003,0x10008])) (nd (lf 0xc4210007c2 [0x305000d0003,0x301]) (nd (lf 0xc610007d2 [0x10500020013,0x12]) (lf 0x54a10005b2 [0x30500060002,0x301])))))) (nd (nd (nd (nd (lf 0x94a10005b2 [0x30500130002,0x301]) (lf 0x10e10007f2 [0x1050101000d,0xc])) (nd (lf 0x50e1000672 [0x21301010202]) (lf 0x94e1000572 [0x30100020013,0x10010]))) (nd (nd (lf 0x94e10005f2 [0x30100020013,0x1000b]) (lf 0x1003000662 [0x1000a0004,0x20005])) (nd (lf 0x1003000762 [0xa00040101,0x500030002]) (lf 0x1003000672 [0x300020014,0x1])))) (nd (nd (nd (lf 0x1003000772 [0x300020014,0x101]) (lf 0x9003000672 [0x301010002,0x50205])) (nd (lf 0xd003000762 [0x301010002]) (lf 0x1043000672 [0xa001a0004]))) (nd (nd (lf 0x1043000772 [0x20101001c]) (lf 0x9043000672 [0x1a01010004,0xa])) (nd (lf 0x1443000772 [0x2000a0018,0x101]) (nd (lf 0x9443000572 [0x301001a0002,0x2000010203]) (lf 0x9443000772 [0xa0004001e,0x1a00020203]))))))
def F12T6_1 := nd (nd (nd (nd (nd (lf 0x1503000772 [0x101000a0004,0x30002]) (lf 0x5503000672 [0x20200040101,0xa02050203,0x5])) (nd (lf 0x9503000672 [0x20500080004,0x1010202000a,0x203]) (lf 0x9503000772 [0x1010022001e,0x205]))) (nd (nd (lf 0x10030007e2 [0x201010205,0x3000a0004]) (lf 0x10030007f2 [0xc01010205])) (nd (lf 0x90030006f2 [0x300020205,0x101]) (lf 0xd0030007e2 [0x301010002,0x205])))) (nd (nd (nd (lf 0xc43000772 [0x2001e001c,0x1010201]) (lf 0x10430007f2 [0x20500020004,0x101])) (nd (lf 0x90430006f2 [0x20205001c,0x101]) (lf 0x14430007f2 [0x1400020017]))) (nd (nd (lf 0x94430005f2 [0x1a02050002,0x102030301]) (lf 0x94430007f2 [0x800040002,0x205])) (nd (lf 0x10c3000772 [0xc00050101,0xa010d0004,0x106]) (nd (lf 0x15030005f2 [0xd01010205,0xa00040006]) (lf 0x15030007f2 [0x300020205,0x10008])))))) (nd (nd (nd (nd (lf 0x55030006f2 [0x20500230017,0x20c]) (lf 0x95030004f2 [0x2302050017])) (nd (lf 0x95030006f2 [0x20500230017,0x101]) (lf 0x95030005f2 [0x20202050101,0x22001e0203]))) (nd (nd (lf 0x95030007f2 [0xc01010205]) (lf 0x9023000672 [0x302050002,0x101])) (nd (lf 0x9423000572 [0x30100030002,0x10100050018]) (nd (lf 0x9063000672 [0x10102050002,0xa001a]) (lf 0x9463000572 [0x301001d0002,0x203001a0005,0x1]))))) (nd (nd (nd (lf 0x95330004f2 [0x302050002]) (lf 0x95330005f2 [0x302050002,0x101])) (nd (lf 0x14043007f2 [0xc02050201]) (lf 0x54043007f2 [0xc02050201]))) (nd (nd (lf 0x94043005f2 [0x402050201,0x6000a000d]) (lf 0x94043007f2 [0xc02050201])) (nd (lf 0xd4043007f2 [0x205000c0201]) (nd (lf 0x1414300462 []) (lf 0x1414300472 [0x1001c]))))))
def F12T6 : BTree NodeData := nd F12T6_0 F12T6_1
def F12M6 : BST := BN 279174235 6400 (BN 221808560 2304 (BN 197589445 6912 (BN 170153353 13056 (BN 145083537 12288 (BN 118580694 11520 (BN 107519727 15616 (BN 104541062 32001 (BL 100105064 15617) BE) (BL 116789255 32000)) (BN 133201146 11521 (BL 131363342 6528) (BL 134188943 7040))) (BN 163376957 7424 (BN 150848166 6530 (BL 147870415 1920) (BL 153673767 7042)) (BN 169078536 30725 (BL 164642538 14341) (BL 169777800 10496)))) (BN 184623419 9348 (BN 179916183 31106 (BN 173640169 14850 (BN 173163879 7425 (BL 171442576 14722) BE) (BL 179466625 30853)) (BN 182768732 29697 (BL 182741784 15234) (BL 184227228 28932))) (BN 191828398 6016 (BN 185216297 4352 (BL 185164718 14080) (BL 188736153 11909)) (BN 192175371 10368 (BL 192038260 15361) (BL 194113714 10244))))) (BN 208734166 10245 (BN 206535070 5504 (BN 204288257 11650 (BN 200013584 14720 (BN 198322260 8448 (BL 198061463 9600) BE) (BL 201444899 6272)) (BN 205694138 9856 (BL 205120889 3078) (BL 205880897 30336))) (BN 207884540 260 (BN 206871921 10112 (BL 206726566 3456) (BL 207706156 5376)) (BN 208330425 29184 (BL 207892583 9601) (BL 208487191 31104)))) (BN 214461534 12802 (BN 211374417 14592 (BN 210792300 4608 (BN 209556887 31750 (BL 209360671 31616) BE) (BL 211312792 15232)) (BN 213292395 518 (BL 212690591 4096) (BL 213557785 898))) (BN 219191791 31617 (BN 216975684 13568 (BL 216366190 5505) (BL 218060494 5250)) (BN 220552789 14473 (BL 219624560 6913) (BL 221181773 15872)))))) (BN 255502395 29952 (BN 231916361 6149 (BN 227524524 15104 (BN 223605449 2432 (BN 222986861 1922 (BN 222705141 29186 (BL 222129439 6148) BE) (BL 223574186 10624)) (BN 223960348 32640 (BL 223771562 1026) (BL 224750588 13957))) (BN 229752038 0 (BN 228998340 256 (BL 227700118 13442) (BL 229606319 1410)) (BN 230451301 32256 (BL 229822317 3721) (BL 230685527 2816)))) (BN 244523551 768 (BN 238697358 10114 (BN 235347413 30976 (BN 234614598 28416 (BL 232887895 13961) BE) (BL 238309687 512)) (BN 242009504 9858 (BL 239835747 9218) (BL 244325311 9984))) (BN 253693050 386 (BN 250310839 11648 (BL 249105275 5122) (BL 251296779 14339)) (BN 254294784 31236 (BL 254105652 29440) (BL 254785402 32512))))) (BN 264958024 5894 (BN 261750908 10249 (BN 258144950 12544 (BN 257292010 11394 (BN 256746905 30464 (BL 255732777 30723) BE) (BL 257720848 3840)) (BN 259580367 896 (BL 258730782 13828) (BL 261334597 12162))) (BN 263800573 8960 (BN 262341193 8192 (BL 262126919 12800) (BL 262439111 15489)) (BN 264469380 14977 (BL 264054930 128) (BL 264578276 30592)))) (BN 273077134 1536 (BN 269818816 32642 (BN 266931634 7298 (BL 265725879 5248) (BL 266990376 12032)) (BN 273025490 13318 (BL 271210191 28928) (BL 273070101 4864))) (BN 275365503 13440 (BN 273738319 12673 (BL 273592145 14210) (BL 275308515 10248)) (BN 277461488 11270 (BL 277085657 1152) (BL 277513132 30208))))))) (BN 316191292 11268 (BN 298064095 16128 (BN 289096423 11008 (BN 284310703 16256 (BN 281755391 772 (BN 281141876 14848 (BN 280088341 14208 (BL 279990810 31874) BE) (BL 281521655 28288)) (BN 282533056 4609 (BL 281906643 5888) (BL 282853005 30848))) (BN 287924615 29568 (BN 286456724 2562 (BL 284426808 30082) (BL 287289003 11904)) (BN 288654693 5632 (BL 288091550 3328) (BL 288794567 7936)))) (BN 294964293 29314 (BN 291512214 12801 (BN 290528295 8322 (BN 289527382 1280 (BL 289100373 14469) BE) (BL 290819259 14464)) (BN 293707246 2176 (BL 292742576 3200) (BL 293862107 776))) (BN 296728252 384 (BN 295439172 11010 (BL 295255257 3712) (BL 295552423 29315)) (BN 297729201 10754 (BL 297178574 32384) (BL 297819576 8964))))) (BN 306925918 7808 (BN 303077793 10756 (BN 298962164 14337 (BN 298532207 7174 (BN 298369901 3717 (BL 298143244 1664) BE) (BL 298796910 9472)) (BN 301010806 31488 (BL 300327212 11392) (BL 303056762 1408))) (BN 306119226 2560 (BN 303398162 30721 (BL 303276033 1028) (BL 303733261 9728)) (BN 306800374 8576 (BL 306573527 8449) (BL 306801193 13184)))) (BN 311045695 14976 (BN 309926292 8968 (BN 308746359 11136 (BN 308561818 31872 (BL 307089104 4868) BE) (BL 308984433 3072)) (BN 310589786 29696 (BL 309966836 7296) (BL 310790710 5760))) (BN 313420431 31744 (BN 311755294 13316 (BL 311654776 8064) (BL 312997816 30080)) (BN 315025784 15360 (BL 314325810 3968) (BL 316103117 1024)))))) (BN 343053792 10241 (BN 333563497 8320 (BN 327564394 7552 (BN 319444863 258 (BN 319195820 4872 (BN 318928017 5762 (BL 316440817 8832) BE) (BL 319241370 3969)) (BN 323680076 15488 (BL 322648834 7553) (BL 325775388 4097))) (BN 329730007 29824 (BN 328116074 13696 (BL 327740025 29056) (BL 329340903 28544)) (BN 331308274 1792 (BL 330767950 12416) (BL 332167302 9216)))) (BN 337999495 29312 (BN 335203948 31360 (BN 334979284 12672 (BN 334428569 28672 (BL 334411197 16258) BE) (BL 335145397 6146)) (BN 337669665 28546 (BL 337651023 1794) (BL 337990501 13312))) (BN 340659125 6656 (BN 339928609 5898 (BL 338807702 8704) (BL 340037478 31361)) (BN 342067158 2688 (BL 341436830 5120) (BL 342426499 11264))))) (BN 369011268 10881 (BN 359180148 10880 (BN 355713030 9988 (BN 350509502 6784 (BN 347983317 6662 (BL 344975428 7168) BE) (BL 351374612 31232)) (BN 357513244 8066 (BL 355810610 13824) (BL 358879229 4481))) (BN 365921803 30722 (BN 362662718 2310 (BL 361656714 28930) (BL 364575270 4224)) (BN 367819746 9992 (BL 366235987 6145) (BL 368836304 12160)))) (BN 396967898 29313 (BN 393129226 7428 (BN 390060756 10752 (BL 384754894 14336) (BL 392449926 9344)) (BN 394066058 13952 (BL 394024422 30720) (BL 396885924 16000))) (BN 406224657 28800 (BN 401427404 9860 (BL 399461227 10240) (BL 405235942 7432)) (BN 424080815 2048 (BL 420120194 4480) (BL 427476952 6144)))))))
def F12T7 : BTree NodeData := nd (nd (nd (lf 0x10003f1 [0x10101050002,0x500030013,0x1]) (lf 0x110003f1 [0x105000d0003,0x100050101])) (nd (lf 0x210003f1 [0x10500020013,0x100050101]) (lf 0x3000371 [0x301010002,0x10005]))) (nd (nd (lf 0x30003f1 [0x300020005,0x10101]) (lf 0x23000371 [0x300020005,0x101])) (nd (lf 0x330003f1 [0x300050002,0x10101]) (nd (lf 0x43003f1 [0xc00010005,0x6000d]) (lf 0x14300271 [0x1]))))
def F12M7 : BST := BN 301207735 2304 (BN 250827711 512 (BN 215266229 4100 (BN 202242476 3717 (BN 187023052 1536 (BN 171134199 7681 (BN 170360730 8068 (BL 156513747 7680) BE) (BL 186290237 6400)) (BN 191828398 7808 (BN 191459050 5632 (BL 190726235 1280) BE) (BL 192455554 3716))) (BN 207892583 4480 (BN 203162326 514 (BN 203127606 2944 (BL 202268330 4358) BE) (BL 207598324 4610)) (BN 208520497 2560 (BN 208325352 6401 (BL 207942062 8072) BE) (BL 210379783 3721)))) (BN 235039507 3074 (BN 223574186 1920 (BN 218452830 0 (BN 217594880 1281 (BL 217162111 6528) BE) (BL 219386319 256)) (BN 234857485 2310 (BN 229886681 4101 (BL 228770920 3720) BE) (BL 234873394 6016))) (BN 243068058 5893 (BN 242393842 7938 (BN 241961268 3713 (BL 241109652 6656) BE) (BL 242806444 15872)) (BN 244203187 3584 (BL 244100433 3968) (BL 246829840 1666))))) (BN 282786850 4865 (BN 265786037 16256 (BN 257343693 8064 (BN 252740781 7816 (BN 252337586 2693 (BL 251205365 5897) BE) (BL 255263709 4608)) (BN 262166724 7048 (BN 260992087 15746 (BL 260474893 2697) BE) (BL 264039989 2952))) (BN 273602148 7812 (BN 268618580 4352 (BN 267628662 7170 (BL 266105805 16264) BE) (BL 273403908 16260)) (BN 277238915 4362 (BN 274961329 4354 (BL 274921326 15744) BE) (BL 280213006 513)))) (BN 294140578 640 (BN 289482534 4609 (BN 285429044 7936 (BN 285293623 3078 (BL 284901356 2948) BE) (BL 287360699 5504)) (BN 292056378 3201 (BN 291903025 3456 (BL 289865042 1664) BE) (BL 293023336 4356))) (BN 299491502 6912 (BN 297061220 1924 (BN 295274319 1537 (BL 294919339 5120) BE) (BL 298967020 2562)) (BN 300376632 128 (BL 299973024 2566) (BL 301119521 1928)))))) (BN 330767950 5376 (BN 316440817 2176 (BN 307942162 896 (BN 304965369 3972 (BN 304543847 5633 (BN 303927500 1797 (BL 303202233 3712) BE) (BL 304812630 16000)) (BN 307550484 2306 (BN 306801193 4224 (BL 305130052 4360) BE) (BL 307628809 6914))) (BN 312064807 1801 (BN 309828070 2314 (BN 308761030 1792 (BL 308360428 6020) BE) (BL 311237191 384)) (BN 313197028 4736 (BN 312845333 1024 (BL 312418729 6024) BE) (BL 316146558 3842)))) (BN 325612491 2308 (BN 317895957 7554 (BN 317231365 3976 (BN 317211690 4992 (BL 316898337 1794) BE) (BL 317882778 7174)) (BN 320876815 2432 (BN 320582556 6786 (BL 320014304 7040) BE) (BL 321334335 4738))) (BN 328282187 4098 (BN 327371062 3072 (BN 326119205 1030 (BL 325710345 6272) BE) (BL 327739065 7044)) (BN 330179372 7552 (BL 330146343 1408) (BL 330455944 642))))) (BN 359814072 5762 (BN 342994810 7297 (BN 335203948 3329 (BN 332562179 6662 (BN 331797638 2049 (BL 331556175 6658) BE) (BL 333725282 2817)) (BN 340037478 3328 (BN 339210294 7424 (BL 337719207 2312) BE) (BL 341067166 6145))) (BN 348479822 768 (BN 344473476 1152 (BN 343784143 4864 (BL 343646292 769) BE) (BL 348220141 3200)) (BN 354624773 6144 (BN 352915820 5248 (BL 350188775 2048) BE) (BL 355378074 16130)))) (BN 386266016 7684 (BN 374319401 5890 (BN 364206307 4097 (BN 363811943 3840 (BL 359960217 7168) BE) (BL 368247941 6784)) (BN 382542649 2054 (BN 381686865 2816 (BL 378755399 2690) BE) (BL 386122863 7296))) (BN 398413276 16128 (BN 391038814 2688 (BN 386978647 6150 (BL 386602816 5888) BE) (BL 398372732 7688)) (BN 402849274 5760 (BL 398488230 1025) (BL 420613742 4096))))))
def F12T8 : BTree NodeData := lf 0x1f0 [0x10005]
def F12M8 : BST := BN 239931588 129 (BN 208350103 137 (BN 190969122 262 (BN 185592344 132 (BN 181156346 772 (BL 180128270 648) BE) (BL 190943268 773)) (BN 199080575 777 (BN 197221289 512 (BL 194653999 896) BE) (BL 200212796 133))) (BN 223740299 2 (BN 221494617 389 (BN 217471712 776 (BL 209774283 388) BE) (BL 221907710 136)) (BN 235235909 641 (BN 230662060 769 (BL 227243154 1920) BE) (BL 235479581 640)))) (BN 281724128 260 (BN 265771167 649 (BN 257469385 392 (BN 257319372 256 (BL 248645601 644) BE) (BL 263662121 258)) (BN 278054582 645 (BN 273994415 6 (BL 265939707 266) BE) (BL 281580975 385))) (BN 294860357 384 (BN 291903025 768 (BN 288673816 518 (BL 287667812 514) BE) (BL 293830844 264)) (BN 302808164 393 (BL 296339023 128) (BL 316071854 0))))
def F12L : Nat → Option (BTree NodeData) | 3 => some F12T3 | 4 => some F12T4 | 5 => some F12T5 | 6 => some F12T6 | 7 => some F12T7 | 8 => some F12T8 | _ => none
def F12M : Nat → BST | 4 => F12M4 | 5 => F12M5 | 6 => F12M6 | 7 => F12M7 | 8 => F12M8 | _ => BE
def tF13 : Sig := 0xfffcffc0ffc0c000#64
def F13P : List Row := mkRows [14,14,14,14,14,14,14,14,22,22,22,22,22,22,22,22,24,24,24,24,24,24,24,24,38,38,38,38,38,38,38,38,40,40,40,40,40,40,40,40,50,50,50,50,50,50,50,50,52,52,52,52,52,52,52,52]
def F13N : List Row := mkRows [6,10,12,18,20,34,36,48,6,10,12,18,20,34,36,48,6,10,12,18,20,34,36,48,6,10,12,18,20,34,36,48,6,10,12,18,20,34,36,48,6,10,12,18,20,34,36,48,6,10,12,18,20,34,36,48]
def F13R : List (Nat × Nat) := [(280379743338495,12150888406395691),(71776123339472895,24019198012642645),(1095233372415,1695472800892422),(72056494543077120,42951977622608024),(72057594021150720,63297651233317088)]
def F13A : List (List Nat) := [[0,1,2,3,4,5],[0,1,2,3,5,4],[0,2,1,3,4,5],[0,2,1,3,5,4]]
def F13C : List CutSpec := [⟨4,16,2,0,0,[0,1,2,3,4,5],0xf0f00000f0f0000#64⟩,⟨0,8,3,0,0,[0,1,2,3,4,5],0xff00ff00ff00ff00#64⟩,⟨0,2,7,2,0,[0,1,2,3,4,5],0xcccccccccccccccc#64⟩,⟨8,0,7,5,0,[0,1,2,3,4,5],0xff00ff00ff00ff#64⟩,⟨6,0,2,0,0,[0,1,2,3,4,5],0x303030303030303#64⟩,⟨2,32,2,0,0,[0,1,2,3,4,5],0x3333333300000000#64⟩,⟨22,0,1,0,0,[0,1,2,3,4,5],0x30300000303#64⟩,⟨0,4,7,2,0,[0,2,1,3,4,5],0xf0f0f0f0f0f0f0f0#64⟩,⟨16,0,5,6,0,[0,1,2,3,4,5],0xffff0000ffff#64⟩,⟨32,0,5,6,0,[0,1,2,3,5,4],0xffffffff#64⟩,⟨4,0,5,4,0,[0,2,1,3,4,5],0xf0f0f0f0f0f0f0f#64⟩,⟨0,16,5,3,0,[0,1,2,3,4,5],0xffff0000ffff0000#64⟩,⟨16,8,2,0,0,[0,1,2,3,4,5],0xff000000ff00#64⟩,⟨0,48,2,0,0,[0,1,2,3,4,5],0xffff000000000000#64⟩,⟨32,2,4,1,0,[0,1,3,4,5,2],0xcccccccc#64⟩,⟨16,2,4,1,0,[0,1,3,4,2,5],0xcccc0000cccc#64⟩,⟨18,4,1,0,0,[0,1,2,3,4,5],0x303000003030#64⟩,⟨2,8,1,0,0,[0,1,2,3,4,5],0x3300330033003300#64⟩,⟨32,16,2,0,0,[0,1,2,3,4,5],0xffff0000#64⟩,⟨0,10,2,0,0,[0,1,2,3,4,5],0xcc00cc00cc00cc00#64⟩,⟨18,0,1,0,0,[0,1,2,3,4,5],0x333300003333#64⟩,⟨2,4,4,1,0,[0,1,2,3,4,5],0x3030303030303030#64⟩,⟨16,34,1,0,0,[0,1,2,3,4,5],0xcccc00000000#64⟩,⟨0,32,5,3,0,[0,1,2,3,5,4],0xffffffff00000000#64⟩,⟨4,2,4,1,0,[0,1,2,3,4,5],0xc0c0c0c0c0c0c0c#64⟩,⟨16,4,4,1,0,[0,3,1,4,2,5],0xf0f00000f0f0#64⟩,⟨32,8,2,0,0,[0,1,2,3,4,5],0xff00ff00#64⟩,⟨32,4,4,1,0,[0,3,1,4,5,2],0xf0f0f0f0#64⟩,⟨2,0,5,4,0,[0,1,2,3,4,5],0x3333333333333333#64⟩,⟨0,12,2,0,0,[0,1,2,3,4,5],0xf000f000f000f000#64⟩,⟨8,16,4,1,0,[0,3,4,1,2,5],0xff000000ff0000#64⟩,⟨4,8,1,0,0,[0,1,2,3,4,5],0xf000f000f000f00#64⟩,⟨8,32,4,1,0,[0,3,4,1,5,2],0xff00ff00000000#64⟩,⟨16,32,2,0,0,[0,1,2,3,4,5],0xffff00000000#64⟩,⟨8,2,4,1,0,[0,1,3,2,4,5],0xcc00cc00cc00cc#64⟩,⟨8,4,4,1,0,[0,3,1,2,4,5],0xf000f000f000f0#64⟩,⟨0,36,2,0,0,[0,1,2,3,4,5],0xf0f0f0f000000000#64⟩,⟨34,4,1,0,0,[0,1,2,3,4,5],0x30303030#64⟩,⟨4,48,1,0,0,[0,1,2,3,4,5],0xf0f000000000000#64⟩,⟨6,8,1,0,0,[0,1,2,3,4,5],0x300030003000300#64⟩,⟨36,2,1,0,0,[0,1,2,3,4,5],0xc0c0c0c#64⟩,⟨2,16,2,0,0,[0,1,2,3,4,5],0x3333000033330000#64⟩,⟨2,48,1,0,0,[0,1,2,3,4,5],0x3333000000000000#64⟩,⟨34,0,1,0,0,[0,1,2,3,4,5],0x33333333#64⟩,⟨4,32,2,0,0,[0,1,2,3,4,5],0xf0f0f0f00000000#64⟩,⟨32,20,1,0,0,[0,1,2,3,4,5],0xf0f00000#64⟩,⟨16,12,1,0,0,[0,1,2,3,4,5],0xf0000000f000#64⟩,⟨32,12,1,0,0,[0,1,2,3,4,5],0xf000f000#64⟩,⟨0,18,2,0,0,[0,1,2,3,4,5],0xcccc0000cccc0000#64⟩,⟨4,18,1,0,0,[0,1,2,3,4,5],0xc0c00000c0c0000#64⟩,⟨32,18,1,0,0,[0,1,2,3,4,5],0xcccc0000#64⟩,⟨38,0,1,0,0,[0,1,2,3,4,5],0x3030303#64⟩,⟨36,0,1,0,0,[0,1,2,3,4,5],0xf0f0f0f#64⟩,⟨16,10,1,0,0,[0,1,2,3,4,5],0xcc000000cc00#64⟩,⟨16,36,1,0,0,[0,1,2,3,4,5],0xf0f000000000#64⟩,⟨2,20,1,0,0,[0,1,2,3,4,5],0x3030000030300000#64⟩,⟨2,36,1,0,0,[0,1,2,3,4,5],0x3030303000000000#64⟩,⟨0,34,2,0,0,[0,1,2,3,4,5],0xcccccccc00000000#64⟩,⟨20,2,1,0,0,[0,1,2,3,4,5],0xc0c00000c0c#64⟩,⟨32,10,1,0,0,[0,1,2,3,4,5],0xcc00cc00#64⟩,⟨4,34,1,0,0,[0,1,2,3,4,5],0xc0c0c0c00000000#64⟩]
def F13T3 : BTree NodeData := nd (nd (nd (lf2 0x50c435481004076 0x26176 []) (nd (lf2 0x1c14310c1005066 0x65776 [0x1]) (lf2 0x5954310c1004836 0x64a87 []))) (nd (nd (lf2 0x1d54310c1006036 0xdd982 [0x2]) (lf2 0xdd54310c1005036 0x64b76 [])) (nd (lf2 0xdd94310c1006066 0xe1680 [0x1e03]) (lf2 0xdd94310c1006036 0xe1582 [])))) (nd (nd (nd (lf2 0xdd94310c1005036 0x64885 [0xe04]) (lf2 0xdd94310c1005036 0x64b85 [0xe04])) (nd (lf2 0xdd94310e2006066 0xe1680 [0x1e030005]) (lf2 0xdd94310e2006036 0xe1582 [0x1e04]))) (nd (nd (lf2 0xdd94310e2005056 0xa4785 [0x5]) (lf2 0xdd95410d3206026 0x60080 [0xf03])) (nd (lf2 0xdd95410d3206026 0xe0280 [0xf03]) (lf2 0xdd95410d3205016 0xa4460 []))))
def F13T4_0 := nd (nd (nd (nd (lf2 0x50c438801003425 0x175 [0x6]) (nd (lf2 0x50c438801003465 0x175 [0x1c080007]) (lf2 0x50c438801002665 0x387 [0x1c0400071c08]))) (nd (nd (lf2 0x588410c01003385 0x172 [0x10a0109]) (lf2 0x588410c010023c5 0x187 [0x80003])) (nd (lf2 0x5d8410c010023c5 0x382 []) (lf2 0x589420c010031a5 0x375 [])))) (nd (nd (nd (lf2 0xd50434c81002435 0x187 [0x1e03140b]) (lf2 0x590434c81003035 0x175 [0x1e031e08110c,0x40b])) (nd (lf2 0x590434c81002235 0x387 [0xd1e080006,0xe]) (lf2 0x592534c81002135 0x387 [0xd]))) (nd (nd (lf2 0xd92534c81003035 0x274 [0x20a]) (lf2 0x9da544c81003035 0x343 [0x20a])) (nd (lf2 0xd93624c81003235 0x274 [0x20f]) (lf2 0x184604c81003985 0x152 [0xc]))))) (nd (nd (nd (lf2 0x50f424c81002c35 0x385 []) (nd (lf2 0x94f424c81003835 0x364 [0x20a]) (lf2 0x50d524c81002535 0x87 []))) (nd (nd (lf2 0x1cd524c81002c35 0x184 []) (lf2 0x54d524c81002c35 0x384 [0x1e08])) (nd (lf2 0x590434c81003075 0x175 [0x40b00021e08]) (lf2 0x590434c81002275 0x387 [0x810000d1c04])))) (nd (nd (nd (lf2 0x951434c81002475 0x287 [0x20a]) (lf2 0x592534c81002175 0x387 [0x809000d])) (nd (lf2 0x5c8544c810030b5 0x364 [0x20a]) (lf2 0x58a64cc81003135 0x175 []))) (nd (nd (lf2 0x95143cc81002c35 0x182 []) (lf2 0x5c8435481003435 0x143 [])) (nd (lf2 0x50c435481003075 0x176 [0x11]) (lf2 0x50c435481002875 0x86 [0x40b])))))
def F13T4_1 := nd (nd (nd (nd (lf2 0x50c435481002475 0x387 [0x2]) (nd (lf2 0x58c635481003075 0x174 [0x11]) (lf2 0x58c635481002875 0x84 [0x180b]))) (nd (nd (lf2 0x58c635481002175 0x387 [0x2]) (lf2 0x50c43d481003035 0x176 [0x1e03140b])) (nd (lf2 0x50c43d481003075 0x176 [0x210000d]) (lf2 0x50c43d481002475 0x387 [0x2])))) (nd (nd (nd (lf2 0x50d6210c1003075 0x375 [0x12]) (lf2 0x1c14310c1003865 0x165 [0x16080001])) (nd (lf2 0x1c14310c1003265 0x376 [0x11608]) (lf2 0xdc94310c1003075 0x165 [0x110c1e080002]))) (nd (nd (lf2 0x5954310c1002835 0x382 [0x21e031a0b]) (lf2 0x5954310c1002875 0x382 [0x2])) (nd (lf2 0x5954310c1002875 0x87 [0x6]) (lf2 0x5954310c1002875 0x287 [0x20b]))))) (nd (nd (nd (nd (lf2 0x1d54310c1002c35 0x182 [0x604]) (lf2 0x1d54310c1003075 0x376 [0x900121604])) (nd (lf2 0xdd54310c1003075 0x376 [0x1604]) (lf2 0xdd94310c1003265 0x280 [0x50e08]))) (nd (nd (lf2 0xdd94310c1003235 0x182 [0x131e080012]) (lf2 0xdd94310c1003235 0x282 [0x141e08])) (nd (lf2 0xdd94310c1003075 0x85 [0xe040012]) (lf2 0xdd94310c1003075 0x185 [0x13])))) (nd (nd (nd (lf2 0xdd94310c1003075 0x285 [0x13]) (lf2 0xdd94310c1003075 0x385 [0xe040e030e08])) (nd (lf2 0xdd94310c1002a35 0x182 [0x1e0300121e08,0x100c]) (lf2 0xdd94310c1002875 0x185 [0x900010006]))) (nd (nd (lf2 0xdc95350c1003435 0x154 [0x1e080810]) (lf2 0xdc95350c1003435 0x254 [0x15])) (nd (lf2 0x9da5350c1002135 0x182 [0x1009]) (lf2 0x1d16214c1002935 0x183 [])))))
def F13T4_2 := nd (nd (nd (nd (lf2 0x9d16214c10030b5 0x374 [0x13]) (nd (lf2 0x5954310c2003025 0x70 [0xa16]) (lf2 0x593438c22002225 0x387 [0x1416]))) (nd (nd (lf2 0x50c439462002475 0x387 [0x2]) (lf2 0x590434ca2002235 0x387 [0x1e081c04000d,0x1])) (nd (lf2 0xdd94310e2003265 0x280 [0x120e04]) (lf2 0xdd94310e2003235 0x182 [0x130e030012])))) (nd (nd (nd (lf2 0xdd94310e2003075 0x85 [0x170002]) (lf2 0xdd94310e2003075 0x185 [0x13])) (nd (lf2 0xdd94310e2003075 0x285 [0x1e03]) (lf2 0xdd94310e2003075 0x385 [0xe030e080e04]))) (nd (nd (lf2 0xd0c605083002a65 0x286 [0x6090018]) (lf2 0xd0d525083002c35 0x185 [])) (nd (lf2 0x590435483002c15 0x81 [0x18090619]) (lf2 0x5906454830028d5 0x81 [0x2]))))) (nd (nd (nd (lf2 0x5906454830020f5 0x387 [0x2]) (nd (lf2 0x5db5410e3002035 0x382 [0x21e03]) (lf2 0xdd95410d3203035 0x80 [0xf080f030006,0x1]))) (nd (nd (lf2 0xdd95410d3203035 0x280 [0xf080f03000d,0x1]) (lf2 0xdd95410d3203035 0x60 [0xf030c1a])) (nd (lf2 0xdd95410d3203035 0x260 [0x60c10]) (lf2 0x1c5501413203405 0x342 [0x21005])))) (nd (nd (nd (lf2 0x1c5501413203505 0x182 [0x319030b001b]) (lf2 0xd09501413202425 0x87 [0x31c])) (nd (lf2 0xdd9501413203125 0x162 [0x130f080002,0xe04]) (lf2 0x541621413202d05 0x81 [0x303]))) (nd (nd (lf2 0x541621413202c25 0x84 [0x303]) (lf2 0x58060d093202825 0x85 [0x111c])) (nd (lf2 0x59465d093202825 0x80 [0x207161a1a]) (lf2 0x59465d093202035 0x387 [0x14])))))
def F13T4_3 := nd (nd (nd (nd (lf2 0x1c1541513203425 0x182 [0x31d0f08001b]) (nd (lf2 0x1c1541513203425 0x120 [0x703]) (lf2 0xdd9541513203035 0x182 [0x13001e0014]))) (nd (nd (lf2 0xdd9541513203035 0x362 [0x130b0f03131d,0xe040f08]) (lf2 0x509301413203425 0x74 [0x1f1816])) (nd (lf2 0x509301413202525 0x87 [0x181d1f081604,0x303]) (lf2 0x1d1301413203425 0x182 [0x1e041816])))) (nd (nd (nd (lf2 0x5516210d3202c25 0x80 [0x1e04061d181a]) (lf2 0x5516210d3202835 0x386 [0x1b030006000d,0x1b080001])) (nd (lf2 0xdd95410d3203035 0x182 [0x1f081f03000d,0x2000060012,0x1]) (lf2 0xdd95410d3203035 0x382 [0x60f03000d,0x10f08]))) (nd (nd (lf2 0xdd95410d3203035 0x362 [0xe040c1a0c10]) (lf2 0x9d85450d3203035 0x182 [0x1e04101c100f])) (nd (lf2 0xdd9541533203035 0x182 [0x1e04101a1010]) (lf2 0x9d85450f3203035 0x182 [0x1e04101a1010]))))) (nd (nd (nd (nd (lf2 0xdd5435484303435 0x182 [0x21]) (lf2 0xdd9435484302235 0x182 [0x21181a1810])) (nd (lf2 0x9c46050c4303075 0x365 [0x20]) (lf2 0xd946050c4303865 0x280 [0x131b03]))) (nd (nd (lf2 0x1c36550c4303865 0x270 [0x131703]) (lf2 0x1c36550c4302875 0x281 [0x20])) (nd (lf2 0x1c36550c4302835 0x182 [0x70400051010]) (lf2 0x1c36550c4302875 0x182 [0x2])))) (nd (nd (nd (lf2 0x9c36550c4302875 0x281 [0x20]) (lf2 0x9c36550c4302875 0x182 [0x2])) (nd (lf2 0x5cb6550c4302875 0x80 [0xf03]) (lf2 0x5cb6550c4303835 0x372 [0xf04]))) (nd (nd (lf2 0x9cb6550c4302835 0x187 [0x1f0300120013,0x1f080020]) (lf2 0xdcb6550c4302875 0x280 [0x14])) (nd (lf2 0x5db4354a4303835 0x10 [0xf0800220a0c]) (lf2 0x9db4354a4303835 0x10 [0x20f])))))
def F13T4 : BTree NodeData := nd (nd F13T4_0 F13T4_1) (nd F13T4_2 F13T4_3)
def F13M4 : BST := BN 215780047 640 (BN 176382803 770 (BN 135748537 768 (BL 94876749 512) (BL 142948311 1920)) (BN 192926208 1280 (BL 182922120 1792) (BL 201375073 514))) (BN 330646100 384 (BN 262953630 1664 (BL 223639178 0) (BL 265856884 128)) (BN 367143700 1536 (BL 364961906 256) (BL 384841722 1152)))
def F13T5_0 := nd (nd (nd (nd (lf 0x50c438801001e24 [0x100006]) (nd (lf 0x5d44388010015a4 [0xf0011]) (lf 0x54e438801001d24 [0x100e08020c]))) (nd (nd (lf 0x5d64388010015a4 [0x20c041d0010]) (lf 0x50e218801001f84 [0x808060c0007,0x2308040618,0x24])) (nd (lf 0xdd53288010015a4 [0x21800040e08,0x41d]) (lf 0x50f328801001f24 [0x1006080618,0x1f])))) (nd (nd (nd (lf 0x50c438801001e64 [0xc040c080007]) (lf 0x5d44388010015e4 [0x30c080007,0x4])) (nd (lf 0xdc94388010017a4 [0x20c020b0021]) (lf 0x5ca4388010017a4 [0xc080021]))) (nd (nd (lf 0xd0e438801001e64 [0xc0400070c08]) (lf 0x5d64388010015e4 [0x40007])) (nd (lf 0x588410c01001bc4 [0x10a]) (lf 0x5d8410c010013c4 [0x1a00250016]))))) (nd (nd (nd (lf 0x589420c01001ba4 [0x1f01090e08]) (nd (lf 0xdcd420c01001764 [0xc]) (lf 0xdd5420c010015e4 [0xc]))) (nd (nd (lf 0xdd9420c010013e4 [0xe08]) (lf 0x885620c01001bc4 [0x1f0608])) (nd (lf 0x9c5620c01001bc4 [0x1a]) (lf 0x909620c01001ba4 [0x1f0608])))) (nd (nd (nd (lf 0xd50434c81001c34 [0x210810060b,0xc]) (lf 0x590434c81001a34 [0x40b08100006,0x41d])) (nd (lf 0x5d4434c81001534 [0xe08020f000e,0x40b]) (lf 0x553434c81001c34 [0xe080026090c,0x218]))) (nd (nd (lf 0xd93434c81001a34 [0x118010c0e08,0xe03]) (lf 0x5d7434c81001534 [0x9180e030001,0x9])) (nd (lf 0x1d1534c81001634 [0x10c020f0a0b]) (lf 0x592534c81001934 [0x1d08090518,0xb])))))
def F13T5_1 := nd (nd (nd (nd (lf 0xd92534c81001934 [0xe080e030518,0x20a0809]) (nd (lf 0x9da534c81001534 [0x20a00040027]) (lf 0xd90544c810018b4 [0xa0b000c0006]))) (nd (nd (lf 0x9d8544c810011b4 [0xe080e030013]) (lf 0x1d9544c810011b4 [0x210026])) (nd (lf 0x9da544c810011b4 [0x400130006]) (lf 0x5d0654c810014b4 [0xe0802180e03,0xd04])))) (nd (nd (nd (lf 0x9d0654c810014b4 [0xe08020a0e03,0xd04]) (lf 0x184604c81001b44 [0xd040a080028,0xc001b])) (nd (lf 0x548604c81001d24 [0xe08021d001b]) (lf 0x1d9524c81001534 [0x20004001b]))) (nd (nd (lf 0x551524c81001d34 [0xe080026020f]) (lf 0xd93624c81001b34 [0xe080618001b,0x104001f])) (nd (lf 0x197624c81001934 [0x8100021060b,0xa0f]) (lf 0x5c8544c81001534 [0x5040002]))))) (nd (nd (nd (lf 0x9d8544c81001174 [0xd040028]) (nd (lf 0x5d4644c81001574 [0xe0800260028,0x40029]) (lf 0xd97644c81001974 [0x4090028]))) (nd (nd (lf 0x9d0654c81001474 [0x20a0d04001b]) (lf 0x184604c81001bc4 [0xd040a080028,0x603])) (nd (lf 0x548604c81001da4 [0xe08000c]) (lf 0x94f424c81001c34 [0xe080e03000d])))) (nd (nd (nd (lf 0x50f424c81001e34 [0x6030e080021,0x60b020a]) (lf 0x90f424c81001e34 [0x130e08060b,0x409])) (nd (lf 0x94f424c81001d34 [0xd00210409,0x918020a]) (lf 0xd93424c81001ab4 [0xe08040b0a0b,0x104040c]))) (nd (nd (lf 0x50d524c81001d34 [0x2020a]) (lf 0x90d524c81001d34 [0x13])) (nd (lf 0x1cd524c81001d34 [0xc001b]) (lf 0xdcd524c81001d34 [])))))
def F13T5_2 := nd (nd (nd (nd (lf 0x591524c810019b4 [0xb000d001d,0x809]) (nd (lf 0xd91524c810019b4 [0x180013001b]) (lf 0x54d524c81001d34 [0xe08001b001d,0x504000b]))) (nd (nd (lf 0x94d524c81001d34 [0xb0904001d]) (lf 0x590434c81001a74 [0xc04041d000d,0x40b0810])) (nd (lf 0x5d4434c81001574 [0xe0026020f,0x20029]) (lf 0x951434c81001c74 [0x1b020a])))) (nd (nd (nd (lf 0xd95434c81001974 [0x28000a]) (lf 0xdd5434c81001574 [0x20004])) (nd (lf 0x152434c81001c74 [0x20a000d]) (lf 0xd96434c81001974 [0xa0028]))) (nd (nd (lf 0x5d6434c81001574 [0xc0013]) (lf 0xd93434c81001a74 [0xe08001b0c04,0x100028])) (nd (lf 0x5d7434c81001574 [0x4020f0002]) (lf 0x9d0534c81001474 [0xe03020a0d04,0x90e08]))))) (nd (nd (nd (lf 0x1d1534c81001674 [0x81d020f0a0b,0x1b0d04]) (nd (lf 0xdd1534c81001674 [0x140d040e08]) (lf 0x592534c81001974 [0xb001d000d,0x809]))) (nd (nd (lf 0xd92534c81001974 [0x8090518001b]) (lf 0x9da534c81001574 [0x9000d])) (nd (lf 0x5c8544c810015b4 [0xc03001d020a,0xd0c08000b,0xc0009]) (lf 0xd90544c810018f4 [0xc001b020a])))) (nd (nd (nd (lf 0x9d8544c810011f4 [0x1b00130d04]) (lf 0x9da544c810011f4 [0x130006001b,0xb])) (nd (lf 0xdd5644c810011f4 [0x100060e08]) (lf 0x5d7644c810011f4 [0xc0006]))) (nd (nd (lf 0x9d0654c810014f4 [0x20a001b0d04]) (lf 0x9d8654c810011f4 [0x2a020b])) (nd (lf 0xdd1654c810012f4 [0x10e080006]) (lf 0x590548c810018b4 [0x809000c0a0b,0x1180e03])))))
def F13T5_3 := nd (nd (nd (nd (lf 0x5d8548c810011b4 [0xe0305040013,0xe08]) (nd (lf 0x592548c810018b4 [0xe08020a0118,0xc08090e03]) (lf 0x5da548c810011b4 [0xc00130006]))) (nd (nd (lf 0x1d5648c810018b4 [0xc0c10060b,0x11804090e03]) (lf 0xdd5648c810018b4 [0x90c0e080006,0x409])) (nd (lf 0x5c854cc81001534 [0x5040002]) (lf 0x5ca54cc81001534 [0xe080e030002,0x20a])))) (nd (nd (nd (lf 0x58a64cc81001b34 [0x60b0a0a0e08,0x10400210a03]) (lf 0x5d664cc81001574 [0x200220218])) (nd (lf 0x50f52cc81001d34 [0xc04100218]) (lf 0x95143cc81001c74 [0x110009001b]))) (nd (nd (lf 0xdd543cc81001574 [0x40002]) (lf 0x5d743cc81001574 [0x400010022,0x40b0002])) (nd (lf 0x5c854cc810015b4 [0x4000c0c10]) (lf 0x5ca54cc810015b4 [0x6020a000c,0x4]))))) (nd (nd (nd (lf 0x59254cc810018f4 [0x1100090006]) (nd (lf 0xdd564cc810011f4 [0x6]) (lf 0x5ce325481001534 [0xc0a00040002]))) (nd (nd (lf 0x5ce3254810015b4 [0x9000b001d,0xc]) (lf 0x5d23254810014b4 [0x40e08000d])) (nd (lf 0x5d23254810015b4 [0x1d00180013,0xb]) (lf 0x9da3254810015b4 [0x408000b001d])))) (nd (nd (nd (lf 0x5c84354810015b4 [0xb0304001d,0x818080c]) (lf 0x50c435481001c74 [0x9000d0c0b,0xc])) (nd (lf 0x5d84354810011f4 [0x1100030008,0xc0009]) (lf 0x9d84354810011f4 [0x4000d001b,0xb]))) (nd (nd (lf 0x1d94354810011f4 [0xc000b0004,0x9]) (lf 0xdd94354810011f4 [0x60002])) (nd (lf 0x5ca4354810015b4 [0x80a0018001b,0xb]) (lf 0xd0e435481001c74 [0xd001b])))))
def F13T5_4 := nd (nd (nd (nd (lf 0x5da4354810011f4 [0xc00060002]) (nd (lf 0x9da4354810011f4 [0x90013]) (lf 0x58c635481001974 [0x11080b]))) (nd (nd (lf 0x5d06354810014f4 [0x90002]) (lf 0x9d06354810014f4 [0x20c0b001b])) (nd (lf 0xdc96354810015b4 [0xc0011]) (lf 0x1d16354810014f4 [0xc0c0b0002])))) (nd (nd (nd (lf 0xdd16354810014f4 [0xc0b0002]) (lf 0x5ca6354810015b4 [0x1000b001d,0x304])) (nd (lf 0xd8e635481001974 [0x10002]) (lf 0x5d23254810016b4 [0x40e08]))) (nd (nd (lf 0x1d15354810014f4 [0x2080b001b,0xc0810]) (lf 0xdd15354810014f4 [0x2080b0e08])) (nd (lf 0xd8e535481001974 [0x280001]) (lf 0x50c43d481001c34 [0x2100c0b0006]))))) (nd (nd (nd (lf 0x5d843d4810011b4 [0xe0300010006,0xd001b0e08]) (nd (lf 0x5da43d4810011b4 [0xc00130006]) (lf 0x9cc32d481001534 [0xc180e030c0b,0xc]))) (nd (nd (lf 0x9d032d4810014b4 [0x80c0e030c0b,0x21]) (lf 0x5d232d4810014b4 [0xe030c0b000d])) (nd (lf 0x9d232d4810014b4 [0xc0e030c0b,0x21]) (lf 0x50c43d481001c74 [0x210000d])))) (nd (nd (nd (lf 0x5d843d4810011f4 [0x1b000d0210]) (lf 0xdc943d4810015b4 [0x304000d000c,0x18])) (nd (lf 0xdd943d4810011f4 [0x6]) (lf 0x5ca43d4810015b4 [0x1b00090c0b,0x304080c]))) (nd (nd (lf 0xd0e43d481001c74 [0xd001b]) (lf 0x5da43d4810011f4 [0x4000d0011])) (nd (lf 0x50d6210c1001a74 [0x60b00140e08,0xe040e03]) (lf 0xdd56210c10011f4 [0x270004002b])))))
def F13T5_5 := nd (nd (nd (nd (lf 0x1c14310c1001e64 [0x10c0e080001]) (nd (lf 0xdc94310c1001674 [0xe080014000d,0x20b010c0e04]) (lf 0x5954310c1001874 [0x110e030e08,0x20b090c]))) (nd (nd (lf 0x5954310c1001a74 [0x10e080011,0x90e03]) (lf 0x1d54310c1001c74 [0x906040006])) (nd (lf 0xdd54310c1001c74 [0x20b00090006]) (lf 0xdd94310c1001274 [0x280e030e08,0xe04])))) (nd (nd (nd (lf 0xdd94310c1001a74 [0x10c0e080006,0x10e03]) (lf 0x5db5310c1001174 [0x1f0026])) (nd (lf 0xdc96510c10011b4 [0xe080810080f,0x2]) (lf 0xdc96510c10011f4 [0x2]))) (nd (nd (lf 0x1846050c1001bc4 [0x180e04000c,0xa08]) (lf 0x94f6250c1001974 [0x9180002000d])) (nd (lf 0xdc95350c1001734 [0xe08080b]) (lf 0x5515350c1001c74 [0x20b0e08021d,0x10090c]))))) (nd (nd (nd (lf 0x9515350c1001c74 [0x90c020b021d,0x90011]) (nd (lf 0x5ca5350c1001574 [0xa0002]) (lf 0x9da5350c1001174 [0x20026]))) (nd (nd (lf 0x9da5350c1001574 [0x90022]) (lf 0x9525350c1001c74 [0x1100260006,0x9])) (nd (lf 0x5c86550c10015b4 [0xc100c0f0204]) (lf 0x9d86550c10011f4 [0x6])))) (nd (nd (nd (lf 0xdc96550c10013b4 [0xb0e08001d]) (lf 0x5cb6550c10011b4 [0xc0e080006])) (nd (lf 0x5cb6550c10011f4 [0x800030002]) (lf 0xd0d6290c1001a34 [0x210e08040f,0x280013]))) (nd (nd (lf 0x54d6290c1001934 [0xe080e03040c,0x20026040a]) (lf 0x54d6290c1001b34 [0x40f0e08060b,0x2c0009])) (nd (lf 0x1516290c10018b4 [0x60b040c040a,0x20e03]) (lf 0xd0d6290c1001a74 [0x1b0e040014,0xe08])))))
def F13T5_6 := nd (nd (nd (nd (lf 0xdc95390c1001534 [0xe08001f0810,0x26]) (nd (lf 0x5c85490c10014b4 [0xe080e03000d]) (lf 0xdc96590c10011b4 [0x180e03000b]))) (nd (nd (lf 0xdc96590c10011f4 [0x2]) (lf 0x1d16214c10019b4 [0x608001d0603,0x90013000b,0x180002])) (nd (lf 0x5d16214c10018b4 [0xe080e030002,0x809]) (lf 0x5d16214c10019b4 [0x603001d0809,0x1b0608000b,0x180002])))) (nd (nd (nd (lf 0x9d16214c10018b4 [0xe080e030002,0x809]) (lf 0x9d16214c10019b4 [0x180002060f])) (nd (lf 0xdd16214c10019b4 [0x20018001b]) (lf 0x1096214c10019b4 [0x304]))) (nd (nd (lf 0x9096214c10019b4 [0xa0018001b,0x2]) (lf 0x5ca6414c10010f4 [0x7040002])) (nd (lf 0x5536254c10019b4 [0x1f0e080410,0x18]) (lf 0x9536254c10019b4 [0x410000c0006]))))) (nd (nd (nd (lf 0xd925454c10018f4 [0x80b0006]) (nd (lf 0x1096294c10019b4 [0x304]) (lf 0x9496294c10019b4 [0x304]))) (nd (nd (lf 0x5ce5494c1001574 [0x260006]) (lf 0xdd9540c420018b4 [0xe030d080c10,0x50c])) (nd (lf 0xdd9540c420011b4 [0xa040c100d08,0xc0e03]) (lf 0xdd9548c420018b4 [0x50b0e03051a])))) (nd (nd (nd (lf 0x50c439442001c34 [0xc0b02100021]) (lf 0x5954310c2001834 [0x210011])) (nd (lf 0x5cd6510c2001934 [0x204]) (lf 0x593438c22001a24 [0x118010c041d]))) (nd (nd (lf 0x5d7438c22001524 [0xf080023000f,0x810090c]) (lf 0xdd9540c620011b4 [0xc0a0f0816])) (nd (lf 0x50c439462001c34 [0x2100c0b0c16,0x1]) (lf 0xdd94310e2001a34 [0x10c0e030006,0x1300070001])))))
def F13T5_7 := nd (nd (nd (nd (lf 0x10d428c22001e24 [0x1f04100c16]) (nd (lf 0x94d428c22001d24 [0xa04041d041a]) (lf 0x551620c620019b4 [0x40c00090018,0x603000f]))) (nd (nd (lf 0xdd9540c620011f4 [0x2e002d001b]) (lf 0x50f329462001d34 [0x2100708040b,0xc])) (nd (lf 0x50c439462001c74 [0x2f0c0b0c16,0x210]) (lf 0xdc94394620015b4 [0x308002f000b,0x210204])))) (nd (nd (nd (lf 0x5ca4394620015b4 [0x80a00180030,0xc0302030204]) (lf 0xd0e439462001c74 [0x2f0030])) (nd (lf 0xd50434ca2001c34 [0x2108100616,0xc]) (lf 0x590434ca2001a34 [0x4190e03000d,0x10e08041d]))) (nd (nd (lf 0xd93434ca2001a34 [0xe08010c0006,0x1]) (lf 0x9da534ca2001534 [0x1a002b])) (nd (lf 0xd90544ca20018b4 [0xa0b01180a1d,0xc]) (lf 0x9da544ca20011b4 [0xa0a000c0e03,0xc04000b]))))) (nd (nd (nd (lf 0xdd954cca2001134 [0x1f00210e03]) (nd (lf 0xdd153cca2001434 [0x2180810]) (lf 0xdc94310e2001634 [0x21002f]))) (nd (nd (lf 0xdd94310e2001274 [0xe080e030e04,0x20007]) (lf 0xd0d6290e2001a34 [0x20e040030])) (nd (lf 0x1516290e20018b4 [0x60b061d0021,0x40c]) (lf 0x5c85490e20014b4 [0x202160c10])))) (nd (nd (nd (lf 0xdd1520c43001d34 [0x28040f]) (lf 0x909520c43001d34 [0xc03001b])) (nd (lf 0x589520c43001934 [0xa0a0d080e03,0x50a]) (lf 0x5d95210430011b4 [0x81a0e030025]))) (nd (nd (lf 0xdd95210430011b4 [0x1b0e03081a,0x18]) (lf 0x5895210430019b4 [0xa040403081a,0x818000a040c])) (nd (lf 0x5d95210430011f4 [0xc0002081a,0xb]) (lf 0xdd95210430011f4 [0x81a0028])))))
def F13T5_8 := nd (nd (nd (nd (lf 0xdc96510430011f4 [0x25081a]) (nd (lf 0x58d529043001934 [0x18040c0419,0x9]) (lf 0x5895290430019b4 [0xa040018081a,0x40c]))) (nd (nd (lf 0xdc9639043001334 [0x818081a001f]) (lf 0xdcd429443001534 [0x20c0d080c0b,0x318])) (nd (lf 0xd0d429443001c74 [0x41a]) (lf 0xdcd429443001574 [0x2f0c0b041a])))) (nd (nd (nd (lf 0x5ce429443001534 [0x3180d080c0b,0x80a]) (lf 0x5cb439443001534 [0xc0b081a])) (nd (lf 0xd92544c830018b4 [0xa0b01180e03,0x20a]) (lf 0x9da544c830011b4 [0xb08090e03,0xc]))) (nd (nd (lf 0x9c4544c83001554 [0xe03020a0d04,0x20b0009]) (lf 0x5c8544c83001534 [0x20a0504001a])) (nd (lf 0xd92544c830018f4 [0x1300060809,0xe03]) (lf 0x592548c830018b4 [0x118020a0e03,0xa080a0b]))))) (nd (nd (nd (lf 0x5da548c830011b4 [0xf080e030809,0x4000b]) (nd (lf 0x1c1648c83001aa4 [0xe03080c0c09,0x18]) (lf 0xdd5648c830018b4 [0xf0804090e03,0x60b]))) (nd (nd (lf 0x95142cc83001c34 [0x60b0e03001b,0x608]) (lf 0xdd542cc83001534 [0xf080e030409,0x4020b])) (nd (lf 0x5ca54cc83001534 [0xf080e030809,0x4020b]) (lf 0x10c605083001e24 [0xa030118061a])))) (nd (nd (nd (lf 0x18c605083001b24 [0xa030118061a]) (lf 0xd8c605083001b24 [0x6090118002a])) (nd (lf 0x9d8435083001634 [0x2d001f000d]) (lf 0x5d7635083001334 [0xc0f0f08000c]))) (nd (nd (lf 0x9da5450830014b4 [0x2090004001c]) (lf 0x9c4655083001594 [0x20b02090e03,0xd04])) (nd (lf 0x9d86550830011b4 [0xf080e030209,0x4000b]) (lf 0x10d655083001a34 [0x209])))))
def F13T5_9 := nd (nd (nd (nd (lf 0x10f6550830018b4 [0x209]) (nd (lf 0x90f6550830018b4 [0x209]) (lf 0x10f655083001a34 [0x209]))) (nd (nd (lf 0x548605083001ca4 [0x609021d0002,0xa0c]) (lf 0xd88605083001aa4 [0x2106090a16,0xa0c0e03050a])) (nd (lf 0x18c605083001a64 [0xd040a1d061a,0x18]) (lf 0x18d525083001c34 [0xe03021a0002])))) (nd (nd (nd (lf 0xd8d525083001c34 [0x2001f]) (lf 0xd8f625083001a34 [0x60c002f])) (nd (lf 0xd976250830018b4 [0xe03002f]) (lf 0x9c46550830014d4 [0x2090d04000d]))) (nd (nd (lf 0x548605083001da4 [0x803000d0018]) (lf 0xd0c605083001e64 [0xd050a0018])) (nd (lf 0x18c605083001b64 [0xd0400180609,0xd]) (lf 0xd8c605083001b64 [0xa1d0018000d,0xf]))))) (nd (nd (nd (lf 0x10d525083001c34 [0xe03021a000d]) (nd (lf 0x18d525083001d34 [0x2090e030018,0x40c]) (lf 0xd8d525083001934 [0xa0b040f040c,0x50b0018]))) (nd (nd (lf 0xd8d525083001d34 [0xe0302090018]) (lf 0x1d1525083001cb4 [0x1805040028])) (nd (lf 0xdd1525083001cb4 [0x2090031]) (lf 0xd0d525083001e34 [0x209060c])))) (nd (nd (nd (lf 0x551525083001cb4 [0x6030009001d,0xa0504]) (lf 0x951525083001cb4 [0x9040009])) (nd (lf 0x5d7435083001674 [0x209020c]) (lf 0x9db435083001674 [0x18010a]))) (nd (nd (lf 0x5d7635083001374 [0xe03000c0014]) (lf 0x9da5450830014f4 [0x1b000a])) (nd (lf 0x9c46550830015d4 [0xd0d040209]) (lf 0x9d86550830011f4 [0xd0209])))))
def F13T5_10 := nd (nd (nd (nd (lf 0x5cc615483001534 [0x104]) (nd (lf 0x5d06154830014b4 [0x81a0e03001e]) (lf 0x5d06154830015b4 [0x290032081a,0x18]))) (nd (nd (lf 0x9d06154830014b4 [0x81a020f]) (lf 0x590435483001c34 [0x81a0e03000d,0x41d])) (nd (lf 0x5db435483001534 [0xf080e030002,0xa0f030b]) (lf 0x5db4354830011b4 [0xb0809001f,0x18])))) (nd (nd (nd (lf 0x5d36354830014b4 [0x104]) (lf 0x9d36354830014b4 [0x104])) (nd (lf 0x9c4645483001594 [0x13030b020f]) (lf 0x5cc645483001534 [0x20c030b0603]))) (nd (nd (lf 0x1c5645483001594 [0x1802190031,0x1b]) (lf 0xd926454830018b4 [0xa1900280033])) (nd (lf 0x5cf645483001534 [0x104]) (lf 0x5d7435483001534 [0x30b020f]))))) (nd (nd (nd (lf 0x5db435483001334 [0xf080e030c1d,0x1f]) (nd (lf 0xd925454830018b4 [0x81a0006]) (lf 0x5d36554830014b4 [0x104]))) (nd (nd (lf 0x9d36554830014b4 [0x104]) (lf 0x5d02154830014b4 [0x104])) (nd (lf 0x5d02154830015b4 [0x1c001f081a,0x18]) (lf 0x9d02154830014b4 [0x104])))) (nd (nd (nd (lf 0x9c4425483001594 [0x104]) (lf 0x9d04254830014b4 [0x104])) (nd (lf 0x5d24254830014b4 [0x104]) (lf 0x5d24254830015b4 [0x20c0009020f,0x18]))) (nd (nd (lf 0x9da4254830015b4 [0x90304]) (lf 0x5c8435483001534 [0x30a030b0e03])) (nd (lf 0x5cb435483001534 [0xc0b001f020f,0x30b]) (lf 0x9c46454830015d4 [0x28])))))
def F13T5_11 := nd (nd (nd (nd (lf 0x5906454830018f4 [0x2]) (nd (lf 0x1c56454830015d4 [0x18000d0002]) (lf 0xdc96454830015b4 [0x9000d0e03,0x18020c]))) (nd (nd (lf 0x5ca6454830015b4 [0x20c0009020f,0x3040006]) (lf 0xd926454830018f4 [0x60002])) (nd (lf 0x5d7435483001574 [0x2020f]) (lf 0xd925454830018f4 [0x3100060809,0xd])))) (nd (nd (nd (lf 0x5db439483001334 [0x21001f081a]) (lf 0x5925494830018b4 [0xb080118020f])) (nd (lf 0x5d562d0c3001934 [0x60b001f0002,0x80f]) (lf 0x9496295030019b4 [0xa00040603]))) (nd (nd (lf 0x5cb439463001534 [0x818001f0810]) (lf 0x5db5410e3001074 [0x210011])) (nd (lf 0x55162d0e3001834 [0xe030418001f]) (lf 0xdc954d0e3001434 [0xe030021080c]))))) (nd (nd (nd (lf 0x1d1301413201424 [0x816]) (nd (lf 0x1d1301413201524 [0x30a0816]) (lf 0x590431413201a34 [0x118080c0810,0x50b002d0f08]))) (nd (nd (lf 0x5905414132018b4 [0x21080c010f,0x50b0f08]) (lf 0x9935414132018b4 [0x10a0006])) (nd (lf 0x1c15410d3201424 [0x21d0c1a]) (lf 0xdd95410d3201034 [0xf030f08])))) (nd (nd (nd (lf 0xdd95410d3201434 [0xf080f030027,0x20b000d021d,0xc]) (lf 0xd4260d5132019a4 [0x303])) (nd (lf 0x151201413201d24 [0x903]) (lf 0x951201413201d24 [0x903]))) (nd (nd (lf 0x1d1201413201724 [0x103]) (lf 0x1c5501413201544 [0x3030e040034])) (nd (lf 0x1c5501413201564 [0xe040005001e,0x708]) (lf 0xd09501413201c24 [0x903])))))
def F13T5_12 := nd (nd (nd (nd (lf 0xd09501413201d24 [0x903]) (nd (lf 0xdc9501413201524 [0x1f001b0007,0x30a00140f08,0x303]) (lf 0x1d1501413201464 [0xe04031c0028,0x3030014]))) (nd (nd (lf 0x1d1501413201564 [0x140e04031c,0x280303]) (lf 0xdd9501413201564 [0xe0400140028,0x303])) (nd (lf 0x5ca511413201534 [0x1b021a0d03,0x30a]) (lf 0xd4a611413201934 [0x35090b0916])))) (nd (nd (nd (lf 0x541621413201d24 [0x303]) (lf 0x5ca541413201534 [0xd03030a0028,0x14])) (nd (lf 0xd0b509413201c24 [0x903]) (lf 0xd0b509413201d24 [0x903]))) (nd (nd (lf 0xd4a619413201934 [0x410090b0916,0x1f]) (lf 0x58060d093201a24 [0x303])) (nd (lf 0xd8260d093201a24 [0x303]) (lf 0x59465d093201834 [0x11c0014]))))) (nd (nd (nd (lf 0x1c165d093201624 [0x3160021020c]) (nd (lf 0xd9665d093201834 [0x14]) (lf 0x1c154d493201524 [0x3160c1a0021,0x1f]))) (nd (nd (lf 0x1c154d493201534 [0x21031d0014]) (lf 0x9c354d493201534 [0x41000210316])) (nd (lf 0x99354d493201834 [0xf08001f0021,0xf03]) (lf 0x1c1541513201464 [0xe040026])))) (nd (nd (nd (lf 0x1c1541513201474 [0xe0403160014,0x703]) (lf 0xd89541513201c34 [0x10f])) (nd (lf 0xdd9541513201074 [0xf080e040028,0xf03]) (lf 0xdd9541513201474 [0xe040028001b,0x10a0f080f03]))) (nd (nd (lf 0x5c8605513201b24 [0x708080c0021]) (lf 0x480605513201b24 [0x303])) (nd (lf 0xd51629513201834 [0x210028]) (lf 0x509301413201d24 [0x903])))))
def F13T5_13 := nd (nd (nd (nd (lf 0xd09301413201c24 [0x903]) (nd (lf 0xd09301413201d24 [0x903]) (lf 0x1d1301413201464 [0x30a0e040816]))) (nd (nd (lf 0x1d1301413201564 [0xe040816030a]) (lf 0xd0b401413201ca4 [0x903])) (nd (lf 0x5cb4014132015a4 [0xc0b030a0023,0x8180303]) (lf 0x10d421413201c34 [0x1f04100c16])))) (nd (nd (nd (lf 0xdc3421413201ca4 [0x503]) (lf 0x9d6431413201574 [0x360010])) (nd (lf 0x9935414132018f4 [0x6001b010a]) (lf 0x9ce435093201634 [0x20c021a0210,0x118]))) (nd (nd (lf 0x9d64350932014b4 [0x1f021a0210]) (lf 0x58060d093201aa4 [0x303])) (nd (lf 0x9cc60d093201634 [0x31d00020209,0x308030b0303]) (lf 0xd8260d093201aa4 [0x303]))))) (nd (nd (nd (lf 0x9d663d093201634 [0x21001e0014]) (nd (lf 0x9d663d0932014b4 [0x21a00210210]) (lf 0xd0260d093201aa4 [0x303]))) (nd (nd (lf 0x9d643d093201634 [0x2f0036]) (lf 0x9d643d0932014b4 [0x21a020c0210])) (nd (lf 0x99743d093201834 [0x10020c0021]) (lf 0x5516210d3201c34 [0x81a0810000d])))) (nd (nd (nd (lf 0x1c15410d3201464 [0xc090e040216]) (lf 0xdd95410d3201074 [0xf0800360e04,0x2f0f03])) (nd (lf 0xdd95410d3201474 [0xe04002f0036,0x409]) (lf 0x5c86050d3201334 [0x108080c080f]))) (nd (nd (lf 0x9d85450d3201074 [0x1c000f0e04]) (lf 0xd4260d5132019e4 [0x13001b])) (nd (lf 0xcc0605523201ca4 [0x303]) (lf 0x9c46055232014b4 [0x7080001])))))
def F13T5_14 := nd (nd (nd (nd (lf 0x589501433201924 [0x1b001a0b03]) (nd (lf 0x58a541433201934 [0x518001a001f,0x20b03]) (lf 0xdd9541533201074 [0x1a00100e04]))) (nd (nd (lf 0x5c8605533201334 [0x10b00210810]) (lf 0x5cb549533201434 [0x10001f0021])) (nd (lf 0x9d85450f3201074 [0x1a00100e04]) (lf 0x5cc605484301534 [0x104])))) (nd (nd (nd (lf 0x5d36354843014b4 [0x104]) (lf 0xdd5435484301c34 [0x1a0010000e,0xc])) (nd (lf 0xdd9435484301634 [0x81a08100021]) (lf 0x50c605484301c74 [0x31d00140010]))) (nd (nd (lf 0x50e605484301c74 [0x100002]) (lf 0xdc9435484301434 [0x14])) (nd (lf 0xdd9435484301074 [0x14]) (lf 0xdc9435484301634 [0x81a00210810]))))) (nd (nd (nd (lf 0xdd5435484301474 [0x1a00100d04,0x2]) (nd (lf 0xdd9435484301274 [0x81a0810000d,0x21]) (lf 0xdd5439484301434 [0x1a00100d04,0xc]))) (nd (nd (lf 0x5c86050c4301234 [0x1160810]) (lf 0x5c86050c4301274 [0x70401160810])) (nd (lf 0x9c46050c4301674 [0x80c0116030b]) (lf 0x5c86050c4301634 [0x7080c0810,0xf08])))) (nd (nd (nd (lf 0xd946050c4301874 [0xb0800100021,0x2800070017]) (lf 0x1c36550c4301874 [0x1700280010,0x7080704])) (nd (lf 0x9c36550c4301874 [0x70800280010,0x7040013]) (lf 0x5cb6550c4301034 [0x28]))) (nd (nd (lf 0x5cb6550c4301834 [0x280f080017,0x2100370f03]) (lf 0x5cb6550c4301074 [0x210014])) (nd (lf 0x5cb6550c4301874 [0xf080f030021,0x200200012]) (lf 0x9cb6550c4301834 [0x70400370017])))))
def F13T5_15 := nd (nd (nd (nd (lf 0xdcb6550c4301874 [0xf080f030021,0x200200012]) (nd (lf 0x1c36550c4301c74 [0x100017]) (lf 0x9c36550c4301c74 [0x1300060010]))) (nd (nd (lf 0x5cb6550c4301434 [0xf080017080c,0x370f030028]) (lf 0x5cb6550c4301c34 [0x80c00370017])) (nd (lf 0x5cb6550c4301234 [0x80c081a0810,0xc]) (lf 0x5cb6550c4301a34 [0x81a08100013,0xc080c])))) (nd (nd (nd (lf 0x5cb6550c4301274 [0x81a0810000d,0x20021]) (lf 0x5cb6550c4301a74 [0xd08090021])) (nd (lf 0x9cb6550c4301a34 [0x81a08100013,0x704]) (lf 0xdcb6550c4301a74 [0x13000d0021]))) (nd (nd (lf 0x5cb6550c4301634 [0x81a080c0810]) (lf 0x5cb6550c4301134 [0x818081c080f])) (nd (lf 0x5cb6550c4301934 [0x81c0021080f]) (lf 0x5cb6550c43011b4 [0x80a0809080c,0xb001d0818]))))) (nd (nd (nd (nd (lf 0x5da5490c4301074 [0x1a00100021]) (lf 0xd0e6054a4301c34 [0x200210030])) (nd (lf 0x9926054a43018b4 [0x810001e]) (lf 0x5db4354a4301834 [0xf08001f0017,0x370f030028,0x21]))) (nd (nd (lf 0x5db4354a4301434 [0x210014]) (lf 0x5db4354a4301c34 [0x21021c020f])) (nd (lf 0x9db4354a4301834 [0xf080021001f,0xf03]) (lf 0x5db4354a43014b4 [0x81a001f0810])))) (nd (nd (nd (lf 0x1c16454a43014a4 [0x3160021020c]) (lf 0x1c16454a43014b4 [0xc09031d0014])) (nd (lf 0x5d74354a4301434 [0x1a00100021]) (lf 0x5d74354a4301c34 [0x1a0010020c,0x21]))) (nd (nd (lf 0x5db4354a4301a34 [0x1f081a0810,0x21]) (lf 0x5cb4354a4301434 [0x14])) (nd (lf 0x5d74394a4301434 [0x1a00100d04]) (lf 0x5c965d0e4301c34 [0x21081c080f])))))
def F13T5 : BTree NodeData := nd (nd (nd (nd F13T5_0 F13T5_1) (nd F13T5_2 F13T5_3)) (nd (nd F13T5_4 F13T5_5) (nd F13T5_6 F13T5_7))) (nd (nd (nd F13T5_8 F13T5_9) (nd F13T5_10 F13T5_11)) (nd (nd F13T5_12 F13T5_13) (nd F13T5_14 F13T5_15)))
def F13M5 : BST := BN 278790726 2176 (BN 240516592 15360 (BN 207811179 9728 (BN 190087970 14720 (BN 186118949 5504 (BN 162124299 12416 (BN 161419611 16000 (BL 97423334 1664) BE) (BL 172820042 14976)) (BN 189808782 7810 (BL 187115736 10370) (BL 189913691 9472))) (BN 196967471 9856 (BN 196070480 9088 (BN 192706865 14336 (BL 192441800 7808) BE) (BL 196891355 4224)) (BN 203375181 13312 (BL 199977549 3201) (BL 206699209 11648)))) (BN 223581561 10882 (BN 215026191 6144 (BN 212230971 10240 (BN 211553030 7296 (BL 210393483 15744) BE) (BL 212382708 13184)) (BN 219904094 9216 (BL 218143955 9600) (BL 220601255 384))) (BN 230228942 4098 (BN 226964239 1410 (BN 225792944 2 (BL 224340092 6656) BE) (BL 229597257 1408)) (BN 236566254 10496 (BL 230362913 6784) (BL 239621069 10624))))) (BN 264527409 7552 (BN 251376045 5376 (BN 243983938 4736 (BN 242339118 5632 (BN 241002252 6400 (BL 240802378 12672) BE) (BL 243376819 13313)) (BN 247812817 9729 (BL 247142858 15488) (BL 249430840 0))) (BN 256398356 2690 (BN 254992107 14466 (BN 253866838 4096 (BL 253782630 3968) BE) (BL 255633067 10368)) (BN 261810425 15616 (BL 257852542 12544) (BL 263477683 7168)))) (BN 269127276 13696 (BN 266934213 10112 (BN 266407854 128 (BN 266219666 1024 (BL 265670855 15872) BE) (BL 266811263 14080)) (BN 268523520 10880 (BL 267335493 2304) (BL 268913763 6786))) (BN 276545883 5120 (BN 276335855 6272 (BN 276011596 2944 (BL 270464321 12928) BE) (BL 276529394 12160)) (BN 277240158 8064 (BL 276926942 7424) (BL 278219001 16256)))))) (BN 328863271 8960 (BN 306669057 4352 (BN 291691296 12290 (BN 286020326 896 (BN 280981881 14848 (BN 280793212 7936 (BL 279508447 9984) BE) (BL 284509285 15104)) (BN 289512535 4864 (BL 288153759 11264) (BL 290914789 256))) (BN 299237017 1537 (BN 296412015 9474 (BN 296007605 5633 (BL 294792338 6018) BE) (BL 297248671 13056)) (BN 300308671 12930 (BL 300176133 1792) (BL 301018465 11776)))) (BN 323509438 14464 (BN 315329192 12288 (BN 310262933 1152 (BN 309279829 13568 (BL 307362857 2688) BE) (BL 315160520 3841)) (BN 321466345 5248 (BL 319308271 7937) (BL 323209453 1536))) (BN 326061938 11392 (BN 324170054 1920 (BN 324086054 12800 (BL 323593247 640) BE) (BL 324271300 5250)) (BN 327672128 7680 (BL 326724232 5888) (BL 327731671 2048))))) (BN 361034745 12801 (BN 344657375 14592 (BN 340597966 3840 (BN 337882937 13058 (BN 337003647 14208 (BL 336187987 9344) BE) (BL 337980097 3328)) (BN 342416095 11520 (BL 340845697 1025) (BL 344422254 2816))) (BN 357874369 5378 (BN 356231214 1280 (BN 353662594 3200 (BL 345181648 6912) BE) (BL 356943133 10752)) (BN 359552265 16128 (BL 359539957 13440) (BL 360772103 12032)))) (BN 375883712 2560 (BN 371556690 4992 (BN 366795125 513 (BN 365901102 4608 (BL 362534726 3584) BE) (BL 371296762 11136)) (BN 374525162 7040 (BL 372302580 12162) (BL 375865666 13824))) (BN 390753807 6016 (BN 381534122 1154 (BL 378961160 15232) (BL 381914753 768)) (BN 393428779 3585 (BL 392719914 512) (BL 401245099 11008))))))
def F13T6_0 := nd (nd (nd (nd (nd (lf 0x438801000fa3 [0x10041d000f,0x608]) (lf 0x1438801000fa3 [0x20c06080006,0x10000f020b,0x218])) (nd (lf 0x2438801000fa3 [0x60800100006,0x41d]) (lf 0x1538801000da3 [0x1d0608020c,0x218]))) (nd (nd (lf 0x2218801000f83 [0x7041d020b,0x1f00340208,0x40021]) (lf 0x318801000fc3 [0x504041d0010,0x1c0034001f,0x23000f])) (nd (lf 0x1328801000fa3 [0x1a0608002a,0xf0021041d,0x6]) (nd (lf 0x3328801000fa3 [0x608001f0007,0xf00060021]) (lf 0x438801000fe3 [0x2b04040010,0x20b04080007]))))) (nd (nd (nd (lf 0x1438801000fe3 [0x23020c0404,0x208020b0408,0x1d02180006]) (lf 0x2438801000fe3 [0x20b001f0007,0x20804080023,0x1d])) (nd (lf 0x410c01000fc3 [0x403020b041d,0x208010a0109]) (nd (lf 0x1420c01000fe3 [0x109020b0608,0x1c001f]) (lf 0x3420c01000fe3 [0x34010a0608,0x1f0304020b])))) (nd (nd (lf 0x1620c01000be3 [0x109001d0608,0x10a001f]) (lf 0x1530c01000d63 [0x608001d001f])) (nd (lf 0x604c81000fa3 [0x60306080027,0x10c]) (nd (lf 0x434c81000f33 [0x40b00100027,0x20a]) (lf 0x3434c81000f33 [0x40b020f0001,0x10406030608])))))) (nd (nd (nd (nd (lf 0x1534c81000f33 [0x603020b010c,0x13000e0608,0x9020f0006]) (lf 0x2534c81000d33 [0x60806030027,0x20a0009])) (nd (lf 0x2534c81000f33 [0x21d06030027,0xc]) (nd (lf 0x544c81000db3 [0x20b06030013,0x9020a000c]) (lf 0x1544c81000db3 [0x6080603000e,0x90218000c])))) (nd (nd (lf 0x2544c81000db3 [0x60806030013,0xc020a]) (lf 0x3544c81000db3 [0x60302180001,0x9000c])) (nd (lf 0x1644c81000bb3 [0x608010c0006,0x118000b001d]) (nd (lf 0x3644c81000bb3 [0x10c06080006,0xc04090118,0xb0104]) (lf 0x654c81000db3 [0x406030027,0x9]))))) (nd (nd (nd (lf 0x3654c81000db3 [0x50406030027,0x20b0009]) (lf 0x604c81000f63 [0x50406080028,0xc0026001b])) (nd (lf 0x3424c81000e33 [0x6080028]) (nd (lf 0x3424c81000f33 [0x21020f0028]) (lf 0x1524c81000d33 [0x6030608001b,0x9020a])))) (nd (nd (lf 0x1524c81000f33 [0x10406080028,0x20f001b]) (lf 0x3624c81000f33 [0x1f00100028,0x20f0021001b])) (nd (lf 0x544c81000d73 [0x6030504001b,0xc020a020b]) (nd (lf 0x1544c81000f73 [0x60805040028,0x26020a]) (lf 0x2544c81000d73 [0x6080603001b,0x20a]))))))
def F13T6_1 := nd (nd (nd (nd (nd (lf 0x2544c81000f73 [0x504001b020f,0x218020b]) (lf 0x644c81000f73 [0x280026020f,0x404001b0029])) (nd (lf 0x3644c81000f73 [0x608001b0028,0x21801040404]) (nd (lf 0x654c81000d73 [0x50400210028,0x20a0026]) (lf 0x3654c81000d73 [0x905040028,0x218020a])))) (nd (nd (lf 0x604c81000fe3 [0x6080001000c,0x21d02030028]) (lf 0x3424c81000eb3 [0x40c041d0028,0x409040b0608,0x104])) (nd (lf 0x3424c81000fb3 [0x41d0028020f,0x608010c0021,0x10040c040b]) (nd (lf 0x1524c81000db3 [0x906080603,0x1d001b000c,0x218020a0504,0xb]) (lf 0x1524c81000fb3 [0x6030608020b,0x10c0010001d,0x4]))))) (nd (nd (nd (lf 0x3524c81000db3 [0xc06030001,0x1b06080009,0x2180006040f,0x20a]) (lf 0x434c81000f73 [0x41d0027020f,0x1b040b0021,0x20b])) (nd (lf 0x1434c81000f73 [0x10406080028,0x40402030218,0xc000f]) (nd (lf 0x2434c81000f73 [0x60802180028,0xf01040404,0xc]) (lf 0x3434c81000f73 [0x41d0028020f,0x608001b0021,0x104040b0203])))) (nd (nd (lf 0x534c81000d73 [0x50400210028,0x20a040f]) (lf 0x1534c81000f73 [0x20b0608021d,0x20305040028,0x9])) (nd (lf 0x2534c81000d73 [0x906030504,0x21800270608,0x20a]) (nd (lf 0x2534c81000f73 [0x20b0608021d,0xc05040028]) (lf 0x544c81000df3 [0xc0504020a,0xb0403001d,0x9001b0408])))))) (nd (nd (nd (nd (lf 0x2544c81000df3 [0xc0027020a,0xb0403001d,0x9001b0408]) (lf 0x1644c81000bf3 [0x608001d0006,0x3000c0028,0x404000b0001,0x18])) (nd (lf 0x3644c81000bf3 [0x608001d0006,0x2d00100118,0x1040404000b,0xc]) (nd (lf 0x654c81000df3 [0x2800090504,0x410020b021d,0x21]) (lf 0x1654c81000bf3 [0xf002a0608,0x1100010028])))) (nd (nd (lf 0x3654c810009f3 [0x60806030504,0xa00090027,0x280018]) (lf 0x3654c81000df3 [0x2a00280504,0x20b00090001])) (nd (lf 0x3654c81000bf3 [0x2a0608020b,0xc]) (nd (lf 0x1638c81000bb3 [0x6080010010c,0xb00210013,0x1180603]) (lf 0x548c81000db3 [0x20b06030013,0x9000c]))))) (nd (nd (nd (lf 0x2548c81000db3 [0x60806030013,0x504]) (lf 0x1648c81000ab3 [0x606080410,0x118010c])) (nd (lf 0x1648c81000bb3 [0x10c06080006,0xb04100118]) (nd (lf 0x352cc81000d33 [0x1b0603020b,0x1f0218]) (lf 0x54cc81000d73 [0x20a05040028,0x9001f])))) (nd (nd (lf 0x154cc81000f73 [0x60805040028,0x26020a020b]) (lf 0x254cc81000d73 [0x6080603001b,0x504])) (nd (lf 0x254cc81000f73 [0x60805040028,0x218020b]) (nd (lf 0x164cc81000f73 [0x1f001b0028,0x21801040608]) (lf 0x264cc81000f73 [0x608001b0028,0x10402030021,0x1f]))))))
def F13T6_2 := nd (nd (nd (nd (nd (lf 0x352cc81000db3 [0xc020b0410,0x40f0006001b,0x218]) (lf 0x143cc81000f73 [0x28001f0010,0x21801040608])) (nd (lf 0x343cc81000f73 [0x100028001b,0x10c06080021,0x40b0104]) (nd (lf 0x153cc81000f73 [0x6080011021d,0x280203020b,0x9010c]) (lf 0x54cc81000df3 [0x28001f0410,0x130504])))) (nd (nd (lf 0x254cc81000df3 [0x9001f020a,0x130504001b]) (lf 0x164cc81000bf3 [0x1d00100006,0x2d06080118,0x1f000b])) (nd (lf 0x165cc81000bf3 [0x100028020b,0x110608]) (nd (lf 0x1325481000d73 [0x104]) (lf 0x1325481000df3 [0x104]))))) (nd (nd (nd (lf 0x2325481000db3 [0x104]) (lf 0x3325481000d73 [0x104])) (nd (lf 0x3325481000df3 [0x104]) (nd (lf 0x435481000df3 [0xd001b0009,0xc0304040b,0x18000a]) (lf 0x1435481000df3 [0x304040b000c,0xa00180009])))) (nd (nd (lf 0x2435481000df3 [0x1d02030009,0xd000b0208,0xc0304040b,0x18000a]) (lf 0x635481000df3 [0xb001d0304,0x9040b000d,0xc])) (nd (lf 0x1635481000df3 [0x202030208,0x9000c040b]) (nd (lf 0x2635481000df3 [0x9040b0002,0xc]) (lf 0x3635481000df3 [0x304000d040b,0x9000c])))))) (nd (nd (nd (nd (lf 0x2325481000fb3 [0x104]) (lf 0x1535481000df3 [0xb001d0504,0xc06080010])) (nd (lf 0x2535481000df3 [0xb000d0504,0xc0009]) (nd (lf 0x3635481000bf3 [0x40b0104041d,0x608010c]) (lf 0x43d481000db3 [0x210020f040b])))) (nd (nd (lf 0x143d481000db3 [0x210020f040b,0x180603000c]) (lf 0x243d481000db3 [0x210040b0006,0xc])) (nd (lf 0x32d481000db3 [0x104]) (nd (lf 0x132d481000d73 [0x104]) (lf 0x132d481000df3 [0xc0002040b,0x203001d0009,0x21003040208]))))) (nd (nd (nd (lf 0x232d481000db3 [0x104]) (lf 0x332d481000d73 [0x104])) (nd (lf 0x332d481000df3 [0x9000c0002,0x10304]) (nd (lf 0x43d481000df3 [0x27000d0210,0x40b]) (lf 0x143d481000df3 [0x60304000c,0xa00180009,0xb])))) (nd (nd (lf 0x243d481000df3 [0x1d000d0210,0xb02080203,0xc0304]) (lf 0x16210c1000bb3 [0xb06030027])) (nd (lf 0x16210c1000bf3 [0x1d002b0010,0x1f000f0608,0xb00270104,0x21]) (nd (lf 0x14310c1000e73 [0x60b06080010,0x20b0604010c]) (lf 0x35310c1000d73 [0x20b040f001f]))))))
def F13T6_3 := nd (nd (nd (nd (nd (lf 0x16510c10009f3 [0x608000f0010,0x2600110004]) (lf 0x16510c1000bf3 [0x110010020b,0x270608])) (nd (lf 0x6050c1000fe3 [0x6080001010c,0x30018]) (nd (lf 0x36250c1000bf3 [0x60800210028,0xb0003001d,0xc010c]) (lf 0x15350c1000f73 [0x608020b021d,0x9000f010c])))) (nd (nd (lf 0x25350c1000d73 [0x60806030009,0xa0518]) (lf 0x25350c1000f73 [0x10020b021d,0x26000c0006])) (nd (lf 0x6550c1000df3 [0xa00090006,0x410040f0204]) (nd (lf 0x16550c1000bf3 [0x300060608,0x2601040001,0x11]) (lf 0x36550c10009f3 [0xb00010603,0x6000c0004,0x9]))))) (nd (nd (nd (lf 0x36550c1000df3 [0xa00090006,0xb]) (lf 0x36550c1000bf3 [0x106080006,0xc0003])) (nd (lf 0x16290c1000bb3 [0x21060b0010,0x60800280013,0xb040f0118]) (nd (lf 0x16290c1000bf3 [0x1000210028,0xb0608001d,0x1f]) (lf 0x34390c1000e73 [0x608000f0010,0x604])))) (nd (nd (lf 0x15390c1000d73 [0x6080010001f,0x518000a]) (lf 0x15390c1000f73 [0x11020b021d,0x900060608,0x26])) (nd (lf 0x5490c1000cf3 [0x28020b0410,0xc000d]) (nd (lf 0x16490c1000bf3 [0x1d00100006,0x10608010c,0xa0018000b]) (lf 0x16590c10009f3 [0x606080010,0xb000c0004,0x11])))))) (nd (nd (nd (nd (lf 0x16590c1000bf3 [0x2d06080011,0x90003]) (lf 0x16214c10009b3 [0x60306080009,0x18])) (nd (lf 0x16214c10009f3 [0x60300090304,0x18000a0608,0x1b0002]) (nd (lf 0x16414c10008f3 [0x60306080021,0x9]) (lf 0x26414c10008f3 [0x9000a0608,0x603])))) (nd (nd (lf 0x36254c10009b3 [0x6030608001f,0x18]) (lf 0x6454c10008f3 [0x6030608001f,0xc000a])) (nd (lf 0x36454c10008f3 [0x60306080021,0xc]) (nd (lf 0x36254c1000bb3 [0x603040b0011,0x118]) (lf 0x36254c1000bf3 [0x6080028041d,0x3001f040b,0x9]))))) (nd (nd (nd (lf 0x15454c1000df3 [0x10000b001d,0x608000e000c,0xf03040504,0x18]) (lf 0x25454c1000df3 [0xc001d0027,0x504000b0010,0xa])) (nd (lf 0x6454c1000af3 [0x608040b0011,0x280704]) (nd (lf 0x36454c1000af3 [0x70406080011,0x28]) (lf 0x36454c1000bf3 [0x6080118041d,0x10040b0603])))) (nd (nd (lf 0x16294c10009b3 [0x60806030027,0x180009]) (lf 0x16294c10009f3 [0x60300090304,0x18000a0608,0x27])) (nd (lf 0x16294c1000bb3 [0x608041d0027]) (nd (lf 0x16294c1000bf3 [0x40b0010041d,0xc00280608]) (lf 0x25494c1000df3 [0xa00090027]))))))
def F13T6_4 := nd (nd (nd (nd (nd (lf 0x16494c1000bf3 [0x6080118041d,0x3040b]) (lf 0x1530c42000d33 [0x508000c0010,0x40f0021])) (nd (lf 0x1540c42000cb3 [0x41905080410,0x340218]) (lf 0x1540c42000db3 [0x50802180410,0xf000c000b]))) (nd (nd (lf 0x1650c420009b3 [0x3405080010,0x18]) (lf 0x1548c42000cb3 [0x5080034001f,0x2180603])) (nd (lf 0x1548c42000db3 [0x508001f0034,0xf0218]) (nd (lf 0x439442000db3 [0x210210040b,0x1f0024]) (lf 0x1439442000db3 [0x603040b0021,0x1d001f]))))) (nd (nd (nd (lf 0x2439442000db3 [0x21040b0210,0x24]) (lf 0x14310c2000e33 [0x21d00100021,0xc0219])) (nd (lf 0x15310c2000d33 [0x708000c040f,0x20b04190007]) (nd (lf 0x16510c20009b3 [0xf00340010,0x70004000b]) (lf 0x15390c2000d33 [0x21000c0010,0x4190708])))) (nd (nd (lf 0x16590c20009b3 [0x700100021,0x4000b]) (lf 0x6154c2000d33 [0x16000c0219,0x21020f0029])) (nd (lf 0x6454c2000d33 [0x708000c020f,0x21900290007]) (nd (lf 0x36454c2000d33 [0x60300070021,0x2190708000c]) (lf 0x438c22000f23 [0x10c00100416])))))) (nd (nd (nd (nd (lf 0x3438c22000f23 [0x403010c0416,0x100118]) (lf 0x1648c22000ba3 [0x1d01180010,0x403010b])) (nd (lf 0x1540c62000db3 [0x50802180410,0xc001d000f]) (nd (lf 0x1640c62000bb3 [0x1001180416]) (lf 0x1650c620009b3 [0x1000230016,0x18])))) (nd (nd (lf 0x1548c62000db3 [0x60305080218,0x410000c]) (lf 0x1648c62000bb3 [0x60305080118,0x23001d010c,0x61d01090604])) (nd (lf 0x439462000db3 [0x20f040b0210,0x18000c0016]) (nd (lf 0x1439462000db3 [0x20f040b0416,0x210]) (lf 0x2439462000db3 [0x18040b0210,0x160001020f]))))) (nd (nd (nd (lf 0x14310e2000e33 [0x10c00100007,0x6040708021d,0x6]) (lf 0x35310e2000d33 [0x10000c0216,0x18])) (nd (lf 0x16510e20009b3 [0xf00100023,0xb]) (nd (lf 0x16490e2000bb3 [0x10010c0006,0x108010b0001]) (lf 0x16590e20009b3 [0x2100100023,0xc000b040f])))) (nd (nd (lf 0x36454e20008b3 [0x18000c0603]) (lf 0x6454e2000ab3 [0x41000230416])) (nd (lf 0x36454e2000ab3 [0x41000230416]) (nd (lf 0x36454e2000bb3 [0x10c00230416,0x410]) (lf 0x16494e2000bb3 [0x118041d0023,0x108010b0010]))))))
def F13T6_5 := nd (nd (nd (nd (nd (lf 0x3328c22000f23 [0x1f00100416]) (lf 0x1428c22000fa3 [0x416001f0006,0x2040010])) (nd (lf 0x3428c22000ea3 [0xf001f0416,0x21]) (nd (lf 0x3428c22000fa3 [0x1f000f0416,0x10]) (lf 0x438c22000f63 [0x604000f0416])))) (nd (nd (lf 0x2538c22000d63 [0x1d0604001a]) (lf 0x1438862000fb3 [0x2305080007,0x41d04030024,0x40b])) (nd (lf 0x1538862000db3 [0x603020c0007,0xe040f0508]) (nd (lf 0x1420c62000fb3 [0x41d00380410,0x218010b000f,0x230118001c]) (lf 0x3420c62000eb3 [0x20f04100416,0x210023]))))) (nd (nd (nd (lf 0x1620c62000bb3 [0x10a00100416,0x41c001b0118]) (lf 0x1540c62000df3 [0x3402180410,0x404001d000f])) (nd (lf 0x3328c62000f33 [0x416011a001f,0x370603]) (nd (lf 0x3428c62000eb3 [0x603001f0416,0x21020f]) (lf 0x1628c62000bb3 [0x11a001f0416,0x370603])))) (nd (nd (lf 0x1548c62000df3 [0x1a00370419,0x5080034]) (lf 0x1329462000db3 [0x41606030027])) (nd (lf 0x3329462000d33 [0x300603040b,0x1f0418]) (nd (lf 0x3329462000db3 [0x1f040b0210,0x2d04180030,0x20f]) (lf 0x439462000df3 [0x21000270416,0x2f040b])))))) (nd (nd (nd (nd (lf 0x1439462000df3 [0x204040b0416,0x1]) (lf 0x2439462000df3 [0x40b02100416,0x2040203002f])) (nd (lf 0x604ca2000fa3 [0x10c0216002b,0x603]) (nd (lf 0x434ca2000f33 [0x7020f001b,0x608041d0023,0x3080027]) (lf 0x3434ca2000f33 [0x230021010c,0x6080001041d,0x3080419020a,0x10])))) (nd (nd (lf 0x2534ca2000d33 [0x603002b001a,0x20a]) (lf 0x544ca2000db3 [0x902160013,0x20a000c])) (nd (lf 0x1544ca2000db3 [0x7080603000e,0x9020b0419,0xc]) (nd (lf 0x2544ca2000db3 [0x21c06030013,0x4001d]) (lf 0x3544ca2000db3 [0x2160218002a,0xf000c0009]))))) (nd (nd (nd (lf 0x1644ca2000bb3 [0x19010c0006,0x1d06030108,0x10608]) (lf 0x3644ca2000bb3 [0x10c01180039,0x10904090404,0x1d])) (nd (lf 0x260cca2000f23 [0x1f00100216]) (nd (lf 0x261cca2000f33 [0x603001f0011,0x37]) (lf 0x154cca2000d33 [0x3706030218,0x1f020b])))) (nd (nd (lf 0x354cca2000d33 [0x41002180216,0x1f]) (lf 0x164cca2000f33 [0x1000210030])) (nd (lf 0x264cca2000f33 [0x1f06030030,0x23021d]) (nd (lf 0x265cca2000d33 [0x1f00100216,0x218]) (lf 0x143cca2000f33 [0x21d00100021,0x2303080219]))))))
def F13T6_6 := nd (nd (nd (nd (nd (lf 0x343cca2000f33 [0x41d06030030,0x23021d]) (lf 0x153cca2000d33 [0xc00100007,0x218020b0708])) (nd (lf 0x154cca2000db3 [0x1f06030037]) (nd (lf 0x354cca2000db3 [0x21804100216,0xc]) (lf 0x164cca2000bb3 [0x11800100006,0x108010b002d])))) (nd (nd (lf 0x16210e2000bb3 [0x1d0603002b,0x10b06080027,0x108]) (lf 0x14310e2000e73 [0x70800100021,0x21d0007])) (nd (lf 0x35310e2000d73 [0x6040216040f]) (nd (lf 0x36250e2000bb3 [0x10c06030021,0x108010b0004,0x410]) (lf 0x16290e2000bb3 [0x700100021,0x20401080608]))))) (nd (nd (nd (lf 0x34390e2000e73 [0x6080010001f,0x7]) (lf 0x5490e2000cf3 [0x60402160410])) (nd (lf 0x16214e20009b3 [0x330603001a,0x18]) (nd (lf 0x6454e20008f3 [0x6040603001c,0xc]) (lf 0x36454e20008f3 [0x60306040007,0x18000c0708])))) (nd (nd (lf 0x1428c03000fa3 [0x41a040c0410,0x3040403]) (lf 0x1520c43000d33 [0x906030034,0x28040f0508])) (nd (lf 0x1520c43000d73 [0x3406030028,0x40f0009]) (nd (lf 0x1528c43000d33 [0x1a00330419]) (lf 0x1528c43000d73 [0x41903040028,0x20a001a])))))) (nd (nd (nd (nd (lf 0x1521043000db3 [0x18040f0032]) (lf 0x1521043000df3 [0xb001a040f,0x1805040028])) (nd (lf 0x16510430009f3 [0x4000f001a,0x250028]) (nd (lf 0x1529043000db3 [0x18001a0032,0xb]) (lf 0x1529043000df3 [0x1c001a0419,0x18001f0028])))) (nd (nd (lf 0x1629043000bf3 [0x1c041a0028,0x10b000b0021]) (lf 0x1639043000b73 [0x603001a001f,0x118])) (nd (lf 0x1329443000d73 [0x304001a0028,0x20f]) (nd (lf 0x1429443000db3 [0x40b041a002d,0x603]) (lf 0x1429443000cf3 [0x41a0416002f]))))) (nd (nd (nd (lf 0x1429443000df3 [0x1d040b041a,0x2f03040203]) (lf 0x2429443000db3 [0x40b041a002d,0x603])) (nd (lf 0x3429443000cf3 [0x40b041a0028]) (nd (lf 0x3429443000df3 [0x28041a040b,0x20f002d0304]) (lf 0x3439443000d73 [0x1a040b020f,0x28])))) (nd (nd (lf 0x1544c83000db3 [0x603001a040c,0x18]) (lf 0x2544c83000db3 [0x603001a040c,0x20a])) (nd (lf 0x3644c83000bb3 [0x6030118041a,0xc]) (nd (lf 0x3654c830009b3 [0x180023001a]) (lf 0x3424c83000e33 [0x28]))))))
def F13T6_7 := nd (nd (nd (nd (nd (lf 0x3424c83000f33 [0x21020f0028]) (lf 0x544c83000d73 [0x603001a001b,0x208020a0504])) (nd (lf 0x1544c83000f73 [0xf05040028,0x20a0603]) (nd (lf 0x2544c83000d73 [0x603021c001b]) (lf 0x2544c83000f73 [0x90504020f,0x218])))) (nd (nd (lf 0x644c83000f73 [0x2030021020f,0xc021d]) (lf 0x3644c83000f73 [0x218001b0028,0x10404090404,0x10a])) (nd (lf 0x3424c83000eb3 [0x603040c041a,0x20a00210023]) (nd (lf 0x2544c83000df3 [0x9002b020a,0x23000c]) (lf 0x3644c83000bf3 [0x3301180409,0x23000c]))))) (nd (nd (nd (lf 0x2548c83000db3 [0x603001a040c,0x20a]) (lf 0x1648c83000ab3 [0x1180603041a,0xc])) (nd (lf 0x1648c83000bb3 [0x6030118041a,0xc001d]) (nd (lf 0x1658c830009b3 [0x2a0603001a,0xc00310018]) (lf 0x142cc83000e33 [0x6030028])))) (nd (nd (lf 0x142cc83000f33 [0x603041a0022,0xf021d0218]) (lf 0x152cc83000d33 [0x1b0603001a,0x40f0218])) (nd (lf 0x254cc83000d73 [0x6030504001a,0x20a]) (nd (lf 0x605083000fa3 [0x60901180216,0x20c002a0603]) (lf 0x435083000e33 [0x180603021a,0x41d])))))) (nd (nd (nd (nd (lf 0x635083000f33 [0x6030118021a,0xc]) (lf 0x3635083000b33 [0x1180616000c,0x40f])) (nd (lf 0x3635083000f33 [0x11806030037,0x209]) (nd (lf 0x1545083000eb3 [0x6030118021a,0xa001d]) (lf 0x2545083000cb3 [0x220603001c])))) (nd (nd (lf 0x2545083000eb3 [0x1d021a0006,0x18]) (lf 0x655083000db3 [0x6030118021a,0xa0208])) (nd (lf 0x1655083000bb3 [0xc02090006,0x10b002d0708]) (nd (lf 0x36550830009b3 [0x70806030022,0x4000b0031,0xc040f]) (lf 0x3655083000db3 [0x50406030037,0xa]))))) (nd (nd (nd (lf 0x3655083000bb3 [0xc00310006,0x180708]) (lf 0x605083000ee3 [0x18000d0028])) (nd (lf 0x1525083000cb3 [0x21a001e0603,0xa001f]) (nd (lf 0x1525083000eb3 [0x1f021a000d,0x603]) (lf 0x3625083000eb3 [0x21000f002f])))) (nd (nd (lf 0x635083000e73 [0x21a0603000d,0x18]) (lf 0x3635083000e73 [0x28002f])) (nd (lf 0x655083000cf3 [0x603021a000d,0x2080504]) (nd (lf 0x3655083000cf3 [0x504000d0028,0xa]) (lf 0x605083000fe3 [0xd00220018,0xf]))))))
def F13T6_8 := nd (nd (nd (nd (nd (lf 0x1525083000db3 [0x28001f0603,0x209040f0708,0x41900090018,0x31000a020b]) (lf 0x1525083000fb3 [0x1f00310209,0xf0603001d,0x118])) (nd (lf 0x435083000e73 [0x21a0603000d,0x18041d]) (lf 0x3435083000e73 [0x280603001f,0x10a0018]))) (nd (nd (lf 0x635083000f73 [0x1f00180209,0xd05040603]) (lf 0x3635083000b73 [0x603000c0504,0x18040f0032,0x61d010b0708,0xf])) (nd (lf 0x3635083000f73 [0x6000f0018,0x40f000d0603,0x209]) (nd (lf 0x1545083000ef3 [0x1d05040209,0xa001f000d]) (lf 0x2545083000cf3 [0x5040603001c,0x20c002b0209]))))) (nd (nd (nd (lf 0x2545083000ef3 [0xf05040209,0x18001d]) (lf 0x655083000df3 [0x208000a0504,0xd0209])) (nd (lf 0x1655083000bf3 [0x220019000d,0x1080031000c]) (nd (lf 0x36550830009f3 [0x70806030504,0xb00280032,0xd040f0022,0xc000a]) (lf 0x3655083000df3 [0x22000a0504,0x209040f000d])))) (nd (nd (lf 0x3655083000bf3 [0x31000c0209,0x18000d0003]) (lf 0x1639083000b33 [0x40f000c0616,0x2307080118])) (nd (lf 0x1649083000bb3 [0x118000f0006,0x708001d000c,0x10b002d]) (nd (lf 0x16590830009b3 [0x40f00220603,0xb00180031]) (lf 0x1659083000bb3 [0x60300310006,0x1f])))))) (nd (nd (nd (nd (lf 0x152d083000cb3 [0x1f06030028,0x21020b0209]) (lf 0x152d083000eb3 [0x21a0603000d,0x104])) (nd (lf 0x152d083000db3 [0x18040f0033,0x41907080028,0x20b]) (nd (lf 0x154d083000ef3 [0x10a00090033,0xd0118]) (lf 0x165d083000bf3 [0xd0031000f])))) (nd (nd (lf 0x615483000db3 [0x219001a0032,0x20f002d0029]) (lf 0x2615483000db3 [0x1a02190033])) (nd (lf 0x435483000d33 [0x603001a020f,0x18]) (nd (lf 0x1435483000db3 [0x18001a0031]) (lf 0x3435483000d33 [0x40b0032020f,0x219]))))) (nd (nd (nd (lf 0x3435483000db3 [0x603001a0031,0x1040018]) (lf 0x3635483000db3 [0x104])) (nd (lf 0x645483000db3 [0x3406030033,0x1d03080032,0x180009]) (nd (lf 0x1645483000db3 [0x60307080033,0x2d0028001d,0x2103080219]) (lf 0x2645483000db3 [0x18020f0032])))) (nd (nd (lf 0x3645483000db3 [0x70800320033,0x90021002d]) (lf 0x3435483000f33 [0x20f001a0031])) (nd (lf 0x1545483000db3 [0x18001a0031]) (nd (lf 0x2545483000db3 [0x20f001a0031,0x1040018]) (lf 0x3645483000bb3 [0x6030118041a,0x104]))))))
def F13T6_9 := nd (nd (nd (nd (nd (lf 0x3655483000db3 [0x104]) (lf 0x215483000db3 [0x104])) (nd (lf 0x2215483000df3 [0x104]) (nd (lf 0x615483000df3 [0x219001e001a]) (lf 0x2615483000df3 [0xb001a0002])))) (nd (nd (lf 0x3325483000d73 [0x104]) (lf 0x425483000db3 [0x104])) (nd (lf 0x1425483000cf3 [0x104]) (nd (lf 0x1425483000df3 [0x104]) (lf 0x2425483000db3 [0x104]))))) (nd (nd (nd (lf 0x3425483000cf3 [0x104]) (lf 0x3425483000df3 [0x20018020f,0x304])) (nd (lf 0x435483000d73 [0x603001a020f,0x18000d0504]) (nd (lf 0x3435483000d73 [0x504020f001b,0x219040b]) (lf 0x645483000df3 [0x1d0304020f,0x9001b0308,0x18])))) (nd (nd (lf 0x1645483000df3 [0x1f02030002,0xd04090308,0xa0018]) (lf 0x2645483000df3 [0x18020f0002])) (nd (lf 0x3645483000df3 [0x4090033001b,0xa00180304]) (nd (lf 0x2425483000fb3 [0x104]) (lf 0x3435483000f73 [0x20f0028001f,0x9])))))) (nd (nd (nd (nd (lf 0x1545483000df3 [0x3300090504,0x18001f000f]) (lf 0x2545483000df3 [0x90304020f,0x18])) (nd (lf 0x3645483000bf3 [0x3301180409,0x104]) (nd (lf 0x3439483000f33 [0x603001a001f,0x1180021]) (lf 0x2549483000db3 [0x504001a020f])))) (nd (nd (lf 0x1649483000bb3 [0x6030118041a,0xc001d]) (lf 0x16210c3000b73 [0x304000f001a,0x21])) (nd (lf 0x15410c3000c73 [0x603001a0021,0x18]) (nd (lf 0x162d0c3000b33 [0x1f000f0028]) (lf 0x162d0c3000b73 [0xf0028]))))) (nd (nd (nd (lf 0x165d0c3000b73 [0x3a000f001a,0xc0028]) (lf 0x162d0c3000bb3 [0x603001f041a,0x418000c])) (nd (lf 0x165d0c30009f3 [0xf001a001f,0x3a000c]) (nd (lf 0x26115030009d3 [0xa00090603,0xb]) (lf 0x16215030009b3 [0x1d000a001a])))) (nd (nd (lf 0x16215030009f3 [0xa0304001a,0x1d]) (lf 0x3625503000bf3 [0xd03040028,0xa0118])) (nd (lf 0x16295030009b3 [0x220603001c,0x409000c]) (nd (lf 0x16295030009f3 [0x3040603001c,0x2b000c0409]) (lf 0x1629503000bb3 [0x1d041a0006,0x18000c]))))))
def F13T6_10 := nd (nd (nd (nd (nd (lf 0x1629503000bf3 [0x1d000f0409,0x18000c]) (lf 0x162d5030009b3 [0x603001a0021])) (nd (lf 0x1529063000df3 [0x2802100419,0x20c0508001f]) (nd (lf 0x439063000e73 [0x419011c0416,0x280210]) (lf 0x1329463000d73 [0x30404160028,0x20f])))) (nd (nd (lf 0x1429463000db3 [0x4100416002d,0xc040b]) (lf 0x1429463000cf3 [0x41004160036])) (nd (lf 0x1429463000df3 [0x1f04160410,0x36000b]) (nd (lf 0x2429463000db3 [0x160410002d,0xc]) (lf 0x3429463000cf3 [0x2804160036]))))) (nd (nd (nd (lf 0x3429463000df3 [0x41000280416,0x2d001f]) (lf 0x3439463000d73 [0x416001f020f])) (nd (lf 0x3424ca3000e33 [0x28]) (nd (lf 0x3424ca3000f33 [0x21020f0028]) (lf 0x1524ca3000d33 [0x708000c0010,0x20a04190028])))) (nd (nd (lf 0x2544ca3000d73 [0x5040603021c,0xc]) (lf 0x142cca3000e33 [0x6030028])) (nd (lf 0x142cca3000f33 [0x410001f0028,0x603]) (nd (lf 0x4350a3000e33 [0x41900270210,0x1f0018]) (lf 0x6350a3000f33 [0x70802100006,0x20c0118003b])))))) (nd (nd (nd (nd (lf 0x36350a3000f33 [0x603020c0118,0x1002d0708,0x210]) (lf 0x25450a3000cb3 [0x1f001c0210])) (nd (lf 0x6550a3000db3 [0x20c01180216,0xa]) (nd (lf 0x36550a3000db3 [0x70800060210,0x20c003b]) (lf 0x15250a3000cb3 [0x1e001f0210,0x603])))) (nd (nd (lf 0x36250a3000eb3 [0x210001f0028,0x603]) (lf 0x6350a3000e73 [0x210001f0036,0x219003b])) (nd (lf 0x36550a3000cf3 [0x70802100036,0x20b003b001f]) (nd (lf 0x15250a3000db3 [0x210001f0017,0x70800280603,0x419]) (lf 0x4350a3000e73 [0x210001f0036,0x2190419]))))) (nd (nd (nd (lf 0x6350a3000f73 [0x1800060210,0x36020c]) (lf 0x25450a3000cf3 [0x1f001c0210])) (nd (lf 0x36550a3000df3 [0x20c00060210,0x360504]) (nd (lf 0x16490a3000bb3 [0x118000f001f,0x10b002d0708]) (lf 0x16210e3000b73 [0x10000f0028])))) (nd (nd (lf 0x35410e3000c73 [0x1000210216]) (lf 0x162d0e3000b33 [0xf001f])) (nd (lf 0x154d0e3000c73 [0x603000c0021]) (nd (lf 0x36255230009b3 [0xb00100021]) (lf 0x16295230009b3 [0x1c0010]))))))
def F13T6_11 := nd (nd (nd (nd (nd (lf 0x16295230009f3 [0x10001c001f]) (lf 0x1301413200d23 [0x103])) (nd (lf 0x3401413200da3 [0x103]) (nd (lf 0x431413200d33 [0xc05030416,0x18]) (lf 0x3431413200d33 [0x30a000c0416,0x100018])))) (nd (nd (lf 0x3101413200fa3 [0x103]) (lf 0x3401413200fa3 [0x103])) (nd (lf 0x511413200db3 [0x703080032,0x33001d0503,0x6000b]) (nd (lf 0x2611413200bb3 [0x10b01160027]) (lf 0x431413200f33 [0x27000c0010,0x5030708030a,0x600310007,0x10a]))))) (nd (nd (nd (lf 0x541413200db3 [0x27000c0503,0x1d030a0032,0x100708]) (lf 0x3541413200db3 [0x503000c0006,0x508001d0032,0x100308002d,0x18])) (nd (lf 0x1641413200bb3 [0x7080118040c,0x103011d0703,0x10b002d]) (nd (lf 0x2641413200bb3 [0x703040c011c,0x103011d]) (lf 0x15410d3200c33 [0x41a0410000c,0x20b021d])))) (nd (nd (lf 0x35410d3200f33 [0xc01180013,0x11c010f]) (lf 0x26510d3200d33 [0x1a00100021,0xc])) (nd (lf 0x26510d3200b33 [0x708000c0021,0x7030027]) (nd (lf 0x26510d3200f33 [0x1a0010000c,0x21]) (lf 0x26510d32009b3 [0xc001a0010])))))) (nd (nd (nd (nd (lf 0x26390d3200b33 [0x10000c010a,0x1a]) (lf 0x26590d32009b3 [0xc001a0010])) (nd (lf 0x354d0d3200c33 [0x7080018000c,0x703]) (nd (lf 0x2601513200bb3 [0x40c0116010f]) (lf 0x3541513200db3 [0x11c010f0013,0xc])))) (nd (nd (lf 0x6055132009a3 [0x1d0018000c]) (lf 0x260d513200bb3 [0x40c01160013,0x9])) (nd (lf 0x3101413200f63 [0x103]) (nd (lf 0x1201413200f23 [0x103]) (lf 0x3401413200f63 [0x103]))))) (nd (nd (nd (lf 0x1501413200d63 [0x103]) (lf 0x511413200d73 [0x30805030028,0x3c00300604])) (nd (lf 0x2511413200d73 [0x5030308003c,0x14]) (nd (lf 0x2611413200b73 [0x140116003c]) (lf 0x3421413200e33 [0x28])))) (nd (nd (lf 0x3421413200f33 [0x2600140028,0x21010a0503,0x204]) (lf 0x3521413200d33 [0x50300070010,0x1400210708,0x26000c])) (nd (lf 0x3521413200f33 [0x503003c0028,0xc]) (nd (lf 0x1621413200f33 [0x3030116003c]) (lf 0x541413200d73 [0x3c05030026,0x21]))))))
def F13T6_12 := nd (nd (nd (nd (nd (lf 0x2541413200d73 [0x503003c0028]) (lf 0x2641413200b73 [0x703011c001b,0x11d])) (nd (lf 0x3509413200d63 [0x103]) (nd (lf 0x2619413200b73 [0x1e01160030]) (lf 0x3429413200e33 [0x503001e])))) (nd (nd (lf 0x3429413200f33 [0x130503001e,0x10a00210026]) (lf 0x549413200d73 [0xc06040026])) (nd (lf 0x2649413200b73 [0x604000c011c,0x11d0703]) (nd (lf 0x60d093200e33 [0x11c010f0002]) (lf 0x260d093200e33 [0x210014]))))) (nd (nd (nd (lf 0x65d093200e33 [0x1f011c010f,0x21]) (lf 0x165d093200e33 [0x303001e0014,0x308])) (nd (lf 0x265d093200e33 [0x210014]) (nd (lf 0x365d093200e33 [0x20c011c010f]) (lf 0x54d093200e33 [0x21011c010f])))) (nd (nd (lf 0x354d093200e33 [0x70800210028,0x10a0703]) (lf 0x65d093200b33 [0x1a0010010a,0x21001f])) (nd (lf 0x265d093200b33 [0x30800210028,0x90703]) (nd (lf 0x54d493200f33 [0x1f0030003c,0x4040021]) (lf 0x154d493200d33 [0x1f00280021])))))) (nd (nd (nd (nd (lf 0x354d493200d33 [0x1f04100021,0x4040708]) (lf 0x354d493200f33 [0x1f0030003c,0x9])) (nd (lf 0x264d493200b33 [0x11c001f010f,0x404]) (nd (lf 0x2601513200b73 [0x10f0028]) (lf 0x1541513200c73 [0x604000c0028,0x7030708])))) (nd (nd (lf 0x605513200b63 [0x116000c0021]) (lf 0x605513200b73 [0x2101160014,0x303])) (nd (lf 0x3625513200b33 [0xc00280021,0x407030708]) (nd (lf 0x2609513200b73 [0x6040116010f,0xc]) (lf 0x1629513200b33 [0x7080028001f,0x21010a0703]))))) (nd (nd (nd (lf 0x3549513200c73 [0xc00280021,0x7030708]) (lf 0x2649513200b73 [0x11c0021010f,0xc])) (nd (lf 0x260d513200b73 [0x1000210028]) (nd (lf 0x1301413200d63 [0x103]) (lf 0x3401413200de3 [0x103])))) (nd (nd (lf 0x1421413200db3 [0x50304160006,0x18000c0410,0xa0010]) (lf 0x3421413200cb3 [0x14040c0416,0x2104100204])) (nd (lf 0x3421413200db3 [0x40c00210026,0x410041d]) (nd (lf 0x431413200d73 [0x60405030026,0x18041d]) (lf 0x3431413200d73 [0xc06040026]))))))
def F13T6_13 := nd (nd (nd (nd (nd (lf 0x3101413200fe3 [0x103]) (lf 0x1201413200fa3 [0x103])) (nd (lf 0x3401413200fe3 [0x2b00140010,0xc]) (nd (lf 0x511413200df3 [0x30805030005,0x1d000c0028,0xb]) (lf 0x2611413200bf3 [0x14010b0116,0x4100604])))) (nd (nd (lf 0x3421413200eb3 [0x14040c0028]) (lf 0x2431413200f73 [0x11d00360503,0x20400140010])) (nd (lf 0x541413200df3 [0xc002b0503,0x3c001d0033,0xa0021]) (nd (lf 0x3541413200df3 [0x3c00060503,0x18001d0033]) (lf 0x2641413200bf3 [0x103002b010a,0x36001b000c]))))) (nd (nd (nd (lf 0x354cc93200db3 [0x41a0410001f]) (lf 0x435093200e33 [0x2100360027,0xc0708001f])) (nd (lf 0x435093200f33 [0x11c0021010f,0x1f]) (nd (lf 0x2435093200eb3 [0x21a020c0210]) (lf 0x635093200b33 [0x21001a0010,0x404001f])))) (nd (nd (lf 0x635093200f33 [0x1180027002b,0x20c]) (lf 0x3635093200f33 [0x703020c0118,0x2a00060708,0x90001002d])) (nd (lf 0x6550932009b3 [0x1a000a0010]) (nd (lf 0x655093200db3 [0x1c000f0021,0x1f0404]) (lf 0x60d093200eb3 [0x11c010f000d,0x21d020c])))))) (nd (nd (nd (nd (lf 0x260d093200eb3 [0x1400210028]) (lf 0x63d093200eb3 [0x21a001f0210,0x21])) (nd (lf 0x163d093200e33 [0x708020c0028,0x210703]) (nd (lf 0x263d093200e33 [0x70800210028,0x703]) (lf 0x263d093200eb3 [0x21a020c0210,0x10a])))) (nd (nd (lf 0x265d093200cb3 [0x1f00280021,0x20b021d0209,0x404]) (lf 0x265d093200eb3 [0x1e00210014,0x1f])) (nd (lf 0x260d093200bb3 [0x1160021010f,0x303]) (nd (lf 0x43d093200e33 [0xc011c010f,0x21]) (lf 0x43d093200eb3 [0x21a020c0210,0x21]))))) (nd (nd (nd (lf 0x143d093200e33 [0x7080021020c,0x280703]) (lf 0x243d093200e33 [0x70800360021,0x2f07030028])) (nd (lf 0x243d093200eb3 [0x21a020c0210,0x21010a]) (nd (lf 0x343d093200e33 [0x11c020c010f,0x404]) (lf 0x54d093200eb3 [0x11c020c010f,0x21])))) (nd (nd (lf 0x354d093200cb3 [0x2e00330021,0x20b021d020c,0x404]) (lf 0x354d093200eb3 [0x2e00210033,0x10a020c])) (nd (lf 0x265d0932009b3 [0x1a00180010,0x404]) (nd (lf 0x265d093200bb3 [0x1a0010001f,0x21]) (lf 0x26010d3200b73 [0x100116010f,0x604]))))))
def F13T6_14 := nd (nd (nd (nd (nd (lf 0x16210d3200f33 [0x1a0010010a,0xd0021]) (lf 0x15410d3200c73 [0x410000c0604,0x20b021d041a])) (nd (lf 0x6050d3200b73 [0xf00210028]) (nd (lf 0x5450d3200c73 [0xc0604000f,0x1c]) (lf 0x26090d3200b73 [0x1000210028])))) (nd (nd (lf 0x25490d3200c73 [0xf0021]) (lf 0x26590d3200b73 [0x703000c0021,0x11d00090708,0x10b])) (nd (lf 0x26390d3200b73 [0x1a06040010,0xc010a]) (nd (lf 0x26590d32009f3 [0x1a00100021,0xc]) (lf 0x260d0d3200b73 [0x6040116010f,0xc]))))) (nd (nd (nd (lf 0x354d0d3200c73 [0x18000c0604,0x7030708]) (lf 0x2601513200bf3 [0x604011d010f,0x28])) (nd (lf 0x6055132009e3 [0xc06040016,0x18]) (nd (lf 0x260d513200bf3 [0x6040010011d,0x170013001b,0xc]) (lf 0x1409423200da3 [0x103])))) (nd (nd (lf 0x15410e3200cb3 [0xc041a0410]) (lf 0x605523200cb3 [0x70800180036,0x2090303040c,0x11031d])) (nd (lf 0x1501433200d63 [0x103]) (nd (lf 0x2541433200d73 [0x1a0503001b]) (lf 0x2641433200b73 [0x11d0604001a,0x103010a])))))) (nd (nd (nd (nd (lf 0x3509433200d63 [0x103]) (lf 0x1621533200b33 [0x2001a0010,0x21010a0004])) (nd (lf 0x1541533200c73 [0x1a00100021]) (nd (lf 0x605533200b73 [0x210028]) (lf 0x2609533200b73 [0x11d010f0028])))) (nd (nd (lf 0x3549533200c73 [0x10001f]) (lf 0x162d533200b33 [0x1a00100021])) (nd (lf 0x3309433200d63 [0x103]) (nd (lf 0x15410f3200c73 [0x60400180010,0x1a]) (lf 0x6050f3200b73 [0x1006040028,0x40a]))))) (nd (nd (nd (lf 0x5450f3200c73 [0x1a00100021]) (lf 0x25490f3200c73 [0xa06040010])) (nd (lf 0x260d0f3200b73 [0x11d010f0028]) (nd (lf 0x605484300db3 [0x27000f0010,0x1400050708,0x1d]) (lf 0x2605484300db3 [0x1d00100027])))) (nd (nd (lf 0x1435484300db3 [0x1a0010000e,0x20c]) (lf 0x3635484300db3 [0x104])) (nd (lf 0x1435484300e33 [0x21001a0010,0xc000e]) (nd (lf 0x3655484300db3 [0x104]) (lf 0x205484300db3 [0x104]))))))
def F13T6_15 := nd (nd (nd (nd (nd (lf 0x2205484300df3 [0x104]) (lf 0x605484300df3 [0x2b00140010,0x1d])) (nd (lf 0x2605484300df3 [0x1d00100002]) (nd (lf 0x1325484300d73 [0x104]) (lf 0x3325484300d73 [0x104])))) (nd (nd (lf 0x1435484300c73 [0x70307080021,0x90028]) (lf 0x1435484300e73 [0x1a00100021,0xd])) (nd (lf 0x1439484300e33 [0x1a00100021,0xc]) (nd (lf 0x6050c4300a73 [0x2800100116]) (lf 0x6050c4300e73 [0x70800100021,0x3a0007000c]))))) (nd (nd (nd (lf 0x36250c4300a73 [0x41a04100021,0xc010b011d]) (lf 0x36550c4300873 [0x70407030708])) (nd (lf 0x36550c4300c73 [0x70307080021,0x9000c]) (nd (lf 0x36550c4300a73 [0x704001a0010,0xc]) (lf 0x36550c4300e73 [0x1a00100021,0x13000c])))) (nd (nd (lf 0x36550c4300973 [0x1c000f0021,0x18]) (lf 0x36550c43009f3 [0x1a00100021,0x130018000c])) (nd (lf 0x16290c4300b33 [0x1a00100021,0x18]) (nd (lf 0x25490c4300c73 [0x10000c0021]) (lf 0x16490c4300a73 [0x1a00100021,0xc])))))) (nd (nd (nd (nd (lf 0x16214143009b3 [0x40f00210016,0x410040c]) (lf 0x16214143009f3 [0x40c00160021,0x410])) (nd (lf 0x3101414300fe3 [0x3040010040c]) (nd (lf 0x511414300df3 [0x30303080021,0x3d000b001d,0x70039]) (lf 0x2611414300bf3 [0x40c0016010b,0x410040f])))) (nd (nd (lf 0x1621414300bb3 [0x40f040c003d,0x410]) (lf 0x16290d4300ab3 [0x1a00100021])) (nd (lf 0x26054a4300db3 [0x100021002e]) (nd (lf 0x34354a4300c33 [0x21021c020f]) (lf 0x34354a4300d33 [0x180021020f,0x40b]))))) (nd (nd (nd (lf 0x34354a4300cb3 [0x1a0010020c]) (lf 0x34354a4300db3 [0x1a00100021,0x20c])) (nd (lf 0x26354a4300d33 [0x1a00100021]) (nd (lf 0x16454a4300cb3 [0x210028020c]) (lf 0x34354a4300e33 [0x1a00100021])))) (nd (nd (lf 0x34354a4300c73 [0x7080021001f,0x703]) (lf 0x34394a4300e33 [0x10001f])) (nd (lf 0x165d0e4300c73 [0x1c000f001f,0x9]) (nd (lf 0x165d0e4300e73 [0x1a00100021,0x13001f]) (lf 0x16294e43009f3 [0x1a00100021,0xa]))))))
def F13T6 : BTree NodeData := nd (nd (nd (nd F13T6_0 F13T6_1) (nd F13T6_2 F13T6_3)) (nd (nd F13T6_4 F13T6_5) (nd F13T6_6 F13T6_7))) (nd (nd (nd F13T6_8 F13T6_9) (nd F13T6_10 F13T6_11)) (nd (nd F13T6_12 F13T6_13) (nd F13T6_14 F13T6_15)))
def F13M6 : BST := BN 316325630 19584 (BN 277406479 55040 (BN 247225037 52352 (BN 212206451 43904 (BN 199162541 7554 (BN 185906259 61056 (BN 165855609 48000 (BN 161419611 56192 (BN 161195179 39041 (BL 132806913 25729) BE) (BL 165631177 62593)) (BN 172838059 27008 (BL 170689139 46976) (BL 176680710 49154))) (BN 194726543 28290 (BN 189544617 14082 (BN 187579377 28544 (BL 186600534 53120) BE) (BL 190342257 40320)) (BN 196070480 26496 (BL 195943927 21504) (BL 197359561 28288)))) (BN 205227783 6273 (BN 202761910 61824 (BN 200506478 6016 (BN 200318606 49152 (BL 199876667 46720) BE) (BL 201795559 7552)) (BN 203307050 45440 (BL 202947952 12160) (BL 203696418 24960))) (BN 208889148 55042 (BN 207770453 11136 (BN 205412237 53121 (BL 205274422 59521) BE) (BL 208148261 42113)) (BN 210491572 59778 (BL 209663781 29825) (BL 210922517 15744))))) (BN 230593160 16256 (BN 224993126 23936 (BN 219052177 46209 (BN 213124590 59776 (BN 212612153 63104 (BL 212419104 41856) BE) (BL 214616791 25472)) (BN 220187037 12416 (BL 219692672 15104) (BL 220557128 7808))) (BN 228041414 31104 (BN 227447075 17280 (BN 225826495 37888 (BL 225677474 3840) BE) (BL 227916185 28032)) (BN 229125662 44802 (BL 228128875 44928) (BL 229698279 43008)))) (BN 239044623 21120 (BN 236084608 10112 (BN 232706764 65152 (BN 232197066 31105 (BL 231170691 15616) BE) (BL 233391273 51200)) (BN 238066769 28545 (BL 237254343 16386) (BL 238276479 46977))) (BN 242855269 25216 (BN 241690341 36866 (BN 239917367 60800 (BL 239491863 15105) BE) (BL 242732913 37248)) (BN 243480621 64128 (BL 242944156 61185) (BL 245025686 22912)))))) (BN 261614065 1408 (BN 255562120 30464 (BN 251659306 56064 (BN 248863936 29568 (BN 248276780 18560 (BN 248027653 2304 (BL 247546007 63360) BE) (BL 248741810 39296)) (BN 250000929 47744 (BL 248901534 18433) (BL 250912656 52480))) (BN 253782630 15232 (BN 253036680 16512 (BN 253033219 63232 (BL 252463651 6400) BE) (BL 253484114 28672)) (BN 254064086 58240 (BL 253794411 53376) (BL 254368229 13568)))) (BN 258245571 30849 (BN 257395336 29312 (BN 257135728 12417 (BN 256229531 61440 (BL 255601256 38656) BE) (BL 257156358 50177)) (BN 258061948 14080 (BL 258005938 3968) (BL 258218628 31616))) (BN 260892239 16384 (BN 260455682 22144 (BN 259215415 12034 (BL 259125863 42496) BE) (BL 260820946 58752)) (BN 261037020 62464 (BL 260904542 54400) (BL 261592356 59905))))) (BN 268750717 50048 (BN 267326657 64001 (BN 263779599 7040 (BN 263052158 30592 (BN 263028557 12928 (BL 262681569 64641) BE) (BL 263396772 1024)) (BN 265328237 36864 (BL 264853484 5760) (BL 265738072 47232))) (BN 268003703 64896 (BN 267725319 65024 (BN 267622459 49024 (BL 267464555 18048) BE) (BL 267832770 10752)) (BN 268501826 12290 (BL 268328892 1280) (BL 268655315 6530)))) (BN 272800795 27648 (BN 270883593 17792 (BN 270621650 56704 (BN 270174070 31872 (BL 270086744 28033) BE) (BL 270735477 14208)) (BN 272123421 14720 (BL 270924940 3072) (BL 272425353 57984))) (BN 275135129 8320 (BN 273271357 63488 (BL 272967407 20736) (BL 274113509 47104)) (BN 275748250 41216 (BL 275505891 18432) (BL 277044858 15745))))))) (BN 294601845 54146 (BN 285593488 128 (BN 281093901 8064 (BN 278957451 16128 (BN 278197253 51201 (BN 277737577 62080 (BN 277707355 51712 (BL 277616345 40192) BE) (BL 277960158 4352)) (BN 278460883 8066 (BL 278362270 57088) (BL 278549507 29184))) (BN 279137841 23040 (BN 279046252 49408 (BN 278974764 14336 (BL 278963553 65408) BE) (BL 279103679 2688)) (BN 279804820 61312 (BL 279472636 9728) (BL 280163918 46464)))) (BN 282763065 41088 (BN 282189464 16896 (BN 282052343 23808 (BN 281959337 55297 (BL 281573077 22784) BE) (BL 282173575 26240)) (BN 282449672 36736 (BL 282435450 60288) (BL 282650430 31360))) (BN 283514805 19328 (BN 283393449 65280 (BN 283275912 60672 (BL 282798268 32512) BE) (BL 283410762 45568)) (BN 284384448 17152 (BL 284184912 39040) (BL 284757470 8194))))) (BN 290858086 25728 (BN 289040345 768 (BN 288433499 59264 (BN 287199063 57472 (BN 287183208 50432 (BL 285832920 51586) BE) (BL 287873913 1792)) (BN 288555097 17408 (BL 288465938 51584) (BL 288620910 62592))) (BN 289628595 62720 (BN 289292200 26112 (BN 289283410 8323 (BL 289193468 45058) BE) (BL 289472854 52224)) (BN 290206235 45952 (BL 290062757 20608) (BL 290243634 2944)))) (BN 292869497 38784 (BN 292064049 512 (BN 291307575 31488 (BN 291008481 49920 (BL 291005586 55680) BE) (BL 291726724 17153)) (BN 292303562 42368 (BL 292139722 12288) (BL 292581751 32001))) (BN 293828885 52994 (BN 293450259 50176 (BN 292991095 43520 (BL 292933364 4224) BE) (BL 293695233 16640)) (BN 294317470 6144 (BL 293946229 18817) (BL 294498755 28800)))))) (BN 304818926 11392 (BN 297959153 52096 (BN 295691616 6272 (BN 295432250 38272 (BN 295143165 28416 (BN 295098281 24448 (BL 294651582 37376) BE) (BL 295360447 19712)) (BN 295481039 41984 (BL 295444479 8960) (BL 295549398 5248))) (BN 297139257 58880 (BN 296499940 38017 (BN 295743573 26368 (BL 295697461 20224) BE) (BL 296957334 38144)) (BN 297642993 44800 (BL 297341761 24320) (BL 297886257 59904)))) (BN 302629983 2176 (BN 300214585 63489 (BN 298923031 27392 (BN 298876830 9088 (BL 298319295 38912) BE) (BL 300127614 29824)) (BN 301657093 40576 (BL 300738463 3200) (BL 301918276 18435))) (BN 304208145 2 (BN 302992162 24578 (BN 302755293 41472 (BL 302683363 44032) BE) (BL 303972994 29056)) (BN 304650583 51713 (BL 304637247 38019) (BL 304775160 55296))))) (BN 308837750 61184 (BN 306804687 46592 (BN 306093091 48512 (BN 305584279 22528 (BN 305407056 23426 (BL 305255274 13186) BE) (BL 305635836 20993)) (BN 306486435 61568 (BL 306465382 25856) (BL 306763678 17920))) (BN 308060634 36738 (BN 307575183 30466 (BN 307570341 56705 (BL 307056102 58496) BE) (BL 307867636 40448)) (BN 308644143 4098 (BL 308395366 8192) (BL 308784041 19968)))) (BN 310783739 49664 (BN 309873937 64000 (BN 309742381 10240 (BN 309652225 23424 (BL 309646446 5888) BE) (BL 309802732 3328)) (BN 310605475 64384 (BL 310020277 25088) (BL 310769697 53888))) (BN 311833783 52481 (BN 311316503 21376 (BL 310975192 57600) (BL 311731429 51328)) (BN 312831364 45056 (BL 312479864 7680) (BL 316167768 6528)))))))) (BN 362346216 52992 (BN 342532970 22529 (BN 328395952 9856 (BN 322547016 53250 (BN 320740018 26752 (BN 318457137 24449 (BN 318188458 36992 (BN 317709937 30848 (BL 317146382 15872) BE) (BL 318254746 55424)) (BN 319871018 18816 (BL 318555809 56576) (BL 320279204 57216))) (BN 321810315 48384 (BN 321770509 32256 (BN 321467905 14592 (BL 320810106 7936) BE) (BL 321772616 13312)) (BN 322367302 40960 (BL 322145935 64640) (BL 322472366 38528)))) (BN 325577653 11520 (BN 324047183 18176 (BN 322906762 13824 (BN 322690744 15488 (BL 322629057 30465) BE) (BL 322991807 64768)) (BN 324857104 62336 (BL 324681950 30336) (BL 325398488 7042))) (BN 327281505 44672 (BN 326621919 29441 (BN 326281046 22273 (BL 326025171 37120) BE) (BL 326630058 24576)) (BN 327732746 12032 (BL 327408487 39808) (BL 327846041 0))))) (BN 333031304 32000 (BN 331213995 51203 (BN 329983753 57728 (BN 328929151 50944 (BN 328840150 43392 (BL 328447627 42880) BE) (BL 329444414 64258)) (BN 330257390 55808 (BL 330105771 56832) (BL 330645008 11008))) (BN 331667278 41600 (BN 331518184 53760 (BN 331436062 19456 (BL 331242543 24704) BE) (BL 331600273 37377)) (BN 332282039 4096 (BL 331717503 21888) (BL 332664390 46208)))) (BN 339810436 2048 (BN 337804885 32641 (BN 336624626 40834 (BN 335690931 31232 (BL 335610464 48128) BE) (BL 337698338 59520)) (BN 338084814 50688 (BL 337893888 27136) (BL 339133527 24064))) (BN 341128843 6912 (BN 340506920 22275 (BN 339996474 29696 (BL 339813552 44801) BE) (BL 340576080 22657)) (BN 341684217 54656 (BL 341226955 1920) (BL 342276339 4864)))))) (BN 351561449 17024 (BN 347566173 21506 (BN 345712366 12544 (BN 344637235 14464 (BN 343655927 9344 (BN 343345810 9216 (BL 343091278 1152) BE) (BL 343996663 10626)) (BN 345256344 22400 (BL 344778302 18177) (BL 345366873 640))) (BN 346968968 25089 (BN 346184912 53248 (BN 346121718 32640 (BL 345816118 42240) BE) (BL 346832372 8832)) (BN 347156228 28418 (BL 347068358 48640) (BL 347244516 6145)))) (BN 349099232 25600 (BN 348645562 58624 (BN 348211478 54144 (BN 347781808 6656 (BL 347732430 13313) BE) (BL 348260907 31744)) (BN 348814911 19072 (BL 348713387 22659) (BL 349073233 48256))) (BN 350003461 45312 (BN 349475724 37250 (BN 349441496 21760 (BL 349255481 28928) BE) (BL 349769604 50304)) (BN 351339418 51585 (BL 351307257 20992) (BL 351545867 37632))))) (BN 356864715 11009 (BN 353877494 54528 (BN 352925455 13440 (BN 352304304 40704 (BN 352213990 55936 (BL 352059365 29440) BE) (BL 352433035 17536)) (BN 353535230 39424 (BL 353250909 59008) (BL 353658811 13952))) (BN 354945511 1536 (BN 354780341 23296 (BN 354778339 54272 (BL 354743277 1793) BE) (BL 354813438 24832)) (BN 356022629 46848 (BL 355291516 7296) (BL 356737758 26624)))) (BN 360726368 56577 (BN 358054450 28417 (BN 357523404 12800 (BN 357340787 43136 (BL 357174224 61696) BE) (BL 357613845 51968)) (BN 360082070 2434 (BL 359032453 5632) (BL 360472633 37760))) (BN 361610222 59648 (BN 361435721 3329 (BL 360830977 49792) (BL 361515278 22274)) (BN 361843469 11264 (BL 361750310 9089) (BL 362190555 4608))))))) (BN 390036097 47105 (BN 374987845 64512 (BN 367563757 58754 (BN 364382426 47616 (BN 363185236 30976 (BN 362715088 2432 (BN 362647092 46336 (BL 362449763 57217) BE) (BL 362871914 47872)) (BN 363603536 21248 (BL 363583015 256) (BL 363711683 5504))) (BN 366746346 23680 (BN 366149068 30208 (BN 365162366 64769 (BL 364879723 59136) BE) (BL 366282835 15360)) (BN 367307912 9984 (BL 367257106 1664) (BL 367423525 2816)))) (BN 371054143 26753 (BN 368944040 8448 (BN 368474706 11776 (BN 368416079 28675 (BL 367692613 63744) BE) (BL 368825869 39680)) (BN 370359555 11904 (BL 369467474 41728) (BL 370406194 52864))) (BN 374210085 12672 (BN 372233502 62208 (BN 371610734 45824 (BL 371400061 18688) BE) (BL 373996125 62976)) (BN 374803711 60544 (BL 374410195 59392) (BL 374827216 1282))))) (BN 383698999 43394 (BN 379551087 46080 (BN 377780293 20482 (BN 375877824 55168 (BN 375836059 47360 (BL 375513095 55552) BE) (BL 377403775 61952)) (BN 378869369 57856 (BL 377822832 9472) (BL 379179077 44160))) (BN 381399975 50816 (BN 380682946 13184 (BN 380546868 58755 (BL 380072053 51074) BE) (BL 380829862 62848)) (BN 382413952 42752 (BL 381609858 44288) (BL 382590865 8704)))) (BN 385977777 38016 (BN 385173931 45696 (BN 384317222 51072 (BN 384137079 40832 (BL 383883998 56449) BE) (BL 384768779 22272)) (BN 385617443 60417 (BL 385340200 10368) (BL 385780242 13825))) (BN 388874832 57857 (BN 387967366 39810 (BN 387844971 58753 (BL 387695030 17664) BE) (BL 388509537 27520)) (BN 389609929 42624 (BL 389590320 46337) (BL 389951348 45184)))))) (BN 420086573 30080 (BN 403231526 15361 (BN 397029518 58241 (BN 394347253 60160 (BN 392021305 56451 (BN 391727030 62465 (BL 391509116 10624) BE) (BL 392996134 40064)) (BN 395314522 57346 (BL 394472095 29185) (BL 395620650 58881))) (BN 400996558 27137 (BN 398912789 22656 (BN 398298968 48896 (BL 397961745 64256) BE) (BL 400107504 7424)) (BN 402073484 18304 (BL 401418189 20480) (BL 402175061 38274)))) (BN 410382811 30720 (BN 407124549 54784 (BN 404890178 62977 (BN 404371134 20352 (BL 403643912 27776) BE) (BL 406296737 49280)) (BN 408808214 13696 (BL 408556844 38400) (BL 410352340 29952))) (BN 414818809 2560 (BN 414424685 3584 (BN 410545018 56448 (BL 410478754 58368) BE) (BL 414749929 54912)) (BN 418952418 57344 (BL 416381536 43776) (BL 419109904 18944))))) (BN 452186344 60416 (BN 434264339 5120 (BN 426900039 45185 (BN 423310559 5376 (BN 422610974 30081 (BL 420214267 21632) BE) (BL 424423041 27650)) (BN 433390280 27904 (BL 430746372 39168) (BL 434084306 42112))) (BN 445906999 26113 (BN 443054801 54785 (BN 442424567 56320 (BL 438700337 14848) BE) (BL 445287432 42753)) (BN 448652064 46593 (BL 448280601 22016) (BL 451109075 39937)))) (BN 474601588 58112 (BN 462988183 44416 (BN 462474311 23553 (BN 461455872 23552 (BL 455176527 30209) BE) (BL 462632363 18306)) (BN 471162435 19840 (BL 465332060 25344) (BL 474363853 11648))) (BN 497745773 23297 (BN 482538105 3456 (BL 481825898 57345) (BL 495845567 39936)) (BN 511154081 22017 (BL 500593149 7169) (BL 526517938 7168))))))))
def F13T7_0 := nd (nd (nd (nd (nd (lf 0x88010007a2 [0x208001d]) (lf 0x88010007e2 [0x2080104001d,0x21001a001f,0x1c])) (nd (lf 0xc010007e2 [0x208001d001a,0x1c0304]) (nd (lf 0x4c810007b2 [0x20802030027,0xb001a000c,0x100104]) (lf 0x4c81000772 [0x10402080028,0xc00210203])))) (nd (nd (lf 0x4c810007f2 [0x20302080104,0x20b001a000c,0xf0021001d,0x27000b0010]) (nd (lf 0x8c810007b2 [0x10402030027,0x10000b001a,0x1d0021010c]) (lf 0xcc81000772 [0x20801040028,0x1f00210010,0x20b0203]))) (nd (lf 0xcc810007f2 [0x20801040010,0x203020b001f,0xf001d0021]) (nd (lf 0x54810005f2 [0x10402030208,0xc0009000b,0x18000a]) (lf 0x54810007f2 [0xb0104001d,0x1002030208,0xf]))))) (nd (nd (nd (lf 0xd4810005b2 [0xc0203000b,0x18]) (nd (lf 0xd4810005f2 [0x1040203000b,0x180009000c,0xa]) (lf 0x10c10007f2 [0x20b000f0010,0x1d02040208,0x2030104]))) (nd (lf 0x50c10007f2 [0x10c02030208,0x1d001c001a,0x10402040118,0x10000c020b,0x18000b000f]) (nd (lf 0x90c10007f2 [0x20b02080010,0x2040118001c,0x2030104001d,0x18000b000f]) (lf 0x14c10005f2 [0x20302080009,0x1800040304,0xa])))) (nd (nd (lf 0x54c10005f2 [0x2030208001f,0xa0004000c,0x18]) (nd (lf 0x54c10007f2 [0x208000b001d,0x1100270203,0xf00100304,0x104]) (lf 0x94c10005f2 [0x20302080009,0x1800040304,0xa]))) (nd (lf 0x94c10007f2 [0x1d000b0010,0x30400270208,0xc000f0104]) (nd (lf 0xd4c10005f2 [0xb001d001f,0xa0018]) (lf 0xc420007b2 [0x10802040010,0xf00210034])))))) (nd (nd (nd (nd (lf 0x8c420007b2 [0x1080034001f,0xc000b0203,0xf0021]) (lf 0x94420005b2 [0xb0016])) (nd (lf 0x10c20007b2 [0xf02040010,0x700340308,0x19]) (nd (lf 0x50c20007b2 [0x1f02030021,0x1d0308000c,0x180019]) (lf 0x90c20007b2 [0x30800100021,0x1900070204,0x18])))) (nd (nd (lf 0x54c2000532 [0xc03080203]) (nd (lf 0x54c20005b2 [0x3080203000c,0x18000b]) (lf 0x8c220007a2 [0x10c00100016,0x3]))) (nd (lf 0xc620007b2 [0x20300100016,0xf0034]) (nd (lf 0x8c620007b2 [0x3400190016,0x100203010c,0xf]) (lf 0x94620005b2 [0xc0203000b,0x18]))))) (nd (nd (nd (lf 0x10e20007b2 [0x216000f0010,0x2040203001d,0x1900070034,0x23]) (nd (lf 0x50e20007b2 [0x10010c0039,0xf001d0203,0x1903080118,0xc02040023]) (lf 0x90e20007b2 [0x11800070010,0x203000f001d,0x1902040308,0x230018]))) (nd (lf 0x54e20005b2 [0x3080203000c,0x18000b]) (nd (lf 0x54e20007b2 [0x10c00230016,0xf02030010]) (lf 0x94e20007b2 [0x20300100016,0xc000f0023])))) (nd (nd (lf 0xd4e20005b2 [0x18000c0016]) (nd (lf 0x8c220007e2 [0x2040016001f,0x21]) (lf 0x88620007b2 [0x10800190016,0x3402030007,0x1c0010001a,0xf]))) (nd (lf 0xc620007f2 [0x20400160010,0x1c00230034,0xf0021]) (nd (lf 0x8c620007f2 [0x190016001f,0x2b00230034,0xf0021001c]) (lf 0x94620005f2 [0xb02040016]))))))
def F13T7_1 := nd (nd (nd (nd (nd (lf 0x4ca20007b2 [0x3080203002b,0x10c00230010,0x4000f0019,0xc0038001d]) (lf 0xcca2000732 [0x21d03080203,0x400100023])) (nd (lf 0xcca20007b2 [0x30800070010,0x203001d0023,0x19021d0004,0xf]) (nd (lf 0x10e20007f2 [0x204000f0010,0x7001d0308,0x1900340023]) (lf 0x50e20007f2 [0x203001f0021,0x1d00230308,0x19])))) (nd (nd (lf 0x90e20007f2 [0x30800100021,0x7001d0023,0x19]) (nd (lf 0x14e20005f2 [0x1d0204001a,0xa0018]) (lf 0x54e20005f2 [0x2030204000c,0xa000b0308,0x18]))) (nd (lf 0x94e20005f2 [0x2030204001a,0xa0018]) (nd (lf 0xd4e20005f2 [0xc02040016,0xa0018]) (lf 0x8c030007e2 [0x3001a001f]))))) (nd (nd (nd (lf 0xc43000772 [0x10800280009,0x1c03040203,0xf]) (nd (lf 0x8c43000772 [0x280019001a,0x1c0304]) (lf 0x10430007f2 [0x28000f001a,0x1040204]))) (nd (lf 0x90430007f2 [0x280019001a,0x204001c0118,0x104000f]) (nd (lf 0x94430005f2 [0xb0203001a,0x304]) (lf 0x4c830007b2 [0x203000c001a])))) (nd (nd (lf 0x4c83000772 [0x20301040028,0x2100190308,0xc0023000f,0x9]) (nd (lf 0x4c830007f2 [0x1040203001a,0x33002b000c,0x23000f0021]) (lf 0x8c830007b2 [0x203000c001a,0x21]))) (nd (lf 0xcc83000772 [0x2030104001a,0xf0021]) (nd (lf 0x50830007b2 [0x1802030037,0x209000f0308,0x104000c0019,0x1d]) (lf 0x50830006f2 [0x10402030028,0x209001f0308,0x18])))))) (nd (nd (nd (nd (lf 0x50830007f2 [0x20902030104,0x1f03080018,0x1d0028000f,0x9002b0019]) (nd (lf 0x90830007b2 [0x21a000f0104,0x2030118001f,0xc00190308]) (lf 0xd0830006f2 [0x20301040028,0xf001f0308,0x2090021]))) (nd (lf 0xd0830007f2 [0x1f0104000f,0x2103080028,0x3400330209,0x19]) (nd (lf 0x54830005b2 [0xb001a0203,0x40018]) (lf 0x54830007b2 [0x330203001a,0x104])))) (nd (nd (lf 0x54830005f2 [0x1f001a0203,0x18000a000b]) (nd (lf 0x54830007f2 [0x1040203001a,0x33001f000f]) (lf 0x94830007b2 [0x1d0104001a,0x21]))) (nd (lf 0x10c3000772 [0x203000f001a]) (nd (lf 0x50c30007f2 [0x203001a001f,0x118000c000f]) (lf 0xd0c3000772 [0x1f0034000f,0x190308]))))) (nd (nd (nd (lf 0xd0c30007f2 [0xf001a001f,0x104000c]) (nd (lf 0x15030005f2 [0x1d000a001a,0x80004]) (lf 0x55030005f2 [0x1a02030021,0xc000b0018]))) (nd (lf 0x55030007f2 [0xf001d001a,0x2103040118,0x104]) (nd (lf 0x95030005f2 [0x3040203001c,0xc00040009]) (lf 0x95030007f2 [0x304000f001a,0x180104])))) (nd (nd (lf 0xd5030005f2 [0x203001a0021,0x4]) (nd (lf 0x8c63000772 [0x2030108001f,0xf001c]) (lf 0x90630007f2 [0x2800190016,0x20c000f001a,0x20400100118,0x18000c0104,0x1c]))) (nd (lf 0x94630005f2 [0x30400160010]) (nd (lf 0x4ca3000772 [0x2030104000c,0x1900280308,0xf0021]) (lf 0xcca3000772 [0x3080010001f,0x10402030028]))))))
def F13T7_2 := nd (nd (nd (nd (nd (lf 0x50a30007b2 [0xc02030027,0x21003080018,0x1040019000f]) (lf 0x50a30006f2 [0x280203001f,0x1801040308])) (nd (lf 0x50a30007f2 [0x3080203001f,0x280018000f,0x1000190104,0x27]) (nd (lf 0x90a30007b2 [0xf0203001f,0x3080118001d,0xc0019]) (lf 0xd0a30006f2 [0x2030028001f,0xf01040308,0x21])))) (nd (nd (lf 0xd0a30007f2 [0x308000f001f,0x2800340021,0x19]) (nd (lf 0x54a30005f2 [0x3080010001f,0xc0203]) (lf 0x10e3000772 [0x34000f0010,0x190308]))) (nd (lf 0xd0e3000772 [0x203000f001f,0x190034000c]) (nd (lf 0x55230005f2 [0x20300100021,0xb00180308,0x4]) (lf 0x95230005f2 [0x40010001c]))))) (nd (nd (nd (lf 0xd5230005f2 [0xc00160021]) (nd (lf 0x14132005b2 [0x10000c0016,0x180103]) (lf 0x14132007b2 [0x3030116000c,0x3080032]))) (nd (lf 0x10d3200732 [0x308000c010f,0x18011c0303]) (nd (lf 0x10d32007b2 [0x1a000c0010,0x18]) (lf 0x90d32007b2 [0x1a000c0010,0x118])))) (nd (nd (lf 0xd0d3200732 [0x308010f000c,0x18011c0303,0x4]) (nd (lf 0x15132007b2 [0x308010f000c,0x1803030027]) (lf 0x55132005b2 [0x3080018000c,0xb001d0303]))) (nd (lf 0xd5132005b2 [0x308000c0018,0xb001d0303,0x4]) (nd (lf 0xd5132007b2 [0x3030027000c,0x130308]) (lf 0x1413200772 [0x20401030028,0xc003c0308,0x21])))))) (nd (nd (nd (nd (lf 0x9413200772 [0x204000c0028,0x2103080103]) (nd (lf 0xd093200632 [0x3030308]) (lf 0xd093200732 [0x3080021010a,0x40303]))) (nd (lf 0xd493200732 [0x308001f0010,0x40103]) (nd (lf 0x1513200772 [0x11c0204003c,0x303000c0021,0x300308]) (lf 0x5513200772 [0xc00280021,0x10303030308,0x108])))) (nd (nd (lf 0x9513200772 [0x204000c0028,0x10a03030308,0x21]) (nd (lf 0xd513200772 [0x308003c0021,0xc02040303,0x30]) (lf 0x14132005f2 [0xc02040016,0xa00180010]))) (nd (lf 0x14132007f2 [0x1030204000c,0x2100100308,0x2b00280032,0x3c0033]) (nd (lf 0xcc932007b2 [0x1a001f0010,0x4]) (lf 0x50932007b2 [0x30803030027,0x2b0018000c,0xa00090004]))))) (nd (nd (nd (lf 0xd0932006b2 [0x3030308020c,0x4]) (nd (lf 0xd0932007b2 [0x30800210033,0x10a0303020c,0x4002e0009,0xc]) (lf 0x10d3200772 [0x1a0204003c,0x303000c0021,0x30010a0308]))) (nd (lf 0x10d32007f2 [0x204000c0010,0xe0021001a,0x10a]) (nd (lf 0x50d3200772 [0x308000c0021,0x2040303]) (lf 0x90d3200772 [0x30303080021,0x90204000c])))) (nd (nd (lf 0x90d32007f2 [0x1a00100021,0x204000c]) (nd (lf 0xd0d3200772 [0x3080204000c,0x21010a0303]) (lf 0x15132005f2 [0x1c0204000f,0x9000c]))) (nd (lf 0x15132007f2 [0x210204000c,0x2b03080303,0x90027010a]) (nd (lf 0x55132005f2 [0x180204000c,0x1d03030308,0x8000b0003]) (lf 0x95132005f2 [0x1c0204000f,0xc]))))))
def F13T7_3 := nd (nd (nd (nd (nd (lf 0xd5132005f2 [0x30802040018,0x1d000c0303,0x9000b]) (lf 0xd5132007f2 [0x303000c0021,0x2b02040308,0xa00090027])) (nd (lf 0x94232005b2 [0x10000c0016,0x18]) (nd (lf 0x10e32007b2 [0x1a000c0010,0x18]) (lf 0x90e32007b2 [0x1a000c0010,0x18])))) (nd (nd (lf 0x54e32005b2 [0x3030308000c,0x18000b001d]) (nd (lf 0x55232004b2 [0xc03030308,0x18]) (lf 0x55232005b2 [0x308000c0018,0xb001d0303]))) (nd (lf 0x1433200772 [0x1030204001a,0x21]) (nd (lf 0x9433200772 [0x3080010001f,0x2040028]) (lf 0x1533200772 [0x204001a0010,0x1f0021]))))) (nd (nd (nd (lf 0x5533200772 [0x308001f0021,0x2040303]) (nd (lf 0x9533200772 [0x3080010001f,0x204010a0021]) (lf 0xd533200772 [0x1a00100021]))) (nd (lf 0x94332005f2 [0x100016001f,0x204]) (nd (lf 0x10f3200772 [0x1a02040010,0x1f0018]) (lf 0x50f3200772 [0x308001f0021,0x2040303])))) (nd (nd (lf 0x90f3200772 [0x1a00100021,0x204]) (nd (lf 0xd0f3200772 [0x3080010001f,0x204010a0021,0xc]) (lf 0x15332005f2 [0x204001a0010,0xa]))) (nd (lf 0x55332005f2 [0x3080018001f,0x1d02040303,0xb]) (nd (lf 0x95332005f2 [0x1c000f001f,0x204]) (lf 0x94043005f2 [0xf00100016])))))) (nd (nd (nd (nd (lf 0x54843005b2 [0x4001c0010,0xf000b001d,0x1a]) (nd (lf 0x54843007b2 [0xa001a0010,0x104]) (lf 0x54843005f2 [0x1a00100104,0xa0021001f,0xb001d]))) (nd (lf 0x54843007f2 [0x1a000a0010,0x1f00210104]) (nd (lf 0x94843007b2 [0xa001a0010,0x104]) (lf 0x50c4300672 [0x1a00210010,0xc])))) (nd (nd (lf 0x50c4300772 [0x18000f0021,0x1c]) (nd (lf 0x50c43007f2 [0x1a00100021,0x18000c]) (lf 0x90c4300772 [0x1a00100021,0x80018]))) (nd (lf 0x94c43005f2 [0x1a00100021,0x40018]) (nd (lf 0x14143005f2 [0xc00210016,0xf00180010,0x4]) (lf 0x14143007f2 [0x103000c0021,0xf003d0308,0x10]))))) (nd (nd (nd (lf 0xd4943005f2 [0x308001f0021,0xc01040303,0xb001d]) (nd (lf 0x90d43006f2 [0x1a00100021,0x8000c]) (lf 0x94243005f2 [0x1800100016,0xf]))) (nd (lf 0x54a43005b2 [0x1a00210010,0xb001d000c,0x18]) (nd (lf 0x54a43007b2 [0x1a00100021,0x1040018]) (lf 0x54a43005f2 [0x1a00100021,0xb001d0104,0x1f])))) (nd (nd (lf 0x94a43007b2 [0x1a00180010,0x104]) (nd (lf 0xd0e4300672 [0x21001c0010,0x1f001a000f]) (lf 0xd0e4300772 [0x1c000f0021,0x18]))) (nd (lf 0xd0e43007f2 [0x1a00100021,0x2040018000c]) (nd (lf 0x94e43005f2 [0xa001a0010,0x4]) (lf 0x55243005f2 [0x308000c0021,0xb001d0303]))))))
def F13T7 : BTree NodeData := nd (nd F13T7_0 F13T7_1) (nd F13T7_2 F13T7_3)
def F13M7 : BST := BN 359382969 116224 (BN 313196657 50944 (BN 282014102 127744 (BN 258675953 9089 (BN 239549552 127232 (BN 212496585 50816 (BN 203026639 116352 (BN 184329079 40705 (BN 174570364 45056 (BL 163545733 55680) (BL 178262028 45058)) (BN 192771138 4992 (BL 188335140 20096) (BL 194235230 121216))) (BN 207905589 119680 (BN 207462637 129408 (BL 206067449 59264) (BL 207679671 120448)) (BN 209544952 49154 (BL 208811367 56448) (BL 212115669 33664)))) (BN 230079606 2304 (BN 223444700 117120 (BN 216932583 63872 (BL 212640842 27776) (BL 219319387 39808)) (BN 227916185 61312 (BL 225621018 27520) (BL 228261614 130688))) (BN 236025945 4866 (BN 233182848 49152 (BL 232352183 16256) (BL 234816468 63360)) (BN 238070974 13824 (BL 237185713 126848) BE)))) (BN 249497566 44162 (BN 246655659 30592 (BN 243178872 11136 (BN 241737898 24448 (BL 240998118 2944) (BL 242944156 125056)) (BN 244171725 49153 (BL 243985550 115968) (BL 246202070 11906))) (BN 247835250 121088 (BN 247380154 54400 (BL 246821702 16641) (BL 247702305 8192)) (BN 249131895 45312 (BL 248835088 11904) BE))) (BN 256649880 38528 (BN 252414102 26752 (BN 250560100 25857 (BL 250490090 40194) (BL 250638068 21378)) (BN 256066611 14592 (BL 253271086 21376) (BL 256477259 20736))) (BN 257311475 30209 (BN 256850100 21632 (BL 256749949 63233) (BL 256869090 36609)) (BN 258110698 38912 (BL 258005938 38784) BE))))) (BN 270041024 7040 (BN 264646756 10624 (BN 261085878 58752 (BN 260364675 7426 (BN 260110656 45824 (BL 259245980 3968) (BL 260329844 12544)) (BN 260889848 51458 (BL 260502609 119552) (BL 260956510 45954))) (BN 263681978 36736 (BN 261305088 41089 (BL 261185947 130817) (BL 262013738 10626)) (BN 264546654 29440 (BL 264173813 33024) BE))) (BN 267686338 59266 (BN 266821512 62338 (BN 265819016 119040 (BL 265006397 36611) (BL 265946689 40962)) (BN 267023929 129664 (BL 266965014 121474) (BL 267275466 14208))) (BN 269336955 24192 (BN 268392829 18816 (BL 267784764 45952) (BL 268918646 17280)) (BN 270018203 22784 (BL 269442395 41091) BE)))) (BN 275924138 40961 (BN 272760340 37120 (BN 271732264 6402 (BN 270889292 9472 (BL 270086744 61313) (BL 271459927 1664)) (BN 272545612 10112 (BL 271908811 122752) (BL 272680758 48897))) (BN 274522742 16257 (BN 273292768 45185 (BL 272899159 32515) (BL 273557626 64128)) (BN 274958785 128896 (BL 274888747 121472) BE))) (BN 279405934 46720 (BN 277956685 39168 (BN 276724587 120066 (BL 276168262 41730) (BL 277578104 62208)) (BN 278920431 55040 (BL 278031770 42624) (BL 279356272 8065))) (BN 280818065 48899 (BN 280732446 124800 (BL 279571013 30080) (BL 280780490 8962)) (BN 281430075 45187 (BL 281109168 31872) BE)))))) (BN 298786048 127360 (BN 292119926 52096 (BN 287909445 41088 (BN 284164488 24960 (BN 283186861 32640 (BN 282392683 25344 (BL 282318593 37635) (BL 282918182 121600)) (BN 283473447 36608 (BL 283275912 124416) (BL 284007011 130944))) (BN 286287816 50048 (BN 285099387 118018 (BL 284725971 6528) (BL 285545166 64640)) (BN 286890780 119424 (BL 286652545 12288) (BL 287377798 129537)))) (BN 290685337 44160 (BN 288981473 122112 (BN 288861658 32128 (BL 288442095 45440) (BL 288911463 2432)) (BN 289732524 20480 (BL 289411674 31360) (BL 290071135 123650))) (BN 291617838 120832 (BN 291414011 57216 (BL 291085632 13184) (BL 291595488 44161)) (BN 291698046 18688 (BL 291628036 31490) BE)))) (BN 295307152 13952 (BN 293721088 43776 (BN 293276249 40960 (BN 292656807 55168 (BL 292182559 39170) (BL 293116320 15872)) (BN 293359856 3712 (BL 293299028 125185) (BL 293643746 45184))) (BN 294620101 21248 (BN 294333434 48768 (BL 293721714 41344) (BL 294569333 52482)) (BN 295267667 122753 (BL 295260513 118400) BE))) (BN 297173826 125824 (BN 296393792 40576 (BN 296064034 124674 (BL 295829578 5378) (BL 296134044 38144)) (BN 296618557 25346 (BL 296450135 60545) (BL 297055406 6016))) (BN 297857486 32002 (BN 297735026 36097 (BL 297552318 48640) (BL 297795854 25472)) (BN 298782186 38658 (BL 298644607 1536) BE))))) (BN 305867337 17281 (BN 301998564 32641 (BN 300682484 5760 (BN 299677495 120192 (BN 299363119 61952 (BL 299356634 59776) (BL 299417470 384)) (BN 300237328 29056 (BL 299732795 44163) (BL 300265576 17536))) (BN 300948333 128769 (BN 300820287 34562 (BL 300729123 124544) (BL 300886133 126081)) (BN 301627246 56194 (BL 301089994 7680) BE))) (BN 304587442 60547 (BN 303102250 47744 (BN 302760483 31616 (BL 302043448 37632) (BL 302768974 26880)) (BN 303844067 35328 (BL 303356153 129536) (BL 304543276 4864))) (BN 305118482 25984 (BN 304946420 11011 (BL 304773053 8064) (BL 305020968 22912)) (BN 305719663 40065 (BL 305384331 16513) BE)))) (BN 309075706 37122 (BN 307287093 62336 (BN 306512176 14978 (BN 306063244 34690 (BL 305919309 42112) (BL 306164571 56960)) (BN 307196481 42880 (BL 306967155 30848) (BL 307204972 128256))) (BN 307947588 41346 (BN 307601639 130432 (BL 307439704 42754) (BL 307748955 29952)) (BN 309023440 126083 (BL 308051714 22274) BE))) (BN 311743659 23680 (BN 309618752 19712 (BN 309124885 39296 (BL 309085640 128771) (BL 309165494 10496)) (BN 309859089 12801 (BL 309769450 116354) (BL 311403153 3200))) (BN 312296473 14720 (BN 312220514 32129 (BL 312110731 125184) (BL 312280675 121730)) (BN 312803515 44544 (BL 312604779 35072) BE))))))) (BN 338686949 9344 (BN 324850669 16131 (BN 319329035 53760 (BN 316177292 50176 (BN 314205448 129410 (BN 313521638 16515 (BN 313473900 129024 (BL 313354567 770) (BL 313512294 41217)) (BN 313856970 40067 (BL 313601492 13568) (BL 314042581 40832))) (BN 314832944 35329 (BN 314615415 49025 (BL 314506878 42368) (BL 314726088 49281)) (BN 315542780 14976 (BL 314912000 26496) (BL 315669544 2)))) (BN 317765526 10368 (BN 316716673 18306 (BN 316584159 30720 (BL 316546729 36096) (BL 316713362 16129)) (BN 317094610 28160 (BL 316972010 19328) (BL 317709937 61184))) (BN 319007421 40192 (BN 318421985 7296 (BL 318388535 37504) (BL 318898840 60544)) (BN 319239396 50818 (BL 319201863 35712) BE)))) (BN 322146073 33408 (BN 321190283 62080 (BN 320105542 122882 (BN 319801024 6272 (BL 319615413 2816) (BL 319804419 17920)) (BN 320363090 13312 (BL 320177481 43394) (BL 320820356 115584))) (BN 321889771 60288 (BN 321386401 1280 (BL 321264131 40448) (BL 321611933 128640)) (BN 322145935 53376 (BL 321904587 11776) BE))) (BN 323596184 125312 (BN 322863395 49283 (BN 322476860 9856 (BL 322201524 50304) (BL 322784174 37633)) (BN 323207791 55554 (BL 322932248 49024) (BL 323334838 126080))) (BN 323839471 117376 (BN 323678570 49409 (BL 323675394 63874) (BL 323745518 116992)) (BN 324093107 116737 (BL 324051411 35584) BE))))) (BN 331952925 49280 (BN 328566529 120833 (BN 325711994 46337 (BN 325390786 45441 (BN 325011301 16386 (BL 324935526 53120) (BL 325270746 2688)) (BN 325597552 896 (BL 325456092 120320) (BL 325626281 125568))) (BN 326796828 19200 (BN 326479350 47232 (BL 325793419 30976) (BL 326771301 9088)) (BN 328492508 43904 (BL 327179487 65408) BE))) (BN 330531568 28672 (BN 329447299 36866 (BN 328710598 46592 (BL 328670792 12800) (BL 328882006 7424)) (BN 329844525 61568 (BL 329837494 16385) (BL 330308547 3713))) (BN 330915348 128128 (BN 330648613 127489 (BL 330537535 17282) (BL 330854716 22656)) (BN 331943920 43648 (BL 331775835 54016) BE)))) (BN 335004425 130690 (BN 333388839 117634 (BN 332815807 31488 (BN 332670935 22400 (BL 332168902 29184) (BL 332772575 28928)) (BN 333108999 60032 (BL 332987603 30336) (BL 333173020 33920))) (BN 334273492 36865 (BN 333910977 12160 (BL 333590171 45826) (BL 334250951 46848)) (BN 334967566 9216 (BL 334744545 25473) BE))) (BN 337164902 62848 (BN 335335118 129280 (BN 335062947 63744 (BL 335007081 18945) (BL 335290714 119936)) (BN 336777450 127616 (BL 336233806 48896) (BL 336986873 128768))) (BN 337836057 58369 (BN 337251805 124672 (BL 337186019 125313) (BL 337583161 27904)) (BN 338113976 64256 (BL 338026169 29442) BE)))))) (BN 348627475 42752 (BN 344132334 46976 (BN 341483799 54657 (BN 341067336 20224 (BN 339931587 30208 (BN 339349440 34048 (BL 339307440 0) (BL 339920237 59392)) (BN 340249595 6400 (BL 339969957 38656) (BL 340550471 9728))) (BN 341321235 45568 (BN 341213448 6784 (BL 341180884 12928) (BL 341315078 116864)) (BN 341451837 30464 (BL 341422871 16512) BE))) (BN 342944462 24320 (BN 342351335 124802 (BN 341684217 38272 (BL 341637578 120193) (BL 341729080 48128)) (BN 342783102 59648 (BL 342776277 52736) (BL 342910827 120064))) (BN 343395145 28544 (BN 343134935 23808 (BL 343120296 4353) (BL 343367607 127233)) (BN 343743438 122880 (BL 343402669 36352) BE)))) (BN 345764680 46464 (BN 345101628 20225 (BN 344671773 63616 (BN 344456304 53249 (BL 344356235 19456) (BL 344550330 130433)) (BN 344839339 121856 (BL 344685593 41728) (BL 344972370 52609))) (BN 345503334 24704 (BN 345320029 44803 (BL 345304412 58114) (BL 345387859 28034)) (BN 345762246 34560 (BL 345709350 118528) BE))) (BN 347219100 3328 (BN 346152489 130434 (BN 345969797 27392 (BL 345792997 43008) (BL 346147734 128512)) (BN 347074387 39936 (BL 346775242 43264) (BL 347130626 43266))) (BN 347803605 115969 (BN 347532704 61953 (BL 347380460 25728) (BL 347740510 16128)) (BN 347912909 15104 (BL 347838667 19968) BE))))) (BN 354118012 29696 (BN 351784943 15744 (BN 349794822 26624 (BN 349297821 8960 (BN 349107771 35968 (BL 348649197 16384) (BL 349239485 22272)) (BN 349682014 34816 (BL 349537626 24705) (BL 349756027 36995))) (BN 350953745 21888 (BN 350390903 49536 (BL 350145348 123008) (BL 350415405 33152)) (BN 351472308 9986 (BL 351116890 44288) BE))) (BN 353081132 25856 (BN 352423860 28801 (BN 352213990 128 (BL 351851364 11649) (BL 352214356 58880)) (BN 352590242 57600 (BL 352574040 3840) (BL 352709364 2305))) (BN 353165944 8448 (BN 353121689 60672 (BL 353085195 36864) (BL 353157826 13056)) (BN 353616718 118016 (BL 353238935 20227) BE)))) (BN 356649988 58496 (BN 355652342 61696 (BN 354257127 44928 (BN 354236010 15232 (BL 354230820 35840) (BL 354241898 118145)) (BN 355319551 14464 (BL 355236879 56192) (BL 355470605 27008))) (BN 356213140 40833 (BN 355731905 17408 (BL 355683672 32770) (BL 355912248 21762)) (BN 356350643 46336 (BL 356343915 23552) BE))) (BN 357940909 5632 (BN 357311781 30721 (BN 357206914 47488 (BL 357010038 8320) (BL 357271384 13696)) (BN 357674933 24707 (BL 357617116 17665) (BL 357769047 123777))) (BN 359027233 18176 (BN 358792715 125826 (BL 358588466 123648) (BL 358911083 117632)) (BN 359343163 119296 (BL 359165677 43521) BE)))))))) (BN 401707537 8323 (BN 380486112 25858 (BN 369285098 59520 (BN 365598409 64000 (BN 362145311 51201 (BN 360119670 4098 (BN 359755549 29824 (BN 359672877 34688 (BL 359449951 123778) (BL 359718296 49792)) (BN 359879817 22914 (BL 359793534 64768) (BL 360047306 125825))) (BN 360608713 51584 (BN 360483853 36480 (BL 360469451 40321) (BL 360561167 28803)) (BN 361853892 24194 (BL 361659528 127361) (BL 361931999 4352)))) (BN 363601675 14849 (BN 363086664 52480 (BN 362546243 897 (BL 362250460 24577) (BL 362838641 130306)) (BN 363351703 19075 (BL 363160613 12672) (BL 363392691 38530))) (BN 364940077 19072 (BN 364644362 130176 (BL 364382426 11264) (BL 364919851 58240)) (BN 365225416 11392 (BL 365021636 4481) BE)))) (BN 367803551 62849 (BN 366476442 31104 (BN 366028105 118272 (BN 365768331 5504 (BL 365720633 116736) (BL 365838341 17152)) (BN 366374817 32000 (BL 366082931 43779) (BL 366423387 121475))) (BN 367493699 9729 (BN 366660876 51456 (BL 366581309 128001) (BL 367321804 120704)) (BN 367689934 43392 (BL 367638472 63104) BE))) (BN 368814662 26240 (BN 368474706 58368 (BN 368048173 127488 (BL 367828689 58754) (BL 368160524 29185)) (BN 368582584 122496 (BL 368514512 2048) (BL 368635623 117248))) (BN 369080360 640 (BN 368897452 115586 (BL 368836399 59778) (BL 369006107 28546)) (BN 369274770 51586 (BL 369251213 24578) BE))))) (BN 375651193 18944 (BN 372897120 40449 (BN 371278034 47747 (BN 370210637 47616 (BN 369939397 60801 (BL 369738979 23937) (BL 370138777 115458)) (BN 370622435 29953 (BL 370470296 65280) (BL 371035321 123266))) (BN 372167428 32513 (BN 371764661 48001 (BL 371637012 17024) (BL 372161356 123776)) (BN 372711484 118785 (BL 372665810 55936) BE))) (BN 373693577 35456 (BN 373148857 56576 (BN 373035198 37248 (BL 372950510 46080) (BL 373071621 55808)) (BN 373393109 39169 (BL 373250660 50560) (BL 373615604 56320))) (BN 374529534 126976 (BN 374019408 64770 (BL 373915536 38400) (BL 374291164 36225)) (BN 375303826 126720 (BL 374646635 31232) BE)))) (BN 378071322 120577 (BN 377144001 35200 (BN 376764352 57728 (BN 375776232 62083 (BL 375758096 115712) (BL 376295521 41856)) (BN 376981000 48000 (BL 376866967 18689) (BL 377094196 64896))) (BN 377829107 25345 (BN 377660782 56578 (BL 377441838 44672) (BL 377756573 126209)) (BN 377977380 43520 (BL 377852112 16000) BE))) (BN 379281154 56705 (BN 378706802 121473 (BN 378575678 121984 (BL 378129575 39552) (BL 378585441 59008)) (BN 378965532 119808 (BL 378722611 127872) (BL 379208925 126337))) (BN 379891963 62721 (BN 379501282 22016 (BL 379321568 32768) (BL 379739824 118912)) (BN 380287268 53504 (BL 380212230 125571) BE)))))) (BN 390330768 3072 (BN 385547681 52608 (BN 382918488 125696 (BN 381871898 768 (BN 381256708 52098 (BN 380830688 27264 (BL 380494844 53248) (BL 381030793 120960)) (BN 381440150 115328 (BL 381302965 38145) (BL 381686287 124161))) (BN 382413378 14848 (BN 382075343 35713 (BL 381877836 54144) (BL 382257462 14336)) (BN 382710937 34561 (BL 382565972 32384) BE))) (BN 383937280 54784 (BN 383561449 47745 (BN 383021439 116096 (BL 383011676 15488) (BL 383142805 55424)) (BN 383755944 32256 (BL 383594621 28032) (BL 383757566 4096))) (BN 384340335 40704 (BN 383999480 61440 (BL 383939387 63488) (BL 384259881 17664)) (BN 385466791 46208 (BL 384605823 62720) BE)))) (BN 388113135 45569 (BN 386813749 124032 (BN 385894770 10240 (BN 385664218 51840 (BL 385617527 47872) (BL 385837512 46465)) (BN 386306005 51968 (BL 386208629 120579) (BL 386394240 56704))) (BN 387708347 121728 (BN 387642618 15616 (BL 387578803 13440) (BL 387705131 23426)) (BN 388059647 62081 (BL 387752018 60160) BE))) (BN 389173865 63232 (BN 388462400 28800 (BN 388379386 51713 (BL 388191942 65024) (BL 388435478 37888)) (BN 389005029 51200 (BL 388598162 124928) (BL 389134232 3841))) (BN 389990406 11520 (BN 389671877 58626 (BL 389284231 34304) (BL 389899675 117760)) (BN 390100216 23168 (BL 390053525 59136) BE))))) (BN 394414344 28033 (BN 392054710 122625 (BN 391541261 43651 (BN 391066703 129025 (BN 390742003 117504 (BL 390369162 24833) (BL 390946425 4480)) (BN 391502505 33536 (BL 391365988 11648) (BL 391539926 52992))) (BN 391725122 55552 (BN 391578643 5121 (BL 391567961 129152) (BL 391723631 130048)) (BN 392030088 39040 (BL 391982447 126211) BE))) (BN 392934599 42240 (BN 392495645 125569 (BN 392188016 6912 (BL 392144345 18304) (BL 392419296 27009)) (BN 392660079 9984 (BL 392604370 123136) (BL 392889109 24576))) (BN 393529409 50432 (BN 393071257 130560 (BL 393034160 52224) (BL 393441027 128000)) (BN 393609863 130816 (BL 393570230 8321) BE)))) (BN 397473046 53251 (BN 396638653 5376 (BN 395864186 60800 (BN 395072219 7168 (BL 394794976 5888) (BL 395755708 40064)) (BN 395975924 57472 (BL 395900233 10241) (BL 396003959 19584))) (BN 397124431 2176 (BN 396745070 125953 (BL 396731851 116480) (BL 397066645 47360)) (BN 397291645 26112 (BL 397271539 3843) BE))) (BN 400192017 122627 (BN 398720043 43009 (BN 397777235 54272 (BL 397506393 57346) (BL 398182478 125952)) (BN 399764509 33792 (BL 399442691 20737) (BL 400035355 52481))) (BN 401205690 49664 (BN 400416536 23424 (BL 400336231 3073) (BL 401076245 48770)) (BN 401560429 5248 (BL 401245131 7936) BE))))))) (BN 434473984 50433 (BN 420948171 61441 (BN 411861293 25986 (BN 407193217 119168 (BN 404113524 1024 (BN 403140639 53633 (BN 403027132 45696 (BL 402741658 20864) (BL 403129953 44290)) (BN 403560740 129794 (BL 403443139 24064) (BL 403824676 43649))) (BN 406218804 34049 (BN 405681129 12416 (BL 405205943 40320) (BL 406160281 386)) (BN 406444952 256 (BL 406393959 18560) (BL 407139245 16640)))) (BN 409465544 27905 (BN 407734234 56832 (BN 407425295 5762 (BL 407220712 16896) (BL 407471934 124546)) (BN 409242083 123264 (BL 408649751 10752) (BL 409377112 118017))) (BN 409953525 7553 (BN 409769627 48386 (BL 409732944 38914) (BL 409899201 63489)) (BN 411491750 121857 (BL 410829957 38016) BE)))) (BN 416505846 21760 (BN 412990805 126210 (BN 412525778 19840 (BN 412194567 15360 (BL 411949016 23425) (BL 412296660 29312)) (BN 412830268 1794 (BL 412544211 60928) (BL 412833327 52352))) (BN 414199815 25088 (BN 413379719 127104 (BL 413085749 121344) (BL 413821743 58112)) (BN 416430429 57345 (BL 416408773 49408) BE))) (BN 418785728 54530 (BN 417073936 62976 (BN 417001437 58624 (BL 416980209 126464) (BL 417003762 122368)) (BN 418541085 21889 (BL 418388841 41600) (BL 418585948 8704))) (BN 419391215 28416 (BN 419039284 14722 (BL 418823722 120576) (BL 419206153 14337)) (BN 420761278 115201 (BL 419929527 2691) BE))))) (BN 427305055 115840 (BN 423827213 20608 (BN 422084383 48256 (BN 421249689 42370 (BN 421144289 57344 (BL 421028188 21122) (BL 421176605 61824)) (BN 421843957 32512 (BL 421696207 115200) (BL 421881721 22144))) (BN 422836275 54912 (BN 422351777 39680 (BL 422217292 5120) (BL 422667014 15617)) (BN 423222371 8832 (BL 422869057 43136) BE))) (BN 426205479 60416 (BN 425728226 118787 (BN 424775666 123265 (BL 424606693 41216) (BL 425384169 37889)) (BN 425891297 117761 (BL 425778946 51712) (BL 425928152 22529))) (BN 426785346 25859 (BN 426479656 57088 (BL 426302743 17922) (BL 426677487 44800)) (BN 427272273 124288 (BL 427251759 55939) BE)))) (BN 431025750 117888 (BN 428951921 21120 (BN 428093250 14080 (BN 427658369 25216 (BL 427618010 44289) (BL 427882842 54656)) (BN 428475681 123905 (BL 428449606 21504) (BL 428777415 57730))) (BN 430289928 126977 (BN 429870116 13697 (BL 429244544 12032) (BL 430287975 58625)) (BN 430499992 7169 (BL 430297716 53890) BE))) (BN 432300687 44674 (BN 431355972 130304 (BN 431184555 17027 (BL 431113485 36992) (BL 431190095 42496)) (BN 432022395 14723 (BL 431936542 49921) (BL 432212942 2689))) (BN 433876221 24832 (BN 433029583 52864 (BL 432368704 31744) (BL 433680542 4224)) (BN 434045194 3457 (BL 434042684 115072) BE)))))) (BN 457979332 57729 (BN 444748511 129792 (BN 437465581 37760 (BN 436208625 60673 (BN 434725926 119809 (BN 434582318 124162 (BL 434547378 2819) (BL 434674813 118784)) (BN 435749184 32896 (BL 435197680 41985) (BL 435878314 7552))) (BN 436787358 3584 (BN 436489084 56321 (BL 436244306 126208) (BL 436736685 54146)) (BN 437098457 23296 (BL 436892888 15619) BE))) (BN 439985064 118656 (BN 438983376 35587 (BN 438221449 53888 (BL 437959186 116225) (BL 438656108 115456)) (BN 439320498 14721 (BL 439170557 50688) (BL 439535174 55937))) (BN 443312212 8576 (BN 440321638 18432 (BL 440017481 48512) (BL 441695640 52866)) (BN 444588298 44801 (BL 443557559 10497) BE)))) (BN 450155893 51328 (BN 446981145 11008 (BN 445758612 513 (BN 445246672 48129 (BL 444757636 62464) (BL 445439452 9600)) (BN 446162416 49923 (BL 446131638 37762) (BL 446367985 56064))) (BN 448268558 115074 (BN 447993557 13569 (BL 447892189 3458) (BL 448178966 6144)) (BN 449024296 36993 (BL 448376879 54529) BE))) (BN 454516200 8705 (BN 452899221 45699 (BN 451852941 22528 (BL 450472472 512) (BL 452614964 44032)) (BN 454018039 1792 (BL 453621220 128384) (BL 454375985 122113))) (BN 456884511 19841 (BN 455022050 27648 (BL 454928190 14081) (BL 456704786 33280)) (BN 457822130 57984 (BL 457538086 8578) BE))))) (BN 479166024 10881 (BN 465398297 21505 (BN 463645513 17153 (BN 461911878 124160 (BN 459114330 123904 (BL 458133323 42497) (BL 461122469 55296)) (BN 463065497 14083 (BL 462404549 118144) (BL 463557081 769))) (BN 464079170 15361 (BN 463962131 127619 (BL 463949725 47490) (BL 464004922 41472)) (BN 465182636 45697 (BL 464499486 49920) BE))) (BN 472721054 126336 (BN 467248860 128385 (BN 465836329 47104 (BL 465815223 19073) (BL 466882609 10883)) (BN 468398129 6787 (BL 467803293 36224) (BL 472568810 123520))) (BN 476245546 127617 (BN 475170140 10880 (BL 473219253 31106) (BL 475325395 122498)) (BN 478349073 53632 (BL 478286958 48384) BE)))) (BN 489308783 32386 (BN 482062811 23936 (BN 480659625 34944 (BN 479598526 44416 (BL 479379326 54528) (BL 480417608 26370)) (BN 481706327 1025 (BL 480681544 6785) (BL 481838338 4736))) (BN 486098951 3456 (BN 484050085 122240 (BL 482153814 28674) (BL 484594923 16002)) (BN 488905895 16897 (BL 486589812 9218) BE))) (BN 521605379 26368 (BN 503635772 64512 (BN 494229452 130305 (BL 490966730 122624) (BL 502785020 55297)) (BN 512054548 25601 (BL 505634283 128386) (BL 519578266 33281))) (BN 537979337 25600 (BN 529756089 29315 (BL 528709809 41984) (BL 535886296 31745)) (BN 552182263 9602 (BL 542039504 29313) BE))))))))
def F13T8 : BTree NodeData := nd (nd (nd (lf 0x10003f1 [0x10400030008,0x4000b]) (nd (lf 0x20003b1 [0x10800030004]) (lf 0x220003b1 [0x400030016]))) (nd (nd (lf 0x220003f1 [0x10800030004,0x23001d]) (lf 0x30003f1 [0x104001a0003,0x40108])) (nd (lf 0x230003f1 [0x10000c0003,0x401040108]) (lf 0x132003b1 [0x1030108000c,0x4])))) (nd (nd (nd (lf 0x13200371 [0x10301080004]) (lf 0x132003f1 [0x10301080004,0xc])) (nd (lf 0x232003b1 [0x10301080004,0xc]) (lf 0x33200371 [0x10301080004]))) (nd (nd (lf 0x332003f1 [0x10800100004,0x103001f]) (lf 0x43003f1 [0x104001c0010,0xf01030108,0x4001a])) (nd (lf 0x143003f1 [0x1080018001f,0xc00040103,0x21]) (lf 0x243003f1 [0x10800210010,0x1801030004,0x1a]))))
def F13M8 : BST := BN 342935122 25728 (BN 302145968 6915 (BN 281018675 2 (BN 266370491 4482 (BN 256223766 4097 (BN 251910739 6914 (BN 244085996 28544 (BN 234816468 12160 (BL 221826390 2560) BE) (BN 249350623 5633 (BL 249280613 7296) BE)) (BN 253786621 26881 (BN 253716611 384 (BL 253555942 27520) BE) (BL 254702584 9344))) (BN 261996457 15361 (BN 259138582 27264 (BN 257542976 15232 (BL 256434763 10624) BE) (BN 261453157 15744 (BL 259155198 27776) BE)) (BN 265092281 10880 (BN 264116369 26368 (BL 263591196 16000) BE) (BL 265704291 27008)))) (BN 274566182 31745 (BN 269325149 6401 (BN 267831974 6272 (BN 267320350 10497 (BL 266688276 3841) BE) (BN 268227197 5506 (BL 268118105 31232) BE)) (BN 270935216 3072 (BN 270514252 31872 (BL 269378187 26754) BE) (BL 272554103 32256))) (BN 276950238 7041 (BN 274958785 29568 (BN 274758367 10113 (BL 274751793 29185) BE) (BL 274966866 29312)) (BN 279951108 10368 (BN 279571013 896 (BL 277301920 26752) BE) (BL 280002990 32001))))) (BN 289444617 9986 (BN 284998474 9474 (BN 283889910 3200 (BN 281924093 3073 (BN 281755551 27136 (BL 281502423 28032) BE) (BN 283628564 31488 (BL 283193663 1538) BE)) (BN 284228313 2944 (BN 284221739 4608 (BL 284007011 25472) BE) (BL 284678166 14336))) (BN 287629661 12546 (BN 286420184 16256 (BN 286191549 11776 (BL 285454673 8194) BE) (BL 287048947 4480)) (BN 288325908 11904 (BN 288173644 8450 (BL 288140297 32003) BE) (BL 288861658 6016)))) (BN 296971418 2306 (BN 293563496 29184 (BN 293098510 6912 (BN 292535420 26114 (BL 291918293 31744) BE) (BN 293359856 5248 (BL 293297656 30592) BE)) (BN 295761941 7040 (BN 294620101 13056 (BL 294008661 6913) BE) (BL 296225969 32128))) (BN 299999935 30976 (BN 298683258 10752 (BN 297795854 26240 (BL 297749215 28288) BE) (BL 299056099 2816)) (BN 301820987 14080 (BN 301084007 9600 (BL 300795064 1280) BE) (BL 302098230 27649)))))) (BN 324235867 12800 (BN 316395477 25347 (BN 309092569 8192 (BN 305492408 3330 (BN 303350418 31489 (BN 302465922 12032 (BL 302331579 27521) BE) (BN 305208489 29697 (BL 304656571 0) BE)) (BN 308258170 25345 (BN 307858047 14722 (BL 307137611 30336) BE) (BL 308987420 29696))) (BN 311487725 31491 (BN 309385741 512 (BN 309240508 4099 (BL 309124885 12928) BE) (BL 309444686 26496)) (BN 314221882 9088 (BN 312619946 1793 (BL 311673336 28545) BE) (BL 316281398 14850)))) (BN 320162684 3584 (BN 318269602 28160 (BN 317986266 27137 (BN 317939373 8704 (BL 316581088 11648) BE) (BN 318262512 9472 (BL 318255180 3840) BE)) (BN 319161865 15234 (BN 319077431 13825 (BL 318657880 4992) BE) (BL 319621426 32385))) (BN 321133273 31104 (BN 320757253 1795 (BN 320717396 15874 (BL 320537105 4610) BE) (BL 320942864 8064)) (BN 322959856 16130 (BN 322900955 4096 (BL 322422264 11777) BE) (BL 323207791 9730))))) (BN 334615959 30209 (BN 330883589 16128 (BN 327222793 3842 (BN 326373399 13184 (BN 326051034 13696 (BL 324598682 14592) BE) (BN 326592619 4098 (BL 326434312 32640) BE)) (BN 329878862 29186 (BN 329805214 30848 (BL 327643789 28930) BE) (BL 330308547 5249))) (BN 333984754 1024 (BN 332854284 14208 (BN 332207973 31616 (BL 332077988 6658) BE) (BL 333747588 7426)) (BN 334388558 3586 (BN 334386576 9984 (BL 333994538 10498) BE) (BL 334594127 13568)))) (BN 338420752 9216 (BN 335974352 640 (BN 335288528 8833 (BN 334776819 32130 (BL 334744545 26241) BE) (BN 335565855 2432 (BL 335392791 3456) BE)) (BN 337513151 15488 (BN 336775332 258 (BL 336513986 7682) BE) (BL 337809982 13952))) (BN 341256774 513 (BN 339650304 3201 (BN 339578075 13441 (BL 338824556 14594) BE) (BL 341256453 5504)) (BN 342241048 26113 (BN 342055437 6657 (BL 341949149 8576) BE) (BL 342742342 27648))))))) (BN 379394173 12672 (BN 361445395 9346 (BN 352447766 14593 (BN 347651563 5888 (BN 345562152 15360 (BN 344086302 11905 (BN 344014073 5761 (BL 343292317 15105) BE) (BN 344558056 1665 (BL 344503231 5379) BE)) (BN 346680179 3328 (BN 346677046 2305 (BL 346491435 7681) BE) (BL 347371120 6784))) (BN 351429624 15107 (BN 350200226 642 (BN 348530933 1920 (BL 348011768 3585) BE) (BN 351215036 32514 (BL 350357147 14464) BE)) (BN 351871655 5632 (BN 351815653 2945 (BL 351710994 1536) BE) (BL 352423860 15617)))) (BN 359252276 25984 (BN 356690975 8448 (BN 354830889 8323 (BN 353784609 28672 (BL 353624840 514) BE) (BN 356307653 26880 (BL 356146992 12544) BE)) (BN 357987703 1154 (BN 357521782 26498 (BL 356859858 769) BE) (BL 359138769 32512))) (BN 360561167 15619 (BN 360485432 1792 (BN 360299821 25856 (BL 359407548 6656) BE) (BL 360551233 12802)) (BN 361157410 10112 (BN 361085181 11136 (BL 361052751 26112) BE) (BL 361213317 8832))))) (BN 370482845 25216 (BN 367114304 8321 (BN 365030512 4354 (BN 363843546 7680 (BN 361601309 8961 (BL 361574840 11264) BE) (BN 364997165 771 (BL 364791822 2561) BE)) (BN 366065162 30080 (BN 365881393 27266 (BL 365488749 2304) BE) (BL 367018307 1152))) (BN 368905071 32384 (BN 368781735 15106 (BN 367832280 8320 (BL 367589862 13313) BE) (BL 368836560 26755)) (BN 370064480 7936 (BN 369738616 8963 (BL 369421430 31746) BE) (BL 370216724 13440)))) (BN 374935359 7424 (BN 374177834 12673 (BN 373365298 7552 (BN 372665810 128 (BL 372563717 11265) BE) (BN 374061350 10753 (BL 373625388 6530) BE)) (BN 374654014 257 (BN 374652722 5760 (BL 374460119 10496) BE) (BL 374758673 13953))) (BN 377101808 4224 (BN 376874996 14848 (BN 375317790 30720 (BL 375196705 4736) BE) (BL 377059808 25600)) (BN 378155295 29440 (BN 377913278 29954 (BL 377257063 31874) BE) (BL 378178317 6275)))))) (BN 412996148 1408 (BN 388735930 29056 (BN 383086069 28803 (BN 381545755 11392 (BN 380887303 14720 (BN 380280741 2688 (BL 379558481 29824) BE) (BN 381310994 15872 (BL 381119975 26753) BE)) (BN 382591293 11008 (BN 382349276 11522 (BL 382039789 26624) BE) (BL 383050734 6400))) (BN 385356181 30464 (BN 383994479 3712 (BN 383877721 3968 (BL 383628870 32000) BE) (BL 385115038 4865)) (BN 387090727 27906 (BN 386401565 13312 (BL 385981753 7808) BE) (BL 388462400 15616)))) (BN 395566830 12289 (BN 392898398 768 (BN 390733300 28673 (BN 390461732 6273 (BL 388924514 13697) BE) (BN 392737854 7169 (BL 391725122 9728) BE)) (BN 393826862 31618 (BN 393252345 4867 (BL 393159744 31360) BE) (BL 395369484 28801))) (BN 407265569 12416 (BN 400002828 2049 (BN 398266271 11649 (BL 396161120 28928) BE) (BL 405292663 256)) (BN 411193823 28416 (BN 409969506 15104 (BL 408746029 14849) BE) (BL 412145396 25217))))) (BN 433381966 7168 (BN 426205479 12288 (BN 421414924 9857 (BN 417073936 5120 (BN 414090969 6528 (BL 413182027 15873) BE) (BN 419564455 8449 (BL 419101049 29952) BE)) (BN 423062159 8960 (BN 422012249 28800 (BL 421598463 13824) BE) (BL 423537047 11520))) (BN 428938642 30081 (BN 428278498 27904 (BN 427251759 131 (BL 426990413 5376) BE) (BL 428833983 4353)) (BN 431281777 2176 (BN 430641477 2048 (BL 430166589 10241) BE) (BL 431687757 4227)))) (BN 448341544 30208 (BN 439535174 129 (BN 436429208 12419 (BN 435382928 10240 (BL 433547843 4352) BE) (BN 438070185 1664 (BL 437808839 25344) BE)) (BN 447078367 4864 (BN 444913269 26625 (BL 443971172 4225) BE) (BL 447339713 9856))) (BN 454182797 6145 (BN 452053573 14976 (BN 449677933 25730 (BL 448712623 12417) BE) (BL 454113931 6786)) (BN 464509272 27392 (BN 459942937 2179 (BL 458896657 6144) BE) (BL 472226352 2177)))))))
def F13T9 : BTree NodeData := lf 0x1f0 [0x400030008]
def F13M9 : BST := BN 311584186 770 (BN 285886236 514 (BN 263144985 128 (BN 249570870 512 (BL 248542794 1538) (BL 252978792 258)) (BN 276764627 1283 (BL 268627320 1281) (BL 276950238 1921))) (BN 295761941 1920 (BN 291400165 1664 (BL 286420184 1408) (BL 294116738 1282)) (BN 304927206 1793 (BL 300093676 129) (BL 309363204 1153)))) (BN 340001853 1152 (BN 326434312 896 (BN 319507919 768 (BL 317060125 1536) (BL 321496123 256)) (BN 335565855 1792 (BL 335304509 1280) (BL 339526965 641))) (BN 354273645 1665 (BN 343455219 771 (BL 342408939 0) (BL 344743304 640)) (BN 363543173 385 (BL 355738634 769) (BL 368257033 384))))
def F13L : Nat → Option (BTree NodeData) | 3 => some F13T3 | 4 => some F13T4 | 5 => some F13T5 | 6 => some F13T6 | 7 => some F13T7 | 8 => some F13T8 | 9 => some F13T9 | _ => none
def F13M : Nat → BST | 4 => F13M4 | 5 => F13M5 | 6 => F13M6 | 7 => F13M7 | 8 => F13M8 | 9 => F13M9 | _ => BE
def tRt : Sig := 0xfee8fe80fe808000#64
def RtP : List Row := mkRows [15,23,39,15,15,15,23,51,23,53,23,54,39,51,39,53,39,54,51,53,51,54,53,54,25,26,41,42,25,28,41,44,26,28,42,44,25,26,25,28,26,28,41,42,41,44,42,44,25,41,26,42,28,44,25,26,28,41,42,44,51,53]
def RtN : List Row := mkRows [7,7,7,11,13,14,19,19,21,21,22,22,35,35,37,37,38,38,49,49,50,50,52,52,11,11,11,11,13,13,13,13,14,14,14,14,19,19,21,21,22,22,35,35,37,37,38,38,49,49,50,50,52,52,56,56,56,56,56,56,7,7]
def RtR : List (Nat × Nat) := [(3621760860598171647,3459675944519529439),(1480638800940465663,3462370083285974255),(2968050870726156159,3472543387125796663),(1152921504590069817,1134907174800064568),(3590780620982104002,1152644358973689792),(4479669911282514564,1152917106577108992)]
def RtA : List (List Nat) := [[0,1,2,3,4,5],[0,1,2,3,5,4],[0,2,1,3,4,5],[0,2,1,3,5,4],[1,0,2,3,4,5],[1,0,2,3,5,4],[1,2,0,3,4,5],[1,2,0,3,5,4],[2,0,1,3,4,5],[2,0,1,3,5,4],[2,1,0,3,4,5],[2,1,0,3,5,4]]
def RtC : List CutSpec := [⟨0,1,10,13,0,[0,1,2,3,4,5],0xaaaaaaaaaaaaaaaa#64⟩,⟨0,2,10,13,0,[1,0,2,3,4,5],0xcccccccccccccccc#64⟩,⟨2,0,8,10,0,[1,0,2,3,4,5],0x3333333333333333#64⟩,⟨8,2,7,5,0,[1,0,2,3,4,5],0xcc00cc00cc00cc#64⟩,⟨0,48,7,2,0,[2,3,4,5,0,1],0xffff000000000000#64⟩,⟨32,8,6,7,0,[0,1,2,3,5,4],0xff00ff00#64⟩,⟨4,0,8,10,0,[1,2,0,3,4,5],0xf0f0f0f0f0f0f0f#64⟩,⟨8,18,4,1,0,[3,0,4,1,2,5],0xcc000000cc0000#64⟩,⟨8,17,4,1,0,[0,3,4,1,2,5],0xaa000000aa0000#64⟩,⟨0,16,9,9,0,[0,1,2,3,4,5],0xffff0000ffff0000#64⟩,⟨1,0,8,10,0,[0,1,2,3,4,5],0x5555555555555555#64⟩,⟨16,0,9,12,0,[0,1,2,3,4,5],0xffff0000ffff#64⟩,⟨0,4,10,13,0,[1,2,0,3,4,5],0xf0f0f0f0f0f0f0f0#64⟩,⟨4,48,4,1,0,[3,4,0,5,1,2],0xf0f000000000000#64⟩,⟨2,48,4,1,0,[3,0,4,5,1,2],0x3333000000000000#64⟩,⟨8,0,10,11,0,[0,1,2,3,4,5],0xff00ff00ff00ff#64⟩,⟨0,5,7,2,0,[0,2,1,3,4,5],0xa0a0a0a0a0a0a0a0#64⟩,⟨32,16,6,7,0,[0,1,2,5,3,4],0xffff0000#64⟩,⟨0,3,7,2,0,[0,1,2,3,4,5],0x8888888888888888#64⟩,⟨0,32,9,9,0,[0,1,2,3,5,4],0xffffffff00000000#64⟩,⟨33,0,3,0,0,[0,1,2,3,4,5],0x55555555#64⟩,⟨0,8,7,8,0,[0,1,2,3,4,5],0xff00ff00ff00ff00#64⟩,⟨32,0,9,12,0,[0,1,2,3,5,4],0xffffffff#64⟩,⟨8,1,7,5,0,[0,1,2,3,4,5],0xaa00aa00aa00aa#64⟩,⟨1,48,4,1,0,[0,3,4,5,1,2],0x5555000000000000#64⟩,⟨0,34,5,3,0,[1,0,2,3,5,4],0xcccccccc00000000#64⟩,⟨37,0,2,0,0,[0,1,2,3,4,5],0x5050505#64⟩,⟨2,17,2,0,0,[0,1,2,3,4,5],0x2222000022220000#64⟩,⟨0,6,7,2,0,[2,0,1,3,4,5],0xc0c0c0c0c0c0c0c0#64⟩,⟨8,4,7,5,0,[1,2,0,3,4,5],0xf000f000f000f0#64⟩,⟨1,4,5,4,0,[0,2,1,3,4,5],0x5050505050505050#64⟩,⟨8,16,7,5,0,[1,2,4,0,3,5],0xff000000ff0000#64⟩,⟨8,32,7,5,0,[1,2,4,0,5,3],0xff00ff00000000#64⟩,⟨4,34,2,0,0,[0,1,2,3,4,5],0xc0c0c0c00000000#64⟩,⟨18,0,3,0,0,[0,1,2,3,4,5],0x333300003333#64⟩,⟨16,32,6,7,0,[0,1,2,5,3,4],0xffff00000000#64⟩,⟨32,6,4,1,0,[3,0,1,4,5,2],0xc0c0c0c0#64⟩,⟨0,33,5,3,0,[0,1,2,3,5,4],0xaaaaaaaa00000000#64⟩,⟨1,20,2,0,0,[0,1,2,3,4,5],0x5050000050500000#64⟩,⟨2,20,2,0,0,[0,1,2,3,4,5],0x3030000030300000#64⟩,⟨4,8,3,0,0,[0,1,2,3,4,5],0xf000f000f000f00#64⟩,⟨4,32,5,4,0,[4,5,0,3,2,1],0xf0f0f0f00000000#64⟩,⟨4,16,5,4,0,[4,5,0,3,1,2],0xf0f00000f0f0000#64⟩,⟨0,20,5,3,0,[1,2,0,3,4,5],0xf0f00000f0f00000#64⟩,⟨5,8,2,0,0,[0,1,2,3,4,5],0x500050005000500#64⟩,⟨16,8,6,7,0,[0,1,2,3,4,5],0xff000000ff00#64⟩,⟨17,0,3,0,0,[0,1,2,3,4,5],0x555500005555#64⟩,⟨8,34,4,1,0,[3,0,4,1,5,2],0xcc00cc00000000#64⟩,⟨0,18,5,3,0,[1,0,2,3,4,5],0xcccc0000cccc0000#64⟩,⟨1,6,4,1,0,[0,1,2,3,4,5],0x4040404040404040#64⟩,⟨0,36,5,3,0,[1,2,0,3,5,4],0xf0f0f0f000000000#64⟩,⟨1,2,5,4,0,[0,1,2,3,4,5],0x4444444444444444#64⟩,⟨16,5,4,1,0,[0,3,1,4,2,5],0xa0a00000a0a0#64⟩,⟨16,2,5,6,0,[1,0,2,3,4,5],0xcccc0000cccc#64⟩,⟨38,0,2,0,0,[0,1,2,3,4,5],0x3030303#64⟩,⟨0,49,2,0,0,[0,1,2,3,4,5],0xaaaa000000000000#64⟩,⟨32,2,5,6,0,[1,0,2,3,5,4],0xcccccccc#64⟩,⟨0,17,5,3,0,[0,1,2,3,4,5],0xaaaa0000aaaa0000#64⟩,⟨0,19,2,0,0,[0,1,2,3,4,5],0x8888000088880000#64⟩,⟨2,32,5,4,0,[4,0,5,3,2,1],0x3333333300000000#64⟩,⟨6,0,3,0,0,[0,1,2,3,4,5],0x303030303030303#64⟩,⟨34,0,3,0,0,[0,1,2,3,4,5],0x33333333#64⟩,⟨2,16,5,4,0,[4,0,5,3,1,2],0x3333000033330000#64⟩,⟨0,14,2,0,0,[0,1,2,3,4,5],0xc000c000c000c000#64⟩,⟨6,8,2,0,0,[0,1,2,3,4,5],0x300030003000300#64⟩,⟨32,3,4,1,0,[0,1,3,4,5,2],0x88888888#64⟩,⟨16,4,5,6,0,[1,2,0,3,4,5],0xf0f00000f0f0#64⟩,⟨1,16,5,4,0,[0,4,5,3,1,2],0x5555000055550000#64⟩,⟨2,4,5,4,0,[2,0,1,3,4,5],0x3030303030303030#64⟩,⟨8,3,4,1,0,[0,1,3,2,4,5],0x88008800880088#64⟩,⟨4,3,4,1,0,[0,1,2,3,4,5],0x808080808080808#64⟩,⟨21,0,2,0,0,[0,1,2,3,4,5],0x50500000505#64⟩,⟨35,0,2,0,0,[0,1,2,3,4,5],0x11111111#64⟩,⟨1,36,2,0,0,[0,1,2,3,4,5],0x5050505000000000#64⟩,⟨1,32,5,4,0,[0,4,5,3,2,1],0x5555555500000000#64⟩,⟨8,5,4,1,0,[0,3,1,2,4,5],0xa000a000a000a0#64⟩,⟨32,5,4,1,0,[0,3,1,4,5,2],0xa0a0a0a0#64⟩,⟨16,3,4,1,0,[0,1,3,4,2,5],0x888800008888#64⟩,⟨0,12,3,0,0,[0,1,2,3,4,5],0xf000f000f000f000#64⟩,⟨16,6,4,1,0,[3,0,1,4,2,5],0xc0c00000c0c0#64⟩,⟨0,38,2,0,0,[0,1,2,3,4,5],0xc0c0c0c000000000#64⟩,⟨0,21,2,0,0,[0,1,2,3,4,5],0xa0a00000a0a00000#64⟩,⟨2,5,4,1,0,[0,1,2,3,4,5],0x2020202020202020#64⟩,⟨4,2,5,4,0,[2,0,1,3,4,5],0xc0c0c0c0c0c0c0c#64⟩,⟨0,10,3,0,0,[0,1,2,3,4,5],0xcc00cc00cc00cc00#64⟩,⟨32,4,5,6,0,[1,2,0,3,5,4],0xf0f0f0f0#64⟩,⟨8,36,4,1,0,[3,4,0,1,5,2],0xf000f000000000#64⟩,⟨16,1,5,6,0,[0,1,2,3,4,5],0xaaaa0000aaaa#64⟩,⟨0,11,2,0,0,[0,1,2,3,4,5],0x8800880088008800#64⟩,⟨0,13,2,0,0,[0,1,2,3,4,5],0xa000a000a000a000#64⟩,⟨0,35,2,0,0,[0,1,2,3,4,5],0x8888888800000000#64⟩]
def RtT5 : BTree NodeData := nd (lf2 0xe1d541503016057 0x1b6c8691 [0x5f027e01]) (nd (lf2 0xe1d541503012077 0x1b6a8a91 [0xe047e010e03]) (lf2 0xa03765505415067 0x1b3c8291 [0x67037005]))
def RtT6_0 := nd (nd (nd (nd (lf2 0x58c210801009b86 0x2a554 [0x839070606,0xf0a0009]) (nd (lf2 0x15021080100bc86 0xe8d54 [0x270c39073c0b,0x380d3802070a]) (lf2 0x150210801009c86 0xea554 [0x3a023c0b010e,0x30605060606,0x380d]))) (nd (nd (lf2 0x152310801009c46 0xea554 [0x3c0b3d0d020f]) (lf2 0x152310801009cc6 0xea554 [0x3b100306020f,0x38113c0b3d0d])) (nd (lf2 0x55163080100cba6 0xa8898 [0xd22061d07]) (lf2 0x152628c01009866 0xea554 [0x380b3e023a07,0x212])))) (nd (nd (lf2 0x152728c01009466 0xea554 [0x380b3e023907]) (nd (lf2 0x152628c010098e6 0xea554 [0x3e020506020e,0x3d10]) (lf2 0x152728c010094e6 0xea554 [0x3e020106010e,0x380b]))) (nd (nd (lf2 0x9c851100100a786 0xea132 [0x10c2507]) (lf2 0x61c51100100a746 0x68c92 [0x38133a020009,0x306])) (nd (lf2 0x550540c8100cc66 0xa8398 [0x3d103e021e0b,0x3d0d0305]) (lf2 0x550540c81008476 0x69f98 [0x1123e023d0d,0x3e01]))))) (nd (nd (nd (lf2 0x550548c8100cc66 0xa8398 [0x3e021e0b010e]) (nd (lf2 0x550548c8100cc36 0xa8b98 [0x3053e021d07,0x1e0b3e01]) (lf2 0x550548c8100cce6 0xa8398 [0x3e022106010e,0x3d10]))) (nd (nd (lf2 0x550548c8100ccb6 0xa8b98 [0x3c101d072106,0x3c0b3e021d10,0x1051e0b]) (lf2 0x61573108100c366 0x24386 [0x2e01390c1714,0x2e133d0d])) (nd (lf2 0x615731081008376 0xaa786 [0x390c3d0d0015,0x143e02]) (lf2 0xe1973108100e176 0xe1753 [0x116])))) (nd (nd (lf2 0xe1973108100a3e6 0x28185 [0x390c36100916,0x143617]) (nd (lf2 0x15132188100a8b6 0x2a154 [0x38073b10270c,0x240a3e023e01]) (lf2 0x1513218810098b6 0xea554 [0x390d]))) (nd (nd (lf2 0x550541881008876 0x68f98 [0x3e0203163c07,0x3e01]) (lf2 0x20143988100e846 0xd4c81 [0x2c03340b3c07,0x1f17])) (nd (lf2 0x550549881008876 0x68f98 [0x3e013e023c07,0x316]) (lf2 0x1c87050c100d066 0x65b53 [0x1a0b21161613])))))
def RtT6_1 := nd (nd (nd (nd (lf2 0x21d5458c100c3b6 0x64892 [0xf0d]) (nd (lf2 0x21d5458c100c3b6 0xe4a92 [0xf0d]) (lf2 0xe1d54150100a4e6 0xa8a90 [0x3e020f07200f,0x1063006]))) (nd (nd (lf2 0xe1d54150100e4b6 0x4ca92 [0xf0d]) (lf2 0xe1d54150100a476 0x28993 [0x1123e020f07,0xe0b3e01])) (nd (lf2 0xe1d54150100a4f6 0x28993 [0xe0b0e130106,0x3e023e100112,0x20050f070e03]) (lf2 0xe1d54150100a476 0xa8a93 [0x21053e020f07,0x3e0d3e0b3e01,0xe0b])))) (nd (nd (lf2 0x60c72550100c746 0x24490 [0x110701062e0b,0x3e0d2e023d0c,0x2107]) (nd (lf2 0x60c72550100e076 0x15096 [0x21161d0c2e0b,0x3f0d190a3e02,0x8052007]) (lf2 0x153219843009856 0xea554 [0x3902]))) (nd (nd (lf2 0xe1d54150300e456 0xc8691 [0xf02]) (lf2 0xe1d54150300a476 0xa8a91 [0x1f0d3e100f07,0x120e033e01])) (nd (lf2 0x152729863009476 0xea554 [0x390738183c0b,0x10501123b0d]) (lf2 0xe1d54152300a466 0xa8690 [0xe0b21050f03,0xf07]))))) (nd (nd (nd (lf2 0xe1d54152300e456 0xc8691 [0xf02]) (nd (lf2 0xe1d54152300a476 0xa8a91 [0xf0321050f07,0xe180e0b3e01,0xf023e10]) (lf2 0xe1d54152300a4e6 0xa8690 [0x3e1030060f03,0xf07200e2105]))) (nd (nd (lf2 0xe1d54152300e4d6 0xc8691 [0xf02]) (lf2 0xe1d54152300a4f6 0xa8a91 [0x20190e183006,0x3e10])) (nd (lf2 0x20976144400d076 0x15193 [0x106]) (lf2 0x151761444009076 0x68e98 [0x7163e01201a,0x1b3f0d000e])))) (nd (nd (nd (lf2 0x20963944400c356 0xa4787 [0x503]) (lf2 0x20963944400e356 0xa4787 [0x3a0c001c0007])) (nd (lf2 0x20963944400e276 0x65387 [0x73d02001c]) (lf2 0xa087158c400a336 0x29d52 [0xf0d3e010f14,0x3]))) (nd (nd (lf2 0xa0376550540b066 0x68f10 [0x701]) (lf2 0xa0376550540d0e6 0xc8291 [0x1f0d1f012703,0x180620063005])) (nd (lf2 0xa0376550540d0e6 0x4c291 [0x70b1f012703,0x100e27073005,0x710]) (lf2 0xa0f76550540d066 0xc4290 [0xf01])))))
def RtT6 : BTree NodeData := nd RtT6_0 RtT6_1
def RtM6 : BST := BN 300606986 128 (BL 290507271 384) BE
def RtT7_0 := nd (nd (nd (nd (nd (lf2 0x90c210801005d05 0x195 [0x7141a02070a,0x1c01190d]) (lf2 0xd0c210801007e85 0x354 [0x19070f171c0b,0x1802070a1710,0x813180d070c,0x81d0811])) (nd (lf2 0x58c210801007b85 0x154 [0xf0a19070606,0x140b]) (lf2 0x150210801007c85 0x154 [0x70a19071c0b,0x6061a02070c,0x180d03060506]))) (nd (nd (lf2 0x550210801005f85 0x393 [0x1907070a1c0b,0x51606160714,0x180d18020316]) (lf2 0x950210801005f05 0x193 [0x1907070c1c0b,0x180d1a020714])) (nd (lf2 0x950210801005f85 0x193 [0x19070f101c0b,0x616070c0714,0x180203160516,0x180d]) (lf2 0x950210801007c85 0x354 [0x70c19071c0b,0x6061a020717,0x180d03060506])))) (nd (nd (nd (lf2 0x152310801007c45 0x154 [0x1c0b1d0d1a03,0x70c070a]) (lf2 0x952310801007c45 0x354 [0x1c0b1d0d1a03,0x717070c])) (nd (lf2 0x8ca310801007f05 0x154 [0xf0a1c0b0306,0x10111507101e,0x11e0204]) (lf2 0x10a310801005f05 0x193 [0x70c1c0b0316,0x717]))) (nd (nd (lf2 0x152310801007cc5 0x154 [0x70a1c0b0306,0x18111d0d]) (lf2 0x552310801005f45 0x393 [0x1d0d1c0b0316,0x1717170c0b10])) (nd (lf2 0x952310801005f45 0x193 [0x70c1c0b0316,0xb1017171d0d,0x1811]) (nd (lf2 0x952310801007cc5 0x354 [0x70c1c0b0306,0x18111d0d]) (lf2 0x60c410801006f85 0x92 [0x130c1c0b0306,0xd07])))))) (nd (nd (nd (nd (lf2 0x551630801004be5 0x98 [0x1e021d0d0206,0x8170c180b,0x9]) (lf2 0x550540801005ce5 0x393 [0x1e021d0d1c0b,0x30a130c])) (nd (lf2 0x550540801004ce5 0x398 [0x1e021d0d0019,0x1060206]) (lf2 0x152628c01007865 0x154 [0x180b1e021a07,0x70c070a]))) (nd (nd (lf2 0x952628c01007865 0x354 [0x180b1e021a07,0x717070c]) (lf2 0x152728c01007465 0x154 [0x70c070a1907,0x1c01])) (nd (lf2 0x952728c01007465 0x354 [0x70c1e021907,0x1c010717]) (lf2 0x550548c01005c65 0x92 [0x130c1c0b0707,0x1e02])))) (nd (nd (nd (lf2 0x550548c01004c65 0x398 [0x1e020019]) (lf2 0x98a318c01007b45 0x154 [0x16070f0a0906,0x8040818])) (nd (lf2 0x9ca318c01007745 0x154 [0xf0a01061507,0x804041f140b]) (lf2 0x552318c01005f45 0x92 [0x1c0b07071106,0x18021810070a,0x13]))) (nd (nd (lf2 0x152628c010078e5 0x154 [0x70a1d100506,0x1a071e02]) (lf2 0x552628c01005b65 0x393 [0x1e021a070516,0x1717070a0d10,0x200214])) (nd (lf2 0x952628c01005b65 0x193 [0x70c1a070516,0x210d101e02]) (nd (lf2 0x952628c010078e5 0x354 [0x70c1d100506,0x1a071e02]) (lf2 0x152728c010074e5 0x154 [0x70a19070106,0x180b1e02]))))))
def RtT7_1 := nd (nd (nd (nd (nd (lf2 0x552728c01005765 0x393 [0x1e0219070116,0x170c180b0d10,0x1717]) (lf2 0x952728c01005765 0x193 [0x70c1e021907,0x70a0d10180b])) (nd (lf2 0x952728c010074e5 0x354 [0x70c19070106,0x180b1e02]) (lf2 0x550548c01005ce5 0x92 [0x1d1007071106,0x1c011e02]))) (nd (nd (lf2 0x550548c01004ce5 0x398 [0x1d101e020019,0x106]) (lf2 0xc8511001006745 0x187 [0x170d17100c0b,0x1b171d0a1d0c,0x1a])) (nd (lf2 0x8c8511001006745 0x187 [0x170d0c0b0022,0x81a1d0a1d0c,0x1b1717100107]) (lf2 0x8c85110010067c5 0x187 [0x1b140c0b0009,0x1b17170d0116])))) (nd (nd (nd (lf2 0x9c8511001007785 0x132 [0x70d]) (lf2 0x61c5110010067c5 0x92 [0x1a00230009,0xf07])) (nd (lf2 0x94a321001005725 0x197 [0x13071e020524,0x1c0b1c131c01]) (lf2 0x94a3210010057a5 0x197 [0x25040f]))) (nd (nd (lf2 0x209531001006765 0x173 [0x1e0201161307,0xd0c13140c0b]) (lf2 0x550540c81004c75 0x398 [0x1e021d0d1d10,0x1c0b03051e01,0x1e0b1c030212,0x1121e13])) (nd (lf2 0xd52540c81006475 0x187 [0x1211d0d1317,0x1e011e02]) (nd (lf2 0x550548c81004c75 0x398 [0x1e0b1e02010e,0x1c0b1e011d0d,0x2121e131c1e,0x1c071c030112,0x1d10]) (lf2 0x61e548c81006535 0x252 [0xb141e02011e,0x1e011b0a1b0c])))))) (nd (nd (nd (nd (lf2 0x550548c81004cf5 0x398 [0x1e021d0d0106,0x3051e011d10,0x2121c131c0b,0x1121e0b1c07]) (lf2 0x201731081007745 0x81 [0x190c160b0106,0xe030e021d0d,0x1601])) (nd (lf2 0x201731081006765 0x85 [0x1e020f17160b,0x190c1d0d]) (lf2 0x201731081006765 0x285 [0x1d0d160b0f17,0x26190c1e02]))) (nd (nd (lf2 0x215731081006375 0x86 [0x1e020e0b1717,0xe14190c1d0d,0xe10]) (lf2 0x615731081006375 0x386 [0x190c0e131714,0x150a1d0d])) (nd (lf2 0xa15731081006575 0x385 [0x1d0d1e020106,0x160b1e01190c]) (lf2 0xa15731081006375 0x86 [0x1d0d0e0b1717,0xe10190c1e02,0xe14])))) (nd (nd (nd (lf2 0xe15731081006375 0x386 [0x1d0d17140e13,0x150a0e17190c]) (lf2 0x219731081007275 0x354 [0x106])) (nd (lf2 0x219731081007375 0x85 [0xd0d16140f17,0x100c16100907,0xf14]) (lf2 0xe19731081007275 0x354 [0x1d0d0f171613,0x160b]))) (nd (nd (lf2 0xe19731081007375 0x85 [0x9070f140027,0x160b0617]) (lf2 0xe19731081007375 0x385 [0xf14090c0027,0x160b1617])) (nd (lf2 0x2017310810067c5 0x81 [0x190c160b0106,0x1160e021d0d,0xe03]) (nd (lf2 0x219731081007375 0x53 [0x60b06130f10,0x9070d0d0603,0x614090c100c,0x92409160617]) (lf2 0x219731081007175 0x353 [0x116]))))))
def RtT7_2 := nd (nd (nd (nd (nd (lf2 0x219731081007375 0x353 [0x116]) (lf2 0x2197310810063f5 0x85 [0xf10190c0f17,0x1603160b1614,0x1610])) (nd (lf2 0x2197310810063f5 0x285 [0x116]) (lf2 0xe19731081007365 0x230 [0x1e021d0d0906,0xe0b190c]))) (nd (nd (lf2 0xe19731081007375 0x53 [0xf1006130027,0x100c09070028,0x100b0916090c,0x924]) (lf2 0xe19731081007375 0x153 [0x116])) (nd (lf2 0xe19731081007375 0x253 [0x100706100906,0x100b]) (lf2 0xe19731081007175 0x353 [0x116])))) (nd (nd (nd (lf2 0xe19731081007375 0x353 [0x116]) (lf2 0xe197310810063f5 0x185 [0x116])) (nd (lf2 0xe197310810063f5 0x385 [0x16100f140906,0x190c]) (lf2 0xe1d6390810062f5 0x354 [0x50a]))) (nd (nd (lf2 0x1513218810078b5 0x154 [0x190d]) (lf2 0x551321881004bb5 0x98 [0x17171807070a,0x1e0114141b10,0x1e02])) (nd (lf2 0x9513218810078b5 0x354 [0x190d]) (nd (lf2 0x951321881004bb5 0x298 [0x18071717070c,0x1e021e011b10,0x1414]) (lf2 0xe09431881007835 0x353 [0x150d])))))) (nd (nd (nd (nd (lf2 0xd4d431881007075 0x387 [0x1e011e020029]) (lf2 0xd4d431881007875 0x294 [0xb0c03161c07,0x121e021e01])) (nd (lf2 0xd4d431881006975 0x298 [0xb0c1c070316,0x180a1e021e01]) (lf2 0x5534318810052f5 0x397 [0x1e011b10042a,0x130c1e02]))) (nd (nd (lf2 0x5505418810058f5 0x393 [0x130c0f101c07,0x3161e021e01,0x50416030a,0x20]) (lf2 0x5505418810048f5 0x398 [0x1c031c0b000e,0x31600061f10])) (nd (lf2 0x60e541881006875 0x354 [0x1e020b171c07,0x2110161e01,0x316]) (lf2 0x60e5418810068f5 0x354 [0x17100b171c07,0x3161e021e01,0x21030c1016])))) (nd (nd (nd (lf2 0x201439881006ac5 0x81 [0x140b1b10000e,0xc03]) (lf2 0x201439881007865 0x353 [0x130a1e021c07,0xf17140b])) (nd (lf2 0xd4d439881007075 0x387 [0x1e020316082b,0x1e01]) (lf2 0xe0d439881006275 0x387 [0x1e02130c002b,0xc1417171e01]))) (nd (nd (lf2 0xd4d439881007875 0x294 [0xb0c03161c07,0x121e021e01]) (lf2 0xd4d439881006175 0x387 [0x1e020b0a081f,0x211717])) (nd (lf2 0xd4d439881006975 0x298 [0x1e011c070316,0x210b0c1e02]) (nd (lf2 0x5534398810052f5 0x397 [0x1b10041f042a,0x1e02130c]) (lf2 0x5505498810058f5 0x393 [0x1e010f101c07,0x416130c1e02,0x20030a0316]))))))
def RtT7_3 := nd (nd (nd (nd (nd (lf2 0x5505498810050f5 0x397 [0x1e02041f000e,0x130c]) (lf2 0x5505498810048f5 0x398 [0x1e011e02000e,0x31600061c10])) (nd (lf2 0x60e549881006875 0x354 [0x1e020b171c07,0x2110161e01,0x316]) (lf2 0x60e5498810068f5 0x354 [0x17100b171c07,0x3161e021e01,0x21030c1016]))) (nd (nd (lf2 0x1c47050c1007445 0x353 [0x160301161a0b,0x1a02]) (lf2 0x1c47050c1007645 0x353 [0x16030f171a0b,0x1a02000e0105])) (nd (lf2 0x1c87050c1007465 0x353 [0x1e0201161a0b,0x102c1607]) (lf2 0x1c87050c10052e5 0x196 [0x1d10001b0613,0x6170a0b])))) (nd (nd (nd (lf2 0xd4c7250c1007075 0x76 [0x1e021b0d002d]) (lf2 0x1d87250c10072b5 0x52 [0x106])) (nd (lf2 0x1d87250c10072b5 0x352 [0xb0d]) (lf2 0x1db5350c1007075 0x272 [0x50a]))) (nd (nd (lf2 0xdd77350c1006475 0x285 [0x317]) (lf2 0x1db7350c1007275 0x52 [0x106])) (nd (lf2 0x1c87650c1007275 0x373 [0x506170d1a0b,0x12070d0c1e02,0xf171a141714,0xd10]) (nd (lf2 0x9c87650c1005275 0x193 [0x7071e021a0b,0x52007171f0d,0x516]) (lf2 0x9d47650c10052f5 0x292 [0x1d1007171a0b,0x180c1e02])))))) (nd (nd (nd (nd (lf2 0x9d47650c1005275 0x193 [0x1e0207171a0b,0x1a0705200516]) (lf2 0x14b7650c10052f5 0x297 [0x7171a13002d])) (nd (lf2 0x1cb7650c1007275 0x373 [0x506170d1a13,0x17140d0c1207,0xf171a14]) (lf2 0xd487250c1005735 0x193 [0x1e02190a1107,0x1e0101160717,0x180b]))) (nd (nd (lf2 0x21d5458c1006375 0x32 [0xf0d00060f10,0x1e021e010b0a,0xb141b0c]) (lf2 0x21d5458c10063f5 0x92 [0x102e0f101006,0x1e020c0b1e01,0x1b0a00070c03,0xd])) (nd (lf2 0x21d5458c10063f5 0x292 [0x1e021e011006,0xc030c0b1b0a,0xd102e0007]) (nd (lf2 0x55054d8c1005875 0x92 [0x130c1c0b0707,0x1e02]) (lf2 0x55054d8c1004875 0x398 [0x1e021c0b000f,0x1c071e01]))))) (nd (nd (nd (lf2 0x55032d8c1004b75 0x398 [0x1b0d03201006,0x1e021e01]) (lf2 0x20954d8c1006b35 0x332 [0xd10])) (nd (lf2 0x209541501004c75 0x193 [0x1e0203070106,0x2031e01020b]) (lf2 0xe1d5415010064e5 0x290 [0x1e020e0b000f,0x1f0d01051f10,0x1061006000e]))) (nd (nd (lf2 0xe1d5415010064f5 0x292 [0xf01120019,0x1e011e020f0d,0x10061e100105,0xe1301060f10]) (lf2 0xe1d541501004475 0x193 [0x1e0101161e02,0x1e131e0b1f0d])) (nd (lf2 0xe1d541501006475 0x193 [0x1e0201120019,0xf1e010105,0x1e0d000e]) (nd (lf2 0xe1d5415010064f5 0x193 [0x1e0201060019,0x10501200112,0xf1e011f0d,0xe13000e]) (lf2 0xe1d541501006475 0x293 [0x1e020f100019,0xe1e01000f,0x1161e0d]))))))
def RtT7_4 := nd (nd (nd (nd (nd (lf2 0x60c725501006765 0x90 [0x11071e020106,0x190a0e0b]) (lf2 0x60c725501006375 0x96 [0x1914190a0e0b,0x1161f0d1e02,0xc170c0c0007])) (nd (lf2 0x5d8521043006375 0x398 [0x1b0d1d02002f,0x90c0a100b17]) (lf2 0x61c521043006475 0x54 [0x50c]))) (nd (nd (lf2 0x5da521043007075 0x54 [0x50c]) (lf2 0x5da521043006375 0x398 [0x301b0d0019])) (nd (lf2 0x61e521043006335 0x262 [0x207]) (lf2 0x54a621043005335 0x397 [0x1e011d020d0c,0x17171207])))) (nd (nd (nd (lf2 0xa0b541043006275 0x176 [0x131713070031]) (lf2 0x109761043007275 0x85 [0x150c0f170031,0x5050032170d,0x707])) (nd (lf2 0x109761043007275 0x385 [0x124]) (lf2 0x209761043006375 0x85 [0x190031002f,0x7170d]))) (nd (nd (lf2 0x151761043005275 0x292 [0x7171d020707,0x51d1e01]) (lf2 0x215761043005375 0x292 [0x1e0107071031,0x717])) (nd (lf2 0xe15761043005375 0x292 [0x1e0107071031,0x330714]) (nd (lf2 0x152729043006275 0x186 [0x1e011d021105,0x1f0d1717]) (lf2 0x153219843007855 0x154 [0x1902])))))) (nd (nd (nd (nd (lf2 0x953219843007855 0x354 [0x1902]) (lf2 0x550549843005875 0x92 [0x1e01130c0707,0x1c100403])) (nd (lf2 0x550549843004875 0x398 [0x1c071e01000f]) (lf2 0x205541503004875 0x196 [0x1e01190c001a,0x207]))) (nd (nd (lf2 0xe1d541503006475 0x291 [0x1e011e100112,0xe031f0d0f02,0xe0105]) (lf2 0xe1d541503004075 0x196 [0x1f0200121e01,0x1f0d])) (nd (lf2 0x5d8521063006365 0x280 [0xb171b0d1d02,0x1d0c0a0b]) (lf2 0x61c521063006475 0x54 [0x50c])))) (nd (nd (nd (lf2 0x61e621063006275 0x54 [0x50c]) (lf2 0x550549863005875 0x92 [0x1e011c030707,0x33130c])) (nd (lf2 0x550549863004875 0x398 [0x1c071e01000f]) (lf2 0x152729863007475 0x154 [0x190718181c0b,0x1903070c070a,0x1902]))) (nd (nd (lf2 0x952729863007475 0x354 [0x190718181c0b,0x1b0d0717070c]) (lf2 0x550549863005c75 0x92 [0x7071c0b1c18,0x4341d02130c])) (nd (lf2 0x550549863004c75 0x398 [0x1d021c180019,0x1f0d]) (nd (lf2 0x205541523006c55 0x161 [0x702]) (lf2 0xe1d541523006465 0x290 [0x1f0201050e0b,0x1f0d]))))))
def RtT7_5 := nd (nd (nd (nd (nd (lf2 0xe1d541523006475 0x291 [0xf0201120019,0xe1f0d1e01]) (lf2 0x584715523005715 0x92 [0x190a011a160b,0x190319140707])) (nd (lf2 0x584715523005755 0x92 [0x11a0707160b,0xf0d190a]) (lf2 0x61c519023006765 0x232 [0xf0d1112010e,0x1e0c181b02]))) (nd (nd (lf2 0x61c519023006665 0x343 [0x1b0201120035]) (lf2 0xc86719023007745 0x353 [0x1302])) (nd (lf2 0xd4e719023005765 0x292 [0x190a19030707,0x180b0717]) (lf2 0x61c521063006675 0x343 [0x50c])))) (nd (nd (nd (lf2 0x61c5210630064f5 0x54 [0x50c]) (lf2 0x61e621063006275 0x343 [0x50c])) (nd (lf2 0x553439863005a75 0x92 [0x130c1c030707,0x43307141e01]) (lf2 0x5505498630058f5 0x92 [0x1c0307071e10,0x4161e01130c,0x33]))) (nd (nd (lf2 0x5505498630050f5 0x397 [0x1e1010060434,0x407]) (lf2 0x5505498630048f5 0x398 [0x61e01000f,0x1c071f0d1e10])) (nd (lf2 0xe1d5415230064e5 0x290 [0x1050e0b1006,0x1f0d1f021e10,0xe000f]) (nd (lf2 0xe1d5415230064f5 0x291 [0x11210060019,0x1f0d0f021e10,0xe18000e1e01]) (lf2 0xd4e729044007075 0x163 [0x1d0219070616,0x1e01])))))) (nd (nd (nd (nd (lf2 0xd4e729044007275 0x163 [0x1e0119071717,0x6161d02]) (lf2 0x2096390440052f5 0x197 [0x1e0100361206,0x12161f0d])) (nd (lf2 0x4ca6214440053b5 0x397 [0x1e011d020506,0x1a0c1207]) (lf2 0x61e621444006335 0x232 [0x207]))) (nd (nd (lf2 0x5d94314440062d5 0x81 [0x103]) (lf2 0x209761444005375 0x193 [0x106101a0009,0x1e0c1f0d1d02])) (nd (lf2 0x2097614440070f5 0x54 [0x1a00230009,0xe17071e01]) (lf2 0x1517614440050f5 0x193 [0x1d0204050009,0x1807])))) (nd (nd (nd (lf2 0x1517614440050f5 0x298 [0x1d0204050009,0xe001b]) (lf2 0xd4e729444007175 0x163 [0xe0c19070616,0x331d021e01])) (nd (lf2 0x58e729444007335 0x392 [0xb0d]) (lf2 0x58e729444007175 0x95 [0x1e0119070406,0x19141d02060b,0x60c]))) (nd (nd (lf2 0x58e729444006375 0x398 [0x1d021e011914,0x160c0907]) (lf2 0x61a7294440063a5 0x20 [0x107])) (nd (lf2 0x61a7294440060f5 0x54 [0x60c]) (nd (lf2 0x209639444006975 0x85 [0x8241e010037]) (lf2 0x209639444006375 0x387 [0x1a0c1d020d14,0x38170d1e01,0x160a0007]))))))
def RtT7_6 := nd (nd (nd (nd (nd (lf2 0x209639444005375 0x197 [0x1e011a0c1006,0x40a0d141d02,0x539]) (lf2 0xc9639444005375 0x197 [0x1a0c10060521,0x40a1e011d02])) (nd (lf2 0x209439844006ab5 0x352 [0x70d]) (lf2 0x209439844006875 0x353 [0x1e0113071c03,0xf17]))) (nd (nd (lf2 0xc9739844005175 0x195 [0x1e011c0c0714,0x1f02170d]) (lf2 0xc847150c4007455 0x353 [0x1302])) (nd (lf2 0xc847150c4007655 0x353 [0x1302]) (lf2 0xd447150c40056d5 0x292 [0x1c0c07170707,0x1d1011031e01,0x61d])))) (nd (nd (nd (lf2 0x6187154c4006075 0x54 [0x60c]) (lf2 0x6187154c40063c5 0x10 [0x903001a102e,0x1d101007])) (nd (lf2 0xc847158c4007a55 0x184 [0x170d1702083a,0x171700370303,0x80c0f17]) (lf2 0xc847158c4007355 0x75 [0x1302]))) (nd (nd (lf2 0xc847158c4007355 0x275 [0x1302]) (lf2 0xc847158c4005b55 0x198 [0x1806170d003b,0x170200370303])) (nd (lf2 0x1c87158c4007355 0x191 [0xb02]) (nd (lf2 0x1c87158c4007355 0x291 [0x10060b030707,0x1b141c0c1e01,0x3c]) (lf2 0x1c87158c4007275 0x184 [0x1e011006003d,0x170d0b030e0a,0x1714])))))) (nd (nd (nd (nd (lf2 0xa087158c4006b35 0x152 [0x70d]) (lf2 0xa087158c4006b35 0x372 [0x70d])) (nd (lf2 0xa087158c4006375 0x75 [0x1e0113070f17,0x170d1c0c1303,0x330f02]) (lf2 0xa087158c4006375 0x275 [0x1e0113070f17,0x13031c0c170d,0xf02]))) (nd (nd (lf2 0xa087158c4006a75 0x184 [0x83a170d020e]) (lf2 0x6107158c4007275 0x75 [0x160a1e010037,0xf0213030f17])) (nd (lf2 0x1d47158c4005375 0x292 [0x1e010717003d,0x7071c0c]) (lf2 0x1d47158c4007175 0x185 [0x1e0104240037,0xb03])))) (nd (nd (nd (lf2 0x9d47158c4005375 0x292 [0x717003a003d,0x707]) (lf2 0x9d47158c4005375 0x198 [0x3a0037])) (nd (lf2 0x6147158c4005b75 0x92 [0x1c0c0f0d0707,0x205003b003e,0x71d1f020714]) (lf2 0x2057558c4006b55 0x292 [0x101603031205,0x1c0c0f0d1e01,0x1a]))) (nd (nd (lf2 0x2057558c4006b55 0x321 [0x702]) (lf2 0xa067558c4006b55 0x321 [0x702])) (nd (lf2 0x1c83158c4006975 0x185 [0x1b020b140b10,0x1c0c1f0d1016,0x1e01]) (nd (lf2 0xa083158c4006b35 0x152 [0x1110]) (lf2 0xa083158c4006b35 0x372 [0x70d]))))))
def RtT7_7 := nd (nd (nd (nd (nd (lf2 0xc847158c4005bd5 0x198 [0x7021816]) (lf2 0x1c87158c40073d5 0x191 [0xb02])) (nd (lf2 0x1c87158c40073d5 0x291 [0x1f0d10160707,0x1b02003f]) (lf2 0xa045358c4006b55 0x292 [0x1110]))) (nd (nd (lf2 0xa045358c4006b55 0x321 [0x1110]) (lf2 0x18b101814307865 0x353 [0x1901])) (nd (lf2 0x18b101814307a65 0x353 [0x1901]) (lf2 0x18b101814306ae5 0x187 [0x90b14060040,0x31100311e10])))) (nd (nd (nd (lf2 0xa0b101814306c65 0x353 [0x1101]) (lf2 0xd4f101814306c65 0x187 [0x1b010040])) (nd (lf2 0xd4f101814306e65 0x187 [0x1b0217171405,0x1b1b010b07]) (lf2 0x197101814306ae5 0x187 [0x1b0217171405,0x1e100b07]))) (nd (nd (lf2 0x600611814305ae5 0x92 [0x1303000e0040,0x311]) (lf2 0x600611814307865 0x353 [0x1501])) (nd (lf2 0xa00611814305ae5 0x292 [0x1303000e0040]) (nd (lf2 0xa00611814307865 0x353 [0x130113030040]) (lf2 0x9c8611814307075 0x353 [0x150b08161507,0x151d1f01])))))) (nd (nd (nd (nd (lf2 0x61c611814307ac5 0x10 [0x50b]) (lf2 0xa0a711814306a75 0x363 [0x1307190b003a,0xc06170d0e0c,0xf170c05])) (nd (lf2 0xa0b101814306965 0x353 [0x180b1c0a1307,0xf171b02]) (lf2 0xd4f101814307965 0x292 [0x1901]))) (nd (nd (lf2 0xd4f101814305b65 0x292 [0x1901]) (lf2 0xa07501814306bc5 0x321 [0x702])) (nd (lf2 0xa07531814305975 0x292 [0x1c0a1c0b0707,0x70207031317,0x43a]) (nd (lf2 0xa0670d4d4304975 0x296 [0xe0a19170234,0x207]) (lf2 0xa037655054070e5 0x310 [0x701]))))) (nd (nd (nd (lf2 0xa037655054070e5 0x130 [0x701]) (lf2 0xa037655054050f5 0x291 [0x70b10050703,0x121f0d1f01,0x70700061f10,0x710])) (nd (lf2 0x60f765505405075 0x90 [0x1f020012070b,0x70707031f0d]) (lf2 0x60f7655054050f5 0x90 [0x120006070b,0x10201f0d1f02,0x70707031005]))) (nd (nd (lf2 0xa0f765505405075 0x290 [0x1f021005070b,0x70707031f0d]) (lf2 0xa0b1018154063e5 0x173 [0x1b0213070c16,0x100a1e171e0c,0x1014])) (nd (lf2 0x205731815407355 0x321 [0x702]) (nd (lf2 0x205731815406375 0x82 [0x60032003d,0x700031e0c,0xc0a140a]) (lf2 0x205731815405375 0x292 [0x1c0a07071006,0x1f02180b0f0d]))))))
def RtT7 : BTree NodeData := nd (nd (nd RtT7_0 RtT7_1) (nd RtT7_2 RtT7_3)) (nd (nd RtT7_4 RtT7_5) (nd RtT7_6 RtT7_7))
def RtM7 : BST := BN 386841446 3328 (BN 348064273 6784 (BN 317747263 6274 (BN 282577578 2440 (BN 270493227 2688 (BN 269477888 7686 (BL 239446966 128) BE) (BN 281426503 1792 (BL 278873659 5380) BE)) (BN 300774178 2816 (BN 295444612 3840 (BL 287013576 5512) BE) (BL 307379687 646))) (BN 329807525 5126 (BN 324411462 640 (BN 319921020 5768 (BL 318196353 896) BE) (BN 329486545 7808 (BL 325371527 1030) BE)) (BN 346507356 4992 (BN 344541933 260 (BL 333922543 6528) BE) (BL 347097471 1536)))) (BN 365139905 3968 (BN 357815805 262 (BN 354278571 7172 (BN 353669633 7680 (BL 348977931 6404) BE) (BN 355076892 0 (BL 354426557 6914) BE)) (BN 360541212 6144 (BN 360371788 2176 (BL 358714569 2564) BE) (BL 362251803 6406))) (BN 381311114 7552 (BN 369865037 3206 (BN 369718245 1026 (BL 365429039 5254) BE) (BL 374154243 5122)) (BN 384737188 2432 (BN 382661978 5376 (BL 381885375 3588) BE) (BL 385176199 2304))))) (BN 435713385 7168 (BN 408387361 3456 (BN 393356141 1024 (BN 389173186 5504 (BN 387837808 6016 (BL 386989021 6912) BE) (BN 389957981 514 (BL 389612197 1280) BE)) (BN 397792139 5120 (BN 396022352 2944 (BL 394393979 6658) BE) (BL 399590680 2048))) (BN 429517939 7810 (BN 415649855 3076 (BN 415584384 5888 (BL 414239249 3590) BE) (BL 427578894 3712)) (BN 433953937 6530 (BN 431515747 5248 (BL 430444237 1028) BE) (BL 434880235 5124)))) (BN 459996573 3072 (BN 447015012 6400 (BN 441160632 5760 (BN 440149383 2560 (BL 435951745 3200) BE) (BN 443218444 7296 (BL 442579014 256) BE)) (BN 455852886 2310 (BN 455049359 7302 (BL 454336728 8064) BE) (BL 457348636 6918))) (BN 479922456 3584 (BN 468360297 512 (BN 466443444 8066 (BL 460288884 1286) BE) (BL 472796295 6656)) (BN 496093418 7424 (BN 489974716 7936 (BL 481094429 5632) BE) (BL 510110212 6272)))))
def RtT8_0 := nd (nd (nd (nd (nd (lf 0x50c210801003f04 [0xa020c0b010e,0x30c050c060c,0x80d]) (lf 0x50c210801003f84 [0x7100c0b010e,0x60c09070a02,0x80d030c050c,0x1d00110013])) (nd (lf 0x90c210801003f04 [0x907070a0c0b,0x80d07140a02]) (lf 0xd0c210801003f84 [0x907070c0c0b,0xa02010e0710,0xb170d170e17,0x80d0717]))) (nd (nd (lf 0x58c210801003b84 [0x62e06060907,0x617060c040b]) (lf 0x150210801003f84 [0x70c0c0b010e,0x60607170a02,0x80d03060506])) (nd (lf 0x550210801003f84 [0x907070a0c0b,0xf100a020714,0x110013080d,0x1d]) (lf 0x950210801003f84 [0x90707140c0b,0xa020710070c,0x32e052e062e,0x110013080d,0x1d])))) (nd (nd (nd (lf 0x10a310801003f04 [0x70c0a030507,0x130717]) (lf 0x152310801003f44 [0xd0d070c0a03,0xc0b0717])) (nd (lf 0x552310801003f44 [0x714070a0a03,0x5070c0b0d0d,0x411]) (lf 0x952310801003f44 [0x70c07140a03,0x5070c0b0d0d,0x13]))) (nd (nd (lf 0x8ca310801003f04 [0x3060a030507,0x70c0b0c032e,0x1e07170b17,0x11]) (lf 0x10a310801003f84 [0xb100c0b032e,0x7170b17070c,0x13])) (nd (lf 0x50e310801003f44 [0xd0d070a0a03,0x30600130c0b,0x717050c0507,0x41108110714]) (lf 0xd0e310801003f44 [0xd0d070c0a03,0x71403060c0b,0x717]))))) (nd (nd (nd (nd (lf 0x152310801003fc4 [0xb100306020f,0xc0b0d0d070c,0x811]) (lf 0x552310801003fc4 [0xd0d0c0b070a,0xb100a030714,0x41108110507,0x204])) (nd (lf 0x952310801003fc4 [0x7140c0b032e,0xa0302040d0d,0x81100130507,0x411]) (lf 0x148410801003f84 [0x7170b0c0c0b,0x32e0306]))) (nd (nd (lf 0xd4c410801003fc4 [0x7170c0b032e,0x81107100d0d]) (lf 0x60c410801002fc4 [0x30c03060c0b,0x11608190d0d,0x1070317])) (nd (lf 0x616430801002d64 [0xe020d0d0c0b,0x30a]) (lf 0xd53430801003ee4 [0xd0d07170c0b,0x30a0b100e02,0x4110413030c])))) (nd (nd (nd (lf 0x551630801003be4 [0x813070a0206,0x507080b0d0d]) (lf 0x550540801003ce4 [0xe020d0d0c0b,0x206030c030a,0x106])) (nd (lf 0xe0d540801002fe4 [0x30a0d0d0c0b,0x31603140e02,0x21601070203,0x116]) (lf 0x60e540801002f64 [0xe020d0d0c0b,0x314030c]))) (nd (nd (lf 0x60e540801002fe4 [0xd0d07100c0b,0x30c03140e02,0x10702030316,0x1160216]) (lf 0xd52540801003ce4 [0xe020d0d0c0b,0x2060317030c,0x106])) (nd (lf 0xd50428c01003e64 [0xb0d07170c0b,0xe02030c]) (nd (lf 0x152628c01003b64 [0xe02070c0a07,0xb0d080b0717,0x205]) (lf 0x552628c01003b64 [0xe020a07070a,0x203080b0714]))))))
def RtT8_1 := nd (nd (nd (nd (nd (lf 0x952628c01003b64 [0xe02070c0a07,0x212080b0714]) (lf 0x152728c01003764 [0x717070c0907,0x80b0e02])) (nd (lf 0x552728c01003764 [0x714070a0907,0x603080b0e02,0xb0d]) (lf 0x952728c01003764 [0x714070c0907,0x80b0e02]))) (nd (nd (lf 0x550548c01003c64 [0x30a0e020c0b,0x30c]) (lf 0x209548c01002f64 [0x30a0c0b0307,0x130e020314])) (nd (lf 0xa0a548c01002f64 [0x3140c0b0307,0x30c0e02]) (lf 0xd52548c01003c64 [0x30c0e020c0b,0x317])))) (nd (nd (nd (lf 0x90a318c01003f44 [0x70d070a0c0b,0x91009060a03,0x80207140e14]) (lf 0x98a318c01003b44 [0x92e09060607,0x60a0203040b,0x614])) (nd (lf 0x9ca318c01003744 [0x10605070a03,0x12e]) (lf 0x552318c01003f44 [0xc0b070a0106,0x8020f0d0910,0x40018]))) (nd (nd (lf 0x148418c01003fc4 [0xb0c0c0b0717,0x8180d10070d]) (lf 0x988418c01003bc4 [0xd100607092e,0xb170d17])) (nd (lf 0x9c8418c010037c4 [0x40b0507012e,0x5170b170d10]) (nd (lf 0xa08418c01002fc4 [0xc0b0307012e,0x3170d170d10]) (lf 0x90a328c01003f24 [0xe020c0b070a,0x30c09060307,0xd170e140603,0x180714])))))) (nd (nd (nd (nd (lf 0x552328c01003f64 [0xe02070a0106,0x6030b0d0c0b,0x18081e0907,0x11e]) (lf 0x60c428c01002f64 [0xc0b0e020116,0xe14030c0b0d,0x1303140317])) (nd (lf 0xd50428c01003ee4 [0x30c0d100506,0xc010e020b0d]) (lf 0x60e428c01002f64 [0x30a0b0d0106,0x200e020c0b]))) (nd (nd (lf 0x50e628c01003b64 [0xe020a07070a,0xa14050c080b,0x1f07140717]) (lf 0xd0e628c01003b64 [0xe020a07070c,0xa140506080b,0x2007170714])) (nd (lf 0x152628c01003be4 [0xe020506020e,0xd100a07070c,0x2050b0d]) (lf 0x552628c01003be4 [0xd100a07070a,0x80b0e020714,0x4180203])))) (nd (nd (nd (lf 0x952628c01003be4 [0x7140a07052e,0x2030d100e02,0x2120418080b]) (lf 0x50e728c01003764 [0xe020907070a,0x7140717080b,0x413])) (nd (lf 0xd0e728c01003764 [0xe02070c0907,0x7140106080b,0x717]) (lf 0x152728c010037e4 [0xd100106010e,0x70c080b0e02]))) (nd (nd (lf 0x552728c010037e4 [0xd100907070a,0x80b07140e02,0x1f06030b0d]) (lf 0x952728c010037e4 [0x7140907012e,0xd10080b0e02,0x11204130603])) (nd (lf 0x209438c01002f64 [0xe020c0b0307,0xe140106030a,0x314]) (nd (lf 0xa0b438c01002f64 [0xe020c0b0307,0xe140106030c,0x314]) (lf 0x550548c01003ce4 [0xe02030a0106,0xd100c0b]))))))
def RtT8_2 := nd (nd (nd (nd (nd (lf 0x209548c01002fe4 [0xd100c0b0307,0xe020314030a,0x130116]) (lf 0xe0d548c01002f64 [0x314030a0116,0xf0d0e020c0b,0x200307])) (nd (lf 0xa0a548c01002fe4 [0xe020307012e,0xd100c0b0314]) (lf 0x60e548c01002f64 [0xc0b0e020116,0xf0d0314030c,0x130307]))) (nd (nd (lf 0xd52548c01003ce4 [0xe02030c0106,0xd100c0b]) (lf 0xc8511001003f44 [0xd0c0b170c0b,0x710070d])) (nd (lf 0x8c8511001003f44 [0xd0c0b170c0b,0x50707100707,0x307]) (lf 0x8c8511001003fc4 [0x7100b170c0b,0x507070d0d0c,0x12e01060307])))) (nd (nd (nd (lf 0x988511001003bc4 [0x6070b170d0c,0x92e0906]) (lf 0x9c85110010037c4 [0x50c0b170507,0x106012e040b])) (nd (lf 0x61c5110010027c4 [0xd0c040b0009,0xf0d0b17001a,0x1160107]) (lf 0x94a321001003f24 [0xe0203070d0c,0x6030c0b0714]))) (nd (nd (lf 0x616321001003f64 [0x7140d0c0307,0x6030c0b0e02,0x106]) (lf 0xa16321001003f64 [0xe020d0c0307,0xb0d0c0b0717,0x12a0603])) (nd (lf 0x94a321001003fa4 [0xe020714092e,0x6030b100c0b,0x3170106]) (lf 0x5ce321001003764 [0x50c0b0d0106,0x1070e02040b]))))) (nd (nd (nd (nd (lf 0x54c521001003de4 [0xd0c03140c0b,0x60303170e02,0x7100b0d]) (lf 0xd4e521001003de4 [0x3140e02052e,0x250b0d0c0b])) (nd (lf 0x5ce5210010037e4 [0x50c0b140106,0xb0d040b0e02,0xa030025]) (lf 0x61e5210010027e4 [0xe02000f0025,0x124]))) (nd (nd (lf 0xd4e621001003be4 [0x7170a07052e,0x7100e02]) (lf 0x5ce6210010033e4 [0x50c0e02080e,0x5170a070506])) (nd (lf 0x4ca7210010037a4 [0x30d]) (lf 0x54e7210010037e4 [0xe0207140907,0x710080b090c,0x413050a0603,0x1f])))) (nd (nd (nd (lf 0xd4e7210010037e4 [0xe020907012e,0x7100717080b]) (lf 0x60e7210010027e4 [0x107090c0106,0x80b0e02])) (nd (lf 0x209531001002fe4 [0xe020d0c0307,0x3140c0b0b10]) (lf 0x5cd531001003764 [0xe020116080f,0x507080e050c,0x813]))) (nd (nd (lf 0xe1d5310010027e4 [0xe02012e000f,0x107000e0b10]) (lf 0xa0b531001002fe4 [0xe020307012e,0x2030c0b0317,0x25])) (nd (lf 0xc9731001003764 [0x310]) (nd (lf 0x2097310010037e4 [0x90c01060041,0x6030e02]) (lf 0x94d731001003764 [0x310]))))))
def RtT8_3 := nd (nd (nd (nd (nd (lf 0x550540c81003c74 [0xd0d0d10030a,0xe010e02030c,0xc03060b0c0b,0x507]) (lf 0xd52540c81003c74 [0xe020d0d0d10,0xc0b0317030c,0xc030e01])) (nd (lf 0x61e540c81002774 [0xe020d0d0121,0xb0a0b0c0e01,0xb0a170e0b]) (lf 0x152428c81003e34 [0xe0209070717,0xe0b06140e01]))) (nd (nd (lf 0x550548c81003c74 [0xe02030c030a,0xd070e0b0d0d,0xc1e0c0b0e01,0xd100c070c03,0x60b0e13]) (lf 0xd52548c81003c74 [0x30c0d0d0e02,0xd070e010317,0xc1e0e0b0c0b,0xd100c070c03,0xe13])) (nd (lf 0x61e548c81002774 [0xe02030c011e,0xb0b170b14,0x10a00030e01]) (lf 0x215748c81002d74 [0x3170e020907,0x1e0e01030a,0xe0b])))) (nd (nd (nd (lf 0xe15748c81002d74 [0x3140e020907,0xe01011e030a]) (lf 0xd0e428c81003e34 [0xe0205060907,0xe010305030c,0x717])) (nd (lf 0xd4e428c81003f34 [0xe0207170305,0xa0b0e010907,0xa0306130e0b,0x121060b0a0c]) (lf 0x152428c81003eb4 [0xe0203050506,0x7170e010d10,0x907]))) (nd (nd (lf 0xa0b438c81003e34 [0xe02030c0507,0xe0b0e170e01,0x1200e130e14]) (lf 0x553438c81003e74 [0x30c0e02030a,0x7170d0d0e01,0x51406140c0b,0x60b081e0c07,0x50709100613,0x11e])) (nd (lf 0x60c548c81002f74 [0xe010e02010e,0xc0b020b0d0d,0x20302130c13,0x107]) (nd (lf 0x550548c81003cf4 [0xd0d030a0106,0xd100e010e02,0x30c0c1e0e0b,0x60b0e130c07]) (lf 0xe0d548c81002f74 [0xd0d01200106,0xc0b0e010e02,0xe0b0c070116])))))) (nd (nd (nd (nd (lf 0x60e548c81002f74 [0xe020d0d0106,0x3140e01030c,0xc1301160e0b,0x20b0c0b0213,0x1070c07]) (lf 0xd52548c81003cf4 [0x12e0d0d0106,0xd100e010e02,0xc070c130c0b,0xe0b])) (nd (lf 0xd4d431081003c74 [0xe02090c090a,0x7170e010d0d,0xc0b0c130a0b,0xe130a030221,0x1210e0b]) (lf 0xd4d431081003e74 [0x90c07170105,0xd0d0e010e02,0xc0b0c130a0b,0x1210a030613]))) (nd (nd (lf 0xe1d531081002774 [0xe020d0d0124,0xa17000b0e01,0xe13]) (lf 0x5cd531081003774 [0x1160e020819,0x50c0e010d0d,0x90a080f0b14,0xa130a0b0a17,0x413])) (nd (lf 0xd51531081003cf4 [0x314050c0317,0xd0d0b100e02,0x60b0c0b0e01,0xe130206]) (lf 0xe1d5310810027f4 [0xe02012e0019,0xb1001240d0d,0xa170c0a000f,0x13])))) (nd (nd (nd (lf 0x61e531081002774 [0xe02050c0d0d,0xb170b140e01,0xe0b0024000b,0xe130006]) (lf 0x5cf531081003574 [0xe02050c0116,0x40b0e010d0d,0xe0b0c0a0403])) (nd (lf 0x5cf531081003774 [0xb17050c0116,0xe010d0d0e02,0xa14040b0e0b,0x40301140e13,0xa0b0a130c0a]) (lf 0xd53631081003a74 [0xe0207170a0b,0x50c0d0d]))) (nd (nd (lf 0x61f631081002374 [0xe020d0d002e,0x140e01]) (lf 0x201731081003764 [0xd0d0e02060b,0xe010106090c])) (nd (lf 0xd51731081003674 [0xe020d0d0106,0x80b0e01]) (nd (lf 0x215731081003774 [0xd0d0e020106,0xe0b0e01090c,0x2401070613,0x114060b]) (lf 0x615731081003774 [0xe020d0d0116,0xe010714090c,0x50a0e13060b,0x60603003c,0x613]))))))
def RtT8_4 := nd (nd (nd (nd (nd (lf 0xa15731081003774 [0xd0d090c0116,0xe0107170e02,0x6030e13060b,0x6130e0b0024,0x114]) (lf 0xe15731081003774 [0xe0207140106,0xe01090c0d0d,0xe13003c])) (nd (lf 0x219731081003374 [0xd0d040f060b,0x617090c0e02,0x2706100614,0x613]) (lf 0xe19731081003374 [0x90c0d0d0613,0x617060b0027,0x614]))) (nd (nd (lf 0x2017310810037e4 [0xe02060b0106,0x116090c0d0d,0xe01]) (lf 0x14d731081003774 [0x310])) (nd (lf 0x94d731081003774 [0x310]) (lf 0x2197310810033f4 [0x90c060b0116,0x9060d0d0e02,0x614040f0610,0x130617])))) (nd (nd (nd (lf 0xe197310810033f4 [0x90c0d0d0613,0x916060b0906,0x706100042,0x614]) (lf 0x60f541081002e74 [0xd0d0e02090c,0x1200e010317,0xe0b02160c0b,0x1160e13])) (nd (lf 0x60f541081002ef4 [0xe02090c0120,0xe010d0d0317,0xe1302160e0b,0xc0b0116]) (lf 0x54f439081003c74 [0x90c0e020105,0xc130e010d0d,0xc0b]))) (nd (nd (lf 0xd8f439081003a74 [0xe02090c060b,0xd170d0d090a,0x6140b170d14]) (lf 0x5cd539081003574 [0xe0201200116,0xc0c0e010d0d,0xe0b])) (nd (lf 0xe1d6390810023f4 [0xf002e0043,0x170e020e01]) (lf 0x61f6390810023f4 [0x2e0043000f,0xe010d0d]))))) (nd (nd (nd (nd (lf 0x151321881003bb4 [0x90d]) (lf 0x551321881003bb4 [0x90d])) (nd (lf 0x951321881003bb4 [0x90d]) (lf 0x50f421881003ab4 [0x90d]))) (nd (nd (lf 0xd4f421881003bb4 [0x90d]) (lf 0x60f421881002b34 [0xe010e02002b])) (nd (lf 0x60f421881002bb4 [0xc0b0710000e,0xc03]) (lf 0xe09431881003ab4 [0x50d])))) (nd (nd (nd (lf 0xd4d431881003874 [0xc030c0b0c07,0x210316]) (lf 0xd4d431881003a74 [0xc0b0717000e,0xe020021])) (nd (lf 0xe0d431881003a74 [0xe02030c000e,0x200c070e01]) (lf 0xe1d4318810032f4 [0xe020b10000e,0xc0e01]))) (nd (nd (lf 0xd4d431881003974 [0xe020c070b0a,0x80b07170e01,0x21080c0803]) (lf 0xe1d4318810023f4 [0x440b10000e,0x3f])) (nd (lf 0x616431881002974 [0x314030a0c07,0xe010e02]) (nd (lf 0x617431881003af4 [0xb100c070714,0xe020e01030c,0x200006]) (lf 0xa17431881003af4 [0xb1007170c07,0xe020e01030c,0xe0024]))))))
def RtT8_5 := nd (nd (nd (nd (nd (lf 0x553431881003af4 [0xb100c070714,0xe020e01030c,0x2004170d0d]) (lf 0xd53431881003af4 [0xe010b10000e,0x2407170e02,0xd0d030c])) (nd (lf 0x5505418810038f4 [0xc030c0b000e,0x60f10030c,0x5]) (lf 0xe0d541881002bf4 [0x30a07100c0b,0xc030c070314,0xe0100200316,0x160d0d0e02,0x817080c]))) (nd (nd (lf 0xe1d5418810023f4 [0xe02002a002b,0x160f100e01]) (lf 0x60e541881002b74 [0xe010e02000e,0x80a0c07030c,0x210016])) (nd (lf 0x60e541881002bf4 [0xc030c0b000e,0x30c00210316,0xe020e010016,0x80a07100d0d]) (lf 0xd525418810038f4 [0x317030c0c0b,0xf100c030c07,0x6])))) (nd (nd (nd (lf 0xe1d439881002374 [0x1f000e]) (lf 0x201439881003ae4 [0xb100e02000e,0x30a040b])) (nd (lf 0xd4d439881003874 [0xe010e020c07,0x210316]) (lf 0xd4d439881003a74 [0xe020717000e,0x4140e01]))) (nd (nd (lf 0xe0d439881003a74 [0xe010e02000e,0x30a030c]) (lf 0xe1d4398810032f4 [0xe020b10000e,0xe01])) (nd (lf 0xd4d439881003974 [0xe020c070b0a,0x80b07170e01,0x21080c0803]) (nd (lf 0xe1d4398810023f4 [0x1f0b10000e,0x45]) (lf 0x616439881002974 [0xe010e020c07,0x314030a])))))) (nd (nd (nd (nd (lf 0x61e439881002374 [0xe010e02002e,0x140f0d0c07]) (lf 0x617439881003af4 [0xb100c070714,0xe02030c0e01,0x6])) (nd (lf 0xa17439881003af4 [0xe0107170c07,0xe02030c0b10,0x20000e0016,0x24]) (lf 0x553439881003af4 [0xe010c070714,0x30c0e020b10,0x816]))) (nd (nd (lf 0xd53439881003af4 [0xe020e01000e,0x20030c0b10,0x8160024]) (lf 0x551739881003374 [0xe02070a0006,0x8070e01])) (nd (lf 0x5505498810038f4 [0xe010e02000e,0x30c00060c10,0x30a]) (lf 0xe0d549881002bf4 [0x30a07100c07,0x3140e020e01,0x2000160316,0x3000b])))) (nd (nd (nd (lf 0xe1d5498810023f4 [0x2a001f002b,0xe02]) (lf 0x60e549881002b74 [0xe010e02000e,0x30c00160021,0x817])) (nd (lf 0x60e549881002bf4 [0xe020e01000e,0x1600210316,0x3000b030c,0x8170710]) (lf 0xd525498810038f4 [0xe010e020c07,0xc100317030c,0x6]))) (nd (nd (lf 0xd487250c1003734 [0x30d]) (lf 0x1507250c1003674 [0xe0207170907,0x6140e0b0e01,0x80b0114])) (nd (lf 0x1c47050c10036c4 [0x6030d100a0b,0x10500160106,0xa02]) (nd (lf 0x1c87050c10036e4 [0xe0201060a0b,0x7070d10001b,0x2c]) (lf 0xd4c7050c1003c64 [0xe020a0b0116]))))))
def RtT8_6 := nd (nd (nd (nd (nd (lf 0xd4c7050c1003e64 [0x7170a0b0105,0x1b000e0e02]) (lf 0x1d47050c10036e4 [0xe020a0b0105,0xe07170d10,0x16])) (nd (lf 0xd4c7250c1003c74 [0xe0b0e020116,0xb0d0a070e13,0xa0b082c0e01,0xa13]) (lf 0xd4c7250c1003e74 [0xe0207170105,0xb0d0a070e0b,0x1b0e010a13,0x370613082c,0xa0b]))) (nd (nd (lf 0xdcc7250c1003674 [0x1060e020b0d,0x50c01050e01,0x2c0a0b0b07,0x7170e130e0b]) (lf 0x1d47250c10036f4 [0xe0207170105,0xa070e0b0d10,0xe0d0e01002c,0xa0b0e130016])) (nd (lf 0x1d87250c10032f4 [0xd10060b0037,0xb170e020b0d,0x617040c090a]) (lf 0xa0b5350c1003c74 [0xe0201210116,0x60b0e01070d,0x613])))) (nd (nd (nd (lf 0x1db5350c1003874 [0x116060b002d,0x6070f0d0e02]) (lf 0xddb5350c1003874 [0xf0d01160613,0x607])) (nd (lf 0xdd75350c1003c74 [0xe010e020112,0xe0f0d0314,0xe130e0b]) (lf 0x1db5350c1003a74 [0x60b0b17000f,0x370f0d0021,0x607]))) (nd (nd (lf 0xddb5350c1003a74 [0xb170613000f,0x214]) (lf 0xa1f5350c1002e74 [0xe010e020112,0xe03140f0d,0xe0b01160e13,0x213])) (nd (lf 0xdd77350c1003674 [0xe010e020106,0xe0f0d0714,0x9100e130e0b]) (lf 0x1db7350c1003274 [0xe02090c060b,0xf09100f0d,0x6140b170607]))))) (nd (nd (nd (nd (lf 0x1d87550c10032f4 [0xe010d10000f,0x60706140b17,0x40c]) (lf 0x1487650c1003af4 [0x106])) (nd (lf 0x1c87650c1003af4 [0x10a]) (lf 0x9c87650c10032f4 [0x10a]))) (nd (nd (lf 0xdcc7650c1003a74 [0x10a]) (lf 0x9d47650c10032f4 [0xd100a0b0717,0x80c0a070e02])) (nd (lf 0x14b7650c1003af4 [0x106]) (lf 0x1cb7650c1003af4 [0x10a])))) (nd (nd (nd (lf 0xdcf7650c1003a74 [0x10a]) (lf 0xd487250c10037b4 [0x30d])) (nd (lf 0xd4c7250c1003574 [0xe02090a0907,0xe0107170e0b,0xc0c0e0d0421,0x1210e13080b]) (lf 0xd4c7250c1003774 [0x71701050907,0xe010e0b0e02,0xc0c0e0d0613,0x121060b080b]))) (nd (nd (lf 0xd8c7250c1003374 [0x90a00060907,0xe010e02]) (lf 0x1507250c10036f4 [0xd1001050907,0x7170e0b0e02,0x60b0d0e01,0x80b0e13])) (nd (lf 0xa0b5350c1003d74 [0xe0201210d0a,0xc0b0e01070d,0xe130e0b0c0c,0x50c03170c03,0x613060b]) (nd (lf 0xa135350c1003c74 [0xe010e020112,0xe0b0f0d050c,0xe13]) (lf 0xa1f5350c1003574 [0x50c0e020116,0xf0d01210e01,0xe130e0b]))))))
def RtT8_7 := nd (nd (nd (nd (nd (lf 0xa0b5350c1002f74 [0x3170d0a0307,0xc0b0e010e02,0xc03020b0e13,0x914010c0c0c,0x213]) (lf 0x9535350c1003c74 [0xe010e020112,0xe0f0d050c,0xe130e0b])) (nd (lf 0xa0a5450c1002ef4 [0xd100e020112,0xe0b0e010307,0xe0d03140e13,0x20b02130806]) (lf 0xa0a75d0c1002ef4 [0xe020d100124,0xe0b03070e01,0x2008160213,0x20b]))) (nd (nd (lf 0x5ce75d0c1003674 [0xe02050a0b17,0xe0f0d0e01,0x370e130e0b,0x60b0a130510]) (lf 0xd8e72d0c1003374 [0x90c00060907,0xe010e02])) (nd (lf 0x20954d0c1002ef4 [0xd1003140307,0xe01090c0e02,0x80602130e0b,0x20b0116]) (lf 0xa0b54d0c1002ef4 [0xe020d100124,0xe0b03070e01,0xc0b00060213,0x20b])))) (nd (nd (nd (lf 0x5503258c1003b74 [0x910]) (lf 0x6103258c1002a74 [0x30a0b0d0c13,0xc17])) (nd (lf 0x21d5458c10023f4 [0xe010e020006,0x70f0d030a,0x2e00090008]) (lf 0x55054d8c1003874 [0x30a0e020c0b,0xc030e01030c,0xc07]))) (nd (nd (lf 0x20954d8c1002b74 [0x30a0c0b0307,0x330e020314]) (lf 0xa0a54d8c1002b74 [0x3140c0b0307,0xe02030c])) (nd (lf 0xd5254d8c1003874 [0x30c0e020c0b,0xc030e010317,0xc07]) (nd (lf 0x55032d8c1003b74 [0x910]) (lf 0xa1032d8c1002a74 [0xe020b0d0c0b,0xc14030c])))))) (nd (nd (nd (nd (lf 0xa0843d8c1002b34 [0x307080f0c0b,0xc14030c0e02,0x806]) (lf 0xa0843d8c1002b74 [0x80f0c0b0307,0x30c0e02070d,0xc140806])) (nd (lf 0xa1443d8c1002974 [0x30c0e020c0b,0xc070317]) (lf 0x20954d8c1002bf4 [0x82e03070806,0x330e020e01,0xd10]))) (nd (nd (lf 0xe1d54d8c10023f4 [0x3c00440046,0x6]) (lf 0x4ca7215010037b4 [0x30d])) (nd (lf 0x60e7215010027f4 [0x90c0e020116,0xe0b01070917,0xb00130e01,0xc140c0a0710]) (lf 0xc9731501003774 [0x310])))) (nd (nd (nd (lf 0x5517315010034f4 [0xe0201200105,0xe0f0d0e01,0x1160e130e0b,0x60b0816002d]) (lf 0x209541501002cf4 [0xe02090c0307,0xe0b0f100e01,0xe130e100806,0x20b0106002d])) (nd (lf 0xe0d541501002cf4 [0xe010e020106,0x1160f0d0120,0x10a0e130e0b]) (lf 0xe1d5415010024f4 [0xf100e010e02,0x1050e0b0f0d,0x11600060e13,0xe100012]))) (nd (nd (lf 0x60c725501002774 [0x914090a0047,0x30e02000b,0x160120]) (lf 0x60c7255010027f4 [0x10701200106,0xb0e010e02,0x301160013,0xe0b0e0d])) (nd (lf 0x4ca7295010037b4 [0x30d]) (nd (lf 0x60e7295010027f4 [0x10709140116,0xe01090c0e02,0x13000b0e0b,0x7100e0d0003,0xc17]) (lf 0xd51739501003474 [0xe010e020517,0x11201210f0d,0x1160e130e0b]))))))
def RtT8_8 := nd (nd (nd (nd (nd (lf 0xd517395010034f4 [0xe010e020106,0x1160f0d0120,0xe130e0b]) (lf 0x5da421043003274 [0xe010b0d0031,0xb17])) (nd (lf 0x5d8521043003374 [0xd0200480b17,0x330e010b0d,0x4906100031,0xd0c]) (lf 0x61c521043002774 [0xe100d02050c,0x330b0d0e01,0xb17]))) (nd (nd (lf 0x5da521043003374 [0xd0200480b14,0x310e010b0d,0x610090c]) (lf 0x61e521043002774 [0xd020e10050c,0x240b0d0e01])) (nd (lf 0x54a621043003b34 [0x30d]) (lf 0xd52621043003a74 [0x50c0e010717,0xa1008070d02])))) (nd (nd (nd (lf 0xd52721043003674 [0xd020e100717,0x10c08070e01,0x24]) (lf 0xa0b541043002e74 [0xd020e10090c,0x3170e01])) (nd (lf 0x5db541043003274 [0xe010b170031,0x407]) (lf 0x109761043003274 [0x10c]))) (nd (nd (lf 0x209761043003374 [0x3200490031,0x71707070e01,0x2a0714]) (lf 0x151761043003274 [0x10c])) (nd (lf 0x215761043003374 [0xe0107170031,0xf0d0d020505,0x50c0048]) (lf 0xe15761043003374 [0xe0105050031,0x2a00480f0d,0x50c]))))) (nd (nd (nd (nd (lf 0x152729043003674 [0xd0209070717,0x6140e010e10,0x114]) (lf 0x61a729043002374 [0xe010d02002c,0x14])) (nd (lf 0x153219843003b54 [0x902]) (lf 0x553219843003b54 [0x902]))) (nd (nd (lf 0x953219843003b54 [0x902]) (lf 0x209419843002b54 [0x307030a0032])) (nd (lf 0xe15419843002954 [0x30a0e010803,0x314]) (lf 0x550549843003874 [0x30a0e010c03,0xc07030c])))) (nd (nd (nd (lf 0x209549843002b74 [0x30a03070c03,0x40e010314]) (lf 0xa0a549843002b74 [0x3140c030307,0xe01030c])) (nd (lf 0xd52549843003874 [0x30c0e010c03,0xc070317]) (lf 0x205541503002c74 [0xe10090c0303,0x3070e01]))) (nd (nd (lf 0xe1d541503002474 [0xf020e010e10,0x1201050f0d]) (lf 0xc84715503003754 [0x302])) (nd (lf 0x618715503002374 [0xe01090a001a,0x7]) (nd (lf 0xc86719503003754 [0x302]) (lf 0x5db549503003074 [0xe0100210917,0xf0d0f02]))))))
def RtT8_9 := nd (nd (nd (nd (nd (lf 0x9c8519023003764 [0x50a0b170507,0x1f040b0b02]) (lf 0xa08519023002f64 [0x31703070d0a,0xc0b0b02])) (nd (lf 0x61c519023002764 [0xb0200320112,0x40b0107]) (lf 0xc86719023003744 [0x302]))) (nd (nd (lf 0x5d8521063003374 [0xd020b170418,0x2e0b0d050c]) (lf 0x61c521063002774 [0xd02050c004a,0x1330b0d0e01,0xb170018000b,0xe10])) (nd (lf 0x5da521063003374 [0xd020b140418,0x50c0b0d]) (lf 0x61e521063002774 [0xd020b0d0124,0xb0e100e01,0x18])))) (nd (nd (nd (lf 0xd52621063003a74 [0xe0107170a07,0x31050c0d02]) (lf 0x61e621063002374 [0xa070e010031,0x140f0d])) (nd (lf 0xd52621063003e74 [0x7170a0b0a18,0xb0d0d02050c,0x81f]) (lf 0xd52721063003674 [0xd0209070717,0x80b0e100e01]))) (nd (nd (lf 0x596721063003774 [0x7140907060b,0x50a090c0d02,0x60018]) (lf 0x996721063003774 [0x717060b0907,0x714090c0d02,0x4b])) (nd (lf 0xa0b541063002e74 [0xd02090c0307,0xe100317]) (nd (lf 0x209651063002f74 [0x2180d0c0307,0x3140d020a0b,0x4c]) (lf 0x152729063003674 [0xd0209070105,0x80b0e100e0b])))))) (nd (nd (nd (nd (lf 0x550549863003874 [0x30a0e010c03,0xc07030c]) (lf 0x209549863002b74 [0x30a0c030307,0x3303140e01])) (nd (lf 0xa0a549863002b74 [0x3140c030307,0x30c0e01]) (lf 0xd52549863003874 [0x30c0e010c03,0xc070317]))) (nd (nd (lf 0x152729863003774 [0x70c09070c0b,0x90307170818,0x1050f02]) (lf 0x552729863003774 [0x818070a0c0b,0x90307140907,0x70201030f02,0x4c])) (nd (lf 0x952729863003774 [0x90707140c0b,0x903070c0818,0x1120f02]) (lf 0x550549863003c74 [0xc0b030a0c18,0xf0d0d02030c,0x4340503])))) (nd (nd (nd (lf 0x209549863002f74 [0xc0b03070c18,0xd020314030a,0x34]) (lf 0xa0a549863002f74 [0xc0b03070c18,0xd02030c0314,0x34])) (nd (lf 0xd52549863003c74 [0xc0b0d020c18,0xf0d0317030c]) (lf 0x205541523002c74 [0xe01090c0303,0xe100f0d020b,0x3070e0b]))) (nd (nd (lf 0xe1d541523002474 [0xf020e010019,0xe1000120f0d]) (lf 0xc84715523003754 [0x302])) (nd (lf 0x584715523003754 [0x302]) (nd (lf 0xc86719523003754 [0x302]) (lf 0x941769523003164 [0xf0205140018,0xd0a0d0c0f0d]))))))
def RtT8_10 := nd (nd (nd (nd (nd (lf 0xc84715923003754 [0x302]) (lf 0xc86719923003754 [0x302])) (nd (lf 0x9ca319023003764 [0x40b05050507,0xb17050a0b02,0x1030a100a04,0x40b03]) (lf 0xa0a319023002f64 [0xb0203070d0a,0xc0c02060c0b,0x3140d14]))) (nd (nd (lf 0x148419023003ee4 [0xe100c0b0717,0x70d090c0b02]) (lf 0xa08419023002ee4 [0x90a0307002e,0x3170e100b02])) (nd (lf 0x9c85190230037e4 [0x50a0b170507,0x40b0e100b02,0x1f082e]) (lf 0xa08519023002fe4 [0x3070d0a0206,0xc0c0e100b02,0x10c])))) (nd (nd (nd (lf 0x61c5190230027e4 [0xe100b020112,0x1070f0d040b,0xc01]) (lf 0xc867190230037c4 [0x302])) (nd (lf 0xd4e719023003764 [0x90a07170903,0xf0d0021080b,0x907]) (lf 0xa07539023002f64 [0x3170d0a0303,0x3070f0d002e]))) (nd (nd (lf 0x552628c63003b74 [0x60a07070a,0x320d020e01,0x404]) (lf 0x209548c63002f74 [0xd0203070806,0x70d030a0e01,0xc03020b0c0b,0x400180103])) (nd (lf 0x61c5210630027f4 [0xb140b0d0008,0x160b170018,0xd020e01]) (lf 0x61e5210630027f4 [0x1240019004d,0xe1001050d02]))))) (nd (nd (nd (nd (lf 0x5ce621063003374 [0xe010a070006,0x80a050c0d02]) (lf 0xd52621063003af4 [0xa070717002e,0x60d020e01,0x240031])) (nd (lf 0x61e6210630023f4 [0xe01002e0031,0xf0d0a070e10,0x140017]) (lf 0xd527210630036f4 [0xe100717002e,0xe010d020907]))) (nd (nd (lf 0xa0b541063002ef4 [0x90c0e100307,0xe0103170d02,0x20b0c0b]) (lf 0xd0e629063003a74 [0x50c0e010a07,0xd170d02050a,0x7170a140d14])) (nd (lf 0xd4e629063003974 [0xe010d0a0a07,0x42107170d02,0x221]) (lf 0x5ce629063003374 [0xd020a070006,0x20050a0e01])))) (nd (nd (nd (lf 0x61e6290630023f4 [0xe010036000e,0xe10]) (lf 0xd0e729063003674 [0xd02050c0907,0x6180e0b0e01,0x91706100e14,0x1807170914,0x80b])) (nd (lf 0xd4e729063003574 [0xe010907042e,0x18090a0d02]) (lf 0xd4e729063003774 [0x71709070105,0x80b0d020e01,0x60b06100018,0x210e0b]))) (nd (nd (lf 0x1527290630036f4 [0xe1009070105,0xe010d020717,0x816]) (lf 0xa0b539063002f74 [0x31703070d0a,0xe0b0e010d02,0x9140a10004e,0x2110818])) (nd (lf 0x209439863002b74 [0x30a0c030307,0xc1400060e01,0x4110314]) (nd (lf 0xa0b439863003a74 [0xe010c030220,0xc14030c070d,0x7140717]) (lf 0xa0b439863002b74 [0x70d0c030220,0xc14030c0e01,0x3140317]))))))
def RtT8_11 := nd (nd (nd (nd (nd (lf 0x553439863003a74 [0xe0107140c03,0xd020f0d030c,0xc07]) (lf 0x5505498630038f4 [0x30a0c030006,0xf0d0e100e01,0xc07030c])) (nd (lf 0x209549863002bf4 [0xe100c030307,0xe010314030a,0x330016]) (lf 0xe0d549863002b74 [0xe010c030006,0x160f0d030a,0x2003070c07]))) (nd (nd (lf 0xe1d5498630023f4 [0x30a0e100032,0x160b140b17]) (lf 0xa0a549863002bf4 [0xc030307002e,0x3303140e01,0x817030c0e10])) (nd (lf 0x60e549863002b74 [0xe010c030006,0x3140f0d030c,0x1603070c07]) (lf 0xd525498630038f4 [0x2e0c030006,0xf0d0e100e01,0xc07])))) (nd (nd (nd (lf 0xc847150e3003754 [0x302]) (lf 0xa0a71d0e3002e74 [0xe0103070816,0xe140f020303,0x31403170020,0x18])) (nd (lf 0x20554d0e3002e74 [0xe0103030806,0xf0d020b090c,0x180307]) (lf 0x205541523002cf4 [0xe0103030806,0x20b090c0e10,0x3070e020f0d]))) (nd (nd (lf 0xe1d5415230024f4 [0xe100e010006,0x1050f0d0f02,0x12]) (lf 0xc847155230037d4 [0x302])) (nd (lf 0xc867195230037d4 [0x302]) (nd (lf 0x4ca629044003ab4 [0x30d]) (lf 0x54e6290440038f4 [0xe010a07002e,0xd020405])))))) (nd (nd (nd (nd (lf 0xd4e6290440038f4 [0xd020c0a0a07,0x71707100e01,0x405]) (lf 0xd4e629044003af4 [0xa070405002e,0xd020e010717])) (nd (lf 0x5ce6290440032f4 [0xd020a07002e,0xa1704200e01]) (lf 0x60e629044002af4 [0xe0102070216,0xd170d020c0a,0x217]))) (nd (nd (lf 0x54e7290440034f4 [0x71000050907,0xe010c0c0d02]) (lf 0xd4e7290440034f4 [0xe010c0c0907,0x71707100d02,0x50116])) (nd (lf 0xd4e7290440036f4 [0x509070717,0xd020e010c0c,0x1160710]) (lf 0x58e7290440032f4 [0xd0200200907,0x6170e010606,0x40c0016])))) (nd (nd (nd (lf 0x58f539044003874 [0xc0a0e010216,0x6070d02]) (lf 0xa0b539044002ef4 [0x3170307002e,0xd020e010c0a,0x36003a])) (nd (lf 0x58f539044003a74 [0xd0202160805,0xf0d0b170e01,0x607]) (lf 0x209639044003af4 [0xd0208200206,0x2160e01070d,0x4f080c]))) (nd (nd (lf 0x4ca621444003bb4 [0x30d]) (lf 0x50e621444003af4 [0x60a0a070d17,0xd020e010710,0xd0d05030030])) (nd (lf 0x54e6214440039f4 [0xa0c05170a07,0xe0107100514,0xd0d020b0d02,0x50001a]) (nd (lf 0x5ce621444003374 [0xd020a07002e,0x40a0e010517,0x814]) (lf 0x61e6214440023f4 [0xe0100430030,0x160010000d]))))))
def RtT8_12 := nd (nd (nd (nd (nd (lf 0x209431444002ef4 [0xa0c03070d17,0xb100d020e01,0xe0d]) (lf 0x5d94314440032f4 [0xb100517003a,0x4070f0d0d02])) (nd (lf 0x61d631444002374 [0xe010a0c0016,0x70d020517]) (lf 0xe1d631444002374 [0xe010d020006,0x70a0c]))) (nd (nd (lf 0x2097614440033f4 [0x70d001a0009,0x510e010d02,0xe0c0d17]) (lf 0xd0d7614440032f4 [0x20c])) (nd (lf 0x1517614440030f4 [0x20c]) (lf 0x4ca629444003bb4 [0x30d])))) (nd (nd (nd (lf 0xd4e6294440039f4 [0x4050a07022e,0x5170d020e01,0x2100390c0a]) (lf 0x61e6294440023f4 [0xe010039000e,0xa0c])) (nd (lf 0xd4e7294440035f4 [0x71009070e0c,0xd020e010517,0x901160005]) (lf 0x58e729444003374 [0x9140e010907,0x16060c0d02,0x33]))) (nd (nd (lf 0x58e7294440033f4 [0xe0109070406,0x33060c0d02,0x4170710]) (lf 0x61a7294440023f4 [0x2400450009,0xd])) (nd (lf 0x58f539444003974 [0xd0202160805,0xf0d060c0e01,0xc0a0607]) (lf 0x5db5394440031f4 [0xe0100240025,0x50b10]))))) (nd (nd (nd (nd (lf 0x209639444003b74 [0xd020006040e,0x50705030e01,0xc0a0d0d0a0c,0x60a]) (lf 0x215639444003974 [0xd0200240006,0x20b0e01])) (nd (lf 0xe1d639444003374 [0xd0200380006,0xf0d0a0c0e01,0x44205070d14]) (lf 0xc9639444003b74 [0x310]))) (nd (nd (lf 0xe1d6394440023f4 [0xe0100060025,0x100024]) (lf 0xd51319844003ad4 [0x902])) (nd (lf 0x209439844002af4 [0xe010b100037,0xc170c030307,0x317]) (lf 0xd4d439844003874 [0xe010c03002e,0xc070f0d])))) (nd (nd (nd (lf 0xd4d439844003a74 [0x7170c030205,0xc070f0d0e01,0x37]) (lf 0x209539844002b74 [0xe010c0c0307,0x30314])) (nd (lf 0x209539844002bf4 [0xc030307002e,0x330e010314,0xc0c0d020b10,0x817]) (lf 0xd515398440038f4 [0xb100c030024,0xc0703170e01]))) (nd (nd (lf 0xe1d5398440023f4 [0xe010b100050,0xc03002e]) (lf 0xa0a539844002b74 [0x31403070c03,0xc0c0e01])) (nd (lf 0xa0b539844002bf4 [0x3170c030307,0xc0c0e010b10,0x360814020a]) (nd (lf 0xc9739844003374 [0x310]) (lf 0xa0b549844002af4 [0xc0300240047,0x2e00060317]))))))
def RtT8_13 := nd (nd (nd (nd (nd (lf 0x60f549844002a74 [0xe010c030024,0xc07]) (lf 0x60f549844002af4 [0xe010c03002e,0xc0702200317])) (nd (lf 0xc847150c40036d4 [0x302]) (lf 0xd447150c40036d4 [0x302]))) (nd (nd (lf 0xd4c7150c4003474 [0xe010903002e,0x9070e02]) (lf 0xd4c7150c4003674 [0xc0c09030717,0x50e020e01,0x9070037])) (nd (lf 0x6187154c4002374 [0xe01060c001a,0x7]) (lf 0xc847154c40037d4 [0x302])))) (nd (nd (nd (lf 0x58c7154c4003374 [0x9140e010903,0xf0d060c0016,0x60709070b02]) (lf 0x6187154c40023f4 [0xe01002e001a,0xd00070d10,0x2060c000a])) (nd (lf 0xc867194c4003754 [0x302]) (lf 0x58e71d4c4003374 [0xe0109170903,0xf0d0016060c,0x80a06070907,0x414]))) (nd (nd (lf 0x61a71d4c40023f4 [0xe01002e0025,0x2]) (lf 0xc847158c4003b54 [0x302])) (nd (lf 0x1c87158c4003374 [0xe010c0c0037,0x70d00060b02,0x307140b14,0x7]) (nd (lf 0x1c87158c4003b74 [0x60b02003a,0x520c0c070d,0x307003b0303]) (lf 0x9c87158c4003374 [0x70d0006003a,0xc0c0050])))))) (nd (nd (nd (nd (lf 0xa087158c4002b74 [0x8060e010307,0xf02070d0c0c,0x314002a0303]) (lf 0xa087158c4003b74 [0x3030253003b,0x20f0f02070d,0x370c0c])) (nd (lf 0x6107158c4003a74 [0x8060303003a,0xc0f0d0605]) (lf 0x1d47158c4003374 [0xc0c00370717,0x30b020e01,0xa0a00160f0d]))) (nd (nd (lf 0x9d47158c4003374 [0x7170037003a,0xc0c0f0d0b02,0x1a]) (lf 0x6147158c4003b74 [0x3030006003b,0xc0c0f0d0714,0x3707020f02,0x60a0205])) (nd (lf 0xdc67158c4003354 [0x302]) (lf 0xa0a7158c4002b74 [0xe0103070006,0xf0203030c0c,0x20a0054])))) (nd (nd (nd (lf 0xa047558c4002b74 [0xe0103030006,0x3070f0d0c0c]) (lf 0x2057558c4002b54 [0x1603140e01,0x2a0f0d0c0c,0x1a0303])) (nd (lf 0x2057558c4002b74 [0x3140e010303,0xf0d0c0c0016,0x307002a001a]) (lf 0xa067558c4002b74 [0xe0103170303,0xf0d00160c0c,0x3c020a0307]))) (nd (nd (lf 0xdd67558c4003174 [0xc0c0e010006,0x3c0f0d0f02,0x2a]) (lf 0x1c83158c4003b74 [0x70d00060820,0x3070e010b02,0x500a0a0c0c])) (nd (lf 0xa083158c4002b74 [0x110]) (nd (lf 0x6143158c4002974 [0x110]) (lf 0xa143158c4002974 [0x110]))))))
def RtT8_14 := nd (nd (nd (nd (nd (lf 0xa1c3158c4002b74 [0xe0100060050]) (lf 0xc847158c4003bd4 [0x302])) (nd (lf 0x1c87158c40033f4 [0xc0c0b020006,0x400e01070d,0x1607100b10,0x70003]) (lf 0xa087158c4002bf4 [0xe0103070806,0x303070d0c0c,0x30208160f02]))) (nd (nd (lf 0xa087158c4003bf4 [0x70203030816,0x70d0f020055,0xc0c0041]) (lf 0x6107158c4003af4 [0x71008060040,0xf020e010c0c])) (nd (lf 0xa045358c4002b54 [0x110]) (lf 0xa045358c4002b74 [0x110])))) (nd (nd (nd (lf 0xd4f219864003bd4 [0x902]) (lf 0x5cf2198640033d4 [0xc0a0e010416,0xc050b0d0b02,0x417])) (nd (lf 0x54f439864003874 [0x50a0c0c03,0xc070f0d0e01]) (lf 0xa0b5398640039f4 [0xc030321022e,0xc0a070d0e01,0x560317]))) (nd (nd (lf 0xa0b539864002bf4 [0xb100c030307,0xe0103170c0a,0x31020c0016]) (lf 0xa0a71d4e4002df4 [0x91703070e0a,0x3030e010d10,0x3020e020057,0x116])) (nd (lf 0x61a71d4e40029f4 [0xe01082e0025,0x120d10]) (nd (lf 0x61a71d4e40023f4 [0xd1000580025,0x16]) (lf 0x18b101814303ae4 [0x901])))))) (nd (nd (nd (nd (lf 0xa0b101814302ee4 [0x101]) (lf 0xd4f101814303c64 [0x901])) (nd (lf 0xd4f101814303e64 [0x901]) (lf 0x197101814303ae4 [0x901]))) (nd (nd (lf 0x61f101814302ee4 [0x10b0e100031,0xb010c050c06,0x307]) (lf 0x600611814303ae4 [0x501])) (nd (lf 0xa00611814303ae4 [0x50b0e100031,0x80503030806,0x3010049]) (lf 0x9c86118143032f4 [0x50708060037,0xf010e10050b,0x51d])))) (nd (nd (nd (lf 0x9c8611814303af4 [0x3a050b0059,0xe10070d0806,0x805]) (lf 0xd4c611814303874 [0x160d010059,0x490b02])) (nd (lf 0xd4c611814303a74 [0xd0107170049,0x370d020005,0x1b]) (lf 0x61c611814303af4 [0x3a00310049,0x418]))) (nd (nd (lf 0xd4e711814303474 [0x90b09030416,0x9070f0d0f01]) (lf 0xd4e711814303674 [0x90307170405,0xf0d0f01090b,0x9070037])) (nd (lf 0xd8e711814303274 [0x90b060c0903,0x40604050f01,0x7170907]) (nd (lf 0x1967118143032f4 [0xe1009030405,0xf01090b0717,0x907]) (lf 0xa0a711814302ef4 [0xe003a002d,0x303090b070d,0x311]))))))
def RtT8_15 := nd (nd (nd (nd (nd (lf 0xd4e711814303c74 [0x90b0b02005a,0xf010c0a]) (lf 0xd4e711814303e74 [0x90b0717083a,0xb0200490405,0xe001b0f0d])) (nd (lf 0xd8e711814303a74 [0xb02060c003a,0x4060f0d090b,0x7170405]) (lf 0x196711814303af4 [0x90b0717003a,0xf0d0e100405,0xe]))) (nd (nd (lf 0xa0670d4d4302c74 [0x30b03030816,0x3070f0d0f01]) (lf 0x9d765d8d4303074 [0x117])) (nd (lf 0xa0b101814302be4 [0x80b0e10000e,0xc0a0b02]) (lf 0xd4f101814303964 [0x901])))) (nd (nd (nd (lf 0xd4f101814303b64 [0x901]) (lf 0x60f101814302b64 [0x80b0c0a0006,0xc070b02])) (nd (lf 0x153101814303ae4 [0x901]) (lf 0xa07501814302be4 [0xc0a03030006,0x3170e10080b,0x3070c07]))) (nd (nd (lf 0x60f501814302b64 [0x3170c0a080b,0xf0d0f020016,0xc070c03]) (lf 0xa07531814303974 [0x2e0c0b0221,0xf0d0c0a0702,0xc0703170d01])) (nd (lf 0xa07531814302b74 [0x3170c0b0303,0xc070f0d0c0a,0x20c0307]) (nd (lf 0xa0670d4d4302d74 [0x30b0303082e,0xf0d0e0a0f01,0x2103070917]) (lf 0xc427095143036e4 [0x301])))))) (nd (nd (nd (nd (lf 0xa0b109824302b64 [0xb02080b0307,0x3140c0a]) (lf 0x201639974302a74 [0x30b0d17001b,0x30703030f0d])) (nd (lf 0xc5739805403374 [0x310]) (lf 0x2015458c54028f4 [0x5030b002d,0x3030f0d0d10,0x307]))) (nd (nd (lf 0x60c705505402474 [0xf02010b0006,0x10701030f0d]) (lf 0xa037655054030f4 [0xf0207010012,0x50f100f0d,0x6])) (nd (lf 0x60f765505402074 [0xf010f020016,0xf0d]) (lf 0x60f765505403074 [0xf0200050012,0xf0d0f01])))) (nd (nd (nd (lf 0x60f7655054030f4 [0xf0200050006,0x200f0d0f01,0x12]) (lf 0xa0f765505403074 [0xf0200050710,0x160f0d0f01])) (nd (lf 0xa0b101815402be4 [0xc140c0a0032,0xf100307]) (lf 0x5cf1018154033e4 [0xc1404160420,0x4070b010b02]))) (nd (nd (lf 0x205731815403374 [0x80b0c0a0006,0x70307020f0d,0x5b]) (lf 0xa0b109825402be4 [0x101])) (nd (lf 0x5cf1098254033e4 [0xb0204210035]) (nd (lf 0x60f109825402b64 [0x80b0c14002e,0xc070b02]) (lf 0x205309825402be4 [0xb100c14004e,0x80b0303]))))))
def RtT8 : BTree NodeData := nd (nd (nd (nd RtT8_0 RtT8_1) (nd RtT8_2 RtT8_3)) (nd (nd RtT8_4 RtT8_5) (nd RtT8_6 RtT8_7))) (nd (nd (nd RtT8_8 RtT8_9) (nd RtT8_10 RtT8_11)) (nd (nd RtT8_12 RtT8_13) (nd RtT8_14 RtT8_15)))
def RtM8 : BST := BN 391906384 29440 (BN 342829452 24192 (BN 312789053 26240 (BN 292147089 19586 (BN 273548844 17538 (BN 253689853 18048 (BN 210247463 24322 (BN 186475276 5760 (BL 178838264 21632) BE) (BN 249195847 1792 (BL 237448513 3200) BE)) (BN 267345089 25227 (BN 260501579 24326 (BL 254619877 30848) BE) (BN 273049873 12416 (BL 269688295 19200) BE))) (BN 284504075 9600 (BN 279225413 28544 (BN 275631240 20864 (BL 274789415 12160) BE) (BN 281977630 28032 (BL 281124437 31872) BE)) (BN 289362278 2818 (BN 285804099 20352 (BL 284900768 12672) BE) (BN 291939799 6784 (BL 290712301 64384) BE)))) (BN 302182057 18438 (BN 298451862 24962 (BN 296583087 27266 (BN 294896795 3458 (BL 294436062 64256) BE) (BN 297314731 65408 (BL 296676446 26880) BE)) (BN 299020860 12038 (BN 298798684 12168 (BL 298577747 29698) BE) (BN 301143638 25856 (BL 299059019 16518) BE))) (BN 306365952 10368 (BN 302661755 23936 (BN 302610482 16130 (BL 302579018 24320) BE) (BN 303234682 28552 (BL 303013745 25090) BE)) (BN 307382911 5504 (BN 307046480 32514 (BL 306618055 30726) BE) (BN 310501381 8072 (BL 307725228 26626) BE))))) (BN 326215972 13440 (BN 321232663 29190 (BN 317574504 16000 (BN 316796665 12806 (BN 313997466 6912 (BL 312884839 13698) BE) (BN 317516052 3328 (BL 316936868 2560) BE)) (BN 319285362 19072 (BN 318606250 10759 (BL 318304295 648) BE) (BN 319809898 132 (BL 319332371 5252) BE))) (BN 323644219 15236 (BN 322506458 25728 (BN 321968754 16512 (BL 321419610 15878) BE) (BN 323042248 27143 (BL 322740293 31368) BE)) (BN 325412039 4741 (BN 324874803 1152 (BL 323920698 63232) BE) (BN 325791680 23296 (BL 325487333 9346) BE)))) (BN 337342006 30466 (BN 333563833 27136 (BN 331089101 5124 (BN 329127835 10752 (BL 328801994 18816) BE) (BN 332219281 25216 (BL 331237087 14594) BE)) (BN 335141613 8320 (BN 334097174 63488 (BL 333601098 30464) BE) (BN 337082491 31620 (BL 335525099 31748) BE))) (BN 340324433 2688 (BN 338296784 27904 (BN 338078617 768 (BL 337351742 28672) BE) (BN 339852404 7552 (BL 338729897 12032) BE)) (BN 341753913 2176 (BN 341317757 14464 (BL 341034284 7808) BE) (BN 342324374 2054 (BL 341881441 21888) BE)))))) (BN 369808942 10624 (BN 359433327 65282 (BN 350964773 30722 (BN 347923077 13568 (BN 346528775 18434 (BN 345275580 65152 (BL 344085578 11394) BE) (BN 347768454 28420 (BL 346760372 6150) BE)) (BN 349238775 29064 (BN 348707877 23682 (BL 348521576 23170) BE) (BN 350516236 3074 (BL 349967118 31106) BE))) (BN 354984814 9734 (BN 353473980 28418 (BN 352864598 16134 (BL 352359075 29952) BE) (BN 354952234 4610 (BL 354403116 9090) BE)) (BN 358014817 11392 (BN 357300596 32518 (BL 355647737 5256) BE) (BN 358970037 0 (BL 358891217 13952) BE)))) (BN 364985526 15232 (BN 362450815 23168 (BN 361412977 3076 (BN 361046048 134 (BL 360663245 14342) BE) (BN 362043982 63872 (BL 361941186 8960) BE)) (BN 363799551 14592 (BN 363289958 22400 (BL 362516192 4224) BE) (BN 364409735 8064 (BL 364017118 25857) BE))) (BN 366768511 13314 (BN 365848975 4612 (BN 365213262 64640 (BL 365017120 63616) BE) (BN 366377184 25344 (BL 365974190 642) BE)) (BN 367695217 19584 (BN 367226785 26630 (BL 366879745 11904) BE) (BN 369649260 14976 (BL 368522535 9344) BE))))) (BN 377946984 32640 (BN 371379404 6402 (BN 370945947 19840 (BN 370219359 640 (BN 370166671 18432 (BL 369843785 20608) BE) (BN 370640654 4736 (BL 370410188 31362) BE)) (BN 371231418 25604 (BN 371204509 8706 (BL 371093377 29700) BE) (BN 371357617 28160 (BL 371238813 8198) BE))) (BN 374602669 30720 (BN 373292683 24448 (BN 373220109 20998 (BL 372131215 27264) BE) (BN 373517837 17926 (BL 373401944 26752) BE)) (BN 375667416 7172 (BN 375529375 25092 (BL 374655357 31360) BE) (BN 377494059 24576 (BL 377011075 12800) BE)))) (BN 386821626 644 (BN 383253466 10882 (BN 381297471 1028 (BN 378202935 17536 (BL 378012830 21760) BE) (BN 381447073 29184 (BL 381327341 12930) BE)) (BN 386671092 2050 (BN 386449214 8068 (BL 385835493 20354) BE) (BN 386761791 9220 (BL 386738350 5638) BE))) (BN 389717192 24836 (BN 389083695 13062 (BN 388782685 31104 (BL 386934917 32384) BE) (BN 389570289 15364 (BL 389280495 63234) BE)) (BN 391107090 6146 (BN 390298515 13190 (BL 390093636 13569) BE) (BN 391396932 20480 (BL 391257624 31364) BE))))))) (BN 448007693 6658 (BN 414268689 14854 (BN 403506390 19968 (BN 398025086 10496 (BN 394529634 29953 (BN 393217274 27520 (BN 392132394 18560 (BL 392030939 17152) BE) (BN 393589088 3584 (BL 393218683 9088) BE)) (BN 395832930 12288 (BN 394942037 16128 (BL 394760153 12164) BE) (BN 396519688 128 (BL 395938824 31232) BE))) (BN 399564407 19716 (BN 399196151 28548 (BN 398764309 63492 (BL 398188781 14848) BE) (BN 399378035 32512 (BL 399363279 384) BE)) (BN 400646366 15490 (BN 400498718 22656 (BL 400374822 1536) BE) (BN 401170264 23808 (BL 400925058 2816) BE)))) (BN 410172092 25984 (BN 406910828 21506 (BN 404389424 7296 (BN 404111745 8961 (BL 403941868 6400) BE) (BN 405009963 14338 (BL 404830249 10240) BE)) (BN 408547743 25345 (BN 408534303 26624 (BL 407254767 18436) BE) (BN 409687443 65286 (BL 409212696 31238) BE))) (BN 411690765 30724 (BN 410865564 8192 (BN 410614389 12928 (BL 410308988 2048) BE) (BN 411495183 22272 (BL 411346826 64514) BE)) (BN 412545934 11520 (BN 412523915 5120 (BL 412170440 7942) BE) (BN 413913926 28288 (BL 413648694 1542) BE))))) (BN 431598285 18944 (BN 425249699 16898 (BN 416959913 31744 (BN 414744986 6144 (BN 414575605 15488 (BL 414354517 20992) BE) (BN 416716606 1920 (BL 415896522 22534) BE)) (BN 422397634 5250 (BN 419116362 16384 (BL 417062298 5376) BE) (BN 424256005 23680 (BL 422718790 4864) BE))) (BN 427817946 5888 (BN 426642803 5248 (BN 425811259 17412 (BL 425644189 1024) BE) (BN 427066904 8194 (BL 426994812 29312) BE)) (BN 429184994 32000 (BN 429017775 11268 (BL 428647859 14336) BE) (BN 431108509 9216 (BL 431080407 64768) BE)))) (BN 442522558 3456 (BN 434173621 64386 (BN 433282266 23040 (BN 432578353 13060 (BL 431988318 21248) BE) (BN 434159166 14598 (BL 433430413 13058) BE)) (BN 438297681 63874 (BN 437137568 64388 (BL 434332770 4352) BE) (BN 441918345 10244 (BL 440323326 22016) BE))) (BN 445622399 26628 (BN 444759324 18688 (BN 444531741 27776 (BL 442847791 3072) BE) (BN 445170827 13312 (BL 444803566 23556) BE)) (BN 447150289 2822 (BN 446566463 7936 (BL 445805535 28416) BE) (BN 447397084 2052 (BL 447283789 4608) BE)))))) (BN 486174095 9732 (BN 466481543 32256 (BN 456964189 25088 (BN 452528191 29696 (BN 451066207 4096 (BN 449804744 32386 (BL 449606825 8704) BE) (BN 451833082 6148 (BL 451764882 65280) BE)) (BN 454880412 8576 (BN 453140500 64000 (BL 452666232 25600) BE) (BN 456620554 30208 (BL 456252513 64128) BE))) (BN 461349452 29568 (BN 458801594 10880 (BN 458079394 15744 (BL 457102230 7168) BE) (BN 460243240 22530 (BL 459862888 22144) BE)) (BN 465522041 1664 (BN 464979262 17665 (BL 461397095 15872) BE) (BN 465735955 14340 (BL 465636140 23046) BE)))) (BN 473167616 24064 (BN 470687348 27648 (BN 468803039 30592 (BN 467709951 63494 (BL 466978914 1280) BE) (BN 470586803 5632 (BL 470157977 17408) BE)) (BN 471152006 24832 (BN 471005103 15360 (BL 470825389 19456) BE) (BN 472207846 26116 (BL 471858256 9473) BE))) (BN 480482976 514 (BN 478684632 14849 (BN 475022801 16640 (BL 474301483 6406) BE) (BN 478997371 7425 (BL 478795714 13696) BE)) (BN 483881136 22528 (BN 480652831 26118 (BL 480627451 20736) BE) (BN 485876365 15617 (BL 485313144 21504) BE))))) (BN 520969232 22532 (BN 503472301 11264 (BN 492058474 32001 (BN 489868292 29315 (BN 489749142 64512 (BL 486217152 14080) BE) (BN 491659114 24960 (BL 491103154 30080) BE)) (BN 492854144 64006 (BN 492764255 14208 (BL 492107981 21120) BE) (BN 500801545 16385 (BL 493668002 63746) BE))) (BN 515227210 12544 (BN 510373997 13824 (BN 505554573 17664 (BL 503652015 16896) BE) (BN 512406367 30214 (BL 511372880 9472) BE)) (BN 518100680 31616 (BN 518016558 7680 (BL 517539322 20096) BE) (BN 519572682 7424 (BL 518532995 6018) BE)))) (BN 535279469 26112 (BN 526815883 26374 (BN 525390989 15616 (BN 522477570 63744 (BL 521675074 10881) BE) (BN 526238380 23552 (BL 525537892 28928) BE)) (BN 533041145 6656 (BN 531369850 18304 (BL 529697279 13830) BE) (BN 534807420 2304 (BL 533538244 19328) BE))) (BN 550165331 11776 (BN 542807772 11136 (BN 539236895 14216 (BL 536539625 17920) BE) (BN 549822596 11648 (BL 549245718 9728) BE)) (BN 579974772 10112 (BN 558885292 512 (BL 556061878 63750) BE) (BN 632504779 13056 (BL 599490833 19712) BE)))))))
def RtT9_0 := nd (nd (nd (nd (nd (lf 0x210801001f83 [0x7100107040b,0x50c060c0202,0x5170617030c,0xd0317]) (lf 0x2310801001f43 [0x40b050d0203])) (nd (lf 0x2310801001fc3 [0x310050d040b,0x30c050c0203,0x1103170517]) (nd (lf 0x410801001fc3 [0x50d040b030c,0x12e00190710,0x1103170517]) (lf 0x1430801001f63 [0x602050d0019,0x10c020c])))) (nd (nd (lf 0x1430801001fe3 [0x602050d0019,0x203040b0310,0x10c020c0107,0x110013]) (nd (lf 0x2430801001f63 [0x50d040b030a,0x10702030602,0x314]) (lf 0x3430801001fe3 [0x50d040b030c,0x1903100602,0x31705170617]))) (nd (lf 0x1630801001be3 [0x50d022e0013,0x20c0206000b,0x217]) (nd (lf 0x540801001fe3 [0x602050d0019,0x2060317030c,0x106]) (lf 0x1540801001fe3 [0x50d040b030a,0x71003140602,0x1301070203,0x11]))))) (nd (nd (nd (lf 0x2540801001fe3 [0x50d040b0314,0x310030c0602,0x22e01070203,0x110013012e]) (lf 0x428c01001f63 [0x30d030c040b,0x31406140602,0x130317])) (nd (lf 0x2428c01001f63 [0x602030d0019,0x30a]) (nd (lf 0x2628c01001b63 [0xb06020207,0x214020a]) (lf 0x2728c01001763 [0xb06020107])))) (nd (nd (lf 0x548c01001f63 [0x30c06020019,0x3170205]) (nd (lf 0x1548c01001f63 [0x602030a040b,0x70d02030314]) (lf 0x2548c01001f63 [0x6020314040b,0x13070d030c]))) (nd (lf 0x2318c01001f43 [0x12e0203040b,0x1100106070d,0x20614060a]) (nd (lf 0x418c01001fc3 [0x510040b012e,0x190018070d,0x3170517]) (lf 0x2328c01001f63 [0x30d0602040b,0x1070106012e,0x317030a030c,0x110001e0314,0x50c060a0203,0x5170614])))))) (nd (nd (nd (nd (lf 0x428c01001fe3 [0x40b030d012e,0x30c05100602,0x31405170614,0x130317]) (lf 0x2428c01001fe3 [0x30d05100019,0x203040b0602,0x18030a])) (nd (lf 0x2628c01001be3 [0x51006020207,0x20a050c000b,0x2140517]) (nd (lf 0x2728c010017e3 [0x60205100107,0x10c0401000b,0x117]) (lf 0x1438c01001f63 [0x602030a040b,0x130305070d,0x31403170106])))) (nd (nd (lf 0x3438c01001f63 [0x602030c040b,0x70d00190106,0x2003170614]) (nd (lf 0x548c01001fe3 [0x60201060019,0x2050510030c]) (lf 0x1548c01001fe3 [0x510040b030a,0x70d03140602,0x180203]))) (nd (lf 0x2548c01001fe3 [0x6020314012e,0x2030510040b,0x180013070d]) (nd (lf 0x511001001fc3 [0x50c0317040b,0x106070d0710,0x12e]) (lf 0x321001001f63 [0x40b0602050c,0x5170310030d]))))) (nd (nd (nd (lf 0x2321001001f63 [0x40b0602050c,0x1070307030d,0x5170310]) (nd (lf 0x2321001001fe3 [0x602030d012e,0x1070310040b,0x31403170517]) (lf 0x521001001fe3 [0x30d0317050c,0x710040b0602,0x12e0106]))) (nd (lf 0x2521001001fe3 [0x30d050c000f,0x20307100602,0x12e]) (nd (lf 0x2621001001be3 [0x6020207050c,0x517000e0710]) (lf 0x27210010017e3 [0x602010c0107,0x1170710000b])))) (nd (nd (lf 0x1531001001fe3 [0x602012e000f,0x3100203050c,0x10a000e070d,0x130117]) (nd (lf 0x3531001001fe3 [0x6020317012e,0x70d0310040b]) (lf 0x17310010017e3 [0x602010c0106,0x107070d000b,0x7100117]))) (nd (lf 0x540c81001f73 [0x5100317030c,0x60b0602050d,0x10506010205,0x2130403040b]) (nd (lf 0x1540c81001f73 [0x50d0510030a,0x60106020314,0x213020b040b,0x10702030403]) (lf 0x2540c81001f73 [0x50d05100314,0x6010602030c,0x213020b040b,0x21702030403,0x60b]))))))
def RtT9_1 := nd (nd (nd (nd (nd (lf 0x2428c81001f33 [0x602030a0107,0x20b03050601,0x60b02030617,0x3140613]) (lf 0x548c81001f73 [0x50d0317030c,0x507060b0602,0x10502050601,0x613041e040b,0x51004070403,0x11e0107])) (nd (lf 0x1548c81001f73 [0x3140602030a,0x5070601050d,0x60b020b040b,0x4030613041e,0x51004070203,0x11e0213]) (nd (lf 0x2548c81001f73 [0x50d06020314,0x5070601030c,0x20b040b060b,0x613041e0107,0x40702030403,0x21302170510,0x11e]) (lf 0x1748c81001f73 [0x602030a011e,0x30506010107,0x6130617020b,0x317060b0203,0x2130314])))) (nd (nd (lf 0x2748c81001f73 [0x30c0602011e,0x20b06010107,0x60b06170613,0x203030a0614,0x21303170314]) (nd (lf 0x2428c81001fb3 [0x6020510030a,0x30506010107,0x20b002e060b,0x20306170613,0x314010c]) (lf 0x1438c81001f73 [0x602050d030a,0x30506010106,0x11e0613040b,0x1070407020b,0x20304030517,0x20c0110060b,0x1e03140317,0x213]))) (nd (lf 0x3438c81001e73 [0x50d06020106,0x613060b0601,0x5140614001e,0x40701100020,0x10a]) (nd (lf 0x3438c81001f73 [0x106050d030c,0x613060b0602,0x107040b0020,0x10a0601011e,0x40305140614,0x31401100407,0x317]) (lf 0x1638c81001b73 [0x602050d002e,0x706010006]))))) (nd (nd (nd (lf 0x3638c81001b73 [0x6050d002e,0x70203020b]) (nd (lf 0x548c81001ff3 [0x50d030c0106,0x510060b0602,0x205012e0601,0x41e06130107,0x11e0407]) (lf 0x1548c81001ff3 [0x6020510030a,0x50d03140601,0x613060b0006,0x20b0507041e,0x403040b011e,0x21304070203,0x107]))) (nd (lf 0x2548c81001ff3 [0x50d0314012e,0x51006010602,0x107020b060b,0x30c041e0613,0x604070203,0x11e0213]) (nd (lf 0x1431081001ef3 [0x310010a010c,0x601050d0602,0x613020b0105,0x203060b0617,0x3170517002e,0x40b0413]) (lf 0x1531081001f73 [0x50d050c0314,0x61306010602,0x107020b040b,0x4130217010a])))) (nd (nd (lf 0x1531081001df3 [0x50d0602012e,0x60b03100601,0x40a050c0413,0x40b]) (nd (lf 0x1531081001ff3 [0x602012e0019,0x601050c050d,0x314020b0310,0x203000f0217,0x10a040a0107,0x21304130117]) (lf 0x2531081001f73 [0x50d050c0314,0x20b06010602,0x203040b0413,0x10a]))) (nd (lf 0x3531081001df3 [0x50d0602012e,0x60b03100601,0x40b040a0413]) (nd (lf 0x3531081001ff3 [0x50d0317012e,0x613060b0602,0x31006010121,0x31404070214,0x40b0413040a,0x20b0213]) (lf 0x3631081001b73 [0x50d020b050c,0x51705140602,0x214])))))) (nd (nd (nd (nd (lf 0x1731081001773 [0x10c0602050d,0x613060b0601,0x11406140617,0x16000b]) (lf 0x17310810017f3 [0x50d06020310,0x106010c0601,0x160613060b,0x1170614000b,0x700030114,0x13040a])) (nd (lf 0x3541081001ef3 [0x50d010c0317,0x601060b0602,0x61002060710,0x40b01060613,0x20b]) (nd (lf 0x3439081001ef3 [0x10c0310010a,0x601050d0602,0x617060b0105,0x51405170613,0x40b04130317,0x20b]) (lf 0x1539081001df3 [0x60203100105,0x2e0601050d,0x413060b0613,0x40b])))) (nd (nd (lf 0x3539081001df3 [0x6020310050a,0x3170601050d,0x413002e060b,0x40b01050221,0x1210613]) (nd (lf 0x3539081001ff3 [0x60203170019,0x1050310050d,0x413040b0121,0x2e0403000f,0x213]) (lf 0x1639081001bf3 [0x50a0213002e,0x20b0505050d,0x514000c0206,0x217]))) (nd (lf 0x3639081001b73 [0x20b050d000f,0x50a]) (nd (lf 0x3639081001bf3 [0x20b002e000f,0x510050a050d]) (lf 0x17390810017f3 [0x602050d0120,0x10501060601,0x16060b000b,0x40c010a0003,0x1170613]))))) (nd (nd (nd (lf 0x549081001ef3 [0x602050d0019,0xf01050317,0x10a07100601,0x40b01060206]) (nd (lf 0x1321881001bb3 [0x10d]) (lf 0x3421881001bb3 [0x10d]))) (nd (lf 0x1431881001b73 [0x6010602000e,0xc030a0407]) (nd (lf 0x1431881001af3 [0x40b03100407,0x16000e0403,0x4140417]) (lf 0x1431881001bf3 [0x40b0310000e,0x602030a0403,0x50d04070601,0xc0016])))) (nd (nd (lf 0x2431881001b73 [0x6020407030a,0x3000b0601,0x31404140417]) (nd (lf 0x3431881001af3 [0x60203100407,0x417030c0601,0x200414]) (lf 0x3431881001bf3 [0x3100407030c,0xe0403040b,0x41404170020,0x317]))) (nd (lf 0x17318810013f3 [0x60602002e,0x6010007]) (nd (lf 0x541881001bf3 [0x403040b000e,0x3170710030c,0x50006]) (lf 0x1541881001bf3 [0x3140407030a,0x7100403040b,0x50d06010602,0x17000c0006]))))))
def RtT9_2 := nd (nd (nd (nd (nd (lf 0x2541881001bf3 [0x403040b000e,0x120710030c,0x40706010602,0x3100006050d]) (lf 0x1439881001b73 [0x6010602000e,0x30a])) (nd (lf 0x1439881001af3 [0x31006020407,0x30a000e0601,0x4140417]) (nd (lf 0x1439881001bf3 [0x6020310000e,0x407030a0601,0x160003000b,0xc]) (lf 0x2439881001b73 [0x6020407030a,0x3000b0601,0x31404140417])))) (nd (nd (lf 0x3439881001af3 [0x60203100407,0x16030c0601,0x2004140417]) (nd (lf 0x3439881001bf3 [0x3100407030c,0xe06010602,0x41700160020,0x3170414]) (lf 0x1739881001373 [0x706010602,0xa002e0006,0x14]))) (nd (lf 0x17398810013f3 [0x6010602002e,0x70006]) (nd (lf 0x549881001bf3 [0x6010602000e,0x60005030c,0x40703170410,0x50d]) (lf 0x1549881001bf3 [0x3140407030a,0x71006010602,0x4100003000b,0x6]))))) (nd (nd (nd (lf 0x2549881001bf3 [0x6010602000e,0x7100012002e,0x3000b030c,0x31004100314]) (lf 0x7250c1001773 [0x602010a0107,0x61701050601,0xb0613060b])) (nd (lf 0x5450c1001e73 [0x31706020019,0x10a06010105,0xe070d000f,0x40b]) (nd (lf 0x7050c1001ee3 [0x6020106020b,0x1050510010a,0x16]) (lf 0x7250c1001ef3 [0x30d06020106,0x10a05100601,0x207060b0105,0x16002c0613,0x213020b])))) (nd (nd (lf 0x35350c1001c73 [0x60101160602,0x613060b070d,0x21]) (nd (lf 0x35350c1001e73 [0x60106020317,0x613050a070d,0x2130214060b]) (lf 0x16350c1001a73 [0x60106020006]))) (nd (lf 0x37350c1001e73 [0x10a06020106,0x105010c0601,0x613060b070d,0x200317]) (nd (lf 0x7550c1001ef3 [0x60205100105,0x70d06010317,0x613060b000e,0x16010a]) (lf 0x37550c1001ef3 [0x31406020106,0x510070d0601,0x60b010a000e,0x613])))))) (nd (nd (nd (nd (lf 0x7650c1001af3 [0x510000f020b,0x2070602070d,0x2140217000c,0x10a]) (lf 0x37650c1001af3 [0xf05100213,0x2170207070d,0x10a0214])) (nd (lf 0x7250c10017f3 [0x10a05100047,0x30d01050107,0x617040c0602,0xb00130117]) (nd (lf 0x35350c1001d73 [0x6010602050a,0x60b0317070d,0x40c040b0613,0x4030021]) (lf 0x35350c1001f73 [0x60203170019,0x601070d050a,0x40c0105040b,0x403000f0114,0x213000e])))) (nd (nd (lf 0x16350c1001b73 [0x60602002e,0x70d050a0601,0xc02070047]) (nd (lf 0x36350c1001b73 [0x602050a0006,0xc070d0601,0x2070203020b]) (lf 0x5450c1001ef3 [0x60201060019,0x40b01050510,0x10a06010317,0x70d0403000f,0xe]))) (nd (lf 0x25450c1001ef3 [0x510010a0314,0x70d06010602,0xe0613020b,0x2030006060b,0x213]) (nd (lf 0x27290c1001773 [0x602010a0107,0x60b01050601,0x613060d0617,0xb]) (lf 0x17590c1001573 [0x114010a0602,0x60b070d0601,0x613]))))) (nd (nd (nd (lf 0x272d0c1001ef3 [0x602030d0120,0x613060b0601,0x6140617010c,0x317010a0016,0x213020b0314]) (nd (lf 0x363d0c1001a73 [0x60106020006,0x207]) (lf 0x175d0c1001ef3 [0x31406020106,0x510070d0601,0x10c0613060b]))) (nd (lf 0x275d0c1001ef3 [0x60106020106,0x60b070d0120,0x10c05100613,0x20b0213]) (nd (lf 0x272d0c10017f3 [0x60201070120,0x60b010c0601,0x617000b0613,0x11700030614,0x130114]) (lf 0x363d0c1001b73 [0x602020b0006,0xa070d050c,0x20702030601])))) (nd (nd (lf 0x154d0c1001ef3 [0x60205100314,0x70d0601010c,0x60613060b,0x213020b]) (nd (lf 0x354d0c1001ef3 [0x60106020106,0x60b070d0120,0x10c05100613,0x20b0213010a]) (lf 0x3258c1001b73 [0x110]))) (nd (lf 0x24358c1001b73 [0x110]) (nd (lf 0x15458c1001bf3 [0x30a04130006,0x4070314070d,0x40b0047]) (lf 0x54d8c1001b73 [0x30c040b000f,0x31706010602,0x50407]))))))
def RtT9_3 := nd (nd (nd (nd (nd (lf 0x154d8c1001b73 [0x602040b030a,0x40306010314,0x407070d]) (lf 0x254d8c1001b73 [0x602040b0314,0x4030601030c,0x120407070d])) (nd (lf 0x32d8c1001b73 [0x110]) (nd (lf 0x43d8c1001b73 [0x110]) (lf 0x243d8c1001b73 [0x110])))) (nd (nd (lf 0x154d8c1001bf3 [0x602030a0006,0x601070d040b,0x2e04070403,0x510]) (nd (lf 0x27215010017f3 [0x60201070019,0x10c07100601,0xf000b0117,0x60d00030105,0x130006]) (lf 0x1731501001773 [0xb06020019,0x70d000f0601,0x107000e]))) (nd (lf 0x17315010017f3 [0x31006020019,0x10c06010105,0xb070d0117,0xe0003000f,0x1300160107]) (nd (lf 0x1541501001cf3 [0x602010c010a,0x710060b0601,0x60613070d,0x20b0610]) (lf 0x7255010017f3 [0x114010a0047,0x60207100107,0x1100610060d,0xb0013]))))) (nd (nd (nd (lf 0x37355010017f3 [0x60201140120,0xb070d0601,0x160613060b,0x10a00030310,0x107]) (nd (lf 0x27295010017f3 [0x10c01140107,0x601060b0602,0x613002e0710,0x4170610060d,0xb0013]) (lf 0x1739501001773 [0x60106020112,0x60b010c0114,0x107070d0121,0x4170613000b]))) (nd (lf 0x17395010017f3 [0x602010c0121,0x60b070d0601,0x31006130016,0x1140003000b,0x4170107]) (nd (lf 0x3549501001cf3 [0x117010c0602,0x70d07100601,0x60613060b,0x610]) (lf 0x2421043001e73 [0x502010c0610,0x30d010a0601,0x3170517])))) (nd (nd (lf 0x521043001f73 [0x5020317050c,0x6010610030d]) (nd (lf 0x2521043001f73 [0x30d0314050c,0x60106100502,0x10a0207]) (lf 0x2621043001b73 [0x502050c0207,0x514001e0601,0x2140517]))) (nd (lf 0x2721043001773 [0x50206100107,0x6140601010c,0x1140117]) (nd (lf 0x3541043001e73 [0x60106100317,0x240502010c]) (lf 0x1761043001373 [0x3106010502,0x7070d050c,0x2100014])))))) (nd (nd (nd (nd (lf 0x2629043001b73 [0x6010502000e,0x50a]) (lf 0x2729043001773 [0x10a06100107,0x306010502,0x11401170614])) (nd (lf 0x549043001e73 [0x61005020105,0x40303170601,0x10a000e]) (nd (lf 0x3219843001b53 [0x102]) (lf 0x1419843001b53 [0x102])))) (nd (nd (lf 0x549843001b73 [0x4030601000f,0x3170004030c,0x407]) (nd (lf 0x1549843001b73 [0x6010403030a,0x70d000b0314,0x407]) (lf 0x2549843001b73 [0x60103140403,0x70d0004030c,0x407]))) (nd (lf 0x2711503001773 [0x60106100105,0x10c070d0103,0x107000e0117]) (nd (lf 0x1541503001c73 [0x6010610010a,0x20b0702010c,0x70d]) (lf 0x715503001773 [0x10a06100103,0x70d06010114,0x107]))))) (nd (nd (nd (lf 0x2719503001773 [0x11406100103,0x70d0601010c,0x107]) (nd (lf 0x3549503001c73 [0x10c06010610,0x70d07020117]) (lf 0x1769503001373 [0x2106010012,0x70d0702]))) (nd (lf 0x519023001f63 [0x3020317050a,0x70d040b]) (nd (lf 0x2719023001763 [0xb01050103,0x107010a070d]) (lf 0x549023001e63 [0x702040b0105,0x70d0317])))) (nd (nd (lf 0x2421063001e73 [0x502010c0019,0x3170610030d,0x10a0517]) (nd (lf 0x521063001f73 [0x5020317050c,0x40b0601030d,0x4180610020b,0x218]) (lf 0x2521063001f73 [0x30d050c0314,0x40b06010502,0x418010a0610,0x20b0218]))) (nd (lf 0x2621063001b73 [0x502050c0207,0x51705140601,0x214]) (nd (lf 0x2621063001f73 [0x30d050c0218,0x514020b0502,0x31403170517,0x1f]) (lf 0x2721063001773 [0x10c05020107,0x614060b0601,0x11401170610,0x18]))))))
def RtT9_4 := nd (nd (nd (nd (nd (lf 0x3541063001e73 [0x502010c0317,0x70d040b0601,0x60b0610]) (lf 0x1651063001f73 [0x50c01050218,0x70d020b0502,0x6010a])) (nd (lf 0x2651063001f73 [0x50c02180019,0x314020b0502,0x70d]) (nd (lf 0x1761063001373 [0x10c05020018,0x140007070d]) (lf 0x2629063001b73 [0x6010502000e,0x50a])))) (nd (nd (lf 0x2629063001f73 [0x50202180019,0x30d001f]) (nd (lf 0x2729063001773 [0x50200190107,0x10a00180105,0x117000b0610]) (lf 0x549063001e73 [0x10505020019,0xe06010317,0x10a]))) (nd (lf 0x549863001b73 [0x50601000f,0x4070317030c]) (nd (lf 0x1549863001b73 [0x601030a0403,0x502070d0314,0x407]) (lf 0x2549863001b73 [0x60103140403,0x407070d030c,0x12]))))) (nd (nd (nd (lf 0x2729863001773 [0x180107040b,0x10c01030702,0x1140117010a]) (lf 0x549863001f73 [0x30c04180019,0x3170502040b,0x70d])) (nd (lf 0x1549863001f73 [0x502030a0418,0x70d040b0314,0x340103]) (nd (lf 0x2549863001f73 [0x40b03140418,0x70d0502030c,0x340117]) (lf 0x2711523001773 [0x60101030019,0x70d0117010c,0x107000e])))) (nd (nd (lf 0x1541523001c73 [0x601010c010a,0x70d0702060b,0x610]) (nd (lf 0x715523001773 [0x114010a0103,0x70d000b0601,0x60b06100018,0x107]) (lf 0x2719523001773 [0x10c01140103,0x60b070d0601,0x1801070610]))) (nd (lf 0x3549523001c73 [0x117010c0601,0x60b070d0702,0x610]) (nd (lf 0x1769523001373 [0x514010c0018,0x70d07020517,0xa00070003]) (lf 0x715923001773 [0x1050103040b,0x70d010a0018,0x1170107])))))) (nd (nd (nd (nd (lf 0x755923001573 [0x117010a040b,0x70d00180702]) (lf 0x3755923001573 [0x114010a040b,0x70d07020018])) (nd (lf 0x2719923001773 [0x1801030019,0x107070d]) (nd (lf 0x2319023001f63 [0x302050a002e,0x40c070d0505,0x31705140206,0x4]) (lf 0x419023001ee3 [0x302010a002e,0x105070d0610,0x317])))) (nd (nd (lf 0x519023001fe3 [0x302050a0206,0x70d002e0610,0x40c]) (nd (lf 0x27190230017e3 [0x610010a0103,0x70d0105000b,0x107]) (lf 0x3439023001e63 [0x702010c040b,0x1050206070d,0x317]))) (nd (lf 0x3539023001f63 [0x317050a002e,0x21070d0702]) (nd (lf 0x549023001ee3 [0x61001050206,0x70d03170702,0x40b]) (lf 0x2428c63001f73 [0x30d0502030a,0x30504060601,0x61704180404,0x403040b0517,0x314010c020c,0x4020b0018,0x103]))))) (nd (nd (nd (lf 0x2628c63001b73 [0x50206010207,0x50c002e0006,0x5140517050a,0x20a04040410,0x214]) (nd (lf 0x1548c63001f73 [0x502030a0006,0x40b070d0601,0x400180403]) (lf 0x2421063001ef3 [0x6010502002e,0x10a030d0105,0x10c0610040b,0x31705170617]))) (nd (lf 0x521063001ff3 [0x6010317050c,0x610030d0502,0x20b040b060b,0x602180418,0x214040a002e]) (nd (lf 0x2521063001ff3 [0x30d042e0019,0x50c01050502,0x604180610,0x218010a]) (lf 0x2621063001bf3 [0x6010207002e,0x50c06100502,0x5170514000a,0x2140217])))) (nd (nd (lf 0x27210630017f3 [0x6010107002e,0x10c06100502,0x6140617040a,0x1801140117]) (nd (lf 0x1731063001773 [0x50206010006,0xb070d010c,0x107]) (lf 0x3541063001ef3 [0x601002e0206,0x40b06100502,0x70d]))) (nd (lf 0x2629063001bf3 [0x5020610000e,0x207050a0601,0xc]) (nd (lf 0x27290630017f3 [0x10a06100107,0x10506010502,0x617060b000b,0x40c00160618,0x180117]) (lf 0x3439063001e73 [0x20605020020,0x21801050601,0x514070d010c]))))))
def RtT9_5 := nd (nd (nd (nd (nd (lf 0x3539063001d73 [0x601050a002e,0x70d0502]) (lf 0x3539063001f73 [0x50203170019,0x60100210105,0xe002e070d])) (nd (lf 0x1739063001773 [0x60601002e,0xb010a0502,0x107070d]) (nd (lf 0x549063001ef3 [0x50202060019,0x61003170105,0xe070d0601,0x10a]) (lf 0x1439863001b73 [0x6010403030a,0x3050006070d,0x31403170407])))) (nd (nd (lf 0x3439863001a73 [0x606010403,0x4140407070d,0x20]) (nd (lf 0x3439863001b73 [0x601030c0403,0xf0006070d,0x41404070020,0x317]) (lf 0x549863001bf3 [0x6010006000f,0x6100005030c,0x4070317070d]))) (nd (lf 0x1549863001bf3 [0x610030a0403,0x70d03140601,0x4070502]) (nd (lf 0x2549863001bf3 [0x6010403002e,0x70d06100314,0x30c000b0012,0x407]) (lf 0x7150e3001773 [0x601050103,0x70d010a0601,0x41006170418,0x107000b]))))) (nd (nd (nd (lf 0x270d0e3001e63 [0x702020b0006,0x70d]) (nd (lf 0x271d0e3001e73 [0x60100200006,0x70d0302]) (lf 0x271d0e3001773 [0x603020020,0x418070d0601,0x107010c0614,0x114]))) (nd (lf 0x154d0e3001e73 [0x60103140006,0x10c070d0702]) (nd (lf 0x27115230017f3 [0x10300060019,0x11701050610,0x10c0601070d,0x180107000e]) (lf 0x1731523001773 [0x70206010019,0xf000b070d,0x107000e0103])))) (nd (nd (lf 0x1541523001cf3 [0x601010a0006,0x70d07020610,0x10c]) (nd (lf 0x7155230017f3 [0x10a06100103,0x70d06010114,0x60b0618000b,0x1601070602,0x18]) (lf 0x3735523001773 [0x10a06010006,0xb070d0702,0x10701030016]))) (nd (lf 0x27195230017f3 [0x1140103002e,0x70d06100601,0x180107010c]) (nd (lf 0x1739523001773 [0x10c06010006,0x70d01140702,0x103000b0016,0x107]) (lf 0x3549523001cf3 [0x601002e0006,0x70d07020610])))))) (nd (nd (nd (nd (lf 0x529044001ef3 [0x50200050317,0x601040c030d,0x10602060710,0x2e]) (lf 0x2629044001af3 [0x502040a0207,0x40507100601,0x2170517])) (nd (lf 0x27290440016f3 [0x601040c0107,0x507100502,0x1170617002e]) (nd (lf 0x1539044001cf3 [0x50601002e,0x502]) (lf 0x3539044001cf3 [0x40a0601002e,0x3100502])))) (nd (nd (lf 0x3539044001ef3 [0x5020005002e,0x31003170601,0x70d]) (nd (lf 0x1639044001af3 [0x20605020020,0x207070d0601,0x405000c0217,0x16]) (lf 0x17390440016f3 [0x5020601002e,0x501060020,0x16]))) (nd (lf 0x2621444001bf3 [0x50205170207,0x710020c0601,0x2e0510050d,0x140006]) (nd (lf 0x1431444001ef3 [0x31000050517,0x601020c0502,0x103070d]) (lf 0x1631444001b73 [0x20c06010006,0x207070d0502,0x14]))))) (nd (nd (nd (lf 0x17614440013f3 [0x1a0601020c,0x70d07100502,0x1600070517,0x90010]) (nd (lf 0x2629444001bf3 [0x50202070405,0x710020c0601,0x40a0006002e,0x17]) (lf 0x27294440017f3 [0x50201070005,0x7100601060c,0x1100610002e]))) (nd (lf 0x3539444001df3 [0x6010121022e,0x60c00050502,0x40a070d]) (nd (lf 0x1639444001b73 [0x50206010514,0x207070d020c,0x40a0006]) (lf 0x1639444001bf3 [0x60100060405,0x20c070d0502,0x40a02070310,0x17])))) (nd (nd (lf 0x17694440013f3 [0x60105020024,0x5070d0710,0x160007]) (nd (lf 0x1319844001bd3 [0x102]) (lf 0x1439844001af3 [0x20a03100403,0x205070d0601,0x31704170407]))) (nd (lf 0x1539844001b73 [0x40c04030314,0x407070d0601,0x20a]) (nd (lf 0x15398440019f3 [0x6010403002e,0x407040c070d]) (lf 0x1539844001bf3 [0x2050403002e,0x310070d0601,0x407000b040c,0x17020a]))))))
def RtT9_6 := nd (nd (nd (nd (nd (lf 0x2539844001b73 [0x60104030314,0x407070d040c,0x20a]) (lf 0x35398440019f3 [0x6010403002e,0x407070d0310])) (nd (lf 0x3539844001bf3 [0x3170403002e,0x310070d0601,0x31404070021]) (nd (lf 0x17398440013f3 [0x40c06010006,0x7070d0003]) (lf 0x3549844001af3 [0x60103170403,0x407070d0710,0x6])))) (nd (nd (lf 0x7150c40016f3 [0x40c05100103,0x602070d0601,0x61701070005,0x117]) (nd (lf 0x35350c4001c73 [0x7020601002e,0x70d]) (lf 0x35350c4001e73 [0x40c00050317,0x70d07020601,0x21]))) (nd (lf 0x7154c4001773 [0x1140103060c,0x107070d0601]) (nd (lf 0x37654c4001373 [0x70206010024,0x70003070d]) (lf 0x7154c40017f3 [0x50103002e,0x60c05100601,0x107070d]))))) (nd (nd (nd (lf 0x16354c4001b73 [0x20c06010514,0x70d07020016,0x40a02070203]) (lf 0x35454c4001cf3 [0x60105100024,0x70d01170702])) (nd (lf 0x37654c40013f3 [0x6010005002e,0x70d07020510,0x700030024]) (nd (lf 0x27194c4001773 [0x114060c0103,0x70d00040601,0x107]) (lf 0x17694c4001373 [0x70206010024,0x70003070d])))) (nd (nd (lf 0x163d4c4001973 [0x601020c0016,0x203070d0702,0x207]) (nd (lf 0x271d4c40017f3 [0x302002e0121,0x117070d0601,0xa0107]) (lf 0x163d4c4001b73 [0x20c06010517,0x70d07020016,0x20702030014]))) (nd (lf 0x7158c4001b73 [0x40c00060601,0x303070d0302,0x30314003c,0x20a]) (nd (lf 0x27158c4001b73 [0x30206010006,0x3070d040c]) (lf 0x35458c4001a73 [0x70206010006,0x4070403070d])))))) (nd (nd (nd (nd (lf 0x7558c4001b73 [0x40c06010006,0xb070d0702,0x14]) (lf 0x17558c4001b73 [0x31406010016,0x70d0702040c,0x302003c020a,0x30d002a])) (nd (lf 0x27558c4001b73 [0x1606010317,0x70d0702040c,0x14]) (nd (lf 0x37558c4001b73 [0x40c06010006,0x70d07020314,0x2a003c]) (lf 0x3158c4001b73 [0x110])))) (nd (nd (lf 0x7158c4001bf3 [0x601040c0006,0x303070d0302,0x160310]) (nd (lf 0x5358c4001b73 [0x110]) (lf 0x25358c4001b73 [0x110]))) (nd (lf 0x271d5040016f3 [0x10306010024,0x117070d0710,0x2e00060107]) (nd (lf 0x173d504001673 [0x70206010024,0x70d]) (lf 0x173d5040016f3 [0x1170601002e,0x1607020020,0x70d]))))) (nd (nd (nd (lf 0x3219864001bd3 [0x102]) (nd (lf 0x3439864001af3 [0x60104030020,0x20c070d0005,0x41700160407]) (lf 0x15398640019f3 [0x31004030005,0x407070d0601]))) (nd (lf 0x35398640019f3 [0x601040a0403,0x70d03170310,0x500160407,0x21]) (nd (lf 0x3539864001bf3 [0x31704030005,0x70d03100601,0x2100160407]) (lf 0x1739864001373 [0x6040a0032,0x706010405])))) (nd (nd (lf 0x17398640013f3 [0x60601002e,0x70d00200003,0x7]) (nd (lf 0x549864001af3 [0x60104030005,0x607100317,0x407070d]) (lf 0x153d0e4001c73 [0x601040c0005,0x70d0702]))) (nd (lf 0x16354e4001973 [0x7020601002e,0x70d020a]) (nd (lf 0x271d4e4001df3 [0x60a0121002e,0x70d06010302,0x117]) (lf 0x271d4e40017f3 [0x51001030405,0x70d01170601,0x414000c0107]))))))
def RtT9_7 := nd (nd (nd (nd (nd (lf 0x3501814301b63 [0x101]) (lf 0x541814301a73 [0x702040b0005,0x403070d0317,0x407])) (nd (lf 0x3101814301ee3 [0x101]) (nd (lf 0x611814301af3 [0x30205010006,0x6100005070d,0x50b0303]) (lf 0x27118143016f3 [0x61004060103,0x10b0405040a,0x107070d0701])))) (nd (nd (lf 0x2711814301ef3 [0x3020610003a,0x406070d010b,0x701040a0405]) (nd (lf 0x3531814301c73 [0x70205010016,0x50b070d]) (lf 0x3531814301e73 [0x50100050317,0x50b070d0702]))) (nd (lf 0x3631814301a73 [0x500060501,0x702050b020c,0x317070d]) (nd (lf 0x651814301af3 [0x31706100005,0x7010702050b,0x70d]) (lf 0x270d4d4301c73 [0x30100210016,0x70d0702]))))) (nd (nd (nd (lf 0x365d4d4301c73 [0x70201140012,0x70d0701]) (nd (lf 0x276d4d4301673 [0x70107020012,0x16070d0114]) (lf 0x365d8d4301a73 [0x70203140006,0x410070d0701]))) (nd (lf 0x3101814301be3 [0x101]) (nd (lf 0x3501814301be3 [0x101]) (lf 0x3531814301973 [0x317040a040b,0x403070d0702,0x210407])))) (nd (nd (lf 0x3531814301b73 [0x5040b0317,0x403070d0702,0x210407]) (nd (lf 0x541814301af3 [0x5040b0006,0x31707020610,0x4070403070d]) (lf 0x270d4d4301d73 [0x3010021002e,0x70d0702060a,0x117]))) (nd (lf 0x274d4d4301c73 [0x702020c0012,0x70d0701]) (nd (lf 0x276d4d4301973 [0x21020c0016,0x70d07010702]) (lf 0x270d4d4301773 [0x117060a010b,0x103070d0702,0x414000c0107])))))) (nd (nd (nd (nd (lf 0x254d4d4301c73 [0x702020c0012,0x70d0701]) (lf 0x27095143016f3 [0x10b06100012,0x114070d0702,0x1070103])) (nd (lf 0x3109824301b63 [0x101]) (nd (lf 0x27198343016f3 [0x10b01030020,0x40c070d0701,0x1601070406,0x114]) (lf 0x27099743016f3 [0x20010b0006,0x103070d0702,0x240107])))) (nd (nd (lf 0x1639974301a73 [0x702020a0517,0x210070d0701]) (nd (lf 0x7055343016f3 [0x6100114010b,0x70d0702040c,0x1601070103]) (lf 0x270d5343016f3 [0x20010b0006,0x103070d0702,0x240107]))) (nd (lf 0x1309805401be3 [0x101]) (nd (lf 0x17398054013f3 [0xb00160005,0x40c070d0702,0x700030417]) (lf 0x3058c5401b73 [0x110]))))) (nd (nd (nd (lf 0x15458c54018f3 [0x70205100005,0x16070d0701]) (nd (lf 0x7055054014f3 [0x710040c010b,0x103070d0702,0x60107]) (lf 0x37355054014f3 [0x70200200006,0x16070d0701,0xa]))) (nd (lf 0x37655054010f3 [0x70d07010702,0x1600050710]) (nd (lf 0x3101815401be3 [0x101]) (lf 0x1731815401373 [0xb0414040a,0x3070d0702,0x2000070016])))) (nd (nd (lf 0x17318154013f3 [0xb00200006,0x16070d0702,0x70003]) (nd (lf 0x3109825401be3 [0x101]) (lf 0x1309825401be3 [0x101]))) (nd (lf 0x17398254013f3 [0x40c000b0006,0x70d07020021,0x70003]) (nd (lf 0x35458e5401873 [0x70107020217,0x120021070d,0x16]) (lf 0x35458e54018f3 [0x70200200006,0x70d00160701]))))))
def RtT9 : BTree NodeData := nd (nd (nd RtT9_0 RtT9_1) (nd RtT9_2 RtT9_3)) (nd (nd RtT9_4 RtT9_5) (nd RtT9_6 RtT9_7))
def RtM9 : BST := BN 411496604 5251 (BN 353785773 36870 (BN 317989672 4102 (BN 292216468 65152 (BN 262224974 61312 (BN 227436497 41604 (BN 200383530 27010 (BN 181280403 42880 (BN 169861955 28544 (BL 133117818 50560) (BL 177562908 17792)) (BN 192643969 60288 (BL 191293946 25346) (BL 195971902 36740))) (BN 222907709 17541 (BN 212096620 53124 (BL 208381236 12160) (BL 221196056 20096)) (BN 226592314 129153 (BL 223016482 386) (BL 227343707 4741)))) (BN 250069449 8836 (BN 239014159 27524 (BN 231254602 64386 (BL 229904579 2818) (BL 234724548 2816)) (BN 248266334 53120 (BL 247452986 56456) (BL 248481062 55428))) (BN 257433556 58504 (BN 253465462 1410 (BL 251888984 54920) (BL 257267488 40320)) (BN 261512788 9472 (BL 257901460 34178) (BL 261869554 62088))))) (BN 273715509 53128 (BN 266660972 8064 (BN 265418560 16768 (BN 263221761 15496 (BL 262637442 15872) (BL 264249837 14468)) (BN 266519547 55682 (BL 266377843 33540) (BL 266634583 56448))) (BN 268435247 16258 (BN 267973111 64384 (BL 267657759 13960) (BL 268212511 40576)) (BN 270629870 20608 (BL 269729058 63104) (BL 271070581 54912)))) (BN 283338892 2567 (BN 279654512 38016 (BN 276744037 130818 (BL 276008828 14720) (BL 278543545 40584)) (BN 281073354 43392 (BL 280099816 45184) (BL 281180035 130))) (BN 287796370 53376 (BN 284090510 19072 (BL 283445567 30596) (BL 284796428 55432)) (BN 291015363 64774 (BL 289934686 32389) BE))))) (BN 302297863 22658 (BN 298495540 40578 (BN 296441753 29832 (BN 295491228 8834 (BN 292603241 51714 (BL 292235126 52610) (BL 294776998 41096)) (BN 295976399 62210 (BL 295705327 16000) (BL 296089502 9600))) (BN 297326422 31618 (BN 296770249 52866 (BL 296573816 8198) (BL 296825876 34944)) (BN 298104806 48768 (BL 297651848 48256) (BL 298463911 4608)))) (BN 300877751 10888 (BN 300512571 9344 (BN 299247454 5760 (BL 298665934 5376) (BL 299790557 37381)) (BN 300731228 30464 (BL 300565203 14472) (BL 300796368 62208))) (BN 301562951 20352 (BN 301433106 54408 (BL 301297494 36736) (BL 301496075 38148)) (BN 302030634 129410 (BL 301972498 35584) (BL 302087846 46720))))) (BN 308345587 40322 (BN 305263818 32896 (BN 303101932 62720 (BN 302714713 36744 (BL 302371796 25088) (BL 302856726 25344)) (BN 303288801 37248 (BL 303134455 25984) (BL 305168156 53765))) (BN 306807794 57856 (BN 305359030 42368 (BL 305338828 7040) (BL 305869104 51848)) (BN 307570453 38272 (BL 306833790 57090) (BL 307960677 37376)))) (BN 313849400 44936 (BN 309826469 47752 (BN 309077228 128640 (BL 308355553 56832) (BL 309604154 29189)) (BN 313161121 53767 (BL 311677419 128136) (BL 313561661 62336))) (BN 317220681 9986 (BN 315970317 56452 (BL 314477602 46336) (BL 316113417 14984)) (BN 317899897 31106 (BL 317597119 29191) BE)))))) (BN 336990710 12032 (BN 326007090 13696 (BN 321621986 384 (BN 319469705 128386 (BN 318639160 61696 (BN 318528674 53890 (BL 318094569 44932) (BL 318573072 15488)) (BN 319110612 41600 (BL 319047819 40832) (BL 319319587 45698))) (BN 320896108 52354 (BN 319756915 33920 (BL 319570945 52864) (BL 320406315 54916)) (BN 321400575 10624 (BL 321373464 7938) (BL 321530816 44928)))) (BN 323360131 65157 (BN 323009070 13952 (BN 322131890 54658 (BL 321645489 37760) (BL 322425670 45062)) (BN 323120017 56704 (BL 323058027 55424) (BL 323201431 47621))) (BN 324650458 32000 (BN 324192913 57984 (BL 323629065 129152) (BL 324299355 58496)) (BN 325332106 59010 (BL 325024371 6274) (BL 325343043 640))))) (BN 333785195 37000 (BN 331009804 17536 (BN 328253472 56450 (BN 327326766 58370 (BL 326998153 130822) (BL 327809886 14850)) (BN 329491458 49792 (BL 328735353 62080) (BL 330165252 12288))) (BN 332481509 1157 (BN 331739092 15492 (BL 331434151 134) (BL 331762764 8706)) (BN 332689470 54914 (BL 332599964 31872) (BL 332889838 3456)))) (BN 335596074 12416 (BN 334825347 52352 (BN 334141957 42752 (BL 334044931 31616) (BL 334510021 64772)) (BN 335362081 64770 (BL 335053497 32384) (BL 335445802 4736))) (BN 336175090 13956 (BN 336088082 33925 (BL 335938623 56960) (BL 336105289 60290)) (BN 336917507 25221 (BL 336200567 8192) BE))))) (BN 345883258 24322 (BN 341319131 40710 (BN 339069236 60292 (BN 337878317 20354 (BN 337644895 13186 (BL 337325836 50048) (BL 337739315 29442)) (BN 338559363 22152 (BL 338223507 58372) (BL 338776548 4232))) (BN 340524080 57989 (BN 339715238 41472 (BL 339261345 59008) (BL 339929903 1408)) (BN 340875397 61568 (BL 340873545 55040) (BL 341108061 7552)))) (BN 343973638 4098 (BN 343415326 9856 (BN 342440180 59522 (BL 341742726 37126) (BL 342659505 8708)) (BN 343622616 35970 (BL 343485316 54400) (BL 343949461 51074))) (BN 345333065 22656 (BN 344816306 8832 (BL 344365901 34176) (BL 345218222 31362)) (BN 345766970 60800 (BL 345755410 39426) (BL 345847832 30724))))) (BN 349147330 50688 (BN 347921314 51840 (BN 347219679 61958 (BN 346211505 51204 (BL 346178724 20742) (BL 346438503 7044)) (BN 347480701 47618 (BL 347301127 16512) (BL 347727587 46081))) (BN 348409636 45058 (BN 348058614 18050 (BL 347929167 63872) (BL 348352391 28928)) (BN 349065180 45826 (BL 349020861 2184) (BL 349081957 25350)))) (BN 351109959 57472 (BN 350283830 19460 (BN 350053274 41986 (BL 349553558 64640) (BL 350156580 1152)) (BN 350496387 16134 (BL 350299658 25094) (BL 350805152 58752))) (BN 352401907 8194 (BN 351332714 46084 (BL 351273565 32262) (BL 351648880 31746)) (BN 353583328 54784 (BL 352983988 55680) BE))))))) (BN 384770121 37504 (BN 369708204 5248 (BN 361327462 3328 (BN 357087906 57094 (BN 354489272 514 (BN 354131757 49536 (BN 353989556 30336 (BL 353951087 4097) (BL 354075292 47232)) (BN 354337042 21888 (BL 354219754 57216) (BL 354352778 21508))) (BN 354823360 58624 (BN 354735656 57862 (BL 354592578 25216) (BL 354796811 28166)) (BN 355779534 42120 (BL 354932385 48902) (BL 356735436 53888)))) (BN 358387085 45057 (BN 357740960 22144 (BN 357271429 11904 (BL 357140295 50694) (BL 357534912 47360)) (BN 358184181 61056 (BL 358036959 128004) (BL 358221771 2054))) (BN 360338652 54656 (BN 360215532 29320 (BL 359043327 7686) (BL 360310666 23936)) (BN 360829480 62468 (BL 360466642 2565) (BL 361038425 3202))))) (BN 366931943 13184 (BN 364312514 65286 (BN 363164407 61824 (BN 362955459 6784 (BL 361576293 54790) (BL 363127530 53254)) (BN 363572321 47108 (BL 363257197 3712) (BL 363599883 32640))) (BN 366091025 30466 (BN 366029924 128006 (BL 365474423 34434) (BL 366030748 60032)) (BN 366326470 57218 (BL 366157576 31104) (BL 366509330 23938)))) (BN 368236076 129664 (BN 367388368 52608 (BN 367203163 25728 (BL 366943015 12805) (BL 367253348 12292)) (BN 367474797 9990 (BL 367469083 9218) (BL 367563528 18438))) (BN 369075592 130816 (BN 368910582 55552 (BL 368841469 56576) (BL 369050031 45440)) (BN 369189776 39298 (BL 369115492 43008) BE))))) (BN 376441655 30976 (BN 373449602 16256 (BN 371634236 64516 (BN 370924855 11912 (BN 370381725 33152 (BL 370225549 4866) (BL 370796617 62595)) (BN 371575572 15234 (BL 371303198 4096) (BL 371627580 7942))) (BN 372461406 52226 (BN 372195471 51200 (BL 371905081 130050) (BL 372271189 49796)) (BN 372749354 42496 (BL 372526725 36480) (BL 373135342 21378)))) (BN 374390722 45573 (BN 373972714 33538 (BN 373511590 128 (BL 373498802 18816) (BL 373625774 22914)) (BN 374144202 35456 (BL 373981985 30848) (BL 374179317 130688))) (BN 375706599 32642 (BN 374996516 14464 (BL 374967664 3200) (BL 375045518 4864)) (BN 375783670 129408 (BL 375739196 45056) (BL 376138862 30722))))) (BN 380374499 29697 (BN 378365824 9220 (BN 377185352 36352 (BN 376926081 39042 (BL 376478519 18560) (BL 377157664 47490)) (BN 377456896 23682 (BL 377402485 56833) (BL 378292524 30594))) (BN 379485512 57345 (BN 379377296 26242 (BL 379315133 59778) (BL 379403662 34432)) (BN 380237596 20992 (BL 379495077 54018) (BL 380334123 50304)))) (BN 382801822 130052 (BN 380845100 48002 (BN 380667970 51072 (BL 380574860 19458) (BL 380722799 41088)) (BN 382070348 11782 (BL 381027056 52228) (BL 382692817 63492))) (BN 383462432 13316 (BN 382840803 2306 (BL 382816641 57728) (BL 383351925 16515)) (BN 384676916 55426 (BL 384315046 54016) BE)))))) (BN 397315244 17028 (BN 390459764 128256 (BN 387627190 13824 (BN 385949897 46980 (BN 385475382 59520 (BN 385135739 2688 (BL 385076625 14080) (BL 385190616 26628)) (BN 385807954 49666 (BL 385737604 29827) (BL 385820276 10368))) (BN 387128815 27652 (BN 386506346 60934 (BL 386023226 42502) (BL 386989198 393)) (BN 387550909 30080 (BL 387363962 42112) (BL 387617936 128642)))) (BN 389554144 7424 (BN 388817533 14082 (BN 388425615 128128 (BL 387993431 29446) (BL 388584661 6530)) (BN 389317959 45952 (BL 388955458 40960) (BL 389512623 52992))) (BN 390205424 16128 (BN 390173602 10883 (BL 389897057 47744) (BL 390188378 30600)) (BN 390413139 15106 (BL 390267204 19840) (BL 390459224 36358))))) (BN 393857699 5632 (BN 392861613 14976 (BN 391799960 29312 (BN 391386135 23680 (BL 390518099 51712) (BL 391566397 35842)) (BN 392034574 1028 (BL 391986907 17280) (BL 392706554 48770))) (BN 393514268 39560 (BN 393253531 52994 (BL 393122976 49288) (BL 393306535 26240)) (BN 393701025 22272 (BL 393590782 27008) (BL 393799901 20486)))) (BN 395599670 59650 (BN 394703202 41856 (BN 394401020 28422 (BL 394260518 65280) (BL 394641422 48896)) (BN 395524326 19586 (BL 394965677 17664) (BL 395592538 56706))) (BN 396704695 49668 (BN 396160392 37888 (BL 396137374 24326) (BL 396470572 7172)) (BN 397209416 13313 (BL 396981595 58886) BE))))) (BN 406189270 35333 (BN 402001862 17026 (BN 399908760 4224 (BN 398297215 57344 (BN 398132491 36866 (BL 397772219 7810) (BL 398235899 34822)) (BN 399165345 57088 (BL 399082374 13315) (BL 399319296 45830))) (BN 401605494 47616 (BN 400183404 7298 (BL 399960324 42626) (BL 401487249 39808)) (BN 401939953 43014 (BL 401846939 55810) (BL 401954984 25602)))) (BN 403206578 23042 (BN 402874724 35202 (BN 402568489 2050 (BL 402214520 130176) (BL 402832313 9602)) (BN 403122041 27136 (BL 403025383 17024) (BL 403168132 56962))) (BN 403881904 58880 (BN 403464480 27392 (BL 403370577 48646) (BL 403714638 38916)) (BN 405977002 63616 (BL 405695952 7808) BE)))) (BN 408294081 15232 (BN 407330416 33157 (BN 406698813 130308 (BN 406390982 16898 (BL 406233342 55042) (BL 406469438 62592)) (BN 407041747 24194 (BL 406723102 41478) (BL 407076694 22148))) (BN 407786234 12932 (BN 407462480 1 (BL 407367442 28678) (BL 407474248 53250)) (BN 407866926 64128 (BL 407806575 8454) (BL 407919039 47104)))) (BN 410021281 18306 (BN 408845745 40704 (BN 408501904 49797 (BL 408391294 4100) (BL 408766426 5506)) (BN 408983786 27904 (BL 408868550 42240) (BL 409552236 9984))) (BN 411097972 65030 (BN 410366744 8576 (BL 410092796 34304) (BL 410756777 23424)) (BN 411451398 44672 (BL 411246151 130817) BE)))))))) (BN 464529666 44036 (BN 435109008 19712 (BN 421770387 36864 (BN 416736439 18433 (BN 415034992 53632 (BN 412834564 47488 (BN 411995127 130566 (BN 411910246 18434 (BL 411898478 32769) (BL 411988465 21250)) (BN 412300441 53249 (BL 412101841 42370) (BL 412827292 45060))) (BN 413991719 8320 (BN 413304548 25856 (BL 412891671 9728) (BL 413705019 7936)) (BN 414903121 56834 (BL 414404776 46080) (BL 414965480 24192)))) (BN 416064529 5504 (BN 415682149 129 (BN 415319741 29824 (BL 415158139 35200) (BL 415403267 2304)) (BN 415968341 772 (BL 415932602 35459) (BL 416035221 5638))) (BN 416395307 32256 (BN 416096861 10757 (BL 416065991 29568) (BL 416224319 128896)) (BN 416499286 30592 (BL 416492647 51328) (BL 416711026 33408))))) (BN 419470990 12672 (BN 417617511 55300 (BN 417129796 12544 (BN 416936950 18182 (BL 416904145 48390) (BL 416958401 11776)) (BN 417563609 48000 (BL 417327669 62976) (BL 417599213 60546))) (BN 418870476 37120 (BN 418372227 33794 (BL 417903143 11650) (BL 418816736 59142)) (BN 419359849 22146 (BL 419170744 35968) (BL 419380305 38528)))) (BN 420720926 28288 (BN 420032348 27520 (BN 419755739 10880 (BL 419658321 58368) (BL 419876492 44288)) (BN 420614440 22145 (BL 420141441 14848) (BL 420627512 22400))) (BN 421340143 47878 (BN 420855627 23045 (BL 420828800 62464) (BL 421090899 129280)) (BN 421736101 20873 (BL 421394399 60928) BE))))) (BN 428617049 43012 (BN 425104824 44680 (BN 422886659 40192 (BN 422079130 53760 (BN 422004322 57475 (BL 421939897 30208) (BL 422053509 14340)) (BN 422706945 129028 (BL 422568904 41988) (BL 422808225 56322))) (BN 423436542 46848 (BN 423306474 20736 (BL 423033562 49408) (BL 423360573 10499)) (BN 424094319 8704 (BL 423606742 18048) (BL 424409238 59648)))) (BN 427142943 60420 (BN 426268992 21632 (BN 426165543 9734 (BL 425787697 1154) (BL 426206385 2048)) (BN 426641839 28800 (BL 426515128 29184) (BL 427004902 516))) (BN 427469560 4352 (BN 427322657 23808 (BL 427282646 30720) (BL 427336093 129666)) (BN 427713984 50178 (BL 427652668 12930) (BL 428331035 128898))))) (BN 431718644 19456 (BN 430070870 29440 (BN 429286858 38536 (BN 428887867 26112 (BL 428807304 21504) (BL 428969586 24576)) (BN 429655245 32386 (BL 429537334 26624) (BL 429678462 6272))) (BN 431050828 3076 (BN 430601541 62982 (BL 430223695 25218) (BL 430984179 38400)) (BN 431230542 3584 (BL 431112144 53248) (BL 431528452 60544)))) (BN 432734228 22402 (BN 431956543 52096 (BN 431865694 7554 (BL 431796153 15104) (BL 431924561 28160)) (BN 432425508 26374 (BL 432149982 48130) (BL 432669174 41734))) (BN 434375533 64258 (BN 433886197 43520 (BL 433766751 64514) (BL 434374352 28296)) (BN 434754882 35844 (BL 434610573 50818) BE)))))) (BN 448605703 50689 (BN 442537127 32768 (BN 439057655 15744 (BN 436500487 10112 (BN 435622622 61446 (BN 435213769 30214 (BL 435124113 16646) (BL 435548142 18432)) (BN 436354083 36224 (BL 436274486 11268) (BL 436465405 9608))) (BN 438101129 0 (BN 437086143 6148 (BL 436587980 34048) (BL 437794082 61952)) (BN 438214813 24320 (BL 438146619 20482) (BL 438977144 38406)))) (BN 440719243 46850 (BN 439560111 57606 (BN 439471773 128000 (BL 439183061 53510) (BL 439487782 53761)) (BN 440193840 129794 (BL 440149225 54146) (BL 440629152 21376))) (BN 441797905 3714 (BN 441041231 33282 (BL 440790081 9088) (BL 441396735 45824)) (BN 442161048 36995 (BL 442062239 16385) (BL 442446670 34310))))) (BN 445746849 37121 (BN 444504414 3590 (BN 443923780 29185 (BN 442878434 9347 (BL 442582617 34818) (BL 443787406 49280)) (BN 444085134 62848 (BL 444063259 52098) (BL 444324700 3078))) (BN 445072433 21122 (BN 444713407 28673 (BL 444590208 2432) (BL 444849059 2176)) (BN 445336941 59396 (BL 445218409 43648) (BL 445734933 42376)))) (BN 447278578 16384 (BN 446534494 13312 (BN 446286671 43010 (BL 445872625 59906) (BL 446523194 27777)) (BN 446739790 18304 (BL 446543663 128384) (BL 447051688 29696))) (BN 448356114 39296 (BN 448061356 38912 (BL 447869563 33921) (BL 448083525 45574)) (BN 448539812 50816 (BL 448425535 4992) BE))))) (BN 456843855 45568 (BN 452658367 18946 (BN 451223915 43650 (BN 450182847 20737 (BN 449415370 26118 (BL 448800148 7042) (BL 449455807 45696)) (BN 450606089 11520 (BL 450235113 1536) (BL 451067433 36482))) (BN 452085114 40066 (BN 451739739 59904 (BL 451714160 28674) (BL 451937972 33284)) (BN 452153293 64002 (BL 452144802 1666) (BL 452305561 57985)))) (BN 454657685 1025 (BN 453069050 64512 (BN 452963928 39424 (BL 452792112 22912) (BL 453041701 54785)) (BN 454327050 48514 (BL 454033795 34562) (BL 454531889 53889))) (BN 455295420 6401 (BN 455174431 10241 (BL 454948462 1798) (BL 455182335 16640)) (BN 456387748 23176 (BL 455993140 11392) BE)))) (BN 461684553 33030 (BN 459134254 17920 (BN 458386355 17410 (BN 457530661 19584 (BL 457521057 47617) (BL 457993546 59654)) (BN 458900228 24704 (BL 458858483 36868) (BL 459093683 7169))) (BN 460398803 48384 (BN 459776697 46208 (BL 459618333 57600) (BL 459800638 9216)) (BN 460928821 25604 (BL 460543399 44550) (BL 461510385 41349)))) (BN 462667787 45312 (BN 461966659 42624 (BN 461852034 45318 (BL 461784515 20480) (BL 461964229 55296)) (BN 462461870 52224 (BL 462242581 21254) (BL 462544495 1793))) (BN 464022802 28161 (BN 463109669 5120 (BL 462822353 15362) (BL 463294481 2052)) (BN 464236636 130048 (BL 464127631 63488) BE))))))) (BN 504287911 34566 (BN 482588987 1542 (BN 472531010 42754 (BN 468038379 39040 (BN 465890272 31360 (BN 465334897 27776 (BN 464834801 47872 (BL 464564948 14593) (BL 465103163 2560)) (BN 465657276 55944 (BL 465364819 16900) (BL 465779574 59776))) (BN 466304269 33536 (BN 466078447 49153 (BL 466074041 1664) (BL 466220513 34816)) (BN 466966943 64130 (BL 466400227 14336) (BL 467592397 19974)))) (BN 469331606 64000 (BN 468563629 27648 (BN 468200240 53252 (BL 468057392 21635) (BL 468537825 50432)) (BN 469288432 31748 (BL 468741727 8835) (BL 469313529 21761))) (BN 470792307 49152 (BN 470262464 39552 (BL 469436273 54144) (BL 470769627 48644)) (BN 471743185 36992 (BL 471342806 128001) (BL 471953896 39938))))) (BN 476537500 37632 (BN 475205625 8452 (BN 474328761 13830 (BN 472738207 20864 (BL 472636238 18436) (BL 473469388 1024)) (BN 475049102 6528 (BL 474548246 50944) (BL 475137524 31232))) (BN 476163832 41728 (BN 475352056 28672 (BL 475214162 17926) (BL 475731532 7296)) (BN 476401742 10113 (BL 476344780 4480) (BL 476482706 10246)))) (BN 479969340 61442 (BN 477905386 7168 (BN 477286786 22532 (BL 476861925 52742) (BL 477653176 9604)) (BN 478139509 49664 (BL 477959795 54272) (BL 478583057 29953))) (BN 481432861 6144 (BN 480796854 46978 (BL 480595924 58118) (BL 481220209 6400)) (BN 482555934 60672 (BL 482240760 12928) BE))))) (BN 494178494 55808 (BN 487304597 50177 (BN 485762882 2310 (BN 484270431 1922 (BN 483094948 27267 (BL 482820899 7680) (BL 483606618 5888)) (BN 484912417 44800 (BL 484629649 64262) (BL 485671270 63361))) (BN 486463819 128512 (BN 486072054 1280 (BL 485807028 13056) (BL 486131777 64257)) (BN 486922704 42372 (BL 486547266 1792) (BL 487070651 11265)))) (BN 491740595 48129 (BN 490413326 12546 (BN 488671418 3074 (BL 488240030 23040) (BL 489683659 59392)) (BN 490489737 39168 (BL 490447956 129798) (BL 491153794 10244))) (BN 493010771 129793 (BN 492692708 46984 (BL 492426167 10114) (BL 492905817 58113)) (BN 493509491 47747 (BL 493056385 11648) (BL 493539959 34690))))) (BN 500052594 6658 (BN 496774543 33792 (BN 495238318 21760 (BN 494980702 5121 (BL 494786268 2561) (BL 495203597 22784)) (BN 496329578 30721 (BL 496007268 44160) (BL 496422942 10752))) (BN 498872611 20484 (BN 498282190 12800 (BL 497634201 6146) (BL 498740994 8966)) (BN 499737691 128518 (BL 498893376 61441) (BL 499952122 26368)))) (BN 502175345 31489 (BN 501210541 56320 (BN 500209076 23554 (BL 500090163 52480) (BL 500765576 19457)) (BN 501422501 38144 (BL 501262641 12801) (BL 501628858 34561))) (BN 503998048 46592 (BN 503308609 34820 (BL 503127187 22016) (BL 503607236 61440)) (BN 504141759 129024 (BL 504003718 41984) BE)))))) (BN 536262806 53504 (BN 517137760 10240 (BN 508710348 45569 (BN 507460035 2434 (BN 505919708 6656 (BN 504507846 54528 (BL 504320020 21248) (BL 505453840 40454)) (BN 506116300 50176 (BL 505925584 35330) (BL 506500120 29058))) (BN 508191173 10243 (BN 507657380 32512 (BL 507550668 129920) (BL 508091889 27264)) (BN 508439716 512 (BL 508230060 39810) (BL 508577757 60416)))) (BN 512485642 3072 (BN 510552298 48128 (BN 509221706 13568 (BL 509176955 28416) (BL 510056859 18176)) (BN 512194728 58112 (BL 511120152 22022) (BL 512440152 28676))) (BN 514293684 130306 (BN 513357355 63360 (BL 512566243 21120) (BL 514091449 40064)) (BN 516189696 35840 (BL 514723368 24070) (BL 516663312 12806))))) (BN 526707088 64256 (BN 519717563 39937 (BN 518205306 33024 (BN 517499588 23426 (BL 517271920 46598) (BL 517709300 11264)) (BN 518783535 29056 (BL 518273163 34049) (BL 519003616 46976))) (BN 523563212 770 (BN 520988940 1920 (BL 520829424 10242) (BL 521633504 22528)) (BN 524602325 50950 (BL 524199283 45961) (BL 525665141 44544)))) (BN 532525395 129792 (BN 528947521 1665 (BN 528778253 129536 (BL 528356484 13440) (BL 528864538 59136)) (BN 532152288 39169 (BL 530258468 34688) (BL 532291272 11521))) (BN 533372786 33280 (BN 533003040 63744 (BL 532706507 18944) (BL 533135944 23168)) (BN 534436447 64768 (BL 533841250 48640) BE))))) (BN 561614474 23302 (BN 546799633 16896 (BN 541250620 44033 (BN 539712080 22017 (BN 536788671 17408 (BL 536765989 262) (BL 538277248 8448)) (BN 540695332 61444 (BL 540508896 35329) (BL 541224669 15360))) (BN 544720147 19968 (BN 542363635 25600 (BL 542235652 8960) (BL 542405472 55936)) (BN 546170397 54529 (BL 545964480 44032) (BL 546365350 34560)))) (BN 550525806 4482 (BN 549087999 256 (BN 548758445 44416 (BL 547021149 36096) (BL 548945534 1281)) (BN 550356212 39936 (BL 549553555 10497) (BL 550416487 10753))) (BN 557452792 31494 (BN 553989675 52736 (BL 550723246 31744) (BL 555175253 23041)) (BN 560901843 59264 (BL 558077077 14592) BE)))) (BN 578047765 10503 (BN 570171371 6016 (BN 563894432 15616 (BN 562963643 52481 (BL 562825602 26369) (BL 563054248 65024)) (BN 566871528 46593 (BL 564939544 130560) (BL 569283035 63362))) (BN 572095186 29952 (BN 570884002 56070 (BL 570575582 40448) (BL 571368842 59393)) (BN 573008559 59266 (BL 572990144 17158) (BL 573897532 23553)))) (BN 601185519 59137 (BN 582278087 6018 (BN 579845110 24064 (BL 578611392 23552) (BL 582259672 49926)) (BN 589051596 31488 (BL 585973724 35328) (BL 594058628 53505))) (BN 615894767 768 (BN 606625239 130304 (BL 605109132 23296) (BL 614378660 56064)) (BN 625754330 49920 (BL 616484802 17152) BE))))))))
def RtT10_0 := nd (nd (nd (nd (lf 0x801000fe2 [0x202010d000b,0x10c020c0310,0x1170217]) (nd (lf 0x8c01000f62 [0x30d0202000b,0x214020a]) (lf 0x8c01000fe2 [0x2020110000b,0x10c020a030d,0x1170214]))) (nd (lf 0x1001000fe2 [0xb0202010c,0x117030d0310]) (nd (lf 0xc81000f72 [0x202010d0110,0x213020b0201,0x20a020c000b,0x302140217,0x114010a]) (lf 0x8c81000f72 [0x201010d0202,0x213020b0107,0x20a020c000b,0x2140217010a,0x3001e0114,0x1100007])))) (nd (nd (lf 0x8c81000ff2 [0x20102020110,0x20b0107010d,0xb011e0213,0x20a020c0007,0x217010a010c,0x11401170214,0x1e0003]) (nd (lf 0x1081000ff2 [0x202010d010c,0x310020b0201,0x217002e0213,0x21000070214,0x114000a0110,0xb00130117]) (lf 0x9081000ff2 [0x202010d010a,0x20b01050201,0xb02130310,0x21000030217,0x1140117000c,0x13]))) (nd (lf 0x1881000bf2 [0x30007000b,0xa000c0310,0x140017]) (nd (lf 0x9881000bf2 [0x20102020007,0xc00100310,0x140017000a]) (lf 0x50c1000f72 [0x2010202010a,0x20b0105030d,0xc02170213,0xb0114]))))) (nd (nd (nd (lf 0x50c1000ef2 [0x20102020110,0x213010a030d,0x2140217020b]) (nd (lf 0x50c1000ff2 [0x2020110010a,0x105030d0201,0xb0213020b,0x30217000c,0x1301140117]) (lf 0x90c1000f72 [0x2010202010a,0xb0105030d,0x2170213020b,0x1140003]))) (nd (lf 0xd0c1000ef2 [0x20102020110,0x20b010c030d,0x21402170213,0x20]) (nd (lf 0xd0c1000ff2 [0x2020110010c,0x20b030d0201,0x21700200213,0x114010a0214,0x117]) (lf 0x58c1000bf2 [0x30d01100013,0x70006002e,0xa000c000b,0x140017])))) (nd (nd (lf 0xd8c1000b72 [0x30d0202000b,0x700030201,0x14000a]) (nd (lf 0xd8c1000bf2 [0x2020110000b,0x6002e030d,0x700030201,0x17000a000c,0x14]) (lf 0x1501000ff2 [0x2020117010c,0x310020b0201,0x2130005030d,0x11002100006]))) (nd (nd (lf 0x5501000ff2 [0x2020114010a,0x30d03100201,0xb0213020b,0x1302100003]) (lf 0x9501000ff2 [0x10c02020114,0x310020b0201,0xb0213030d,0x2100003002e,0x1300170110])) (nd (lf 0x1043000f72 [0x1020210010c,0x214030d0201,0x1170114]) (lf 0x9043000f72 [0x1020210010a,0x105030d0201,0x11401170003])))))
def RtT10_1 := nd (nd (nd (nd (lf 0x9843000b72 [0x30d02010003,0x14000a0007]) (nd (lf 0x1503000f72 [0x2100117010c,0x503020201,0x30d]) (lf 0x5503000f72 [0x2010210010a,0x30d03020114,0xb]))) (nd (lf 0x9503000f72 [0x20102100114,0x30d0302010c]) (nd (lf 0x9023000f62 [0x302000b010a,0x1140105030d]) (lf 0x1063000f72 [0x2010102010c,0xb020b030d,0x11402100214,0x180117])))) (nd (nd (lf 0x9063000f72 [0x190102010a,0x30d01050201,0x117020b0210,0x180114]) (nd (lf 0x9863000b72 [0x30d02010003,0x14000a0007]) (lf 0x9863000f72 [0xb01020018,0x10a010c030d,0x1140117]))) (nd (nd (lf 0x1523000f72 [0x2010117010c,0x50302020b,0xb0210030d,0x18]) (lf 0x5523000f72 [0x2010114010a,0x20b030d0302,0x180210])) (nd (lf 0x9523000f72 [0x201010c0114,0x30d0302020b,0x180210000b]) (lf 0x5923000f72 [0xb010a0018,0x105030d0302,0x1140117]))))) (nd (nd (nd (lf 0x9923000f72 [0xb010c0018,0x19030d0302,0x1170114010a]) (nd (lf 0x9023000fe2 [0xb0210010a,0x105030d0302,0x114000c]) (lf 0x8c63000f72 [0x2e02010102,0x40006030d,0x20a020c0018,0x217010a010c,0x11401170214,0x3000b]))) (nd (lf 0x1063000ff2 [0x1020201002e,0x30d010c0210,0x217000a000b,0x11701140214,0x18]) (nd (lf 0x9063000ff2 [0x1020210010a,0x30d01050201,0x2170218020b,0x1140117000c,0xb0018]) (lf 0x9863000bf2 [0x20102100003,0xc0007030d,0x140017000a])))) (nd (nd (lf 0x50e3000f72 [0x60201010a,0x30d01050302,0x217000b0018,0x11401170010]) (nd (lf 0xd0e3000e72 [0x30202010006,0x2140018030d,0xa0010]) (lf 0xd0e3000f72 [0x60201010c,0xb030d0302,0x214000a0018,0x11701140010]))) (nd (nd (lf 0x1523000ff2 [0x201010c0006,0x2e03020210,0x18000b030d]) (lf 0x5523000ff2 [0x1140210010a,0x30d03020201,0xb0218020b,0x18])) (nd (lf 0x9523000ff2 [0x2010114002e,0x30d03020210,0x18010c000b]) (lf 0x9044000ef2 [0xa0201000c,0x30d03100102,0x11702170005])))))
def RtT10_2 := nd (nd (nd (nd (lf 0x1444000ff2 [0x1020117020c,0x30d03100201,0x11000060210,0x2e]) (nd (lf 0x9444000ff2 [0x102020c0005,0x30d03100201,0xa002e0210]) (lf 0x9844000bf2 [0x201000c0003,0x7030d0310,0x140017]))) (nd (lf 0x50c4000ef2 [0xc000a0110,0x30d03020201,0x11702170005]) (nd (lf 0x54c4000f72 [0x201020c0114,0xb030d0302,0xa]) (lf 0x54c4000df2 [0x3020201002e,0x20c030d])))) (nd (nd (lf 0x54c4000ff2 [0x2010005002e,0x20c01100302,0xa000b030d,0x17]) (nd (lf 0x94c4000f72 [0x201020c0114,0xa030d0302]) (lf 0xd4c4000df2 [0x3020201002e,0x30d0110]))) (nd (lf 0xd4c4000ff2 [0x2010117002e,0x30d01100302,0x1140021]) (nd (lf 0x58c4000b72 [0x302000c0201,0x70003030d,0x14]) (lf 0x58c4000bf2 [0x6000c0201,0x110030d0302,0x1700070003,0x14]))))) (nd (nd (nd (lf 0xd504000ef2 [0x201000c0117,0x30d03100302,0x6]) (nd (lf 0x9864000bf2 [0x201000a0003,0x30d03100005,0x1700100007]) (lf 0xd0e4000ef2 [0x30202010020,0x5000c030d,0x2140217000a]))) (nd (lf 0x54e4000df2 [0x20101100005,0x30d0302]) (nd (lf 0xd4e4000df2 [0x1100201020a,0x30d03020117,0x210005]) (lf 0xd4e4000ff2 [0x20101170005,0x30d03020110,0x21])))) (nd (nd (lf 0x58e4000bf2 [0x502010020,0x30d03020006,0x70003000a,0x17]) (nd (lf 0x1524000ef2 [0x11702010005,0x30d03100302,0x6000a]) (lf 0x1814300b72 [0x5000a000b,0x3030d0302,0x7]))) (nd (nd (lf 0x1514300e72 [0x30103020005,0xa030d0117]) (lf 0x1814300ef2 [0x30201010006,0xa0210030d,0x10b0005])) (nd (lf 0xd4d4300c72 [0x30103020016,0x30d]) (lf 0xd4d4300e72 [0x30103020117,0x20a030d])))))
def RtT10_3 := nd (nd (nd (nd (lf 0xd8d4300e72 [0xc000a0006,0x30103020005,0x117030d]) (nd (lf 0x1954300ef2 [0x11702100005,0x30d03010302,0xa]) (lf 0xd954300ef2 [0x30201140006,0x210030d0301,0xa]))) (nd (lf 0x1814300bf2 [0xa0210000b,0x5030d0302,0x700030101,0x17]) (nd (lf 0xd4d4300d72 [0x3010302020a,0x117030d]) (lf 0xd4d4300f72 [0x30201170005,0x14030d0301,0x20a])))) (nd (nd (lf 0x1514300ef2 [0x21000050006,0x30d03010302,0xa0117]) (nd (lf 0x9514300ef2 [0xa02100114,0x30d03010302]) (lf 0x9824300b72 [0x3020005000b,0x3020c030d,0x7]))) (nd (nd (lf 0x5964300972 [0x3020014000a,0x30d0301]) (lf 0x9834300ef2 [0x30201010020,0x6000c030d,0x114000a])) (nd (lf 0x5974300ef2 [0x30201140006,0x30d02100301,0xc]) (lf 0x9974300ef2 [0x30200200006,0x210030d0301,0xc]))))) (nd (nd (nd (lf 0x9834300bf2 [0x302000b0020,0x3030d000c,0x1400170007]) (nd (lf 0x5534300ef2 [0xc02100114,0x30d03010302]) (lf 0xd534300ef2 [0x30200200006,0x210030d0301,0xa000c]))) (nd (lf 0x9805400bf2 [0x302000b0005,0xc0310030d,0x700030017]) (nd (lf 0x58c5400b72 [0x30103020005,0x3000b030d,0x7]) (lf 0x58c5400bf2 [0x30201100005,0xc030d0301,0x3000b0017,0x7])))) (nd (nd (lf 0x5505400cf2 [0x302000c000a,0x310030d0301]) (nd (lf 0x1815400bf2 [0x14000a000b,0x30d03020310,0x1000070003]) (lf 0xd8d5400bf2 [0x30200140020,0x110030d0301,0x3000b000a,0x7]))) (nd (nd (lf 0x9825400bf2 [0xc0014000b,0x310030d0302,0x70003]) (lf 0x58e5400b72 [0xc00140012,0x30103020021,0x3000b030d,0x7])) (nd (lf 0x58e5400bf2 [0x302000c0021,0x110030d0301,0x3000b0014,0x7]) (lf 0xd525400cf2 [0x3020017000c,0x310030d0301])))))
def RtT10 : BTree NodeData := nd (nd RtT10_0 RtT10_1) (nd RtT10_2 RtT10_3)
def RtM10 : BST := BN 397901830 61833 (BN 348189934 19970 (BN 311695135 55432 (BN 281202684 30468 (BN 260660077 7808 (BN 236703958 29572 (BN 219591704 53384 (BN 214509793 20356 (BN 212606305 136 (BL 198021170 4480) (BL 213634381 31492)) (BN 218195186 57730 (BL 217042303 56456) (BL 218833696 54912))) (BN 225074137 58500 (BN 220938929 17284 (BL 220619780 9988) (BL 224027702 25224)) (BN 236358529 32640 (BL 225374927 23428) BE))) (BN 251103102 30080 (BN 244468289 64136 (BN 240794527 65408 (BL 240032291 14472) (BL 241060367 20228)) (BN 249949747 31496 (BL 247410130 23938) (BL 250679507 20352))) (BN 259599984 52360 (BN 255539100 62848 (BL 255163986 7944) (BL 256935146 9992)) (BN 260633941 63872 (BL 259856763 61312) BE)))) (BN 275517259 24704 (BN 270936669 29824 (BN 266448282 12160 (BN 264157187 18816 (BL 260752867 18048) (BL 264292761 8064)) (BN 267324779 1666 (BL 266500671 61184) (BL 268403703 59776))) (BN 273507240 58242 (BN 272157217 1282 (BL 271963222 52231) (BL 273297142 15872)) (BN 274846228 64898 (BL 273672890 16256) BE))) (BN 278559016 13957 (BN 277330775 22914 (BN 276835173 6016 (BL 276128682 20360) (BL 276977186 1280)) (BN 278529088 32641 (BL 277375733 20232) BE)) (BN 280987956 3968 (BN 278839140 26248 (BL 278633223 58498) (BL 280174608 6280)) (BN 281140255 24328 (BL 281123636 132) BE))))) (BN 299819600 64128 (BN 292507428 60168 (BN 285576253 11400 (BN 283385819 1664 (BN 282965086 65409 (BL 281246801 56962) (BL 283142554 59137)) (BN 284610606 6792 (BL 283644320 27394) (BL 285559634 56452))) (BN 289222834 60040 (BN 286956869 13698 (BL 286729136 13952) (BL 288109035 53380)) (BN 291430724 29056 (BL 289854108 63109) BE))) (BN 297353807 52096 (BN 295742446 30336 (BN 292814602 54920 (BL 292545033 25220) (BL 295383602 14464)) (BN 297149320 51848 (BL 295866722 10624) BE)) (BN 299609143 27653 (BN 298791135 26242 (BL 298513479 31368) (BL 298928513 22664)) (BN 299703887 22146 (BL 299668274 13696) BE)))) (BN 305616170 22404 (BN 303879753 30338 (BN 303364511 23176 (BN 301428553 64648 (BL 299956589 63236) (BL 302775778 13188)) (BN 303517028 3077 (BL 303418917 25472) (BL 303761396 30592))) (BN 305262615 62722 (BN 304763981 4482 (BL 304659627 57728) (BL 304892479 30085)) (BN 305598317 29696 (BL 305497750 53120) BE))) (BN 308549622 14468 (BN 306872855 52739 (BN 306472450 9734 (BL 306341971 1152) (BL 306714868 26240)) (BN 307953026 19461 (BL 307627620 22144) BE)) (BN 309328477 62853 (BN 308679672 19328 (BL 308630481 26884) (BL 308947068 9856)) (BN 310225749 58240 (BL 309916147 25730) BE)))))) (BN 332117738 23432 (BN 322305815 64256 (BN 317465784 62857 (BN 313812246 24960 (BN 313052990 64896 (BN 312985620 64132 (BL 312723211 3844) (BL 313029786 30089)) (BN 313519363 23688 (BL 313457849 3590) (BL 313688750 27013))) (BN 316131133 14984 (BN 314903940 23936 (BL 313920133 63746) (BL 315537537 22912)) (BN 317233846 22917 (BL 316309940 52226) BE))) (BN 319705716 62080 (BN 318483697 6920 (BN 318110110 22656 (BL 317518050 30472) (BL 318195492 32386)) (BN 319134904 16390 (BL 318893552 2560) BE)) (BN 321355503 17792 (BN 320026911 26244 (BL 319820994 58496) (BL 320458348 1408)) (BN 321826057 27017 (BL 321513079 11909) BE)))) (BN 327465020 65154 (BN 324007763 27010 (BN 323029022 16002 (BN 322546108 23168 (BL 322510133 13701) (BL 322600494 9864)) (BN 323570902 8198 (BL 323168432 18821) (BL 323786637 29442))) (BN 325564675 12032 (BN 325371153 22921 (BL 324097526 8840) (BL 325395597 17536)) (BN 326297326 18304 (BL 326264521 17280) BE))) (BN 329262700 18308 (BN 328794331 51842 (BN 328177112 55168 (BL 327681740 17288) (BL 328398865 54018)) (BN 329246979 19842 (BL 329167891 63104) BE)) (BN 330647440 13705 (BN 329945321 53378 (BL 329650386 11913) (BL 330000673 5248)) (BN 331305739 18825 (BL 330700519 23424) BE))))) (BN 339961917 6784 (BN 336651677 3456 (BN 333701982 12034 (BN 332997640 52738 (BN 332749299 24192 (BL 332691137 30341) (BL 332834863 13058)) (BN 333121237 3204 (BL 333019109 59016) (BL 333298575 28418))) (BN 334381319 25218 (BN 333898436 27398 (BL 333725722 12037) (BL 334002373 54916)) (BN 336271955 63240 (BL 335525919 6272) BE))) (BN 337869054 53376 (BN 337667753 60800 (BN 337305198 63106 (BL 336780170 19080) (BL 337515683 9346)) (BN 337734573 21634 (BL 337689510 51970) BE)) (BN 338397073 4488 (BN 338137980 5250 (BL 337940490 52610) (BL 338161720 5253)) (BN 339293575 18050 (BL 338686713 24577) BE)))) (BN 342864998 17153 (BN 342029550 29568 (BN 340860470 62469 (BN 340620889 14722 (BL 340518242 8832) (BL 340828444 30345)) (BN 341827650 26368 (BL 341785884 22400) (BL 341831183 59272))) (BN 342288637 5768 (BN 342125508 11010 (BL 342103751 7552) (BL 342187708 10498)) (BN 342679387 64001 (BL 342305052 25216) BE))) (BN 345211495 53504 (BN 344574145 60032 (BN 343549931 59136 (BL 343446769 29576) (BL 344195698 128)) (BN 345056887 5506 (BL 344611271 30081) BE)) (BN 346758683 25732 (BN 345801305 63616 (BL 345565608 7938) (BL 346623706 54530)) (BN 348041948 26628 (BL 347692927 31104) BE))))))) (BN 376773506 16131 (BN 364174249 63750 (BN 355965463 13570 (BN 352971104 59010 (BN 349090972 52229 (BN 348689048 56322 (BN 348543437 56704 (BL 348337520 54400) (BL 348631696 56448)) (BN 349038577 3848 (BL 348691939 6276) (BL 349047269 62849))) (BN 351807046 20224 (BN 349911859 11522 (BL 349647493 12544) (BL 350001606 52354)) (BN 352477946 9220 (BL 352334944 64768) BE))) (BN 353864790 31360 (BN 353414714 15233 (BN 353109051 65288 (BL 352987671 3202) (BL 353127937 6788)) (BN 353746756 55944 (BL 353533732 64385) (BL 353830203 64392))) (BN 354861993 30721 (BN 353901579 5890 (BL 353883418 20616) (BL 354304589 0)) (BN 355946279 8321 (BL 355516731 62726) BE)))) (BN 360031498 64000 (BN 357952737 30978 (BN 357314925 19712 (BN 356793103 59520 (BL 356385831 63492) (BL 357045824 7170)) (BN 357628781 386 (BL 357545049 7304) (BL 357740165 60036))) (BN 359006055 3712 (BN 358467120 30724 (BL 358319416 31880) (BL 358775746 30848)) (BN 359623233 23680 (BL 359529313 12674) BE))) (BN 362421146 12292 (BN 361229101 27264 (BN 360293708 31617 (BL 360159367 16513) (BL 360894837 59008)) (BN 362240632 5762 (BL 361676701 17152) BE)) (BN 363917552 129 (BN 363243336 55042 (BL 362887224 18817) (BL 363481622 16386)) (BN 364083586 8323 (BL 363965311 61826) BE))))) (BN 369903775 2432 (BN 367353427 59268 (BN 366286332 27652 (BN 365408940 23810 (BN 364308838 64384 (BL 364302033 648) (BL 364708848 24582)) (BN 365649258 60292 (BL 365454872 59528) (BL 365666651 51844))) (BN 366827416 12672 (BN 366558420 11269 (BL 366482948 14084) (BL 366783152 1671)) (BN 367235059 22408 (BL 367030810 31364) BE))) (BN 368425181 19074 (BN 368251569 57096 (BN 367711242 56960 (BL 367445844 22660) (BL 367917620 8194)) (BN 368353550 56449 (BL 368296674 16515) BE)) (BN 369659703 63494 (BN 369524065 27142 (BL 368911795 1921) (BL 369566567 63618)) (BN 369890870 27272 (BL 369679997 62088) BE)))) (BN 372499824 12418 (BN 371263414 61824 (BN 370194217 3076 (BN 370011820 55424 (BL 369945884 64644) (BL 370164365 5760)) (BN 371044929 25984 (BL 370233877 52864) (BL 371212410 15744))) (BN 371881842 23172 (BN 371598179 61952 (BL 371280985 10888) (BL 371602957 2944)) (BN 372375461 16770 (BL 372054859 131) BE))) (BN 374533554 63232 (BN 374040753 29446 (BN 373571561 17032 (BL 372687567 27784) (BL 373840450 20096)) (BN 374447818 14976 (BL 374206880 59012) BE)) (BN 375277964 21761 (BN 374795304 27008 (BL 374630215 19460) (BL 374918786 7044)) (BN 376490857 56451 (BL 375975875 27392) BE)))))) (BN 387470369 29958 (BN 382105251 52873 (BN 379477665 62344 (BN 377498946 13824 (BN 377024928 21380 (BN 376952773 20864 (BL 376935822 53890) (BL 376959117 61569)) (BN 377350558 32130 (BL 377339796 18312) (BL 377479805 4738))) (BN 378829646 7936 (BN 378469168 17664 (BL 378433478 25728) (BL 378652981 54022)) (BN 379379936 24580 (BL 378930482 6146) BE))) (BN 381330884 13954 (BN 380752398 19968 (BN 379728999 22658 (BL 379584844 4484) (BL 380212466 55428)) (BN 381284530 62594 (BL 381209504 60547) BE)) (BN 381841581 61570 (BN 381644989 8578 (BL 381395115 29313) (BL 381764372 55552)) (BN 382036694 23684 (BL 381934944 30208) BE)))) (BN 384649084 27648 (BN 383600200 9728 (BN 383265644 52352 (BN 383088979 13062 (BL 382989398 25733) (BL 383151877 28160)) (BN 383468089 3078 (BL 383366480 21506) (BL 383476408 5764))) (BN 384164997 23170 (BN 383721358 59394 (BL 383689137 2688) (BL 383895054 62337)) (BN 384648464 14980 (BL 384574538 52992) BE))) (BN 386429063 12416 (BN 386277579 29314 (BN 386202099 4994 (BL 385328525 12677) (BL 386222301 53632)) (BN 386368765 9986 (BL 386294456 54148) BE)) (BN 387203874 1675 (BN 386989314 1792 (BL 386757738 10112) (BL 387119518 16384)) (BN 387466835 55041 (BL 387281224 56067) BE))))) (BN 392708237 13314 (BN 391226860 18184 (BN 389764523 61829 (BN 388210923 19586 (BN 387943626 51974 (BL 387904087 19462) (BL 388157356 25602)) (BN 388278736 60418 (BL 388272239 55298) (BL 388556969 3072))) (BN 390452493 15112 (BN 389956300 62336 (BL 389827223 6148) (BL 390426092 61185)) (BN 391015465 27910 (BL 390865061 53888) BE))) (BN 392061745 64905 (BN 391703455 24579 (BN 391409044 4736 (BL 391353329 512) (BL 391555516 8192)) (BN 392036965 64388 (BL 391949363 30464) BE)) (BN 392379624 11014 (BN 392120459 11650 (BL 392082027 28544) (BL 392349072 768)) (BN 392614857 8836 (BL 392441824 10502) BE)))) (BN 395294698 26118 (BN 394145850 60416 (BN 393465832 12681 (BN 392992967 19456 (BL 392794658 62214) (BL 393164582 56193)) (BN 393990025 15232 (BL 393915707 22274) (BL 394125617 16130))) (BN 394862090 29825 (BN 394263221 21508 (BL 394257462 57216) (BL 394292498 9984)) (BN 395161261 65280 (BL 394976087 7173) BE))) (BN 396877822 54534 (BN 396147475 55176 (BN 395770820 61568 (BL 395343953 59522) (BL 395789327 20992)) (BN 396785070 4864 (BL 396740789 19840) BE)) (BN 397358785 2818 (BN 396957130 257 (BL 396936781 5888) (BL 397169986 8448)) (BN 397594170 62720 (BL 397523777 18436) BE)))))))) (BN 446651815 27136 (BN 420480528 13440 (BN 409372083 57985 (BN 404659364 22401 (BN 401823587 51840 (BN 399779951 27266 (BN 399168980 55300 (BN 398864454 10114 (BL 398561615 60546) (BL 398987886 2566)) (BN 399597259 7296 (BL 399346294 518) (BL 399613643 31106))) (BN 400619142 31488 (BN 400165975 11526 (BL 399808332 31616) (BL 400206818 29312)) (BN 401389987 28034 (BL 400792385 28416) BE))) (BN 403604978 13316 (BN 402798314 14088 (BN 401989052 60162 (BL 401959775 1028) (BL 402785904 56064)) (BN 403294798 14336 (BL 402949510 1542) (BL 403421254 11266))) (BN 404188743 28546 (BN 403988209 58886 (BL 403782292 20998) (BL 403995790 28290)) (BN 404633335 56066 (BL 404345160 64901) BE)))) (BN 406427076 32256 (BN 405561280 19206 (BN 405228383 21632 (BN 404848649 24448 (BL 404659933 32384) (BL 405070365 57091)) (BN 405363902 24576 (BL 405297501 19076) (BL 405434300 52608))) (BN 406219579 13574 (BN 405595011 23304 (BL 405587559 57472) (BL 405916613 21760)) (BN 406278538 55040 (BL 406251688 63744) BE))) (BN 408101370 13184 (BN 407529898 29952 (BN 406767864 12288 (BL 406472756 6662) (BL 407385508 17926)) (BN 407575763 3200 (BL 407537659 62468) BE)) (BN 409055566 24578 (BN 408431788 61058 (BL 408206853 30982) (BL 408858880 55172)) (BN 409369979 13825 (BL 409098067 55936) BE))))) (BN 415663056 23814 (BN 412003084 20872 (BN 410537594 3584 (BN 409518589 13192 (BN 409493463 16000 (BL 409386604 27904) (BL 409506363 27779)) (BN 410041169 6402 (BL 410023557 15488) (BL 410161728 25474))) (BN 411407057 24064 (BN 411225793 23554 (BL 410975239 2305) (BL 411306286 59910)) (BN 411782170 64642 (BL 411593065 57474) BE))) (BN 414006421 63490 (BN 413648287 1920 (BN 412513952 28802 (BL 412018217 10242) (BL 413216547 14080)) (BN 413929461 65152 (BL 413805977 30209) BE)) (BN 414991225 10244 (BN 414883124 25089 (BL 414814216 6528) (BL 414893014 7426)) (BN 415557320 32128 (BL 415176037 28676) BE)))) (BN 417963671 62982 (BN 416454215 17410 (BN 416029063 15490 (BN 415768833 256 (BL 415742284 23046) (BL 415774131 14720)) (BN 416225352 26882 (BL 416118192 29440) (BL 416279205 28288))) (BN 417425986 55169 (BN 416949950 12930 (BL 416778802 52224) (BL 416955365 24450)) (BN 417694741 64770 (BL 417684427 62340) BE))) (BN 419427223 17412 (BN 418944610 22530 (BN 418713063 55553 (BL 418088916 55426) (BL 418779424 62976)) (BN 419319122 10753 (BL 419310697 22786) BE)) (BN 420210129 5504 (BN 420100568 28161 (BL 419705903 64640) (BL 420188405 19713)) (BN 420445185 28928 (BL 420340996 31489) BE)))))) (BN 432512151 58370 (BN 426435264 3840 (BN 423231267 23557 (BN 422100783 1794 (BN 421272612 53640 (BN 420730420 54016 (BL 420715203 61056) (BL 420866955 24320)) (BN 421384149 16128 (BL 421342271 2176) (BL 421539182 30720))) (BN 422920608 4992 (BN 422524914 14978 (BL 422264087 55940) (BL 422674722 19714)) (BN 423224362 513 (BL 422969204 12290) BE))) (BN 424934098 11777 (BN 424207614 16388 (BN 424024557 14594 (BL 423380608 54274) (BL 424083744 55680)) (BN 424517794 2052 (BL 424353070 16896) BE)) (BN 425820147 60544 (BN 425302953 11392 (BL 425166418 13056) (BL 425425166 4352)) (BN 426081493 57986 (BL 425900411 62464) BE)))) (BN 429370096 60929 (BN 427982591 5377 (BN 427036498 17154 (BN 426448527 62082 (BL 426443191 28800) (BL 426632296 10880)) (BN 427660360 20993 (BL 427267304 26498) (BL 427814807 18434))) (BN 429060612 18562 (BN 428643612 8196 (BL 428478303 31491) (BL 428789068 18944)) (BN 429333051 12800 (BL 429299704 6657) BE))) (BN 430021065 51968 (BN 429727898 4614 (BN 429457933 60673 (BL 429403694 53379) (BL 429476762 26624)) (BN 429841351 22532 (BL 429786942 2304) BE)) (BN 430879189 12928 (BN 430646315 3334 (BL 430631614 20608) (BL 430806307 56705)) (BN 432250805 1026 (BL 431692595 32137) BE))))) (BN 438197328 62084 (BN 434277349 54276 (BN 433912760 9216 (BN 433334294 32515 (BN 432819364 644 (BL 432513379 26496) (BL 433065837 52737)) (BN 433694827 25088 (BL 433519905 26753) (BL 433839692 25219))) (BN 433972203 59524 (BN 433940986 57862 (BL 433928769 27649) (BL 433962701 59264)) (BN 434171793 60672 (BL 434118677 8449) BE))) (BN 436152443 63234 (BN 434771559 25729 (BN 434519263 10496 (BL 434457063 11008) (BL 434639571 54784)) (BN 435253090 60160 (BL 435067612 31872) BE)) (BN 437820645 63488 (BN 437169288 9344 (BL 436950909 22272) (BL 437626942 16902)) (BN 438130825 10752 (BL 437836654 3073) BE)))) (BN 442272652 19457 (BN 441020603 56320 (BN 438955261 54528 (BN 438408201 27268 (BL 438402369 26754) (BL 438952207 16641)) (BN 439891533 62470 (BL 439798316 10884) (BL 440010732 57984))) (BN 442062940 18950 (BN 441687109 53377 (BL 441454437 19072) (BL 441878128 62592)) (BN 442243414 11520 (BL 442088892 17028) BE))) (BN 443976010 32133 (BN 443408892 58372 (BN 442989851 18560 (BL 442606923 12806) (BL 443388205 24833)) (BN 443653203 643 (BL 443464098 57475) BE)) (BN 446123107 25217 (BN 445906045 55814 (BL 444093222 384) (BL 446048167 52736)) (BN 446441204 65024 (BL 446126365 9600) BE))))))) (BN 477290399 6912 (BN 461560047 52743 (BN 455190165 61444 (BN 450782476 13826 (BN 448579945 12033 (BN 447900096 15491 (BN 447296090 53761 (BL 446968699 25094) (BL 447612901 2822)) (BN 448021476 20098 (BL 448017199 14208) (BL 448297018 13568))) (BN 450052809 2049 (BN 449377379 7168 (BL 449017454 3328) (BL 449489697 32000)) (BN 450686405 32514 (BL 450284292 30976) BE))) (BN 452770680 2562 (BN 451767397 14082 (BN 451404697 10758 (BL 451112013 19974) (BL 451584705 15104)) (BN 452331608 26752 (BL 452226566 64513) (BL 452647132 9729))) (BN 453971816 1795 (BN 453128188 57856 (BL 453015943 5249) (BL 453190855 20868)) (BN 454336673 21122 (BL 454282524 4737) BE)))) (BN 459321017 21254 (BN 457740495 23808 (BN 456334533 56200 (BN 455572747 11776 (BL 455218474 30210) (BL 455936618 641)) (BN 457554884 14849 (BL 456728254 19584) (BL 457708869 770))) (BN 458621240 5376 (BN 458168178 5638 (BL 457989087 4609) (BL 458254360 896)) (BN 459110144 18694 (BL 458839902 16768) BE))) (BN 460459313 61696 (BN 460008745 60928 (BN 459533857 7681 (BL 459522755 28672) (BL 459614269 11648)) (BN 460321272 62208 (BL 460295285 6406) BE)) (BN 460767331 5122 (BN 460575895 4608 (BL 460487079 8320) (BL 460652725 14854)) (BN 461493809 23299 (BL 461341565 56713) BE))))) (BN 468864512 2048 (BN 465147130 7430 (BN 462148347 4224 (BN 461792091 55297 (BN 461696512 15360 (BL 461606480 18433) (BL 461699005 11906)) (BN 462123674 59392 (BL 461824000 52482) (BL 462144867 4866))) (BN 464321708 57348 (BN 463546142 9478 (BL 462460383 53636) (BL 463552052 21121)) (BN 464750196 7680 (BL 464367198 8704) BE))) (BN 467437706 22022 (BN 466559672 25600 (BN 466228089 13313 (BL 466042478 1025) (BL 466510604 54785)) (BN 466813168 56192 (BL 466579066 64002) BE)) (BN 468265912 21120 (BN 468109430 8576 (BL 468071252 1536) (BL 468153853 4226)) (BN 468803196 51712 (BL 468757706 4100) BE)))) (BN 473551966 57601 (BN 471262037 6144 (BN 469590856 16640 (BN 469074740 10370 (BL 468883797 28032) (BL 469564813 22790)) (BN 470974850 60288 (BL 469922253 31238) (BL 471038269 64512))) (BN 472392069 60296 (BN 471467954 10497 (BL 471276410 21762) (BL 471664072 5124)) (BN 473499157 20484 (BL 472507250 17920) BE))) (BN 474512360 3842 (BN 474026854 24832 (BN 473749161 62593 (BL 473624980 56709) (BL 473982420 11904)) (BN 474280537 24065 (BL 474278673 14598) BE)) (BN 475903952 54529 (BN 475180096 62465 (BL 474921812 59654) (BL 475698035 21504)) (BN 476447935 6401 (BL 475936226 21248) BE)))))) (BN 501067954 58880 (BN 488263925 56832 (BN 482579383 640 (BN 480244378 7040 (BN 478029777 57345 (BN 477934739 53760 (BL 477641070 8710) (BL 477944937 32512)) (BN 478958591 18432 (BL 478768305 57600) (BL 479229708 52742))) (BN 482077068 51718 (BN 481532469 13441 (BL 480603794 55296) (BL 481661597 7048)) (BN 482465775 4097 (BL 482350520 21376) BE))) (BN 483767739 21384 (BN 483469394 11264 (BN 483394589 1024 (BL 483003979 10368) (BL 483410598 52225)) (BN 483600506 6656 (BL 483550065 56833) BE)) (BN 486898037 25858 (BN 485717463 25857 (BL 485039792 13312) (BL 485827138 9987)) (BN 487557547 57088 (BL 487055058 18176) BE)))) (BN 494541295 56196 (BN 491993545 27776 (BN 489690340 2816 (BN 488434036 59904 (BL 488298646 4353) (BL 489505776 10881)) (BN 491620048 54144 (BL 491208611 53766) (BL 491848911 17024))) (BN 493037267 54152 (BN 492374443 26112 (BL 492206531 12801) (BL 492870034 23040)) (BN 494205057 58369 (BL 494050386 15366) BE))) (BN 498681189 19200 (BN 497012886 53252 (BN 496167565 58626 (BL 495990296 58881) (BL 496426039 10240)) (BN 498110553 9985 (BL 497568174 20737) BE)) (BN 500024886 4227 (BN 499531590 60674 (BL 499427422 57857) (BL 499536883 61440)) (BN 500878046 11265 (BL 500862037 17408) BE))))) (BN 524245476 5633 (BN 509995967 3585 (BN 503557348 23552 (BN 502282034 20736 (BN 501710640 31744 (BL 501476059 29185) (BL 501720574 59905)) (BN 502604802 18688 (BL 502372724 6400) (BL 503392143 64518))) (BN 507224569 7424 (BN 506189919 29184 (BL 506156572 23041) (BL 507040800 9472)) (BN 508668426 57344 (BL 508556907 26880) BE))) (BN 515712163 54272 (BN 512078116 52486 (BN 511276165 22528 (BL 510898023 55809) (BL 511642252 22784)) (BN 513104424 4096 (BL 512629536 20481) BE)) (BN 519463791 29190 (BN 517845875 20480 (BL 516356112 14592) (BL 518416470 59648)) (BN 523033795 55808 (BL 520510071 17027) BE)))) (BN 546421681 58630 (BN 534411752 31233 (BN 529295713 7169 (BN 528297072 10241 (BL 524843706 58368) (BL 529066866 16512)) (BN 532793486 17025 (BL 532733070 17409) (BL 534064514 31750))) (BN 539425678 23809 (BN 537152153 25862 (BL 536645744 53249) (BL 537780475 14848)) (BN 543980991 23296 (BL 541359604 53248) BE))) (BN 557550893 23553 (BN 553304803 22785 (BN 548385026 5121 (BL 547050003 31232) (BL 553098886 5120)) (BN 555247923 5632 (BL 554155555 52480) BE)) (BN 579229592 25856 (BN 564517451 22016 (BL 562574331 58625) (BL 570098049 7425)) (BN 601102344 22017 (BL 588499120 58624) BE))))))))
def RtT11 : BTree NodeData := nd (nd (nd (lf 0x10007f1 [0x11000010002,0x13000b010d,0x17000a000c,0x100014]) (nd (lf 0x3000771 [0x10200010010,0x14000a010d]) (lf 0x23000771 [0x10d01020001,0x14000a000b,0x10]))) (nd (nd (lf 0x230007f1 [0x10200010010,0x18000b010d,0x17000a000c,0x14]) (lf 0x40007f1 [0x1020001000c,0x10010d0110,0x170014])) (nd (lf 0x240007f1 [0x50001000a,0x10d01100102,0x140017]) (lf 0x14300771 [0x1010102000a,0x140005010d])))) (nd (nd (nd (lf 0x143006f1 [0x10101020010,0xa010d]) (lf 0x143007f1 [0x1020010000a,0x5010d0101,0x140017])) (nd (lf 0x24300771 [0x1010102000a,0x140005010d]) (lf 0x343006f1 [0x10101020010,0xc010d]))) (nd (nd (lf 0x343007f1 [0x1020010000c,0xa010d0101,0x170014]) (lf 0x54007f1 [0x1020017000c,0x110010d0101,0x10])) (nd (lf 0x154007f1 [0x1020014000a,0x110010d0101]) (lf 0x254007f1 [0x102000c0014,0x110010d0101,0x10]))))
def RtM11 : BST := BN 362285912 256 (BN 317684075 1536 (BN 295491291 13700 (BN 273534625 12672 (BN 264282250 14600 (BN 250466774 16130 (BN 230514779 16136 (BN 222818225 5760 (BL 215832826 640) BE) (BL 243258812 16256)) (BN 262825779 15876 (BN 261797703 1288 (BL 258390507 16128) BE) (BL 263144928 13956))) (BN 267580926 2436 (BN 265985320 6020 (BN 265310326 7684 (BL 264877107 3456) BE) (BL 266233701 6920)) (BN 269871131 12418 (BL 268718248 2824) (BL 271702550 16132)))) (BN 285744264 5764 (BN 278956596 11908 (BN 277820531 5768 (BN 276669541 904 (BL 274812835 13704) BE) (BL 278884441 2176)) (BN 283401129 1920 (BL 281882229 4229) (BL 284366776 128))) (BN 291636007 3336 (BN 289616129 4738 (BN 288445334 14469 (BL 288013357 7040) BE) (BL 290019536 4233)) (BN 292504083 130 (BL 292449355 15232) (BL 292664083 4356))))) (BN 306238198 1408 (BN 300977764 7432 (BN 297304002 12160 (BN 296615988 5896 (BN 296582641 14473 (BL 296072005 3848) BE) (BL 296830745 13696)) (BN 299451935 2050 (BL 299141145 15880) (BL 300375841 896))) (BN 302155034 6016 (BN 301802200 3712 (BN 301740000 8064 (BL 301625692 7688) BE) (BL 302005840 2308)) (BN 304668313 2948 (BL 304655074 12928) (BL 305413762 7944)))) (BN 313545926 13058 (BN 311972837 514 (BN 309526351 15744 (BN 308706670 6400 (BL 306743549 2053) BE) (BL 311792762 645)) (BN 313142668 4864 (BL 312309886 7296) (BL 313348585 2688))) (BN 316300391 11656 (BN 315579955 5504 (BN 314921656 3968 (BL 313934752 2184) BE) (BL 315833132 14464)) (BN 316745884 15488 (BL 316700514 13445) (BL 317567229 4480)))))) (BN 343219163 2952 (BN 332799581 14596 (BN 327324047 1664 (BN 322120073 5632 (BN 319930069 649 (BN 319250710 258 (BL 317887030 3972) BE) (BL 320666662 6272)) (BN 325023432 13184 (BL 324837821 13449) (BL 325102660 1152))) (BN 330315034 1284 (BN 328979449 4360 (BN 328164126 14465 (BL 327604209 6024) BE) (BL 329194454 14593)) (BN 332678211 12548 (BL 331650135 11528) (BL 332737975 2689)))) (BN 338321206 2312 (BN 337235579 2820 (BN 335248036 13826 (BN 334751032 6916 (BL 333630452 2817) BE) (BL 336086133 12040)) (BN 337517372 7425 (BL 337331761 14595) (BL 337848955 5378))) (BN 341767759 2819 (BN 340006691 11648 (BN 339088274 768 (BL 338750891 3713) BE) (BL 340228017 2562)) (BN 342284953 15106 (BL 341953370 7937) (BL 343186889 1409))))) (BN 355266421 5248 (BN 349698797 900 (BN 345217676 1800 (BN 344279613 4098 (BN 343730872 7809 (BL 343301362 15616) BE) (BL 344589793 11778)) (BN 346987318 3328 (BL 346743646 5761) (BL 348715611 12290))) (BN 353000400 6529 (BN 351778194 5376 (BN 351511554 641 (BL 351423316 3840) BE) (BL 351967299 5888)) (BN 355122523 2180 (BL 354683872 14594) (BL 355176354 4100)))) (BN 359119870 2818 (BN 356419306 13441 (BN 356329075 7424 (BN 356214192 15104 (BL 355663848 13318) BE) (BL 356335572 12416)) (BN 357109939 4736 (BL 356973277 14208) (BL 358148395 5126))) (BN 360765073 7936 (BN 359657380 12936 (BN 359612352 12292 (BL 359194675 4226) BE) (BL 360153338 3332)) (BN 360993155 6785 (BL 360866204 6277) (BL 362226953 518))))))) (BN 400568987 1792 (BN 377278904 5769 (BN 370013101 13440 (BN 368470520 13952 (BN 365302202 1157 (BN 365044751 6401 (BN 364589336 3844 (BL 363273233 2697) BE) (BL 365133319 5892)) (BN 367528554 6784 (BL 365964126 3976) (BL 367581113 12932))) (BN 369495095 7428 (BN 369003511 6281 (BN 368993577 12552 (BL 368681393 2944) BE) (BL 369480749 4865)) (BN 369887739 13960 (BL 369655661 7808) (BL 369930338 1793)))) (BN 373931093 7940 (BN 372906518 2432 (BN 371776207 3072 (BN 371478090 4224 (BL 370043653 5253) BE) (BL 372151320 1282)) (BN 373439509 1161 (BL 373420738 2052) (BL 373472856 14088))) (BN 375556648 2693 (BN 374824700 14848 (BN 374507506 4992 (BL 374323737 2440) BE) (BL 375262164 3586)) (BN 376798082 14976 (BL 376587318 6914) (BL 376951885 769))))) (BN 388829705 4610 (BN 384282188 11904 (BN 380525168 4 (BN 379282629 3200 (BN 378925189 16000 (BL 378180960 5257) BE) (BL 380075053 1280)) (BN 383043872 1538 (BL 382063257 13056) (BL 383639049 384))) (BN 385699407 11912 (BN 385502152 13830 (BN 384511051 6912 (BL 384393707 15362) BE) (BL 385617898 7681)) (BN 387001446 11520 (BL 385794316 7168) (BL 387479870 5634)))) (BN 393571156 12802 (BN 391437444 12032 (BN 389702201 14336 (BN 389562319 5765 (BL 389329647 11652) BE) (BL 390482133 2566)) (BN 391783490 2048 (BL 391528413 6793) (BL 393557382 3205))) (BN 394843909 11782 (BN 394138199 1024 (BN 393940816 2305 (BL 393755205 7683) BE) (BL 394409743 13570)) (BN 400167466 11524 (BL 395871643 14592) (BL 400307641 2816)))))) (BN 434647823 15366 (BN 414840779 5889 (BN 405020994 1153 (BN 403811828 6789 (BN 402976073 14342 (BN 401694689 3209 (BL 400584996 6273) BE) (BL 403410762 4352)) (BN 404304392 512 (BL 404022353 1283) (BL 404603464 12036))) (BN 409762445 5249 (BN 408338982 13568 (BN 407412071 1030 (BL 406708615 13185) BE) (BL 408458351 6915)) (BN 412752519 2304 (BL 411107316 7682) (BL 413735007 1796)))) (BN 424871886 0 (BN 420587740 16001 (BN 417924034 5121 (BN 417084885 6658 (BL 416305768 1281) BE) (BL 418109645 11777)) (BN 421438492 7552 (BL 420741766 6913) (BL 424110307 14081))) (BN 428824167 14080 (BN 427579591 13824 (BN 427045643 6144 (BL 425516280 3590) BE) (BL 428574764 15874)) (BN 432559572 2560 (BL 429857268 14721) (BL 433276174 3201))))) (BN 452295087 7680 (BN 441063175 2049 (BN 437380986 4993 (BN 436611168 4096 (BN 436498497 15872 (BL 435276145 5120) BE) (BL 436921348 11776)) (BN 439083821 4614 (BL 437850023 14977) (BL 441047166 12288))) (BN 445531672 15617 (BN 443424890 12544 (BN 441990187 14084 (BL 441253083 513) BE) (BL 443825272 12806)) (BN 446512529 6528 (BL 446086613 15361) (BL 450522611 4609)))) (BN 476725262 15360 (BN 467339001 6662 (BN 459399517 6150 (BN 455782057 14720 (BL 452743593 13312) BE) (BL 460445797 15875)) (BN 468385281 14985 (BL 467593719 3584) (BL 472729212 15873))) (BN 485902711 12800 (BN 481161260 4608 (BN 480686372 12801 (BL 480668696 14981) BE) (BL 484614626 13313)) (BN 504702580 6657 (BL 495433052 2561) (BL 509416440 6656)))))))
def RtT12 : BTree NodeData := lf 0x3f0 [0xd00010002,0x10]
def RtM12 : BST := BN 317805548 1153 (BN 294862528 1408 (BN 271587329 128 (BN 261421136 264 (BN 258013214 516 (BL 256985138 1544) BE) (BN 267508771 1280 (BL 265024224 768) BE)) (BN 285392582 1921 (BN 285206971 1289 (BL 277069664 1285) BE) (BL 294328580 520))) (BN 308536020 129 (BN 302559082 1288 (BN 300597167 2 (BL 299842509 1664) BE) (BL 304204285 1920)) (BN 316772447 256 (BN 313369550 1793 (BL 312336449 1536) BE) (BL 316788456 1281)))) (BN 348444197 1152 (BN 329938467 260 (BN 325502469 1540 (BN 321362305 769 (BL 320026530 776) BE) (BL 327950263 772)) (BN 344008199 1792 (BN 343746853 1284 (BL 334876656 896) BE) (BL 347969309 641))) (BN 364180978 773 (BN 353185648 640 (BN 351897563 777 (BL 350851283 6) BE) (BL 362715989 1665)) (BN 376699377 384 (BN 371985517 385 (BL 368759893 512) BE) (BL 392928722 0))))
def RtL : Nat → Option (BTree NodeData) | 5 => some RtT5 | 6 => some RtT6 | 7 => some RtT7 | 8 => some RtT8 | 9 => some RtT9 | 10 => some RtT10 | 11 => some RtT11 | 12 => some RtT12 | _ => none
def RtM : Nat → BST | 6 => RtM6 | 7 => RtM7 | 8 => RtM8 | 9 => RtM9 | 10 => RtM10 | 11 => RtM11 | 12 => RtM12 | _ => BE
end CertData
noncomputable section CertVerify
abbrev ok (f : Forest) (k : Nat) (t : BTree NodeData) := t.all (fastNodeOK f k) = true
def base0 (_ : Nat) : List Sig × Sig × Nat := ([], 0, 0)
private theorem base0_s : ∀ k, k ≠ 0 → LowerBV (base0 k).1 (base0 k).2.1 (base0 k).2.2 := fun _ _ _ _ _ _ => Nat.zero_le _
def fF1 : Forest := ⟨56,tF1,3,F1P,F1N,F1R,F1A,F1C,F1L,F1M⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F1v : graphValid fF1 base0 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F1k3 : ok fF1 3 F1T3 := by decide +kernel
private theorem F1lv : levelsChecked fF1 := by
  intro k hk tree ht; change k ≤ 3 at hk; interval_cases k
  all_goals simp [fF1,F1L] at ht
  subst ht; exact F1k3
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowF1 : LowerBV (rawOf 56) tF1 4 :=
  lower_forest fF1 base0 base0_s F1v F1lv (by decide +kernel)
def base1 : Nat → List Sig × Sig × Nat | 1 => (rawOf 56,tF1,4) | _ => ([],0,0)
private theorem base1_s : ∀ k, k ≠ 0 → LowerBV (base1 k).1 (base1 k).2.1 (base1 k).2.2 := by
  intro k _; match k with
  | 1 => exact lowF1
  | 0 | _ + 2 => exact fun _ _ _ _ => Nat.zero_le _
def fF2 : Forest := ⟨60,tF2,6,F2P,F2N,F2R,F2A,F2C,F2L,F2M⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F2v : graphValid fF2 base1 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F2k3 : ok fF2 3 F2T3 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F2k4 : ok fF2 4 F2T4 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F2k5 : ok fF2 5 F2T5 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F2k6 : ok fF2 6 F2T6 := by decide +kernel
private theorem F2lv : levelsChecked fF2 := by
  intro k hk tree ht; change k ≤ 6 at hk; interval_cases k
  all_goals simp [fF2,F2L] at ht
  · subst ht; exact F2k3
  · subst ht; exact F2k4
  · subst ht; exact F2k5
  · subst ht; exact F2k6
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowF2 : LowerBV (rawOf 60) tF2 7 :=
  lower_forest fF2 base1 base1_s F2v F2lv (by decide +kernel)
def base2 : Nat → List Sig × Sig × Nat | 1 => (rawOf 56,tF1,4) | 2 => (rawOf 60,tF2,7) | _ => ([],0,0)
private theorem base2_s : ∀ k, k ≠ 0 → LowerBV (base2 k).1 (base2 k).2.1 (base2 k).2.2 := by
  intro k _; match k with
  | 1 => exact lowF1
  | 2 => exact lowF2
  | 0 | _ + 3 => exact fun _ _ _ _ => Nat.zero_le _
def fF3 : Forest := ⟨46,tF3,4,F3P,F3N,F3R,F3A,F3C,F3L,F3M⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F3v : graphValid fF3 base2 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F3k4 : ok fF3 4 F3T4 := by decide +kernel
private theorem F3lv : levelsChecked fF3 := by
  intro k hk tree ht; change k ≤ 4 at hk; interval_cases k
  all_goals simp [fF3,F3L] at ht
  subst ht; exact F3k4
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowF3 : LowerBV (rawOf 46) tF3 5 :=
  lower_forest fF3 base2 base2_s F3v F3lv (by decide +kernel)
def base3 : Nat → List Sig × Sig × Nat | 1 => (rawOf 56,tF1,4) | 2 => (rawOf 60,tF2,7) | 3 => (rawOf 46,tF3,5) | _ => ([],0,0)
private theorem base3_s : ∀ k, k ≠ 0 → LowerBV (base3 k).1 (base3 k).2.1 (base3 k).2.2 := by
  intro k _; match k with
  | 1 => exact lowF1
  | 2 => exact lowF2
  | 3 => exact lowF3
  | 0 | _ + 4 => exact fun _ _ _ _ => Nat.zero_le _
def fF4 : Forest := ⟨60,tF4,4,F4P,F4N,F4R,F4A,F4C,F4L,F4M⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F4v : graphValid fF4 base3 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F4k4 : ok fF4 4 F4T4 := by decide +kernel
private theorem F4lv : levelsChecked fF4 := by
  intro k hk tree ht; change k ≤ 4 at hk; interval_cases k
  all_goals simp [fF4,F4L] at ht
  subst ht; exact F4k4
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowF4 : LowerBV (rawOf 60) tF4 5 :=
  lower_forest fF4 base3 base3_s F4v F4lv (by decide +kernel)
def base4 : Nat → List Sig × Sig × Nat | 1 => (rawOf 56,tF1,4) | 2 => (rawOf 60,tF2,7) | 3 => (rawOf 46,tF3,5) | 4 => (rawOf 60,tF4,5) | _ => ([],0,0)
private theorem base4_s : ∀ k, k ≠ 0 → LowerBV (base4 k).1 (base4 k).2.1 (base4 k).2.2 := by
  intro k _; match k with
  | 1 => exact lowF1
  | 2 => exact lowF2
  | 3 => exact lowF3
  | 4 => exact lowF4
  | 0 | _ + 5 => exact fun _ _ _ _ => Nat.zero_le _
def fF5 : Forest := ⟨54,tF5,6,F5P,F5N,F5R,F5A,F5C,F5L,F5M⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F5v : graphValid fF5 base4 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F5k3 : ok fF5 3 F5T3 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F5k4 : ok fF5 4 F5T4 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F5k5 : ok fF5 5 F5T5 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F5k6 : ok fF5 6 F5T6 := by decide +kernel
private theorem F5lv : levelsChecked fF5 := by
  intro k hk tree ht; change k ≤ 6 at hk; interval_cases k
  all_goals simp [fF5,F5L] at ht
  · subst ht; exact F5k3
  · subst ht; exact F5k4
  · subst ht; exact F5k5
  · subst ht; exact F5k6
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowF5 : LowerBV (rawOf 54) tF5 7 :=
  lower_forest fF5 base4 base4_s F5v F5lv (by decide +kernel)
def base5 : Nat → List Sig × Sig × Nat | 1 => (rawOf 56,tF1,4) | 2 => (rawOf 60,tF2,7) | 3 => (rawOf 46,tF3,5) | 4 => (rawOf 60,tF4,5) | 5 => (rawOf 54,tF5,7) | _ => ([],0,0)
private theorem base5_s : ∀ k, k ≠ 0 → LowerBV (base5 k).1 (base5 k).2.1 (base5 k).2.2 := by
  intro k _; match k with
  | 1 => exact lowF1
  | 2 => exact lowF2
  | 3 => exact lowF3
  | 4 => exact lowF4
  | 5 => exact lowF5
  | 0 | _ + 6 => exact fun _ _ _ _ => Nat.zero_le _
def fF6 : Forest := ⟨46,tF6,4,F6P,F6N,F6R,F6A,F6C,F6L,F6M⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F6v : graphValid fF6 base5 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F6k4 : ok fF6 4 F6T4 := by decide +kernel
private theorem F6lv : levelsChecked fF6 := by
  intro k hk tree ht; change k ≤ 4 at hk; interval_cases k
  all_goals simp [fF6,F6L] at ht
  subst ht; exact F6k4
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowF6 : LowerBV (rawOf 46) tF6 5 :=
  lower_forest fF6 base5 base5_s F6v F6lv (by decide +kernel)
def base6 : Nat → List Sig × Sig × Nat | 1 => (rawOf 56,tF1,4) | 2 => (rawOf 60,tF2,7) | 3 => (rawOf 46,tF3,5) | 4 => (rawOf 60,tF4,5) | 5 => (rawOf 54,tF5,7) | 6 => (rawOf 46,tF6,5) | _ => ([],0,0)
private theorem base6_s : ∀ k, k ≠ 0 → LowerBV (base6 k).1 (base6 k).2.1 (base6 k).2.2 := by
  intro k _; match k with
  | 1 => exact lowF1
  | 2 => exact lowF2
  | 3 => exact lowF3
  | 4 => exact lowF4
  | 5 => exact lowF5
  | 6 => exact lowF6
  | 0 | _ + 7 => exact fun _ _ _ _ => Nat.zero_le _
def fF7 : Forest := ⟨39,tF7,5,F7P,F7N,F7R,F7A,F7C,F7L,F7M⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7v : graphValid fF7 base6 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7k2 : ok fF7 2 F7T2 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7k3 : ok fF7 3 F7T3 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7k4 : ok fF7 4 F7T4 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7k5 : ok fF7 5 F7T5 := by decide +kernel
private theorem F7lv : levelsChecked fF7 := by
  intro k hk tree ht; change k ≤ 5 at hk; interval_cases k
  all_goals simp [fF7,F7L] at ht
  · subst ht; exact F7k2
  · subst ht; exact F7k3
  · subst ht; exact F7k4
  · subst ht; exact F7k5
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowF7 : LowerBV (rawOf 39) tF7 6 :=
  lower_forest fF7 base6 base6_s F7v F7lv (by decide +kernel)
def base7 : Nat → List Sig × Sig × Nat | 1 => (rawOf 56,tF1,4) | 2 => (rawOf 60,tF2,7) | 3 => (rawOf 46,tF3,5) | 4 => (rawOf 60,tF4,5) | 5 => (rawOf 54,tF5,7) | 6 => (rawOf 46,tF6,5) | 7 => (rawOf 39,tF7,6) | _ => ([],0,0)
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
def fF8 : Forest := ⟨55,tF8,6,F8P,F8N,F8R,F8A,F8C,F8L,F8M⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F8v : graphValid fF8 base7 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F8k6 : ok fF8 6 F8T6 := by decide +kernel
private theorem F8lv : levelsChecked fF8 := by
  intro k hk tree ht; change k ≤ 6 at hk; interval_cases k
  all_goals simp [fF8,F8L] at ht
  subst ht; exact F8k6
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowF8 : LowerBV (rawOf 55) tF8 7 :=
  lower_forest fF8 base7 base7_s F8v F8lv (by decide +kernel)
def base8 : Nat → List Sig × Sig × Nat | 1 => (rawOf 56,tF1,4) | 2 => (rawOf 60,tF2,7) | 3 => (rawOf 46,tF3,5) | 4 => (rawOf 60,tF4,5) | 5 => (rawOf 54,tF5,7) | 6 => (rawOf 46,tF6,5) | 7 => (rawOf 39,tF7,6) | 8 => (rawOf 55,tF8,7) | _ => ([],0,0)
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
def fF9 : Forest := ⟨47,tF9,8,F9P,F9N,F9R,F9A,F9C,F9L,F9M⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F9v : graphValid fF9 base8 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F9k2 : ok fF9 2 F9T2 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F9k3 : ok fF9 3 F9T3 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F9k4 : ok fF9 4 F9T4 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F9k5 : ok fF9 5 F9T5 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F9k6 : ok fF9 6 F9T6 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F9k7 : ok fF9 7 F9T7 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F9k8 : ok fF9 8 F9T8 := by decide +kernel
private theorem F9lv : levelsChecked fF9 := by
  intro k hk tree ht; change k ≤ 8 at hk; interval_cases k
  all_goals simp [fF9,F9L] at ht
  · subst ht; exact F9k2
  · subst ht; exact F9k3
  · subst ht; exact F9k4
  · subst ht; exact F9k5
  · subst ht; exact F9k6
  · subst ht; exact F9k7
  · subst ht; exact F9k8
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowF9 : LowerBV (rawOf 47) tF9 9 :=
  lower_forest fF9 base8 base8_s F9v F9lv (by decide +kernel)
def base9 : Nat → List Sig × Sig × Nat | 1 => (rawOf 56,tF1,4) | 2 => (rawOf 60,tF2,7) | 3 => (rawOf 46,tF3,5) | 4 => (rawOf 60,tF4,5) | 5 => (rawOf 54,tF5,7) | 6 => (rawOf 46,tF6,5) | 7 => (rawOf 39,tF7,6) | 8 => (rawOf 55,tF8,7) | 9 => (rawOf 47,tF9,9) | _ => ([],0,0)
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
def fF10 : Forest := ⟨62,tF10,7,F10P,F10N,F10R,F10A,F10C,F10L,F10M⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F10v : graphValid fF10 base9 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F10k3 : ok fF10 3 F10T3 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F10k4 : ok fF10 4 F10T4 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F10k5_0 : ok fF10 5 F10T5_0 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F10k5_1 : ok fF10 5 F10T5_1 := by decide +kernel
private theorem F10k5 : ok fF10 5 F10T5 := by
  simp only [ok,F10T5,nd,BTree.all,F10k5_0,F10k5_1,Bool.and_true]
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F10k6 : ok fF10 6 F10T6 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F10k7 : ok fF10 7 F10T7 := by decide +kernel
private theorem F10lv : levelsChecked fF10 := by
  intro k hk tree ht; change k ≤ 7 at hk; interval_cases k
  all_goals simp [fF10,F10L] at ht
  · subst ht; exact F10k3
  · subst ht; exact F10k4
  · subst ht; exact F10k5
  · subst ht; exact F10k6
  · subst ht; exact F10k7
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowF10 : LowerBV (rawOf 62) tF10 8 :=
  lower_forest fF10 base9 base9_s F10v F10lv (by decide +kernel)
def base10 : Nat → List Sig × Sig × Nat | 1 => (rawOf 56,tF1,4) | 2 => (rawOf 60,tF2,7) | 3 => (rawOf 46,tF3,5) | 4 => (rawOf 60,tF4,5) | 5 => (rawOf 54,tF5,7) | 6 => (rawOf 46,tF6,5) | 7 => (rawOf 39,tF7,6) | 8 => (rawOf 55,tF8,7) | 9 => (rawOf 47,tF9,9) | 10 => (rawOf 62,tF10,8) | _ => ([],0,0)
private theorem base10_s : ∀ k, k ≠ 0 → LowerBV (base10 k).1 (base10 k).2.1 (base10 k).2.2 := by
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
  | 10 => exact lowF10
  | 0 | _ + 11 => exact fun _ _ _ _ => Nat.zero_le _
def fF11 : Forest := ⟨55,tF11,9,F11P,F11N,F11R,F11A,F11C,F11L,F11M⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F11v : graphValid fF11 base10 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F11k3 : ok fF11 3 F11T3 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F11k4 : ok fF11 4 F11T4 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F11k5_0 : ok fF11 5 F11T5_0 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F11k5_1 : ok fF11 5 F11T5_1 := by decide +kernel
private theorem F11k5 : ok fF11 5 F11T5 := by
  simp only [ok,F11T5,nd,BTree.all,F11k5_0,F11k5_1,Bool.and_true]
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F11k6 : ok fF11 6 F11T6 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F11k7 : ok fF11 7 F11T7 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F11k8 : ok fF11 8 F11T8 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F11k9 : ok fF11 9 F11T9 := by decide +kernel
private theorem F11lv : levelsChecked fF11 := by
  intro k hk tree ht; change k ≤ 9 at hk; interval_cases k
  all_goals simp [fF11,F11L] at ht
  · subst ht; exact F11k3
  · subst ht; exact F11k4
  · subst ht; exact F11k5
  · subst ht; exact F11k6
  · subst ht; exact F11k7
  · subst ht; exact F11k8
  · subst ht; exact F11k9
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowF11 : LowerBV (rawOf 55) tF11 10 :=
  lower_forest fF11 base10 base10_s F11v F11lv (by decide +kernel)
def base11 : Nat → List Sig × Sig × Nat | 1 => (rawOf 56,tF1,4) | 2 => (rawOf 60,tF2,7) | 3 => (rawOf 46,tF3,5) | 4 => (rawOf 60,tF4,5) | 5 => (rawOf 54,tF5,7) | 6 => (rawOf 46,tF6,5) | 7 => (rawOf 39,tF7,6) | 8 => (rawOf 55,tF8,7) | 9 => (rawOf 47,tF9,9) | 10 => (rawOf 62,tF10,8) | 11 => (rawOf 55,tF11,10) | _ => ([],0,0)
private theorem base11_s : ∀ k, k ≠ 0 → LowerBV (base11 k).1 (base11 k).2.1 (base11 k).2.2 := by
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
  | 10 => exact lowF10
  | 11 => exact lowF11
  | 0 | _ + 12 => exact fun _ _ _ _ => Nat.zero_le _
def fF12 : Forest := ⟨47,tF12,8,F12P,F12N,F12R,F12A,F12C,F12L,F12M⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F12v : graphValid fF12 base11 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F12k3 : ok fF12 3 F12T3 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F12k4_0 : ok fF12 4 F12T4_0 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F12k4_1 : ok fF12 4 F12T4_1 := by decide +kernel
private theorem F12k4 : ok fF12 4 F12T4 := by
  simp only [ok,F12T4,nd,BTree.all,F12k4_0,F12k4_1,Bool.and_true]
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F12k5_0 : ok fF12 5 F12T5_0 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F12k5_1 : ok fF12 5 F12T5_1 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F12k5_2 : ok fF12 5 F12T5_2 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F12k5_3 : ok fF12 5 F12T5_3 := by decide +kernel
private theorem F12k5 : ok fF12 5 F12T5 := by
  simp only [ok,F12T5,nd,BTree.all,F12k5_0,F12k5_1,F12k5_2,F12k5_3,Bool.and_true]
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F12k6_0 : ok fF12 6 F12T6_0 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F12k6_1 : ok fF12 6 F12T6_1 := by decide +kernel
private theorem F12k6 : ok fF12 6 F12T6 := by
  simp only [ok,F12T6,nd,BTree.all,F12k6_0,F12k6_1,Bool.and_true]
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F12k7 : ok fF12 7 F12T7 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F12k8 : ok fF12 8 F12T8 := by decide +kernel
private theorem F12lv : levelsChecked fF12 := by
  intro k hk tree ht; change k ≤ 8 at hk; interval_cases k
  all_goals simp [fF12,F12L] at ht
  · subst ht; exact F12k3
  · subst ht; exact F12k4
  · subst ht; exact F12k5
  · subst ht; exact F12k6
  · subst ht; exact F12k7
  · subst ht; exact F12k8
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowF12 : LowerBV (rawOf 47) tF12 9 :=
  lower_forest fF12 base11 base11_s F12v F12lv (by decide +kernel)
def base12 : Nat → List Sig × Sig × Nat | 1 => (rawOf 56,tF1,4) | 2 => (rawOf 60,tF2,7) | 3 => (rawOf 46,tF3,5) | 4 => (rawOf 60,tF4,5) | 5 => (rawOf 54,tF5,7) | 6 => (rawOf 46,tF6,5) | 7 => (rawOf 39,tF7,6) | 8 => (rawOf 55,tF8,7) | 9 => (rawOf 47,tF9,9) | 10 => (rawOf 62,tF10,8) | 11 => (rawOf 55,tF11,10) | 12 => (rawOf 47,tF12,9) | _ => ([],0,0)
private theorem base12_s : ∀ k, k ≠ 0 → LowerBV (base12 k).1 (base12 k).2.1 (base12 k).2.2 := by
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
  | 10 => exact lowF10
  | 11 => exact lowF11
  | 12 => exact lowF12
  | 0 | _ + 13 => exact fun _ _ _ _ => Nat.zero_le _
def fF13 : Forest := ⟨62,tF13,9,F13P,F13N,F13R,F13A,F13C,F13L,F13M⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F13v : graphValid fF13 base12 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F13k3 : ok fF13 3 F13T3 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F13k4_0 : ok fF13 4 F13T4_0 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F13k4_1 : ok fF13 4 F13T4_1 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F13k4_2 : ok fF13 4 F13T4_2 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F13k4_3 : ok fF13 4 F13T4_3 := by decide +kernel
private theorem F13k4 : ok fF13 4 F13T4 := by
  simp only [ok,F13T4,nd,BTree.all,F13k4_0,F13k4_1,F13k4_2,F13k4_3,Bool.and_true]
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F13k5_0 : ok fF13 5 F13T5_0 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F13k5_1 : ok fF13 5 F13T5_1 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F13k5_2 : ok fF13 5 F13T5_2 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F13k5_3 : ok fF13 5 F13T5_3 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F13k5_4 : ok fF13 5 F13T5_4 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F13k5_5 : ok fF13 5 F13T5_5 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F13k5_6 : ok fF13 5 F13T5_6 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F13k5_7 : ok fF13 5 F13T5_7 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F13k5_8 : ok fF13 5 F13T5_8 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F13k5_9 : ok fF13 5 F13T5_9 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F13k5_10 : ok fF13 5 F13T5_10 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F13k5_11 : ok fF13 5 F13T5_11 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F13k5_12 : ok fF13 5 F13T5_12 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F13k5_13 : ok fF13 5 F13T5_13 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F13k5_14 : ok fF13 5 F13T5_14 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F13k5_15 : ok fF13 5 F13T5_15 := by decide +kernel
private theorem F13k5 : ok fF13 5 F13T5 := by
  simp only [ok,F13T5,nd,BTree.all,F13k5_0,F13k5_1,F13k5_2,F13k5_3,F13k5_4,F13k5_5,F13k5_6,F13k5_7,F13k5_8,F13k5_9,F13k5_10,F13k5_11,F13k5_12,F13k5_13,F13k5_14,F13k5_15,Bool.and_true]
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F13k6_0 : ok fF13 6 F13T6_0 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F13k6_1 : ok fF13 6 F13T6_1 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F13k6_2 : ok fF13 6 F13T6_2 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F13k6_3 : ok fF13 6 F13T6_3 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F13k6_4 : ok fF13 6 F13T6_4 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F13k6_5 : ok fF13 6 F13T6_5 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F13k6_6 : ok fF13 6 F13T6_6 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F13k6_7 : ok fF13 6 F13T6_7 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F13k6_8 : ok fF13 6 F13T6_8 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F13k6_9 : ok fF13 6 F13T6_9 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F13k6_10 : ok fF13 6 F13T6_10 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F13k6_11 : ok fF13 6 F13T6_11 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F13k6_12 : ok fF13 6 F13T6_12 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F13k6_13 : ok fF13 6 F13T6_13 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F13k6_14 : ok fF13 6 F13T6_14 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F13k6_15 : ok fF13 6 F13T6_15 := by decide +kernel
private theorem F13k6 : ok fF13 6 F13T6 := by
  simp only [ok,F13T6,nd,BTree.all,F13k6_0,F13k6_1,F13k6_2,F13k6_3,F13k6_4,F13k6_5,F13k6_6,F13k6_7,F13k6_8,F13k6_9,F13k6_10,F13k6_11,F13k6_12,F13k6_13,F13k6_14,F13k6_15,Bool.and_true]
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F13k7_0 : ok fF13 7 F13T7_0 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F13k7_1 : ok fF13 7 F13T7_1 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F13k7_2 : ok fF13 7 F13T7_2 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F13k7_3 : ok fF13 7 F13T7_3 := by decide +kernel
private theorem F13k7 : ok fF13 7 F13T7 := by
  simp only [ok,F13T7,nd,BTree.all,F13k7_0,F13k7_1,F13k7_2,F13k7_3,Bool.and_true]
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F13k8 : ok fF13 8 F13T8 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F13k9 : ok fF13 9 F13T9 := by decide +kernel
private theorem F13lv : levelsChecked fF13 := by
  intro k hk tree ht; change k ≤ 9 at hk; interval_cases k
  all_goals simp [fF13,F13L] at ht
  · subst ht; exact F13k3
  · subst ht; exact F13k4
  · subst ht; exact F13k5
  · subst ht; exact F13k6
  · subst ht; exact F13k7
  · subst ht; exact F13k8
  · subst ht; exact F13k9
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowF13 : LowerBV (rawOf 62) tF13 10 :=
  lower_forest fF13 base12 base12_s F13v F13lv (by decide +kernel)
def base13 : Nat → List Sig × Sig × Nat | 1 => (rawOf 56,tF1,4) | 2 => (rawOf 60,tF2,7) | 3 => (rawOf 46,tF3,5) | 4 => (rawOf 60,tF4,5) | 5 => (rawOf 54,tF5,7) | 6 => (rawOf 46,tF6,5) | 7 => (rawOf 39,tF7,6) | 8 => (rawOf 55,tF8,7) | 9 => (rawOf 47,tF9,9) | 10 => (rawOf 62,tF10,8) | 11 => (rawOf 55,tF11,10) | 12 => (rawOf 47,tF12,9) | 13 => (rawOf 62,tF13,10) | _ => ([],0,0)
private theorem base13_s : ∀ k, k ≠ 0 → LowerBV (base13 k).1 (base13 k).2.1 (base13 k).2.2 := by
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
  | 10 => exact lowF10
  | 11 => exact lowF11
  | 12 => exact lowF12
  | 13 => exact lowF13
  | 0 | _ + 14 => exact fun _ _ _ _ => Nat.zero_le _
def fRt : Forest := ⟨63,tRt,12,RtP,RtN,RtR,RtA,RtC,RtL,RtM⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtv : graphValid fRt base13 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk5 : ok fRt 5 RtT5 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk6_0 : ok fRt 6 RtT6_0 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk6_1 : ok fRt 6 RtT6_1 := by decide +kernel
private theorem Rtk6 : ok fRt 6 RtT6 := by
  simp only [ok,RtT6,nd,BTree.all,Rtk6_0,Rtk6_1,Bool.and_true]
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk7_0 : ok fRt 7 RtT7_0 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk7_1 : ok fRt 7 RtT7_1 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk7_2 : ok fRt 7 RtT7_2 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk7_3 : ok fRt 7 RtT7_3 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk7_4 : ok fRt 7 RtT7_4 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk7_5 : ok fRt 7 RtT7_5 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk7_6 : ok fRt 7 RtT7_6 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk7_7 : ok fRt 7 RtT7_7 := by decide +kernel
private theorem Rtk7 : ok fRt 7 RtT7 := by
  simp only [ok,RtT7,nd,BTree.all,Rtk7_0,Rtk7_1,Rtk7_2,Rtk7_3,Rtk7_4,Rtk7_5,Rtk7_6,Rtk7_7,Bool.and_true]
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk8_0 : ok fRt 8 RtT8_0 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk8_1 : ok fRt 8 RtT8_1 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk8_2 : ok fRt 8 RtT8_2 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk8_3 : ok fRt 8 RtT8_3 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk8_4 : ok fRt 8 RtT8_4 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk8_5 : ok fRt 8 RtT8_5 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk8_6 : ok fRt 8 RtT8_6 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk8_7 : ok fRt 8 RtT8_7 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk8_8 : ok fRt 8 RtT8_8 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk8_9 : ok fRt 8 RtT8_9 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk8_10 : ok fRt 8 RtT8_10 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk8_11 : ok fRt 8 RtT8_11 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk8_12 : ok fRt 8 RtT8_12 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk8_13 : ok fRt 8 RtT8_13 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk8_14 : ok fRt 8 RtT8_14 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk8_15 : ok fRt 8 RtT8_15 := by decide +kernel
private theorem Rtk8 : ok fRt 8 RtT8 := by
  simp only [ok,RtT8,nd,BTree.all,Rtk8_0,Rtk8_1,Rtk8_2,Rtk8_3,Rtk8_4,Rtk8_5,Rtk8_6,Rtk8_7,Rtk8_8,Rtk8_9,Rtk8_10,Rtk8_11,Rtk8_12,Rtk8_13,Rtk8_14,Rtk8_15,Bool.and_true]
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk9_0 : ok fRt 9 RtT9_0 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk9_1 : ok fRt 9 RtT9_1 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk9_2 : ok fRt 9 RtT9_2 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk9_3 : ok fRt 9 RtT9_3 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk9_4 : ok fRt 9 RtT9_4 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk9_5 : ok fRt 9 RtT9_5 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk9_6 : ok fRt 9 RtT9_6 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk9_7 : ok fRt 9 RtT9_7 := by decide +kernel
private theorem Rtk9 : ok fRt 9 RtT9 := by
  simp only [ok,RtT9,nd,BTree.all,Rtk9_0,Rtk9_1,Rtk9_2,Rtk9_3,Rtk9_4,Rtk9_5,Rtk9_6,Rtk9_7,Bool.and_true]
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk10_0 : ok fRt 10 RtT10_0 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk10_1 : ok fRt 10 RtT10_1 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk10_2 : ok fRt 10 RtT10_2 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk10_3 : ok fRt 10 RtT10_3 := by decide +kernel
private theorem Rtk10 : ok fRt 10 RtT10 := by
  simp only [ok,RtT10,nd,BTree.all,Rtk10_0,Rtk10_1,Rtk10_2,Rtk10_3,Bool.and_true]
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk11 : ok fRt 11 RtT11 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk12 : ok fRt 12 RtT12 := by decide +kernel
private theorem Rtlv : levelsChecked fRt := by
  intro k hk tree ht; change k ≤ 12 at hk; interval_cases k
  all_goals simp [fRt,RtL] at ht
  · subst ht; exact Rtk5
  · subst ht; exact Rtk6
  · subst ht; exact Rtk7
  · subst ht; exact Rtk8
  · subst ht; exact Rtk9
  · subst ht; exact Rtk10
  · subst ht; exact Rtk11
  · subst ht; exact Rtk12
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowRt : LowerBV (rawOf 63) tRt 13 :=
  lower_forest fRt base13 base13_s Rtv Rtlv (by decide +kernel)
end CertVerify
-- ============================================================
-- 7. Monotone Witness & Main Theorem for L-meta-12152
-- ============================================================

def targetFun (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4276682368 * 2 ^ 32 + 4269834240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def smallCircuit : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [2, 3]⟩,
    ⟨.or, [3, 6]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [9, 12]⟩,
    ⟨.or, [6, 13]⟩, ⟨.and, [10, 13]⟩, ⟨.or, [11, 15]⟩, ⟨.and, [7, 16]⟩,
    ⟨.or, [8, 17]⟩, ⟨.and, [14, 18]⟩], 19⟩

private theorem witnessMonotone : Monotone2 smallCircuit := by
  intro g hg
  simp only [smallCircuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl, by decide⟩ | exact ⟨Or.inr rfl, by decide⟩

set_option maxRecDepth 8192 in set_option maxHeartbeats 0 in
private theorem witnessCorrect : ∀ x : Fin 6 → Bool, smallCircuit.eval (List.ofFn x) = targetFun x := by
  decide +kernel

def sample6 (r : Row) (i : Fin 6) : Bool := bitBV r ((rawOf 63).getD i.val zeroBV)

private theorem raw63_list : List.ofFn (fun i : Fin 6 => (rawOf 63).getD i.val zeroBV) = rawOf 63 := rfl

private theorem sample6_eq (r : Row) :
    List.ofFn (sample6 r) = ((rawOf 63).map observeBV).map (fun f => f r) := by
  rw [← raw63_list, List.map_map, List.map_ofFn]; rfl

set_option maxRecDepth 8192 in set_option maxHeartbeats 0 in
private theorem sample6_target : ∀ r : Row, targetFun (sample6 r) = bitBV r tRt := by
  decide +kernel

private theorem fanInTwo_ops {C : Circuit} (h : FanInTwo C) :
    ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨ho, hl⟩ := h g hg
  refine ⟨?_, hl⟩
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ho

private theorem mainProof (s : ℕ) (h : HasCircuitSize 6 targetFun s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = targetFun x := by
  classical
  obtain ⟨C, hFanIn, hSize, hEval⟩ := h
  by_cases big : 14 ≤ C.size
  · have hsc : smallCircuit.size = 14 := rfl
    exact ⟨smallCircuit, witnessMonotone, by omega, witnessCorrect⟩
  have hfit := fanInTwo_ops hFanIn
  by_cases mono : ∀ g ∈ C.gates, g.op ≠ GateOp.not
  · refine ⟨C, ?_, hSize, hEval⟩
    intro g hg
    obtain ⟨ops, ar⟩ := hfit g hg
    refine ⟨?_, ar⟩
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
  have h13 := lowRt q bank hreach havail
  simp [Circuit.size] at big
  omega

end PEqualNP.Outside.L_meta_12152

open PEqualNP.Outside.L_meta_12152 in
theorem PEqualNP.Outside.L_meta_12152 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276682368 * 2 ^ 32 + 4269834240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276682368 * 2 ^ 32 + 4269834240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  mainProof
