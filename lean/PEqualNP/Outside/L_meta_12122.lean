import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12122
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
def tF2 : Sig := 0xa880a880a880a880#64
def F2P : List Row := mkRows [7,7,7,7,11,11,11,11,13,13,13,13]
def F2N : List Row := mkRows [3,5,9,14,3,5,9,14,3,5,9,14]
def F2R : List (Nat × Nat) := [(4095,1911),(255,2457),(3855,2730),(4080,3276)]
def F2A : List (List Nat) := [[0,1,2,3,4,5],[0,1,3,2,4,5],[0,2,1,3,4,5],[0,2,3,1,4,5],[0,3,1,2,4,5],[0,3,2,1,4,5]]
def F2C : List CutSpec := [⟨0,1,4,1,0,[3,0,1,2,4,5],0xaaaaaaaaaaaaaaaa#64⟩]
def F2T4 : BTree NodeData := lf 0xf0 [0x1]
def F2L : Nat → Option (BTree NodeData) | 4 => some F2T4 | _ => none
def F2M : Nat → BST | _ => BE
def tF3 : Sig := 0xe888e888e888e888#64
def F3P : List Row := mkRows [3,3,3,3,3,13,13,13,13,13,14,14,14,14,14]
def F3N : List Row := mkRows [5,6,9,10,12,5,6,9,10,12,5,6,9,10,12]
def F3R : List (Nat × Nat) := [(1023,5285),(31775,10570),(32736,20083),(32736,29596)]
def F3A : List (List Nat) := [[0,1,2,3,4,5],[0,1,3,2,4,5],[1,0,2,3,4,5],[1,0,3,2,4,5]]
def F3C : List CutSpec := [⟨0,4,4,1,0,[0,1,3,2,4,5],0xf0f0f0f0f0f0f0f0#64⟩]
def F3T4 : BTree NodeData := lf 0xf0 [0x1]
def F3L : Nat → Option (BTree NodeData) | 4 => some F3T4 | _ => none
def F3M : Nat → BST | _ => BE
def tF4 : Sig := 0xe8a8e8a8e8a8e8a8#64
def F4P : List Row := mkRows [3,3,3,3,5,5,5,5,14,14,14,14]
def F4N : List Row := mkRows [6,9,10,12,6,9,10,12,6,9,10,12]
def F4R : List (Nat × Nat) := [(255,546),(3855,1365),(4080,2457),(3840,3822)]
def F4A : List (List Nat) := [[0,1,2,3,4,5],[0,2,1,3,4,5]]
def F4C : List CutSpec := [⟨0,8,4,1,0,[0,1,2,3,4,5],0xff00ff00ff00ff00#64⟩]
def F4T4 : BTree NodeData := lf 0xf0 [0x1]
def F4L : Nat → Option (BTree NodeData) | 4 => some F4T4 | _ => none
def F4M : Nat → BST | _ => BE
def tF5 : Sig := 0xeee8eee8eee8eee8#64
def F5P : List Row := mkRows [3,3,3,5,5,5,6,6,6,9,9,9,10,10,10]
def F5N : List Row := mkRows [1,2,12,1,2,12,1,2,12,1,2,12,1,2,12]
def F5R : List (Nat × Nat) := [(3647,4681),(29127,9362),(504,18724),(32256,18724)]
def F5A : List (List Nat) := [[0,1,2,3,4,5],[0,1,3,2,4,5],[1,0,2,3,4,5],[1,0,3,2,4,5]]
def F5C : List CutSpec := [⟨4,0,4,1,0,[0,1,3,2,4,5],0xf0f0f0f0f0f0f0f#64⟩]
def F5T4 : BTree NodeData := lf 0xf0 [0x1]
def F5L : Nat → Option (BTree NodeData) | 4 => some F5T4 | _ => none
def F5M : Nat → BST | _ => BE
def tF6 : Sig := 0xfeeafeeafeeafeea#64
def F6P : List Row := mkRows [1,1,1,6,6,6,10,10,10,12,12,12]
def F6N : List Row := mkRows [2,4,8,2,4,8,2,4,8,2,4,8]
def F6R : List (Nat × Nat) := [(7,0),(504,585),(3640,1170),(4032,2340)]
def F6A : List (List Nat) := [[0,1,2,3,4,5],[0,1,3,2,4,5],[0,2,1,3,4,5],[0,2,3,1,4,5],[0,3,1,2,4,5],[0,3,2,1,4,5]]
def F6C : List CutSpec := [⟨1,0,4,1,0,[3,0,1,2,4,5],0x5555555555555555#64⟩]
def F6T4 : BTree NodeData := lf 0xf0 [0x1]
def F6L : Nat → Option (BTree NodeData) | 4 => some F6T4 | _ => none
def F6M : Nat → BST | _ => BE
def tF7 : Sig := 0xeaa8eaa8eaa8eaa8#64
def F7P : List Row := mkRows [3,3,3,3,5,5,5,5,9,9,9,9,14,14,14,14]
def F7N : List Row := mkRows [1,6,10,12,1,6,10,12,1,6,10,12,1,6,10,12]
def F7R : List (Nat × Nat) := [(4095,4369),(61455,26214),(61680,43690),(65280,52428)]
def F7A : List (List Nat) := [[0,1,2,3,4,5],[0,1,3,2,4,5],[0,2,1,3,4,5],[0,2,3,1,4,5],[0,3,1,2,4,5],[0,3,2,1,4,5]]
def F7C : List CutSpec := [⟨2,0,2,0,0,[0,1,2,3,4,5],0x3333333333333333#64⟩,⟨0,2,2,0,0,[0,1,2,3,4,5],0xcccccccccccccccc#64⟩,⟨0,4,2,0,0,[0,1,2,3,4,5],0xf0f0f0f0f0f0f0f0#64⟩,⟨4,0,2,0,0,[0,1,2,3,4,5],0xf0f0f0f0f0f0f0f#64⟩,⟨0,8,2,0,0,[0,1,2,3,4,5],0xff00ff00ff00ff00#64⟩,⟨8,0,2,0,0,[0,1,2,3,4,5],0xff00ff00ff00ff#64⟩,⟨0,6,1,0,0,[0,1,2,3,4,5],0xc0c0c0c0c0c0c0c0#64⟩,⟨0,10,1,0,0,[0,1,2,3,4,5],0xcc00cc00cc00cc00#64⟩,⟨6,0,1,0,0,[0,1,2,3,4,5],0x303030303030303#64⟩,⟨10,0,1,0,0,[0,1,2,3,4,5],0x33003300330033#64⟩]
def F7T2 : BTree NodeData := lf 0x3544842100493 []
def F7T3 : BTree NodeData := nd (nd (nd (lf 0x90810002a2 []) (nd (lf 0x50810002b2 [0x1]) (lf 0x90810002b2 []))) (nd (lf 0xd0910002a2 []) (nd (lf 0x10910002b2 [0x2]) (lf 0xd0910002b2 [])))) (nd (nd (lf 0xc4210003c2 []) (nd (lf 0x4842100392 [0x20001]) (lf 0x50221002e2 [0x2]))) (nd (nd (lf 0x90221002e2 [0x1]) (lf 0xc862100392 [])) (nd (lf 0x50e2100272 [0x1]) (lf 0x90e2100272 [0x3]))))
def F7M3 : BST := BL 137829317 0
def F7T4 : BTree NodeData := nd (nd (nd (lf 0x10001e1 [0x400030001,0x60005]) (lf 0x10001f1 [0x20001])) (nd (lf 0x110001e1 [0x300040002,0x50006]) (nd (lf 0x110001f1 [0x10002]) (lf 0x210001e1 [0x80007])))) (nd (nd (lf 0x210001f1 [0x10002]) (nd (lf 0x310001e1 [0xa0009]) (lf 0x310001f1 [0x20001]))) (nd (lf 0x21001f1 [0x10007]) (nd (lf 0x121001f1 [0x20009]) (lf 0x221001f1 [0x30001]))))
def F7M4 : BST := BN 223209938 896 (BN 196174516 384 (BN 186858240 1664 (BN 177753524 769 (BL 103077589 1408) BE) (BL 191772605 256)) (BN 208836991 640 (BN 205976568 1 (BL 200214949 1792) BE) (BL 214418912 1537))) (BN 244030727 768 (BN 234933659 128 (BN 234382945 512 (BL 233061833 0) BE) (BL 241504177 1536)) (BN 284262306 513 (BN 271055739 1793 (BL 262613395 257) BE) (BL 285806013 1920)))
def F7T5 : BTree NodeData := lf 0xf0 []
def F7M5 : BST := BN 253542168 897 (BN 222203707 1796 (BN 187951761 768 (BN 179509417 256 (BN 176322816 385 (BL 175294740 1923) BE) (BL 181699594 1920)) (BN 212638182 387 (BN 206028427 2 (BL 200504755 1924) BE) (BL 214470771 514))) (BN 245950249 1794 (BN 241225197 899 (BN 239607500 1792 (BL 230646051 132) BE) (BL 243812071 1921)) (BN 248199857 1925 (BL 248049844 128) (BL 253421069 260)))) (BN 277148485 644 (BN 264724887 384 (BN 261863413 772 (BN 256670179 1922 (BL 254392593 130) BE) (BL 264012256 640)) (BN 272454600 1664 (BL 269955940 258) (BL 276118972 642))) (BN 285590829 1668 (BN 279404288 896 (BN 278627151 4 (BL 278398284 770) BE) (BL 284561316 1666)) (BN 298359982 0 (BL 287069495 516) (BL 306802326 512))))
def F7L : Nat → Option (BTree NodeData) | 2 => some F7T2 | 3 => some F7T3 | 4 => some F7T4 | 5 => some F7T5 | _ => none
def F7M : Nat → BST | 3 => F7M3 | 4 => F7M4 | 5 => F7M5 | _ => BE
def tF8 : Sig := 0xe880e880e880e880#64
def F8P : List Row := mkRows [7,7,7,7,7,7,11,11,11,11,11,11,13,13,13,13,13,13,14,14,14,14,14,14]
def F8N : List Row := mkRows [3,5,6,9,10,12,3,5,6,9,10,12,3,5,6,9,10,12,3,5,6,9,10,12]
def F8R : List (Nat × Nat) := [(262143,2929355),(16519167,5592405),(16773183,10119590),(16777152,14913080)]
def F8A : List (List Nat) := [[0,1,2,3,4,5],[0,1,3,2,4,5],[0,2,1,3,4,5],[0,2,3,1,4,5],[0,3,1,2,4,5],[0,3,2,1,4,5],[1,0,2,3,4,5],[1,0,3,2,4,5],[1,2,0,3,4,5],[1,2,3,0,4,5],[1,3,0,2,4,5],[1,3,2,0,4,5],[2,0,1,3,4,5],[2,0,3,1,4,5],[2,1,0,3,4,5],[2,1,3,0,4,5],[2,3,0,1,4,5],[2,3,1,0,4,5],[3,0,1,2,4,5],[3,0,2,1,4,5],[3,1,0,2,4,5],[3,1,2,0,4,5],[3,2,0,1,4,5],[3,2,1,0,4,5]]
def F8C : List CutSpec := [⟨0,2,4,1,0,[0,3,1,2,4,5],0xcccccccccccccccc#64⟩,⟨0,4,4,1,0,[0,1,3,2,4,5],0xf0f0f0f0f0f0f0f0#64⟩,⟨0,8,4,1,0,[0,1,2,3,4,5],0xff00ff00ff00ff00#64⟩,⟨0,1,4,1,0,[3,0,1,2,4,5],0xaaaaaaaaaaaaaaaa#64⟩]
def F8T3 : BTree NodeData := nd (lf 0x210801000783 [0x20001]) (lf 0x2531081000473 [])
def F8T4 : BTree NodeData := nd (lf 0x8010003e2 [0x20001]) (nd (lf 0x10810002f2 [0x3]) (lf 0x90810002f2 []))
def F8M4 : BST := BN 268178193 0 (BL 197086774 128) BE
def F8T5 : BTree NodeData := lf 0x10001f1 [0x200040001,0x3]
def F8M5 : BST := BN 294398772 6 (BN 245994181 129 (BN 218854910 385 (BL 205996701 7) BE) (BL 285649811 128)) (BN 338745490 0 (BL 299667920 384) (BL 411344214 1))
def F8T6 : BTree NodeData := lf 0xf0 [0x200040001,0x3]
def F8M6 : BST := BN 264724887 8 (BN 212638182 16 (BL 176322816 10) (BL 214470771 2)) (BN 306802326 0 (BL 287069495 4) BE)
def F8L : Nat → Option (BTree NodeData) | 3 => some F8T3 | 4 => some F8T4 | 5 => some F8T5 | 6 => some F8T6 | _ => none
def F8M : Nat → BST | 4 => F8M4 | 5 => F8M5 | 6 => F8M6 | _ => BE
def tF9 : Sig := 0xfee8fee8fee8fee8#64
def F9P : List Row := mkRows [3,3,3,3,5,5,5,5,6,6,6,6,9,9,9,9,10,10,10,10,12,12,12,12]
def F9N : List Row := mkRows [1,2,4,8,1,2,4,8,1,2,4,8,1,2,4,8,1,2,4,8,1,2,4,8]
def F9R : List (Nat × Nat) := [(61695,1118481),(986895,2236962),(15732720,4473924),(16773120,8947848)]
def F9A : List (List Nat) := [[0,1,2,3,4,5],[0,1,3,2,4,5],[0,2,1,3,4,5],[0,2,3,1,4,5],[0,3,1,2,4,5],[0,3,2,1,4,5],[1,0,2,3,4,5],[1,0,3,2,4,5],[1,2,0,3,4,5],[1,2,3,0,4,5],[1,3,0,2,4,5],[1,3,2,0,4,5],[2,0,1,3,4,5],[2,0,3,1,4,5],[2,1,0,3,4,5],[2,1,3,0,4,5],[2,3,0,1,4,5],[2,3,1,0,4,5],[3,0,1,2,4,5],[3,0,2,1,4,5],[3,1,0,2,4,5],[3,1,2,0,4,5],[3,2,0,1,4,5],[3,2,1,0,4,5]]
def F9C : List CutSpec := [⟨4,0,4,1,0,[0,1,3,2,4,5],0xf0f0f0f0f0f0f0f#64⟩,⟨1,0,4,1,0,[3,0,1,2,4,5],0x5555555555555555#64⟩,⟨2,0,4,1,0,[0,3,1,2,4,5],0x3333333333333333#64⟩,⟨8,0,4,1,0,[0,1,2,3,4,5],0xff00ff00ff00ff#64⟩]
def F9T3 : BTree NodeData := nd (lf 0x1214811000783 [0x20001]) (lf 0x3535091000473 [])
def F9T4 : BTree NodeData := nd (lf 0x48110003e2 [0x10003]) (nd (lf 0x50910002f2 [0x4]) (lf 0xd0910002f2 []))
def F9M4 : BST := BN 292369923 128 (BL 227934542 0) BE
def F9T5 : BTree NodeData := lf 0x110001f1 [0x100030002,0x4]
def F9M5 : BST := BN 267287567 1 (BN 258378692 384 (BN 190227608 6 (BL 164365488 7) BE) (BL 263734569 129)) (BN 283822438 0 (BL 275491737 385) (BL 295564700 128))
def F9T6 : BTree NodeData := lf 0xf0 [0x100030002,0x4]
def F9M6 : BST := BN 261863413 4 (BN 241225197 16 (BL 187951761 0) (BL 253542168 10)) (BN 279404288 8 (BL 278398284 2) BE)
def F9L : Nat → Option (BTree NodeData) | 3 => some F9T3 | 4 => some F9T4 | 5 => some F9T5 | 6 => some F9T6 | _ => none
def F9M : Nat → BST | 4 => F9M4 | 5 => F9M5 | 6 => F9M6 | _ => BE
def tF10 : Sig := 0xa8888880a8888880#64
def F10P : List Row := mkRows [7,7,7,7,7,11,11,11,11,11,19,19,19,19,19,29,29,29,29,29]
def F10N : List Row := mkRows [3,13,21,25,30,3,13,21,25,30,3,13,21,25,30,3,13,21,25,30]
def F10R : List (Nat × Nat) := [(1048575,507375),(32767,575025),(1015839,744150),(1016800,879450),(1047552,947100)]
def F10A : List (List Nat) := [[0,1,2,3,4,5],[0,1,2,4,3,5],[0,1,3,2,4,5],[0,1,3,4,2,5],[0,1,4,2,3,5],[0,1,4,3,2,5]]
def F10C : List CutSpec := [⟨0,1,6,7,0,[4,0,1,2,3,5],0xaaaaaaaaaaaaaaaa#64⟩]
def F10T6 : BTree NodeData := lf 0x1f0 [0x1]
def F10L : Nat → Option (BTree NodeData) | 6 => some F10T6 | _ => none
def F10M : Nat → BST | _ => BE
def tF11 : Sig := 0xa8808000a8808000#64
def F11P : List Row := mkRows [15,15,15,15,15,15,15,23,23,23,23,23,23,23,27,27,27,27,27,27,27,29,29,29,29,29,29,29]
def F11N : List Row := mkRows [7,11,13,19,21,25,30,7,11,13,19,21,25,30,7,11,13,19,21,25,30,7,11,13,19,21,25,30]
def F11R : List (Nat × Nat) := [(268435455,133160895),(2097151,158524875),(266354687,179661525),(268419199,215593830),(268435328,253639800)]
def F11A : List (List Nat) := [[0,1,2,3,4,5],[0,1,2,4,3,5],[0,1,3,2,4,5],[0,1,3,4,2,5],[0,1,4,2,3,5],[0,1,4,3,2,5],[0,2,1,3,4,5],[0,2,1,4,3,5],[0,2,3,1,4,5],[0,2,3,4,1,5],[0,2,4,1,3,5],[0,2,4,3,1,5],[0,3,1,2,4,5],[0,3,1,4,2,5],[0,3,2,1,4,5],[0,3,2,4,1,5],[0,3,4,1,2,5],[0,3,4,2,1,5],[0,4,1,2,3,5],[0,4,1,3,2,5],[0,4,2,1,3,5],[0,4,2,3,1,5],[0,4,3,1,2,5],[0,4,3,2,1,5]]
def F11C : List CutSpec := [⟨0,1,7,8,0,[4,0,1,2,3,5],0xaaaaaaaaaaaaaaaa#64⟩]
def F11T7 : BTree NodeData := lf 0x1f0 [0x1]
def F11L : Nat → Option (BTree NodeData) | 7 => some F11T7 | _ => none
def F11M : Nat → BST | _ => BE
def tF12 : Sig := 0xe8808880e8808880#64
def F12P : List Row := mkRows [7,7,7,7,7,7,7,7,11,11,11,11,11,11,11,11,29,29,29,29,29,29,29,29,30,30,30,30,30,30,30,30]
def F12N : List Row := mkRows [13,14,19,21,22,25,26,28,13,14,19,21,22,25,26,28,13,14,19,21,22,25,26,28,13,14,19,21,22,25,26,28]
def F12R : List (Nat × Nat) := [(16777215,757935405),(4278255615,1448498774),(4294902015,2610666395),(4294967040,3823363043),(4294901760,4244438268)]
def F12A : List (List Nat) := [[0,1,2,3,4,5],[0,1,3,2,4,5],[1,0,2,3,4,5],[1,0,3,2,4,5]]
def F12C : List CutSpec := [⟨0,16,7,8,0,[0,1,2,3,4,5],0xffff0000ffff0000#64⟩]
def F12T7 : BTree NodeData := lf 0x1f0 [0x1]
def F12L : Nat → Option (BTree NodeData) | 7 => some F12T7 | _ => none
def F12M : Nat → BST | _ => BE
def tF13 : Sig := 0xeee8e8a0eee8e8a0#64
def F13P : List Row := mkRows [5,5,5,5,5,5,5,11,11,11,11,11,11,11,14,14,14,14,14,14,14,19,19,19,19,19,19,19,22,22,22,22,22,22,22,25,25,25,25,25,25,25,26,26,26,26,26,26,26]
def F13N : List Row := mkRows [3,6,9,10,17,18,28,3,6,9,10,17,18,28,3,6,9,10,17,18,28,3,6,9,10,17,18,28,3,6,9,10,17,18,28,3,6,9,10,17,18,28,3,6,9,10,17,18,28]
def F13R : List (Nat × Nat) := [(4363953127423,93086212770453),(558586266648448,190605102339499),(34093383807,292556668707138),(562915595779968,336883436693068),(562949951324160,496459801442416)]
def F13A : List (List Nat) := [[0,1,2,3,4,5],[0,1,2,4,3,5]]
def F13C : List CutSpec := [⟨0,2,7,9,0,[0,4,1,2,3,5],0xcccccccccccccccc#64⟩]
def F13T7 : BTree NodeData := lf 0x1f0 [0x1]
def F13L : Nat → Option (BTree NodeData) | 7 => some F13T7 | _ => none
def F13M : Nat → BST | _ => BE
def tF14 : Sig := 0xeeeaeaa0eeeaeaa0#64
def F14P : List Row := mkRows [5,5,5,5,5,9,9,9,9,9,14,14,14,14,14,17,17,17,17,17,22,22,22,22,22,26,26,26,26,26]
def F14N : List Row := mkRows [3,6,10,18,28,3,6,10,18,28,3,6,10,18,28,3,6,10,18,28,3,6,10,18,28,3,6,10,18,28]
def F14R : List (Nat × Nat) := [(1016831,34636833),(1072724992,519552495),(32537631,623462994),(1040220128,692736660),(1073709056,831283992)]
def F14A : List (List Nat) := [[0,1,2,3,4,5],[0,1,2,4,3,5],[0,1,3,2,4,5],[0,1,3,4,2,5],[0,1,4,2,3,5],[0,1,4,3,2,5]]
def F14C : List CutSpec := [⟨0,2,7,9,0,[0,4,1,2,3,5],0xcccccccccccccccc#64⟩]
def F14T7 : BTree NodeData := lf 0x1f0 [0x1]
def F14L : Nat → Option (BTree NodeData) | 7 => some F14T7 | _ => none
def F14M : Nat → BST | _ => BE
def tF15 : Sig := 0xfee8eaa8fee8eaa8#64
def F15P : List Row := mkRows [3,3,3,3,3,3,3,5,5,5,5,5,5,5,9,9,9,9,9,9,9,14,14,14,14,14,14,14,22,22,22,22,22,22,22,26,26,26,26,26,26,26,28,28,28,28,28,28,28]
def F15N : List Row := mkRows [6,10,12,17,18,20,24,6,10,12,17,18,20,24,6,10,12,17,18,20,24,6,10,12,17,18,20,24,6,10,12,17,18,20,24,6,10,12,17,18,20,24,6,10,12,17,18,20,24]
def F15R : List (Nat × Nat) := [(2097151,35461414388744),(4398044414079,84220859173267),(558586264567680,164009041547941),(562915862102016,310287375901510),(562949684985856,531921215831160)]
def F15A : List (List Nat) := [[0,1,2,3,4,5],[0,1,3,2,4,5],[0,2,1,3,4,5],[0,2,3,1,4,5],[0,3,1,2,4,5],[0,3,2,1,4,5]]
def F15C : List CutSpec := [⟨28,0,1,0,0,[0,1,2,3,4,5],0xf0000000f#64⟩,⟨0,1,2,0,0,[0,1,2,3,4,5],0xaaaaaaaaaaaaaaaa#64⟩,⟨16,0,6,7,0,[0,1,2,3,4,5],0xffff0000ffff#64⟩,⟨2,4,2,0,0,[0,1,2,3,4,5],0x3030303030303030#64⟩,⟨8,1,1,0,0,[0,1,2,3,4,5],0xaa00aa00aa00aa#64⟩,⟨0,2,5,6,0,[0,4,1,2,3,5],0xcccccccccccccccc#64⟩,⟨8,0,5,4,0,[0,1,2,4,3,5],0xff00ff00ff00ff#64⟩,⟨1,0,7,8,0,[4,0,1,2,3,5],0x5555555555555555#64⟩,⟨0,16,7,9,0,[0,1,2,3,4,5],0xffff0000ffff0000#64⟩,⟨4,10,1,0,0,[0,1,2,3,4,5],0xc000c000c000c00#64⟩,⟨16,10,1,0,0,[0,1,2,3,4,5],0xcc000000cc00#64⟩,⟨0,8,5,6,0,[0,1,2,4,3,5],0xff00ff00ff00ff00#64⟩,⟨16,6,1,0,0,[0,1,2,3,4,5],0xc0c00000c0c0#64⟩,⟨2,0,5,4,0,[0,4,1,2,3,5],0x3333333333333333#64⟩,⟨4,0,5,4,0,[0,1,4,2,3,5],0xf0f0f0f0f0f0f0f#64⟩,⟨0,4,5,6,0,[0,1,4,2,3,5],0xf0f0f0f0f0f0f0f0#64⟩,⟨1,2,4,1,0,[3,4,0,1,2,5],0x4444444444444444#64⟩,⟨8,6,1,0,0,[0,1,2,3,4,5],0xc000c000c000c0#64⟩,⟨1,4,4,1,0,[3,0,4,1,2,5],0x5050505050505050#64⟩]
def F15T2 : BTree NodeData := nd (lf2 0x1cf654842104116 0xe6173 [0x20001]) (lf2 0x9cf654842106106 0xdcd80 [0x21f03])
def F15T3 : BTree NodeData := nd (nd (lf2 0x1cf654842103115 0x173 [0x40001]) (lf2 0x9cf654842102985 0x180 [])) (nd (lf2 0x9cf654842103115 0x373 [0x50001]) (lf2 0xdcf654842102985 0x180 [0x5]))
def F15M3 : BST := BN 251158856 128 (BL 151654995 0) BE
def F15T4 : BTree NodeData := nd (nd (nd (lf 0x1d5320c91001524 [0xe0809070606,0xf09]) (lf 0xdd9320c91001324 [0xf09000a])) (nd (lf 0xdd9210874001284 [0xb00010e03]) (lf 0x5c3654842101984 [0x50f090004,0x70c]))) (nd (nd (lf 0x1cf654842101994 [0x1000a]) (lf 0x5cf654842101994 [0xb])) (nd (lf 0x9cf654842101994 [0x70800040001]) (lf 0xdcf654842101994 [0x708000d070c,0x7030709])))
def F15M4 : BST := BN 280037759 128 (BN 264396775 384 (BL 220521110 0) BE) (BL 302901357 256)
def F15T5 : BTree NodeData := nd (nd (nd (nd (lf 0x1320c91000f23 [0x107010c0606,0x20e0709]) (lf 0x2650c910009e3 [0x1070709010f,0x608])) (nd (lf 0x654c910009e3 [0x50707090206,0x608050f]) (lf 0x3328c91000f23 [0x107010f0709,0x608]))) (nd (nd (lf 0x2658c910009e3 [0x50707090206,0xc]) (lf 0x1320cb1000f03 [0x107010c0709,0x20e])) (nd (lf 0x3654cb10009c3 [0x50f05070709,0x50c0510]) (nd (lf 0x6354b1000b43 [0x1100709040e]) (lf 0x36354b1000b43 [0x110010c0709]))))) (nd (nd (nd (lf 0x634871000b43 [0x50f0709040e]) (lf 0x3634871000b43 [0x10c01100709])) (nd (lf 0x1320cb1000f23 [0x1070709010c,0x608020e]) (nd (lf 0x1210874000e83 [0x106010f0603]) (lf 0x3218874000e83 [0x10f01100603])))) (nd (nd (lf 0x3604842100b83 [0x709040f0011,0x107]) (lf 0x634842100b13 [0x107040f0708,0x709])) (nd (lf 0x3654842100993 [0x7090708]) (nd (lf 0x160cc42100bc3 [0x110107060f,0x709]) (lf 0x160d4d2100963 [0x41004060709])))))
def F15M5 : BST := BN 294021991 516 (BN 245282818 256 (BN 218899576 128 (BL 213638945 768) BE) (BL 292330657 896)) (BN 331780260 384 (BN 312183727 512 (BL 309505629 0) BE) (BL 345694692 640))
def F15T6 : BTree NodeData := nd (nd (nd (nd (lf 0xc910007e2 [0x107010f0206,0x10000e0309,0xc]) (nd (lf 0x4c910007e2 [0x3090206010c,0x107000e010f,0x10]) (lf 0x8c910007e2 [0x309010c0206,0x7010f]))) (nd (lf 0xcb10007c2 [0x10f03090107,0x11020e]) (nd (lf 0x4cb10007c2 [0x10c03090110,0x11000e]) (lf 0x8cb10007c2 [0x10f0309010c,0x11020e])))) (nd (nd (lf 0x54b10007c2 [0x309000e0110,0x10c0107]) (nd (lf 0x94b10007c2 [0x309010f0011,0x10c0107000e]) (lf 0x48710007c2 [0x309000e0110,0x10c0107]))) (nd (lf 0xc8710007c2 [0x309000e010f,0x10c01070207]) (nd (lf 0xcb10007e2 [0x309010f020e,0x110107]) (lf 0x4cb10007e2 [0x309020e0110,0x1030011010c]))))) (nd (nd (nd (lf 0x8cb10007e2 [0x309010c020e,0x11010f]) (nd (lf 0x8740006e2 [0x203010e010f,0x10c0107]) (lf 0x48740006e2 [0x11002030106,0x10c0107]))) (nd (lf 0x88740006e2 [0x1100203010e,0x10c0107]) (nd (lf 0x54021005e2 [0x10803090012,0xf000c0007,0xe]) (lf 0x4842100792 [0xf00060308,0x1070309])))) (nd (nd (lf 0xcc421007d2 [0x309020f0107,0x308]) (nd (lf 0xd4121005e2 [0x30900100011,0xc00070008]) (lf 0x14d2100572 [0x1000060308,0x3090007]))) (nd (lf 0xd4d2100572 [0xc03090308,0x100006]) (nd (lf 0x54221005e2 [0xe03090013,0xc00070108]) (lf 0xc862100792 [0x1003090308,0xf])))))
def F15M6 : BST := BN 299459397 0 (BN 250585063 1152 (BN 214686185 896 (BN 191094818 1408 (BL 189714074 768) (BL 210531090 3712)) (BN 248545930 128 (BL 244104284 1923) BE)) (BN 280919058 1280 (BN 269090615 1536 (BL 259270263 1540) (BL 273461690 384)) (BN 294937834 3840 (BL 290051428 1920) BE))) (BN 340436479 3968 (BN 309226930 1024 (BN 305532081 130 (BL 303398916 1792) (BL 307571214 1154)) (BN 333552451 512 (BL 316290492 1664) BE)) (BN 383962236 640 (BN 365029665 4 (BL 352153597 256) BE) (BN 388757081 644 (BL 384321083 1284) BE)))
def F15T7 : BTree NodeData := nd (nd (lf 0x110003e1 [0xf01090006,0xc00070010]) (nd (lf 0x310003c1 [0xe0109]) (lf 0x310003e1 [0xf0109000e,0xc00070010]))) (nd (nd (lf 0x340002e1 [0x3]) (lf 0x21003f1 [0xf0108000e,0xc00070109])) (nd (lf 0x121003f1 [0x10901080006,0xc00070010,0x3]) (lf 0x221003f1 [0xe01080010,0xc00070109])))
def F15M7 : BST := BN 337892268 3076 (BN 289153095 640 (BN 263715108 1920 (BN 257575762 3072 (BN 238945638 387 (BL 179934457 3968) (BL 239035423 3584)) (BN 263701248 896 (BL 261662115 3456) BE)) (BN 282748241 643 (BN 264958069 384 (BL 264245438 769) (BL 276378865 512)) (BN 285693859 3712 (BL 283776317 1153) BE))) (BN 317282851 3329 (BN 304965880 1536 (BN 295829714 256 (BL 294919204 0) (BL 302426428 770)) (BN 311940540 3585 (BL 307958256 644) BE)) (BN 323506219 1024 (BN 320410862 768 (BL 320091683 1155) BE) (BN 330480879 3073 (BL 327432018 257) BE)))) (BN 364746221 1281 (BN 355268212 1280 (BN 347452708 1664 (BN 343144971 3328 (BL 342078601 128) (BL 344028987 1408)) (BN 351265572 641 (BL 348678698 3203) BE)) (BN 360995669 3201 (BN 357183686 3588 (BL 355653358 645) (BL 357532606 386)) (BN 364123680 642 (BL 361619684 132) BE))) (BN 420917561 4 (BN 400131122 3330 (BN 379422043 1792 (BL 372178388 1152) (BL 386857789 3200)) (BN 414983718 129 (BL 408009058 3840) BE)) (BN 444644977 1796 (BN 440208979 516 (BL 435596962 1028) BE) (BN 459324378 3844 (BL 454888380 1540) BE))))
def F15T8 : BTree NodeData := lf 0x1f0 [0x90008]
def F15M8 : BST := BN 325056725 901 (BN 277361623 900 (BN 253179684 641 (BN 252151608 899 (BL 237825946 256) BE) (BN 258556462 896 (BL 256366285 0) BE)) (BN 294812097 258 (BN 289495050 643 (BL 281538764 128) BE) (BN 320668939 897 (BL 318082065 387) BE))) (BN 346812808 2 (BN 333527047 898 (BN 330399036 385 (BL 330277937 4) BE) (BN 341581755 640 (BL 340869124 768) BE)) (BN 354005353 772 (BN 352975840 770 (BL 349569355 260) BE) (BL 356261156 384)))
def F15L : Nat → Option (BTree NodeData) | 2 => some F15T2 | 3 => some F15T3 | 4 => some F15T4 | 5 => some F15T5 | 6 => some F15T6 | 7 => some F15T7 | 8 => some F15T8 | _ => none
def F15M : Nat → BST | 3 => F15M3 | 4 => F15M4 | 5 => F15M5 | 6 => F15M6 | 7 => F15M7 | 8 => F15M8 | _ => BE
def tF16 : Sig := 0xe8808000e8808000#64
def F16P : List Row := mkRows [15,15,15,15,15,15,15,15,15,15,23,23,23,23,23,23,23,23,23,23,27,27,27,27,27,27,27,27,27,27,29,29,29,29,29,29,29,29,29,29,30,30,30,30,30,30,30,30,30,30]
def F16N : List Row := mkRows [7,11,13,14,19,21,22,25,26,28,7,11,13,14,19,21,22,25,26,28,7,11,13,14,19,21,22,25,26,28,7,11,13,14,19,21,22,25,26,28,7,11,13,14,19,21,22,25,26,28]
def F16R : List (Nat × Nat) := [(1099511627775,201407314713783),(1124801468956671,381903487462747),(1125898834149375,683464166323821),(1125899905795071,1001533641472910),(1125899906841600,1109391110554608)]
def F16A : List (List Nat) := [[0,1,2,3,4,5],[0,1,2,4,3,5],[0,1,3,2,4,5],[0,1,3,4,2,5],[0,1,4,2,3,5],[0,1,4,3,2,5],[0,2,1,3,4,5],[0,2,1,4,3,5],[0,2,3,1,4,5],[0,2,3,4,1,5],[0,2,4,1,3,5],[0,2,4,3,1,5],[0,3,1,2,4,5],[0,3,1,4,2,5],[0,3,2,1,4,5],[0,3,2,4,1,5],[0,3,4,1,2,5],[0,3,4,2,1,5],[0,4,1,2,3,5],[0,4,1,3,2,5],[0,4,2,1,3,5],[0,4,2,3,1,5],[0,4,3,1,2,5],[0,4,3,2,1,5],[1,0,2,3,4,5],[1,0,2,4,3,5],[1,0,3,2,4,5],[1,0,3,4,2,5],[1,0,4,2,3,5],[1,0,4,3,2,5],[1,2,0,3,4,5],[1,2,0,4,3,5],[1,2,3,0,4,5],[1,2,3,4,0,5],[1,2,4,0,3,5],[1,2,4,3,0,5],[1,3,0,2,4,5],[1,3,0,4,2,5],[1,3,2,0,4,5],[1,3,2,4,0,5],[1,3,4,0,2,5],[1,3,4,2,0,5],[1,4,0,2,3,5],[1,4,0,3,2,5],[1,4,2,0,3,5],[1,4,2,3,0,5],[1,4,3,0,2,5],[1,4,3,2,0,5],[2,0,1,3,4,5],[2,0,1,4,3,5],[2,0,3,1,4,5],[2,0,3,4,1,5],[2,0,4,1,3,5],[2,0,4,3,1,5],[2,1,0,3,4,5],[2,1,0,4,3,5],[2,1,3,0,4,5],[2,1,3,4,0,5],[2,1,4,0,3,5],[2,1,4,3,0,5],[2,3,0,1,4,5],[2,3,0,4,1,5],[2,3,1,0,4,5],[2,3,1,4,0,5],[2,3,4,0,1,5],[2,3,4,1,0,5],[2,4,0,1,3,5],[2,4,0,3,1,5],[2,4,1,0,3,5],[2,4,1,3,0,5],[2,4,3,0,1,5],[2,4,3,1,0,5],[3,0,1,2,4,5],[3,0,1,4,2,5],[3,0,2,1,4,5],[3,0,2,4,1,5],[3,0,4,1,2,5],[3,0,4,2,1,5],[3,1,0,2,4,5],[3,1,0,4,2,5],[3,1,2,0,4,5],[3,1,2,4,0,5],[3,1,4,0,2,5],[3,1,4,2,0,5],[3,2,0,1,4,5],[3,2,0,4,1,5],[3,2,1,0,4,5],[3,2,1,4,0,5],[3,2,4,0,1,5],[3,2,4,1,0,5],[3,4,0,1,2,5],[3,4,0,2,1,5],[3,4,1,0,2,5],[3,4,1,2,0,5],[3,4,2,0,1,5],[3,4,2,1,0,5],[4,0,1,2,3,5],[4,0,1,3,2,5],[4,0,2,1,3,5],[4,0,2,3,1,5],[4,0,3,1,2,5],[4,0,3,2,1,5],[4,1,0,2,3,5],[4,1,0,3,2,5],[4,1,2,0,3,5],[4,1,2,3,0,5],[4,1,3,0,2,5],[4,1,3,2,0,5],[4,2,0,1,3,5],[4,2,0,3,1,5],[4,2,1,0,3,5],[4,2,1,3,0,5],[4,2,3,0,1,5],[4,2,3,1,0,5],[4,3,0,1,2,5],[4,3,0,2,1,5],[4,3,1,0,2,5],[4,3,1,2,0,5],[4,3,2,0,1,5],[4,3,2,1,0,5]]
def F16C : List CutSpec := [⟨0,10,4,1,0,[0,3,1,4,2,5],0xcc00cc00cc00cc00#64⟩,⟨0,4,7,8,0,[0,1,4,2,3,5],0xf0f0f0f0f0f0f0f0#64⟩,⟨0,12,4,1,0,[0,1,3,4,2,5],0xf000f000f000f000#64⟩,⟨0,3,4,1,0,[3,4,0,1,2,5],0x8888888888888888#64⟩,⟨0,2,7,8,0,[0,4,1,2,3,5],0xcccccccccccccccc#64⟩,⟨0,16,7,8,0,[0,1,2,3,4,5],0xffff0000ffff0000#64⟩,⟨0,8,7,8,0,[0,1,2,4,3,5],0xff00ff00ff00ff00#64⟩,⟨0,5,4,1,0,[3,0,4,1,2,5],0xa0a0a0a0a0a0a0a0#64⟩,⟨0,6,4,1,0,[0,3,4,1,2,5],0xc0c0c0c0c0c0c0c0#64⟩,⟨0,9,4,1,0,[3,0,1,4,2,5],0xaa00aa00aa00aa00#64⟩,⟨0,1,7,8,0,[4,0,1,2,3,5],0xaaaaaaaaaaaaaaaa#64⟩]
def F16T3 : BTree NodeData := nd (lf2 0x10c210801007806 0x19053 [0x1]) (nd (lf2 0xc8310801006c06 0xa1254 []) (lf2 0x990310801006246 0x9d283 []))
def F16T4 : BTree NodeData := nd (nd (nd (nd (lf2 0x10c210801003d05 0x53 []) (lf2 0x10c210801002d85 0x85 [0x2])) (nd (lf2 0x14c210801003d05 0x343 []) (nd (lf2 0x14c210801003985 0x64 [0x1]) (lf2 0x14c210801003985 0x264 [])))) (nd (nd (lf2 0x14c210801002d85 0x284 []) (lf2 0x94c210801003985 0x264 [])) (nd (lf2 0x94c210801002d85 0x284 []) (nd (lf2 0xc8310801003d05 0x54 [0x3]) (lf2 0xc8310801003d05 0x254 [0x4]))))) (nd (nd (nd (lf2 0x108310801003e05 0x43 []) (lf2 0x990310801002b45 0x283 [0x5])) (nd (lf2 0x9903108010032c5 0x274 []) (nd (lf2 0xd0c530801002d25 0x282 []) (lf2 0x1d8540c810021e5 0x280 [])))) (nd (nd (lf2 0x9ca540c810030b5 0x264 []) (nd (lf2 0x9c0650c810031c5 0x271 []) (lf2 0x9c0650c810030e5 0x174 []))) (nd (lf2 0x1933214810021b5 0x187 []) (nd (lf2 0x58c631481002875 0x84 [0xb06]) (lf2 0x9d2631481003075 0x243 [0x706])))))
def F16M4 : BST := BN 193161047 134 (BN 151535728 128 (BN 139424069 98 (BL 114841535 420) BE) (BL 176861034 24)) (BN 298601115 384 (BN 195581145 410 (BL 193262867 0) BE) (BL 320189048 396))
def F16T5_0 := nd (nd (nd (nd (lf 0x10c210801001f84 [0x80207070805,0x900080004]) (nd (lf 0x14c210801001d84 [0x100040902,0xa]) (lf 0x14c210801001f84 [0x109020004,0xa]))) (nd (lf 0x94c210801001d84 [0x807070004,0x9]) (nd (lf 0xc8310801001f04 [0x300080004,0x1]) (lf 0x108310801001f84 [])))) (nd (nd (lf 0x1c8310801001f84 [0x10009040b]) (nd (lf 0x150310801001dc4 []) (lf 0x950310801001dc4 []))) (nd (lf 0x190310801001bc4 [0x1]) (nd (lf 0x990310801001bc4 [0x8]) (lf 0x1d44308010015e4 [0x2]))))) (nd (nd (nd (lf 0xc8530801001da4 [0x2]) (nd (lf 0x9c8530801001da4 [0x20004000a]) (lf 0xd0c530801001d64 []))) (nd (lf 0x1905308010019e4 [0x1]) (nd (lf 0x9905308010019e4 []) (lf 0x9d05308010015e4 [0xd02])))) (nd (nd (lf 0x9c85308010017a4 [0x2000a]) (nd (lf 0xca530801001da4 [0x307]) (lf 0x9925308010019e4 []))) (nd (nd (lf 0x9d25308010015e4 [0x2]) (lf 0x184600c81001bc4 [0x60b0d020a05])) (nd (lf 0x1d8540c810011f4 []) (lf 0x9d8540c810011f4 [0xd02])))))
def F16T5_1 := nd (nd (nd (nd (lf 0x9ca540c810015b4 [0x7]) (nd (lf 0x992540c810018f4 []) (lf 0x9da540c810011f4 []))) (nd (lf 0x9c0650c810019e4 [0x5]) (nd (lf 0x5d0650c810018f4 []) (lf 0x9d0650c810010f4 [])))) (nd (nd (lf 0x9d0650c810018f4 [0x6]) (nd (lf 0x9d0650c810011f4 []) (lf 0x9c8650c810015b4 [0x2]))) (nd (nd (lf 0x9d0650c810014f4 [0xd02]) (lf 0x9c2650c810013e4 [0x5])) (nd (lf 0x9d6650c810011f4 [0x6]) (lf 0x1933214810019b4 [0x7]))))) (nd (nd (nd (lf 0x9933214810019b4 []) (nd (lf 0x9d33214810015b4 []) (lf 0x5db3214810015b4 [0x80009]))) (nd (lf 0x9c06314810015e4 [0x5]) (nd (lf 0x58c631481001974 [0x307]) (lf 0x9d06314810014f4 [])))) (nd (nd (lf 0x8ca631481001974 [0x2]) (nd (lf 0x9d26314810011f4 []) (lf 0xd8e631481001974 [0x307]))) (nd (nd (lf 0xd4e631481001974 []) (lf 0x8ca639481001974 [0x2])) (nd (lf 0xd0e639481001974 []) (lf 0x9d26394810011f4 [])))))
def F16T5 : BTree NodeData := nd F16T5_0 F16T5_1
def F16M5 : BST := BN 279273545 256 (BN 236267309 1280 (BN 212430633 670 (BN 180442554 46 (BN 166310738 446 (BN 161713729 20 (BL 161678573 1188) BE) (BL 177756307 676)) (BN 201841615 3596 (BN 198884918 1044 (BL 198372766 3840) BE) (BL 205233494 3736))) (BN 223666126 3615 (BN 220083158 384 (BN 217207869 640 (BL 215116880 1) BE) (BL 220990809 1024)) (BN 230340095 1792 (BN 225036050 128 (BL 223832684 1811) BE) (BL 233808944 1539)))) (BN 263830164 1552 (BN 250866353 3614 (BN 242105177 31 (BN 241409675 1541 (BL 240067959 3591) BE) (BL 250805397 1560)) (BN 258507010 7 (BN 257421048 1304 (BL 256777351 646) BE) (BL 263406580 3584))) (BN 269929575 3846 (BN 267511284 1038 (BN 267207230 1536 (BL 267125864 3760) BE) (BL 269648445 3968)) (BN 276835208 3808 (BN 276690753 1852 (BL 273730225 1798) BE) (BL 278402440 12))))) (BN 313727705 1545 (BN 289557559 896 (BN 286729227 3528 (BN 282833682 1561 (BN 281851637 386 (BL 280997278 3712) BE) (BL 284560319 3608)) (BN 288723816 444 (BN 287724078 1054 (BL 287139421 0) BE) (BL 288953385 1692))) (BN 306230538 1632 (BN 299264827 1159 (BN 291507064 3480 (BL 290838251 3876) BE) (BL 299722314 3504)) (BN 308652354 1664 (BN 307433904 1834 (BL 307316137 1668) BE) (BL 309927055 3598)))) (BN 346156003 30 (BN 325794020 270 (BN 321370718 768 (BN 320769741 3900 (BL 320454376 3784) BE) (BL 322423162 3638)) (BN 331805591 6 (BN 327748505 1036 (BL 326223812 1585) BE) (BL 343400523 3456))) (BN 367026086 1164 (BN 362422831 1030 (BN 358394286 1408 (BL 353616449 1420) BE) (BL 366609536 1414)) (BN 383103820 652 (BN 376060270 1828 (BL 375369643 1152) BE) (BL 396278636 512)))))
def F16T6 : BTree NodeData := nd (nd (nd (nd (lf 0x210801000f83 [0x40b00080004,0x907060707,0x205]) (lf 0x310801000fc3 [0x50203070004,0x10008])) (nd (lf 0x430801000fe3 [0x800040405,0x3070402]) (nd (lf 0x530801000de3 [0x4000a0502,0x1]) (lf 0x530801000fe3 [0xa05020004,0x1])))) (nd (nd (lf 0x2530801000de3 [0x30705020004,0x8]) (nd (lf 0x600c81000fe3 [0x3000a0605,0x80502]) (lf 0x540c81000df3 [0x405040b0003,0x5060502]))) (nd (lf 0x2540c81000df3 [0x50200030004,0x506]) (nd (lf 0x650c810009f3 [0x605060b0006,0x5070502]) (lf 0x650c81000df3 [0x402060502]))))) (nd (nd (nd (lf 0x2650c81000bf3 [0x605]) (lf 0x321481000df3 [0x403020007])) (nd (lf 0x3321481000db3 [0x102]) (nd (lf 0x631481000df3 [0x70306]) (lf 0x26314810009f3 [0x60b07060307,0x40605])))) (nd (nd (lf 0x2631481000df3 [0x800090307,0x4]) (nd (lf 0x3321481000fb3 [0x102]) (lf 0x531481000df3 [0x60505070302]))) (nd (lf 0x2631481000bf3 [0x60501070009,0x8]) (nd (lf 0x329481000df3 [0x102]) (lf 0x26394810009f3 [0x603070004])))))
def F16M6 : BST := BN 333973877 3328 (BN 294316744 3840 (BN 277086932 3358 (BN 259267671 3614 (BN 254386917 2560 (BN 252657916 1025 (BN 224593345 3620 (BL 222419588 6656) BE) (BL 253531324 2944)) (BN 257087645 1024 (BL 256560674 1572) (BL 258871656 7452))) (BN 268542512 6272 (BN 262563320 7476 (BL 261128262 7939) (BL 266920196 128)) (BN 270886271 1378 (BL 269129109 1645) (BL 276835208 7296)))) (BN 287857934 1651 (BN 284227857 7936 (BN 282997930 2176 (BL 277234408 7428) (BL 284226916 2048)) (BN 284702565 2330 (BL 284625245 2049) (BL 285684177 2581))) (BN 291558106 7680 (BN 290749911 3072 (BL 290017800 1820) (BL 291235000 1566)) (BN 293976397 3584 (BL 293731863 7754) (BL 294218760 2060))))) (BN 315388127 1664 (BN 308380552 1796 (BN 305855080 794 (BN 298980413 7168 (BN 297777047 1536 (BL 295817975 282) BE) (BL 303614389 3590)) (BN 307083238 3334 (BL 306834606 6912) (BL 308146958 6657))) (BN 311838622 3591 (BN 310635256 3335 (BL 309054261 1305) (BL 311613542 2079)) (BN 312496561 6786 (BL 312438289 131) (BL 314885073 3610)))) (BN 328015375 2055 (BN 318892962 1054 (BN 317709238 7194 (BL 316015646 6414) (BL 318533740 8064)) (BN 325489648 6784 (BL 324214725 1031) (BL 326586009 7196))) (BN 329074307 2579 (BN 328688675 130 (BL 328315870 6275) (BL 328893086 2054)) (BN 330747391 2062 (BL 330277673 7220) (BL 332771679 548)))))) (BN 388399756 7552 (BN 352383564 0 (BN 343243498 2078 (BN 335852056 1920 (BN 335286229 2561 (BN 335183389 256 (BL 334604268 538) BE) (BL 335581718 1542)) (BN 338977893 1543 (BL 337774527 1280) (BL 339050567 1281))) (BN 345852560 1480 (BN 345368464 1055 (BL 343642705 5844) (BL 345481051 512)) (BN 346893216 7730 (BL 346007886 5784) (BL 349840842 7424)))) (BN 368400883 6151 (BN 363105140 7708 (BN 353692076 2688 (BL 352651600 385) (BL 357706718 2575)) (BN 366796804 7732 (BL 365897366 2354) (BL 367446005 542))) (BN 382613124 3712 (BN 381467892 7684 (BL 369278594 6150) (BL 381932376 1586)) (BN 385525629 7756 (BL 385265266 5888) (BL 387270094 270))))) (BN 416943979 6144 (BN 398904039 7218 (BN 391938015 1792 (BN 390788811 2304 (BL 390286027 1432) (BL 391262609 3456)) (BN 398501277 1456 (BL 395398709 3200) (BL 398818765 1030))) (BN 405614635 1224 (BN 402253166 6175 (BL 400107092 1562) (BL 402372888 2573)) (BN 410368775 5948 (BL 408506201 640) (BL 410392472 1176)))) (BN 461908187 1548 (BN 432990128 7686 (BN 418607722 1200 (BL 417342308 6145) (BL 429940858 3596)) (BN 442179486 1408 (BL 433883122 6174) (BL 451596956 768))) (BN 490050078 2306 (BN 463464454 562 (BL 462285931 1152) (BL 466845933 6400)) (BN 501165488 258 (BL 498528194 5760) (BL 511202593 770))))))
def F16T7 : BTree NodeData := nd (nd (lf 0x8010007e2 [0x802050102,0x30603070004]) (lf 0xc810007f2 [0x20b01020205,0x300040107,0x1060206])) (nd (lf 0x14810005f2 [0x307020b0009,0x400080306]) (nd (lf 0x14810007f2 [0x30700090004,0x802050306,0x20b]) (lf 0x94810005f2 [0x30701020004,0x306])))
def F16M7 : BST := BN 399786038 1031 (BN 356967970 1610 (BN 327654942 256 (BN 314796733 1024 (BN 278379640 3712 (BN 275719163 282 (BL 261701054 1562) BE) (BN 309525784 3968 (BL 285882993 646) BE)) (BN 323728112 647 (BN 323225213 257 (BL 316970490 1060) BE) (BL 325147818 3713))) (BN 345035061 0 (BN 342895855 1586 (BN 338065235 188 (BL 329834968 768) BE) (BL 342998695 1564)) (BN 354794213 1536 (BN 351644816 1054 (BL 346690359 1588) BE) (BL 355192542 1537)))) (BN 378457530 640 (BN 366181792 3969 (BN 361802297 3328 (BN 361361447 1540 (BL 357016804 284) BE) (BL 364744232 1158)) (BN 369855182 3331 (BN 369464077 1566 (BL 366504040 1793) BE) (BL 375379556 260))) (BN 394782022 263 (BN 389944188 384 (BN 383873291 771 (BL 382613124 1792) BE) (BL 394418117 3610)) (BN 398582672 1543 (BN 396094374 1025 (BL 395991534 1030) BE) (BL 399460383 1542))))) (BN 457864881 897 (BN 425124618 600 (BN 408152955 3388 (BN 404854102 1153 (BN 402704129 540 (BL 401059598 1152) BE) (BN 408016996 1304 (BL 406395793 576) BE)) (BN 421166043 3840 (BN 421066881 516 (BL 411096703 896) BE) (BL 422950861 512))) (BN 438013302 1280 (BN 436712366 385 (BN 434813926 3457 (BL 434415597 3456) BE) (BL 436778639 641)) (BN 446041873 1159 (BN 439845891 3590 (BL 438968180 3591) BE) (BL 452231943 828)))) (BN 489685033 1364 (BN 478068588 1665 (BN 475612918 1340 (BN 469386062 262 (BL 467048567 1538) BE) (BL 475715758 3612)) (BN 487511276 3584 (BN 481066676 258 (BL 479407422 1346) BE) (BL 487909605 3585))) (BN 513724834 128 (BN 499221103 3906 (BN 494177672 1664 (BL 494078510 3588) BE) (BL 511174593 1408)) (BN 569495702 1409 (BN 522318003 1036 (BL 515330187 3900) BE) (BL 599765630 3586)))))
def F16T8 : BTree NodeData := lf 0x10003f1 [0x102000b0005,0x401060107]
def F16M8 : BST := BN 382513962 4 (BN 323249378 132 (BN 295711778 898 (BN 291282049 900 (BL 282853569 26) BE) (BL 322851049 130)) (BN 371255640 24 (BN 364151210 28 (BL 362506679 128) BE) (BL 376524788 896))) (BN 455568112 386 (BN 422212113 256 (BN 415602358 0 (BL 391007697 259) BE) (BL 426006617 257)) (BN 488201082 2 (BL 455966441 388) (BL 495223742 384)))
def F16T9 : BTree NodeData := lf 0x1f0 [0x2000b0005,0x60007]
def F16M9 : BST := BN 293289554 66 (BN 258290634 90 (BN 258239243 18 (BL 253179684 36) BE) (BN 291327639 6 (BL 289495050 60) BE)) (BN 363926363 12 (BN 341581755 30 (BL 334477325 42) BE) (BL 383659194 0))
def F16L : Nat → Option (BTree NodeData) | 3 => some F16T3 | 4 => some F16T4 | 5 => some F16T5 | 6 => some F16T6 | 7 => some F16T7 | 8 => some F16T8 | 9 => some F16T9 | _ => none
def F16M : Nat → BST | 4 => F16M4 | 5 => F16M5 | 6 => F16M6 | 7 => F16M7 | 8 => F16M8 | 9 => F16M9 | _ => BE
def tF17 : Sig := 0xfee8e880fee8e880#64
def F17P : List Row := mkRows [7,11,19,7,13,21,7,14,22,11,13,25,11,14,26,13,14,28,19,21,25,19,22,26,21,22,28,25,26,28,13,14,21,22,25,26,11,14,19,22,25,28,11,13,19,21,26,28,7,14,19,21,26,28,7,13,19,22,25,28,7,11]
def F17N : List Row := mkRows [3,3,3,5,5,5,6,6,6,9,9,9,10,10,10,12,12,12,17,17,17,18,18,18,20,20,20,24,24,24,3,3,3,3,3,3,5,5,5,5,5,5,6,6,6,6,6,6,9,9,9,9,9,9,10,10,10,10,10,10,12,12]
def F17R : List (Nat × Nat) := [(3876822290746089087,17737320507379263),(3699519054091219919,1135184250688008647),(1939831685450016249,3459045920195445240),(3220864544365870738,4611404544390462976),(1098020480628967716,1073479680)]
def F17A : List (List Nat) := [[0,1,2,3,4,5],[0,1,2,4,3,5],[0,1,3,2,4,5],[0,1,3,4,2,5],[0,1,4,2,3,5],[0,1,4,3,2,5],[0,2,1,3,4,5],[0,2,1,4,3,5],[0,2,3,1,4,5],[0,2,3,4,1,5],[0,2,4,1,3,5],[0,2,4,3,1,5],[0,3,1,2,4,5],[0,3,1,4,2,5],[0,3,2,1,4,5],[0,3,2,4,1,5],[0,3,4,1,2,5],[0,3,4,2,1,5],[0,4,1,2,3,5],[0,4,1,3,2,5],[0,4,2,1,3,5],[0,4,2,3,1,5],[0,4,3,1,2,5],[0,4,3,2,1,5],[1,0,2,3,4,5],[1,0,2,4,3,5],[1,0,3,2,4,5],[1,0,3,4,2,5],[1,0,4,2,3,5],[1,0,4,3,2,5],[1,2,0,3,4,5],[1,2,0,4,3,5],[1,2,3,0,4,5],[1,2,3,4,0,5],[1,2,4,0,3,5],[1,2,4,3,0,5],[1,3,0,2,4,5],[1,3,0,4,2,5],[1,3,2,0,4,5],[1,3,2,4,0,5],[1,3,4,0,2,5],[1,3,4,2,0,5],[1,4,0,2,3,5],[1,4,0,3,2,5],[1,4,2,0,3,5],[1,4,2,3,0,5],[1,4,3,0,2,5],[1,4,3,2,0,5],[2,0,1,3,4,5],[2,0,1,4,3,5],[2,0,3,1,4,5],[2,0,3,4,1,5],[2,0,4,1,3,5],[2,0,4,3,1,5],[2,1,0,3,4,5],[2,1,0,4,3,5],[2,1,3,0,4,5],[2,1,3,4,0,5],[2,1,4,0,3,5],[2,1,4,3,0,5],[2,3,0,1,4,5],[2,3,0,4,1,5],[2,3,1,0,4,5],[2,3,1,4,0,5],[2,3,4,0,1,5],[2,3,4,1,0,5],[2,4,0,1,3,5],[2,4,0,3,1,5],[2,4,1,0,3,5],[2,4,1,3,0,5],[2,4,3,0,1,5],[2,4,3,1,0,5],[3,0,1,2,4,5],[3,0,1,4,2,5],[3,0,2,1,4,5],[3,0,2,4,1,5],[3,0,4,1,2,5],[3,0,4,2,1,5],[3,1,0,2,4,5],[3,1,0,4,2,5],[3,1,2,0,4,5],[3,1,2,4,0,5],[3,1,4,0,2,5],[3,1,4,2,0,5],[3,2,0,1,4,5],[3,2,0,4,1,5],[3,2,1,0,4,5],[3,2,1,4,0,5],[3,2,4,0,1,5],[3,2,4,1,0,5],[3,4,0,1,2,5],[3,4,0,2,1,5],[3,4,1,0,2,5],[3,4,1,2,0,5],[3,4,2,0,1,5],[3,4,2,1,0,5],[4,0,1,2,3,5],[4,0,1,3,2,5],[4,0,2,1,3,5],[4,0,2,3,1,5],[4,0,3,1,2,5],[4,0,3,2,1,5],[4,1,0,2,3,5],[4,1,0,3,2,5],[4,1,2,0,3,5],[4,1,2,3,0,5],[4,1,3,0,2,5],[4,1,3,2,0,5],[4,2,0,1,3,5],[4,2,0,3,1,5],[4,2,1,0,3,5],[4,2,1,3,0,5],[4,2,3,0,1,5],[4,2,3,1,0,5],[4,3,0,1,2,5],[4,3,0,2,1,5],[4,3,1,0,2,5],[4,3,1,2,0,5],[4,3,2,0,1,5],[4,3,2,1,0,5]]
def F17C : List CutSpec := [⟨2,0,7,8,0,[0,4,1,2,3,5],0x3333333333333333#64⟩,⟨0,2,7,9,0,[0,4,1,2,3,5],0xcccccccccccccccc#64⟩,⟨4,0,7,8,0,[0,1,4,2,3,5],0xf0f0f0f0f0f0f0f#64⟩,⟨0,4,7,9,0,[0,1,4,2,3,5],0xf0f0f0f0f0f0f0f0#64⟩,⟨8,0,7,8,0,[0,1,2,4,3,5],0xff00ff00ff00ff#64⟩,⟨0,8,7,9,0,[0,1,2,4,3,5],0xff00ff00ff00ff00#64⟩,⟨16,0,7,8,0,[0,1,2,3,4,5],0xffff0000ffff#64⟩,⟨0,16,7,9,0,[0,1,2,3,4,5],0xffff0000ffff0000#64⟩]
def F17T9 : BTree NodeData := lf 0x1f0 [0x300020001,0x600050004,0x80007]
def F17L : Nat → Option (BTree NodeData) | 9 => some F17T9 | _ => none
def F17M : Nat → BST | _ => BE
def tRt : Sig := 0xfee8e880fe008000#64
def RtP : List Row := mkRows [15,43,15,45,15,46,39,43,51,39,45,53,39,46,54,43,45,43,46,45,46,51,53,51,54,53,54,25,26,25,28,26,28,15,39,51,53,54,25,26,28,25,26,28,25,26,28,39,45,46,51,39,43,46,53,39,43,45,54,25,26,28]
def RtN : List Row := mkRows [11,11,13,13,14,14,35,35,35,37,37,37,38,38,38,41,41,42,42,44,44,49,49,50,50,52,52,11,11,13,13,14,14,23,23,23,23,23,41,42,44,49,50,52,56,56,56,11,11,11,11,13,13,13,13,14,14,14,14,23,23,23]
def RtR : List (Nat × Nat) := [(855000437414928351,4071116067863367631),(1566870790114571255,4577773504694743539),(2804556432225959549,4609444388661657148),(4265893751708165311,576445092720508991),(4342736652408473856,4035364071009157120),(576320272647323626,140462744666048)]
def RtA : List (List Nat) := [[0,1,2,3,4,5],[0,2,1,3,4,5],[1,0,2,3,4,5],[1,2,0,3,4,5],[2,0,1,3,4,5],[2,1,0,3,4,5]]
def RtC : List CutSpec := [⟨0,16,8,14,0,[2,3,4,0,5,1],0xffff0000ffff0000#64⟩,⟨8,0,8,11,0,[1,2,3,5,4,0],0xff00ff00ff00ff#64⟩,⟨16,0,10,16,0,[0,1,2,3,5,4],0xffff0000ffff#64⟩,⟨4,3,4,1,0,[3,4,5,0,1,2],0x808080808080808#64⟩,⟨0,8,9,15,0,[1,2,3,5,0,4],0xff00ff00ff00ff00#64⟩,⟨0,4,8,13,0,[3,4,5,0,2,1],0xf0f0f0f0f0f0f0f0#64⟩,⟨4,0,8,12,0,[2,3,5,0,1,4],0xf0f0f0f0f0f0f0f#64⟩,⟨0,3,5,5,0,[4,5,2,0,3,1],0x8888888888888888#64⟩,⟨2,1,5,3,0,[4,5,2,0,1,3],0x2222222222222222#64⟩,⟨32,8,6,7,0,[1,2,3,4,0,5],0xff00ff00#64⟩,⟨16,32,7,8,0,[0,1,2,3,4,5],0xffff00000000#64⟩,⟨0,32,10,17,0,[0,1,2,3,4,5],0xffffffff00000000#64⟩,⟨32,0,7,10,0,[2,3,4,0,1,5],0xffffffff#64⟩,⟨0,36,7,9,0,[0,1,4,2,3,5],0xf0f0f0f000000000#64⟩,⟨1,0,8,12,0,[5,2,3,0,1,4],0x5555555555555555#64⟩,⟨2,5,4,1,0,[3,4,5,0,1,2],0x2020202020202020#64⟩,⟨0,40,7,9,0,[0,1,2,4,3,5],0xff00ff0000000000#64⟩,⟨2,16,5,4,0,[1,4,2,0,5,3],0x3333000033330000#64⟩,⟨4,32,7,8,0,[0,1,4,2,3,5],0xf0f0f0f00000000#64⟩,⟨0,1,8,13,0,[5,3,4,0,2,1],0xaaaaaaaaaaaaaaaa#64⟩,⟨8,1,5,2,0,[4,1,2,5,3,0],0xaa00aa00aa00aa#64⟩,⟨0,12,5,6,0,[1,2,4,5,0,3],0xf000f000f000f000#64⟩,⟨0,2,8,13,0,[3,5,4,0,2,1],0xcccccccccccccccc#64⟩,⟨2,0,8,12,0,[2,5,3,0,1,4],0x3333333333333333#64⟩,⟨4,8,5,4,0,[1,2,4,5,0,3],0xf000f000f000f00#64⟩,⟨16,4,7,8,0,[0,1,4,2,5,3],0xf0f00000f0f0#64⟩,⟨4,2,5,3,0,[2,4,5,0,1,3],0xc0c0c0c0c0c0c0c#64⟩,⟨0,9,5,6,0,[4,1,2,5,0,3],0xaa00aa00aa00aa00#64⟩,⟨16,2,7,8,0,[0,4,1,2,5,3],0xcccc0000cccc#64⟩,⟨4,16,5,4,0,[1,2,4,0,5,3],0xf0f00000f0f0000#64⟩,⟨16,1,7,8,0,[4,0,1,2,5,3],0xaaaa0000aaaa#64⟩,⟨0,33,7,9,0,[4,0,1,2,3,5],0xaaaaaaaa00000000#64⟩]
def RtT3 : BTree NodeData := lf2 0xa0f544401023088 0xf2da228b76 [0xf301]
def RtT4 : BTree NodeData := nd (nd (lf2 0xdd8534401011187 0x3ba64892 [0x4047f037b02]) (lf2 0xa0f54440101b087 0x1a228b76 [0x7301])) (nd (lf2 0xa0f54440101b087 0x3a2a8b76 [0x7301]) (lf2 0xddb544401011087 0x3ba64892 [0x7f057b010404]))
def RtM4 : BST := BL 162387671 0
def RtT5 : BTree NodeData := nd (nd (nd (lf2 0xdd853440100d186 0x64892 [0x3f033b053b02,0xf070f06]) (nd (lf2 0xdd853440100d186 0xe4a92 [0x4083f033b02,0x409]) (lf2 0xdd853440100b0c6 0x69392 [0x3b053b02]))) (nd (lf2 0xa0f54440100f0c6 0x28b76 [0x130a33011707,0x1702]) (nd (lf2 0xa0f54440100f0c6 0x68b76 [0x3301130a1702]) (lf2 0xa0f54440100f0c6 0xa8b76 [0x3301130a1702])))) (nd (nd (lf2 0xa0f54440100f0c6 0xe8b76 [0x33011702130a,0x130b]) (nd (lf2 0xddb54440100d086 0x64892 [0x3b0104090408,0x3f05]) (lf2 0xddb54440100d086 0xe4a92 [0x3b0104080409,0x3f05]))) (nd (nd (lf2 0xddb54440100d046 0x64c93 [0xf05]) (lf2 0xddb54440100d046 0xe4e93 [0xf05])) (nd (lf2 0x20b764401008386 0xea582 [0x43f0c3f03,0x3f05]) (lf2 0xa0b76440100a186 0xa9782 [0x3f053f032009,0xf0e0f0d]))))
def RtM5 : BST := BN 163139780 256 (BN 141127879 0 (BL 78152726 384) BE) (BL 244477768 128)
def RtT6 : BTree NodeData := nd (nd (nd (nd (nd (lf2 0xd503244010070c5 0x376 [0x130b1b050804,0x1301]) (lf2 0x6103244010062c5 0x376 [0x13071f0c1b05,0x13021301])) (nd (lf2 0x6103244010046c5 0x97 [0x1f0c1c0f1b05,0x1307]) (lf2 0xd533244010070c5 0x376 [0x130b1b050810,0x1301]))) (nd (nd (lf2 0x6133244010062c5 0x376 [0x13061f0c1b05,0x1301]) (lf2 0xdd85344010071c5 0x92 [0x1f030f071b02,0xf061b050409])) (nd (lf2 0xdd85344010071c5 0x192 [0x1f0304091b02,0x1b050f06]) (lf2 0xdd85344010071c5 0x292 [0x1f030f071b02,0xb110409])))) (nd (nd (nd (lf2 0xdd85344010071c5 0x392 [0x1f030f061b02,0xf070b110409]) (lf2 0x60b5444010070c5 0x376 [0x1f0513010410,0x1702])) (nd (lf2 0xa0b5444010070c5 0x376 [0x1f0513010404,0x1702]) (lf2 0xa0f5444010070c5 0x376 [0x13011702130a]))) (nd (nd (lf2 0xddb5444010070c5 0x92 [0x1f0504080f07,0xb0b0f021b01]) (lf2 0xddb5444010070c5 0x192 [0x1f0504090f06,0xb0b0f021b01])) (nd (lf2 0xddb5444010070c5 0x292 [0x1f0504090f07,0xb0b0f021b01]) (lf2 0xddb5444010070c5 0x392 [0x1f0504080f06,0xb0b0f021b01]))))) (nd (nd (nd (nd (lf2 0xddb5444010070c5 0x93 [0x1b010f020404,0xb0b]) (lf2 0xddb5444010070c5 0x293 [0x1b010f020410,0xb0b])) (nd (lf2 0xddb5444010070c5 0x198 [0x1f0500120410,0xf02]) (lf2 0xddb5444010070c5 0x398 [0x1f0500120404,0xf02]))) (nd (nd (lf2 0x20b764401006385 0x182 [0x81f0c1f03,0x1f050009]) (lf2 0xa0b764401006385 0x382 [0x81f031f0c,0x1f050009])) (nd (lf2 0xa0b7644010052c5 0x194 [0x70100091f0c,0x1f050707]) (lf2 0xa0b7644010051c5 0x295 [0x91f030713,0x702])))) (nd (nd (nd (lf2 0xe0b764401005345 0x293 [0x7021f0c1f03,0x706]) (lf2 0xe0b7644010052c5 0x194 [0x70607011f0c,0x1f050008])) (nd (lf2 0xe0b7644010051c5 0x295 [0x81f03070e,0x702]) (lf2 0x20f764401006345 0x183 [0x705]))) (nd (nd (lf2 0x20f7644010052c5 0x194 [0x81f0c0702,0x701]) (lf2 0xa0f764401007245 0x143 [0x705])) (nd (lf2 0xa0f764401006345 0x383 [0x705]) (lf2 0xa0f7644010052c5 0x194 [0x10041f0c0702,0x701])))))
def RtM6 : BST := BN 247951051 128 (BN 141879988 0 (BN 122317855 384 (BL 78904835 640) (BL 139098199 896)) (BN 223217976 512 (BL 160242823 1664) BE)) (BN 280971243 256 (BN 263761465 1408 (BL 258776425 768) (BL 267681137 1536)) (BN 373134605 1792 (BL 293215668 1920) BE))
def RtT7 : BTree NodeData := nd (nd (nd (nd (nd (lf 0xd50324401003cc4 [0xc140b050b07,0x301030b0c0f]) (lf 0x610324401002ec4 [0xf0c0c140b05,0x30101070c0f])) (nd (lf 0xdd83244010033c4 [0xf030f0c0b02,0x90b050b07,0x8]) (lf 0xd53324401003cc4 [0xc140b050b06,0x301030b0c0f]))) (nd (nd (lf 0x613324401002ec4 [0xc140f0c0b05,0x9070b070c0f]) (lf 0xddb3244010033c4 [0xf030b050b06,0x800090f0c])) (nd (lf 0xa1f3244010027c4 [0xc0f0f0c0015,0xb050306]) (nd (lf 0x14c724401003584 [0xc0f0f030702,0x705]) (lf 0xdd85344010031c4 [0xf030b02]))))) (nd (nd (nd (lf 0x60b544401003cc4 [0xc1403010706,0x7020f050c0f]) (lf 0xa0b544401003cc4 [0xc1403010707,0x7020f050c0f])) (nd (lf 0xa0f544401003cc4 [0xc1403010702,0x70607070c0f]) (nd (lf 0xddb5444010030c4 [0xb010f05]) (lf 0x20b7644010033c4 [0xf030f0c0707,0x7020f050008])))) (nd (nd (lf 0x60b7644010033c4 [0xf030f0c0706,0x7020f050009]) (lf 0xa0b7644010033c4 [0xf030f0c0707,0x7020f050009])) (nd (lf 0xe0b7644010033c4 [0xf0c0f030706,0x7050f050008,0x702]) (nd (lf 0x20f7644010033c4 [0xf030f0c0702,0x70607070008]) (lf 0xa0f7644010033c4 [0xf030f0c0702,0x7060f050004])))))) (nd (nd (nd (nd (lf 0x5db540c810030f4 [0xe0f0e140416,0x10e180e17,0xb]) (lf 0x5db54cc810030f4 [0xe0f0e140419,0x10e180e17,0xb])) (nd (lf 0x61a72d5010028f4 [0xf0509010208,0x2020b07091a]) (nd (lf 0x9db540c910030f4 [0xd0706170415,0xb00010d06]) (lf 0x219740c910022f4 [0x9070f0c0d05,0xe170e0f0e18,0xe14])))) (nd (nd (lf 0x9db54cc910030f4 [0xd0606170415,0xb00010d07]) (lf 0x19574cc910030f4 [0x61706140d05,0x9010906])) (nd (lf 0xa1a72d5110028f4 [0x9010614021b,0x2020f05]) (nd (lf 0xd5032c421003cc4 [0xc170b050b07,0x301030b0c14]) (lf 0x61032c421002ec4 [0xc170f0c0b05,0xf030c14]))))) (nd (nd (nd (lf 0xd5332c421003cc4 [0xc170b050b06,0x301030b0c14]) (lf 0x61332c421002ec4 [0x3060f0c0b05,0xc140c17])) (nd (lf 0x60b54c421003cc4 [0xc1703010706,0x7020f050c14]) (nd (lf 0xa0b54c421003cc4 [0xc1703010707,0x7020f050c14]) (lf 0xa0f54c421003cc4 [0xc1703010702,0x70607070c14])))) (nd (nd (lf 0x5db540ca10030f4 [0xd060d050409,0xb00010d07]) (lf 0x5db54cca10030f4 [0x5060d050409,0xb0001])) (nd (lf 0x61a72d5210028f4 [0xf0509010209,0x2020b07091a]) (nd (lf 0x61a71d5030028f4 [0x91d0901021c,0x20602070b18]) (lf 0x61a71d5330028f4 [0x9010e050209,0x2060207]))))))
def RtM7 : BST := BN 243963457 3968 (BN 199706116 1664 (BN 174541480 2816 (BN 167907923 512 (BN 163716106 3840 (BL 139850308 640) BE) (BL 174224232 128)) (BN 196736298 768 (BL 183263328 3456) (BL 199547851 0))) (BN 235109526 3072 (BN 221188296 2688 (BL 202345671 1152) (BL 226691259 256)) (BN 239221412 1024 (BL 237516633 1536) (BL 241688323 896)))) (BN 284528023 3712 (BN 257299898 1280 (BN 254853842 384 (BL 245229877 3328) (BL 255642045 2176)) (BN 265651457 2432 (BL 259711451 2560) (BL 272687177 2048))) (BN 296688951 1408 (BN 290885611 3200 (BL 288899660 1792) (BL 291232856 2304)) (BN 324706938 1920 (BL 323527190 2944) (BL 351874813 3584))))
def RtT8_0 := nd (nd (nd (nd (lf 0x324401001fc3 [0x70c03050307,0x40f04140703]) (nd (lf 0x3324401001fc3 [0x305070c0306,0x40f04140703,0x107]) (lf 0x724401001783 [0x40f0703070c,0x7050107]))) (nd (lf 0x534401001dc3 [0x41407030302,0x507040f]) (nd (lf 0x3544401001cc3 [0x7050414040f,0x301]) (lf 0x37644010013c3 [0x705070c0703])))) (nd (nd (lf 0x53c801001de3 [0x61803020507,0x305]) (nd (lf 0x3540c81001cf3 [0x5050507060f,0x201020b0618,0x101010b]) (lf 0x1740c810016f3 [0x6180505060f,0x1010107070c]))) (nd (lf 0x1760c810013f3 [0x703070c0016,0x618060f0614,0xd00060617]) (nd (lf 0x354cc81001cf3 [0x505060f0506,0x201020b0618,0x101010b]) (lf 0x174cc810016f3 [0x70c0505060f,0x61801010106,0x2]))))) (nd (nd (nd (lf 0x176cc810013f3 [0x106070c0505,0x61706140703]) (nd (lf 0x172d501001cf3 [0x101060f0306,0x60207050618,0x1e0302]) (lf 0x272d501001cf3 [0x1010307060f,0x60207050618,0x302]))) (nd (lf 0x273d501001cf3 [0x1010302060f,0x60706060618,0xa03060307]) (nd (lf 0x3540c91001cf3 [0x50505070617,0x40204060614,0x10b020b0201,0x101]) (lf 0x3640c91001af3 [0x201070c0502,0x50502170214,0x1f])))) (nd (nd (lf 0x1740c910016f3 [0x70c05050617,0x701010614,0x20406]) (nd (lf 0x650c910019f3 [0x50707030502,0x20d02170214,0x200505]) (lf 0x2760c910013f3 [0x217070c0015,0x105050703]))) (nd (lf 0x354cc91001cf3 [0x50505060617,0x20104070614,0x101010b020b]) (nd (lf 0x364cc91001af3 [0x201070c0502,0x21702140506,0x1f0505]) (lf 0x174cc910016f3 [0x70c05050617,0x10101060614,0x1a00020407])))))
def RtT8_1 := nd (nd (nd (nd (lf 0x65cc910019f3 [0x50507030506,0x20d02170214,0x20]) (nd (lf 0x276cc910013f3 [0x217070c0015,0x105050703]) (lf 0x5318910019b3 [0x70304170302,0x3050414]))) (nd (lf 0x53d8910019b3 [0x40607030302,0x414]) (nd (lf 0x36414d10018f3 [0x21402010502,0x5050217]) (lf 0x172d511001cf3 [0x10103060617,0x1e07050614,0x3020602])))) (nd (nd (lf 0x272d511001cf3 [0x10103070617,0x1a07050614,0xb03020602]) (nd (lf 0x273d511001cf3 [0x10103020617,0x607000a0614,0x30603070606,0xb]) (lf 0x32c421001fc3 [0x70303050307,0x4140417070c]))) (nd (lf 0x332c421001fc3 [0x70303050306,0x4140417070c]) (nd (lf 0x53c421001dc3 [0x41707030302,0x414]) (lf 0x354c421001cc3 [0x70504140417,0x301]))))) (nd (nd (nd (lf 0x3540ca1001cf3 [0x50505070617,0x201020b060f,0x101010b]) (nd (lf 0x1740ca10016f3 [0x70c05050617,0x1010107060f,0x2]) (lf 0x1760ca10013f3 [0x703070c0505,0x614060f0217,0x507]))) (nd (lf 0x354cca1001cf3 [0x50505060617,0x201020b060f,0x101010b]) (nd (lf 0x174cca10016f3 [0x70c05050617,0x1010106060f]) (lf 0x176cca10013f3 [0x505070c0106,0x61802170703])))) (nd (nd (lf 0x172d521001cf3 [0x10103060617,0x6020705060f,0x1e0302]) (nd (lf 0x272d521001cf3 [0x10103070617,0x6020705060f,0x302]) (lf 0x273d521001cf3 [0x10103020617,0x6070606060f,0xa03060307]))) (nd (nd (lf 0x171d503001cf3 [0x605060f0317,0x60706060101,0x1203060307]) (lf 0x271d503001cf3 [0x6050318060f,0x60706060101,0x3070306])) (nd (lf 0x171d533001cf3 [0x60503170614,0x60706060101,0x1203060307]) (lf 0x271d533001cf3 [0x60503180614,0x60706060101,0x3070306])))))
def RtT8 : BTree NodeData := nd RtT8_0 RtT8_1
def RtM8 : BST := BN 298667501 3712 (BN 235486953 768 (BN 223970085 7680 (BN 209023500 2944 (BN 203462820 1664 (BL 160994932 3328) BE) (BL 217989871 7296)) (BN 226636318 128 (BN 224661579 1792 (BL 224452947 896) BE) (BL 235169705 3840))) (BN 267027573 2432 (BN 260493324 1024 (BN 257681771 7424 (BL 241277216 512) BE) (BL 265993329 3200)) (BN 295804422 1920 (BN 291389230 640 (BL 272917144 0) BE) (BL 296054999 2560)))) (BN 334229176 384 (BN 318599170 1280 (BN 316587518 7936 (BN 313475169 8064 (BL 308478819 3072) BE) (BL 318098705 2688)) (BN 329457195 2176 (BN 326307090 1152 (BL 325528105 3968) BE) (BL 330669191 2304))) (BN 356419548 3456 (BN 349845133 2816 (BN 346056470 2048 (BL 344349527 7552) BE) (BL 353418344 3584)) (BN 373566244 1536 (BN 371806827 7808 (BL 364602149 256) BE) (BL 390352506 1408))))
def RtT9 : BTree NodeData := nd (nd (nd (nd (lf 0x4401000fc2 [0x3030014030c,0x1070305000f]) (nd (lf 0xc801000fe2 [0x30c02180107,0x3050303]) (lf 0xc81000ff2 [0x30c0107020f,0x21803030105]))) (nd (lf 0xcc81000ff2 [0x30c020f0106,0x21703030105,0x1402140018,0x20017]) (nd (lf 0x14c1000df2 [0x303020f0102,0x20601050218,0x207]) (lf 0xd501000cf2 [0x3050218020f,0x20702060101,0xb0202])))) (nd (nd (lf 0xc91000ff2 [0x10501070217,0x214030c0303,0x20006]) (nd (lf 0xcc91000ff2 [0x10501060217,0x214030c0303,0x20007]) (lf 0x1891000bb2 [0x170303030c,0x30500070014]))) (nd (nd (lf 0xd891000bb2 [0x60303030c,0x30500170014]) (lf 0x14d1000df2 [0x30302170102,0x20602070214,0x11])) (nd (lf 0x18d1000b72 [0x20303030c,0x170014]) (lf 0xd511000cf2 [0x30502140217,0x20602070101,0xb0202]))))) (nd (nd (nd (lf 0xd911000af2 [0x140001030c,0x3050017]) (nd (lf 0x19510009f2 [0x1703030020,0x20305]) (lf 0xc421000fc2 [0x17030c0303,0x3050014]))) (nd (nd (lf 0xca1000ff2 [0x10501070217,0x20f0303030c,0x2]) (lf 0xcca1000ff2 [0x30c02170106,0x20f03030105,0x18])) (nd (lf 0x14e1000df2 [0x30302170102,0x2070206020f]) (lf 0xd521000cf2 [0x305020f0217,0x20702060101,0xb0202])))) (nd (nd (lf 0xd503000cf2 [0x1010205020f,0x20602180217,0xb0207]) (nd (lf 0x5903000af2 [0xf030c0205,0x20001]) (lf 0xd533000cf2 [0x10102050214,0x20602180217,0xb0207]))) (nd (nd (lf 0x5933000af2 [0x14030c0205,0x1]) (lf 0x5835400cf2 [0x30500010114,0x10701170118,0x1020106])) (nd (lf 0x9835400cf2 [0x3050001010f,0x10601180117,0x1020107]) (lf 0x98f5400cf2 [0x10f00010102,0x11701180114,0x1060107])))))
def RtM9 : BST := BN 338896240 7680 (BN 297367629 2688 (BN 266153708 6020 (BN 245921574 3459 (BN 234364225 3072 (BN 221940405 7168 (BL 220045675 7936) (BL 229838342 6018)) (BN 244441412 1922 (BL 235215120 2947) BE)) (BN 251685603 3328 (BN 249818190 899 (BL 249713464 2435) BE) (BN 260114582 7808 (BL 254020281 8066) BE))) (BN 287247278 1792 (BN 280143758 3456 (BN 269968973 7552 (BL 268623351 3970) BE) (BN 285398420 6528 (BL 280756778 1924) BE)) (BN 291115462 7043 (BN 288371025 1152 (BL 287581791 1536) BE) (BN 297339378 1024 (BL 291964393 3200) BE)))) (BN 323886639 1281 (BN 318240413 6403 (BN 310185705 2949 (BN 309437650 640 (BL 301715383 8068) BE) (BN 316318453 3972 (BL 311783686 384) BE)) (BN 320892159 3461 (BN 319864749 387 (BL 318386083 1411) BE) (BN 323802366 515 (BL 323089735 3712) BE))) (BN 328946867 7683 (BN 324824929 768 (BN 324788775 901 (BL 324684049 2437) BE) (BN 328487632 7424 (BL 326938802 6912) BE)) (BN 332843483 2307 (BN 332738757 6659 (BL 332186803 6272) BE) (BN 333862617 0 (BL 332919814 643) BE))))) (BN 390402668 256 (BN 363808461 7041 (BN 351388664 6144 (BN 347345361 1408 (BN 343626268 7939 (BL 343370608 7296) BE) (BN 347522884 7299 (BL 347418158 771) BE)) (BN 353223675 1920 (BN 352334703 2176 (BL 351745009 3968) BE) (BN 359612974 6784 (BL 357465712 7040) BE))) (BN 374140755 1283 (BN 369424292 2048 (BN 366086047 7045 (BL 364049307 3840) BE) (BN 370536168 2560 (BL 369535733 2944) BE)) (BN 384923012 2432 (BN 381870468 7042 (BL 374500140 514) BE) (BN 388820156 2691 (BL 387814152 2689) BE)))) (BN 416090777 1795 (BN 402890042 2563 (BN 394835334 389 (BN 393977184 7044 (BL 393356668 1413) BE) (BN 401411376 3587 (BL 395174649 1664) BE)) (BN 407076718 8065 (BN 406097843 3584 (BL 403468691 896) BE) (BN 410684106 2816 (BL 408555384 6017) BE))) (BN 441009676 3969 (BN 419788123 8064 (BN 417569443 3331 (BL 416218194 1280) BE) (BN 428288215 6400 (BL 421266789 6016) BE)) (BN 446245781 128 (BN 443675494 6656 (BL 442488342 1921) BE) (BN 496992111 512 (BL 462221173 2304) BE)))))
def RtT10 : BTree NodeData := nd (nd (lf 0x10007f1 [0x103010c000f,0x601050018,0x20007]) (nd (lf 0x110007f1 [0x10c01030017,0x701050014,0x500020006]) (lf 0x210007f1 [0x103010c0017,0x60105000f,0x20007]))) (nd (nd (lf 0x30007f1 [0x103010c0002,0x170005000f,0x700060018]) (lf 0x330007f1 [0x10300050014,0x180017010c,0x70006])) (nd (lf 0x53005f1 [0x1030002]) (lf 0x354004f1 [0x10105])))
def RtM10 : BST := BN 312250418 384 (BN 276107837 2816 (BN 239651694 3585 (BN 225685678 3458 (BN 206880517 3715 (BL 201503739 386) (BL 213132684 3840)) (BN 237819105 388 (BL 227600789 1920) (BL 238307243 896))) (BN 263879920 1792 (BN 242099133 1408 (BL 240239443 2946) (BL 242203859 2944)) (BN 273230767 3712 (BL 269855670 1667) (BL 273380780 3460)))) (BN 295571152 1924 (BN 286341345 768 (BN 281851102 3717 (BL 279573516 3713) (BL 283501131 3968)) (BN 289934713 128 (BL 289905810 3587) (BL 295309698 0))) (BN 304585211 3843 (BN 302626847 1537 (BL 297635523 3714) (BL 303579207 3841)) (BN 309742239 3716 (BL 308282557 1922) (BL 310771752 3456))))) (BN 372470460 1026 (BN 342548669 1665 (BN 329504110 2948 (BN 321060055 3200 (BL 312631076 256) (BL 321772686 1027)) (BN 331983249 3584 (BL 330157123 3328) (BL 336205920 1664))) (BN 360610676 1666 (BN 348192751 1280 (BL 344826255 1669) (BL 352880963 1539)) (BN 367560364 2819 (BL 366554360 2817) (BL 372131187 1152)))) (BN 454302141 2693 (BN 380810222 643 (BN 372729159 640 (BL 372717392 1668) (BL 379331556 2691)) (BN 408290834 2688 (BL 394958402 1536) (BL 431481641 3072))) (BN 467043316 512 (BN 462356849 515 (BL 455780807 645) (BL 463835515 3075)) (BN 478514916 259 (BL 477036250 1283) (BL 494962431 1024)))))
def RtT11 : BTree NodeData := lf 0x3f0 [0x5000c0003]
def RtM11 : BST := BN 340518989 769 (BN 286631151 642 (BN 262449212 130 (BN 262241339 384 (BL 199266186 896) BE) (BN 274078157 256 (BL 267825990 771) BE)) (BN 334176240 768 (BN 300597167 1 (BL 298764578 132) BE) (BL 334326253 644))) (BN 365530684 259 (BN 358580996 770 (BN 350851283 3 (BL 342796575 773) BE) (BL 364524680 257)) (BN 373195891 128 (BN 371717225 640 (BL 370687712 772) BE) (BL 392928722 0)))
def RtL : Nat → Option (BTree NodeData) | 3 => some RtT3 | 4 => some RtT4 | 5 => some RtT5 | 6 => some RtT6 | 7 => some RtT7 | 8 => some RtT8 | 9 => some RtT9 | 10 => some RtT10 | 11 => some RtT11 | _ => none
def RtM : Nat → BST | 4 => RtM4 | 5 => RtM5 | 6 => RtM6 | 7 => RtM7 | 8 => RtM8 | 9 => RtM9 | 10 => RtM10 | 11 => RtM11 | _ => BE
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
def fF2 : Forest := ⟨15,tF2,4,F2P,F2N,F2R,F2A,F2C,F2L,F2M⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F2v : graphValid fF2 base1 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F2k4 : ok fF2 4 F2T4 := by decide +kernel
private theorem F2lv : levelsChecked fF2 := by
  intro k hk tree ht; change k ≤ 4 at hk; interval_cases k
  all_goals simp [fF2,F2L] at ht
  subst ht; exact F2k4
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowF2 : LowerBV (rawOf 15) tF2 5 :=
  lower_forest fF2 base1 base1_s F2v F2lv (by decide +kernel)
def base2 : Nat → List Sig × Sig × Nat | 1 => (rawOf 7,tF1,4) | 2 => (rawOf 15,tF2,5) | _ => ([],0,0)
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
def base3 : Nat → List Sig × Sig × Nat | 1 => (rawOf 7,tF1,4) | 2 => (rawOf 15,tF2,5) | 3 => (rawOf 15,tF3,5) | _ => ([],0,0)
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
def base4 : Nat → List Sig × Sig × Nat | 1 => (rawOf 7,tF1,4) | 2 => (rawOf 15,tF2,5) | 3 => (rawOf 15,tF3,5) | 4 => (rawOf 15,tF4,5) | _ => ([],0,0)
private theorem base4_s : ∀ k, k ≠ 0 → LowerBV (base4 k).1 (base4 k).2.1 (base4 k).2.2 := by
  intro k _; match k with
  | 1 => exact lowF1
  | 2 => exact lowF2
  | 3 => exact lowF3
  | 4 => exact lowF4
  | 0 | _ + 5 => exact fun _ _ _ _ => Nat.zero_le _
def fF5 : Forest := ⟨15,tF5,4,F5P,F5N,F5R,F5A,F5C,F5L,F5M⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F5v : graphValid fF5 base4 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F5k4 : ok fF5 4 F5T4 := by decide +kernel
private theorem F5lv : levelsChecked fF5 := by
  intro k hk tree ht; change k ≤ 4 at hk; interval_cases k
  all_goals simp [fF5,F5L] at ht
  subst ht; exact F5k4
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowF5 : LowerBV (rawOf 15) tF5 5 :=
  lower_forest fF5 base4 base4_s F5v F5lv (by decide +kernel)
def base5 : Nat → List Sig × Sig × Nat | 1 => (rawOf 7,tF1,4) | 2 => (rawOf 15,tF2,5) | 3 => (rawOf 15,tF3,5) | 4 => (rawOf 15,tF4,5) | 5 => (rawOf 15,tF5,5) | _ => ([],0,0)
private theorem base5_s : ∀ k, k ≠ 0 → LowerBV (base5 k).1 (base5 k).2.1 (base5 k).2.2 := by
  intro k _; match k with
  | 1 => exact lowF1
  | 2 => exact lowF2
  | 3 => exact lowF3
  | 4 => exact lowF4
  | 5 => exact lowF5
  | 0 | _ + 6 => exact fun _ _ _ _ => Nat.zero_le _
def fF6 : Forest := ⟨15,tF6,4,F6P,F6N,F6R,F6A,F6C,F6L,F6M⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F6v : graphValid fF6 base5 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F6k4 : ok fF6 4 F6T4 := by decide +kernel
private theorem F6lv : levelsChecked fF6 := by
  intro k hk tree ht; change k ≤ 4 at hk; interval_cases k
  all_goals simp [fF6,F6L] at ht
  subst ht; exact F6k4
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowF6 : LowerBV (rawOf 15) tF6 5 :=
  lower_forest fF6 base5 base5_s F6v F6lv (by decide +kernel)
def base6 : Nat → List Sig × Sig × Nat | 1 => (rawOf 7,tF1,4) | 2 => (rawOf 15,tF2,5) | 3 => (rawOf 15,tF3,5) | 4 => (rawOf 15,tF4,5) | 5 => (rawOf 15,tF5,5) | 6 => (rawOf 15,tF6,5) | _ => ([],0,0)
private theorem base6_s : ∀ k, k ≠ 0 → LowerBV (base6 k).1 (base6 k).2.1 (base6 k).2.2 := by
  intro k _; match k with
  | 1 => exact lowF1
  | 2 => exact lowF2
  | 3 => exact lowF3
  | 4 => exact lowF4
  | 5 => exact lowF5
  | 6 => exact lowF6
  | 0 | _ + 7 => exact fun _ _ _ _ => Nat.zero_le _
def fF7 : Forest := ⟨15,tF7,5,F7P,F7N,F7R,F7A,F7C,F7L,F7M⟩
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
theorem lowF7 : LowerBV (rawOf 15) tF7 6 :=
  lower_forest fF7 base6 base6_s F7v F7lv (by decide +kernel)
def base7 : Nat → List Sig × Sig × Nat | 1 => (rawOf 7,tF1,4) | 2 => (rawOf 15,tF2,5) | 3 => (rawOf 15,tF3,5) | 4 => (rawOf 15,tF4,5) | 5 => (rawOf 15,tF5,5) | 6 => (rawOf 15,tF6,5) | 7 => (rawOf 15,tF7,6) | _ => ([],0,0)
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
def fF8 : Forest := ⟨15,tF8,6,F8P,F8N,F8R,F8A,F8C,F8L,F8M⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F8v : graphValid fF8 base7 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F8k3 : ok fF8 3 F8T3 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F8k4 : ok fF8 4 F8T4 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F8k5 : ok fF8 5 F8T5 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F8k6 : ok fF8 6 F8T6 := by decide +kernel
private theorem F8lv : levelsChecked fF8 := by
  intro k hk tree ht; change k ≤ 6 at hk; interval_cases k
  all_goals simp [fF8,F8L] at ht
  · subst ht; exact F8k3
  · subst ht; exact F8k4
  · subst ht; exact F8k5
  · subst ht; exact F8k6
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowF8 : LowerBV (rawOf 15) tF8 7 :=
  lower_forest fF8 base7 base7_s F8v F8lv (by decide +kernel)
def base8 : Nat → List Sig × Sig × Nat | 1 => (rawOf 7,tF1,4) | 2 => (rawOf 15,tF2,5) | 3 => (rawOf 15,tF3,5) | 4 => (rawOf 15,tF4,5) | 5 => (rawOf 15,tF5,5) | 6 => (rawOf 15,tF6,5) | 7 => (rawOf 15,tF7,6) | 8 => (rawOf 15,tF8,7) | _ => ([],0,0)
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
def fF9 : Forest := ⟨15,tF9,6,F9P,F9N,F9R,F9A,F9C,F9L,F9M⟩
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
theorem lowF9 : LowerBV (rawOf 15) tF9 7 :=
  lower_forest fF9 base8 base8_s F9v F9lv (by decide +kernel)
def base9 : Nat → List Sig × Sig × Nat | 1 => (rawOf 7,tF1,4) | 2 => (rawOf 15,tF2,5) | 3 => (rawOf 15,tF3,5) | 4 => (rawOf 15,tF4,5) | 5 => (rawOf 15,tF5,5) | 6 => (rawOf 15,tF6,5) | 7 => (rawOf 15,tF7,6) | 8 => (rawOf 15,tF8,7) | 9 => (rawOf 15,tF9,7) | _ => ([],0,0)
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
def fF10 : Forest := ⟨31,tF10,6,F10P,F10N,F10R,F10A,F10C,F10L,F10M⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F10v : graphValid fF10 base9 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F10k6 : ok fF10 6 F10T6 := by decide +kernel
private theorem F10lv : levelsChecked fF10 := by
  intro k hk tree ht; change k ≤ 6 at hk; interval_cases k
  all_goals simp [fF10,F10L] at ht
  subst ht; exact F10k6
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowF10 : LowerBV (rawOf 31) tF10 7 :=
  lower_forest fF10 base9 base9_s F10v F10lv (by decide +kernel)
def base10 : Nat → List Sig × Sig × Nat | 1 => (rawOf 7,tF1,4) | 2 => (rawOf 15,tF2,5) | 3 => (rawOf 15,tF3,5) | 4 => (rawOf 15,tF4,5) | 5 => (rawOf 15,tF5,5) | 6 => (rawOf 15,tF6,5) | 7 => (rawOf 15,tF7,6) | 8 => (rawOf 15,tF8,7) | 9 => (rawOf 15,tF9,7) | 10 => (rawOf 31,tF10,7) | _ => ([],0,0)
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
def fF11 : Forest := ⟨31,tF11,7,F11P,F11N,F11R,F11A,F11C,F11L,F11M⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F11v : graphValid fF11 base10 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F11k7 : ok fF11 7 F11T7 := by decide +kernel
private theorem F11lv : levelsChecked fF11 := by
  intro k hk tree ht; change k ≤ 7 at hk; interval_cases k
  all_goals simp [fF11,F11L] at ht
  subst ht; exact F11k7
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowF11 : LowerBV (rawOf 31) tF11 8 :=
  lower_forest fF11 base10 base10_s F11v F11lv (by decide +kernel)
def base11 : Nat → List Sig × Sig × Nat | 1 => (rawOf 7,tF1,4) | 2 => (rawOf 15,tF2,5) | 3 => (rawOf 15,tF3,5) | 4 => (rawOf 15,tF4,5) | 5 => (rawOf 15,tF5,5) | 6 => (rawOf 15,tF6,5) | 7 => (rawOf 15,tF7,6) | 8 => (rawOf 15,tF8,7) | 9 => (rawOf 15,tF9,7) | 10 => (rawOf 31,tF10,7) | 11 => (rawOf 31,tF11,8) | _ => ([],0,0)
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
def fF12 : Forest := ⟨31,tF12,7,F12P,F12N,F12R,F12A,F12C,F12L,F12M⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F12v : graphValid fF12 base11 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F12k7 : ok fF12 7 F12T7 := by decide +kernel
private theorem F12lv : levelsChecked fF12 := by
  intro k hk tree ht; change k ≤ 7 at hk; interval_cases k
  all_goals simp [fF12,F12L] at ht
  subst ht; exact F12k7
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowF12 : LowerBV (rawOf 31) tF12 8 :=
  lower_forest fF12 base11 base11_s F12v F12lv (by decide +kernel)
def base12 : Nat → List Sig × Sig × Nat | 1 => (rawOf 7,tF1,4) | 2 => (rawOf 15,tF2,5) | 3 => (rawOf 15,tF3,5) | 4 => (rawOf 15,tF4,5) | 5 => (rawOf 15,tF5,5) | 6 => (rawOf 15,tF6,5) | 7 => (rawOf 15,tF7,6) | 8 => (rawOf 15,tF8,7) | 9 => (rawOf 15,tF9,7) | 10 => (rawOf 31,tF10,7) | 11 => (rawOf 31,tF11,8) | 12 => (rawOf 31,tF12,8) | _ => ([],0,0)
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
def fF13 : Forest := ⟨31,tF13,7,F13P,F13N,F13R,F13A,F13C,F13L,F13M⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F13v : graphValid fF13 base12 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F13k7 : ok fF13 7 F13T7 := by decide +kernel
private theorem F13lv : levelsChecked fF13 := by
  intro k hk tree ht; change k ≤ 7 at hk; interval_cases k
  all_goals simp [fF13,F13L] at ht
  subst ht; exact F13k7
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowF13 : LowerBV (rawOf 31) tF13 8 :=
  lower_forest fF13 base12 base12_s F13v F13lv (by decide +kernel)
def base13 : Nat → List Sig × Sig × Nat | 1 => (rawOf 7,tF1,4) | 2 => (rawOf 15,tF2,5) | 3 => (rawOf 15,tF3,5) | 4 => (rawOf 15,tF4,5) | 5 => (rawOf 15,tF5,5) | 6 => (rawOf 15,tF6,5) | 7 => (rawOf 15,tF7,6) | 8 => (rawOf 15,tF8,7) | 9 => (rawOf 15,tF9,7) | 10 => (rawOf 31,tF10,7) | 11 => (rawOf 31,tF11,8) | 12 => (rawOf 31,tF12,8) | 13 => (rawOf 31,tF13,8) | _ => ([],0,0)
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
def fF14 : Forest := ⟨31,tF14,7,F14P,F14N,F14R,F14A,F14C,F14L,F14M⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F14v : graphValid fF14 base13 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F14k7 : ok fF14 7 F14T7 := by decide +kernel
private theorem F14lv : levelsChecked fF14 := by
  intro k hk tree ht; change k ≤ 7 at hk; interval_cases k
  all_goals simp [fF14,F14L] at ht
  subst ht; exact F14k7
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowF14 : LowerBV (rawOf 31) tF14 8 :=
  lower_forest fF14 base13 base13_s F14v F14lv (by decide +kernel)
def base14 : Nat → List Sig × Sig × Nat | 1 => (rawOf 7,tF1,4) | 2 => (rawOf 15,tF2,5) | 3 => (rawOf 15,tF3,5) | 4 => (rawOf 15,tF4,5) | 5 => (rawOf 15,tF5,5) | 6 => (rawOf 15,tF6,5) | 7 => (rawOf 15,tF7,6) | 8 => (rawOf 15,tF8,7) | 9 => (rawOf 15,tF9,7) | 10 => (rawOf 31,tF10,7) | 11 => (rawOf 31,tF11,8) | 12 => (rawOf 31,tF12,8) | 13 => (rawOf 31,tF13,8) | 14 => (rawOf 31,tF14,8) | _ => ([],0,0)
private theorem base14_s : ∀ k, k ≠ 0 → LowerBV (base14 k).1 (base14 k).2.1 (base14 k).2.2 := by
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
  | 14 => exact lowF14
  | 0 | _ + 15 => exact fun _ _ _ _ => Nat.zero_le _
def fF15 : Forest := ⟨31,tF15,8,F15P,F15N,F15R,F15A,F15C,F15L,F15M⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F15v : graphValid fF15 base14 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F15k2 : ok fF15 2 F15T2 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F15k3 : ok fF15 3 F15T3 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F15k4 : ok fF15 4 F15T4 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F15k5 : ok fF15 5 F15T5 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F15k6 : ok fF15 6 F15T6 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F15k7 : ok fF15 7 F15T7 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F15k8 : ok fF15 8 F15T8 := by decide +kernel
private theorem F15lv : levelsChecked fF15 := by
  intro k hk tree ht; change k ≤ 8 at hk; interval_cases k
  all_goals simp [fF15,F15L] at ht
  · subst ht; exact F15k2
  · subst ht; exact F15k3
  · subst ht; exact F15k4
  · subst ht; exact F15k5
  · subst ht; exact F15k6
  · subst ht; exact F15k7
  · subst ht; exact F15k8
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowF15 : LowerBV (rawOf 31) tF15 9 :=
  lower_forest fF15 base14 base14_s F15v F15lv (by decide +kernel)
def base15 : Nat → List Sig × Sig × Nat | 1 => (rawOf 7,tF1,4) | 2 => (rawOf 15,tF2,5) | 3 => (rawOf 15,tF3,5) | 4 => (rawOf 15,tF4,5) | 5 => (rawOf 15,tF5,5) | 6 => (rawOf 15,tF6,5) | 7 => (rawOf 15,tF7,6) | 8 => (rawOf 15,tF8,7) | 9 => (rawOf 15,tF9,7) | 10 => (rawOf 31,tF10,7) | 11 => (rawOf 31,tF11,8) | 12 => (rawOf 31,tF12,8) | 13 => (rawOf 31,tF13,8) | 14 => (rawOf 31,tF14,8) | 15 => (rawOf 31,tF15,9) | _ => ([],0,0)
private theorem base15_s : ∀ k, k ≠ 0 → LowerBV (base15 k).1 (base15 k).2.1 (base15 k).2.2 := by
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
  | 14 => exact lowF14
  | 15 => exact lowF15
  | 0 | _ + 16 => exact fun _ _ _ _ => Nat.zero_le _
def fF16 : Forest := ⟨31,tF16,9,F16P,F16N,F16R,F16A,F16C,F16L,F16M⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F16v : graphValid fF16 base15 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F16k3 : ok fF16 3 F16T3 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F16k4 : ok fF16 4 F16T4 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F16k5_0 : ok fF16 5 F16T5_0 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F16k5_1 : ok fF16 5 F16T5_1 := by decide +kernel
private theorem F16k5 : ok fF16 5 F16T5 := by
  simp only [ok,F16T5,nd,BTree.all,F16k5_0,F16k5_1,Bool.and_true]
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F16k6 : ok fF16 6 F16T6 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F16k7 : ok fF16 7 F16T7 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F16k8 : ok fF16 8 F16T8 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F16k9 : ok fF16 9 F16T9 := by decide +kernel
private theorem F16lv : levelsChecked fF16 := by
  intro k hk tree ht; change k ≤ 9 at hk; interval_cases k
  all_goals simp [fF16,F16L] at ht
  · subst ht; exact F16k3
  · subst ht; exact F16k4
  · subst ht; exact F16k5
  · subst ht; exact F16k6
  · subst ht; exact F16k7
  · subst ht; exact F16k8
  · subst ht; exact F16k9
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowF16 : LowerBV (rawOf 31) tF16 10 :=
  lower_forest fF16 base15 base15_s F16v F16lv (by decide +kernel)
def base16 : Nat → List Sig × Sig × Nat | 1 => (rawOf 7,tF1,4) | 2 => (rawOf 15,tF2,5) | 3 => (rawOf 15,tF3,5) | 4 => (rawOf 15,tF4,5) | 5 => (rawOf 15,tF5,5) | 6 => (rawOf 15,tF6,5) | 7 => (rawOf 15,tF7,6) | 8 => (rawOf 15,tF8,7) | 9 => (rawOf 15,tF9,7) | 10 => (rawOf 31,tF10,7) | 11 => (rawOf 31,tF11,8) | 12 => (rawOf 31,tF12,8) | 13 => (rawOf 31,tF13,8) | 14 => (rawOf 31,tF14,8) | 15 => (rawOf 31,tF15,9) | 16 => (rawOf 31,tF16,10) | _ => ([],0,0)
private theorem base16_s : ∀ k, k ≠ 0 → LowerBV (base16 k).1 (base16 k).2.1 (base16 k).2.2 := by
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
  | 14 => exact lowF14
  | 15 => exact lowF15
  | 16 => exact lowF16
  | 0 | _ + 17 => exact fun _ _ _ _ => Nat.zero_le _
def fF17 : Forest := ⟨31,tF17,9,F17P,F17N,F17R,F17A,F17C,F17L,F17M⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F17v : graphValid fF17 base16 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F17k9 : ok fF17 9 F17T9 := by decide +kernel
private theorem F17lv : levelsChecked fF17 := by
  intro k hk tree ht; change k ≤ 9 at hk; interval_cases k
  all_goals simp [fF17,F17L] at ht
  subst ht; exact F17k9
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowF17 : LowerBV (rawOf 31) tF17 10 :=
  lower_forest fF17 base16 base16_s F17v F17lv (by decide +kernel)
def base17 : Nat → List Sig × Sig × Nat | 1 => (rawOf 7,tF1,4) | 2 => (rawOf 15,tF2,5) | 3 => (rawOf 15,tF3,5) | 4 => (rawOf 15,tF4,5) | 5 => (rawOf 15,tF5,5) | 6 => (rawOf 15,tF6,5) | 7 => (rawOf 15,tF7,6) | 8 => (rawOf 15,tF8,7) | 9 => (rawOf 15,tF9,7) | 10 => (rawOf 31,tF10,7) | 11 => (rawOf 31,tF11,8) | 12 => (rawOf 31,tF12,8) | 13 => (rawOf 31,tF13,8) | 14 => (rawOf 31,tF14,8) | 15 => (rawOf 31,tF15,9) | 16 => (rawOf 31,tF16,10) | 17 => (rawOf 31,tF17,10) | _ => ([],0,0)
private theorem base17_s : ∀ k, k ≠ 0 → LowerBV (base17 k).1 (base17 k).2.1 (base17 k).2.2 := by
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
  | 14 => exact lowF14
  | 15 => exact lowF15
  | 16 => exact lowF16
  | 17 => exact lowF17
  | 0 | _ + 18 => exact fun _ _ _ _ => Nat.zero_le _
def fRt : Forest := ⟨63,tRt,11,RtP,RtN,RtR,RtA,RtC,RtL,RtM⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtv : graphValid fRt base17 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk3 : ok fRt 3 RtT3 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk4 : ok fRt 4 RtT4 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk5 : ok fRt 5 RtT5 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk6 : ok fRt 6 RtT6 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk7 : ok fRt 7 RtT7 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk8_0 : ok fRt 8 RtT8_0 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk8_1 : ok fRt 8 RtT8_1 := by decide +kernel
private theorem Rtk8 : ok fRt 8 RtT8 := by
  simp only [ok,RtT8,nd,BTree.all,Rtk8_0,Rtk8_1,Bool.and_true]
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk9 : ok fRt 9 RtT9 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk10 : ok fRt 10 RtT10 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk11 : ok fRt 11 RtT11 := by decide +kernel
private theorem Rtlv : levelsChecked fRt := by
  intro k hk tree ht; change k ≤ 11 at hk; interval_cases k
  all_goals simp [fRt,RtL] at ht
  · subst ht; exact Rtk3
  · subst ht; exact Rtk4
  · subst ht; exact Rtk5
  · subst ht; exact Rtk6
  · subst ht; exact Rtk7
  · subst ht; exact Rtk8
  · subst ht; exact Rtk9
  · subst ht; exact Rtk10
  · subst ht; exact Rtk11
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowRt : LowerBV (rawOf 63) tRt 12 :=
  lower_forest fRt base17 base17_s Rtv Rtlv (by decide +kernel)
end CertVerify

def targetFun (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4276676736 * 2 ^ 32 + 4261445632) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def smallCircuit : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [3, 7]⟩, ⟨.or, [4, 8]⟩, ⟨.and, [3, 11]⟩, ⟨.and, [5, 7]⟩, ⟨.and, [9, 11]⟩, ⟨.and, [9, 13]⟩, ⟨.or, [10, 14]⟩, ⟨.or, [12, 15]⟩, ⟨.and, [16, 17]⟩], 18⟩

private theorem witnessMonotone : Monotone2 smallCircuit := by
  intro g hg
  simp only [smallCircuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl, by decide⟩ | exact ⟨Or.inr rfl, by decide⟩

def idx6 (x : Fin 6 → Bool) : Nat :=
  (if x 0 then 1 else 0) + (if x 1 then 2 else 0) + (if x 2 then 4 else 0) +
  (if x 3 then 8 else 0) + (if x 4 then 16 else 0) + (if x 5 then 32 else 0)
private theorem sum_fin6 (x : Fin 6 → Bool) :
    (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) = idx6 x := by
  simp [Fin.sum_univ_six, idx6]
private theorem witnessCorrectFast : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    smallCircuit.eval [b0, b1, b2, b3, b4, b5] =
    Nat.testBit (4276676736 * 2 ^ 32 + 4261445632)
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
private theorem sample6_targetFast : ∀ r : Row, Nat.testBit (4276676736 * 2 ^ 32 + 4261445632) (idx6 (sample6 r)) = bitBV r tRt := by decide +kernel
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
  by_cases big : 13 ≤ C.size
  · have hsc : smallCircuit.size = 13 := rfl
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

end PEqualNP.Outside.L_meta_12122

open PEqualNP.Outside.L_meta_12122 in
theorem PEqualNP.Outside.L_meta_12122 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676736 * 2 ^ 32 + 4261445632) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676736 * 2 ^ 32 + 4261445632) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  mainProof
