import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10908

open PEqualNP.CircuitLowerBounds

abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r

def comb {R} (d : Nat) (a b : Wire R) : Wire R :=
  if d = 0 then combine false a b else if d = 1 then combine true a b else
    if d = 2 then combine false a (inv b) else combine false (inv a) b

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

theorem Reach.two {R} {roots : List (Wire R)} {p bank a b} (op : Bool) (h : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) :
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

def kept {α : Type} (save : Bool) (x : α) (xs : List α) : List α :=
  if save then x :: xs else xs

def Run {R} (goal : Wire R) : Nat → List (Wire R) → Prop
  | 0, zs => List.Perm [goal] zs
  | s + 1, zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire R) (rest : List (Wire R)),
      op < 4 ∧ (a :: b :: rest).Perm zs ∧ Run goal s (comb op a b :: kept ka a (kept kb b rest))

theorem Run.stop {R} {goal : Wire R} : Run goal 0 [goal] := List.Perm.refl _

theorem Run.perm {R} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run goal s xs) : Run goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s => obtain ⟨op, ka, kb, a, b, rest, hd, q, h⟩ := h; exact ⟨op, ka, kb, a, b, rest, hd, q.trans p, h⟩

theorem Run.two {R} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)}
    (op : Nat) (hd : op < 4) (ka kb : Bool)
    (h : Run goal s (comb op a b :: kept ka a (kept kb b rest))) :
    Run goal (s + 1) (a :: b :: rest) :=
  ⟨op, ka, kb, a, b, rest, hd, List.Perm.refl _, h⟩

theorem Run.ind {R} {goal : Wire R} {motive : ∀ s ws, Run goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run goal s xs), motive s xs h → motive s zs (Run.perm p h))
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
  have : Constant (inv a) ↔ Constant a := ⟨fun h => inv_inv' a ▸ inv_constant h, inv_constant⟩
  by_cases h : Constant a <;> simp [cost, h, this]
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
  rcases h with ⟨v, rfl⟩ | ⟨v, rfl⟩ <;> cases op <;> cases v
  · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
  · simpa [combine] using hb
  · simpa [combine] using hb
  · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)
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

theorem comb_prime {R} {bank : List (Wire R)} {d a b} (hd : d < 4)
    (ha : Available bank a) (hb : Available bank b) :
    ∃ op x y, comb d a b = combine op x y ∧ Available bank x ∧ Available bank y ∧
      cost x = cost a ∧ cost y = cost b := by
  have : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl
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

-- Parametric BitVec n signal layer (used for n = 64 and n = 128)
section BV
variable {N : Nat}

def bvZero : BitVec N := 0
def bvOne : BitVec N := BitVec.allOnes N
def bvNeg (a : BitVec N) : BitVec N := ~~~a
def bvBin (d : Nat) (a b : BitVec N) : BitVec N :=
  if d = 0 then a &&& b else if d = 1 then a ||| b else if d = 2 then a &&& ~~~b else ~~~a &&& b
def bvProper (a : BitVec N) : Prop := a ≠ bvZero ∧ a ≠ bvOne
def bvBit (i : Fin N) (a : BitVec N) : Bool := a.getLsbD i.val
def bvFlipOp (d : Nat) : Nat := if d = 2 then 3 else if d = 3 then 2 else d

theorem bvBit_zero (i : Fin N) : bvBit i (bvZero (N := N)) = false := by simp [bvBit, bvZero]
theorem bvBit_one (i : Fin N) : bvBit i (bvOne (N := N)) = true := by
  unfold bvBit bvOne; rw [BitVec.getLsbD_allOnes]; simp
theorem bvBit_neg (i : Fin N) (a : BitVec N) : bvBit i (bvNeg a) = !(bvBit i a) := by
  simp [bvBit, bvNeg, i.isLt]
theorem bvBit_bin (i : Fin N) (d : Nat) (a b : BitVec N) : bvBit i (bvBin d a b) =
    (if d = 0 then bvBit i a && bvBit i b else if d = 1 then bvBit i a || bvBit i b else
      if d = 2 then bvBit i a && !(bvBit i b) else !(bvBit i a) && bvBit i b) := by
  unfold bvBin; split_ifs <;> simp [bvBit]
theorem bvBit_ext {a b : BitVec N} (h : ∀ i : Fin N, bvBit i a = bvBit i b) : a = b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j, hj⟩

theorem bvBin_flip {d : Nat} (hd : d < 4) (a b : BitVec N) :
    bvBin d a b = bvBin (bvFlipOp d) b a := by
  have : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;>
    simp [bvBin, bvFlipOp, BitVec.and_comm, BitVec.or_comm]

theorem bvFlip_ok {d : Nat} (hd : d < 4) : bvFlipOp d < 4 ∧ bvFlipOp (bvFlipOp d) = d := by
  have : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;> simp [bvFlipOp]

def bvLive (target : BitVec N) : Nat → Finset (BitVec N) → Prop
  | 0, S => S = {target} ∧ bvProper target
  | k + 1, S => ∃ (U : Finset (BitVec N)) (a b : BitVec N) (d : Nat),
      d < 4 ∧ S = insert a (insert b U) ∧ bvProper a ∧ bvProper b ∧ a ≠ b ∧
      bvBin d a b ∉ insert a (insert b U) ∧ bvLive target k (insert (bvBin d a b) U)

theorem bvLive.stop {target : BitVec N} (hp : bvProper target) : bvLive target 0 {target} := ⟨rfl, hp⟩
theorem bvLive.binary {target : BitVec N} {k : Nat} {U : Finset (BitVec N)} {a b : BitVec N} {d : Nat}
    (hd : d < 4) (ha : bvProper a) (hb : bvProper b) (hab : a ≠ b)
    (hfresh : bvBin d a b ∉ insert a (insert b U)) (tail : bvLive target k (insert (bvBin d a b) U)) :
    bvLive target (k + 1) (insert a (insert b U)) :=
  ⟨U, a, b, d, hd, rfl, ha, hb, hab, hfresh, tail⟩

theorem bvLive.ind {target : BitVec N} {motive : ∀ (k : Nat) (S : Finset (BitVec N)), bvLive target k S → Prop}
    (stop : ∀ (hp : bvProper target), motive 0 {target} (bvLive.stop hp))
    (binary : ∀ {k : Nat} {U : Finset (BitVec N)} {a b : BitVec N} {d : Nat} (hd : d < 4)
      (ha : bvProper a) (hb : bvProper b) (hab : a ≠ b)
      (hfresh : bvBin d a b ∉ insert a (insert b U)) (tail : bvLive target k (insert (bvBin d a b) U)),
      motive k (insert (bvBin d a b) U) tail →
      motive (k + 1) (insert a (insert b U)) (bvLive.binary hd ha hb hab hfresh tail))
    {k : Nat} {S : Finset (BitVec N)} (h : bvLive target k S) : motive k S h := by
  induction k generalizing S with
  | zero => obtain ⟨rfl, hp⟩ := h; exact stop hp
  | succ k ih => obtain ⟨U, a, b, d, hd, rfl, ha, hb, hab, hf, tail⟩ := h; exact binary hd ha hb hab hf tail (ih tail)

theorem bvLive_proper {target : BitVec N} {k S} (h : bvLive target k S) : ∀ a ∈ S, bvProper a := by
  induction h using bvLive.ind with
  | stop hp => simpa using hp
  | binary _ ha hb _ _ _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha, hb, fun a h => ih a (Finset.mem_insert_of_mem h)⟩

theorem bvLive_size {target : BitVec N} {k S} (h : bvLive target k S) : S.card ≤ k + 1 := by
  induction h using bvLive.ind with
  | stop _ => simp
  | @binary k U a b d _ _ _ _ hf _ ih =>
    have hu : bvBin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

def bvObs (a : BitVec N) : Wire (Fin N) := fun r => bvBit r a
def bvTab (f : Wire (Fin N)) : BitVec N :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn

theorem bvBit_tab (f : Wire (Fin N)) (r : Fin N) : bvBit r (bvTab f) = f r := by
  simp only [bvBit, bvTab, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [r.isLt]
theorem bvTab_obs (v : BitVec N) : bvTab (bvObs v) = v :=
  bvBit_ext fun r => bvBit_tab (bvObs v) r
theorem bvObs_tab (f : Wire (Fin N)) : bvObs (bvTab f) = f := funext (bvBit_tab f)
theorem bvObs_neg (a : BitVec N) : bvObs (bvNeg a) = inv (bvObs a) := funext fun r => bvBit_neg r a
theorem bvObs_bin (d : Nat) (a b : BitVec N) : bvObs (bvBin d a b) = comb d (bvObs a) (bvObs b) := by
  funext r; simp only [bvObs, bvBit_bin, comb]; split_ifs <;> rfl

theorem bvLive_row_diff {T : BitVec N} {k S} (h : bvLive T k S) {r s : Fin N}
    (diff : bvBit r T ≠ bvBit s T) : ∃ a ∈ S, bvBit r a ≠ bvBit s a := by
  induction h using bvLive.ind with
  | stop _ => exact ⟨_, by simp, diff⟩
  | @binary k U a b d _ _ _ _ _ _ ih =>
    obtain ⟨v, hv, hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bvBit r a = bvBit s a
      · refine ⟨b, by simp, fun beq => hd ?_⟩
        rw [bvBit_bin, bvBit_bin, aeq, beq]
      · exact ⟨a, by simp, aeq⟩
    · exact ⟨v, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu), hd⟩

theorem bvRaw_required {T : BitVec N} {k S} (h : bvLive T k S) (roots : List (BitVec N)) (a : BitVec N)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Fin N) (diff : bvBit r T ≠ bvBit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bvBit r v = bvBit s v) : a ∈ S := by
  obtain ⟨v, hv, hd⟩ := bvLive_row_diff h diff
  by_cases veq : v = a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl
theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept, hn, ha]
theorem kept_fin {α : Type} [DecidableEq α] (k : Bool) (a : α) (l : List α) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by cases k <;> simp [kept]

theorem bvList_run {T : BitVec N} {k S} (h : bvLive T k S) (v : List (BitVec N))
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run (bvObs T) k (v.map bvObs) := by
  classical
  induction h using bvLive.ind generalizing v with
  | stop _ =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv; simpa [eqv]
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
    have hf : bvBin d a b ∉ tail := fun hz =>
      fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bvBin d a b :: tail) (List.nodup_cons.mpr ⟨hf, nd⟩) (by simp [ht])
    change Run _ _ ((bvBin d a b :: kept ka a (kept kb b rest)).map bvObs) at progress
    rw [List.map_cons, map_kept, map_kept, bvObs_bin] at progress
    have perm : (a :: b :: rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab, ar, br, hr]) hv
      ext j; by_cases ja : j = a <;> by_cases jb : j = b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d hd ka kb progress)

-- Normalization (requires N > 0)
def bvNrm [NeZero N] (a : BitVec N) : BitVec N :=
  if bvBit (0 : Fin N) a then bvNeg a else a

theorem bvNrm_bit [NeZero N] (a : BitVec N) : bvBit (0 : Fin N) (bvNrm a) = false := by
  unfold bvNrm; cases h : bvBit (0 : Fin N) a <;> simp [h, bvBit_neg]
theorem bvNrm_id [NeZero N] {a : BitVec N} (h : bvBit (0 : Fin N) a = false) : bvNrm a = a := by
  unfold bvNrm; simp [h]
theorem bvNeg_neg (a : BitVec N) : bvNeg (bvNeg a) = a := by simp [bvNeg]
theorem bvNrm_neg [NeZero N] (a : BitVec N) : bvNrm (bvNeg a) = bvNrm a := by
  unfold bvNrm; cases h : bvBit (0 : Fin N) a <;> simp [h, bvBit_neg, bvNeg_neg]
theorem bvProper_neg {a : BitVec N} (h : bvProper (bvNeg a)) : bvProper a := by
  refine ⟨?_, ?_⟩
  · rintro rfl; exact h.2 (by simp [bvNeg, bvZero, bvOne])
  · rintro rfl; exact h.1 (by simp [bvNeg, bvZero, bvOne])
theorem bvProper_nrm [NeZero N] {a : BitVec N} (h : bvProper (bvNrm a)) : bvProper a := by
  unfold bvNrm at h; split at h
  · exact bvProper_neg h
  · exact h
theorem bvNrm_ne_one [NeZero N] (a : BitVec N) : bvNrm a ≠ bvOne := by
  intro h; have := bvNrm_bit a; rw [h, bvBit_one] at this; exact Bool.noConfusion this

def bvPrime (d : Bool) (a b : BitVec N) : BitVec N := if d then a ||| b else a &&& b
theorem bvBit_prime (i : Fin N) (d : Bool) (a b : BitVec N) :
    bvBit i (bvPrime d a b) = (if d then bvBit i a || bvBit i b else bvBit i a && bvBit i b) := by
  cases d <;> simp [bvPrime, bvBit]

theorem bvNrm_prime [NeZero N] (d : Bool) (a b : BitVec N) :
    ∃ e, e < 4 ∧ bvNrm (bvPrime d a b) = bvBin e (bvNrm a) (bvNrm b) := by
  refine ⟨if d then (if bvBit (0 : Fin N) a then (if bvBit (0 : Fin N) b then 0 else 2)
            else (if bvBit (0 : Fin N) b then 3 else 1))
          else (if bvBit (0 : Fin N) a then (if bvBit (0 : Fin N) b then 1 else 3)
            else (if bvBit (0 : Fin N) b then 2 else 0)), ?_, ?_⟩
  · split_ifs <;> omega
  · apply bvBit_ext; intro i
    cases d <;> cases ha : bvBit (0 : Fin N) a <;> cases hb : bvBit (0 : Fin N) b <;>
      simp only [bvNrm, bvBit_prime, ha, hb, bvBit_bin, bvBit_neg,
        Bool.and_true, Bool.and_false, Bool.or_false, Bool.or_true,
        Bool.false_eq_true, ite_true, ite_false] <;>
      cases hx : bvBit i a <;> cases hy : bvBit i b <;> simp

def bvRep (w : List (BitVec N)) (v : BitVec N) : Prop := v ∈ w ∨ ¬bvProper v
def bvRepr [NeZero N] (w : List (BitVec N)) (v : BitVec N) : Prop := bvRep w (bvNrm v)
def bvWit (w : List (BitVec N)) (z : BitVec N) : Prop :=
  ∃ d a b, d < 4 ∧ a ∈ w ∧ b ∈ w ∧ bvProper a ∧ bvProper b ∧ a ≠ b ∧ z = bvBin d a b

private lemma bvBin_laws (a : BitVec N) :
    bvBin 0 a bvOne = a ∧ bvBin 1 a bvZero = a ∧
    bvBin 0 a bvZero = bvZero ∧ bvBin 1 a bvOne = bvOne ∧
    bvBin 0 a a = a ∧ bvBin 1 a a = a ∧ bvBin 2 a a = bvZero ∧ bvBin 3 a a = bvZero ∧
    bvBin 2 a bvZero = a ∧ bvBin 3 bvZero a = a ∧ bvBin 2 bvZero a = bvZero ∧ bvBin 3 a bvZero = bvZero ∧
    bvBin 0 bvZero a = bvZero ∧ bvBin 1 bvZero a = a ∧ bvBin 0 bvOne a = a ∧ bvBin 1 bvOne a = bvOne := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply bvBit_ext <;> intro i <;>
    simp [bvBit_bin, bvBit_zero, bvBit_one]

private lemma bvOperand_cases {w : List (BitVec N)} {a : BitVec N} (h : bvRep w a) :
    a = bvZero ∨ a = bvOne ∨ a ∈ w ∧ bvProper a := by
  by_cases hz : a = bvZero; · exact Or.inl hz
  by_cases ho : a = bvOne; · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz, ho⟩), hz, ho⟩)

private lemma bvBin_rep {w : List (BitVec N)} {a b : BitVec N} (d : Nat) (hd : d < 4)
    (ha : bvRep w a) (hb : bvRep w b) (no : a ≠ bvOne ∧ b ≠ bvOne) :
    bvRep w (bvBin d a b) ∨ bvWit w (bvBin d a b) := by
  have rz : bvRep w bvZero := Or.inr fun h => h.1 rfl
  have ro : bvRep w bvOne := Or.inr fun h => h.2 rfl
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := bvBin_laws a
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := bvBin_laws b
  have hd4 : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  by_cases he : a = b
  · subst b; left
    rcases hd4 with rfl | rfl | rfl | rfl
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases bvOperand_cases ha with rfl | rfl | ⟨ham, hap⟩
  · left
    rcases hd4 with rfl | rfl | rfl | rfl
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · exact absurd rfl no.1
  rcases bvOperand_cases hb with rfl | rfl | ⟨hbm, hbp⟩
  · left
    rcases hd4 with rfl | rfl | rfl | rfl
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · exact absurd rfl no.2
  exact Or.inr ⟨d, a, b, hd, ham, hbm, hap, hbp, he, rfl⟩

theorem bvPrime_rep [NeZero N] {w : List (BitVec N)} {a b : BitVec N} (d : Bool)
    (ha : bvRepr w a) (hb : bvRepr w b) :
    bvRepr w (bvPrime d a b) ∨ bvWit w (bvNrm (bvPrime d a b)) := by
  obtain ⟨e, he, eq⟩ := bvNrm_prime d a b
  unfold bvRepr; rw [eq]
  exact bvBin_rep e he ha hb ⟨bvNrm_ne_one a, bvNrm_ne_one b⟩

theorem bvRepr_const [NeZero N] {w : List (BitVec N)} {v : BitVec N} (h : v = bvZero ∨ v = bvOne) :
    bvRepr w v := by
  refine Or.inr fun hp => ?_
  have := bvProper_nrm hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl

theorem bvGet_rep [NeZero N] (w : List (BitVec N)) (i : Nat) :
    bvRepr (w.map bvNrm) (w.getD i bvZero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact bvRepr_const (Or.inl rfl)
  | some a => exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))

theorem bvRepr_neg [NeZero N] {w : List (BitVec N)} {a : BitVec N} (h : bvRepr w a) :
    bvRepr w (bvNeg a) := by unfold bvRepr; rwa [bvNrm_neg]

def isNot (g : Gate) : Bool := match g.op with | .not => true | _ => false

def bvGv (w : List (BitVec N)) (g : Gate) : BitVec N :=
  let xs := g.inputs.map fun i => w.getD i bvZero
  match g.op with
  | .and => xs.foldr (bvPrime false) bvOne
  | .or => xs.foldr (bvPrime true) bvZero
  | .not => bvNeg (xs.headD bvZero)
  | _ => bvZero

def bvExec (gs : List Gate) (w : List (BitVec N)) : List (BitVec N) :=
  gs.foldl (fun l g => l ++ [bvGv l g]) w

private lemma bvGate_rep [NeZero N] (w : List (BitVec N)) (g : Gate)
    (h : (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) :
    bvRepr (w.map bvNrm) (bvGv w g) ∨ (isNot g = false ∧ bvWit (w.map bvNrm) (bvNrm (bvGv w g))) := by
  obtain ⟨o, l⟩ := g
  obtain ⟨ho, hl⟩ := h
  have prim (d : Bool) : bvRepr (w.map bvNrm) ((l.map fun i => w.getD i bvZero).foldr (bvPrime d) (if d then bvZero else bvOne)) ∨
      bvWit (w.map bvNrm) (bvNrm ((l.map fun i => w.getD i bvZero).foldr (bvPrime d) (if d then bvZero else bvOne))) := by
    have unit (v : BitVec N) : bvPrime d v (if d then bvZero else bvOne) = v := by
      apply bvBit_ext; intro i; cases d <;> simp [bvBit_prime, bvBit_zero, bvBit_one]
    cases l with
    | nil => exact Or.inl (bvRepr_const (by cases d <;> simp))
    | cons i l =>
      cases l with
      | nil => simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, unit]; exact Or.inl (bvGet_rep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil => simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, unit]; exact bvPrime_rep d (bvGet_rep w i) (bvGet_rep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id fun h => ⟨rfl, h⟩
  · exact (prim true).imp id fun h => ⟨rfl, h⟩
  · left
    cases l with
    | nil => exact bvRepr_const (Or.inr (by simp [bvGv, bvNeg, bvZero, bvOne]))
    | cons i l => exact bvRepr_neg (bvGet_rep w i)

private lemma bvPull_gate {target : BitVec N} {w : List (BitVec N)} {z : BitVec N} {k S c}
    (h : bvLive target k S) (hz : bvRep w z ∨ (c = 1 ∧ bvWit w z)) (sub : ∀ a ∈ S, a ∈ w ++ [z]) :
    ∃ k' S', k' ≤ k + c ∧ bvLive target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k, S, by omega, h, fun a ha => ?_⟩
      rcases (by simpa using sub a ha : a ∈ w ∨ a = z) with hu | rfl
      · exact hu
      · exact hw
    · have hp := bvLive_proper h z hm
      rcases hz with hr | ⟨rfl, d, a, b, hd, ha, hb, pa, pb, hab, eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bvBin d a b)
        have ht : bvLive target k (insert (bvBin d a b) U) := by simpa [U, Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := fun v hv => by
          obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hv; simpa [hne] using sub v hm
        have hf : bvBin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_, _, Nat.le_refl _, bvLive.binary hd pa pb hab hf ht, by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k, S, by omega, h, fun a ha => ?_⟩
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

theorem bvExtract [NeZero N] {target : BitVec N} (gs : List Gate) (w : List (BitVec N))
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hp : bvProper target) (hout : target ∈ (bvExec gs w).map bvNrm) :
    ∃ k S, k ≤ gs.countP (fun g => !isNot g) ∧ bvLive target k S ∧ ∀ a ∈ S, a ∈ w.map bvNrm := by
  induction gs generalizing w with
  | nil => exact ⟨0, {target}, by simp, bvLive.stop hp, by simpa [bvExec] using hout⟩
  | cons g gs ih =>
    obtain ⟨k, S, hk, ht, hs⟩ := ih (w ++ [bvGv w g]) (fun a ha => legal a (by simp [ha])) hout
    have rep := bvGate_rep w g (legal g (by simp))
    rw [List.map_append] at hs
    have rep' : bvRep (w.map bvNrm) (bvNrm (bvGv w g)) ∨
        ((if isNot g then 0 else 1) = 1 ∧ bvWit (w.map bvNrm) (bvNrm (bvGv w g))) :=
      rep.imp id fun h => ⟨by simp [h.1], h.2⟩
    obtain ⟨l, T, hl, hu, hT⟩ := bvPull_gate ht rep' hs
    refine ⟨l, T, ?_, hu, hT⟩
    rw [List.countP_cons]
    cases hn : isNot g <;> simp [hn] at hl ⊢ <;> omega

private lemma bvB_read (i : Fin N) (w : List (BitVec N)) (j : Nat) :
    (w.map (bvBit i)).getD j false = bvBit i (w.getD j bvZero) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[j]? with
  | none => exact (bvBit_zero i).symm
  | some a => rfl

private lemma bvRun_bit (i : Fin N) (g : Gate) (w : List (BitVec N))
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) :
    bvBit i (bvGv w g) = g.op.eval (g.inputs.map fun j => (w.map (bvBit i)).getD j false) := by
  obtain ⟨o, l⟩ := g
  simp only [bvB_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bvBit_one i
    | cons a l ih =>
      change bvBit i (bvPrime false _ _) = (_ && _)
      rw [bvBit_prime]; exact congrArg (fun x => bvBit i (w.getD a bvZero) && x) ih
  · induction l with
    | nil => exact bvBit_zero i
    | cons a l ih =>
      change bvBit i (bvPrime true _ _) = (_ || _)
      rw [bvBit_prime]; exact congrArg (fun x => bvBit i (w.getD a bvZero) || x) ih
  · cases l with
    | nil => change bvBit i (bvNeg bvZero) = !false; rw [bvBit_neg, bvBit_zero]
    | cons a l => exact bvBit_neg i _

theorem bvExec_bits (gs : List Gate) (i : Fin N) (w : List (BitVec N))
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) :
    (bvExec gs w).map (bvBit i) =
    gs.foldl (fun (l : List Bool) g => l ++ [g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bvBit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (bvExec gs (w ++ [bvGv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons, List.map_append, List.map_singleton, bvRun_bit i g w (hg g (by simp))]

theorem bvTable_inv (f : Wire (Fin N)) : bvTab (inv f) = bvNeg (bvTab f) := by
  rw [← bvTab_obs (bvNeg (bvTab f)), bvObs_neg, bvObs_tab]
theorem bvTable_prime (d : Bool) (f g : Wire (Fin N)) :
    bvTab (combine d f g) = bvPrime d (bvTab f) (bvTab g) := by
  apply bvBit_ext; intro r; rw [bvBit_tab, bvBit_prime, bvBit_tab, bvBit_tab]; cases d <;> rfl

theorem bvAvail_rep [NeZero N] {bank : List (Wire (Fin N))} {a} (h : Available bank a) :
    bvRepr ((bank.map bvTab).map bvNrm) (bvTab a) := by
  rcases h with hm | ⟨b, rfl⟩ | hm
  · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hm))
  · apply bvRepr_const
    cases b
    · exact Or.inl (bvBit_ext fun i => (bvBit_tab _ i).trans (bvBit_zero i).symm)
    · exact Or.inr (bvBit_ext fun i => (bvBit_tab _ i).trans (bvBit_one i).symm)
  · refine Or.inl ?_
    rw [← bvNrm_neg, ← bvTable_inv a]
    exact List.mem_map_of_mem (List.mem_map_of_mem hm)

theorem bvReach_live_sub [NeZero N] {roots : List (Wire (Fin N))} {p bank}
    (h : Reach roots p bank) {T k S} (run : bvLive T k S)
    (sub : ∀ a ∈ S, a ∈ (bank.map bvTab).map bvNrm) :
    ∃ l V, l ≤ p + k ∧ bvLive T l V ∧ ∀ a ∈ V, a ∈ (roots.map bvTab).map bvNrm := by
  induction h using Reach.ind generalizing k S with
  | start => exact ⟨k, S, by omega, run, sub⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons, List.map_cons, bvTable_prime] at sub
    have rep := bvPrime_rep d (bvAvail_rep ha) (bvAvail_rep hb)
    obtain ⟨k', S', hk, run', sub'⟩ := bvPull_gate (c := 1) run (rep.imp id fun h => ⟨rfl, h⟩)
      (fun a hm => by simpa [or_comm] using sub a hm)
    obtain ⟨l, V, hl, hr, hs⟩ := ih run' sub'
    exact ⟨l, V, by omega, hr, hs⟩

def bvPlain [NeZero N] (a : BitVec N) : Bool := !(bvBit (0 : Fin N) a)
theorem bvNrm_map [NeZero N] {w : List (BitVec N)} (h : w.all bvPlain = true) : w.map bvNrm = w := by
  have e : w.map bvNrm = w.map id := by
    apply List.map_congr_left; intro a ha
    exact bvNrm_id (by simpa [bvPlain] using List.all_eq_true.mp h a ha)
  rw [e, List.map_id]

theorem bvReach_live [NeZero N] {roots : List (BitVec N)} {p bank T}
    (hp : bvProper T) (nT : bvPlain T = true) (nR : roots.all bvPlain = true)
    (h : Reach (roots.map bvObs) p bank) (hit : Available bank (bvObs T)) :
    ∃ k S, k ≤ p ∧ bvLive T k S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := bvAvail_rep hit
  rw [bvTab_obs] at hm
  unfold bvRepr at hm
  rw [bvNrm_id (by simpa [bvPlain] using nT)] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l, V, hl, hr, hs⟩ := bvReach_live_sub h (bvLive.stop hp) (by simpa using mem)
  refine ⟨l, V, by omega, hr, ?_⟩
  have e : (roots.map bvObs).map bvTab = roots := by simp [List.map_map, Function.comp_def, bvTab_obs]
  rw [e, bvNrm_map nR] at hs
  exact hs

end BV

-- 6-vertex specialization (Sig = BitVec 64)
abbrev Sig := BitVec 64
abbrev Row := Fin 64
abbrev Bits := BitVec 128

def Impossible (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k ≤ cap, ¬bvLive T k S

def Lower (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map bvObs) p bank → Available bank (bvObs T) → L ≤ p

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bvBit r T ≠ bvBit s T ∧ ∀ v ∈ roots, v ≠ a → bvBit r v = bvBit s v

theorem obs_proper {v : Sig} (hv : bvProper v) : ¬Constant (bvObs v) := by
  rintro ⟨b, h⟩
  cases b
  · exact hv.1 (bvBit_ext fun i => (congrFun h i).trans (bvBit_zero i).symm)
  · exact hv.2 (bvBit_ext fun i => (congrFun h i).trans (bvBit_one i).symm)

theorem lower_impossible {roots : List Sig} {T : Sig} {L : Nat}
    (hp : bvProper T) (nT : bvPlain T = true) (nR : roots.all bvPlain = true)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible T L roots.toFinset) : Lower roots T (L + 1) := by
  intro p bank h ha
  obtain ⟨k, S, hk, run, hs⟩ := bvReach_live hp nT nR h ha
  have he : roots.toFinset = S := by
    ext a; rw [List.mem_toFinset]
    refine ⟨fun hm => ?_, hs a⟩
    obtain ⟨r, s, hd, iso⟩ := essential _ hm
    exact bvRaw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k (by omega) (he.symm ▸ run)

def Slice (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bvBit (f r) d = true) ∧
    (∀ a ∈ raw, Available (roots.map bvObs) (restrictRows f (bvObs a))) ∧
    ¬Constant (restrictRows f (bvObs T)) ∧
    ∀ p bank, Reach (roots.map bvObs) p bank → Available bank (restrictRows f (bvObs T)) → L ≤ p

def masked (d a : Sig) : Sig := a &&& d
def availableB (d : Sig) (pool : List Sig) (a : Sig) : Bool :=
  let m := masked d a
  m == bvZero || m == d || pool.any (fun v => masked d v == m || masked d v == (d ^^^ m))

theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bvBit (f r) d = true)
    (eq : masked d a = masked d b) : restrictRows f (bvObs a) = restrictRows f (bvObs b) := by
  funext r
  have h := congrArg (bvBit (f r)) eq
  change bvBit (f r) a = bvBit (f r) b
  simpa only [bvBit, masked, BitVec.getLsbD_and, show d.getLsbD (f r).val = true from dom r, Bool.and_true] using h

theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bvBit (f r) d = true)
    (eq : masked d a = bvZero) : restrictRows f (bvObs a) = fun _ => false := by
  funext r
  have h := congrArg (bvBit (f r)) eq
  change bvBit (f r) a = false
  rw [bvBit_zero] at h
  simpa only [bvBit, masked, BitVec.getLsbD_and, show d.getLsbD (f r).val = true from dom r, Bool.and_true] using h

theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bvBit (f r) d = true)
    (eq : masked d a = d) : restrictRows f (bvObs a) = fun _ => true := by
  funext r
  have h := congrArg (bvBit (f r)) eq
  change bvBit (f r) a = true
  rw [dom r] at h
  simpa only [bvBit, masked, BitVec.getLsbD_and, show d.getLsbD (f r).val = true from dom r, Bool.and_true] using h

theorem masked_comp (d x : Sig) : masked d (bvNeg x) = d ^^^ masked d x := by
  apply bvBit_ext; intro r
  simp only [masked, bvNeg, bvBit, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_xor, r.isLt, decide_true, Bool.true_and]
  cases d.getLsbD r.val <;> cases x.getLsbD r.val <;> rfl

def poolSupply (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) : Prop :=
  ∀ a ∈ pool, Available bank (restrictRows f (bvObs a))

theorem availableB_sound {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bvBit (f r) d = true) (supplyB : poolSupply f bank pool)
    (check : availableB d pool a = true) : Available bank (restrictRows f (bvObs a)) := by
  simp only [availableB, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at check
  rcases check with (hz | ho) | ⟨v, hv, he | he⟩
  · exact Or.inr (Or.inl ⟨false, masked_zero dom hz⟩)
  · exact Or.inr (Or.inl ⟨true, masked_one dom ho⟩)
  · exact masked_eq dom he.symm ▸ supplyB v hv
  · have he' : masked d (bvNeg a) = masked d v := by rw [masked_comp]; exact he.symm
    have h := avail_inv (masked_eq dom he' ▸ supplyB v hv)
    rw [bvObs_neg] at h
    have e : inv (restrictRows f (inv (bvObs a))) = restrictRows f (bvObs a) := by
      funext r; simp [inv, restrictRows]
    rwa [e] at h

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) : Sig := bvBin c.1 c.2.1 c.2.2
def choiceOK (d : Sig) (pool : List Sig) (c : Choice) : Bool :=
  decide (c.1 < 4) && availableB d pool c.2.1 && availableB d pool c.2.2

theorem pay_choice {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bvBit (f r) d = true) (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (c : Choice) (valid : choiceOK d pool c = true) :
    ∃ next, Reach roots (q + 1) next ∧ poolSupply f next (choiceVal c :: pool) := by
  simp only [choiceOK, Bool.and_eq_true, decide_eq_true_eq] at valid
  obtain ⟨op, x, y, e, hx, hy, _, _⟩ := comb_prime valid.1.1 (availableB_sound dom hs valid.1.2) (availableB_sound dom hs valid.2)
  refine ⟨_, Reach.two op hp hx hy, fun a hm => ?_⟩
  rcases List.mem_cons.mp hm with rfl | hm
  · rw [choiceVal, bvObs_bin, restrict_comb, e]; exact Or.inl (by simp)
  · exact available_cons _ (hs _ hm)

def makePool (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c :: cs => if choiceOK d pool c then makePool d (choiceVal c :: pool) cs else none

theorem makePool_sound {d : Sig} {f : Row → Row} (dom : ∀ r, bvBit (f r) d = true)
    {roots bank q pool} (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (cs : List Choice) {result} (ok : makePool d pool cs = some result) :
    ∃ next, Reach roots (q + cs.length) next ∧ poolSupply f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_, hp, hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next, hr, sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out, hr', sh'⟩ := ih hr sh ok
      exact ⟨out, by simpa [Nat.add_assoc, Nat.add_comm 1] using hr', sh'⟩
    next => contradiction

def isMaskedConst (d a : Sig) : Bool := masked d a == bvZero || masked d a == d

theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r, bvBit (f r) d = true)
    (ws : List Sig) : ws.countP (isMaskedConst d) ≤ mass ((ws.map bvObs).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons, List.map_cons, mass_cons]
    cases h : isMaskedConst d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (bvObs a)) := by
        simp only [isMaskedConst, Bool.or_eq_true, beq_iff_eq] at h
        rcases h with hz | ho
        · exact ⟨false, masked_zero dom hz⟩
        · exact ⟨true, masked_one dom ho⟩
      simpa [cost, hc, Nat.add_comm] using Nat.succ_le_succ ih

abbrev BoundPool := Sig × Nat × Nat × List Sig

def ValidPool (raw : List Sig) (T : Sig) (c : BoundPool) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bvBit (f r) c.1 = true) ∧ ¬Constant (restrictRows f (bvObs T)) ∧
    (∀ q ws, Reach (roots.map bvObs) q ws → Available ws (restrictRows f (bvObs T)) → c.2.1 ≤ q) ∧
    Reach (roots.map bvObs) c.2.2.1 bank ∧ poolSupply f bank c.2.2.2

theorem materialize_sound {raw T d L cs c} (slice : Slice raw T d L)
    (h : (makePool d raw cs).map (fun pool => (d, L, cs.length, pool)) = some c) :
    ValidPool raw T c := by
  cases he : makePool d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he, Option.map_some, Option.some.injEq] at h
    subst c
    obtain ⟨f, roots, dom, sup, nc, prior⟩ := slice
    obtain ⟨bank, hr, hs⟩ := makePool_sound dom (Reach.start (roots := roots.map bvObs)) sup cs he
    exact ⟨f, roots, bank, dom, nc, prior, by simpa using hr, hs⟩

def scalarPoolCut (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) : Bool :=
  let (d, lb, paid, wires) := c
  let z := choiceVal op
  let extra := !(availableB d wires z)
  (k + paid + extra.toNat < lb + (z :: rest).countP (isMaskedConst d)) &&
    rest.all (availableB d wires) && (!extra || choiceOK d wires op)

theorem scalarPoolCut_sound {raw T c} (valid : ValidPool raw T c) {k rest op}
    (nd : (choiceVal op :: rest).Nodup) (cut : scalarPoolCut c k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  obtain ⟨d, lb, paid, wires⟩ := c
  obtain ⟨f, roots, bank, dom, nc, lo, hp, hs⟩ := valid
  dsimp only at dom lo hp hs
  intro t ht run
  simp only [scalarPoolCut, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true] at cut
  let ws := choiceVal op :: rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach (roots.map bvObs) n out)
      (zs : poolSupply f out ws) (le : n = paid + (!(availableB d wires (choiceVal op))).toNat) : False := by
    have covered : supply out ((ws.map bvObs).map (restrictRows f)) := by
      intro v hv
      obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b := projected_bound f (bvList_run run ws nd rfl) nc reach covered lo
    have cm := count_constants dom ws
    have ineq := cut.1.1
    change k + paid + (!(availableB d wires (choiceVal op))).toNat < lb + ws.countP (isMaskedConst d) at ineq
    omega
  cases he : availableB d wires (choiceVal op)
  · simp only [he, Bool.not_false, Bool.not_true] at cut
    have hch : choiceOK d wires op = true := cut.2.resolve_left (by decide)
    obtain ⟨out, hr, hc⟩ := pay_choice dom hp hs op hch
    apply done _ _ hr _ (by simp [he])
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · exact availableB_sound dom (fun v hu => hc v (List.mem_cons_of_mem _ hu)) (cut.1.2 _ hm)
  · apply done _ _ hp _ (by simp [he])
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact availableB_sound dom hs he
    · exact availableB_sound dom hs (cut.1.2 _ hm)

-- Rename / Restriction helpers on BitVec 64
def inputs6 : List Sig :=
  [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0,
   0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

def selected6 (m : Nat) : List (Nat × Sig) :=
  (List.range 6).filterMap fun i => if m.testBit i then some (i, inputs6.getD i bvZero) else none
def vars6 (m : Nat) : List Sig := (selected6 m).map Prod.snd
def vtx6 (m j : Nat) : Sig := if m.testBit j then inputs6.getD j bvZero else bvZero
def graphGoal (m : Nat) : Sig :=
  let x := vtx6 m
  (x 0 &&& x 2) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) ||| (x 2 &&& x 4) |||
    (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) ||| (x 4 &&& x 5)

def subcube (z o : Nat) : Sig :=
  (List.range 6).foldl (fun acc j =>
    if z.testBit j then acc &&& ~~~(inputs6.getD j bvZero)
    else if o.testBit j then acc &&& inputs6.getD j bvZero
    else acc) bvOne

def fixRow (z o : Nat) (r : Row) : Row :=
  Fin.ofNat 64 ((r.val &&& (63 ^^^ (z ||| o))) ||| (o &&& 63))

def fixWord (z o : Nat) (a : Sig) : Sig :=
  bvTab fun r => bvBit (fixRow z o r) a

theorem bvBit_fixWord (z o : Nat) (a : Sig) (r : Row) :
    bvBit r (fixWord z o a) = bvBit (fixRow z o r) a := bvBit_tab _ _

theorem obs_fixWord (z o : Nat) (a : Sig) :
    bvObs (fixWord z o a) = restrictRows (fixRow z o) (bvObs a) := by
  funext r; exact bvBit_fixWord z o a r

def freeWord (roots : List Sig) (w : Sig) : Bool :=
  w == bvZero || w == bvOne || roots.contains w

theorem freeWord_ok {roots : List Sig} {w : Sig} (ok : freeWord roots w = true) :
    Available (roots.map bvObs) (bvObs w) := by
  simp only [freeWord, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr (Or.inl ⟨false, funext bvBit_zero⟩)
  · exact Or.inr (Or.inl ⟨true, funext bvBit_one⟩)
  · exact Or.inl (List.mem_map_of_mem hm)

def properB (T : Sig) : Bool := T != bvZero && T != bvOne
theorem proper_of {T : Sig} (h : properB T = true) : bvProper T := by
  simpa only [properB, bvProper, Bool.and_eq_true, bne_iff_ne] using h

def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) : Bool :=
  (bvBit rs.1 T != bvBit rs.2 T) &&
    roots.all fun w => w == a || bvBit rs.1 w == bvBit rs.2 w

theorem witnessB_sound {T : Sig} {roots : List Sig} {a : Sig} {rs : Row × Row}
    (ok : witnessB T roots a rs = true) : Essential T roots a := by
  simp only [witnessB, Bool.and_eq_true, bne_iff_ne, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at ok
  exact ⟨rs.1, rs.2, ok.1, fun w hw hne => (ok.2 w hw).resolve_left hne⟩

theorem lower_count {raw : List Sig} {T : Sig} (pT : bvProper T) (nT : bvPlain T = true)
    (nR : raw.all bvPlain = true) (xs : List (Sig × Row × Row))
    (hxs : xs.all (fun e => witnessB T raw e.1 e.2) = true) :
    Lower raw T ((xs.map Prod.fst).toFinset.card - 1) := by
  intro p bank hr hit
  obtain ⟨k, S, hk, run, sub⟩ := bvReach_live pT nT nR hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨⟨a, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    obtain ⟨r', s', hd, iso⟩ := witnessB_sound (List.all_eq_true.mp hxs _ hm)
    exact bvRaw_required run raw a sub r' s' hd iso
  have bound := bvLive_size run
  omega

theorem lower_lift {raw base : List Sig} {T G : Sig} (z o L : Nat)
    (pT : bvProper T) (nT : bvPlain T = true) (nR : raw.all bvPlain = true) (pG : bvProper G)
    (eq : fixWord z o T = G)
    (cov : raw.all (fun a => freeWord base (fixWord z o a)) = true)
    (xs : List (Sig × Row × Row))
    (ess : xs.all (fun e => witnessB T raw e.1 e.2) = true)
    (con : xs.all (fun e => fixWord z o e.1 == bvZero || fixWord z o e.1 == bvOne) = true)
    (prior : Lower base G L) :
    Lower raw T (L + (xs.map Prod.fst).toFinset.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k, S, hk, run, sub⟩ := bvReach_live pT nT nR hh ha
  let singles := (xs.map Prod.fst).toFinset
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨⟨a, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hs)
    obtain ⟨r', s', hd, hiso⟩ := witnessB_sound (List.all_eq_true.mp ess _ hm)
    exact bvRaw_required run raw a sub r' s' hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front, List.nodup_append]
    refine ⟨Finset.nodup_toList _, Finset.nodup_toList _, fun a ha b hb he => ?_⟩
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset = S := by ext a; simp [front, Finset.union_sdiff_of_subset subS]
  have run' := bvList_run run front nd fe
  have gc : restrictRows (fixRow z o) (bvObs T) = bvObs G :=
    (obs_fixWord z o T).symm.trans (congrArg bvObs eq)
  have supp : supply (base.map bvObs) ((front.map bvObs).map (restrictRows (fixRow z o))) := by
    intro v hv
    obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv
    obtain ⟨a, hmem, rfl⟩ := List.mem_map.mp hm
    rw [← obs_fixWord]
    exact freeWord_ok (List.all_eq_true.mp cov a (sub _ (fe ▸ List.mem_toFinset.mpr hmem)))
  have bound := projected_bound (fixRow z o) run' (gc ▸ obs_proper pG) Reach.start supp (L := L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map bvObs).map (restrictRows (fixRow z o))) := by
    simp only [front, List.map_append, mass_append]
    let ys := (singles.toList.map bvObs).map (restrictRows (fixRow z o))
    have only : ∀ v ∈ ys, Constant v := by
      intro v hv
      obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv
      obtain ⟨a, hmem, rfl⟩ := List.mem_map.mp hm
      rw [← obs_fixWord]
      obtain ⟨⟨a, r, s⟩, hm', rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp (Finset.mem_toList.mp hmem))
      have hh := List.all_eq_true.mp con _ hm'
      simp only [Bool.or_eq_true, beq_iff_eq] at hh
      rcases hh with h0 | h1
      · rw [h0]; exact ⟨false, funext bvBit_zero⟩
      · rw [h1]; exact ⟨true, funext bvBit_one⟩
    have sz := mass_constants ys only
    simp only [ys, List.length_map, Finset.length_toList] at sz
    change singles.card ≤ mass ys + _
    rw [sz]; omega
  dsimp only [singles] at massLo
  omega

theorem slice_of_lower {raw base : List Sig} {T G d : Sig} (z o L : Nat)
    (pG : bvProper G) (eq : fixWord z o T = G)
    (dom : fixWord z o d = bvOne)
    (cov : raw.all (fun a => freeWord base (fixWord z o a)) = true)
    (hL : Lower base G L) :
    Slice raw T d L := by
  have obs : restrictRows (fixRow z o) (bvObs T) = bvObs G :=
    (obs_fixWord z o T).symm.trans (congrArg bvObs eq)
  refine ⟨fixRow z o, base, ?_, ?_, ?_, ?_⟩
  · intro r; rw [← bvBit_fixWord, dom, bvBit_one]
  · intro a ha; rw [← obs_fixWord]; exact freeWord_ok (List.all_eq_true.mp cov a ha)
  · rw [obs]; exact obs_proper pG
  · rw [obs]; exact hL

-- Symmetry swap13 on BitVec 64
def swap13Row (r : Row) : Row :=
  let b1 := (r.val >>> 1) &&& 1
  let b3 := (r.val >>> 3) &&& 1
  Fin.ofNat 64 (if b1 != b3 then r.val ^^^ 10 else r.val)

def swap13 (a : Sig) : Sig :=
  (a &&& 0xcc33cc33cc33cc33) ||| ((a &&& 0x00cc00cc00cc00cc) <<< 6) ||| ((a &&& 0x3300330033003300) >>> 6)

theorem swap13_inv (r : Row) : swap13Row (swap13Row r) = r := by revert r; decide +kernel

theorem swap13_cases (r : Row) :
    ((0xcc33cc33cc33cc33 : Sig).getLsbD r.val = true ∧
     (!decide (r.val < 6) && (0x00cc00cc00cc00cc : Sig).getLsbD (r.val - 6)) = false ∧
     (0x3300330033003300 : Sig).getLsbD (6 + r.val) = false ∧
     (swap13Row r).val = r.val) ∨
    ((0xcc33cc33cc33cc33 : Sig).getLsbD r.val = false ∧
     (!decide (r.val < 6) && (0x00cc00cc00cc00cc : Sig).getLsbD (r.val - 6)) = true ∧
     (0x3300330033003300 : Sig).getLsbD (6 + r.val) = false ∧
     (swap13Row r).val = r.val - 6) ∨
    ((0xcc33cc33cc33cc33 : Sig).getLsbD r.val = false ∧
     (!decide (r.val < 6) && (0x00cc00cc00cc00cc : Sig).getLsbD (r.val - 6)) = false ∧
     (0x3300330033003300 : Sig).getLsbD (6 + r.val) = true ∧
     (swap13Row r).val = 6 + r.val) := by
  revert r; decide +kernel

theorem swap13_bit (a : Sig) (r : Row) : bvBit r (swap13 a) = bvBit (swap13Row r) a := by
  simp only [bvBit, swap13, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, r.isLt, decide_true, Bool.true_and]
  rcases swap13_cases r with ⟨h0, h1, h2, hr⟩ | ⟨h0, h1, h2, hr⟩ | ⟨h0, h1, h2, hr⟩ <;>
    (cases hlt : decide (r.val < 6) <;> simp_all [Nat.add_comm])
theorem swap13_bin (d : Nat) (a b : Sig) : swap13 (bvBin d a b) = bvBin d (swap13 a) (swap13 b) := by
  apply bvBit_ext; intro r; simp only [swap13_bit, bvBit_bin]
theorem swap13_inj : Function.Injective swap13 := by
  intro a b h; apply bvBit_ext; intro r
  have := congrArg (bvBit (swap13Row r)) h
  simpa only [swap13_bit, swap13_inv] using this
theorem swap13_consts : swap13 bvZero = bvZero ∧ swap13 bvOne = bvOne := by
  constructor <;> apply bvBit_ext <;> intro r <;> simp [swap13_bit, bvBit_zero, bvBit_one]
theorem swap13_invol (a : Sig) : swap13 (swap13 a) = a := by
  apply bvBit_ext; intro r; simp [swap13_bit, swap13_inv]
theorem swap13_goal63 : swap13 (graphGoal 63) = graphGoal 63 := by decide +kernel

theorem live_swap13 {T : Sig} {k S} (h : bvLive T k S) :
    bvLive (swap13 T) k (S.image swap13) := by
  have pp (v) (p : bvProper v) : bvProper (swap13 v) :=
    ⟨fun e => p.1 (swap13_inj (e.trans swap13_consts.1.symm)),
     fun e => p.2 (swap13_inj (e.trans swap13_consts.2.symm))⟩
  induction h using bvLive.ind with
  | stop hp => simpa using bvLive.stop (pp _ hp)
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have fresh : swap13 (bvBin d a b) ∉ (insert a (insert b U)).image swap13 := by
      intro hm; obtain ⟨v, hv, eq⟩ := Finset.mem_image.mp hm; exact hf (swap13_inj eq ▸ hv)
    simp only [Finset.image_insert, swap13_bin] at fresh ih ⊢
    exact bvLive.binary hd (pp _ ha) (pp _ hb) (fun hh => hab (swap13_inj hh)) fresh ih

theorem swap13_impossible {k : Nat} {ws : List Sig}
    (h : Impossible (graphGoal 63) k ws.toFinset) :
    Impossible (graphGoal 63) k (ws.map swap13).toFinset := by
  intro t ht run
  have r2 := live_swap13 run
  rw [swap13_goal63] at r2
  have eq : (ws.map swap13).toFinset.image swap13 = ws.toFinset := by
    ext x; simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩; simpa [swap13_invol] using hw
    · intro hx; exact ⟨swap13 x, ⟨x, hx, rfl⟩, swap13_invol x⟩
  rw [eq] at r2
  exact h t ht r2

-- Sorting & Binary Search for DAG lookup
def insSig (x : Sig) : List Sig → List Sig
  | [] => [x]
  | y :: ys => if x.toNat ≤ y.toNat then x :: y :: ys else y :: insSig x ys

def sortSig : List Sig → List Sig
  | [] => []
  | x :: xs => insSig x (sortSig xs)

theorem insSig_mem (x a : Sig) (l : List Sig) : a ∈ insSig x l ↔ a = x ∨ a ∈ l := by
  induction l with
  | nil => simp [insSig]
  | cons y ys ih =>
    unfold insSig; split
    · simp
    · simp only [List.mem_cons, ih]; tauto

theorem sortSig_toFinset (l : List Sig) : (sortSig l).toFinset = l.toFinset := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    ext a; simp only [sortSig, List.mem_toFinset, insSig_mem, List.mem_cons]
    have := Finset.ext_iff.mp ih a
    simp only [List.mem_toFinset] at this
    tauto

def cmpListSig : List Sig → List Sig → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs =>
    if a.toNat < b.toNat then .lt
    else if a.toNat > b.toNat then .gt
    else cmpListSig as bs

theorem cmpListSig_eq {xs ys : List Sig} (h : cmpListSig xs ys = .eq) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys with | nil => rfl | cons _ _ => simp [cmpListSig] at h
  | cons a as ih =>
    cases ys with
    | nil => simp [cmpListSig] at h
    | cons b bs =>
      unfold cmpListSig at h
      split at h
      · cases h
      · split at h
        · cases h
        · have hab : a = b := BitVec.eq_of_toNat_eq (by omega)
          rw [hab, ih h]

def bsearchAux (arr : Array (List Sig)) (tgt : List Sig) (lo hi : Nat) : Nat → Bool
  | 0 => false
  | fuel + 1 =>
    if lo ≥ hi then false
    else
      let mid := (lo + hi) / 2
      match arr[mid]? with
      | none => false
      | some v =>
        match cmpListSig tgt v with
        | .eq => true
        | .lt => bsearchAux arr tgt lo mid fuel
        | .gt => bsearchAux arr tgt (mid + 1) hi fuel

def bsearch (arr : Array (List Sig)) (tgt : List Sig) : Bool :=
  bsearchAux arr tgt 0 arr.size 12

theorem bsearchAux_sound (arr : Array (List Sig)) (tgt : List Sig) (lo hi fuel : Nat)
    (h : bsearchAux arr tgt lo hi fuel = true) : ∃ i < arr.size, arr[i]? = some tgt := by
  induction fuel generalizing lo hi with
  | zero => simp [bsearchAux] at h
  | succ fuel ih =>
    unfold bsearchAux at h
    split at h
    · cases h
    · cases hm : arr[(lo + hi) / 2]? with
      | none => simp [hm] at h
      | some v =>
        simp only [hm] at h
        cases hc : cmpListSig tgt v with
        | eq =>
          have hv : tgt = v := cmpListSig_eq hc
          have hlt : (lo + hi) / 2 < arr.size := by
            by_contra hge
            simp [Array.getElem?_eq_none (Nat.le_of_not_lt hge)] at hm
          exact ⟨(lo + hi) / 2, hlt, hv ▸ hm⟩
        | lt => simp only [hc] at h; exact ih lo ((lo + hi) / 2) h
        | gt => simp only [hc] at h; exact ih ((lo + hi) / 2 + 1) hi h

theorem bsearch_sound (arr : Array (List Sig)) (tgt : List Sig)
    (h : bsearch arr tgt = true) : ∃ i < arr.size, arr[i]? = some tgt :=
  bsearchAux_sound arr tgt 0 arr.size 12 h

-- Separation pairs checker
def pairsOK (T : Sig) (ps : List (Row × Row)) : Bool :=
  ps.all fun p => bvBit p.1 T && !(bvBit p.2 T)

def sepCol (ps : List (Row × Row)) (w : Sig) : Bits :=
  bvTab fun i : Fin 128 =>
    match ps[i.val]? with
    | none => false
    | some p => bvBit p.1 w != bvBit p.2 w

def sepMask (n : Nat) : Bits :=
  bvTab fun i : Fin 128 => decide (i.val < n)

def covList (ps : List (Row × Row)) (ws : List Sig) : Bits :=
  ws.foldl (fun acc w => acc ||| sepCol ps w) 0

theorem covList_bit (ps : List (Row × Row)) (ws : List Sig) (i : Fin 128) :
    (covList ps ws).getLsbD i.val = true ↔ ∃ w ∈ ws, (sepCol ps w).getLsbD i.val = true := by
  have go (acc : Bits) : (ws.foldl (fun a w => a ||| sepCol ps w) acc).getLsbD i.val = true ↔
      acc.getLsbD i.val = true ∨ ∃ w ∈ ws, (sepCol ps w).getLsbD i.val = true := by
    induction ws generalizing acc with
    | nil => simp
    | cons w ws ih =>
      simp only [List.foldl_cons, ih, BitVec.getLsbD_or, Bool.or_eq_true, List.mem_cons, exists_eq_or_imp]
      tauto
  simpa [covList] using go 0

theorem sep_required {T : Sig} {k : Nat} {ws : List Sig} (h : bvLive T k ws.toFinset)
    {ps : List (Row × Row)} (hp : pairsOK T ps = true) (hlen : ps.length ≤ 128) :
    covList ps ws = sepMask ps.length := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change (covList ps ws).getLsbD j = bvBit ⟨j, hj⟩ (sepMask ps.length)
  rw [sepMask, bvBit_tab]
  by_cases hlt : j < ps.length
  · simp only [hlt, decide_true]
    apply (covList_bit ps ws ⟨j, hj⟩).mpr
    have hm : ps[j] ∈ ps := List.getElem_mem hlt
    have hpair := List.all_eq_true.mp hp _ hm
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hpair
    obtain ⟨a, ha, hdiff⟩ := bvLive_row_diff h (show bvBit ps[j].1 T ≠ bvBit ps[j].2 T by simp [hpair.1, hpair.2])
    refine ⟨a, List.mem_toFinset.mp ha, ?_⟩
    change bvBit ⟨j, hj⟩ (sepCol ps a) = true
    rw [sepCol, bvBit_tab, List.getElem?_eq_getElem hlt]
    exact bne_iff_ne.mpr hdiff
  · simp only [hlt, decide_false]
    apply Bool.eq_false_iff.mpr
    intro ht
    obtain ⟨w, _, hw⟩ := (covList_bit ps ws ⟨j, hj⟩).mp ht
    change bvBit ⟨j, hj⟩ (sepCol ps w) = true at hw
    rw [sepCol, bvBit_tab, List.getElem?_eq_none (Nat.le_of_not_lt hlt)] at hw
    cases hw

-- Node verification
def childTwo (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  bvBin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x; simp [h.mem_erase_iff]

theorem enum_step {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d < 4, ∀ ka kb, a ≠ b → bvBin d a b ∉ ws →
      bvProper (bvBin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible T (cap - 1) (childTwo ws a b d ka kb).toFinset) :
    Impossible T cap ws.toFinset := by
  classical
  intro k hk h
  generalize he : ws.toFinset = S at h
  induction h using bvLive.ind with
  | stop _ => exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  | @binary k U a b d hd _ _ hab hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bvBin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := bvLive_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest = (ws.erase a).erase b from rfl, erase_fin (hn.erase _) b, erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin, kept_fin, er, he]; ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j = a <;>
        by_cases jb : j = b <;> simp_all [ka, kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => hn.not_mem_erase (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept, ar, hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨fun h => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h))), kept_nd ka a _ nk ax⟩
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bvBin d a b) U := by
      change (bvBin d a b :: kept ka a (kept kb b rest)).toFinset = _; simp [ke]
    have sc := bvLive_size tail
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [← List.toFinset_card_of_nodup nd, eq]; omega
    exact twoStep a am b bm d hd ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)

theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w = a ∧ k = true) ∨ w ∈ v := by cases k <;> simp [kept]

theorem childTwo_swap (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : d < 4) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (bvFlipOp d) kb ka).toFinset := by
  ext x
  simp only [childTwo, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset,
    keep_mem, (nd.erase _).mem_erase_iff, nd.mem_erase_iff, bvBin_flip hd a b]
  tauto

def checkChild (useSym : Bool) (ps : List (Row × Row)) (smask : Bits)
    (pools : List BoundPool) (prev : Array (List Sig)) (cap : Nat)
    (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : Bool :=
  let z := bvBin d a b
  let rest := kept ka a (kept kb b ((ws.erase a).erase b))
  let child := z :: rest
  if child.length > cap then true else
  if !properB z || ws.contains z then true else
  if covList ps child != smask then true else
  let s1 := sortSig child
  if bsearch prev s1 then true else
  if useSym && bsearch prev (sortSig (child.map swap13)) then true else
  pools.any fun p => scalarPoolCut p (cap - 1) rest (d, a, b)

def checkPair (useSym : Bool) (ps : List (Row × Row)) (smask : Bits)
    (pools : List BoundPool) (prev : Array (List Sig)) (cap : Nat)
    (ws : List Sig) (a b : Sig) (d : Nat) : Bool :=
  let f := checkChild useSym ps smask pools prev cap ws a b d
  f false false && f true false && f false true && f true true

def checkPairs (useSym : Bool) (ps : List (Row × Row)) (smask : Bits)
    (pools : List BoundPool) (prev : Array (List Sig)) (cap : Nat)
    (ws : List Sig) : List Sig → Bool
  | [] => true
  | a :: bs =>
    bs.all (fun b => ([0, 1, 2, 3] : List Nat).all (checkPair useSym ps smask pools prev cap ws a b)) &&
    checkPairs useSym ps smask pools prev cap ws bs

theorem checkPairs_at {useSym ps smask pools prev cap ws l}
    (h : checkPairs useSym ps smask pools prev cap ws l = true)
    {a b : Sig} (ha : a ∈ l) (hb : b ∈ l) (ne : a ≠ b) :
    (∀ d < 4, checkPair useSym ps smask pools prev cap ws a b d = true) ∨
    (∀ d < 4, checkPair useSym ps smask pools prev cap ws b a d = true) := by
  induction l with
  | nil => simp at ha
  | cons w rest ih =>
    simp only [checkPairs, Bool.and_eq_true, List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | ha'
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => h.1 b bm d (by rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3) with rfl | rfl | rfl | rfl <;> decide)
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact Or.inr fun d hd => h.1 a ha' d (by rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3) with rfl | rfl | rfl | rfl <;> decide)
      · exact ih h.2 ha' hb'

theorem checkChild_sound {useSym : Bool} {rawL : List Sig} {T0 : Sig}
    {ps : List (Row × Row)} {pools : List BoundPool} {prev : Array (List Sig)} {cap : Nat}
    {ws : List Sig} {a b : Sig} {d : Nat} {ka kb : Bool}
    (hSym : useSym = true → T0 = graphGoal 63)
    (hp : pairsOK T0 ps = true) (hlen : ps.length ≤ 128)
    (hnd : ws.Nodup) (ha : a ∈ ws) (hb : b ∈ ws) (hab : a ≠ b)
    (hfresh : bvBin d a b ∉ ws) (hpro : bvProper (bvBin d a b))
    (hcap : (childTwo ws a b d ka kb).length ≤ cap)
    (hPools : ∀ p ∈ pools, ValidPool rawL T0 p)
    (hPrev : ∀ i < prev.size, ∀ v, prev[i]? = some v → Impossible T0 (cap - 1) v.toFinset)
    (hok : checkChild useSym ps (sepMask ps.length) pools prev cap ws a b d ka kb = true) :
    Impossible T0 (cap - 1) (childTwo ws a b d ka kb).toFinset := by
  let z := bvBin d a b
  let rest := kept ka a (kept kb b ((ws.erase a).erase b))
  have hchild : childTwo ws a b d ka kb = z :: rest := rfl
  rw [hchild] at hcap ⊢
  have rn : ((ws.erase a).erase b).Nodup := (hnd.erase _).erase _
  have ar : a ∉ (ws.erase a).erase b := fun h => hnd.not_mem_erase (List.mem_of_mem_erase h)
  have br : b ∉ (ws.erase a).erase b := (hnd.erase a).not_mem_erase
  have nk := kept_nd kb b _ rn br
  have ax : a ∉ kept kb b ((ws.erase a).erase b) := by cases kb <;> simp [kept, ar, hab]
  have hrsub : ∀ x ∈ rest, x ∈ ws := by
    intro x hx
    rcases (keep_mem a ka).mp hx with ⟨rfl, _⟩ | hx
    · exact ha
    rcases (keep_mem b kb).mp hx with ⟨rfl, _⟩ | hx
    · exact hb
    exact List.mem_of_mem_erase (List.mem_of_mem_erase hx)
  have hndc : (z :: rest).Nodup :=
    List.nodup_cons.mpr ⟨fun hm => hfresh (hrsub z hm), kept_nd ka a _ nk ax⟩
  unfold checkChild at hok
  change (if (z :: rest).length > cap then true else if (!properB z || ws.contains z) = true then true else
    if (covList ps (z :: rest) != sepMask ps.length) = true then true else
    if bsearch prev (sortSig (z :: rest)) = true then true else
    if (useSym && bsearch prev (sortSig ((z :: rest).map swap13))) = true then true else
    pools.any fun p => scalarPoolCut p (cap - 1) rest (d, a, b)) = true at hok
  rw [ite_eq_right (by omega)] at hok
  have hpp : properB z = true := by simpa [properB, bvProper] using hpro
  have hct : ws.contains z = false := by simp [List.contains_eq_mem, z, hfresh]
  rw [hpp, hct] at hok
  simp only [Bool.not_true, Bool.false_or, Bool.false_eq_true, ite_false] at hok
  by_cases hsep : (covList ps (z :: rest) != sepMask ps.length) = true
  · intro k hk run
    exact (bne_iff_ne.mp hsep) (sep_required run hp hlen)
  rw [ite_eq_right hsep] at hok
  by_cases hbs : bsearch prev (sortSig (z :: rest)) = true
  · obtain ⟨i, hi, hget⟩ := bsearch_sound prev (sortSig (z :: rest)) hbs
    have := hPrev i hi _ hget
    rwa [sortSig_toFinset] at this
  rw [ite_eq_right hbs] at hok
  by_cases hbs2 : (useSym && bsearch prev (sortSig ((z :: rest).map swap13))) = true
  · simp only [Bool.and_eq_true] at hbs2
    obtain ⟨i, hi, hget⟩ := bsearch_sound prev (sortSig ((z :: rest).map swap13)) hbs2.2
    have hT63 := hSym hbs2.1
    have := hPrev i hi _ hget
    rw [sortSig_toFinset, hT63] at this
    have h2 := swap13_impossible this
    have heq : (((z :: rest).map swap13).map swap13).toFinset = (z :: rest).toFinset := by
      simp [List.map_map, Function.comp_def, swap13_invol]
    rw [heq] at h2
    rwa [hT63]
  rw [ite_eq_right hbs2] at hok
  obtain ⟨p, hpM, hcut⟩ := List.any_eq_true.mp hok
  exact scalarPoolCut_sound (hPools p hpM) (op := (d, a, b)) hndc hcut

def checkNode (useSym : Bool) (T : Sig) (ps : List (Row × Row)) (smask : Bits)
    (pools : List BoundPool) (prev : Array (List Sig)) (cap : Nat) (ws : List Sig) : Bool :=
  decide ws.Nodup && !(ws.contains T) &&
    (if cap = 0 then true else checkPairs useSym ps smask pools prev cap ws ws)

theorem checkNode_sound {rawL : List Sig} {useSym : Bool} {T : Sig}
    {ps : List (Row × Row)} {pools : List BoundPool} {prev : Array (List Sig)} {cap : Nat} {ws : List Sig}
    (hSym : useSym = true → T = graphGoal 63)
    (hp : pairsOK T ps = true) (hlen : ps.length ≤ 128)
    (hPools : ∀ p ∈ pools, ValidPool rawL T p)
    (hPrev : cap > 0 → ∀ i < prev.size, ∀ v, prev[i]? = some v → Impossible T (cap - 1) v.toFinset)
    (hok : checkNode useSym T ps (sepMask ps.length) pools prev cap ws = true) :
    Impossible T cap ws.toFinset := by
  simp only [checkNode, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem] at hok
  have hnd := hok.1.1
  have hout : T ∉ ws := by simpa using hok.1.2
  by_cases hc : cap = 0
  · subst hc; intro k hk h
    have : k = 0 := by omega
    subst k; obtain ⟨hS, _⟩ := h
    exact hout (List.mem_toFinset.mp (by rw [hS]; exact Finset.mem_singleton_self _))
  have hcp := hok.2
  rw [if_neg hc] at hcp
  apply enum_step hnd hout
  intro a ha b hb d hd ka kb hab hfresh hpro hlenC
  rcases checkPairs_at hcp ha hb hab with h1 | h1
  · have hp' := h1 d hd
    simp only [checkPair, Bool.and_eq_true] at hp'
    have hc' : checkChild useSym ps (sepMask ps.length) pools prev cap ws a b d ka kb = true := by
      cases ka <;> cases kb <;> first | exact hp'.1.1.1 | exact hp'.1.2 | exact hp'.1.1.2 | exact hp'.2
    exact checkChild_sound hSym hp hlen hnd ha hb hab hfresh hpro hlenC hPools (hPrev (by omega)) hc'
  · rw [childTwo_swap ws hnd a b d hd ka kb]
    have hd' := bvFlip_ok hd
    have hp' := h1 (bvFlipOp d) hd'.1
    simp only [checkPair, Bool.and_eq_true] at hp'
    have hc' : checkChild useSym ps (sepMask ps.length) pools prev cap ws b a (bvFlipOp d) kb ka = true := by
      cases kb <;> cases ka <;> first | exact hp'.1.1.1 | exact hp'.1.2 | exact hp'.1.1.2 | exact hp'.2
    have hlenC' : (childTwo ws b a (bvFlipOp d) kb ka).length ≤ cap := by
      have hsub1 : (childTwo ws a b d ka kb).toFinset = (childTwo ws b a (bvFlipOp d) kb ka).toFinset :=
        childTwo_swap ws hnd a b d hd ka kb
      have ar1 : a ∉ (ws.erase a).erase b := fun h => hnd.not_mem_erase (List.mem_of_mem_erase h)
      have br2 : b ∉ (ws.erase b).erase a := fun h => hnd.not_mem_erase (List.mem_of_mem_erase h)
      have hnd1 : (childTwo ws a b d ka kb).Nodup := by
        unfold childTwo
        refine List.nodup_cons.mpr ⟨fun hm => hfresh ?_, ?_⟩
        · rcases (keep_mem a ka).mp hm with ⟨heq, _⟩ | hm
          · exact heq.symm ▸ ha
          rcases (keep_mem b kb).mp hm with ⟨heq, _⟩ | hm
          · exact heq.symm ▸ hb
          exact List.mem_of_mem_erase (List.mem_of_mem_erase hm)
        · exact kept_nd ka a _ (kept_nd kb b _ ((hnd.erase _).erase _) (hnd.erase a).not_mem_erase)
            (by cases kb <;> simp [kept, hab, ar1])
      have hnd2 : (childTwo ws b a (bvFlipOp d) kb ka).Nodup := by
        unfold childTwo
        have hfr' : bvBin (bvFlipOp d) b a ∉ ws := bvBin_flip hd a b ▸ hfresh
        refine List.nodup_cons.mpr ⟨fun hm => hfr' ?_, ?_⟩
        · rcases (keep_mem b kb).mp hm with ⟨heq, _⟩ | hm
          · exact heq.symm ▸ hb
          rcases (keep_mem a ka).mp hm with ⟨heq, _⟩ | hm
          · exact heq.symm ▸ ha
          exact List.mem_of_mem_erase (List.mem_of_mem_erase hm)
        · exact kept_nd kb b _ (kept_nd ka a _ ((hnd.erase _).erase _) (hnd.erase b).not_mem_erase)
            (by cases ka <;> simp [kept, Ne.symm hab, br2])
      rw [← List.toFinset_card_of_nodup hnd2, ← hsub1, List.toFinset_card_of_nodup hnd1]
      exact hlenC
    exact checkChild_sound hSym hp hlen hnd hb ha (Ne.symm hab)
      (bvBin_flip hd a b ▸ hfresh) (bvBin_flip hd a b ▸ hpro) hlenC' hPools (hPrev (by omega)) hc'

-- Restriction table & level checker
abbrev RestrEntry := Nat × Nat × Nat
abbrev PoolDesc := Nat × List Choice
abbrev NodeData := List Sig × List PoolDesc

def buildPools (raw : List Sig) (rs : Array RestrEntry) (pds : List PoolDesc) : List BoundPool :=
  pds.filterMap fun (ri, cs) =>
    match rs[ri]? with
    | none => none
    | some (z, o, lb) =>
      let d := subcube z o
      (makePool d raw cs).map fun pool => (d, lb, cs.length, pool)

theorem buildPools_sound {raw : List Sig} {T : Sig} {rs : Array RestrEntry}
    (hRs : ∀ i < rs.size, ∀ r, rs[i]? = some r → Slice raw T (subcube r.1 r.2.1) r.2.2)
    (pds : List PoolDesc) :
    ∀ p ∈ buildPools raw rs pds, ValidPool raw T p := by
  intro p hp
  obtain ⟨⟨ri, cs⟩, _, hfm⟩ := List.mem_filterMap.mp hp
  cases he : rs[ri]? with
  | none => simp [he] at hfm
  | some r =>
    simp only [he] at hfm
    have hlt : ri < rs.size := by
      by_contra hge; simp [Array.getElem?_eq_none (Nat.le_of_not_lt hge)] at he
    exact materialize_sound (hRs ri hlt r he) hfm

-- Fast precomputed separation masks (Decor)
def pairBits (sel : Row × Row → Row) (w : Sig) : List (Row × Row) → Bits
  | [] => 0
  | p :: ps => (pairBits sel w ps <<< 1) ||| (if bvBit (sel p) w then 1 else 0)

theorem pairBits_getLsbD (sel : Row × Row → Row) (w : Sig) (ps : List (Row × Row)) (j : Nat) (hj : j < 128) :
    (pairBits sel w ps).getLsbD j = match ps[j]? with | none => false | some p => bvBit (sel p) w := by
  induction ps generalizing j with
  | nil => simp [pairBits]
  | cons p ps ih =>
    cases j with
    | zero =>
      simp only [pairBits, List.getElem?_cons_zero, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
      cases bvBit (sel p) w <;> simp
    | succ j =>
      simp only [pairBits, List.getElem?_cons_succ, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
      have h1 : (if bvBit (sel p) w then (1 : Bits) else 0).getLsbD (j + 1) = false := by
        cases bvBit (sel p) w <;> simp
      rw [h1, Bool.or_false]
      simp [hj, ih j (by omega)]

theorem pairBits_bin (sel : Row × Row → Row) (d : Nat) (a b : Sig) (ps : List (Row × Row)) :
    pairBits sel (bvBin d a b) ps = bvBin d (pairBits sel a ps) (pairBits sel b ps) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change (pairBits sel (bvBin d a b) ps).getLsbD j = bvBit ⟨j, hj⟩ (bvBin d (pairBits sel a ps) (pairBits sel b ps))
  rw [bvBit_bin]
  change (pairBits sel (bvBin d a b) ps).getLsbD j =
    (if d = 0 then (pairBits sel a ps).getLsbD j && (pairBits sel b ps).getLsbD j
     else if d = 1 then (pairBits sel a ps).getLsbD j || (pairBits sel b ps).getLsbD j
     else if d = 2 then (pairBits sel a ps).getLsbD j && !((pairBits sel b ps).getLsbD j)
     else !((pairBits sel a ps).getLsbD j) && (pairBits sel b ps).getLsbD j)
  rw [pairBits_getLsbD _ _ _ j hj, pairBits_getLsbD _ _ _ j hj, pairBits_getLsbD _ _ _ j hj]
  cases h : ps[j]? with
  | none => split_ifs <;> rfl
  | some p => simp only [bvBit_bin]

theorem pairBits_xor (ps : List (Row × Row)) (w : Sig) :
    pairBits Prod.fst w ps ^^^ pairBits Prod.snd w ps = sepCol ps w := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change (pairBits Prod.fst w ps ^^^ pairBits Prod.snd w ps).getLsbD j = bvBit ⟨j, hj⟩ (sepCol ps w)
  rw [BitVec.getLsbD_xor, pairBits_getLsbD _ _ _ j hj, pairBits_getLsbD _ _ _ j hj, sepCol, bvBit_tab]
  cases ps[j]? with
  | none => rfl
  | some p => cases bvBit p.1 w <;> cases bvBit p.2 w <;> rfl

abbrev Decor := Sig × Bits × Bits
def mkDecor (ps : List (Row × Row)) (w : Sig) : Decor :=
  (w, pairBits Prod.fst w ps, pairBits Prod.snd w ps)
def dbin (d : Nat) (x y : Decor) : Decor :=
  (bvBin d x.1 y.1, bvBin d x.2.1 y.2.1, bvBin d x.2.2 y.2.2)
def dsep (x : Decor) : Bits := x.2.1 ^^^ x.2.2
def covDecor (ds : List Decor) : Bits :=
  ds.foldl (fun acc u => acc ||| dsep u) 0

theorem dbin_mkDecor (ps : List (Row × Row)) (d : Nat) (a b : Sig) :
    dbin d (mkDecor ps a) (mkDecor ps b) = mkDecor ps (bvBin d a b) := by
  simp only [dbin, mkDecor, pairBits_bin]

theorem dsep_mkDecor (ps : List (Row × Row)) (w : Sig) :
    dsep (mkDecor ps w) = sepCol ps w := pairBits_xor ps w

theorem covDecor_mkDecor (ps : List (Row × Row)) (ws : List Sig) :
    covDecor (ws.map (mkDecor ps)) = covList ps ws := by
  have go (acc : Bits) : (ws.map (mkDecor ps)).foldl (fun a u => a ||| dsep u) acc =
      ws.foldl (fun a w => a ||| sepCol ps w) acc := by
    induction ws generalizing acc with
    | nil => rfl
    | cons w ws ih => simp only [List.map_cons, List.foldl_cons, dsep_mkDecor, ih]
  exact go 0

theorem erase_map_mkDecor (ps : List (Row × Row)) (ws : List Sig) (a : Sig) :
    (ws.map (mkDecor ps)).erase (mkDecor ps a) = (ws.erase a).map (mkDecor ps) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons, List.erase_cons]
    by_cases h : w = a
    · subst h; simp
    · have hne : mkDecor ps w ≠ mkDecor ps a := fun he => h (congrArg Prod.fst he)
      simp [h, hne, ih]

theorem map_fst_mkDecor (ps : List (Row × Row)) (ws : List Sig) :
    (ws.map (mkDecor ps)).map Prod.fst = ws := by
  simp [List.map_map, Function.comp_def, mkDecor]

def checkChildD (useSym : Bool) (smask : Bits)
    (pools : List BoundPool) (prev : Array (List Sig)) (cap : Nat)
    (ws : List Sig) (dws : List Decor) (x y : Decor) (d : Nat) (ka kb : Bool) : Bool :=
  let z := bvBin d x.1 y.1
  let drest := kept ka x (kept kb y ((dws.erase x).erase y))
  if drest.length + 1 > cap then true else
  if !properB z || ws.contains z then true else
  let dz := dbin d x y
  if covDecor (dz :: drest) != smask then true else
  let rest := drest.map Prod.fst
  let child := z :: rest
  let s1 := sortSig child
  if bsearch prev s1 then true else
  if useSym && bsearch prev (sortSig (child.map swap13)) then true else
  pools.any fun p => scalarPoolCut p (cap - 1) rest (d, x.1, y.1)

def checkPairD (useSym : Bool) (smask : Bits)
    (pools : List BoundPool) (prev : Array (List Sig)) (cap : Nat)
    (ws : List Sig) (dws : List Decor) (x y : Decor) (d : Nat) : Bool :=
  let f := checkChildD useSym smask pools prev cap ws dws x y d
  f false false && f true false && f false true && f true true

def checkPairsD (useSym : Bool) (smask : Bits)
    (pools : List BoundPool) (prev : Array (List Sig)) (cap : Nat)
    (ws : List Sig) (dws : List Decor) : List Decor → Bool
  | [] => true
  | x :: ys =>
    ys.all (fun y => ([0, 1, 2, 3] : List Nat).all (checkPairD useSym smask pools prev cap ws dws x y)) &&
    checkPairsD useSym smask pools prev cap ws dws ys

def checkNodeD (useSym : Bool) (T : Sig) (ps : List (Row × Row)) (smask : Bits)
    (pools : List BoundPool) (prev : Array (List Sig)) (cap : Nat) (ws : List Sig) : Bool :=
  decide ws.Nodup && !(ws.contains T) &&
    (if cap = 0 then true else
      let dws := ws.map (mkDecor ps)
      checkPairsD useSym smask pools prev cap ws dws dws)

theorem checkChildD_eq (useSym : Bool) (ps : List (Row × Row)) (smask : Bits)
    (pools : List BoundPool) (prev : Array (List Sig)) (cap : Nat)
    (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) :
    checkChildD useSym smask pools prev cap ws (ws.map (mkDecor ps)) (mkDecor ps a) (mkDecor ps b) d ka kb =
    checkChild useSym ps smask pools prev cap ws a b d ka kb := by
  unfold checkChildD checkChild
  dsimp only
  rw [erase_map_mkDecor, erase_map_mkDecor, ← map_kept, ← map_kept, dbin_mkDecor,
    ← List.map_cons, covDecor_mkDecor, map_fst_mkDecor, List.length_map]
  rfl

theorem checkPairD_eq (useSym : Bool) (ps : List (Row × Row)) (smask : Bits)
    (pools : List BoundPool) (prev : Array (List Sig)) (cap : Nat)
    (ws : List Sig) (a b : Sig) (d : Nat) :
    checkPairD useSym smask pools prev cap ws (ws.map (mkDecor ps)) (mkDecor ps a) (mkDecor ps b) d =
    checkPair useSym ps smask pools prev cap ws a b d := by
  simp only [checkPairD, checkPair, checkChildD_eq]

theorem checkPairsD_eq (useSym : Bool) (ps : List (Row × Row)) (smask : Bits)
    (pools : List BoundPool) (prev : Array (List Sig)) (cap : Nat)
    (ws l : List Sig) :
    checkPairsD useSym smask pools prev cap ws (ws.map (mkDecor ps)) (l.map (mkDecor ps)) =
    checkPairs useSym ps smask pools prev cap ws l := by
  induction l with
  | nil => rfl
  | cons a bs ih =>
    simp only [List.map_cons, checkPairsD, checkPairs, List.all_map, Function.comp_def, ih]
    have h1 : ∀ b, ([0, 1, 2, 3] : List Nat).all (checkPairD useSym smask pools prev cap ws (ws.map (mkDecor ps)) (mkDecor ps a) (mkDecor ps b)) =
        ([0, 1, 2, 3] : List Nat).all (checkPair useSym ps smask pools prev cap ws a b) :=
      fun b => by simp only [List.all_cons, List.all_nil, checkPairD_eq]
    simp only [h1]

theorem checkNodeD_eq (useSym : Bool) (T : Sig) (ps : List (Row × Row)) (smask : Bits)
    (pools : List BoundPool) (prev : Array (List Sig)) (cap : Nat) (ws : List Sig) :
    checkNodeD useSym T ps smask pools prev cap ws =
    checkNode useSym T ps smask pools prev cap ws := by
  simp only [checkNodeD, checkNode, checkPairsD_eq]

def checkRange (useSym : Bool) (raw : List Sig) (T : Sig) (ps : List (Row × Row))
    (rs : Array RestrEntry) (prev : Array (List Sig)) (cap : Nat)
    (nodes : Array NodeData) (lo len : Nat) : Bool :=
  let smask := sepMask ps.length
  (List.range len).all fun off =>
    match nodes[lo + off]? with
    | none => true
    | some nd =>
      let pools := buildPools raw rs nd.2
      checkNodeD useSym T ps smask pools prev cap nd.1

theorem checkRange_sound {raw : List Sig} {useSym : Bool} {T : Sig} {ps : List (Row × Row)}
    {rs : Array RestrEntry} {prev : Array (List Sig)} {cap : Nat} {nodes : Array NodeData}
    {lo len : Nat}
    (hSym : useSym = true → T = graphGoal 63)
    (hp : pairsOK T ps = true) (hlen : ps.length ≤ 128)
    (hRs : ∀ i < rs.size, ∀ r, rs[i]? = some r → Slice raw T (subcube r.1 r.2.1) r.2.2)
    (hPrev : cap > 0 → ∀ i < prev.size, ∀ v, prev[i]? = some v → Impossible T (cap - 1) v.toFinset)
    (hok : checkRange useSym raw T ps rs prev cap nodes lo len = true) :
    ∀ i, lo ≤ i → i < lo + len → ∀ nd, nodes[i]? = some nd → Impossible T cap nd.1.toFinset := by
  intro i hlo hhi nd hnd
  have hm := List.all_eq_true.mp hok (i - lo) (List.mem_range.mpr (by omega))
  rw [Nat.add_sub_of_le hlo, hnd] at hm; dsimp only at hm; rw [checkNodeD_eq] at hm
  exact checkNode_sound hSym hp hlen (buildPools_sound hRs nd.2) hPrev hm

theorem level_of_nodes {T : Sig} {cap : Nat} {nodes : Array NodeData}
    (hall : ∀ i < nodes.size, ∀ nd, nodes[i]? = some nd → Impossible T cap nd.1.toFinset) :
    ∀ i < (nodes.map Prod.fst).size, ∀ v, (nodes.map Prod.fst)[i]? = some v → Impossible T cap v.toFinset := by
  intro i hi v hv
  simp only [Array.size_map] at hi
  rw [Array.getElem?_map] at hv
  cases he : nodes[i]? with
  | none => simp [he] at hv
  | some nd =>
    simp only [he, Option.map_some, Option.some.injEq] at hv
    subst hv
    exact hall i hi nd he

theorem low_5 : Lower (vars6 5) (graphGoal 5) 1 := by
  have h := lower_count (raw := vars6 5) (T := graphGoal 5) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 4, 5), (0xf0f0f0f0f0f0f0f0, 1, 5)] (by decide +kernel)
  simpa [show ((List.map Prod.fst [(0xaaaaaaaaaaaaaaaa, (4 : Row), (5 : Row)), (0xf0f0f0f0f0f0f0f0, (1 : Row), (5 : Row))]).toFinset.card - 1) = 1 by decide +kernel] using h

theorem low_10 : Lower (vars6 10) (graphGoal 10) 1 := by
  have h := lower_count (raw := vars6 10) (T := graphGoal 10) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xcccccccccccccccc, 8, 10), (0xff00ff00ff00ff00, 2, 10)] (by decide +kernel)
  simpa [show ((List.map Prod.fst [(0xcccccccccccccccc, (8 : Row), (10 : Row)), (0xff00ff00ff00ff00, (2 : Row), (10 : Row))]).toFinset.card - 1) = 1 by decide +kernel] using h

theorem low_17 : Lower (vars6 17) (graphGoal 17) 1 := by
  have h := lower_count (raw := vars6 17) (T := graphGoal 17) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 16, 17), (0xffff0000ffff0000, 1, 17)] (by decide +kernel)
  simpa [show ((List.map Prod.fst [(0xaaaaaaaaaaaaaaaa, (16 : Row), (17 : Row)), (0xffff0000ffff0000, (1 : Row), (17 : Row))]).toFinset.card - 1) = 1 by decide +kernel] using h

theorem low_20 : Lower (vars6 20) (graphGoal 20) 1 := by
  have h := lower_count (raw := vars6 20) (T := graphGoal 20) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xf0f0f0f0f0f0f0f0, 16, 20), (0xffff0000ffff0000, 4, 20)] (by decide +kernel)
  simpa [show ((List.map Prod.fst [(0xf0f0f0f0f0f0f0f0, (16 : Row), (20 : Row)), (0xffff0000ffff0000, (4 : Row), (20 : Row))]).toFinset.card - 1) = 1 by decide +kernel] using h

theorem low_33 : Lower (vars6 33) (graphGoal 33) 1 := by
  have h := lower_count (raw := vars6 33) (T := graphGoal 33) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 32, 33), (0xffffffff00000000, 1, 33)] (by decide +kernel)
  simpa [show ((List.map Prod.fst [(0xaaaaaaaaaaaaaaaa, (32 : Row), (33 : Row)), (0xffffffff00000000, (1 : Row), (33 : Row))]).toFinset.card - 1) = 1 by decide +kernel] using h

theorem low_34 : Lower (vars6 34) (graphGoal 34) 1 := by
  have h := lower_count (raw := vars6 34) (T := graphGoal 34) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xcccccccccccccccc, 32, 34), (0xffffffff00000000, 2, 34)] (by decide +kernel)
  simpa [show ((List.map Prod.fst [(0xcccccccccccccccc, (32 : Row), (34 : Row)), (0xffffffff00000000, (2 : Row), (34 : Row))]).toFinset.card - 1) = 1 by decide +kernel] using h

theorem low_40 : Lower (vars6 40) (graphGoal 40) 1 := by
  have h := lower_count (raw := vars6 40) (T := graphGoal 40) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xff00ff00ff00ff00, 32, 40), (0xffffffff00000000, 8, 40)] (by decide +kernel)
  simpa [show ((List.map Prod.fst [(0xff00ff00ff00ff00, (32 : Row), (40 : Row)), (0xffffffff00000000, (8 : Row), (40 : Row))]).toFinset.card - 1) = 1 by decide +kernel] using h

theorem low_48 : Lower (vars6 48) (graphGoal 48) 1 := by
  have h := lower_count (raw := vars6 48) (T := graphGoal 48) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xffff0000ffff0000, 32, 48), (0xffffffff00000000, 16, 48)] (by decide +kernel)
  simpa [show ((List.map Prod.fst [(0xffff0000ffff0000, (32 : Row), (48 : Row)), (0xffffffff00000000, (16 : Row), (48 : Row))]).toFinset.card - 1) = 1 by decide +kernel] using h

def rs_21 : Array RestrEntry := #[(1, 0, 1), (4, 0, 1), (16, 0, 1), (0, 1, 1), (0, 4, 1), (0, 16, 1)]
theorem rs_21_ok : ∀ i < rs_21.size, ∀ r, rs_21[i]? = some r → Slice (vars6 21) (graphGoal 21) (subcube r.1 r.2.1) r.2.2 := by
  intro i hi r hr
  have hi' : i < 6 := hi
  interval_cases i <;> simp [rs_21] at hr <;> subst hr
  · exact slice_of_lower 1 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_20
  · exact slice_of_lower 4 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_17
  · exact slice_of_lower 16 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5
  · refine slice_of_lower 0 1 1 (G := fixWord 0 1 (graphGoal 21)) (base := vars6 20) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_count (raw := vars6 20) (T := fixWord 0 1 (graphGoal 21)) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xf0f0f0f0f0f0f0f0, 0, 4), (0xffff0000ffff0000, 0, 16)] (by decide +kernel)
    simpa [show (List.map Prod.fst [(0xf0f0f0f0f0f0f0f0, (0 : Row), (4 : Row)), (0xffff0000ffff0000, (0 : Row), (16 : Row))]).toFinset.card - 1 = 1 by decide +kernel] using hl
  · refine slice_of_lower 0 4 1 (G := fixWord 0 4 (graphGoal 21)) (base := vars6 17) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_count (raw := vars6 17) (T := fixWord 0 4 (graphGoal 21)) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 0, 1), (0xffff0000ffff0000, 0, 16)] (by decide +kernel)
    simpa [show (List.map Prod.fst [(0xaaaaaaaaaaaaaaaa, (0 : Row), (1 : Row)), (0xffff0000ffff0000, (0 : Row), (16 : Row))]).toFinset.card - 1 = 1 by decide +kernel] using hl
  · refine slice_of_lower 0 16 1 (G := fixWord 0 16 (graphGoal 21)) (base := vars6 5) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_count (raw := vars6 5) (T := fixWord 0 16 (graphGoal 21)) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 0, 1), (0xf0f0f0f0f0f0f0f0, 0, 4)] (by decide +kernel)
    simpa [show (List.map Prod.fst [(0xaaaaaaaaaaaaaaaa, (0 : Row), (1 : Row)), (0xf0f0f0f0f0f0f0f0, (0 : Row), (4 : Row))]).toFinset.card - 1 = 1 by decide +kernel] using hl

def ps_21 : List (Row × Row) := [(5, 1), (5, 4), (17, 1), (17, 16), (20, 4), (20, 16)]
theorem ps_21_ok : pairsOK (graphGoal 21) ps_21 = true := by decide +kernel
def lv_21_3 : Array NodeData := #[
  ([0xaaaaaaaaaaaaaaaa, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000], [])
]
def keys_21_3 : Array (List Sig) := lv_21_3.map Prod.fst
set_option maxHeartbeats 0 in
theorem chk_21_3_0 : checkRange false (vars6 21) (graphGoal 21) ps_21 rs_21 #[] 3 lv_21_3 0 1 = true := by decide +kernel
theorem lv_21_3_ok : ∀ i < keys_21_3.size, ∀ v, keys_21_3[i]? = some v → Impossible (graphGoal 21) 3 v.toFinset := by
  apply level_of_nodes
  intro i hi nd hnd
  have hsz : lv_21_3.size = 1 := by decide +kernel
  exact checkRange_sound (fun h => by cases h) ps_21_ok (by decide) rs_21_ok (fun _ => (fun _ h => by simp at h)) chk_21_3_0 i (by omega) (by omega) nd hnd

theorem imp_21 : Impossible (graphGoal 21) 3 (vars6 21).toFinset := by
  have h := lv_21_3_ok 0 (by decide +kernel) (sortSig (vars6 21)) (by decide +kernel)
  rwa [sortSig_toFinset] at h

theorem low_21 : Lower (vars6 21) (graphGoal 21) 4 := by
  apply lower_impossible (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) _ imp_21
  intro a ha
  have hw : [(0xaaaaaaaaaaaaaaaa, (4 : Row), (5 : Row)), (0xf0f0f0f0f0f0f0f0, (1 : Row), (5 : Row)), (0xffff0000ffff0000, (1 : Row), (17 : Row))].all (fun e => witnessB (graphGoal 21) (vars6 21) e.1 e.2) = true := by decide +kernel
  have hv : vars6 21 = [0xaaaaaaaaaaaaaaaa, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000] := by decide +kernel
  rw [hv] at ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 21) (vars6 21) 0xaaaaaaaaaaaaaaaa (4, 5) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 21) (vars6 21) 0xf0f0f0f0f0f0f0f0 (1, 5) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 21) (vars6 21) 0xffff0000ffff0000 (1, 17) = true)

theorem low_35 : Lower (vars6 35) (graphGoal 35) 2 := by
  have h := lower_count (raw := vars6 35) (T := graphGoal 35) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 32, 33), (0xcccccccccccccccc, 32, 34), (0xffffffff00000000, 1, 33)] (by decide +kernel)
  simpa [show ((List.map Prod.fst [(0xaaaaaaaaaaaaaaaa, (32 : Row), (33 : Row)), (0xcccccccccccccccc, (32 : Row), (34 : Row)), (0xffffffff00000000, (1 : Row), (33 : Row))]).toFinset.card - 1) = 2 by decide +kernel] using h

theorem low_37 : Lower (vars6 37) (graphGoal 37) 2 := by
  have h := lower_count (raw := vars6 37) (T := graphGoal 37) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 4, 5), (0xf0f0f0f0f0f0f0f0, 1, 5), (0xffffffff00000000, 1, 33)] (by decide +kernel)
  simpa [show ((List.map Prod.fst [(0xaaaaaaaaaaaaaaaa, (4 : Row), (5 : Row)), (0xf0f0f0f0f0f0f0f0, (1 : Row), (5 : Row)), (0xffffffff00000000, (1 : Row), (33 : Row))]).toFinset.card - 1) = 2 by decide +kernel] using h

theorem low_41 : Lower (vars6 41) (graphGoal 41) 2 := by
  have h := lower_count (raw := vars6 41) (T := graphGoal 41) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 32, 33), (0xff00ff00ff00ff00, 32, 40), (0xffffffff00000000, 1, 33)] (by decide +kernel)
  simpa [show ((List.map Prod.fst [(0xaaaaaaaaaaaaaaaa, (32 : Row), (33 : Row)), (0xff00ff00ff00ff00, (32 : Row), (40 : Row)), (0xffffffff00000000, (1 : Row), (33 : Row))]).toFinset.card - 1) = 2 by decide +kernel] using h

def rs_42 : Array RestrEntry := #[(2, 0, 1), (8, 0, 1), (32, 0, 1), (0, 2, 1), (0, 8, 1), (0, 32, 1)]
theorem rs_42_ok : ∀ i < rs_42.size, ∀ r, rs_42[i]? = some r → Slice (vars6 42) (graphGoal 42) (subcube r.1 r.2.1) r.2.2 := by
  intro i hi r hr
  have hi' : i < 6 := hi
  interval_cases i <;> simp [rs_42] at hr <;> subst hr
  · exact slice_of_lower 2 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_40
  · exact slice_of_lower 8 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_34
  · exact slice_of_lower 32 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10
  · refine slice_of_lower 0 2 1 (G := fixWord 0 2 (graphGoal 42)) (base := vars6 40) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_count (raw := vars6 40) (T := fixWord 0 2 (graphGoal 42)) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xff00ff00ff00ff00, 0, 8), (0xffffffff00000000, 0, 32)] (by decide +kernel)
    simpa [show (List.map Prod.fst [(0xff00ff00ff00ff00, (0 : Row), (8 : Row)), (0xffffffff00000000, (0 : Row), (32 : Row))]).toFinset.card - 1 = 1 by decide +kernel] using hl
  · refine slice_of_lower 0 8 1 (G := fixWord 0 8 (graphGoal 42)) (base := vars6 34) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_count (raw := vars6 34) (T := fixWord 0 8 (graphGoal 42)) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xcccccccccccccccc, 0, 2), (0xffffffff00000000, 0, 32)] (by decide +kernel)
    simpa [show (List.map Prod.fst [(0xcccccccccccccccc, (0 : Row), (2 : Row)), (0xffffffff00000000, (0 : Row), (32 : Row))]).toFinset.card - 1 = 1 by decide +kernel] using hl
  · refine slice_of_lower 0 32 1 (G := fixWord 0 32 (graphGoal 42)) (base := vars6 10) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_count (raw := vars6 10) (T := fixWord 0 32 (graphGoal 42)) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xcccccccccccccccc, 0, 2), (0xff00ff00ff00ff00, 0, 8)] (by decide +kernel)
    simpa [show (List.map Prod.fst [(0xcccccccccccccccc, (0 : Row), (2 : Row)), (0xff00ff00ff00ff00, (0 : Row), (8 : Row))]).toFinset.card - 1 = 1 by decide +kernel] using hl

def ps_42 : List (Row × Row) := [(10, 2), (10, 8), (34, 2), (34, 32), (40, 8), (40, 32)]
theorem ps_42_ok : pairsOK (graphGoal 42) ps_42 = true := by decide +kernel
def lv_42_3 : Array NodeData := #[
  ([0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffffffff00000000], [])
]
def keys_42_3 : Array (List Sig) := lv_42_3.map Prod.fst
set_option maxHeartbeats 0 in
theorem chk_42_3_0 : checkRange false (vars6 42) (graphGoal 42) ps_42 rs_42 #[] 3 lv_42_3 0 1 = true := by decide +kernel
theorem lv_42_3_ok : ∀ i < keys_42_3.size, ∀ v, keys_42_3[i]? = some v → Impossible (graphGoal 42) 3 v.toFinset := by
  apply level_of_nodes
  intro i hi nd hnd
  have hsz : lv_42_3.size = 1 := by decide +kernel
  exact checkRange_sound (fun h => by cases h) ps_42_ok (by decide) rs_42_ok (fun _ => (fun _ h => by simp at h)) chk_42_3_0 i (by omega) (by omega) nd hnd

theorem imp_42 : Impossible (graphGoal 42) 3 (vars6 42).toFinset := by
  have h := lv_42_3_ok 0 (by decide +kernel) (sortSig (vars6 42)) (by decide +kernel)
  rwa [sortSig_toFinset] at h

theorem low_42 : Lower (vars6 42) (graphGoal 42) 4 := by
  apply lower_impossible (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) _ imp_42
  intro a ha
  have hw : [(0xcccccccccccccccc, (8 : Row), (10 : Row)), (0xff00ff00ff00ff00, (2 : Row), (10 : Row)), (0xffffffff00000000, (2 : Row), (34 : Row))].all (fun e => witnessB (graphGoal 42) (vars6 42) e.1 e.2) = true := by decide +kernel
  have hv : vars6 42 = [0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffffffff00000000] := by decide +kernel
  rw [hv] at ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 42) (vars6 42) 0xcccccccccccccccc (8, 10) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 42) (vars6 42) 0xff00ff00ff00ff00 (2, 10) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 42) (vars6 42) 0xffffffff00000000 (2, 34) = true)

def rs_49 : Array RestrEntry := #[(1, 0, 1), (16, 0, 1), (32, 0, 1), (0, 1, 1), (0, 16, 1), (0, 32, 1)]
theorem rs_49_ok : ∀ i < rs_49.size, ∀ r, rs_49[i]? = some r → Slice (vars6 49) (graphGoal 49) (subcube r.1 r.2.1) r.2.2 := by
  intro i hi r hr
  have hi' : i < 6 := hi
  interval_cases i <;> simp [rs_49] at hr <;> subst hr
  · exact slice_of_lower 1 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_48
  · exact slice_of_lower 16 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_33
  · exact slice_of_lower 32 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_17
  · refine slice_of_lower 0 1 1 (G := fixWord 0 1 (graphGoal 49)) (base := vars6 48) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_count (raw := vars6 48) (T := fixWord 0 1 (graphGoal 49)) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xffff0000ffff0000, 0, 16), (0xffffffff00000000, 0, 32)] (by decide +kernel)
    simpa [show (List.map Prod.fst [(0xffff0000ffff0000, (0 : Row), (16 : Row)), (0xffffffff00000000, (0 : Row), (32 : Row))]).toFinset.card - 1 = 1 by decide +kernel] using hl
  · refine slice_of_lower 0 16 1 (G := fixWord 0 16 (graphGoal 49)) (base := vars6 33) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_count (raw := vars6 33) (T := fixWord 0 16 (graphGoal 49)) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 0, 1), (0xffffffff00000000, 0, 32)] (by decide +kernel)
    simpa [show (List.map Prod.fst [(0xaaaaaaaaaaaaaaaa, (0 : Row), (1 : Row)), (0xffffffff00000000, (0 : Row), (32 : Row))]).toFinset.card - 1 = 1 by decide +kernel] using hl
  · refine slice_of_lower 0 32 1 (G := fixWord 0 32 (graphGoal 49)) (base := vars6 17) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_count (raw := vars6 17) (T := fixWord 0 32 (graphGoal 49)) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 0, 1), (0xffff0000ffff0000, 0, 16)] (by decide +kernel)
    simpa [show (List.map Prod.fst [(0xaaaaaaaaaaaaaaaa, (0 : Row), (1 : Row)), (0xffff0000ffff0000, (0 : Row), (16 : Row))]).toFinset.card - 1 = 1 by decide +kernel] using hl

def ps_49 : List (Row × Row) := [(17, 1), (17, 16), (33, 1), (33, 32), (48, 16), (48, 32)]
theorem ps_49_ok : pairsOK (graphGoal 49) ps_49 = true := by decide +kernel
def lv_49_3 : Array NodeData := #[
  ([0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000, 0xffffffff00000000], [])
]
def keys_49_3 : Array (List Sig) := lv_49_3.map Prod.fst
set_option maxHeartbeats 0 in
theorem chk_49_3_0 : checkRange false (vars6 49) (graphGoal 49) ps_49 rs_49 #[] 3 lv_49_3 0 1 = true := by decide +kernel
theorem lv_49_3_ok : ∀ i < keys_49_3.size, ∀ v, keys_49_3[i]? = some v → Impossible (graphGoal 49) 3 v.toFinset := by
  apply level_of_nodes
  intro i hi nd hnd
  have hsz : lv_49_3.size = 1 := by decide +kernel
  exact checkRange_sound (fun h => by cases h) ps_49_ok (by decide) rs_49_ok (fun _ => (fun _ h => by simp at h)) chk_49_3_0 i (by omega) (by omega) nd hnd

theorem imp_49 : Impossible (graphGoal 49) 3 (vars6 49).toFinset := by
  have h := lv_49_3_ok 0 (by decide +kernel) (sortSig (vars6 49)) (by decide +kernel)
  rwa [sortSig_toFinset] at h

theorem low_49 : Lower (vars6 49) (graphGoal 49) 4 := by
  apply lower_impossible (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) _ imp_49
  intro a ha
  have hw : [(0xaaaaaaaaaaaaaaaa, (16 : Row), (17 : Row)), (0xffff0000ffff0000, (1 : Row), (17 : Row)), (0xffffffff00000000, (1 : Row), (33 : Row))].all (fun e => witnessB (graphGoal 49) (vars6 49) e.1 e.2) = true := by decide +kernel
  have hv : vars6 49 = [0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000, 0xffffffff00000000] := by decide +kernel
  rw [hv] at ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 49) (vars6 49) 0xaaaaaaaaaaaaaaaa (16, 17) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 49) (vars6 49) 0xffff0000ffff0000 (1, 17) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 49) (vars6 49) 0xffffffff00000000 (1, 33) = true)

theorem low_50 : Lower (vars6 50) (graphGoal 50) 2 := by
  have h := lower_count (raw := vars6 50) (T := graphGoal 50) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xcccccccccccccccc, 32, 34), (0xffff0000ffff0000, 32, 48), (0xffffffff00000000, 2, 34)] (by decide +kernel)
  simpa [show ((List.map Prod.fst [(0xcccccccccccccccc, (32 : Row), (34 : Row)), (0xffff0000ffff0000, (32 : Row), (48 : Row)), (0xffffffff00000000, (2 : Row), (34 : Row))]).toFinset.card - 1) = 2 by decide +kernel] using h

theorem low_52 : Lower (vars6 52) (graphGoal 52) 2 := by
  have h := lower_count (raw := vars6 52) (T := graphGoal 52) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xf0f0f0f0f0f0f0f0, 16, 20), (0xffff0000ffff0000, 4, 20), (0xffffffff00000000, 16, 48)] (by decide +kernel)
  simpa [show ((List.map Prod.fst [(0xf0f0f0f0f0f0f0f0, (16 : Row), (20 : Row)), (0xffff0000ffff0000, (4 : Row), (20 : Row)), (0xffffffff00000000, (16 : Row), (48 : Row))]).toFinset.card - 1) = 2 by decide +kernel] using h

theorem low_56 : Lower (vars6 56) (graphGoal 56) 2 := by
  have h := lower_count (raw := vars6 56) (T := graphGoal 56) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xff00ff00ff00ff00, 32, 40), (0xffff0000ffff0000, 32, 48), (0xffffffff00000000, 8, 40)] (by decide +kernel)
  simpa [show ((List.map Prod.fst [(0xff00ff00ff00ff00, (32 : Row), (40 : Row)), (0xffff0000ffff0000, (32 : Row), (48 : Row)), (0xffffffff00000000, (8 : Row), (40 : Row))]).toFinset.card - 1) = 2 by decide +kernel] using h

theorem low_15 : Lower (vars6 15) (graphGoal 15) 3 := by
  have h := lower_count (raw := vars6 15) (T := graphGoal 15) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 4, 5), (0xcccccccccccccccc, 8, 10), (0xf0f0f0f0f0f0f0f0, 1, 5), (0xff00ff00ff00ff00, 2, 10)] (by decide +kernel)
  simpa [show ((List.map Prod.fst [(0xaaaaaaaaaaaaaaaa, (4 : Row), (5 : Row)), (0xcccccccccccccccc, (8 : Row), (10 : Row)), (0xf0f0f0f0f0f0f0f0, (1 : Row), (5 : Row)), (0xff00ff00ff00ff00, (2 : Row), (10 : Row))]).toFinset.card - 1) = 3 by decide +kernel] using h

theorem low_27 : Lower (vars6 27) (graphGoal 27) 3 := by
  have h := lower_count (raw := vars6 27) (T := graphGoal 27) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 16, 17), (0xcccccccccccccccc, 8, 10), (0xff00ff00ff00ff00, 2, 10), (0xffff0000ffff0000, 1, 17)] (by decide +kernel)
  simpa [show ((List.map Prod.fst [(0xaaaaaaaaaaaaaaaa, (16 : Row), (17 : Row)), (0xcccccccccccccccc, (8 : Row), (10 : Row)), (0xff00ff00ff00ff00, (2 : Row), (10 : Row)), (0xffff0000ffff0000, (1 : Row), (17 : Row))]).toFinset.card - 1) = 3 by decide +kernel] using h

theorem low_30 : Lower (vars6 30) (graphGoal 30) 3 := by
  have h := lower_count (raw := vars6 30) (T := graphGoal 30) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xcccccccccccccccc, 8, 10), (0xf0f0f0f0f0f0f0f0, 16, 20), (0xff00ff00ff00ff00, 2, 10), (0xffff0000ffff0000, 4, 20)] (by decide +kernel)
  simpa [show ((List.map Prod.fst [(0xcccccccccccccccc, (8 : Row), (10 : Row)), (0xf0f0f0f0f0f0f0f0, (16 : Row), (20 : Row)), (0xff00ff00ff00ff00, (2 : Row), (10 : Row)), (0xffff0000ffff0000, (4 : Row), (20 : Row))]).toFinset.card - 1) = 3 by decide +kernel] using h

def rs_39 : Array RestrEntry := #[(2, 0, 2), (4, 0, 2), (0, 2, 2), (0, 4, 2), (1, 0, 1), (32, 0, 1), (5, 0, 1), (6, 0, 1), (34, 0, 1), (0, 1, 1), (0, 32, 1)]
theorem rs_39_ok : ∀ i < rs_39.size, ∀ r, rs_39[i]? = some r → Slice (vars6 39) (graphGoal 39) (subcube r.1 r.2.1) r.2.2 := by
  intro i hi r hr
  have hi' : i < 11 := hi
  interval_cases i <;> simp [rs_39] at hr <;> subst hr
  · exact slice_of_lower 2 0 2 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_37
  · exact slice_of_lower 4 0 2 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_35
  · refine slice_of_lower 0 2 2 (G := fixWord 0 2 (graphGoal 39)) (base := vars6 37) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_lift (raw := vars6 37) (base := vars6 5) (T := fixWord 0 2 (graphGoal 39)) (G := graphGoal 5) 32 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xffffffff00000000, 0, 32)] (by decide +kernel) (by decide +kernel) low_5
    simpa [show 1 + (List.map Prod.fst [(0xffffffff00000000, (0 : Row), (32 : Row))]).toFinset.card = 2 by decide +kernel] using hl
  · refine slice_of_lower 0 4 2 (G := fixWord 0 4 (graphGoal 39)) (base := vars6 35) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_lift (raw := vars6 35) (base := vars6 34) (T := fixWord 0 4 (graphGoal 39)) (G := graphGoal 34) 1 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 0, 1)] (by decide +kernel) (by decide +kernel) low_34
    simpa [show 1 + (List.map Prod.fst [(0xaaaaaaaaaaaaaaaa, (0 : Row), (1 : Row))]).toFinset.card = 2 by decide +kernel] using hl
  · exact slice_of_lower 5 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_34
  · exact slice_of_lower 34 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5
  · exact slice_of_lower 5 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_34
  · exact slice_of_lower 6 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_33
  · exact slice_of_lower 34 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5
  · refine slice_of_lower 0 1 1 (G := fixWord 0 1 (graphGoal 39)) (base := vars6 38) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_count (raw := vars6 38) (T := fixWord 0 1 (graphGoal 39)) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xf0f0f0f0f0f0f0f0, 0, 4), (0xffffffff00000000, 0, 32)] (by decide +kernel)
    simpa [show (List.map Prod.fst [(0xf0f0f0f0f0f0f0f0, (0 : Row), (4 : Row)), (0xffffffff00000000, (0 : Row), (32 : Row))]).toFinset.card - 1 = 1 by decide +kernel] using hl
  · refine slice_of_lower 0 32 1 (G := fixWord 0 32 (graphGoal 39)) (base := vars6 7) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_count (raw := vars6 7) (T := fixWord 0 32 (graphGoal 39)) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 0, 1), (0xcccccccccccccccc, 0, 2)] (by decide +kernel)
    simpa [show (List.map Prod.fst [(0xaaaaaaaaaaaaaaaa, (0 : Row), (1 : Row)), (0xcccccccccccccccc, (0 : Row), (2 : Row))]).toFinset.card - 1 = 1 by decide +kernel] using hl

def ps_39 : List (Row × Row) := [(5, 1), (5, 3), (5, 4), (5, 6), (7, 3), (7, 6), (33, 1), (33, 3), (33, 32), (34, 2), (34, 6)]
theorem ps_39_ok : pairsOK (graphGoal 39) ps_39 = true := by decide +kernel
def lv_39_3 : Array NodeData := #[
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000], [])
]
def keys_39_3 : Array (List Sig) := lv_39_3.map Prod.fst
set_option maxHeartbeats 0 in
theorem chk_39_3_0 : checkRange false (vars6 39) (graphGoal 39) ps_39 rs_39 #[] 3 lv_39_3 0 1 = true := by decide +kernel
theorem lv_39_3_ok : ∀ i < keys_39_3.size, ∀ v, keys_39_3[i]? = some v → Impossible (graphGoal 39) 3 v.toFinset := by
  apply level_of_nodes
  intro i hi nd hnd
  have hsz : lv_39_3.size = 1 := by decide +kernel
  exact checkRange_sound (fun h => by cases h) ps_39_ok (by decide) rs_39_ok (fun _ => (fun _ h => by simp at h)) chk_39_3_0 i (by omega) (by omega) nd hnd

theorem imp_39 : Impossible (graphGoal 39) 3 (vars6 39).toFinset := by
  have h := lv_39_3_ok 0 (by decide +kernel) (sortSig (vars6 39)) (by decide +kernel)
  rwa [sortSig_toFinset] at h

theorem low_39 : Lower (vars6 39) (graphGoal 39) 4 := by
  apply lower_impossible (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) _ imp_39
  intro a ha
  have hw : [(0xaaaaaaaaaaaaaaaa, (4 : Row), (5 : Row)), (0xcccccccccccccccc, (32 : Row), (34 : Row)), (0xf0f0f0f0f0f0f0f0, (1 : Row), (5 : Row)), (0xffffffff00000000, (1 : Row), (33 : Row))].all (fun e => witnessB (graphGoal 39) (vars6 39) e.1 e.2) = true := by decide +kernel
  have hv : vars6 39 = [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000] := by decide +kernel
  rw [hv] at ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 39) (vars6 39) 0xaaaaaaaaaaaaaaaa (4, 5) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 39) (vars6 39) 0xcccccccccccccccc (32, 34) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 39) (vars6 39) 0xf0f0f0f0f0f0f0f0 (1, 5) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 39) (vars6 39) 0xffffffff00000000 (1, 33) = true)

def rs_43 : Array RestrEntry := #[(1, 0, 4), (2, 0, 2), (8, 0, 2), (0, 1, 2), (0, 32, 2), (32, 0, 1), (3, 0, 1), (9, 0, 1), (33, 0, 1), (10, 0, 1), (0, 2, 1), (0, 8, 1)]
theorem rs_43_ok : ∀ i < rs_43.size, ∀ r, rs_43[i]? = some r → Slice (vars6 43) (graphGoal 43) (subcube r.1 r.2.1) r.2.2 := by
  intro i hi r hr
  have hi' : i < 12 := hi
  interval_cases i <;> simp [rs_43] at hr <;> subst hr
  · exact slice_of_lower 1 0 4 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_42
  · exact slice_of_lower 2 0 2 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_41
  · exact slice_of_lower 8 0 2 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_35
  · refine slice_of_lower 0 1 2 (G := fixWord 0 1 (graphGoal 43)) (base := vars6 42) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_lift (raw := vars6 42) (base := vars6 10) (T := fixWord 0 1 (graphGoal 43)) (G := graphGoal 10) 32 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xffffffff00000000, 0, 32)] (by decide +kernel) (by decide +kernel) low_10
    simpa [show 1 + (List.map Prod.fst [(0xffffffff00000000, (0 : Row), (32 : Row))]).toFinset.card = 2 by decide +kernel] using hl
  · refine slice_of_lower 0 32 2 (G := fixWord 0 32 (graphGoal 43)) (base := vars6 11) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_count (raw := vars6 11) (T := fixWord 0 32 (graphGoal 43)) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 0, 1), (0xcccccccccccccccc, 0, 2), (0xff00ff00ff00ff00, 0, 8)] (by decide +kernel)
    simpa [show (List.map Prod.fst [(0xaaaaaaaaaaaaaaaa, (0 : Row), (1 : Row)), (0xcccccccccccccccc, (0 : Row), (2 : Row)), (0xff00ff00ff00ff00, (0 : Row), (8 : Row))]).toFinset.card - 1 = 2 by decide +kernel] using hl
  · exact slice_of_lower 33 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10
  · exact slice_of_lower 3 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_40
  · exact slice_of_lower 9 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_34
  · exact slice_of_lower 33 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10
  · exact slice_of_lower 10 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_33
  · refine slice_of_lower 0 2 1 (G := fixWord 0 2 (graphGoal 43)) (base := vars6 41) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_count (raw := vars6 41) (T := fixWord 0 2 (graphGoal 43)) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xff00ff00ff00ff00, 0, 8), (0xffffffff00000000, 0, 32)] (by decide +kernel)
    simpa [show (List.map Prod.fst [(0xff00ff00ff00ff00, (0 : Row), (8 : Row)), (0xffffffff00000000, (0 : Row), (32 : Row))]).toFinset.card - 1 = 1 by decide +kernel] using hl
  · refine slice_of_lower 0 8 1 (G := fixWord 0 8 (graphGoal 43)) (base := vars6 35) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_count (raw := vars6 35) (T := fixWord 0 8 (graphGoal 43)) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xcccccccccccccccc, 0, 2), (0xffffffff00000000, 0, 32)] (by decide +kernel)
    simpa [show (List.map Prod.fst [(0xcccccccccccccccc, (0 : Row), (2 : Row)), (0xffffffff00000000, (0 : Row), (32 : Row))]).toFinset.card - 1 = 1 by decide +kernel] using hl

theorem imp_43 : Impossible (graphGoal 43) 4 (vars6 43).toFinset := by
  have hS := rs_43_ok 0 (by decide) (1, 0, 4) (by decide)
  obtain ⟨f, roots, dom, base, nc, lo⟩ := hS
  intro k hk run
  have nd : (vars6 43).Nodup := by decide +kernel
  have supp : supply (roots.map bvObs) (((vars6 43).map bvObs).map (restrictRows f)) := by
    intro v hv; obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv; obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm; exact base a ha
  have b := projected_bound f (bvList_run run (vars6 43) nd rfl) nc Reach.start supp lo
  have cm := count_constants dom (vars6 43)
  dsimp only at cm b
  have hc : (vars6 43).countP (isMaskedConst (subcube 1 0)) = 1 := by decide +kernel
  omega

theorem low_43 : Lower (vars6 43) (graphGoal 43) 5 := by
  apply lower_impossible (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) _ imp_43
  intro a ha
  have hw : [(0xaaaaaaaaaaaaaaaa, (32 : Row), (33 : Row)), (0xcccccccccccccccc, (8 : Row), (10 : Row)), (0xff00ff00ff00ff00, (2 : Row), (10 : Row)), (0xffffffff00000000, (1 : Row), (33 : Row))].all (fun e => witnessB (graphGoal 43) (vars6 43) e.1 e.2) = true := by decide +kernel
  have hv : vars6 43 = [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffffffff00000000] := by decide +kernel
  rw [hv] at ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 43) (vars6 43) 0xaaaaaaaaaaaaaaaa (32, 33) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 43) (vars6 43) 0xcccccccccccccccc (8, 10) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 43) (vars6 43) 0xff00ff00ff00ff00 (2, 10) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 43) (vars6 43) 0xffffffff00000000 (1, 33) = true)

def rs_45 : Array RestrEntry := #[(4, 0, 2), (8, 0, 2), (0, 4, 2), (0, 8, 2), (1, 0, 1), (32, 0, 1), (5, 0, 1), (12, 0, 1), (40, 0, 1), (0, 1, 1), (0, 32, 1)]
theorem rs_45_ok : ∀ i < rs_45.size, ∀ r, rs_45[i]? = some r → Slice (vars6 45) (graphGoal 45) (subcube r.1 r.2.1) r.2.2 := by
  intro i hi r hr
  have hi' : i < 11 := hi
  interval_cases i <;> simp [rs_45] at hr <;> subst hr
  · exact slice_of_lower 4 0 2 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_41
  · exact slice_of_lower 8 0 2 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_37
  · refine slice_of_lower 0 4 2 (G := fixWord 0 4 (graphGoal 45)) (base := vars6 41) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_lift (raw := vars6 41) (base := vars6 40) (T := fixWord 0 4 (graphGoal 45)) (G := graphGoal 40) 1 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 0, 1)] (by decide +kernel) (by decide +kernel) low_40
    simpa [show 1 + (List.map Prod.fst [(0xaaaaaaaaaaaaaaaa, (0 : Row), (1 : Row))]).toFinset.card = 2 by decide +kernel] using hl
  · refine slice_of_lower 0 8 2 (G := fixWord 0 8 (graphGoal 45)) (base := vars6 37) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_lift (raw := vars6 37) (base := vars6 5) (T := fixWord 0 8 (graphGoal 45)) (G := graphGoal 5) 32 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xffffffff00000000, 0, 32)] (by decide +kernel) (by decide +kernel) low_5
    simpa [show 1 + (List.map Prod.fst [(0xffffffff00000000, (0 : Row), (32 : Row))]).toFinset.card = 2 by decide +kernel] using hl
  · exact slice_of_lower 5 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_40
  · exact slice_of_lower 40 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5
  · exact slice_of_lower 5 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_40
  · exact slice_of_lower 12 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_33
  · exact slice_of_lower 40 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5
  · refine slice_of_lower 0 1 1 (G := fixWord 0 1 (graphGoal 45)) (base := vars6 44) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_count (raw := vars6 44) (T := fixWord 0 1 (graphGoal 45)) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xf0f0f0f0f0f0f0f0, 0, 4), (0xffffffff00000000, 0, 32)] (by decide +kernel)
    simpa [show (List.map Prod.fst [(0xf0f0f0f0f0f0f0f0, (0 : Row), (4 : Row)), (0xffffffff00000000, (0 : Row), (32 : Row))]).toFinset.card - 1 = 1 by decide +kernel] using hl
  · refine slice_of_lower 0 32 1 (G := fixWord 0 32 (graphGoal 45)) (base := vars6 13) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_count (raw := vars6 13) (T := fixWord 0 32 (graphGoal 45)) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 0, 1), (0xff00ff00ff00ff00, 0, 8)] (by decide +kernel)
    simpa [show (List.map Prod.fst [(0xaaaaaaaaaaaaaaaa, (0 : Row), (1 : Row)), (0xff00ff00ff00ff00, (0 : Row), (8 : Row))]).toFinset.card - 1 = 1 by decide +kernel] using hl

def ps_45 : List (Row × Row) := [(5, 1), (5, 4), (5, 9), (5, 12), (13, 9), (13, 12), (33, 1), (33, 9), (33, 32), (40, 8), (40, 12)]
theorem ps_45_ok : pairsOK (graphGoal 45) ps_45 = true := by decide +kernel
def lv_45_3 : Array NodeData := #[
  ([0xaaaaaaaaaaaaaaaa, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffffffff00000000], [])
]
def keys_45_3 : Array (List Sig) := lv_45_3.map Prod.fst
set_option maxHeartbeats 0 in
theorem chk_45_3_0 : checkRange false (vars6 45) (graphGoal 45) ps_45 rs_45 #[] 3 lv_45_3 0 1 = true := by decide +kernel
theorem lv_45_3_ok : ∀ i < keys_45_3.size, ∀ v, keys_45_3[i]? = some v → Impossible (graphGoal 45) 3 v.toFinset := by
  apply level_of_nodes
  intro i hi nd hnd
  have hsz : lv_45_3.size = 1 := by decide +kernel
  exact checkRange_sound (fun h => by cases h) ps_45_ok (by decide) rs_45_ok (fun _ => (fun _ h => by simp at h)) chk_45_3_0 i (by omega) (by omega) nd hnd

theorem imp_45 : Impossible (graphGoal 45) 3 (vars6 45).toFinset := by
  have h := lv_45_3_ok 0 (by decide +kernel) (sortSig (vars6 45)) (by decide +kernel)
  rwa [sortSig_toFinset] at h

theorem low_45 : Lower (vars6 45) (graphGoal 45) 4 := by
  apply lower_impossible (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) _ imp_45
  intro a ha
  have hw : [(0xaaaaaaaaaaaaaaaa, (4 : Row), (5 : Row)), (0xf0f0f0f0f0f0f0f0, (1 : Row), (5 : Row)), (0xff00ff00ff00ff00, (32 : Row), (40 : Row)), (0xffffffff00000000, (1 : Row), (33 : Row))].all (fun e => witnessB (graphGoal 45) (vars6 45) e.1 e.2) = true := by decide +kernel
  have hv : vars6 45 = [0xaaaaaaaaaaaaaaaa, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffffffff00000000] := by decide +kernel
  rw [hv] at ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 45) (vars6 45) 0xaaaaaaaaaaaaaaaa (4, 5) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 45) (vars6 45) 0xf0f0f0f0f0f0f0f0 (1, 5) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 45) (vars6 45) 0xff00ff00ff00ff00 (32, 40) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 45) (vars6 45) 0xffffffff00000000 (1, 33) = true)

def rs_51 : Array RestrEntry := #[(2, 0, 4), (1, 0, 2), (16, 0, 2), (0, 2, 2), (0, 32, 2), (32, 0, 1), (3, 0, 1), (17, 0, 1), (18, 0, 1), (34, 0, 1), (0, 1, 1), (0, 16, 1)]
theorem rs_51_ok : ∀ i < rs_51.size, ∀ r, rs_51[i]? = some r → Slice (vars6 51) (graphGoal 51) (subcube r.1 r.2.1) r.2.2 := by
  intro i hi r hr
  have hi' : i < 12 := hi
  interval_cases i <;> simp [rs_51] at hr <;> subst hr
  · exact slice_of_lower 2 0 4 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_49
  · exact slice_of_lower 1 0 2 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_50
  · exact slice_of_lower 16 0 2 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_35
  · refine slice_of_lower 0 2 2 (G := fixWord 0 2 (graphGoal 51)) (base := vars6 49) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_lift (raw := vars6 49) (base := vars6 17) (T := fixWord 0 2 (graphGoal 51)) (G := graphGoal 17) 32 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xffffffff00000000, 0, 32)] (by decide +kernel) (by decide +kernel) low_17
    simpa [show 1 + (List.map Prod.fst [(0xffffffff00000000, (0 : Row), (32 : Row))]).toFinset.card = 2 by decide +kernel] using hl
  · refine slice_of_lower 0 32 2 (G := fixWord 0 32 (graphGoal 51)) (base := vars6 19) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_count (raw := vars6 19) (T := fixWord 0 32 (graphGoal 51)) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 0, 1), (0xcccccccccccccccc, 0, 2), (0xffff0000ffff0000, 0, 16)] (by decide +kernel)
    simpa [show (List.map Prod.fst [(0xaaaaaaaaaaaaaaaa, (0 : Row), (1 : Row)), (0xcccccccccccccccc, (0 : Row), (2 : Row)), (0xffff0000ffff0000, (0 : Row), (16 : Row))]).toFinset.card - 1 = 2 by decide +kernel] using hl
  · exact slice_of_lower 34 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_17
  · exact slice_of_lower 3 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_48
  · exact slice_of_lower 17 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_34
  · exact slice_of_lower 18 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_33
  · exact slice_of_lower 34 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_17
  · refine slice_of_lower 0 1 1 (G := fixWord 0 1 (graphGoal 51)) (base := vars6 50) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_count (raw := vars6 50) (T := fixWord 0 1 (graphGoal 51)) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xffff0000ffff0000, 0, 16), (0xffffffff00000000, 0, 32)] (by decide +kernel)
    simpa [show (List.map Prod.fst [(0xffff0000ffff0000, (0 : Row), (16 : Row)), (0xffffffff00000000, (0 : Row), (32 : Row))]).toFinset.card - 1 = 1 by decide +kernel] using hl
  · refine slice_of_lower 0 16 1 (G := fixWord 0 16 (graphGoal 51)) (base := vars6 35) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_count (raw := vars6 35) (T := fixWord 0 16 (graphGoal 51)) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 0, 1), (0xffffffff00000000, 0, 32)] (by decide +kernel)
    simpa [show (List.map Prod.fst [(0xaaaaaaaaaaaaaaaa, (0 : Row), (1 : Row)), (0xffffffff00000000, (0 : Row), (32 : Row))]).toFinset.card - 1 = 1 by decide +kernel] using hl

theorem imp_51 : Impossible (graphGoal 51) 4 (vars6 51).toFinset := by
  have hS := rs_51_ok 0 (by decide) (2, 0, 4) (by decide)
  obtain ⟨f, roots, dom, base, nc, lo⟩ := hS
  intro k hk run
  have nd : (vars6 51).Nodup := by decide +kernel
  have supp : supply (roots.map bvObs) (((vars6 51).map bvObs).map (restrictRows f)) := by
    intro v hv; obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv; obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm; exact base a ha
  have b := projected_bound f (bvList_run run (vars6 51) nd rfl) nc Reach.start supp lo
  have cm := count_constants dom (vars6 51)
  dsimp only at cm b
  have hc : (vars6 51).countP (isMaskedConst (subcube 2 0)) = 1 := by decide +kernel
  omega

theorem low_51 : Lower (vars6 51) (graphGoal 51) 5 := by
  apply lower_impossible (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) _ imp_51
  intro a ha
  have hw : [(0xaaaaaaaaaaaaaaaa, (16 : Row), (17 : Row)), (0xcccccccccccccccc, (32 : Row), (34 : Row)), (0xffff0000ffff0000, (1 : Row), (17 : Row)), (0xffffffff00000000, (1 : Row), (33 : Row))].all (fun e => witnessB (graphGoal 51) (vars6 51) e.1 e.2) = true := by decide +kernel
  have hv : vars6 51 = [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xffff0000ffff0000, 0xffffffff00000000] := by decide +kernel
  rw [hv] at ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 51) (vars6 51) 0xaaaaaaaaaaaaaaaa (16, 17) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 51) (vars6 51) 0xcccccccccccccccc (32, 34) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 51) (vars6 51) 0xffff0000ffff0000 (1, 17) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 51) (vars6 51) 0xffffffff00000000 (1, 33) = true)

def rs_53 : Array RestrEntry := #[(4, 0, 4), (32, 0, 4), (1, 0, 2), (16, 0, 2), (0, 1, 2), (0, 16, 2), (5, 0, 1), (33, 0, 1), (20, 0, 1), (36, 0, 1), (48, 0, 1), (0, 4, 1), (0, 32, 1)]
theorem rs_53_ok : ∀ i < rs_53.size, ∀ r, rs_53[i]? = some r → Slice (vars6 53) (graphGoal 53) (subcube r.1 r.2.1) r.2.2 := by
  intro i hi r hr
  have hi' : i < 13 := hi
  interval_cases i <;> simp [rs_53] at hr <;> subst hr
  · exact slice_of_lower 4 0 4 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_49
  · exact slice_of_lower 32 0 4 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_21
  · exact slice_of_lower 1 0 2 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_52
  · exact slice_of_lower 16 0 2 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_37
  · refine slice_of_lower 0 1 2 (G := fixWord 0 1 (graphGoal 53)) (base := vars6 52) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_count (raw := vars6 52) (T := fixWord 0 1 (graphGoal 53)) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xf0f0f0f0f0f0f0f0, 0, 4), (0xffff0000ffff0000, 0, 16), (0xffffffff00000000, 0, 32)] (by decide +kernel)
    simpa [show (List.map Prod.fst [(0xf0f0f0f0f0f0f0f0, (0 : Row), (4 : Row)), (0xffff0000ffff0000, (0 : Row), (16 : Row)), (0xffffffff00000000, (0 : Row), (32 : Row))]).toFinset.card - 1 = 2 by decide +kernel] using hl
  · refine slice_of_lower 0 16 2 (G := fixWord 0 16 (graphGoal 53)) (base := vars6 37) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_count (raw := vars6 37) (T := fixWord 0 16 (graphGoal 53)) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 0, 1), (0xf0f0f0f0f0f0f0f0, 0, 4), (0xffffffff00000000, 0, 32)] (by decide +kernel)
    simpa [show (List.map Prod.fst [(0xaaaaaaaaaaaaaaaa, (0 : Row), (1 : Row)), (0xf0f0f0f0f0f0f0f0, (0 : Row), (4 : Row)), (0xffffffff00000000, (0 : Row), (32 : Row))]).toFinset.card - 1 = 2 by decide +kernel] using hl
  · exact slice_of_lower 5 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_48
  · exact slice_of_lower 33 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_20
  · exact slice_of_lower 20 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_33
  · exact slice_of_lower 36 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_17
  · exact slice_of_lower 48 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5
  · refine slice_of_lower 0 4 1 (G := fixWord 0 4 (graphGoal 53)) (base := vars6 49) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_count (raw := vars6 49) (T := fixWord 0 4 (graphGoal 53)) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 0, 1), (0xffff0000ffff0000, 0, 16)] (by decide +kernel)
    simpa [show (List.map Prod.fst [(0xaaaaaaaaaaaaaaaa, (0 : Row), (1 : Row)), (0xffff0000ffff0000, (0 : Row), (16 : Row))]).toFinset.card - 1 = 1 by decide +kernel] using hl
  · refine slice_of_lower 0 32 1 (G := fixWord 0 32 (graphGoal 53)) (base := vars6 21) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_count (raw := vars6 21) (T := fixWord 0 32 (graphGoal 53)) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 0, 1), (0xffff0000ffff0000, 0, 16)] (by decide +kernel)
    simpa [show (List.map Prod.fst [(0xaaaaaaaaaaaaaaaa, (0 : Row), (1 : Row)), (0xffff0000ffff0000, (0 : Row), (16 : Row))]).toFinset.card - 1 = 1 by decide +kernel] using hl

theorem imp_53 : Impossible (graphGoal 53) 4 (vars6 53).toFinset := by
  have hS := rs_53_ok 0 (by decide) (4, 0, 4) (by decide)
  obtain ⟨f, roots, dom, base, nc, lo⟩ := hS
  intro k hk run
  have nd : (vars6 53).Nodup := by decide +kernel
  have supp : supply (roots.map bvObs) (((vars6 53).map bvObs).map (restrictRows f)) := by
    intro v hv; obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv; obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm; exact base a ha
  have b := projected_bound f (bvList_run run (vars6 53) nd rfl) nc Reach.start supp lo
  have cm := count_constants dom (vars6 53)
  dsimp only at cm b
  have hc : (vars6 53).countP (isMaskedConst (subcube 4 0)) = 1 := by decide +kernel
  omega

theorem low_53 : Lower (vars6 53) (graphGoal 53) 5 := by
  apply lower_impossible (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) _ imp_53
  intro a ha
  have hw : [(0xaaaaaaaaaaaaaaaa, (4 : Row), (5 : Row)), (0xf0f0f0f0f0f0f0f0, (1 : Row), (5 : Row)), (0xffff0000ffff0000, (1 : Row), (17 : Row)), (0xffffffff00000000, (1 : Row), (33 : Row))].all (fun e => witnessB (graphGoal 53) (vars6 53) e.1 e.2) = true := by decide +kernel
  have hv : vars6 53 = [0xaaaaaaaaaaaaaaaa, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000, 0xffffffff00000000] := by decide +kernel
  rw [hv] at ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 53) (vars6 53) 0xaaaaaaaaaaaaaaaa (4, 5) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 53) (vars6 53) 0xf0f0f0f0f0f0f0f0 (1, 5) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 53) (vars6 53) 0xffff0000ffff0000 (1, 17) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 53) (vars6 53) 0xffffffff00000000 (1, 33) = true)

def rs_54 : Array RestrEntry := #[(2, 0, 2), (4, 0, 2), (0, 2, 2), (0, 4, 2), (16, 0, 1), (32, 0, 1), (6, 0, 1), (34, 0, 1), (20, 0, 1), (0, 16, 1), (0, 32, 1)]
theorem rs_54_ok : ∀ i < rs_54.size, ∀ r, rs_54[i]? = some r → Slice (vars6 54) (graphGoal 54) (subcube r.1 r.2.1) r.2.2 := by
  intro i hi r hr
  have hi' : i < 11 := hi
  interval_cases i <;> simp [rs_54] at hr <;> subst hr
  · exact slice_of_lower 2 0 2 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_52
  · exact slice_of_lower 4 0 2 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_50
  · refine slice_of_lower 0 2 2 (G := fixWord 0 2 (graphGoal 54)) (base := vars6 52) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_lift (raw := vars6 52) (base := vars6 20) (T := fixWord 0 2 (graphGoal 54)) (G := graphGoal 20) 32 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xffffffff00000000, 0, 32)] (by decide +kernel) (by decide +kernel) low_20
    simpa [show 1 + (List.map Prod.fst [(0xffffffff00000000, (0 : Row), (32 : Row))]).toFinset.card = 2 by decide +kernel] using hl
  · refine slice_of_lower 0 4 2 (G := fixWord 0 4 (graphGoal 54)) (base := vars6 50) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_lift (raw := vars6 50) (base := vars6 34) (T := fixWord 0 4 (graphGoal 54)) (G := graphGoal 34) 16 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xffff0000ffff0000, 0, 16)] (by decide +kernel) (by decide +kernel) low_34
    simpa [show 1 + (List.map Prod.fst [(0xffff0000ffff0000, (0 : Row), (16 : Row))]).toFinset.card = 2 by decide +kernel] using hl
  · exact slice_of_lower 20 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_34
  · exact slice_of_lower 34 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_20
  · exact slice_of_lower 6 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_48
  · exact slice_of_lower 34 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_20
  · exact slice_of_lower 20 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_34
  · refine slice_of_lower 0 16 1 (G := fixWord 0 16 (graphGoal 54)) (base := vars6 38) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_count (raw := vars6 38) (T := fixWord 0 16 (graphGoal 54)) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xf0f0f0f0f0f0f0f0, 0, 4), (0xffffffff00000000, 0, 32)] (by decide +kernel)
    simpa [show (List.map Prod.fst [(0xf0f0f0f0f0f0f0f0, (0 : Row), (4 : Row)), (0xffffffff00000000, (0 : Row), (32 : Row))]).toFinset.card - 1 = 1 by decide +kernel] using hl
  · refine slice_of_lower 0 32 1 (G := fixWord 0 32 (graphGoal 54)) (base := vars6 22) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_count (raw := vars6 22) (T := fixWord 0 32 (graphGoal 54)) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xcccccccccccccccc, 0, 2), (0xffff0000ffff0000, 0, 16)] (by decide +kernel)
    simpa [show (List.map Prod.fst [(0xcccccccccccccccc, (0 : Row), (2 : Row)), (0xffff0000ffff0000, (0 : Row), (16 : Row))]).toFinset.card - 1 = 1 by decide +kernel] using hl

def ps_54 : List (Row × Row) := [(20, 4), (20, 6), (20, 16), (20, 18), (22, 6), (22, 18), (34, 2), (34, 6), (34, 18), (34, 32), (48, 18), (48, 36)]
theorem ps_54_ok : pairsOK (graphGoal 54) ps_54 = true := by decide +kernel
def lv_54_3 : Array NodeData := #[
  ([0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000, 0xffffffff00000000], [])
]
def keys_54_3 : Array (List Sig) := lv_54_3.map Prod.fst
set_option maxHeartbeats 0 in
theorem chk_54_3_0 : checkRange false (vars6 54) (graphGoal 54) ps_54 rs_54 #[] 3 lv_54_3 0 1 = true := by decide +kernel
theorem lv_54_3_ok : ∀ i < keys_54_3.size, ∀ v, keys_54_3[i]? = some v → Impossible (graphGoal 54) 3 v.toFinset := by
  apply level_of_nodes
  intro i hi nd hnd
  have hsz : lv_54_3.size = 1 := by decide +kernel
  exact checkRange_sound (fun h => by cases h) ps_54_ok (by decide) rs_54_ok (fun _ => (fun _ h => by simp at h)) chk_54_3_0 i (by omega) (by omega) nd hnd

theorem imp_54 : Impossible (graphGoal 54) 3 (vars6 54).toFinset := by
  have h := lv_54_3_ok 0 (by decide +kernel) (sortSig (vars6 54)) (by decide +kernel)
  rwa [sortSig_toFinset] at h

theorem low_54 : Lower (vars6 54) (graphGoal 54) 4 := by
  apply lower_impossible (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) _ imp_54
  intro a ha
  have hw : [(0xcccccccccccccccc, (32 : Row), (34 : Row)), (0xf0f0f0f0f0f0f0f0, (16 : Row), (20 : Row)), (0xffff0000ffff0000, (4 : Row), (20 : Row)), (0xffffffff00000000, (2 : Row), (34 : Row))].all (fun e => witnessB (graphGoal 54) (vars6 54) e.1 e.2) = true := by decide +kernel
  have hv : vars6 54 = [0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000, 0xffffffff00000000] := by decide +kernel
  rw [hv] at ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 54) (vars6 54) 0xcccccccccccccccc (32, 34) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 54) (vars6 54) 0xf0f0f0f0f0f0f0f0 (16, 20) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 54) (vars6 54) 0xffff0000ffff0000 (4, 20) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 54) (vars6 54) 0xffffffff00000000 (2, 34) = true)

def rs_57 : Array RestrEntry := #[(8, 0, 4), (1, 0, 2), (16, 0, 2), (0, 8, 2), (0, 32, 2), (32, 0, 1), (9, 0, 1), (17, 0, 1), (24, 0, 1), (40, 0, 1), (0, 1, 1), (0, 16, 1)]
theorem rs_57_ok : ∀ i < rs_57.size, ∀ r, rs_57[i]? = some r → Slice (vars6 57) (graphGoal 57) (subcube r.1 r.2.1) r.2.2 := by
  intro i hi r hr
  have hi' : i < 12 := hi
  interval_cases i <;> simp [rs_57] at hr <;> subst hr
  · exact slice_of_lower 8 0 4 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_49
  · exact slice_of_lower 1 0 2 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_56
  · exact slice_of_lower 16 0 2 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_41
  · refine slice_of_lower 0 8 2 (G := fixWord 0 8 (graphGoal 57)) (base := vars6 49) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_lift (raw := vars6 49) (base := vars6 17) (T := fixWord 0 8 (graphGoal 57)) (G := graphGoal 17) 32 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xffffffff00000000, 0, 32)] (by decide +kernel) (by decide +kernel) low_17
    simpa [show 1 + (List.map Prod.fst [(0xffffffff00000000, (0 : Row), (32 : Row))]).toFinset.card = 2 by decide +kernel] using hl
  · refine slice_of_lower 0 32 2 (G := fixWord 0 32 (graphGoal 57)) (base := vars6 25) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_count (raw := vars6 25) (T := fixWord 0 32 (graphGoal 57)) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 0, 1), (0xff00ff00ff00ff00, 0, 8), (0xffff0000ffff0000, 0, 16)] (by decide +kernel)
    simpa [show (List.map Prod.fst [(0xaaaaaaaaaaaaaaaa, (0 : Row), (1 : Row)), (0xff00ff00ff00ff00, (0 : Row), (8 : Row)), (0xffff0000ffff0000, (0 : Row), (16 : Row))]).toFinset.card - 1 = 2 by decide +kernel] using hl
  · exact slice_of_lower 40 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_17
  · exact slice_of_lower 9 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_48
  · exact slice_of_lower 17 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_40
  · exact slice_of_lower 24 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_33
  · exact slice_of_lower 40 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_17
  · refine slice_of_lower 0 1 1 (G := fixWord 0 1 (graphGoal 57)) (base := vars6 56) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_count (raw := vars6 56) (T := fixWord 0 1 (graphGoal 57)) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xffff0000ffff0000, 0, 16), (0xffffffff00000000, 0, 32)] (by decide +kernel)
    simpa [show (List.map Prod.fst [(0xffff0000ffff0000, (0 : Row), (16 : Row)), (0xffffffff00000000, (0 : Row), (32 : Row))]).toFinset.card - 1 = 1 by decide +kernel] using hl
  · refine slice_of_lower 0 16 1 (G := fixWord 0 16 (graphGoal 57)) (base := vars6 41) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_count (raw := vars6 41) (T := fixWord 0 16 (graphGoal 57)) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 0, 1), (0xffffffff00000000, 0, 32)] (by decide +kernel)
    simpa [show (List.map Prod.fst [(0xaaaaaaaaaaaaaaaa, (0 : Row), (1 : Row)), (0xffffffff00000000, (0 : Row), (32 : Row))]).toFinset.card - 1 = 1 by decide +kernel] using hl

theorem imp_57 : Impossible (graphGoal 57) 4 (vars6 57).toFinset := by
  have hS := rs_57_ok 0 (by decide) (8, 0, 4) (by decide)
  obtain ⟨f, roots, dom, base, nc, lo⟩ := hS
  intro k hk run
  have nd : (vars6 57).Nodup := by decide +kernel
  have supp : supply (roots.map bvObs) (((vars6 57).map bvObs).map (restrictRows f)) := by
    intro v hv; obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv; obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm; exact base a ha
  have b := projected_bound f (bvList_run run (vars6 57) nd rfl) nc Reach.start supp lo
  have cm := count_constants dom (vars6 57)
  dsimp only at cm b
  have hc : (vars6 57).countP (isMaskedConst (subcube 8 0)) = 1 := by decide +kernel
  omega

theorem low_57 : Lower (vars6 57) (graphGoal 57) 5 := by
  apply lower_impossible (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) _ imp_57
  intro a ha
  have hw : [(0xaaaaaaaaaaaaaaaa, (16 : Row), (17 : Row)), (0xff00ff00ff00ff00, (32 : Row), (40 : Row)), (0xffff0000ffff0000, (1 : Row), (17 : Row)), (0xffffffff00000000, (1 : Row), (33 : Row))].all (fun e => witnessB (graphGoal 57) (vars6 57) e.1 e.2) = true := by decide +kernel
  have hv : vars6 57 = [0xaaaaaaaaaaaaaaaa, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000] := by decide +kernel
  rw [hv] at ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 57) (vars6 57) 0xaaaaaaaaaaaaaaaa (16, 17) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 57) (vars6 57) 0xff00ff00ff00ff00 (32, 40) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 57) (vars6 57) 0xffff0000ffff0000 (1, 17) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 57) (vars6 57) 0xffffffff00000000 (1, 33) = true)

def rs_58 : Array RestrEntry := #[(16, 0, 4), (2, 0, 2), (8, 0, 2), (0, 16, 2), (0, 32, 2), (32, 0, 1), (10, 0, 1), (18, 0, 1), (24, 0, 1), (48, 0, 1), (0, 2, 1), (0, 8, 1)]
theorem rs_58_ok : ∀ i < rs_58.size, ∀ r, rs_58[i]? = some r → Slice (vars6 58) (graphGoal 58) (subcube r.1 r.2.1) r.2.2 := by
  intro i hi r hr
  have hi' : i < 12 := hi
  interval_cases i <;> simp [rs_58] at hr <;> subst hr
  · exact slice_of_lower 16 0 4 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_42
  · exact slice_of_lower 2 0 2 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_56
  · exact slice_of_lower 8 0 2 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_50
  · refine slice_of_lower 0 16 2 (G := fixWord 0 16 (graphGoal 58)) (base := vars6 42) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_lift (raw := vars6 42) (base := vars6 10) (T := fixWord 0 16 (graphGoal 58)) (G := graphGoal 10) 32 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xffffffff00000000, 0, 32)] (by decide +kernel) (by decide +kernel) low_10
    simpa [show 1 + (List.map Prod.fst [(0xffffffff00000000, (0 : Row), (32 : Row))]).toFinset.card = 2 by decide +kernel] using hl
  · refine slice_of_lower 0 32 2 (G := fixWord 0 32 (graphGoal 58)) (base := vars6 26) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_count (raw := vars6 26) (T := fixWord 0 32 (graphGoal 58)) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xcccccccccccccccc, 0, 2), (0xff00ff00ff00ff00, 0, 8), (0xffff0000ffff0000, 0, 16)] (by decide +kernel)
    simpa [show (List.map Prod.fst [(0xcccccccccccccccc, (0 : Row), (2 : Row)), (0xff00ff00ff00ff00, (0 : Row), (8 : Row)), (0xffff0000ffff0000, (0 : Row), (16 : Row))]).toFinset.card - 1 = 2 by decide +kernel] using hl
  · exact slice_of_lower 48 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10
  · exact slice_of_lower 10 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_48
  · exact slice_of_lower 18 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_40
  · exact slice_of_lower 24 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_34
  · exact slice_of_lower 48 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10
  · refine slice_of_lower 0 2 1 (G := fixWord 0 2 (graphGoal 58)) (base := vars6 56) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_count (raw := vars6 56) (T := fixWord 0 2 (graphGoal 58)) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xff00ff00ff00ff00, 0, 8), (0xffffffff00000000, 0, 32)] (by decide +kernel)
    simpa [show (List.map Prod.fst [(0xff00ff00ff00ff00, (0 : Row), (8 : Row)), (0xffffffff00000000, (0 : Row), (32 : Row))]).toFinset.card - 1 = 1 by decide +kernel] using hl
  · refine slice_of_lower 0 8 1 (G := fixWord 0 8 (graphGoal 58)) (base := vars6 50) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_count (raw := vars6 50) (T := fixWord 0 8 (graphGoal 58)) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xcccccccccccccccc, 0, 2), (0xffffffff00000000, 0, 32)] (by decide +kernel)
    simpa [show (List.map Prod.fst [(0xcccccccccccccccc, (0 : Row), (2 : Row)), (0xffffffff00000000, (0 : Row), (32 : Row))]).toFinset.card - 1 = 1 by decide +kernel] using hl

theorem imp_58 : Impossible (graphGoal 58) 4 (vars6 58).toFinset := by
  have hS := rs_58_ok 0 (by decide) (16, 0, 4) (by decide)
  obtain ⟨f, roots, dom, base, nc, lo⟩ := hS
  intro k hk run
  have nd : (vars6 58).Nodup := by decide +kernel
  have supp : supply (roots.map bvObs) (((vars6 58).map bvObs).map (restrictRows f)) := by
    intro v hv; obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv; obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm; exact base a ha
  have b := projected_bound f (bvList_run run (vars6 58) nd rfl) nc Reach.start supp lo
  have cm := count_constants dom (vars6 58)
  dsimp only at cm b
  have hc : (vars6 58).countP (isMaskedConst (subcube 16 0)) = 1 := by decide +kernel
  omega

theorem low_58 : Lower (vars6 58) (graphGoal 58) 5 := by
  apply lower_impossible (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) _ imp_58
  intro a ha
  have hw : [(0xcccccccccccccccc, (8 : Row), (10 : Row)), (0xff00ff00ff00ff00, (2 : Row), (10 : Row)), (0xffff0000ffff0000, (32 : Row), (48 : Row)), (0xffffffff00000000, (2 : Row), (34 : Row))].all (fun e => witnessB (graphGoal 58) (vars6 58) e.1 e.2) = true := by decide +kernel
  have hv : vars6 58 = [0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000] := by decide +kernel
  rw [hv] at ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 58) (vars6 58) 0xcccccccccccccccc (8, 10) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 58) (vars6 58) 0xff00ff00ff00ff00 (2, 10) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 58) (vars6 58) 0xffff0000ffff0000 (32, 48) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 58) (vars6 58) 0xffffffff00000000 (2, 34) = true)

def rs_60 : Array RestrEntry := #[(4, 0, 2), (8, 0, 2), (0, 4, 2), (0, 8, 2), (16, 0, 1), (32, 0, 1), (12, 0, 1), (20, 0, 1), (40, 0, 1), (0, 16, 1), (0, 32, 1)]
theorem rs_60_ok : ∀ i < rs_60.size, ∀ r, rs_60[i]? = some r → Slice (vars6 60) (graphGoal 60) (subcube r.1 r.2.1) r.2.2 := by
  intro i hi r hr
  have hi' : i < 11 := hi
  interval_cases i <;> simp [rs_60] at hr <;> subst hr
  · exact slice_of_lower 4 0 2 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_56
  · exact slice_of_lower 8 0 2 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_52
  · refine slice_of_lower 0 4 2 (G := fixWord 0 4 (graphGoal 60)) (base := vars6 56) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_lift (raw := vars6 56) (base := vars6 40) (T := fixWord 0 4 (graphGoal 60)) (G := graphGoal 40) 16 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xffff0000ffff0000, 0, 16)] (by decide +kernel) (by decide +kernel) low_40
    simpa [show 1 + (List.map Prod.fst [(0xffff0000ffff0000, (0 : Row), (16 : Row))]).toFinset.card = 2 by decide +kernel] using hl
  · refine slice_of_lower 0 8 2 (G := fixWord 0 8 (graphGoal 60)) (base := vars6 52) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_lift (raw := vars6 52) (base := vars6 20) (T := fixWord 0 8 (graphGoal 60)) (G := graphGoal 20) 32 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xffffffff00000000, 0, 32)] (by decide +kernel) (by decide +kernel) low_20
    simpa [show 1 + (List.map Prod.fst [(0xffffffff00000000, (0 : Row), (32 : Row))]).toFinset.card = 2 by decide +kernel] using hl
  · exact slice_of_lower 20 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_40
  · exact slice_of_lower 40 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_20
  · exact slice_of_lower 12 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_48
  · exact slice_of_lower 20 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_40
  · exact slice_of_lower 40 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_20
  · refine slice_of_lower 0 16 1 (G := fixWord 0 16 (graphGoal 60)) (base := vars6 44) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_count (raw := vars6 44) (T := fixWord 0 16 (graphGoal 60)) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xf0f0f0f0f0f0f0f0, 0, 4), (0xffffffff00000000, 0, 32)] (by decide +kernel)
    simpa [show (List.map Prod.fst [(0xf0f0f0f0f0f0f0f0, (0 : Row), (4 : Row)), (0xffffffff00000000, (0 : Row), (32 : Row))]).toFinset.card - 1 = 1 by decide +kernel] using hl
  · refine slice_of_lower 0 32 1 (G := fixWord 0 32 (graphGoal 60)) (base := vars6 28) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_count (raw := vars6 28) (T := fixWord 0 32 (graphGoal 60)) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xff00ff00ff00ff00, 0, 8), (0xffff0000ffff0000, 0, 16)] (by decide +kernel)
    simpa [show (List.map Prod.fst [(0xff00ff00ff00ff00, (0 : Row), (8 : Row)), (0xffff0000ffff0000, (0 : Row), (16 : Row))]).toFinset.card - 1 = 1 by decide +kernel] using hl

def ps_60 : List (Row × Row) := [(20, 4), (20, 12), (20, 16), (20, 24), (20, 36), (28, 12), (28, 24), (40, 8), (40, 12), (40, 32), (48, 24), (48, 36)]
theorem ps_60_ok : pairsOK (graphGoal 60) ps_60 = true := by decide +kernel
def lv_60_3 : Array NodeData := #[
  ([0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [])
]
def keys_60_3 : Array (List Sig) := lv_60_3.map Prod.fst
set_option maxHeartbeats 0 in
theorem chk_60_3_0 : checkRange false (vars6 60) (graphGoal 60) ps_60 rs_60 #[] 3 lv_60_3 0 1 = true := by decide +kernel
theorem lv_60_3_ok : ∀ i < keys_60_3.size, ∀ v, keys_60_3[i]? = some v → Impossible (graphGoal 60) 3 v.toFinset := by
  apply level_of_nodes
  intro i hi nd hnd
  have hsz : lv_60_3.size = 1 := by decide +kernel
  exact checkRange_sound (fun h => by cases h) ps_60_ok (by decide) rs_60_ok (fun _ => (fun _ h => by simp at h)) chk_60_3_0 i (by omega) (by omega) nd hnd

theorem imp_60 : Impossible (graphGoal 60) 3 (vars6 60).toFinset := by
  have h := lv_60_3_ok 0 (by decide +kernel) (sortSig (vars6 60)) (by decide +kernel)
  rwa [sortSig_toFinset] at h

theorem low_60 : Lower (vars6 60) (graphGoal 60) 4 := by
  apply lower_impossible (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) _ imp_60
  intro a ha
  have hw : [(0xf0f0f0f0f0f0f0f0, (16 : Row), (20 : Row)), (0xff00ff00ff00ff00, (32 : Row), (40 : Row)), (0xffff0000ffff0000, (4 : Row), (20 : Row)), (0xffffffff00000000, (8 : Row), (40 : Row))].all (fun e => witnessB (graphGoal 60) (vars6 60) e.1 e.2) = true := by decide +kernel
  have hv : vars6 60 = [0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000] := by decide +kernel
  rw [hv] at ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 60) (vars6 60) 0xf0f0f0f0f0f0f0f0 (16, 20) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 60) (vars6 60) 0xff00ff00ff00ff00 (32, 40) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 60) (vars6 60) 0xffff0000ffff0000 (4, 20) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 60) (vars6 60) 0xffffffff00000000 (8, 40) = true)

def rs_31 : Array RestrEntry := #[(0, 2, 5), (0, 8, 5), (2, 0, 4), (8, 0, 4), (10, 0, 4), (1, 0, 3), (4, 0, 3), (16, 0, 3), (0, 1, 3), (0, 4, 3), (0, 16, 3), (3, 0, 1), (5, 0, 1), (9, 0, 1), (17, 0, 1), (6, 0, 1), (18, 0, 1), (12, 0, 1), (20, 0, 1), (24, 0, 1)]
theorem rs_31_ok : ∀ i < rs_31.size, ∀ r, rs_31[i]? = some r → Slice (vars6 31) (graphGoal 31) (subcube r.1 r.2.1) r.2.2 := by
  intro i hi r hr
  have hi' : i < 20 := hi
  interval_cases i <;> simp [rs_31] at hr <;> subst hr
  · refine slice_of_lower 0 2 5 (G := fixWord 0 2 (graphGoal 31)) (base := vars6 29) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_lift (raw := vars6 29) (base := vars6 21) (T := fixWord 0 2 (graphGoal 31)) (G := graphGoal 21) 8 0 4 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xff00ff00ff00ff00, 0, 8)] (by decide +kernel) (by decide +kernel) low_21
    simpa [show 4 + (List.map Prod.fst [(0xff00ff00ff00ff00, (0 : Row), (8 : Row))]).toFinset.card = 5 by decide +kernel] using hl
  · refine slice_of_lower 0 8 5 (G := fixWord 0 8 (graphGoal 31)) (base := vars6 23) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_lift (raw := vars6 23) (base := vars6 21) (T := fixWord 0 8 (graphGoal 31)) (G := graphGoal 21) 2 0 4 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xcccccccccccccccc, 0, 2)] (by decide +kernel) (by decide +kernel) low_21
    simpa [show 4 + (List.map Prod.fst [(0xcccccccccccccccc, (0 : Row), (2 : Row))]).toFinset.card = 5 by decide +kernel] using hl
  · exact slice_of_lower 10 0 4 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_21
  · exact slice_of_lower 10 0 4 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_21
  · exact slice_of_lower 10 0 4 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_21
  · exact slice_of_lower 1 0 3 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_30
  · exact slice_of_lower 4 0 3 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_27
  · exact slice_of_lower 16 0 3 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15
  · refine slice_of_lower 0 1 3 (G := fixWord 0 1 (graphGoal 31)) (base := vars6 30) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_lift (raw := vars6 30) (base := vars6 10) (T := fixWord 0 1 (graphGoal 31)) (G := graphGoal 10) 20 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xf0f0f0f0f0f0f0f0, 0, 4), (0xffff0000ffff0000, 0, 16)] (by decide +kernel) (by decide +kernel) low_10
    simpa [show 1 + (List.map Prod.fst [(0xf0f0f0f0f0f0f0f0, (0 : Row), (4 : Row)), (0xffff0000ffff0000, (0 : Row), (16 : Row))]).toFinset.card = 3 by decide +kernel] using hl
  · refine slice_of_lower 0 4 3 (G := fixWord 0 4 (graphGoal 31)) (base := vars6 27) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_lift (raw := vars6 27) (base := vars6 10) (T := fixWord 0 4 (graphGoal 31)) (G := graphGoal 10) 17 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 0, 1), (0xffff0000ffff0000, 0, 16)] (by decide +kernel) (by decide +kernel) low_10
    simpa [show 1 + (List.map Prod.fst [(0xaaaaaaaaaaaaaaaa, (0 : Row), (1 : Row)), (0xffff0000ffff0000, (0 : Row), (16 : Row))]).toFinset.card = 3 by decide +kernel] using hl
  · refine slice_of_lower 0 16 3 (G := fixWord 0 16 (graphGoal 31)) (base := vars6 15) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_lift (raw := vars6 15) (base := vars6 10) (T := fixWord 0 16 (graphGoal 31)) (G := graphGoal 10) 5 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 0, 1), (0xf0f0f0f0f0f0f0f0, 0, 4)] (by decide +kernel) (by decide +kernel) low_10
    simpa [show 1 + (List.map Prod.fst [(0xaaaaaaaaaaaaaaaa, (0 : Row), (1 : Row)), (0xf0f0f0f0f0f0f0f0, (0 : Row), (4 : Row))]).toFinset.card = 3 by decide +kernel] using hl
  · exact slice_of_lower 11 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_20
  · exact slice_of_lower 21 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10
  · exact slice_of_lower 11 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_20
  · exact slice_of_lower 21 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10
  · exact slice_of_lower 14 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_17
  · exact slice_of_lower 26 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5
  · exact slice_of_lower 14 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_17
  · exact slice_of_lower 21 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10
  · exact slice_of_lower 26 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5

theorem imp_31 : Impossible (graphGoal 31) 5 (vars6 31).toFinset := by
  have hS := rs_31_ok 0 (by decide) (0, 2, 5) (by decide)
  obtain ⟨f, roots, dom, base, nc, lo⟩ := hS
  intro k hk run
  have nd : (vars6 31).Nodup := by decide +kernel
  have supp : supply (roots.map bvObs) (((vars6 31).map bvObs).map (restrictRows f)) := by
    intro v hv; obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv; obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm; exact base a ha
  have b := projected_bound f (bvList_run run (vars6 31) nd rfl) nc Reach.start supp lo
  have cm := count_constants dom (vars6 31)
  dsimp only at cm b
  have hc : (vars6 31).countP (isMaskedConst (subcube 0 2)) = 1 := by decide +kernel
  omega

theorem low_31 : Lower (vars6 31) (graphGoal 31) 6 := by
  apply lower_impossible (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) _ imp_31
  intro a ha
  have hw : [(0xaaaaaaaaaaaaaaaa, (4 : Row), (5 : Row)), (0xcccccccccccccccc, (8 : Row), (10 : Row)), (0xf0f0f0f0f0f0f0f0, (1 : Row), (5 : Row)), (0xff00ff00ff00ff00, (2 : Row), (10 : Row)), (0xffff0000ffff0000, (1 : Row), (17 : Row))].all (fun e => witnessB (graphGoal 31) (vars6 31) e.1 e.2) = true := by decide +kernel
  have hv : vars6 31 = [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000] := by decide +kernel
  rw [hv] at ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 31) (vars6 31) 0xaaaaaaaaaaaaaaaa (4, 5) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 31) (vars6 31) 0xcccccccccccccccc (8, 10) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 31) (vars6 31) 0xf0f0f0f0f0f0f0f0 (1, 5) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 31) (vars6 31) 0xff00ff00ff00ff00 (2, 10) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 31) (vars6 31) 0xffff0000ffff0000 (1, 17) = true)

def rs_47 : Array RestrEntry := #[(4, 0, 5), (0, 4, 5), (1, 0, 4), (2, 0, 4), (8, 0, 4), (5, 0, 4), (32, 0, 3), (0, 1, 3), (0, 2, 3), (0, 8, 3), (6, 0, 2), (10, 0, 2), (12, 0, 2), (0, 32, 2), (3, 0, 1), (9, 0, 1), (33, 0, 1), (34, 0, 1), (36, 0, 1), (40, 0, 1)]
theorem rs_47_ok : ∀ i < rs_47.size, ∀ r, rs_47[i]? = some r → Slice (vars6 47) (graphGoal 47) (subcube r.1 r.2.1) r.2.2 := by
  intro i hi r hr
  have hi' : i < 20 := hi
  interval_cases i <;> simp [rs_47] at hr <;> subst hr
  · exact slice_of_lower 4 0 5 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_43
  · refine slice_of_lower 0 4 5 (G := fixWord 0 4 (graphGoal 47)) (base := vars6 43) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_lift (raw := vars6 43) (base := vars6 42) (T := fixWord 0 4 (graphGoal 47)) (G := graphGoal 42) 1 0 4 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 0, 1)] (by decide +kernel) (by decide +kernel) low_42
    simpa [show 4 + (List.map Prod.fst [(0xaaaaaaaaaaaaaaaa, (0 : Row), (1 : Row))]).toFinset.card = 5 by decide +kernel] using hl
  · exact slice_of_lower 5 0 4 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_42
  · exact slice_of_lower 2 0 4 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_45
  · exact slice_of_lower 8 0 4 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_39
  · exact slice_of_lower 5 0 4 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_42
  · exact slice_of_lower 32 0 3 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15
  · refine slice_of_lower 0 1 3 (G := fixWord 0 1 (graphGoal 47)) (base := vars6 46) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_lift (raw := vars6 46) (base := vars6 10) (T := fixWord 0 1 (graphGoal 47)) (G := graphGoal 10) 36 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xf0f0f0f0f0f0f0f0, 0, 4), (0xffffffff00000000, 0, 32)] (by decide +kernel) (by decide +kernel) low_10
    simpa [show 1 + (List.map Prod.fst [(0xf0f0f0f0f0f0f0f0, (0 : Row), (4 : Row)), (0xffffffff00000000, (0 : Row), (32 : Row))]).toFinset.card = 3 by decide +kernel] using hl
  · refine slice_of_lower 0 2 3 (G := fixWord 0 2 (graphGoal 47)) (base := vars6 45) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_lift (raw := vars6 45) (base := vars6 5) (T := fixWord 0 2 (graphGoal 47)) (G := graphGoal 5) 40 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xff00ff00ff00ff00, 0, 8), (0xffffffff00000000, 0, 32)] (by decide +kernel) (by decide +kernel) low_5
    simpa [show 1 + (List.map Prod.fst [(0xff00ff00ff00ff00, (0 : Row), (8 : Row)), (0xffffffff00000000, (0 : Row), (32 : Row))]).toFinset.card = 3 by decide +kernel] using hl
  · refine slice_of_lower 0 8 3 (G := fixWord 0 8 (graphGoal 47)) (base := vars6 39) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_lift (raw := vars6 39) (base := vars6 5) (T := fixWord 0 8 (graphGoal 47)) (G := graphGoal 5) 34 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xcccccccccccccccc, 0, 2), (0xffffffff00000000, 0, 32)] (by decide +kernel) (by decide +kernel) low_5
    simpa [show 1 + (List.map Prod.fst [(0xcccccccccccccccc, (0 : Row), (2 : Row)), (0xffffffff00000000, (0 : Row), (32 : Row))]).toFinset.card = 3 by decide +kernel] using hl
  · exact slice_of_lower 6 0 2 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_41
  · exact slice_of_lower 10 0 2 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_37
  · exact slice_of_lower 12 0 2 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_35
  · refine slice_of_lower 0 32 2 (G := fixWord 0 32 (graphGoal 47)) (base := vars6 15) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_count (raw := vars6 15) (T := fixWord 0 32 (graphGoal 47)) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 0, 1), (0xcccccccccccccccc, 0, 2), (0xff00ff00ff00ff00, 0, 8)] (by decide +kernel)
    simpa [show (List.map Prod.fst [(0xaaaaaaaaaaaaaaaa, (0 : Row), (1 : Row)), (0xcccccccccccccccc, (0 : Row), (2 : Row)), (0xff00ff00ff00ff00, (0 : Row), (8 : Row))]).toFinset.card - 1 = 2 by decide +kernel] using hl
  · exact slice_of_lower 7 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_40
  · exact slice_of_lower 13 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_34
  · exact slice_of_lower 37 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10
  · exact slice_of_lower 42 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5
  · exact slice_of_lower 37 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10
  · exact slice_of_lower 42 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5

def ps_47 : List (Row × Row) := [(5, 1), (5, 4), (7, 3), (7, 6), (7, 12), (10, 2), (10, 3), (10, 6), (10, 8), (10, 9), (10, 12), (11, 3), (11, 9), (13, 9), (13, 12), (14, 6), (14, 12), (33, 1), (33, 3), (33, 9), (33, 32), (34, 0), (34, 2), (34, 6), (34, 32), (38, 6), (40, 0), (40, 8), (40, 12), (40, 32)]
theorem ps_47_ok : pairsOK (graphGoal 47) ps_47 = true := by decide +kernel
def lv_47_4 : Array NodeData := #[
  ([0xff00ff00cc00cc, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000], []),
  ([0x3333333333003300, 0xaaaaaaaaaaaaaaaa, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffffffff00000000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccc00cc00, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffffffff00000000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00cc00cc00, 0xffffffff00000000], [])
]
def keys_47_4 : Array (List Sig) := lv_47_4.map Prod.fst
set_option maxHeartbeats 0 in
theorem chk_47_4_0 : checkRange false (vars6 47) (graphGoal 47) ps_47 rs_47 #[] 4 lv_47_4 0 4 = true := by decide +kernel
theorem lv_47_4_ok : ∀ i < keys_47_4.size, ∀ v, keys_47_4[i]? = some v → Impossible (graphGoal 47) 4 v.toFinset := by
  apply level_of_nodes
  intro i hi nd hnd
  have hsz : lv_47_4.size = 4 := by decide +kernel
  exact checkRange_sound (fun h => by cases h) ps_47_ok (by decide) rs_47_ok (fun _ => (fun _ h => by simp at h)) chk_47_4_0 i (by omega) (by omega) nd hnd

def lv_47_5 : Array NodeData := #[
  ([0xff00ff00000000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffffffff00000000], [(0, [(3, 0xff00ff00ff00ff00, 0xffffffff00000000)]), (1, [(3, 0xff00ff00ff00ff00, 0xffffffff00000000)])]),
  ([0x3333333300000000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffffffff00000000], [(0, [(3, 0xcccccccccccccccc, 0xffffffff00000000)]), (1, [(3, 0xcccccccccccccccc, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffccffccffccffcc, 0xffffffff00000000], [(3, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffffffff00000000, 0xffffffffcccccccc], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffffffff00000000, 0xffffffffff00ff00], [])
]
def keys_47_5 : Array (List Sig) := lv_47_5.map Prod.fst
set_option maxHeartbeats 0 in
theorem chk_47_5_0 : checkRange false (vars6 47) (graphGoal 47) ps_47 rs_47 keys_47_4 5 lv_47_5 0 5 = true := by decide +kernel
theorem lv_47_5_ok : ∀ i < keys_47_5.size, ∀ v, keys_47_5[i]? = some v → Impossible (graphGoal 47) 5 v.toFinset := by
  apply level_of_nodes
  intro i hi nd hnd
  have hsz : lv_47_5.size = 5 := by decide +kernel
  exact checkRange_sound (fun h => by cases h) ps_47_ok (by decide) rs_47_ok (fun _ => lv_47_4_ok) chk_47_5_0 i (by omega) (by omega) nd hnd

def lv_47_6 : Array NodeData := #[
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffffffff00000000], [(1, []), (2, []), (3, []), (4, []), (5, [])])
]
def keys_47_6 : Array (List Sig) := lv_47_6.map Prod.fst
set_option maxHeartbeats 0 in
theorem chk_47_6_0 : checkRange false (vars6 47) (graphGoal 47) ps_47 rs_47 keys_47_5 6 lv_47_6 0 1 = true := by decide +kernel
theorem lv_47_6_ok : ∀ i < keys_47_6.size, ∀ v, keys_47_6[i]? = some v → Impossible (graphGoal 47) 6 v.toFinset := by
  apply level_of_nodes
  intro i hi nd hnd
  have hsz : lv_47_6.size = 1 := by decide +kernel
  exact checkRange_sound (fun h => by cases h) ps_47_ok (by decide) rs_47_ok (fun _ => lv_47_5_ok) chk_47_6_0 i (by omega) (by omega) nd hnd

theorem imp_47 : Impossible (graphGoal 47) 6 (vars6 47).toFinset := by
  have h := lv_47_6_ok 0 (by decide +kernel) (sortSig (vars6 47)) (by decide +kernel)
  rwa [sortSig_toFinset] at h

theorem low_47 : Lower (vars6 47) (graphGoal 47) 7 := by
  apply lower_impossible (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) _ imp_47
  intro a ha
  have hw : [(0xaaaaaaaaaaaaaaaa, (4 : Row), (5 : Row)), (0xcccccccccccccccc, (8 : Row), (10 : Row)), (0xf0f0f0f0f0f0f0f0, (1 : Row), (5 : Row)), (0xff00ff00ff00ff00, (2 : Row), (10 : Row)), (0xffffffff00000000, (1 : Row), (33 : Row))].all (fun e => witnessB (graphGoal 47) (vars6 47) e.1 e.2) = true := by decide +kernel
  have hv : vars6 47 = [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffffffff00000000] := by decide +kernel
  rw [hv] at ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 47) (vars6 47) 0xaaaaaaaaaaaaaaaa (4, 5) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 47) (vars6 47) 0xcccccccccccccccc (8, 10) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 47) (vars6 47) 0xf0f0f0f0f0f0f0f0 (1, 5) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 47) (vars6 47) 0xff00ff00ff00ff00 (2, 10) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 47) (vars6 47) 0xffffffff00000000 (1, 33) = true)

def rs_55 : Array RestrEntry := #[(2, 0, 5), (4, 0, 5), (0, 2, 5), (1, 0, 4), (16, 0, 4), (32, 0, 4), (6, 0, 4), (34, 0, 4), (0, 4, 3), (3, 0, 2), (5, 0, 2), (18, 0, 2), (20, 0, 2), (0, 1, 2), (0, 16, 2), (0, 32, 2), (17, 0, 1), (33, 0, 1), (36, 0, 1), (48, 0, 1)]
theorem rs_55_ok : ∀ i < rs_55.size, ∀ r, rs_55[i]? = some r → Slice (vars6 55) (graphGoal 55) (subcube r.1 r.2.1) r.2.2 := by
  intro i hi r hr
  have hi' : i < 20 := hi
  interval_cases i <;> simp [rs_55] at hr <;> subst hr
  · exact slice_of_lower 2 0 5 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_53
  · exact slice_of_lower 4 0 5 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_51
  · refine slice_of_lower 0 2 5 (G := fixWord 0 2 (graphGoal 55)) (base := vars6 53) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_lift (raw := vars6 53) (base := vars6 21) (T := fixWord 0 2 (graphGoal 55)) (G := graphGoal 21) 32 0 4 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xffffffff00000000, 0, 32)] (by decide +kernel) (by decide +kernel) low_21
    simpa [show 4 + (List.map Prod.fst [(0xffffffff00000000, (0 : Row), (32 : Row))]).toFinset.card = 5 by decide +kernel] using hl
  · exact slice_of_lower 1 0 4 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_54
  · exact slice_of_lower 16 0 4 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_39
  · exact slice_of_lower 34 0 4 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_21
  · exact slice_of_lower 6 0 4 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_49
  · exact slice_of_lower 34 0 4 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_21
  · refine slice_of_lower 0 4 3 (G := fixWord 0 4 (graphGoal 55)) (base := vars6 51) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_lift (raw := vars6 51) (base := vars6 34) (T := fixWord 0 4 (graphGoal 55)) (G := graphGoal 34) 17 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 0, 1), (0xffff0000ffff0000, 0, 16)] (by decide +kernel) (by decide +kernel) low_34
    simpa [show 1 + (List.map Prod.fst [(0xaaaaaaaaaaaaaaaa, (0 : Row), (1 : Row)), (0xffff0000ffff0000, (0 : Row), (16 : Row))]).toFinset.card = 3 by decide +kernel] using hl
  · exact slice_of_lower 3 0 2 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_52
  · exact slice_of_lower 5 0 2 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_50
  · exact slice_of_lower 18 0 2 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_37
  · exact slice_of_lower 20 0 2 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_35
  · refine slice_of_lower 0 1 2 (G := fixWord 0 1 (graphGoal 55)) (base := vars6 54) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_count (raw := vars6 54) (T := fixWord 0 1 (graphGoal 55)) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xf0f0f0f0f0f0f0f0, 0, 4), (0xffff0000ffff0000, 0, 16), (0xffffffff00000000, 0, 32)] (by decide +kernel)
    simpa [show (List.map Prod.fst [(0xf0f0f0f0f0f0f0f0, (0 : Row), (4 : Row)), (0xffff0000ffff0000, (0 : Row), (16 : Row)), (0xffffffff00000000, (0 : Row), (32 : Row))]).toFinset.card - 1 = 2 by decide +kernel] using hl
  · refine slice_of_lower 0 16 2 (G := fixWord 0 16 (graphGoal 55)) (base := vars6 39) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_count (raw := vars6 39) (T := fixWord 0 16 (graphGoal 55)) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 0, 1), (0xf0f0f0f0f0f0f0f0, 0, 4), (0xffffffff00000000, 0, 32)] (by decide +kernel)
    simpa [show (List.map Prod.fst [(0xaaaaaaaaaaaaaaaa, (0 : Row), (1 : Row)), (0xf0f0f0f0f0f0f0f0, (0 : Row), (4 : Row)), (0xffffffff00000000, (0 : Row), (32 : Row))]).toFinset.card - 1 = 2 by decide +kernel] using hl
  · refine slice_of_lower 0 32 2 (G := fixWord 0 32 (graphGoal 55)) (base := vars6 23) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_count (raw := vars6 23) (T := fixWord 0 32 (graphGoal 55)) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 0, 1), (0xcccccccccccccccc, 0, 2), (0xffff0000ffff0000, 0, 16)] (by decide +kernel)
    simpa [show (List.map Prod.fst [(0xaaaaaaaaaaaaaaaa, (0 : Row), (1 : Row)), (0xcccccccccccccccc, (0 : Row), (2 : Row)), (0xffff0000ffff0000, (0 : Row), (16 : Row))]).toFinset.card - 1 = 2 by decide +kernel] using hl
  · exact slice_of_lower 21 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_34
  · exact slice_of_lower 35 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_20
  · exact slice_of_lower 38 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_17
  · exact slice_of_lower 50 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5

def ps_55 : List (Row × Row) := [(5, 1), (5, 2), (5, 4), (7, 3), (7, 6), (17, 1), (17, 3), (17, 16), (17, 18), (19, 3), (19, 18), (20, 4), (20, 16), (20, 32), (33, 1), (33, 32), (34, 2), (34, 6), (34, 32), (38, 6), (38, 36), (48, 16), (48, 32)]
theorem ps_55_ok : pairsOK (graphGoal 55) ps_55 = true := by decide +kernel
def lv_55_4 : Array NodeData := #[
  ([0xf0f0a0a0f0f0a0a, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xffff0000ffff0000, 0xffffffff00000000], [])
]
def keys_55_4 : Array (List Sig) := lv_55_4.map Prod.fst
set_option maxHeartbeats 0 in
theorem chk_55_4_0 : checkRange false (vars6 55) (graphGoal 55) ps_55 rs_55 #[] 4 lv_55_4 0 1 = true := by decide +kernel
theorem lv_55_4_ok : ∀ i < keys_55_4.size, ∀ v, keys_55_4[i]? = some v → Impossible (graphGoal 55) 4 v.toFinset := by
  apply level_of_nodes
  intro i hi nd hnd
  have hsz : lv_55_4.size = 1 := by decide +kernel
  exact checkRange_sound (fun h => by cases h) ps_55_ok (by decide) rs_55_ok (fun _ => (fun _ h => by simp at h)) chk_55_4_0 i (by omega) (by omega) nd hnd

def lv_55_5 : Array NodeData := #[
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000, 0xffffaaaaffffaaaa, 0xffffffff00000000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000)]), (1, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000)]), (2, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000)]), (3, [])])
]
def keys_55_5 : Array (List Sig) := lv_55_5.map Prod.fst
set_option maxHeartbeats 0 in
theorem chk_55_5_0 : checkRange false (vars6 55) (graphGoal 55) ps_55 rs_55 keys_55_4 5 lv_55_5 0 1 = true := by decide +kernel
theorem lv_55_5_ok : ∀ i < keys_55_5.size, ∀ v, keys_55_5[i]? = some v → Impossible (graphGoal 55) 5 v.toFinset := by
  apply level_of_nodes
  intro i hi nd hnd
  have hsz : lv_55_5.size = 1 := by decide +kernel
  exact checkRange_sound (fun h => by cases h) ps_55_ok (by decide) rs_55_ok (fun _ => lv_55_4_ok) chk_55_5_0 i (by omega) (by omega) nd hnd

def lv_55_6 : Array NodeData := #[
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000, 0xffffffff00000000], [(0, []), (1, []), (2, []), (3, []), (4, []), (7, [])])
]
def keys_55_6 : Array (List Sig) := lv_55_6.map Prod.fst
set_option maxHeartbeats 0 in
theorem chk_55_6_0 : checkRange false (vars6 55) (graphGoal 55) ps_55 rs_55 keys_55_5 6 lv_55_6 0 1 = true := by decide +kernel
theorem lv_55_6_ok : ∀ i < keys_55_6.size, ∀ v, keys_55_6[i]? = some v → Impossible (graphGoal 55) 6 v.toFinset := by
  apply level_of_nodes
  intro i hi nd hnd
  have hsz : lv_55_6.size = 1 := by decide +kernel
  exact checkRange_sound (fun h => by cases h) ps_55_ok (by decide) rs_55_ok (fun _ => lv_55_5_ok) chk_55_6_0 i (by omega) (by omega) nd hnd

theorem imp_55 : Impossible (graphGoal 55) 6 (vars6 55).toFinset := by
  have h := lv_55_6_ok 0 (by decide +kernel) (sortSig (vars6 55)) (by decide +kernel)
  rwa [sortSig_toFinset] at h

theorem low_55 : Lower (vars6 55) (graphGoal 55) 7 := by
  apply lower_impossible (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) _ imp_55
  intro a ha
  have hw : [(0xaaaaaaaaaaaaaaaa, (4 : Row), (5 : Row)), (0xcccccccccccccccc, (32 : Row), (34 : Row)), (0xf0f0f0f0f0f0f0f0, (1 : Row), (5 : Row)), (0xffff0000ffff0000, (1 : Row), (17 : Row)), (0xffffffff00000000, (1 : Row), (33 : Row))].all (fun e => witnessB (graphGoal 55) (vars6 55) e.1 e.2) = true := by decide +kernel
  have hv : vars6 55 = [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000, 0xffffffff00000000] := by decide +kernel
  rw [hv] at ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 55) (vars6 55) 0xaaaaaaaaaaaaaaaa (4, 5) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 55) (vars6 55) 0xcccccccccccccccc (32, 34) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 55) (vars6 55) 0xf0f0f0f0f0f0f0f0 (1, 5) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 55) (vars6 55) 0xffff0000ffff0000 (1, 17) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 55) (vars6 55) 0xffffffff00000000 (1, 33) = true)

def rs_59 : Array RestrEntry := #[(1, 0, 5), (2, 0, 5), (8, 0, 5), (16, 0, 5), (17, 0, 4), (10, 0, 4), (32, 0, 3), (0, 1, 3), (0, 2, 3), (0, 8, 3), (0, 16, 3), (0, 32, 3), (3, 0, 2), (9, 0, 2), (18, 0, 2), (24, 0, 2), (33, 0, 1), (34, 0, 1), (40, 0, 1), (48, 0, 1)]
theorem rs_59_ok : ∀ i < rs_59.size, ∀ r, rs_59[i]? = some r → Slice (vars6 59) (graphGoal 59) (subcube r.1 r.2.1) r.2.2 := by
  intro i hi r hr
  have hi' : i < 20 := hi
  interval_cases i <;> simp [rs_59] at hr <;> subst hr
  · exact slice_of_lower 1 0 5 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_58
  · exact slice_of_lower 2 0 5 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_57
  · exact slice_of_lower 8 0 5 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_51
  · exact slice_of_lower 16 0 5 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_43
  · exact slice_of_lower 17 0 4 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_42
  · exact slice_of_lower 10 0 4 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_49
  · exact slice_of_lower 32 0 3 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_27
  · refine slice_of_lower 0 1 3 (G := fixWord 0 1 (graphGoal 59)) (base := vars6 58) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_lift (raw := vars6 58) (base := vars6 10) (T := fixWord 0 1 (graphGoal 59)) (G := graphGoal 10) 48 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xffff0000ffff0000, 0, 16), (0xffffffff00000000, 0, 32)] (by decide +kernel) (by decide +kernel) low_10
    simpa [show 1 + (List.map Prod.fst [(0xffff0000ffff0000, (0 : Row), (16 : Row)), (0xffffffff00000000, (0 : Row), (32 : Row))]).toFinset.card = 3 by decide +kernel] using hl
  · refine slice_of_lower 0 2 3 (G := fixWord 0 2 (graphGoal 59)) (base := vars6 57) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_lift (raw := vars6 57) (base := vars6 17) (T := fixWord 0 2 (graphGoal 59)) (G := graphGoal 17) 40 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xff00ff00ff00ff00, 0, 8), (0xffffffff00000000, 0, 32)] (by decide +kernel) (by decide +kernel) low_17
    simpa [show 1 + (List.map Prod.fst [(0xff00ff00ff00ff00, (0 : Row), (8 : Row)), (0xffffffff00000000, (0 : Row), (32 : Row))]).toFinset.card = 3 by decide +kernel] using hl
  · refine slice_of_lower 0 8 3 (G := fixWord 0 8 (graphGoal 59)) (base := vars6 51) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_lift (raw := vars6 51) (base := vars6 17) (T := fixWord 0 8 (graphGoal 59)) (G := graphGoal 17) 34 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xcccccccccccccccc, 0, 2), (0xffffffff00000000, 0, 32)] (by decide +kernel) (by decide +kernel) low_17
    simpa [show 1 + (List.map Prod.fst [(0xcccccccccccccccc, (0 : Row), (2 : Row)), (0xffffffff00000000, (0 : Row), (32 : Row))]).toFinset.card = 3 by decide +kernel] using hl
  · refine slice_of_lower 0 16 3 (G := fixWord 0 16 (graphGoal 59)) (base := vars6 43) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_lift (raw := vars6 43) (base := vars6 10) (T := fixWord 0 16 (graphGoal 59)) (G := graphGoal 10) 33 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 0, 1), (0xffffffff00000000, 0, 32)] (by decide +kernel) (by decide +kernel) low_10
    simpa [show 1 + (List.map Prod.fst [(0xaaaaaaaaaaaaaaaa, (0 : Row), (1 : Row)), (0xffffffff00000000, (0 : Row), (32 : Row))]).toFinset.card = 3 by decide +kernel] using hl
  · refine slice_of_lower 0 32 3 (G := fixWord 0 32 (graphGoal 59)) (base := vars6 27) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_count (raw := vars6 27) (T := fixWord 0 32 (graphGoal 59)) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 0, 1), (0xcccccccccccccccc, 0, 2), (0xff00ff00ff00ff00, 0, 8), (0xffff0000ffff0000, 0, 16)] (by decide +kernel)
    simpa [show (List.map Prod.fst [(0xaaaaaaaaaaaaaaaa, (0 : Row), (1 : Row)), (0xcccccccccccccccc, (0 : Row), (2 : Row)), (0xff00ff00ff00ff00, (0 : Row), (8 : Row)), (0xffff0000ffff0000, (0 : Row), (16 : Row))]).toFinset.card - 1 = 3 by decide +kernel] using hl
  · exact slice_of_lower 3 0 2 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_56
  · exact slice_of_lower 9 0 2 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_50
  · exact slice_of_lower 18 0 2 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_41
  · exact slice_of_lower 24 0 2 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_35
  · exact slice_of_lower 49 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10
  · exact slice_of_lower 42 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_17
  · exact slice_of_lower 42 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_17
  · exact slice_of_lower 49 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10

def ps_59 : List (Row × Row) := [(10, 2), (10, 3), (10, 8), (10, 9), (10, 16), (10, 18), (11, 3), (11, 9), (17, 1), (17, 3), (17, 9), (17, 16), (19, 3), (19, 18), (25, 9), (25, 24), (26, 18), (26, 24), (33, 0), (33, 1), (33, 3), (33, 8), (33, 9), (33, 32), (34, 0), (34, 2), (34, 3), (34, 16), (34, 18), (34, 32), (35, 3), (40, 0), (40, 8), (40, 9), (40, 24), (40, 32), (41, 9), (48, 0), (48, 16), (48, 18), (48, 24), (48, 32), (50, 18), (56, 24)]
theorem ps_59_ok : pairsOK (graphGoal 59) ps_59 = true := by decide +kernel
def lv_59_4 : Array NodeData := #[
  ([0xaaff0000aaaa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffffffff00000000], []),
  ([0xbbbb0000aaaa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffffffff00000000], []),
  ([0xffff0000eeee, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffffffff00000000], []),
  ([0xffff0000ffaa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffffffff00000000], []),
  ([0xcc00ff00cc00cc, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xdd00dd00cc00cc, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xff00ff00ee00ee, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xff00ff00ff00cc, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0x3300333333003300, 0xaaaaaaaaaaaaaaaa, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0x3311331133003300, 0xaaaaaaaaaaaaaaaa, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0x3333333333223322, 0xaaaaaaaaaaaaaaaa, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0x3333333333333300, 0xaaaaaaaaaaaaaaaa, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0x5555005555550000, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0x5555111155550000, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0x5555555555554444, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0x5555555555555500, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffffeeeeffff0000, 0xffffffff00000000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffffffaaffff0000, 0xffffffff00000000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xffeeffeeff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xffff0000ffff0000, 0xffffffccff00ff00, 0xffffffff00000000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xff00ff00ff00ff00, 0xffeeffeecccccccc, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffcccccccccc, 0xffffffff00000000], []),
  ([0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffeeeeaaaaaaaa, 0xffffffff00000000], []),
  ([0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffaaaaaaaaaa, 0xffffffff00000000], [])
]
def keys_59_4 : Array (List Sig) := lv_59_4.map Prod.fst
set_option maxHeartbeats 0 in
theorem chk_59_4_0 : checkRange false (vars6 59) (graphGoal 59) ps_59 rs_59 #[] 4 lv_59_4 0 16 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem chk_59_4_16 : checkRange false (vars6 59) (graphGoal 59) ps_59 rs_59 #[] 4 lv_59_4 16 8 = true := by decide +kernel
theorem lv_59_4_ok : ∀ i < keys_59_4.size, ∀ v, keys_59_4[i]? = some v → Impossible (graphGoal 59) 4 v.toFinset := by
  apply level_of_nodes
  intro i hi nd hnd
  have hsz : lv_59_4.size = 24 := by decide +kernel
  by_cases h0 : i < 16
  · exact checkRange_sound (fun h => by cases h) ps_59_ok (by decide) rs_59_ok (fun _ => (fun _ h => by simp at h)) chk_59_4_0 i (by omega) h0 nd hnd
  exact checkRange_sound (fun h => by cases h) ps_59_ok (by decide) rs_59_ok (fun _ => (fun _ h => by simp at h)) chk_59_4_16 i (by omega) (by omega) nd hnd

def lv_59_5 : Array NodeData := #[
  ([0xeeeeeeee, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xffaaffaa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xffffcccc, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xffffff00, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xff00000000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0x333300000000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xffff00000000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffffffff00000000, 0xffffffffffff0000], [(3, []), (4, [])]),
  ([0xffff0000aaaa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffffffff00000000], []),
  ([0xffff0000aaaa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffffffff00000000, 0xffffffffaaaaaaaa], [(3, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)])]),
  ([0xffff0000cccc, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xffff0000ff00, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0x55005500000000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xff00ff00000000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffff00ff00], [(2, []), (5, [])]),
  ([0xff00ff00aa00aa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xff00ff00cc00cc, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xff00ff00cc00cc, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffcccccccc], [(2, [(1, 0xcccccccccccccccc, 0xffffffff00000000)])]),
  ([0xff00ff00ff0000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0x1111111100000000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0x3333333300000000, 0xaaaaaaaaaaaaaaaa, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffcccccccc], [(1, []), (5, [])]),
  ([0x3333333322222222, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0x3333333333003300, 0xaaaaaaaaaaaaaaaa, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0x3333333333003300, 0xaaaaaaaaaaaaaaaa, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffff00ff00], [(1, [(1, 0xff00ff00ff00ff00, 0xffffffff00000000)])]),
  ([0x3333333333330000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0x5555555500000000, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffaaaaaaaa], [(0, []), (4, [])]),
  ([0x5555555544444444, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0x5555555555005500, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0x5555555555550000, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0x5555555555550000, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffffff0000], [(0, [(1, 0xffff0000ffff0000, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xaaffaaffaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(4, [(3, 0xff00ff00ff00ff00, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xbbbbbbbbaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(4, [(3, 0xcccccccccccccccc, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xccccffffcccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(5, [(3, 0xffff0000ffff0000, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xddddddddcccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(5, [(3, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xeeeeeeee00000000, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(0, 0xeeeeeeeeeeeeeeee, 0xffffffff00000000)]), (1, [(0, 0xeeeeeeeeeeeeeeee, 0xffffffff00000000)]), (4, [(0, 0xeeeeeeeeeeeeeeee, 0xffffffff00000000)]), (5, [(0, 0xeeeeeeeeeeeeeeee, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xff00ffffff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(5, [(3, 0xffff0000ffff0000, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xff55ff55ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(5, [(3, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffaaffaa00000000, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(0, 0xffaaffaaffaaffaa, 0xffffffff00000000)]), (2, [(0, 0xffaaffaaffaaffaa, 0xffffffff00000000)]), (4, [(0, 0xffaaffaaffaaffaa, 0xffffffff00000000)]), (5, [(0, 0xffaaffaaffaaffaa, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffff00ffffff0000, 0xffffffff00000000], [(4, [(3, 0xff00ff00ff00ff00, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffff3333ffff0000, 0xffffffff00000000], [(4, [(3, 0xcccccccccccccccc, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffcccc00000000, 0xffffffff00000000], [(4, [(0, 0xffffccccffffcccc, 0xffffffff00000000)]), (5, [(0, 0xffffccccffffcccc, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffff0000000000, 0xffffffff00000000], [(4, [(0, 0xffffff00ffffff00, 0xffffffff00000000)]), (5, [(0, 0xffffff00ffffff00, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffeeeeeeee], [(4, [(1, 0xeeeeeeeeeeeeeeee, 0xffffffff00000000)]), (5, [(1, 0xeeeeeeeeeeeeeeee, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffffaaffaa], [(4, [(1, 0xffaaffaaffaaffaa, 0xffffffff00000000)]), (5, [(1, 0xffaaffaaffaaffaa, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffffffcccc], [(4, [(1, 0xffffccccffffcccc, 0xffffffff00000000)]), (5, [(1, 0xffffccccffffcccc, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffffffff00], [(4, [(1, 0xffffff00ffffff00, 0xffffffff00000000)]), (5, [(1, 0xffffff00ffffff00, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffffccccffffcccc, 0xffffffff00000000, 0xffffffffffff0000], [(1, [(1, 0xffff0000ffff0000, 0xffffffff00000000)]), (4, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffffff00ffffff00, 0xffffffff00000000, 0xffffffffffff0000], [(2, [(1, 0xffff0000ffff0000, 0xffffffff00000000)]), (4, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xffaaffaaffaaffaa, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffff00ff00], [(0, [(1, 0xff00ff00ff00ff00, 0xffffffff00000000)]), (5, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xffff0000ffff0000, 0xffffff00ffffff00, 0xffffffff00000000, 0xffffffffff00ff00], [(3, [(1, 0xff00ff00ff00ff00, 0xffffffff00000000)]), (5, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xeeeeeeeeeeeeeeee, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffcccccccc], [(0, [(1, 0xcccccccccccccccc, 0xffffffff00000000)]), (5, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffccccffffcccc, 0xffffffff00000000, 0xffffffffcccccccc], [(3, [(1, 0xcccccccccccccccc, 0xffffffff00000000)]), (5, [])]),
  ([0xcccccccccccccccc, 0xeeeeeeeeeeeeeeee, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffaaaaaaaa], [(1, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (4, [])]),
  ([0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffaaffaaffaaffaa, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffaaaaaaaa], [(2, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (4, [])])
]
def keys_59_5 : Array (List Sig) := lv_59_5.map Prod.fst
set_option maxHeartbeats 0 in
theorem chk_59_5_0 : checkRange false (vars6 59) (graphGoal 59) ps_59 rs_59 keys_59_4 5 lv_59_5 0 16 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem chk_59_5_16 : checkRange false (vars6 59) (graphGoal 59) ps_59 rs_59 keys_59_4 5 lv_59_5 16 16 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem chk_59_5_32 : checkRange false (vars6 59) (graphGoal 59) ps_59 rs_59 keys_59_4 5 lv_59_5 32 16 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem chk_59_5_48 : checkRange false (vars6 59) (graphGoal 59) ps_59 rs_59 keys_59_4 5 lv_59_5 48 4 = true := by decide +kernel
theorem lv_59_5_ok : ∀ i < keys_59_5.size, ∀ v, keys_59_5[i]? = some v → Impossible (graphGoal 59) 5 v.toFinset := by
  apply level_of_nodes
  intro i hi nd hnd
  have hsz : lv_59_5.size = 52 := by decide +kernel
  by_cases h0 : i < 16
  · exact checkRange_sound (fun h => by cases h) ps_59_ok (by decide) rs_59_ok (fun _ => lv_59_4_ok) chk_59_5_0 i (by omega) h0 nd hnd
  by_cases h1 : i < 32
  · exact checkRange_sound (fun h => by cases h) ps_59_ok (by decide) rs_59_ok (fun _ => lv_59_4_ok) chk_59_5_16 i (by omega) h1 nd hnd
  by_cases h2 : i < 48
  · exact checkRange_sound (fun h => by cases h) ps_59_ok (by decide) rs_59_ok (fun _ => lv_59_4_ok) chk_59_5_32 i (by omega) h2 nd hnd
  exact checkRange_sound (fun h => by cases h) ps_59_ok (by decide) rs_59_ok (fun _ => lv_59_4_ok) chk_59_5_48 i (by omega) (by omega) nd hnd

def lv_59_6 : Array NodeData := #[
  ([0xffff00000000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(3, 0xffff0000ffff0000, 0xffffffff00000000)]), (1, [(3, 0xffff0000ffff0000, 0xffffffff00000000)]), (2, [(3, 0xffff0000ffff0000, 0xffffffff00000000)]), (4, [])]),
  ([0xff00ff00000000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(3, 0xff00ff00ff00ff00, 0xffffffff00000000)]), (1, [(3, 0xff00ff00ff00ff00, 0xffffffff00000000)]), (3, [(3, 0xff00ff00ff00ff00, 0xffffffff00000000)]), (5, [])]),
  ([0x3333333300000000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(3, 0xcccccccccccccccc, 0xffffffff00000000)]), (1, []), (2, [(3, 0xcccccccccccccccc, 0xffffffff00000000)]), (3, [(3, 0xcccccccccccccccc, 0xffffffff00000000)]), (5, [])]),
  ([0x5555555500000000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, []), (1, [(3, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (2, [(3, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (3, [(3, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (4, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xeeeeeeeeeeeeeeee, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, []), (1, []), (3, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc)]), (4, []), (5, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffaaffaaffaaffaa, 0xffff0000ffff0000, 0xffffffff00000000], [(0, []), (3, [(1, 0xaaaaaaaaaaaaaaaa, 0xff00ff00ff00ff00)]), (4, []), (5, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffccccffffcccc, 0xffffffff00000000], [(1, []), (2, [(1, 0xcccccccccccccccc, 0xffff0000ffff0000)]), (4, []), (5, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffff00ffffff00, 0xffffffff00000000], [(1, [(1, 0xff00ff00ff00ff00, 0xffff0000ffff0000)]), (4, []), (5, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffaaaaaaaa], [(0, []), (1, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (2, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (4, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffcccccccc], [(0, [(1, 0xcccccccccccccccc, 0xffffffff00000000)]), (1, []), (3, [(1, 0xcccccccccccccccc, 0xffffffff00000000)]), (5, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffff00ff00], [(0, [(1, 0xff00ff00ff00ff00, 0xffffffff00000000)]), (2, []), (3, [(1, 0xff00ff00ff00ff00, 0xffffffff00000000)]), (5, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffffff0000], [(1, [(1, 0xffff0000ffff0000, 0xffffffff00000000)]), (2, [(1, 0xffff0000ffff0000, 0xffffffff00000000)]), (4, [])])
]
def keys_59_6 : Array (List Sig) := lv_59_6.map Prod.fst
set_option maxHeartbeats 0 in
theorem chk_59_6_0 : checkRange false (vars6 59) (graphGoal 59) ps_59 rs_59 keys_59_5 6 lv_59_6 0 12 = true := by decide +kernel
theorem lv_59_6_ok : ∀ i < keys_59_6.size, ∀ v, keys_59_6[i]? = some v → Impossible (graphGoal 59) 6 v.toFinset := by
  apply level_of_nodes
  intro i hi nd hnd
  have hsz : lv_59_6.size = 12 := by decide +kernel
  exact checkRange_sound (fun h => by cases h) ps_59_ok (by decide) rs_59_ok (fun _ => lv_59_5_ok) chk_59_6_0 i (by omega) (by omega) nd hnd

def lv_59_7 : Array NodeData := #[
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, []), (1, []), (2, []), (4, []), (5, [])])
]
def keys_59_7 : Array (List Sig) := lv_59_7.map Prod.fst
set_option maxHeartbeats 0 in
theorem chk_59_7_0 : checkRange false (vars6 59) (graphGoal 59) ps_59 rs_59 keys_59_6 7 lv_59_7 0 1 = true := by decide +kernel
theorem lv_59_7_ok : ∀ i < keys_59_7.size, ∀ v, keys_59_7[i]? = some v → Impossible (graphGoal 59) 7 v.toFinset := by
  apply level_of_nodes
  intro i hi nd hnd
  have hsz : lv_59_7.size = 1 := by decide +kernel
  exact checkRange_sound (fun h => by cases h) ps_59_ok (by decide) rs_59_ok (fun _ => lv_59_6_ok) chk_59_7_0 i (by omega) (by omega) nd hnd

theorem imp_59 : Impossible (graphGoal 59) 7 (vars6 59).toFinset := by
  have h := lv_59_7_ok 0 (by decide +kernel) (sortSig (vars6 59)) (by decide +kernel)
  rwa [sortSig_toFinset] at h

theorem low_59 : Lower (vars6 59) (graphGoal 59) 8 := by
  apply lower_impossible (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) _ imp_59
  intro a ha
  have hw : [(0xaaaaaaaaaaaaaaaa, (16 : Row), (17 : Row)), (0xcccccccccccccccc, (8 : Row), (10 : Row)), (0xff00ff00ff00ff00, (2 : Row), (10 : Row)), (0xffff0000ffff0000, (1 : Row), (17 : Row)), (0xffffffff00000000, (1 : Row), (33 : Row))].all (fun e => witnessB (graphGoal 59) (vars6 59) e.1 e.2) = true := by decide +kernel
  have hv : vars6 59 = [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000] := by decide +kernel
  rw [hv] at ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 59) (vars6 59) 0xaaaaaaaaaaaaaaaa (16, 17) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 59) (vars6 59) 0xcccccccccccccccc (8, 10) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 59) (vars6 59) 0xff00ff00ff00ff00 (2, 10) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 59) (vars6 59) 0xffff0000ffff0000 (1, 17) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 59) (vars6 59) 0xffffffff00000000 (1, 33) = true)

def rs_61 : Array RestrEntry := #[(4, 0, 5), (8, 0, 5), (0, 8, 5), (1, 0, 4), (16, 0, 4), (32, 0, 4), (12, 0, 4), (40, 0, 4), (0, 4, 3), (5, 0, 2), (9, 0, 2), (20, 0, 2), (24, 0, 2), (0, 1, 2), (0, 16, 2), (0, 32, 2), (17, 0, 1), (33, 0, 1), (36, 0, 1), (48, 0, 1)]
theorem rs_61_ok : ∀ i < rs_61.size, ∀ r, rs_61[i]? = some r → Slice (vars6 61) (graphGoal 61) (subcube r.1 r.2.1) r.2.2 := by
  intro i hi r hr
  have hi' : i < 20 := hi
  interval_cases i <;> simp [rs_61] at hr <;> subst hr
  · exact slice_of_lower 4 0 5 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_57
  · exact slice_of_lower 8 0 5 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_53
  · refine slice_of_lower 0 8 5 (G := fixWord 0 8 (graphGoal 61)) (base := vars6 53) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_lift (raw := vars6 53) (base := vars6 21) (T := fixWord 0 8 (graphGoal 61)) (G := graphGoal 21) 32 0 4 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xffffffff00000000, 0, 32)] (by decide +kernel) (by decide +kernel) low_21
    simpa [show 4 + (List.map Prod.fst [(0xffffffff00000000, (0 : Row), (32 : Row))]).toFinset.card = 5 by decide +kernel] using hl
  · exact slice_of_lower 1 0 4 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_60
  · exact slice_of_lower 16 0 4 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_45
  · exact slice_of_lower 40 0 4 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_21
  · exact slice_of_lower 12 0 4 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_49
  · exact slice_of_lower 40 0 4 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_21
  · refine slice_of_lower 0 4 3 (G := fixWord 0 4 (graphGoal 61)) (base := vars6 57) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_lift (raw := vars6 57) (base := vars6 40) (T := fixWord 0 4 (graphGoal 61)) (G := graphGoal 40) 17 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 0, 1), (0xffff0000ffff0000, 0, 16)] (by decide +kernel) (by decide +kernel) low_40
    simpa [show 1 + (List.map Prod.fst [(0xaaaaaaaaaaaaaaaa, (0 : Row), (1 : Row)), (0xffff0000ffff0000, (0 : Row), (16 : Row))]).toFinset.card = 3 by decide +kernel] using hl
  · exact slice_of_lower 5 0 2 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_56
  · exact slice_of_lower 9 0 2 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_52
  · exact slice_of_lower 20 0 2 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_41
  · exact slice_of_lower 24 0 2 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_37
  · refine slice_of_lower 0 1 2 (G := fixWord 0 1 (graphGoal 61)) (base := vars6 60) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_count (raw := vars6 60) (T := fixWord 0 1 (graphGoal 61)) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xf0f0f0f0f0f0f0f0, 0, 4), (0xffff0000ffff0000, 0, 16), (0xffffffff00000000, 0, 32)] (by decide +kernel)
    simpa [show (List.map Prod.fst [(0xf0f0f0f0f0f0f0f0, (0 : Row), (4 : Row)), (0xffff0000ffff0000, (0 : Row), (16 : Row)), (0xffffffff00000000, (0 : Row), (32 : Row))]).toFinset.card - 1 = 2 by decide +kernel] using hl
  · refine slice_of_lower 0 16 2 (G := fixWord 0 16 (graphGoal 61)) (base := vars6 45) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_count (raw := vars6 45) (T := fixWord 0 16 (graphGoal 61)) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 0, 1), (0xf0f0f0f0f0f0f0f0, 0, 4), (0xffffffff00000000, 0, 32)] (by decide +kernel)
    simpa [show (List.map Prod.fst [(0xaaaaaaaaaaaaaaaa, (0 : Row), (1 : Row)), (0xf0f0f0f0f0f0f0f0, (0 : Row), (4 : Row)), (0xffffffff00000000, (0 : Row), (32 : Row))]).toFinset.card - 1 = 2 by decide +kernel] using hl
  · refine slice_of_lower 0 32 2 (G := fixWord 0 32 (graphGoal 61)) (base := vars6 29) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_count (raw := vars6 29) (T := fixWord 0 32 (graphGoal 61)) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 0, 1), (0xff00ff00ff00ff00, 0, 8), (0xffff0000ffff0000, 0, 16)] (by decide +kernel)
    simpa [show (List.map Prod.fst [(0xaaaaaaaaaaaaaaaa, (0 : Row), (1 : Row)), (0xff00ff00ff00ff00, (0 : Row), (8 : Row)), (0xffff0000ffff0000, (0 : Row), (16 : Row))]).toFinset.card - 1 = 2 by decide +kernel] using hl
  · exact slice_of_lower 21 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_40
  · exact slice_of_lower 41 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_20
  · exact slice_of_lower 44 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_17
  · exact slice_of_lower 56 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5

def ps_61 : List (Row × Row) := [(5, 1), (5, 4), (5, 8), (13, 9), (13, 12), (17, 1), (17, 9), (17, 16), (17, 24), (20, 4), (20, 16), (20, 32), (25, 9), (25, 24), (33, 1), (33, 32), (40, 8), (40, 12), (40, 32), (44, 12), (44, 36), (48, 16), (48, 32)]
theorem ps_61_ok : pairsOK (graphGoal 61) ps_61 = true := by decide +kernel
def lv_61_4 : Array NodeData := #[
  ([0xf0f0a0a0f0f0a0a, 0xaaaaaaaaaaaaaaaa, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [])
]
def keys_61_4 : Array (List Sig) := lv_61_4.map Prod.fst
set_option maxHeartbeats 0 in
theorem chk_61_4_0 : checkRange false (vars6 61) (graphGoal 61) ps_61 rs_61 #[] 4 lv_61_4 0 1 = true := by decide +kernel
theorem lv_61_4_ok : ∀ i < keys_61_4.size, ∀ v, keys_61_4[i]? = some v → Impossible (graphGoal 61) 4 v.toFinset := by
  apply level_of_nodes
  intro i hi nd hnd
  have hsz : lv_61_4.size = 1 := by decide +kernel
  exact checkRange_sound (fun h => by cases h) ps_61_ok (by decide) rs_61_ok (fun _ => (fun _ h => by simp at h)) chk_61_4_0 i (by omega) (by omega) nd hnd

def lv_61_5 : Array NodeData := #[
  ([0xaaaaaaaaaaaaaaaa, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffaaaaffffaaaa, 0xffffffff00000000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000)]), (1, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000)]), (2, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000)]), (3, [])])
]
def keys_61_5 : Array (List Sig) := lv_61_5.map Prod.fst
set_option maxHeartbeats 0 in
theorem chk_61_5_0 : checkRange false (vars6 61) (graphGoal 61) ps_61 rs_61 keys_61_4 5 lv_61_5 0 1 = true := by decide +kernel
theorem lv_61_5_ok : ∀ i < keys_61_5.size, ∀ v, keys_61_5[i]? = some v → Impossible (graphGoal 61) 5 v.toFinset := by
  apply level_of_nodes
  intro i hi nd hnd
  have hsz : lv_61_5.size = 1 := by decide +kernel
  exact checkRange_sound (fun h => by cases h) ps_61_ok (by decide) rs_61_ok (fun _ => lv_61_4_ok) chk_61_5_0 i (by omega) (by omega) nd hnd

def lv_61_6 : Array NodeData := #[
  ([0xaaaaaaaaaaaaaaaa, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, []), (1, []), (2, []), (3, []), (4, []), (7, [])])
]
def keys_61_6 : Array (List Sig) := lv_61_6.map Prod.fst
set_option maxHeartbeats 0 in
theorem chk_61_6_0 : checkRange false (vars6 61) (graphGoal 61) ps_61 rs_61 keys_61_5 6 lv_61_6 0 1 = true := by decide +kernel
theorem lv_61_6_ok : ∀ i < keys_61_6.size, ∀ v, keys_61_6[i]? = some v → Impossible (graphGoal 61) 6 v.toFinset := by
  apply level_of_nodes
  intro i hi nd hnd
  have hsz : lv_61_6.size = 1 := by decide +kernel
  exact checkRange_sound (fun h => by cases h) ps_61_ok (by decide) rs_61_ok (fun _ => lv_61_5_ok) chk_61_6_0 i (by omega) (by omega) nd hnd

theorem imp_61 : Impossible (graphGoal 61) 6 (vars6 61).toFinset := by
  have h := lv_61_6_ok 0 (by decide +kernel) (sortSig (vars6 61)) (by decide +kernel)
  rwa [sortSig_toFinset] at h

theorem low_61 : Lower (vars6 61) (graphGoal 61) 7 := by
  apply lower_impossible (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) _ imp_61
  intro a ha
  have hw : [(0xaaaaaaaaaaaaaaaa, (4 : Row), (5 : Row)), (0xf0f0f0f0f0f0f0f0, (1 : Row), (5 : Row)), (0xff00ff00ff00ff00, (32 : Row), (40 : Row)), (0xffff0000ffff0000, (1 : Row), (17 : Row)), (0xffffffff00000000, (1 : Row), (33 : Row))].all (fun e => witnessB (graphGoal 61) (vars6 61) e.1 e.2) = true := by decide +kernel
  have hv : vars6 61 = [0xaaaaaaaaaaaaaaaa, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000] := by decide +kernel
  rw [hv] at ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 61) (vars6 61) 0xaaaaaaaaaaaaaaaa (4, 5) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 61) (vars6 61) 0xf0f0f0f0f0f0f0f0 (1, 5) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 61) (vars6 61) 0xff00ff00ff00ff00 (32, 40) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 61) (vars6 61) 0xffff0000ffff0000 (1, 17) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 61) (vars6 61) 0xffffffff00000000 (1, 33) = true)

def rs_62 : Array RestrEntry := #[(4, 0, 5), (0, 4, 5), (2, 0, 4), (8, 0, 4), (16, 0, 4), (20, 0, 4), (32, 0, 3), (0, 2, 3), (0, 8, 3), (0, 16, 3), (6, 0, 2), (10, 0, 2), (12, 0, 2), (0, 32, 2), (18, 0, 1), (34, 0, 1), (36, 0, 1), (24, 0, 1), (40, 0, 1), (48, 0, 1)]
theorem rs_62_ok : ∀ i < rs_62.size, ∀ r, rs_62[i]? = some r → Slice (vars6 62) (graphGoal 62) (subcube r.1 r.2.1) r.2.2 := by
  intro i hi r hr
  have hi' : i < 20 := hi
  interval_cases i <;> simp [rs_62] at hr <;> subst hr
  · exact slice_of_lower 4 0 5 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_58
  · refine slice_of_lower 0 4 5 (G := fixWord 0 4 (graphGoal 62)) (base := vars6 58) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_lift (raw := vars6 58) (base := vars6 42) (T := fixWord 0 4 (graphGoal 62)) (G := graphGoal 42) 16 0 4 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xffff0000ffff0000, 0, 16)] (by decide +kernel) (by decide +kernel) low_42
    simpa [show 4 + (List.map Prod.fst [(0xffff0000ffff0000, (0 : Row), (16 : Row))]).toFinset.card = 5 by decide +kernel] using hl
  · exact slice_of_lower 2 0 4 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_60
  · exact slice_of_lower 8 0 4 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_54
  · exact slice_of_lower 20 0 4 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_42
  · exact slice_of_lower 20 0 4 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_42
  · exact slice_of_lower 32 0 3 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_30
  · refine slice_of_lower 0 2 3 (G := fixWord 0 2 (graphGoal 62)) (base := vars6 60) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_lift (raw := vars6 60) (base := vars6 20) (T := fixWord 0 2 (graphGoal 62)) (G := graphGoal 20) 40 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xff00ff00ff00ff00, 0, 8), (0xffffffff00000000, 0, 32)] (by decide +kernel) (by decide +kernel) low_20
    simpa [show 1 + (List.map Prod.fst [(0xff00ff00ff00ff00, (0 : Row), (8 : Row)), (0xffffffff00000000, (0 : Row), (32 : Row))]).toFinset.card = 3 by decide +kernel] using hl
  · refine slice_of_lower 0 8 3 (G := fixWord 0 8 (graphGoal 62)) (base := vars6 54) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_lift (raw := vars6 54) (base := vars6 20) (T := fixWord 0 8 (graphGoal 62)) (G := graphGoal 20) 34 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xcccccccccccccccc, 0, 2), (0xffffffff00000000, 0, 32)] (by decide +kernel) (by decide +kernel) low_20
    simpa [show 1 + (List.map Prod.fst [(0xcccccccccccccccc, (0 : Row), (2 : Row)), (0xffffffff00000000, (0 : Row), (32 : Row))]).toFinset.card = 3 by decide +kernel] using hl
  · refine slice_of_lower 0 16 3 (G := fixWord 0 16 (graphGoal 62)) (base := vars6 46) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_lift (raw := vars6 46) (base := vars6 10) (T := fixWord 0 16 (graphGoal 62)) (G := graphGoal 10) 36 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xf0f0f0f0f0f0f0f0, 0, 4), (0xffffffff00000000, 0, 32)] (by decide +kernel) (by decide +kernel) low_10
    simpa [show 1 + (List.map Prod.fst [(0xf0f0f0f0f0f0f0f0, (0 : Row), (4 : Row)), (0xffffffff00000000, (0 : Row), (32 : Row))]).toFinset.card = 3 by decide +kernel] using hl
  · exact slice_of_lower 6 0 2 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_56
  · exact slice_of_lower 10 0 2 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_52
  · exact slice_of_lower 12 0 2 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_50
  · refine slice_of_lower 0 32 2 (G := fixWord 0 32 (graphGoal 62)) (base := vars6 30) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_count (raw := vars6 30) (T := fixWord 0 32 (graphGoal 62)) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xcccccccccccccccc, 0, 2), (0xff00ff00ff00ff00, 0, 8), (0xffff0000ffff0000, 0, 16)] (by decide +kernel)
    simpa [show (List.map Prod.fst [(0xcccccccccccccccc, (0 : Row), (2 : Row)), (0xff00ff00ff00ff00, (0 : Row), (8 : Row)), (0xffff0000ffff0000, (0 : Row), (16 : Row))]).toFinset.card - 1 = 2 by decide +kernel] using hl
  · exact slice_of_lower 22 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_40
  · exact slice_of_lower 42 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_20
  · exact slice_of_lower 52 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10
  · exact slice_of_lower 28 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_34
  · exact slice_of_lower 42 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_20
  · exact slice_of_lower 52 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10

def ps_62 : List (Row × Row) := [(10, 2), (10, 4), (10, 8), (10, 18), (14, 6), (14, 12), (20, 4), (20, 12), (20, 16), (20, 18), (22, 6), (22, 18), (22, 24), (22, 36), (26, 18), (26, 24), (28, 12), (28, 24), (34, 0), (34, 2), (34, 6), (34, 18), (34, 32), (38, 6), (40, 0), (40, 8), (40, 12), (40, 32), (48, 16), (48, 18), (48, 24), (48, 32), (48, 36)]
theorem ps_62_ok : pairsOK (graphGoal 62) ps_62 = true := by decide +kernel
def lv_62_4 : Array NodeData := #[
  ([0xff00ff00cc00cc, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0x3333333333003300, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xcccccccccc00cc00, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00cc00cc00, 0xffff0000ffff0000, 0xffffffff00000000], [])
]
def keys_62_4 : Array (List Sig) := lv_62_4.map Prod.fst
set_option maxHeartbeats 0 in
theorem chk_62_4_0 : checkRange false (vars6 62) (graphGoal 62) ps_62 rs_62 #[] 4 lv_62_4 0 4 = true := by decide +kernel
theorem lv_62_4_ok : ∀ i < keys_62_4.size, ∀ v, keys_62_4[i]? = some v → Impossible (graphGoal 62) 4 v.toFinset := by
  apply level_of_nodes
  intro i hi nd hnd
  have hsz : lv_62_4.size = 4 := by decide +kernel
  exact checkRange_sound (fun h => by cases h) ps_62_ok (by decide) rs_62_ok (fun _ => (fun _ h => by simp at h)) chk_62_4_0 i (by omega) (by omega) nd hnd

def lv_62_5 : Array NodeData := #[
  ([0xff00ff00000000, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(3, 0xff00ff00ff00ff00, 0xffffffff00000000)]), (1, [(3, 0xff00ff00ff00ff00, 0xffffffff00000000)])]),
  ([0x3333333300000000, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(3, 0xcccccccccccccccc, 0xffffffff00000000)]), (1, [(3, 0xcccccccccccccccc, 0xffffffff00000000)])]),
  ([0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffccffccffccffcc, 0xffff0000ffff0000, 0xffffffff00000000], [(2, [])]),
  ([0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffcccccccc], []),
  ([0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffff00ff00], [])
]
def keys_62_5 : Array (List Sig) := lv_62_5.map Prod.fst
set_option maxHeartbeats 0 in
theorem chk_62_5_0 : checkRange false (vars6 62) (graphGoal 62) ps_62 rs_62 keys_62_4 5 lv_62_5 0 5 = true := by decide +kernel
theorem lv_62_5_ok : ∀ i < keys_62_5.size, ∀ v, keys_62_5[i]? = some v → Impossible (graphGoal 62) 5 v.toFinset := by
  apply level_of_nodes
  intro i hi nd hnd
  have hsz : lv_62_5.size = 5 := by decide +kernel
  exact checkRange_sound (fun h => by cases h) ps_62_ok (by decide) rs_62_ok (fun _ => lv_62_4_ok) chk_62_5_0 i (by omega) (by omega) nd hnd

def lv_62_6 : Array NodeData := #[
  ([0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, []), (1, []), (2, []), (3, []), (5, [])])
]
def keys_62_6 : Array (List Sig) := lv_62_6.map Prod.fst
set_option maxHeartbeats 0 in
theorem chk_62_6_0 : checkRange false (vars6 62) (graphGoal 62) ps_62 rs_62 keys_62_5 6 lv_62_6 0 1 = true := by decide +kernel
theorem lv_62_6_ok : ∀ i < keys_62_6.size, ∀ v, keys_62_6[i]? = some v → Impossible (graphGoal 62) 6 v.toFinset := by
  apply level_of_nodes
  intro i hi nd hnd
  have hsz : lv_62_6.size = 1 := by decide +kernel
  exact checkRange_sound (fun h => by cases h) ps_62_ok (by decide) rs_62_ok (fun _ => lv_62_5_ok) chk_62_6_0 i (by omega) (by omega) nd hnd

theorem imp_62 : Impossible (graphGoal 62) 6 (vars6 62).toFinset := by
  have h := lv_62_6_ok 0 (by decide +kernel) (sortSig (vars6 62)) (by decide +kernel)
  rwa [sortSig_toFinset] at h

theorem low_62 : Lower (vars6 62) (graphGoal 62) 7 := by
  apply lower_impossible (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) _ imp_62
  intro a ha
  have hw : [(0xcccccccccccccccc, (8 : Row), (10 : Row)), (0xf0f0f0f0f0f0f0f0, (16 : Row), (20 : Row)), (0xff00ff00ff00ff00, (2 : Row), (10 : Row)), (0xffff0000ffff0000, (4 : Row), (20 : Row)), (0xffffffff00000000, (2 : Row), (34 : Row))].all (fun e => witnessB (graphGoal 62) (vars6 62) e.1 e.2) = true := by decide +kernel
  have hv : vars6 62 = [0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000] := by decide +kernel
  rw [hv] at ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 62) (vars6 62) 0xcccccccccccccccc (8, 10) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 62) (vars6 62) 0xf0f0f0f0f0f0f0f0 (16, 20) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 62) (vars6 62) 0xff00ff00ff00ff00 (2, 10) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 62) (vars6 62) 0xffff0000ffff0000 (4, 20) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 62) (vars6 62) 0xffffffff00000000 (2, 34) = true)

def rs_63 : Array RestrEntry := #[(4, 0, 8), (2, 0, 7), (8, 0, 7), (16, 0, 7), (1, 0, 7), (32, 0, 6), (0, 8, 6), (0, 4, 6), (0, 2, 6), (12, 0, 5), (5, 0, 5), (20, 0, 5), (6, 0, 5), (10, 0, 5), (18, 0, 4), (34, 0, 4), (24, 0, 4), (40, 0, 4), (0, 1, 4), (17, 0, 4), (9, 0, 4), (3, 0, 4), (0, 16, 4), (33, 0, 3), (36, 0, 3), (48, 0, 3), (0, 32, 3)]
theorem rs_63_ok : ∀ i < rs_63.size, ∀ r, rs_63[i]? = some r → Slice (vars6 63) (graphGoal 63) (subcube r.1 r.2.1) r.2.2 := by
  intro i hi r hr
  have hi' : i < 27 := hi
  interval_cases i <;> simp [rs_63] at hr <;> subst hr
  · exact slice_of_lower 4 0 8 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_59
  · exact slice_of_lower 2 0 7 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_61
  · exact slice_of_lower 8 0 7 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_55
  · exact slice_of_lower 16 0 7 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47
  · exact slice_of_lower 1 0 7 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_62
  · exact slice_of_lower 32 0 6 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_31
  · refine slice_of_lower 0 8 6 (G := fixWord 0 8 (graphGoal 63)) (base := vars6 55) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_lift (raw := vars6 55) (base := vars6 21) (T := fixWord 0 8 (graphGoal 63)) (G := graphGoal 21) 34 0 4 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xcccccccccccccccc, 0, 2), (0xffffffff00000000, 0, 32)] (by decide +kernel) (by decide +kernel) low_21
    simpa [show 4 + (List.map Prod.fst [(0xcccccccccccccccc, (0 : Row), (2 : Row)), (0xffffffff00000000, (0 : Row), (32 : Row))]).toFinset.card = 6 by decide +kernel] using hl
  · refine slice_of_lower 0 4 6 (G := fixWord 0 4 (graphGoal 63)) (base := vars6 59) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_lift (raw := vars6 59) (base := vars6 42) (T := fixWord 0 4 (graphGoal 63)) (G := graphGoal 42) 17 0 4 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 0, 1), (0xffff0000ffff0000, 0, 16)] (by decide +kernel) (by decide +kernel) low_42
    simpa [show 4 + (List.map Prod.fst [(0xaaaaaaaaaaaaaaaa, (0 : Row), (1 : Row)), (0xffff0000ffff0000, (0 : Row), (16 : Row))]).toFinset.card = 6 by decide +kernel] using hl
  · refine slice_of_lower 0 2 6 (G := fixWord 0 2 (graphGoal 63)) (base := vars6 61) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_lift (raw := vars6 61) (base := vars6 21) (T := fixWord 0 2 (graphGoal 63)) (G := graphGoal 21) 40 0 4 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xff00ff00ff00ff00, 0, 8), (0xffffffff00000000, 0, 32)] (by decide +kernel) (by decide +kernel) low_21
    simpa [show 4 + (List.map Prod.fst [(0xff00ff00ff00ff00, (0 : Row), (8 : Row)), (0xffffffff00000000, (0 : Row), (32 : Row))]).toFinset.card = 6 by decide +kernel] using hl
  · exact slice_of_lower 12 0 5 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_51
  · exact slice_of_lower 5 0 5 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_58
  · exact slice_of_lower 20 0 5 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_43
  · exact slice_of_lower 6 0 5 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_57
  · exact slice_of_lower 10 0 5 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_53
  · exact slice_of_lower 18 0 4 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_45
  · exact slice_of_lower 42 0 4 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_21
  · exact slice_of_lower 24 0 4 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_39
  · exact slice_of_lower 42 0 4 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_21
  · refine slice_of_lower 0 1 4 (G := fixWord 0 1 (graphGoal 63)) (base := vars6 62) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_lift (raw := vars6 62) (base := vars6 10) (T := fixWord 0 1 (graphGoal 63)) (G := graphGoal 10) 52 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xf0f0f0f0f0f0f0f0, 0, 4), (0xffff0000ffff0000, 0, 16), (0xffffffff00000000, 0, 32)] (by decide +kernel) (by decide +kernel) low_10
    simpa [show 1 + (List.map Prod.fst [(0xf0f0f0f0f0f0f0f0, (0 : Row), (4 : Row)), (0xffff0000ffff0000, (0 : Row), (16 : Row)), (0xffffffff00000000, (0 : Row), (32 : Row))]).toFinset.card = 4 by decide +kernel] using hl
  · exact slice_of_lower 21 0 4 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_42
  · exact slice_of_lower 9 0 4 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_54
  · exact slice_of_lower 3 0 4 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_60
  · refine slice_of_lower 0 16 4 (G := fixWord 0 16 (graphGoal 63)) (base := vars6 47) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_lift (raw := vars6 47) (base := vars6 10) (T := fixWord 0 16 (graphGoal 63)) (G := graphGoal 10) 37 0 1 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 0, 1), (0xf0f0f0f0f0f0f0f0, 0, 4), (0xffffffff00000000, 0, 32)] (by decide +kernel) (by decide +kernel) low_10
    simpa [show 1 + (List.map Prod.fst [(0xaaaaaaaaaaaaaaaa, (0 : Row), (1 : Row)), (0xf0f0f0f0f0f0f0f0, (0 : Row), (4 : Row)), (0xffffffff00000000, (0 : Row), (32 : Row))]).toFinset.card = 4 by decide +kernel] using hl
  · exact slice_of_lower 33 0 3 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_30
  · exact slice_of_lower 36 0 3 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_27
  · exact slice_of_lower 48 0 3 (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15
  · refine slice_of_lower 0 32 3 (G := fixWord 0 32 (graphGoal 63)) (base := vars6 31) (proper_of (by decide +kernel)) rfl (by decide +kernel) (by decide +kernel) ?_
    have hl := lower_count (raw := vars6 31) (T := fixWord 0 32 (graphGoal 63)) (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 0, 1), (0xcccccccccccccccc, 0, 2), (0xff00ff00ff00ff00, 0, 8), (0xffff0000ffff0000, 0, 16)] (by decide +kernel)
    simpa [show (List.map Prod.fst [(0xaaaaaaaaaaaaaaaa, (0 : Row), (1 : Row)), (0xcccccccccccccccc, (0 : Row), (2 : Row)), (0xff00ff00ff00ff00, (0 : Row), (8 : Row)), (0xffff0000ffff0000, (0 : Row), (16 : Row))]).toFinset.card - 1 = 3 by decide +kernel] using hl

def ps_63 : List (Row × Row) := [(5, 0), (5, 1), (5, 3), (5, 4), (5, 6), (5, 8), (5, 12), (5, 32), (5, 36), (7, 1), (7, 3), (7, 6), (10, 0), (10, 2), (10, 3), (10, 8), (10, 9), (10, 12), (10, 16), (11, 1), (11, 2), (11, 3), (11, 9), (13, 1), (13, 6), (13, 9), (13, 12), (13, 32), (14, 4), (14, 6), (14, 12), (17, 0), (17, 1), (17, 3), (17, 9), (17, 16), (17, 32), (19, 3), (19, 18), (20, 0), (20, 4), (20, 6), (20, 12), (20, 16), (20, 32), (20, 36), (21, 4), (21, 32), (22, 6), (22, 18), (25, 3), (25, 9), (25, 24), (25, 32), (26, 2), (26, 16), (26, 18), (26, 24), (28, 12), (28, 24), (28, 32), (33, 0), (33, 1), (33, 3), (33, 4), (33, 8), (33, 9), (33, 32), (34, 2), (34, 3), (34, 6), (34, 16), (34, 18), (34, 32), (35, 1), (35, 3), (37, 36), (38, 6), (38, 36), (40, 4), (40, 8), (40, 9), (40, 12), (40, 24), (40, 32), (40, 36), (41, 1), (41, 9), (41, 32), (42, 2), (42, 32), (44, 12), (44, 36), (48, 0), (48, 4), (48, 16), (48, 18), (48, 24), (48, 32), (48, 36), (50, 18), (52, 36), (56, 24), (56, 32)]
theorem ps_63_ok : pairsOK (graphGoal 63) ps_63 = true := by decide +kernel
def lv_63_4 : Array NodeData := #[
  ([0xcc00ff00cc00fc, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xfffffffff0f0f0f0, 0xffffffffffff0000], []),
  ([0xdd00dd00dc00dc, 0xcccccccccccccccc, 0xffff0000ffff0000, 0xffffffffaaaaaaaa, 0xfffffffff0f0f0f0], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff33ff22ff33ff22, 0xfffffffff0f0f0f0, 0xffffffffffff0000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xffffffaafff0ffa0, 0xfffffffff0f0f0f0, 0xffffffffffff0000], []),
  ([0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff33ff22ff33ff22, 0xffffffffaaaaaaaa, 0xffffffffffff0000], []),
  ([0xcccccccccccccccc, 0xff33ff22ff33ff22, 0xffff0000ffff0000, 0xffffffffaaaaaaaa, 0xfffffffff0f0f0f0], []),
  ([0xcccccccccccccccc, 0xffff0000ffff0000, 0xffffffaafff0ffa0, 0xffffffffaaaaaaaa, 0xfffffffff0f0f0f0], [])
]
def keys_63_4 : Array (List Sig) := lv_63_4.map Prod.fst
set_option maxHeartbeats 0 in
theorem chk_63_4_0 : checkRange true (vars6 63) (graphGoal 63) ps_63 rs_63 #[] 4 lv_63_4 0 7 = true := by decide +kernel
theorem lv_63_4_ok : ∀ i < keys_63_4.size, ∀ v, keys_63_4[i]? = some v → Impossible (graphGoal 63) 4 v.toFinset := by
  apply level_of_nodes
  intro i hi nd hnd
  have hsz : lv_63_4.size = 7 := by decide +kernel
  exact checkRange_sound (fun _ => rfl) ps_63_ok (by decide) rs_63_ok (fun _ => (fun _ h => by simp at h)) chk_63_4_0 i (by omega) (by omega) nd hnd

def lv_63_5 : Array NodeData := #[
  ([0xf0f0e0e, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0x44cccccccc, 0xaaaaaaaaaaaaaaaa, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xff000000f0, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xfffffffff0f0f0f0, 0xffffffffffff0000], []),
  ([0x44440c0c4c4c, 0xaaaaaaaaaaaaaaaa, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xfffffffff0f0f0f0], []),
  ([0x555500000000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xfffffffff0f0f0f0], []),
  ([0x555500005050, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xfffffffff0f0f0f0, 0xffffffffffff0000], []),
  ([0x555500005050, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffffaaaaaaaa, 0xfffffffff0f0f0f0], []),
  ([0xeeee0000eeee, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffffaaaaaaaa, 0xfffffffff0f0f0f0], []),
  ([0xf5f50000f0f0, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf5f5f5f5f0f0f0f0, 0xff00ff00ff00ff00, 0xffffffffffff0000], []),
  ([0xffff0000aaaa, 0xffff0000f0f0, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xfffffffff0f0f0f0], []),
  ([0xffff0000aaaa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffffaaaaffffaaaa, 0xfffffffff0f0f0f0], [(19, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)])]),
  ([0xffff0000aaaa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xfffffffff0f0f0f0, 0xffffffffffff0000], []),
  ([0xffff0000aaaa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xfffffffff0f0f0f0, 0xffffffffffffaaaa], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (1, 0xffffaaaaffffaaaa, 0xffffffff00000000), (2, 0xffffffffffffaaaa, 0xffff0000ffff0000)])]),
  ([0xffff0000aaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffffaaaaffffaaaa, 0xffffffffaaaaaaaa, 0xfffffffff0f0f0f0], []),
  ([0xffff0000f0f0, 0x5555555550505050, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffffffffffff0000], []),
  ([0xffff0000f0f0, 0x5555555550505050, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffffaaaaaaaa], []),
  ([0xffff0000f0f0, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff5555ffff0000, 0xfffffffff0f0f0f0], []),
  ([0x55005500500050, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffffaaaaaaaa, 0xfffffffff0f0f0f0], []),
  ([0xcc00ff00cc00ee, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xcc00ff00cc00fc, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xffff0000ffff0000, 0xffffffff00000000, 0xfffffffff0f0f0f0], []),
  ([0xdd00dd00dc00dc, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xffff0000ffff0000, 0xffffffff00000000, 0xfffffffff0f0f0f0], []),
  ([0xdd00dd00dd00cc, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xee00ee00ee00ee, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffffaaaaaaaa, 0xfffffffff0f0f0f0], [(2, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)])]),
  ([0xee00ff00ee00ee, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xff00aa00ff00aa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xfffffffff0f0f0f0, 0xffffffffffff0000], []),
  ([0xff00aa00ff00aa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffffffffaaaaaaaa, 0xffffffffffff0000], []),
  ([0xff00aa00ff00aa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffffaaaaaaaa, 0xfffffffff0f0f0f0], []),
  ([0xff00cc00ff00cc, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xfffffffff0f0f0f0, 0xffffffffffff0000], [(2, [(1, 0xcccccccccccccccc, 0xffff0000ffff0000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (1, 0xffff0000ffff0000, 0xffffffff00000000)])]),
  ([0xff00dd00ff00cc, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xff00ff00cc00cc, 0xf0f0a0a0f0f0a0a, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xff00ff00ee00ee, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xffff0000ffff0000, 0xffffffff00000000, 0xfffffffff0f0f0f0], []),
  ([0xff00ff00ee00ee, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xffff0000ffff0000, 0xffffffffaaaaaaaa, 0xfffffffff0f0f0f0], []),
  ([0xff00ff00ff00cc, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xffff0000ffff0000, 0xffffffff00000000, 0xfffffffff0f0f0f0], []),
  ([0xff00ff00ff00cc, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xffff0000ffff0000, 0xfffffffff0f0f0f0, 0xffffffffffff0000], []),
  ([0xff00ff00ff00ee, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xa0a0a0a0f0f0e0e, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xc0c08080f0f0a0a, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xc0c0c0c0f0f0e0e, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xf0f00000f0f0e0e, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xf0f0a0a0f0f0a0a, 0xaaaaaaaaaaaaaaaa, 0xcccccccccc00cc00, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xf0f0a0f0f0f0a0a, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xf0f0f0f0f0f0a0a, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xf0f0f0f0f0f0e0e, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xfff0aff0f0f0a0a, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0x5050555550505050, 0xcccccccccccccccc, 0xf0f0fffff0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffffaaaaaaaa], []),
  ([0x5555444455554444, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xfffffffff0f0f0f0, 0xffffffffffff0000], []),
  ([0x5555555550505050, 0x5555555555550000, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xfffffffff0f0f0f0], []),
  ([0x5555555550505050, 0xaaaaffffaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xfffffffff0f0f0f0], []),
  ([0x5555555555550000, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffaaaaffffaaaa, 0xfffffffff0f0f0f0], [(19, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)])]),
  ([0x5555555555550000, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffffaaaaaaaa, 0xfffffffff0f0f0f0], []),
  ([0x5555555555550000, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xfffffffff0f0f0f0, 0xffffffffffffaaaa], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (1, 0xffffaaaaffffaaaa, 0xffffffff00000000), (2, 0xffffffffffffaaaa, 0xaaaaaaaaaaaaaaaa)])]),
  ([0x5555555555550000, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffffaaaaffffaaaa, 0xfffffffff0f0f0f0, 0xffffffffffff0000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xaaaaffffaaaafafa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xfffffffff0f0f0f0, 0xffffffffffff0000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcc00cc44cc00cc44, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xfffffffff0f0f0f0], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcc00cccccc00cc88, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcc00cccccc00ccc0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xfffffffff0f0f0f0], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcc44cc44cc40cc40, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xfffffffff0f0f0f0], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcc44cc44cc44cc00, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcc88cccccc88cc88, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccc44cccccc00, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccc88cc88, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xfffffffff0f0f0f0], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccc88cc88, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffffaaaaaaaa, 0xfffffffff0f0f0f0], [(2, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (0, 0xffffffffffaaffaa, 0xcccccccccccccccc), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccc00, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xfffffffff0f0f0f0], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccc00, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xfffffffff0f0f0f0, 0xffffffffffff0000], [(2, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (1, 0xffff0000ffff0000, 0xffffffff00000000), (0, 0xffffffffffffff00, 0xcccccccccccccccc)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccc88, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xccccdddd00000000, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xfffffffff0f0f0f0], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xccccffffccccfcfc, 0xff00ff00ff00ff00, 0xfffffffff0f0f0f0, 0xffffffffffff0000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffffeeeeffff0000, 0xffffffff00000000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff33ff22ff33ff22, 0xffffffff00000000, 0xffffffffffff0000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000, 0xffffffeeff00ff00, 0xffffffff00000000], [(8, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (1, 0xffffeeee00000000, 0xff00ff00ff00ff00)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f5f5f0f0f4f4, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0ffa0aaf0f0a0a0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (3, 0xff00ff00ff00ff00, 0xffffffff00000000), (0, 0xf0fff0fff0f0f0f0, 0xffffaaaaffffaaaa)]), (3, [(3, 0xff00ff00ff00ff00, 0xffffffff00000000), (1, 0xff00ff00000000, 0xf0f0f0f0f0f0f0f0), (0, 0xf0fff0fff0f0f0f0, 0xffffaaaaffffaaaa)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf5f5f5f5f0f0f0f0, 0xff00ff00ff00ff00, 0xffffccccffffcccc, 0xffffffffffff0000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xfafafafff0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xfcfcfcfff0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xfcfcfdfdf0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xfcfdfcfdf0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffaaaaf0f0f0f0, 0xfffffffff0f0f0f0], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffeeeef0f0e0e0, 0xffffffff00000000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xfffff0f5f0f0f0f0, 0xffffffff00000000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xfffffefef0f0f0f0, 0xffffffff00000000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffff0f0f0a0a], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffff0f0f0e0e], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00ff00aa, 0xfffffffff0f0f0f0], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xfffffffff0f0f0f0, 0xffffffffffffaaaa], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (2, 0xffffaaaaffffaaaa, 0xffffffff00000000), (1, 0xffffaaaa, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff5555ffff0000, 0xffffaaaaffffaaaa, 0xfffffffff0f0f0f0], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff5555ffff0000, 0xffffccccffffcccc, 0xfffffffff0f0f0f0], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffffaaaaf0f0a0a0, 0xffffffff00000000, 0xffffffffffff0000], [(4, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (0, 0xfffffffff0f0f0f0, 0xffffaaaaffffaaaa), (1, 0xffff0000ffff0000, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffffaaaaf0f0a0a0, 0xfffffffff0f0f0f0, 0xffffffffffff0000], [(3, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (0, 0xfffffffff0f0f0f0, 0xffffaaaaffffaaaa)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffffccccf0f0c0c0, 0xfffffffff0f0f0f0, 0xffffffffffff0000], [(3, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (0, 0xfffffffff0f0f0f0, 0xffffccccffffcccc)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffffeeeeffffeeee, 0xfffffffff0f0f0f0, 0xffffffffffff0000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff33ff22ff33ff22, 0xffff0000ffff0000, 0xffffffff00000000, 0xfffffffff0f0f0f0], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xffff0000ffff0000, 0xffffffaafff0ffa0, 0xffffffff00000000, 0xfffffffff0f0f0f0], []),
  ([0xaaaaffffaaaaaaaa, 0xcccccccccccccccc, 0xeeeeeeeeeeeeeeee, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xfffffffff0f0f0f0], []),
  ([0xaaaaffffaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffaaaaffffaaaa, 0xfffffffff0f0f0f0], []),
  ([0xcccccccccccccccc, 0xdddddddddcdcdcdc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffffaaaaaaaa, 0xfffffffff0f0f0f0], []),
  ([0xcccccccccccccccc, 0xeeeeeeeee0e0e0e0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffffaaaaaaaa, 0xfffffffff0f0f0f0], [(4, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (0, 0xfffffffff0f0f0f0, 0xeeeeeeeeeeeeeeee)])]),
  ([0xcccccccccccccccc, 0xeeeeeeeeeeeeeeee, 0xf0f0fffff0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffffaaaaaaaa], []),
  ([0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffeeeeaaaaaaaa, 0xffffffff00000000], []),
  ([0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffffeeeeffffeeee, 0xffffffffaaaaaaaa, 0xffffffffffff0000], []),
  ([0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff33ff22ff33ff22, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffaaaaaaaa], []),
  ([0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffff5555ffff5050, 0xffffffffaaaaaaaa, 0xfffffffff0f0f0f0], []),
  ([0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffaaaaf0f0a0a0, 0xffffffff00000000, 0xffffffffaaaaaaaa], [(3, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (0, 0xfffffffff0f0f0f0, 0xffffaaaaffffaaaa)])]),
  ([0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffaaaaf0f0a0a0, 0xffffffffaaaaaaaa, 0xfffffffff0f0f0f0], [(4, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (0, 0xfffffffff0f0f0f0, 0xffffaaaaffffaaaa)])]),
  ([0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffeeeeffffeeee, 0xffffffffaaaaaaaa, 0xfffffffff0f0f0f0], []),
  ([0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffffaaaaffffaaaa, 0xffffffffaaaaaaaa, 0xfffffffff0f0f0f0, 0xffffffffffff0000], [(3, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)])])
]
def keys_63_5 : Array (List Sig) := lv_63_5.map Prod.fst
set_option maxHeartbeats 0 in
theorem chk_63_5_0 : checkRange true (vars6 63) (graphGoal 63) ps_63 rs_63 keys_63_4 5 lv_63_5 0 16 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem chk_63_5_16 : checkRange true (vars6 63) (graphGoal 63) ps_63 rs_63 keys_63_4 5 lv_63_5 16 16 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem chk_63_5_32 : checkRange true (vars6 63) (graphGoal 63) ps_63 rs_63 keys_63_4 5 lv_63_5 32 16 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem chk_63_5_48 : checkRange true (vars6 63) (graphGoal 63) ps_63 rs_63 keys_63_4 5 lv_63_5 48 16 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem chk_63_5_64 : checkRange true (vars6 63) (graphGoal 63) ps_63 rs_63 keys_63_4 5 lv_63_5 64 16 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem chk_63_5_80 : checkRange true (vars6 63) (graphGoal 63) ps_63 rs_63 keys_63_4 5 lv_63_5 80 16 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem chk_63_5_96 : checkRange true (vars6 63) (graphGoal 63) ps_63 rs_63 keys_63_4 5 lv_63_5 96 10 = true := by decide +kernel
theorem lv_63_5_ok : ∀ i < keys_63_5.size, ∀ v, keys_63_5[i]? = some v → Impossible (graphGoal 63) 5 v.toFinset := by
  apply level_of_nodes
  intro i hi nd hnd
  have hsz : lv_63_5.size = 106 := by decide +kernel
  by_cases h0 : i < 16
  · exact checkRange_sound (fun _ => rfl) ps_63_ok (by decide) rs_63_ok (fun _ => lv_63_4_ok) chk_63_5_0 i (by omega) h0 nd hnd
  by_cases h1 : i < 32
  · exact checkRange_sound (fun _ => rfl) ps_63_ok (by decide) rs_63_ok (fun _ => lv_63_4_ok) chk_63_5_16 i (by omega) h1 nd hnd
  by_cases h2 : i < 48
  · exact checkRange_sound (fun _ => rfl) ps_63_ok (by decide) rs_63_ok (fun _ => lv_63_4_ok) chk_63_5_32 i (by omega) h2 nd hnd
  by_cases h3 : i < 64
  · exact checkRange_sound (fun _ => rfl) ps_63_ok (by decide) rs_63_ok (fun _ => lv_63_4_ok) chk_63_5_48 i (by omega) h3 nd hnd
  by_cases h4 : i < 80
  · exact checkRange_sound (fun _ => rfl) ps_63_ok (by decide) rs_63_ok (fun _ => lv_63_4_ok) chk_63_5_64 i (by omega) h4 nd hnd
  by_cases h5 : i < 96
  · exact checkRange_sound (fun _ => rfl) ps_63_ok (by decide) rs_63_ok (fun _ => lv_63_4_ok) chk_63_5_80 i (by omega) h5 nd hnd
  exact checkRange_sound (fun _ => rfl) ps_63_ok (by decide) rs_63_ok (fun _ => lv_63_4_ok) chk_63_5_96 i (by omega) (by omega) nd hnd

def lv_63_6 : Array NodeData := #[
  ([0xeeee, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xf0f0a0a, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(3, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (3, 0xfffffffff0f0f0f0, 0xffffaaaaffffaaaa)]), (4, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (3, 0xfffffffff0f0f0f0, 0xffffaaaaffffaaaa)]), (7, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000)])]),
  ([0x55554444, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xeeeeeeee, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xfffffffff0f0f0f0], []),
  ([0xeeeeeeee, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffaaffaaffaaffaa, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xffffaaaa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xfffffffff0f0f0f0], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (2, 0xffffaaaaffffaaaa, 0xffffffff00000000)])]),
  ([0xffffcccc, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffffff00ffffff00, 0xffffffff00000000], []),
  ([0xffffcccc, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xfffffffff0f0f0f0], []),
  ([0xffffeeee, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (1, 0xffffaaaaffffaaaa, 0xcccccccccccccccc), (2, 0xffffeeeeffffeeee, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(5, [(1, 0xff00ff00ff00ff00, 0xffff0000ffff0000)])]),
  ([0xcccccccccc, 0xaaaaaaaaaaaaaaaa, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(5, [(1, 0xff00ff00ff00ff00, 0xffff0000ffff0000)])]),
  ([0xff000000aa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xff000000f0, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xfffffffff0f0f0f0], []),
  ([0x4444cccccccc, 0xaaaaaaaaaaaaaaaa, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(5, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000)])]),
  ([0x555500000000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffaaaaffffaaaa, 0xfffffffff0f0f0f0], [(3, [(3, 0xffffaaaaffffaaaa, 0xffffffff00000000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (19, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)])]),
  ([0x555500000000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xfffffffff0f0f0f0], [(3, [(3, 0xffffaaaaffffaaaa, 0xffffffff00000000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (4, [(3, 0xffffaaaaffffaaaa, 0xffffffff00000000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (5, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000)])]),
  ([0x555500004444, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (1, 0xcccccccccccccccc, 0xffffffff00000000), (2, 0xffffffffcccccccc, 0xffffaaaaffffaaaa)])]),
  ([0x555500005050, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xfffffffff0f0f0f0], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (2, 0xfffffffff0f0f0f0, 0xffffaaaaffffaaaa)]), (3, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (2, 0xfffffffff0f0f0f0, 0xffffaaaaffffaaaa)]), (19, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)])]),
  ([0xaaff0000aaaa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xeeee0000eeee, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xfffffffff0f0f0f0], []),
  ([0xeeee0000eeee, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffaaaaaaaa], []),
  ([0xf0ff0000f0f0, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0fff0fff0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xf5f50000f0f0, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf5f5f5f5f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xffff00000000, 0xff00ff00f000f0, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xfffffffff0f0f0f0], []),
  ([0xffff00000000, 0x5555555550505050, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xfffffffff0f0f0f0], [(11, [(2, 0xfffffffff0f0f0f0, 0xaaaaaaaaaaaaaaaa)])]),
  ([0xffff00000000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xeeeeeeeeeeeeeeee, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xfffffffff0f0f0f0], []),
  ([0xffff00000000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffccffccffccffcc, 0xffff0000ffff0000, 0xfffffffff0f0f0f0], [(1, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (3, 0xffff0000ffff0000, 0xffffffff00000000)]), (5, [(1, 0xcccccccccccccccc, 0xff00ff00ff00ff00)]), (13, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (3, 0xffff0000ffff0000, 0xffffffff00000000)])]),
  ([0xffff00000000, 0xcccccccccccccccc, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffffaaaaaaaa], []),
  ([0xffff0000aaaa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffffaaaaffffaaaa, 0xffffffff00000000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (1, 0xffffaaaaffffaaaa, 0xffffffff00000000), (2, 0xffffffffffffaaaa, 0xffff0000ffff0000)]), (3, [(1, 0xffffaaaaffffaaaa, 0xffffffff00000000)])]),
  ([0xffff0000aaaa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffffffff00000000, 0xffffffffffff0000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (2, 0xffffffffaaaaaaaa, 0xffff0000ffff0000), (1, 0xffff0000ffff0000, 0xffffffff00000000)])]),
  ([0xffff0000aaaa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffffffff00000000, 0xffffffffffffaaaa], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (1, 0xffffaaaaffffaaaa, 0xffffffff00000000), (2, 0xffffffffffffaaaa, 0xffff0000ffff0000)])]),
  ([0xffff0000aaaa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffffffffaaaaaaaa, 0xffffffffffff0000], [(5, [(2, 0xffffffffaaaaaaaa, 0xffff0000ffff0000)])]),
  ([0xffff0000aaaa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xfffffffff0f0f0f0], [(3, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)])]),
  ([0xffff0000aaaa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffffaaaaaaaa, 0xfffffffff0f0f0f0], [(3, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (5, [(2, 0xffffffffaaaaaaaa, 0xffff0000ffff0000)])]),
  ([0xffff0000aaaa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xfffffffff0f0f0f0], [(3, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (4, [(2, 0xffffffffaaaaaaaa, 0xffff0000ffff0000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (11, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)])]),
  ([0xffff0000aaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffffaaaaffffaaaa, 0xffffffff00000000, 0xffffffffaaaaaaaa], [(3, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (4, [(2, 0xffffffffaaaaaaaa, 0xffff0000ffff0000)])]),
  ([0xffff0000eeee, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xffff0000f0f0, 0x5555555500000000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xfffffffff0f0f0f0], [(10, [(2, 0xfffffffff0f0f0f0, 0xffff0000ffff0000)])]),
  ([0xffff0000f0f0, 0x5555555550505050, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(3, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (2, 0xfffffffff0f0f0f0, 0xaaaaaaaaaaaaaaaa)])]),
  ([0xffff0000f0f0, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffffaaaaaaaa, 0xfffffffff0f0f0f0], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (2, 0xfffffffff0f0f0f0, 0xffff0000ffff0000)]), (4, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (2, 0xfffffffff0f0f0f0, 0xffff0000ffff0000)])]),
  ([0xffff0000f0f0, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffffffff00000000, 0xfffffffff0f0f0f0, 0xffffffffffff0000], [(0, [(2, 0xfffffffff0f0f0f0, 0xffff0000ffff0000), (1, 0xffff0000ffff0000, 0xffffffff00000000)])]),
  ([0xffff0000f0f0, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xfffffffff0f0f0f0, 0xffffffffffff0000], [(3, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (7, [(1, 0xffff0000ffff0000, 0xffffffff00000000)])]),
  ([0x440044cccccccc, 0xaaaaaaaaaaaaaaaa, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(5, [(1, 0xaaaaaaaaaaaaaaaa, 0xff00ff00ff00ff00)])]),
  ([0x550000ffff0000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffffffff00000000], [(5, [(1, 0xaaaaaaaaaaaaaaaa, 0xff00ff00ff00ff00)])]),
  ([0x55005500500050, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xfffffffff0f0f0f0], []),
  ([0x55005500550000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xaa00ff00aa00aa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xbb00bb00aa00aa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(1, [(1, 0x3333333300000000, 0xaaaaaaaaaaaaaaaa), (2, 0xbbbbbbbbaaaaaaaa, 0xff00ff00ff00ff00)])]),
  ([0xee00ee00ee00ee, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xfffffffff0f0f0f0], [(2, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)])]),
  ([0xee00ee00ee00ee, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffaaaaaaaa], [(2, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)])]),
  ([0xf000ff00f000f0, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0fffff0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xf300f300f000f0, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf3f3f3f3f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xf500f500f000f0, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf5f5f5f5f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xff003300ff0000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(1, [(1, 0x3333333300000000, 0xffff0000ffff0000), (2, 0xffff3333ffff0000, 0xff00ff00ff00ff00)])]),
  ([0xff005500ff0000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xff00aa00ff00aa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffffffff00000000, 0xffffffffffff0000], []),
  ([0xff00aa00ff00aa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xfffffffff0f0f0f0], []),
  ([0xff00aa00ff00aa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffaaaaaaaa], []),
  ([0xff00cc00ff00cc, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffffffff00000000, 0xffffffffffff0000], [(2, [(1, 0xcccccccccccccccc, 0xffff0000ffff0000), (1, 0xffff0000ffff0000, 0xffffffff00000000)])]),
  ([0xff00cc00ff00cc, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xfffffffff0f0f0f0], [(2, [(1, 0xcccccccccccccccc, 0xffff0000ffff0000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)])]),
  ([0xff00ee00ff00ee, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(2, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (1, 0xffffaaaaffffaaaa, 0xcccccccccccccccc)])]),
  ([0xff00ff00000000, 0xf0f0a0a0f0f0a0a, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xff00ff00aa00aa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xfffffffff0f0f0f0], [(2, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)])]),
  ([0xff00ff00aa00aa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffffaaaaaaaa, 0xfffffffff0f0f0f0], [(2, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (5, [(2, 0xffffffffaaaaaaaa, 0xff00ff00ff00ff00)]), (6, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)])]),
  ([0xff00ff00aa00aa, 0xcccccccccccccccc, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(1, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (2, 0xffffffffaaaaaaaa, 0xff00ff00ff00ff00)])]),
  ([0xff00ff00cc00cc, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000, 0xffffaaaaffffaaaa, 0xffffffff00000000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (1, 0xcccccccccccccccc, 0xffffffff00000000), (2, 0xffffffffcccccccc, 0xff00ff00ff00ff00)]), (3, [(1, 0xcccccccccccccccc, 0xffffffff00000000), (2, 0xffffffffcccccccc, 0xff00ff00ff00ff00)])]),
  ([0xff00ff00ee00ee, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xff00ff00ee00ee, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xffffffffaaaaaaaa, 0xcccccccccccccccc), (2, 0xffffffffeeeeeeee, 0xff00ff00ff00ff00)])]),
  ([0xff00ff00ee00ee, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffaaaaaaaa], []),
  ([0xff00ff00f000f0, 0x3333333330303030, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(1, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (2, 0xfffffffff0f0f0f0, 0xff00ff00ff00ff00)])]),
  ([0xff00ff00f000f0, 0x5555555500000000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xfffffffff0f0f0f0], []),
  ([0xff00ff00f000f0, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffffaaaaaaaa, 0xfffffffff0f0f0f0], [(4, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (2, 0xfffffffff0f0f0f0, 0xff00ff00ff00ff00)])]),
  ([0xff00ff00f000f0, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xfffffffff0f0f0f0, 0xffffffffffff0000], [(3, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (2, 0xfffffffff0f0f0f0, 0xff00ff00ff00ff00)])]),
  ([0xff00ff00ff0000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffffccccffffcccc, 0xffffffff00000000], [(1, [(1, 0xffff0000ffff0000, 0xffffffff00000000), (2, 0xffffffffffff0000, 0xff00ff00ff00ff00)])]),
  ([0xff00ff00ff0000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xfffffffff0f0f0f0], [(2, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (1, 0xffff0000ffff0000, 0xffffffff00000000)])]),
  ([0xff00ff00ff0000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xfffffffff0f0f0f0, 0xffffffffffff0000], [(2, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (1, 0xffff0000ffff0000, 0xffffffff00000000)]), (5, [(2, 0xffffffffffff0000, 0xff00ff00ff00ff00)]), (6, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (1, 0xffff0000ffff0000, 0xffffffff00000000)])]),
  ([0xff00ff00ff00aa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xff00ff00ff00cc, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xff00ff00ff00cc, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(1, 0xffff0000ffff0000, 0xffffffff00000000), (1, 0xffffffffffff0000, 0xcccccccccccccccc), (2, 0xffffffffffffcccc, 0xff00ff00ff00ff00)])]),
  ([0xff00ff00ff00cc, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffffff0000], []),
  ([0xf0f0a0a0f0f0a0a, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffccffccffccffcc, 0xffff0000ffff0000, 0xffffffff00000000], [(1, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (2, 0xffffaaaaffffaaaa, 0xf0f0f0f0f0f0f0f0)])]),
  ([0xf0f0a0a0f0f0a0a, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffcccccccc], []),
  ([0xf0f0e0e0f0f0e0e, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffaaaaffffaaaa, 0xffffffff00000000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (1, 0xffffaaaaffffaaaa, 0xcccccccccccccccc)]), (3, [(1, 0xffffaaaaffffaaaa, 0xcccccccccccccccc), (2, 0xffffeeeeffffeeee, 0xf0f0f0f0f0f0f0f0)])]),
  ([0xf0f0e0e0f0f0e0e, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xf0f0f0f0f0f0a0a, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffaaaaffffaaaa, 0xffffffff00000000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (1, 0xffffaaaaffffaaaa, 0xffffffff00000000)]), (3, [(1, 0xffffaaaaffffaaaa, 0xffffffff00000000), (2, 0xffffffffffffaaaa, 0xf0f0f0f0f0f0f0f0)])]),
  ([0xf0f0f0f0f0f0a0a, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(19, [(2, 0xffffffffffffaaaa, 0xf0f0f0f0f0f0f0f0)])]),
  ([0xf0f0f0f0f0f0a0a, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffaaaaaaaa], [(19, [(2, 0xffffffffffffaaaa, 0xf0f0f0f0f0f0f0f0)])]),
  ([0xf0f0f0f0f0f0a0a, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffffff0000], [(19, [(2, 0xffffffffffffaaaa, 0xf0f0f0f0f0f0f0f0)])]),
  ([0xf0f0f0f0f0f0a0a, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffffffaaaa], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (1, 0xffffaaaaffffaaaa, 0xffffffff00000000)]), (19, [(2, 0xffffffffffffaaaa, 0xf0f0f0f0f0f0f0f0)])]),
  ([0x5050555550505050, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0fffff0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0x5055505550505050, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0fff0fff0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0x5555005555550000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0x5555444455554444, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffffffff00000000, 0xffffffffffff0000], []),
  ([0x5555444455554444, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xfffffffff0f0f0f0], []),
  ([0x5555555500000000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffffccccffffcccc, 0xffffffffffff0000], []),
  ([0x5555555500000000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffccffccffccffcc, 0xffff0000ffff0000, 0xfffffffff0f0f0f0], [(1, [(3, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (5, [(1, 0xcccccccccccccccc, 0xff00ff00ff00ff00)]), (13, [(3, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)])]),
  ([0x5555555500000000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffccccffffcccc, 0xfffffffff0f0f0f0], []),
  ([0x5555555550505050, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xfffffffff0f0f0f0, 0xffffffffffff0000], [(0, [(2, 0xfffffffff0f0f0f0, 0xaaaaaaaaaaaaaaaa), (1, 0xffff0000ffff0000, 0xffffffff00000000)]), (3, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (2, 0xfffffffff0f0f0f0, 0xaaaaaaaaaaaaaaaa)])]),
  ([0x5555555550505050, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffaaaaaaaa, 0xfffffffff0f0f0f0], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (2, 0xfffffffff0f0f0f0, 0xaaaaaaaaaaaaaaaa)])]),
  ([0x5555555550505050, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffffaaaaaaaa, 0xfffffffff0f0f0f0], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (2, 0xfffffffff0f0f0f0, 0xaaaaaaaaaaaaaaaa)]), (4, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (7, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)])]),
  ([0x5555555555550000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xfffffffff0f0f0f0], [(3, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (2, 0xffffffffffff0000, 0xaaaaaaaaaaaaaaaa)])]),
  ([0x5555555555550000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xfffffffff0f0f0f0], [(3, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (2, 0xffffffffffff0000, 0xaaaaaaaaaaaaaaaa)]), (4, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (1, 0xffff0000ffff0000, 0xffffffff00000000)]), (10, [(1, 0xffff0000ffff0000, 0xffffffff00000000)])]),
  ([0x5555555555550000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xfffffffff0f0f0f0, 0xffffffffffff0000], [(3, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (2, 0xffffffffffff0000, 0xaaaaaaaaaaaaaaaa)]), (5, [(2, 0xffffffffffff0000, 0xaaaaaaaaaaaaaaaa)])]),
  ([0x5555555555550000, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffaaaaffffaaaa, 0xffffffff00000000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (1, 0xffffaaaaffffaaaa, 0xffffffff00000000), (2, 0xffffffffffffaaaa, 0xaaaaaaaaaaaaaaaa)]), (3, [(1, 0xffffaaaaffffaaaa, 0xffffffff00000000), (2, 0xffffffffffffaaaa, 0xaaaaaaaaaaaaaaaa)])]),
  ([0x5555555555550000, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffaaaaaaaa], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xffffffffaaaaaaaa, 0xffff0000ffff0000), (2, 0xffffffffffffaaaa, 0xaaaaaaaaaaaaaaaa)])]),
  ([0x5555555555550000, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffffffaaaa], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (1, 0xffffaaaaffffaaaa, 0xffffffff00000000), (2, 0xffffffffffffaaaa, 0xaaaaaaaaaaaaaaaa)])]),
  ([0x5555555555550000, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffffaaaaaaaa, 0xffffffffffff0000], [(5, [(2, 0xffffffffffff0000, 0xaaaaaaaaaaaaaaaa)])]),
  ([0x5555555555550000, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffffaaaaffffaaaa, 0xffffffff00000000, 0xffffffffffff0000], [(3, [(2, 0xffffffffffff0000, 0xaaaaaaaaaaaaaaaa)]), (4, [(1, 0xffff0000ffff0000, 0xffffffff00000000)])]),
  ([0x5555555555554444, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xaaaa8888ffffcccc, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaffffeeee, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(1, 0xcccccccccccccccc, 0xffff0000ffff0000), (2, 0xffffccccffffcccc, 0xffffffff00000000), (1, 0xffffcccc, 0xaaaaaaaaaaaaaaaa)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xaaaaaaff00000000, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(1, 0xff00ff00ff00ff00, 0xffff0000ffff0000), (2, 0xffffff00ffffff00, 0xaaaaaaaaaaaaaaaa), (3, 0x5555550055555500, 0xffffffff00000000)]), (2, [(2, 0xffffff00ffffff00, 0xaaaaaaaaaaaaaaaa), (3, 0x5555550055555500, 0xffffffff00000000)]), (3, [(2, 0xffffff00ffffff00, 0xaaaaaaaaaaaaaaaa), (3, 0x5555550055555500, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xaaaaffffaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xfffffffff0f0f0f0], [(4, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (3, 0xffff0000ffff0000, 0xffffffff00000000)]), (5, []), (11, [(1, 0xffff00000000, 0xaaaaaaaaaaaaaaaa)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xaaaaffffaaaaeeee, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xaaaaffffaaaafafa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xfffffffff0f0f0f0], [(3, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (1, 0xffff0000f0f0, 0xaaaaaaaaaaaaaaaa)]), (4, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (2, 0xfffffffff0f0f0f0, 0xffff0000ffff0000)]), (10, [(2, 0xfffffffff0f0f0f0, 0xffff0000ffff0000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xaaffaaeeaaffaaee, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xaaffaaffaaeeaaee, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(4, [(1, 0xcccccccccccccccc, 0xffffffff00000000), (2, 0xffffffffcccccccc, 0xff00ff00ff00ff00)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xaaffaaffaafaaafa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xfffffffff0f0f0f0], []),
  ([0xaaaaaaaaaaaaaaaa, 0xaaffaaffaaffaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcc00cc44cc00cc44, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (2, 0xffffaaaaffffaaaa, 0xff00ff00ff00ff00), (3, 0xff00aa00ff00aa, 0xcccccccccccccccc)]), (1, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (2, 0xffffaaaaffffaaaa, 0xff00ff00ff00ff00)]), (3, [(2, 0xffffaaaaffffaaaa, 0xff00ff00ff00ff00), (3, 0xff00aa00ff00aa, 0xcccccccccccccccc)]), (4, [(2, 0xffffaaaaffffaaaa, 0xff00ff00ff00ff00), (3, 0xff00aa00ff00aa, 0xcccccccccccccccc)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcc88cc88ffaaffaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccc8888ffffaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (3, 0xcccccccccccccccc, 0xffffffff00000000), (3, 0x3333333300000000, 0xffffaaaaffffaaaa)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccc00ffffff00, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccc00cc00, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffaaaaffffaaaa, 0xffffffff00000000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (1, 0xff00ff00ff00ff00, 0xffffffff00000000), (0, 0xffffffffff00ff00, 0xcccccccccccccccc)]), (2, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (0, 0xffffffffff00ff00, 0xcccccccccccccccc)]), (3, [(1, 0xff00ff00ff00ff00, 0xffffffff00000000), (0, 0xffffffffff00ff00, 0xcccccccccccccccc)]), (6, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccc88cc88, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xffffffffaaaaaaaa, 0xff00ff00ff00ff00), (0, 0xffffffffffaaffaa, 0xcccccccccccccccc)]), (1, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xffffffffaaaaaaaa, 0xff00ff00ff00ff00)]), (2, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (0, 0xffffffffffaaffaa, 0xcccccccccccccccc)]), (6, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccc88cc88, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffaaaaaaaa], [(2, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (0, 0xffffffffffaaffaa, 0xcccccccccccccccc)]), (6, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccc00, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(1, 0xffff0000ffff0000, 0xffffffff00000000), (1, 0xffffffffffff0000, 0xff00ff00ff00ff00), (0, 0xffffffffffffff00, 0xcccccccccccccccc)]), (1, [(1, 0xffff0000ffff0000, 0xffffffff00000000), (1, 0xffffffffffff0000, 0xff00ff00ff00ff00)]), (2, [(1, 0xffff0000ffff0000, 0xffffffff00000000), (0, 0xffffffffffffff00, 0xcccccccccccccccc)]), (6, [(1, 0xffff0000ffff0000, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccc00, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffffff0000], [(2, [(1, 0xffff0000ffff0000, 0xffffffff00000000), (0, 0xffffffffffffff00, 0xcccccccccccccccc)]), (6, [(1, 0xffff0000ffff0000, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xccccccccffeeffee, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xccccccccffffeeee, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (2, 0xffffaaaaffffaaaa, 0xffffffff00000000), (1, 0xffffaaaa, 0xcccccccccccccccc)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xccccccccffffffcc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xccccccff00000000, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(1, 0xff00ff00ff00ff00, 0xffff0000ffff0000), (2, 0xffffff00ffffff00, 0xcccccccccccccccc), (3, 0x3333330033333300, 0xffffffff00000000)]), (1, [(1, 0xff00ff00ff00ff00, 0xffff0000ffff0000), (3, 0x3333330033333300, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xccccdddd00000000, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (2, 0xffffaaaaffffaaaa, 0xcccccccccccccccc), (3, 0x3333222233332222, 0xffffffff00000000)]), (1, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (3, 0x3333222233332222, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xccccddddcccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(15, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xccccffeeccccffee, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(1, [(1, 0xaaaaaaaaaaaaaaaa, 0xff00ff00ff00ff00), (2, 0xffaaffaaffaaffaa, 0xffff0000ffff0000)]), (2, [(2, 0xffaaffaaffaaffaa, 0xffff0000ffff0000), (1, 0xffaa0000ffaa, 0xcccccccccccccccc)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xccccffffcccceeee, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xccccffffccccfcfc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xfffffffff0f0f0f0], [(3, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (1, 0xffff0000f0f0, 0xcccccccccccccccc)]), (12, [(2, 0xfffffffff0f0f0f0, 0xffff0000ffff0000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xccccffffccccffcc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(2, [(2, 0xffffffffff00ff00, 0xffff0000ffff0000), (1, 0xffff0000ff00, 0xcccccccccccccccc)]), (6, [(1, 0xffff0000ff00, 0xcccccccccccccccc)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xccddccdd00000000, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xff00ff00ff00ff00), (2, 0xffaaffaaffaaffaa, 0xcccccccccccccccc), (3, 0x3322332233223322, 0xffffffff00000000)]), (1, [(1, 0xaaaaaaaaaaaaaaaa, 0xff00ff00ff00ff00), (3, 0x3322332233223322, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xccffcceeccffccee, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xccffccffcceeccee, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(1, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (2, 0xffffffffaaaaaaaa, 0xff00ff00ff00ff00)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xccffccffccfcccfc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xfffffffff0f0f0f0], [(1, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (2, 0xfffffffff0f0f0f0, 0xff00ff00ff00ff00)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xccffccffccffcccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(1, [(1, 0xffff0000ffff0000, 0xffffffff00000000), (2, 0xffffffffffff0000, 0xff00ff00ff00ff00)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xddddddccddddddcc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(1, [(1, 0xff00ff00ff00ff00, 0xffff0000ffff0000), (2, 0xffffff00ffffff00, 0xaaaaaaaaaaaaaaaa)]), (2, [(2, 0xffffff00ffffff00, 0xaaaaaaaaaaaaaaaa), (1, 0x5555550055555500, 0xcccccccccccccccc)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xdddddddddcdcdcdc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xfffffffff0f0f0f0], [(4, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (1, 0x5555555550505050, 0xcccccccccccccccc)]), (12, [(2, 0xfffffffff0f0f0f0, 0xaaaaaaaaaaaaaaaa)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xddddddddddccddcc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(2, [(2, 0xffffffffff00ff00, 0xaaaaaaaaaaaaaaaa), (1, 0x5555555555005500, 0xcccccccccccccccc)]), (6, [(1, 0x5555555555005500, 0xcccccccccccccccc)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xddddddddddddcccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xeeee0000eeeeeeee, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xeeeeee00eeeeee00, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xeeeeeeeee0e0e0e0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xfffffffff0f0f0f0], [(4, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (0, 0xfffffffff0f0f0f0, 0xeeeeeeeeeeeeeeee)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xeeeeeeeeee00ee00, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(1, [(1, 0xff00ff00ff00ff00, 0xffffffff00000000), (0, 0xffffffffff00ff00, 0xeeeeeeeeeeeeeeee)]), (2, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (0, 0xffffffffff00ff00, 0xeeeeeeeeeeeeeeee)]), (6, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xeeeeeeeeeeee0000, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(4, [(1, 0xffff0000ffff0000, 0xffffffff00000000), (0, 0xffffffffffff0000, 0xeeeeeeeeeeeeeeee)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xeeeeeeeeeeeeeeee, 0xf0f0fffff0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xeeeeeeeeeeeeeeee, 0xf0fff0fff0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xeeeeeeeeeeeeeeee, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xfffffffff0f0f0f0, 0xffffffffffff0000], [(8, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (1, 0xffff0000ffff0000, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xeeeeffffeeeeeeee, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xeeffeeffeeeeeeee, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(6, [(1, 0xaaffaaffaaaaaaaa, 0xcccccccccccccccc)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffeeffeecccccccc, 0xffff0000ffff0000, 0xffffffff00000000], [(1, [(1, 0xaaaaaaaaaaaaaaaa, 0xff00ff00ff00ff00), (0, 0xffaaffaaffaaffaa, 0xffffffff00000000)]), (2, [(0, 0xffaaffaaffaaffaa, 0xffffffff00000000), (1, 0xffaaffaa00000000, 0xcccccccccccccccc)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffff0000ffffeeee, 0xffffffff00000000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (2, 0xeeeeeeeeeeeeeeee, 0xffffffff00000000), (1, 0xeeeeeeee, 0xffff0000ffff0000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffff005500000000, 0xffffffff00000000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xff00ff00ff00ff00), (2, 0xffaaffaaffaaffaa, 0xffff0000ffff0000), (3, 0xffaa0000ffaa, 0xffffffff00000000)]), (3, [(1, 0xaaaaaaaaaaaaaaaa, 0xff00ff00ff00ff00), (3, 0xffaa0000ffaa, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffff00eeffff00ee, 0xffffffff00000000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffff00ffffff00aa, 0xffffffff00000000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffff00ffffff00cc, 0xffffffff00000000], [(3, [(1, 0xcccccccccccccccc, 0xffffffff00000000), (2, 0xffffffffcccccccc, 0xff00ff00ff00ff00)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffff5555ffff4444, 0xffffffff00000000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffaaaacccc8888, 0xffffffff00000000], [(8, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffaaffffffaaaa, 0xffffffff00000000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (3, 0xff00ff00ff00ff00, 0xffffffff00000000), (1, 0xff00ff00000000, 0xffffaaaaffffaaaa)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffccccaaaa8888, 0xffffffff00000000], [(3, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (0, 0xffffccccffffcccc, 0xffffffffaaaaaaaa)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffccccff00cc00, 0xffffffff00000000], [(1, [(1, 0xff00ff00ff00ff00, 0xffffffff00000000), (0, 0xffffffffff00ff00, 0xffffccccffffcccc)]), (2, [(1, 0xcccccccccccccccc, 0xffff0000ffff0000), (0, 0xffffffffff00ff00, 0xffffccccffffcccc)]), (6, [(1, 0xcccccccccccccccc, 0xffff0000ffff0000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffccffffffcccc, 0xffffffff00000000], [(6, [(1, 0xffff00ffffff0000, 0xcccccccccccccccc)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffddddffffcccc, 0xffffffff00000000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffeeee00000000, 0xffffffff00000000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (1, 0xffffaaaaffffaaaa, 0xcccccccccccccccc), (0, 0xffffeeeeffffeeee, 0xffffffff00000000)]), (8, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffeeeeaaaaaaaa, 0xffffffff00000000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffeeeecccccccc, 0xffffffff00000000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffeeeeffff0000, 0xffffffff00000000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffcccccccccc, 0xffffffff00000000], [(1, [(1, 0xff00ff00ff00ff00, 0xffff0000ffff0000), (0, 0xffffff00ffffff00, 0xffffffff00000000)]), (2, [(0, 0xffffff00ffffff00, 0xffffffff00000000), (1, 0xffffff0000000000, 0xcccccccccccccccc)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffff0000eeee], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffff00ee00ee], [(6, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffff00ff00aa], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffff00ff00cc], [(6, [(1, 0xcccccccccccccccc, 0xffff0000ffff0000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffff55554444], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffffffaaaa], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (2, 0xffffaaaaffffaaaa, 0xffffffff00000000), (1, 0xffffaaaa, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffffffeeee], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (1, 0xffffaaaaffffaaaa, 0xffffffff00000000), (1, 0xffffffffffffaaaa, 0xcccccccccccccccc)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff00ffffff0000, 0xffffaaaaffffaaaa, 0xffffffff00000000], [(4, [(3, 0xff00ff00ff00ff00, 0xffffffff00000000), (1, 0xff00ff00000000, 0xffff0000ffff0000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff00ffffff0000, 0xffffccccffffcccc, 0xffffffff00000000], [(1, [(3, 0xff00ff00ff00ff00, 0xffffffff00000000), (1, 0xff00ff00000000, 0xffff0000ffff0000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff5555ffff0000, 0xffffaaaaffffaaaa, 0xffffffff00000000], [(3, [(3, 0xffffaaaaffffaaaa, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff5555ffff0000, 0xffffccccffffcccc, 0xffffffff00000000], [(1, [(3, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0x5555555500000000, 0xffff0000ffff0000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffffccccffffcccc, 0xffffffff00000000, 0xffffffffffffff00], [(1, [(1, 0xffff0000ffff0000, 0xffffffff00000000), (1, 0xffffffffffff0000, 0xff00ff00ff00ff00)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffffccccffffcccc, 0xffffffffaaaaaaaa, 0xffffffffffff0000], [(8, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xffff0000ffff0000, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffffeeeeffff0000, 0xffffffff00000000], [(1, [(0, 0xeeeeeeeeeeeeeeee, 0xffffffff00000000), (1, 0xeeeeeeee00000000, 0xffff0000ffff0000)]), (2, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (0, 0xeeeeeeeeeeeeeeee, 0xffffffff00000000), (1, 0xeeeeeeee00000000, 0xffff0000ffff0000)]), (4, [(0, 0xeeeeeeeeeeeeeeee, 0xffffffff00000000), (1, 0xeeeeeeee00000000, 0xffff0000ffff0000)]), (5, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffffeeeeffffeeee, 0xffffffff00000000, 0xffffffffffff0000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff33ff22ff33ff22, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (2, 0xffffaaaaffffaaaa, 0xcccccccccccccccc), (1, 0x3333222233332222, 0xff00ff00ff00ff00)]), (3, [(2, 0xffffaaaaffffaaaa, 0xcccccccccccccccc), (1, 0x3333222233332222, 0xff00ff00ff00ff00)]), (4, [(2, 0xffffaaaaffffaaaa, 0xcccccccccccccccc), (1, 0x3333222233332222, 0xff00ff00ff00ff00)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xffeeffeeff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(1, [(0, 0xeeeeeeeeeeeeeeee, 0xffffffff00000000), (1, 0xeeeeeeee00000000, 0xff00ff00ff00ff00)]), (5, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc)]), (8, [(1, 0xeeeeeeee00000000, 0xff00ff00ff00ff00)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000, 0xffffffaaff00ff00, 0xffffffff00000000], [(5, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000, 0xffffffccff00ff00, 0xffffffff00000000], [(1, [(0, 0xffffccccffffcccc, 0xffffffff00000000), (1, 0xffffcccc00000000, 0xff00ff00ff00ff00)]), (5, [(1, 0xcccccccccccccccc, 0xffff0000ffff0000)]), (8, [(1, 0xffffcccc00000000, 0xff00ff00ff00ff00)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f5f5f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffaaaaffffaaaa, 0xffffffff00000000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (3, 0xffffaaaaffffaaaa, 0xffffffff00000000)]), (3, [(3, 0xffffaaaaffffaaaa, 0xffffffff00000000), (1, 0x555500000000, 0xf0f0f0f0f0f0f0f0)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f5f5f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (3, 0xffffaaaaffffaaaa, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0fffff0f0f0f0, 0xff00ff00ff00ff00, 0xffccffccffccffcc, 0xffff0000ffff0000, 0xffffffff00000000], [(1, [(3, 0xffff0000ffff0000, 0xffffffff00000000), (1, 0xffff00000000, 0xf0f0f0f0f0f0f0f0)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0fffff0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffffaaaaaaaa], [(3, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xffff00000000, 0xf0f0f0f0f0f0f0f0)]), (4, [(3, 0xffff0000ffff0000, 0xffffffff00000000), (1, 0xffff00000000, 0xf0f0f0f0f0f0f0f0)]), (5, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0fff0fff0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffaaaaffffaaaa, 0xffffffff00000000], [(3, [(3, 0xff00ff00ff00ff00, 0xffffffff00000000), (1, 0xff00ff00000000, 0xf0f0f0f0f0f0f0f0)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0fff0fff0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffccccffffcccc, 0xffffffff00000000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf5f5f5f5f0f0f0f0, 0xff00ff00ff00ff00, 0xffccffccffccffcc, 0xffff0000ffff0000, 0xffffffff00000000], [(1, [(3, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0x5555555500000000, 0xf0f0f0f0f0f0f0f0)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf5f5f5f5f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffccccffffcccc, 0xffffffff00000000], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf5f5f5f5f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffffffff0000], [(3, [(3, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0x5555555500000000, 0xf0f0f0f0f0f0f0f0)]), (4, [(1, 0x5555555500000000, 0xf0f0f0f0f0f0f0f0), (1, 0xffff0000ffff0000, 0xffffffff00000000)]), (5, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xfefefefef0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (0, 0xeeeeeeeeeeeeeeee, 0xffffffff00000000)]), (4, [(0, 0xeeeeeeeeeeeeeeee, 0xffffffff00000000), (1, 0xeeeeeeee00000000, 0xf0f0f0f0f0f0f0f0)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffccffccffccffcc, 0xffff0000ffff0000, 0xffffffffaaaaaaaa, 0xfffffffff0f0f0f0], [(1, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (6, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (13, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffccffccffccffcc, 0xffff0000ffff0000, 0xfffffffff0f0f0f0, 0xffffffffffff0000], [(1, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (1, 0xffff0000ffff0000, 0xffffffff00000000)]), (6, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (1, 0xffff0000ffff0000, 0xffffffff00000000)]), (13, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (1, 0xffff0000ffff0000, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffff00ffffff00f0, 0xffffffff00000000, 0xfffffffff0f0f0f0], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffff5555ffff0000, 0xfffffffff0f0f0f0], [(3, [(3, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (5, []), (10, [(1, 0x5555555500000000, 0xffff0000ffff0000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffff5555ffff5050, 0xffffffff00000000, 0xfffffffff0f0f0f0], [(3, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (2, 0xfffffffff0f0f0f0, 0xaaaaaaaaaaaaaaaa)]), (4, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (1, 0x5555555550505050, 0xffff0000ffff0000)]), (11, [(2, 0xfffffffff0f0f0f0, 0xaaaaaaaaaaaaaaaa)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffaaaaf0f0a0a0, 0xffffffff00000000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (0, 0xfffffffff0f0f0f0, 0xffffaaaaffffaaaa)]), (3, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (0, 0xfffffffff0f0f0f0, 0xffffaaaaffffaaaa)]), (4, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (0, 0xfffffffff0f0f0f0, 0xffffaaaaffffaaaa)]), (19, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffaaaaf0f0a0a0, 0xffffffff00000000, 0xfffffffff0f0f0f0], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (0, 0xfffffffff0f0f0f0, 0xffffaaaaffffaaaa)]), (3, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (0, 0xfffffffff0f0f0f0, 0xffffaaaaffffaaaa)]), (7, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffaaaaffffaaaa, 0xfffffffff0f0f0f0, 0xffffffffffffaaaa], [(3, [(1, 0xffffaaaaffffaaaa, 0xffffffff00000000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (19, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffccccf0f0c0c0, 0xffffffff00000000, 0xfffffffff0f0f0f0], [(3, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (0, 0xfffffffff0f0f0f0, 0xffffccccffffcccc)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffccccffffcccc, 0xffffffffaaaaaaaa, 0xfffffffff0f0f0f0], [(8, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffeeeeffffeeee, 0xffffffff00000000, 0xfffffffff0f0f0f0], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xfffffafaf0f0f0f0, 0xffffffff00000000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (0, 0xffffaaaaffffaaaa, 0xffffffff00000000)]), (3, [(0, 0xffffaaaaffffaaaa, 0xffffffff00000000), (1, 0xffffaaaa00000000, 0xf0f0f0f0f0f0f0f0)]), (4, [(0, 0xffffaaaaffffaaaa, 0xffffffff00000000), (1, 0xffffaaaa00000000, 0xf0f0f0f0f0f0f0f0)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xfffffcfcf0f0f0f0, 0xffffffff00000000], [(0, [(1, 0xcccccccccccccccc, 0xffff0000ffff0000), (0, 0xffffccccffffcccc, 0xffffffff00000000)]), (3, [(0, 0xffffccccffffcccc, 0xffffffff00000000), (1, 0xffffcccc00000000, 0xf0f0f0f0f0f0f0f0)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffff0f0f0a0a], [(7, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffeeeeeeee, 0xfffffffff0f0f0f0], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xfffffffff0f0f0f0, 0xffffffffffffaaaa], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (1, 0xffffaaaaffffaaaa, 0xffffffff00000000)]), (19, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xfffffffff0f0f0f0, 0xffffffffffffcccc], []),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffffaaaaaaaa, 0xffffffffcccccccc, 0xfffffffff0f0f0f0], [(8, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (15, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffffaaaaaaaa, 0xffffffffeeeeeeee, 0xfffffffff0f0f0f0], [(1, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (15, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffffaaaaaaaa, 0xfffffffff0f0f0f0, 0xffffffffffff0000], [(3, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffffaaaaaaaa, 0xfffffffff0f0f0f0, 0xffffffffffffaaaa], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xffffffffaaaaaaaa, 0xffff0000ffff0000)]), (19, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffffcccccccc, 0xfffffffff0f0f0f0, 0xffffffffff00ff00], [(1, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (1, 0xff00ff00ff00ff00, 0xffffffff00000000)]), (2, [(1, 0xcccccccccccccccc, 0xffffffff00000000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (6, [(1, 0xcccccccccccccccc, 0xffffffff00000000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffffcccccccc, 0xfffffffff0f0f0f0, 0xffffffffffff0000], [(1, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (1, 0xffff0000ffff0000, 0xffffffff00000000)]), (8, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (1, 0xffff0000ffff0000, 0xffffffff00000000)]), (15, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xfffffffff0f0f0f0, 0xffffffffffff0000, 0xffffffffffffaaaa], [(0, [(1, 0xffff0000ffff0000, 0xffffffff00000000), (1, 0xffffffffffff0000, 0xaaaaaaaaaaaaaaaa)]), (19, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xfffffffff0f0f0f0, 0xffffffffffff0000, 0xffffffffffffcccc], [(1, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (1, 0xffff0000ffff0000, 0xffffffff00000000)]), (15, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xfffffffff0f0f0f0, 0xffffffffffffaaaa], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (1, 0xffffaaaaffffaaaa, 0xffffffff00000000)]), (3, [(1, 0xffffaaaaffffaaaa, 0xffffffff00000000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (4, [(1, 0xffffaaaaffffaaaa, 0xffffffff00000000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (19, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffffaaaaffffaaaa, 0xffffffff00000000, 0xfffffffff0f0f0f0, 0xffffffffffff0000], [(4, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (1, 0xffff0000ffff0000, 0xffffffff00000000)]), (5, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffffaaaaffffaaaa, 0xfffffffff0f0f0f0, 0xffffffffffff0000], [(3, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (4, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (1, 0xffff0000ffff0000, 0xffffffff00000000)]), (5, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000)]), (7, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (1, 0xffff0000ffff0000, 0xffffffff00000000)]), (19, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffffccccffffcccc, 0xffffff00ffffff00, 0xffffffff00000000, 0xfffffffff0f0f0f0], [(1, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (1, 0xff00ff00ff00ff00, 0xffff0000ffff0000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffffccccffffcccc, 0xffffffff00000000, 0xfffffffff0f0f0f0, 0xffffffffffff0000], [(1, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (1, 0xffff0000ffff0000, 0xffffffff00000000)]), (8, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (1, 0xffff0000ffff0000, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffffccccffffcccc, 0xfffffffff0f0f0f0, 0xffffffffffff0000], [(1, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (1, 0xffff0000ffff0000, 0xffffffff00000000)]), (8, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (1, 0xffff0000ffff0000, 0xffffffff00000000)])]),
  ([0xaaaaffffaaaaaaaa, 0xcccccccccccccccc, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(1, [(3, 0xffff0000ffff0000, 0xffffffff00000000), (1, 0xffff00000000, 0xaaaaaaaaaaaaaaaa)])]),
  ([0xaaaaffffaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffaaaaffffaaaa, 0xffffffff00000000], [(3, [(3, 0xffffaaaaffffaaaa, 0xffffffff00000000), (1, 0x555500000000, 0xaaaaaaaaaaaaaaaa)])]),
  ([0xaaffaaffaaaaaaaa, 0xcccccccccccccccc, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(1, [(3, 0xff00ff00ff00ff00, 0xffffffff00000000), (1, 0xff00ff00000000, 0xaaaaaaaaaaaaaaaa)])]),
  ([0xaaffaaffaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffaaaaffffaaaa, 0xffffffff00000000], [(3, [(3, 0xff00ff00ff00ff00, 0xffffffff00000000), (1, 0xff00ff00000000, 0xaaaaaaaaaaaaaaaa)])]),
  ([0xcccccccccccccccc, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffffaaffaa], [(1, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xffffffffaaaaaaaa, 0xff00ff00ff00ff00)])]),
  ([0xcccccccccccccccc, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffffaaaaaaaa, 0xffffffffffff0000], [(8, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xffff0000ffff0000, 0xffffffff00000000)])]),
  ([0xcccccccccccccccc, 0xeeeeeeeeeeeeeeee, 0xff00ff00ff00ff00, 0xffaaffaaffaaffaa, 0xffff0000ffff0000, 0xffffffff00000000, 0xfffffffff0f0f0f0], [(1, [(1, 0xaaaaaaaaaaaaaaaa, 0xff00ff00ff00ff00), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)])]),
  ([0xcccccccccccccccc, 0xeeeeeeeeeeeeeeee, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffaaaaaaaa, 0xfffffffff0f0f0f0], [(1, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (8, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)])]),
  ([0xcccccccccccccccc, 0xeeeeeeeeeeeeeeee, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffffaaaaaaaa, 0xfffffffff0f0f0f0], [(1, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (2, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (4, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (8, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)])]),
  ([0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffeeeeaaaaaaaa, 0xffffffff00000000], [(1, [(0, 0xffffccccffffcccc, 0xffffffff00000000), (1, 0xffffcccc00000000, 0xaaaaaaaaaaaaaaaa)]), (2, [(1, 0xcccccccccccccccc, 0xffff0000ffff0000), (0, 0xffffccccffffcccc, 0xffffffff00000000), (1, 0xffffcccc00000000, 0xaaaaaaaaaaaaaaaa)]), (3, [(0, 0xffffccccffffcccc, 0xffffffff00000000), (1, 0xffffcccc00000000, 0xaaaaaaaaaaaaaaaa)]), (5, [(1, 0xcccccccccccccccc, 0xffff0000ffff0000)])]),
  ([0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffeeeeffffeeee, 0xffffffff00000000, 0xffffffffaaaaaaaa], []),
  ([0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffffaaaaffffaaaa, 0xffffffff00000000, 0xffffffffaaaaaaaa, 0xffffffffffff0000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xffff0000ffff0000, 0xffffffff00000000)]), (3, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (5, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000)])]),
  ([0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffffaaaaffffaaaa, 0xffffffffaaaaaaaa, 0xffffffffffff0000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xffff0000ffff0000, 0xffffffff00000000)]), (3, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (4, [(1, 0xffff0000ffff0000, 0xffffffff00000000)]), (5, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000)]), (19, [])]),
  ([0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffaaaaffffaaaa, 0xffffffff00000000, 0xffffffffaaaaaaaa, 0xfffffffff0f0f0f0], [(3, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (5, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000)])]),
  ([0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffaaaaffffaaaa, 0xffffffffaaaaaaaa, 0xfffffffff0f0f0f0], [(3, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (4, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (5, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000)]), (7, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (19, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)])])
]
def keys_63_6 : Array (List Sig) := lv_63_6.map Prod.fst
set_option maxHeartbeats 0 in
theorem chk_63_6_0 : checkRange true (vars6 63) (graphGoal 63) ps_63 rs_63 keys_63_5 6 lv_63_6 0 16 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem chk_63_6_16 : checkRange true (vars6 63) (graphGoal 63) ps_63 rs_63 keys_63_5 6 lv_63_6 16 16 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem chk_63_6_32 : checkRange true (vars6 63) (graphGoal 63) ps_63 rs_63 keys_63_5 6 lv_63_6 32 16 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem chk_63_6_48 : checkRange true (vars6 63) (graphGoal 63) ps_63 rs_63 keys_63_5 6 lv_63_6 48 16 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem chk_63_6_64 : checkRange true (vars6 63) (graphGoal 63) ps_63 rs_63 keys_63_5 6 lv_63_6 64 16 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem chk_63_6_80 : checkRange true (vars6 63) (graphGoal 63) ps_63 rs_63 keys_63_5 6 lv_63_6 80 16 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem chk_63_6_96 : checkRange true (vars6 63) (graphGoal 63) ps_63 rs_63 keys_63_5 6 lv_63_6 96 16 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem chk_63_6_112 : checkRange true (vars6 63) (graphGoal 63) ps_63 rs_63 keys_63_5 6 lv_63_6 112 16 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem chk_63_6_128 : checkRange true (vars6 63) (graphGoal 63) ps_63 rs_63 keys_63_5 6 lv_63_6 128 16 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem chk_63_6_144 : checkRange true (vars6 63) (graphGoal 63) ps_63 rs_63 keys_63_5 6 lv_63_6 144 16 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem chk_63_6_160 : checkRange true (vars6 63) (graphGoal 63) ps_63 rs_63 keys_63_5 6 lv_63_6 160 16 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem chk_63_6_176 : checkRange true (vars6 63) (graphGoal 63) ps_63 rs_63 keys_63_5 6 lv_63_6 176 16 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem chk_63_6_192 : checkRange true (vars6 63) (graphGoal 63) ps_63 rs_63 keys_63_5 6 lv_63_6 192 16 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem chk_63_6_208 : checkRange true (vars6 63) (graphGoal 63) ps_63 rs_63 keys_63_5 6 lv_63_6 208 16 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem chk_63_6_224 : checkRange true (vars6 63) (graphGoal 63) ps_63 rs_63 keys_63_5 6 lv_63_6 224 16 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem chk_63_6_240 : checkRange true (vars6 63) (graphGoal 63) ps_63 rs_63 keys_63_5 6 lv_63_6 240 10 = true := by decide +kernel
theorem lv_63_6_ok : ∀ i < keys_63_6.size, ∀ v, keys_63_6[i]? = some v → Impossible (graphGoal 63) 6 v.toFinset := by
  apply level_of_nodes
  intro i hi nd hnd
  have hsz : lv_63_6.size = 250 := by decide +kernel
  by_cases h0 : i < 16
  · exact checkRange_sound (fun _ => rfl) ps_63_ok (by decide) rs_63_ok (fun _ => lv_63_5_ok) chk_63_6_0 i (by omega) h0 nd hnd
  by_cases h1 : i < 32
  · exact checkRange_sound (fun _ => rfl) ps_63_ok (by decide) rs_63_ok (fun _ => lv_63_5_ok) chk_63_6_16 i (by omega) h1 nd hnd
  by_cases h2 : i < 48
  · exact checkRange_sound (fun _ => rfl) ps_63_ok (by decide) rs_63_ok (fun _ => lv_63_5_ok) chk_63_6_32 i (by omega) h2 nd hnd
  by_cases h3 : i < 64
  · exact checkRange_sound (fun _ => rfl) ps_63_ok (by decide) rs_63_ok (fun _ => lv_63_5_ok) chk_63_6_48 i (by omega) h3 nd hnd
  by_cases h4 : i < 80
  · exact checkRange_sound (fun _ => rfl) ps_63_ok (by decide) rs_63_ok (fun _ => lv_63_5_ok) chk_63_6_64 i (by omega) h4 nd hnd
  by_cases h5 : i < 96
  · exact checkRange_sound (fun _ => rfl) ps_63_ok (by decide) rs_63_ok (fun _ => lv_63_5_ok) chk_63_6_80 i (by omega) h5 nd hnd
  by_cases h6 : i < 112
  · exact checkRange_sound (fun _ => rfl) ps_63_ok (by decide) rs_63_ok (fun _ => lv_63_5_ok) chk_63_6_96 i (by omega) h6 nd hnd
  by_cases h7 : i < 128
  · exact checkRange_sound (fun _ => rfl) ps_63_ok (by decide) rs_63_ok (fun _ => lv_63_5_ok) chk_63_6_112 i (by omega) h7 nd hnd
  by_cases h8 : i < 144
  · exact checkRange_sound (fun _ => rfl) ps_63_ok (by decide) rs_63_ok (fun _ => lv_63_5_ok) chk_63_6_128 i (by omega) h8 nd hnd
  by_cases h9 : i < 160
  · exact checkRange_sound (fun _ => rfl) ps_63_ok (by decide) rs_63_ok (fun _ => lv_63_5_ok) chk_63_6_144 i (by omega) h9 nd hnd
  by_cases h10 : i < 176
  · exact checkRange_sound (fun _ => rfl) ps_63_ok (by decide) rs_63_ok (fun _ => lv_63_5_ok) chk_63_6_160 i (by omega) h10 nd hnd
  by_cases h11 : i < 192
  · exact checkRange_sound (fun _ => rfl) ps_63_ok (by decide) rs_63_ok (fun _ => lv_63_5_ok) chk_63_6_176 i (by omega) h11 nd hnd
  by_cases h12 : i < 208
  · exact checkRange_sound (fun _ => rfl) ps_63_ok (by decide) rs_63_ok (fun _ => lv_63_5_ok) chk_63_6_192 i (by omega) h12 nd hnd
  by_cases h13 : i < 224
  · exact checkRange_sound (fun _ => rfl) ps_63_ok (by decide) rs_63_ok (fun _ => lv_63_5_ok) chk_63_6_208 i (by omega) h13 nd hnd
  by_cases h14 : i < 240
  · exact checkRange_sound (fun _ => rfl) ps_63_ok (by decide) rs_63_ok (fun _ => lv_63_5_ok) chk_63_6_224 i (by omega) h14 nd hnd
  exact checkRange_sound (fun _ => rfl) ps_63_ok (by decide) rs_63_ok (fun _ => lv_63_5_ok) chk_63_6_240 i (by omega) (by omega) nd hnd

def lv_63_7 : Array NodeData := #[
  ([0xeeeeeeee, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (2, 0xeeeeeeeeeeeeeeee, 0xffffffff00000000)]), (1, [(2, 0xeeeeeeeeeeeeeeee, 0xffffffff00000000)]), (2, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (2, 0xeeeeeeeeeeeeeeee, 0xffffffff00000000)]), (3, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (2, 0xeeeeeeeeeeeeeeee, 0xffffffff00000000)]), (4, [(2, 0xeeeeeeeeeeeeeeee, 0xffffffff00000000)]), (8, []), (21, [])]),
  ([0xffffaaaa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (2, 0xffffaaaaffffaaaa, 0xffffffff00000000)]), (1, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (2, 0xffffaaaaffffaaaa, 0xffffffff00000000)]), (2, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (2, 0xffffaaaaffffaaaa, 0xffffffff00000000)]), (3, [(2, 0xffffaaaaffffaaaa, 0xffffffff00000000)]), (4, [(2, 0xffffaaaaffffaaaa, 0xffffffff00000000)]), (19, [])]),
  ([0xffffcccc, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(1, 0xcccccccccccccccc, 0xffff0000ffff0000), (2, 0xffffccccffffcccc, 0xffffffff00000000)]), (1, [(2, 0xffffccccffffcccc, 0xffffffff00000000)]), (2, [(1, 0xcccccccccccccccc, 0xffff0000ffff0000), (2, 0xffffccccffffcccc, 0xffffffff00000000)]), (4, [(1, 0xcccccccccccccccc, 0xffff0000ffff0000), (2, 0xffffccccffffcccc, 0xffffffff00000000)]), (8, []), (14, [])]),
  ([0x555500000000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffaaaaffffaaaa, 0xffffffff00000000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (3, 0xffffaaaaffffaaaa, 0xffffffff00000000)]), (3, [(3, 0xffffaaaaffffaaaa, 0xffffffff00000000)]), (19, [])]),
  ([0x555500000000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (3, 0xffffaaaaffffaaaa, 0xffffffff00000000)]), (1, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (3, 0xffffaaaaffffaaaa, 0xffffffff00000000)]), (2, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (3, 0xffffaaaaffffaaaa, 0xffffffff00000000)]), (3, [(3, 0xffffaaaaffffaaaa, 0xffffffff00000000)]), (4, [(3, 0xffffaaaaffffaaaa, 0xffffffff00000000)]), (5, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000)])]),
  ([0xeeee0000eeee, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (2, 0xeeeeeeeeeeeeeeee, 0xffff0000ffff0000)]), (1, [(2, 0xeeeeeeeeeeeeeeee, 0xffff0000ffff0000)]), (2, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (2, 0xeeeeeeeeeeeeeeee, 0xffff0000ffff0000)]), (3, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc)]), (8, []), (21, [])]),
  ([0xffff00000000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (3, 0xffff0000ffff0000, 0xffffffff00000000)]), (1, [(3, 0xffff0000ffff0000, 0xffffffff00000000)]), (4, [(3, 0xffff0000ffff0000, 0xffffffff00000000)]), (5, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc)]), (8, [(3, 0xffff0000ffff0000, 0xffffffff00000000)])]),
  ([0xffff00000000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffccffccffccffcc, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(1, 0xcccccccccccccccc, 0xff00ff00ff00ff00), (3, 0xffff0000ffff0000, 0xffffffff00000000)]), (1, [(3, 0xffff0000ffff0000, 0xffffffff00000000)]), (2, [(3, 0xffff0000ffff0000, 0xffffffff00000000)]), (5, [(1, 0xcccccccccccccccc, 0xff00ff00ff00ff00)]), (6, [(3, 0xffff0000ffff0000, 0xffffffff00000000)]), (8, [(3, 0xffff0000ffff0000, 0xffffffff00000000)]), (13, [(3, 0xffff0000ffff0000, 0xffffffff00000000)])]),
  ([0xffff00000000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffffaaaaaaaa], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (3, 0xffff0000ffff0000, 0xffffffff00000000)]), (3, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (4, [(3, 0xffff0000ffff0000, 0xffffffff00000000)]), (5, []), (19, [])]),
  ([0xffff00000000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xfffffffff0f0f0f0], [(1, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (3, 0xffff0000ffff0000, 0xffffffff00000000)]), (2, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (3, 0xffff0000ffff0000, 0xffffffff00000000)]), (3, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (4, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (3, 0xffff0000ffff0000, 0xffffffff00000000)]), (5, []), (7, [(3, 0xffff0000ffff0000, 0xffffffff00000000)]), (11, [])]),
  ([0xffff0000aaaa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (2, 0xffffffffaaaaaaaa, 0xffff0000ffff0000)]), (1, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (2, 0xffffffffaaaaaaaa, 0xffff0000ffff0000)]), (2, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (2, 0xffffffffaaaaaaaa, 0xffff0000ffff0000)]), (3, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (4, [(2, 0xffffffffaaaaaaaa, 0xffff0000ffff0000)])]),
  ([0xffff0000aaaa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffaaaaaaaa], [(3, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (4, [(2, 0xffffffffaaaaaaaa, 0xffff0000ffff0000)]), (5, [(2, 0xffffffffaaaaaaaa, 0xffff0000ffff0000)])]),
  ([0xffff0000cccc, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(1, 0xcccccccccccccccc, 0xffffffff00000000), (2, 0xffffffffcccccccc, 0xffff0000ffff0000)]), (1, [(2, 0xffffffffcccccccc, 0xffff0000ffff0000)]), (2, [(1, 0xcccccccccccccccc, 0xffffffff00000000), (2, 0xffffffffcccccccc, 0xffff0000ffff0000)]), (3, [(1, 0xcccccccccccccccc, 0xffffffff00000000)]), (4, [(1, 0xcccccccccccccccc, 0xffffffff00000000), (2, 0xffffffffcccccccc, 0xffff0000ffff0000)]), (8, []), (15, [])]),
  ([0xffff0000f0f0, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xfffffffff0f0f0f0], [(0, [(2, 0xfffffffff0f0f0f0, 0xffff0000ffff0000)]), (1, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (2, 0xfffffffff0f0f0f0, 0xffff0000ffff0000)]), (2, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (2, 0xfffffffff0f0f0f0, 0xffff0000ffff0000)]), (3, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (4, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (2, 0xfffffffff0f0f0f0, 0xffff0000ffff0000)]), (7, [])]),
  ([0xee00ee00ee00ee, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (2, 0xeeeeeeeeeeeeeeee, 0xff00ff00ff00ff00)]), (1, [(2, 0xeeeeeeeeeeeeeeee, 0xff00ff00ff00ff00)]), (2, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc)]), (3, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (2, 0xeeeeeeeeeeeeeeee, 0xff00ff00ff00ff00)]), (4, [(2, 0xeeeeeeeeeeeeeeee, 0xff00ff00ff00ff00)]), (6, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc)]), (8, [])]),
  ([0xff00aa00ff00aa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (2, 0xffffaaaaffffaaaa, 0xff00ff00ff00ff00)]), (1, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (2, 0xffffaaaaffffaaaa, 0xff00ff00ff00ff00)]), (2, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000)]), (3, [(2, 0xffffaaaaffffaaaa, 0xff00ff00ff00ff00)]), (4, [(2, 0xffffaaaaffffaaaa, 0xff00ff00ff00ff00)]), (6, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000)])]),
  ([0xff00cc00ff00cc, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(1, 0xcccccccccccccccc, 0xffff0000ffff0000), (2, 0xffffccccffffcccc, 0xff00ff00ff00ff00)]), (1, [(2, 0xffffccccffffcccc, 0xff00ff00ff00ff00)]), (2, [(1, 0xcccccccccccccccc, 0xffff0000ffff0000)]), (3, [(2, 0xffffccccffffcccc, 0xff00ff00ff00ff00)]), (4, [(1, 0xcccccccccccccccc, 0xffff0000ffff0000), (2, 0xffffccccffffcccc, 0xff00ff00ff00ff00)]), (6, [(1, 0xcccccccccccccccc, 0xffff0000ffff0000)]), (8, [])]),
  ([0xff00ff00000000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (3, 0xff00ff00ff00ff00, 0xffffffff00000000)]), (1, [(3, 0xff00ff00ff00ff00, 0xffffffff00000000)]), (2, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc)]), (4, [(3, 0xff00ff00ff00ff00, 0xffffffff00000000)]), (5, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc)]), (6, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc)]), (8, [(3, 0xff00ff00ff00ff00, 0xffffffff00000000)])]),
  ([0xff00ff00000000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffaaaaffffaaaa, 0xffffffff00000000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (3, 0xff00ff00ff00ff00, 0xffffffff00000000)]), (3, [(3, 0xff00ff00ff00ff00, 0xffffffff00000000)]), (4, [(3, 0xff00ff00ff00ff00, 0xffffffff00000000)]), (5, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000)])]),
  ([0xff00ff00000000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffccccffffcccc, 0xffffffff00000000], [(0, [(1, 0xcccccccccccccccc, 0xffff0000ffff0000), (3, 0xff00ff00ff00ff00, 0xffffffff00000000)]), (1, [(3, 0xff00ff00ff00ff00, 0xffffffff00000000)]), (2, [(1, 0xcccccccccccccccc, 0xffff0000ffff0000)]), (3, [(3, 0xff00ff00ff00ff00, 0xffffffff00000000)]), (5, [(1, 0xcccccccccccccccc, 0xffff0000ffff0000)]), (6, [(1, 0xcccccccccccccccc, 0xffff0000ffff0000)]), (8, [(3, 0xff00ff00ff00ff00, 0xffffffff00000000)])]),
  ([0xff00ff00000000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffffcccccccc], [(1, [(3, 0xff00ff00ff00ff00, 0xffffffff00000000)]), (2, [(1, 0xcccccccccccccccc, 0xffffffff00000000)]), (5, []), (8, [(3, 0xff00ff00ff00ff00, 0xffffffff00000000)])]),
  ([0xff00ff00aa00aa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (2, 0xffffffffaaaaaaaa, 0xff00ff00ff00ff00)]), (1, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (2, 0xffffffffaaaaaaaa, 0xff00ff00ff00ff00)]), (2, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (3, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (2, 0xffffffffaaaaaaaa, 0xff00ff00ff00ff00)]), (4, [(2, 0xffffffffaaaaaaaa, 0xff00ff00ff00ff00)]), (6, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)])]),
  ([0xff00ff00aa00aa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffaaaaaaaa], [(2, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (5, [(2, 0xffffffffaaaaaaaa, 0xff00ff00ff00ff00)]), (6, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)])]),
  ([0xff00ff00cc00cc, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(1, 0xcccccccccccccccc, 0xffffffff00000000), (2, 0xffffffffcccccccc, 0xff00ff00ff00ff00)]), (1, [(2, 0xffffffffcccccccc, 0xff00ff00ff00ff00)]), (2, [(1, 0xcccccccccccccccc, 0xffffffff00000000)]), (3, [(1, 0xcccccccccccccccc, 0xffffffff00000000), (2, 0xffffffffcccccccc, 0xff00ff00ff00ff00)]), (4, [(1, 0xcccccccccccccccc, 0xffffffff00000000), (2, 0xffffffffcccccccc, 0xff00ff00ff00ff00)]), (6, [(1, 0xcccccccccccccccc, 0xffffffff00000000)]), (15, [])]),
  ([0xff00ff00cc00cc, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(1, 0xcccccccccccccccc, 0xffffffff00000000), (2, 0xffffffffcccccccc, 0xff00ff00ff00ff00)]), (3, [(1, 0xcccccccccccccccc, 0xffffffff00000000), (2, 0xffffffffcccccccc, 0xff00ff00ff00ff00)]), (4, [(1, 0xcccccccccccccccc, 0xffffffff00000000), (2, 0xffffffffcccccccc, 0xff00ff00ff00ff00)]), (15, [])]),
  ([0xff00ff00f000f0, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xfffffffff0f0f0f0], [(0, [(2, 0xfffffffff0f0f0f0, 0xff00ff00ff00ff00)]), (1, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (2, 0xfffffffff0f0f0f0, 0xff00ff00ff00ff00)]), (2, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (3, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (2, 0xfffffffff0f0f0f0, 0xff00ff00ff00ff00)]), (4, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (2, 0xfffffffff0f0f0f0, 0xff00ff00ff00ff00)]), (6, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (7, [])]),
  ([0xff00ff00ff0000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(1, 0xffff0000ffff0000, 0xffffffff00000000), (2, 0xffffffffffff0000, 0xff00ff00ff00ff00)]), (1, [(1, 0xffff0000ffff0000, 0xffffffff00000000), (2, 0xffffffffffff0000, 0xff00ff00ff00ff00)]), (2, [(1, 0xffff0000ffff0000, 0xffffffff00000000)]), (3, [(2, 0xffffffffffff0000, 0xff00ff00ff00ff00)]), (4, [(1, 0xffff0000ffff0000, 0xffffffff00000000), (2, 0xffffffffffff0000, 0xff00ff00ff00ff00)]), (6, [(1, 0xffff0000ffff0000, 0xffffffff00000000)])]),
  ([0xff00ff00ff0000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffffff0000], [(2, [(1, 0xffff0000ffff0000, 0xffffffff00000000)]), (5, [(2, 0xffffffffffff0000, 0xff00ff00ff00ff00)]), (6, [(1, 0xffff0000ffff0000, 0xffffffff00000000)])]),
  ([0xf0f0a0a0f0f0a0a, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000)]), (1, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (2, 0xffffaaaaffffaaaa, 0xf0f0f0f0f0f0f0f0)]), (2, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (2, 0xffffaaaaffffaaaa, 0xf0f0f0f0f0f0f0f0)]), (3, [(2, 0xffffaaaaffffaaaa, 0xf0f0f0f0f0f0f0f0)]), (19, [])]),
  ([0x5555444455554444, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(1, 0xcccccccccccccccc, 0xffff0000ffff0000), (2, 0xffffccccffffcccc, 0xaaaaaaaaaaaaaaaa)]), (2, [(1, 0xcccccccccccccccc, 0xffff0000ffff0000), (2, 0xffffccccffffcccc, 0xaaaaaaaaaaaaaaaa)]), (4, [(1, 0xcccccccccccccccc, 0xffff0000ffff0000)]), (8, []), (14, [])]),
  ([0x5555555500000000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffccffccffccffcc, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(3, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xcccccccccccccccc, 0xff00ff00ff00ff00)]), (1, [(3, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (2, [(3, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (5, [(1, 0xcccccccccccccccc, 0xff00ff00ff00ff00)]), (6, [(3, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (8, [(3, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (13, [(3, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)])]),
  ([0x5555555500000000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffccccffffcccc, 0xffffffff00000000], [(0, [(3, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xcccccccccccccccc, 0xffff0000ffff0000)]), (1, [(3, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (3, [(3, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (5, [(1, 0xcccccccccccccccc, 0xffff0000ffff0000)]), (8, [(3, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)])]),
  ([0x5555555500000000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffffffff0000], [(0, [(3, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xffff0000ffff0000, 0xffffffff00000000)]), (3, [(3, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (4, [(1, 0xffff0000ffff0000, 0xffffffff00000000)]), (5, []), (19, [])]),
  ([0x5555555500000000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xfffffffff0f0f0f0], [(1, [(3, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (2, [(3, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (3, [(3, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (4, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (5, []), (7, [(3, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (10, [])]),
  ([0x5555555544444444, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(1, 0xcccccccccccccccc, 0xffffffff00000000), (2, 0xffffffffcccccccc, 0xaaaaaaaaaaaaaaaa)]), (2, [(1, 0xcccccccccccccccc, 0xffffffff00000000), (2, 0xffffffffcccccccc, 0xaaaaaaaaaaaaaaaa)]), (3, [(1, 0xcccccccccccccccc, 0xffffffff00000000), (2, 0xffffffffcccccccc, 0xaaaaaaaaaaaaaaaa)]), (4, [(1, 0xcccccccccccccccc, 0xffffffff00000000)]), (8, []), (15, [])]),
  ([0x5555555550505050, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xfffffffff0f0f0f0], [(0, [(2, 0xfffffffff0f0f0f0, 0xaaaaaaaaaaaaaaaa)]), (1, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (2, 0xfffffffff0f0f0f0, 0xaaaaaaaaaaaaaaaa)]), (2, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (2, 0xfffffffff0f0f0f0, 0xaaaaaaaaaaaaaaaa)]), (3, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (2, 0xfffffffff0f0f0f0, 0xaaaaaaaaaaaaaaaa)]), (4, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (7, [])]),
  ([0x5555555555550000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(1, 0xffff0000ffff0000, 0xffffffff00000000), (2, 0xffffffffffff0000, 0xaaaaaaaaaaaaaaaa)]), (1, [(1, 0xffff0000ffff0000, 0xffffffff00000000), (2, 0xffffffffffff0000, 0xaaaaaaaaaaaaaaaa)]), (2, [(1, 0xffff0000ffff0000, 0xffffffff00000000), (2, 0xffffffffffff0000, 0xaaaaaaaaaaaaaaaa)]), (3, [(2, 0xffffffffffff0000, 0xaaaaaaaaaaaaaaaa)]), (4, [(1, 0xffff0000ffff0000, 0xffffffff00000000)])]),
  ([0x5555555555550000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffffff0000], [(3, [(2, 0xffffffffffff0000, 0xaaaaaaaaaaaaaaaa)]), (4, [(1, 0xffff0000ffff0000, 0xffffffff00000000)]), (5, [(2, 0xffffffffffff0000, 0xaaaaaaaaaaaaaaaa)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xaaaaffffaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(3, 0xffff0000ffff0000, 0xffffffff00000000), (1, 0xffff00000000, 0xaaaaaaaaaaaaaaaa)]), (1, [(3, 0xffff0000ffff0000, 0xffffffff00000000), (1, 0xffff00000000, 0xaaaaaaaaaaaaaaaa)]), (2, [(3, 0xffff0000ffff0000, 0xffffffff00000000), (1, 0xffff00000000, 0xaaaaaaaaaaaaaaaa)]), (4, [(3, 0xffff0000ffff0000, 0xffffffff00000000)]), (5, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xaaffaaffaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(3, 0xff00ff00ff00ff00, 0xffffffff00000000), (1, 0xff00ff00000000, 0xaaaaaaaaaaaaaaaa)]), (1, [(3, 0xff00ff00ff00ff00, 0xffffffff00000000), (1, 0xff00ff00000000, 0xaaaaaaaaaaaaaaaa)]), (2, [(1, 0xff00ff00000000, 0xaaaaaaaaaaaaaaaa)]), (3, [(3, 0xff00ff00ff00ff00, 0xffffffff00000000), (1, 0xff00ff00000000, 0xaaaaaaaaaaaaaaaa)]), (4, [(3, 0xff00ff00ff00ff00, 0xffffffff00000000)]), (5, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccc00cc00, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(1, 0xff00ff00ff00ff00, 0xffffffff00000000), (0, 0xffffffffff00ff00, 0xcccccccccccccccc)]), (1, [(1, 0xff00ff00ff00ff00, 0xffffffff00000000)]), (2, [(0, 0xffffffffff00ff00, 0xcccccccccccccccc)]), (3, [(1, 0xff00ff00ff00ff00, 0xffffffff00000000), (0, 0xffffffffff00ff00, 0xcccccccccccccccc)]), (4, [(1, 0xff00ff00ff00ff00, 0xffffffff00000000), (0, 0xffffffffff00ff00, 0xcccccccccccccccc)]), (6, []), (17, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xccccffffcccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(1, [(3, 0xffff0000ffff0000, 0xffffffff00000000)]), (4, [(3, 0xffff0000ffff0000, 0xffffffff00000000), (1, 0xffff00000000, 0xcccccccccccccccc)]), (8, [(3, 0xffff0000ffff0000, 0xffffffff00000000)]), (15, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xccffccffcccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(1, [(3, 0xff00ff00ff00ff00, 0xffffffff00000000)]), (4, [(3, 0xff00ff00ff00ff00, 0xffffffff00000000), (1, 0xff00ff00000000, 0xcccccccccccccccc)]), (8, [(3, 0xff00ff00ff00ff00, 0xffffffff00000000)]), (15, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xddddddddcccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(3, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0x5555555500000000, 0xcccccccccccccccc)]), (1, [(3, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (4, [(1, 0x5555555500000000, 0xcccccccccccccccc)]), (5, []), (8, [(3, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (15, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xeeeeeeee00000000, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (0, 0xeeeeeeeeeeeeeeee, 0xffffffff00000000)]), (1, [(0, 0xeeeeeeeeeeeeeeee, 0xffffffff00000000)]), (2, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (0, 0xeeeeeeeeeeeeeeee, 0xffffffff00000000)]), (3, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (0, 0xeeeeeeeeeeeeeeee, 0xffffffff00000000)]), (4, [(0, 0xeeeeeeeeeeeeeeee, 0xffffffff00000000)]), (5, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffff00ffffff00, 0xffffffff00000000], [(1, [(1, 0xff00ff00ff00ff00, 0xffff0000ffff0000)]), (2, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc)]), (6, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc)]), (8, [(1, 0xff00ff00ff00ff00, 0xffff0000ffff0000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffff00ff00], [(1, [(1, 0xff00ff00ff00ff00, 0xffffffff00000000)]), (2, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc)]), (6, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc)]), (8, [(1, 0xff00ff00ff00ff00, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffffff0000], [(1, [(1, 0xffff0000ffff0000, 0xffffffff00000000)]), (8, [(1, 0xffff0000ffff0000, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xeeeeeeeeeeeeeeee, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xfffffffff0f0f0f0], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc)]), (1, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (2, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (3, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (4, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (5, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc)]), (7, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc)]), (8, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffccffccffccffcc, 0xffff0000ffff0000, 0xffffaaaaffffaaaa, 0xffffffff00000000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (1, 0xcccccccccccccccc, 0xff00ff00ff00ff00)]), (1, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000)]), (3, [(1, 0xcccccccccccccccc, 0xff00ff00ff00ff00)]), (6, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000)]), (13, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffccffccffccffcc, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffaaaaaaaa], [(1, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (6, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (13, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffccffccffccffcc, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffffff0000], [(1, [(1, 0xffff0000ffff0000, 0xffffffff00000000)]), (6, [(1, 0xffff0000ffff0000, 0xffffffff00000000)]), (13, [(1, 0xffff0000ffff0000, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffff00ffffff0000, 0xffffffff00000000], [(0, [(3, 0xff00ff00ff00ff00, 0xffffffff00000000), (1, 0xff00ff00000000, 0xffff0000ffff0000)]), (1, [(3, 0xff00ff00ff00ff00, 0xffffffff00000000), (1, 0xff00ff00000000, 0xffff0000ffff0000)]), (2, [(1, 0xff00ff00000000, 0xffff0000ffff0000)]), (3, [(3, 0xff00ff00ff00ff00, 0xffffffff00000000)]), (4, [(3, 0xff00ff00ff00ff00, 0xffffffff00000000), (1, 0xff00ff00000000, 0xffff0000ffff0000)]), (5, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffff5555ffff0000, 0xffffffff00000000], [(0, [(3, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0x5555555500000000, 0xffff0000ffff0000)]), (1, [(3, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0x5555555500000000, 0xffff0000ffff0000)]), (2, [(3, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0x5555555500000000, 0xffff0000ffff0000)]), (3, [(3, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (5, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffaaaa00000000, 0xffffffff00000000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (0, 0xffffaaaaffffaaaa, 0xffffffff00000000)]), (1, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (0, 0xffffaaaaffffaaaa, 0xffffffff00000000)]), (2, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (0, 0xffffaaaaffffaaaa, 0xffffffff00000000)]), (3, [(0, 0xffffaaaaffffaaaa, 0xffffffff00000000)]), (4, [(0, 0xffffaaaaffffaaaa, 0xffffffff00000000)]), (5, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffaaaaffffaaaa, 0xffffeeeeffffeeee, 0xffffffff00000000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (1, 0xffffaaaaffffaaaa, 0xcccccccccccccccc)]), (1, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000)]), (3, [(1, 0xffffaaaaffffaaaa, 0xcccccccccccccccc)]), (8, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000)]), (14, []), (19, []), (21, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffaaaaffffaaaa, 0xffffffff00000000, 0xffffffffcccccccc], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (1, 0xcccccccccccccccc, 0xffffffff00000000)]), (1, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000)]), (3, [(1, 0xcccccccccccccccc, 0xffffffff00000000)]), (8, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffaaaaffffaaaa, 0xffffffff00000000, 0xffffffffffffaaaa], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (1, 0xffffaaaaffffaaaa, 0xffffffff00000000)]), (3, [(1, 0xffffaaaaffffaaaa, 0xffffffff00000000)]), (5, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000)]), (19, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffcccc00000000, 0xffffffff00000000], [(0, [(1, 0xcccccccccccccccc, 0xffff0000ffff0000), (0, 0xffffccccffffcccc, 0xffffffff00000000)]), (1, [(0, 0xffffccccffffcccc, 0xffffffff00000000)]), (2, [(1, 0xcccccccccccccccc, 0xffff0000ffff0000), (0, 0xffffccccffffcccc, 0xffffffff00000000)]), (3, [(0, 0xffffccccffffcccc, 0xffffffff00000000)]), (4, [(1, 0xcccccccccccccccc, 0xffff0000ffff0000), (0, 0xffffccccffffcccc, 0xffffffff00000000)]), (5, [(1, 0xcccccccccccccccc, 0xffff0000ffff0000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffccccffffcccc, 0xffffffff00000000, 0xffffffffaaaaaaaa], [(1, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (8, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffccccffffcccc, 0xffffffff00000000, 0xffffffffff00ff00], [(1, [(1, 0xff00ff00ff00ff00, 0xffffffff00000000)]), (2, [(1, 0xcccccccccccccccc, 0xffff0000ffff0000)]), (6, [(1, 0xcccccccccccccccc, 0xffff0000ffff0000)]), (8, [(1, 0xff00ff00ff00ff00, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffeeeeffffeeee, 0xffffffff00000000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (1, 0xffffaaaaffffaaaa, 0xcccccccccccccccc)]), (1, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000)]), (2, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (1, 0xffffaaaaffffaaaa, 0xcccccccccccccccc)]), (3, [(1, 0xffffaaaaffffaaaa, 0xcccccccccccccccc)]), (4, [(1, 0xffffaaaaffffaaaa, 0xcccccccccccccccc)]), (8, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffaaaaaaaa, 0xffffffffcccccccc], [(4, [(1, 0xcccccccccccccccc, 0xffffffff00000000)]), (8, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (15, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffaaaaaaaa, 0xffffffffeeeeeeee], [(1, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (8, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (15, []), (21, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffaaaaaaaa, 0xffffffffffff0000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xffff0000ffff0000, 0xffffffff00000000)]), (3, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (4, [(1, 0xffff0000ffff0000, 0xffffffff00000000)]), (5, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffaaaaaaaa, 0xffffffffffffaaaa], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xffffffffaaaaaaaa, 0xffff0000ffff0000)]), (3, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (19, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffcccccccc, 0xffffffffff00ff00], [(0, [(1, 0xcccccccccccccccc, 0xffffffff00000000), (1, 0xff00ff00ff00ff00, 0xffffffff00000000)]), (1, [(1, 0xff00ff00ff00ff00, 0xffffffff00000000)]), (2, [(1, 0xcccccccccccccccc, 0xffffffff00000000)]), (5, []), (6, [(1, 0xcccccccccccccccc, 0xffffffff00000000)]), (8, [(1, 0xff00ff00ff00ff00, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffcccccccc, 0xffffffffffff0000], [(1, [(1, 0xffff0000ffff0000, 0xffffffff00000000)]), (8, [(1, 0xffff0000ffff0000, 0xffffffff00000000)]), (15, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffeeeeeeee], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xffffffffaaaaaaaa, 0xcccccccccccccccc)]), (1, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (2, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xffffffffaaaaaaaa, 0xcccccccccccccccc)]), (3, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xffffffffaaaaaaaa, 0xcccccccccccccccc)]), (4, [(1, 0xffffffffaaaaaaaa, 0xcccccccccccccccc)]), (8, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (21, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffffff0000, 0xffffffffffffaaaa], [(0, [(1, 0xffff0000ffff0000, 0xffffffff00000000), (1, 0xffffffffffff0000, 0xaaaaaaaaaaaaaaaa)]), (4, [(1, 0xffff0000ffff0000, 0xffffffff00000000)]), (19, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffffff0000, 0xffffffffffffcccc], [(1, [(1, 0xffff0000ffff0000, 0xffffffff00000000)]), (8, [(1, 0xffff0000ffff0000, 0xffffffff00000000)]), (14, []), (15, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffffffaaaa], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (1, 0xffffaaaaffffaaaa, 0xffffffff00000000)]), (1, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (1, 0xffffaaaaffffaaaa, 0xffffffff00000000)]), (2, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (1, 0xffffaaaaffffaaaa, 0xffffffff00000000)]), (3, [(1, 0xffffaaaaffffaaaa, 0xffffffff00000000)]), (4, [(1, 0xffffaaaaffffaaaa, 0xffffffff00000000)]), (19, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffffffcccc], [(0, [(1, 0xffff0000ffff0000, 0xffffffff00000000), (1, 0xffffffffffff0000, 0xcccccccccccccccc)]), (1, [(1, 0xffff0000ffff0000, 0xffffffff00000000)]), (2, [(1, 0xffff0000ffff0000, 0xffffffff00000000), (1, 0xffffffffffff0000, 0xcccccccccccccccc)]), (3, [(1, 0xffffffffffff0000, 0xcccccccccccccccc)]), (4, [(1, 0xffff0000ffff0000, 0xffffffff00000000), (1, 0xffffffffffff0000, 0xcccccccccccccccc)]), (8, [(1, 0xffff0000ffff0000, 0xffffffff00000000)]), (14, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffffaaaaaaaa, 0xffffffffffff0000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xffff0000ffff0000, 0xffffffff00000000)]), (3, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (4, [(1, 0xffff0000ffff0000, 0xffffffff00000000)]), (5, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffffcccccccc, 0xffffffffff00ff00], [(1, [(1, 0xff00ff00ff00ff00, 0xffffffff00000000)]), (2, [(1, 0xcccccccccccccccc, 0xffffffff00000000)]), (6, [(1, 0xcccccccccccccccc, 0xffffffff00000000)]), (8, [(1, 0xff00ff00ff00ff00, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffffaaaaffffaaaa, 0xffffffff00000000, 0xffffffffffff0000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (1, 0xffff0000ffff0000, 0xffffffff00000000)]), (3, []), (4, [(1, 0xffff0000ffff0000, 0xffffffff00000000)]), (5, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000)]), (19, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffffccccffffcccc, 0xffffff00ffffff00, 0xffffffff00000000], [(0, [(1, 0xcccccccccccccccc, 0xffff0000ffff0000), (1, 0xff00ff00ff00ff00, 0xffff0000ffff0000)]), (1, [(1, 0xff00ff00ff00ff00, 0xffff0000ffff0000)]), (2, [(1, 0xcccccccccccccccc, 0xffff0000ffff0000)]), (6, [(1, 0xcccccccccccccccc, 0xffff0000ffff0000)]), (8, [(1, 0xff00ff00ff00ff00, 0xffff0000ffff0000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffffccccffffcccc, 0xffffffff00000000, 0xffffffffffff0000], [(0, [(1, 0xcccccccccccccccc, 0xffff0000ffff0000), (1, 0xffff0000ffff0000, 0xffffffff00000000)]), (1, [(1, 0xffff0000ffff0000, 0xffffffff00000000)]), (3, []), (5, [(1, 0xcccccccccccccccc, 0xffff0000ffff0000)]), (8, [(1, 0xffff0000ffff0000, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0fffff0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(1, [(3, 0xffff0000ffff0000, 0xffffffff00000000), (1, 0xffff00000000, 0xf0f0f0f0f0f0f0f0)]), (2, [(3, 0xffff0000ffff0000, 0xffffffff00000000), (1, 0xffff00000000, 0xf0f0f0f0f0f0f0f0)]), (3, [(1, 0xffff00000000, 0xf0f0f0f0f0f0f0f0)]), (4, [(3, 0xffff0000ffff0000, 0xffffffff00000000), (1, 0xffff00000000, 0xf0f0f0f0f0f0f0f0)]), (5, []), (7, [(3, 0xffff0000ffff0000, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0fff0fff0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(1, [(3, 0xff00ff00ff00ff00, 0xffffffff00000000), (1, 0xff00ff00000000, 0xf0f0f0f0f0f0f0f0)]), (2, [(1, 0xff00ff00000000, 0xf0f0f0f0f0f0f0f0)]), (3, [(3, 0xff00ff00ff00ff00, 0xffffffff00000000), (1, 0xff00ff00000000, 0xf0f0f0f0f0f0f0f0)]), (4, [(3, 0xff00ff00ff00ff00, 0xffffffff00000000), (1, 0xff00ff00000000, 0xf0f0f0f0f0f0f0f0)]), (5, []), (7, [(3, 0xff00ff00ff00ff00, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf5f5f5f5f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(1, [(3, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0x5555555500000000, 0xf0f0f0f0f0f0f0f0)]), (2, [(3, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0x5555555500000000, 0xf0f0f0f0f0f0f0f0)]), (3, [(3, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0x5555555500000000, 0xf0f0f0f0f0f0f0f0)]), (4, [(1, 0x5555555500000000, 0xf0f0f0f0f0f0f0f0)]), (5, []), (7, [(3, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffccffccffccffcc, 0xffff0000ffff0000, 0xffffffff00000000, 0xfffffffff0f0f0f0], [(0, [(1, 0xcccccccccccccccc, 0xff00ff00ff00ff00)]), (1, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (4, [(1, 0xcccccccccccccccc, 0xff00ff00ff00ff00), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (6, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (8, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (13, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffaaaaffffaaaa, 0xffffffff00000000, 0xfffffffff0f0f0f0], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000)]), (1, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (2, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (3, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (4, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (5, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000)]), (7, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000)]), (19, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffccccffffcccc, 0xffffffff00000000, 0xfffffffff0f0f0f0], [(0, [(1, 0xcccccccccccccccc, 0xffff0000ffff0000)]), (1, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (2, [(1, 0xcccccccccccccccc, 0xffff0000ffff0000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (3, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (4, [(1, 0xcccccccccccccccc, 0xffff0000ffff0000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (5, [(1, 0xcccccccccccccccc, 0xffff0000ffff0000)]), (7, [(1, 0xcccccccccccccccc, 0xffff0000ffff0000)]), (8, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffaaaaaaaa, 0xfffffffff0f0f0f0], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (1, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (2, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (3, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (4, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (5, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffcccccccc, 0xfffffffff0f0f0f0], [(0, [(1, 0xcccccccccccccccc, 0xffffffff00000000)]), (1, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (4, [(1, 0xcccccccccccccccc, 0xffffffff00000000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (5, []), (8, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (15, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xfffffffff0f0f0f0, 0xffffffffffff0000], [(0, [(1, 0xffff0000ffff0000, 0xffffffff00000000)]), (1, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (1, 0xffff0000ffff0000, 0xffffffff00000000)]), (2, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (1, 0xffff0000ffff0000, 0xffffffff00000000)]), (3, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (4, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (1, 0xffff0000ffff0000, 0xffffffff00000000)]), (5, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffffaaaaaaaa, 0xfffffffff0f0f0f0], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (1, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (2, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (3, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000), (1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (4, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (5, []), (7, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xfffffffff0f0f0f0, 0xffffffffffff0000], [(0, [(1, 0xffff0000ffff0000, 0xffffffff00000000)]), (1, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (1, 0xffff0000ffff0000, 0xffffffff00000000)]), (2, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (1, 0xffff0000ffff0000, 0xffffffff00000000)]), (3, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (4, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000), (1, 0xffff0000ffff0000, 0xffffffff00000000)]), (5, []), (7, [(1, 0xffff0000ffff0000, 0xffffffff00000000)])]),
  ([0xcccccccccccccccc, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffaaffaaffaaffaa, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (1, 0xaaaaaaaaaaaaaaaa, 0xff00ff00ff00ff00)]), (1, [(1, 0xaaaaaaaaaaaaaaaa, 0xff00ff00ff00ff00)]), (2, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc)]), (4, []), (6, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc)]), (8, [(1, 0xaaaaaaaaaaaaaaaa, 0xff00ff00ff00ff00)])]),
  ([0xcccccccccccccccc, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffaaaaaaaa], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (1, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (2, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (4, []), (5, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc)]), (8, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)])]),
  ([0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffaaaaffffaaaa, 0xffffffff00000000, 0xffffffffaaaaaaaa], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (3, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (4, []), (5, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000)]), (19, [])])
]
def keys_63_7 : Array (List Sig) := lv_63_7.map Prod.fst
set_option maxHeartbeats 0 in
theorem chk_63_7_0 : checkRange true (vars6 63) (graphGoal 63) ps_63 rs_63 keys_63_6 7 lv_63_7 0 16 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem chk_63_7_16 : checkRange true (vars6 63) (graphGoal 63) ps_63 rs_63 keys_63_6 7 lv_63_7 16 16 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem chk_63_7_32 : checkRange true (vars6 63) (graphGoal 63) ps_63 rs_63 keys_63_6 7 lv_63_7 32 16 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem chk_63_7_48 : checkRange true (vars6 63) (graphGoal 63) ps_63 rs_63 keys_63_6 7 lv_63_7 48 16 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem chk_63_7_64 : checkRange true (vars6 63) (graphGoal 63) ps_63 rs_63 keys_63_6 7 lv_63_7 64 16 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem chk_63_7_80 : checkRange true (vars6 63) (graphGoal 63) ps_63 rs_63 keys_63_6 7 lv_63_7 80 12 = true := by decide +kernel
theorem lv_63_7_ok : ∀ i < keys_63_7.size, ∀ v, keys_63_7[i]? = some v → Impossible (graphGoal 63) 7 v.toFinset := by
  apply level_of_nodes
  intro i hi nd hnd
  have hsz : lv_63_7.size = 92 := by decide +kernel
  by_cases h0 : i < 16
  · exact checkRange_sound (fun _ => rfl) ps_63_ok (by decide) rs_63_ok (fun _ => lv_63_6_ok) chk_63_7_0 i (by omega) h0 nd hnd
  by_cases h1 : i < 32
  · exact checkRange_sound (fun _ => rfl) ps_63_ok (by decide) rs_63_ok (fun _ => lv_63_6_ok) chk_63_7_16 i (by omega) h1 nd hnd
  by_cases h2 : i < 48
  · exact checkRange_sound (fun _ => rfl) ps_63_ok (by decide) rs_63_ok (fun _ => lv_63_6_ok) chk_63_7_32 i (by omega) h2 nd hnd
  by_cases h3 : i < 64
  · exact checkRange_sound (fun _ => rfl) ps_63_ok (by decide) rs_63_ok (fun _ => lv_63_6_ok) chk_63_7_48 i (by omega) h3 nd hnd
  by_cases h4 : i < 80
  · exact checkRange_sound (fun _ => rfl) ps_63_ok (by decide) rs_63_ok (fun _ => lv_63_6_ok) chk_63_7_64 i (by omega) h4 nd hnd
  exact checkRange_sound (fun _ => rfl) ps_63_ok (by decide) rs_63_ok (fun _ => lv_63_6_ok) chk_63_7_80 i (by omega) (by omega) nd hnd

def lv_63_8 : Array NodeData := #[
  ([0xffff00000000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(3, 0xffff0000ffff0000, 0xffffffff00000000)]), (1, [(3, 0xffff0000ffff0000, 0xffffffff00000000)]), (2, [(3, 0xffff0000ffff0000, 0xffffffff00000000)]), (3, []), (4, [(3, 0xffff0000ffff0000, 0xffffffff00000000)]), (5, [])]),
  ([0xff00ff00000000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(3, 0xff00ff00ff00ff00, 0xffffffff00000000)]), (1, [(3, 0xff00ff00ff00ff00, 0xffffffff00000000)]), (2, []), (3, [(3, 0xff00ff00ff00ff00, 0xffffffff00000000)]), (4, [(3, 0xff00ff00ff00ff00, 0xffffffff00000000)]), (5, [])]),
  ([0x5555555500000000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(3, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (1, [(3, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (2, [(3, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (3, [(3, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (4, []), (5, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc)]), (1, []), (2, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc)]), (3, [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc)]), (4, []), (8, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffccffccffccffcc, 0xffff0000ffff0000, 0xffffffff00000000], [(0, [(1, 0xcccccccccccccccc, 0xff00ff00ff00ff00)]), (1, []), (2, []), (3, [(1, 0xcccccccccccccccc, 0xff00ff00ff00ff00)]), (4, [(1, 0xcccccccccccccccc, 0xff00ff00ff00ff00)]), (6, []), (8, []), (13, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffaaaaffffaaaa, 0xffffffff00000000], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000)]), (1, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000)]), (2, [(1, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000)]), (3, []), (4, []), (19, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffccccffffcccc, 0xffffffff00000000], [(0, [(1, 0xcccccccccccccccc, 0xffff0000ffff0000)]), (1, []), (2, [(1, 0xcccccccccccccccc, 0xffff0000ffff0000)]), (3, []), (4, [(1, 0xcccccccccccccccc, 0xffff0000ffff0000)]), (8, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffaaaaaaaa], [(0, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (1, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (2, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (3, [(1, 0xaaaaaaaaaaaaaaaa, 0xffffffff00000000)]), (4, []), (5, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffcccccccc], [(0, [(1, 0xcccccccccccccccc, 0xffffffff00000000)]), (1, []), (2, [(1, 0xcccccccccccccccc, 0xffffffff00000000)]), (3, [(1, 0xcccccccccccccccc, 0xffffffff00000000)]), (4, [(1, 0xcccccccccccccccc, 0xffffffff00000000)]), (5, []), (8, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xffffffffffff0000], [(0, [(1, 0xffff0000ffff0000, 0xffffffff00000000)]), (1, [(1, 0xffff0000ffff0000, 0xffffffff00000000)]), (2, [(1, 0xffff0000ffff0000, 0xffffffff00000000)]), (3, []), (4, [(1, 0xffff0000ffff0000, 0xffffffff00000000)]), (5, [])]),
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0xfffffffff0f0f0f0], [(0, []), (1, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (2, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (3, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (4, [(1, 0xf0f0f0f0f0f0f0f0, 0xffffffff00000000)]), (5, []), (7, [])])
]
def keys_63_8 : Array (List Sig) := lv_63_8.map Prod.fst
set_option maxHeartbeats 0 in
theorem chk_63_8_0 : checkRange true (vars6 63) (graphGoal 63) ps_63 rs_63 keys_63_7 8 lv_63_8 0 11 = true := by decide +kernel
theorem lv_63_8_ok : ∀ i < keys_63_8.size, ∀ v, keys_63_8[i]? = some v → Impossible (graphGoal 63) 8 v.toFinset := by
  apply level_of_nodes
  intro i hi nd hnd
  have hsz : lv_63_8.size = 11 := by decide +kernel
  exact checkRange_sound (fun _ => rfl) ps_63_ok (by decide) rs_63_ok (fun _ => lv_63_7_ok) chk_63_8_0 i (by omega) (by omega) nd hnd

def lv_63_9 : Array NodeData := #[
  ([0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000], [(0, []), (1, []), (2, []), (3, []), (4, [])])
]
def keys_63_9 : Array (List Sig) := lv_63_9.map Prod.fst
set_option maxHeartbeats 0 in
theorem chk_63_9_0 : checkRange true (vars6 63) (graphGoal 63) ps_63 rs_63 keys_63_8 9 lv_63_9 0 1 = true := by decide +kernel
theorem lv_63_9_ok : ∀ i < keys_63_9.size, ∀ v, keys_63_9[i]? = some v → Impossible (graphGoal 63) 9 v.toFinset := by
  apply level_of_nodes
  intro i hi nd hnd
  have hsz : lv_63_9.size = 1 := by decide +kernel
  exact checkRange_sound (fun _ => rfl) ps_63_ok (by decide) rs_63_ok (fun _ => lv_63_8_ok) chk_63_9_0 i (by omega) (by omega) nd hnd

theorem imp_63 : Impossible (graphGoal 63) 9 (vars6 63).toFinset := by
  have h := lv_63_9_ok 0 (by decide +kernel) (sortSig (vars6 63)) (by decide +kernel)
  rwa [sortSig_toFinset] at h

theorem low_63 : Lower (vars6 63) (graphGoal 63) 10 := by
  apply lower_impossible (proper_of (by decide +kernel)) (by decide +kernel) (by decide +kernel) _ imp_63
  intro a ha
  have hw : [(0xaaaaaaaaaaaaaaaa, (4 : Row), (5 : Row)), (0xcccccccccccccccc, (8 : Row), (10 : Row)), (0xf0f0f0f0f0f0f0f0, (1 : Row), (5 : Row)), (0xff00ff00ff00ff00, (2 : Row), (10 : Row)), (0xffff0000ffff0000, (1 : Row), (17 : Row)), (0xffffffff00000000, (1 : Row), (33 : Row))].all (fun e => witnessB (graphGoal 63) (vars6 63) e.1 e.2) = true := by decide +kernel
  have hv : vars6 63 = [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000] := by decide +kernel
  rw [hv] at ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 63) (vars6 63) 0xaaaaaaaaaaaaaaaa (4, 5) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 63) (vars6 63) 0xcccccccccccccccc (8, 10) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 63) (vars6 63) 0xf0f0f0f0f0f0f0f0 (1, 5) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 63) (vars6 63) 0xff00ff00ff00ff00 (2, 10) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 63) (vars6 63) 0xffff0000ffff0000 (1, 17) = true)
  · exact witnessB_sound (by decide +kernel : witnessB (graphGoal 63) (vars6 63) 0xffffffff00000000 (1, 33) = true)


-- 7-vertex layer for L_meta_10908
abbrev Sig7 := BitVec 128
abbrev Row7 := Fin 128

def edgeList : List ℕ := [0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6]

def targetFn (x : Fin 7 → Bool) : Bool :=
  decide (∃ i < edgeList.length / 2,
    (List.ofFn x).getD (edgeList.getD (2 * i) 0) false = true ∧
    (List.ofFn x).getD (edgeList.getD (2 * i + 1) 0) false = true)

def mono12 : List Gate :=
  [⟨.or, [0, 1]⟩, ⟨.and, [7, 5]⟩, ⟨.or, [8, 3]⟩, ⟨.or, [9, 6]⟩,
   ⟨.or, [0, 5]⟩, ⟨.and, [11, 10]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [13, 4]⟩,
   ⟨.or, [14, 12]⟩, ⟨.or, [13, 4]⟩, ⟨.and, [16, 6]⟩, ⟨.or, [17, 15]⟩]

theorem mono12_ok : ∀ g ∈ mono12, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono12, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem mono12_len : mono12.length = 12 := rfl

theorem mono12_eval : ∀ x : Fin 7 → Bool, Circuit.eval ⟨mono12, 18⟩ (List.ofFn x) = targetFn x := by
  decide +kernel

def inputs7 : List Sig7 :=
  (List.range 7).map fun j => bvTab fun r : Row7 => r.val.testBit j

def sample7 (r : Row7) (j : Fin 7) : Bool := bvBit r (inputs7.getD j.val bvZero)

def graph7 : Sig7 := bvTab fun r : Row7 => targetFn (sample7 r)

theorem graph7_bit (r : Row7) : bvBit r graph7 = targetFn (sample7 r) :=
  bvBit_tab _ r

theorem inputs7_list : List.ofFn (fun j : Fin 7 => inputs7.getD j.val bvZero) = inputs7 := by
  decide +kernel

theorem sampled7 (r : Row7) : List.ofFn (sample7 r) = inputs7.map (bvBit r) := by
  rw [← inputs7_list, List.map_ofFn]; rfl

theorem table_eval7 (gs : List Gate)
    (legal : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (i : Nat) (r : Row7) :
    bvBit r ((bvExec gs inputs7).getD i bvZero) =
      ((Circuit.mk gs 0).wires (List.ofFn (sample7 r))).getD i false := by
  rw [← bvB_read, bvExec_bits gs r inputs7 legal, sampled7]; rfl

-- Embed 6-vertex row (dropping x1 = false) into 7-vertex row:
-- bit 0 -> bit 0, bit 1 -> false, bits 1..5 -> bits 2..6
def embed6 (r : Row) : Row7 :=
  Fin.ofNat 128 ((r.val &&& 1) ||| ((r.val >>> 1) <<< 2))

theorem embed6_graph7 : restrictRows embed6 (bvObs graph7) = bvObs (graphGoal 63) := by
  funext r
  change bvBit (embed6 r) graph7 = bvBit r (graphGoal 63)
  revert r; decide +kernel

theorem embed6_x1 : restrictRows embed6 (bvObs (inputs7.getD 1 bvZero)) = fun _ => false := by
  funext r
  change bvBit (embed6 r) (inputs7.getD 1 bvZero) = false
  revert r; decide +kernel

theorem embed6_inps : ∀ a ∈ inputs7, Available ((vars6 63).map bvObs) (restrictRows embed6 (bvObs a)) := by
  have h0 : restrictRows embed6 (bvObs (inputs7.getD 0 bvZero)) = bvObs (inputs6.getD 0 bvZero) := by
    funext r; revert r; decide +kernel
  have h2 : restrictRows embed6 (bvObs (inputs7.getD 2 bvZero)) = bvObs (inputs6.getD 1 bvZero) := by
    funext r; revert r; decide +kernel
  have h3 : restrictRows embed6 (bvObs (inputs7.getD 3 bvZero)) = bvObs (inputs6.getD 2 bvZero) := by
    funext r; revert r; decide +kernel
  have h4 : restrictRows embed6 (bvObs (inputs7.getD 4 bvZero)) = bvObs (inputs6.getD 3 bvZero) := by
    funext r; revert r; decide +kernel
  have h5 : restrictRows embed6 (bvObs (inputs7.getD 5 bvZero)) = bvObs (inputs6.getD 4 bvZero) := by
    funext r; revert r; decide +kernel
  have h6 : restrictRows embed6 (bvObs (inputs7.getD 6 bvZero)) = bvObs (inputs6.getD 5 bvZero) := by
    funext r; revert r; decide +kernel
  intro a ha
  have hmem : a = inputs7.getD 0 bvZero ∨ a = inputs7.getD 1 bvZero ∨ a = inputs7.getD 2 bvZero ∨
      a = inputs7.getD 3 bvZero ∨ a = inputs7.getD 4 bvZero ∨ a = inputs7.getD 5 bvZero ∨
      a = inputs7.getD 6 bvZero := by
    rw [← inputs7_list] at ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    fin_cases j <;> simp
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h0]; exact Or.inl (List.mem_map_of_mem (by decide))
  · rw [embed6_x1]; exact Or.inr (Or.inl ⟨false, rfl⟩)
  · rw [h2]; exact Or.inl (List.mem_map_of_mem (by decide))
  · rw [h3]; exact Or.inl (List.mem_map_of_mem (by decide))
  · rw [h4]; exact Or.inl (List.mem_map_of_mem (by decide))
  · rw [h5]; exact Or.inl (List.mem_map_of_mem (by decide))
  · rw [h6]; exact Or.inl (List.mem_map_of_mem (by decide))

theorem no_10_binary (gs : List Gate) (o : Nat)
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (small : gs.countP (fun g => !isNot g) ≤ 10)
    (hev : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = targetFn x) : False := by
  let result := (bvExec gs inputs7).getD o bvZero
  have goalEq : result = graph7 := by
    apply bvBit_ext; intro r
    rw [table_eval7 gs (fun g hg => (legal g hg).1) o r, graph7_bit]
    exact hev (sample7 r)
  have rep := bvGet_rep (bvExec gs inputs7) o
  change bvNrm result ∈ _ ∨ ¬bvProper (bvNrm result) at rep
  have pg : bvBit (0 : Fin 128) graph7 = false := by decide +kernel
  have hprop7 : bvProper graph7 := by unfold bvProper bvZero bvOne; decide +kernel
  rw [goalEq, bvNrm_id pg] at rep
  have targetIn := rep.resolve_right fun hn => hn hprop7
  obtain ⟨k, S, hk, run, hs⟩ := bvExtract gs inputs7 legal hprop7 targetIn
  have ns : inputs7.all bvPlain = true := by decide +kernel
  rw [bvNrm_map ns] at hs
  have hx1 : inputs7.getD 1 bvZero ∈ S := by
    apply bvRaw_required run inputs7 (inputs7.getD 1 bvZero) hs ⟨18, by decide⟩ ⟨16, by decide⟩
    · decide +kernel
    · intro v hv hne
      rw [← inputs7_list] at hv
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hv
      fin_cases j
      · decide +kernel
      · exact False.elim (hne rfl)
      · decide +kernel
      · decide +kernel
      · decide +kernel
      · decide +kernel
      · decide +kernel
  let rest := (S.erase (inputs7.getD 1 bvZero)).toList
  let ws := inputs7.getD 1 bvZero :: rest
  have hnd : ws.Nodup := List.nodup_cons.mpr ⟨by simp [rest], Finset.nodup_toList _⟩
  have hfe : ws.toFinset = S := by
    dsimp only [ws, rest]
    rw [List.toFinset_cons, Finset.toList_toFinset, Finset.insert_erase hx1]
  have run' := bvList_run run ws hnd hfe
  have supp : supply ((vars6 63).map bvObs) ((ws.map bvObs).map (restrictRows embed6)) := by
    intro v hv
    obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
    exact embed6_inps a (hs a (hfe ▸ List.mem_toFinset.mpr ha))
  have hprop6 : bvProper (graphGoal 63) := proper_of (by decide +kernel)
  have b := projected_bound embed6 run'
    (by rw [embed6_graph7]; exact obs_proper hprop6)
    Reach.start supp (L := 10)
    (by intro q bs hq ha; rw [embed6_graph7] at ha; exact low_63 q bs hq ha)
  have hmass : 1 ≤ mass ((ws.map bvObs).map (restrictRows embed6)) := by
    simp only [ws, List.map_cons, mass_cons, embed6_x1]
    have hc : Constant (fun _ : Row => false) := ⟨false, rfl⟩
    simp [cost, hc]
  omega

theorem countP_lt_of_not {gs : List Gate} (h : ∃ g ∈ gs, g.op = GateOp.not) :
    gs.countP (fun g => !isNot g) + 1 ≤ gs.length := by
  induction gs with
  | nil => obtain ⟨g, hg, _⟩ := h; cases hg
  | cons g gs ih =>
    rw [List.countP_cons, List.length_cons]
    by_cases hg : g.op = GateOp.not
    · have h1 : (!isNot g) = false := by simp [isNot, hg]
      have h2 := List.countP_le_length (p := fun g => !isNot g) (l := gs)
      simp only [h1, Bool.false_eq_true, ite_false]; omega
    · obtain ⟨g', hg', hop'⟩ := h
      rcases List.mem_cons.mp hg' with rfl | hg''
      · exact absurd hop' hg
      · have := ih ⟨g', hg'', hop'⟩
        split <;> omega

theorem main_proof (gates : List Gate) (o : ℕ)
    (hlegal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (_hone : ∀ i j : Fin gates.length, (gates.get i).op = GateOp.not → (gates.get j).op = GateOp.not → i = j)
    (hev : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = targetFn x) :
    ∃ (gates' : List Gate) (o' : ℕ),
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧
      ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = targetFn x := by
  by_cases h12 : 12 ≤ gates.length
  · exact ⟨mono12, 18, mono12_ok, mono12_len ▸ h12, mono12_eval⟩
  · by_cases hnot : ∃ g ∈ gates, g.op = GateOp.not
    · have hcnt := countP_lt_of_not hnot
      exact False.elim (no_10_binary gates o hlegal (by omega) hev)
    · push_neg at hnot
      refine ⟨gates, o, fun g hg => ?_, le_rfl, hev⟩
      have := hlegal g hg
      rcases this.1 with h1 | h2 | h3
      · exact ⟨Or.inl h1, this.2⟩
      · exact ⟨Or.inr h2, this.2⟩
      · exact absurd h3 (hnot g hg)

end PEqualNP.Outside.L_meta_10908

theorem PEqualNP.Outside.L_meta_10908 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) :=
  PEqualNP.Outside.L_meta_10908.main_proof
