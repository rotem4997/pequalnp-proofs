import PEqualNP.Defs

-- The signed live-wire search is adapted from L-meta-9539 (Apache-2.0).

namespace PEqualNP.Outside.L_meta_10566

-- The signed live-wire search follows L-meta-8463 and L-meta-1449, Apache-2.0.

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

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

-- Oppositely labeled assignments are paired across the upper and lower halves.
abbrev W := BitVec 256
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 128 := ((x >>> 128) ^^^ x).setWidth 128
def cuts (ws : List W) : BitVec 128 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 128) ++ (0 : BitVec 128)
abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 128) (w : W) : Prop :=
  w.getLsbD (128+i.val) ≠ w.getLsbD i.val

set_option maxRecDepth 100000 in
theorem ops_differs (i : Fin 128) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 128+i.val < 256 := by omega
  have hi' : i.val < 256 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

set_option maxRecDepth 100000 in
theorem cuts_spec (ws : List W) (i : Fin 128) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

set_option maxRecDepth 100000 in
theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 128)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

set_option maxRecDepth 100000 in
theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

set_option maxRecDepth 100000 in
theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

set_option maxRecDepth 100000 in
theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

-- The numeric evaluator is adapted from L-meta-10085 (Apache-2.0).
section Fast

def cutMask : ℕ := 0xffffffffffffffffffffffffffffffff
def cutModulus : ℕ := 0x100000000000000000000000000000000

def nsep (x : ℕ) : ℕ :=
  Nat.mod (Nat.xor (Nat.shiftRight x 128) x) cutModulus

def ncuts (ws : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun w _ ih => Nat.lor (nsep w) ih) ws

def len (ws : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun _ _ ih => Nat.succ ih) ws

def orBGoal (w : ℕ) : Bool := Nat.beq w cutMask || Nat.beq w (Nat.shiftLeft cutMask 128)

def nisGoal (ws : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun w t _ => List.rec (motive := fun _ => Bool)
      (orBGoal w) (fun _ _ _ => false) t) ws

-- force a word: the continuation receives a closed numeral
def frc (w : ℕ) (k : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k Nat.zero) (fun m _ => k (Nat.succ m)) w

-- reverse `xs` onto `acc`, then continue
def revK (xs : List ℕ) (acc : List ℕ) (k : List ℕ → Bool) : Bool :=
  List.rec (motive := fun _ => List ℕ → Bool) (fun acc => k acc) (fun x _ ih acc => ih (x :: acc))
    xs acc

-- insert into an ascending list, then continue
def insK (w : ℕ) (l : List ℕ) (k : List ℕ → Bool) : Bool :=
  List.rec (motive := fun _ => (List ℕ → Bool) → Bool) (fun k => k [w])
    (fun x xs ih k => Bool.rec (ih (fun l2 => k (x :: l2))) (k (w :: x :: xs)) (Nat.ble w x)) l k

def call (next : List ℕ → Bool) (c : List ℕ) : Bool := Bool.rec false true (next c)

def orB (x y : Bool) : Bool := Bool.rec y true x

-- no slack: both operands leave the live set
def one0 (next : List ℕ → Bool) (base : ℕ) (pre mid post : List ℕ) (w : ℕ) : Bool :=
  Bool.rec false
    (frc w (fun w2 => revK mid post (fun m => revK pre m (fun r =>
      insK w2 r (fun c => call next c)))))
    (Nat.beq (Nat.lor (nsep w) base) cutMask)

def maxWord : ℕ := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def opsN (a b : ℕ) : List ℕ :=
  [Nat.land a b, Nat.lor a b, Nat.land a (Nat.sub maxWord b), Nat.land b (Nat.sub maxWord a)]

def fresh (a b w : ℕ) : Bool := w != a && w != b

def pair0 (next : List ℕ → Bool) (a b _sa _sb base : ℕ) (pre mid post : List ℕ) : Bool :=
  (opsN a b).any fun w => fresh a b w && one0 next base pre mid post w

-- with slack: an operand may stay
def oneG (next : List ℕ → Bool) (extra a b sa sb base : ℕ) (pre mid post : List ℕ) (w : ℕ) :
    Bool :=
  frc w (fun w2 =>
    let covered := Nat.lor (nsep w2) base
    let withRest (f : List ℕ → Bool) := revK mid post (fun m => revK pre m f)
    orB (Bool.rec false (withRest (fun r => insK w2 r (call next)))
      (Nat.beq covered cutMask))
    (orB (Bool.rec false (withRest (fun r => insK a r (fun ar => insK w2 ar (call next))))
      (Nat.beq (Nat.lor covered sa) cutMask))
    (orB (Bool.rec false (withRest (fun r => insK b r (fun br => insK w2 br (call next))))
      (Nat.beq (Nat.lor covered sb) cutMask))
      (Bool.rec false
        (withRest (fun r => insK b r (fun br => insK a br (fun abr => insK w2 abr (call next)))))
        (Nat.ble 2 extra)))))

def pairG (next : List ℕ → Bool) (extra a b sa sb base : ℕ) (pre mid post : List ℕ) : Bool :=
  (opsN a b).any fun w => fresh a b w && oneG next extra a b sa sb base pre mid post w

-- the second operand runs over `rest`; `mid` holds the words between the operands, reversed
def innerAux (P : ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → Bool) (a sa : ℕ)
    (pre : List ℕ) (preCut : ℕ) (rest mid : List ℕ) (midCut : ℕ) : Bool :=
  List.rec (motive := fun _ => List ℕ → ℕ → Bool) (fun _ _ => false)
    (fun b post ih mid midCut =>
      Bool.rec (ih (b :: mid) (Nat.lor midCut (nsep b))) true
        (P a b sa (nsep b) (Nat.lor (Nat.lor preCut midCut) (ncuts post)) pre mid post))
    rest mid midCut

-- the first operand runs over `ws`; `pre` holds the words before it, reversed
def outerAux (P : ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → Bool) (ws pre : List ℕ)
    (preCut : ℕ) : Bool :=
  List.rec (motive := fun _ => List ℕ → ℕ → Bool) (fun _ _ => false)
    (fun a rest ih pre preCut =>
      Bool.rec (ih (a :: pre) (Nat.lor preCut (nsep a))) true
        (innerAux P a (nsep a) pre preCut rest [] 0))
    ws pre preCut

def stepF (k1 : ℕ) (next : List ℕ → Bool) (ws : List ℕ) : Bool :=
  Bool.rec
    (Bool.rec (outerAux (pairG next (Nat.sub (Nat.succ (Nat.succ k1)) (len ws))) ws [] 0)
      (outerAux (pair0 next) ws [] 0) (Nat.beq (len ws) (Nat.succ (Nat.succ k1))))
    true (nisGoal ws)

def nopt (k : ℕ) (ws : List ℕ) : Bool :=
  Nat.rec (motive := fun _ => List ℕ → Bool) (fun ws => nisGoal ws)
    (fun k1 ih ws => stepF k1 ih ws) k ws

def ins (w : ℕ) : List ℕ → List ℕ
  | [] => [w]
  | x :: xs => if Nat.ble w x = true then w :: x :: xs else x :: ins w xs

def cutR (l : List ℕ) : ℕ := l.foldr (fun x c => Nat.lor c (nsep x)) 0

def baseOf (pre mid post : List ℕ) : ℕ := Nat.lor (Nat.lor (cutR pre) (cutR mid)) (ncuts post)

def rOf (pre mid post : List ℕ) : List ℕ := pre.reverse ++ (mid.reverse ++ post)

abbrev Split := List ℕ × ℕ × List ℕ × ℕ × List ℕ

def innerS (pre : List ℕ) (a : ℕ) : List ℕ → List ℕ → List Split
  | [], _ => []
  | b :: post, mid => (pre, a, mid, b, post) :: innerS pre a post (b :: mid)

def outerS : List ℕ → List ℕ → List Split
  | [], _ => []
  | a :: rest, pre => innerS pre a rest [] ++ outerS rest (a :: pre)

def kids0 (base : ℕ) (r : List ℕ) (w : ℕ) : List (List ℕ) :=
  if Nat.beq (Nat.lor (nsep w) base) cutMask = true then [ins w r] else []

def kidsG (extra a b sa sb base : ℕ) (r : List ℕ) (w : ℕ) : List (List ℕ) :=
  (if Nat.beq (Nat.lor (nsep w) base) cutMask = true then [ins w r] else []) ++
  ((if Nat.beq (Nat.lor (Nat.lor (nsep w) base) sa) cutMask = true then [ins w (ins a r)] else []) ++
  ((if Nat.beq (Nat.lor (Nat.lor (nsep w) base) sb) cutMask = true then [ins w (ins b r)] else []) ++
   (if Nat.ble 2 extra = true then [ins w (ins a (ins b r))] else [])))

def kidsPair0 (t : Split) : List (List ℕ) :=
  ((opsN t.2.1 t.2.2.2.1).filter (fresh t.2.1 t.2.2.2.1)).flatMap (kids0 (baseOf t.1 t.2.2.1 t.2.2.2.2) (rOf t.1 t.2.2.1 t.2.2.2.2))

def kidsPairG (extra : ℕ) (t : Split) : List (List ℕ) :=
  ((opsN t.2.1 t.2.2.2.1).filter (fresh t.2.1 t.2.2.2.1)).flatMap
    (kidsG extra t.2.1 t.2.2.2.1 (nsep t.2.1) (nsep t.2.2.2.1) (baseOf t.1 t.2.2.1 t.2.2.2.2)
      (rOf t.1 t.2.2.1 t.2.2.2.2))

def kidsL (k1 : ℕ) (ws : List ℕ) : List (List ℕ) :=
  if Nat.beq (len ws) (Nat.succ (Nat.succ k1)) = true then (outerS ws []).flatMap kidsPair0
  else (outerS ws []).flatMap (kidsPairG (Nat.sub (Nat.succ (Nat.succ k1)) (len ws)))

theorem brec {α : Type} (f t : α) (c : Bool) :
    (Bool.rec (motive := fun _ => α) f t c) = if c = true then t else f := by
  cases c <;> rfl

theorem frc_eq (w : ℕ) (k : ℕ → Bool) : frc w k = k w := by
  cases w <;> rfl

theorem revK_eq (xs : List ℕ) : ∀ (acc : List ℕ) (k : List ℕ → Bool),
    revK xs acc k = k (xs.reverse ++ acc) := by
  induction xs with
  | nil => intro acc k; rfl
  | cons x xs ih =>
    intro acc k
    have e : revK (x :: xs) acc k = revK xs (x :: acc) k := rfl
    rw [e, ih]
    simp

theorem insK_eq (w : ℕ) (l : List ℕ) : ∀ k : List ℕ → Bool, insK w l k = k (ins w l) := by
  induction l with
  | nil => intro k; rfl
  | cons x xs ih =>
    intro k
    have e : insK w (x :: xs) k =
        Bool.rec (insK w xs (fun l2 => k (x :: l2))) (k (w :: x :: xs)) (Nat.ble w x) := rfl
    rw [e, brec, ih]
    by_cases h : Nat.ble w x = true <;> simp [ins, h]

theorem call_eq (next : List ℕ → Bool) (c : List ℕ) : call next c = next c := by
  unfold call
  cases next c <;> rfl

theorem orB_eq (x y : Bool) : orB x y = (x || y) := by
  cases x <;> rfl

theorem one0_eq (next : List ℕ → Bool) (base : ℕ) (pre mid post : List ℕ) (w : ℕ) :
    one0 next base pre mid post w = (kids0 base (rOf pre mid post) w).any next := by
  unfold one0 kids0 rOf
  rw [brec]
  generalize Nat.beq (Nat.lor (nsep w) base) cutMask = c
  cases c <;> simp [frc_eq, revK_eq, insK_eq, call_eq]

theorem oneG_eq (next : List ℕ → Bool) (extra a b sa sb base : ℕ) (pre mid post : List ℕ)
    (w : ℕ) :
    oneG next extra a b sa sb base pre mid post w =
      (kidsG extra a b sa sb base (rOf pre mid post) w).any next := by
  unfold oneG kidsG rOf
  simp only [frc_eq, revK_eq, insK_eq, call_eq, orB_eq, brec, List.any_append]
  generalize Nat.beq (Nat.lor (nsep w) base) cutMask = c1
  generalize Nat.beq (Nat.lor (Nat.lor (nsep w) base) sa) cutMask = c2
  generalize Nat.beq (Nat.lor (Nat.lor (nsep w) base) sb) cutMask = c3
  generalize Nat.ble 2 extra = c4
  cases c1 <;> cases c2 <;> cases c3 <;> cases c4 <;> simp

theorem pair0_eq (next : List ℕ → Bool) (a b sa sb base : ℕ) (pre mid post : List ℕ) :
    pair0 next a b sa sb base pre mid post =
      (((opsN a b).filter (fresh a b)).flatMap (kids0 base (rOf pre mid post))).any next := by
  simp only [pair0, List.any_flatMap, List.any_filter, one0_eq]

theorem pairG_eq (next : List ℕ → Bool) (extra a b sa sb base : ℕ) (pre mid post : List ℕ) :
    pairG next extra a b sa sb base pre mid post =
      (((opsN a b).filter (fresh a b)).flatMap (kidsG extra a b sa sb base (rOf pre mid post))).any next := by
  simp only [pairG, List.any_flatMap, List.any_filter, oneG_eq]

def HP (P : ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → Bool) (t : Split) : Bool :=
  P t.2.1 t.2.2.2.1 (nsep t.2.1) (nsep t.2.2.2.1) (baseOf t.1 t.2.2.1 t.2.2.2.2)
    t.1 t.2.2.1 t.2.2.2.2

theorem innerAux_eq (P : ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → Bool) (a : ℕ)
    (pre : List ℕ) : ∀ rest mid : List ℕ,
    innerAux P a (nsep a) pre (cutR pre) rest mid (cutR mid) =
      (innerS pre a rest mid).any (HP P) := by
  intro rest
  induction rest with
  | nil => intro mid; rfl
  | cons b post ih =>
    intro mid
    have e : innerAux P a (nsep a) pre (cutR pre) (b :: post) mid (cutR mid) =
        Bool.rec (innerAux P a (nsep a) pre (cutR pre) post (b :: mid)
            (Nat.lor (cutR mid) (nsep b)))
          true (P a b (nsep a) (nsep b) (Nat.lor (Nat.lor (cutR pre) (cutR mid)) (ncuts post))
            pre mid post) := rfl
    have c : Nat.lor (cutR mid) (nsep b) = cutR (b :: mid) := rfl
    rw [e, brec, c, ih]
    simp only [innerS, List.any_cons, HP, baseOf]
    cases P a b (nsep a) (nsep b) (Nat.lor (Nat.lor (cutR pre) (cutR mid)) (ncuts post))
      pre mid post <;> simp

theorem outerAux_eq (P : ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → Bool) :
    ∀ ws pre : List ℕ, outerAux P ws pre (cutR pre) = (outerS ws pre).any (HP P) := by
  intro ws
  induction ws with
  | nil => intro pre; rfl
  | cons a rest ih =>
    intro pre
    have e : outerAux P (a :: rest) pre (cutR pre) =
        Bool.rec (outerAux P rest (a :: pre) (Nat.lor (cutR pre) (nsep a))) true
          (innerAux P a (nsep a) pre (cutR pre) rest [] 0) := rfl
    have c : Nat.lor (cutR pre) (nsep a) = cutR (a :: pre) := rfl
    have z : (0 : ℕ) = cutR [] := rfl
    rw [e, brec, c, ih, z, innerAux_eq]
    simp only [outerS, List.any_append]
    cases (innerS pre a rest []).any (HP P) <;> simp

theorem HP_pair0 (next : List ℕ → Bool) :
    HP (pair0 next) = fun t => (kidsPair0 t).any next := by
  funext t
  simp only [HP, pair0_eq, kidsPair0]

theorem HP_pairG (next : List ℕ → Bool) (extra : ℕ) :
    HP (pairG next extra) = fun t => (kidsPairG extra t).any next := by
  funext t
  simp only [HP, pairG_eq, kidsPairG]

theorem stepF_eq (k1 : ℕ) (next : List ℕ → Bool) (ws : List ℕ) :
    stepF k1 next ws = (nisGoal ws || (kidsL k1 ws).any next) := by
  have z : (0 : ℕ) = cutR [] := rfl
  unfold stepF kidsL
  rw [brec, brec, z, outerAux_eq, outerAux_eq, HP_pair0, HP_pairG]
  cases nisGoal ws
  · cases Nat.beq (len ws) (Nat.succ (Nat.succ k1)) <;> simp [List.any_flatMap]
  · simp

theorem nopt_zero (ws : List ℕ) : nopt 0 ws = nisGoal ws := rfl

theorem nopt_succ (k : ℕ) (ws : List ℕ) :
    nopt (k + 1) ws = (nisGoal ws || (kidsL k ws).any (nopt k)) := by
  rw [← stepF_eq]
  rfl

theorem beq_of_eq {a b : ℕ} (h : a = b) : Nat.beq a b = true := h ▸ Nat.beq_refl a

theorem cutMask_eq : (-1 : BitVec 128).toNat = cutMask := by decide

theorem nsep_toNat (w : W) : nsep w.toNat = (sep w).toNat := by
  simp only [nsep, sep, BitVec.toNat_xor, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight]
  rfl

theorem ncuts_cons (w : ℕ) (ws : List ℕ) : ncuts (w :: ws) = Nat.lor (nsep w) (ncuts ws) := rfl

theorem cuts_cons (a : W) (l : List W) : cuts (a :: l) = sep a ||| cuts l := rfl

theorem ncuts_map (l : List W) : ncuts (l.map BitVec.toNat) = (cuts l).toNat := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, ncuts_cons, cuts_cons, BitVec.toNat_or, ih, nsep_toNat]
    rfl

theorem ncuts_append (l1 l2 : List ℕ) : ncuts (l1 ++ l2) = Nat.lor (ncuts l1) (ncuts l2) := by
  induction l1 with
  | nil =>
    have e : ncuts ([] : List ℕ) = 0 := rfl
    rw [List.nil_append, e]
    exact (Nat.zero_or _).symm
  | cons a l ih =>
    rw [List.cons_append, ncuts_cons, ih, ncuts_cons]
    exact (Nat.or_assoc _ _ _).symm

theorem cutR_eq (l : List ℕ) : cutR l = ncuts l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have e : cutR (a :: l) = Nat.lor (cutR l) (nsep a) := rfl
    rw [e, ih, ncuts_cons]
    exact Nat.or_comm _ _

theorem ncuts_reverse (l : List ℕ) : ncuts l.reverse = ncuts l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have e1 : ncuts [a] = nsep a ||| 0 := rfl
    have e2 : ncuts (a :: l) = nsep a ||| ncuts l := rfl
    rw [List.reverse_cons, ncuts_append, ih, e1, e2]
    change (ncuts l ||| (nsep a ||| 0)) = (nsep a ||| ncuts l)
    rw [Nat.or_zero, Nat.or_comm]

theorem baseOf_map (xs ys zs : List W) :
    baseOf (xs.map BitVec.toNat).reverse (ys.map BitVec.toNat).reverse (zs.map BitVec.toNat) =
      (cuts (xs ++ (ys ++ zs))).toNat := by
  rw [← ncuts_map, List.map_append, List.map_append, ncuts_append, ncuts_append]
  unfold baseOf
  rw [cutR_eq, cutR_eq, ncuts_reverse, ncuts_reverse]
  exact Nat.or_assoc _ _ _

theorem opsN_map (a b : W) : opsN a.toNat b.toNat = (ops a b).map BitVec.toNat := by
  simp only [opsN, ops, List.map_cons, List.map_nil, BitVec.toNat_and, BitVec.toNat_or, BitVec.toNat_not]
  rfl

theorem len_eq (l : List ℕ) : len l = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have e : len (a :: l) = Nat.succ (len l) := rfl
    rw [e, ih]
    rfl

def insW (w : W) : List W → List W
  | [] => [w]
  | x :: xs => if Nat.ble w.toNat x.toNat = true then w :: x :: xs else x :: insW w xs

theorem insW_map (w : W) (l : List W) :
    (insW w l).map BitVec.toNat = ins w.toNat (l.map BitVec.toNat) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [insW, ins, List.map_cons]
    split_ifs
    · rfl
    · rw [List.map_cons, ih]

theorem insW_perm (w : W) (l : List W) : (insW w l).Perm (w :: l) := by
  induction l with
  | nil => exact .refl _
  | cons x xs ih =>
    simp only [insW]
    split_ifs
    · exact .refl _
    · exact (ih.cons x).trans (.swap _ _ _)

theorem mem_innerS (pre : List ℕ) (a b : ℕ) (zs : List ℕ) : ∀ ys mid : List ℕ,
    (pre, a, ys.reverse ++ mid, b, zs) ∈ innerS pre a (ys ++ b :: zs) mid := by
  intro ys
  induction ys with
  | nil => intro mid; simp [innerS]
  | cons y ys ih =>
    intro mid
    simp only [List.cons_append, innerS, List.reverse_cons, List.append_assoc]
    exact List.mem_cons_of_mem _ (ih (y :: mid))

theorem mem_outerS (a b : ℕ) (ys zs : List ℕ) : ∀ xs pre : List ℕ,
    (xs.reverse ++ pre, a, ys.reverse, b, zs) ∈ outerS (xs ++ a :: (ys ++ b :: zs)) pre := by
  intro xs
  induction xs with
  | nil =>
    intro pre
    simp only [List.nil_append, List.reverse_nil, outerS]
    exact List.mem_append_left _ (by simpa using mem_innerS pre a b zs ys [])
  | cons x xs ih =>
    intro pre
    simp only [List.cons_append, outerS, List.reverse_cons, List.append_assoc]
    exact List.mem_append_right _ (ih (x :: pre))

theorem split_two {α : Type} {a b : α} {l : List α} (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b) :
    (∃ xs ys zs, l = xs ++ a :: (ys ++ b :: zs)) ∨ (∃ xs ys zs, l = xs ++ b :: (ys ++ a :: zs)) := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem ha
  rcases List.mem_append.mp hb with h | h
  · obtain ⟨s1, s2, rfl⟩ := List.append_of_mem h
    exact .inr ⟨s1, s2, t, by simp⟩
  · rcases List.mem_cons.mp h with h | h
    · exact absurd h.symm hne
    · obtain ⟨t1, t2, rfl⟩ := List.append_of_mem h
      exact .inl ⟨s, t1, t2, rfl⟩

theorem nisGoal_goal {g : W} (hg : g = goal ∨ g = ~~~goal) : nisGoal [g.toNat] = true := by
  rcases hg with rfl | rfl <;> decide +kernel

theorem mem_kids0 {base w : ℕ} {r : List ℕ} (h : Nat.beq (Nat.lor (nsep w) base) cutMask = true) :
    ins w r ∈ kids0 base r w := by
  unfold kids0
  rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
  exact List.mem_singleton.mpr rfl

theorem mem_kidsG1 {extra a b sa sb base w : ℕ} {r : List ℕ}
    (h : Nat.beq (Nat.lor (nsep w) base) cutMask = true) :
    ins w r ∈ kidsG extra a b sa sb base r w := by
  unfold kidsG
  refine List.mem_append_left _ ?_
  rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
  exact List.mem_singleton.mpr rfl

theorem mem_kidsG2 {extra a b sa sb base w : ℕ} {r : List ℕ}
    (h : Nat.beq (Nat.lor (Nat.lor (nsep w) base) sa) cutMask = true) :
    ins w (ins a r) ∈ kidsG extra a b sa sb base r w := by
  unfold kidsG
  refine List.mem_append_right _ (List.mem_append_left _ ?_)
  rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
  exact List.mem_singleton.mpr rfl

theorem mem_kidsG3 {extra a b sa sb base w : ℕ} {r : List ℕ}
    (h : Nat.beq (Nat.lor (Nat.lor (nsep w) base) sb) cutMask = true) :
    ins w (ins b r) ∈ kidsG extra a b sa sb base r w := by
  unfold kidsG
  refine List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ ?_))
  rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
  exact List.mem_singleton.mpr rfl

theorem mem_kidsG4 {extra a b sa sb base w : ℕ} {r : List ℕ} (h : Nat.ble 2 extra = true) :
    ins w (ins a (ins b r)) ∈ kidsG extra a b sa sb base r w := by
  unfold kidsG
  refine List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ ?_))
  rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
  exact List.mem_singleton.mpr rfl

theorem mem_kidsL {k : ℕ} {wsN : List ℕ} {t : Split} {w : ℕ} {c : List ℕ}
    (ht : t ∈ outerS wsN []) (hw : w ∈ (opsN t.2.1 t.2.2.2.1).filter (fresh t.2.1 t.2.2.2.1))
    (h0 : Nat.beq (len wsN) (Nat.succ (Nat.succ k)) = true →
      c ∈ kids0 (baseOf t.1 t.2.2.1 t.2.2.2.2) (rOf t.1 t.2.2.1 t.2.2.2.2) w)
    (hG : ¬ Nat.beq (len wsN) (Nat.succ (Nat.succ k)) = true →
      c ∈ kidsG (Nat.sub (Nat.succ (Nat.succ k)) (len wsN)) t.2.1 t.2.2.2.1 (nsep t.2.1)
        (nsep t.2.2.2.1) (baseOf t.1 t.2.2.1 t.2.2.2.2) (rOf t.1 t.2.2.1 t.2.2.2.2) w) :
    c ∈ kidsL k wsN := by
  unfold kidsL
  split_ifs with hd
  · exact List.mem_flatMap.mpr ⟨t, ht, List.mem_flatMap.mpr ⟨w, hw, h0 hd⟩⟩
  · exact List.mem_flatMap.mpr ⟨t, ht, List.mem_flatMap.mpr ⟨w, hw, hG hd⟩⟩

theorem guard1 {z : W} {r : List W} (h : cuts (z :: r) = -1) :
    Nat.beq (Nat.lor (nsep z.toNat) (cuts r).toNat) cutMask = true := by
  rw [cuts_cons] at h
  have e := congrArg BitVec.toNat h
  rw [BitVec.toNat_or, ← nsep_toNat, cutMask_eq] at e
  exact beq_of_eq e

theorem guard2 {z a : W} {r : List W} (h : cuts (z :: a :: r) = -1) :
    Nat.beq (Nat.lor (Nat.lor (nsep z.toNat) (cuts r).toNat) (nsep a.toNat)) cutMask = true := by
  rw [cuts_cons, cuts_cons] at h
  have e := congrArg BitVec.toNat h
  rw [BitVec.toNat_or, BitVec.toNat_or, ← nsep_toNat, ← nsep_toNat, cutMask_eq] at e
  refine beq_of_eq (Eq.trans ?_ e)
  change (nsep z.toNat ||| (cuts r).toNat ||| nsep a.toNat) =
    (nsep z.toNat ||| (nsep a.toNat ||| (cuts r).toNat))
  rw [Nat.or_assoc, Nat.or_comm (cuts r).toNat]

theorem child_of_split {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws xs ys zs : List W}
    {a b z : W} {needed : Finset W} (hn : ws.Nodup)
    (hsplit : ws = xs ++ a :: (ys ++ b :: zs)) (hz : z ∈ basicOps a b) (hout : z ∉ ws.toFinset)
    (hs : ws.toFinset = insert a (insert b needed))
    (tail : live basicOps g k (insert z needed)) :
    ∃ cW : List W, cW.Nodup ∧ cW.length ≤ k + 1 ∧ live basicOps g k cW.toFinset ∧
      cW.map BitVec.toNat ∈ kidsL k (ws.map BitVec.toNat) := by
  have p1 : (xs ++ a :: (ys ++ b :: zs)).Perm (a :: (xs ++ (ys ++ b :: zs))) := List.perm_middle
  have p2 : (xs ++ (ys ++ b :: zs)).Perm (b :: (xs ++ (ys ++ zs))) := by
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.perm_middle
  have perm : ws.Perm (a :: b :: (xs ++ (ys ++ zs))) := hsplit ▸ p1.trans (p2.cons a)
  obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hs
  have hznew : z ∉ kept := by
    intro hu
    apply hout
    rw [hs]
    exact Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
  have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
  have hl2 : live basicOps g k (z :: kept).toFinset := by
    simpa [hfin] using tail
  have hc := live_card hl2
  rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
  have hcut := cuts_full hg hl2
  have hlen2 := perm.length_eq
  simp only [List.length_cons] at hlen2
  have hmap : ws.map BitVec.toNat = xs.map BitVec.toNat ++
      a.toNat :: (ys.map BitVec.toNat ++ b.toNat :: zs.map BitVec.toNat) := by
    rw [hsplit]
    simp
  have ht := mem_outerS a.toNat b.toNat (ys.map BitVec.toNat) (zs.map BitVec.toNat)
    (xs.map BitVec.toNat) []
  rw [List.append_nil, ← hmap] at ht
  have hzN : z.toNat ∈ (opsN a.toNat b.toNat).filter (fresh a.toNat b.toNat) := by
    apply List.mem_filter.mpr
    refine ⟨?_, ?_⟩
    · rw [opsN_map]
      exact List.mem_map_of_mem (List.mem_toFinset.mp hz)
    · have hza : z ≠ a := fun e => hout (by simp [hs, e])
      have hzb : z ≠ b := fun e => hout (by simp [hs, e])
      simp [fresh, BitVec.toNat_inj, hza, hzb]
  have hr : rOf (xs.map BitVec.toNat).reverse (ys.map BitVec.toNat).reverse
      (zs.map BitVec.toNat) = (xs ++ (ys ++ zs)).map BitVec.toNat := by
    simp [rOf]
  have hbase := baseOf_map xs ys zs
  have hlenN : len (ws.map BitVec.toNat) = ws.length := by
    rw [len_eq, List.length_map]
  have live_of (cW : List W) (hp : cW.Perm (z :: kept)) :
      cW.Nodup ∧ cW.length ≤ k + 1 ∧ live basicOps g k cW.toFinset := by
    refine ⟨hp.nodup_iff.mpr hnd, ?_, ?_⟩
    · rw [hp.length_eq, List.length_cons]
      exact hc
    · have e : cW.toFinset = (z :: kept).toFinset := List.toFinset_eq_of_perm _ _ hp
      rw [e]
      exact hl2
  simp only [keepChoices, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · refine ⟨insW z (xs ++ (ys ++ zs)), (live_of _ (insW_perm _ _)).1, (live_of _ (insW_perm _ _)).2.1,
      (live_of _ (insW_perm _ _)).2.2, ?_⟩
    rw [insW_map]
    refine mem_kidsL ht hzN ?_ ?_
    · intro _
      simp only [hr, hbase]
      exact mem_kids0 (guard1 hcut)
    · intro _
      simp only [hr, hbase]
      exact mem_kidsG1 (guard1 hcut)
  · have hp : (insW z (insW a (xs ++ (ys ++ zs)))).Perm (z :: a :: (xs ++ (ys ++ zs))) :=
      (insW_perm _ _).trans ((insW_perm _ _).cons z)
    refine ⟨_, (live_of _ hp).1, (live_of _ hp).2.1, (live_of _ hp).2.2, ?_⟩
    rw [insW_map, insW_map]
    refine mem_kidsL ht hzN ?_ ?_
    · intro hd
      exfalso
      rw [hlenN] at hd
      have := Nat.eq_of_beq_eq_true hd
      simp only [List.length_cons] at hc
      omega
    · intro _
      simp only [hr, hbase]
      exact mem_kidsG2 (guard2 hcut)
  · have hp : (insW z (insW b (xs ++ (ys ++ zs)))).Perm (z :: b :: (xs ++ (ys ++ zs))) :=
      (insW_perm _ _).trans ((insW_perm _ _).cons z)
    refine ⟨_, (live_of _ hp).1, (live_of _ hp).2.1, (live_of _ hp).2.2, ?_⟩
    rw [insW_map, insW_map]
    refine mem_kidsL ht hzN ?_ ?_
    · intro hd
      exfalso
      rw [hlenN] at hd
      have := Nat.eq_of_beq_eq_true hd
      simp only [List.length_cons] at hc
      omega
    · intro _
      simp only [hr, hbase]
      exact mem_kidsG3 (guard2 hcut)
  · have hp : (insW z (insW a (insW b (xs ++ (ys ++ zs))))).Perm
        (z :: a :: b :: (xs ++ (ys ++ zs))) :=
      (insW_perm _ _).trans (((insW_perm _ _).trans ((insW_perm _ _).cons a)).cons z)
    refine ⟨_, (live_of _ hp).1, (live_of _ hp).2.1, (live_of _ hp).2.2, ?_⟩
    rw [insW_map, insW_map, insW_map]
    simp only [List.length_cons] at hc
    refine mem_kidsL ht hzN ?_ ?_
    · intro hd
      exfalso
      rw [hlenN] at hd
      have := Nat.eq_of_beq_eq_true hd
      omega
    · intro _
      simp only [hr]
      refine mem_kidsG4 ?_
      rw [hlenN]
      apply Nat.ble_eq_true_of_le
      change 2 ≤ k + 2 - ws.length
      omega

theorem child_exists {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (hn : ws.Nodup) (hl : live basicOps g (k + 1) ws.toFinset) :
    ws = [g] ∨ ∃ cW : List W, cW.Nodup ∧ cW.length ≤ k + 1 ∧ live basicOps g k cW.toFinset ∧
      cW.map BitVec.toNat ∈ kidsL k (ws.map BitVec.toNat) := by
  rcases first_live hl with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
  · exact .inl (singleton_list hn done)
  · right
    rcases split_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab with
      ⟨xs, ys, zs, e⟩ | ⟨xs, ys, zs, e⟩
    · exact child_of_split hg hn e hz hout hs tail
    · exact child_of_split hg hn e (ops_swap a b ▸ hz) hout
        (by rw [hs, Finset.insert_comm]) tail

theorem nopt_complete {g : W} (hg : g = goal ∨ g = ~~~goal) : ∀ (k : ℕ) (ws : List W),
    ws.Nodup → live basicOps g k ws.toFinset → nopt k (ws.map BitVec.toNat) = true := by
  intro k
  induction k with
  | zero =>
    intro ws hn h
    have e := singleton_list hn h
    rw [e]
    exact nisGoal_goal hg
  | succ k ih =>
    intro ws hn hl
    rw [nopt_succ]
    rcases child_exists hg hn hl with e | ⟨cW, hcn, _, hcl, hmem⟩
    · rw [e]
      have := nisGoal_goal hg
      simp only [List.map_cons, List.map_nil, this, Bool.true_or]
    · have := ih cW hcn hcl
      rw [Bool.or_eq_true]
      exact .inr (List.any_eq_true.mpr ⟨_, hmem, this⟩)

-- the first step is laid out as a list, so that it can be checked in several parts
def rootsN (n : ℕ) (insN : List ℕ) : List (List ℕ) :=
  insN.sublists.filter (fun ws => Nat.ble ws.length (n + 1) && Nat.beq (ncuts ws) cutMask)

def allKids (m : ℕ) (insN : List ℕ) : List (List ℕ) := (rootsN (m + 1) insN).flatMap (kidsL m)

def isort (l : List ℕ) : List ℕ := l.foldr ins []

-- sort a list by insertion (every word forced), then continue
def sortK (l : List ℕ) (k : List ℕ → Bool) : Bool :=
  List.rec (motive := fun _ => (List ℕ → Bool) → Bool) (fun k => k [])
    (fun x _ ih k => ih (fun s => frc x (fun x2 => insK x2 s k))) l k

theorem sortK_eq (l : List ℕ) : ∀ k : List ℕ → Bool, sortK l k = k (isort l) := by
  induction l with
  | nil => intro k; rfl
  | cons x xs ih =>
    intro k
    have e : sortK (x :: xs) k = sortK xs (fun s => frc x (fun x2 => insK x2 s k)) := rfl
    rw [e, ih, frc_eq, insK_eq]
    rfl

def isortW (l : List W) : List W := l.foldr insW []

theorem isortW_map (l : List W) :
    (isortW l).map BitVec.toNat = isort (l.map BitVec.toNat) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have e1 : isortW (x :: xs) = insW x (isortW xs) := rfl
    have e2 : isort (x.toNat :: xs.map BitVec.toNat) =
        ins x.toNat (isort (xs.map BitVec.toNat)) := rfl
    rw [List.map_cons, e1, e2, insW_map, ih]

theorem isortW_perm (l : List W) : (isortW l).Perm l := by
  induction l with
  | nil => exact .refl _
  | cons x xs ih => exact (insW_perm x (isortW xs)).trans (ih.cons x)

-- a state of the first step, sorted, has no run below it
def dead (m : ℕ) (c : List ℕ) : Bool := sortK c (fun c2 => Bool.rec true false (nopt m c2))

theorem dead_eq (m : ℕ) (c : List ℕ) : dead m c = !nopt m (isort c) := by
  unfold dead
  rw [sortK_eq, brec]
  cases nopt m (isort c) <;> rfl

theorem refute (m : ℕ) (inputs : List W) (hnd : inputs.Nodup)
    (h0 : (rootsN (m + 1) (inputs.map BitVec.toNat)).all (fun ws => !nisGoal ws) = true)
    (hk : (allKids m (inputs.map BitVec.toNat)).all (dead m) = true) :
    ∀ t, (t = goal ∨ t = ~~~goal) → build basicOps t (m + 1) inputs.toFinset → False := by
  intro g hg hb
  classical
  obtain ⟨s, hs, hl⟩ := compress hb
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd2 : ws.Nodup := hnd.filter _
  have hl2 : live basicOps g (m + 1) ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl2
  rw [List.toFinset_card_of_nodup hnd2] at sz
  have hroot : ws.map BitVec.toNat ∈ rootsN (m + 1) (inputs.map BitVec.toNat) := by
    unfold rootsN
    refine List.mem_filter.mpr ⟨List.mem_sublists.mpr ((List.filter_sublist).map _), ?_⟩
    rw [Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · apply Nat.ble_eq_true_of_le
      rw [List.length_map]
      exact sz
    · rw [ncuts_map, cuts_full hg hl2, cutMask_eq]
      exact Nat.beq_refl _
  rcases child_exists hg hnd2 hl2 with e | ⟨cW, hcn, _, hcl, hmem⟩
  · have h1 := List.all_eq_true.mp h0 _ hroot
    rw [e] at h1
    have h2 := nisGoal_goal hg
    simp only [List.map_cons, List.map_nil, h2] at h1
    exact absurd h1 (by decide)
  · have hd := List.all_eq_true.mp hk _ (List.mem_flatMap.mpr ⟨_, hroot, hmem⟩)
    have hp := isortW_perm cW
    have e : (isortW cW).toFinset = cW.toFinset := List.toFinset_eq_of_perm _ _ hp
    have run := nopt_complete hg m (isortW cW) (hp.nodup_iff.mpr hcn) (e ▸ hcl)
    rw [isortW_map] at run
    rw [dead_eq, run] at hd
    exact absurd hd (by decide)

theorem all_chunk {α : Type} (p : α → Bool) (l : List α) (i n : ℕ)
    (h1 : ((l.drop i).take n).all p = true) (h2 : (l.drop (i + n)).all p = true) :
    (l.drop i).all p = true := by
  have e : (l.drop i).take n ++ l.drop (i + n) = l.drop i := by
    rw [← List.drop_drop]
    exact List.take_append_drop n (l.drop i)
  rw [← e, List.all_append, h1, h2]
  rfl

theorem all_first {α : Type} (p : α → Bool) (l : List α) (n : ℕ)
    (h1 : (l.take n).all p = true) (h2 : (l.drop n).all p = true) : l.all p = true := by
  have e : l.take n ++ l.drop n = l := List.take_append_drop n l
  rw [← e, List.all_append, h1, h2]
  rfl

theorem all_next {α : Type} (p : α → Bool) (l : List α) (i n j : ℕ) (hj : i + n = j)
    (h1 : ((l.drop i).take n).all p = true) (h2 : (l.drop j).all p = true) :
    (l.drop i).all p = true := by
  subst hj
  exact all_chunk p l i n h1 h2

end Fast

open PEqualNP.CircuitLowerBounds

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

set_option maxRecDepth 100000 in
theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

set_option maxRecDepth 100000 in
theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

set_option maxRecDepth 100000 in
theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 100000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 256 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 256)
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

set_option maxRecDepth 100000 in
theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 256) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

set_option maxRecDepth 100000 in
private theorem read_bit (w : List W) (i : ℕ) (k : Fin 256) :
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

set_option maxRecDepth 100000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 256) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#256)[k.val] = false; simp
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

set_option maxRecDepth 100000 in
theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k (~~~goal)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (~~~goal) := by
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
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩

def F (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 3) || (x 1 && x 3) || (x 0 && x 4) || (x 2 && x 4) || (x 3 && x 4) || (x 1 && x 5) || (x 2 && x 5) || (x 3 && x 5) || (x 4 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)

theorem bound_from_search (inputs : List W) (width : inputs.length = 7)
    (noSmall : ∀ t, (t = goal ∨ t = ~~~goal) → build basicOps t 10 inputs.toFinset → False)
    (sample : ∀ k : Fin 256, F (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = F x) :
    10 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 256) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 7) : Bool := bit k (inputs.getD i.val 0)
    have same : List.ofFn x = inputs.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < inputs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (inputs.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample k
  obtain ⟨t, ht, run⟩ := compile gs o hg inputs inputs.toFinset init evaluate
  have lift {a c : ℕ} (h : a ≤ c) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t c inputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact noSmall t ht (lift low run)

-- The root sample includes every assignment. Its pairs rule out consuming both inputs of the first live step.
def rows : List W :=
  [0x2a905520d482a91520b4814900149fffeaaaaaaad555557aaab556af801cd, 0x330466089823305608d8258488ea0ffff33333336666665cccd99f35c8ea2, 0x3c017802e00bc03802e00e0352f04ffffc3c3c3c7878786f0f1e1bc712f14, 0x18003000c00200300080253006fffffc03fc07f807f8ff01fe3f9c1407, 0x6000c003000400c0030040c090fffffffc0007fff800fffe003fe05898, 0x18003000c001803000c00820000fffffffffff8000000ffffffc0026120, 0x200040010002004001001000000ffffffffffffffffff00000000038240]

def lowRows : List W :=
  [0x609044a0888b244ca2e489945a47249363b1dde3bbc100040fe00081fa0301ff, 0x2432086411060e2c7181c58e34150f8a7c3e1efc3f800207f00040fe0403ff80, 0x8024804902040a30410146082418090c803fe0ffc3c003f800007f0007fc01ff, 0x49000092200930408226081042623010ffc000fffc01fc00003f800007fffe00, 0x12091000001040810408102080804020ffffff00003e0000003ffffff8000000, 0x208102081020410100804000000000003fffffffc0000000000000]

def highRows : List W :=
  [0x415a2a5468a97524d554b51b4b4a5253c77878f1e1e3fc005041f40b030240ff, 0xc82aa46daa919072e34e685c191f8acaf87f80fffe03c010607e080c03ff80c0, 0x333648ccd92020f184201d0c0ac302007fff01fffc00007f80000ffc03ff00, 0x92000001110200530208486010110c8cff800001fffff81f80000ff00003ffff, 0x24444080000005840410858262601010fffffffe000007e000000ffffffc0000, 0x208082102008080202000000000000007fffffff00000000000]

def universalRows : List W :=
  [0x8d152e3455598586e2e2219898e38a33bc3c7ff0ff1d0102c0c000903fe703f, 0x43552325546ca24270a4b51e4b4a94d2c3fc078ff0fe2000300ff40e03039fc0, 0x199b24e664900e17470685b1c1be28a03fff80fff0000203ff0080ffc03e000, 0x90000008888000a1804048601011430cfc00000fffffc03fc0000ff00003ffff, 0x22220400000023020080858462600410fffffff000003fc000000ffffffc0000, 0x1c1c0b0b0200808008200000000000003ffffffff00000000000]

-- For each deleted vertex, the bytes index the root samples in the order used by its six-variable search.
def projectionCodes : List ℕ :=
  [0xe3e6f0e7e5eee7e5ecffe4f0e7e3eee7e3ecffe7eeecffffe6e4f0e5e3eee5e3ecffe5eeecffe3eeecffe9e7e6e4f0e6e9e7e6e5e4f0e4e9e7e6e4e3f0f0e9e7e6e4f0eee9e7e6e4f0ece6e9e7e6e5e4f0e4e9e7e6e4e3f0f0e9e7e6e4f0eee9e7e6e4f0ece4e6e9e7e6e5e4e3f0e6f0e9e7e6e5e4f0eee4f0e9e7e6e4e3f0ec302e2e2c2c2c2a2a2a0e2727252525232323211f1f1f0d051c1c1c1a1a1a1818180c0b0b0b040a0a0a121111111111454343434343433f3b3b3b3b3b3b091010101010100f0f0f0f0f0f2a0e0e0e0e0e0e252121212121211f0d0d0d0d0d0d0505050505051a180c0c0c0c0c0c0c0b0b040404040404040a0a12121212121212,
   0xe3e8efe5e7eee5e7ebffe4efe5e3eee5e3ebffe5eeebffffe8e4efe7e3eee7e3ebffe7eeebffe3eeebffe9e5e8e4efe8e9e5e8e7e4efe4e9e5e8e4e3efefe9e5e8e4efeee9e5e8e4efebe8e9e5e8e7e4efe4e9e5e8e4e3efefe9e5e8e4efeee9e5e8e4efebe4e8e9e5e8e7e4e3efe8efe9e5e8e7e4efeee4efe9e5e8e4e3efeb302d2d2c2c2c2929290e1b1b1a1a1a1717170c1515150403262626252525222222210808080d020202004343434343531111111111113f3b3b3b3b3b3b39101010101010060606060606290e0e0e0e0e0e1a0c0c0c0c0c0c1504040404040403030303030325222121212121212108080d0d0d0d0d0d0d020200000000000000,
   0xe7e6ede3e5ebe3e5ecffe8ede3e7ebe3e7ecffe3ebecffffe6e8ede5e7ebe5e7ecffe5ebecffe7ebecffe9e3e6e8ede6e9e3e6e5e8ede8e9e3e6e8e7edede9e3e6e8edebe9e3e6e8edece6e9e3e6e5e8ede8e9e3e6e8e7edede9e3e6e8edebe9e3e6e8edece8e6e9e3e6e5e8e7ede6ede9e3e6e5e8edebe8ede9e3e6e8e7edec3019191717171818180c24242222222323232113131300122b2b2b2929292a2a2a0e070707031e1e1e053b3b3b3b3b4543434343434353111111111111380606060606060f0f0f0f0f0f180c0c0c0c0c0c2221212121212113000000000000121212121212292a0e0e0e0e0e0e0e0707030303030303031e1e05050505050505,
   0xe6ede7e5ece7e5ebffe8f0efede7f1eeece7f1eeebf0efffe7f1ecebf0edffe6f0efede5f1eeece5f1eeebf0efffe5f1ecebefedffe8e9e8e7e6f1e6e9e8e6e5f1f1f0efe9e8e6f1eeede9e8e6f1ece9e8e6f1ebe6e8e9e8e7e6e5f1f1f0e8efe9e8e7e6f1eee8ede9e8e7e6f1ecf1e6f0efe9e8e6e5f1eee6ede9e8e6e5f1eb2b2b2a2a2a2929290e202020201f1f1f1f080808080d0d0d1e1e1e1e050505161616160b0b0b0b15151515040404070707070303035311111111114543434343433a09391010101010380f0f0f0f0f06060606062a290e0e0e0e0e0e201f08080d0d0d0d0d0d1e1e050505050505160b0b150404040404040707030303030303,
   0xe4efe7e3eee7e3ebffe8f0edefe7f1eceee7f1ecebf0edffe7f1eeebf0efffe4f0edefe3f1eceee3f1ecebf0edffe3f1eeebedefffe8e9e8e7e4f1e4e9e8e4e3f1f1f0ede9e8e4f1ecefe9e8e4f1eee9e8e4f1ebe4e8e9e8e7e4e3f1f1f0e8ede9e8e7e4f1ece8efe9e8e7e4f1eef1e4f0ede9e8e4e3f1ece4efe9e8e4e3f1eb262625252522222221202020201f1f1f1f1e1e1e1e050505080808080d0d0d141414140a0a0a0a13131313121212020202020000005311111111113f3b3b3b3b3b3a09380f0f0f0f0f39101010101006060606062522212121212121201f1e1e05050505050508080d0d0d0d0d0d140a0a131212121212120202000000000000,
   0xe6f0e3e5ece3e5eeffe4edeff0e3f1ebece3f1ebeeedefffe3f1eceeedf0ffe6edeff0e5f1ebece5f1ebeeedefffe5f1eceeeff0ffe4e9e4e3e6f1e6e9e4e6e5f1f1edefe9e4e6f1ebf0e9e4e6f1ece9e4e6f1eee6e4e9e4e3e6e5f1f1ede4efe9e4e3e6f1ebe4f0e9e4e3e6f1ecf1e6edefe9e4e6e5f1ebe6f0e9e4e6e5f1ee1c1c1818181a1a1a0c1414141413131313020202020000000a0a0a0a1212121616161607070707151515150303030b0b0b0b0404043f3b3b3b3b3b4543434343433a38390606060606090f0f0f0f0f1010101010181a0c0c0c0c0c0c141302020000000000000a0a121212121212160707150303030303030b0b040404040404,
   0xe3ece5e3ebffe6f0efede5f1eeece5f1eeebf0efffe5f1ecebefedffe4f0efede3f1eeece3f1eeebe3f1ecebf0edffefedffe6e8e8e7e6e5e4f1e4e8e8e7e6e4e3f1f1f0e8efe8e7e6e4f1eee8ede8e7e6e4f1ece4e6e8e6e5e4e3f1f1e6f0efe8e6e5e4f1eee6ede8e6e5e4f1ebf1e4f0e4efede8e6e4e3f1ece8e6e4e3f1eb18181717170c161616160b0b0b0b1515151504040407070707030303141414140a0a0a0a02020202131313131212120000002a290e0e0e0e0e0e2522212121212121201f08080d0d0d0d0d0d1e1e0505050505051a180c0c0c0c0c0c160b0b150404040404040707030303030303140a0a020213121212121212000000000000]

def packBits (f : ℕ → Bool) (start : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => (if f start then 1 else 0) ||| (packBits f (start + 1) n <<< 1)

theorem packBits_spec (f : ℕ → Bool) (start n i : ℕ) (hi : i < n) :
    (packBits f start n).testBit i = f (start + i) := by
  induction i generalizing start n with
  | zero =>
    cases n with
    | zero => omega
    | succ n =>
      simp only [packBits, Nat.testBit_or, Nat.testBit_shiftLeft]
      cases f start <;> simp
  | succ i ih =>
    cases n with
    | zero => omega
    | succ n =>
      have hlow : (if f start then 1 else 0 : ℕ).testBit (i + 1) = false := by
        cases f start <;> simp [Nat.testBit_succ]
      simp only [packBits, Nat.testBit_or, hlow, Bool.false_or, Nat.testBit_shiftLeft]
      have hn : i < n := by omega
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using ih (start + 1) n hn

def projectIndex (i : Fin 7) (j : ℕ) : ℕ :=
  (projectionCodes.getD i.val 0 >>> (8 * j)) % 256

def project (i : Fin 7) (w : W) : W :=
  BitVec.ofNat 256 (packBits (fun j => w.getLsbD (projectIndex i j)) 0 256)

theorem project_bit (i : Fin 7) (w : W) (j : Fin 256) :
    (project i w)[j.val] = w.getLsbD (projectIndex i j.val) := by
  rw [← BitVec.getLsbD_eq_getElem j.isLt, project, BitVec.getLsbD_ofNat,
      packBits_spec _ _ _ _ j.isLt]
  simp only [j.isLt, decide_true, Bool.true_and, Nat.zero_add]

theorem project_bound (i : Fin 7) (j : ℕ) : projectIndex i j < 256 := Nat.mod_lt _ (by decide)

theorem project_and (i : Fin 7) (a b : W) : project i (a &&& b) = project i a &&& project i b := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  rw [project_bit i _ ⟨j, hj⟩, BitVec.getElem_and, project_bit i a ⟨j, hj⟩,
    project_bit i b ⟨j, hj⟩, BitVec.getLsbD_and]

theorem project_or (i : Fin 7) (a b : W) : project i (a ||| b) = project i a ||| project i b := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  rw [project_bit i _ ⟨j, hj⟩, BitVec.getElem_or, project_bit i a ⟨j, hj⟩,
    project_bit i b ⟨j, hj⟩, BitVec.getLsbD_or]

theorem project_not (i : Fin 7) (a : W) : project i (~~~a) = ~~~project i a := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  rw [project_bit i _ ⟨j, hj⟩, BitVec.getElem_not, project_bit i a ⟨j, hj⟩]
  simp only [BitVec.getLsbD_not, project_bound, decide_true, Bool.true_and]

def minorRows (i : Fin 7) : List W :=
  if i.val < 3 then lowRows else if i.val < 6 then highRows else universalRows

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem project_goal : ∀ i : Fin 7, project i goal = goal := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem project_zero : ∀ i : Fin 7, project i (rows.getD i.val 0) = 0 := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem project_initial : ∀ (i j : Fin 7),
    project i (rows.getD j.val 0) = 0 ∨ project i (rows.getD j.val 0) ∈ minorRows i := by
  decide +kernel

theorem extend {g : W} {av : Finset W} {l k : ℕ} (le : l ≤ k)
    (run : build basicOps g l av) : build basicOps g k av := by
  induction le with
  | refl => exact run
  | step _ ih => exact Or.inl ih

def projectedBuild (i : Fin 7) (g : W) (k : ℕ) (av : Finset W) : Prop :=
  ∃ t, (t = project i g ∨ t = ~~~project i g) ∧ build basicOps t k av

theorem projectedExtend {i : Fin 7} {g : W} {av : Finset W} {l k : ℕ} (le : l ≤ k)
    (run : projectedBuild i g l av) : projectedBuild i g k av := by
  obtain ⟨t, ht, hb⟩ := run
  exact ⟨t, ht, extend le hb⟩

theorem project_reach (i : Fin 7) {a b z : W} {A : Finset W}
    (hz : z ∈ basicOps a b) (ha : holds A (project i a)) (hb : holds A (project i b)) :
    reachable A (project i z) := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl <;> simp only [project_and, project_or, project_not]
  · exact and_reach ha hb
  · exact or_reach ha hb
  · exact and_reach ha (holds_not hb)
  · exact and_reach hb (holds_not ha)

theorem project_step_free (i : Fin 7) {a b z : W} {A : Finset W}
    (hz : z ∈ basicOps a b) (ha : holds A (project i a)) (hb : holds A (project i b))
    (hzero : project i a = 0 ∨ project i b = 0) : holds A (project i z) := by
  have zero : holds A (0 : W) := .inl rfl
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl <;>
    rcases hzero with h | h <;>
    simp only [project_and, project_or, project_not, h,
      show ∀ x : W, (0 : W) &&& x = 0 from fun x => BitVec.zero_and,
      show ∀ x : W, x &&& (0 : W) = 0 from fun x => BitVec.and_zero,
      show ∀ x : W, (0 : W) ||| x = x from fun x => BitVec.zero_or,
      show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
      show ∀ x : W, x &&& ~~~(0 : W) = x from fun x => BitVec.and_allOnes] <;>
    first | exact zero | exact ha | exact hb

theorem project_singleton (i : Fin 7) {g : W} {A : Finset W}
    (h : holds A (project i g)) (h0 : project i g ≠ 0) (h1 : project i g ≠ ~~~0) :
    projectedBuild i g 0 A := by
  rcases h with h | h | ⟨t, ht, e | e⟩
  · exact (h0 h).elim
  · exact (h1 h).elim
  · exact ⟨t, .inl e.symm, ht⟩
  · exact ⟨t, .inr (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) e.symm), ht⟩

-- Restriction preserves the available binary operations. A constant live wire saves one step
-- when the run first consumes it.
theorem project_live (i : Fin 7) {g : W} (h0 : project i g ≠ 0) (h1 : project i g ≠ ~~~0)
    {k : ℕ} {s A : Finset W} (h : live basicOps g k s)
    (initial : ∀ w ∈ s, holds A (project i w)) :
    projectedBuild i g k A ∧
      ((∃ w ∈ s, project i w = 0) → projectedBuild i g (k - 1) A) := by
  induction k generalizing s A with
  | zero =>
    change s = {g} at h
    subst s
    have run := project_singleton i (initial g (by simp)) h0 h1
    exact ⟨run, fun _ => run⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, hs, tail⟩
    · obtain ⟨run, save⟩ := ih skip initial
      exact ⟨projectedExtend (by omega) run, fun h => projectedExtend (by omega) (save h)⟩
    have restMem (w : W) (hw : w ∈ rest) : w ∈ s := hs.symm ▸
      Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw)
    have next (B : Finset W) (hrest : ∀ w ∈ rest, holds B (project i w))
        (hzB : holds B (project i z)) :
        ∀ w ∈ insert z rest, holds B (project i w) := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact hzB
      · exact hrest w hw
    have step := project_reach i hz (initial a ha) (initial b hb)
    have continuation (m : ℕ)
        (short : ∀ B, (∀ w ∈ insert z rest, holds B (project i w)) → projectedBuild i g m B) :
        projectedBuild i g (m + 1) A := by
      rcases step with old | ⟨u, hu, v, hv, hne, n, hop, hn⟩
      · exact projectedExtend (by omega)
          (short A (next A (fun w hw => initial w (restMem w hw)) old))
      · obtain ⟨t, ht, hr⟩ := short (insert n A)
          (next _ (fun w hw => holds_insert (initial w (restMem w hw))) hn)
        exact ⟨t, ht, Or.inr ⟨u, hu, v, hv, hne, n, hop, hr⟩⟩
    refine ⟨continuation k (fun B hB => (ih tail hB).1), ?_⟩
    rintro ⟨w, hw, hw0⟩
    rw [hs, Finset.mem_insert, Finset.mem_insert] at hw
    have free (hz0 : project i a = 0 ∨ project i b = 0) :
        projectedBuild i g k A :=
      (ih tail (next A (fun x hx => initial x (restMem x hx))
        (project_step_free i hz (initial a ha) (initial b hb) hz0))).1
    rcases hw with rfl | rfl | hw
    · exact free (.inl hw0)
    · exact free (.inr hw0)
    · cases k with
      | zero =>
        change insert z rest = {g} at tail
        have e : w = g := Finset.mem_singleton.mp (tail ▸ Finset.mem_insert_of_mem hw)
        exact (h0 (e ▸ hw0)).elim
      | succ l =>
        exact continuation l (fun B hB => (ih tail hB).2
          ⟨w, Finset.mem_insert_of_mem hw, hw0⟩)

def rootWire (i : Fin 7) : W := rows.getD i.val 0

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem noDoubleDrop : ∀ (i j : Fin 7) (k : Fin 4), rootWire i ≠ rootWire j →
    cuts ((ops (rootWire i) (rootWire j)).getD k.val 0 ::
      rows.filter (fun w => w != rootWire i && w != rootWire j)) ≠ -1 := by
  decide +kernel

theorem rootNotTarget : ∀ i : Fin 7, rootWire i ≠ goal ∧ rootWire i ≠ ~~~goal := by
  decide +kernel

theorem root_index {w : W} (hw : w ∈ rows.toFinset) : ∃ i : Fin 7, rootWire i = w := by
  obtain ⟨i, hi, he⟩ := List.getElem_of_mem (List.mem_toFinset.mp hw)
  have hir : i < 7 := hi
  exact ⟨⟨i, hir⟩, by
    change rows.getD i 0 = w
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] using he⟩

theorem cuts_full_of_subset {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {s : Finset W}
    {ws : List W} (h : live basicOps g k s) (ss : s ⊆ ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  obtain ⟨w, hw, good⟩ := live_separates (differs ⟨j, hj⟩) (hd ⟨j, hj⟩) (ops_differs ⟨j, hj⟩) h
  have hb := (cuts_spec ws ⟨j, hj⟩).mpr ⟨w, List.mem_toFinset.mp (ss hw), good⟩
  change (cuts ws)[j] = (BitVec.allOnes 128)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hb

theorem root_retains {g a b z : W} {s rest : Finset W} (hg : g = goal ∨ g = ~~~goal)
    (hs : s ⊆ rows.toFinset) (ha : a ∈ s) (hb : b ∈ s) (hne : a ≠ b)
    (hz : z ∈ basicOps a b) (e : s = insert a (insert b rest))
    (tail : live basicOps g 9 (insert z rest)) : a ∈ rest ∨ b ∈ rest := by
  by_contra! h
  obtain ⟨i, rfl⟩ := root_index (hs ha)
  obtain ⟨j, rfl⟩ := root_index (hs hb)
  obtain ⟨l, hlt, he⟩ := List.getElem_of_mem (List.mem_toFinset.mp hz)
  have hl : l < 4 := hlt
  have hval : (ops (rootWire i) (rootWire j)).getD l 0 = z := by
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt] using he
  have hc := noDoubleDrop i j ⟨l, hl⟩ hne
  change cuts ((ops (rootWire i) (rootWire j)).getD l 0 ::
    rows.filter (fun w => w != rootWire i && w != rootWire j)) ≠ -1 at hc
  apply hc
  rw [hval]
  apply cuts_full_of_subset hg tail
  intro w hw
  apply List.mem_toFinset.mpr
  rcases Finset.mem_insert.mp hw with rfl | hw
  · exact List.mem_cons_self
  · apply List.mem_cons_of_mem
    refine List.mem_filter.mpr ⟨List.mem_toFinset.mp (hs ?_), ?_⟩
    · exact e.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw)
    · have ha' : w ≠ rootWire i := fun eq => h.1 (eq ▸ hw)
      have hb' : w ≠ rootWire j := fun eq => h.2 (eq ▸ hw)
      simp [ha', hb']

-- Restrict a retained input of the first step. The first operation collapses immediately,
-- and the retained constant saves a second step in the rest of the run.
theorem noSmall (minor : ∀ i : Fin 7, ∀ t, (t = goal ∨ t = ~~~goal) →
    build basicOps t 8 (minorRows i).toFinset → False)
    (g : W) (hg : g = goal ∨ g = ~~~goal) (h : build basicOps g 10 rows.toFinset) : False := by
  obtain ⟨s, hs, hl⟩ := compress h
  rcases first_live hl with done | ⟨a, ha, b, hb, hne, z, hz, _, rest, e, tail⟩
  · have hm : g ∈ rows.toFinset := hs (by simp [done])
    obtain ⟨i, hi⟩ := root_index hm
    rcases hg with rfl | rfl
    · exact (rootNotTarget i).1 hi
    · exact (rootNotTarget i).2 hi
  · have hret := root_retains hg hs ha hb hne hz e tail
    obtain ⟨i, hi, hold, harg⟩ : ∃ (i : Fin 7) (w : W),
        w ∈ rest ∧ (w = a ∨ w = b) ∧ rootWire i = w := by
      rcases hret with h | h
      · obtain ⟨i, hi⟩ := root_index (hs ha)
        exact ⟨i, a, h, .inl rfl, hi⟩
      · obtain ⟨i, hi⟩ := root_index (hs hb)
        exact ⟨i, b, h, .inr rfl, hi⟩
    rcases harg with ⟨harg, hw⟩
    let A := (minorRows i).toFinset
    have initial (v : W) (hv : v ∈ s) : holds A (project i v) := by
      obtain ⟨j, rfl⟩ := root_index (hs hv)
      rcases project_initial i j with zero | row
      · exact .inl zero
      · exact .inr (.inr ⟨_, List.mem_toFinset.mpr row, .inl rfl⟩)
    have hzero : project i hi = 0 := hw ▸ project_zero i
    have hz0 : project i a = 0 ∨ project i b = 0 := by
      rcases harg with rfl | rfl
      · exact .inl hzero
      · exact .inr hzero
    have hnew : ∀ w ∈ insert z rest, holds A (project i w) := by
      intro w hm
      rcases Finset.mem_insert.mp hm with rfl | hm
      · exact project_step_free i hz (initial a ha) (initial b hb) hz0
      · exact initial w (e.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    have hproj : project i g = goal ∨ project i g = ~~~goal := by
      rcases hg with rfl | rfl
      · exact .inl (project_goal i)
      · exact .inr (by rw [project_not, project_goal])
    have h0 : project i g ≠ 0 := by
      rcases hproj with h | h <;> rw [h] <;> decide
    have h1 : project i g ≠ ~~~0 := by
      rcases hproj with h | h <;> rw [h] <;> decide
    obtain ⟨t, ht, hb⟩ := (project_live i h0 h1 tail hnew).2
      ⟨hi, Finset.mem_insert_of_mem hold, hzero⟩
    have ht' : t = goal ∨ t = ~~~goal := by
      rcases hproj with h | h
      · simpa only [h] using ht
      · rw [h, BitVec.not_not] at ht
        exact ht.symm
    exact minor i t ht' hb

def lowChildren : List (List ℕ) := allKids 7 (lowRows.map BitVec.toNat)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem lowCheck0 :
    ((lowChildren.drop 0).take 10).all (dead 7) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem lowCheck10 :
    ((lowChildren.drop 10).take 13).all (dead 7) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem lowCheck23 :
    ((lowChildren.drop 23).take 5).all (dead 7) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem lowCheck28 :
    ((lowChildren.drop 28).take 15).all (dead 7) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem lowCheck43 :
    ((lowChildren.drop 43).take 15).all (dead 7) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem lowCheck58 :
    ((lowChildren.drop 58).take 6).all (dead 7) = true := by
  decide +kernel

private theorem lowTail : (lowChildren.drop 64).all (dead 7) = true := by decide +kernel

theorem lowReject : lowChildren.all (dead 7) = true := by

  apply all_first _ _ 10 lowCheck0

  apply all_next _ _ 10 13 23 rfl lowCheck10

  apply all_next _ _ 23 5 28 rfl lowCheck23

  apply all_next _ _ 28 15 43 rfl lowCheck28

  apply all_next _ _ 43 15 58 rfl lowCheck43

  apply all_next _ _ 58 6 64 rfl lowCheck58

  exact lowTail


theorem lowBound : ∀ t, (t = goal ∨ t = ~~~goal) → build basicOps t 8 lowRows.toFinset → False :=
  refute 7 lowRows (by decide +kernel) (by decide +kernel) lowReject

def highChildren : List (List ℕ) := allKids 7 (highRows.map BitVec.toNat)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem highCheck0 :
    ((highChildren.drop 0).take 7).all (dead 7) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem highCheck7 :
    ((highChildren.drop 7).take 9).all (dead 7) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem highCheck16 :
    ((highChildren.drop 16).take 6).all (dead 7) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem highCheck22 :
    ((highChildren.drop 22).take 5).all (dead 7) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem highCheck27 :
    ((highChildren.drop 27).take 6).all (dead 7) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem highCheck33 :
    ((highChildren.drop 33).take 6).all (dead 7) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem highCheck39 :
    ((highChildren.drop 39).take 9).all (dead 7) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem highCheck48 :
    ((highChildren.drop 48).take 6).all (dead 7) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem highCheck54 :
    ((highChildren.drop 54).take 8).all (dead 7) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem highCheck62 :
    ((highChildren.drop 62).take 6).all (dead 7) = true := by
  decide +kernel

private theorem highTail : (highChildren.drop 68).all (dead 7) = true := by decide +kernel

theorem highReject : highChildren.all (dead 7) = true := by

  apply all_first _ _ 7 highCheck0

  apply all_next _ _ 7 9 16 rfl highCheck7

  apply all_next _ _ 16 6 22 rfl highCheck16

  apply all_next _ _ 22 5 27 rfl highCheck22

  apply all_next _ _ 27 6 33 rfl highCheck27

  apply all_next _ _ 33 6 39 rfl highCheck33

  apply all_next _ _ 39 9 48 rfl highCheck39

  apply all_next _ _ 48 6 54 rfl highCheck48

  apply all_next _ _ 54 8 62 rfl highCheck54

  apply all_next _ _ 62 6 68 rfl highCheck62

  exact highTail


theorem highBound : ∀ t, (t = goal ∨ t = ~~~goal) → build basicOps t 8 highRows.toFinset → False :=
  refute 7 highRows (by decide +kernel) (by decide +kernel) highReject

def universalChildren : List (List ℕ) := allKids 7 (universalRows.map BitVec.toNat)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem universalCheck0 :
    ((universalChildren.drop 0).take 18).all (dead 7) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem universalCheck18 :
    ((universalChildren.drop 18).take 13).all (dead 7) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem universalCheck31 :
    ((universalChildren.drop 31).take 10).all (dead 7) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem universalCheck41 :
    ((universalChildren.drop 41).take 12).all (dead 7) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem universalCheck53 :
    ((universalChildren.drop 53).take 11).all (dead 7) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem universalCheck64 :
    ((universalChildren.drop 64).take 2).all (dead 7) = true := by
  decide +kernel

private theorem universalTail : (universalChildren.drop 66).all (dead 7) = true := by decide +kernel

theorem universalReject : universalChildren.all (dead 7) = true := by

  apply all_first _ _ 18 universalCheck0

  apply all_next _ _ 18 13 31 rfl universalCheck18

  apply all_next _ _ 31 10 41 rfl universalCheck31

  apply all_next _ _ 41 12 53 rfl universalCheck41

  apply all_next _ _ 53 11 64 rfl universalCheck53

  apply all_next _ _ 64 2 66 rfl universalCheck64

  exact universalTail


theorem universalBound : ∀ t, (t = goal ∨ t = ~~~goal) → build basicOps t 8 universalRows.toFinset → False :=
  refute 7 universalRows (by decide +kernel) (by decide +kernel) universalReject

theorem rejectMinor (i : Fin 7) : ∀ t, (t = goal ∨ t = ~~~goal) →
    build basicOps t 8 (minorRows i).toFinset → False := by
  unfold minorRows
  split
  · exact lowBound
  · split
    · exact highBound
    · exact universalBound

set_option maxRecDepth 8000 in
theorem bound (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = F x) : 10 < binaryCost gs :=
  bound_from_search rows rfl (noSmall rejectMinor) (by decide +kernel) gs o hg he

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem bridge : ∀ x : Fin 7 → Bool, decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 3, 4, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 3, 4, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 3, 4, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) = F x := by
  decide +kernel

def wg : List Gate :=
  [⟨.or, [0, 5]⟩,
   ⟨.or, [1, 4]⟩,
   ⟨.and, [8, 7]⟩,
   ⟨.or, [9, 2]⟩,
   ⟨.or, [10, 3]⟩,
   ⟨.or, [6, 5]⟩,
   ⟨.or, [12, 4]⟩,
   ⟨.and, [13, 11]⟩,
   ⟨.or, [8, 7]⟩,
   ⟨.or, [3, 6]⟩,
   ⟨.and, [16, 15]⟩,
   ⟨.or, [17, 14]⟩]

theorem wfits : ∀ g ∈ wg, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem weval : ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 3, 4, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 3, 4, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 3, 4, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  have h : ∀ x : Fin 7 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = F x := by
    decide +kernel
  exact fun x => (h x).trans (bridge x).symm

end PEqualNP.Outside.L_meta_10566

theorem PEqualNP.Outside.L_meta_10566 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 3, 4, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 3, 4, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 3, 4, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 3, 4, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 3, 4, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 3, 4, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fits _ computes
  by_cases hasNot : ∃ g ∈ gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : PEqualNP.Outside.L_meta_10566.binaryCost gates < gates.length :=
      (List.length_filter_lt_length_iff_exists (p := PEqualNP.Outside.L_meta_10566.isBinary)).mpr
        ⟨g, mem, by simp [PEqualNP.Outside.L_meta_10566.isBinary, op]⟩
    have hb := PEqualNP.Outside.L_meta_10566.bound gates o (fun g hg => fits g hg) (fun x => (computes x).trans (PEqualNP.Outside.L_meta_10566.bridge x))
    have hl : PEqualNP.Outside.L_meta_10566.wg.length = 12 := rfl
    exact ⟨PEqualNP.Outside.L_meta_10566.wg, 18, PEqualNP.Outside.L_meta_10566.wfits, by omega, PEqualNP.Outside.L_meta_10566.weval⟩
  · refine ⟨gates, o, fun g hg => ⟨?_, (fits g hg).2⟩, le_refl _, computes⟩
    rcases (fits g hg).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hasNot ⟨g, hg, h⟩).elim
