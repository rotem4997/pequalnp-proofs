import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_16767

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace Core

abbrev Sig := BitVec 64
abbrev Row := Fin 64

def zero : Sig := 0
def one : Sig := BitVec.allOnes 64
def neg (a : Sig) : Sig := ~~~a

def bin (d : Nat) (a b : Sig) : Sig :=
  if d = 0 then a &&& b
  else if d = 1 then a ||| b
  else if d = 2 then a &&& ~~~b
  else ~~~a &&& b

def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def properB (a : Sig) : Bool := a != zero && a != one

theorem proper_of {a : Sig} (h : properB a = true) : proper a := by
  simpa only [properB, proper, Bool.and_eq_true, bne_iff_ne] using h

def allowed (u : Bool) (d : Nat) : Prop := d < 2 ∨ (u = true ∧ d < 4)

theorem allowed_four {u d} (h : allowed u d) :
    d = 0 ∨ d = 1 ∨ (u = true ∧ d = 2) ∨ (u = true ∧ d = 3) := by
  rcases h with h | ⟨hu, hd⟩
  · omega
  · have : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl ⟨hu, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hu, rfl⟩))

def bit (i : Row) (a : Sig) : Bool := a.getLsbD i.val

theorem bit_zero (i : Row) : bit i zero = false := by simp [bit, zero]
theorem bit_one (i : Row) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
theorem bit_neg (i : Row) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit, neg, i.isLt]
theorem bit_and (i : Row) (a b : Sig) : bit i (a &&& b) = (bit i a && bit i b) := by simp [bit]
theorem bit_or (i : Row) (a b : Sig) : bit i (a ||| b) = (bit i a || bit i b) := by simp [bit]

theorem bit_bin (i : Row) (d : Nat) (a b : Sig) :
    bit i (bin d a b) =
      if d = 0 then bit i a && bit i b
      else if d = 1 then bit i a || bit i b
      else if d = 2 then bit i a && !(bit i b)
      else !(bit i a) && bit i b := by
  unfold bin
  split_ifs <;> simp [bit, i.isLt]

theorem bit_ext {a b : Sig} (h : ∀ i : Row, bit i a = bit i b) : a = b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j, hj⟩

def nrm (u : Bool) (a : Sig) : Sig := if u && bit 0 a then neg a else a
theorem nrm_false (a : Sig) : nrm false a = a := rfl
theorem nrm_id {u} {a : Sig} (h : bit 0 a = false) : nrm u a = a := by simp [nrm, h]
theorem neg_neg' (a : Sig) : neg (neg a) = a := by simp [neg]

theorem nrm_neg (a : Sig) : nrm true (neg a) = nrm true a := by
  cases h : bit 0 a <;> simp [nrm, bit_neg, h, neg_neg']

theorem proper_neg {a : Sig} (h : proper (neg a)) : proper a := by
  refine ⟨fun e => h.2 ?_, fun e => h.1 ?_⟩
  · subst e; exact bit_ext fun i => by rw [bit_neg, bit_zero, bit_one]; rfl
  · subst e; exact bit_ext fun i => by rw [bit_neg, bit_one, bit_zero]; rfl

theorem proper_nrm {u} {a : Sig} (h : proper (nrm u a)) : proper a := by
  unfold nrm at h
  split at h
  · exact proper_neg h
  · exact h

def Live (u : Bool) (target : Sig) : Nat → Finset Sig → Prop
  | 0, S => S = {target} ∧ proper target
  | k + 1, S =>
      ∃ (U : Finset Sig) (a b : Sig) (d : Nat), allowed u d ∧
        S = insert a (insert b U) ∧ proper a ∧ proper b ∧ a ≠ b ∧
        bin d a b ∉ insert a (insert b U) ∧ Live u target k (insert (bin d a b) U)

theorem Live.stop {u target} (hp : proper target) : Live u target 0 {target} := ⟨rfl, hp⟩

theorem Live.binary {u target k U a b d} (hd : allowed u d) (ha : proper a) (hb : proper b)
    (hab : a ≠ b) (hfresh : bin d a b ∉ insert a (insert b U))
    (tail : Live u target k (insert (bin d a b) U)) :
    Live u target (k + 1) (insert a (insert b U)) :=
  ⟨U, a, b, d, hd, rfl, ha, hb, hab, hfresh, tail⟩

theorem Live.ind {u target} {motive : ∀ (k : Nat) (S : Finset Sig), Live u target k S → Prop}
    (stop : ∀ hp : proper target, motive 0 {target} (Live.stop hp))
    (binary : ∀ {k U a b d} (hd : allowed u d) (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)),
      motive k (insert (bin d a b) U) tail →
      motive (k + 1) (insert a (insert b U)) (Live.binary hd ha hb hab hfresh tail))
    {k S} (h : Live u target k S) : motive k S h := by
  induction k generalizing S with
  | zero => obtain ⟨rfl, hp⟩ := h; exact stop hp
  | succ k ih => obtain ⟨U, a, b, d, hd, rfl, ha, hb, hab, hf, tail⟩ := h; exact binary hd ha hb hab hf tail (ih tail)

theorem live_proper {u target k S} (h : Live u target k S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary _ ha hb _ _ _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha, hb, fun a h => ih a (Finset.mem_insert_of_mem h)⟩

theorem live_size {u target k S} (h : Live u target k S) : S.card ≤ k + 1 := by
  induction h using Live.ind with
  | stop _ => simp
  | @binary k U a b d _ _ _ _ hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

def prime (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b

theorem bit_prime (i : Row) (d : Bool) (a b : Sig) :
    bit i (prime d a b) = if d then bit i a || bit i b else bit i a && bit i b := by
  cases d <;> simp [prime, bit]

theorem bit_nrm_true (i : Row) (a : Sig) :
    bit i (nrm true a) = if bit 0 a then !(bit i a) else bit i a := by
  cases h : bit 0 a <;> simp [nrm, h, bit_neg]

theorem nrm_prime (d : Bool) (a b : Sig) :
    ∃ (k : Nat), k < 4 ∧ nrm true (prime d a b) = bin k (nrm true a) (nrm true b) := by
  cases d <;> cases ha : bit 0 a <;> cases hb : bit 0 b
  · exact ⟨0, by omega, bit_ext fun i => by rw [bit_nrm_true, bit_bin, bit_nrm_true, bit_nrm_true, bit_prime, bit_prime, ha, hb]; cases bit i a <;> cases bit i b <;> rfl⟩
  · exact ⟨2, by omega, bit_ext fun i => by rw [bit_nrm_true, bit_bin, bit_nrm_true, bit_nrm_true, bit_prime, bit_prime, ha, hb]; cases bit i a <;> cases bit i b <;> rfl⟩
  · exact ⟨3, by omega, bit_ext fun i => by rw [bit_nrm_true, bit_bin, bit_nrm_true, bit_nrm_true, bit_prime, bit_prime, ha, hb]; cases bit i a <;> cases bit i b <;> rfl⟩
  · exact ⟨1, by omega, bit_ext fun i => by rw [bit_nrm_true, bit_bin, bit_nrm_true, bit_nrm_true, bit_prime, bit_prime, ha, hb]; cases bit i a <;> cases bit i b <;> rfl⟩
  · exact ⟨1, by omega, bit_ext fun i => by rw [bit_nrm_true, bit_bin, bit_nrm_true, bit_nrm_true, bit_prime, bit_prime, ha, hb]; cases bit i a <;> cases bit i b <;> rfl⟩
  · exact ⟨3, by omega, bit_ext fun i => by rw [bit_nrm_true, bit_bin, bit_nrm_true, bit_nrm_true, bit_prime, bit_prime, ha, hb]; cases bit i a <;> cases bit i b <;> rfl⟩
  · exact ⟨2, by omega, bit_ext fun i => by rw [bit_nrm_true, bit_bin, bit_nrm_true, bit_nrm_true, bit_prime, bit_prime, ha, hb]; cases bit i a <;> cases bit i b <;> rfl⟩
  · exact ⟨0, by omega, bit_ext fun i => by rw [bit_nrm_true, bit_bin, bit_nrm_true, bit_nrm_true, bit_prime, bit_prime, ha, hb]; cases bit i a <;> cases bit i b <;> rfl⟩

def gv (w : List Sig) (g : Gate) : Sig :=
  match g.op with
  | .and => (g.inputs.map fun i => w.getD i zero).foldr (· &&& ·) one
  | .or => (g.inputs.map fun i => w.getD i zero).foldr (· ||| ·) zero
  | .not => neg ((g.inputs.map fun i => w.getD i zero).headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun w g => w ++ [gv w g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v
def Repr (u : Bool) (w : List Sig) (v : Sig) : Prop := represented w (nrm u v)

theorem bin_zero_l (d : Nat) (a : Sig) (hd : d < 4) :
    bin d zero a = if d = 0 ∨ d = 2 then zero else a := by
  apply bit_ext; intro i; rw [bit_bin, bit_zero]
  have : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;> simp [bit_zero]

theorem bin_zero_r (d : Nat) (a : Sig) (hd : d < 4) :
    bin d a zero = if d = 0 ∨ d = 3 then zero else a := by
  apply bit_ext; intro i; rw [bit_bin, bit_zero]
  have : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;> simp [bit_zero]

theorem bin_one_l (d : Nat) (a : Sig) (hd : d < 2) :
    bin d one a = if d = 0 then a else one := by
  apply bit_ext; intro i; rw [bit_bin, bit_one]
  have : d = 0 ∨ d = 1 := by omega
  rcases this with rfl | rfl <;> simp [bit_one]

theorem bin_one_r (d : Nat) (a : Sig) (hd : d < 2) :
    bin d a one = if d = 0 then a else one := by
  apply bit_ext; intro i; rw [bit_bin, bit_one]
  have : d = 0 ∨ d = 1 := by omega
  rcases this with rfl | rfl <;> simp [bit_one]

theorem bin_self (d : Nat) (a : Sig) (hd : d < 4) :
    bin d a a = if d < 2 then a else zero := by
  apply bit_ext; intro i; rw [bit_bin]
  have : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl
  · simp [Bool.and_self]
  · simp [Bool.or_self]
  · simp [bit_zero]
  · simp [bit_zero]

theorem operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ (a ∈ w ∧ proper a) := by
  by_cases hp : proper a
  · exact Or.inr (Or.inr ⟨h.resolve_right (fun hn => hn hp), hp⟩)
  · unfold proper at hp
    by_cases hz : a = zero
    · exact Or.inl hz
    · right; left; by_contra ho; exact hp ⟨hz, ho⟩

def witness (u : Bool) (w : List Sig) (z : Sig) : Prop :=
  represented w z ∨ ∃ a b d, allowed u d ∧ a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b

theorem not_proper_zero : ¬proper zero := fun h => h.1 rfl
theorem not_proper_one : ¬proper one := fun h => h.2 rfl

theorem bin_rep {u w a b} (d : Nat) (hd : allowed u d) (ha : represented w a) (hb : represented w b)
    (noOne : u = true → a ≠ one ∧ b ≠ one) : witness u w (bin d a b) := by
  have hd4 : d < 4 := by rcases hd with h | ⟨_, h⟩ <;> omega
  rcases operand_cases ha with rfl | rfl | ⟨am, pa⟩
  · rw [bin_zero_l d b hd4]; split_ifs
    · exact Or.inl (Or.inr not_proper_zero)
    · exact Or.inl hb
  · rcases allowed_four hd with rfl | rfl | ⟨hu, rfl⟩ | ⟨hu, rfl⟩
    · rw [bin_one_l 0 b (by omega)]; exact Or.inl hb
    · rw [bin_one_l 1 b (by omega)]; exact Or.inl (Or.inr not_proper_one)
    · exact absurd rfl (noOne hu).1
    · exact absurd rfl (noOne hu).1
  · rcases operand_cases hb with rfl | rfl | ⟨bm, pb⟩
    · rw [bin_zero_r d a hd4]; split_ifs
      · exact Or.inl (Or.inr not_proper_zero)
      · exact Or.inl ha
    · rcases allowed_four hd with rfl | rfl | ⟨hu, rfl⟩ | ⟨hu, rfl⟩
      · rw [bin_one_r 0 a (by omega)]; exact Or.inl ha
      · rw [bin_one_r 1 a (by omega)]; exact Or.inl (Or.inr not_proper_one)
      · exact absurd rfl (noOne hu).2
      · exact absurd rfl (noOne hu).2
    · by_cases hab : a = b
      · subst hab; rw [bin_self d a hd4]; split_ifs
        · exact Or.inl ha
        · exact Or.inl (Or.inr not_proper_zero)
      · exact Or.inr ⟨a, b, d, hd, am, bm, pa, pb, hab, rfl⟩

theorem norm_ne_one (a : Sig) : nrm true a ≠ one := by
  intro h
  have := congrArg (bit 0) h
  rw [bit_one, bit_nrm_true] at this
  cases ha : bit 0 a <;> simp [ha] at this

theorem prime_rep {u w a b} (d : Bool) (ha : Repr u w a) (hb : Repr u w b) :
    witness u w (nrm u (prime d a b)) := by
  cases u with
  | false =>
    cases d with
    | false =>
      have e : nrm false (prime false a b) = bin 0 (nrm false a) (nrm false b) := by simp [nrm, prime, bin]
      rw [e]; exact bin_rep 0 (Or.inl (by omega)) ha hb (fun h => Bool.noConfusion h)
    | true =>
      have e : nrm false (prime true a b) = bin 1 (nrm false a) (nrm false b) := by simp [nrm, prime, bin]
      rw [e]; exact bin_rep 1 (Or.inl (by omega)) ha hb (fun h => Bool.noConfusion h)
  | true =>
    obtain ⟨k, hk, heq⟩ := nrm_prime d a b
    rw [heq]
    exact bin_rep k (Or.inr ⟨rfl, hk⟩) ha hb (fun _ => ⟨norm_ne_one a, norm_ne_one b⟩)

theorem repr_const {u w} {v : Sig} (h : v = zero ∨ v = one) : Repr u w v := by
  apply Or.inr
  intro hp
  have hv := proper_nrm hp
  rcases h with rfl | rfl
  · exact hv.1 rfl
  · exact hv.2 rfl

theorem get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
  by_cases hi : i < w.length
  · left
    rw [List.getD_eq_getElem _ _ hi]
    exact List.mem_map_of_mem (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]
    exact repr_const (Or.inl rfl)

theorem repr_neg {w a} (h : Repr true w a) : Repr true w (neg a) := by
  unfold Repr; rw [nrm_neg]; exact h

def isNot (g : Gate) : Bool :=
  match g.op with
  | .not => true
  | _ => false

theorem and_one_r (a : Sig) : a &&& one = a :=
  bit_ext fun i => by rw [bit_and, bit_one, Bool.and_true]

theorem or_zero_r (a : Sig) : a ||| zero = a :=
  bit_ext fun i => by rw [bit_or, bit_zero, Bool.or_false]

theorem gate_rep (u : Bool) (w : List Sig) (g : Gate)
    (hop : (g.op = GateOp.and ∨ g.op = GateOp.or ∨ (u = true ∧ g.op = GateOp.not)) ∧ g.inputs.length ≤ 2) :
    (isNot g = true → Repr u (w.map (nrm u)) (gv w g)) ∧
    witness u (w.map (nrm u)) (nrm u (gv w g)) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨ho, hl⟩ := hop
  rcases ho with rfl | rfl | ⟨rfl, rfl⟩
  · refine ⟨by simp [isNot], ?_⟩
    cases ins with
    | nil => exact Or.inl (repr_const (Or.inr rfl))
    | cons i t =>
      cases t with
      | nil =>
        have h : gv w ⟨.and, [i]⟩ = w.getD i zero := by simp [gv, and_one_r]
        rw [h]; exact Or.inl (get_rep w i)
      | cons j t2 =>
        cases t2 with
        | nil =>
          have h : gv w ⟨.and, [i, j]⟩ = prime false (w.getD i zero) (w.getD j zero) := by
            simp [gv, prime, and_one_r]
          rw [h]; exact prime_rep false (get_rep w i) (get_rep w j)
        | cons _ _ => simp at hl
  · refine ⟨by simp [isNot], ?_⟩
    cases ins with
    | nil => exact Or.inl (repr_const (Or.inl rfl))
    | cons i t =>
      cases t with
      | nil =>
        have h : gv w ⟨.or, [i]⟩ = w.getD i zero := by simp [gv, or_zero_r]
        rw [h]; exact Or.inl (get_rep w i)
      | cons j t2 =>
        cases t2 with
        | nil =>
          have h : gv w ⟨.or, [i, j]⟩ = prime true (w.getD i zero) (w.getD j zero) := by
            simp [gv, prime, or_zero_r]
          rw [h]; exact prime_rep true (get_rep w i) (get_rep w j)
        | cons _ _ => simp at hl
  · have hrep : Repr true (w.map (nrm true)) (gv w ⟨.not, ins⟩) := by
      cases ins with
      | nil => exact repr_neg (repr_const (Or.inl rfl))
      | cons i _ => exact repr_neg (get_rep w i)
    exact ⟨fun _ => hrep, Or.inl hrep⟩

theorem pull_gate {u target} {w : List Sig} {z : Sig} {k S c} (h : Live u target k S)
    (sub : ∀ v ∈ S, v ∈ w ++ [z]) (step : witness u w z) (hc : c = if z ∈ w then 0 else 1) :
    ∃ k' S', k' ≤ k + c ∧ Live u target k' S' ∧ ∀ v ∈ S', v ∈ w := by
  by_cases hz : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k, S, by omega, h, fun v hv => ?_⟩
      rcases List.mem_append.mp (sub v hv) with hm | hm
      · exact hm
      · simp at hm; exact hm ▸ hw
    · have hc1 : c = 1 := by simp [hc, hw]
      rcases step with hrep | ⟨a, b, d, hd, am, bm, pa, pb, hab, rfl⟩
      · exfalso
        have hp := live_proper h z hz
        exact hw (hrep.resolve_right (fun hn => hn hp))
      · let U := S.erase (bin d a b)
        have hS : insert (bin d a b) U = S := Finset.insert_erase hz
        have hsubU : ∀ v ∈ U, v ∈ w := by
          intro v hv
          have hne := Finset.ne_of_mem_erase hv
          rcases List.mem_append.mp (sub v (Finset.mem_of_mem_erase hv)) with hm | hm
          · exact hm
          · simp at hm; exact absurd hm hne
        have hfresh : bin d a b ∉ insert a (insert b U) := by
          intro hm
          simp only [Finset.mem_insert] at hm
          rcases hm with e | e | hu
          · exact hw (by rw [e]; exact am)
          · exact hw (by rw [e]; exact bm)
          · exact hw (hsubU _ hu)
        refine ⟨k + 1, insert a (insert b U), by omega,
          Live.binary hd pa pb hab hfresh (hS.symm ▸ h), ?_⟩
        intro v hv
        simp only [Finset.mem_insert] at hv
        rcases hv with hva | hvb | hu
        · rw [hva]; exact am
        · rw [hvb]; exact bm
        · exact hsubU v hu
  · refine ⟨k, S, by omega, h, fun v hv => ?_⟩
    rcases List.mem_append.mp (sub v hv) with hm | hm
    · exact hm
    · simp at hm; exact absurd (hm ▸ hv) hz

theorem extract {u target} (gs : List Gate) (w : List Sig)
    (ok : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ (u = true ∧ g.op = GateOp.not)) ∧ g.inputs.length ≤ 2)
    (hp : proper target) (hit : target ∈ (execute gs w).map (nrm u)) :
    ∃ k S, k ≤ gs.countP (fun g => !isNot g) ∧ Live u target k S ∧ ∀ v ∈ S, v ∈ w.map (nrm u) := by
  induction gs generalizing w with
  | nil =>
    exact ⟨0, {target}, Nat.zero_le _, Live.stop hp, fun v hv => by rw [Finset.mem_singleton.mp hv]; exact hit⟩
  | cons g gs ih =>
    have hg := ok g List.mem_cons_self
    have hgs : ∀ g' ∈ gs, (g'.op = GateOp.and ∨ g'.op = GateOp.or ∨ (u = true ∧ g'.op = GateOp.not)) ∧ g'.inputs.length ≤ 2 :=
      fun g' hm => ok g' (List.mem_cons_of_mem _ hm)
    have hit' : target ∈ (execute gs (w ++ [gv w g])).map (nrm u) := hit
    obtain ⟨k, S, hk, hlive, hsub⟩ := ih (w ++ [gv w g]) hgs hit'
    rw [List.map_append, List.map_singleton] at hsub
    obtain ⟨hnot, hwit⟩ := gate_rep u w g hg
    by_cases hn : isNot g = true
    · have hrep := hnot hn
      have hsub' : ∀ v ∈ S, v ∈ w.map (nrm u) := by
        intro v hv
        rcases List.mem_append.mp (hsub v hv) with hm | hm
        · exact hm
        · simp at hm; subst hm
          exact hrep.resolve_right (fun hnp => hnp (live_proper hlive _ hv))
      exact ⟨k, S, by simpa [List.countP_cons, hn] using hk, hlive, hsub'⟩
    · have hnf : (!isNot g) = true := by cases h : isNot g <;> simp_all
      obtain ⟨k', S', hk', hlive', hsub'⟩ := pull_gate hlive hsub hwit rfl
      have hc : (if nrm u (gv w g) ∈ w.map (nrm u) then 0 else 1) ≤ 1 := by split_ifs <;> omega
      exact ⟨k', S', by simp only [List.countP_cons, hnf, ite_true]; omega, hlive', hsub'⟩

theorem b_read (i : Row) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  by_cases hj : j < w.length
  · simp [List.getD_eq_getElem, hj]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega), bit_zero]

theorem run_bit (i : Row) (g : Gate) (w : List Sig)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨op, ins⟩ := g
  rcases hop with rfl | rfl | rfl
  · simp only [gv, GateOp.eval]
    induction ins with
    | nil => exact bit_one i
    | cons j t ih =>
      simp only [List.map_cons, List.foldr_cons, List.all_cons, id_eq, bit_and]
      rw [b_read]; exact congrArg (bit i (w.getD j zero) && ·) ih
  · simp only [gv, GateOp.eval]
    induction ins with
    | nil => exact bit_zero i
    | cons j t ih =>
      simp only [List.map_cons, List.foldr_cons, List.any_cons, id_eq, bit_or]
      rw [b_read]; exact congrArg (bit i (w.getD j zero) || ·) ih
  · simp only [gv, GateOp.eval]
    cases ins with
    | nil => simp [bit_neg, bit_zero]
    | cons j t =>
      simp only [List.map_cons, List.headD_cons, bit_neg]
      rw [b_read]

theorem execute_bits (gs : List Gate) (i : Row) (w : List Sig)
    (ok : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) :
    (execute gs w).map (bit i) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [execute, List.foldl_cons]
    have h1 := ih (w ++ [gv w g]) (fun g' hg' => ok g' (List.mem_cons_of_mem _ hg'))
    rw [List.map_append, List.map_singleton, run_bit i g w (ok g List.mem_cons_self)] at h1
    exact h1

abbrev Wire := Row → Bool
def inv (a : Wire) : Wire := fun r => !(a r)
def comb (d : Nat) (a b : Wire) : Wire :=
  if d = 0 then fun r => a r && b r
  else if d = 1 then fun r => a r || b r
  else if d = 2 then fun r => a r && !(b r)
  else fun r => !(a r) && b r

def Constant (a : Wire) : Prop := ∃ b : Bool, a = fun _ => b
def observe (a : Sig) : Wire := fun r => bit r a
def restrictRows (f : Row → Row) (a : Wire) : Wire := fun r => a (f r)

def Available (u : Bool) (pool : List Wire) (v : Wire) : Prop :=
  v ∈ pool ∨ Constant v ∨ (u = true ∧ inv v ∈ pool)

def supply (u : Bool) (pool xs : List Wire) : Prop := ∀ a ∈ xs, Available u pool a

def Reach (u : Bool) (roots : List Wire) : Nat → List Wire → Prop
  | 0, bank => bank = roots
  | p + 1, bank =>
      ∃ prev a b d, allowed u d ∧ Reach u roots p prev ∧
        Available u prev a ∧ Available u prev b ∧ bank = comb d a b :: prev

theorem Reach.start {u roots} : Reach u roots 0 roots := rfl

theorem Reach.step {u roots p prev a b d} (hd : allowed u d) (hr : Reach u roots p prev)
    (ha : Available u prev a) (hb : Available u prev b) :
    Reach u roots (p + 1) (comb d a b :: prev) :=
  ⟨prev, a, b, d, hd, hr, ha, hb, rfl⟩

theorem available_cons {u bank v} (w : Wire) (h : Available u bank v) :
    Available u (w :: bank) v := by
  rcases h with hm | hc | ⟨hu, hm⟩
  · exact Or.inl (List.mem_cons_of_mem _ hm)
  · exact Or.inr (Or.inl hc)
  · exact Or.inr (Or.inr ⟨hu, List.mem_cons_of_mem _ hm⟩)

theorem obs_bin (d : Nat) (a b : Sig) : observe (bin d a b) = comb d (observe a) (observe b) := by
  funext r; unfold observe comb; rw [bit_bin]; split_ifs <;> rfl

theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r; exact bit_neg r a

def kept {α : Type} (k : Bool) (a : α) (xs : List α) : List α := if k then a :: xs else xs

def Run (u : Bool) (goal : Wire) (s : Nat) (ws : List Wire) : Prop :=
  ∀ P : Nat → List Wire → Prop,
    P 0 [goal] →
    (∀ {t xs ys}, List.Perm xs ys → P t xs → P t ys) →
    (∀ {t a b xs d} (ka kb : Bool), allowed u d →
      P t (comb d a b :: kept ka a (kept kb b xs)) → P (t + 1) (a :: b :: xs)) →
    P s ws

theorem Run.done {u goal} : Run u goal 0 [goal] := fun _ d _ _ => d
theorem Run.perm {u goal s xs ys} (hp : List.Perm xs ys) (h : Run u goal s xs) : Run u goal s ys :=
  fun P d q b => q hp (h P d q b)
theorem Run.two {u goal s a b xs d} (ka kb : Bool) (hd : allowed u d)
    (h : Run u goal s (comb d a b :: kept ka a (kept kb b xs))) :
    Run u goal (s + 1) (a :: b :: xs) :=
  fun P d0 q b0 => b0 ka kb hd (h P d0 q b0)

theorem Run.ind {u goal} {P : ∀ s ws, Run u goal s ws → Prop}
    (done : P 0 [goal] Run.done)
    (perm : ∀ {t xs ys} (hp : List.Perm xs ys) (h : Run u goal t xs), P t xs h → P t ys (Run.perm hp h))
    (two : ∀ {t a b xs d} (ka kb : Bool) (hd : allowed u d)
      (h : Run u goal t (comb d a b :: kept ka a (kept kb b xs))),
      P t _ h → P (t + 1) (a :: b :: xs) (Run.two ka kb hd h))
    {s ws} (h : Run u goal s ws) : P s ws h := by
  have hex := h (fun t xs => ∃ h' : Run u goal t xs, P t xs h')
    ⟨Run.done, done⟩
    (fun hp ⟨h', ih⟩ => ⟨Run.perm hp h', perm hp h' ih⟩)
    (fun ka kb hd ⟨h', ih⟩ => ⟨Run.two ka kb hd h', two ka kb hd h' ih⟩)
  exact hex.elim fun _ hp => hp

noncomputable def cost (a : Wire) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass : List Wire → Nat
  | [] => 0
  | a :: xs => cost a + mass xs

theorem mass_perm {xs ys : List Wire} (hp : List.Perm xs ys) : mass xs = mass ys := by
  induction hp with
  | nil => rfl
  | cons a _ ih => simp [mass, ih]
  | swap a b l => simp [mass]; omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem mass_kept (a : Wire) (xs : List Wire) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept, mass]

theorem inv_inv (a : Wire) : inv (inv a) = a := funext fun r => Bool.not_not (a r)

theorem avail_inv {u bank a} (hu : u = true) (h : Available u bank a) : Available u bank (inv a) := by
  rcases h with hm | ⟨b, rfl⟩ | ⟨_, hm⟩
  · exact Or.inr (Or.inr ⟨hu, by rw [inv_inv]; exact hm⟩)
  · exact Or.inr (Or.inl ⟨!b, funext fun _ => rfl⟩)
  · exact Or.inl hm

theorem comb_const_left {u bank d a b} (hd : allowed u d) (hc : Constant a) (hb : Available u bank b) :
    Available u bank (comb d a b) := by
  obtain ⟨v, rfl⟩ := hc
  rcases allowed_four hd with rfl | rfl | ⟨hu, rfl⟩ | ⟨hu, rfl⟩
  · cases v
    · exact Or.inr (Or.inl ⟨false, funext fun _ => rfl⟩)
    · have e : comb 0 (fun _ => true) b = b := funext fun _ => rfl
      rw [e]; exact hb
  · cases v
    · have e : comb 1 (fun _ => false) b = b := funext fun _ => rfl
      rw [e]; exact hb
    · exact Or.inr (Or.inl ⟨true, funext fun _ => rfl⟩)
  · cases v
    · exact Or.inr (Or.inl ⟨false, funext fun _ => rfl⟩)
    · have e : comb 2 (fun _ => true) b = inv b := funext fun _ => rfl
      rw [e]; exact avail_inv hu hb
  · cases v
    · have e : comb 3 (fun _ => false) b = b := funext fun _ => rfl
      rw [e]; exact hb
    · exact Or.inr (Or.inl ⟨false, funext fun _ => rfl⟩)

theorem comb_const_right {u bank d a b} (hd : allowed u d) (ha : Available u bank a) (hc : Constant b) :
    Available u bank (comb d a b) := by
  obtain ⟨v, rfl⟩ := hc
  rcases allowed_four hd with rfl | rfl | ⟨hu, rfl⟩ | ⟨hu, rfl⟩
  · cases v
    · exact Or.inr (Or.inl ⟨false, funext fun r => by simp [comb]⟩)
    · have e : comb 0 a (fun _ => true) = a := funext fun r => by simp [comb]
      rw [e]; exact ha
  · cases v
    · have e : comb 1 a (fun _ => false) = a := funext fun r => by simp [comb]
      rw [e]; exact ha
    · exact Or.inr (Or.inl ⟨true, funext fun r => by simp [comb]⟩)
  · cases v
    · have e : comb 2 a (fun _ => false) = a := funext fun r => by simp [comb]
      rw [e]; exact ha
    · exact Or.inr (Or.inl ⟨false, funext fun r => by simp [comb]⟩)
  · cases v
    · exact Or.inr (Or.inl ⟨false, funext fun r => by simp [comb]⟩)
    · have e : comb 3 a (fun _ => true) = inv a := funext fun r => by simp [comb, inv]
      rw [e]; exact avail_inv hu ha

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs : List α} (h : x ∈ kept k a xs) :
    x = a ∨ x ∈ xs := by
  cases k with
  | false => exact Or.inr h
  | true => exact List.mem_cons.mp h

theorem contraction {u goal} (nc : ¬Constant goal) {s ws} (run : Run u goal s ws)
    (roots : List Wire) {p bank} (hr : Reach u roots p bank) (hs : supply u bank ws) :
    ∃ q next, Reach u roots q next ∧ Available u next goal ∧ q + mass ws ≤ p + s := by
  induction run using Run.ind generalizing p bank with
  | done =>
    have hm : mass [goal] = 0 := by classical simp [mass, cost, nc]
    exact ⟨p, bank, hr, hs goal List.mem_cons_self, by omega⟩
  | perm hp _ ih =>
    obtain ⟨q, next, hq, ha, hle⟩ := ih hr (fun x hx => hs x (hp.mem_iff.mp hx))
    exact ⟨q, next, hq, ha, by rw [← mass_perm hp]; exact hle⟩
  | @two t a b xs d ka kb hd _ ih =>
    have ha := hs a List.mem_cons_self
    have hb := hs b (List.mem_cons_of_mem _ List.mem_cons_self)
    have hxs : ∀ x ∈ xs, Available u bank x :=
      fun x hx => hs x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))
    classical
    by_cases ca : Constant a
    · have hc := comb_const_left hd ca hb
      have hsup : supply u bank (comb d a b :: kept ka a (kept kb b xs)) := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hc
        · rcases mem_kept hx with rfl | hx
          · exact ha
          · rcases mem_kept hx with rfl | hx
            · exact hb
            · exact hxs x hx
      obtain ⟨q, next, hq, hhit, hle⟩ := ih hr hsup
      have hca : cost a = 1 := by simp [cost, ca]
      have hmk : mass xs ≤ mass (kept ka a (kept kb b xs)) :=
        (mass_kept b xs kb).trans (mass_kept a _ ka)
      have hma : mass (a :: b :: xs) = cost a + cost b + mass xs := by simp [mass]; omega
      have hmc : mass (comb d a b :: kept ka a (kept kb b xs)) = cost (comb d a b) + mass (kept ka a (kept kb b xs)) := rfl
      by_cases cb : Constant b
      · have hcb1 : cost b = 1 := by simp [cost, cb]
        have hcc1 : cost (comb d a b) = 1 := by
          have : Constant (comb d a b) := by
            obtain ⟨va, rfl⟩ := ca; obtain ⟨vb, rfl⟩ := cb
            refine ⟨(comb d (fun _ => va) (fun _ => vb)) 0, funext fun r => ?_⟩
            unfold comb; split_ifs <;> rfl
          simp [cost, this]
        exact ⟨q, next, hq, hhit, by omega⟩
      · have hcb0 : cost b = 0 := by simp [cost, cb]
        have hcc : cost (comb d a b) ≤ 1 := by simp [cost]; split_ifs <;> omega
        exact ⟨q, next, hq, hhit, by omega⟩
    · by_cases cb : Constant b
      · have hc := comb_const_right hd ha cb
        have hsup : supply u bank (comb d a b :: kept ka a (kept kb b xs)) := by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hc
          · rcases mem_kept hx with rfl | hx
            · exact ha
            · rcases mem_kept hx with rfl | hx
              · exact hb
              · exact hxs x hx
        obtain ⟨q, next, hq, hhit, hle⟩ := ih hr hsup
        have hca0 : cost a = 0 := by simp [cost, ca]
        have hcb1 : cost b = 1 := by simp [cost, cb]
        have hcc : cost (comb d a b) ≤ 1 := by simp [cost]; split_ifs <;> omega
        have hmk : mass xs ≤ mass (kept ka a (kept kb b xs)) :=
          (mass_kept b xs kb).trans (mass_kept a _ ka)
        have hma : mass (a :: b :: xs) = cost a + cost b + mass xs := by simp [mass]; omega
        have hmc : mass (comb d a b :: kept ka a (kept kb b xs)) = cost (comb d a b) + mass (kept ka a (kept kb b xs)) := rfl
        exact ⟨q, next, hq, hhit, by omega⟩
      · have hr' := Reach.step hd hr ha hb
        have hsup : supply u (comb d a b :: bank) (comb d a b :: kept ka a (kept kb b xs)) := by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact Or.inl List.mem_cons_self
          · apply available_cons
            rcases mem_kept hx with rfl | hx
            · exact ha
            · rcases mem_kept hx with rfl | hx
              · exact hb
              · exact hxs x hx
        obtain ⟨q, next, hq, hhit, hle⟩ := ih hr' hsup
        have hca0 : cost a = 0 := by simp [cost, ca]
        have hcb0 : cost b = 0 := by simp [cost, cb]
        have hmk : mass xs ≤ mass (kept ka a (kept kb b xs)) :=
          (mass_kept b xs kb).trans (mass_kept a _ ka)
        have hma : mass (a :: b :: xs) = cost a + cost b + mass xs := by simp [mass]; omega
        have hmc : mass (comb d a b :: kept ka a (kept kb b xs)) = cost (comb d a b) + mass (kept ka a (kept kb b xs)) := rfl
        exact ⟨q, next, hq, hhit, by omega⟩

theorem restrict_comb (f : Row → Row) (d : Nat) (a b : Wire) :
    restrictRows f (comb d a b) = comb d (restrictRows f a) (restrictRows f b) := by
  funext r; unfold restrictRows comb; split_ifs <;> rfl

theorem restrict_kept (f : Row → Row) (k : Bool) (a : Wire) (ws : List Wire) :
    (kept k a ws).map (restrictRows f) = kept k (restrictRows f a) (ws.map (restrictRows f)) := by
  cases k <;> rfl

theorem restrict_run {u goal s ws} (f : Row → Row) (h : Run u goal s ws) :
    Run u (restrictRows f goal) s (ws.map (restrictRows f)) := by
  induction h using Run.ind with
  | done => exact Run.done
  | perm hp _ ih => exact Run.perm (hp.map _) ih
  | two ka kb hd _ ih =>
    simp only [List.map_cons, restrict_comb, restrict_kept] at ih ⊢
    exact Run.two ka kb hd ih

theorem restrict_avail {u bank v} (f : Row → Row) (h : Available u bank v) :
    Available u (bank.map (restrictRows f)) (restrictRows f v) := by
  rcases h with hm | ⟨b, rfl⟩ | ⟨hu, hm⟩
  · exact Or.inl (List.mem_map_of_mem hm)
  · exact Or.inr (Or.inl ⟨b, rfl⟩)
  · exact Or.inr (Or.inr ⟨hu, List.mem_map_of_mem hm⟩)

theorem avail_trans {u bank1 bank2 v} (hsub : ∀ x ∈ bank1, Available u bank2 x)
    (h : Available u bank1 v) : Available u bank2 v := by
  rcases h with hm | hc | ⟨hu, hm⟩
  · exact hsub v hm
  · exact Or.inr (Or.inl hc)
  · have h2 := avail_inv hu (hsub (inv v) hm)
    rwa [inv_inv] at h2

theorem restrict_reach {u roots base p bank} (f : Row → Row)
    (hr : Reach u roots p bank) (hroots : ∀ a ∈ roots, Available u base (restrictRows f a)) :
    ∃ bank', Reach u base p bank' ∧ ∀ v ∈ bank, Available u bank' (restrictRows f v) := by
  induction p generalizing bank with
  | zero =>
    cases hr
    exact ⟨base, Reach.start, hroots⟩
  | succ p ih =>
    obtain ⟨prev, a, b, d, hd, hrp, ha, hb, rfl⟩ := hr
    obtain ⟨bank', hr', hsub⟩ := ih hrp
    have hsubM : ∀ x ∈ prev.map (restrictRows f), Available u bank' x := by
      intro x hx; obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx; exact hsub v hv
    have ha' := avail_trans hsubM (restrict_avail f ha)
    have hb' := avail_trans hsubM (restrict_avail f hb)
    refine ⟨comb d (restrictRows f a) (restrictRows f b) :: bank', Reach.step hd hr' ha' hb', ?_⟩
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · rw [restrict_comb]; exact Or.inl List.mem_cons_self
    · exact available_cons _ (hsub v hv)

theorem map_kept {α β : Type} (f : α → β) (k : Bool) (a : α) (l : List α) :
    (kept k a l).map f = kept k (f a) (l.map f) := by cases k <;> rfl

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem restoreInputs (U : Finset Sig) (a b : Sig) (hab : a ≠ b) :
    (if a ∈ U then insert a (if b ∈ U then insert b ((U.erase a).erase b) else (U.erase a).erase b)
     else if b ∈ U then insert b ((U.erase a).erase b) else (U.erase a).erase b) = U := by
  ext x
  by_cases ha : a ∈ U <;> by_cases hb : b ∈ U <;> simp [ha, hb] <;> grind

theorem list_run {u T k S} (h : Live u T k S) :
    ∀ v : List Sig, v.Nodup → v.toFinset = S → Run u (observe T) k (v.map observe) := by
  classical
  induction h using Live.ind with
  | stop _ =>
    intro v hnd heq
    have hlen : v.length = 1 := by rw [← List.toFinset_card_of_nodup hnd, heq]; simp
    match v, hlen with
    | [a], _ =>
      have ha : a = T := by simpa using heq
      subst ha; exact Run.done
  | @binary k U a b d hd _ _ hab hf _ ih =>
    intro v hnd heq
    have ha : a ∈ v := List.mem_toFinset.mp (heq.symm ▸ Finset.mem_insert_self ..)
    have hb : b ∈ v := List.mem_toFinset.mp (heq.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    let rest := (v.erase a).erase b
    have hperm : List.Perm (a :: b :: rest) v := by
      have hp1 : List.Perm (a :: v.erase a) v := (List.perm_cons_erase ha).symm
      have hb' : b ∈ v.erase a := (hnd.mem_erase_iff).mpr ⟨hab.symm, hb⟩
      have hp2 : List.Perm (b :: rest) (v.erase a) := (List.perm_cons_erase hb').symm
      exact (hp2.cons a).trans hp1
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let child := bin d a b :: kept ka a (kept kb b rest)
    have her : rest.toFinset = (v.toFinset.erase a).erase b := by
      ext x; simp [rest, hnd.mem_erase_iff, (hnd.erase a).mem_erase_iff]
    have hke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin, kept_fin, her, heq, Finset.erase_insert_eq_erase,
        Finset.erase_insert_of_ne hab.symm, Finset.erase_insert_eq_erase]
      simpa only [ka, kb, decide_eq_true_eq] using restoreInputs U a b hab
    have hrnd : rest.Nodup := (hnd.erase a).erase b
    have han : a ∉ rest := fun hm => hnd.not_mem_erase (List.mem_of_mem_erase hm)
    have hbn : b ∉ rest := (hnd.erase a).not_mem_erase
    have hkbnd : (kept kb b rest).Nodup := by cases kb <;> simp [kept, hrnd, hbn]
    have hakb : a ∉ kept kb b rest := by cases kb <;> simp [kept, han, hab]
    have hcnd : child.Nodup := by
      refine List.nodup_cons.mpr ⟨?_, ?_⟩
      · intro hm
        exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hke ▸ List.mem_toFinset.mpr hm)))
      · cases ka with
        | false => exact hkbnd
        | true => exact List.nodup_cons.mpr ⟨hakb, hkbnd⟩
    have hceq : child.toFinset = insert (bin d a b) U := by simp [child, hke]
    have htail := ih child hcnd hceq
    have hmap : child.map observe =
        comb d (observe a) (observe b) :: kept ka (observe a) (kept kb (observe b) (rest.map observe)) := by
      simp [child, obs_bin, map_kept]
    rw [hmap] at htail
    exact Run.perm (hperm.map observe) (Run.two ka kb hd htail)

theorem live_row_difference {u T k S} (h : Live u T k S) {r s : Row} (hd : bit r T ≠ bit s T) :
    ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Live.ind with
  | stop _ => exact ⟨T, Finset.mem_singleton_self T, hd⟩
  | binary _ _ _ _ _ _ ih =>
    obtain ⟨v, hv, hne⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin, bit_bin] at hne
      by_contra! hall
      have ha := hall _ (Finset.mem_insert_self ..)
      have hb := hall _ (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
      rw [ha, hb] at hne
      exact hne rfl
    · exact ⟨v, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu), hne⟩

theorem mono_row_difference {T k S} (h : Live false T k S) {r s : Row}
    (pos : bit r T = true) (negR : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h using Live.ind with
  | stop _ => exact ⟨T, Finset.mem_singleton_self T, pos, negR⟩
  | @binary k U a b d hd _ _ _ _ _ ih =>
    obtain ⟨v, hv, hp, hn⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      rcases allowed_four hd with rfl | rfl | ⟨h, _⟩ | ⟨h, _⟩
      · cases p : bit r a <;> cases q : bit s a <;> cases x : bit r b <;> cases y : bit s b <;> simp_all
      · cases p : bit r a <;> cases q : bit s a <;> cases x : bit r b <;> cases y : bit s b <;> simp_all
      · exact Bool.noConfusion h
      · exact Bool.noConfusion h
    · exact ⟨v, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu), hp, hn⟩

theorem raw_required {u T k S} (h : Live u T k S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (hd : bit r T ≠ bit s T)
    (iso : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v, hv, hne⟩ := live_row_difference h hd
  by_contra! hna
  have hve : v ≠ a := fun e => hna (e ▸ hv)
  exact hne (iso v (sub v hv) hve)

def sepCovered (u : Bool) (pairs : List (Row × Row)) (ws : List Sig) : Bool :=
  pairs.all fun p => ws.any fun w =>
    if u then bit p.1 w != bit p.2 w else bit p.1 w && !(bit p.2 w)

theorem sepCovered_required {u T k ws} (h : Live u T k ws.toFinset) (pairs : List (Row × Row))
    (hpairs : pairs.all (fun p => bit p.1 T && !(bit p.2 T)) = true) :
    sepCovered u pairs ws = true := by
  rw [sepCovered, List.all_eq_true]
  intro p hp
  have hpt := List.all_eq_true.mp hpairs p hp
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hpt
  rw [List.any_eq_true]
  cases u with
  | false =>
    obtain ⟨a, ha, h1, h2⟩ := mono_row_difference h hpt.1 hpt.2
    exact ⟨a, List.mem_toFinset.mp ha, by simp only [Bool.false_eq_true, ite_false, h1, h2, Bool.not_false, Bool.and_self]⟩
  | true =>
    obtain ⟨a, ha, hne⟩ := live_row_difference h (r := p.1) (s := p.2) (by rw [hpt.1, hpt.2]; decide)
    exact ⟨a, List.mem_toFinset.mp ha, by simp only [ite_true, bne_iff_ne]; exact hne⟩

def isConstOn (d w : Sig) : Bool :=
  let m := w &&& d
  m == zero || m == d

theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (isConstOn d) ≤ mass ((ws.map observe).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons, List.map_cons, mass]
    cases h : isConstOn d a
    · simp only [Bool.false_eq_true, ite_false]; omega
    · have hc : Constant (restrictRows f (observe a)) := by
        simp only [isConstOn, Bool.or_eq_true, beq_iff_eq] at h
        rcases h with hz | ho
        · refine ⟨false, funext fun r => ?_⟩
          have hr := congrArg (bit (f r)) hz
          rw [bit_and, bit_zero, dom r, Bool.and_true] at hr
          exact hr
        · refine ⟨true, funext fun r => ?_⟩
          have hr := congrArg (bit (f r)) ho
          rw [bit_and, dom r, Bool.and_true] at hr
          exact hr
      have hcost : cost (restrictRows f (observe a)) = 1 := by simp [cost, hc]
      simp only [ite_true, hcost]; omega

def Lower (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (observe T) → L ≤ p

def Slice (u : Bool) (roots : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (base : List Sig),
    (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ roots, Available u (base.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach u (base.map observe) p bank → Available u bank (restrictRows f (observe T)) → L ≤ p

def ImpossibleFrom (u : Bool) (roots : List Sig) (T : Sig) (cap k_rem : Nat) (ws : List Sig) : Prop :=
  ∀ bank, Reach u (roots.map observe) (cap - k_rem) bank → supply u bank (ws.map observe) →
    ∀ k, k ≤ k_rem → ¬Live u T k ws.toFinset

theorem impossible_of_size {u roots T cap k_rem ws} (hnd : ws.Nodup) (hsz : k_rem + 1 < ws.length) :
    ImpossibleFrom u roots T cap k_rem ws := by
  intro _ _ _ k hk hlive
  have hs := live_size hlive
  rw [List.toFinset_card_of_nodup hnd] at hs
  omega

theorem impossible_of_sep {u roots T cap k_rem ws} (pairs : List (Row × Row))
    (hpairs : pairs.all (fun p => bit p.1 T && !(bit p.2 T)) = true)
    (hfail : sepCovered u pairs ws = false) :
    ImpossibleFrom u roots T cap k_rem ws := by
  intro _ _ _ k _ hlive
  have hok := sepCovered_required hlive pairs hpairs
  rw [hfail] at hok; exact Bool.noConfusion hok

theorem impossible_of_slice {u roots T cap k_rem ws d L} (hnd : ws.Nodup) (hkr : k_rem ≤ cap)
    (hs : Slice u roots T d L) (hcut : cap < L + ws.countP (isConstOn d)) :
    ImpossibleFrom u roots T cap k_rem ws := by
  intro bank hr hsup k hk hlive
  obtain ⟨f, base, dom, hroots, nc, hlo⟩ := hs
  obtain ⟨bank', hr', hsub⟩ := restrict_reach f hr (fun a ha => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ha; exact hroots w hw)
  have hsubM : ∀ x ∈ bank.map (restrictRows f), Available u bank' x := by
    intro x hx; obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx; exact hsub v hv
  have hsup' : supply u bank' ((ws.map observe).map (restrictRows f)) := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    exact avail_trans hsubM (restrict_avail f (hsup w hw))
  have hrun := restrict_run f (list_run hlive ws hnd rfl)
  obtain ⟨q, next, hq, hhit, hle⟩ := contraction nc hrun (base.map observe) hr' hsup'
  have hL := hlo q next hq hhit
  have hcm := count_constants dom ws
  omega

theorem impossible_zero {u roots T cap ws} (hout : T ∉ ws) :
    ImpossibleFrom u roots T cap 0 ws := by
  intro _ _ _ k hk hlive
  have hk0 : k = 0 := by omega
  subst hk0
  obtain ⟨heq, _⟩ := hlive
  exact hout (List.mem_toFinset.mp (heq.symm ▸ Finset.mem_singleton_self T))

def insertSorted (x : Sig) : List Sig → List Sig
  | [] => [x]
  | a :: l => if x.toNat ≤ a.toNat then x :: a :: l else a :: insertSorted x l

theorem perm_insertSorted (x : Sig) (l : List Sig) : List.Perm (insertSorted x l) (x :: l) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons a l ih =>
    simp only [insertSorted]
    split
    · exact List.Perm.refl _
    · exact (ih.cons a).trans (List.Perm.swap x a l)

def removeIf (keep : Bool) (x : Sig) (l : List Sig) : List Sig :=
  if keep then l else l.erase x

theorem perm_removeIf {a : Sig} {l : List Sig} (ha : a ∈ l) (keep : Bool) :
    List.Perm (removeIf keep a l) (kept keep a (l.erase a)) := by
  cases keep with
  | false => exact List.Perm.refl _
  | true => exact List.perm_cons_erase ha

def childCanon (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  insertSorted (bin d a b) (removeIf ka a (removeIf kb b ws))

theorem perm_childCanon {ws : List Sig} {a b : Sig} (hnd : ws.Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (hab : a ≠ b) (d : Nat) (ka kb : Bool) :
    List.Perm (childCanon ws a b d ka kb) (bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))) := by
  have h1 := perm_insertSorted (bin d a b) (removeIf ka a (removeIf kb b ws))
  have hb_nd : (removeIf kb b ws).Nodup := by
    cases kb with
    | false => exact hnd.erase b
    | true => exact hnd
  have ha_in : a ∈ removeIf kb b ws := by
    cases kb with
    | false => exact (hnd.mem_erase_iff).mpr ⟨hab, ha⟩
    | true => exact ha
  have h2 := perm_removeIf ha_in ka
  have her_comm : (ws.erase b).erase a = (ws.erase a).erase b := List.erase_comm b a
  have h3 : List.Perm (kept ka a ((removeIf kb b ws).erase a)) (kept ka a (kept kb b ((ws.erase a).erase b))) := by
    have hinner : List.Perm ((removeIf kb b ws).erase a) (kept kb b ((ws.erase a).erase b)) := by
      cases kb with
      | false => rw [removeIf, if_neg Bool.false_ne_true, her_comm]; exact List.Perm.refl _
      | true =>
        rw [removeIf, if_pos rfl]
        have hb_in : b ∈ ws.erase a := (hnd.mem_erase_iff).mpr ⟨hab.symm, hb⟩
        exact List.perm_cons_erase hb_in
    cases ka with
    | false => exact hinner
    | true => exact hinner.cons a
  exact h1.trans ((h2.trans h3).cons (bin d a b))

theorem impossible_of_perm {u roots T cap k_rem ws ws'} (hp : List.Perm ws ws')
    (h : ImpossibleFrom u roots T cap k_rem ws') : ImpossibleFrom u roots T cap k_rem ws := by
  intro bank hr hsup k hk hlive
  have heq : ws.toFinset = ws'.toFinset := by ext x; simp [hp.mem_iff]
  exact h bank hr (fun v hv => hsup v ((hp.map observe).mem_iff.mpr hv)) k hk (heq ▸ hlive)

theorem impossible_branch {u roots T cap k_rem ws} (hkr : 0 < k_rem) (hkr2 : k_rem ≤ cap)
    (hnd : ws.Nodup) (hout : T ∉ ws)
    (hstep : ∀ a ∈ ws, ∀ b ∈ ws, a.toNat < b.toNat →
      ∀ d, allowed u d →
        proper (bin d a b) → bin d a b ∉ ws →
        ∀ ka kb : Bool, (childCanon ws a b d ka kb).length ≤ k_rem →
        ImpossibleFrom u roots T cap (k_rem - 1) (childCanon ws a b d ka kb)) :
    ImpossibleFrom u roots T cap k_rem ws := by
  classical
  intro bank hr hsup k hk hlive
  generalize he : ws.toFinset = S at hlive
  induction hlive using Live.ind with
  | stop _ =>
    exact hout (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  | @binary k' U a b d hd ha hb hab hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self ..)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    have fresh : bin d a b ∉ ws := fun hm => hf (he ▸ List.mem_toFinset.mpr hm)
    have hz := live_proper tail _ (Finset.mem_insert_self ..)
    have flip_case : ∀ (x y : Sig) (d' : Nat), x ∈ ws → y ∈ ws → x.toNat < y.toNat →
        allowed u d' → bin d' x y = bin d a b →
        insert x (insert y U) = insert a (insert b U) → False := by
      intro x y d' hx hy hxy hd' hbin hS
      have hxy_ne : x ≠ y := fun e => Nat.ne_of_lt hxy (congrArg BitVec.toNat e)
      let ka := decide (x ∈ U)
      let kb := decide (y ∈ U)
      let rest := (ws.erase x).erase y
      have her : rest.toFinset = (ws.toFinset.erase x).erase y := by
        ext z; simp [rest, hnd.mem_erase_iff, (hnd.erase x).mem_erase_iff]
      have hke : (kept ka x (kept kb y rest)).toFinset = U := by
        rw [kept_fin, kept_fin, her, he, ← hS, Finset.erase_insert_eq_erase,
          Finset.erase_insert_of_ne hxy_ne.symm, Finset.erase_insert_eq_erase]
        simpa only [ka, kb, decide_eq_true_eq] using restoreInputs U x y hxy_ne
      have hrnd : rest.Nodup := (hnd.erase x).erase y
      have hxn : x ∉ rest := fun hm => hnd.not_mem_erase (List.mem_of_mem_erase hm)
      have hyn : y ∉ rest := (hnd.erase x).not_mem_erase
      have hkbnd : (kept kb y rest).Nodup := by cases kb <;> simp [kept, hrnd, hyn]
      have hxkb : x ∉ kept kb y rest := by cases kb <;> simp [kept, hxn, hxy_ne]
      let ch := bin d' x y :: kept ka x (kept kb y rest)
      have hcnd : ch.Nodup := by
        refine List.nodup_cons.mpr ⟨?_, ?_⟩
        · intro hm
          have : bin d a b ∈ U := hbin ▸ (hke ▸ List.mem_toFinset.mpr hm)
          exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem this))
        · cases ka with
          | false => exact hkbnd
          | true => exact List.nodup_cons.mpr ⟨hxkb, hkbnd⟩
      have hceq : ch.toFinset = insert (bin d a b) U := by simp [ch, hbin, hke]
      have hperm := perm_childCanon hnd hx hy hxy_ne d' ka kb
      have hlen : (childCanon ws x y d' ka kb).length ≤ k_rem := by
        rw [hperm.length_eq, ← List.toFinset_card_of_nodup hcnd, hceq]
        have := live_size tail; omega
      have himp := hstep x hx y hy hxy d' hd' (hbin ▸ hz) (hbin ▸ fresh) ka kb hlen
      have himp' := impossible_of_perm hperm.symm himp
      have hx_av := hsup (observe x) (List.mem_map_of_mem hx)
      have hy_av := hsup (observe y) (List.mem_map_of_mem hy)
      have hstep_reach : Reach u (roots.map observe) (cap - (k_rem - 1))
          (comb d' (observe x) (observe y) :: bank) := by
        have heq_p : cap - (k_rem - 1) = (cap - k_rem) + 1 := by omega
        rw [heq_p]; exact Reach.step hd' hr hx_av hy_av
      have hsup' : supply u (comb d' (observe x) (observe y) :: bank) (ch.map observe) := by
        intro v hv
        obtain ⟨z, hz_mem, rfl⟩ := List.mem_map.mp hv
        rcases List.mem_cons.mp hz_mem with rfl | hz_mem
        · rw [obs_bin]; exact Or.inl List.mem_cons_self
        · apply available_cons
          rcases mem_kept hz_mem with rfl | hz_mem
          · exact hx_av
          · rcases mem_kept hz_mem with rfl | hz_mem
            · exact hy_av
            · exact hsup _ (List.mem_map_of_mem (List.mem_of_mem_erase (List.mem_of_mem_erase hz_mem)))
      exact himp' _ hstep_reach hsup' k' (by omega) (hceq.symm ▸ tail)
    have hne_nat : a.toNat ≠ b.toNat := fun e => hab (BitVec.eq_of_toNat_eq e)
    rcases Nat.lt_or_gt_of_ne hne_nat with hlt | hgt
    · exact flip_case a b d am bm hlt hd rfl rfl
    · let d' := if d = 2 then 3 else if d = 3 then 2 else d
      have hd' : allowed u d' := by
        rcases allowed_four hd with rfl | rfl | ⟨hu, rfl⟩ | ⟨hu, rfl⟩
        · exact Or.inl (by decide)
        · exact Or.inl (by decide)
        · exact Or.inr ⟨hu, by decide⟩
        · exact Or.inr ⟨hu, by decide⟩
      have hbin : bin d' b a = bin d a b := by
        rcases allowed_four hd with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩
        · exact bit_ext fun i => by rw [bit_bin, bit_bin]; exact Bool.and_comm _ _
        · exact bit_ext fun i => by rw [bit_bin, bit_bin]; exact Bool.or_comm _ _
        · exact bit_ext fun i => by rw [bit_bin, bit_bin]; exact Bool.and_comm _ _
        · exact bit_ext fun i => by rw [bit_bin, bit_bin]; exact Bool.and_comm _ _
      exact flip_case b a d' bm am hgt hd' hbin (Finset.insert_comm b a U)

def isSortedStrict : List Sig → Bool
  | [] => true
  | [_] => true
  | a :: b :: l => decide (a.toNat < b.toNat) && isSortedStrict (b :: l)

theorem sortedStrict_lt {a : Sig} {l : List Sig} (h : isSortedStrict (a :: l) = true) :
    ∀ x ∈ l, a.toNat < x.toNat := by
  induction l generalizing a with
  | nil => intro _ hx; cases hx
  | cons b l ih =>
    simp only [isSortedStrict, Bool.and_eq_true, decide_eq_true_eq] at h
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact Nat.lt_trans h.1 (ih h.2 x hx)

theorem sortedStrict_nodup : ∀ {l : List Sig}, isSortedStrict l = true → l.Nodup
  | [], _ => List.nodup_nil
  | [_], _ => List.nodup_singleton _
  | a :: b :: l, h => by
    have hlt := sortedStrict_lt h
    simp only [isSortedStrict, Bool.and_eq_true] at h
    exact List.nodup_cons.mpr ⟨fun hm => Nat.ne_of_lt (hlt a hm) rfl, sortedStrict_nodup h.2⟩

def hashState (ws : List Sig) : Nat :=
  ws.foldl (fun acc w => acc * 31 + (w.toNat &&& 255) + ((w.toNat >>> 16) &&& 255)) 0

def memBucket (tbl : List (List (List (List Sig)))) (ws : List Sig) : Bool :=
  let h := hashState ws
  let row := tbl.getD (h &&& 15) []
  let bkt := row.getD ((h >>> 4) &&& 15) []
  bkt.any (fun s => s == ws)

theorem memBucket_sound (tbl : List (List (List (List Sig)))) (P : List Sig → Prop)
    (hall : ∀ row ∈ tbl, ∀ bkt ∈ row, ∀ ws ∈ bkt, P ws)
    {ws : List Sig} (hm : memBucket tbl ws = true) : P ws := by
  unfold memBucket at hm
  set h := hashState ws
  by_cases hr : (h &&& 15) < tbl.length
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr, Option.getD_some] at hm
    set row := tbl[h &&& 15]
    have hrm : row ∈ tbl := List.getElem_mem hr
    by_cases hb : ((h >>> 4) &&& 15) < row.length
    · simp only [List.getElem?_eq_getElem hb, Option.getD_some] at hm
      set bkt := row[(h >>> 4) &&& 15]
      have hbm : bkt ∈ row := List.getElem_mem hb
      obtain ⟨s, hsm, heq⟩ := List.any_eq_true.mp hm
      rw [beq_iff_eq] at heq; subst heq
      exact hall row hrm bkt hbm s hsm
    · simp only [List.getElem?_eq_none (Nat.le_of_not_lt hb), Option.getD_none] at hm; simp at hm
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hr), Option.getD_none] at hm; simp at hm

def opsList (u : Bool) : List Nat := if u then [0, 1, 2, 3] else [0, 1]

def checkChild (ws : List Sig) (a b : Sig) (d : Nat) (k_rem : Nat)
    (nextMem : List Sig → Bool) : Bool :=
  let w := bin d a b
  if !properB w || ws.contains w then true
  else
    [false, true].all fun ka =>
      [false, true].all fun kb =>
        let ch := childCanon ws a b d ka kb
        if ch.length ≤ k_rem then nextMem ch else true

def checkPairs (u : Bool) (ws : List Sig) (k_rem : Nat) (nextMem : List Sig → Bool) : List Sig → Bool
  | [] => true
  | a :: rest =>
      rest.all (fun b => (opsList u).all fun d => checkChild ws a b d k_rem nextMem) &&
      checkPairs u ws k_rem nextMem rest

def quickPrune (u : Bool) (cap k_rem : Nat) (pairs : List (Row × Row))
    (slices : List (Sig × Nat)) (ws : List Sig) : Bool :=
  decide (k_rem + 1 < ws.length) ||
  !sepCovered u pairs ws ||
  slices.any (fun sl => decide (cap < sl.2 + ws.countP (isConstOn sl.1)))

theorem quickPrune_sound {u roots T cap k_rem pairs slices ws}
    (hnd : ws.Nodup) (hkr2 : k_rem ≤ cap)
    (hpairs : pairs.all (fun p => bit p.1 T && !(bit p.2 T)) = true)
    (hslices : ∀ sl ∈ slices, Slice u roots T sl.1 sl.2)
    (hq : quickPrune u cap k_rem pairs slices ws = true) :
    ImpossibleFrom u roots T cap k_rem ws := by
  unfold quickPrune at hq
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hq
  rcases hq with (hsz | hsep) | hslice
  · exact impossible_of_size hnd hsz
  · exact impossible_of_sep pairs hpairs hsep
  · obtain ⟨sl, hslm, hcut⟩ := List.any_eq_true.mp hslice
    exact impossible_of_slice hnd hkr2 (hslices sl hslm) (decide_eq_true_eq.mp hcut)

def checkState (u : Bool) (T : Sig) (cap k_rem : Nat) (pairs : List (Row × Row))
    (slices : List (Sig × Nat)) (nextMem : List Sig → Bool) (ws : List Sig) : Bool :=
  isSortedStrict ws &&
  (quickPrune u cap k_rem pairs slices ws ||
   (decide (0 < k_rem) && !ws.contains T && checkPairs u ws k_rem nextMem ws))

theorem checkPairs_sound {u ws k_rem nextMem} :
    ∀ {l : List Sig}, isSortedStrict l = true → checkPairs u ws k_rem nextMem l = true →
      ∀ a ∈ l, ∀ b ∈ l, a.toNat < b.toNat →
        ∀ d, allowed u d → checkChild ws a b d k_rem nextMem = true
  | [], _, _ => fun _ ha => by cases ha
  | a :: rest, hs, hc => by
    simp only [checkPairs, Bool.and_eq_true, List.all_eq_true] at hc
    have hlt_a := sortedStrict_lt hs
    have hs_rest : isSortedStrict rest = true := by
      cases rest with
      | nil => rfl
      | cons b r => exact (Bool.and_eq_true _ _ |>.mp hs).2
    intro x hx y hy hxy d hd
    have hd_mem : d ∈ opsList u := by
      rcases allowed_four hd with rfl | rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · cases u <;> simp [opsList]
      · cases u <;> simp [opsList]
      · simp [opsList]
      · simp [opsList]
    rcases List.mem_cons.mp hx with hxa | hxr
    · subst hxa
      rcases List.mem_cons.mp hy with hya | hyr
      · subst hya; omega
      · exact hc.1 y hyr d hd_mem
    · rcases List.mem_cons.mp hy with hya | hyr
      · subst hya; have := hlt_a x hxr; omega
      · exact checkPairs_sound hs_rest hc.2 x hxr y hyr hxy d hd

theorem checkState_sound {u roots T cap k_rem pairs slices nextMem ws}
    (hkr2 : k_rem ≤ cap)
    (hpairs : pairs.all (fun p => bit p.1 T && !(bit p.2 T)) = true)
    (hslices : ∀ sl ∈ slices, Slice u roots T sl.1 sl.2)
    (hnext : ∀ ch, ch.Nodup → nextMem ch = true → ImpossibleFrom u roots T cap (k_rem - 1) ch)
    (hok : checkState u T cap k_rem pairs slices nextMem ws = true) :
    ImpossibleFrom u roots T cap k_rem ws := by
  unfold checkState at hok
  simp only [Bool.and_eq_true, Bool.or_eq_true] at hok
  obtain ⟨hsort, hbody⟩ := hok
  have hnd := sortedStrict_nodup hsort
  rcases hbody with hq | ⟨⟨hpos, hout⟩, hpairs_ok⟩
  · exact quickPrune_sound hnd hkr2 hpairs hslices hq
  · have hpos' : 0 < k_rem := decide_eq_true_eq.mp hpos
    have hout' : T ∉ ws := by
      intro hm
      have hc : ws.contains T = true := List.contains_iff_mem.mpr hm
      rw [hc] at hout
      exact Bool.noConfusion hout
    refine impossible_branch hpos' hkr2 hnd hout' ?_
    intro a ha b hb hab d hd hprop hfresh ka kb hlen
    have hc := checkPairs_sound hsort hpairs_ok a ha b hb hab d hd
    unfold checkChild at hc
    have hpb : properB (bin d a b) = true := by
      simp only [properB, Bool.and_eq_true, bne_iff_ne]; exact hprop
    have hcf : ws.contains (bin d a b) = false := by
      cases h : ws.contains (bin d a b)
      · rfl
      · exact absurd (List.contains_iff_mem.mp h) hfresh
    simp only [hpb, hcf, Bool.not_true, Bool.false_or, List.all_cons, List.all_nil, Bool.and_true] at hc
    simp only [Bool.false_eq_true, ite_false, Bool.and_eq_true] at hc
    have hka : (if (childCanon ws a b d ka kb).length ≤ k_rem then nextMem (childCanon ws a b d ka kb) else true) = true := by
      cases ka <;> cases kb
      · exact hc.1.1
      · exact hc.1.2
      · exact hc.2.1
      · exact hc.2.2
    rw [if_pos hlen] at hka
    have hch_nd : (childCanon ws a b d ka kb).Nodup := by
      have hab_ne : a ≠ b := fun e => Nat.ne_of_lt hab (congrArg BitVec.toNat e)
      have hperm := perm_childCanon hnd ha hb hab_ne d ka kb
      rw [hperm.nodup_iff]
      have hrnd : ((ws.erase a).erase b).Nodup := (hnd.erase a).erase b
      have han : a ∉ (ws.erase a).erase b := fun hm => hnd.not_mem_erase (List.mem_of_mem_erase hm)
      have hbn : b ∉ (ws.erase a).erase b := (hnd.erase a).not_mem_erase
      have hkbnd : (kept kb b ((ws.erase a).erase b)).Nodup := by cases kb <;> simp [kept, hrnd, hbn]
      have hakb : a ∉ kept kb b ((ws.erase a).erase b) := by cases kb <;> simp [kept, han, hab_ne]
      have hsub_ws : ∀ z ∈ kept ka a (kept kb b ((ws.erase a).erase b)), z ∈ ws := by
        intro z hz
        rcases mem_kept hz with rfl | hz
        · exact ha
        · rcases mem_kept hz with rfl | hz
          · exact hb
          · exact List.mem_of_mem_erase (List.mem_of_mem_erase hz)
      refine List.nodup_cons.mpr ⟨fun hm => hfresh (hsub_ws _ hm), ?_⟩
      cases ka with
      | false => exact hkbnd
      | true => exact List.nodup_cons.mpr ⟨hakb, hkbnd⟩
    exact hnext _ hch_nd hka

def plainWord (a : Sig) : Bool := !(bit 0 a)

theorem nrm_map {u} {w : List Sig} (h : w.all plainWord = true) : w.map (nrm u) = w := by
  induction w with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons, Bool.and_eq_true, plainWord, Bool.not_eq_true'] at h
    simp [nrm_id h.1, ih h.2]

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b, h⟩
  cases b
  · exact hv.1 (bit_ext fun i => (congrFun h i).trans (bit_zero i).symm)
  · exact hv.2 (bit_ext fun i => (congrFun h i).trans (bit_one i).symm)

def table (f : Wire) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn

theorem bit_table (f : Wire) (r : Row) : bit r (table f) = f r := by
  simp only [bit, table, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [r.isLt]

theorem observe_table (f : Wire) : observe (table f) = f := funext (bit_table f)
theorem table_observe (a : Sig) : table (observe a) = a := bit_ext (bit_table (observe a))

theorem table_inv (f : Wire) : table (inv f) = neg (table f) :=
  bit_ext fun i => by rw [bit_table, bit_neg, bit_table]; rfl

theorem table_comb (d : Nat) (f g : Wire) : table (comb d f g) = bin d (table f) (table g) :=
  bit_ext fun i => by
    rw [bit_table, bit_bin, bit_table, bit_table]
    unfold comb; split_ifs <;> rfl

theorem available_rep {u bank a} (h : Available u bank a) :
    Repr u (bank.map (fun w => nrm u (table w))) (table a) := by
  rcases h with hm | ⟨b, rfl⟩ | ⟨rfl, hm⟩
  · left; exact List.mem_map_of_mem hm
  · cases b
    · exact repr_const (Or.inl (bit_ext fun i => by rw [bit_table, bit_zero]))
    · exact repr_const (Or.inr (bit_ext fun i => by rw [bit_table, bit_one]))
  · rw [← inv_inv a, table_inv]
    exact repr_neg (Or.inl (List.mem_map_of_mem hm))

theorem reach_live {u : Bool} {roots : List Sig} {p : Nat} {bank : List Wire} {T : Sig}
    (hp : proper T) (nT : plainWord T = true)
    (nR : roots.all plainWord = true)
    (hr : Reach u (roots.map observe) p bank) (ha : Available u bank (observe T)) :
    ∃ k S, k ≤ p ∧ Live u T k S ∧ ∀ v ∈ S, v ∈ roots := by
  have hmain : ∀ {p : Nat} {bank : List Wire}, Reach u (roots.map observe) p bank →
      ∀ {k S}, Live u T k S → (∀ v ∈ S, v ∈ bank.map (fun w => nrm u (table w))) →
      ∃ k' S', k' ≤ k + p ∧ Live u T k' S' ∧ ∀ v ∈ S', v ∈ roots := by
    intro p
    induction p with
    | zero =>
      intro bank hr k S hl hsub
      cases hr
      refine ⟨k, S, by omega, hl, fun v hv => ?_⟩
      have hm := hsub v hv
      rw [List.map_map] at hm
      obtain ⟨w, hwm, rfl⟩ := List.mem_map.mp hm
      have hpw : bit 0 w = false := by
        have := List.all_eq_true.mp nR w hwm
        simpa [plainWord] using this
      simpa [Function.comp_def, table_observe, nrm_id hpw] using hwm
    | succ p ih =>
      intro bank hr k S hl hsub
      obtain ⟨prev, a, b, d, hd, hrp, ha', hb', rfl⟩ := hr
      have hsub' : ∀ v ∈ S, v ∈ prev.map (fun w => nrm u (table w)) ++ [nrm u (table (comb d a b))] := by
        intro v hv
        rcases List.mem_cons.mp (hsub v hv) with rfl | hm
        · exact List.mem_append_right _ List.mem_cons_self
        · exact List.mem_append_left _ hm
      have hta := available_rep ha'
      have htb := available_rep hb'
      have hstep : witness u (prev.map (fun w => nrm u (table w))) (nrm u (table (comb d a b))) := by
        rw [table_comb]
        cases u with
        | false =>
          exact bin_rep d hd hta htb (fun h => Bool.noConfusion h)
        | true =>
          have hbin_eq : ∃ d' : Bool, ∃ x y : Sig,
              (x = table a ∨ x = neg (table a)) ∧ (y = table b ∨ y = neg (table b)) ∧
              bin d (table a) (table b) = prime d' x y := by
            rcases allowed_four hd with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩
            · exact ⟨false, table a, table b, Or.inl rfl, Or.inl rfl, by simp [bin, prime]⟩
            · exact ⟨true, table a, table b, Or.inl rfl, Or.inl rfl, by simp [bin, prime]⟩
            · exact ⟨false, table a, neg (table b), Or.inl rfl, Or.inr rfl, by simp [bin, prime, neg]⟩
            · exact ⟨false, neg (table a), table b, Or.inr rfl, Or.inl rfl, by simp [bin, prime, neg]⟩
          obtain ⟨d', x, y, hx, hy, heq⟩ := hbin_eq
          rw [heq]
          have hrx : Repr true (prev.map (fun w => nrm true (table w))) x := by
            rcases hx with rfl | rfl; exact hta; exact repr_neg hta
          have hry : Repr true (prev.map (fun w => nrm true (table w))) y := by
            rcases hy with rfl | rfl; exact htb; exact repr_neg htb
          exact prime_rep d' hrx hry
      obtain ⟨k1, S1, hk1, hl1, hsub1⟩ := pull_gate hl hsub' hstep rfl
      have hc : (if nrm u (table (comb d a b)) ∈ prev.map (fun w => nrm u (table w)) then 0 else 1) ≤ 1 := by
        split_ifs <;> omega
      obtain ⟨k2, S2, hk2, hl2, hsub2⟩ := ih hrp hl1 hsub1
      exact ⟨k2, S2, by omega, hl2, hsub2⟩
  have hrepT := available_rep ha
  have hT0 : bit 0 T = false := by simpa [plainWord] using nT
  rw [table_observe, Repr, nrm_id hT0] at hrepT
  have hmemT : T ∈ bank.map (fun w => nrm u (table w)) := hrepT.resolve_right (fun hn => hn hp)
  obtain ⟨k, S, hk, hl, hsub⟩ := hmain hr (Live.stop hp) (fun v hv => by rw [Finset.mem_singleton.mp hv]; exact hmemT)
  exact ⟨k, S, by omega, hl, hsub⟩

def essOk (T : Sig) (roots : List Sig) (es : List (Sig × Row × Row)) : Bool :=
  plainWord T && roots.all plainWord &&
  es.all fun e => roots.contains e.1 && (bit e.2.1 T != bit e.2.2 T) &&
    roots.all fun w => w == e.1 || bit e.2.1 w == bit e.2.2 w

theorem lower_of_count {u roots T} (hp : proper T) (es : List (Sig × Row × Row))
    (hok : essOk T roots es = true) :
    Lower u roots T ((es.map Prod.fst).toFinset.card - 1) := by
  simp only [essOk, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne] at hok
  intro p bank hr ha
  obtain ⟨k, S, hk, hlive, hsub⟩ := reach_live hp hok.1.1 (List.all_eq_true.mpr hok.1.2) hr ha
  have hle : (es.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a hma
    obtain ⟨⟨a, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hma)
    have he := hok.2 (a, r, s) hm
    exact raw_required hlive roots a hsub r s he.1.2 (fun w hw hne => (he.2 w hw).resolve_left hne)
  have hsz := live_size hlive
  omega

theorem lower_of_impossible {u roots T cap} (hp : proper T) (es : List (Sig × Row × Row))
    (hok : essOk T roots es = true) (hcov : roots.all (fun a => (es.map Prod.fst).contains a) = true)
    (himp : ImpossibleFrom u roots T cap cap roots) :
    Lower u roots T (cap + 1) := by
  simp only [essOk, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne] at hok
  intro p bank hr ha
  obtain ⟨k, S, hk, hlive, hsub⟩ := reach_live hp hok.1.1 (List.all_eq_true.mpr hok.1.2) hr ha
  have hS : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_, hsub a⟩
    have hae : a ∈ es.map Prod.fst := List.contains_iff_mem.mp (List.all_eq_true.mp hcov a hm)
    obtain ⟨⟨a, r, s⟩, hme, rfl⟩ := List.mem_map.mp hae
    have he := hok.2 (a, r, s) hme
    exact raw_required hlive roots a hsub r s he.1.2 (fun w hw hne => (he.2 w hw).resolve_left hne)
  by_contra! hlt
  have hsupp : supply u (roots.map observe) (roots.map observe) := fun x hx => Or.inl hx
  have hr0 : Reach u (roots.map observe) (cap - cap) (roots.map observe) := by simp [Reach.start]
  exact himp (roots.map observe) hr0 hsupp k (by omega) (hS.symm ▸ hlive)

def restrictRow (z o : Nat) (r : Row) : Row :=
  Fin.ofNat 64 ((r.val &&& (63 ^^^ z)) ||| o)

def freeAvail (u : Bool) (base : List Sig) (w : Sig) : Bool :=
  w == zero || w == one || base.contains w || (u && base.contains (neg w))

theorem freeAvail_sound {u base w} (h : freeAvail u base w = true) :
    Available u (base.map observe) (observe w) := by
  simp only [freeAvail, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at h
  rcases h with ((rfl | rfl) | hm) | ⟨rfl, hm⟩
  · exact Or.inr (Or.inl ⟨false, funext bit_zero⟩)
  · exact Or.inr (Or.inl ⟨true, funext bit_one⟩)
  · exact Or.inl (List.mem_map_of_mem hm)
  · exact Or.inr (Or.inr ⟨rfl, by rw [← obs_neg]; exact List.mem_map_of_mem hm⟩)

def renameSig (z o : Nat) (a : Sig) : Sig :=
  table fun r => bit (restrictRow z o r) a

theorem observe_rename (z o : Nat) (a : Sig) :
    observe (renameSig z o a) = restrictRows (restrictRow z o) (observe a) := by
  funext r; exact bit_table _ r

theorem slice_of_lower {u : Bool} {roots base : List Sig} {T G d : Sig} {z o L : Nat}
    (hdom : ∀ r : Row, bit (restrictRow z o r) d = true)
    (heq : renameSig z o T = G ∨ (u = true ∧ renameSig z o T = neg G))
    (hmap : roots.all (fun a => freeAvail u base (renameSig z o a)) = true)
    (hpG : proper G)
    (hlo : Lower u base G L) :
    Slice u roots T d L := by
  refine ⟨restrictRow z o, base, hdom, ?_, ?_, ?_⟩
  · intro a ha
    rw [← observe_rename]
    exact freeAvail_sound (List.all_eq_true.mp hmap a ha)
  · rw [← observe_rename]
    rcases heq with h | ⟨_, h⟩
    · rw [h]; exact observe_proper hpG
    · rw [h]; exact observe_proper (proper_neg (by rw [neg_neg']; exact hpG))
  · intro p bank hr ha
    rw [← observe_rename] at ha
    rcases heq with h | ⟨rfl, h⟩
    · rw [h] at ha; exact hlo p bank hr ha
    · rw [h, obs_neg] at ha
      have ha' := avail_inv rfl ha
      rw [inv_inv] at ha'
      exact hlo p bank hr ha'

def xVars : List Sig :=
  [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0,
   0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

def maskVars (m : Nat) : List Sig :=
  (List.range 6).filterMap fun i => if m.testBit i then some (xVars.getD i zero) else none

def sampleRow (r : Row) (i : Fin 6) : Bool := bit r (xVars.getD i.val zero)

theorem sampledInput (r : Row) : List.ofFn (sampleRow r) = xVars.map (bit r) := by
  rw [xVars]; rfl

theorem binaryLower_of_lower (T : Sig) (f : (Fin 6 → Bool) → Bool) (L : Nat)
    (hp : proper T) (hT0 : bit 0 T = false)
    (hmatch : ∀ r : Row, bit r T = f (sampleRow r))
    (hlo : Lower true xVars T L)
    (C : Circuit) (fit : FanInTwo C)
    (comp : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = f x) :
    L ≤ C.gates.countP (fun g => !isNot g) := by
  have ok_g : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ (true = true ∧ g.op = GateOp.not)) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨ho, hl⟩ := fit g hg
    refine ⟨?_, hl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho
    rcases ho with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨rfl, h⟩)
  have goalEq : (execute C.gates xVars).getD C.output zero = T := by
    apply bit_ext; intro r
    rw [← b_read, execute_bits _ _ _ (fun g hg => by
      obtain ⟨ho, _⟩ := ok_g g hg
      rcases ho with h | h | ⟨_, h⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)), ← sampledInput]
    exact (comp (sampleRow r)).trans (hmatch r).symm
  have out := get_rep (u := true) (execute C.gates xVars) C.output
  rw [goalEq, Repr, nrm_id hT0] at out
  obtain ⟨k, S, hk, hlive, hsub⟩ := extract (u := true) C.gates xVars ok_g hp (out.resolve_right (fun hn => hn hp))
  rw [nrm_map (by decide +kernel : xVars.all plainWord = true)] at hsub
  have hrun := list_run hlive S.toList (Finset.nodup_toList _) (by simp)
  have hsupp : supply true (xVars.map observe) (S.toList.map observe) := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
    exact Or.inl (List.mem_map_of_mem (hsub a (Finset.mem_toList.mp ha)))
  obtain ⟨q, next, hq, hhit, hle⟩ := contraction (observe_proper hp) hrun (xVars.map observe) Reach.start hsupp
  have hL := hlo q next hq hhit
  omega


def c568_roots : List Sig := maskVars 14
def c568_T : Sig := 0xfcc0fcc0fcc0fcc0
def c568_es : List (Sig × Row × Row) := [(xVars.getD 1 zero, ⟨4, by decide⟩, ⟨6, by decide⟩), (xVars.getD 2 zero, ⟨2, by decide⟩, ⟨6, by decide⟩), (xVars.getD 3 zero, ⟨2, by decide⟩, ⟨10, by decide⟩)]
def c568_sep : List (Row × Row) := [(⟨6, by decide⟩, ⟨2, by decide⟩), (⟨6, by decide⟩, ⟨4, by decide⟩), (⟨10, by decide⟩, ⟨2, by decide⟩), (⟨10, by decide⟩, ⟨8, by decide⟩), (⟨12, by decide⟩, ⟨4, by decide⟩), (⟨12, by decide⟩, ⟨8, by decide⟩)]
theorem c568_sep_ok : c568_sep.all (fun p => bit p.1 c568_T && !(bit p.2 c568_T)) = true := by decide +kernel
def c568_slices : List (Sig × Nat) := []
theorem c568_slices_ok : ∀ sl ∈ c568_slices, Slice true c568_roots c568_T sl.1 sl.2 := by
  intro sl hsl; cases hsl
def c568_tbl_1 : List (List (List (List Sig))) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
theorem c568_lvl_1 : ∀ ch, memBucket c568_tbl_1 ch = true → ImpossibleFrom true c568_roots c568_T 3 1 ch := by
  intro ch hch
  apply memBucket_sound c568_tbl_1 (ImpossibleFrom true c568_roots c568_T 3 1) _ hch
  intro row hrow bkt hbkt ws hws
  have hcs : checkState true c568_T 3 1 c568_sep c568_slices (fun ch => !ch.contains c568_T) ws = true := by
    simp only [c568_tbl_1, List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases hbkt
  refine checkState_sound (by omega) c568_sep_ok c568_slices_ok ?_ hcs
  intro ch' hnd' hmem'
  apply impossible_zero
  intro hm; have hc : ch'.contains c568_T = true := List.contains_iff_mem.mpr hm; rw [hc] at hmem'; exact Bool.noConfusion hmem'
def c568_tbl_2 : List (List (List (List Sig))) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
theorem c568_lvl_2 : ∀ ch, memBucket c568_tbl_2 ch = true → ImpossibleFrom true c568_roots c568_T 3 2 ch := by
  intro ch hch
  apply memBucket_sound c568_tbl_2 (ImpossibleFrom true c568_roots c568_T 3 2) _ hch
  intro row hrow bkt hbkt ws hws
  have hcs : checkState true c568_T 3 2 c568_sep c568_slices (fun ch => quickPrune true 3 1 c568_sep c568_slices ch || memBucket c568_tbl_1 ch) ws = true := by
    simp only [c568_tbl_2, List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases hbkt
  refine checkState_sound (by omega) c568_sep_ok c568_slices_ok ?_ hcs
  intro ch' hnd' hmem'
  simp only [Bool.or_eq_true] at hmem'
  rcases hmem' with hq | hm
  · exact quickPrune_sound hnd' (by omega) c568_sep_ok c568_slices_ok hq
  · exact c568_lvl_1 ch' hm
def c568_t3_r8 : List (List (List Sig)) := [[], [], [], [], [], [], [], [], [], [], [], [[0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]], [], [], [], []]
def c568_tbl_3 : List (List (List (List Sig))) := [[], [], [], [], [], [], [], [], c568_t3_r8, [], [], [], [], [], [], []]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c568_ok_3_r8 : c568_t3_r8.all (fun bkt => bkt.all (checkState true c568_T 3 3 c568_sep c568_slices (fun ch => quickPrune true 3 2 c568_sep c568_slices ch || memBucket c568_tbl_2 ch))) = true := by decide +kernel
theorem c568_lvl_3 : ∀ ch, memBucket c568_tbl_3 ch = true → ImpossibleFrom true c568_roots c568_T 3 3 ch := by
  intro ch hch
  apply memBucket_sound c568_tbl_3 (ImpossibleFrom true c568_roots c568_T 3 3) _ hch
  intro row hrow bkt hbkt ws hws
  have hcs : checkState true c568_T 3 3 c568_sep c568_slices (fun ch => quickPrune true 3 2 c568_sep c568_slices ch || memBucket c568_tbl_2 ch) ws = true := by
    simp only [c568_tbl_3, List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · cases hbkt
    · cases hbkt
    · cases hbkt
    · cases hbkt
    · cases hbkt
    · cases hbkt
    · cases hbkt
    · cases hbkt
    · exact List.all_eq_true.mp (List.all_eq_true.mp c568_ok_3_r8 bkt hbkt) ws hws
    · cases hbkt
    · cases hbkt
    · cases hbkt
    · cases hbkt
    · cases hbkt
    · cases hbkt
    · cases hbkt
  refine checkState_sound (by omega) c568_sep_ok c568_slices_ok ?_ hcs
  intro ch' hnd' hmem'
  simp only [Bool.or_eq_true] at hmem'
  rcases hmem' with hq | hm
  · exact quickPrune_sound hnd' (by omega) c568_sep_ok c568_slices_ok hq
  · exact c568_lvl_2 ch' hm
theorem c568_lower : Lower true c568_roots c568_T 4 := by
  refine lower_of_impossible (cap := 3) (by unfold proper; decide +kernel) c568_es (by decide +kernel) (by decide +kernel) ?_
  exact c568_lvl_3 c568_roots (by decide +kernel)

def c649_roots : List Sig := maskVars 14
def c649_T : Sig := 0xfcc0fcc0fcc0fcc0
def c649_es : List (Sig × Row × Row) := [(xVars.getD 1 zero, ⟨4, by decide⟩, ⟨6, by decide⟩), (xVars.getD 2 zero, ⟨2, by decide⟩, ⟨6, by decide⟩), (xVars.getD 3 zero, ⟨2, by decide⟩, ⟨10, by decide⟩)]
def c649_sep : List (Row × Row) := [(⟨6, by decide⟩, ⟨2, by decide⟩), (⟨6, by decide⟩, ⟨4, by decide⟩), (⟨10, by decide⟩, ⟨2, by decide⟩), (⟨10, by decide⟩, ⟨8, by decide⟩), (⟨12, by decide⟩, ⟨4, by decide⟩), (⟨12, by decide⟩, ⟨8, by decide⟩)]
theorem c649_sep_ok : c649_sep.all (fun p => bit p.1 c649_T && !(bit p.2 c649_T)) = true := by decide +kernel
def c649_slices : List (Sig × Nat) := []
theorem c649_slices_ok : ∀ sl ∈ c649_slices, Slice true c649_roots c649_T sl.1 sl.2 := by
  intro sl hsl; cases hsl
def c649_tbl_1 : List (List (List (List Sig))) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
theorem c649_lvl_1 : ∀ ch, memBucket c649_tbl_1 ch = true → ImpossibleFrom true c649_roots c649_T 3 1 ch := by
  intro ch hch
  apply memBucket_sound c649_tbl_1 (ImpossibleFrom true c649_roots c649_T 3 1) _ hch
  intro row hrow bkt hbkt ws hws
  have hcs : checkState true c649_T 3 1 c649_sep c649_slices (fun ch => !ch.contains c649_T) ws = true := by
    simp only [c649_tbl_1, List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases hbkt
  refine checkState_sound (by omega) c649_sep_ok c649_slices_ok ?_ hcs
  intro ch' hnd' hmem'
  apply impossible_zero
  intro hm; have hc : ch'.contains c649_T = true := List.contains_iff_mem.mpr hm; rw [hc] at hmem'; exact Bool.noConfusion hmem'
def c649_tbl_2 : List (List (List (List Sig))) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
theorem c649_lvl_2 : ∀ ch, memBucket c649_tbl_2 ch = true → ImpossibleFrom true c649_roots c649_T 3 2 ch := by
  intro ch hch
  apply memBucket_sound c649_tbl_2 (ImpossibleFrom true c649_roots c649_T 3 2) _ hch
  intro row hrow bkt hbkt ws hws
  have hcs : checkState true c649_T 3 2 c649_sep c649_slices (fun ch => quickPrune true 3 1 c649_sep c649_slices ch || memBucket c649_tbl_1 ch) ws = true := by
    simp only [c649_tbl_2, List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases hbkt
  refine checkState_sound (by omega) c649_sep_ok c649_slices_ok ?_ hcs
  intro ch' hnd' hmem'
  simp only [Bool.or_eq_true] at hmem'
  rcases hmem' with hq | hm
  · exact quickPrune_sound hnd' (by omega) c649_sep_ok c649_slices_ok hq
  · exact c649_lvl_1 ch' hm
def c649_t3_r8 : List (List (List Sig)) := [[], [], [], [], [], [], [], [], [], [], [], [[0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]], [], [], [], []]
def c649_tbl_3 : List (List (List (List Sig))) := [[], [], [], [], [], [], [], [], c649_t3_r8, [], [], [], [], [], [], []]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c649_ok_3_r8 : c649_t3_r8.all (fun bkt => bkt.all (checkState true c649_T 3 3 c649_sep c649_slices (fun ch => quickPrune true 3 2 c649_sep c649_slices ch || memBucket c649_tbl_2 ch))) = true := by decide +kernel
theorem c649_lvl_3 : ∀ ch, memBucket c649_tbl_3 ch = true → ImpossibleFrom true c649_roots c649_T 3 3 ch := by
  intro ch hch
  apply memBucket_sound c649_tbl_3 (ImpossibleFrom true c649_roots c649_T 3 3) _ hch
  intro row hrow bkt hbkt ws hws
  have hcs : checkState true c649_T 3 3 c649_sep c649_slices (fun ch => quickPrune true 3 2 c649_sep c649_slices ch || memBucket c649_tbl_2 ch) ws = true := by
    simp only [c649_tbl_3, List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · cases hbkt
    · cases hbkt
    · cases hbkt
    · cases hbkt
    · cases hbkt
    · cases hbkt
    · cases hbkt
    · cases hbkt
    · exact List.all_eq_true.mp (List.all_eq_true.mp c649_ok_3_r8 bkt hbkt) ws hws
    · cases hbkt
    · cases hbkt
    · cases hbkt
    · cases hbkt
    · cases hbkt
    · cases hbkt
    · cases hbkt
  refine checkState_sound (by omega) c649_sep_ok c649_slices_ok ?_ hcs
  intro ch' hnd' hmem'
  simp only [Bool.or_eq_true] at hmem'
  rcases hmem' with hq | hm
  · exact quickPrune_sound hnd' (by omega) c649_sep_ok c649_slices_ok hq
  · exact c649_lvl_2 ch' hm
theorem c649_lower : Lower true c649_roots c649_T 4 := by
  refine lower_of_impossible (cap := 3) (by unfold proper; decide +kernel) c649_es (by decide +kernel) (by decide +kernel) ?_
  exact c649_lvl_3 c649_roots (by decide +kernel)

def c567_roots : List Sig := maskVars 15
def c567_T : Sig := 0xfcc8fcc8fcc8fcc8
def c567_es : List (Sig × Row × Row) := [(xVars.getD 0 zero, ⟨2, by decide⟩, ⟨3, by decide⟩), (xVars.getD 1 zero, ⟨1, by decide⟩, ⟨3, by decide⟩), (xVars.getD 2 zero, ⟨2, by decide⟩, ⟨6, by decide⟩), (xVars.getD 3 zero, ⟨2, by decide⟩, ⟨10, by decide⟩)]
def c567_sep : List (Row × Row) := []
theorem c567_sep_ok : c567_sep.all (fun p => bit p.1 c567_T && !(bit p.2 c567_T)) = true := by decide +kernel
def c567_slices : List (Sig × Nat) := [(0x555500000000, 4)]
theorem c567_slices_ok : ∀ sl ∈ c567_slices, Slice true c567_roots c567_T sl.1 sl.2 := by
  intro sl hsl
  simp only [c567_slices, List.mem_cons, List.not_mem_nil, or_false] at hsl
  rcases hsl with rfl
  · exact slice_of_lower (u := true) (z := 17) (o := 32) (by decide +kernel) (Or.inl (by decide +kernel)) (by decide +kernel) (by unfold proper; decide +kernel) c568_lower
def c567_tbl_1 : List (List (List (List Sig))) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
theorem c567_lvl_1 : ∀ ch, memBucket c567_tbl_1 ch = true → ImpossibleFrom true c567_roots c567_T 4 1 ch := by
  intro ch hch
  apply memBucket_sound c567_tbl_1 (ImpossibleFrom true c567_roots c567_T 4 1) _ hch
  intro row hrow bkt hbkt ws hws
  have hcs : checkState true c567_T 4 1 c567_sep c567_slices (fun ch => !ch.contains c567_T) ws = true := by
    simp only [c567_tbl_1, List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases hbkt
  refine checkState_sound (by omega) c567_sep_ok c567_slices_ok ?_ hcs
  intro ch' hnd' hmem'
  apply impossible_zero
  intro hm; have hc : ch'.contains c567_T = true := List.contains_iff_mem.mpr hm; rw [hc] at hmem'; exact Bool.noConfusion hmem'
def c567_tbl_2 : List (List (List (List Sig))) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
theorem c567_lvl_2 : ∀ ch, memBucket c567_tbl_2 ch = true → ImpossibleFrom true c567_roots c567_T 4 2 ch := by
  intro ch hch
  apply memBucket_sound c567_tbl_2 (ImpossibleFrom true c567_roots c567_T 4 2) _ hch
  intro row hrow bkt hbkt ws hws
  have hcs : checkState true c567_T 4 2 c567_sep c567_slices (fun ch => quickPrune true 4 1 c567_sep c567_slices ch || memBucket c567_tbl_1 ch) ws = true := by
    simp only [c567_tbl_2, List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases hbkt
  refine checkState_sound (by omega) c567_sep_ok c567_slices_ok ?_ hcs
  intro ch' hnd' hmem'
  simp only [Bool.or_eq_true] at hmem'
  rcases hmem' with hq | hm
  · exact quickPrune_sound hnd' (by omega) c567_sep_ok c567_slices_ok hq
  · exact c567_lvl_1 ch' hm
def c567_tbl_3 : List (List (List (List Sig))) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
theorem c567_lvl_3 : ∀ ch, memBucket c567_tbl_3 ch = true → ImpossibleFrom true c567_roots c567_T 4 3 ch := by
  intro ch hch
  apply memBucket_sound c567_tbl_3 (ImpossibleFrom true c567_roots c567_T 4 3) _ hch
  intro row hrow bkt hbkt ws hws
  have hcs : checkState true c567_T 4 3 c567_sep c567_slices (fun ch => quickPrune true 4 2 c567_sep c567_slices ch || memBucket c567_tbl_2 ch) ws = true := by
    simp only [c567_tbl_3, List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases hbkt
  refine checkState_sound (by omega) c567_sep_ok c567_slices_ok ?_ hcs
  intro ch' hnd' hmem'
  simp only [Bool.or_eq_true] at hmem'
  rcases hmem' with hq | hm
  · exact quickPrune_sound hnd' (by omega) c567_sep_ok c567_slices_ok hq
  · exact c567_lvl_2 ch' hm
def c567_tbl_4 : List (List (List (List Sig))) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
theorem c567_lvl_4 : ∀ ch, memBucket c567_tbl_4 ch = true → ImpossibleFrom true c567_roots c567_T 4 4 ch := by
  intro ch hch
  apply memBucket_sound c567_tbl_4 (ImpossibleFrom true c567_roots c567_T 4 4) _ hch
  intro row hrow bkt hbkt ws hws
  have hcs : checkState true c567_T 4 4 c567_sep c567_slices (fun ch => quickPrune true 4 3 c567_sep c567_slices ch || memBucket c567_tbl_3 ch) ws = true := by
    simp only [c567_tbl_4, List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases hbkt
  refine checkState_sound (by omega) c567_sep_ok c567_slices_ok ?_ hcs
  intro ch' hnd' hmem'
  simp only [Bool.or_eq_true] at hmem'
  rcases hmem' with hq | hm
  · exact quickPrune_sound hnd' (by omega) c567_sep_ok c567_slices_ok hq
  · exact c567_lvl_3 ch' hm
theorem c567_lower : Lower true c567_roots c567_T 5 := by
  refine lower_of_impossible (cap := 4) (by unfold proper; decide +kernel) c567_es (by decide +kernel) (by decide +kernel) ?_
  exact quickPrune_sound (sortedStrict_nodup (by decide +kernel : isSortedStrict c567_roots = true)) le_rfl c567_sep_ok c567_slices_ok (by decide +kernel)

def c648_roots : List Sig := maskVars 15
def c648_T : Sig := 0xfeeafeeafeeafeea
def c648_es : List (Sig × Row × Row) := [(xVars.getD 0 zero, ⟨0, by decide⟩, ⟨1, by decide⟩), (xVars.getD 1 zero, ⟨4, by decide⟩, ⟨6, by decide⟩), (xVars.getD 2 zero, ⟨2, by decide⟩, ⟨6, by decide⟩), (xVars.getD 3 zero, ⟨2, by decide⟩, ⟨10, by decide⟩)]
def c648_sep : List (Row × Row) := []
theorem c648_sep_ok : c648_sep.all (fun p => bit p.1 c648_T && !(bit p.2 c648_T)) = true := by decide +kernel
def c648_slices : List (Sig × Nat) := [(0x5555000000000000, 4)]
theorem c648_slices_ok : ∀ sl ∈ c648_slices, Slice true c648_roots c648_T sl.1 sl.2 := by
  intro sl hsl
  simp only [c648_slices, List.mem_cons, List.not_mem_nil, or_false] at hsl
  rcases hsl with rfl
  · exact slice_of_lower (u := true) (z := 1) (o := 48) (by decide +kernel) (Or.inl (by decide +kernel)) (by decide +kernel) (by unfold proper; decide +kernel) c649_lower
def c648_tbl_1 : List (List (List (List Sig))) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
theorem c648_lvl_1 : ∀ ch, memBucket c648_tbl_1 ch = true → ImpossibleFrom true c648_roots c648_T 4 1 ch := by
  intro ch hch
  apply memBucket_sound c648_tbl_1 (ImpossibleFrom true c648_roots c648_T 4 1) _ hch
  intro row hrow bkt hbkt ws hws
  have hcs : checkState true c648_T 4 1 c648_sep c648_slices (fun ch => !ch.contains c648_T) ws = true := by
    simp only [c648_tbl_1, List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases hbkt
  refine checkState_sound (by omega) c648_sep_ok c648_slices_ok ?_ hcs
  intro ch' hnd' hmem'
  apply impossible_zero
  intro hm; have hc : ch'.contains c648_T = true := List.contains_iff_mem.mpr hm; rw [hc] at hmem'; exact Bool.noConfusion hmem'
def c648_tbl_2 : List (List (List (List Sig))) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
theorem c648_lvl_2 : ∀ ch, memBucket c648_tbl_2 ch = true → ImpossibleFrom true c648_roots c648_T 4 2 ch := by
  intro ch hch
  apply memBucket_sound c648_tbl_2 (ImpossibleFrom true c648_roots c648_T 4 2) _ hch
  intro row hrow bkt hbkt ws hws
  have hcs : checkState true c648_T 4 2 c648_sep c648_slices (fun ch => quickPrune true 4 1 c648_sep c648_slices ch || memBucket c648_tbl_1 ch) ws = true := by
    simp only [c648_tbl_2, List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases hbkt
  refine checkState_sound (by omega) c648_sep_ok c648_slices_ok ?_ hcs
  intro ch' hnd' hmem'
  simp only [Bool.or_eq_true] at hmem'
  rcases hmem' with hq | hm
  · exact quickPrune_sound hnd' (by omega) c648_sep_ok c648_slices_ok hq
  · exact c648_lvl_1 ch' hm
def c648_tbl_3 : List (List (List (List Sig))) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
theorem c648_lvl_3 : ∀ ch, memBucket c648_tbl_3 ch = true → ImpossibleFrom true c648_roots c648_T 4 3 ch := by
  intro ch hch
  apply memBucket_sound c648_tbl_3 (ImpossibleFrom true c648_roots c648_T 4 3) _ hch
  intro row hrow bkt hbkt ws hws
  have hcs : checkState true c648_T 4 3 c648_sep c648_slices (fun ch => quickPrune true 4 2 c648_sep c648_slices ch || memBucket c648_tbl_2 ch) ws = true := by
    simp only [c648_tbl_3, List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases hbkt
  refine checkState_sound (by omega) c648_sep_ok c648_slices_ok ?_ hcs
  intro ch' hnd' hmem'
  simp only [Bool.or_eq_true] at hmem'
  rcases hmem' with hq | hm
  · exact quickPrune_sound hnd' (by omega) c648_sep_ok c648_slices_ok hq
  · exact c648_lvl_2 ch' hm
def c648_tbl_4 : List (List (List (List Sig))) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
theorem c648_lvl_4 : ∀ ch, memBucket c648_tbl_4 ch = true → ImpossibleFrom true c648_roots c648_T 4 4 ch := by
  intro ch hch
  apply memBucket_sound c648_tbl_4 (ImpossibleFrom true c648_roots c648_T 4 4) _ hch
  intro row hrow bkt hbkt ws hws
  have hcs : checkState true c648_T 4 4 c648_sep c648_slices (fun ch => quickPrune true 4 3 c648_sep c648_slices ch || memBucket c648_tbl_3 ch) ws = true := by
    simp only [c648_tbl_4, List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases hbkt
  refine checkState_sound (by omega) c648_sep_ok c648_slices_ok ?_ hcs
  intro ch' hnd' hmem'
  simp only [Bool.or_eq_true] at hmem'
  rcases hmem' with hq | hm
  · exact quickPrune_sound hnd' (by omega) c648_sep_ok c648_slices_ok hq
  · exact c648_lvl_3 ch' hm
theorem c648_lower : Lower true c648_roots c648_T 5 := by
  refine lower_of_impossible (cap := 4) (by unfold proper; decide +kernel) c648_es (by decide +kernel) (by decide +kernel) ?_
  exact quickPrune_sound (sortedStrict_nodup (by decide +kernel : isSortedStrict c648_roots = true)) le_rfl c648_sep_ok c648_slices_ok (by decide +kernel)

def c486_roots : List Sig := maskVars 31
def c486_T : Sig := 0xfeeafcc8feeafcc8
def c486_es : List (Sig × Row × Row) := [(xVars.getD 0 zero, ⟨2, by decide⟩, ⟨3, by decide⟩), (xVars.getD 1 zero, ⟨1, by decide⟩, ⟨3, by decide⟩), (xVars.getD 2 zero, ⟨2, by decide⟩, ⟨6, by decide⟩), (xVars.getD 3 zero, ⟨2, by decide⟩, ⟨10, by decide⟩), (xVars.getD 4 zero, ⟨1, by decide⟩, ⟨17, by decide⟩)]
def c486_sep : List (Row × Row) := [(⟨3, by decide⟩, ⟨1, by decide⟩), (⟨3, by decide⟩, ⟨2, by decide⟩), (⟨3, by decide⟩, ⟨5, by decide⟩), (⟨3, by decide⟩, ⟨9, by decide⟩), (⟨3, by decide⟩, ⟨18, by decide⟩), (⟨3, by decide⟩, ⟨20, by decide⟩), (⟨3, by decide⟩, ⟨24, by decide⟩), (⟨6, by decide⟩, ⟨2, by decide⟩), (⟨6, by decide⟩, ⟨4, by decide⟩), (⟨6, by decide⟩, ⟨5, by decide⟩), (⟨6, by decide⟩, ⟨9, by decide⟩), (⟨6, by decide⟩, ⟨18, by decide⟩), (⟨6, by decide⟩, ⟨20, by decide⟩), (⟨6, by decide⟩, ⟨24, by decide⟩), (⟨7, by decide⟩, ⟨5, by decide⟩), (⟨10, by decide⟩, ⟨2, by decide⟩), (⟨10, by decide⟩, ⟨5, by decide⟩), (⟨10, by decide⟩, ⟨8, by decide⟩), (⟨10, by decide⟩, ⟨9, by decide⟩), (⟨10, by decide⟩, ⟨18, by decide⟩), (⟨10, by decide⟩, ⟨20, by decide⟩), (⟨10, by decide⟩, ⟨24, by decide⟩), (⟨11, by decide⟩, ⟨9, by decide⟩), (⟨12, by decide⟩, ⟨4, by decide⟩), (⟨12, by decide⟩, ⟨5, by decide⟩), (⟨12, by decide⟩, ⟨8, by decide⟩), (⟨12, by decide⟩, ⟨9, by decide⟩), (⟨12, by decide⟩, ⟨18, by decide⟩), (⟨12, by decide⟩, ⟨20, by decide⟩), (⟨12, by decide⟩, ⟨24, by decide⟩), (⟨13, by decide⟩, ⟨5, by decide⟩), (⟨13, by decide⟩, ⟨9, by decide⟩), (⟨17, by decide⟩, ⟨1, by decide⟩), (⟨17, by decide⟩, ⟨5, by decide⟩), (⟨17, by decide⟩, ⟨9, by decide⟩), (⟨17, by decide⟩, ⟨16, by decide⟩), (⟨17, by decide⟩, ⟨18, by decide⟩), (⟨17, by decide⟩, ⟨20, by decide⟩), (⟨17, by decide⟩, ⟨24, by decide⟩), (⟨19, by decide⟩, ⟨18, by decide⟩), (⟨21, by decide⟩, ⟨5, by decide⟩), (⟨21, by decide⟩, ⟨20, by decide⟩), (⟨22, by decide⟩, ⟨18, by decide⟩), (⟨22, by decide⟩, ⟨20, by decide⟩), (⟨25, by decide⟩, ⟨9, by decide⟩), (⟨25, by decide⟩, ⟨24, by decide⟩), (⟨26, by decide⟩, ⟨18, by decide⟩), (⟨28, by decide⟩, ⟨20, by decide⟩), (⟨28, by decide⟩, ⟨24, by decide⟩)]
theorem c486_sep_ok : c486_sep.all (fun p => bit p.1 c486_T && !(bit p.2 c486_T)) = true := by decide +kernel
def c486_slices : List (Sig × Nat) := [(0xffff00000000, 5), (0x555500000000, 4), (0xffff000000000000, 5)]
theorem c486_slices_ok : ∀ sl ∈ c486_slices, Slice true c486_roots c486_T sl.1 sl.2 := by
  intro sl hsl
  simp only [c486_slices, List.mem_cons, List.not_mem_nil, or_false] at hsl
  rcases hsl with rfl | rfl | rfl
  · exact slice_of_lower (u := true) (z := 16) (o := 32) (by decide +kernel) (Or.inl (by decide +kernel)) (by decide +kernel) (by unfold proper; decide +kernel) c567_lower
  · exact slice_of_lower (u := true) (z := 17) (o := 32) (by decide +kernel) (Or.inl (by decide +kernel)) (by decide +kernel) (by unfold proper; decide +kernel) c568_lower
  · exact slice_of_lower (u := true) (z := 0) (o := 48) (by decide +kernel) (Or.inl (by decide +kernel)) (by decide +kernel) (by unfold proper; decide +kernel) c648_lower
def c486_tbl_1 : List (List (List (List Sig))) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
theorem c486_lvl_1 : ∀ ch, memBucket c486_tbl_1 ch = true → ImpossibleFrom true c486_roots c486_T 6 1 ch := by
  intro ch hch
  apply memBucket_sound c486_tbl_1 (ImpossibleFrom true c486_roots c486_T 6 1) _ hch
  intro row hrow bkt hbkt ws hws
  have hcs : checkState true c486_T 6 1 c486_sep c486_slices (fun ch => !ch.contains c486_T) ws = true := by
    simp only [c486_tbl_1, List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases hbkt
  refine checkState_sound (by omega) c486_sep_ok c486_slices_ok ?_ hcs
  intro ch' hnd' hmem'
  apply impossible_zero
  intro hm; have hc : ch'.contains c486_T = true := List.contains_iff_mem.mpr hm; rw [hc] at hmem'; exact Bool.noConfusion hmem'
def c486_t2_r6 : List (List (List Sig)) := [[], [], [], [], [], [], [], [], [], [], [], [], [[0xeeeecccceeeecccc, 0xf0faf0faf0faf0fa, 0xff00ff00ff00ff00]], [], [], []]
def c486_t2_r8 : List (List (List Sig)) := [[], [[0xcccccccccccccccc, 0xfafaf8f8fafaf8f8, 0xffaaff88ffaaff88]], [], [], [], [], [], [], [[0xeeeecccceeeecccc, 0xfafaf8f8fafaf8f8, 0xff00ff00ff00ff00]], [], [], [], [], [], [], []]
def c486_t2_r12 : List (List (List Sig)) := [[], [], [], [], [], [], [], [], [[0xeeeecccceeeecccc, 0xf0f0f0f0f0f0f0f0, 0xffaaff88ffaaff88]], [], [], [], [], [], [], []]
def c486_t2_r14 : List (List (List Sig)) := [[], [], [], [], [], [], [[0xeeeecccceeeecccc, 0xf0f0f0f0f0f0f0f0, 0xff0aff0aff0aff0a]], [], [], [], [], [], [], [], [], []]
def c486_tbl_2 : List (List (List (List Sig))) := [[], [], [], [], [], [], c486_t2_r6, [], c486_t2_r8, [], [], [], c486_t2_r12, [], c486_t2_r14, []]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c486_ok_2_r6 : c486_t2_r6.all (fun bkt => bkt.all (checkState true c486_T 6 2 c486_sep c486_slices (fun ch => quickPrune true 6 1 c486_sep c486_slices ch || memBucket c486_tbl_1 ch))) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c486_ok_2_r8 : c486_t2_r8.all (fun bkt => bkt.all (checkState true c486_T 6 2 c486_sep c486_slices (fun ch => quickPrune true 6 1 c486_sep c486_slices ch || memBucket c486_tbl_1 ch))) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c486_ok_2_r12 : c486_t2_r12.all (fun bkt => bkt.all (checkState true c486_T 6 2 c486_sep c486_slices (fun ch => quickPrune true 6 1 c486_sep c486_slices ch || memBucket c486_tbl_1 ch))) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c486_ok_2_r14 : c486_t2_r14.all (fun bkt => bkt.all (checkState true c486_T 6 2 c486_sep c486_slices (fun ch => quickPrune true 6 1 c486_sep c486_slices ch || memBucket c486_tbl_1 ch))) = true := by decide +kernel
theorem c486_lvl_2 : ∀ ch, memBucket c486_tbl_2 ch = true → ImpossibleFrom true c486_roots c486_T 6 2 ch := by
  intro ch hch
  apply memBucket_sound c486_tbl_2 (ImpossibleFrom true c486_roots c486_T 6 2) _ hch
  intro row hrow bkt hbkt ws hws
  have hcs : checkState true c486_T 6 2 c486_sep c486_slices (fun ch => quickPrune true 6 1 c486_sep c486_slices ch || memBucket c486_tbl_1 ch) ws = true := by
    simp only [c486_tbl_2, List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · cases hbkt
    · cases hbkt
    · cases hbkt
    · cases hbkt
    · cases hbkt
    · cases hbkt
    · exact List.all_eq_true.mp (List.all_eq_true.mp c486_ok_2_r6 bkt hbkt) ws hws
    · cases hbkt
    · exact List.all_eq_true.mp (List.all_eq_true.mp c486_ok_2_r8 bkt hbkt) ws hws
    · cases hbkt
    · cases hbkt
    · cases hbkt
    · exact List.all_eq_true.mp (List.all_eq_true.mp c486_ok_2_r12 bkt hbkt) ws hws
    · cases hbkt
    · exact List.all_eq_true.mp (List.all_eq_true.mp c486_ok_2_r14 bkt hbkt) ws hws
    · cases hbkt
  refine checkState_sound (by omega) c486_sep_ok c486_slices_ok ?_ hcs
  intro ch' hnd' hmem'
  simp only [Bool.or_eq_true] at hmem'
  rcases hmem' with hq | hm
  · exact quickPrune_sound hnd' (by omega) c486_sep_ok c486_slices_ok hq
  · exact c486_lvl_1 ch' hm
def c486_t3_r0 : List (List (List Sig)) := [[], [], [], [[0xaaaaaaaaaaaaaaaa, 0xeeeecccceeeecccc, 0xf0f0f0f0f0f0f0f0, 0xffaaff00ffaaff00]], [], [], [], [], [], [], [], [], [], [], [], []]
def c486_t3_r2 : List (List (List Sig)) := [[], [], [], [], [], [], [], [[0xeeeecccceeeecccc, 0xf0f0f0f0f0f0f0f0, 0xfafafafafafafafa, 0xff00ff00ff00ff00]], [], [], [], [], [], [[0x4444444444444444, 0xeeeecccceeeecccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]], [[0xaaaa0000aaaa0000, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff0aff0aff0aff0a]], []]
def c486_t3_r3 : List (List (List Sig)) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [[0xaaaaaaaaaaaaaaaa, 0xfcccfcccfcccfccc, 0xfff0fff0fff0fff0, 0xffff0000ffff0000]], []]
def c486_t3_r4 : List (List (List Sig)) := [[], [], [], [], [], [], [], [[0xaaaa8888aaaa8888, 0xcccccccccccccccc, 0xfafaf8f8fafaf8f8, 0xff00ff00ff00ff00]], [], [], [], [], [[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xfafaf0f0fafaf0f0, 0xffaaff00ffaaff00]], [], [], []]
def c486_t3_r6 : List (List (List Sig)) := [[], [], [], [], [[0xaaaa8888aaaa8888, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00], [0xaaaa0088aaaa0088, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]], [], [], [], [[0xaaaaaaaaaaaaaaaa, 0xeeeecccceeeecccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00], [0xaa00aa00aa00aa, 0xeeeecccceeeecccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]], [], [], [], [[0xa0a0a0a0a0a0a0a, 0xeeeecccceeeecccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00], [0xaaaa0808aaaa0808, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]], [], [], []]
def c486_t3_r8 : List (List (List Sig)) := [[], [], [], [], [], [], [], [[0xaaaa8888aaaa8888, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xffaaff88ffaaff88]], [], [], [], [], [], [], [[0xaaaa8888aaaa8888, 0xeeeecccceeeecccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]], []]
def c486_t3_r10 : List (List (List Sig)) := [[], [], [], [[0xeeeecccceeeecccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffaaffaaffaaffaa], [0xaaaa0000aaaa0000, 0xcccccccccccccccc, 0xf0faf0faf0faf0fa, 0xff00ff00ff00ff00]], [[0x4444444444444444, 0xaaaa8888aaaa8888, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]], [[0x5050707050507070, 0xaaaa8888aaaa8888, 0xcccccccccccccccc, 0xff00ff00ff00ff00]], [], [], [], [[0x5050f0f05050f0f0, 0xaaaaaaaaaaaaaaaa, 0xeeeecccceeeecccc, 0xff00ff00ff00ff00]], [], [[0x5500ff005500ff00, 0xaaaaaaaaaaaaaaaa, 0xeeeecccceeeecccc, 0xf0f0f0f0f0f0f0f0]], [], [], [], [[0x5500770055007700, 0xaaaa8888aaaa8888, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0]]]
def c486_t3_r11 : List (List (List Sig)) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [[0xff00ff00ff00ff0, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xffff0000ffff0000]], [], []]
def c486_t3_r12 : List (List (List Sig)) := [[], [], [], [], [], [], [], [], [], [], [], [[0xaaaaaaaaaaaaaaaa, 0xeeeecccceeeecccc, 0xfafaf0f0fafaf0f0, 0xff00ff00ff00ff00]], [], [], [], []]
def c486_t3_r14 : List (List (List Sig)) := [[], [], [], [], [], [], [], [], [], [], [], [[0xaaaa0000aaaa0000, 0xcccccccccccccccc, 0xf8f8f8f8f8f8f8f8, 0xff00ff00ff00ff00]], [], [[0xaaaa0000aaaa0000, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff88ff88ff88ff88]], [], []]
def c486_tbl_3 : List (List (List (List Sig))) := [c486_t3_r0, [], c486_t3_r2, c486_t3_r3, c486_t3_r4, [], c486_t3_r6, [], c486_t3_r8, [], c486_t3_r10, c486_t3_r11, c486_t3_r12, [], c486_t3_r14, []]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c486_ok_3_r0 : c486_t3_r0.all (fun bkt => bkt.all (checkState true c486_T 6 3 c486_sep c486_slices (fun ch => quickPrune true 6 2 c486_sep c486_slices ch || memBucket c486_tbl_2 ch))) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c486_ok_3_r2 : c486_t3_r2.all (fun bkt => bkt.all (checkState true c486_T 6 3 c486_sep c486_slices (fun ch => quickPrune true 6 2 c486_sep c486_slices ch || memBucket c486_tbl_2 ch))) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c486_ok_3_r3 : c486_t3_r3.all (fun bkt => bkt.all (checkState true c486_T 6 3 c486_sep c486_slices (fun ch => quickPrune true 6 2 c486_sep c486_slices ch || memBucket c486_tbl_2 ch))) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c486_ok_3_r4 : c486_t3_r4.all (fun bkt => bkt.all (checkState true c486_T 6 3 c486_sep c486_slices (fun ch => quickPrune true 6 2 c486_sep c486_slices ch || memBucket c486_tbl_2 ch))) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c486_ok_3_r6 : c486_t3_r6.all (fun bkt => bkt.all (checkState true c486_T 6 3 c486_sep c486_slices (fun ch => quickPrune true 6 2 c486_sep c486_slices ch || memBucket c486_tbl_2 ch))) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c486_ok_3_r8 : c486_t3_r8.all (fun bkt => bkt.all (checkState true c486_T 6 3 c486_sep c486_slices (fun ch => quickPrune true 6 2 c486_sep c486_slices ch || memBucket c486_tbl_2 ch))) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c486_ok_3_r10 : c486_t3_r10.all (fun bkt => bkt.all (checkState true c486_T 6 3 c486_sep c486_slices (fun ch => quickPrune true 6 2 c486_sep c486_slices ch || memBucket c486_tbl_2 ch))) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c486_ok_3_r11 : c486_t3_r11.all (fun bkt => bkt.all (checkState true c486_T 6 3 c486_sep c486_slices (fun ch => quickPrune true 6 2 c486_sep c486_slices ch || memBucket c486_tbl_2 ch))) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c486_ok_3_r12 : c486_t3_r12.all (fun bkt => bkt.all (checkState true c486_T 6 3 c486_sep c486_slices (fun ch => quickPrune true 6 2 c486_sep c486_slices ch || memBucket c486_tbl_2 ch))) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c486_ok_3_r14 : c486_t3_r14.all (fun bkt => bkt.all (checkState true c486_T 6 3 c486_sep c486_slices (fun ch => quickPrune true 6 2 c486_sep c486_slices ch || memBucket c486_tbl_2 ch))) = true := by decide +kernel
theorem c486_lvl_3 : ∀ ch, memBucket c486_tbl_3 ch = true → ImpossibleFrom true c486_roots c486_T 6 3 ch := by
  intro ch hch
  apply memBucket_sound c486_tbl_3 (ImpossibleFrom true c486_roots c486_T 6 3) _ hch
  intro row hrow bkt hbkt ws hws
  have hcs : checkState true c486_T 6 3 c486_sep c486_slices (fun ch => quickPrune true 6 2 c486_sep c486_slices ch || memBucket c486_tbl_2 ch) ws = true := by
    simp only [c486_tbl_3, List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact List.all_eq_true.mp (List.all_eq_true.mp c486_ok_3_r0 bkt hbkt) ws hws
    · cases hbkt
    · exact List.all_eq_true.mp (List.all_eq_true.mp c486_ok_3_r2 bkt hbkt) ws hws
    · exact List.all_eq_true.mp (List.all_eq_true.mp c486_ok_3_r3 bkt hbkt) ws hws
    · exact List.all_eq_true.mp (List.all_eq_true.mp c486_ok_3_r4 bkt hbkt) ws hws
    · cases hbkt
    · exact List.all_eq_true.mp (List.all_eq_true.mp c486_ok_3_r6 bkt hbkt) ws hws
    · cases hbkt
    · exact List.all_eq_true.mp (List.all_eq_true.mp c486_ok_3_r8 bkt hbkt) ws hws
    · cases hbkt
    · exact List.all_eq_true.mp (List.all_eq_true.mp c486_ok_3_r10 bkt hbkt) ws hws
    · exact List.all_eq_true.mp (List.all_eq_true.mp c486_ok_3_r11 bkt hbkt) ws hws
    · exact List.all_eq_true.mp (List.all_eq_true.mp c486_ok_3_r12 bkt hbkt) ws hws
    · cases hbkt
    · exact List.all_eq_true.mp (List.all_eq_true.mp c486_ok_3_r14 bkt hbkt) ws hws
    · cases hbkt
  refine checkState_sound (by omega) c486_sep_ok c486_slices_ok ?_ hcs
  intro ch' hnd' hmem'
  simp only [Bool.or_eq_true] at hmem'
  rcases hmem' with hq | hm
  · exact quickPrune_sound hnd' (by omega) c486_sep_ok c486_slices_ok hq
  · exact c486_lvl_2 ch' hm
def c486_t4_r0 : List (List (List Sig)) := [[], [], [], [[0xaaaa0000aaaa0000, 0xaaaaaaaaaaaaaaaa, 0xeeeecccceeeecccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]], [], [], [], [], [], [], [], [], [], [], [], []]
def c486_t4_r1 : List (List (List Sig)) := [[], [], [], [], [], [], [], [[0xaaaaaaaaaaaaaaaa, 0xbbbb0000bbbb0000, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]], [], [], [], [], [], [], [], []]
def c486_t4_r2 : List (List (List Sig)) := [[], [[0x5050f0f05050f0f0, 0xaaaa0000aaaa0000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00]], [[0xaa00aa00aa00aa, 0xaaaa0000aaaa0000, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]], [], [], [], [], [], [], [], [], [[0x5500ff005500ff00, 0xaaaa0000aaaa0000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0]], [], [[0xeeee0000eeee, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]], [[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xfafa0000fafa0000, 0xff00ff00ff00ff00], [0xa0a0a0a0a0a0a0a, 0xaaaa0000aaaa0000, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]], []]
def c486_t4_r3 : List (List (List Sig)) := [[], [], [[0xcccccccccccccccc, 0xeaeaeaeaeaeaeaea, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]], [], [], [], [[0x33ff000033ff0000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00], [0xfff00000fff0000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]], [], [], [], [[0xaaaaaaaaaaaaaaaa, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffffccccffffcccc], [0x3f3f00003f3f0000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00], [0xcccccccccccccccc, 0xeeaaeeaaeeaaeeaa, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000], [0x30f030f030f030f0, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000], [0xccc0ccc0ccc0ccc, 0xaaaaaaaaaaaaaaaa, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]], [], [], [], [[0x3f003f003f003f00, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000]], []]
def c486_t4_r4 : List (List (List Sig)) := [[], [], [], [], [], [], [], [], [], [], [], [], [[0xaaaa0000aaaa0000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xfafaf0f0fafaf0f0, 0xff00ff00ff00ff00]], [], [], []]
def c486_t4_r5 : List (List (List Sig)) := [[], [], [], [], [[0xaaaa8888aaaa8888, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffffccccffffcccc]], [], [], [], [], [], [], [], [], [], [], []]
def c486_t4_r6 : List (List (List Sig)) := [[[0x2222000022220000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00], [0x222200002222, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]], [[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xeeeecccceeeecccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00], [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xcccceeeecccceeee, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00], [0xaaaa8888aaaa8888, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00], [0x8888aaaa8888aaaa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]], [], [], [[0xaaaa0000aaaa0000, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffaaffaaffaaffaa], [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffaa0000ffaa0000], [0xaaaa8888aaaa8888, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]], [[0x4444444444444444, 0xaaaa0000aaaa0000, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]], [], [], [[0xaaaaaaaaaaaaaaaa, 0xeeeecccceeeecccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]], [], [], [], [], [], [], []]
def c486_t4_r7 : List (List (List Sig)) := [[], [], [], [], [], [], [[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff00ccffff00cc], [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffffccccffffcccc]], [], [], [[0x3333000033330000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]], [[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0c0cffff0c0c]], [], [], [], [], []]
def c486_t4_r8 : List (List (List Sig)) := [[], [], [], [[0xaaaa0000aaaa0000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xffaaff00ffaaff00]], [], [], [], [[0xaaaa0000aaaa, 0xaaaa0000aaaa0000, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]], [], [], [], [], [], [], [], []]
def c486_t4_r9 : List (List (List Sig)) := [[[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xf3f30000f3f30000, 0xff00ff00ff00ff00]], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
def c486_t4_r10 : List (List (List Sig)) := [[], [], [], [], [[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xeeee0000eeee0000, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]], [], [], [], [[0x3333000033330000, 0xaaaaaaaaaaaaaaaa, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffffccccffffcccc]], [[0x4444cccc4444cccc, 0xaaaa0000aaaa0000, 0xaaaaaaaaaaaaaaaa, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]], [], [], [], [], [], []]
def c486_t4_r11 : List (List (List Sig)) := [[[0xa0a0a0a0a0a0a0a, 0x5050505050505050, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000], [0xaa00aa00aa00aa, 0x5500550055005500, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000], [0xc0c0c0c0c0c0c0c, 0x3030303030303030, 0xaaaaaaaaaaaaaaaa, 0xff00ff00ff00ff00, 0xffff0000ffff0000], [0xcc00cc00cc00cc, 0x3300330033003300, 0xaaaaaaaaaaaaaaaa, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000], [0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xfaaafaaafaaafaaa, 0xff00ff00ff00ff00, 0xffff0000ffff0000], [0xaaaaaaaaaaaaaaaa, 0xf0f0f0f0f0f0f0f0, 0xfcccfcccfcccfccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000]], [[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xffc0ffc0ffc0ffc0, 0xffff0000ffff0000]], [], [[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0c0f0c0f0c0f0c0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]], [], [[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffffc0c0ffffc0c0]], [], [], [], [[0x2222222222222222, 0x4444444444444444, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000], [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff5500ffff5500], [0x2a2a2a2a2a2a2a2a, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000], [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xfc00fc00fc00fc00, 0xffff0000ffff0000], [0x22aa22aa22aa22aa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000], [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xfcf0fcf0fcf0fcf0, 0xff00ff00ff00ff00, 0xffff0000ffff0000], [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffffcc00ffffcc00], [0xaaa0aaa0aaa0aaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000], [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xfffff000fffff000], [0xf000f000f000f0, 0xf000f000f000f00, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xffff0000ffff0000]], [], [], [], [[0xfc00fc00fc00fc, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000], [0xf0c0f0c0f0c0f0c, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xff00ff00ff00ff00, 0xffff0000ffff0000], [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf000f000f000f000, 0xfff0fff0fff0fff0, 0xffff0000ffff0000]], [[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff5050ffff5050]], []]
def c486_t4_r12 : List (List (List Sig)) := [[], [], [[0x5555444455554444, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffffccccffffcccc]], [], [], [], [], [], [], [], [], [], [], [], [], []]
def c486_t4_r13 : List (List (List Sig)) := [[], [], [], [], [], [], [], [], [], [], [[0xaaaaaaaaaaaaaaaa, 0xaaff0000aaff0000, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]], [], [], [], [], [[0xaaaaaaaaaaaaaaaa, 0xafaf0000afaf0000, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]]]
def c486_t4_r14 : List (List (List Sig)) := [[], [], [], [], [], [], [], [[0xaaaa0000aaaa0000, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xfafafafafafafafa, 0xff00ff00ff00ff00]], [[0xffaa0000ffaa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00], [0xaaaa0000aaaa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00], [0xaaaa0000aaaa0000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]], [], [], [], [], [[0xfafa0000fafa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00], [0x8888888888888888, 0xaaaa0000aaaa0000, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]], [], []]
def c486_t4_r15 : List (List (List Sig)) := [[], [], [], [], [], [[0x4444444444444444, 0xaaaaaaaaaaaaaaaa, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffffccccffffcccc]], [], [], [], [], [], [], [[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xff330000ff330000]], [[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff4444ffff4444]], [], []]
def c486_tbl_4 : List (List (List (List Sig))) := [c486_t4_r0, c486_t4_r1, c486_t4_r2, c486_t4_r3, c486_t4_r4, c486_t4_r5, c486_t4_r6, c486_t4_r7, c486_t4_r8, c486_t4_r9, c486_t4_r10, c486_t4_r11, c486_t4_r12, c486_t4_r13, c486_t4_r14, c486_t4_r15]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c486_ok_4_r0 : c486_t4_r0.all (fun bkt => bkt.all (checkState true c486_T 6 4 c486_sep c486_slices (fun ch => quickPrune true 6 3 c486_sep c486_slices ch || memBucket c486_tbl_3 ch))) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c486_ok_4_r1 : c486_t4_r1.all (fun bkt => bkt.all (checkState true c486_T 6 4 c486_sep c486_slices (fun ch => quickPrune true 6 3 c486_sep c486_slices ch || memBucket c486_tbl_3 ch))) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c486_ok_4_r2 : c486_t4_r2.all (fun bkt => bkt.all (checkState true c486_T 6 4 c486_sep c486_slices (fun ch => quickPrune true 6 3 c486_sep c486_slices ch || memBucket c486_tbl_3 ch))) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c486_ok_4_r3 : c486_t4_r3.all (fun bkt => bkt.all (checkState true c486_T 6 4 c486_sep c486_slices (fun ch => quickPrune true 6 3 c486_sep c486_slices ch || memBucket c486_tbl_3 ch))) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c486_ok_4_r4 : c486_t4_r4.all (fun bkt => bkt.all (checkState true c486_T 6 4 c486_sep c486_slices (fun ch => quickPrune true 6 3 c486_sep c486_slices ch || memBucket c486_tbl_3 ch))) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c486_ok_4_r5 : c486_t4_r5.all (fun bkt => bkt.all (checkState true c486_T 6 4 c486_sep c486_slices (fun ch => quickPrune true 6 3 c486_sep c486_slices ch || memBucket c486_tbl_3 ch))) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c486_ok_4_r6 : c486_t4_r6.all (fun bkt => bkt.all (checkState true c486_T 6 4 c486_sep c486_slices (fun ch => quickPrune true 6 3 c486_sep c486_slices ch || memBucket c486_tbl_3 ch))) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c486_ok_4_r7 : c486_t4_r7.all (fun bkt => bkt.all (checkState true c486_T 6 4 c486_sep c486_slices (fun ch => quickPrune true 6 3 c486_sep c486_slices ch || memBucket c486_tbl_3 ch))) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c486_ok_4_r8 : c486_t4_r8.all (fun bkt => bkt.all (checkState true c486_T 6 4 c486_sep c486_slices (fun ch => quickPrune true 6 3 c486_sep c486_slices ch || memBucket c486_tbl_3 ch))) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c486_ok_4_r9 : c486_t4_r9.all (fun bkt => bkt.all (checkState true c486_T 6 4 c486_sep c486_slices (fun ch => quickPrune true 6 3 c486_sep c486_slices ch || memBucket c486_tbl_3 ch))) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c486_ok_4_r10 : c486_t4_r10.all (fun bkt => bkt.all (checkState true c486_T 6 4 c486_sep c486_slices (fun ch => quickPrune true 6 3 c486_sep c486_slices ch || memBucket c486_tbl_3 ch))) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c486_ok_4_r11 : c486_t4_r11.all (fun bkt => bkt.all (checkState true c486_T 6 4 c486_sep c486_slices (fun ch => quickPrune true 6 3 c486_sep c486_slices ch || memBucket c486_tbl_3 ch))) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c486_ok_4_r12 : c486_t4_r12.all (fun bkt => bkt.all (checkState true c486_T 6 4 c486_sep c486_slices (fun ch => quickPrune true 6 3 c486_sep c486_slices ch || memBucket c486_tbl_3 ch))) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c486_ok_4_r13 : c486_t4_r13.all (fun bkt => bkt.all (checkState true c486_T 6 4 c486_sep c486_slices (fun ch => quickPrune true 6 3 c486_sep c486_slices ch || memBucket c486_tbl_3 ch))) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c486_ok_4_r14 : c486_t4_r14.all (fun bkt => bkt.all (checkState true c486_T 6 4 c486_sep c486_slices (fun ch => quickPrune true 6 3 c486_sep c486_slices ch || memBucket c486_tbl_3 ch))) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c486_ok_4_r15 : c486_t4_r15.all (fun bkt => bkt.all (checkState true c486_T 6 4 c486_sep c486_slices (fun ch => quickPrune true 6 3 c486_sep c486_slices ch || memBucket c486_tbl_3 ch))) = true := by decide +kernel
theorem c486_lvl_4 : ∀ ch, memBucket c486_tbl_4 ch = true → ImpossibleFrom true c486_roots c486_T 6 4 ch := by
  intro ch hch
  apply memBucket_sound c486_tbl_4 (ImpossibleFrom true c486_roots c486_T 6 4) _ hch
  intro row hrow bkt hbkt ws hws
  have hcs : checkState true c486_T 6 4 c486_sep c486_slices (fun ch => quickPrune true 6 3 c486_sep c486_slices ch || memBucket c486_tbl_3 ch) ws = true := by
    simp only [c486_tbl_4, List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact List.all_eq_true.mp (List.all_eq_true.mp c486_ok_4_r0 bkt hbkt) ws hws
    · exact List.all_eq_true.mp (List.all_eq_true.mp c486_ok_4_r1 bkt hbkt) ws hws
    · exact List.all_eq_true.mp (List.all_eq_true.mp c486_ok_4_r2 bkt hbkt) ws hws
    · exact List.all_eq_true.mp (List.all_eq_true.mp c486_ok_4_r3 bkt hbkt) ws hws
    · exact List.all_eq_true.mp (List.all_eq_true.mp c486_ok_4_r4 bkt hbkt) ws hws
    · exact List.all_eq_true.mp (List.all_eq_true.mp c486_ok_4_r5 bkt hbkt) ws hws
    · exact List.all_eq_true.mp (List.all_eq_true.mp c486_ok_4_r6 bkt hbkt) ws hws
    · exact List.all_eq_true.mp (List.all_eq_true.mp c486_ok_4_r7 bkt hbkt) ws hws
    · exact List.all_eq_true.mp (List.all_eq_true.mp c486_ok_4_r8 bkt hbkt) ws hws
    · exact List.all_eq_true.mp (List.all_eq_true.mp c486_ok_4_r9 bkt hbkt) ws hws
    · exact List.all_eq_true.mp (List.all_eq_true.mp c486_ok_4_r10 bkt hbkt) ws hws
    · exact List.all_eq_true.mp (List.all_eq_true.mp c486_ok_4_r11 bkt hbkt) ws hws
    · exact List.all_eq_true.mp (List.all_eq_true.mp c486_ok_4_r12 bkt hbkt) ws hws
    · exact List.all_eq_true.mp (List.all_eq_true.mp c486_ok_4_r13 bkt hbkt) ws hws
    · exact List.all_eq_true.mp (List.all_eq_true.mp c486_ok_4_r14 bkt hbkt) ws hws
    · exact List.all_eq_true.mp (List.all_eq_true.mp c486_ok_4_r15 bkt hbkt) ws hws
  refine checkState_sound (by omega) c486_sep_ok c486_slices_ok ?_ hcs
  intro ch' hnd' hmem'
  simp only [Bool.or_eq_true] at hmem'
  rcases hmem' with hq | hm
  · exact quickPrune_sound hnd' (by omega) c486_sep_ok c486_slices_ok hq
  · exact c486_lvl_3 ch' hm
def c486_t5_r3 : List (List (List Sig)) := [[[0xcc00cc00cc00cc, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000], [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xfff0fff0fff0fff0, 0xffff0000ffff0000]], [[0x4444444444444444, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]], [], [], [], [], [], [[0xaaaaaaaaaaaaaaaa, 0xcc00cc00cc00cc00, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]], [[0xc0c0c0c0c0c0c0c, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]], [], [[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf000f000f000f000, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]], [], [], [], [], [[0xaaaaaaaaaaaaaaaa, 0xc0c0c0c0c0c0c0c0, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]]]
def c486_t5_r7 : List (List (List Sig)) := [[], [], [], [], [[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]], [], [[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffffccccffffcccc]], [], [], [[0x3333000033330000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]], [], [], [], [[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xfafafafafafafafa, 0xff00ff00ff00ff00, 0xffff0000ffff0000]], [], []]
def c486_t5_r11 : List (List (List Sig)) := [[], [], [], [[0x3030303030303030, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]], [[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffccffccffccffcc, 0xffff0000ffff0000]], [], [], [], [], [[0x5500550055005500, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000], [0x3300330033003300, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000], [0xf000f000f000f00, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]], [], [[0xf000f000f000f0, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]], [], [[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xfcfcfcfcfcfcfcfc, 0xff00ff00ff00ff00, 0xffff0000ffff0000]], [], [[0x5050505050505050, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]]]
def c486_t5_r14 : List (List (List Sig)) := [[], [], [], [], [], [], [], [], [[0xaaaa0000aaaa0000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00], [0xaaaa0000aaaa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]], [], [], [], [], [], [], []]
def c486_t5_r15 : List (List (List Sig)) := [[[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffaaffaaffaaffaa, 0xffff0000ffff0000]], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
def c486_tbl_5 : List (List (List (List Sig))) := [[], [], [], c486_t5_r3, [], [], [], c486_t5_r7, [], [], [], c486_t5_r11, [], [], c486_t5_r14, c486_t5_r15]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c486_ok_5_r3 : c486_t5_r3.all (fun bkt => bkt.all (checkState true c486_T 6 5 c486_sep c486_slices (fun ch => quickPrune true 6 4 c486_sep c486_slices ch || memBucket c486_tbl_4 ch))) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c486_ok_5_r7 : c486_t5_r7.all (fun bkt => bkt.all (checkState true c486_T 6 5 c486_sep c486_slices (fun ch => quickPrune true 6 4 c486_sep c486_slices ch || memBucket c486_tbl_4 ch))) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c486_ok_5_r11 : c486_t5_r11.all (fun bkt => bkt.all (checkState true c486_T 6 5 c486_sep c486_slices (fun ch => quickPrune true 6 4 c486_sep c486_slices ch || memBucket c486_tbl_4 ch))) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c486_ok_5_r14 : c486_t5_r14.all (fun bkt => bkt.all (checkState true c486_T 6 5 c486_sep c486_slices (fun ch => quickPrune true 6 4 c486_sep c486_slices ch || memBucket c486_tbl_4 ch))) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c486_ok_5_r15 : c486_t5_r15.all (fun bkt => bkt.all (checkState true c486_T 6 5 c486_sep c486_slices (fun ch => quickPrune true 6 4 c486_sep c486_slices ch || memBucket c486_tbl_4 ch))) = true := by decide +kernel
theorem c486_lvl_5 : ∀ ch, memBucket c486_tbl_5 ch = true → ImpossibleFrom true c486_roots c486_T 6 5 ch := by
  intro ch hch
  apply memBucket_sound c486_tbl_5 (ImpossibleFrom true c486_roots c486_T 6 5) _ hch
  intro row hrow bkt hbkt ws hws
  have hcs : checkState true c486_T 6 5 c486_sep c486_slices (fun ch => quickPrune true 6 4 c486_sep c486_slices ch || memBucket c486_tbl_4 ch) ws = true := by
    simp only [c486_tbl_5, List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · cases hbkt
    · cases hbkt
    · cases hbkt
    · exact List.all_eq_true.mp (List.all_eq_true.mp c486_ok_5_r3 bkt hbkt) ws hws
    · cases hbkt
    · cases hbkt
    · cases hbkt
    · exact List.all_eq_true.mp (List.all_eq_true.mp c486_ok_5_r7 bkt hbkt) ws hws
    · cases hbkt
    · cases hbkt
    · cases hbkt
    · exact List.all_eq_true.mp (List.all_eq_true.mp c486_ok_5_r11 bkt hbkt) ws hws
    · cases hbkt
    · cases hbkt
    · exact List.all_eq_true.mp (List.all_eq_true.mp c486_ok_5_r14 bkt hbkt) ws hws
    · exact List.all_eq_true.mp (List.all_eq_true.mp c486_ok_5_r15 bkt hbkt) ws hws
  refine checkState_sound (by omega) c486_sep_ok c486_slices_ok ?_ hcs
  intro ch' hnd' hmem'
  simp only [Bool.or_eq_true] at hmem'
  rcases hmem' with hq | hm
  · exact quickPrune_sound hnd' (by omega) c486_sep_ok c486_slices_ok hq
  · exact c486_lvl_4 ch' hm
def c486_t6_r11 : List (List (List Sig)) := [[], [], [], [], [], [], [], [], [], [[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]], [], [], [], [], [], []]
def c486_tbl_6 : List (List (List (List Sig))) := [[], [], [], [], [], [], [], [], [], [], [], c486_t6_r11, [], [], [], []]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c486_ok_6_r11 : c486_t6_r11.all (fun bkt => bkt.all (checkState true c486_T 6 6 c486_sep c486_slices (fun ch => quickPrune true 6 5 c486_sep c486_slices ch || memBucket c486_tbl_5 ch))) = true := by decide +kernel
theorem c486_lvl_6 : ∀ ch, memBucket c486_tbl_6 ch = true → ImpossibleFrom true c486_roots c486_T 6 6 ch := by
  intro ch hch
  apply memBucket_sound c486_tbl_6 (ImpossibleFrom true c486_roots c486_T 6 6) _ hch
  intro row hrow bkt hbkt ws hws
  have hcs : checkState true c486_T 6 6 c486_sep c486_slices (fun ch => quickPrune true 6 5 c486_sep c486_slices ch || memBucket c486_tbl_5 ch) ws = true := by
    simp only [c486_tbl_6, List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · cases hbkt
    · cases hbkt
    · cases hbkt
    · cases hbkt
    · cases hbkt
    · cases hbkt
    · cases hbkt
    · cases hbkt
    · cases hbkt
    · cases hbkt
    · cases hbkt
    · exact List.all_eq_true.mp (List.all_eq_true.mp c486_ok_6_r11 bkt hbkt) ws hws
    · cases hbkt
    · cases hbkt
    · cases hbkt
    · cases hbkt
  refine checkState_sound (by omega) c486_sep_ok c486_slices_ok ?_ hcs
  intro ch' hnd' hmem'
  simp only [Bool.or_eq_true] at hmem'
  rcases hmem' with hq | hm
  · exact quickPrune_sound hnd' (by omega) c486_sep_ok c486_slices_ok hq
  · exact c486_lvl_5 ch' hm
theorem c486_lower : Lower true c486_roots c486_T 7 := by
  refine lower_of_impossible (cap := 6) (by unfold proper; decide +kernel) c486_es (by decide +kernel) (by decide +kernel) ?_
  exact c486_lvl_6 c486_roots (by decide +kernel)

def c0_roots : List Sig := maskVars 63
def c0_T : Sig := 0xfeeafcc8feeaccc0
def c0_es : List (Sig × Row × Row) := [(xVars.getD 0 zero, ⟨16, by decide⟩, ⟨17, by decide⟩), (xVars.getD 1 zero, ⟨4, by decide⟩, ⟨6, by decide⟩), (xVars.getD 2 zero, ⟨2, by decide⟩, ⟨6, by decide⟩), (xVars.getD 3 zero, ⟨2, by decide⟩, ⟨10, by decide⟩), (xVars.getD 4 zero, ⟨1, by decide⟩, ⟨17, by decide⟩), (xVars.getD 5 zero, ⟨3, by decide⟩, ⟨35, by decide⟩)]
def c0_sep : List (Row × Row) := []
theorem c0_sep_ok : c0_sep.all (fun p => bit p.1 c0_T && !(bit p.2 c0_T)) = true := by decide +kernel
def c0_slices : List (Sig × Nat) := [(0xffffffff00000000, 7)]
theorem c0_slices_ok : ∀ sl ∈ c0_slices, Slice true c0_roots c0_T sl.1 sl.2 := by
  intro sl hsl
  simp only [c0_slices, List.mem_cons, List.not_mem_nil, or_false] at hsl
  rcases hsl with rfl
  · exact slice_of_lower (u := true) (z := 0) (o := 32) (by decide +kernel) (Or.inl (by decide +kernel)) (by decide +kernel) (by unfold proper; decide +kernel) c486_lower
def c0_tbl_1 : List (List (List (List Sig))) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
theorem c0_lvl_1 : ∀ ch, memBucket c0_tbl_1 ch = true → ImpossibleFrom true c0_roots c0_T 7 1 ch := by
  intro ch hch
  apply memBucket_sound c0_tbl_1 (ImpossibleFrom true c0_roots c0_T 7 1) _ hch
  intro row hrow bkt hbkt ws hws
  have hcs : checkState true c0_T 7 1 c0_sep c0_slices (fun ch => !ch.contains c0_T) ws = true := by
    simp only [c0_tbl_1, List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases hbkt
  refine checkState_sound (by omega) c0_sep_ok c0_slices_ok ?_ hcs
  intro ch' hnd' hmem'
  apply impossible_zero
  intro hm; have hc : ch'.contains c0_T = true := List.contains_iff_mem.mpr hm; rw [hc] at hmem'; exact Bool.noConfusion hmem'
def c0_tbl_2 : List (List (List (List Sig))) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
theorem c0_lvl_2 : ∀ ch, memBucket c0_tbl_2 ch = true → ImpossibleFrom true c0_roots c0_T 7 2 ch := by
  intro ch hch
  apply memBucket_sound c0_tbl_2 (ImpossibleFrom true c0_roots c0_T 7 2) _ hch
  intro row hrow bkt hbkt ws hws
  have hcs : checkState true c0_T 7 2 c0_sep c0_slices (fun ch => quickPrune true 7 1 c0_sep c0_slices ch || memBucket c0_tbl_1 ch) ws = true := by
    simp only [c0_tbl_2, List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases hbkt
  refine checkState_sound (by omega) c0_sep_ok c0_slices_ok ?_ hcs
  intro ch' hnd' hmem'
  simp only [Bool.or_eq_true] at hmem'
  rcases hmem' with hq | hm
  · exact quickPrune_sound hnd' (by omega) c0_sep_ok c0_slices_ok hq
  · exact c0_lvl_1 ch' hm
def c0_tbl_3 : List (List (List (List Sig))) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
theorem c0_lvl_3 : ∀ ch, memBucket c0_tbl_3 ch = true → ImpossibleFrom true c0_roots c0_T 7 3 ch := by
  intro ch hch
  apply memBucket_sound c0_tbl_3 (ImpossibleFrom true c0_roots c0_T 7 3) _ hch
  intro row hrow bkt hbkt ws hws
  have hcs : checkState true c0_T 7 3 c0_sep c0_slices (fun ch => quickPrune true 7 2 c0_sep c0_slices ch || memBucket c0_tbl_2 ch) ws = true := by
    simp only [c0_tbl_3, List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases hbkt
  refine checkState_sound (by omega) c0_sep_ok c0_slices_ok ?_ hcs
  intro ch' hnd' hmem'
  simp only [Bool.or_eq_true] at hmem'
  rcases hmem' with hq | hm
  · exact quickPrune_sound hnd' (by omega) c0_sep_ok c0_slices_ok hq
  · exact c0_lvl_2 ch' hm
def c0_tbl_4 : List (List (List (List Sig))) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
theorem c0_lvl_4 : ∀ ch, memBucket c0_tbl_4 ch = true → ImpossibleFrom true c0_roots c0_T 7 4 ch := by
  intro ch hch
  apply memBucket_sound c0_tbl_4 (ImpossibleFrom true c0_roots c0_T 7 4) _ hch
  intro row hrow bkt hbkt ws hws
  have hcs : checkState true c0_T 7 4 c0_sep c0_slices (fun ch => quickPrune true 7 3 c0_sep c0_slices ch || memBucket c0_tbl_3 ch) ws = true := by
    simp only [c0_tbl_4, List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases hbkt
  refine checkState_sound (by omega) c0_sep_ok c0_slices_ok ?_ hcs
  intro ch' hnd' hmem'
  simp only [Bool.or_eq_true] at hmem'
  rcases hmem' with hq | hm
  · exact quickPrune_sound hnd' (by omega) c0_sep_ok c0_slices_ok hq
  · exact c0_lvl_3 ch' hm
def c0_tbl_5 : List (List (List (List Sig))) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
theorem c0_lvl_5 : ∀ ch, memBucket c0_tbl_5 ch = true → ImpossibleFrom true c0_roots c0_T 7 5 ch := by
  intro ch hch
  apply memBucket_sound c0_tbl_5 (ImpossibleFrom true c0_roots c0_T 7 5) _ hch
  intro row hrow bkt hbkt ws hws
  have hcs : checkState true c0_T 7 5 c0_sep c0_slices (fun ch => quickPrune true 7 4 c0_sep c0_slices ch || memBucket c0_tbl_4 ch) ws = true := by
    simp only [c0_tbl_5, List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases hbkt
  refine checkState_sound (by omega) c0_sep_ok c0_slices_ok ?_ hcs
  intro ch' hnd' hmem'
  simp only [Bool.or_eq_true] at hmem'
  rcases hmem' with hq | hm
  · exact quickPrune_sound hnd' (by omega) c0_sep_ok c0_slices_ok hq
  · exact c0_lvl_4 ch' hm
def c0_tbl_6 : List (List (List (List Sig))) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
theorem c0_lvl_6 : ∀ ch, memBucket c0_tbl_6 ch = true → ImpossibleFrom true c0_roots c0_T 7 6 ch := by
  intro ch hch
  apply memBucket_sound c0_tbl_6 (ImpossibleFrom true c0_roots c0_T 7 6) _ hch
  intro row hrow bkt hbkt ws hws
  have hcs : checkState true c0_T 7 6 c0_sep c0_slices (fun ch => quickPrune true 7 5 c0_sep c0_slices ch || memBucket c0_tbl_5 ch) ws = true := by
    simp only [c0_tbl_6, List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases hbkt
  refine checkState_sound (by omega) c0_sep_ok c0_slices_ok ?_ hcs
  intro ch' hnd' hmem'
  simp only [Bool.or_eq_true] at hmem'
  rcases hmem' with hq | hm
  · exact quickPrune_sound hnd' (by omega) c0_sep_ok c0_slices_ok hq
  · exact c0_lvl_5 ch' hm
def c0_tbl_7 : List (List (List (List Sig))) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
theorem c0_lvl_7 : ∀ ch, memBucket c0_tbl_7 ch = true → ImpossibleFrom true c0_roots c0_T 7 7 ch := by
  intro ch hch
  apply memBucket_sound c0_tbl_7 (ImpossibleFrom true c0_roots c0_T 7 7) _ hch
  intro row hrow bkt hbkt ws hws
  have hcs : checkState true c0_T 7 7 c0_sep c0_slices (fun ch => quickPrune true 7 6 c0_sep c0_slices ch || memBucket c0_tbl_6 ch) ws = true := by
    simp only [c0_tbl_7, List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases hbkt
  refine checkState_sound (by omega) c0_sep_ok c0_slices_ok ?_ hcs
  intro ch' hnd' hmem'
  simp only [Bool.or_eq_true] at hmem'
  rcases hmem' with hq | hm
  · exact quickPrune_sound hnd' (by omega) c0_sep_ok c0_slices_ok hq
  · exact c0_lvl_6 ch' hm
theorem c0_lower : Lower true c0_roots c0_T 8 := by
  refine lower_of_impossible (cap := 7) (by unfold proper; decide +kernel) c0_es (by decide +kernel) (by decide +kernel) ?_
  exact quickPrune_sound (sortedStrict_nodup (by decide +kernel : isSortedStrict c0_roots = true)) le_rfl c0_sep_ok c0_slices_ok (by decide +kernel)

theorem rootLower : Lower true xVars c0_T 8 := c0_lower
end Core

open Core

def targetFn : (Fin 6 → Bool) → Bool := fun x : Fin 6 → Bool => Nat.testBit (4276813000 * 2 ^ 32 + 4276800704) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem matchTarget : ∀ r : Row, bit r c0_T = targetFn (sampleRow r) := by decide +kernel
def witnessGates : List Gate := [⟨GateOp.or, [1, 4]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [9, 12]⟩, ⟨GateOp.or, [11, 13]⟩]
def witnessCirc : Circuit := ⟨witnessGates, 14⟩
theorem witnessMono : Monotone2 witnessCirc := by
  intro g hg
  simp only [witnessCirc, witnessGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem witnessEval : ∀ x : Fin 6 → Bool, witnessCirc.eval (List.ofFn x) = targetFn x := by decide +kernel

end PEqualNP.Outside.L_meta_16767

theorem PEqualNP.Outside.L_meta_16767 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813000 * 2 ^ 32 + 4276800704) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813000 * 2 ^ 32 + 4276800704) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  intro s hcs
  obtain ⟨C, hfit, hsz, hev⟩ := hcs
  by_cases hnot : ∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · have hbin := PEqualNP.Outside.L_meta_16767.Core.binaryLower_of_lower PEqualNP.Outside.L_meta_16767.Core.c0_T PEqualNP.Outside.L_meta_16767.targetFn 8 (by unfold PEqualNP.Outside.L_meta_16767.Core.proper; decide +kernel) (by decide +kernel) PEqualNP.Outside.L_meta_16767.matchTarget PEqualNP.Outside.L_meta_16767.Core.rootLower C hfit hev
    obtain ⟨g, hg, hop⟩ := hnot
    have hextra : C.gates.countP (fun t => !PEqualNP.Outside.L_meta_16767.Core.isNot t) < C.gates.length := by
      by_contra! hge
      have hall := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length hge) g hg
      simp [PEqualNP.Outside.L_meta_16767.Core.isNot, hop] at hall
    have hwl : PEqualNP.Outside.L_meta_16767.witnessCirc.size = 9 := rfl
    have hcsz : C.size = C.gates.length := rfl
    exact ⟨PEqualNP.Outside.L_meta_16767.witnessCirc, PEqualNP.Outside.L_meta_16767.witnessMono, by omega, PEqualNP.Outside.L_meta_16767.witnessEval⟩
  · refine ⟨C, ?_, hsz, hev⟩
    intro g hg
    obtain ⟨ho, hl⟩ := hfit g hg
    refine ⟨?_, hl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho ⊢
    rcases ho with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd ⟨g, hg, h⟩ hnot
