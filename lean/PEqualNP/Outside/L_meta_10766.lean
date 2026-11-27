import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.IntervalCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10766

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

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

lemma nat_land (a b : ℕ) : Nat.land a b = a &&& b := rfl
lemma nat_lor (a b : ℕ) : Nat.lor a b = a ||| b := rfl
lemma nat_xor (a b : ℕ) : Nat.xor a b = a ^^^ b := rfl
lemma nat_shr (a b : ℕ) : Nat.shiftRight a b = a >>> b := rfl
lemma nat_add (a b : ℕ) : Nat.add a b = a + b := rfl
lemma nat_sub (a b : ℕ) : Nat.sub a b = a - b := rfl

lemma nat_beq_false {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.beq_eq.mp hb) h

lemma bv_toNat_not {n : ℕ} (w : BitVec n) : (~~~w).toNat = Nat.xor w.toNat (2 ^ n - 1) := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [nat_xor, BitVec.testBit_toNat, Nat.testBit_xor, Nat.testBit_two_pow_sub_one, BitVec.testBit_toNat]
  by_cases hk : k < n
  · simp [hk]
  · simp [hk, BitVec.getLsbD_of_ge w k (Nat.le_of_not_lt hk)]

def elemN (w : ℕ) : List ℕ → Bool
  | [] => false
  | x :: xs => Nat.beq x w || elemN w xs

lemma elemN_map_false {n : ℕ} {w : BitVec n} {r : List (BitVec n)} (h : w ∉ r) :
    elemN w.toNat (r.map BitVec.toNat) = false := by
  induction r with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mem_cons, not_or] at h
    simp only [List.map_cons, elemN, Bool.or_eq_false_iff]
    exact ⟨nat_beq_false (fun he => h.1 (BitVec.eq_of_toNat_eq he.symm)), ih h.2⟩

abbrev W4 := BitVec 110
def M4 : ℕ := 0x7fffffffffffff
def A4 : ℕ := 0x3fffffffffffffffffffffffffff
def G4 : ℕ := 0x3fffffffffffff80000000000000
def goal4 : W4 := BitVec.ofNat 110 G4
def ops4 (x y : W4) : List W4 := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
abbrev basicOps4 (a b : W4) : Finset W4 := (ops4 a b).toFinset
def sep4 (x : W4) : BitVec 55 := ((x >>> 55) ^^^ x).setWidth 55
def cuts4 (ws : List W4) : BitVec 55 := ws.foldr (fun w v => sep4 w ||| v) 0
def k4inputs : List W4 := [BitVec.ofNat 110 0x2add5bab756ead800000003ff800, BitVec.ofNat 110 0x336e6dcdb9b736800001ffc00000, BitVec.ofNat 110 0x3c778ef1de3bc7000ffe00000000, BitVec.ofNat 110 0x3f87f0fe1fc3f87ff00000000000]

lemma hM4_pow : M4 = 2 ^ 55 - 1 := by decide
lemma hA4_pow : A4 = 2 ^ 110 - 1 := by decide

def sep4N (w : ℕ) : ℕ := Nat.land (Nat.xor (Nat.shiftRight w 55) w) 0x7fffffffffffff

lemma sep4_toNat (w : W4) : (sep4 w).toNat = sep4N w.toNat := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [sep4N, show (0x7fffffffffffff : ℕ) = 2 ^ 55 - 1 from hM4_pow, nat_land, nat_xor, nat_shr]
  rw [BitVec.testBit_toNat, Nat.testBit_land, Nat.testBit_xor, Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one, BitVec.testBit_toNat, BitVec.testBit_toNat]
  by_cases hk : k < 55
  · simp [sep4, hk, Nat.add_comm]
  · rw [BitVec.getLsbD_of_ge (sep4 w) k (Nat.le_of_not_lt hk)]; simp [hk]

def cuts4N : List ℕ → ℕ
  | [] => 0
  | w :: r => Nat.lor (sep4N w) (cuts4N r)

lemma cuts4N_map (ws : List W4) : cuts4N (ws.map BitVec.toNat) = (cuts4 ws).toNat := by
  induction ws with
  | nil => simp [cuts4, cuts4N]
  | cons w r ih =>
    simp only [List.map_cons, cuts4N, cuts4, List.foldr_cons, BitVec.toNat_or, sep4_toNat, ih]
    rfl

def differs4 (i : Fin 55) (w : W4) : Prop :=
  w.getLsbD (55 + i.val) ≠ w.getLsbD i.val

theorem ops4_differs (i : Fin 55) (a b z : W4) (hz : z ∈ basicOps4 a b)
    (hd : differs4 i z) : differs4 i a ∨ differs4 i b := by
  simp only [basicOps4, ops4, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha, hb⟩ := fail
  apply hd
  unfold differs4 at ha hb
  simp only [not_not] at ha hb
  have hi : 55 + i.val < 110 := by omega
  have hi' : i.val < 110 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts4_spec (ws : List W4) (i : Fin 55) :
    (cuts4 ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs4 i w := by
  induction ws with
  | nil => simp [cuts4]
  | cons a rest ih =>
    change (sep4 a ||| cuts4 rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep4, i.isLt, differs4, Nat.add_comm, bx]

theorem cuts4_full {g : W4} (hg : g = goal4 ∨ g = ~~~goal4) {k : ℕ} {ws : List W4}
    (h : live basicOps4 g k ws.toFinset) : cuts4N (ws.map BitVec.toNat) = M4 := by
  rw [cuts4N_map]
  have hd : ∀ i, differs4 i g := by rcases hg with rfl | rfl <;> unfold differs4 <;> decide +kernel
  have hall : cuts4 ws = -1 := by
    apply BitVec.eq_of_getElem_eq
    intro j hj
    have hw := live_separates (differs4 ⟨j, hj⟩) (hd ⟨j, hj⟩) (ops4_differs ⟨j, hj⟩) h
    have hbit := (cuts4_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
    change (cuts4 ws)[j] = (BitVec.allOnes 55)[j]
    rw [BitVec.getElem_allOnes]
    simpa only [BitVec.getLsbD_eq_getElem hj] using hbit
  rw [hall]
  decide

theorem ops4_swap (a b : W4) : basicOps4 a b = basicOps4 b a := by
  ext z
  simp only [basicOps4, ops4, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices4 (a b : W4) (r : List W4) : List (List W4) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept4 {ws r : List W4} {a b : W4} {needed : Finset W4}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices4 a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v; simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices4], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices4], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices4], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices4], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list4 {g : W4} {ws : List W4} (hn : ws.Nodup) (hs : ws.toFinset = {g}) : ws = [g] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def tryW4 (extra : ℕ) (next : ℕ → List ℕ → Bool) (a b : ℕ) (sa sb base : ℕ) (r : List ℕ) (w : ℕ) : Bool :=
  if Nat.beq w a || Nat.beq w b || elemN w r then false
  else
    let v := Nat.lor (sep4N w) base
    if Nat.beq v 0x7fffffffffffff && next extra (w :: r) then true
    else if Nat.beq extra 0 then false
    else if Nat.beq (Nat.lor v sa) 0x7fffffffffffff && next (Nat.sub extra 1) (w :: a :: r) then true
    else if Nat.beq (Nat.lor v sb) 0x7fffffffffffff && next (Nat.sub extra 1) (w :: b :: r) then true
    else if Nat.ble 2 extra && Nat.beq (Nat.lor (Nat.lor v sa) sb) 0x7fffffffffffff && next (Nat.sub extra 2) (w :: a :: b :: r) then true
    else false

def disp4 (extra : ℕ) (next : ℕ → List ℕ → Bool) (a b : ℕ) (r : List ℕ) : Bool :=
  let base := cuts4N r
  let sa := sep4N a
  let sb := sep4N b
  tryW4 extra next a b sa sb base r (Nat.land a b) ||
  tryW4 extra next a b sa sb base r (Nat.lor a b) ||
  tryW4 extra next a b sa sb base r (Nat.land a (Nat.xor b 0x3fffffffffffffffffffffffffff)) ||
  tryW4 extra next a b sa sb base r (Nat.land b (Nat.xor a 0x3fffffffffffffffffffffffffff))

def pickB4 (extra : ℕ) (next : ℕ → List ℕ → Bool) (a : ℕ) (pre : List ℕ) : List ℕ → Bool
  | [] => false
  | b :: rest =>
    disp4 extra next a b (pre ++ rest) || pickB4 extra next a (b :: pre) rest

def pickA4 (extra : ℕ) (next : ℕ → List ℕ → Bool) (pre : List ℕ) : List ℕ → Bool
  | [] => false
  | a :: rest =>
    pickB4 extra next a pre rest || pickA4 extra next (a :: pre) rest

def opt4 : ℕ → ℕ → List ℕ → Bool
  | 0, _, ws => match ws with | [w] => Nat.beq w 0x3fffffffffffff80000000000000 || Nat.beq w 0x7fffffffffffff | _ => false
  | k + 1, extra, ws =>
    (match ws with | [w] => Nat.beq w 0x3fffffffffffff80000000000000 || Nat.beq w 0x7fffffffffffff | _ => false) ||
    pickA4 extra (opt4 k) [] ws

lemma pickB4_exists (extra : ℕ) (next : ℕ → List ℕ → Bool) (a b : W4) (pre ys : List W4)
    (hb : b ∈ ys) :
    ∃ r : List W4, (pre ++ ys).Perm (b :: r) ∧
      (disp4 extra next a.toNat b.toNat (r.map BitVec.toNat) = true →
        pickB4 extra next a.toNat (pre.map BitVec.toNat) (ys.map BitVec.toNat) = true) := by
  induction ys generalizing pre with
  | nil => simp at hb
  | cons y rest ih =>
    rcases List.mem_cons.mp hb with rfl | hbr
    · refine ⟨pre ++ rest, List.perm_middle, fun hd => ?_⟩
      simp only [List.map_cons, pickB4, List.map_append] at hd ⊢
      rw [hd]; rfl
    · obtain ⟨r, hp, himp⟩ := ih (y :: pre) hbr
      refine ⟨r, List.perm_middle.trans hp, fun hd => ?_⟩
      have h := himp hd
      simp only [List.map_cons] at h
      simp only [List.map_cons, pickB4, h, Bool.or_true]

lemma pickA4_exists (extra : ℕ) (next : ℕ → List ℕ → Bool) (a b : W4) (pre ys : List W4)
    (ha : a ∈ ys) (hb : b ∈ ys) (hne : a ≠ b) :
    ∃ r : List W4, (pre ++ ys).Perm (a :: b :: r) ∧
      ((disp4 extra next a.toNat b.toNat (r.map BitVec.toNat) = true →
          pickA4 extra next (pre.map BitVec.toNat) (ys.map BitVec.toNat) = true) ∨
       (disp4 extra next b.toNat a.toNat (r.map BitVec.toNat) = true →
          pickA4 extra next (pre.map BitVec.toNat) (ys.map BitVec.toNat) = true)) := by
  induction ys generalizing pre with
  | nil => simp at ha
  | cons y rest ih =>
    rcases List.mem_cons.mp ha with rfl | har
    · have hbr : b ∈ rest := (List.mem_cons.mp hb).resolve_left (Ne.symm hne)
      obtain ⟨r, hp, himp⟩ := pickB4_exists extra next a b pre rest hbr
      refine ⟨r, List.perm_middle.trans (hp.cons a), .inl fun hd => ?_⟩
      simp only [List.map_cons, pickA4, himp hd, Bool.true_or]
    · rcases List.mem_cons.mp hb with rfl | hbr
      · obtain ⟨r, hp, himp⟩ := pickB4_exists extra next b a pre rest har
        refine ⟨r, List.perm_middle.trans ((hp.cons b).trans (List.Perm.swap a b r)), .inr fun hd => ?_⟩
        simp only [List.map_cons, pickA4, himp hd, Bool.true_or]
      · obtain ⟨r, hp, himp⟩ := ih (y :: pre) har hbr
        refine ⟨r, List.perm_middle.trans hp, himp.imp (fun f hd => ?_) (fun f hd => ?_)⟩
        · have h := f hd; simp only [List.map_cons] at h; simp only [List.map_cons, pickA4, h, Bool.or_true]
        · have h := f hd; simp only [List.map_cons] at h; simp only [List.map_cons, pickA4, h, Bool.or_true]

theorem disp4_complete {k extra : ℕ} {a b z : W4} {r kept : List W4}
    (next : ℕ → List ℕ → Bool)
    (hz : z ∈ basicOps4 a b) (hza : z ≠ a) (hzb : z ≠ b) (hzr : z ∉ r)
    (hk : kept ∈ keepChoices4 a b r) (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts4N ((z :: kept).map BitVec.toNat) = M4)
    (ht : next (k - kept.length) ((z :: kept).map BitVec.toNat) = true) :
    disp4 extra next a.toNat b.toNat (r.map BitVec.toNat) = true := by
  have htry : tryW4 extra next a.toNat b.toNat (sep4N a.toNat) (sep4N b.toNat)
      (cuts4N (r.map BitVec.toNat)) (r.map BitVec.toNat) z.toNat = true := by
    unfold tryW4
    have hna : Nat.beq z.toNat a.toNat = false := nat_beq_false (fun heq => hza (BitVec.eq_of_toNat_eq heq))
    have hnb : Nat.beq z.toNat b.toNat = false := nat_beq_false (fun heq => hzb (BitVec.eq_of_toNat_eq heq))
    have hnr : elemN z.toNat (r.map BitVec.toNat) = false := elemN_map_false hzr
    rw [hna, hnb, hnr]; simp only [Bool.false_or, Bool.false_eq_true, ↓reduceIte]
    have hM4v : (0x7fffffffffffff : ℕ) = M4 := rfl
    simp only [hM4v]
    simp only [keepChoices4, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with hkeq | hkeq | hkeq | hkeq
    · rw [hkeq] at hc ht hn
      simp only [List.map_cons, cuts4N] at hc
      have h1 : Nat.beq (Nat.lor (sep4N z.toNat) (cuts4N (r.map BitVec.toNat))) M4 = true :=
        Nat.beq_eq.mpr hc
      have h2 : next extra (z.toNat :: r.map BitVec.toNat) = true := by
        simpa only [List.map_cons] using (show next extra ((z :: r).map BitVec.toNat) = true by convert ht using 2; omega)
      rw [h1, h2]; rfl
    · rw [hkeq] at hc ht hn
      simp only [List.map_cons, cuts4N] at hc
      simp only [List.length_cons] at hn ht
      have hnz : Nat.beq extra 0 = false := nat_beq_false (by omega)
      have h1 : Nat.beq (Nat.lor (Nat.lor (sep4N z.toNat) (cuts4N (r.map BitVec.toNat))) (sep4N a.toNat)) M4 = true := by
        have hcomm : Nat.lor (Nat.lor (sep4N z.toNat) (cuts4N (r.map BitVec.toNat))) (sep4N a.toNat) =
            Nat.lor (sep4N z.toNat) (Nat.lor (sep4N a.toNat) (cuts4N (r.map BitVec.toNat))) := by
          apply Nat.eq_of_testBit_eq; intro t; simp only [nat_lor, Nat.testBit_lor]; grind
        rw [hcomm]; exact Nat.beq_eq.mpr hc
      have h2 : next (Nat.sub extra 1) (z.toNat :: a.toNat :: r.map BitVec.toNat) = true := by
        rw [nat_sub]; simpa only [List.map_cons] using (show next (extra - 1) ((z :: a :: r).map BitVec.toNat) = true by convert ht using 2; omega)
      rw [hnz, h1, h2]
      split_ifs <;> simp_all
    · rw [hkeq] at hc ht hn
      simp only [List.map_cons, cuts4N] at hc
      simp only [List.length_cons] at hn ht
      have hnz : Nat.beq extra 0 = false := nat_beq_false (by omega)
      have h1 : Nat.beq (Nat.lor (Nat.lor (sep4N z.toNat) (cuts4N (r.map BitVec.toNat))) (sep4N b.toNat)) M4 = true := by
        have hcomm : Nat.lor (Nat.lor (sep4N z.toNat) (cuts4N (r.map BitVec.toNat))) (sep4N b.toNat) =
            Nat.lor (sep4N z.toNat) (Nat.lor (sep4N b.toNat) (cuts4N (r.map BitVec.toNat))) := by
          apply Nat.eq_of_testBit_eq; intro t; simp only [nat_lor, Nat.testBit_lor]; grind
        rw [hcomm]; exact Nat.beq_eq.mpr hc
      have h2 : next (Nat.sub extra 1) (z.toNat :: b.toNat :: r.map BitVec.toNat) = true := by
        rw [nat_sub]; simpa only [List.map_cons] using (show next (extra - 1) ((z :: b :: r).map BitVec.toNat) = true by convert ht using 2; omega)
      rw [hnz, h1, h2]
      split_ifs <;> simp_all
    · rw [hkeq] at hc ht hn
      simp only [List.map_cons, cuts4N] at hc
      simp only [List.length_cons] at hn ht
      have hnz : Nat.beq extra 0 = false := nat_beq_false (by omega)
      have hge2 : Nat.ble 2 extra = true := Nat.ble_eq.mpr (by omega)
      have h1 : Nat.beq (Nat.lor (Nat.lor (Nat.lor (sep4N z.toNat) (cuts4N (r.map BitVec.toNat))) (sep4N a.toNat)) (sep4N b.toNat)) M4 = true := by
        have hcomm : Nat.lor (Nat.lor (Nat.lor (sep4N z.toNat) (cuts4N (r.map BitVec.toNat))) (sep4N a.toNat)) (sep4N b.toNat) =
            Nat.lor (sep4N z.toNat) (Nat.lor (sep4N a.toNat) (Nat.lor (sep4N b.toNat) (cuts4N (r.map BitVec.toNat)))) := by
          apply Nat.eq_of_testBit_eq; intro t; simp only [nat_lor, Nat.testBit_lor]; grind
        rw [hcomm]; exact Nat.beq_eq.mpr hc
      have h2 : next (Nat.sub extra 2) (z.toNat :: a.toNat :: b.toNat :: r.map BitVec.toNat) = true := by
        rw [nat_sub]; simpa only [List.map_cons] using (show next (extra - 2) ((z :: a :: b :: r).map BitVec.toNat) = true by convert ht using 2; omega)
      rw [hnz, hge2, h1, h2]
      split_ifs <;> simp_all
  simp only [basicOps4, ops4, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  unfold disp4
  have hnot_b : (~~~b).toNat = Nat.xor b.toNat 0x3fffffffffffffffffffffffffff := by
    rw [show (0x3fffffffffffffffffffffffffff : ℕ) = 2 ^ 110 - 1 from hA4_pow]; exact bv_toNat_not b
  have hnot_a : (~~~a).toNat = Nat.xor a.toNat 0x3fffffffffffffffffffffffffff := by
    rw [show (0x3fffffffffffffffffffffffffff : ℕ) = 2 ^ 110 - 1 from hA4_pow]; exact bv_toNat_not a
  rcases hz with rfl | rfl | rfl | rfl
  · rw [BitVec.toNat_and, ← nat_land] at htry; simp only [htry, Bool.true_or]
  · rw [BitVec.toNat_or, ← nat_lor] at htry; simp only [htry, Bool.or_true, Bool.true_or]
  · rw [BitVec.toNat_and, ← nat_land, hnot_b] at htry; simp only [htry, Bool.or_true, Bool.true_or]
  · rw [BitVec.toNat_and, ← nat_land, hnot_a] at htry; simp only [htry, Bool.or_true]

theorem opt4_complete {g : W4} (hg : g = goal4 ∨ g = ~~~goal4) (n : ℕ) (ws : List W4) (extra : ℕ)
    (hn : ws.Nodup) (room : extra + ws.length = n + 1) (h : live basicOps4 g n ws.toFinset) :
    opt4 n extra (ws.map BitVec.toNat) = true := by
  have hdone : ∀ (u : List W4), u.Nodup → u.toFinset = {g} →
      (match u.map BitVec.toNat with | [w] => Nat.beq w 0x3fffffffffffff80000000000000 || Nat.beq w 0x7fffffffffffff | _ => false) = true := by
    intro u hun hu
    rw [singleton_list4 hun hu]
    rcases hg with rfl | rfl <;> decide
  induction n generalizing ws extra with
  | zero => exact hdone ws hn h
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · simp only [opt4, hdone ws hn done, Bool.true_or]
    · obtain ⟨r, hp, hpick⟩ := pickA4_exists extra (opt4 k) a b [] ws
        (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      simp only [List.nil_append] at hp
      have go {u v : W4} (perm : ws.Perm (u :: v :: r))
          (hset : ws.toFinset = insert u (insert v needed)) (hop : z ∈ basicOps4 u v) :
          disp4 extra (opt4 k) u.toNat v.toNat (r.map BitVec.toNat) = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept4 perm hn hset
        have hzu : z ≠ u := fun he => hout (hset ▸ he ▸ Finset.mem_insert_self _ _)
        have hzv : z ≠ v := fun he => hout (hset ▸ he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
        have hzr : z ∉ r := fun hr => hout (List.mem_toFinset.mpr (perm.mem_iff.mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))))
        have hznew : z ∉ kept := fun hu => hout (hset ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps4 g k (z :: kept).toFinset := by simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply disp4_complete (k := k) (extra := extra) (opt4 k) hop hzu hzv hzr hk (by omega) (by omega) (cuts4_full hg hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [opt4, Bool.or_eq_true]
      right
      rcases hpick with h1 | h2
      · exact h1 (go hp hs hz)
      · exact h2 (go (hp.trans (List.Perm.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops4_swap a b ▸ hz))

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem k4_exact : opt4 6 3 [0x2add5bab756ead800000003ff800, 0x336e6dcdb9b736800001ffc00000, 0x3c778ef1de3bc7000ffe00000000, 0x3f87f0fe1fc3f87ff00000000000] = false := by decide +kernel

lemma k4_nd : k4inputs.Nodup := by decide +kernel

lemma k4_sep_only : ∀ i : Fin 4, ∃ p : Fin 55,
    differs4 p (k4inputs.getD i.val 0) ∧
    ∀ j : Fin 4, j ≠ i → ¬ differs4 p (k4inputs.getD j.val 0) := by
  unfold differs4; decide +kernel

lemma k4_all_mem {g : W4} (hg : g = goal4 ∨ g = ~~~goal4) {k : ℕ} {s : Finset W4}
    (hsub : s ⊆ k4inputs.toFinset) (hl : live basicOps4 g k s) : s = k4inputs.toFinset := by
  apply Finset.Subset.antisymm hsub
  intro w hw
  have hw' : w ∈ k4inputs := List.mem_toFinset.mp hw
  have hidx : ∃ i : Fin 4, k4inputs.getD i.val 0 = w := by
    simp only [k4inputs, List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  obtain ⟨i, rfl⟩ := hidx
  obtain ⟨p, hpi, hpj⟩ := k4_sep_only i
  have hdg : ∀ q : Fin 55, differs4 q g := by rcases hg with rfl | rfl <;> unfold differs4 <;> decide +kernel
  obtain ⟨u, hu, hdu⟩ := live_separates (differs4 p) (hdg p) (ops4_differs p) hl
  have hu' : u ∈ k4inputs := List.mem_toFinset.mp (hsub hu)
  have hju : ∃ j : Fin 4, k4inputs.getD j.val 0 = u := by
    simp only [k4inputs, List.mem_cons, List.not_mem_nil, or_false] at hu'
    rcases hu' with rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  obtain ⟨j, rfl⟩ := hju
  by_cases hij : j = i
  · subst hij; exact hu
  · exact False.elim (hpj j hij hdu)

theorem k4_no_build6 {g : W4} (hg : g = goal4 ∨ g = ~~~goal4)
    (hb : build basicOps4 g 6 k4inputs.toFinset) : False := by
  obtain ⟨s, hsub, hl⟩ := compress hb
  have heq := k4_all_mem hg hsub hl
  rw [heq] at hl
  have hit := opt4_complete hg 6 k4inputs 3 k4_nd (by decide) hl
  have hmap : k4inputs.map BitVec.toNat = [0x2add5bab756ead800000003ff800, 0x336e6dcdb9b736800001ffc00000, 0x3c778ef1de3bc7000ffe00000000, 0x3f87f0fe1fc3f87ff00000000000] := by decide
  rw [hmap] at hit
  exact Bool.noConfusion (k4_exact.symm.trans hit)

def holds4 (av : Finset W4) (z : W4) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds4_mono {av av' : Finset W4} (sub : av ⊆ av') {x : W4} (h : holds4 av x) :
    holds4 av' x :=
  h.imp_right (Or.imp_right fun ⟨a, ha, e⟩ => ⟨a, sub ha, e⟩)

theorem holds4_not {av : Finset W4} {z : W4} (h : holds4 av z) : holds4 av (~~~z) := by
  rcases h with rfl | rfl | ⟨a, ha, he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he | he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable4 (av : Finset W4) (z : W4) : Prop :=
  holds4 av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps4 a b, holds4 (insert w av) z

theorem reachable4_not {av : Finset W4} {z : W4} (h : reachable4 av z) : reachable4 av (~~~z) := by
  rcases h with h | ⟨a, ha, b, hb, ne, w, hop, hw⟩
  · exact .inl (holds4_not h)
  · exact .inr ⟨a, ha, b, hb, ne, w, hop, holds4_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach4 {av : Finset W4} {x y : W4} (hx : holds4 av x) (hy : holds4 av y) :
    reachable4 av (x &&& y) := by
  have const : holds4 av (0 : W4) := .inl rfl
  have oldx := hx
  rcases hx with rfl | rfl | ⟨a, ha, ea⟩
  · rw [show (0 : W4) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable4 av (BitVec.allOnes 110 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl | rfl | ⟨b, hb, eb⟩
  · rw [show x &&& (0 : W4) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable4 av (x &&& BitVec.allOnes 110)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea | ea <;> rcases eb with eb | eb <;> rw [ea, eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a, ha, .inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a, ha, .inr rfl⟩))
  have add (w : W4) (hw : w ∈ basicOps4 a b) (z : W4) (hz : z = w ∨ z = ~~~w) :
      reachable4 av z :=
    .inr ⟨a, ha, b, hb, h, w, hw, .inr (.inr ⟨w, Finset.mem_insert_self .., hz⟩)⟩
  rcases ea with ea | ea <;> rcases eb with eb | eb <;> rw [ea, eb]
  · exact add _ (by simp [basicOps4, ops4] : a &&& b ∈ basicOps4 a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps4, ops4] : a &&& ~~~b ∈ basicOps4 a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps4, ops4] : b &&& ~~~a ∈ basicOps4 a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps4, ops4] : a ||| b ∈ basicOps4 a b) _ (.inr BitVec.not_or.symm)

theorem or_reach4 {av : Finset W4} {x y : W4} (hx : holds4 av x) (hy : holds4 av y) :
    reachable4 av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable4_not (and_reach4 (holds4_not hx) (holds4_not hy))

theorem mem_ops_reach4 {av : Finset W4} {x y z : W4} (hx : holds4 av x) (hy : holds4 av y)
    (hz : z ∈ basicOps4 x y) : reachable4 av z := by
  simp only [basicOps4, ops4, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact and_reach4 hx hy
  · exact or_reach4 hx hy
  · exact and_reach4 hx (holds4_not hy)
  · exact and_reach4 hy (holds4_not hx)

set_option maxRecDepth 5000 in
theorem mem_ops_const4 {av : Finset W4} {x y z : W4} (hx : holds4 av x) (hy : holds4 av y)
    (hc : (x = 0 ∨ x = ~~~0) ∨ (y = 0 ∨ y = ~~~0)) (hz : z ∈ basicOps4 x y) : holds4 av z := by
  simp only [basicOps4, ops4, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  have h0 : holds4 av (0 : W4) := .inl rfl
  have h1 : holds4 av (~~~(0 : W4)) := .inr (.inl rfl)
  have h0and (v : W4) : (0 : W4) &&& v = 0 := BitVec.zero_and
  have hand0 (v : W4) : v &&& (0 : W4) = 0 := BitVec.and_zero
  have h0or (v : W4) : (0 : W4) ||| v = v := BitVec.zero_or
  have hor0 (v : W4) : v ||| (0 : W4) = v := BitVec.or_zero
  have hand1 (v : W4) : v &&& (~~~(0 : W4)) = v :=
    (congrArg (fun u : W4 => v &&& u) (BitVec.not_zero (n := 110))).trans BitVec.and_allOnes
  have h1and (v : W4) : (~~~(0 : W4)) &&& v = v :=
    (congrArg (fun u : W4 => u &&& v) (BitVec.not_zero (n := 110))).trans BitVec.allOnes_and
  have hor1 (v : W4) : v ||| (~~~(0 : W4)) = ~~~(0 : W4) :=
    (congrArg (fun u : W4 => v ||| u) (BitVec.not_zero (n := 110))).trans (BitVec.or_allOnes.trans (BitVec.not_zero (n := 110)).symm)
  have h1or (v : W4) : (~~~(0 : W4)) ||| v = ~~~(0 : W4) :=
    (congrArg (fun u : W4 => u ||| v) (BitVec.not_zero (n := 110))).trans (BitVec.allOnes_or.trans (BitVec.not_zero (n := 110)).symm)
  rcases hc with (rfl | rfl) | (rfl | rfl) <;> rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [h0and, hand0, h0or, hor0, BitVec.not_not,
      hand1, h1and, hor1, h1or] <;>
    first | exact h0 | exact h1 | exact hx | exact hy | exact holds4_not hx | exact holds4_not hy

lemma ops4_const_both {x y z : W4} (hx : x = 0 ∨ x = ~~~0) (hy : y = 0 ∨ y = ~~~0)
    (hz : z ∈ basicOps4 x y) : z = 0 ∨ z = ~~~0 := by
  simp only [basicOps4, ops4, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl | rfl | rfl <;> decide

def SignedBuild4 (k : ℕ) (av : Finset W4) (z : W4) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ build basicOps4 z k av ∨ build basicOps4 (~~~z) k av

theorem sb4_not {av : Finset W4} {z : W4} {k : ℕ} (h : SignedBuild4 k av (~~~z)) :
    SignedBuild4 k av z := by
  rcases h with h | h | h | h
  · exact .inr (.inl (by rw [← BitVec.not_not (b := z), h]))
  · exact .inl (by rw [← BitVec.not_not (b := z), h, BitVec.not_not])
  · exact .inr (.inr (.inr h))
  · exact .inr (.inr (.inl (by simpa only [BitVec.not_not] using h)))

theorem sb4_zero {av : Finset W4} {z : W4} (h : holds4 av z) : SignedBuild4 0 av z := by
  rcases h with h | h | ⟨a, ha, rfl | rfl⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl ha))
  · exact .inr (.inr (.inr (by simpa only [BitVec.not_not, build] using ha)))

theorem sb4_wait {av : Finset W4} {z : W4} {k : ℕ} (h : SignedBuild4 k av z) :
    SignedBuild4 (k + 1) av z :=
  h.imp_right (Or.imp_right (Or.imp .inl .inl))

theorem sb4_le {av : Finset W4} {z : W4} {k l : ℕ} (hkl : k ≤ l) (h : SignedBuild4 k av z) :
    SignedBuild4 l av z := by
  induction hkl with
  | refl => exact h
  | step _ ih => exact sb4_wait ih

theorem sb4_step {av : Finset W4} {t a b z : W4} {k : ℕ} (ha : a ∈ av) (hb : b ∈ av)
    (hne : a ≠ b) (hz : z ∈ basicOps4 a b) (h : SignedBuild4 k (insert z av) t) :
    SignedBuild4 (k + 1) av t :=
  h.imp_right (Or.imp_right (Or.imp (.inr ⟨a, ha, b, hb, hne, z, hz, ·⟩) (.inr ⟨a, ha, b, hb, hne, z, hz, ·⟩)))

theorem sb4_advance {av : Finset W4} {z t : W4} {k : ℕ} (hz : reachable4 av z)
    (next : ∀ av' : Finset W4, av ⊆ av' → holds4 av' z → SignedBuild4 k av' t) :
    SignedBuild4 (k + 1) av t := by
  rcases hz with h | ⟨a, ha, b, hb, hn, w, hw, ok⟩
  · exact sb4_wait (next av (fun _ h => h) h)
  · exact sb4_step ha hb hn hw (next (insert w av) (fun _ h => Finset.mem_insert_of_mem h) ok)

theorem k4_no_signed6 : ¬ SignedBuild4 6 k4inputs.toFinset goal4 := by
  intro h
  rcases h with c | c | run | run
  · exact (by decide : goal4 ≠ 0) c
  · exact (by decide : goal4 ≠ ~~~0) c
  · exact k4_no_build6 (.inl rfl) run
  · exact k4_no_build6 (.inr rfl) run

abbrev W5 := BitVec 152
def M5 : ℕ := 0xfffffffffffffffffff
def A5 : ℕ := 0xffffffffffffffffffffffffffffffffffffff
def G5 : ℕ := 0xfffffffffffffffffff0000000000000000000
def goal5 : W5 := BitVec.ofNat 152 G5
def ops5 (x y : W5) : List W5 := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
abbrev basicOps5 (a b : W5) : Finset W5 := (ops5 a b).toFinset
def sep5 (x : W5) : BitVec 76 := ((x >>> 76) ^^^ x).setWidth 76
def cuts5 (ws : List W5) : BitVec 76 := ws.foldr (fun w v => sep5 w ||| v) 0

def x0 : W5 := BitVec.ofNat 152 0xab7712c4b12c4b12c4b00000000000000ffc00
def x1 : W5 := BitVec.ofNat 152 0xcdbb254952549525495000000000003ff00000
def x2 : W5 := BitVec.ofNat 152 0xf1dd499264992649926000000000ffc0000000
def x3 : W5 := BitVec.ofNat 152 0xfe1e8e2388e2388e2380000003ff0000000000
def x4 : W5 := BitVec.ofNat 152 0xffe0f03c0f03c0f03c00000ffc000000000000
def x01 : W5 := x0 ||| x1
def x02 : W5 := x0 ||| x2
def x23 : W5 := x2 ||| x3
def w03_or : W5 := x01 ||| x2
def w03_an : W5 := x01 &&& ~~~x2
def in5 : List W5 := [x0, x1, x2, x3, x4]
def vinput5 (i : Fin 5) : W5 := in5.getD i.val 0
def mask5 (i : Fin 5) : W5 := ~~~(vinput5 i)

lemma hM5_pow : M5 = 2 ^ 76 - 1 := by decide
lemma hA5_pow : A5 = 2 ^ 152 - 1 := by decide

def sep5N (w : ℕ) : ℕ := Nat.land (Nat.xor (Nat.shiftRight w 76) w) 0xfffffffffffffffffff

lemma sep5_toNat (w : W5) : (sep5 w).toNat = sep5N w.toNat := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [sep5N, show (0xfffffffffffffffffff : ℕ) = 2 ^ 76 - 1 from hM5_pow, nat_land, nat_xor, nat_shr]
  rw [BitVec.testBit_toNat, Nat.testBit_land, Nat.testBit_xor, Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one, BitVec.testBit_toNat, BitVec.testBit_toNat]
  by_cases hk : k < 76
  · simp [sep5, hk, Nat.add_comm]
  · rw [BitVec.getLsbD_of_ge (sep5 w) k (Nat.le_of_not_lt hk)]; simp [hk]

def cuts5N : List ℕ → ℕ
  | [] => 0
  | w :: r => Nat.lor (sep5N w) (cuts5N r)

lemma cuts5N_map (ws : List W5) : cuts5N (ws.map BitVec.toNat) = (cuts5 ws).toNat := by
  induction ws with
  | nil => simp [cuts5, cuts5N]
  | cons w r ih =>
    simp only [List.map_cons, cuts5N, cuts5, List.foldr_cons, BitVec.toNat_or, sep5_toNat, ih]
    rfl

def differs5 (i : Fin 76) (w : W5) : Prop :=
  w.getLsbD (76 + i.val) ≠ w.getLsbD i.val

theorem ops5_differs (i : Fin 76) (a b z : W5) (hz : z ∈ basicOps5 a b)
    (hd : differs5 i z) : differs5 i a ∨ differs5 i b := by
  simp only [basicOps5, ops5, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha, hb⟩ := fail
  apply hd
  unfold differs5 at ha hb
  simp only [not_not] at ha hb
  have hi : 76 + i.val < 152 := by omega
  have hi' : i.val < 152 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts5_spec (ws : List W5) (i : Fin 76) :
    (cuts5 ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs5 i w := by
  induction ws with
  | nil => simp [cuts5]
  | cons a rest ih =>
    change (sep5 a ||| cuts5 rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep5, i.isLt, differs5, Nat.add_comm, bx]

theorem cuts5_full {g : W5} (hg : g = goal5 ∨ g = ~~~goal5) {k : ℕ} {ws : List W5}
    (h : live basicOps5 g k ws.toFinset) : cuts5N (ws.map BitVec.toNat) = M5 := by
  rw [cuts5N_map]
  have hd : ∀ i, differs5 i g := by rcases hg with rfl | rfl <;> unfold differs5 <;> decide +kernel
  have hall : cuts5 ws = -1 := by
    apply BitVec.eq_of_getElem_eq
    intro j hj
    have hw := live_separates (differs5 ⟨j, hj⟩) (hd ⟨j, hj⟩) (ops5_differs ⟨j, hj⟩) h
    have hbit := (cuts5_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
    change (cuts5 ws)[j] = (BitVec.allOnes 76)[j]
    rw [BitVec.getElem_allOnes]
    simpa only [BitVec.getLsbD_eq_getElem hj] using hbit
  rw [hall]
  decide

theorem ops5_swap (a b : W5) : basicOps5 a b = basicOps5 b a := by
  ext z
  simp only [basicOps5, ops5, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices5 (a b : W5) (r : List W5) : List (List W5) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept5 {ws r : List W5} {a b : W5} {needed : Finset W5}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices5 a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v; simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices5], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices5], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices5], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices5], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list5 {g : W5} {ws : List W5} (hn : ws.Nodup) (hs : ws.toFinset = {g}) : ws = [g] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def holds5 (av : Finset W5) (z : W5) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds5_mono {av av' : Finset W5} (sub : av ⊆ av') {x : W5} (h : holds5 av x) :
    holds5 av' x :=
  h.imp_right (Or.imp_right fun ⟨a, ha, e⟩ => ⟨a, sub ha, e⟩)

theorem holds5_not {av : Finset W5} {z : W5} (h : holds5 av z) : holds5 av (~~~z) := by
  rcases h with rfl | rfl | ⟨a, ha, he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he | he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable5 (av : Finset W5) (z : W5) : Prop :=
  holds5 av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps5 a b, holds5 (insert w av) z

theorem reachable5_not {av : Finset W5} {z : W5} (h : reachable5 av z) : reachable5 av (~~~z) := by
  rcases h with h | ⟨a, ha, b, hb, ne, w, hop, hw⟩
  · exact .inl (holds5_not h)
  · exact .inr ⟨a, ha, b, hb, ne, w, hop, holds5_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach5 {av : Finset W5} {x y : W5} (hx : holds5 av x) (hy : holds5 av y) :
    reachable5 av (x &&& y) := by
  have const : holds5 av (0 : W5) := .inl rfl
  have oldx := hx
  rcases hx with rfl | rfl | ⟨a, ha, ea⟩
  · rw [show (0 : W5) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable5 av (BitVec.allOnes 152 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl | rfl | ⟨b, hb, eb⟩
  · rw [show x &&& (0 : W5) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable5 av (x &&& BitVec.allOnes 152)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea | ea <;> rcases eb with eb | eb <;> rw [ea, eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a, ha, .inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a, ha, .inr rfl⟩))
  have add (w : W5) (hw : w ∈ basicOps5 a b) (z : W5) (hz : z = w ∨ z = ~~~w) :
      reachable5 av z :=
    .inr ⟨a, ha, b, hb, h, w, hw, .inr (.inr ⟨w, Finset.mem_insert_self .., hz⟩)⟩
  rcases ea with ea | ea <;> rcases eb with eb | eb <;> rw [ea, eb]
  · exact add _ (by simp [basicOps5, ops5] : a &&& b ∈ basicOps5 a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps5, ops5] : a &&& ~~~b ∈ basicOps5 a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps5, ops5] : b &&& ~~~a ∈ basicOps5 a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps5, ops5] : a ||| b ∈ basicOps5 a b) _ (.inr BitVec.not_or.symm)

theorem or_reach5 {av : Finset W5} {x y : W5} (hx : holds5 av x) (hy : holds5 av y) :
    reachable5 av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable5_not (and_reach5 (holds5_not hx) (holds5_not hy))

private def bit (k : Fin 152) (z : W5) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W5) (i : ℕ) (k : Fin 152) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W5) (g : Gate) : W5 := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W5) (g : Gate) (hg : legal g) (k : Fin 152) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W5)[k.val] = false := by change (BitVec.ofNat 152 0)[k.val] = false; simp
  all_goals rcases hop with rfl | rfl | rfl <;>
    simp only [step, List.map_cons, List.map_nil, read_bit, List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons, List.foldr_nil, List.head?_cons, List.head?_nil,
      List.headD_cons, List.headD_nil, Option.map_some, Option.map_none, Option.getD_some, Option.getD_none,
      List.all_cons, List.all_nil, List.any_cons, List.any_nil, List.map_cons, List.map_nil, id_eq,
      Bool.and_true, Bool.or_false, bit, BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not,
      bit0, Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read5 {av : Finset W5} {w : List W5} (hw : ∀ u ∈ w, holds5 av u) (i : ℕ) :
    holds5 av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W5) (av : Finset W5) (hw : ∀ u ∈ w, holds5 av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable5 av (action w g) else holds5 av (action w g) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl | rfl | rfl <;> simp only [isBinary, Bool.false_eq_true, ite_false, ite_true,
    action, List.head?_nil, List.head?_cons, List.map_nil, List.map_cons, List.foldr_nil, List.foldr_cons,
    Option.map_none, Option.map_some, Option.getD_none, Option.getD_some,
    show ∀ x : W5, x ||| (0 : W5) = x from fun x => BitVec.or_zero,
    show ∀ x : W5, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read5 hw _)
    | exact holds5_not (available_read5 hw _)
    | exact and_reach5 (available_read5 hw _) (available_read5 hw _)
    | exact or_reach5 (available_read5 hw _) (available_read5 hw _)

set_option maxRecDepth 4000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W5) (av : Finset W5) (hw : ∀ u ∈ w, holds5 av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k goal5) :
    ∃ t, (t = goal5 ∨ t = ~~~goal5) ∧ build basicOps5 t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = goal5 := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i, hi⟩
    have h := hv ▸ available_read5 hw out
    rcases h with zero | ones | ⟨t, ht, eq | eq⟩
    · exact False.elim ((by decide : goal5 ≠ 0) zero)
    · exact False.elim ((by decide : goal5 ≠ ~~~0) ones)
    · exact ⟨t, .inl eq.symm, ht⟩
    · exact ⟨t, .inr (by rw [eq, BitVec.not_not]), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal5 := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W5) (hold : ∀ u ∈ w, holds5 A u) (new : holds5 A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu | hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg, Bool.false_eq_true, ite_false] at stepClass
      simpa [binaryCost, neg] using cont av hw stepClass
    · simp only [neg, ite_true] at stepClass
      have len : binaryCost (g :: gs) = binaryCost gs + 1 := by simp [binaryCost, neg]
      rw [len]
      rcases stepClass with existing | ⟨a, ha, b, hb, ne, new, op, rep⟩
      · obtain ⟨t, ht, run⟩ := cont av hw existing
        exact ⟨t, ht, Or.inl run⟩
      · obtain ⟨t, ht, run⟩ := cont (insert new av) (fun u hu => holds5_mono (Finset.subset_insert _ _) (hw u hu)) rep
        exact ⟨t, ht, Or.inr ⟨a, ha, b, hb, ne, new, op, run⟩⟩

def table (x : Fin 5 → Bool) : Bool :=
  Nat.testBit 0xfffefee8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

theorem spec_k5 : ∀ j : Fin 152,
    Nat.testBit 0xfffefee8 (∑ i : Fin 5, if (in5.getD i.val 0)[j.val] then 2 ^ (i : ℕ) else 0) = goal5[j.val] := by
  intro j; rw [Fin.sum_univ_five]; revert j; decide +kernel

def src4Tbl : Fin 5 → List ℕ :=
  ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 78, 80, 81, 139, 83, 84, 143, 85, 146, 148, 150, 78, 80, 81, 139, 83, 84, 143, 85, 146, 148, 150, 78, 80, 81, 139, 83, 84, 143, 85, 146, 148, 150, 78, 80, 81, 139, 83, 84, 143, 85, 146, 148, 150, 78, 80, 81, 139, 83, 84, 143, 85, 146, 148, 150],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 77, 79, 81, 138, 82, 84, 142, 85, 145, 148, 149, 77, 79, 81, 138, 82, 84, 142, 85, 145, 148, 149, 77, 79, 81, 138, 82, 84, 142, 85, 145, 148, 149, 77, 79, 81, 138, 82, 84, 142, 85, 145, 148, 149, 77, 79, 81, 138, 82, 84, 142, 85, 145, 148, 149],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 76, 79, 80, 137, 82, 83, 141, 85, 145, 146, 147, 76, 79, 80, 137, 82, 83, 141, 85, 145, 146, 147, 76, 79, 80, 137, 82, 83, 141, 85, 145, 146, 147, 76, 79, 80, 137, 82, 83, 141, 85, 145, 146, 147, 76, 79, 80, 137, 82, 83, 141, 85, 145, 146, 147],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 76, 77, 78, 136, 82, 83, 141, 84, 142, 143, 144, 76, 77, 78, 136, 82, 83, 141, 84, 142, 143, 144, 76, 77, 78, 136, 82, 83, 141, 84, 142, 143, 144, 76, 77, 78, 136, 82, 83, 141, 84, 142, 143, 144, 76, 77, 78, 136, 82, 83, 141, 84, 142, 143, 144],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 76, 77, 78, 136, 79, 80, 137, 81, 138, 139, 140, 76, 77, 78, 136, 79, 80, 137, 81, 138, 139, 140, 76, 77, 78, 136, 79, 80, 137, 81, 138, 139, 140, 76, 77, 78, 136, 79, 80, 137, 81, 138, 139, 140, 76, 77, 78, 136, 79, 80, 137, 81, 138, 139, 140]]

def src4Ix (i : Fin 5) (b : Fin 110) : Fin 152 :=
  ⟨(src4Tbl i).getD b.val 0 % 152, Nat.mod_lt _ (by decide)⟩

def rest4 (i : Fin 5) (w : W5) : W4 :=
  (BitVec.ofBoolListLE (List.ofFn (fun b : Fin 110 => w[(src4Ix i b).val]))).cast List.length_ofFn

theorem rest4_bit (i : Fin 5) (w : W5) (b : ℕ) (hb : b < 110) :
    (rest4 i w)[b] = w[(src4Ix i ⟨b, hb⟩).val] := by
  rw [← BitVec.getLsbD_eq_getElem hb]
  simp only [rest4, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, hb, dite_true, Option.getD_some]

theorem rest4_not (i : Fin 5) (u : W5) : rest4 i (~~~u) = ~~~rest4 i u :=
  BitVec.eq_of_getElem_eq fun b hb => by simp only [rest4_bit, BitVec.getElem_not]

theorem rest4_ops (i : Fin 5) (a b z : W5) (hz : z ∈ basicOps5 a b) :
    rest4 i z ∈ basicOps4 (rest4 i a) (rest4 i b) := by
  have hand (u v : W5) : rest4 i (u &&& v) = rest4 i u &&& rest4 i v :=
    BitVec.eq_of_getElem_eq fun b hb => by simp only [rest4_bit, BitVec.getElem_and]
  have hor (u v : W5) : rest4 i (u ||| v) = rest4 i u ||| rest4 i v :=
    BitVec.eq_of_getElem_eq fun b hb => by simp only [rest4_bit, BitVec.getElem_or]
  simp only [basicOps5, ops5, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  simp only [basicOps4, ops4, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rcases hz with rfl | rfl | rfl | rfl <;> simp [hand, hor, rest4_not]

set_option maxRecDepth 8000 in
theorem rest4_goal : ∀ i : Fin 5, rest4 i goal5 = goal4 := by decide +kernel

set_option maxRecDepth 8000 in
theorem rest4_avail : ∀ i j : Fin 5, rest4 i (vinput5 j) = 0 ∨ rest4 i (vinput5 j) ∈ k4inputs := by
  decide +kernel

theorem rest4_holds (i j : Fin 5) : holds4 k4inputs.toFinset (rest4 i (vinput5 j)) := by
  rcases rest4_avail i j with h | h
  · exact .inl h
  · exact .inr (.inr ⟨_, List.mem_toFinset.mpr h, .inl rfl⟩)

set_option maxRecDepth 8000 in
theorem src4_mask : ∀ (i : Fin 5) (b : Fin 110), (mask5 i)[(src4Ix i b).val] = true := by
  decide +kernel

def isC (m w : ℕ) : Bool :=
  let v := Nat.land w m
  Nat.beq v 0 || Nat.beq v m

lemma isC_sound (i : Fin 5) (w : W5) (h : isC (mask5 i).toNat w.toNat = true) :
    rest4 i w = 0 ∨ rest4 i w = ~~~0 := by
  unfold isC at h
  simp only [Bool.or_eq_true, Nat.beq_eq] at h
  rcases h with h0 | hm
  · left
    apply BitVec.eq_of_getElem_eq
    intro b hb
    rw [rest4_bit]
    have hbit : (w &&& mask5 i)[(src4Ix i ⟨b, hb⟩).val] = (0 : W5)[(src4Ix i ⟨b, hb⟩).val] := by
      have heq : w &&& mask5 i = 0 := BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_and]; exact h0)
      rw [heq]
    rw [BitVec.getElem_and, src4_mask i ⟨b, hb⟩, Bool.and_true] at hbit
    simpa using hbit
  · right
    apply BitVec.eq_of_getElem_eq
    intro b hb
    rw [rest4_bit]
    have hbit : (w &&& mask5 i)[(src4Ix i ⟨b, hb⟩).val] = (mask5 i)[(src4Ix i ⟨b, hb⟩).val] := by
      have heq : w &&& mask5 i = mask5 i := BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_and]; exact hm)
      rw [heq]
    rw [BitVec.getElem_and, src4_mask i ⟨b, hb⟩, Bool.and_true] at hbit
    change w[(src4Ix i ⟨b, hb⟩).val] = (BitVec.allOnes 110)[b]
    rw [BitVec.getElem_allOnes]
    exact hbit

theorem live_transport_saveN {f : W5 → W4}
    (hm : ∀ a b z, z ∈ basicOps5 a b → f z ∈ basicOps4 (f a) (f b))
    {g : W5} (hg : f g ≠ 0 ∧ f g ≠ ~~~0) {k : ℕ} {s : Finset W5} {av : Finset W4}
    (run : live basicOps5 g k s) (hav : ∀ w ∈ s, holds4 av (f w))
    (P : Finset W5) (hPs : P ⊆ s) (hP0 : ∀ p ∈ P, f p = 0 ∨ f p = ~~~0) :
    P.card ≤ k ∧ SignedBuild4 (k - P.card) av (f g) := by
  classical
  induction k generalizing s av P with
  | zero =>
    change s = {g} at run
    have hPe : P = ∅ := by
      ext p
      simp only [Finset.notMem_empty, iff_false]
      intro hp
      have hpg : p = g := Finset.mem_singleton.mp (run ▸ hPs hp)
      subst hpg
      rcases hP0 p hp with h | h
      · exact hg.1 h
      · exact hg.2 h
    rw [hPe, Finset.card_empty, Nat.sub_zero]
    exact ⟨le_refl 0, sb4_zero (hav g (by simp [run]))⟩
  | succ k ih =>
    rcases run with skip | ⟨a, ha, b, hb, hab, z, hz, hout, r, hs, tail⟩
    · obtain ⟨hck, hsb⟩ := ih skip hav P hPs hP0
      exact ⟨Nat.le_succ_of_le hck, sb4_le (by omega) hsb⟩
    · have mapped := hm a b z hz
      have hrsub : ∀ u ∈ r, u ∈ s := fun u hu => hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu)
      have inOld : ∀ u ∈ r, holds4 av (f u) := fun u hu => hav u (hrsub u hu)
      by_cases haP : a ∈ P
      · by_cases hbP : b ∈ P
        · have hfz0 : f z = 0 ∨ f z = ~~~0 := ops4_const_both (hP0 a haP) (hP0 b hbP) mapped
          have hfzH : holds4 av (f z) := mem_ops_const4 (hav a ha) (hav b hb) (.inl (hP0 a haP)) mapped
          let P' := insert z ((P.erase a).erase b)
          have hznot : z ∉ (P.erase a).erase b := fun hm =>
            hout (hPs (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hm)))
          have hbPa : b ∈ P.erase a := Finset.mem_erase.mpr ⟨hab.symm, hbP⟩
          have hcard : P'.card = P.card - 1 := by
            rw [Finset.card_insert_of_notMem hznot, Finset.card_erase_of_mem hbPa,
              Finset.card_erase_of_mem haP]
            have h2 : 2 ≤ P.card := by
              have := Finset.one_lt_card.mpr ⟨a, haP, b, hbP, hab⟩; omega
            omega
          have hP'sub : P' ⊆ insert z r := by
            intro u hu
            rcases Finset.mem_insert.mp hu with rfl | hu'
            · exact Finset.mem_insert_self _ _
            · have h1 := Finset.mem_erase.mp hu'
              have h2 := Finset.mem_erase.mp h1.2
              have hus : u ∈ s := hPs h2.2
              rw [hs] at hus
              rcases Finset.mem_insert.mp hus with rfl | hus'
              · exact absurd rfl h2.1
              · rcases Finset.mem_insert.mp hus' with rfl | hur
                · exact absurd rfl h1.1
                · exact Finset.mem_insert_of_mem hur
          have hP'0 : ∀ p ∈ P', f p = 0 ∨ f p = ~~~0 := by
            intro p hp
            rcases Finset.mem_insert.mp hp with rfl | hp'
            · exact hfz0
            · exact hP0 p (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hp'))
          obtain ⟨hck, hsb⟩ := ih tail (fun u hu => by
            rcases Finset.mem_insert.mp hu with rfl | hur
            · exact hfzH
            · exact inOld u hur) P' hP'sub hP'0
          rw [hcard] at hck hsb
          have h2 : 2 ≤ P.card := by
            have := Finset.one_lt_card.mpr ⟨a, haP, b, hbP, hab⟩; omega
          exact ⟨by omega, sb4_le (by omega) hsb⟩
        · have hfzH : holds4 av (f z) := mem_ops_const4 (hav a ha) (hav b hb) (.inl (hP0 a haP)) mapped
          let P' := P.erase a
          have hcard : P'.card = P.card - 1 := Finset.card_erase_of_mem haP
          have hP'sub : P' ⊆ insert z r := by
            intro u hu
            have h1 := Finset.mem_erase.mp hu
            have hus : u ∈ s := hPs h1.2
            rw [hs] at hus
            rcases Finset.mem_insert.mp hus with rfl | hus'
            · exact absurd rfl h1.1
            · rcases Finset.mem_insert.mp hus' with rfl | hur
              · exact absurd h1.2 hbP
              · exact Finset.mem_insert_of_mem hur
          have hP'0 : ∀ p ∈ P', f p = 0 ∨ f p = ~~~0 := fun p hp => hP0 p (Finset.mem_of_mem_erase hp)
          obtain ⟨hck, hsb⟩ := ih tail (fun u hu => by
            rcases Finset.mem_insert.mp hu with rfl | hur
            · exact hfzH
            · exact inOld u hur) P' hP'sub hP'0
          rw [hcard] at hck hsb
          have h1 : 1 ≤ P.card := Finset.card_pos.mpr ⟨a, haP⟩
          exact ⟨by omega, sb4_le (by omega) hsb⟩
      · by_cases hbP : b ∈ P
        · have hfzH : holds4 av (f z) := mem_ops_const4 (hav a ha) (hav b hb) (.inr (hP0 b hbP)) mapped
          let P' := P.erase b
          have hcard : P'.card = P.card - 1 := Finset.card_erase_of_mem hbP
          have hP'sub : P' ⊆ insert z r := by
            intro u hu
            have h1 := Finset.mem_erase.mp hu
            have hus : u ∈ s := hPs h1.2
            rw [hs] at hus
            rcases Finset.mem_insert.mp hus with rfl | hus'
            · exact absurd h1.2 haP
            · rcases Finset.mem_insert.mp hus' with rfl | hur
              · exact absurd rfl h1.1
              · exact Finset.mem_insert_of_mem hur
          have hP'0 : ∀ p ∈ P', f p = 0 ∨ f p = ~~~0 := fun p hp => hP0 p (Finset.mem_of_mem_erase hp)
          obtain ⟨hck, hsb⟩ := ih tail (fun u hu => by
            rcases Finset.mem_insert.mp hu with rfl | hur
            · exact hfzH
            · exact inOld u hur) P' hP'sub hP'0
          rw [hcard] at hck hsb
          have h1 : 1 ≤ P.card := Finset.card_pos.mpr ⟨b, hbP⟩
          exact ⟨by omega, sb4_le (by omega) hsb⟩
        · have hPsub : P ⊆ insert z r := by
            intro u hu
            have hus : u ∈ s := hPs hu
            rw [hs] at hus
            rcases Finset.mem_insert.mp hus with rfl | hus'
            · exact absurd hu haP
            · rcases Finset.mem_insert.mp hus' with rfl | hur
              · exact absurd hu hbP
              · exact Finset.mem_insert_of_mem hur
          have hreach := mem_ops_reach4 (hav a ha) (hav b hb) mapped
          have hck : P.card ≤ k := by
            rcases hreach with h | ⟨u, hu, v, hv, hne, w, hw, hok⟩
            · exact (ih tail (fun t ht => by
                rcases Finset.mem_insert.mp ht with rfl | htr
                · exact h
                · exact inOld t htr) P hPsub hP0).1
            · exact (ih tail (fun t ht => by
                rcases Finset.mem_insert.mp ht with rfl | htr
                · exact hok
                · exact holds4_mono (Finset.subset_insert w av) (inOld t htr)) P hPsub hP0).1
          refine ⟨Nat.le_succ_of_le hck, ?_⟩
          have hsub_eq : k + 1 - P.card = (k - P.card) + 1 := by omega
          rw [hsub_eq]
          apply sb4_advance hreach
          intro av' sub ok
          exact (ih tail (fun t ht => by
            rcases Finset.mem_insert.mp ht with rfl | htr
            · exact ok
            · exact holds4_mono sub (inOld t htr)) P hPsub hP0).2

def HasAvoid (k : ℕ) (s : Fin 5 → ℕ) (ws : Finset W5) : Prop :=
  ∀ i : Fin 5, ∃ av : Finset W4,
    (∀ w ∈ ws, holds4 av (rest4 i w)) ∧
    (3 ≤ k + s i → ¬ SignedBuild4 (k + s i - 3) av goal4)

lemma hasAvoid_init {ws : Finset W5} (hsub : ws ⊆ in5.toFinset) :
    HasAvoid 9 (fun _ => 0) ws := by
  intro i
  refine ⟨k4inputs.toFinset, ?_, fun _ => k4_no_signed6⟩
  intro w hw
  have hw' : w ∈ in5 := List.mem_toFinset.mp (hsub hw)
  simp only [in5, List.mem_cons, List.not_mem_nil, or_false] at hw'
  rcases hw' with rfl | rfl | rfl | rfl | rfl
  · exact rest4_holds i 0
  · exact rest4_holds i 1
  · exact rest4_holds i 2
  · exact rest4_holds i 3
  · exact rest4_holds i 4

lemma hasAvoid_step {k : ℕ} {s : Fin 5 → ℕ} {ws ws' : Finset W5} {a b z : W5}
    (hav : HasAvoid (k + 1) s ws) (ha : a ∈ ws) (hb : b ∈ ws)
    (hz : z ∈ basicOps5 a b) (hsub : ws' ⊆ insert z ws) :
    HasAvoid k (fun i => s i + if isC (mask5 i).toNat a.toNat || isC (mask5 i).toNat b.toNat then 1 else 0) ws' := by
  intro i
  obtain ⟨av, hhold, hno⟩ := hav i
  have mapped := rest4_ops i a b z hz
  cases hc : (isC (mask5 i).toNat a.toNat || isC (mask5 i).toNat b.toNat)
  · rcases mem_ops_reach4 (hhold a ha) (hhold b hb) mapped with hok | ⟨u, hu, v, hv, hne, w, hw, hok⟩
    · refine ⟨av, fun t ht => ?_, fun h3 hsb => ?_⟩
      · rcases Finset.mem_insert.mp (hsub ht) with rfl | htw
        · exact hok
        · exact hhold t htw
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at h3 hsb
        exact hno (by omega) (sb4_le (by omega) hsb)
    · refine ⟨insert w av, fun t ht => ?_, fun h3 hsb => ?_⟩
      · rcases Finset.mem_insert.mp (hsub ht) with rfl | htw
        · exact hok
        · exact holds4_mono (Finset.subset_insert w av) (hhold t htw)
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at h3 hsb
        have hsb' : SignedBuild4 (k + 1 + s i - 3) av goal4 := by
          have heq : k + 1 + s i - 3 = (k + s i - 3) + 1 := by omega
          rw [heq]
          exact sb4_step hu hv hne hw hsb
        exact hno (by omega) hsb'
  · have hconst : (rest4 i a = 0 ∨ rest4 i a = ~~~0) ∨ (rest4 i b = 0 ∨ rest4 i b = ~~~0) := by
      rcases Bool.or_eq_true_iff.mp hc with hca | hcb
      · exact .inl (isC_sound i a hca)
      · exact .inr (isC_sound i b hcb)
    have hok := mem_ops_const4 (hhold a ha) (hhold b hb) hconst mapped
    refine ⟨av, fun t ht => ?_, fun h3 hsb => ?_⟩
    · rcases Finset.mem_insert.mp (hsub ht) with rfl | htw
      · exact hok
      · exact hhold t htw
    · simp only [hc, ↓reduceIte] at h3 hsb
      exact hno (by omega) (by convert hsb using 2; omega)

def okOne (m s : ℕ) : List ℕ → Bool
  | [] => true
  | w :: rest =>
    if isC m w then
      if Nat.ble 2 s then false else okOne m (Nat.add s 1) rest
    else okOne m s rest

def okAll (s0 s1 s2 s3 s4 : ℕ) (ws : List ℕ) : Bool :=
  okOne 0x5488ed3b4ed3b4ed3b4ffffffffffffff003ff s0 ws &&
  okOne 0x3244dab6adab6adab6afffffffffffc00fffff s1 ws &&
  okOne 0xe22b66d9b66d9b66d9fffffffff003fffffff s2 ws &&
  okOne 0x1e171dc771dc771dc7ffffffc00ffffffffff s3 ws &&
  okOne 0x1f0fc3f0fc3f0fc3fffff003ffffffffffff s4 ws

lemma okOne_false_card (m s : ℕ) (ws : List W5) (hnd : ws.Nodup)
    (h : okOne m s (ws.map BitVec.toNat) = false) :
    3 ≤ s + (ws.toFinset.filter (fun w => isC m w.toNat = true)).card := by
  induction ws generalizing s with
  | nil => simp [okOne] at h
  | cons w rest ih =>
    obtain ⟨hwnot, hnd_r⟩ := List.nodup_cons.mp hnd
    have hwnot_f : w ∉ rest.toFinset := fun hm => hwnot (List.mem_toFinset.mp hm)
    simp only [List.map_cons, okOne] at h
    cases hc : isC m w.toNat
    · rw [hc] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
      have hrec := ih s hnd_r h
      have hfil : ((w :: rest).toFinset.filter (fun u => isC m u.toNat = true)) =
          rest.toFinset.filter (fun u => isC m u.toNat = true) := by
        ext u; simp only [List.toFinset_cons, Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hr, hu⟩
          · rw [hc] at hu; cases hu
          · exact ⟨hr, hu⟩
        · rintro ⟨hr, hu⟩; exact ⟨.inr hr, hu⟩
      rw [hfil]; exact hrec
    · rw [hc] at h; simp only [↓reduceIte] at h
      have hfil : ((w :: rest).toFinset.filter (fun u => isC m u.toNat = true)) =
          insert w (rest.toFinset.filter (fun u => isC m u.toNat = true)) := by
        ext u; simp only [List.toFinset_cons, Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hr, hu⟩
          · exact .inl rfl
          · exact .inr ⟨hr, hu⟩
        · rintro (rfl | ⟨hr, hu⟩)
          · exact ⟨.inl rfl, hc⟩
          · exact ⟨.inr hr, hu⟩
      have hwnot_fil : w ∉ rest.toFinset.filter (fun u => isC m u.toNat = true) :=
        fun hm => hwnot_f (Finset.mem_filter.mp hm).1
      rw [hfil, Finset.card_insert_of_notMem hwnot_fil]
      cases hle : Nat.ble 2 s
      · rw [hle] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
        have hrec := ih (Nat.add s 1) hnd_r h
        rw [nat_add] at hrec
        omega
      · have h2 : 2 ≤ s := Nat.ble_eq.mp hle
        omega

lemma rest4_g_ne {g : W5} (hg : g = goal5 ∨ g = ~~~goal5) (i : Fin 5) :
    rest4 i g ≠ 0 ∧ rest4 i g ≠ ~~~0 := by
  have hne : goal4 ≠ 0 ∧ goal4 ≠ ~~~0 ∧ ~~~goal4 ≠ 0 ∧ ~~~goal4 ≠ ~~~0 := by decide
  rcases hg with rfl | rfl
  · rw [rest4_goal]; exact ⟨hne.1, hne.2.1⟩
  · rw [rest4_not, rest4_goal]; exact ⟨hne.2.2.1, hne.2.2.2⟩

lemma sb4_of_rest4_g {g : W5} (hg : g = goal5 ∨ g = ~~~goal5) (i : Fin 5) {k : ℕ} {av : Finset W4}
    (h : SignedBuild4 k av (rest4 i g)) : SignedBuild4 k av goal4 := by
  rcases hg with rfl | rfl
  · rwa [rest4_goal] at h
  · rw [rest4_not, rest4_goal] at h; exact sb4_not h

lemma hasAvoid_s_lt3 {g : W5} (hg : g = goal5 ∨ g = ~~~goal5) {k : ℕ} {s : Fin 5 → ℕ} {ws : Finset W5}
    (hl : live basicOps5 g k ws) (hav : HasAvoid k s ws) (i : Fin 5) : s i < 3 := by
  by_contra hge
  obtain ⟨av, hhold, hno⟩ := hav i
  have ⟨_, hsb⟩ := live_transport_saveN (rest4_ops i) (rest4_g_ne hg i) hl hhold ∅
    (Finset.empty_subset _) (fun _ h => absurd h (Finset.notMem_empty _))
  rw [Finset.card_empty, Nat.sub_zero] at hsb
  exact hno (by omega) (sb4_le (by omega) (sb4_of_rest4_g hg i hsb))

lemma hasAvoid_okOne {g : W5} (hg : g = goal5 ∨ g = ~~~goal5) {k : ℕ} {s : Fin 5 → ℕ} {ws : List W5}
    (hnd : ws.Nodup) (hl : live basicOps5 g k ws.toFinset) (hav : HasAvoid k s ws.toFinset) (i : Fin 5) :
    okOne (mask5 i).toNat (s i) (ws.map BitVec.toNat) = true := by
  cases h : okOne (mask5 i).toNat (s i) (ws.map BitVec.toNat)
  · exfalso
    have hcard := okOne_false_card (mask5 i).toNat (s i) ws hnd h
    obtain ⟨av, hhold, hno⟩ := hav i
    let P := ws.toFinset.filter (fun w => isC (mask5 i).toNat w.toNat = true)
    have hcard' : 3 ≤ s i + P.card := hcard
    have ⟨hPk, hsb⟩ := live_transport_saveN (rest4_ops i) (rest4_g_ne hg i) hl hhold P
      (Finset.filter_subset _ _) (fun p hp => isC_sound i p (by simpa [P] using (Finset.mem_filter.mp hp).2))
    exact hno (by omega) (sb4_le (by omega) (sb4_of_rest4_g hg i hsb))
  · rfl

lemma mask5_toNat_vals :
    (mask5 0).toNat = 0x5488ed3b4ed3b4ed3b4ffffffffffffff003ff ∧
    (mask5 1).toNat = 0x3244dab6adab6adab6afffffffffffc00fffff ∧
    (mask5 2).toNat = 0xe22b66d9b66d9b66d9fffffffff003fffffff ∧
    (mask5 3).toNat = 0x1e171dc771dc771dc7ffffffc00ffffffffff ∧
    (mask5 4).toNat = 0x1f0fc3f0fc3f0fc3fffff003ffffffffffff := by decide

lemma hasAvoid_okAll {g : W5} (hg : g = goal5 ∨ g = ~~~goal5) {k : ℕ} {s : Fin 5 → ℕ} {ws : List W5}
    (hnd : ws.Nodup) (hl : live basicOps5 g k ws.toFinset) (hav : HasAvoid k s ws.toFinset) :
    okAll (s 0) (s 1) (s 2) (s 3) (s 4) (ws.map BitVec.toNat) = true := by
  unfold okAll
  have hm := mask5_toNat_vals
  rw [← hm.1, ← hm.2.1, ← hm.2.2.1, ← hm.2.2.2.1, ← hm.2.2.2.2]
  simp only [hasAvoid_okOne hg hnd hl hav 0, hasAvoid_okOne hg hnd hl hav 1,
    hasAvoid_okOne hg hnd hl hav 2, hasAvoid_okOne hg hnd hl hav 3,
    hasAvoid_okOne hg hnd hl hav 4, Bool.and_self]

def tryW5 (extra ns0 ns1 ns2 ns3 ns4 : ℕ)
    (next : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → Bool)
    (a b sa sb base : ℕ) (r : List ℕ) (w : ℕ) : Bool :=
  if Nat.beq w a || Nat.beq w b || elemN w r then false
  else
    let v := Nat.lor (sep5N w) base
    if Nat.beq v 0xfffffffffffffffffff && okAll ns0 ns1 ns2 ns3 ns4 (w :: r) && next extra ns0 ns1 ns2 ns3 ns4 (w :: r) then true
    else if Nat.beq extra 0 then false
    else if Nat.beq (Nat.lor v sa) 0xfffffffffffffffffff && okAll ns0 ns1 ns2 ns3 ns4 (w :: a :: r) && next (Nat.sub extra 1) ns0 ns1 ns2 ns3 ns4 (w :: a :: r) then true
    else if Nat.beq (Nat.lor v sb) 0xfffffffffffffffffff && okAll ns0 ns1 ns2 ns3 ns4 (w :: b :: r) && next (Nat.sub extra 1) ns0 ns1 ns2 ns3 ns4 (w :: b :: r) then true
    else if Nat.ble 2 extra && Nat.beq (Nat.lor (Nat.lor v sa) sb) 0xfffffffffffffffffff && okAll ns0 ns1 ns2 ns3 ns4 (w :: a :: b :: r) && next (Nat.sub extra 2) ns0 ns1 ns2 ns3 ns4 (w :: a :: b :: r) then true
    else false

def disp5 (extra s0 s1 s2 s3 s4 : ℕ)
    (next : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → Bool)
    (a b : ℕ) (r : List ℕ) : Bool :=
  let ns0 := if isC 0x5488ed3b4ed3b4ed3b4ffffffffffffff003ff a || isC 0x5488ed3b4ed3b4ed3b4ffffffffffffff003ff b then Nat.add s0 1 else s0
  if Nat.ble 3 ns0 then false else
  let ns1 := if isC 0x3244dab6adab6adab6afffffffffffc00fffff a || isC 0x3244dab6adab6adab6afffffffffffc00fffff b then Nat.add s1 1 else s1
  if Nat.ble 3 ns1 then false else
  let ns2 := if isC 0xe22b66d9b66d9b66d9fffffffff003fffffff a || isC 0xe22b66d9b66d9b66d9fffffffff003fffffff b then Nat.add s2 1 else s2
  if Nat.ble 3 ns2 then false else
  let ns3 := if isC 0x1e171dc771dc771dc7ffffffc00ffffffffff a || isC 0x1e171dc771dc771dc7ffffffc00ffffffffff b then Nat.add s3 1 else s3
  if Nat.ble 3 ns3 then false else
  let ns4 := if isC 0x1f0fc3f0fc3f0fc3fffff003ffffffffffff a || isC 0x1f0fc3f0fc3f0fc3fffff003ffffffffffff b then Nat.add s4 1 else s4
  if Nat.ble 3 ns4 then false else
    let base := cuts5N r
    let sa := sep5N a
    let sb := sep5N b
    tryW5 extra ns0 ns1 ns2 ns3 ns4 next a b sa sb base r (Nat.land a b) ||
    tryW5 extra ns0 ns1 ns2 ns3 ns4 next a b sa sb base r (Nat.lor a b) ||
    tryW5 extra ns0 ns1 ns2 ns3 ns4 next a b sa sb base r (Nat.land a (Nat.xor b 0xffffffffffffffffffffffffffffffffffffff)) ||
    tryW5 extra ns0 ns1 ns2 ns3 ns4 next a b sa sb base r (Nat.land b (Nat.xor a 0xffffffffffffffffffffffffffffffffffffff))

def pickB5 (extra s0 s1 s2 s3 s4 : ℕ)
    (next : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → Bool)
    (a : ℕ) (pre : List ℕ) : List ℕ → Bool
  | [] => false
  | b :: rest =>
    disp5 extra s0 s1 s2 s3 s4 next a b (pre ++ rest) || pickB5 extra s0 s1 s2 s3 s4 next a (b :: pre) rest

def pickA5 (extra s0 s1 s2 s3 s4 : ℕ)
    (next : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → Bool)
    (pre : List ℕ) : List ℕ → Bool
  | [] => false
  | a :: rest =>
    pickB5 extra s0 s1 s2 s3 s4 next a pre rest || pickA5 extra s0 s1 s2 s3 s4 next (a :: pre) rest

def opt5 : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → Bool
  | 0, _, _, _, _, _, _, ws => match ws with | [w] => Nat.beq w 0xfffffffffffffffffff0000000000000000000 || Nat.beq w 0xfffffffffffffffffff | _ => false
  | k + 1, extra, s0, s1, s2, s3, s4, ws =>
    (match ws with | [w] => Nat.beq w 0xfffffffffffffffffff0000000000000000000 || Nat.beq w 0xfffffffffffffffffff | _ => false) ||
    pickA5 extra s0 s1 s2 s3 s4 (opt5 k) [] ws

lemma pickB5_exists (extra s0 s1 s2 s3 s4 : ℕ)
    (next : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → Bool) (a b : W5) (pre ys : List W5)
    (hb : b ∈ ys) :
    ∃ r : List W5, (pre ++ ys).Perm (b :: r) ∧
      (disp5 extra s0 s1 s2 s3 s4 next a.toNat b.toNat (r.map BitVec.toNat) = true →
        pickB5 extra s0 s1 s2 s3 s4 next a.toNat (pre.map BitVec.toNat) (ys.map BitVec.toNat) = true) := by
  induction ys generalizing pre with
  | nil => simp at hb
  | cons y rest ih =>
    rcases List.mem_cons.mp hb with rfl | hbr
    · refine ⟨pre ++ rest, List.perm_middle, fun hd => ?_⟩
      simp only [List.map_cons, pickB5, List.map_append] at hd ⊢
      rw [hd]; rfl
    · obtain ⟨r, hp, himp⟩ := ih (y :: pre) hbr
      refine ⟨r, List.perm_middle.trans hp, fun hd => ?_⟩
      have h := himp hd
      simp only [List.map_cons] at h
      simp only [List.map_cons, pickB5, h, Bool.or_true]

lemma pickA5_exists (extra s0 s1 s2 s3 s4 : ℕ)
    (next : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → Bool) (a b : W5) (pre ys : List W5)
    (ha : a ∈ ys) (hb : b ∈ ys) (hne : a ≠ b) :
    ∃ r : List W5, (pre ++ ys).Perm (a :: b :: r) ∧
      ((disp5 extra s0 s1 s2 s3 s4 next a.toNat b.toNat (r.map BitVec.toNat) = true →
          pickA5 extra s0 s1 s2 s3 s4 next (pre.map BitVec.toNat) (ys.map BitVec.toNat) = true) ∨
       (disp5 extra s0 s1 s2 s3 s4 next b.toNat a.toNat (r.map BitVec.toNat) = true →
          pickA5 extra s0 s1 s2 s3 s4 next (pre.map BitVec.toNat) (ys.map BitVec.toNat) = true)) := by
  induction ys generalizing pre with
  | nil => simp at ha
  | cons y rest ih =>
    rcases List.mem_cons.mp ha with rfl | har
    · have hbr : b ∈ rest := (List.mem_cons.mp hb).resolve_left (Ne.symm hne)
      obtain ⟨r, hp, himp⟩ := pickB5_exists extra s0 s1 s2 s3 s4 next a b pre rest hbr
      refine ⟨r, List.perm_middle.trans (hp.cons a), .inl fun hd => ?_⟩
      simp only [List.map_cons, pickA5, himp hd, Bool.true_or]
    · rcases List.mem_cons.mp hb with rfl | hbr
      · obtain ⟨r, hp, himp⟩ := pickB5_exists extra s0 s1 s2 s3 s4 next b a pre rest har
        refine ⟨r, List.perm_middle.trans ((hp.cons b).trans (List.Perm.swap a b r)), .inr fun hd => ?_⟩
        simp only [List.map_cons, pickA5, himp hd, Bool.true_or]
      · obtain ⟨r, hp, himp⟩ := ih (y :: pre) har hbr
        refine ⟨r, List.perm_middle.trans hp, himp.imp (fun f hd => ?_) (fun f hd => ?_)⟩
        · have h := f hd; simp only [List.map_cons] at h; simp only [List.map_cons, pickA5, h, Bool.or_true]
        · have h := f hd; simp only [List.map_cons] at h; simp only [List.map_cons, pickA5, h, Bool.or_true]

theorem disp5_complete {k extra : ℕ} {s : Fin 5 → ℕ} {a b z : W5} {r kept : List W5}
    (next : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → Bool)
    (hz : z ∈ basicOps5 a b) (hza : z ≠ a) (hzb : z ≠ b) (hzr : z ∉ r)
    (hk : kept ∈ keepChoices5 a b r) (he : extra + r.length = k) (hn : kept.length ≤ k)
    (ns_lt : ∀ i : Fin 5, s i + (if isC (mask5 i).toNat a.toNat || isC (mask5 i).toNat b.toNat then 1 else 0) < 3)
    (hc : cuts5N ((z :: kept).map BitVec.toNat) = M5)
    (hok : okAll
      (s 0 + if isC (mask5 0).toNat a.toNat || isC (mask5 0).toNat b.toNat then 1 else 0)
      (s 1 + if isC (mask5 1).toNat a.toNat || isC (mask5 1).toNat b.toNat then 1 else 0)
      (s 2 + if isC (mask5 2).toNat a.toNat || isC (mask5 2).toNat b.toNat then 1 else 0)
      (s 3 + if isC (mask5 3).toNat a.toNat || isC (mask5 3).toNat b.toNat then 1 else 0)
      (s 4 + if isC (mask5 4).toNat a.toNat || isC (mask5 4).toNat b.toNat then 1 else 0)
      ((z :: kept).map BitVec.toNat) = true)
    (ht : next (k - kept.length)
      (s 0 + if isC (mask5 0).toNat a.toNat || isC (mask5 0).toNat b.toNat then 1 else 0)
      (s 1 + if isC (mask5 1).toNat a.toNat || isC (mask5 1).toNat b.toNat then 1 else 0)
      (s 2 + if isC (mask5 2).toNat a.toNat || isC (mask5 2).toNat b.toNat then 1 else 0)
      (s 3 + if isC (mask5 3).toNat a.toNat || isC (mask5 3).toNat b.toNat then 1 else 0)
      (s 4 + if isC (mask5 4).toNat a.toNat || isC (mask5 4).toNat b.toNat then 1 else 0)
      ((z :: kept).map BitVec.toNat) = true) :
    disp5 extra (s 0) (s 1) (s 2) (s 3) (s 4) next a.toNat b.toNat (r.map BitVec.toNat) = true := by
  have hm := mask5_toNat_vals
  let ns : Fin 5 → ℕ := fun i => s i + if isC (mask5 i).toNat a.toNat || isC (mask5 i).toNat b.toNat then 1 else 0
  have htry : tryW5 extra (ns 0) (ns 1) (ns 2) (ns 3) (ns 4) next a.toNat b.toNat (sep5N a.toNat) (sep5N b.toNat)
      (cuts5N (r.map BitVec.toNat)) (r.map BitVec.toNat) z.toNat = true := by
    unfold tryW5
    have hna : Nat.beq z.toNat a.toNat = false := nat_beq_false (fun heq => hza (BitVec.eq_of_toNat_eq heq))
    have hnb : Nat.beq z.toNat b.toNat = false := nat_beq_false (fun heq => hzb (BitVec.eq_of_toNat_eq heq))
    have hnr : elemN z.toNat (r.map BitVec.toNat) = false := elemN_map_false hzr
    rw [hna, hnb, hnr]; simp only [Bool.false_or, Bool.false_eq_true, ↓reduceIte]
    have hM5v : (0xfffffffffffffffffff : ℕ) = M5 := rfl
    simp only [hM5v]
    simp only [keepChoices5, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with hkeq | hkeq | hkeq | hkeq
    · rw [hkeq] at hc hok ht hn
      simp only [List.map_cons, cuts5N] at hc
      have h1 : Nat.beq (Nat.lor (sep5N z.toNat) (cuts5N (r.map BitVec.toNat))) M5 = true :=
        Nat.beq_eq.mpr hc
      have hok' : okAll (ns 0) (ns 1) (ns 2) (ns 3) (ns 4) (z.toNat :: r.map BitVec.toNat) = true := by
        simpa only [List.map_cons] using hok
      have h2 : next extra (ns 0) (ns 1) (ns 2) (ns 3) (ns 4) (z.toNat :: r.map BitVec.toNat) = true := by
        simpa only [List.map_cons] using (show next extra (ns 0) (ns 1) (ns 2) (ns 3) (ns 4) ((z :: r).map BitVec.toNat) = true by convert ht using 2; omega)
      rw [h1, hok', h2]; rfl
    · rw [hkeq] at hc hok ht hn
      simp only [List.map_cons, cuts5N] at hc
      simp only [List.length_cons] at hn ht
      have hnz : Nat.beq extra 0 = false := nat_beq_false (by omega)
      have h1 : Nat.beq (Nat.lor (Nat.lor (sep5N z.toNat) (cuts5N (r.map BitVec.toNat))) (sep5N a.toNat)) M5 = true := by
        have hcomm : Nat.lor (Nat.lor (sep5N z.toNat) (cuts5N (r.map BitVec.toNat))) (sep5N a.toNat) =
            Nat.lor (sep5N z.toNat) (Nat.lor (sep5N a.toNat) (cuts5N (r.map BitVec.toNat))) := by
          apply Nat.eq_of_testBit_eq; intro t; simp only [nat_lor, Nat.testBit_lor]; grind
        rw [hcomm]; exact Nat.beq_eq.mpr hc
      have hok' : okAll (ns 0) (ns 1) (ns 2) (ns 3) (ns 4) (z.toNat :: a.toNat :: r.map BitVec.toNat) = true := by
        simpa only [List.map_cons] using hok
      have h2 : next (Nat.sub extra 1) (ns 0) (ns 1) (ns 2) (ns 3) (ns 4) (z.toNat :: a.toNat :: r.map BitVec.toNat) = true := by
        rw [nat_sub]; simpa only [List.map_cons] using (show next (extra - 1) (ns 0) (ns 1) (ns 2) (ns 3) (ns 4) ((z :: a :: r).map BitVec.toNat) = true by convert ht using 2; omega)
      rw [hnz, h1, hok', h2]
      split_ifs <;> simp_all
    · rw [hkeq] at hc hok ht hn
      simp only [List.map_cons, cuts5N] at hc
      simp only [List.length_cons] at hn ht
      have hnz : Nat.beq extra 0 = false := nat_beq_false (by omega)
      have h1 : Nat.beq (Nat.lor (Nat.lor (sep5N z.toNat) (cuts5N (r.map BitVec.toNat))) (sep5N b.toNat)) M5 = true := by
        have hcomm : Nat.lor (Nat.lor (sep5N z.toNat) (cuts5N (r.map BitVec.toNat))) (sep5N b.toNat) =
            Nat.lor (sep5N z.toNat) (Nat.lor (sep5N b.toNat) (cuts5N (r.map BitVec.toNat))) := by
          apply Nat.eq_of_testBit_eq; intro t; simp only [nat_lor, Nat.testBit_lor]; grind
        rw [hcomm]; exact Nat.beq_eq.mpr hc
      have hok' : okAll (ns 0) (ns 1) (ns 2) (ns 3) (ns 4) (z.toNat :: b.toNat :: r.map BitVec.toNat) = true := by
        simpa only [List.map_cons] using hok
      have h2 : next (Nat.sub extra 1) (ns 0) (ns 1) (ns 2) (ns 3) (ns 4) (z.toNat :: b.toNat :: r.map BitVec.toNat) = true := by
        rw [nat_sub]; simpa only [List.map_cons] using (show next (extra - 1) (ns 0) (ns 1) (ns 2) (ns 3) (ns 4) ((z :: b :: r).map BitVec.toNat) = true by convert ht using 2; omega)
      rw [hnz, h1, hok', h2]
      split_ifs <;> simp_all
    · rw [hkeq] at hc hok ht hn
      simp only [List.map_cons, cuts5N] at hc
      simp only [List.length_cons] at hn ht
      have hnz : Nat.beq extra 0 = false := nat_beq_false (by omega)
      have hge2 : Nat.ble 2 extra = true := Nat.ble_eq.mpr (by omega)
      have h1 : Nat.beq (Nat.lor (Nat.lor (Nat.lor (sep5N z.toNat) (cuts5N (r.map BitVec.toNat))) (sep5N a.toNat)) (sep5N b.toNat)) M5 = true := by
        have hcomm : Nat.lor (Nat.lor (Nat.lor (sep5N z.toNat) (cuts5N (r.map BitVec.toNat))) (sep5N a.toNat)) (sep5N b.toNat) =
            Nat.lor (sep5N z.toNat) (Nat.lor (sep5N a.toNat) (Nat.lor (sep5N b.toNat) (cuts5N (r.map BitVec.toNat)))) := by
          apply Nat.eq_of_testBit_eq; intro t; simp only [nat_lor, Nat.testBit_lor]; grind
        rw [hcomm]; exact Nat.beq_eq.mpr hc
      have hok' : okAll (ns 0) (ns 1) (ns 2) (ns 3) (ns 4) (z.toNat :: a.toNat :: b.toNat :: r.map BitVec.toNat) = true := by
        simpa only [List.map_cons] using hok
      have h2 : next (Nat.sub extra 2) (ns 0) (ns 1) (ns 2) (ns 3) (ns 4) (z.toNat :: a.toNat :: b.toNat :: r.map BitVec.toNat) = true := by
        rw [nat_sub]; simpa only [List.map_cons] using (show next (extra - 2) (ns 0) (ns 1) (ns 2) (ns 3) (ns 4) ((z :: a :: b :: r).map BitVec.toNat) = true by convert ht using 2; omega)
      rw [hnz, hge2, h1, hok', h2]
      split_ifs <;> simp_all
  unfold disp5
  rw [← hm.1, ← hm.2.1, ← hm.2.2.1, ← hm.2.2.2.1, ← hm.2.2.2.2]
  have hns_eq : ∀ i : Fin 5, (if isC (mask5 i).toNat a.toNat || isC (mask5 i).toNat b.toNat then Nat.add (s i) 1 else s i) = ns i := by
    intro i; dsimp only [ns]; cases isC (mask5 i).toNat a.toNat || isC (mask5 i).toNat b.toNat <;> simp
  have hble_f : ∀ i : Fin 5, Nat.ble 3 (ns i) = false := by
    intro i
    have hlt := ns_lt i
    change ns i < 3 at hlt
    cases hb : Nat.ble 3 (ns i)
    · rfl
    · exfalso; have := Nat.ble_eq.mp hb; omega
  simp only [hns_eq 0, hns_eq 1, hns_eq 2, hns_eq 3, hns_eq 4,
    hble_f 0, hble_f 1, hble_f 2, hble_f 3, hble_f 4, Bool.false_eq_true, ↓reduceIte]
  simp only [basicOps5, ops5, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  have hnot_b : (~~~b).toNat = Nat.xor b.toNat 0xffffffffffffffffffffffffffffffffffffff := by
    rw [show (0xffffffffffffffffffffffffffffffffffffff : ℕ) = 2 ^ 152 - 1 from hA5_pow]; exact bv_toNat_not b
  have hnot_a : (~~~a).toNat = Nat.xor a.toNat 0xffffffffffffffffffffffffffffffffffffff := by
    rw [show (0xffffffffffffffffffffffffffffffffffffff : ℕ) = 2 ^ 152 - 1 from hA5_pow]; exact bv_toNat_not a
  rcases hz with rfl | rfl | rfl | rfl
  · rw [BitVec.toNat_and, ← nat_land] at htry; simp only [htry, Bool.true_or]
  · rw [BitVec.toNat_or, ← nat_lor] at htry; simp only [htry, Bool.or_true, Bool.true_or]
  · rw [BitVec.toNat_and, ← nat_land, hnot_b] at htry; simp only [htry, Bool.or_true, Bool.true_or]
  · rw [BitVec.toNat_and, ← nat_land, hnot_a] at htry; simp only [htry, Bool.or_true]

theorem opt5_complete {g : W5} (hg : g = goal5 ∨ g = ~~~goal5) (n : ℕ) (ws : List W5) (extra : ℕ)
    (s : Fin 5 → ℕ) (hn : ws.Nodup) (room : extra + ws.length = n + 1)
    (h : live basicOps5 g n ws.toFinset) (hav : HasAvoid n s ws.toFinset) :
    opt5 n extra (s 0) (s 1) (s 2) (s 3) (s 4) (ws.map BitVec.toNat) = true := by
  have hdone : ∀ (u : List W5), u.Nodup → u.toFinset = {g} →
      (match u.map BitVec.toNat with | [w] => Nat.beq w 0xfffffffffffffffffff0000000000000000000 || Nat.beq w 0xfffffffffffffffffff | _ => false) = true := by
    intro u hun hu
    rw [singleton_list5 hun hu]
    rcases hg with rfl | rfl <;> decide
  induction n generalizing ws extra s with
  | zero => exact hdone ws hn h
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · simp only [opt5, hdone ws hn done, Bool.true_or]
    · obtain ⟨r, hp, hpick⟩ := pickA5_exists extra (s 0) (s 1) (s 2) (s 3) (s 4) (opt5 k) a b [] ws
        (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      simp only [List.nil_append] at hp
      have go {u v : W5} (perm : ws.Perm (u :: v :: r))
          (hset : ws.toFinset = insert u (insert v needed)) (hop : z ∈ basicOps5 u v) :
          disp5 extra (s 0) (s 1) (s 2) (s 3) (s 4) (opt5 k) u.toNat v.toNat (r.map BitVec.toNat) = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept5 perm hn hset
        have hzu : z ≠ u := fun he => hout (hset ▸ he ▸ Finset.mem_insert_self _ _)
        have hzv : z ≠ v := fun he => hout (hset ▸ he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
        have hzr : z ∉ r := fun hr => hout (List.mem_toFinset.mpr (perm.mem_iff.mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))))
        have hznew : z ∉ kept := fun hu => hout (hset ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps5 g k (z :: kept).toFinset := by simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        have hsub : (z :: kept).toFinset ⊆ insert z ws.toFinset := by
          intro t ht
          rcases Finset.mem_insert.mp (by simpa [hfin] using ht) with rfl | htn
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (hset ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem htn))
        have hu_mem : u ∈ ws.toFinset := hset ▸ Finset.mem_insert_self _ _
        have hv_mem : v ∈ ws.toFinset := hset ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
        have hav' := hasAvoid_step hav hu_mem hv_mem hop hsub
        have hlt3 := hasAvoid_s_lt3 hg hl hav'
        have hok := hasAvoid_okAll hg hnd hl hav'
        apply disp5_complete (k := k) (extra := extra) (s := s) (opt5 k) hop hzu hzv hzr hk
          (by omega) (by omega) hlt3 (cuts5_full hg hl) hok
        apply ih _ _ _ hnd _ hl hav'
        simp; omega
      simp only [opt5, Bool.or_eq_true]
      right
      rcases hpick with h1 | h2
      · exact h1 (go hp hs hz)
      · exact h2 (go (hp.trans (List.Perm.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops5_swap a b ▸ hz))

lemma disp5_of_step {g : W5} (hg : g = goal5 ∨ g = ~~~goal5) {k extra : ℕ} {s : Fin 5 → ℕ}
    {ws r : List W5} {a b z : W5} {rest : Finset W5}
    (hn : ws.Nodup) (room : extra + ws.length = k + 2)
    (perm : ws.Perm (a :: b :: r)) (hs : ws.toFinset = insert a (insert b rest))
    (hz : z ∈ basicOps5 a b) (hzout : z ∉ ws.toFinset)
    (tail : live basicOps5 g k (insert z rest)) (hav : HasAvoid (k + 1) s ws.toFinset) :
    disp5 extra (s 0) (s 1) (s 2) (s 3) (s 4) (opt5 k) a.toNat b.toNat (r.map BitVec.toNat) = true := by
  obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept5 perm hn hs
  have hza : z ≠ a := fun he => hzout (hs ▸ he ▸ Finset.mem_insert_self _ _)
  have hzb : z ≠ b := fun he => hzout (hs ▸ he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hzr : z ∉ r := fun hr => hzout (List.mem_toFinset.mpr (perm.mem_iff.mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))))
  have hznew : z ∉ kept := fun hu => hzout (hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu)))
  have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
  have hl : live basicOps5 g k (z :: kept).toFinset := by simpa [hfin] using tail
  have hc := live_card hl
  rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
  have len := perm.length_eq
  simp only [List.length_cons] at len
  have hsub : (z :: kept).toFinset ⊆ insert z ws.toFinset := by
    intro t ht
    rcases Finset.mem_insert.mp (by simpa [hfin] using ht) with rfl | htn
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem htn))
  have ha_mem : a ∈ ws.toFinset := hs ▸ Finset.mem_insert_self _ _
  have hb_mem : b ∈ ws.toFinset := hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hav' := hasAvoid_step hav ha_mem hb_mem hz hsub
  have hlt3 := hasAvoid_s_lt3 hg hl hav'
  have hok := hasAvoid_okAll hg hnd hl hav'
  apply disp5_complete (k := k) (extra := extra) (s := s) (opt5 k) hz hza hzb hzr hk
    (by omega) (by omega) hlt3 (cuts5_full hg hl) hok
  apply opt5_complete hg k (z :: kept) (k - kept.length) _ hnd (by simp; omega) hl hav'

def row5Tbl : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 5, 6, 9, 10, 12, 17, 18, 20, 24, 3, 5, 6, 9, 10, 12, 17, 18, 20, 24, 3, 5, 6, 9, 10, 12, 17, 18, 20, 24, 3, 5, 6, 9, 10, 12, 17, 18, 20, 24, 3, 5, 6, 9, 10, 12, 17, 18, 20, 24, 3, 5, 6, 9, 10, 12, 17, 18, 20, 24, 7, 11, 13, 14, 15, 19, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31]
def rowPosTbl : List ℕ := [0, 10, 20, 76, 30, 77, 78, 136, 40, 79, 80, 137, 81, 138, 139, 140, 50, 82, 83, 141, 84, 142, 143, 144, 85, 145, 146, 147, 148, 149, 150, 151]

def row5 (k : Fin 152) : Fin 32 :=
  ⟨row5Tbl.getD k.val 0 % 32, Nat.mod_lt _ (by decide)⟩

def rowPos (r : Fin 32) : Fin 152 :=
  ⟨rowPosTbl.getD r.val 0 % 152, Nat.mod_lt _ (by decide)⟩

def swap (a b x : Fin 5) : Fin 5 :=
  if x = a then b else if x = b then a else x

def permRow (σ : Fin 5 → Fin 5) (r : Fin 32) : Fin 32 :=
  let b (i : Fin 5) (p : ℕ) : ℕ := if Nat.testBit r.val (σ i).val then p else 0
  ⟨(b 0 1 + b 1 2 + b 2 4 + b 3 8 + b 4 16) % 32, Nat.mod_lt _ (by decide)⟩

def permIx (σ : Fin 5 → Fin 5) (k : Fin 152) : Fin 152 :=
  rowPos (permRow σ (row5 k))

def perm5 (σ : Fin 5 → Fin 5) (w : W5) : W5 :=
  (BitVec.ofBoolListLE (List.ofFn (fun k : Fin 152 => w[(permIx σ k).val]))).cast List.length_ofFn

theorem perm5_bit (σ : Fin 5 → Fin 5) (w : W5) (k : ℕ) (hk : k < 152) :
    (perm5 σ w)[k] = w[(permIx σ ⟨k, hk⟩).val] := by
  rw [← BitVec.getLsbD_eq_getElem hk]
  simp only [perm5, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, hk, dite_true, Option.getD_some]

theorem perm5_not (σ : Fin 5 → Fin 5) (u : W5) : perm5 σ (~~~u) = ~~~perm5 σ u :=
  BitVec.eq_of_getElem_eq fun k hk => by simp only [perm5_bit, BitVec.getElem_not]

theorem perm5_and (σ : Fin 5 → Fin 5) (u v : W5) : perm5 σ (u &&& v) = perm5 σ u &&& perm5 σ v :=
  BitVec.eq_of_getElem_eq fun k hk => by simp only [perm5_bit, BitVec.getElem_and]

theorem perm5_or (σ : Fin 5 → Fin 5) (u v : W5) : perm5 σ (u ||| v) = perm5 σ u ||| perm5 σ v :=
  BitVec.eq_of_getElem_eq fun k hk => by simp only [perm5_bit, BitVec.getElem_or]

theorem perm5_ops (σ : Fin 5 → Fin 5) (a b z : W5) (hz : z ∈ basicOps5 a b) :
    perm5 σ z ∈ basicOps5 (perm5 σ a) (perm5 σ b) := by
  simp only [basicOps5, ops5, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
  rcases hz with rfl | rfl | rfl | rfl <;> simp [perm5_and, perm5_or, perm5_not]

def Valid5 (w : W5) : Prop :=
  ∀ k : Fin 152, w[k.val] = w[(rowPos (row5 k)).val]

def valid5B (w : W5) : Bool := (List.finRange 152).all fun k => w[k.val] == w[(rowPos (row5 k)).val]

lemma valid5_of_valid5B {w : W5} (h : valid5B w = true) : Valid5 w := by
  intro k
  have hk := List.all_eq_true.mp h k (List.mem_finRange k)
  simpa using hk

lemma valid5_ops {a b z : W5} (ha : Valid5 a) (hb : Valid5 b) (hz : z ∈ basicOps5 a b) : Valid5 z := by
  simp only [basicOps5, ops5, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  intro k
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not, ha k, hb k]

set_option maxRecDepth 8000 in
lemma row5_rowPos : ∀ r : Fin 32, row5 (rowPos r) = r := by decide +kernel

lemma perm5_valid (a b : Fin 5) (w : W5) : Valid5 (perm5 (swap a b) w) := by
  intro k
  rw [perm5_bit, perm5_bit]
  have h1 : permIx (swap a b) ⟨k.val, k.isLt⟩ = permIx (swap a b) ⟨(rowPos (row5 k)).val, (rowPos (row5 k)).isLt⟩ := by
    simp only [permIx, Fin.eta, row5_rowPos]
  exact congrArg (fun j : Fin 152 => w[j.val]) h1

set_option maxRecDepth 8000 in
lemma permRow_swap_invol : ∀ (a b : Fin 5) (r : Fin 32),
    permRow (swap a b) (permRow (swap a b) r) = r := by decide +kernel

lemma perm5_swap_row (a b : Fin 5) (k : Fin 152) :
    row5 (permIx (swap a b) (permIx (swap a b) k)) = row5 k := by
  simp only [permIx, row5_rowPos, permRow_swap_invol]

lemma perm5_swap_invol (a b : Fin 5) {w : W5} (hw : Valid5 w) :
    perm5 (swap a b) (perm5 (swap a b) w) = w := by
  apply BitVec.eq_of_getElem_eq
  intro k hk
  rw [perm5_bit, perm5_bit, hw (permIx (swap a b) (permIx (swap a b) ⟨k, hk⟩))]
  exact (congrArg (fun r : Fin 32 => w[(rowPos r).val]) (perm5_swap_row a b ⟨k, hk⟩)).trans (hw ⟨k, hk⟩).symm

lemma perm5_swap_inj (a b : Fin 5) {u v : W5} (hu : Valid5 u) (hv : Valid5 v)
    (heq : perm5 (swap a b) u = perm5 (swap a b) v) : u = v := by
  rw [← perm5_swap_invol a b hu, ← perm5_swap_invol a b hv, heq]

lemma valid5_goal : Valid5 goal5 := valid5_of_valid5B (by decide +kernel)

set_option maxRecDepth 8000 in
lemma goal5_permRow : ∀ (a b : Fin 5) (r : Fin 32),
    goal5[(rowPos (permRow (swap a b) r)).val] = goal5[(rowPos r).val] := by decide +kernel

lemma perm5_swap_goal (a b : Fin 5) : perm5 (swap a b) goal5 = goal5 := by
  apply BitVec.eq_of_getElem_eq
  intro k hk
  rw [perm5_bit]
  exact (goal5_permRow a b (row5 ⟨k, hk⟩)).trans (valid5_goal ⟨k, hk⟩).symm

set_option maxRecDepth 8000 in
lemma vinput5_bit : ∀ (i : Fin 5) (k : Fin 152),
    (vinput5 i)[k.val] = Nat.testBit (row5 k).val i.val := by decide +kernel

set_option maxRecDepth 8000 in
lemma permRow_bit : ∀ (a b i : Fin 5) (r : Fin 32),
    Nat.testBit (permRow (swap a b) r).val i.val = Nat.testBit r.val (swap a b i).val := by decide +kernel

lemma perm5_swap_in (a b i : Fin 5) : perm5 (swap a b) (vinput5 i) = vinput5 (swap a b i) := by
  apply BitVec.eq_of_getElem_eq
  intro k hk
  rw [perm5_bit, vinput5_bit i (permIx (swap a b) ⟨k, hk⟩), permIx, row5_rowPos,
    permRow_bit, ← vinput5_bit (swap a b i) ⟨k, hk⟩]

lemma p_01_x0 : perm5 (swap 0 1) x0 = x1 := perm5_swap_in 0 1 0
lemma p_01_x1 : perm5 (swap 0 1) x1 = x0 := perm5_swap_in 0 1 1
lemma p_01_x2 : perm5 (swap 0 1) x2 = x2 := perm5_swap_in 0 1 2
lemma p_01_x3 : perm5 (swap 0 1) x3 = x3 := perm5_swap_in 0 1 3
lemma p_01_x4 : perm5 (swap 0 1) x4 = x4 := perm5_swap_in 0 1 4
lemma p_12_x0 : perm5 (swap 1 2) x0 = x0 := perm5_swap_in 1 2 0
lemma p_12_x1 : perm5 (swap 1 2) x1 = x2 := perm5_swap_in 1 2 1
lemma p_12_x2 : perm5 (swap 1 2) x2 = x1 := perm5_swap_in 1 2 2
lemma p_12_x3 : perm5 (swap 1 2) x3 = x3 := perm5_swap_in 1 2 3
lemma p_12_x4 : perm5 (swap 1 2) x4 = x4 := perm5_swap_in 1 2 4
lemma p_23_x0 : perm5 (swap 2 3) x0 = x0 := perm5_swap_in 2 3 0
lemma p_23_x1 : perm5 (swap 2 3) x1 = x1 := perm5_swap_in 2 3 1
lemma p_23_x2 : perm5 (swap 2 3) x2 = x3 := perm5_swap_in 2 3 2
lemma p_23_x3 : perm5 (swap 2 3) x3 = x2 := perm5_swap_in 2 3 3
lemma p_23_x4 : perm5 (swap 2 3) x4 = x4 := perm5_swap_in 2 3 4
lemma p_24_x0 : perm5 (swap 2 4) x0 = x0 := perm5_swap_in 2 4 0
lemma p_24_x1 : perm5 (swap 2 4) x1 = x1 := perm5_swap_in 2 4 1
lemma p_24_x2 : perm5 (swap 2 4) x2 = x4 := perm5_swap_in 2 4 2
lemma p_24_x3 : perm5 (swap 2 4) x3 = x3 := perm5_swap_in 2 4 3
lemma p_24_x4 : perm5 (swap 2 4) x4 = x2 := perm5_swap_in 2 4 4
lemma p_34_x0 : perm5 (swap 3 4) x0 = x0 := perm5_swap_in 3 4 0
lemma p_34_x1 : perm5 (swap 3 4) x1 = x1 := perm5_swap_in 3 4 1
lemma p_34_x2 : perm5 (swap 3 4) x2 = x2 := perm5_swap_in 3 4 2
lemma p_34_x3 : perm5 (swap 3 4) x3 = x4 := perm5_swap_in 3 4 3
lemma p_34_x4 : perm5 (swap 3 4) x4 = x3 := perm5_swap_in 3 4 4
lemma p_02_x0 : perm5 (swap 0 2) x0 = x2 := perm5_swap_in 0 2 0
lemma p_02_x1 : perm5 (swap 0 2) x1 = x1 := perm5_swap_in 0 2 1
lemma p_02_x2 : perm5 (swap 0 2) x2 = x0 := perm5_swap_in 0 2 2
lemma p_02_x3 : perm5 (swap 0 2) x3 = x3 := perm5_swap_in 0 2 3
lemma p_02_x4 : perm5 (swap 0 2) x4 = x4 := perm5_swap_in 0 2 4
lemma p_13_x0 : perm5 (swap 1 3) x0 = x0 := perm5_swap_in 1 3 0
lemma p_13_x1 : perm5 (swap 1 3) x1 = x3 := perm5_swap_in 1 3 1
lemma p_13_x2 : perm5 (swap 1 3) x2 = x2 := perm5_swap_in 1 3 2
lemma p_13_x3 : perm5 (swap 1 3) x3 = x1 := perm5_swap_in 1 3 3
lemma p_13_x4 : perm5 (swap 1 3) x4 = x4 := perm5_swap_in 1 3 4
lemma p_01_x01 : perm5 (swap 0 1) x01 = x01 := by rw [x01, perm5_or, p_01_x0, p_01_x1, BitVec.or_comm]
lemma p_12_x01 : perm5 (swap 1 2) x01 = x02 := by rw [x01, perm5_or, p_12_x0, p_12_x1]; rfl
lemma p_12_x02 : perm5 (swap 1 2) x02 = x01 := by rw [x02, perm5_or, p_12_x0, p_12_x2]; rfl
lemma p_23_x01 : perm5 (swap 2 3) x01 = x01 := by rw [x01, perm5_or, p_23_x0, p_23_x1]
lemma p_24_x01 : perm5 (swap 2 4) x01 = x01 := by rw [x01, perm5_or, p_24_x0, p_24_x1]
lemma p_34_x01 : perm5 (swap 3 4) x01 = x01 := by rw [x01, perm5_or, p_34_x0, p_34_x1]
lemma p_34_x02 : perm5 (swap 3 4) x02 = x02 := by rw [x02, perm5_or, p_34_x0, p_34_x2]
lemma p_01_x23 : perm5 (swap 0 1) x23 = x23 := by rw [x23, perm5_or, p_01_x2, p_01_x3]
lemma p_23_x23 : perm5 (swap 2 3) x23 = x23 := by rw [x23, perm5_or, p_23_x2, p_23_x3, BitVec.or_comm]
lemma p_01_w03_or : perm5 (swap 0 1) w03_or = w03_or := by rw [w03_or, perm5_or, p_01_x01, p_01_x2]
lemma p_34_w03_or : perm5 (swap 3 4) w03_or = w03_or := by rw [w03_or, perm5_or, p_34_x01, p_34_x2]
lemma p_01_w03_an : perm5 (swap 0 1) w03_an = w03_an := by rw [w03_an, perm5_and, perm5_not, p_01_x01, p_01_x2]
lemma p_34_w03_an : perm5 (swap 3 4) w03_an = w03_an := by rw [w03_an, perm5_and, perm5_not, p_34_x01, p_34_x2]
lemma p_0213_x01 : perm5 (swap 1 3) (perm5 (swap 0 2) x01) = x23 := by rw [x01, perm5_or, p_02_x0, p_02_x1, perm5_or, p_13_x2, p_13_x1]; rfl
lemma p_0213_x23 : perm5 (swap 1 3) (perm5 (swap 0 2) x23) = x01 := by rw [x23, perm5_or, p_02_x2, p_02_x3, perm5_or, p_13_x0, p_13_x3]; rfl
lemma p_0213_x0 : perm5 (swap 1 3) (perm5 (swap 0 2) x0) = x2 := by rw [p_02_x0, p_13_x2]
lemma p_0213_x1 : perm5 (swap 1 3) (perm5 (swap 0 2) x1) = x3 := by rw [p_02_x1, p_13_x1]
lemma p_0213_x2 : perm5 (swap 1 3) (perm5 (swap 0 2) x2) = x0 := by rw [p_02_x2, p_13_x0]
lemma p_0213_x3 : perm5 (swap 1 3) (perm5 (swap 0 2) x3) = x1 := by rw [p_02_x3, p_13_x3]
lemma p_0213_x4 : perm5 (swap 1 3) (perm5 (swap 0 2) x4) = x4 := by rw [p_02_x4, p_13_x4]

lemma perm5_swap_g (a b : Fin 5) {g : W5} (hg : g = goal5 ∨ g = ~~~goal5) :
    perm5 (swap a b) g = g := by
  rcases hg with rfl | rfl
  · exact perm5_swap_goal a b
  · rw [perm5_not, perm5_swap_goal]

theorem live_swap5 (a b : Fin 5) {g : W5} (hg : g = goal5 ∨ g = ~~~goal5) {k : ℕ} {s : Finset W5}
    (hval : ∀ w ∈ s, Valid5 w) (h : live basicOps5 g k s) :
    live basicOps5 g k (s.image (perm5 (swap a b))) := by
  induction k generalizing s with
  | zero =>
    change s = {g} at h
    rw [h, Finset.image_singleton, perm5_swap_g a b hg]
    rfl
  | succ k ih =>
    rcases h with skip | ⟨u, hu, v, hv, huv, z, hz, hout, r, hs, tail⟩
    · exact .inl (ih hval skip)
    · have hvu : Valid5 u := hval u hu
      have hvv : Valid5 v := hval v hv
      have hvz : Valid5 z := valid5_ops hvu hvv hz
      have hne : perm5 (swap a b) u ≠ perm5 (swap a b) v :=
        fun he => huv (perm5_swap_inj a b hvu hvv he)
      have hout' : perm5 (swap a b) z ∉ s.image (perm5 (swap a b)) := by
        intro hm
        obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp hm
        exact hout (perm5_swap_inj a b (hval w hw) hvz heq ▸ hw)
      have hval' : ∀ w ∈ insert z r, Valid5 w := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hwr
        · exact hvz
        · exact hval w (hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hwr))
      refine .inr ⟨perm5 (swap a b) u, Finset.mem_image_of_mem _ hu,
        perm5 (swap a b) v, Finset.mem_image_of_mem _ hv, hne,
        perm5 (swap a b) z, perm5_ops _ _ _ _ hz, hout', r.image (perm5 (swap a b)), ?_, ?_⟩
      · rw [hs, Finset.image_insert, Finset.image_insert]
      · simpa only [Finset.image_insert] using ih hval' tail

lemma step_swap5 (a b : Fin 5) {g : W5} (hg : g = goal5 ∨ g = ~~~goal5) {k : ℕ}
    {s rest : Finset W5} {u v z : W5}
    (hval : ∀ w ∈ s, Valid5 w) (hz : z ∈ basicOps5 u v) (hzout : z ∉ s)
    (hs : s = insert u (insert v rest)) (tail : live basicOps5 g k (insert z rest)) :
    ∃ (z' : W5) (rest' : Finset W5),
      z' ∈ basicOps5 (perm5 (swap a b) u) (perm5 (swap a b) v) ∧
      z' ∉ s.image (perm5 (swap a b)) ∧
      s.image (perm5 (swap a b)) = insert (perm5 (swap a b) u) (insert (perm5 (swap a b) v) rest') ∧
      live basicOps5 g k (insert z' rest') := by
  have hvu : Valid5 u := hval u (hs ▸ Finset.mem_insert_self _ _)
  have hvv : Valid5 v := hval v (hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hvz : Valid5 z := valid5_ops hvu hvv hz
  have hout' : perm5 (swap a b) z ∉ s.image (perm5 (swap a b)) := by
    intro hm
    obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp hm
    exact hzout (perm5_swap_inj a b (hval w hw) hvz heq ▸ hw)
  have hval' : ∀ w ∈ insert z rest, Valid5 w := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hwr
    · exact hvz
    · exact hval w (hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hwr))
  refine ⟨perm5 (swap a b) z, rest.image (perm5 (swap a b)), perm5_ops _ _ _ _ hz, hout', ?_, ?_⟩
  · rw [hs, Finset.image_insert, Finset.image_insert]
  · simpa only [Finset.image_insert] using live_swap5 a b hg hval' tail

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem chk_c03_or_b : (disp5 2 1 1 1 0 0 (opt5 6) 0xffff7fdff7fdff7fdff000000000fffffffc00 0xf1dd499264992649926000000000ffc0000000 [0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 2 1 1 1 0 0 (opt5 6) 0xffff7fdff7fdff7fdff000000000fffffffc00 0xab7712c4b12c4b12c4b00000000000000ffc00 [0xf1dd499264992649926000000000ffc0000000, 0xcdbb254952549525495000000000003ff00000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 2 1 1 1 0 0 (opt5 6) 0xffff7fdff7fdff7fdff000000000fffffffc00 0xfe1e8e2388e2388e2380000003ff0000000000 [0xf1dd499264992649926000000000ffc0000000, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 2 1 1 1 0 0 (opt5 6) 0xf1dd499264992649926000000000ffc0000000 0xab7712c4b12c4b12c4b00000000000000ffc00 [0xffff7fdff7fdff7fdff000000000fffffffc00, 0xcdbb254952549525495000000000003ff00000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 2 1 1 1 0 0 (opt5 6) 0xf1dd499264992649926000000000ffc0000000 0xfe1e8e2388e2388e2380000003ff0000000000 [0xffff7fdff7fdff7fdff000000000fffffffc00, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 2 1 1 1 0 0 (opt5 6) 0xab7712c4b12c4b12c4b00000000000000ffc00 0xcdbb254952549525495000000000003ff00000 [0xffff7fdff7fdff7fdff000000000fffffffc00, 0xf1dd499264992649926000000000ffc0000000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 2 1 1 1 0 0 (opt5 6) 0xab7712c4b12c4b12c4b00000000000000ffc00 0xfe1e8e2388e2388e2380000003ff0000000000 [0xffff7fdff7fdff7fdff000000000fffffffc00, 0xf1dd499264992649926000000000ffc0000000, 0xcdbb254952549525495000000000003ff00000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 2 1 1 1 0 0 (opt5 6) 0xfe1e8e2388e2388e2380000003ff0000000000 0xffe0f03c0f03c0f03c00000ffc000000000000 [0xffff7fdff7fdff7fdff000000000fffffffc00, 0xf1dd499264992649926000000000ffc0000000, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000]) = false := by decide +kernel

lemma ws_c03_or_b_nd : ([w03_or, x2, x0, x1, x3, x4] : List W5).Nodup := by decide +kernel
lemma ws_c03_or_b_valid : ∀ w ∈ ([w03_or, x2, x0, x1, x3, x4] : List W5), Valid5 w := fun w hw => valid5_of_valid5B ((List.all_eq_true.mp (by decide +kernel : ([w03_or, x2, x0, x1, x3, x4] : List W5).all valid5B = true)) w hw)
lemma ws_c03_or_b_not_goal : ∀ g : W5, (g = goal5 ∨ g = ~~~goal5) → ([w03_or, x2, x0, x1, x3, x4] : List W5).toFinset ≠ {g} := by
  intro g _ heq; have hc := congrArg Finset.card heq; rw [List.toFinset_card_of_nodup ws_c03_or_b_nd, Finset.card_singleton] at hc; simp at hc
lemma ws_c03_or_b_inv_01 : ([w03_or, x2, x0, x1, x3, x4] : List W5).toFinset.image (perm5 (swap 0 1)) = ([w03_or, x2, x0, x1, x3, x4] : List W5).toFinset := by
  ext w; simp only [List.toFinset_cons, List.toFinset_nil, Finset.image_insert, Finset.image_empty, Finset.mem_insert, Finset.notMem_empty, or_false, p_01_w03_or, p_01_x2, p_01_x0, p_01_x1, p_01_x3, p_01_x4]; tauto
lemma ws_c03_or_b_inv_34 : ([w03_or, x2, x0, x1, x3, x4] : List W5).toFinset.image (perm5 (swap 3 4)) = ([w03_or, x2, x0, x1, x3, x4] : List W5).toFinset := by
  ext w; simp only [List.toFinset_cons, List.toFinset_nil, Finset.image_insert, Finset.image_empty, Finset.mem_insert, Finset.notMem_empty, or_false, p_34_w03_or, p_34_x2, p_34_x0, p_34_x1, p_34_x3, p_34_x4]; tauto
lemma no_c03_or_b {g : W5} (hg : g = goal5 ∨ g = ~~~goal5)
    (hl : live basicOps5 g 7 ([w03_or, x2, x0, x1, x3, x4] : List W5).toFinset)
    (hav : HasAvoid 7 ![1, 1, 1, 0, 0] ([w03_or, x2, x0, x1, x3, x4] : List W5).toFinset) : False := by
  have hstep : ∀ a b : W5, (a, b) ∈ [(w03_or, x2), (w03_or, x0), (w03_or, x3), (x2, x0), (x2, x3), (x0, x1), (x0, x3), (x3, x4)] →
      ∀ z ∈ basicOps5 a b, z ∉ ([w03_or, x2, x0, x1, x3, x4] : List W5).toFinset → ∀ rest : Finset W5,
      ([w03_or, x2, x0, x1, x3, x4] : List W5).toFinset = insert a (insert b rest) →
      live basicOps5 g 6 (insert z rest) → False := by
    intro a b hab z hz hzout rest hs tail
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hab
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hperm : ([w03_or, x2, x0, x1, x3, x4] : List W5).Perm (w03_or :: x2 :: [x0, x1, x3, x4]) := List.Perm.refl _
      have hdisp := disp5_of_step (extra := 2) hg ws_c03_or_b_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_or_b
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.1.1.1.1.symm.trans hdisp)
    · have hperm : ([w03_or, x2, x0, x1, x3, x4] : List W5).Perm (w03_or :: x0 :: [x2, x1, x3, x4]) := (List.perm_middle (l₁ := [x2]) (a := x0) (l₂ := [x1, x3, x4])).cons w03_or
      have hdisp := disp5_of_step (extra := 2) hg ws_c03_or_b_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_or_b
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.1.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_or, x2, x0, x1, x3, x4] : List W5).Perm (w03_or :: x3 :: [x2, x0, x1, x4]) := (List.perm_middle (l₁ := [x2, x0, x1]) (a := x3) (l₂ := [x4])).cons w03_or
      have hdisp := disp5_of_step (extra := 2) hg ws_c03_or_b_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_or_b
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_or, x2, x0, x1, x3, x4] : List W5).Perm (x2 :: x0 :: [w03_or, x1, x3, x4]) := (List.perm_middle (l₁ := [w03_or]) (a := x2) (l₂ := [x0, x1, x3, x4])).trans ((List.perm_middle (l₁ := [w03_or]) (a := x0) (l₂ := [x1, x3, x4])).cons x2)
      have hdisp := disp5_of_step (extra := 2) hg ws_c03_or_b_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_or_b
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_or, x2, x0, x1, x3, x4] : List W5).Perm (x2 :: x3 :: [w03_or, x0, x1, x4]) := (List.perm_middle (l₁ := [w03_or]) (a := x2) (l₂ := [x0, x1, x3, x4])).trans ((List.perm_middle (l₁ := [w03_or, x0, x1]) (a := x3) (l₂ := [x4])).cons x2)
      have hdisp := disp5_of_step (extra := 2) hg ws_c03_or_b_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_or_b
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_or, x2, x0, x1, x3, x4] : List W5).Perm (x0 :: x1 :: [w03_or, x2, x3, x4]) := (List.perm_middle (l₁ := [w03_or, x2]) (a := x0) (l₂ := [x1, x3, x4])).trans ((List.perm_middle (l₁ := [w03_or, x2]) (a := x1) (l₂ := [x3, x4])).cons x0)
      have hdisp := disp5_of_step (extra := 2) hg ws_c03_or_b_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_or_b
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_or, x2, x0, x1, x3, x4] : List W5).Perm (x0 :: x3 :: [w03_or, x2, x1, x4]) := (List.perm_middle (l₁ := [w03_or, x2]) (a := x0) (l₂ := [x1, x3, x4])).trans ((List.perm_middle (l₁ := [w03_or, x2, x1]) (a := x3) (l₂ := [x4])).cons x0)
      have hdisp := disp5_of_step (extra := 2) hg ws_c03_or_b_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_or_b
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.2.symm.trans hdisp)
    · have hperm : ([w03_or, x2, x0, x1, x3, x4] : List W5).Perm (x3 :: x4 :: [w03_or, x2, x0, x1]) := (List.perm_middle (l₁ := [w03_or, x2, x0, x1]) (a := x3) (l₂ := [x4])).trans ((List.perm_middle (l₁ := [w03_or, x2, x0, x1]) (a := x4) (l₂ := [])).cons x3)
      have hdisp := disp5_of_step (extra := 2) hg ws_c03_or_b_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_or_b
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.2.symm.trans hdisp)
  rcases first_live (k := 6) hl with hend | ⟨a, ha, b, hb, hab, z, hz, hzout, rest, hs, tail⟩
  · exact ws_c03_or_b_not_goal g hg hend
  have hval : ∀ w ∈ ([w03_or, x2, x0, x1, x3, x4] : List W5).toFinset, Valid5 w := fun w hw => ws_c03_or_b_valid w (List.mem_toFinset.mp hw)
  have ha' : a ∈ ([w03_or, x2, x0, x1, x3, x4] : List W5) := List.mem_toFinset.mp ha
  have hb' : b ∈ ([w03_or, x2, x0, x1, x3, x4] : List W5) := List.mem_toFinset.mp hb
  have hstep_sym : ∀ (u v : W5) (z' : W5) (rest' : Finset W5),
      (u, v) ∈ [(w03_or, x2), (w03_or, x0), (w03_or, x3), (x2, x0), (x2, x3), (x0, x1), (x0, x3), (x3, x4)] ∨ (v, u) ∈ [(w03_or, x2), (w03_or, x0), (w03_or, x3), (x2, x0), (x2, x3), (x0, x1), (x0, x3), (x3, x4)] →
      z' ∈ basicOps5 u v → z' ∉ ([w03_or, x2, x0, x1, x3, x4] : List W5).toFinset →
      ([w03_or, x2, x0, x1, x3, x4] : List W5).toFinset = insert u (insert v rest') →
      live basicOps5 g 6 (insert z' rest') → False := by
    intro u v z' rest' huv hz' hzout' hs' tail'
    rcases huv with h | h
    · exact hstep u v h z' hz' hzout' rest' hs' tail'
    · exact hstep v u h z' (ops5_swap u v ▸ hz') hzout' rest' (by rw [hs', Finset.insert_comm]) tail'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha' hb'
  rcases ha' with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_or_b_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) w03_or) = w03_or := by rw [p_01_w03_or]
    have hfb : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_or_b_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) w03_or) = w03_or := by rw [p_34_w03_or]
    have hfb : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_or_b_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x2) = x2 := by rw [p_01_x2]
    have hfb : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_or_b_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x2) = x2 := by rw [p_34_x2]
    have hfb : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_or_b_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x0) = x0 := by rw [p_34_x0]
    have hfb : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_or_b_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    have hfb : (perm5 (swap 0 1) w03_or) = w03_or := by rw [p_01_w03_or]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_or_b_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    have hfb : (perm5 (swap 0 1) x2) = x2 := by rw [p_01_x2]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_or_b_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    have hfb : (perm5 (swap 0 1) x3) = x3 := by rw [p_01_x3]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_or_b_inv_34] at hzout0 hs0
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 0 1 hg hval hz0 hzout0 hs0 tail0
    rw [ws_c03_or_b_inv_01] at hzout1 hs1
    have hfa : (perm5 (swap 0 1) (perm5 (swap 3 4) x1)) = x0 := by rw [p_34_x1, p_01_x1]
    have hfb : (perm5 (swap 0 1) (perm5 (swap 3 4) x4)) = x3 := by rw [p_34_x4, p_01_x3]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inl (by simp)) hz1 hzout1 hs1 tail1
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_or_b_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x3) = x3 := by rw [p_01_x3]
    have hfb : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_or_b_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    have hfb : (perm5 (swap 3 4) w03_or) = w03_or := by rw [p_34_w03_or]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_or_b_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    have hfb : (perm5 (swap 3 4) x2) = x2 := by rw [p_34_x2]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_or_b_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    have hfb : (perm5 (swap 3 4) x0) = x0 := by rw [p_34_x0]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_or_b_inv_34] at hzout0 hs0
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 0 1 hg hval hz0 hzout0 hs0 tail0
    rw [ws_c03_or_b_inv_01] at hzout1 hs1
    have hfa : (perm5 (swap 0 1) (perm5 (swap 3 4) x4)) = x3 := by rw [p_34_x4, p_01_x3]
    have hfb : (perm5 (swap 0 1) (perm5 (swap 3 4) x1)) = x0 := by rw [p_34_x1, p_01_x1]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inr (by simp)) hz1 hzout1 hs1 tail1
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem chk_c03_or_ab : (disp5 1 1 1 1 0 0 (opt5 6) 0xffff7fdff7fdff7fdff000000000fffffffc00 0xefff37cdf37cdf37cdf000000000003ffffc00 [0xf1dd499264992649926000000000ffc0000000, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 1 1 1 1 0 0 (opt5 6) 0xffff7fdff7fdff7fdff000000000fffffffc00 0xf1dd499264992649926000000000ffc0000000 [0xefff37cdf37cdf37cdf000000000003ffffc00, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 1 1 1 1 0 0 (opt5 6) 0xffff7fdff7fdff7fdff000000000fffffffc00 0xab7712c4b12c4b12c4b00000000000000ffc00 [0xefff37cdf37cdf37cdf000000000003ffffc00, 0xf1dd499264992649926000000000ffc0000000, 0xcdbb254952549525495000000000003ff00000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 1 1 1 1 0 0 (opt5 6) 0xffff7fdff7fdff7fdff000000000fffffffc00 0xfe1e8e2388e2388e2380000003ff0000000000 [0xefff37cdf37cdf37cdf000000000003ffffc00, 0xf1dd499264992649926000000000ffc0000000, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 1 1 1 1 0 0 (opt5 6) 0xefff37cdf37cdf37cdf000000000003ffffc00 0xf1dd499264992649926000000000ffc0000000 [0xffff7fdff7fdff7fdff000000000fffffffc00, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 1 1 1 1 0 0 (opt5 6) 0xefff37cdf37cdf37cdf000000000003ffffc00 0xab7712c4b12c4b12c4b00000000000000ffc00 [0xffff7fdff7fdff7fdff000000000fffffffc00, 0xf1dd499264992649926000000000ffc0000000, 0xcdbb254952549525495000000000003ff00000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 1 1 1 1 0 0 (opt5 6) 0xefff37cdf37cdf37cdf000000000003ffffc00 0xfe1e8e2388e2388e2380000003ff0000000000 [0xffff7fdff7fdff7fdff000000000fffffffc00, 0xf1dd499264992649926000000000ffc0000000, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 1 1 1 1 0 0 (opt5 6) 0xf1dd499264992649926000000000ffc0000000 0xab7712c4b12c4b12c4b00000000000000ffc00 [0xffff7fdff7fdff7fdff000000000fffffffc00, 0xefff37cdf37cdf37cdf000000000003ffffc00, 0xcdbb254952549525495000000000003ff00000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 1 1 1 1 0 0 (opt5 6) 0xf1dd499264992649926000000000ffc0000000 0xfe1e8e2388e2388e2380000003ff0000000000 [0xffff7fdff7fdff7fdff000000000fffffffc00, 0xefff37cdf37cdf37cdf000000000003ffffc00, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 1 1 1 1 0 0 (opt5 6) 0xab7712c4b12c4b12c4b00000000000000ffc00 0xcdbb254952549525495000000000003ff00000 [0xffff7fdff7fdff7fdff000000000fffffffc00, 0xefff37cdf37cdf37cdf000000000003ffffc00, 0xf1dd499264992649926000000000ffc0000000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 1 1 1 1 0 0 (opt5 6) 0xab7712c4b12c4b12c4b00000000000000ffc00 0xfe1e8e2388e2388e2380000003ff0000000000 [0xffff7fdff7fdff7fdff000000000fffffffc00, 0xefff37cdf37cdf37cdf000000000003ffffc00, 0xf1dd499264992649926000000000ffc0000000, 0xcdbb254952549525495000000000003ff00000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 1 1 1 1 0 0 (opt5 6) 0xfe1e8e2388e2388e2380000003ff0000000000 0xffe0f03c0f03c0f03c00000ffc000000000000 [0xffff7fdff7fdff7fdff000000000fffffffc00, 0xefff37cdf37cdf37cdf000000000003ffffc00, 0xf1dd499264992649926000000000ffc0000000, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000]) = false := by decide +kernel

lemma ws_c03_or_ab_nd : ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).Nodup := by decide +kernel
lemma ws_c03_or_ab_valid : ∀ w ∈ ([w03_or, x01, x2, x0, x1, x3, x4] : List W5), Valid5 w := fun w hw => valid5_of_valid5B ((List.all_eq_true.mp (by decide +kernel : ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).all valid5B = true)) w hw)
lemma ws_c03_or_ab_not_goal : ∀ g : W5, (g = goal5 ∨ g = ~~~goal5) → ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).toFinset ≠ {g} := by
  intro g _ heq; have hc := congrArg Finset.card heq; rw [List.toFinset_card_of_nodup ws_c03_or_ab_nd, Finset.card_singleton] at hc; simp at hc
lemma ws_c03_or_ab_inv_01 : ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).toFinset.image (perm5 (swap 0 1)) = ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).toFinset := by
  ext w; simp only [List.toFinset_cons, List.toFinset_nil, Finset.image_insert, Finset.image_empty, Finset.mem_insert, Finset.notMem_empty, or_false, p_01_w03_or, p_01_x01, p_01_x2, p_01_x0, p_01_x1, p_01_x3, p_01_x4]; tauto
lemma ws_c03_or_ab_inv_34 : ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).toFinset.image (perm5 (swap 3 4)) = ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).toFinset := by
  ext w; simp only [List.toFinset_cons, List.toFinset_nil, Finset.image_insert, Finset.image_empty, Finset.mem_insert, Finset.notMem_empty, or_false, p_34_w03_or, p_34_x01, p_34_x2, p_34_x0, p_34_x1, p_34_x3, p_34_x4]; tauto
lemma no_c03_or_ab {g : W5} (hg : g = goal5 ∨ g = ~~~goal5)
    (hl : live basicOps5 g 7 ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).toFinset)
    (hav : HasAvoid 7 ![1, 1, 1, 0, 0] ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).toFinset) : False := by
  have hstep : ∀ a b : W5, (a, b) ∈ [(w03_or, x01), (w03_or, x2), (w03_or, x0), (w03_or, x3), (x01, x2), (x01, x0), (x01, x3), (x2, x0), (x2, x3), (x0, x1), (x0, x3), (x3, x4)] →
      ∀ z ∈ basicOps5 a b, z ∉ ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).toFinset → ∀ rest : Finset W5,
      ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).toFinset = insert a (insert b rest) →
      live basicOps5 g 6 (insert z rest) → False := by
    intro a b hab z hz hzout rest hs tail
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hab
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hperm : ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).Perm (w03_or :: x01 :: [x2, x0, x1, x3, x4]) := List.Perm.refl _
      have hdisp := disp5_of_step (extra := 1) hg ws_c03_or_ab_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_or_ab
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.1.1.1.1.1.1.1.1.symm.trans hdisp)
    · have hperm : ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).Perm (w03_or :: x2 :: [x01, x0, x1, x3, x4]) := (List.perm_middle (l₁ := [x01]) (a := x2) (l₂ := [x0, x1, x3, x4])).cons w03_or
      have hdisp := disp5_of_step (extra := 1) hg ws_c03_or_ab_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_or_ab
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.1.1.1.1.1.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).Perm (w03_or :: x0 :: [x01, x2, x1, x3, x4]) := (List.perm_middle (l₁ := [x01, x2]) (a := x0) (l₂ := [x1, x3, x4])).cons w03_or
      have hdisp := disp5_of_step (extra := 1) hg ws_c03_or_ab_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_or_ab
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.1.1.1.1.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).Perm (w03_or :: x3 :: [x01, x2, x0, x1, x4]) := (List.perm_middle (l₁ := [x01, x2, x0, x1]) (a := x3) (l₂ := [x4])).cons w03_or
      have hdisp := disp5_of_step (extra := 1) hg ws_c03_or_ab_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_or_ab
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.1.1.1.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).Perm (x01 :: x2 :: [w03_or, x0, x1, x3, x4]) := (List.perm_middle (l₁ := [w03_or]) (a := x01) (l₂ := [x2, x0, x1, x3, x4])).trans ((List.perm_middle (l₁ := [w03_or]) (a := x2) (l₂ := [x0, x1, x3, x4])).cons x01)
      have hdisp := disp5_of_step (extra := 1) hg ws_c03_or_ab_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_or_ab
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.1.1.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).Perm (x01 :: x0 :: [w03_or, x2, x1, x3, x4]) := (List.perm_middle (l₁ := [w03_or]) (a := x01) (l₂ := [x2, x0, x1, x3, x4])).trans ((List.perm_middle (l₁ := [w03_or, x2]) (a := x0) (l₂ := [x1, x3, x4])).cons x01)
      have hdisp := disp5_of_step (extra := 1) hg ws_c03_or_ab_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_or_ab
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.1.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).Perm (x01 :: x3 :: [w03_or, x2, x0, x1, x4]) := (List.perm_middle (l₁ := [w03_or]) (a := x01) (l₂ := [x2, x0, x1, x3, x4])).trans ((List.perm_middle (l₁ := [w03_or, x2, x0, x1]) (a := x3) (l₂ := [x4])).cons x01)
      have hdisp := disp5_of_step (extra := 1) hg ws_c03_or_ab_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_or_ab
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).Perm (x2 :: x0 :: [w03_or, x01, x1, x3, x4]) := (List.perm_middle (l₁ := [w03_or, x01]) (a := x2) (l₂ := [x0, x1, x3, x4])).trans ((List.perm_middle (l₁ := [w03_or, x01]) (a := x0) (l₂ := [x1, x3, x4])).cons x2)
      have hdisp := disp5_of_step (extra := 1) hg ws_c03_or_ab_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_or_ab
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).Perm (x2 :: x3 :: [w03_or, x01, x0, x1, x4]) := (List.perm_middle (l₁ := [w03_or, x01]) (a := x2) (l₂ := [x0, x1, x3, x4])).trans ((List.perm_middle (l₁ := [w03_or, x01, x0, x1]) (a := x3) (l₂ := [x4])).cons x2)
      have hdisp := disp5_of_step (extra := 1) hg ws_c03_or_ab_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_or_ab
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).Perm (x0 :: x1 :: [w03_or, x01, x2, x3, x4]) := (List.perm_middle (l₁ := [w03_or, x01, x2]) (a := x0) (l₂ := [x1, x3, x4])).trans ((List.perm_middle (l₁ := [w03_or, x01, x2]) (a := x1) (l₂ := [x3, x4])).cons x0)
      have hdisp := disp5_of_step (extra := 1) hg ws_c03_or_ab_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_or_ab
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).Perm (x0 :: x3 :: [w03_or, x01, x2, x1, x4]) := (List.perm_middle (l₁ := [w03_or, x01, x2]) (a := x0) (l₂ := [x1, x3, x4])).trans ((List.perm_middle (l₁ := [w03_or, x01, x2, x1]) (a := x3) (l₂ := [x4])).cons x0)
      have hdisp := disp5_of_step (extra := 1) hg ws_c03_or_ab_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_or_ab
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.2.symm.trans hdisp)
    · have hperm : ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).Perm (x3 :: x4 :: [w03_or, x01, x2, x0, x1]) := (List.perm_middle (l₁ := [w03_or, x01, x2, x0, x1]) (a := x3) (l₂ := [x4])).trans ((List.perm_middle (l₁ := [w03_or, x01, x2, x0, x1]) (a := x4) (l₂ := [])).cons x3)
      have hdisp := disp5_of_step (extra := 1) hg ws_c03_or_ab_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_or_ab
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.2.symm.trans hdisp)
  rcases first_live (k := 6) hl with hend | ⟨a, ha, b, hb, hab, z, hz, hzout, rest, hs, tail⟩
  · exact ws_c03_or_ab_not_goal g hg hend
  have hval : ∀ w ∈ ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).toFinset, Valid5 w := fun w hw => ws_c03_or_ab_valid w (List.mem_toFinset.mp hw)
  have ha' : a ∈ ([w03_or, x01, x2, x0, x1, x3, x4] : List W5) := List.mem_toFinset.mp ha
  have hb' : b ∈ ([w03_or, x01, x2, x0, x1, x3, x4] : List W5) := List.mem_toFinset.mp hb
  have hstep_sym : ∀ (u v : W5) (z' : W5) (rest' : Finset W5),
      (u, v) ∈ [(w03_or, x01), (w03_or, x2), (w03_or, x0), (w03_or, x3), (x01, x2), (x01, x0), (x01, x3), (x2, x0), (x2, x3), (x0, x1), (x0, x3), (x3, x4)] ∨ (v, u) ∈ [(w03_or, x01), (w03_or, x2), (w03_or, x0), (w03_or, x3), (x01, x2), (x01, x0), (x01, x3), (x2, x0), (x2, x3), (x0, x1), (x0, x3), (x3, x4)] →
      z' ∈ basicOps5 u v → z' ∉ ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).toFinset →
      ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).toFinset = insert u (insert v rest') →
      live basicOps5 g 6 (insert z' rest') → False := by
    intro u v z' rest' huv hz' hzout' hs' tail'
    rcases huv with h | h
    · exact hstep u v h z' hz' hzout' rest' hs' tail'
    · exact hstep v u h z' (ops5_swap u v ▸ hz') hzout' rest' (by rw [hs', Finset.insert_comm]) tail'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha' hb'
  rcases ha' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_or_ab_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) w03_or) = w03_or := by rw [p_01_w03_or]
    have hfb : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_or_ab_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) w03_or) = w03_or := by rw [p_34_w03_or]
    have hfb : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_or_ab_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x01) = x01 := by rw [p_01_x01]
    have hfb : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_or_ab_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x01) = x01 := by rw [p_34_x01]
    have hfb : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_or_ab_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x2) = x2 := by rw [p_01_x2]
    have hfb : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_or_ab_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x2) = x2 := by rw [p_34_x2]
    have hfb : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_or_ab_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x0) = x0 := by rw [p_34_x0]
    have hfb : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_or_ab_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    have hfb : (perm5 (swap 0 1) w03_or) = w03_or := by rw [p_01_w03_or]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_or_ab_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    have hfb : (perm5 (swap 0 1) x01) = x01 := by rw [p_01_x01]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_or_ab_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    have hfb : (perm5 (swap 0 1) x2) = x2 := by rw [p_01_x2]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_or_ab_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    have hfb : (perm5 (swap 0 1) x3) = x3 := by rw [p_01_x3]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_or_ab_inv_34] at hzout0 hs0
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 0 1 hg hval hz0 hzout0 hs0 tail0
    rw [ws_c03_or_ab_inv_01] at hzout1 hs1
    have hfa : (perm5 (swap 0 1) (perm5 (swap 3 4) x1)) = x0 := by rw [p_34_x1, p_01_x1]
    have hfb : (perm5 (swap 0 1) (perm5 (swap 3 4) x4)) = x3 := by rw [p_34_x4, p_01_x3]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inl (by simp)) hz1 hzout1 hs1 tail1
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_or_ab_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x3) = x3 := by rw [p_01_x3]
    have hfb : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_or_ab_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    have hfb : (perm5 (swap 3 4) w03_or) = w03_or := by rw [p_34_w03_or]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_or_ab_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    have hfb : (perm5 (swap 3 4) x01) = x01 := by rw [p_34_x01]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_or_ab_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    have hfb : (perm5 (swap 3 4) x2) = x2 := by rw [p_34_x2]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_or_ab_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    have hfb : (perm5 (swap 3 4) x0) = x0 := by rw [p_34_x0]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_or_ab_inv_34] at hzout0 hs0
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 0 1 hg hval hz0 hzout0 hs0 tail0
    rw [ws_c03_or_ab_inv_01] at hzout1 hs1
    have hfa : (perm5 (swap 0 1) (perm5 (swap 3 4) x4)) = x3 := by rw [p_34_x4, p_01_x3]
    have hfb : (perm5 (swap 0 1) (perm5 (swap 3 4) x1)) = x0 := by rw [p_34_x1, p_01_x1]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inr (by simp)) hz1 hzout1 hs1 tail1
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem chk_c03_an_b : (disp5 2 1 1 1 0 0 (opt5 6) 0xe22364d9364d9364d9000000000003ffffc00 0xf1dd499264992649926000000000ffc0000000 [0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 2 1 1 1 0 0 (opt5 6) 0xe22364d9364d9364d9000000000003ffffc00 0xab7712c4b12c4b12c4b00000000000000ffc00 [0xf1dd499264992649926000000000ffc0000000, 0xcdbb254952549525495000000000003ff00000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 2 1 1 1 0 0 (opt5 6) 0xe22364d9364d9364d9000000000003ffffc00 0xfe1e8e2388e2388e2380000003ff0000000000 [0xf1dd499264992649926000000000ffc0000000, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 2 1 1 1 0 0 (opt5 6) 0xf1dd499264992649926000000000ffc0000000 0xab7712c4b12c4b12c4b00000000000000ffc00 [0xe22364d9364d9364d9000000000003ffffc00, 0xcdbb254952549525495000000000003ff00000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 2 1 1 1 0 0 (opt5 6) 0xf1dd499264992649926000000000ffc0000000 0xfe1e8e2388e2388e2380000003ff0000000000 [0xe22364d9364d9364d9000000000003ffffc00, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 2 1 1 1 0 0 (opt5 6) 0xab7712c4b12c4b12c4b00000000000000ffc00 0xcdbb254952549525495000000000003ff00000 [0xe22364d9364d9364d9000000000003ffffc00, 0xf1dd499264992649926000000000ffc0000000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 2 1 1 1 0 0 (opt5 6) 0xab7712c4b12c4b12c4b00000000000000ffc00 0xfe1e8e2388e2388e2380000003ff0000000000 [0xe22364d9364d9364d9000000000003ffffc00, 0xf1dd499264992649926000000000ffc0000000, 0xcdbb254952549525495000000000003ff00000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 2 1 1 1 0 0 (opt5 6) 0xfe1e8e2388e2388e2380000003ff0000000000 0xffe0f03c0f03c0f03c00000ffc000000000000 [0xe22364d9364d9364d9000000000003ffffc00, 0xf1dd499264992649926000000000ffc0000000, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000]) = false := by decide +kernel

lemma ws_c03_an_b_nd : ([w03_an, x2, x0, x1, x3, x4] : List W5).Nodup := by decide +kernel
lemma ws_c03_an_b_valid : ∀ w ∈ ([w03_an, x2, x0, x1, x3, x4] : List W5), Valid5 w := fun w hw => valid5_of_valid5B ((List.all_eq_true.mp (by decide +kernel : ([w03_an, x2, x0, x1, x3, x4] : List W5).all valid5B = true)) w hw)
lemma ws_c03_an_b_not_goal : ∀ g : W5, (g = goal5 ∨ g = ~~~goal5) → ([w03_an, x2, x0, x1, x3, x4] : List W5).toFinset ≠ {g} := by
  intro g _ heq; have hc := congrArg Finset.card heq; rw [List.toFinset_card_of_nodup ws_c03_an_b_nd, Finset.card_singleton] at hc; simp at hc
lemma ws_c03_an_b_inv_01 : ([w03_an, x2, x0, x1, x3, x4] : List W5).toFinset.image (perm5 (swap 0 1)) = ([w03_an, x2, x0, x1, x3, x4] : List W5).toFinset := by
  ext w; simp only [List.toFinset_cons, List.toFinset_nil, Finset.image_insert, Finset.image_empty, Finset.mem_insert, Finset.notMem_empty, or_false, p_01_w03_an, p_01_x2, p_01_x0, p_01_x1, p_01_x3, p_01_x4]; tauto
lemma ws_c03_an_b_inv_34 : ([w03_an, x2, x0, x1, x3, x4] : List W5).toFinset.image (perm5 (swap 3 4)) = ([w03_an, x2, x0, x1, x3, x4] : List W5).toFinset := by
  ext w; simp only [List.toFinset_cons, List.toFinset_nil, Finset.image_insert, Finset.image_empty, Finset.mem_insert, Finset.notMem_empty, or_false, p_34_w03_an, p_34_x2, p_34_x0, p_34_x1, p_34_x3, p_34_x4]; tauto
lemma no_c03_an_b {g : W5} (hg : g = goal5 ∨ g = ~~~goal5)
    (hl : live basicOps5 g 7 ([w03_an, x2, x0, x1, x3, x4] : List W5).toFinset)
    (hav : HasAvoid 7 ![1, 1, 1, 0, 0] ([w03_an, x2, x0, x1, x3, x4] : List W5).toFinset) : False := by
  have hstep : ∀ a b : W5, (a, b) ∈ [(w03_an, x2), (w03_an, x0), (w03_an, x3), (x2, x0), (x2, x3), (x0, x1), (x0, x3), (x3, x4)] →
      ∀ z ∈ basicOps5 a b, z ∉ ([w03_an, x2, x0, x1, x3, x4] : List W5).toFinset → ∀ rest : Finset W5,
      ([w03_an, x2, x0, x1, x3, x4] : List W5).toFinset = insert a (insert b rest) →
      live basicOps5 g 6 (insert z rest) → False := by
    intro a b hab z hz hzout rest hs tail
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hab
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hperm : ([w03_an, x2, x0, x1, x3, x4] : List W5).Perm (w03_an :: x2 :: [x0, x1, x3, x4]) := List.Perm.refl _
      have hdisp := disp5_of_step (extra := 2) hg ws_c03_an_b_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_an_b
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.1.1.1.1.symm.trans hdisp)
    · have hperm : ([w03_an, x2, x0, x1, x3, x4] : List W5).Perm (w03_an :: x0 :: [x2, x1, x3, x4]) := (List.perm_middle (l₁ := [x2]) (a := x0) (l₂ := [x1, x3, x4])).cons w03_an
      have hdisp := disp5_of_step (extra := 2) hg ws_c03_an_b_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_an_b
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.1.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_an, x2, x0, x1, x3, x4] : List W5).Perm (w03_an :: x3 :: [x2, x0, x1, x4]) := (List.perm_middle (l₁ := [x2, x0, x1]) (a := x3) (l₂ := [x4])).cons w03_an
      have hdisp := disp5_of_step (extra := 2) hg ws_c03_an_b_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_an_b
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_an, x2, x0, x1, x3, x4] : List W5).Perm (x2 :: x0 :: [w03_an, x1, x3, x4]) := (List.perm_middle (l₁ := [w03_an]) (a := x2) (l₂ := [x0, x1, x3, x4])).trans ((List.perm_middle (l₁ := [w03_an]) (a := x0) (l₂ := [x1, x3, x4])).cons x2)
      have hdisp := disp5_of_step (extra := 2) hg ws_c03_an_b_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_an_b
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_an, x2, x0, x1, x3, x4] : List W5).Perm (x2 :: x3 :: [w03_an, x0, x1, x4]) := (List.perm_middle (l₁ := [w03_an]) (a := x2) (l₂ := [x0, x1, x3, x4])).trans ((List.perm_middle (l₁ := [w03_an, x0, x1]) (a := x3) (l₂ := [x4])).cons x2)
      have hdisp := disp5_of_step (extra := 2) hg ws_c03_an_b_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_an_b
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_an, x2, x0, x1, x3, x4] : List W5).Perm (x0 :: x1 :: [w03_an, x2, x3, x4]) := (List.perm_middle (l₁ := [w03_an, x2]) (a := x0) (l₂ := [x1, x3, x4])).trans ((List.perm_middle (l₁ := [w03_an, x2]) (a := x1) (l₂ := [x3, x4])).cons x0)
      have hdisp := disp5_of_step (extra := 2) hg ws_c03_an_b_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_an_b
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_an, x2, x0, x1, x3, x4] : List W5).Perm (x0 :: x3 :: [w03_an, x2, x1, x4]) := (List.perm_middle (l₁ := [w03_an, x2]) (a := x0) (l₂ := [x1, x3, x4])).trans ((List.perm_middle (l₁ := [w03_an, x2, x1]) (a := x3) (l₂ := [x4])).cons x0)
      have hdisp := disp5_of_step (extra := 2) hg ws_c03_an_b_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_an_b
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.2.symm.trans hdisp)
    · have hperm : ([w03_an, x2, x0, x1, x3, x4] : List W5).Perm (x3 :: x4 :: [w03_an, x2, x0, x1]) := (List.perm_middle (l₁ := [w03_an, x2, x0, x1]) (a := x3) (l₂ := [x4])).trans ((List.perm_middle (l₁ := [w03_an, x2, x0, x1]) (a := x4) (l₂ := [])).cons x3)
      have hdisp := disp5_of_step (extra := 2) hg ws_c03_an_b_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_an_b
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.2.symm.trans hdisp)
  rcases first_live (k := 6) hl with hend | ⟨a, ha, b, hb, hab, z, hz, hzout, rest, hs, tail⟩
  · exact ws_c03_an_b_not_goal g hg hend
  have hval : ∀ w ∈ ([w03_an, x2, x0, x1, x3, x4] : List W5).toFinset, Valid5 w := fun w hw => ws_c03_an_b_valid w (List.mem_toFinset.mp hw)
  have ha' : a ∈ ([w03_an, x2, x0, x1, x3, x4] : List W5) := List.mem_toFinset.mp ha
  have hb' : b ∈ ([w03_an, x2, x0, x1, x3, x4] : List W5) := List.mem_toFinset.mp hb
  have hstep_sym : ∀ (u v : W5) (z' : W5) (rest' : Finset W5),
      (u, v) ∈ [(w03_an, x2), (w03_an, x0), (w03_an, x3), (x2, x0), (x2, x3), (x0, x1), (x0, x3), (x3, x4)] ∨ (v, u) ∈ [(w03_an, x2), (w03_an, x0), (w03_an, x3), (x2, x0), (x2, x3), (x0, x1), (x0, x3), (x3, x4)] →
      z' ∈ basicOps5 u v → z' ∉ ([w03_an, x2, x0, x1, x3, x4] : List W5).toFinset →
      ([w03_an, x2, x0, x1, x3, x4] : List W5).toFinset = insert u (insert v rest') →
      live basicOps5 g 6 (insert z' rest') → False := by
    intro u v z' rest' huv hz' hzout' hs' tail'
    rcases huv with h | h
    · exact hstep u v h z' hz' hzout' rest' hs' tail'
    · exact hstep v u h z' (ops5_swap u v ▸ hz') hzout' rest' (by rw [hs', Finset.insert_comm]) tail'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha' hb'
  rcases ha' with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_an_b_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) w03_an) = w03_an := by rw [p_01_w03_an]
    have hfb : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_an_b_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) w03_an) = w03_an := by rw [p_34_w03_an]
    have hfb : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_an_b_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x2) = x2 := by rw [p_01_x2]
    have hfb : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_an_b_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x2) = x2 := by rw [p_34_x2]
    have hfb : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_an_b_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x0) = x0 := by rw [p_34_x0]
    have hfb : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_an_b_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    have hfb : (perm5 (swap 0 1) w03_an) = w03_an := by rw [p_01_w03_an]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_an_b_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    have hfb : (perm5 (swap 0 1) x2) = x2 := by rw [p_01_x2]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_an_b_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    have hfb : (perm5 (swap 0 1) x3) = x3 := by rw [p_01_x3]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_an_b_inv_34] at hzout0 hs0
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 0 1 hg hval hz0 hzout0 hs0 tail0
    rw [ws_c03_an_b_inv_01] at hzout1 hs1
    have hfa : (perm5 (swap 0 1) (perm5 (swap 3 4) x1)) = x0 := by rw [p_34_x1, p_01_x1]
    have hfb : (perm5 (swap 0 1) (perm5 (swap 3 4) x4)) = x3 := by rw [p_34_x4, p_01_x3]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inl (by simp)) hz1 hzout1 hs1 tail1
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_an_b_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x3) = x3 := by rw [p_01_x3]
    have hfb : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_an_b_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    have hfb : (perm5 (swap 3 4) w03_an) = w03_an := by rw [p_34_w03_an]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_an_b_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    have hfb : (perm5 (swap 3 4) x2) = x2 := by rw [p_34_x2]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_an_b_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    have hfb : (perm5 (swap 3 4) x0) = x0 := by rw [p_34_x0]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_an_b_inv_34] at hzout0 hs0
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 0 1 hg hval hz0 hzout0 hs0 tail0
    rw [ws_c03_an_b_inv_01] at hzout1 hs1
    have hfa : (perm5 (swap 0 1) (perm5 (swap 3 4) x4)) = x3 := by rw [p_34_x4, p_01_x3]
    have hfb : (perm5 (swap 0 1) (perm5 (swap 3 4) x1)) = x0 := by rw [p_34_x1, p_01_x1]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inr (by simp)) hz1 hzout1 hs1 tail1
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem chk_c03_an_ab : (disp5 1 1 1 1 0 0 (opt5 6) 0xe22364d9364d9364d9000000000003ffffc00 0xefff37cdf37cdf37cdf000000000003ffffc00 [0xf1dd499264992649926000000000ffc0000000, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 1 1 1 1 0 0 (opt5 6) 0xe22364d9364d9364d9000000000003ffffc00 0xf1dd499264992649926000000000ffc0000000 [0xefff37cdf37cdf37cdf000000000003ffffc00, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 1 1 1 1 0 0 (opt5 6) 0xe22364d9364d9364d9000000000003ffffc00 0xab7712c4b12c4b12c4b00000000000000ffc00 [0xefff37cdf37cdf37cdf000000000003ffffc00, 0xf1dd499264992649926000000000ffc0000000, 0xcdbb254952549525495000000000003ff00000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 1 1 1 1 0 0 (opt5 6) 0xe22364d9364d9364d9000000000003ffffc00 0xfe1e8e2388e2388e2380000003ff0000000000 [0xefff37cdf37cdf37cdf000000000003ffffc00, 0xf1dd499264992649926000000000ffc0000000, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 1 1 1 1 0 0 (opt5 6) 0xefff37cdf37cdf37cdf000000000003ffffc00 0xf1dd499264992649926000000000ffc0000000 [0xe22364d9364d9364d9000000000003ffffc00, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 1 1 1 1 0 0 (opt5 6) 0xefff37cdf37cdf37cdf000000000003ffffc00 0xab7712c4b12c4b12c4b00000000000000ffc00 [0xe22364d9364d9364d9000000000003ffffc00, 0xf1dd499264992649926000000000ffc0000000, 0xcdbb254952549525495000000000003ff00000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 1 1 1 1 0 0 (opt5 6) 0xefff37cdf37cdf37cdf000000000003ffffc00 0xfe1e8e2388e2388e2380000003ff0000000000 [0xe22364d9364d9364d9000000000003ffffc00, 0xf1dd499264992649926000000000ffc0000000, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 1 1 1 1 0 0 (opt5 6) 0xf1dd499264992649926000000000ffc0000000 0xab7712c4b12c4b12c4b00000000000000ffc00 [0xe22364d9364d9364d9000000000003ffffc00, 0xefff37cdf37cdf37cdf000000000003ffffc00, 0xcdbb254952549525495000000000003ff00000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 1 1 1 1 0 0 (opt5 6) 0xf1dd499264992649926000000000ffc0000000 0xfe1e8e2388e2388e2380000003ff0000000000 [0xe22364d9364d9364d9000000000003ffffc00, 0xefff37cdf37cdf37cdf000000000003ffffc00, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 1 1 1 1 0 0 (opt5 6) 0xab7712c4b12c4b12c4b00000000000000ffc00 0xcdbb254952549525495000000000003ff00000 [0xe22364d9364d9364d9000000000003ffffc00, 0xefff37cdf37cdf37cdf000000000003ffffc00, 0xf1dd499264992649926000000000ffc0000000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 1 1 1 1 0 0 (opt5 6) 0xab7712c4b12c4b12c4b00000000000000ffc00 0xfe1e8e2388e2388e2380000003ff0000000000 [0xe22364d9364d9364d9000000000003ffffc00, 0xefff37cdf37cdf37cdf000000000003ffffc00, 0xf1dd499264992649926000000000ffc0000000, 0xcdbb254952549525495000000000003ff00000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 1 1 1 1 0 0 (opt5 6) 0xfe1e8e2388e2388e2380000003ff0000000000 0xffe0f03c0f03c0f03c00000ffc000000000000 [0xe22364d9364d9364d9000000000003ffffc00, 0xefff37cdf37cdf37cdf000000000003ffffc00, 0xf1dd499264992649926000000000ffc0000000, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000]) = false := by decide +kernel

lemma ws_c03_an_ab_nd : ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).Nodup := by decide +kernel
lemma ws_c03_an_ab_valid : ∀ w ∈ ([w03_an, x01, x2, x0, x1, x3, x4] : List W5), Valid5 w := fun w hw => valid5_of_valid5B ((List.all_eq_true.mp (by decide +kernel : ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).all valid5B = true)) w hw)
lemma ws_c03_an_ab_not_goal : ∀ g : W5, (g = goal5 ∨ g = ~~~goal5) → ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).toFinset ≠ {g} := by
  intro g _ heq; have hc := congrArg Finset.card heq; rw [List.toFinset_card_of_nodup ws_c03_an_ab_nd, Finset.card_singleton] at hc; simp at hc
lemma ws_c03_an_ab_inv_01 : ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).toFinset.image (perm5 (swap 0 1)) = ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).toFinset := by
  ext w; simp only [List.toFinset_cons, List.toFinset_nil, Finset.image_insert, Finset.image_empty, Finset.mem_insert, Finset.notMem_empty, or_false, p_01_w03_an, p_01_x01, p_01_x2, p_01_x0, p_01_x1, p_01_x3, p_01_x4]; tauto
lemma ws_c03_an_ab_inv_34 : ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).toFinset.image (perm5 (swap 3 4)) = ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).toFinset := by
  ext w; simp only [List.toFinset_cons, List.toFinset_nil, Finset.image_insert, Finset.image_empty, Finset.mem_insert, Finset.notMem_empty, or_false, p_34_w03_an, p_34_x01, p_34_x2, p_34_x0, p_34_x1, p_34_x3, p_34_x4]; tauto
lemma no_c03_an_ab {g : W5} (hg : g = goal5 ∨ g = ~~~goal5)
    (hl : live basicOps5 g 7 ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).toFinset)
    (hav : HasAvoid 7 ![1, 1, 1, 0, 0] ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).toFinset) : False := by
  have hstep : ∀ a b : W5, (a, b) ∈ [(w03_an, x01), (w03_an, x2), (w03_an, x0), (w03_an, x3), (x01, x2), (x01, x0), (x01, x3), (x2, x0), (x2, x3), (x0, x1), (x0, x3), (x3, x4)] →
      ∀ z ∈ basicOps5 a b, z ∉ ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).toFinset → ∀ rest : Finset W5,
      ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).toFinset = insert a (insert b rest) →
      live basicOps5 g 6 (insert z rest) → False := by
    intro a b hab z hz hzout rest hs tail
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hab
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hperm : ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).Perm (w03_an :: x01 :: [x2, x0, x1, x3, x4]) := List.Perm.refl _
      have hdisp := disp5_of_step (extra := 1) hg ws_c03_an_ab_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_an_ab
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.1.1.1.1.1.1.1.1.symm.trans hdisp)
    · have hperm : ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).Perm (w03_an :: x2 :: [x01, x0, x1, x3, x4]) := (List.perm_middle (l₁ := [x01]) (a := x2) (l₂ := [x0, x1, x3, x4])).cons w03_an
      have hdisp := disp5_of_step (extra := 1) hg ws_c03_an_ab_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_an_ab
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.1.1.1.1.1.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).Perm (w03_an :: x0 :: [x01, x2, x1, x3, x4]) := (List.perm_middle (l₁ := [x01, x2]) (a := x0) (l₂ := [x1, x3, x4])).cons w03_an
      have hdisp := disp5_of_step (extra := 1) hg ws_c03_an_ab_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_an_ab
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.1.1.1.1.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).Perm (w03_an :: x3 :: [x01, x2, x0, x1, x4]) := (List.perm_middle (l₁ := [x01, x2, x0, x1]) (a := x3) (l₂ := [x4])).cons w03_an
      have hdisp := disp5_of_step (extra := 1) hg ws_c03_an_ab_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_an_ab
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.1.1.1.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).Perm (x01 :: x2 :: [w03_an, x0, x1, x3, x4]) := (List.perm_middle (l₁ := [w03_an]) (a := x01) (l₂ := [x2, x0, x1, x3, x4])).trans ((List.perm_middle (l₁ := [w03_an]) (a := x2) (l₂ := [x0, x1, x3, x4])).cons x01)
      have hdisp := disp5_of_step (extra := 1) hg ws_c03_an_ab_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_an_ab
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.1.1.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).Perm (x01 :: x0 :: [w03_an, x2, x1, x3, x4]) := (List.perm_middle (l₁ := [w03_an]) (a := x01) (l₂ := [x2, x0, x1, x3, x4])).trans ((List.perm_middle (l₁ := [w03_an, x2]) (a := x0) (l₂ := [x1, x3, x4])).cons x01)
      have hdisp := disp5_of_step (extra := 1) hg ws_c03_an_ab_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_an_ab
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.1.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).Perm (x01 :: x3 :: [w03_an, x2, x0, x1, x4]) := (List.perm_middle (l₁ := [w03_an]) (a := x01) (l₂ := [x2, x0, x1, x3, x4])).trans ((List.perm_middle (l₁ := [w03_an, x2, x0, x1]) (a := x3) (l₂ := [x4])).cons x01)
      have hdisp := disp5_of_step (extra := 1) hg ws_c03_an_ab_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_an_ab
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).Perm (x2 :: x0 :: [w03_an, x01, x1, x3, x4]) := (List.perm_middle (l₁ := [w03_an, x01]) (a := x2) (l₂ := [x0, x1, x3, x4])).trans ((List.perm_middle (l₁ := [w03_an, x01]) (a := x0) (l₂ := [x1, x3, x4])).cons x2)
      have hdisp := disp5_of_step (extra := 1) hg ws_c03_an_ab_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_an_ab
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).Perm (x2 :: x3 :: [w03_an, x01, x0, x1, x4]) := (List.perm_middle (l₁ := [w03_an, x01]) (a := x2) (l₂ := [x0, x1, x3, x4])).trans ((List.perm_middle (l₁ := [w03_an, x01, x0, x1]) (a := x3) (l₂ := [x4])).cons x2)
      have hdisp := disp5_of_step (extra := 1) hg ws_c03_an_ab_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_an_ab
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).Perm (x0 :: x1 :: [w03_an, x01, x2, x3, x4]) := (List.perm_middle (l₁ := [w03_an, x01, x2]) (a := x0) (l₂ := [x1, x3, x4])).trans ((List.perm_middle (l₁ := [w03_an, x01, x2]) (a := x1) (l₂ := [x3, x4])).cons x0)
      have hdisp := disp5_of_step (extra := 1) hg ws_c03_an_ab_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_an_ab
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).Perm (x0 :: x3 :: [w03_an, x01, x2, x1, x4]) := (List.perm_middle (l₁ := [w03_an, x01, x2]) (a := x0) (l₂ := [x1, x3, x4])).trans ((List.perm_middle (l₁ := [w03_an, x01, x2, x1]) (a := x3) (l₂ := [x4])).cons x0)
      have hdisp := disp5_of_step (extra := 1) hg ws_c03_an_ab_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_an_ab
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.2.symm.trans hdisp)
    · have hperm : ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).Perm (x3 :: x4 :: [w03_an, x01, x2, x0, x1]) := (List.perm_middle (l₁ := [w03_an, x01, x2, x0, x1]) (a := x3) (l₂ := [x4])).trans ((List.perm_middle (l₁ := [w03_an, x01, x2, x0, x1]) (a := x4) (l₂ := [])).cons x3)
      have hdisp := disp5_of_step (extra := 1) hg ws_c03_an_ab_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_an_ab
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.2.symm.trans hdisp)
  rcases first_live (k := 6) hl with hend | ⟨a, ha, b, hb, hab, z, hz, hzout, rest, hs, tail⟩
  · exact ws_c03_an_ab_not_goal g hg hend
  have hval : ∀ w ∈ ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).toFinset, Valid5 w := fun w hw => ws_c03_an_ab_valid w (List.mem_toFinset.mp hw)
  have ha' : a ∈ ([w03_an, x01, x2, x0, x1, x3, x4] : List W5) := List.mem_toFinset.mp ha
  have hb' : b ∈ ([w03_an, x01, x2, x0, x1, x3, x4] : List W5) := List.mem_toFinset.mp hb
  have hstep_sym : ∀ (u v : W5) (z' : W5) (rest' : Finset W5),
      (u, v) ∈ [(w03_an, x01), (w03_an, x2), (w03_an, x0), (w03_an, x3), (x01, x2), (x01, x0), (x01, x3), (x2, x0), (x2, x3), (x0, x1), (x0, x3), (x3, x4)] ∨ (v, u) ∈ [(w03_an, x01), (w03_an, x2), (w03_an, x0), (w03_an, x3), (x01, x2), (x01, x0), (x01, x3), (x2, x0), (x2, x3), (x0, x1), (x0, x3), (x3, x4)] →
      z' ∈ basicOps5 u v → z' ∉ ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).toFinset →
      ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).toFinset = insert u (insert v rest') →
      live basicOps5 g 6 (insert z' rest') → False := by
    intro u v z' rest' huv hz' hzout' hs' tail'
    rcases huv with h | h
    · exact hstep u v h z' hz' hzout' rest' hs' tail'
    · exact hstep v u h z' (ops5_swap u v ▸ hz') hzout' rest' (by rw [hs', Finset.insert_comm]) tail'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha' hb'
  rcases ha' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_an_ab_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) w03_an) = w03_an := by rw [p_01_w03_an]
    have hfb : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_an_ab_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) w03_an) = w03_an := by rw [p_34_w03_an]
    have hfb : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_an_ab_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x01) = x01 := by rw [p_01_x01]
    have hfb : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_an_ab_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x01) = x01 := by rw [p_34_x01]
    have hfb : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_an_ab_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x2) = x2 := by rw [p_01_x2]
    have hfb : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_an_ab_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x2) = x2 := by rw [p_34_x2]
    have hfb : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_an_ab_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x0) = x0 := by rw [p_34_x0]
    have hfb : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_an_ab_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    have hfb : (perm5 (swap 0 1) w03_an) = w03_an := by rw [p_01_w03_an]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_an_ab_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    have hfb : (perm5 (swap 0 1) x01) = x01 := by rw [p_01_x01]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_an_ab_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    have hfb : (perm5 (swap 0 1) x2) = x2 := by rw [p_01_x2]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_an_ab_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    have hfb : (perm5 (swap 0 1) x3) = x3 := by rw [p_01_x3]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_an_ab_inv_34] at hzout0 hs0
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 0 1 hg hval hz0 hzout0 hs0 tail0
    rw [ws_c03_an_ab_inv_01] at hzout1 hs1
    have hfa : (perm5 (swap 0 1) (perm5 (swap 3 4) x1)) = x0 := by rw [p_34_x1, p_01_x1]
    have hfb : (perm5 (swap 0 1) (perm5 (swap 3 4) x4)) = x3 := by rw [p_34_x4, p_01_x3]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inl (by simp)) hz1 hzout1 hs1 tail1
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_an_ab_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x3) = x3 := by rw [p_01_x3]
    have hfb : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_an_ab_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    have hfb : (perm5 (swap 3 4) w03_an) = w03_an := by rw [p_34_w03_an]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_an_ab_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    have hfb : (perm5 (swap 3 4) x01) = x01 := by rw [p_34_x01]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_an_ab_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    have hfb : (perm5 (swap 3 4) x2) = x2 := by rw [p_34_x2]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_an_ab_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    have hfb : (perm5 (swap 3 4) x0) = x0 := by rw [p_34_x0]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_an_ab_inv_34] at hzout0 hs0
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 0 1 hg hval hz0 hzout0 hs0 tail0
    rw [ws_c03_an_ab_inv_01] at hzout1 hs1
    have hfa : (perm5 (swap 0 1) (perm5 (swap 3 4) x4)) = x3 := by rw [p_34_x4, p_01_x3]
    have hfb : (perm5 (swap 0 1) (perm5 (swap 3 4) x1)) = x0 := by rw [p_34_x1, p_01_x1]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inr (by simp)) hz1 hzout1 hs1 tail1
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem chk_c13_or_b_0 : disp5 2 2 1 1 0 0 (opt5 6) 0xfbff5bd6f5bd6f5bd6f000000000ffc00ffc00 0xf1dd499264992649926000000000ffc0000000 [0xefff37cdf37cdf37cdf000000000003ffffc00, 0xcdbb254952549525495000000000003ff00000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem chk_c13_or_b_1 : disp5 2 2 1 1 0 0 (opt5 6) 0xfbff5bd6f5bd6f5bd6f000000000ffc00ffc00 0xefff37cdf37cdf37cdf000000000003ffffc00 [0xf1dd499264992649926000000000ffc0000000, 0xcdbb254952549525495000000000003ff00000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem chk_c13_or_b_2 : disp5 2 2 1 1 0 0 (opt5 6) 0xfbff5bd6f5bd6f5bd6f000000000ffc00ffc00 0xcdbb254952549525495000000000003ff00000 [0xf1dd499264992649926000000000ffc0000000, 0xefff37cdf37cdf37cdf000000000003ffffc00, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem chk_c13_or_b_3 : disp5 2 2 1 1 0 0 (opt5 6) 0xfbff5bd6f5bd6f5bd6f000000000ffc00ffc00 0xfe1e8e2388e2388e2380000003ff0000000000 [0xf1dd499264992649926000000000ffc0000000, 0xefff37cdf37cdf37cdf000000000003ffffc00, 0xcdbb254952549525495000000000003ff00000, 0xffe0f03c0f03c0f03c00000ffc000000000000] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem chk_c13_or_b_4 : disp5 2 2 1 1 0 0 (opt5 6) 0xf1dd499264992649926000000000ffc0000000 0xcdbb254952549525495000000000003ff00000 [0xfbff5bd6f5bd6f5bd6f000000000ffc00ffc00, 0xefff37cdf37cdf37cdf000000000003ffffc00, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem chk_c13_or_b_5 : disp5 2 2 1 1 0 0 (opt5 6) 0xf1dd499264992649926000000000ffc0000000 0xfe1e8e2388e2388e2380000003ff0000000000 [0xfbff5bd6f5bd6f5bd6f000000000ffc00ffc00, 0xefff37cdf37cdf37cdf000000000003ffffc00, 0xcdbb254952549525495000000000003ff00000, 0xffe0f03c0f03c0f03c00000ffc000000000000] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem chk_c13_or_b_6 : disp5 2 2 1 1 0 0 (opt5 6) 0xfe1e8e2388e2388e2380000003ff0000000000 0xffe0f03c0f03c0f03c00000ffc000000000000 [0xfbff5bd6f5bd6f5bd6f000000000ffc00ffc00, 0xf1dd499264992649926000000000ffc0000000, 0xefff37cdf37cdf37cdf000000000003ffffc00, 0xcdbb254952549525495000000000003ff00000] = false := by decide +kernel

lemma ws_c13_or_b_nd : ([x02, x2, x01, x1, x3, x4] : List W5).Nodup := by decide +kernel
lemma ws_c13_or_b_valid : ∀ w ∈ ([x02, x2, x01, x1, x3, x4] : List W5), Valid5 w := fun w hw => valid5_of_valid5B ((List.all_eq_true.mp (by decide +kernel : ([x02, x2, x01, x1, x3, x4] : List W5).all valid5B = true)) w hw)
lemma ws_c13_or_b_not_goal : ∀ g : W5, (g = goal5 ∨ g = ~~~goal5) → ([x02, x2, x01, x1, x3, x4] : List W5).toFinset ≠ {g} := by
  intro g _ heq; have hc := congrArg Finset.card heq; rw [List.toFinset_card_of_nodup ws_c13_or_b_nd, Finset.card_singleton] at hc; simp at hc
lemma ws_c13_or_b_inv_12 : ([x02, x2, x01, x1, x3, x4] : List W5).toFinset.image (perm5 (swap 1 2)) = ([x02, x2, x01, x1, x3, x4] : List W5).toFinset := by
  ext w; simp only [List.toFinset_cons, List.toFinset_nil, Finset.image_insert, Finset.image_empty, Finset.mem_insert, Finset.notMem_empty, or_false, p_12_x02, p_12_x2, p_12_x01, p_12_x1, p_12_x3, p_12_x4]; tauto
lemma ws_c13_or_b_inv_34 : ([x02, x2, x01, x1, x3, x4] : List W5).toFinset.image (perm5 (swap 3 4)) = ([x02, x2, x01, x1, x3, x4] : List W5).toFinset := by
  ext w; simp only [List.toFinset_cons, List.toFinset_nil, Finset.image_insert, Finset.image_empty, Finset.mem_insert, Finset.notMem_empty, or_false, p_34_x02, p_34_x2, p_34_x01, p_34_x1, p_34_x3, p_34_x4]; tauto
lemma no_c13_or_b {g : W5} (hg : g = goal5 ∨ g = ~~~goal5)
    (hl : live basicOps5 g 7 ([x02, x2, x01, x1, x3, x4] : List W5).toFinset)
    (hav : HasAvoid 7 ![2, 1, 1, 0, 0] ([x02, x2, x01, x1, x3, x4] : List W5).toFinset) : False := by
  have hstep : ∀ a b : W5, (a, b) ∈ [(x02, x2), (x02, x01), (x02, x1), (x02, x3), (x2, x1), (x2, x3), (x3, x4)] →
      ∀ z ∈ basicOps5 a b, z ∉ ([x02, x2, x01, x1, x3, x4] : List W5).toFinset → ∀ rest : Finset W5,
      ([x02, x2, x01, x1, x3, x4] : List W5).toFinset = insert a (insert b rest) →
      live basicOps5 g 6 (insert z rest) → False := by
    intro a b hab z hz hzout rest hs tail
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hab
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hperm : ([x02, x2, x01, x1, x3, x4] : List W5).Perm (x02 :: x2 :: [x01, x1, x3, x4]) := List.Perm.refl _
      have hdisp := disp5_of_step (extra := 2) hg ws_c13_or_b_nd (by decide) hperm hs hz hzout tail hav
      exact Bool.noConfusion (chk_c13_or_b_0.symm.trans hdisp)
    · have hperm : ([x02, x2, x01, x1, x3, x4] : List W5).Perm (x02 :: x01 :: [x2, x1, x3, x4]) := (List.perm_middle (l₁ := [x2]) (a := x01) (l₂ := [x1, x3, x4])).cons x02
      have hdisp := disp5_of_step (extra := 2) hg ws_c13_or_b_nd (by decide) hperm hs hz hzout tail hav
      exact Bool.noConfusion (chk_c13_or_b_1.symm.trans hdisp)
    · have hperm : ([x02, x2, x01, x1, x3, x4] : List W5).Perm (x02 :: x1 :: [x2, x01, x3, x4]) := (List.perm_middle (l₁ := [x2, x01]) (a := x1) (l₂ := [x3, x4])).cons x02
      have hdisp := disp5_of_step (extra := 2) hg ws_c13_or_b_nd (by decide) hperm hs hz hzout tail hav
      exact Bool.noConfusion (chk_c13_or_b_2.symm.trans hdisp)
    · have hperm : ([x02, x2, x01, x1, x3, x4] : List W5).Perm (x02 :: x3 :: [x2, x01, x1, x4]) := (List.perm_middle (l₁ := [x2, x01, x1]) (a := x3) (l₂ := [x4])).cons x02
      have hdisp := disp5_of_step (extra := 2) hg ws_c13_or_b_nd (by decide) hperm hs hz hzout tail hav
      exact Bool.noConfusion (chk_c13_or_b_3.symm.trans hdisp)
    · have hperm : ([x02, x2, x01, x1, x3, x4] : List W5).Perm (x2 :: x1 :: [x02, x01, x3, x4]) := (List.perm_middle (l₁ := [x02]) (a := x2) (l₂ := [x01, x1, x3, x4])).trans ((List.perm_middle (l₁ := [x02, x01]) (a := x1) (l₂ := [x3, x4])).cons x2)
      have hdisp := disp5_of_step (extra := 2) hg ws_c13_or_b_nd (by decide) hperm hs hz hzout tail hav
      exact Bool.noConfusion (chk_c13_or_b_4.symm.trans hdisp)
    · have hperm : ([x02, x2, x01, x1, x3, x4] : List W5).Perm (x2 :: x3 :: [x02, x01, x1, x4]) := (List.perm_middle (l₁ := [x02]) (a := x2) (l₂ := [x01, x1, x3, x4])).trans ((List.perm_middle (l₁ := [x02, x01, x1]) (a := x3) (l₂ := [x4])).cons x2)
      have hdisp := disp5_of_step (extra := 2) hg ws_c13_or_b_nd (by decide) hperm hs hz hzout tail hav
      exact Bool.noConfusion (chk_c13_or_b_5.symm.trans hdisp)
    · have hperm : ([x02, x2, x01, x1, x3, x4] : List W5).Perm (x3 :: x4 :: [x02, x2, x01, x1]) := (List.perm_middle (l₁ := [x02, x2, x01, x1]) (a := x3) (l₂ := [x4])).trans ((List.perm_middle (l₁ := [x02, x2, x01, x1]) (a := x4) (l₂ := [])).cons x3)
      have hdisp := disp5_of_step (extra := 2) hg ws_c13_or_b_nd (by decide) hperm hs hz hzout tail hav
      exact Bool.noConfusion (chk_c13_or_b_6.symm.trans hdisp)
  rcases first_live (k := 6) hl with hend | ⟨a, ha, b, hb, hab, z, hz, hzout, rest, hs, tail⟩
  · exact ws_c13_or_b_not_goal g hg hend
  have hval : ∀ w ∈ ([x02, x2, x01, x1, x3, x4] : List W5).toFinset, Valid5 w := fun w hw => ws_c13_or_b_valid w (List.mem_toFinset.mp hw)
  have ha' : a ∈ ([x02, x2, x01, x1, x3, x4] : List W5) := List.mem_toFinset.mp ha
  have hb' : b ∈ ([x02, x2, x01, x1, x3, x4] : List W5) := List.mem_toFinset.mp hb
  have hstep_sym : ∀ (u v : W5) (z' : W5) (rest' : Finset W5),
      (u, v) ∈ [(x02, x2), (x02, x01), (x02, x1), (x02, x3), (x2, x1), (x2, x3), (x3, x4)] ∨ (v, u) ∈ [(x02, x2), (x02, x01), (x02, x1), (x02, x3), (x2, x1), (x2, x3), (x3, x4)] →
      z' ∈ basicOps5 u v → z' ∉ ([x02, x2, x01, x1, x3, x4] : List W5).toFinset →
      ([x02, x2, x01, x1, x3, x4] : List W5).toFinset = insert u (insert v rest') →
      live basicOps5 g 6 (insert z' rest') → False := by
    intro u v z' rest' huv hz' hzout' hs' tail'
    rcases huv with h | h
    · exact hstep u v h z' hz' hzout' rest' hs' tail'
    · exact hstep v u h z' (ops5_swap u v ▸ hz') hzout' rest' (by rw [hs', Finset.insert_comm]) tail'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha' hb'
  rcases ha' with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c13_or_b_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x02) = x02 := by rw [p_34_x02]
    have hfb : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 1 2 hg hval hz hzout hs tail
    rw [ws_c13_or_b_inv_12] at hzout0 hs0
    have hfa : (perm5 (swap 1 2) x2) = x1 := by rw [p_12_x2]
    have hfb : (perm5 (swap 1 2) x01) = x02 := by rw [p_12_x01]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c13_or_b_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x2) = x2 := by rw [p_34_x2]
    have hfb : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 1 2 hg hval hz hzout hs tail
    rw [ws_c13_or_b_inv_12] at hzout0 hs0
    have hfa : (perm5 (swap 1 2) x01) = x02 := by rw [p_12_x01]
    have hfb : (perm5 (swap 1 2) x2) = x1 := by rw [p_12_x2]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hab rfl
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 1 2 hg hval hz hzout hs tail
    rw [ws_c13_or_b_inv_12] at hzout0 hs0
    have hfa : (perm5 (swap 1 2) x01) = x02 := by rw [p_12_x01]
    have hfb : (perm5 (swap 1 2) x1) = x2 := by rw [p_12_x1]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 1 2 hg hval hz hzout hs tail
    rw [ws_c13_or_b_inv_12] at hzout0 hs0
    have hfa : (perm5 (swap 1 2) x01) = x02 := by rw [p_12_x01]
    have hfb : (perm5 (swap 1 2) x3) = x3 := by rw [p_12_x3]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c13_or_b_inv_34] at hzout0 hs0
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 1 2 hg hval hz0 hzout0 hs0 tail0
    rw [ws_c13_or_b_inv_12] at hzout1 hs1
    have hfa : (perm5 (swap 1 2) (perm5 (swap 3 4) x01)) = x02 := by rw [p_34_x01, p_12_x01]
    have hfb : (perm5 (swap 1 2) (perm5 (swap 3 4) x4)) = x3 := by rw [p_34_x4, p_12_x3]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inl (by simp)) hz1 hzout1 hs1 tail1
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 1 2 hg hval hz hzout hs tail
    rw [ws_c13_or_b_inv_12] at hzout0 hs0
    have hfa : (perm5 (swap 1 2) x1) = x2 := by rw [p_12_x1]
    have hfb : (perm5 (swap 1 2) x01) = x02 := by rw [p_12_x01]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  · exact hab rfl
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 1 2 hg hval hz hzout hs tail
    rw [ws_c13_or_b_inv_12] at hzout0 hs0
    have hfa : (perm5 (swap 1 2) x1) = x2 := by rw [p_12_x1]
    have hfb : (perm5 (swap 1 2) x3) = x3 := by rw [p_12_x3]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c13_or_b_inv_34] at hzout0 hs0
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 1 2 hg hval hz0 hzout0 hs0 tail0
    rw [ws_c13_or_b_inv_12] at hzout1 hs1
    have hfa : (perm5 (swap 1 2) (perm5 (swap 3 4) x1)) = x2 := by rw [p_34_x1, p_12_x1]
    have hfb : (perm5 (swap 1 2) (perm5 (swap 3 4) x4)) = x3 := by rw [p_34_x4, p_12_x3]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inl (by simp)) hz1 hzout1 hs1 tail1
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 1 2 hg hval hz hzout hs tail
    rw [ws_c13_or_b_inv_12] at hzout0 hs0
    have hfa : (perm5 (swap 1 2) x3) = x3 := by rw [p_12_x3]
    have hfb : (perm5 (swap 1 2) x01) = x02 := by rw [p_12_x01]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 1 2 hg hval hz hzout hs tail
    rw [ws_c13_or_b_inv_12] at hzout0 hs0
    have hfa : (perm5 (swap 1 2) x3) = x3 := by rw [p_12_x3]
    have hfb : (perm5 (swap 1 2) x1) = x2 := by rw [p_12_x1]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c13_or_b_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    have hfb : (perm5 (swap 3 4) x02) = x02 := by rw [p_34_x02]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c13_or_b_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    have hfb : (perm5 (swap 3 4) x2) = x2 := by rw [p_34_x2]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c13_or_b_inv_34] at hzout0 hs0
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 1 2 hg hval hz0 hzout0 hs0 tail0
    rw [ws_c13_or_b_inv_12] at hzout1 hs1
    have hfa : (perm5 (swap 1 2) (perm5 (swap 3 4) x4)) = x3 := by rw [p_34_x4, p_12_x3]
    have hfb : (perm5 (swap 1 2) (perm5 (swap 3 4) x01)) = x02 := by rw [p_34_x01, p_12_x01]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inr (by simp)) hz1 hzout1 hs1 tail1
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c13_or_b_inv_34] at hzout0 hs0
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 1 2 hg hval hz0 hzout0 hs0 tail0
    rw [ws_c13_or_b_inv_12] at hzout1 hs1
    have hfa : (perm5 (swap 1 2) (perm5 (swap 3 4) x4)) = x3 := by rw [p_34_x4, p_12_x3]
    have hfb : (perm5 (swap 1 2) (perm5 (swap 3 4) x1)) = x2 := by rw [p_34_x1, p_12_x1]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inr (by simp)) hz1 hzout1 hs1 tail1
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem chk_c34_or_ab_0 : disp5 1 1 1 1 1 0 (opt5 6) 0xffdfcfb3ecfb3ecfb3e0000003ffffc0000000 0xf1dd499264992649926000000000ffc0000000 [0xfe1e8e2388e2388e2380000003ff0000000000, 0xefff37cdf37cdf37cdf000000000003ffffc00, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000, 0xffe0f03c0f03c0f03c00000ffc000000000000] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem chk_c34_or_ab_1 : disp5 1 1 1 1 1 0 (opt5 6) 0xffdfcfb3ecfb3ecfb3e0000003ffffc0000000 0xefff37cdf37cdf37cdf000000000003ffffc00 [0xf1dd499264992649926000000000ffc0000000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000, 0xffe0f03c0f03c0f03c00000ffc000000000000] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem chk_c34_or_ab_2 : disp5 1 1 1 1 1 0 (opt5 6) 0xffdfcfb3ecfb3ecfb3e0000003ffffc0000000 0xab7712c4b12c4b12c4b00000000000000ffc00 [0xf1dd499264992649926000000000ffc0000000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xefff37cdf37cdf37cdf000000000003ffffc00, 0xcdbb254952549525495000000000003ff00000, 0xffe0f03c0f03c0f03c00000ffc000000000000] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem chk_c34_or_ab_3 : disp5 1 1 1 1 1 0 (opt5 6) 0xffdfcfb3ecfb3ecfb3e0000003ffffc0000000 0xffe0f03c0f03c0f03c00000ffc000000000000 [0xf1dd499264992649926000000000ffc0000000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xefff37cdf37cdf37cdf000000000003ffffc00, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem chk_c34_or_ab_4 : disp5 1 1 1 1 1 0 (opt5 6) 0xf1dd499264992649926000000000ffc0000000 0xfe1e8e2388e2388e2380000003ff0000000000 [0xffdfcfb3ecfb3ecfb3e0000003ffffc0000000, 0xefff37cdf37cdf37cdf000000000003ffffc00, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000, 0xffe0f03c0f03c0f03c00000ffc000000000000] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem chk_c34_or_ab_5 : disp5 1 1 1 1 1 0 (opt5 6) 0xf1dd499264992649926000000000ffc0000000 0xab7712c4b12c4b12c4b00000000000000ffc00 [0xffdfcfb3ecfb3ecfb3e0000003ffffc0000000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xefff37cdf37cdf37cdf000000000003ffffc00, 0xcdbb254952549525495000000000003ff00000, 0xffe0f03c0f03c0f03c00000ffc000000000000] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem chk_c34_or_ab_6 : disp5 1 1 1 1 1 0 (opt5 6) 0xf1dd499264992649926000000000ffc0000000 0xffe0f03c0f03c0f03c00000ffc000000000000 [0xffdfcfb3ecfb3ecfb3e0000003ffffc0000000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xefff37cdf37cdf37cdf000000000003ffffc00, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000] = false := by decide +kernel

lemma ws_c34_or_ab_nd : ([x23, x2, x3, x01, x0, x1, x4] : List W5).Nodup := by decide +kernel
lemma ws_c34_or_ab_valid : ∀ w ∈ ([x23, x2, x3, x01, x0, x1, x4] : List W5), Valid5 w := fun w hw => valid5_of_valid5B ((List.all_eq_true.mp (by decide +kernel : ([x23, x2, x3, x01, x0, x1, x4] : List W5).all valid5B = true)) w hw)
lemma ws_c34_or_ab_not_goal : ∀ g : W5, (g = goal5 ∨ g = ~~~goal5) → ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset ≠ {g} := by
  intro g _ heq; have hc := congrArg Finset.card heq; rw [List.toFinset_card_of_nodup ws_c34_or_ab_nd, Finset.card_singleton] at hc; simp at hc
lemma ws_c34_or_ab_inv_01 : ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset.image (perm5 (swap 0 1)) = ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset := by
  ext w; simp only [List.toFinset_cons, List.toFinset_nil, Finset.image_insert, Finset.image_empty, Finset.mem_insert, Finset.notMem_empty, or_false, p_01_x23, p_01_x2, p_01_x3, p_01_x01, p_01_x0, p_01_x1, p_01_x4]; tauto
lemma ws_c34_or_ab_inv_23 : ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset.image (perm5 (swap 2 3)) = ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset := by
  ext w; simp only [List.toFinset_cons, List.toFinset_nil, Finset.image_insert, Finset.image_empty, Finset.mem_insert, Finset.notMem_empty, or_false, p_23_x23, p_23_x2, p_23_x3, p_23_x01, p_23_x0, p_23_x1, p_23_x4]; tauto
lemma ws_c34_or_ab_inv_0213 : (([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset.image (perm5 (swap 0 2))).image (perm5 (swap 1 3)) = ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset := by
  ext w; simp only [List.toFinset_cons, List.toFinset_nil, Finset.image_insert, Finset.image_empty, Finset.mem_insert, Finset.notMem_empty, or_false, p_0213_x23, p_0213_x2, p_0213_x3, p_0213_x01, p_0213_x0, p_0213_x1, p_0213_x4]; tauto
lemma no_c34_or_ab {g : W5} (hg : g = goal5 ∨ g = ~~~goal5)
    (hl : live basicOps5 g 7 ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset)
    (hav : HasAvoid 7 ![1, 1, 1, 1, 0] ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset) : False := by
  have hstep : ∀ a b : W5, (a, b) ∈ [(x23, x2), (x23, x01), (x23, x0), (x23, x4), (x2, x3), (x2, x0), (x2, x4)] →
      ∀ z ∈ basicOps5 a b, z ∉ ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset → ∀ rest : Finset W5,
      ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset = insert a (insert b rest) →
      live basicOps5 g 6 (insert z rest) → False := by
    intro a b hab z hz hzout rest hs tail
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hab
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hperm : ([x23, x2, x3, x01, x0, x1, x4] : List W5).Perm (x23 :: x2 :: [x3, x01, x0, x1, x4]) := List.Perm.refl _
      have hdisp := disp5_of_step (extra := 1) hg ws_c34_or_ab_nd (by decide) hperm hs hz hzout tail hav
      exact Bool.noConfusion (chk_c34_or_ab_0.symm.trans hdisp)
    · have hperm : ([x23, x2, x3, x01, x0, x1, x4] : List W5).Perm (x23 :: x01 :: [x2, x3, x0, x1, x4]) := (List.perm_middle (l₁ := [x2, x3]) (a := x01) (l₂ := [x0, x1, x4])).cons x23
      have hdisp := disp5_of_step (extra := 1) hg ws_c34_or_ab_nd (by decide) hperm hs hz hzout tail hav
      exact Bool.noConfusion (chk_c34_or_ab_1.symm.trans hdisp)
    · have hperm : ([x23, x2, x3, x01, x0, x1, x4] : List W5).Perm (x23 :: x0 :: [x2, x3, x01, x1, x4]) := (List.perm_middle (l₁ := [x2, x3, x01]) (a := x0) (l₂ := [x1, x4])).cons x23
      have hdisp := disp5_of_step (extra := 1) hg ws_c34_or_ab_nd (by decide) hperm hs hz hzout tail hav
      exact Bool.noConfusion (chk_c34_or_ab_2.symm.trans hdisp)
    · have hperm : ([x23, x2, x3, x01, x0, x1, x4] : List W5).Perm (x23 :: x4 :: [x2, x3, x01, x0, x1]) := (List.perm_middle (l₁ := [x2, x3, x01, x0, x1]) (a := x4) (l₂ := [])).cons x23
      have hdisp := disp5_of_step (extra := 1) hg ws_c34_or_ab_nd (by decide) hperm hs hz hzout tail hav
      exact Bool.noConfusion (chk_c34_or_ab_3.symm.trans hdisp)
    · have hperm : ([x23, x2, x3, x01, x0, x1, x4] : List W5).Perm (x2 :: x3 :: [x23, x01, x0, x1, x4]) := (List.perm_middle (l₁ := [x23]) (a := x2) (l₂ := [x3, x01, x0, x1, x4])).trans ((List.perm_middle (l₁ := [x23]) (a := x3) (l₂ := [x01, x0, x1, x4])).cons x2)
      have hdisp := disp5_of_step (extra := 1) hg ws_c34_or_ab_nd (by decide) hperm hs hz hzout tail hav
      exact Bool.noConfusion (chk_c34_or_ab_4.symm.trans hdisp)
    · have hperm : ([x23, x2, x3, x01, x0, x1, x4] : List W5).Perm (x2 :: x0 :: [x23, x3, x01, x1, x4]) := (List.perm_middle (l₁ := [x23]) (a := x2) (l₂ := [x3, x01, x0, x1, x4])).trans ((List.perm_middle (l₁ := [x23, x3, x01]) (a := x0) (l₂ := [x1, x4])).cons x2)
      have hdisp := disp5_of_step (extra := 1) hg ws_c34_or_ab_nd (by decide) hperm hs hz hzout tail hav
      exact Bool.noConfusion (chk_c34_or_ab_5.symm.trans hdisp)
    · have hperm : ([x23, x2, x3, x01, x0, x1, x4] : List W5).Perm (x2 :: x4 :: [x23, x3, x01, x0, x1]) := (List.perm_middle (l₁ := [x23]) (a := x2) (l₂ := [x3, x01, x0, x1, x4])).trans ((List.perm_middle (l₁ := [x23, x3, x01, x0, x1]) (a := x4) (l₂ := [])).cons x2)
      have hdisp := disp5_of_step (extra := 1) hg ws_c34_or_ab_nd (by decide) hperm hs hz hzout tail hav
      exact Bool.noConfusion (chk_c34_or_ab_6.symm.trans hdisp)
  rcases first_live (k := 6) hl with hend | ⟨a, ha, b, hb, hab, z, hz, hzout, rest, hs, tail⟩
  · exact ws_c34_or_ab_not_goal g hg hend
  have hval : ∀ w ∈ ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset, Valid5 w := fun w hw => ws_c34_or_ab_valid w (List.mem_toFinset.mp hw)
  have ha' : a ∈ ([x23, x2, x3, x01, x0, x1, x4] : List W5) := List.mem_toFinset.mp ha
  have hb' : b ∈ ([x23, x2, x3, x01, x0, x1, x4] : List W5) := List.mem_toFinset.mp hb
  have hstep_sym : ∀ (u v : W5) (z' : W5) (rest' : Finset W5),
      (u, v) ∈ [(x23, x2), (x23, x01), (x23, x0), (x23, x4), (x2, x3), (x2, x0), (x2, x4)] ∨ (v, u) ∈ [(x23, x2), (x23, x01), (x23, x0), (x23, x4), (x2, x3), (x2, x0), (x2, x4)] →
      z' ∈ basicOps5 u v → z' ∉ ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset →
      ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset = insert u (insert v rest') →
      live basicOps5 g 6 (insert z' rest') → False := by
    intro u v z' rest' huv hz' hzout' hs' tail'
    rcases huv with h | h
    · exact hstep u v h z' hz' hzout' rest' hs' tail'
    · exact hstep v u h z' (ops5_swap u v ▸ hz') hzout' rest' (by rw [hs', Finset.insert_comm]) tail'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha' hb'
  rcases ha' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 2 3 hg hval hz hzout hs tail
    rw [ws_c34_or_ab_inv_23] at hzout0 hs0
    have hfa : (perm5 (swap 2 3) x23) = x23 := by rw [p_23_x23]
    have hfb : (perm5 (swap 2 3) x3) = x2 := by rw [p_23_x3]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c34_or_ab_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x23) = x23 := by rw [p_01_x23]
    have hfb : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 2 hg hval hz hzout hs tail
    have hval0 : ∀ w ∈ ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset.image (perm5 (swap 0 2)), Valid5 w := fun w hw => by obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hw; exact perm5_valid 0 2 u
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 1 3 hg hval0 hz0 hzout0 hs0 tail0
    rw [ws_c34_or_ab_inv_0213] at hzout1 hs1
    have hfa : (perm5 (swap 1 3) (perm5 (swap 0 2) x2)) = x0 := by rw [p_0213_x2]
    have hfb : (perm5 (swap 1 3) (perm5 (swap 0 2) x01)) = x23 := by rw [p_0213_x01]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inr (by simp)) hz1 hzout1 hs1 tail1
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 2 hg hval hz hzout hs tail
    have hval0 : ∀ w ∈ ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset.image (perm5 (swap 0 2)), Valid5 w := fun w hw => by obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hw; exact perm5_valid 0 2 u
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 1 3 hg hval0 hz0 hzout0 hs0 tail0
    rw [ws_c34_or_ab_inv_0213] at hzout1 hs1
    obtain ⟨z2, r2, hz2, hzout2, hs2, tail2⟩ := step_swap5 2 3 hg hval hz1 hzout1 hs1 tail1
    rw [ws_c34_or_ab_inv_23] at hzout2 hs2
    have hfa : (perm5 (swap 2 3) (perm5 (swap 1 3) (perm5 (swap 0 2) x2))) = x0 := by rw [p_0213_x2, p_23_x0]
    have hfb : (perm5 (swap 2 3) (perm5 (swap 1 3) (perm5 (swap 0 2) x1))) = x2 := by rw [p_0213_x1, p_23_x3]
    rw [hfa, hfb] at hz2 hs2
    exact hstep_sym _ _ z2 r2 (.inr (by simp)) hz2 hzout2 hs2 tail2
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 2 3 hg hval hz hzout hs tail
    rw [ws_c34_or_ab_inv_23] at hzout0 hs0
    have hfa : (perm5 (swap 2 3) x3) = x2 := by rw [p_23_x3]
    have hfb : (perm5 (swap 2 3) x23) = x23 := by rw [p_23_x23]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 2 hg hval hz hzout hs tail
    have hval0 : ∀ w ∈ ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset.image (perm5 (swap 0 2)), Valid5 w := fun w hw => by obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hw; exact perm5_valid 0 2 u
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 1 3 hg hval0 hz0 hzout0 hs0 tail0
    rw [ws_c34_or_ab_inv_0213] at hzout1 hs1
    obtain ⟨z2, r2, hz2, hzout2, hs2, tail2⟩ := step_swap5 0 1 hg hval hz1 hzout1 hs1 tail1
    rw [ws_c34_or_ab_inv_01] at hzout2 hs2
    have hfa : (perm5 (swap 0 1) (perm5 (swap 1 3) (perm5 (swap 0 2) x3))) = x0 := by rw [p_0213_x3, p_01_x1]
    have hfb : (perm5 (swap 0 1) (perm5 (swap 1 3) (perm5 (swap 0 2) x01))) = x23 := by rw [p_0213_x01, p_01_x23]
    rw [hfa, hfb] at hz2 hs2
    exact hstep_sym _ _ z2 r2 (.inr (by simp)) hz2 hzout2 hs2 tail2
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 2 3 hg hval hz hzout hs tail
    rw [ws_c34_or_ab_inv_23] at hzout0 hs0
    have hfa : (perm5 (swap 2 3) x3) = x2 := by rw [p_23_x3]
    have hfb : (perm5 (swap 2 3) x0) = x0 := by rw [p_23_x0]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 2 3 hg hval hz hzout hs tail
    rw [ws_c34_or_ab_inv_23] at hzout0 hs0
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 0 1 hg hval hz0 hzout0 hs0 tail0
    rw [ws_c34_or_ab_inv_01] at hzout1 hs1
    have hfa : (perm5 (swap 0 1) (perm5 (swap 2 3) x3)) = x2 := by rw [p_23_x3, p_01_x2]
    have hfb : (perm5 (swap 0 1) (perm5 (swap 2 3) x1)) = x0 := by rw [p_23_x1, p_01_x1]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inl (by simp)) hz1 hzout1 hs1 tail1
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 2 3 hg hval hz hzout hs tail
    rw [ws_c34_or_ab_inv_23] at hzout0 hs0
    have hfa : (perm5 (swap 2 3) x3) = x2 := by rw [p_23_x3]
    have hfb : (perm5 (swap 2 3) x4) = x4 := by rw [p_23_x4]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 2 hg hval hz hzout hs tail
    have hval0 : ∀ w ∈ ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset.image (perm5 (swap 0 2)), Valid5 w := fun w hw => by obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hw; exact perm5_valid 0 2 u
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 1 3 hg hval0 hz0 hzout0 hs0 tail0
    rw [ws_c34_or_ab_inv_0213] at hzout1 hs1
    have hfa : (perm5 (swap 1 3) (perm5 (swap 0 2) x01)) = x23 := by rw [p_0213_x01]
    have hfb : (perm5 (swap 1 3) (perm5 (swap 0 2) x2)) = x0 := by rw [p_0213_x2]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inl (by simp)) hz1 hzout1 hs1 tail1
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 2 hg hval hz hzout hs tail
    have hval0 : ∀ w ∈ ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset.image (perm5 (swap 0 2)), Valid5 w := fun w hw => by obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hw; exact perm5_valid 0 2 u
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 1 3 hg hval0 hz0 hzout0 hs0 tail0
    rw [ws_c34_or_ab_inv_0213] at hzout1 hs1
    obtain ⟨z2, r2, hz2, hzout2, hs2, tail2⟩ := step_swap5 0 1 hg hval hz1 hzout1 hs1 tail1
    rw [ws_c34_or_ab_inv_01] at hzout2 hs2
    have hfa : (perm5 (swap 0 1) (perm5 (swap 1 3) (perm5 (swap 0 2) x01))) = x23 := by rw [p_0213_x01, p_01_x23]
    have hfb : (perm5 (swap 0 1) (perm5 (swap 1 3) (perm5 (swap 0 2) x3))) = x0 := by rw [p_0213_x3, p_01_x1]
    rw [hfa, hfb] at hz2 hs2
    exact hstep_sym _ _ z2 r2 (.inl (by simp)) hz2 hzout2 hs2 tail2
  · exact hab rfl
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 2 hg hval hz hzout hs tail
    have hval0 : ∀ w ∈ ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset.image (perm5 (swap 0 2)), Valid5 w := fun w hw => by obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hw; exact perm5_valid 0 2 u
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 1 3 hg hval0 hz0 hzout0 hs0 tail0
    rw [ws_c34_or_ab_inv_0213] at hzout1 hs1
    have hfa : (perm5 (swap 1 3) (perm5 (swap 0 2) x01)) = x23 := by rw [p_0213_x01]
    have hfb : (perm5 (swap 1 3) (perm5 (swap 0 2) x0)) = x2 := by rw [p_0213_x0]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inl (by simp)) hz1 hzout1 hs1 tail1
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 2 hg hval hz hzout hs tail
    have hval0 : ∀ w ∈ ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset.image (perm5 (swap 0 2)), Valid5 w := fun w hw => by obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hw; exact perm5_valid 0 2 u
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 1 3 hg hval0 hz0 hzout0 hs0 tail0
    rw [ws_c34_or_ab_inv_0213] at hzout1 hs1
    obtain ⟨z2, r2, hz2, hzout2, hs2, tail2⟩ := step_swap5 2 3 hg hval hz1 hzout1 hs1 tail1
    rw [ws_c34_or_ab_inv_23] at hzout2 hs2
    have hfa : (perm5 (swap 2 3) (perm5 (swap 1 3) (perm5 (swap 0 2) x01))) = x23 := by rw [p_0213_x01, p_23_x23]
    have hfb : (perm5 (swap 2 3) (perm5 (swap 1 3) (perm5 (swap 0 2) x1))) = x2 := by rw [p_0213_x1, p_23_x3]
    rw [hfa, hfb] at hz2 hs2
    exact hstep_sym _ _ z2 r2 (.inl (by simp)) hz2 hzout2 hs2 tail2
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 2 hg hval hz hzout hs tail
    have hval0 : ∀ w ∈ ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset.image (perm5 (swap 0 2)), Valid5 w := fun w hw => by obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hw; exact perm5_valid 0 2 u
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 1 3 hg hval0 hz0 hzout0 hs0 tail0
    rw [ws_c34_or_ab_inv_0213] at hzout1 hs1
    have hfa : (perm5 (swap 1 3) (perm5 (swap 0 2) x01)) = x23 := by rw [p_0213_x01]
    have hfb : (perm5 (swap 1 3) (perm5 (swap 0 2) x4)) = x4 := by rw [p_0213_x4]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inl (by simp)) hz1 hzout1 hs1 tail1
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 2 3 hg hval hz hzout hs tail
    rw [ws_c34_or_ab_inv_23] at hzout0 hs0
    have hfa : (perm5 (swap 2 3) x0) = x0 := by rw [p_23_x0]
    have hfb : (perm5 (swap 2 3) x3) = x2 := by rw [p_23_x3]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 2 hg hval hz hzout hs tail
    have hval0 : ∀ w ∈ ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset.image (perm5 (swap 0 2)), Valid5 w := fun w hw => by obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hw; exact perm5_valid 0 2 u
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 1 3 hg hval0 hz0 hzout0 hs0 tail0
    rw [ws_c34_or_ab_inv_0213] at hzout1 hs1
    have hfa : (perm5 (swap 1 3) (perm5 (swap 0 2) x0)) = x2 := by rw [p_0213_x0]
    have hfb : (perm5 (swap 1 3) (perm5 (swap 0 2) x01)) = x23 := by rw [p_0213_x01]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inr (by simp)) hz1 hzout1 hs1 tail1
  · exact hab rfl
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 2 hg hval hz hzout hs tail
    have hval0 : ∀ w ∈ ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset.image (perm5 (swap 0 2)), Valid5 w := fun w hw => by obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hw; exact perm5_valid 0 2 u
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 1 3 hg hval0 hz0 hzout0 hs0 tail0
    rw [ws_c34_or_ab_inv_0213] at hzout1 hs1
    have hfa : (perm5 (swap 1 3) (perm5 (swap 0 2) x0)) = x2 := by rw [p_0213_x0]
    have hfb : (perm5 (swap 1 3) (perm5 (swap 0 2) x1)) = x3 := by rw [p_0213_x1]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inl (by simp)) hz1 hzout1 hs1 tail1
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 2 hg hval hz hzout hs tail
    have hval0 : ∀ w ∈ ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset.image (perm5 (swap 0 2)), Valid5 w := fun w hw => by obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hw; exact perm5_valid 0 2 u
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 1 3 hg hval0 hz0 hzout0 hs0 tail0
    rw [ws_c34_or_ab_inv_0213] at hzout1 hs1
    have hfa : (perm5 (swap 1 3) (perm5 (swap 0 2) x0)) = x2 := by rw [p_0213_x0]
    have hfb : (perm5 (swap 1 3) (perm5 (swap 0 2) x4)) = x4 := by rw [p_0213_x4]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inl (by simp)) hz1 hzout1 hs1 tail1
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c34_or_ab_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    have hfb : (perm5 (swap 0 1) x23) = x23 := by rw [p_01_x23]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 2 hg hval hz hzout hs tail
    have hval0 : ∀ w ∈ ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset.image (perm5 (swap 0 2)), Valid5 w := fun w hw => by obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hw; exact perm5_valid 0 2 u
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 1 3 hg hval0 hz0 hzout0 hs0 tail0
    rw [ws_c34_or_ab_inv_0213] at hzout1 hs1
    obtain ⟨z2, r2, hz2, hzout2, hs2, tail2⟩ := step_swap5 2 3 hg hval hz1 hzout1 hs1 tail1
    rw [ws_c34_or_ab_inv_23] at hzout2 hs2
    have hfa : (perm5 (swap 2 3) (perm5 (swap 1 3) (perm5 (swap 0 2) x1))) = x2 := by rw [p_0213_x1, p_23_x3]
    have hfb : (perm5 (swap 2 3) (perm5 (swap 1 3) (perm5 (swap 0 2) x2))) = x0 := by rw [p_0213_x2, p_23_x0]
    rw [hfa, hfb] at hz2 hs2
    exact hstep_sym _ _ z2 r2 (.inl (by simp)) hz2 hzout2 hs2 tail2
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 2 3 hg hval hz hzout hs tail
    rw [ws_c34_or_ab_inv_23] at hzout0 hs0
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 0 1 hg hval hz0 hzout0 hs0 tail0
    rw [ws_c34_or_ab_inv_01] at hzout1 hs1
    have hfa : (perm5 (swap 0 1) (perm5 (swap 2 3) x1)) = x0 := by rw [p_23_x1, p_01_x1]
    have hfb : (perm5 (swap 0 1) (perm5 (swap 2 3) x3)) = x2 := by rw [p_23_x3, p_01_x2]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inr (by simp)) hz1 hzout1 hs1 tail1
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 2 hg hval hz hzout hs tail
    have hval0 : ∀ w ∈ ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset.image (perm5 (swap 0 2)), Valid5 w := fun w hw => by obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hw; exact perm5_valid 0 2 u
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 1 3 hg hval0 hz0 hzout0 hs0 tail0
    rw [ws_c34_or_ab_inv_0213] at hzout1 hs1
    obtain ⟨z2, r2, hz2, hzout2, hs2, tail2⟩ := step_swap5 2 3 hg hval hz1 hzout1 hs1 tail1
    rw [ws_c34_or_ab_inv_23] at hzout2 hs2
    have hfa : (perm5 (swap 2 3) (perm5 (swap 1 3) (perm5 (swap 0 2) x1))) = x2 := by rw [p_0213_x1, p_23_x3]
    have hfb : (perm5 (swap 2 3) (perm5 (swap 1 3) (perm5 (swap 0 2) x01))) = x23 := by rw [p_0213_x01, p_23_x23]
    rw [hfa, hfb] at hz2 hs2
    exact hstep_sym _ _ z2 r2 (.inr (by simp)) hz2 hzout2 hs2 tail2
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 2 hg hval hz hzout hs tail
    have hval0 : ∀ w ∈ ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset.image (perm5 (swap 0 2)), Valid5 w := fun w hw => by obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hw; exact perm5_valid 0 2 u
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 1 3 hg hval0 hz0 hzout0 hs0 tail0
    rw [ws_c34_or_ab_inv_0213] at hzout1 hs1
    have hfa : (perm5 (swap 1 3) (perm5 (swap 0 2) x1)) = x3 := by rw [p_0213_x1]
    have hfb : (perm5 (swap 1 3) (perm5 (swap 0 2) x0)) = x2 := by rw [p_0213_x0]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inr (by simp)) hz1 hzout1 hs1 tail1
  · exact hab rfl
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 2 hg hval hz hzout hs tail
    have hval0 : ∀ w ∈ ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset.image (perm5 (swap 0 2)), Valid5 w := fun w hw => by obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hw; exact perm5_valid 0 2 u
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 1 3 hg hval0 hz0 hzout0 hs0 tail0
    rw [ws_c34_or_ab_inv_0213] at hzout1 hs1
    obtain ⟨z2, r2, hz2, hzout2, hs2, tail2⟩ := step_swap5 2 3 hg hval hz1 hzout1 hs1 tail1
    rw [ws_c34_or_ab_inv_23] at hzout2 hs2
    have hfa : (perm5 (swap 2 3) (perm5 (swap 1 3) (perm5 (swap 0 2) x1))) = x2 := by rw [p_0213_x1, p_23_x3]
    have hfb : (perm5 (swap 2 3) (perm5 (swap 1 3) (perm5 (swap 0 2) x4))) = x4 := by rw [p_0213_x4, p_23_x4]
    rw [hfa, hfb] at hz2 hs2
    exact hstep_sym _ _ z2 r2 (.inl (by simp)) hz2 hzout2 hs2 tail2
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 2 3 hg hval hz hzout hs tail
    rw [ws_c34_or_ab_inv_23] at hzout0 hs0
    have hfa : (perm5 (swap 2 3) x4) = x4 := by rw [p_23_x4]
    have hfb : (perm5 (swap 2 3) x3) = x2 := by rw [p_23_x3]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 2 hg hval hz hzout hs tail
    have hval0 : ∀ w ∈ ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset.image (perm5 (swap 0 2)), Valid5 w := fun w hw => by obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hw; exact perm5_valid 0 2 u
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 1 3 hg hval0 hz0 hzout0 hs0 tail0
    rw [ws_c34_or_ab_inv_0213] at hzout1 hs1
    have hfa : (perm5 (swap 1 3) (perm5 (swap 0 2) x4)) = x4 := by rw [p_0213_x4]
    have hfb : (perm5 (swap 1 3) (perm5 (swap 0 2) x01)) = x23 := by rw [p_0213_x01]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inr (by simp)) hz1 hzout1 hs1 tail1
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 2 hg hval hz hzout hs tail
    have hval0 : ∀ w ∈ ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset.image (perm5 (swap 0 2)), Valid5 w := fun w hw => by obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hw; exact perm5_valid 0 2 u
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 1 3 hg hval0 hz0 hzout0 hs0 tail0
    rw [ws_c34_or_ab_inv_0213] at hzout1 hs1
    have hfa : (perm5 (swap 1 3) (perm5 (swap 0 2) x4)) = x4 := by rw [p_0213_x4]
    have hfb : (perm5 (swap 1 3) (perm5 (swap 0 2) x0)) = x2 := by rw [p_0213_x0]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inr (by simp)) hz1 hzout1 hs1 tail1
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 2 hg hval hz hzout hs tail
    have hval0 : ∀ w ∈ ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset.image (perm5 (swap 0 2)), Valid5 w := fun w hw => by obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hw; exact perm5_valid 0 2 u
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 1 3 hg hval0 hz0 hzout0 hs0 tail0
    rw [ws_c34_or_ab_inv_0213] at hzout1 hs1
    obtain ⟨z2, r2, hz2, hzout2, hs2, tail2⟩ := step_swap5 2 3 hg hval hz1 hzout1 hs1 tail1
    rw [ws_c34_or_ab_inv_23] at hzout2 hs2
    have hfa : (perm5 (swap 2 3) (perm5 (swap 1 3) (perm5 (swap 0 2) x4))) = x4 := by rw [p_0213_x4, p_23_x4]
    have hfb : (perm5 (swap 2 3) (perm5 (swap 1 3) (perm5 (swap 0 2) x1))) = x2 := by rw [p_0213_x1, p_23_x3]
    rw [hfa, hfb] at hz2 hs2
    exact hstep_sym _ _ z2 r2 (.inr (by simp)) hz2 hzout2 hs2 tail2
  · exact hab rfl

lemma ws1_nd : ([x01, x0, x1, x2, x3, x4] : List W5).Nodup := by decide +kernel
lemma ws1_valid : ∀ w ∈ ([x01, x0, x1, x2, x3, x4] : List W5), Valid5 w := fun w hw => valid5_of_valid5B ((List.all_eq_true.mp (by decide +kernel : ([x01, x0, x1, x2, x3, x4] : List W5).all valid5B = true)) w hw)
lemma ws1_not_goal : ∀ g : W5, (g = goal5 ∨ g = ~~~goal5) → ([x01, x0, x1, x2, x3, x4] : List W5).toFinset ≠ {g} := by
  intro g _ heq; have hc := congrArg Finset.card heq; rw [List.toFinset_card_of_nodup ws1_nd, Finset.card_singleton] at hc; simp at hc
lemma ws1_inv_01 : ([x01, x0, x1, x2, x3, x4] : List W5).toFinset.image (perm5 (swap 0 1)) = ([x01, x0, x1, x2, x3, x4] : List W5).toFinset := by
  ext w; simp only [List.toFinset_cons, List.toFinset_nil, Finset.image_insert, Finset.image_empty, Finset.mem_insert, Finset.notMem_empty, or_false, p_01_x01, p_01_x0, p_01_x1, p_01_x2, p_01_x3, p_01_x4]; tauto
lemma ws1_inv_23 : ([x01, x0, x1, x2, x3, x4] : List W5).toFinset.image (perm5 (swap 2 3)) = ([x01, x0, x1, x2, x3, x4] : List W5).toFinset := by
  ext w; simp only [List.toFinset_cons, List.toFinset_nil, Finset.image_insert, Finset.image_empty, Finset.mem_insert, Finset.notMem_empty, or_false, p_23_x01, p_23_x0, p_23_x1, p_23_x2, p_23_x3, p_23_x4]; tauto
lemma ws1_inv_24 : ([x01, x0, x1, x2, x3, x4] : List W5).toFinset.image (perm5 (swap 2 4)) = ([x01, x0, x1, x2, x3, x4] : List W5).toFinset := by
  ext w; simp only [List.toFinset_cons, List.toFinset_nil, Finset.image_insert, Finset.image_empty, Finset.mem_insert, Finset.notMem_empty, or_false, p_24_x01, p_24_x0, p_24_x1, p_24_x2, p_24_x3, p_24_x4]; tauto
lemma ws1_inv_34 : ([x01, x0, x1, x2, x3, x4] : List W5).toFinset.image (perm5 (swap 3 4)) = ([x01, x0, x1, x2, x3, x4] : List W5).toFinset := by
  ext w; simp only [List.toFinset_cons, List.toFinset_nil, Finset.image_insert, Finset.image_empty, Finset.mem_insert, Finset.notMem_empty, or_false, p_34_x01, p_34_x0, p_34_x1, p_34_x2, p_34_x3, p_34_x4]; tauto
lemma no_ws1 {g : W5} (hg : g = goal5 ∨ g = ~~~goal5)
    (hl : live basicOps5 g 8 ([x01, x0, x1, x2, x3, x4] : List W5).toFinset)
    (hav : HasAvoid 8 ![1, 1, 0, 0, 0] ([x01, x0, x1, x2, x3, x4] : List W5).toFinset) : False := by
  have hstep : ∀ a b : W5, (a, b) ∈ [(x01, x0), (x01, x2), (x0, x1), (x0, x2), (x2, x3)] →
      ∀ z ∈ basicOps5 a b, z ∉ ([x01, x0, x1, x2, x3, x4] : List W5).toFinset → ∀ rest : Finset W5,
      ([x01, x0, x1, x2, x3, x4] : List W5).toFinset = insert a (insert b rest) →
      live basicOps5 g 7 (insert z rest) → False := by
    intro a b hab z hz hzout rest hs tail
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hab
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hperm : ([x01, x0, x1, x2, x3, x4] : List W5).Perm (x01 :: x0 :: [x1, x2, x3, x4]) := List.Perm.refl _
      obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept5 hperm ws1_nd hs
      have hznew : z ∉ kept := fun hu => hzout (hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu)))
      have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
      have hl' : live basicOps5 g 7 (z :: kept).toFinset := by simpa [hfin] using tail
      have hav' : HasAvoid 7 ![2, 1, 0, 0, 0] (z :: kept).toFinset := by
        have hsub : (z :: kept).toFinset ⊆ insert z ([x01, x0, x1, x2, x3, x4] : List W5).toFinset := by
          intro u hu; rcases Finset.mem_insert.mp (by simpa [hfin] using hu) with rfl | hr
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hr))
        have hstep_av := hasAvoid_step (k := 7) hav (List.mem_toFinset.mpr (by simp)) (List.mem_toFinset.mpr (by simp)) hz hsub
        have hseq : (fun i : Fin 5 => (![1, 1, 0, 0, 0] : Fin 5 → ℕ) i + if isC (mask5 i).toNat x01.toNat || isC (mask5 i).toNat x0.toNat then 1 else 0) = ![2, 1, 0, 0, 0] := by
          funext i; fin_cases i <;> decide +kernel
        rwa [hseq] at hstep_av
      simp only [basicOps5, ops5, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
      simp only [keepChoices5, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hz with rfl | rfl | rfl | rfl <;> rcases hk with rfl | rfl | rfl | rfl
      · exact hzout (List.mem_toFinset.mpr (by decide))
      · exact hzout (List.mem_toFinset.mpr (by decide))
      · exact hzout (List.mem_toFinset.mpr (by decide))
      · exact hzout (List.mem_toFinset.mpr (by decide))
      · exact hzout (List.mem_toFinset.mpr (by decide))
      · exact hzout (List.mem_toFinset.mpr (by decide))
      · exact hzout (List.mem_toFinset.mpr (by decide))
      · exact hzout (List.mem_toFinset.mpr (by decide))
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
    · have hperm : ([x01, x0, x1, x2, x3, x4] : List W5).Perm (x01 :: x2 :: [x0, x1, x3, x4]) := (List.perm_middle (l₁ := [x0, x1]) (a := x2) (l₂ := [x3, x4])).cons x01
      obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept5 hperm ws1_nd hs
      have hznew : z ∉ kept := fun hu => hzout (hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu)))
      have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
      have hl' : live basicOps5 g 7 (z :: kept).toFinset := by simpa [hfin] using tail
      have hav' : HasAvoid 7 ![1, 1, 1, 0, 0] (z :: kept).toFinset := by
        have hsub : (z :: kept).toFinset ⊆ insert z ([x01, x0, x1, x2, x3, x4] : List W5).toFinset := by
          intro u hu; rcases Finset.mem_insert.mp (by simpa [hfin] using hu) with rfl | hr
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hr))
        have hstep_av := hasAvoid_step (k := 7) hav (List.mem_toFinset.mpr (by simp)) (List.mem_toFinset.mpr (by simp)) hz hsub
        have hseq : (fun i : Fin 5 => (![1, 1, 0, 0, 0] : Fin 5 → ℕ) i + if isC (mask5 i).toNat x01.toNat || isC (mask5 i).toNat x2.toNat then 1 else 0) = ![1, 1, 1, 0, 0] := by
          funext i; fin_cases i <;> decide +kernel
        rwa [hseq] at hstep_av
      simp only [basicOps5, ops5, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
      simp only [keepChoices5, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hz with rfl | rfl | rfl | rfl <;> rcases hk with rfl | rfl | rfl | rfl
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact no_c03_or_b hg hl' hav'
      · exact no_c03_or_ab hg hl' hav'
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact no_c03_an_b hg hl' hav'
      · exact no_c03_an_ab hg hl' hav'
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
    · have hperm : ([x01, x0, x1, x2, x3, x4] : List W5).Perm (x0 :: x1 :: [x01, x2, x3, x4]) := (List.perm_middle (l₁ := [x01]) (a := x0) (l₂ := [x1, x2, x3, x4])).trans ((List.perm_middle (l₁ := [x01]) (a := x1) (l₂ := [x2, x3, x4])).cons x0)
      obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept5 hperm ws1_nd hs
      have hznew : z ∉ kept := fun hu => hzout (hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu)))
      have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
      have hl' : live basicOps5 g 7 (z :: kept).toFinset := by simpa [hfin] using tail
      have hav' : HasAvoid 7 ![2, 2, 0, 0, 0] (z :: kept).toFinset := by
        have hsub : (z :: kept).toFinset ⊆ insert z ([x01, x0, x1, x2, x3, x4] : List W5).toFinset := by
          intro u hu; rcases Finset.mem_insert.mp (by simpa [hfin] using hu) with rfl | hr
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hr))
        have hstep_av := hasAvoid_step (k := 7) hav (List.mem_toFinset.mpr (by simp)) (List.mem_toFinset.mpr (by simp)) hz hsub
        have hseq : (fun i : Fin 5 => (![1, 1, 0, 0, 0] : Fin 5 → ℕ) i + if isC (mask5 i).toNat x0.toNat || isC (mask5 i).toNat x1.toNat then 1 else 0) = ![2, 2, 0, 0, 0] := by
          funext i; fin_cases i <;> decide +kernel
        rwa [hseq] at hstep_av
      simp only [basicOps5, ops5, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
      simp only [keepChoices5, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hz with rfl | rfl | rfl | rfl <;> rcases hk with rfl | rfl | rfl | rfl
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
      · exact hzout (List.mem_toFinset.mpr (by decide))
      · exact hzout (List.mem_toFinset.mpr (by decide))
      · exact hzout (List.mem_toFinset.mpr (by decide))
      · exact hzout (List.mem_toFinset.mpr (by decide))
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
    · have hperm : ([x01, x0, x1, x2, x3, x4] : List W5).Perm (x0 :: x2 :: [x01, x1, x3, x4]) := (List.perm_middle (l₁ := [x01]) (a := x0) (l₂ := [x1, x2, x3, x4])).trans ((List.perm_middle (l₁ := [x01, x1]) (a := x2) (l₂ := [x3, x4])).cons x0)
      obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept5 hperm ws1_nd hs
      have hznew : z ∉ kept := fun hu => hzout (hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu)))
      have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
      have hl' : live basicOps5 g 7 (z :: kept).toFinset := by simpa [hfin] using tail
      have hav' : HasAvoid 7 ![2, 1, 1, 0, 0] (z :: kept).toFinset := by
        have hsub : (z :: kept).toFinset ⊆ insert z ([x01, x0, x1, x2, x3, x4] : List W5).toFinset := by
          intro u hu; rcases Finset.mem_insert.mp (by simpa [hfin] using hu) with rfl | hr
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hr))
        have hstep_av := hasAvoid_step (k := 7) hav (List.mem_toFinset.mpr (by simp)) (List.mem_toFinset.mpr (by simp)) hz hsub
        have hseq : (fun i : Fin 5 => (![1, 1, 0, 0, 0] : Fin 5 → ℕ) i + if isC (mask5 i).toNat x0.toNat || isC (mask5 i).toNat x2.toNat then 1 else 0) = ![2, 1, 1, 0, 0] := by
          funext i; fin_cases i <;> decide +kernel
        rwa [hseq] at hstep_av
      simp only [basicOps5, ops5, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
      simp only [keepChoices5, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hz with rfl | rfl | rfl | rfl <;> rcases hk with rfl | rfl | rfl | rfl
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact no_c13_or_b hg hl' hav'
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
    · have hperm : ([x01, x0, x1, x2, x3, x4] : List W5).Perm (x2 :: x3 :: [x01, x0, x1, x4]) := (List.perm_middle (l₁ := [x01, x0, x1]) (a := x2) (l₂ := [x3, x4])).trans ((List.perm_middle (l₁ := [x01, x0, x1]) (a := x3) (l₂ := [x4])).cons x2)
      obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept5 hperm ws1_nd hs
      have hznew : z ∉ kept := fun hu => hzout (hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu)))
      have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
      have hl' : live basicOps5 g 7 (z :: kept).toFinset := by simpa [hfin] using tail
      have hav' : HasAvoid 7 ![1, 1, 1, 1, 0] (z :: kept).toFinset := by
        have hsub : (z :: kept).toFinset ⊆ insert z ([x01, x0, x1, x2, x3, x4] : List W5).toFinset := by
          intro u hu; rcases Finset.mem_insert.mp (by simpa [hfin] using hu) with rfl | hr
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hr))
        have hstep_av := hasAvoid_step (k := 7) hav (List.mem_toFinset.mpr (by simp)) (List.mem_toFinset.mpr (by simp)) hz hsub
        have hseq : (fun i : Fin 5 => (![1, 1, 0, 0, 0] : Fin 5 → ℕ) i + if isC (mask5 i).toNat x2.toNat || isC (mask5 i).toNat x3.toNat then 1 else 0) = ![1, 1, 1, 1, 0] := by
          funext i; fin_cases i <;> decide +kernel
        rwa [hseq] at hstep_av
      simp only [basicOps5, ops5, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
      simp only [keepChoices5, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hz with rfl | rfl | rfl | rfl <;> rcases hk with rfl | rfl | rfl | rfl
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact no_c34_or_ab hg hl' hav'
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
  rcases first_live (k := 7) hl with hend | ⟨a, ha, b, hb, hab, z, hz, hzout, rest, hs, tail⟩
  · exact ws1_not_goal g hg hend
  have hval : ∀ w ∈ ([x01, x0, x1, x2, x3, x4] : List W5).toFinset, Valid5 w := fun w hw => ws1_valid w (List.mem_toFinset.mp hw)
  have ha' : a ∈ ([x01, x0, x1, x2, x3, x4] : List W5) := List.mem_toFinset.mp ha
  have hb' : b ∈ ([x01, x0, x1, x2, x3, x4] : List W5) := List.mem_toFinset.mp hb
  have hstep_sym : ∀ (u v : W5) (z' : W5) (rest' : Finset W5),
      (u, v) ∈ [(x01, x0), (x01, x2), (x0, x1), (x0, x2), (x2, x3)] ∨ (v, u) ∈ [(x01, x0), (x01, x2), (x0, x1), (x0, x2), (x2, x3)] →
      z' ∈ basicOps5 u v → z' ∉ ([x01, x0, x1, x2, x3, x4] : List W5).toFinset →
      ([x01, x0, x1, x2, x3, x4] : List W5).toFinset = insert u (insert v rest') →
      live basicOps5 g 7 (insert z' rest') → False := by
    intro u v z' rest' huv hz' hzout' hs' tail'
    rcases huv with h | h
    · exact hstep u v h z' hz' hzout' rest' hs' tail'
    · exact hstep v u h z' (ops5_swap u v ▸ hz') hzout' rest' (by rw [hs', Finset.insert_comm]) tail'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha' hb'
  rcases ha' with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws1_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x01) = x01 := by rw [p_01_x01]
    have hfb : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 2 3 hg hval hz hzout hs tail
    rw [ws1_inv_23] at hzout0 hs0
    have hfa : (perm5 (swap 2 3) x01) = x01 := by rw [p_23_x01]
    have hfb : (perm5 (swap 2 3) x3) = x2 := by rw [p_23_x3]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 2 4 hg hval hz hzout hs tail
    rw [ws1_inv_24] at hzout0 hs0
    have hfa : (perm5 (swap 2 4) x01) = x01 := by rw [p_24_x01]
    have hfb : (perm5 (swap 2 4) x4) = x2 := by rw [p_24_x4]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 2 3 hg hval hz hzout hs tail
    rw [ws1_inv_23] at hzout0 hs0
    have hfa : (perm5 (swap 2 3) x0) = x0 := by rw [p_23_x0]
    have hfb : (perm5 (swap 2 3) x3) = x2 := by rw [p_23_x3]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 2 4 hg hval hz hzout hs tail
    rw [ws1_inv_24] at hzout0 hs0
    have hfa : (perm5 (swap 2 4) x0) = x0 := by rw [p_24_x0]
    have hfb : (perm5 (swap 2 4) x4) = x2 := by rw [p_24_x4]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws1_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    have hfb : (perm5 (swap 0 1) x01) = x01 := by rw [p_01_x01]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws1_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    have hfb : (perm5 (swap 0 1) x2) = x2 := by rw [p_01_x2]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 2 3 hg hval hz hzout hs tail
    rw [ws1_inv_23] at hzout0 hs0
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 0 1 hg hval hz0 hzout0 hs0 tail0
    rw [ws1_inv_01] at hzout1 hs1
    have hfa : (perm5 (swap 0 1) (perm5 (swap 2 3) x1)) = x0 := by rw [p_23_x1, p_01_x1]
    have hfb : (perm5 (swap 0 1) (perm5 (swap 2 3) x3)) = x2 := by rw [p_23_x3, p_01_x2]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inl (by simp)) hz1 hzout1 hs1 tail1
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 2 4 hg hval hz hzout hs tail
    rw [ws1_inv_24] at hzout0 hs0
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 0 1 hg hval hz0 hzout0 hs0 tail0
    rw [ws1_inv_01] at hzout1 hs1
    have hfa : (perm5 (swap 0 1) (perm5 (swap 2 4) x1)) = x0 := by rw [p_24_x1, p_01_x1]
    have hfb : (perm5 (swap 0 1) (perm5 (swap 2 4) x4)) = x2 := by rw [p_24_x4, p_01_x2]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inl (by simp)) hz1 hzout1 hs1 tail1
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws1_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x2) = x2 := by rw [p_01_x2]
    have hfb : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws1_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x2) = x2 := by rw [p_34_x2]
    have hfb : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 2 3 hg hval hz hzout hs tail
    rw [ws1_inv_23] at hzout0 hs0
    have hfa : (perm5 (swap 2 3) x3) = x2 := by rw [p_23_x3]
    have hfb : (perm5 (swap 2 3) x01) = x01 := by rw [p_23_x01]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 2 3 hg hval hz hzout hs tail
    rw [ws1_inv_23] at hzout0 hs0
    have hfa : (perm5 (swap 2 3) x3) = x2 := by rw [p_23_x3]
    have hfb : (perm5 (swap 2 3) x0) = x0 := by rw [p_23_x0]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 2 3 hg hval hz hzout hs tail
    rw [ws1_inv_23] at hzout0 hs0
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 0 1 hg hval hz0 hzout0 hs0 tail0
    rw [ws1_inv_01] at hzout1 hs1
    have hfa : (perm5 (swap 0 1) (perm5 (swap 2 3) x3)) = x2 := by rw [p_23_x3, p_01_x2]
    have hfb : (perm5 (swap 0 1) (perm5 (swap 2 3) x1)) = x0 := by rw [p_23_x1, p_01_x1]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inr (by simp)) hz1 hzout1 hs1 tail1
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 2 4 hg hval hz hzout hs tail
    rw [ws1_inv_24] at hzout0 hs0
    have hfa : (perm5 (swap 2 4) x3) = x3 := by rw [p_24_x3]
    have hfb : (perm5 (swap 2 4) x4) = x2 := by rw [p_24_x4]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 2 4 hg hval hz hzout hs tail
    rw [ws1_inv_24] at hzout0 hs0
    have hfa : (perm5 (swap 2 4) x4) = x2 := by rw [p_24_x4]
    have hfb : (perm5 (swap 2 4) x01) = x01 := by rw [p_24_x01]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 2 4 hg hval hz hzout hs tail
    rw [ws1_inv_24] at hzout0 hs0
    have hfa : (perm5 (swap 2 4) x4) = x2 := by rw [p_24_x4]
    have hfb : (perm5 (swap 2 4) x0) = x0 := by rw [p_24_x0]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 2 4 hg hval hz hzout hs tail
    rw [ws1_inv_24] at hzout0 hs0
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 0 1 hg hval hz0 hzout0 hs0 tail0
    rw [ws1_inv_01] at hzout1 hs1
    have hfa : (perm5 (swap 0 1) (perm5 (swap 2 4) x4)) = x2 := by rw [p_24_x4, p_01_x2]
    have hfb : (perm5 (swap 0 1) (perm5 (swap 2 4) x1)) = x0 := by rw [p_24_x1, p_01_x1]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inr (by simp)) hz1 hzout1 hs1 tail1
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws1_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    have hfb : (perm5 (swap 3 4) x2) = x2 := by rw [p_34_x2]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 2 4 hg hval hz hzout hs tail
    rw [ws1_inv_24] at hzout0 hs0
    have hfa : (perm5 (swap 2 4) x4) = x2 := by rw [p_24_x4]
    have hfb : (perm5 (swap 2 4) x3) = x3 := by rw [p_24_x3]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hab rfl

lemma in5_valid : ∀ w ∈ in5, Valid5 w := fun w hw => valid5_of_valid5B ((List.all_eq_true.mp (by decide +kernel : in5.all valid5B = true)) w hw)

lemma in5_not_goal : ∀ i : Fin 5, vinput5 i ≠ goal5 ∧ vinput5 i ≠ ~~~goal5 := by decide +kernel

lemma in5_index : ∀ w ∈ in5, ∃ i : Fin 5, vinput5 i = w := by
  intro w hw
  simp only [in5, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩

lemma sep_after_01 : ∀ (op : Fin 4) (q : Fin 5), ∃ p : Fin 76,
    ¬ differs5 p ((ops5 x0 x1).getD op.val 0) ∧
    ∀ r : Fin 5, r ≠ q → ¬ differs5 p (vinput5 r) := by
  unfold differs5; decide +kernel

lemma live_after_01 {g : W5} (hg : g = goal5 ∨ g = ~~~goal5) {z : W5}
    (hz : z ∈ basicOps5 x0 x1) {rest : Finset W5} (hsub : rest ⊆ in5.toFinset)
    (hl : live basicOps5 g 8 (insert z rest)) : ∀ q : Fin 5, vinput5 q ∈ rest := by
  intro q
  have ⟨o, ho⟩ : ∃ o : Fin 4, (ops5 x0 x1).getD o.val 0 = z := by
    simp only [basicOps5, ops5, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  obtain ⟨p, hpz, hpr⟩ := sep_after_01 o q
  rw [ho] at hpz
  have hdg : ∀ r : Fin 76, differs5 r g := by rcases hg with rfl | rfl <;> unfold differs5 <;> decide +kernel
  obtain ⟨w, hw, hdw⟩ := live_separates (differs5 p) (hdg p) (ops5_differs p) hl
  rcases Finset.mem_insert.mp hw with rfl | hwr
  · exact False.elim (hpz hdw)
  · obtain ⟨r, rfl⟩ := in5_index w (List.mem_toFinset.mp (hsub hwr))
    by_cases hrq : r = q
    · subst hrq; exact hwr
    · exact False.elim (hpr r hrq hdw)

theorem no_nine_k5_01 {g : W5} (hg : g = goal5 ∨ g = ~~~goal5) {s rest : Finset W5}
    (hsub : s ⊆ in5.toFinset) {z : W5} (hz : z ∈ basicOps5 x0 x1)
    (hs : s = insert x0 (insert x1 rest)) (tail : live basicOps5 g 8 (insert z rest)) : False := by
  have hrest_sub : rest ⊆ in5.toFinset := fun u hu => hsub (hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu))
  have hall := live_after_01 hg hz hrest_sub tail
  have hrest_eq : rest = in5.toFinset := by
    apply Finset.Subset.antisymm hrest_sub
    intro w hw
    obtain ⟨q, rfl⟩ := in5_index w (List.mem_toFinset.mp hw)
    exact hall q
  rw [hrest_eq] at tail
  have hav0 : HasAvoid 9 (fun _ => 0) in5.toFinset := hasAvoid_init (Finset.Subset.refl _)
  have hav1 := hasAvoid_step (k := 8) hav0 (List.mem_toFinset.mpr (by simp [in5])) (List.mem_toFinset.mpr (by simp [in5]))
    hz (Finset.Subset.refl _)
  have hseq : (fun i : Fin 5 => (0 : ℕ) + if isC (mask5 i).toNat x0.toNat || isC (mask5 i).toNat x1.toNat then 1 else 0) = ![1, 1, 0, 0, 0] := by
    funext i; fin_cases i <;> decide +kernel
  rw [hseq] at hav1
  simp only [basicOps5, ops5, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · have hnd : ((x0 &&& x1) :: in5).Nodup := by decide +kernel
    have hl' : live basicOps5 g 8 ((x0 &&& x1) :: in5).toFinset := by simpa using tail
    have hav' : HasAvoid 8 ![1, 1, 0, 0, 0] ((x0 &&& x1) :: in5).toFinset := by simpa using hav1
    exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
  · have heq : insert (x0 ||| x1) in5.toFinset = ([x01, x0, x1, x2, x3, x4] : List W5).toFinset := by
      simp [in5, x01]
    rw [heq] at tail hav1
    exact no_ws1 hg tail hav1
  · have hnd : ((x0 &&& ~~~x1) :: in5).Nodup := by decide +kernel
    have hl' : live basicOps5 g 8 ((x0 &&& ~~~x1) :: in5).toFinset := by simpa using tail
    have hav' : HasAvoid 8 ![1, 1, 0, 0, 0] ((x0 &&& ~~~x1) :: in5).toFinset := by simpa using hav1
    exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
  · have hnd : ((x1 &&& ~~~x0) :: in5).Nodup := by decide +kernel
    have hl' : live basicOps5 g 8 ((x1 &&& ~~~x0) :: in5).toFinset := by simpa using tail
    have hav' : HasAvoid 8 ![1, 1, 0, 0, 0] ((x1 &&& ~~~x0) :: in5).toFinset := by simpa using hav1
    exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)

lemma in5_image_swap (a b : Fin 5) {s : Finset W5} (hsub : s ⊆ in5.toFinset) :
    s.image (perm5 (swap a b)) ⊆ in5.toFinset := by
  intro w hw
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨i, rfl⟩ := in5_index u (List.mem_toFinset.mp (hsub hu))
  rw [perm5_swap_in]
  generalize swap a b i = j
  fin_cases j <;> exact List.mem_toFinset.mpr (by simp [in5, vinput5])

theorem no_nine_binary (t : W5) (ht : t = goal5 ∨ t = ~~~goal5)
    (run : build basicOps5 t 9 in5.toFinset) : False := by
  obtain ⟨s, hs, hl⟩ := compress run
  rcases first_live (k := 8) hl with endcase | ⟨a, ha, b, hb, hab, z, hz, hzout, rest, he, tail⟩
  · have tx : t ∈ s := by simp [endcase]
    obtain ⟨i, hi⟩ := in5_index _ (List.mem_toFinset.mp (hs tx))
    rcases ht with rfl | rfl
    · exact (in5_not_goal i).1 hi
    · exact (in5_not_goal i).2 hi
  · obtain ⟨i, rfl⟩ := in5_index _ (List.mem_toFinset.mp (hs ha))
    obtain ⟨j, rfl⟩ := in5_index _ (List.mem_toFinset.mp (hs hb))
    have hij : i ≠ j := fun eq => hab (congrArg vinput5 eq)
    have hval : ∀ w ∈ s, Valid5 w := fun w hw => in5_valid w (List.mem_toFinset.mp (hs hw))
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 i 0 ht hval hz hzout he tail
    rw [perm5_swap_in, perm5_swap_in] at hz1 hs1
    have hsi : swap i 0 i = 0 := by simp [swap]
    rw [hsi] at hz1 hs1
    have hsub1 : s.image (perm5 (swap i 0)) ⊆ in5.toFinset := in5_image_swap i 0 hs
    have hval1 : ∀ w ∈ s.image (perm5 (swap i 0)), Valid5 w := fun w hw => in5_valid w (List.mem_toFinset.mp (hsub1 hw))
    let j1 := swap i 0 j
    have hj1_ne0 : j1 ≠ 0 := by
      intro h0
      have hinv : swap i 0 j1 = swap i 0 0 := congrArg (swap i 0) h0
      have hj1_inv : swap i 0 (swap i 0 j) = j := by simp [swap]; split_ifs <;> grind
      have h0_inv : swap i 0 0 = i := by simp [swap]
      exact hij (h0_inv.symm.trans (hinv.symm.trans hj1_inv))
    obtain ⟨z2, r2, hz2, _, hs2, tail2⟩ := step_swap5 j1 1 ht hval1 hz1 hzout1 hs1 tail1
    rw [perm5_swap_in, perm5_swap_in] at hz2 hs2
    have hs0 : swap j1 1 0 = 0 := by
      simp [swap, Ne.symm hj1_ne0]
    have hsj1 : swap j1 1 j1 = 1 := by simp [swap]
    rw [hs0, hsj1] at hz2 hs2
    exact no_nine_k5_01 ht (in5_image_swap j1 1 hsub1) hz2 hs2 tail2

theorem ten_binary (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = table x) :
    9 < binaryCost gs := by
  by_contra hlow
  have low : binaryCost gs ≤ 9 := by omega
  have init : ∀ u ∈ in5, holds5 in5.toFinset u := fun u hu =>
    .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 152) :
      (gs.foldl step (in5.map (bit k))).getD o false = bit k goal5 := by
    have same : List.ofFn (fun i : Fin 5 => bit k (in5.getD i.val 0)) =
        in5.map (bit k) := by
      apply List.ext_getElem (by simp [in5])
      intro i hi hj
      have hlt : i < in5.length := by simpa using hj
      simp only [List.getElem_ofFn, List.getElem_map, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs, o⟩ (in5.map (bit k)) = bit k goal5
    rw [← same, he]
    exact spec_k5 k
  obtain ⟨t, ht, run⟩ := compile gs o hg in5 in5.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps5 t a in5.toFinset) :
      build basicOps5 t b in5.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact no_nine_binary t ht (lift low run)

def rcStep (nOut : ℕ) (st : List Gate × List (Bool ⊕ ℕ)) (g : Gate) : List Gate × List (Bool ⊕ ℕ) :=
  let out := st.1
  let env := st.2
  match g.op with
  | GateOp.not =>
    match g.inputs with
    | [] => (out, env ++ [Sum.inl true])
    | i :: _ =>
      match env.getD i (Sum.inl false) with
      | Sum.inl b => (out, env ++ [Sum.inl (!b)])
      | Sum.inr w' => (out ++ [{ op := GateOp.not, inputs := [w'] }], env ++ [Sum.inr (nOut + out.length)])
  | GateOp.and =>
    if g.inputs.any (fun i => match env.getD i (Sum.inl false) with | Sum.inl false => true | _ => false) then
      (out, env ++ [Sum.inl false])
    else
      let ws' := g.inputs.filterMap (fun i => match env.getD i (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none)
      match ws' with
      | [] => (out, env ++ [Sum.inl true])
      | [w'] => (out, env ++ [Sum.inr w'])
      | _ => (out ++ [{ op := GateOp.and, inputs := ws' }], env ++ [Sum.inr (nOut + out.length)])
  | GateOp.or =>
    if g.inputs.any (fun i => match env.getD i (Sum.inl false) with | Sum.inl true => true | _ => false) then
      (out, env ++ [Sum.inl true])
    else
      let ws' := g.inputs.filterMap (fun i => match env.getD i (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none)
      match ws' with
      | [] => (out, env ++ [Sum.inl false])
      | [w'] => (out, env ++ [Sum.inr w'])
      | _ => (out ++ [{ op := GateOp.or, inputs := ws' }], env ++ [Sum.inr (nOut + out.length)])
  | _ => (out, env ++ [Sum.inl false])

def rcCircuit (nOut : ℕ) (env0 : List (Bool ⊕ ℕ)) (gs : List Gate) (o : ℕ) : List Gate × ℕ :=
  let res := gs.foldl (rcStep nOut) ([], env0)
  match res.2.getD o (Sum.inl false) with
  | Sum.inr w' => (res.1, w')
  | Sum.inl false => (res.1, nOut + res.1.length)
  | Sum.inl true => (res.1 ++ [{ op := GateOp.not, inputs := [] }], nOut + res.1.length)

lemma list_filterMap_len_le {α β : Type} (f : α → Option β) (l : List α) :
    (l.filterMap f).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons a t ih => cases h : f a <;> simp [h] <;> omega

lemma list_filterMap_len_lt {α β : Type} (f : α → Option β) (l : List α)
    (x : α) (hx : x ∈ l) (hnone : f x = none) :
    (l.filterMap f).length < l.length := by
  induction l with
  | nil => cases hx
  | cons a t ih =>
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hxt
    · simp only [List.filterMap_cons, hnone, List.length_cons]
      have := list_filterMap_len_le f t; omega
    · have hlt := ih hxt
      cases h : f a with
      | none => simp only [List.filterMap_cons, h, List.length_cons]; omega
      | some b => simp only [List.filterMap_cons, h, List.length_cons]; omega

lemma wfold_len (gs : List Gate) (xs : List Bool) :
    (gs.foldl step xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp
  | cons g rest ih =>
    simp only [List.foldl_cons, List.length_cons, ih, step, List.length_append, List.length_nil]; omega

lemma rcStep_env_len (nOut : ℕ) (st : List Gate × List (Bool ⊕ ℕ)) (g : Gate) :
    (rcStep nOut st g).2.length = st.2.length + 1 := by
  rcases st with ⟨out, env⟩
  cases h : g.op
  · simp only [rcStep, h]; split_ifs
    · simp
    · cases g.inputs.filterMap _ with
      | nil => simp
      | cons a t => cases t <;> simp
  · simp only [rcStep, h]; split_ifs
    · simp
    · cases g.inputs.filterMap _ with
      | nil => simp
      | cons a t => cases t <;> simp
  · simp only [rcStep, h]
    cases g.inputs with
    | nil => simp
    | cons i _ =>
      dsimp only
      cases env.getD i (Sum.inl false) <;> simp
  · simp [rcStep, h]
  · simp [rcStep, h]

lemma rcStep_legal (nOut : ℕ) (st : List Gate × List (Bool ⊕ ℕ)) (g : Gate)
    (h1 : ∀ g' ∈ st.1, legal g') (hg : legal g) :
    ∀ g' ∈ (rcStep nOut st g).1, legal g' := by
  rcases st with ⟨out, env⟩
  dsimp only at h1 ⊢
  obtain ⟨hop, hlen⟩ := hg
  change g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not at hop
  rcases hop with hop | hop | hop
  · simp only [rcStep, hop]
    split_ifs
    · exact h1
    · cases hins : g.inputs.filterMap _ with
      | nil => exact h1
      | cons a t =>
        cases t with
        | nil => exact h1
        | cons b t2 =>
          intro g' hg'
          simp only [List.mem_append, List.mem_singleton] at hg'
          rcases hg' with h | rfl
          · exact h1 g' h
          · have hl := list_filterMap_len_le (fun i => match env.getD i (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none) g.inputs
            rw [hins] at hl
            exact ⟨by simp, hl.trans hlen⟩
  · simp only [rcStep, hop]
    split_ifs
    · exact h1
    · cases hins : g.inputs.filterMap _ with
      | nil => exact h1
      | cons a t =>
        cases t with
        | nil => exact h1
        | cons b t2 =>
          intro g' hg'
          simp only [List.mem_append, List.mem_singleton] at hg'
          rcases hg' with h | rfl
          · exact h1 g' h
          · have hl := list_filterMap_len_le (fun i => match env.getD i (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none) g.inputs
            rw [hins] at hl
            exact ⟨by simp, hl.trans hlen⟩
  · simp only [rcStep, hop]
    cases g.inputs with
    | nil => exact h1
    | cons i _ =>
      dsimp only
      cases env.getD i (Sum.inl false) with
      | inl b => exact h1
      | inr w' =>
        intro g' hg'
        simp only [List.mem_append, List.mem_singleton] at hg'
        rcases hg' with h | rfl
        · exact h1 g' h
        · exact ⟨by simp, by simp⟩

lemma rcFold_legal (nOut : ℕ) (gs : List Gate) (st : List Gate × List (Bool ⊕ ℕ))
    (h1 : ∀ g' ∈ st.1, legal g') (hM : ∀ g ∈ gs, legal g) :
    ∀ g' ∈ (gs.foldl (rcStep nOut) st).1, legal g' := by
  induction gs generalizing st with
  | nil => exact h1
  | cons g rest ih =>
    simp only [List.foldl_cons]
    exact ih (rcStep nOut st g) (rcStep_legal nOut st g h1 (hM g List.mem_cons_self))
      (fun g' hg' => hM g' (List.mem_cons_of_mem _ hg'))

lemma binaryCost_append_one (gs : List Gate) (g : Gate) :
    binaryCost (gs ++ [g]) = binaryCost gs + (if isBinary g then 1 else 0) := by
  unfold binaryCost
  rw [List.filter_append, List.length_append, List.filter_cons, List.filter_nil]
  cases isBinary g <;> simp

lemma rcStep_binCost_le (nOut : ℕ) (st : List Gate × List (Bool ⊕ ℕ)) (g : Gate) :
    binaryCost (rcStep nOut st g).1 ≤ binaryCost st.1 + (if isBinary g then 1 else 0) := by
  rcases st with ⟨out, env⟩
  dsimp only
  cases h : g.op
  · simp only [rcStep, h, isBinary, ite_true]
    split_ifs
    · dsimp only; omega
    · cases g.inputs.filterMap _ with
      | nil => dsimp only; omega
      | cons a t =>
        cases t with
        | nil => dsimp only; omega
        | cons b t2 => dsimp only; rw [binaryCost_append_one]; simp [isBinary]
  · simp only [rcStep, h, isBinary, ite_true]
    split_ifs
    · dsimp only; omega
    · cases g.inputs.filterMap _ with
      | nil => dsimp only; omega
      | cons a t =>
        cases t with
        | nil => dsimp only; omega
        | cons b t2 => dsimp only; rw [binaryCost_append_one]; simp [isBinary]
  · simp only [rcStep, h, isBinary, Bool.false_eq_true, ite_false, Nat.add_zero]
    cases g.inputs with
    | nil => dsimp only; exact le_refl _
    | cons i _ =>
      dsimp only
      cases env.getD i (Sum.inl false) with
      | inl b => dsimp only; exact le_refl _
      | inr w' => dsimp only; rw [binaryCost_append_one]; simp [isBinary]
  · simp [rcStep, h, isBinary]
  · simp [rcStep, h, isBinary]

lemma rcFold_binCost_le (nOut : ℕ) (gs : List Gate) (st : List Gate × List (Bool ⊕ ℕ)) :
    binaryCost (gs.foldl (rcStep nOut) st).1 ≤ binaryCost st.1 + binaryCost gs := by
  induction gs generalizing st with
  | nil => simp [binaryCost]
  | cons g rest ih =>
    simp only [List.foldl_cons]
    have h1 := ih (rcStep nOut st g)
    have h2 := rcStep_binCost_le nOut st g
    have h3 : binaryCost (g :: rest) = binaryCost rest + (if isBinary g then 1 else 0) := by
      unfold binaryCost; rw [List.filter_cons]; cases isBinary g <;> simp
    omega

lemma rcFold_eval_inv (nOut : ℕ) (gs : List Gate) (ys : List Bool) (hyl : ys.length = nOut)
    (hM : ∀ g ∈ gs, legal g) (ws : List Bool) (st : List Gate × List (Bool ⊕ ℕ))
    (hlen_ws : ws.length = st.2.length)
    (hinv : ∀ i, match st.2.getD i (Sum.inl false) with
      | Sum.inl b => ws.getD i false = b
      | Sum.inr w' => w' < nOut + st.1.length ∧ ws.getD i false = (st.1.foldl step ys).getD w' false) :
    let ws' := gs.foldl step ws
    let st' := gs.foldl (rcStep nOut) st
    ws'.length = st'.2.length ∧
    ∀ i, match st'.2.getD i (Sum.inl false) with
      | Sum.inl b => ws'.getD i false = b
      | Sum.inr w' => w' < nOut + st'.1.length ∧ ws'.getD i false = (st'.1.foldl step ys).getD w' false := by
  induction gs generalizing ws st with
  | nil => exact ⟨hlen_ws, hinv⟩
  | cons g rest ih =>
    simp only [List.foldl_cons]
    have hg := hM g List.mem_cons_self
    rcases st with ⟨out, env⟩
    dsimp only at hlen_ws hinv
    have hws'_len : (step ws g).length = env.length + 1 := by simp [step, hlen_ws]
    have hget_old : ∀ i < env.length, (step ws g).getD i false = ws.getD i false := fun i hi => by
      rw [List.getD_eq_getElem _ _ (by simp [step]; omega), List.getD_eq_getElem _ _ (by omega)]
      simp [step, List.getElem_append_left (by omega : i < ws.length)]
    have hget_last : (step ws g).getD env.length false = g.op.eval (g.inputs.map fun i => ws.getD i false) := by
      rw [← hlen_ws, List.getD_eq_getElem _ _ (by simp [step])]; simp [step]
    have hget_hi : ∀ i, env.length + 1 ≤ i → (step ws g).getD i false = false := fun i hi =>
      List.getD_eq_default _ _ (by omega)
    have hstep_inv :
        (step ws g).length = (rcStep nOut (out, env) g).2.length ∧
        ∀ i, match (rcStep nOut (out, env) g).2.getD i (Sum.inl false) with
          | Sum.inl b => (step ws g).getD i false = b
          | Sum.inr w' => w' < nOut + (rcStep nOut (out, env) g).1.length ∧
              (step ws g).getD i false = ((rcStep nOut (out, env) g).1.foldl step ys).getD w' false := by
      constructor
      · rw [rcStep_env_len]; exact hws'_len
      · have hfold_app : ∀ (gnew : Gate),
            ((out ++ [gnew]).foldl step ys) = step (out.foldl step ys) gnew := fun gnew => by
          rw [List.foldl_append]; rfl
        have hkeep_old : ∀ (x : Bool ⊕ ℕ) (i : ℕ) (hi : i < env.length),
            match (env ++ [x]).getD i (Sum.inl false) with
            | Sum.inl b => (step ws g).getD i false = b
            | Sum.inr w' => w' < nOut + out.length ∧ (step ws g).getD i false = (out.foldl step ys).getD w' false := by
          intro x i hi
          have h1 : (env ++ [x]).getD i (Sum.inl false) = env.getD i (Sum.inl false) := by
            rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hi]
            simp [List.getElem_append_left hi]
          rw [h1, hget_old i hi]; exact hinv i
        have hkeep_old_app : ∀ (x : Bool ⊕ ℕ) (gnew : Gate) (i : ℕ) (hi : i < env.length),
            match (env ++ [x]).getD i (Sum.inl false) with
            | Sum.inl b => (step ws g).getD i false = b
            | Sum.inr w' => w' < nOut + (out ++ [gnew]).length ∧
                (step ws g).getD i false = ((out ++ [gnew]).foldl step ys).getD w' false := by
          intro x gnew i hi
          have hk := hkeep_old x i hi
          cases hm : (env ++ [x]).getD i (Sum.inl false) with
          | inl b => rw [hm] at hk; exact hk
          | inr w' =>
            rw [hm] at hk; dsimp only at hk
            have hw' : w' < nOut + out.length := hk.1
            refine ⟨by simp; omega, ?_⟩
            rw [hk.2, hfold_app gnew]
            have hlen_out : (out.foldl step ys).length = nOut + out.length := by rw [wfold_len, hyl]
            have hlen_w : (step (out.foldl step ys) gnew).length = nOut + out.length + 1 := by simp [step, hlen_out]
            rw [List.getD_eq_getElem _ _ (by omega : w' < (out.foldl step ys).length),
                List.getD_eq_getElem _ _ (by omega : w' < (step (out.foldl step ys) gnew).length)]
            simp [step, List.getElem_append_left (by omega : w' < (out.foldl step ys).length)]
        have hkeep_hi : ∀ (x : Bool ⊕ ℕ) (i : ℕ) (hi : env.length + 1 ≤ i),
            (env ++ [x]).getD i (Sum.inl false) = Sum.inl false := fun x i hi =>
          List.getD_eq_default _ _ (by simp; omega)
        have hget_env_last : ∀ (x : Bool ⊕ ℕ), (env ++ [x]).getD env.length (Sum.inl false) = x := fun x => by
          rw [List.getD_eq_getElem _ _ (by simp)]; simp
        have hmem_bound : ∀ w' ∈ g.inputs.filterMap (fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none),
            w' < nOut + out.length := by
          intro w' hw'
          obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp hw'
          have hij := hinv j
          cases hm : env.getD j (Sum.inl false) with
          | inl b => rw [hm] at hj; cases hj
          | inr w0 =>
            rw [hm] at hj hij; dsimp only at hij
            cases hj; exact hij.1
        have hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := hg.1
        rcases hop with hop | hop | hop
        ·
          simp only [rcStep, hop]
          split_ifs with hany
          · intro i
            by_cases hi : i < env.length
            · exact hkeep_old (Sum.inl false) i hi
            · by_cases heq : i = env.length
              · subst heq
                rw [hget_env_last (Sum.inl false), hget_last, hop]
                simp only [GateOp.eval, List.all_eq_false, id_eq]
                rw [List.any_eq_true] at hany
                obtain ⟨j, hj, hjf⟩ := hany
                have hj' := hinv j
                cases hm : env.getD j (Sum.inl false) with
                | inl b =>
                  rw [hm] at hjf hj'; dsimp only at hj'
                  cases b with
                  | false => exact ⟨ws.getD j false, List.mem_map.mpr ⟨j, hj, rfl⟩, by rw [hj']; decide⟩
                  | true => simp at hjf
                | inr w' => rw [hm] at hjf; simp at hjf
              · rw [hkeep_hi (Sum.inl false) i (by omega)]; exact hget_hi i (by omega)
          · have hand_eq : (g.inputs.map fun j => ws.getD j false).all id =
                ((g.inputs.filterMap fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none).map
                  fun w' => (out.foldl step ys).getD w' false).all id := by
              have hnof : ∀ j ∈ g.inputs, env.getD j (Sum.inl false) ≠ Sum.inl false := by
                intro j hj heqf
                apply hany; rw [List.any_eq_true]; exact ⟨j, hj, by rw [heqf]⟩
              have hlist : ∀ l : List ℕ, (∀ j ∈ l, env.getD j (Sum.inl false) ≠ Sum.inl false) →
                  (l.map fun j => ws.getD j false).all id =
                  ((l.filterMap fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none).map
                    fun w' => (out.foldl step ys).getD w' false).all id := by
                intro l
                induction l with
                | nil => intro _; rfl
                | cons a t iht =>
                  intro hnf
                  have ha := hnf a List.mem_cons_self
                  have hia := hinv a
                  have ht := iht (fun j hj => hnf j (List.mem_cons_of_mem _ hj))
                  cases hm : env.getD a (Sum.inl false) with
                  | inl b =>
                    cases b with
                    | false => exact absurd hm ha
                    | true =>
                      rw [hm] at hia; dsimp only at hia
                      simp only [List.filterMap_cons, hm, List.map_cons, List.all_cons, id_eq, hia, Bool.true_and, ht]
                  | inr w' =>
                    rw [hm] at hia; dsimp only at hia
                    simp only [List.filterMap_cons, hm, List.map_cons, List.all_cons, id_eq, hia.2, ht]
              exact hlist g.inputs hnof
            cases hins : g.inputs.filterMap (fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none) with
            | nil =>
              rw [hins] at hand_eq
              intro i
              by_cases hi : i < env.length
              · exact hkeep_old (Sum.inl true) i hi
              · by_cases heq : i = env.length
                · subst heq; rw [hget_env_last (Sum.inl true), hget_last, hop]; simpa [GateOp.eval] using hand_eq
                · rw [hkeep_hi (Sum.inl true) i (by omega)]; exact hget_hi i (by omega)
            | cons a t =>
              cases t with
              | nil =>
                rw [hins] at hand_eq
                intro i
                by_cases hi : i < env.length
                · exact hkeep_old (Sum.inr a) i hi
                · by_cases heq : i = env.length
                  · subst heq
                    rw [hget_env_last (Sum.inr a)]
                    refine ⟨hmem_bound a (by rw [hins]; simp), ?_⟩
                    rw [hget_last, hop]; simpa [GateOp.eval] using hand_eq
                  · rw [hkeep_hi (Sum.inr a) i (by omega)]; exact hget_hi i (by omega)
              | cons b t2 =>
                rw [hins] at hand_eq
                intro i
                by_cases hi : i < env.length
                · exact hkeep_old_app (Sum.inr (nOut + out.length)) _ i hi
                · by_cases heq : i = env.length
                  · subst heq
                    rw [hget_env_last (Sum.inr (nOut + out.length))]
                    refine ⟨by simp, ?_⟩
                    rw [hget_last, hop, hfold_app]
                    have hlen_out : (out.foldl step ys).length = nOut + out.length := by rw [wfold_len, hyl]
                    rw [← hlen_out, List.getD_eq_getElem _ _ (by simp [step])]
                    simp only [step, List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero]
                    simpa [GateOp.eval] using hand_eq
                  · rw [hkeep_hi (Sum.inr (nOut + out.length)) i (by omega)]; exact hget_hi i (by omega)
        ·
          simp only [rcStep, hop]
          split_ifs with hany
          · intro i
            by_cases hi : i < env.length
            · exact hkeep_old (Sum.inl true) i hi
            · by_cases heq : i = env.length
              · subst heq
                rw [hget_env_last (Sum.inl true), hget_last, hop]
                simp only [GateOp.eval, List.any_eq_true, id_eq]
                rw [List.any_eq_true] at hany
                obtain ⟨j, hj, hjt⟩ := hany
                have hj' := hinv j
                cases hm : env.getD j (Sum.inl false) with
                | inl b =>
                  rw [hm] at hjt hj'; dsimp only at hj'
                  cases b with
                  | true => exact ⟨ws.getD j false, List.mem_map.mpr ⟨j, hj, rfl⟩, hj'⟩
                  | false => simp at hjt
                | inr w' => rw [hm] at hjt; simp at hjt
              · rw [hkeep_hi (Sum.inl true) i (by omega)]; exact hget_hi i (by omega)
          · have hor_eq : (g.inputs.map fun j => ws.getD j false).any id =
                ((g.inputs.filterMap fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none).map
                  fun w' => (out.foldl step ys).getD w' false).any id := by
              have hnot : ∀ j ∈ g.inputs, env.getD j (Sum.inl false) ≠ Sum.inl true := by
                intro j hj heqt
                apply hany; rw [List.any_eq_true]; exact ⟨j, hj, by rw [heqt]⟩
              have hlist : ∀ l : List ℕ, (∀ j ∈ l, env.getD j (Sum.inl false) ≠ Sum.inl true) →
                  (l.map fun j => ws.getD j false).any id =
                  ((l.filterMap fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none).map
                    fun w' => (out.foldl step ys).getD w' false).any id := by
                intro l
                induction l with
                | nil => intro _; rfl
                | cons a t iht =>
                  intro hnt
                  have ha := hnt a List.mem_cons_self
                  have hia := hinv a
                  have ht := iht (fun j hj => hnt j (List.mem_cons_of_mem _ hj))
                  cases hm : env.getD a (Sum.inl false) with
                  | inl b =>
                    cases b with
                    | true => exact absurd hm ha
                    | false =>
                      rw [hm] at hia; dsimp only at hia
                      simp only [List.filterMap_cons, hm, List.map_cons, List.any_cons, id_eq, hia, Bool.false_or, ht]
                  | inr w' =>
                    rw [hm] at hia; dsimp only at hia
                    simp only [List.filterMap_cons, hm, List.map_cons, List.any_cons, id_eq, hia.2, ht]
              exact hlist g.inputs hnot
            cases hins : g.inputs.filterMap (fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none) with
            | nil =>
              rw [hins] at hor_eq
              intro i
              by_cases hi : i < env.length
              · exact hkeep_old (Sum.inl false) i hi
              · by_cases heq : i = env.length
                · subst heq; rw [hget_env_last (Sum.inl false), hget_last, hop]; simpa [GateOp.eval] using hor_eq
                · rw [hkeep_hi (Sum.inl false) i (by omega)]; exact hget_hi i (by omega)
            | cons a t =>
              cases t with
              | nil =>
                rw [hins] at hor_eq
                intro i
                by_cases hi : i < env.length
                · exact hkeep_old (Sum.inr a) i hi
                · by_cases heq : i = env.length
                  · subst heq
                    rw [hget_env_last (Sum.inr a)]
                    refine ⟨hmem_bound a (by rw [hins]; simp), ?_⟩
                    rw [hget_last, hop]; simpa [GateOp.eval] using hor_eq
                  · rw [hkeep_hi (Sum.inr a) i (by omega)]; exact hget_hi i (by omega)
              | cons b t2 =>
                rw [hins] at hor_eq
                intro i
                by_cases hi : i < env.length
                · exact hkeep_old_app (Sum.inr (nOut + out.length)) _ i hi
                · by_cases heq : i = env.length
                  · subst heq
                    rw [hget_env_last (Sum.inr (nOut + out.length))]
                    refine ⟨by simp, ?_⟩
                    rw [hget_last, hop, hfold_app]
                    have hlen_out : (out.foldl step ys).length = nOut + out.length := by rw [wfold_len, hyl]
                    rw [← hlen_out, List.getD_eq_getElem _ _ (by simp [step])]
                    simp only [step, List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero]
                    simpa [GateOp.eval] using hor_eq
                  · rw [hkeep_hi (Sum.inr (nOut + out.length)) i (by omega)]; exact hget_hi i (by omega)
        ·
          simp only [rcStep, hop]
          cases hgi : g.inputs with
          | nil =>
            intro i
            by_cases hi : i < env.length
            · exact hkeep_old (Sum.inl true) i hi
            · by_cases heq : i = env.length
              · subst heq; rw [hget_env_last (Sum.inl true), hget_last, hop, hgi]; rfl
              · rw [hkeep_hi (Sum.inl true) i (by omega)]; exact hget_hi i (by omega)
          | cons j rest_i =>
            dsimp only
            cases hm : env.getD j (Sum.inl false) with
            | inl b =>
              dsimp only
              have hj' := hinv j; rw [hm] at hj'; dsimp only at hj'
              intro i
              by_cases hi : i < env.length
              · exact hkeep_old (Sum.inl (!b)) i hi
              · by_cases heq : i = env.length
                · subst heq; rw [hget_env_last (Sum.inl (!b)), hget_last, hop, hgi]; simpa [GateOp.eval] using hj'
                · rw [hkeep_hi (Sum.inl (!b)) i (by omega)]; exact hget_hi i (by omega)
            | inr w' =>
              dsimp only
              have hj' := hinv j; rw [hm] at hj'; dsimp only at hj'
              intro i
              by_cases hi : i < env.length
              · exact hkeep_old_app (Sum.inr (nOut + out.length)) _ i hi
              · by_cases heq : i = env.length
                · subst heq
                  rw [hget_env_last (Sum.inr (nOut + out.length))]
                  refine ⟨by simp, ?_⟩
                  rw [hget_last, hop, hgi, hfold_app]
                  have hlen_out : (out.foldl step ys).length = nOut + out.length := by rw [wfold_len, hyl]
                  rw [← hlen_out, List.getD_eq_getElem _ _ (by simp [step])]
                  simp only [step, List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero]
                  simpa [GateOp.eval] using hj'.2
                · rw [hkeep_hi (Sum.inr (nOut + out.length)) i (by omega)]; exact hget_hi i (by omega)
    exact ih (fun g' hg' => hM g' (List.mem_cons_of_mem _ hg')) (step ws g) (rcStep nOut (out, env) g)
      hstep_inv.1 hstep_inv.2

lemma rcFold_inr_agree (nOut : ℕ) (gs : List Gate) (hM : ∀ g ∈ gs, legal g)
    (wx wy : List Bool) (st : List Gate × List (Bool ⊕ ℕ))
    (hxlen : wx.length = st.2.length) (hylen : wy.length = st.2.length)
    (heq_cost : binaryCost (gs.foldl (rcStep nOut) st).1 = binaryCost st.1 + binaryCost gs)
    (hagree : ∀ i w', st.2.getD i (Sum.inl false) = Sum.inr w' → wx.getD i false = wy.getD i false) :
    ∀ i w', (gs.foldl (rcStep nOut) st).2.getD i (Sum.inl false) = Sum.inr w' →
      (gs.foldl step wx).getD i false = (gs.foldl step wy).getD i false := by
  induction gs generalizing wx wy st with
  | nil => exact hagree
  | cons g rest ih =>
    simp only [List.foldl_cons] at heq_cost ⊢
    have hg := hM g List.mem_cons_self
    have h1 := rcFold_binCost_le nOut rest (rcStep nOut st g)
    have h2 := rcStep_binCost_le nOut st g
    have h3 : binaryCost (g :: rest) = binaryCost rest + (if isBinary g then 1 else 0) := by
      unfold binaryCost; rw [List.filter_cons]; cases isBinary g <;> simp
    have hstep_cost : binaryCost (rcStep nOut st g).1 = binaryCost st.1 + (if isBinary g then 1 else 0) := by omega
    have hrest_cost : binaryCost (rest.foldl (rcStep nOut) (rcStep nOut st g)).1 =
        binaryCost (rcStep nOut st g).1 + binaryCost rest := by omega
    rcases st with ⟨out, env⟩
    dsimp only at hxlen hylen hagree hstep_cost
    refine ih (fun g' hg' => hM g' (List.mem_cons_of_mem _ hg')) (step wx g) (step wy g)
      (rcStep nOut (out, env) g) (by rw [rcStep_env_len]; simp [step, hxlen])
      (by rw [rcStep_env_len]; simp [step, hylen]) hrest_cost ?_
    have hget_old_x : ∀ i < env.length, (step wx g).getD i false = wx.getD i false := fun i hi => by
      rw [List.getD_eq_getElem _ _ (by simp [step]; omega), List.getD_eq_getElem _ _ (by omega)]
      simp [step, List.getElem_append_left (by omega : i < wx.length)]
    have hget_old_y : ∀ i < env.length, (step wy g).getD i false = wy.getD i false := fun i hi => by
      rw [List.getD_eq_getElem _ _ (by simp [step]; omega), List.getD_eq_getElem _ _ (by omega)]
      simp [step, List.getElem_append_left (by omega : i < wy.length)]
    have hget_last_x : (step wx g).getD env.length false = g.op.eval (g.inputs.map fun j => wx.getD j false) := by
      rw [← hxlen, List.getD_eq_getElem _ _ (by simp [step])]; simp [step]
    have hget_last_y : (step wy g).getD env.length false = g.op.eval (g.inputs.map fun j => wy.getD j false) := by
      rw [← hylen, List.getD_eq_getElem _ _ (by simp [step])]; simp [step]
    have hall_inr_of_len2 :
        (g.inputs.filterMap fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none).length ≥ 2 →
        ∀ j ∈ g.inputs, ∃ w0, env.getD j (Sum.inl false) = Sum.inr w0 := by
      intro hl2 j hj
      cases hm : env.getD j (Sum.inl false) with
      | inr w0 => exact ⟨w0, rfl⟩
      | inl b =>
        exfalso
        have hlt := list_filterMap_len_lt (fun i => match env.getD i (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none)
          g.inputs j hj (by rw [hm])
        have hcap := hg.2
        omega
    have hstep_env_old : ∀ (x : Bool ⊕ ℕ) (i : ℕ) (hi : i < env.length),
        (env ++ [x]).getD i (Sum.inl false) = env.getD i (Sum.inl false) := fun x i hi => by
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hi]
      simp [List.getElem_append_left hi]
    have hstep_env_hi : ∀ (x : Bool ⊕ ℕ) (i : ℕ) (hi : env.length + 1 ≤ i),
        (env ++ [x]).getD i (Sum.inl false) = Sum.inl false := fun x i hi =>
      List.getD_eq_default _ _ (by simp; omega)
    have hstep_env_last : ∀ (x : Bool ⊕ ℕ), (env ++ [x]).getD env.length (Sum.inl false) = x := fun x => by
      rw [List.getD_eq_getElem _ _ (by simp)]; simp
    intro i w' hiw'
    by_cases hi : i < env.length
    · have h1 : (rcStep nOut (out, env) g).2.getD i (Sum.inl false) = env.getD i (Sum.inl false) := by
        cases h : g.op
        · simp only [rcStep, h]; split_ifs
          · exact hstep_env_old _ i hi
          · cases g.inputs.filterMap _ with | nil => exact hstep_env_old _ i hi | cons a t => cases t <;> exact hstep_env_old _ i hi
        · simp only [rcStep, h]; split_ifs
          · exact hstep_env_old _ i hi
          · cases g.inputs.filterMap _ with | nil => exact hstep_env_old _ i hi | cons a t => cases t <;> exact hstep_env_old _ i hi
        · simp only [rcStep, h]; cases g.inputs with
          | nil => exact hstep_env_old _ i hi
          | cons j _ => dsimp only; cases env.getD j (Sum.inl false) <;> exact hstep_env_old _ i hi
        · simp only [rcStep, h]; exact hstep_env_old _ i hi
        · simp only [rcStep, h]; exact hstep_env_old _ i hi
      rw [h1] at hiw'
      rw [hget_old_x i hi, hget_old_y i hi]
      exact hagree i w' hiw'
    · by_cases heq : i = env.length
      · subst heq
        rw [hget_last_x, hget_last_y]
        have hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := hg.1
        rcases hop with hop | hop | hop
        · simp only [rcStep, hop, isBinary, ite_true] at hstep_cost
          split_ifs at hstep_cost with hany
          · dsimp only at hstep_cost; omega
          · cases hins : g.inputs.filterMap (fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none) with
            | nil => rw [hins] at hstep_cost; dsimp only at hstep_cost; omega
            | cons a t =>
              cases t with
              | nil => rw [hins] at hstep_cost; dsimp only at hstep_cost; omega
              | cons b t2 =>
                have hl2 : (g.inputs.filterMap fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none).length ≥ 2 := by
                  rw [hins]; simp
                congr 1; apply List.map_congr_left
                intro j hj
                obtain ⟨w0, hw0⟩ := hall_inr_of_len2 hl2 j hj
                exact hagree j w0 hw0
        · simp only [rcStep, hop, isBinary, ite_true] at hstep_cost
          split_ifs at hstep_cost with hany
          · dsimp only at hstep_cost; omega
          · cases hins : g.inputs.filterMap (fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none) with
            | nil => rw [hins] at hstep_cost; dsimp only at hstep_cost; omega
            | cons a t =>
              cases t with
              | nil => rw [hins] at hstep_cost; dsimp only at hstep_cost; omega
              | cons b t2 =>
                have hl2 : (g.inputs.filterMap fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none).length ≥ 2 := by
                  rw [hins]; simp
                congr 1; apply List.map_congr_left
                intro j hj
                obtain ⟨w0, hw0⟩ := hall_inr_of_len2 hl2 j hj
                exact hagree j w0 hw0
        · simp only [rcStep, hop] at hiw'
          cases hgi : g.inputs with
          | nil =>
            rw [hgi] at hiw'; dsimp only at hiw'; rw [hstep_env_last] at hiw'; cases hiw'
          | cons j rest_i =>
            rw [hgi] at hiw'; dsimp only at hiw'
            cases hm : env.getD j (Sum.inl false) with
            | inl b => rw [hm] at hiw'; dsimp only at hiw'; rw [hstep_env_last] at hiw'; cases hiw'
            | inr w0 =>
              rw [hop]
              simp only [GateOp.eval, List.map_cons, List.headD_cons, hagree j w0 hm]
      · exfalso
        have hlen_st : (rcStep nOut (out, env) g).2.length = env.length + 1 := rcStep_env_len nOut (out, env) g
        rw [List.getD_eq_default _ _ (by omega)] at hiw'; cases hiw'

lemma rcCircuit_props (nIn nOut : ℕ) (env0 : List (Bool ⊕ ℕ)) (hlen0 : env0.length = nIn)
    (gs : List Gate) (o : ℕ) (hM : ∀ g ∈ gs, legal g) :
    let res := rcCircuit nOut env0 gs o
    (∀ g ∈ res.1, legal g) ∧
    binaryCost res.1 ≤ binaryCost gs ∧
    (∀ (xs ys : List Bool), xs.length = nIn → ys.length = nOut →
      (∀ i < nIn, match env0.getD i (Sum.inl false) with
        | Sum.inl b => xs.getD i false = b
        | Sum.inr w' => w' < nOut ∧ xs.getD i false = ys.getD w' false) →
      Circuit.eval ⟨res.1, res.2⟩ ys = Circuit.eval ⟨gs, o⟩ xs) := by
  dsimp only [rcCircuit]
  have hfold_leg := rcFold_legal nOut gs ([], env0) (by intro g h; cases h) hM
  have hfold_bc : binaryCost (gs.foldl (rcStep nOut) ([], env0)).1 ≤ binaryCost gs := by
    have := rcFold_binCost_le nOut gs ([], env0); simpa [binaryCost] using this
  have hcore_eval : ∀ (xs ys : List Bool), xs.length = nIn → ys.length = nOut →
      (∀ i < nIn, match env0.getD i (Sum.inl false) with
        | Sum.inl b => xs.getD i false = b
        | Sum.inr w' => w' < nOut ∧ xs.getD i false = ys.getD w' false) →
      ∀ i, match (gs.foldl (rcStep nOut) ([], env0)).2.getD i (Sum.inl false) with
        | Sum.inl b => (gs.foldl step xs).getD i false = b
        | Sum.inr w' => w' < nOut + (gs.foldl (rcStep nOut) ([], env0)).1.length ∧
            (gs.foldl step xs).getD i false = ((gs.foldl (rcStep nOut) ([], env0)).1.foldl step ys).getD w' false := by
    intro xs ys hxl hyl hinit
    have hinit' : ∀ i, match (([] : List Gate), env0).2.getD i (Sum.inl false) with
        | Sum.inl b => xs.getD i false = b
        | Sum.inr w' => w' < nOut + (([] : List Gate), env0).1.length ∧ xs.getD i false = ((([] : List Gate), env0).1.foldl step ys).getD w' false := by
      intro i
      by_cases hi : i < nIn
      · simpa using hinit i hi
      · dsimp only
        rw [List.getD_eq_default _ _ (by omega)]
        exact List.getD_eq_default _ _ (by omega)
    exact (rcFold_eval_inv nOut gs ys hyl hM xs ([], env0) (by simp [hlen0, hxl]) hinit').2
  cases hm : (gs.foldl (rcStep nOut) ([], env0)).2.getD o (Sum.inl false) with
  | inr w' =>
    refine ⟨hfold_leg, hfold_bc, ?_⟩
    intro xs ys hxl hyl hinit
    have h := hcore_eval xs ys hxl hyl hinit o
    rw [hm] at h; exact h.2.symm
  | inl b =>
    cases b with
    | false =>
      refine ⟨hfold_leg, hfold_bc, ?_⟩
      intro xs ys hxl hyl hinit
      have h := hcore_eval xs ys hxl hyl hinit o
      rw [hm] at h
      change ((gs.foldl (rcStep nOut) ([], env0)).1.foldl step ys).getD (nOut + (gs.foldl (rcStep nOut) ([], env0)).1.length) false =
        (gs.foldl step xs).getD o false
      rw [h, List.getD_eq_default _ _ (by rw [wfold_len, hyl])]
    | true =>
      refine ⟨?_, ?_, ?_⟩
      · intro g hg
        simp only [List.mem_append, List.mem_singleton] at hg
        rcases hg with h | rfl
        · exact hfold_leg g h
        · exact ⟨by simp, by decide⟩
      · rw [binaryCost_append_one]; simp [isBinary]; exact hfold_bc
      · intro xs ys hxl hyl hinit
        have h := hcore_eval xs ys hxl hyl hinit o
        rw [hm] at h
        change (((gs.foldl (rcStep nOut) ([], env0)).1 ++ [({ op := GateOp.not, inputs := [] } : Gate)]).foldl step ys).getD
            (nOut + (gs.foldl (rcStep nOut) ([], env0)).1.length) false =
          (gs.foldl step xs).getD o false
        rw [h, List.foldl_append]
        change (step ((gs.foldl (rcStep nOut) ([], env0)).1.foldl step ys) ({ op := GateOp.not, inputs := [] } : Gate)).getD
            (nOut + (gs.foldl (rcStep nOut) ([], env0)).1.length) false = true
        have hlen : ((gs.foldl (rcStep nOut) ([], env0)).1.foldl step ys).length =
            nOut + (gs.foldl (rcStep nOut) ([], env0)).1.length := by rw [wfold_len, hyl]
        rw [← hlen, List.getD_eq_getElem _ _ (by simp [step])]
        simp [step, GateOp.eval]

lemma rcCircuit_binCost_lt (k : ℕ) (hk : k < 7) (gs : List Gate) (o : ℕ) (hM : ∀ g ∈ gs, legal g)
    (x1 x2 : List Bool) (hx1l : x1.length = 7) (hx2l : x2.length = 7)
    (hagree_xy : ∀ i < 7, i ≠ k → x1.getD i false = x2.getD i false)
    (hdiff_xy : Circuit.eval ⟨gs, o⟩ x1 ≠ Circuit.eval ⟨gs, o⟩ x2)
    (z1 z2 : List Bool) (hz1l : z1.length = 7) (hz2l : z2.length = 7)
    (hz1k : z1.getD k false = false) (hz2k : z2.getD k false = false)
    (hdiff_zz : Circuit.eval ⟨gs, o⟩ z1 ≠ Circuit.eval ⟨gs, o⟩ z2) :
    let env0 : List (Bool ⊕ ℕ) := List.ofFn fun i : Fin 7 => if i.val = k then Sum.inl false else Sum.inr i.val
    binaryCost (rcCircuit 7 env0 gs o).1 + 1 ≤ binaryCost gs := by
  intro env0
  have hle_fold : binaryCost (gs.foldl (rcStep 7) ([], env0)).1 ≤ binaryCost gs := by
    have := rcFold_binCost_le 7 gs ([], env0); simpa [binaryCost] using this
  have hbc_rc : binaryCost (rcCircuit 7 env0 gs o).1 = binaryCost (gs.foldl (rcStep 7) ([], env0)).1 := by
    dsimp only [rcCircuit]
    cases (gs.foldl (rcStep 7) ([], env0)).2.getD o (Sum.inl false) with
    | inr w' => rfl
    | inl b => cases b with
      | false => rfl
      | true => dsimp only; rw [binaryCost_append_one]; simp [isBinary]
  rw [hbc_rc]
  by_contra hlt
  have hzero : binaryCost ([] : List Gate) = 0 := rfl
  have heq_cost : binaryCost (gs.foldl (rcStep 7) ([], env0)).1 = binaryCost ([] : List Gate) + binaryCost gs := by
    rw [hzero, Nat.zero_add]; omega
  cases hm : (gs.foldl (rcStep 7) ([], env0)).2.getD o (Sum.inl false) with
  | inr w' =>
    have hinit : ∀ i w0, (([] : List Gate), env0).2.getD i (Sum.inl false) = Sum.inr w0 → x1.getD i false = x2.getD i false := by
      intro i w0 hiw
      by_cases hi : i < 7
      · dsimp only at hiw
        rw [List.getD_eq_getElem env0 _ (by simp [env0, hi])] at hiw
        change (List.ofFn fun j : Fin 7 => if j.val = k then Sum.inl false else Sum.inr j.val)[i]'(by simp [hi]) = Sum.inr w0 at hiw
        rw [List.getElem_ofFn] at hiw
        by_cases hik : i = k
        · simp [hik] at hiw
        · exact hagree_xy i hi hik
      · dsimp only at hiw
        rw [List.getD_eq_default env0 _ (by simp [env0]; omega)] at hiw; cases hiw
    have hsame := rcFold_inr_agree 7 gs hM x1 x2 ([], env0) (by simp [env0, hx1l]) (by simp [env0, hx2l])
      heq_cost hinit o w' hm
    exact hdiff_xy hsame
  | inl b =>
    have hinit_z : ∀ (z : List Bool), z.length = 7 → z.getD k false = false →
        ∀ i, match (([] : List Gate), env0).2.getD i (Sum.inl false) with
          | Sum.inl b0 => z.getD i false = b0
          | Sum.inr w' => w' < 7 + ([] : List Gate).length ∧ z.getD i false = (([] : List Gate).foldl step z).getD w' false := by
      intro z hzl hzk i
      by_cases hi : i < 7
      · dsimp only
        rw [List.getD_eq_getElem env0 _ (by simp [env0, hi])]
        change match (List.ofFn fun j : Fin 7 => if j.val = k then Sum.inl false else Sum.inr j.val)[i]'(by simp [hi]) with
          | Sum.inl b0 => z.getD i false = b0
          | Sum.inr w' => w' < 7 + 0 ∧ z.getD i false = z.getD w' false
        rw [List.getElem_ofFn]
        by_cases hik : i = k
        · subst hik; simp only [ite_true]; exact hzk
        · simp [hik, hi]
      · dsimp only
        rw [List.getD_eq_default env0 _ (by simp [env0]; omega)]
        exact List.getD_eq_default z false (by omega)
    have hz1 := (rcFold_eval_inv 7 gs z1 hz1l hM z1 ([], env0) (by simp [env0, hz1l]) (hinit_z z1 hz1l hz1k)).2 o
    have hz2 := (rcFold_eval_inv 7 gs z2 hz2l hM z2 ([], env0) (by simp [env0, hz2l]) (hinit_z z2 hz2l hz2k)).2 o
    rw [hm] at hz1 hz2
    dsimp only at hz1 hz2
    exact hdiff_zz (hz1.trans hz2.symm)

def graphF (x : Fin 7 → Bool) : Bool :=
  decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2,
    (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧
    (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)

def witGates : List Gate :=
  [ { op := GateOp.or,  inputs := [0, 6] }
  , { op := GateOp.and, inputs := [3, 7] }
  , { op := GateOp.or,  inputs := [5, 8] }
  , { op := GateOp.or,  inputs := [9, 6] }
  , { op := GateOp.and, inputs := [4, 10] }
  , { op := GateOp.or,  inputs := [2, 9] }
  , { op := GateOp.or,  inputs := [4, 10] }
  , { op := GateOp.and, inputs := [6, 12] }
  , { op := GateOp.or,  inputs := [1, 14] }
  , { op := GateOp.or,  inputs := [0, 15] }
  , { op := GateOp.and, inputs := [16, 13] }
  , { op := GateOp.or,  inputs := [11, 17] } ]

lemma witGates_mono : ∀ g ∈ witGates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma witGates_eval : ∀ x : Fin 7 → Bool, Circuit.eval ⟨witGates, 18⟩ (List.ofFn x) = graphF x := by
  decide +kernel

def lift5 (y : Fin 5 → Bool) : Fin 7 → Bool
  | ⟨0, _⟩ => y 0
  | ⟨1, _⟩ => y 1
  | ⟨2, _⟩ => false
  | ⟨3, _⟩ => y 1
  | ⟨4, _⟩ => y 2
  | ⟨5, _⟩ => y 3
  | ⟨6, _⟩ => y 4

lemma graphF_lift5 : ∀ y : Fin 5 → Bool, graphF (lift5 y) = table y := by
  decide +kernel

lemma main_proof (gates : List Gate) (o : ℕ)
    (hleg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (heval : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = graphF x) :
    ∃ (gates' : List Gate) (o' : ℕ),
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧
      ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = graphF x := by
  by_cases hasNot : ∃ g ∈ gates, g.op = GateOp.not
  · obtain ⟨gNot, hgNot, hopNot⟩ := hasNot
    have hbc_lt : binaryCost gates < gates.length :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨gNot, hgNot, by simp [isBinary, hopNot]⟩
    have hleg' : ∀ g ∈ gates, legal g := fun g hg => ⟨by simpa using (hleg g hg).1, (hleg g hg).2⟩
    let env2 : List (Bool ⊕ ℕ) := List.ofFn fun i : Fin 7 => if i.val = 2 then Sum.inl false else Sum.inr i.val
    let C1 := rcCircuit 7 env2 gates o
    have h1_props := rcCircuit_props 7 7 env2 (by simp [env2]) gates o hleg'
    have h1_eval : ∀ x : Fin 7 → Bool, x 2 = false → Circuit.eval ⟨C1.1, C1.2⟩ (List.ofFn x) = graphF x := by
      intro x hx2
      rw [h1_props.2.2 (List.ofFn x) (List.ofFn x) (by simp) (by simp) ?_, heval x]
      intro i hi
      rw [List.getD_eq_getElem env2 _ (by simp [env2, hi])]
      change match (List.ofFn fun j : Fin 7 => if j.val = 2 then Sum.inl false else Sum.inr j.val)[i]'(by simp [hi]) with
        | Sum.inl b => (List.ofFn x).getD i false = b
        | Sum.inr w' => w' < 7 ∧ (List.ofFn x).getD i false = (List.ofFn x).getD w' false
      rw [List.getElem_ofFn]
      by_cases hi2 : i = 2
      · subst hi2; simp only [ite_true]; rw [List.getD_eq_getElem _ _ (by simp)]; simpa using hx2
      · simp [hi2, hi]
    have h1_lt : binaryCost C1.1 + 1 ≤ binaryCost gates := by
      let fx1 : Fin 7 → Bool := fun i => decide (i.val = 2 ∨ i.val = 6)
      let fx2 : Fin 7 → Bool := fun i => decide (i.val = 6)
      let fz1 : Fin 7 → Bool := fun _ => false
      let fz2 : Fin 7 → Bool := fun i => decide (i.val = 0 ∨ i.val = 3)
      exact rcCircuit_binCost_lt 2 (by decide) gates o hleg'
        (List.ofFn fx1) (List.ofFn fx2) (by simp) (by simp) (by decide)
        (by rw [heval fx1, heval fx2]; decide)
        (List.ofFn fz1) (List.ofFn fz2) (by simp) (by simp) (by decide) (by decide)
        (by rw [heval fz1, heval fz2]; decide)
    let env5 : List (Bool ⊕ ℕ) := [Sum.inr 0, Sum.inr 1, Sum.inl false, Sum.inr 1, Sum.inr 2, Sum.inr 3, Sum.inr 4]
    let C2 := rcCircuit 5 env5 C1.1 C1.2
    have h2_props := rcCircuit_props 7 5 env5 (by decide) C1.1 C1.2 h1_props.1
    have h2_eval : ∀ y : Fin 5 → Bool, Circuit.eval ⟨C2.1, C2.2⟩ (List.ofFn y) = table y := by
      intro y
      rw [h2_props.2.2 (List.ofFn (lift5 y)) (List.ofFn y) (by simp) (by simp) ?_,
          h1_eval (lift5 y) rfl, graphF_lift5 y]
      intro i hi
      interval_cases i
      · exact ⟨by decide, by simp [lift5]⟩
      · exact ⟨by decide, by simp [lift5]⟩
      · simp [env5, lift5]
      · exact ⟨by decide, by simp [lift5]⟩
      · exact ⟨by decide, by simp [lift5]⟩
      · exact ⟨by decide, by simp [lift5]⟩
      · exact ⟨by decide, by simp [lift5]⟩
    have h10 : 9 < binaryCost C2.1 := ten_binary C2.1 C2.2 h2_props.1 h2_eval
    have h2_le : binaryCost C2.1 ≤ binaryCost C1.1 := h2_props.2.1
    have h12 : witGates.length ≤ gates.length := by
      change 12 ≤ gates.length; omega
    exact ⟨witGates, 18, witGates_mono, h12, witGates_eval⟩
  · refine ⟨gates, o, fun g hg => ⟨?_, (hleg g hg).2⟩, le_refl _, heval⟩
    rcases (hleg g hg).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hasNot ⟨g, hg, h⟩).elim

end PEqualNP.Outside.L_meta_10766

theorem PEqualNP.Outside.L_meta_10766 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gates o hleg _ heval
  exact PEqualNP.Outside.L_meta_10766.main_proof gates o hleg heval
