import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.IntervalCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12102

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


def opsN {M : ℕ} (x y : BitVec M) : List (BitVec M) :=
  [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]

def basicOpsN {M : ℕ} (x y : BitVec M) : Finset (BitVec M) :=
  (opsN x y).toFinset

lemma opsN_swap {M : ℕ} (a b : BitVec M) : basicOpsN a b = basicOpsN b a := by
  ext w
  simp only [basicOpsN, opsN, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm, BitVec.or_comm]
  tauto

lemma index_of_opN {M : ℕ} (a b z : BitVec M) (hz : z ∈ basicOpsN a b) :
    ∃ o : Fin 4, (opsN a b).getD o.val 0 = z := by
  simp only [basicOpsN, opsN, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩

def holdsN {M : ℕ} (av : Finset (BitVec M)) (z : BitVec M) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

lemma holdsN_mono {M : ℕ} {av av' : Finset (BitVec M)} (sub : av ⊆ av') {x : BitVec M}
    (h : holdsN av x) : holdsN av' x :=
  h.imp_right (Or.imp_right fun ⟨a, ha, e⟩ => ⟨a, sub ha, e⟩)

lemma holdsN_not {M : ℕ} {av : Finset (BitVec M)} {z : BitVec M} (h : holdsN av z) :
    holdsN av (~~~z) := by
  rcases h with rfl | rfl | ⟨a, ha, he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he | he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachableN {M : ℕ} (av : Finset (BitVec M)) (z : BitVec M) : Prop :=
  holdsN av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOpsN a b, holdsN (insert w av) z

lemma reachableN_not {M : ℕ} {av : Finset (BitVec M)} {z : BitVec M} (h : reachableN av z) :
    reachableN av (~~~z) := by
  rcases h with h | ⟨a, ha, b, hb, ne, w, hop, hw⟩
  · exact .inl (holdsN_not h)
  · exact .inr ⟨a, ha, b, hb, ne, w, hop, holdsN_not hw⟩

lemma bv_zero_and {M : ℕ} (x : BitVec M) : (0 : BitVec M) &&& x = 0 := by simp
lemma bv_and_zero {M : ℕ} (x : BitVec M) : x &&& (0 : BitVec M) = 0 := by simp
lemma bv_zero_or {M : ℕ} (x : BitVec M) : (0 : BitVec M) ||| x = x := by simp
lemma bv_or_zero {M : ℕ} (x : BitVec M) : x ||| (0 : BitVec M) = x := by simp
lemma bv_allOnes_and {M : ℕ} (x : BitVec M) : (~~~(0 : BitVec M)) &&& x = x := by
  apply BitVec.eq_of_getElem_eq; intro i hi; simp
lemma bv_and_allOnes {M : ℕ} (x : BitVec M) : x &&& (~~~(0 : BitVec M)) = x := by
  apply BitVec.eq_of_getElem_eq; intro i hi; simp
lemma bv_allOnes_or {M : ℕ} (x : BitVec M) : (~~~(0 : BitVec M)) ||| x = ~~~(0 : BitVec M) := by
  apply BitVec.eq_of_getElem_eq; intro i hi; simp
lemma bv_or_allOnes {M : ℕ} (x : BitVec M) : x ||| (~~~(0 : BitVec M)) = ~~~(0 : BitVec M) := by
  apply BitVec.eq_of_getElem_eq; intro i hi; simp
lemma bv_getLsbD_zero {M : ℕ} (i : ℕ) : (0 : BitVec M).getLsbD i = false := by simp

lemma and_reachN {M : ℕ} {av : Finset (BitVec M)} {x y : BitVec M}
    (hx : holdsN av x) (hy : holdsN av y) : reachableN av (x &&& y) := by
  have base (a b : BitVec M) (ha : a ∈ av) (hb : b ∈ av) (op : BitVec M)
      (hop : op ∈ basicOpsN a b) (same : a = b → holdsN av op) : reachableN av op := by
    by_cases h : a = b
    · exact .inl (same h)
    · exact .inr ⟨a, ha, b, hb, h, op, hop, .inr (.inr ⟨op, Finset.mem_insert_self _ _, .inl rfl⟩)⟩
  rcases hx with rfl | rfl | ⟨a, ha, hxa⟩
  · exact .inl (.inl (bv_zero_and y))
  · simpa only [bv_allOnes_and] using .inl hy
  · rcases hxa with hxa | hxa
    · rw [hxa]
      rcases hy with rfl | rfl | ⟨b, hb, hyb⟩
      · exact .inl (.inl (bv_and_zero a))
      · exact .inl (.inr (.inr ⟨a, ha, .inl (bv_and_allOnes a)⟩))
      · rcases hyb with hyb | hyb
        · rw [hyb]
          exact base a b ha hb (a &&& b) (by simp [basicOpsN, opsN]) fun h => by
            subst h; exact .inr (.inr ⟨a, ha, .inl BitVec.and_self⟩)
        · rw [hyb]
          exact base a b ha hb (a &&& ~~~b) (by simp [basicOpsN, opsN]) fun h => by
            subst h; exact .inl (BitVec.and_not_self a)
    · rw [hxa]
      rcases hy with rfl | rfl | ⟨b, hb, hyb⟩
      · exact .inl (.inl (bv_and_zero (~~~a)))
      · exact .inl (.inr (.inr ⟨a, ha, .inr (bv_and_allOnes (~~~a))⟩))
      · rcases hyb with hyb | hyb
        · rw [hyb]
          exact base a b ha hb (b &&& ~~~a) (by simp [basicOpsN, opsN]) (fun h => by
            subst h; exact .inl (BitVec.and_not_self a)) |> fun r => by simpa only [BitVec.and_comm] using r
        · rw [hyb]
          have h := base a b ha hb (a ||| b) (by simp [basicOpsN, opsN]) fun h => by
            subst h; exact .inr (.inr ⟨a, ha, .inl BitVec.or_self⟩)
          simpa only [BitVec.not_or] using reachableN_not h

lemma or_reachN {M : ℕ} {av : Finset (BitVec M)} {x y : BitVec M}
    (hx : holdsN av x) (hy : holdsN av y) : reachableN av (x ||| y) := by
  have h := and_reachN (holdsN_not hx) (holdsN_not hy)
  simpa only [BitVec.not_and, BitVec.not_not] using reachableN_not h

lemma mem_ops_reachN {M : ℕ} {av : Finset (BitVec M)} {x y z : BitVec M}
    (hx : holdsN av x) (hy : holdsN av y) (hz : z ∈ basicOpsN x y) : reachableN av z := by
  simp only [basicOpsN, opsN, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact and_reachN hx hy
  · exact or_reachN hx hy
  · exact and_reachN hx (holdsN_not hy)
  · exact and_reachN hy (holdsN_not hx)

lemma mem_ops_constN {M : ℕ} {av : Finset (BitVec M)} {x y z : BitVec M}
    (hx : holdsN av x) (hy : holdsN av y)
    (hc : (x = 0 ∨ x = ~~~0) ∨ (y = 0 ∨ y = ~~~0)) (hz : z ∈ basicOpsN x y) : holdsN av z := by
  simp only [basicOpsN, opsN, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hc with (rfl | rfl) | (rfl | rfl)
  · rcases hz with rfl | rfl | rfl | rfl
    · exact .inl (bv_zero_and y)
    · simpa only [bv_zero_or] using hy
    · exact .inl (bv_zero_and (~~~y))
    · simpa only [bv_and_allOnes] using hy
  · rcases hz with rfl | rfl | rfl | rfl
    · simpa only [bv_allOnes_and] using hy
    · exact .inr (.inl (bv_allOnes_or y))
    · simpa only [bv_allOnes_and] using holdsN_not hy
    · exact .inl (by rw [BitVec.not_not, bv_and_zero])
  · rcases hz with rfl | rfl | rfl | rfl
    · exact .inl (bv_and_zero x)
    · simpa only [bv_or_zero] using hx
    · simpa only [bv_and_allOnes] using hx
    · exact .inl (bv_zero_and (~~~x))
  · rcases hz with rfl | rfl | rfl | rfl
    · simpa only [bv_and_allOnes] using hx
    · exact .inr (.inl (bv_or_allOnes x))
    · exact .inl (by rw [BitVec.not_not, bv_and_zero])
    · simpa only [bv_allOnes_and] using holdsN_not hx

lemma opsN_const_both {M : ℕ} {x y z : BitVec M} (hx : x = 0 ∨ x = ~~~0) (hy : y = 0 ∨ y = ~~~0)
    (hz : z ∈ basicOpsN x y) : z = 0 ∨ z = ~~~0 := by
  have h := mem_ops_constN (av := ∅) (hx.imp_right Or.inl) (hy.imp_right Or.inl) (.inl hx) hz
  rcases h with h | h | ⟨a, ha, _⟩
  · exact .inl h
  · exact .inr h
  · exact False.elim (Finset.notMem_empty a ha)

def SignedBuildN {M : ℕ} (k : ℕ) (av : Finset (BitVec M)) (z : BitVec M) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ build basicOpsN z k av ∨ build basicOpsN (~~~z) k av

lemma sbN_not {M : ℕ} {av : Finset (BitVec M)} {z : BitVec M} {k : ℕ}
    (h : SignedBuildN k av (~~~z)) : SignedBuildN k av z := by
  rcases h with h | h | h | h
  · exact .inr (.inl (by rw [← BitVec.not_not (b := z), h]))
  · exact .inl (by rw [← BitVec.not_not (b := z), h, BitVec.not_not])
  · exact .inr (.inr (.inr h))
  · exact .inr (.inr (.inl (by simpa only [BitVec.not_not] using h)))

lemma sbN_zero {M : ℕ} {av : Finset (BitVec M)} {z : BitVec M} (h : holdsN av z) :
    SignedBuildN 0 av z := by
  rcases h with h | h | ⟨a, ha, rfl | rfl⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl ha))
  · exact .inr (.inr (.inr (by simpa only [BitVec.not_not, build] using ha)))

lemma sbN_wait {M : ℕ} {av : Finset (BitVec M)} {z : BitVec M} {k : ℕ}
    (h : SignedBuildN k av z) : SignedBuildN (k + 1) av z :=
  h.imp_right (Or.imp_right (Or.imp .inl .inl))

lemma sbN_le {M : ℕ} {av : Finset (BitVec M)} {z : BitVec M} {k l : ℕ} (hkl : k ≤ l)
    (h : SignedBuildN k av z) : SignedBuildN l av z := by
  induction hkl with
  | refl => exact h
  | step _ ih => exact sbN_wait ih

lemma sbN_step {M : ℕ} {av : Finset (BitVec M)} {t a b z : BitVec M} {k : ℕ}
    (ha : a ∈ av) (hb : b ∈ av) (hne : a ≠ b) (hz : z ∈ basicOpsN a b)
    (h : SignedBuildN k (insert z av) t) : SignedBuildN (k + 1) av t :=
  h.imp_right (Or.imp_right (Or.imp (.inr ⟨a, ha, b, hb, hne, z, hz, ·⟩) (.inr ⟨a, ha, b, hb, hne, z, hz, ·⟩)))

def proj {N M : ℕ} (src : Fin M → Fin N) (w : BitVec N) : BitVec M :=
  (BitVec.ofBoolListLE (List.ofFn fun r : Fin M => w.getLsbD (src r).val)).cast List.length_ofFn

lemma proj_getLsbD {N M : ℕ} (src : Fin M → Fin N) (w : BitVec N) (j : ℕ) (hj : j < M) :
    (proj src w).getLsbD j = w.getLsbD (src ⟨j, hj⟩).val := by
  simp only [proj, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj, dite_true, Option.getD_some]

lemma proj_eq_iff {N M : ℕ} (src : Fin M → Fin N) (w : BitVec N) (v : BitVec M) :
    proj src w = v ↔ ∀ r : Fin M, w.getLsbD (src r).val = v.getLsbD r.val := by
  constructor
  · intro h r; rw [← h, proj_getLsbD src w r.val r.isLt]
  · intro h
    apply BitVec.eq_of_getElem_eq
    intro j hj
    rw [← BitVec.getLsbD_eq_getElem hj, ← BitVec.getLsbD_eq_getElem hj, proj_getLsbD src w j hj]
    exact h ⟨j, hj⟩

lemma proj_and {N M : ℕ} (src : Fin M → Fin N) (a b : BitVec N) :
    proj src (a &&& b) = proj src a &&& proj src b := by
  rw [proj_eq_iff]
  intro r
  rw [BitVec.getLsbD_and, BitVec.getLsbD_and, proj_getLsbD src a r.val r.isLt, proj_getLsbD src b r.val r.isLt]

lemma proj_or {N M : ℕ} (src : Fin M → Fin N) (a b : BitVec N) :
    proj src (a ||| b) = proj src a ||| proj src b := by
  rw [proj_eq_iff]
  intro r
  rw [BitVec.getLsbD_or, BitVec.getLsbD_or, proj_getLsbD src a r.val r.isLt, proj_getLsbD src b r.val r.isLt]

lemma proj_not {N M : ℕ} (src : Fin M → Fin N) (a : BitVec N) :
    proj src (~~~a) = ~~~(proj src a) := by
  rw [proj_eq_iff]
  intro r
  rw [BitVec.getLsbD_not, BitVec.getLsbD_not, proj_getLsbD src a r.val r.isLt]
  simp only [r.isLt, (src r).isLt, decide_true, Bool.true_and]

lemma proj_ops {N M : ℕ} (src : Fin M → Fin N) (a b z : BitVec N) (hz : z ∈ basicOpsN a b) :
    proj src z ∈ basicOpsN (proj src a) (proj src b) := by
  simp only [basicOpsN, opsN, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
  rcases hz with rfl | rfl | rfl | rfl
  · exact .inl (proj_and src a b)
  · exact .inr (.inl (proj_or src a b))
  · exact .inr (.inr (.inl (by rw [proj_and, proj_not])))
  · exact .inr (.inr (.inr (by rw [proj_and, proj_not])))

def isConstB {M : ℕ} (u : BitVec M) : Bool := (u == 0) || (u == ~~~0)

lemma isConstB_iff {M : ℕ} (u : BitVec M) : isConstB u = true ↔ u = 0 ∨ u = ~~~0 := by
  simp [isConstB]

def constCount {N M : ℕ} (src : Fin M → Fin N) (s : Finset (BitVec N)) : ℕ :=
  (s.filter fun w => isConstB (proj src w) = true).card

lemma live_transport_const_save {N M : ℕ} (src : Fin M → Fin N)
    {k : ℕ} {t : BitVec N} {s : Finset (BitVec N)} {av : Finset (BitVec M)}
    (hnc : isConstB (proj src t) = false)
    (hl : live basicOpsN t k s)
    (hcov : ∀ w ∈ s, holdsN av (proj src w)) :
    ∃ k', k' + constCount src s ≤ k ∧ SignedBuildN k' av (proj src t) := by
  induction k generalizing s av with
  | zero =>
    change s = {t} at hl
    subst hl
    have hcnt : constCount src {t} = 0 := by
      simp [constCount, hnc]
    exact ⟨0, by omega, sbN_zero (hcov t (Finset.mem_singleton_self t))⟩
  | succ k ih =>
    rcases hl with skip | ⟨a, ha, b, hb, hab, z, hz, hzout, rest, heq, tail⟩
    · obtain ⟨k', hle, hsb⟩ := ih skip hcov
      exact ⟨k', by omega, hsb⟩
    · have hpa : holdsN av (proj src a) := hcov a ha
      have hpb : holdsN av (proj src b) := hcov b hb
      have hpz : proj src z ∈ basicOpsN (proj src a) (proj src b) := proj_ops src a b z hz
      have hrest_sub : rest ⊆ s := fun u hu => heq ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu)
      have hz_nrest : z ∉ rest := fun hu => hzout (hrest_sub hu)
      by_cases hca : isConstB (proj src a) = true
      · have hconst_z : holdsN av (proj src z) :=
          mem_ops_constN hpa hpb (.inl ((isConstB_iff _).mp hca)) hpz
        have hcov' : ∀ w ∈ insert z rest, holdsN av (proj src w) := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hr
          · exact hconst_z
          · exact hcov w (hrest_sub hr)
        obtain ⟨k', hle, hsb⟩ := ih tail hcov'
        have hdrop : constCount src s ≤ constCount src (insert z rest) + 1 := by
          by_cases hcb : isConstB (proj src b) = true
          · have hcz : isConstB (proj src z) = true :=
              (isConstB_iff _).mpr (opsN_const_both ((isConstB_iff _).mp hca) ((isConstB_iff _).mp hcb) hpz)
            have h1 : (s.filter fun w => isConstB (proj src w) = true) ⊆
                insert a (insert b (rest.filter fun w => isConstB (proj src w) = true)) := by
              intro w hw
              rcases Finset.mem_filter.mp hw with ⟨hws, hwc⟩
              rw [heq] at hws
              rcases Finset.mem_insert.mp hws with rfl | hws
              · exact Finset.mem_insert_self _ _
              · rcases Finset.mem_insert.mp hws with rfl | hwr
                · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
                · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hwr, hwc⟩))
            have h2 : ((insert z rest).filter fun w => isConstB (proj src w) = true) =
                insert z (rest.filter fun w => isConstB (proj src w) = true) := by
              ext w
              simp only [Finset.mem_filter, Finset.mem_insert]
              constructor
              · rintro ⟨rfl | hwr, hwc⟩
                · exact .inl rfl
                · exact .inr ⟨hwr, hwc⟩
              · rintro (rfl | ⟨hwr, hwc⟩)
                · exact ⟨.inl rfl, hcz⟩
                · exact ⟨.inr hwr, hwc⟩
            have hcard1 := Finset.card_le_card h1
            have hcard_ins1 := Finset.card_insert_le a (insert b (rest.filter fun w => isConstB (proj src w) = true))
            have hcard_ins2 := Finset.card_insert_le b (rest.filter fun w => isConstB (proj src w) = true)
            have hzn : z ∉ rest.filter (fun w => isConstB (proj src w) = true) :=
              fun hu => hz_nrest (Finset.mem_filter.mp hu).1
            have hcard2 : constCount src (insert z rest) =
                (rest.filter fun w => isConstB (proj src w) = true).card + 1 := by
              dsimp only [constCount]
              rw [h2, Finset.card_insert_of_notMem hzn]
            dsimp only [constCount] at hcard1 hcard2 ⊢
            omega
          · have h1 : (s.filter fun w => isConstB (proj src w) = true) ⊆
                insert a ((insert z rest).filter fun w => isConstB (proj src w) = true) := by
              intro w hw
              rcases Finset.mem_filter.mp hw with ⟨hws, hwc⟩
              rw [heq] at hws
              rcases Finset.mem_insert.mp hws with rfl | hws
              · exact Finset.mem_insert_self _ _
              · rcases Finset.mem_insert.mp hws with rfl | hwr
                · exact False.elim (hcb hwc)
                · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem hwr, hwc⟩)
            have hcard1 := Finset.card_le_card h1
            have hcard_ins := Finset.card_insert_le a ((insert z rest).filter fun w => isConstB (proj src w) = true)
            dsimp only [constCount] at hcard1 ⊢
            omega
        exact ⟨k', by omega, hsb⟩
      · by_cases hcb : isConstB (proj src b) = true
        · have hconst_z : holdsN av (proj src z) :=
            mem_ops_constN hpa hpb (.inr ((isConstB_iff _).mp hcb)) hpz
          have hcov' : ∀ w ∈ insert z rest, holdsN av (proj src w) := by
            intro w hw
            rcases Finset.mem_insert.mp hw with rfl | hr
            · exact hconst_z
            · exact hcov w (hrest_sub hr)
          obtain ⟨k', hle, hsb⟩ := ih tail hcov'
          have h1 : (s.filter fun w => isConstB (proj src w) = true) ⊆
              insert b ((insert z rest).filter fun w => isConstB (proj src w) = true) := by
            intro w hw
            rcases Finset.mem_filter.mp hw with ⟨hws, hwc⟩
            rw [heq] at hws
            rcases Finset.mem_insert.mp hws with rfl | hws
            · exact False.elim (hca hwc)
            · rcases Finset.mem_insert.mp hws with rfl | hwr
              · exact Finset.mem_insert_self _ _
              · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem hwr, hwc⟩)
          have hcard1 := Finset.card_le_card h1
          have hcard_ins := Finset.card_insert_le b ((insert z rest).filter fun w => isConstB (proj src w) = true)
          have hdrop : constCount src s ≤ constCount src (insert z rest) + 1 := by
            dsimp only [constCount] at hcard1 ⊢; omega
          exact ⟨k', by omega, hsb⟩
        · have hsub_cnt : (s.filter fun w => isConstB (proj src w) = true) ⊆
              ((insert z rest).filter fun w => isConstB (proj src w) = true) := by
            intro w hw
            rcases Finset.mem_filter.mp hw with ⟨hws, hwc⟩
            rw [heq] at hws
            rcases Finset.mem_insert.mp hws with rfl | hws
            · exact False.elim (hca hwc)
            · rcases Finset.mem_insert.mp hws with rfl | hwr
              · exact False.elim (hcb hwc)
              · exact Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem hwr, hwc⟩
          have hcnt_le : constCount src s ≤ constCount src (insert z rest) := Finset.card_le_card hsub_cnt
          rcases mem_ops_reachN hpa hpb hpz with hhold | ⟨u, hu, v, hv, huv, w, hwu, hzw⟩
          · have hcov' : ∀ x ∈ insert z rest, holdsN av (proj src x) := by
              intro x hx
              rcases Finset.mem_insert.mp hx with rfl | hr
              · exact hhold
              · exact hcov x (hrest_sub hr)
            obtain ⟨k', hle, hsb⟩ := ih tail hcov'
            exact ⟨k', by omega, hsb⟩
          · have hcov' : ∀ x ∈ insert z rest, holdsN (insert w av) (proj src x) := by
              intro x hx
              rcases Finset.mem_insert.mp hx with rfl | hr
              · exact hzw
              · exact holdsN_mono (Finset.subset_insert _ _) (hcov x (hrest_sub hr))
            obtain ⟨k', hle, hsb⟩ := ih tail hcov'
            exact ⟨k' + 1, by omega, sbN_step hu hv huv hwu hsb⟩

def differsBit {N : ℕ} (r0 r1 : Fin N) (w : BitVec N) : Prop :=
  w.getLsbD r0.val ≠ w.getLsbD r1.val

lemma opsN_differsBit {N : ℕ} (r0 r1 : Fin N) (a b z : BitVec N) (hz : z ∈ basicOpsN a b)
    (hd : differsBit r0 r1 z) : differsBit r0 r1 a ∨ differsBit r0 r1 b := by
  by_contra h
  rw [not_or] at h
  obtain ⟨ha, hb⟩ := h
  simp only [differsBit, not_not] at ha hb
  simp only [basicOpsN, opsN, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  apply hd
  rcases hz with rfl | rfl | rfl | rfl
  · simp only [BitVec.getLsbD_and, ha, hb]
  · simp only [BitVec.getLsbD_or, ha, hb]
  · simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, r0.isLt, r1.isLt, decide_true, Bool.true_and, ha, hb]
  · simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, r0.isLt, r1.isLt, decide_true, Bool.true_and, ha, hb]

def projEqB {N M : ℕ} (src : Fin M → Fin N) (w : BitVec N) (v : BitVec M) : Bool :=
  (List.finRange M).all fun r => w.getLsbD (src r).val == v.getLsbD r.val

lemma proj_eq_of_projEqB {N M : ℕ} (src : Fin M → Fin N) (w : BitVec N) (v : BitVec M)
    (h : projEqB src w v = true) : proj src w = v := by
  rw [proj_eq_iff]
  intro r
  have h1 := List.all_eq_true.mp h r (List.mem_finRange r)
  exact beq_iff_eq.mp h1

def projConstB {N M : ℕ} (src : Fin M → Fin N) (w : BitVec N) : Bool :=
  ((List.finRange M).all fun r => !w.getLsbD (src r).val) ||
  ((List.finRange M).all fun r => w.getLsbD (src r).val)

lemma isConstB_proj_of_projConstB {N M : ℕ} (src : Fin M → Fin N) (w : BitVec N)
    (h : projConstB src w = true) : isConstB (proj src w) = true := by
  rw [isConstB_iff]
  simp only [projConstB, Bool.or_eq_true] at h
  rcases h with h0 | h1
  · left
    rw [proj_eq_iff]
    intro r
    have hr := List.all_eq_true.mp h0 r (List.mem_finRange r)
    simp only [Bool.not_eq_true'] at hr
    rw [hr, bv_getLsbD_zero]
  · right
    rw [proj_eq_iff]
    intro r
    have hr := List.all_eq_true.mp h1 r (List.mem_finRange r)
    rw [hr, BitVec.getLsbD_not, bv_getLsbD_zero]
    simp [r.isLt]

def projHoldsB {N M : ℕ} (src : Fin M → Fin N) (av : List (BitVec M)) (w : BitVec N) : Bool :=
  projConstB src w || av.any fun a => projEqB src w a || projEqB src w (~~~a)

lemma holdsN_proj_of_projHoldsB {N M : ℕ} (src : Fin M → Fin N) (av : List (BitVec M)) (w : BitVec N)
    (h : projHoldsB src av w = true) : holdsN av.toFinset (proj src w) := by
  simp only [projHoldsB, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with hc | ⟨a, ha, heq⟩
  · exact ((isConstB_iff _).mp (isConstB_proj_of_projConstB src w hc)).imp_right Or.inl
  · rcases heq with h1 | h2
    · exact .inr (.inr ⟨a, List.mem_toFinset.mpr ha, .inl (proj_eq_of_projEqB src w a h1)⟩)
    · exact .inr (.inr ⟨a, List.mem_toFinset.mpr ha, .inr (proj_eq_of_projEqB src w (~~~a) h2)⟩)

lemma sbN_k4_false {k : ℕ} (hk : k ≤ 6) {t : W4} (ht : t = goal4 ∨ t = ~~~goal4)
    (hsb : SignedBuildN k k4inputs.toFinset t) : False := by
  have hsb6 : SignedBuild4 6 k4inputs.toFinset t := sbN_le hk hsb
  rcases ht with rfl | rfl
  · exact k4_no_signed6 hsb6
  · exact k4_no_signed6 (sb4_not hsb6)

lemma sbN_k5_false {k : ℕ} (hk : k ≤ 9) {t : W5} (ht : t = goal5 ∨ t = ~~~goal5)
    (hsb : SignedBuildN k in5.toFinset t) : False := by
  have hsb9 : SignedBuildN 9 in5.toFinset t := sbN_le hk hsb
  have hne0 : goal5 ≠ 0 := by decide
  have hne1 : goal5 ≠ ~~~0 := by decide
  rcases hsb9 with h0 | h1 | run | run
  · rcases ht with rfl | rfl
    · exact hne0 h0
    · exact hne1 (by rw [← BitVec.not_not (b := goal5), h0])
  · rcases ht with rfl | rfl
    · exact hne1 h1
    · exact hne0 (by rw [← BitVec.not_not (b := goal5), h1, BitVec.not_not])
  · exact no_nine_binary t ht run
  · refine no_nine_binary (~~~t) ?_ run
    rcases ht with rfl | rfl
    · exact .inr rfl
    · exact .inl BitVec.not_not

def row4Tbl : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 3, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 3, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 3, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 3, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 3, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15]

def insBit4 (d : Fin 5) (val : Bool) (r4 : ℕ) : Fin 32 :=
  let lo := r4 % (2 ^ d.val)
  let hi := r4 / (2 ^ d.val)
  ⟨(lo + (if val then 2 ^ d.val else 0) + hi * (2 ^ (d.val + 1))) % 32, Nat.mod_lt _ (by decide)⟩

def srcK4 (d : Fin 5) (r : Fin 110) : Fin 32 := insBit4 d true (row4Tbl.getD r.val 0)
def srcDK4 (d : Fin 5) (r : Fin 110) : Fin 32 := insBit4 d false (15 - row4Tbl.getD r.val 0)
def srcM5 (d : Fin 5) (val : Bool) : Fin 110 → Fin 32 := if val then srcK4 d else srcDK4 d

def in32 : List (BitVec 32) := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]
def v32 (i : Fin 5) : BitVec 32 := in32.getD i.val 0

lemma in32_index : ∀ w ∈ in32, ∃ i : Fin 5, v32 i = w := by
  intro w hw
  simp only [in32, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩

def goalM5 : BitVec 32 := BitVec.ofNat 32 0xfee8e880
def goal41 : BitVec 32 := BitVec.ofNat 32 0xfee8e800

lemma m5_in_not_goal : ∀ i : Fin 5, v32 i ≠ goalM5 ∧ v32 i ≠ ~~~goalM5 := by decide +kernel
lemma m5_proj_goal : ∀ (d : Fin 5) (val : Bool),
    projEqB (srcM5 d val) goalM5 goal4 = true ∨ projEqB (srcM5 d val) goalM5 (~~~goal4) = true := by
  decide +kernel
lemma m5_proj_in : ∀ (d : Fin 5) (val : Bool) (i : Fin 5),
    projHoldsB (srcM5 d val) k4inputs (v32 i) = true := by decide +kernel

def pickM5 (i j : Fin 5) (o : Fin 4) : Fin 5 × Bool :=
  match o.val with
  | 0 => (i, false)
  | 1 => (i, true)
  | 2 => (i, false)
  | _ => (j, false)

lemma m5_pick_mem : ∀ (i j : Fin 5) (o : Fin 4),
    (pickM5 i j o).1 = i ∨ (pickM5 i j o).1 = j := by decide +kernel

lemma m5_pick_const : ∀ (i j : Fin 5), i ≠ j → ∀ o : Fin 4,
    let dv := pickM5 i j o
    projConstB (srcM5 dv.1 dv.2) (v32 dv.1) = true ∧
    projConstB (srcM5 dv.1 dv.2) ((opsN (v32 i) (v32 j)).getD o.val 0) = true := by decide +kernel

set_option maxRecDepth 8000 in
lemma m5_sep : ∀ (i j : Fin 5), i ≠ j → ∀ o : Fin 4,
    let d := (pickM5 i j o).1
    ∃ r0 r1 : Fin 32,
      goalM5.getLsbD r0.val ≠ goalM5.getLsbD r1.val ∧
      ((opsN (v32 i) (v32 j)).getD o.val 0).getLsbD r0.val = ((opsN (v32 i) (v32 j)).getD o.val 0).getLsbD r1.val ∧
      ∀ q : Fin 5, q ≠ d → (v32 q).getLsbD r0.val = (v32 q).getLsbD r1.val := by decide +kernel

lemma goal_differsBit {N : ℕ} {g t : BitVec N} (ht : t = g ∨ t = ~~~g)
    {r0 r1 : Fin N} (hd : g.getLsbD r0.val ≠ g.getLsbD r1.val) : differsBit r0 r1 t := by
  rcases ht with rfl | rfl
  · exact hd
  · simp only [differsBit, BitVec.getLsbD_not, r0.isLt, r1.isLt, decide_true, Bool.true_and, ne_eq, Bool.not_inj_iff]
    exact hd

lemma constCount_ge_two {N M : ℕ} (src : Fin M → Fin N) {s : Finset (BitVec N)}
    {u v : BitVec N} (hu : u ∈ s) (hv : v ∈ s) (hne : u ≠ v)
    (hcu : isConstB (proj src u) = true) (hcv : isConstB (proj src v) = true) :
    2 ≤ constCount src s := by
  have hsub : ({u, v} : Finset (BitVec N)) ⊆ s.filter (fun w => isConstB (proj src w) = true) := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact Finset.mem_filter.mpr ⟨hu, hcu⟩
    · rcases Finset.mem_singleton.mp hw with rfl
      exact Finset.mem_filter.mpr ⟨hv, hcv⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_pair hne] at hc
  exact hc

lemma constCount_ge_one {N M : ℕ} (src : Fin M → Fin N) {s : Finset (BitVec N)}
    {u : BitVec N} (hu : u ∈ s) (hcu : isConstB (proj src u) = true) :
    1 ≤ constCount src s := by
  have hmem : u ∈ s.filter (fun w => isConstB (proj src w) = true) := Finset.mem_filter.mpr ⟨hu, hcu⟩
  exact Finset.one_le_card.mpr ⟨u, hmem⟩

lemma goal4_nc : isConstB goal4 = false ∧ isConstB (~~~goal4) = false := by decide +kernel
lemma goal5_nc : isConstB goal5 = false ∧ isConstB (~~~goal5) = false := by decide +kernel
lemma goalM5_nc : isConstB goalM5 = false ∧ isConstB (~~~goalM5) = false := by decide +kernel
lemma goal41_nc : isConstB goal41 = false ∧ isConstB (~~~goal41) = false := by decide +kernel

theorem no_nine_maj5 {t : BitVec 32} (ht : t = goalM5 ∨ t = ~~~goalM5)
    (run : build basicOpsN t 9 in32.toFinset) : False := by
  obtain ⟨s, hs, hl⟩ := compress run
  rcases first_live (k := 8) hl with endcase | ⟨a, ha, b, hb, hab, z, hz, hzout, rest, he, tail⟩
  · have htin : t ∈ s := by simp [endcase]
    obtain ⟨i, hi⟩ := in32_index _ (List.mem_toFinset.mp (hs htin))
    rcases ht with rfl | rfl
    · exact (m5_in_not_goal i).1 hi
    · exact (m5_in_not_goal i).2 hi
  · obtain ⟨i, rfl⟩ := in32_index _ (List.mem_toFinset.mp (hs ha))
    obtain ⟨j, rfl⟩ := in32_index _ (List.mem_toFinset.mp (hs hb))
    have hij : i ≠ j := fun eq => hab (congrArg v32 eq)
    obtain ⟨o, ho⟩ := index_of_opN _ _ _ hz
    have hrest_sub : rest ⊆ in32.toFinset :=
      fun w hw => hs (he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw))
    let d := (pickM5 i j o).1
    let val := (pickM5 i j o).2
    let src := srcM5 d val
    obtain ⟨r0, r1, hdg, hdz, hdq⟩ := m5_sep i j hij o
    rw [ho] at hdz
    have hd_mem : v32 d ∈ rest := by
      obtain ⟨w, hw, hdw⟩ := live_separates (differsBit r0 r1) (goal_differsBit ht hdg) (opsN_differsBit r0 r1) tail
      rcases Finset.mem_insert.mp hw with rfl | hwr
      · exact False.elim (hdw hdz)
      · obtain ⟨q, rfl⟩ := in32_index _ (List.mem_toFinset.mp (hrest_sub hwr))
        by_cases hqd : q = d
        · subst hqd; exact hwr
        · exact False.elim (hdw (hdq q hqd))
    have hconsts := m5_pick_const i j hij o
    have hcd : isConstB (proj src (v32 d)) = true := isConstB_proj_of_projConstB src (v32 d) hconsts.1
    have hcz : isConstB (proj src z) = true := isConstB_proj_of_projConstB src z (ho ▸ hconsts.2)
    have hne : z ≠ v32 d := fun eq => hzout (eq ▸ (he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hd_mem)))
    have hcnt : 2 ≤ constCount src (insert z rest) :=
      constCount_ge_two src (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hd_mem) hne hcz hcd
    have hpg : proj src t = goal4 ∨ proj src t = ~~~goal4 := by
      rcases m5_proj_goal d val with h | h
      · have h' := proj_eq_of_projEqB src goalM5 goal4 h
        rcases ht with rfl | rfl
        · exact .inl h'
        · exact .inr (by rw [proj_not, h'])
      · have h' := proj_eq_of_projEqB src goalM5 (~~~goal4) h
        rcases ht with rfl | rfl
        · exact .inr h'
        · exact .inl (by rw [proj_not, h', BitVec.not_not])
    have hnc : isConstB (proj src t) = false := by
      rcases hpg with h | h <;> rw [h]
      · exact goal4_nc.1
      · exact goal4_nc.2
    have hcov : ∀ w ∈ insert z rest, holdsN k4inputs.toFinset (proj src w) := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hwr
      · exact ((isConstB_iff _).mp hcz).imp_right Or.inl
      · obtain ⟨q, rfl⟩ := in32_index _ (List.mem_toFinset.mp (hrest_sub hwr))
        exact holdsN_proj_of_projHoldsB src k4inputs (v32 q) (m5_proj_in d val q)
    obtain ⟨k', hle, hsb⟩ := live_transport_const_save src hnc tail hcov
    exact sbN_k4_false (by omega) hpg hsb

def src41 (d : Fin 5) : Fin 110 → Fin 32 := if d.val < 3 then srcDK4 d else srcK4 d

lemma f41_in_not_goal : ∀ i : Fin 5, v32 i ≠ goal41 ∧ v32 i ≠ ~~~goal41 := by decide +kernel
lemma f41_proj_goal : ∀ d : Fin 5,
    projEqB (src41 d) goal41 goal4 = true ∨ projEqB (src41 d) goal41 (~~~goal4) = true := by
  decide +kernel
lemma f41_proj_in : ∀ (d i : Fin 5),
    projHoldsB (src41 d) k4inputs (v32 i) = true := by decide +kernel
lemma f41_proj_const : ∀ d : Fin 5, projConstB (src41 d) (v32 d) = true := by decide +kernel

set_option maxRecDepth 8000 in
lemma f41_sep : ∀ (i j : Fin 5), i ≠ j → ∀ o : Fin 4,
    ∃ r0 r1 : Fin 32,
      goal41.getLsbD r0.val ≠ goal41.getLsbD r1.val ∧
      ((opsN (v32 i) (v32 j)).getD o.val 0).getLsbD r0.val = ((opsN (v32 i) (v32 j)).getD o.val 0).getLsbD r1.val ∧
      ∀ q : Fin 5, q ≠ i → (v32 q).getLsbD r0.val = (v32 q).getLsbD r1.val := by decide +kernel

theorem no_eight_f41 {t : BitVec 32} (ht : t = goal41 ∨ t = ~~~goal41)
    (run : build basicOpsN t 8 in32.toFinset) : False := by
  obtain ⟨s, hs, hl⟩ := compress run
  rcases first_live (k := 7) hl with endcase | ⟨a, ha, b, hb, hab, z, hz, _, rest, he, tail⟩
  · have htin : t ∈ s := by simp [endcase]
    obtain ⟨i, hi⟩ := in32_index _ (List.mem_toFinset.mp (hs htin))
    rcases ht with rfl | rfl
    · exact (f41_in_not_goal i).1 hi
    · exact (f41_in_not_goal i).2 hi
  · obtain ⟨i, rfl⟩ := in32_index _ (List.mem_toFinset.mp (hs ha))
    obtain ⟨j, rfl⟩ := in32_index _ (List.mem_toFinset.mp (hs hb))
    have hij : i ≠ j := fun eq => hab (congrArg v32 eq)
    obtain ⟨o, ho⟩ := index_of_opN _ _ _ hz
    have hrest_sub : rest ⊆ in32.toFinset :=
      fun w hw => hs (he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw))
    let src := src41 i
    obtain ⟨r0, r1, hdg, hdz, hdq⟩ := f41_sep i j hij o
    rw [ho] at hdz
    have hi_mem : v32 i ∈ rest := by
      obtain ⟨w, hw, hdw⟩ := live_separates (differsBit r0 r1) (goal_differsBit ht hdg) (opsN_differsBit r0 r1) tail
      rcases Finset.mem_insert.mp hw with rfl | hwr
      · exact False.elim (hdw hdz)
      · obtain ⟨q, rfl⟩ := in32_index _ (List.mem_toFinset.mp (hrest_sub hwr))
        by_cases hqi : q = i
        · subst hqi; exact hwr
        · exact False.elim (hdw (hdq q hqi))
    have hci : isConstB (proj src (v32 i)) = true := isConstB_proj_of_projConstB src (v32 i) (f41_proj_const i)
    have hcnt : 1 ≤ constCount src (insert z rest) :=
      constCount_ge_one src (Finset.mem_insert_of_mem hi_mem) hci
    have hpg : proj src t = goal4 ∨ proj src t = ~~~goal4 := by
      rcases f41_proj_goal i with h | h
      · have h' := proj_eq_of_projEqB src goal41 goal4 h
        rcases ht with rfl | rfl
        · exact .inl h'
        · exact .inr (by rw [proj_not, h'])
      · have h' := proj_eq_of_projEqB src goal41 (~~~goal4) h
        rcases ht with rfl | rfl
        · exact .inr h'
        · exact .inl (by rw [proj_not, h', BitVec.not_not])
    have hnc : isConstB (proj src t) = false := by
      rcases hpg with h | h <;> rw [h]
      · exact goal4_nc.1
      · exact goal4_nc.2
    have hcov : ∀ w ∈ insert z rest, holdsN k4inputs.toFinset (proj src w) := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hwr
      · exact mem_ops_constN
          (holdsN_proj_of_projHoldsB src k4inputs (v32 i) (f41_proj_in i i))
          (holdsN_proj_of_projHoldsB src k4inputs (v32 j) (f41_proj_in i j))
          (.inl ((isConstB_iff _).mp hci)) (proj_ops src _ _ _ hz)
      · obtain ⟨q, rfl⟩ := in32_index _ (List.mem_toFinset.mp (hrest_sub hwr))
        exact holdsN_proj_of_projHoldsB src k4inputs (v32 q) (f41_proj_in i q)
    obtain ⟨k', hle, hsb⟩ := live_transport_const_save src hnc tail hcov
    exact sbN_k4_false (by omega) hpg hsb

lemma sbN_maj5_false {k : ℕ} (hk : k ≤ 9) {t : BitVec 32} (ht : t = goalM5 ∨ t = ~~~goalM5)
    (hsb : SignedBuildN k in32.toFinset t) : False := by
  have hsb9 := sbN_le hk hsb
  have hne0 : goalM5 ≠ 0 := by decide
  have hne1 : goalM5 ≠ ~~~0 := by decide
  rcases hsb9 with h0 | h1 | run | run
  · rcases ht with rfl | rfl
    · exact hne0 h0
    · exact hne1 (by rw [← BitVec.not_not (b := goalM5), h0])
  · rcases ht with rfl | rfl
    · exact hne1 h1
    · exact hne0 (by rw [← BitVec.not_not (b := goalM5), h1, BitVec.not_not])
  · exact no_nine_maj5 ht run
  · refine no_nine_maj5 ?_ run
    rcases ht with rfl | rfl
    · exact .inr rfl
    · exact .inl BitVec.not_not

lemma sbN_f41_false {k : ℕ} (hk : k ≤ 8) {t : BitVec 32} (ht : t = goal41 ∨ t = ~~~goal41)
    (hsb : SignedBuildN k in32.toFinset t) : False := by
  have hsb8 := sbN_le hk hsb
  have hne0 : goal41 ≠ 0 := by decide
  have hne1 : goal41 ≠ ~~~0 := by decide
  rcases hsb8 with h0 | h1 | run | run
  · rcases ht with rfl | rfl
    · exact hne0 h0
    · exact hne1 (by rw [← BitVec.not_not (b := goal41), h0])
  · rcases ht with rfl | rfl
    · exact hne1 h1
    · exact hne0 (by rw [← BitVec.not_not (b := goal41), h1, BitVec.not_not])
  · exact no_eight_f41 ht run
  · refine no_eight_f41 ?_ run
    rcases ht with rfl | rfl
    · exact .inr rfl
    · exact .inl BitVec.not_not

def goal6 : BitVec 64 := BitVec.ofNat 64 (4276676608 * 2 ^ 32 + 3892346880)
def in6 : List (BitVec 64) :=
  [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0,
   0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
def v6 (i : Fin 6) : BitVec 64 := in6.getD i.val 0
def z1_6 : BitVec 64 := v6 4 &&& v6 5
def s1List : List (BitVec 64) := [z1_6, v6 0, v6 1, v6 2, v6 3, v6 4, v6 5]
def s1v (i : Fin 7) : BitVec 64 := s1List.getD i.val 0

lemma in6_index : ∀ w ∈ in6, ∃ i : Fin 6, v6 i = w := by
  intro w hw
  simp only [in6, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩
  · exact ⟨5, rfl⟩

lemma s1_index : ∀ w ∈ s1List, ∃ i : Fin 7, s1v i = w := by
  intro w hw
  simp only [s1List, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩
  · exact ⟨5, rfl⟩
  · exact ⟨6, rfl⟩

def insBit5 (d : Fin 6) (val : Bool) (r5 : ℕ) : Fin 64 :=
  let lo := r5 % (2 ^ d.val)
  let hi := r5 / (2 ^ d.val)
  ⟨(lo + (if val then 2 ^ d.val else 0) + hi * (2 ^ (d.val + 1))) % 64, Nat.mod_lt _ (by decide)⟩

def srcToK5 (d : Fin 3) (r : Fin 152) : Fin 64 :=
  insBit5 ⟨d.val, by omega⟩ false (31 - row5Tbl.getD r.val 0)
def srcToM5 (r : Fin 32) : Fin 64 := insBit5 3 true r.val
def srcToF41 (e : Fin 2) (r : Fin 32) : Fin 64 := insBit5 ⟨4 + e.val, by omega⟩ true r.val

lemma f6_in_not_goal : ∀ i : Fin 6, v6 i ≠ goal6 ∧ v6 i ≠ ~~~goal6 := by decide +kernel
lemma f6_s1_not_goal : ∀ i : Fin 7, s1v i ≠ goal6 ∧ s1v i ≠ ~~~goal6 := by decide +kernel

lemma f6_proj_k5_goal : ∀ d : Fin 3, projEqB (srcToK5 d) goal6 (~~~goal5) = true := by decide +kernel
lemma f6_proj_k5_in : ∀ (d : Fin 3) (i : Fin 6), projHoldsB (srcToK5 d) in5 (v6 i) = true := by decide +kernel
lemma f6_proj_k5_const : ∀ d : Fin 3, projConstB (srcToK5 d) (v6 ⟨d.val, by omega⟩) = true := by decide +kernel
lemma f6_proj_k5_z1 : ∀ d : Fin 3, projEqB (srcToK5 d) z1_6 (~~~(x3 ||| x4)) = true := by decide +kernel
lemma x3_ne_x4 : x3 ≠ x4 := by decide

lemma f6_proj_m5_goal : projEqB srcToM5 goal6 goalM5 = true := by decide +kernel
lemma f6_proj_m5_in : ∀ i : Fin 6, projHoldsB srcToM5 in32 (v6 i) = true := by decide +kernel
lemma f6_proj_m5_const : projConstB srcToM5 (v6 3) = true := by decide +kernel
lemma f6_proj_m5_z1 : projEqB srcToM5 z1_6 (v32 3 &&& v32 4) = true := by decide +kernel
lemma v32_3_ne_4 : v32 3 ≠ v32 4 := by decide

lemma f6_proj_f41_goal : ∀ e : Fin 2, projEqB (srcToF41 e) goal6 goal41 = true := by decide +kernel
lemma f6_proj_f41_in : ∀ (e : Fin 2) (i : Fin 6), projHoldsB (srcToF41 e) in32 (v6 i) = true := by decide +kernel
lemma f6_proj_f41_s1 : ∀ (e : Fin 2) (i : Fin 7), projHoldsB (srcToF41 e) in32 (s1v i) = true := by decide +kernel
lemma f6_proj_f41_const : ∀ e : Fin 2, projConstB (srcToF41 e) (v6 ⟨4 + e.val, by omega⟩) = true := by decide +kernel

lemma f6_step1_45_const :
    projConstB (srcToF41 0) (v6 4 ||| v6 5) = true ∧
    projConstB (srcToF41 1) (v6 4 &&& ~~~v6 5) = true ∧
    projConstB (srcToF41 0) (v6 5 &&& ~~~v6 4) = true := by decide +kernel

set_option maxRecDepth 16000 in
lemma f6_sep1 : ∀ (i j : Fin 6), i ≠ j → ∀ o : Fin 4, ∀ d : Fin 6, (d = i ∨ d = j) →
    ∃ r0 r1 : Fin 64,
      goal6.getLsbD r0.val ≠ goal6.getLsbD r1.val ∧
      ((opsN (v6 i) (v6 j)).getD o.val 0).getLsbD r0.val = ((opsN (v6 i) (v6 j)).getD o.val 0).getLsbD r1.val ∧
      ∀ q : Fin 6, q ≠ d → (v6 q).getLsbD r0.val = (v6 q).getLsbD r1.val := by decide +kernel

set_option maxRecDepth 8000 in
lemma f6_sep_z1 : ∀ d : Fin 6,
    ∃ r0 r1 : Fin 64,
      goal6.getLsbD r0.val ≠ goal6.getLsbD r1.val ∧
      z1_6.getLsbD r0.val = z1_6.getLsbD r1.val ∧
      ∀ q : Fin 6, q ≠ d → (v6 q).getLsbD r0.val = (v6 q).getLsbD r1.val := by decide +kernel

set_option maxRecDepth 32000 in
lemma f6_step2_k5_check : ∀ (d : Fin 3) (b : Fin 7), b.val ≠ d.val + 1 → ∀ o : Fin 4,
    let z2 := (opsN (v6 ⟨d.val, by omega⟩) (s1v b)).getD o.val 0
    projConstB (srcToK5 d) z2 = true ∨
    ∃ r0 r1 : Fin 64,
      goal6.getLsbD r0.val ≠ goal6.getLsbD r1.val ∧
      z1_6.getLsbD r0.val = z1_6.getLsbD r1.val ∧
      z2.getLsbD r0.val = z2.getLsbD r1.val ∧
      ∀ q : Fin 6, q.val ≠ d.val → (v6 q).getLsbD r0.val = (v6 q).getLsbD r1.val := by decide +kernel

set_option maxRecDepth 16000 in
lemma f6_step2_m5_check : ∀ (b : Fin 7), b.val ≠ 4 → ∀ o : Fin 4,
    let z2 := (opsN (v6 3) (s1v b)).getD o.val 0
    projConstB srcToM5 z2 = true ∨
    ∃ r0 r1 : Fin 64,
      goal6.getLsbD r0.val ≠ goal6.getLsbD r1.val ∧
      z1_6.getLsbD r0.val = z1_6.getLsbD r1.val ∧
      z2.getLsbD r0.val = z2.getLsbD r1.val ∧
      ∀ q : Fin 6, q.val ≠ 3 → (v6 q).getLsbD r0.val = (v6 q).getLsbD r1.val := by decide +kernel

lemma f6_step2_45_check : ∀ (i j : Fin 7),
    (i.val = 0 ∨ i.val = 5 ∨ i.val = 6) → (j.val = 0 ∨ j.val = 5 ∨ j.val = 6) → i ≠ j → ∀ o : Fin 4,
    let z2 := (opsN (s1v i) (s1v j)).getD o.val 0
    s1List.elem z2 = true ∨ projConstB (srcToF41 0) z2 = true ∨ projConstB (srcToF41 1) z2 = true := by decide +kernel

lemma step2_kill_k5 {t : BitVec 64} (ht : t = goal6 ∨ t = ~~~goal6)
    (d : Fin 3) (b : Fin 7) (hbne : b.val ≠ d.val + 1)
    {z2 : BitVec 64} (hz2 : z2 ∈ basicOpsN (v6 ⟨d.val, by omega⟩) (s1v b))
    {rest2 : Finset (BitVec 64)} (hrest2_sub : rest2 ⊆ s1List.toFinset)
    (tail2 : live basicOpsN t 9 (insert z2 rest2)) : False := by
  let src := srcToK5 d
  let vd := v6 ⟨d.val, by omega⟩
  obtain ⟨o, ho⟩ := index_of_opN _ _ _ hz2
  have hcnt : 1 ≤ constCount src (insert z2 rest2) := by
    rcases f6_step2_k5_check d b hbne o with hcz | ⟨r0, r1, hdg, hdz1, hdz2, hdq⟩
    · rw [ho] at hcz
      exact constCount_ge_one src (Finset.mem_insert_self _ _) (isConstB_proj_of_projConstB src z2 hcz)
    · rw [ho] at hdz2
      have hvd_mem : vd ∈ rest2 := by
        obtain ⟨w, hw, hdw⟩ := live_separates (differsBit r0 r1) (goal_differsBit ht hdg) (opsN_differsBit r0 r1) tail2
        rcases Finset.mem_insert.mp hw with rfl | hwr
        · exact False.elim (hdw hdz2)
        · obtain ⟨idx, rfl⟩ := s1_index _ (List.mem_toFinset.mp (hrest2_sub hwr))
          fin_cases idx
          · exact False.elim (hdw hdz1)
          all_goals
            first
            | (by_cases heq : (0 : ℕ) = d.val
               · have : (⟨d.val, by omega⟩ : Fin 6) = 0 := Fin.ext heq.symm
                 simpa [vd, this, s1v, s1List] using hwr
               · exact False.elim (hdw (hdq 0 heq)))
            | (by_cases heq : (1 : ℕ) = d.val
               · have : (⟨d.val, by omega⟩ : Fin 6) = 1 := Fin.ext heq.symm
                 simpa [vd, this, s1v, s1List] using hwr
               · exact False.elim (hdw (hdq 1 heq)))
            | (by_cases heq : (2 : ℕ) = d.val
               · have : (⟨d.val, by omega⟩ : Fin 6) = 2 := Fin.ext heq.symm
                 simpa [vd, this, s1v, s1List] using hwr
               · exact False.elim (hdw (hdq 2 heq)))
            | exact False.elim (hdw (hdq 3 (by omega)))
            | exact False.elim (hdw (hdq 4 (by omega)))
            | exact False.elim (hdw (hdq 5 (by omega)))
      exact constCount_ge_one src (Finset.mem_insert_of_mem hvd_mem)
        (isConstB_proj_of_projConstB src vd (f6_proj_k5_const d))
  let av' : Finset W5 := insert (x3 ||| x4) in5.toFinset
  have hs1_cov : ∀ idx : Fin 7, holdsN av' (proj src (s1v idx)) := by
    intro idx
    fin_cases idx
    · have h1 := proj_eq_of_projEqB src z1_6 (~~~(x3 ||| x4)) (f6_proj_k5_z1 d)
      exact .inr (.inr ⟨x3 ||| x4, Finset.mem_insert_self _ _, .inr h1⟩)
    · exact holdsN_mono (Finset.subset_insert _ _) (holdsN_proj_of_projHoldsB src in5 (v6 0) (f6_proj_k5_in d 0))
    · exact holdsN_mono (Finset.subset_insert _ _) (holdsN_proj_of_projHoldsB src in5 (v6 1) (f6_proj_k5_in d 1))
    · exact holdsN_mono (Finset.subset_insert _ _) (holdsN_proj_of_projHoldsB src in5 (v6 2) (f6_proj_k5_in d 2))
    · exact holdsN_mono (Finset.subset_insert _ _) (holdsN_proj_of_projHoldsB src in5 (v6 3) (f6_proj_k5_in d 3))
    · exact holdsN_mono (Finset.subset_insert _ _) (holdsN_proj_of_projHoldsB src in5 (v6 4) (f6_proj_k5_in d 4))
    · exact holdsN_mono (Finset.subset_insert _ _) (holdsN_proj_of_projHoldsB src in5 (v6 5) (f6_proj_k5_in d 5))
  have hcov : ∀ w ∈ insert z2 rest2, holdsN av' (proj src w) := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hwr
    · have hcd := (isConstB_iff _).mp (isConstB_proj_of_projConstB src vd (f6_proj_k5_const d))
      exact mem_ops_constN (hcd.imp_right Or.inl) (hs1_cov b) (.inl hcd) (proj_ops src _ _ _ hz2)
    · obtain ⟨idx, rfl⟩ := s1_index _ (List.mem_toFinset.mp (hrest2_sub hwr))
      exact hs1_cov idx
  have hpg : proj src t = goal5 ∨ proj src t = ~~~goal5 := by
    have h' := proj_eq_of_projEqB src goal6 (~~~goal5) (f6_proj_k5_goal d)
    rcases ht with rfl | rfl
    · exact .inr h'
    · exact .inl (by rw [proj_not, h', BitVec.not_not])
  have hnc : isConstB (proj src t) = false := by
    rcases hpg with h | h <;> rw [h]
    · exact goal5_nc.1
    · exact goal5_nc.2
  obtain ⟨k', hle, hsb⟩ := live_transport_const_save src hnc tail2 hcov
  have hsb9 : SignedBuildN (k' + 1) in5.toFinset (proj src t) :=
    sbN_step (List.mem_toFinset.mpr (by simp [in5])) (List.mem_toFinset.mpr (by simp [in5]))
      x3_ne_x4 (by simp [basicOpsN, opsN]) hsb
  exact sbN_k5_false (by omega) hpg hsb9

lemma step2_kill_m5 {t : BitVec 64} (ht : t = goal6 ∨ t = ~~~goal6)
    (b : Fin 7) (hbne : b.val ≠ 4)
    {z2 : BitVec 64} (hz2 : z2 ∈ basicOpsN (v6 3) (s1v b))
    {rest2 : Finset (BitVec 64)} (hrest2_sub : rest2 ⊆ s1List.toFinset)
    (tail2 : live basicOpsN t 9 (insert z2 rest2)) : False := by
  let src := srcToM5
  obtain ⟨o, ho⟩ := index_of_opN _ _ _ hz2
  have hcnt : 1 ≤ constCount src (insert z2 rest2) := by
    rcases f6_step2_m5_check b hbne o with hcz | ⟨r0, r1, hdg, hdz1, hdz2, hdq⟩
    · rw [ho] at hcz
      exact constCount_ge_one src (Finset.mem_insert_self _ _) (isConstB_proj_of_projConstB src z2 hcz)
    · rw [ho] at hdz2
      have hv3_mem : v6 3 ∈ rest2 := by
        obtain ⟨w, hw, hdw⟩ := live_separates (differsBit r0 r1) (goal_differsBit ht hdg) (opsN_differsBit r0 r1) tail2
        rcases Finset.mem_insert.mp hw with rfl | hwr
        · exact False.elim (hdw hdz2)
        · obtain ⟨idx, rfl⟩ := s1_index _ (List.mem_toFinset.mp (hrest2_sub hwr))
          fin_cases idx
          · exact False.elim (hdw hdz1)
          · exact False.elim (hdw (hdq 0 (by decide)))
          · exact False.elim (hdw (hdq 1 (by decide)))
          · exact False.elim (hdw (hdq 2 (by decide)))
          · simpa [s1v, s1List] using hwr
          · exact False.elim (hdw (hdq 4 (by decide)))
          · exact False.elim (hdw (hdq 5 (by decide)))
      exact constCount_ge_one src (Finset.mem_insert_of_mem hv3_mem)
        (isConstB_proj_of_projConstB src (v6 3) f6_proj_m5_const)
  let av' : Finset (BitVec 32) := insert (v32 3 &&& v32 4) in32.toFinset
  have hs1_cov : ∀ idx : Fin 7, holdsN av' (proj src (s1v idx)) := by
    intro idx
    fin_cases idx
    · have h1 := proj_eq_of_projEqB src z1_6 (v32 3 &&& v32 4) f6_proj_m5_z1
      exact .inr (.inr ⟨v32 3 &&& v32 4, Finset.mem_insert_self _ _, .inl h1⟩)
    · exact holdsN_mono (Finset.subset_insert _ _) (holdsN_proj_of_projHoldsB src in32 (v6 0) (f6_proj_m5_in 0))
    · exact holdsN_mono (Finset.subset_insert _ _) (holdsN_proj_of_projHoldsB src in32 (v6 1) (f6_proj_m5_in 1))
    · exact holdsN_mono (Finset.subset_insert _ _) (holdsN_proj_of_projHoldsB src in32 (v6 2) (f6_proj_m5_in 2))
    · exact holdsN_mono (Finset.subset_insert _ _) (holdsN_proj_of_projHoldsB src in32 (v6 3) (f6_proj_m5_in 3))
    · exact holdsN_mono (Finset.subset_insert _ _) (holdsN_proj_of_projHoldsB src in32 (v6 4) (f6_proj_m5_in 4))
    · exact holdsN_mono (Finset.subset_insert _ _) (holdsN_proj_of_projHoldsB src in32 (v6 5) (f6_proj_m5_in 5))
  have hcov : ∀ w ∈ insert z2 rest2, holdsN av' (proj src w) := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hwr
    · have hc3 := (isConstB_iff _).mp (isConstB_proj_of_projConstB src (v6 3) f6_proj_m5_const)
      exact mem_ops_constN (hc3.imp_right Or.inl) (hs1_cov b) (.inl hc3) (proj_ops src _ _ _ hz2)
    · obtain ⟨idx, rfl⟩ := s1_index _ (List.mem_toFinset.mp (hrest2_sub hwr))
      exact hs1_cov idx
  have hpg : proj src t = goalM5 ∨ proj src t = ~~~goalM5 := by
    have h' := proj_eq_of_projEqB src goal6 goalM5 f6_proj_m5_goal
    rcases ht with rfl | rfl
    · exact .inl h'
    · exact .inr (by rw [proj_not, h'])
  have hnc : isConstB (proj src t) = false := by
    rcases hpg with h | h <;> rw [h]
    · exact goalM5_nc.1
    · exact goalM5_nc.2
  obtain ⟨k', hle, hsb⟩ := live_transport_const_save src hnc tail2 hcov
  have hsb9 : SignedBuildN (k' + 1) in32.toFinset (proj src t) :=
    sbN_step (List.mem_toFinset.mpr (by simp [in32, v32])) (List.mem_toFinset.mpr (by simp [in32, v32]))
      v32_3_ne_4 (by simp [basicOpsN, opsN]) hsb
  exact sbN_maj5_false (by omega) hpg hsb9

lemma no_ten_after_z1 {t : BitVec 64} (ht : t = goal6 ∨ t = ~~~goal6)
    (tail1 : live basicOpsN t 10 s1List.toFinset) : False := by
  rcases first_live (k := 9) tail1 with endcase | ⟨a, ha, b, hb, hab, z2, hz2, hz2out, rest2, he2, tail2⟩
  · have htin : t ∈ s1List.toFinset := by simp [endcase]
    obtain ⟨i, hi⟩ := s1_index _ (List.mem_toFinset.mp htin)
    rcases ht with rfl | rfl
    · exact (f6_s1_not_goal i).1 hi
    · exact (f6_s1_not_goal i).2 hi
  · obtain ⟨i, rfl⟩ := s1_index _ (List.mem_toFinset.mp ha)
    obtain ⟨j, rfl⟩ := s1_index _ (List.mem_toFinset.mp hb)
    have hij : i ≠ j := fun eq => hab (congrArg s1v eq)
    have hrest2_sub : rest2 ⊆ s1List.toFinset :=
      fun w hw => he2 ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw)
    by_cases hi1 : 1 ≤ i.val ∧ i.val ≤ 3
    · let d : Fin 3 := ⟨i.val - 1, by omega⟩
      have hvd : s1v i = v6 ⟨d.val, by omega⟩ := by
        have : i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
        rcases this with h | h | h
        · have : i = 1 := Fin.ext h; subst this; rfl
        · have : i = 2 := Fin.ext h; subst this; rfl
        · have : i = 3 := Fin.ext h; subst this; rfl
      rw [hvd] at hz2
      exact step2_kill_k5 ht d j (by intro h; dsimp only [d] at h; exact hij (Fin.ext (by omega))) hz2 hrest2_sub tail2
    · by_cases hj1 : 1 ≤ j.val ∧ j.val ≤ 3
      · let d : Fin 3 := ⟨j.val - 1, by omega⟩
        have hvd : s1v j = v6 ⟨d.val, by omega⟩ := by
          have : j.val = 1 ∨ j.val = 2 ∨ j.val = 3 := by omega
          rcases this with h | h | h
          · have : j = 1 := Fin.ext h; subst this; rfl
          · have : j = 2 := Fin.ext h; subst this; rfl
          · have : j = 3 := Fin.ext h; subst this; rfl
        rw [opsN_swap, hvd] at hz2
        exact step2_kill_k5 ht d i (by intro h; dsimp only [d] at h; exact hij (Fin.ext (by omega))) hz2 hrest2_sub tail2
      · by_cases hi4 : i.val = 4
        · have hv3 : s1v i = v6 3 := by have : i = 4 := Fin.ext hi4; subst this; rfl
          rw [hv3] at hz2
          exact step2_kill_m5 ht j (by intro h; exact hij (Fin.ext (by omega))) hz2 hrest2_sub tail2
        · by_cases hj4 : j.val = 4
          · have hv3 : s1v j = v6 3 := by have : j = 4 := Fin.ext hj4; subst this; rfl
            rw [opsN_swap, hv3] at hz2
            exact step2_kill_m5 ht i (by intro h; exact hij (Fin.ext (by omega))) hz2 hrest2_sub tail2
          · have hi056 : i.val = 0 ∨ i.val = 5 ∨ i.val = 6 := by omega
            have hj056 : j.val = 0 ∨ j.val = 5 ∨ j.val = 6 := by omega
            obtain ⟨o, ho⟩ := index_of_opN _ _ _ hz2
            have hchk := f6_step2_45_check i j hi056 hj056 hij o
            rw [ho] at hchk
            have kill_e (e : Fin 2) (hce : projConstB (srcToF41 e) z2 = true) : False := by
              let src := srcToF41 e
              have hcz : isConstB (proj src z2) = true := isConstB_proj_of_projConstB src z2 hce
              have hcnt : 1 ≤ constCount src (insert z2 rest2) :=
                constCount_ge_one src (Finset.mem_insert_self _ _) hcz
              have hcov : ∀ w ∈ insert z2 rest2, holdsN in32.toFinset (proj src w) := by
                intro w hw
                rcases Finset.mem_insert.mp hw with rfl | hwr
                · exact ((isConstB_iff _).mp hcz).imp_right Or.inl
                · obtain ⟨idx, rfl⟩ := s1_index _ (List.mem_toFinset.mp (hrest2_sub hwr))
                  exact holdsN_proj_of_projHoldsB src in32 (s1v idx) (f6_proj_f41_s1 e idx)
              have hpg : proj src t = goal41 ∨ proj src t = ~~~goal41 := by
                have h' := proj_eq_of_projEqB src goal6 goal41 (f6_proj_f41_goal e)
                rcases ht with rfl | rfl
                · exact .inl h'
                · exact .inr (by rw [proj_not, h'])
              have hnc : isConstB (proj src t) = false := by
                rcases hpg with h | h <;> rw [h]
                · exact goal41_nc.1
                · exact goal41_nc.2
              obtain ⟨k', hle, hsb⟩ := live_transport_const_save src hnc tail2 hcov
              exact sbN_f41_false (by omega) hpg hsb
            rcases hchk with hmem | h0 | h1
            · exact hz2out (List.mem_toFinset.mpr (List.elem_iff.mp hmem))
            · exact kill_e 0 h0
            · exact kill_e 1 h1

theorem no_eleven_f {t : BitVec 64} (ht : t = goal6 ∨ t = ~~~goal6)
    (run : build basicOpsN t 11 in6.toFinset) : False := by
  obtain ⟨s, hs, hl⟩ := compress run
  rcases first_live (k := 10) hl with endcase | ⟨a, ha, b, hb, hab, z1, hz1, hz1out, rest1, he1, tail1⟩
  · have htin : t ∈ s := by simp [endcase]
    obtain ⟨i, hi⟩ := in6_index _ (List.mem_toFinset.mp (hs htin))
    rcases ht with rfl | rfl
    · exact (f6_in_not_goal i).1 hi
    · exact (f6_in_not_goal i).2 hi
  · obtain ⟨i, rfl⟩ := in6_index _ (List.mem_toFinset.mp (hs ha))
    obtain ⟨j, rfl⟩ := in6_index _ (List.mem_toFinset.mp (hs hb))
    have hij : i ≠ j := fun eq => hab (congrArg v6 eq)
    obtain ⟨o, ho⟩ := index_of_opN _ _ _ hz1
    have hrest1_sub : rest1 ⊆ in6.toFinset :=
      fun w hw => hs (he1 ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw))
    have hkeep (d : Fin 6) (hd : d = i ∨ d = j) : v6 d ∈ rest1 := by
      obtain ⟨r0, r1, hdg, hdz, hdq⟩ := f6_sep1 i j hij o d hd
      rw [ho] at hdz
      obtain ⟨w, hw, hdw⟩ := live_separates (differsBit r0 r1) (goal_differsBit ht hdg) (opsN_differsBit r0 r1) tail1
      rcases Finset.mem_insert.mp hw with rfl | hwr
      · exact False.elim (hdw hdz)
      · obtain ⟨q, rfl⟩ := in6_index _ (List.mem_toFinset.mp (hrest1_sub hwr))
        by_cases hqd : q = d
        · subst hqd; exact hwr
        · exact False.elim (hdw (hdq q hqd))
    have kill_k5 (d : Fin 3) (hd : (⟨d.val, by omega⟩ : Fin 6) = i ∨ (⟨d.val, by omega⟩ : Fin 6) = j) : False := by
      let src := srcToK5 d
      let vd := v6 ⟨d.val, by omega⟩
      have hvd_mem : vd ∈ rest1 := hkeep ⟨d.val, by omega⟩ hd
      have hcd : isConstB (proj src vd) = true := isConstB_proj_of_projConstB src vd (f6_proj_k5_const d)
      have hcnt : 1 ≤ constCount src (insert z1 rest1) :=
        constCount_ge_one src (Finset.mem_insert_of_mem hvd_mem) hcd
      have hcov : ∀ w ∈ insert z1 rest1, holdsN in5.toFinset (proj src w) := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hwr
        · have hci : (proj src (v6 i) = 0 ∨ proj src (v6 i) = ~~~0) ∨ (proj src (v6 j) = 0 ∨ proj src (v6 j) = ~~~0) := by
            rcases hd with h | h
            · exact .inl (h ▸ (isConstB_iff _).mp hcd)
            · exact .inr (h ▸ (isConstB_iff _).mp hcd)
          exact mem_ops_constN
            (holdsN_proj_of_projHoldsB src in5 (v6 i) (f6_proj_k5_in d i))
            (holdsN_proj_of_projHoldsB src in5 (v6 j) (f6_proj_k5_in d j))
            hci (proj_ops src _ _ _ hz1)
        · obtain ⟨q, rfl⟩ := in6_index _ (List.mem_toFinset.mp (hrest1_sub hwr))
          exact holdsN_proj_of_projHoldsB src in5 (v6 q) (f6_proj_k5_in d q)
      have hpg : proj src t = goal5 ∨ proj src t = ~~~goal5 := by
        have h' := proj_eq_of_projEqB src goal6 (~~~goal5) (f6_proj_k5_goal d)
        rcases ht with rfl | rfl
        · exact .inr h'
        · exact .inl (by rw [proj_not, h', BitVec.not_not])
      have hnc : isConstB (proj src t) = false := by
        rcases hpg with h | h <;> rw [h]
        · exact goal5_nc.1
        · exact goal5_nc.2
      obtain ⟨k', hle, hsb⟩ := live_transport_const_save src hnc tail1 hcov
      exact sbN_k5_false (by omega) hpg hsb
    have kill_m5 (hd : (3 : Fin 6) = i ∨ (3 : Fin 6) = j) : False := by
      let src := srcToM5
      have hv3_mem : v6 3 ∈ rest1 := hkeep 3 hd
      have hc3 : isConstB (proj src (v6 3)) = true := isConstB_proj_of_projConstB src (v6 3) f6_proj_m5_const
      have hcnt : 1 ≤ constCount src (insert z1 rest1) :=
        constCount_ge_one src (Finset.mem_insert_of_mem hv3_mem) hc3
      have hcov : ∀ w ∈ insert z1 rest1, holdsN in32.toFinset (proj src w) := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hwr
        · have hci : (proj src (v6 i) = 0 ∨ proj src (v6 i) = ~~~0) ∨ (proj src (v6 j) = 0 ∨ proj src (v6 j) = ~~~0) := by
            rcases hd with h | h
            · exact .inl (h ▸ (isConstB_iff _).mp hc3)
            · exact .inr (h ▸ (isConstB_iff _).mp hc3)
          exact mem_ops_constN
            (holdsN_proj_of_projHoldsB src in32 (v6 i) (f6_proj_m5_in i))
            (holdsN_proj_of_projHoldsB src in32 (v6 j) (f6_proj_m5_in j))
            hci (proj_ops src _ _ _ hz1)
        · obtain ⟨q, rfl⟩ := in6_index _ (List.mem_toFinset.mp (hrest1_sub hwr))
          exact holdsN_proj_of_projHoldsB src in32 (v6 q) (f6_proj_m5_in q)
      have hpg : proj src t = goalM5 ∨ proj src t = ~~~goalM5 := by
        have h' := proj_eq_of_projEqB src goal6 goalM5 f6_proj_m5_goal
        rcases ht with rfl | rfl
        · exact .inl h'
        · exact .inr (by rw [proj_not, h'])
      have hnc : isConstB (proj src t) = false := by
        rcases hpg with h | h <;> rw [h]
        · exact goalM5_nc.1
        · exact goalM5_nc.2
      obtain ⟨k', hle, hsb⟩ := live_transport_const_save src hnc tail1 hcov
      exact sbN_maj5_false (by omega) hpg hsb
    by_cases hi3 : i.val < 3
    · exact kill_k5 ⟨i.val, hi3⟩ (.inl (Fin.ext rfl))
    · by_cases hj3 : j.val < 3
      · exact kill_k5 ⟨j.val, hj3⟩ (.inr (Fin.ext rfl))
      · by_cases hi3eq : i.val = 3
        · exact kill_m5 (.inl (Fin.ext hi3eq.symm))
        · by_cases hj3eq : j.val = 3
          · exact kill_m5 (.inr (Fin.ext hj3eq.symm))
          · have h45 : (i = 4 ∧ j = 5) ∨ (i = 5 ∧ j = 4) := by
              have hi' : i.val = 4 ∨ i.val = 5 := by omega
              have hj' : j.val = 4 ∨ j.val = 5 := by omega
              rcases hi' with h1 | h1 <;> rcases hj' with h2 | h2
              · exact False.elim (hij (Fin.ext (by omega)))
              · exact .inl ⟨Fin.ext h1, Fin.ext h2⟩
              · exact .inr ⟨Fin.ext h1, Fin.ext h2⟩
              · exact False.elim (hij (Fin.ext (by omega)))
            have hz45 : z1 ∈ basicOpsN (v6 4) (v6 5) := by
              rcases h45 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact hz1
              · rw [opsN_swap]; exact hz1
            have h4_mem : v6 4 ∈ rest1 := by
              rcases h45 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact hkeep 4 (.inl rfl)
              · exact hkeep 4 (.inr rfl)
            have h5_mem : v6 5 ∈ rest1 := by
              rcases h45 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact hkeep 5 (.inr rfl)
              · exact hkeep 5 (.inl rfl)
            have kill_45 (e : Fin 2) (hczB : projConstB (srcToF41 e) z1 = true) : False := by
              let src := srcToF41 e
              let ve := v6 ⟨4 + e.val, by omega⟩
              have hve_mem : ve ∈ rest1 := by
                fin_cases e
                · simpa [ve] using h4_mem
                · simpa [ve] using h5_mem
              have hce : isConstB (proj src ve) = true := isConstB_proj_of_projConstB src ve (f6_proj_f41_const e)
              have hcz : isConstB (proj src z1) = true := isConstB_proj_of_projConstB src z1 hczB
              have hne : z1 ≠ ve := fun eq => hz1out (eq ▸ (he1 ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hve_mem)))
              have hcnt : 2 ≤ constCount src (insert z1 rest1) :=
                constCount_ge_two src (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hve_mem) hne hcz hce
              have hcov : ∀ w ∈ insert z1 rest1, holdsN in32.toFinset (proj src w) := by
                intro w hw
                rcases Finset.mem_insert.mp hw with rfl | hwr
                · exact ((isConstB_iff _).mp hcz).imp_right Or.inl
                · obtain ⟨q, rfl⟩ := in6_index _ (List.mem_toFinset.mp (hrest1_sub hwr))
                  exact holdsN_proj_of_projHoldsB src in32 (v6 q) (f6_proj_f41_in e q)
              have hpg : proj src t = goal41 ∨ proj src t = ~~~goal41 := by
                have h' := proj_eq_of_projEqB src goal6 goal41 (f6_proj_f41_goal e)
                rcases ht with rfl | rfl
                · exact .inl h'
                · exact .inr (by rw [proj_not, h'])
              have hnc : isConstB (proj src t) = false := by
                rcases hpg with h | h <;> rw [h]
                · exact goal41_nc.1
                · exact goal41_nc.2
              obtain ⟨k', hle, hsb⟩ := live_transport_const_save src hnc tail1 hcov
              exact sbN_f41_false (by omega) hpg hsb
            simp only [basicOpsN, opsN, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz45
            rcases hz45 with rfl | rfl | rfl | rfl
            · have hall6 : ∀ q : Fin 6, v6 q ∈ rest1 := by
                intro q
                obtain ⟨r0, r1, hdg, hdz1, hdq⟩ := f6_sep_z1 q
                obtain ⟨w, hw, hdw⟩ := live_separates (differsBit r0 r1) (goal_differsBit ht hdg) (opsN_differsBit r0 r1) tail1
                rcases Finset.mem_insert.mp hw with rfl | hwr
                · exact False.elim (hdw hdz1)
                · obtain ⟨q', rfl⟩ := in6_index _ (List.mem_toFinset.mp (hrest1_sub hwr))
                  by_cases hqq : q' = q
                  · subst hqq; exact hwr
                  · exact False.elim (hdw (hdq q' hqq))
              have hrest_eq : insert (v6 4 &&& v6 5) rest1 = s1List.toFinset := by
                apply Finset.Subset.antisymm
                · intro w hw
                  rcases Finset.mem_insert.mp hw with rfl | hwr
                  · exact List.mem_toFinset.mpr (by simp [s1List, z1_6])
                  · obtain ⟨q, rfl⟩ := in6_index _ (List.mem_toFinset.mp (hrest1_sub hwr))
                    fin_cases q <;> exact List.mem_toFinset.mpr (by simp [s1List])
                · intro w hw
                  obtain ⟨idx, rfl⟩ := s1_index _ (List.mem_toFinset.mp hw)
                  fin_cases idx
                  · exact Finset.mem_insert_self _ _
                  · exact Finset.mem_insert_of_mem (hall6 0)
                  · exact Finset.mem_insert_of_mem (hall6 1)
                  · exact Finset.mem_insert_of_mem (hall6 2)
                  · exact Finset.mem_insert_of_mem (hall6 3)
                  · exact Finset.mem_insert_of_mem (hall6 4)
                  · exact Finset.mem_insert_of_mem (hall6 5)
              rw [hrest_eq] at tail1
              exact no_ten_after_z1 ht tail1
            · exact kill_45 0 f6_step1_45_const.1
            · exact kill_45 1 f6_step1_45_const.2.1
            · exact kill_45 0 f6_step1_45_const.2.2

def step6 (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def bit6 (k : Fin 64) (w : BitVec 64) : Bool := w[k.val]

lemma read_bit6 (w : List (BitVec 64)) (i : ℕ) (k : Fin 64) :
    (w.map (bit6 k)).getD i false = bit6 k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit6]

def action6 (w : List (BitVec 64)) (g : Gate) : BitVec 64 := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
lemma action6_spec (w : List (BitVec 64)) (g : Gate) (hg : legal g) (k : Fin 64) :
    step6 (w.map (bit6 k)) g = (w ++ [action6 w g]).map (bit6 k) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : BitVec 64)[k.val] = false := by change (BitVec.ofNat 64 0)[k.val] = false; simp
  all_goals rcases hop with rfl | rfl | rfl <;>
    simp only [step6, List.map_cons, List.map_nil, read_bit6, List.map_append] <;>
    simp only [action6, GateOp.eval, List.foldr_cons, List.foldr_nil, List.head?_cons, List.head?_nil,
      List.headD_cons, List.headD_nil, Option.map_some, Option.map_none, Option.getD_some, Option.getD_none,
      List.all_cons, List.all_nil, List.any_cons, List.any_nil, List.map_cons, List.map_nil, id_eq,
      Bool.and_true, Bool.or_false, bit6, BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not,
      bit0, Bool.not_false]

lemma available_read6 {av : Finset (BitVec 64)} {w : List (BitVec 64)}
    (hw : ∀ u ∈ w, holdsN av u) (i : ℕ) : holdsN av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
lemma gate_reach6 (w : List (BitVec 64)) (av : Finset (BitVec 64)) (hw : ∀ u ∈ w, holdsN av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachableN av (action6 w g) else holdsN av (action6 w g) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl | rfl | rfl <;> simp only [isBinary, Bool.false_eq_true, ite_false, ite_true,
    action6, List.head?_nil, List.head?_cons, List.map_nil, List.map_cons, List.foldr_nil, List.foldr_cons,
    Option.map_none, Option.map_some, Option.getD_none, Option.getD_some,
    show ∀ x : BitVec 64, x ||| (0 : BitVec 64) = x from fun x => BitVec.or_zero,
    show ∀ x : BitVec 64, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read6 hw _)
    | exact holdsN_not (available_read6 hw _)
    | exact and_reachN (available_read6 hw _) (available_read6 hw _)
    | exact or_reachN (available_read6 hw _) (available_read6 hw _)

set_option maxRecDepth 4000 in
theorem compile6 (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List (BitVec 64)) (av : Finset (BitVec 64)) (hw : ∀ u ∈ w, holdsN av u)
    (he : ∀ k, (gs.foldl step6 (w.map (bit6 k))).getD out false = bit6 k goal6) :
    ∃ t, (t = goal6 ∨ t = ~~~goal6) ∧ build basicOpsN t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = goal6 := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit6, bit6] using he ⟨i, hi⟩
    have h := hv ▸ available_read6 hw out
    rcases h with zero | ones | ⟨t, ht, eq | eq⟩
    · exact False.elim ((by decide : goal6 ≠ 0) zero)
    · exact False.elim ((by decide : goal6 ≠ ~~~0) ones)
    · exact ⟨t, .inl eq.symm, ht⟩
    · exact ⟨t, .inr (by rw [eq, BitVec.not_not]), ht⟩
  | cons g gs ih =>
    let z := action6 w g
    have stepOK := action6_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step6 ((w ++ [z]).map (bit6 k))).getD out false = bit6 k goal6 := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset (BitVec 64)) (hold : ∀ u ∈ w, holdsN A u) (new : holdsN A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu | hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach6 w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg, Bool.false_eq_true, ite_false] at stepClass
      simpa [binaryCost, neg] using cont av hw stepClass
    · simp only [neg, ite_true] at stepClass
      have len : binaryCost (g :: gs) = binaryCost gs + 1 := by simp [binaryCost, neg]
      rw [len]
      rcases stepClass with existing | ⟨a, ha, b, hb, ne, new, op, rep⟩
      · obtain ⟨t, ht, run⟩ := cont av hw existing
        exact ⟨t, ht, Or.inl run⟩
      · obtain ⟨t, ht, run⟩ := cont (insert new av) (fun u hu => holdsN_mono (Finset.subset_insert _ _) (hw u hu)) rep
        exact ⟨t, ht, Or.inr ⟨a, ha, b, hb, ne, new, op, run⟩⟩

def targetF (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4276676608 * 2 ^ 32 + 3892346880) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

lemma spec_f6 : ∀ k : Fin 64, targetF (fun i => bit6 k (v6 i)) = bit6 k goal6 := by decide +kernel

theorem twelve_binary (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = targetF x) :
    11 < binaryCost gs := by
  by_contra hlow
  have low : binaryCost gs ≤ 11 := by omega
  have init : ∀ u ∈ in6, holdsN in6.toFinset u := fun u hu =>
    .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 64) :
      (gs.foldl step6 (in6.map (bit6 k))).getD o false = bit6 k goal6 := by
    let x (i : Fin 6) : Bool := bit6 k (v6 i)
    have same : List.ofFn x = in6.map (bit6 k) := by
      apply List.ext_getElem
      · simp [in6]
      · intro i hi hj
        have hlt : i < in6.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, v6, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs, o⟩ (in6.map (bit6 k)) = bit6 k goal6
    rw [← same, he]
    exact spec_f6 k
  obtain ⟨t, ht, run⟩ := compile6 gs o hg in6 in6.toFinset init evaluate
  have lift {a c : ℕ} (h : a ≤ c) (hr : build basicOpsN t a in6.toFinset) :
      build basicOpsN t c in6.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact no_eleven_f ht (lift low run)

def witGates : List Gate :=
  [ { op := GateOp.or,  inputs := [0, 2] }
  , { op := GateOp.or,  inputs := [4, 5] }
  , { op := GateOp.and, inputs := [7, 6] }
  , { op := GateOp.or,  inputs := [8, 1] }
  , { op := GateOp.and, inputs := [0, 2] }
  , { op := GateOp.and, inputs := [5, 4] }
  , { op := GateOp.and, inputs := [1, 8] }
  , { op := GateOp.and, inputs := [11, 3] }
  , { op := GateOp.or,  inputs := [13, 10] }
  , { op := GateOp.or,  inputs := [14, 12] }
  , { op := GateOp.and, inputs := [9, 15] }
  , { op := GateOp.or,  inputs := [3, 11] }
  , { op := GateOp.and, inputs := [16, 17] } ]

def witCirc : Circuit := ⟨witGates, 18⟩

lemma witCirc_mono : Monotone2 witCirc := by
  intro g hg
  simp only [witCirc, witGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by simp, by decide⟩

lemma witCirc_eval : ∀ x : Fin 6 → Bool, witCirc.eval (List.ofFn x) = targetF x := by decide +kernel

lemma main_proof (s : ℕ) (h : HasCircuitSize 6 targetF s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = targetF x := by
  obtain ⟨C, hFan, hSize, hEval⟩ := h
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨gNot, hgNot, hopNot⟩ := hasNot
    have hbc_lt : binaryCost C.gates < C.gates.length :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨gNot, hgNot, by simp [isBinary, hopNot]⟩
    have hleg : ∀ g ∈ C.gates, legal g := fun g hg => by
      obtain ⟨hop, hlen⟩ := hFan g hg
      exact ⟨by simpa using hop, hlen⟩
    have h12 : 11 < binaryCost C.gates := twelve_binary C.gates C.output hleg (fun x => by
      simpa [Circuit.eval] using hEval x)
    have hwit_le : witCirc.size ≤ s := by
      have hcs : C.gates.length ≤ s := hSize
      have hwl : witCirc.size = 13 := rfl
      omega
    exact ⟨witCirc, witCirc_mono, hwit_le, witCirc_eval⟩
  · refine ⟨C, ?_, hSize, hEval⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := hFan g hg
    refine ⟨?_, hlen⟩
    have hop' : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by simpa using hop
    rcases hop' with h1 | h2 | h3
    · simp [h1]
    · simp [h2]
    · exact False.elim (hasNot ⟨g, hg, h3⟩)

end PEqualNP.Outside.L_meta_12102

theorem PEqualNP.Outside.L_meta_12102 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676608 * 2 ^ 32 + 3892346880) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676608 * 2 ^ 32 + 3892346880) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  exact PEqualNP.Outside.L_meta_12102.main_proof
