import Mathlib
import PEqualNP.Defs

-- Signed compiler and bounds adapted from sirusdv, PR 7201, under Apache-2.0.
-- Uses the induced-graph bounds of L-meta-1667 and the finite circuit search of L-meta-515.
namespace PEqualNP.Outside.L_meta_3612_aux

namespace ThetaSigned
abbrev Wire (X : Type) := X → Bool
def inv {X : Type} (f : Wire X) : Wire X := fun x => !(f x)
def bit {X : Type} (b : Bool) : Wire X := fun _ => b
def bin {X : Type} (isOr : Bool) (a b : Wire X) : Wire X :=
  fun x => if isOr then a x || b x else a x && b x
def plus {X : Type} (P : Set (Wire X)) (f : Wire X) : Set (Wire X) :=
  {g | g ∈ P ∨ g = f ∨ g = inv f}
def Closed {X : Type} (P : Set (Wire X)) : Prop :=
  (∀ b, bit b ∈ P) ∧ ∀ f ∈ P, inv f ∈ P
theorem inv_inv {X : Type} (f : Wire X) : inv (inv f) = f := by funext x; simp [inv]
theorem plus_closed {X : Type} {P : Set (Wire X)} (hP : Closed P) (f : Wire X) : Closed (plus P f) := by
  refine ⟨fun b => Or.inl (hP.1 b),?_⟩
  intro g hg
  rcases hg with hg|rfl|rfl
  · exact Or.inl (hP.2 _ hg)
  · exact Or.inr (Or.inr rfl)
  · exact Or.inr (Or.inl (inv_inv _))
inductive Run {X : Type} : Set (Wire X) → ℕ → Wire X → Prop
  | done {P k f} : f ∈ P → Run P k f
  | gate {P k f a b} (isOr : Bool) : a ∈ P → b ∈ P →
      Run (plus P (bin isOr a b)) k f → Run P (k+1) f
end ThetaSigned

namespace P2828
open ThetaSigned
abbrev Y := Fin 9 → Bool
def small : Set (Wire Y) := {f | (∃ c, f=bit c) ∨ ∃ i : Fin 9, f=(fun x => x i) ∨ f=inv (fun x => x i)}
theorem small_closed : Closed small := by
  constructor
  · exact fun b => Or.inl ⟨b,rfl⟩
  · intro f hf
    rcases hf with ⟨b,rfl⟩|⟨i,rfl|rfl⟩
    · exact Or.inl ⟨!b,rfl⟩
    · exact Or.inr ⟨i,Or.inr rfl⟩
    · exact Or.inr ⟨i,Or.inl (inv_inv _)⟩
def nine (y : Y) : Bool := (y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 4) || (y 4 && y 0) || (y 0 && y 5) || (y 1 && y 6) || (y 2 && y 7) || (y 3 && y 8) || (y 5 && y 7) || (y 6 && y 8) || (y 8 && y 5)
end P2828

namespace P2828Live
variable {α : Type} [DecidableEq α]
def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k+1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)
def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k+1, s => live ops goal k s ∨
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
    (h : live ops goal k s) : s.card ≤ k+1 := by
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
end P2828Live
namespace P2828Live
variable {α : Type} [DecidableEq α] {ops : α → α → Finset α} {goal : α}
theorem first_live {k : ℕ} {s : Finset α} (h : live ops goal (k+1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a,ha,b,hb,hab,z,hz,hn,r,hs,tail⟩
      · exact .inl done
      · exact .inr ⟨a,ha,b,hb,hab,z,hz,hn,r,hs,Or.inl tail⟩
    · exact .inr step
end P2828Live
namespace P2828Check
abbrev W := BitVec 1378
def neg (x : W) : W := ~~~x
def both (x y : W) : W := x &&& y
def canon (x : W) : W := if x.getLsbD 0 then neg x else x
def ops (x y : W) : List W :=
  [canon (both x y), canon (both x (neg y)), canon (both (neg x) y), canon (both (neg x) (neg y))]
def sep (x : W) := (x ^^^ (x >>> 689)).setWidth 689
def cuts (ws : List W) : BitVec 689 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := canon (((-1 : BitVec 689) ++ (0 : BitVec 689)))
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a,rest) :: (singles rest).map (fun (b,bs) => (b,a :: bs))
def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b,bs) => (a,b,bs)) ++
      (pairs rest).map (fun (b,c,bs) => (b,c,a :: bs))
def rawInputs : List W := [0x2aaaaaaaaaabaab555d556bebaab6adb557aad55ebb7daab6ab5575557add7edefb75fef8000000000000000007fffff8000000007ffa900a801202004212000849425ffaab16212008042142480955602a1bfffffffe14015555544d5502048aa4b58100469aaad540804cae850155aaaa02012aae0855a827795115115115115115115115115115115115114805400901002109000424a12ffd558b1090040210a12404aab0150d00000000,
0x333333333332cf399966672b3ccdb36d99acfe66b2fafccdb3de7bf99acee6f6f7dfeb778000000000000007ff8000000000007fffff8200014a000521444ffd11014800100a1444401114c148373ffffffff5560149608188808899228cccb311948060d9860412233359351020c884114ccd6551033a857588208e08e08e08e08e08e08e08e08e08e08e08c10000a5000290a227fe8880a40008050a2220088a60a41b900000000aab00a4b,
0x3c3c3c3c3c3cf3de1e787bcfdf0e3c71e1cf37873cdcef0e3ce79dfe1cf77bf8bae5f3fb0000000000007ff8000000000007fffff800004a321079784e098000260000920020409816e67fffffffee0128cec2012a121e1e021e0206016303042c220f870638f0e598c0864a678702714e33020a84bc457288758c50c50c50c50c50c50c50c50c50c50c50c5002519083cbc2704c000130000490010204c0b733000000007009467610095090,
0x3fc03fc03fc0fc1fe07f83f3eff03f81fe0fc7f83f1f7ff03f07e19fe0f87cbf3cf9fdbd0000000007ff8000000000007fffff8000003390c06382018000049000187120ddcf9fffffffe01871d9c06443010004406041601de015607e00203bc049f07819c00b02633c198098781d82b0ccf0743a439a0c768a01a41a41a41a41a41a41a41a41a41a41a41a59c86031c100c0000248000c38906ee7c0000000000c38ece0322180800220302,
0x3fffc0003fff001fff8003fc0fffc001fff007ffc01f8fffc007fe1fff007f3fc0fe7e3e0000000000000000000007fffff800000000406303804c4e098e092638218007fffff8e0fb3b98a1802208818c0a1bb98f839e9fe0000a9b000fdf8001b40787e000545000c3e0050787e00145030f80051c602109002a4aa4aa4aa4aa4aa4aa4aa4aa4aa4aa4aa4a03181c0262704c704931c10c00000000c707d9dcc50c0110440c6050ddcc7c1c,
0x3fffffffc000001ffffffc000ffffffe000007ffffe00ffffff8001fffff803fff007fc07ff8007ff8000000007ff800000000000000007c03fc0f8ff00001c7fffffff8010c00001c3c0000013c0001f00c0001f3fc1e3e6aaa200000030337440007effb96000003f7fb3007afeaa4000fdfed401f7a803d80006c06c06c06c06c06c06c06c06c06c06c06c03e01fe07c7f80000e000000000008600000e1e0000009e0000f8060000f9fe0,
0x3fffffffffffffe0000000000ffffffffffff80000000fffffffffe00000003fffff80000007ff8000000007ff8000000000000000007c7ffc000ff001fffff8003e01c0e1f000009fc0003e01c000f9fff00021fc001f7e777f7766dd7000000000079f2679fbeddc00000007df377beeb00000001cc57a80000370370370370370370370370370370370373e3ffe0007f800000000001f00e070f800004fe0001f00e0007cfff80010fe000,
0x3ffffffffffffffffffffffff00000000000000000000fffffffffffffffffc0000000000000007ff8007ff8000000000000000000007f8000007ffffff00e07c03ffe04fe001f00e0001f3ffe0010fe00001c3e000001c19541ddf9fe9cfcc893ddf00000000000000000000050150ab1c020103b40000000003383383383383383383383383383383383383fc00000000000f80703e01fff027f000f8070000f9fff00087f00000e1f00000,
0x3ffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000007fffff8007ff8000000000000000000000007ffffffff00001fff007ffc0000700001fff00001fc000001f0000001fc00000008180008899008cdcc03bb60800000004100000044f60000000000000000000000000003c03c03c03c03c03c03c03c03c03c03c03c000000000380000fff803ffe0000380000fff80000fe000000f8000000fe000000]
def inputs := rawInputs.map canon
end P2828Check
namespace P2828Check
variable {α : Type}
theorem pick_one {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a,rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a,rest),hm,rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)
theorem pick_two {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a,b,rest) ∈ pairs ws ∨ (b,a,rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b,r),hm,rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r,.inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a,r),hm,rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_, (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a,b,r),hm,rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b,a,r),hm,rfl⟩))
end P2828Check
namespace P2828Check
abbrev basicOps (a b : W) := (ops a b).toFinset
def differs (i : Fin 689) (w : W) : Prop :=
  w.getLsbD i.val ≠ w.getLsbD (689+i.val)
theorem neg_differs (i : Fin 689) (w : W) : differs i (neg w) ↔ differs i w := by
  have lo : i.val < 1378 := by omega
  have hi : 689+i.val < 1378 := by omega
  simp [neg, differs, hi, lo]
theorem canon_differs (i : Fin 689) (w : W) : differs i (canon w) ↔ differs i w := by
  unfold canon
  split <;> simp [neg_differs]
theorem ops_differs (i : Fin 689) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  by_contra! h
  have e₁ : a.getLsbD i.val = a.getLsbD (689+i.val) := by simpa [differs] using h.1
  have e₂ : b.getLsbD i.val = b.getLsbD (689+i.val) := by simpa [differs] using h.2
  have lo : i.val < 1378 := by omega
  have hi : 689+i.val < 1378 := by omega
  simp [basicOps, ops] at hz
  rcases hz with rfl|rfl|rfl|rfl <;>
    rw [canon_differs] at hd <;>
    simp only [both, neg, differs, BitVec.getLsbD_and, BitVec.getLsbD_not, hi, lo, e₁, e₂] at hd <;> simp_all
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem goal_differs (i : Fin 689) : differs i goal := by
  rw [goal, canon_differs]
  unfold differs
  rw [BitVec.getLsbD_append, BitVec.getLsbD_append]
  simp [i.isLt, show ¬689 + i.val < 689 by omega]
  exact BitVec.getElem_allOnes _ _
theorem cuts_spec (ws : List W) (i : Fin 689) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    simp [sep, i.isLt, differs]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem cuts_full {k : ℕ} {ws : List W} (h : P2828Live.live basicOps goal k ws.toFinset) :
    cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := P2828Live.live_separates (differs ⟨j,hj⟩) (goal_differs ⟨j,hj⟩) (ops_differs ⟨j,hj⟩) h
  have hbit := (cuts_spec ws ⟨j,hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 689)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit
theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp [basicOps, ops, both, BitVec.and_comm]
  grind [BitVec.and_comm]
end P2828Check
namespace P2828Check
def keepChoices (a b : W) (r : List W) := [r, a::r, b::r, a::b::r]
theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simpa [hp.mem_iff] using (hp.mem_iff (a := v))
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a::b::r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a::r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b::r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind
theorem singleton_list {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc
end P2828Check
namespace P2828Check
private def possible (w : List W) (z : W) : Bool :=
  z == 0 || z == (-1) || w.any (fun u => z == u || z == ~~~u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))
private def bit (k : Fin 1378) (z : W) := z[k.val]
theorem canon_neg (x : W) : canon (~~~x) = canon x := by
  unfold canon neg
  simp only [BitVec.getLsbD_not, BitVec.not_not]
  cases h : x.getLsbD 0 <;> simp [h]
theorem sign (x : W) : x = canon x ∨ x = neg (canon x) := by
  unfold canon neg
  split <;> simp
theorem signed_both {x y a b : W} (hx : x = a ∨ x = neg a) (hy : y = b ∨ y = neg b) :
    canon (x &&& y) ∈ basicOps a b := by
  rcases hx with rfl|rfl <;> rcases hy with rfl|rfl <;> simp [basicOps, ops, both]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem same_both {x y : W} (eq : canon x = canon y) :
    canon (x &&& y) = canon x ∨ canon (x &&& y) = 0 := by
  have signs : x = y ∨ x = ~~~y := by
    rcases sign x with h|h <;> rcases sign y with j|j <;> rw [eq] at h
    · exact .inl (h.trans j.symm)
    · exact .inr (h.trans (by simpa only [neg, BitVec.not_not] using congrArg (fun v : W => ~~~v) j.symm))
    · exact .inr (h.trans (congrArg neg j.symm))
    · exact .inl (h.trans j.symm)
  rcases signs with rfl|rfl
  · exact .inl (by rw [BitVec.and_self])
  · exact .inr (by rw [BitVec.not_and_self]; decide)
def represents (available : Finset W) (w : List W) :=
  ∀ u ∈ w, canon u = 0 ∨ canon u ∈ available
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem classify {available : Finset W} {ws : List W} (hw : represents available ws)
    {z : W} (hz : possible ws z) :
    canon z = 0 ∨ canon z ∈ available ∨
      ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ canon z ∈ basicOps a b := by
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hz
  rcases hz with ((h | h) | ⟨x,hx, (h | h) | ⟨y,hy, hh⟩⟩)
  · subst z; left; decide
  · subst z; left; decide
  · subst z; exact (hw _ hx).imp_right Or.inl
  · subst z; rw [canon_neg]; exact (hw _ hx).imp_right Or.inl
  · have andCase (u v : W) (hu : canon u = 0 ∨ canon u ∈ available)
        (hv : canon v = 0 ∨ canon v ∈ available) :
        canon (u &&& v) = 0 ∨ canon (u &&& v) ∈ available ∨
        ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ canon (u &&& v) ∈ basicOps a b := by
      have zeroOrFull (t : W) (h : canon t = 0) : t = 0 ∨ t = BitVec.allOnes 1378 := by
        rcases sign t with h'|h' <;> rw [h] at h'
        · exact .inl h'
        · exact .inr h'
      rcases hu with h | hu
      · rcases zeroOrFull _ h with rfl|rfl
        · left; exact (congrArg canon (BitVec.zero_and (x := v))).trans (by decide)
        · rw [BitVec.allOnes_and]; exact hv.imp_right Or.inl
      rcases hv with h | hv
      · rcases zeroOrFull _ h with rfl|rfl
        · left; exact (congrArg canon (BitVec.and_zero (x := u))).trans (by decide)
        · rw [BitVec.and_allOnes]; exact .inr (.inl hu)
      by_cases h : canon u = canon v
      · rcases same_both h with ht|ht
        · exact .inr (.inl (ht ▸ hu))
        · exact .inl ht
      · exact .inr (.inr ⟨_,hu,_,hv,h,signed_both (sign u) (sign v)⟩)
    rcases hh with rfl|rfl
    · exact andCase x y (hw _ hx) (hw _ hy)
    · rw [← canon_neg (x ||| y), BitVec.not_or]
      exact andCase _ _ (by simpa only [canon_neg] using hw _ hx) (by simpa only [canon_neg] using hw _ hy)
open ThetaSigned P2828
def assignment (k : Fin 1378) (i : Fin 9) := bit k (rawInputs.getD i.val 0)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem graph_rows : ∀ k : Fin 1378, nine (assignment k) =
    bit k ((-1 : BitVec 689) ++ (0 : BitVec 689)) := by
  let x := fun (i : Nat) => rawInputs.getD i 0
  let H := (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) ||| (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) ||| (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
  have h : H = ((-1 : BitVec 689) ++ (0 : BitVec 689)) := by decide +kernel
  intro k
  rw [← h]
  simp only [H,bit,BitVec.getElem_or,BitVec.getElem_and]
  have nine_eq : ∀ y : Y, nine y = ((y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 4) || (y 4 && y 0) || (y 0 && y 5) || (y 1 && y 6) || (y 2 && y 7) || (y 3 && y 8) || (y 5 && y 7) || (y 6 && y 8) || (y 8 && y 5)) := fun _ => rfl
  exact nine_eq (assignment k)
def rawOps (a b : W) := [both a b, both a (neg b), both (neg a) b, both (neg a) (neg b)]
theorem sep_canon (x : W) : sep (canon x) = sep x := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  have h (v : W) : (sep v)[i] = true ↔ differs ⟨i,hi⟩ v := by
    change (sep v).getLsbD i = true ↔ _
    simp [sep, hi, differs]
  have eq := (h (canon x)).trans ((canon_differs ⟨i,hi⟩ x).trans (h x).symm)
  exact Bool.eq_iff_iff.mpr eq
def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (rawOps a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (canon w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra-1) (canon w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra-1) (canon w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra-2) (canon w :: a :: b :: r))
def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => ws == [goal]
  | k+1, extra, ws => ws == [goal] ||
    (pairs ws).any (fun (a,b,r) => dispatch extra (optimized k) a b r)
theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z::kept) = -1) (ht : next (k-kept.length) (z::kept) = true) :
    dispatch extra next a b r = true := by
  have hmap : ops a b = (rawOps a b).map canon := rfl
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp (hmap ▸ List.mem_toFinset.mp hz)
  apply List.any_eq_true.mpr
  refine ⟨w,hw,?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl|rfl|rfl|rfl <;>
    simp only [cuts, List.foldr_cons, sep_canon] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2 <;> omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1 <;> ac_rfl, by convert ht using 2 <;> omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1 <;> ac_rfl, by convert ht using 2 <;> omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1 <;> ac_rfl⟩, by convert ht using 2 <;> omega⟩
end P2828Check
namespace P2828Check
theorem optimized_complete (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n+1) (h : P2828Live.live basicOps goal n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases P2828Live.first_live h with done | ⟨a,ha,b,hb,hab,z,hz,hout,needed,hs,tail⟩
    · simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a::b::r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept,hk,hnk,hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z::kept).Nodup := List.nodup_cons.mpr ⟨hznew,hnk⟩
        have hl : P2828Live.live basicOps goal k (z::kept).toFinset := by
          simpa [hfin] using tail
        have hc := P2828Live.live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a,b,r), direct, go hp hs hz⟩
      · exact ⟨(b,a,r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩
end P2828Check

namespace SignedCofactor
open ThetaSigned
def literals (n : Nat) : Set (Wire (Fin n → Bool)) :=
  {f | (∃ c, f=bit c) ∨ ∃ i : Fin n, f=(fun x => x i) ∨ f=inv (fun x => x i)}
theorem literals_closed (n : Nat) : Closed (literals n) := by
  constructor
  · exact fun b => Or.inl ⟨b,rfl⟩
  · intro f hf
    rcases hf with ⟨b,rfl⟩|⟨i,rfl|rfl⟩
    · exact Or.inl ⟨!b,rfl⟩
    · exact Or.inr ⟨i,Or.inr rfl⟩
    · exact Or.inr ⟨i,Or.inl (inv_inv _)⟩
end SignedCofactor

namespace P2828Generic
open P2828Check P2828Live ThetaSigned
def wordBit (r : Fin 1378) (w : W) := w[r.val]
def representsPool {T} (pick : Fin 1378 → T) (P : Set (Wire T)) (S : Finset W) :=
  ∀ f ∈ P, ∃ w, (canon w=0 ∨ canon w ∈ S) ∧ ∀ r, f (pick r)=wordBit r w
private def possibleIn (w : List W) (z : W) : Bool :=
  z == 0 || z == (-1) || w.any (fun u => z == u || z == ~~~u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))
private theorem singletonPossible {ws : List W} {x : W} (hx : x = 0 ∨ x ∈ ws) :
    possibleIn ws x ∧ possibleIn ws (~~~x) := by
  rcases hx with rfl | hx
  · simp [possibleIn]
  · simp only [possibleIn, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    grind
private theorem pairPossible {ws : List W} {x y : W} (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
    possibleIn ws (x &&& y) ∧ possibleIn ws (x ||| y) := by
  rcases hx with rfl | hx
  · simpa [possibleIn] using (show possibleIn ws 0 ∧ possibleIn ws y from ⟨by simp [possibleIn], (singletonPossible hy).1⟩)
  rcases hy with rfl | hy
  · simpa [possibleIn] using (show possibleIn ws 0 ∧ possibleIn ws x from ⟨by simp [possibleIn], (singletonPossible (.inr hx)).1⟩)
  · simp only [possibleIn, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    constructor
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inl rfl⟩⟩
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inr rfl⟩⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem anyBuild {T : Type} (pick : Fin 1378 → T) {target : Wire T}
    (agrees : ∀ r, target (pick r) = wordBit r goal) {P : Set (Wire T)} {k : Nat} (h : Run P k target) :
    ∀ av, representsPool pick P av → P2828Live.build basicOps goal k av := by
  generalize eqF : target = f at h
  induction h with
  | @done P k f hf =>
    subst f
    intro av rep
    obtain ⟨u,hu,huv⟩ := rep _ hf
    have eq : u = goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      exact ((huv ⟨i,hi⟩).symm.trans (agrees ⟨i,hi⟩))
    rw [eq,show canon goal=goal by decide +kernel] at hu
    have ing : goal ∈ av := hu.resolve_left (by decide)
    induction k with
    | zero => exact ing
    | succ k ih => exact Or.inl ih
  | @gate P k f a b op ha hb tail ih =>
    intro av rep
    obtain ⟨u,ru,eu⟩ := rep _ ha
    obtain ⟨v,rv,ev⟩ := rep _ hb
    let z := if op then u ||| v else u &&& v
    have hbits (r) : ThetaSigned.bin op a b (pick r) = wordBit r z := by
      cases op <;> simp [z,ThetaSigned.bin,eu,ev,wordBit]
    have add {av' : Finset W} (sub : av ⊆ av') (has : canon z=0 ∨ canon z ∈ av') :
        representsPool pick (plus P (ThetaSigned.bin op a b)) av' := by
      rintro g (old|rfl|rfl)
      · obtain ⟨w,hw,e⟩ := rep g old
        exact ⟨w,hw.imp_right (fun h => sub h),e⟩
      · exact ⟨_,has,hbits⟩
      · refine ⟨~~~z,by simpa only [canon_neg] using has,?_⟩
        intro r
        simp [ThetaSigned.inv,hbits,wordBit]
    have hws : represents av [u,v] := by
      intro t ht
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl|rfl <;> assumption
    have hz : possibleIn [u,v] z := by
      have hh := pairPossible (ws:=[u,v]) (Or.inr (List.mem_cons_self ..) : u=0 ∨ u∈[u,v])
        (Or.inr (by simp) : v=0 ∨ v∈[u,v])
      cases op <;> first | exact hh.1 | exact hh.2
    rcases classify hws hz with hz|hz|⟨a',ha',b',hb',ne,mem⟩
    · exact Or.inl (ih eqF av (add (fun _ h=>h) (Or.inl hz)))
    · exact Or.inl (ih eqF av (add (fun _ h=>h) (Or.inr hz)))
    · exact Or.inr ⟨a',ha',b',hb',ne,_,mem,ih eqF _ (add (Finset.subset_insert ..) (Or.inr (Finset.mem_insert_self ..)))⟩
def columnPick {n : Nat} (cols : List W) (r : Fin 1378) (i : Fin n) := wordBit r (cols.getD i.val 0)
def signals (cols : List W) := cols.map canon
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem columnGood {n} (cols : List W) (len : cols.length=n) :
    representsPool (columnPick (n:=n) cols) (SignedCofactor.literals n) (signals cols).toFinset := by
  have present (i : Fin n) : canon (cols.getD i.val 0) ∈ (signals cols).toFinset := by
    have h : i.val < cols.length := len ▸ i.isLt
    apply List.mem_toFinset.mpr
    exact List.mem_map.mpr ⟨_,by rw [List.getD_eq_getElem _ _ h];exact List.getElem_mem ..,rfl⟩
  rintro f (⟨b,rfl⟩|⟨i,rfl|rfl⟩)
  · cases b
    · exact ⟨0,Or.inl (by decide),by simp [ThetaSigned.bit,wordBit]⟩
    · exact ⟨-1,Or.inl (by decide),by intro r; exact (BitVec.getElem_allOnes r.val r.isLt).symm⟩
  · exact ⟨_,Or.inr (present i),fun r=>rfl⟩
  · refine ⟨~~~(cols.getD i.val 0),Or.inr ?_,?_⟩
    · rw [canon_neg];exact present i
    · intro r;simp [inv,columnPick,wordBit]
def critical (ws : List W) (sites : List (Fin 689)) : Bool :=
  ws.all fun a => sites.any fun i => ws.all fun b => (b.getLsbD i.val == b.getLsbD (689+i.val)) || b == a
theorem all_required {ws : List W} {sites} {k s} (crit : critical ws sites=true)
    (hs : s⊆ws.toFinset) (hr : live basicOps goal k s) : s=ws.toFinset := by
  apply Finset.Subset.antisymm hs
  intro a ha
  obtain ⟨i,_,all⟩ := List.any_eq_true.mp (List.all_eq_true.mp crit a (List.mem_toFinset.mp ha))
  obtain ⟨b,hb,hd⟩ := live_separates (differs i) (goal_differs i) (ops_differs i) hr
  have eq := List.all_eq_true.mp all _ (List.mem_toFinset.mp (hs hb))
  simp only [Bool.or_eq_true,beq_iff_eq] at eq
  exact eq.resolve_left hd ▸ hb
end P2828Generic
namespace P2828Check
open ThetaSigned P2828 P2828Generic P2828Live
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem inputLive {k} (h : Run small k nine) : live basicOps goal k inputs.toFinset := by
  have b := anyBuild (columnPick (n:=9) rawInputs) (target:=nine) graph_rows h _ (columnGood rawInputs rfl)
  obtain ⟨s,hs,hl⟩ := compress b
  exact all_required (ws:=inputs) (sites:=[0,32,64,96,128,150,182,204,226]) (by decide +kernel) hs hl ▸ hl
end P2828Check

namespace P2828Live
variable {α β : Type} [DecidableEq α] [DecidableEq β]
def kept (p : α → Option β) (s : Finset α) : Finset β := s.biUnion (fun a => (p a).toFinset)
def zeros (p : α → Option β) (s : Finset α) : ℕ :=
  (s.filter (fun a => p a = none)).card
theorem kept_insert (p : α → Option β) (a : α) (s : Finset α) :
    kept p (insert a s) = (p a).toFinset ∪ kept p s := by
  simp [kept]
theorem zeros_some {p : α → Option β} {a : α} {v : β} (h : p a = some v) (s : Finset α) :
    zeros p (insert a s) = zeros p s := by simp [zeros, Finset.filter_insert, h]
theorem zeros_none {p : α → Option β} {a : α} (h : p a = none) {s : Finset α} (ha : a ∉ s) :
    zeros p (insert a s) = zeros p s + 1 := by simp [zeros, Finset.filter_insert, h, ha]
theorem zeros_le (p : α → Option β) (a : α) (s : Finset α) :
    zeros p (insert a s) ≤ zeros p s + 1 := by
  cases h : p a with
  | some v => rw [zeros_some h]; omega
  | none =>
    by_cases hm : a ∈ s
    · rw [Finset.insert_eq_of_mem hm]; omega
    · exact (zeros_none h hm).le
theorem zeros_mono (p : α → Option β) {s t : Finset α} (h : s ⊆ t) :
    zeros p s ≤ zeros p t := Finset.card_le_card (Finset.filter_subset_filter _ h)
theorem build_mono {ops : β → β → Finset β} {goal : β} {k : ℕ} {s t : Finset β}
    (hs : s ⊆ t) (h : build ops goal k s) : build ops goal k t := by
  induction k generalizing s t with
  | zero => exact hs h
  | succ k ih =>
    rcases h with skip|⟨a,ha,b,hb,hab,z,hz,tail⟩
    · exact .inl (ih hs skip)
    · exact .inr ⟨a,hs ha,b,hs hb,hab,z,hz,ih (Finset.insert_subset_insert _ hs) tail⟩
def projects (p : α → Option β) (ops : α → α → Finset α) (ops' : β → β → Finset β) : Prop :=
  ∀ a b z, z ∈ ops a b → ∀ v, p z = some v →
    p a = some v ∨ p b = some v ∨
    ∃ u w, p a = some u ∧ p b = some w ∧ u ≠ w ∧ v ∈ ops' u w
theorem zeros_step {p : α → Option β} {ops : α → α → Finset α} {ops' : β → β → Finset β}
    (P : projects p ops ops') {a b z : α} (hz : z ∈ ops a b) (r : Finset α)
    (fresh : z ∉ insert a (insert b r)) :
    zeros p (insert a (insert b r)) ≤ zeros p (insert z r)+1 := by
  have mono := zeros_mono p (Finset.subset_insert z r)
  cases ha : p a with
  | some u =>
    rw [zeros_some ha]
    have h := zeros_le p b r
    omega
  | none =>
    cases hb : p b with
    | some v =>
      have h := zeros_le p a (insert b r)
      rw [zeros_some hb] at h
      omega
    | none =>
      have hzn : p z = none := by
        cases he : p z with
        | none => rfl
        | some v => simpa [ha, hb] using P a b z hz v he
      have hzout : z ∉ r := by intro h; exact fresh (by simp [h])
      rw [zeros_none hzn hzout]
      have u := zeros_le p a (insert b r)
      have v := zeros_le p b r
      omega
theorem zeros_budget {p : α → Option β} {ops : α → α → Finset α} {ops' : β → β → Finset β}
    {g : α} {g' : β} (hg : p g = some g') (P : projects p ops ops') {k : ℕ} {s : Finset α}
    (h : live ops g k s) : zeros p s ≤ k := by
  induction k generalizing s with
  | zero => change s = {g} at h; simp [h, zeros, hg]
  | succ k ih =>
    rcases h with skip | ⟨a,ha,b,hb,hab,z,hz,hn,r,rfl,tail⟩
    · exact (ih skip).trans (by omega)
    · exact (zeros_step P hz r hn).trans (Nat.succ_le_succ (ih tail))
theorem project_live {p : α → Option β} {ops : α → α → Finset α} {ops' : β → β → Finset β}
    {g : α} {g' : β} (hg : p g = some g') (P : projects p ops ops') {k : ℕ} {s : Finset α}
    (h : live ops g k s) (n : ℕ) (budget : k ≤ n + zeros p s) :
    build ops' g' n (kept p s) := by
  induction k generalizing s n with
  | zero =>
    change s = {g} at h
    have mem : g' ∈ kept p s := by simp [h, kept, hg]
    induction n with
    | zero => exact mem
    | succ n ih => exact Or.inl (ih (by omega))
  | succ k ih =>
    rcases h with skip|⟨a,ha,b,hb,hab,z,hz,hn,r,rfl,tail⟩
    · exact ih skip n (by omega)
    · have dz := zeros_step P hz r hn
      have free (hs : kept p (insert z r) ⊆ kept p (insert a (insert b r))) :
          build ops' g' n (kept p (insert a (insert b r))) :=
        build_mono hs (ih tail n (by omega))
      cases hZ : p z with
      | none =>
        apply free
        simp [kept_insert, hZ]
        exact fun _ hx => Finset.mem_union_right _ (Finset.mem_union_right _ hx)
      | some v =>
        rcases P a b z hz v hZ with ha|hb|⟨u,w,hA,hB,hw,hop⟩
        · apply free
          simp [kept_insert, hZ, ha]
        · apply free
          simp [kept_insert, hZ, hb]
        · rw [zeros_some hA, zeros_some hB] at budget
          have dz' := zeros_some hZ r
          have bound := zeros_budget hg P tail
          cases n with
          | zero => omega
          | succ n =>
            have next := ih tail n (by omega)
            have covers : kept p (insert z r) ⊆ insert v (kept p (insert a (insert b r))) := by
              simp [kept_insert,hZ,hA,hB]
              intro x hx
              simp only [Finset.mem_insert] at hx ⊢
              tauto
            exact Or.inr ⟨u, by simp [kept_insert,hA], w, by simp [kept_insert,hB],
                hw, v, hop, build_mono covers next⟩
end P2828Live

namespace P2828Check
def crop (m : W) (r : Fin 1378) (x : W) : W :=
  (x &&& m) ||| (if x[r.val] then ~~~m else 0)
def pos (m : W) (r : Fin 1378) (i : Nat) := if m.getLsbD i then i else r.val
theorem pos_lt (m : W) (r : Fin 1378) {i} (hi : i < 1378) : pos m r i < 1378 := by
  unfold pos; split <;> omega
theorem crop_bit (m : W) (r : Fin 1378) (x : W) (i : Nat) (hi : i < 1378) :
    (crop m r x).getLsbD i = x.getLsbD (pos m r i) := by
  unfold crop pos
  rw [BitVec.getLsbD_eq_getElem hi (x := m)]
  cases hr : x[r.val] <;> cases hm : m[i] <;> simp [hr,hm,hi]
theorem crop_and (m : W) (r : Fin 1378) (x y : W) :
    crop m r (x &&& y) = crop m r x &&& crop m r y := by
  apply BitVec.eq_of_getElem_eq
  intro j h
  change (crop m r (x &&& y)).getLsbD j = (crop m r x &&& crop m r y).getLsbD j
  simp only [crop_bit _ _ _ _ h, BitVec.getLsbD_and]
theorem crop_neg (m : W) (r : Fin 1378) (x : W) :
    crop m r (~~~x) = ~~~crop m r x := by
  apply BitVec.eq_of_getElem_eq
  intro j h
  change (crop m r (~~~x)).getLsbD j = (~~~crop m r x).getLsbD j
  simp only [crop_bit _ _ _ _ h, BitVec.getLsbD_not, h, pos_lt _ _ h]
def wrap (x : W) : Option W := if canon x = 0 then none else some (canon x)
theorem wrap_neg (x : W) : wrap (~~~x) = wrap x := by simp only [wrap, canon_neg]
def cropOpt (m : W) (r : Fin 1378) (x : W) := wrap (crop m r x)
theorem crop_canon (m : W) (r : Fin 1378) (x : W) :
    cropOpt m r (canon x) = cropOpt m r x := by
  unfold canon
  split
  · simp only [cropOpt, neg, crop_neg, wrap_neg]
  · rfl
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem binary_project {x y v : W} (h : wrap (x &&& y) = some v) :
    wrap x = some v ∨ wrap y = some v ∨
    ∃ u w, wrap x = some u ∧ wrap y = some w ∧ u ≠ w ∧ v ∈ basicOps u w := by
  have trivial (t : W) (ht : canon t = 0) : t = 0 ∨ t = BitVec.allOnes 1378 := by
    rcases sign t with h'|h' <;> rw [ht] at h'
    · exact .inl h'
    · exact .inr h'
  by_cases hx : canon x = 0
  · rcases trivial _ hx with rfl|rfl
    · rw [show (0 : W) &&& y = 0 from BitVec.zero_and] at h
      have h0 : wrap 0 = none := by decide
      have bad := h0.symm.trans h; cases bad
    · rw [BitVec.allOnes_and] at h; exact .inr (.inl h)
  by_cases hy : canon y = 0
  · rcases trivial _ hy with rfl|rfl
    · rw [show x &&& (0 : W) = 0 from BitVec.and_zero] at h
      have h0 : wrap 0 = none := by decide
      have bad := h0.symm.trans h; cases bad
    · rw [BitVec.and_allOnes] at h; exact .inl h
  have hn : canon (x &&& y) ≠ 0 := by intro hn; simp [wrap, hn] at h
  have hval : canon (x &&& y) = v := by simpa only [wrap, if_neg hn, Option.some.injEq] using h
  by_cases eq : canon x = canon y
  · rcases same_both eq with same|bad
    · exact .inl (by simp only [wrap, if_neg hx, ← hval, same])
    · exact False.elim (hn bad)
  · exact .inr (.inr ⟨canon x,canon y,by simp only [wrap,if_neg hx],by simp only [wrap,if_neg hy],eq,
        hval ▸ signed_both (sign x) (sign y)⟩)
theorem mask_projects (m : W) (r : Fin 1378) : P2828Live.projects (cropOpt m r) basicOps basicOps := by
  intro a b z hz v hv
  simp [basicOps, ops] at hz
  rcases hz with rfl|rfl|rfl|rfl <;>
    rw [crop_canon] at hv <;> simp only [cropOpt, both, neg, crop_and, crop_neg] at hv ⊢ <;>
    simpa only [wrap_neg] using binary_project hv
def projectedBudget (m : W) (r : Fin 1378) (n : Nat) (ws : List W) : Nat :=
  n - (ws.filter (fun w => (cropOpt m r w).isNone)).length
def available (m : W) (r : Fin 1378) (ws : List W) : List W :=
  (ws.filterMap (cropOpt m r)).dedup
theorem projected_bound (m : W) (r : Fin 1378) (n : Nat) {ws : List W} (hn : ws.Nodup) :
    n ≤ projectedBudget m r n ws + P2828Live.zeros (cropOpt m r) ws.toFinset := by
  let xs := ws.filter (fun w => (cropOpt m r w).isNone)
  have eq : (xs.toFinset) = ws.toFinset.filter (fun w => cropOpt m r w = none) := by
    ext w; simp [xs]
  have card := List.toFinset_card_of_nodup (hn.sublist (List.filter_sublist :
    xs.Sublist ws))
  rw [eq] at card
  change (ws.toFinset.filter (fun w => cropOpt m r w = none)).card = xs.length at card
  change n ≤ n-xs.length + (ws.toFinset.filter (fun w => cropOpt m r w = none)).card
  omega
end P2828Check

namespace P2828Check
open ThetaSigned
variable {T : Type}
def interpret (pick : T → Fin 1378) (w : W) : Wire T := fun x => w.getLsbD (pick x).val
theorem interpret_neg (pick : T → Fin 1378) (w : W) : interpret pick (neg w) = inv (interpret pick w) := by
  funext x
  simp [neg,interpret,inv,(pick x).isLt]
theorem interpret_canon (pick : T → Fin 1378) (w : W) :
    interpret pick (canon w) = interpret pick w ∨ interpret pick (canon w) = inv (interpret pick w) := by
  unfold canon; split
  · exact Or.inr (interpret_neg _ _)
  · exact Or.inl rfl
theorem interpret_both (pick : T → Fin 1378) (a b : W) :
    interpret pick (both a b) = bin false (interpret pick a) (interpret pick b) := by
  funext x;simp [interpret,both,bin]
theorem Run_pad {P : Set (Wire T)} {k f} (h : Run P k f) : Run P (k+1) f := by
  induction h with
  | done hf => exact .done hf
  | gate op ha hb _ ih => exact .gate op ha hb ih
theorem Run_inv {P : Set (Wire T)} {k f} (h : Run P k f) (hc : Closed P) : Run P k (inv f) := by
  induction h with
  | done hf => exact .done (hc.2 _ hf)
  | gate op ha hb _ ih => exact .gate op ha hb (ih (plus_closed hc _))
theorem decode_build (pick : T → Fin 1378) {g k s} (h : P2828Live.build basicOps g k s)
    {P : Set (Wire T)} (hp : Closed P) (raw : ∀ a ∈ s, interpret pick a ∈ P) :
    Run P k (interpret pick g) := by
  induction k generalizing s P with
  | zero => exact .done (raw _ h)
  | succ k ih =>
    rcases h with skip|⟨a,ha,b,hb,_,z,hz,ht⟩
    · exact Run_pad (ih skip hp raw)
    · have put {s₁ s₂ : W} (ha' : interpret pick s₁ ∈ P) (hb' : interpret pick s₂ ∈ P)
          (ed : z = canon (both s₁ s₂)) : Run P (k+1) (interpret pick g) := by
        apply Run.gate false ha' hb'
        apply ih ht (plus_closed hp _)
        intro v hv
        rcases Finset.mem_insert.mp hv with rfl|hv
        · rcases interpret_canon pick (both s₁ s₂) with same|opp
          · exact Or.inr (Or.inl (ed ▸ same.trans (interpret_both _ _ _)))
          · exact Or.inr (Or.inr (ed ▸ opp.trans (congrArg inv (interpret_both _ _ _))))
        · exact Or.inl (raw _ hv)
      have an : interpret pick (neg a) ∈ P := interpret_neg pick a ▸ hp.2 _ (raw _ ha)
      have bn : interpret pick (neg b) ∈ P := interpret_neg pick b ▸ hp.2 _ (raw _ hb)
      simp [basicOps,ops] at hz
      rcases hz with hz|hz|hz|hz
      · exact put (raw _ ha) (raw _ hb) hz
      · exact put (raw _ ha) bn hz
      · exact put an (raw _ hb) hz
      · exact put an bn hz
end P2828Check

namespace P2828Live
variable {α β : Type} [DecidableEq α] [DecidableEq β]
inductive History (ops : α → α → Finset α) (start : Finset α) : Finset α → Prop where
  | initial : History ops start start
  | gate {s} (old : History ops start s) {a b z} (ha : a ∈ s) (hb : b ∈ s)
      (hz : z ∈ ops a b) : History ops start (insert z s)
theorem History.contains {ops : α → α → Finset α} {start s} (h : History ops start s) : start ⊆ s := by
  induction h with
  | initial => exact Finset.Subset.refl _
  | gate old ha hb hz ih => exact ih.trans (Finset.subset_insert _ _)
theorem kept_mono (p : α → Option β) {s t : Finset α} (h : s ⊆ t) : kept p s ⊆ kept p t := by
  intro v hv
  obtain ⟨x,hx,px⟩ := Finset.mem_biUnion.mp hv
  exact Finset.mem_biUnion.mpr ⟨x,h hx,px⟩
theorem kept_of {p : α → Option β} {s : Finset α} {a : α} {v : β} (ha : a ∈ s) (hp : p a = some v) :
    v ∈ kept p s := Finset.mem_biUnion.mpr ⟨a,ha,by simp [hp]⟩
def price (p : α → Option β) (start s : Finset α) := (kept p s \ kept p start).card
theorem History.compose {ops : α → α → Finset α} {ops' : β → β → Finset β} {p : α → Option β}
    (proj : projects p ops ops') {start s} (h : History ops start s) {g : β} {k : ℕ}
    (tail : build ops' g k (kept p s)) : build ops' g (k + price p start s) (kept p start) := by
  induction h generalizing k with
  | initial => simpa [price] using tail
  | @gate s old a b z ha hb hz ih =>
    cases eq : p z with
    | none => simpa [price,kept_insert,eq] using ih (by simpa [kept_insert,eq] using tail)
    | some v =>
      have avail : kept p (insert z s) = insert v (kept p s) := by simp [kept_insert,eq]
      by_cases dup : v ∈ kept p s
      · rw [Finset.insert_eq_of_mem dup] at avail
        simpa [price,avail] using ih (avail ▸ tail)
      · have nv : v ∉ kept p start := fun hv => dup (kept_mono p old.contains hv)
        have cost : price p start (insert z s) = price p start s + 1 := by
          simp [price,avail,Finset.insert_sdiff_of_notMem, nv,dup]
        obtain ea|eb|⟨u,w,eu,ew,ne,mem⟩ := proj a b z hz v eq
        · exact (dup (kept_of ha ea)).elim
        · exact (dup (kept_of hb eb)).elim
        · have t : build ops' g (k+1) (kept p s) :=
            Or.inr ⟨u,kept_of ha eu,w,kept_of hb ew,ne,v,mem,avail ▸ tail⟩
          simpa [cost,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih t
theorem face_budget {ops : α → α → Finset α} {ops' : β → β → Finset β} {p : α → Option β}
    (proj : projects p ops ops') {start hist s g g' k} (past : History ops start hist)
    (pool : s ⊆ hist) (target : p g = some g') (run : live ops g k s) :
    build ops' g' (k - zeros p s + price p start hist) (kept p start) := by
  apply past.compose proj
  apply build_mono (kept_mono p pool)
  exact project_live target proj run _ (by omega)
end P2828Live

namespace P2828Check
open P2828 ThetaSigned
private def rowPages : Array Nat := #[0x888bd179af2564004118415a6b481102156200010192,0x89312223b1588cc519a31388ab555a80456800d59802,0x898be225af75740255c808894b595c00756e0195b005,0x8a51462831989ec622731789ab5d5e80c57802d5d80a,0x8a914d7dafa5bab701602b5b6b68150295b2b6014027,0x8b716a2cb1d8b115d9db1c8acb7d5f80e8aab795f00d,0x8c31822fafc8bcb89610118bab85608108b8b816000f,0x8d31a233b208cd1963231f8c6b91620138c4b8d61812,0x8d6c0980b0058c0541a84f8d4bfd7f2fd58a0501a04c,0x8e51c63846f8dcc899fb218dac123630359005d63816,0x8f71ea3cc788eed49a8b508ed1d63a3828e6d3da734d,0x91121e4348590920e414819011fe3f3878fad523e353,0x91922d843075d4ba41c838915225833055d0b9c1b836,0x92d2564a493925245a1b2392123e4730991abad64818,0x9432824fc9e93b271ac35793726a4cb8c93125dab355,0x95f2ba56cac9572aa54ca894f29a52b8f94928e51359,0x9652c594327960c9992b245dcbb41e83c5940641d873,0x9712de5b32b96acaa5a329966bbd6681c59806d6581a,0x9833025fcbe97ae6a5e3999772e9af35d972d71adb5a,0x99d336664cb995326644c798d31662361986d826135f,0x9af35a6acd49a7349d1ba29a3341ba37399edc9b8b70,0x9c938e714e19c137e6f4dd9b936e6d3779b2dda6c375,0x9e33c277cee9db3b275ba89d53a6743a79cf39a72ba6,0x9ff3fa7ecfc9f73ea7ccf89ef3da7abaa9e93ce793a9,0xa0b41281d02a02cb996b2ca00c3986b0c59c0741f85b,0xa1b43285d0aa12cc28432fa0ec428330f5a007d6781e,0xa354668c517a2d4568a513a254468850fa1cd91b1b62,0xa5149e93525a4948e91521a4147e8f51da38d9a8db65,0xa674ca98d30a5f4b9d8bb0a5b4b295d2aa52de9bcb78,0xa835029fd3ea7b4f29dd3aa734e29bd36a6adf29a37b,0xaa3542a7d4ea9b532a5d4aa93522a3d46a8b512a1d42,0xac3582afd5eabb572add5aab3562abd56aab552a9d52]
private def rowAt (i : Nat) : Fin 1378 := Fin.ofNat 1378 (((rowPages.getD (i/16) 0) >>> (11*(i % 16))) &&& 2047)
private def bits (x : Y) : BitVec 9 := (BitVec.ofBoolListLE (List.ofFn x)).setWidth 9
private theorem bits_spec (x : Y) (i : Fin 9) : (bits x).getLsbD i.val = x i := by
  simp only [bits,BitVec.getLsbD_setWidth,decide_eq_true i.isLt,Bool.true_and,BitVec.getLsbD_ofBoolListLE]
  fin_cases i <;> rfl
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem row_ok : ∀ (v : Fin 512) (i : Fin 9),
  assignment (rowAt v.val) i = (BitVec.ofNat 9 v.val).getLsbD i.val := by decide +kernel
def chooseRow (x : Y) := rowAt (bits x).toNat
theorem chooseRow_spec (x : Y) : assignment (chooseRow x)=x := by
  funext i
  have e := row_ok ⟨(bits x).toNat,(bits x).isLt⟩ i
  simpa only [chooseRow, BitVec.ofNat_toNat, BitVec.setWidth_eq, bits_spec] using e
end P2828Check

namespace P2828Check
open P2828 ThetaSigned P2828Live
def pin (fixed values : BitVec 9) (y : Y) : Y := fun i =>
  if fixed.getLsbD i.val then values.getLsbD i.val else y i
def faceMaskList (fixed values : BitVec 9) : List (Fin 9) → W
  | [] => BitVec.allOnes 1378
  | i :: is =>
    let rest := faceMaskList fixed values is
    let column := rawInputs.getD i.val 0
    if fixed.getLsbD i.val then
      (if values.getLsbD i.val then column else neg column) &&& rest
    else rest
def faceMask (fixed values : BitVec 9) := faceMaskList fixed values (List.finRange 9)
def pickFace (f v : BitVec 9) (y : Y) := chooseRow (pin f v y)
theorem pickFace_row (f v : BitVec 9) (y : Y) : assignment (pickFace f v y) = pin f v y := chooseRow_spec _
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem pickFace_inside (f v : BitVec 9) (y : Y) :
    (faceMask f v).getLsbD (pickFace f v y).val = true := by
  let r := pickFace f v y
  have val (i : Fin 9) : (rawInputs.getD i.val 0).getLsbD r.val = pin f v y i := by
    exact congrFun (pickFace_row f v y) i
  have go : ∀ is : List (Fin 9), (faceMaskList f v is).getLsbD r.val = true := by
    intro is
    induction is with
    | nil => simp only [faceMaskList,BitVec.getLsbD_allOnes,decide_eq_true r.isLt]
    | cons i is ih =>
      cases hi : f.getLsbD i.val <;> cases hv : v.getLsbD i.val <;>
        simp only [faceMaskList,hi,hv,Bool.false_eq_true,if_false,if_true,neg,BitVec.getLsbD_and,
          BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and,val,pin,ih] <;> rfl
  exact go _
theorem interpret_crop (f v : BitVec 9) (r : Fin 1378) (w : W) :
    interpret (pickFace f v) (crop (faceMask f v) r w) = interpret (pickFace f v) w := by
  funext y
  simp only [interpret,crop_bit _ _ _ _ (pickFace f v y).isLt,pos,pickFace_inside,if_true]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem interpret_raw (f v : BitVec 9) (i : Fin 9) : interpret (pickFace f v) (rawInputs.getD i.val 0) ∈ small := by
  have eq : interpret (pickFace f v) (rawInputs.getD i.val 0) = fun y => pin f v y i := by
    funext y;exact congrFun (pickFace_row f v y) i
  rw [eq]
  unfold pin
  split
  · exact small_closed.1 _
  · exact Or.inr ⟨i,Or.inl rfl⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem decoded_kept (f v : BitVec 9) (r : Fin 1378) :
    ∀ w ∈ kept (cropOpt (faceMask f v) r) inputs.toFinset, interpret (pickFace f v) w ∈ small := by
  intro w hw
  obtain ⟨a,ha,hw⟩ := Finset.mem_biUnion.mp hw
  obtain ⟨raw,mem,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  obtain ⟨i,hi,ei⟩ := List.getElem_of_mem mem
  have len : rawInputs.length = 9 := rfl
  have e : rawInputs.getD i 0 = raw := by rw [List.getD_eq_getElem _ _ hi];exact ei
  have hh : interpret (pickFace f v) raw ∈ small := e ▸ interpret_raw f v ⟨i,by omega⟩
  have hh' : cropOpt (faceMask f v) r (canon raw) = some w := by simpa using hw
  rw [crop_canon] at hh'
  unfold cropOpt wrap at hh'
  split at hh'
  · contradiction
  obtain rfl := Option.some.inj hh'
  rcases interpret_canon (pickFace f v) (crop (faceMask f v) r raw) with hs|hs <;>
    rw [hs,interpret_crop] <;> first | exact hh | exact small_closed.2 _ hh
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem interpret_goal (f v : BitVec 9) : interpret (pickFace f v) goal = fun y => nine (pin f v y) := by
  have hg : goal = ((-1 : BitVec 689) ++ (0 : BitVec 689)) := by decide +kernel
  funext y
  have z := graph_rows (pickFace f v y)
  rw [pickFace_row] at z
  rw [hg]
  exact z.symm
end P2828Check

namespace P2828Check
open P2828 ThetaSigned P2828Live
structure Face where
  fixed : BitVec 9
  values : BitVec 9
  lower : ℕ
  mask : W
  anchor : Fin 1378
def Face.Valid (c : Face) : Prop := c.mask = faceMask c.fixed c.values ∧
    (∃ g, cropOpt c.mask c.anchor goal = some g) ∧
    ∀ k, Run small k (fun y => nine (pin c.fixed c.values y)) → c.lower ≤ k
end P2828Check

namespace P2828Minor
open P2828Check P2828Live P2828Generic ThetaSigned
structure Minor where
  lower : Nat
  mask : W
  anchor : Fin 1378
def Minor.Valid (c : Minor) (base : List W) : Prop :=
  ∃ g, cropOpt c.mask c.anchor goal = some g ∧
    ∀ k, build basicOps g k (kept (cropOpt c.mask c.anchor) base.toFinset) → c.lower ≤ k
theorem transfer {T : Type} (base : List W) (c : Minor) (pick : T → Fin 1378)
    (inside : ∀ t, c.mask.getLsbD (pick t).val = true) (P : Set (Wire T)) (closed : Closed P)
    (raw : ∀ w ∈ base, interpret pick w ∈ P) (F : Wire T)
    (target : interpret pick goal = F) (someGoal : ∃ g, cropOpt c.mask c.anchor goal = some g)
    (lower : ∀ k, Run P k F → c.lower ≤ k) : c.Valid base := by
  obtain ⟨g,hg⟩ := someGoal
  refine ⟨g,hg,?_⟩
  intro k proof
  have same (w : W) : interpret pick (crop c.mask c.anchor w) = interpret pick w := by
    funext y
    simp only [interpret,crop_bit _ _ _ _ (pick y).isLt,pos,inside,if_true]
  have image (u v : W) (ev : cropOpt c.mask c.anchor u = some v) :
      interpret pick v = interpret pick u ∨ interpret pick v = inv (interpret pick u) := by
    unfold cropOpt wrap at ev
    split at ev
    · contradiction
    obtain rfl := Option.some.inj ev
    simpa only [same] using interpret_canon pick (crop c.mask c.anchor u)
  have haveRaw (w : W) (hw : w ∈ kept (cropOpt c.mask c.anchor) base.toFinset) : interpret pick w ∈ P := by
    obtain ⟨u,hu,m⟩ := Finset.mem_biUnion.mp hw
    have pr : cropOpt c.mask c.anchor u = some w := by simpa using m
    rcases image u w pr with e|e
    · rw [e]; exact raw _ (List.mem_toFinset.mp hu)
    · rw [e]; exact closed.2 _ (raw _ (List.mem_toFinset.mp hu))
  have yes := decode_build pick proof closed haveRaw
  apply lower k
  rcases image goal g hg with e|e
  · rwa [e,target] at yes
  · rw [e,target] at yes
    simpa only [inv_inv] using Run_inv yes closed
def seen (base h : List W) := h.toFinset ∪ base.toFinset
def rejects (base : List W) (c : Minor) (k : ℕ) (ws hist : List W) : Bool :=
  let p := cropOpt c.mask c.anchor
  decide (k - zeros p ws.toFinset + price p base.toFinset (seen base hist) < c.lower)
theorem safe {base c k ws hist} (valid : Minor.Valid c base)
    (past : History basicOps base.toFinset (seen base hist)) (pool : ws.toFinset ⊆ seen base hist)
    (run : live basicOps goal k ws.toFinset) : rejects base c k ws hist = false := by
  obtain ⟨g,hg,lower⟩ := valid
  exact decide_eq_false (Nat.not_lt.mpr (lower _ (face_budget (mask_projects _ _) past pool hg run)))
theorem ofOrdinary (c : Face) (valid : c.Valid) : Minor.Valid ⟨c.lower,c.mask,c.anchor⟩ inputs := by
  obtain ⟨em,⟨g,hg⟩,bound⟩ := valid
  refine ⟨g,hg,?_⟩
  rw [em] at hg ⊢
  intro k h
  have decoded := decode_build (pickFace c.fixed c.values) h P2828.small_closed (decoded_kept _ _ _)
  apply bound k
  unfold cropOpt wrap at hg
  split at hg
  · contradiction
  obtain rfl := Option.some.inj hg
  rcases interpret_canon (pickFace c.fixed c.values) (crop (faceMask c.fixed c.values) c.anchor goal) with e|e <;>
    rw [e,interpret_crop,interpret_goal] at decoded
  · exact decoded
  · simpa only [inv_inv] using Run_inv decoded P2828.small_closed
end P2828Minor

namespace P2828Check
open P2828Live
def gone (p : W → Option W) (ws : List W) := (ws.filter fun w => (p w).isNone).length
def paid (p : W → Option W) (ws : List W) (base : List W) :=
  ((ws.filterMap p).filter (fun z => !base.contains z)).dedup.length
theorem gone_eq (p : W → Option W) {ws : List W} (hn : ws.Nodup) : gone p ws = zeros p ws.toFinset := by
  unfold gone zeros
  rw [← List.toFinset_card_of_nodup (hn.sublist (List.filter_sublist ..))]
  congr 1
  ext a
  simp [Option.isNone_iff_eq_none]
end P2828Check

namespace P2828Check
def limited (m : W) (r : Fin 1378) (w : W) : W := (if w[r.val] then ~~~w else w) &&& m
theorem limited_anchor (m : W) (r : Fin 1378) (w : W) : (limited m r w)[r.val] = false := by
  cases e : w[r.val] <;> simp [limited,e]
theorem limited_crop (m : W) (r : Fin 1378) (w : W) :
    canon (crop m r w) = canon (limited m r w) := by
  cases e : w[r.val] with
  | false => simp [crop,limited,e]
  | true =>
    have eq : crop m r w = ~~~(limited m r w) := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simp only [crop,limited,e,ite_true,BitVec.getElem_or,BitVec.getElem_and,BitVec.getElem_not]
      cases w[i] <;> cases m[i] <;> rfl
    rw [eq,canon_neg]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem limited_zero (m : W) (r : Fin 1378) (w : W) :
    canon (limited m r w) = 0 ↔ limited m r w = 0 := by
  constructor
  · intro h
    rcases sign (limited m r w) with a|a
    · exact a.trans h
    · rw [h] at a
      have e := congrArg (fun z : W => z[r.val]) a
      rw [limited_anchor] at e
      exact False.elim (Bool.noConfusion (e.trans (BitVec.getElem_allOnes _ _)))
  · rintro h;rw [h];decide
def projectFast (m : W) (r : Fin 1378) (w : W) : Option W :=
  let q := limited m r w
  if q=0 then none else some (canon q)
theorem projectFast_eq (m : W) (r : Fin 1378) : projectFast m r = cropOpt m r := by
  funext w
  simp only [projectFast,cropOpt,wrap,limited_crop,limited_zero]
end P2828Check

namespace P2828Minor
open P2828Check P2828Live
private theorem kept_list (p : W → Option W) (ws : List W) :
    kept p ws.toFinset = (ws.filterMap p).toFinset := by
  ext a; simp [kept,List.mem_filterMap]
theorem price_eq (base : List W) (p : W → Option W) (hist : List W) :
    paid p hist (base.filterMap p) = price p base.toFinset (seen base hist) := by
  let h := (hist.filterMap p).filter fun z => !(base.filterMap p).contains z
  change h.dedup.length = _
  rw [← List.toFinset_card_of_nodup (List.nodup_dedup _),List.toFinset_dedup]
  unfold price seen
  rw [show kept p (hist.toFinset ∪ base.toFinset) = kept p hist.toFinset ∪ kept p base.toFinset by
    ext a; simp [kept, or_and_right, exists_or]]
  rw [kept_list,kept_list]
  congr 1
  ext a
  simp [h]
def cheap (base : List W) (c : Minor) (k : Nat) (ws hist : List W) : Bool :=
  let p := projectFast c.mask c.anchor
  let rem := k - (ws.filter (fun w => limited c.mask c.anchor w == 0)).length
  if c.lower ≤ rem then false else
    decide (rem + paid p hist (base.filterMap p) < c.lower)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem cheap_eq (base : List W) (c : Minor) (k : Nat) (ws hist : List W) (hn : ws.Nodup) :
    cheap base c k ws hist = rejects base c k ws hist := by
  have columns (w : W) : (projectFast c.mask c.anchor w).isNone = (limited c.mask c.anchor w == 0) := by
    let z := limited c.mask c.anchor w
    change (if z=0 then none else some (canon z)).isNone = (z == 0)
    by_cases hz : z=0
    · rw [if_pos hz,hz];rfl
    · rw [if_neg hz];exact (beq_eq_false_iff_ne.mpr hz).symm
  change _ = decide (_ < _)
  rw [← projectFast_eq,←gone_eq _ hn,← price_eq]
  unfold cheap gone
  simp only [columns]
  split
  · symm; apply decide_eq_false;omega
  · rfl
end P2828Minor

namespace P2828Truth
open P2828Check P2828Minor P2828Live P2828Generic ThetaSigned SignedCofactor
def index {n} (x : Fin n → Bool) : Nat :=
  (List.finRange n).foldl (fun a i => a + if x i then 2^i.val else 0) 0
def truth (n t : Nat) (x : Fin n → Bool) := t.testBit (index x)
def select {n} (map : Array (Fin 1378)) (x : Fin n → Bool) : Fin 1378 := map.getD (index x) 0
def literal {n} (w : Wire (Fin n → Bool)) : Prop :=
  (∃ b : Bool, ∀ x, w x=b) ∨ ∃ i : Fin n, ∃ b : Bool, ∀ x, w x = (x i != b)
instance {n} (w : Wire (Fin n → Bool)) : Decidable (literal w) := by unfold literal;infer_instance
theorem mem_literal {n w} (hw : @literal n w) : w ∈ literals n := by
  rcases hw with ⟨b,e⟩|⟨i,b,e⟩
  · exact Or.inl ⟨b,funext e⟩
  · refine Or.inr ⟨i,?_⟩
    cases b
    · exact Or.inl (funext fun x => by simpa using e x)
    · exact Or.inr (funext fun x => by simpa [inv] using e x)
theorem validates {n t} (base : List W) (c : Minor) (rows : Array (Fin 1378))
    (inside : ∀ x : Fin n → Bool, c.mask.getLsbD (select rows x).val=true)
    (raw : base.all (fun w => decide (literal (interpret (@select n rows) w))) = true)
    (target : ∀ x : Fin n → Bool, interpret (select rows) goal x = truth n t x)
    (someGoal : ∃ g, cropOpt c.mask c.anchor goal = some g)
    (lower : ∀ k, Run (literals n) k (truth n t) → c.lower ≤ k) : c.Valid base := by
  apply transfer base c (select rows) inside _ (literals_closed n) _ _ (funext target) someGoal lower
  intro w hw
  exact mem_literal (of_decide_eq_true (List.all_eq_true.mp raw w hw))
theorem table_live {n k t} (cols : List W) (sites : List (Fin 689))
    (len : cols.length=n) (agrees : ∀ r : Fin 1378, truth n t (columnPick cols r) = wordBit r goal)
    (crit : critical (signals cols) sites=true) (run : Run (literals n) k (truth n t)) :
    live basicOps goal k (signals cols).toFinset := by
  obtain ⟨s,hs,hr⟩ := compress (anyBuild _ agrees run _ (columnGood cols len))
  exact all_required crit hs hr ▸ hr
theorem table_lower {n t cap extra k : Nat} (cols : List W) (sites : List (Fin 689))
    (len : cols.length=n) (agrees : ∀ r : Fin 1378, truth n t (columnPick cols r) = wordBit r goal)
    (crit : critical (signals cols) sites=true) (nodup : (signals cols).Nodup)
    (room : extra + (signals cols).length = cap+1) (scan : optimized cap extra (signals cols) = false)
    (run : Run (literals n) k (truth n t)) : cap+1 ≤ k := by
  by_contra! tooSmall
  have hl := table_live cols sites len agrees crit run
  have pad (k' : Nat) (h : k≤k') : live basicOps goal k' (signals cols).toFinset := by
    induction h with
    | refl => exact hl
    | step _ ih => exact Or.inl ih
  have yes := optimized_complete cap _ extra nodup room (pad _ (by omega))
  exact Bool.noConfusion (yes.symm.trans scan)
end P2828Truth

namespace C4Base
open ThetaSigned
abbrev Y := Fin 7 → Bool
def small : Set (Wire Y) := {f | (∃ c, f=bit c) ∨ ∃ i : Fin 7, f=(fun x => x i) ∨ f=inv (fun x => x i)}
def nine (y : Y) : Bool := (y 0 && y 1) || (y 2 && y 4) || (y 0 && y 5) || (y 2 && y 5) || (y 3 && y 5) || (y 1 && y 6) || (y 3 && y 6) || (y 4 && y 6)
theorem small_closed : Closed small := by
  constructor
  · exact fun b => Or.inl ⟨b,rfl⟩
  · intro f hf
    rcases hf with ⟨b,rfl⟩|⟨i,rfl|rfl⟩
    · exact Or.inl ⟨!b,rfl⟩
    · exact Or.inr ⟨i,Or.inr rfl⟩
    · exact Or.inr ⟨i,Or.inl (inv_inv _)⟩
end C4Base

namespace UnifiedSearch
open P2828Minor P2828Check P2828Live
def widen (v : Nat) : W :=
  let copy := fun x : Nat => x + (if x.testBit 0 then (((1<<<457)-1)<<<232) else 0)
  BitVec.ofNat 1378 (copy (v % (1<<<232)) ||| (copy (v>>>232) <<< 689))
abbrev Advice := List W → List W → List Minor
def checkChild (base : List W) (ad : Advice) (further : ℕ → List W → List W → Bool) (k : ℕ)
    (ws hist : List W) (extra : ℕ) (child : List W) : Bool :=
  match child with
  | [] => false
  | z :: _ => !(ws.contains z) && !((ad ws hist).any (fun c => cheap base c k child (z::hist))) &&
      further extra child (z::hist)
def guided (base : List W) (ad : Advice) : ℕ → ℕ → List W → List W → Bool
  | 0, _, ws, _ => ws == [goal]
  | k+1, extra, ws, hist => ws == [goal] ||
    let more := checkChild base ad (guided base ad k) k ws hist
    (pairs ws).any (fun (a,b,r) => dispatch extra more a b r)
theorem guided_complete (base : List W) (ad : Advice) (valid : ∀ ws hist, ∀ c ∈ ad ws hist, c.Valid base)
    (n : ℕ) (ws hist : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n+1) (past : History basicOps base.toFinset (seen base hist))
    (pool : ws.toFinset ⊆ seen base hist) (h : live basicOps goal n ws.toFinset) :
    guided base ad n extra ws hist = true := by
  induction n generalizing ws hist extra with
  | zero => simp [guided,singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a,ha,b,hb,hab,z,hz,hout,needed,hs,tail⟩
    · simp [guided,singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have extendSeen : seen base (z::hist) = insert z (seen base hist) := by simp [P2828Minor.seen]
      have extended : History basicOps base.toFinset (seen base (z::hist)) := extendSeen ▸ .gate past (pool ha) (pool hb) hz
      have go {a b : W} (perm : ws.Perm (a::b::r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (checkChild base ad (guided base ad k) k ws hist) a b r = true := by
        obtain ⟨kept,hk,hnk,hfin⟩ := recover_kept perm hn hset
        have sub : kept.toFinset ⊆ ws.toFinset := by rw [hfin,hset];exact (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
        have hnd : (z::kept).Nodup := List.nodup_cons.mpr ⟨fun hv => hout (sub (List.mem_toFinset.mpr hv)),hnk⟩
        have hl : live basicOps goal k (z::kept).toFinset := by simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd,List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) _ hop hk (by omega) (by omega) (cuts_full hl)
        have pool' : (z::kept).toFinset ⊆ seen base (z::hist) := by
          rw [extendSeen,List.toFinset_cons]; exact Finset.insert_subset_insert _ (sub.trans pool)
        have succ := ih _ _ (k-kept.length) hnd (by simp;omega) extended pool' hl
        have none : (ad ws hist).any (fun c => cheap base c k (z::kept) (z::hist)) = false :=
          List.any_eq_false.mpr fun c hc => by rw [cheap_eq _ _ _ _ _ hnd,safe (valid _ _ c hc) extended pool' hl]; decide
        have fresh : z ∉ ws := by simpa using hout
        simp [checkChild,fresh,none,succ]
      simp only [guided,Bool.or_eq_true,List.any_eq_true]
      right
      rcases hm with direct|swap
      · exact ⟨(a,b,r),direct,go hp hs hz⟩
      · exact ⟨(b,a,r),swap,go (hp.trans (.swap _ _ _)) (by rw [hs,Finset.insert_comm]) (ops_swap a b ▸ hz)⟩
end UnifiedSearch
namespace UnifiedLeaf0
open UnifiedSearch (widen)
open P2828Check P2828Live P2828Generic P2828Truth P2828Minor ThetaSigned SignedCofactor
def cols : List W := [(widen 0x9fdebe96753d7f9fcf4797e96fffc94c4d978adc1243e73f76be7852f3e020416080c308a089c09803102602003301184c18c02070349c380073),(widen 0x3dbf723bf2ffa5c837fa6ba7269ebfc7fba78763c9f61af58bdc8aae7c42408e4209021800488010166061a85442a48200158000cc85dc000e7c),(widen 0xf73357f53f7f5cbfedceb09cf38bc4bbdf4c7efcb71e899d50ef15cf9108ce0c0a1000a248003a045846812884442c02a026360509806001cf80),(widen 0x67eebf238ed7dfa5b4fdfe7f0fffa166e033a616603d7fe37df5e1f4261815009c500c040b2414016084985081840a649140245e034021c1f000),(widen 0x4ef7d7cbfd4fab639a1b29fff1aa3ff9d7df7921efcce810dbf9ff09483100300402e844b22104e980091e010110135009880898127a01fe0000)]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem scan : optimized 6 2 (signals cols)=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem lower (k) (run : Run (literals 5) k (truth 5 0xfefceea0)) : 7≤k :=
  table_lower (cap:=6) (extra:=2) cols [7,13,0,1,3] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) scan run
end UnifiedLeaf0
namespace UnifiedLeaf1
open UnifiedSearch (widen)
open P2828Check P2828Live P2828Generic P2828Truth P2828Minor ThetaSigned SignedCofactor
def cols : List W := [(widen 0x7fe00bf047d607f5013f806ff8223faedea87f16055dbf1e38494f83c77f807381870001f0021f0000f8003f800e003820304cae0e38000781c3),(widen 0xf768245a7ed6a04cb9d9a418129df4ec0de7ef01af97f7224bc7389e4d8060047038d6080500c08090005dc029209787080b93500001c7381e0c),(widen 0xd2db6695ab2d20de0eac75c9a7729255859f12ccd9e6de4fc092913ff0088824558100a0464626241815620b440c9810005046ce0fc000001ff0),(widen 0x8fc6de0ce0635c3d6684cfc4ad8651f0737db9ae0bf8fa8495f83fe490a140c208501b4d090090c0c02081500271238dac09b8300001f83fe000),(widen 0xb1b18db3611f33831c6333236bf1ce33f343485e57ff1cf921ffc2092200010820609c40019800db0302898033b142c01e0fb110f001ffc00000),(widen 0x8f8fb38e9f00fe70fde70f1f188fc18830c0c1e3f3ffe0ffff24245008420230828200b212ed231d0d5c02238004405052b04480fffe00000000)]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem scan : optimized 7 2 (signals cols)=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem lower (k) (run : Run (literals 6) k (truth 6 0xfffeffccfafaf888)) : 8≤k :=
  table_lower (cap:=7) (extra:=2) cols [2,0,13,4,1,3] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) scan run
end UnifiedLeaf1
namespace UnifiedLeaf2
open UnifiedSearch (widen)
open P2828Check P2828Live P2828Generic P2828Truth P2828Minor ThetaSigned SignedCofactor
def cols : List W := [(widen 0xffffffffffffffffffffffffffffffffffffffffffdfd7fe57d3e7f57bffffffffffffffffffffffffffffffffffffffffff20340081500c601b),(widen 0xba79cbfd2e5daadc00000000000000000000000000000000000000000044a43a34101b60dc),(widen 0xffffffffffffffffffffffffffffffffffffffffff3ff45d4fd633bce9000000000000000000000000000000000000000000c20ad2260ea28ce0),(widen 0xed7ffbbcedfcef960000000000000000000000000000000000000000001240840a88c08f00)]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem scan : optimized 3 0 (signals cols)=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem lower (k) (run : Run (literals 4) k (truth 4 0xeea0)) : 4≤k :=
  table_lower (cap:=3) (extra:=0) cols [5,9,0,1] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) scan run
end UnifiedLeaf2
namespace UnifiedLeaf3
open UnifiedSearch (widen)
open P2828Check P2828Live P2828Generic P2828Truth P2828Minor ThetaSigned SignedCofactor
def cols : List W := [(widen 0x7a023fb020ffe829ff437f8447f9a1f647fc17c85d6ff8e0f0f0f1c737700c3c000c3f8040fe083f8007f000f007e063839d6fb8e0707070c31),(widen 0x48a93fbb5a2106b26c3e62453bf2b9cef3fdc137a7e7fc9279393935d708a01c3b0230068160144800bb8095e05b81c0848221000038383831c6),(widen 0x4d64d4c699a3538dd68ea38ee5296f46de8aa9ddd8fb5bf012527fc1f848f6c040582107cd93ca6242c40d29ce4c020134d87b5bf000003fc1f8),(widen 0xac1c7211b758ceedc19790bb0ca7e0f3afa665f893fc7124bfc03ffe008458280db3782c85cb1483a902a021b0bf9565e491fc70003fc03ffe00),(widen 0x9b63b24f8fc6399c326d8d9fe399e7319e9e1ac84eff9a493fffd240a81000322e23c0301000158d2d1300c63191d800c8078480003fffc00000),(widen 0xf71f4dc07f7df87bf1e37c791f8710f341807e03fa7fe3ffe4a4a4ab04610340804c04416a10623050044f000600000a01280203ffc000000000)]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem scan : optimized 6 1 (signals cols)=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem lower (k) (run : Run (literals 6) k (truth 6 0xffffffccf8f88888)) : 7≤k :=
  table_lower (cap:=6) (extra:=1) cols [1,0,22,39,3,2] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) scan run
end UnifiedLeaf3
namespace UnifiedC4
open UnifiedSearch (widen)
open P2828Check P2828Live P2828Generic P2828Truth P2828Minor ThetaSigned SignedCofactor
def cols : List W := [(widen 0x507619494848240f0e83fb98007ac0be8fc384922aa4aa49400495ffff003e38000000000f0f83fff8003fc07f80c004922aa4aa49400495f800),(widen 0xa2120815d8690b2b023eaa88056a6c8abfc2d924c449009014a93ffabf00000001f87801f0003c000007c03f803f005924c449009014a90002bf),(widen 0x30bac2258c801200107ffbaf58003b5b51540038b071ccfd81ffd8500a003fc00000000000003ffffff8003fffc0000038b071ccfd800018500a),(widen 0x50124ba0112dd5fa07fffcfe6bf000062a80e3f077e00e3fe0e01602c00000000000001fff03fffffffffc00000000e3f077e00e0000e01602c),(widen 0xc82240c1ee84618fdb6f330d4800091344106fc007801ffc18cfc1833000000001ff8001ffffc000000000000000006fc00780000018cfc18330),(widen 0xf1fc9703fd577f1dacb7c3f674b3b27c001f70003ffff0021ff02007c0ffc00001fffffe00000000000000000000007000000010021ff02007c0),(widen 0xfe3f27fdf66781eecf3bfc07873c3c6038207ffff8001f03e1003e0400fffffffe0000000000000000000000000000000038001f03e1003e0400)]
def base := signals cols
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem root {k} (h : Run C4Base.small k C4Base.nine) : live basicOps goal k base.toFinset := by
  have eq : ∀ x, C4Base.nine x=truth 7 0xfffffffeffffffccfffafffaf8f88888 x := by decide +kernel
  exact table_live cols [0,11,22,33,42,53,70] (by decide +kernel) (by decide +kernel) (by decide +kernel) ((funext eq) ▸ h)
def face0 : Minor := ⟨7,(widen 0xd89e6a22796d0d0f1400467fa851341403c224911125526ab52400000ffc1c7fe0787fe00f0400007f8000000403fa24911125526ab526a0540),6⟩
def pick0 : Array (Fin 1378) := #[87,42,57,45,22,711,25,714,6,717,722,749,8,719,724,823,17,19,726,728,737,739,770,825,10,721,730,826,741,883,856,827]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid0 : face0.Valid base := validates (n:=5) (t:=0xfefceea0) base face0 pick0
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) UnifiedLeaf0.lower
def face1 : Minor := ⟨7,(widen 0x7453d1a117b8c7024800450a7ffc4a4aaab9007480e20026600262cc5ffc03ffe007ffe000000000007ffc0003fff9007480e33026730262cc5),0⟩
def pick1 : Array (Fin 1378) := #[87,11,57,13,0,689,2,691,6,695,722,747,7,696,723,810,17,18,726,727,706,707,763,812,10,699,730,813,710,879,819,814]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid1 : face1.Valid base := validates (n:=5) (t:=0xfefceea0) base face1 pick1
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) UnifiedLeaf0.lower
def face2 : Minor := ⟨8,(widen 0xfafedb45feed22a05f8000301940ffff9d57f1c0f881ff1c01f1fe9fd3fffffffffffffe000fc0000000003ffffffff1c0f881ff1ffff1fe9fd3),0⟩
def pick2 : Array (Fin 1378) := #[87,11,0,689,42,12,1,690,22,15,4,693,711,712,713,794,6,695,7,696,717,744,718,796,8,697,9,698,719,797,720,884,17,18,706,707,19,20,708,709,737,738,769,850,739,740,804,906,10,699,710,879,721,758,806,909,741,852,775,887,883,910,888,889]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid2 : face2.Valid base := validates (n:=6) (t:=0xfffeffccfafaf888) base face2 pick2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) UnifiedLeaf1.lower
def face3 : Minor := ⟨4,(widen 0xd0124822316c0d0e1000440a285000000282241010211022a00000000ffc007fe0787fe00f040000000000000003fa241010211022b52620540),6⟩
def pick3 : Array (Fin 1378) := #[87,57,22,25,6,722,8,724,17,726,737,770,10,730,741,856]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid3 : face3.Valid base := validates (n:=4) (t:=0xeea0) base face3 pick3
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) UnifiedLeaf2.lower
def face4 : Minor := ⟨4,(widen 0xc0980000080200008000301040c28c814780000001e00000300018c300000000007ffe000000000000003fffffff9000c001e01c06300018c3),0⟩
def pick4 : Array (Fin 1378) := #[87,11,42,12,0,689,1,690,6,695,717,744,7,696,718,796]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid4 : face4.Valid base := validates (n:=4) (t:=0xeea0) base face4 pick4
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) UnifiedLeaf2.lower
def face5 : Minor := ⟨4,(widen 0x240000000000000800000000001140003880000001800018500a003fc00000000000003ffffff8003fffc0000038b071ccfd800018500a),1⟩
def pick5 : Array (Fin 1378) := #[42,19,12,20,45,728,14,729,1,708,690,709,3,766,692,836]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid5 : face5.Valid base := validates (n:=4) (t:=0xeea0) base face5 pick5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) UnifiedLeaf2.lower
def face6 : Minor := ⟨4,(widen 0xa000004000000000000000000000449009014a900000000000001f87801f0003c000007c03f803f005924c449009014a90002bf),0⟩
def pick6 : Array (Fin 1378) := #[0,1,2,3,4,713,5,716,7,718,723,751,9,720,725,843]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid6 : face6.Valid base := validates (n:=4) (t:=0xeea0) base face6 pick6
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) UnifiedLeaf2.lower
def face7 : Minor := ⟨4,(widen 0x480000000000001000000000000000049200000a494004800000003e38000000000f0f83fff8003fc07f80c004922aa4aa49400495f800),11⟩
def pick7 : Array (Fin 1378) := #[11,18,12,20,13,727,14,729,15,738,712,740,16,771,715,837]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid7 : face7.Valid base := validates (n:=4) (t:=0xeea0) base face7 pick7
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) UnifiedLeaf2.lower
def face8 : Minor := ⟨4,(widen 0x600100000000000000000400000007800000180001833000000001ff8001ffffc000000000000000006fc00780000018cfc18330),4⟩
def pick8 : Array (Fin 1378) := #[22,15,25,16,4,693,5,694,8,697,724,754,9,698,725,857]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid8 : face8.Valid base := validates (n:=4) (t:=0xeea0) base face8 pick8
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) UnifiedLeaf2.lower
def face9 : Minor := ⟨4,(widen 0xa00400402a000a05100000009000d0110000140c000051400014a00000001c7fe000000000040000000003f807f3f8140d0014514a0014a0013),0⟩
def pick9 : Array (Fin 1378) := #[87,22,0,4,42,711,1,713,17,737,706,769,19,739,708,804]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid9 : face9.Valid base := validates (n:=4) (t:=0xeea0) base face9 pick9
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) UnifiedLeaf2.lower
def face10 : Minor := ⟨4,(widen 0xc0d000008020001080003018008315001500000080e00c0050c00140000000000787fe000fc000000000007fc0ffa0c00080e00c0a50c09940),6⟩
def pick10 : Array (Fin 1378) := #[87,42,11,12,22,711,15,712,6,717,695,744,8,719,697,797]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid10 : face10.Valid base := validates (n:=4) (t:=0xeea0) base face10 pick10
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) UnifiedLeaf2.lower
def face11 : Minor := ⟨4,(widen 0xa000840022800a043000000014044808c0081c040000300000006881100003ffe000000000fc00000000000003fff81c0488023006001c68811),0⟩
def pick11 : Array (Fin 1378) := #[87,17,11,18,22,737,15,738,0,706,689,707,4,769,693,850]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid11 : face11.Valid base := validates (n:=4) (t:=0xeea0) base face11 pick11
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) UnifiedLeaf2.lower
def face12 : Minor := ⟨4,(widen 0x545350a0112845024800450a295802400290003080620026200000440ffc03ffe0007fe0000000000003fc00000ff8003080633026310262c40),6⟩
def pick12 : Array (Fin 1378) := #[87,57,11,13,17,726,18,727,6,722,695,747,10,730,699,813]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid12 : face12.Valid base := validates (n:=4) (t:=0xeea0) base face12 pick12
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) UnifiedLeaf2.lower
def face13 : Minor := ⟨4,(widen 0x589a6220112905020000462b2851240002c000910124002a310000000ffc1c7fe0007fe0000000007f8000000403f800910125526a3102a0440),6⟩
def pick13 : Array (Fin 1378) := #[87,57,42,45,17,726,19,728,6,722,717,749,10,730,721,826]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid13 : face13.Valid base := validates (n:=4) (t:=0xeea0) base face13 pick13
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) UnifiedLeaf2.lower
def face14 : Minor := ⟨7,(widen 0xe0368fc02a880e253483c098b4c4d83ffe08fffc0000ffde00fdff83f003ffffe000001ffffffffffffffffffffff8fffffffeffde00fdff83f),0⟩
def pick14 : Array (Fin 1378) := #[87,11,0,689,42,12,1,690,57,13,2,691,45,14,3,692,22,15,4,693,711,712,713,794,25,16,5,694,714,715,716,828,17,18,706,707,19,20,708,709,726,727,763,812,728,729,766,836,737,738,769,850,739,740,804,906,770,771,772,858,825,837,844,838]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid14 : face14.Valid base := validates (n:=6) (t:=0xffffffccf8f88888) base face14 pick14
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) UnifiedLeaf3.lower
def face15 : Minor := ⟨7,(widen 0x1c0d80209987e1130c403f878c3c39fc7df800007ffe0fc1effc1fbff00000001ffffffffffffffffffffffffffffffffc7ffe0fc1effc1fbff),0⟩
def pick15 : Array (Fin 1378) := #[87,0,11,689,22,4,15,693,57,2,13,691,25,5,16,694,42,1,12,690,711,713,712,794,45,3,14,692,714,716,715,828,6,7,695,696,8,9,697,698,722,723,747,810,724,725,754,857,717,718,744,796,719,720,797,884,749,751,750,832,823,843,833,834]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid15 : face15.Valid base := validates (n:=6) (t:=0xffffffccf8f88888) base face15 pick15
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) UnifiedLeaf3.lower
def face16 : Minor := ⟨4,(widen 0x70124121133887020000440a785040020281005400a00022600220000ffc007fe007ffe000000000007c000003f3f9005400a110227302204c5),0⟩
def pick16 : Array (Fin 1378) := #[87,57,0,2,6,722,7,723,17,726,706,763,10,730,710,819]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid16 : face16.Valid base := validates (n:=4) (t:=0xeea0) base face16 pick16
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) UnifiedLeaf2.lower
def face17 : Minor := ⟨4,(widen 0x888c20026840080510000201800134100142040100055040150400000ffc1c7fe0787fe000040000000000000403fa04010005506ab506a0540),6⟩
def pick17 : Array (Fin 1378) := #[87,42,17,19,6,717,10,721,22,711,737,739,8,719,741,883]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid17 : face17.Valid base := validates (n:=4) (t:=0xeea0) base face17 pick17
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) UnifiedLeaf2.lower
def face18 : Minor := ⟨4,(widen 0x244190010690020048000100140c4a488039000480020000000260cc1ffc03ffe007ffe0000000000000000003fff9000480033026730260cc1),0⟩
def pick18 : Array (Fin 1378) := #[87,11,17,18,6,695,10,699,0,689,706,707,7,696,710,879]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid18 : face18.Valid base := validates (n:=4) (t:=0xeea0) base face18 pick18
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) UnifiedLeaf2.lower
def face19 : Minor := ⟨4,(widen 0xc0160a0028080c0514004018a0401014020024900000524a0024000000001c7fe00000000f0400007f8000000403f824911124524a0024a0000),17⟩
def pick19 : Array (Fin 1378) := #[87,17,42,19,57,726,45,728,22,737,711,739,25,770,714,825]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid19 : face19.Valid base := validates (n:=4) (t:=0xeea0) base face19 pick19
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) UnifiedLeaf2.lower
def face20 : Minor := ⟨4,(widen 0x60128180028806000000400834c4480aaa0800740000000600006280500003ffe000000000000000007ffc0003fff8007480e23006000062805),0⟩
def pick20 : Array (Fin 1378) := #[87,17,11,18,57,726,13,727,0,706,689,707,2,763,691,812]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid20 : face20.Valid base := validates (n:=4) (t:=0xeea0) base face20 pick20
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) UnifiedLeaf2.lower
def face21 : Minor := ⟨4,(widen 0x180c002019050103040006078810301401c0000011240240a52400000000000000787fe00f0400007f8000000403fa249011240240a52400140),6⟩
def pick21 : Array (Fin 1378) := #[87,42,57,45,22,711,25,714,6,717,722,749,8,719,724,823]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid21 : face21.Valid base := validates (n:=4) (t:=0xeea0) base face21 pick21
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) UnifiedLeaf2.lower
def face22 : Minor := ⟨4,(widen 0x140180201180c102080005020c3c084828b8000000e200006000028c500000000007ffe000000000007ffc0003fff9007400e200006300028c5),0⟩
def pick22 : Array (Fin 1378) := #[87,11,57,13,0,689,2,691,6,695,722,747,7,696,723,810]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid22 : face22.Valid base := validates (n:=4) (t:=0xeea0) base face22 pick22
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) UnifiedLeaf2.lower
def faces : Array Minor := #[face0,face1,face2,face3,face4,face5,face6,face7,face8,face9,face10,face11,face12,face13,face14,face15,face16,face17,face18,face19,face20,face21,face22]
def faceAt (i : Fin 23) := faces[i.val]
theorem valid (i : Fin 23) : (faceAt i).Valid base := by
  fin_cases i
  · exact valid0
  · exact valid1
  · exact valid2
  · exact valid3
  · exact valid4
  · exact valid5
  · exact valid6
  · exact valid7
  · exact valid8
  · exact valid9
  · exact valid10
  · exact valid11
  · exact valid12
  · exact valid13
  · exact valid14
  · exact valid15
  · exact valid16
  · exact valid17
  · exact valid18
  · exact valid19
  · exact valid20
  · exact valid21
  · exact valid22
def masks : Array Nat := #[0x57,0x113,0x0,0x202,0x2,0x1067,0xc23f,0x3,0x8277,0x1,0x4,0xf7,0x827,0xe3,0x215,0x1e7,0x224,0xce7,0x117,0x286,0x12,0x6,0x22,0x317,0x2f,0x1b3,0x60,0x227,0x441,0x287,0x10,0x1a7,0xc72,0xa3,0x41,0x23,0x36,0x150,0x1d7,0x5,0x9f7,0x7,0x111,0x81f7,0x1a3,0x67,0x2af,0x4c7,0x81,0x177,0x917,0x9b7,0x282,0x291,0xc7,0x517,0x9d7,0x2b4,0x4cb7,0x8b57,0x687,0x183,0x1a57,0xc1,0xab,0x800,0x237,0x6f,0x140,0x2187,0x15,0xc7f7,0x100,0x8217,0x5c1,0x244,0x46,0x80b7,0x4ef,0x43a7,0x80,0x417,0x102,0xf17,0x8a17,0x11,0xe1,0x210,0x3d7,0x82,0x8197,0x16b,0x257,0x285,0x110,0xa17,0x43,0xc157,0x822,0x4a07,0x357,0x37,0x8157,0x2c7,0x3e7,0x2a0,0x4e7,0x153,0x8a6,0x887,0x681,0x4000,0x83f7,0x977,0x4727,0x127,0x27,0x4215,0x26,0x3f,0xc355,0x577,0x97,0x40c7,0x25,0xd7,0x137,0x8b97,0x8127,0xb7,0x2d5,0x116,0x17,0x337,0xc457,0x2b7,0xd04,0x4177,0x143,0x2e7,0x810,0x40a7,0x63,0xe7,0x880,0x217,0x20,0x157,0x14b,0xc27,0xba7,0x8a7,0x132,0xaa7,0xc4f6,0x53,0x447,0x1467,0x45,0x77,0x82f7,0xd37,0xb37,0x4b77,0x4437,0x200,0x957,0x47,0x4245,0x477,0x11a7,0x804,0xc807,0x457,0xaf,0x541,0x197,0x2a7,0x81d7,0x823,0x373,0x267,0x8417,0x820,0x41a7,0x416,0x220,0xae7,0x142,0x8b7,0x5c7,0x437,0x84f7,0x44,0x8097,0xd3,0x42a7,0x1b7,0x2197,0x42,0xd1,0x8c7,0xe67,0xce13,0x52f,0xa7,0xa5f,0x8117,0x443,0x8dd7,0xe17,0x67f,0x20b7,0x867,0x2c5,0xa1,0x5f,0xe87,0x81b7,0x2d7,0x2a1,0xc2a7,0x105,0x485,0x4467,0x1f7,0x8877,0x986,0x6b,0x84,0x300,0x55,0x1bf,0x557,0x401,0x4337,0x3a7,0xbf7,0x46f,0x8057,0x4cf,0x4c5,0x685,0x87,0x8237,0x6c7,0x297,0x2f7,0x2ff,0x8317,0xc9f7,0x440,0xc117,0x400,0x1ac7,0xc1f7,0x826,0x3b7,0x280,0x85,0x41b7,0x40,0x4bef,0x42b7,0x391,0xa6f,0x1f3,0x4306,0x913,0x201,0x226,0x445,0xaf7,0x923,0x404,0x122,0x42ef,0xe97,0x57f,0x21af,0x1047,0xa0,0x4c1,0x922,0x22f,0x13,0x4f7,0x8977,0x42e7,0x937,0x936,0x24,0xc004,0x4127,0x8b37,0x6bf,0x7f,0x123,0x8000,0x5d7,0x3bf,0x7d7,0x4d27,0x43e7,0x877]
def pages : Array Nat := #[0x884004020103c1c0a0683016040100814090100804040401c0c04028100602010080200,0x1208c44090100842200107c0e1e010083a020a870361a0c80830170105804150a04c2402,0x1c01004371b0d46807198c8620201010602f010b85a02000b0562a148600828138984a09,0x491c8c0a228000844218d88441200087e041f0f4040202008043c1d8082a3a1c8080402,0x1008a80e01008a65228808a0020113c121627134040201130444b021280e00010089248,0x30144be040a808bc5d2e16c82022d02c0402011645c31290100e582b888ac55028081802,0x11a80469340082a6702198040232808046431808042d011888661010244e18138080402,0x3b1d4e8023980884720214804020a1c40470378083a6e36808046c0a8840427358c00402,0x5140fe7e01008087d3e008040701008f66d24008e82d3d0080802111e40878010081277,0x1024a40245a291288438c004860121404840201106020219d04744089c0004400080402,0x1008ce0216a44129105240a08f472340e2933854fc4301008120203808040246010ec3f,0x500886994c2104e090125c8602048252c7401008041f0100804024aa3d2802498080892,0x5088404a0350093e32010093c3101024049d0108c0402010083a0201270ba154d8093436,0x54aa00402020080409539ec04a601295482301008040203808449c51899260204a880402,0x5a2c0eb4011496604010096427492c5608a022bc04ae010115a155609c1202192ad5493,0x5f0597abc35808046b5d80862ba0d8c172b85b809229c090242a04010516cb5048081231,0x100804c601008000262b1042c30101c088a61008306a04b0404c00100804bf049801202,0x678259ccd0133004020201d9631650086cc9011bd900256808120a0d8258e09010086002,0x10083c736b35404d4010090a0201008040269809a40201344084301009a00c010081402,0x18388126070811c0020100808df010d860026f37446026e36db4666c809b0d7180080402,0x2822804020109c04e801008a40266b9c04e60101c046b023940052721f8600201009c602,0x1008040f013c0040262bbddced14809d8eb5d0080402020c40409113a808300105404e9,0x7987c0402790302a7401008ce025280812150480804f10c00804024f8080402010080402,0x10600407010240402010080402583dd24020200012027b00804020603dea020203004f4,0x100804020b0c004db7f80014021696804020100854fe0ebf5f8041f809f6fa4881df2f8,0x38094e15010600503629d004370b008fc028100a02093c8084e09802495ab1050080402,0x10080e1286008040913c2c6e0201429fb09110080508010c20e020102a0d05820080487,0x100a2a8a0106005148080a26028900804600f2b6220288174c002878321c0486b6c126b,0x1474ce0204c702c30010263655300243d1a8c88c04430500a311701008240248c582450,0xbc9649130480a460233b200e029101e4202900084c0901008011f8f008a402010280402,0x30132b3981c040201026540241b200e0d010081283948da500293c9812040a8084e6b,0x130049125e020b00a5cb51180a5a0a29026580201008046a010086ca1048094209]
def bucket (i : Nat) : Nat := masks.getD (((pages.getD (i/32) 0) >>> (9*(i % 32))) &&& 511) 0
def old (w : W) := (w.toNat % 2^232) + (((w.toNat >>> 689) % 2^232) <<< 232)
def code (ws : List W) := ws.foldl (fun a w=>a+(old w) % 65521) 0
def advice (ws hist : List W) : List Minor :=
  let m := bucket ((code ws+37*code hist) % 1021)
  ((List.finRange 23).filter (fun i=>m.testBit i.val)).map faceAt
theorem advice_ok (ws hist : List W) : ∀ c∈advice ws hist,c.Valid base := by
  rintro c hc;obtain ⟨i,_,rfl⟩ := List.mem_map.mp hc;exact valid i
def rootPair (i : Nat) : Bool := match (pairs base)[i]? with
  | none => false
  | some (a,b,r) => dispatch 4 (UnifiedSearch.checkChild base advice (UnifiedSearch.guided base advice 9) 9 base []) a b r
end UnifiedC4

namespace UnifiedC4
open P2828Check P2828Live P2828Generic P2828Truth P2828Minor ThetaSigned SignedCofactor
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem check0 : rootPair 0=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem check1 : rootPair 1=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem check2 : rootPair 2=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem check3 : rootPair 3=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem check4 : rootPair 4=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem check5 : rootPair 5=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem check6 : rootPair 6=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem check7 : rootPair 7=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem check8 : rootPair 8=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem check9 : rootPair 9=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem check10 : rootPair 10=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem check11 : rootPair 11=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem check12 : rootPair 12=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem check13 : rootPair 13=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem check14 : rootPair 14=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem check15 : rootPair 15=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem check16 : rootPair 16=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem check17 : rootPair 17=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem check18 : rootPair 18=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem check19 : rootPair 19=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem check20 : rootPair 20=false := by decide +kernel
theorem allPairs (i : Fin 21) : rootPair i.val=false := by
  fin_cases i
  · exact check0
  · exact check1
  · exact check2
  · exact check3
  · exact check4
  · exact check5
  · exact check6
  · exact check7
  · exact check8
  · exact check9
  · exact check10
  · exact check11
  · exact check12
  · exact check13
  · exact check14
  · exact check15
  · exact check16
  · exact check17
  · exact check18
  · exact check19
  · exact check20
theorem noTen : UnifiedSearch.guided base advice 10 4 base [] = false := by
  have len : (pairs base).length=21 := by decide
  apply Bool.eq_false_iff.mpr
  intro hit
  simp only [UnifiedSearch.guided,Bool.or_eq_true] at hit
  rcases hit with short|next
  · exact (by decide +kernel : (base==[goal])≠true) short
  obtain ⟨q,hq,ok⟩ := List.any_eq_true.mp next
  obtain ⟨i,hi⟩ := List.get_of_mem hq
  have no := allPairs (Fin.cast len i)
  simp only [Fin.val_cast,rootPair,List.getElem?_eq_getElem i.isLt] at no
  rw [←hi] at ok
  exact Bool.noConfusion (no.symm.trans ok)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem signed_lower {k} (hr : Run C4Base.small k C4Base.nine) : 11≤k := by
  by_contra! tooSmall
  have hl := root hr
  have stride (t : Nat) (le : k≤t) : live basicOps goal t base.toFinset := by
    induction le with
    | refl => exact hl
    | step _ ih => exact Or.inl ih
  have start : P2828Minor.seen base []=base.toFinset := by simp [P2828Minor.seen]
  have yes := UnifiedSearch.guided_complete base advice advice_ok 10 base [] 4
    (by decide +kernel) (by decide +kernel) (start ▸ History.initial) (start ▸ Finset.Subset.refl _) (stride 10 (by omega))
  exact Bool.noConfusion (yes.symm.trans noTen)
end UnifiedC4

namespace P2828Raw
open P2828Check P2828Live
def data : Array Face := #[
⟨17,0,11,0x155540005540002aa801400015240005500014402000154800a000520000100080007fffffffffffffffff8000000007fffff800169c547e9391f250d6d9434a5a000000050d0444254a5b5d622871544000000000200aaaa0202aa000375400a0681b960102ab341b3010280aa4105cd06d50031a84748840a40a40a40a40a40a40a40a40a40a40a40a4b4e2a3f49c8f9286b6ca1a52d002aa74286822212a52daeb11438aa2223383e3,0⟩,
⟨66,0,11,0x6669998d4c0000000000001994d0500000000000665311900000014887ff8007ffffffff8007fffffffffff800000018002b5f00ade000002eec0b63f0e05ebbb202eeb00b608c00000000a8802b68000000000000003334cee6b78000000000000cca6cae80000000003329aaee000000a77dc01c01c01c01c01c01c01c01c01c01c01c000c0015af8056f5dd80177605b1f8702f5dd901775805b046f830007f544015b4,2⟩,
⟨132,0,11,0xf1c38e1e30c878c32310000000000000000007451a0c04ffffff8007ff8007fffffffffff8000007ff8035cdef8000000671f819c0016901dfa0670919800000000100d73121c0d5ede02068a020000000003340000078f9c70f1a673f79b59828e884000cdde54003ba8d778a402c02c02c02c02c02c02c02c02c02c02c02c01ae6f7c343d80338fc0ce000b480efd033848cc06000fff0806b9890e06af6f, 0⟩,
⟨24,0,11,0x3fc00003e000007c001000007e0000380000e0000000f800600007804003000040fffffffff8007ffffffff8000000007fffff8c0c3c1c31b07671f249c7c60ed800000000000007460e04371a30f4e442301c2000021fe00481f000443e020800063fa0ad9c00067a6000027c0a30000bc0a005d28075d4114114114114114114114114114114114106061e0e18d83b38f924e3e3076f9118338f826233a307021b8d187a7221180e1,0⟩,
⟨160,0,11,0x1fffff800001ff000000000000000000000ff803f8007ff8007ff8007ff8007ffffffffffffff8003fc038000000ff0380000000300f3e0ff03c3e0c000c3ef000ff3e3c00c03e0000014020601600000282208100469fffffc0804cff80000514e30000284a0857fc27fcc10c10c10c10c10c10c10c10c10c10c10c10001fe01f8380707f81c1fe000fd8079f07f81e1f0600061f78007f9f1e00601f, 0⟩]
def faceAt (i : Fin 5) := data[i.val]
end P2828Raw

namespace P2828Raw
open P2828 P2828Check ThetaSigned SignedCofactor
theorem pull {X Z : Type} {P : Set (Wire X)} {k f} (hr : Run P k f) (phi : Z → X) :
    ∀ Q : Set (Wire Z), (∀ g ∈ P, (fun z => g (phi z)) ∈ Q) → Run Q k (fun z => f (phi z)) := by
  induction hr with
  | done h => exact fun Q hh => .done (hh _ h)
  | @gate P k f a b op ha hb hr ih =>
    intro Q hh
    apply Run.gate op (hh _ ha) (hh _ hb)
    apply ih
    intro g hg
    rcases hg with h|rfl|rfl
    · exact Or.inl (hh _ h)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
def insertVars {n : Nat} (idx : Fin 9 → Option (Fin n)) (x : Fin n → Bool) (v : Fin 9) :=
  match idx v with
  | none => false
  | some i => x i
theorem pullSmall {n : Nat} (idx : Fin 9 → Option (Fin n)) (f : Wire P2828.Y) (h : f ∈ P2828.small) :
    (fun x => f (insertVars idx x)) ∈ literals n := by
  rcases h with ⟨b,rfl⟩|⟨i,rfl|rfl⟩
  · exact Or.inl ⟨b,rfl⟩
  · cases e : idx i with
    | none => exact Or.inl ⟨false,funext fun x => by simp [insertVars,e,ThetaSigned.bit]⟩
    | some j => exact Or.inr ⟨j,Or.inl (funext fun x => by simp [insertVars,e])⟩
  · cases e : idx i with
    | none => exact Or.inl ⟨true,funext fun x => by simp [insertVars,e,inv,ThetaSigned.bit]⟩
    | some j => exact Or.inr ⟨j,Or.inr (funext fun x => by simp [insertVars,e,inv])⟩
def Lower4 := ∀ k, Run C4Base.small k C4Base.nine → 11 ≤ k
def selector0 : Fin 9 → Option (Fin 7) := ![none,some 0,some 5,some 3,none,some 4,some 1,some 2,some 6]
theorem good0 (lower : Lower4) : (faceAt 0).Valid := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  intro k h
  have run := pull h (insertVars selector0) (literals 7) (pullSmall selector0)
  have eq : ∀ x, nine (pin (faceAt 0).fixed (faceAt 0).values (insertVars selector0 x)) = C4Base.nine x := by decide +kernel
  rw [funext eq] at run
  exact lower k run
def selector1 : Fin 9 → Option (Fin 7) := ![some 0,none,some 4,some 6,some 1,some 5,none,some 2,some 3]
theorem good1 (lower : Lower4) : (faceAt 1).Valid := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  intro k h
  have run := pull h (insertVars selector1) (literals 7) (pullSmall selector1)
  have eq : ∀ x, nine (pin (faceAt 1).fixed (faceAt 1).values (insertVars selector1 x)) = C4Base.nine x := by decide +kernel
  rw [funext eq] at run
  exact lower k run
def selector2 : Fin 9 → Option (Fin 7) := ![some 5,some 0,none,some 4,some 2,some 3,some 1,none,some 6]
theorem good2 (lower : Lower4) : (faceAt 2).Valid := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  intro k h
  have run := pull h (insertVars selector2) (literals 7) (pullSmall selector2)
  have eq : ∀ x, nine (pin (faceAt 2).fixed (faceAt 2).values (insertVars selector2 x)) = C4Base.nine x := by decide +kernel
  rw [funext eq] at run
  exact lower k run
def selector3 : Fin 9 → Option (Fin 7) := ![some 3,some 5,some 0,none,none,some 6,some 2,some 1,some 4]
theorem good3 (lower : Lower4) : (faceAt 3).Valid := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  intro k h
  have run := pull h (insertVars selector3) (literals 7) (pullSmall selector3)
  have eq : ∀ x, nine (pin (faceAt 3).fixed (faceAt 3).values (insertVars selector3 x)) = C4Base.nine x := by decide +kernel
  rw [funext eq] at run
  exact lower k run
def selector4 : Fin 9 → Option (Fin 7) := ![some 0,some 5,some 3,some 6,some 1,none,some 2,none,some 4]
theorem good4 (lower : Lower4) : (faceAt 4).Valid := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  intro k h
  have run := pull h (insertVars selector4) (literals 7) (pullSmall selector4)
  have eq : ∀ x, nine (pin (faceAt 4).fixed (faceAt 4).values (insertVars selector4 x)) = C4Base.nine x := by decide +kernel
  rw [funext eq] at run
  exact lower k run
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem allValid (lower : Lower4) (i : Fin 5) : (faceAt i).Valid := by
  fin_cases i
  · exact good0 lower
  · exact good1 lower
  · exact good2 lower
  · exact good3 lower
  · exact good4 lower
end P2828Raw

namespace P2828Raw
open P2828Check P2828Live P2828Minor P2828 ThetaSigned
def mkMinor (f : Face) : Minor := ⟨f.lower,f.mask,f.anchor⟩
def allFaces (_ _ : List W) : List Minor := (List.finRange 5).map fun i=>mkMinor (faceAt i)
theorem facesGood (ws hist) : ∀c∈allFaces ws hist,c.Valid inputs := by
  intro c hc
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hc
  exact ofOrdinary _ (allValid (fun _ h => UnifiedC4.signed_lower h) i)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem rawScan : UnifiedSearch.guided inputs allFaces 13 5 inputs []=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem lower14 {k} (h : Run small k nine) : 14≤k := by
  by_contra! bad
  have pad (t : Nat) (le : k≤t) : live basicOps goal t inputs.toFinset := by
    induction le with
    | refl => exact inputLive h
    | step _ ih => exact Or.inl ih
  have start : P2828Minor.seen inputs []=inputs.toFinset := by simp [P2828Minor.seen]
  have result := UnifiedSearch.guided_complete inputs allFaces facesGood 13 inputs [] 5 (by decide +kernel) (by decide)
    (start ▸ History.initial) (start ▸ Finset.Subset.refl _) (pad 13 (by omega))
  exact Bool.noConfusion (result.symm.trans rawScan)
end P2828Raw

namespace SignedCircuitAux
open PEqualNP.CircuitLowerBounds
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp
theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]
def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2
theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp
end SignedCircuitAux
namespace ThetaSigned
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity SignedCircuitAux
def isBinary (g : Gate) : Bool := match g.op with | .not => false | _ => true
def budget (gs : List Gate) := gs.countP isBinary
def readW {X : Type} (w : X → List Bool) (i : ℕ) : Wire X := fun x => (w x).getD i false
def observe {X : Type} (w : X → List Bool) (g : Gate) : Wire X :=
  fun x => g.op.eval (g.inputs.map fun i => (w x).getD i false)
def emits {X : Type} (w : X → List Bool) (g : Gate) (x : X) := w x ++ [observe w g x]
theorem decode {X : Type} (w : X → List Bool) (g : Gate) (ok : Ok g) (P : Set (Wire X))
    (cp : Closed P) (hw : ∀ i, readW w i ∈ P) :
    (isBinary g = false ∧ observe w g ∈ P) ∨
    (isBinary g = true ∧ ∃ a ∈ P, ∃ b ∈ P, ∃ op, observe w g = bin op a b) := by
  rcases g with ⟨op,inputs⟩
  obtain ⟨allowed,short⟩ := ok
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at allowed
  change op = _ ∨ op = _ ∨ op = _ at allowed
  rcases allowed with rfl|rfl|rfl
  · refine Or.inr ⟨rfl,?_⟩
    rcases inputs with _|⟨a,_|⟨b,_|⟨d,tl⟩⟩⟩
    · exact ⟨_,cp.1 true,_,cp.1 true,false,rfl⟩
    · refine ⟨_,hw a,_,cp.1 true,false,?_⟩
      funext x; simp [bin,readW,observe,bit,GateOp.eval]
    · refine ⟨_,hw a,_,hw b,false,?_⟩
      funext x; simp [bin,readW,observe,bit,GateOp.eval]
    · change (a::b::d::tl).length ≤ 2 at short; simp at short
  · refine Or.inr ⟨rfl,?_⟩
    rcases inputs with _|⟨a,_|⟨b,_|⟨d,tl⟩⟩⟩
    · exact ⟨_,cp.1 false,_,cp.1 false,true,rfl⟩
    · refine ⟨_,hw a,_,cp.1 false,true,?_⟩
      funext x; simp [bin,readW,observe,bit,GateOp.eval]
    · refine ⟨_,hw a,_,hw b,true,?_⟩
      funext x; simp [bin,readW,observe,bit,GateOp.eval]
    · change (a::b::d::tl).length ≤ 2 at short; simp at short
  · refine Or.inl ⟨rfl,?_⟩
    cases inputs with
    | nil => exact cp.1 true
    | cons a tl => exact cp.2 _ (hw a)
theorem reads_after {X : Type} (w : X → List Bool) (g : Gate) (m : ℕ)
    (wm : ∀ x, (w x).length=m) (P : Set (Wire X)) (old : ∀ i, readW w i ∈ P)
    (fresh : observe w g ∈ P) : ∀ i, readW (emits w g) i ∈ P := by
  intro i
  by_cases e : i=m
  · have eq : readW (emits w g) i = observe w g := by
      funext x
      change (w x ++ [_]).getD i false = _
      rw [e,← wm x,getD_snoc_eq]
    exact eq ▸ fresh
  · have eq : readW (emits w g) i = readW w i := by
      funext x
      change (w x ++ [_]).getD i false = _
      exact getD_snoc_ne _ _ _ _ (by rw [wm x];exact e)
    exact eq ▸ old i
theorem compile {X : Type} (gs : List Gate) (out : ℕ) (ok : ∀ g ∈ gs, Ok g) :
    ∀ (w : X → List Bool) (m : ℕ), (∀ x, (w x).length=m) → ∀ P : Set (Wire X),
      Closed P → (∀ i, readW w i ∈ P) →
      Run P (budget gs) (fun x => (wiresFrom gs (w x)).getD out false) := by
  induction gs with
  | nil => intro w m wm P cp hw; exact .done (hw out)
  | cons g gs ih =>
    intro w m wm P cp hw
    have next := ih (fun g' hg => ok g' (List.mem_cons_of_mem _ hg)) (emits w g) (m+1)
      (fun x => by simp [emits,wm])
    obtain one|two := decode w g (ok g (List.mem_cons_self ..)) P cp hw
    · rcases one with ⟨hn,v⟩
      simp only [budget,List.countP_cons,hn,Bool.false_eq_true,ite_false,Nat.add_zero]
      exact next P cp (reads_after w g m wm P hw v)
    · rcases two with ⟨hn,a,ha,b,hb,op,v⟩
      simp only [budget,List.countP_cons,hn,ite_true]
      apply Run.gate op ha hb
      exact next _ (plus_closed cp _) (reads_after w g m wm _ (fun i => Or.inl (hw i)) (Or.inr (Or.inl v)))
end ThetaSigned

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open ThetaSigned P2828 SignedCircuitAux

def firstOr : Wire P2828.Y := ThetaSigned.bin true (fun x => x 0) (fun x => x 6)

def signedInputs (t : Fin 9) (x : P2828.Y) : List Bool :=
  (List.ofFn x ++ [firstOr x]).set t.val (!x t)

theorem signedInputs_length (t : Fin 9) (x : P2828.Y) : (signedInputs t x).length = 10 := by
  simp [signedInputs]

theorem signedInputs_read (t : Fin 9) (i : Nat) : readW (signedInputs t) i ∈ plus small firstOr := by
  by_cases hij : i = t.val
  · subst i
    refine Or.inl (Or.inr ⟨t, Or.inr ?_⟩)
    funext x
    change (signedInputs t x).getD t.val false = !x t
    rw [List.getD_eq_getElem?_getD]
    unfold signedInputs
    rw [List.getElem?_set_self (by simpa using Nat.lt_trans t.isLt (by decide : 9 < 10))]
    rfl
  · by_cases hi : i < 9
    · refine Or.inl (Or.inr ⟨⟨i, hi⟩, Or.inl ?_⟩)
      funext x
      change (signedInputs t x).getD i false = x ⟨i, hi⟩
      rw [List.getD_eq_getElem?_getD]
      unfold signedInputs
      rw [List.getElem?_set_ne (Ne.symm hij), List.getElem?_append_left (by simp [hi])]
      rw [List.getElem?_ofFn, dif_pos hi]
      rfl
    · by_cases last : i = 9
      · subst i
        refine Or.inr (Or.inl ?_)
        funext x
        change (signedInputs t x).getD 9 false = firstOr x
        rw [List.getD_eq_getElem?_getD]
        unfold signedInputs
        rw [List.getElem?_set_ne (Ne.symm hij), List.getElem?_append_right (by simp)]
        simp
      · refine Or.inl (Or.inl ⟨false, ?_⟩)
        funext x
        change (signedInputs t x).getD i false = false
        rw [List.getD_eq_default _ _ (by rw [signedInputs_length]; omega)]

theorem suffix_with_not_cannot_compute (t : Fin 9) (D : Circuit) (fan : FanInTwo D)
    (limit : D.size ≤ 13) (hasNot : ∃ g ∈ D.gates, g.op = .not)
    (correct : ∀ x : P2828.Y, D.eval (signedInputs t x) = nine x) : False := by
  have basic (i : Fin 9) : (fun x : P2828.Y => x i) ∈ small := .inr ⟨i, .inl rfl⟩
  have run := ThetaSigned.compile D.gates D.output fan (signedInputs t) 10
    (signedInputs_length t) (plus small firstOr) (plus_closed small_closed firstOr) (signedInputs_read t)
  have whole := Run.gate true (basic 0) (basic 6) run
  have lower := P2828Raw.lower14 ((funext correct) ▸ whole)
  obtain ⟨g, hg, ng⟩ := hasNot
  obtain ⟨pre, post, form⟩ := List.append_of_mem hg
  have front := List.countP_le_length (p := isBinary) (l := pre)
  have rear := List.countP_le_length (p := isBinary) (l := post)
  change D.gates.length ≤ 13 at limit
  change 14 ≤ D.gates.countP isBinary + 1 at lower
  have skipped : isBinary g = false := by simp [isBinary, ng]
  rw [form] at lower limit
  simp only [List.countP_append, List.countP_cons, skipped, Bool.false_eq_true, ite_false, Nat.add_zero] at lower
  simp only [List.length_append, List.length_cons] at limit
  omega


namespace ZeroNot

open PEqualNP.CircuitLowerBounds

def target (x : Fin 9 → Bool) : Bool :=
  ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any
    fun k => x (Fin.ofNat 9 (k / 10)) && x (Fin.ofNat 9 (k % 10))

def sample (t : Fin 9) (x : Fin 9 → Bool) : List Bool :=
  (List.ofFn x ++ [x 0 || x 6]).set t.val (!x t)

def neighbor (t : Fin 9) : Fin 9 := (![1, 0, 1, 2, 3, 0, 1, 2, 3] : Fin 9 → Fin 9) t

def low (t : Fin 9) (i : Fin 9) : Bool := decide (i = neighbor t)

def high (t : Fin 9) (i : Fin 9) : Bool := decide (i = neighbor t ∨ i = t)

theorem target_test : ∀ t : Fin 9, target (low t) = false ∧ target (high t) = true := by
  decide +kernel

theorem sample_order : ∀ (t : Fin 9), t ≠ 0 → t ≠ 6 →
    ∀ (k : Fin 10), (sample t (high t)).getD k.val false = true →
      (sample t (low t)).getD k.val false = true := by
  decide +kernel

theorem sample_length (t : Fin 9) (x : Fin 9 → Bool) : (sample t x).length = 10 := by
  simp [sample]

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem append_bit (W : List Bool) (v : Bool) (i : ℕ) :
    (W ++ [v]).getD i false = if i = W.length then v else W.getD i false := by
  rcases lt_trichotomy i W.length with h | h | h
  · rw [ite_eq_right (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · rw [ite_eq_right (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem circuit_order (gs : List Gate) (W1 W2 : List Bool)
    (lengthEq : W1.length = W2.length)
    (legal : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (inp : ∀ i, W1.getD i false = true → W2.getD i false = true) :
    ∀ i, (gs.foldl step W1).getD i false = true → (gs.foldl step W2).getD i false = true := by
  induction gs generalizing W1 W2 with
  | nil => exact inp
  | cons g gs ih =>
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (step W1 g) (step W2 g) (by simp [step, lengthEq])
      (fun h hh => legal h (List.mem_cons_of_mem _ hh))
    intro i
    simp only [step, append_bit, lengthEq]
    split_ifs
    · rcases legal g List.mem_cons_self with kind | kind
      · simp only [kind, GateOp.eval, List.all_eq_true, List.mem_map]
        intro yes b hb
        obtain ⟨w, hw, rfl⟩ := hb
        exact inp w (yes _ ⟨w, hw, rfl⟩)
      · simp only [kind, GateOp.eval, List.any_eq_true, List.mem_map]
        rintro ⟨_, ⟨w, hw, rfl⟩, yes⟩
        exact ⟨_, ⟨w, hw, rfl⟩, inp w yes⟩
    · exact inp i

theorem excludes (t : Fin 9) (C : Circuit) (not0 : t ≠ 0) (not6 : t ≠ 6)
    (legal : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or) :
    ∃ x : Fin 9 → Bool, C.eval (sample t x) ≠ target x := by
  by_contra! exactness
  have inp (i : ℕ) (yes : (sample t (high t)).getD i false = true) :
      (sample t (low t)).getD i false = true := by
    by_cases hi : i < 10
    · exact sample_order t not0 not6 ⟨i, hi⟩ yes
    · rw [List.getD_eq_default _ _ (by rw [sample_length]; omega)] at yes
      exact Bool.noConfusion yes
  have lhs : C.eval (sample t (high t)) = true := (exactness _).trans (target_test t).2
  have rhs : C.eval (sample t (low t)) = false := (exactness _).trans (target_test t).1
  have preserves : C.eval (sample t (low t)) = true :=
    circuit_order C.gates _ _ (by rw [sample_length, sample_length]) legal inp C.output lhs
  cases rhs.symm.trans preserves

end ZeroNot

set_option maxHeartbeats 0 in
theorem target_agrees : ∀ x : Fin 9 → Bool, ZeroNot.target x = P2828.nine x := by
  decide +kernel

end PEqualNP.Outside.L_meta_3612_aux

open PEqualNP.Outside.L_meta_3612_aux

theorem PEqualNP.Outside.L_meta_3612 :
  have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); have x2 : (Fin (9 : ℕ) → Bool) → List Bool := fun (x2 : Fin (9 : ℕ) → Bool) => List.ofFn x2 ++ [x2 (0 : Fin (9 : ℕ)) || x2 (6 : Fin (9 : ℕ))]; ∀ (x3 : Fin (9 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), x3 ≠ (0 : Fin (9 : ℕ)) → x3 ≠ (6 : Fin (9 : ℕ)) → PEqualNP.MetaComplexity.FanInTwo x4 → x4.size ≤ (13 : ℕ) → ∃ (x9 : Fin (9 : ℕ) → Bool), x4.eval ((x2 x9).set ↑x3 !x9 x3) ≠ x1 x9 := by
  intro recordedTarget recordedInputs t C no0 no6 fan limit
  change ∃ x : Fin 9 → Bool, C.eval (ZeroNot.sample t x) ≠ ZeroNot.target x
  by_cases hasNot : ∃ g ∈ C.gates, g.op = .not
  · by_contra! correct
    apply suffix_with_not_cannot_compute t C fan limit hasNot
    intro x
    exact (correct x).trans (target_agrees x)
  · have legal : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or := by
      intro g hg
      have basis := (fan g hg).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at basis
      rcases basis with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact False.elim (hasNot ⟨g, hg, h⟩)
    exact ZeroNot.excludes t C no0 no6 legal
