import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_14764

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def zeroGate (k : Fin 4) (a b : Bool) : Bool :=
  match k.val with
  | 0 => a && b
  | 1 => a || b
  | 2 => a && !b
  | _ => !a && b

section Generic
variable {α : Type} {β : Type}

def UC (G : Fin 4 → α → α → α) (A : Fin 4 → Prop) : ℕ → (α → Prop) → α → Prop
  | 0, S, f => S f
  | t + 1, S, f => UC G A t S f ∨
      ∃ k a b, A k ∧ S a ∧ S b ∧ UC G A t (fun w => w = G k a b ∨ S w) f

theorem UC_le {G : Fin 4 → α → α → α} {A : Fin 4 → Prop} {t t' : ℕ} {S : α → Prop} {f : α}
    (h : t ≤ t') (hu : UC G A t S f) : UC G A t' S f := by
  induction h with
  | refl => exact hu
  | step _ ih => exact Or.inl ih

theorem UC_gate {G : Fin 4 → α → α → α} {A : Fin 4 → Prop} {t : ℕ} {S : α → Prop} {f : α}
    (k : Fin 4) (a b : α) (hk : A k) (ha : S a) (hb : S b)
    (hu : UC G A t (fun w => w = G k a b ∨ S w) f) : UC G A (t + 1) S f :=
  Or.inr ⟨k, a, b, hk, ha, hb, hu⟩

def TR (G : Fin 4 → α → α → α) (C : Fin 4 → α → α → Prop) (ys : List α) (t : ℕ)
    (ws : List α) : Prop :=
  ∀ P : ℕ → List α → Prop, P 0 ys →
    (∀ s xs zs, List.Perm xs zs → P s xs → P s zs) →
    (∀ s a b r (k : Fin 4) (u : ℕ), C k a b →
      P s (List.replicate (u + 1) (G k a b) ++ r) → P (s + 1) (a :: b :: r)) →
    P t ws

section Run
variable {G : Fin 4 → α → α → α} {C : Fin 4 → α → α → Prop} {ys : List α}

theorem TR.done : TR G C ys 0 ys := fun _ d _ _ => d

theorem TR.perm {s : ℕ} {xs zs : List α} (p : List.Perm xs zs) (h : TR G C ys s xs) :
    TR G C ys s zs := fun P d q st => q s xs zs p (h P d q st)

theorem TR.step {s : ℕ} {a b : α} {r : List α} (k : Fin 4) (u : ℕ) (hc : C k a b)
    (h : TR G C ys s (List.replicate (u + 1) (G k a b) ++ r)) :
    TR G C ys (s + 1) (a :: b :: r) := fun P d q st => st s a b r k u hc (h P d q st)

theorem TR.ind {P : ℕ → List α → Prop} {t : ℕ} {ws : List α} (h : TR G C ys t ws)
    (d : P 0 ys)
    (p : ∀ s xs zs, List.Perm xs zs → TR G C ys s xs → P s xs → P s zs)
    (st : ∀ s a b r (k : Fin 4) (u : ℕ), C k a b →
      TR G C ys s (List.replicate (u + 1) (G k a b) ++ r) →
      P s (List.replicate (u + 1) (G k a b) ++ r) → P (s + 1) (a :: b :: r)) : P t ws :=
  (h (fun s xs => TR G C ys s xs ∧ P s xs) ⟨TR.done, d⟩
    (fun s xs zs hp hx => ⟨TR.perm hp hx.1, p s xs zs hp hx.1 hx.2⟩)
    (fun s a b r k u hc hx => ⟨TR.step k u hc hx.1, st s a b r k u hc hx.1 hx.2⟩)).2

theorem TR.monoC {C' : Fin 4 → α → α → Prop} (hC : ∀ k a b, C k a b → C' k a b) {t : ℕ}
    {ws : List α} (h : TR G C ys t ws) : TR G C' ys t ws :=
  TR.ind (P := fun t ws => TR G C' ys t ws) h TR.done (fun _ _ _ hp _ ih => TR.perm hp ih)
    (fun _ _ _ _ k u hc _ ih => TR.step k u (hC _ _ _ hc) ih)

end Run

def strictC (G : Fin 4 → α → α → α) (z : α) (A : Fin 4 → Prop) (I : α → Prop) :
    Fin 4 → α → α → Prop :=
  fun k a b => A k ∧ I a ∧ I b ∧ a ≠ b ∧ G k a b ≠ a ∧ G k a b ≠ b ∧ G k a b ≠ z

theorem normalize [DecidableEq α] (G : Fin 4 → α → α → α) (z : α) (A : Fin 4 → Prop)
    (I : α → Prop) (hI : ∀ k a b, I a → I b → I (G k a b))
    (hz1 : ∀ k b, G k z b = z ∨ G k z b = b) (hz2 : ∀ k a, G k a z = z ∨ G k a z = a)
    (hd : ∀ k a, G k a a = z ∨ G k a a = a) :
    ∀ (t : ℕ) (S : α → Prop) (f : α), (∀ w, S w → I w) → f ≠ z → UC G A t S f →
      ∃ t', t' ≤ t ∧ ∃ ws : List α, (∀ w ∈ ws, S w ∧ w ≠ z) ∧
        TR G (strictC G z A I) [f] t' ws
  | 0, S, f, _, hf, hu => ⟨0, le_rfl, [f], by simpa using ⟨hu, hf⟩, TR.done⟩
  | t + 1, S, f, hS, hf, hu => by
    rcases hu with hu | ⟨k, a, b, hk, ha, hb, hu⟩
    · obtain ⟨t', ht, ws, hws, hr⟩ := normalize G z A I hI hz1 hz2 hd t S f hS hf hu
      exact ⟨t', by omega, ws, hws, hr⟩
    · obtain ⟨t', ht, ws, hws, hr⟩ := normalize G z A I hI hz1 hz2 hd t _ f (by
        rintro w (rfl | hw)
        · exact hI k a b (hS a ha) (hS b hb)
        · exact hS w hw) hf hu
      by_cases hg : S (G k a b)
      · refine ⟨t', by omega, ws, fun w hw => ⟨?_, (hws w hw).2⟩, hr⟩
        rcases (hws w hw).1 with rfl | h
        · exact hg
        · exact h
      by_cases hc : G k a b ∈ ws
      · have hgz : G k a b ≠ z := (hws _ hc).2
        have hga : G k a b ≠ a := fun h => hg (by rw [h]; exact ha)
        have hgb : G k a b ≠ b := fun h => hg (by rw [h]; exact hb)
        have hab : a ≠ b := by
          rintro rfl
          rcases hd k a with h | h
          · exact hgz h
          · exact hga h
        have haz : a ≠ z := by
          rintro rfl
          rcases hz1 k b with h | h
          · exact hgz h
          · exact hgb h
        have hbz : b ≠ z := by
          rintro rfl
          rcases hz2 k a with h | h
          · exact hgz h
          · exact hga h
        obtain ⟨u, hu1⟩ : ∃ u, List.count (G k a b) ws = u + 1 :=
          ⟨List.count (G k a b) ws - 1, by have := List.count_pos_iff.2 hc; omega⟩
        have hperm : ws.Perm (List.replicate (u + 1) (G k a b) ++ ws.filter (· ≠ G k a b)) := by
          rw [← hu1, ← List.filter_eq]
          have := List.filter_append_perm (fun x => decide (x = G k a b)) ws
          refine this.symm.trans ?_
          simp
        refine ⟨t' + 1, by omega, a :: b :: ws.filter (· ≠ G k a b), ?_,
          TR.step k u ⟨hk, hS a ha, hS b hb, hab, hga, hgb, hgz⟩ (TR.perm hperm hr)⟩
        intro w hw
        simp only [List.mem_cons, List.mem_filter, decide_eq_true_eq] at hw
        rcases hw with rfl | rfl | ⟨hw, hne⟩
        · exact ⟨ha, haz⟩
        · exact ⟨hb, hbz⟩
        · rcases (hws w hw).1 with h | h
          · exact absurd h hne
          · exact ⟨h, (hws w hw).2⟩
      · refine ⟨t', by omega, ws, fun w hw => ⟨?_, (hws w hw).2⟩, hr⟩
        rcases (hws w hw).1 with rfl | h
        · exact absurd hw hc
        · exact h

end Generic

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

abbrev W := BitVec 128

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 64 := ((x >>> 64) ^^^ x).setWidth 64
def cuts (ws : List W) : BitVec 64 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 64) ++ (0 : BitVec 64)

def opW (k : Fin 4) (a b : W) : W :=
  match k.val with
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => a &&& ~~~b
  | _ => b &&& ~~~a

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 64) (w : W) : Prop :=
  w.getLsbD (64 + i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 64) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha, hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 64 + i.val < 128 := by omega
  have hi' : i.val < 128 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 64) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j, hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 64)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

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

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) :
    ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ)
    (hn : ws.Nodup) (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hg hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n + 1) && (cuts ws == -1) && optimized n (n + 1 - ws.length) ws

theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s, hs, hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  exact List.any_eq_true.mpr ⟨ws, List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', optimized_complete hg n ws _ hnd (by omega : n + 1 - ws.length + ws.length = n + 1) hl']⟩

abbrev BF := (Fin 8 → Bool) → Bool

def gF (k : Fin 4) (a b : BF) : BF := fun x => zeroGate k (a x) (b x)
def var (i : Fin 8) : BF := fun x => x i
def zF : BF := fun _ => false
def rst (p : Fin 8) (a : BF) : BF := fun x => a (Function.update x p false)

theorem gF_zero_left (k : Fin 4) (b : BF) : gF k zF b = zF ∨ gF k zF b = b := by
  fin_cases k
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])

theorem gF_zero_right (k : Fin 4) (a : BF) : gF k a zF = zF ∨ gF k a zF = a := by
  fin_cases k
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])

theorem gF_self (k : Fin 4) (a : BF) : gF k a a = zF ∨ gF k a a = a := by
  fin_cases k
  · exact Or.inr (funext fun x => by simp [gF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])

theorem gF_zero_zero (k : Fin 4) : gF k zF zF = zF := by
  fin_cases k <;> exact funext fun x => by simp [gF, zF, zeroGate]

theorem rst_var_self (p : Fin 8) : rst p (var p) = zF :=
  funext fun x => by simp [rst, var, zF]

theorem rst_var_ne {i p : Fin 8} (h : i ≠ p) : rst p (var i) = var i :=
  funext fun x => by simp [rst, var, Function.update_of_ne h]

theorem TRF_det {C : Fin 4 → BF → BF → Prop} {ys : List BF} {s : ℕ} {ws : List BF}
    (h : TR gF C ys s ws) (x x' : Fin 8 → Bool) :
    (∀ w ∈ ws, w x = w x') → ∀ y ∈ ys, y x = y x' := by
  refine TR.ind (P := fun _ ws => (∀ w ∈ ws, w x = w x') → ∀ y ∈ ys, y x = y x') h
    (fun h => h) ?_ ?_
  · intro s xs zs hp _ ih hz
    exact ih fun t ht => hz t (hp.mem_iff.1 ht)
  · intro s a b r k u _ _ ih hz
    apply ih
    intro t ht
    rcases List.mem_append.1 ht with ht | ht
    · rw [List.eq_of_mem_replicate ht]
      show zeroGate k (a x) (b x) = zeroGate k (a x') (b x')
      rw [hz a (by simp), hz b (by simp)]
    · exact hz t (by simp [ht])

def dcount (p : Fin 8) (ws : List BF) : ℕ := ws.countP fun w => decide (rst p w = zF)

theorem dcount_cons (p : Fin 8) (a : BF) (l : List BF) :
    dcount p (a :: l) = dcount p l + if rst p a = zF then 1 else 0 := by
  simp [dcount, List.countP_cons]

theorem dcount_rep (p : Fin 8) (n : ℕ) (g : BF) (r : List BF) :
    dcount p (List.replicate n g ++ r) = (if rst p g = zF then n else 0) + dcount p r := by
  simp only [dcount, List.countP_append, List.countP_replicate]
  split_ifs <;> simp_all

theorem pot_dead {A : Fin 4 → Prop} (p : Fin 8) {F : BF} (hF : rst p F ≠ zF) {s : ℕ}
    {ws : List BF} (h : TR gF (fun k _ _ => A k) [F] s ws) :
    dcount p ws ≤ s ∧ ∀ S : BF → Prop, (∀ w ∈ ws, rst p w ≠ zF → S (rst p w)) →
      UC gF A (s - dcount p ws) S (rst p F) := by
  refine TR.ind (P := fun s ws => dcount p ws ≤ s ∧ ∀ S : BF → Prop,
    (∀ w ∈ ws, rst p w ≠ zF → S (rst p w)) → UC gF A (s - dcount p ws) S (rst p F)) h ?_ ?_ ?_
  · refine ⟨by simp [dcount, hF], fun S hS => ?_⟩
    have : dcount p [F] = 0 := by simp [dcount, hF]
    rw [this]
    exact hS F (by simp) hF
  · intro s xs zs hp _ ih
    have hc : dcount p zs = dcount p xs := (hp.countP_eq _).symm
    rw [hc]
    exact ⟨ih.1, fun S hS => ih.2 S fun w hw => hS w (hp.mem_iff.1 hw)⟩
  · intro s a b r k u hk _ ih
    obtain ⟨ih1, ih2⟩ := ih
    have hg : rst p (gF k a b) = gF k (rst p a) (rst p b) := rfl
    rw [dcount_rep] at ih1 ih2
    rw [dcount_cons, dcount_cons]
    have hmem : ∀ (S : BF → Prop), (∀ w ∈ a :: b :: r, rst p w ≠ zF → S (rst p w)) →
        ∀ w ∈ r, rst p w ≠ zF → S (rst p w) := fun S hS w hw => hS w (by simp [hw])
    by_cases ha : rst p a = zF <;> by_cases hb : rst p b = zF
    · have hgz : rst p (gF k a b) = zF := by rw [hg, ha, hb, gF_zero_zero]
      simp only [hgz, ha, hb, ite_true] at ih1 ih2 ⊢
      refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
      intro w hw hwz
      rcases List.mem_append.1 hw with hw | hw
      · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
      · exact hmem S hS w hw hwz
    · by_cases hgz : rst p (gF k a b) = zF
      · simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
        · exact hmem S hS w hw hwz
      · have hgb : rst p (gF k a b) = rst p b := by
          rcases gF_zero_left k (rst p b) with h | h
          · exact absurd (by rw [hg, ha, h]) hgz
          · rw [hg, ha, h]
        simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · rw [List.eq_of_mem_replicate hw, hgb]
          exact hS b (by simp) hb
        · exact hmem S hS w hw hwz
    · by_cases hgz : rst p (gF k a b) = zF
      · simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
        · exact hmem S hS w hw hwz
      · have hga : rst p (gF k a b) = rst p a := by
          rcases gF_zero_right k (rst p a) with h | h
          · exact absurd (by rw [hg, hb, h]) hgz
          · rw [hg, hb, h]
        simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · rw [List.eq_of_mem_replicate hw, hga]
          exact hS a (by simp) ha
        · exact hmem S hS w hw hwz
    · by_cases hgz : rst p (gF k a b) = zF
      · simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
        · exact hmem S hS w hw hwz
      · simp only [hgz, ha, hb, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => ?_⟩
        have h1 := ih2 (fun w => w = gF k (rst p a) (rst p b) ∨ S w) (by
          intro w hw hwz
          rcases List.mem_append.1 hw with hw | hw
          · exact Or.inl (by rw [List.eq_of_mem_replicate hw, hg])
          · exact Or.inr (hmem S hS w hw hwz))
        have h2 := UC_gate k (rst p a) (rst p b) hk (hS a (by simp) ha) (hS b (by simp) hb) h1
        exact UC_le (by omega) h2

def MonoA : Fin 4 → Prop := fun k => k.val < 2

theorem mono_cases (k : Fin 4) (hk : MonoA k) : k = 0 ∨ k = 1 := by
  fin_cases k <;> simp_all [MonoA]

theorem gF_and (a b : BF) : gF 0 a b = fun p => a p && b p := rfl
theorem gF_or (a b : BF) : gF 1 a b = fun p => a p || b p := rfl

def gv (g : Gate) (W : List BF) : BF :=
  fun x => g.op.eval (g.inputs.map fun i => (W.getD i zF) x)

def wiresF : List Gate → List BF → List BF
  | [], W => W
  | g :: gs, W => wiresF gs (W ++ [gv g W])

theorem getD_map_x (W : List BF) (i : ℕ) (x : Fin 8 → Bool) :
    (W.map fun w => w x).getD i false = (W.getD i zF) x := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases W[i]? <;> rfl

theorem wires_eq (x : Fin 8 → Bool) : ∀ (gs : List Gate) (W : List BF),
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (W.map fun w => w x) = (wiresF gs W).map fun w => w x
  | [], W => rfl
  | g :: gs, W => by
    simp only [List.foldl_cons, wiresF]
    rw [← wires_eq x gs (W ++ [gv g W])]
    congr 1
    simp only [List.map_append, List.map_cons, List.map_nil, gv, getD_map_x]

theorem getD_mem (W : List BF) (i : ℕ) : W.getD i zF ∈ W ∨ W.getD i zF = zF := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : W[i]? with _ | a
  · exact Or.inr rfl
  · exact Or.inl (List.mem_of_getElem? h)

theorem gate_form (g : Gate) (W : List BF)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hl : g.inputs.length ≤ 2) :
    gv g W = zF ∨ gv g W = (fun _ => true) ∨
    (∃ a, (a ∈ W ∨ a = zF) ∧ gv g W = a) ∨
    (∃ a, (a ∈ W ∨ a = zF) ∧ gv g W = fun x => !a x) ∨
    (∃ k a b, MonoA k ∧ (a ∈ W ∨ a = zF) ∧ (b ∈ W ∨ b = zF) ∧ gv g W = gF k a b) := by
  rcases g with ⟨op, ins⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨l, rest⟩⟩⟩
  · rcases hop with rfl | rfl | rfl
    · exact Or.inr (Or.inl (funext fun x => by simp [gv, GateOp.eval]))
    · exact Or.inl (funext fun x => by simp [gv, GateOp.eval, zF])
    · exact Or.inr (Or.inl (funext fun x => by simp [gv, GateOp.eval]))
  · rcases hop with rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inl ⟨W.getD i zF, getD_mem W i,
        funext fun x => by simp [gv, GateOp.eval]⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨W.getD i zF, getD_mem W i,
        funext fun x => by simp [gv, GateOp.eval]⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨W.getD i zF, getD_mem W i,
        funext fun x => by simp [gv, GateOp.eval]⟩)))
  · rcases hop with rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨0, W.getD i zF, W.getD j zF, by simp [MonoA],
        getD_mem W i, getD_mem W j, funext fun x => by simp [gv, GateOp.eval, gF_and]⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨1, W.getD i zF, W.getD j zF, by simp [MonoA],
        getD_mem W i, getD_mem W j, funext fun x => by simp [gv, GateOp.eval, gF_or]⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨W.getD i zF, getD_mem W i,
        funext fun x => by simp [gv, GateOp.eval]⟩)))
  · simp at hl

def ori (w : BF) : BF := fun x => xor (w x) (w fun _ => false)

theorem ori_zero : ori zF = zF := funext fun x => by simp [ori, zF]
theorem ori_true : ori (fun _ => true) = zF := funext fun x => by simp [ori, zF]

theorem ori_not (a : BF) : ori (fun x => !a x) = ori a :=
  funext fun x => by
    simp only [ori]
    cases a x <;> cases a (fun _ => false) <;> rfl

theorem ori_zp {w : BF} (h : w (fun _ => false) = false) : ori w = w :=
  funext fun x => by simp [ori, h]

theorem ori_gate (k : Fin 4) (hk : MonoA k) (a b : BF) :
    ∃ k', ori (gF k a b) = gF k' (ori a) (ori b) := by
  rcases mono_cases k hk with rfl | rfl
  · cases hu : a (fun _ => false) <;> cases hv : b (fun _ => false)
    · exact ⟨0, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨2, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨3, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨1, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
  · cases hu : a (fun _ => false) <;> cases hv : b (fun _ => false)
    · exact ⟨1, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨3, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨2, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨0, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩

abbrev GOK (gs : List Gate) : Prop :=
  ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem ori_key (g : Gate) (W : List BF) (S : BF → Prop)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hl : g.inputs.length ≤ 2) (hW : ∀ w ∈ W, ori w = zF ∨ S (ori w)) :
    (ori (gv g W) = zF ∨ S (ori (gv g W))) ∨
      ∃ k a b, S a ∧ S b ∧ ori (gv g W) = gF k a b := by
  have hWz : ∀ a, (a ∈ W ∨ a = zF) → ori a = zF ∨ S (ori a) := by
    rintro a (h | rfl)
    · exact hW a h
    · exact Or.inl ori_zero
  rcases gate_form g W hop hl with h | h | ⟨a, ha, h⟩ | ⟨a, ha, h⟩ | ⟨k, a, b, hk, ha, hb, h⟩
  · rw [h]; exact Or.inl (Or.inl ori_zero)
  · rw [h]; exact Or.inl (Or.inl ori_true)
  · rw [h]; exact Or.inl (hWz a ha)
  · rw [h, ori_not]; exact Or.inl (hWz a ha)
  · obtain ⟨k', hk'⟩ := ori_gate k hk a b
    rw [h, hk']
    rcases hWz a ha with ha1 | ha1
    · rw [ha1]
      rcases gF_zero_left k' (ori b) with e | e
      · rw [e]; exact Or.inl (Or.inl rfl)
      · rw [e]; exact Or.inl (hWz b hb)
    rcases hWz b hb with hb1 | hb1
    · rw [hb1]
      rcases gF_zero_right k' (ori a) with e | e
      · rw [e]; exact Or.inl (Or.inl rfl)
      · rw [e]; exact Or.inl (Or.inr ha1)
    exact Or.inr ⟨k', ori a, ori b, ha1, hb1, rfl⟩

def isNot : GateOp → Bool
  | .not => true
  | _ => false

theorem isNot_true (op : GateOp) : isNot op = true ↔ op = GateOp.not := by
  cases op <;> simp [isNot]

def countBinary : List Gate → ℕ
  | [] => 0
  | g :: gs => countBinary gs + if isNot g.op then 0 else 1

theorem countBinary_le (gs : List Gate) : countBinary gs ≤ gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [countBinary, List.length_cons]
    split <;> omega

theorem countBinary_lt (gs : List Gate) (h : ∃ g ∈ gs, g.op = GateOp.not) :
    countBinary gs < gs.length := by
  induction gs with
  | nil => simp at h
  | cons g gs ih =>
    obtain ⟨a, ha, he⟩ := h
    rcases List.mem_cons.1 ha with rfl | ha
    · have hb := countBinary_le gs
      simp [countBinary, he, isNot, Nat.lt_succ_of_le hb]
    · have hb := ih ⟨a, ha, he⟩
      simp only [countBinary, List.length_cons]
      split <;> omega

theorem not_key (g : Gate) (W : List BF) (S : BF → Prop) (hop : g.op = GateOp.not)
    (hW : ∀ w ∈ W, ori w = zF ∨ S (ori w)) :
    ori (gv g W) = zF ∨ S (ori (gv g W)) := by
  obtain ⟨op, ins⟩ := g
  change op = GateOp.not at hop
  subst op
  cases ins with
  | nil => exact Or.inl ori_true
  | cons i rest =>
    have he : gv ⟨GateOp.not, i :: rest⟩ W = fun x => !(W.getD i zF) x := rfl
    rw [he, ori_not]
    rcases getD_mem W i with h | h
    · exact hW _ h
    · rw [h]; exact Or.inl ori_zero

theorem trans_binary : ∀ (gs : List Gate) (W : List BF) (S : BF → Prop), GOK gs →
    (∀ w ∈ W, ori w = zF ∨ S (ori w)) → ∀ o : ℕ,
    ori ((wiresF gs W).getD o zF) = zF ∨
      UC gF (fun _ => True) (countBinary gs) S (ori ((wiresF gs W).getD o zF))
  | [], W, S, _, hw, o => by
    rcases getD_mem W o with h | h
    · exact hw _ h
    · rw [wiresF, h]; exact Or.inl ori_zero
  | g :: gs, W, S, hg, hw, o => by
    have hg1 := hg g (by simp)
    have hg2 : GOK gs := fun g' h => hg g' (by simp [h])
    have free (h : ori (gv g W) = zF ∨ S (ori (gv g W))) :=
      trans_binary gs (W ++ [gv g W]) S hg2 (by
        intro w hm
        rcases List.mem_append.1 hm with hm | hm
        · exact hw w hm
        · rw [List.mem_singleton.1 hm]; exact h) o
    simp only [wiresF, countBinary]
    by_cases hn : g.op = GateOp.not
    · simpa [hn, isNot] using free (not_key g W S hn hw)
    · rw [ite_eq_right (fun ht => hn ((isNot_true g.op).1 ht))]
      rcases ori_key g W S hg1.1 hg1.2 hw with h | ⟨k, a, b, ha, hb, h⟩
      · exact (free h).imp id (UC_le (Nat.le_succ _))
      · have next := trans_binary gs (W ++ [gv g W]) (fun w => w = gF k a b ∨ S w) hg2 (by
          intro w hm
          rcases List.mem_append.1 hm with hm | hm
          · exact (hw w hm).imp id Or.inr
          · rw [List.mem_singleton.1 hm]; exact Or.inr (Or.inl h)) o
        exact next.imp id (UC_gate k a b trivial ha hb)

def sourceVars (xs : Finset (Fin 8)) (f : BF) : Prop := ∃ i ∈ xs, f = var i

theorem remove_var (F : BF) (p : Fin 8) (xs : Finset (Fin 8)) (s : ℕ)
    (hd : ∃ x, rst p F x ≠ F x) (hn : rst p F ≠ zF)
    (h : UC gF (fun _ => True) s (sourceVars xs) F) :
    ∃ t, t + 1 ≤ s ∧ UC gF (fun _ => True) t (sourceVars (xs.erase p)) (rst p F) := by
  have hf : F ≠ zF := fun e => hn (by rw [e]; rfl)
  obtain ⟨k, hk, ws, hws, run⟩ := normalize gF zF (fun _ => True) (fun _ => True)
    (fun _ _ _ _ _ => trivial) gF_zero_left gF_zero_right gF_self
    s (sourceVars xs) F (fun _ _ => trivial) hf h
  have hp : var p ∈ ws := by
    by_contra hmiss
    obtain ⟨x, hx⟩ := hd
    apply hx
    exact TRF_det run (Function.update x p false) x (by
      intro w hw
      obtain ⟨i, _, rfl⟩ := (hws w hw).1
      have hi : i ≠ p := fun e => hmiss (e ▸ hw)
      exact Function.update_of_ne hi false x) F (by simp)
  have hc : 1 ≤ dcount p ws := by
    apply Nat.succ_le_of_lt
    unfold dcount
    exact List.countP_pos_iff.2 ⟨var p, hp, by simp [rst_var_self]⟩
  have dr := pot_dead p hn (TR.monoC (fun _ _ _ _ => trivial) run)
  refine ⟨k - dcount p ws, by omega, dr.2 (sourceVars (xs.erase p)) ?_⟩
  intro w hw hz
  obtain ⟨i, hi, rfl⟩ := (hws w hw).1
  have hne : i ≠ p := fun e => hz (e ▸ rst_var_self p)
  exact ⟨i, Finset.mem_erase.2 ⟨hne, hi⟩, rst_var_ne hne⟩

def enc (w : BF) : List (Fin 8 → Bool) → ℕ
  | [] => 0
  | p :: t => Nat.bit (w p) (enc w t)

theorem enc_testBit (w : BF) : ∀ (l : List (Fin 8 → Bool)) (j : ℕ),
    (enc w l).testBit j = (l.map w).getD j false
  | [], j => by simp [enc]
  | p :: t, 0 => by simp [enc]
  | p :: t, j + 1 => by simp [enc, Nat.testBit_bit_succ, enc_testBit w t j]

def evalW (pts : List (Fin 8 → Bool)) (f : BF) : W := BitVec.ofNat 128 (enc f pts)

theorem evalW_gF (pts : List (Fin 8 → Bool)) (hlen : pts.length = 128)
    (k : Fin 4) (a b : BF) :
    evalW pts (gF k a b) = opW k (evalW pts a) (evalW pts b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [evalW, opW]
  have bitA : (BitVec.ofNat 128 (enc a pts)).getLsbD j = a (pts[j]'(by omega)) := by
    rw [BitVec.getLsbD_ofNat, decide_eq_true hj, Bool.true_and, enc_testBit]
    simp [List.getD_eq_getElem?_getD, hlen, hj]
  have bitB : (BitVec.ofNat 128 (enc b pts)).getLsbD j = b (pts[j]'(by omega)) := by
    rw [BitVec.getLsbD_ofNat, decide_eq_true hj, Bool.true_and, enc_testBit]
    simp [List.getD_eq_getElem?_getD, hlen, hj]
  have bitG : (BitVec.ofNat 128 (enc (gF k a b) pts)).getLsbD j = zeroGate k (a (pts[j]'(by omega))) (b (pts[j]'(by omega))) := by
    rw [BitVec.getLsbD_ofNat, decide_eq_true hj, Bool.true_and, enc_testBit]
    simp [List.getD_eq_getElem?_getD, hlen, hj, gF]
  rw [bitG]
  fin_cases k
  · simp only [zeroGate, BitVec.getLsbD_and, bitA, bitB]
  · simp only [zeroGate, BitVec.getLsbD_or, bitA, bitB]
  · simp only [zeroGate, BitVec.getLsbD_and, BitVec.getLsbD_not, hj, decide_true, Bool.true_and, bitA, bitB]
  · simp only [zeroGate, BitVec.getLsbD_and, BitVec.getLsbD_not, hj, decide_true, Bool.true_and, bitA, bitB, Bool.and_comm]

def zeroOr (av : Finset W) (x : W) : Prop := x = 0 ∨ x ∈ av

theorem zeroOr_insert {av : Finset W} {x z : W} (h : zeroOr av x) : zeroOr (insert z av) x :=
  h.imp id (fun hm => Finset.mem_insert_of_mem hm)

theorem opW_step (k : Fin 4) {av : Finset W} {a b : W} (ha : zeroOr av a) (hb : zeroOr av b) :
    zeroOr av (opW k a b) ∨
      ∃ x ∈ av, ∃ y ∈ av, x ≠ y ∧ ∃ z ∈ basicOps x y, opW k a b = z := by
  have hall : ∀ x : W, x &&& ~~~(0 : W) = x := fun x => BitVec.and_allOnes
  have hzo : ∀ x : W, (0 : W) ||| x = x := fun x => BitVec.zero_or
  have hoz : ∀ x : W, x ||| (0 : W) = x := fun x => BitVec.or_zero
  rcases ha with rfl | ha
  · left
    fin_cases k
    · exact Or.inl BitVec.zero_and
    · simpa only [opW, hzo] using hb
    · exact Or.inl BitVec.zero_and
    · simpa only [opW, hall] using hb
  rcases hb with rfl | hb
  · left
    fin_cases k
    · exact Or.inl BitVec.and_zero
    · exact Or.inr (by simpa only [opW, hoz] using ha)
    · exact Or.inr (by simpa only [opW, hall] using ha)
    · exact Or.inl BitVec.zero_and
  by_cases hab : a = b
  · subst b; left; fin_cases k <;> simp [opW, zeroOr, ha]
  · right
    refine ⟨a, ha, b, hb, hab, opW k a b, ?_, rfl⟩
    fin_cases k <;> simp [opW, basicOps, ops]

theorem uc_to_build (pts : List (Fin 8 → Bool)) (hlen : pts.length = 128) :
    ∀ (t : ℕ) (S : BF → Prop) (av : Finset W) (f : BF),
      (∀ w, S w → zeroOr av (evalW pts w)) → evalW pts f ≠ 0 →
      UC gF (fun _ => True) t S f → build basicOps (evalW pts f) t av
  | 0, S, av, f, hS, hf, hu => (hS f hu).resolve_left hf
  | t + 1, S, av, f, hS, hf, hu => by
    rcases hu with hu | ⟨k, a, b, _, ha, hb, tail⟩
    · exact Or.inl (uc_to_build pts hlen t S av f hS hf hu)
    · rcases opW_step k (hS a ha) (hS b hb) with hz | ⟨x, hx, y, hy, hxy, z, hz, heq⟩
      · refine Or.inl (uc_to_build pts hlen t _ av f ?_ hf tail)
        rintro w (rfl | hw)
        · rw [evalW_gF pts hlen]; exact hz
        · exact hS w hw
      · refine Or.inr ⟨x, hx, y, hy, hxy, z, hz, uc_to_build pts hlen t _ (insert z av) f ?_ hf tail⟩
        rintro w (rfl | hw)
        · rw [evalW_gF pts hlen, heq]; exact Or.inr (Finset.mem_insert_self ..)
        · exact zeroOr_insert (hS w hw)

theorem UC_monoS {α : Type} {G : Fin 4 → α → α → α} {A : Fin 4 → Prop} :
    ∀ (t : ℕ) (S S' : α → Prop) (f : α), (∀ w, S w → S' w) → UC G A t S f → UC G A t S' f
  | 0, _, _, f, h, hu => h f hu
  | t + 1, S, S', f, h, hu => by
    rcases hu with hu | ⟨k, a, b, hk, ha, hb, hu⟩
    · exact Or.inl (UC_monoS t S S' f h hu)
    · exact Or.inr ⟨k, a, b, hk, h a ha, h b hb,
        UC_monoS t _ _ f (fun w hw => hw.imp id (h w)) hu⟩

def phi (p : Fin 8) (b : Bool) (a : BF) : BF :=
  ori (fun x => a (Function.update x p b))

def Fix (p : Fin 8) (a : BF) : Prop :=
  (∀ b x, a (Function.update x p b) = a x) ∧ a (fun _ => false) = false

theorem phi_var_self (p : Fin 8) (b : Bool) : phi p b (var p) = zF :=
  funext fun x => by simp [phi, ori, var, zF]

theorem phi_fix {p : Fin 8} {a : BF} (h : Fix p a) (b : Bool) : phi p b a = a :=
  funext fun x => by simp [phi, ori, h.1, h.2]

theorem fix_var {p i : Fin 8} (h : i ≠ p) : Fix p (var i) :=
  ⟨fun b x => by simp [var, Function.update_of_ne h], rfl⟩

theorem not_fix_var (p : Fin 8) : ¬ Fix p (var p) := by
  intro h
  have h1 := h.1 true (fun _ => false)
  simp [var] at h1

theorem fix_gF {p : Fin 8} {a b : BF} (k : Fin 4) (ha : Fix p a) (hb : Fix p b) :
    Fix p (gF k a b) :=
  ⟨fun v x => by simp [gF, ha.1, hb.1], by fin_cases k <;> simp [gF, zeroGate, ha.2, hb.2]⟩

theorem phi_gF (p : Fin 8) (v : Bool) (k : Fin 4) (a b : BF) :
    ∃ k', phi p v (gF k a b) = gF k' (phi p v a) (phi p v b) := by
  fin_cases k <;> cases hca : a (Function.update (fun _ => false) p v) <;>
    cases hcb : b (Function.update (fun _ => false) p v) <;>
    first
    | (refine ⟨0, funext fun x => ?_⟩; cases hax : a (Function.update x p v) <;> cases hbx : b (Function.update x p v) <;> simp [phi, ori, gF, zeroGate, hca, hcb, hax, hbx] <;> done)
    | (refine ⟨1, funext fun x => ?_⟩; cases hax : a (Function.update x p v) <;> cases hbx : b (Function.update x p v) <;> simp [phi, ori, gF, zeroGate, hca, hcb, hax, hbx] <;> done)
    | (refine ⟨2, funext fun x => ?_⟩; cases hax : a (Function.update x p v) <;> cases hbx : b (Function.update x p v) <;> simp [phi, ori, gF, zeroGate, hca, hcb, hax, hbx] <;> done)
    | (refine ⟨3, funext fun x => ?_⟩; cases hax : a (Function.update x p v) <;> cases hbx : b (Function.update x p v) <;> simp [phi, ori, gF, zeroGate, hca, hcb, hax, hbx] <;> done)

theorem UC_phi (p : Fin 8) (v : Bool) :
    ∀ (t : ℕ) (S S' : BF → Prop) (f : BF),
      (∀ w, S w → phi p v w = zF ∨ S' (phi p v w)) → phi p v f ≠ zF →
      UC gF (fun _ => True) t S f → UC gF (fun _ => True) t S' (phi p v f)
  | 0, _, _, f, hS, hf, hu => (hS f hu).resolve_left hf
  | t + 1, S, S', f, hS, hf, hu => by
    rcases hu with hu | ⟨k, a, b, _, ha, hb, tail⟩
    · exact Or.inl (UC_phi p v t S S' f hS hf hu)
    · obtain ⟨k', hk'⟩ := phi_gF p v k a b
      rcases hS a ha with ha0 | ha1
      · refine Or.inl (UC_phi p v t _ S' f ?_ hf tail)
        rintro w (rfl | hw)
        · rw [hk', ha0]
          rcases gF_zero_left k' (phi p v b) with e | e
          · exact Or.inl e
          · rw [e]; exact hS b hb
        · exact hS w hw
      rcases hS b hb with hb0 | hb1
      · refine Or.inl (UC_phi p v t _ S' f ?_ hf tail)
        rintro w (rfl | hw)
        · rw [hk', hb0]
          rcases gF_zero_right k' (phi p v a) with e | e
          · exact Or.inl e
          · rw [e]; exact Or.inr ha1
        · exact hS w hw
      · refine Or.inr ⟨k', phi p v a, phi p v b, trivial, ha1, hb1, UC_phi p v t _ _ f ?_ hf tail⟩
        rintro w (rfl | hw)
        · exact Or.inr (Or.inl hk')
        · exact (hS w hw).imp id Or.inr

theorem kill_left (p : Fin 8) (k : Fin 4) : ∃ b : Bool, ∀ y : BF, phi p b (gF k (var p) y) = zF := by
  fin_cases k
  · exact ⟨false, fun y => funext fun x => by simp [phi, ori, gF, var, zeroGate, zF]⟩
  · exact ⟨true, fun y => funext fun x => by simp [phi, ori, gF, var, zeroGate, zF]⟩
  · exact ⟨false, fun y => funext fun x => by simp [phi, ori, gF, var, zeroGate, zF]⟩
  · exact ⟨true, fun y => funext fun x => by simp [phi, ori, gF, var, zeroGate, zF]⟩

theorem kill_right (p : Fin 8) (k : Fin 4) : ∃ b : Bool, ∀ x : BF, phi p b (gF k x (var p)) = zF := by
  fin_cases k
  · exact ⟨false, fun a => funext fun x => by simp [phi, ori, gF, var, zeroGate, zF]⟩
  · exact ⟨true, fun a => funext fun x => by simp [phi, ori, gF, var, zeroGate, zF]⟩
  · exact ⟨true, fun a => funext fun x => by simp [phi, ori, gF, var, zeroGate, zF]⟩
  · exact ⟨false, fun a => funext fun x => by simp [phi, ori, gF, var, zeroGate, zF]⟩

def Good (p : Fin 8) (S : BF → Prop) : Prop := ∀ w, S w → w = var p ∨ Fix p w

theorem phase2 (p : Fin 8) (b : Bool) (f : BF) (hf1 : phi p b f ≠ zF) (hf2 : ¬ Fix p f) :
    ∀ (t : ℕ) (S : BF → Prop) (s : BF), Good p S → phi p b s = zF →
      UC gF (fun _ => True) t (fun w => w = s ∨ S w) f →
      ∃ t', t' + 1 ≤ t ∧ UC gF (fun _ => True) t' (fun w => S w ∧ w ≠ var p) (phi p b f) := by
  have noMem : ∀ (S : BF → Prop) (s : BF), Good p S → phi p b s = zF →
      (f = s ∨ S f) → False := by
    rintro S s hG hs (rfl | hf)
    · exact hf1 hs
    · rcases hG f hf with rfl | hfx
      · exact hf1 (phi_var_self p b)
      · exact hf2 hfx
  intro t
  induction t with
  | zero => intro S s hG hs hu; exact (noMem S s hG hs hu).elim
  | succ t ih =>
    intro S s hG hs hu
    rcases hu with hu | ⟨k, a, c, _, ha, hc, tail⟩
    · obtain ⟨t', ht, hr⟩ := ih S s hG hs hu
      exact ⟨t', by omega, hr⟩
    · have cls : ∀ w, (w = s ∨ S w) → phi p b w = zF ∨ (S w ∧ Fix p w ∧ w ≠ var p) := by
        rintro w (rfl | hw)
        · exact Or.inl hs
        · rcases hG w hw with rfl | hfx
          · exact Or.inl (phi_var_self p b)
          · exact Or.inr ⟨hw, hfx, fun e => not_fix_var p (e ▸ hfx)⟩
      have drop : phi p b (gF k a c) = zF ∨
          (S (phi p b (gF k a c)) ∧ phi p b (gF k a c) ≠ var p) →
          ∃ t', t' + 1 ≤ t + 1 ∧ UC gF (fun _ => True) t' (fun w => S w ∧ w ≠ var p) (phi p b f) := by
        intro hg
        refine ⟨t, le_rfl, UC_phi p b t _ _ f ?_ hf1 tail⟩
        rintro w (rfl | hw)
        · exact hg
        · rcases cls w hw with h0 | ⟨hwS, hfx, hne⟩
          · exact Or.inl h0
          · rw [phi_fix hfx b]; exact Or.inr ⟨hwS, hne⟩
      rcases cls a ha with ha0 | ⟨haS, hafx, hane⟩
      · apply drop
        obtain ⟨k', hk'⟩ := phi_gF p b k a c
        rw [hk', ha0]
        rcases gF_zero_left k' (phi p b c) with e | e
        · exact Or.inl e
        · rw [e]
          rcases cls c hc with hc0 | ⟨hcS, hcfx, hcne⟩
          · exact Or.inl hc0
          · rw [phi_fix hcfx b]; exact Or.inr ⟨hcS, hcne⟩
      rcases cls c hc with hc0 | ⟨hcS, hcfx, hcne⟩
      · apply drop
        obtain ⟨k', hk'⟩ := phi_gF p b k a c
        rw [hk', hc0]
        rcases gF_zero_right k' (phi p b a) with e | e
        · exact Or.inl e
        · rw [e, phi_fix hafx b]; exact Or.inr ⟨haS, hane⟩
      · have hgfx : Fix p (gF k a c) := fix_gF k hafx hcfx
        have hG' : Good p (fun w => w = gF k a c ∨ S w) := by
          rintro w (rfl | hw)
          · exact Or.inr hgfx
          · exact hG w hw
        have tail' : UC gF (fun _ => True) t (fun w => w = s ∨ (w = gF k a c ∨ S w)) f :=
          UC_monoS t _ _ f (by rintro w (rfl | rfl | hw) <;> tauto) tail
        obtain ⟨t', ht, hr⟩ := ih (fun w => w = gF k a c ∨ S w) s hG' hs tail'
        refine ⟨t' + 1, by omega, UC_gate k a c trivial ⟨haS, hane⟩ ⟨hcS, hcne⟩ ?_⟩
        exact UC_monoS t' _ _ _ (by rintro w ⟨rfl | hw, hne⟩; exact Or.inl rfl; exact Or.inr ⟨hw, hne⟩) hr

theorem two_gates (p : Fin 8) (f : BF) (h0 : phi p false f ≠ zF) (h1 : phi p true f ≠ zF)
    (hf : ¬ Fix p f) :
    ∀ (t : ℕ) (S : BF → Prop), Good p S → UC gF (fun _ => True) t S f →
      ∃ t', t' + 2 ≤ t ∧
        (UC gF (fun _ => True) t' (fun w => S w ∧ w ≠ var p) (phi p false f) ∨
         UC gF (fun _ => True) t' (fun w => S w ∧ w ≠ var p) (phi p true f)) := by
  have noMem : ∀ (S : BF → Prop), Good p S → S f → False := by
    intro S hG hSf
    rcases hG f hSf with rfl | hfx
    · exact h0 (phi_var_self p false)
    · exact hf hfx
  intro t
  induction t with
  | zero => intro S hG hu; exact (noMem S hG hu).elim
  | succ t ih =>
    intro S hG hu
    rcases hu with hu | ⟨k, a, c, _, ha, hc, tail⟩
    · obtain ⟨t', ht, hr⟩ := ih S hG hu
      exact ⟨t', by omega, hr⟩
    · have kill (b : Bool) (hkb : phi p b (gF k a c) = zF) :
          ∃ t', t' + 2 ≤ t + 1 ∧
            (UC gF (fun _ => True) t' (fun w => S w ∧ w ≠ var p) (phi p false f) ∨
             UC gF (fun _ => True) t' (fun w => S w ∧ w ≠ var p) (phi p true f)) := by
        cases b
        · obtain ⟨t', ht, hr⟩ := phase2 p false f h0 hf t S (gF k a c) hG hkb tail
          exact ⟨t', by omega, Or.inl hr⟩
        · obtain ⟨t', ht, hr⟩ := phase2 p true f h1 hf t S (gF k a c) hG hkb tail
          exact ⟨t', by omega, Or.inr hr⟩
      rcases hG a ha with rfl | hafx
      · obtain ⟨b, hb⟩ := kill_left p k
        exact kill b (hb c)
      rcases hG c hc with rfl | hcfx
      · obtain ⟨b, hb⟩ := kill_right p k
        exact kill b (hb a)
      · have hane : a ≠ var p := fun e => not_fix_var p (e ▸ hafx)
        have hcne : c ≠ var p := fun e => not_fix_var p (e ▸ hcfx)
        have hgfx : Fix p (gF k a c) := fix_gF k hafx hcfx
        have hG' : Good p (fun w => w = gF k a c ∨ S w) := by
          rintro w (rfl | hw)
          · exact Or.inr hgfx
          · exact hG w hw
        obtain ⟨t', ht, hr⟩ := ih (fun w => w = gF k a c ∨ S w) hG' tail
        refine ⟨t' + 1, by omega, ?_⟩
        rcases hr with hr | hr
        · exact Or.inl (UC_gate k a c trivial ⟨ha, hane⟩ ⟨hc, hcne⟩
            (UC_monoS t' _ _ _ (by rintro w ⟨rfl | hw, hne⟩; exact Or.inl rfl; exact Or.inr ⟨hw, hne⟩) hr))
        · exact Or.inr (UC_gate k a c trivial ⟨ha, hane⟩ ⟨hc, hcne⟩
            (UC_monoS t' _ _ _ (by rintro w ⟨rfl | hw, hne⟩; exact Or.inl rfl; exact Or.inr ⟨hw, hne⟩) hr))

def graph (x : Fin 8 → Bool) : Bool :=
  (x 0 && x 3) || (x 1 && x 4) || (x 0 && x 5) || (x 2 && x 5) ||
  (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 4 && x 6) ||
  (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 5 && x 7)

def assignment (a : ℕ) (i : Fin 8) : Bool := a.testBit i.val

def ptsNat : List ℕ :=
  [18, 66, 130, 36, 68, 132, 22, 38, 70, 134, 18, 80, 22, 52, 84, 148, 36, 160, 38, 50, 98, 162,
   50, 52, 112, 176, 66, 68, 80, 98, 100, 112, 224, 130, 132, 160, 146, 148, 176, 208, 194, 196,
   208, 224, 18, 36, 66, 68, 80, 130, 132, 160, 18, 36, 66, 68, 80, 130, 132, 160, 18, 36, 66, 68,
   2, 2, 2, 4, 4, 4, 6, 6, 6, 6, 16, 16, 20, 20, 20, 20, 32, 32, 34, 34, 34, 34, 48, 48, 48, 48,
   64, 64, 64, 96, 96, 96, 96, 128, 128, 128, 144, 144, 144, 144, 192, 192, 192, 192, 6, 6, 6, 6,
   6, 6, 6, 6, 20, 20, 20, 20, 20, 20, 20, 20, 34, 34, 34, 34]

def pts : List (Fin 8 → Bool) := ptsNat.map assignment

def rows : List W :=
  [((0xf00ff000003c03c7 : BitVec 64) ++ (0x52525112247c17c7 : BitVec 64)),
   ((0xffff0000000f3f8 : BitVec 64) ++ (0xa4a4a2244885f3f8 : BitVec 64)),
   ((0xff000f003c0fc00 : BitVec 64) ++ (0x111114f093c8fc41 : BitVec 64)),
   ((0xf0000001e3ff0000 : BitVec 64) ++ (0x28282849e3ff2088 : BitVec 64)),
   ((0xf01fc000000 : BitVec 64) ++ (0xc1c1cf81fd104912 : BitVec 64)),
   ((0xffe00000000 : BitVec 64) ++ (0xe0e0fff02228224 : BitVec 64))]

def Fend : BF := rst 0 (rst 3 graph)

theorem evalW_Fend : evalW pts Fend = ~~~goal := by decide +kernel

theorem evalW_vars :
    ∀ i ∈ (((Finset.univ : Finset (Fin 8)).erase 3).erase 0),
      evalW pts (var i) ∈ rows := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem search_reject : search 7 rows = false := by decide +kernel

theorem rst0_phi3_false : rst 0 (phi 3 false graph) = Fend := by
  funext x
  simp [rst, phi, ori, Fend, graph]

theorem rst0_phi3_true : rst 0 (phi 3 true graph) = Fend := by
  funext x
  simp [rst, phi, ori, Fend, graph]

theorem lower_with_not (gates : List Gate) (o : ℕ) (legal : GOK gates)
    (hnot : ∃ g ∈ gates, g.op = GateOp.not)
    (comp : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = graph x) :
    12 ≤ gates.length := by
  have hg : (wiresF gates (List.ofFn var)).getD o zF = graph := by
    funext x
    rw [← comp x, ← getD_map_x, ← wires_eq]
    simp only [Circuit.eval, Circuit.wires, List.map_ofFn]
    rfl
  have start := trans_binary gates (List.ofFn var) (sourceVars Finset.univ) legal (by
    intro w hw
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hw
    exact Or.inr ⟨i, Finset.mem_univ i, ori_zp rfl⟩) o
  rw [hg, ori_zp (by decide : graph (fun _ => false) = false)] at start
  rcases start with e | base
  · have c := congrFun e (assignment 18)
    exact False.elim ((by decide : graph (assignment 18) ≠ false) c)
  have hGood : Good 3 (sourceVars Finset.univ) := by
    rintro w ⟨i, _, rfl⟩
    by_cases hi : i = 3
    · exact Or.inl (hi ▸ rfl)
    · exact Or.inr (fix_var hi)
  obtain ⟨t1, pay1, h1⟩ := two_gates 3 graph
    (by intro h; exact (by decide : phi 3 false graph (assignment 18) ≠ false) (congrFun h (assignment 18)))
    (by intro h; exact (by decide : phi 3 true graph (assignment 18) ≠ false) (congrFun h (assignment 18)))
    (by intro h; exact (by decide : graph (Function.update (assignment 1) 3 true) ≠ graph (assignment 1)) (h.1 true (assignment 1)))
    (countBinary gates) (sourceVars Finset.univ) hGood base
  have hSub : ∀ w, (sourceVars Finset.univ w ∧ w ≠ var 3) → sourceVars (Finset.univ.erase 3) w := by
    rintro w ⟨⟨i, _, rfl⟩, hne⟩
    refine ⟨i, Finset.mem_erase.2 ⟨fun e => hne (e ▸ rfl), Finset.mem_univ i⟩, rfl⟩
  have hEnd : ∃ t2, t2 + 1 ≤ t1 ∧ UC gF (fun _ => True) t2 (sourceVars ((Finset.univ.erase 3).erase 0)) Fend := by
    rcases h1 with h1 | h1
    · have h1' := UC_monoS t1 _ _ _ hSub h1
      obtain ⟨t2, pay2, h2⟩ := remove_var (phi 3 false graph) 0 (Finset.univ.erase 3) t1
        ⟨assignment 33, by decide⟩
        (by intro h; exact (by decide : rst 0 (phi 3 false graph) (assignment 18) ≠ false) (congrFun h (assignment 18))) h1'
      rw [rst0_phi3_false] at h2
      exact ⟨t2, pay2, h2⟩
    · have h1' := UC_monoS t1 _ _ _ hSub h1
      obtain ⟨t2, pay2, h2⟩ := remove_var (phi 3 true graph) 0 (Finset.univ.erase 3) t1
        ⟨assignment 1, by decide⟩
        (by intro h; exact (by decide : rst 0 (phi 3 true graph) (assignment 18) ≠ false) (congrFun h (assignment 18))) h1'
      rw [rst0_phi3_true] at h2
      exact ⟨t2, pay2, h2⟩
  obtain ⟨t2, pay2, h2⟩ := hEnd
  have extra := countBinary_lt gates hnot
  by_contra! small
  have hle : t2 ≤ 7 := by omega
  have hb : build basicOps (evalW pts Fend) 7 rows.toFinset :=
    uc_to_build pts (by simp [pts, ptsNat]) 7 _ rows.toFinset Fend (by
      rintro w ⟨i, hi, rfl⟩
      exact Or.inr (List.mem_toFinset.mpr (evalW_vars i hi)))
      (by rw [evalW_Fend]; decide) (UC_le hle h2)
  rw [evalW_Fend] at hb
  have hs := search_complete (Or.inr rfl) 7 rows (by decide) hb
  rw [search_reject] at hs
  exact Bool.noConfusion hs

def witness : List Gate :=
  [⟨.or, [0, 2]⟩, ⟨.and, [0, 3]⟩, ⟨.or, [9, 5]⟩, ⟨.or, [1, 8]⟩,
   ⟨.or, [1, 6]⟩, ⟨.or, [8, 7]⟩, ⟨.and, [4, 12]⟩, ⟨.and, [10, 13]⟩,
   ⟨.or, [14, 15]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [11, 17]⟩, ⟨.or, [18, 16]⟩]

theorem witnessBasis : ∀ g ∈ witness,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 8 → Bool,
    Circuit.eval ⟨witness, 19⟩ (List.ofFn x) = graph x := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem graph_correct : ∀ x : Fin 8 → Bool,
    graph x = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 5, 7] : List ℕ).length / 2,
      (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧
      (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  decide +kernel

end PEqualNP.Outside.L_meta_14764

open PEqualNP.Outside.L_meta_14764 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_14764 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gates o legal _oneNot computes
  by_cases hnot : ∃ g ∈ gates, g.op = GateOp.not
  · have comp : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = graph x :=
      fun x => (computes x).trans (graph_correct x).symm
    have large := lower_with_not gates o legal hnot comp
    have hw : witness.length = 12 := rfl
    exact ⟨witness, 19, witnessBasis, by omega, fun x => (witnessCorrect x).trans (graph_correct x)⟩
  · refine ⟨gates, o, ?_, le_rfl, computes⟩
    intro g hg
    obtain ⟨ops, hlen⟩ := legal g hg
    refine ⟨?_, hlen⟩
    rcases ops with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim (hnot ⟨g, hg, h⟩)
