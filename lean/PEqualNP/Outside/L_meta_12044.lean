import PEqualNP.Defs

-- The witness has twelve binary gates. Any circuit with a NOT and fewer gates
-- would have at most ten binary gates even with every negation available for free.
-- Finite signed-circuit certificates below exclude that possibility.
-- Signed-wire search and gate projections adapt the project’s Apache 2.0 proofs.
namespace PEqualNP.Outside.L_meta_12044_aux
namespace CoreSigned

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

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
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

def F (x : Fin 6 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 3) || (x 1 && x 5) || (x 2 && x 3) || (x 2 && x 4)

end CoreSigned

namespace SignedProjection
variable {α β : Type} [DecidableEq α] [DecidableEq β] [Zero β]

def avail (pin : α → β) (S : Finset α) := (S.image pin).erase 0
def lost (pin : α → β) (S : Finset α) := (S.filter fun x => pin x = 0).card

theorem avail_mem (pin : α → β) {S : Finset α} {x : β} :
    x ∈ avail pin S ↔ x ≠ 0 ∧ ∃ a ∈ S, pin a = x := by simp [avail]

theorem avail_mono (pin : α → β) {S T : Finset α} (h : S ⊆ T) : avail pin S ⊆ avail pin T := by
  intro y hy
  obtain ⟨hn,x,hx,rfl⟩ := (avail_mem pin).mp hy
  exact (avail_mem pin).mpr ⟨hn,x,h hx,rfl⟩

theorem avail_cases (pin : α → β) {S : Finset α} {c : α} {x : β} (h : x ∈ avail pin (insert c S)) :
    x = pin c ∨ x ∈ avail pin S := by
  obtain ⟨hn,y,hy,rfl⟩ := (avail_mem pin).mp h
  rcases Finset.mem_insert.mp hy with rfl|hy
  · exact Or.inl rfl
  · exact Or.inr ((avail_mem pin).mpr ⟨hn,y,hy,rfl⟩)

theorem lost_insert (pin : α → β) (c : α) (S : Finset α) :
    lost pin (insert c S) = lost pin S + (if pin c = 0 ∧ c ∉ S then 1 else 0) := by
  by_cases mem : c ∈ S
  · rw [Finset.insert_eq_of_mem mem,ite_eq_right (fun q => q.2 mem),Nat.add_zero]
  · by_cases h : pin c = 0
    · rw [ite_eq_left ⟨h,mem⟩]
      unfold lost
      rw [Finset.filter_insert,ite_eq_left h,Finset.card_insert_of_notMem]
      exact fun q => mem (Finset.mem_filter.mp q).1
    · rw [ite_eq_right (fun q => h q.1),Nat.add_zero]
      unfold lost
      rw [Finset.filter_insert,ite_eq_right h]

theorem projected (pin : α → β) (ops : α → α → Finset α) (ops2 : β → β → Finset β) (goal : α)
    (hgoal : pin goal ≠ 0)
    (maps : ∀ {a b c}, c ∈ ops a b → pin c ∈ ops2 (pin a) (pin b))
    (idA : ∀ {a b c}, c ∈ ops2 a b → a = 0 → c = 0 ∨ c = b)
    (idB : ∀ {a b c}, c ∈ ops2 a b → b = 0 → c = 0 ∨ c = a)
    (idS : ∀ {a b c}, c ∈ ops2 a b → a = b → c = 0 ∨ c = b)
    {k : Nat} {S : Finset α} (h : CoreSigned.live ops goal k S) :
    ∃ j, j + lost pin S ≤ k ∧ ∃ T ⊆ avail pin S, CoreSigned.live ops2 (pin goal) j T := by
  induction k generalizing S with
  | zero =>
    change S = {goal} at h
    subst S
    exact ⟨0,by simp [lost,hgoal],{(pin goal)},by simp [avail,hgoal],rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a,_,b,_,ne,c,op,fresh,U,rfl,tail⟩
    · obtain ⟨j,hj,ws,sub,hws⟩ := ih skip
      exact ⟨j,by omega,ws,sub,hws⟩
    let prev := insert a (insert b U)
    have cnew : c ∉ U := fun h => fresh (by simp [h])
    have repr := maps op
    obtain ⟨j,limit,T,sub,path⟩ := ih tail
    have both (ha : pin a = 0) (hb : pin b = 0) : pin c = 0 := by
      exact (idA repr ha).elim id (fun e => e.trans hb)
    have skipcost : lost pin prev ≤ lost pin (insert c U) + 1 := by
      simp only [prev,lost_insert]
      split_ifs <;> grind
    have liftU : avail pin U ⊆ avail pin prev := avail_mono pin (by intro u hu; simp [prev,hu])
    by_cases useful : pin c ∈ T ∧ pin c ∉ avail pin prev
    · have nz := ((avail_mem pin).mp (sub useful.1)).1
      have df (v : α) (hv : v ∈ prev) : pin c ≠ pin v := by
        intro e
        exact useful.2 ((avail_mem pin).mpr ⟨nz,v,hv,e.symm⟩)
      have da := df a (by simp [prev])
      have db := df b (by simp [prev])
      have ha : pin a ≠ 0 := fun e => (idA repr e).elim nz db
      have hb : pin b ≠ 0 := fun e => (idB repr e).elim nz da
      have distinct : pin a ≠ pin b := fun e => (idS repr e).elim nz db
      have vcost : lost pin prev ≤ lost pin (insert c U) := by
        simp only [prev,lost_insert]
        split_ifs <;> grind
      let V := T.erase (pin c)
      have old (v : β) (hv : v ∈ V) : v ∈ avail pin U :=
        (avail_cases pin (sub (Finset.mem_erase.mp hv).2)).resolve_left (Finset.mem_erase.mp hv).1
      let B := insert (pin a) (insert (pin b) V)
      refine ⟨j+1,by change j+1+lost pin prev ≤ k+1; omega,B,?_,Or.inr ?_⟩
      · intro v hv
        rcases Finset.mem_insert.mp hv with rfl|hv
        · exact (avail_mem pin).mpr ⟨ha,a,by simp,rfl⟩
        rcases Finset.mem_insert.mp hv with rfl|hv
        · exact (avail_mem pin).mpr ⟨hb,b,by simp,rfl⟩
        exact liftU (old _ hv)
      · refine ⟨pin a,by simp [B],pin b,by simp [B],distinct,pin c,?_,?_,V,rfl,?_⟩
        · exact repr
        · simp [B,V,da,db]
        · rwa [show insert (pin c) V = T from Finset.insert_erase useful.1]
    · refine ⟨j,by change j+lost pin prev ≤ k+1; omega,T,?_,path⟩
      intro v hv
      rcases avail_cases pin (sub hv) with rfl|old
      · by_contra miss
        exact useful ⟨hv,miss⟩
      · exact liftU old


end SignedProjection

namespace SignedProjection
variable {n : Nat}

def signedOps (a b : BitVec n) := [a &&& b, a ||| b, a &&& ~~~b, b &&& ~~~a].toFinset

theorem zero_left {a b c : BitVec n} (h : c ∈ signedOps a b) (eq : a = 0) : c = 0 ∨ c = b := by
  subst a
  simpa [signedOps,or_comm] using h

theorem zero_right {a b c : BitVec n} (h : c ∈ signedOps a b) (eq : b = 0) : c = 0 ∨ c = a := by
  subst b
  simpa [signedOps,or_comm] using h

theorem equal_inputs {a b c : BitVec n} (h : c ∈ signedOps a b) (eq : a = b) : c = 0 ∨ c = b := by
  subst a
  simpa [signedOps,or_comm] using h

def signedPin (mask : BitVec n) (base : Fin n) (x : BitVec n) : BitVec n :=
  (if x[base.val] then ~~~x else x) &&& mask

theorem masked_ops (m : BitVec n) {a b c : BitVec n} (h : c ∈ signedOps a b) :
    c &&& m ∈ signedOps (a &&& m) (b &&& m) := by
  simp only [signedOps,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at *
  rcases h with rfl|rfl|rfl|rfl
  · left; ext i h; simp [Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
  · right;left; ext i h; simp only [BitVec.getElem_or,BitVec.getElem_and]; cases a[i] <;> cases b[i] <;> simp
  · right;right;left; ext i h
    simp only [BitVec.getElem_and,BitVec.getElem_not]
    cases a[i] <;> cases b[i] <;> cases m[i] <;> decide
  · right;right;right; ext i h
    simp only [BitVec.getElem_and,BitVec.getElem_not]
    cases a[i] <;> cases b[i] <;> cases m[i] <;> decide

def polarity (b : Bool) (x : BitVec n) := if b then ~~~x else x

theorem polarity_ops (i : Fin n) {a b c : BitVec n} (h : c ∈ signedOps a b) :
    polarity (c[i.val]) c ∈ signedOps (polarity (a[i.val]) a) (polarity (b[i.val]) b) := by
  simp only [signedOps,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at *
  rcases h with rfl|rfl|rfl|rfl <;>
    simp only [BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not] <;>
    cases a[i.val] <;> cases b[i.val] <;>
    simp [polarity,BitVec.not_and,BitVec.not_or,BitVec.and_comm,BitVec.or_comm]

theorem signedPin_ops (m : BitVec n) (i : Fin n) {a b c : BitVec n} (h : c ∈ signedOps a b) :
    signedPin m i c ∈ signedOps (signedPin m i a) (signedPin m i b) :=
  masked_ops m (polarity_ops i h)

theorem live_build {α : Type} [DecidableEq α] {ops : α → α → Finset α} {goal : α}
    {k : Nat} {S V : Finset α} (h : CoreSigned.live ops goal k S) (sub : S ⊆ V) :
    CoreSigned.build ops goal k V := by
  induction k generalizing S V with
  | zero => change S = {goal} at h; subst S; exact sub (Finset.mem_singleton_self _)
  | succ k ih =>
    rcases h with skip|⟨a,ha,b,hb,ne,c,opc,_,rest,eq,tail⟩
    · exact Or.inl (ih skip sub)
    · refine Or.inr ⟨a,sub ha,b,sub hb,ne,c,opc,ih tail ?_⟩
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl|hr
      · simp
      · exact Finset.mem_insert_of_mem (sub (eq ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hr)))

end SignedProjection

namespace SignedProjection
variable {α : Type} [DecidableEq α]

def generated (ops : α → α → Finset α) (stock : Finset α) : List (α × α × α) → Finset α → Prop
  | [], result => stock = result
  | (a,b,w) :: rest, result =>
    a ∈ stock ∧ b ∈ stock ∧ a ≠ b ∧ w ∈ ops a b ∧ generated ops (insert w stock) rest result

theorem extend_generated {ops : α → α → Finset α} {goal : α} {stock result : Finset α}
    {recipe : List (α × α × α)} {k : ℕ}
    (h : generated ops stock recipe result) (tail : CoreSigned.build ops goal k result) :
    CoreSigned.build ops goal (k + recipe.length) stock := by
  induction recipe generalizing stock with
  | nil => change stock = result at h; simpa [h] using tail
  | cons step rest ih =>
    obtain ⟨a,b,w⟩ := step
    rcases h with ⟨ha,hb,hn,ho,hrest⟩
    change CoreSigned.build ops goal (k+rest.length+1) stock
    exact Or.inr ⟨a,ha,b,hb,hn,w,ho,ih hrest⟩

theorem pad_build {ops : α → α → Finset α} {goal : α} {S : Finset α} {a b : Nat}
    (le : a ≤ b) (ha : CoreSigned.build ops goal a S) : CoreSigned.build ops goal b S := by
  induction le with
  | refl => exact ha
  | step _ ih => exact Or.inl ih

end SignedProjection

namespace SignedProjection
variable {n : Nat}

theorem exclude_cut (m : BitVec n) (i : Fin n) (goal : BitVec n) (k cap : ℕ)
    (S A U : Finset (BitVec n)) (recipes : List (BitVec n × BitVec n × BitVec n))
    (nonzero : signedPin m i goal ≠ 0)
    (bound : ¬ CoreSigned.build signedOps (signedPin m i goal) cap A)
    (regen : generated signedOps A recipes U) (sub : avail (signedPin m i) S ⊆ U)
    (budget : recipes.length + k ≤ cap + lost (signedPin m i) S) :
    ¬ CoreSigned.live signedOps goal k S := by
  intro h
  obtain ⟨j, hj, T, ht, path⟩ := projected (signedPin m i) signedOps signedOps goal nonzero
    (signedPin_ops m i) zero_left zero_right equal_inputs h
  have localRun := live_build path (ht.trans sub)
  exact bound (pad_build (by omega) (extend_generated regen localRun))

end SignedProjection

namespace SignedProjection
open CoreSigned (live build first_live live_card pairs pick_two live_separates)

abbrev Word := BitVec 64
def signedList (a b : Word) := [a &&& b, a ||| b, a &&& ~~~b, b &&& ~~~a]
theorem ops_swap (a b : Word) : signedOps a b = signedOps b a := by
  ext z
  simp only [signedOps, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto
def keepChoices (a b : Word) (r : List Word) : List (List Word) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List Word} {a b : Word} {needed : Finset Word}
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

theorem singleton_list {goal : Word} {ws : List Word} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def insertW (v : Word) : List Word → List Word
  | [] => [v]
  | x :: xs => if v ≤ x then v :: x :: xs else x :: insertW v xs

def ordered (ws : List Word) := ws.foldr insertW []

theorem insertW_perm (v : Word) (ws : List Word) : (insertW v ws).Perm (v :: ws) := by
  induction ws with
  | nil => exact .refl _
  | cons x xs ih =>
    simp only [insertW]
    split
    · exact .refl _
    · exact (ih.cons x).trans (.swap _ _ _)

theorem ordered_perm (ws : List Word) : (ordered ws).Perm ws := by
  induction ws with
  | nil => exact .refl _
  | cons x xs ih => exact (insertW_perm x (ordered xs)).trans (ih.cons x)

theorem perm_set {u v : List Word} (p : u.Perm v) : u.toFinset = v.toFinset := by
  ext a
  simpa only [List.mem_toFinset] using (p.mem_iff : a ∈ u ↔ a ∈ v)


def children (k : Nat) (ws : List Word) : List (List Word) :=
  (pairs ws).flatMap fun (a,b,r) => (signedList a b).flatMap fun z =>
    if z ∈ ws then [] else
      (keepChoices a b r).filterMap fun kept =>
        if kept.length ≤ k then some (ordered (z :: kept)) else none

theorem zero_prune {goal : Word} (nz : goal ≠ 0) {k : Nat} {S : Finset Word}
    (h : live signedOps goal k S) : ∃ j ≤ k, ∃ T ⊆ S.erase 0, live signedOps goal j T := by
  obtain ⟨j,le,T,sub,path⟩ := projected id signedOps signedOps goal nz (fun q => q)
    zero_left zero_right equal_inputs h
  refine ⟨j,by omega,T,?_,path⟩
  simpa [avail] using sub

theorem step_no (goal : Word) (n : Nat) (ws : List Word) (hn : ws.Nodup)
    (done_ : ws ≠ [goal])
    (children_ : ∀ qs ∈ children n ws, ¬ live signedOps goal n qs.toFinset)
    : ¬ live signedOps goal (n+1) ws.toFinset := by
  intro h
  rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
  · exact done_ (singleton_list hn done)
  obtain ⟨r,hm,hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
  have go {a b : Word} (hp : ws.Perm (a :: b :: r)) (hmem : (a,b,r) ∈ pairs ws)
      (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ signedOps a b) : False := by
    obtain ⟨kept,hkeep,hnk,hfin⟩ := recover_kept hp hn hset
    have hznew : z ∉ kept := by
      intro hu
      apply hout
      rw [hset]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu))
    have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
    have hraw : live signedOps goal n (z :: kept).toFinset := by simpa [hfin] using tail
    have hc := live_card hraw
    rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
    have hzws : z ∉ ws := by simpa using hout
    have hp' := ordered_perm (z :: kept)
    have mem : ordered (z :: kept) ∈ children n ws := by
      apply List.mem_flatMap.mpr
      refine ⟨(a,b,r),hmem,List.mem_flatMap.mpr ⟨z,List.mem_toFinset.mp hop,?_⟩⟩
      simpa only [hzws,ite_false] using
        (List.mem_filterMap.mpr ⟨kept,hkeep,by simp [show kept.length ≤ n by omega]⟩ :
          ordered (z::kept) ∈ ((keepChoices a b r).filterMap fun kept =>
            if kept.length ≤ n then some (ordered (z :: kept)) else none))
    exact children_ _ mem ((perm_set hp').symm ▸ hraw)
  rcases hm with direct|swap
  · exact go hp direct hs hz
  · exact go (hp.trans (.swap _ _ _)) swap (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)
end SignedProjection

namespace SignedProjection
abbrev V64 := BitVec 64

def bitAt (w : V64) (n : Nat) := w.getLsbD n
def mismatch (g : V64) (ws : List V64) (p q : Nat) :=
  (bitAt g p != bitAt g q) && ws.all (fun w => bitAt w p == bitAt w q)

theorem mismatch_sound {g : V64} {ws : List V64} {p q : Nat} (pp : p < 64) (qq : q < 64)
    (cert : mismatch g ws p q = true) (k : ℕ) : ¬ CoreSigned.live signedOps g k ws.toFinset := by
  intro h
  have parts := Bool.and_eq_true_iff.mp cert
  let D : V64 → Prop := fun w => bitAt w p ≠ bitAt w q
  have dg : D g := by simpa [D] using parts.1
  have hop (a b : V64) (z : V64) (hz : z ∈ signedOps a b) (dz : D z) : D a ∨ D b := by
    by_contra! fail
    apply dz
    obtain ⟨ea,eb⟩ := fail
    simp only [D, not_not] at ea eb
    change bitAt a p = bitAt a q at ea
    change bitAt b p = bitAt b q at eb
    simp only [signedOps, List.mem_toFinset,List.mem_cons, List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl <;>
      simpa only [bitAt, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not,
        pp,qq,decide_true, Bool.true_and, show a.getLsbD p = a.getLsbD q from ea,
        show b.getLsbD p = b.getLsbD q from eb]
  obtain ⟨x,hx,dx⟩ := CoreSigned.live_separates D dg hop h
  exact dx (beq_iff_eq.mp (List.all_eq_true.mp parts.2 x (List.mem_toFinset.mp hx)))

end SignedProjection

namespace SignedProjection
abbrev View := Word × Fin 64 × Word × List Word × Nat × (Nat → Nat)
abbrev Node := Nat × Nat × List Word × (Nat → Nat)
def vm (v : View) := v.1
def va (v : View) := v.2.1
def vg (v : View) := v.2.2.1
def vs (v : View) := v.2.2.2.1
def vk (v : View) := v.2.2.2.2.1
def vh (v : View) := v.2.2.2.2.2
def nv (a : Node) := a.1
def nk (a : Node) := a.2.1
def ns (a : Node) := a.2.2.1
def nh (a : Node) := a.2.2.2

def recipeRun : Nat → Nat → List Word → Option (List (Word × Word × Word) × List Word)
  | 0, code, ws => if code = 1 then some ([],ws) else none
  | fuel+1, code, ws => if code = 1 then some ([],ws) else
    let i := code % 16
    let j := (code / 16) % 16
    let o := (code / 256) % 4
    match ws[i]?, ws[j]? with
    | some a, some b => if a = b then none else
      let w := (signedList a b).getD o 0
      match recipeRun fuel (code / 1024) (ws++[w]) with
      | some (rs,ws') => some ((a,b,w)::rs,ws')
      | none => none
    | _,_ => none

theorem recipeRun_sound (fuel code : Nat) (ws : List Word) {rs out}
    (h : recipeRun fuel code ws = some (rs,out)) :
    generated signedOps ws.toFinset rs out.toFinset := by
  induction fuel generalizing code ws rs out with
  | zero =>
    simp only [recipeRun] at h
    split at h
    · cases h; rfl
    · contradiction
  | succ k ih =>
    simp only [recipeRun] at h
    split at h
    · cases h; rfl
    split at h <;> try contradiction
    rename_i a b ha hb
    split at h <;> try contradiction
    rename_i ne
    split at h <;> try contradiction
    rename_i tail end_ ht
    cases h
    set r := (code / 256) % 4
    let w := (signedList a b).getD r 0
    change a ∈ ws.toFinset ∧ b ∈ ws.toFinset ∧ a ≠ b ∧ w ∈ signedOps a b ∧ _
    refine ⟨List.mem_toFinset.mpr (List.mem_of_getElem? ha),
      List.mem_toFinset.mpr (List.mem_of_getElem? hb),ne,?_,?_⟩
    · have hr : r < 4 := Nat.mod_lt _ (by decide)
      change w ∈ (signedList a b).toFinset
      simp only [List.mem_toFinset]
      have hr' : r < (signedList a b).length := by simpa [signedList] using hr
      simpa [w, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr'] using
        (List.getElem_mem (l := signedList a b) (i := r) hr')
    · have eq : (ws++[w]).toFinset = insert w ws.toFinset := by
        ext x
        simp [or_comm]
      rw [← eq]
      exact ih _ _ ht

def ViewOK (v : View) := ¬ CoreSigned.build signedOps (vg v) (vk v) (vs v).toFinset

def cutOK (v : View) (g : Word) (k : Nat) (ws : List Word) (recipe : Nat) : Bool :=
  let p := signedPin (vm v) (va v)
  if p g != vg v || p g == 0 then false else
    match recipeRun 12 recipe (vs v) with
    | none => false
    | some (rs,out) =>
      decide (avail p ws.toFinset ⊆ out.toFinset) &&
      decide (rs.length+k ≤ vk v + lost p ws.toFinset)

theorem cutOK_sound {v : View} {g : Word} {k : Nat} {ws : List Word} {recipe : Nat}
    (hv : ViewOK v) (hc : cutOK v g k ws recipe = true) :
    ¬ CoreSigned.live signedOps g k ws.toFinset := by
  simp only [cutOK] at hc
  split at hc <;> try contradiction
  rename_i ok
  split at hc <;> try contradiction
  rename_i rs out hr
  have parts := Bool.and_eq_true_iff.mp hc
  have good : signedPin (vm v) (va v) g = vg v ∧ signedPin (vm v) (va v) g ≠ 0 := by
    simpa using ok
  apply exclude_cut (vm v) (va v) g k (vk v) ws.toFinset (vs v).toFinset out.toFinset rs good.2
    (good.1 ▸ hv) (recipeRun_sound _ _ _ hr) (of_decide_eq_true parts.1)
    (of_decide_eq_true parts.2)

end SignedProjection
namespace SignedProjection

def quickCut (v : View) (g : Word) (k : Nat) (ws : List Word) (receipt : Nat) : Bool :=
  let p := signedPin (vm v) (va v)
  if p g != vg v || p g == 0 then false else
    match recipeRun 12 receipt (vs v) with
    | none => false
    | some (rs,out) =>
      decide ws.Nodup &&
      ws.all (fun w => p w == 0 || out.contains (p w)) &&
      decide (rs.length+k ≤ vk v + ws.countP (fun w => p w = 0))

theorem quickCut_sound {v : View} {g : Word} {k : Nat} {ws : List Word} {receipt : Nat}
    (hv : ViewOK v) (ok : quickCut v g k ws receipt = true) :
    ¬ CoreSigned.live signedOps g k ws.toFinset := by
  simp only [quickCut] at ok
  split at ok <;> try contradiction
  rename_i good
  split at ok <;> try contradiction
  rename_i rs out hr
  have parts := Bool.and_eq_true_iff.mp ok
  have pp := Bool.and_eq_true_iff.mp parts.1
  have nd := of_decide_eq_true pp.1
  have gg : signedPin (vm v) (va v) g = vg v ∧ signedPin (vm v) (va v) g ≠ 0 := by
    simpa using good
  apply exclude_cut (vm v) (va v) g k (vk v) ws.toFinset (vs v).toFinset out.toFinset rs gg.2
    (gg.1 ▸ hv) (recipeRun_sound _ _ _ hr)
  · intro x hx
    obtain ⟨ne,w,hw,rfl⟩ := (avail_mem _).mp hx
    have has := List.all_eq_true.mp pp.2 w (List.mem_toFinset.mp hw)
    simp only [Bool.or_eq_true,beq_iff_eq,List.contains_iff_mem] at has
    exact List.mem_toFinset.mpr (has.resolve_left ne)
  · unfold lost
    rw [List.Nodup.card_eq_countP nd]
    exact of_decide_eq_true parts.2

end SignedProjection

namespace SignedProjection.QFast
abbrev Table (α : Type) := Nat × (Nat → Option α)
def get {α : Type} (t : Table α) (i : Nat) : Option α := if i < t.1 then t.2 i else none

def checkHint (views : Table View) (nodes : Table Node) (vID : Nat) (g : Word)
    (k : Nat) (ws : List Word) (hint : Nat) : Bool :=
  let val := hint/4
  match hint % 4 with
  | 0 => mismatch g ws (val % 64) ((val/64)%64)
  | 1 => match (get nodes val) with
    | some a => (nv a == vID) && (nk a == k) && (ns a == ws)
    | none => false
  | 2 =>
    let j := val % 1024
    if j < vID then
      match (get views j) with
      | some v => quickCut v g k ws (val/1024)
      | none => false
    else false
  | _ => (k == 0 && ws.toFinset != {g}) || decide (k+1 < ws.toFinset.card)

theorem checkHint_sound {views : Table View} {nodes : Table Node} {vID : Nat} {g : Word}
    {k : Nat} {ws : List Word} {h : Nat}
    (known : ∀ i < vID, ∀ v, (get views i) = some v → ViewOK v)
    (closed : ∀ (i : Nat) (a : Node), (get nodes i) = some a → nv a = vID → nk a = k →
      ¬ CoreSigned.live signedOps g k (ns a).toFinset)
    (ok : checkHint views nodes vID g k ws h = true) : ¬ CoreSigned.live signedOps g k ws.toFinset := by
  simp only [checkHint] at ok
  split at ok
  · exact mismatch_sound (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) ok k
  · split at ok <;> try contradiction
    rename_i a ha
    simp only [Bool.and_eq_true,beq_iff_eq] at ok
    exact ok.2 ▸ closed _ a ha ok.1.1 ok.1.2
  · split at ok <;> try contradiction
    rename_i lt
    split at ok <;> try contradiction
    rename_i v hv
    exact quickCut_sound (known _ lt _ hv) ok
  · simp only [Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,bne_iff_ne,decide_eq_true_eq] at ok
    intro h
    rcases ok with ⟨rfl,ne⟩|wide
    · exact ne h
    · exact (Nat.not_lt_of_ge (CoreSigned.live_card h)) wide

def scanFrom {α : Type} (f : Nat → α → Bool) : Nat → List α → Bool
  | _, [] => true
  | i, x::xs => f i x && scanFrom f (i+1) xs

theorem scanFrom_sound {α : Type} (f : Nat → α → Bool) {i : Nat} {xs : List α}
    (ok : scanFrom f i xs = true) {x : α} (hx : x ∈ xs) : ∃ j, f j x = true := by
  induction xs generalizing i with
  | nil => simp at hx
  | cons a xs ih =>
    have parts := Bool.and_eq_true_iff.mp ok
    rcases List.mem_cons.mp hx with rfl|hm
    · exact ⟨_,parts.1⟩
    · exact ih parts.2 hm

def evalNode (views : Table View) (nodes : Table Node) (a : Node) : Bool :=
  match (get views (nv a)) with
  | none => false
  | some v => decide (ns a).Nodup && (ns a != [vg v]) &&
    match nk a with
    | 0 => true
    | k+1 => scanFrom (fun i ws => checkHint views nodes (nv a) (vg v) k ws (nh a i)) 0
               (children k (ns a))

def evalRoot (views : Table View) (nodes : Table Node) (i : Nat) (v : View) : Bool :=
  scanFrom (fun q ws => checkHint views nodes i (vg v) (vk v) ws (vh v q)) 0 (vs v).sublists

theorem view_from_earlier (views : Table View) (nodes : Table Node) (vID : Nat) (v : View)
    (hv : (get views vID) = some v)
    (earlier : ∀ i < vID, ∀ w, (get views i) = some w → ViewOK w)
    (hroots : evalRoot views nodes vID v = true)
    (hnodes : ∀ (i : Nat) (a : Node), (get nodes i) = some a → evalNode views nodes a = true) :
    ViewOK v := by
  have closed (k : Nat) : ∀ (i : Nat) (a : Node), (get nodes i) = some a → nv a = vID → nk a = k →
      ¬ CoreSigned.live signedOps (vg v) k (ns a).toFinset := by
    induction k with
    | zero =>
      intro i a found owner fuel h
      have ok := hnodes i a found
      simp only [evalNode,owner,hv,fuel,Bool.and_true,Bool.and_eq_true,decide_eq_true_eq,bne_iff_ne] at ok
      exact ok.2 (singleton_list ok.1 h)
    | succ k ih =>
      intro i a found owner fuel
      have ok := hnodes i a found
      simp only [evalNode,owner,hv,fuel,Bool.and_eq_true,decide_eq_true_eq,bne_iff_ne] at ok
      apply step_no _ _ _ ok.1.1 ok.1.2
      intro ws hm
      obtain ⟨j,good⟩ := scanFrom_sound _ ok.2 hm
      exact checkHint_sound earlier ih good
  intro build_
  classical
  obtain ⟨S, sub, path⟩ := CoreSigned.compress build_
  let ws := (vs v).filter (· ∈ S)
  have eq : ws.toFinset = S := by
    ext w
    simp only [ws,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (sub hw)
  obtain ⟨q,hq⟩ := scanFrom_sound _ hroots (show ws ∈ (vs v).sublists from
    List.mem_sublists.mpr (List.filter_sublist ..))
  exact checkHint_sound earlier (closed _) hq (eq.symm ▸ path)

theorem whole_sound (views : Table View) (nodes : Table Node)
    (allRoots : ∀ (i : Nat) (v : View), (get views i) = some v → evalRoot views nodes i v = true)
    (allNodes : ∀ (i : Nat) (a : Node), (get nodes i) = some a → evalNode views nodes a = true)
    (i : Nat) (v : View) (hv : (get views i) = some v) : ViewOK v := by
  induction i using Nat.strong_induction_on generalizing v with
  | ind i ih => exact view_from_earlier views nodes i v hv ih (allRoots i v hv) allNodes

def checkRootAt (views : Table View) (nodes : Table Node) (i : Nat) : Bool :=
  match (get views i) with
  | some v => evalRoot views nodes i v
  | none => true

def checkNodeAt (views : Table View) (nodes : Table Node) (i : Nat) : Bool :=
  match (get nodes i) with
  | some a => evalNode views nodes a
  | none => true

def passBlock (check : Nat → Bool) (start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => passBlock check start n && check (start+n)

theorem block_at (check : Nat → Bool) {s n i} (ok : passBlock check s n = true)
    (lo : s ≤ i) (hi : i < s+n) : check i = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    have parts := Bool.and_eq_true_iff.mp ok
    by_cases lt : i < s+n
    · exact ih parts.1 lt
    · have eq : i = s+n := by omega
      exact eq ▸ parts.2

theorem merge_blocks {c : Nat → Bool} {s a b : Nat} (x : passBlock c s a = true)
    (y : passBlock c (s+a) b = true) : passBlock c s (a+b) = true := by
  induction b with
  | zero => simpa using x
  | succ b ih =>
    have parts := Bool.and_eq_true_iff.mp y
    change passBlock c s (a+b) && c (s+(a+b)) = true
    exact Bool.and_eq_true_iff.mpr ⟨ih parts.1,by simpa [Nat.add_assoc] using parts.2⟩

theorem certified_view (views : Table View) (nodes : Table Node)
    (roots : passBlock (checkRootAt views nodes) 0 views.1 = true)
    (states : passBlock (checkNodeAt views nodes) 0 nodes.1 = true)
    {i : Nat} {v : View} (hv : (get views i) = some v) : ViewOK v := by
  apply whole_sound views nodes _ _ i v hv
  · intro j w hw
    have hj : j < views.1 := by by_contra! lo; simp [get, Nat.not_lt_of_ge lo] at hw
    have ok := block_at _ roots (i := j) (Nat.zero_le _) (by omega)
    simpa [checkRootAt,hw] using ok
  · intro j a ha
    have hj : j < nodes.1 := by by_contra! lo; simp [get, Nat.not_lt_of_ge lo] at ha
    have ok := block_at _ states (i := j) (Nat.zero_le _) (by omega)
    simpa [checkNodeAt,ha] using ok

end SignedProjection.QFast
namespace SignedProjection.QFast

def rowAt (m : Array Nat) (k : Fin 64) := Fin.ofNat 64 (m[k.val]?.getD 0)
def rowWord (m : Array Nat) (w : Word) : Word :=
  (BitVec.ofBoolListLE (List.ofFn (fun k : Fin 64 => w[(rowAt m k).val]))).cast List.length_ofFn

theorem rowWord_bit (m : Array Nat) (w : Word) (j : Nat) (hj : j < 64) :
    (rowWord m w)[j] = w[(rowAt m ⟨j,hj⟩).val] := by
  rw [← BitVec.getLsbD_eq_getElem hj]
  simp only [rowWord, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj, dite_true, Option.getD_some]

theorem rowWord_and (m : Array Nat) (x y : Word) : rowWord m (x &&& y) = rowWord m x &&& rowWord m y :=
  BitVec.eq_of_getElem_eq fun j hj => by simp only [rowWord_bit,BitVec.getElem_and]
theorem rowWord_or (m : Array Nat) (x y : Word) : rowWord m (x ||| y) = rowWord m x ||| rowWord m y :=
  BitVec.eq_of_getElem_eq fun j hj => by simp only [rowWord_bit,BitVec.getElem_or]
theorem rowWord_not (m : Array Nat) (x : Word) : rowWord m (~~~x) = ~~~rowWord m x :=
  BitVec.eq_of_getElem_eq fun j hj => by simp only [rowWord_bit,BitVec.getElem_not]

def viewMap (m : Array Nat) (v : View) (w : Word) := signedPin (vm v) (va v) (rowWord m w)
theorem viewMap_ops (m : Array Nat) (v : View) {a b c : Word} (hc : c ∈ signedOps a b) :
    viewMap m v c ∈ signedOps (viewMap m v a) (viewMap m v b) := by
  apply signedPin_ops
  simp only [signedOps,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hc ⊢
  rcases hc with rfl|rfl|rfl|rfl
  · exact Or.inl (rowWord_and ..)
  · exact Or.inr (Or.inl (rowWord_or ..))
  · exact Or.inr (Or.inr (Or.inl (by rw [rowWord_and,rowWord_not])))
  · exact Or.inr (Or.inr (Or.inr (by rw [rowWord_and,rowWord_not])))

def viewAliasOK (m : Array Nat) (src dst : View) : Bool :=
  (vg dst != 0) && (viewMap m dst (vg src) == vg dst) && decide (vk src ≤ vk dst) &&
  (vs src).all fun w => viewMap m dst w == 0 || (vs dst).contains (viewMap m dst w)

theorem viewAlias_sound {m : Array Nat} {src dst : View} (yes : ViewOK dst)
    (valid : viewAliasOK m src dst = true) : ViewOK src := by
  simp only [viewAliasOK,Bool.and_eq_true, bne_iff_ne,beq_iff_eq,decide_eq_true_eq] at valid
  obtain ⟨⟨⟨nz,go⟩,le⟩,all⟩ := valid
  intro run
  obtain ⟨S,sub,path⟩ := CoreSigned.compress run
  have ng := fun h : viewMap m dst (vg src) = 0 => nz (go.symm.trans h)
  obtain ⟨j,hj,T,ts,tail⟩ := projected (viewMap m dst) signedOps signedOps _ ng
    (viewMap_ops m dst) zero_left zero_right equal_inputs path
  have supply : T ⊆ (vs dst).toFinset := by
    intro y hy
    obtain ⟨pn,w,hw,rfl⟩ := (avail_mem _).mp (ts hy)
    have h := List.all_eq_true.mp all w (List.mem_toFinset.mp (sub hw))
    simp only [Bool.or_eq_true,beq_iff_eq] at h
    exact List.mem_toFinset.mpr (List.contains_iff_mem.mp (h.resolve_left pn))
  rw [go] at tail
  exact yes (pad_build (by omega) (live_build tail supply))

abbrev AliasTable := Nat → Option (Nat × Array Nat)
def symCheckRoot (aliases : AliasTable) (views : Table View) (nodes : Table Node) (i : Nat) : Bool :=
  match get views i with
  | none => true
  | some v => match aliases i with
    | none => evalRoot views nodes i v
    | some (j,m) => decide (j < i) &&
      match get views j with
      | none => false
      | some w => viewAliasOK m v w

theorem symCertified (aliases : AliasTable) (views : Table View) (nodes : Table Node)
    (roots : passBlock (symCheckRoot aliases views nodes) 0 views.1 = true)
    (states : passBlock (checkNodeAt views nodes) 0 nodes.1 = true)
    {i : Nat} {v : View} (hv : get views i = some v) : ViewOK v := by
  have allNodes (j : Nat) (a : Node) (ha : get nodes j = some a) : evalNode views nodes a = true := by
    have hj : j < nodes.1 := by by_contra! lo; simp [get, Nat.not_lt_of_ge lo] at ha
    have ok := block_at _ states (i := j) (Nat.zero_le _) (by omega)
    simpa [checkNodeAt,ha] using ok
  induction i using Nat.strong_induction_on generalizing v with
  | ind i ih =>
    have hi : i < views.1 := by by_contra! lo; simp [get, Nat.not_lt_of_ge lo] at hv
    have ok := block_at _ roots (i := i) (Nat.zero_le _) (by omega)
    simp only [symCheckRoot,hv] at ok
    cases he : aliases i with
    | none =>
      exact view_from_earlier views nodes i v hv ih (by simpa only [he] using ok) allNodes
    | some x =>
      rcases x with ⟨j,m⟩
      simp only [he,Bool.and_eq_true,decide_eq_true_eq] at ok
      cases hh : get views j with
      | none => simp [hh] at ok
      | some w => exact viewAlias_sound (ih j ok.1 hh) (by simpa only [hh] using ok.2)

end SignedProjection.QFast


namespace LowerSymSix
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.and,[0,1]⟩, ⟨.and,[2,5]⟩, ⟨.and,[3,4]⟩, ⟨.or,[0,1]⟩, ⟨.or,[2,5]⟩, ⟨.and,[8,9]⟩, ⟨.or,[7,11]⟩, ⟨.or,[3,4]⟩, ⟨.and,[6,13]⟩, ⟨.and,[10,8]⟩, ⟨.or,[14,15]⟩, ⟨.and,[12,16]⟩],17⟩

theorem size : witness.size = 12 := rfl

theorem monotone : Monotone2 witness := by
  simp [Monotone2,witness]

set_option maxRecDepth 16000 in
theorem correct : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) =
    Nat.testBit (4269834240 * 2 ^ 32 + 3892314112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel

end LowerSymSix

namespace Direct64
open PEqualNP.CircuitLowerBounds SignedProjection
abbrev W := BitVec 64
abbrev basicOps (a b : W) := signedOps a b
abbrev goal : W := ~~~0xfe808000e8000000
open CoreSigned (build)
def tableB (x : Fin 6 → Bool) :=
  Nat.testBit (4269834240 * 2 ^ 32 + 3892314112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  · change reachable av (BitVec.allOnes 64 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 64)
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
  · exact add _ (by simp [basicOps,SignedProjection.signedOps] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,SignedProjection.signedOps] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,SignedProjection.signedOps] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,SignedProjection.signedOps] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

set_option maxRecDepth 100000 in
theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 64) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

set_option maxRecDepth 100000 in
private theorem read_bit (w : List W) (i : ℕ) (k : Fin 64) :
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
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 64) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#64)[k.val] = false; simp
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


def cols : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

theorem sample64 : ∀ k : Fin 64, tableB (fun i => (cols.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by
  decide +kernel

theorem zero_open (k : ℕ) {t : W} (av : Finset W) (hz : ∀ u ∈ av, u.getLsbD 0 = false)
    (h : build basicOps t k av) : t.getLsbD 0 = false := by
  induction k generalizing av with
  | zero => exact hz t h
  | succ k ih =>
    rcases h with skip | ⟨a,ha,b,hb,_,z,hop,tail⟩
    · exact ih av hz skip
    · apply ih (insert z av) _ tail
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl|hu
      · simp only [basicOps,signedOps,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hop
        rcases hop with rfl|rfl|rfl|rfl <;> simp only [BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,hz a ha,hz b hb,Bool.false_and,Bool.or_self]
      · exact hz u hu

theorem low (reject : ¬ build basicOps (0xfe808000e8000000 : W) 10 cols.toFinset)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = tableB x) : 10 < binaryCost gs := by
  by_contra! low
  have width : cols.length = 6 := rfl
  have init : ∀ u ∈ cols, holds cols.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 64) :
      (gs.foldl step (cols.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (cols.getD i.val 0)
    have same : List.ofFn x = cols.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < cols.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (cols.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample64 k
  obtain ⟨t, ht, run⟩ := compile gs o hg cols cols.toFinset init evaluate

  have h0 : ∀ u ∈ cols.toFinset, u.getLsbD 0 = false := by
    intro u hu
    simp only [cols,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
  rcases ht with rfl|rfl
  · have odd : goal.getLsbD 0 ≠ false := by decide +kernel
    exact odd (zero_open _ _ h0 run)
  · apply reject
    apply pad_build low
    exact run
end Direct64

namespace LowerSymSix
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem finish
    (reject : ¬ CoreSigned.build SignedProjection.signedOps (0xfe808000e8000000 : BitVec 64) 10 Direct64.cols.toFinset) :
∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4269834240 * 2 ^ 32 + 3892314112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4269834240 * 2 ^ 32 + 3892314112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  rintro s ⟨C, hg, hs, he⟩
  by_cases neg : ∃ g ∈ C.gates, g.op = .not
  · obtain ⟨g, hm, op⟩ := neg
    have lo := Direct64.low reject C.gates C.output hg he
    have proper : Direct64.binaryCost C.gates < C.gates.length := by
      apply List.length_filter_lt_length_iff_exists.mpr
      exact ⟨g, hm, by simp [Direct64.isBinary, op]⟩
    have cap : C.gates.length ≤ s := hs
    exact ⟨witness, monotone, by rw [size]; omega, correct⟩
  · refine ⟨C, ?_, hs, he⟩
    intro g hm
    obtain ⟨hop, hin⟩ := hg g hm
    refine ⟨?_, hin⟩
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (neg ⟨g, hm, h⟩).elim

end LowerSymSix


namespace SignedProjection

def ew0 : Word := 0x88000000

def ew1 : Word := 0xa0000000

def ew2 : Word := 0xaa000000

def ew3 : Word := 0xaa00aa00

def ew4 : Word := 0xaaaa0000

def ew5 : Word := 0xc0000000

def ew6 : Word := 0xcc000000

def ew7 : Word := 0xcc00cc00

def ew8 : Word := 0xcccc0000

def ew9 : Word := 0xf0000000

def ew10 : Word := 0xf000f000

def ew11 : Word := 0xf0f00000

def ew12 : Word := 0xff000000

def ew13 : Word := 0x2a002a000000

def ew14 : Word := 0x4c004c000000

def ew15 : Word := 0x700070000000

def ew16 : Word := 0x800080000000

def ew17 : Word := 0x880000008800

def ew18 : Word := 0x880088000000

def ew19 : Word := 0xa0000000a000

def ew20 : Word := 0xa000a0000000

def ew21 : Word := 0xaa0000000000

def ew22 : Word := 0xaa000a000000

def ew23 : Word := 0xaa0022000000

def ew24 : Word := 0xaa002a000000

def ew25 : Word := 0xaa00aa000000

def ew26 : Word := 0xc000c0000000

def ew27 : Word := 0xcc0000000000

def ew28 : Word := 0xcc000c000000

def ew29 : Word := 0xcc0044000000

def ew30 : Word := 0xcc004c000000

def ew31 : Word := 0xcc00cc000000

def ew32 : Word := 0xf00000000000

def ew33 : Word := 0xf00030000000

def ew34 : Word := 0xf00050000000

def ew35 : Word := 0xf00070000000

def ew36 : Word := 0xf000f0000000

def ew37 : Word := 0xff0000000000

def ew38 : Word := 0xff0080000000

def ew39 : Word := 0xff0088000000

def ew40 : Word := 0xff00a0000000

def ew41 : Word := 0xff00c0000000

def ew42 : Word := 0x800800008008000

def ew43 : Word := 0xa0000000a000000

def ew44 : Word := 0xa000a000a000a00

def ew45 : Word := 0xa00a00000000000

def ew46 : Word := 0xa00a0000a00a000

def ew47 : Word := 0xa0a00000a0a0000

def ew48 : Word := 0xc000c000c000c00

def ew49 : Word := 0xc00c0000c00c000

def ew50 : Word := 0xc0c00000c0c0000

def ew51 : Word := 0xf0000000f000000

def ew52 : Word := 0xf000f0000000000

def ew53 : Word := 0xf00f00000000000

def ew54 : Word := 0xf0f000000000000

def ew55 : Word := 0x2000800020008000

def ew56 : Word := 0x2200000022000000

def ew57 : Word := 0x2200220022002200

def ew58 : Word := 0x2200880000000000

def ew59 : Word := 0x2200880022008800

def ew60 : Word := 0x2222000022220000

def ew61 : Word := 0x3000300030003000

def ew62 : Word := 0x3000c0003000c000

def ew63 : Word := 0x3030000030300000

def ew64 : Word := 0x3300000033000000

def ew65 : Word := 0x3300330000000000

def ew66 : Word := 0x3300cc0000000000

def ew67 : Word := 0x3333000000000000

def ew68 : Word := 0x4400440044004400

def ew69 : Word := 0x4400880044008800

def ew70 : Word := 0x4444000044440000

def ew71 : Word := 0x5000500050005000

def ew72 : Word := 0x5000a0005000a000

def ew73 : Word := 0x5050000050500000

def ew74 : Word := 0x5500000055000000

def ew75 : Word := 0x5500550000000000

def ew76 : Word := 0x5500aa0000000000

def ew77 : Word := 0x5555000000000000

def ew78 : Word := 0x8000800008000800

def ew79 : Word := 0x8000800020002000

def ew80 : Word := 0x8000800080008000

def ew81 : Word := 0x8080000080800000

def ew82 : Word := 0x8080808000000000

def ew83 : Word := 0x8080808008080808

def ew84 : Word := 0x8080808020202020

def ew85 : Word := 0x8080808040404040

def ew86 : Word := 0x8080808080808080

def ew87 : Word := 0x8200000082000000

def ew88 : Word := 0x8200820000000000

def ew89 : Word := 0x8200820082008200

def ew90 : Word := 0x8282000082820000

def ew91 : Word := 0x8282828200000000

def ew92 : Word := 0x8400840084008400

def ew93 : Word := 0x8484000084840000

def ew94 : Word := 0x8484848400000000

def ew95 : Word := 0x8800000022000000

def ew96 : Word := 0x8800880000000000

def ew97 : Word := 0x8800880022002200

def ew98 : Word := 0x8800880044004400

def ew99 : Word := 0x8800880088008800

def ew100 : Word := 0x8888000022220000

def ew101 : Word := 0x8888000044440000

def ew102 : Word := 0x8888000088880000

def ew103 : Word := 0x8888888800000000

def ew104 : Word := 0x8888888888888888

def ew105 : Word := 0x9000900090009000

def ew106 : Word := 0x9090000090900000

def ew107 : Word := 0x9090909000000000

def ew108 : Word := 0x9900990000000000

def ew109 : Word := 0x9999000000000000

def ew110 : Word := 0xa00000000a000000

def ew111 : Word := 0xa000a00000000000

def ew112 : Word := 0xa000a0000a000a00

def ew113 : Word := 0xa000a00050005000

def ew114 : Word := 0xa000a000a000a000

def ew115 : Word := 0xa0a000000a0a0000

def ew116 : Word := 0xa0a0000050500000

def ew117 : Word := 0xa0a00000a0a00000

def ew118 : Word := 0xa0a0a0a000000000

def ew119 : Word := 0xa0a0a0a0a0a0a0a0

def ew120 : Word := 0xa800a800a800a800

def ew121 : Word := 0xaa000000aa000000

def ew122 : Word := 0xaa00aa0000000000

def ew123 : Word := 0xaa00aa0088008800

def ew124 : Word := 0xaa00aa00a000a000

def ew125 : Word := 0xaa00aa00aa00aa00

def ew126 : Word := 0xaaaa000000000000

def ew127 : Word := 0xaaaa0000aaaa0000

def ew128 : Word := 0xaaaaaaaa00000000

def ew129 : Word := 0xaaaaaaaaaaaaaaaa

def ew130 : Word := 0xc000c0000c000c00

def ew131 : Word := 0xc000c00030003000

def ew132 : Word := 0xc000c000c000c000

def ew133 : Word := 0xc0c000000c0c0000

def ew134 : Word := 0xc0c0000030300000

def ew135 : Word := 0xc0c00000c0c00000

def ew136 : Word := 0xc0c0c0c000000000

def ew137 : Word := 0xc0c0c0c0c0c0c0c0

def ew138 : Word := 0xcc000000cc000000

def ew139 : Word := 0xcc00cc0000000000

def ew140 : Word := 0xcc00cc00cc00cc00

def ew141 : Word := 0xcccc000000000000

def ew142 : Word := 0xcccc0000cccc0000

def ew143 : Word := 0xcccccccc00000000

def ew144 : Word := 0xcccccccccccccccc

def ew145 : Word := 0xea00ea00c000c000

def ew146 : Word := 0xec00ec00a000a000

def ew147 : Word := 0xf0000000f0000000

def ew148 : Word := 0xf000f00000000000

def ew149 : Word := 0xf000f000f000f000

def ew150 : Word := 0xf0f0000000000000

def ew151 : Word := 0xf0f00000f0f00000

def ew152 : Word := 0xf0f0f0f000000000

def ew153 : Word := 0xf0f0f0f0f0f0f0f0

def ew154 : Word := 0xf800f80088008800

def ew155 : Word := 0xff00000000000000

def ew156 : Word := 0xff000000ff000000

def ew157 : Word := 0xff00ff0000000000

def ew158 : Word := 0xff00ff00ff00ff00

def ew159 : Word := 0xffff000000000000

def ew160 : Word := 0xffff0000ffff0000

def ew161 : Word := 0xffffffff00000000

def labelsBlock0 : Array Nat := #[
  0x1b64,
  0x1d64,
  0x1b2c,
  0x1b68,
  0x102a,
  0x3964,
  0x1b4c,
  0x2f3c,
  0x1e68,
  0x1d70,
  0x1e70,
  0x1d34,
  0x103e,
  0x2fac,
  0x2fb4,
  0x1bac
]

def labelsBlock1 : Array Nat := #[
  0x1b60,
  0x2fb8,
  0x1d60,
  0x2f9c,
  0x1e60,
  0x1d54,
  0x3a68,
  0x104a,
  0x1036,
  0x103a,
  0x379c,
  0x1e38,
  0x1db4,
  0x1002,
  0x1b24,
  0x109a
]

def labelsBlock2 : Array Nat := #[
  0x1d24,
  0x10a2,
  0x1056,
  0x1eb8,
  0x3924,
  0x1006,
  0x1e58,
  0x1032,
  0x1b28,
  0x10ae,
  0x1046,
  0x10b6,
  0x3c70,
  0x100a,
  0x1082,
  0x1b0c
]

def labelsBlock3 : Array Nat := #[
  0x108a,
  0x39a4,
  0x2f2c,
  0x2f34,
  0x375c,
  0x39e0,
  0x3ae0,
  0x3ce0,
  0x1b44,
  0x3960,
  0x3a60,
  0x3c60,
  0x100e,
  0x1d44,
  0x10c2,
  0x1b48
]

def labelsBlock4 : Array Nat := #[
  0x1096,
  0x1ba8,
  0x1ba4,
  0x1da4,
  0x109e,
  0x102e,
  0x10aa,
  0x10a6,
  0x2f1c,
  0x371c,
  0x1052,
  0x3944,
  0x4100aa,
  0x4200aa,
  0x4300aa,
  0x4210aa
]

def labelsBlock5 : Array Nat := #[
  0x4310aa,
  0x4320aa,
  0x1062,
  0x37d4,
  0x1086,
  0x37cc,
  0x2f38,
  0x1108100b6,
  0x1108100c2,
  0x1104200b6,
  0x1104200c2,
  0x1084400b6,
  0x1084400c2,
  0x1ea8,
  0x4100b6,
  0x4200b6
]

def labelsBlock6 : Array Nat := #[
  0x4400b6,
  0x4210b6,
  0x4410b6,
  0x4420b6,
  0x1e28,
  0x3a28,
  0x4100c2,
  0x4200c2,
  0x4400c2,
  0x37d8,
  0x4210c2,
  0x4410c2,
  0x4420c2,
  0x431036,
  0x430036,
  0x410036
]

def labelsBlock7 : Array Nat := #[
  0x10c6,
  0x106a,
  0x1b20,
  0x1db0,
  0x1eb0,
  0x107a,
  0x41009a,
  0x43009a,
  0x43109a,
  0x10b2,
  0x1066,
  0x2f60,
  0x2fa4,
  0x1f3c,
  0x3cb0,
  0x3aa8
]

def labelsBlock8 : Array Nat := #[
  0x1042,
  0x43002e,
  0x43102e,
  0x43202e,
  0x1072,
  0x2f64,
  0x1d30,
  0x1e30,
  0x4100a2,
  0x4300a2,
  0x4310a2,
  0x10ba,
  0x1b04,
  0x2f68,
  0x101e,
  0x1022
]

def labelsBlock9 : Array Nat := #[
  0x1026,
  0x41002e,
  0x104e,
  0x62004e,
  0x42002e,
  0x620042,
  0x42102e,
  0x621042,
  0x1f5c,
  0x430032,
  0x4100a6,
  0x430082,
  0x41009e,
  0x1e48,
  0x41008a,
  0x430096
]

def labelsBlock10 : Array Nat := #[
  0x3a48,
  0x1e20,
  0x1d20,
  0x2f24,
  0x1b00,
  0x1d,
  0x2f70,
  0x25,
  0x9,
  0x19,
  0x49,
  0x45,
  0x81,
  0x7d,
  0x4100ae,
  0x70205a
]

def labelsBlock11 : Array Nat := #[
  0x4200ae,
  0x71205a,
  0x73205a,
  0x4210ae,
  0x71204e,
  0x73204e,
  0x732042,
  0x11d,
  0x121,
  0x105e,
  0x12d,
  0x106e,
  0x141,
  0x10be,
  0x370c,
  0x2f0c
]

def labelsBlock12 : Array Nat := #[
  0x1d04,
  0x1f64,
  0x1fac,
  0x2fa8,
  0x21,
  0x29,
  0x2d,
  0x31,
  0x2fb0,
  0x4d,
  0x51,
  0x55,
  0x65,
  0x69,
  0x85,
  0x89
]

def labelsBlock13 : Array Nat := #[
  0x99,
  0x1f2c,
  0x3b2c,
  0x3bac,
  0x3d34,
  0x3db4,
  0x1016,
  0x1012,
  0x410042,
  0xed,
  0x41004e,
  0xf9,
  0x105,
  0x43004e,
  0x430042,
  0x41005a
]

def labelsBlock14 : Array Nat := #[
  0x43005a,
  0x431042,
  0x43105a,
  0x43104e,
  0x105a,
  0x1d50,
  0x1e50,
  0x125,
  0x131,
  0x139,
  0x108e,
  0x3904,
  0x3704,
  0x3714,
  0x2f04,
  0x2f14
]

def labelsBlock15 : Array Nat := #[
  0x2f20,
  0x2f28,
  0x2f30,
  0x1e00,
  0x1d00,
  0x1b40,
  0x5,
  0x1f68,
  0x15,
  0x1ba0,
  0x1da0,
  0x1ea0,
  0xd,
  0x11,
  0x1fb4,
  0x41
]

def labelsBlock16 : Array Nat := #[
  0x39,
  0x3d,
  0x5d,
  0x61,
  0x1fb8,
  0x79,
  0x71,
  0x75,
  0x91,
  0x95,
  0xa1,
  0xa5,
  0x35,
  0x59,
  0x6d,
  0x8d
]

def labelsBlock17 : Array Nat := #[
  0x9d,
  0xa9,
  0x1b3c,
  0x1d3c,
  0x1f34,
  0x3ba4,
  0x3da4,
  0xb1,
  0xb5,
  0xb9,
  0xbd,
  0xc1,
  0xc5,
  0xc9,
  0xcd,
  0xd1
]

def labelsBlock18 : Array Nat := #[
  0xd5,
  0xd9,
  0xdd,
  0xe9,
  0x7010aa,
  0x6010aa,
  0xf5,
  0x7020aa,
  0x6020aa,
  0x101,
  0x7030aa,
  0x6030aa,
  0x7120aa,
  0x6120aa,
  0x7130aa,
  0x6130aa
]

def labelsBlock19 : Array Nat := #[
  0x7230aa,
  0x6230aa,
  0xf1,
  0xfd,
  0x109,
  0x10d,
  0x111,
  0x115,
  0x7010b6,
  0x6010b6,
  0x1076,
  0x7020b6,
  0x6020b6,
  0x7040b6,
  0x6040b6,
  0x7120b6
]

def labelsBlock20 : Array Nat := #[
  0x6120b6,
  0x7140b6,
  0x6140b6,
  0x107e,
  0x1092,
  0x7240b6,
  0x6240b6,
  0x129,
  0x135,
  0x13d,
  0x145,
  0x149,
  0x14d,
  0x1,
  0xad,
  0x101a
]

def labelsBlock21 : Array Nat := #[
  0xe1,
  0xe5,
  0x3c20,
  0x3a20,
  0x3920,
  0x119,
  0x3c00,
  0x3a00,
  0x3900,
  0x3700,
  0x3708,
  0x3710,
  0x3718,
  0x2f00,
  0x2f08,
  0x2f10
]

def labelsBlock22 : Array Nat := #[
  0x2f18,
  0x1b08,
  0x1e40,
  0x1d40,
  0x151
]

def labelsGet (i : Nat) : Nat :=
  if i < 176 then
    if i < 80 then
      if i < 32 then
        if i < 16 then
          labelsBlock0.getD (i-0) 3
        else
          labelsBlock1.getD (i-16) 3
      else
        if i < 48 then
          labelsBlock2.getD (i-32) 3
        else
          if i < 64 then
            labelsBlock3.getD (i-48) 3
          else
            labelsBlock4.getD (i-64) 3
    else
      if i < 128 then
        if i < 96 then
          labelsBlock5.getD (i-80) 3
        else
          if i < 112 then
            labelsBlock6.getD (i-96) 3
          else
            labelsBlock7.getD (i-112) 3
      else
        if i < 144 then
          labelsBlock8.getD (i-128) 3
        else
          if i < 160 then
            labelsBlock9.getD (i-144) 3
          else
            labelsBlock10.getD (i-160) 3
  else
    if i < 272 then
      if i < 224 then
        if i < 192 then
          labelsBlock11.getD (i-176) 3
        else
          if i < 208 then
            labelsBlock12.getD (i-192) 3
          else
            labelsBlock13.getD (i-208) 3
      else
        if i < 240 then
          labelsBlock14.getD (i-224) 3
        else
          if i < 256 then
            labelsBlock15.getD (i-240) 3
          else
            labelsBlock16.getD (i-256) 3
    else
      if i < 320 then
        if i < 288 then
          labelsBlock17.getD (i-272) 3
        else
          if i < 304 then
            labelsBlock18.getD (i-288) 3
          else
            labelsBlock19.getD (i-304) 3
      else
        if i < 336 then
          labelsBlock20.getD (i-320) 3
        else
          if i < 352 then
            labelsBlock21.getD (i-336) 3
          else
            labelsBlock22.getD (i-352) 3

def decodeHints (enc i : Nat) := labelsGet ((enc >>> (i * 9)) % 512)

def localHints (stride dict enc i : Nat) : Nat :=
  let q := (enc >>> (stride*i)) % (2^stride)
  labelsGet ((dict >>> (9*q)) % 512)

def viewsBlock0 : Array View := #[
  ⟨0xff000000,⟨24,by decide⟩,0xe8000000,[ew2,ew6,ew9],3,decodeHints 0xa680c0010008482810⟩,
  ⟨0xaa00aa000000,⟨25,by decide⟩,0x8000a8000000,[ew18,ew20,ew21],3,decodeHints 0x0⟩,
  ⟨0xcc00cc000000,⟨26,by decide⟩,0x8000c8000000,[ew18,ew26,ew27],3,decodeHints 0x0⟩,
  ⟨0xf000f0000000,⟨28,by decide⟩,0x8000e0000000,[ew20,ew26,ew32],3,decodeHints 0x0⟩,
  ⟨0xa00a0000a00a000,⟨13,by decide⟩,0xa00800008000000,[ew42,ew43,ew45],3,decodeHints 0x0⟩,
  ⟨0x2200880022008800,⟨11,by decide⟩,0x2200800020000000,[ew55,ew56,ew58],3,decodeHints 0x0⟩,
  ⟨0x8080808080808080,⟨7,by decide⟩,0x8080800080000000,[ew80,ew81,ew82],3,decodeHints 0x0⟩,
  ⟨0x8200820082008200,⟨9,by decide⟩,0x8200800080000000,[ew80,ew87,ew88],3,decodeHints 0x0⟩,
  ⟨0x8800880022002200,⟨9,by decide⟩,0x8800800020000000,[ew79,ew95,ew96],3,decodeHints 0x0⟩,
  ⟨0xa000a0000a000a00,⟨9,by decide⟩,0xa000800008000000,[ew78,ew110,ew111],3,decodeHints 0x0⟩,
  ⟨0xff00ff00,⟨8,by decide⟩,0xe8000000,[ew3,ew7,ew10,ew12],4,decodeHints 0xe80c0010008482810010a03c72102894272⟩,
  ⟨0xff00ff000000,⟨24,by decide⟩,0x8000e8000000,[ew25,ew31,ew36,ew37],6,localHints 3 0xa703c0600008482810 0xf60688d60688⟩,
  ⟨0x8888888888888888,⟨3,by decide⟩,0x8880800088000000,[ew86,ew99,ew102,ew103],4,decodeHints 0xa78340c06010085e2f038c890bf24af85e2f⟩,
  ⟨0xaa00aa00aa00aa00,⟨9,by decide⟩,0xaa008000a8000000,[ew99,ew114,ew121,ew122],5,decodeHints 0xa8000020001078401e038cc64a312078401e⟩,
  ⟨0xffff0000,⟨16,by decide⟩,0xe8000000,[ew4,ew8,ew11,ew12],4,decodeHints 0x0⟩,
  ⟨0xf000f000f000f00,⟨8,by decide⟩,0xe00000008000000,[ew44,ew48,ew51,ew52],4,decodeHints 0x0⟩
]

def viewsBlock1 : Array View := #[
  ⟨0xf00f0000f00f000,⟨12,by decide⟩,0xe00800008000000,[ew46,ew49,ew51,ew53],6,decodeHints 0x0⟩,
  ⟨0xf0f00000f0f0000,⟨16,by decide⟩,0xe00000008000000,[ew47,ew50,ew51,ew54],4,decodeHints 0x0⟩,
  ⟨0x3300330033003300,⟨8,by decide⟩,0x3200000020000000,[ew57,ew61,ew64,ew65],4,decodeHints 0x0⟩,
  ⟨0x3300cc003300cc00,⟨10,by decide⟩,0x3200800020000000,[ew59,ew62,ew64,ew66],6,decodeHints 0x0⟩,
  ⟨0x3333000033330000,⟨16,by decide⟩,0x3200000020000000,[ew60,ew63,ew64,ew67],4,decodeHints 0x0⟩,
  ⟨0x5500550055005500,⟨8,by decide⟩,0x5400000040000000,[ew68,ew71,ew74,ew75],4,decodeHints 0x0⟩,
  ⟨0x5500aa005500aa00,⟨9,by decide⟩,0x5400800040000000,[ew69,ew72,ew74,ew76],6,decodeHints 0x0⟩,
  ⟨0x5555000055550000,⟨16,by decide⟩,0x5400000040000000,[ew70,ew73,ew74,ew77],4,decodeHints 0x0⟩,
  ⟨0x8282828282828282,⟨1,by decide⟩,0x8280800080000000,[ew86,ew89,ew90,ew91],6,decodeHints 0x0⟩,
  ⟨0x8484848484848484,⟨2,by decide⟩,0x8480800080000000,[ew86,ew92,ew93,ew94],6,decodeHints 0x0⟩,
  ⟨0x8888888822222222,⟨1,by decide⟩,0x8880800020000000,[ew84,ew97,ew100,ew103],6,decodeHints 0x0⟩,
  ⟨0x8888888844444444,⟨2,by decide⟩,0x8880800040000000,[ew85,ew98,ew101,ew103],6,decodeHints 0x0⟩,
  ⟨0x9090909090909090,⟨4,by decide⟩,0x9080800080000000,[ew86,ew105,ew106,ew107],6,decodeHints 0x0⟩,
  ⟨0x9999999900000000,⟨32,by decide⟩,0x9880800000000000,[ew103,ew107,ew108,ew109],6,decodeHints 0x0⟩,
  ⟨0xa0a0a0a00a0a0a0a,⟨1,by decide⟩,0xa080800008000000,[ew83,ew112,ew115,ew118],6,decodeHints 0x0⟩,
  ⟨0xa0a0a0a050505050,⟨4,by decide⟩,0xa080800040000000,[ew85,ew113,ew116,ew118],6,decodeHints 0x0⟩
]

def viewsBlock2 : Array View := #[
  ⟨0xa0a0a0a0a0a0a0a0,⟨5,by decide⟩,0xa0808000a0000000,[ew86,ew114,ew117,ew118],4,decodeHints 0x0⟩,
  ⟨0xaaaa0000aaaa0000,⟨17,by decide⟩,0xaa800000a8000000,[ew102,ew117,ew121,ew126],5,decodeHints 0x0⟩,
  ⟨0xaaaaaaaa00000000,⟨33,by decide⟩,0xaa80800000000000,[ew103,ew118,ew122,ew126],4,decodeHints 0x0⟩,
  ⟨0xc0c0c0c00c0c0c0c,⟨2,by decide⟩,0xc080800008000000,[ew83,ew130,ew133,ew136],6,decodeHints 0x0⟩,
  ⟨0xc0c0c0c030303030,⟨4,by decide⟩,0xc080800020000000,[ew84,ew131,ew134,ew136],6,decodeHints 0x0⟩,
  ⟨0xc0c0c0c0c0c0c0c0,⟨6,by decide⟩,0xc0808000c0000000,[ew86,ew132,ew135,ew136],4,decodeHints 0x0⟩,
  ⟨0xcc00cc00cc00cc00,⟨10,by decide⟩,0xcc008000c8000000,[ew99,ew132,ew138,ew139],5,decodeHints 0x0⟩,
  ⟨0xcccccccc00000000,⟨34,by decide⟩,0xcc80800000000000,[ew103,ew136,ew139,ew141],4,decodeHints 0x0⟩,
  ⟨0xf000f000f000f000,⟨12,by decide⟩,0xf0008000e0000000,[ew114,ew132,ew147,ew148],5,decodeHints 0x0⟩,
  ⟨0xf0f0f0f000000000,⟨36,by decide⟩,0xf080800000000000,[ew118,ew136,ew148,ew150],4,decodeHints 0x0⟩,
  ⟨0xff000000ff000000,⟨24,by decide⟩,0xfe000000e8000000,[ew121,ew138,ew147,ew155],6,decodeHints 0x0⟩,
  ⟨0xff00ff0000000000,⟨40,by decide⟩,0xfe00800000000000,[ew122,ew139,ew148,ew155],5,decodeHints 0x0⟩,
  ⟨0xaaaaaaaaaaaaaaaa,⟨1,by decide⟩,0xaa808000a8000000,[ew104,ew119,ew125,ew127,ew128],7,decodeHints 0xa88000200030e07a3801078401e17a31808c038cc64a3243bd7eee24bb57cec75a31808c⟩,
  ⟨0xff00ff00ff00ff00,⟨8,by decide⟩,0xfe008000e8000000,[ew125,ew140,ew149,ew156,ew157],8,decodeHints 0xaa80c0010008482810010a03c721028942720395866f2193c546f012552a672a92894272⟩,
  ⟨0xcccccccccccccccc,⟨2,by decide⟩,0xcc808000c8000000,[ew104,ew137,ew140,ew142,ew143],7,decodeHints 0x0⟩,
  ⟨0xf0f0f0f0f0f0f0f0,⟨4,by decide⟩,0xf0808000e0000000,[ew119,ew137,ew149,ew151,ew152],7,decodeHints 0x0⟩
]

def viewsBlock3 : Array View := #[
  ⟨0xffff0000ffff0000,⟨16,by decide⟩,0xfe800000e8000000,[ew127,ew142,ew151,ew156,ew159],8,decodeHints 0x0⟩,
  ⟨0xffffffff00000000,⟨32,by decide⟩,0xfe80800000000000,[ew128,ew143,ew152,ew157,ew159],7,decodeHints 0x0⟩,
  ⟨0xffffffffffffffff,⟨0,by decide⟩,0xfe808000e8000000,[ew129,ew144,ew153,ew158,ew160,ew161],10,decodeHints 0xb200c0010008482810030fc70f51ed8ec4f5010a03c7210289427217d8518a4603d1e6a40395866f2193c546f024581df5f5fd79dd5d24d71db5b5f569d95975d62aea4ab3d1e6a4⟩
]

def viewsGet (i : Nat) : Option View :=
  if i < 32 then
    if i < 16 then
      viewsBlock0[(i-0)]?
    else
      viewsBlock1[(i-16)]?
  else
    if i < 48 then
      viewsBlock2[(i-32)]?
    else
      viewsBlock3[(i-48)]?

def nodesBlock0 : Array Node := #[
  ⟨0,3,[ew2,ew6,ew9],localHints 4 0x14090041010018001409 0x258168155262367057066353024314322010⟩,
  ⟨11,3,[ew25,ew31,ew36,ew38],decodeHints 0x83c86010007084000a05010000188c8203090480203080400009⟩,
  ⟨11,4,[ew16,ew25,ew31,ew36,ew37],decodeHints 0x20f21804001c2100028140400006232080c24120080c2010000243a0f7b03c1a01070002203⟩,
  ⟨11,4,[ew15,ew25,ew31,ew36,ew37],localHints 4 0x184426088c82f7080701e01050001203 0x65d526c22b320a900810772165654432321010⟩,
  ⟨11,4,[ew25,ew31,ew36,ew37,ew39],localHints 4 0xe0341ec2001082803089042401040281c09 0xfd4ee44dc4bb1221a299348870076055430210⟩,
  ⟨11,3,[ew25,ew31,ew35,ew37],decodeHints 0x83c86010007084000a05010000188c8203090480203080400009⟩,
  ⟨11,4,[ew0,ew25,ew31,ew36,ew37],decodeHints 0x20d21804141c3a028281404004122339824241200820120a070241e0f7c0047801000000603⟩,
  ⟨11,3,[ew18,ew20,ew26,ew37],localHints 4 0x1f60f7d071f214128485a10 0x489428722432065004300210⟩,
  ⟨11,4,[ew18,ew20,ew31,ew36,ew37],localHints 4 0x17428a5079cc240a0e104103c080245a03 0x5be587b8dd5c2ba299281207600540330210⟩,
  ⟨11,3,[ew2,ew6,ew18,ew36],decodeHints 0x3d9ed4c010a0501001000003a0a0904802080180c3a09048284a09⟩,
  ⟨11,4,[ew2,ew18,ew31,ew36,ew37],decodeHints 0x834ba010529ce80a0a05010010e88c2223618041a01000001e09090480208048285a090180c3a09⟩,
  ⟨11,4,[ew18,ew25,ew26,ew36,ew37],localHints 4 0x219d02823078494a090e108023c050940010 0x5bf53be3dd8cb8aa59832817611541132100⟩,
  ⟨11,4,[ew6,ew18,ew25,ew36,ew37],decodeHints 0x834860104a9ce6090904802080e8701c1c3e0041a010180c1e0a0a0501001050244a09000003a0a⟩,
  ⟨11,5,[ew18,ew25,ew31,ew36,ew37],localHints 5 0x43638518cc511849880854bf41e1c7e0f01aa8008280025168741203 0x761d2d6a5983b4e669aec60dad330c3858c7b1a10a9ce168693991ad0cc243c830904e78c2012046631084135af631cd6898c5a52a39d494a0e7210a23148300820⟩,
  ⟨11,4,[ew14,ew25,ew31,ew36,ew37],localHints 4 0x21b0446410903c3808008000609 0x36b36565a34319817731011065654343221010⟩,
  ⟨11,4,[ew25,ew31,ew36,ew37,ew40],localHints 4 0x7804860e0e3f82809089cc100d01840000a 0xffee4554d51cc11ba199513873376335432210⟩
]

def nodesBlock1 : Array Node := #[
  ⟨11,3,[ew25,ew30,ew36,ew37],decodeHints 0x83c86010007084000a05010000188c8203090480203080400009⟩,
  ⟨11,4,[ew1,ew25,ew31,ew36,ew37],decodeHints 0x100f2e820000e2100028140400006232080c06080680c201000028380f00805fe00168001203⟩,
  ⟨11,3,[ew2,ew9,ew20,ew31],localHints 4 0x1ec280108000148d0e8204a03 0xaa4699268832776504300210⟩,
  ⟨11,4,[ew2,ew20,ew31,ew36,ew37],decodeHints 0x42a8ba0800038e8000a05010000e88c222300805900007000820301820780308040000a018243a03⟩,
  ⟨11,4,[ew20,ew25,ew26,ew31,ew37],decodeHints 0x7084000403cba080a05006232080c20100029406081280c020f218040200168000208128042412⟩,
  ⟨11,4,[ew9,ew20,ew25,ew31,ew37],decodeHints 0x38840001aa8820308040000a0e83c1a0f3e0001a000480cba080a05010000400c4a03008043a08⟩,
  ⟨11,5,[ew20,ew25,ew31,ew36,ew37],localHints 5 0x32cba420a329924111841880a55c04380f04006002d072a000251e0243a03 0xb6af4c60db95b165614ed69d982b4a55de03bc16b2d8a0602b39919404c002006b5908421640848052c6100b5af631cd6858c211415a9273a0a541ce62948310400⟩,
  ⟨11,4,[ew25,ew29,ew31,ew36,ew37],localHints 4 0x690c840f0e0284673090041010000242203 0x6fe63bd33653cc9b5656a32982776544322100⟩,
  ⟨11,4,[ew25,ew31,ew34,ew36,ew37],localHints 4 0x218701e0807108464109004220901840000a 0x6df6ed9dc61ba1160110013983776335432210⟩,
  ⟨11,4,[ew2,ew6,ew25,ew31,ew36],localHints 4 0xa6538002223008201c2d0183c4a1c 0x67677676cc5b6767aa891876760540332210⟩,
  ⟨11,4,[ew2,ew9,ew25,ew31,ew36],localHints 4 0x8d550042223068f0000a018704a0f 0x5445cc7b5454aa4545891807605454330210⟩,
  ⟨11,5,[ew2,ew25,ew31,ew36,ew37],localHints 5 0xcd06975980e3a05192c51288c1f031e0055608810b400a9050742203 0xa72af8bddd65094571695a51d3288a54486a90d082a8a21082f089ce7a9414202a54508794a118c252c06313da27358a52d085a949420e529863314a418c4200820⟩,
  ⟨11,4,[ew13,ew25,ew31,ew36,ew37],localHints 4 0x10c38420a03c4601040001403 0x46a42982773265654343212165654343212100⟩,
  ⟨11,4,[ew25,ew31,ew36,ew37,ew41],localHints 4 0x7820ba0a071d01a1111c102401018400009 0xff4e9449d41cb11ba114913883376355432210⟩,
  ⟨11,3,[ew24,ew31,ew36,ew37],decodeHints 0x83c86010007084000a05010000188c8203090480203080400009⟩,
  ⟨11,4,[ew5,ew25,ew31,ew36,ew37],decodeHints 0x20f21804001c2100000010680006112080c24120080c201000024460f0400414008280c4a03⟩
]

def nodesBlock2 : Array Node := #[
  ⟨11,3,[ew6,ew9,ew25,ew26],localHints 4 0xf61201a143a10048045a00 0x996726528827065044030210⟩,
  ⟨11,4,[ew6,ew25,ew26,ew36,ew37],decodeHints 0xab086010e8701c1c0400406113980c24120080c06c80700c8400000047800000283a00080400009⟩,
  ⟨11,4,[ew9,ew25,ew26,ew31,ew37],decodeHints 0x2b084000e83c1a0f0500006112080c20100002406c30680c8601008005a00008203a01090480203⟩,
  ⟨11,5,[ew25,ew26,ew31,ew36,ew37],localHints 5 0x33c86ce210715b07040283a0f2088c781200b285a10003181306128455003 0xbb2f50836d95c16781f16b26173d8e749dab5a5298b9d58428e746104a6715ad2d944e70400273850781c002d856b0ab5814029d004a007394c500c022084310020⟩,
  ⟨11,4,[ew23,ew25,ew31,ew36,ew37],localHints 4 0x690ce814208401e1c11804100e050001203 0x6fe638d3cc5607b06560aa0399876565432210⟩,
  ⟨11,4,[ew25,ew31,ew33,ew36,ew37],localHints 4 0x1741e010e108280e050448208018400009 0x4de4bdbdcc1ba1994118713653340330032210⟩,
  ⟨11,4,[ew6,ew9,ew25,ew31,ew36],localHints 4 0x42ab0020e068f00003048705a0f 0xbb7a43343443992812343407605543430210⟩,
  ⟨11,5,[ew6,ew25,ew31,ew36,ew37],localHints 5 0xd00690d9ccc089cc24c7168701f091e0215a010e83801081280d5209 0x8722f8bddd641d0739ccf31dce7a946420ca5550813853a4e6e908e21222054408409420180278846102003bda77358a52d085a949420e729cc5208430006210400⟩,
  ⟨11,4,[ew22,ew25,ew31,ew36,ew37],localHints 4 0x1741c420a048121c0788c1a08008001403 0x47e42dc2bb429679aa94212978765433212100⟩,
  ⟨11,4,[ew25,ew28,ew31,ew36,ew37],localHints 4 0x86140503c380d040002241090040609 0x2ad2b9abccb2a9a98272661541332101100110⟩,
  ⟨11,5,[ew9,ew25,ew31,ew36,ew37],localHints 5 0xd0071099ecd0890596101e0701e1d06806162d052b4010a128255603 0xc6316f5b1ad2b4b7c5eedb15852aca779ceb396a503413a4e6d9018002c027884b10220116003c005288e263dcc6b58c5316a49ce829507398a5208430006210400⟩,
  ⟨11,6,[ew25,ew31,ew36,ew37],localHints 5 0x88834871007108381487c38220f20874463c090061a08168404a03004301409 0x72aaadea1066ab972a0a70e03c5eb53de1670ea338d14605543850898d4371204945ad2c60f711a42914b6010b2814a4910428066390262906310020⟩,
  ⟨13,4,[ew80,ew99,ew114,ew121,ew122],localHints 4 0x2410078168e03814fa02068041c00 0xcc647672bb947670aa49028767654543210⟩,
  ⟨13,4,[ew99,ew114,ew120,ew121,ew122],localHints 4 0x483119344023303814040b000341c8e 0xdd6576765c5cbb76a545998876545433210⟩,
  ⟨13,4,[ew17,ew99,ew114,ew121,ew122],localHints 4 0x2419080621e0581c0a02068041c00 0xcc57bb62aa7965608070230656544323210⟩,
  ⟨13,4,[ew56,ew99,ew114,ew121,ew122],localHints 4 0x34864d1890cc3c0e3e0140e0b010041a00 0x3e63dd52c3b3aa569387212656543212100⟩
]

def nodesBlock3 : Array Node := #[
  ⟨13,4,[ew96,ew99,ew114,ew121,ew122],localHints 4 0x24100151e1e0581da602068041c00 0xcca42a32bb740a988470230665454323210⟩,
  ⟨13,4,[ew99,ew114,ew121,ew122,ew123],localHints 4 0xad2188c84000038391e02059f01a01 0xd734434cb40110aa7099348876543432010⟩,
  ⟨13,4,[ew19,ew99,ew114,ew121,ew122],localHints 4 0x24100cc3c31038141602068041c00 0xcc647672b24aa7099480210767654321010⟩,
  ⟨13,4,[ew43,ew99,ew114,ew121,ew122],localHints 4 0x350642019c52260b3e0340a0701004000e 0x8e58dd45c86bb41a8981761545433221010⟩,
  ⟨13,4,[ew99,ew111,ew114,ew121,ew122],localHints 4 0x24480800ed5068143c02058041c00 0xcc6426baa34998484720610554302100110⟩,
  ⟨13,4,[ew99,ew114,ew121,ew122,ew124],localHints 4 0xad418805200e1981c3c02059f01a00 0xd643344cb4aa61934340880776055430210⟩,
  ⟨13,4,[ew2,ew99,ew114,ew121,ew122],localHints 4 0x24194586715188140e0200834000e 0xc75bb53a337995181171321654432321010⟩,
  ⟨13,4,[ew21,ew99,ew114,ew121,ew122],localHints 4 0x120800a1e0581c6202068041c00 0xb942932aa74091088470230665432321010⟩,
  ⟨13,5,[ew99,ew114,ew121,ew122],localHints 5 0x91484483112a4065208fc7a3a206ba3c671c03c6c0b1a8c87804d605a3a300e06c5c0200 0xfa5bdf71fddf1adda5e9d05f9d0db9c0defb85a1b0cf4a8534984e798d29901f1911b1811ef701a06112a580ea40129410e730060310212906310020⟩,
  ⟨44,7,[ew104,ew119,ew125,ew127,ew128],localHints 5 0x49240d05e1a098c8ea201e9546607388143c022a02c70060c14c2a0e069480200 0x5b35c5e21c5e35a5b20c3a21b3df5b3de103a3483dd993a3193a18c3df17a8616a8dd6a8e10a85c158d54585945854a58d8c3c8b338513384a53c90878211791d179210781c05918d5814d5818c5914a39909380a938108398a510060110211106310020⟩,
  ⟨45,5,[ew125,ew140,ew149,ew154,ew156,ew157],localHints 5 0x120c8400d1d0150e0b0005072070b218041b018442401040281c09 0xbde49649924c130b5984ad6092528464d924c5307bc22738646358b4a92839cc02948300820⟩,
  ⟨45,6,[ew99,ew125,ew140,ew148,ew149,ew156,ew157],decodeHints 0x482402808020544080400b0101c0e7e011f8040d008e87416028090e02058502808008282e1f050e472050b0090c020d848240104024441804824146d0201452050102c040b0600442010205e4604000000603⟩,
  ⟨45,7,[ew99,ew125,ew140,ew149,ew156,ew157],localHints 6 0x24188c9b2206c0e90e141b0e42c865786c2435042b852070201498460124d240b440841a17060064a0a00062481f489141203 0x5535ac56b62c0eb5960d36133ca62a68d5aa3cd618a4a58a54d42854a4e89ca4109cd4d31086181235a61236181085965554d35484254884d34924101236e41082a41086db12328a18161819c86219c6181818615554d35417a07c14d37df79e19c29d1816dd18128a19c6db1811811842081861863176186995966996183175965514d35544105544d349141030b34d3ce28a3ce34d30b28a1891870c22071851000c2040⟩,
  ⟨45,5,[ew125,ew140,ew146,ew149,ew156,ew157],localHints 5 0x90766402804661e058501c39038a0041b04034121101840000a 0xb5a695d573a51e95cd737a5e9948c78c5618412f738e10b5a15b1635292819cc31948310820⟩,
  ⟨45,6,[ew114,ew125,ew139,ew140,ew149,ew156,ew157],decodeHints 0x482402808763b16014c8640580800053b0783c020585028080001c0e7f011fc040c04084100e000e47205018a050020d80c106e08040000a018883003020145205058081602008042e000f800080c930101203⟩,
  ⟨45,7,[ew114,ew125,ew140,ew149,ew156,ew157],localHints 6 0x24188ecc8336d879b4141b8e42c285886c2035052c05207020149a4605a5500029402002173b07c1c0c000624e2104a508a03 0x5505ac56b62c0ab59609061010e6181235aa12361810e5965554e954e42948e4d34924102c76286895a82c96189c75875494265474e69474109494d32c73a411b8e42db38e1078c718061819c86219c6181808405554205407a07c04107df79e18018018438e18618619c1dd1806dd1801c719c6db2176186995966996182175965514d35544105544d349141018f18d08138d20c2492ca1c72ca2492081c7185103081000⟩
]

def nodesBlock4 : Array Node := #[
  ⟨45,5,[ew125,ew140,ew145,ew149,ew156,ew157],localHints 5 0x328ec40050b020741e05834140e2b01c50020d8480211018400009 0xbde6855945ad5e8551533a0e8915c5545418410f095c10b5815ad434a507318a31908310820⟩,
  ⟨45,6,[ew122,ew125,ew132,ew140,ew149,ew156,ew157],decodeHints 0xca650b008763b16004402005808743a0b0003c1e0102c00013b8102c290b06c041b01020020a0000c2c6f140a0041b0904802030804000090188830030381c6202188081801108042e000f8001804948102203⟩,
  ⟨45,7,[ew122,ew125,ew140,ew149,ew156,ew157],localHints 6 0x328ec40de1d0b03cdd05851b8285906c240808028132b0b01c9c461880818891083402173b87c1c0400062542908a048a03 0x5525eb55356b0935d709209240d9aa10e5ea40e9a610d5cd54e8e954d4a9a0d8e3a0e4922c75e71099a72c95d71079875494a55478e59074929098e32c772241a3622da71c8473471801801845d71861865554a05407a07c04927df79e18035d19971d19934d1807001991db18069b1801c71996991981960815d65414d35544925544d308149221138e40f34d40f38e20834d20c2492ca1c72ca2492081c7185103081000⟩,
  ⟨45,7,[ew125,ew132,ew140,ew149,ew156,ew157],localHints 6 0x24188ec403a0f2d01629020148c97404b4112c052588ab32b01db816278a004df0d84802211b840001f1b024446f0c0441803 0x4d18ac4eb5ac6ab8a269159130d59630b8aa30b59630d88d4d39694cd46980d9658204512095962078a82075962098894d34674c99679894519a696520920920c34d2082080635966248a26245960638a24df3cf4e14514e13cf81f45121e21d69934d21c31b6992491005976025171025965405004c24524c03d24004514023cf10034e3062ce10634d3002c010624a2001ca1002492061c61000c00421421020c2040040⟩,
  ⟨45,7,[ew125,ew139,ew140,ew149,ew156,ew157],localHints 6 0x24188ec40e10f2d416149781c8c7f060841b2e072088a39028a4585014009c01b4504802db04040001f05024446e0c0440803 0x5125ec52b52c6ab5d76926923cd56a59d5ea3dd55558d5cd51d96950d4a9a0d965a1d4922092092165d72082085144a75099679894929a69652092e42073642072cb2093492232226995e251982052149252182069949205f75d3de34d3de75d04134d21c59b6992491005d85825581025d758054050249350041344049244241010034e3c62ce10634d3002c010624a2001ca1002492061c61000c00421421020c2040040⟩,
  ⟨45,7,[ew125,ew140,ew148,ew149,ew156,ew157],localHints 6 0x24188816d3103918fd3006a0c8a3a0f38c16140b87c1c39028a42c5114009c41b0900442081106022043c040da03003641409 0x5125ec52b52c8ab5d789289234e34e3565d734d34d51476a50e4aaa4e75da694923683678a15e75219655264925269658a14923645a38a138e1c35605995e01d95555835c351949f50375f78349279975d1c331c34139c1c130c3433831c36832196d91d96992032031445d85895581495d758454450949350441344449244941014438f34030f14038e3443041442842092c91492892042041400c61c40461440c3080040⟩,
  ⟨45,8,[ew125,ew140,ew149,ew156,ew157],localHints 6 0x24189146537102001a339b0143c920702c2935149580f340b11850027204436210900666080f8403003004c81409 0x4907a84a75689a779e99055030a5655e17a532155590a78a4a16a348a42388a69a8a14101c35605db7a01db5557c378349b41d48369d70341071b69a1c32193012991c12086032831445565ce4d614e5555044c448e4114843513c44103ce34d14428b30020b14028a2442041400c61c40461440c3080040⟩,
  ⟨50,8,[ew86,ew129,ew144,ew153,ew158,ew160,ew161],localHints 6 0x24920682f0d04c7637100f474360f02c70150a0e46a161406c7e2609020200a048c00e0515064fa024c0181a010b8380022088300803 0x3ccb6f3eb46f3ebb6d3cc44c08a46e0aab6e0aa45108ab4a0aa32c08aaec08a30c0aaaea0884510a84290a845108840808f8a70883270888a208230c0828260882a608882008228a1c54511e44251e44511c54053cf3233c58a33c530c3cf8a20822a108582108528a08282008559f09421f09459608520510045111d71e11d4511007003cf31b3c069b3c030c3cf69a08229908061908028a0826180802170935970932080805801d31551c05151c01451d351308145108241009245108141008f34d08e30c08e34d08230c0822cb08128a0812cb08228a082089081208087086081145084083081000⟩,
  ⟨50,8,[ew103,ew129,ew144,ew153,ew158,ew160,ew161],localHints 6 0x24258bc762c100f4aa3a1b07816380a85072350b0a0363f130481010050240a070c8680413030305c0d0085c1c00110440803 0x4d46c04e3ec04e45104d04d04b46b04c06b04c45104b04b04c36a04b3aa04b34d04c38c047a29048469048a280474473c88673c73673c78613c834d0657e60472e60477df0652cb0446e40634640636db0444443cf3623c48623c434d3cf8610412e00447e00442cb0417df18455e1931de1935551841c404045d05c6dd05c4510406c03cf35a3c065a3c034d3cf6590412d80405d80402cb0415d70c01d60d25560d21c70c05401921141804d41801041924d204105004145004f38e04134d04f38e04134d04130c0412cb04130c0412cb04a2080411c70492080411c7046045041104043042041000⟩,
  ⟨50,8,[ew104,ew129,ew144,ew152,ew153,ew158,ew160,ew161],localHints 6 0x24258bc403d039283413068e90ee60a0d872164306dca26090d4109a1121060050c808b00b0315c2a99060048e270b8b81400200101203 0x494c29470a545124523d4be83afa1450f38fa12b8fa6e3d24a8a6828629551454659142d292b4a41045248e36c28fb0a34d38f3c61ab1d4ad1a69a924aaa6945248ea281cf3c7a2838f3d55671ca2858268949a282015451149215094549245040e3cf14d9053cf38d36266314a8c565988a2852056071d82081471415216a085a51406081149205e7c149245e78e3cf05c7413cf39c71a29b0596c128a6996412016175d82080570411810c514319608c09551454c2425144524934104d249141038f3c234d08f3ce34d2cc2c628a18c24b28a0880891c72482021c21861021440c3002040⟩,
  ⟨50,9,[ew104,ew129,ew144,ew153,ew158,ew160,ew161],localHints 6 0x124903417868273a19211ce201e9547487730506c390b2e50c1b728982435041e4e22903ae00a4a1f008cc0b031782a52138841ab700ce4300a0008a701f0b8ac1203 0x616e3a5766fa636e385566d60d36f94b5e390f56db493e130f55b7613db70d35964b5db5c8b6f3d0d673c8d6dbc4b64b54d53060b5b060b51454d5964ae46f0cb4ef0cb4514ae4d33c86db0e966d3e96db0c86596155960c852c6085960d55140d24d30c846b0c84d30d24513e97ea0c82ea3c87df0e92cb3c16db1a09e83e06db1819e79955966019256015961959241924d30c18a30c14d31928a23e02e11817e13c12cb1a07df0c12411842083c425e3dd6db0dc6593dc6db0da6596155960d75146175960d55140d24d30c24510c24d30d24513d034d0ce2cb3ce34d0cc2cb0ca2470c22071851000c2040⟩,
  ⟨50,8,[ew118,ew129,ew144,ew153,ew158,ew160,ew161],localHints 6 0x24258bc7637160807a3a0f02c70530a85072350b0a0363f130481010050240a070c8680413030301a010b89c1c00110440803 0x4d46c04e3ec04e45104d04d04b46b04c06b04c45104b04b04c36a04b3aa04b34d04c38c0489e90684690689e70484483cf8a63c83663c88a23cf34d0417e50482e50487df0412cb0446e40454640456db0444443c53633c48a33c434d3c58a20602e10447e10442cb0607df28455e29321e29355528420404045d05c6dd05c4510406c03cf35a3c065a3c034d3cf6590412d80405d80402cb0415d72802162925562922082805400d21140c04d40c01040d24d204105004145004f38e04134d04f38e04134d04130c0412cb04130c0412cb04a049041208047145041104046145041104043042041000⟩,
  ⟨50,8,[ew119,ew129,ew143,ew144,ew153,ew158,ew160,ew161],localHints 6 0x24258bc76644e87870141b81c541a09838722c1406c7e263d0406a0a4e08860050c82cb4020a9640c080089d3617001105c0c200240803 0x414c24470914510450354be33af8d450d38d8d0b8d92e350423923320b6752d9e080c514452b0c42c31249141038facc36b30f3ce34d1ca1d551454a6d142a1d2a8741045248e3691cfa4734d38f3c7328627a1830c1e71ca2a611499192495042592445040e8e310d3448e338d3445c414c3055c510c3155621071c052166085951402001141f01e7c041045e78e35d01c74034d39c7002800cc30329b64768061a0071d961800a0175965ca1405800490555145491815144524934104d249141038f3c134d04f3ce34d28a2c130b20920a1c72891881c70450461041851411010c3081000⟩,
  ⟨50,9,[ew119,ew129,ew144,ew153,ew158,ew160,ew161],localHints 6 0x124903417868263b32274e2333d3a03c38298506e390b2e4501b1f898f2101a828ea2903ae80a2a1f02cce020a97c0d3c0c02002521707c1cb70008a7621048305603 0x614e3a5766fa636e385546d40916f94b5e390b56db491e110b5537611db70915144b5db52ce6db0a96742e96db08e6596155b308e53360e5960955140924f208e47208e4d3092451bc76f0c49670bc96dbb8764754952d6075ad6075145495964ab46c0874ec0874514ab4d30873aa2dea6a2de38e087a472c06db19f9e82df6db1809c09955256009256005141959241924630808a30804511928a20803c018438e2c43e12df1e01807a02c01c719f79e2dd6db09c6592dc6db09a6596155960975146175960955140924d30814510814d30924510903cd08138d2cc24908a1c72ca2490881c7185103081000⟩,
  ⟨50,8,[ew128,ew129,ew137,ew144,ew153,ew158,ew160,ew161],localHints 6 0x65500bc76201e8e8581e058e02a1904028a4280d8fc4c121b8406c094f8882c0715068b8020996c0c2e0089d3c17001006004220441803 0x415c12470495550450355bcf3af3d554d38d3d0b8d4ae35040f48f2e9b5b56d6e9a4b54b467b0b42c2e79d14103a5acb36b2e594e34d1d5a99a6a655547a47450a079e81d04119e738d9879661cd34e9651ca1cc2cb30a8445c41555455c51155517df9104247df45040e75d10d34475d38d34a2a310b2cc3221071c02800d55432a14508007e00104117df38d78075e00d34e75d00b7186dc60b2c06c060768065a0071d865800a0175965ca14058028a5015544524934104d249141038f3c134d04f3ce34d04904c2cb3091812cb20920a1c72891881c70450461041851411040c3081000⟩,
  ⟨50,9,[ew128,ew129,ew144,ew153,ew158,ew160,ew161],localHints 6 0x195402f1d8807a551d0b03c0b1c14c2a520a2edd2705c8a0363f130481010050267c180b01c323e0d1a0041330018ea2106ae802711807c1cb80008a7a29088105603 0x956fa6575ba6576db0955950926f90944f90946db0924d20945786525f80925554d45d408dcb72cf6f72cfcb208d6cd58fc3664d57664dc3058f5554f4b7508d4b508db6d4f44920876f32c9cb32c96db087c87589571647c31647555589c304ee4af087b6f0874924eeb6db0786bb1f36ba9f861a473470807001846db2c47289d65666409666405551969651934a40808e40804921938e32c036219e8622de34d1808402de1e01807e02c01c719e7de09d71a0816da6565d70985556585d70965550935140814920815140934922d13cf09034d2d03cf08e34d2cc24908a1c72ca2490881c7185103081000⟩
]

def nodesBlock5 : Array Node := #[
  ⟨50,8,[ew129,ew136,ew144,ew153,ew158,ew160,ew161],localHints 6 0x24258bc7637160807a3a1b07816380a8500e1a098341c390285850020c86c7e063489824010602020000b8281222138440803 0x545ec05c4ec05c5d70540540505eb05b06b05b5d705005005b52a05072a05051405b71b04c9e90685e90689e704c5cc4d38664cc5264cc8614d35140417e504c42504c7df0414100485a40635e40635960485c84d35224c88624c85144d38610414200487e00484100417df2c829e2c631e2c628a2c830804105d0415dd05371c04151405371c0415140416db0414100416db04141004b05a04130c0470590412080405d80425980425d70405804c25154c04954c05144c249204f41104039104041004f38e2c030d2c528d2c530c2c02801c52091c01891c02081c51850400400421020420c2040040⟩,
  ⟨50,9,[ew129,ew137,ew144,ew153,ew158,ew160,ew161],localHints 6 0x124903417868263b100f4744a0f02c701545ba852bc028fa801f044fc420a15aecac5203ba42c2815008d41b1f818c269130480237080002e36049e88018088316e03 0x5d6e3a5766fa5f6e385566d60926f9475e390b56db452e120b55b75d2db7092596475db514d6db08c9f414c6db08d9cd5d5bb308d5b35cdbae095596091b3208d4b208db2c09149214a6db2489f11486db24a9cac155af5cabaf5ca596255bae2514ad08ab2d08a492251b2c08a90a26134d16192b16a6db0a99e71696db0a89e75d55140a65965e65140955960913cf09f49209f3cf0914920a592309f34d26286009f28a7006dd78365d7036db6806405435985c05185c05965435144504930803d30804924503cf08034e14730e14734d08030024728b14020b14028a247207080100143183143103080040⟩,
  ⟨50,9,[ew129,ew143,ew144,ew153,ew158,ew160,ew161],localHints 6 0x90962f1d8807a55381283c0b1c05429420f81c7c1a09ba8420d5e504520e158e40a2c14064046b0d8fc0c6234898f41238805d008080002e0a04aec8818088117003 0x9977a6a863a6a875d0996190957790a75390a775d0955150a7678695a38095659527a2708e73716477716471c08e74e624c3668e67668ec30624659534bb508e57508ebae53455508aaca26175d161af3c9867168ac3168a659258c3025456f08abaf08a555254bae14a32d2483ad14830c24a38a0acaea09f76a698a280a96596a9a280986590949e709f55509f9e70945551669240a538e1659240a338e26286009f28a08075e14371e14375d08070060365b6805db6806596035d75135560804960805555134924403904473103c738e34030024728b14020b14028a247207080100143183143103080040⟩,
  ⟨50,9,[ew129,ew144,ew152,ew153,ew158,ew160,ew161],localHints 6 0x90962f380a8403da30840e3e0d04e8a29068ac741e058e0a6150a5103e0e5e0e40a1614064046c0d8fc0c633489824010602286470c04408ba42040ea030039c1409 0x25977a6af63a6af75d25961925577926e53926e75d25551526e678695bf825565952ebee250c903ec75d32ccb7d989f56906756909e73d86593d49342505742509243d4555273cb126a771698bef2706596b0bef258659254bae26a55526abae2545553edb2b26a41024372932076932071c2437436206686839e86836596209e75255662439262435555259243c33a330142330138e3c34032438433208a03208602437c324475e30a71e30a75d24470460a65b6845db68465960a5d75135562444962445555134923c44113003913004103c43842442c430a34a30a2ca2442041c00c61c40461440c3080040⟩,
  ⟨50,10,[ew129,ew144,ew153,ew158,ew160,ew161],localHints 6 0x1249034178682632a60801a3d2a8ce96050f038163829854294a2b1c00f490b0a0043e0886c7e06159a44cbd09006900845840f2030051c1409 0x515c3252e67252ec305156553d06713edc313ed6593d0c103ed56f3d0baf3d05553edbad30a66c6a992c6a9659aca90a52986a50a56a50a8615295553e77a83ca4283ca79e3e74101c36666a29266a26599439035225635038635035555228613df4203c37a03c34103df79e1c321d30129d1c120870328314465b6935db6936596045c45135565044965045555134923ce4113c43513c44103ce34d14428b30020b14028a2442041400c61c40461440c3080040⟩
]

def nodesGet (i : Nat) : Option Node :=
  if i < 48 then
    if i < 16 then
      nodesBlock0[(i-0)]?
    else
      if i < 32 then
        nodesBlock1[(i-16)]?
      else
        nodesBlock2[(i-32)]?
  else
    if i < 64 then
      nodesBlock3[(i-48)]?
    else
      if i < 80 then
        nodesBlock4[(i-64)]?
      else
        nodesBlock5[(i-80)]?

def fastViews : QFast.Table View := ⟨51,viewsGet⟩

def fastNodes : QFast.Table Node := ⟨85,nodesGet⟩

end SignedProjection


namespace SignedProjection
def aliasMap1 : Array Nat := #[0,32,0,33,0,34,0,35,0,40,0,41,0,42,0,43,0,48,0,49,0,50,0,51,0,56,0,57,0,58,0,59,0,36,0,37,0,38,0,39,0,44,0,45,0,46,0,47,0,52,0,53,0,54,0,55,0,60,0,61,0,62,0,63]
def aliasMap2 : Array Nat := #[0,0,0,0,0,0,0,0,0,17,0,19,0,21,0,23,0,0,0,0,0,0,0,0,0,25,0,27,0,29,0,31,0,0,0,0,0,0,0,0,0,49,0,51,0,53,0,55,0,0,0,0,0,0,0,0,0,57,0,59,0,61,0,63]
def aliasMap3 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,9,11,25,27,45,47,61,63,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap4 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,9,13,25,29,43,47,59,63,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap5 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,9,15,25,31,41,47,57,63,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap6 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,11,15,25,29,43,47,57,61,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap7 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,13,15,25,27,45,47,57,59,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap8 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,31,29,27,25,47,45,43,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap9 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,37,39,45,47,53,55,61,63,0,0,0,0,0,0,0,0,1,3,9,11,17,19,25,27,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap10 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,31,30,29,28,47,46,45,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap11 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,31,30,27,26,47,46,43,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap12 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,35,39,43,47,51,55,59,63,0,0,0,0,0,0,0,0,1,5,9,13,17,21,25,29,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap13 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,33,39,41,47,49,55,57,63,0,0,0,0,0,0,0,0,1,7,9,15,17,23,25,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap14 : Array Nat := #[0,0,0,0,0,0,0,0,16,17,18,19,20,21,22,23,0,0,0,0,0,0,0,0,24,25,26,27,28,29,30,31,0,0,0,0,0,0,0,0,48,49,50,51,52,53,54,55,0,0,0,0,0,0,0,0,56,57,58,59,60,61,62,63]
def aliasMap15 : Array Nat := #[0,0,0,0,0,0,0,0,0,63,0,62,0,61,0,60,0,0,0,0,0,0,0,0,0,47,0,46,0,45,0,44,0,0,0,0,0,0,0,0,0,59,0,58,0,57,0,56,0,0,0,0,0,0,0,0,0,43,0,42,0,41,0,40]
def aliasMap16 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,31,30,29,28,27,26,25,24,0,0,0,0,0,0,0,0,63,62,61,60,59,58,57,56,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap17 : Array Nat := #[0,0,0,0,0,0,0,0,0,12,0,13,0,14,0,15,0,0,0,0,0,0,0,0,0,28,0,29,0,30,0,31,0,0,0,0,0,0,0,0,0,44,0,45,0,46,0,47,0,0,0,0,0,0,0,0,0,60,0,61,0,62,0,63]
def aliasMap18 : Array Nat := #[0,0,0,0,0,0,0,0,0,10,0,11,0,14,0,15,0,0,0,0,0,0,0,0,0,26,0,27,0,30,0,31,0,0,0,0,0,0,0,0,0,42,0,43,0,46,0,47,0,0,0,0,0,0,0,0,0,58,0,59,0,62,0,63]
def aliasMap19 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,41,43,45,47,56,58,60,62,0,0,0,0,0,0,0,0,9,11,13,15,24,26,28,30,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap20 : Array Nat := #[0,0,0,0,0,0,0,0,8,10,12,14,40,42,44,46,0,0,0,0,0,0,0,0,24,26,28,30,56,58,60,62,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap21 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,43,46,47,56,57,60,61,0,0,0,0,0,0,0,0,10,11,14,15,24,25,28,29,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap22 : Array Nat := #[0,0,0,0,0,0,0,0,8,9,12,13,40,41,44,45,0,0,0,0,0,0,0,0,24,25,28,29,56,57,60,61,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap23 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,45,46,47,56,57,58,59,0,0,0,0,0,0,0,0,12,13,14,15,24,25,26,27,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap24 : Array Nat := #[0,0,0,0,0,0,0,0,8,9,10,11,40,41,42,43,0,0,0,0,0,0,0,0,24,25,26,27,56,57,58,59,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap25 : Array Nat := #[0,4,0,5,0,6,0,7,0,12,0,13,0,14,0,15,0,20,0,21,0,22,0,23,0,28,0,29,0,30,0,31,0,36,0,37,0,38,0,39,0,44,0,45,0,46,0,47,0,52,0,53,0,54,0,55,0,60,0,61,0,62,0,63]
def aliasMap26 : Array Nat := #[0,0,0,36,0,0,0,37,0,0,0,44,0,0,0,45,0,0,0,52,0,0,0,53,0,0,0,60,0,0,0,61,0,0,0,38,0,0,0,39,0,0,0,46,0,0,0,47,0,0,0,54,0,0,0,55,0,0,0,62,0,0,0,63]
def aliasMap27 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,15,23,31,39,47,55,63,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap28 : Array Nat := #[0,2,0,3,0,6,0,7,0,10,0,11,0,14,0,15,0,18,0,19,0,22,0,23,0,26,0,27,0,30,0,31,0,34,0,35,0,38,0,39,0,42,0,43,0,46,0,47,0,50,0,51,0,54,0,55,0,58,0,59,0,62,0,63]
def aliasMap29 : Array Nat := #[0,0,0,34,0,0,0,35,0,0,0,42,0,0,0,43,0,0,0,50,0,0,0,51,0,0,0,58,0,0,0,59,0,0,0,38,0,0,0,39,0,0,0,46,0,0,0,47,0,0,0,54,0,0,0,55,0,0,0,62,0,0,0,63]
def aliasMap30 : Array Nat := #[0,0,0,6,0,0,0,7,0,0,0,14,0,0,0,15,0,0,0,22,0,0,0,23,0,0,0,30,0,0,0,31,0,0,0,38,0,0,0,39,0,0,0,46,0,0,0,47,0,0,0,54,0,0,0,55,0,0,0,62,0,0,0,63]
def aliasMap31 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,38,39,46,47,54,55,62,63,0,0,0,0,0,0,0,0,4,5,12,13,20,21,28,29,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap32 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,38,39,46,47,54,55,62,63,0,0,0,0,0,0,0,0,2,3,10,11,18,19,26,27,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap33 : Array Nat := #[0,0,0,33,0,0,0,35,0,0,0,41,0,0,0,43,0,0,0,49,0,0,0,51,0,0,0,57,0,0,0,59,0,0,0,37,0,0,0,39,0,0,0,45,0,0,0,47,0,0,0,53,0,0,0,55,0,0,0,61,0,0,0,63]
def aliasMap34 : Array Nat := #[0,0,0,5,0,0,0,7,0,0,0,13,0,0,0,15,0,0,0,21,0,0,0,23,0,0,0,29,0,0,0,31,0,0,0,37,0,0,0,39,0,0,0,45,0,0,0,47,0,0,0,53,0,0,0,55,0,0,0,61,0,0,0,63]
def aliasMap35 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,37,39,45,47,53,55,61,63,0,0,0,0,0,0,0,0,4,6,12,14,20,22,28,30,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap36 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,48,51,52,55,56,59,60,63,0,0,0,0,0,0,0,0,32,35,36,39,40,43,44,47,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap37 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,36,39,44,47,52,55,60,63,0,0,0,0,0,0,0,0,4,7,12,15,20,23,28,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap38 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,35,39,43,47,51,55,59,63,0,0,0,0,0,0,0,0,2,6,10,14,18,22,26,30,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap39 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,34,39,42,47,50,55,58,63,0,0,0,0,0,0,0,0,2,7,10,15,18,23,26,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap40 : Array Nat := #[0,0,0,0,0,0,0,0,16,18,20,22,48,50,52,54,0,0,0,0,0,0,0,0,24,26,28,30,56,58,60,62,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap41 : Array Nat := #[0,0,0,0,0,0,0,0,16,17,20,21,48,49,52,53,0,0,0,0,0,0,0,0,24,25,28,29,56,57,60,61,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap42 : Array Nat := #[0,0,0,0,0,0,0,0,16,17,18,19,48,49,50,51,0,0,0,0,0,0,0,0,24,25,26,27,56,57,58,59,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap43 : Array Nat := #[0,0,0,0,0,0,0,0,16,17,18,19,20,21,22,23,0,0,0,0,0,0,0,0,24,25,26,27,28,29,30,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def rootAliases : QFast.AliasTable
  | 1 => some (0, aliasMap8)
  | 2 => some (0, aliasMap11)
  | 3 => some (0, aliasMap10)
  | 4 => some (0, aliasMap7)
  | 5 => some (0, aliasMap6)
  | 6 => some (0, aliasMap27)
  | 7 => some (0, aliasMap5)
  | 8 => some (0, aliasMap4)
  | 9 => some (0, aliasMap3)
  | 14 => some (10, aliasMap43)
  | 15 => some (10, aliasMap24)
  | 16 => some (11, aliasMap23)
  | 17 => some (10, aliasMap42)
  | 18 => some (10, aliasMap22)
  | 19 => some (11, aliasMap21)
  | 20 => some (10, aliasMap41)
  | 21 => some (10, aliasMap20)
  | 22 => some (11, aliasMap19)
  | 23 => some (10, aliasMap40)
  | 24 => some (11, aliasMap13)
  | 25 => some (11, aliasMap39)
  | 26 => some (11, aliasMap12)
  | 27 => some (11, aliasMap38)
  | 28 => some (11, aliasMap37)
  | 29 => some (11, aliasMap36)
  | 30 => some (11, aliasMap9)
  | 31 => some (11, aliasMap35)
  | 32 => some (12, aliasMap34)
  | 33 => some (13, aliasMap2)
  | 34 => some (12, aliasMap33)
  | 35 => some (11, aliasMap32)
  | 36 => some (11, aliasMap31)
  | 37 => some (12, aliasMap30)
  | 38 => some (13, aliasMap18)
  | 39 => some (12, aliasMap29)
  | 40 => some (13, aliasMap17)
  | 41 => some (12, aliasMap26)
  | 42 => some (11, aliasMap16)
  | 43 => some (13, aliasMap15)
  | 46 => some (44, aliasMap28)
  | 47 => some (44, aliasMap25)
  | 48 => some (45, aliasMap14)
  | 49 => some (44, aliasMap1)
  | _ => none
end SignedProjection


namespace SignedProjection

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_0 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 16 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_16 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 16 16 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_32 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 32 16 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_48 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 48 3 = true := by decide +kernel

theorem joinRoots_0_0 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 32 = true :=
  @QFast.merge_blocks (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 16 16 blockRoots_0 blockRoots_16

theorem joinRoots_0_32 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 32 19 = true :=
  @QFast.merge_blocks (QFast.symCheckRoot rootAliases fastViews fastNodes) 32 16 3 blockRoots_32 blockRoots_48

theorem joinRoots_1_0 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 51 = true :=
  @QFast.merge_blocks (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 32 19 joinRoots_0_0 joinRoots_0_32

theorem certifiedRoots : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 51 = true := joinRoots_1_0

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 12 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_24 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 24 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_36 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 36 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_48 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 48 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_60 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 60 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_72 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 72 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_84 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 84 1 = true := by decide +kernel

theorem joinNodes_0_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 12 12 blockNodes_0 blockNodes_12

theorem joinNodes_0_24 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 24 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 24 12 12 blockNodes_24 blockNodes_36

theorem joinNodes_0_48 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 48 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 48 12 12 blockNodes_48 blockNodes_60

theorem joinNodes_0_72 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 72 13 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 72 12 1 blockNodes_72 blockNodes_84

theorem joinNodes_1_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 48 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 24 24 joinNodes_0_0 joinNodes_0_24

theorem joinNodes_1_48 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 48 37 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 48 24 13 joinNodes_0_48 joinNodes_0_72

theorem joinNodes_2_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 85 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 48 37 joinNodes_1_0 joinNodes_1_48

theorem certifiedNodes : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 85 = true := joinNodes_2_0

end SignedProjection

namespace SignedProjection
def bMatches (z : Option View) : Bool :=
  match z with
  | none => false
  | some v => vg v == (0xfe808000e8000000 : Word) && vk v == 10 && (vs v).toFinset == Direct64.cols.toFinset

theorem rootNegative : ¬ CoreSigned.build signedOps (0xfe808000e8000000 : BitVec 64) 10 Direct64.cols.toFinset := by
  have shape : bMatches (QFast.get fastViews 50) = true := by decide +kernel
  cases ev : QFast.get fastViews 50 with
  | none => simp [ev, bMatches] at shape
  | some v =>
    have valid := QFast.symCertified rootAliases fastViews fastNodes certifiedRoots certifiedNodes ev
    simp only [ev,bMatches,Bool.and_eq_true,beq_iff_eq] at shape
    change ¬ CoreSigned.build signedOps (vg v) (vk v) (vs v).toFinset at valid
    rwa [shape.1.1,shape.1.2,shape.2] at valid
end SignedProjection
end PEqualNP.Outside.L_meta_12044_aux

open PEqualNP.Outside.L_meta_12044_aux in
theorem PEqualNP.Outside.L_meta_12044 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4269834240 * 2 ^ 32 + 3892314112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4269834240 * 2 ^ 32 + 3892314112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  LowerSymSix.finish SignedProjection.rootNegative
