import PEqualNP.Defs

-- The witness has twelve binary gates. Any circuit with a NOT and fewer gates
-- would have at most ten binary gates even with every negation available for free.
-- Finite signed-circuit certificates below exclude that possibility.
-- Signed-wire search and gate projections adapt the project’s Apache 2.0 proofs.
namespace PEqualNP.Outside.L_meta_12362_aux
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
  ⟨[⟨.and,[0,1]⟩, ⟨.and,[4,5]⟩, ⟨.or,[3,7]⟩, ⟨.or,[0,1]⟩, ⟨.and,[2,9]⟩, ⟨.or,[4,5]⟩, ⟨.and,[8,9]⟩, ⟨.or,[10,11]⟩, ⟨.or,[2,12]⟩, ⟨.and,[8,13]⟩, ⟨.or,[6,15]⟩, ⟨.and,[14,16]⟩],17⟩

theorem size : witness.size = 12 := rfl

theorem monotone : Monotone2 witness := by
  simp [Monotone2,witness]

set_option maxRecDepth 16000 in
theorem correct : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) =
    Nat.testBit (4278124160 * 2 ^ 32 + 4269860992) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel

end LowerSymSix

namespace Direct64
open PEqualNP.CircuitLowerBounds SignedProjection
abbrev W := BitVec 64
abbrev basicOps (a b : W) := signedOps a b
abbrev goal : W := ~~~0xfefefe80fe80e880
open CoreSigned (build)
def tableB (x : Fin 6 → Bool) :=
  Nat.testBit (4278124160 * 2 ^ 32 + 4269860992) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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

theorem low (reject : ¬ build basicOps (0xfefefe80fe80e880 : W) 10 cols.toFinset)
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
    (reject : ¬ CoreSigned.build SignedProjection.signedOps (0xfefefe80fe80e880 : BitVec 64) 10 Direct64.cols.toFinset) :
∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124160 * 2 ^ 32 + 4269860992) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124160 * 2 ^ 32 + 4269860992) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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

def ew0 : Word := 0xaaa

def ew1 : Word := 0xccc

def ew2 : Word := 0xf00

def ew3 : Word := 0x22aa

def ew4 : Word := 0x2a2a

def ew5 : Word := 0x2aaa

def ew6 : Word := 0x30f0

def ew7 : Word := 0x3f00

def ew8 : Word := 0x44cc

def ew9 : Word := 0x4c4c

def ew10 : Word := 0x4ccc

def ew11 : Word := 0x50f0

def ew12 : Word := 0x5f00

def ew13 : Word := 0x7070

def ew14 : Word := 0x70f0

def ew15 : Word := 0x7700

def ew16 : Word := 0x7f00

def ew17 : Word := 0x8080

def ew18 : Word := 0x8800

def ew19 : Word := 0x8888

def ew20 : Word := 0xa000

def ew21 : Word := 0xa0a0

def ew22 : Word := 0xaa00

def ew23 : Word := 0xaaaa

def ew24 : Word := 0xc000

def ew25 : Word := 0xc0c0

def ew26 : Word := 0xcc00

def ew27 : Word := 0xcccc

def ew28 : Word := 0xf000

def ew29 : Word := 0xf0f0

def ew30 : Word := 0xff00

def ew31 : Word := 0xaa0000

def ew32 : Word := 0xcc0000

def ew33 : Word := 0xf00000

def ew34 : Word := 0xa000a00

def ew35 : Word := 0xa0a0a0a

def ew36 : Word := 0xaa00000

def ew37 : Word := 0xc000c00

def ew38 : Word := 0xc0c0c0c

def ew39 : Word := 0xcc00000

def ew40 : Word := 0xf000000

def ew41 : Word := 0xf000f00

def ew42 : Word := 0xf0f0000

def ew43 : Word := 0x22222222

def ew44 : Word := 0x22880000

def ew45 : Word := 0x30303030

def ew46 : Word := 0x30c00000

def ew47 : Word := 0x33000000

def ew48 : Word := 0x33003300

def ew49 : Word := 0x33330000

def ew50 : Word := 0x44444444

def ew51 : Word := 0x44880000

def ew52 : Word := 0x50505050

def ew53 : Word := 0x50a00000

def ew54 : Word := 0x55000000

def ew55 : Word := 0x55005500

def ew56 : Word := 0x55550000

def ew57 : Word := 0x82820000

def ew58 : Word := 0x82828282

def ew59 : Word := 0x84840000

def ew60 : Word := 0x84848484

def ew61 : Word := 0x88880000

def ew62 : Word := 0x88888888

def ew63 : Word := 0x90900000

def ew64 : Word := 0x90909090

def ew65 : Word := 0x99000000

def ew66 : Word := 0x99009900

def ew67 : Word := 0x99990000

def ew68 : Word := 0xa0a00000

def ew69 : Word := 0xa0a0a0a0

def ew70 : Word := 0xa5000000

def ew71 : Word := 0xa500a500

def ew72 : Word := 0xa5a50000

def ew73 : Word := 0xaa00aa00

def ew74 : Word := 0xaaaa0000

def ew75 : Word := 0xaaaaaaaa

def ew76 : Word := 0xc0c00000

def ew77 : Word := 0xc0c0c0c0

def ew78 : Word := 0xc3000000

def ew79 : Word := 0xc300c300

def ew80 : Word := 0xc3c30000

def ew81 : Word := 0xcc00cc00

def ew82 : Word := 0xcccc0000

def ew83 : Word := 0xcccccccc

def ew84 : Word := 0xeeee0000

def ew85 : Word := 0xeeeeeeee

def ew86 : Word := 0xf000f000

def ew87 : Word := 0xf0f00000

def ew88 : Word := 0xf0f0f0f0

def ew89 : Word := 0xfafa0000

def ew90 : Word := 0xfafafafa

def ew91 : Word := 0xfcfc0000

def ew92 : Word := 0xfcfcfcfc

def ew93 : Word := 0xff000000

def ew94 : Word := 0xff00ff00

def ew95 : Word := 0xffff0000

def ew96 : Word := 0xa0a00000a0a

def ew97 : Word := 0xc0c00000c0c

def ew98 : Word := 0xf0000000f00

def ew99 : Word := 0xf0f00000000

def ew100 : Word := 0x222200002222

def ew101 : Word := 0x303000003030

def ew102 : Word := 0x330000003300

def ew103 : Word := 0x333300000000

def ew104 : Word := 0x444400004444

def ew105 : Word := 0x505000005050

def ew106 : Word := 0x550000005500

def ew107 : Word := 0x555500000000

def ew108 : Word := 0x888800008888

def ew109 : Word := 0xa0a00000a0a0

def ew110 : Word := 0xaa000000aa00

def ew111 : Word := 0xaaaa00000000

def ew112 : Word := 0xaaaa0000aaaa

def ew113 : Word := 0xc0c00000c0c0

def ew114 : Word := 0xcc000000cc00

def ew115 : Word := 0xcccc00000000

def ew116 : Word := 0xcccc0000cccc

def ew117 : Word := 0xf0000000f000

def ew118 : Word := 0xf0f000000000

def ew119 : Word := 0xf0f00000f0f0

def ew120 : Word := 0xff0000000000

def ew121 : Word := 0xff000000ff00

def ew122 : Word := 0xffff00000000

def ew123 : Word := 0xa000a0a000a00

def ew124 : Word := 0xa0a00000a0a00

def ew125 : Word := 0xc000c0c000c00

def ew126 : Word := 0xc0c00000c0c00

def ew127 : Word := 0xf0000000f0000

def ew128 : Word := 0xf00000f000000

def ew129 : Word := 0xf000f00000000

def ew130 : Word := 0xf0f0000000000

def ew131 : Word := 0x82008200820082

def ew132 : Word := 0x84008400840084

def ew133 : Word := 0x88000000880000

def ew134 : Word := 0x88008800880088

def ew135 : Word := 0x90000000900000

def ew136 : Word := 0x90009000900090

def ew137 : Word := 0x99000000000000

def ew138 : Word := 0x99000000990000

def ew139 : Word := 0x99009900000000

def ew140 : Word := 0xa000a000a000a0

def ew141 : Word := 0xa5000000a50000

def ew142 : Word := 0xa500a500000000

def ew143 : Word := 0xaa000000aa0000

def ew144 : Word := 0xaa00aa00000000

def ew145 : Word := 0xaa00aa00aa00aa

def ew146 : Word := 0xc000c000c000c0

def ew147 : Word := 0xc3000000c30000

def ew148 : Word := 0xc300c300000000

def ew149 : Word := 0xcc000000cc0000

def ew150 : Word := 0xcc00cc00000000

def ew151 : Word := 0xcc00cc00cc00cc

def ew152 : Word := 0xf0000000f00000

def ew153 : Word := 0xf000f000000000

def ew154 : Word := 0xf000f000f000f0

def ew155 : Word := 0xff000000000000

def ew156 : Word := 0xff000000ff0000

def ew157 : Word := 0xff00ff00000000

def ew158 : Word := 0x202020202020202

def ew159 : Word := 0x300030003000300

def ew160 : Word := 0x303000003030000

def ew161 : Word := 0x303030300000000

def ew162 : Word := 0x404040404040404

def ew163 : Word := 0x500050005000500

def ew164 : Word := 0x505000005050000

def ew165 : Word := 0x505050500000000

def ew166 : Word := 0x808080808080808

def ew167 : Word := 0xa000a000a000a00

def ew168 : Word := 0xa0a00000a0a0000

def ew169 : Word := 0xa0a0a0a00000000

def ew170 : Word := 0xa0a0a0a0a0a0a0a

def ew171 : Word := 0xc000c000c000c00

def ew172 : Word := 0xc0c00000c0c0000

def ew173 : Word := 0xc0c0c0c00000000

def ew174 : Word := 0xc0c0c0c0c0c0c0c

def ew175 : Word := 0xf0000000f000000

def ew176 : Word := 0xf000f0000000000

def ew177 : Word := 0xf000f000f000000

def ew178 : Word := 0xf000f000f000f00

def ew179 : Word := 0xf0f00000f0f0000

def ew180 : Word := 0xf0f00000f0f0f00

def ew181 : Word := 0xf0f0f0f00000000

def ew182 : Word := 0xf0f0f0f00000f00

def ew183 : Word := 0xf0f0f0f0f0f0000

def ew184 : Word := 0x1010101010101010

def ew185 : Word := 0x1100110011001100

def ew186 : Word := 0x1111000011110000

def ew187 : Word := 0x1111111100000000

def ew188 : Word := 0x2020202020202020

def ew189 : Word := 0x2200220022002200

def ew190 : Word := 0x2222000022220000

def ew191 : Word := 0x2222222200000000

def ew192 : Word := 0x2222222222222222

def ew193 : Word := 0x3000300030003000

def ew194 : Word := 0x3030000030300000

def ew195 : Word := 0x3030303000000000

def ew196 : Word := 0x3030303030303030

def ew197 : Word := 0x3300000033000000

def ew198 : Word := 0x3300330000000000

def ew199 : Word := 0x3300330033003300

def ew200 : Word := 0x3333000033330000

def ew201 : Word := 0x3333333300000000

def ew202 : Word := 0x4040404040404040

def ew203 : Word := 0x4400440044004400

def ew204 : Word := 0x4444000044440000

def ew205 : Word := 0x4444444400000000

def ew206 : Word := 0x4444444444444444

def ew207 : Word := 0x5000500050005000

def ew208 : Word := 0x5050000050500000

def ew209 : Word := 0x5050505000000000

def ew210 : Word := 0x5050505050505050

def ew211 : Word := 0x5500550055005500

def ew212 : Word := 0x5555000055550000

def ew213 : Word := 0x5555555500000000

def ew214 : Word := 0x8888888888888888

def ew215 : Word := 0xa0a0a0a0a0a0a0a0

def ew216 : Word := 0xaa00aa00aa00aa00

def ew217 : Word := 0xaaaa0000aaaa0000

def ew218 : Word := 0xaaaaaaaa00000000

def ew219 : Word := 0xaaaaaaaaaaaaaaaa

def ew220 : Word := 0xc0c0c0c0c0c0c0c0

def ew221 : Word := 0xcc00cc00cc00cc00

def ew222 : Word := 0xcccc0000cccc0000

def ew223 : Word := 0xcccccccc00000000

def ew224 : Word := 0xcccccccccccccccc

def ew225 : Word := 0xeeeeeeeeeeeeeeee

def ew226 : Word := 0xf000f000f000f000

def ew227 : Word := 0xf0f00000f0f00000

def ew228 : Word := 0xf0f0f0f000000000

def ew229 : Word := 0xf0f0f0f0f0f0f0f0

def ew230 : Word := 0xfafafafafafafafa

def ew231 : Word := 0xfcfcfcfcfcfcfcfc

def ew232 : Word := 0xff000000ff000000

def ew233 : Word := 0xff00ff0000000000

def ew234 : Word := 0xff00ff00ff00ff00

def ew235 : Word := 0xffff000000000000

def ew236 : Word := 0xffff0000ffff0000

def ew237 : Word := 0xffffffff00000000

def labelsBlock0 : Array Nat := #[
  0xb0c,
  0x70c,
  0x714,
  0x718,
  0x1924,
  0x1036,
  0xb24,
  0xb28,
  0xd14,
  0x2924,
  0x104a,
  0x10ca,
  0x1056,
  0x1a28,
  0xd24,
  0x1944
]

def labelsBlock1 : Array Nat := #[
  0x104e,
  0xd30,
  0xe18,
  0x1960,
  0x105e,
  0xe28,
  0x1a60,
  0x704,
  0xe30,
  0xb04,
  0x3144,
  0x1c30,
  0x174c,
  0x710,
  0xd04,
  0xb08
]

def labelsBlock2 : Array Nat := #[
  0x708,
  0x2a28,
  0x3184,
  0x1754,
  0x1758,
  0x1a48,
  0x1002,
  0x1062,
  0x1904,
  0x1c60,
  0xb20,
  0x1006,
  0x2c30,
  0xe08,
  0x1c50,
  0x3104
]

def labelsBlock3 : Array Nat := #[
  0x10a2,
  0x1076,
  0x100a,
  0x2984,
  0x700,
  0xd10,
  0x278c,
  0x109a,
  0x2794,
  0xe10,
  0x31c0,
  0x1066,
  0x103e,
  0x109e,
  0x100e,
  0x32c0
]

def labelsBlock4 : Array Nat := #[
  0x10d2,
  0x2798,
  0x2904,
  0xd20,
  0x1940,
  0x1032,
  0x1a40,
  0x170c,
  0x106a,
  0xe20,
  0x1714,
  0x1920,
  0x5100ca,
  0x5200ca,
  0x5210ca,
  0xb00
]

def labelsBlock5 : Array Nat := #[
  0x1a20,
  0x1718,
  0x10a6,
  0x34c0,
  0x107a,
  0x1c40,
  0x10e6,
  0x1748,
  0x1744,
  0x1750,
  0x10ce,
  0x3288,
  0x3248,
  0x29a0,
  0x2aa0,
  0x10c6
]

def labelsBlock6 : Array Nat := #[
  0xd00,
  0xe00,
  0x10b2,
  0x10de,
  0x2714,
  0x270c,
  0x10e2,
  0x1c20,
  0x10aa,
  0x2718,
  0x10da,
  0x2a88,
  0x10ea,
  0x10ee,
  0x10f2,
  0x107e
]

def labelsBlock7 : Array Nat := #[
  0x1046,
  0x410066,
  0x420066,
  0x421066,
  0x2920,
  0x2a20,
  0x3100,
  0x510066,
  0x610066,
  0x710066,
  0x520066,
  0x620066,
  0x720066,
  0x521066,
  0x621066,
  0x721066
]

def labelsBlock8 : Array Nat := #[
  0x10ae,
  0x1096,
  0x10be,
  0x144010066,
  0x148020066,
  0x148421066,
  0x3140,
  0x3240,
  0x1042,
  0x1082,
  0x108e,
  0x1092,
  0x1a00,
  0x1900,
  0x1022,
  0x3180
]

def labelsBlock9 : Array Nat := #[
  0x144010032,
  0x410032,
  0x510032,
  0x610032,
  0x710032,
  0x148020032,
  0x420032,
  0x520032,
  0x620032,
  0x720032,
  0x148421032,
  0x421032,
  0x521032,
  0x621032,
  0x721032,
  0x632036
]

def labelsBlock10 : Array Nat := #[
  0x10b6,
  0x3200,
  0x1026,
  0x102a,
  0x3280,
  0x14401003e,
  0x41003e,
  0x51003e,
  0x61003e,
  0x71003e,
  0x14802003e,
  0x42003e,
  0x52003e,
  0x62003e,
  0x72003e,
  0x14842103e
]

def labelsBlock11 : Array Nat := #[
  0x42103e,
  0x52103e,
  0x62103e,
  0x72103e,
  0x1c10,
  0x2c90,
  0x2c10,
  0x5100c6,
  0x1a08,
  0x2a08,
  0x5200c6,
  0x5210c6,
  0x1c00,
  0x1d,
  0x25,
  0x9
]

def labelsBlock12 : Array Nat := #[
  0x15,
  0x49,
  0x41,
  0x81,
  0x79,
  0x2790,
  0x2788,
  0x2784,
  0x3490,
  0x3480,
  0x74c,
  0x12d,
  0x1086,
  0x338c,
  0x334c,
  0x106e
]

def labelsBlock13 : Array Nat := #[
  0x10d6,
  0x5100da,
  0x5200da,
  0x5210da,
  0x10c2,
  0x3400,
  0x21,
  0x29,
  0x2d,
  0x31,
  0x4d,
  0x51,
  0x55,
  0x65,
  0x69,
  0x85
]

def labelsBlock14 : Array Nat := #[
  0x89,
  0x99,
  0x1b4c,
  0x1b44,
  0x1d54,
  0x1d44,
  0x1e58,
  0x1e48,
  0x101e,
  0x101a,
  0x1016,
  0x754,
  0xe9,
  0xfd,
  0x111,
  0x3924
]

def labelsBlock15 : Array Nat := #[
  0x108a,
  0x131,
  0xb4c,
  0x63206a,
  0x5320aa,
  0x3594,
  0x3554,
  0x7320ee,
  0x7320f2,
  0x151,
  0x7310ee,
  0x7310f2,
  0x159,
  0x1072,
  0x7300ee,
  0x7300f2
]

def labelsBlock16 : Array Nat := #[
  0x161,
  0x10ba,
  0x1740,
  0x2780,
  0x2a00,
  0x2900,
  0x5,
  0x11,
  0xd,
  0x19,
  0x3d,
  0x39,
  0x45,
  0x5d,
  0x61,
  0x75
]

def labelsBlock17 : Array Nat := #[
  0x71,
  0x7d,
  0x91,
  0x95,
  0xa1,
  0xa5,
  0x35,
  0x59,
  0x6d,
  0x8d,
  0x9d,
  0xa9,
  0x194c,
  0x1954,
  0x1a4c,
  0x1b48
]

def labelsBlock18 : Array Nat := #[
  0x1a58,
  0x1c54,
  0x1d50,
  0x1c58,
  0x1e50,
  0xb1,
  0xb5,
  0xb9,
  0xbd,
  0xc1,
  0xc5,
  0xc9,
  0xcd,
  0xd1,
  0xd5,
  0xd9
]

def labelsBlock19 : Array Nat := #[
  0xdd,
  0x103a,
  0x1052,
  0x105a,
  0xed,
  0xf1,
  0xf5,
  0xf9,
  0x101,
  0x105,
  0x109,
  0x10d,
  0x115,
  0x119,
  0x11d,
  0x121
]

def labelsBlock20 : Array Nat := #[
  0x129,
  0x139,
  0x2980,
  0x2a80,
  0xb8c,
  0x432036,
  0x141,
  0x135,
  0x13d,
  0x145,
  0x314c,
  0x3154,
  0x5100ee,
  0x5100f2,
  0x5200ee,
  0x5200f2
]

def labelsBlock21 : Array Nat := #[
  0x5210ee,
  0x5210f2,
  0x155,
  0x15d,
  0x165,
  0x169,
  0x16d,
  0x171,
  0x1,
  0xad,
  0x1012,
  0xe1,
  0x3300,
  0x330c,
  0x102e,
  0xe5
]

def labelsBlock22 : Array Nat := #[
  0x125,
  0x149,
  0x14d,
  0x2c20,
  0x2c00,
  0x175
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
  ⟨0xaaaa,⟨1,by decide⟩,0xa880,[ew19,ew21,ew22],3,decodeHints 0xac0080217000643c17⟩,
  ⟨0xcccc,⟨2,by decide⟩,0xc880,[ew19,ew25,ew26],3,decodeHints 0x0⟩,
  ⟨0xf0f0,⟨4,by decide⟩,0xe080,[ew21,ew25,ew28],3,decodeHints 0x0⟩,
  ⟨0xff00,⟨8,by decide⟩,0xe800,[ew22,ew26,ew28],3,decodeHints 0x0⟩,
  ⟨0xf000f00,⟨8,by decide⟩,0xe000800,[ew34,ew37,ew40],3,decodeHints 0x0⟩,
  ⟨0xff00000,⟨20,by decide⟩,0xe800000,[ew36,ew39,ew40],3,decodeHints 0x0⟩,
  ⟨0x33cc0000,⟨18,by decide⟩,0x32800000,[ew44,ew46,ew47],3,decodeHints 0x0⟩,
  ⟨0x55aa0000,⟨17,by decide⟩,0x54800000,[ew51,ew53,ew54],3,decodeHints 0x0⟩,
  ⟨0x99990000,⟨16,by decide⟩,0x98800000,[ew61,ew63,ew65],3,decodeHints 0x0⟩,
  ⟨0xa5a50000,⟨16,by decide⟩,0xa4800000,[ew59,ew68,ew70],3,decodeHints 0x0⟩,
  ⟨0xc3c30000,⟨16,by decide⟩,0xc2800000,[ew57,ew76,ew78],3,decodeHints 0x0⟩,
  ⟨0x99000000990000,⟨16,by decide⟩,0x98000000800000,[ew133,ew135,ew137],3,decodeHints 0x0⟩,
  ⟨0xffff,⟨0,by decide⟩,0xe880,[ew23,ew27,ew29,ew30],6,decodeHints 0xac80c041d008802e340007c324f0f180c234⟩,
  ⟨0xf0f0f0f,⟨0,by decide⟩,0xe000800,[ew35,ew38,ew41,ew42],4,decodeHints 0xad01c0c2a0007c324f0212ca02a14235184f⟩,
  ⟨0x99999999,⟨0,by decide⟩,0x98808880,[ew62,ew64,ew66,ew67],4,localHints 3 0x4706c3a010013d7834 0xf606a0d60688⟩,
  ⟨0xffff0000,⟨16,by decide⟩,0xfe800000,[ew74,ew82,ew87,ew93],5,decodeHints 0xad89046590e15cb102079108c442a9108d02⟩
]

def viewsBlock1 : Array View := #[
  ⟨0x99009900990099,⟨0,by decide⟩,0x98008000800080,[ew134,ew136,ew138,ew139],4,decodeHints 0xaf0740234668740234670740234aed71aa34⟩,
  ⟨0xff00ff00000000,⟨32,by decide⟩,0xfe008000000000,[ew144,ew150,ew153,ew155],4,decodeHints 0xaf90470c51b3198f031123d488f64a3d4903⟩,
  ⟨0x33333333,⟨0,by decide⟩,0x32002000,[ew43,ew45,ew48,ew49],4,decodeHints 0x0⟩,
  ⟨0x55555555,⟨0,by decide⟩,0x54004000,[ew50,ew52,ew55,ew56],4,decodeHints 0x0⟩,
  ⟨0xa5a5a5a5,⟨0,by decide⟩,0xa480a080,[ew60,ew69,ew71,ew72],4,decodeHints 0x0⟩,
  ⟨0xaaaaaaaa,⟨1,by decide⟩,0xaa80a880,[ew62,ew69,ew73,ew74],4,decodeHints 0x0⟩,
  ⟨0xc3c3c3c3,⟨0,by decide⟩,0xc280c080,[ew58,ew77,ew79,ew80],4,decodeHints 0x0⟩,
  ⟨0xcccccccc,⟨2,by decide⟩,0xcc80c880,[ew62,ew77,ew81,ew82],4,decodeHints 0x0⟩,
  ⟨0xf0f0f0f0,⟨4,by decide⟩,0xf080e080,[ew69,ew77,ew86,ew87],4,decodeHints 0x0⟩,
  ⟨0xff00ff00,⟨8,by decide⟩,0xfe00e800,[ew73,ew81,ew86,ew93],6,decodeHints 0x0⟩,
  ⟨0xf0f00000f0f,⟨0,by decide⟩,0xe0000000800,[ew96,ew97,ew98,ew99],4,decodeHints 0x0⟩,
  ⟨0x333300003333,⟨0,by decide⟩,0x320000002000,[ew100,ew101,ew102,ew103],4,decodeHints 0x0⟩,
  ⟨0x555500005555,⟨0,by decide⟩,0x540000004000,[ew104,ew105,ew106,ew107],4,decodeHints 0x0⟩,
  ⟨0xaaaa0000aaaa,⟨1,by decide⟩,0xaa800000a880,[ew108,ew109,ew110,ew111],4,decodeHints 0x0⟩,
  ⟨0xcccc0000cccc,⟨2,by decide⟩,0xcc800000c880,[ew108,ew113,ew114,ew115],4,decodeHints 0x0⟩,
  ⟨0xf0f00000f0f0,⟨4,by decide⟩,0xf0800000e080,[ew109,ew113,ew117,ew118],4,decodeHints 0x0⟩
]

def viewsBlock2 : Array View := #[
  ⟨0xffff00000000,⟨32,by decide⟩,0xfe8000000000,[ew111,ew115,ew118,ew120],5,decodeHints 0x0⟩,
  ⟨0xf000f0f000f00,⟨8,by decide⟩,0xe00000e000800,[ew123,ew125,ew128,ew129],4,decodeHints 0x0⟩,
  ⟨0xf0f00000f0f00,⟨8,by decide⟩,0xe0e0000000800,[ew124,ew126,ew127,ew130],4,decodeHints 0x0⟩,
  ⟨0xa500a500a500a5,⟨0,by decide⟩,0xa4008000800080,[ew132,ew140,ew141,ew142],4,decodeHints 0x0⟩,
  ⟨0xc300c300c300c3,⟨0,by decide⟩,0xc2008000800080,[ew131,ew146,ew147,ew148],4,decodeHints 0x0⟩,
  ⟨0xff000000ff0000,⟨16,by decide⟩,0xfe000000800000,[ew143,ew149,ew152,ew155],5,decodeHints 0x0⟩,
  ⟨0x303030303030303,⟨0,by decide⟩,0x202020002000000,[ew158,ew159,ew160,ew161],4,decodeHints 0x0⟩,
  ⟨0x505050505050505,⟨0,by decide⟩,0x404040004000000,[ew162,ew163,ew164,ew165],4,decodeHints 0x0⟩,
  ⟨0xa0a0a0a0a0a0a0a,⟨1,by decide⟩,0xa0a0a000a000800,[ew166,ew167,ew168,ew169],4,decodeHints 0x0⟩,
  ⟨0xc0c0c0c0c0c0c0c,⟨2,by decide⟩,0xc0c0c000c000800,[ew166,ew171,ew172,ew173],4,decodeHints 0x0⟩,
  ⟨0xf000f000f000f00,⟨8,by decide⟩,0xe000e000e000800,[ew167,ew171,ew175,ew176],4,decodeHints 0x0⟩,
  ⟨0x1111111111111111,⟨0,by decide⟩,0x1010100010000000,[ew184,ew185,ew186,ew187],4,decodeHints 0x0⟩,
  ⟨0x2222222222222222,⟨1,by decide⟩,0x2222220022002000,[ew188,ew189,ew190,ew191],4,decodeHints 0x0⟩,
  ⟨0x3030303030303030,⟨4,by decide⟩,0x3030300030002000,[ew188,ew193,ew194,ew195],4,decodeHints 0x0⟩,
  ⟨0x3300330033003300,⟨8,by decide⟩,0x3200320032002000,[ew189,ew193,ew197,ew198],4,decodeHints 0x0⟩,
  ⟨0x4444444444444444,⟨2,by decide⟩,0x4444440044004000,[ew202,ew203,ew204,ew205],4,decodeHints 0x0⟩
]

def viewsBlock3 : Array View := #[
  ⟨0x5050505050505050,⟨4,by decide⟩,0x5050500050004000,[ew202,ew207,ew208,ew209],4,decodeHints 0x0⟩,
  ⟨0xffffffff,⟨0,by decide⟩,0xfe80e880,[ew75,ew83,ew88,ew94,ew95],8,decodeHints 0xb000c041d008802e340007c324f0f180c2340200c041d008802e3414235184f5e180c234⟩,
  ⟨0xff00ff00ff00ff,⟨0,by decide⟩,0xfe008000800080,[ew145,ew151,ew154,ew156,ew157],6,localHints 4 0x102220d00c041d008802e2f6a9d94234 0xda987650ca987650ba98765042123210⟩,
  ⟨0xf0f0f0f0f0f0f0f,⟨0,by decide⟩,0xe0e0e000e000800,[ew170,ew174,ew178,ew179,ew181],7,decodeHints 0xb081c0c2a0007c324f0212ca02a14235184f049d0ea2a21416084f179d9427614235184f⟩,
  ⟨0xaaaaaaaaaaaaaaaa,⟨1,by decide⟩,0xaaaaaa80aa80a880,[ew214,ew215,ew216,ew217,ew218],6,localHints 4 0xb1000080901004842f140643c17 0xb760a210976032108760521044403210⟩,
  ⟨0xff00ff00ff00ff00,⟨8,by decide⟩,0xfe00fe00fe00e800,[ew216,ew221,ew226,ew232,ew233],6,localHints 4 0xec0e0607024e875b181096503390c922a 0xedc0b21065403210a980721065403210⟩,
  ⟨0xffff0000ffff,⟨0,by decide⟩,0xfe800000e880,[ew112,ew116,ew119,ew121,ew122],8,decodeHints 0x0⟩,
  ⟨0x3333333333333333,⟨0,by decide⟩,0x3232320032002000,[ew192,ew196,ew199,ew200,ew201],7,decodeHints 0x0⟩,
  ⟨0x5555555555555555,⟨0,by decide⟩,0x5454540054004000,[ew206,ew210,ew211,ew212,ew213],7,decodeHints 0x0⟩,
  ⟨0xcccccccccccccccc,⟨2,by decide⟩,0xcccccc80cc80c880,[ew214,ew220,ew221,ew222,ew223],6,decodeHints 0x0⟩,
  ⟨0xf0f0f0f0f0f0f0f0,⟨4,by decide⟩,0xf0f0f080f080e080,[ew215,ew220,ew226,ew227,ew228],6,decodeHints 0x0⟩,
  ⟨0xffff0000ffff0000,⟨16,by decide⟩,0xfefe0000fe800000,[ew217,ew222,ew227,ew232,ew235],6,decodeHints 0x0⟩,
  ⟨0xffffffff00000000,⟨32,by decide⟩,0xfefefe8000000000,[ew218,ew223,ew228,ew233,ew235],6,decodeHints 0x0⟩,
  ⟨0xffffffffffffffff,⟨0,by decide⟩,0xfefefe80fe80e880,[ew219,ew224,ew229,ew234,ew236,ew237],10,decodeHints 0xb280c041d008802e340007c324f0f180c2340200c041d008802e3414235184f5e180c2340480c041d008802e3421416084fb2180c234179d942766a9d9423414235184f5e180c234⟩
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
  ⟨0,3,[ew19,ew21,ew22],localHints 4 0x1e0c8001017010041c06 0x258168155262367057066353024314322010⟩,
  ⟨12,3,[ew16,ew23,ew27,ew29],decodeHints 0xb85c02061008002070e87404110f07810010c86400020f87c0003⟩,
  ⟨12,4,[ew17,ew23,ew27,ew29,ew30],decodeHints 0x3c1e0400032190002092490a8183e1f0004886430701c542a030460c001f0000201010080603⟩,
  ⟨12,4,[ew13,ew23,ew27,ew29,ew30],localHints 4 0xc85c3e12100a81000070043006010440e03 0x6896ff89ee64dd8cbb61aa4298987654332100⟩,
  ⟨12,3,[ew14,ew23,ew27,ew30],decodeHints 0xc86400020f87c00030e87404110f07810010b85c0206100800207⟩,
  ⟨12,4,[ew18,ew23,ew27,ew29,ew30],decodeHints 0x3c1e040047239090082e17008386a350400c4020008543a1d010440000838046401030080e03⟩,
  ⟨12,4,[ew15,ew23,ew27,ew29,ew30],localHints 4 0xc85c3e200a8741000070043006010440e03 0x6876ff83ee67dd80cc6baa3298767653432010⟩,
  ⟨12,3,[ew19,ew21,ew25,ew30],decodeHints 0x309842400301801000008044c432793c0008010084c2a0180c562a⟩,
  ⟨12,4,[ew19,ew21,ew27,ew29,ew30],decodeHints 0x168b41000000e40008249242abd1a8001000008042218158443e1f000200e151901c04020180c5607⟩,
  ⟨12,3,[ew19,ew22,ew26,ew29],localHints 4 0x184c0001a0041c39130d4561d 0xaa4699268832776504300210⟩,
  ⟨12,4,[ew19,ew22,ew27,ew29,ew30],decodeHints 0x168b424011c8e424be00924020e0000086010700422181584406121f00c4020008383a1d0181c5603⟩,
  ⟨12,4,[ew19,ew23,ew25,ew29,ew30],decodeHints 0xf07810001c8002400008040035000488643072f42218130443219000200c0e190180402130180603⟩,
  ⟨12,4,[ew19,ew23,ew26,ew29,ew30],decodeHints 0xf07810010000092010a8046a35042f802430085422181304404081f0082e17008380406130083a1d⟩,
  ⟨12,5,[ew19,ew23,ew27,ew29,ew30],localHints 5 0x7872d924b606ad70910dac15848f800c00442064015f8383002158982203 0x85e8cdd196b435036b4abc95adc2d63420a6b9508b18c26b433a85ada4e6242030905088c20110465288427b5ae5adcd6b16b521093192841cc6108822904300820⟩,
  ⟨12,4,[ew9,ew23,ew27,ew29,ew30],localHints 4 0xf05c3e122187400080a83802060101c2203 0xff899893ee36dd9cbb62aa3198987655432100⟩,
  ⟨12,3,[ew10,ew23,ew29,ew30],decodeHints 0xf07810010f87c00031008002070c86400020b85c02060e8740411⟩
]

def nodesBlock1 : Array Node := #[
  ⟨12,4,[ew20,ew23,ew27,ew29,ew30],decodeHints 0x5a2d090043219000082e17008183e1f0000c40200081c3a1d010601000070061402158082203⟩,
  ⟨12,4,[ew12,ew23,ew27,ew29,ew30],localHints 4 0x782e35040803a18000541c01030080e03 0xeeb42b32dd43ccb0aa41992877645432321010⟩,
  ⟨12,3,[ew21,ew22,ew27,ew28],localHints 4 0xc24f010b44c340307c6420 0x996726528827065044030210⟩,
  ⟨12,4,[ew21,ew22,ew27,ew29,ew30],localHints 4 0x16b0472490f85454121f0803a020301c6403 0xff8edd84c443bb2a12943408706655430210⟩,
  ⟨12,4,[ew21,ew23,ew25,ew27,ew30],decodeHints 0xc8640008168b42400010083e1f00048542a032f40e151301c3c1e040001c06158180201130380603⟩,
  ⟨12,4,[ew21,ew23,ew27,ew28,ew30],decodeHints 0x168b432190000804490a8083e1f003040e151301c042a0106002001f004020e130042e17008184020⟩,
  ⟨12,5,[ew21,ew23,ew27,ew29,ew30],localHints 5 0xb5b81924b6c3eda090a9ac18860f810c200054030b158097e06190980e03 0x36e94bd29adcad665e08dc116b334c455cc331946258825d433a856ba4e611046a50842118c184826346107b5ae5adcd6b16b109225250631c84398c52104300820⟩,
  ⟨12,4,[ew8,ew23,ew27,ew29,ew30],localHints 4 0xf0640c3510054541204000020e010440607 0xff75ee87545dcc71bb5a911287665454331210⟩,
  ⟨12,4,[ew11,ew23,ew27,ew29,ew30],localHints 4 0x3c190f90c3a18090200001010180607 0xdd75cc532332bb51a110993875654432321010⟩,
  ⟨12,4,[ew22,ew23,ew26,ew27,ew29],decodeHints 0xb85c020e168b424011c8e44020008543a1d012f806121300c3c1e040041002158080000130206a35⟩,
  ⟨12,4,[ew22,ew23,ew27,ew28,ew29],decodeHints 0x168b42e1700818723909008402000b0406121300c3a1d010600001190040008130003219000083e1f⟩,
  ⟨12,5,[ew22,ew23,ew27,ew29,ew30],localHints 5 0xb5bc396e85c40da0a875ae18090021c3207308030d1581980021f01c4c03 0x97e963d2def4e5247e0c3c19ef25c864d88bb112932cc00806f784210a6a09d4094d273092408480424610085c17b9ab5b12962d6a4a50631c84398c52102310400⟩,
  ⟨12,4,[ew4,ew23,ew27,ew29,ew30],localHints 4 0xf06410491007400120705402060c0080e03 0xffd9ee9dcc649890bb06aa0398987655432210⟩,
  ⟨12,3,[ew5,ew27,ew29,ew30],decodeHints 0xf07810010c86400020b85c02060f87c00031008002070e8740411⟩,
  ⟨12,4,[ew23,ew24,ew27,ew29,ew30],decodeHints 0x3c1e040043219000082e170081824000a80430020f87c00031008002070e874041101c3c4c03⟩,
  ⟨12,4,[ew7,ew23,ew27,ew29,ew30],localHints 4 0x5a390b848401d088001c01030080e03 0xdda4cca2bb430a109941882766545432321010⟩
]

def nodesBlock2 : Array Node := #[
  ⟨12,3,[ew23,ew25,ew26,ew28],localHints 4 0x5632300789e19018d02e07 0x469416911481776355432210⟩,
  ⟨12,4,[ew23,ew25,ew26,ew29,ew30],localHints 4 0xf30c320e1f05c64350410c5406018740407 0xff7edd4c9417b1aa14918873633035432210⟩,
  ⟨12,4,[ew23,ew25,ew27,ew28,ew30],decodeHints 0xf07832190030c0c0e1581802001f004020e158042e170f87c00030190c1c031500c0611100800207⟩,
  ⟨12,5,[ew23,ew25,ew27,ew29,ew30],localHints 5 0x79c0196f822223e62004041f0004886320736c542b0336023101300d7e07 0xcb696fd2ed6cbde87e0f6c1defbdac741d8b5a108ab9d47be8e74def422435c90c88cf113e007400f789c202da26084b1014029d2240847114c500c022084310020⟩,
  ⟨12,4,[ew3,ew23,ew27,ew29,ew30],localHints 4 0xf0e42e0e0f81c54080900002150c0080c03 0xff85ee72dd5cbb87545a292387665454232100⟩,
  ⟨12,4,[ew6,ew23,ew27,ew29,ew30],localHints 4 0x2d0c9243e1d088200001010180607 0xcc65bb53a33299510110883765654432321010⟩,
  ⟨12,4,[ew23,ew26,ew27,ew28,ew29],decodeHints 0xf0782e1700b0c04081580800011900400081580032191008002071a8d410030e87404110f87c0003⟩,
  ⟨12,5,[ew23,ew26,ew27,ew29,ew30],localHints 5 0x79c2176f8380113193100c3e1a821ba2000854561d0136423121301d8003 0xb76ad0d59ce5e56749e0e725294af07b60eb5ded64a6a37568a54d6b9a9525ad3088ce7039e283c4e701a012d805300b5894229d004a007394c500c022084310020⟩,
  ⟨12,4,[ew0,ew23,ew27,ew29,ew30],localHints 4 0x168642e061a90c2212000202a01070083003 0xff84ee72dd4c7b784a45212978764543212100⟩,
  ⟨12,4,[ew1,ew23,ew27,ew29,ew30],localHints 4 0x1e1c9243e20038001001070080611 0xcc546b654a4399618847011065654343221010⟩,
  ⟨12,5,[ew23,ew27,ew28,ew29,ew30],localHints 5 0x201c197085dc0068a8ad883e0f801bc3210005b8078a099841d018083011 0xa62a0e7318c6334673990c994a13b148628e70ae2a2ac26584a552b4148419843208a221b9e883d0e70da34296362c6a52128198603800600ca3008830906210020⟩,
  ⟨12,6,[ew23,ew27,ew29,ew30],localHints 5 0xf46c331a0405e320e030f83e008c048642000c5c2a07158744c03014583011 0x6aefb9521b6d2f7d2e0b38e1994ef93ce10c0ee33cd7668e9638d6bace9329211921d12a210791c42a16c6912c2916b5212828066390262906310020⟩,
  ⟨15,4,[ew61,ew74,ew82,ew87,ew93],localHints 4 0xaa2e231104a130b239c40f0e0a44624 0xddc4bb943237aa493238876545432321100⟩,
  ⟨15,4,[ew74,ew82,ew84,ew87,ew93],localHints 4 0xaa2e719602c0f1295c38290988c488e 0xddc88c8c5454b878aa54928787665431210⟩,
  ⟨15,4,[ew68,ew74,ew82,ew87,ew93],localHints 4 0xaa2e231104a295104dc80f0e08c2c24 0xddc4bb941221aa496872126545433212100⟩,
  ⟨15,4,[ew74,ew82,ew87,ew89,ew93],localHints 4 0x1ca2e14918b00f1284c3824511644616 0x8787d8c8b5aa78011099508787645432210⟩
]

def nodesBlock3 : Array Node := #[
  ⟨15,4,[ew31,ew74,ew82,ew87,ew93],localHints 4 0x55230b8b0441284c1e1c1488c2c24 0xcca7bb7a994186743462126554343212100⟩,
  ⟨15,4,[ew54,ew74,ew82,ew87,ew93],localHints 4 0x72c75c71c2c110ae591283c521c0b08c2624 0xf6e6d6c6bb43a6099458823765454323210⟩,
  ⟨15,4,[ew74,ew76,ew82,ew87,ew93],localHints 4 0xaa2e2305852a3730704644078944813 0xddc3bb23a98737366554432011001100110⟩,
  ⟨15,4,[ew74,ew82,ew87,ew91,ew93],localHints 4 0x1ce2e1485946440789448570e1644613 0x6767d7c7b36767a13198876055044302210⟩,
  ⟨15,4,[ew32,ew74,ew82,ew87,ew93],localHints 4 0x5523058882e2b8941e1c1488c4813 0xcc85ba5434a995877400110654343221010⟩,
  ⟨15,4,[ew47,ew74,ew82,ew87,ew93],localHints 4 0x73c808c588fc784a572c83c521c0b08c2624 0xf9e9d92cc45b9a988417721665454321010⟩,
  ⟨15,4,[ew33,ew74,ew82,ew87,ew93],localHints 4 0x551491888252c8b81e1c118584813 0xcb5aa852332995801107730654432321010⟩,
  ⟨15,4,[ew40,ew74,ew82,ew87,ew93],localHints 4 0x2ac924658914845c572c83c521c0b08c2624 0xf94e9d9cc43b9a988417721665432321010⟩,
  ⟨15,5,[ew74,ew82,ew87,ew93],decodeHints 0x980705c55978a41e55750a45c2e750701e0f9708c4a46968581e46748584a257488c1e0f5185838585188c52589608c381c958585216950901e449484c4a447404c1e0f740904a255104c385751090525794090381c9384c52134704c4659470902c599309046239284c2c13⟩,
  ⟨17,4,[ew144,ew150,ew153,ew155],localHints 4 0x32590a463a3c445b630d8a6c5208e07e3a 0x6de59e5dd69928c19c18829916b25b26615139a08a099388067357366050024314322010⟩,
  ⟨49,6,[ew62,ew85,ew88,ew94,ew95],localHints 5 0x1403c8ea50e2403c4b0d8d5062e2183052132508dd6040c8001017008380d3105008221d 0xd299fe7abfe798cd2b4ad1ee7e6d9de6ef7d1d87a9d39a9959a9929a9d4790598942f89418c906e19494a906969054a95694940e790633904e794230188621b98f1b86d189821894b1952b1954a18922194e8188c8188e7194c51906018820⟩,
  ⟨49,7,[ew62,ew75,ew83,ew88,ew94,ew95],localHints 6 0x280791d4c1c0da443c501c9242c4b068d4244309855d8451e010e23b000204e01070600410050142203 0x78b3a486336486338e78b78b7887c88603a28607df78838834829d3472dd34728a3482c80c65dc0d939c0d95d70c638e0cd2cb0c629b0c62cb0c328a0d92080c61da0c62080d91c71013981135d811338e1015d710d2cb1015561012cb1045551132081014941012081134920c10c10c31860c31110d00d00c338e0cf0cf0c338e0cd2cb0c328a0cc2cb0c328a0c22080c31c70c92080c21c70c30c50c21850c40c00c2040⟩,
  ⟨49,7,[ew75,ew83,ew85,ew88,ew94,ew95],localHints 6 0xa01e4753871241e1e114363b3b8b84e292508c32080b8501c060c14448040687c0012100300215038440a020182820ec 0x94d42a9e97ea9e941094d94d9498499e64289e68619494097c96247d53647d56187c934928a4102a386128a4102a286128a34d2a079e28a34d29f79e28524929d71c28a24928571c5843c409a41b59a3cf08440458435909461959434d0846045942570845575842490945540410530841442834030513d22914100433c328334e04730e28734d04330328724b04320b283249047207082086083143082104043043082040⟩,
  ⟨49,7,[ew43,ew75,ew83,ew88,ew94,ew95],localHints 6 0x1403c8ea80e06d261e280e492140b144481f090802a070e9147804069e076080009c1c01060403002088280a03 0x84b4279263a792641084b84b8488889234259238a28484083883203892e038930c3882c87053df09b41f71b3cf08541071c2cb08531e7052cb08e30c71b20808525d70520809b2491804001993da1994101803c01802d81945d81942cb1805c01942161805561802081945540821931801800821451924101863cf1914101863cf18e30c1862cb18d30c1862cb18124918620818a249181208187184081144082083081000⟩,
  ⟨49,7,[ew50,ew75,ew83,ew88,ew94,ew95],localHints 6 0xa01e475487036940f12846190405c1c06258d48613080748a3c06810f23b090004e1500860040c050142203 0x80a3a68e53668e538e80a80a8078478e23a48e28618073873476df35929f3596db3472870c53c50dd39e0dd3cf0c53850c529c0d86dc0d828a0c56c50d81da0c565a0c51c70d86581013974d43d711438e4c13cf10428a4c12d610128a4cd2cb1141c74c12151011c74d42080c34d20c31450c10c10d13cf0c338e0d03cf0c338e0cd2cb0c328a0cc2cb0c328a0c22080c31c70c92080c21c70c30c60c21450c40c00c2040⟩,
  ⟨49,6,[ew69,ew83,ew90,ew94,ew95],localHints 5 0x1403c961f12929542306a543284150302c132387194040f0200132038802e02008141c06 0xb259fcfa9fcf98cb26c991d9d942fd9418c91ee79493c91f7c91d299537bb12e4ce19ace2f7b1184a1135a0155a0129a1144944f391204910e49461010c431398f1384d10d8310d4b1052b1054a10d231204610ce61048510c0510c8310400⟩
]

def nodesBlock4 : Array Node := #[
  ⟨49,7,[ew69,ew75,ew83,ew88,ew94,ew95],localHints 6 0x280799c362d252ac46960c924524b0687c24ed1504c30451e010e43b040002a01050500406080140e03 0x70a3a47a33647a338e70a70a0898620993a209986108938e08d2e00892a00892cb08228a7055c579d39f79d5d770538534529b3442db34428a3452c508425a0856450852450846440c13980d25d80d238e0c15c10cd2960c15560c128a0c35550810810822490820d40d21450c14530c11450d245109009008238e08f08f08238e08d2cb08228a08c2cb08228a082088082248087145082104086145082104083080082040⟩,
  ⟨49,7,[ew75,ew83,ew88,ew90,ew94,ew95],localHints 6 0xa01e3c228ec4a470e06c3c15252b046970c9e81014050582e2707018a224020346a000901c0205768741803010403011 0x70c3ea7a96aa7a93cf70c70c1453cf16838e1453cf16738e14530c16696514530c15a9655098892233e45238a22093c95096612133215136592093090820a020920970338379d3df79d38e7033c368331b69265b69230c6836431566161435c31431431565d62122555034d55032492124d21443c40903911503cf08438414430c0802cd14030c0842c420820a2042042082490840842080871400c60840461440c3080040⟩,
  ⟨49,7,[ew35,ew75,ew83,ew88,ew94,ew95],localHints 6 0x1403cce1b169295a234c0649227149444835090803a18089147804069ec7600040302a010a018200a0101c0a03 0x7cc4278663a78664107cc7cc70992505b42571b92404941071c2e30493237092cb04e30c7c33c38604228603cf7c340338331e3862de38630c3832c304625d7036c37032430466c61404001593da1594101403c014030c1535d815330c1405c00411561401400412491530d51405151400c31535131524101453cf1514101453cf14e30c1452cb14d30c1452cb14a1480412481441861450c31471861440c3041042041000⟩,
  ⟨49,7,[ew52,ew75,ew83,ew88,ew94,ew95],localHints 6 0xa01e470e07894ae11a6432080b8380c4b0687c402a0804c8a3c0d810f83b090002a01050503002060140e03 0x78a3a682536682538e78a78a0883c80a33a40a33cf08838808872209a2a209a71c0882887845c481f3a181f5d778438434429d35971d35928a34470409921b08469b0842080996990c13984d25d80d238e4c15c10c32964c12d60c128a4cd2cb0824d50822080810810d21044c11540c11044d21450913cf08238e0903cf08238e08d2cb08228a08c2cb08228a082089082208087145082104086145082104083080082040⟩,
  ⟨49,6,[ew75,ew77,ew92,ew94,ew95],localHints 5 0xa0a0190791c38ca16ccc2e5157890089a0687c0085090a80c140b04c4003008142a07 0x8363e9ed9e9ee318360d425fd41e3d41def42629421bc4277c425ad4337b10c431663a1645810e2310d77105b71056b10da31585510d35812249c9f49ca31811e4611ae6016e601ad611644192a410e441124418e610065110251106310020⟩,
  ⟨49,7,[ew75,ew77,ew83,ew88,ew94,ew95],localHints 6 0x280799c361e2806410ee228f076010114560240226c1a1f001cc2443070a454060505822100600c0a07 0x48f4e45633a45634d348f48f04b86204a4e204a86104b4cb04e76004b3e004b75d0413cf1c845f1c64df1c64511c84c81ce3de1c875e1c83cf1c775d0480480412cb0411dc05b05b0414d305a05a0414d304e34d0413cf05934d0413cf0410580412d80470570412174824c25544565544d34824423823d03803503803cf3823420402cc0422820422c20402801c52091c21821c22021c51850400400421020420c2040040⟩,
  ⟨49,7,[ew75,ew83,ew88,ew92,ew94,ew95],localHints 6 0x503c228ec1e470e06c5a0e2508c7208033b8a2b112011380d0f800fa12060402620138040a15038742803010283011 0x5525a96254696255965525521455141685961455141675961454921669651454921519652ca88a2635a42e38a224a58a2ca7212484a12c871c24a48a0820a024a24a14350309e59f15e51408358314349208171d14149208370324925b24324324928a08308324909a54458461751961759654450444449344741344749244440414d3cd1443841443c414d38d24728c2c420c2c428a2472070800c61440461440c3080040⟩,
  ⟨49,7,[ew38,ew75,ew83,ew88,ew94,ew95],localHints 6 0x1403cce1b0f12846390b94564244e87c2443138a43a1808914780d021f87600040501c010301404100601c1403 0x6cc3e77663a77663cf6cc6cc5c99251963e55d69241893c95d72e31893235c92cb18e30c0454050613e20614100453c504530c0542e005430c0452c518605f0450451862496c03c075c41e75c3cf6c040038031a38265a38230c3806401822585c05805c02401825820531550405150401450535130524100413cf0514100413cf04e30c0412cb04d30c0412cb04a048186248186187186145044082041000043082041000⟩,
  ⟨49,7,[ew45,ew75,ew83,ew88,ew94,ew95],localHints 6 0xa01e470e0b4a0190b94566244f0343e12100540e2a050588a3c0d810fe3b040001c010a0180410060440a03 0x6ca3a676536676538e6ca6ca0483c80633a40633cf0483880482e20562a20562cb0482881c66a14d23a11d269a4c63861c72a04c62e01c628a4cd2cb0414df0412080460466c038075c69e75c38e6c068034029935561935528a3406000552170405970402080555954c21941c04801c01804c24820513cf04138e0503cf04138e04d2cb04128a04c2cb04128a041049041208047045041185044082041000043082041000⟩,
  ⟨49,8,[ew75,ew83,ew88,ew94,ew95],localHints 6 0x1403c8e1c0d87894230c8227f3e0bcf6780e031447824021141a1f000ec253b9d08272019c0540f379b0766a03014d03011 0x5935eb66a4ab66a5d759359358c9cc6685e96689e758c5cc48c8a649c4e649c8a248c4cc5835436645e56645555835c34834e349b8a349b4d348388385b31f80371f78330c75b71b5845c465855a6585d75845444844d44894544894d348444440930e3c428e34430c2c92892000c61c40461440c3080040⟩,
  ⟨51,5,[ew170,ew174,ew178,ew179,ew181,ew182],localHints 5 0x1a4f811de22000a06675108588c0f3a0248807128a80c13 0x2869c25289a067bda8334c87390d5042a631610a941484280108039cc4200042908310820⟩,
  ⟨51,5,[ew2,ew170,ew174,ew178,ew179,ew181],localHints 5 0x2f4f9085033439708c0f430688825150240800030580e13 0x29454e52832316406f70c6210da31b02b50420005210a0e7180c6294841886208020⟩,
  ⟨51,5,[ew41,ew98,ew170,ew174,ew179,ew181],localHints 5 0xbd3e872e2185442198680816098245022230188807128000a0f 0xb59d53526633186249c422d648c4cb841ee6b4cc3308b22d4a4a40831cc02148310820⟩,
  ⟨51,6,[ew98,ew170,ew174,ew178,ew179,ew181],localHints 6 0x17a7de268141d4bc461f9d0ba212d91074251532e80090d3c04404240141e00290186e161801c7a13 0x223e33508cd3cf89040941084f3e041024f24b2df24e24b34d19879d41e7586064061971843441171063466d470624619419b24909069961a65040260208d0805c000d0025c25495825020890955140064c21130861801002904123cf45040a3cf2ce30a34c2cb20a2481461871041c61851040420830000c2081000⟩,
  ⟨51,5,[ew170,ew174,ew178,ew179,ew180,ew181],decodeHints 0x34f30482408ef0d010440421108660f000001e330203c08f20321cb8062f0180c5e281401a06230180c0f03a1834072e81c0e5d2592c08072201c0e25150a80c13⟩,
  ⟨51,6,[ew41,ew170,ew174,ew178,ew179,ew181],localHints 6 0x1e62f213c4d0872850c7e862e12c1b421d1ac541609b30340965d040848110146600290186e5e1801c7a5d 0xd4642e590b45134a34a2a325224a45124d3622cb84d3492c919b18446011b6c64461997d435f51964634675678624619619d2490910806dc0114426c208d69365a4cd3426425c96025820890975964c654251508619351329240a45030d34f2cb38d34c2cb28a20a2481461871041c61851040420830000c2081000⟩
]

def nodesBlock5 : Array Node := #[
  ⟨51,5,[ew170,ew174,ew177,ew178,ew179,ew181],decodeHints 0x5e2f0d514001aa20000022790001209240680804028881e000321cb806030582c060c864003f030582c0603a1834070384c26070f87c003a0384c2607150a80c13⟩,
  ⟨51,6,[ew170,ew174,ew178,ew179,ew181,ew183],localHints 6 0x12043432d9946028cc90f4290dd0e5e0c8fc1e301ea18ba1a2e088b61f000e84a2a038182c13 0x196e131b85b6e029b81b30c29929b6db1df1d179145d4477071db1da30c6986873071d91d129145844728709708158105704258208b09431550b2c23020890812810490422824874c24530871d24510d00c03c00100033c30cc0cd2ce34c3032c30ca0c024000a0032431872031480c71c61450021030440c2080040⟩,
  ⟨51,7,[ew170,ew174,ew178,ew179,ew181],localHints 6 0x5f49a4108661aa38a0d0223a978a019290fc1e742e8240a2125810900d0f80074251e8a86007030dc2c13 0x44e82535c4a591c82044e48e44a4a28e182276149244a80a34a39e7d571e75538e34a70a44341b09a49b5da4104434833433190813995c130c3433835d62980835585c328a0965554444941d341415349244440434438f1c030f14038e34430414928b1c420b14428a1c92080800c61c40461440c3080040⟩,
  ⟨52,6,[ew214,ew215,ew216,ew217,ew218],localHints 6 0x5e4219868500f111946cf6a591c38f565078c8386752818092508d9aeb188103200310202e02008c01c06 0x44a8a545f42545f8a244a40a4484244638a44634104488882c82a12e07e12e028a2c87c844370345d41e45d71b4434032c36032d929a2d96172c32830831960812160811860832034444c44544154544d24444042c43442ce28f2ce34c2c42841c42091c01891c02081c41840800c50840450840c3080040⟩,
  ⟨61,8,[ew178,ew219,ew224,ew225,ew229,ew234,ew236,ew237],localHints 6 0x17ad96a1a5a088ca36238703cf87b9205c2702990704a1185c306920884a22406848405308a206e3d50534122c67d30081b040001c01181a0160a0a01804100601c9803 0x478ef657bdb8e115513d5eb9e3ae5554fe0f3d1deddb7b5144fd8f314334575d1450c54c310332473c9040c44c059c413cf30132b555c14530555ad452e451bd042f451b904093cf06db413cf26db6b30cb1c72c30cadc705885a55aa98a21551457c59d1a277df15114578518f3c679e14f14632615c98530c19c19a6a51491405408e292355502200044081f86045101f0003cf09e7823cf01e00231d01c74030c09c09a69b00901a14501a0196172155415145955415144d14414104914414100413813ce2c134130c2c12812490c10c12492061811451c61811451020810000c2081000⟩,
  ⟨61,9,[ew219,ew224,ew225,ew229,ew234,ew236,ew237],localHints 7 0x5e4219868500f111956e3623b4438f90f1dcdc3c161b5121b680b8d85a1499070542508c32082905c1c060c1a48209109444804188343e000908002300a81c220b060082803401588063 0xe51f4126ecc4172edf3e0e50c140e40c4072fdf4072fcc180e41f102640a3d6cf1dbd6cf0a142641d900e3578d18e0c3a72e17af0e34c0d263560d18d4a376cd562c2634a0d683503318748336475020183480d0e04c180ec57af0ec4c180ec17af0e04a1426b962c0eb8a1426b562c0e2081006ad52a0e04810062152a0e0468d18a53a70e0468d18a13a70e18b860a94c260a94b970e18c060a189064888a230a889122618a060a1882106710210a7081006190060a7069e3e18e9e0a1868d1870e9c0a0411b0e184060e10c040e64b9a0e64c180e10b840e10a0426549160e54a1426109040e1081106287910e2881006107840e2868e181058e0e1068d182858a0e040890e104040e043060a100840608080⟩,
  ⟨61,8,[ew199,ew219,ew224,ew229,ew230,ew234,ew236,ew237],localHints 6 0x5eb93586970227dbe99e25328d858470e06c2a641c12846190a0282e6920944481203a286e1d1fd3c122124538080d040007a0b0289c1c01290180410060449a03 0x476e74579d36d91551395e37db8dd554ed8e391d70d35c1144ed0e895573514cd5562514c51472410c9147141030e381c3004e38cc3022d22e56fbadb4854822a22b46caeaa8844821c20938e25c70838869aa483081541675689d450554515016546695040544505990138e1411578d71621458c55e25d72211498452085c92405407d481f55501400044075079d45101000038e09c70238e01c01a69b00c01a20801a0191c70856005d80051425c22d55415145955415144d14414104914414100413c138e34134130c0c10c130c2c92412082892412081c11811451020810000c2081000⟩,
  ⟨61,9,[ew219,ew224,ew229,ew230,ew234,ew236,ew237],localHints 7 0x2f210cc342807888dc3c36a25a025328d8586f23870361e0a99174382534846fc0c9e8c4082b18c2c1707018d24104884a224020c41a35000480e0b0089cd8402d0741803010f43011 0xa4dec024e8bc052e9ebd0a4cb930a3cbbf52f9ebf52f8b970a3de8f243c9bc4cedd3c4cec993243dd0f0a20b970ae4b160ae4b970ae0b160a2099324dc8910adc99324d88910a3078f04d5a340a2078f0431a340a2d88b14c8bb314c98b10a2cb8b142d68b60b89af14b96ad242c98b142d02c046c7ac146d020042c78b14204ab0a2c60b0a0cb0342a0baa52a0b160a0cb83240c88342949a74c94891240c983480c7a34269023446878f420d0030474f9d0a0c4030a0c4030474f1d046859c140cd9c140c58b0468d9a0a10b840a60b190a60b970a10b040a1098424508950a5099324108840a1078f04007100a0078f04107040a2040d0a106040a2058b141040404244070a0018604100860a101830400080⟩,
  ⟨61,8,[ew211,ew219,ew224,ew229,ew231,ew234,ew236,ew237],localHints 6 0x5e421986850227fbf9fa0f328d858470e06c1c641c12846080322cd241288907a1f06040401d1d5444209245401a04090006e0b0289c2a010505030021801c9c03 0x436e74539d36d90510394e37db8dd450ed8e390d70d35c1040ed0e695573514cd555a514c51472410c9147141030e381c3004e38cc3022d22e52fbadb4850822a22b42caeaa8840822420938e2649083888a2a483081151275289d554450411112542695144440410e38592414e3849048a28c43048882048847430c05008158605140150004007917de41001100175c04e3800405db5c068001b0176975c86402590082172495c46001580041171452d55415145955415144d14414104914414100413c138e34134130c18118130c2c92412082892412081c51411041851411040c1081000⟩,
  ⟨61,9,[ew211,ew219,ew224,ew229,ew234,ew236,ew237],localHints 6 0x17908661a1403c44651b0b08e1c0d878c8701c12902230c8202f0007018d24128890621f100c03a0c310e8786e10825126d0681024002d1b02a013195830022001c1603 0x60ee3b7754bbb35e3860e48e04c4ba079e3a07949204ce0c04c3b7076d7707638e04cd4c608c886b34b4b33cb2608488748bc86b03b1a70bef7483880489ae06332e0639a60483086044c45eb4adb2b4d36044847443c45e83aaa683cf7443840443270629a706230c0449846a22255c48e59042086a28e26004806204e16204926004c060038075e3df61e38e7403c00410dc04130c04004061621b68025b6002086962496161195c01596001045d61450554d30414920544d30414920513cf04138e0503cf04138e04104d04130c04b24904120804a249041208047145041104046145041104043042041000⟩,
  ⟨61,9,[ew219,ew224,ew229,ew231,ew234,ew236,ew237],localHints 6 0x17908661a14088dc3c36a25a00f328d8586f23870362d07190704a118e41006059b0b4695d904122128b4c48042a036001f3e80104122b100cc131009c0215038742803010dc3011 0x158f3f5fa77f7faf3c15875815277e7fdf3e7fd75d152f125d263b6b4ebb6b46185d2e9214f71c17975d17971c17875d14f5965f76181775965f66181634920b5d3414f4920a3d34149c492b27732b2c71149749289b49c2e62f2aeb6d5c960928996c0884ac28896508948928f8ab1498c914370316976a16971c1437431435835e76281675965c360314349208196614149208394314f3e41438c314f2492833c30a23e114474445e7207de75d1447045c460445959b6996185c45845444944474144c749244440408c38c1443c414438408c34c08724b28420b2842490872070800c61440461440c3080040⟩,
  ⟨61,9,[ew199,ew219,ew224,ew229,ew234,ew236,ew237],localHints 6 0x2f5c9ac34b812888ca361611c381b16990704a118642e6938104a281121503e1241081f8520a81c3a14808fc786e04885126d0203410002d1b01c012b0180466200441603 0x60fe7c8b64fc9f6e7960f4cf04c4fb07ae7b07a4d304ce4c04c3f8077db80773cf04cd8c608cc87344f59f4cf36084c8888c087313f2931c308883c804882f04932f04982004830860548562d4ee62d4926054c56053858ab3ec62b38e8853c50411ea04130c0450456162297052696052087162496004c07e64a89e64d36004808803c07e33a59233cf88038004032105a82105a30c04080071a21e7c06de74020871a6da5c21596005996001455c25820554d30414920544d30414920513cf04138e0503cf04138e04104d04130c04b24904120804a249041208047046041145044082041000043082041000⟩,
  ⟨61,9,[ew178,ew219,ew224,ew229,ew234,ew236,ew237],localHints 6 0x2f5b2d434b417088ca36238703c641c12846390b9a4e041109450224378346a121009cd0536a075f2a00c044786e048b1126d0206c10003603802632b01804662001c1603 0x78fe7c8f64fca76e7978f4cf04d4fb07ae7b07a4d304de4d04d3f8077db80773cf04dd8d7894897b44f57b44927894c97893898f23f37b238e8c93c90412f104134d0490497859c562f4f0a6f9e77854c58c588562d3ee96d8a28c53c504582c04636c04682004534574626b78572b7852497467067804c06e89eaa684d37809c08c03c06e48a69643cf8c088004036104282104234d04080074225f78071f78024974270261615a6c05da6401456165d60554d30414920544d30414920513cf04138e0503cf04138e04104c04134c04b04a041249048186041145047186041145044082041000043082041000⟩,
  ⟨61,10,[ew219,ew224,ew229,ew234,ew236,ew237],localHints 6 0xbc84330d0a01e22328d858470e06eae1e320e09423ab0641017aa8380c692f9041221289a8480406d503e3b000484153009682a0733076a4030118c3011 0x6d4cf66f06766f0cf36d46546cf6756f4cf56f46596cfccf58f5325b1c325b151458fc0f6cbb4b2ae66f6eeb6d28b64b58ba8b2ab52c5abaaa28b50ba4b86829e3e841e86128b3cb6c36030a66676e66180836435834c30a45255a44d30835038c33e209d86241d3cf08384329d2e00837a07c32cb29d79d6c46441da61c6da6591c46045845041d54d75955141c44c44843d11c83914083cf1c43842882cd1c424d3042cb2882480800c61c40461440c3080040⟩
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

def fastViews : QFast.Table View := ⟨62,viewsGet⟩

def fastNodes : QFast.Table Node := ⟨94,nodesGet⟩

end SignedProjection


namespace SignedProjection
def aliasMap1 : Array Nat := #[63,62,61,60,59,58,57,56,0,0,0,0,0,0,0,0,55,54,53,52,51,50,49,48,0,0,0,0,0,0,0,0,47,46,45,44,43,42,41,40,0,0,0,0,0,0,0,0,39,38,37,36,35,34,33,32,0,0,0,0,0,0,0,0]
def aliasMap2 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,16,17,18,19,20,21,22,23,48,49,50,51,52,53,54,55,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap3 : Array Nat := #[0,16,0,17,0,22,0,23,0,24,0,25,0,30,0,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap4 : Array Nat := #[0,16,0,18,0,21,0,23,0,24,0,26,0,29,0,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap5 : Array Nat := #[0,16,0,19,0,20,0,23,0,24,0,27,0,28,0,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap6 : Array Nat := #[0,17,0,19,0,21,0,23,0,24,0,26,0,28,0,30,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap7 : Array Nat := #[0,18,0,19,0,22,0,23,0,24,0,25,0,28,0,29,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap8 : Array Nat := #[0,20,0,21,0,22,0,23,0,24,0,25,0,26,0,27,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap9 : Array Nat := #[63,62,61,60,59,58,57,56,0,0,0,0,0,0,0,0,55,54,53,52,51,50,49,48,0,0,0,0,0,0,0,0,31,30,29,28,27,26,25,24,0,0,0,0,0,0,0,0,23,22,21,20,19,18,17,16,0,0,0,0,0,0,0,0]
def aliasMap10 : Array Nat := #[31,30,29,28,27,26,25,24,15,14,13,12,11,10,9,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap11 : Array Nat := #[0,8,0,9,0,10,0,11,0,12,0,13,0,14,0,15,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap12 : Array Nat := #[0,4,0,5,0,6,0,7,0,12,0,13,0,14,0,15,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap13 : Array Nat := #[0,2,0,3,0,6,0,7,0,10,0,11,0,14,0,15,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap14 : Array Nat := #[0,4,0,5,0,6,0,7,0,12,0,13,0,14,0,15,0,20,0,21,0,22,0,23,0,28,0,29,0,30,0,31,0,36,0,37,0,38,0,39,0,44,0,45,0,46,0,47,0,52,0,53,0,54,0,55,0,60,0,61,0,62,0,63]
def aliasMap15 : Array Nat := #[61,0,0,53,45,0,0,37,29,0,0,21,13,0,0,5,57,0,0,49,41,0,0,33,25,0,0,17,9,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap16 : Array Nat := #[59,0,0,51,43,0,0,35,27,0,0,19,11,0,0,3,57,0,0,49,41,0,0,33,25,0,0,17,9,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap17 : Array Nat := #[47,0,0,39,45,0,0,37,43,0,0,35,41,0,0,33,15,0,0,7,13,0,0,5,11,0,0,3,9,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap18 : Array Nat := #[31,0,0,23,29,0,0,21,27,0,0,19,25,0,0,17,15,0,0,7,13,0,0,5,11,0,0,3,9,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap19 : Array Nat := #[0,2,0,3,0,6,0,7,0,10,0,11,0,14,0,15,0,18,0,19,0,22,0,23,0,26,0,27,0,30,0,31,0,34,0,35,0,38,0,39,0,42,0,43,0,46,0,47,0,50,0,51,0,54,0,55,0,58,0,59,0,62,0,63]
def aliasMap20 : Array Nat := #[0,2,4,6,0,0,0,0,8,10,12,14,0,0,0,0,16,18,20,22,0,0,0,0,24,26,28,30,0,0,0,0,32,34,36,38,0,0,0,0,40,42,44,46,0,0,0,0,48,50,52,54,0,0,0,0,56,58,60,62,0,0,0,0]
def aliasMap21 : Array Nat := #[59,0,0,58,57,0,0,56,0,0,0,0,0,0,0,0,43,0,0,42,41,0,0,40,0,0,0,0,0,0,0,0,27,0,0,26,25,0,0,24,0,0,0,0,0,0,0,0,11,0,0,10,9,0,0,8,0,0,0,0,0,0,0,0]
def aliasMap22 : Array Nat := #[0,16,0,19,0,20,0,23,0,48,0,51,0,52,0,55,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap23 : Array Nat := #[59,0,0,51,43,0,0,35,27,0,0,19,11,0,0,3,58,0,0,50,42,0,0,34,26,0,0,18,10,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap24 : Array Nat := #[0,8,16,24,0,0,0,0,2,10,18,26,0,0,0,0,32,40,48,56,0,0,0,0,34,42,50,58,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap25 : Array Nat := #[0,8,0,9,0,10,0,11,0,24,0,25,0,26,0,27,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap26 : Array Nat := #[0,8,16,24,0,0,0,0,1,9,17,25,0,0,0,0,32,40,48,56,0,0,0,0,33,41,49,57,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap27 : Array Nat := #[16,0,0,48,17,0,0,49,18,0,0,50,19,0,0,51,8,0,0,40,9,0,0,41,10,0,0,42,11,0,0,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap28 : Array Nat := #[32,0,0,48,33,0,0,49,34,0,0,50,35,0,0,51,8,0,0,24,9,0,0,25,10,0,0,26,11,0,0,27,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap29 : Array Nat := #[0,1,2,3,0,0,0,0,8,9,10,11,0,0,0,0,32,33,34,35,0,0,0,0,40,41,42,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap30 : Array Nat := #[62,0,0,54,46,0,0,38,30,0,0,22,14,0,0,6,60,0,0,52,44,0,0,36,28,0,0,20,12,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap31 : Array Nat := #[62,0,0,54,46,0,0,38,30,0,0,22,14,0,0,6,58,0,0,50,42,0,0,34,26,0,0,18,10,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap32 : Array Nat := #[0,1,4,5,0,0,0,0,8,9,12,13,0,0,0,0,16,17,20,21,0,0,0,0,24,25,28,29,0,0,0,0,32,33,36,37,0,0,0,0,40,41,44,45,0,0,0,0,48,49,52,53,0,0,0,0,56,57,60,61,0,0,0,0]
def aliasMap33 : Array Nat := #[61,0,0,60,57,0,0,56,0,0,0,0,0,0,0,0,45,0,0,44,41,0,0,40,0,0,0,0,0,0,0,0,29,0,0,28,25,0,0,24,0,0,0,0,0,0,0,0,13,0,0,12,9,0,0,8,0,0,0,0,0,0,0,0]
def aliasMap34 : Array Nat := #[61,0,0,53,45,0,0,37,29,0,0,21,13,0,0,5,60,0,0,52,44,0,0,36,28,0,0,20,12,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap35 : Array Nat := #[0,8,16,24,0,0,0,0,4,12,20,28,0,0,0,0,32,40,48,56,0,0,0,0,36,44,52,60,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap36 : Array Nat := #[0,0,0,1,6,0,0,7,0,0,0,0,0,0,0,0,16,0,0,17,22,0,0,23,0,0,0,0,0,0,0,0,32,0,0,33,38,0,0,39,0,0,0,0,0,0,0,0,48,0,0,49,54,0,0,55,0,0,0,0,0,0,0,0]
def aliasMap37 : Array Nat := #[0,0,0,2,5,0,0,7,0,0,0,0,0,0,0,0,16,0,0,18,21,0,0,23,0,0,0,0,0,0,0,0,32,0,0,34,37,0,0,39,0,0,0,0,0,0,0,0,48,0,0,50,53,0,0,55,0,0,0,0,0,0,0,0]
def aliasMap38 : Array Nat := #[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap39 : Array Nat := #[31,0,0,23,30,0,0,22,29,0,0,21,28,0,0,20,15,0,0,7,14,0,0,6,13,0,0,5,12,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap40 : Array Nat := #[31,0,0,23,30,0,0,22,27,0,0,19,26,0,0,18,15,0,0,7,14,0,0,6,11,0,0,3,10,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap41 : Array Nat := #[0,0,0,6,1,0,0,7,8,0,0,14,9,0,0,15,16,0,0,22,17,0,0,23,24,0,0,30,25,0,0,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap42 : Array Nat := #[0,0,0,5,2,0,0,7,8,0,0,13,10,0,0,15,16,0,0,21,18,0,0,23,24,0,0,29,26,0,0,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap43 : Array Nat := #[0,2,4,6,0,0,0,0,8,10,12,14,0,0,0,0,16,18,20,22,0,0,0,0,24,26,28,30,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap44 : Array Nat := #[0,1,4,5,0,0,0,0,8,9,12,13,0,0,0,0,16,17,20,21,0,0,0,0,24,25,28,29,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap45 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap46 : Array Nat := #[47,0,0,39,46,0,0,38,45,0,0,37,44,0,0,36,15,0,0,7,14,0,0,6,13,0,0,5,12,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap47 : Array Nat := #[47,0,0,39,46,0,0,38,43,0,0,35,42,0,0,34,15,0,0,7,14,0,0,6,11,0,0,3,10,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap48 : Array Nat := #[0,2,4,6,0,0,0,0,8,10,12,14,0,0,0,0,32,34,36,38,0,0,0,0,40,42,44,46,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap49 : Array Nat := #[0,1,4,5,0,0,0,0,8,9,12,13,0,0,0,0,32,33,36,37,0,0,0,0,40,41,44,45,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def rootAliases : QFast.AliasTable
  | 1 => some (0, aliasMap13)
  | 2 => some (0, aliasMap12)
  | 3 => some (0, aliasMap11)
  | 4 => some (0, aliasMap25)
  | 5 => some (0, aliasMap8)
  | 6 => some (0, aliasMap7)
  | 7 => some (0, aliasMap6)
  | 8 => some (0, aliasMap5)
  | 9 => some (0, aliasMap4)
  | 10 => some (0, aliasMap3)
  | 11 => some (0, aliasMap22)
  | 18 => some (13, aliasMap44)
  | 19 => some (13, aliasMap43)
  | 20 => some (14, aliasMap42)
  | 21 => some (14, aliasMap18)
  | 22 => some (14, aliasMap41)
  | 23 => some (14, aliasMap40)
  | 24 => some (14, aliasMap39)
  | 25 => some (12, aliasMap10)
  | 26 => some (13, aliasMap29)
  | 27 => some (13, aliasMap49)
  | 28 => some (13, aliasMap48)
  | 29 => some (14, aliasMap17)
  | 30 => some (14, aliasMap47)
  | 31 => some (14, aliasMap46)
  | 32 => some (15, aliasMap45)
  | 33 => some (14, aliasMap28)
  | 34 => some (14, aliasMap27)
  | 35 => some (16, aliasMap37)
  | 36 => some (16, aliasMap36)
  | 37 => some (15, aliasMap2)
  | 38 => some (13, aliasMap26)
  | 39 => some (13, aliasMap24)
  | 40 => some (14, aliasMap16)
  | 41 => some (14, aliasMap23)
  | 42 => some (16, aliasMap21)
  | 43 => some (13, aliasMap35)
  | 44 => some (14, aliasMap15)
  | 45 => some (14, aliasMap34)
  | 46 => some (16, aliasMap33)
  | 47 => some (14, aliasMap31)
  | 48 => some (14, aliasMap30)
  | 54 => some (49, aliasMap38)
  | 55 => some (51, aliasMap32)
  | 56 => some (51, aliasMap20)
  | 57 => some (52, aliasMap19)
  | 58 => some (52, aliasMap14)
  | 59 => some (50, aliasMap9)
  | 60 => some (50, aliasMap1)
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
theorem blockRoots_48 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 48 14 = true := by decide +kernel

theorem joinRoots_0_0 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 32 = true :=
  @QFast.merge_blocks (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 16 16 blockRoots_0 blockRoots_16

theorem joinRoots_0_32 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 32 30 = true :=
  @QFast.merge_blocks (QFast.symCheckRoot rootAliases fastViews fastNodes) 32 16 14 blockRoots_32 blockRoots_48

theorem joinRoots_1_0 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 62 = true :=
  @QFast.merge_blocks (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 32 30 joinRoots_0_0 joinRoots_0_32

theorem certifiedRoots : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 62 = true := joinRoots_1_0

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
theorem blockNodes_84 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 84 10 = true := by decide +kernel

theorem joinNodes_0_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 12 12 blockNodes_0 blockNodes_12

theorem joinNodes_0_24 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 24 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 24 12 12 blockNodes_24 blockNodes_36

theorem joinNodes_0_48 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 48 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 48 12 12 blockNodes_48 blockNodes_60

theorem joinNodes_0_72 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 72 22 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 72 12 10 blockNodes_72 blockNodes_84

theorem joinNodes_1_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 48 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 24 24 joinNodes_0_0 joinNodes_0_24

theorem joinNodes_1_48 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 48 46 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 48 24 22 joinNodes_0_48 joinNodes_0_72

theorem joinNodes_2_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 94 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 48 46 joinNodes_1_0 joinNodes_1_48

theorem certifiedNodes : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 94 = true := joinNodes_2_0

end SignedProjection

namespace SignedProjection
def bMatches (z : Option View) : Bool :=
  match z with
  | none => false
  | some v => vg v == (0xfefefe80fe80e880 : Word) && vk v == 10 && (vs v).toFinset == Direct64.cols.toFinset

theorem rootNegative : ¬ CoreSigned.build signedOps (0xfefefe80fe80e880 : BitVec 64) 10 Direct64.cols.toFinset := by
  have shape : bMatches (QFast.get fastViews 61) = true := by decide +kernel
  cases ev : QFast.get fastViews 61 with
  | none => simp [ev, bMatches] at shape
  | some v =>
    have valid := QFast.symCertified rootAliases fastViews fastNodes certifiedRoots certifiedNodes ev
    simp only [ev,bMatches,Bool.and_eq_true,beq_iff_eq] at shape
    change ¬ CoreSigned.build signedOps (vg v) (vk v) (vs v).toFinset at valid
    rwa [shape.1.1,shape.1.2,shape.2] at valid
end SignedProjection
end PEqualNP.Outside.L_meta_12362_aux

open PEqualNP.Outside.L_meta_12362_aux in
theorem PEqualNP.Outside.L_meta_12362 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124160 * 2 ^ 32 + 4269860992) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124160 * 2 ^ 32 + 4269860992) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  LowerSymSix.finish SignedProjection.rootNegative
