import PEqualNP.Defs

-- The witness has twelve binary gates. Any circuit with a NOT and fewer gates
-- would have at most ten binary gates even with every negation available for free.
-- Finite signed-circuit certificates below exclude that possibility.
-- Signed-wire search and gate projections adapt the project’s Apache 2.0 proofs.
namespace PEqualNP.Outside.L_meta_12206_aux
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


namespace LowerSymSix
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.and,[0,1]⟩, ⟨.or,[0,1]⟩, ⟨.and,[2,7]⟩, ⟨.or,[6,8]⟩, ⟨.and,[2,6]⟩,
    ⟨.and,[4,5]⟩, ⟨.or,[3,11]⟩, ⟨.and,[10,12]⟩,
    ⟨.or,[4,5]⟩, ⟨.and,[3,14]⟩, ⟨.and,[9,15]⟩, ⟨.or,[13,16]⟩],17⟩

theorem size : witness.size = 12 := rfl

theorem monotone : Monotone2 witness := by
  simp [Monotone2,witness]

set_option maxRecDepth 16000 in
theorem correct : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) =
    Nat.testBit (3900762112 * 2 ^ 32 + 3892346880) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel

end LowerSymSix

namespace Direct64
open PEqualNP.CircuitLowerBounds SignedProjection
abbrev W := BitVec 64
abbrev basicOps (a b : W) := signedOps a b
abbrev goal : W := ~~~0xe880e800e8008000
open CoreSigned (build)
def tableB (x : Fin 6 → Bool) :=
  Nat.testBit (3900762112 * 2 ^ 32 + 3892346880) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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

theorem low (reject : ¬ build basicOps (0xe880e800e8008000 : W) 10 cols.toFinset)
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
    (reject : ¬ CoreSigned.build SignedProjection.signedOps (0xe880e800e8008000 : BitVec 64) 10 Direct64.cols.toFinset) :
∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3900762112 * 2 ^ 32 + 3892346880) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3900762112 * 2 ^ 32 + 3892346880) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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

def ew0 : Word := 0xa00aa00

def ew1 : Word := 0xc00cc00

def ew2 : Word := 0x2200aa00

def ew3 : Word := 0x2a002a00

def ew4 : Word := 0x2a00aa00

def ew5 : Word := 0x3000f000

def ew6 : Word := 0x3f000000

def ew7 : Word := 0x4400cc00

def ew8 : Word := 0x4c004c00

def ew9 : Word := 0x4c00cc00

def ew10 : Word := 0x5000f000

def ew11 : Word := 0x5f000000

def ew12 : Word := 0x70007000

def ew13 : Word := 0x7000f000

def ew14 : Word := 0x77000000

def ew15 : Word := 0x7f000000

def ew16 : Word := 0x80008000

def ew17 : Word := 0x88000000

def ew18 : Word := 0x88008800

def ew19 : Word := 0x88888888

def ew20 : Word := 0xa0000000

def ew21 : Word := 0xa000a000

def ew22 : Word := 0xa0a0a0a0

def ew23 : Word := 0xaa000000

def ew24 : Word := 0xaa00aa00

def ew25 : Word := 0xaaaa0000

def ew26 : Word := 0xaaaaaaaa

def ew27 : Word := 0xc0000000

def ew28 : Word := 0xc000c000

def ew29 : Word := 0xc0c0c0c0

def ew30 : Word := 0xcc000000

def ew31 : Word := 0xcc00cc00

def ew32 : Word := 0xcccc0000

def ew33 : Word := 0xcccccccc

def ew34 : Word := 0xf0000000

def ew35 : Word := 0xf000f000

def ew36 : Word := 0xf0f00000

def ew37 : Word := 0xf0f0f0f0

def ew38 : Word := 0xff000000

def ew39 : Word := 0xff00ff00

def ew40 : Word := 0xffff0000

def ew41 : Word := 0xa000000aa00

def ew42 : Word := 0xc000000cc00

def ew43 : Word := 0x22000000aa00

def ew44 : Word := 0x2a0000002a00

def ew45 : Word := 0x2a000000aa00

def ew46 : Word := 0x30000000f000

def ew47 : Word := 0x3f0000000000

def ew48 : Word := 0x44000000cc00

def ew49 : Word := 0x4c0000004c00

def ew50 : Word := 0x4c000000cc00

def ew51 : Word := 0x50000000f000

def ew52 : Word := 0x5f0000000000

def ew53 : Word := 0x700000007000

def ew54 : Word := 0x70000000f000

def ew55 : Word := 0x770000000000

def ew56 : Word := 0x7f0000000000

def ew57 : Word := 0x800000008000

def ew58 : Word := 0x880000000000

def ew59 : Word := 0x880000008800

def ew60 : Word := 0xa00000000000

def ew61 : Word := 0xa0000000a000

def ew62 : Word := 0xaa0000000000

def ew63 : Word := 0xaa000000aa00

def ew64 : Word := 0xaaaa0000aaaa

def ew65 : Word := 0xc00000000000

def ew66 : Word := 0xc0000000c000

def ew67 : Word := 0xcc0000000000

def ew68 : Word := 0xcc000000cc00

def ew69 : Word := 0xcccc0000cccc

def ew70 : Word := 0xf00000000000

def ew71 : Word := 0xf0000000f000

def ew72 : Word := 0xf0f00000f0f0

def ew73 : Word := 0xff0000000000

def ew74 : Word := 0xff000000ff00

def ew75 : Word := 0xffff00000000

def ew76 : Word := 0x80008000800080

def ew77 : Word := 0x80008080008000

def ew78 : Word := 0x80800000808000

def ew79 : Word := 0x88000000880000

def ew80 : Word := 0x88000088000000

def ew81 : Word := 0x88008800000000

def ew82 : Word := 0x88880000000000

def ew83 : Word := 0xa0000000a00000

def ew84 : Word := 0xa00000a0000000

def ew85 : Word := 0xa000a000000000

def ew86 : Word := 0xa0a00000000000

def ew87 : Word := 0xc0000000c00000

def ew88 : Word := 0xc00000c0000000

def ew89 : Word := 0xc000c000000000

def ew90 : Word := 0xc0c00000000000

def ew91 : Word := 0x800080008000800

def ew92 : Word := 0x880000008800000

def ew93 : Word := 0x880088000000000

def ew94 : Word := 0x880088008800880

def ew95 : Word := 0xa000a000a000a00

def ew96 : Word := 0xa0a0a0a0a0a0a0a

def ew97 : Word := 0xaa000000aa00000

def ew98 : Word := 0xaa00aa000000000

def ew99 : Word := 0xaaa000000000000

def ew100 : Word := 0xaaa0aaa0aaa0aaa

def ew101 : Word := 0xc000c000c000c00

def ew102 : Word := 0xc0c0c0c0c0c0c0c

def ew103 : Word := 0xcc000000cc00000

def ew104 : Word := 0xcc00cc000000000

def ew105 : Word := 0xccc000000000000

def ew106 : Word := 0xccc0ccc0ccc0ccc

def ew107 : Word := 0xe0e0e0e0e0e0e0e

def ew108 : Word := 0xf000f000f000f00

def ew109 : Word := 0x2000200020002000

def ew110 : Word := 0x2080000020800000

def ew111 : Word := 0x2080208000000000

def ew112 : Word := 0x2080208020802080

def ew113 : Word := 0x2200220022002200

def ew114 : Word := 0x2222222222222222

def ew115 : Word := 0x2288000022880000

def ew116 : Word := 0x2288228800000000

def ew117 : Word := 0x22aa000000000000

def ew118 : Word := 0x22aa22aa22aa22aa

def ew119 : Word := 0x2a2a000000000000

def ew120 : Word := 0x2aaa000000000000

def ew121 : Word := 0x2aaa2aaa2aaa2aaa

def ew122 : Word := 0x3000300030003000

def ew123 : Word := 0x3030303030303030

def ew124 : Word := 0x30c0000030c00000

def ew125 : Word := 0x30c030c000000000

def ew126 : Word := 0x30f0000000000000

def ew127 : Word := 0x30f030f030f030f0

def ew128 : Word := 0x3232323232323232

def ew129 : Word := 0x3300330033003300

def ew130 : Word := 0x3f00000000000000

def ew131 : Word := 0x4000400040004000

def ew132 : Word := 0x4080000040800000

def ew133 : Word := 0x4080408000000000

def ew134 : Word := 0x4080408040804080

def ew135 : Word := 0x4400440044004400

def ew136 : Word := 0x4444444444444444

def ew137 : Word := 0x4488000044880000

def ew138 : Word := 0x4488448800000000

def ew139 : Word := 0x44cc000000000000

def ew140 : Word := 0x44cc44cc44cc44cc

def ew141 : Word := 0x4c4c000000000000

def ew142 : Word := 0x4ccc000000000000

def ew143 : Word := 0x4ccc4ccc4ccc4ccc

def ew144 : Word := 0x5000500050005000

def ew145 : Word := 0x5050505050505050

def ew146 : Word := 0x50a0000050a00000

def ew147 : Word := 0x50a050a000000000

def ew148 : Word := 0x50f0000000000000

def ew149 : Word := 0x50f050f050f050f0

def ew150 : Word := 0x5454545454545454

def ew151 : Word := 0x5500550055005500

def ew152 : Word := 0x5f00000000000000

def ew153 : Word := 0x7070000000000000

def ew154 : Word := 0x70f0000000000000

def ew155 : Word := 0x70f070f070f070f0

def ew156 : Word := 0x7700000000000000

def ew157 : Word := 0x7f00000000000000

def ew158 : Word := 0x7f007f007f007f00

def ew159 : Word := 0x8000080080000800

def ew160 : Word := 0x8000200080002000

def ew161 : Word := 0x8000400080004000

def ew162 : Word := 0x8000800008000800

def ew163 : Word := 0x8000800020002000

def ew164 : Word := 0x8000800040004000

def ew165 : Word := 0x8000800080008000

def ew166 : Word := 0x8080000000000000

def ew167 : Word := 0x8080000000008080

def ew168 : Word := 0x8080000008080000

def ew169 : Word := 0x8080000020200000

def ew170 : Word := 0x8080000040400000

def ew171 : Word := 0x8080000080800000

def ew172 : Word := 0x8080080800000000

def ew173 : Word := 0x8080202000000000

def ew174 : Word := 0x8080404000000000

def ew175 : Word := 0x8080808000000000

def ew176 : Word := 0x8080808080808080

def ew177 : Word := 0x8282828282828282

def ew178 : Word := 0x8484848484848484

def ew179 : Word := 0x8800000000000000

def ew180 : Word := 0x8800000000008800

def ew181 : Word := 0x8800880088008800

def ew182 : Word := 0x8888000000000000

def ew183 : Word := 0x8888000088880000

def ew184 : Word := 0x8888808088888080

def ew185 : Word := 0x8888888800000000

def ew186 : Word := 0x8888888880808080

def ew187 : Word := 0x8888888888880000

def ew188 : Word := 0x8888888888888888

def ew189 : Word := 0x8a0a8a0a8a0a8a0a

def ew190 : Word := 0x8c0c8c0c8c0c8c0c

def ew191 : Word := 0x9090909090909090

def ew192 : Word := 0x9900990099009900

def ew193 : Word := 0x9999000099990000

def ew194 : Word := 0x9999999900000000

def ew195 : Word := 0xa000000000000000

def ew196 : Word := 0xa00000000000a000

def ew197 : Word := 0xa000a000a000a000

def ew198 : Word := 0xa0a0000000000000

def ew199 : Word := 0xa0a00000a0a00000

def ew200 : Word := 0xa0a08080a0a08080

def ew201 : Word := 0xa0a0a0a000000000

def ew202 : Word := 0xa0a0a0a080808080

def ew203 : Word := 0xa0a0a0a0a0a00000

def ew204 : Word := 0xa0a0a0a0a0a0a0a0

def ew205 : Word := 0xa222a222a222a222

def ew206 : Word := 0xa500a500a500a500

def ew207 : Word := 0xa5a50000a5a50000

def ew208 : Word := 0xa5a5a5a500000000

def ew209 : Word := 0xa8a8a8a8a8a8a8a8

def ew210 : Word := 0xaa00000000000000

def ew211 : Word := 0xaa000000aa000000

def ew212 : Word := 0xaa00aa0000000000

def ew213 : Word := 0xaa00aa00aa00aa00

def ew214 : Word := 0xaaaa000000000000

def ew215 : Word := 0xaaaa0000aaaa0000

def ew216 : Word := 0xaaaaaaaa00000000

def ew217 : Word := 0xaaaaaaaaaaaaaaaa

def ew218 : Word := 0xaf00af00af00af00

def ew219 : Word := 0xb030b030b030b030

def ew220 : Word := 0xbb00bb00bb00bb00

def ew221 : Word := 0xc000000000000000

def ew222 : Word := 0xc00000000000c000

def ew223 : Word := 0xc000c000c000c000

def ew224 : Word := 0xc0c0000000000000

def ew225 : Word := 0xc0c00000c0c00000

def ew226 : Word := 0xc0c08080c0c08080

def ew227 : Word := 0xc0c0c0c000000000

def ew228 : Word := 0xc0c0c0c080808080

def ew229 : Word := 0xc0c0c0c0c0c00000

def ew230 : Word := 0xc0c0c0c0c0c0c0c0

def ew231 : Word := 0xc300c300c300c300

def ew232 : Word := 0xc3c30000c3c30000

def ew233 : Word := 0xc3c3c3c300000000

def ew234 : Word := 0xc444c444c444c444

def ew235 : Word := 0xc8c8c8c8c8c8c8c8

def ew236 : Word := 0xcc00000000000000

def ew237 : Word := 0xcc000000cc000000

def ew238 : Word := 0xcc00cc0000000000

def ew239 : Word := 0xcc00cc00cc00cc00

def ew240 : Word := 0xcccc000000000000

def ew241 : Word := 0xcccc0000cccc0000

def ew242 : Word := 0xcccccccc00000000

def ew243 : Word := 0xcccccccccccccccc

def ew244 : Word := 0xcf00cf00cf00cf00

def ew245 : Word := 0xd050d050d050d050

def ew246 : Word := 0xdd00dd00dd00dd00

def ew247 : Word := 0xe0e0e0e0e0e0e0e0

def ew248 : Word := 0xee00ee00ee00ee00

def ew249 : Word := 0xeeeeeeeeeeeeeeee

def ew250 : Word := 0xf000000000000000

def ew251 : Word := 0xf0000000f0000000

def ew252 : Word := 0xf000f00000000000

def ew253 : Word := 0xf000f000f000f000

def ew254 : Word := 0xf0f0000000000000

def ew255 : Word := 0xf0f00000f0f00000

def ew256 : Word := 0xf0f0f0f000000000

def ew257 : Word := 0xf0f0f0f0f0f0f0f0

def ew258 : Word := 0xf300f300f300f300

def ew259 : Word := 0xf500f500f500f500

def ew260 : Word := 0xfa00fa00fa00fa00

def ew261 : Word := 0xfafafafafafafafa

def ew262 : Word := 0xfc00fc00fc00fc00

def ew263 : Word := 0xfcfcfcfcfcfcfcfc

def ew264 : Word := 0xff00000000000000

def ew265 : Word := 0xff000000ff000000

def ew266 : Word := 0xff00ff0000000000

def ew267 : Word := 0xff00ff00ff00ff00

def ew268 : Word := 0xffff000000000000

def ew269 : Word := 0xffff0000ffff0000

def ew270 : Word := 0xffffffff00000000

def labelsBlock0 : Array Nat := #[
  0x1b2c,
  0x2b2c,
  0xf2c,
  0xf34,
  0xf38,
  0x1d34,
  0x2d34,
  0xf1c,
  0x1b4c,
  0x1b64,
  0x1b68,
  0x375c,
  0x1d64,
  0x10a6,
  0x1d54,
  0x37cc
]

def labelsBlock1 : Array Nat := #[
  0x379c,
  0x1d70,
  0x37d4,
  0x1e38,
  0x2e38,
  0x37d8,
  0x1e58,
  0x1e68,
  0x10ae,
  0x1e70,
  0x10b6,
  0x371c,
  0x2b8c,
  0x2ba4,
  0x2ba8,
  0x2da4
]

def labelsBlock2 : Array Nat := #[
  0x107a,
  0x108e,
  0x107e,
  0x10ba,
  0x10aa,
  0x1082,
  0x1b24,
  0x2b24,
  0x1d24,
  0x1b28,
  0x2d24,
  0x2b28,
  0x1b0c,
  0x1092,
  0xf24,
  0x2b0c
]

def labelsBlock3 : Array Nat := #[
  0xf28,
  0x2db0,
  0xf30,
  0x109a,
  0x2ea8,
  0x10c2,
  0x3bcc,
  0x2eb0,
  0x1096,
  0x2d94,
  0x1b60,
  0x1d60,
  0x1b48,
  0x1b44,
  0x109e,
  0x1e60
]

def labelsBlock4 : Array Nat := #[
  0x1d44,
  0x37c4,
  0x37c8,
  0x10b2,
  0x37d0,
  0x2e98,
  0x4100a6,
  0x1e28,
  0x2e28,
  0x3dd4,
  0x1e48,
  0xf0c,
  0x10a2,
  0xf14,
  0x1d50,
  0x10c6
]

def labelsBlock5 : Array Nat := #[
  0x10da,
  0xf18,
  0x10de,
  0x10d6,
  0x1e50,
  0x3be4,
  0x1d14,
  0x2d14,
  0x3be8,
  0x3de4,
  0x3ed8,
  0x1e18,
  0x1d30,
  0x1002,
  0x2e18,
  0x2d30
]

def labelsBlock6 : Array Nat := #[
  0x1012,
  0x1066,
  0x1e30,
  0x2e30,
  0x3df0,
  0x3bc4,
  0x3bc8,
  0x3dc4,
  0x3ee8,
  0x2ba0,
  0x1006,
  0x3ef0,
  0xf20,
  0x1016,
  0x106e,
  0x2da0
]

def labelsBlock7 : Array Nat := #[
  0x1094100d6,
  0x2ea0,
  0x4300c2,
  0x4310c2,
  0x4320c2,
  0x1b5c,
  0x1d5c,
  0x1e5c,
  0x4100d6,
  0x4200d6,
  0x4210d6,
  0x100a,
  0x101a,
  0x1072,
  0x4100aa,
  0x1b40
]

def labelsBlock8 : Array Nat := #[
  0x1b20,
  0x2b20,
  0x1d40,
  0x1e40,
  0x3ec8,
  0x1d20,
  0x2d20,
  0x1e20,
  0x2b88,
  0x2b84,
  0x2e20,
  0x4300c6,
  0x4310c6,
  0x4320c6,
  0x100e,
  0x101e
]

def labelsBlock9 : Array Nat := #[
  0x1076,
  0x2d84,
  0x1080100d6,
  0x1084100d6,
  0x1084200d6,
  0x1f5c,
  0x3dd0,
  0x10c4300c2,
  0x10c8300c2,
  0x2e88,
  0x10c8310c2,
  0x10d5100c2,
  0x10d5200c2,
  0x10d5210c2,
  0x3ed0,
  0x2f9c
]

def labelsBlock10 : Array Nat := #[
  0x10c4300c6,
  0x10c8300c6,
  0x10c8310c6,
  0x436440100c2,
  0x10d5100c6,
  0x10d5100da,
  0x436480200c2,
  0x10d5200c6,
  0x10d5200da,
  0x436484210c2,
  0x10d5210c6,
  0x10d5210da,
  0x10d4100c2,
  0x10d4200c2,
  0x10d4210c2,
  0x3be0
]

def labelsBlock11 : Array Nat := #[
  0x1b08,
  0x1b04,
  0x10d5100de,
  0x10d5200de,
  0x10d5210de,
  0xf00,
  0xf9c,
  0xf5c,
  0x3de0,
  0x2d90,
  0x2e90,
  0x2b08,
  0x2b04,
  0x1d04,
  0x436440100c6,
  0x436440100da
]

def labelsBlock12 : Array Nat := #[
  0x4100c2,
  0x436480200c6,
  0x436480200da,
  0x4200c2,
  0x4210c2,
  0x436484210c6,
  0x436484210da,
  0x3ee0,
  0x4320da,
  0x4310da,
  0x4300da,
  0x1094100c2,
  0x2d04,
  0x436440100de,
  0x4320de,
  0x436480200de
]

def labelsBlock13 : Array Nat := #[
  0x4310de,
  0x4300de,
  0x7300c2,
  0x436484210de,
  0x7310c2,
  0x7320c2,
  0x1e08,
  0x10c6100c2,
  0x10c3100c2,
  0x10ca200c2,
  0x10c3200c2,
  0x10ca210c2,
  0x10c7210c2,
  0x370c,
  0x3714,
  0x3718
]

def labelsBlock14 : Array Nat := #[
  0x2e08,
  0x1080100c2,
  0x10c0100c2,
  0x1084100c2,
  0x10c4100c2,
  0x5100c2,
  0x6100c2,
  0x7100c2,
  0x10c0200c2,
  0x1084200c2,
  0x10c8200c2,
  0x5200c2,
  0x6200c2,
  0x7200c2,
  0x10c4210c2,
  0x10c8210c2
]

def labelsBlock15 : Array Nat := #[
  0x5210c2,
  0x6210c2,
  0x7210c2,
  0x4100c6,
  0x4100da,
  0x1cd6100c2,
  0x1cd7100c2,
  0x4200c6,
  0x4200da,
  0x1cd6200c2,
  0x1cd7200c2,
  0x1c54300c2,
  0x1c94300c2,
  0x4210c6,
  0x4210da,
  0x7300c6
]

def labelsBlock16 : Array Nat := #[
  0x1cd6210c2,
  0x1cd7210c2,
  0x1940310c2,
  0x1c94310c2,
  0x7310c6,
  0x1940320c2,
  0x1944320c2,
  0x7320c6,
  0x374c,
  0x3754,
  0x3758,
  0x1094100da,
  0x1094100c6,
  0x7010a6,
  0x10ca,
  0x4100de
]

def labelsBlock17 : Array Nat := #[
  0x10ce,
  0x10d2,
  0x4200de,
  0x4210de,
  0x378c,
  0x3794,
  0x3798,
  0x1f1c,
  0x2f1c,
  0x1094100de,
  0x1d10,
  0x1e10,
  0x10d4100c6,
  0x10d4100da,
  0x1440100c2,
  0x1080100c6
]

def labelsBlock18 : Array Nat := #[
  0x1080100da,
  0x10c0100c6,
  0x10c0100da,
  0x1084100c6,
  0x1084100da,
  0x10c4100c6,
  0x10c4100da,
  0x5100c6,
  0x5100da,
  0x1cd6100c6,
  0x1cd6100da,
  0x10c6100c6,
  0x10c6100da,
  0x6100c6,
  0x6100da,
  0x1cd7100c6
]

def labelsBlock19 : Array Nat := #[
  0x1cd7100da,
  0x10c3100c6,
  0x10c3100da,
  0x7100c6,
  0x7100da,
  0x10d4200c6,
  0x10d4200da,
  0x1480200c2,
  0x10c0200c6,
  0x10c0200da,
  0x1084200c6,
  0x1084200da,
  0x10c8200c6,
  0x10c8200da,
  0x5200c6,
  0x5200da
]

def labelsBlock20 : Array Nat := #[
  0x1cd6200c6,
  0x1cd6200da,
  0x10ca200c6,
  0x10ca200da,
  0x6200c6,
  0x6200da,
  0x1cd7200c6,
  0x1cd7200da,
  0x10c3200c6,
  0x10c3200da,
  0x7200c6,
  0x7200da,
  0x1c54300c6,
  0x1c54300da,
  0x1c94300c6,
  0x1c94300da
]

def labelsBlock21 : Array Nat := #[
  0x10c4300da,
  0x10c8300da,
  0x7300da,
  0x10d4210c6,
  0x10d4210da,
  0x1484210c2,
  0x10c4210c6,
  0x10c4210da,
  0x10c8210c6,
  0x10c8210da,
  0x5210c6,
  0x5210da,
  0x1cd6210c6,
  0x1cd6210da,
  0x10ca210c6,
  0x10ca210da
]

def labelsBlock22 : Array Nat := #[
  0x6210c6,
  0x6210da,
  0x1cd7210c6,
  0x1cd7210da,
  0x10c7210c6,
  0x10c7210da,
  0x7210c6,
  0x7210da,
  0x1940310c6,
  0x1940310da,
  0x1c94310c6,
  0x1c94310da,
  0x10c8310da,
  0x7310da,
  0x1940320c6,
  0x1940320da
]

def labelsBlock23 : Array Nat := #[
  0x1944320c6,
  0x1944320da,
  0x7320da,
  0x2d10,
  0x2e10,
  0x10d4100de,
  0x421080100c2,
  0x1080100de,
  0x4310c0100c2,
  0x10c0100de,
  0x1084100de,
  0x10c4100de,
  0x1095100c2,
  0x1895100c2,
  0x5100de,
  0x1cd6100de
]

def labelsBlock24 : Array Nat := #[
  0x10c6100de,
  0x6100de,
  0x1cd7100de,
  0x10c3100de,
  0x7100de,
  0x10d4200de,
  0x4320c0200c2,
  0x10c0200de,
  0x1084200de,
  0x10c8200de,
  0x1145200c2,
  0x1d45200c2,
  0x5200de,
  0x1cd6200de,
  0x10ca200de,
  0x6200de
]

def labelsBlock25 : Array Nat := #[
  0x1cd7200de,
  0x10c3200de,
  0x7200de,
  0x1c54300de,
  0x1c94300de,
  0x10c4300de,
  0x10c8300de,
  0x7300de,
  0x10d4210de,
  0x4320c4210c2,
  0x10c4210de,
  0x10c8210de,
  0x1141210c2,
  0x1d41210c2,
  0x5210de,
  0x1cd6210de
]

def labelsBlock26 : Array Nat := #[
  0x10ca210de,
  0x6210de,
  0x1cd7210de,
  0x10c7210de,
  0x7210de,
  0x1940310de,
  0x1c94310de,
  0x10c8310de,
  0x7310de,
  0x1940320de,
  0x1944320de,
  0x7320de,
  0x421080100d6,
  0x1440100c6,
  0x1440100da,
  0x421080100c6
]

def labelsBlock27 : Array Nat := #[
  0x421080100da,
  0x1d00,
  0x1e00,
  0x4310c0100c6,
  0x4310c0100da,
  0x1095100c6,
  0x1095100da,
  0x1895100c6,
  0x1895100da,
  0x1480200c6,
  0x1480200da,
  0x1b00,
  0x4320c0200c6,
  0x4320c0200da,
  0x1145200c6,
  0x1145200da
]

def labelsBlock28 : Array Nat := #[
  0x1d45200c6,
  0x1d45200da,
  0x1484210c6,
  0x1484210da,
  0x4320c4210c6,
  0x4320c4210da,
  0x1141210c6,
  0x1141210da,
  0x1d41210c6,
  0x1d41210da,
  0x1b1c,
  0x1d1c,
  0x1e1c,
  0x37c0,
  0x426440100c2,
  0xf10
]

def labelsBlock29 : Array Nat := #[
  0x1440100de,
  0x421080100de,
  0x4100b2,
  0x4310c0100de,
  0x1095100de,
  0x1895100de,
  0x461480200c2,
  0xf08,
  0x1480200de,
  0x2b80,
  0x4320c0200de,
  0x1145200de,
  0x1d45200de,
  0x460484210c2,
  0xf04,
  0x1484210de
]

def labelsBlock30 : Array Nat := #[
  0x4320c4210de,
  0x1141210de,
  0x1d41210de,
  0x1f2c,
  0x1f34,
  0x1f38,
  0x3bc0,
  0x3dc0,
  0x3ec0,
  0x319,
  0x4100ca,
  0x426440100c6,
  0x426440100da,
  0x2d00,
  0x2e00,
  0x461480200c6
]

def labelsBlock31 : Array Nat := #[
  0x461480200da,
  0x2b00,
  0x460484210c6,
  0x460484210da,
  0x2f2c,
  0x2f34,
  0x2f38,
  0x426440100de,
  0x2d80,
  0x2e80,
  0x461480200de,
  0x460484210de,
  0x1bcc,
  0x2bcc,
  0x1dd4,
  0x2dd4
]

def labelsBlock32 : Array Nat := #[
  0x1ed8,
  0x2ed8,
  0x2b9c,
  0x2b1c,
  0x2d9c,
  0x2d1c,
  0x2e9c,
  0x2e1c,
  0x3b2c,
  0x3d34,
  0x3e38,
  0x341,
  0x345,
  0x34d,
  0x361,
  0x365
]

def labelsBlock33 : Array Nat := #[
  0x36d,
  0x38d,
  0x391,
  0x399,
  0x3b9,
  0x425,
  0x44d,
  0x1f0c,
  0x1f14,
  0x1f18,
  0x1046,
  0x1052,
  0x105e,
  0x103a,
  0x104a,
  0x1056
]

def labelsBlock34 : Array Nat := #[
  0x1062,
  0x103e,
  0x104e,
  0x105a,
  0x106a,
  0x1042,
  0x349,
  0x351,
  0x355,
  0x369,
  0x371,
  0x375,
  0x3a1,
  0x395,
  0x3bd,
  0x3d5
]

def labelsBlock35 : Array Nat := #[
  0x429,
  0x42d,
  0x451,
  0x469,
  0x1054300c6,
  0x1054300c2,
  0x1094300c6,
  0x1094300c2,
  0x4d5,
  0x1140310c6,
  0x1140310c2,
  0x1094310c6,
  0x1094310c2,
  0x1140320c6,
  0x1140320c2,
  0x1144320c6
]

def labelsBlock36 : Array Nat := #[
  0x1144320c2,
  0x3700,
  0x2f0c,
  0x2f14,
  0x2f18,
  0x3b0c,
  0x3d14,
  0x3e18,
  0x91,
  0x99,
  0x7d,
  0x89,
  0xbd,
  0xb5,
  0xf5,
  0xed
]

def labelsBlock37 : Array Nat := #[
  0x13d,
  0x145,
  0x129,
  0x135,
  0x169,
  0x161,
  0x1a1,
  0x199,
  0x285,
  0x28d,
  0x271,
  0x27d,
  0x2b1,
  0x2a9,
  0x2e9,
  0x2e1
]

def labelsBlock38 : Array Nat := #[
  0x70109e,
  0x701096,
  0x4100ce,
  0x39d,
  0x3a5,
  0x3a9,
  0x3b1,
  0x3c5,
  0x3c1,
  0x3c9,
  0x3cd,
  0x3d9,
  0x3e5,
  0x359,
  0x379,
  0x7010aa
]

def labelsBlock39 : Array Nat := #[
  0x445,
  0x45d,
  0x455,
  0x459,
  0x461,
  0x46d,
  0x475,
  0x431,
  0x4d9,
  0x4dd,
  0x515,
  0x51d,
  0x521,
  0x501,
  0x95,
  0x9d
]

def labelsBlock40 : Array Nat := #[
  0xa1,
  0xa5,
  0xc1,
  0xc5,
  0xc9,
  0xd9,
  0xdd,
  0xf9,
  0xfd,
  0x10d,
  0x141,
  0x149,
  0x14d,
  0x151,
  0x16d,
  0x171
]

def labelsBlock41 : Array Nat := #[
  0x175,
  0x185,
  0x189,
  0x1a5,
  0x1a9,
  0x1b9,
  0x3b4c,
  0x1026,
  0x1022,
  0x3d54,
  0x102e,
  0x102a,
  0x3e58,
  0x1036,
  0x1032,
  0x289
]

def labelsBlock42 : Array Nat := #[
  0x291,
  0x295,
  0x299,
  0x2b5,
  0x2b9,
  0x2bd,
  0x2cd,
  0x2d1,
  0x2ed,
  0x2f1,
  0x301,
  0x331,
  0x335,
  0x339,
  0x61009a,
  0x3790
]

def labelsBlock43 : Array Nat := #[
  0x3750,
  0x610092,
  0x410092,
  0x3788,
  0x3748,
  0x61008e,
  0x41008e,
  0x3784,
  0x3744,
  0x7260d4100da,
  0x7260d4100de,
  0x4320d4100c6,
  0x4320d4100c2,
  0x37d,
  0x381,
  0x385
]

def labelsBlock44 : Array Nat := #[
  0x4320c0100c6,
  0x4320c0100c2,
  0x3b5,
  0x4320c4100c6,
  0x4320c4100c2,
  0x3e1,
  0x10c8100c6,
  0x10c8100c2,
  0x389,
  0x3ad,
  0x3d1,
  0x3dd,
  0x3e9,
  0x3ed,
  0x40d,
  0x419
]

def labelsBlock45 : Array Nat := #[
  0x7160d4200da,
  0x7160d4200de,
  0x4310d4200c6,
  0x4310d4200c2,
  0x435,
  0x439,
  0x43d,
  0x4310c0200c6,
  0x4310c0200c2,
  0x449,
  0x4320c4200c6,
  0x4320c4200c2,
  0x10c4200c6,
  0x10c4200c2,
  0x47d,
  0x441
]

def labelsBlock46 : Array Nat := #[
  0x465,
  0x471,
  0x479,
  0x481,
  0x4a1,
  0x4ad,
  0x1054300da,
  0x1054300de,
  0x432c54300c6,
  0x432c54300c2,
  0x4bd,
  0x1094300da,
  0x1094300de,
  0x431c94300c6,
  0x431c94300c2,
  0x4cd
]

def labelsBlock47 : Array Nat := #[
  0x436084300c6,
  0x436084300c2,
  0x431084300c6,
  0x431084300c2,
  0x432084300c6,
  0x432084300c2,
  0x1084300c6,
  0x1084300c2,
  0x7260c4300c6,
  0x7260c4300c2,
  0x4e5,
  0x6610c8300c6,
  0x6610c8300c2,
  0x4ed,
  0x4e1,
  0x4e9
]

def labelsBlock48 : Array Nat := #[
  0x4f1,
  0x6600d4210da,
  0x6600d4210de,
  0x505,
  0x509,
  0x50d,
  0x519,
  0x529,
  0x511,
  0x525,
  0x52d,
  0x54d,
  0x559,
  0x1140310da,
  0x1140310de,
  0x432940310c6
]

def labelsBlock49 : Array Nat := #[
  0x432940310c2,
  0x569,
  0x1094310da,
  0x1094310de,
  0x6600c8310c6,
  0x6600c8310c2,
  0x57d,
  0x581,
  0x1140320da,
  0x1140320de,
  0x1144320da,
  0x1144320de,
  0x1b14,
  0x1b18,
  0x1d0c,
  0x1d18
]

def labelsBlock50 : Array Nat := #[
  0x1e0c,
  0x1e14,
  0x1086,
  0x3710,
  0x3708,
  0x3704,
  0x10be,
  0xf8c,
  0x1b8c,
  0xf4c,
  0x2b4c,
  0xf94,
  0x1d94,
  0xf54,
  0x2d54,
  0xf98
]

def labelsBlock51 : Array Nat := #[
  0x1e98,
  0xf58,
  0x2e58,
  0x79,
  0x85,
  0x81,
  0x8d,
  0xb1,
  0xad,
  0xb9,
  0xd1,
  0xd5,
  0xe9,
  0xe5,
  0xf1,
  0x105
]

def labelsBlock52 : Array Nat := #[
  0x109,
  0x115,
  0x119,
  0xa9,
  0xcd,
  0xe1,
  0x101,
  0x111,
  0x11d,
  0x125,
  0x131,
  0x12d,
  0x139,
  0x15d,
  0x159,
  0x165
]

def labelsBlock53 : Array Nat := #[
  0x17d,
  0x181,
  0x195,
  0x191,
  0x19d,
  0x1b1,
  0x1b5,
  0x1c1,
  0x1c5,
  0x155,
  0x179,
  0x18d,
  0x1ad,
  0x1bd,
  0x1c9,
  0x1f4c
]

def labelsBlock54 : Array Nat := #[
  0x2f8c,
  0x3b8c,
  0x1d1,
  0x1d5,
  0x1d9,
  0x1dd,
  0x1e1,
  0x1e5,
  0x1e9,
  0x1ed,
  0x1f1,
  0x1f5,
  0x1f9,
  0x1fd,
  0x1f54,
  0x2f94
]

def labelsBlock55 : Array Nat := #[
  0x3d94,
  0x205,
  0x209,
  0x20d,
  0x211,
  0x215,
  0x219,
  0x21d,
  0x221,
  0x225,
  0x229,
  0x22d,
  0x231,
  0x1f58,
  0x2f98,
  0x3e98
]

def labelsBlock56 : Array Nat := #[
  0x239,
  0x23d,
  0x241,
  0x245,
  0x249,
  0x24d,
  0x251,
  0x255,
  0x259,
  0x25d,
  0x261,
  0x265,
  0x26d,
  0x279,
  0x275,
  0x281
]

def labelsBlock57 : Array Nat := #[
  0x2a5,
  0x2a1,
  0x2ad,
  0x2c5,
  0x2c9,
  0x2dd,
  0x2d9,
  0x2e5,
  0x2f9,
  0x2fd,
  0x309,
  0x30d,
  0x29d,
  0x2c1,
  0x2d5,
  0x2f5
]

def labelsBlock58 : Array Nat := #[
  0x305,
  0x311,
  0x31d,
  0x321,
  0x325,
  0x41009a,
  0x7010a2,
  0x4100a2,
  0x41009e,
  0x410096,
  0x329,
  0x32d,
  0x33d,
  0x35d,
  0x4010ce,
  0x4200ca
]

def labelsBlock59 : Array Nat := #[
  0x3f5,
  0x3f9,
  0x3fd,
  0x401,
  0x409,
  0x415,
  0x421,
  0x4210ce,
  0x489,
  0x48d,
  0x491,
  0x495,
  0x49d,
  0x4a9,
  0x70108e,
  0x4b9
]

def labelsBlock60 : Array Nat := #[
  0x4c9,
  0x6100a2,
  0x4b5,
  0x4c1,
  0x4c5,
  0x4d1,
  0x4fd,
  0x4100d2,
  0x4210d2,
  0x535,
  0x539,
  0x53d,
  0x541,
  0x549,
  0x555,
  0x565
]

def labelsBlock61 : Array Nat := #[
  0x575,
  0x561,
  0x56d,
  0x571,
  0x579,
  0x591,
  0x59d,
  0x58d,
  0x595,
  0x599,
  0x5a1,
  0x3f1,
  0x405,
  0x411,
  0x41d,
  0x485
]

def labelsBlock62 : Array Nat := #[
  0x499,
  0x4a5,
  0x4b1,
  0x4f5,
  0x4f9,
  0x531,
  0x545,
  0x551,
  0x55d,
  0x585,
  0x589,
  0x5a5,
  0x5a9,
  0x1,
  0x5,
  0x9
]

def labelsBlock63 : Array Nat := #[
  0xd,
  0x11,
  0x15,
  0x19,
  0x1d,
  0x21,
  0x25,
  0x29,
  0x2d,
  0x31,
  0x35,
  0x39,
  0x3d,
  0x41,
  0x45,
  0x49
]

def labelsBlock64 : Array Nat := #[
  0x4d,
  0x51,
  0x55,
  0x59,
  0x5d,
  0x61,
  0x65,
  0x69,
  0x6d,
  0x71,
  0x75,
  0x121,
  0x1cd,
  0x2b14,
  0x1b54,
  0x2b18
]

def labelsBlock65 : Array Nat := #[
  0x1b58,
  0x2d0c,
  0x1d4c,
  0x2d18,
  0x1d58,
  0x2e0c,
  0x1e4c,
  0x2e14,
  0x1e54,
  0x201,
  0x235,
  0x269,
  0x315,
  0x108a,
  0x3740,
  0x3780
]

def labelsBlock66 : Array Nat := #[
  0x5ad
]

def labelsGet (i : Nat) : Nat :=
  if i < 528 then
    if i < 256 then
      if i < 128 then
        if i < 64 then
          if i < 32 then
            if i < 16 then
              labelsBlock0.getD (i-0) 3
            else
              labelsBlock1.getD (i-16) 3
          else
            if i < 48 then
              labelsBlock2.getD (i-32) 3
            else
              labelsBlock3.getD (i-48) 3
        else
          if i < 96 then
            if i < 80 then
              labelsBlock4.getD (i-64) 3
            else
              labelsBlock5.getD (i-80) 3
          else
            if i < 112 then
              labelsBlock6.getD (i-96) 3
            else
              labelsBlock7.getD (i-112) 3
      else
        if i < 192 then
          if i < 160 then
            if i < 144 then
              labelsBlock8.getD (i-128) 3
            else
              labelsBlock9.getD (i-144) 3
          else
            if i < 176 then
              labelsBlock10.getD (i-160) 3
            else
              labelsBlock11.getD (i-176) 3
        else
          if i < 224 then
            if i < 208 then
              labelsBlock12.getD (i-192) 3
            else
              labelsBlock13.getD (i-208) 3
          else
            if i < 240 then
              labelsBlock14.getD (i-224) 3
            else
              labelsBlock15.getD (i-240) 3
    else
      if i < 384 then
        if i < 320 then
          if i < 288 then
            if i < 272 then
              labelsBlock16.getD (i-256) 3
            else
              labelsBlock17.getD (i-272) 3
          else
            if i < 304 then
              labelsBlock18.getD (i-288) 3
            else
              labelsBlock19.getD (i-304) 3
        else
          if i < 352 then
            if i < 336 then
              labelsBlock20.getD (i-320) 3
            else
              labelsBlock21.getD (i-336) 3
          else
            if i < 368 then
              labelsBlock22.getD (i-352) 3
            else
              labelsBlock23.getD (i-368) 3
      else
        if i < 448 then
          if i < 416 then
            if i < 400 then
              labelsBlock24.getD (i-384) 3
            else
              labelsBlock25.getD (i-400) 3
          else
            if i < 432 then
              labelsBlock26.getD (i-416) 3
            else
              labelsBlock27.getD (i-432) 3
        else
          if i < 480 then
            if i < 464 then
              labelsBlock28.getD (i-448) 3
            else
              labelsBlock29.getD (i-464) 3
          else
            if i < 496 then
              labelsBlock30.getD (i-480) 3
            else
              if i < 512 then
                labelsBlock31.getD (i-496) 3
              else
                labelsBlock32.getD (i-512) 3
  else
    if i < 800 then
      if i < 656 then
        if i < 592 then
          if i < 560 then
            if i < 544 then
              labelsBlock33.getD (i-528) 3
            else
              labelsBlock34.getD (i-544) 3
          else
            if i < 576 then
              labelsBlock35.getD (i-560) 3
            else
              labelsBlock36.getD (i-576) 3
        else
          if i < 624 then
            if i < 608 then
              labelsBlock37.getD (i-592) 3
            else
              labelsBlock38.getD (i-608) 3
          else
            if i < 640 then
              labelsBlock39.getD (i-624) 3
            else
              labelsBlock40.getD (i-640) 3
      else
        if i < 720 then
          if i < 688 then
            if i < 672 then
              labelsBlock41.getD (i-656) 3
            else
              labelsBlock42.getD (i-672) 3
          else
            if i < 704 then
              labelsBlock43.getD (i-688) 3
            else
              labelsBlock44.getD (i-704) 3
        else
          if i < 752 then
            if i < 736 then
              labelsBlock45.getD (i-720) 3
            else
              labelsBlock46.getD (i-736) 3
          else
            if i < 768 then
              labelsBlock47.getD (i-752) 3
            else
              if i < 784 then
                labelsBlock48.getD (i-768) 3
              else
                labelsBlock49.getD (i-784) 3
    else
      if i < 928 then
        if i < 864 then
          if i < 832 then
            if i < 816 then
              labelsBlock50.getD (i-800) 3
            else
              labelsBlock51.getD (i-816) 3
          else
            if i < 848 then
              labelsBlock52.getD (i-832) 3
            else
              labelsBlock53.getD (i-848) 3
        else
          if i < 896 then
            if i < 880 then
              labelsBlock54.getD (i-864) 3
            else
              labelsBlock55.getD (i-880) 3
          else
            if i < 912 then
              labelsBlock56.getD (i-896) 3
            else
              labelsBlock57.getD (i-912) 3
      else
        if i < 992 then
          if i < 960 then
            if i < 944 then
              labelsBlock58.getD (i-928) 3
            else
              labelsBlock59.getD (i-944) 3
          else
            if i < 976 then
              labelsBlock60.getD (i-960) 3
            else
              labelsBlock61.getD (i-976) 3
        else
          if i < 1024 then
            if i < 1008 then
              labelsBlock62.getD (i-992) 3
            else
              labelsBlock63.getD (i-1008) 3
          else
            if i < 1040 then
              labelsBlock64.getD (i-1024) 3
            else
              if i < 1056 then
                labelsBlock65.getD (i-1040) 3
              else
                labelsBlock66.getD (i-1056) 3

def decodeHints (enc i : Nat) := labelsGet ((enc >>> (i * 11)) % 2048)

def localHints (stride dict enc i : Nat) : Nat :=
  let q := (enc >>> (stride*i)) % (2^stride)
  labelsGet ((dict >>> (11*q)) % 2048)

def viewsBlock0 : Array View := #[
  ⟨0xaa00aa00,⟨9,by decide⟩,0xa8008000,[ew18,ew21,ew23],3,decodeHints 0x7da00c0102e0000981402e⟩,
  ⟨0xcc00cc00,⟨10,by decide⟩,0xc8008000,[ew18,ew28,ew30],3,decodeHints 0x7dc010010300000a423830⟩,
  ⟨0xf000f000,⟨12,by decide⟩,0xe0008000,[ew21,ew28,ew34],3,decodeHints 0x7de0100183200a17031032⟩,
  ⟨0xff000000,⟨24,by decide⟩,0xe8000000,[ew23,ew30,ew34],3,decodeHints 0x7e00280483a0180ec1f83a⟩,
  ⟨0xaa000000aa00,⟨9,by decide⟩,0xa80000008000,[ew59,ew61,ew62],3,decodeHints 0x7e200c0102e00209c1502e⟩,
  ⟨0xcc000000cc00,⟨10,by decide⟩,0xc80000008000,[ew59,ew66,ew67],3,decodeHints 0x7e4010010300020ac24030⟩,
  ⟨0xf0000000f000,⟨12,by decide⟩,0xe00000008000,[ew61,ew66,ew70],3,decodeHints 0x7e60100183200c17c31832⟩,
  ⟨0xff0000000000,⟨40,by decide⟩,0xe80000000000,[ew62,ew67,ew70],3,decodeHints 0x7e80780e86903e1bc38869⟩,
  ⟨0x88008888008800,⟨11,by decide⟩,0x80000088008000,[ew77,ew80,ew81],3,localHints 2 0x7ea2d800002 0xc484⟩,
  ⟨0x88880000888800,⟨11,by decide⟩,0x80880000008000,[ew78,ew79,ew82],3,localHints 2 0x7ec2dc00802 0xc844⟩,
  ⟨0xa000a0a000a000,⟨13,by decide⟩,0x800000a0008000,[ew77,ew84,ew85],3,localHints 2 0x7ee2d802803 0xc484⟩,
  ⟨0xa0a00000a0a000,⟨13,by decide⟩,0x80a00000008000,[ew78,ew83,ew86],3,localHints 2 0x7f02dc03003 0xc844⟩,
  ⟨0xc000c0c000c000,⟨14,by decide⟩,0x800000c0008000,[ew77,ew88,ew89],3,localHints 2 0x7f22d809804 0xc484⟩,
  ⟨0xc0c00000c0c000,⟨14,by decide⟩,0x80c00000008000,[ew78,ew87,ew90],3,localHints 2 0x7f42dc0a004 0xc844⟩,
  ⟨0x880088008800880,⟨7,by decide⟩,0x880080008000000,[ew91,ew92,ew93],3,decodeHints 0x7f61d4001ca00280c0d9ca⟩,
  ⟨0x2080208020802080,⟨7,by decide⟩,0x2080200020000000,[ew109,ew110,ew111],3,decodeHints 0x7f81d8029cb00c8140d9cb⟩
]

def viewsBlock1 : Array View := #[
  ⟨0x4080408040804080,⟨7,by decide⟩,0x4080400040000000,[ew131,ew132,ew133],3,decodeHints 0x7fa1dc099cc02881c0d9cc⟩,
  ⟨0x8080080880800808,⟨3,by decide⟩,0x8080080080000000,[ew159,ew171,ew172],3,decodeHints 0x7fc254f1a170020bc6ea17⟩,
  ⟨0x8080202080802020,⟨5,by decide⟩,0x8080200080000000,[ew160,ew171,ew173],3,decodeHints 0x7fe254f221800c15c6f218⟩,
  ⟨0x8080404080804040,⟨6,by decide⟩,0x8080400080000000,[ew161,ew171,ew174],3,decodeHints 0x800254f2a190281786fa19⟩,
  ⟨0x8080808008080808,⟨3,by decide⟩,0x8080800008000000,[ew162,ew168,ew175],3,decodeHints 0x8020200002c3e89086e82c⟩,
  ⟨0x8080808020202020,⟨5,by decide⟩,0x8080800020000000,[ew163,ew169,ew175],3,decodeHints 0x804038028563ea90c6f056⟩,
  ⟨0x8080808040404040,⟨6,by decide⟩,0x8080800040000000,[ew164,ew170,ew175],3,decodeHints 0x8060580985b3ec9106f85b⟩,
  ⟨0x8888000000008888,⟨3,by decide⟩,0x8880000000008000,[ew167,ew180,ew182],3,decodeHints 0x8080080384b0363752284b⟩,
  ⟨0xa0a000000000a0a0,⟨5,by decide⟩,0xa080000000008000,[ew167,ew196,ew198],3,decodeHints 0x80a00c0384d0363792304d⟩,
  ⟨0xaaaa000000000000,⟨49,by decide⟩,0xa880000000000000,[ew182,ew198,ew210],3,decodeHints 0x80c0480784106c19433841⟩,
  ⟨0xc0c000000000c0c0,⟨6,by decide⟩,0xc080000000008000,[ew167,ew222,ew224],3,decodeHints 0x80e0100385103637d23851⟩,
  ⟨0xcccc000000000000,⟨50,by decide⟩,0xc880000000000000,[ew182,ew224,ew236],3,decodeHints 0x8100540784206c19842042⟩,
  ⟨0xf0f0000000000000,⟨52,by decide⟩,0xe080000000000000,[ew198,ew224,ew250],3,decodeHints 0x812054090440922584f044⟩,
  ⟨0xff00000000000000,⟨56,by decide⟩,0xe800000000000000,[ew210,ew236,ew250],3,decodeHints 0x8141602a8af0b22e0638af⟩,
  ⟨0xaaaaaaaa,⟨1,by decide⟩,0xa8008000,[ew19,ew22,ew24,ew25],4,decodeHints 0xba00c0102e00e134259de0000981402e0582c45e9de⟩,
  ⟨0xcccccccc,⟨2,by decide⟩,0xc8008000,[ew19,ew29,ew31,ew32],4,decodeHints 0xd40100103000e144259d70000a4238300582c06b1d7⟩
]

def viewsBlock2 : Array View := #[
  ⟨0xf0f0f0f0,⟨4,by decide⟩,0xe0008000,[ew22,ew29,ew35,ew36],4,decodeHints 0xf60100183200e144269cf00a170310320ac4688d9cf⟩,
  ⟨0xff00ff00,⟨8,by decide⟩,0xe8008000,[ew24,ew31,ew35,ew38],6,decodeHints 0x816010018320040c01706c0000a4130800502144386c⟩,
  ⟨0xff000000ff00,⟨8,by decide⟩,0xe80000008000,[ew63,ew68,ew71,ew73],6,decodeHints 0x818010018320040c01706c0020ac138810542184506c⟩,
  ⟨0xaa00aa00aa00aa0,⟨5,by decide⟩,0x880080008000000,[ew94,ew95,ew97,ew98],4,decodeHints 0x43a0243ac0e000098e531c00209d01c0d036378e531c⟩,
  ⟨0xcc00cc00cc00cc0,⟨6,by decide⟩,0x880080008000000,[ew94,ew101,ew103,ew104],4,decodeHints 0x43a0283ac100000a4e531d0020ad01c0f03637ce531d⟩,
  ⟨0x2288228822882288,⟨3,by decide⟩,0x2080200020000000,[ew112,ew113,ew115,ew116],4,decodeHints 0x4420303b41200a0a0e5b1e00c0a902c11036374e5b1e⟩,
  ⟨0x30c030c030c030c0,⟨6,by decide⟩,0x2080200020000000,[ew112,ew122,ew124,ew125],4,decodeHints 0x4420443b41400a170e5b1f00c17d02c1303637ce5b1f⟩,
  ⟨0x4488448844884488,⟨3,by decide⟩,0x4080400040000000,[ew134,ew135,ew137,ew138],4,decodeHints 0x44a05c3bc1602611ce632002812103c15036374e6320⟩,
  ⟨0x50a050a050a050a0,⟨5,by decide⟩,0x4080400040000000,[ew134,ew144,ew146,ew147],4,decodeHints 0x44a0643bc18026188e632102818d03c17036378e6321⟩,
  ⟨0x8888888888888888,⟨3,by decide⟩,0x8880880088008000,[ew176,ew181,ew183,ew185],5,decodeHints 0x8320080384b0000081604b0020081784b0363741604b⟩,
  ⟨0xa0a0a0a0a0a0a0a0,⟨5,by decide⟩,0xa080a000a0008000,[ew176,ew197,ew199,ew201],5,decodeHints 0x83400c0384d00a00c2b04d00c00c2b84d0363782b04d⟩,
  ⟨0xaa00aa00aa00aa00,⟨9,by decide⟩,0xa800a800a8008000,[ew181,ew197,ew211,ew212],4,decodeHints 0xba00c0102e0000981402e00209c1502e0000981402e⟩,
  ⟨0xc0c0c0c0c0c0c0c0,⟨6,by decide⟩,0xc080c000c0008000,[ew176,ew223,ew225,ew227],5,decodeHints 0x836010038510260102d8510280102f05103637c2d851⟩,
  ⟨0xcc00cc00cc00cc00,⟨10,by decide⟩,0xc800c800c8008000,[ew181,ew223,ew237,ew238],4,decodeHints 0xd4010010300000a4238300020ac240300000a423830⟩,
  ⟨0xf000f000f000f000,⟨12,by decide⟩,0xe000e000e0008000,[ew197,ew223,ew251,ew252],4,decodeHints 0xf60100183200a1703103200c17c3183200a17031032⟩,
  ⟨0xffff000000000000,⟨48,by decide⟩,0xe880000000000000,[ew214,ew240,ew254,ew264],6,decodeHints 0x8380540904401e108209cd06c198329e60ce79cf41cd⟩
]

def viewsBlock3 : Array View := #[
  ⟨0xffffffff,⟨0,by decide⟩,0xe8008000,[ew26,ew33,ew37,ew39,ew40],7,decodeHints 0x644010018320040c01706c00e144269cf09675cef0b50000a4130800502144386c0582c0589bb17a6c4d90b5⟩,
  ⟨0xffff0000ffff,⟨0,by decide⟩,0xe80000008000,[ew64,ew69,ew72,ew74,ew75],7,decodeHints 0x83a010018320040c01706c00e144269cf09675cef0b50020ac138810542184506c05e2ec5e1f11987b4f70b5⟩,
  ⟨0x9999999999999999,⟨0,by decide⟩,0x8880880088008000,[ew188,ew191,ew192,ew193,ew194],6,decodeHints 0x1a0c80106c00e73c258b50002000106c0586ec258b50022040106c05e7c4258b5036c8c6ea410586ec258b5⟩,
  ⟨0xa5a5a5a5a5a5a5a5,⟨0,by decide⟩,0xa080a000a0008000,[ew178,ew204,ew206,ew207,ew208],6,decodeHints 0x4800c1806c00e134eb8b500a00c4286c0ac134d88b500c00c4306c0ae134f68b5036379922410ac134d88b5⟩,
  ⟨0xc3c3c3c3c3c3c3c3,⟨0,by decide⟩,0xc080c000c0008000,[ew177,ew230,ew231,ew232,ew233],6,decodeHints 0x860101706c00e144ef0b50260104386c0b6144d90b50280104506c0bc144f70b503637d92a410b6144d90b5⟩,
  ⟨0xff00ff00ff00ff00,⟨8,by decide⟩,0xe800e800e8008000,[ew213,ew239,ew253,ew265,ew266],7,decodeHints 0x644010018320040c01706c0000a4130800502144386c0020ac138810542184506c0000a4130800502144386c⟩,
  ⟨0xffff0000ffff0000,⟨16,by decide⟩,0xe8800000e8000000,[ew215,ew241,ew255,ew265,ew268],7,decodeHints 0x64c0280483a0180ec1f83a0100f01e87f0802084187f01642884ab0210ad15c41e0100f01e87f0802084187f⟩,
  ⟨0xffffffff00000000,⟨32,by decide⟩,0xe880e80000000000,[ew216,ew242,ew256,ew266,ew268],7,decodeHints 0x64c0780e86903e1bc38869038220449d91227e0fc9d90204588aaaf228acd5bc1f038220449d91227e0fc9d9⟩,
  ⟨0xffffffffffffffff,⟨0,by decide⟩,0xe880e800e8008000,[ew217,ew243,ew257,ew267,ew269,ew270],10,decodeHints 0x840010018320040c01706c00e144269cf09675cef0b50000a4130800502144386c0582c0589bb17a6c4d90b50020ac138810542184506c05e2ec5e1f11987b4f70b503637c6f3231bac9192a410582c0589bb17a6c4d90b5⟩
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
  ⟨0,3,[ew18,ew21,ew23],localHints 4 0x2804c0000282e00600806009 0x258168155262367057066353024314322010⟩,
  ⟨1,3,[ew18,ew28,ew30],localHints 4 0x47052000098300080080b80a 0x258168155262367057066353024314322010⟩,
  ⟨2,3,[ew21,ew28,ew34],localHints 4 0x620b80140983200800c0c811 0x258168155262367057066353024314322010⟩,
  ⟨3,3,[ew23,ew30,ew34],localHints 4 0x3f0760300b83a0140240c811 0x258168155262367057066353024314322010⟩,
  ⟨4,3,[ew59,ew61,ew62],localHints 4 0x2a04e0040302e0060080f81d 0x258168155262367057066353024314322010⟩,
  ⟨5,3,[ew59,ew66,ew67],localHints 4 0x480560040a0300080081a01e 0x258168155262367057066353024314322010⟩,
  ⟨6,3,[ew61,ew66,ew70],localHints 4 0x630be0180a03200800c1b831 0x258168155262367057066353024314322010⟩,
  ⟨7,3,[ew62,ew67,ew70],localHints 4 0x710de07c1a06903c0741b831 0x258168155262367057066353024314322010⟩,
  ⟨8,3,[ew77,ew80,ew81],localHints 3 0x6502d9939fc01e04000002 0x30ad94e7118391ea2008325a408⟩,
  ⟨9,3,[ew78,ew79,ew82],localHints 3 0x65402c0080f16eca4fe802 0x799b4eeed184b66c280c4263408⟩,
  ⟨10,3,[ew77,ew84,ew85],localHints 3 0x6582d9959fe02404002803 0x30ad94e7118391ea2008325a408⟩,
  ⟨11,3,[ew78,ew83,ew86],localHints 3 0x65c02c0301216ecb4ff803 0x799b4eeed184b66c280c4263408⟩,
  ⟨12,3,[ew77,ew88,ew89],localHints 3 0x6602d997a0002a04009804 0x30ad94e7118391ea2008325a408⟩,
  ⟨13,3,[ew78,ew87,ew90],localHints 3 0x66402c0a01516ecc500804 0x799b4eeed184b66c280c4263408⟩,
  ⟨14,3,[ew91,ew92,ew93],localHints 4 0x1b406004059ca0ea00008202 0x258168155262367057066353024314322010⟩,
  ⟨15,3,[ew109,ew110,ew111],localHints 4 0x1b40a018059cb0ec01408204 0x258168155262367057066353024314322010⟩
]

def nodesBlock1 : Array Node := #[
  ⟨16,3,[ew131,ew132,ew133],localHints 4 0x1b40e050059cc0ee04c08206 0x258168155262367057066353024314322010⟩,
  ⟨17,3,[ew159,ew171,ew172],localHints 4 0xdd05e00405a1712a78c8a01c 0x258168155262367057066353024314322010⟩,
  ⟨18,3,[ew160,ew171,ew173],localHints 4 0xde0ae01805a1812a7908a839 0x258168155262367057066353024314322010⟩,
  ⟨19,3,[ew161,ew171,ew174],localHints 4 0xdf0bc05005a1912a7948b045 0x258168155262367057066353024314322010⟩,
  ⟨20,3,[ew162,ew168,ew175],localHints 4 0xdd4847d08402c0100000809f 0x258168155262367057066353024314322010⟩,
  ⟨21,3,[ew163,ew169,ew175],localHints 4 0xde4867d48485601c0140809f 0x258168155262367057066353024314322010⟩,
  ⟨22,3,[ew164,ew170,ew175],localHints 4 0xdf4887d88505b02c04c0809f 0x258168155262367057066353024314322010⟩,
  ⟨23,3,[ew167,ew180,ew182],localHints 4 0x2451ba06d0404b00401c1b00f 0x258168155262367057066353024314322010⟩,
  ⟨24,3,[ew167,ew196,ew198],localHints 4 0x2461bc06d0484d00601c24812 0x258168155262367057066353024314322010⟩,
  ⟨25,3,[ew182,ew198,ew210],localHints 4 0x670ca0d82484102403c2c855 0x258168155262367057066353024314322010⟩,
  ⟨26,3,[ew167,ew222,ew224],localHints 4 0x2471be06d0505100801c2d015 0x258168155262367057066353024314322010⟩,
  ⟨27,3,[ew182,ew224,ew236],localHints 4 0x840cc0d82d04202a03c34058 0x258168155262367057066353024314322010⟩,
  ⟨28,3,[ew198,ew224,ew250],localHints 4 0x9e12c1242d04402a04835864 0x258168155262367057066353024314322010⟩,
  ⟨29,3,[ew210,ew236,ew250],localHints 4 0xc7170164340af0b015435864 0x258168155262367057066353024314322010⟩,
  ⟨33,3,[ew15,ew24,ew31,ew35],decodeHints 0x5c0b8010090600c00100a0640c8018110500a00280204c098000030520a400004⟩,
  ⟨33,4,[ew16,ew24,ew31,ew35,ew38],decodeHints 0x1402800a000130260000141f83f02e0241482900004c1d83b0180281d03a0120459980011c0000100200600c02004⟩
]

def nodesBlock2 : Array Node := #[
  ⟨33,4,[ew12,ew24,ew31,ew35,ew38],localHints 4 0x4c0b8148130600e8028000180080c80900604405004 0x6896ff89ee64dd8cbb61aa4298987654332100⟩,
  ⟨33,3,[ew13,ew24,ew31,ew38],decodeHints 0x4c098000030520a4000040640c8018110500a00280205c0b8010090600c00100a⟩,
  ⟨33,4,[ew17,ew24,ew31,ew35,ew38],decodeHints 0x1402800a0083106202600c1702e0040302e05c00a0101803000405c19032006044000006680083d80201200c05004⟩,
  ⟨33,4,[ew14,ew24,ew31,ew35,ew38],localHints 4 0x4c0b81483002e0c8028000180080c80900604405004 0x6876ff83ee67dd80cc6baa3298767653432010⟩,
  ⟨33,3,[ew18,ew21,ew28,ew38],localHints 4 0x870262140103b100000028030ba0103503a 0xccb6aa569938776544302210⟩,
  ⟨33,4,[ew18,ew21,ew31,ew35,ew38],localHints 5 0x470c40fd2405c004064088290000140b87b0060103500a 0x840c73bce6738ad61cc75ad2a0a508398052006310820⟩,
  ⟨33,3,[ew18,ew23,ew30,ew35],localHints 4 0x21c428000d8008060620ba17035032 0xaa4699268832776504300210⟩,
  ⟨33,4,[ew18,ew23,ew31,ew35,ew38],localHints 5 0x470c49241f8000760640881311c0c00100c06402835004 0x841057bd0e2b4a4631652152a0a408380c62906300820⟩,
  ⟨33,4,[ew18,ew24,ew28,ew35,ew38],decodeHints 0x500a0028000c4000098000040080005c00004c1d83b018920088190ba044130260000140480c0f6024018030ba02402004⟩,
  ⟨33,4,[ew18,ew24,ew30,ew35,ew38],decodeHints 0x500a0028020000001f80202e0082e05c00a9240103b00405c088190ba0440180511c00c1702e004030018090ba00c19032⟩,
  ⟨33,5,[ew18,ew24,ew31,ew35,ew38],localHints 5 0xa03128107ea002e27f0260ed3f01766c2380024b00acd43d8024940300c8030d417408804 0x85e8cdd196b435036b4abc95adc2d63420a6b9508b18c26b433a85ada4e6242030905088c20110465288427b5ae5adcd6b16b521093192841cc6108822904300820⟩,
  ⟨33,4,[ew8,ew24,ew31,ew35,ew38],localHints 4 0x500b8148130760c80000502e0300100900602808804 0xff899893ee36dd9cbb62aa3198987655432100⟩,
  ⟨33,3,[ew9,ew24,ew35,ew38],decodeHints 0x500a0028020520a4000040600c00100a04c0980000305c0b8010090640c801811⟩,
  ⟨33,4,[ew20,ew24,ew31,ew35,ew38],decodeHints 0x238470260081302600000c1702e004024148290000101803000402819032006064028000180099b8030d400c08804⟩,
  ⟨33,4,[ew11,ew24,ew31,ew35,ew38],localHints 4 0xa01705c00a0c01901900005c0600201200c05004 0xeeb42b32dd43ccb0aa41992877645432321010⟩,
  ⟨33,3,[ew21,ew23,ew31,ew34],localHints 4 0x4388000611c2e86c0120a43d830 0x996726528827065044030210⟩
]

def nodesBlock3 : Array Node := #[
  ⟨33,4,[ew21,ew23,ew31,ew35,ew38],localHints 4 0x8e9303103f05205c1d01311c0c0190030120283d804 0xff8edd84c443bb2a12943408706655430210⟩,
  ⟨33,4,[ew21,ew24,ew28,ew31,ew38],decodeHints 0x4c0980000508e11c0980000600c1482900004c1d03a012920050170ba0281402800a000060090d4024010020ba03002004⟩,
  ⟨33,4,[ew21,ew24,ew31,ew34,ew38],decodeHints 0x8e11c1302600000c0183f02e00c14829000930050170ba0280183a0060640100011c0080100c0ba0081702e00402418030⟩,
  ⟨33,5,[ew21,ew24,ew31,ew35,ew38],localHints 5 0x11d4202607ea0c14a820260e93f01967223802a4d00005c013380d400d250090f617405004 0x36e94bd29adcad665e08dc116b334c455cc331946258825d433a856ba4e611046a50842118c184826346107b5ae5adcd6b16b109225250631c84398c52104300820⟩,
  ⟨33,4,[ew7,ew24,ew31,ew35,ew38],localHints 4 0x500980485c06005c1d01300a0000100c0060440200a 0xff75ee87545dcc71bb5a911287665454331210⟩,
  ⟨33,4,[ew10,ew24,ew31,ew35,ew38],localHints 4 0x140260520ec19019026014000020060240200a 0xdd75cc532332bb51a110993875654432321010⟩,
  ⟨33,4,[ew23,ew24,ew30,ew31,ew35],decodeHints 0x5c0b80100c08e11c098020c41881803000405c19032006924020130ba0101402800a008028030d400c000000ba0142e05c⟩,
  ⟨33,4,[ew23,ew24,ew31,ew34,ew35],decodeHints 0x8e11c1702e0040243106202600c18030004930020130ba01019032006064000020f6008000050ba0001302600000c14829⟩,
  ⟨33,5,[ew23,ew24,ew31,ew35,ew38],localHints 5 0x11d4306250a0b81828202e0c93f8190260019d87b0189340133a0d40252580311c0282e804 0x97e963d2def4e5247e0c3c19ef25c864d88bb112932cc00806f784210a6a09d4094d273092408480424610085c17b9ab5b12962d6a4a50631c84398c52102310400⟩,
  ⟨33,4,[ew3,ew24,ew31,ew35,ew38],localHints 4 0x500980283f0600c80001301805c0100903200c05004 0xffd9ee9dcc649890bb06aa0398987655432210⟩,
  ⟨33,3,[ew4,ew31,ew35,ew38],decodeHints 0x500a00280204c0980000305c0b8010090520a4000040600c00100a0640c801811⟩,
  ⟨33,4,[ew24,ew27,ew31,ew35,ew38],decodeHints 0x1402800a0081302600000c1702e0040240980002e0080c8030520a4000040600c00100a0640c801811008cf02e804⟩,
  ⟨33,4,[ew6,ew24,ew31,ew35,ew38],localHints 4 0x2386205c04c180320220000600201200c05004 0xdda4cca2bb430a109941882766545432321010⟩,
  ⟨33,3,[ew24,ew28,ew30,ew34],localHints 4 0x3507b10a0a0400260081b01700a 0x469416911481776355432210⟩,
  ⟨33,4,[ew24,ew28,ew30,ew35,ew38],localHints 4 0x509381300c11c0b83d85c00a0ec1d0090080c80180a 0xff7edd4c9417b1aa14918873633035432210⟩,
  ⟨33,4,[ew24,ew28,ew31,ew34,ew38],localHints 5 0x2804c9380488e0d40b8148000760301d0040220c00100a 0x841ef439a65b428604265854a4a50421cc42908310820⟩
]

def nodesBlock4 : Array Node := #[
  ⟨33,5,[ew24,ew28,ew31,ew35,ew38],localHints 5 0xa14402650e0159f08e49e0080182900004c1d87b018a0c1d06a012a0008b3d0ba0112500a 0xcb696fd2ed6cbde87e0f6c1defbdac741d8b5a108ab9d47be8e74def422435c90c88cf113e007400f789c202da26084b1014029d2240847114c500c022084310020⟩,
  ⟨33,4,[ew2,ew24,ew31,ew35,ew38],localHints 4 0x501881700c0520281d0050260000101703200c04804 0xff85ee72dd5cbb87545a292387665454232100⟩,
  ⟨33,4,[ew5,ew24,ew31,ew35,ew38],localHints 4 0x4704c0fc14832022014000020060240200a 0xcc65bb53a33299510110883765654432321010⟩,
  ⟨33,4,[ew24,ew30,ew31,ew34,ew35],localHints 5 0x2805c9383d86a04c0c00100a0b8014190030220a400004 0x841ef4b886610296a4266056b5292839cc02948310820⟩,
  ⟨33,5,[ew24,ew30,ew31,ew35,ew38],localHints 5 0xa14482e50e030003400f693c0488e0b80154283000405c35032006a0408b3f0ba02925804 0xb76ad0d59ce5e56749e0e725294af07b60eb5ded64a6a37568a54d6b9a9525ad3088ce7039e283c4e701a012d805300b5894229d004a007394c500c022084310020⟩,
  ⟨33,4,[ew0,ew24,ew31,ew35,ew38],localHints 4 0x8e098170090b80ec088130000140b80201800c0c804 0xff84ee72dd4c7b784a45212978764543212100⟩,
  ⟨33,4,[ew1,ew24,ew31,ew35,ew38],localHints 4 0x280c40fc148300140000280201800c02011 0xcc546b654a4399618847011065654343221010⟩,
  ⟨33,5,[ew24,ew31,ew34,ew35,ew38],localHints 5 0x14060265120b9440096841a92788e0520014307b0600094200a6821752683200800c0c811 0xa62a0e7318c6334673990c994a13b148628e70ae2a2ac26584a552b4148419843208a221b9e883d0e70da34296362c6a52128198603800600ca3008830906210020⟩,
  ⟨33,6,[ew24,ew31,ew35,ew38],localHints 5 0x50d201334700a0b9a300c0122381480068a04c3d830004d100b80a0d40c82e804006d0c0c811 0x6aefb9521b6d2f7d2e0b38e1994ef93ce10c0ee33cd7668e9638d6bace9329211921d12a210791c42a16c6912c2916b5212828066390262906310020⟩,
  ⟨34,3,[ew56,ew63,ew68,ew71],decodeHints 0x5c0b80101d0600c00101e0640c8018310540a80300204e09c008030560ac00804⟩,
  ⟨34,4,[ew57,ew63,ew68,ew71,ew73],decodeHints 0x1502a00c00413827002018388710680741582b0020503786f03e0783486903a0c5a480111e0040100200600c02004⟩,
  ⟨34,4,[ew53,ew63,ew68,ew71,ew73],localHints 4 0x4e0b8158140601a40300103e0081b81d0060c40f004 0x6896ff89ee64dd8cbb61aa4298987654332100⟩,
  ⟨34,3,[ew54,ew63,ew68,ew73],decodeHints 0x4e09c008030560ac008040640c8018310540a80300205c0b80101d0600c00101e⟩,
  ⟨34,4,[ew58,ew63,ew68,ew71,ew73],decodeHints 0x1502a00c0083186302800c1702e00407c2f85f00c010180300040d0190320060c4008016940083e00203a00c0f004⟩,
  ⟨34,4,[ew55,ew63,ew68,ew71,ew73],localHints 4 0x4e0b8158300680c80300103e0081b81d0060c40f004 0x6876ff83ee67dd80cc6baa3298767653432010⟩,
  ⟨34,3,[ew59,ew61,ew66,ew73],localHints 4 0x8a0282180106f102004030030c001036869 0xccb6aa569938776544302210⟩
]

def nodesBlock5 : Array Node := #[
  ⟨34,4,[ew59,ew61,ew68,ew71,ew73],localHints 5 0x480c61c52805f0040dc1882b0020181a07c0060103681e 0x840c73bce6738ad61cc75ad2a0a508398052006310820⟩,
  ⟨34,3,[ew59,ew62,ew67,ew71],localHints 4 0x228430010d80080f8630c017c36832 0xaa4699268832776504300210⟩,
  ⟨34,4,[ew59,ew62,ew68,ew71,ew73],localHints 5 0x480c6944388010de0dc1881411e0c00101f06407836804 0x841057bd0e2b4a4631652152a0a408380c62906300820⟩,
  ⟨34,4,[ew59,ew63,ew66,ew71,ew73],decodeHints 0x540a8030010c60040a0010040080085f0020503786f03e940188370c00c4138270020180e81f0f8074018030c007402004⟩,
  ⟨34,4,[ew59,ew63,ew67,ew71,ew73],decodeHints 0x540a803002002004388020680082f85f00c9440106f0040d0188370c00c40180611e00c1702e00407c0181d0c000c19032⟩,
  ⟨34,5,[ew59,ew63,ew68,ew71,ew73],localHints 5 0xa831a8d0e2a302fa8b0281bd4503469823c00a5300cd2c3e0024a407c1b8030da18018804 0x85e8cdd196b435036b4abc95adc2d63420a6b9508b18c26b433a85ada4e6242030905088c20110465288427b5ae5adcd6b16b521093192841cc6108822904300820⟩,
  ⟨34,4,[ew49,ew63,ew68,ew71,ew73],localHints 4 0x540b8158140de0c80080606807c0101d00607818804 0xff899893ee36dd9cbb62aa3198987655432100⟩,
  ⟨34,3,[ew50,ew63,ew71,ew73],decodeHints 0x540a8030020560ac008040600c00101e04e09c0080305c0b80101d0640c801831⟩,
  ⟨34,4,[ew60,ew63,ew68,ew71,ew73],decodeHints 0x240480280081382700200c1702e0040741582b00201018030004078190320060dc0300103e009a68030da00c18804⟩,
  ⟨34,4,[ew52,ew63,ew68,ew71,ew73],localHints 4 0xa81705f00c0c0190370020d00f80203a00c0f004 0xeeb42b32dd43ccb0aa41992877645432321010⟩,
  ⟨34,3,[ew61,ew62,ew68,ew70],localHints 4 0x450810061203006c03a0ac3e030 0x996726528827065044030210⟩,
  ⟨34,4,[ew61,ew62,ew68,ew71,ew73],localHints 4 0x90950318710560d03481411e0c01900303a0783e004 0xff8edd84c443bb2a12943408706655430210⟩,
  ⟨34,4,[ew61,ew63,ew66,ew68,ew73],decodeHints 0x4e09c008060901200a00100600c1582b0020503486903a9400f0340c00781502a00c0040f81d0da074010020c007c02004⟩,
  ⟨34,4,[ew61,ew63,ew68,ew70,ew73],decodeHints 0x901201382700200c0187106800c1582b0029500f0340c0078018690060dc0100111e0080101f0c00081702e00407418030⟩,
  ⟨34,5,[ew61,ew63,ew68,ew71,ew73],localHints 5 0x121480270e2a3c15a8e0281a54503769e23c032550020d00134e0da00d2901d0f81800f004 0x36e94bd29adcad665e08dc116b334c455cc331946258825d433a856ba4e611046a50842118c184826346107b5ae5adcd6b16b109225250631c84398c52104300820⟩,
  ⟨34,4,[ew48,ew63,ew68,ew71,ew73],localHints 4 0x5409c0e85f0600d03481400c0040101f0060c40201e 0xff75ee87545dcc71bb5a911287665454331210⟩
]

def nodesBlock6 : Array Node := #[
  ⟨34,4,[ew51,ew63,ew68,ew71,ew73],localHints 4 0x150270561bc19037028018008020060740201e 0xdd75cc532332bb51a110993875654432321010⟩,
  ⟨34,4,[ew62,ew63,ew67,ew68,ew71],decodeHints 0x5c0b80101f0901200a0020c618c180300040d019032006944020140c00101502a00c008030030da00c008010c00182f85f⟩,
  ⟨34,4,[ew62,ew63,ew68,ew70,ew71],decodeHints 0x901201702e0040743186302800c18030004950020140c0010190320060dc008020f8008008060c00041382700200c1582b⟩,
  ⟨34,5,[ew62,ew63,ew68,ew71,ew73],localHints 5 0x121490635220b81828e0680c945837028005a887c03e954013500da0752980311e07830004 0x97e963d2def4e5247e0c3c19ef25c864d88bb112932cc00806f784210a6a09d4094d273092408480424610085c17b9ab5b12962d6a4a50631c84398c52102310400⟩,
  ⟨34,4,[ew44,ew63,ew68,ew71,ew73],localHints 4 0x5409c030710600c80081403e0d00101d06e00c0f004 0xffd9ee9dcc649890bb06aa0398987655432210⟩,
  ⟨34,3,[ew45,ew68,ew71,ew73],decodeHints 0x540a80300204e09c0080305c0b80101d0560ac008040600c00101e0640c801831⟩,
  ⟨34,4,[ew63,ew65,ew68,ew71,ew73],decodeHints 0x1502a00c0081382700200c1702e0040740a0010680081b8030560ac008040600c00101e0640c801831008d4830004⟩,
  ⟨34,4,[ew47,ew63,ew68,ew71,ew73],localHints 4 0x2406305c050180320620040f80203a00c0f004 0xdda4cca2bb430a109941882766545432321010⟩,
  ⟨34,3,[ew63,ew66,ew67,ew70],localHints 4 0x3687c10c0a8408270081b01701e 0x469416911481776355432210⟩,
  ⟨34,4,[ew63,ew66,ew67,ew71,ew73],localHints 4 0x549581381f11e0b83e05f00c1bc3481d0080c80181e 0xff7edd4c9417b1aa14918873633035432210⟩,
  ⟨34,4,[ew63,ew66,ew68,ew70,ew73],localHints 5 0x2a04e9580e88f0da0b8158010de07c348040620c00101e 0x841ef439a65b428604265854a4a50421cc42908310820⟩,
  ⟨34,5,[ew63,ew66,ew68,ew71,ew73],localHints 5 0xa94a027526019aa08f4ae0080182b0020503787c03ea3c3486d03aa3018b530c00112901e 0xcb696fd2ed6cbde87e0f6c1defbdac741d8b5a108ab9d47be8e74def422435c90c88cf113e007400f789c202da26084b1014029d2240847114c500c022084310020⟩,
  ⟨34,4,[ew43,ew63,ew68,ew71,ew73],localHints 4 0x5418c1701f056078348060280040103406e00c0e804 0xff85ee72dd5cbb87545a292387665454232100⟩,
  ⟨34,4,[ew46,ew63,ew68,ew71,ew73],localHints 4 0x4804e1c415832062018008020060740201e 0xcc65bb53a33299510110883765654432321010⟩,
  ⟨34,4,[ew63,ew67,ew68,ew70,ew71],localHints 5 0x2a05c9583e06d04e0c00101e0be018190030620ac00804 0x841ef4b886610296a4266056b5292839cc02948310820⟩,
  ⟨34,5,[ew63,ew67,ew68,ew71,ew73],localHints 5 0xa94a82e52607c00b560f895c0e88f0be019488300040d036832006a3418b550c007929804 0xb76ad0d59ce5e56749e0e725294af07b60eb5ded64a6a37568a54d6b9a9525ad3088ce7039e283c4e701a012d805300b5894229d004a007394c500c022084310020⟩
]

def nodesBlock7 : Array Node := #[
  ⟨34,4,[ew41,ew63,ew68,ew71,ew73],localHints 4 0x9009c1701d0be1bc188140020181a00203e00c1b804 0xff84ee72dd4c7b784a45212978764543212100⟩,
  ⟨34,4,[ew42,ew63,ew68,ew71,ew73],localHints 4 0x2a0c61c41583003c0040300203e00c02031 0xcc546b654a4399618847011065654343221010⟩,
  ⟨34,5,[ew63,ew68,ew70,ew71,ew73],localHints 5 0x180f82752a0b94a01d6b01b52b88f0560054907c0600094801e6ae1812a83200800c1b831 0xa62a0e7318c6334673990c994a13b148628e70ae2a2ac26584a552b4148419843208a221b9e883d0e70da34296362c6a52128198603800600ca3008830906210020⟩,
  ⟨34,6,[ew63,ew68,ew71,ew73],localHints 5 0x54d7813b5d00c0b9ae01f03a23c158016b60503e030004d681a01e0da0c830004006d641b831 0x6aefb9521b6d2f7d2e0b38e1994ef93ce10c0ee33cd7668e9638d6bace9329211921d12a210791c42a16c6912c2916b5212828066390262906310020⟩,
  ⟨41,4,[ew76,ew176,ew181,ew183,ew185],localHints 4 0x1b05e0b00e04b01002c0081000001c07802 0xcc63bb57aa3905600340807656543432210⟩,
  ⟨41,4,[ew91,ew176,ew181,ew183,ew185],localHints 4 0xd91822e4208a04b01e0040580002002003802 0xdd541c611b41a6569434817656543432100⟩,
  ⟨41,4,[ew171,ew176,ew181,ew183,ew185],localHints 4 0x2f058868258080160040800012a01c07802 0x4674cc62bb42067004a9928767654323210⟩,
  ⟨41,4,[ew176,ew181,ew183,ew184,ew185],localHints 4 0xd80005e0708b9080160040101001e86803808 0x7676dd76ccbb61a11a19018676554321010⟩,
  ⟨41,4,[ew175,ew176,ew181,ew183,ew185],localHints 4 0x2f05886c258080160040800013e01c07802 0x4654cc62bb4206a04509928765454323210⟩,
  ⟨41,4,[ew176,ew181,ew183,ew185,ew186],localHints 4 0x81b2300701600201603d0d91402000003808 0xdd2332cc7201101ba199218876542321010⟩,
  ⟨41,4,[ew59,ew176,ew181,ew183,ew185],localHints 4 0x1b52c0b08a0106be0200080b00001c0100f 0xcc455b56a68154119817116545433221010⟩,
  ⟨41,4,[ew79,ew176,ew181,ew183,ew185],localHints 4 0x5e0b02581c0160040800001001c07802 0x4674bb62a42067004109928767654321010⟩,
  ⟨41,4,[ew18,ew176,ew181,ew183,ew185],localHints 4 0x1b05ed848400b6c00700080002001c0100f 0xcc84b684a46198114317116554343221010⟩,
  ⟨41,4,[ew81,ew176,ew181,ew183,ew185],localHints 4 0x5e0b0258080160040800003801c07802 0x4654b62aa42061004509928765454321010⟩,
  ⟨41,4,[ew176,ew181,ew182,ew183,ew185],localHints 4 0x21c0160401782c06c0040000f00412c03808 0x56cb6a59961885117713643354334432210⟩,
  ⟨41,4,[ew176,ew181,ew183,ew185,ew187],localHints 4 0x800438a580e00f21002c8a01000412c03808 0xddcc64b10011a9110013883376335432210⟩
]

def nodesBlock8 : Array Node := #[
  ⟨41,5,[ew176,ew181,ew183,ew185],localHints 5 0x8700db6d6d8dadb502f038a61b4b68058a5d0db67016d9800a1a6ca041b20006c6d882580200e87407808 0xf21fdf29bde29efda1a8d0db8cddf8b5dadb0de3a8d13a01539010890d43891e4885ad805ef711a461144605085854a4910438465310051106310400⟩,
  ⟨42,4,[ew76,ew176,ew197,ew199,ew201],localHints 4 0x1b0ae1581c84d01c02c0301000a01c09003 0xcc63bb57aa3905600340807656543432210⟩,
  ⟨42,4,[ew109,ew176,ew197,ew199,ew201],localHints 4 0xd91822e4248a84d0240180580502003803803 0xdd541c611b41a6569434817656543432100⟩,
  ⟨42,4,[ew171,ew176,ew197,ew199,ew201],localHints 4 0x570ac8782680e0160180800512a01c09003 0x4674cc62bb42067004a9928767654323210⟩,
  ⟨42,4,[ew176,ew197,ew199,ew200,ew201],localHints 4 0xd8050ae0e48b909016018018100248780380e 0x7676dd76ccbb61a11a19018676554321010⟩,
  ⟨42,4,[ew175,ew176,ew197,ew199,ew201],localHints 4 0x570ac87c2680e0160180800513e01c09003 0x4654cc62bb4206a04509928765454323210⟩,
  ⟨42,4,[ew176,ew197,ew199,ew201,ew202],localHints 4 0x301b2300e42b0030160490f9150200140380e 0xdd2332cc7201101ba199218876542321010⟩,
  ⟨42,4,[ew61,ew176,ew197,ew199,ew201],localHints 4 0x1b5321588a8106dc0380300b00a01c01812 0xcc455b56a68154119817116545433221010⟩,
  ⟨42,4,[ew83,ew176,ew197,ew199,ew201],localHints 4 0xae158268390160180800501c01c09003 0x4674bb62a42067004109928767654321010⟩,
  ⟨42,4,[ew21,ew176,ew197,ew199,ew201],localHints 4 0x1b0aedc08480b6de0e40300502001c01812 0xcc84b684a46198114317116554343221010⟩,
  ⟨42,4,[ew85,ew176,ew197,ew199,ew201],localHints 4 0xae1582680e0160180800507201c09003 0x4654b62aa42061004509928765454321010⟩,
  ⟨42,4,[ew176,ew197,ew198,ew199,ew201],localHints 4 0x2200160402b856092018028120061340380e 0x56cb6a59961885117713643354334432210⟩,
  ⟨42,4,[ew176,ew197,ew199,ew201,ew203],localHints 4 0x3005440a641c81221202c8a8100061340380e 0xddcc64b10011a9110013883376335432210⟩,
  ⟨42,5,[ew176,ew197,ew199,ew201],localHints 5 0x8800db7c6f6de9bc857072a6dbc3770aca690fb76016dd40321e6e8041b98056e4dc42680300e8840900e 0xf21fdf29bde29efda1a8d0db8cddf8b5dadb0de3a8d13a01539010890d43891e4885ad805ef711a461144605085854a4910438465310051106310400⟩,
  ⟨44,4,[ew76,ew176,ew223,ew225,ew227],localHints 4 0x1b0bc16c2285102c02c0a01002601c0a804 0xcc63bb57aa3905600340807656543432210⟩,
  ⟨44,4,[ew131,ew176,ew223,ew225,ew227],localHints 4 0xd91822e4288b05102a0500581302005803804 0xdd541c611b41a6569434817656543432100⟩
]

def nodesBlock9 : Array Node := #[
  ⟨44,4,[ew171,ew176,ew223,ew225,ew227],localHints 4 0x5e0b6888288160160500801312a01c0a804 0x4674cc62bb42067004a9928767654323210⟩,
  ⟨44,4,[ew176,ew223,ew225,ew226,ew227],localHints 4 0xd8130bc1148b90a0160500201002a88803816 0x7676dd76ccbb61a11a19018676554321010⟩,
  ⟨44,4,[ew175,ew176,ew223,ew225,ew227],localHints 4 0x5e0b688c288160160500801313e01c0a804 0x4654cc62bb4206a04509928765454323210⟩,
  ⟨44,4,[ew176,ew223,ew225,ew227,ew228],localHints 4 0xa01b2301142d8040160551191602004c03816 0xdd2332cc7201101ba199218876542321010⟩,
  ⟨44,4,[ew66,ew176,ew223,ew225,ew227],localHints 4 0x1b53816c8b0106fa0580a00b02601c02015 0xcc455b56a68154119817116545433221010⟩,
  ⟨44,4,[ew87,ew176,ew223,ew225,ew227],localHints 4 0xbc16c288450160500801302c01c0a804 0x4674bb62a42067004109928767654321010⟩,
  ⟨44,4,[ew28,ew176,ew223,ew225,ew227],localHints 4 0x1b0bcdfc8500b6fc1140a01302001c02015 0xcc84b684a46198114317116554343221010⟩,
  ⟨44,4,[ew89,ew176,ew223,ew225,ew227],localHints 4 0xbc16c288160160500801308a01c0a804 0x4654b62aa42061004509928765454321010⟩,
  ⟨44,4,[ew176,ew223,ew224,ew225,ew227],localHints 4 0x2240160402f05b0b40500981500814403816 0x56cb6a59961885117713643354334432210⟩,
  ⟨44,4,[ew176,ew223,ew225,ew227,ew229],localHints 4 0xa013448a702281521402c8b01000814403816 0xddcc64b10011a9110013883376335432210⟩,
  ⟨44,5,[ew176,ew223,ew225,ew227],localHints 5 0x8900db8b714e25c405e08aa79c3b860b6a7511b85016e100a222706041c1013702e002880400e8940a816 0xf21fdf29bde29efda1a8d0db8cddf8b5dadb0de3a8d13a01539010890d43891e4885ad805ef711a461144605085854a4910438465310051106310400⟩,
  ⟨47,3,[ew157,ew214,ew240,ew254],decodeHints 0x821040785508410807858088110090640ce19c2480f0ca1941b0120cc1981b015⟩,
  ⟨47,4,[ew166,ew214,ew240,ew254,ew264],decodeHints 0x338670920d83286506c124638c70d01543306606c1685c0b80b2160578af0aa191c60361200d80780f0240480a815⟩,
  ⟨47,4,[ew153,ew214,ew240,ew254,ew264],localHints 4 0xca1043305a0842bc248360b203c358550241902c015 0x6896ff89ee64dd8cbb61aa4298987654332100⟩,
  ⟨47,3,[ew154,ew214,ew240,ew264],decodeHints 0xca1941b0120cc1981b015088110090640ce19c2480f0821040785508410807858⟩,
  ⟨47,4,[ew179,ew214,ew240,ew254,ew264],decodeHints 0x3386709203c4f09e0b40482084101e1644b0960920542104201e1a0220440241901b03671a03c3e80f0aa0482c015⟩
]

def nodesBlock10 : Array Node := #[
  ⟨47,4,[ew156,ew214,ew240,ew254,ew264],localHints 4 0xca104330420d0110248360b203c358550241902c015 0x6876ff83ee67dd80cc6baa3298767653432010⟩,
  ⟨47,3,[ew182,ew198,ew224,ew264],localHints 4 0x1e80b479c078b83cc0d8248120c2054370af 0xccb6aa569938776544302210⟩,
  ⟨47,4,[ew182,ew198,ew240,ew254,ew264],localHints 5 0x8413c31d2c09601e1ac3206606c1243407d02405437058 0x840c73bce6738ad61cc75ad2a0a508398052006310820⟩,
  ⟨47,3,[ew182,ew210,ew236,ew254],localHints 4 0x7a0f383639a03c2c89e0c225837044 0xaa4699268832776504300210⟩,
  ⟨47,4,[ew182,ew210,ew240,ew254,ew264],localHints 5 0x8413c964638361701ac3205a1201080785908816037015 0x841057bd0e2b4a4631652152a0a408380c62906300820⟩,
  ⟨47,4,[ew182,ew214,ew224,ew254,ew264],decodeHints 0xce19c2483613c0d82d03601e03c1b09606c1685c0b80b29603206b0c21903286506c1242a8590fa154090120c21540a815⟩,
  ⟨47,4,[ew182,ew214,ew236,ew254,ew264],decodeHints 0xce19c2480f06c0d86380f0d003c4b096092964078b801e1a03206b0c2190090491200482084101e164090550c204822044⟩,
  ⟨47,5,[ew182,ew214,ew240,ew254,ew264],localHints 5 0x19c4f2a218ea844b2a00b42e14f86871e2401b25b092e383e80f4b4164358120dc18432015 0x85e8cdd196b435036b4abc95adc2d63420a6b9508b18c26b433a85ada4e6242030905088c20110465288427b5ae5adcd6b16b521093192841cc6108822904300820⟩,
  ⟨47,4,[ew141,ew214,ew240,ew254,ew264],localHints 4 0xce1043305a1701101b0490d01640785502416032015 0xff899893ee36dd9cbb62aa3198987655432100⟩,
  ⟨47,3,[ew142,ew214,ew254,ew264],decodeHints 0xce19c2480f0cc1981b015084108078580ca1941b0120821040785508811009064⟩,
  ⟨47,4,[ew195,ew214,ew240,ew254,ew264],decodeHints 0x420840b403c3286506c0482084101e1543306606c0542104201e160220440241ac248360b203dc80120dc04832015⟩,
  ⟨47,4,[ew152,ew214,ew240,ew254,ew264],localHints 4 0x19c208960921082206b06c1a02c80f0aa0482c015 0xeeb42b32dd43ccb0aa41992877645432321010⟩,
  ⟨47,3,[ew198,ew210,ew240,ew250],localHints 4 0xf41e6024210309cd0aa1983e842 0x996726528827065044030210⟩,
  ⟨47,4,[ew198,ew210,ew240,ew254,ew264],localHints 4 0x1089704f0c70cc1a05785a120108220120aa1603e815 0xff8edd84c443bb2a12943408706655430210⟩,
  ⟨47,4,[ew198,ew214,ew224,ew240,ew264],decodeHints 0xca1941b0491082102d0360240483306606c168578af0aa9602c0680c2160338670920d82c8550dc1540780f0c21640a815⟩,
  ⟨47,4,[ew198,ew214,ew240,ew250,ew264],localHints 5 0x4206518e1992e0680b02bc0906b06c2402c86108203c2a842 0x8c6103a52f625ce3b56c22d2a4a047308452086310400⟩
]

def nodesBlock11 : Array Node := #[
  ⟨47,5,[ew198,ew214,ew240,ew254,ew264],localHints 5 0x2115286518ea90332a30b42bd4f86b72424024a5d06c1a007b910dc0492d0550fa1842c015 0x36e94bd29adcad665e08dc116b334c455cc331946258825d433a856ba4e611046a50842118c184826346107b5ae5adcd6b16b109225250631c84398c52104300820⟩,
  ⟨47,4,[ew139,ew214,ew240,ew254,ew264],localHints 4 0xce1942a8960841a05785a0920d8078590241900a858 0xff75ee87545dcc71bb5a911287665454331210⟩,
  ⟨47,4,[ew148,ew214,ew240,ew254,ew264],localHints 4 0x338650cc2e02206b0b41241b00f0241540a858 0xdd75cc532332bb51a110993875654432321010⟩,
  ⟨47,4,[ew210,ew214,ew236,ew240,ew254],decodeHints 0x82104078591082102d00f13c2782104201e1a0220440249640a85a0c20543386709203c248120dc0481b0360c21244b096⟩,
  ⟨47,4,[ew210,ew214,ew240,ew250,ew254],localHints 5 0x420410aa2782125c0b40542206b0fa03c248610ca0d809066 0x8c61033dce585ad3314b229290a046398452086310400⟩,
  ⟨47,5,[ew210,ew214,ew240,ew254,ew264],localHints 5 0x2115389e54c104212a30d01115006b0b40d9ca07d0b297407b930dc1552d81212016030815 0x97e963d2def4e5247e0c3c19ef25c864d88bb112932cc00806f784210a6a09d4094d273092408480424610085c17b9ab5b12962d6a4a50631c84398c52102310400⟩,
  ⟨47,4,[ew119,ew214,ew240,ew254,ew264],localHints 4 0xce194248c70841101b05a0b21a0078550d60482c015 0xffd9ee9dcc649890bb06aa0398987655432210⟩,
  ⟨47,3,[ew120,ew240,ew254,ew264],decodeHints 0xce19c2480f0ca1941b012082104078550cc1981b0150841080785808811009064⟩,
  ⟨47,4,[ew214,ew221,ew240,ew254,ew264],decodeHints 0x3386709203c3286506c0482084101e1542d0360d003c358120cc1981b015084108078580881100906402ae5430815⟩,
  ⟨47,4,[ew130,ew214,ew240,ew254,ew264],localHints 4 0x4209e082168210440c80d82c80f0aa0482c015 0xdda4cca2bb430a109941882766545432321010⟩,
  ⟨47,3,[ew214,ew224,ew236,ew250],localHints 4 0x3707d3ce19cf306502a73420858 0x469416911481776355432210⟩,
  ⟨47,4,[ew214,ew224,ew236,ew254,ew264],localHints 4 0xce978328591201043e8960922e05785502a11009058 0xff7edd4c9417b1aa14918873633035432210⟩,
  ⟨47,4,[ew214,ew224,ew240,ew250,ew264],localHints 5 0x670ca9782a8900dc10433036170164578150c810807858 0x841ef439a65b428604265854a4a50421cc42908310820⟩,
  ⟨47,5,[ew214,ew224,ew240,ew254,ew264],localHints 5 0x19d54865550125cb8904be03c0906606c1685c07d0b2a905786e0aaa84323960c20552d058 0xcb696fd2ed6cbde87e0f6c1defbdac741d8b5a108ab9d47be8e74def422435c90c88cf113e007400f789c202da26084b1014029d2240847114c500c022084310020⟩,
  ⟨47,4,[ew117,ew214,ew240,ew254,ew264],localHints 4 0xce278208590cc160578490b40d8078680d60482a815 0xff85ee72dd5cbb87545a292387665454232100⟩,
  ⟨47,4,[ew126,ew214,ew240,ew254,ew264],localHints 4 0x840ca31c330440c81241b00f0241540a858 0xcc65bb53a33299510110883765654432321010⟩
]

def nodesBlock12 : Array Node := #[
  ⟨47,4,[ew214,ew236,ew240,ew250,ew254],localHints 5 0x670829783e86e0ca1080785812c124220120c81981b015 0x841ef4b886610296a4266056b5292839cc02948310820⟩,
  ⟨47,5,[ew214,ew236,ew240,ew254,ew264],localHints 5 0x19d550415501641b3990fa97c2a89012c1255304201e1a037044024a88323980c21612d815 0xb76ad0d59ce5e56749e0e725294af07b60eb5ded64a6a37568a54d6b9a9525ad3088ce7039e283c4e701a012d805300b5894229d004a007394c500c022084310020⟩,
  ⟨47,4,[ew99,ew214,ew240,ew254,ew264],localHints 4 0x1081942085512c2e03205a06c1243400f0b204835815 0xff84ee72dd4c7b784a45212978764543212100⟩,
  ⟨47,4,[ew105,ew214,ew240,ew254,ew264],localHints 4 0x6713c31c330420b00d82480f0b20480a864 0xcc546b654a4399618847011065654343221010⟩,
  ⟨47,5,[ew214,ew240,ew250,ew254,ew264],localHints 5 0x1242c865554105548557361b92f8900cc0d95387d08403d528587341852e84402a04835864 0xa62a0e7318c6334673990c994a13b148628e70ae2a2ac26584a552b4148419843208a221b9e883d0e70da34296362c6a52128198603800600ca3008830906210020⟩,
  ⟨47,6,[ew214,ew240,ew254,ew264],localHints 5 0xcee8432ba0092105cf8590aa2403303673c1683e84201ee74340580dc11030815024e7035864 0x6aefb9521b6d2f7d2e0b38e1994ef93ce10c0ee33cd7668e9638d6bace9329211921d12a210791c42a16c6912c2916b5212828066390262906310020⟩,
  ⟨56,7,[ew165,ew217,ew243,ew257,ew267,ew269,ew270],localHints 6 0x6c1780b0580400e02a05007c2000f04e0181301d00a0f40900e07e0ac0a02903c04c1e01502c0ec0b83a032044290010a013c0007001001c1980c0040b4048030420d405004 0x370cae432bb0c0d40d2d0c6dc31b5040bc0bb4dbcbbaf2cd36dbad226b2a42caa6988410aa3ac836b2238ea34da20a482e92208282cb1509e49a79104059a690d9458e514d3648e384b88582214b2e18201557d321f4d554520505079b75e6d040175d6cd70169c04d35b69a60b6415d904b2d85d70485925564882015414855014d40451524d208309141044344241038338f34d3c33ce34d3032822ca2431c22071831021440c3002040⟩,
  ⟨56,6,[ew121,ew176,ew243,ew257,ew267,ew269,ew270],decodeHints 0x3606c0580005e0bc008080580b00001c0540a8030010500a0028000801000700804e09c0080604c0980000507a0f40400e07e0fc0b80900800405801008000080000a2144020080600c0190320560ac008140520a4000130780f0038070760ec0600a0740e8048110140101a804⟩,
  ⟨56,6,[ew143,ew176,ew217,ew257,ew267,ew269,ew270],decodeHints 0x3606c0580005e0bc008080580b00001c0540a8030010500a002800080100070080560ac008140520a4000130780f0040160760ec0600a006004058010060000800009a1340180805c0b81903204e09c0080604c0980000507a0f40380707e0fc0b8090740e80481101200c1a803⟩,
  ⟨56,6,[ew155,ew176,ew217,ew243,ew267,ew269,ew270],decodeHints 0x3606c0580005e0bc008080580b00001c04e09c0080604c0980000507a0f40400e0560ac008140520a4000130780f0040160740e804811004004058020040000800209612c0100805c0b8180300540a8030010500a0028000801000380707e0fc0b8090760ec0600a0180081a802⟩,
  ⟨56,7,[ew165,ew176,ew217,ew243,ew257,ew267,ew269,ew270],decodeHints 0x6c0d80b0000bc178010100b0160000380a8150060020a0140050001002000e01009c1380100c0981300000a0f41e80801c0fc1f8170120ac158010280a4148000260f01e00802c0ec1d80c0140e81d00902202c0080b002040000100000840407001e0300900902a028658012320048600021600003807748031d18097440280c035⟩,
  ⟨56,7,[ew158,ew217,ew243,ew257,ew267,ew269,ew270],localHints 6 0x1b23027c8b8950540a00f84b04e0181301d00a1341f82b0280a40f0130a20ec0b83a032044290010161400004f0200201a80704a0301080f0040880483802400c380200140f80a804 0x557d136344d75d56154184325f3c986105d04154304f1c155504d03aabed62fb6aa8e618b67b8e56e3a79ed555310b0e16c39040c34c258ae8aaba18609aaaa15a499e92555689e71d098916625040720725d95b3a56dd7493890d89218e48586038e38558838220d55618200507c315f0d04010810ce79a75e68e3837436897036dc0c925a6da4586195d76586115d75155564d35955544d334d49141014e38f30c3ce2cd30b14924a1c72891881c61430c4041103002040⟩,
  ⟨56,6,[ew158,ew176,ew213,ew243,ew257,ew269,ew270],decodeHints 0xd81b0160001502a00c0041402800a00013827002018130260000141f83f02e0240391800201c0391700001c1d80700e0281d00700e044850010160048b0000200002100c0880242885100e0282f05e0020582d85b0001142504a02c0342a05402c0901e00701401c3b816⟩,
  ⟨56,6,[ew158,ew176,ew217,ew239,ew257,ew269,ew270],decodeHints 0xd81b0160001502a00c0041402800a0000391800201c0391700001c1f80700e0241582b0020501482900004c1d83b0180280383a00e044848010160048a8000200002080c09a134038090880282b8570020382b0560000e42004001c0341e80701201c2704e01c10c3b00e⟩,
  ⟨56,6,[ew158,ew176,ew217,ew243,ew253,ew269,ew270],decodeHints 0xd81b0160000391800c01c0391700a01c13827002018130260000140383f00e0241582b0020501482900004c0383b00e0281d03a012044840010160048a0000200002584b00e030208090840281782f0020201602c0000702000701801c1e83d0100901e03c01010c3a808⟩,
  ⟨56,7,[ew158,ew176,ew217,ew243,ew257,ew267,ew269,ew270],localHints 6 0x364608b82a050ab41380604c0155603f02e0ac0a029026aac1d83a0220840781202a004058000200200380c01a0241207001410c0c035 0x279cd30998e24994c2649203a38de3092098a184e81f7cc78918975c71b19a68e65860c5c90c95955480d45064cd38d38b30b3042524484063c338d38d30b30b2892042071841850c40c2040⟩
]

def nodesBlock13 : Array Node := #[
  ⟨56,6,[ew176,ew213,ew239,ew257,ew269,ew270],localHints 6 0x1b0540a00f97400c46c5d0051065cc0a11a17204c4101700e02804ab001625c00aaf0202800000d0180081200374ee983b854086060023a555c1d82204e 0x457b1356c4d75d15513e7ae956ba679cf555a64a8f46a3e4929451215a259e89555489e795198892621146592465c8c83e321c2193d901589f8627d55408617d18007a001145f79e68f74071d00f01a71a0196da21b6996402005976015550575d65554935014510534d24514103813ce04d30620c2ca241208047146005103081000⟩,
  ⟨56,6,[ew176,ew213,ew243,ew253,ew269,ew270],localHints 6 0xd8e01ac2641380604c074028831760505808802601c0607f0320455a00b13000559810142000068027509803b84a08c09004803086060022b25621d42103c 0x498b545ad518612592328b2a5acaa8a0c596aa5acc4ab32596a492256a66a29996589a289929c99672524a696524c91b7646cc3097490168e08a38165808a28128407e10124a07df01d79a31e69d7403006897006dc00901a6da5d86415960586175964d45414920545134920514063103ce34130c2ca201248047146005103081000⟩,
  ⟨56,7,[ew176,ew213,ew243,ew257,ew267,ew269,ew270],localHints 6 0x6c2f05b08a0a81401f0948301380604c074028544160fc158140520780980707605c1d019022428058720024580808b000aac3b8160180080682401200c218040e00600a80a 0x3d5c914f245554f4cf313c6f571bd34cc54cbcfc0c47030f3ef46f2e8bac4eeb28a0b4d3b25b4b3ed2e596c3cf0ccacb0eb2cc30322a1d3a66a299934c7a2898f9c79671cf3e69650cc9070e41cc3032631da8982e261a6872c701385e8217934c082078f7c075f00f3de75d0c970031c00b6d769b5cb2c06805c76406190071d76175155814d30555544d34114813cf0514503cf04e04230c08334130c2492812ca2481811c6045102004083081000⟩,
  ⟨56,6,[ew176,ew217,ew239,ew253,ew269,ew270],localHints 6 0xd8cc17a2445e006162224028070560501481e0262080b87f0320455c00b1340055b810144000068027529843b04004806001ab656a1d41e84608610405004 0x498b545ad518612592328b2a5acaa8a0c596aa5acc4ab32596a492156a66a29996585a289929c59671524a696515d91b3246dd7453050568e08a38165818a28128417e10524a07df04c79a75e68c3017416857016dc04515a6da5d86425960986175964d454249209451349209140a3103ce34230c08b24a149207182145103002040⟩,
  ⟨56,7,[ew176,ew217,ew239,ew257,ew267,ew269,ew270],localHints 6 0x3615c2b0390540a00f8400fc8341380604c0740280707e0ac0a02903c04c2720b07605c1d019022424058730024540808c000ab03b00e018008120030e00600480d08604805004 0x3d5cd14f345554f4cf313cb0572c134cc54cc0fc4c47130f3f04702e8bed4efb68a0b4d3b65b8b3ee2e596d3cf1ccb0b1ec2cc307aea153a66a299934c5a2898f9c596714f3e69651c490532415a8d82e361a6852c505389f8627d34c18617cf8017a004f3df79e1cc7411dd04c30711c04b6d769b5cb2c16815c56416190451576175155824d30955544d34114823cf0914503cf08e08630c18734230c1042822ca089206148187182145103002040⟩,
  ⟨56,7,[ew176,ew217,ew243,ew253,ew267,ew269,ew270],localHints 6 0x360bc1601c0540a00f80704e0181301d00a0f50683f0560501481e0260f10603b02e0e80c81121002c3a0012280404680055a1d40400d0041c00c00c0480240184608603c05004 0x416cd2533496590510354cb05b2c1450d58dc10c4d4b13504304b022abed52fb6aa88514b67b8842e2279ed410287b0836c194ae8aaba14506aaaa10a469e91904289e728d9862a618d34a12519b91922465b6c62060548e08a38145018a28108417e10504207df28d78129e04d34a11d0487186dc6082016c160668165a0461986585565c25140965955144524c241009249141008f08934d24a38234d08c2c920b24a242208107142185103002040⟩,
  ⟨56,8,[ew176,ew217,ew243,ew257,ew267,ew269,ew270],localHints 6 0x360bc0e02c0540a00f84045009c0302603a0141ea2701c0fc158140520780983c44c0581d817074064089190a402c0090b0a00408604f000eb1d587003001dd51e90100300102401200c068431960d405004 0xd36bb55667b61669a0d36530ce67a7396ba7396590ce68e54e4f860b5b860b4d354e58e0cac77735677735c710ca659575bb660a4f660abae5754d320838e40a2f440a38e2332cb0c767272fc7272f6590c7c7156f4f0607bb06074d356fbae14538e407aed40738e16caeb14782a15e2aa15e8201472870c1669726a297266590c1a285664e76019676014d356696514538e4018a440138e1638a21412a115d82115d28a14180115d1df14179f1411c715d79d0c269a71b65971b69a0c26595545966174d36175965544d349138e40f2cb40f38e34c2cb1451490c22891452060c21c61451000c2040⟩,
  ⟨56,7,[ew155,ew217,ew243,ew257,ew267,ew269,ew270],localHints 6 0x360bc0582c0200715d2b909609c1301d07a0481702b0280a40f0130780540b03021a0e8290060021400284f0000940700800e084060350040880c81801200c1982002206805004 0x4f1cef5f3bf1c535d3417caec72b975d0c50b93c10bf04134eebee2d82ed5d7b5860b5cb2d52ec4d3b1554b4cb151acb42b2d12ce4101d7aa862aa175c7618a13a475691d34e85559909c74671d04264511cb94916524b2c76c70579218e48575c18e38538818220534e18207907c175f05041e75d04b70315c0cb2c16c10c768125a0471c32433186195d765860c5d75155564d35955544d31514524104913ce40f38e34c2cb14924a1c72891881c61430c4041103002040⟩,
  ⟨56,6,[ew181,ew204,ew230,ew267,ew269,ew270],localHints 6 0x1b0ae02c2b0100722280a0870261c44188610a1bc4101600405409081002018400000d2014d600e00e00c1f8040660941d83a 0x3229203e482288c3cc20f8df8a37cf3c88887cc84882120c31f81f15d79a3de69d7453cf69b70531c15b6da30c45464521915451120804e6163d858e3813cf58a5c131704a29630c4885415150482125140514d215349144114100f40b3902cf3c038e2cc34028d00c30b28a2431c0207003182146083080140003102044083080040⟩,
  ⟨56,6,[ew181,ew204,ew243,ew253,ew269,ew270],localHints 6 0x36040058e01ac2643186206e20c2f85c062008070120842ec008061600004400500e1280c0190060cc020255641d40883c 0x3a18e24638a184e44e29081e46079040a45178c7ca39f28c31e38e21145b41d6d14484106ce38831c20e39b30c50a68855a20a2945550506574515d04014515cc60138e04c31738e4d558129605555328a0540532084d44c120101148d41235144041034e3c030f00e38d30c0062c428b1061002802461c0207006144045103080040⟩,
  ⟨56,7,[ew181,ew204,ew243,ew257,ew267,ew269,ew270],localHints 6 0xd8570161580803909011c1a04a41e18c310370a80fc06a0e0be1701884e02c0e0010150240ac008060520000f00512403803817030064018040660940880a 0x3abb6946da6bace44e291b28aeca1144aacaa0ea8aa6a28e3a8a682109e546795040845194c9883a620c32538e0ca9080e420a28b0e319146042281144641080e38632118e3a030c4d77c629f1975d328a0c87860de18820375c0506d945165040145164c68138e04c31938e50a6015d804a2945d75965412150530541865134c118101148d41235144041034e3c030f00e38d30c2c32402890030022080830802001c3140185003102044083080040⟩,
  ⟨56,6,[ew181,ew217,ew230,ew253,ew269,ew270],localHints 6 0xd8100163305e8910c61881b8020be0502e0310262080b0150822f0008061620004480500e1000182556c1d40c81a0660f408804 0x3a39644659238ce44e2908a046281040a45180c84a3a128c32038e15a7dd45175a68545175778538e1575dd38e4d570529c15555328a05145869b61144169a60e3815d904e3985d750a58155604a2945550530541455134c114109148d41235144241034e3c230f08e38d30c0832c828b203202282083248149207182142103002040⟩,
  ⟨56,7,[ew181,ew217,ew230,ew257,ew267,ew269,ew270],localHints 6 0x3615c058560200e41502803e101080630c40dc2a03e00417c0a05c06204c270160760350701502409c0080604c0000e8051260380380c0060940c81a06602408804 0x3adbeb46faedb4e44e291baab6ea9144ab4aa8eb0aaec28e3aaaea210a674699d04084519cca083a820c32738e0ca9880e620a28b0e515d92245189d74545189a8c538e15a6a238e4d88452a115861328a0e07c521f05145b75e6d144175d6ce38169c04e39b69a50a64161904a2946180c85c10d70482035950530541455134c114109148d41235144241034e3c230f08e38d30c2c32422890830862081831822020831c6147183182142103002040⟩,
  ⟨56,7,[ew181,ew217,ew243,ew253,ew257,ew269,ew270],localHints 6 0x6c0800b578aec2b8560720083186206e105080540be0502e0310261082320f09c0580a81205e0040302c0000700287501e01c1280e0300640181a06602008804 0x3ecbad4aeb6cb0f48fad144b4922d146b492a8d34b3cf2cd36a3cf211a674a99d14484929cda083e820d3673cf0c79882e61924a34658d24864518cf3c636418f3e334d0cb8860c618b18366151680622019659420805249c79f71248179e70f3c16dd04f3dc6db0cb6810c104b0436585485c15970482155960540551865545011810924ce45339248245138f40235008f3ce34d0830892cb2433022c208328920a2432422021c3142185103002040⟩,
  ⟨56,8,[ew181,ew217,ew243,ew257,ew267,ew269,ew270],localHints 6 0x3615c058560200e41501f0501011580f0c61881b85407e8a82f8140b80c40984e02c0ed1481702a048ba8520020188e850000470278050f00340700775a0cc128023d20301f01803200c1c01a1580d408804 0xd7e7b5b76fb677e790d76d70d16fa776e7a7766db0d1e515b65f8651df86515d75b6df60cc6b57746f577469a0cc6cc58c53364a5f364a51458c5cc3b047220c4cc38c44c4f0c700c76db76d6af76d6db0c769a5ad5d764752e6475d75ad51425e8ec20746c1478e315e45125230c3872ab38730c4aa28a0c16db766a297666db0c1a285a65d76419676415d75a696515f4642018e414145125f8e315230c38182214130c4a182014178125f1c715f79e4c11c10c26db75c69a75c6db0c269a5955d76585146585d75955144d34900c245038f30c14d28a38d30c14b28a2482060c21c61441000c2040⟩,
  ⟨56,7,[ew188,ew247,ew267,ew269,ew270],localHints 6 0x1b05e0700582c02021837885096090078081027dc3480139c018401ec0007ac0284d03001c0900e3d4eb8360030040341d83a 0x4cf86439f52441f8614cf50f4ca5235a28635a25144ca84a38a3e04187e04183cf38a7ca4c349e59d51e59d4924c350338335c4013dc40134d3833c369929b2c361b2c328a6996184c45175954975955144c44843843d14003514003cf38434408928c2c420c2c428a0892081c00c51840450840c3080040⟩
]

def nodesBlock14 : Array Node := #[
  ⟨56,7,[ew188,ew248,ew257,ew269,ew270],localHints 6 0x360a80f82805e0700582c02012c1200f01009c6681d00228c0302617e0005f00505c0080600975e73c0c00300e0342204e 0x48e76335b4e33db75d48e4ce48a4625614e256145148a4ca34a3203c93a03c930c34a38a4834df55e75f55e4d348374334339c3d76dc3d738e3436c315729a64361a1432836576174844d65544565544d34844443443903c83103c838e34430408828b08424b08428a0882481c10c61440061440c3081000⟩,
  ⟨56,7,[ew188,ew248,ew257,ew267,ew269,ew270],localHints 6 0x360a80f8280be02c2e0310200800383b04803c138cd03a0045180604c2fc000be00a0b80100d0180248703200606022011 0x44d7a331b4a339b79e44d48d45149251479e51449245179e30c34d38e6db38e34d30c6db4494225214a25214104494893092e03873603872cb3093490965d60890890890890965d644049251c79f51c49244079e31c34d3806dd38034d31c6db69a69944045908224908059808024909759644349551341551349244340330334f3862cf38634d3032c308120108308308308308120120624a2031ca2032492061c6081144083004083083081000⟩,
  ⟨56,8,[ew188,ew249,ew257,ew267,ew269,ew270],localHints 6 0x6c1781c0160b00802a03e0a02580f01017c2e03109cafd5f03b0400915e8273a00740080604c6b8001ad00a1340c0070240381700201a0300490e23c00c08832 0xd1aee42956e4a9aeb0d15510cc56d5ecaed5ec5550ccacc40c46a4a3a6a4a345140ca4c0c85285e75685e75140c85484083e64864664863cf4084486a43253488e534830c6a48e30c15555e01e25e05550c11c14204514811e14814514201e06c730c3411df6c130c35e1dd6c72081c11dc6c12081da1d90c25585d65185d65550c25024024534853d34854514023c21cb30e34228e34230c1cb28a1c52091c21891c22081c51851041000c2040⟩,
  ⟨56,6,[ew188,ew197,ew230,ew267,ew269,ew270],localHints 6 0x1b05e02c160100382280a0870261c44188610a1bcd600700420400806100000348050fe0200b00302a03c1f80405a0881d83a 0x3a292046482288e44e2918df8a37d144a88a7ce84a82128e39f81f15d79a45e69d74545169b70539c15b6da38e18964529914924628a05061645859040145158c5c139704c31638e5435012940434c215308308114101148d41235144041034e3c030f00e38d30c1ca2c024b00a2872490062071481c61801400021030440c2080040⟩,
  ⟨56,6,[ew188,ew197,ew239,ew257,ew269,ew270],localHints 6 0x6c0800b09011c1a02f058070419732342e40c00200e0ac008060520000f00501e05c018080881500202d0441d80504e 0x3a08a146286080e44e2907dd45f75040a45174c78a39e28c31d38e21171a41c69144841068e6c831b20e39a30c20a6462d918a1882c801061645859040045158c5c039700c31638e5445002940044c32130c40c020805148d41235144141034e3c130f04e38d30c04b04728a1cb2c12811c8241189048207186043144005103081000⟩,
  ⟨56,7,[ew188,ew197,ew243,ew257,ew267,ew269,ew270],localHints 6 0xd82f0160b00801c09011c1a04a0c61881b8544240fc122110be1701889200e0600102b0020181480003c0141e00802c054078170420640180405a0880880a 0x42bb694eda6bad04d0313b28aeca134ccacca10a8ca6a310428a682129e54e79524884d394e98842620e3a541024b90832420b2c930c1934e14a38534c64928504063a219042138e0cc3060e018c3180df0c87860de18821d0dc0526d94d36524814d364e68141004e3994106035c131758354121504304218608308118101350f4943d34c04923d044039101040f38e28c3402cd00c30a2cb00900a2082892402001c71401850021030440c2080040⟩,
  ⟨56,6,[ew188,ew204,ew223,ew267,ew269,ew270],localHints 6 0x1b05e02c160100382280a0870261c4d600710c2143788200420400806100000348050fe020070030420801f80402403c1d83a 0x3a292046482288e44e2918df8a37d144a88a7ce84a82128e39f81f15d79a45e69d74545169b70539c15b6da38e6476052980505d545755040145154c58139604c31538e08950129404924228a0464c71531c618114101148d41235144041034e3c030f00e38d30c0ca2c024b00a2832490062071481c61801400021030440c2080040⟩,
  ⟨56,7,[ew188,ew204,ew230,ew267,ew269,ew270],localHints 6 0x1b05e0700582c0202280a0870261c4418434262184286f10409108808004204e88012ec018401b00006bc348050fe6b003a0e01c0800183f3d4089310250080341d83a 0x5d3b704ab63052bb6d5d36135cd62f66eb6f66e6185cdb4d48d4ec51caec51c4d348dacd5c8a6a66662a666a695c86184a69e85084e85089e74a64d392434d38872538834d92371c5c15a26606226605965c16184a04215014e15014104a04d379e34d38171f38134d79d71c1c129b1c621b0820820812015c061a65159a6516185c05964914d55004155004d349141008234d3802cf38034d08c2cb1c02891442090820820802001c0183144043082082080040⟩,
  ⟨56,6,[ew188,ew204,ew239,ew253,ew269,ew270],localHints 6 0x1b02002c2b8560720bc1601c00e17c2e03100405c0d0240ea0ac008060520000f0050460343b00e0060200c80402403c0880a 0x3a29234648e288e44e21085f4617d04084517cc8083a020c31f38e19179c41e71144641070e74631d18e39c30c1966c521b15658620605069845161040145160c64138e04c31838e0885c15970482025960540551865544c118601148d41235144041034e3c030f00e38d30c00a00b2082ca2402080c61c01470061831450021030440c2080040⟩,
  ⟨56,7,[ew188,ew204,ew239,ew257,ew267,ew269,ew270],localHints 6 0xd8570161580803909011c1a22c0c61881b80707e84c2f85c0621383f2120040901580100c0a40001e00a0e03b00e01a05c10003124064110040340480880a 0x46bb6952da6bad1511314b28aeca1450cacca11a8ca6a311468a682939e55279534ca51494f98a46628f3e54511cc30a1ca28c3076641945214e38545064d38514463e21914613cf1cb80632064a7c639f18a29939e05375b5146d34c15146cf70145104f3db4511cc6811da04c30765838e5c12970560431860d60c11810145504d54145004d34114803d20114503cf08b08030c00e34230c00b00228a08b080280089200188007002186005102044083080040⟩,
  ⟨56,7,[ew188,ew204,ew243,ew253,ew267,ew269,ew270],localHints 6 0xd82f0160b00801c09011c1a0070c61881ba2c07e84c2f85c0621d4100020480ac008060520000f0050780204904641e0340b82103200c1280404603c0880a 0x4abb6956da6bad2552395b28aeca1554eacea12a8ea6a3924a8a682549e55679545095559509894a62504254923579093a41d55615238555475148524874221d24a141034e3873471ce38d3202097c731f1c924831e05475b5556d45015556d070149205041b49209708138e04868238e09960125804d0422490570421c708c0811c10155915164555405144524c041301249141034e3c034f00e38d30b00a0032490ca0c02402081801c60021050440c2080040⟩,
  ⟨56,8,[ew188,ew204,ew243,ew257,ew267,ew269,ew270],localHints 6 0xd82f03802c1601009011c1a04a4ca18c310370a89901fa630be17018a2d0100081202b2ee004030292400008f81e00a0f0490074520380b8e103200c110250080340880a 0x212bb146c5b14ecbae21259220c5b05efbb05ef59620cb8c44c4ad4dbb2d4db49244cb0c20956b5e95ab5e95552095964693ea4c94aa4c93cf46949265930c3496e834930c6676db2075965e45665e45962075554644924c73e54c74924643cf08230c3472a334730c0a228a0822610870a10872490990a020155f5dd5965dd55520159645d3de4c14924c13cf45d49265930c3416db34130c65c6db08209a20125a0816410851c70850820811c12005985d05585d05962005554504944c03d44c04924503cf08230c34028e34030c08b28a0800800842490840820802400820862001c6080143084043082082080040⟩,
  ⟨56,6,[ew149,ew188,ew239,ew257,ew269,ew270],localHints 6 0xd8100167b4fc1b105e0b00e04b0560181481e00a0c041003028004b98131720008d0170040601685401001c3b03808813805004 0x3a39644a59238ce48e2da8a14a285a68b48b2d78153a05575cb38b1d27dd69f75248769a74e7875de1ce39d5d71cb70855c20b2c75550526d869b61248169a60e6415d904e3985d704b5835560cb2c15550c75012140471c32080934cf4923d34424913d040238e09034f38d2493022cb08808a1c72481821c6083084045103002040⟩,
  ⟨56,7,[ew149,ew188,ew243,ew257,ew267,ew269,ew270],localHints 6 0x360bc0582c0200704306f10a12c3186206e1513310d0480ac0302903c0141e03007600c0a05f00204c2e0310000581000800e0b40b8020440640c00d02a04405004 0x3edbeb4efaedb4f4cf313baab6ea934ccb4ca8fb0caec30f3eaaea21da684e9a1d7484c821a9d73e75da6883c814e98832620e20a30c1934e37658d34c675d8cf3c66a418f3e369a14c30616218c3058218082065d718821f5d705379b75e6d34c175d6cf70169c04f3db69a0cc64139904c30338e0486035d80c82015d71455811960955504d34155024d34124823cf0924503cf14e38230c08e2cd30b28a2422080860871471c6182142083085041103002040⟩,
  ⟨56,6,[ew188,ew213,ew223,ew257,ew269,ew270],localHints 6 0x1b02002c1502803e5d08d8ba034008178140580700988200e09c0080604c0000e80501e030018210401dc2a0040120202204e 0x3a29234648e288e44e29085f4617d040a4517cc80a3a028c31f38e15879c45e71860545171574539d15555c38e6c868529a09165661959144261858e5c255708e39655508a5002d400a0022c20874c81532071c21420d148d41235144341034e3c330f0ce38d30c0cb0c128a04b2c32830c72481492071831450421030040c2081000⟩,
  ⟨56,6,[ew188,ew213,ew230,ew253,ew269,ew270],localHints 6 0x6c0800b0bc16c228630c40dc0102f0280b00e01300e030218180ea09c0080604c0000e8050460343b81600603c0c8040120200a811 0x3a49a546696490e44e2108e146385040845184c8883a220c32138e15b81e45179b6c54517987c538e15861e38e18874559d1482065960917196dc6514426db64e68261a08e3996180965c02170165822020940951455544c21420d148d41235144341034e3c330f0ce38d30c0ca0cb2082ca2432080c61c11470461831430421030040c2081000⟩
]

def nodesBlock15 : Array Node := #[
  ⟨56,7,[ew188,ew213,ew230,ew257,ew267,ew269,ew270],localHints 6 0x1b0bc02c2d81008a0a81401f45c18c310370a87490a0020be0502e03102601c1d82442210c1380100c0980001d00a0f83b81601a03010003030064110041260240a811 0x46ec2c530b2eb91511314bebbafad450cb8cad1b4cb2d31146bb2b293aa852aa134ca514a0fa4a46928f3e84510cc30a0ca28c30362719e9a451491e78651491b94645119b6e44510cc8c60e318c3038a138e8062a001451c79f71450079e7114406dd01145c6db0cb68031a60a64039900a2983970070161865871c01800945504d54145024d34114823d20914503cf04b04230c08e34130c08b08128a04b042282089201188047042182045102004083081000⟩,
  ⟨56,6,[ew127,ew188,ew213,ew257,ew269,ew270],localHints 6 0xd8100167b8fc9b205e0501601c02612c1382603a0b84180400c004ba0051740008d80c0040601084e01001c3b83e08815004803 0x3a39644a59238ce48e2d38a14a28534cb48b2d08153a055040b38b1d27dc79f71248779e70e7476dd1ce39c6db1cb68855a20b2c75550526574d95d24814d35ce60141804e39741004b5835560cb2c15550c75012140471c32080934cf4923d34424913d040238e09034f38d2493022cb08820a1c72481821c6083084045103002040⟩,
  ⟨56,7,[ew188,ew213,ew239,ew257,ew269,ew270],localHints 6 0x1b02002c1501f0505d08d8ba4ce20d0a1730284685c8134cc2090901700e068e98012f025c031b40006cc500050040350580c04000c3b85407c0880c0040ec0e02204e 0x5d3bb04af63052fbae5d36135cf56d66c62d66c5555cf60f48f42b50c4eb50c41048f4cf5c862a66856a6686185c85554a84e95084295084d34a84106a73cf0883266883cf0a530c5c06246618e46616185c08e34a14e25008225004d34a182015f3cf1c071e1403cf1dd71c0802db1c621b15a14e0802005d66186415556416185d65554914d35014105014d349141038e3cf38130c3813cf38d30c0812ca14520a1c71c90812081c1184145004082083081000⟩,
  ⟨56,7,[ew188,ew213,ew243,ew253,ew257,ew269,ew270],localHints 6 0xd810016b056005e0b6114010630c40dd170544280bc0a02c03804c3a82000e0044c0060002840284201e0902320c0460343b816042064018040300200a811 0x4ebb6c5adb2bad3593a9450f5963d452a596a5144f4d33d14694d3214a265a89945085969919c84e72114664d30c39483e51965a25248965865148934c64631934e245134f3c634618f18e3611c880636018820735f09679b75e6d658275d6d370269c0934db69a0830803c00076423c20985c02170030022020030021820830801805565815140565955144934c14510534d245134f40135004f3ce34c04a04b2082ca2412081c71411850421030040c2081000⟩,
  ⟨56,8,[ew188,ew213,ew243,ew257,ew267,ew269,ew270],localHints 6 0x361780585b0201141501f0501293500f0c61881b8540349a41fa680be0502e03102601d6103b45a05cbc8010e40189100024222c0287702c00806a260183880c8030440100c0780a60f80a811 0x294d774f3637573d7529461428f636672d7667261828fd4f4f253454fcf454f5144f2cf228e5b167063167059628e60e4ce46f54b52f54b4514ce50e12c3ee14e10e14e3ce12cb6c2896186695ab6696182895964e951454946a5495144e94510843e81491280893cf9c436608d38e3492e508938e3642cb2806186608a36606182808a24e05145407e15405144e07df14435e2803de15d38e08069c14038e09b69a08014008724908714d0802402976186415966416182975964d25145414515415144d24511013411453cf0820900813cf34d38e3412cb34138e34c2cb1451482812480811c6145006145103081000⟩,
  ⟨56,7,[ew188,ew217,ew223,ew257,ew267,ew269,ew270],localHints 6 0x360bc0582c0200701502803e1003186206e01c0d0020be0502e03102613849a140761f9098270020181300003a0141e80801c0480780c0060800c82105a02408804 0x42dbeb4efaedb504d0313baab6ea934ccb4ca90b0caec31042aaea212a674e99d24884d39cea0842820e3a741024b98832620b2c930c15e9634d38de7854d38db90541015b6e34106448853228448052200534dc79f7134c179e7104016dd05041c6db10c30111a04c3191181085c111704821611504604414510618114109350f4943d34c24923d044239109040f38e28c3422cd08c30a2cb08908a2082892422020861c4147106182142103002040⟩,
  ⟨56,7,[ew188,ew217,ew230,ew253,ew267,ew269,ew270],localHints 6 0x1b05e02c160100380a81401f04801c3186206e1d4110020be0502e0310268b81da1108609c0080604c0000e80507a020498464200340602500608c0781905a02408804 0x4aec2c570b2eb92552395bebbafad554eb8ead2b4eb2d3924abb2b254aa856aa14509555a10a494a92504284923679893a611e9635558de7845558db90449211b6e349215714438e10388538e16180426010d10524905555c79f71554179e7124816dd05249c6db34e38134104e38d31a0c96413190492433180450571043051411010955915164555425144524c241309249141034e3c234f08e38d30b08a08624918a1822420851c81071851421020c3002040⟩,
  ⟨56,8,[ew188,ew217,ew230,ew257,ew267,ew269,ew270],localHints 6 0xd82f03802c160100540a00f8404d618c3103745e0200105f0281701881309c9a00b03b04898c218272f4004030262480009181d00a0f4498074540380602004a00c0c80d1c602408804 0xd2cb54705b54f0cb20d25920cc5b45f3cb45f35960ccc8c44c4b14e6c314e649244cc0c0c956f5ed5af5ed5550c959646d3ee4c94ae4c93cf46d4926db30c3499ac34930c6eb9a60c58ea5e85965e88e30c55964688294c54924c582046849265930c3459a634530c6679a61041250c52650c15965e18e45e15960c18e34614924c18224c149246182010430c34175f34130c11e75d10425c10111c10124911b11a1012011191451042041011410c25985d05585d05960c25554504944c23d44c24924503cf10430c34228e34230c10b28a1021021072491071041022421022061071461041041021421041000c2040⟩,
  ⟨56,7,[ew127,ew188,ew217,ew257,ew267,ew269,ew270],localHints 6 0x360bc0582c0200704507110e12c2f8140b80c40984e4ce4343f02704c0741e82e07e01003063002014310370000381100800e084060020400440d00d02406404803 0x3edbeb4efaedb4f4cf313baab6ea934ccb4ca8fb0caec30f3eaaea215a684e9a155484c82129d73e75d24883c814e98832620e20a30c1934e29258934c692488f3c686318f3e286114c30616018c30579f7882065d718821d5d705371a55c6934c155568f6c149b04f3da4920cc64139904c30338e0486035d80c82015d71455811960955504d34155024d34124823cf0924503cf14e38230c08e2cd30b28a2422080861871471c6182142083085041103002040⟩,
  ⟨56,7,[ew188,ew217,ew239,ew253,ew257,ew269,ew270],localHints 6 0x6c0800b588b0c2b8560720081782c0381d4110070be0502e0310268b027212002268030001440142080f0fc1190682301a1d8070180060680401905a04808804 0x52cbad5eeb6cb145d4ad55505d741556b5d7a924905144124aa514255a675e99d55495d79d2a095282524a75142089894261579635658d75c55558d49054a41545234921461444041038854051618042601061052450575dc79f7175c179e7145016dd05451c6db39040138105004f39a0c96413990492433980451461041851411015975c25550975d65554d450249209451349239044239109040f38d08b08c24930b2822490851c81071851421040c3002040⟩,
  ⟨56,8,[ew188,ew217,ew239,ew257,ew267,ew269,ew270],localHints 6 0x3615c058560200e41501f0501013600f0c61881b80758a0fd1785f0281701881309c9a41da6402e5ec0087300c498001251180143b00e0040351380c040060018780a60e00c81a1c804808804 0xd5d775336775b3d750d56550d06766b2d766b26590d0d50532574590cf4590555532cf20cf5f16b06716b05d70cf64f50f4af58c56f58c49250f54f22c42e28f20f28f40f22cb6c0c56596a95eb6a96590c55d75295555854aa5855555294921083a80c54281273cf1853261053cf1a530c0c16596a18e46a16590c18e352155558182258155552182018841f28121f18141028839e18e3cf3816dd1813cf39c6db1812c11841451842ce1811410d86596825d76826590d85d751355558249258255551349220238228a41018619118241038e3cf38230c3823cf38d30c1822c928a1491042071821451041000c2040⟩,
  ⟨56,8,[ew188,ew217,ew243,ew253,ew257,ew267,ew269,ew270],localHints 6 0x1b05e02c16010038b1d6307521e3d0798071800083186206e9b13582245e17c0a05c06204d352650408b46700100c3200008d00a0600407845609407824450034118463d20840c80305a1d008804 0x576e34638d36d95615458df3db7cd8611d91cd5d51d35455573d33c975cd6183575f2618c534cd5553534f155534c352451186c2b5d7bd862f5d7ad862d4d3b9556e4d3b5555032cad1b124aaacda856189d7a676181575e7555153a055559d34d045115014545140898834d14814534530894690a1481459051888c16187e189f61806185f55505e8015557de79045105004145140874834d0480413413087036ca0480416c10c86811810c514318c0986195d76586025d75155564d35955544d341145240949145020f20d34e20938d34c20b18a28920924a2462071861021440c3002040⟩,
  ⟨56,9,[ew188,ew217,ew243,ew257,ew267,ew269,ew270],localHints 6 0xd82f03802c1601005407c1404b59a03c040630c40dc2a2cc07eb2c2f8140b80c40984e5940581dac902eb20878520020187a0500003cc278050f014c03a6e01c0900126d0180640180d1800d408804 0xd3db94b45f9574db60d35d30cd5f8677db86775d70cdd8d48d4f556dd3556d4d348dd0d0c95b36725f36725960c95c94894315474f15474104894c92ae3703c9b703c934dbeeb6d0c65d766a5ac66a5d70c65964aa4d354642b5464d34aa41010434d3c62e93c634d1282cb1042491061e71062491261c70c15d76629256625d70c19244a24d35418635414d34a286110434d3c17a03c134d11f79e1042491016dd10124911c6db10110110418610411a0c25d76585966585d70c25964914d35544105544d349141010434d3ce2cb3ce34d10c2cb10424910a1c71042491081c71041050c21851041000c2040⟩,
  ⟨56,8,[ew217,ew243,ew247,ew267,ew269,ew270],localHints 6 0x1b05e0700582c0200a80f8280960900780804e0740302600a1340d01201c4441700c0120acea01e0025f00a02936c000da8130a201c0c01502c4401800202e0281102000800c06abd 0x592c7446f5f44efc715925d258e5f3672c736725d758ec4e44e4b04e8bf04e849244ebce58896e66d5ee66d9655885c84488ec4dc4ac4dc8e3448488aa93ab348a2b34838eaa9a285825e76669676665d75829424424a44db8e44db4924428c21603a23427e214238e8607df15b21d78271d14220805b71b5835da65855a6585d75835434434944c64144c649244340310c38f3432cf10338e34c2cb1062092831c91032080461c6101082143043103082041040⟩,
  ⟨56,8,[ew107,ew217,ew243,ew267,ew269,ew270],localHints 6 0xd82f03802c160101141c44384d034048070860de050428130a20540b06c07e0ecea81f0025f40302a370000db80505008c0c00801e01c258220120300182e01a0800100a04a05c02030 0x696cb55706f55f0cb26966d668e6f4773cb47736db68ec8e54e5b15d0c315d059654ec0e6896ef76e66f76e6db6896495495ad5df52d5df59654950932a3ac449a6c30938eaeaa696816e87679a87676db6819815415a55de9255de5965419011a23a344186318138e46286119e2603017e01812491de7de6856c575c65975c6d86856585455855ca5145ca59354551348f4100c538e44540d0cf38d1ca2cb3052453052c80ca2481c21041850451851000c2040⟩,
  ⟨56,8,[ew217,ew243,ew248,ew257,ew269,ew270],localHints 6 0x6c1501f0500bc0e00b0580402582401e0201381d00c0980282e0180242681a024038158b203c0044d814052294000a40260c0010170141440381802a0581102000800c06abe 0x551b3242a5b24aab2c55159154d8f16305b16308e354d58d40d86f49f46f49f86140d44d5495ae62db2e62d596549b0940946b4a6aab4a6451409a89226369a099e9209349a269e65425a56248e56245965428c240246249e86249e45140284215e3600427e014234d05e7de15b25d20269d14224971b69a54359961751961759654350340345348b3d348b4514033c310b34e04330e10334d04b30b10724a20318a103249207186101082143043103082041040⟩
]

def nodesBlock16 : Array Node := #[
  ⟨56,8,[ew217,ew243,ew248,ew257,ew267,ew269,ew270],localHints 6 0x360a80f8280a402c2804f0200d40382504803c1381d00c0980282e0180240c8120562c80f001136050148a50002900983000405c0501102a088100040060680c2bf 0x4cfaaf3a752f427aaa4cf50f4d3514596aaa5965144d3aaa38e3cf4109e74103cf38e9e74cb7ee5ad52e5ad7df4cb50b38b76c41b3ec41b75d38b3cb0628e204b04b04b04b0628e24e65145abaaa5ab5144e6aaa3a83cf4299e74293cf3a89e71451654e64e50412cb0648a20642cb0638a24c35215a07e15a05144c37c33833de41a75e41a3cf38374319819804304318318305809819a2dc0836dc1832cb09a6da1981990430431831830580984c45175954975955144c44843843d14093514093cf3843441471470440441441440470471492cc04428c1442cb0492891471480440441441440470471410c31840441440c3042040⟩,
  ⟨56,9,[ew217,ew243,ew249,ew257,ew267,ew269,ew270],localHints 6 0xd82f03802c1601005407c1404b01e0202905009e14dd9bb2762091d802703a0181300509a0680900e05c030048190565f80f0010280a49400024e04c288070300540b03000405c050111ca0d41000304401006ac8 0x1d4ebd4f863d578eba1d46141d063c6bbebc6bb6181d0e904d0539572e395725144d0e101cb9b76b66376b69a61cb60b4cb93555e53555e9244cb50bab34343cbcb43cb410ab3cb21c66186b10716b16181c60464ef5145700705705144ef06f1414103ee06e16e4103ed06c1412cb06a06b1412cb06a0691c46286a79a86a76181c49844c452555d92555d5144c49040e14233c48230c44108a18200dd2df04479f0c42cb05d79d0c105c1c41841c261b6995db6996181c25c24c25165494965495144c248214e4113c23511424103ce34d1492cc04228c1422cb0492891410481c21821411040c2042041040⟩,
  ⟨56,8,[ew217,ew243,ew246,ew257,ew267,ew269,ew270],localHints 6 0x3615c058560200e41501f050100078520a013c1a80704a18c0306206e0143b03f0860300182b2fe078008f50280a49500025204c2700e0300c0010170140800a80d0220e0190220240100d019 0x614d774f3677573d756146546106766f2d766f2659610d504f2534550cf45505144f2cf260d9716f06716f096560d64d4cd8af55e52f55e8a24cd50d06d42e3cd04d3cd40d06d7ed6296596ec9656ec6596299654ea51456b8a256b5144ea8a210412862942804134d1a779e06734d19f79e6006596e39666e36596009654e35145408a45405144e38a21031033c041010012118341010134d0407a010034d05f79e10329d3c03dd10010018304360265c6da5dc6da6596025c24c251654b49654b5144c24821894113c20421824023c920918b34e20230e18234d20b30b1892891820421822821892071810c51020051020c2041000⟩,
  ⟨56,8,[ew114,ew217,ew239,ew257,ew267,ew269,ew270],localHints 6 0x3615c058560200e41501f050100078630c40dc0383f0560780a0290260c00b80a0640802218000c1cc0092c00a4ac460000701d8070430180880101803200c0681a02235c09004 0x90c734af57352fc7109055008d57262ec7262e55508dc4d4ae43050dbf050d4104aebee0895ed62c56d62c5d70895494894eb50b42b50b4d348940912936a2091092093491293290875556265e86265550875d74a64105074e75074104a64d328a2a50873651042493c72e41072493cc2cb08056362286362255508084048042051c7e051c4104807c03d934d2001003c03402191593dc25e14075e3c024915c75c3d969b3c01db3c06803d91c70965d76015556015d70965554914d35014105014d34914103c134d28f28e20834d28128110c2cb2812491012cb2842492082060811c6105103081000⟩,
  ⟨56,9,[ew114,ew217,ew243,ew257,ew267,ew269,ew270],localHints 6 0xd82f03802c1601005407c1404b01e0203186206e1516703f0560780a0290261440a81606005c0510e064604290060024b82800525a13c003b403414c07007086090060020440640180d0223981a804 0x91db94f45f95b4db60915d108c5f86b7db86b75d708cd8c4cc4755aed355ae4514ccd0c0886336b25f36b26180885c84c85315894715895144c84482af3303c8bb03c830c2efbae0865d76ab62d6ab5d70866184eb45158652c5864514eb5141c430c3c636a1c630c3e934d1c42081062681c620810b2490805e76a69676a65d70809404c046459d8e459d4514c08c01213223c08223c030c12182011d21f10079f10020811d79d71c71b1c01001041860816186995d76996180815d74d25145954515955144d24513d034d1ce30c3ce34d1c430c10b2491c420810a2491c42081c4105081185104103081000⟩,
  ⟨56,8,[ew217,ew220,ew243,ew257,ew267,ew269,ew270],localHints 6 0x6c2f00b0b60402282a03e0a02500f04e0740302600a1501700c0121482804f06a01c1282201a0480c85f3040047b0140b84c00012f06204c3b8160760081201706400c020200220f80c015 0x551d364325b64b2d3455159154c5b55f1d355f159654cd0c43147348ccb348c451431cb154aa705ef5b05efa6954a58a40a9ee4a446e4a49e740a44a06c32d04a04a04a30a06c26c5465ab5eaa6b5ea596546a464064684a39e84a34514069c609a32604604608630605a6da0a32a56c692508628a6e392355f5965e25145e259655f5144204514a138e4a145142038e10411e55f31e04128a09d20805d28a08920808118609c69a09c18609b6995435965cf5185cf59654351440f45148339348345140f38e10010004330c10310d08030c10128a04320b10328a049208103187080047100186043043100105043045103103080040⟩,
  ⟨56,8,[ew136,ew213,ew243,ew257,ew267,ew269,ew270],localHints 6 0x6c2f00b0b60402282a03e0a02500f04e0740302600a0b8060090be170188070760c8110443060503900126404c9888b0000f83b81604805c1000201a064018181b005408804 0xcfc3246e5324eec300cf50f0cc5315edc315ed5140ccc0c46d3ef4ccbaf4cc3cf46dbad0c896c5eb52c5eb9650c85084488ea4e13ea4e18e34483c81283291081081083081282e80c55275e69675e65140c59454453e44e08e44e03cf4458c539830c1051053853051181d83a02221c58623852081e08600c15145dd59f5dd5140c159645d3cf4c149e4c13cf45d49224925c0c131c10420838129b10120838b28a38115a39961a3991453816010d55965c25145c25960d55144504924c23cf4c24924503cf38230c24e24d10430c24224210b28a24220810228a2442081071060c21451041000c2040⟩,
  ⟨56,9,[ew136,ew217,ew243,ew257,ew267,ew269,ew270],localHints 6 0x1b05e0700582c0200a80f82809603c0402703a0181300509a0480702e0180242f85c0621396783b21c0c8c20520280049a0500264cc2780076a0602981600e0900b80203200c1000d1ce0d408804 0xd0d784b35b8573d750d05900cb5b7676d776765960cbd4b48b43456dcf456d41048bccb0c8ab26715b2671aaa0c8588488a30563430563a284884082ae2ef388b6f3882cb2aeb6d0c65ac66baac66b5960c6a86486429562a29562410486a061262e73869673862cb1269651222241068e41062081228e20c159665f5e165f5960c15d749f4105414e054141049f4d31442cb38131e1412cb39d30c14420810125c14120810a2496db6da1441861011010c25d76585966585d70c25964914d35544105544d349141038f30c14d2cb38d30c1442cb10a24914420810a2491442081041070c21861441000c2040⟩,
  ⟨56,7,[ew143,ew217,ew243,ew257,ew267,ew269,ew270],localHints 6 0x1b05e02c160100380a81401f08003d68ad009a0b93782b0280a40f0130780540b03b0641182900100c1400004f00a0201c00e00e0880b8180180081080906a00c1682001408c08804 0x572d30634c32c95615498cefcb3bd8612c92bd5c52c3149556fc2f2d7bac62eb175cb618b13b4b56d2d34ec555a90acb4ab2d042a4921986295d7a586065c61955684d3a155464c61529c642719219141014d9862e618d1a52cb0d89218e48586038e38558838220d55618207927c375f0d249e75d0cb70135c04b2c33430466c315b0c61816811d86195d76586075d75155564d35955544d315248e4103923d140f14d34e2cb38d28c2ca2492071861430c4041103002040⟩,
  ⟨56,6,[ew197,ew217,ew230,ew239,ew269,ew270],localHints 6 0x1b02002c5e0b1112120238340060ac0a02903c04c3f81602a104660060022f40289100001c1e8020441d80b82305a10005004 0x2e29233e48e288b3cb24f85f4217cf3c94107cb80936024b2df34d15979c3de7196453cf7167452dd15659c2cb4946c525b15451224904f69765a5cf3c16595cb60159804b2d75964c95415150492535140520531454d248114109044c3d13104023cf30d3822ce08d34c2cb08328724a1c31c22490832071481c3182142103002040⟩,
  ⟨56,7,[ew197,ew217,ew230,ew243,ew267,ew269,ew270],localHints 6 0x360bc0582c0200701382603a0f50a84808e0d02504c0060ac0a02903c04c1e0160741190881501e0a8030010500140f800128020038090040880b82305a03005004 0x32dbeb42faedb4c40c290baab6ea9040ab4aa8cb0aaec28c32aaea210a674699d04084519cca083a820c32738e0ca9880e620a28b0e515d92242489d74541089a8c532315a6a230c4d88452a115861328a0e07c521f05079b75e6d040175d6cc70169c04c31b69a50a64161904a2946180c85c10d70482035950530541455134c114109148d41235144241034e3c230f08e38d30c2c32422890830862081831822080831c6147183182142103002040⟩,
  ⟨56,7,[ew197,ew217,ew239,ew243,ew257,ew269,ew270],localHints 6 0x360400584808e0d169ad20821f90a82f058070250030560501481e02603c220464240f00a8160ae0180085600a0e40001802e0083b01200e0880402305a03805004 0x36dbee46fbadb4d44d2d2b2a46ca9248b451a8facb36b2cf3ea34da51448492211469492a0d3483cf20d3683cf0cb2c80e720b2e60e51519224a489144549288d8c53e314d3623cf14b8546a150b5056850cc8052200517dc79f71144179e70d7416dd04d35c6db05a0552cb55a6812c10c86410c10480436175455815160451555140924ce45339248245138f40235008f3ce34d3032822ca0830862081832422020831c6147183182145103002040⟩,
  ⟨56,8,[ew197,ew217,ew243,ew257,ew267,ew269,ew270],localHints 6 0xd82f0160b00801c09011c1a04a04e0741303d4620481fa300560501481e0260f01f01602a03c1d04645a064c285200c0049b05000a4d4278000f2090040070980600b80276c0b4110033d20241082315a0d405004 0xd4efd5b96bd679efb0d46940d16bc778efc77869a0d1ed15b853a651e7a6515145b8e780cd6f77756b77756db0cd69a5b55f664d53664d5d75b55143e293438d47414d9241624510c86b37726f377269a0c86c85885316465f16465145885c82ae4703884c82884484eebee28636d3c8488288348486b060c16ab768aab76869a0c1aaa5a85296419e96415145a89e71634663819261414519639241418813e334d1638a24c13411522082817a114120881f79e0c26db75c69a75c6db0c269a5955d76585146585d75955144d34900c24503ce38c0c234c28b2081491862892081471861441000c2040⟩,
  ⟨56,7,[ew204,ew235,ew267,ew269,ew270],localHints 6 0x1b05e0700582c0202043488009a048070863f41bc031d6002214f80053de0002581800e090078084c47a8360030040341d83a 0x50e8643df4e445f86150e4ce50b4e35e28635e24d350b84b3cb3a04487e044838e3cb7cb5044de5dd55e5dd4d35045443c439c44041c44038e3c440409a2db30465b3042cb09a6595035585d64d85d65555034c33c34124413924414103c33832892cd30320d3032cb2892081c1105183005083103081000⟩,
  ⟨56,7,[ew204,ew243,ew260,ew269,ew270],localHints 6 0x362ec4400b1600401381d04c1340900e05433c0f80614c004140c200a304003b73ae060038240840f01700300403406009 0x4cd82339e4a341e8204cd48d4c94a25a18225a14924c980938935f40679f40634d3897894c449d59c51d59c4924c450438435b4003db40034d3843c409925a28461a2842490996184c35175954975955144c34833833d14013514013cf38334330724b28318b283249207186081105083005083103081000⟩,
  ⟨56,7,[ew204,ew243,ew260,ew267,ew269,ew270],localHints 6 0x360ac0582903c0401000704e0741303a0240a86781f00c2980082818401460800048440180180840281700300403406009 0x48c86335e4633de86148c44c49245155586155545149286134d30c3cf79e3cf30c34d79e48646255f86255f45148686135f3203c67a03c630c35f79e75d75c48649c48445b55a4db55a4514844c43443193c03993c030c3443842170972042042042042170972171982042042041842170974834d65544565544d34834433433903c13103c138e3433032072c72032032032032072c7207289203189203203207186081105083005083103081000⟩
]

def nodesBlock17 : Array Node := #[
  ⟨56,8,[ew204,ew243,ew261,ew267,ew269,ew270],localHints 6 0x6c1781c0160b00802b0520781e2d65aa09c0e82609a0480703a040b50151d803e01800828374014dc8000960600382401e020881370140c01700300403406009 0x210aee46956e4e9aeb21055020d56d62caed62c55520dacd44d42a4caa6a4ca41044da4d2075686260a86265552070874664274c70a74c74104660a66c234d3870a56c734d3a40a32045626215a26215552045844444204c04a04c041044448409e35f38475f38434d09e75d0821dc6c40846c41c408209a2035996175596175962035434434944c14144c149244340330b34f38328f38334d30b28a2492462031c6081105083005083103081000⟩,
  ⟨56,6,[ew140,ew204,ew243,ew253,ew269,ew270],localHints 6 0xd8100163806b0993e2764dd84d0be0182e0050620081907f0280045d813110000580180940380383303200c3a8210840f008804 0x3a39644a59238ce48e2da8a04a281a68b49281884b3a12d862038e1927de69f79248668618e75461d50e38660650b70629c18b19429405a6d74925da6814925d864138e05861738e0ca5812d604a2832cb0465435150c61815140934cf4923d34424913d040238e09034f38d08b08c28a20b2422892081c2186083084045103002040⟩,
  ⟨56,7,[ew140,ew204,ew243,ew257,ew267,ew269,ew270],localHints 6 0x3615c058560200e42404706812937a701021a44004d01a17c0305c00a0c4270020640e80a00105604c0f0000520581000e00e0940b83303200c0c02402a02808804 0x42dbeb52faedb50510314baab6ea9450cb4ca90b0caec31042aaea25da675299dd7495149dba0942825b6e741014c98916624c3059641948e27638945067461908566e15904066c614e80632018e18830c5895867c61891967d605d79a51469d74151469b70141005b6da4100cc64139904c30338e1456012580465c35970c61815960955515144554c25134524824100923d140f14e38230c08e2cd30b08908a14a2892421422081c2186083085041103002040⟩,
  ⟨56,6,[ew204,ew213,ew223,ew243,ew269,ew270],localHints 6 0x1b02002c1382603a3806b09904600c5d8141602200987f00e0a8030010500140f800024024010210401dc250040180382103c 0x3229234248e288c40c29085f4617d040a4517cc80a3a028c31f38e15879c41e71860541071574531d15555c30c6c868529a01065661959040061858c5c055700c31655508a5002d400a0022c20074c81532071c01400d148d41235144341034e3c330f0ce38d30c0cb0c128a04b04328a0c72481492071831450421030040c2081000⟩,
  ⟨56,6,[ew204,ew213,ew230,ew239,ew269,ew270],localHints 6 0x6c0800b0bc16c2284808e0d0018570281581c81300e024218180ec0a8030010500140f8000340903b8160040480b8040180380a80a 0x3249a542696490c40c2108e146385040845184c8883a220c32138e15b81e42079b6c54107987c531f15861e30c18874559d1482065960907196dc6504026db64c68261a08c3196180965c02170165822020940951455544c21420d148d41235144341034e3c330f0ce38d30c0ca0cb2082ca2432080c61c11470461831430421030040c2081000⟩,
  ⟨56,7,[ew204,ew213,ew230,ew243,ew267,ew269,ew270],localHints 6 0x1b0bc02c2d81008a09c1301d464120238340947490b0030560501481e02601c1d20e0860a8030010500140f8000981dc0b02401a0241000203005c128041280300a80a 0x42ec2c530b2eb90510354bebbafad450db8dad0b4db2d35042bb2b294aa856aa1450a555a10a4a4a92904284920cd34a0ca28d3432e719e9a452691e78651491b94642519b6e44100cd8c60e318d3438a13cf8062a00147dc79f71450079e7107406dd01041c6db0cb68035a2ca6403d900a28b3d80070171865c71c01800955915164555425144524c241309249141004c04234d08f38134d08c08128a04b04228a089201188047042182045102004083081000⟩,
  ⟨56,7,[ew204,ew213,ew239,ew243,ew257,ew269,ew270],localHints 6 0xd810016120238345b0b5d1905e0b61142521600615c0a05607204c3b02000e0184b80100a2800003802e0082201201a1f90581a0481dc0b0040300380a80a 0x46bb6c52db2bad15113d6aa852aa1658f514a13a4f4693d34e84519d450c59631452759699144c4d33114664d32cf3cc2cc30f3ca2e51549225a48945055968918c54e31514624d328f84542114f14a4200c37c531f09479b75e6d450275d6d170269c09145b69a0030023c20830803c00830803000106423020985c01570030021425565815140565955144934c14510534d24514103813ce2cc3412cd04c30b2890470481452071811450421030040c2081000⟩,
  ⟨56,6,[ew106,ew204,ew213,ew243,ew269,ew270],localHints 6 0x36040059ee3f26c85d8141602200984d0540a00f82e106010008061c00004c8051ac084048030300e01e00e00e9803b84c08412806002 0x4a59e65679a59525523159235248d554c50c3128974225d248c40c25585e8217955498207927c975f25249e75d20c7095dc24c3085d70546d955b65450155565068149a05041949204c6035d80cc3015d70c85812560482032490955515144554c25134524824100923d140f38e34230c08924b2082891c2207083086045103002040⟩,
  ⟨56,7,[ew204,ew213,ew243,ew253,ew269,ew270],localHints 6 0x6c0800b1c03584c82703a09841a7142c2ec0a0b011004c0382301a9c03fa0f03276803186130004de805378284000200041dc25046006091060090980940c0040ea0842103c 0x611c324f15b2571c3061159160d66f6ad5af6ad65960d5964ed52e54d46e54d5144ed45160b5ac6ab66c6ab59660b64b4cb46a54852a5484514cb50b08836980ba0b80b34b0889c86005a66a39666a35966009654e34645408a45404514e38a20804211c636116015f08034015e2cb1c06dd1402cb1dc6db6176596815966816596175964d25145414515415144d245108140f14534f1c71ce08134d28a2cb3012083012cb2892081c1184145004082083081000⟩,
  ⟨56,8,[ew204,ew213,ew243,ew257,ew267,ew269,ew270],localHints 6 0x1b0bc02c2d81008a1202383409408d3a02703a0982a2730240fd3902b0280a40f01300eb641d22903261c030720024e4029381160003b8161d005c0100d0060911300904a0100c0790a61300a80a 0x3d2db85345f85b4db63d25d23d05f76b3db76b35d73d0d905334b5590d35590492533d333ce6726b05f26b06593ce5d753057158e4b158e55553049208442f14e12f08e410b842ad3cb5ec6ab66c6ab5d73cb64b50b4aa58856a58849250b54b12742914b10b14b40b127a273083a608b28b08b38b2889483c05e46a18e46a15d73c08e35214a258082258049252182014431f3c041f08014008738e08714a08038015e2cb0806dd1402cb09c6db3d86596815d76816593d85d751355558149258155551349210128114541008209108141014514d3c138d28a2cb3012083012cb2892080811c6145006145103081000⟩,
  ⟨56,7,[ew204,ew217,ew223,ew243,ew267,ew269,ew270],localHints 6 0x360bc0582c0200701382603a0f42404706801c118030560501481e0260f04a2160741190982a00c0041400503e0002000e010048078090040800b82106603005004 0x3adbeb4afaedb4e48e2d2baab6ea9248bb4ba8eb0baec2ce3aaaea212a674e99d24884d39cea0842820e3a741028b98832620b2ca30c15e9634a58de7854928db9053a415b6e338e6448852e28448052200527dc79f71248179e70e7416dd04e39c6db10b68111a04b2d91181085c111704821611504604414510618114109350f4943d34c24923d044239109040f38e24c3422cd08c3092cb08a08920824a2422080861c4147106182142103002040⟩,
  ⟨56,7,[ew204,ew217,ew230,ew239,ew267,ew269,ew270],localHints 6 0x1b0ae02c2b01007209c1301d00e120238340ec0940182b0280a40f0134640e90704301a0a8030010500140f8000800384a07e42a090048220040680901706603005004 0x42ec2c530b2eb90510394bebbafad450eb8ead0b4eb2d39042bb2b254aa856aa14509555a10a494a92504284923579c93a711f9a452691f7c451491c94442511c72441015814438e1038c538e16284426110d10524905481d7e07545017df75078171e05041d71c34e38134104e38d5db0c96815da0492435d90450581045c51411010955915164555425144524c241309249141034e3c234f08e38d30b08a08624918a1822490851c81071851421020c3002040⟩,
  ⟨56,8,[ew204,ew217,ew230,ew243,ew267,ew269,ew270],localHints 6 0x6c1781c0160b00802704c0741ea7501c120238340948cc0182b0280a40f0130789c80b03a4c610c1518800c0041413b00a4e80f80008025003a300100241002200405c068241d203005004 0xd0cf64b15b6531cf30d05900cd5b5634cf56345960cdccd48d43250bc7250b41048dc4d0ca5b062e5f062e5960ca5d74ae42f50a4ef50a4104ae4d314534d38aaed38a34d16caeb0c68ea6285aa6288e30c65964a88295064295068204a841069a34d3862e738634d6a62cb1451250c62a50c15a46218e46215960c18e34a14225018225014104a182014534d38175f38134d15e75d14529c14115c14128a14515b14124115a1861452451411810c25d96115996115d70c25964914d55024155024d349141010434d3822cf38234d10c2cb14210214828a14814514228a1422471481871451451421821451000c2040⟩,
  ⟨56,7,[ew204,ew217,ew239,ew243,ew253,ew269,ew270],localHints 6 0x6c0800b0ae1581cadb5b41d81782c038094038030560501481e02608d1603c41e0184d00100a288000180040380b8410241183f20d0340903a80806603c05004 0x46cbad52eb6cb11511396ae952ba5658e514a53a8e46a3934e9451a1450b5962d45285969d144b4d32d14674d32cd35a38e0cd98b38e1149635a58d45045968d19044e41114634d310d8623a168d3443844108042e00547dc79f71450179e7117416dd05145c6db04e39a34d68e38134128b2c128104b04a2990c46012980441032975565825140965955144934c24510934d245108e3d034f1ce38234d28b30228c08b08a2480860871041c61421040c3002040⟩,
  ⟨56,8,[ew204,ew217,ew239,ew243,ew257,ew267,ew269,ew270],localHints 6 0x1b0ae02c2b010072120238344ecb756e0764ea4487c0f700e095198c30060ac0a02903c04d39a640408a4680060023240288c0000600707946205c01022024035138240340e03f1e90661cc05004 0x4f6e345f8d36d935d3457df3db7cd75d1d91cd3d51d354534f3d33398cb05f2c1860e5d7c15c4e4f13955704d341144e40e39145016fb975cb6182d75ee618b534cb5552d34ed5552ca2d2451186b0a38e2ca2cb38e14aae45d7a9862a5d79186284d3a555694d3a155502a79119c538e98622638e1469524a390b8c15e27e189f5d706185f4e005e8014d37de79045105004145140a7411810ce38318a28b2c128104b04a29c0db28128105b04329a0986195d76586025d75155564d35955544d341145240749145014f18634238d28b2cc28730b2ca1491882071471c81c61440c3002040⟩,
  ⟨56,7,[ew106,ew204,ew217,ew243,ew267,ew269,ew270],localHints 6 0x360bc0582c0200704507110e1341c02b0280a40f0130789c42302a05007c2002e07e010008060900001a00508e0201280e00e084048030400281180d01e05c06002 0x4adbeb56faedb52552395baab6ea9554eb4ea92b0eaec3924aaaea215a68529a155485082129d74275d248840814e98832620e22530c1959218e48555468e38528868221924a182014e7c615f18e38575e7482065d718821d5d705471a55c6945015556906c149b05041a4920cc64139904c30338e0486035d80c82015d71455811960955515144554c25134524824100923d140f14e38230c08e2cd30b28a2422080861871471c6182142083085041103002040⟩
]

def nodesBlock18 : Array Node := #[
  ⟨56,8,[ew204,ew217,ew243,ew253,ew267,ew269,ew270],localHints 6 0xd82f0160b00801c09011c1a00704e0741303d4ec0481fade4660ac0a02903c04c1e27401a0e9328193120183a00127a0149e08d0001d4040200300083c85304205c230030488a0048231d403c05004 0xd3df95756395f5df70d36130d16386f4df86f46180d1dd15744f65d1d765d14d3574d740ca6b36f16336f169a0ca6185715b25ca4f25ca5965714d310d1f00ca4700c862f6ee6af6ee6180c86885484ed5c55ad5c54d354858836a46c3c83483c844836aaea2c52a9108a081082882c59c50c16266e39666e36180c19655634e45c18a45c14d35638a22cd4613c13612c14513cd1e02c14012c428a2c441f2c12812c720824171e2c120825d71c0d969a6c26186c269a0d96185545965c24d35c25965544d33421c23cf4512cb2d22c24512c240e3cf28e10434c2c228a1c72082421452422081c61451041000c2040⟩,
  ⟨56,9,[ew204,ew217,ew243,ew257,ew267,ew269,ew270],localHints 6 0xd82f03802c1601009011c1a04a5c609c0e82609ab880900e07eb84158140520780983c5c00596f83a5920648905200c0047c05000a3dc278000f214c03a7701005c0100d0069b4048241860d405004 0xd0db94b45b9574db60d05900cd5b8677db86775960cdd8d48d43554bd3554b41048dd0d0ca5f36715b36715d70ca5964b14f254a43254a4d34b141010434d3ca2f03ca34d12f2cb0c75ae66d5ee66d5960c75c748742c5454ec5454104874c722936b3c7a2b3c734daa9a282052a71071072072871059850c15a56629256625960c19244a24235418635414104a286120434d3c17a03c134d11f79e20120110428a20421d2041c720169c2011c721b69a0c25d76585966585d70c25964914d35544105544d349141010434d3ce2cb3ce34d10c2cb2082090c22891041c72081452081c71061451041000c2040⟩,
  ⟨56,8,[ew217,ew235,ew257,ew267,ew269,ew270],localHints 6 0x1b05e0700582c0200a80f82809608c0780804e0740302600a1340900e2220b8060090be76c188013140502e1bf0006f80985100e0600a81604a008122d421c0c8100040060340c811 0x5d3c744af63452fc715d36135cf6336b2c736b26185cfc4f48f4f0528bf05284d348fbcf5ca96e6ad62e6ad9655ca60a48a8ec51d4ec51d8e348a4ca2e93eb38aa2b2ca3cfaa9a285c36276a69676a66185c39434834e451c8e451c4d34838c30a13e23838223833cf0a18207dc29e2c375e2c328a09c75c5c461869959b6996185c45844844d35004555004d348444414d3d03843101443cf38d30c14228a2c408414428a0890881400c61c40461440c3080040⟩,
  ⟨56,8,[ew128,ew217,ew257,ew267,ew269,ew270],localHints 6 0xd82f03802c160101141c44384b04603c040810d2050400130a20540b06c07e0e8ee01d00c62c00827382014e000004c0680c00e02401c268250180240102e01a0800181104406402032 0x694cb55706755f0cb269465468e674773cb477365968ec8e54e5315e9c315e951454ec0e6896ef76e66f76e6db6896495495ad5df52d5df59654950932a3ac449a6c30938eaeaa696816687679a87676596819815415255de9255de5145419011a23a344186318138e46286119e2603017e01812491de7de6856c575c65975c6d86856585455855ca5145ca59354551348f4100c538e44540d0cf38d1ca2ca0c52493052c80ca2481c21041850451851000c2040⟩,
  ⟨56,8,[ew217,ew243,ew257,ew260,ew269,ew270],localHints 6 0x6c1781c0160b00802a03e0a02582301e0201381d00c0980284d0240381700c01217c598310022700a05c150000538130a201c0c01502c094010245aa0c8100040060340c811 0x592bf246d5f24edbef5925d258e5f1670bf16705d758ebce44e4ae4e6b6e4e649244eb4e5898ec66b5ec66b8e35895c944986a4dc4aa4dc8614494892a73a93499a928938ea279a65835e56648e56645d75838c34434a24db8624db49244384309f3a03437a034338e09f79e09b25d28371d28324909b71b5845d765855a6585d75845444444924c04144c049244440414c38f3442cf14438e34c2cb1422492840841442490880871400c60840461440c3080040⟩,
  ⟨56,8,[ew217,ew243,ew257,ew260,ew267,ew269,ew270],localHints 6 0x361480585009e0401a80705407c1401701e09c0e80604c0141100d0240b8060090be2cc188011380502e0a800029c0980a02a094010235ac0c8100040060600c811 0x4cfb6f3aa52f42ab6d4cf50f4d3514596b6d5965144d3b6d38e3cf410aaa4103cf38eaaa4e95145aeb6d5ae5144e9b6d3ab3cf42caaa42c3cf3abaaa1451684e94e84c98275a65275a68204c95093897a54193e541979e3893c92a32a30890892892890a32232a32a40890892892890a32234c35225a18225a15144c38033833df41879f4183cf38378309b71b08308308308309b71b09b75b08308308374309b71b21825a28365a2832492186584c45145954975955144c44843843cf4003514003cf38434414b14b08408414414408b08b14b14c08408414414408b08b1422492840841442490880871400c60840461440c3080040⟩,
  ⟨56,9,[ew217,ew243,ew257,ew261,ew267,ew269,ew270],localHints 6 0xd82f03802c160100a414027853776ee81501f05012c1180f01005c1381d00c0980284d024039dcbb805c0300485f3180c4008140b84fc0013e0261440381802a058050eb06a008128245be0c8100040060340c811 0x315ebd53867d5b8eba31565531167c6fbebc6fb659311e915115795abe395ab555511e1130b6596f70b76f765930b08b5355555b60b65b65555350b51424514340b41744514330b230a9f16f06716f09e730a64a50a96f59e56f59e96550a54a26c46e40aaee24a451b6caeb24222a30a2ca3036696e89e96e86593039c350356659d96659d5555039430a34644038a44034510a38a20820a11430831430830820a009d29f24379f24328a09d79d3046596da61c6da6593046045045555804d75805555044c414f45240439214445140f38e14208d3042c414228a2440840880871400c60840461440c3080040⟩,
  ⟨56,8,[ew217,ew243,ew257,ew259,ew267,ew269,ew270],localHints 6 0x1b05e02c160100381482804f06a01c240470681d40102703a0181300507a0481103f0860242f98d0620047c8140b8504001400260f0040180400541200a0600940782302e0c8108040061180c811 0x655db85346b85b4db66556956516b7733db773369a651d91533575591d35591555533d3366f9a673269a7329a666f69a5309245b15555b192453055528a2ae66f46e6479ad72b6ad72b9a664769a52b92c58756c58792452b5552892894074512872aa1494512893e94074292872871492096436a87279a872769a64398350356559e92559e5555039032224634032034034432227e215e85e20320320384315e7de21e1e02832032831c321e7de64469a71b61d71b69a6446045045555804d75805555044c414e45240420414444440e34e14e3ce1442041443c414e34c14824b2841cb2842442081c71400c60840461440c3080040⟩,
  ⟨56,8,[ew96,ew217,ew243,ew253,ew267,ew269,ew270],localHints 6 0x1b05e02c160100381202383400e09c0e82607a0481f85f0620502e0130600802103208c0640898e0021d003143000508468050421d40401802e0082180904a00c1202301436407804 0x93cb44b05f4530cb20935d308d5f362fcb362f5d708dc8d4af4f150dc3150d4d34afc2f08b56e62c5ee62c55508b5d74ac42d50b4ed50b4104ac4d31c71eb08b36b0865ea62956a6295d70865464864e85084285084d34864061263673061063063461262663c82e51061061062c63c82480805d76238a46235d70808804804d35198215194d34808003dd34d3001003c034031d15d3dd79f3c02df3c07803dd2cb3d919c6c069c3c01866d96990965d76015556015d70965554914d35014105014d34914103c134d1cf1ce30c34d1c11c130c30a0812ca1092081c11861012081c4186105103081000⟩,
  ⟨56,9,[ew96,ew217,ew243,ew257,ew267,ew269,ew270],localHints 6 0xd82f03802c1601009011c1a04a5c809c0e82609a0480703f0be0c40a05c0261440a8162200c01901902263c2900100c5142800028813c02bbc04614c0400702e0082180d012094018240143b01a804 0x94db94f46395b4db609461408c6386b7db86b761808cd8c4cc53558dd3558d5144ccd0c08b5f36b16336b15d708b6184f147258b53258b4514f151418430c3cb37018b30c3ef34d08562e6ad5ee6ad6180855c54c552c58746c5875144c544522a32b3c5a6b3c530c26aa692072e81851051852c51072470806186a69676a66180809404c051459b8e459b5144c08c02213223c08223c030c1218207df7de1802001042cb21b15d20071d20014521b71b0816186995d76996180815d74d25145954515955144d24513d034d18e30c3ce34d18430c18820a0812ca1091c71881452081c7184145104103081000⟩,
  ⟨56,8,[ew217,ew218,ew243,ew257,ew267,ew269,ew270],localHints 6 0x6c2f00b0b60402282a03e0a02502703a018130050a80481700c0121482804f06a01c1282401e05c1102b3200047d01405251c0014603c04c3b8160600081d00301a064020200141300c015 0x551d364325b64b2d3455159154c5b55f1d355f159654cd0c43147348ccb348c451431cb154aab05ef5b05efaaa54a58a40aa2e4a446e4a4a2840a44a09b32d04a04a08a30a05b71b5485ac5ebaac5eb596548a884084694a3a294a3451408a080663270480480483080661e61e32a508892508828a1e392355f5965e25145e259655f5144204514a138e4a145142038e10411e55f31e08128a09d6db09d28a09c6da0412080991860592080871865435985cf5185cf59654351440f45348339348345140f38e10010004330c10310d08030c10328b08004b10028a043043101208043189103208047186100105043045103103080040⟩,
  ⟨56,8,[ew145,ew213,ew243,ew257,ew267,ew269,ew270],localHints 6 0x361780585b0201141501f05009c0e80604c0142a01205c0300482b0520780383004a1081d1910281c800949026520458000980f83b81604805c0100d032080018181b405405004 0xd0c734af57352fc710d05500cc57262ec7262e5550ccc4c4ae43050cbf050c4104aebee0c9a2d62c56d62ca280c95494899ab52242b5229a64894093da30c1091093c930911a2da0c556a629a2a6295550c5a054854275219a75214104859851243251051051053051242242212633c58a33c52492218a10c156061e5e061e5550c15d749e41f5014df50141049e4d318619d0c131d3c125c3db69c3db2493c16811041453c11d91011453c81c70d65d76025556025d70d65554914d35024105024d34914103c230c18e18d10430c18218210b10a0c22491081c71821451021c71841451041000c2040⟩,
  ⟨56,9,[ew145,ew217,ew243,ew257,ew267,ew269,ew270],localHints 6 0x1b05e0700582c0200a80f82809603c0402703a0181300509a0480702e0180241582903c0f1729100600e8c9052028004a58500265282780077a0602981600e0900b80203200c1000d1da0d405004 0xd0d784b35b8573d750d05900cb5b7676d776765960cbd4b48b43456dcf456d41048bccb0c8ab26715b2671aaa0c8588488a30563430563a284884082ae2ef388b6f3882cb2aeb6d0c65ac66baac66b5960c6a86486429562a29562410486a061262e73869673862cb1269651222241068e41062081228e20c15a165f5e165f5960c15d749f4205414e054141049f4d31442cb38131e1412cb39d30c71c71b1442081011011441861011da1411861041c70c25d76585966585d70c25964914d35544105544d349141038f30c14d2cb38d30c1442cb10a1090c22081041c71441861041c71441861441000c2040⟩,
  ⟨56,8,[ew181,ew213,ew217,ew243,ew257,ew267,ew269,ew270],localHints 6 0x361780585b0201141501f050128078630c40dc2a03f0ee110092e746a05173234026038198170700446880100c3280008b00a0340b04c0040300c8030300680a83e0441c856035 0x471cef533bf1c51511354caec72b9450dc4db91c0dbf035146ebee2d3b6c52db134cb50b2cfaca46b28f3cb44ba4da8b30b2cd2e93292545264e89945094d39914493e72514663cf84d94912524d3615e110b2c92a424b2cc28a7d450579e15451f79e7114456db15145c6db15714434d1178cc2cb1586052cb31860486214924586110925f51481e7a05147de79c45175b6dd45171b6d75da04d68c2cb6586192cb1186041071092575d71c45811560945154d35545024d34114523cf4914503cf1c438234d30b2c428a30b2c428a1042022481c41821451040c2040⟩,
  ⟨56,7,[ew217,ew219,ew243,ew257,ew267,ew269,ew270],localHints 6 0x1b05e02c160100381202383409409c0e82609a0fc290060a00142783300e0381a8020440840482b0020501480003c04c1e00802a0580781706400c0c0040400441680a 0x42ec2c4f0b2eb904d0313bebbafad34ccb8cad0b4cb2d31042bb2b220aa84eaa208084d3a1ea4842921e7a841025a9c832721a68930c1939a58269534c68061909157a455040678604c8c66a318c19c69a5488860461881950556608214d38608194d375e79f4107de79d41071a6d731b5da69630c1416192180461975555c619655501350f4943d34c04923d044039101040f38e2cc34028d00c30b28a0090022080890802000861c0047006182142003102144083080040⟩,
  ⟨56,7,[ew140,ew217,ew243,ew253,ew257,ew269,ew270],localHints 6 0x6c0800b5d2ba02b8560720085e08900c2c40284609a0f42f85c06210937a7009c0c80a00105e04c0e000058ef83a82501e058070070660640180802a06008804 0x42cbad52eb6cb10510ae38cb5142e38eb514aa184b4102e186a410263a675299e38c95149e1a094282618674100829892e61549648e59145058c515089e86279040584578b78580514b15e81e78a7c525f14a15e25e05451b55d6d45015556d040149c05041b49208b68108104b0590980c95c129704924328a0455830960c51410811155515144554c45134524844101123d140f10b10c38d30b2c408410a1022491ca2042481c71841450830c4044103002040⟩
]

def nodesBlock19 : Array Node := #[
  ⟨56,8,[ew140,ew217,ew243,ew257,ew267,ew269,ew270],localHints 6 0x1b0ae02c2b0100720a80f828080ba80782703a0181300509a0b8060090be1701884e076b64191930a40500094d0a004ca604f0000880b00e00eefc128170040340c8fb06a00c1f02002a06008804 0x213db8574678634db6213653210677733db7733659210d905734f5610d356104d3573d3320bab2731672731aaa20b64b54ba306254f0625a2854b4cb0ad42f08b08b08b40b0adbad20666c72baac72b659206a865464e9624a296244d3546a061424670864271464460824101642e62869661462cb2a49642016597216a372165920169a5614d36015a26014d35615960834200814601414101434510822cb08131f0812cb09e30c08119d14309d14318608108120769a71b65971b69a2076595545966174d36175965544d314245108241015244f08440f14e30c08d2cb14d30c0822cb14a0892071861420c30840411440c0082040⟩,
  ⟨56,8,[ew197,ew213,ew217,ew243,ew257,ew267,ew269,ew270],localHints 6 0x361780585b020114240470681281381d04c1500903f0ee10807aec46e05175a360260201082d032028688060023280288b0000900b04c02e0080180903008c0a83e04a1c856835 0x3f1cef4f3bf1c4f4cf353caec72b934cdc4db8fc0dbf034f3eebee2d4b6b4edad450b4d3ad1b0b3ec2d146b3cf84da8b32a2cd361661253a68529a134c950924f9c846720f3c944994d98910924d26512520b90910924b2481087d34c579e1534df79e70f3c56db14f3dc6db15914434d1198cc86214b2c586130b2c42491575c52491175df4d381e7a04d37de79c3cf75b6dd3cf71b6d965a04d68c10710b2d96591092585d76092445d71c45811560945154d35545024d34114523cf4914503cf1c438234d3042822ca1092442081092442081c41821451040c2040⟩,
  ⟨56,7,[ew190,ew217,ew243,ew257,ew267,ew269,ew270],localHints 6 0x6c1780b0580400e02a03e0a0258630c40dc2a03f0560501481e0260f00a8160600482900100c1400004f00a0b4038250100e0070220040840603503200c0c00404002819811 0x570cae632bb0c156153d8c6dc31b5860fc0fb55bcfbaf3d556dbad2d7b2b62cad75cb60b2d3a8956a2534cb54b04da4b3e92cd2d23cf1d86265e89986075d79955474e71d55664d368f3c73651cf3da34d04b2c72641cb2c12490988e08a38186028a28158427e10955607df74f78271e08f3dd71c08b6c005b00b2c214201a0021c209a0801c02186195d76586085d75155564d35955544d348f45035140f3ce34d04b2cc24930b2ca2491411881c61421030040c2081000⟩,
  ⟨56,7,[ew149,ew217,ew239,ew243,ew257,ew269,ew270],localHints 6 0x6c0800b1982445eaee5da1f8178060580700284b08000c1582903c0c02210d4cc0f00a0010ae04c1c8000ac05c012610ec0880902d02c0200380e02a06005004 0x42cbad52eb6cb10510364aea52baa490d50d361a5f4297e184d40da145099242545289249d040986125042786160d3497df24d3667df1949629258945069248908c686319042286118d8077e01cd3467df08278625e05475b55d6d45015556d070149c05041b49204d68309a0cd3410810896410810490580970c65811d60461831c71155515144554c45134524844101123d140f20838434d10910a30b2892440841071021862071441850830c4044103002040⟩,
  ⟨56,8,[ew149,ew217,ew243,ew257,ew267,ew269,ew270],localHints 6 0xd82f0160b00801c05407c1404b04e0740302600a0f57781221a0b8060090560a40f03c0600e9611940a40500094f0a004ca704f0000940b00800e0900b8fc06a009e002203200c2602002a06005004 0x313df9575679635df7313653310678734df8734659310dd05744f6610d766104d3574d7430ab73732673732b6d30a64a54aaf16254f1625aeb54a4ca14247008a43014a44a08241030666f72eb6f72e659306b465464ec624aec6244d3546ac60a842a0860860864060a8a689e42a614696614628a3a49643016637216a372165930169a5614e26015a26014d356159608342008146014141014345108129f14309f14328a0810810821860811de08118609d1c730b69a71b65971b69a30b6595545966174d36175965544d314245108241015244f08440f14e08d30b28a1491c70881861481c70821861420c30840411440c0082040⟩,
  ⟨56,7,[ew213,ew217,ew223,ew243,ew257,ew269,ew270],localHints 6 0x360400582a05007c1380604c0740285e0b611401023006bc5780420fc858220464281dc178010280b00001c0261000600f07a0240900e00e0800b0210340200a804 0x46dbee52fbadb51511368b2a52caa8a0d514aa5acd46b36596a451294a66a2999450aa289919ca96729146696528c28934d24c30a34a1539225248934c551488f8c546314f3e24510c48453618047c529f7945014d305451e4d37514413cf05145d3cf10d34111c04d35b11a10a28111904a2981170460441451065811450945504d54145024d34114823d20914503cf08d38830e20d20230220a2c224b08a0882480861c4147106182142103002040⟩,
  ⟨56,7,[ew213,ew217,ew230,ew239,ew257,ew269,ew270],localHints 6 0x6c0800b0540a00f85e00c16c2280512e280010035e6bc91907708874806a0b0ae0040a0560000e4098400181f81f21504401c048160860603b0120340380a804 0x4ecbad5aeb6cb135933e7ae95aba679cf596a64a8f4ea3e49294d3216a259e89565889e79539889262134e59242432483c82032093c98d55445961155635968914444d31114624d334d8443e11088062601882042497d658155505659f5557934c14510534de45164f3c164104f3ce65d0492432083497012086446c165b04411a6580965d25574965825554935024540934d245138f40235008f08e34c08928b20a0c92422020860871041c61421020c3002040⟩,
  ⟨56,7,[ew213,ew217,ew230,ew243,ew253,ew269,ew270],localHints 6 0x6c0800b0bc16c2282700c0980e805130284010035eabd03ba2e0847490602f0020501600003804c128070460300b03d012118262100860603a80f0340200a804 0x52cbad5eeb6cb145d4367ae95eba679cd5d7a64a8d52a3649295142d7a259e89575cb9e795498b9262d45259242cd34f38e3cd34b38b8d65845d71165a35d78924845141124a251410d8463a118d34438e2498042e07d75c15960575df59679450149205451e49204e38f34d24e74134d28b2c128104b2ca29c2846c129b04411a2990976135984d75c25964d454249509451349208e4113503ce38234228b30224c08b08a2480860871041c61421020c3002040⟩,
  ⟨56,8,[ew213,ew217,ew230,ew243,ew257,ew267,ew269,ew270],localHints 6 0xd85e01616c080450540a00fa7904e0181301d00a9e0688ca1168e001072006bdd7b0774e49a0102262260040a0fe0003f40987a02c01c1280c0488c01100901a131150430307481f1e90343100a804 0x5f7e756b9d77dd76974dae34df8d1a693dd3d17d93d764d75f4d7442ecf16b3c6eb9069ac6bc905f242baf15d75134d05104134d43f031abecbafb1a68cbaeb17b4caed3175ecaeb5134cc50c3134d42ea30530a4102852e4659a5a6a965991a6a7555a175e85559d75d44d31d41c74d350698516591094a2a390c8e269a05964169a8996615d70555415d78555412c10d34c51602d04012c105040f2df2cc3012c104c30b2de2dd1c12c105d0462dc09a69b6596da6826595975d85556175d655550b4824d23d041114f45040f14e2cc30d28b34c30b2891871c81482071c61440c3002040⟩,
  ⟨56,7,[ew127,ew213,ew217,ew243,ew257,ew269,ew270],localHints 6 0x36040058e01323581382603a0b97caf80fc11086a6705e0501601c02612c2503d0080180085e00a1140005b018008090090069803b82002a0680c02101c05804007 0x46dbee56fbadb51551396b2b56cad658e54e393a9946a6534ce44e315a675a99d554c5969d1a0c4e83114674d330e98d1a634e38c18c95554779e1d556579e9114476db1d14646db84e3876591ce3a365918c3071a21cc3068600557dc79f71554179e7117416dd05145c6db04e68365a0ce3816590cc60135804c0433431865c11d70965925554965025544934c24510934124501043c238e14d34230208d2c530b0870882892071c21820830c5041103002040⟩,
  ⟨56,8,[ew213,ew217,ew239,ew243,ew257,ew269,ew270],localHints 6 0x6c0800b05407c142780bc0182d84500abe82523801800d398444d21dc2b9950020502b1500002801c8135de1000123102e1d80902007c0880380d0700580c01a12e0380a804 0xd7c325b16f2631c300d76d70d1aaf72e6ef72eaaa0d16d15919ed6235ed6239e75915d10c36db70daaa70d6db0c3aaa5965d760d9e760d5d75969e72c845120d8e32cd45122c8e30c66eb728aab7286db0c6aaa5a85e96069e96065d75a89e71264511c68e51064511e48e31451620c63620c36db70169a7016db0c369a5965d76015146015d75965141c84512013cf1c14512213cf1c83602c12201c134d20821f1c13011c41861cb31e1c11860c26dd71569d7156db0c269a5955d96025196025d75955141534512c23d21424512d03cf2c21422ca34d1ca1ce1c23421c23092ca1891441481c21821441000c2040⟩,
  ⟨56,7,[ew106,ew213,ew217,ew243,ew257,ew269,ew270],localHints 6 0x1b02002c1502803e5d05d11b05cbf17d8424e2118178140580700984009a1500d0040020182f00008a0142d80f01800810809006f043b82002a08c0c03801005807007 0x52ec2f5f0beeb945d43d6b6b5edad658f5d7ad2b0f52c3d24ab5142d7aa95aaa575cb58b2d4a1a4a869450b48b1909cb3e72d02c63cf9975c78201d75e682095450775d1d452575d18f3c71a41cf3c68a388b2c769a1cb2e269a0d785e8217975c38207947c375f0d451e75d0cf70141c04f04340304b6c369b0cb2c169a6596031d80975d35964d75425954d45024920944534911504023c20903853ce34d3022cb0870882892071c21820830c5041103002040⟩,
  ⟨56,8,[ew213,ew217,ew243,ew253,ew257,ew269,ew270],localHints 6 0x1b02002c2f05b08a0081381d00c09802a790a8bf51c0090849d03b82408c9a817996002050161510002840e0130ea03c1002500e034108165d40f40184c4560640c0231300200a804 0xd7cb45b36f4633cb20d76d70c3aeb7126db712aeb0c36db596a696125d7612a695965d70ccaf172f6f172faeb0cc6db5afa7060c5f060ca695af5d714516e0cc4ae0c96ed72caed72c6db0c9ac95895ea624a6a6245d7589a497e44a4209809209489824a243643271099891093093649640c36db70169a7016db0c369a5965d76015146015d75965143604a320182334149282082234144134430c34846134130c3602497c11863412497de1860c26dd71569d7156db0c269a5955d96025196025d759551420214221049235035334248234244f21030f14414e34230214b24920218a1422492071861441000c2040⟩,
  ⟨56,9,[ew213,ew217,ew243,ew257,ew267,ew269,ew270],localHints 6 0x6c2f00b0b60402282a03e0a02530001e09c0e80604c0142a2ff0240b97f00c0121dd72ae059eb28688520020506505000022c2781302c01de2824004f113b81778603401bc24dc0640c0530e40d40a804 0xd7e3a5b66fa676e380d76d70d36f9775e397756db0d3e135b55f7653db76535d75b5db50cfb347736f4773b2c0cf6cf58fab26645f2664aaa58f5cf12f4f114f10f14f4cf12fc2f0c96ee76db2e76d6db0c9b095895eb663aab6635d7589a891274e91491091494c9127a272a33e64099262893cf9639230c36db74169a7416db0c369a5965d76415146415d75965141412811444d31441221613cf40130c1413cf42030c15f24928118614124929e1860c26db75c69a75c6db0c269a5955d76585146585d75955141442920c24d21513cf41030c1503cf38d30c14b24928a18614a2492071861441000c2040⟩,
  ⟨56,9,[ew151,ew217,ew243,ew257,ew267,ew269,ew270],localHints 6 0x1b05e0700582c0200a80f82809603c0402703a0181300509a0480702e018024289970a4050009520a004c7f84f0000600b00704805c0101901a00c100531a40d40a804 0xcfb7046b57052bb6d0cf54f0cc56f62eb6f62e5550ccb4c44c3ec525aec5253cf44cacc0c98aa62956a6298a20c954944982851b3e851b8204493c912632738996738930c1269650c65646238a46235550c68864463e151a82151a3cf44680611e31f38675f38630c11e75d1da25c1c66dc1c62491da6da0c35556015966015550c35964513cf5014925013cf45149238411914430c3811c11472491c128a1412491cb28a1471861c12081411861c72080c25966175556175960c25554504925133cf5134924503cf3841cd0c230c1cb28a1472491cb28a1472491c72081471861c72081471861441000c2040⟩,
  ⟨56,7,[ew121,ew217,ew243,ew257,ew267,ew269,ew270],localHints 6 0x6c1780b0580400e02a05007c2000f04e0181301d00a0f40900e07ec09808510601f8190460a40040a05000013c0980807c0580380c03405c0102001208c0c8030420281a804 0x4f0cae5b2bb0c13593416c6dc31b56590c10b53bd0baf4134edbad326b2a5acaa698c596aa3acc4eb3238ea4d3a20a4c4293208284101d69e49a79165879a69139478e51d34e48e38508878221d04218201ca7c531f14a28730701659e5557965805400134dd4517534c04400d070039c01000f38e0cc6c029b00c01a28a0c76401590070181450565975555d65815554934d44515134d24510d040838e21034f38d0cc30828a20c24b2890c71c81452071061440c3081000⟩
]

def nodesBlock20 : Array Node := #[
  ⟨56,8,[ew217,ew223,ew243,ew257,ew267,ew269,ew270],localHints 6 0x6c1780b0580400e02a05007c2002700c0980e80507a0e00701201e1482804f00e008118350060accc01e0022b80a0292a8000a98130780680407a4700541d8330181f91983a05a10c0484645e045e3020008084f480a 0x79af3e67a7fe6faf3c79a7da7957fd879f3d8797df795f156796bb6d5ebb6d569a679eb978fcf88767f8876cf378f7df676c376cf6b76cfc3067669a42bb7558f57508fb6d0ab5557897f4871cf48717df789cf36716b26c9c326c969a671c302ec56f589b6f2c9555bacb6d2c9ac942c3cf2ecaeb5093c97a475d86a7df86a75d7a47df6686186e969a6e961866869a5142a77a45674165a67a43e62e59637a42637837e28607628607df78374364369c6c061c6c069a6436030925575835030835435124d20803d14032830833c338034008624c2c32830832432061c6080100083143083103080040⟩,
  ⟨56,7,[ew209,ew230,ew267,ew269,ew270],localHints 6 0x1b05e0700582c0202283888709610c078081027ec348013ba050401f30007c80985103401c0a8163d4f1c360040040341f83a 0x4cf86439f52441f8614cf50f4ca5235a28635a25144ca84a38a3e04187e04183cf38a7ca4c349e59d51e59d4924c350338335c4013dc40134d3833c369929b2c361b2c328a6996184c45175954975955144c44843843d14003514003cf38434408928c2c420c2c428a0892081c00c51840450840c3080040⟩,
  ⟨56,7,[ew217,ew230,ew262,ew269,ew270],localHints 6 0x362f04480b1620402403408ef20ef0430820f4158d303c00454814052318000c50261440d00702a058180040040340b80a 0x44d82331e4a339e82044d48d4484a252182252149244880830835f39679f39634d30878844341d51c49d51c4104434833032db38135b3812cb30334369721924359924320861759644449551341551349244440430434f3802cf38034d3042c408720a24418a2442080871860800c50840450840c3080040⟩,
  ⟨56,7,[ew217,ew230,ew262,ew267,ew269,ew270],localHints 6 0x3609c0582603a040110070900d0238432220b82082b1a6078008a90280a46300018a04c1d009034054180040040340b80a 0x40c8632de46335e86140c44c4104514d38614d34514108612cb30c34d79e34d30c2cb79e4084624df8624df4514088612df3203487a034830c2df79e75d75c40841c4033db4da45b4da3cf4034432c329934131934128a2c33031d56151c31c31c31c31d56151d55d61c32161c31c31d52084044544d23d44d24514043c42c430e34028e34030c2c42841c60861c41c41c41c41c60861c62091c41c41c42041c60860800c50840450840c3080040⟩,
  ⟨56,8,[ew217,ew230,ew263,ew267,ew269,ew270],localHints 6 0x6c1781c0160b00802704c0741eb056081201a04709610c078082220b8159df03c004aa81405270c001c20261440d00702a0581d022012c0c180040040340b80a 0x551aee4295ae4a9aeb55159154c5ad62caed62c59654cacc40c46a49ca6a49c45140ca4c5475a86260a86265965470874264674870a74874514260a620230c3470a520730c3640a35435226215a26215145435834033e04814604813cf40344379d31f34371f34330c79d71c6db6da5431da5445996175196175965445044044534803d34804514043c408b30e34428e34430c08b28a0821c92040842041c40820860800c50840450840c3080040⟩,
  ⟨56,6,[ew118,ew217,ew230,ew253,ew269,ew270],localHints 6 0x36040058cc17a2443186206e008f89d90286ec098510641fc03001178014448001620682604002c01d5a87505a1040c8030660441e804 0x4259e65279a595051031592252489554c5148928cc4233124a241015b85f5147db6c55147d980541015965f41018b78531e14b2c630c01475c6dd7145006c001069665a59040064058c6002d800c0162d65865c01570060161560555515144554c15134524814100523d140f04c04e2cb34c2812ca0460491481c61011440c3081000⟩,
  ⟨56,7,[ew118,ew217,ew230,ew257,ew267,ew269,ew270],localHints 6 0x1b0ae02c2b0100720a81401f0801f93d0630c40dc2a0021021a40a0800261442600d0640e80300104e0140e80004c0381101600e0940601a0480480c80306604404804 0x42ec2c530b2eb90510394bebbafad450eb8ead0b4eb2d39042bb2b255aa852aa15549514a12a494292524a841020e9c922724e3889a515d92251489d74551489b8c541015b6e241018c8453a114c30638e2088052600147de75f7945007400107166dc5904006c020e68031a00e01930c5895806000090166165865c01570060161560555515144554c15134524814100523d140f20e38130c04e2cd30b04904a20a2892412010460481451c61011440c3081000⟩,
  ⟨56,6,[ew100,ew217,ew230,ew239,ew269,ew270],localHints 6 0x36040058bc1622242404706800cf69f80286c409851060208008061980004880517a0681f03d02c01d308760661040b80205a02820004 0x4a59e65679a595255231592252489554c5148928cc4233124a241015b85f5617db6c55557d98054a015965f49218b78531e14b2c630c01575c6dd7155406c001269665a59248064058c6002d800c0162d65865c01570060161560555515144554c15134524814100523d140f04c30e2cb34c2812ca0460491481c61011440c3081000⟩,
  ⟨56,7,[ew217,ew230,ew239,ew253,ew269,ew270],localHints 6 0x36040058cc17a2445e0061622240280701a268510220041d8128180061d4159e003c004cc814052714001c40262093d8230800b50a87f4f40681e8334200442304100810d0680a 0x655c735326b35b2c7165569564fb3072e6b072eb2c64f69a52ea6f58f56f58fa6952e5556496ad72ab2d72a69a649b2c52a56b589a6b58955552aa693899282213e82902a73893c966661870469a70461866669a5254d35845555844d35255553849232a03e32082223843cf20485f2a025f38e39e38424964369d71b61d71b69a6436035035575804d75805555034c33803d24034434033c338034020624c2832c32832432061c6140100083083143103080040⟩,
  ⟨56,8,[ew217,ew230,ew239,ew257,ew267,ew269,ew270],localHints 6 0x3615c058560200e41502803e10011a7c04e0181301d00a01c120731181d80102503000c2982b334078008ee0280a4ab8002ac04c2700e0f49e00a83b0181f93a83a60c068048334540440681200810d1380a 0x718e7b5f777b677e7971875871477a7f6e7a7f675d714e545f6638654df86546185f6df670fbb57f37757f3bae70f75d5f3af464f63464faeb5f361821353228f4f220f514c530b070976f7ecbaf7ec75d709bae5ec62d649aed6496185ecaeb29316a70952a2092892243cf2242a92093c97286db7c475d7c46db72875d5e75966446186445965e76184c40842a351420822620451428a2a57043e52049222a326228a4e12042497037607de6e07de75d7036c35c361a64059a6406185c35834d15152834c32835034d14911403d02030832033c338034020624c2832c32832432061c6140100083083143103080040⟩,
  ⟨56,7,[ew100,ew217,ew230,ew243,ew267,ew269,ew270],localHints 6 0x360bc0582c0200701382603a0f53d84808e0d02500310c1bc0a0850261441f0460600ec008060540000f8050500201281600e0880482301a03c0b80205a02806004 0x4adbeb56faedb52552395baab6ea9554eb4ea92b0eaec3924aaaea255a675299d55495149d2a094282524a741020e98922624e38862515d92256489d74555589b8c54a315b6e249218c8453a114c30638e2088052600157de75f7955407400127166dc5924806c020e68031a00e01930c5895806000090166165865c01570060161560555515144554c15134524814100523d140f20e38130c04e2cd30b04924a20a2892412010460481451c61011440c3081000⟩,
  ⟨56,8,[ew217,ew230,ew243,ew253,ew267,ew269,ew270],localHints 6 0x360bc0582c0200701502803e0900382700c0980e80507a9f00687411a1d41101800414c0182b336078008ef0280a4ac8002b004c1e01a0101e93c815076c1c1180c4600e8168094d60442300f00810d1400a 0x718e7b5f777b677e7971875871377a7f6e7a7f675d713e535f6638653df86536185f6df670cbf57f37757f3bef70c75d5f3b3464c63464cb2c5f3618352cb170c4f17087707edbf07ed75d708bef5ed62e648b2e6486185edb2c2524eb5084ab2484d35120aa24894824d30c24d9692483087286db7c475d7c46db72875d5e75966446186445965e76184840845244d32492662444d324496352432334d4a224430c34d3617042217037607de6e07de75d7036c35c361a64059a6406185c35834904d55034835034c349045024030f3433833433032402c014620a2430832432031461c6140100083083143103080040⟩,
  ⟨56,9,[ew217,ew230,ew243,ew257,ew267,ew269,ew270],localHints 6 0x6c1781c0160b00802a05007c2030a04e0181301d00a0f58480e6101482804f0a69f40400206a00c1591303c004620140523f8000fd0261443d0075fc0540b03b0180917083a012b2c0880d00810d3680a 0x655dfa5356ba5b5df76556956506b9738df973869a650dd05105765a1d765a1555510d5064bbb47326b4732bae64b69a532af358b57358baeb53255528241044b87144b4100b08616476af72cbaf72c69a647bae52c56d587aed58755552caeb102410447a2a4474100a9a2810710728a2cb10a12765f61872669a72661865f69a5244d35a55555a54d35245550824104638614634100a286110412065f2e028a29e65f1de64369d71b61d71b69a6436035035575804d75805555034c310e4124433524434103ce34d1002cc2830831032c32802401051c81030831031c3105185100100083083103103080040⟩,
  ⟨56,8,[ew209,ew243,ew257,ew267,ew269,ew270],localHints 6 0x1b05e0700582c0201201a04709608c078080c60dc0306200a1340900e048c0c159e103c004ce01405271c001c60261440d00702a0588803004a0080b80a21c0c8110040060340c811 0x655c7452f6b45afc716556956506b3732c7373269a650c505105705a8bf05a8555510bd064a96e72d6ae72d96564a68a50a8ec58956c5898e350a54a2e942b44aa2b2ca410aa9a2864369a72696772669a6439435035555818e45815555038c316142244382214341046182014228a2c308314328a09f09e64469d71b61d71b69a6446045045575884d75885555044c408f41244439244441008f38e34828c2c424c2c428a0882481c00c61440461440c3080040⟩,
  ⟨56,8,[ew150,ew243,ew257,ew267,ew269,ew270],localHints 6 0xd82f03802c1601010c1bc4284b04603c040810d20184000509a0680900e0d80ec1d1e203c050ce801056724099c80000a40c01602a01c2882502e0280103001a0880201904004401832 0x653cb55306355b0cb265361364e634733cb473361864ec8e50e4f15a9c315a94d350ec0e6499af72e62f72e9a664960950992d59e4ed59e9245094c932a3ac449a6c30938eaeaa696416287279a87276186419815014e559d92559d4d35019011a13a344182318138e8a182019d25f30179f1812491dd79d64568571b61871b69764561750554558a4d358a5525054d244f4100c538e44540d0cf38d1ca2ca0c52493052c80ca2481c21020c50411851000c2040⟩,
  ⟨56,8,[ew217,ew243,ew257,ew262,ew269,ew270],localHints 6 0x6c1781c0160b00804806811c2582301e0203183700c1880284d024038123040562d00f00113a050148ab0002a80985103401c0a816060094010170140c8110040060340c811 0x5d3bf24ad63252dbef5d36135ce6316b0bf16b06185cebce48e4ee526b6e5264d348eb4e5c98ec6ab62c6ab8e35c960948986a5084ea5088614894c92a73a93c99a928938ea279a65c36186a48e56a46185c38c34834d35018625014d348384315f3a03c37a014338e3df79e14224928308314324909d09c5c461b69959b6996185c45844844d55074555074d348444408d3903c43103c438e08d30c08724b28420b2842490872070800c61440461440c3080040⟩
]

def nodesBlock21 : Array Node := #[
  ⟨56,8,[ew217,ew243,ew257,ew262,ew267,ew269,ew270],localHints 6 0x1b0a402c2804f0200d40384806811c0600f0c60dc0306200a0240c01260a0ac5a01e0022740a029156000550130400340a83004a008118170140c8110040060680c811 0x592bb046b5f04ebbae5925d25965d7659bae6595d7596bae4514924d3aeb4d3492451aeb5aa5d766fbae66f5d75aabae46c4924edaeb4ed49246caeb1451695aa5a958a8686675e866786158a5ca44a7e64c84a64c87df44a48a2e42e408a08a2ca2ca0a42642e42e508a74a2ca2ca0a42645835d76628636625d75838434434924c17e04c14924437c315c15c08308314314309c09c15c15e08374314314309c09c14228a2c308314328a08909b5845da65855a6585d75845444444944c74144c749244440408d38d08408408408408d38d08d3cd0840840843c408d38d24728c2c420c2c428a2472070800c61440461440c3080040⟩,
  ⟨56,9,[ew217,ew243,ew257,ew263,ew267,ew269,ew270],localHints 6 0xd82f03802c160100a414027853798f2c2403408e12c1180f0100303183700c1880284d02403804835048c201599e03c0047801405256c0015a0261440d00702a059e53c9060094010170140c8110040060340c811 0x655ebd5386bd5b8eba6556956506bc73bebc73b69a650e905105795abe395ab555510e1066069a7370b773769a6600a05355555b60b65b65555350b51424104740b41744104730b26499f17306b17309e764968950996f58856f5889655095492ac42e449aee289410b6caeb2827ea64980964369a7289e972869a6439c35035555819665815555039431634244438a41434104638a21420a164380314224928308309f09e64469d71b61d71b69a6446045045575874d75875555044c408f41244439244441008f38e08208d14408414408408208c08724b28420b2842490872070800c61440461440c3080040⟩,
  ⟨56,8,[ew217,ew243,ew257,ew258,ew267,ew269,ew270],localHints 6 0xd82f0160b00801c0a41402783500e0a81401f0ea0600106306e0183100507a088090430120b80782b33e078009000280a4ae8002b804c1e01a0100541003b04a030118240140c8168040061180c811 0x614df94f5679575df761465460f6786f4df86f465960fdcf4f453654fd7654f5144f4d746309a66f36596f39a66306594f19245725145729244f15142cb2ef6303ef60a9ae6ec66e6ec9a660a6594ec92d54a52d54a9244ec5142dd2dd40a3cf2ca2eb15d3cf2dd8a940aaa92ca2ca15d25d6036596e79a86e76596039834c35145419255415144c39031613e34032431433c34218211618a114324314388316181f14975e2c329e2c374324928a60465c6da5dc6da6596045c44c45165474965475144c448424e3d14042444043c424e20e14734724424424434414720724728c2c42442c42842472070800c61440461440c3080040⟩,
  ⟨56,8,[ew102,ew217,ew243,ew253,ew267,ew269,ew270],localHints 6 0x6c1780b0580400e02a05007c0386306e188170220820ac0f01405204c1e0150760c8230190226800087400c57c0015e11a014168210ea0600401a018008218091b600c1200f01409411804 0x1d5d365326765b2d341d56551cd6756b1d356b16591cdd0d53157358dcb358d555531cb11cb5f06ae6706ae5d71cb65952e4af58b56f58b49252e5550820ad1cb36d1c66596ab5ec6ab6591c65c650655559c4aa59c55550648646734d306046446346327267467a294462e9446a064672cb1c06666a59266a56591c09005005635838a35835555008800603613000403003400601604432df0400400402c044314375b19e44071e44018675b71b1d86596845d76846591d85d751355558449258455551349244434d09008f30e34d08408430c30a1c42ca0490481c41860450c30840000440c3081000⟩,
  ⟨56,9,[ew102,ew217,ew243,ew257,ew267,ew269,ew270],localHints 6 0xd82f03802c160100540a00f84061618c1b86209a0480711105c0ac0f01405204c2881502c0ec190190226842900100c584280002c013c02bcd04614c04007018008218091e20d40180d01409412004 0x1d4db94f46395b4db61d46141cc6386b7db86b76181ccd8c4cc53558dd3558d5144ccd0c1cb5f36b16336b15d71cb6184f147258b53258b4514f151408130c3cb37008b30c3ef34d1c56186ad5ee6ad6181c55c54c551459c46c59c5144c544512a32b3c5a6b3c530c26aa69a28a270851050412cb1c06266a59266a56181c09004c05235838a35835144c08801203213c07e13c030c0607df1032de0800400802c004304311b15d10071d10014511b71b1c66186995d76996181c65d74d25145954515955144d24513d034d08e30c3ce34d08130c08410a1c62ca0490481c61450410c30840001040c3081000⟩,
  ⟨56,8,[ew217,ew243,ew244,ew257,ew267,ew269,ew270],localHints 6 0x3615c058560200e42403408e1002905009e0d40382508603c0602700c0980e8050ec0b80c0030240acd101e0024040a0292c6000b101309c0380a83000405c050200660e81100900806806811 0x592d774735f74f3d755925d258e5f6672d766725d758ed4e4724b44cecf44ce492472cf258b8f16705f16708e358b5cb44b82f4ca4af4ca82044b48b1e63ae08b08b1cb38b0a69e65aa5d766d8e366d5d75aa8e346b4924ec8204ec49246b8201451695aa3a91c22cb1e89a61e82cb1e79a55845e46618e46615d75848e34614a24c48224c449246182015b15b08438e14415f1db38e1442de1db09e15b2cb08408415b15c08475c1441441db09b5835da65855a6585d75835434434944c94144c949244340308d38f08308308338308d04d0492cc1c328c1c32cb0492891c02000830830832031c0040080106143083143103080040⟩,
  ⟨56,8,[ew123,ew217,ew239,ew257,ew267,ew269,ew270],localHints 6 0x1b0ae02c2b0100721201a04704e0980e80705c0942082b03c0501481309c054180170140e8d18060e6004b28052c8230000330701d80c00e086030010dc01200c068120220880d004 0x211cb44f05b4570cb221159120c5b366fcb366f59620cc8c4ef47154cc3154c4514efc2f20962e66d5ae66d6182095894c952c55c46c55c5144c944942530c0490494093090652e52075ab66962b6695962076184e946a54752a5474514e95140820a82073284072674269674262494079472005a46638a46635962008804c046155b82155b4514c080005e31f04004004030005e15e15b25d40071d40024915b71b4031da0400400401c04031432176186445966446182175964d25145444515445144d245140430c08f08e04d30c08408404b04a2042490410462041c60450c30840000440c3081000⟩,
  ⟨56,9,[ew123,ew217,ew243,ew257,ew267,ew269,ew270],localHints 6 0xd82f03802c160100900d02382409603c0402704c0741eb0c2220b81581e0280a40985102a058180170140e8d205200c004b385000a5982780079c0682980e00e10c060021e40d40480302208806804 0x1d0db94b45b9574db61d05901cb5b8677db86775961cbd8b48b43556dd3556d41048bd0b1c85f36725b36725d71c85884884f155c43155c4d3488408c2e2ef388b6f3882cb2aeb6d1c55ac66a5ec66a5961c55d74aa42b5454eb5454104aa4d30812cb3853290852cb3a830c9e79e60812080450451c05a56648e56645961c08c048042255b86255b41048084005f2e03807a03802cb05f79e05b21d04071d04020805b71b04315a0800400801400430431c65d76585966585d71c65964914d35544105544d349141038f30c08d2cb38d30c0812cb04a0491c62080810441c61440410c30810000410c3081000⟩,
  ⟨56,8,[ew181,ew217,ew239,ew243,ew257,ew267,ew269,ew270],localHints 6 0x6c2b80b0ac0401c82a03e0a02000f0ecc391d30d4720580c85f0281701881309c0ec0b84402a0f86800100c3240008c00a0680680e06600806018024080560350701cc08804 0x470cae532bb0c11511314c6dc31b5450cc0cb51bccbaf31146dbad293b2b52cad34ca50a28fa8946a24f3ca44aa0ca4a2ca28c2a82e89545074d31d45254d38d14473cf1d14633cf1c31c330c0c39cb28a1c924728a2c92655149934e65149534e345190f3e44518cf3d60e214c30b28a0c924b28a0c92480e114784151475f81d51405f7dd45105c78145175c71731b0436c130c5c35c328a05968128a2d96411c15c36171c70430410c10c33830d60945154d35545024d34114523cf4914503cf38334230c2ca2832492ca2832492032021c70c31821440c3002040⟩,
  ⟨56,7,[ew217,ew243,ew245,ew257,ew267,ew269,ew270],localHints 6 0x6c1780b0580400e02a05007c200520a013c0383500409c0302603a0141e81201c03c0182b03c0040a02900004c288080980581d80c040028108320120100d019 0x3ecbaa4aeaacb0f48f312b69b2da5248cb0ca4faccaab30f3e9aa921da264a899d74849299a9c83e721a6a63cf5979483252175d630c81146449291146049288e3a33cf8ce3a23cf2ca8473211ca28530c0457e021f0d279b75e6d248375d6cf70369c0cf3db69a60c6435d90cc3185d70d60c02080160032030c75400550070031430925134544d248244208f40639018f3c238214c34228d08c08b28a188242142088086146187182142087086146143102004083081000⟩,
  ⟨56,7,[ew118,ew217,ew243,ew253,ew257,ew269,ew270],localHints 6 0x1b02002d8830f0ae1581c8020c61881b8410fc9e82a0bb1100505801308c1441e03200c00417805038000162b10ea0940784c01c0580381a0240600c80306604404004 0x4aec2f5b0beeb92592b575cd5963575ed596b1450d49235452c4922d7ae95aba575cb596a54a8b4aa2d4529492186a0b3681565a55e79565855d79524855261524a551420d90520514d1632221ca8452e114a2872cb01681f7a07d658078001275971d65248070064d6406c000d0196d964b68029a00b0192992076001580070081450575d35964d75415954d450149205445349104d04e40f38d34120104b04828a30b2412892071c11410471061440c3081000⟩,
  ⟨56,8,[ew118,ew217,ew243,ew257,ew267,ew269,ew270],localHints 6 0xd8570161580803905407c1404062203c3186206e1501fb060560780a029026144180170140c8d285200c004b485000a5a02780001c05803bcf04a030010220400480c0190060e00681a0224081a804 0x94df95b56b9675df70946940936b8774df877469a093dd35b4536653d766535145b4d7408d6f37726b37726db08d68d58d5f164e53164e5d758d50d12e4f024d10d24d4cd12ebee08869a76b6ed76b69a0886db5ab5146485ec6485145ab5d710a4aa2484ea18849218a4d310434d1083a910834d12838e0806a776696776669a08094058052465f8e465f5145808c01844e22404a21804c024449219f36114082118034d15f81f18429e10021e1802801042080816db75c69a75c6db08169a5955d76585146585d75955141844d324949218b4d110c49119038e10f34d18f38e10434d18428a10c20818b287249207185103081000⟩,
  ⟨56,8,[ew217,ew223,ew239,ew243,ew257,ew267,ew269,ew270],localHints 6 0x3615c058560200e41502803e1003b04101ec4d1e0066248ec0280805a024680c911810c1980203408c1287315c0d41581e0020501480002613807015076030090210220101c00a 0x331cef3f3bf1c4c3cc24fcaec72b8f3c9c49b8cc09bf024c32ebee1a4b6b3edae49063cfae1b0632c1a186b30c9c9a8666a1892677e794f3c592414f3e592488c30586114c32286115f14124905fa599e81461859e76461a53cf9a49263cf96492230c8e186330c8a185f7e04c981905704619f7df5c179315e50e39d3cf74e3943cf6cb2dc30c70b2db30c5c16942496416141985c15941450415544d208f45039140f3c238208c3402cd00c3022c22092820420890880480061c20420860800400c50c20420850830430c40c2042084083043001002042081080040⟩,
  ⟨56,7,[ew189,ew217,ew243,ew257,ew267,ew269,ew270],localHints 6 0x6c1780b0580400e04806811c2582704c0741e81205c17c0a05c06204c270160760542900100c1400004f00a01c1280801c0800102102e0300c0030440240c81a0660d408804 0x570cae632bb0c15615418c6dc31b58610c10b55bd0baf41556dbad357b2b62cad75cd60d353a8b56a2d34cd54d0cfa4d42934f34c410198a265e89986065d79959c64e71955664d39109463e51904243cf18d8c50e314d34610605861f8627d86018617d55417a005555f79e69040171d05041a71c0cd3412db04d3432cb04619a1456861811410986195d76586025d75155564d35955544d33104913d24504033cf0cd34e2cb38d34c2ca2462071481c6183145103002040⟩,
  ⟨56,8,[ew127,ew217,ew243,ew257,ew267,ew269,ew270],localHints 6 0x360bc0582c0200702403408e12c1382603a0f41702b03c05014813078be80a90d0601f80b80a074b14d305200c004b585000a5a82780004a03804007086030818350040880901801200de80330400440d004 0x354e7b5b76bb677e793546943516ba776e7a77669a351e515b6538651df86515145b6df634b6f57746b57746db34b68b58b5f36615336615d758b50b1014b204b47210b48b0414513476b176f6f176f69a3476db5af5306475f06475145af5d704946e0474ae1074511094920472ed10906d1092cb0470473406ac76baac76b69a340a80580529660a29660514580a000654670400400404400659a59202e31008631002cb8a08600421df0400400401c004278234c6db75c69a75c6db34c69a5955d76585146585d759551410149204845111349004a45010f04e34c2cb10124904a1c710a2460481c6105082043000103082041000⟩,
  ⟨56,7,[ew100,ew217,ew239,ew243,ew257,ew269,ew270],localHints 6 0x1b02002c24047068c558a0414f60bc1601c09400cb98b90284680983008c1442700100c15c0003900a1580781802e009570760440481181a07c0200b00705a02807004 0x56ec2f630beeb956153d7b6b62dad75cf618ad3b0f56c3d34eb555a9860a5d729862a5d7a5554a4d32955694d324f3ca26828f3c96e71989a45e69186065d79159464e51955644d318f8c546314f1464464108862a20188607e18186007c001579975e6555407402517003dc0110093cf64a6406c000a0196d964668015a0060191590586145d75185815d65155414d30554944d22114413c10513903ce04a04b34c2ca2812410461881451c61011440c3081000⟩
]

def nodesBlock22 : Array Node := #[
  ⟨56,8,[ew217,ew239,ew243,ew253,ew257,ew269,ew270],localHints 6 0xd81001615c2b0390041053e07605e0181601c00a1d41102500e0340182b34e0780089a0280a4b600014404c0787e4ec1398b02301c8c40504305a0482326c078c440d0080080cd15811 0x718cf55f4775674cf371875871caaa7d575d7d5aaa71c75d5d79e76556186559e75d761870fab27f07727f0aaa70f75d5f09f164f63164f9e75f061814516f70f56f71c75d7caaaa7ca75d71caaa5d761864a9e764a6185d79e72cc56e08a32e2ca55530c32d2ca94a2d03cf2c296c2ca3cf70476b7e8aab7e875d704aaa5e86296449e96446185e89e70841440a45552e42e62c45442c49630a43e31501622c43c41504217042a17037607de6e07de75d7036c35c361a64d59a64d6185c358324d54d08330308354350d4cd2cd3d24034434033c32cd38d2402802c33032c3283240200080107143183143103080040⟩,
  ⟨56,9,[ew217,ew239,ew243,ew257,ew267,ew269,ew270],localHints 6 0x3615c058560200e41501f0501018b80f0ecc318485200c1402780500ef50123d34fa0301a8030563400f0010e6050148c90002300984e01c14d7f8150860c0012e202e02967012598f480d00d008f4537011 0x6d7e7b5b773b637e796d77176d373a7b6e7a7b671c6d3e535b65f8613df86135d75b6df66cdaf57b47357b4aeb6cd70d58da336225f3622a2858d5cd4b04f214d48d14d4cd4b0c706db71c788aeb78871c6dbaeb5965d7608a286085d7596a281481081524d31524af16e34d3c88a214834d3ed8a26e171c7acaeb7ac71c6e1aeb5a95d762aa2862a5d75a9a281521276e14e716634d3e58a216534d9238a21524a06e12206c371f79d69f79d71c6c36835835d960a55960a5d75835434904d41434831434c349045010a34e3c32ce10334d30a2ca1002001432431432031001c0100100143183143103080040⟩,
  ⟨56,9,[ew129,ew217,ew243,ew257,ew267,ew269,ew270],localHints 6 0xd82f03802c1601005407c1404b01e0202682b03c050148130a20540b03002e028d405200c004b685000a4102780003403803843048030010531a80d40900302208806804 0x1d0bb14ac5b156cbae1d05901cd5b066fbb066f5961cdb8d48d42d566b2d56641048db0d1c95eb66a5ab66a5d71c95894894e954a42954a4d34894092273683c99a83c934d2279a61c75966455d76455961c75d74924105454d35454104924d33c822508834d3c504508124904528a08524904c28a1c05a46638a46635961c088048042155a82155a41048080021e35f3c075f3c034d21e75d05a25c0406dc04024905a6da0431430800400801400430431c65d76585966585d71c65964914d35544105544d34914103c804e1c634d04c28a08124904b28a0812490882041c61440410c30810000410c3081000⟩,
  ⟨56,8,[ew197,ew217,ew243,ew253,ew257,ew267,ew269,ew270],localHints 6 0x6c1780b0580400e0756328f98c23d02c05c1381d04c0f40902b0280a40f0130781080a84c074064670060023200288d00008c1200803003c100ad06a0b4018090421d005004 0x3f0cae4f2bb0c0f4cf313c6dc31b534ccc0cb4fbccbaf30f3edbada9450a4d329452a4d3a1144a3cf2914683cf28328330c0c3b2a514ad34eb514a934e8451a4f3e9451a0f3d80e720c30b0e620a9854e59149644d31541453e31118c43cf1511613221461453058468442841461452851061040c41461451851031014e075f81d4d305f7dd3de05c7813cf75c71931b0436c130c64364128164369928a0430410c10c33830d80c51415970451465960945154d35545024d34114523cf4914503cf38334230c2c32c228a0c32422071851431041851431040c3002040⟩,
  ⟨56,7,[ew217,ew234,ew243,ew257,ew267,ew269,ew270],localHints 6 0x1b05e02c160100380a81401f08003c1380604c0740283d01c0482905009e01c0d00206a00c2f8310020502e0000261440403e02c0c00602302e0e8048200080441080a 0x42ec2c4f0b2eb904d0353bebbafad34cdb8dad0b4db2d35042bb2b264aa84eaa249094d3a21a4942926186841099f9c936725f7e634d1539629258934c59248908c586315042286178d8057e014d35e7df14715e2497871c52455d249d4d37524974d36cf3dc41070f3db41030b68435a10b2c134d6476042581071c12492015971560d34d44955134c34830d04023d10904033c304d3832ce0cd0cc2cb0492831ca0c90c81c70851830430c50c20420840830430c40c2040⟩,
  ⟨56,8,[ew100,ew217,ew243,ew257,ew267,ew269,ew270],localHints 6 0x6c1780b0580400e04808e0d02502703a0981eb160240fd8385f0620502e0130a20c019046032044d4852002018b78500005b8278050100580382504003c0c017004f5411009006084120230144141a804 0x97e3a5b66fa676e380976d70936f9775e397756db093e135b55f7653db76535d75b5db508c6b47726f477269a08c6db5b253364c5f364c5145b25d710e4b134c4f118c49218e4d30876f076f6b076f6db0876875875ee64852e6485d758750712b4ed3471073474c712bb2b10832a107107107307108a480806db7679a87676db0809805805d765e92565e5d75809001844e33404a31804c03444921843a210032218038010430c19e1e18007e11801c781e7de0816db75c69a75c6db08169a5955d76585146585d75955141844d334d49218f4d111049118438e11030c18f38b34d30b18a2081091c71892081041c7185103081000⟩,
  ⟨56,8,[ew217,ew223,ew243,ew253,ew257,ew267,ew269,ew270],localHints 6 0x6c1780b0580400e0756369018d23f01c0301380604c0740283d082048198ce190234118430340885703505a1d00182b03c0040a02900004c1e00802a03c1d0090220101080a 0x2f0cae3b2bb0c0b38b20ec6dc31b4e388c08b4bbc8baf20b2edbadaa490638e1a492a38ea218462cb1a18682cb181181208041b2a924ace3ab924a8e3a8861a4b2e9861a0b2dd0675482170665469843a58a496238e1249222e31218c42cb8a185e2201138042087937841847937de1861131040440536414dd48d35c38e70d35238e68a29b2cb6ca29a2cb6416122085c15d21860415925544c145211108e40f3503ce38234208b30028c00b2c22821c82420420880870470060020420860800400010020420810800400c4142042084083043001002042081080040⟩,
  ⟨56,7,[ew205,ew217,ew243,ew257,ew267,ew269,ew270],localHints 6 0x6c1780b0580400e02a05007c2000f0c60dc3104d05c0ac0a02903c04c1e01602a0e8290060021400284f0000e00380e0100600102201805c100030420640482305a0d405004 0x4f0cae5f2bb0c135d33d7c6dc31b575cfc0fb53bcfbaf3d34edbad2d8b2a5eca9860b5d7a95acb4eb2d556a4d3a10a4b3e92d04283cf2175e66279975c86082134c65651934c85480cf90842420f2124100ca8c82e320a2042cb05789f8627d75c18617d38017a00534df79e6cf74171d04f3db71c04b2db28a6cb2c12810c820119a0482031860986195d76586025d75155564d35955544d349044c3d13104033cf38b34c28d30b2c328a0c8209186248207185103002040⟩,
  ⟨56,8,[ew106,ew217,ew243,ew257,ew267,ew269,ew270],localHints 6 0x360bc0582c0200701502803e100318370c41341702b03c05014813078bf40a83b5bc0c8230190226a82900100c5c4280002e013c0280801c01c1282201e0680c00c00410c0490606a00deb02d04002811804 0x218e7b5f773b6b7e7921871821473a7b6e7a7b671c214e545f6638694df86946185f6df620c6f57b37357b36db20c71c5f357468c63468c5555f361804f4f238c53210c4d310f51420671c7b06f17b071c2066c65c66186a056f6a06185c654610152e3864ee1065063814d31013ed04632d1063c604130c20072c7abaac7ab71c200a805c0629682a296826185c0a000655273800403805000659a50423240400400403000428c285f1a210082210018685f81f20771c79d6db79d71c2076db5d66186995556996185d655510151438d4d31105120514d21013cf05130c1103cb38d30b10a049207186105082043000103082041000⟩,
  ⟨56,9,[ew217,ew243,ew253,ew257,ew267,ew269,ew270],localHints 6 0x360bc0582c0200703a8520a013c0383500409c0e80604c0141eb17024c2d853da7b29f40482b19c078008740280a46400011a04c1e0080a6c000aae401eb8dec02301af5d3b80a0860c812004006b340c811 0x718e7b5f777b677e7971875871477a7f6e7a7f675d714e545f6638654df86546185f6df671cb2c7cf75d7cfb2c71c75d5d7aaa64f61864faaa5d761830f14f3135143134f5730b2c7f475d7f4b2c73075d5f2aaa673618673aaa5f26183131717305313134ef7303ef70376e7edb2e7ed75d703b035c362b661aab6616185c3a834e75293034c33035034e7a271e13e13039833033c31e19611e12e13039033032c38e18a17047607de6e07de75d7046c45c461a64859a6486185c45844d15153044c43045044d14911483c83044043043c41483881482c83043443042c42882481400c61c40461440c3080040⟩,
  ⟨56,9,[ew108,ew217,ew243,ew257,ew267,ew269,ew270],localHints 6 0xd85707202c2b01009609c0e82609a0480702b03c050148130a20540b032032044d5852002018b905000041c27805046020038531aa0d4078020860240180d01409412004 0x2d3bb14ac5f156cbae2d35d32cd5f066fbb066f5d72cdb8d48d4ed565b2d5654d348db0d2cb5966495d76495962cb5d74924105494d35494104924d33cc32b08c34d3c90492c55ea6695aa6695d72c55854854e85464285464d34854053263673c59673c534d3269650462460850450852450461c62c05e46638a46635d72c08804804e15438215434d348080031e35f3c075f3c034d31e75d04324308004008024004304305a15c0406dc04014505a6da2ca5d76585966585d72ca5964914d35544105544d34914103cc04e2ca34d08c3082ca2480471860841450441860811450410c30840000440c3081000⟩,
  ⟨56,10,[ew217,ew243,ew257,ew267,ew269,ew270],localHints 7 0xd82f03802c1601005407c143ec096fac0780804e0740302600afa826be9024039f43e705cf99f280c0120ac2901e0020d40a0290a0000278137c8144298077c60540b3e27c20c1f00027be05c053de7ba0c9ee004006f6c0c811 0x3c69f4132f0fc136f1f3e3c68f9a3c50fc042fdf4042fcf9f3c51f143250d3d36d1e3d36d0d1a3251e143c318bb42e8fbb42e98b13c30f8c32317b93690d3936917af3230d0c70d4a372a31a372a30a146cd5a343c0cfb342c98b342c8f9f3c0d883320cd30368d7b0368cd1a320d7835caca2d2a0d52d2a0ca1458ad52a528c627500d2274c0c60c4a8d2233c10fa24280ea24280f9f3c10e843210d1c3624c1c3624d1a3210c042e48a162a108962a10a142648891202460e1e1050e1a1060c162450910001860e100860a101830400080⟩
]

def nodesGet (i : Nat) : Option Node :=
  if i < 176 then
    if i < 80 then
      if i < 32 then
        if i < 16 then
          nodesBlock0[(i-0)]?
        else
          nodesBlock1[(i-16)]?
      else
        if i < 48 then
          nodesBlock2[(i-32)]?
        else
          if i < 64 then
            nodesBlock3[(i-48)]?
          else
            nodesBlock4[(i-64)]?
    else
      if i < 128 then
        if i < 96 then
          nodesBlock5[(i-80)]?
        else
          if i < 112 then
            nodesBlock6[(i-96)]?
          else
            nodesBlock7[(i-112)]?
      else
        if i < 144 then
          nodesBlock8[(i-128)]?
        else
          if i < 160 then
            nodesBlock9[(i-144)]?
          else
            nodesBlock10[(i-160)]?
  else
    if i < 272 then
      if i < 224 then
        if i < 192 then
          nodesBlock11[(i-176)]?
        else
          if i < 208 then
            nodesBlock12[(i-192)]?
          else
            nodesBlock13[(i-208)]?
      else
        if i < 240 then
          nodesBlock14[(i-224)]?
        else
          if i < 256 then
            nodesBlock15[(i-240)]?
          else
            nodesBlock16[(i-256)]?
    else
      if i < 320 then
        if i < 288 then
          nodesBlock17[(i-272)]?
        else
          if i < 304 then
            nodesBlock18[(i-288)]?
          else
            nodesBlock19[(i-304)]?
      else
        if i < 336 then
          nodesBlock20[(i-320)]?
        else
          if i < 352 then
            nodesBlock21[(i-336)]?
          else
            nodesBlock22[(i-352)]?

def fastViews : QFast.Table View := ⟨57,viewsGet⟩

def fastNodes : QFast.Table Node := ⟨364,nodesGet⟩

end SignedProjection



namespace SignedProjection

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_0 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 0 16 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_16 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 16 16 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_32 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 32 16 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_48 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 48 9 = true := by decide +kernel

theorem joinRoots_0_0 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 0 32 = true :=
  @QFast.merge_blocks (QFast.checkRootAt fastViews fastNodes) 0 16 16 blockRoots_0 blockRoots_16

theorem joinRoots_0_32 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 32 25 = true :=
  @QFast.merge_blocks (QFast.checkRootAt fastViews fastNodes) 32 16 9 blockRoots_32 blockRoots_48

theorem joinRoots_1_0 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 0 57 = true :=
  @QFast.merge_blocks (QFast.checkRootAt fastViews fastNodes) 0 32 25 joinRoots_0_0 joinRoots_0_32

theorem certifiedRoots : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 0 57 = true := joinRoots_1_0

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
theorem blockNodes_84 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 84 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_96 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 96 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_108 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 108 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_120 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 120 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_132 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 132 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_144 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 144 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_156 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 156 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_168 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 168 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_180 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 180 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_192 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 192 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_204 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 204 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_216 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 216 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_228 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 228 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_240 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 240 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_252 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 252 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_264 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 264 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_276 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 276 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_288 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 288 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_300 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 300 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_312 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 312 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_324 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 324 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_336 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 336 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_348 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 348 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_360 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 360 4 = true := by decide +kernel

theorem joinNodes_0_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 12 12 blockNodes_0 blockNodes_12

theorem joinNodes_0_24 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 24 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 24 12 12 blockNodes_24 blockNodes_36

theorem joinNodes_0_48 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 48 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 48 12 12 blockNodes_48 blockNodes_60

theorem joinNodes_0_72 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 72 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 72 12 12 blockNodes_72 blockNodes_84

theorem joinNodes_0_96 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 96 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 96 12 12 blockNodes_96 blockNodes_108

theorem joinNodes_0_120 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 120 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 120 12 12 blockNodes_120 blockNodes_132

theorem joinNodes_0_144 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 144 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 144 12 12 blockNodes_144 blockNodes_156

theorem joinNodes_0_168 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 168 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 168 12 12 blockNodes_168 blockNodes_180

theorem joinNodes_0_192 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 192 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 192 12 12 blockNodes_192 blockNodes_204

theorem joinNodes_0_216 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 216 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 216 12 12 blockNodes_216 blockNodes_228

theorem joinNodes_0_240 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 240 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 240 12 12 blockNodes_240 blockNodes_252

theorem joinNodes_0_264 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 264 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 264 12 12 blockNodes_264 blockNodes_276

theorem joinNodes_0_288 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 288 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 288 12 12 blockNodes_288 blockNodes_300

theorem joinNodes_0_312 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 312 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 312 12 12 blockNodes_312 blockNodes_324

theorem joinNodes_0_336 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 336 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 336 12 12 blockNodes_336 blockNodes_348

theorem joinNodes_1_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 48 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 24 24 joinNodes_0_0 joinNodes_0_24

theorem joinNodes_1_48 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 48 48 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 48 24 24 joinNodes_0_48 joinNodes_0_72

theorem joinNodes_1_96 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 96 48 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 96 24 24 joinNodes_0_96 joinNodes_0_120

theorem joinNodes_1_144 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 144 48 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 144 24 24 joinNodes_0_144 joinNodes_0_168

theorem joinNodes_1_192 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 192 48 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 192 24 24 joinNodes_0_192 joinNodes_0_216

theorem joinNodes_1_240 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 240 48 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 240 24 24 joinNodes_0_240 joinNodes_0_264

theorem joinNodes_1_288 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 288 48 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 288 24 24 joinNodes_0_288 joinNodes_0_312

theorem joinNodes_1_336 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 336 28 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 336 24 4 joinNodes_0_336 blockNodes_360

theorem joinNodes_2_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 96 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 48 48 joinNodes_1_0 joinNodes_1_48

theorem joinNodes_2_96 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 96 96 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 96 48 48 joinNodes_1_96 joinNodes_1_144

theorem joinNodes_2_192 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 192 96 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 192 48 48 joinNodes_1_192 joinNodes_1_240

theorem joinNodes_2_288 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 288 76 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 288 48 28 joinNodes_1_288 joinNodes_1_336

theorem joinNodes_3_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 192 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 96 96 joinNodes_2_0 joinNodes_2_96

theorem joinNodes_3_192 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 192 172 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 192 96 76 joinNodes_2_192 joinNodes_2_288

theorem joinNodes_4_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 364 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 192 172 joinNodes_3_0 joinNodes_3_192

theorem certifiedNodes : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 364 = true := joinNodes_4_0

end SignedProjection

namespace SignedProjection
def bMatches (z : Option View) : Bool :=
  match z with
  | none => false
  | some v => vg v == (0xe880e800e8008000 : Word) && vk v == 10 && (vs v).toFinset == Direct64.cols.toFinset

theorem rootNegative : ¬ CoreSigned.build signedOps (0xe880e800e8008000 : BitVec 64) 10 Direct64.cols.toFinset := by
  have shape : bMatches (QFast.get fastViews 56) = true := by decide +kernel
  cases ev : QFast.get fastViews 56 with
  | none => simp [ev, bMatches] at shape
  | some v =>
    have valid := QFast.certified_view fastViews fastNodes certifiedRoots certifiedNodes ev
    simp only [ev,bMatches,Bool.and_eq_true,beq_iff_eq] at shape
    change ¬ CoreSigned.build signedOps (vg v) (vk v) (vs v).toFinset at valid
    rwa [shape.1.1,shape.1.2,shape.2] at valid
end SignedProjection
end PEqualNP.Outside.L_meta_12206_aux

open PEqualNP.Outside.L_meta_12206_aux in
theorem PEqualNP.Outside.L_meta_12206 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3900762112 * 2 ^ 32 + 3892346880) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3900762112 * 2 ^ 32 + 3892346880) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  LowerSymSix.finish SignedProjection.rootNegative
