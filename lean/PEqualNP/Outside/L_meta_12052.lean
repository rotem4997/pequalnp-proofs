import PEqualNP.Defs

-- The witness has twelve binary gates. Any circuit with a NOT and fewer gates
-- would have at most ten binary gates even with every negation available for free.
-- Finite signed-circuit certificates below exclude that possibility.
-- Signed-wire search and gate projections adapt the project’s Apache 2.0 proofs.
namespace PEqualNP.Outside.L_meta_12052_aux
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
  ⟨[⟨.and,[2,0]⟩,
    ⟨.and,[1,6]⟩,
    ⟨.or,[0,2]⟩,
    ⟨.or,[6,5]⟩,
    ⟨.and,[8,3]⟩,
    ⟨.and,[8,9]⟩,
    ⟨.or,[10,5]⟩,
    ⟨.or,[1,11]⟩,
    ⟨.and,[4,3]⟩,
    ⟨.or,[14,7]⟩,
    ⟨.and,[13,15]⟩,
    ⟨.and,[16,12]⟩],17⟩

theorem size : witness.size = 12 := rfl

theorem monotone : Monotone2 witness := by
  simp [Monotone2,witness]

set_option maxRecDepth 16000 in
theorem correct : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) =
    Nat.testBit (4269834368 * 2 ^ 32 + 3892346880) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel

end LowerSymSix

namespace Direct64
open PEqualNP.CircuitLowerBounds SignedProjection
abbrev W := BitVec 64
abbrev basicOps (a b : W) := signedOps a b
abbrev goal : W := ~~~0xfe808080e8008000
open CoreSigned (build)
def tableA (x : Fin 6 → Bool) :=
  Nat.testBit (4269834368 * 2 ^ 32 + 3892346880) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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

theorem sample64 : ∀ k : Fin 64, tableA (fun i => (cols.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by
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

theorem low (reject : ¬ build basicOps (0xfe808080e8008000 : W) 10 cols.toFinset)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = tableA x) : 10 < binaryCost gs := by
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
    (reject : ¬ CoreSigned.build SignedProjection.signedOps (0xfe808080e8008000 : BitVec 64) 10 Direct64.cols.toFinset) :
∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4269834368 * 2 ^ 32 + 3892346880) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4269834368 * 2 ^ 32 + 3892346880) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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

def ew0 : Word := 0xaa00

def ew1 : Word := 0xcc00

def ew2 : Word := 0xf000

def ew3 : Word := 0xa0aaaaa

def ew4 : Word := 0xc0ccccc

def ew5 : Word := 0x2222aaaa

def ew6 : Word := 0x2a2a2a2a

def ew7 : Word := 0x2a2aaaaa

def ew8 : Word := 0x3030f0f0

def ew9 : Word := 0x3f3f0000

def ew10 : Word := 0x4444cccc

def ew11 : Word := 0x4c4c4c4c

def ew12 : Word := 0x4c4ccccc

def ew13 : Word := 0x5050f0f0

def ew14 : Word := 0x5f5f0000

def ew15 : Word := 0x70707070

def ew16 : Word := 0x7070f0f0

def ew17 : Word := 0x77770000

def ew18 : Word := 0x7f7f0000

def ew19 : Word := 0x80808080

def ew20 : Word := 0x88008800

def ew21 : Word := 0x88880000

def ew22 : Word := 0x88888888

def ew23 : Word := 0xa000a000

def ew24 : Word := 0xa0a00000

def ew25 : Word := 0xa0a0a0a0

def ew26 : Word := 0xaa000000

def ew27 : Word := 0xaa0000aa

def ew28 : Word := 0xaa00aa00

def ew29 : Word := 0xaaaa0000

def ew30 : Word := 0xaaaaaaaa

def ew31 : Word := 0xc000c000

def ew32 : Word := 0xc0c00000

def ew33 : Word := 0xc0c0c0c0

def ew34 : Word := 0xcc000000

def ew35 : Word := 0xcc0000cc

def ew36 : Word := 0xcc00cc00

def ew37 : Word := 0xcccc0000

def ew38 : Word := 0xcccccccc

def ew39 : Word := 0xf0000000

def ew40 : Word := 0xf00000f0

def ew41 : Word := 0xf000f000

def ew42 : Word := 0xf0f00000

def ew43 : Word := 0xf0f0f0f0

def ew44 : Word := 0xff000000

def ew45 : Word := 0xff00ff00

def ew46 : Word := 0xffff0000

def ew47 : Word := 0x8800000088

def ew48 : Word := 0x8888000000

def ew49 : Word := 0xa0000000a0

def ew50 : Word := 0xa0a0000000

def ew51 : Word := 0xaa00000000

def ew52 : Word := 0xc0000000c0

def ew53 : Word := 0xc0c0000000

def ew54 : Word := 0xcc00000000

def ew55 : Word := 0xf000000000

def ew56 : Word := 0x80008000000

def ew57 : Word := 0x88000000000

def ew58 : Word := 0x88008800000

def ew59 : Word := 0xa000a000000

def ew60 : Word := 0xaa000000000

def ew61 : Word := 0xc000c000000

def ew62 : Word := 0xcc000000000

def ew63 : Word := 0x200020000000

def ew64 : Word := 0x208000000000

def ew65 : Word := 0x208020800000

def ew66 : Word := 0x220022000000

def ew67 : Word := 0x228800000000

def ew68 : Word := 0x300030000000

def ew69 : Word := 0x30c000000000

def ew70 : Word := 0x400040000000

def ew71 : Word := 0x408000000000

def ew72 : Word := 0x408040800000

def ew73 : Word := 0x440044000000

def ew74 : Word := 0x448800000000

def ew75 : Word := 0x500050000000

def ew76 : Word := 0x50a000000000

def ew77 : Word := 0xa0a000000000

def ew78 : Word := 0xaa0000000000

def ew79 : Word := 0xc0c000000000

def ew80 : Word := 0xcc0000000000

def ew81 : Word := 0xf00000000000

def ew82 : Word := 0x80008000800080

def ew83 : Word := 0x80008008800880

def ew84 : Word := 0x80008020802080

def ew85 : Word := 0x80008040804080

def ew86 : Word := 0x88000000880000

def ew87 : Word := 0x88000088000000

def ew88 : Word := 0x88008800000000

def ew89 : Word := 0xa0000000a00000

def ew90 : Word := 0xa00000a0000000

def ew91 : Word := 0xa000a000000000

def ew92 : Word := 0xaa000000000000

def ew93 : Word := 0xc0000000c00000

def ew94 : Word := 0xc00000c0000000

def ew95 : Word := 0xc000c000000000

def ew96 : Word := 0xcc000000000000

def ew97 : Word := 0xf0000000000000

def ew98 : Word := 0x200020080008000

def ew99 : Word := 0x200080000000000

def ew100 : Word := 0x200080002000800

def ew101 : Word := 0x200200000000000

def ew102 : Word := 0x200200002002000

def ew103 : Word := 0x200800002008000

def ew104 : Word := 0x202000002020000

def ew105 : Word := 0x202808000000000

def ew106 : Word := 0x202808002028080

def ew107 : Word := 0x202a0a000000000

def ew108 : Word := 0x208000000000000

def ew109 : Word := 0x208000002080000

def ew110 : Word := 0x208208000000000

def ew111 : Word := 0x208208002082080

def ew112 : Word := 0x220000000000000

def ew113 : Word := 0x220000002200000

def ew114 : Word := 0x220088000000000

def ew115 : Word := 0x288028800000000

def ew116 : Word := 0x2a002a000000000

def ew117 : Word := 0x3000000c0000000

def ew118 : Word := 0x300030000000000

def ew119 : Word := 0x300300000000000

def ew120 : Word := 0x300300003003000

def ew121 : Word := 0x300c0000300c000

def ew122 : Word := 0x303000003030000

def ew123 : Word := 0x303c0c000000000

def ew124 : Word := 0x30c000000000000

def ew125 : Word := 0x30c0000030c0000

def ew126 : Word := 0x30c30c000000000

def ew127 : Word := 0x400040080008000

def ew128 : Word := 0x400080000000000

def ew129 : Word := 0x400080004000800

def ew130 : Word := 0x400400000000000

def ew131 : Word := 0x400400004004000

def ew132 : Word := 0x400800004008000

def ew133 : Word := 0x404000004040000

def ew134 : Word := 0x404808000000000

def ew135 : Word := 0x404808004048080

def ew136 : Word := 0x404c0c000000000

def ew137 : Word := 0x408000000000000

def ew138 : Word := 0x408000004080000

def ew139 : Word := 0x408408000000000

def ew140 : Word := 0x408408004084080

def ew141 : Word := 0x440000000000000

def ew142 : Word := 0x440000004400000

def ew143 : Word := 0x440088000000000

def ew144 : Word := 0x488048800000000

def ew145 : Word := 0x4c004c000000000

def ew146 : Word := 0x5000000a0000000

def ew147 : Word := 0x500050000000000

def ew148 : Word := 0x500500000000000

def ew149 : Word := 0x500500005005000

def ew150 : Word := 0x500a0000500a000

def ew151 : Word := 0x505000005050000

def ew152 : Word := 0x505a0a000000000

def ew153 : Word := 0x50a000000000000

def ew154 : Word := 0x50a0000050a0000

def ew155 : Word := 0x50a50a000000000

def ew156 : Word := 0x700700007007000

def ew157 : Word := 0x707000007070000

def ew158 : Word := 0x800008008000080

def ew159 : Word := 0x800080008000800

def ew160 : Word := 0x808808000000000

def ew161 : Word := 0x808808008088080

def ew162 : Word := 0x880000008800000

def ew163 : Word := 0x880088000000000

def ew164 : Word := 0x880088008800880

def ew165 : Word := 0xa0000000000a000

def ew166 : Word := 0xa0000000a000000

def ew167 : Word := 0xa00000a0a00000a

def ew168 : Word := 0xa0000a000000000

def ew169 : Word := 0xa000a0000000000

def ew170 : Word := 0xa000a000a000a00

def ew171 : Word := 0xa00a00000000000

def ew172 : Word := 0xa00a0000a00a000

def ew173 : Word := 0xa0a000000000000

def ew174 : Word := 0xa0a00000a0a0000

def ew175 : Word := 0xa0a0a0a0a0a0a0a

def ew176 : Word := 0xa0aa0a000000000

def ew177 : Word := 0xa0aa0a00a0aa0a0

def ew178 : Word := 0xaa0000000000000

def ew179 : Word := 0xaa000000aa00000

def ew180 : Word := 0xaa00aa000000000

def ew181 : Word := 0xc0000000000c000

def ew182 : Word := 0xc0000000c000000

def ew183 : Word := 0xc00000c0c00000c

def ew184 : Word := 0xc0000c000000000

def ew185 : Word := 0xc000c0000000000

def ew186 : Word := 0xc000c000c000c00

def ew187 : Word := 0xc00c00000000000

def ew188 : Word := 0xc00c0000c00c000

def ew189 : Word := 0xc0c000000000000

def ew190 : Word := 0xc0c00000c0c0000

def ew191 : Word := 0xc0c0c0c0c0c0c0c

def ew192 : Word := 0xc0cc0c000000000

def ew193 : Word := 0xc0cc0c00c0cc0c0

def ew194 : Word := 0xcc0000000000000

def ew195 : Word := 0xcc000000cc00000

def ew196 : Word := 0xcc00cc000000000

def ew197 : Word := 0xe00ee000e00ee00

def ew198 : Word := 0xf00000000000000

def ew199 : Word := 0xf0000000f000000

def ew200 : Word := 0xf00000f00000000

def ew201 : Word := 0xf000f0000000000

def ew202 : Word := 0xf000f000f000f00

def ew203 : Word := 0xf00f00000000000

def ew204 : Word := 0xf00f0000f00f000

def ew205 : Word := 0xf0f000000000000

def ew206 : Word := 0xf0f00000f0f0000

def ew207 : Word := 0xf0f0f0f00000000

def ew208 : Word := 0xf0ff0f000000000

def ew209 : Word := 0x1000100080008000

def ew210 : Word := 0x1000200000000000

def ew211 : Word := 0x1000200010002000

def ew212 : Word := 0x1000400000000000

def ew213 : Word := 0x1000400010004000

def ew214 : Word := 0x1000800010008000

def ew215 : Word := 0x1010000010100000

def ew216 : Word := 0x1010808000000000

def ew217 : Word := 0x1010808010108080

def ew218 : Word := 0x1020000000000000

def ew219 : Word := 0x1020000010200000

def ew220 : Word := 0x1020408000000000

def ew221 : Word := 0x1040000000000000

def ew222 : Word := 0x1040000010400000

def ew223 : Word := 0x1040208000000000

def ew224 : Word := 0x10a010a000000000

def ew225 : Word := 0x10c010c000000000

def ew226 : Word := 0x1100000088000000

def ew227 : Word := 0x1100110000000000

def ew228 : Word := 0x1100880011008800

def ew229 : Word := 0x1111000011110000

def ew230 : Word := 0x1111888800000000

def ew231 : Word := 0x2000008020000080

def ew232 : Word := 0x2000200020002000

def ew233 : Word := 0x2020808000000000

def ew234 : Word := 0x2020808020208080

def ew235 : Word := 0x2080000020800000

def ew236 : Word := 0x2080208000000000

def ew237 : Word := 0x2080208020802080

def ew238 : Word := 0x2200000000008800

def ew239 : Word := 0x2200000022000000

def ew240 : Word := 0x2200002222000022

def ew241 : Word := 0x2200008800000000

def ew242 : Word := 0x2200220000000000

def ew243 : Word := 0x2200220022002200

def ew244 : Word := 0x2200880000000000

def ew245 : Word := 0x2222000022220000

def ew246 : Word := 0x2222222222222222

def ew247 : Word := 0x2288000000000000

def ew248 : Word := 0x2288000022880000

def ew249 : Word := 0x2288228800000000

def ew250 : Word := 0x2a2a2a2a2a2a2a2a

def ew251 : Word := 0x300000000000c000

def ew252 : Word := 0x3000000030000000

def ew253 : Word := 0x3000003030000030

def ew254 : Word := 0x300000c000000000

def ew255 : Word := 0x3000300000000000

def ew256 : Word := 0x3000300030003000

def ew257 : Word := 0x3000c00000000000

def ew258 : Word := 0x3000c0003000c000

def ew259 : Word := 0x3030000000000000

def ew260 : Word := 0x3030000030300000

def ew261 : Word := 0x3030303030303030

def ew262 : Word := 0x3030c0c000000000

def ew263 : Word := 0x30c0000000000000

def ew264 : Word := 0x30c0000030c00000

def ew265 : Word := 0x30c030c000000000

def ew266 : Word := 0x3200fa003200fa00

def ew267 : Word := 0x3300000000000000

def ew268 : Word := 0x3300000033000000

def ew269 : Word := 0x3300003300000000

def ew270 : Word := 0x3300330000000000

def ew271 : Word := 0x3300330033003300

def ew272 : Word := 0x3333000000000000

def ew273 : Word := 0x3333000033330000

def ew274 : Word := 0x3333333300000000

def ew275 : Word := 0x3f3f3f3f2a2a2a2a

def ew276 : Word := 0x4000008040000080

def ew277 : Word := 0x4000400040004000

def ew278 : Word := 0x4040808000000000

def ew279 : Word := 0x4040808040408080

def ew280 : Word := 0x4080000040800000

def ew281 : Word := 0x4080408000000000

def ew282 : Word := 0x4080408040804080

def ew283 : Word := 0x4400000000008800

def ew284 : Word := 0x4400000044000000

def ew285 : Word := 0x4400004444000044

def ew286 : Word := 0x4400008800000000

def ew287 : Word := 0x4400440000000000

def ew288 : Word := 0x4400440044004400

def ew289 : Word := 0x4400880000000000

def ew290 : Word := 0x4444000044440000

def ew291 : Word := 0x4444444444444444

def ew292 : Word := 0x4488000000000000

def ew293 : Word := 0x4488000044880000

def ew294 : Word := 0x4488448800000000

def ew295 : Word := 0x4c4c4c4c4c4c4c4c

def ew296 : Word := 0x500000000000a000

def ew297 : Word := 0x5000000050000000

def ew298 : Word := 0x5000005050000050

def ew299 : Word := 0x500000a000000000

def ew300 : Word := 0x5000500000000000

def ew301 : Word := 0x5000500050005000

def ew302 : Word := 0x5000a00000000000

def ew303 : Word := 0x5000a0005000a000

def ew304 : Word := 0x5050000000000000

def ew305 : Word := 0x5050000050500000

def ew306 : Word := 0x5050505050505050

def ew307 : Word := 0x5050a0a000000000

def ew308 : Word := 0x50a0000000000000

def ew309 : Word := 0x50a0000050a00000

def ew310 : Word := 0x50a050a000000000

def ew311 : Word := 0x5400fc005400fc00

def ew312 : Word := 0x5500000000000000

def ew313 : Word := 0x5500000055000000

def ew314 : Word := 0x5500005500000000

def ew315 : Word := 0x5500550000000000

def ew316 : Word := 0x5500550055005500

def ew317 : Word := 0x5555000000000000

def ew318 : Word := 0x5555000055550000

def ew319 : Word := 0x5555555500000000

def ew320 : Word := 0x5f5f5f5f4c4c4c4c

def ew321 : Word := 0x7070707070707070

def ew322 : Word := 0x7777777770707070

def ew323 : Word := 0x8000008008000008

def ew324 : Word := 0x8000008020000020

def ew325 : Word := 0x8000008040000040

def ew326 : Word := 0x8000008080000080

def ew327 : Word := 0x8000800008000800

def ew328 : Word := 0x8000800020002000

def ew329 : Word := 0x8000800040004000

def ew330 : Word := 0x8080000000008080

def ew331 : Word := 0x8080000008080000

def ew332 : Word := 0x8080000020200000

def ew333 : Word := 0x8080000040400000

def ew334 : Word := 0x8080000080800000

def ew335 : Word := 0x8080808080808080

def ew336 : Word := 0x8200000000008200

def ew337 : Word := 0x8200000041000000

def ew338 : Word := 0x8200000082000000

def ew339 : Word := 0x8200008200000000

def ew340 : Word := 0x8200820000000000

def ew341 : Word := 0x8200820082008200

def ew342 : Word := 0x8282000000000000

def ew343 : Word := 0x8282000082820000

def ew344 : Word := 0x8282828200000000

def ew345 : Word := 0x8282828282828282

def ew346 : Word := 0x8400000000008400

def ew347 : Word := 0x8400000021000000

def ew348 : Word := 0x8400000084000000

def ew349 : Word := 0x8400008400000000

def ew350 : Word := 0x8400840000000000

def ew351 : Word := 0x8400840084008400

def ew352 : Word := 0x8484000000000000

def ew353 : Word := 0x8484000084840000

def ew354 : Word := 0x8484848400000000

def ew355 : Word := 0x8484848484848484

def ew356 : Word := 0x8800000000008800

def ew357 : Word := 0x8800000022000000

def ew358 : Word := 0x8800000044000000

def ew359 : Word := 0x8800008800000000

def ew360 : Word := 0x8800008888000088

def ew361 : Word := 0x8800880000000000

def ew362 : Word := 0x8800880088008800

def ew363 : Word := 0x8888000000000000

def ew364 : Word := 0x8888000000008888

def ew365 : Word := 0x8888000088880000

def ew366 : Word := 0x8888888800000000

def ew367 : Word := 0x8888888888888888

def ew368 : Word := 0x8a8a8a8a8a8a8a8a

def ew369 : Word := 0x8c8c8c8c8c8c8c8c

def ew370 : Word := 0x9000000000009000

def ew371 : Word := 0x9000000009000000

def ew372 : Word := 0x9000000090000000

def ew373 : Word := 0x9000009000000000

def ew374 : Word := 0x9000900000000000

def ew375 : Word := 0x9000900090009000

def ew376 : Word := 0x9090000000000000

def ew377 : Word := 0x9090000090900000

def ew378 : Word := 0x9090909000000000

def ew379 : Word := 0x9090909090909090

def ew380 : Word := 0x9900000000000000

def ew381 : Word := 0x9900000099000000

def ew382 : Word := 0x9900990000000000

def ew383 : Word := 0x9900990099009900

def ew384 : Word := 0x9999000099990000

def ew385 : Word := 0x9999999900000000

def ew386 : Word := 0xa00000000000a000

def ew387 : Word := 0xa00000000a000000

def ew388 : Word := 0xa000000050000000

def ew389 : Word := 0xa00000a000000000

def ew390 : Word := 0xa00000a0a00000a0

def ew391 : Word := 0xa000a00000000000

def ew392 : Word := 0xa000a000a000a000

def ew393 : Word := 0xa0a0000000000000

def ew394 : Word := 0xa0a000000000a0a0

def ew395 : Word := 0xa0a00000a0a00000

def ew396 : Word := 0xa0a0a0a000000000

def ew397 : Word := 0xa0a0a0a0a0a0a0a0

def ew398 : Word := 0xa2a2a2a2a2a2a2a2

def ew399 : Word := 0xa500000000000000

def ew400 : Word := 0xa5000000a5000000

def ew401 : Word := 0xa500a50000000000

def ew402 : Word := 0xa500a500a500a500

def ew403 : Word := 0xa5a50000a5a50000

def ew404 : Word := 0xa5a5a5a500000000

def ew405 : Word := 0xa80000a8a80000a8

def ew406 : Word := 0xa8a80000a8a80000

def ew407 : Word := 0xa8a8a8a8a8a8a8a8

def ew408 : Word := 0xaa0000000000aa00

def ew409 : Word := 0xaa000000aa000000

def ew410 : Word := 0xaa0000aa00000000

def ew411 : Word := 0xaa0000aa88000088

def ew412 : Word := 0xaa0000aaa00000a0

def ew413 : Word := 0xaa0000aaaa0000aa

def ew414 : Word := 0xaa00aa0000000000

def ew415 : Word := 0xaa00aa00aa00aa00

def ew416 : Word := 0xaaaa000000000000

def ew417 : Word := 0xaaaa000088880000

def ew418 : Word := 0xaaaa0000a0a00000

def ew419 : Word := 0xaaaa0000aaaa0000

def ew420 : Word := 0xaaaaaaaa00000000

def ew421 : Word := 0xaaaaaaaa0a0a0a0a

def ew422 : Word := 0xaaaaaaaa22222222

def ew423 : Word := 0xaaaaaaaa80808080

def ew424 : Word := 0xaaaaaaaa88888888

def ew425 : Word := 0xaaaaaaaaa0a0a0a0

def ew426 : Word := 0xaaaaaaaaaaaaaaaa

def ew427 : Word := 0xafafafaf8c8c8c8c

def ew428 : Word := 0xb0b0b0b0b0b0b0b0

def ew429 : Word := 0xbbbbbbbbb0b0b0b0

def ew430 : Word := 0xc00000000000c000

def ew431 : Word := 0xc00000000c000000

def ew432 : Word := 0xc000000030000000

def ew433 : Word := 0xc00000c000000000

def ew434 : Word := 0xc00000c0c00000c0

def ew435 : Word := 0xc000c00000000000

def ew436 : Word := 0xc000c000c000c000

def ew437 : Word := 0xc0c0000000000000

def ew438 : Word := 0xc0c000000000c0c0

def ew439 : Word := 0xc0c00000c0c00000

def ew440 : Word := 0xc0c0c0c000000000

def ew441 : Word := 0xc0c0c0c0c0c0c0c0

def ew442 : Word := 0xc300000000000000

def ew443 : Word := 0xc3000000c3000000

def ew444 : Word := 0xc300c30000000000

def ew445 : Word := 0xc300c300c300c300

def ew446 : Word := 0xc3c30000c3c30000

def ew447 : Word := 0xc3c3c3c300000000

def ew448 : Word := 0xc4c4c4c4c4c4c4c4

def ew449 : Word := 0xc80000c8c80000c8

def ew450 : Word := 0xc8c80000c8c80000

def ew451 : Word := 0xc8c8c8c8c8c8c8c8

def ew452 : Word := 0xcc0000000000cc00

def ew453 : Word := 0xcc000000cc000000

def ew454 : Word := 0xcc0000cc00000000

def ew455 : Word := 0xcc0000cc88000088

def ew456 : Word := 0xcc0000ccc00000c0

def ew457 : Word := 0xcc0000cccc0000cc

def ew458 : Word := 0xcc00cc0000000000

def ew459 : Word := 0xcc00cc00cc00cc00

def ew460 : Word := 0xcccc000000000000

def ew461 : Word := 0xcccc000088880000

def ew462 : Word := 0xcccc0000c0c00000

def ew463 : Word := 0xcccc0000cccc0000

def ew464 : Word := 0xcccccccc00000000

def ew465 : Word := 0xcccccccc0c0c0c0c

def ew466 : Word := 0xcccccccc44444444

def ew467 : Word := 0xcccccccc80808080

def ew468 : Word := 0xcccccccc88888888

def ew469 : Word := 0xccccccccc0c0c0c0

def ew470 : Word := 0xcccccccccccccccc

def ew471 : Word := 0xcfcfcfcf8a8a8a8a

def ew472 : Word := 0xd0d0d0d0d0d0d0d0

def ew473 : Word := 0xddddddddd0d0d0d0

def ew474 : Word := 0xe00000e0e00000e0

def ew475 : Word := 0xe0e00000e0e00000

def ew476 : Word := 0xe0e0e0e0e0e0e0e0

def ew477 : Word := 0xea0000eac00000c0

def ew478 : Word := 0xeaea0000c0c00000

def ew479 : Word := 0xeaeaeaeaeaeaeaea

def ew480 : Word := 0xec0000eca00000a0

def ew481 : Word := 0xecec0000a0a00000

def ew482 : Word := 0xecececececececec

def ew483 : Word := 0xee0000000000ee00

def ew484 : Word := 0xee000000ee000000

def ew485 : Word := 0xee0000ee00000000

def ew486 : Word := 0xee00ee0000000000

def ew487 : Word := 0xee00ee00ee00ee00

def ew488 : Word := 0xeeee000000000000

def ew489 : Word := 0xeeeeeeeee0e0e0e0

def ew490 : Word := 0xeeeeeeeeeeeeeeee

def ew491 : Word := 0xf00000000000f000

def ew492 : Word := 0xf0000000f0000000

def ew493 : Word := 0xf00000f000000000

def ew494 : Word := 0xf00000f0a00000a0

def ew495 : Word := 0xf00000f0c00000c0

def ew496 : Word := 0xf00000f0f00000f0

def ew497 : Word := 0xf000f00000000000

def ew498 : Word := 0xf000f000f000f000

def ew499 : Word := 0xf0f0000000000000

def ew500 : Word := 0xf0f00000a0a00000

def ew501 : Word := 0xf0f00000c0c00000

def ew502 : Word := 0xf0f00000f0f00000

def ew503 : Word := 0xf0f0f0f000000000

def ew504 : Word := 0xf0f0f0f030303030

def ew505 : Word := 0xf0f0f0f050505050

def ew506 : Word := 0xf0f0f0f080808080

def ew507 : Word := 0xf0f0f0f0a0a0a0a0

def ew508 : Word := 0xf0f0f0f0c0c0c0c0

def ew509 : Word := 0xf0f0f0f0f0f0f0f0

def ew510 : Word := 0xf3f3f3f3a2a2a2a2

def ew511 : Word := 0xf5f5f5f5c4c4c4c4

def ew512 : Word := 0xf80000f888000088

def ew513 : Word := 0xf8f8000088880000

def ew514 : Word := 0xf8f8f8f8f8f8f8f8

def ew515 : Word := 0xfa0000000000fa00

def ew516 : Word := 0xfa000000fa000000

def ew517 : Word := 0xfa0000fa00000000

def ew518 : Word := 0xfa00fa0000000000

def ew519 : Word := 0xfa00fa00fa00fa00

def ew520 : Word := 0xfafa000000000000

def ew521 : Word := 0xfafafafac8c8c8c8

def ew522 : Word := 0xfafafafafafafafa

def ew523 : Word := 0xfc0000000000fc00

def ew524 : Word := 0xfc000000fc000000

def ew525 : Word := 0xfc0000fc00000000

def ew526 : Word := 0xfc00fc0000000000

def ew527 : Word := 0xfc00fc00fc00fc00

def ew528 : Word := 0xfcfc000000000000

def ew529 : Word := 0xfcfcfcfca8a8a8a8

def ew530 : Word := 0xfcfcfcfcfcfcfcfc

def ew531 : Word := 0xff00000000000000

def ew532 : Word := 0xff000000ff000000

def ew533 : Word := 0xff0000ff00000000

def ew534 : Word := 0xff00ff0000000000

def ew535 : Word := 0xff00ff00ff00ff00

def ew536 : Word := 0xffff000000000000

def ew537 : Word := 0xffff0000ffff0000

def ew538 : Word := 0xffffffff00000000

def ew539 : Word := 0xffffffff88888888

def ew540 : Word := 0xffffffffa0a0a0a0

def ew541 : Word := 0xffffffffaaaaaaaa

def ew542 : Word := 0xffffffffc0c0c0c0

def ew543 : Word := 0xffffffffcccccccc

def ew544 : Word := 0xfffffffff0f0f0f0

def labelsBlock0 : Array Nat := #[
  0xf1c,
  0x271c,
  0x1b2c,
  0xf2c,
  0x3964,
  0xf34,
  0xf38,
  0x1b64,
  0x1b68,
  0x1d64,
  0x1d34,
  0x1b4c,
  0x1d70,
  0x3a68,
  0x1e68,
  0x1e70
]

def labelsBlock1 : Array Nat := #[
  0x2794,
  0x2798,
  0x278c,
  0x1d54,
  0x1e38,
  0x39e0,
  0x122a,
  0x3ae0,
  0x1b0c,
  0x3c70,
  0x1e58,
  0x375c,
  0x12ee,
  0x12d2,
  0x3ce0,
  0x12d6
]

def labelsBlock2 : Array Nat := #[
  0x39c4,
  0x39a4,
  0x124e,
  0x12f6,
  0x12de,
  0x1232,
  0x12fa,
  0x1202,
  0x1266,
  0x12e2,
  0x37cc,
  0x1032,
  0x1b24,
  0x37d4,
  0x1b28,
  0x1d24
]

def labelsBlock3 : Array Nat := #[
  0xf24,
  0x3924,
  0xf28,
  0xf30,
  0x37d8,
  0x2714,
  0x1252,
  0x2718,
  0x1d14,
  0x270c,
  0x11fa,
  0x10b6,
  0xf14,
  0xf18,
  0x1226,
  0xf0c
]

def labelsBlock4 : Array Nat := #[
  0x130a,
  0x1026,
  0x1b60,
  0x371c,
  0x128e,
  0x3ac8,
  0x1d60,
  0x3aa8,
  0x2fac,
  0x275c,
  0x1e60,
  0x1e18,
  0x124a,
  0x126a,
  0x12e6,
  0x2fb4
]

def labelsBlock5 : Array Nat := #[
  0x1e28,
  0x2fb8,
  0x3cb0,
  0x12ea,
  0x3a28,
  0x10fa,
  0x39b4,
  0x12a6,
  0x3984,
  0x1262,
  0x3960,
  0x4102d2,
  0x4202d2,
  0x1d30,
  0x3cd0,
  0x4212d2
]

def labelsBlock6 : Array Nat := #[
  0x3a60,
  0x1b44,
  0x1b48,
  0x1e30,
  0x3c60,
  0x1d44,
  0x102a,
  0x1b1c,
  0x12f2,
  0x1d1c,
  0x1e1c,
  0x4102ee,
  0x11ee,
  0x12b6,
  0x1b5c,
  0x1d5c
]

def labelsBlock7 : Array Nat := #[
  0x1e5c,
  0x5402ee,
  0x5412ee,
  0x3ab8,
  0x3a88,
  0x7212d2,
  0x2790,
  0x3754,
  0x3758,
  0x374c,
  0x4102f6,
  0x7102d2,
  0x7202d2,
  0x3944,
  0x3c30,
  0x4102fa
]

def labelsBlock8 : Array Nat := #[
  0x1d50,
  0x3904,
  0x1e48,
  0x1b04,
  0x1b08,
  0x1d04,
  0x11f2,
  0x7102ee,
  0x6412ee,
  0x6402ee,
  0x5402f6,
  0x3c90,
  0xf20,
  0x1440102d2,
  0x1480202d2,
  0x1484212d2
]

def labelsBlock9 : Array Nat := #[
  0x12ca,
  0x6402f6,
  0x7012d2,
  0x7022d2,
  0x1e50,
  0x5412f6,
  0x3994,
  0x6102f6,
  0x27b4,
  0x27b8,
  0x7122d2,
  0x4122d2,
  0x102e,
  0x11f6,
  0x12c2,
  0x37c8
]

def labelsBlock10 : Array Nat := #[
  0x37c4,
  0x2f2c,
  0x4022d2,
  0x4012d2,
  0x2788,
  0x2784,
  0x2f34,
  0x2f38,
  0x11fe,
  0x7102f6,
  0x5102d2,
  0x5202d2,
  0x37d0,
  0x3a08,
  0x27ac,
  0x5212d2
]

def labelsBlock11 : Array Nat := #[
  0x6212d2,
  0x3a48,
  0x1e08,
  0x27cc,
  0x112e,
  0x5402fa,
  0x5412fa,
  0x1440102ee,
  0x6102ee,
  0x1d10,
  0x5102ee,
  0x6102fa,
  0x7102fa,
  0x6102d2,
  0x6202d2,
  0x3a98
]

def labelsBlock12 : Array Nat := #[
  0x1e10,
  0x6412f6,
  0x3920,
  0x3a20,
  0x3c20,
  0x6412fa,
  0x6402fa,
  0x5102f6,
  0x3bcc,
  0x39c0,
  0x1206,
  0x1f1c,
  0x1f5c,
  0x3ac0,
  0x1440102fa,
  0x41030a
]

def labelsBlock13 : Array Nat := #[
  0x1440102f6,
  0x42030a,
  0x42130a,
  0x2fa8,
  0x2fa4,
  0x1b20,
  0x1d20,
  0x1e20,
  0x7012ee,
  0x2fb0,
  0xf04,
  0xf08,
  0x3980,
  0x2710,
  0x3dd4,
  0x3a80
]

def labelsBlock14 : Array Nat := #[
  0x3ed8,
  0xf10,
  0x122e,
  0x1276,
  0x3bac,
  0x3c10,
  0x39a0,
  0x127a,
  0x1272,
  0x126e,
  0x4102ca,
  0x4202ca,
  0x4212ca,
  0x1c94102d2,
  0x5102fa,
  0x1c54202d2
]

def labelsBlock15 : Array Nat := #[
  0x2704,
  0x2708,
  0x3c80,
  0x3aa0,
  0x1282,
  0x14401030a,
  0x1095102d2,
  0x14802030a,
  0x14842130a,
  0x1b54,
  0x1b58,
  0x1d4c,
  0x1d58,
  0x1e4c,
  0x1e54,
  0x3b8c
]

def labelsBlock16 : Array Nat := #[
  0x3c50,
  0x3be0,
  0x3ca0,
  0x3cc0,
  0x1296,
  0x398c,
  0x3c98,
  0x3a8c,
  0x3c94,
  0x3d94,
  0x3db4,
  0x3e98,
  0x3eb8,
  0x10be,
  0x129a,
  0x128a
]

def labelsBlock17 : Array Nat := #[
  0x2780,
  0x12ae,
  0x6022d2,
  0x6012d2,
  0x1c96102d2,
  0x1c97102d2,
  0x1c56202d2,
  0x1c57202d2,
  0x1c16212d2,
  0x1c17212d2,
  0x1940212d2,
  0xf00,
  0x106a,
  0x12a2,
  0x1b14,
  0x3914
]

def labelsBlock18 : Array Nat := #[
  0x39d4,
  0x1b18,
  0x1d0c,
  0x39cc,
  0x1d18,
  0x3cb8,
  0x1e0c,
  0x3acc,
  0x1e14,
  0x3cb4,
  0x3b64,
  0x3b68,
  0x3d64,
  0x3de0,
  0x3ee0,
  0x63222a
]

def labelsBlock19 : Array Nat := #[
  0x12ba,
  0x1306,
  0x3a18,
  0x3ad8,
  0x3934,
  0x3c18,
  0x3cd8,
  0x3c14,
  0x3cd4,
  0x1b40,
  0x3d70,
  0x3e68,
  0x3e70,
  0x1076,
  0x120e,
  0x127e
]

def labelsBlock20 : Array Nat := #[
  0x1286,
  0x129e,
  0x12b2,
  0x1094102d2,
  0x6122d2,
  0x4012ee,
  0x1145202d2,
  0x1141212d2,
  0x1302,
  0x1b00,
  0x3990,
  0x3a90,
  0x39b0,
  0x3ab0,
  0x390c,
  0x3a0c
]

def labelsBlock21 : Array Nat := #[
  0x2fa0,
  0x37c0,
  0x272c,
  0x109a,
  0x2734,
  0x2738,
  0x1216,
  0xfac,
  0x5012ee,
  0x1b8c,
  0x1bcc,
  0x3b2c,
  0x1092,
  0x10aa,
  0x10de,
  0x107e
]

def labelsBlock22 : Array Nat := #[
  0x120a,
  0x12c6,
  0x12ce,
  0x5122d2,
  0x2d9c,
  0x2b9c,
  0x2e9c,
  0x39ac,
  0x3aac,
  0x1f64,
  0x1e40,
  0x1f68,
  0x1d40,
  0x1f70,
  0x3d34,
  0x3e38
]

def labelsBlock23 : Array Nat := #[
  0x108e,
  0x10a2,
  0x10d6,
  0x10ee,
  0x1112,
  0x110a,
  0x121e,
  0xfb4,
  0x63228e,
  0x1e00,
  0x1d00,
  0x1d94,
  0x1dd4,
  0xf64,
  0xf68,
  0x3954
]

def labelsBlock24 : Array Nat := #[
  0x3a58,
  0x394c,
  0x3c58,
  0x3a4c,
  0x3c54,
  0x3744,
  0x3748,
  0x3750,
  0x1122,
  0x6102ca,
  0x7102ca,
  0x4012f6,
  0x6202ca,
  0x7202ca,
  0x6212ca,
  0x7212ca
]

def labelsBlock25 : Array Nat := #[
  0x1e98,
  0x1ed8,
  0x3740,
  0x274c,
  0x10da,
  0x1212,
  0x632266,
  0x63224e,
  0x5022d2,
  0x410302,
  0x410306,
  0x5012d2,
  0x420302,
  0xfb8,
  0x540306,
  0x421302
]

def labelsBlock26 : Array Nat := #[
  0x541306,
  0x542306,
  0x27c4,
  0x27c8,
  0xf70,
  0x108a,
  0x10ba,
  0x10e6,
  0x110e,
  0x4012fa,
  0x420306,
  0x421306,
  0x2700,
  0x339c,
  0x359c,
  0x369c
]

def labelsBlock27 : Array Nat := #[
  0x3a38,
  0x3940,
  0x3a40,
  0x3c40,
  0x1096,
  0x111a,
  0x119e,
  0x1166,
  0x116a,
  0x1440102ca,
  0x5412e6,
  0x5102ca,
  0x510306,
  0x61030a,
  0x71030a,
  0x1480202ca
]

def labelsBlock28 : Array Nat := #[
  0x5402ea,
  0x5202ca,
  0x520306,
  0x62030a,
  0x72030a,
  0x1484212ca,
  0x5402f2,
  0x5212ca,
  0x4042ee,
  0x4142ee,
  0x62130a,
  0x72130a,
  0x521306,
  0x4142f6,
  0x3c38,
  0x392c
]

def labelsBlock29 : Array Nat := #[
  0x3c34,
  0x3a2c,
  0x3b0c,
  0x3d14,
  0x3e18,
  0x190810306,
  0x51030a,
  0x52030a,
  0x52130a,
  0x3a00,
  0x3900,
  0x3c00,
  0xfa4,
  0xfa8,
  0xfb0,
  0x2f24
]

def labelsBlock30 : Array Nat := #[
  0x3b24,
  0x2f28,
  0x3d24,
  0x2f30,
  0x3e28,
  0xf4c,
  0x10a6,
  0x2f94,
  0x2f98,
  0x1036,
  0x114a,
  0x105a,
  0x115a,
  0x1182,
  0x410236,
  0x1066
]

def labelsBlock31 : Array Nat := #[
  0x6012ee,
  0x1148102d2,
  0x6412e6,
  0x150810306,
  0x610306,
  0x710306,
  0x6402ea,
  0x150420306,
  0x190420306,
  0x1055202d2,
  0x620306,
  0x720306,
  0x108540306,
  0x1015212d2,
  0x6402f2,
  0x108640306
]

def labelsBlock32 : Array Nat := #[
  0x640306,
  0x621306,
  0x721306,
  0x4042f6,
  0x641306,
  0x4042fa,
  0x4142fa,
  0x642306,
  0x1ee0,
  0x1de0,
  0x27d0,
  0x1be0,
  0x370c,
  0x103a,
  0x105e,
  0x10b2
]

def labelsBlock33 : Array Nat := #[
  0x118a,
  0x11b6,
  0x11e2,
  0x118e,
  0x11ba,
  0x11e6,
  0x1102,
  0x1236,
  0x6322a6,
  0x1494102d2,
  0x144010306,
  0x610302,
  0x710302,
  0x1454202d2,
  0x148020306,
  0x620302
]

def labelsBlock34 : Array Nat := #[
  0x720302,
  0x1540212d2,
  0x148421306,
  0x621302,
  0x721302,
  0x3930,
  0x3a30,
  0x1f04,
  0x3704,
  0x1f44,
  0x1f08,
  0x3708,
  0x1f48,
  0x3b28,
  0x1f10,
  0x1f50
]

def labelsBlock35 : Array Nat := #[
  0x3d30,
  0x3714,
  0x3e30,
  0x3718,
  0x1b34,
  0x109e,
  0x27a4,
  0x1b38,
  0x10ae,
  0x27a8,
  0x10e2,
  0x27d4,
  0x10f2,
  0x27b0,
  0x1116,
  0x27d8
]

def labelsBlock36 : Array Nat := #[
  0x1126,
  0x113e,
  0x1f0c,
  0x115e,
  0x1196,
  0x1f4c,
  0x3b4c,
  0x1172,
  0x3d54,
  0x11aa,
  0x114e,
  0x1162,
  0x11c2,
  0x1176,
  0x3e58,
  0x11d6
]

def labelsBlock37 : Array Nat := #[
  0x117a,
  0x119a,
  0x11c6,
  0x103e,
  0x11ae,
  0x11da,
  0x1062,
  0x1186,
  0x11b2,
  0x11de,
  0x1136,
  0x1192,
  0x11be,
  0x11ea,
  0x10c2,
  0x107a
]

def labelsBlock38 : Array Nat := #[
  0x116e,
  0x11ca,
  0x11ce,
  0x11a2,
  0x1292,
  0x144010302,
  0x510302,
  0x148020302,
  0x520302,
  0x1c14212d2,
  0x148421302,
  0x521302,
  0x100e,
  0x1016,
  0x1bac,
  0x1db4
]

def labelsBlock39 : Array Nat := #[
  0x1eb8,
  0x2de4,
  0x2be4,
  0x2ee8,
  0x2be8,
  0x2ef0,
  0x2df0,
  0xfa0,
  0x39d0,
  0x3ad0,
  0x3928,
  0x3c28,
  0x3988,
  0x3c88,
  0x39a8,
  0x3ca8
]

def labelsBlock40 : Array Nat := #[
  0x39c8,
  0x3cc8,
  0x3a24,
  0x3c24,
  0x3a84,
  0x3c84,
  0x3aa4,
  0x3ca4,
  0x3ac4,
  0x3cc4,
  0x3b04,
  0x3b08,
  0x3b44,
  0x3b48,
  0x3b20,
  0x3b80
]

def labelsBlock41 : Array Nat := #[
  0x3ba0,
  0x3bc0,
  0x3d04,
  0x3d10,
  0x3d44,
  0x3d50,
  0x3d20,
  0x3d80,
  0x3da0,
  0x3dc0,
  0x3e08,
  0x3e10,
  0x3e48,
  0x3e50,
  0x3e20,
  0x3e80
]

def labelsBlock42 : Array Nat := #[
  0x3ea0,
  0x3ec0,
  0x106e,
  0x1042,
  0x1082,
  0x1046,
  0x104a,
  0x2754,
  0x10ce,
  0x104e,
  0x1052,
  0x2758,
  0x10ca,
  0x1056,
  0x1f14,
  0x3b84
]

def labelsBlock43 : Array Nat := #[
  0x3d84,
  0x1f54,
  0x3bc4,
  0x3dc4,
  0x3e88,
  0x3ec8,
  0x10fe,
  0x1106,
  0x55d,
  0x565,
  0x549,
  0x555,
  0x589,
  0x581,
  0x5c1,
  0x5b9
]

def labelsBlock44 : Array Nat := #[
  0x123a,
  0x117e,
  0x1156,
  0x1146,
  0x43128a,
  0x4102b2,
  0x43028a,
  0x4102a2,
  0x41028a,
  0x4302a2,
  0x12be,
  0x431296,
  0x4102ba,
  0x430296,
  0x4102ae,
  0x410296
]

def labelsBlock45 : Array Nat := #[
  0x4302ae,
  0x12da,
  0x7012f6,
  0x426440102d2,
  0x121a,
  0x779,
  0x77d,
  0x1242,
  0x74d,
  0x150a10306,
  0x190a10306,
  0x150b10306,
  0x190b10306,
  0x416480202d2,
  0x123e,
  0x809
]

def labelsBlock46 : Array Nat := #[
  0x80d,
  0x150620306,
  0x190620306,
  0x150720306,
  0x190720306,
  0x406484212d2,
  0x879,
  0x188540306,
  0x1c8540306,
  0x8bd,
  0x188640306,
  0x1c8640306,
  0x1256,
  0x12fe,
  0x1002,
  0x1006
]

def labelsBlock47 : Array Nat := #[
  0x100a,
  0x101e,
  0x1022,
  0x33e4,
  0x35e4,
  0x33e8,
  0x36e8,
  0x35f0,
  0x36f0,
  0x189,
  0x3794,
  0x191,
  0x199,
  0x1a5,
  0x1a9,
  0x1ad
]

def labelsBlock48 : Array Nat := #[
  0x1c9,
  0x3798,
  0x1d1,
  0x1d9,
  0x1e5,
  0x1e9,
  0x1ed,
  0x209,
  0x211,
  0x219,
  0x221,
  0x229,
  0x231,
  0x241,
  0x378c,
  0x249
]

def labelsBlock49 : Array Nat := #[
  0x251,
  0x25d,
  0x261,
  0x265,
  0x10ea,
  0x281,
  0x289,
  0x291,
  0x29d,
  0x2a1,
  0x2a5,
  0x2bd,
  0x2c5,
  0x2cd,
  0x2d9,
  0x2dd
]

def labelsBlock50 : Array Nat := #[
  0x2e1,
  0x111e,
  0x2fd,
  0x305,
  0x30d,
  0x319,
  0x31d,
  0x321,
  0x1f18,
  0x3b88,
  0x1f58,
  0x3bc8,
  0x3d90,
  0x3e90,
  0x3dd0,
  0x3ed0
]

def labelsBlock51 : Array Nat := #[
  0x112a,
  0x10f6,
  0x1132,
  0x3ba4,
  0x3da4,
  0x3ea8,
  0x113a,
  0x561,
  0x569,
  0x56d,
  0x571,
  0x58d,
  0x591,
  0x595,
  0x5a5,
  0x5a9
]

def labelsBlock52 : Array Nat := #[
  0x5c5,
  0x5c9,
  0x5d9,
  0x420232,
  0x430236,
  0x421232,
  0x431236,
  0x10d2,
  0x1086,
  0x1072,
  0x621,
  0x62d,
  0x63d,
  0x661,
  0x420266,
  0x42024e
]

def labelsBlock53 : Array Nat := #[
  0x669,
  0x42328e,
  0x675,
  0x679,
  0x67d,
  0x68d,
  0x699,
  0x421266,
  0x42022a,
  0x69d,
  0x6a1,
  0x6a9,
  0x6bd,
  0x6c1,
  0x6c9,
  0x6d1
]

def labelsBlock54 : Array Nat := #[
  0x42124e,
  0x42122a,
  0x6dd,
  0x70d,
  0x719,
  0x729,
  0x5102e6,
  0x751,
  0x7102e6,
  0x75d,
  0x5402e6,
  0x765,
  0x769,
  0x54244010306,
  0x775,
  0x64244010306
]

def labelsBlock55 : Array Nat := #[
  0x76550810306,
  0x781,
  0x789,
  0x78d,
  0x150910306,
  0x190910306,
  0x79d,
  0x7a1,
  0x5102fe,
  0x4012ea,
  0x7a9,
  0x76550a10306,
  0x1048012d2,
  0x5012fa,
  0x1086102d2,
  0x7b5
]

def labelsBlock56 : Array Nat := #[
  0x401306,
  0x7b9,
  0x7bd,
  0x4012f2,
  0x7c5,
  0x76550b10306,
  0x1008012d2,
  0x1083102d2,
  0x7d1,
  0x7d5,
  0x7d9,
  0x5012ea,
  0x7e1,
  0x7012ea,
  0x7ed,
  0x5412ea
]

def labelsBlock57 : Array Nat := #[
  0x7f5,
  0x7f9,
  0x54148020306,
  0x805,
  0x64148020306,
  0x76550420306,
  0x811,
  0x819,
  0x81d,
  0x150520306,
  0x190520306,
  0x82d,
  0x831,
  0x5202fe,
  0x4012e6,
  0x839
]

def labelsBlock58 : Array Nat := #[
  0x1048022d2,
  0x5012f6,
  0x104a202d2,
  0x845,
  0x402306,
  0x849,
  0x84d,
  0x855,
  0x1043202d2,
  0x861,
  0x865,
  0x869,
  0x75608540306,
  0x12aa,
  0x52108540306,
  0x875
]

def labelsBlock59 : Array Nat := #[
  0x148540306,
  0x100a212d2,
  0x889,
  0x891,
  0x1007212d2,
  0x899,
  0x8a1,
  0x87d,
  0x885,
  0x895,
  0x8a5,
  0x5402fe,
  0x52108640306,
  0x148640306,
  0x8c1,
  0x8c5
]

def labelsBlock60 : Array Nat := #[
  0x8c9,
  0x8cd,
  0x5102f2,
  0x8d5,
  0x6102f2,
  0x8e1,
  0x8e9,
  0x5412f2,
  0x8f1,
  0x8f9,
  0x5212fe,
  0x412306,
  0x5412fe,
  0x5422fe,
  0x1012,
  0x101a
]

def labelsBlock61 : Array Nat := #[
  0x1b84,
  0x1d84,
  0x1b88,
  0x1e88,
  0x1d90,
  0x1e90,
  0x1bc4,
  0x1dc4,
  0x1bc8,
  0x1ec8,
  0x1dd0,
  0x1ed0,
  0xf44,
  0x2744,
  0x1ea0,
  0xf48
]

def labelsBlock62 : Array Nat := #[
  0x2748,
  0x1da0,
  0xf50,
  0x2750,
  0x1ba0,
  0x18d,
  0x1b5,
  0x195,
  0x19d,
  0x1a1,
  0x1b1,
  0x1b9,
  0x1bd,
  0x1cd,
  0x1f5,
  0x1d5
]

def labelsBlock63 : Array Nat := #[
  0x1dd,
  0x1e1,
  0x1f1,
  0x1f9,
  0x1fd,
  0x20d,
  0x225,
  0x205,
  0x215,
  0x21d,
  0x22d,
  0x235,
  0x239,
  0x245,
  0x26d,
  0x24d
]

def labelsBlock64 : Array Nat := #[
  0x255,
  0x259,
  0x269,
  0x271,
  0x275,
  0x1d38,
  0xf54,
  0x285,
  0x2ad,
  0x28d,
  0x295,
  0x299,
  0x2a9,
  0x2b1,
  0x2b5,
  0x2c1
]

def labelsBlock65 : Array Nat := #[
  0x2e9,
  0x2c9,
  0x2d1,
  0x2d5,
  0x2e5,
  0x2ed,
  0x2f1,
  0x1e34,
  0xf58,
  0x301,
  0x329,
  0x309,
  0x311,
  0x315,
  0x325,
  0x32d
]

def labelsBlock66 : Array Nat := #[
  0x331,
  0x339,
  0x33d,
  0x341,
  0x345,
  0x349,
  0x34d,
  0x351,
  0x355,
  0x359,
  0x35d,
  0x361,
  0x365,
  0x36d,
  0x371,
  0x375
]

def labelsBlock67 : Array Nat := #[
  0x379,
  0x37d,
  0x381,
  0x385,
  0x389,
  0x38d,
  0x391,
  0x395,
  0x399,
  0x3a1,
  0x3a5,
  0x3a9,
  0x3ad,
  0x3b1,
  0x3b5,
  0x3b9
]

def labelsBlock68 : Array Nat := #[
  0x3bd,
  0x3c1,
  0x3c5,
  0x3c9,
  0x3cd,
  0x3d5,
  0x3d9,
  0x3dd,
  0x3e1,
  0x3e5,
  0x3e9,
  0x3ed,
  0x3f1,
  0x3f5,
  0x3f9,
  0x3fd
]

def labelsBlock69 : Array Nat := #[
  0x401,
  0x409,
  0x40d,
  0x411,
  0x415,
  0x419,
  0x41d,
  0x421,
  0x425,
  0x429,
  0x42d,
  0x431,
  0x435,
  0x43d,
  0x441,
  0x445
]

def labelsBlock70 : Array Nat := #[
  0x449,
  0x44d,
  0x451,
  0x455,
  0x459,
  0x45d,
  0x461,
  0x465,
  0x469,
  0x471,
  0x475,
  0x479,
  0x47d,
  0x481,
  0x485,
  0x489
]

def labelsBlock71 : Array Nat := #[
  0x48d,
  0x491,
  0x495,
  0x499,
  0x49d,
  0x4a9,
  0x4ad,
  0x4b1,
  0x4b5,
  0x4b9,
  0x4bd,
  0x4c1,
  0x4c5,
  0x4c9,
  0x4cd,
  0x4d1
]

def labelsBlock72 : Array Nat := #[
  0x4d5,
  0x3ba8,
  0x3db0,
  0x3eb0,
  0x4dd,
  0x4e1,
  0x4e5,
  0x4e9,
  0x4ed,
  0x4f1,
  0x4f5,
  0x4f9,
  0x4fd,
  0x501,
  0x505,
  0x509
]

def labelsBlock73 : Array Nat := #[
  0x511,
  0x515,
  0x519,
  0x51d,
  0x521,
  0x525,
  0x529,
  0x52d,
  0x531,
  0x535,
  0x539,
  0x53d,
  0x545,
  0x551,
  0x54d,
  0x559
]

def labelsBlock74 : Array Nat := #[
  0x57d,
  0x579,
  0x585,
  0x59d,
  0x5a1,
  0x5b5,
  0x5b1,
  0x5bd,
  0x5d1,
  0x5d5,
  0x5e1,
  0x5e5,
  0x575,
  0x599,
  0x5ad,
  0x5cd
]

def labelsBlock75 : Array Nat := #[
  0x5dd,
  0x5e9,
  0x5f1,
  0x5f5,
  0x5f9,
  0x5fd,
  0x601,
  0x605,
  0x609,
  0x1152,
  0x1142,
  0x61d,
  0x4102c6,
  0x629,
  0x4202c6,
  0x639
]

def labelsBlock76 : Array Nat := #[
  0x4302b2,
  0x4212c6,
  0x4312b2,
  0x4312a2,
  0x625,
  0x631,
  0x635,
  0x641,
  0x645,
  0x649,
  0x64d,
  0x651,
  0x655,
  0x659,
  0x671,
  0x6322b6
]

def labelsBlock77 : Array Nat := #[
  0x66d,
  0x695,
  0x6a5,
  0x6b9,
  0x4232a6,
  0x6d9,
  0x665,
  0x681,
  0x685,
  0x689,
  0x691,
  0x6ad,
  0x6b1,
  0x6b5,
  0x6c5,
  0x6cd
]

def labelsBlock78 : Array Nat := #[
  0x6d5,
  0x6e1,
  0x6e5,
  0x6e9,
  0x6ed,
  0x6f1,
  0x6f5,
  0x6f9,
  0x6fd,
  0x701,
  0x709,
  0x4102ce,
  0x715,
  0x4202ce,
  0x725,
  0x4302ba
]

def labelsBlock79 : Array Nat := #[
  0x4212ce,
  0x4312ba,
  0x4312ae,
  0x711,
  0x71d,
  0x721,
  0x72d,
  0x731,
  0x735,
  0x739,
  0x73d,
  0x741,
  0x745,
  0x7012e6,
  0x76d,
  0x11d942440102fe
]

def labelsBlock80 : Array Nat := #[
  0x542440102fe,
  0x642440102fe,
  0x1440102fe,
  0x765508102fe,
  0x785,
  0x1508102fe,
  0x1908102fe,
  0x755,
  0x759,
  0x761,
  0x771,
  0x4102fe,
  0x46550910306,
  0x465509102fe,
  0x799,
  0x1509102fe
]

def labelsBlock81 : Array Nat := #[
  0x1909102fe,
  0x795,
  0x1c961030a,
  0x6142f6,
  0x76550a102fe,
  0x7b1,
  0x150a102fe,
  0x190a102fe,
  0x7ad,
  0x1222,
  0x6102fe,
  0x1c971030a,
  0x6142ee,
  0x76550b102fe,
  0x7cd,
  0x150b102fe
]

def labelsBlock82 : Array Nat := #[
  0x190b102fe,
  0x7c9,
  0x7102fe,
  0x6012ea,
  0x7012fa,
  0x7fd,
  0x11d941480202fe,
  0x541480202fe,
  0x641480202fe,
  0x1480202fe,
  0x765504202fe,
  0x815,
  0x1504202fe,
  0x6412da,
  0x1904202fe,
  0x7e5
]

def labelsBlock83 : Array Nat := #[
  0x7e9,
  0x7f1,
  0x801,
  0x4202fe,
  0x46550520306,
  0x465505202fe,
  0x829,
  0x1505202fe,
  0x1905202fe,
  0x825,
  0x1c562030a,
  0x6142fa,
  0x76550620306,
  0x765506202fe,
  0x841,
  0x1506202fe
]

def labelsBlock84 : Array Nat := #[
  0x1906202fe,
  0x83d,
  0x1246,
  0x6202fe,
  0x1c572030a,
  0x6042ee,
  0x76550720306,
  0x125a,
  0x765507202fe,
  0x85d,
  0x1507202fe,
  0x1907202fe,
  0x859,
  0x7202fe,
  0x756085402fe,
  0x115d21085402fe
]

def labelsBlock85 : Array Nat := #[
  0x521085402fe,
  0x871,
  0x1085402fe,
  0x45648540306,
  0x456485402fe,
  0x881,
  0x1485402fe,
  0x1c162130a,
  0x6042fa,
  0x75688540306,
  0x756885402fe,
  0x88d,
  0x1885402fe,
  0x1c172130a,
  0x6042f6,
  0x756c8540306
]

def labelsBlock86 : Array Nat := #[
  0x756c85402fe,
  0x89d,
  0x1c85402fe,
  0x8a9,
  0x8ad,
  0x521086402fe,
  0x6402da,
  0x1086402fe,
  0x1486402fe,
  0x1886402fe,
  0x1c86402fe,
  0x8b5,
  0x8b9,
  0x6402fe,
  0x6012f2,
  0x6012fa
]

def labelsBlock87 : Array Nat := #[
  0x6012f6,
  0x8ed,
  0x1484212fe,
  0x8d9,
  0x8dd,
  0x8e5,
  0x8f5,
  0x4212fe,
  0x901,
  0x909,
  0x125e,
  0x6212fe,
  0x911,
  0x7212fe,
  0x919,
  0x91d
]

def labelsBlock88 : Array Nat := #[
  0x925,
  0x929,
  0x6412fe,
  0x931,
  0x935,
  0x93d,
  0x941,
  0x6422fe,
  0x791,
  0x7a5,
  0x7c1,
  0x7dd,
  0x821,
  0x835,
  0x851,
  0x86d
]

def labelsBlock89 : Array Nat := #[
  0x8b1,
  0x8d1,
  0x8fd,
  0x905,
  0x90d,
  0x915,
  0x921,
  0x92d,
  0x939,
  0x945,
  0x1,
  0x5,
  0x9,
  0xd,
  0x11,
  0x15
]

def labelsBlock90 : Array Nat := #[
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
  0x49,
  0x4d,
  0x51,
  0x55
]

def labelsBlock91 : Array Nat := #[
  0x59,
  0x5d,
  0x61,
  0x65,
  0x69,
  0x6d,
  0x71,
  0x75,
  0x79,
  0x7d,
  0x81,
  0x85,
  0x89,
  0x8d,
  0x91,
  0x95
]

def labelsBlock92 : Array Nat := #[
  0x99,
  0x9d,
  0xa1,
  0xa5,
  0xa9,
  0xad,
  0xb1,
  0xb5,
  0xb9,
  0xbd,
  0xc1,
  0xc5,
  0xc9,
  0xcd,
  0xd1,
  0xd5
]

def labelsBlock93 : Array Nat := #[
  0xd9,
  0xdd,
  0xe1,
  0xe5,
  0xe9,
  0xed,
  0xf1,
  0xf5,
  0xf9,
  0xfd,
  0x101,
  0x105,
  0x109,
  0x10d,
  0x111,
  0x115
]

def labelsBlock94 : Array Nat := #[
  0x119,
  0x11d,
  0x121,
  0x125,
  0x129,
  0x12d,
  0x131,
  0x135,
  0x139,
  0x13d,
  0x141,
  0x145,
  0x149,
  0x14d,
  0x151,
  0x155
]

def labelsBlock95 : Array Nat := #[
  0x159,
  0x15d,
  0x161,
  0x165,
  0x169,
  0x16d,
  0x171,
  0x175,
  0x179,
  0x17d,
  0x181,
  0x185,
  0x1c1,
  0x1c5,
  0x201,
  0x23d
]

def labelsBlock96 : Array Nat := #[
  0x10c6,
  0x279,
  0x27d,
  0x2b9,
  0x2f5,
  0x2f9,
  0x335,
  0x11a6,
  0x369,
  0x39d,
  0x11d2,
  0x3d1,
  0x405,
  0x439,
  0x46d,
  0x4a1
]

def labelsBlock97 : Array Nat := #[
  0x4a5,
  0x4d9,
  0x50d,
  0x541,
  0x5ed,
  0x3a10,
  0x3910,
  0x60d,
  0x611,
  0x615,
  0x619,
  0x65d,
  0x705,
  0x749,
  0x949
]

def labelsGet (i : Nat) : Nat :=
  if i < 784 then
    if i < 384 then
      if i < 192 then
        if i < 96 then
          if i < 48 then
            if i < 16 then
              labelsBlock0.getD (i-0) 3
            else
              if i < 32 then
                labelsBlock1.getD (i-16) 3
              else
                labelsBlock2.getD (i-32) 3
          else
            if i < 64 then
              labelsBlock3.getD (i-48) 3
            else
              if i < 80 then
                labelsBlock4.getD (i-64) 3
              else
                labelsBlock5.getD (i-80) 3
        else
          if i < 144 then
            if i < 112 then
              labelsBlock6.getD (i-96) 3
            else
              if i < 128 then
                labelsBlock7.getD (i-112) 3
              else
                labelsBlock8.getD (i-128) 3
          else
            if i < 160 then
              labelsBlock9.getD (i-144) 3
            else
              if i < 176 then
                labelsBlock10.getD (i-160) 3
              else
                labelsBlock11.getD (i-176) 3
      else
        if i < 288 then
          if i < 240 then
            if i < 208 then
              labelsBlock12.getD (i-192) 3
            else
              if i < 224 then
                labelsBlock13.getD (i-208) 3
              else
                labelsBlock14.getD (i-224) 3
          else
            if i < 256 then
              labelsBlock15.getD (i-240) 3
            else
              if i < 272 then
                labelsBlock16.getD (i-256) 3
              else
                labelsBlock17.getD (i-272) 3
        else
          if i < 336 then
            if i < 304 then
              labelsBlock18.getD (i-288) 3
            else
              if i < 320 then
                labelsBlock19.getD (i-304) 3
              else
                labelsBlock20.getD (i-320) 3
          else
            if i < 352 then
              labelsBlock21.getD (i-336) 3
            else
              if i < 368 then
                labelsBlock22.getD (i-352) 3
              else
                labelsBlock23.getD (i-368) 3
    else
      if i < 576 then
        if i < 480 then
          if i < 432 then
            if i < 400 then
              labelsBlock24.getD (i-384) 3
            else
              if i < 416 then
                labelsBlock25.getD (i-400) 3
              else
                labelsBlock26.getD (i-416) 3
          else
            if i < 448 then
              labelsBlock27.getD (i-432) 3
            else
              if i < 464 then
                labelsBlock28.getD (i-448) 3
              else
                labelsBlock29.getD (i-464) 3
        else
          if i < 528 then
            if i < 496 then
              labelsBlock30.getD (i-480) 3
            else
              if i < 512 then
                labelsBlock31.getD (i-496) 3
              else
                labelsBlock32.getD (i-512) 3
          else
            if i < 544 then
              labelsBlock33.getD (i-528) 3
            else
              if i < 560 then
                labelsBlock34.getD (i-544) 3
              else
                labelsBlock35.getD (i-560) 3
      else
        if i < 672 then
          if i < 624 then
            if i < 592 then
              labelsBlock36.getD (i-576) 3
            else
              if i < 608 then
                labelsBlock37.getD (i-592) 3
              else
                labelsBlock38.getD (i-608) 3
          else
            if i < 640 then
              labelsBlock39.getD (i-624) 3
            else
              if i < 656 then
                labelsBlock40.getD (i-640) 3
              else
                labelsBlock41.getD (i-656) 3
        else
          if i < 720 then
            if i < 688 then
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
                labelsBlock48.getD (i-768) 3
  else
    if i < 1168 then
      if i < 976 then
        if i < 880 then
          if i < 832 then
            if i < 800 then
              labelsBlock49.getD (i-784) 3
            else
              if i < 816 then
                labelsBlock50.getD (i-800) 3
              else
                labelsBlock51.getD (i-816) 3
          else
            if i < 848 then
              labelsBlock52.getD (i-832) 3
            else
              if i < 864 then
                labelsBlock53.getD (i-848) 3
              else
                labelsBlock54.getD (i-864) 3
        else
          if i < 928 then
            if i < 896 then
              labelsBlock55.getD (i-880) 3
            else
              if i < 912 then
                labelsBlock56.getD (i-896) 3
              else
                labelsBlock57.getD (i-912) 3
          else
            if i < 944 then
              labelsBlock58.getD (i-928) 3
            else
              if i < 960 then
                labelsBlock59.getD (i-944) 3
              else
                labelsBlock60.getD (i-960) 3
      else
        if i < 1072 then
          if i < 1024 then
            if i < 992 then
              labelsBlock61.getD (i-976) 3
            else
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
        else
          if i < 1120 then
            if i < 1088 then
              labelsBlock67.getD (i-1072) 3
            else
              if i < 1104 then
                labelsBlock68.getD (i-1088) 3
              else
                labelsBlock69.getD (i-1104) 3
          else
            if i < 1136 then
              labelsBlock70.getD (i-1120) 3
            else
              if i < 1152 then
                labelsBlock71.getD (i-1136) 3
              else
                labelsBlock72.getD (i-1152) 3
    else
      if i < 1360 then
        if i < 1264 then
          if i < 1216 then
            if i < 1184 then
              labelsBlock73.getD (i-1168) 3
            else
              if i < 1200 then
                labelsBlock74.getD (i-1184) 3
              else
                labelsBlock75.getD (i-1200) 3
          else
            if i < 1232 then
              labelsBlock76.getD (i-1216) 3
            else
              if i < 1248 then
                labelsBlock77.getD (i-1232) 3
              else
                labelsBlock78.getD (i-1248) 3
        else
          if i < 1312 then
            if i < 1280 then
              labelsBlock79.getD (i-1264) 3
            else
              if i < 1296 then
                labelsBlock80.getD (i-1280) 3
              else
                labelsBlock81.getD (i-1296) 3
          else
            if i < 1328 then
              labelsBlock82.getD (i-1312) 3
            else
              if i < 1344 then
                labelsBlock83.getD (i-1328) 3
              else
                labelsBlock84.getD (i-1344) 3
      else
        if i < 1456 then
          if i < 1408 then
            if i < 1376 then
              labelsBlock85.getD (i-1360) 3
            else
              if i < 1392 then
                labelsBlock86.getD (i-1376) 3
              else
                labelsBlock87.getD (i-1392) 3
          else
            if i < 1424 then
              labelsBlock88.getD (i-1408) 3
            else
              if i < 1440 then
                labelsBlock89.getD (i-1424) 3
              else
                labelsBlock90.getD (i-1440) 3
        else
          if i < 1504 then
            if i < 1472 then
              labelsBlock91.getD (i-1456) 3
            else
              if i < 1488 then
                labelsBlock92.getD (i-1472) 3
              else
                labelsBlock93.getD (i-1488) 3
          else
            if i < 1536 then
              if i < 1520 then
                labelsBlock94.getD (i-1504) 3
              else
                labelsBlock95.getD (i-1520) 3
            else
              if i < 1552 then
                labelsBlock96.getD (i-1536) 3
              else
                labelsBlock97.getD (i-1552) 3

def decodeHints (enc i : Nat) := labelsGet ((enc >>> (i * 11)) % 2048)

def localHints (stride dict enc i : Nat) : Nat :=
  let q := (enc >>> (stride*i)) % (2^stride)
  labelsGet ((dict >>> (11*q)) % 2048)

def viewsBlock0 : Array View := #[
  ⟨0x88008800000,⟨23,by decide⟩,0x8008000000,[ew56,ew57],2,decodeHints 0xb341b82486e⟩,
  ⟨0x208020800000,⟨23,by decide⟩,0x8020000000,[ew63,ew64],2,decodeHints 0xb361bc2486f⟩,
  ⟨0x408040800000,⟨23,by decide⟩,0x8040000000,[ew70,ew71],2,decodeHints 0xb381c024870⟩,
  ⟨0x208208000000000,⟨39,by decide⟩,0x8200000000000,[ew101,ew108],2,decodeHints 0xb3a590d6964⟩,
  ⟨0x220088000000000,⟨39,by decide⟩,0x20080000000000,[ew99,ew112],2,decodeHints 0xb3c594d7165⟩,
  ⟨0x408408000000000,⟨39,by decide⟩,0x8400000000000,[ew130,ew137],2,decodeHints 0xb3e598d6966⟩,
  ⟨0x440088000000000,⟨39,by decide⟩,0x40080000000000,[ew128,ew141],2,decodeHints 0xb40594d7965⟩,
  ⟨0x1020408000000000,⟨39,by decide⟩,0x20400000000000,[ew212,ew218],2,decodeHints 0xb42598d7166⟩,
  ⟨0x1040208000000000,⟨39,by decide⟩,0x40200000000000,[ew210,ew221],2,decodeHints 0xb44590d7964⟩,
  ⟨0xaa00aa00,⟨9,by decide⟩,0xa8008000,[ew20,ew23,ew26],3,decodeHints 0xb46014018300040b017830⟩,
  ⟨0xcc00cc00,⟨10,by decide⟩,0xc8008000,[ew20,ew31,ew34],3,decodeHints 0xb48018018320040b828032⟩,
  ⟨0xf000f000,⟨12,by decide⟩,0xe0008000,[ew23,ew31,ew39],3,decodeHints 0xb4a0180283301417431833⟩,
  ⟨0xff000000,⟨24,by decide⟩,0xe8000000,[ew26,ew34,ew39],3,decodeHints 0xb4c0200384201211825042⟩,
  ⟨0xaaaa000000,⟨25,by decide⟩,0x80a8000000,[ew48,ew50,ew51],3,localHints 2 0xb4e56404807 0xc484⟩,
  ⟨0xcccc000000,⟨26,by decide⟩,0x80c8000000,[ew48,ew53,ew54],3,localHints 2 0xb5056407008 0xc484⟩,
  ⟨0xf0f0000000,⟨28,by decide⟩,0x80e0000000,[ew50,ew53,ew55],3,localHints 2 0xb525ec0780c 0xc484⟩
]

def viewsBlock1 : Array View := #[
  ⟨0xaa00aa00000,⟨21,by decide⟩,0x8008000000,[ew58,ew59,ew60],3,decodeHints 0x5dc01c370f9092a9c370f9⟩,
  ⟨0xcc00cc00000,⟨22,by decide⟩,0x8008000000,[ew58,ew61,ew62],3,decodeHints 0x5dc020370fa092aac370fa⟩,
  ⟨0x228822880000,⟨19,by decide⟩,0x8020000000,[ew65,ew66,ew67],3,decodeHints 0x5de024378fb09264c378fb⟩,
  ⟨0x30c030c00000,⟨22,by decide⟩,0x8020000000,[ew65,ew68,ew69],3,decodeHints 0x5de030378fc092aac378fc⟩,
  ⟨0x448844880000,⟨19,by decide⟩,0x8040000000,[ew72,ew73,ew74],3,decodeHints 0x5e0038380fd09264c380fd⟩,
  ⟨0x50a050a00000,⟨21,by decide⟩,0x8040000000,[ew72,ew75,ew76],3,decodeHints 0x5e003c380fe092a9c380fe⟩,
  ⟨0xaa0000aa000000,⟨25,by decide⟩,0x800000a8000000,[ew87,ew90,ew92],3,localHints 2 0xb5456804807 0xc484⟩,
  ⟨0xcc0000cc000000,⟨26,by decide⟩,0x800000c8000000,[ew87,ew94,ew96],3,localHints 2 0xb5656807008 0xc484⟩,
  ⟨0xf00000f0000000,⟨28,by decide⟩,0x800000e0000000,[ew90,ew94,ew97],3,localHints 2 0xb585f00780c 0xc484⟩,
  ⟨0x202808002028080,⟨7,by decide⟩,0x200808000008000,[ew103,ew104,ew105],3,localHints 2 0xb5a5f400800 0xc844⟩,
  ⟨0x208208002082080,⟨7,by decide⟩,0x200008000000000,[ew102,ew109,ew110],3,localHints 2 0x4d81584c001 0xd900⟩,
  ⟨0x220088002200880,⟨7,by decide⟩,0x200008000000000,[ew100,ew113,ew114],3,localHints 2 0x79c59c57001 0xd900⟩,
  ⟨0x3000300c000c000,⟨14,by decide⟩,0x2000000c0008000,[ew98,ew117,ew118],3,localHints 2 0xb5c7700a006 0xc484⟩,
  ⟨0x30c30c000000000,⟨38,by decide⟩,0x200008000000000,[ew110,ew119,ew124],3,localHints 2 0x4d81584c011 0xc484⟩,
  ⟨0x404808004048080,⟨7,by decide⟩,0x400808000008000,[ew132,ew133,ew134],3,localHints 2 0xb5e5f800800 0xc844⟩,
  ⟨0x408408004084080,⟨7,by decide⟩,0x400008000000000,[ew131,ew138,ew139],3,localHints 2 0x4da1cc4c801 0xd900⟩
]

def viewsBlock2 : Array View := #[
  ⟨0x440088004400880,⟨7,by decide⟩,0x400008000000000,[ew129,ew142,ew143],3,localHints 2 0x79e5a057001 0xd900⟩,
  ⟨0x5000500a000a000,⟨13,by decide⟩,0x4000000a0008000,[ew127,ew146,ew147],3,localHints 2 0xb6077405005 0xc484⟩,
  ⟨0x50a50a000000000,⟨37,by decide⟩,0x400008000000000,[ew139,ew148,ew153],3,localHints 2 0x4da1cc4c810 0xc484⟩,
  ⟨0x880088008800880,⟨7,by decide⟩,0x880008008000000,[ew159,ew162,ew163],2,decodeHints 0x5dc1b80106700200400867⟩,
  ⟨0xa0000a00a0000a0,⟨5,by decide⟩,0xa00008008000000,[ew158,ew166,ew168],3,decodeHints 0xb6201c3391e0020d48f91e⟩,
  ⟨0xa0aa0a000000000,⟨37,by decide⟩,0xa00808000000000,[ew160,ew171,ew173],2,decodeHints 0x4d8040100100ac0404b010⟩,
  ⟨0xaa000000aa00000,⟨21,by decide⟩,0xa80000008000000,[ew162,ew166,ew178],3,decodeHints 0xb6401c370f90361dcbf8f9⟩,
  ⟨0xaa00aa000000000,⟨37,by decide⟩,0xa80008000000000,[ew163,ew169,ew178],2,decodeHints 0x79c040570100420404b010⟩,
  ⟨0xc0000c00c0000c0,⟨6,by decide⟩,0xc00008008000000,[ew158,ew182,ew184],3,decodeHints 0xb66020339210020dc99121⟩,
  ⟨0xc0cc0c000000000,⟨38,by decide⟩,0xc00808000000000,[ew160,ew187,ew189],2,decodeHints 0x4da044228110e60445f811⟩,
  ⟨0xcc000000cc00000,⟨22,by decide⟩,0xc80000008000000,[ew162,ew182,ew194],3,decodeHints 0xb68020370fa0361e0c00fa⟩,
  ⟨0xcc00cc000000000,⟨38,by decide⟩,0xc80008000000000,[ew163,ew185,ew194],2,decodeHints 0x79e0445701108e0445f811⟩,
  ⟨0xf0000000000f000,⟨12,by decide⟩,0xe00000000008000,[ew165,ew181,ew198],3,decodeHints 0xb6a0180283326889513033⟩,
  ⟨0xf0000000f000000,⟨24,by decide⟩,0xe00000008000000,[ew166,ew182,ew198],3,decodeHints 0xb6c0200384200816830042⟩,
  ⟨0xf0000f000000000,⟨36,by decide⟩,0xe00008000000000,[ew168,ew184,ew198],3,decodeHints 0xb6e0440807612c528a5876⟩,
  ⟨0xf00f00000000000,⟨44,by decide⟩,0xe00800000000000,[ew171,ew187,ew198],3,decodeHints 0xb70144278d90ac530a68d9⟩
]

def viewsBlock3 : Array View := #[
  ⟨0xff0000000000000,⟨52,by decide⟩,0xe80000000000000,[ew178,ew194,ew198],3,decodeHints 0xb720d0168ac2409e13c8ac⟩,
  ⟨0x1010808010108080,⟨7,by decide⟩,0x1000808000008000,[ew214,ew215,ew216],3,localHints 2 0xb7469000800 0xc844⟩,
  ⟨0x1020408010204080,⟨7,by decide⟩,0x1000008000000000,[ew213,ew219,ew220],3,localHints 2 0x5e24944c801 0xd900⟩,
  ⟨0x1040208010402080,⟨7,by decide⟩,0x1000008000000000,[ew211,ew222,ew223],3,localHints 2 0x5e44a44c001 0xd900⟩,
  ⟨0x1100110088008800,⟨11,by decide⟩,0x1000000088008000,[ew209,ew226,ew227],3,localHints 2 0xb7677801003 0xc484⟩,
  ⟨0x2080208020802080,⟨7,by decide⟩,0x2080008020000000,[ew232,ew235,ew236],2,decodeHints 0x5de1bc0506900200400869⟩,
  ⟨0x2200008822000088,⟨3,by decide⟩,0x2200008020000000,[ew231,ew239,ew241],3,decodeHints 0xb78024349220020e4a7122⟩,
  ⟨0x2288000022880000,⟨19,by decide⟩,0x2280000020000000,[ew235,ew239,ew247],3,decodeHints 0xb7a024378fb0361e4c08fb⟩,
  ⟨0x2288228800000000,⟨35,by decide⟩,0x2280008000000000,[ew236,ew242,ew247],2,decodeHints 0x4d80484c01204204882812⟩,
  ⟨0x300000c0300000c0,⟨6,by decide⟩,0x3000008020000000,[ew231,ew252,ew254],3,decodeHints 0xb7c030349240020dc9a924⟩,
  ⟨0x3030c0c000000000,⟨38,by decide⟩,0x3000808000000000,[ew233,ew257,ew259],2,decodeHints 0x5e20442f01124a04483011⟩,
  ⟨0x30c0000030c00000,⟨22,by decide⟩,0x3080000020000000,[ew235,ew252,ew263],3,decodeHints 0xb7e030378fc0361e0c10fc⟩,
  ⟨0x30c030c000000000,⟨38,by decide⟩,0x3080008000000000,[ew236,ew255,ew263],2,decodeHints 0x5e40444c0110a404483011⟩,
  ⟨0x330000000000cc00,⟨10,by decide⟩,0x3200000000008000,[ew238,ew251,ew267],3,decodeHints 0xb800180183239e9e93d832⟩,
  ⟨0x3300000033000000,⟨24,by decide⟩,0x3200000020000000,[ew239,ew252,ew267],3,decodeHints 0xb820300484600816832046⟩,
  ⟨0x330000cc00000000,⟨34,by decide⟩,0x3200008000000000,[ew241,ew254,ew267],3,decodeHints 0xb84044090a420a9f13e8a4⟩
]

def viewsBlock4 : Array View := #[
  ⟨0x3300cc0000000000,⟨42,by decide⟩,0x3200800000000000,[ew244,ew257,ew267],3,decodeHints 0xb86144240d32ce9f93f8d3⟩,
  ⟨0x33cc000000000000,⟨50,by decide⟩,0x3280000000000000,[ew247,ew263,ew267],3,decodeHints 0xb880d01509f246a014089f⟩,
  ⟨0x4080408040804080,⟨7,by decide⟩,0x4080008040000000,[ew277,ew280,ew281],2,decodeHints 0x5e01c00a06a0020040086a⟩,
  ⟨0x4400008844000088,⟨3,by decide⟩,0x4400008040000000,[ew276,ew284,ew286],3,decodeHints 0xb8a038351260020e4a7926⟩,
  ⟨0x4488000044880000,⟨19,by decide⟩,0x4480000040000000,[ew280,ew284,ew292],3,decodeHints 0xb8c038380fd0361e4c18fd⟩,
  ⟨0x4488448800000000,⟨35,by decide⟩,0x4480008000000000,[ew281,ew287,ew292],2,decodeHints 0x4da0484c81208e04883812⟩,
  ⟨0x500000a0500000a0,⟨5,by decide⟩,0x5000008040000000,[ew276,ew297,ew299],3,decodeHints 0xb8e03c351280020d49b928⟩,
  ⟨0x5050a0a000000000,⟨37,by decide⟩,0x5000808000000000,[ew278,ew302,ew304],2,decodeHints 0x5e40402f01025204084010⟩,
  ⟨0x50a0000050a00000,⟨21,by decide⟩,0x5080000040000000,[ew280,ew297,ew308],3,decodeHints 0xb9003c380fe0361dcc20fe⟩,
  ⟨0x50a050a000000000,⟨37,by decide⟩,0x5080008000000000,[ew281,ew300,ew308],2,decodeHints 0x5e20404c8100a404084010⟩,
  ⟨0x550000000000aa00,⟨9,by decide⟩,0x5400000000008000,[ew283,ew296,ew312],3,decodeHints 0xb92014018303a2a0941830⟩,
  ⟨0x5500000055000000,⟨24,by decide⟩,0x5400000040000000,[ew284,ew297,ew312],3,decodeHints 0xb9403c0704a01a1803204a⟩,
  ⟨0x550000aa00000000,⟨33,by decide⟩,0x5400008000000000,[ew286,ew299,ew312],3,decodeHints 0xb96040090a520ea11428a5⟩,
  ⟨0x5500aa0000000000,⟨41,by decide⟩,0x5400800000000000,[ew289,ew302,ew312],3,decodeHints 0xb9813c240d42d0a19438d4⟩,
  ⟨0x55aa000000000000,⟨49,by decide⟩,0x5480000000000000,[ew292,ew308,ew312],3,decodeHints 0xb9a0b4150a024ea21448a0⟩,
  ⟨0x8200008282000082,⟨1,by decide⟩,0x8200008080000000,[ew326,ew338,ew339],3,decodeHints 0xb9c5a465a270023c040a27⟩
]

def viewsBlock5 : Array View := #[
  ⟨0x8282000000008282,⟨1,by decide⟩,0x8280000000008000,[ew330,ew336,ew342],3,decodeHints 0xb9e0c0000da0868a0408da⟩,
  ⟨0x8282000041410000,⟨16,by decide⟩,0x8280000040000000,[ew333,ew337,ew342],3,decodeHints 0xba01280d16a0f0648d896a⟩,
  ⟨0x8282000082820000,⟨17,by decide⟩,0x8280000080000000,[ew334,ew338,ew342],3,decodeHints 0xba25a4662290366143ea29⟩,
  ⟨0x8400008484000084,⟨2,by decide⟩,0x8400008080000000,[ew326,ew348,ew349],3,decodeHints 0xba45ac65a2a0023c456a2a⟩,
  ⟨0x8484000000008484,⟨2,by decide⟩,0x8480000000008000,[ew330,ew346,ew352],3,decodeHints 0xba60c8000db0868ac568db⟩,
  ⟨0x8484000021210000,⟨16,by decide⟩,0x8480000020000000,[ew332,ew347,ew352],3,decodeHints 0xba81180996c0ee648d916c⟩,
  ⟨0x8484000084840000,⟨18,by decide⟩,0x8480000080000000,[ew334,ew348,ew352],3,decodeHints 0xbaa5ac6622c03661858a2c⟩,
  ⟨0x8800008822000022,⟨1,by decide⟩,0x8800008020000000,[ew324,ew357,ew359],3,decodeHints 0xbac0241c08506a3c145085⟩,
  ⟨0x8800008844000044,⟨2,by decide⟩,0x8800008040000000,[ew325,ew358,ew359],3,decodeHints 0xbae038258b206e3c5458b2⟩,
  ⟨0x8800880022002200,⟨9,by decide⟩,0x8800800020000000,[ew328,ew357,ew361],3,decodeHints 0xbb00240502f14c77cf002f⟩,
  ⟨0x8800880044004400,⟨10,by decide⟩,0x8800800040000000,[ew329,ew358,ew361],3,decodeHints 0xbb20380a05014e78516850⟩,
  ⟨0x8888000000008888,⟨3,by decide⟩,0x8880000000008000,[ew330,ew356,ew363],3,decodeHints 0xbb400c0003f086830e903f⟩,
  ⟨0x8888000022220000,⟨17,by decide⟩,0x8880000020000000,[ew332,ew357,ew363],3,decodeHints 0xbb6024098650ee61546065⟩,
  ⟨0x8888000044440000,⟨18,by decide⟩,0x8880000040000000,[ew333,ew358,ew363],3,decodeHints 0xbb80380d0820f061946882⟩,
  ⟨0x9000009090000090,⟨4,by decide⟩,0x9000008080000000,[ew326,ew372,ew373],3,decodeHints 0xbba5b465a2e00237472a2e⟩,
  ⟨0x9090000009090000,⟨16,by decide⟩,0x9080000008000000,[ew331,ew371,ew376],3,decodeHints 0xbbc108059390f2648d9939⟩
]

def viewsBlock6 : Array View := #[
  ⟨0x9090000090900000,⟨20,by decide⟩,0x9080000080000000,[ew334,ew372,ew376],3,decodeHints 0xbbe5b46622f03661c8022f⟩,
  ⟨0x9900000000009900,⟨8,by decide⟩,0x9800000000008000,[ew356,ew370,ew380],3,decodeHints 0xbc00cc0188c2b6a386208c⟩,
  ⟨0x9900009900000000,⟨32,by decide⟩,0x9800008000000000,[ew359,ew373,ew380],3,decodeHints 0xbc21d8091101fea3c79110⟩,
  ⟨0x9900990000000000,⟨40,by decide⟩,0x9800800000000000,[ew361,ew374,ew380],3,decodeHints 0xbc4364241501c8a4081150⟩,
  ⟨0x9999000000000000,⟨48,by decide⟩,0x9880000000000000,[ew363,ew376,ew380],3,decodeHints 0xbc62b015151190a4481951⟩,
  ⟨0xa00000a00a00000a,⟨1,by decide⟩,0xa000008008000000,[ew323,ew387,ew389],3,decodeHints 0xbc801c0c0830723c149083⟩,
  ⟨0xa00000a050000050,⟨4,by decide⟩,0xa000008040000000,[ew325,ew388,ew389],3,decodeHints 0xbca03c258c006e375498c0⟩,
  ⟨0xa000a0000a000a00,⟨9,by decide⟩,0xa000800008000000,[ew327,ew387,ew391],3,decodeHints 0xbcc01c0102c14277cf102c⟩,
  ⟨0xa000a00050005000,⟨12,by decide⟩,0xa000800040000000,[ew329,ew388,ew391],3,decodeHints 0xbce03c0a06314e78d18063⟩,
  ⟨0xa0a000000000a0a0,⟨5,by decide⟩,0xa080000000008000,[ew330,ew386,ew393],3,decodeHints 0xbd00140003c0868c4e983c⟩,
  ⟨0xa0a000000a0a0000,⟨17,by decide⟩,0xa080000008000000,[ew331,ew387,ew393],3,decodeHints 0xbd201c058610f26154a061⟩,
  ⟨0xa0a0000050500000,⟨20,by decide⟩,0xa080000040000000,[ew333,ew388,ew393],3,decodeHints 0xbd403c0d0940f061d4a894⟩,
  ⟨0xa50000000000a500,⟨8,by decide⟩,0xa400000000008000,[ew346,ew386,ew399],3,decodeHints 0xbd60141908c0a830d4b08c⟩,
  ⟨0xa50000a500000000,⟨32,by decide⟩,0xa400008000000000,[ew349,ew389,ew399],3,decodeHints 0xbd8040521100e837d4b910⟩,
  ⟨0xa500a50000000000,⟨40,by decide⟩,0xa400800000000000,[ew350,ew391,ew399],3,decodeHints 0xbda13c6995008e3cd4c150⟩,
  ⟨0xa5a5000000000000,⟨48,by decide⟩,0xa480000000000000,[ew352,ew393,ew399],3,decodeHints 0xbdc0b44f95108a3354c951⟩
]

def viewsBlock7 : Array View := #[
  ⟨0xc00000c00c00000c,⟨2,by decide⟩,0xc000008008000000,[ew323,ew431,ew433],3,decodeHints 0xbde0200c0840723c54d084⟩,
  ⟨0xc00000c030000030,⟨4,by decide⟩,0xc000008020000000,[ew324,ew432,ew433],3,decodeHints 0xbe00301c0b906a3754d8b9⟩,
  ⟨0xc000c0000c000c00,⟨10,by decide⟩,0xc000800008000000,[ew327,ew431,ew435],3,decodeHints 0xbe20200102e142784f202e⟩,
  ⟨0xc000c00030003000,⟨12,by decide⟩,0xc000800020000000,[ew328,ew432,ew435],3,decodeHints 0xbe40300505d14c78d1905d⟩,
  ⟨0xc0c000000000c0c0,⟨6,by decide⟩,0xc080000000008000,[ew330,ew430,ew437],3,decodeHints 0xbe60180003d0868ccea03d⟩,
  ⟨0xc0c000000c0c0000,⟨18,by decide⟩,0xc080000008000000,[ew331,ew431,ew437],3,decodeHints 0xbe8020058620f26194e062⟩,
  ⟨0xc0c0000030300000,⟨20,by decide⟩,0xc080000020000000,[ew332,ew432,ew437],3,decodeHints 0xbea030098800ee61d4e880⟩,
  ⟨0xc30000000000c300,⟨8,by decide⟩,0xc200000000008000,[ew336,ew430,ew442],3,decodeHints 0xbec0181808c0623094f08c⟩,
  ⟨0xc30000c300000000,⟨32,by decide⟩,0xc200008000000000,[ew339,ew433,ew442],3,decodeHints 0xbee044529100b03714f910⟩,
  ⟨0xc300c30000000000,⟨40,by decide⟩,0xc200800000000000,[ew340,ew435,ew442],3,decodeHints 0xbf01446a15004239950150⟩,
  ⟨0xc3c3000000000000,⟨48,by decide⟩,0xc280000000000000,[ew342,ew437,ew442],3,decodeHints 0xbf20d05015104032550951⟩,
  ⟨0xaaaaaaaa,⟨1,by decide⟩,0xa8008000,[ew22,ew25,ew28,ew29],4,decodeHints 0x82014018300000f01f8da0040b01783003020c428da⟩,
  ⟨0xcccccccc,⟨2,by decide⟩,0xc8008000,[ew22,ew33,ew36,ew37],4,decodeHints 0xcc018018320000f41f8db0040b828032030210590db⟩,
  ⟨0xf0f0f0f0,⟨4,by decide⟩,0xe0008000,[ew25,ew33,ew41,ew42],4,decodeHints 0x138018028330000f41e0e1014174318330702e4600e1⟩,
  ⟨0xff0000ff,⟨0,by decide⟩,0xe8000000,[ew27,ew35,ew40,ew44],4,decodeHints 0x5602003842012118250420302104194910a5e8bc949⟩,
  ⟨0xff00ff00,⟨8,by decide⟩,0xe8008000,[ew28,ew36,ew41,ew44],5,decodeHints 0xbf4018028330060c81808c0040b8160d505e3586b88c⟩
]

def viewsBlock8 : Array View := #[
  ⟨0xffff0000,⟨16,by decide⟩,0xe8000000,[ew29,ew37,ew42,ew44],4,decodeHints 0x560200384201211825042016188309390ca5b0b5139⟩,
  ⟨0x303c0c00303c0c0,⟨6,by decide⟩,0x200808000008000,[ew106,ew121,ew122,ew123],4,localHints 3 0x7bcbe8060020dc0003d 0xd08b08688688⟩,
  ⟨0x30c30c0030c30c0,⟨6,by decide⟩,0x200008000000000,[ew111,ew120,ew125,ew126],4,localHints 3 0x8e05613004400837 0xa9a89a208208⟩,
  ⟨0x505a0a00505a0a0,⟨5,by decide⟩,0x400808000008000,[ew135,ew150,ew151,ew152],4,localHints 3 0x97cbf0050020d40003c 0xd08b08688688⟩,
  ⟨0x50a50a0050a50a0,⟨5,by decide⟩,0x400008000000000,[ew140,ew149,ew154,ew155],4,localHints 3 0xaf87313204000835 0xa9a89a208208⟩,
  ⟨0xa0aa0a00a0aa0a0,⟨5,by decide⟩,0xa00808008008000,[ew161,ew172,ew174,ew176],4,localHints 3 0xbf6158028000020d48f83c 0xf60d606a0688⟩,
  ⟨0xaa00aa00aa00aa0,⟨5,by decide⟩,0xa80008008000000,[ew164,ew170,ew179,ew180],5,decodeHints 0xbf801c370f90040b03391e0020d4008350020d48f91e⟩,
  ⟨0xc0cc0c00c0cc0c0,⟨6,by decide⟩,0xc00808008008000,[ew161,ew188,ew190,ew192],4,localHints 3 0xbfa1cc030000020dc9903d 0xf60d606a0688⟩,
  ⟨0xcc00cc00cc00cc0,⟨6,by decide⟩,0xc80008008000000,[ew164,ew186,ew195,ew196],5,decodeHints 0xbfc020370fa0040b8339210020dc008370020dc99121⟩,
  ⟨0xf00000f0f00000f,⟨0,by decide⟩,0xe00000008000000,[ew167,ew183,ew199,ew200],4,decodeHints 0x76020038420302104194900816830042102768ec949⟩,
  ⟨0xf000f000f000f00,⟨8,by decide⟩,0xe00000008000000,[ew170,ew186,ew199,ew201],4,decodeHints 0x76020038420040b8160d500816830042062308618d5⟩,
  ⟨0xf00f0000f00f000,⟨12,by decide⟩,0xe00800008008000,[ew172,ew188,ew199,ew203],4,decodeHints 0x76018028330ac018028330080180283326889513033⟩,
  ⟨0xf0f00000f0f0000,⟨16,by decide⟩,0xe00000008000000,[ew174,ew190,ew199,ew205],4,decodeHints 0x760200384201618830939008168300420fa6c4d9139⟩,
  ⟨0xf0ff0f000000000,⟨36,by decide⟩,0xe00808000000000,[ew176,ew192,ew203,ew205],5,decodeHints 0xbfe04408076040044080760ac0440807612c528a5876⟩,
  ⟨0x1111888811118888,⟨3,by decide⟩,0x1000808000008000,[ew217,ew228,ew229,ew230],4,localHints 3 0x1800d20030020e40003f 0xd08b08688688⟩,
  ⟨0x2288228822882288,⟨3,by decide⟩,0x2280008020000000,[ew237,ew243,ew248,ew249],5,decodeHints 0xc02024378fb0140bc349220020e4008390020e4a7122⟩
]

def viewsBlock9 : Array View := #[
  ⟨0x3030c0c03030c0c0,⟨6,by decide⟩,0x3000808020008000,[ew234,ew258,ew260,ew262],4,localHints 3 0xc04494030000020dc9a83d 0xf60d606a0688⟩,
  ⟨0x30c030c030c030c0,⟨6,by decide⟩,0x3080008020000000,[ew237,ew256,ew264,ew265],5,decodeHints 0xc06030378fc014174349240020dc008370020dc9a924⟩,
  ⟨0x3300003333000033,⟨0,by decide⟩,0x3200000020000000,[ew240,ew253,ew268,ew269],4,decodeHints 0xaa030048460702e44297a00816832046102768ed97a⟩,
  ⟨0x3300330033003300,⟨8,by decide⟩,0x3200000020000000,[ew243,ew256,ew268,ew270],4,decodeHints 0xaa03004846014174178d600816832046062308620d6⟩,
  ⟨0x3333000033330000,⟨16,by decide⟩,0x3200000020000000,[ew245,ew260,ew268,ew272],4,decodeHints 0xaa030048460262003296c008168320460fa6c4d996c⟩,
  ⟨0x4488448844884488,⟨3,by decide⟩,0x4480008040000000,[ew282,ew288,ew293,ew294],5,decodeHints 0xc08038380fd028140351260020e4008390020e4a7926⟩,
  ⟨0x5050a0a05050a0a0,⟨5,by decide⟩,0x5000808040008000,[ew279,ew303,ew305,ew307],4,localHints 3 0xc0a4a4028000020d49b83c 0xf60d606a0688⟩,
  ⟨0x50a050a050a050a0,⟨5,by decide⟩,0x5080008040000000,[ew282,ew301,ew309,ew310],5,decodeHints 0xc0c03c380fe02818c351280020d4008350020d49b928⟩,
  ⟨0x5500005555000055,⟨0,by decide⟩,0x5400000040000000,[ew285,ew298,ew313,ew314],4,decodeHints 0x16803c0704a0963005917901a1803204a15a764ed979⟩,
  ⟨0x5500550055005500,⟨8,by decide⟩,0x5400000040000000,[ew288,ew301,ew313,ew315],4,decodeHints 0x16803c0704a02818c280d701a1803204a0a830c620d7⟩,
  ⟨0x5555000055550000,⟨16,by decide⟩,0x5400000040000000,[ew290,ew305,ew313,ew317],4,decodeHints 0x16803c0704a0342504116a01a1803204a1626c8d996a⟩,
  ⟨0x8282828282828282,⟨1,by decide⟩,0x8280808080008000,[ew335,ew341,ew343,ew344],4,localHints 3 0x3d4084180000023c0408da 0xf60d606a0688⟩,
  ⟨0x8484848484848484,⟨2,by decide⟩,0x8480808080008000,[ew335,ew351,ew353,ew354],4,localHints 3 0x3d811c190000023c4568db 0xf60d606a0688⟩,
  ⟨0x8888888888888888,⟨3,by decide⟩,0x8880808088008000,[ew335,ew362,ew365,ew366],3,localHints 3 0x4c0008018000020e40c03f 0xf60d486a0688⟩,
  ⟨0x9090909090909090,⟨4,by decide⟩,0x9080808080008000,[ew335,ew375,ew377,ew378],4,localHints 3 0x3da14819800002374728e1 0xf60d606a0688⟩,
  ⟨0x9900990099009900,⟨8,by decide⟩,0x9800800088008000,[ew362,ew375,ew381,ew382],4,localHints 3 0x426064198030043546208c 0xf606a0d60688⟩
]

def viewsBlock10 : Array View := #[
  ⟨0xa0a0a0a0a0a0a0a0,⟨5,by decide⟩,0xa0808080a0008000,[ew335,ew392,ew395,ew396],3,localHints 3 0xc0e028028000020d41c03c 0xf60d486a0688⟩,
  ⟨0xa500a500a500a500,⟨8,by decide⟩,0xa4008000a0008000,[ew351,ew392,ew400,ew401],4,decodeHints 0x4280141908c0140146b08c01a0141908c0a830c6b08c⟩,
  ⟨0xaa0000aaaa0000aa,⟨1,by decide⟩,0xaa000080a8000000,[ew360,ew390,ew409,ew410],5,decodeHints 0xc1001c0480703020c428830020d41c8f010220c42883⟩,
  ⟨0xaa00aa00aa00aa00,⟨9,by decide⟩,0xaa008000a8008000,[ew362,ew392,ew409,ew414],4,decodeHints 0x82014018300040b017830008014018300620b017830⟩,
  ⟨0xaaaa00000000aaaa,⟨1,by decide⟩,0xaa80000000008000,[ew364,ew394,ew408,ew416],4,decodeHints 0x4c0014018300000f01f8da0868c506228102204408da⟩,
  ⟨0xaaaa0000aaaa0000,⟨17,by decide⟩,0xaa800000a8000000,[ew365,ew395,ew409,ew416],5,decodeHints 0xc1201c04807016184328610361dc3c9850fa18432861⟩,
  ⟨0xc0c0c0c0c0c0c0c0,⟨6,by decide⟩,0xc0808080c0008000,[ew335,ew436,ew439,ew440],3,localHints 3 0xc14050030000020dc2583d 0xf60d486a0688⟩,
  ⟨0xc300c300c300c300,⟨8,by decide⟩,0xc2008000c0008000,[ew341,ew436,ew443,ew444],4,decodeHints 0x42a0181808c0280186b88c0080181808c0623086b88c⟩,
  ⟨0xcc0000cccc0000cc,⟨2,by decide⟩,0xcc000080c8000000,[ew360,ew434,ew453,ew454],5,decodeHints 0xc1602007008030210590840020dc1c8f115a21059084⟩,
  ⟨0xcc00cc00cc00cc00,⟨10,by decide⟩,0xcc008000c8008000,[ew362,ew436,ew453,ew458],4,decodeHints 0xcc018018320040b82803201a018018320a80b828032⟩,
  ⟨0xcccc00000000cccc,⟨2,by decide⟩,0xcc80000000008000,[ew364,ew438,ew452,ew460],4,decodeHints 0x4c0018018320000f41f8db0868cd0622b15a2b4568db⟩,
  ⟨0xcccc0000cccc0000,⟨18,by decide⟩,0xcc800000c8000000,[ew365,ew439,ew453,ew460],5,decodeHints 0xc1802007008016188410620361e03c98616218841062⟩,
  ⟨0xf00000f0f00000f0,⟨4,by decide⟩,0xf0000080e0000000,[ew390,ew434,ew492,ew493],5,decodeHints 0xc1a0300780c0702e4600b90020dc1a8dd1ca2e4600b9⟩,
  ⟨0xf000f000f000f000,⟨12,by decide⟩,0xf0008000e0008000,[ew392,ew436,ew492,ew497],4,decodeHints 0x1380180283301417431833032018028330fc17431833⟩,
  ⟨0xf0f00000f0f00000,⟨20,by decide⟩,0xf0800000e0000000,[ew395,ew439,ew492,ew499],5,decodeHints 0xc1c0300780c0262004a0800361e03b9872002004a080⟩,
  ⟨0xff0000000000ff00,⟨8,by decide⟩,0xfe00000000008000,[ew408,ew452,ew491,ew531],5,decodeHints 0xc1e018028330060c81808c062308618c21883086188c⟩
]

def viewsBlock11 : Array View := #[
  ⟨0xff000000ff000000,⟨24,by decide⟩,0xfe000000e8000000,[ew409,ew453,ew492,ew531],5,decodeHints 0xc200200384201211825042008168300420c811825042⟩,
  ⟨0xff0000ff00000000,⟨32,by decide⟩,0xfe00008000000000,[ew410,ew454,ew493,ew531],5,decodeHints 0xc2204408076024290529100b03706f8dc1e43706f910⟩,
  ⟨0xff00ff0000000000,⟨40,by decide⟩,0xfe00800000000000,[ew414,ew458,ew497,ew531],5,decodeHints 0xc24144278d909034c6a150042398798e620439879950⟩,
  ⟨0xffff000000000000,⟨48,by decide⟩,0xfe80000000000000,[ew416,ew460,ew499,ew531],5,decodeHints 0xc260d0168ac05427c50151040324668c920632466951⟩,
  ⟨0xffffffff,⟨0,by decide⟩,0xe8008000,[ew30,ew38,ew43,ew45,ew46],7,decodeHints 0xc28018028330060c81808c0000f41e0e107e36c6d11b0040b8160d505e3586b88c0302104194910a5e8bc91b⟩,
  ⟨0xf0f0f0f0f0f0f0f,⟨0,by decide⟩,0xe00000008000000,[ew175,ew191,ew202,ew206,ew207],5,decodeHints 0x2c02003842016188309390040b8160d503021041949008168300420fa6c4d9139062308618d5102768ec949⟩,
  ⟨0xf0ff0f00f0ff0f0,⟨4,by decide⟩,0xe00808008008000,[ew177,ew193,ew204,ew206,ew208],7,localHints 4 0xc2e158030050660001e83c0020dc1a8dd23f85b0a8e1 0xfdcba980edcba9807654a98076543210⟩,
  ⟨0x3333333333333333,⟨0,by decide⟩,0x3200000020000000,[ew246,ew261,ew271,ew273,ew274],5,decodeHints 0x44030048460262003296c014174178d60702e44297a008168320460fa6c4d996c062308620d6102768ed97a⟩,
  ⟨0x5555555555555555,⟨0,by decide⟩,0x5400000040000000,[ew291,ew306,ew316,ew318,ew319],5,decodeHints 0x5003c0704a0342504116a02818c280d70963005917901a1803204a1626c8d996a0a830c620d715a764ed979⟩,
  ⟨0x9999999999999999,⟨0,by decide⟩,0x9880808088008000,[ew367,ew379,ew383,ew384,ew385],6,decodeHints 0xc300cc0188c0003841f91b0043540188c0305241f91b0023741c9ac0003841f91b0023741c9ac030524ed91b⟩,
  ⟨0xa5a5a5a5a5a5a5a5,⟨0,by decide⟩,0xa4808080a0008000,[ew355,ew397,ew402,ew403,ew404],6,decodeHints 0xc320141908c0000f06d91b0140146b08c0700f0bd11b0020d4789ac0000f06d91b0020d4789ac15a764bd11b⟩,
  ⟨0xaaaaaaaaaaaaaaaa,⟨1,by decide⟩,0xaa808080a8008000,[ew367,ew397,ew415,ew419,ew420],6,decodeHints 0x208014018300000f01f8da0040b01783003020c428da0020d41c8f00000f01f8da0020d41c8f010220c428da⟩,
  ⟨0xc3c3c3c3c3c3c3c3,⟨0,by decide⟩,0xc2808080c0008000,[ew345,ew441,ew445,ew446,ew447],6,decodeHints 0xc340181808c0000f46d11b0280186b88c0960f4bc91b0020dc781ac0000f46d11b0020dc781ac102768bc91b⟩,
  ⟨0xcccccccccccccccc,⟨2,by decide⟩,0xcc808080c8008000,[ew367,ew441,ew459,ew463,ew464],6,decodeHints 0x222018018320000f41f8db0040b828032030210590db0020dc1c8f10000f41f8db0020dc1c8f115a210590db⟩,
  ⟨0xf0f0f0f0f0f0f0f0,⟨4,by decide⟩,0xf0808080e0008000,[ew397,ew441,ew498,ew502,ew503],6,decodeHints 0x260018028330000f41e0e1014174318330702e4600e10020dc1a8dd0000f41e0e10020dc1a8dd1ca2e4600e1⟩,
  ⟨0xff0000ffff0000ff,⟨0,by decide⟩,0xfe000080e8000000,[ew413,ew457,ew496,ew532,ew533],8,decodeHints 0xc3602003842012118250420302104194910a5e8bc9490020dc1a8dd0723c4781ac102768ec9493b65e8bc949⟩
]

def viewsBlock12 : Array View := #[
  ⟨0xff00ff00ff00ff00,⟨8,by decide⟩,0xfe008000e8008000,[ew415,ew459,ew498,ew532,ew534],8,decodeHints 0xc38018028330060c81808c0040b8160d505e3586b88c008018028330060c81808c062308618d51883586b88c⟩,
  ⟨0xffff0000ffff0000,⟨16,by decide⟩,0xfe800000e8000000,[ew419,ew463,ew502,ew532,ew536],8,decodeHints 0xc3a0200384201211825042016188309390ca5b0b51390361e03b9870f2618c29920fa6c4d91393665b0b5139⟩,
  ⟨0xffffffff00000000,⟨32,by decide⟩,0xfe80808000000000,[ew420,ew464,ew503,ew534,ew536],6,localHints 4 0x4802004204408076024290528581e43706f910 0xda987650ca987650ba98765042123210⟩,
  ⟨0xffffffffffffffff,⟨0,by decide⟩,0xfe808080e8008000,[ew426,ew470,ew509,ew535,ew537,ew538],10,decodeHints 0xc3c018028330060c81808c0000f41e0e107e36c6d11b0040b8160d505e3586b88c0302104194910a5e8bc91b0020dc1a8dd0723c4781ac0000f41e0e107e36c6d11b0020dc1a8dd0723c4781ac102768ec9493b65e8bc91b⟩
]

def viewsGet (i : Nat) : Option View :=
  if i < 96 then
    if i < 48 then
      if i < 16 then
        viewsBlock0[(i-0)]?
      else
        if i < 32 then
          viewsBlock1[(i-16)]?
        else
          viewsBlock2[(i-32)]?
    else
      if i < 64 then
        viewsBlock3[(i-48)]?
      else
        if i < 80 then
          viewsBlock4[(i-64)]?
        else
          viewsBlock5[(i-80)]?
  else
    if i < 144 then
      if i < 112 then
        viewsBlock6[(i-96)]?
      else
        if i < 128 then
          viewsBlock7[(i-112)]?
        else
          viewsBlock8[(i-128)]?
    else
      if i < 176 then
        if i < 160 then
          viewsBlock9[(i-144)]?
        else
          viewsBlock10[(i-160)]?
      else
        if i < 192 then
          viewsBlock11[(i-176)]?
        else
          viewsBlock12[(i-192)]?

def nodesBlock0 : Array Node := #[
  ⟨0,2,[ew56,ew57],localHints 2 0x15c9b82486e 0x235e84⟩,
  ⟨1,2,[ew63,ew64],localHints 2 0x1309bc2486f 0x235e84⟩,
  ⟨2,2,[ew70,ew71],localHints 2 0x1329c024870 0x235e84⟩,
  ⟨3,2,[ew101,ew108],localHints 2 0x5e69c4d6964 0x235e84⟩,
  ⟨4,2,[ew99,ew112],localHints 2 0x5e89c8d7165 0x235e84⟩,
  ⟨5,2,[ew130,ew137],localHints 2 0x5ea9ccd6966 0x235e84⟩,
  ⟨6,2,[ew128,ew141],localHints 2 0x5ec9d0d7965 0x235e84⟩,
  ⟨7,2,[ew212,ew218],localHints 2 0x5ee9d4d7166 0x235e84⟩,
  ⟨8,2,[ew210,ew221],localHints 2 0x5f09d8d7964 0x235e84⟩,
  ⟨9,3,[ew20,ew23,ew26],localHints 4 0x2f0580080503000a00c04807 0x258168155262367057066353024314322010⟩,
  ⟨10,3,[ew20,ew31,ew34],localHints 4 0x5005c0080a03200c00c07008 0x258168155262367057066353024314322010⟩,
  ⟨11,3,[ew23,ew31,ew39],localHints 4 0x630ba0280a03300c0140780c 0x258168155262367057066353024314322010⟩,
  ⟨12,3,[ew26,ew34,ew39],localHints 4 0x4a08c0240704201001c0780c 0x258168155262367057066353024314322010⟩,
  ⟨13,3,[ew48,ew50,ew51],localHints 3 0x7a2565e817b02004804807 0x30ad94e7118391ea2008325a408⟩,
  ⟨14,3,[ew48,ew53,ew54],localHints 3 0x7a6565e919002204807008 0x30ad94e7118391ea2008325a408⟩,
  ⟨15,3,[ew50,ew53,ew55],localHints 3 0x7aa5edea1900220400780c 0x30ad94e7118391ea2008325a408⟩
]

def nodesBlock1 : Array Node := #[
  ⟨22,3,[ew87,ew90,ew92],localHints 3 0x7ae569eb17c05a0a804807 0x30ad94e7118391ea2008325a408⟩,
  ⟨23,3,[ew87,ew94,ew96],localHints 3 0x7b2569ec1910680a807008 0x30ad94e7118391ea2008325a408⟩,
  ⟨24,3,[ew90,ew94,ew97],localHints 3 0x7b65f1ed1910680b40780c 0x30ad94e7118391ea2008325a408⟩,
  ⟨25,3,[ew103,ew104,ew105],localHints 3 0x7ba010008202faf70d1000 0x799b4eeed184b66c280c4263408⟩,
  ⟨28,3,[ew98,ew117,ew118],localHints 3 0x7bc7713ba0802a0840a006 0x30ad94e7118391ea2008325a408⟩,
  ⟨30,3,[ew132,ew133,ew134],localHints 3 0x7c0034008452fcf7cd1800 0x799b4eeed184b66c280c4263408⟩,
  ⟨33,3,[ew127,ew146,ew147],localHints 3 0x7c27753ba0902e11c05005 0x30ad94e7118391ea2008325a408⟩,
  ⟨36,3,[ew158,ew166,ew168],localHints 4 0x11f06a0040211e00e19c4b010 0x258168155262367057066353024314322010⟩,
  ⟨38,3,[ew162,ew166,ew178],localHints 4 0x17f0ee06c020f900e1b89002d 0x258168155262367057066353024314322010⟩,
  ⟨40,3,[ew158,ew182,ew184],localHints 4 0x13206e0040692101019c5f811 0x258168155262367057066353024314322010⟩,
  ⟨42,3,[ew162,ew182,ew194],localHints 4 0x1800f006c068fa0101b899834 0x258168155262367057066353024314322010⟩,
  ⟨44,3,[ew165,ew181,ew198],localHints 4 0x22644a4d0d803300c0140b815 0x258168155262367057066353024314322010⟩,
  ⟨45,3,[ew166,ew182,ew198],localHints 4 0x600b40100684201001c0b815 0x258168155262367057066353024314322010⟩,
  ⟨46,3,[ew168,ew184,ew198],localHints 4 0x14b2942585f8760220400b815 0x258168155262367057066353024314322010⟩,
  ⟨47,3,[ew171,ew187,ew198],localHints 4 0x14d298158398d90a213c0b815 0x258168155262367057066353024314322010⟩,
  ⟨48,3,[ew178,ew194,ew198],localHints 4 0x2794f0480998ac0680b40b815 0x258168155262367057066353024314322010⟩
]

def nodesBlock2 : Array Node := #[
  ⟨49,3,[ew214,ew215,ew216],localHints 3 0x7c60640085e348f8905000 0x799b4eeed184b66c280c4263408⟩,
  ⟨52,3,[ew209,ew226,ew227],localHints 3 0x7c87793ba0b03c14801003 0x30ad94e7118391ea2008325a408⟩,
  ⟨54,3,[ew231,ew239,ew241],localHints 4 0x14e072004021220121a482812 0x258168155262367057066353024314322010⟩,
  ⟨55,3,[ew235,ew239,ew247],localHints 4 0x1810f206c020fb0121bc9182a 0x258168155262367057066353024314322010⟩,
  ⟨57,3,[ew231,ew252,ew254],localHints 4 0x13506e0040c9240181a483011 0x258168155262367057066353024314322010⟩,
  ⟨59,3,[ew235,ew252,ew263],localHints 4 0x1820f006c0c8fc0181bc9b034 0x258168155262367057066353024314322010⟩,
  ⟨61,3,[ew238,ew251,ew267],localHints 4 0x27b4f473ce703200c00c0f015 0x258168155262367057066353024314322010⟩,
  ⟨62,3,[ew239,ew252,ew267],localHints 4 0x640b40100c8460180240f015 0x258168155262367057066353024314322010⟩,
  ⟨63,3,[ew241,ew254,ew267],localHints 4 0x27d4f8414830a40220480f015 0x258168155262367057066353024314322010⟩,
  ⟨64,3,[ew244,ew257,ew267],localHints 4 0x27f4fc59c928d30a21200f015 0x258168155262367057066353024314322010⟩,
  ⟨65,3,[ew247,ew263,ew267],localHints 4 0x28150048c9b09f0680a80f015 0x258168155262367057066353024314322010⟩,
  ⟨67,3,[ew276,ew284,ew286],localHints 4 0x14f0720040692601c1a883812 0x258168155262367057066353024314322010⟩,
  ⟨68,3,[ew280,ew284,ew292],localHints 4 0x1830f206c068fd01c1c09382a 0x258168155262367057066353024314322010⟩,
  ⟨70,3,[ew276,ew297,ew299],localHints 4 0x13706a0040c92801e1a884010 0x258168155262367057066353024314322010⟩,
  ⟨72,3,[ew280,ew297,ew308],localHints 4 0x1840ee06c0c8fe01e1c09c02d 0x258168155262367057066353024314322010⟩,
  ⟨74,3,[ew283,ew296,ew312],localHints 4 0x283504744e803000a00c0f017 0x258168155262367057066353024314322010⟩
]

def nodesBlock3 : Array Node := #[
  ⟨75,3,[ew284,ew297,ew312],localHints 4 0x640c00340c84a01e0380f017 0x258168155262367057066353024314322010⟩,
  ⟨76,3,[ew286,ew299,ew312],localHints 4 0x28550841c840a50200480f017 0x258168155262367057066353024314322010⟩,
  ⟨77,3,[ew289,ew302,ew312],localHints 4 0x28750c5a0948d409e1200f017 0x258168155262367057066353024314322010⟩,
  ⟨78,3,[ew292,ew308,ew312],localHints 4 0x28951049c9c0a005a0a80f017 0x258168155262367057066353024314322010⟩,
  ⟨79,3,[ew326,ew338,ew339],localHints 4 0x811e0004022272d232c2c0a5 0x258168155262367057066353024314322010⟩,
  ⟨80,3,[ew330,ew336,ew342],localHints 4 0x8145010c188da060000100a0 0x258168155262367057066353024314322010⟩,
  ⟨81,3,[ew333,ew337,ew342],localHints 4 0x1b13241e02d16a094068100a0 0x258168155262367057066353024314322010⟩,
  ⟨82,3,[ew334,ew338,ew342],localHints 4 0x7d30a06c022292d2330100a0 0x258168155262367057066353024314322010⟩,
  ⟨83,3,[ew326,ew348,ew349],localHints 4 0xad1e200406a2a2d632c3a0a4 0x258168155262367057066353024314322010⟩,
  ⟨84,3,[ew330,ew346,ew352],localHints 4 0xad45610c2a0db0640002289f 0x258168155262367057066353024314322010⟩,
  ⟨85,3,[ew332,ew347,ew352],localHints 4 0x1b23241dc3016c08c04c2289f 0x258168155262367057066353024314322010⟩,
  ⟨86,3,[ew334,ew348,ew352],localHints 4 0xb130c06c06a2c2d63302289f 0x258168155262367057066353024314322010⟩,
  ⟨87,3,[ew324,ew357,ew359],localHints 4 0x28a1e00d4950850120e07f812 0x258168155262367057066353024314322010⟩,
  ⟨88,3,[ew325,ew358,ew359],localHints 4 0x28b1e20dc958b201c12c7f812 0x258168155262367057066353024314322010⟩,
  ⟨89,3,[ew328,ew357,ew361],localHints 4 0x1e03be2989502f01202872048 0x258168155262367057066353024314322010⟩,
  ⟨90,3,[ew329,ew358,ew361],localHints 4 0x22d3c229c9585001c05072048 0x258168155262367057066353024314322010⟩
]

def nodesBlock4 : Array Node := #[
  ⟨91,3,[ew330,ew356,ew363],localHints 4 0x1d241810cad83f0060006402a 0x258168155262367057066353024314322010⟩,
  ⟨92,3,[ew332,ew357,ew363],localHints 4 0x28c30a1dc9506501204c6402a 0x258168155262367057066353024314322010⟩,
  ⟨93,3,[ew333,ew358,ew363],localHints 4 0x28d30c1e09588201c0686402a 0x258168155262367057066353024314322010⟩,
  ⟨94,3,[ew326,ew372,ew373],localHints 4 0xe51ba0040ca2e2da32c45876 0x258168155262367057066353024314322010⟩,
  ⟨95,3,[ew331,ew371,ew376],localHints 4 0x1b33241e43213908402c2f0ac 0x258168155262367057066353024314322010⟩,
  ⟨96,3,[ew334,ew372,ew376],localHints 4 0x10030e06c0ca2f2da3302f0ac 0x258168155262367057066353024314322010⟩,
  ⟨97,3,[ew356,ew370,ew380],localHints 4 0xc451c56c3f08c06600c0f101 0x258168155262367057066353024314322010⟩,
  ⟨98,3,[ew359,ew373,ew380],localHints 4 0xf251e3fc459100ec0480f101 0x258168155262367057066353024314322010⟩,
  ⟨99,3,[ew361,ew374,ew380],localHints 4 0x102520390291501b21200f101 0x258168155262367057066353024314322010⟩,
  ⟨100,3,[ew363,ew376,ew380],localHints 4 0x1035223202f1511580a80f101 0x258168155262367057066353024314322010⟩,
  ⟨101,3,[ew323,ew387,ew389],localHints 4 0x2921e00e49608300e06084810 0x258168155262367057066353024314322010⟩,
  ⟨102,3,[ew325,ew388,ew389],localHints 4 0x2931ba0dc9d0c001e12c84810 0x258168155262367057066353024314322010⟩,
  ⟨103,3,[ew327,ew387,ew391],localHints 4 0x1e23be2849602c00e0088504f 0x258168155262367057066353024314322010⟩,
  ⟨104,3,[ew329,ew388,ew391],localHints 4 0x2303c629c9d06301e0508504f 0x258168155262367057066353024314322010⟩,
  ⟨105,3,[ew330,ew386,ew393],localHints 4 0x1d346210cb703c00a0006f02d 0x258168155262367057066353024314322010⟩,
  ⟨106,3,[ew331,ew387,ew393],localHints 4 0x29430a1e49606100e02c6f02d 0x258168155262367057066353024314322010⟩
]

def nodesBlock5 : Array Node := #[
  ⟨107,3,[ew333,ew388,ew393],localHints 4 0x29530e1e09d09401e0686f02d 0x258168155262367057066353024314322010⟩,
  ⟨108,3,[ew346,ew386,ew399],localHints 4 0x296186150b708c00a0c896817 0x258168155262367057066353024314322010⟩,
  ⟨109,3,[ew349,ew389,ew399],localHints 4 0x2971be1d08491002029096817 0x258168155262367057066353024314322010⟩,
  ⟨110,3,[ew350,ew391,ew399],localHints 4 0x2981e611c8515009e34c96817 0x258168155262367057066353024314322010⟩,
  ⟨111,3,[ew352,ew393,ew399],localHints 4 0x29919a1146f15105a27c96817 0x258168155262367057066353024314322010⟩,
  ⟨112,3,[ew323,ew431,ew433],localHints 4 0x29a1e20e49d88401006085811 0x258168155262367057066353024314322010⟩,
  ⟨113,3,[ew324,ew432,ew433],localHints 4 0x29b1ba0d49e0b90180e085811 0x258168155262367057066353024314322010⟩,
  ⟨114,3,[ew327,ew431,ew435],localHints 4 0x1e43c22849d82e01000886051 0x258168155262367057066353024314322010⟩,
  ⟨115,3,[ew328,ew432,ew435],localHints 4 0x2323c62989e05d01802886051 0x258168155262367057066353024314322010⟩,
  ⟨116,3,[ew330,ew430,ew437],localHints 4 0x1d446610cb783d00c00070034 0x258168155262367057066353024314322010⟩,
  ⟨117,3,[ew331,ew431,ew437],localHints 4 0x29c30c1e49d86201002c70034 0x258168155262367057066353024314322010⟩,
  ⟨118,3,[ew332,ew432,ew437],localHints 4 0x29d30e1dc9e08001804c70034 0x258168155262367057066353024314322010⟩,
  ⟨119,3,[ew336,ew430,ew442],localHints 4 0x29e1840c4b788c00c0c097015 0x258168155262367057066353024314322010⟩,
  ⟨120,3,[ew339,ew433,ew442],localHints 4 0x29f1b81608591002229497015 0x258168155262367057066353024314322010⟩,
  ⟨121,3,[ew340,ew435,ew442],localHints 4 0x2a01cc084861500a235097015 0x258168155262367057066353024314322010⟩,
  ⟨122,3,[ew342,ew437,ew442],localHints 4 0x2a11920807015106828097015 0x258168155262367057066353024314322010⟩
]

def nodesBlock6 : Array Node := #[
  ⟨127,5,[ew28,ew36,ew41,ew44],localHints 5 0x2f1380b0050300cc0240382e0040501900301c0201980600a1040780c 0x9a2349b9749ba319a16878d727b6327b56b78e237b51078dd078d087b5cd1116c1194c1196b1114411909110e911108118e610065110251106310020⟩,
  ⟨133,4,[ew161,ew172,ew174,ew176],localHints 5 0x4d0c99b40ce02cf28350020111a0071665f42b03c00a00010010 0x82a455acaa8c16b128415ac2a509621144e3bdc5688e21ad805300b58d4319c682a50730ca3008830906210020⟩,
  ⟨134,2,[ew116,ew164,ew166],decodeHints 0x23c4783381023e47c0206706a0d400807⟩,
  ⟨134,3,[ew116,ew164,ew170,ew179],decodeHints 0xce19c012f90580b0010101f23e43701000210c248010025fca900106a0d400807⟩,
  ⟨134,3,[ew159,ew164,ew166,ew180],localHints 4 0x47c1a804020be4a90010ce0084b007 0xaa84994821276454332100⟩,
  ⟨134,4,[ew159,ew164,ew170,ew179,ew180],decodeHints 0x10c008490025fc008040020084b0025f60d41a8010080097d002020040902367ca0051a801004084010210dc1b803807⟩,
  ⟨134,3,[ew82,ew164,ew166,ew180],localHints 4 0x8f91e004258a900100819c08007 0x99344340887645432210⟩,
  ⟨134,4,[ew82,ew164,ew170,ew179,ew180],localHints 5 0x430925fc4b2fc0580847c920002011511530041b808007 0x40ef3b8e638da361cc702d6352408398e628c8310820⟩,
  ⟨134,4,[ew163,ew164,ew170,ew179,ew180],localHints 4 0x625fc338042e00b0108f92400047200215c1b808007 0xffc4eec2dd430cbaa498827665454323210⟩,
  ⟨134,2,[ew83,ew166,ew180],decodeHints 0x23e47c0206706a0d40080723c47833810⟩,
  ⟨134,3,[ew164,ew166,ew169,ew180],localHints 4 0x104b02106a0057ea3600e47833810 0xa616811981776335432210⟩,
  ⟨134,3,[ew91,ew164,ew166,ew180],localHints 3 0x23e0108f00112c19c08007 0xff2188b5191a208⟩,
  ⟨134,4,[ew164,ew166,ew170,ew180],localHints 5 0x2ff2a4bf81895c0ce0d4008045f82b97d82c00e00810810 0x20841929321ee4a448685290a1024a58c588cb1a5404280948d030180338c66180a0008830906210020⟩,
  ⟨134,3,[ew83,ew170,ew179,ew180],decodeHints 0x86004248012fe004a90010ce19c012fd06a0d4008070580b0010101f23e437010⟩,
  ⟨134,4,[ew164,ew169,ew170,ew179,ew180],decodeHints 0x10c008490021b8009520ce19c012fe008004108020420085706e06a0d4008070580b0010101f23e43701000ef98b8007⟩,
  ⟨134,4,[ew91,ew164,ew170,ew179,ew180],localHints 4 0xc4bf8675fe010160f9002a8ca980215c1b808007 0xeea4da2cc4b0a1099418821776454321010⟩
]

def nodesBlock7 : Array Node := #[
  ⟨134,5,[ew164,ew170,ew179,ew180],localHints 5 0x2181b092a8df617f2a4facae0677d42b91a835002fa402153058009510217d03e4b80070dcf9c90010 0x62b9d621efd239bd29efc8db88c9ef8c9b7b0defac954a8eb460d4a64a72291f0881b0281ef711a46014b6110b4914a4810028066390262906310020⟩,
  ⟨135,4,[ew161,ew188,ew190,ew192],localHints 5 0x6c0c99e60ce02cf28370020351b8081665f83983d00c00022811 0x82a455acaa8c16b128415ac2a509621144e3bdc5688e21ad805300b58d4319c682a50730ca3008830906210020⟩,
  ⟨136,2,[ew145,ew164,ew182],decodeHints 0x242484338112644c80686706e0dc00808⟩,
  ⟨136,3,[ew145,ew164,ew186,ew195],decodeHints 0xce19c0130005c0b8010111f43e83701100210c24801002600a900106e0dc00808⟩,
  ⟨136,3,[ew159,ew164,ew182,ew196],localHints 4 0x4c81b80d022c00a90010ce0085f808 0xaa84994821276454332100⟩,
  ⟨136,4,[ew159,ew164,ew186,ew195,ew196],decodeHints 0x10c008490026000080d0020085f8026040dc1b80101a0098080202204499a397da0051c00100411c010470dc1b804008⟩,
  ⟨136,3,[ew82,ew164,ew182,ew196],localHints 4 0x991210042fca900101a19c08808 0x99344340887645432210⟩,
  ⟨136,4,[ew82,ew164,ew186,ew195,ew196],localHints 5 0x430926005fb0305c11c7d1330020355215d0041b808808 0x40ef3b8e638da361cc702d6352408398e628c8310820⟩,
  ⟨136,4,[ew163,ew164,ew186,ew195,ew196],localHints 4 0xa86003380d2e00b8238fa2660047200215c1b808808 0xffc4eec2dd430cbaa498827665454323210⟩,
  ⟨136,2,[ew83,ew182,ew196],decodeHints 0x2644c80686706e0dc0080824248433811⟩,
  ⟨136,3,[ew164,ew182,ew185,ew196],localHints 4 0x345f84706e0058223901048433811 0xa616811981776335432210⟩,
  ⟨136,3,[ew95,ew164,ew182,ew196],localHints 3 0x2640349080117e19c08808 0xff2188b5191a208⟩,
  ⟨136,4,[ew164,ew182,ew186,ew196],localHints 5 0x3062a4c142a1710ce0dc0080d6062b98102e01000823811 0x20841929321ee4a448685290a1024a58c588cb1a5404280948d030180338c66180a0008830906210020⟩,
  ⟨136,3,[ew83,ew186,ew195,ew196],decodeHints 0x8600424801300004a90010ce19c0130406e0dc0080805c0b8010111f43e837011⟩,
  ⟨136,4,[ew164,ew185,ew186,ew195,ew196],decodeHints 0x10c008490021b8009520ce19c0130501a0042380208e0085706e06e0dc0080805c0b8010111f43e837011010fb8b8008⟩,
  ⟨136,4,[ew95,ew164,ew186,ew195,ew196],localHints 4 0x150c006760c034170fa002a94ae80215c1b808808 0xeea4da2cc4b0a1099418821776454321010⟩
]

def nodesBlock8 : Array Node := #[
  ⟨136,5,[ew164,ew186,ew195,ew196],localHints 5 0x2181b092a95fa1802a4fccb88677e42b91c037002fc40695d05c009520477e03e8b80080dcfbc99811 0x62b9d621efd239bd29efc8db88c9ef8c9b7b0defac954a8eb460d4a64a72291f0881b0281ef711a46014b6110b4914a4810028066390262906310020⟩,
  ⟨141,4,[ew160,ew176,ew192,ew203,ew205],localHints 4 0x12c5346694c0e63242281502e6d05985619008008011 0xff45eeb4dd92cc4baa29876545432321100⟩,
  ⟨141,2,[ew136,ew176,ew198],decodeHints 0x2945284b01129652c5f8100ec1d808015⟩,
  ⟨141,3,[ew136,ew176,ew203,ew205],decodeHints 0x12c2582b3070225302b0110227a04c8110205343981002079c4c0100ec1d808015⟩,
  ⟨141,3,[ew173,ew176,ew192,ew198],localHints 4 0x52c3b01712c0805fb073440400a811 0xaa52056099287765423210⟩,
  ⟨141,4,[ew173,ew176,ew192,ew203,ew205],decodeHints 0x2fc5f873610040a6873020040f3898020044399a30227a04c8110ec1d8080170ac15810045040115fa8103cc0400a811⟩,
  ⟨141,3,[ew77,ew176,ew192,ew198],localHints 4 0xa594a0402fc0a8963440400b811 0x99628876212544232100⟩,
  ⟨141,4,[ew77,ew176,ew192,ew203,ew205],localHints 5 0xbf612534f38982981cc6484502a158d290d0400400b811 0x420a789ca109ac12cea4a46810447318a320c4110400⟩,
  ⟨141,2,[ew107,ew192,ew198],decodeHints 0x29652c5f8102945284b0110ec1d808015⟩,
  ⟨141,3,[ew107,ew192,ew203,ew205],decodeHints 0x12c2582b30a0205343981002079c4c0100225302b0110227a04c8110ec1d808015⟩,
  ⟨141,3,[ew176,ew189,ew192,ew198],localHints 4 0x2fc228172942583b01002ac28d1811 0x4694a69684776055430210⟩,
  ⟨141,4,[ew176,ew189,ew192,ew203,ew205],decodeHints 0x2584b0566160402b1a202079c4c0100e61582282008a0800b8100225302b0110227a04c8110ec1d808015022fd8da011⟩,
  ⟨141,3,[ew79,ew176,ew192,ew198],localHints 4 0x14b08a5285f89602068c08815 0x88746641011054331210⟩,
  ⟨141,4,[ew79,ew176,ew192,ew203,ew205],localHints 5 0x966185340b8cd08a530f40990e61589e90d04004008815 0x42067b9a6631630a8c10a50100420398a320c4208020⟩,
  ⟨141,4,[ew176,ew192,ew198,ew205],localHints 5 0xd3096618689858cd6122ccd1b08192080228760220400b815 0x23181950128417842a709a21144133025288c21a8605800a48d031986029c0630ca3008830906210020⟩,
  ⟨141,5,[ew176,ew192,ew203,ew205],localHints 5 0x6984b3fc166feca6bfa3ce13c4c13d7f25302b3f80e6434f4051040264d28453cc1d8da011020fdc0b815 0xf7a3df2f7d72e317737b38de3d0639385efc0e2370d0375977a5915a0d6329224981f228231811e4711647310d4b16a4910428066390262906310020⟩
]

def nodesBlock9 : Array Node := #[
  ⟨143,2,[ew115,ew237,ew239],decodeHints 0x2444883481229c538020690720e400809⟩,
  ⟨143,3,[ew115,ew237,ew243,ew248],decodeHints 0xd21a40530d05e0bc050121f63ec3781200210c24801002604aa0010720e400809⟩,
  ⟨143,3,[ew232,ew237,ew239,ew249],localHints 4 0x5381c804024c34aa0010d202882809 0xaa84994821276454332100⟩,
  ⟨143,4,[ew232,ew237,ew243,ew248,ew249],decodeHints 0x10c00849002604008040020288280a61e0e41c8010080298700a02404891a367fa0051d001014084050210de1bc04809⟩,
  ⟨143,3,[ew82,ew237,ew239,ew249],localHints 4 0xa7122014414aa0010081a409009 0x99344340887645432210⟩,
  ⟨143,4,[ew82,ew237,ew243,ew248,ew249],localHints 5 0x4309260482b1005e0847d9230020108e15e0141bc09009 0x40ef3b8e638da361cc702d6352408398e628c8310820⟩,
  ⟨143,4,[ew236,ew237,ew243,ew248,ew249],localHints 4 0x62604348042e40bc108fb2460048500a1301bc09009 0xffc4eec2dd430cbaa498827665454323210⟩,
  ⟨143,2,[ew84,ew239,ew249],decodeHints 0x29c538020690720e40080924448834812⟩,
  ⟨143,3,[ew237,ew239,ew242,ew249],localHints 4 0x108282107200588a3601248834812 0xa616811981776335432210⟩,
  ⟨143,3,[ew88,ew237,ew239,ew249],localHints 3 0x29c0109100120a1a409009 0xff2188b5191a208⟩,
  ⟨143,4,[ew237,ew239,ew243,ew249],localHints 5 0x3132a8c48189940d20e4008046202618782f01202810812 0x20841929321ee4a448685290a1024a58c588cb1a5404280948d030180338c66180a0008830906210020⟩,
  ⟨143,3,[ew84,ew243,ew248,ew249],decodeHints 0x8600424801302004aa0010d21a4053110720e40080905e0bc050121f63ec37812⟩,
  ⟨143,4,[ew237,ew242,ew243,ew248,ew249],decodeHints 0x10c008490021bc009540d21a4053120080041080a0420284c06f0720e40080905e0bc050121f63ec37812012ff8b9009⟩,
  ⟨143,4,[ew88,ew237,ew243,ew248,ew249],localHints 4 0xc4c0869626010178fb002a98af00a1301bc09009 0xeea4da2cc4b0a1099418821776454321010⟩,
  ⟨143,5,[ew237,ew243,ew248,ew249],localHints 5 0x2181b092a9a021812a900cca0698042611d0390030040215e05e0288e0218003ecb90090deffc91812 0x62b9d621efd239bd29efc8db88c9ef8c9b7b0defac954a8eb460d4a64a72291f0881b0281ef711a46014b6110b4914a4810028066390262906310020⟩,
  ⟨144,4,[ew234,ew258,ew260,ew262],localHints 5 0x73953b140d204e030370020660280c4766909283d00c0002f011 0x82a455acaa8c16b128415ac2a509621144e3bdc5688e21ad805300b58d4319c682a50730ca3008830906210020⟩
]

def nodesBlock10 : Array Node := #[
  ⟨145,2,[ew225,ew237,ew252],decodeHints 0x2484903481126a4d40c86906e0dc0080c⟩,
  ⟨145,3,[ew225,ew237,ew256,ew264],decodeHints 0xd21a4053150ba174050111f83f03781100210c24801002608aa00106e0dc0080c⟩,
  ⟨145,3,[ew232,ew237,ew252,ew265],localHints 4 0x4d41b819022c54aa0010d20288300c 0xaa84994821276454332100⟩,
  ⟨145,4,[ew232,ew237,ew256,ew264,ew265],decodeHints 0x10c00849002608008190020288300a62c0dc1b8010320298080a0220449b23d80e0051e001014148050520de1bc0600c⟩,
  ⟨145,3,[ew82,ew237,ew252,ew265],localHints 4 0x9a924014418aa0010321a40880c 0x99344340887645432210⟩,
  ⟨145,4,[ew82,ew237,ew256,ew264,ew265],localHints 5 0x43092608833170ba1487e136002065541730141bc0880c 0x40ef3b8e638da361cc702d6352408398e628c8310820⟩,
  ⟨145,4,[ew236,ew237,ew256,ew264,ew265],localHints 4 0xfc608348192e4174290fc26c0048500a1301bc0880c 0xffc4eec2dd430cbaa498827665454323210⟩,
  ⟨145,2,[ew84,ew252,ew265],decodeHints 0x26a4d40c86906e0dc0080c24849034811⟩,
  ⟨145,3,[ew237,ew252,ew255,ew265],localHints 4 0x648305206e0058c23d01849034811 0xa616811981776335432210⟩,
  ⟨145,3,[ew95,ew237,ew252,ew265],localHints 3 0x26a0649200120c1a40880c 0xff2188b5191a208⟩,
  ⟨145,4,[ew237,ew252,ew256,ew265],localHints 5 0x31a2a8c643f1a70d20dc0081962e2618b05d01802829011 0x20841929321ee4a448685290a1024a58c588cb1a5404280948d030180338c66180a0008830906210020⟩,
  ⟨145,3,[ew84,ew256,ew264,ew265],decodeHints 0x8600424801304004aa0010d21a40531806e0dc0080c0ba174050111f83f037811⟩,
  ⟨145,4,[ew237,ew255,ew256,ew264,ew265],decodeHints 0x10c008490021bc009540d21a4053190320042900a0a40284c06f06e0dc0080c0ba174050111f83f037811019020b900c⟩,
  ⟨145,4,[ew95,ew237,ew256,ew264,ew265],localHints 4 0x1f8c10696340642e8fc002aa4b980a1301bc0880c 0xeea4da2cc4b0a1099418821776454321010⟩,
  ⟨145,5,[ew237,ew256,ew264,ew265],localHints 5 0x2181b092aa6071822a9034d38698182611e03700302c0c9730ba029540528143f0b900c0df0249b011 0x62b9d621efd239bd29efc8db88c9ef8c9b7b0defac954a8eb460d4a64a72291f0881b0281ef711a46014b6110b4914a4810028066390262906310020⟩,
  ⟨149,2,[ew144,ew282,ew284],decodeHints 0x24c4983501229e53c0686a0720e40080e⟩
]

def nodesBlock11 : Array Node := #[
  ⟨149,3,[ew144,ew282,ew288,ew293],decodeHints 0xd41a80a31b0a01400a0121fa3f43801200210c2480100260caa8010720e40080e⟩,
  ⟨149,3,[ew277,ew282,ew284,ew294],localHints 4 0x53c1c80d024c6caa8010d40508380e 0xaa84994821276454332100⟩,
  ⟨149,4,[ew277,ew282,ew288,ew293,ew294],decodeHints 0x10c0084900260c0080d002050838146380e41c80101a0518701402404893a3981e0051f00102811c0a0470e01c00700e⟩,
  ⟨149,3,[ew82,ew282,ew284,ew294],localHints 4 0xa792602841caa80101a1a80900e 0x99344340887645432210⟩,
  ⟨149,4,[ew82,ew282,ew288,ew293,ew294],localHints 5 0x4309260c83b1d0a011c7e927002034af9740281c00900e 0x40ef3b8e638da361cc702d6352408398e628c8310820⟩,
  ⟨149,4,[ew281,ew282,ew288,ew293,ew294],localHints 4 0xa860c3500d2ea140238fd24e004860141321c00900e 0xffc4eec2dd430cbaa498827665454323210⟩,
  ⟨149,2,[ew85,ew284,ew294],decodeHints 0x29e53c0686a0720e40080e24c49835012⟩,
  ⟨149,3,[ew282,ew284,ew287,ew294],localHints 4 0x34838470720058f23901c49835012 0xa616811981776335432210⟩,
  ⟨149,3,[ew88,ew282,ew284,ew294],localHints 3 0x29e0349300120e1a80900e 0xff2188b5191a208⟩,
  ⟨149,4,[ew282,ew284,ew288,ew294],localHints 5 0x3202aac7c2a1a80d40e40080d63a2658e05001c05023812 0x20841929321ee4a448685290a1024a58c588cb1a5404280948d030180338c66180a0008830906210020⟩,
  ⟨149,3,[ew85,ew288,ew293,ew294],decodeHints 0x8600424801306004aa8010d41a80a31e0720e40080e0a01400a0121fa3f438012⟩,
  ⟨149,4,[ew282,ew287,ew288,ew293,ew294],decodeHints 0x10c008490021c0009550d41a80a31f01a0042381408e0504c8700720e40080e0a01400a0121fa3f43801201d040ba80e⟩,
  ⟨149,4,[ew88,ew282,ew288,ew293,ew294],localHints 4 0x150c186a640034280fd002aa8ba0141321c00900e 0xeea4da2cc4b0a1099418821776454321010⟩,
  ⟨149,5,[ew282,ew288,ew293,ew294],localHints 5 0x2181b092aaa0b1832ab054d406a8282651f03900304c069740a0050af8478243f4ba80e0e104493812 0x62b9d621efd239bd29efc8db88c9ef8c9b7b0defac954a8eb460d4a64a72291f0881b0281ef711a46014b6110b4914a4810028066390262906310020⟩,
  ⟨150,4,[ew279,ew303,ew305,ew307],localHints 5 0x74155b210d406a0c0350020660b80f47e6909483c00a0002f010 0x82a455acaa8c16b128415ac2a509621144e3bdc5688e21ad805300b58d4319c682a50730ca3008830906210020⟩,
  ⟨151,2,[ew224,ew282,ew297],decodeHints 0x2504a03501026e4dc0c86a06a0d40080f⟩
]

def nodesBlock12 : Array Node := #[
  ⟨151,3,[ew224,ew282,ew301,ew309],decodeHints 0xd41a80a3220c618c0a0101fc3f83801000210c24801002610aa80106a0d40080f⟩,
  ⟨151,3,[ew277,ew282,ew297,ew310],localHints 4 0x4dc1a819020c88aa8010d40508400f 0xaa84994821276454332100⟩,
  ⟨151,4,[ew277,ew282,ew301,ew309,ew310],decodeHints 0x10c0084900261000819002050840146460d41a8010320517d0140200409c23d832005200010281480a0520e01c00780f⟩,
  ⟨151,3,[ew82,ew282,ew297,ew310],localHints 4 0x9b928028420aa8010321a80800f 0x99344340887645432210⟩,
  ⟨151,4,[ew82,ew282,ew301,ew309,ew310],localHints 5 0x43092610843240c61487f138002065561880281c00800f 0x40ef3b8e638da361cc702d6352408398e628c8310820⟩,
  ⟨151,4,[ew281,ew282,ew301,ew309,ew310],localHints 4 0xfc610350192ea18c290fe270004860141321c00800f 0xffc4eec2dd430cbaa498827665454323210⟩,
  ⟨151,2,[ew85,ew297,ew310],decodeHints 0x26e4dc0c86a06a0d40080f2504a035010⟩,
  ⟨151,3,[ew282,ew297,ew300,ew310],localHints 4 0x648405206a00592a3d01e4a035010 0xa616811981776335432210⟩,
  ⟨151,3,[ew91,ew282,ew297,ew310],localHints 3 0x26e064940012101a80800f 0xff2188b5191a208⟩,
  ⟨151,4,[ew282,ew297,ew301,ew310],localHints 5 0x3272aac983f1b50d40d4008196482659186301e05029010 0x20841929321ee4a448685290a1024a58c588cb1a5404280948d030180338c66180a0008830906210020⟩,
  ⟨151,3,[ew85,ew301,ew309,ew310],decodeHints 0x8600424801308004aa8010d41a80a32506a0d40080f0c618c0a0101fc3f838010⟩,
  ⟨151,4,[ew282,ew300,ew301,ew309,ew310],decodeHints 0x10c008490021c0009550d41a80a326032004290140a40504c87006a0d40080f0c618c0a0101fc3f83801001f068ba80f⟩,
  ⟨151,4,[ew91,ew282,ew301,ew309,ew310],localHints 4 0x1f8c206a64e064318fe002ab4c40141321c00800f 0xeea4da2cc4b0a1099418821776454321010⟩,
  ⟨151,5,[ew282,ew301,ew309,ew310],localHints 5 0x2181b092ab6101842ab07cda86a83c265200350030740c9880c6051560528383f8ba80f0e106c9c010 0x62b9d621efd239bd29efc8db88c9ef8c9b7b0defac954a8eb460d4a64a72291f0881b0281ef711a46014b6110b4914a4810028066390262906310020⟩,
  ⟨162,4,[ew326,ew360,ew390,ew409,ew410],localHints 4 0x8110a20c1c2410020106581802402408007 0xcc647672bb947670aa49028767654543210⟩,
  ⟨162,4,[ew360,ew390,ew405,ew409,ew410],localHints 4 0x40858072908048350020100c03800e04808241 0xdd6576765c5cbb76a545998876545433210⟩
]

def nodesBlock13 : Array Node := #[
  ⟨162,4,[ew47,ew360,ew390,ew409,ew410],localHints 4 0x810722142c0830700040201802402408007 0xcc57bb62aa7965608070230656544323210⟩,
  ⟨162,4,[ew239,ew360,ew390,ew409,ew410],localHints 4 0x7481ca420ce0d44181014a0100083803002409007 0x3e63dd52c3b3aa569387212656543212100⟩,
  ⟨162,4,[ew359,ew360,ew390,ew409,ew410],localHints 4 0x8110a011218830700047f81802402408007 0xcca42a32bb740a988470230665454323210⟩,
  ⟨162,4,[ew360,ew390,ew409,ew410,ew411],localHints 4 0x21d20b00e4428070020412181807029409009 0xd734434cb40110aa7099348876543432010⟩,
  ⟨162,4,[ew49,ew360,ew390,ew409,ew410],localHints 4 0x8110a0d4418580020101c01802402408007 0xcc647672b24aa7099480210767654321010⟩,
  ⟨162,4,[ew166,ew360,ew390,ew409,ew410],localHints 4 0x74c1c88506aab83483814a0480200103002403810 0x8e58dd45c86bb41a8981761545433221010⟩,
  ⟨162,4,[ew360,ew389,ew390,ew409,ew410],localHints 4 0x81488214009090240104181807002408007 0xcc6426baa34998484720610554302100110⟩,
  ⟨162,4,[ew360,ew390,ew409,ew410,ew412],localHints 4 0x21d30b00252201006a0044181807029409007 0xd643344cb4aa61934340880776055430210⟩,
  ⟨162,4,[ew26,ew360,ew390,ew409,ew410],localHints 4 0x81072ac01aaaf0b00100081801204803810 0xc75bb53a337995181171321654432321010⟩,
  ⟨162,4,[ew51,ew360,ew390,ew409,ew410],localHints 4 0x102214020830700042c01802402408007 0xb942932aa74091088470230665432321010⟩,
  ⟨162,5,[ew360,ew390,ew409,ew410],localHints 5 0x8590ac408583d29101cc2a8530a2138852b890c1ac260030940242484620c0c1940709061101002508404807 0xfa5bdf71fddf1adda5e9d05f9d0db9c0defb85a1b0cf4a8534984e798d29901f1911b1811ef701a06112a580ea40129410e730060310212906310020⟩,
  ⟨165,4,[ew334,ew365,ew395,ew409,ew416],localHints 4 0x7d0ca184099ea0360106600b05402416807 0xcc647672bb947670aa49028767654543210⟩,
  ⟨165,4,[ew365,ew395,ew406,ew409,ew416],localHints 4 0x3e8200f2914048770360100581300e0a8169ea 0xdd6576765c5cbb76a545998876545433210⟩,
  ⟨165,4,[ew86,ew365,ew395,ew409,ew416],localHints 4 0x7d0f21941006102606c0200b05402416807 0xcc57bb62aa7965608070230656544323210⟩,
  ⟨165,4,[ew239,ew365,ew395,ew409,ew416],localHints 4 0x9183ca450dc1dc3082d1400100d81301602415007 0x3e63dd52c3b3aa569387212656543212100⟩,
  ⟨165,4,[ew363,ew365,ew395,ew409,ew416],localHints 4 0x7d0ca0112386102606c6400b05402416807 0xcca42a32bb740a988470230665454323210⟩
]

def nodesBlock14 : Array Node := #[
  ⟨165,4,[ew365,ew395,ew409,ew416,ew417],localHints 4 0x22460401e4328070360b52380b02628015009 0xd734434cb40110aa7099348876543432010⟩,
  ⟨165,4,[ew89,ew365,ew395,ew409,ew416],localHints 4 0x7d0ca1dc308200360100980b05402416807 0xcc647672b24aa7099480210767654321010⟩,
  ⟨165,4,[ew166,ew365,ew395,ew409,ew416],localHints 4 0x9203c8650eeac4378131400a80201b0160240382d 0x8e58dd45c86bb41a8981761545433221010⟩,
  ⟨165,4,[ew365,ew393,ew395,ew409,ew416],localHints 4 0x7d4921940d8de0540103080b02602416807 0xcc6426baa34998484720610554302100110⟩,
  ⟨165,4,[ew365,ew395,ew409,ew416,ew418],localHints 4 0x22480400252482d0ee06c3080b02628015007 0xd643344cb4aa61934340880776055430210⟩,
  ⟨165,4,[ew26,ew365,ew395,ew409,ew416],localHints 4 0x7d0f2acc3bab20400100d80b0120a80382d 0xc75bb53a337995181171321654432321010⟩,
  ⟨165,4,[ew92,ew365,ew395,ew409,ew416],localHints 4 0xfa1940206102606c1000b05402416807 0xb942932aa74091088470230665432321010⟩,
  ⟨165,5,[ew365,ew395,ew409,ew416],localHints 5 0x8710dc3e8203d69243cc3686b0d2198652a691c3bc320370c40243085e1840595e0267aa1702d0550b404807 0xfa5bdf71fddf1adda5e9d05f9d0db9c0defb85a1b0cf4a8534984e798d29901f1911b1811ef701a06112a580ea40129410e730060310212906310020⟩,
  ⟨168,4,[ew326,ew360,ew434,ew453,ew454],localHints 4 0xad16421025a4a0020346581802403808808 0xcc647672bb947670aa49028767654543210⟩,
  ⟨168,4,[ew360,ew434,ew449,ew453,ew454],localHints 4 0x56874072908070370020340c04b01004808a4a 0xdd6576765c5cbb76a545998876545433210⟩,
  ⟨168,4,[ew47,ew360,ew434,ew453,ew454],localHints 4 0xad0722c83a0840960040681802403808808 0xcc57bb62aa7965608070230656544323210⟩,
  ⟨168,4,[ew284,ew360,ew434,ew453,ew454],localHints 4 0x7481ca420ce0dc420111480340084b03003809008 0x3e63dd52c3b3aa569387212656543212100⟩,
  ⟨168,4,[ew359,ew360,ew434,ew453,ew454],localHints 4 0xad164035258840960047f81802403808808 0xcca42a32bb740a988470230665454323210⟩,
  ⟨168,4,[ew360,ew434,ew453,ew454,ew455],localHints 4 0x69d20e80e459008002045258180962900900e 0xd734434cb40110aa7099348876543432010⟩,
  ⟨168,4,[ew52,ew360,ew434,ew453,ew454],localHints 4 0xad1640dc420740020342581802403808808 0xcc647672b24aa7099480210767654321010⟩,
  ⟨168,4,[ew182,ew360,ew434,ew453,ew454],localHints 4 0x7501c8b206eca03504b1480480680103003804011 0x8e58dd45c86bb41a8981761545433221010⟩
]

def nodesBlock15 : Array Node := #[
  ⟨168,4,[ew360,ew433,ew434,ew453,ew454],localHints 4 0xad4982c80090b0240344201809603808808 0xcc6426baa34998484720610554302100110⟩,
  ⟨168,4,[ew360,ew434,ew453,ew454,ew456],localHints 4 0x69d40e80392601106e0044201809629009008 0xd643344cb4aa61934340880776055430210⟩,
  ⟨168,4,[ew34,ew360,ew434,ew453,ew454],localHints 4 0xad072ad01bb290e80340081801c04804011 0xc75bb53a337995181171321654432321010⟩,
  ⟨168,4,[ew54,ew360,ew434,ew453,ew454],localHints 4 0x15a2c8068840960043a01802403808808 0xb942932aa74091088470230665432321010⟩,
  ⟨168,5,[ew360,ew434,ew453,ew454],localHints 5 0x88910c5687441a9301cc428831021f8b22e292c1bc3e0030f406c3c8762100c1a809692a1d0110250e407008 0xfa5bdf71fddf1adda5e9d05f9d0db9c0defb85a1b0cf4a8534984e798d29901f1911b1811ef701a06112a580ea40129410e730060310212906310020⟩,
  ⟨171,4,[ew334,ew365,ew439,ew453,ew460],localHints 4 0xb11041880d1ec0360346600b0540381a008 0xcc647672bb947670aa49028767654543210⟩,
  ⟨171,4,[ew365,ew439,ew450,ew453,ew460],localHints 4 0x588450f2914070780360340581a0100a81a1ec 0xdd6576765c5cbb76a545998876545433210⟩,
  ⟨171,4,[ew86,ew365,ew439,ew453,ew460],localHints 4 0xb10f22082286203406c0680b0540381a008 0xcc57bb62aa7965608070230656544323210⟩,
  ⟨171,4,[ew284,ew365,ew439,ew453,ew460],localHints 4 0x9183ca450dc1e03103413e0340d81a01603815008 0x3e63dd52c3b3aa569387212656543212100⟩,
  ⟨171,4,[ew363,ew365,ew439,ew453,ew460],localHints 4 0xb11040352686203406c6400b0540381a008 0xcca42a32bb740a988470230665454323210⟩,
  ⟨171,4,[ew365,ew439,ew453,ew460,ew461],localHints 4 0x6a4608a1e4410080360d12680b03427c1500e 0xd734434cb40110aa7099348876543432010⟩,
  ⟨171,4,[ew93,ew365,ew439,ew453,ew460],localHints 4 0xb11041e0310450360340d00b0540381a008 0xcc647672b24aa7099480210767654321010⟩,
  ⟨171,4,[ew182,ew365,ew439,ew453,ew460],localHints 4 0x9383c8820f0ca83801a13e0a80681b01603804034 0x8e58dd45c86bb41a8981761545433221010⟩,
  ⟨171,4,[ew365,ew437,ew439,ew453,ew460],localHints 4 0xb149e2080d8e00540343100b0340381a008 0xcc6426baa34998484720610554302100110⟩,
  ⟨171,4,[ew365,ew439,ew453,ew460,ew462],localHints 4 0x6a4e08a039278340f006c3100b03427c15008 0xd643344cb4aa61934340880776055430210⟩,
  ⟨171,4,[ew34,ew365,ew439,ew453,ew460],localHints 4 0xb10f2ad43c32b08a0340d80b01c0a804034 0xc75bb53a337995181171321654432321010⟩
]

def nodesBlock16 : Array Node := #[
  ⟨171,4,[ew96,ew365,ew439,ew453,ew460],localHints 4 0x1622080686203406c2280b0540381a008 0xb942932aa74091088470230665432321010⟩,
  ⟨171,5,[ew365,ew439,ew453,ew460],localHints 5 0x8a113c5884541c93c3cc4e89b132258822ba9343c44a03712406c4888e188059740347b22303405511407008 0xfa5bdf71fddf1adda5e9d05f9d0db9c0defb85a1b0cf4a8534984e798d29901f1911b1811ef701a06112a580ea40129410e730060310212906310020⟩,
  ⟨172,4,[ew326,ew390,ew434,ew492,ew493],localHints 4 0xe51802e425a500020646583802003c0880c 0xcc647672bb947670aa49028767654543210⟩,
  ⟨172,4,[ew390,ew434,ew474,ew492,ew493],localHints 4 0x7288b06aab8078370020641c04b01804008a50 0xdd6576765c5cbb76a545998876545433210⟩,
  ⟨172,4,[ew49,ew390,ew434,ew492,ew493],localHints 4 0xe506a300458b90960040c83802003c0880c 0xcc57bb62aa7965608070230656544323210⟩,
  ⟨172,4,[ew297,ew390,ew434,ew492,ew493],localHints 4 0x74c1aaae0d20dc5c8110ec0640084b07003c0800c 0x3e63dd52c3b3aa569387212656543212100⟩,
  ⟨172,4,[ew389,ew390,ew434,ew492,ew493],localHints 4 0xe5180065288b90960048483802003c0880c 0xcca42a32bb740a988470230665454323210⟩,
  ⟨172,4,[ew390,ew434,ew492,ew493,ew494],localHints 4 0xc9d31160d46000c002045288380961d80800f 0xd734434cb40110aa7099348876543432010⟩,
  ⟨172,4,[ew52,ew390,ew434,ew492,ew493],localHints 4 0xe51800dc5c88b0020642583802003c0880c 0xcc647672b24aa7099480210767654321010⟩,
  ⟨172,4,[ew252,ew390,ew434,ew492,ew493],localHints 4 0x7501a8c006eca03504b0ec0400c80107003c06011 0x8e58dd45c86bb41a8981761545433221010⟩,
  ⟨172,4,[ew390,ew433,ew434,ew492,ew493],localHints 4 0xe54a43000090b0200645c83809603c0880c 0xcc6426baa34998484720610554302100110⟩,
  ⟨172,4,[ew390,ew434,ew492,ew493,ew495],localHints 4 0xc9d411603d2901106e0045c8380961d80800c 0xd643344cb4aa61934340880776055430210⟩,
  ⟨172,4,[ew39,ew390,ew434,ew492,ew493],localHints 4 0xe506acb41bb2c1160640083801e04006011 0xc75bb53a337995181171321654432321010⟩,
  ⟨172,4,[ew55,ew390,ew434,ew492,ew493],localHints 4 0x1ca3000c8b90960044583802003c0880c 0xb942932aa74091088470230665432321010⟩,
  ⟨172,5,[ew390,ew434,ew492,ew493],localHints 5 0x8b916c7288b4a69481ac5a8b31622b8c034e9441bc560031540cc548a62e41c1b5096942290110211440780c 0xfa5bdf71fddf1adda5e9d05f9d0db9c0defb85a1b0cf4a8534984e798d29901f1911b1811ef701a06112a580ea40129410e730060310212906310020⟩,
  ⟨174,4,[ew334,ew395,ew439,ew492,ew499],localHints 4 0x1001282000d1ed0360646601305a03c1a00c 0xcc647672bb947670aa49028767654543210⟩
]

def nodesBlock17 : Array Node := #[
  ⟨174,4,[ew395,ew439,ew475,ew492,ew499],localHints 4 0x8005e0eeac4078780360640981a0180b41a1ed 0xdd6576765c5cbb76a545998876545433210⟩,
  ⟨174,4,[ew89,ew395,ew439,ew492,ew499],localHints 4 0x1000ee2502f08003406c0c81305a03c1a00c 0xcc57bb62aa7965608070230656544323210⟩,
  ⟨174,4,[ew297,ew395,ew439,ew492,ew499],localHints 4 0x9203bab10de1e0400341580640d81a02603c1680c 0x3e63dd52c3b3aa569387212656543212100⟩,
  ⟨174,4,[ew393,ew395,ew439,ew492,ew499],localHints 4 0x1001280652a08003406c6f01305a03c1a00c 0xcca42a32bb740a988470230665454323210⟩,
  ⟨174,4,[ew395,ew439,ew492,ew499,ew500],localHints 4 0xca480bc1dc4a00c0360d12a0130342b01680f 0xd734434cb40110aa7099348876543432010⟩,
  ⟨174,4,[ew93,ew395,ew439,ew492,ew499],localHints 4 0x1001281e04005e0360640d01305a03c1a00c 0xcc647672b24aa7099480210767654321010⟩,
  ⟨174,4,[ew252,ew395,ew439,ew492,ew499],localHints 4 0x9383b8940f0ca83801a1580b40c81b02603c06034 0x8e58dd45c86bb41a8981761545433221010⟩,
  ⟨174,4,[ew395,ew437,ew439,ew492,ew499],localHints 4 0x1004aa2500d8e005a0644001303403c1a00c 0xcc6426baa34998484720610554302100110⟩,
  ⟨174,4,[ew395,ew439,ew492,ew499,ew501],localHints 4 0xca4e0bc03d2a8340f006c400130342b01680c 0xd643344cb4aa61934340880776055430210⟩,
  ⟨174,4,[ew39,ew395,ew439,ew492,ew499],localHints 4 0x1000eecbc3c32e0bc0640d81301e0b406034 0xc75bb53a337995181171321654432321010⟩,
  ⟨174,4,[ew97,ew395,ew439,ew492,ew499],localHints 4 0x2002500c88003406c2f01305a03c1a00c 0xb942932aa74091088470230665432321010⟩,
  ⟨174,5,[ew395,ew439,ew492,ew499],localHints 5 0x8d119c8005e4ac9543bc668cb192318942e69503c4620371840cc608be200099880347b62f03405b1740780c 0xfa5bdf71fddf1adda5e9d05f9d0db9c0defb85a1b0cf4a8534984e798d29901f1911b1811ef701a06112a580ea40129410e730060310212906310020⟩,
  ⟨175,4,[ew356,ew408,ew452,ew491,ew531],localHints 4 0x6207e1863082a01502e95cad83100607802806 0xddc4bb943237aa493238876545432321100⟩,
  ⟨175,4,[ew408,ew452,ew483,ew491,ew531],localHints 4 0x6207e3c00c00b8310a80c80181e02a01403257 0xddc88c8c5454b878aa54928787665431210⟩,
  ⟨175,4,[ew386,ew408,ew452,ew491,ew531],localHints 4 0x6207e1863082a01e4b0054b70310060140b806 0xddc4bb941221aa496872126545433212100⟩,
  ⟨175,4,[ew408,ew452,ew491,ew515,ew531],localHints 4 0xf107e03c30c180310a8054018064b00cc02817 0x8787d8c8b5aa78011099508787645432210⟩
]

def nodesBlock18 : Array Node := #[
  ⟨175,4,[ew0,ew408,ew452,ew491,ew531],localHints 4 0xc41861f8180c20a80541880303c0140b806 0xcca7bb7a994186743462126554343212100⟩,
  ⟨175,4,[ew312,ew408,ew452,ew491,ew531],localHints 4 0x3c44d0f01cf060308190330a80c40f00302e0140a806 0xf6e6d6c6bb43a6099458823765454323210⟩,
  ⟨175,4,[ew408,ew430,ew452,ew491,ew531],localHints 4 0x6207e18605c0f2592de00c028c206215003015 0xddc3bb23a98737366554432011001100110⟩,
  ⟨175,4,[ew408,ew452,ew491,ew523,ew531],localHints 4 0xf207e03c05d2c8c2062150030320060cc02815 0x6767d7c7b36767a13198876055044302210⟩,
  ⟨175,4,[ew1,ew408,ew452,ew491,ew531],localHints 4 0xc418605c6107e0641501880303c01403015 0xcc85ba5434a995877400110654343221010⟩,
  ⟨175,4,[ew267,ew408,ew452,ew491,ew531],localHints 4 0x3c86c06183045a7442a0320660c40f00302e0140a806 0xf9e9d92cc45b9a988417721665454321010⟩,
  ⟨175,4,[ew2,ew408,ew452,ew491,ew531],localHints 4 0xc403c30c610540661f81880300a05c03015 0xcb5aa852332995801107730654432321010⟩,
  ⟨175,4,[ew198,ew408,ew452,ew491,ew531],localHints 4 0x1888c8e70304607403f0320660c40f00302e0140a806 0xf94e9d9cc43b9a988417721665432321010⟩,
  ⟨175,5,[ew408,ew452,ew491,ew531],localHints 6 0x4748e63103f20f8e51c461b314b20c23846f8dd1b4610316601512c0328d800e3581e4ae0ce3500600b1a40b815 0x80a75e7c841e70875d70a4106c339968141960138e6034105c12965c321654328a5012014c44114803913c04103c438e34028c34420c2c428a2402001c00c61c40461440c3080040⟩,
  ⟨176,5,[ew409,ew453,ew492,ew531],localHints 5 0x6403c064300170941680a804056034230090760382100800e1540780c 0x5a2545cd945ce525a18858d515c1915c14a58d8338ccf3850f384c638d035918e5b54e5b58c5914439109380c938108390c410065110251106310020⟩,
  ⟨177,4,[ew359,ew410,ew454,ew493,ew531],localHints 4 0x7908b1be3703a01502e8407f85802407808011 0xddc4bb943237aa493238876545432321100⟩,
  ⟨177,4,[ew410,ew454,ew485,ew493,ew531],localHints 4 0x7908b55e2940b8580e82900901e02a04008a10 0xddc88c8c5454b878aa54928787665431210⟩,
  ⟨177,4,[ew389,ew410,ew454,ew493,ew531],localHints 4 0x7908b1be3703a01e422054848580240400b811 0xddc4bb941221aa496872126545433212100⟩,
  ⟨177,4,[ew410,ew454,ew493,ew517,ew531],localHints 4 0x15808b03c37c528580e8054090114221d808017 0x8787d8c8b5aa78011099508787645432210⟩,
  ⟨177,4,[ew51,ew410,ew454,ew493,ew531],localHints 4 0xf21be22c528dc0e80542c01203c0400b811 0xcca7bb7a994186743462126554343212100⟩,
  ⟨177,4,[ew312,ew410,ew454,ew493,ew531],localHints 4 0x5602595790514a370520760e81600f01202e0400a811 0xf6e6d6c6bb43a6099458823765454323210⟩
]

def nodesBlock19 : Array Node := #[
  ⟨177,4,[ew410,ew433,ew454,ew493,ew531],localHints 4 0x7908b1be05c0f212216048080dc0b01d008815 0xddc3bb23a98737366554432011001100110⟩,
  ⟨177,4,[ew410,ew454,ew493,ew525,ew531],localHints 4 0x15a08b03c05d090dc0b01d0088a40241d808015 0x6767d7c7b36767a13198876055044302210⟩,
  ⟨177,4,[ew54,ew410,ew454,ew493,ew531],localHints 4 0xf21be05c6e08b1481d02c01203c04008815 0xcc85ba5434a995877400110654343221010⟩,
  ⟨177,4,[ew267,ew410,ew454,ew493,ew531],localHints 4 0x5682fc6f8a565241c3a0a40ec1600f01202e0400a811 0xf9e9d92cc45b9a988417721665454321010⟩,
  ⟨177,4,[ew55,ew410,ew454,ew493,ew531],localHints 4 0xf203c37c6e0740ec22c2c01202005c08815 0xcb5aa852332995801107730654432321010⟩,
  ⟨177,4,[ew198,ew410,ew454,ew493,ew531],localHints 4 0x1e4cb4830a5658420458a40ec1600f01202e0400a811 0xf94e9d9cc43b9a988417721665432321010⟩,
  ⟨177,5,[ew410,ew454,ew493,ew531],localHints 6 0x4808fe3c8459a68fd1f46fab64242963e47b8f51e46e0586641d1088a48f004a3b81e4201da3b0110211d40b815 0x80a75e7c841e70875d70a4106c339968141960138e6034105c12965c321654328a5012014c44114803913c04103c438e34028c34420c2c428a2402001c00c61c40461440c3080040⟩,
  ⟨178,4,[ew361,ew414,ew458,ew497,ew531],localHints 4 0x810521e63982381502e84c7202109007827851 0xddc4bb943237aa493238876545432321100⟩,
  ⟨178,4,[ew414,ew458,ew486,ew497,ew531],localHints 4 0x810526663500b82108e34c2401e02a13c28a13 0xddc88c8c5454b878aa54928787665431210⟩,
  ⟨178,4,[ew391,ew414,ew458,ew497,ew531],localHints 4 0x810521e63982381e4280548502109013c0b851 0xddc4bb941221aa496872126545433212100⟩,
  ⟨178,4,[ew414,ew458,ew497,ew518,ew531],localHints 4 0x19a05203c3cc6a02108e0542405142836427817 0x8787d8c8b5aa78011099508787645432210⟩,
  ⟨178,4,[ew78,ew414,ew458,ew497,ew531],localHints 4 0x1021e61486a0e608e0541084803c13c0b851 0xcca7bb7a994186743462126554343212100⟩,
  ⟨178,4,[ew312,ew414,ew458,ew497,ew531],localHints 4 0x668159999671a8398698d908e0840f04802e13c0a851 0xf6e6d6c6bb43a6099458823765454323210⟩,
  ⟨178,4,[ew414,ew435,ew458,ew497,ew531],localHints 4 0x810521e605c0f215218120278e604211c28815 0xddc3bb23a98737366554432011001100110⟩,
  ⟨178,4,[ew414,ew458,ew497,ew526,ew531],localHints 4 0x19a85203c05d0a8e604211c288d309036427815 0x6767d7c7b36767a13198876055044302210⟩,
  ⟨178,4,[ew80,ew414,ew458,ew497,ew531],localHints 4 0x1021e605c730521a611c1084803c13c28815 0xcc85ba5434a995877400110654343221010⟩
]

def nodesBlock20 : Array Node := #[
  ⟨178,4,[ew267,ew414,ew458,ew497,ew531],localHints 4 0x66a1cc798d49025a0238d31b20840f04802e13c0a851 0xf9e9d92cc45b9a988417721665454321010⟩,
  ⟨178,4,[ew81,ew414,ew458,ew497,ew531],localHints 4 0x10203c3cc730471b21481084809e05c28815 0xcb5aa852332995801107730654432321010⟩,
  ⟨178,4,[ew198,ew414,ew458,ew497,ew531],localHints 4 0x20520c928d49044a4290d31b20840f04802e13c0a851 0xf94e9d9cc43b9a988417721665432321010⟩,
  ⟨178,5,[ew414,ew458,ew497,ew531],localHints 6 0x48f91c4082910d91b23079a1642a35245c8a913220730214b411d0a0d390e1224301e4263664285109f2100b815 0x80a75e7c841e70875d70a4106c339968141960138e6034105c12965c321654328a5012014c44114803913c04103c438e34028c34420c2c428a2402001c00c61c40461440c3080040⟩,
  ⟨179,4,[ew363,ew416,ew460,ew499,ew531],localHints 4 0x8185e19a3242281502e96c6402005407816834 0xddc4bb943237aa493238876545432321100⟩,
  ⟨179,4,[ew416,ew460,ew488,ew499,ew531],localHints 4 0x8185e5642800b82008a27c1501e02a0b41a25b 0xddc88c8c5454b878aa54928787665431210⟩,
  ⟨179,4,[ew393,ew416,ew460,ew499,ew531],localHints 4 0x8185e19a3242281e4b80546f0200540b40b834 0xddc4bb941221aa496872126545433212100⟩,
  ⟨179,4,[ew416,ew460,ew499,ew520,ew531],localHints 4 0x15985e03c3345002008a054150344b82b016817 0x8787d8c8b5aa78011099508787645432210⟩,
  ⟨179,4,[ew92,ew416,ew460,ew499,ew531],localHints 4 0x10319a178500c908a0541002a03c0b40b834 0xcca7bb7a994186743462126554343212100⟩,
  ⟨179,4,[ew312,ew416,ew460,ew499,ew531],localHints 4 0x566481591231403244f8ac08a0800f02a02e0b40a834 0xf6e6d6c6bb43a6099458823765454323210⟩,
  ⟨179,4,[ew416,ew437,ew460,ew499,ew531],localHints 4 0x8185e19a05c0f25d1c00a8168c90401141a015 0xddc3bb23a98737366554432011001100110⟩,
  ⟨179,4,[ew416,ew460,ew499,ew528,ew531],localHints 4 0x15a85e03c05d2e8c90401141a09f0542b016815 0x6767d7c7b36767a13198876055044302210⟩,
  ⟨179,4,[ew96,ew416,ew460,ew499,ew531],localHints 4 0x10319a05c6485e13e1141002a03c0b41a015 0xcc85ba5434a995877400110654343221010⟩,
  ⟨179,4,[ew267,ew416,ew460,ew499,ew531],localHints 4 0x56a4cc668a065649c2289f1580800f02a02e0b40a834 0xf9e9d92cc45b9a988417721665454321010⟩,
  ⟨179,4,[ew97,ew416,ew460,ew499,ew531],localHints 4 0x10303c334648451581781002a05a05c1a015 0xcb5aa852332995801107730654432321010⟩,
  ⟨179,4,[ew198,ew416,ew460,ew499,ew531],localHints 4 0x206cbc9b0a065c4e02f09f1580800f02a02e0b40a834 0xf94e9d9cc43b9a988417721665432321010⟩
]

def nodesBlock21 : Array Node := #[
  ⟨179,5,[ew416,ew460,ew499,ew531],localHints 6 0x49b93440c2f25e93326066ab74ba2824bc9692b2506482066c1152e09f9260aa4901e4b62b24883405b2400b815 0x80a75e7c841e70875d70a4106c339968141960138e6034105c12965c321654328a5012014c44114803913c04103c438e34028c34420c2c428a2402001c00c61c40461440c3080040⟩,
  ⟨180,4,[ew18,ew30,ew38,ew43,ew45],decodeHints 0x7e0fc0000b0780f0000130600c00180707a0f40001a0640c8018080660cc0280c0300600100005e0bc050030580b00100505c0b801006⟩,
  ⟨180,5,[ew19,ew30,ew38,ew43,ew45,ew46],localHints 5 0x601786505802830813094038170140c4068230090101080380c93809c0100001600c02806 0x35a29339b149820ef72d89525273926312c08f239ad62d4a4a0e53148320c4208400⟩,
  ⟨180,5,[ew15,ew30,ew38,ew43,ew45,ew46],localHints 5 0x300fc0582c0c20c0170140c4068190420140080980001200c0780700a03004006 0x2f7520ca59ad64569452d1342652312315410f439ad3058c2096a5a9284a0e62906310400⟩,
  ⟨180,4,[ew16,ew30,ew38,ew45,ew46],decodeHints 0x30060010000580b0010050780f00001305c0b80100607a0f40001a0660cc0280c05e0bc0500307e0fc0000b0600c0018070640c801808⟩,
  ⟨180,5,[ew21,ew30,ew38,ew43,ew45,ew46],localHints 5 0xe01783f0c60501e0130600242e80a07a0681900e0660300100b0012744e80300e01404006 0x35a81f39813183a2f7b0ab53d27324a31801ef3b9ad2316b1292941d07310a418820⟩,
  ⟨180,5,[ew17,ew30,ew38,ew43,ew45,ew46],localHints 5 0x300fc0582c0780c01703d0340c8070330140080980001200c0780700a03004006 0x2f7520ca39ad64569450e734265231e315021043dce3358c1896a4a128398e628c8310020⟩,
  ⟨180,4,[ew22,ew25,ew33,ew45,ew46],localHints 5 0x3035c0a16a1ac5b00580308c3540100a272000098050d801843042 0x9cd2694a29340cd7bd09338cd6306b5292831cc52106010820⟩,
  ⟨180,5,[ew22,ew25,ew38,ew43,ew45,ew46],localHints 5 0x30140410631281295c05d01600c0780c05c0080506200004c0709d00a01843008 0xbdd47b592a3d4ef551493cce6948b18292a3bcef7398d0b16b524e8398052006310820⟩,
  ⟨180,4,[ew22,ew29,ew37,ew43,ew45],localHints 5 0x1f80b18035c5c8d60043840001311800c048630d817443033 0x8c5307bc89738866b449630465ac625292839cc50106000820⟩,
  ⟨180,5,[ew22,ew29,ew38,ew43,ew45,ew46],localHints 5 0x961401f863572250250020161180780c02809c1e8000260c80180906602043006 0xbdd68b5965ad50fa5173449072c4a4841e87a1c52158d0b00b5012941cc62906300820⟩,
  ⟨180,5,[ew22,ew30,ew33,ew43,ew45,ew46],localHints 5 0xc02f0ca18c058030ba0504001a08cae00780c0580080506100004c0489d00a1b003806 0xce547c612a3dcf5b2a4a3d4f5a5153548f13c1ef2b98d1316b524e8398252046310400⟩,
  ⟨180,5,[ew22,ew30,ew37,ew43,ew45,ew46],localHints 5 0x1c02f07e0080584a0baae44001a08c0380780c01409c1e0000260c00180900e1b002833 0xce568c6165bdd15b5aa8aa285716735c911440af2b98d1302b5052941cc62902310400⟩,
  ⟨180,6,[ew22,ew30,ew38,ew43,ew45,ew46],localHints 6 0x300bc1f80b0c6ce84a04a6721759c0141000682333701d27c13802576028000410272784e8035740240780510c1b006006 0xd42380c8e041034c3483a219088638e21020c36122084834d32080341014e7c541078e38334d14b74534d30b2c32081467052086c618241005868141065860234d0565c134d3165822080535412085134c10810c514208249041138e45040f38e30d34c2cb30d34c2cb288209186248207186082102144083002040⟩,
  ⟨180,5,[ew11,ew30,ew38,ew43,ew45,ew46],localHints 5 0x300bc3283c0260c0170140c4068230330040280580001c0240180700a02006006 0x2f75a2d652d154256a58e9444e5219a315c10f439ad3098c1856a5a9284a0e62948310400⟩,
  ⟨180,4,[ew12,ew30,ew43,ew45,ew46],decodeHints 0x300600100005e0bc0500307e0fc0000b05c0b80100607a0f40001a0640c8018080580b0010050780f0000130600c0018070660cc0280c⟩
]

def nodesBlock22 : Array Node := #[
  ⟨180,5,[ew24,ew30,ew38,ew43,ew45,ew46],localHints 5 0x602801407e02c1603c06001c1703d0340c80403301e0280101300002401ca010c01406006 0x35a49f39c16f73dab548a943a2732ca31482103bdce2b58c12d4941d073148218820⟩,
  ⟨180,5,[ew14,ew30,ew38,ew43,ew45,ew46],localHints 5 0xe01783f07804c1805d0140f40d03206603c0100b0000380480300e01404006 0x2d679eb5792943a04f18a733ca3120e10781ce3b58c2056b1292941d07310a41886208020⟩,
  ⟨180,4,[ew25,ew29,ew38,ew42,ew45],localHints 5 0xb207804c6b8841aa0146d8000161403608c00e0b84e832 0x840c87bd0e6b4ca63048118a25ac4a4a507018a02100300820⟩,
  ⟨180,5,[ew25,ew29,ew38,ew43,ew45,ew46],localHints 5 0x961415e0820c60f00984a05c1880704202809c1e8000160c81980500e0204e806 0xbdd68b5975451079cd6494911810837bdc83a04d089841900b5012941cc62948300820⟩,
  ⟨180,5,[ew25,ew30,ew33,ew38,ew45,ew46],localHints 5 0x60160610261404100505c0503101a084ae00700805e0280106500002c430070061b004806 0xd6927ce52a3e0f7b5a493d4e6a52734c8f13c1ef2398d1316b524e8398242906310400⟩,
  ⟨180,5,[ew25,ew30,ew38,ew42,ew45,ew46],localHints 5 0x60280820580f00984a05caf03101a01c0202100501e0081383f00002c0486c06000c03832 0xd6947ce707a9ef7532d63d5947b273548f13c1cf2398d62c4a48908398452086310400⟩,
  ⟨180,6,[ew25,ew30,ew38,ew43,ew45,ew46],localHints 6 0x301419e8820580f00984a6780b99d8140c40682133701f2881380a57a0080004101603801ca110c0155d00713a1b004006 0xd3a32cc8cb38e34c34342228e88a41084e38334d28b80a34d30b2c639f1107c438e19018c35e19d78634d31d74429c18318628611b10239a05868138e65860234d0565c134d3165810810ca2820820861814d50461944d349041138e45040f38e30d34c2cb30d34c2cb0822422892061871041c6185104083002040⟩,
  ⟨180,5,[ew10,ew30,ew38,ew43,ew45,ew46],localHints 5 0x700bc1f82c0c204c0385d07a0681900e0840500500200002c0180900a03003008 0x2f749ed6496b539a94524f33c8a42c610485ef3b9ad2b16108949420e6398a42906308820⟩,
  ⟨180,5,[ew13,ew30,ew38,ew43,ew45,ew46],localHints 5 0xc02f0ca0b01e01305c0f40d04606603c0a00a0040000580300a01c03008 0x2b539a9449cd33165238e3134043189ef385ce335810816b1a92741cc5314841886208020⟩,
  ⟨180,5,[ew29,ew30,ew37,ew38,ew43,ew45],localHints 5 0xfc0583c0260c00484b0a018c1e81a06403819ab90280181c00005e00c430050041b00505d 0xd6919c6117b58d5a51689cd6694a31441ef339ad2314b129290a0e7098242906310400⟩,
  ⟨180,5,[ew29,ew30,ew38,ew42,ew43,ew45],localHints 5 0xfc0584b0a00f00983000e18c1e81a064af00a00606603c0c00013a00c0506c0580080282e 0xd6919c61a8bded64569434e5268631441ef3398d2316b0a92912046398452086310400⟩,
  ⟨180,6,[ew29,ew30,ew38,ew43,ew45,ew46],localHints 6 0x4b0a0cfc1f86367c0f00983007a0681933b01c0cd9c00f0280081d00b0820025209d012af401ca310c01d5d80504e02036006 0xe4e44039104d338f3894e32c38cb4d326224f3a125084938e3d04044e01838064d311f10f39e11d78438e3dd74625c10b70424918b1800400d34c104104e6c069b00e38f69a0496405d90092585d70445805160041155140414814d23d041138e3d040f38e34b2cc24930b2ca2492061871041c6185104043081000⟩,
  ⟨180,5,[ew6,ew30,ew38,ew43,ew45,ew46],localHints 5 0x300bc3282c0141840984a07a06819033004050058000120380180701e01404006 0x2f75a2d69ad15426945cd12446103116a581ef439ad0198c00d6a5a9284a0e62948310820⟩,
  ⟨180,4,[ew7,ew38,ew43,ew45,ew46],decodeHints 0x300600100005e0bc0500307e0fc0000b0580b0010050780f0000130600c00180705c0b80100607a0f40001a0640c8018080660cc0280c⟩,
  ⟨180,5,[ew30,ew32,ew38,ew43,ew45,ew46],localHints 5 0x601780a07e02c1603c0260c00381401c03c1700207a0000d0320060201980501929436006 0x35a62b39c1ef755ab56129454e523c60c4a92a79dc46b5805ad49420e62948300820⟩,
  ⟨180,5,[ew9,ew30,ew38,ew43,ew45,ew46],localHints 5 0x2585007e18c1e0130600501e81a0640cc060020160000480300e01404006 0x2b571a947127331e5270a31341ef20c0e081ad3316b2054a12508398e6290a41886208020⟩
]

def nodesBlock23 : Array Node := #[
  ⟨180,4,[ew30,ew33,ew37,ew42,ew45],localHints 5 0x851063680588613a0f40001a1ac0bc6a82c00c23018008 0x840c97bc89219847392d09981091615292839cc32948310820⟩,
  ⟨180,5,[ew30,ew33,ew37,ew43,ew45,ew46],localHints 5 0x700bd5f0650581840482707802c1809d0ba0281e8000341182100700c0cc02808 0xbdd48b59554510e9ce48720916102a805ef439ad091815ad434a50730c601948310820⟩,
  ⟨180,5,[ew30,ew33,ew38,ew42,ew45,ew46],localHints 5 0xc02f0ca0b15f06102601c1383f0162181802e0040f40001a08c024210060180c801808 0xce569c62e99a6d65d5344ce467482b886104bc26705ad631645292821cc42908310820⟩,
  ⟨180,6,[ew30,ew33,ew38,ew43,ew45,ew46],localHints 6 0x1805ed043282c6800283081394e09d5f84101600c0282e0040501e8000cc0682309d012cf02108600ece4064a60d80195d008 0x104e45cf9174d340f40c7a32d38cb79e8934cc4102d784b4103d75c84e01de8074d37de7884101dc7474103dc70720730b2c82086d249a4d36924994d33d04185d761040f5d72085832d620c5431d50935004940134c24823d044239109040f38e00b34230208b080280147242202087085185003002102083080040⟩,
  ⟨180,5,[ew5,ew30,ew38,ew43,ew45,ew46],localHints 5 0x700bc1f86307804c1800905c1880d0080840280a00200002c0180e01e01403806 0x2f751ed6516b539a9448a733ca312c1ef524ee3b4a42b04b10d49420e6398a42904310400⟩,
  ⟨180,5,[ew8,ew30,ew38,ew43,ew45,ew46],localHints 5 0x180a02081603c0261281703d0340cc0600a0040000580300a01c03008 0x29439a7341cd23163138e1033dc3189ad3858c32c010814a1a50741cc5314841886208020⟩,
  ⟨180,5,[ew30,ew37,ew38,ew42,ew43,ew45],localHints 5 0x1f80b0700bc1e013060af80c09d10c0b01e8000340c8018080ba028198050180b801006 0xce598bdcccb5ab5652734c886792310b02982426785ce6b58b5292839cc02948310820⟩,
  ⟨180,6,[ew30,ew37,ew38,ew43,ew45,ew46],localHints 6 0x1c02f6840fc1e013060d000480207410405ca913aafc038270ba0299f03d0001980d0320060384303300ace8064a80d80215d806 0xf4a56549594923ce3cb4a475491d4922e32ce3e22d988b3cf39964724751248924924f8478211cf3ce82024b7c775f1cb2de75d24970349c39965b3cf69964e3cf60a2972cb5ca2962cb2545431c70124c251309248044038f40035000f3ce34d08b30028c00b2c22821472002480071c5185003002102083080040⟩,
  ⟨180,5,[ew3,ew30,ew38,ew43,ew45,ew46],localHints 5 0x301401f80b0580f0180070ba2000d0460180500100a00004c0700301201407806 0x2f749ed6512b53d27348a5239a312412f4a8ee3b48c2144112d2a4a0e63988520c4110400⟩,
  ⟨180,5,[ew4,ew30,ew38,ew43,ew45,ew46],localHints 5 0x1805e0fc058631281281703d0340c804002014000098030120140300c 0x29441a73392523451041ccf3148e20dad4058c32d4a224010810741cc53148320c4208020⟩,
  ⟨180,6,[ew30,ew38,ew42,ew43,ew45,ew46],localHints 6 0xc03f0160281d0410120b1a103c0260c1a08079562195f82705c0099f83d0002700d09d06400d9e8089541b15e83300c0140780c 0xf4a58d49634923ce3ca30a51248c30c30f90a8e428f3ce8e330c88649239b6e13cf81b6ce3cf3147c628a09279851e61248274238f7026dc08f3ce6db60a68231a08a2986580960815c10560425420d24c851321248344338f4033500cf3ce34d20a2c330b0ca2882480c60c01c00060031430021030440c2080040⟩,
  ⟨180,7,[ew30,ew38,ew43,ew45,ew46],localHints 6 0x180560be5883f13802c164b00140f0330130612bc0480704e0b8014ae0280f4000411500684e8320072b40700810c0cc3600600b2b00780c 0x4115685e23e85e25559d13d134b7e65d95663597df94b54b34f46440b8a434b4518cf8a21c35615d87e11d85558037c31cf45e40371e1c345174f71c1d82db34365b1c32cb6986581445565c84d61485555044c414f45240439214445140f38e1482cc34424c1442cb2882481400c61c40461440c3080040⟩,
  ⟨182,5,[ew156,ew177,ew193,ew204,ew206,ew208],localHints 5 0x13432619cf283529a1cc1e03701a5301e8760080042b0b30400000b81000a05408806 0x30aba8ca598d6a9a9452c93912313121053c2e485ad3058c2096a5a9284a0e62906310400⟩,
  ⟨182,5,[ew157,ew177,ew193,ew204,ew206,ew208],localHints 5 0x32619cf28354680f00803746e2cc1e811066010008560400000b80700a05404006 0x149ba4c9518d6a9a9448c7370e52346104800f701ad3316b1894952508398e628c8310020⟩,
  ⟨182,6,[ew161,ew177,ew193,ew204,ew206,ew208],localHints 6 0x9a1930ce02cf286029a7bcbb0cd0b4034a625f0e63242295627a004f700496609459856964388001600404700b8052be3280a806 0x1142531248c4244524894091d248741025224930988d8e232124d25d49215080549245041d5df14c7c55d778c31d2491477052491871d449205a6c149245a69431905764130c6175d42490555812490d55411810c51431944524934104d24914103cd34e30c38d34230c2c924a1c72892481c71861021440c3002040⟩,
  ⟨182,6,[ew172,ew177,ew193,ew204,ew206,ew208],localHints 6 0x1343262c45f83b1660d51a0072fa0dc06b431321d80b9a527a0100095c04a1589f07308a000af91c00a580080e232a32808806 0x144a439144e4a35114444a22d144b4925114443a12df84b38e81f7c745e1527854511d21c730770e75c31b1ce1c52c51c41c72c714815445a05968145151964138160c31838e04c0410c10cb2c30d72471c15560471c95555124834514d248345140e38330c3ce38d30c1032822ca2471c31452071c6145103002040⟩
]

def nodesBlock24 : Array Node := #[
  ⟨182,6,[ew174,ew177,ew193,ew204,ew206,ew208],localHints 6 0x6c01d8353de0f01001006e034bf03d08a044ab03302ed109e8040021cc2b15c1c402c0025f2be01c0282527c02065006 0x442238f3ce41048f3c940974f3dd41024f24938928428a38a2612453e071081c3cf15014538518418638615f15c25e15d78524971d7003db59a6d63cf01a0000c00ce3830d95896005d80092565d65455004d40051484d34904033cf4504033cf10334138d30a2832492ca2832492061831451c6181145103081000⟩,
  ⟨182,6,[ew177,ew188,ew193,ew204,ew206,ew208],localHints 6 0x1343261f44b03b1660d4023451304f4b8825000328028370020351b8080ac5f8398e20401d808015238018b0011 0x166602cf3cb65f58f3c865e1cf3c765958f3c82dd1db7472cb71b6d63da1596853cf59964524560b2d824914b1450450471c105758e3813cf58e3813cf5492412cb5092522cb2014d21d320145215108f40039000f3c238208b08c24d30b2822420070022020870800c01051820c20850840c40010020c2083080040⟩,
  ⟨182,6,[ew177,ew190,ew193,ew204,ew206,ew208],localHints 6 0x1340760d40217d0780800834627a1ccb88e201601c1b80101a0942b03d000114089760660140a9ef23802065006 0xe76035040d75d61040b74b69041a75d2d02cb34b4ce4d33532df2c641e65d79941019d18604604d34105c64b6c669b18b2d969960f3c14105cf3c141038158134d5534c12cb5134c12cb3814811860104493d12504003c000d00238208d08010024b30028c00b2c92891461c0207006185105001002102083080040⟩,
  ⟨182,7,[ew177,ew193,ew204,ew206,ew208],localHints 6 0x4d0c98670167941d8b306a0111a0072fb2e01e4b70400408683700285c06a3704a0202b17e96c1cc1e8e20012d4228112ec0ccab00600b2d00b815 0x4d68aa6515d74d18a95965d730b88b65b5d731b8a264b5cb30b44b4e792832746694b90b1c35e365a8a31da5d75838831c33834e04614e039f7834431da2dd3036dd3032cb71a6da1445d86485581485d75845441444444d23944d24503c43841482cd30424d3042cb2882481400c61c40461440c3080040⟩,
  ⟨185,6,[ew367,ew379,ew383,ew384,ew385],localHints 6 0x10d300e4036124f68c80300e41503f02402d080dd002d1c0c8e3582354012c00a43840013f0bc1d84603300639c0f042 0x3cd7e28604d33e07de74d4d320944921c4d321c4512094c920935b21621b21634d2092090834da09709a0974d30830830832c309934d0992cb0833430972580835980832490975964044d45464544864d348444440434e3c02ce30034d3042c420624a2041ca2042492061c60800c50840450840c3080040⟩,
  ⟨186,6,[ew355,ew397,ew402,ew403,ew404],localHints 6 0x4397206c249ec07084478b4801a3d1610d627c36ca00451480d40082d08e0281e00002004c460050643a00b846 0x54a7a07cb34d54b79d70a34d4485c845034d4505d744834844829b44645b44628a44844858335968f5d960f34d6035c35832945402d44c028a4c32c344f21244341244320844f40f08434e08708e08734d0840840842c408c28a08c2cb0842840872090841890842080871860810c50840050840c3081000⟩,
  ⟨188,6,[ew345,ew441,ew445,ew446,ew447],localHints 6 0x4397406c249ea09684878349008439618d7194368a082014a0dc008340420501e800022068460060603a40a84a 0x54a7a07cb34d54b79d70a34d4485c845034d4505d744834844829b44645b44628a44844858335968f5d960f34d6035c35832945402d44c028a4c32c344f21244341244320844f40f08434e08708e08734d0840840842c408c28a08c2cb0842840872090841890842080871860810c50840050840c3081000⟩,
  ⟨191,5,[ew413,ew457,ew496,ew512,ew532,ew533],localHints 5 0x1020e4428120c00106003800e1282d00101a2e40c04b0100442300901c03c0800c 0xbde49649924c130b5984ad6092528464d924c5307bc22738646358b4a92839cc02948300820⟩,
  ⟨191,6,[ew360,ew413,ew457,ew493,ew496,ew532,ew533],decodeHints 0x408810080600480458a214428380300040088b03022c0c0120121803000d008060600180701282500e01203c2611d01e1682d00401a0605c8180961182300901c0302c90f01803007ac4074010b08040300e00c03807c024a10090741325d83a00e01c04008⟩,
  ⟨191,7,[ew360,ew413,ew457,ew496,ew532,ew533],localHints 6 0x810b12f01cac5694214300c009405c2d00d17212c2301501c43cb0801008154158180705080903e01203c038590980e806008 0x38c3e43a34243a33cf38c40c8074218893e18094107c73c73892de38731e3872cb38930c0c64100da3dd0da4100c63cf0ce30c0c62dc0c630c0c32cb0da4db0c61db0c64d30da1c710141011461911441010161810e30c10159710130c1045961141d51014d51011c71144d30c10c10c31860c31120c24100c33cf0d14100c23cf0ce30c0c32cb0cd30c0c32cb0c82490c31c70ca2490c81c70c30c50c21850c40c00c2040⟩,
  ⟨191,5,[ew413,ew457,ew480,ew496,ew532,ew533],localHints 5 0x204320b20080241a8830701280805a0022100c04b01c048060110101080380f 0xb5a695d573a51e95cd737a5e9948c78c5618412f738e10b5a15b1635292819cc31948310820⟩,
  ⟨191,6,[ew390,ew413,ew454,ew457,ew496,ew532,ew533],decodeHints 0x4088100806032064032010590b20700600380458e20c418180701282500e00e004008740301d00c03e01c5080701000e1682d00401021042018096020072c60841080380f01016487808074010b08040700601c0180120242600723a01c1d03e97a0e806008⟩,
  ⟨191,7,[ew390,ew413,ew457,ew496,ew532,ew533],localHints 6 0x810b0190594be06ab1da58830940782d00d10812c8784202a03cb08010080ec158380300380484c23a040038590180f81d008 0x38b3e43a34243a33cf38b40b08a41009a3e209a41008a3cf08e32108a2e108a30c0822cb78541f8063df7864107453c53862dc38531c3852cb38630c08529b09269b09228a08568510041011361911341010060010e2d71005971002cb10459608008008228a0821151131541004941001451134920814100823cf0914100813cf08e30c0822cb08d30c0822cb082089081289088186082145087186082145084083081000⟩,
  ⟨191,7,[ew409,ew413,ew457,ew496,ew532,ew533],localHints 6 0x15a0e4da8b20241d01a8c002022c251a806e0341586a076154b08040022d0258182840241f00e23a01c2600f0b20e808808 0x54d42355e3e355e41054d3cd54a3e24df42285f3cf54a40a4df36054a7a054a34d4df79e5463dd49b41d61b3cf54640649b35c54669c54634d49b69a4c62194842996042084c62860d53d70c15970c13cf0c35960c10c10c334d0d50d40d328a0c12080c128a0c32080d21860c11040c11860c31040c24100c33cf0d14100c23cf0ce0cc0c234c0c928a0c32080cb28a0c92080c51860c31040c71860c51040c30c00c2040⟩,
  ⟨191,5,[ew413,ew457,ew477,ew496,ew532,ew533],localHints 5 0x15a1904280401a038300830700480781006e00442018096118048110101080380c 0xbde6855945ad5e8551533a0e8915c5545418410f095c10b5815ad434a507318a31908310820⟩,
  ⟨191,6,[ew410,ew413,ew434,ew457,ew496,ew532,ew533],decodeHints 0x568ad01a06032064032024428850700603006001a01c418830300e0038095920e80696101a12c0c04b0300380480f00e02006ac81082100c04b08c118048080841080380c010164878080020042c0180b00601f0092840242600723a01c1f03a97e0e808808⟩
]

def nodesBlock25 : Array Node := #[
  ⟨191,7,[ew410,ew413,ew457,ew496,ew532,ew533],localHints 6 0x15a1904286003220c1c4c0094b25a610f10812c2300e08403c0600d0020ac2c01807c50809009098474080070b20441d008 0x4c42304d3a304d41004c04c0487e20494220497df04840838976138832138875d38930c0444200457e00454100447c438531e38475e38430c38575d68451b71221b6925146442040400400414100410d80ce3170c05970c030c0c35960c02150d15150d12080c05000d11130c04930c01040d149104104f04140f04e34d04130c04e34d04130c04b24904120804a249041208047145041104046145041104043042041000⟩,
  ⟨191,7,[ew413,ew434,ew457,ew496,ew532,ew533],localHints 6 0x810b0190428601060e08e9610080ac0700f0753041bac8002d30068840300ec258460120782100709805c0605921e0441f008 0x38f6e43a34e43a36db38f4cf04b4d304a6e204a4d304b6cb04e7a104b3e104b79e0413cf1c84d31c66e01c64d31c86c81ce3df1c879f1c83cf1c779e0480480412cb0411dd0574d30416db05c4d30576db04e34d0413cf05a34d0413cf0410590572cb0470580572085004d55824555024d34804403823d03803503803cf38234d0402cc04528c0452cb0402801c52091c01891c02081c51850400400421020420c2040040⟩,
  ⟨191,7,[ew413,ew453,ew457,ew496,ew532,ew533],localHints 6 0x810722140905806a010349610305081f03a00ead81b80101a2e4158380aa044459a708c6500483b01c2d00805921e0202600c 0x4507a446052446079e4505104495232217a332151444978922142244982244941022182005151f04579f04551404179e04504504141005105d0481c70452490451c70412490584d304151405c4d305851404f05b05841b0591c704124905a1c705924904105705815744251558e4d528e5144424c228e4124423524424103ce34d20224b3001cb2802492021c20401400421820421420400400400400421020420c2040040⟩,
  ⟨191,7,[ew413,ew454,ew457,ew496,ew532,ew533],localHints 6 0x810b01904291d1060e0250010e80f8a1012020168020191080601584b984119630096960382100709803c0605921e0441d008 0x5256406346406355505205204c52205856205851404c54c4587a144c4a144c79e4584920480480415550411e01d149f1c879f1c84921c779e1c829d1c631d1c628a1c830804105c04155c0516db0414920516db04149205a61804130c05961804130c04705704120804055604251604255504050044249344041344049244241034030e3c528e34530c2c02801c52091c01891c02081c51850400400421020420c2040040⟩,
  ⟨191,7,[ew413,ew457,ew492,ew496,ew532,ew533],localHints 6 0x408390ce5840c8380740241a8041060402c04c23a6981b80101a210158180760443a0b40241648783e2e2108ae00800e1540780c 0x45072545952545971c45051021152420b72420b51420871c20b20b20841021122321f86120851422286121f51420f22021f41020821e21f2de44351d59a71d1da5144437031da41b44365b4434103da6592032c32010812012c12032032032032016012015c120320344451558e4d514e5144444c414e4124443524444103ce34d2042c42003002002c02042042042042002802002402042041400c61c40461440c3080040⟩,
  ⟨191,7,[ew413,ew457,ew493,ew496,ew532,ew533],localHints 6 0x810b050842801116048300830701282611d0201680200d1080601584b08c0241f00e0b243c0883a9861096200800ed280780c 0x21256422346422355521221220e20e2085552083623516e134e4a134e6db34d4922082202085602117df2084922117df20849220d21e20838e20351d21755d21751420354345749c4436dc4434924576db34331a34139a34130c34338320320321765721761720320320455620951620955520450444949344441344449244941034438f34030f34038e3443042042042092c92092892042041400c61c40461440c3080040⟩,
  ⟨191,7,[ew413,ew457,ew496,ew531,ew532,ew533],localHints 6 0xac8040b00e44281207c5080f0351060401c04c23a05c250b406e004420180560442585921e0541d25308c0241d80e41a108f480800e1540780c 0x35435434d59634d4e934d36834d59635336734d51434a5a636426636459634a34a4e47654ca5254ca75d4e451434a34a3618e13618a134a34a3435a035e0a035e5963433434de51f4c375f4c35144de75d34334335a71a35a6da3433431c32193012991c12082432833445973526173525963443444d25154c44554c45144d245134434434e40e34e3ce34434414428b30020b14028a2442041400c61c40461440c3080040⟩,
  ⟨191,8,[ew413,ew457,ew496,ew532,ew533],localHints 6 0x810b13341cccc10b32c0903599401041cc90200e0254c82c20dc00cc701a2104f01898c0442594208c0266280e23a1088780800f3100780c 0x4507a85e756846779e99055030a5655e17a532155590a78a3216a344a42344a69a8a14101c35605db7a01db5557c37831db41d44369d44341071b69a1c32193012991c12086032831445565ce4d614e5555044c414e4124443524444103ce34d14428b30020b14028a2442041400c61c40461440c3080040⟩,
  ⟨192,6,[ew362,ew487,ew498,ew532,ew534],localHints 5 0x62084db0a10901041785a0321742a85208c1100f01514c13cbb804058008050300060240393f04401406033 0xd299fd7abfd798cd2b4ae9ee7eed9cd6ef7d1d87a9d39a9959a9929a9d4790598942f89418c906e19494a906969054a95694940e790633904e794230188621b98f1b86d189821894b1952b1954a18922194e8188c8188e7194c51906018820⟩,
  ⟨192,7,[ew362,ew415,ew459,ew498,ew532,ew534],localHints 6 0x31042284750480320bc3006309405c2d00d0ba0502301501cd34208a81200102a82b0040283680301203c0282804405806006 0x44b3a436336436338e44b34b4487c88603a28607df44838834829e3472de34728a3482c80c661d0da39d0da6180c638e0cd2cb0c629c0c62cb0c328a0da2080c61db0c62080da1c710139911461911438e10161810d2cb1015971012cb1045961142081014d51012081144d30c10c10c31860c31120d10d00c338e0cf0cf0c338e0cd2cb0c328a0cc2cb0c328a0c22080c31c70c92080c21c70c30c50c21850c40c00c2040⟩,
  ⟨192,5,[ew415,ew459,ew484,ew492,ew498,ew534],localHints 5 0x2843f0190120c42b00a0882980683000e494160a70080c8018080a44a41700200c0cc02855 0x13ac2739c2ee9b5964226a9252640ca218412f09dc16b4811b1635292819cc32948310820⟩,
  ⟨192,6,[ew415,ew459,ew484,ew498,ew532,ew534],localHints 6 0x7e142121a80410320083681614c13c2b83001201c538510080342205206400c070220100a01980600ad3da7055 0x70f80c02030f3dc71c29b29e3df79b6ca3ca28c2930134cc4ca74a70f3dc6db70f3dc6db34d69831a6134d928a6534d828a0ce0d63d758e3833c30d50d231249548330348a5034d40ca2924d20c60d221248648320310f11039140f3c438410d1073071cd1c43041ca2c424b10a2872471081071871c81c41840831440451030c2040⟩,
  ⟨192,5,[ew197,ew415,ew459,ew498,ew532,ew534],localHints 5 0xc4508a601a0b01800714e0b819008008064290020140780180900a03c0300c 0xb59682d5452a1251d263949038c4b00bd61739016b4ac184605a96a42507298a41886208020⟩,
  ⟨192,6,[ew415,ew459,ew487,ew492,ew498,ew532,ew534],localHints 5 0x622842b00a01206415b500db3380b0a601a0b01800704415c078a70080b8010320060201404401801403055 0x3ff5a4fed1ce9ee97a5f13b3af4bd2729c1ee7ad6c4a8a9314a4914627809ee1344162c2a5242841cc12902308820⟩,
  ⟨192,6,[ew199,ew415,ew459,ew487,ew498,ew532,ew534],localHints 5 0x1f85082f0a40585300d06003c538140140c806055008064010090060ec2206d00e01404006 0x35a5bcf951f0f3ad4b53eefb9c87b0ab4109f014e671c8408ac0f83c0e71c2d0080c5a96a4a507314a41886208020⟩,
  ⟨192,6,[ew44,ew415,ew459,ew487,ew498,ew532],localHints 5 0x1881fa6781e3c00c0078540640380612f32e6582ab51082008188090c800c1597841e0640380501001006806 0x2bdf637ecf794d6a1ad4fbc86b63ef514aef38852a9ce131b2b5a5c608d6955a23344528ac2ca59250806b478c0dad0630355c16b814a1d8739d41404c84048139460f709ad13186528cc5894a324c240848118e6114a1210252888408c620004310400⟩
]

def nodesBlock26 : Array Node := #[
  ⟨192,7,[ew415,ew459,ew487,ew498,ew532,ew534],localHints 6 0x354062084db0a1090d4c178556a41040c82b9a01483681e14c13c1600a06015c0480701e29c2880401a0b8010140641100180e0100300b00500c0881434d 0x88d42b8aab2b8aa41088d88da49849a674288a78618894099896259153659156188c934928a4102a286128a4102a286128a34d2a079e28a34d29f79e28524929d71c28a24928571c5843c409a41b59a3cf08440458435909461959434d0846045942570845575842490945540410530841442834030513d22914100433c328334e04730e28734d04330328724b04320b283249047207082086083143082104043043082040⟩,
  ⟨192,7,[ew243,ew415,ew459,ew498,ew532,ew534],localHints 6 0x62085308a1090064178550c018c2505702e29c2882e0280c8070080661043300401a2d01580a0041b4048030880a0078050180880b006 0x48b4274663a746641048b44b9488889634244638a24884083883218092e180930c3882c87053df09b41f71b3cf08541071c2cb08531e7052cb08e30c71b20808525d70520809b2491804001993da1994101803c01802d81945d81942cb1805c01942161805561802081945540821931801800821451924101863cf1914101863cf18e30c1862cb18d30c1862cb18124918620818a249181208187184081144082083081000⟩,
  ⟨192,7,[ew288,ew415,ew459,ew498,ew532,ew534],localHints 6 0x310426d8508480320bc5304f0580281800900e1682e84602a0a01984101a0102a82b0280083680e00603c0284404405806006 0x40a3a442336442338e40a40a8877c78a03a14207df40738734769e35829e35869a3472870c53c50dc39d0dc3cf0c53850c529b0d769b0d728a0c56850d71d90c56190c51c70d76171013964933d611338e4813cf10428a4812d510128a48d2cb1131c74812141011c74932080c34910c31450c10c10d03cf0c338e0d03cf0c338e0cd2cb0c328a0cc2cb0c328a0c22080c31c70c92080c21c70c30c60c21450c40c00c2040⟩,
  ⟨192,6,[ew392,ew459,ew519,ew532,ew534],localHints 5 0x620842d02e08e6dc5304f01a1041603b0841100b815142120ab80405e028011400100c81800500605804807 0xb259fb7a9fb798cb26c991d9d942fd9418c91ee79493c91f7c91d299537bd12e4d6199b62f7b1184a1135a0155a0129a1144944f391204910e49461010c431398f1384d10d8310d4b1052b1054a10d231204610ce61048510c0510c8310400⟩,
  ⟨192,7,[ew392,ew415,ew459,ew498,ew532,ew534],localHints 6 0x310421900c85014c3ac2782c0940782d00d05c051aa84202a03c208a81200101d82b0140080700304415c0280705005804006 0x44a3a436336436338e44a34a08986209a3a209a86108938e08d2e00892a00892cb08228a44560579d39f79d61844538534529c3442dc34428a3452c508425b0856850852450846840c13990d36190d338e0c16010cd2970c15970c128a0c35960810810822490820d50d31450c14940c11450d349209109008238e08f08f08238e08d2cb08228a08c2cb08228a082088082248087145082104086145082104083080082040⟩,
  ⟨192,5,[ew266,ew415,ew459,ew498,ew532,ew534],localHints 5 0xc45081905e2981800914e0b81980c0080340504700400c0701700a01c03008 0xb5969356869cd261c9431a5038c4d00bd6173921304c06b46c5a96a4a0e7314c51906208020⟩,
  ⟨192,5,[ew415,ew453,ew459,ew498,ew516,ew534],localHints 5 0xc45081905e298b3830012150068020881cc038a7008174050320060ec1980501811cb4006 0x35a5a4f9c1ef749c9689089a92943ce528ae107a44771da40316052920420e62948300820⟩,
  ⟨192,6,[ew415,ew453,ew459,ew498,ew519,ew532,ew534],localHints 5 0x620adab0a10320bc070a62ce15c1800901a00a6882202c1b4038a7008174050080060ec198050180a022006 0x3ff5a5735cd3e4f4fcd9f5a49f2726264226f621215a9e935cd729460183cee3b48062c0a5240801c062948300820⟩,
  ⟨192,6,[ew268,ew415,ew459,ew498,ew519,ew532,ew534],localHints 5 0x150238a10320385302c0440c0538140100ec1980401a0280105508815c0480300e01406006 0x35a6258b62d394e498b9089812c415562a244610a72910a08b0098240f0100e6b44162d8b52507398a42906208020⟩,
  ⟨192,6,[ew415,ew459,ew498,ew516,ew532,ew534],localHints 6 0x2a041004284240190da29827b560ae0881800900e29c2880401a1102380802c0a0190036b0d5c1d83300c0140780c 0x81084d1613504208208104203cf8104203cf38e7cb35f21c21d41e75c70840821b21435451b50834820a2142d450a5082c808f09941a64f3c240208d0931534cd4c26020970935934d74c25824c85425150882135130d00d13d24504033c30ce0c034000e0033430cb0c028c00b0032831c82431890c82071850021030440c2080040⟩,
  ⟨192,6,[ew44,ew415,ew459,ew498,ew519,ew532],localHints 5 0x3c41f8070c343065c0b8300a8020979960760cc07b510820081882b2f083c0c80900601c3000501801006806 0x2dad65eeb6b677b9fdf435a8f78ed6d29d3d4e4bf0cde1af7235b9de49a21164ceb263e088c10e7320c06b477b8dad05ef5ad815054e705015a4c64902320108388e0f709ad0b0225884b105411210939d28408e7118c1210262888408c220004310400⟩,
  ⟨192,7,[ew415,ew459,ew498,ew519,ew532,ew534],localHints 6 0x35b06208415cd208e2842401905e038db8a609e105ad02c076d640505704405c1806d01201c538510080342e802028020018166aa0cc2200600a0a00780c 0x78c3eb7aab2b7aa3cf78c78c1453cf15e38e1453cf15e38e14530c1699e714530c1689e75099092253e65259242093c95096632133235136592093090820a220920984338385f3e079f38e7833c374331c6d265c6d230c6836431566161435c31431431565d62122555034d55032492124d21443c40903911503cf08438414430c0802cd14030c0842c420820a2042042082490840842080871400c60840461440c3080040⟩,
  ⟨192,7,[ew170,ew415,ew459,ew498,ew532,ew534],localHints 6 0x62084320190a09885304f0580ec2506d03c29c2885d0280c81980f0181044e00401a2d015802014110070030ae01c1402200a0200b006 0x48c4274663a746641048c44c70992505b42571b92404941071c2e30493237092cb04e30c8833c38a04214603cf48340338331f7862df78630c3832c304625d7036c37032430466c61404001593da1594101403c014030c1535d815330c1405c00411561401400412491530d51405151400c31535131524101453cf1514101453cf14e30c1452cb14d30c1452cb14a1480412481441861450c31471861440c3041042041000⟩,
  ⟨192,7,[ew301,ew415,ew459,ew498,ew532,ew534],localHints 6 0x310422842402f36e2982782c0140c0048070b4034170320840a00a8410320101d82b0280080700304415c0780508805804006 0x40a3a442336442338e40a40a0883c80a13a20a13cf0883880886e00992a00996db0882887c45847dd39e41d59640438434429c3586dc35828a3446c409821a08465a0842080986580c13974915970d138e4815810c32954812d50c128a48d2cb0824940822080810810d11044811530c11044911450903cf08238e0903cf08238e08d2cb08228a08c2cb08228a082089082208087145082104086145082104083080082040⟩,
  ⟨192,5,[ew311,ew415,ew459,ew498,ew532,ew534],localHints 5 0xc45081905e298160a70640381980f01a0100a02100400c0480500e05403008 0xb5949356869cd26249648c524310c30c1410a5017bcce6b48c5a96a4a0e7314c520c8308820⟩,
  ⟨192,5,[ew409,ew415,ew459,ew498,ew524,ew534],localHints 5 0x150508190a02983183007629cb403201c0cc0783100803401044028158018212ce01404006 0x35a51cb9c16f73945650ab538a942cc1258007882102bdce1358c5a92941c853148218820⟩
]

def nodesBlock27 : Array Node := #[
  ⟨192,6,[ew409,ew415,ew459,ew498,ew527,ew532,ew534],localHints 5 0xa80adae0a1032140048a60c601c1d8a70285a02203201c0cc0780401a00a6982802c1b4018220ae01404006 0x3ff64d6c5b27e9f4bcd975a9972516162bde62b08a2a828c0027288008840af7384d62d8b529281a0e53148218820⟩,
  ⟨192,7,[ew409,ew415,ew459,ew498,ew532,ew534],localHints 6 0x2a0b41421200c85008e2992d04f0c61481835d14e144159680760c80705506603c20890008034220140041b4048030ae01c110050100a00b006 0x44c3e9663a296633cf44ca0c4489485e63e78669654483c85c83246498e464930c5c88c84443845203e286038e4443c450431f64679f64630c5047845c621d50425d7042085c62460803c009a39b09a3cf08038008008008230c0990980972160805560802080825550941130804930801040824920913cf08238e0903cf08238e08d08b08130b08124908220808a249081208085186082104087186085104082083081000⟩,
  ⟨192,6,[ew313,ew415,ew459,ew498,ew527,ew532,ew534],localHints 5 0xc4108a10320245300a00e0ec5382e0500c81980d008050010b40ae1100700301e01404006 0x35a5a58b62d394e498b9089a12c4155824d122988829022b041203000f738856b44362d8b52506398a42906218820⟩,
  ⟨192,7,[ew313,ew415,ew459,ew498,ew532,ew534],localHints 6 0x5a0310426d8508480320bcdb8a609e0b0050306bc024038a70a20ac170320760cc2a84101a0100a0020da0380185701e088028440100a00b006 0x40c3a8427a6842738e40c40c9898c99a43a54248e34093894c976259a32259a75d4c93098453c585f3a041f3cf40538544531e59975e59930c4457454d925c44569c6c52494d96991003800973d811738e0803c009609510430c08008010425408029410024909328a1041520801d21001450911c71103cf10438e1103cf10438e08208d08130c10128a10424910b28a1012491061c71041451081c7106145104103081000⟩,
  ⟨192,6,[ew415,ew436,ew527,ew532,ew534],localHints 5 0xc43002c042284241570a0504181b814e1440206601a0b80103b0281080385702e0541900600605807008 0x8363e86d9e86e318360d425fd41e3d41def42629421bc4277c425ad4337b10c431663a1645810e2310d77105b71056b10da31585510d35a1224a49f384a31811e4611ae6016e601ad611644192a410e441124418e610065110251106310020⟩,
  ⟨192,7,[ew415,ew436,ew459,ew498,ew532,ew534],localHints 6 0x188210c806417860058029af8411502401580300a29c760510081980682e0040ec0a0460120782100704405c060280880180b008 0x48f4e53a43a53a44d348f38f04b8a304a4e304a8a204b4cb04e7a104b3e104b79e0413cf1c84601c64e01c64511c84c81ce3df1c879f1c83cf1c779e0480480412cb0411dd05c05b0414d305a05a0414d304e34d0413cf05934d0413cf0410580412d80470570412174824c25544565544d34824423823d03803503803cf3823420402cc0422820422c20402801c52091c21821c22021c51850400400421020420c2040040⟩,
  ⟨192,6,[ew415,ew459,ew498,ew524,ew532,ew534],localHints 6 0x62198208021421200c86d0122982785700e058110306c2d80538510080341d8216b8110140320060380403300c0140780c 0x88f8cc36330f3e28a284e3a23cf88e3a13cf6188163201dd1de3df79d7473c71dc1c630619c1873071d51c659b19518758708e0993da64e3823c20980813010580423020960815570560425424c75024940871d348d0cf0d039140f3c33830cc0c534514c1432c30ca0c524514a1432431472031880c71c51850021030440c2080040⟩,
  ⟨192,6,[ew44,ew415,ew459,ew498,ew527,ew532],localHints 5 0x3c81f80480725e65c1d8c20a85e0cb0150640cc064d40cc0081882b43083c0c80e00603c0280401016806806 0x2ef7635abbdf2d69fdf435a8f78ed6eb5d3ece5bdccd69af72b5bbdf0bb2ece72e8bbd640dc0ef81b5a0bde96a02a005814ad0679811301ce340e25900d2014b13460f711ad230815842b091442208939d28410e72188129426090a508c640008310400⟩,
  ⟨192,7,[ew415,ew459,ew498,ew527,ew532,ew534],localHints 6 0x36206210415cd5042284240190a00245304f0c602803b5f37029c288040cc035af02e076009ae8140880a00a8320da00c0b00e0100cc2b80600a0880780c 0x5d262b5e7b2b5e76185d25d214559615761814559616a6181454921699e71454921689e72ca90a2656262e592424a60a2ca7a32484a32c879e24a48a0820a224a24a1435830a062116059608360314349208179f14149208378324925d24324324928a08308324909c6c46046d959a5d96185c45845444944c74144c749244440414d3cd1443841443c414d38d24728c2c420c2c428a2472070800c61440461440c3080040⟩,
  ⟨192,7,[ew186,ew415,ew459,ew498,ew532,ew534],localHints 6 0x310421900c82f14c13c318304c629c2886605c0ec0a0460da0781980f0181044e00d0081541580201415c0480300e0580282808802011006 0x70c3e84673a84673cf70c44c5c99661963e65d69651893c95d72e41893245c92cb18e30c0454050623e30624100453c504530c0542e105430c0452c51860600450451862497c03c07dd41e45d3cf70040038031b68265b68230c3806401822585c05805c02401825820531550405150401450535130524100413cf0514100413cf04e30c0412cb04d30c0412cb04a048186248186187186145044082041000043082041000⟩,
  ⟨192,7,[ew256,ew415,ew459,ew498,ew532,ew534],localHints 6 0x18821142120280600580c0dc0a70a2034170140640380404204405c208660320101d82b014008048030ae01c028280880300b006 0x40a3a542436542438e40a40a0483c80623a30623cf0483880482e10562a10562cb0482881c66a04d23a01d269a4c63861c729f4c62df1c628a4cd2cb0414de04120804604674038075b69c41b38e40068034029935561935528a3406000552170405970402080555954c21941c04801c01804c24820513cf04138e0503cf04138e04d2cb04128a04c2cb04128a041049041208047045041185044082041000043082041000⟩,
  ⟨192,7,[ew415,ew453,ew459,ew498,ew532,ew534],localHints 6 0xc4508480320bc108a609e59c180090822402b8020da01c0b0a742c1440206601a1741580a0aa148193590060ec070b40660140602808802011006 0x51056a4653ea4655555103d050b9cb2a85695e89e750b54b28b42646096646041028b94b0464c60635640634d304654604604604141005106204a2e10468210462cb04182005f4d304155505e4d304155505d05c05941c0592490412cb05b2490592cb04105a0591865005405d64d85d65555004c03c04124423924424103c03802822cd20024d3002cb2822420451870402070401860450450400400421020420c2040040⟩,
  ⟨192,7,[ew268,ew415,ew459,ew498,ew532,ew534],localHints 6 0x15023a611421200c85014c13c1603037029c2882e0560505a0326b40ec0700806615420866008034050020da024018070440580284401815c14006 0x40c3ea4294aa4293cf40c40ca09949a263e74269654093c95896a46ca3246ca69a5893090853851e23e30a238e1c53c51db1e108230c1c51c50822601c52a00852491d628a7c03c07dd39e41d3cf40038048031c6d469c6d430c4806805942586405585c02495945541c31530800930801451c34830913cf08238e0903cf08238e1c71cd1c630c08628a08224908b28a0862490820881c61450810c30840000840c3081000⟩,
  ⟨192,7,[ew415,ew459,ew492,ew498,ew532,ew534],localHints 6 0x62284240e20ac104480190da028048a609e0b01083000e0882b8a721a1440209c01a0b81580207611c190030100a0220161680cda900600a1540780c 0x51056b45d3eb45d5555103d020c90c22956a22992420c54c20c20c20841022822722692420855522592420855522322220841020822120830c5034c35df5605df4d35035433c341e45b75e45b4103c374321b31c20309c20330c21b21b2032032016812016412032035045445d64d85d65555044c43c441244b39244b4103c438420b30d2041cd20430c20b20b2042042002802002402042040800c61c40461440c3080040⟩,
  ⟨192,7,[ew199,ew415,ew459,ew498,ew532,ew534],localHints 6 0x1f8290a10900bd310a609e18c1826314e1440685d0560501903b1680cda985501e0302089c008064050020120580185700e088028440101b414006 0x40d3ea42962a4293cf40d40d0893892a73e80a738e2893c929b2a608234d2892899457459633e442375d4053c56056a26c73626c769a6053452872610850a10852492876078003c081e75f41e3cf40074060035c6c369c6c334d6006802832590800990802492836035121565c04d65401455124d20913cf08238e0903cf08238e28a28c28a34c08208b28a2490861c70881450881c70861450810c30840000840c3081000⟩,
  ⟨192,7,[ew415,ew459,ew498,ew531,ew532],localHints 6 0x9e1500c41786403c0641600a0c005c1800900e0ac170021680502d0150080344e0320060ec070080cc0cc2080600a1540780c 0x5a48e214f52234b72159852135871c28b50b14b78b35f3e035f79e14b3cb1c351d59771d1d75140837031433831da3db1da38e1433c31d72d93436191c32cb2976171445155884951485144c44841443c41503911503cf1443841482cc34424c1442cb2882481400c61c40461440c3080040⟩
]

def nodesBlock28 : Array Node := #[
  ⟨192,7,[ew44,ew415,ew459,ew498,ew532],localHints 6 0x6207e1860c1b10c20a80c9ad80e066d500780c150008188190121901d80300e1802a8055940ac020080b42d006806 0x34c82118f46118f82034c4512486df18b45f18b6db24845134b31e2483de74830c34b3cb08045c1846dc1844510806db34431a08061a64030c3446042542170805575802082545541934d21854511853cf1d030c1903ce34530c1852cb1c12081812ca2452081811041c5000185103081000⟩,
  ⟨192,8,[ew415,ew459,ew498,ew532,ew534],localHints 6 0x9d20c410ce81421200cce705f3985304f9ca0b27200a9c7388184e19c0024038a7120144020a801b37c1709e0053780a4dd9b80ca6d8039b4038044d99b00ce6b80600b3580780c 0x6136726f1cf2531659613c1360cb4c6ee66f6eeb6d60c64cb0c92b51e4eb51e924a8c4cc6035c36e86696e85d76036439c34e651d92651d4d39439038dd3218837a180330c7dd79d6046446da5dc6da6596045c45844d55094555094d348444440930e3c428e34430c2c92892000c61c40461440c3080040⟩,
  ⟨193,5,[ew419,ew463,ew502,ew513,ew532,ew536],localHints 5 0xfa1e43282a0c00104a01300e1282d01b01a2000581a0100d02300901c03c1680c 0xbde49649924c130b5984ad6092528464d924c5307bc22738646358b4a92839cc02948300820⟩,
  ⟨193,6,[ew365,ew419,ew463,ew499,ew502,ew532,ew536],decodeHints 0x3e87d00802c048045981943281301606c0d85e0161780582a0121803000d00802c4a00b0261282500e01203c1b11101e1682d00401a02c4000b0341182300901c0302690401803007acb04e010b100401604c0581304a0249800904e0da7502700e01c04008⟩,
  ⟨193,7,[ew365,ew419,ew463,ew502,ew532,ew536],localHints 6 0x7d0413ac3cacc6c61943009409405c2d00d1000682301501c410b101b0081541580b0264c01502501203c0384d06c09c06008 0x38c3e43a34243a33cf38c40c8074218893e18094107c73c73892de38731e3872cb38930c0c64100da3dd0da4100c63cf0ce30c0c62dc0c630c0c32cb0da4db0c61db0c64d30da1c710141011461911441010161810e30c10159710130c1045961141d51014d51011c71144d30c10c10c31860c31120c24100c33cf0d14100c23cf0ce30c0c32cb0cd30c0c32cb0c82490c31c70ca2490c81c70c30c50c21850c40c00c2040⟩,
  ⟨193,5,[ew419,ew463,ew481,ew502,ew532,ew536],localHints 5 0x1f4320820080243b8610261281685a0361880581a01c0a8060340101080380f 0xb5a695d573a51e95cd737a5e9948c78c5618412f738e10b5a15b1635292819cc31948310820⟩,
  ⟨193,6,[ew395,ew419,ew460,ew463,ew502,ew532,ew536],decodeHints 0x3e87d00802c320640320104108202602c0380459c1843080b0261282500e00e06c0d8450161140582501c4c00702d00e1682d0040101883100b034020072cd0841080380f0101348200804e010b100402602c0980b0120241b00722201c138259d809c06008⟩,
  ⟨193,7,[ew395,ew419,ew463,ew502,ew532,ew536],localHints 6 0x7d040190414ed0eeb39b20610940782d00d0c40688204202a03cb101b0080ec15813016038048362220b40384d01809413808 0x38b3e43a34243a33cf38b40b08a41009a3e209a41008a3cf08e32108a2e108a30c0822cb78541f8063df7864107453c53862dc38531c3852cb38630c08529b09269b09228a08568510041011361911341010060010e2d71005971002cb10459608008008228a0821151131541004941001451134920814100823cf0914100813cf08e30c0822cb08d30c0822cb082089081289088186082145087186082145084083081000⟩,
  ⟨193,7,[ew409,ew419,ew463,ew502,ew532,ew536],localHints 6 0x1621e4c40820541143b89405a178251740f003415870076154b10040362d00d00b2600241280e22201c1b00f09a09c1a008 0x54d42355e3e355e41054d3cd54a3e24df42285f3cf54a40a4df36054a7a054a34d4df79e5463dd49b41d61b3cf54640649b35c54669c54634d49b69a4c62194842996042084c62860d53d70c15970c13cf0c35960c10c10c334d0d50d40d328a0c12080c128a0c32080d21860c11040c11860c31040c24100c33cf0d14100c23cf0ce0cc0c234c0c928a0c32080cb28a0c92080c51860c31040c71860c51040c30c00c2040⟩,
  ⟨193,5,[ew419,ew463,ew478,ew502,ew532,ew536],localHints 5 0x1621903280401a038300610260a80782d0f006c3100b034118048340101080380c 0xbde6855945ad5e8551533a0e8915c5545418410f095c10b5815ad434a507318a31908310820⟩,
  ⟨193,6,[ew416,ew419,ew439,ew463,ew502,ew532,ew536],decodeHints 0x588b101a02c320640320243286502602c3006001a01c3086101604c038095a009c0696201a0680581a0160380480f00e02006acf0c41880581a08c118048080841080380c0101348200803606c1000b04002c128092600241b00722201c128279dc09c1a008⟩,
  ⟨193,7,[ew416,ew419,ew463,ew502,ew532,ew536],localHints 6 0x1621903286003218409cef094b41b29040c40682300e08403c0600d0360ac1000b04a4c01500906c4441680709a0d013808 0x4c42304d3a304d41004c04c0487e20494220497df04840838976138832138875d38930c0444200457e00454100447c438531e38475e38430c38575d68451b71221b6925146442040400400414100410d80ce3170c05970c030c0c35960c02150d15150d12080c05000d11130c04930c01040d149104104f04140f04e34d04130c04e34d04130c04b24904120804a249041208047145041104046145041104043042041000⟩,
  ⟨193,7,[ew419,ew439,ew463,ew502,ew532,ew536],localHints 6 0x7d040190328600c204c889620080ac0700f04f3c03c2cf036d94068620160ec0d0460120782100706c05c0604d2080d012808 0x38f6e43a34e43a36db38f4cf04b4d304a6e204a4d304b6cb04e7a104b3e104b79e0413cf1c84d31c66e01c64d31c86c81ce3df1c879f1c83cf1c779e0480480412cb0411dd0574d30416db05c4d30576db04e34d0413cf05a34d0413cf0410590572cb0470580572085004d55824555024d34804403823d03803503803cf38234d0402cc04528c0452cb0402801c52091c01891c02081c51850400400421020420c2040040⟩,
  ⟨193,7,[ew419,ew453,ew463,ew502,ew532,ew536],localHints 6 0x7d0f2194150200ee010379620164c01282700eadc3c01b01a200158130aa0d02f17308c5780483b01c2d01684d2080201b00c 0x4507a446052446079e4505104495232217a332151444978922142244982244941022182005151f04579f04551404179e04504504141005105d0481c70452490451c70412490584d304151405c4d305851404f05b05841b0591c704124905a1c705924904105705815744251558e4d528e5144424c228e4124423524424103ce34d20224b3001cb2802492021c20401400421820421420400400400400421020420c2040040⟩,
  ⟨193,7,[ew419,ew460,ew463,ew502,ew532,ew536],localHints 6 0x7d040190329110c204c2501b08a0949802a05a168020190c402c1581a9e2119668096c80382100706c03c0604d2080d013808 0x5256406346406355505205204c52205856205851404c54c4587a144c4a144c79e4584920480480415550411e01d149f1c879f1c84921c779e1c829d1c631d1c628a1c830804105c04155c0516db0414920516db04149205a61804130c05961804130c04705704120804055604251604255504050044249344041344049244241034030e3c528e34530c2c02801c52091c01891c02081c51850400400421020420c2040040⟩,
  ⟨193,7,[ew419,ew463,ew492,ew502,ew532,ew536],localHints 6 0x3e8790dc5880c81304e0243b8040c20b4100362229783c01b01a1881580b0760d0228b4054134820252ba108a980800e1540780c 0x45072545952545971c45051021152420b72420b51420871c20b20b20841021122321f86120851422286121f51420f22021f41020821e21f2de44351d59a71d1da5144437031da41b44365b4434103da6592032c32010812012c12032032032032016012015c120320344451558e4d514e5144444c414e4124443524444103ce34d2042c42003002002c02042042042042002802002402042041400c61c40461440c3080040⟩
]

def nodesBlock29 : Array Node := #[
  ⟨193,7,[ew419,ew463,ew499,ew502,ew532,ew536],localHints 6 0x7d0404c03281b0bc0a8300610261281b11105a1680200d0c402c1581a08c0241280e09a4101a0279e41096580800ed8c0780c 0x21256422346422355521221220e20e2085552083623516e134e4a134e6db34d4922082202085602117df2084922117df20849220d21e20838e20351d21755d21751420354345749c4436dc4434924576db34331a34139a34130c34338320320321765721761720320320455620951620955520450444949344441344449244941034438f34030f34038e3443042042042092c92092892042041400c61c40461440c3080040⟩,
  ⟨193,7,[ew419,ew463,ew502,ew531,ew532,ew536],localHints 6 0xad0040401e43282a04a4c00f0770c20b40983622205c250b40f006c3100b0560d00d04d20805413a5608c0241d80e41c108f580800e1540780c 0x35435434d59634d4e934d36834d59635336734d51434a5a636426636459634a34a4e47654ca5254ca75d4e451434a34a3618e13618a134a34a3435a035e0a035e5963433434de51f4c375f4c35144de75d34334335a71a35a6da3433431c32193012991c12082432833445973526173525963443444d25154c44554c45144d245134434434e40e34e3ce34434414428b30020b14028a2442041400c61c40461440c3080040⟩,
  ⟨193,8,[ew419,ew463,ew502,ew532,ew536],localHints 6 0x7d0413f03ccfb0cb3e8150779f201030cf805a04c254f72c41e00dcf601a1884f00b9ea0d00d13008c0267a00e2221088200800f3cc0780c 0x4507a85e756846779e99055030a5655e17a532155590a78a3216a344a42344a69a8a14101c35605db7a01db5557c37831db41d44369d44341071b69a1c32193012991c12086032831445565ce4d614e5555044c414e4124443524444103ce34d14428b30020b14028a2442041400c61c40461440c3080040⟩,
  ⟨195,8,[ew335,ew426,ew470,ew509,ew535,ew537,ew538],localHints 6 0x10c1081b0920801f0180c8078178650c005c1600a0c204c2505a02a034170140c40683f84601c1e82106b01e030200010080956882713c0080b0000160240182400e0141481f28607404006 0xced364b55144b5d330ce5140cc4cc3725143724d30cc50cc4c3b0c4bc7034b38e34c34c0ca51412e4ef76e5140ca4ca752a2d10a3ad74aa2810438e74d30c10a2ec74a30c1042cb0c751422a4eb6aa5140c74c76923a9207a2968738e208a2868d30c2079a768730c2089a66876e57572a56976db1072870c15141638a46235140c18816123a114182160138e14582060d30c14179f60130c14579e60129c7566dc61628a1016c16161d96815d96011c72165d60c25141154d31155140c24d311211110438e11010f10438e10d30c1042cb10d30c1042cb1041090c22891081060c21c61051000c2040⟩,
  ⟨195,7,[ew367,ew490,ew509,ew514,ew535,ew537,ew538],localHints 6 0x10c0d8490980607a8210400e41503f02402c6c0090b40642e8360a42001105e0381385d01506a0040202d0040281e00002004cf800711a00c670246cc01406033 0xfb6ea124a8b6c3d248c44c9d24a745131230c3ea8abaa23cf319307492a514454921d14453cf728a053cf728a0530c6679c530c6679c64a68d19a349219118638694f3e538e18f1a33241a290630c8e288586018718149251e7d449205e0553cf05b7413cf71b6d530c05868130c6586145d40560415c15165141860550411865155024932d14cb4920910823cf40e3903cf08e08b30d08a34230c2ca2852480870851860850851040c3002040⟩,
  ⟨195,8,[ew367,ew426,ew470,ew509,ew514,ew535,ew537,ew538],localHints 6 0x430361242601819e084100390540fc0900b0121803189402e1680685d0282000d04e03808c148156ce38c0080406c0080502200004c0f85b03a00c2987f0482e80780518e86406006 0x4b3d2e555bb3c925553d43ed555b5450f54f3d2c28c70a1248f40f31556f51421554c514212493bae212493bae20f3d0b6d20f3d0b6d295b2952ca5554a50a2912ab492ad144a48aa4fa8aa2a28f3e9a282089ca30a1555635268d55455144d248546515248745140f3c53a414f3c738e8da8c570515a1636e38ca28520514a2a31e30555588626155418614d24817e00524997df40f3c175e04f3d975d61b60170105b05869860a28120104a2986580460431450c65c25551d45165550945134921d14534921d14503cf1ce3903cf1ce3881cd08c2c828a2482481c71861021440c3002040⟩,
  ⟨195,8,[ew321,ew426,ew470,ew509,ew535,ew537,ew538],localHints 6 0x860840d8490400f80c0390540fc0900b0c005c0202c0c20c02d01501a0b80a0620341fc14832084090200190020941380a004058098000123b40e803038510b180f00e0140f82322421ccc00c15213804006 0x497e7b6ba6db6bae784976db494b545b76db5b7b6d4946d4d945f5db0db55b05d75945944906f4271b748b16db490b508906102735d78b36182505d08b1532250c32890514271c3048b6db7aeb6f0ee6db48bb4b0da5ec78b62c0cb5d779a6180d651478b56b0cb5147965550cb42a88c7aa0cc41024b24b4816db8689e91a86db4819c119a5e68419661815d785a9651965148418e41815148568e31814208848601844102412411842df0c131f1812cb78430449171c25d6db25d71c4916db25a6182495d72596182495d725655524951425655524951424925349141024f30c0ce2cb0cd30a1822ca2481041870411851000c2040⟩,
  ⟨195,7,[ew321,ew367,ew490,ew509,ew535,ew537,ew538],localHints 6 0x10c1081b092080260180720a81f8120161682e852100178438e30080b0308306d01087a8190020281b002026088001450480240181c0181380a95819c23403805 0x10b2eb534edb2b4134cd6cda934ea6db35334d4288e9a2341034e3494e791b9e44d325b24948999042649225026436526394934d9238c74d31548854d31d41dd4101e084741046081d34d1de7c734d39e7852491dd1c724915d1414d32db6dc4d305b05141a0526814102d248e34d04f64134d2cf3c32d80c92412c15d75811d60945154d35545024d345249141045249141038f3ce34d38f3ce34d30b2822491871c81452071c6145103002040⟩,
  ⟨195,8,[ew321,ew367,ew426,ew470,ew509,ew535,ew537,ew538],localHints 6 0x860840d8490401300c0390540fc0900b0c018c4a05a01a1740a0800340a5b48e30080940b01f10e01c5480819e0640080a06c008098220000900480301e05c1181c0181380a87f04c16c7681d 0x4b5df6555db5d125553df3f3555cdf7cf54f3d2c6ccb1b1248f40f315c2d7f0b5554c7cc31432f492bd450c48cb4fb8cb2e30f3edb2c2d554a7eb29554b7df4d248b52a2d248e51440f3cb4692cf3ce45128c30b38b2cc30a38a1d55459e81555479e74d24879661d24a296540f3c78e41cf3e28e314c3078871cc3058851db1d92cb65b84155539f7e055505f7d349239451e4923945103cf39145d3cf39144438e10c31c39c6db6812da6596011d80965975555d65825554d45134924d45134924114503cf4114503cf38e34230c20b2c928a24b2c628a2471c81452071c61451040c2040⟩,
  ⟨195,6,[ew367,ew490,ew506,ew509,ew535,ew537,ew538],localHints 5 0x218490300bc3280b0061682e852100178230159fa234060040020b00100a0c20000980900a04003842 0xeaf8b32d86ded265b164d6909364d85b16ca2689360d8bdd765b5354d0d334a31241af7356c5854a4a0c7314241046310400⟩,
  ⟨195,7,[ew367,ew490,ew509,ew535,ew537,ew538,ew539],localHints 6 0x40860840d8490401300c0ce6d60e41783f02402c2705d06c148388800441782301e02a014008f511a5dc1680201413c000131c600c120096d41d80800c 0x103ec44f44b6cb31030c40c2db2cca6ba9146aa683114485c82502494092172093c99d14674272512493257a695e30c2572449041901869061231064627d089f45118f1862e110c8442cb18c19f26019e8062497de7803c04dd4d33d300f0004514d94d345100f01930c01a70030c6da6992490166002495d65931860145401864d44cf3d204f48f45105004f3ce04c30d2cb34c3012cb04924a2082892412081c61811040461851040c3081000⟩,
  ⟨195,7,[ew367,ew426,ew470,ew506,ew509,ew535,ew537,ew538],localHints 6 0x861240c02f0ca148058030c018c4a04a1b01680685d0282000d04601cb480600f6d6004020020140000981f1c60240e8530b67c403808 0x273a638a38d2a594c28e34e1a490b30a8ca84e34e36232230a84a86080e7ce34c78c2ca74a25c7131906c340e68e64c60c5ca58a5545064d148345140f38d38d30b30b2892892061c61440c2041000⟩,
  ⟨195,8,[ew367,ew426,ew470,ew509,ew535,ew537,ew538,ew539],localHints 6 0x204304206c248200980603fcfe0720bc1f81201618c4a04a02e1382e8141000a40d04602a039b601d00233c200360040281100002638c018240121c40800f1140442d80c 0x481c5305339038f48f3d23ce40e3eec2f4d3beeb4f4d32cd2cc48c31230b34b30132c4d3b12b0c4cc30faa3aea8cf3cc34c1e91c9489269247a072539e44a79134c904924e9873e61ce3893c990c9498e524c3248e310111f79f7c17c40441134df49f7d34c404440f3c43a210f3c838e34c3042e110c3082cb7c92441e010925f1c70010177975c15c00400134d74975d34c004040f3c071d00f3da71c34c30065b00c31a6595c92405980092575960060031040c65410540415014d305244104140f3c838e40f3c838e34c3082cb34c3082cb2892481c72892481c71861411040c3081000⟩,
  ⟨195,6,[ew367,ew489,ew509,ew535,ew537,ew538],localHints 6 0x10c1081b0920827f81819c191699570541202d2640bab007a1b901600c0a8350020646a8020140f0000100260480f03309c01406042 0x3249a53cf9648cc3cf24e2623cf88e3893c924c8138604cc30950974f3c67de18f3dd75c18b2db30c6cb2c630c18925a4d36892464d304f3d139944f3c138160b5c130c04b2d630c5492414d30492544d344648115204605115108f40839020f3c238208c3402cd00c3022c22092821ca0892481c7006002142086080140003102044083080040⟩,
  ⟨195,7,[ew367,ew490,ew509,ew535,ew537,ew538,ew544],localHints 6 0x20360860840d84904408280018006234ab82a09002c0e36e0badb4290721006e42f0151c633812035002064160020140f0000100260480f00737401406033 0x128ad3e23ccb0c2d22cb48b31a30ca6ba8f3eaa6830f3de9de25224948979678938998f3e638e24f2493247a591e30c2562628a31a28e23cf1921a28a118b2e030c80b2c630c18925f79e7c924679e61d74160105d05261c04f3d438e50f3c138160c30165b04c31a65960924155704925655550618114104605415411310248209208444408f40839020f3c238208c3442cd10c3022c22092821ca0892481c71061021420860841440c3002040⟩,
  ⟨195,7,[ew43,ew367,ew490,ew509,ew535,ew537,ew538],localHints 6 0x620843e820a020601c82a0901682e8521001781603c02004c0f1f2066338020016de0d8050023720880000b11a0480181c0182200a8241c60147a807 0x1056ba81aea55540b40d54da01a6855534b34d42632798c41034f34b2e529628b55529146441091144a41028d36330c8cd34a30c1d58851a21555472c71904078211d041382018d34779f1cd34f79e14a2876471ca1c564508b09b5556c16c254209074045d0104024426cd70269c08d35b69a00a00264208a0806406185c21d72d650b5544d14414104914414103cd34130c38d34130c2cb24b2891871c81452071c61451020810000c2081000⟩
]

def nodesBlock30 : Array Node := #[
  ⟨195,8,[ew367,ew490,ew509,ew535,ew537,ew538],localHints 6 0x860840d8490414080c2d6072b541783f5a80480585a0321750d0521009942f0460380780a8356d80040202c06c0080503c044000080136d20c1b38030480240384e11a01406033 0xd2c738725964f2c700d25960ce54e7af5963ef5550ce58e3ce4ad4e5bad3e549284e78e0c85abb2656baa65960c85488484694c64a94c64518484887a63a83c89683c838e9e69650c15966d98e46d95960c18c16db4926c18226c14926e18206db38e6c175f6c138e6de75d6d92086c169c6c12086d96990c25981cd5585cd5960c25424c24941c54544c54921c24423cd3901c23103c238e1cd30c2c520a1c218a2422081c51851041000c2040⟩,
  ⟨195,7,[ew322,ew426,ew470,ew509,ew535,ew537,ew538],localHints 6 0x860840d84904140c0c07f0720a81f8120164a80b82c0c20c09581505cdc00a0620340c8210040320056b8270140087501602638c001f10120740f0ed006510b180f00e0148919801813804006 0x5b5df669adb5d1669a45b47369acdb6d1691456c6bcb1ad65915512dabecc2fb1a68b30b2d72ee596b975cb58bb11b4baed2d146caeb1da6a96eaa5a6876c7496a075e81d65a25d74914474e71d14554d31cb98836620b2c734705a6a46e591a6816c14968c18630565a28614914417e00514557df04b78335e0cb2c13410c774121d0471c320339b70c69a31b6ce69a6575d85966175d25965534d44515134d245140d3ce2cb38d34c2cb08820a1c72481821c60830c5041103002040⟩,
  ⟨195,8,[ew367,ew426,ew470,ew509,ew535,ew537,ew538,ew544],localHints 6 0x80d82182103612411020a0a06001957054120058230c62500b81c0521740a0800340556a8e3a0814c1205b002064f9827004b5c050160003a8098260241fc0f1130e403c0289212a07406006 0x298dd76174f64d129144a4535534f3d745d7d33c935d7a71a4f28f3ca3e93a93d63f05d7c1658f5cf3d3ba9beea534cf38f618b4b62d6175cb28b618b0b451ad34eb4512d34cb3cfaa9a6a3cf2e9a4aa2818a186a062996465d79565a55d71961954d31919c64d355144e3cf18d9863cf38d3652cb1891862c694994a92404a0419012a38c15d779659e5d70560554d30618814d356184e3cf05f8013cf39f7de2cb0490412c17897811c10c61831dd29c6cc29a30a30a6590975d85966175c25965534d44515134d245138f3d034d40f3ce34d28b2cc24930b2ca249207142185103002040⟩,
  ⟨195,8,[ew43,ew367,ew426,ew470,ew509,ew535,ew537,ew538],localHints 6 0x188210fa082830180720a8240600c62502d00d0ba0504001a5ac09c0b01304c07c0f113110014490c103a0183f8040027541b00a0043a81100001616c0900304603c0b8290380300a8241c627467840 0x4d8e78079e18613393418436077d98610390413d0fd743d34d049038eccd64d39860d514c934f25143534cd410c4f3f141034f3cab30258c09b2c2986164d3294bca4d35945124102a4b8a4104a490934d2a128a34a26124662d16cb456181acb164d31aaac64d35aaa924101a8a464104a8a0534d1a11863461611467c670a29c7e76ce6ce61838101b6185934e65149934d651449042592495041292488d3638618cd36286181f79b29e75c69b19a3995ce6175945014d35545014d34904013cf4504013cf38e30e34c10a28b2492ca2812492061871451c61811451011010000c1081000⟩,
  ⟨195,9,[ew367,ew426,ew470,ew509,ew535,ew537,ew538],localHints 6 0x860840d84904142c0c373072dc81783f02402c300631281280b85a01a1740a0800341181481501cdc6850400020101b09e00466805022150000cc813a13422838260060916c00903803c028230b607406006 0xd7e7b5ba6db67ae780d76db0d26924776db53769a0d26d25125f566edb552e5d75924520cb6f3d2f6b3caf6db0cb68b58b5716485f164855558b5cb46f4b050bbb050b49246fbae0c66db2a96ad1296db0c669a1165d728656c1065d729655511149228642b1064922914101292cb28622a1062cb2a92080c16db8609e81e06db0c19e71d65d78419661c15d78569651d14928418e41c14928518e31e02cb8417e21c12cb8607df1c11c11041861c41de0c26db29c69a75c6db0c269a6565d72985556585d72965555114922934105134922914103ce2cb28c20834c2cb2892081c71c50c21851041000c2040⟩,
  ⟨195,8,[ew426,ew470,ew476,ew509,ew535,ew537,ew538],localHints 6 0x10c1081b0920801f0180c83b82002504e0580f80b03a00c1a8040580281e0100261a04d02313601c1b8011ec034170020280f400011034078270531262880400600a0700b815 0x4d0c32a31514a31c2f4d05144cd80d9ae5149ae8204cd50db4d42cb64b6c9a441098d98d4d351494a82ba8a5144d3820aa879e94a410a8a79e965410aa634d94a924a8a34d9659244e35149698209695144e382096879e96541096779e96541096634d96592496634d9659242082224e32a24c352161c82161c5144c380360341f61679f61641060378361c35d6036dd60334d61c6db6966966832836036036162966962566836436036036165d64c451508c49508c5144c44840844110853d10854100843c408c34e0842ce08434d08c2cb2052052042840840840852852052452041c40840840851850800c30840440840c3080040⟩,
  ⟨195,7,[ew426,ew470,ew489,ew509,ew535,ew537,ew538],localHints 6 0x218210361241050d0303b8321570541200226404f4307a01637602c2980303a3d81a82c0140f00801313426c03837002064170020280f4000110340480f09309c2880400600a2543936e 0x433d744d3d33c904d33523714d3c5248d4cd350be2c2f89040d8cd7934cabad2934de7ac29b6eb410adb6ca41028d36a8a2a8d34a8a27d34de4a97934df492a1b6e74109db6e641094d3648a290d3638a284a81f2607ca29e2490d375949d6534c34830d07156dc5504036c364d68361a0cd35961854a5432430ca0d52555475435c30c70d559511350c4943134c44841104453d11504043c430d3842ce10d34c2cb14a14424410a1052451471442041071051850430c40441030c2040⟩,
  ⟨195,8,[ew426,ew470,ew490,ew509,ew535,ew537,ew538,ew544],localHints 6 0x406c10c1081b0920881050f03000cab82a09002e870aa04edd029016376178130ee0460d41600a0780400980712403c0e037002064170020280f4000110340480f0082260300e80500c254392d5 0x828e13a1343741c81c720710990434db54d3d74cd04d3ab2a8d80d36036a8ea3523714d3c5248d4cd350beac2fa9040d8cda28b8aa2ea134ca80aa28b4a71cb1042c71c29040a34daeaaab34d2aaa81555841841555801a454d3a124a84d31524814109e59414109a594134d92288134d8e288128a84924128a8092587d81021047c46026044de69279a4d311210441d61c75841011c11a35b1196c434d6996582981091042846096015d61051085480c10c35432012034d431250c4d30d20c341120f4484100cf0cc34e0cb38334d30b2c82880c90c32832092011c60c50c11040c10c2040⟩,
  ⟨195,8,[ew43,ew426,ew470,ew490,ew509,ew535,ew537,ew538],localHints 6 0x188210fa082880180720a8240270a40582f02603e0b01e0100262480780d05c0501e8110340788980c03ab5877004002dd41b00a0046ec110000162a8090033ac274298400460146080703801844008 0x4d8e782f9e186133934184362f7d98610390413d0fd743d34d049038eccd64d39860d514c934f25143534cd410c4f3f141034f3db61838120e6186ce6c14d3c2fbc14d35afbc1410badb414104adb4134db1e78134dade786906a186289241981864ea114a844d31941a84291a7a46410a279c434419e18634611e1019a519b1826028249206180a40824e30228c04d30a20a042109f84241081f7c034009e08234201e00175c09b08118608108505a3995ce61759450b4d355450b4d349040b3cf45040b3cf38e30e34c04b2830490c10c12081461871041c61851040420830000c2081000⟩,
  ⟨195,9,[ew426,ew470,ew490,ew509,ew535,ew537,ew538],localHints 6 0x860840d849040de00c377072dd81783f088b500900b0800644f1bc0a42a13305e04d4440f0350080b00503c02004c1800900e03c1b80101a0b80101407a0000881a06400c070080182a80e80500c08c0e371 0x191e7ba3a514a3ae7819151418e7ce977514bf77df18e50ebce475dacdb5bec451a0e94e18a533d2d7f3cad51418a7caa0a771a18471a1875da0a44a96d3b0bcab30bca38ebadb2c18551406baaa041514185aaa0414510699e70414510689e704138e06692404138e06592404128a06386104128a06286118452009b7e009b5141847c408445e09775e09745108474409b39c08469c08438e09b69a09729908461908428a09761704109618414418351504d4d504d5141834c304345204841204845104340304d38f04330f04338e04d30c04828b04324b04328a048248041047183143041104043043042040⟩,
  ⟨195,7,[ew426,ew470,ew472,ew535,ew537,ew538,ew544],localHints 6 0x80bc218210361243282007c0605dd130074480e9142ae0a82400b04605c1602501425430816026014233790120a41b8010320b80101407a0000881a0240780403300e0180a80f 0xa64cd04d0353c9ba726d36cd70d36fc70410c2fb8d410813b4aa4a2932a062028f2ac410b0f3ca40a28daa0aea80d34a60aa689c74e79504079871d04259231cc32234d88c30734d1ca2a182084a2878200df0c04d301f0034c30d041e3cf7904033c368d7436dd0cd35c6db68a2835d90ca2985d70c75801960070031831535425020930854850904493d12504023c208d38530e14d34230224a2c220b08a289208147142182087085185043102004083081000⟩,
  ⟨195,8,[ew426,ew470,ew472,ew509,ew535,ew537,ew538],localHints 6 0x4304206c2482007c061bd02f0ca1001380b03a00c300170080b01280a0c2058098530d02680281c1360dc0091401a0b80101407a0000881a08c2ec049120526600f80809c0cc3580700c08c0a80f 0x615db8977659977db56156596129d28b46598b49e7612652cd2572ceccf28ac55589289260d6592499e73b165960d9cd3a593024d57038d9242495553a249224db2f38d492249b2c62b65926e9e726e65962b9e726551424955526d514249555262492249b2c262492249b2c1c71ea62b36a6046590a89e90a86596049c40825660849260845550a59240824920848630844920a28617c47c47c034d08008008434414481d7c079d0807000846c460365a2d15da1516596035c31435562c85161485552c35031514932c34131434922d141014834f3832c31433432482481483082432c31432832482481c11061c3006143103081000⟩,
  ⟨195,7,[ew426,ew470,ew473,ew509,ew535,ew537,ew538],localHints 6 0x21821036124105140300bc328271ce0580584e0060748a0170080b1bd80a0c2624098121340140e09b06e0040c82e0040501e8000220682300903c4485d998352020dd03300e0184a80f 0x4f3d74596d33c93596423431596c638d0590413be9c2fa534d079031659c8e371658c8cc720b8c4ee32081c4d371040ca6d31041ca699965a58e39565a68e3ad24ac4d3b124a14d3ad042aa69a9041ea69a1c9e632799c72530c0d65a48e39165838c30538838220d34e182005040375f0d041e75d0dc0c030c01c0033030d96806da0190036030965cf5573d65825420935064941934c24823d044239109040f38e18c3422c208c0862c618a1822420880861c6143102004083081000⟩,
  ⟨195,7,[ew246,ew426,ew469,ew509,ew535,ew537,ew538],localHints 6 0x4304206c248200980603202f0ca1803182401600c0b8370323540a03d0220680f03309c109bf0040020d80500205808809861000098048126fa03c02b7c12a03003806 0x42ec2f4d3beeb504d32d42ec4d3b1450b4cb2d0aa3aea8d040b38b2534c85292134c9509211a0942825144841020b2c98e724b2c88e31934e15268534c651449d94641019d76441038b2c68e318b2e48e38488862621881a124901381b7e06d34c07c001079675e5904007406cb70069c00b2db69a5895806400090166565976001980170161960540554d35545014d34914414100513c340f38d3412cb04d3032cb0490432082892412011c3141185103081000⟩,
  ⟨195,8,[ew246,ew426,ew470,ew509,ew535,ew537,ew538,ew544],localHints 6 0x1240101b04304206c248220414580c0032ae0a82400b046dfc3189402e070148370320b80a03d0220680f0083740ce8a84e17a10000ad904e0280118902c04c000bb6f4098090aa0e403c0285b12a0300e806 0x33be955d547945231248c491511476e37555df6d51555b34b0d30d34c36c42c363373555ce38cd54d351c6ccb1b1144d40d5d7c095f05d55493095d7bc9492b9146e49225144934db6cb2d34d26cb03aeb183186ac6303a865559e38e75551a3183451192a4645151248334d18ea0634d40e3a724919d1862469dd9dc99c00c0009807257005647e391f55502300046272189c45102101f36001e80034d7de79c25c01d00024071d71b6da0070031863036436182832836180570575555c35815555124834514d248345140e38334d3ce38334d3032c3249283283249207141185103081000⟩,
  ⟨195,8,[ew43,ew246,ew426,ew470,ew509,ew535,ew537,ew538],localHints 6 0xc41087d04145c0c039054120300631280b80a03d0220680f1f20660341381602607c130aa1100142d80c03a2485d804002b681b00a004624110000162f40900304603c0b8290380180404037a2746084e 0x4d8eb90fae586133934184370f8dd8610390413d4fdb53d34d049038ed0d64d39860d514cd34f35143534cd410c8f3f241034f3ca9b1258c499a62986014d3294c0a4d35945014102a3bca4104a38c934d2a928a34a269246606ae69ab6181a61864ee16db854d31ad1ab42c1aab06410aeaa853451a9186346169168a2719f18128a6d860e9a639861b9a65945014d39545014d34a38c14109238c141088188134d84184134d81f79b29e74171b1866995ce6175945034d35545034d34904033cf4504033cf38e30e34c04a28b2492ca2812492061871451c6183145001001104043080040⟩
]

def nodesBlock31 : Array Node := #[
  ⟨195,9,[ew246,ew426,ew470,ew509,ew535,ew537,ew538],localHints 6 0x10c1081b0920828d0187040e5c082f09a0fc1451902402c300631281280b83701a0b80a03d0220681902901c02019840008004fa09e0140090d8a80260028c0260121380181c01e015c00230182f40e806 0x92e3a579596bf9e3709259608e5ce476596b765d708e58eb4e4b4bead74b6a49254e44e0895b2ceb5f2c6b5960895c95494f0bcb4b0bcb4d354948946b3aeb49aaeb4938eb2baaa0875961255e91255960875d71044921074e81074921154d310438e1073e710738e1113cf1252491072e61072491252cb0805a471f8e421f5960808c02004a271a86221a49270084021f3a07007a020038e71f79e21a25d7006dd20024971a6da28a2992002001041c70815d72845961185d70815961154d32844921144d32844921113cf28438e1103cf28438e10d2cb28424910c2cb2842492082060811c6105103081000⟩,
  ⟨195,7,[ew426,ew428,ew470,ew535,ew537,ew538,ew544],localHints 6 0x8140218210361244102007c060253830480d41603c02004c5e51c00746c0e9152ae0a80504801601c0e00e02a0040c82e0040940a0720c40000b01a0660140b8060240300f008 0x85ccd25123d4c9987265464f38f3efc70492c2fb8f4925d4b4a84a2942972572912ac492b1144a48a28fa97aea5cf3ca24a594a46a061941969d61929a34668d248644618f95666558f3c66468ca9068a418a2a38a28607c351f7524837830d249d71b0d965a3cf6996433cf0ca2985d760a2835d70461835960c61815960150025140950805000124934514d248044030f40035000f3ce34d30a28020b00a2892080861c0147006182142003102044083080040⟩,
  ⟨195,8,[ew426,ew428,ew470,ew509,ew535,ew537,ew538],localHints 6 0x10c1081b0920801f018708140410350580f0080130942f02000404e0280581d006090a207a2c607c0385a02a0048a80d05c008128140c40000b01a01c1381980502e14c4980601807051008 0x552d36475596475d3355259654e90e37259637292454e58ec4e4b0c61c7036149234e34e54b59669a9249af59654b9249918ae68b4ae98b8a269a49298d38e68b86d98b38e69a8615485ac7a992c7295965489087084ab7998ab7194927888887293aa788a2a70838e7a9a287192e79887887082c86996995605966a59246a55965609246918a269a4926a38a269a49268d38e69a86168d38e69a86128a29f5602df69e20871d65971b20869a65954059609751809759654050008249308041308049209141008238e08030f08038e08d30c1801801832cb0830830802c02832092801c90802080831c3180184183144083083080040⟩,
  ⟨195,7,[ew426,ew429,ew470,ew509,ew535,ew537,ew538],localHints 6 0x10c1081b0920828e8180a02081a8190580f0080130940780202701439c0b00b09c00c0e915178510b19a900e0540080d05c009c28140c4000c501a024038dd03300a1c84980603803051008 0x4b4db5555d74cd25553943b2555c9450e54e392c20c7081248e34e29554b5142d554a50a2e3bca4af2a38cb4922ce38a82e28e38b8201d5b69b2da55547b071d2ad78eb5d24878c7a4ea87a2a1ce3a9a285ca9c79871ca1d799775555c52571555d5148a38e44929238d149288e3a182084e38d8207cb79d29e74b2dc28a6c71da5d76471d85d70155565145955405001924c041301249141018e38030f00e38d30c00b00228a08b0802800872002480071c2182003102144083080040⟩,
  ⟨195,7,[ew291,ew425,ew470,ew509,ew535,ew537,ew538],localHints 6 0x4304206c248200b2060320501040d40c8d50780400981e0b41740502901600c0a83309c109c380d0021340a00205c0a00d0620000980701270c03c02b7d0e402006006 0x42ec2f4d3beeb504d32d42ec4d3b1450b4cb2d0a9baea6d040b38b2534c85292134c950921da0942825d74841020b2c96e724b2c86db1539a29668934c594515091676459040574588b8c586314b2e28615895858051491568160534d951f6534c151449d78141005d75c41038b2c16db04b2dc6db64868125a0480592490456175985c51415960940954d35545024d34914424100913c340f38d3422cb08d3032cb0890832082892422021c3182145103002040⟩,
  ⟨195,8,[ew291,ew426,ew470,ew509,ew535,ew537,ew538,ew544],localHints 6 0x44c020360860840d8490440828f81800655c1504801608c120350580281e01002601c0e3880321744001e02a6e819d1e09c1ec200015b609c0a0023140580d000178e10130120b603c028aa0e407406006 0x2fae545944384262e698b9904d0435df6514db5d10514af3acc2cc30b32b3eb31f332514c9f7cc50c310c2bc70ad040c3cc596bc85af5945082c8596b889a6b5042d9a621040830cb2baec30c22bae2aa214b145a858a988552891fa2451415f1454278a69e241016616432516394530c9238e222215c14520589c8838610430418412c38015146df7db51405f0434100517814104d144330c04d74130c3cd35b20805c0412016dc6da6990c51410c12c36035d72432435d70960965145835425144d14434104914434103cd34330c38d34330c2c32832082432432081c3182145103002040⟩,
  ⟨195,8,[ew43,ew291,ew426,ew470,ew509,ew535,ew537,ew538],localHints 6 0x188210fa082900180720a82402c0780400985a0ba2000f1f20660341381402c0680f8260b603c5501d00c44c5e004002b701b00a004628110000161ec0900304808c028070380300a84037c2744404e 0x4d8e780f9e186133934184360f7d98610390413d0fd743d34d049038eccd64d39860d514c934f25143534cd410c4f3f141034f3c9989b9862e9a62582494f0214c084d325426e42f26dbc9410badb4834826924934922920662c166b056181a69814d31a4ac64d35a49014101a2a864104a288534d1a9186346169168a2704924604672698e6183a699c6185a49014d39649014d34a28814108e288141084184134d80180134d7c179c2497416dc19b6995ce6175945034d35545034d34904033cf4504033cf38e30e34c2c924a2082892432080461871451c6181145001001104043080040⟩,
  ⟨195,9,[ew291,ew426,ew470,ew509,ew535,ew537,ew538],localHints 6 0x10c1081b092082910187140e5c482f06c0fc112d402402c1a8040580281e0100260c01182401201c2d05d1001180a833080034009f513c0500121c1500680052104c0382700370003c0281c0f607406006 0xd1e3a539555bf9e370d15550cda0d436555b76a280cd54db4d474bead74b6a45150d40d0c8572ceba32c6b5550c8a085089b0bdf470bdf9a650844842b36eb48aaeb4834db2baaa0c5569824a298645550c5a0584546781e9a785e4518059858643658058e584534d8248e385e2228057e284520881e7de0c155511959d1195550c159610445110149c10145111449210434d10139b10134d11038e11920810129a10120811928a2492581041451011010c25962445551175960c255511449224445111349224445111038e24434d10f38e24434d10c28a24420810b28a2442081071060c21451041000c2040⟩,
  ⟨195,7,[ew397,ew470,ew482,ew522,ew535,ew537,ew538],localHints 6 0x10c0d84907c0602d00d05c11c310451ee094108160400702983505a0f0080132b0054f80070720040202a0140081f80002402dc58080643600488e00a00c6801f 0xeb6e8524a1b6c39248c44c7d249f45131230c3aa2aba8a38e3203084925a8a564922282173a72269c838e8a699730c22494830c8249044928d144149211144138e8a184138e8a184130c81f7c130c81f7dd20879659e20875658349c6517194920d10c338e6cf3db38e0cf0d931a0d868330c6586172080d60c32035d65815540c40c24932d14cb4920910823c240e3903cf08e08b30d08a34230c2ca2892470881c11850840810c3081081000⟩,
  ⟨195,8,[ew397,ew426,ew470,ew482,ew509,ew535,ew537,ew538],localHints 6 0x2181b0920f80c0640a0208688210400d41683c02004c0f0070b4034170140c4069c6053038098148151e8004020250140080b000016560070030481700e80509c1e80fad21dc87404006 0x4b4d6c596b34cd259641542b596ad5550590412c4fcb13d24904503565a557095658d555513bcd4af3534c549245040d3ee3504053cf2965ad55519658a555192494b2c192494b2c190411aeb190411aeb70d35a96518d35b965216aa756a9d65885482124a94d3a524884c89d0a089a82104279a618d34894820d2059651869082880565988a361658188151284182105249982045040179f05041979e04e04334d0ce7586d805c0416c161a6182080460412086196025961555575960955544d31524944d315249141014f3d141014f3ce38c08d30614b08a2462081c61c6145103002040⟩,
  ⟨195,8,[ew295,ew426,ew470,ew509,ew535,ew537,ew538],localHints 6 0x21821036124100250980603201e05e1941a80405a0f0080130601680a82e0281880d0460520cc2000d0020d8138020140880b00b0000704d07a2c60382700900607c038ef03a01412026226360cd80817814c06006 0x31cefd7bc7dfe3cefa31c7df317c176b97df679c303177d7657736e18df665871c6976973107df3b4c350f47df310c100de6f33907330d06db39e71c0da5d73906320d05d739a61830a7f126dc3152d7df30ac0a50a71c26f6db52f71c24a6ca52d5ee24ab2e50a5d726db2c50e4ab0ca42b50a48a38e4103047df8e982a1a97df30480419e7288c49e818471c8de9e719a5d78c49661845d78da9651844240c14a41814103844841812a25048e218428a24124130b8202617df26182030b7df25e71c2496db25d71c2496db25a6182495d72596182495d73964920d541051348f19140f38e38d30b28a2481041870411851000c2040⟩,
  ⟨195,7,[ew295,ew397,ew470,ew522,ew535,ew537,ew538],localHints 6 0x10c1081b0920801f0180b40b82386208a0d41683c02004c6c0f40080bc32b8d08c0c07b80d0020081280a0160580001c01014c0a94503e01c029581a023804803 0x12b2eb534edb2b4934cd6cda934ea6db35334d4a83e9a0f49234e34b4d32549c94d32d42dd4a62e598b49246595d34d2e390b34d3a38c54e27db89f4d315b14549285042149215015f36015e80534d7de79d2cb1491452c57492414d31db6dc4d305b05141a0526814101d248e34d04f64134d1cf3d861704b5c31d60c51411c10945154d35545024d345249141045249141038f3ce34d38f3ce34d28b2cc24930b2ca249207182145103002040⟩,
  ⟨195,8,[ew295,ew397,ew426,ew470,ew509,ew535,ew537,ew538],localHints 6 0x860840d8490400f80c0640a02081a82d0780400985a05c0503101a71c0a47a0041b00245e00c1a20340080204a028058160000380f01f00e0141301c01014c0a87a0461707781d 0x531cf2555cb1c145553dc3ef555bdc70f54f3d4b51bad45450f40f39554d72c35554e71c4d2ace52b39248c51440f3ce46a38f3cc451295a6672999554a70a294528492a1450a48a98f9ca96728f3e696530e38a34a28e28c34d1d55455a41555475874d48c78a31d451e8a240f3c78211cf3de8201db1d938e65b7c528a1de1c728a15e14155531c71d55505c7134923145134923145103cf3114503cf31145b6da04e68430c10a28c30c6596011c70965975555d65825554d45134924d45134924114503cf4114503cf20e38934d10e38634d30c2c228a2471c81452071c61451040c2040⟩,
  ⟨195,6,[ew397,ew467,ew470,ew522,ew535,ew537,ew538],localHints 5 0x218490301681706208a0b03081308405423d2311c020028040020bc050020ca0000584600e00c09009 0xeaf8b32d86ded065e96ece511360d75b163b5909354d49cc725b16c8a228314c5839ee6b56c5814a4a0c73148400c2310820⟩,
  ⟨195,7,[ew397,ew470,ew522,ew535,ew537,ew538,ew540],localHints 6 0x40860840d8490400f80c05305c094238720c4058228d07200d41603c02004c2101702a00c008f711c55c1500a0041200000b71e290040f40240140f807 0x103ec44f44b88b31030c40c2e22cba6ba9146aa682d144878825024940921e2093c99d14674272512492e52269482cb25e2453c54e44d33d314f1454514e04d345114f1602e31618c52cb8a186024915d7c524979d74070009008270201b00245a5d069745108f0822d900c6402cb08c0972580966022495d65941550930821425134cf3d20cf48f4510d00cf3ce0cc30d2cb34c3032cb0c924a2082892432081c71831451020830000c2081000⟩,
  ⟨195,7,[ew397,ew426,ew467,ew470,ew509,ew535,ew537,ew538],localHints 6 0x10c248180c81404102c0c204c250473e00142d02e0281880d00e72010807d240020100500200002c048241e801c0e84e0b87c406008 0x263e53cb3ce2e490c2cf8cf3a288d30b84b28f38f1a080c34b7cb79d75418f38f39c31c30b28b29b50351a68f64f01860c5cb58b5405134921910100c03ce3ce34c34c2ca2ca2492061c61440c2040⟩
]

def nodesBlock32 : Array Node := #[
  ⟨195,8,[ew397,ew426,ew470,ew509,ew535,ew537,ew538,ew540],localHints 6 0x204304206c2482007c060280820f54941a82c0780400984a03c14c170140c40a40d3910840540781d002344200250140080b0000161c80900e1e80140f80716a0442e008 0x481c5305339038f48f3d23ce40e3aec2f4d3beeb4e4d32cd2cc48c31230b34b30132c4d3b12b0c4cc30ea8baea2ce38c34c20121f79f7c17c80482134df49f7d34c804840fa483a920f3c538e34c3082e820c3052cb1271064861a71849841939624a58934c604618e9043e410e3863c688c8c686318c3228611088067c61881847c40010167965815800400134d64965934c004040e74071d00e39a71c34c30065b00c31a65900a0032080ca6161860155c01865955410540415014d305244104140f3c538e40f3c538e34c3052cb34c3052cb28a2412081c61851041c61851040c3081000⟩,
  ⟨195,6,[ew397,ew470,ew521,ew535,ew537,ew538],localHints 6 0x860840d8490414980c05a4c80b89f0e30c46fc680605ba5dc1684f0260140a8390020346b00a0040fc000120160c82980802000c0b846 0x2e59e63cf9a590b3cf24e2633cf8ce3893c924b8478a11cb2c968910f3d13a044f3c43847cb78431e10b2dd30c7092444db10925a4d35cf3c36580cf3d75d60cb2d530c54b2c330c0c92544d35092434d30444834520c410145108f40839020f3c238208c3402cd00c3022c22092821ca0892481c7005182106085080100003002042083080040⟩,
  ⟨195,7,[ew397,ew470,ew522,ew535,ew537,ew538,ew543],localHints 6 0x20250860840d84902c08293818038e4c1739208e1c4311bf08a0144717705a13c098151e83400f8390020341780a0040fc000120167000403202000c0b809 0x1266d3d93ccb0c2d22cb48b32030ba6ba8f3eaa682cf3d59d525224948955c54938998f3e638e24f2492e41e59072cb25c25e8e315e1458c549e8853cf50e3943cf14e15e2e115f8452cb81f7de24915b74524971b6d965a0d96993cf0d20d96580cb2d730c5cb2c330c0c92565555892435550451435030c514151401300248209208044008f40839020f3c238208c3402cd00c3022c22092821ca0892481c7186102144003002042083080040⟩,
  ⟨195,7,[ew38,ew397,ew470,ew522,ew535,ew537,ew538],localHints 6 0x620843e820a500602d02e08e1882283505a13c1783f02402cfb03202e340020017280940100a37e058000130380204481511c0400281f1e800c7b809 0x1156ba81aea55544744d54da01a6855534734d4666a799a45134f34a5652099485552872894642a390a4514e38c934d2a188a34d3e18471e019618755519145f4107d144641018d35e30c78d34630c5ca28620618a29720808709b5556c16c254209074045d0104024426cd70269c08d35b69a6596022980060025c20860805c01d65075544d14414104914414103cd34130c38d34130c24a28b2082ca2892081c71471851020810000c2081000⟩,
  ⟨195,8,[ew397,ew470,ew522,ew535,ew537,ew538],localHints 6 0x860840d8490414a40c05a01a0b82386208ab801aadf0588793383c5bc0400984203805c0a8397220040202f04a0280103f02c0000900b0a62380403271c0c1c600500607c04807 0x291c738b25964f2c7029159628e54e86f5963ef55528e58e3ce46d4ccbad3cc45188e84e2895966d9aec6d9596289ac96db46a6c9a6a6c94516e2a696db38e6c99e86c938e6e19e72845a599e56591e5962845448844634c04a34c045188448485e3a03c47603c438e7de75d6da25c6c46446c42446da65928359808d5585cd5962835434c34940814544c14920834433cd3900833103c338e08d30c2cb2c82832481c1106083006143103081000⟩,
  ⟨195,7,[ew320,ew426,ew470,ew509,ew535,ew537,ew538],localHints 6 0x10c1081b09208295018258078178650f40d41683c02004c1801505ce540a0620341181980401a004bb027004028758160163d00009a2c6038048033e201c0e8171de0148999b01014c06006 0x5f4db569ad74cd769a45b47269ac9b6d1691457c13c704d75d155135a6ae6efb9a68d6cd496b4d5ed3565a25d749144d4ec3514554d319aaa7aea9da6861c61975e9596a575c65869d1a069a81914679a620e94636518e18834d0da6a46db91a6836c34978c38630d75e28614914437e00d14557df0cd78139e04d34338304674321d0c618120125b70769a1db6c969a6575d85966175d25965534d44515134d245108e39034d3ce30234c2c82891862482071860830c5041103002040⟩,
  ⟨195,8,[ew397,ew426,ew470,ew509,ew535,ew537,ew538,ew543],localHints 6 0x8094218210361240b020a5806013050104014bb82d09e04c0f01c0520b80a062034b7c0a8f4a561380f85c002034fb8270145d8010220003ac059120e2038018230201e80b89316c07404006 0x198dd76174f64d1191446453553473d745d7d33c915d79b198f18f3c63e63a63d63f05d7c1658f5cf3d1b8dbee35144f38f1adb4a18a2862866592975e55969575ca58a553b0a46c2934d545138f3ca36b28f3ce34d618a8762a6175c7187618a47451a134e84511d34c73cf9e69a73cf1e698528a1e51c728a1651469240460419011a38c15d775659d5d705605546206188145156184e3cf05f8013cf39f7c12c10ca2832de7471c114104705d15d19c6c819a2062066590975d85966175c25965534d44515134d245138f3d034d40f3ce34d30b2422891871c81452071c6145103002040⟩,
  ⟨195,8,[ew38,ew397,ew426,ew470,ew509,ew535,ew537,ew538],localHints 6 0xc41087d0414b80c0640a02081a82d09e1680c82e0281880d2e004f4b41100b2242240182304805c498c503a0183d0040027e0128020143ac0b0000260980701e0b8040028290380200a81f1e821868840 0x518eb907ae586142d4418437078dd86102d0414d64db591451049036dd0c63432db4d618593ccd5333534d651449040d9323504129242cbc4a64a2d860a514c134f05142934ca410bcf3ef41028f3de34d28c28a34d78c78662e16db856181ad19652c1abb065145abad24101a9a864104a9a4688670d35c8a814a28678618a1857856cb6cb6182c101b6185934e75149d34e65144904259249504129248e285b3617ca2a079e80a29f79e75c69b19a2d95cb6175945014d35545014d34904013cf4504013cf10d34e30c38d34130c2cb24b2892061871451c61811451011010000c1081000⟩,
  ⟨195,9,[ew397,ew426,ew470,ew509,ew535,ew537,ew538],localHints 6 0x4304206c24820a6606032050104e601ab970580f0080130940782d00d05c0503101a72c1081481501f4c8200010086a81289e014b4401016150000ce00b03803801d31a614bc1180503eb60038260b807404006 0xd5ebc6bb71c67beb90d571c0d26d247871c5386db0d2712512576650df65105556924520ce71c1ea6f512a71c0ce6db11a5f41ce57410e5d71da5551114921ce43310e4921d14100c8731cad6f1c2d71c0c86c868856f6455ef6455556885c846d4ae508b2e50849246db2c1c53ab108a881083881c5a850c171c860a293e071c0c1a013da5678419a73c155585a9a63d14928419253c14928519243c13c110438e3c43e33e02088417e23c12088607df0c271c1dd6db79d71c0c26db65a5d71d85556585d71d65555114921d34105134921d14103cf3cd0c238d30b2081c91452892081c61451041000c2040⟩,
  ⟨195,8,[ew426,ew451,ew470,ew509,ew535,ew537,ew538],localHints 6 0x4304206c248200980601c82f07e0480586018e1000203604e0281101604804ca20680a60984d80903a0141b80128c0342e8020280f40001103400c0f01502e0202709200c0705180c 0x4d0cb4933514933cb14d05144cd94d8705148709654cd50dbcd42ebe9bee86941084d84d4ca52d6aa96d6aa5144ca94a68a8ac69842c6988a268a40a6aa36b68aa6b68a34d6aaa694d35147c79689c75144d39659e44107c78a29c74107df8a29e134d7c779e9c734d7df79e70728a71c6189da28a6876184d75147e69657e65144d79657e44107df8a27e34107df8a27e134d7df79e7e034d7df79e71d28a71b61869a28a6996181451564d71d64c351508c49508c5144c34830834100803d10804100833c308c34e0832ce08334d08c2cb08828a08324308328a0882481401401431c30830830801c0140146143103083083080040⟩,
  ⟨195,7,[ew426,ew470,ew509,ew521,ew535,ew537,ew538],localHints 6 0x10c1081b0920829a81800899013d341c6058e083905e0fc0900b28826c638602ee0b40504f0261380281d3f20241b80101a1740101407a0000881a010248298a30062d838b930200180b80c 0x474db5514d74cd15143933b2514c934ce50e391c24c7091144ea4e6145174ef5d45184d3b9146d75db5146c75dace3aa6dba8e3a96db1d4a254e89545074c71dd9d646759d74744794e9879261ce3a59245895878c71c91d68965d45038600d45175df0d145e75d79144375d0ce39c6db70e3836db0586436990d80c15c10471c35960c71c159609454d4d53545024c209144041201144240234e3c230f08e38d30c0092c22820890802001471c21420871c6144003002042083080040⟩,
  ⟨195,8,[ew426,ew470,ew509,ew522,ew535,ew537,ew538,ew543],localHints 6 0x404a10c1081b092058105370314d813b9908e088e084504c0e41783f02402c4980e00a2acbb82d01413c0982318e0240e0370020342e8020280f4000110344480401d0062d838adf0200180b80c 0x5dee137936f76d05d041741bb1b434db54d3d74cd04d367264d5cd357359a593523714d3c5248d4cd350be2c2f89040da4d15555815815555716e2134de4927934c849215042daeb15042caeb14d36aa2814d369a285a75875c71d71d61961d39a34a68d34c74871db95642559b6c74078cd9078a41cd3638a216180720779e7c379f7934c35c379e74341071b6dc4100db6c334d69965a34d0d96416010c50c31430570411c70d65831c70565805400850825420050024d431250c4d309208241000f44041008f08c34e08b38234d30b2c52890880851c7085086144003002042083080040⟩,
  ⟨195,8,[ew38,ew426,ew470,ew509,ew522,ew535,ew537,ew538],localHints 6 0x188210fa0829c01804e11c1104505e0fc0900b1260381a82d09e08c120190ba0501e8110344480401d5c005c63804002e68128020147040b00002675c4304e080098018c50122ac080050380184480c 0x518e783b9e186141944184363b7d98610190414d2cd74b1451049071860604b19861c19c054533cb2054516cb2050431c30050412c3026426d618b64909609253bc752f1d34c9509b50b89b2e25042db2c06ba89709186a45645198605514a134e85141534c54109cf3e741014f3da99a1411450456a569a2491471c52496871c26028249206180a40825140228c05140a20a042109f84241081f7c179d09c08124908108805b0050026820850806801995c661759450e4d355450e4d349040e3cf45040e3cf04e34304c0c10c12cb20924a1c72892481c71861061440420830000c2081000⟩,
  ⟨195,9,[ew426,ew470,ew509,ew522,ew535,ew537,ew538],localHints 6 0x10c1081b092081ce818080278238a808a0e41783f02402c0739c06ae6c0202c3840293403c088b78080130474e40b83001201c1b80101a1740101407a0000881a0102ac0e80304ce581980600a0700780c 0x291e3a8f95148f9e3729151428e94e8765147f696528e50e7ce474d6ad747ea4518ce84e2895140b34d30825142894d30824510b2c710824510a3c7108238e0b0bef08238e0a1bef28852e1eb96e1eb5142889481c88ad1d746d1d78a21c84481eb3ac1c8aac1c838e1ebaaa0821e9288248283527a1d96799d5142839438c34648d68a48d64518c388385d3a07c37207c338e79d71c0996d90830830830830996991d62181c35d81c32081d65d628451508d4d508d5142844c408445108041208045108440408d38f08430f08438e08d30c08208b2842440822080840840870860800c50840450840c3080040⟩,
  ⟨195,7,[ew426,ew448,ew509,ew535,ew537,ew538,ew543],localHints 6 0x405810c1081b092184098200980601301e05e0281b0b60ca0884bd3b00b4e80e9162ee0b42780b006109cf0070520dc0080d0ba0080a03d0000440d0320120540701000c0300b808 0x85cd11511994cce8733943a69663b0cb1451c70bce451b54b8b84b2d42ed8ad2d02ec451b1040b44b2cea98aea60e38b88b1e91c55141611475141d1468410a114474079269c73a71e69a538e90b2c76231cb2e26188607c451f75144478411145d71b10d35a38e68d34438e10b2d961864b2c46180455c41d71051411c70945835430d40c24c20d148a4122914434030ce38234f08e38334328b30324c0cb2ca2491872031480c70c61450840830430c40c2040⟩,
  ⟨195,8,[ew426,ew448,ew470,ew509,ew535,ew537,ew538],localHints 6 0x860840d8490401300c06403c0bc32b9f058028308130800101b027044058058682881380181c136074028370024580685d0040501e800022068298320120980a80e08425c03913052514cd8060480300f808 0x697e7ba7a6dba7ae786976db694a949f76db9f7aaa6946d4d945f5da5db59e55d79d49d468f6db3b3ab43b36db68fa8f38ebb238f5f238fbae3a95d738e51438f97138f5143a79656896db0c3aaa2b06db689a892a95ef0c9baf2895d70c3bae2a75140c9b2d2895140c3b2c9093099243cf28e30c3893c969e6db0ebaaa0eb6db69eaaa0e95960c35d70e85960c35d70e75140c39650e65140c39659233211a23e13a030c39f3cf45145d69e25d6846dc1d365c1936db6846441845d71c25981825d71c45841935151c44951845141d349244d3d04443101843c438d30c18224b2841c41842440c20c21822020c41c41841440c2040⟩
]

def nodesBlock33 : Array Node := #[
  ⟨195,7,[ew426,ew470,ew509,ew511,ew535,ew537,ew538],localHints 6 0x860840d8490414f40c0272ac3a00b01e05f4f03298c0165100181c1360101600a0c204c2980503a458080370020342e8020280f40001103444c4b99b316020e00320122d80704200e0180b80c 0x535df65d7db5d145d74624735d7ce28915d1454c67cb19d4511a116d75da8a26975db8a2b934f0514c134ef514b9146d9e7b514689e71d75ec8a2b175c78871a0ac752b1e082a5141914479e91d14689e71e49459a51641478c70d75d98a26575c38836548438210d451982065144379f0d145979e0db71975c65b6436830c50d91c76451431c30976105984175c25820945004d50145024c24114823d20914503cf00e00234208c0802ca247202148087086145003102042083080040⟩,
  ⟨195,7,[ew175,ew426,ew470,ew508,ew535,ew537,ew538],localHints 6 0x218210361241003e0301902808203e180160610260140f03701a3580a03d0220681905302e119d10040020940100a05e05805865000e840700304601c083a016c02004806 0x46fc704d3c2fb914d32d42ed4d3b5450b4cb2d1acdb2b35144b38b2534e152a8534c951449da4946925d76745138b2c936824b2e734d1934c55261534c650615194642519144541014b2c68e418b2c58e318988586214924684601381b7e06d34c07c001179675e5914407406cb70069c00b2db69a5986402590180162565865805c00060165d60540554d35545014d34914414100513c340f38d3412cb04d3032cb2832012480461871451c6181141103081000⟩,
  ⟨195,8,[ew175,ew426,ew470,ew509,ew535,ew537,ew538,ew543],localHints 6 0x93008094218210361240b020a7e060133a30a02080297705a13c0981e0380a41b80d0ba0501e811034700190170194f82705317c10000ae104e0080518c04402c000ab0e203801b9f04625c0805c16c0200e806 0x1bced55d547a4521924864915114b7e78555e37d92555a75a4d18d346369429364374555d2490d54d352c8ecf239248d40d1b1c4a18a2862860f0295568924a1554a90a0d1bca4af2914544920cd34a3ae28d35038e5d7b455ed5d55451855d7b05492ad146b49215144534daa9a6a34d169a5c28a16814528a72871b9db0060009c06e66c05658249605550240004926e28db49202202036101f84034d81f7de79d00b00328a6c56c070000501b71b1836876191c61c66180570575555c35815555124834514d248345140e38334d3ce38334d30b2412891832071451c61c6145103081000⟩,
  ⟨195,8,[ew38,ew175,ew426,ew470,ew509,ew535,ew537,ew538],localHints 6 0xc41087d0415000c0640a02081a82d09e1740a03d022068fb03202e064138220162ac4480304808c2e00803a24c4b804002b88128020146300b0000260980701e17c040028290380180604038621862853 0x518eb90fae586142d44184370f8dd86102d0414d63db58d4510490366d0c63432698d618053ccd5333534d651405040d8f23504128e32cbc4a64a2d860a514c134f05142934ca410bcf3ef41028f3e734d28c28a34d9cc9c6606ae69ab6181a618651416db855141ad1ab42c1aab06410aeaaa9a681a118134d14a1469c618a1859c56d860b9a62d861b9a65945014d39545014d34a38c14109238c14108a181b3607c17de28a78178128a74171b1866995cb6175945034d35545034d34904033cf4504033cf04d34e30c38d34130c2cb24b2892061871451c6183145001001104043080040⟩,
  ⟨195,9,[ew175,ew426,ew470,ew509,ew535,ew537,ew538],localHints 6 0x10c1081b092082a18180c8140413a606ae941604d0780a2a10100261280f03701a1740a03d0220681903305203c06040008004fd09e0040290f8a80160000e00e007504118070a6015d20260102f80e806 0x93e3a579596b39e3709359608e5ce476596ab65d708e58ea8e4f4b0fd74a8f4d354e44e08c5961255f312559608c5d71044b210c4f210c4921154d310438e10c3f110c38e1113cf0865afc285efba85960865c65464edb084adb084d35464864683aba869eba8638ea689e71083261069461063061089480805a46df8e435f5960808c03404d36d98623594d36c084035f3a06c07a034038e6df79e1c71dd34034010430c35919c6c069c3401866d96990815d71c45961185d70815961154d31c44921144d31c44921113cf1c438e1103cf1c438e34d34b08130b10a2081c91861092081c4186105103081000⟩,
  ⟨195,7,[ew369,ew426,ew509,ew535,ew537,ew538,ew543],localHints 6 0x818c218210361244a0200980602538303e0e41783f02402c0e01501a0b81b0140e21881101a06407854d4501e016a200103a45cbb82d0040282780002600c048060200200b80c 0x54ecd04d0293c8b54b2d32ca74a2efc70410c2fb8b4101d3b4854821320764721f22c410b1f7c840820baa2aea88b2c8648153a46a061931859c51909a37e68d04067c618a9452e514a2862c68c89068a41882238a20210024c20a10804c00904207df8104027c26cb78271e08b2dd71c6c820261a0882196180865c05970061825825544834d23d04034430d040f38d0cb2cc28a30b2c328a0c82091c72482031c70461831450c61811450421030040c2081000⟩,
  ⟨195,8,[ew369,ew426,ew470,ew509,ew535,ew537,ew538],localHints 6 0x4304206c2482004a1300c03905e0fc0900b74e18c4a04a0b40540682e0281880d053064078200010080d8138020140880b00004804c3f89a15258c0181f01245c0e80f00a248270060100705180c 0x298db86b771ccf7db529871c2946d45b471c5746db294714554631ceccb156c61859459428d73032d6f046d71c28d6cd44d5ef30b62f44b5d730d60d46d52e30db2e44d51432db2c28871c4d36db3eb71c2886db3da6184c85ea3c86184d35d73d65144c84a93c85144d34923cc34d4482e83c834d30c2cb28371c0a69670a671c2839430826240838e408361809a8e308251408386208351409686180335f80079f08034d08378314014014320308308308020028971c4dd6db4dd71c2896db4da6184d35d74d96184d35d74d65144d34924d55144d349230c34d4502cb3ce34d30c2cb1451472892071460c41450040820c3081000⟩,
  ⟨195,7,[ew426,ew427,ew470,ew509,ew535,ew537,ew538],localHints 6 0x860840d8490415200c03905e0fc0900b0c62502501700806413d470143a00b013152268b198b0121380281d22e0540080d05c00aa30140c4000c681a3800c80187102003c490060380205180c 0x4b5df6555db5d125553943b3555cd450e54e392c6ccb1b1248e34e255c2d530b55549509263bdb4af6e38c9489b4eb89b2e24e3adb2c1955479a61d55469861d24868eb1924878e31ce38682a18e387820a092466e91892686db6155579a75d55589a68924a58e39524a48e388e3a182084e38d8207c925e6db74925c6db6876581996071d71860955565145955425022124c241309249141020e38230f08e38d30c0892802ca009242202007002182087080180003102144083080040⟩,
  ⟨195,7,[ew306,ew424,ew470,ew509,ew535,ew537,ew538],localHints 6 0x21821036124100590300e46b03f02402c3006312805c2d00d05c028310290260c82984600a055d40190021340a05d0040a00d080000e180700304603c083a10e203004006 0x3efc704d3c2fb8f4d32e02ed4d3b6080b4cb2cfae6b2b98f3cb38b213aa782a9d34c880821ea583e961e7883c89cba089a820b2e79a61934c55251534c650614f3c67a418f3c579e14b2c66e318b2c56db8882066181882226180534d68215934c180148f7c179f04f3dc79e38b2c16dd04b2dc6db04869961a6482016185855c11970450561860940954d35545024d34914423cf0914033cf38d3422cb08d3032cb2832422080860831451c6182142103002040⟩,
  ⟨195,8,[ew306,ew426,ew470,ew509,ew535,ew537,ew538,ew543],localHints 6 0x448020250860840d84902c082a501804c07c1c82f07e048058052ee0b40504f0260240e3a901a0b8311c006405c0ad490a61f0200015c609c0a00231a0880d0000b8038018a974e08c080ab0e207404006 0x23ae545949789502104084254e5435df6514db5d105148f38cc20c3083233e331f332514c9f7cc50c310c29c70a5040c3cc8af889209248262ba2254b6a7eda945097c9265b2242c8a5949409a8cac9a6b24c32aa69596a055a85945052055969c54109a596641016594530c9238e430c1638da2491628852496a288386104304184120380151465f7d951405f04341e0517814104d144330c04d74130c3cd35c71b0c92410c16451416810450596992036035d71831835d70960965145835425144d14434104914434103cd34330c38d34330c2c32822492031c3145183183145103002040⟩,
  ⟨195,8,[ew38,ew306,ew426,ew470,ew509,ew535,ew537,ew538],localHints 6 0xc41087d04152c0c02f07e0480583505a13c2d02e0c47d81901703209c0a022034170070240462ac0e8062242a4020015c80940100a31a0580001303e098018090f80400281c010054201c410c14c4484e 0x559eb913ae596552d5459477138dd96512d1455d71db5c555514d1367372659ca79cd64d354d0c57431450d54dc91ccdc73351472c712cbc0a68a2d964a555bd452f55529450a451b9042e45129042834d28c30a34da0c30766d1a7b466591e71c156c1e5b075555e59414511e3ac74514e38eaaa904d34704718a287a071ca1c6a067679cb6592e79dd6595e59415559a59415554e38c14519238c145188185d34d80180128a7c17c128a78171d1dc6da60b6585d55445145955445144d14444104914444103cd34e30c38d34430c2cb24b2890471c81862071c11860810811450440c2040⟩,
  ⟨195,9,[ew306,ew426,ew470,ew509,ew535,ew537,ew538],localHints 6 0x860840d8490415340c03905e0fc0900b7560d5d50040580940503c02cb78080130600980f80900e1680682e0c40c821015080064009fb13c05001220150068003a401c00ea602301e14c0281c0f807404006 0xd1e7b53a555abae780d15550cdb0d4375559f7b2c0cd54d9cd475ab0db59f045150d40d0ca574871b348b15550cab0a88aa738604738a0a6984a44a8b137284ac3288a34d871c300c556ebe5b2eb655550c5b0550546ba9fa6ba9f451505a454253689c59289c534d9a592485f2a388582388528a85f81f0c155511875e1185550c174110445c10149c10145111449210434d10139b10134d11038e18619a10428a1011011181451011d91011451181c70c25961845551175960c255511449218445111349218445111038e18434d10f38e18434d10c10b0c228a1091c71841451081c71841451041000c2040⟩,
  ⟨195,7,[ew275,ew426,ew470,ew509,ew535,ew537,ew538],localHints 6 0x218210361241054e0300781786502e0b1d600a0c204c250370680f40881a0640cc020012ac09c010141d80580590e00024ccc0093e00380186b12466c038d801e014f880803a05534806 0x673d7471cd33c9971c4dd4f171cc5d7537134d9bd5c2f5596535d341c72e75db9c710750528b5066d428a296595134d056c4134d755525c72b75dadc709749519a89a2a259669a285134c99a72534d79a624e9474251ce38940901c92132485c7000400196636188d96406008538808220134e18200907c039f01000238e0897801de0090021c70dd74171c05d74371c6d965a6186996546185d55564d35955544d331041238e45034f38d30924b1c72891881c61421030000c2081000⟩,
  ⟨195,6,[ew426,ew441,ew529,ew535,ew537,ew538],localHints 6 0x860840d84904153c0c06075a0b0650e30c27141c8041ae0fc0900b0d00c05b85a002b94ce834004050288000340180381702200c0a84a 0x2e59e63cf9a590b3cf2182233cf8d86083c820b8548a150b2c868814f3c462010f3c56057cb78529e14b2dd28a7082051db14821a1c708f65561954f3c260208a5c02d700a2822c254858251608821551401348215209108014038f3c34500cf3ce38d0cb2cc28a30b2c328a0c82091c72482031c70451831060c51411010420830000c2081000⟩,
  ⟨195,7,[ew426,ew441,ew530,ew535,ew537,ew538,ew541],localHints 6 0x1a0942181b09205aa8018046ebc163ae042228309c50404380f8390081401f812016718180060022dc4799d0680080a0510000680381702200c0a80e 0xe36b3cd3c9a8928e28a38a26024aa297cf3dfa2728f3c69861ce1c738719c1875c76cf3db5d71cf1c72a44e591328a1dc1ce8e314e14538539e8853cf1175c43cf15715e2a115f84528a81f7de1c715b7451c771b6c068008e0823820190023d85176143cf09708225600a58024908a0941d50935421c75134d249108544d3500cd40d3cf0ce0cd34c0ca28b2492ca2832490c71c81862071c31860451431030c51411010420830000c2081000⟩,
  ⟨195,8,[ew426,ew441,ew470,ew509,ew535,ew537,ew538,ew541],localHints 6 0x1a094218210361240b020aa40601302f0ca08c1202c01418409ae621d5442701f0087f0139560503b00594411400c4d0b503a014030010be6741a0020281440001a0120780381703804435815 0x4fdd03d02f62cc04c30130b78b333d74410d33c8c41023120904924124868825f270410c1f7c940924cb99bee64c30968906db470471c11c18201d04067df1904077c77a7b0732c1e79de30c68924766b1c925a65906aa85045141141a691504047df1104057c578ca059e814c31e9e768924596614925a9651571541c75179018e20c18430430608134103df7cf4104df7de2cb74c31d2cb70c31a2496d965b2496996585d64c75955124c548f3d108f44f41008108f3ce08c30d2cb34c3022cb08924a2082892422080071c21820871c0180005142102085140100003002042083080040⟩
]

def nodesBlock34 : Array Node := #[
  ⟨195,7,[ew426,ew470,ew509,ew529,ew535,ew537,ew538],localHints 6 0x860840d8490415500c3ad04f54c7181638e0e42803f02402c6c0092242881a8040c60281e0100267c0039131462d4453af1741680099d0680080a0510000682700603a7f40180e0220140a80f 0x3b5df6451db5d0e4512e02f3451ce080b44b2cec66cb198e38bacb1d1446820191447820c0e3af34dbce3ae34db4b2ec28ab0b2eb28a151aa782a9d144580515ea443a911e7853859cba059a814b2e79a61259058c515314488409185c82171144280208e38079f00e38278270b7426dd08b2dc6db01a6426020930805c05451425420851565541914434d20d14461900ce38f34d3ce38334d0cb2cc28a30b2c328a0472032480c70c11810451431040c51411040420830000c2081000⟩,
  ⟨195,8,[ew426,ew470,ew509,ew530,ew535,ew537,ew538,ew541],localHints 6 0x34128430361240b55603155413bb00420a0e382004c0e42803f02402c4d0090460d4020630140f00801328801c0e8b5114b980300115e6741a0020281440001a0382e80180e0220140a80f 0x18fd903d02f52cc18c30630bb0b333d2b410af3c8c410231209189246248a4825d268410a1d74940924cbe2c2f88c309a4919f7c71871c61c64ee55040f75d3d041575d4cc32daeb4cc32caeb4c926aa284c9269a281271051851461445041509a37668d040574515b94432511b6c53058c99058a41492638a24e180554501f0021820860804c009079975e65040274208c3006dc00c3026c264968261a0892596184d75825424c51424c251348f3d10cf44f4100c60cf3ce0cc30d2cb34c3032cb0c924a2082892432080470431830c70c11810451431040c51411040420830000c2081000⟩,
  ⟨195,7,[ew398,ew470,ew509,ew535,ew537,ew538,ew541],localHints 6 0xd05c050218210361243101a0401640c02603c0bc268b50ca0a02139e0480d4020630780400983002e2e2ac00800d55c0081d2306741a00a0041440000b0060240701100a05407807 0x58fd11511c94ccb5b32d42f29722efc70451c2fb8b451b14b4958925426c8ac25d26b451add74944924ba48aa920b2c988916814650619618551419146775d9d144674690c9862e618c3252cb9092462231892622080548438030d40c17c10d179a75e6914437430cb2c131c04b2c33036896c365b0c925a6595c56031980c50d71865954c45134114444841114503ce10c30d2cb34c3042cb10924a2082892442080861c41471061821450830c40411030c2040⟩,
  ⟨195,7,[ew426,ew470,ew509,ew510,ew535,ew537,ew538],localHints 6 0x860840d8490415680c0272ec3a40b01e05f5643298e016560890031440d4020630140f0080131242e0cd94500e718180b5002034170020281880001a0a60180e918022024070420100140a80f 0x435df64d3db5d104d33613734d3ce184d4cd350c67cb19d040da0d2534c84922134c9492b9f7f0410c1f7ef410b8d36d9e7b4d3689e71934ec861b134c684651fac642b19f7ea41050d3469e918d3689e716690696419a1858c509389d8627534c28420904007e00104027c274d78271e08d35d71c01b0026820990806175855421950850941860d34c74921d34c34831d04433d10d04073cf1cd34330e0cd34730c0c92872ca1c91c32030c61871451c61831430420830040c2081000⟩,
  ⟨195,7,[ew191,ew426,ew470,ew507,ew535,ew537,ew538],localHints 6 0x218210361241003e0301901786503e0d4020d7078040098300d0168170140c40680301e02a129d880d0020940100a0a005805882000560048037402d4038050380200880e 0x46fc704d3c2fb914d32e52ed4d3b6594b4cb2d1acdb2b35144b38b2534d896a6134c9949490a4946925042745138b2c936824b2e734d1139a29668934c494411191642459144440488b8c486310b2e286159f80426011f1162560934c151e0534c250205174271d09144171c04b2c269b08b2c169a0896416190492426025c41025960841175960140154d35545004d34914404100113c640f38d3402cb00d3062cb2862002481c61401040020830410c2080040⟩,
  ⟨195,8,[ew191,ew426,ew470,ew509,ew535,ew537,ew538,ew541],localHints 6 0x1a094218210361240b020ab8060133b305e1941182406a0103183c02004ce303000c6741a0140a20680f01501f56c2706816010000ae704e0080518e05002c001631140240189b00e074028b57640705c011 0x57ed55d583a8120524814a05204b7e78555e37d925557b578d04d34135e41e36a374555d2aa8d54d352c8ecf239248d40d071c4a04a28128113029555daaa75554aa8a111bca4af29145449210d34a3ae28d35038e6ed6c504514115bb1b155ae7aab9d5545a8515249b4696d24854459cda059a814d3679a69659052c510a2975e30178d75550010175e20124a182085248082000d35f79e7cd34079e70a28074000a29c75c7051406db00515c6db0446820590810816181971975555c45865555124844514d248445140e38434d3ce38434d30b2462892041c61450440c2000081081000⟩,
  ⟨195,7,[ew368,ew470,ew509,ew535,ew537,ew538,ew541],localHints 6 0xd0ba050218210361244001a0401640c0466f207c1c85007e0480582302e0101604d1141841403003c21eaf00c00d5740081d2326741a002014144000130060380480502201c0a80f 0x58fd11511c94ccc58c31433273232fc70451c2fb8c451b14b4958925426c66c25e26b451ade78944924ca61aa984c309649194a079c71d41c69861d19627a58914477871cb90632418b2c73078898c78631c926286102000250209608051409145f79e7d14427826cc7422dd08c31c2cb6c924221a0892592080876005d80071c25c25954c35134114434830d14503ce0cc30d2cb34c3032cb0c924a2082892432080471c31860c71c11850421030040c2081000⟩,
  ⟨195,7,[ew426,ew470,ew471,ew509,ew535,ew537,ew538],localHints 6 0x4304206c24820ac00601c85007e0480580d04eb5c74816126660a280902e0101655f014184c781338c0c045158226014438a30020642e8020282000001a08c00c0a80e09c0180e91902201c0780c 0x436e374d3df6d504d33623744d3d2288d4cd350cadcf2b5040d74d293c6e8b1b934ca88a29fc0843021f7ca40ab8dbcab6f28d36eb6d1534c44ac1134c5492a5042b7dfad042a7dfa4d36871ca0d35d71c54a2a720898a2a52240934e38a28d34c28826508427e10904207df64d34271e08d35d71c08a6816da04a2826420585825d60950815010134c34920d34c04800d04003d10104033cf0cd34030e00d34330c24a28020b00a2892080051831c60c50c01000020830410c2080040⟩,
  ⟨195,7,[ew261,ew426,ew468,ew509,ew535,ew537,ew538],localHints 6 0x218210361241004c0300e46b83f02402c30004058184120300d01682e8141000680a84a00c05dda0190020d80506300408809894000df0048032b0228038050380300880f 0x3efc704d3c2fb8f4d32e42ed4d3b6490b4cb2cfae6b2b98f3cb38b213aa792a9d34c8908211a583e96114483c89cba089a820b2e79a61534d69255934c590548f8c546314f3e145138b2c536214b2e134d14881f6207c82056180934c151e0534c250204f3c271d08f3c171c04b2c269b08b2c169a6482026180882196180855c15970451425820140154d35545004d34914403cf0114063cf38d3402cb00d3062cb2862402081c61001440020830410c2080040⟩,
  ⟨195,8,[ew261,ew426,ew470,ew509,ew535,ew537,ew538,ew541],localHints 6 0x341284304206c248160415880c02603e0e42803f02402c11bb60080b0309c6060018ce8340281440d00e02e056b08530d01d4200015d009c0500231e0a0098001360240196303a01c0288a76a07043811 0x56e945947f97d005040141f4df436e37514df6d5051477474c04c30131d3dd327333514ce79cc50c310c6acb1a9040c3cc73070904924125cbdc254bab9eead45099c9251b5c42d711449409accb09aac24c32baaa069a4604618118112819451b9e76d45069c611098646619041345110c30636518c30f34d9248c42491841965a20168965140010165a10104207df8104007df00c31e75d78c30075d68924071c00925a71c6861806c000619a6da0446420580810815d71d61d65145845475144d14444104914444103cd34430c38d34430c2c42872492041471850440c2000081081000⟩,
  ⟨195,8,[ew426,ew468,ew470,ew509,ew535,ew537,ew538],localHints 6 0x218210361241004c0300e41783f02402c3189476c1284500406c09c0502202c04c3402604807c0491300a168008190ba0080a0800000682300302a0380e00f09c2480301d02216c5180c 0x52cf5074555074cf205255504f90f07155507192404f54fc0f4afc2ac2f82a49280f80f04c56e06b92e06b55504c90c8cc86d8d94ad8d98618cc48c82b3ec80caac80c3cf82baaa0485550419240415550489249634926c88699484926db8619603cf6c87a89483cf6db79e96730c6c866694830c6db6590445550419240415550449246e34926db8616e24926db8616e03cf6db79e6df3cf6db79e6da30c6dd6596dc30c6da6591d81d70442170405550435160435550405002434922404532404922434512433cf2403902403cf24338e24b30c24028d24030c24b28a1c01c01c32082432430802000401051c3185043103080040⟩,
  ⟨195,8,[ew426,ew470,ew507,ew509,ew535,ew537,ew538],localHints 6 0x4304206c2482007c0602808204e02c8900306a010160250140f00b010026129d98b50d00901181f00e1680080d05c0080a062000068070531260180e8110b82882100800a0700a80f 0x192cb41b35551b3cb119255518f98f1b05551b09a618f54fbcf4aebeabee86a49284f84f18d5551869a618655518d9a67248ed60d4ad70d8e36184927213cf60daac70d3cf618aaa1895551869a61865551899a66248e361849262b8e36184926213cf618aaa6213cf618aaa3293281893681835671a09a71a05551839839034a59178e59174929038c38603e28437e28433cf8607df61735e7037437033436176176176d76036836036436176171845551885161885551845040884930844530844920884510883cf0843900843cf08838e30430430834d0880881c434418424a3082ca1882481c41840810c30840050840c3081000⟩,
  ⟨195,9,[ew426,ew470,ew509,ew535,ew537,ew538,ew541],localHints 6 0xd13c10c1081b0922a0103bb03009ab203905e0fc0900b04758c1a8040586780503c08824008013774ee4183b876e02403806002074ce8340040502880003400c0701100a0700a80f 0x3823b438f38f08acca08b08b08b08b08a78a38bc323b13cf3b1c2f38b3cf087b870880880880880876873888083ad3cf3ad8203883c86c82ebb24b2b6e42cb788688085a85086086086086085a453863e83a58283a53cf3868067867677922e779275d7862c66a52266c69266c62086a59240808c00830830830830808803833e13998213993cf3838037832df79175f7912cb78374369921c6c361c6c32086996185d11955834955031864d149138e39038439038e3cf38408438e38d0842cb08c28a08c2cb08428a0842080891c70892080841c70811860841450841860811450810c30840000840c3081000⟩,
  ⟨195,8,[ew426,ew466,ew470,ew509,ew535,ew537,ew538],localHints 6 0x620843e8200980603201905e0fc0900b0580281e0130600240380106c09c110160d00980f8a308003c1b80401a174010141000000d046006054070910520cc028242267200899b0f60300e806 0xd56370f66f70f66180d50d50d26120f46f50f46180d20d2cd2572ceccf286c5558528520cfc0f0ed6310edc300cf60f8cfaaf8e656f8e6aaa8cf54f86d4ae84fb2e84f49286db2c0c95c90c36180c35d70c960930956b225aab325555209a893214a9209a29309492208a283253e72099a73093cf2259a50c15e40c76240c35d70c161822351420855522251420855522145120849222045120849221d34d21f3cf21e34d21d3cf6dc6da0c12490c26190c55d90c56180c25d71855552c25161825552c55141854922c24531824922c545118e3cf2c23501823cf2ce34d0c224a3052ca1852492022020c21c20c50451851000c2040⟩,
  ⟨195,8,[ew426,ew470,ew505,ew509,ew535,ew537,ew538],localHints 6 0xc41087d0400f80c02f07e02c0081904e2882000e0c00b01280a078058080130600240386804808c1b80401a0b8010140c40000d0c606400c0f9120226603e01d00c108e480800a0a40a80f 0x255636275a76275618255255252612273a74273618252252c92571caecb18ae55589289224eb0e249618249b2c24e60e40e93035e57041e92434e54e4224af34ebaf40e49234dbae248b2d24c62d249b2c24861836551434d55536b51434d55536245134d49236245134d492a6aa6824838e2435c32616272615d724360394356695d92695d5559439038a14a38838238834928a182035d39f40379f40338e35d79d3437033406c034068034334324461924b5d924b6182445c414b55608451614455508b51414b49208445314449208b45124438f40b08f14b38e34434424430424b20b14b2872442071410c30840061440c3081000⟩,
  ⟨195,7,[ew30,ew426,ew441,ew530,ew535,ew537,ew538],localHints 6 0x2a0b1aca0603002c0421841005007e048059fe0600dc1a05102a2dc068017780940101438a0580001a04601c4881703e438018f801c23c08806 0x115698c4a6355544244d54d844a2155534234d46676799d45134f34a5652099485552822894642a390a4514e38c934d2a188a34d3e184508579555e11e1551454200d180341015115e35f15d7c534d79d75c71b14a6c209a05604255505145941065144141004d35830c60d34130c5ca28120104a2972175c51410c30451570c30965025544d14444104914444103cd34430c38d34430c24a28b2082ca2892081c51440c31851440c3082002040⟩
]

def nodesBlock35 : Array Node := #[
  ⟨195,8,[ew30,ew426,ew441,ew470,ew509,ew535,ew537,ew538],localHints 6 0xa808458820ace0603202f0ca1800c82c01418409ae904f5981400b0ea244018b018c074028370681440e02902a26c3580d0027fc128020283b00b0000340980481e04808c0381703e438360d208017c08806 0x518efa13be98614094418438139e18610090414da8df6a14510490371d4c635331c4d60d5afd0d53436fbd651449040da33350412a28258c88c72218609c49594c09bf0254516bef490409b6e250412b6d26626334d8e6b220a20986021038986164d3ad452b4d3a94512410a68a294104a8a279a588d9648e18898420a005904261805451f4d37d45014d305041e3cf7904013cf6cd34130104d35b31b6c924120104925b21b6dd6c170105d05b71b6995c26175945044d35545044d34904043cf4504043cf1cd34e30c38d34430c2c924a2082892442081c41c40c31841440c3082002040⟩,
  ⟨195,8,[ew30,ew426,ew470,ew509,ew530,ew535,ew537,ew538],localHints 6 0x541635a00c0270420a01005007e048058b00120643180a0780400987500e075748370681440e02902a58c5d00d002ef41280202871c0b0000347603604e080098018c601c08c0289101e2bc08806 0x518e333b8cd86140944184313b7c58610090414d6ddb5b5451049089860210b0986220a2114534cf3114516cf3110432c71110412c7126a26e618baaa89609268c075301e8a09509b90bc9b6f25042eb6d12cac9889158166aaa998605a85154503a290d4505a059909c59671504269651248c58851092451052048420a005904261805451f4d37d45014d305041e3cf7904013cf6dd6c110105d05b71b6c92411c704925b1c76c51410c304515b0c36995c261759450e4d355450e4d349040e3cf45040e3cf10e34610c1841842cb20924a1c72892481c71051460c31851440c3082002040⟩,
  ⟨195,8,[ew30,ew191,ew426,ew470,ew509,ew535,ew537,ew538],localHints 6 0xa808458820ad20603202f0ca18c1e0100267f8180370681440a81904e0281400b15e2440185f00e0741481c1342e0068015d40940101431c0580001a04c0240f024046014078b0022018201ca0d81a063053 0x559efa13be99655215459478139e19651211455da4df69155514d13a8d4d675368a0e64e066d0e5743a699755505144e9333914539242992b0a28c1964aa0a2955499b225554a98ac11c4abf1291470befbaeb4a88a04e38822c1da1c86591d556b514ad55475141d146a410a91447410a4e3873471ce3a9369a4a2872491ca2a9249799648a2821965ea285d55419a69d55419a64e49014519649014518e285e3a18017de28a74175c1c77017011c76da6086585d55445145955445144d144441049144441004e38f34d3ce38134d30a28b2492ca2842492081881c60810811450440c2040⟩,
  ⟨195,8,[ew30,ew261,ew426,ew470,ew509,ew535,ew537,ew538],localHints 6 0x150108b10415a80c05007e04805860058184ff03006e0d02881503209c0502802617c048af03a0141481c28821c068015d60940101431e0580001a03e0980180e04601c0b875022018201cb0d81a04884e 0x559eb913ae59655215459477138dd9651211455d71db5c555514d1367372659ca79cd64d365d0c57432594d54dc91ccdc73351472c71299c099f025964a9ca055bca96f29555796505144a8ee2914538e3b6db0134d28128822b1da1c86591d556a514a955475141d1469410a51447410a0d34730c1cd36830ca0a2872471ca2a82687e79c86592279df6595e59415559a59415554e38c14519238c145188185f34d80179f29e74175c1c77017011c76da6086585d55445145955445144d14444104914444103cd34e30c38d34430c04a28b2492ca2812492081881c60810811450440c2040⟩,
  ⟨195,9,[ew30,ew426,ew470,ew509,ew535,ew537,ew538],localHints 6 0x150108b10415b40c06405e0fc0900b0c00641604d0140f014010026f05e003077eef80480706e0d02882902a07006801400278010141202a00001aad80980180ead608c0284001e07408806 0x915760b51360b555509109108d54d0b31340b355508d08d94d471a2ccb196c4514cd3cd089a890ad5700adaaa0895494c99efa1d46fa1d9e74c94493ed36e949b2e94934d3edb2c0855450a4aab0a4555085a854c5469a1c9e9a1c4514c59c53e43669458e694534d3e48e389c2608457607c524979c75c08209b08158108255558145161a41059a45160141058134d61930c59934d60130c5972496012085812496172085971456010c35811456170c308259408255411345110441011245110441010f34d10430c10e34d10430c10b24910a20810a2491042081071451060c31061451040c3082080082040⟩,
  ⟨195,7,[ew426,ew441,ew479,ew530,ew535,ew537,ew538],localHints 6 0x2181b0920f80c060058084308201f00942381608a08c340390080a81f812016f08182d201c0dc0080d0680080a03d0000440d00718e05c0408f0060185b81f 0xeb2d991466b2b39144b6cb9114646db2d12cb3a95eaa5738e2e02c845119ba0645121b2073a72269c838e8a69872cb2249482cb8249044518d040145111040138e8a184138e8a18412cb81f7c12cb81f7c120878618120874618345c61b7184510db0c334368e39a34d0ce0d82d90d76432cb6175d65950c85415130c40c245229048a45109008238e3cd34f38e08d08a2cc0893022cb2892412080860822021c61810450840810c3081080040⟩,
  ⟨195,8,[ew426,ew441,ew470,ew479,ew509,ew535,ew537,ew538],localHints 6 0x860840d8490400f80c06405e1946904708a1801600a0c204de182304c4380202502c02cf80c70060a40e8d81dc884028370020341a0020280f4000110340240f0080be01c1201709c0183581f 0x435df64d3db5d104d33613734d3ce184d4cd350c5ecb179040d7cd2934c98702534ca84a828bca42f2a8a004107cd34a7ae28d34079e1d34ed4920534c7492050420b2c050420b2c04d35faeb04d35faeb04a2a324904a2a42491934c486a1134c6846810a46a29190405a287cd3469a718d3459a619c19728a5dc9449041811860461231164d30218624d35a18603cf0104203cf01041f34d01e79f34d01e79d71b58a6c101a5876585d55865424d431250c4d309208241044f3d141008f08c34e08b38234d30b2c128a0890822820092410480870811860840821821441010c3081080040⟩,
  ⟨195,8,[ew250,ew426,ew470,ew509,ew535,ew537,ew538],localHints 6 0x21821036124100250b20603201e05e19430017058028308130940dc0683407a0440d0320661000200109a09c010140500580582900008c49998012138070030480984b8920d666c038bb0a603c0281f0104680e806 0x9defd7fc820e3cefa09d8200978576f98206b9861097817697776e19df669975d6d76d709382013487523482009385321fbb3113773213bae11f75d21b5d71136722135d711b6590898203f087137082008984935f76f3c9baf34975d3dfbae35b5d73c9b2d3495d73dbb2c34946b2064eb3464511094c908082a626a6a2e6820080a402c075d62871c2e875d6007002e65e76009672c05d76269652c44e42004642c04c01044512cf2633401a32c02403cf18608186162282062286108182061f75d61871c61e75d61871c61b6596185d761a6596185d71164d32154512d44d03524503ce24934c1862ca245207185104103081000⟩,
  ⟨195,7,[ew250,ew426,ew441,ew530,ew535,ew537,ew538],localHints 6 0x8606c2483e030180160210c208087050104f102503701a0d01e81103425c190f80080040102502802c0b00004601c3401716e0380198b03e02047806 0x11aab9124a4aa945248c4cc8924a24d331230c4673a89ce45130d30a4922139884922932964652a494a45142491630c2a28ca30c3628864920d34e14921934d03e01918063cf0d144d30c18e7c630c0ce39e79d18a74049c61b71849201b00045168f3da45100f01831901764030c6175d628a0080002805882031d50070031860534d44925134c14924114503cf4114503cf34e38d30c34e38d30c24a28b2081ca2892081c7141185103081000⟩,
  ⟨195,8,[ew250,ew426,ew441,ew470,ew509,ew535,ew537,ew538],localHints 6 0x860840d8490400f80c06405e1943002c01418409bc521c25c070bb01e0dc0683407a0440d0241a40100080204a050058160000240f02604601c340170d60708d01d03e0202f806 0x531cf2555cb1c145553d63ef555bd658f54f3d4b51bad45450f40f39554d5ac35554e58e4e7ace52b3a79c351440f3ce46a38f3c34512955485a921554a58a4d4a0a9e82945189e740f3ca96628f3d89652a22a038e8229055550d65a35551565934920d45134920d45103cf0d14503cf0d14628a114e3a081f14a28055e69d79a55501d00051471249c51401201a3db0196c03cf69964338e00d0003800cd35828a0080002806082031c30070030c30565975555d65815554d45134924d45134924114503cf4114503cf2ce38c34d1ce38934d30a28b2081ca2892081c71811440c3081000⟩,
  ⟨195,6,[ew423,ew426,ew441,ew530,ew535,ew537,ew538],localHints 5 0x10c248180c00b0308200a02082502e0281880d04202e0200200101a084010000175b84780700604807006 0xf33ac43168e712866d84d692a4651862d81bde6945907ad58b63a944cd124461023dc11398d62d495250741cc42906310400⟩,
  ⟨195,7,[ew423,ew426,ew441,ew470,ew509,ew535,ew537,ew538],localHints 6 0x861240c06405e1943002c01418409bc601c03c170140c4068230420180a4870080080040682100400005d700135bc0384e03a17cf8806 0x273a638a38d2a594b28e90e1e38df2ca88a24e84e16080b7ca78a7451dc38d38d60b60b2892896c768538d3906592d82972965551d051415341245038f38d30b30b289289207087185085103081000⟩,
  ⟨195,7,[ew426,ew441,ew530,ew535,ew537,ew538,ew542],localHints 6 0x102181b0920f80c068058094108950c2058100032ae0a82400b78e2945bbc61f00dc0088f05c0080a03d0000440d04200e05c0a90e0240180f808 0x1342a45044e88e35334d4cd3a238ea29851461a273914587982d32cb4cb61e60b40b75145d4dd2d12cb3a562695838e2de2c74071a41864061d01c74511a01864511d01e03a31e18c738e8a18602cb1dd7c72cb79d75041c0d07104510d30d041b0cd35a38e68d34338e0cb2d961864b2c36185d75831c70150024c209508050009148a4d229144240208e3c034f00e38234228b30224c08b2ca249147202182087085185003002102083080040⟩,
  ⟨195,8,[ew426,ew441,ew470,ew509,ew535,ew537,ew538,ew542],localHints 6 0x204304206c2482007c060178650d00b00506104804de401d0800940b00b12a0485b0100d75c46903700217c170020280f4000110341180481e08401c0b80c21c0180f808 0x552c5349341e40f54f3d53d079042ec2f4d3beeb504d371d70d54d35535c75c35236c4d3b15b0d4cd350a9caea71040d74d2522489c82122094892534c85482134c94897a5a4942926594141074d34972824d34171c1921859c51521464861934c55451534c648679098696619042396574d3468a418d3638a219b19924965b8524a04928124d34957d249278f3c141078f3c141074d34171c74d34171c6db69224965961218601700254209708058009350c5543134c24820904403d10104023c230d3822ce08d34c2cb0092822020890802001061c21420860841440010020c2083080040⟩,
  ⟨195,8,[ew426,ew441,ew530,ew535,ew537,ew538],localHints 6 0x2181b0935c80c06005808430820072f200205007e04805868060ba41bae600223c0682e04a009110144d40f40b0005d80440d04200e08c0b81578a0c9e180600607c07008 0x696c3156a6db5eac2f6966db6909504e86db4689656906d04505ad5e1bad4615965504d068b6db28996c2896db68b94b28a5ab28baab28b596295aaa28a41028ba2928b410293a286836e70a29679a26db6839435c35240815a45c15140835834624230838634434100a286182081f6832df6846dd78e65d70e6db6846445445985c05185c05965445044ce4124443524444103ce34d2882cc2842442842c42882480800c61c40461440c3080040⟩,
  ⟨195,9,[ew426,ew441,ew470,ew509,ew535,ew537,ew538],localHints 6 0x4304206c24820aee0603202f0ca1801600a0c204de4d760800104f2d115002c0181d00aef81bbb700217c0682e04a008d581407a0580019f022068230260120782102300e0900b80caeb5d2b981c00c07d6c008 0x79aebc67b7df6fbeb979a7df795a955387df5b8aaa7957d55956b66e6df65a669a65551578f7df08eab540e7df78fa8f419c3408f6b440fc3009969a41455508f9b340f5550949a678b7df289ab23097df78ba8b3196b128bc3130b69a299c3031455528bbaf30b555294bae30b30b4103cf31032d7a47df0abaaab2b7df7a4aaa6d96180a969a6e96180a869a5945550a79a65a75550949a630c3257a43e54104237a42e37837e18937618137df78374364369c6c061c6c069a6436035135575834975835555134920803d14033834033c30803802882cd3032433032c32882480801001c3183143103080040⟩
]

def nodesBlock36 : Array Node := #[
  ⟨195,8,[ew407,ew426,ew470,ew509,ew535,ew537,ew538],localHints 6 0x4304206c248200b20601c85007e048058350c60281e0100260780b85a01a2e820001008134138020280a00b0000520688905301200c130a201c44c0380504628c0784e28e0740a806 0xd8cb46b371c6b3cb10d871c0d46d45b071c5b06db0d4714bd462ebe9bee5a96185945940ce72d36a6ed36a71c0ce6ce34e9ac34b62c34b9a634e60e36a52b34ea6b34e51436aa690c87281e46e81e471c0c86c81c86181c59a71c56181c89881e45251c88e51c85141e48e31e138e1c88881c838e1e18a10c371c4c17e078171c0c37df79a6184c15d77816184d35d77965144c14927815144d349240138e4102cb78d38e3412cb1012081041457872081c11450c271c4dd6db4dd71c0c26db4da6184d35d74d96184d35d74d65144d34924d55144d349241138e4102cf34d38e34c2cb10a2081041491c72081c61451041000c2040⟩,
  ⟨195,9,[ew426,ew470,ew509,ew530,ew535,ew537,ew538],localHints 6 0x43036125e5018080278108a80400e42803f02402c0483500818c0503c02004c0381d792efc1bbb80022bc0682e0047300a26b07a15c002ec0220680e57802a0c80182601c0201980600a08c0780c 0x697df85b16db5b1df66976db6919d152f6db4af9e76916d14915f4d6ad744aa5d75915116a06db0b39e70826db6a09e70825d70b2c710825d7096c710824510b0bef082451094bef6896ee22b9ee22b6db6899c920996d2075ed2079652095c922b46c209aac20945122baaa0822296898096836e80a39e80a36db6839c30835d70819660815d70839430a34640838a40834510a38a20820a168380308224908308308809f6846dd78f65d70f6db6846445845d85865585865d758454450f45348439348445140f38e08b34b08408408434408b30b20624a2041ca2042492061c60800c50840450840c3080040⟩,
  ⟨195,8,[ew398,ew426,ew470,ew509,ew535,ew537,ew538],localHints 6 0x21821036124100360b20601106403c0bc3283500818c1e0100261a0180177640b80a0620341082000101a1341380a0040a00b00005202c8904e00608c04826144038c589217066c0282403e03c0385323007404006 0xdbefd7bc820e3cefa0db8200d8bd86b9820d79bef0d8818d586f6e16df6d566db6986980d1820433bf44338200d1bd14107324116f241171c41e6db4106184115b141161841a5960c983022cbf036c8200c9bc93496db20672e3466db20970936c62d209aed34961822caebaa83a9a894693493894284510c18205d77df2e78200c17c12de6e65c19662c16db5d79652da6185c18e42c16185d78e310145110438e2d04514013812c82493411a22c12492081860c28205e17df5e18200c27df5de71c5d76db5dd71c5d76db5da6185d75965d96185d759611545311439341245140f38e20824934c1862ca2492071851041000c2040⟩,
  ⟨195,9,[ew191,ew426,ew470,ew509,ew535,ew537,ew538],localHints 6 0x10c1081b092082bd8180c80bc3283500818c1e0100260c1e00377720b81b01407a08abd0110341180f03304803c0604001a0050089e004029118a801600011809006f2c038b003a016bc81c0101a013006 0x213e3a579596979e3721359620ebce4765968b6bef20e58e88e4f494fd7488f4d354e44e20c59605dbf305d59620cbcc0414b204c4f204c4920554d304138e04c3f104c38e0513cf2065b06ecbf036c596206bc63464d36da4ae35a4d36c648636c3ad6c6aed34638e6ecaeb0820aa34634604130c2005a8a605e89e05962005c05404e69439269434d35409004603a38807e388038e8607df04331e0407400403000437436d919c34069c3401866d96992075d70815960585d72075960554d30814920544d30814920513cf08138e0503cf08138e34d34b20730b04a0492071860450c30840000440c3081000⟩,
  ⟨195,8,[ew368,ew426,ew470,ew509,ew535,ew537,ew538],localHints 6 0x21821036124100250b20601c85007e0480586002e010160610d00c00f3b50ba0504001a08c1000080d09a09c0100a050058000290266a44988733000c0f80e01244c0280704628c0784e23207406006 0xd9df96f875dd38df60d975d0d5a955f575d5b5aaa0d5755595672d2dcf25ad6595d55d50ce77136eab14ae75d0cea8e48e63034c67048c61834e64e4ae56f34eb6f48e55536eb6d0c875d1ebaac1eb75d0c8a881c76691c86291c86591db6181c75551c84e81c85551d74d39c83a69c59661c538e1c89480c175d51471c42475d0c171c41b6595018a34016595148a241755550182140155551482040d38e48131f40138e34d30c1012081041454072081c11410c275d51e71c51e75d0c271c51b65951461851a6595146185175555144d35165555144d334d38e49130c40f38e34d30b10a2091041491c72081c61451041000c2040⟩,
  ⟨195,9,[ew261,ew426,ew470,ew509,ew535,ew537,ew538],localHints 6 0x860840d8490415f40c0390a00fc0900b0c001016061060f041bbba01a0b81281407a059760110340c81301f01c0202101708006400a0213c0280122415004c003cb01200c3a81d00e016be01c0181a011806 0x251e7b53a55597ae7825155524db8d4375558b7bae24d54d88d475970db58b045150d40d24a574731bb477155524ab8a74a4b371b47375b49270a44a77137270ac3274a34d731c30247555058baf058555247b8704146d0474ad04745105449204134d0473ac04734d05038e0820ab04128a047047240569aa09e9a205552409c050046695a92695a4515009004203638807e388034d8607df71a29e7406de74028a71a6da0431d90406000401c004360324859608155505759624855505449208145105349208145105038e08134d04f38e08134d04c04b24828a0410462481c60450c30840000440c3081000⟩,
  ⟨195,8,[ew424,ew426,ew470,ew509,ew535,ew537,ew538],localHints 6 0x10c1081b0920802c8180720bc1f8120161800c8631281280b85d0282000d3a908c038388230080040684d04e0080502802c0000985304c00c1481f01244c0281014603c4904e0b607406006 0xd6d360f569a0f5d330d669a0d26520f269a0f26590d2692c525b0c6bc7052b5965125120ce6af0ec66f0ec69a0ce64e60e56e60b5ae60b55560e58e52c4ad50eaed50e49252caeb0c669a0c8a6a0c869a0c6a4670859670656870659670855570849270646770649270845172538e7062e670638e7252cb0c169a0c36590c369a0c16597585963418e474159634d8e375449234186274149234d86176038e34179f74138e34d79e10120110418675c2080c11810c269a0c765b0c769a0c265935859634d55535759634d55535449234d45135349234d45134c38e3502cb34f38e34c2cb10a2090c21890c22080c71861051000c2040⟩,
  ⟨195,8,[ew426,ew470,ew508,ew509,ew535,ew537,ew538],localHints 6 0x4304206c2482007c0601786504e02ca20030c00101600a0c204c3409a00a0740805f06e0044d80d05c0081281407a0000b011034119d18b601214c1481c03e0202100700c08c0b80c 0x656cb467369a673cb165669a65299267069a6709a6652692bd25aebeabee46a59645245264b69a6599a665969a64b98b31592d1cb5ad30b9241c75963114921cbaac30b4921c7aaa65e69a6599a665969a65e9a61d55141c75961eb5141c75961d14921c7aaa1d14921c7aaa86986865e2e864469a65d9a765d69a64498409d5a508492508459609d92409d4920848a308449209d8a284484485d2cb09d09d7042c464479f85d81f65d79d70464464369b65061b65069a6436035435975465175465965435034504934433d34434924503cf1c62ce3033433032c31c61c61c62861c32431c32031c61c6080105083043083103080040⟩,
  ⟨195,9,[ew426,ew470,ew509,ew535,ew537,ew538,ew543],localHints 6 0x413c10c1081b0922a0103cc03009abf83905e0fc0900b00a5dc1680a09e04c0481cafc0dc0081d01a0b8011a00280f42b8001200440d3aa74a0c9cd80372e0380401000c08c0b80c 0x6026346196190a0ce00950950950950a0520615c32631659631c2f61565909eb9e09009009009009e3de6105d062d65962d5d761065045056bb24b2b4645555103d009da9d08808808808809da5d6086686255e86256596085c850882751d56751d8205085483e54264489264484103e59246186236046236186596040846186220845550a18200a155508482008441009f79e09f41008479e08120808475d08420808175d0807000830830837030806c060365a60e5da60e6596035c35035565054d65055555034c33ce4124433524434103ce34d30520a2c318a2432081c5185080100083043083103080040⟩,
  ⟨195,8,[ew422,ew426,ew470,ew509,ew535,ew537,ew538],localHints 6 0x310421f4100590301900c82f06c0fc110120160d43189409480c0b82e0280f40d03201c020198240020100684d04e0280102802c04c0005304c0241481f006224cd81001e014518400182480e806 0x956b80b71380b769a0950950916910b51360b569a091091b51573bebd33b6b55551151108bc4b0ac6b20acc7108b68b60b5b0bce570bce59660b54b52c46eb4baeeb4b45152caeb08766a0886aa08865908769a9885557075a99875557085969884517074a89874517084929a52cb7073a79872cb72538e08068008265908269a08064028056435e8e429e5553408c029446234086228045134d86129e2e03407e02802cb35e7de29c21d0801dd28020071c1c708169b08265b08269a08165935859634d55535759634d55535449234d45135349234d45134c38e3502cb34f38e34c2cb0812080821c72892060811c6105103081000⟩,
  ⟨195,8,[ew426,ew470,ew504,ew509,ew535,ew537,ew538],localHints 6 0xc41087d0400f80c05007e02c0081904e26c2000906a0b0050610260c0a20102c60740285a0081d40682e0040940a03d0000580881a0643140180e01014c1481c03e108e680700c0900b80c 0x6976f66b5a766b56db6976976936d36b3a746b36db693693c935f1caecb14ae5d749349368db0d69a6db69ab2c68d6cd38d9701cc5f038c9651cd5cd3924ef1cdbaf38d4d31c7bae69eb2d6a16ed69ab2c69e6db1d69651c75d71eb9651c75d71d28e31c74d31d28e31c74d3a6aa6869e34d6846676a06e76a06596846c41605e60849661445d70a09651604d30848e41444d30a08e36843623a00a216034d1c41c46848446a07a01607dd68479d6836c369165c6916db6836435835d858b55858b5d75835434914d44834144834d34914101cb34f38330f38334d1cb30b1c32831c02401c02001c31c3080106143043143103080040⟩,
  ⟨195,9,[ew38,ew426,ew470,ew509,ew535,ew537,ew538],localHints 6 0xc41087d0416080c06405e0fc0900b06a0b42785a0320b81b01407a0880881a756e981939c7300380402402e08c020014082780100a1202a000013b020980180903a04002d800380182000c 0x1d15761f50761f55551d11d11cd54d1f30741f35551cd1cd88d47196ccb18ac4514cd3cd1c99c91ed5701ed9e71c95494c942f94846f9484104c94493ed36e889b2e88934d3edb2c1c71eb1c65861c755558645162a4105aa45160641058634d62930c5a934d60630c5972496062085862496172081c25421e19e81e15551c29c24c24669599269594514c29023e136388282388234d3e18207d925d78269d7022496d96996001805825c25821826005c01c75941c755405345104141005245104141004f34d04130c04e34d04130c04b24904a20804a2490412081c71c51c7185044082043000043082041000⟩,
  ⟨195,8,[ew425,ew426,ew470,ew509,ew535,ew537,ew538],localHints 6 0x10c1081b0920802c8180c8140410350320b01e0100261280f02e0281880d0267101083900f0080040684d04e0280102802c000059120060485100e09c08c0282904801c498530b807404006 0xd5d360f569a0f5d330d569a0d26520f269a0f26590d2692c52570c51c705115555125120cc69a0ce66f0ce69a0cc64c80e5ae80c56e80c59680e55580e49280c46d80c49280e4510c96ac0e8aec0e869a0c9ac960956a6065aa6065556095895284a95099e95094925289e78063268099498093098069460c169a0c36590c369a0c16417585642018e47415552088e375449220186274149220886110138110430c76038e0c130175f24920171e74124920871c0c269a0cd65b0cd69a0c265921859620855521759620855521449220845121349220845111038f0c230f0c238e0cd30c20724920b18620a2492071861051000c2040⟩,
  ⟨195,8,[ew426,ew469,ew470,ew509,ew535,ew537,ew538],localHints 6 0x218210361241004c030190178650580283081300809c0b00b28800c0909b1341a00e80506e0042f81905c0081b01407a000110110341180482603c109bf89500e0302702903801812008 0x656cf567469a674cf265669a6529d267169a6719e7652692c125afc24c2f46459645245264d69a6619ee66169a64d9cd321aad30d5ad30daaa32159632149230d92c30d49232192464769a6599e765969a6479c72155ab047aab207596041aaa211492047a29207492041a2878784779e34d20c86164734765d69a6609e766069a65d9e70555140415960665140415960514920419240654920419247a386265d36265d86166034d79f79c65d1dc64269b65061b65069a6426025425975405175405965425024504934423d34424924503cf30034e3022c23023423002c00461ca2022422021c20460460401400421020420c2040040⟩,
  ⟨195,9,[ew426,ew470,ew509,ew535,ew537,ew538,ew544],localHints 6 0x413c10c1081b0922a0103cd03000cab82a09002c11d8406a0b00503c02004c0381cb060dc0081d0320b8011a10280f4368001200440d01204c078043897020cdbb00600adc80780c 0x60b6346196192d5cd52e12e12e12e12d5515615c32631659631c2f6156592e6ba62d02d02d02d02e63e66105d062d65962d5d761065045056bb26b2b4665555103d061862a60c62a61865960c2cc6186292cc8612e85552e88612cc5552cc4102e79a62e74102cc9a62dd95d2c32c32c39432dd91d60366361f5e361f6596035c350356251d86251d5555038433df4204437a04434103df79e2dd31d2c32832c33032dd29d2c97092c42c42c47042c96c960465a60e5da60e6596045c45045565094d65095555044c43ce4124443524444103ce34d2c93092c42842c43042c92892000c61c40461440c3080040⟩,
  ⟨195,8,[ew421,ew426,ew470,ew509,ew535,ew537,ew538],localHints 6 0x620843e8200b20601c8190a02083002c04a0f0080130948140f05d0280f40d03203e0cc0780c0020100684d04e0080502802c02c000883300480700309c08c038290480145104001024c0e806 0x966b70b61370b669a0960960916910b41350b469a0910914d15b2ad2cf24d259651151108dc3108e6b108ec3008d69a98e56f7cd5af98d5557ce59698e4517cd4ae98d4517ce4920866460a96ad0a96590866866065acac956cac959660654652946a4c6a2a4c6451529a287c93679869469863467c994908068008265908269a08064040059621c8e441c5962008c041446220086240045120886141f3a00803604003807df34d41c19e20075e40018621c75c08169b08265b08269a08165921859620855521759620855521449220845121349220845108138e08234d40f38c08134c20724920b18620a249207186105103081000⟩
]

def nodesBlock37 : Array Node := #[
  ⟨195,8,[ew426,ew465,ew470,ew509,ew535,ew537,ew538],localHints 6 0x620843e8200980601c81905e1943183c0260c00082701402cb181200626c2000703a1680209a01a0b81280206c0501e8160000880881a08c8180481f03c0cc6080501e0302702903802012006 0x71877773687773675d71871871375373487573475d713713513632666cf252661849349370dc31724771724c3070d74d3a49ef30d62f38d9e73246183a44d330d9ae38d4d33249a67086c871c75d71c6db7087482486180479ed2476180489c82524ec048aec2484d3041aeb24c92a70836a24890830c34d71f6e971c76971c6db71f75d0576180419e70686180419e70529a60414d30549a60414d371f92471c34d26592371f36386286071f2087007407116de71175d7006c05c061a64259a6426185c05804914d55004155004d349141030234f3802c03803403022c204620a2401ca2402080461c60401400421020420c2040040⟩,
  ⟨195,9,[ew43,ew426,ew470,ew509,ew535,ew537,ew538],localHints 6 0xc41087d04161c0c0390541203002c0780400985a01a0b81281407a0580881a03e079c5382066dddb980f0180980200140e278050021202a00000b03a04801d8604601403d8503801820008 0x2d05762f50762f55552d02d02cd54d2f30742f35552cd2cd88d43194ccb188c4104cd3cd2cb2f02ca58a2cb55558a4517ef4105af4517ca41058a34d7ee30c5ae34d7ca30c2c69c62ea56d2ea9e72c65464c642c94546c9454104c64463ea36b886a6b88634d3eaa697c52855867865862867c57852c25422e19e82e15552c29c24c24269409269404104c29023e136388282388234d3e18207c02805827825822827c078075719b70261b6821866576172cb5942cb55405345104141005245104141004f34d04130c04e34d04130c2cb2c92cb289048186047145047186041145044082043000043082041000⟩,
  ⟨195,10,[ew426,ew470,ew509,ew535,ew537,ew538],localHints 6 0x21821036124102ed0316641cd9805e0fc0900bb2e0d6cb0040580281e010027656ca030b2764804807b220dec800103a034170022620501e8002900440d58fb1c0cac6803b180380458bb140cec480600b6200780c 0x6d8efd5fc71c5fcefa6d871c6d4b144f971c4f9b2c6d4714e14637e30e375f06185d44d46cc735db1b35d3171c6ccb0c5ccab35e16335e1aaa5cc60c4f15324ccc324cc5144f1c306c372ebe8b2eb6871c6c3b035c362b5e0aab5e06185c3a834e85294c39e94c35144e89e79a03249438648c330c8a08606c471e7d269e75271c6c46845c46195c95995c96185c45844d25154c44554c45144d245140930e3c428e34430c2c92892000c61c40461440c3080040⟩
]

def nodesGet (i : Nat) : Option Node :=
  if i < 304 then
    if i < 144 then
      if i < 64 then
        if i < 32 then
          if i < 16 then
            nodesBlock0[(i-0)]?
          else
            nodesBlock1[(i-16)]?
        else
          if i < 48 then
            nodesBlock2[(i-32)]?
          else
            nodesBlock3[(i-48)]?
      else
        if i < 96 then
          if i < 80 then
            nodesBlock4[(i-64)]?
          else
            nodesBlock5[(i-80)]?
        else
          if i < 112 then
            nodesBlock6[(i-96)]?
          else
            if i < 128 then
              nodesBlock7[(i-112)]?
            else
              nodesBlock8[(i-128)]?
    else
      if i < 224 then
        if i < 176 then
          if i < 160 then
            nodesBlock9[(i-144)]?
          else
            nodesBlock10[(i-160)]?
        else
          if i < 192 then
            nodesBlock11[(i-176)]?
          else
            if i < 208 then
              nodesBlock12[(i-192)]?
            else
              nodesBlock13[(i-208)]?
      else
        if i < 256 then
          if i < 240 then
            nodesBlock14[(i-224)]?
          else
            nodesBlock15[(i-240)]?
        else
          if i < 272 then
            nodesBlock16[(i-256)]?
          else
            if i < 288 then
              nodesBlock17[(i-272)]?
            else
              nodesBlock18[(i-288)]?
  else
    if i < 448 then
      if i < 368 then
        if i < 336 then
          if i < 320 then
            nodesBlock19[(i-304)]?
          else
            nodesBlock20[(i-320)]?
        else
          if i < 352 then
            nodesBlock21[(i-336)]?
          else
            nodesBlock22[(i-352)]?
      else
        if i < 400 then
          if i < 384 then
            nodesBlock23[(i-368)]?
          else
            nodesBlock24[(i-384)]?
        else
          if i < 416 then
            nodesBlock25[(i-400)]?
          else
            if i < 432 then
              nodesBlock26[(i-416)]?
            else
              nodesBlock27[(i-432)]?
    else
      if i < 528 then
        if i < 480 then
          if i < 464 then
            nodesBlock28[(i-448)]?
          else
            nodesBlock29[(i-464)]?
        else
          if i < 496 then
            nodesBlock30[(i-480)]?
          else
            if i < 512 then
              nodesBlock31[(i-496)]?
            else
              nodesBlock32[(i-512)]?
      else
        if i < 560 then
          if i < 544 then
            nodesBlock33[(i-528)]?
          else
            nodesBlock34[(i-544)]?
        else
          if i < 576 then
            nodesBlock35[(i-560)]?
          else
            if i < 592 then
              nodesBlock36[(i-576)]?
            else
              nodesBlock37[(i-592)]?

def fastViews : QFast.Table View := ⟨196,viewsGet⟩

def fastNodes : QFast.Table Node := ⟨595,nodesGet⟩

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
theorem blockRoots_48 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 48 16 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_64 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 64 16 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_80 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 80 16 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_96 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 96 16 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_112 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 112 16 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_128 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 128 16 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_144 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 144 16 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_160 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 160 16 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_176 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 176 16 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_192 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 192 4 = true := by decide +kernel

theorem joinRoots_0_0 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 0 32 = true :=
  @QFast.merge_blocks (QFast.checkRootAt fastViews fastNodes) 0 16 16 blockRoots_0 blockRoots_16

theorem joinRoots_0_32 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 32 32 = true :=
  @QFast.merge_blocks (QFast.checkRootAt fastViews fastNodes) 32 16 16 blockRoots_32 blockRoots_48

theorem joinRoots_0_64 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 64 32 = true :=
  @QFast.merge_blocks (QFast.checkRootAt fastViews fastNodes) 64 16 16 blockRoots_64 blockRoots_80

theorem joinRoots_0_96 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 96 32 = true :=
  @QFast.merge_blocks (QFast.checkRootAt fastViews fastNodes) 96 16 16 blockRoots_96 blockRoots_112

theorem joinRoots_0_128 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 128 32 = true :=
  @QFast.merge_blocks (QFast.checkRootAt fastViews fastNodes) 128 16 16 blockRoots_128 blockRoots_144

theorem joinRoots_0_160 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 160 32 = true :=
  @QFast.merge_blocks (QFast.checkRootAt fastViews fastNodes) 160 16 16 blockRoots_160 blockRoots_176

theorem joinRoots_1_0 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 0 64 = true :=
  @QFast.merge_blocks (QFast.checkRootAt fastViews fastNodes) 0 32 32 joinRoots_0_0 joinRoots_0_32

theorem joinRoots_1_64 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 64 64 = true :=
  @QFast.merge_blocks (QFast.checkRootAt fastViews fastNodes) 64 32 32 joinRoots_0_64 joinRoots_0_96

theorem joinRoots_1_128 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 128 64 = true :=
  @QFast.merge_blocks (QFast.checkRootAt fastViews fastNodes) 128 32 32 joinRoots_0_128 joinRoots_0_160

theorem joinRoots_2_0 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 0 128 = true :=
  @QFast.merge_blocks (QFast.checkRootAt fastViews fastNodes) 0 64 64 joinRoots_1_0 joinRoots_1_64

theorem joinRoots_2_128 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 128 68 = true :=
  @QFast.merge_blocks (QFast.checkRootAt fastViews fastNodes) 128 64 4 joinRoots_1_128 blockRoots_192

theorem joinRoots_3_0 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 0 196 = true :=
  @QFast.merge_blocks (QFast.checkRootAt fastViews fastNodes) 0 128 68 joinRoots_2_0 joinRoots_2_128

theorem certifiedRoots : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 0 196 = true := joinRoots_3_0

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
theorem blockNodes_360 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 360 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_372 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 372 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_384 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 384 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_396 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 396 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_408 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 408 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_420 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 420 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_432 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 432 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_444 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 444 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_456 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 456 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_468 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 468 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_480 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 480 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_492 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 492 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_504 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 504 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_516 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 516 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_528 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 528 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_540 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 540 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_552 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 552 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_564 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 564 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_576 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 576 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_588 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 588 7 = true := by decide +kernel

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

theorem joinNodes_0_360 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 360 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 360 12 12 blockNodes_360 blockNodes_372

theorem joinNodes_0_384 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 384 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 384 12 12 blockNodes_384 blockNodes_396

theorem joinNodes_0_408 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 408 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 408 12 12 blockNodes_408 blockNodes_420

theorem joinNodes_0_432 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 432 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 432 12 12 blockNodes_432 blockNodes_444

theorem joinNodes_0_456 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 456 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 456 12 12 blockNodes_456 blockNodes_468

theorem joinNodes_0_480 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 480 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 480 12 12 blockNodes_480 blockNodes_492

theorem joinNodes_0_504 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 504 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 504 12 12 blockNodes_504 blockNodes_516

theorem joinNodes_0_528 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 528 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 528 12 12 blockNodes_528 blockNodes_540

theorem joinNodes_0_552 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 552 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 552 12 12 blockNodes_552 blockNodes_564

theorem joinNodes_0_576 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 576 19 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 576 12 7 blockNodes_576 blockNodes_588

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

theorem joinNodes_1_336 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 336 48 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 336 24 24 joinNodes_0_336 joinNodes_0_360

theorem joinNodes_1_384 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 384 48 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 384 24 24 joinNodes_0_384 joinNodes_0_408

theorem joinNodes_1_432 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 432 48 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 432 24 24 joinNodes_0_432 joinNodes_0_456

theorem joinNodes_1_480 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 480 48 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 480 24 24 joinNodes_0_480 joinNodes_0_504

theorem joinNodes_1_528 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 528 48 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 528 24 24 joinNodes_0_528 joinNodes_0_552

theorem joinNodes_2_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 96 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 48 48 joinNodes_1_0 joinNodes_1_48

theorem joinNodes_2_96 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 96 96 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 96 48 48 joinNodes_1_96 joinNodes_1_144

theorem joinNodes_2_192 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 192 96 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 192 48 48 joinNodes_1_192 joinNodes_1_240

theorem joinNodes_2_288 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 288 96 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 288 48 48 joinNodes_1_288 joinNodes_1_336

theorem joinNodes_2_384 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 384 96 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 384 48 48 joinNodes_1_384 joinNodes_1_432

theorem joinNodes_2_480 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 480 96 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 480 48 48 joinNodes_1_480 joinNodes_1_528

theorem joinNodes_3_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 192 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 96 96 joinNodes_2_0 joinNodes_2_96

theorem joinNodes_3_192 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 192 192 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 192 96 96 joinNodes_2_192 joinNodes_2_288

theorem joinNodes_3_384 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 384 192 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 384 96 96 joinNodes_2_384 joinNodes_2_480

theorem joinNodes_4_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 384 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 192 192 joinNodes_3_0 joinNodes_3_192

theorem joinNodes_4_384 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 384 211 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 384 192 19 joinNodes_3_384 joinNodes_0_576

theorem joinNodes_5_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 595 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 384 211 joinNodes_4_0 joinNodes_4_384

theorem certifiedNodes : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 595 = true := joinNodes_5_0

end SignedProjection

namespace SignedProjection
def bMatches (z : Option View) : Bool :=
  match z with
  | none => false
  | some v => vg v == (0xfe808080e8008000 : Word) && vk v == 10 && (vs v).toFinset == Direct64.cols.toFinset

theorem rootNegative : ¬ CoreSigned.build signedOps (0xfe808080e8008000 : BitVec 64) 10 Direct64.cols.toFinset := by
  have shape : bMatches (QFast.get fastViews 195) = true := by decide +kernel
  cases ev : QFast.get fastViews 195 with
  | none => simp [ev, bMatches] at shape
  | some v =>
    have valid := QFast.certified_view fastViews fastNodes certifiedRoots certifiedNodes ev
    simp only [ev,bMatches,Bool.and_eq_true,beq_iff_eq] at shape
    change ¬ CoreSigned.build signedOps (vg v) (vk v) (vs v).toFinset at valid
    rwa [shape.1.1,shape.1.2,shape.2] at valid
end SignedProjection
end PEqualNP.Outside.L_meta_12052_aux

open PEqualNP.Outside.L_meta_12052_aux in
theorem PEqualNP.Outside.L_meta_12052 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4269834368 * 2 ^ 32 + 3892346880) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4269834368 * 2 ^ 32 + 3892346880) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  LowerSymSix.finish SignedProjection.rootNegative
