import PEqualNP.Defs

-- The witness has 10 binary gates. Any circuit with a NOT and fewer gates
-- would have at most 8 binary gates even with every negation available for free.
-- Finite signed-circuit certificates below exclude that possibility.
-- Signed-wire search and gate projections adapt the project’s Apache 2.0 proofs.
namespace PEqualNP.Outside.L_meta_16701_aux
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
  ⟨[⟨.or,[0,1]⟩, ⟨.and,[2,3]⟩, ⟨.and,[4,5]⟩, ⟨.or,[0,3]⟩, ⟨.and,[7,8]⟩, ⟨.or,[6,10]⟩, ⟨.or,[4,5]⟩, ⟨.and,[9,12]⟩, ⟨.or,[2,13]⟩, ⟨.and,[11,14]⟩],15⟩

theorem size : witness.size = 10 := rfl

theorem monotone : Monotone2 witness := by
  simp [Monotone2,witness]

set_option maxRecDepth 16000 in
theorem correct : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) =
    Nat.testBit (4276809450 * 2 ^ 32 + 4008370400) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel

end LowerSymSix

namespace Direct64
open PEqualNP.CircuitLowerBounds SignedProjection
abbrev W := BitVec 64
abbrev basicOps (a b : W) := signedOps a b
abbrev goal : W := ~~~0xfeeaeeeaeeeae0e0
open CoreSigned (build)
def tableB (x : Fin 6 → Bool) :=
  Nat.testBit (4276809450 * 2 ^ 32 + 4008370400) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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

theorem low (reject : ¬ build basicOps (0xfeeaeeeaeeeae0e0 : W) 8 cols.toFinset)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = tableB x) : 8 < binaryCost gs := by
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
    (reject : ¬ CoreSigned.build SignedProjection.signedOps (0xfeeaeeeaeeeae0e0 : BitVec 64) 8 Direct64.cols.toFinset) :
∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4008370400) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4008370400) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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

def ew0 : Word := 0x15001500

def ew1 : Word := 0x44004400

def ew2 : Word := 0x54005400

def ew3 : Word := 0x150000001500

def ew4 : Word := 0x440000004400

def ew5 : Word := 0x444444444444

def ew6 : Word := 0x505050505050

def ew7 : Word := 0x540000005400

def ew8 : Word := 0x400040004000400

def ew9 : Word := 0x404040404040404

def ew10 : Word := 0x404040444444444

def ew11 : Word := 0x404444404044444

def ew12 : Word := 0x505000005050000

def ew13 : Word := 0x505000055550000

def ew14 : Word := 0x505050500000000

def ew15 : Word := 0x505555500000000

def ew16 : Word := 0x1000100010001000

def ew17 : Word := 0x1000100040004000

def ew18 : Word := 0x1000400010004000

def ew19 : Word := 0x1010000010100000

def ew20 : Word := 0x1010000055550000

def ew21 : Word := 0x1010101000000000

def ew22 : Word := 0x1010101010101010

def ew23 : Word := 0x1010101040404040

def ew24 : Word := 0x1010101050505050

def ew25 : Word := 0x1010404010104040

def ew26 : Word := 0x1010505010105050

def ew27 : Word := 0x1010555500000000

def ew28 : Word := 0x1100000011000000

def ew29 : Word := 0x1100000044000000

def ew30 : Word := 0x1100110000000000

def ew31 : Word := 0x1100110044004400

def ew32 : Word := 0x1100440000000000

def ew33 : Word := 0x1100440011004400

def ew34 : Word := 0x1111000000000000

def ew35 : Word := 0x1111000011110000

def ew36 : Word := 0x1111000044440000

def ew37 : Word := 0x1111000055550000

def ew38 : Word := 0x1111111100000000

def ew39 : Word := 0x1111444400000000

def ew40 : Word := 0x1111555500000000

def ew41 : Word := 0x1400000014000000

def ew42 : Word := 0x1400140000000000

def ew43 : Word := 0x1400140014001400

def ew44 : Word := 0x1414000014140000

def ew45 : Word := 0x1414141400000000

def ew46 : Word := 0x1500000015000000

def ew47 : Word := 0x1500050015000500

def ew48 : Word := 0x1500150000000000

def ew49 : Word := 0x1500150005000500

def ew50 : Word := 0x1500150015001500

def ew51 : Word := 0x1515000005050000

def ew52 : Word := 0x1515000015150000

def ew53 : Word := 0x1515050500000000

def ew54 : Word := 0x1515151500000000

def ew55 : Word := 0x4000040040000400

def ew56 : Word := 0x4000400004000400

def ew57 : Word := 0x4040040440400404

def ew58 : Word := 0x4040404004040404

def ew59 : Word := 0x4040404040404040

def ew60 : Word := 0x4040404044444444

def ew61 : Word := 0x4040404050505050

def ew62 : Word := 0x4040444440404444

def ew63 : Word := 0x4040505040405050

def ew64 : Word := 0x4400000000004400

def ew65 : Word := 0x4400440044004400

def ew66 : Word := 0x4444000000000000

def ew67 : Word := 0x4444000000004444

def ew68 : Word := 0x4444000044440000

def ew69 : Word := 0x4444000055550000

def ew70 : Word := 0x4444444400000000

def ew71 : Word := 0x4444444444444444

def ew72 : Word := 0x4444555500000000

def ew73 : Word := 0x4545000045450000

def ew74 : Word := 0x4545444445454444

def ew75 : Word := 0x4545454500000000

def ew76 : Word := 0x4545454544444444

def ew77 : Word := 0x5000000000005000

def ew78 : Word := 0x5000000005000000

def ew79 : Word := 0x5000000050000000

def ew80 : Word := 0x5000050000000000

def ew81 : Word := 0x5000050050000500

def ew82 : Word := 0x5000500000000000

def ew83 : Word := 0x5000500005000500

def ew84 : Word := 0x5000500050005000

def ew85 : Word := 0x5050000000000000

def ew86 : Word := 0x5050000000005050

def ew87 : Word := 0x5050000005050000

def ew88 : Word := 0x5050000050500000

def ew89 : Word := 0x5050000055550000

def ew90 : Word := 0x5050050500000000

def ew91 : Word := 0x5050404040404040

def ew92 : Word := 0x5050505000000000

def ew93 : Word := 0x5050505050505050

def ew94 : Word := 0x5050555500000000

def ew95 : Word := 0x5151000051510000

def ew96 : Word := 0x5151505051515050

def ew97 : Word := 0x5151515100000000

def ew98 : Word := 0x5151515150505050

def ew99 : Word := 0x5400000054000000

def ew100 : Word := 0x5400440054004400

def ew101 : Word := 0x5400540000000000

def ew102 : Word := 0x5400540044004400

def ew103 : Word := 0x5400540054005400

def ew104 : Word := 0x5454000044440000

def ew105 : Word := 0x5454000054540000

def ew106 : Word := 0x5454444400000000

def ew107 : Word := 0x5454444454544444

def ew108 : Word := 0x5454505054545050

def ew109 : Word := 0x5454545400000000

def ew110 : Word := 0x5454545444444444

def ew111 : Word := 0x5454545450505050

def ew112 : Word := 0x5454545454545454

def ew113 : Word := 0x5500000000000000

def ew114 : Word := 0x5500000000005500

def ew115 : Word := 0x5500000055000000

def ew116 : Word := 0x5500050005000500

def ew117 : Word := 0x5500440044004400

def ew118 : Word := 0x5500500055005000

def ew119 : Word := 0x5500550000000000

def ew120 : Word := 0x5500550050005000

def ew121 : Word := 0x5500550055000000

def ew122 : Word := 0x5500550055005500

def ew123 : Word := 0x5555000000000000

def ew124 : Word := 0x5555000055550000

def ew125 : Word := 0x5555444444444444

def ew126 : Word := 0x5555505050505050

def ew127 : Word := 0x5555555500000000

def ew128 : Word := 0xaaaaaaaaaaaaaaaa

def ew129 : Word := 0xcccccccccccccccc

def ew130 : Word := 0xf0f0f0f0f0f0f0f0

def ew131 : Word := 0xff00ff00ff00ff00

def ew132 : Word := 0xffff0000ffff0000

def ew133 : Word := 0xffffffff00000000

def labelsBlock0 : Array Nat := #[
  0x608,
  0x1a28,
  0x610,
  0x2a28,
  0x1a48,
  0x3c70,
  0x3cb0,
  0x2a88,
  0x600,
  0x1a60,
  0x1a08,
  0x2a08,
  0x3cd0,
  0xe28,
  0x3ce0,
  0xe30
]

def labelsBlock1 : Array Nat := #[
  0x628,
  0x1648,
  0xe08,
  0x1650,
  0x648,
  0x1032,
  0x1608,
  0x2608,
  0x2688,
  0x2690,
  0x2aa0,
  0x630,
  0xe10,
  0x1610,
  0x2610,
  0x1026
]

def labelsBlock2 : Array Nat := #[
  0x1a20,
  0x2a20,
  0x3c60,
  0x103a,
  0x101e,
  0x1a40,
  0x1022,
  0x103e,
  0x3c30,
  0x688,
  0x3c20,
  0x3ca0,
  0x102a,
  0xe20,
  0x1a70,
  0x102e
]

def labelsBlock3 : Array Nat := #[
  0x36d0,
  0x3cc0,
  0x36c8,
  0x500,
  0x3ae0,
  0x3ac8,
  0x1a00,
  0x3c50,
  0x1036,
  0x3a28,
  0x2a00,
  0x410032,
  0x1600,
  0x2600,
  0x1640,
  0x650
]

def labelsBlock4 : Array Nat := #[
  0x690,
  0x2ab0,
  0x1e70,
  0x620,
  0xe00,
  0x2680,
  0x610032,
  0x710032,
  0x1100,
  0x1e28,
  0x2eb0,
  0x510032,
  0x504,
  0xeb0,
  0xe70,
  0x2e28
]

def labelsBlock5 : Array Nat := #[
  0x36c0,
  0x3650,
  0x420032,
  0x720032,
  0x430032,
  0x730032,
  0x421032,
  0x721032,
  0x431032,
  0x731032,
  0x432032,
  0x1104,
  0x1ae0,
  0x2ae0,
  0x3ac0,
  0x3a60
]

def labelsBlock6 : Array Nat := #[
  0x100e,
  0x1012,
  0x1016,
  0x3c90,
  0x3a08,
  0x3c40,
  0x3c00,
  0x1e20,
  0x1c9010032,
  0x1cd010032,
  0x109110032,
  0x10d110032,
  0x1cd020032,
  0x3648,
  0x73003a,
  0x1c9030032
]

def labelsBlock7 : Array Nat := #[
  0x43103a,
  0x1cd321032,
  0x3690,
  0x2a80,
  0x1c9331032,
  0x2100,
  0x510,
  0x2e20,
  0x3a20,
  0x1e30,
  0x2e30,
  0x3aa0,
  0x100a,
  0x1006,
  0x1002,
  0x3c80
]

def labelsBlock8 : Array Nat := #[
  0xf5,
  0x101,
  0x26d0,
  0x13d,
  0x16d0,
  0x195,
  0x2104,
  0x59,
  0x85,
  0x91,
  0x51,
  0x55,
  0x81,
  0x89,
  0x8d,
  0x95
]

def labelsBlock9 : Array Nat := #[
  0x9d,
  0xdd,
  0xe9,
  0xd1,
  0xd5,
  0xd9,
  0xe1,
  0xe5,
  0xed,
  0x3a48,
  0x43103e,
  0x121,
  0x125,
  0x73003e,
  0x145,
  0x15d
]

def labelsBlock10 : Array Nat := #[
  0x161,
  0x17d,
  0x1e50,
  0x3688,
  0x1b1,
  0x2e90,
  0x1e1,
  0x101a,
  0xea0,
  0x1aa0,
  0xe60,
  0x2a60,
  0x1a30,
  0x2a30,
  0x1e60,
  0x2ea0
]

def labelsBlock11 : Array Nat := #[
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
  0x5d,
  0x61,
  0x65,
  0x69
]

def labelsBlock12 : Array Nat := #[
  0x6d,
  0x71,
  0x75,
  0x79,
  0x7d,
  0xa1,
  0xa5,
  0xa9,
  0xad,
  0xb1,
  0xb5,
  0xb9,
  0xbd,
  0xc1,
  0x640,
  0xc9
]

def labelsBlock13 : Array Nat := #[
  0xcd,
  0xf9,
  0x105,
  0xfd,
  0x109,
  0x111,
  0x115,
  0x119,
  0x11d,
  0x131,
  0x135,
  0x12d,
  0x139,
  0x141,
  0x14d,
  0x151
]

def labelsBlock14 : Array Nat := #[
  0x155,
  0x159,
  0x16d,
  0x171,
  0x169,
  0x175,
  0x179,
  0x185,
  0x189,
  0x18d,
  0x191,
  0x199,
  0x1a1,
  0x1a5,
  0x1a9,
  0x1ad
]

def labelsBlock15 : Array Nat := #[
  0x1b9,
  0x1bd,
  0x1c1,
  0x1c5,
  0x1c9,
  0x1d1,
  0x1d5,
  0x1d9,
  0x1dd,
  0x11053003a,
  0x11093003a,
  0x1e9,
  0x1ed,
  0x53003a,
  0x1c923103a,
  0x1fd
]

def labelsBlock16 : Array Nat := #[
  0x63103a,
  0x1f1,
  0x1f5,
  0x1f9,
  0x201,
  0x99,
  0xc5,
  0xf1,
  0x10d,
  0x129,
  0x149,
  0x165,
  0x181,
  0x19d,
  0x1b5,
  0x1cd
]

def labelsBlock17 : Array Nat := #[
  0x1e5,
  0x205,
  0x1,
  0x5,
  0x9,
  0xd,
  0x11,
  0x15,
  0x19,
  0x4d,
  0x3a00,
  0x209,
  0x1042
]

def labelsGet (i : Nat) : Nat :=
  if i < 144 then
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
          if i < 128 then
            labelsBlock7.getD (i-112) 3
          else
            labelsBlock8.getD (i-128) 3
  else
    if i < 208 then
      if i < 176 then
        if i < 160 then
          labelsBlock9.getD (i-144) 3
        else
          labelsBlock10.getD (i-160) 3
      else
        if i < 192 then
          labelsBlock11.getD (i-176) 3
        else
          labelsBlock12.getD (i-192) 3
    else
      if i < 240 then
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

def decodeHints (enc i : Nat) := labelsGet ((enc >>> (i * 9)) % 512)

def localHints (stride dict enc i : Nat) : Nat :=
  let q := (enc >>> (stride*i)) % (2^stride)
  labelsGet ((dict >>> (9*q)) % 512)

def viewsBlock0 : Array View := #[
  ⟨0x1100110044004400,⟨10,by decide⟩,0x1000000044004000,[ew17,ew29,ew30],3,localHints 2 0x89134020d 0xc484⟩,
  ⟨0x1100440011004400,⟨10,by decide⟩,0x1000440000004000,[ew18,ew28,ew32],3,localHints 2 0x89938060d 0xc844⟩,
  ⟨0x1400140014001400,⟨10,by decide⟩,0x1400040004000000,[ew16,ew41,ew42],3,localHints 2 0x8a0b80601 0xe050⟩,
  ⟨0x5000050050000500,⟨8,by decide⟩,0x5000040040000000,[ew55,ew79,ew80],3,decodeHints 0x8a9089267018845467⟩,
  ⟨0x5000500005000500,⟨8,by decide⟩,0x5000400004000000,[ew56,ew78,ew82],3,decodeHints 0x8b0240220279dc5420⟩,
  ⟨0x5500000000005500,⟨8,by decide⟩,0x5400000000004000,[ew64,ew77,ew113],3,decodeHints 0x8b83c1a2d1c9e0542d⟩,
  ⟨0x5555000000000000,⟨48,by decide⟩,0x5440000000000000,[ew66,ew85,ew113],3,decodeHints 0x8c0c064501a9786250⟩,
  ⟨0x1111111144444444,⟨2,by decide⟩,0x1000000044404040,[ew23,ew31,ew36,ew38],4,localHints 3 0xfc40020041400 0xa18408818408⟩,
  ⟨0x1111444411114444,⟨2,by decide⟩,0x1000444000004040,[ew25,ew33,ew35,ew39],4,localHints 3 0xfa071f80c1600 0xa20618408408⟩,
  ⟨0x1414141414141414,⟨2,by decide⟩,0x1400040004000000,[ew22,ew43,ew44,ew45],4,localHints 3 0x1f05c040182c020a 0xd642406d2240⟩,
  ⟨0x5050050550500505,⟨0,by decide⟩,0x5040040040400000,[ew57,ew81,ew88,ew90],4,decodeHints 0x3004c0e130b0f02c3c01884163a0b0f0cc3c⟩,
  ⟨0x5050505005050505,⟨0,by decide⟩,0x5040404004000000,[ew58,ew83,ew87,ew92],4,decodeHints 0x3082408250088014360b8f42e3d0b8f4cc36⟩,
  ⟨0x5500550055005500,⟨8,by decide⟩,0x5400440044004000,[ew65,ew84,ew115,ew119],5,decodeHints 0x8c83c1a2d008801a2d018841a2d00880542d⟩,
  ⟨0x5555000000005555,⟨0,by decide⟩,0x5440000000004040,[ew67,ew86,ew114,ew123],4,decodeHints 0x3100800081a80800081c808000832468cc08⟩,
  ⟨0x5555000055550000,⟨16,by decide⟩,0x5440000044400000,[ew68,ew88,ew115,ew123],4,localHints 3 0x53814261102094ca3e 0xf606a0d60688⟩,
  ⟨0x5555555500000000,⟨32,by decide⟩,0x5440444000000000,[ew70,ew92,ew119,ew123],4,localHints 3 0x538183218039ccfe45 0xf606a0d60688⟩
]

def viewsBlock1 : Array View := #[
  ⟨0x5555555555555555,⟨0,by decide⟩,0x5440444044404040,[ew71,ew93,ew122,ew124,ew127],7,localHints 4 0x8d810060b1d0040400050d8cc08 0xb540a540654032409540874065403210⟩,
  ⟨0xffffffffffffffff,⟨0,by decide⟩,0xfeeaeeeaeeeae0e0,[ew128,ew129,ew130,ew131,ew132,ew133],8,localHints 4 0x23804011d90c3a3a930b636241981033 0xdaba6010caba6010535360105343601097976010978760105353601053432010⟩
]

def viewsGet (i : Nat) : Option View :=
  if i < 16 then
    viewsBlock0[(i-0)]?
  else
    viewsBlock1[(i-16)]?

def nodesBlock0 : Array Node := #[
  ⟨0,3,[ew17,ew29,ew30],localHints 3 0x54935505c07018020d 0x30ad94e7118391ea2008325a408⟩,
  ⟨1,3,[ew18,ew28,ew32],localHints 3 0x55814060e272a8ba0d 0x799b4eeed184b66c280c4263408⟩,
  ⟨2,3,[ew16,ew41,ew42],localHints 3 0x2ab4062e032b08201 0x1c3b5fe289e1b4fd2d2cc023440⟩,
  ⟨3,3,[ew55,ew79,ew80],localHints 4 0x2a1080c0a6721124561a 0x258168155262367057066353024314322010⟩,
  ⟨4,3,[ew56,ew78,ew82],localHints 4 0x2a3b93c4420048040c4a 0x258168155262367057066353024314322010⟩,
  ⟨5,3,[ew64,ew77,ew113],localHints 4 0x2a3c0e4502d078341c34 0x258168155262367057066353024314322010⟩,
  ⟨6,3,[ew66,ew85,ew113],localHints 4 0x312f0d41850180c81c34 0x258168155262367057066353024314322010⟩,
  ⟨12,4,[ew8,ew65,ew84,ew115,ew119],localHints 4 0x22159e8f22d0700c0a0103034120f 0x4654c656b4346a604940807656543432210⟩,
  ⟨12,4,[ew16,ew65,ew84,ew115,ew119],localHints 4 0x10880342d048140606008381a0f 0x356315611341bb57aa39817656543432100⟩,
  ⟨12,4,[ew4,ew65,ew84,ew115,ew119],localHints 4 0x281597c4006570240605008341c0f 0xc54525422b825a569682726545433212100⟩,
  ⟨12,4,[ew28,ew65,ew84,ew115,ew119],localHints 4 0x108805a1a0280c0c0107034120f 0x467426722432bb60a409928767654323210⟩,
  ⟨12,4,[ew1,ew65,ew84,ew115,ew119],localHints 4 0x28110840a7b578680601030341c0f 0x4c942b922432a6948462726554343212100⟩,
  ⟨12,4,[ew30,ew65,ew84,ew115,ew119],localHints 4 0x108805a090280c0c0107034340f 0x465426322452b60aa409928765454323210⟩,
  ⟨12,4,[ew65,ew79,ew84,ew115,ew119],localHints 4 0x60028181c2101880022d06824840f 0x57b537b335cb7b7a5938870665044320110⟩,
  ⟨12,4,[ew65,ew84,ew115,ew118,ew119],localHints 4 0x5001110141a060718042030d1e41e09 0xa4a4d4a4ccb4a4998765541311312010110⟩,
  ⟨12,4,[ew65,ew82,ew84,ew115,ew119],localHints 4 0x61028181c2101880022d06824940f 0x57a537c35a3b7a5a5938870665044320110⟩
]

def nodesBlock1 : Array Node := #[
  ⟨12,4,[ew65,ew84,ew115,ew119,ew120],localHints 4 0x628068141c6115818f41a100041e09 0xdd26622ca2bba9872620110154133210110⟩,
  ⟨12,4,[ew65,ew84,ew113,ew115,ew119],localHints 4 0x62028181c21018800234078b41a09 0x57cb7a51791159119918873665334432210⟩,
  ⟨12,4,[ew65,ew84,ew115,ew119,ew121],localHints 4 0x60131038440515818be1a078b41a09 0xddcc86b1aa1198117613003354330032210⟩,
  ⟨12,5,[ew65,ew84,ew115,ew119],localHints 5 0xc4bb5d18572b8302dd6cb55a08434033f01566b210004fa0658ac05a0f069f01c09 0xea9caea210e21cedaa0ad0dc3d0610c85cec0e03b8d03b854ab0508a8d43a12129c5d27c610791c46914b6010b4814a4910438065310251106310020⟩,
  ⟨16,5,[ew9,ew71,ew93,ew122,ew124,ew127],localHints 5 0xb0501c442b188783a1c0d8201c03028040c04060001202 0x19073528824e6694507440c533c83201c8001a60018b0280941d07314c520c8310820⟩,
  ⟨16,5,[ew22,ew71,ew93,ew122,ew124,ew127],decodeHints 0x406050082c1603020281401038002e05000002c140000024100008442030488040010d0944a040602000090280c0a03030040c01060101804070000402⟩,
  ⟨16,3,[ew46,ew48,ew71,ew93],localHints 4 0x10091d01800360102c0a0a 0x995825157723056544030210⟩,
  ⟨16,4,[ew46,ew50,ew71,ew93,ew127],decodeHints 0x1702800041e01808100800024160b01a1c0e000800012020d808020302804020003000400200808140a⟩,
  ⟨16,4,[ew3,ew50,ew71,ew93,ew127],decodeHints 0x1702800041e018081008000241464018281400318006c36050080205018040200158003402100080e0a⟩,
  ⟨16,4,[ew48,ew50,ew71,ew93,ew124],decodeHints 0x160a000041d00808100800024140a00a1c0800080004a020d808060102804060002800420201808160b⟩,
  ⟨16,4,[ew0,ew50,ew71,ew93,ew124],decodeHints 0x160a000041d0080810080002416640082c16001b800743a0580802050080c060011000120210808080b⟩,
  ⟨16,5,[ew50,ew71,ew93,ew124,ew127],localHints 5 0x2e180b044281e0c8143a13030217e0b01af97a0a00af00e0e080004a040486c1802 0x5d9737be76b2deb358dc7f796b19e634cda5ef53c996603c17b62ef782c002c149d68b5826019a404480630d0323e098c12f791c44ad846b08b5a5492208131828390c608ca40008310400⟩,
  ⟨16,5,[ew52,ew71,ew93,ew122,ew127],localHints 5 0x2c2e1809034201e0c8701e1b060200a0305010d007070500020048040c02 0x533484e90c6292a2b4b86670d695852bcb655ecfa9545030136d26c601a0028117ca2a801e0195c03b80528ce3134416302d689824a96242c4a1250811c4129427308a508c820004310400⟩,
  ⟨16,5,[ew52,ew71,ew93,ew122,ew124,ew127],localHints 5 0xb0b85824100f074381b0401406010201c1c11000242602 0x1495269449cc73987350c7228c7180c0f4800e1000d6016b1894952508398e628c8310020⟩,
  ⟨16,5,[ew54,ew71,ew93,ew122,ew124],localHints 5 0x5058221409034201d098701e1b0602012060082c0e690203800210d00c0a02 0x4af6746ceb5a5092b0b95eb2cc15652bcb63decfa94e502c136526b5818001c117ca27801e0695c0338052b4cd130415ac2c0896b425423a849120e71184129426088a508c820004310400⟩,
  ⟨16,5,[ew54,ew71,ew93,ew122,ew124,ew127],localHints 5 0x282e160a048201e0e87036080480c0c01038101c18000683202 0x1094a0c739ad641c7528c7498c7288c101000f4000e6818c1ad4a4a128398e628c8310020⟩
]

def nodesBlock2 : Array Node := #[
  ⟨16,5,[ew59,ew71,ew88,ew122,ew124,ew127],decodeHints 0x80c0a010582c06040502802071100c0a03158046204060104221018244020008684a2502030120e1702400171480000010a0000012080000011130001008⟩,
  ⟨16,4,[ew59,ew71,ew94,ew122,ew124],decodeHints 0x140a0081c542a11004160b018104020008684a250203042210182400160a0000012080000017148001008⟩,
  ⟨16,5,[ew12,ew59,ew71,ew122,ew124,ew127],decodeHints 0x542a0280c160b01810fe040201c4221018243409048684a250203000171480000161600000120800010084400c44030080408070201c122e048682200⟩,
  ⟨16,5,[ew59,ew71,ew92,ew122,ew124,ew127],decodeHints 0x80c0c010582c06040502802071100c5601030046204060104221018244020008684a2502030120e2082400031480000160a0000012080000018120001008⟩,
  ⟨16,4,[ew59,ew71,ew89,ew122,ew127],decodeHints 0x160b01810542a11004140a0081c4221018244a250203040200086800171480000120800000160a0001008⟩,
  ⟨16,5,[ew14,ew59,ew71,ew122,ew124,ew127],decodeHints 0x542a11004ca6511010140a0081c12220d0244020008684a250203000171780000160a00000120800010080180d1201158040e040381034090d0243000⟩,
  ⟨16,6,[ew59,ew71,ew93,ew122,ew124,ew127],localHints 6 0x2c1407478891c8d15a306221028800c1a128305cc46189c480361304462600b00760445838008a0f8541202 0xb6cb6504196db2d02c84269099a44102092242e52099482cb9099236e21904066db85042065f18b2c665978b2c959d18820659624820141c61b71841005b0582da0596812cb6196092170565c12082565810c10c61830d55034c34104834914103c33832cb34334c2cb2432822080890892081c3142185103002040⟩,
  ⟨16,3,[ew71,ew93,ew99,ew101],localHints 4 0xa061d02c6c0a01020002e 0x469416911481776355432210⟩,
  ⟨16,4,[ew71,ew93,ew99,ew103,ew127],decodeHints 0x160b01a40020302804140a0005c0a00000482000000040c00010780602010703602011e4020204020002e⟩,
  ⟨16,4,[ew7,ew71,ew93,ew103,ew127],localHints 4 0x1902e1e1b0205c050181c140d0003c0202 0x5e753d8335430c70bb50aa3918716543432010⟩,
  ⟨16,4,[ew71,ew93,ew101,ew103,ew124],decodeHints 0x140a00a40060102804160b0005828000004820000000c0a00010740202010703602011e8060204020002e⟩,
  ⟨16,4,[ew2,ew71,ew93,ew103,ew124],localHints 4 0x32058281d1d0205c0500810160d0003c0602 0x5f753ed335430c70bb50aa3978716543432010⟩,
  ⟨16,5,[ew71,ew93,ew103,ew124,ew127],localHints 6 0xc805b1d8c0a6281c2e180b0442812068403c19018143a1300818380f0206c1808010003e2e 0x2ce2ca3cf28e38b3cb1cf7da81f68f3c778768b70775c1cb2da6da08e0983d960e3823c208a0962d758a5422c20850931d44c54821c20cf0d039140f3c33830cb0cc28d30b2c32830c70c81492071831430421030440c2081040⟩,
  ⟨16,5,[ew71,ew93,ew105,ew122,ew127],localHints 5 0x2c146a0385c3012068402c110a0783203028701e040d8303a13008181002000683e2e 0x643dbe7b708338c3bce6840cf79e07e33a7df4ec3f37b1bc7986b2f78e031a877662eab0d83198743d68698ce3240917ca30811e42308d539ac5914421c8832507390c410ca40948318820⟩,
  ⟨16,5,[ew71,ew93,ew105,ew122,ew124,ew127],localHints 5 0x16010201c2e0509040221e01870361301020002e 0x18761e313bdcf7b98761e107b9ee0b5810a5210ad410a5211a0e319083198a31908310820⟩,
  ⟨16,5,[ew71,ew93,ew109,ew122,ew124],localHints 5 0x140b039ac2c110a0481a100b8603a1300818380f0206c181e0c80c0a08010003e09 0xdbfabd756f7ef5b338c57bcae299efd6f865f0db3696b138587e70eb89e2124555daa9a09621145234e45288c21bc707460f78dc31ac6c4b58b50d23198672a0e630ca3008830906210020⟩
]

def nodesBlock3 : Array Node := #[
  ⟨16,5,[ew71,ew93,ew109,ew122,ew124,ew127],localHints 5 0x280606038102c1409040301d008703619010200009 0xf081dcf7ba523be3181e077b9ee0a5210b5810ad410a521190831a0e3198a31908310820⟩,
  ⟨16,6,[ew71,ew93,ew112,ew122,ew124,ew127],localHints 6 0x2c1407138919acc1189996ca25b242e180b044281206841140e0f06406050e84c02060e03c081b0622c1215000083e2e 0xd40d31144c41035134946aa1faa845125f26836925fa4934da1fa014519c19e645194190134d8c18e234d84181f24911f1042497c178340371175c4100d10c330368d6da3190cd0c31c35c96171d60c90c15540c40c24424904d245109008234238c3ce34d08c0822422872ca2480870811850840810c3081081040⟩,
  ⟨16,5,[ew71,ew93,ew95,ew122,ew124,ew127],decodeHints 0x20302804160b01810140a0081c0a030280c0c010601018040005c0a00000042800000482000000441c000107806020108002020107036020104c260204020001a⟩,
  ⟨16,5,[ew71,ew93,ew97,ew122,ew124,ew127],decodeHints 0x20303004160b01810140a0081c0a03030040c010601018040000c5200000582800000482000000601c00010840602010740202010703602010643202040200009⟩,
  ⟨16,5,[ew9,ew22,ew71,ew122,ew124,ew127],decodeHints 0x20302804160b01810140a0081c103d01820103c0082010442182044030280c5601030046204060100408000142e00000502c00000402400048203e00⟩,
  ⟨16,5,[ew9,ew22,ew93,ew122,ew124,ew127],decodeHints 0x20302804160b01810140a0081c103d02820103c6702010442182004030f00804010e808041b0e0081c0810884060910080021a12894080c000203e02⟩,
  ⟨16,5,[ew9,ew71,ew88,ew122,ew124,ew127],decodeHints 0x20302804160b01810140a0081c44030280c5601188101804040f406080404c0208041108608040f82608000142e00000500200000402400088001208⟩,
  ⟨16,4,[ew9,ew71,ew94,ew122,ew124],decodeHints 0x140a0081c542a11004160b01810103c00820104421820103d0182000140b00000100900000220b8001208⟩,
  ⟨16,5,[ew9,ew12,ew71,ew122,ew124,ew127],decodeHints 0x150a80a030582c06043f8100807040f40608040f07e080411086084880c44030080408070201c1c081f02000050b800002b0b0000010090001208000444c00⟩,
  ⟨16,5,[ew9,ew71,ew92,ew122,ew124,ew127],decodeHints 0x20303004160b01810140a0081c4403158040c01188101804040640608040f00208041108608041143208000a40600000502c000004024000c0001208⟩,
  ⟨16,4,[ew9,ew71,ew89,ew122,ew127],decodeHints 0x160b01810542a11004140a0081c103d01820104421820103c0082000220b80000100900000140b0001208⟩,
  ⟨16,5,[ew9,ew14,ew71,ew122,ew124,ew127],decodeHints 0x150a84401329944404050280207040f48008040f002080411086080180d2401158040e04038101c082282000220b80000140b0000010090001208000604800⟩,
  ⟨16,6,[ew9,ew71,ew93,ew122,ew124,ew127],localHints 6 0x2c14074c0892e9615a54621e0c874261c0786d2893043404e03120159e23008980c04230301c000f8242a02 0xb38b25040938e2d02c84269079a44102072242e52079482cb9079233a215040538e85042025f14b2c524978b2c719d1482051861c82004006ce71b41000e0002c06496992cb0090002005c661721600601551300300314549041138e45040f38e34b2cc24930b2ca2491c82011860482071860c31011440c3081000⟩,
  ⟨16,5,[ew19,ew71,ew93,ew122,ew124,ew127],decodeHints 0x20302804160b01810140a0081c00170280000160a000001208000041e01808041d00808041c0d8081008000240a030280c0c01060101804070002602⟩,
  ⟨16,4,[ew27,ew71,ew93,ew122,ew124],decodeHints 0x50280207000582800000482000010740202010703602040200009018040a010582c06040b8000a000f0080602⟩,
  ⟨16,5,[ew71,ew73,ew93,ew122,ew124,ew127],localHints 5 0x500b0b8142410688e00204038443c031f87036080004c1202 0x2a8922944316c62c7390c6a50c7180de8721ad62d8b50d4302500004e0018a02106100820⟩
]

def nodesBlock4 : Array Node := #[
  ⟨16,5,[ew21,ew71,ew93,ew122,ew124,ew127],decodeHints 0x20303004160b01810140a0081c00171480000160a000001208000041e01808041d00808041c0d8081008000240a03030040c01060101804070003202⟩,
  ⟨16,4,[ew20,ew71,ew93,ew122,ew127],decodeHints 0x582c06040005c0a000004820000107806020107036020402000090080c0a010502802070b00028000e8080202⟩,
  ⟨16,5,[ew71,ew75,ew93,ew122,ew124,ew127],decodeHints 0x22802804083702810140a0081c00220280000160a0000012080000603690047001038100e040c0003000010148002010740202010703602040200009010643402⟩,
  ⟨16,6,[ew22,ew71,ew93,ew122,ew124,ew127],localHints 6 0x2c14070b8602c110a0481a101088034254a24c10d41209c0a8101b4c4c2303200020c238101c000f8541202 0x94492cf3cb45124f2463e69079a43cf1871a426518794624990790444488f8e245110f1042c48098602df10910420474679d21c1061013db6516d93cf05105925a04b68124964b6471980486011861c82175950c41010c15114533cf4914503cf38b2cd24930b2ca2491c82021860882071860c31421040c3002040⟩,
  ⟨16,5,[ew71,ew93,ew108,ew122,ew124,ew127],localHints 5 0x500b0087c0e0503050080c00078061d1f87036090d044042e 0x2a9826944b62d6c609826737c9b16c449825e27384d6096b0a9210a0e1098a12042310420⟩,
  ⟨16,5,[ew26,ew71,ew93,ew122,ew124,ew127],localHints 5 0x58280e1608878401c0d8f80a03030041804000240413 0xc849a7341252345e84a210799e42bc2e4042d3042c58541089284a0e6398a42906308820⟩,
  ⟨16,5,[ew40,ew71,ew93,ew122,ew124],localHints 5 0x141608850240d08074261c0786c1808070240c010581cd8040b860001e0c80c0a02 0x533a84f50c6292a2b4bb6736dd15852c4b846711b9505030156daac601a0020138d26890220716007c0052b9ee134416302d0898c4a96242c4a12508118e129426088a508c820004310400⟩,
  ⟨16,5,[ew40,ew71,ew93,ew122,ew124,ew127],localHints 5 0xe5320a368582812081443a1c0d8201203030040e040c0003202 0xd639895292943145318852888507880e0800d3000c5814a12508398e6290a41886208020⟩,
  ⟨16,5,[ew68,ew71,ew88,ew93,ew122,ew127],decodeHints 0x582c06040005c0a000004820001400c0a03318100c0408800041e01808041c0d80810080006804061f80802034d004140a0081c02000a00002060f8044002⟩,
  ⟨16,5,[ew68,ew71,ew93,ew122,ew123,ew127],decodeHints 0x1400c160b01810086303010001714800002b03000001208000041e01808040641008041c0d80810080006802031c004020612004140a0081c2c000a0003a02⟩,
  ⟨16,6,[ew68,ew71,ew93,ew122,ew124,ew127],localHints 6 0xa1380b0b8613612068403c19028fc380f0d830100e0d361ae271200c0c01021480ed66a84400231304c2a02 0x46e634e38d6db94e38b3a424a90938e2ca2c93492ca2cb34b24a2456c588e8e26db14e1453451841863461611455857cb81f59e14b14038071b75c38e01b0000c00cd3430da00b01859960b5c05804c554051500515351348344338e40340f38e10330134c28b2c124904b2ca2492061831451c6183145103081000⟩,
  ⟨16,5,[ew71,ew93,ew96,ew122,ew124,ew127],localHints 5 0x58280e2202818620c020003c030e804381b048f8041a 0xc879a7342e52345e87a1c67198b62e087a1c6719ab62d4a0a50109cc1094810042310420⟩,
  ⟨16,4,[ew47,ew71,ew93,ew124,ew127],decodeHints 0x80c0a010005c0a000005828000107806020107402020402000090582c0604050280207020002000128080802⟩,
  ⟨16,4,[ew53,ew71,ew93,ew122,ew124],decodeHints 0x50280207000582800000482000010740202010703602040200009018040a010582c0604018000a00108080602⟩,
  ⟨16,5,[ew63,ew71,ew93,ew122,ew124,ew127],decodeHints 0x20302804160b01810140a0081c44030280c560107004620406010041e01808041d00808041c0d808120201025b4031780c4c0103005b2040a81000000104c0409⟩,
  ⟨16,5,[ew34,ew71,ew93,ew122,ew124,ew127],decodeHints 0x20337004160b01810140a0081c00171480000160a000001208000041e01808041d00808041c0d8081008000240a03030041804060101c00070006002⟩
]

def nodesBlock5 : Array Node := #[
  ⟨16,5,[ew71,ew72,ew93,ew122,ew124,ew127],decodeHints 0x22802804083702810140a0081c00220280000160a0000012080000603120040c01038100e040c0003000010143202010740202010703602040200009010643202⟩,
  ⟨16,5,[ew12,ew35,ew71,ew93,ew122,ew127],decodeHints 0x582c06040005c0a0000048200001078060201070360204020001a1400c0a03318100c04158000c001f80802034e804140a0081c2800100080202008184c01⟩,
  ⟨16,6,[ew35,ew71,ew93,ew122,ew124,ew127],localHints 6 0x274160a0385c309e0b0442812068403c1911874380f0d82034dd1209c0a8301818020c29811b81f6d83900001304c2a02 0xd44da8f3db45134f34a3e99cba673cf28b2a736828ba0a34d9cb9c444494f9a545110f10490488d8e26e110d1043047ca81f31e10a1003c071175c3cf01101b6da0cd3400c000a01831960a5c03005445801960041151955114533cf4914503cf0c338134d2cc30128a04c30b28a2461881041c61851040c3081000⟩,
  ⟨16,5,[ew71,ew93,ew111,ew122,ew124,ew127],localHints 5 0x281b828061f0381452060c03008000f1003a010e06c0409 0x94711337265223e3174184611e97a5cb73564611695250809cc10948108c410042000420⟩,
  ⟨16,5,[ew24,ew71,ew93,ew122,ew124,ew127],localHints 5 0x160a0385c30210e870360501818020c020000409 0xa74163138e102bdce41da5315a320c2c3842b2842a484010810741cc53148320c4208020⟩,
  ⟨16,5,[ew37,ew71,ew93,ew122,ew127],localHints 5 0x16170c0481a100f064380f0d830100e04814060a021bc0e1608850001d098040c02 0x5b7a95752d6ad4b2b8bb6f36e715a52c8b95eb32c15650341675ecd681c002c149568b9824079620844052be0f138416b42e709a252d824b04b1292911d0129427308a508c820004310400⟩,
  ⟨16,5,[ew37,ew71,ew93,ew122,ew124,ew127],localHints 5 0xe41617090403c1c0d8201205018040807088002602 0x24741e313948529050408431884f7080d380010800c5814a1250741cc6290a41886208020⟩,
  ⟨16,5,[ew70,ew71,ew92,ew93,ew122,ew124],decodeHints 0x50280207000582800000482000140040a011b8100a0411000041d00808041c0d808100800024040520008060138004160b0181006001480006050f80c4202⟩,
  ⟨16,5,[ew70,ew71,ew93,ew122,ew123,ew124],decodeHints 0x14004140a0081c08370281000160a000002202800001208000041d00808040542008041c0d80810080002406011c00406051300c160b018102e00148003c02⟩,
  ⟨16,6,[ew70,ew71,ew93,ew122,ew124,ew127],localHints 6 0x28500dc14224f85822140903420400e84c0c1c0786c1808070240a0370b8046010395008df6f0600027120642a02 0xc44c644a194513273094492ca98b45124a24b32524a94930c2ca2c544518490645116314564584c8a166014c1455457897de55d1491400c00d14430dc00c01a65b68c3006400090175585c95805404855004d40051524d21034014503c338330c34334330c28b2c124904b2ca2492061831451c6183145103081000⟩,
  ⟨16,5,[ew71,ew93,ew98,ew122,ew124,ew127],localHints 5 0x160a0381456061883008000f00c3a010e06c0409 0x86712313261023dc67198461149525c6719a4611695250809cc10948108c410042000420⟩,
  ⟨16,4,[ew49,ew71,ew93,ew124,ew127],decodeHints 0x80c0c010005c52000005828000107806020107402020402000090582c0604050280207020002000128080802⟩,
  ⟨16,4,[ew51,ew71,ew93,ew122,ew127],decodeHints 0x582c06040005c52000004820000107806020107036020402000090080c0c01050280207008002800100080202⟩,
  ⟨16,5,[ew61,ew71,ew93,ew122,ew124,ew127],decodeHints 0x20303004160b01810140a0081c44030700c560103004620406010041e01808041d00808041c0d80812020102448030280dc60116005c4040a8100000010240409⟩,
  ⟨16,5,[ew69,ew71,ew93,ew122,ew124,ew127],localHints 5 0x50060585c521208078381b040244805018040807088002602 0x2a7a1e73394852905288843188507880e380010800d6016b1292741cc6290a41886208020⟩,
  ⟨16,5,[ew14,ew38,ew71,ew93,ew122,ew124],decodeHints 0x50280207000582800000482000010740202010703602040200009140040a011b8100a04110000a0020008060137004160b018105200108080602018144803⟩
]

def nodesBlock6 : Array Node := #[
  ⟨16,6,[ew38,ew71,ew93,ew122,ew124,ew127],localHints 6 0x3702c14075085c30290b0442812068404e1e0e84c380f0d820120501b984c230320c020c2a811ca1f720390200120642a02 0xdacd3d34cfacf35334a4eaa0baa84d328b2a836928ba4a34da0ba049c49539a57641131043c488d8e23e110d1043047ca81f31e10a11d75c0d34c00c000d01a3db68d3403c000a01831960a5c03005445801960041151950c35014d348f3d134d40f3ce34d2cc30128a04c30b28a2461881041c61851040c3081000⟩,
  ⟨16,4,[ew71,ew93,ew100,ew124,ew127],decodeHints 0x80c0a010582c06040502802070005c0a0000058280000048200001078060201074020201070080204020002e⟩,
  ⟨16,4,[ew71,ew93,ew106,ew122,ew124],decodeHints 0x50280207018040a010582c06040005828000004820000005c0a00010740202010703602010780602040200009⟩,
  ⟨16,5,[ew71,ew93,ew107,ew122,ew124,ew127],decodeHints 0x20302804160b01810140a0081c062401ba002060087c08150239c00170280000160a0000012080001c000009806510184c0213008fc08a20204c04020004c002e⟩,
  ⟨16,5,[ew11,ew71,ew93,ew122,ew124,ew127],localHints 5 0x160a0385c2812081443aa2098f8060500818080c070002202 0xe941eb5496943cc5240847888507892e4adad398ac2ac4a10d284a0e6398a42904310400⟩,
  ⟨16,5,[ew71,ew85,ew93,ew122,ew124,ew127],decodeHints 0x20338004160b01810140a0081c00171480000160a0000012080000a03030041804060106400010780602010740202010703602040200009010c06002⟩,
  ⟨16,5,[ew15,ew71,ew93,ew122,ew124,ew127],decodeHints 0x22802804083702810140a0081c006d0280000160a00000120800004510c808041d00808041c0d8081008000240603160040c01038100e040c00030000c8083202⟩,
  ⟨16,6,[ew71,ew88,ew93,ew122,ew124,ew127],localHints 6 0x268160a0385c30140903420eb1789d0a062b0b022150f064060511880029b0e03c081b0625410004602500ea7484c4c02 0x11511a9555351445544d5699dba6755535b36746835ba0d4519db9c85089559a55142152086886914534e420b22236388b84834881451f55579451d55569a7184516cb2d834d60b2db34d69a6582080150165175955405000110024d209144040000d00e2cf38d3002c01882402890082061c6005002102083080040⟩,
  ⟨16,5,[ew71,ew74,ew93,ew122,ew124,ew127],localHints 5 0x160a0385c2c14090400a260717c060103094080c1f0001202 0x1096a2b54969444c52688518084f7092d4b50741ca42904c12d2a4850141cc62904310400⟩,
  ⟨16,5,[ew62,ew71,ew93,ew122,ew124,ew127],localHints 5 0x500b0b85824102f8804a0c0480c0a26030040e04088001c02 0x2aa4aa94510a42145348852388518094f52dce59dad2304112d4952507318a42904310400⟩,
  ⟨16,5,[ew71,ew93,ew94,ew122,ew124],localHints 5 0x2816073885822140903420170c0742601030701e040d8303c19018152208010011009 0xe43ccdf9908737c3bce6840cf31e10df3a7674fc3ed8c13c5986b2fc0a021285665ecaa8982118533d266308e21c0717ca3080de31b06d539ac58d4319c683250738cc3008832906210020⟩,
  ⟨16,5,[ew71,ew93,ew94,ew122,ew124,ew127],localHints 5 0x72990500c0c0702058281208060be1d008703619010200009 0xf589df483e733c25289e2783e0f0a9410b9a10b1610a9411a4831a0e3198a31908310820⟩,
  ⟨16,5,[ew12,ew71,ew93,ew122,ew123,ew127],decodeHints 0x1400c160b0181008630301000171480000a303000001208000041e01808047241008041c0d80810080002402031c004020617804140a0081c2800100080202⟩,
  ⟨16,6,[ew12,ew71,ew93,ew122,ew124,ew127],localHints 6 0xa1480b0b8602c12068403c1902a783a131f8701e1b06258108d77bb84e030300408570388c58110a801da1f760244c02 0xa7ea3d040f7dfa5040d4282cca0b41034c34b3cb34c34d3cd2cc2c67c69909e67df19018926524f3c62461971a33648d78863460100207e18104007c001e01c3dd70a6c03c000d0195da64d6005c00865405950061825024c94894104494494102893873ce30d3472cb1cd34c2cb2892071861420840000c2081000⟩,
  ⟨16,4,[ew71,ew93,ew102,ew124,ew127],decodeHints 0x80c0c010582c06040502802070005c5200000582800000482000010780602010740202010700802040200041⟩,
  ⟨16,4,[ew71,ew93,ew104,ew122,ew127],decodeHints 0x582c06040080c0c010502802070005c520000048200000058280001078060201070360201074020204020001a⟩
]

def nodesBlock7 : Array Node := #[
  ⟨16,5,[ew71,ew93,ew110,ew122,ew124,ew127],decodeHints 0x20303004160b01810140a0081c06050187c022600bc40815023c000171480000160a0000012080001c000009006190190002720086408a5020640402000640041⟩,
  ⟨16,5,[ew10,ew71,ew93,ew122,ew124,ew127],localHints 5 0x160a03858281208078e4a50c914060500818080c070003002 0xe941eb5496943cc494085288850789ce4a0ed3acac2ac4a10d284a0e6398a42904310400⟩,
  ⟨16,5,[ew13,ew71,ew93,ew122,ew124,ew127],localHints 5 0x50060585c521208078381b040245805018040807088002602 0x2a7a1e73394852905288843188507880e380010800d6016b1292741cc6290a41886208020⟩,
  ⟨16,6,[ew71,ew92,ew93,ew122,ew124,ew127],localHints 6 0x3802c14071485822140903420057a0b046852c0bc301513884069f0e84c02060e03c081b0625c10004702502f3790644802 0x11ad1415550ad045544d56aa1baa855535b36846935ba4d451a1ba086886955575e721022546695090844820b22236388b84834869a8185557d041e45175041c4516cb2d834d60b2db34d69a6582080150025d609554050001101241349144040000d00e2cf38d3002c01882402890082061c6005002102083080040⟩,
  ⟨16,5,[ew71,ew76,ew93,ew122,ew124,ew127],localHints 5 0x160a0385c2c14090400c240700c0a7b009cc080c228003402 0xea49eb5516943cc52488518084f70949524ed3b4a42904c12d49524e8384a62904310400⟩,
  ⟨16,5,[ew60,ew71,ew93,ew122,ew124,ew127],decodeHints 0x22802804083702810140a0081c00170280000160a00000120800042210d014027b00868087302030000e0006848050180c02060081808070201c0018000380402⟩,
  ⟨16,5,[ew71,ew89,ew93,ew122,ew127],localHints 5 0x2c2e1809034200a3a01c2c110a0783203028701e040d831240800224121d098040c02 0x643d6bfad0832ec3bcfc8778f79e073a8fa66f4ac9d8713c418402f78a02bb302b604c15ed6152a139c34988e7040117ca30801e00300d539ac5814029d004a007394c5008030906210020⟩,
  ⟨16,5,[ew71,ew89,ew93,ew122,ew124,ew127],localHints 5 0xe41617090400a010201c221e018703608000242602 0x24769e313ad4b5a87068c6948c6f70da769d8c5a96a48d23020e000420018a02106200420⟩,
  ⟨16,5,[ew14,ew71,ew93,ew122,ew123,ew124],decodeHints 0x14004140a0081c08370281000160a000006d02800001208000041d00808045142008041c0d80810080002406011c00406051600c160b018105200108080602⟩,
  ⟨16,6,[ew14,ew71,ew93,ew122,ew124,ew127],localHints 6 0xa14c370505c2c110a0481a105087832400e84c0c1c0786c18980423c120501be1ee23160040e590209c5e180a801ec1f7a8684802 0xe50e74ab9d5143ad38b50b34cb0d5142cc2cd3ab2ccacb38e34c34926a25450624619d1a83a9a1d9c63861991a52e69599062c602302152284a80050000e01e75f78e38074000b01b65c6cb6806405465c06170061955952894c751348944938e40940f38e30d3472cb1cd34c2cb2892071861420840000c2081000⟩,
  ⟨16,4,[ew71,ew91,ew122,ew124,ew127],decodeHints 0x80df2010582c06040502802070005c520000058280000048200010884060910080021a128940830040200009⟩,
  ⟨16,4,[ew71,ew93,ew117,ew124,ew127],decodeHints 0x80df4010582c06040502802070005c5200000582800000482000010780602010740202010700802040200034⟩,
  ⟨16,5,[ew71,ew93,ew122,ew124,ew125,ew127],decodeHints 0x6050189802037e8040c0100890160b018102a04023f0140a0081c0017148003e00003ec00160a000001208000063001a100402008c00282021780830001400034⟩,
  ⟨16,5,[ew5,ew71,ew93,ew122,ew124,ew127],localHints 5 0x2c14070b858281208144e45e181406803028040c041a8006402 0xc839ad6412b53505338852888507890e41ccd3148c22c4a1250741cc53148320c4110400⟩,
  ⟨16,5,[ew71,ew93,ew122,ew124,ew126,ew127],localHints 5 0x16350501c0a00030c418040f00c3a010e06c0409 0x1a6698866908b5923132110821ef239a66998c591645212809cc1004200948108c4100420⟩,
  ⟨16,4,[ew71,ew93,ew116,ew124,ew127],decodeHints 0x80dfc010582c06040502802070005c5200000582800000102000010780602010740202010940802040200009⟩
]

def nodesBlock8 : Array Node := #[
  ⟨16,5,[ew6,ew71,ew93,ew122,ew124,ew127],decodeHints 0x20380004160b01810140a0081cda031900d460119004620406010041e01808041d00808041c0d80812020102458030280c5e0103005fe040a8100000010240409⟩,
  ⟨16,6,[ew71,ew93,ew122,ew123,ew124,ew127],localHints 6 0xa380302c14070a8d4b4a60b86052a40b044282c8240c64850903420270f06406a01187426014e20e050118090380f0206c1808010001c09 0x10c10c155534d3c30c6b555c30beb4101d5baca6eb15547a47b10b47a6d1d042ca6c1eb1eaa6aaaba87a470a80a65679989425420a40a24238938424020a009d7dd75e74270208509a1db6856421c20d50d66175955435030d00d14d24504033c30ce0cb34b2cc2c32830c70c81492071831430021030440c2080040⟩,
  ⟨16,7,[ew71,ew93,ew122,ew124,ew127],localHints 6 0x111058280f100b8621f0e0b044290d09034210c0f09c320385816141d1184c0309030701e040d8541908838220c02004141c09 0x4d159168f6184cf596b1161128c62b2a92ab2a961828c28c2a946a28c2aa28c4512a92a9a035836a66276a65969436039033c34e24634e23e180344328324329e31f29e25d28330370460469959b6996185c45845444444d23d44d24514043c428430428d24e28d30b2842442000c61c40461440c3080040⟩
]

def nodesGet (i : Nat) : Option Node :=
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

def fastViews : QFast.Table View := ⟨18,viewsGet⟩

def fastNodes : QFast.Table Node := ⟨131,nodesGet⟩

end SignedProjection



namespace SignedProjection

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_0 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 0 16 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_16 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 16 2 = true := by decide +kernel

theorem joinRoots_0_0 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 0 18 = true :=
  @QFast.merge_blocks (QFast.checkRootAt fastViews fastNodes) 0 16 2 blockRoots_0 blockRoots_16

theorem certifiedRoots : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 0 18 = true := joinRoots_0_0

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
theorem blockNodes_120 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 120 11 = true := by decide +kernel

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

theorem joinNodes_1_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 48 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 24 24 joinNodes_0_0 joinNodes_0_24

theorem joinNodes_1_48 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 48 48 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 48 24 24 joinNodes_0_48 joinNodes_0_72

theorem joinNodes_1_96 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 96 35 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 96 24 11 joinNodes_0_96 blockNodes_120

theorem joinNodes_2_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 96 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 48 48 joinNodes_1_0 joinNodes_1_48

theorem joinNodes_3_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 131 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 96 35 joinNodes_2_0 joinNodes_1_96

theorem certifiedNodes : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 131 = true := joinNodes_3_0

end SignedProjection

namespace SignedProjection
def bMatches (z : Option View) : Bool :=
  match z with
  | none => false
  | some v => vg v == (0xfeeaeeeaeeeae0e0 : Word) && vk v == 8 && (vs v).toFinset == Direct64.cols.toFinset

theorem rootNegative : ¬ CoreSigned.build signedOps (0xfeeaeeeaeeeae0e0 : BitVec 64) 8 Direct64.cols.toFinset := by
  have shape : bMatches (QFast.get fastViews 17) = true := by decide +kernel
  cases ev : QFast.get fastViews 17 with
  | none => simp [ev, bMatches] at shape
  | some v =>
    have valid := QFast.certified_view fastViews fastNodes certifiedRoots certifiedNodes ev
    simp only [ev,bMatches,Bool.and_eq_true,beq_iff_eq] at shape
    change ¬ CoreSigned.build signedOps (vg v) (vk v) (vs v).toFinset at valid
    rwa [shape.1.1,shape.1.2,shape.2] at valid
end SignedProjection
end PEqualNP.Outside.L_meta_16701_aux

open PEqualNP.Outside.L_meta_16701_aux in
theorem PEqualNP.Outside.L_meta_16701 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4008370400) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4008370400) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  LowerSymSix.finish SignedProjection.rootNegative
