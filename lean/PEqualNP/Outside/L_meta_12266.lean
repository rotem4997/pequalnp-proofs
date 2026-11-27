import PEqualNP.Defs

-- The witness has eleven binary gates. Any circuit with a NOT and fewer gates
-- would have at most nine binary gates even with every negation available for free.
-- Finite signed-circuit certificates below exclude that possibility.
-- Signed-wire search and gate projections adapt the project’s Apache 2.0 proofs.
namespace PEqualNP.Outside.L_meta_12266_aux
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
  ⟨[⟨.and,[0,1]⟩, ⟨.or,[0,1]⟩, ⟨.and,[2,7]⟩, ⟨.or,[6,8]⟩, ⟨.and,[2,6]⟩, ⟨.or,[2,7]⟩, ⟨.and,[4,11]⟩, ⟨.and,[5,9]⟩, ⟨.or,[12,13]⟩, ⟨.and,[3,14]⟩, ⟨.or,[10,15]⟩],16⟩

theorem size : witness.size = 11 := rfl

theorem monotone : Monotone2 witness := by
  simp [Monotone2,witness]

set_option maxRecDepth 16000 in
theorem correct : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) =
    Nat.testBit (4269860992 * 2 ^ 32 + 4269834368) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel

end LowerSymSix

namespace Direct64
open PEqualNP.CircuitLowerBounds SignedProjection
abbrev W := BitVec 64
abbrev basicOps (a b : W) := signedOps a b
abbrev goal : W := ~~~0xfe80e880fe808080
open CoreSigned (build)
def tableB (x : Fin 6 → Bool) :=
  Nat.testBit (4269860992 * 2 ^ 32 + 4269834368) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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

theorem low (reject : ¬ build basicOps (0xfe80e880fe808080 : W) 9 cols.toFinset)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = tableB x) : 9 < binaryCost gs := by
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
    (reject : ¬ CoreSigned.build SignedProjection.signedOps (0xfe80e880fe808080 : BitVec 64) 9 Direct64.cols.toFinset) :
∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4269860992 * 2 ^ 32 + 4269834368) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4269860992 * 2 ^ 32 + 4269834368) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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

def ew3 : Word := 0xa00a000

def ew4 : Word := 0xc00c000

def ew5 : Word := 0xf000000

def ew6 : Word := 0x22008800

def ew7 : Word := 0x3000c000

def ew8 : Word := 0x33000000

def ew9 : Word := 0x44008800

def ew10 : Word := 0x5000a000

def ew11 : Word := 0x55000000

def ew12 : Word := 0x82008200

def ew13 : Word := 0x84008400

def ew14 : Word := 0x88008800

def ew15 : Word := 0x90009000

def ew16 : Word := 0x99000000

def ew17 : Word := 0xa000a000

def ew18 : Word := 0xa5000000

def ew19 : Word := 0xaa00aa00

def ew20 : Word := 0xc000c000

def ew21 : Word := 0xc3000000

def ew22 : Word := 0xcc00cc00

def ew23 : Word := 0xee00ee00

def ew24 : Word := 0xf000f000

def ew25 : Word := 0xfa00fa00

def ew26 : Word := 0xfc00fc00

def ew27 : Word := 0xff000000

def ew28 : Word := 0xa000000aa00

def ew29 : Word := 0xc000000cc00

def ew30 : Word := 0x22000000aa00

def ew31 : Word := 0x2a0000002a00

def ew32 : Word := 0x2a000000aa00

def ew33 : Word := 0x30000000f000

def ew34 : Word := 0x3f0000000000

def ew35 : Word := 0x44000000cc00

def ew36 : Word := 0x4c0000004c00

def ew37 : Word := 0x4c000000cc00

def ew38 : Word := 0x50000000f000

def ew39 : Word := 0x5f0000000000

def ew40 : Word := 0x700000007000

def ew41 : Word := 0x70000000f000

def ew42 : Word := 0x770000000000

def ew43 : Word := 0x7f0000000000

def ew44 : Word := 0x800000008000

def ew45 : Word := 0x880000000000

def ew46 : Word := 0x880000008800

def ew47 : Word := 0xa00000000000

def ew48 : Word := 0xa0000000a000

def ew49 : Word := 0xaa0000000000

def ew50 : Word := 0xaa000000aa00

def ew51 : Word := 0xc00000000000

def ew52 : Word := 0xc0000000c000

def ew53 : Word := 0xcc0000000000

def ew54 : Word := 0xcc000000cc00

def ew55 : Word := 0xee0000000000

def ew56 : Word := 0xf00000000000

def ew57 : Word := 0xf0000000f000

def ew58 : Word := 0xfa0000000000

def ew59 : Word := 0xfc0000000000

def ew60 : Word := 0xfe0000000000

def ew61 : Word := 0xff0000000000

def ew62 : Word := 0xa000a0000000000

def ew63 : Word := 0xa000a000a000a00

def ew64 : Word := 0xc000c0000000000

def ew65 : Word := 0xc000c000c000c00

def ew66 : Word := 0xe000e0000000000

def ew67 : Word := 0xf00000000000000

def ew68 : Word := 0xf0000000f000000

def ew69 : Word := 0xf000a0000000000

def ew70 : Word := 0xf000c0000000000

def ew71 : Word := 0xf000e0000000000

def ew72 : Word := 0xf000f0000000000

def ew73 : Word := 0x2200220000000000

def ew74 : Word := 0x2200220022002200

def ew75 : Word := 0x3000300000000000

def ew76 : Word := 0x3000300030003000

def ew77 : Word := 0x3200320000000000

def ew78 : Word := 0x3300000000000000

def ew79 : Word := 0x3300000033000000

def ew80 : Word := 0x3300220000000000

def ew81 : Word := 0x3300300000000000

def ew82 : Word := 0x3300320000000000

def ew83 : Word := 0x3300330000000000

def ew84 : Word := 0x4400440000000000

def ew85 : Word := 0x4400440044004400

def ew86 : Word := 0x5000500000000000

def ew87 : Word := 0x5000500050005000

def ew88 : Word := 0x5400540000000000

def ew89 : Word := 0x5500000000000000

def ew90 : Word := 0x5500000055000000

def ew91 : Word := 0x5500440000000000

def ew92 : Word := 0x5500500000000000

def ew93 : Word := 0x5500540000000000

def ew94 : Word := 0x5500550000000000

def ew95 : Word := 0x8200820082008200

def ew96 : Word := 0x8400840084008400

def ew97 : Word := 0x8800880088008800

def ew98 : Word := 0x9000900090009000

def ew99 : Word := 0x9900000099000000

def ew100 : Word := 0x9900990000000000

def ew101 : Word := 0xa000a000a000a000

def ew102 : Word := 0xa5000000a5000000

def ew103 : Word := 0xa500a50000000000

def ew104 : Word := 0xaa000000aa000000

def ew105 : Word := 0xaa00aa0000000000

def ew106 : Word := 0xaa00aa00aa00aa00

def ew107 : Word := 0xaaaaaaaaaaaaaaaa

def ew108 : Word := 0xc000c000c000c000

def ew109 : Word := 0xc3000000c3000000

def ew110 : Word := 0xc300c30000000000

def ew111 : Word := 0xcc000000cc000000

def ew112 : Word := 0xcc00cc0000000000

def ew113 : Word := 0xcc00cc00cc00cc00

def ew114 : Word := 0xcccccccccccccccc

def ew115 : Word := 0xee00ee0000000000

def ew116 : Word := 0xee00ee00ee00ee00

def ew117 : Word := 0xf0000000f0000000

def ew118 : Word := 0xf000f00000000000

def ew119 : Word := 0xf000f000f000f000

def ew120 : Word := 0xf0f0f0f0f0f0f0f0

def ew121 : Word := 0xfa00fa0000000000

def ew122 : Word := 0xfa00fa00fa00fa00

def ew123 : Word := 0xfc00fc0000000000

def ew124 : Word := 0xfc00fc00fc00fc00

def ew125 : Word := 0xfe00fe0000000000

def ew126 : Word := 0xff00000000000000

def ew127 : Word := 0xff000000ff000000

def ew128 : Word := 0xff00aa0000000000

def ew129 : Word := 0xff00cc0000000000

def ew130 : Word := 0xff00ee0000000000

def ew131 : Word := 0xff00f00000000000

def ew132 : Word := 0xff00fa0000000000

def ew133 : Word := 0xff00fc0000000000

def ew134 : Word := 0xff00ff0000000000

def ew135 : Word := 0xff00ff00ff00ff00

def ew136 : Word := 0xffff0000ffff0000

def ew137 : Word := 0xffffffff00000000

def labelsBlock0 : Array Nat := #[
  0xf2c,
  0x2b2c,
  0x2ba4,
  0xf34,
  0x1924,
  0xf38,
  0x2ba8,
  0x2da4,
  0x39a4,
  0x2d34,
  0x2db0,
  0x2ea8,
  0x1960,
  0x1a28,
  0x2eb0,
  0x1a60
]

def labelsBlock1 : Array Nat := #[
  0x1c60,
  0x103e,
  0x3aa8,
  0x2e38,
  0xf24,
  0xf28,
  0xf30,
  0x1042,
  0x1026,
  0x1c30,
  0x2b24,
  0x2b28,
  0x2d24,
  0x3cb0,
  0x101a,
  0x1046
]

def labelsBlock2 : Array Nat := #[
  0x103a,
  0x1920,
  0x39e0,
  0x2ba0,
  0x1a20,
  0x3ae0,
  0x2da0,
  0x2ea0,
  0x3ce0,
  0x101e,
  0x102a,
  0x1c20,
  0x2e28,
  0x1022,
  0x102e,
  0x1052
]

def labelsBlock3 : Array Nat := #[
  0x1062,
  0xf20,
  0x2d30,
  0x39a0,
  0x3aa0,
  0x2e30,
  0x3ca0,
  0x51003a,
  0x52003a,
  0x52103a,
  0x1032,
  0x61003a,
  0x71003a,
  0x62003a,
  0x72003a,
  0x62103a
]

def labelsBlock4 : Array Nat := #[
  0x72103a,
  0x41003a,
  0x42003a,
  0x42103a,
  0x105a,
  0x14401003a,
  0x14802003a,
  0x14842103a,
  0x510062,
  0x520062,
  0x521062,
  0x410062,
  0x610062,
  0x710062,
  0x420062,
  0x620062
]

def labelsBlock5 : Array Nat := #[
  0x720062,
  0x421062,
  0x621062,
  0x721062,
  0x1b2c,
  0x19a4,
  0x3924,
  0x1d34,
  0x1e38,
  0x144010062,
  0x148020062,
  0x148421062,
  0x105e,
  0x2b20,
  0x2d20,
  0x2e20
]

def labelsBlock6 : Array Nat := #[
  0x1934,
  0x192c,
  0x700,
  0x1a38,
  0x1a2c,
  0x1c38,
  0x1c34,
  0x1900,
  0x1b60,
  0x1b20,
  0x1d20,
  0x1e20,
  0x100e,
  0x1b24,
  0x1012,
  0x1d24
]

def labelsBlock7 : Array Nat := #[
  0x1016,
  0x1e28,
  0x2bb0,
  0x704,
  0x708,
  0x70c,
  0x710,
  0x714,
  0x718,
  0x1d60,
  0x1e60,
  0x1a00,
  0x1930,
  0x1a30,
  0x1928,
  0x1c28
]

def labelsBlock8 : Array Nat := #[
  0x1a24,
  0x1c24,
  0x81,
  0x89,
  0x6d,
  0x79,
  0xad,
  0xa5,
  0xe5,
  0xdd,
  0x115,
  0x2be0,
  0x2fe0,
  0x11d,
  0x131,
  0x13d
]

def labelsBlock9 : Array Nat := #[
  0x2de0,
  0x149,
  0x161,
  0x2ee0,
  0x185,
  0x195,
  0x1036,
  0x100a,
  0x1006,
  0x1002,
  0x85,
  0x8d,
  0x91,
  0x95,
  0xb1,
  0xb5
]

def labelsBlock10 : Array Nat := #[
  0xb9,
  0xc9,
  0xcd,
  0xe9,
  0xed,
  0xfd,
  0x119,
  0x121,
  0x125,
  0x129,
  0x14d,
  0x151,
  0x159,
  0x16d,
  0x175,
  0x189
]

def labelsBlock11 : Array Nat := #[
  0x18d,
  0x1a5,
  0x1c1,
  0x1d5,
  0x1e9,
  0x1c00,
  0x1904,
  0x1b28,
  0x1d30,
  0x1e30,
  0x35,
  0x39,
  0x3d,
  0x41,
  0x45,
  0x49
]

def labelsBlock12 : Array Nat := #[
  0x4d,
  0x51,
  0x55,
  0x59,
  0x5d,
  0x61,
  0x69,
  0x75,
  0x71,
  0x7d,
  0xa1,
  0x9d,
  0xa9,
  0xc1,
  0xc5,
  0xd9
]

def labelsBlock13 : Array Nat := #[
  0xd5,
  0xe1,
  0xf5,
  0xf9,
  0x105,
  0x109,
  0x99,
  0xbd,
  0xd1,
  0xf1,
  0x101,
  0x10d,
  0x3bb0,
  0x2da8,
  0x39a8,
  0x12d
]

def labelsBlock14 : Array Nat := #[
  0x139,
  0x135,
  0x141,
  0x39b0,
  0x15d,
  0x155,
  0x165,
  0x171,
  0x179,
  0x3ab0,
  0x191,
  0x181,
  0x199,
  0x1a1,
  0x1a9,
  0x1b1
]

def labelsBlock15 : Array Nat := #[
  0x1b5,
  0x145,
  0x169,
  0x17d,
  0x19d,
  0x1ad,
  0x1b9,
  0x104a,
  0x104e,
  0x1056,
  0x1c5,
  0x1c9,
  0x1cd,
  0x1d1,
  0x1d9,
  0x1dd
]

def labelsBlock16 : Array Nat := #[
  0x1e1,
  0x1e5,
  0x1ed,
  0x1f1,
  0x1f5,
  0x1f9,
  0x1,
  0x5,
  0x9,
  0xd,
  0x11,
  0x15,
  0x19,
  0x1d,
  0x21,
  0x25
]

def labelsBlock17 : Array Nat := #[
  0x29,
  0x2d,
  0x31,
  0x65,
  0x111,
  0x1bd,
  0x1fd,
  0x2e00,
  0x2d00,
  0x2d04,
  0x2b00,
  0x2b04,
  0x2b08,
  0x2b0c,
  0x1944,
  0x1066
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
  ⟨0xf00f000,⟨12,by decide⟩,0xe008000,[ew3,ew4,ew5],3,decodeHints 0x830140616301f0fa16⟩,
  ⟨0x3300cc00,⟨10,by decide⟩,0x32008000,[ew6,ew7,ew8],3,decodeHints 0x838140015309f8fe15⟩,
  ⟨0x5500aa00,⟨9,by decide⟩,0x54008000,[ew9,ew10,ew11],3,decodeHints 0x8400c0014322010214⟩,
  ⟨0x99009900,⟨8,by decide⟩,0x98008000,[ew14,ew15,ew16],3,decodeHints 0x8485800312a1a45631⟩,
  ⟨0xa500a500,⟨8,by decide⟩,0xa4008000,[ew13,ew17,ew18],3,decodeHints 0x8500c2a3106890d431⟩,
  ⟨0xc300c300,⟨8,by decide⟩,0xc2008000,[ew12,ew20,ew21],3,decodeHints 0x85814283102084d631⟩,
  ⟨0xaa000000aa00,⟨9,by decide⟩,0xa80000008000,[ew46,ew48,ew49],3,decodeHints 0x8600c0014008683814⟩,
  ⟨0xcc000000cc00,⟨10,by decide⟩,0xc80000008000,[ew46,ew52,ew53],3,decodeHints 0x8681400150086c5815⟩,
  ⟨0xf0000000f000,⟨12,by decide⟩,0xe00000008000,[ew48,ew52,ew56],3,decodeHints 0x870140616048c86a16⟩,
  ⟨0xff0000000000,⟨40,by decide⟩,0xe80000000000,[ew49,ew53,ew56],3,decodeHints 0x878180423038984e23⟩,
  ⟨0xf000f0000000000,⟨40,by decide⟩,0xe00080000000000,[ew62,ew64,ew67],3,decodeHints 0x880180423040cc6823⟩,
  ⟨0x3300330000000000,⟨40,by decide⟩,0x3200200000000000,[ew73,ew75,ew78],3,decodeHints 0x888280e26040cc6c26⟩,
  ⟨0x5500550000000000,⟨40,by decide⟩,0x5400400000000000,[ew84,ew86,ew89],3,decodeHints 0x890381627090d06c27⟩,
  ⟨0xff00ff00,⟨8,by decide⟩,0xfe008000,[ew19,ew22,ew24,ew27],5,decodeHints 0x898140616000542831020844821158844831⟩,
  ⟨0xff000000ff00,⟨8,by decide⟩,0xe80000008000,[ew50,ew54,ew57,ew61],6,decodeHints 0x8a01406160005428310086c345d0e178be31⟩,
  ⟨0xf000f000f000f00,⟨8,by decide⟩,0xe0008000e000000,[ew63,ew65,ew68,ew72],4,decodeHints 0x150301e0c0208448210086c345d020844821⟩
]

def viewsBlock1 : Array View := #[
  ⟨0x3300330033003300,⟨8,by decide⟩,0x3200200032000000,[ew74,ew76,ew79,ew83],4,decodeHints 0x17030200c020845621048c8385e020845621⟩,
  ⟨0x5500550055005500,⟨8,by decide⟩,0x5400400054000000,[ew85,ew87,ew90,ew94],4,decodeHints 0x1d03c200f068905624098d4585f068905624⟩,
  ⟨0x9900990099009900,⟨8,by decide⟩,0x9800880098008000,[ew97,ew98,ew99,ew100],4,decodeHints 0x3605800312a1a456310097400312a1a45631⟩,
  ⟨0xa500a500a500a500,⟨8,by decide⟩,0xa400a000a4008000,[ew96,ew101,ew102,ew103],4,decodeHints 0x3700c2a3106890d4310480cbc3106890d431⟩,
  ⟨0xaa00aa00aa00aa00,⟨9,by decide⟩,0xaa00a800aa008000,[ew97,ew101,ew104,ew105],4,localHints 3 0xf00c00010d0700814 0xfa82488d0248⟩,
  ⟨0xc300c300c300c300,⟨8,by decide⟩,0xc200c000c2008000,[ew95,ew108,ew109,ew110],4,decodeHints 0x38014283102084d63109814be3102084d631⟩,
  ⟨0xcc00cc00cc00cc00,⟨10,by decide⟩,0xcc00c800cc008000,[ew97,ew108,ew111,ew112],4,localHints 3 0x1481400010d8b01a15 0xfa82488d0248⟩,
  ⟨0xf000f000f000f000,⟨12,by decide⟩,0xf000e000f0008000,[ew101,ew108,ew117,ew118],4,localHints 3 0x168140609190d43216 0xfa82488d0248⟩,
  ⟨0xff00ff0000000000,⟨40,by decide⟩,0xfe00e80000000000,[ew105,ew112,ew118,ew126],6,decodeHints 0x8a8180423038984e23040cc68231b0984e23⟩,
  ⟨0xff00ff00ff00ff00,⟨8,by decide⟩,0xfe00e800fe008000,[ew106,ew113,ew119,ew127,ew134],8,decodeHints 0x8b01406160005428310208448211588448310086c345d0e178be31020844821158844831⟩,
  ⟨0xffffffffffffffff,⟨0,by decide⟩,0xfe80e880fe808080,[ew107,ew114,ew120,ew135,ew136,ew137],9,localHints 5 0x23f1e00c76391b8d4663117021e0ee763a9d0e6b65a99cf662 0xaa928398a0a2928398a05a928398a020822188209a928398a09460f735805a928398a02082218820⟩
]

def viewsGet (i : Nat) : Option View :=
  if i < 16 then
    viewsBlock0[(i-0)]?
  else
    viewsBlock1[(i-16)]?

def nodesBlock0 : Array Node := #[
  ⟨0,3,[ew3,ew4,ew5],localHints 4 0x7d3e180c6160280c1e0c 0x258168155262367057066353024314322010⟩,
  ⟨1,3,[ew6,ew7,ew8],localHints 4 0x7f3f184ca1502800200c 0x258168155262367057066353024314322010⟩,
  ⟨2,3,[ew9,ew10,ew11],localHints 4 0x8140190cc1401800200f 0x258168155262367057066353024314322010⟩,
  ⟨3,3,[ew14,ew15,ew16],localHints 4 0x2b3495032310b0002068 0x258168155262367057066353024314322010⟩,
  ⟨4,3,[ew13,ew17,ew18],localHints 4 0x6a12034ae3101854f20f 0x258168155262367057066353024314322010⟩,
  ⟨5,3,[ew12,ew20,ew21],localHints 4 0x6b10810b03102850f40c 0x258168155262367057066353024314322010⟩,
  ⟨6,3,[ew46,ew48,ew49],localHints 4 0x1c0d0041214018000e02 0x258168155262367057066353024314322010⟩,
  ⟨7,3,[ew46,ew52,ew53],localHints 4 0x2c0d8042615028001606 0x258168155262367057066353024314322010⟩,
  ⟨8,3,[ew48,ew52,ew56],localHints 4 0x351902426160280c1c0a 0x258168155262367057066353024314322010⟩,
  ⟨9,3,[ew49,ew53,ew56],localHints 4 0x271301c1623030081c0a 0x258168155262367057066353024314322010⟩,
  ⟨10,3,[ew62,ew64,ew67],localHints 4 0x34198202423030084a22 0x258168155262367057066353024314322010⟩,
  ⟨11,3,[ew73,ew75,ew78],localHints 4 0x36198203a260501c5022 0x258168155262367057066353024314322010⟩,
  ⟨12,3,[ew84,ew86,ew89],localHints 4 0x361a0483a270702c5025 0x258168155262367057066353024314322010⟩,
  ⟨13,4,[ew14,ew19,ew22,ew24,ew27],localHints 4 0x5619120841a0c079b0a804000400605 0xddc4bb943237aa493238876545432321100⟩,
  ⟨13,4,[ew19,ew22,ew23,ew24,ew27],localHints 4 0x5619368501e040685400100600c0a6c 0xddc88c8c5454b878aa54928787665431210⟩,
  ⟨13,4,[ew17,ew19,ew22,ew24,ew27],localHints 4 0x5619120841a1037030ae040000c1e05 0xddc4bb941221aa496872126545433212100⟩
]

def nodesBlock1 : Array Node := #[
  ⟨13,4,[ew19,ew22,ew24,ew25,ew27],localHints 4 0xde1908090280406830000537058060f 0x8787d8c8b5aa78011099508787645432210⟩,
  ⟨13,4,[ew0,ew19,ew22,ew24,ew27],localHints 4 0x2b1206428210683008000800c1e05 0xcca7bb7a994186743462126554343212100⟩,
  ⟨13,4,[ew11,ew19,ew22,ew24,ew27],localHints 4 0x37980da610a0842a160681020000780c1805 0xf6e6d6c6bb43a6099458823765454323210⟩,
  ⟨13,4,[ew19,ew20,ew22,ew24,ew27],localHints 4 0x56191203c20702c0000621020340a0c 0xddc3bb23a98737366554432011001100110⟩,
  ⟨13,4,[ew19,ew22,ew24,ew26,ew27],localHints 4 0xe2190803ce021020340a1500058060c 0x6767d7c7b36767a13198876055044302210⟩,
  ⟨13,4,[ew1,ew19,ew22,ew24,ew27],localHints 4 0x2b1203c42190a83408000800c0a0c 0xcc85ba5434a995877400110654343221010⟩,
  ⟨13,4,[ew8,ew19,ew22,ew24,ew27],localHints 4 0x3898c48145b9901a150b01020000780c1805 0xf9e9d92cc45b9a988417721665454321010⟩,
  ⟨13,4,[ew2,ew19,ew22,ew24,ew27],localHints 4 0x2b08090420d0b06408000183c0a0c 0xcb5aa852332995801107730654432321010⟩,
  ⟨13,4,[ew5,ew19,ew22,ew24,ew27],localHints 4 0x15ae4ca145c19832150b01020000780c1805 0xf94e9d9cc43b9a988417721665432321010⟩,
  ⟨13,5,[ew19,ew22,ew24,ew27],decodeHints 0x62800322b62040082b4c84032194c80008046180c1a246103c08244c03c1a0d4c00c08043803c00143800c20146080c00006003c200f5f81408215f0301a214b83008044b8141a0d3703000153701420155e81400005e030200c360300616360141e165d81406035d0301e0c⟩,
  ⟨14,3,[ew43,ew50,ew54,ew57],decodeHints 0xa05000020a85400060b058060a0e07012000d06802030d86c0205⟩,
  ⟨14,4,[ew44,ew50,ew54,ew57,ew61],decodeHints 0x381c04804341a008244e2705808361b0084c4c26038184623010298c010c00400000180c0a05⟩,
  ⟨14,4,[ew40,ew50,ew54,ew57,ew61],localHints 4 0xd05036130a88c1201038001c02018280c05 0x6896ff89ee64dd8cbb61aa4298987654332100⟩,
  ⟨14,3,[ew41,ew50,ew54,ew61],decodeHints 0xd06802030d86c02050b058060a0e07012000a05000020a8540006⟩,
  ⟨14,4,[ew45,ew50,ew54,ew57,ew61],decodeHints 0x381c048006a350980c28140001c6432048142a150002c2c16018280201638005a000100c0c05⟩,
  ⟨14,4,[ew42,ew50,ew54,ew57,ew61],localHints 4 0xd0503615058581201038001c02018280c05 0x6876ff83ee67dd80cc6baa3298767653432010⟩
]

def nodesBlock2 : Array Node := #[
  ⟨14,3,[ew46,ew48,ew52,ew61],decodeHints 0x2f97c26012f1781201000003c262e97402090180c3c23028145223⟩,
  ⟨14,4,[ew46,ew48,ew54,ew57,ew61],decodeHints 0x160b01201008d402091389c168219004120100000140e14828361b008240c0b168180603028145206⟩,
  ⟨14,3,[ew46,ew49,ew53,ew57],localHints 4 0x17cbc01188000e350f0c85216 0xaa4699268832776504300210⟩,
  ⟨14,4,[ew46,ew49,ew54,ew57,ew61],decodeHints 0x160b026001a8d426830009c0007008044c0003800140e148280a130c0142a150001c2c16028185205⟩,
  ⟨14,4,[ew46,ew50,ew52,ew57,ew61],decodeHints 0xe07012011a80426010000002320084c4c2603a08140e0f028341a0082404071680806030f0080a05⟩,
  ⟨14,4,[ew46,ew50,ew53,ew57,ew61],decodeHints 0xe0701200008044e0005800643204a0c00260002c140e0f02806090c00c28140001c06020f00c2c16⟩,
  ⟨14,5,[ew46,ew50,ew54,ew57,ew61],localHints 5 0x706a9d13a70649b09899340b64860028504b205a004201c1c03148781405 0x85e8cdd196b435036b4abc95adc2d63420a6b9508b18c26b433a85ada4e6242030905088c20110465288427b5ae5adcd6b16b521093192841cc6108822904300820⟩,
  ⟨14,4,[ew36,ew50,ew54,ew57,ew61],localHints 4 0xe05036131305802090581c0002018181405 0xff899893ee36dd9cbb62aa3198987655432100⟩,
  ⟨14,3,[ew37,ew50,ew57,ew61],decodeHints 0xe07012000d86c02050a85400060d06802030a05000020b058060a⟩,
  ⟨14,4,[ew47,ew50,ew54,ew57,ew61],decodeHints 0x582c09800341a0080c281400008361b008142a15000182c160183812010380194031480c1405⟩,
  ⟨14,4,[ew39,ew50,ew54,ew57,ew61],localHints 4 0x702832048542c0e0082c0e000100c0c05 0xeeb42b32dd43ccb0aa41992877645432321010⟩,
  ⟨14,3,[ew48,ew49,ew54,ew56],localHints 4 0xbe5d018b03c310106c5a15 0x996726528827065044030210⟩,
  ⟨14,4,[ew48,ew49,ew54,ew57,ew61],localHints 4 0x162186a270d82c46130c0542c03010185a05 0xff8edd84c443bb2a12943408706655430210⟩,
  ⟨14,4,[ew48,ew50,ew52,ew54,ew61],decodeHints 0xd0680209160b026010180c361b0084c4623012080c0b0f018381c048040e021480800000f01c0a05⟩,
  ⟨14,4,[ew48,ew50,ew54,ew56,ew61],decodeHints 0x160b0341a0080c06270580c361b00a180c0b0f01806230183800010c00000070f0002814000082a15⟩,
  ⟨14,5,[ew48,ew50,ew54,ew57,ew61],localHints 5 0xb1401a13a7c369e0988d340e6606012870082c00cb1480d0802168780c05 0x36e94bd29adcad665e08dc116b334c455cc331946258825d433a856ba4e611046a50842118c184826346107b5ae5adcd6b16b109225250631c84398c52104300820⟩
]

def nodesBlock3 : Array Node := #[
  ⟨14,4,[ew35,ew50,ew54,ew57,ew61],localHints 4 0xe06804320a82c4613048040007018280a06 0xff75ee87545dcc71bb5a911287665454331210⟩,
  ⟨14,4,[ew38,ew50,ew54,ew57,ew61],localHints 4 0x381a0d8982c0e098240200018080a06 0xdd75cc532332bb51a110993875654432321010⟩,
  ⟨14,4,[ew49,ew50,ew53,ew54,ew57],decodeHints 0xa0500007160b026001a8d42a150002c2c1601a0c0a130f014381c0480012031480c02010f0246432⟩,
  ⟨14,4,[ew49,ew50,ew54,ew56,ew57],decodeHints 0x160b02814000086a350980c2a15002180a130f0142c160183802001680002090f004341a0080c361b⟩,
  ⟨14,5,[ew49,ew50,ew54,ew57,ew61],localHints 5 0xb14435508502a9e05859360e098059c2d03a1c00cd148090a030c0183c05 0x97e963d2def4e5247e0c3c19ef25c864d88bb112932cc00806f784210a6a09d4094d273092408480424610085c17b9ab5b12962d6a4a50631c84398c52102310400⟩,
  ⟨14,4,[ew31,ew50,ew54,ew57,ew61],localHints 4 0xe06812270a85802130382c00020700c0c05 0xffd9ee9dcc649890bb06aa0398987655432210⟩,
  ⟨14,3,[ew32,ew54,ew57,ew61],decodeHints 0xe07012000d06802030a05000020d86c02050a85400060b058060a⟩,
  ⟨14,4,[ew50,ew51,ew54,ew57,ew61],decodeHints 0x381c04800341a0080c2814000082601058001c030d86c02050a85400060b058060a02b3c3c05⟩,
  ⟨14,4,[ew34,ew50,ew54,ew57,ew61],localHints 4 0x58350a04c2a16050040e000100c0c05 0xdda4cca2bb430a109941882766545432321010⟩,
  ⟨14,3,[ew50,ew52,ew53,ew56],localHints 4 0x522d2f070ba1a028c42806 0x469416911481776355432210⟩,
  ⟨14,4,[ew50,ew52,ew53,ew57,ew61],localHints 4 0xe22034070c0505a32048984602028580606 0xff7edd4c9417b1aa14918873633035432210⟩,
  ⟨14,4,[ew50,ew52,ew54,ew56,ew61],decodeHints 0xe070341a00a2004071480800010c00000071480028140d86c0205028980e05118140a0a0a8540006⟩,
  ⟨14,5,[ew50,ew52,ew54,ew57,ew61],localHints 5 0x71481a51825a21844800061b0084c4c2d03a7c46290127014d00f0150806 0xcb696fd2ed6cbde87e0f6c1defbdac741d8b5a108ab9d47be8e74def422435c90c88cf113e007400f789c202da26084b1014029d2240847114c500c022084310020⟩,
  ⟨14,4,[ew30,ew50,ew54,ew57,ew61],localHints 4 0xe0d428070d818460909804000b0700c0405 0xff85ee72dd5cbb87545a292387665454232100⟩,
  ⟨14,4,[ew33,ew50,ew54,ew57,ew61],localHints 4 0x2c0d09c3616050240200018080a06 0xcc65bb53a33299510110883765654432321010⟩,
  ⟨14,4,[ew50,ew53,ew54,ew56,ew57],decodeHints 0xe07028140022006091480c020016800020914804341a0a8540006190c812050b058060a0d86c0205⟩
]

def nodesBlock4 : Array Node := #[
  ⟨14,5,[ew50,ew53,ew54,ew57,ew61],localHints 5 0x714a145181c02d316a2404181902542150002c521601a7414d20f0190a05 0xb76ad0d59ce5e56749e0e725294af07b60eb5ded64a6a37568a54d6b9a9525ad3088ce7039e283c4e701a012d805300b5894229d004a007394c500c022084310020⟩,
  ⟨14,4,[ew28,ew50,ew54,ew57,ew61],localHints 4 0x1606828021909814130082416000380c1c05 0xff84ee72dd4c7b784a45212978764543212100⟩,
  ⟨14,4,[ew29,ew50,ew54,ew57,ew61],localHints 4 0x1c1a89c36150300412000380c0a0a 0xcc546b654a4399618847011065654343221010⟩,
  ⟨14,5,[ew50,ew54,ew56,ew57,ew61],localHints 5 0x240e1a5285148026a8a512180d805442d0a80140066a0790e160280c1c0a 0xa62a0e7318c6334673990c994a13b148628e70ae2a2ac26584a552b4148419843208a221b9e883d0e70da34296362c6a52128198603800600ca3008830906210020⟩,
  ⟨14,6,[ew50,ew54,ew57,ew61],localHints 5 0xe36c34da04851b2070106036016c04c5a150035c1606148583c0501b581c0a 0x6aefb9521b6d2f7d2e0b38e1994ef93ce10c0ee33cd7668e9638d6bace9329211921d12a210791c42a16c6912c2916b5212828066390262906310020⟩,
  ⟨24,3,[ew115,ew121,ew123,ew126],localHints 3 0x90b9b808011c80c2a 0x73b9e165e962698288⟩,
  ⟨24,4,[ew112,ew115,ew118,ew121,ew126],localHints 4 0x5874142a040480c2e03a281c02 0x767537a3b37a795958393807605004032010⟩,
  ⟨24,3,[ew115,ew118,ew128,ew129],localHints 4 0x5c0b0700814060c2300e8b 0x646916868114676345431210⟩,
  ⟨24,4,[ew112,ew115,ew118,ew126,ew128],localHints 4 0x12050605022030b8108d0382c1c02 0xc5233735937b7a585a393870060540032010⟩,
  ⟨24,4,[ew105,ew115,ew118,ew123,ew126],localHints 4 0x70e838162a09020043a6ea281406 0x567596b6c56b6a5a589a9867605054032010⟩,
  ⟨24,4,[ew105,ew115,ew118,ew126,ew129],localHints 4 0x100e090605025010e9bc8d0581c1406 0xd727372b927c7ab8ba292870760540232010⟩,
  ⟨24,3,[ew60,ew105,ew112,ew118],localHints 3 0x581c6c021a0181033 0x77b1700e0d758e3408⟩,
  ⟨24,4,[ew105,ew112,ew118,ew125,ew126],localHints 4 0xdf0c074502509020440b03818040a 0x6c6b36a393167181134167625234321210⟩,
  ⟨24,4,[ew66,ew105,ew112,ew118,ew126],localHints 4 0xd84e12130203a07010380c0a 0xaa563683992368617701313065654432321010⟩,
  ⟨24,3,[ew71,ew105,ew112,ew126],localHints 3 0x90206c02138180e26 0x77b1700e03758e3408⟩,
  ⟨24,4,[ew105,ew112,ew118,ew126,ew130],localHints 4 0x1d700a8500e05048100b038180422 0xc5b33a3593811561134172565234321210⟩
]

def nodesBlock5 : Array Node := #[
  ⟨24,4,[ew55,ew105,ew112,ew118,ew126],localHints 4 0x6c1d1a0cc1608038a01c02128280c22 0xddc7bb344794aa017971414088767645431210⟩,
  ⟨24,5,[ew105,ew112,ew115,ew118,ew126],localHints 5 0xd9c48f0eb851c2a142a5500e5382024a60382c1418010e80c2e 0x79d9eab3e733a8e452ab39d14a24e7039e4f7c4e783de348c0a539291a86330c073b4c619c62030641854a1252b52829084e7118c839c26080050902018c2208000⟩,
  ⟨24,3,[ew112,ew121,ew128,ew131],localHints 4 0x48540b030600e0e052300490 0x5a5958567736154141132110⟩,
  ⟨24,4,[ew112,ew118,ew121,ew126,ew128],localHints 4 0x120306054910582810251101c1c02 0xc5bb6a535a62292582721006054040030210⟩,
  ⟨24,4,[ew105,ew112,ew121,ew123,ew126],localHints 4 0x1038162e040480e3a031c9140a 0x5765767959586767bb9a9876765054332210⟩,
  ⟨24,4,[ew77,ew105,ew112,ew118,ew126],localHints 4 0x746827118202407058081406 0x46a49956883465604340770165654343221010⟩,
  ⟨24,4,[ew105,ew112,ew121,ew126,ew131],localHints 4 0x100b140603a25038e9c69103038040a 0xd77c7a9b9a17211981811870760540331210⟩,
  ⟨24,3,[ew82,ew105,ew118,ew126],localHints 3 0xe8206807138280423 0x77b1700e03752e3408⟩,
  ⟨24,4,[ew105,ew112,ew118,ew126,ew132],localHints 4 0x1205b905c2503074100711038040a 0xc5b44564a1191581142177565040431210⟩,
  ⟨24,4,[ew58,ew105,ew112,ew118,ew126],localHints 4 0x6c34198481c080581c5002128181422 0xdd56cca44694bb0a6160494188676543432210⟩,
  ⟨24,5,[ew105,ew112,ew118,ew121,ew126],localHints 5 0x39924ac0e82c68e5470b84aab5502024180301c543a530081c0a 0x852ac94d54a42526998aa55273328c42c8c8309316aa2d4a44a1360d13842789ae688a2098c1604461014a2252b52809494a7020e531804014a5008440846210020⟩,
  ⟨24,4,[ew105,ew112,ew118,ew128,ew129],localHints 4 0x1094242e040e80c0705a2d1a22 0x797847343443bb9a98343470765543432210⟩,
  ⟨24,4,[ew80,ew105,ew112,ew118,ew126],localHints 4 0x281a09c460e040480e0b010284406 0x57c5bb67aa4576705450990876765454332010⟩,
  ⟨24,4,[ew105,ew112,ew118,ew128,ew131],localHints 4 0x12038a03a2a040e80c9048888040e 0x7c78bb9a9817010110100172765544321010⟩,
  ⟨24,4,[ew69,ew105,ew112,ew118,ew126],localHints 4 0x6c25138981612040740e0207018440a 0xdd6747c4bb947670aa09434078765543432210⟩,
  ⟨24,5,[ew105,ew112,ew118,ew126,ew128],localHints 5 0x49d092152b850e7478b95a251381810185501c163a53808440e 0x445928496a534cc6a18b3299068a531944c930200138427880e009026252c6b049108ab01960294461210a0a1484a4240a108098c4294e6304a5088440006210400⟩
]

def nodesBlock6 : Array Node := #[
  ⟨24,4,[ew88,ew105,ew112,ew118,ew126],localHints 4 0x74662611848100b038380406 0x35a31561134199568834771265654343212100⟩,
  ⟨24,3,[ew105,ew123,ew129,ew131],localHints 4 0x20540701038300b052300c93 0xaa4988457765143131132110⟩,
  ⟨24,4,[ew105,ew118,ew123,ew126,ew129],localHints 4 0x801094300e152500e121102c1406 0xccbb894a4982272462551001043030030210⟩,
  ⟨24,4,[ew105,ew112,ew123,ew126,ew131],localHints 4 0x1007140605ce94a038040b0e8880c0a 0xddcc4a3b3a46496876551401132121120110⟩,
  ⟨24,3,[ew93,ew112,ew118,ew126],localHints 3 0xe848660b130280c23 0x77b1700e03752e3408⟩,
  ⟨24,4,[ew105,ew112,ew118,ew126,ew133],localHints 4 0x8038083a0e12ba874121102c0c0a 0xccbb2492aa494828276115143112010110⟩,
  ⟨24,4,[ew59,ew105,ew112,ew118,ew126],localHints 4 0x6c341982824080382c5002070940c22 0xdd58cc286362bb8116a1a11a98776544321010⟩,
  ⟨24,5,[ew105,ew112,ew118,ew123,ew126],localHints 5 0x3b12ab00e81d5e18010cc101275a387422152ac162e540181c0a 0x10632cd6d58c835a5994ed6d2732b5a43c8b09058c235b16302d69cef0c1e72942409ce7135c86390d6898242d024884a1212811c4029406008a2010020884310020⟩,
  ⟨24,4,[ew91,ew105,ew112,ew118,ew126],localHints 4 0x2819898460a090201607070940406 0x46c416711451bb67aa45991876765454312100⟩,
  ⟨24,4,[ew105,ew112,ew118,ew129,ew131],localHints 4 0x8038a03a2a170092694128480c0a 0xcc28bb9a9823276655431201011010010110⟩,
  ⟨24,4,[ew70,ew105,ew112,ew118,ew126],localHints 4 0x6c271109810120e82c0e02128380c0a 0xdd758782cc2518b1aa51011099876544321010⟩,
  ⟨24,5,[ew105,ew112,ew118,ew126,ew129],localHints 5 0x21dc95152c4500257bb51e3a0c2b444121301c162e548184a0a 0x45d90bb1aa62cca5a14d3319668a111944c832d700ae0b420240ad6b094a4319e5284c6038026084d1018012c494212a48902118e029c06308a2010020884310020⟩,
  ⟨24,4,[ew92,ew105,ew112,ew118,ew126],localHints 4 0x4a331308c241d0402c5007070081406 0x478427d22432cc70bb40aa2397876454323210⟩,
  ⟨24,4,[ew81,ew105,ew112,ew118,ew126],localHints 4 0x68271108c101d0901c500b070081406 0x4784dd72cc4207b00410aa2199876654321010⟩,
  ⟨24,5,[ew105,ew112,ew118,ew126,ew131],localHints 5 0x200ef04a8b96225583bd243a0c2b8441d152b05023030081c0a 0x75d90bb2d752aeab420a72ad6b150419043308a4212c50422118090211c412842f088a21b8606000d00d831ac694212a48d0319c602800600ca3008830906210020⟩,
  ⟨24,6,[ew105,ew112,ew118,ew126],localHints 5 0x1b3d8501d1a3d44a277a0cde6220406024267901c540b1d08de206010b81c0a 0x72b1b4e5fbd6718729ea70db7155f7b55ad70de348d14105549850848d43711f23c1b28c1ef711a44914c3810c5814a4910410066390262906310020⟩
]

def nodesBlock7 : Array Node := #[
  ⟨25,6,[ew97,ew116,ew119,ew127,ew134],localHints 5 0x56041543807158c84219050bc34012c824da5430810280001041ee172280c1816 0x1a86a1ee1c1ec7a1aa0a7a1d97e2197e1ce7a2081a2971995719a941a14a786107cdf67ce10786411cd55186951854a1ce949050894cc694d08904c178a1179dd179e10789c21898d18d4a18d8b1894a21d09208c92090821cc62148018820⟩,
  ⟨25,7,[ew97,ew106,ew113,ew119,ew127,ew134],localHints 6 0xac082a8700e2b0c8d4480e1904c420d052c8600125824a8042e00022100780c3e17208801805 0xcc0cc0e04210e00df0cc40c3ca39e3dd41e3dd38e3ca40a0ca6dc0c831c0c86db0ca30c3c74103d839a3d84103c738e0d85190c73190c75140d830c10728a11820811828a1072073c14103d35973d34103c15960d33150c15150c130c0d351414128a15320815328a1412011011011041c71041523cf4103d138e3d14103cf38e0c234d0c330c0c334d0c230c10928a10420810b28a1092081041060c21c61051000c2040⟩,
  ⟨25,7,[ew106,ew113,ew116,ew119,ew127,ew134],localHints 6 0x56041543807158c12c192e04434093685088020786c0248098101a15178000c10060dc40030285c3eb2 0x18e18e1a34641a31a218e44e40a62142046142061840a44a18a71f18839f18871c18a38e41045141e41e41e4514102dd18538e18671c18638e18571c2da28a2db2082cb28a2da20840445941461941445140460418435718638e18634d18438e55429608421654428a0942080410531841444034524093d24094514033c318338e18634d18638e18334d2c928c04320c2c328a049208082087183143082104043043082040⟩,
  ⟨25,7,[ew74,ew106,ew113,ew119,ew127,ew134],localHints 6 0x15810550e0ac3235121101c1b098540c100b0c0124c008101a5c03844002f0f83c0617060ec4005 0x8e08e0a13e20a10a008e3ce40945f40b3df40b4514093c908975e09439e09475d08938e4063cf41945c4193cf40645109935b08639b08634d09938e6862491195146992491065064003d84155d84153cf4005c008038e08234d08238e08034d1d52561c05161c02491d55141041d31c01c01041864104514123cf4124514103cf08138e08234d08238e08134d1ca2cb1c72491cc2cb1ca2491c81c5081185104103081000⟩,
  ⟨25,7,[ew85,ew106,ew113,ew119,ew127,ew134],localHints 6 0x2b020aa1c038ac321a049b428021908414100f8586013268041a042e02c22000780c5e171e0801805 0xcc0cc0e23a30e20e10cc38c3c86e03df3a03df6db3c83880c875e0d431e0d475d0c830c3c639c3d86dc3d838e3c66c60c635a0c330c0c334d0c630c1182191065191062081185143c138e3d54173d538e3c14100d53160c13560c130c0d534d1412084d55141552084c15011044d21041861011013cf4103d138e3d14103cf38e0c234d0c330c0c334d0c230c10928a10420810b28a1092081041070c21861051000c2040⟩,
  ⟨25,6,[ew101,ew113,ew122,ew127,ew134],localHints 5 0x560415436210d008480d030bc38092d004de5730011f046060542803000440e0f 0x4290a46ddc46d1a429ca79dd97cdf97cdce79e4744d5841e9841d4a44e94791d77da177d9ce792044129540155402944114a90260910e491264900e778e11785d17861078dc340d8d4214a4218b40d4a1244640ce61048510c0510c8310400⟩,
  ⟨25,7,[ew101,ew106,ew113,ew119,ew127,ew134],localHints 6 0xac082a8b056190d008480b0d84c420d59818600927004ae04080002e440183c3e11210801805 0xcc0cc0e03a10e00df0cc38c3cb41e3d839e3d84103cb38e0d871d0cb31d0cb71c0d830c3c739b3da41b3da38e3c74070c75190c63190c65140c730c1066061072c71076071062c63c13973d25973d238e3c15960d23150c15150c130c0d25141011011042cb1041531411c71521861521c71411813cf4103d138e3d14103cf38e0c234d0c330c0c334d0c230c10410a0c22ca1091c71041861081c71041861051000c2040⟩,
  ⟨25,7,[ew106,ew113,ew119,ew122,ew127,ew134],localHints 6 0x560415460960e1bc32100d00812242205c285c038c80249098101a0c1c0800011598585e050187c140f 0x2ce2ce2e34642e32e22ce44e4104514214214214514101602ca38e2cb34d2cb38e2ca34d40965f41345f4136594094492c975e2cb38e2cb75d2c938e08209c2c928940345b41a65b41a4514036432c33582c03982c034d2c338e1405c01435831431431405802002555034d55032492004c04044514013d24014514043c42c438e2cb34d2cb38e2c434d20820c2c42842082490840842080871410c60840061440c3081000⟩,
  ⟨25,7,[ew63,ew106,ew113,ew119,ew127,ew134],localHints 6 0x1581055160ac321a121701632098542c0a078c0024f048101a2f0800088020f85c0611060f44005 0x8e08e0a14620a10a008e44e40b3df41945f4193cf40b45109975e08b39e08b75d09938e40545c4083dc4084514053c508535b09339b09334d08538e1136536852c56856451132d34004514145d84144514005c008038e08234d08238e08034d1041d61c01c01042cb1d41551c04d51c01451d44d34104514123cf4124514103cf08138e08234d08238e08134d1cc1ca0812ca1c62081c71451c92081c6145104103081000⟩,
  ⟨25,7,[ew87,ew106,ew113,ew119,ew127,ew134],localHints 6 0x2b020aa1c378680409120500e1b108342a060f83c6013280043204080002e440700c5e111f0801805 0xcc0cc0e23a30e20e10cc38c3ca7203d93a03d971c3ca38a0ca35f0c330c0c334d0ca30c3c639e3dd71e3dd38e3c67060c659b0d231b0d25960c630c11229a10665a10628a1126523c13983d44183d438e3c14100d43170c15970c130c0d45961044d510428a1011011411864d44921541864c14813cf4103d138e3d14103cf38e0c234d0c330c0c334d0c230c10410b0c228a1091c71041861081c71041861051000c2040⟩,
  ⟨25,6,[ew106,ew108,ew124,ew127,ew134],localHints 5 0x56041543424161c4b0637c85036060096c26210211c1a022203c2a0500044160c 0x52d4b56dfc56d5a52deb719f9721d9721ef718e65213851978519295216b70db7705f7705ad70de350eb65296b52ab450d6b14c5250cd2711f1741b1741ef711a45116c5012c5016b5112938100390c439104380c010065110251106310020⟩,
  ⟨25,7,[ew106,ew108,ew113,ew119,ew127,ew134],localHints 6 0xac082a87056190d02448b41816000200186c0c012884c4204218340e100105c1e1f17814220c 0x2cc2cc2e04212e02df2cc40c3c869e3c941e3c969a3c84102c971d2c831d2c871c2c930c3c541b3c769b3c74103c569a2c72992c53192c528a2c730c0450450412080411983cf38e3d74103d738e3cf4102d45962cb30c2cb5962d430c0410552d42150460532d41533c24123d13923d14103c23822c230d2c028d2c030c2c228a0402400422020422420402001801c01821421821c21801400400400421020420c2040040⟩,
  ⟨25,7,[ew106,ew113,ew119,ew124,ew127,ew134],localHints 6 0x56041546096161c432101a8241e205a06c0c012504c42041c8345e1f0a97000110585888050185c1c0c 0x3d03d03e35243e33e23d05104d35144e14e14e15144d31603d838e3cf4103cf38e3d84104c969f4c751f4c769a4c95093c975e3cf4103cf75d3c941008209c3c96094c35144c169b4c15144c36833c338e3cf4103cf38e3c34102082193c36032082490830832080974c45164d54964d55144c44843c44113c03913c04103c438e14034014430414434414030020024b2841cb2842492001c00800c61440461440c3080040⟩,
  ⟨25,7,[ew65,ew106,ew113,ew119,ew127,ew134],localHints 6 0x15810550e0ac32350a06c26212e01c2c0e060c0025204834084408000220f1f880061f178182e05 0x1cd1cd1e14621e11e01cd44d40b3df41645f4163cf40b4511d675e1cb35e1cb75d1d634d4054514143dc4144514053c51c538e1c734d1c738e1c534d24905b0450452492cb40045a40265a4024514006401c03581d33981d334d1c038e2535935c02c05c05802532d30531550405150401450535134104514123cf4124514103cf1c638e1c734d1c738e1c634d04c04a1c62ca2492481c6145044082041000043082041000⟩,
  ⟨25,7,[ew76,ew106,ew113,ew119,ew127,ew134],localHints 6 0x2b020aa2c3886848140d81826210685416020b83060092980432040800088401003c061f178282205 0x20c20c2223a322222120c38c3ca4203d53a03d54103ca38a20a35f20830c20834d20a30c3c639e3d441e3d438e3c64102145dd20631d2065d721430c0414dc04128a0460463c039b3da65b3da38e3c06402003182125d821230c2005d705229604055604028a0525524d25122401802405004d21923cf4103d138e3d14103cf38e20734d20830c20834d20730c04104b20728a049045207185044082041000043082041000⟩,
  ⟨25,8,[ew106,ew113,ew119,ew127,ew134],localHints 6 0x56041543807158643402048920b040a40e041b03004601310810400d80c002aff003f820fd7e059f60501be81e0c 0x4524524675a846746645259254b7e55645a55647df54b58b44b8a34494a34498a244b4925435a15607e15605965437c344341e44149e4414104434927412db70325b6832cb6412415445985575185575965445044444934404134404924444103c02cd38424d3042cb2802402000c61c40461440c3080040⟩
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
        nodesBlock7[(i-112)]?

def fastViews : QFast.Table View := ⟨27,viewsGet⟩

def fastNodes : QFast.Table Node := ⟨128,nodesGet⟩

end SignedProjection



namespace SignedProjection

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_0 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 0 4 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_4 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 4 4 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_8 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 8 4 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_12 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 12 4 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_16 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 16 4 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_20 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 20 4 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_24 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 24 3 = true := by decide +kernel

theorem joinRoots_0_0 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 0 8 = true :=
  @QFast.merge_blocks (QFast.checkRootAt fastViews fastNodes) 0 4 4 blockRoots_0 blockRoots_4

theorem joinRoots_0_8 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 8 8 = true :=
  @QFast.merge_blocks (QFast.checkRootAt fastViews fastNodes) 8 4 4 blockRoots_8 blockRoots_12

theorem joinRoots_0_16 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 16 8 = true :=
  @QFast.merge_blocks (QFast.checkRootAt fastViews fastNodes) 16 4 4 blockRoots_16 blockRoots_20

theorem joinRoots_1_0 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 0 16 = true :=
  @QFast.merge_blocks (QFast.checkRootAt fastViews fastNodes) 0 8 8 joinRoots_0_0 joinRoots_0_8

theorem joinRoots_1_16 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 16 11 = true :=
  @QFast.merge_blocks (QFast.checkRootAt fastViews fastNodes) 16 8 3 joinRoots_0_16 blockRoots_24

theorem joinRoots_2_0 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 0 27 = true :=
  @QFast.merge_blocks (QFast.checkRootAt fastViews fastNodes) 0 16 11 joinRoots_1_0 joinRoots_1_16

theorem certifiedRoots : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 0 27 = true := joinRoots_2_0

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 8 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_8 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 8 8 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_16 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 16 8 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_24 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 24 8 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_32 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 32 8 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_40 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 40 8 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_48 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 48 8 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_56 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 56 8 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_64 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 64 8 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_72 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 72 8 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_80 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 80 8 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_88 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 88 8 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_96 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 96 8 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_104 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 104 8 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_112 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 112 8 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_120 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 120 8 = true := by decide +kernel

theorem joinNodes_0_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 16 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 8 8 blockNodes_0 blockNodes_8

theorem joinNodes_0_16 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 16 16 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 16 8 8 blockNodes_16 blockNodes_24

theorem joinNodes_0_32 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 32 16 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 32 8 8 blockNodes_32 blockNodes_40

theorem joinNodes_0_48 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 48 16 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 48 8 8 blockNodes_48 blockNodes_56

theorem joinNodes_0_64 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 64 16 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 64 8 8 blockNodes_64 blockNodes_72

theorem joinNodes_0_80 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 80 16 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 80 8 8 blockNodes_80 blockNodes_88

theorem joinNodes_0_96 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 96 16 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 96 8 8 blockNodes_96 blockNodes_104

theorem joinNodes_0_112 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 112 16 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 112 8 8 blockNodes_112 blockNodes_120

theorem joinNodes_1_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 32 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 16 16 joinNodes_0_0 joinNodes_0_16

theorem joinNodes_1_32 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 32 32 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 32 16 16 joinNodes_0_32 joinNodes_0_48

theorem joinNodes_1_64 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 64 32 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 64 16 16 joinNodes_0_64 joinNodes_0_80

theorem joinNodes_1_96 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 96 32 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 96 16 16 joinNodes_0_96 joinNodes_0_112

theorem joinNodes_2_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 64 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 32 32 joinNodes_1_0 joinNodes_1_32

theorem joinNodes_2_64 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 64 64 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 64 32 32 joinNodes_1_64 joinNodes_1_96

theorem joinNodes_3_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 128 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 64 64 joinNodes_2_0 joinNodes_2_64

theorem certifiedNodes : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 128 = true := joinNodes_3_0

end SignedProjection

namespace SignedProjection
def bMatches (z : Option View) : Bool :=
  match z with
  | none => false
  | some v => vg v == (0xfe80e880fe808080 : Word) && vk v == 9 && (vs v).toFinset == Direct64.cols.toFinset

theorem rootNegative : ¬ CoreSigned.build signedOps (0xfe80e880fe808080 : BitVec 64) 9 Direct64.cols.toFinset := by
  have shape : bMatches (QFast.get fastViews 26) = true := by decide +kernel
  cases ev : QFast.get fastViews 26 with
  | none => simp [ev, bMatches] at shape
  | some v =>
    have valid := QFast.certified_view fastViews fastNodes certifiedRoots certifiedNodes ev
    simp only [ev,bMatches,Bool.and_eq_true,beq_iff_eq] at shape
    change ¬ CoreSigned.build signedOps (vg v) (vk v) (vs v).toFinset at valid
    rwa [shape.1.1,shape.1.2,shape.2] at valid
end SignedProjection
end PEqualNP.Outside.L_meta_12266_aux

open PEqualNP.Outside.L_meta_12266_aux in
theorem PEqualNP.Outside.L_meta_12266 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4269860992 * 2 ^ 32 + 4269834368) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4269860992 * 2 ^ 32 + 4269834368) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  LowerSymSix.finish SignedProjection.rootNegative
