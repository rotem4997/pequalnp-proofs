import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_13501

namespace CoreSigned

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

def F (x : Fin 6 → Bool) : Bool := Nat.testBit (3941264072 * 2 ^ 32 + 3939035784) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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

namespace Direct64
open PEqualNP.CircuitLowerBounds SignedProjection
abbrev W := BitVec 64
abbrev basicOps (a b : W) := signedOps a b
abbrev goal : W := ~~~0xeaeaeac8eac8ea88
open CoreSigned (build)
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

theorem sample64 : ∀ k : Fin 64, CoreSigned.F (fun i => (cols.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by
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

theorem low (reject : ¬ build basicOps (0xeaeaeac8eac8ea88 : W) 8 cols.toFinset)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = CoreSigned.F x) : 8 < binaryCost gs := by
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
namespace SignedProjection.Fast
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
      | some v => cutOK v g k ws (val/1024)
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
    exact cutOK_sound (known _ lt _ hv) ok
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

end SignedProjection.Fast
namespace SignedProjection
def labelsBlock0 : Array Nat := #[
  1,
  5,
  9,
  12,
  13,
  17,
  21,
  25,
  28,
  29,
  33,
  36,
  37,
  41,
  45,
  49
]
def labelsBlock1 : Array Nat := #[
  52,
  53,
  56,
  57,
  60,
  61,
  65,
  69,
  73,
  77,
  81,
  85,
  88,
  89,
  92,
  93
]
def labelsBlock2 : Array Nat := #[
  97,
  101,
  105,
  109,
  113,
  116,
  117,
  120,
  121,
  125,
  129,
  133,
  137,
  141,
  145,
  149
]
def labelsBlock3 : Array Nat := #[
  152,
  153,
  156,
  157,
  161,
  165,
  169,
  173,
  177,
  180,
  181,
  184,
  185,
  189,
  193,
  196
]
def labelsBlock4 : Array Nat := #[
  197,
  201,
  205,
  209,
  212,
  213,
  216,
  217,
  221,
  225,
  229,
  233,
  237,
  241,
  245,
  249
]
def labelsBlock5 : Array Nat := #[
  253,
  257,
  261,
  265,
  268,
  269,
  273,
  277,
  281,
  285,
  289,
  292,
  293,
  297,
  301,
  305
]
def labelsBlock6 : Array Nat := #[
  309,
  313,
  317,
  321,
  325,
  329,
  333,
  337,
  341,
  345,
  349,
  353,
  357,
  361,
  365,
  369
]
def labelsBlock7 : Array Nat := #[
  373,
  377,
  381,
  385,
  389,
  393,
  397,
  401,
  405,
  409,
  413,
  417,
  421,
  425,
  429,
  433
]
def labelsBlock8 : Array Nat := #[
  437,
  441,
  445,
  449,
  452,
  453,
  457,
  461,
  465,
  469,
  473,
  477,
  481,
  485,
  489,
  493
]
def labelsBlock9 : Array Nat := #[
  497,
  501,
  505,
  509,
  513,
  517,
  521,
  524,
  525,
  529,
  533,
  537,
  600,
  664,
  1308,
  1332
]
def labelsBlock10 : Array Nat := #[
  1368,
  1372,
  1396,
  1432,
  1436,
  1460,
  1492,
  1564,
  1592,
  1624,
  1628,
  1688,
  1692,
  1752,
  2616,
  3100
]
def labelsBlock11 : Array Nat := #[
  3124,
  3128,
  3160,
  3188,
  3192,
  3224,
  3252,
  3256,
  4098,
  4102,
  4106,
  4110,
  4114,
  4118,
  4122,
  4126
]
def labelsBlock12 : Array Nat := #[
  4130,
  4134,
  4138,
  4142,
  4146,
  4150,
  4154,
  4158,
  4162,
  4166,
  4170,
  4174,
  5148,
  5172,
  5176,
  5208
]
def labelsBlock13 : Array Nat := #[
  5212,
  5236,
  5240,
  5272,
  5332,
  5336,
  5404,
  5428,
  5464,
  5468,
  5492,
  5588,
  7220,
  7224,
  7284,
  7288
]
def labelsBlock14 : Array Nat := #[
  7348,
  7380,
  9244,
  9268,
  9272,
  9304,
  9368,
  9372,
  9396,
  9400,
  9428,
  9432,
  9500,
  9524,
  9624,
  9628
]
def labelsBlock15 : Array Nat := #[
  9652,
  9684,
  11316,
  11320,
  11444,
  11448,
  11476,
  13400,
  13464,
  13524,
  13528,
  4259894,
  4395054,
  5308470,
  5374006,
  5378102
]
def labelsBlock16 : Array Nat := #[
  5439534,
  5439538,
  5439542,
  5443638,
  5447734,
  6357046,
  6422582,
  6426678,
  6488118,
  6492206,
  6492210,
  6492214,
  7405622,
  7536686,
  5519769654,
  5519904814
]
def labelsBlock17 : Array Nat := #[
  5521997878,
  5523046446,
  5586878518,
  5589041206,
  5637345326,
  6594560054,
  6661668918,
  6661738550,
  7794266166
]
def labelsGet (i : Nat) : Option Nat :=
  if i < 144 then
    if i < 64 then
      if i < 32 then
        if i < 16 then
          labelsBlock0[(i - 0)]?
        else
          labelsBlock1[(i - 16)]?
      else
        if i < 48 then
          labelsBlock2[(i - 32)]?
        else
          labelsBlock3[(i - 48)]?
    else
      if i < 96 then
        if i < 80 then
          labelsBlock4[(i - 64)]?
        else
          labelsBlock5[(i - 80)]?
      else
        if i < 112 then
          labelsBlock6[(i - 96)]?
        else
          if i < 128 then
            labelsBlock7[(i - 112)]?
          else
            labelsBlock8[(i - 128)]?
  else
    if i < 208 then
      if i < 176 then
        if i < 160 then
          labelsBlock9[(i - 144)]?
        else
          labelsBlock10[(i - 160)]?
      else
        if i < 192 then
          labelsBlock11[(i - 176)]?
        else
          labelsBlock12[(i - 192)]?
    else
      if i < 240 then
        if i < 224 then
          labelsBlock13[(i - 208)]?
        else
          labelsBlock14[(i - 224)]?
      else
        if i < 256 then
          labelsBlock15[(i - 240)]?
        else
          if i < 272 then
            labelsBlock16[(i - 256)]?
          else
            labelsBlock17[(i - 272)]?
def hints (enc i : Nat) : Nat := (labelsGet ((enc >>> (i * 9)) % 512)).getD 0
def viewsBlock0 : Array View := #[
  ⟨0xf0f0,⟨4,by decide⟩,0xe080,[0xa0a0, 0xc0c0, 0xf000],3,hints 0x4da9d3c084f8402408⟩,
  ⟨0x3030c0c0,⟨6,by decide⟩,0x2000c080,[0x20208080, 0x3000c000, 0x30300000],3,hints 0x4802024086b0202408⟩,
  ⟨0xa0a05050,⟨4,by decide⟩,0xa0804000,[0x80804040, 0xa0005000, 0xa0a00000],3,hints 0x4c2c55012550784a12⟩,
  ⟨0x30300000c0c0,⟨6,by decide⟩,0x20000000c080,[0x202000008080, 0x30000000c000, 0x303000000000],3,hints 0x488202408760202408⟩,
  ⟨0xa0a000005050,⟨4,by decide⟩,0xa08000004000,[0x808000004040, 0xa00000005000, 0xa0a000000000],3,hints 0x4cac55012560c87212⟩,
  ⟨0x30003000c000c0,⟨6,by decide⟩,0x20000000c00080,[0x20002000800080, 0x30000000c00000, 0x30003000000000],3,hints 0x498203808760203808⟩,
  ⟨0x3000c0003000c0,⟨6,by decide⟩,0x2000c000000080,[0x20008000200080, 0x30000000300000, 0x3000c000000000],3,hints 0x49021ac08180206008⟩,
  ⟨0x60006000600060,⟨5,by decide⟩,0x60004000400000,[0x40004000400040, 0x60000000600000, 0x60006000000000],3,hints 0x4a361521c558c0881c⟩,
  ⟨0xa0005000a00050,⟨4,by decide⟩,0xa0004000800000,[0x80004000800040, 0xa0000000a00000, 0xa0005000000000],3,hints 0x4ab65541e558c0881e⟩,
  ⟨0xa000a000500050,⟨4,by decide⟩,0xa0008000400000,[0x80008000400040, 0xa0000000500000, 0xa000a000000000],3,hints 0x4b33d521c560c8881c⟩,
  ⟨0xf00000000000f0,⟨4,by decide⟩,0xe0000000000080,[0xa00000000000a0, 0xc00000000000c0, 0xf0000000000000],3,hints 0x4d29d3c08531108c08⟩,
  ⟨0xf0f0f0f0,⟨4,by decide⟩,0xe0c0e080,[0xa0a0a0a0, 0xc0c0c0c0, 0xf000f000, 0xf0f00000],4,hints ((6040019 * 1152921504606846976 + 867030356660880714) * 1152921504606846976 + 703547275388920840)⟩,
  ⟨0xf0f00000f0f0,⟨4,by decide⟩,0xe0c00000e080,[0xa0a00000a0a0, 0xc0c00000c0c0, 0xf0000000f000, 0xf0f000000000],4,hints ((6040019 * 1152921504606846976 + 867030356660880730) * 1152921504606846976 + 704250962830697480)⟩,
  ⟨0xf000f000f000f0,⟨4,by decide⟩,0xe000c000c00080,[0xa000a000a000a0, 0xc000c000c000c0, 0xf0000000f00000, 0xf000f000000000],5,hints ((4270547 * 1152921504606846976 + 867036016375006554) * 1152921504606846976 + 704250963783858184)⟩,
  ⟨0x30303030c0c0c0c0,⟨6,by decide⟩,0x20202000c0c0c080,[0x2020202080808080, 0x30003000c000c000, 0x30300000c0c00000, 0x3030303000000000],4,hints ((6128130 * 1152921504606846976 + 290497577755903840) * 1152921504606846976 + 144749060289471496)⟩,
  ⟨0x3030c0c03030c0c0,⟨6,by decide⟩,0x2020c0c02000c080,[0x2020808020208080, 0x3000c0003000c000, 0x3030000030300000, 0x3030c0c000000000],4,hints ((6062594 * 1152921504606846976 + 290599832337285504) * 1152921504606846976 + 144749062973826056)⟩
]
def viewsBlock1 : Array View := #[
  ⟨0x6060606060606060,⟨5,by decide⟩,0x6060604060406000,[0x4040404040404040, 0x6000600060006000, 0x6060000060600000, 0x6060606000000000],4,hints ((6272514 * 1152921504606846976 + 4596538458309976) * 1152921504606846976 + 865255187054338064)⟩,
  ⟨0xa0a05050a0a05050,⟨4,by decide⟩,0xa0a04040a0804000,[0x8080404080804040, 0xa0005000a0005000, 0xa0a00000a0a00000, 0xa0a0505000000000],4,hints ((6106197 * 1152921504606846976 + 5160040359077208) * 1152921504606846976 + 870603349051329042)⟩,
  ⟨0xa0a0a0a050505050,⟨4,by decide⟩,0xa0a0a08040404000,[0x8080808040404040, 0xa000a00050005000, 0xa0a0000050500000, 0xa0a0a0a000000000],4,hints ((6171733 * 1152921504606846976 + 5159488730506592) * 1152921504606846976 + 902726680767918610)⟩,
  ⟨0xf0f0f0f0f0f0f0f0,⟨4,by decide⟩,0xe0e0e0c0e0c0e080,[0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],7,hints ((((179646268664 * 1152921504606846976 + 288864267331713032) * 1152921504606846976 + 358106693878786502) * 1152921504606846976 + 2339228205745457) * 1152921504606846976 + 73043327557051400)⟩,
  ⟨0xffffffffffffffff,⟨0,by decide⟩,0xeaeaeac8eac8ea88,[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],8,hints (((((((((27285825539 * 1152921504606846976 + 392477994212229834) * 1152921504606846976 + 577355216861541706) * 1152921504606846976 + 417286880109541379) * 1152921504606846976 + 204962883164799682) * 1152921504606846976 + 289168971637208298) * 1152921504606846976 + 416020233953519619) * 1152921504606846976 + 204962316230463434) * 1152921504606846976 + 577377812705456856) * 1152921504606846976 + 201114089234899971)⟩
]
def viewsGet (i : Nat) : Option View :=
  if i < 16 then
    viewsBlock0[(i - 0)]?
  else
    viewsBlock1[(i - 16)]?
def nodesBlock0 : Array Node := #[
  ⟨19,7,[0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints (((((((((((((((((((((((439846117516131413 * 1152921504606846976 + 479137739802785306) * 1152921504606846976 + 744618506590194335) * 1152921504606846976 + 444661566112185368) * 1152921504606846976 + 787393982839256618) * 1152921504606846976 + 565388627990368930) * 1152921504606846976 + 444565033266096085) * 1152921504606846976 + 188977081766577059) * 1152921504606846976 + 692255834206983851) * 1152921504606846976 + 439797738870286229) * 1152921504606846976 + 152053335042671371) * 1152921504606846976 + 276173776465027742) * 1152921504606846976 + 444300898062216275) * 1152921504606846976 + 1013981358412432938) * 1152921504606846976 + 546037154340255399) * 1152921504606846976 + 201484778517085467) * 1152921504606846976 + 494095966185092642) * 1152921504606846976 + 711052461686215337) * 1152921504606846976 + 145093628272978389) * 1152921504606846976 + 191229990730270250) * 1152921504606846976 + 870603228964798111) * 1152921504606846976 + 444340482975935507) * 1152921504606846976 + 866965647943303322) * 1152921504606846976 + 708131530517602992)⟩,
  ⟨19,6,[0x8080808080808080, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints ((((((((((((((((((((((((11643028890283 * 1152921504606846976 + 374860583156361941) * 1152921504606846976 + 189007869311104299) * 1152921504606846976 + 873538713750945439) * 1152921504606846976 + 565902918076675743) * 1152921504606846976 + 492950277191308632) * 1152921504606846976 + 872798590103803563) * 1152921504606846976 + 399533262601750297) * 1152921504606846976 + 1076657401700717963) * 1152921504606846976 + 888947408309412511) * 1152921504606846976 + 41312296813176787) * 1152921504606846976 + 1058466498446275931) * 1152921504606846976 + 944469173213157040) * 1152921504606846976 + 543459721090480030) * 1152921504606846976 + 206136621793252600) * 1152921504606846976 + 294434372705140383) * 1152921504606846976 + 561438471489858585) * 1152921504606846976 + 49918592825525787) * 1152921504606846976 + 150989907524592328) * 1152921504606846976 + 34636088029098520) * 1152921504606846976 + 632848837870649451) * 1152921504606846976 + 78015393019300603) * 1152921504606846976 + 358737619200422227) * 1152921504606846976 + 1053563251931764106) * 1152921504606846976 + 540516090390077607)⟩,
  ⟨19,5,[0x2020202020202020, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints ((((((((10644 * 1152921504606846976 + 926427228159268090) * 1152921504606846976 + 564161018113056939) * 1152921504606846976 + 398691955683918978) * 1152921504606846976 + 335605763087906106) * 1152921504606846976 + 708524284602831007) * 1152921504606846976 + 376087190753356507) * 1152921504606846976 + 480610458364712186) * 1152921504606846976 + 726181821661405351)⟩,
  ⟨19,5,[0x4040404040404040, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints ((((((((10644 * 1152921504606846976 + 926427228159268090) * 1152921504606846976 + 564161018141952171) * 1152921504606846976 + 356480647731029907) * 1152921504606846976 + 1056181163375048026) * 1152921504606846976 + 870652428310028447) * 1152921504606846976 + 378338913239283413) * 1152921504606846976 + 494081751986935106) * 1152921504606846976 + 564368278499708583)⟩,
  ⟨19,5,[0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf080f080f080f080, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints (((((((((((((((((381518770676803998 * 1152921504606846976 + 205878786320405752) * 1152921504606846976 + 221783612944932874) * 1152921504606846976 + 534377316790272595) * 1152921504606846976 + 1070260944589842106) * 1152921504606846976 + 564403462875144422) * 1152921504606846976 + 493357243989077083) * 1152921504606846976 + 482264123406350216) * 1152921504606846976 + 511697959608771249) * 1152921504606846976 + 466861590840312982) * 1152921504606846976 + 191495565738636675) * 1152921504606846976 + 492597999792154843) * 1152921504606846976 + 493919687136525398) * 1152921504606846976 + 62580535491237602) * 1152921504606846976 + 870648934391619760) * 1152921504606846976 + 378374251944590933) * 1152921504606846976 + 47384768226821514) * 1152921504606846976 + 853727377296024240)⟩,
  ⟨19,4,[0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf080f080f080f080, 0xf0f0f080f0f0f080, 0xf0f0f0f000000000],hints (((((1428721347162 * 1152921504606846976 + 1056942569783161216) * 1152921504606846976 + 870719823195230950) * 1152921504606846976 + 464650739262171867) * 1152921504606846976 + 480606609937700458) * 1152921504606846976 + 870900506468135088)⟩,
  ⟨19,3,[0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf0f0f080f0f0f080, 0xf0f0f0f0f080f080],hints (((21382409897 * 1152921504606846976 + 108298969155503893) * 1152921504606846976 + 195175042781984538) * 1152921504606846976 + 744794425502052528)⟩,
  ⟨19,4,[0x70000000700000, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf080f080f080f080, 0xf0f0f0f000000000],hints (((((1368575616966 * 1152921504606846976 + 13604997216412994) * 1152921504606846976 + 564650583750615056) * 1152921504606846976 + 358776548371475476) * 1152921504606846976 + 911536553026253024) * 1152921504606846976 + 510361503224947369)⟩,
  ⟨19,4,[0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf080f080f080f080, 0xf0f00000f0f00000, 0xf0f0f0f0f080f080],hints (((((1428721347155 * 1152921504606846976 + 1053691311433617792) * 1152921504606846976 + 870721884779532977) * 1152921504606846976 + 466902539127368406) * 1152921504606846976 + 48229159965202202) * 1152921504606846976 + 870899063359123632)⟩,
  ⟨19,4,[0x70007000000000, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf080f080f080f080, 0xf0f00000f0f00000],hints (((((1368524564419 * 1152921504606846976 + 584435150473995586) * 1152921504606846976 + 564650446445355024) * 1152921504606846976 + 358776548371475476) * 1152921504606846976 + 911536553072390528) * 1152921504606846976 + 870719842427188907)⟩,
  ⟨19,5,[0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f08080f0f08080, 0xf0f0f0f000000000],hints (((((((((((((((((381518770676803998 * 1152921504606846976 + 205878786320405756) * 1152921504606846976 + 257812409963897102) * 1152921504606846976 + 534377316790289299) * 1152921504606846976 + 1070260944590923450) * 1152921504606846976 + 564403462875144422) * 1152921504606846976 + 493357243989077083) * 1152921504606846976 + 482264123406350216) * 1152921504606846976 + 511697959608771249) * 1152921504606846976 + 466861590840312982) * 1152921504606846976 + 191495565738636675) * 1152921504606846976 + 492597999792154843) * 1152921504606846976 + 493919687136525396) * 1152921504606846976 + 1071386849874745058) * 1152921504606846976 + 870648934391619760) * 1152921504606846976 + 378374251944590933) * 1152921504606846976 + 47384783261304202) * 1152921504606846976 + 889757136119227056)⟩,
  ⟨19,5,[0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f08080f0f08080, 0xf0f0f0f000000000],hints ((((((((1884071766747 * 1152921504606846976 + 480598365733295354) * 1152921504606846976 + 674882388830565535) * 1152921504606846976 + 358996819790269461) * 1152921504606846976 + 482253666609993099) * 1152921504606846976 + 277511308432724127) * 1152921504606846976 + 397070717232064987) * 1152921504606846976 + 914327720216428672) * 1152921504606846976 + 293836259854758064)⟩,
  ⟨19,5,[0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f080808080],hints (((((((((((((((((381518770676803998 * 1152921504606846976 + 205878786320405756) * 1152921504606846976 + 329870004001825042) * 1152921504606846976 + 534377316790289555) * 1152921504606846976 + 1070260944590939834) * 1152921504606846976 + 564403462875144422) * 1152921504606846976 + 493357243989077083) * 1152921504606846976 + 482264123406350216) * 1152921504606846976 + 511697959608771249) * 1152921504606846976 + 466861590840312982) * 1152921504606846976 + 191495565738636675) * 1152921504606846976 + 492281340442306779) * 1152921504606846976 + 493919687136525398) * 1152921504606846976 + 62580535491237602) * 1152921504606846976 + 870648934391619760) * 1152921504606846976 + 378374251944590933) * 1152921504606846976 + 47384806883624330) * 1152921504606846976 + 889758648216150704)⟩,
  ⟨19,5,[0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000, 0xf0f0f0f080808080],hints ((((((((1471753272414 * 1152921504606846976 + 191777627150390523) * 1152921504606846976 + 873146325556912287) * 1152921504606846976 + 358750503419455388) * 1152921504606846976 + 914609753555669216) * 1152921504606846976 + 510361482916614303) * 1152921504606846976 + 376787141555404062) * 1152921504606846976 + 626097287152177280) * 1152921504606846976 + 293836259854758064)⟩,
  ⟨19,6,[0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xe0e0e0e0e0e0e0e0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints ((((((((((((((((((((((((11643028890283 * 1152921504606846976 + 374860583156361941) * 1152921504606846976 + 189008968822732075) * 1152921504606846976 + 873609082495123103) * 1152921504606846976 + 570406517704046239) * 1152921504606846976 + 781180653343094106) * 1152921504606846976 + 776040259838891691) * 1152921504606846976 + 439982251301972548) * 1152921504606846976 + 632775203128776227) * 1152921504606846976 + 151024884124613320) * 1152921504606846976 + 61912669210459992) * 1152921504606846976 + 765143165097063715) * 1152921504606846976 + 852705029867256990) * 1152921504606846976 + 381250927925966421) * 1152921504606846976 + 191771579662329154) * 1152921504606846976 + 549344549226762408) * 1152921504606846976 + 356485020522720339) * 1152921504606846976 + 920228740060573898) * 1152921504606846976 + 780637342253534891) * 1152921504606846976 + 376787115629554261) * 1152921504606846976 + 150158912860624186) * 1152921504606846976 + 708166817429934333) * 1152921504606846976 + 358736897114354176) * 1152921504606846976 + 626092369303602418) * 1152921504606846976 + 546321511785533656)⟩,
  ⟨19,5,[0xc0c0c0c0c0c0c0c0, 0xe0e0e0e0e0e0e0e0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0a0a0f0f0a0a0, 0xf0f0f0f000000000],hints ((((((((5483227 * 1152921504606846976 + 479443323504473418) * 1152921504606846976 + 708167227596951711) * 1152921504606846976 + 358772012667873237) * 1152921504606846976 + 492112506256033083) * 1152921504606846976 + 80552313020825297) * 1152921504606846976 + 359132643923961748) * 1152921504606846976 + 1053366480152430258) * 1152921504606846976 + 546002035061383838)⟩
]
def nodesBlock1 : Array Node := #[
  ⟨19,5,[0xa0a00000a0a0, 0xc0c0c0c0c0c0c0c0, 0xe0e0e0e0e0e0e0e0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints ((((((((21 * 1152921504606846976 + 192367987413112682) * 1152921504606846976 + 564052311848867540) * 1152921504606846976 + 386035589173260563) * 1152921504606846976 + 1067722265531663706) * 1152921504606846976 + 546005952205765791) * 1152921504606846976 + 378998783122582210) * 1152921504606846976 + 1055945308441838842) * 1152921504606846976 + 708765488760306904)⟩,
  ⟨19,4,[0xc0c0c0c0c0c0c0c0, 0xe0e0e0e0e0e0e0e0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f00000a0a0],hints (((((1454489414101 * 1152921504606846976 + 44842112120415954) * 1152921504606846976 + 564334261033323699) * 1152921504606846976 + 374864465638702676) * 1152921504606846976 + 1053366456530134346) * 1152921504606846976 + 546002035061383838)⟩,
  ⟨19,5,[0xc0c0c0c0c0c0c0c0, 0xe0e0e0e0e0e0e0e0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000, 0xf0f0f0f0a0a0a0a0],hints ((((((((5614037 * 1152921504606846976 + 191254180001375962) * 1152921504606846976 + 744512261180964517) * 1152921504606846976 + 534377213763233748) * 1152921504606846976 + 1058437931492919003) * 1152921504606846976 + 906682187461508840) * 1152921504606846976 + 359132721132287507) * 1152921504606846976 + 910701462014268746) * 1152921504606846976 + 546002035061383838)⟩,
  ⟨19,5,[0xa0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xe0e0e0e0e0e0e0e0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints ((((((((21 * 1152921504606846976 + 192380082041042818) * 1152921504606846976 + 564051830409877174) * 1152921504606846976 + 385916842840210707) * 1152921504606846976 + 1074196189996311898) * 1152921504606846976 + 546002172634545311) * 1152921504606846976 + 378998783124285908) * 1152921504606846976 + 1056390060895274234) * 1152921504606846976 + 708765488760306904)⟩,
  ⟨19,4,[0xc0c0c0c0c0c0c0c0, 0xe0e0e0e0e0e0e0e0, 0xf000f000f000f000, 0xf0f00000f0f0a0a0, 0xf0f0f0f000000000],hints (((((1428803496403 * 1152921504606846976 + 1055663275138217210) * 1152921504606846976 + 708414676919209648) * 1152921504606846976 + 377125061478301267) * 1152921504606846976 + 911510152835359987) * 1152921504606846976 + 834232411213095582)⟩,
  ⟨19,5,[0xe000e000e000e0, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints (((((((((((((((((381518770676803998 * 1152921504606846976 + 205878786320404626) * 1152921504606846976 + 775268495652672171) * 1152921504606846976 + 385138814475643458) * 1152921504606846976 + 347472654729123144) * 1152921504606846976 + 332739845999567080) * 1152921504606846976 + 385310453337523221) * 1152921504606846976 + 436858218754151752) * 1152921504606846976 + 673902867530207760) * 1152921504606846976 + 36723828609057940) * 1152921504606846976 + 1053366241487553786) * 1152921504606846976 + 780229948369920171) * 1152921504606846976 + 372246544793971283) * 1152921504606846976 + 1070185135196509458) * 1152921504606846976 + 559477648363437224) * 1152921504606846976 + 40613007248533442) * 1152921504606846976 + 293389464374997120) * 1152921504606846976 + 293836188851118096)⟩,
  ⟨19,4,[0xe0000000e00000, 0xe000e000e000e0, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf0f0f0f000000000],hints (((((155614282882 * 1152921504606846976 + 16164487409247472) * 1152921504606846976 + 293841000017509394) * 1152921504606846976 + 355864970192192532) * 1152921504606846976 + 911536552912430408) * 1152921504606846976 + 330206463916093087)⟩,
  ⟨19,4,[0xe0000000e0, 0xe000e000e000e0, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf0f0f0f000000000],hints (((((155614282882 * 1152921504606846976 + 16164487409247472) * 1152921504606846976 + 294249125809764370) * 1152921504606846976 + 355864970192454677) * 1152921504606846976 + 205849646013162736) * 1152921504606846976 + 330136085239774879)⟩,
  ⟨19,3,[0xe000e0, 0xe0000000e0, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0],hints (((2152283152 * 1152921504606846976 + 108166913411220500) * 1152921504606846976 + 1013325328979928376) * 1152921504606846976 + 294107287184560855)⟩,
  ⟨19,4,[0xe000e000000000, 0xe000e000e000e0, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf0f00000f0f00000],hints (((((155278673026 * 1152921504606846976 + 10527291293639920) * 1152921504606846976 + 293839487786368018) * 1152921504606846976 + 355864970192192532) * 1152921504606846976 + 911536552918721880) * 1152921504606846976 + 330276829707491999)⟩,
  ⟨19,4,[0xe000e0, 0xe000e000e000e0, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf0f00000f0f00000],hints (((((155278673026 * 1152921504606846976 + 10527291293639920) * 1152921504606846976 + 294178756802928658) * 1152921504606846976 + 355864970192454677) * 1152921504606846976 + 205849646013162736) * 1152921504606846976 + 330136085239774879)⟩,
  ⟨19,5,[0xe0e00000e0e0, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f0f0f000000000],hints (((((((((((((((((359255799091276126 * 1152921504606846976 + 78099031760957666) * 1152921504606846976 + 775620476815398571) * 1152921504606846976 + 385182795108854275) * 1152921504606846976 + 627213701539857728) * 1152921504606846976 + 509999420044773610) * 1152921504606846976 + 385358849029024213) * 1152921504606846976 + 479443865362445632) * 1152921504606846976 + 672841695236018343) * 1152921504606846976 + 403767318499165972) * 1152921504606846976 + 1053366416528491850) * 1152921504606846976 + 780581885635846827) * 1152921504606846976 + 374543922918369235) * 1152921504606846976 + 1086894963283326202) * 1152921504606846976 + 746271696947330217) * 1152921504606846976 + 63174994440436803) * 1152921504606846976 + 584435140049966490) * 1152921504606846976 + 873182060739913385)⟩,
  ⟨19,5,[0xe0e00000e0e0, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints ((((((((1884071766739 * 1152921504606846976 + 1055380150875432658) * 1152921504606846976 + 564016777570826268) * 1152921504606846976 + 466818812664358804) * 1152921504606846976 + 1057059113737598706) * 1152921504606846976 + 708167423288491175) * 1152921504606846976 + 356696238748710613) * 1152921504606846976 + 191772104724423922) * 1152921504606846976 + 888278905146920670)⟩,
  ⟨19,5,[0xe0e0e0e0, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000],hints (((((((((((((((((359260196768622747 * 1152921504606846976 + 366598788257280386) * 1152921504606846976 + 740293858362501801) * 1152921504606846976 + 380767345726466566) * 1152921504606846976 + 51597395647694144) * 1152921504606846976 + 870288764629715156) * 1152921504606846976 + 380855060791962069) * 1152921504606846976 + 191213489252689216) * 1152921504606846976 + 1033235218541924519) * 1152921504606846976 + 410522889739570196) * 1152921504606846976 + 1053366419791742298) * 1152921504606846976 + 744551579741173417) * 1152921504606846976 + 374552907990018003) * 1152921504606846976 + 1087188556512359674) * 1152921504606846976 + 783074753357888683) * 1152921504606846976 + 108298968824231622) * 1152921504606846976 + 13604986792293810) * 1152921504606846976 + 872408004554484907)⟩,
  ⟨19,5,[0xe0e0e0e0, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints ((((((((1455750163027 * 1152921504606846976 + 1076492423395944122) * 1152921504606846976 + 560138533100666017) * 1152921504606846976 + 381250419744319380) * 1152921504606846976 + 1060169082376722314) * 1152921504606846976 + 708167423288491175) * 1152921504606846976 + 356735820361940053) * 1152921504606846976 + 212038326670001394) * 1152921504606846976 + 888280485694885620)⟩,
  ⟨19,6,[0x2020202020202020, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints ((((((((((((((((((((((((11643028890283 * 1152921504606846976 + 374860583156361941) * 1152921504606846976 + 189013366869243179) * 1152921504606846976 + 873890557471833759) * 1152921504606846976 + 588420916213528224) * 1152921504606846976 + 781180653343020376) * 1152921504606846976 + 872798590103803563) * 1152921504606846976 + 399533262601750297) * 1152921504606846976 + 1076657401700717963) * 1152921504606846976 + 888947408309412511) * 1152921504606846976 + 41312296813176787) * 1152921504606846976 + 1055933213589550424) * 1152921504606846976 + 926454773495713447) * 1152921504606846976 + 543418635433315230) * 1152921504606846976 + 212042648497321210) * 1152921504606846976 + 567641042398297759) * 1152921504606846976 + 376790875974795796) * 1152921504606846976 + 1065193336214328859) * 1152921504606846976 + 494107766695941851) * 1152921504606846976 + 494003250020891742) * 1152921504606846976 + 200221798725261195) * 1152921504606846976 + 78015392995163909) * 1152921504606846976 + 379043485158715733) * 1152921504606846976 + 47397962330690954) * 1152921504606846976 + 547482597271621287)⟩
]
def nodesBlock2 : Array Node := #[
  ⟨19,5,[0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f02020f0f02020, 0xf0f0f0f000000000],hints ((((((((1884071766740 * 1152921504606846976 + 911536555077309690) * 1152921504606846976 + 674882390023028392) * 1152921504606846976 + 358750503415843861) * 1152921504606846976 + 482264164480967946) * 1152921504606846976 + 601770481603399839) * 1152921504606846976 + 376804518841789467) * 1152921504606846976 + 911789497619477754) * 1152921504606846976 + 726181732769943217)⟩,
  ⟨19,5,[0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000, 0xf0f0f0f020202020],hints ((((((((1471753272414 * 1152921504606846976 + 191775897306174786) * 1152921504606846976 + 564052235212151455) * 1152921504606846976 + 358750503420082579) * 1152921504606846976 + 909254511305625824) * 1152921504606846976 + 510361482916614303) * 1152921504606846976 + 376826723822714139) * 1152921504606846976 + 479443876527633658) * 1152921504606846976 + 726181732769943217)⟩,
  ⟨19,5,[0x2020202020202020, 0x4040404040404040, 0xa0a0a0a0a0a0a0a0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints ((((((((20 * 1152921504606846976 + 911536552908838762) * 1152921504606846976 + 564051830409793586) * 1152921504606846976 + 493179412798636545) * 1152921504606846976 + 5716919399417178) * 1152921504606846976 + 883692636257657874) * 1152921504606846976 + 379003092752870100) * 1152921504606846976 + 621020841842959602) * 1152921504606846976 + 726181136843247774)⟩,
  ⟨19,5,[0x2020202020202020, 0x4040404040404040, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints ((((((((20 * 1152921504606846976 + 911536552908838762) * 1152921504606846976 + 564051830409793586) * 1152921504606846976 + 385093021740597761) * 1152921504606846976 + 5721867452003674) * 1152921504606846976 + 708453916129185439) * 1152921504606846976 + 379003178652805851) * 1152921504606846976 + 480574724192768128) * 1152921504606846976 + 293836257394528423)⟩,
  ⟨19,5,[0x2020202020202020, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0a0a0f0f0a0a0, 0xf0f0f0f000000000],hints ((((((((20 * 1152921504606846976 + 1057059113735448282) * 1152921504606846976 + 780576792327346847) * 1152921504606846976 + 379003026701002906) * 1152921504606846976 + 1053587278005997632) * 1152921504606846976 + 150003165372979377) * 1152921504606846976 + 40613007267080923) * 1152921504606846976 + 480574722089543395) * 1152921504606846976 + 510009039684451486)⟩,
  ⟨19,5,[0xa0a00000a0a0, 0x2020202020202020, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints ((((((((5548763 * 1152921504606846976 + 480002424131155194) * 1152921504606846976 + 746271464856049329) * 1152921504606846976 + 63174994754602133) * 1152921504606846976 + 44871253599368602) * 1152921504606846976 + 746412904468790952) * 1152921504606846976 + 356480699300620766) * 1152921504606846976 + 191209101083701312) * 1152921504606846976 + 150003164022671527)⟩,
  ⟨19,4,[0x2020202020202020, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f00000a0a0],hints (((((1454489414101 * 1152921504606846976 + 44842112120415954) * 1152921504606846976 + 558728400987240476) * 1152921504606846976 + 381284399159977942) * 1152921504606846976 + 47126897297626418) * 1152921504606846976 + 744196220307717278)⟩,
  ⟨19,5,[0x2020202020202020, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000, 0xf0f0f0f0a0a0a0a0],hints ((((((((21 * 1152921504606846976 + 479444973891777842) * 1152921504606846976 + 692264157029678759) * 1152921504606846976 + 358763886537582746) * 1152921504606846976 + 1053565244815381899) * 1152921504606846976 + 494352594960994993) * 1152921504606846976 + 40613007265901019) * 1152921504606846976 + 501146115405158282) * 1152921504606846976 + 744196220307717278)⟩,
  ⟨19,5,[0xa0a0a0a0, 0x2020202020202020, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints ((((((((5548766 * 1152921504606846976 + 191772054428185850) * 1152921504606846976 + 620065122173408945) * 1152921504606846976 + 63174994754602133) * 1152921504606846976 + 44854760977381202) * 1152921504606846976 + 747081407538478760) * 1152921504606846976 + 356481145913977414) * 1152921504606846976 + 767669853387124800) * 1152921504606846976 + 150003164022671015)⟩,
  ⟨19,4,[0x2020202020202020, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f0a0a0, 0xf0f0f0f000000000],hints (((((1428803496403 * 1152921504606846976 + 1055663275138217210) * 1152921504606846976 + 704253713259696136) * 1152921504606846976 + 376829178044229588) * 1152921504606846976 + 912914792917399266) * 1152921504606846976 + 708167423288753310)⟩,
  ⟨19,6,[0x4040404040404040, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints ((((((((((((((((((((((((11643028890283 * 1152921504606846976 + 374860583156361941) * 1152921504606846976 + 189017215159940395) * 1152921504606846976 + 874136848076455583) * 1152921504606846976 + 604183514909324961) * 1152921504606846976 + 637065465267086682) * 1152921504606846976 + 548856091853543083) * 1152921504606846976 + 356748902614214555) * 1152921504606846976 + 212039401506247923) * 1152921504606846976 + 888275538022111391) * 1152921504606846976 + 359216292773701587) * 1152921504606846976 + 914351310370420059) * 1152921504606846976 + 944469173213157040) * 1152921504606846976 + 543459721090480030) * 1152921504606846976 + 206136621793252600) * 1152921504606846976 + 294434372705140383) * 1152921504606846976 + 561438469286920729) * 1152921504606846976 + 44560097137591834) * 1152921504606846976 + 780639953593596075) * 1152921504606846976 + 385917272086162005) * 1152921504606846976 + 160573486764037451) * 1152921504606846976 + 80553615590248716) * 1152921504606846976 + 358737764697780563) * 1152921504606846976 + 1053671004111131890) * 1152921504606846976 + 547482596063666343)⟩,
  ⟨19,5,[0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f04040f0f04040, 0xf0f0f0f000000000],hints ((((((((1469823955157 * 1152921504606846976 + 192367987585094906) * 1152921504606846976 + 674882388817432735) * 1152921504606846976 + 358781315514837269) * 1152921504606846976 + 476905662453507315) * 1152921504606846976 + 276173015450734750) * 1152921504606846976 + 397070717232363412) * 1152921504606846976 + 1055906278058659968) * 1152921504606846976 + 293836237261847728)⟩,
  ⟨19,4,[0xf0f04040, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000],hints (((((358768121371693461 * 1152921504606846976 + 157652438940320289) * 1152921504606846976 + 77909815548001960) * 1152921504606846976 + 18050940902091157) * 1152921504606846976 + 190932564264482184) * 1152921504606846976 + 870710977614663335)⟩,
  ⟨19,5,[0x404000004040, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints ((((((((20 * 1152921504606846976 + 911536555056322410) * 1152921504606846976 + 564051830409870500) * 1152921504606846976 + 385752900483655571) * 1152921504606846976 + 909538178749871834) * 1152921504606846976 + 780823915755741200) * 1152921504606846976 + 358775111048702997) * 1152921504606846976 + 494082827875947842) * 1152921504606846976 + 564368278499708583)⟩,
  ⟨19,5,[0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000, 0xf0f0f0f040404040],hints ((((((((1884066589269 * 1152921504606846976 + 199377376359650554) * 1152921504606846976 + 726497862672572575) * 1152921504606846976 + 358750503419456604) * 1152921504606846976 + 909251283513894130) * 1152921504606846976 + 600432188621410462) * 1152921504606846976 + 397391327883832030) * 1152921504606846976 + 624689912268624000) * 1152921504606846976 + 293836237261847728)⟩,
  ⟨19,4,[0xf0f000004040, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f0f0f000000000],hints (((((358768310349599125 * 1152921504606846976 + 440242298966622753) * 1152921504606846976 + 77909952986955432) * 1152921504606846976 + 18050940566546837) * 1152921504606846976 + 479162940416193928) * 1152921504606846976 + 510351264022875815)⟩
]
def nodesBlock3 : Array Node := #[
  ⟨19,5,[0x40404040, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints ((((((((20 * 1152921504606846976 + 911536552908838762) * 1152921504606846976 + 564051830409814064) * 1152921504606846976 + 518610208412706707) * 1152921504606846976 + 909538178749916890) * 1152921504606846976 + 870895221106548752) * 1152921504606846976 + 358775111048702997) * 1152921504606846976 + 480570953104823618) * 1152921504606846976 + 564368278499708583)⟩,
  ⟨19,6,[0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0a0a0f0f0a0a0, 0xf0f0f0f000000000],hints ((((((((((((((((((((((((13429749093035 * 1152921504606846976 + 385376312365263573) * 1152921504606846976 + 504523733535995187) * 1152921504606846976 + 890425988422129353) * 1152921504606846976 + 442098106827581407) * 1152921504606846976 + 909577775104329715) * 1152921504606846976 + 816254020504124584) * 1152921504606846976 + 358903954014152661) * 1152921504606846976 + 55543100647012051) * 1152921504606846976 + 888420410236681969) * 1152921504606846976 + 358732531416381126) * 1152921504606846976 + 64833436829725938) * 1152921504606846976 + 885215801951992990) * 1152921504606846976 + 448804575803647896) * 1152921504606846976 + 621047857187451403) * 1152921504606846976 + 275791691074064402) * 1152921504606846976 + 399268014011460115) * 1152921504606846976 + 909532750001555402) * 1152921504606846976 + 780652804135828651) * 1152921504606846976 + 385921471692616020) * 1152921504606846976 + 1064108162355599091) * 1152921504606846976 + 78968882714197726) * 1152921504606846976 + 379043150151269973) * 1152921504606846976 + 47410011860821386) * 1152921504606846976 + 883455277720494769)⟩,
  ⟨19,5,[0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f0a0a0f0f0a0a0, 0xf0f0c0c0f0f0c0c0, 0xf0f0f0f000000000],hints ((((((((5450133 * 1152921504606846976 + 504496251067864970) * 1152921504606846976 + 744550263051115167) * 1152921504606846976 + 358750099692857299) * 1152921504606846976 + 1056188349929026802) * 1152921504606846976 + 546392361839972511) * 1152921504606846976 + 379003482036611806) * 1152921504606846976 + 206723815758787834) * 1152921504606846976 + 726181827847498959)⟩,
  ⟨19,5,[0xa0a0a0a0a0a0a0a0, 0xc0c08080c0c08080, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints ((((((((1428721347283 * 1152921504606846976 + 1055380150875203258) * 1152921504606846976 + 560138525186810609) * 1152921504606846976 + 498426367983232984) * 1152921504606846976 + 480515902361212483) * 1152921504606846976 + 889647783697267870) * 1152921504606846976 + 397070717232360667) * 1152921504606846976 + 626009161811527042) * 1152921504606846976 + 891091524607903920)⟩,
  ⟨19,4,[0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf0c0f080f0c0f080, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints (((((374530728862394717 * 1152921504606846976 + 765418047248396672) * 1152921504606846976 + 870719843233020593) * 1152921504606846976 + 40613007265901275) * 1152921504606846976 + 480574734930215040) * 1152921504606846976 + 293836259720027312)⟩,
  ⟨19,4,[0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f0c0c08080],hints (((((374530728862394717 * 1152921504606846976 + 765418047248396672) * 1152921504606846976 + 870719843246389937) * 1152921504606846976 + 40613007265606107) * 1152921504606846976 + 480574734930215040) * 1152921504606846976 + 293836259854768304)⟩,
  ⟨19,5,[0x3030202030302020, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints ((((((((1428721347155 * 1152921504606846976 + 1055380150875203258) * 1152921504606846976 + 560138525186734108) * 1152921504606846976 + 381332777671600084) * 1152921504606846976 + 1057059113737557730) * 1152921504606846976 + 708167423288414216) * 1152921504606846976 + 376830907189668574) * 1152921504606846976 + 191817132087608570) * 1152921504606846976 + 726145952512851111)⟩,
  ⟨19,5,[0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000, 0xf0f0f0f0f0f0a0a0],hints ((((((((21 * 1152921504606846976 + 480570875788814044) * 1152921504606846976 + 5921922292465317) * 1152921504606846976 + 534377213763233750) * 1152921504606846976 + 188675286199060274) * 1152921504606846976 + 546002177734747154) * 1152921504606846976 + 378998697375708443) * 1152921504606846976 + 494961890750743802) * 1152921504606846976 + 726181821666376881)⟩,
  ⟨19,5,[0xf0f0a0a0, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints ((((((((1488935496403 * 1152921504606846976 + 1057070650002908858) * 1152921504606846976 + 560138525181820065) * 1152921504606846976 + 466817607707928469) * 1152921504606846976 + 624727297841030883) * 1152921504606846976 + 510009039684451505) * 1152921504606846976 + 356564708864862816) * 1152921504606846976 + 67923061284439282) * 1152921504606846976 + 888276843560287476)⟩,
  ⟨19,6,[0xa0a00000a0a0, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints ((((((((((((((((((((((((11643029653675 * 1152921504606846976 + 385411496736500437) * 1152921504606846976 + 189013916625057067) * 1152921504606846976 + 873925741843922591) * 1152921504606846976 + 590672716027442848) * 1152921504606846976 + 926140266348930392) * 1152921504606846976 + 872798590103803563) * 1152921504606846976 + 356748902614206233) * 1152921504606846976 + 1031058455473591539) * 1152921504606846976 + 77627605058675359) * 1152921504606846976 + 41312296811571155) * 1152921504606846976 + 927299197964301659) * 1152921504606846976 + 1034541171934582468) * 1152921504606846976 + 442102341734183189) * 1152921504606846976 + 191821519396922690) * 1152921504606846976 + 728397818785779880) * 1152921504606846976 + 500595807990885442) * 1152921504606846976 + 909251274936620571) * 1152921504606846976 + 169004374753582281) * 1152921504606846976 + 174247676477583966) * 1152921504606846976 + 199658849096561916) * 1152921504606846976 + 114008945646714565) * 1152921504606846976 + 379041896004006358) * 1152921504606846976 + 193977660623062410) * 1152921504606846976 + 889615155377585319)⟩,
  ⟨19,5,[0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xc0c0e0e0c0c0e0e0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints ((((((((1454575037011 * 1152921504606846976 + 1055380150875231954) * 1152921504606846976 + 564477953995264711) * 1152921504606846976 + 381615467184240275) * 1152921504606846976 + 910947202863076682) * 1152921504606846976 + 546002035061383838) * 1152921504606846976 + 376804518841789019) * 1152921504606846976 + 911785041462982018) * 1152921504606846976 + 708452608982727902)⟩,
  ⟨19,5,[0xa0a0a0a0a0a0a0a0, 0xc0c04040c0c04040, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints ((((((((1428721347155 * 1152921504606846976 + 1055380150875203258) * 1152921504606846976 + 564016777570893041) * 1152921504606846976 + 381250419744319381) * 1152921504606846976 + 494082827876242763) * 1152921504606846976 + 888627450462691998) * 1152921504606846976 + 397070717232163419) * 1152921504606846976 + 624038836974551104) * 1152921504606846976 + 149686437167582887)⟩,
  ⟨19,5,[0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f00000a0a0],hints (((((((((((((((((381518795188316564 * 1152921504606846976 + 926425589641549124) * 1152921504606846976 + 348195495580876563) * 1152921504606846976 + 358776513892435155) * 1152921504606846976 + 1070259299618469586) * 1152921504606846976 + 564297909758877854) * 1152921504606846976 + 493356625513360475) * 1152921504606846976 + 482253678045885744) * 1152921504606846976 + 511697959603752094) * 1152921504606846976 + 356523399969735830) * 1152921504606846976 + 191495513125283571) * 1152921504606846976 + 492281203003352283) * 1152921504606846976 + 494121997278194068) * 1152921504606846976 + 927271663946065203) * 1152921504606846976 + 906677731410656990) * 1152921504606846976 + 379043150151269973) * 1152921504606846976 + 47410011860833674) * 1152921504606846976 + 883525646464672419)⟩,
  ⟨19,5,[0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000, 0xf0f0f0f00000a0a0],hints ((((((((1471753272414 * 1152921504606846976 + 191775897352312130) * 1152921504606846976 + 564052235212151455) * 1152921504606846976 + 358781315515459475) * 1152921504606846976 + 914599237328167136) * 1152921504606846976 + 510360177246556318) * 1152921504606846976 + 376787142328663326) * 1152921504606846976 + 350811461398467834) * 1152921504606846976 + 726181821666376881)⟩,
  ⟨19,5,[0xa0a00000a0a0, 0xc0c00000c0c0, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f0f0f000000000],hints ((((((((5220701 * 1152921504606846976 + 765345930359718112) * 1152921504606846976 + 708474449670813355) * 1152921504606846976 + 83480689446422299) * 1152921504606846976 + 7974443589211458) * 1152921504606846976 + 564368275915494067) * 1152921504606846976 + 383551517393889683) * 1152921504606846976 + 1056181698244494600) * 1152921504606846976 + 510290456947822249)⟩,
  ⟨19,5,[0xa0a00000a0a0, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f0f0f000000000, 0xf0f0f0f0f0f00000],hints ((((((((5614163 * 1152921504606846976 + 1056495605421815682) * 1152921504606846976 + 559433463082073299) * 1152921504606846976 + 516357203609003925) * 1152921504606846976 + 335921874914330331) * 1152921504606846976 + 546037836703415473) * 1152921504606846976 + 356564502675237464) * 1152921504606846976 + 494121310761944314) * 1152921504606846976 + 726147255769583271)⟩
]
def nodesBlock4 : Array Node := #[
  ⟨19,6,[0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000, 0xf0f0f0f0a0a0a0a0],hints ((((((((((((((((((((((((13907551696581 * 1152921504606846976 + 385801796758057246) * 1152921504606846976 + 211990499008726346) * 1152921504606846976 + 746307156223282417) * 1152921504606846976 + 494108786359052832) * 1152921504606846976 + 335605795274749970) * 1152921504606846976 + 564370888632173727) * 1152921504606846976 + 541396548844600147) * 1152921504606846976 + 1070536918871701202) * 1152921504606846976 + 744305222697696937) * 1152921504606846976 + 358815374907477907) * 1152921504606846976 + 909273196449314186) * 1152921504606846976 + 547303796446677222) * 1152921504606846976 + 185660496308807573) * 1152921504606846976 + 152110545708578122) * 1152921504606846976 + 744166052320595986) * 1152921504606846976 + 399268014011460115) * 1152921504606846976 + 909532720960010147) * 1152921504606846976 + 95961212435425482) * 1152921504606846976 + 550298452714208349) * 1152921504606846976 + 358410736070760331) * 1152921504606846976 + 942706528429620980) * 1152921504606846976 + 379043339129830997) * 1152921504606846976 + 47422106488747402) * 1152921504606846976 + 883560830842528433)⟩,
  ⟨19,5,[0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f0a0a0a0a0, 0xf0f0f0f0c0c0c0c0],hints ((((((((7187157 * 1152921504606846976 + 488731997631419722) * 1152921504606846976 + 783110204556660895) * 1152921504606846976 + 379003026717780122) * 1152921504606846976 + 1053647869257344347) * 1152921504606846976 + 924696654686802079) * 1152921504606846976 + 379003543390895252) * 1152921504606846976 + 1055941462470595834) * 1152921504606846976 + 726181830806067430)⟩,
  ⟨19,5,[0xa0a0a0a0a0a0a0a0, 0xc0c0c0c080808080, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints ((((((((1428721347155 * 1152921504606846976 + 1055380150875203258) * 1152921504606846976 + 564689069880391708) * 1152921504606846976 + 381332777671600085) * 1152921504606846976 + 480587971969061554) * 1152921504606846976 + 745532598037331102) * 1152921504606846976 + 397119095827868251) * 1152921504606846976 + 624038836974552450) * 1152921504606846976 + 890317468421949104)⟩,
  ⟨19,4,[0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf0c0f0c0f080f080, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints (((((374530728828840285 * 1152921504606846976 + 765418047248397706) * 1152921504606846976 + 963325090533036721) * 1152921504606846976 + 40613007265901979) * 1152921504606846976 + 481982099076321408) * 1152921504606846976 + 293836259720016048)⟩,
  ⟨19,4,[0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f0c0c0f0f08080, 0xf0f0f0f000000000],hints (((((374530728828840285 * 1152921504606846976 + 765418047248397707) * 1152921504606846976 + 350835541210649265) * 1152921504606846976 + 40613007265901979) * 1152921504606846976 + 481977149126512768) * 1152921504606846976 + 293836259854757040)⟩,
  ⟨19,5,[0x3030303020202020, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints ((((((((1428721347155 * 1152921504606846976 + 1055380150875203258) * 1152921504606846976 + 560138525186734108) * 1152921504606846976 + 381332777671600084) * 1152921504606846976 + 1057059113737557898) * 1152921504606846976 + 708167423288414216) * 1152921504606846976 + 376830907189668574) * 1152921504606846976 + 191817132087608570) * 1152921504606846976 + 726145952512862375)⟩,
  ⟨19,5,[0xf0f00000a0a0, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints ((((((((1454608591443 * 1152921504606846976 + 1055380150875231954) * 1152921504606846976 + 564016785489672220) * 1152921504606846976 + 381249214787889050) * 1152921504606846976 + 636254082617218802) * 1152921504606846976 + 744196220307717297) * 1152921504606846976 + 356564296550889182) * 1152921504606846976 + 191772051037127922) * 1152921504606846976 + 888276843560298718)⟩,
  ⟨19,6,[0xa0a0a0a0, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints ((((((((((((((((((((((((11639808451243 * 1152921504606846976 + 386118526031932117) * 1152921504606846976 + 189015016136684891) * 1152921504606846976 + 873996316746530463) * 1152921504606846976 + 595176315654583969) * 1152921504606846976 + 60604712963663192) * 1152921504606846976 + 872790068888688299) * 1152921504606846976 + 356643349497939737) * 1152921504606846976 + 1076657401700717811) * 1152921504606846976 + 888275537985364639) * 1152921504606846976 + 41312296811571155) * 1152921504606846976 + 919686136493549475) * 1152921504606846976 + 60071506998580473) * 1152921504606846976 + 381299581318118677) * 1152921504606846976 + 191821519397012802) * 1152921504606846976 + 729171874971734184) * 1152921504606846976 + 550135403975846979) * 1152921504606846976 + 188675358179661339) * 1152921504606846976 + 187862923315349706) * 1152921504606846976 + 442238225368429195) * 1152921504606846976 + 775838126423274748) * 1152921504606846976 + 150037742934113989) * 1152921504606846976 + 379042033442959766) * 1152921504606846976 + 193985906960270730) * 1152921504606846976 + 889579902286031015)⟩,
  ⟨19,5,[0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xc0c0c0c0e0e0e0e0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints ((((((((1454575757907 * 1152921504606846976 + 1057070650002908858) * 1152921504606846976 + 564476510886253297) * 1152921504606846976 + 381615467553340435) * 1152921504606846976 + 910947202863076682) * 1152921504606846976 + 546002035061383838) * 1152921504606846976 + 376804733590153822) * 1152921504606846976 + 191209101083702658) * 1152921504606846976 + 708454120811216088)⟩,
  ⟨19,5,[0xa0a0a0a0a0a0a0a0, 0xc0c0c0c040404040, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints ((((((((1428721347155 * 1152921504606846976 + 1055380150875203258) * 1152921504606846976 + 564020557142113441) * 1152921504606846976 + 381250419744319381) * 1152921504606846976 + 494082827876242763) * 1152921504606846976 + 888627450462691998) * 1152921504606846976 + 388063517977619035) * 1152921504606846976 + 624038836974551104) * 1152921504606846976 + 149686437167320743)⟩,
  ⟨19,5,[0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f0a0a0, 0xf0f0f0f000000000],hints (((((((((((((((((381285674211715806 * 1152921504606846976 + 190931475496604924) * 1152921504606846976 + 293841206312034576) * 1152921504606846976 + 541132673281967125) * 1152921504606846976 + 44847601089053946) * 1152921504606846976 + 726533665385636070) * 1152921504606846976 + 374011853863757716) * 1152921504606846976 + 909261663076214664) * 1152921504606846976 + 509973923900023473) * 1152921504606846976 + 356523399969735830) * 1152921504606846976 + 191495513125283554) * 1152921504606846976 + 690404539675568294) * 1152921504606846976 + 374767811059924052) * 1152921504606846976 + 1070823899917129443) * 1152921504606846976 + 942706528429620956) * 1152921504606846976 + 379043132971400789) * 1152921504606846976 + 47408912349222282) * 1152921504606846976 + 883631199580414624)⟩,
  ⟨19,5,[0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f00000f0f0a0a0, 0xf0f0f0f000000000],hints ((((((((1884071766740 * 1152921504606846976 + 911536555077309690) * 1152921504606846976 + 783074334196186792) * 1152921504606846976 + 358750503415843861) * 1152921504606846976 + 476916087310193906) * 1152921504606846976 + 601769175933341854) * 1152921504606846976 + 388063517977323995) * 1152921504606846976 + 933505402024084730) * 1152921504606846976 + 726181821666376881)⟩,
  ⟨19,5,[0xa0a0a0a0, 0xc0c0c0c0, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000],hints ((((((((5220506 * 1152921504606846976 + 1053587301623595392) * 1152921504606846976 + 1068763794249984169) * 1152921504606846976 + 128604646651005981) * 1152921504606846976 + 878295095196693826) * 1152921504606846976 + 564368275920737974) * 1152921504606846976 + 388063921670662547) * 1152921504606846976 + 1056181701419664672) * 1152921504606846976 + 870578424185195691)⟩,
  ⟨19,5,[0xa0a0a0a0, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f0f0f00000],hints ((((((((5548627 * 1152921504606846976 + 1057058555375232722) * 1152921504606846976 + 560138525181820111) * 1152921504606846976 + 466817607707928469) * 1152921504606846976 + 624709705654945443) * 1152921504606846976 + 582066633722379441) * 1152921504606846976 + 356564511298005720) * 1152921504606846976 + 638224427832214778) * 1152921504606846976 + 726147255769583271)⟩,
  ⟨19,6,[0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0c0c0f0f0c0c0, 0xf0f0f0f000000000],hints ((((((((((((((((((((((((13423294074055 * 1152921504606846976 + 228304066145530328) * 1152921504606846976 + 480035413689021785) * 1152921504606846976 + 656238796121920199) * 1152921504606846976 + 442414147701090271) * 1152921504606846976 + 1053692963180185595) * 1152921504606846976 + 816254020501765791) * 1152921504606846976 + 379170229797759507) * 1152921504606846976 + 1064344469377775314) * 1152921504606846976 + 744551512900452009) * 1152921504606846976 + 358948037759678170) * 1152921504606846976 + 791038876845979259) * 1152921504606846976 + 78964616479456452) * 1152921504606846976 + 381299219835105560) * 1152921504606846976 + 636810377514841338) * 1152921504606846976 + 566304036244766367) * 1152921504606846976 + 377015179689700062) * 1152921504606846976 + 638224348400481665) * 1152921504606846976 + 636707900225310407) * 1152921504606846976 + 376825469843255572) * 1152921504606846976 + 1071386852021507826) * 1152921504606846976 + 708519199361474736) * 1152921504606846976 + 378374251944585685) * 1152921504606846976 + 47103311505684090) * 1152921504606846976 + 708452266595688112)⟩,
  ⟨19,5,[0xa0a08080a0a08080, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints ((((((((1454575037011 * 1152921504606846976 + 1055380150875231954) * 1152921504606846976 + 560138525186734108) * 1152921504606846976 + 381332777671600086) * 1152921504606846976 + 48252801520408290) * 1152921504606846976 + 739154409738559665) * 1152921504606846976 + 489416499827419870) * 1152921504606846976 + 191794592222934738) * 1152921504606846976 + 564016371433033383)⟩
]
def nodesBlock5 : Array Node := #[
  ⟨19,5,[0x5050404050504040, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints ((((((((1428721347155 * 1152921504606846976 + 1055380150875203258) * 1152921504606846976 + 564016777570892961) * 1152921504606846976 + 381250419744319382) * 1152921504606846976 + 48252801520408458) * 1152921504606846976 + 739154409738473480) * 1152921504606846976 + 356559899306866389) * 1152921504606846976 + 212043825320424770) * 1152921504606846976 + 564684873155563175)⟩,
  ⟨19,5,[0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f0c0c0f0f0c0c0, 0xf0f0f0f000000000, 0xf0f0f0f0f0f00000],hints ((((((((5614165 * 1152921504606846976 + 212043776035591899) * 1152921504606846976 + 59649153583365851) * 1152921504606846976 + 541132613303412693) * 1152921504606846976 + 202473647203235771) * 1152921504606846976 + 275785988699934879) * 1152921504606846976 + 376795748518573339) * 1152921504606846976 + 479448822027321472) * 1152921504606846976 + 293836191132634800)⟩,
  ⟨19,5,[0xf0f0c0c0, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000],hints (((((((((((((((((359264594815035803 * 1152921504606846976 + 366881912495141250) * 1152921504606846976 + 740293435979308713) * 1152921504606846976 + 380766701481372166) * 1152921504606846976 + 51597395647694144) * 1152921504606846976 + 870288764610054366) * 1152921504606846976 + 380855145431509461) * 1152921504606846976 + 191213489166681408) * 1152921504606846976 + 294433773420630183) * 1152921504606846976 + 397038479136525332) * 1152921504606846976 + 1055058011988624730) * 1152921504606846976 + 744551569660950185) * 1152921504606846976 + 381307663185979925) * 1152921504606846976 + 78619100987426114) * 1152921504606846976 + 780224406914677931) * 1152921504606846976 + 108298969646741190) * 1152921504606846976 + 13604986792293762) * 1152921504606846976 + 872408004554481835)⟩,
  ⟨19,5,[0xf0f0c0c0, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints ((((((((1428722068051 * 1152921504606846976 + 1055380150875231954) * 1152921504606846976 + 560138533113516751) * 1152921504606846976 + 381496796248287188) * 1152921504606846976 + 1060167982865094386) * 1152921504606846976 + 703125612719333543) * 1152921504606846976 + 376826096824663125) * 1152921504606846976 + 212043187517781234) * 1152921504606846976 + 547730948247080624)⟩,
  ⟨19,6,[0xc0c00000c0c0, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints ((((((((((((((((((((((((18240098656939 * 1152921504606846976 + 374860583159507669) * 1152921504606846976 + 477244842532582699) * 1152921504606846976 + 873960926216011423) * 1152921504606846976 + 592924517048858272) * 1152921504606846976 + 1069411106804266330) * 1152921504606846976 + 783430307149338283) * 1152921504606846976 + 467087515029997337) * 1152921504606846976 + 1064933847309686394) * 1152921504606846976 + 726502260715929256) * 1152921504606846976 + 379214132799583956) * 1152921504606846976 + 1077580403215021786) * 1152921504606846976 + 708589568127225566) * 1152921504606846976 + 178681346622630360) * 1152921504606846976 + 623559053394249024) * 1152921504606846976 + 294433773420630183) * 1152921504606846976 + 397272657938590164) * 1152921504606846976 + 1069978385111516698) * 1152921504606846976 + 780643183409027243) * 1152921504606846976 + 385917272086163925) * 1152921504606846976 + 199698431515198788) * 1152921504606846976 + 131706066468688069) * 1152921504606846976 + 358737146691924313) * 1152921504606846976 + 1053338366388708738) * 1152921504606846976 + 868361801771868336)⟩,
  ⟨19,5,[0xa0a0a0a0a0a0a0a0, 0xa0a0e0e0a0a0e0e0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints ((((((((1428721347283 * 1152921504606846976 + 1055380150875203258) * 1152921504606846976 + 564016777570826268) * 1152921504606846976 + 466818812664358805) * 1152921504606846976 + 462276129888957770) * 1152921504606846976 + 744191890988285105) * 1152921504606846976 + 356696203585235412) * 1152921504606846976 + 1056789733371970810) * 1152921504606846976 + 708132170073202855)⟩,
  ⟨19,4,[0xa000e000a000e0, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints (((((374530728857767637 * 1152921504606846976 + 437422039909867648) * 1152921504606846976 + 1034527194196843024) * 1152921504606846976 + 36109319339490132) * 1152921504606846976 + 765418104045565168) * 1152921504606846976 + 329819563329928720)⟩,
  ⟨19,4,[0xa0a0e0e0, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000],hints (((((358750503415187225 * 1152921504606846976 + 1022343567395455521) * 1152921504606846976 + 79528164738809511) * 1152921504606846976 + 112802454937384660) * 1152921504606846976 + 911503640574448880) * 1152921504606846976 + 870253580240637611)⟩,
  ⟨19,5,[0xa0a02020a0a02020, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints ((((((((1428721347155 * 1152921504606846976 + 1055380150875203258) * 1152921504606846976 + 560138525186734108) * 1152921504606846976 + 381332777671600084) * 1152921504606846976 + 1057059113737557898) * 1152921504606846976 + 708167423288414216) * 1152921504606846976 + 376830907189668574) * 1152921504606846976 + 191817132087608570) * 1152921504606846976 + 728223133717848231)⟩,
  ⟨19,5,[0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000, 0xf0f0f0f00000c0c0],hints ((((((((1884073278549 * 1152921504606846976 + 191779751011726586) * 1152921504606846976 + 726497862672572575) * 1152921504606846976 + 358750503419455388) * 1152921504606846976 + 923050704198496480) * 1152921504606846976 + 511702151357878431) * 1152921504606846976 + 397052678453308126) * 1152921504606846976 + 623559075296866432) * 1152921504606846976 + 293836191132634800)⟩,
  ⟨19,5,[0xc0c0, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints ((((((((20 * 1152921504606846976 + 911536655988053866) * 1152921504606846976 + 564051830409814064) * 1152921504606846976 + 518824593770133909) * 1152921504606846976 + 44847051349649114) * 1152921504606846976 + 708449662366654480) * 1152921504606846976 + 358772158779075605) * 1152921504606846976 + 480570875792979266) * 1152921504606846976 + 564016364721884848)⟩,
  ⟨19,6,[0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000, 0xf0f0f0f0c0c0c0c0],hints ((((((((((((((((((((((((13632686347973 * 1152921504606846976 + 385929571110007061) * 1152921504606846976 + 191793492669515298) * 1152921504606846976 + 745462937429038833) * 1152921504606846976 + 255514762729007072) * 1152921504606846976 + 477192656381446170) * 1152921504606846976 + 726183814660753055) * 1152921504606846976 + 541185494151707667) * 1152921504606846976 + 1057026119991686866) * 1152921504606846976 + 744305222831914665) * 1152921504606846976 + 358895467141214547) * 1152921504606846976 + 919672941250897715) * 1152921504606846976 + 60920396796744442) * 1152921504606846976 + 543719446352804254) * 1152921504606846976 + 208981057298453754) * 1152921504606846976 + 567078092436749983) * 1152921504606846976 + 396810863054629332) * 1152921504606846976 + 1064630360352687419) * 1152921504606846976 + 59935776215787602) * 1152921504606846976 + 550175099992652884) * 1152921504606846976 + 1071386852022228706) * 1152921504606846976 + 708519199361474736) * 1152921504606846976 + 378374251944585685) * 1152921504606846976 + 47103335128004402) * 1152921504606846976 + 708453778424188080)⟩,
  ⟨19,5,[0xa0a0a0a080808080, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints ((((((((1454575757907 * 1152921504606846976 + 1057070650002908858) * 1152921504606846976 + 560138525186734108) * 1152921504606846976 + 381332777671600086) * 1152921504606846976 + 48265445904127714) * 1152921504606846976 + 739154409738559665) * 1152921504606846976 + 487164700013112030) * 1152921504606846976 + 191817132257441666) * 1152921504606846976 + 564016374385823399)⟩,
  ⟨19,5,[0x5050505040404040, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints ((((((((1428721347155 * 1152921504606846976 + 1055380150875203258) * 1152921504606846976 + 564016777570892961) * 1152921504606846976 + 381250419744319382) * 1152921504606846976 + 48252801520408290) * 1152921504606846976 + 739154409738473480) * 1152921504606846976 + 356559899306866389) * 1152921504606846976 + 212043825320424770) * 1152921504606846976 + 564684876242570919)⟩,
  ⟨19,5,[0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f0c0c0c0c0, 0xf0f0f0f0f0f00000],hints ((((((((5617365 * 1152921504606846976 + 487607750318036699) * 1152921504606846976 + 77663689531801256) * 1152921504606846976 + 379003027558574037) * 1152921504606846976 + 497179070850262827) * 1152921504606846976 + 675239112826769567) * 1152921504606846976 + 376804544611887572) * 1152921504606846976 + 1058437960489922688) * 1152921504606846976 + 293836191132634800)⟩,
  ⟨19,5,[0xf0f00000c0c0, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f0f0f000000000],hints (((((((((((((((((359268993230645662 * 1152921504606846976 + 78945105948045538) * 1152921504606846976 + 775620126104472747) * 1152921504606846976 + 385182339842320899) * 1152921504606846976 + 627213701539857728) * 1152921504606846976 + 509999420030879988) * 1152921504606846976 + 385358934037440981) * 1152921504606846976 + 479443865318393152) * 1152921504606846976 + 294433773420630183) * 1152921504606846976 + 397025113197643540) * 1152921504606846976 + 1054211937749026122) * 1152921504606846976 + 780581878508413611) * 1152921504606846976 + 385802466720262677) * 1152921504606846976 + 78900575966233922) * 1152921504606846976 + 744195612854533289) * 1152921504606846976 + 63174995648756803) * 1152921504606846976 + 584435140049966466) * 1152921504606846976 + 873182060739911849)⟩
]
def nodesBlock6 : Array Node := #[
  ⟨19,5,[0xf0f00000c0c0, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints ((((((((1428721347283 * 1152921504606846976 + 1057070650002908858) * 1152921504606846976 + 564477541675186204) * 1152921504606846976 + 467135557912504276) * 1152921504606846976 + 1057059113737598690) * 1152921504606846976 + 703125612719333543) * 1152921504606846976 + 376826097630033621) * 1152921504606846976 + 191776989194614002) * 1152921504606846976 + 548538608257158832)⟩,
  ⟨19,6,[0xc0c0c0c0, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints ((((((((((((((((((((((((11643028890378 * 1152921504606846976 + 374860583156363477) * 1152921504606846976 + 189016665404323115) * 1152921504606846976 + 874101663716949663) * 1152921504606846976 + 601931715095639713) * 1152921504606846976 + 492950277191382552) * 1152921504606846976 + 872797171413268187) * 1152921504606846976 + 518658682909145823) * 1152921504606846976 + 335892803415336754) * 1152921504606846976 + 726503772544428712) * 1152921504606846976 + 379315287869339348) * 1152921504606846976 + 1077538633584326362) * 1152921504606846976 + 709433993057357534) * 1152921504606846976 + 381299349389191637) * 1152921504606846976 + 191213489166681408) * 1152921504606846976 + 294433773420630183) * 1152921504606846976 + 397369414962588116) * 1152921504606846976 + 1076170834647385627) * 1152921504606846976 + 114116485859608745) * 1152921504606846976 + 381035629804038741) * 1152921504606846976 + 199417033847899460) * 1152921504606846976 + 203763661043486917) * 1152921504606846976 + 358737138085212508) * 1152921504606846976 + 909230325138449794) * 1152921504606846976 + 868819198609023152)⟩,
  ⟨19,5,[0xa0a0a0a0a0a0a0a0, 0xa0a0a0a0e0e0e0e0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints ((((((((1428721347155 * 1152921504606846976 + 1055380150875203258) * 1152921504606846976 + 560138533100666017) * 1152921504606846976 + 381250419744319387) * 1152921504606846976 + 488171801825211723) * 1152921504606846976 + 77660039490649265) * 1152921504606846976 + 356797358671768020) * 1152921504606846976 + 1056508258395260154) * 1152921504606846976 + 708132170075562151)⟩,
  ⟨19,4,[0xa000a000e000e0, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints (((((374530728824212508 * 1152921504606846976 + 581537239719288960) * 1152921504606846976 + 1034527194196843024) * 1152921504606846976 + 36109319339490132) * 1152921504606846976 + 765418104045565168) * 1152921504606846976 + 329819563329928720)⟩,
  ⟨19,4,[0xa0a00000e0e0, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f0f0f000000000],hints (((((358763886533282844 * 1152921504606846976 + 728472675118334497) * 1152921504606846976 + 79774452653833895) * 1152921504606846976 + 67678497397847764) * 1152921504606846976 + 911503616952116464) * 1152921504606846976 + 509964235661463209)⟩,
  ⟨19,5,[0xa0a0a0a020202020, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints ((((((((1428721347155 * 1152921504606846976 + 1055380150875203258) * 1152921504606846976 + 560138525186734108) * 1152921504606846976 + 381332777671600084) * 1152921504606846976 + 1057059113737557898) * 1152921504606846976 + 708167423288414216) * 1152921504606846976 + 376830907189668574) * 1152921504606846976 + 191817132087608570) * 1152921504606846976 + 728997189903802535)⟩,
  ⟨19,5,[0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f00000f0f0c0c0, 0xf0f0f0f000000000],hints ((((((((1885664029397 * 1152921504606846976 + 192930937538516218) * 1152921504606846976 + 674882388817432735) * 1152921504606846976 + 358781315511225372) * 1152921504606846976 + 923043480139097419) * 1152921504606846976 + 276176865083609247) * 1152921504606846976 + 376852897353705940) * 1152921504606846976 + 1058437903581606016) * 1152921504606846976 + 293836191132634800)⟩,
  ⟨19,6,[0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000, 0xf0f0f0f0f0f00000],hints ((((((((((((((((((((((((13495234836165 * 1152921504606846976 + 385917065090347349) * 1152921504606846976 + 199123440713353099) * 1152921504606846976 + 60917569792589530) * 1152921504606846976 + 444565214410385368) * 1152921504606846976 + 765418152357988059) * 1152921504606846976 + 494850908375332511) * 1152921504606846976 + 359181031933785755) * 1152921504606846976 + 361533888094926066) * 1152921504606846976 + 23587768915304134) * 1152921504606846976 + 466818537769349331) * 1152921504606846976 + 929550998811645746) * 1152921504606846976 + 548148211707100367) * 1152921504606846976 + 543595930526918558) * 1152921504606846976 + 188675276241835256) * 1152921504606846976 + 330498374492569246) * 1152921504606846976 + 376597364903032731) * 1152921504606846976 + 885079552142505275) * 1152921504606846976 + 492281330387773659) * 1152921504606846976 + 493880310808951892) * 1152921504606846976 + 1071337980663109362) * 1152921504606846976 + 709469177407873200) * 1152921504606846976 + 378374251944585685) * 1152921504606846976 + 47103247802594696) * 1152921504606846976 + 150001857144644272)⟩,
  ⟨19,5,[0xa0a0a0a0a0a00000, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints ((((((((1454575037011 * 1152921504606846976 + 1057070650002937554) * 1152921504606846976 + 560138525181753372) * 1152921504606846976 + 381249214787889044) * 1152921504606846976 + 1057059113737557730) * 1152921504606846976 + 703125612719247368) * 1152921504606846976 + 356560310819990238) * 1152921504606846976 + 191817132211304146) * 1152921504606846976 + 566092249381321895)⟩,
  ⟨19,5,[0x5050505050500000, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints ((((((((1428721353555 * 1152921504606846976 + 1055380150875203258) * 1152921504606846976 + 564016785489738913) * 1152921504606846976 + 466817607707928468) * 1152921504606846976 + 1057340588714272650) * 1152921504606846976 + 703125612719247368) * 1152921504606846976 + 356559898502379221) * 1152921504606846976 + 191791920709235690) * 1152921504606846976 + 565740404318256295)⟩,
  ⟨19,4,[0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf050f050f050f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints (((((374530730573670749 * 1152921504606846976 + 765418047248397554) * 1152921504606846976 + 656551262103641246) * 1152921504606846976 + 40613007248829211) * 1152921504606846976 + 479443877525876864) * 1152921504606846976 + 293836168542370992)⟩,
  ⟨19,5,[0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c00000, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints ((((((((1428721352467 * 1152921504606846976 + 1055380150875203258) * 1152921504606846976 + 564020565866265841) * 1152921504606846976 + 482580206403725205) * 1152921504606846976 + 480585772889183771) * 1152921504606846976 + 889647791884574366) * 1152921504606846976 + 376852897353411803) * 1152921504606846976 + 623475887021125696) * 1152921504606846976 + 149686435960651431)⟩,
  ⟨19,4,[0xc0c0c0c0c0c0c0c0, 0xe0e0e0e0e0e0a0a0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints (((((374530730624002397 * 1152921504606846976 + 765418047248397626) * 1152921504606846976 + 782336012006570151) * 1152921504606846976 + 36100534369724637) * 1152921504606846976 + 621020832290431120) * 1152921504606846976 + 330181006434843824)⟩,
  ⟨19,4,[0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf0c0f0c0f0c0f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints (((((374530730540116317 * 1152921504606846976 + 765418047248397554) * 1152921504606846976 + 963077511746006174) * 1152921504606846976 + 40613007248829851) * 1152921504606846976 + 479443887221010560) * 1152921504606846976 + 293836168542370992)⟩,
  ⟨19,5,[0x3030303030300000, 0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000],hints ((((((((1454575037011 * 1152921504606846976 + 1057070650002937554) * 1152921504606846976 + 560138525181753372) * 1152921504606846976 + 381249214787889044) * 1152921504606846976 + 1057059113737557746) * 1152921504606846976 + 703125612719247368) * 1152921504606846976 + 356560310819990238) * 1152921504606846976 + 191817132211304146) * 1152921504606846976 + 565740406333881511)⟩,
  ⟨13,5,[0xa000a000a000a0, 0xc000c000c000c0, 0xf0000000f00000, 0xf000f000000000],hints ((((((((((((((6367835 * 1152921504606846976 + 479177322120504443) * 1152921504606846976 + 890425973120784041) * 1152921504606846976 + 318200134767098267) * 1152921504606846976 + 445960514278438378) * 1152921504606846976 + 548148209147007516) * 1152921504606846976 + 311660840566600661) * 1152921504606846976 + 191789082901865994) * 1152921504606846976 + 710278421479249579) * 1152921504606846976 + 309593572930496981) * 1152921504606846976 + 479457618275497475) * 1152921504606846976 + 1032778505699844849) * 1152921504606846976 + 302477103306292819) * 1152921504606846976 + 867015126029469178) * 1152921504606846976 + 708131556038123215)⟩
]
def nodesBlock7 : Array Node := #[
  ⟨13,4,[0x20002000200020, 0xa000a000a000a0, 0xc000c000c000c0, 0xf0000000f00000, 0xf000f000000000],hints (((((10644 * 1152921504606846976 + 926427108728288888) * 1152921504606846976 + 505399965189494491) * 1152921504606846976 + 376786498400518676) * 1152921504606846976 + 1067192217303168906) * 1152921504606846976 + 747081407401685671)⟩,
  ⟨13,4,[0x40004000400040, 0xa000a000a000a0, 0xc000c000c000c0, 0xf0000000f00000, 0xf000f000000000],hints (((((10644 * 1152921504606846976 + 926427227083158770) * 1152921504606846976 + 546108274044393179) * 1152921504606846976 + 386088366771569171) * 1152921504606846976 + 934872641409234251) * 1152921504606846976 + 888668275066097319)⟩,
  ⟨13,4,[0xa0000000a00000, 0xa000a000a000a0, 0xc000c000c000c0, 0xf0000000f00000, 0xf000f000000000],hints (((((10837 * 1152921504606846976 + 494081544500720880) * 1152921504606846976 + 505399955525818075) * 1152921504606846976 + 376786497573224979) * 1152921504606846976 + 923077029227313034) * 1152921504606846976 + 746236234476155559)⟩,
  ⟨13,4,[0xa000a000a000a0, 0xc000c000c000c0, 0xf0000000f00000, 0xf000a000f000a0, 0xf000f000000000],hints (((((14037 * 1152921504606846976 + 494082770961544538) * 1152921504606846976 + 744539802794015974) * 1152921504606846976 + 356481240252068819) * 1152921504606846976 + 924458067270726971) * 1152921504606846976 + 891479651015015631)⟩,
  ⟨13,4,[0xa000a000000000, 0xa000a000a000a0, 0xc000c000c000c0, 0xf0000000f00000, 0xf000f000000000],hints (((((10837 * 1152921504606846976 + 500273993988355312) * 1152921504606846976 + 505399955525818049) * 1152921504606846976 + 376795911722107411) * 1152921504606846976 + 923077029273442186) * 1152921504606846976 + 747010293614899879)⟩,
  ⟨13,4,[0xa000a000a000a0, 0xc000c000c000c0, 0xf0000000f00000, 0xf000f000000000, 0xf000f000a000a0],hints (((((10965 * 1152921504606846976 + 480047585569695027) * 1152921504606846976 + 492349164818636446) * 1152921504606846976 + 370308077822290515) * 1152921504606846976 + 911789494459176786) * 1152921504606846976 + 747081407414484175)⟩,
  ⟨13,4,[0xc0000000c0, 0xa000a000a000a0, 0xc000c000c000c0, 0xf0000000f00000, 0xf000f000000000],hints (((((10644 * 1152921504606846976 + 926428340656191096) * 1152921504606846976 + 511702907141076647) * 1152921504606846976 + 377081784751892948) * 1152921504606846976 + 1067165880463242570) * 1152921504606846976 + 744160349835841273)⟩,
  ⟨13,4,[0x30000000300000, 0xa000a000a000a0, 0xc000c000c000c0, 0xf0000000f00000, 0xf000f000000000],hints (((((10837 * 1152921504606846976 + 494081544500720880) * 1152921504606846976 + 510360197285131943) * 1152921504606846976 + 376795980441584147) * 1152921504606846976 + 929550953691658122) * 1152921504606846976 + 745884395052593831)⟩,
  ⟨13,4,[0xc000c0, 0xa000a000a000a0, 0xc000c000c000c0, 0xf0000000f00000, 0xf000f000000000],hints (((((10644 * 1152921504606846976 + 926427109110166859) * 1152921504606846976 + 780581122740434599) * 1152921504606846976 + 376795911729424852) * 1152921504606846976 + 1073639753383875915) * 1152921504606846976 + 888275537911697145)⟩,
  ⟨13,4,[0x30003000000000, 0xa000a000a000a0, 0xc000c000c000c0, 0xf0000000f00000, 0xf000f000000000],hints (((((10837 * 1152921504606846976 + 500273994246250720) * 1152921504606846976 + 510360197285147303) * 1152921504606846976 + 376795911722107411) * 1152921504606846976 + 923077029273442186) * 1152921504606846976 + 746693635610636967)⟩,
  ⟨13,4,[0xa000a000a000a0, 0xc000c000c000c0, 0xf0000000000000, 0xf0000000f00000, 0xf000f000000000],hints (((((10837 * 1152921504606846976 + 487072290348634496) * 1152921504606846976 + 870718517525172894) * 1152921504606846976 + 356886032329976543) * 1152921504606846976 + 191213500392699195) * 1152921504606846976 + 1035593100919127247)⟩,
  ⟨13,4,[0xa000a000a000a0, 0xc000c000c000c0, 0xf0000000f00000, 0xf000f000000000, 0xf000f000f00000],hints (((((10965 * 1152921504606846976 + 480007979679884531) * 1152921504606846976 + 277510021604297886) * 1152921504606846976 + 356696546962816607) * 1152921504606846976 + 191213546500683067) * 1152921504606846976 + 765095648300186831)⟩,
  ⟨1,3,[0x20208080, 0x3000c000, 0x30300000],hints (((((603970 * 1152921504606846976 + 349709799057643120) * 1152921504606846976 + 331789866878111966) * 1152921504606846976 + 498621637665882651) * 1152921504606846976 + 722832372332880016) * 1152921504606846976 + 332085113881895944)⟩,
  ⟨3,3,[0x202000008080, 0x30000000c000, 0x303000000000],hints (((((605378 * 1152921504606846976 + 355914366841730848) * 1152921504606846976 + 332563923069833460) * 1152921504606846976 + 548258179938583070) * 1152921504606846976 + 434602019803578512) * 1152921504606846976 + 332860684849128456)⟩,
  ⟨6,3,[0x20008000200080, 0x30000000300000, 0x3000c000000000],hints (((((7026394 * 1152921504606846976 + 934523363019044507) * 1152921504606846976 + 398008916734906617) * 1152921504606846976 + 108299639864525318) * 1152921504606846976 + 2256427658745795) * 1152921504606846976 + 1017581958531772424)⟩,
  ⟨5,3,[0x20002000800080, 0x30000000c00000, 0x30003000000000],hints (((((933315 * 1152921504606846976 + 644426217972266792) * 1152921504606846976 + 512708595359420665) * 1152921504606846976 + 557283014329041438) * 1152921504606846976 + 1011062773180764384) * 1152921504606846976 + 513180660658092040)⟩
]
def nodesBlock8 : Array Node := #[
  ⟨7,3,[0x40004000400040, 0x60000000600000, 0x60006000000000],hints (((((5551816 * 1152921504606846976 + 644390303455622874) * 1152921504606846976 + 744618509143400686) * 1152921504606846976 + 493357312708556315) * 1152921504606846976 + 493275182602749832) * 1152921504606846976 + 512014618973561582)⟩,
  ⟨8,3,[0x80004000800040, 0xa0000000a00000, 0xa0005000000000],hints (((((5584584 * 1152921504606846976 + 642419978603968218) * 1152921504606846976 + 762632976506577126) * 1152921504606846976 + 493357243989079643) * 1152921504606846976 + 493552260610889552) * 1152921504606846976 + 548078669216208102)⟩,
  ⟨9,3,[0x80008000400040, 0xa0000000500000, 0xa000a000000000],hints (((((5551368 * 1152921504606846976 + 644390853211408034) * 1152921504606846976 + 744653692307793135) * 1152921504606846976 + 477603518712525786) * 1152921504606846976 + 634857645643986824) * 1152921504606846976 + 511697959625024239)⟩,
  ⟨2,3,[0x80804040, 0xa0005000, 0xa0a00000],hints (((((5516484 * 1152921504606846976 + 782030983976924570) * 1152921504606846976 + 726568852307590361) * 1152921504606846976 + 403205974918507606) * 1152921504606846976 + 482286112544069328) * 1152921504606846976 + 330498374508066009)⟩,
  ⟨4,3,[0x808000004040, 0xa00000005000, 0xa0a000000000],hints (((((5516679 * 1152921504606846976 + 211763802193749426) * 1152921504606846976 + 726639221052302575) * 1152921504606846976 + 410049524301966422) * 1152921504606846976 + 914643771399542656) * 1152921504606846976 + 330498374513844463)⟩,
  ⟨10,3,[0xa00000000000a0, 0xc00000000000c0, 0xf0000000000000],hints (((((5188424 * 1152921504606846976 + 935151207784830314) * 1152921504606846976 + 546283441186441465) * 1152921504606846976 + 389862576614484437) * 1152921504606846976 + 767719320356288464) * 1152921504606846976 + 150001857163818233)⟩,
  ⟨0,3,[0xa0a0, 0xc0c0, 0xf000],hints (((((5188098 * 1152921504606846976 + 338138877903144258) * 1152921504606846976 + 546037150579957936) * 1152921504606846976 + 378374251944585685) * 1152921504606846976 + 47103247802594696) * 1152921504606846976 + 150001857144644272)⟩
]
def nodesGet (i : Nat) : Option Node :=
  if i < 64 then
    if i < 32 then
      if i < 16 then
        nodesBlock0[(i - 0)]?
      else
        nodesBlock1[(i - 16)]?
    else
      if i < 48 then
        nodesBlock2[(i - 32)]?
      else
        nodesBlock3[(i - 48)]?
  else
    if i < 96 then
      if i < 80 then
        nodesBlock4[(i - 64)]?
      else
        nodesBlock5[(i - 80)]?
    else
      if i < 112 then
        nodesBlock6[(i - 96)]?
      else
        if i < 128 then
          nodesBlock7[(i - 112)]?
        else
          nodesBlock8[(i - 128)]?
def fastViews : Fast.Table View := ⟨21,viewsGet⟩
def fastNodes : Fast.Table Node := ⟨135,nodesGet⟩
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkRoots_0 : Fast.passBlock (Fast.checkRootAt fastViews fastNodes) 0 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkRoots_10 : Fast.passBlock (Fast.checkRootAt fastViews fastNodes) 10 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkRoots_20 : Fast.passBlock (Fast.checkRootAt fastViews fastNodes) 20 1 = true := by decide +kernel
theorem combineRoots_0_0 : Fast.passBlock (Fast.checkRootAt fastViews fastNodes) 0 20 = true := @Fast.merge_blocks (Fast.checkRootAt fastViews fastNodes) 0 10 10 checkRoots_0 checkRoots_10
theorem combineRoots_1_0 : Fast.passBlock (Fast.checkRootAt fastViews fastNodes) 0 21 = true := @Fast.merge_blocks (Fast.checkRootAt fastViews fastNodes) 0 20 1 combineRoots_0_0 checkRoots_20
theorem certifiedRoots : Fast.passBlock (Fast.checkRootAt fastViews fastNodes) 0 21 = true := combineRoots_1_0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_0 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 0 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_10 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 10 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_20 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 20 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_30 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 30 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_40 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 40 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_50 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 50 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_60 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 60 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_70 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 70 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_80 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 80 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_90 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 90 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_100 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 100 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_110 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 110 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_120 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 120 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_130 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 130 5 = true := by decide +kernel
theorem combineNodes_0_0 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 0 20 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 0 10 10 checkNodes_0 checkNodes_10
theorem combineNodes_0_20 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 20 20 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 20 10 10 checkNodes_20 checkNodes_30
theorem combineNodes_0_40 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 40 20 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 40 10 10 checkNodes_40 checkNodes_50
theorem combineNodes_0_60 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 60 20 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 60 10 10 checkNodes_60 checkNodes_70
theorem combineNodes_0_80 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 80 20 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 80 10 10 checkNodes_80 checkNodes_90
theorem combineNodes_0_100 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 100 20 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 100 10 10 checkNodes_100 checkNodes_110
theorem combineNodes_0_120 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 120 15 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 120 10 5 checkNodes_120 checkNodes_130
theorem combineNodes_1_0 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 0 40 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 0 20 20 combineNodes_0_0 combineNodes_0_20
theorem combineNodes_1_40 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 40 40 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 40 20 20 combineNodes_0_40 combineNodes_0_60
theorem combineNodes_1_80 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 80 40 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 80 20 20 combineNodes_0_80 combineNodes_0_100
theorem combineNodes_2_0 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 0 80 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 0 40 40 combineNodes_1_0 combineNodes_1_40
theorem combineNodes_2_80 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 80 55 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 80 40 15 combineNodes_1_80 combineNodes_0_120
theorem combineNodes_3_0 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 0 135 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 0 80 55 combineNodes_2_0 combineNodes_2_80
theorem certifiedNodes : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 0 135 = true := combineNodes_3_0

end SignedProjection
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity SignedProjection

def witness : Circuit := ⟨[⟨.or,[0,4]⟩, ⟨.and,[1,2]⟩, ⟨.or,[0,7]⟩, ⟨.or,[1,4]⟩, ⟨.and,[1,6]⟩, ⟨.or,[10,3]⟩, ⟨.and,[9,5]⟩, ⟨.or,[11,12]⟩, ⟨.and,[8,13]⟩],14⟩

theorem witness_legal : Monotone2 witness := by
  intro g hg
  simp only [witness,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with h|h|h|h|h|h|h|h|h <;> subst g <;>
    first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩

set_option maxRecDepth 10000 in
theorem witness_table : ∀ x, witness.eval (List.ofFn x) = CoreSigned.F x := by decide +kernel

def rootMatches (item : Option View) : Bool :=
  match item with
  | none => false
  | some v => vg v == (0xeaeaeac8eac8ea88 : BitVec 64) && vk v == 8 &&
      (vs v).toFinset == Direct64.cols.toFinset

theorem lower (C : Circuit) (legal : FanInTwo C)
    (eq : ∀ x, C.eval (List.ofFn x) = CoreSigned.F x) : 9 ≤ C.size := by
  have reject : ¬ CoreSigned.build SignedProjection.signedOps
      (0xeaeaeac8eac8ea88 : BitVec 64) 8 Direct64.cols.toFinset := by
    have shape : rootMatches (Fast.get fastViews 20) = true := by decide +kernel
    cases ev : Fast.get fastViews 20 with
    | none => simp [rootMatches,ev] at shape
    | some v =>
      have valid := Fast.certified_view fastViews fastNodes certifiedRoots certifiedNodes ev
      simp only [rootMatches,ev,Bool.and_eq_true,beq_iff_eq] at shape
      rcases shape with ⟨⟨goal,budget⟩,stock⟩
      unfold ViewOK at valid
      rw [goal,budget,stock] at valid
      exact valid
  have lb := Direct64.low reject C.gates C.output (fun g hg => legal g hg) eq
  change 8 < (C.gates.filter Direct64.isBinary).length at lb
  exact le_trans lb (List.length_filter_le _ _)

end PEqualNP.Outside.L_meta_13501

open PEqualNP.Outside.L_meta_13501 in
theorem PEqualNP.Outside.L_meta_13501 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941264072 * 2 ^ 32 + 3939035784) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941264072 * 2 ^ 32 + 3939035784) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  intro s h
  obtain ⟨D,hd,hsize,heq⟩ := h
  exact ⟨witness, witness_legal, le_trans (lower D hd heq) hsize, witness_table⟩
