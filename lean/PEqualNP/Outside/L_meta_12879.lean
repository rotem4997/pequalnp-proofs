import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12879

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

def F (x : Fin 6 → Bool) : Bool := Nat.testBit (4276676840 * 2 ^ 32 + 4003504288) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
abbrev goal : W := ~~~0xfee8e8e8eea0a0a0
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

theorem low (reject : ¬ build basicOps (0xfee8e8e8eea0a0a0 : W) 8 cols.toFinset)
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

namespace SevenGlue
open SignedProjection

def rootMatches (item : Option View) : Bool :=
  match item with
  | none => false
  | some v => vg v == (0xfee8e8e8eea0a0a0 : BitVec 64) && vk v == 8 &&
      (vs v).toFinset == Direct64.cols.toFinset

theorem from_blocks (views : Fast.Table View) (nodes : Fast.Table Node)
    (roots : Fast.passBlock (Fast.checkRootAt views nodes) 0 views.1 = true)
    (states : Fast.passBlock (Fast.checkNodeAt views nodes) 0 nodes.1 = true)
    (which : Nat) (shape : rootMatches (Fast.get views which) = true) :
    ¬ CoreSigned.build SignedProjection.signedOps (0xfee8e8e8eea0a0a0 : BitVec 64) 8 Direct64.cols.toFinset := by
  cases ev : Fast.get views which with
  | none => simp [rootMatches,ev] at shape
  | some v =>
    have valid := Fast.certified_view views nodes roots states ev
    simp only [rootMatches,ev,Bool.and_eq_true,beq_iff_eq] at shape
    rcases shape with ⟨⟨goal,budget⟩,stock⟩
    unfold ViewOK at valid
    rw [goal,budget,stock] at valid
    exact valid
end SevenGlue

namespace SignedProjection
def labelsBlock0 : Array Nat := #[
  1,
  5,
  9,
  13,
  17,
  20,
  21,
  25,
  29,
  33,
  37,
  41,
  45,
  49,
  52,
  53
]
def labelsBlock1 : Array Nat := #[
  57,
  60,
  61,
  65,
  69,
  73,
  77,
  81,
  85,
  89,
  93,
  97,
  100,
  101,
  104,
  105
]
def labelsBlock2 : Array Nat := #[
  108,
  109,
  113,
  116,
  117,
  120,
  121,
  124,
  125,
  129,
  133,
  137,
  140,
  141,
  145,
  149
]
def labelsBlock3 : Array Nat := #[
  152,
  153,
  157,
  161,
  165,
  169,
  172,
  173,
  177,
  180,
  181,
  184,
  185,
  188,
  189,
  193
]
def labelsBlock4 : Array Nat := #[
  197,
  201,
  205,
  209,
  213,
  217,
  221,
  225,
  228,
  229,
  232,
  233,
  236,
  237,
  240,
  241
]
def labelsBlock5 : Array Nat := #[
  244,
  245,
  248,
  249,
  253,
  257,
  261,
  265,
  269,
  273,
  276,
  277,
  281,
  285,
  289,
  293
]
def labelsBlock6 : Array Nat := #[
  297,
  301,
  305,
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
  356
]
def labelsBlock7 : Array Nat := #[
  357,
  361,
  365,
  369,
  373,
  377,
  381,
  385,
  389,
  393,
  396,
  397,
  401,
  405,
  409,
  413
]
def labelsBlock8 : Array Nat := #[
  417,
  421,
  425,
  429,
  433,
  437,
  441,
  445,
  449,
  453,
  457,
  461,
  465,
  469,
  473,
  477
]
def labelsBlock9 : Array Nat := #[
  481,
  485,
  489,
  493,
  497,
  501,
  505,
  509,
  513,
  517,
  521,
  525,
  529,
  533,
  537,
  541
]
def labelsBlock10 : Array Nat := #[
  545,
  549,
  553,
  557,
  561,
  565,
  569,
  573,
  577,
  581,
  585,
  589,
  593,
  597,
  601,
  605
]
def labelsBlock11 : Array Nat := #[
  609,
  613,
  617,
  621,
  625,
  629,
  633,
  637,
  641,
  645,
  649,
  652,
  653,
  657,
  661,
  665
]
def labelsBlock12 : Array Nat := #[
  669,
  673,
  677,
  681,
  685,
  689,
  693,
  697,
  701,
  705,
  709,
  713,
  717,
  721,
  725,
  729
]
def labelsBlock13 : Array Nat := #[
  733,
  737,
  741,
  745,
  749,
  753,
  757,
  761,
  765,
  769,
  773,
  777,
  781,
  785,
  789,
  793
]
def labelsBlock14 : Array Nat := #[
  797,
  801,
  805,
  809,
  813,
  817,
  821,
  825,
  829,
  833,
  837,
  841,
  845,
  849,
  853,
  857
]
def labelsBlock15 : Array Nat := #[
  861,
  865,
  869,
  873,
  877,
  881,
  885,
  889,
  893,
  897,
  901,
  905,
  908,
  909,
  913,
  917
]
def labelsBlock16 : Array Nat := #[
  921,
  925,
  929,
  933,
  937,
  941,
  945,
  949,
  953,
  957,
  961,
  965,
  969,
  973,
  977,
  981
]
def labelsBlock17 : Array Nat := #[
  985,
  989,
  993,
  997,
  1001,
  1005,
  1009,
  1013,
  1017,
  1021,
  1025,
  1029,
  1033,
  1037,
  1041,
  1044
]
def labelsBlock18 : Array Nat := #[
  1045,
  1049,
  1053,
  1057,
  1061,
  1065,
  1069,
  1073,
  1077,
  1081,
  1085,
  1089,
  1093,
  1097,
  1101,
  1105
]
def labelsBlock19 : Array Nat := #[
  1109,
  1113,
  1117,
  1121,
  1125,
  1129,
  1133,
  1137,
  1141,
  1145,
  1149,
  1153,
  1157,
  1161,
  1165,
  1169
]
def labelsBlock20 : Array Nat := #[
  1173,
  1177,
  1181,
  1185,
  1189,
  1193,
  1197,
  1201,
  1205,
  1209,
  1213,
  1217,
  1221,
  1225,
  1229,
  1233
]
def labelsBlock21 : Array Nat := #[
  1237,
  1241,
  1245,
  1249,
  1253,
  1257,
  1261,
  1265,
  1269,
  1273,
  1277,
  1281,
  1285,
  1289,
  1293,
  1297
]
def labelsBlock22 : Array Nat := #[
  1301,
  1305,
  1309,
  1313,
  1317,
  1321,
  1325,
  1329,
  1333,
  1337,
  1341,
  1345,
  1349,
  1353,
  1357,
  1361
]
def labelsBlock23 : Array Nat := #[
  1365,
  1369,
  1373,
  1377,
  1381,
  1385,
  1389,
  1393,
  1397,
  1401,
  1405,
  1409,
  1413,
  1417,
  1421,
  1425
]
def labelsBlock24 : Array Nat := #[
  1429,
  1433,
  1437,
  1441,
  1445,
  1449,
  1453,
  1457,
  1461,
  1465,
  1469,
  1473,
  1477,
  1481,
  1485,
  1489
]
def labelsBlock25 : Array Nat := #[
  1493,
  1497,
  1501,
  1505,
  1509,
  1513,
  1517,
  1521,
  1525,
  1529,
  1533,
  1537,
  1541,
  1545,
  1549,
  1553
]
def labelsBlock26 : Array Nat := #[
  1557,
  1561,
  1565,
  1569,
  1573,
  1577,
  1581,
  1585,
  1589,
  1593,
  1597,
  1601,
  1605,
  1609,
  1613,
  1617
]
def labelsBlock27 : Array Nat := #[
  1621,
  1625,
  1629,
  1633,
  1637,
  1641,
  1645,
  1649,
  1653,
  1657,
  1661,
  1665,
  1669,
  1673,
  1677,
  1681
]
def labelsBlock28 : Array Nat := #[
  1685,
  1689,
  1693,
  1697,
  1701,
  1705,
  1709,
  1713,
  1717,
  1721,
  1725,
  1729,
  1733,
  1737,
  1741,
  1745
]
def labelsBlock29 : Array Nat := #[
  1749,
  1753,
  1757,
  1761,
  1765,
  1769,
  1773,
  1777,
  1781,
  1785,
  1789,
  1793,
  1797,
  1801,
  1805,
  1809
]
def labelsBlock30 : Array Nat := #[
  1813,
  1817,
  1821,
  1825,
  1829,
  1833,
  1837,
  1841,
  1845,
  1849,
  1853,
  1857,
  1861,
  1865,
  1869,
  1873
]
def labelsBlock31 : Array Nat := #[
  1877,
  1881,
  1885,
  1889,
  1893,
  1897,
  1901,
  1905,
  1909,
  1913,
  1917,
  1921,
  1925,
  1929,
  1933,
  1937
]
def labelsBlock32 : Array Nat := #[
  1941,
  1945,
  1949,
  1953,
  1957,
  1961,
  1965,
  1969,
  1973,
  1977,
  1981,
  2152,
  2356,
  2364,
  2404,
  2408
]
def labelsBlock33 : Array Nat := #[
  2412,
  2420,
  2428,
  2476,
  2484,
  2532,
  2544,
  2548,
  2612,
  2620,
  2660,
  2664,
  2668,
  2680,
  2684,
  2732
]
def labelsBlock34 : Array Nat := #[
  2744,
  2792,
  2796,
  2808,
  2868,
  2876,
  2916,
  2920,
  2924,
  2932,
  2936,
  2940,
  2988,
  3004,
  3052,
  3124
]
def labelsBlock35 : Array Nat := #[
  3132,
  3172,
  3176,
  3180,
  3188,
  3192,
  3196,
  3244,
  3252,
  3256,
  3260,
  3312,
  3636,
  3644,
  3684,
  3688
]
def labelsBlock36 : Array Nat := #[
  3692,
  3700,
  3704,
  3764,
  3768,
  4098,
  4102,
  4106,
  4110,
  4114,
  4118,
  4122,
  4126,
  4130,
  4134,
  4138
]
def labelsBlock37 : Array Nat := #[
  4142,
  4146,
  4150,
  4154,
  4158,
  4162,
  4166,
  4170,
  4174,
  4178,
  4182,
  4186,
  4190,
  4194,
  4198,
  4200
]
def labelsBlock38 : Array Nat := #[
  4202,
  4206,
  4210,
  4214,
  4218,
  4222,
  4226,
  4230,
  4234,
  4238,
  4242,
  4246,
  4250,
  4254,
  4258,
  4262
]
def labelsBlock39 : Array Nat := #[
  4266,
  4270,
  4274,
  4452,
  6196,
  6204,
  6244,
  6248,
  6252,
  6260,
  6264,
  6268,
  6316,
  6372,
  6376,
  6380
]
def labelsBlock40 : Array Nat := #[
  6384,
  7220,
  7228,
  7268,
  7272,
  7276,
  7284,
  7288,
  7292,
  7348,
  7400,
  7408,
  7412,
  7416,
  10292,
  10300
]
def labelsBlock41 : Array Nat := #[
  10344,
  10348,
  10356,
  10360,
  10412,
  10420,
  10424,
  10428,
  10472,
  10476,
  10480,
  10484,
  10488,
  10548,
  10596,
  10604
]
def labelsBlock42 : Array Nat := #[
  10612,
  10668,
  10676,
  10680,
  10724,
  10736,
  10740,
  10812,
  10856,
  10872,
  10924,
  10932,
  10936,
  10980,
  10984,
  10992
]
def labelsBlock43 : Array Nat := #[
  11000,
  11316,
  11324,
  11436,
  11444,
  11448,
  11452,
  11492,
  11496,
  11500,
  11504,
  14436,
  14440,
  14444,
  14508,
  14516
]
def labelsBlock44 : Array Nat := #[
  14520,
  14524,
  14564,
  14568,
  14572,
  14576,
  4260014,
  4325550,
  4329614,
  4329646,
  4391018,
  4391086,
  4395106,
  4395114,
  4395122,
  4395138
]
def labelsBlock45 : Array Nat := #[
  4395182,
  4399218,
  4399278,
  5308562,
  5308586,
  5308590,
  5374098,
  5374114,
  5374118,
  5374122,
  5374126,
  5378170,
  5378210,
  5378214,
  5378222,
  5439662
]
def labelsBlock46 : Array Nat := #[
  5443758,
  5447854,
  6295694,
  6295722,
  6357138,
  6357166,
  6422650,
  6422674,
  6422690,
  6422702,
  6426786,
  6426798,
  6488238,
  6492334,
  6496430,
  7405738
]
def labelsBlock47 : Array Nat := #[
  7405742,
  7471270,
  7471274,
  7471278,
  7475366,
  7475374,
  7536754,
  7536810,
  7536814,
  7540910,
  7544938,
  7544994,
  7545006,
  4514185362,
  4514250898,
  4514250918
]
def labelsBlock48 : Array Nat := #[
  4514255014,
  5387718830,
  5387784366,
  5387788462,
  5388767406,
  5388832942,
  5388837038,
  5452726446,
  5452791982,
  5504041130,
  5510332590,
  5519900846,
  5519904942,
  5571149998,
  5572198574,
  5577441454
]
def labelsBlock49 : Array Nat := #[
  5579669678,
  5581701294,
  5581705390,
  5581766830,
  5586878638,
  5586944174,
  5586948270,
  5588975790,
  5589041326,
  5589045422,
  5589106862,
  5590024366,
  5590089902,
  5590093998,
  5637279918,
  5637345454
]
def labelsBlock50 : Array Nat := #[
  5637349550,
  6581977262,
  6644891822,
  6649086126,
  6653345966,
  6653350062,
  6661669038,
  6661734574,
  6661738670,
  6711087278,
  7600210094,
  7600275630,
  7667384494,
  7667388590,
  7727153326,
  7734427822
]
def labelsBlock51 : Array Nat := #[
  7785812142,
  7785877678,
  7785881774
]
def labelsGet (i : Nat) : Option Nat :=
  if i < 416 then
    if i < 208 then
      if i < 96 then
        if i < 48 then
          if i < 16 then
            labelsBlock0[(i - 0)]?
          else
            if i < 32 then
              labelsBlock1[(i - 16)]?
            else
              labelsBlock2[(i - 32)]?
        else
          if i < 64 then
            labelsBlock3[(i - 48)]?
          else
            if i < 80 then
              labelsBlock4[(i - 64)]?
            else
              labelsBlock5[(i - 80)]?
      else
        if i < 144 then
          if i < 112 then
            labelsBlock6[(i - 96)]?
          else
            if i < 128 then
              labelsBlock7[(i - 112)]?
            else
              labelsBlock8[(i - 128)]?
        else
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
      if i < 304 then
        if i < 256 then
          if i < 224 then
            labelsBlock13[(i - 208)]?
          else
            if i < 240 then
              labelsBlock14[(i - 224)]?
            else
              labelsBlock15[(i - 240)]?
        else
          if i < 272 then
            labelsBlock16[(i - 256)]?
          else
            if i < 288 then
              labelsBlock17[(i - 272)]?
            else
              labelsBlock18[(i - 288)]?
      else
        if i < 352 then
          if i < 320 then
            labelsBlock19[(i - 304)]?
          else
            if i < 336 then
              labelsBlock20[(i - 320)]?
            else
              labelsBlock21[(i - 336)]?
        else
          if i < 384 then
            if i < 368 then
              labelsBlock22[(i - 352)]?
            else
              labelsBlock23[(i - 368)]?
          else
            if i < 400 then
              labelsBlock24[(i - 384)]?
            else
              labelsBlock25[(i - 400)]?
  else
    if i < 624 then
      if i < 512 then
        if i < 464 then
          if i < 432 then
            labelsBlock26[(i - 416)]?
          else
            if i < 448 then
              labelsBlock27[(i - 432)]?
            else
              labelsBlock28[(i - 448)]?
        else
          if i < 480 then
            labelsBlock29[(i - 464)]?
          else
            if i < 496 then
              labelsBlock30[(i - 480)]?
            else
              labelsBlock31[(i - 496)]?
      else
        if i < 560 then
          if i < 528 then
            labelsBlock32[(i - 512)]?
          else
            if i < 544 then
              labelsBlock33[(i - 528)]?
            else
              labelsBlock34[(i - 544)]?
        else
          if i < 592 then
            if i < 576 then
              labelsBlock35[(i - 560)]?
            else
              labelsBlock36[(i - 576)]?
          else
            if i < 608 then
              labelsBlock37[(i - 592)]?
            else
              labelsBlock38[(i - 608)]?
    else
      if i < 720 then
        if i < 672 then
          if i < 640 then
            labelsBlock39[(i - 624)]?
          else
            if i < 656 then
              labelsBlock40[(i - 640)]?
            else
              labelsBlock41[(i - 656)]?
        else
          if i < 688 then
            labelsBlock42[(i - 672)]?
          else
            if i < 704 then
              labelsBlock43[(i - 688)]?
            else
              labelsBlock44[(i - 704)]?
      else
        if i < 768 then
          if i < 736 then
            labelsBlock45[(i - 720)]?
          else
            if i < 752 then
              labelsBlock46[(i - 736)]?
            else
              labelsBlock47[(i - 752)]?
        else
          if i < 800 then
            if i < 784 then
              labelsBlock48[(i - 768)]?
            else
              labelsBlock49[(i - 784)]?
          else
            if i < 816 then
              labelsBlock50[(i - 800)]?
            else
              labelsBlock51[(i - 816)]?
def hints (enc i : Nat) : Nat := (labelsGet ((enc >>> (i * 10)) % 1024)).getD 0
def lhints (b dict data i : Nat) := hints dict ((data >>> (i*b)) % (2^b))
def viewsBlock0 : Array View := #[
  ⟨0x14002800,⟨11,by decide⟩,0x4002000,[0x10002000, 0x14000000],2,hints 0x8280e0780e⟩,
  ⟨0x3c003c00,⟨10,by decide⟩,0x2c002000,[0x28002800, 0x30003000, 0x3c000000],2,hints 0x9162f8900e0781e0780e⟩,
  ⟨0x5500aa00,⟨9,by decide⟩,0x4400a000,[0x44008800, 0x5000a000, 0x55000000],2,hints 0x916770380e89c1e0380e⟩,
  ⟨0xc300c300,⟨8,by decide⟩,0xc2008000,[0x82008200, 0xc000c000, 0xc3000000],3,hints 0x7de3d834118381c09411⟩,
  ⟨0xf00f0000000,⟨28,by decide⟩,0x800e0000000,[0xa00a0000000, 0xc00c0000000, 0xf0000000000],3,hints 0x7e82309423a802309423⟩,
  ⟨0xcc000000cc00,⟨10,by decide⟩,0xc80000008000,[0x880000008800, 0xc0000000c000, 0xcc0000000000],3,hints 0x8023d894118b0360ec11⟩,
  ⟨0xff0000000000,⟨40,by decide⟩,0xe80000000000,[0xaa0000000000, 0xcc0000000000, 0xf00000000000],3,hints 0x7e6aaa8436a88390ec36⟩,
  ⟨0xa000a0005000500,⟨8,by decide⟩,0xa00080004000000,[0x800080004000400, 0xa00000005000000, 0xa000a0000000000],3,hints 0x7ee7786c1e87c361201e⟩,
  ⟨0xc000c0003000300,⟨8,by decide⟩,0xc00080002000000,[0x800080002000200, 0xc00000003000000, 0xc000c0000000000],3,hints 0x7da768381c84c361281c⟩,
  ⟨0xf000f0000000000,⟨40,by decide⟩,0xe00080000000000,[0xa000a0000000000, 0xc000c0000000000, 0xf00000000000000],3,hints 0x7e2aaa8436a904812836⟩,
  ⟨0x1100110088008800,⟨11,by decide⟩,0x1000000088008000,[0x1000100080008000, 0x1100000088000000, 0x1100110000000000],3,hints 0x7f81108011ac81108011⟩,
  ⟨0x1100880011008800,⟨11,by decide⟩,0x1000880000008000,[0x1000800010008000, 0x1100000011000000, 0x1100880000000000],3,hints 0x7f411a08110d8110d811⟩,
  ⟨0x1800180018001800,⟨11,by decide⟩,0x1800080008000000,[0x1000100010001000, 0x1800000018000000, 0x1800180000000000],3,hints 0x7f285080200d83608020⟩,
  ⟨0x30000c0030000c00,⟨10,by decide⟩,0x3000080020000000,[0x2000080020000800, 0x3000000030000000, 0x30000c0000000000],3,hints 0x806868a4238b03613823⟩,
  ⟨0x3300330000000000,⟨40,by decide⟩,0x3200200000000000,[0x2200220000000000, 0x3000300000000000, 0x3300000000000000],3,hints 0x7feb4a8839a904813839⟩,
  ⟨0x50000a0050000a00,⟨9,by decide⟩,0x5000080040000000,[0x4000080040000800, 0x5000000050000000, 0x50000a0000000000],3,hints 0x812878a8258b03613825⟩
]
def viewsBlock1 : Array View := #[
  ⟨0x5000500050005000,⟨12,by decide⟩,0x5000400040000000,[0x4000400040004000, 0x5000000050000000, 0x5000500000000000],3,hints 0x80a87908259103b13825⟩,
  ⟨0x5500550000000000,⟨40,by decide⟩,0x5400400000000000,[0x4400440000000000, 0x5000500000000000, 0x5500000000000000],3,hints 0x80eb5ab03bab84a1383b⟩,
  ⟨0x9000090090000900,⟨8,by decide⟩,0x9000080080000000,[0x8000080080000800, 0x9000000090000000, 0x9000090000000000],3,hints 0x81e888ac278b03613827⟩,
  ⟨0x9000900009000900,⟨8,by decide⟩,0x9000800008000000,[0x8000800008000800, 0x9000000009000000, 0x9000900000000000],3,hints 0x816788a0208b43d13820⟩,
  ⟨0x9900000000009900,⟨8,by decide⟩,0x9800000000008000,[0x8800000000008800, 0x9000000000009000, 0x9900000000000000],3,hints 0x81a30894118b84c13811⟩,
  ⟨0xa0000a0050000500,⟨8,by decide⟩,0xa000080040000000,[0x8000080040000400, 0xa000000050000000, 0xa0000a0000000000],3,hints 0x822878742587c3614025⟩,
  ⟨0xc0000c0030000300,⟨8,by decide⟩,0xc000080020000000,[0x8000080020000200, 0xc000000030000000, 0xc0000c0000000000],3,hints 0x826868442384c3614823⟩,
  ⟨0xff00ff00,⟨8,by decide⟩,0xee00a000,[0xaa00aa00, 0xcc00cc00, 0xf000f000, 0xff000000],3,lhints 3 0x9de488be0e8301e0700e 0xd7d618851610⟩,
  ⟨0xff000000ff00,⟨8,by decide⟩,0xe8000000a000,[0xaa000000aa00, 0xcc000000cc00, 0xf0000000f000, 0xff0000000000],4,hints 0x92e2fa862f8300e8300e8b21f84c368300e0ec0e⟩,
  ⟨0xff00ff000000,⟨24,by decide⟩,0xe800ee000000,[0xaa00aa000000, 0xcc00cc000000, 0xf000f0000000, 0xff0000000000],4,lhints 3 0x2a2a7a4b0781c 0x408808608608⟩,
  ⟨0xf000f000f000f00,⟨8,by decide⟩,0xe0008000e000000,[0xa000a000a000a00, 0xc000c000c000c00, 0xf0000000f000000, 0xf000f0000000000],4,hints 0x93a769de768381c0781c8b21f84c368381c0781c⟩,
  ⟨0xf000f00f000f000,⟨12,by decide⟩,0xe000800e000a000,[0xa000a00a000a000, 0xc000c00c000c000, 0xf000000f0000000, 0xf000f0000000000],4,lhints 3 0xa768793a420940e 0x620408a20408⟩,
  ⟨0x3300330033003300,⟨8,by decide⟩,0x3200200022002000,[0x2200220022002200, 0x3000300030003000, 0x3300000033000000, 0x3300330000000000],4,lhints 3 0xa2e538be0e8304e0700e 0xd58858f58850⟩,
  ⟨0x33003300cc00cc00,⟨10,by decide⟩,0x32002000cc008000,[0x2200220088008800, 0x30003000c000c000, 0x33000000cc000000, 0x3300330000000000],4,lhints 3 0xaf2538f62507811 0x8d0248ad0248⟩,
  ⟨0x3300cc003300cc00,⟨10,by decide⟩,0x3200c80022008000,[0x2200880022008800, 0x3000c0003000c000, 0x3300000033000000, 0x3300cc0000000000],4,hints 0x92a3d894118981c894118b0360ec118981c0ec11⟩,
  ⟨0x3c003c003c003c00,⟨10,by decide⟩,0x3c0028002c002000,[0x2800280028002800, 0x3000300030003000, 0x3c0000003c000000, 0x3c003c0000000000],4,lhints 3 0x22f8b2246c0360780e 0x7a0248aa0248⟩
]
def viewsBlock2 : Array View := #[
  ⟨0x5500550055005500,⟨8,by decide⟩,0x5400400044000000,[0x4400440044004400, 0x5000500050005000, 0x5500000055000000, 0x5500550000000000],4,hints 0x95677ab27786c1e86c1e912398803b86c1e1381e⟩,
  ⟨0x55005500aa00aa00,⟨9,by decide⟩,0x54004000aa00a000,[0x4400440088008800, 0x50005000a000a000, 0x55000000aa000000, 0x5500550000000000],4,lhints 3 0x2b5ac6560700e 0x5002406c0240⟩,
  ⟨0x5500aa005500aa00,⟨9,by decide⟩,0x5400a8004400a000,[0x4400880044008800, 0x5000a0005000a000, 0x5500000055000000, 0x5500aa0000000000],4,lhints 3 0x2778b2276bc360780e 0x780840a80840⟩,
  ⟨0x5a005a005a005a00,⟨9,by decide⟩,0x5a0048004a000000,[0x4800480048004800, 0x5000500050005000, 0x5a0000005a000000, 0x5a005a0000000000],4,lhints 3 0xa1e839562c0d81c 0x764000451000⟩,
  ⟨0x9900990099009900,⟨8,by decide⟩,0x9800880088008000,[0x8800880088008800, 0x9000900090009000, 0x9900000099000000, 0x9900990000000000],5,hints 0x6c630894118a020894118b036894118a02013811⟩,
  ⟨0xaa00aa0055005500,⟨8,by decide⟩,0xaa00a80044000000,[0x8800880044004400, 0xa000a00050005000, 0xaa00000055000000, 0xaa00aa0000000000],4,hints 0x93277a8a7786c1e86c1e87c360e4361201e0e41e⟩,
  ⟨0xc300c300c300c300,⟨8,by decide⟩,0xc200c000c2008000,[0x8200820082008200, 0xc000c000c000c000, 0xc3000000c3000000, 0xc300c30000000000],4,hints 0x9223d834118381c094119123d0ec118381c09411⟩,
  ⟨0xcc00cc0033003300,⟨8,by decide⟩,0xcc00c80022002000,[0x8800880022002200, 0xc000c00030003000, 0xcc00000033000000, 0xcc00cc0000000000],4,hints 0x9362f8300e8381c8300e84c360ec0e1281c0ec0e⟩,
  ⟨0xcc00cc00cc00cc00,⟨10,by decide⟩,0xcc00c800cc008000,[0x8800880088008800, 0xc000c000c000c000, 0xcc000000cc000000, 0xcc00cc0000000000],4,lhints 3 0x92a3d8b2250ec3607811 0xfa0248a98248⟩,
  ⟨0xf0000f00f0000f00,⟨8,by decide⟩,0xf0000800e0000000,[0xa0000a00a0000a00, 0xc0000c00c0000c00, 0xf0000000f0000000, 0xf0000f0000000000],5,hints 0x6fa86a1e8684423094238b21f84c361382309423⟩,
  ⟨0xf000f000f000f000,⟨12,by decide⟩,0xf000e000e000a000,[0xa000a000a000a000, 0xc000c000c000c000, 0xf0000000f0000000, 0xf000f00000000000],4,lhints 3 0xa1e55912421383b0940e 0xc38808a10608⟩,
  ⟨0xff00ff0000000000,⟨40,by decide⟩,0xfe00e80000000000,[0xaa00aa0000000000, 0xcc00cc0000000000, 0xf000f00000000000, 0xff00000000000000],6,hints 0x72eaaa8436a88390ec36a904812836138390ec36⟩,
  ⟨0xff00ff00ff00ff00,⟨8,by decide⟩,0xfe00e800ee00a000,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],8,lhints 4 0x9de2f8b21f84e0e8304e0ec360781c03800 0xcdc717182327131ba94715182326131⟩,
  ⟨0xffffffffffffffff,⟨0,by decide⟩,0xfee8e8e8eea0a0a0,[0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000],8,lhints 5 0x9de739ca5f83a0b47cfc2ec7a1bc5a138300b01e07005 0x7ae2b300c082dcb300c06ad8b300c038441300405250330080525033008052503300803844128040⟩
]
def viewsGet (i : Nat) : Option View :=
  if i < 16 then
    viewsBlock0[(i - 0)]?
  else
    if i < 32 then
      viewsBlock1[(i - 16)]?
    else
      viewsBlock2[(i - 32)]?
def nodesBlock0 : Array Node := #[
  ⟨44,8,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0xb16acaaaa4a8aa1a2e879de769c64490a3f8f63c8c22f8b2258921f86e158521383a0d831a6691a26819e6698d5e9735b9615714d4d5183f4e836cb320c681041e0701203801 0xb5dc5db74960b74c71b5d95db5bb1bb7395fb73b2cb5b95b69badb67775d637aea5db75bb6f95eb72c5eb72965b6fc6f5b284456f74452f8614f275d4af91c4706db4309233ef6dbb66962b75b22b75965b66b263a674336e84332e75d2e68612ae6c1266d812266db1eedae1a6ca6169be70a9ca8026be6⟩,
  ⟨44,7,[0x8800880088008800, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0x2c6b16b5ad2aca92a2a868ba1e779da719c26a99a629825d912428fe3d8f2398e22f8b2288961b8561483a0c0781c0380d02c0801802 0xa89889aa53cbaa58a2a893c9a885c8aa43caaa45d7a883c81085880e92490a9595048248aa03cfaa8892aa83cfaa08a06a83076a02476a030c6a82496a034d6a12086a134d6a0208a903cfaa75d1aa73cfa905d06d02466df3066df2496d030c6df2056d09856d02086df99f71071071c82069a6d3aaa3cfa9e5d7a9e3cfaaa5d769838e69a24968038e69a24969934d69a20869d34d69a20871c723a9e82071c714a9e410⟩,
  ⟨44,6,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff008800ff008800, 0xff00ff0000000000],lhints 6 0x314b5ac5ad6b4ab2a2a868ba1e779da719c26f9aa6899a62976448f63c8e6388be2c8a22789a258520e8300e01003 0x90a29841060a2a441025c26428a91c7092894921096040d00de2857904032830d70c65861971835830c10e224988088324368a2a170d84a29a71a85275a55a6926a156184925a49a6891e148768619b0c36c619a0c32ca2a040c80a28b40b2d12d954f65464b54b2c92594d964920b4c864308b7c22c30d97d92e32e369a49338b68b⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff008800ff008800, 0xff00f000ff00f000, 0xff00ff0000000000],lhints 5 0x2c5ad6849ea779da6f912428fe3c8ee398e2358d22f8b22889e2683a0c 0x85790ab2b821241e579400759ad2a8b224842421d594e922a4a62186331e26898d134986⟩,
  ⟨44,5,[0xf0000000f000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff008800ff008800, 0xff00ff0000000000],lhints 5 0x314b16b59de76912428f23b8e6388d6348be2c8aa2889e26896148460e8300e 0x541520926108ca153d556b656284a15394b5b28b000295d62b42b0810ae1aa0c6a20e7⟩,
  ⟨44,6,[0x8800880088008800, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf0000000f0000000, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0xb16a1a2e87a1a779da6598a5d912428fe3d8f2398e22f8b2288961b8561483a0c0781c03807 0xa7d9486990858ed7b5c8bd22dcbc0c682a4892635ac2dab6084540424bb3396330f5cd735154549124a5416e620c⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xf8008800f8008800, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x28ba1e869de769123f8f63c8e6388be2c8a22586e158520e8301e0700e 0x21ac4545514912419623192031a10353553108e49d6b340d035314b084875be8b000725cdcb⟩,
  ⟨44,6,[0x8800880088008800, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00f000ff00f000, 0xff00ff0000000000],lhints 5 0xb16b5a868ba127a9de769c26e9b26698a609764490a3f8f63c8ee398e2358d22f8b20e8300a02403 0x20581565e14848160518dff71545cdb399a10ff675bc9525308c6a18f8360c6c1b2c2c0b00d6f38bc0f97effee5a6⟩,
  ⟨44,5,[0x7700700077007000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x2c5aaaa1a2e779da4490a3f8f63c8be2c8a22587e1c866138420e8360c 0x4aa6942a08425c82115218d340851239d4b3192b295115c98b82a0a109e9002c8952545d56d⟩,
  ⟨44,5,[0x5500500055005000, 0x8800880088008800, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x294a2e779da448fe3d8f2398e2348be2c8a22587e1c86e1a86618120390700e 0x8ee100a800066064196584c1500804a5944056128140c59ac7b0e1706a0681b1b364d⟩,
  ⟨44,6,[0xf0000000f000, 0x8800880088008800, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x2c5ad6a1a2e849ea779da709be629824490a3d8f2398e22f8b22886e158460e8301e0700c 0x86c9209824bc22589b084725af8b2569504243d54aaaacd4c130411048f29cd59ca8260979063ddb765555594c13⟩,
  ⟨44,5,[0x8800f8008800f800, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0xb16b5a868b9ea779da448f2398e2308be2c8a2258921b8561183a0c0781c 0x1968342a0820ee353952084c344ce75354b0006642d115b1eb5515448d2310917acad25c571⟩,
  ⟨44,6,[0xf0000000f000000, 0x8800880088008800, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x2c6b16b5a868ba1e779da6f98a5d912428f63c8ee398e2358d22f8b2258521183a0c0400f03804 0x1e9d2487990d2225c9c3192e2088225a95297750424bab104cd33a481241104de22a1a7c9297a4c6719baaeaad856⟩,
  ⟨44,5,[0x8f0088008f008800, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x28ba1e779da4490a3d8f2398e2358d22f8b22889e26896148460e8300e 0x426c80924108e214b934430c6284a14b52a42ce700033551ea4c93210911284a1a569582a6a⟩,
  ⟨44,5,[0x8800880088008800, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xf000ff0000000000, 0xff000000ff000000],lhints 5 0x2a1a2e779da448fe3d8f2398e22f8b2288961b8520e8301e0700e 0x249320c8f18cb0188462258991c671842432569500038aa4d411044c13038ce3a49ca⟩,
  ⟨44,7,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xee00ee00ee00ee00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0xb56c5aeaacaaaa4a8aa1a2e779c6709ba6a99a629825d912428fe3d8f22f8b2258921f86e198561484e1083a0d8303c0e0350c82e0b42a0a02107c1605413 0xc4fa4fc6c653c6ca69c4f64fc4d7cdc6b652c6b7dfc4d64d30d78d2f03cf2b079d24d3cdc71659c67a69c67659c71a699603cf948bef9653cf960bef96534d966c3096634d961c30c71651c6aa51c6a659c71a6996a5508873cf9655558aa3cf96a60e88634d9656178aa34d924928c6a9e8c5c656c6d7d6c6d659c5c7dc15c3cf8c45550c23cf8dc55506d34d8dcb9401c34d8edbad92491ac5c9da924aaa91c91c8a28db⟩
]
def nodesBlock1 : Array Node := #[
  ⟨44,6,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xee00ee00ee00ee00, 0xf000f000f000f000, 0xfa00fa00fa00fa00, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0xb8ad5aeaacaaaa1a2e779c26e9b26a99660912428f63c8be2c8921b8561484e1083a0d83014 0x67b8d5c500681a026784237074155d571ec7b9ca320d4302955720d03a631210521b594f534681a32d0b7ab5e1ac⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xee00ee00ee00ee00, 0xf000f000f000f000, 0xfa00fa0000000000, 0xff000000ff000000],lhints 5 0xb8acaaeaa1a2e779c2448fe3d8f22f8b22487e1b86615852138420e8360c 0x18531004f000b000aa2aae6b98220b0c481108b9840a04a42409094adc0382ec651cd⟩,
  ⟨44,6,[0x5000500050005000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xee00ee00ee00ee00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x2baab2aaa868b9de769c26e9b26a99a659824490a3d8b22487e1b86615852138420e8360c 0x46c080570002681785e05c1701503c845e06240820502f74a56e1204838356b675172dcb689a2d825384a59a658c⟩,
  ⟨44,6,[0xcc00cc00cc00cc00, 0xee00ee00ee00ee00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00aa00ff00aa00, 0xff00ff0000000000],lhints 6 0xc36d7b5ac5b0aacaaaa4a8aa1a2e86a067d9e6779da6a99a5d9123d8f22f8b22789a258921f86e198561484e0f83a0d8301d0681906017 0x5933a55ce9534d65d61e11e44cb9218474c76593475871571634ca8d75c54c59963059451561669651441681c7a03a051c56d34e785e9d34db85b61651b6946d659869a6071dba9b6c71d8a9f6c5160a1d80515ba1bad32628498934eb861a965a26a28965426958922011c7a924621c7890180145a903e2145a697226db⟩,
  ⟨44,5,[0xc000c000c000c00, 0xee00ee00ee00ee00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00aa00ff00aa00, 0xff00ff0000000000],hints 0x87e1f8b23c83a15a2e0e86e0e832149120c8f20c832a38320eb160c8b2398b2768be2f8f2b583a7683a81832798327684e138b244aaa3ca863c83e0e89a0e8920c9de76⟩,
  ⟨44,5,[0xcc000000cc00, 0xee00ee00ee00ee00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00aa00ff00aa00, 0xff00ff0000000000],hints 0x87e1f8b23d83a15a2e0eaea0e832149120c8660c832aa8320eb160c8b27d8b2768be2f8f6e783a7683a81832798327684e138b28b8f6a18f23c89a0e8360c8920cad676⟩,
  ⟨44,5,[0xcc008800cc008800, 0xee00ee00ee00ee00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00aa00ff00aa00, 0xff00ff0000000000],hints 0x8b2438b23c83a15a2e0e86a0e832149120c8620c832a38320eb160c8b2398b2768be2f8f2b583a7683a81832798327684e138b2448f63c83e0e89a0e8360c8920c9de76⟩,
  ⟨44,5,[0xcc00cc00cc00cc00, 0xee00ee00ee00ee00, 0xf000f000f000f000, 0xff00aa00ff00aa00, 0xff00f000ff00f000, 0xff00ff0000000000],hints 0x83a159120e87e1f8b23d83a1b83aaa9122c9122c8320c8f6aa8f63f8b27d8b27683a768381b8be2f8f6ba9d274a067684e138b28b83e0e89a0e8f6a18f23ca86c5c26a19de76⟩,
  ⟨44,4,[0xcc00cc00cc00cc00, 0xee00e000ee00e000, 0xf000f000f000f000, 0xff00aa00ff00aa00, 0xff00ff0000000000],hints 0x87e1f8b23d85a169122c8f69a8f63f83a159120e0701c83aaa8320ca060e84e138b28b8f6948f23ca86a5c26a183e0e89a0e⟩,
  ⟨44,5,[0xf0000000f000000, 0xcc00cc00cc00cc00, 0xee00ee00ee00ee00, 0xf000f000f000f000, 0xff00aa00ff00aa00, 0xff00ff0000000000],hints 0x87e1f8b23d832149120c8660c832aa8b27d8b2768be2f8f6ba832818327684e138b28b8f6a18f23c8360c8920c9de7683a15a7a0e86e0eb160c9da0e83a8183a0f89a0e⟩,
  ⟨44,6,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xee00ee00ee00ee00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00aa00ff00aa00, 0xff00ff0000000000],lhints 5 0xb5ac5ab2a1a2e779da6e9aa6899a5d9123d8b22789a2486e15852138420e8360c 0x16d5b446a88e2015a0b801700b005d575746111404e060182117595ad11892208100a516d5b58c13d40b82f39db2f⟩,
  ⟨44,6,[0xaa000000aa00, 0xcc00cc00cc00cc00, 0xee00ee00ee00ee00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0x322ba2e7b16c2aeaaeab2aaa8aa1a2e869f6799de7699a629764490a3f8f63c8be2c896248861f86e1a8661484e0e8360c098240881c 0x2df2e440d91f7cb40b1161214088565844041151272cb9d55042c46904267dd99041a7da5cb01a94068b2d796568411e9dc78411a9daa901e07c781042a7df80b2c3965a4b2a094a80f142104a4f3a0104a286e069a4d032258c8904135930591932c68841138c94c41228e2a59453691620813a134e0498652⟩,
  ⟨44,5,[0xcc00cc00cc00cc00, 0xee00ee00ee00ee00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00aa00ff00aa00, 0xff00ff0000000000],hints 0x87e1f8b23d83a15a2e0e86e0e832149120c8660c832aa8320eb160c8b27d8b2768be2f8f66a83a7683a81832798327684e138b28b8f6a18f23c83e0e89a0e8360c8920c9de76⟩,
  ⟨44,5,[0xaa000000aa00, 0xc000c000c000c00, 0xee00ee00ee00ee00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],hints 0x86e21a2e1b832149120c8321b8fa0c8b2398b2760701c86eb5832798327684e138b24486e4186a1a8920c9de7687e1f8b23c83a0e8323c832a38be2f8f2aaa863c⟩,
  ⟨44,5,[0xaa000000aa00, 0xcc000000cc00, 0xee00ee00ee00ee00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],hints 0x8ee2ca2e2c832149120c8329aaea0c8b27d8b2760701c9daba832798327684e138b28b86a1a8360c8920cad67687e1f8b23d83a0e83219832aa8be2fa863d8f23c⟩,
  ⟨44,6,[0x5500000055000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xee00ee00ee00ee00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x2c5aaaa1a2e779ba6a9a25d9123d8f22f8b2268921f8721b86615852138420e8360c0a422 0x88c904798844e09f97e4812505c170c67e4a47106268b18631f25924248b7086a51cbf2f51382e0ad4adadabe812⟩
]
def nodesBlock2 : Array Node := #[
  ⟨44,5,[0xee000000ee00, 0x5500000055000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff00ff0000000000],hints 0x832149120c84e138b2778360c8920c070488b01c070238301c070208f01c8ee2ca2e2ca6a0caea0c0781e9dea19d81c83a8b8560e832c58320e83a268420e8bc1c8381c86e0e⟩,
  ⟨44,6,[0xc000c000c000c00, 0xaa00aa00aa00aa00, 0xee00ee00ee00ee00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0xc86e4b52c5aeab5aaaa4a8ea2a868ba1e7a9de6e9b26698a4490a3c8e6358be2c8921f86e15852138420e8302b09017 0x11a11e30879a6843040d20dc3077124833030d10e210489144310364c32068f80c31969980411984e6441208605430d98986430d58a240c29f48a7cc3104904041012490041102497c30d08904030df89d92435064d94c19b4866cc3254926c915310408925b1048d32db0c35935db65751f7db4106df6d3410⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xee00ee00ee00ee00, 0xf000f000f000f000, 0xff000000ff000000, 0xff000c00ff000c00, 0xff00ff0000000000],lhints 5 0x2c5ad6aaa8ea1a2e7a9de448f2398be2c89a248861f86e1a8521383a0c 0x1094e29e25084037001240005b014c53e4f7d4af2d41003cc6535b4934844940d04d6b⟩,
  ⟨44,6,[0xcc000000cc00, 0xaa00aa00aa00aa00, 0xee00ee00ee00ee00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0x323b9ed4b16c3aeab5ab2aaa92a2a868ba1e7e9ea779ba6698a5d9123d8f22f8b2258921f86e198561484e0f83a0d8302607818 0x15c15f3c97dc7053c50d30de3c87934c33c30e30e51459638c314360f3e471a90f3d87185050588c16051548e36030db9596c30d895848f3204cc80f3d24d24851428e30051528c68030d284a4830e08609e7412610a0f1dd70774f3e871c5d52dd14574e1150c398e35d0c35d589d61859249d9dd752455551⟩,
  ⟨44,6,[0xee000000ee00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0x326b16baab2aaa8aa1a6a8ba1e779da719c26f9ba6a9a26498a5d9123d8f23b8be2c8962487e198521383a0d830310bc290781c 0xa2042638e9a082838e1531633898d34c53851661671219e69850c578e22280888e39e81e89905e9817967a29a278d19f1457cd31e14548e2e44cb90e3924d248201d98075775299274515294a48515d95d7627527924a245d791a0e39c82070e3a88205d71dc98768515b9e76c515a9e756289879e62289579e5d23d874f61249475d⟩,
  ⟨44,5,[0xee000000ee00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf0000000f0000000, 0xf000f000f000f000, 0xff00ff0000000000],lhints 5 0xa6a8ba1e86912428fe3c8ee358d22c8921b866158521083a0c128480781c 0x21e647b2ccb9023604245842ea8402600092000da0001800b64149121645284c1500a0⟩,
  ⟨44,5,[0xee000000ee00, 0xf0000000f000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff00ff0000000000],lhints 5 0xaea9aa2e849964490a3d8f23b8d6348b21b856118420e8304e12848094230781c 0xc6a342568423b040468002900018828d834e7c85e1901c045d6846148405216010044ea8⟩,
  ⟨44,6,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xee00ee00ee00ee00, 0xf0000000f0000000, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],hints 0x83a15a2e0e832149120c8320e8fe8b8b28b8b24283ac58322ca2e2ca2e0e0be0e9760c9c20c9826c0d26e9761384e2ca2e1083a1b83a0d83224832a198a6ea86779de1f87e2c8f60e86e0e86e0c8660caaa3d998338f62f8bea18f63c⟩,
  ⟨44,5,[0xcc00cc00cc00cc00, 0xee00ee00ee00ee00, 0xf000f000f000f000, 0xfa00aa00fa00aa00, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x2aaa868ba1a83a06779aa448fe3d8f22f8b22487e1b86615852138420e8360c 0x46b09295b8481200580002780e0061765d45514d8c74415050845d862409d76b42050252⟩,
  ⟨44,5,[0xe00ee000e00ee00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0xb16baaaaa1a2e87a1a77912428fe3d8f22f8b22487e1b86615852138420e8360c 0x11aa201620009e02117418902081404a56e1204801c179b9ad5d575160500641994ad4631d3⟩,
  ⟨44,6,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xee00ee00ee00ee00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00f000ff00f000, 0xff00ff0000000000],lhints 5 0xb72d4b16baaaaa1a2e779c26e99662912428fe3d8f23b8be2c87e1383a0c0dc1a 0x1a66990699863699a61099759a669c22f0b2ccb66f1b90869d1d8a32cca52f8a4a452995552aaa6015552aa73d149⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xee00e000ee00e000, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0xb52c5aeaaaa869aa528b9de6f9aa4490a3f8f63c8ee2f8b21f84e0e8301b 0x39605615855c94a6158510975085d618cb05d5739daf37bdb3210a94ac09a2534319348a508⟩,
  ⟨44,6,[0xf0000000f000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xee00ee00ee00ee00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x2eab16aaa868b9de709be6e98a5d912428f63c8be2c87e1b856138461083a0c0e831 0x67b0dea7a8b91aacab0c0386b34c98cab10681df3abd6a94a9a340d186b70b5ddac7a9ea70c420ce538de576e1b8⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xee000e00ee000e00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x2c5aeab5aaaa1a5a8b9de769764490a3c8c22f8b21f86e1584e118420e8300e 0x11a42725c920ae24b92e134577e02129532188e29ced48c6964212a11c4700155542aa52d8a⟩,
  ⟨44,6,[0xf0000000f000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xee00ee00ee00ee00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],hints 0x8ee2ca2e2c832149120c846428322ca2e2ca2e42aea42aea0c9c20c9821384e2ca2e42aea42a860d83224832779de1f87e2c8f63d9081d8f60c8660caaa2f8bea18f63c1022cb562c83a0eb160c0fe6f9ba6f98aa19baa199a3d0fa3d⟩,
  ⟨44,5,[0xaf00aa00af00aa00, 0xcc00cc00cc00cc00, 0xee00ee00ee00ee00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],hints 0x83a15a2e0e832149120c8320e90a0c8b27d8b27683a7683aba832798327684e138b28b83e0e89a0e8360c8920c9de7687e1f8b23d83a1b83a3d83219832aa8be2f8f66fa863d8f23c⟩
]
def nodesBlock3 : Array Node := #[
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xe000ee00e000ee00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x2c5aeaa1a2e879de76912428f63c8ee2f8b22487e19852138460e8360c0781c 0x6aeab11e22116025d57585c84160583197308616189429d2d34a56f0024f12052631f293dce⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xee00ee00ee00ee00, 0xf000f000f000f000, 0xf000ff0000000000, 0xff000000ff000000],lhints 5 0x2faaeaaaa868b9de709123f8f63c8be2c8921f86e19852138420e8360c 0x28521004e000af00aa2aaa4a90200b0c471108a9040904622388e8429a03028b5cdac⟩,
  ⟨44,7,[0x2200220022002200, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0x2e5b16b5ab2aaa92a2a868ba1e779c6709ba6a99a629825d912428fe3d8e6308be2c8961f86e198561483a0c18c6117c5c15c451081e 0xa89889aa540baa58a2a89409a885c8aa440aaa45d7a884081c85881a9249169595108248aa0410aa8893aa8410aa08a07683406a024076034d6a82497603cf6a12087613cf6a0208a9440eaa65ceaa6410a945d46d42496db34d6c32496d434d6e62086d49cc6d42086e69e671c71271471471c820aaa702a9f410a9fa9faaa41071824971c34d70124971c34d71920871c3cf71e20871c3cf71d723a9f82071a711a9f511⟩,
  ⟨44,6,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff002200ff002200, 0xff00ff0000000000],lhints 6 0x317b16b5ab2aaa92a2a868ba1e779da719c26f9ba6a9a26699262976448f6398c22f8b22587e1b866158521083a0c11043 0x99e79a2cb69e7a62cb0de0e12c685e7832c35962036830900a02c58104022c229928260209908a60a0810a50c39409420c270b2e478e90b2dc79c91791c49c71572449f91711c0c37137240c370a29d08274a29c0823cb26240988b2cf40f3d131b48c6d56cf48f3c30db51b6c30cf50f6c208f8c73c209b8db6d634f70d3d63db71b⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff002200ff002200, 0xff00f000ff00f000, 0xff00ff0000000000],lhints 5 0xb16aaa868ba127a9de769d26f912428fe3d8ee398d6308be2c87e1b8561083a0c 0x2378566b18240c1e679800765ad328d3106614a5d79d2b3294cc0b03839e4c8b19242192⟩,
  ⟨44,5,[0xf0000000f000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff002200ff002200, 0xff00ff0000000000],hints 0x8ee2ca2e2c832149120c8760c832258b2398b2778d63590aa184a0c8960c87e1f8b23d8be2f9da3d83219832768c2308f67683a15a7a0e86e0eb160c83a109de0e9da0e83a3d⟩,
  ⟨44,6,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xdd00dd0000000000, 0xf000f000f000f000, 0xff000000ff000000],lhints 6 0xbdae5b16b5abaacaaa8ba1e779da6e9b66a99e669724490a3f8f63c8c22f8b225892218821f86e1383a0d83055150531444b124471181e0700e 0x28b6cb26b34d22b6da1cb34b195a5276634d166a6675534d115a1175c2cb0dca1c7552cb8aa3c2b643428a43cfb6a34d8a450cb652cb8a5513b642cb86454eb2a98eb2a555b249a47963417a33c17a334d7963cf7a32c0796a007962cb7a3a23b16550b27710b275557d6716816816b19917819818816916⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xdd00dd0000000000, 0xf000f000f000f000, 0xfd00fd00f000f000, 0xff000000ff000000],lhints 5 0xab2aaa2e879de769724490a3c8ee398c22f8b21b83a0c0781c 0x2c6b1ac6b188491c4652cd8d084837c20f7c20f4218f00064718ce718ce3324631d46⟩,
  ⟨44,5,[0x20002000f000f000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xdd00dd0000000000, 0xf000f000f000f000, 0xff000000ff000000],lhints 5 0xab2a8a1e779da4490a3c8c22f8b2218821f86e1383a0c0781c 0x346d1a07219e69084a38463021130000657a94f3192a52d8a68da3109c98c23053d4f⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xdd00dd0000000000, 0xf000f000f000f000, 0xff000000ff000000, 0xff00dd00ff000000],lhints 5 0xb96baad6aeab2aaaa29aa628ba027e9de769ba3c8c22f8b22483a0d8300e 0xc619cc21858252d1d1685c14ad777ad75104815b2ab32946329460002a33a4631d06⟩,
  ⟨44,5,[0x22000000ff000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xdd00dd0000000000, 0xf000f000f000f000, 0xff000000ff000000],lhints 5 0xaeab5aba9aa628b9de769123c8c22f8b2248862087e1383a0d8304f1340e 0xe971a6ab40de39c63620d43319716420c0007039d6c635cc2944308e4b8da368320c⟩,
  ⟨44,4,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xdd00dd0000000000, 0xf200f000ff00f000, 0xff000000ff000000],hints 0x8320e8fe0c88621a022c8820c9120c8ca328feb58360c8920c84e138b2778be319d22f0380e832aa87e1f8b22f8be308f22f⟩,
  ⟨44,4,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xd000f0000000f000, 0xdd00dd0000000000, 0xff000000ff000000],hints 0x8860eaa20e8320e8fe0c832209120c0781e86e0e84e138b2778360c8920c0701c83a1b87e1f8b22f0380e832768be308f22f⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xdd00dd0000000000, 0xf0000000f0000000, 0xf000f000f000f000, 0xff000000ff000000],lhints 5 0x2c5a2e87a1a779da4490a3f8f2308be2c892218821f86e1383a0d8301e0700e 0xcb089703516e548e4365eec108e520d63a5ad431994084a7000736d6ad4218d6b9ed⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xdd00dd0000000000, 0xf000f000f000f000, 0xff000000ff000000, 0xff00f000ff00f000],lhints 5 0xbdac5ad6aaa2e849ea779da6e912428fe3c8ee358d2308be2c87e1383a0c 0x420032cb235a422664235a474217421958465010890a14b429de5794af18c8529945⟩,
  ⟨44,5,[0xf0000000f000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xdd00dd0000000000, 0xf000f000f000f000, 0xff000000ff000000],lhints 5 0xb16b5a2e849ea779da4490a3c8c22f8b22187e1b84e1183a0c0781c 0x12a340e634b9c9084c38465029530000667a94f39d2a52d8a68c42725c9a429053d4f⟩
]
def nodesBlock4 : Array Node := #[
  ⟨44,5,[0xf0000000f000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xdd00dd0000000000, 0xf000f000f000f000, 0xff000000ff000000],hints 0x21190a0c8b23ba2e2c8820c9120c8d63590ab58360c8920c84e138b2778be349da2f0380e8327687e1f8b22f8be308f22f83a0eb160c9722c15a2c9de879de879da2f9da2f⟩,
  ⟨44,4,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xdf00dd000f000000, 0xf000f000f000f000, 0xff000000ff000000],hints 0x8321190a0c83a0ea2e2c8820c9120c8d63590ab58360c8920c84e138b2878be349da2f0380e8327687e1f8b22f8be308f22f⟩,
  ⟨44,6,[0x2200220022002200, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00aa00ff00aa00, 0xff00ff0000000000],lhints 6 0xc3ad6b16c2aeeb5ab2aaa92a2a868ba1e869de769aa6899a448f6398c22f8b2278961f86e198561483a0c16c5916022 0x44d29e48a78d35149115a15d34775a6853454d324544511211c3467124843447d120478411111f79e1031231458c28c41445cd36069080d3576978113d754f5d146056080c3171455cc3201455cb2d910464b2d71045a45a234d8a585634d06439644e50515630c58516430c5841182cb6041162cb0246d65d6⟩,
  ⟨44,5,[0xcc00cc00cc00cc00, 0xdd008800dd008800, 0xf000f000f000f000, 0xff000000ff000000, 0xff00aa00ff00aa00, 0xff00ff0000000000],lhints 5 0xb16b5ab2a1a2e779da448f63c8e6388be2c89e258561483a0c0700e 0x4290919623084447080014c43a890e439a938ce3308c242d10a258938ce3308c293e0f⟩,
  ⟨44,5,[0x2200220022002200, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff00aa00ff00aa00, 0xff00f000ff00f000, 0xff00ff0000000000],lhints 5 0x2bbad6aaa8682a06779da759d2448fe3d8e6308be2c89e1f86e1583a0c 0x2260484328230d186618005514b324d0284a14215573a5079ac60942539dad8be6f⟩,
  ⟨44,5,[0xf0000000f000000, 0x2200220022002200, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff00aa00ff00aa00, 0xff00ff0000000000],lhints 5 0x2c5aeeb5aaaa1a7a779da448f6398c22f8b2278961f86e198561483a0c 0x3192d009c0200134b1305adb4380e07a6a95280701e4f08e21286c00a10140428⟩,
  ⟨44,6,[0x2200220022002200, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf0000000f0000000, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0xb4ac5aaaa1a2e879de6a99a5d912428fe3d8e6308be2c8961f86e198561483a0c1785d1441e 0xa7c9486990858e599648bc231ecb80092ac8b25f18ba94c8152549104dc2a383a170b3ac2a4a922c8ba5856d5dad⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xf2002200f2002200, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x28ba1e86a0e779123f8f6398c22f8b22587e1b866158520e8301e 0x11282a26891184608de1089c1404284b130000c284e704050139d2d1184652a4d094315adb0⟩,
  ⟨44,5,[0x2200220022002200, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xfa00aa00fa00aa00, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0xc82aaa868ba1a779123f8f6398c22f8b22587e1b866158520e8301e 0x1124239d2d1184608de1089c1284344b130000c25adb0405018a6a911846528280a270⟩,
  ⟨44,6,[0x2200220022002200, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00f000ff00f000, 0xff00ff0000000000],lhints 5 0xb86c5ad6aaa868ba127a9de709ba6a98a609764490a3f8f63b8e6358c22f8b21f83a0c1805914c43 0x20781d87d1ca581e07211fe71d67bd6f79a94fedf19b98c76f1ade35e26f1ade25b709fe71d2d48bc0f97adeddd08⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xdd00d000dd00d000, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x2c5aaaa1a2e77912428fe3d8d6308be2c89a258921f86e158521383a0c0700e 0x19aa31166210e229b26c38e4350b022119478d63a0922b5296421900847000057bc1ad73a14⟩,
  ⟨44,6,[0xf0000000f000, 0x2200220022002200, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x2eeb16b5aaaa1a2e849ea779c26f9aa60912428f6398c22f8b21f86e158460e830621501e 0x86b91e97a4bb22589a0007252b6a2109690e43e5adcadb40a78921c8786e7bc514a7a5e971063d53546e5b98c852⟩,
  ⟨44,5,[0x2200f2002200f200, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x2c5ad6aaa868ba12779da448f2398c22f8b22587e1b8561483a0d8301e 0x19643091c108ec14b130000c31062139d2a198660a83452daa725c9198660a036ac27053d54⟩,
  ⟨44,6,[0xf0000000f000000, 0x2200220022002200, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],hints 0x8ee2ca2e2c832149120c846428322c8e62c9de358d642ad625832258321f87e2c8f63d9085b8f60c8660caaa308f6771562cbf22c97642112428322583225a86778be2f19a2cb962c83a0eb160c9de879de8799a3d1963d9aa6f1926f⟩,
  ⟨44,5,[0x2f0022002f002200, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0xa2e879de769c65c912428f6398c22f8b22587e1b866158521083a0c 0x92a100de0005c04b133105c14010039d2d0b82d014125adb2826290982e020089d27452a4d⟩,
  ⟨44,5,[0x2200220022002200, 0xaf00aa00af00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x2bbaaaa1a2e879de76912428f6398c22f8b2278961f86e198561483a0c 0x8e61009e0005c04b13140501380e03192d0942d010155adb2826c90a02801c07a414a⟩
]
def nodesBlock5 : Array Node := #[
  ⟨44,5,[0x2200220022002200, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xf000ff0000000000, 0xff000000ff000000],lhints 5 0x2aaa868b9de5c9123f8f6398c22f8b22587e1b8661483a0c19c1e 0x24721886e1088f100061a5898a04810cc331ce9688a2a2db11986682429120489c54a⟩,
  ⟨44,4,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xf200ff0022002200, 0xff000000ff000000],lhints 4 0x2aa9de3f8f6308b2258821f86e1984e0e8301e 0x252512c171180052933d31812525669b141e3a3d⟩,
  ⟨44,7,[0x4400440044004400, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0x2f0b16b4ab2a4a8aa1a2e779da719c26e9aa6698a609764490a3f8f6388c22f8b2258921b8561484e1083a0d830801f87b1e0761c4701b86d1ac690700e 0xc0fa4fc2c5d3c2ca69c0f5cfc0d78dc2b5d2c2b79ec0d5cd30d74d2ef3cf2af75c24d3cdc305d1c2aa51c2a5d7c30a6986a5108613cf84851486a3cf86a58e86134d84759586a34dc185d7c2e79ac2e5d7c187981983c18a75011673cf898514127340898b400d834d8a7b678e38d98e3aaa8d88d8c3079ec265d7c2679ec305d78df5148e33cf8c25148e33cf8e0b6d8e334d8e5b6d8e334d8e18e8c26aa88e48dbc26618⟩,
  ⟨44,6,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff004400ff004400, 0xff00ff0000000000],lhints 6 0x31bb16b4abaaca8aa1a2e879de769c6709be6e9aa6898a5d912428fe3d8e2308be2c896248861c86e1484e0e8360c1a80e 0x9934db30c6d34e630c1df1e33098df7c73075d71076c40930a13068534c230209a0a266289a8826420920a51c79524421c274c1607c580c31d7dd81581d55d7557605608071dd55d7471e056074b0de08278b29d08234c3244cf90c30d4cd35835c51c71640d58d34121c1c771670d1c770200d88034209c89c36035774e5e080d74d⟩,
  ⟨44,5,[0x5500000055000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff004400ff004400, 0xff00ff0000000000],hints 0x83a159120e832149120c8320eab20c84e138b2778420e89a0e8360c8920c872228b21c0701c83a2f0380e8321c8be1c86a1a86e21a2e1baea0e86e0c8fe0c9de1b86ea19da1b⟩,
  ⟨44,6,[0x4400440044004400, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xfa00fa00fa00fa00, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x2f0ab2a1a2e839de769c26e9aa659824490a3d8e2308be2c8921b8561484e1083a0d8306c 0x67c8d5c500681a02680423787612955920d03a6b53105215354b1a068b2c2bc334b82a0a40d03a4e53886a1bddcb⟩,
  ⟨44,5,[0x4400440044004400, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xfa00fa0000000000, 0xff000000ff000000],lhints 5 0xb2aa1a2e779da709123f8f6388c22f8b22486e15852138420e8360c0700e 0x209520890108f111489218cba8c4a104244adcb600029b6cc491248ae2bb8a42a51ec⟩,
  ⟨44,6,[0x4400440044004400, 0x5000500050005000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x2acaaaa1a2e789de769c26e9b26a9824490a2f8b22486e15852138420e8360c0700e 0x88b904770844688c65dca4490625096e5b82122402a5b1472dcb691a4d0a189618c72dcb4912478a62ad7348c270⟩,
  ⟨44,6,[0x4400440044004400, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00aa00ff00aa00, 0xff00ff0000000000],lhints 5 0x2c5ab2a1a2e819e6789de769ba6a9a25d9122f8b2268921b8561484e1083a0d83022 0x16d5b467b8d03099a1c843908f41295778e31020d43105215b56d63072b06a1953126adab741f070de3c87219cc12⟩,
  ⟨44,6,[0x4400440044004400, 0x5500000055000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0xb16aca868b9de769ba6a976448f6388c22f8b2268921b8561484e1083a0d8306a0700e 0xa9c146890c65d8ce76e0c56148358db06b82570003d3f2ec370d51763d8e99ae6ce9364d99445d0f43bde2e9d2b4⟩,
  ⟨44,6,[0x4400440044004400, 0xaa00aa00aa00aa00, 0xf000f000f000f000, 0xfc00fc00fc00fc00, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0xc2aefb4eb5ad2aca92a1a2e87a12779da6e9aa6598a4490a3f8f2398e22f8b2248821d86e1584e1083a0c1d4741c81c 0x15d15f3487dd74534594d1de94778d36590378918214590925e1453142e034b81450c34c31328114591348c14555510c78438d36150f84d34e50e38501924064514e24965e64e5ce39e3995d964c30e80e38c31981971442234d89451c34d88925c14570926214592369c79a5a081c30c7206e330c62345c38e⟩,
  ⟨44,5,[0xf0000000f000, 0x4400440044004400, 0xaa00aa00aa00aa00, 0xfc00fc00fc00fc00, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0xab28ba12779da448fe3c8e6388be2c8922086e1584e1083a0c1cc1c 0x19a832954120ce35314b000678ad716aa0a38ce3949cb4220978c425a5314cea9⟩,
  ⟨44,4,[0xf0000000f000, 0x4400440044004400, 0xaa00aa00aa00aa00, 0xfc00fc0000000000, 0xff000000ff000000],hints 0x1384ea020e0701c83a1b0d83684e2f0781e86e0e8e613912138f22f8fe0c832139120c0380e8327683277ab20c⟩,
  ⟨44,5,[0xfc000000fc00, 0x4400440044004400, 0xaa00aa00aa00aa00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x2c5ad6a1a2e849de769123c8e6388be2c8922086e1584e1183a0c0781c 0x19a63421e920ec35314b0006b4ad306a9ea086238a64972ca554ce3109345c170a46b1⟩,
  ⟨44,5,[0x4400440044004400, 0xaa00aa00aa00aa00, 0xf000f000f000f000, 0xfc00fc0000000000, 0xff000000ff000000],lhints 5 0x2fdbbeb5ad2aeab28ba1e849de769ba4490a3f8f2398be1b84e0e830730d81e0700e 0xf63d0c6a5a87318ad290c6cb585314ae2d4e7ab9c5395260c101818c9421271ddc3b9ce972605026a0494b0ac308144c28a11831a2e560e7c39d139e358cca59d651295fa5c529⟩,
  ⟨44,6,[0x4400440044004400, 0xaa00aa00aa00aa00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00cc00ff00cc00, 0xff00ff0000000000],lhints 6 0xc3eefb5ac5b0eb5ad2aeab2a2a868ba1e849de769ba6a99262912428fe3d8e2308be2c89a258922186e1484e0e8360c1dc0e 0x9cc15d9c574c3275c11dc1e030881c70730751410774409309e3067934c23020a608a7432a62427420920a41c79124421c234c3214cf84c30d4cd35d35858e61d60d58d34b2d81c760b2cd1c760200d7c03420987d86534e330c8d34d930c5e58997595471d92cb6471e52cb65f65b0826df6990825e541934d⟩
]
def nodesBlock6 : Array Node := #[
  ⟨44,5,[0x4400440044004400, 0xaa00aa00aa00aa00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00cc0000000000],lhints 5 0x2feb16c3b0aaeab28ba1e849de769ba64912428fe3c8e62f86e1383a0c0d81e0700e 0xb42d8c6b52853148d254c6ab5a43108c264a5cb164291061dda3b98c86a1050c0e1814a839e04022a041090ac22d4e0c6c35b1319c7144a289cfa296358cc849d651211fa54508⟩,
  ⟨44,6,[0x4400440044004400, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf0000000f0000000, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x2c5ab2a1a2e869de769ba6a98a5d912428fe3d8e2308be2c8921b8561484e1083a0d830790700e 0xa9d946898c658ed9b648be19cecd98aa2906b1f2b7e31ec6842550003c375a6bb8d9b26c51545e8fa3a5856ce60d⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xf4004400f4004400, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x2aca868ba1e869de769123f8f6388c22f8b22486e15852138420e8360c0700e 0x222c48ae2b4912411e22112021630231975291249ceb7189425b96c08489651ec00052636ec⟩,
  ⟨44,6,[0x4400440044004400, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00f000ff00f000, 0xff00ff0000000000],lhints 5 0x2efb16baa868b9de769c26a99a629824490a3f8f63b8e2348c22f8b21383a0c1f47c 0x1c571545b1463715c5109b961085b5e1abb70dbdf3ab9525304c689914350c6a1ee6715c504a726e1b87e679ad566⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xbb00b000bb00b000, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0xb16baab2aaa8696a2e779da629123f8f6308be2c89e218821f8761b84e0e8301e 0x2226439dea291c418d5300095a52f59aa6a10b0408737856523194b591248ad715b2ab6ad76⟩,
  ⟨44,5,[0x4400440044004400, 0x5500500055005000, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],hints 0x7048a2c1c038399100e0381c8fc0e0d8368b28b0801c8981c0440e8900e8be2c8e22c86c1c8d01c9d80e8bc0e8be948c22f9122c87e1f9081c8701caa80e8640e9de778f62f9962f⟩,
  ⟨44,6,[0xf0000000f000, 0x4400440044004400, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0xb16a1a2e779da709be6e9aa629824490a3d8e2308be2c86e1584e118420e8307f1c81c 0x88c920a828db21ceac948926b61d29aa580044dd6bbb34b82a0a491248eedbc61cb82a0a7906396a9a5dd779d455⟩,
  ⟨44,5,[0x4400f4004400f400, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0xb16b5ab2a1a2e779da448fe3c8e2308be2c8821b8661584e118420e8301c 0x11a624a60a209e22955318902a5ab45354b0004839d715b1cb82a0a40902086b794ad45c571⟩,
  ⟨44,6,[0xf0000000f000000, 0x4400440044004400, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x2f0b16baab2a1a2e779da6f9ba6a98a4490a3d8ee388d2308be2c8921484e1183a0d830822040e 0x1eaca86890cd119ceacc791d10691a9ca5adb758003bb34b92a4a8f23cd8f63c620b12bca297a39eababaeeba5836⟩,
  ⟨44,5,[0x4f0044004f004400, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x2baab2a1a2e879de769123f8f6388c22f8b2248861c86e1484e1183a0d8300e 0x3a6a709a2109201295733ccf6105415b96c41e4700032636cc8ae2b18cf8b86e19d276931ec⟩,
  ⟨44,5,[0x4400440044004400, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xf000ff0000000000, 0xff000000ff000000],lhints 5 0xab2a1a2e779da448fe3d8e2308be2c8921b852138420e8360c0700e 0x28932088f108f011488218ca98c4910424429aa580028b28b4110482a0aa8aa2949cb⟩,
  ⟨44,7,[0xa000a000a000a000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0xb1ec5ab2aaa92a1a2e87a12839ea779da719c26f9ba6a9a66698a609764490a3f8be2c8821f8761b8561383a0c2c4af2a8a525c9623c86214840781c 0xbcda4dbeb50fbeba69bcd50dbef613bed513bed618bef51486d5d16ae34d86e5d66ad34dbe450ebeaa4ebea514be4a642ea4012a434126441022a34d6a4b64868ba5868b676a4ba4be3512bec612bec514be361872c34072340072334d72c410723723861b6d861766723aa372c92472caaa723923bef707be2514be2be2bef51471970676034d70570475934d71a70cbe2b4c71b70375e92471f70275b924861855be28d5⟩,
  ⟨44,6,[0xaa00aa00aa00aa00, 0xec00ec00ec00ec00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0x307b52c5ab2aaa92a1a2e879de769ba6c9aa6999a60912428fe3c8be2c8922087e1d86e188561383a0c0781c 0x8836c389d30589d6db88330388b44a89f30a89f45188b30b84b4084a00c386040f48b0c389930489c6c489c30c8996d95dc1c15d90c15d91c75dc0c35992c259a80285a2cb5d981988e30989e44989e30c88e44e4ce0c04d81c04d80c34ce1c74d82c684e7c684e2cb5187d855870d54e64d54e70e558658⟩,
  ⟨44,6,[0x4c004c004c004c00, 0xaa00aa00aa00aa00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0xcaaefb16acaaaa4a8aa1a2e879de769a666996629824490a3f8f22f8b22487e1b8561484e0e8301e0700e 0x84464485c2c785c6598442c484340385b2c685b4108432c38033c345f10481f3ce44310384c2c985d40985d2cb84c40c50c10151620151610450c2085160c080c78080c0c35567968572c585a64585a2cb85765749a20249710249720849a1044977974980c34d878a4d70c349775749a30c49a74d49730c⟩,
  ⟨44,6,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff00a000ff00a000, 0xff00ff0000000000],lhints 6 0xc56d9b16acaaaa4a868ba1e84a067a9de769d26f9a6669824490a3f8b22087e1b8561383a0c2388d228870781c 0x8c77078de3498de71c8c73478e340c8e034c8e04108e334d5203c65211c65213ce5201c78d73488dd7088dd34d8d771715d2811171c10d728a09d1c745781789b85889b81a4578578d634b8df40b8df34d8d641049f1c08962804961c749f28a4964958998158994d94d681649675649f5d749f75d4965d6⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc008000cc008000, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff00a000ff00a000, 0xff00ff0000000000],hints 0x20e8568b83a20882448b20c832ba83a1384e2ca2ea183a26a5a96ab2a12262cc562c86e0e982ac9beac9de7787e1f8b2440701c83aaa9d274a06769da94a86769da6622276⟩
]
def nodesBlock7 : Array Node := #[
  ⟨44,4,[0xcc00cc00cc00cc00, 0xee00aa00ee00aa00, 0xf000f000f000f000, 0xff00a000ff00a000, 0xff00ff0000000000],hints 0x83a15a2e0e882209122c8320caea0e87e1f8b2440701c83aaa9d274a067684e138b28b83e0e89a0ea5a96ab2a19de76a8676⟩,
  ⟨44,4,[0x33007f0000000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff00a000ff00a000],hints 0x8320c8fe0e0781e86e0e9de7aa12770701c83a1b9d274a06769da77a86768560ea2e0e882209122c84e138b27787e1f8b244⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff00a000ff00a000, 0xff00ec00ff00ec00, 0xff00ff0000000000],hints 0x22cc562c2321b8868b86e0e83a20882448b2d9ab2ac9be1d86e3f86e2c9fa2c9dea19de1b9de269de7aa127787e1f8b24422e769dad98721b89e1b9d274a06769da77aaa76⟩,
  ⟨44,4,[0x5500440055004400, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff00a000ff00a000, 0xff00ff0000000000],hints 0x7048a2c1c882209122c0380e8bc1c0d8368b2770801c86c1c9de7aa12779122c87e1f86c1c86c1c9da819d2749da949de76⟩,
  ⟨44,4,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff00a000ff00a000, 0xff00ec0000000000],hints 0x83a15a2e0e882209122c8320c8fe0e84e138b2770781e86e0e9de7aa127787e1f8b2440701c83a1b9d274a06769da77aaa76⟩,
  ⟨44,5,[0x4c0000004c00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff00a000ff00a000, 0xff00ff0000000000],lhints 5 0x2c5aeaacaaaa1a2e84a067e9ea779da749122c8821f86e1583a0c0781c 0xc9119ce9408551a1c8605836360c3190900073529eb5b26b4451128e96a5a4c9ae6b⟩,
  ⟨44,5,[0x3300200033002000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff00a000ff00a000, 0xff00ff0000000000],lhints 5 0xb16acaaaa1a5a94a2e819de769d2448fe2c89e218821f8761c86e138381e 0xd1119cec5146b1884a880749ced43194c20d236b60e74a8e8aa2a086f6bd9ef755d5⟩,
  ⟨44,6,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00a000ff00a000, 0xff00ff0000000000],lhints 6 0x315b16acaaaa1a2e87a1a84a0e819ea799de769c6709be6e9a66899a6498a5d9122f8b22087e1383a0c2549424890 0x91f7d524955f7e424991f7e424991f7e42494d316454590b22224888b2e42498931234c48d38e24e28938a34e38d38e24e25c91a07c68092577d78128173575ce5e03608038170975c15e00205e25de8d97a27178d75891e12c78492562cb84c29650a5905a152184f8563d658f5a13da58f59d8987516d68965a05a15d78608165d6⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc000000cc000000, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff00a000ff00a000, 0xff00ff0000000000],hints 0x83a15a2e0e882209122c8320caea0e84e138b28ba860e89a0ea5a96ab2a12462cc562c86e0e982ac9beac9de7787e1f8b2440701c83aaa9d274a06769da82a86769da6622276⟩,
  ⟨44,4,[0x3300ff0000000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff00a000ff00a000],hints 0x8320c8fe0e0781e86e0e9de7aa12770701c83a1b9d274a06769da77a86768560ea2e0e882209122c84e138b27787e1f8b244⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff00a000ff00a000, 0xff00cc00ff00cc00, 0xff00ff0000000000],hints 0x8b3158b09386e21a2e1b83a0e86e6f882209122cb66acab26f8320c8fe1b8b27e8b277a867786e7786e269de7aa127787e1f8b24422e769da818721b89e1b9da79a0e769da77aaa76⟩,
  ⟨44,4,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff00a000ff00a000, 0xff00cc0000000000],hints 0x83a15a2e0e882209122c8320c8fe0e84e138b2770781e86e0e9de7aa127787e1f8b2440701c83a1b9d274a06769da77aaa76⟩,
  ⟨44,5,[0xcc000000cc00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff00a000ff00a000, 0xff00ff0000000000],lhints 5 0xb16baab2aaa868ba12819fa7a9de769d26f9122c8821f86e1583a0c0781c 0x6490ce74a042b0d0f4342168dae8b4c6424001d16b8318da31124494328eb7ade6da328c⟩,
  ⟨44,5,[0x3300000033000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff00a000ff00a000, 0xff00ff0000000000],lhints 5 0x2c5ab2aaa8696a528ba0e819e6779da448fe2c89e218821f8721b84e0e8301e 0x2224439d8a0856418d5200095a52f53194c291246be2d6cead92a4a10b17c5dce6d9b0⟩,
  ⟨44,6,[0x5f0000005f000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff00ff0000000000],lhints 6 0xcbef2b16acaaaa4a8aa1a2e879de769a66899a609764490a3f8f63c8c22f8b2258921f86e158521383a0d8301e0700e 0x94350395f34795f51494334395b34695e74695e34d95b75b59b30491c0c391c30b59b0c394e34a96150a96134d94e50e5da0c090e88090e0c365a89a5ce78e5d16cf5d17905ce6ce94574596034896075d9453455458c59130c39138d25450c35456c25497825496c9545785549681545381605685909389⟩,
  ⟨44,6,[0x5f005f0000000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000],lhints 6 0x2f7b1ec5ab2aaa92a1a2e879de7699e66986609724490a3f8f63c8c22f8b2258922087e1b8561383a0d830a428ca12789d268992601e0700e 0xb0b6cb7aa34db2a6da78b34b2a64022633422234101e634d7a350cb242cbb245137a32cb81634182240182234d8164108222c0b16a40b162cbae2a628169968198d78199988168d61959cf76534d1659e575534dad5a52adc2cbadca5c7d52cb12598e7558ce0d59957658e3adca11ad5591ad5a1585c596⟩
]
def nodesBlock8 : Array Node := #[
  ⟨44,5,[0x5f005f0000000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xdf00df00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000],lhints 5 0xaf2a4a868b9de769123f8f62f8b2258862087e1b83a0c0700e 0x86c110641a048110641a04813de108c80009ca5ad4a5ad471c866134504c5332952a⟩,
  ⟨44,5,[0x5f005f0000000000, 0x80008000cc00cc00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000],lhints 5 0x2aaa868ba027d9de768fe3d8be2c8961b8561383a0c0700e 0x86b1186619c4710423300026254a4986619c47135aa4a9251c06f140448c1c992508⟩,
  ⟨44,5,[0x5f005f0000000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff005f00ff000000],hints 0x20e83a0cab2ac8320ca6aba8309c9de7726e989de77a860d832248322f9da768be2f9da768bc0e03a0c9da2f8c23c8be2c8b2a4a2e9ea020ca2e0c9fa77a86779f62faaa2f⟩,
  ⟨44,4,[0x5f005f0000000000, 0xaa00aa00aa00aa00, 0xcc004c00cc000000, 0xf000f000f000f000, 0xff000000ff000000],lhints 5 0x2baaaaa1a2e84a027d9de768be1584e0e8301e0700e 0x192031092448d8308487000683a5c7311a458da3295c951de7⟩,
  ⟨44,4,[0x3300130033000000, 0x5f005f0000000000, 0xaa00aa00aa00aa00, 0xf000f000f000f000, 0xff000000ff000000],hints 0x941e8c81e0801e83c1e0380e832761281ea2c1e0ec3b8e60c0d83684e2f8381e9dc1e9de0c9ea0c9da2f9da2f9de139fa13⟩,
  ⟨44,5,[0x5f005f0000000000, 0xa0000000ff000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000],lhints 5 0xb1ebaa92a1a6a98a2e779da609123c8c22f8b2248821f8561383a0d8300e 0x6760ca10a08280a9ef500017a96c50c6e0dc30a428f53d45aa4e1684844c0c64aa29⟩,
  ⟨44,5,[0x5f005f0000000000, 0xaa00aa00aa00aa00, 0xcc000000cc000000, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000],hints 0x20c83aba832a183a268360c8920c86e0e9820cbde0c9de770701c83a2f0380e832768be308f22f8be662822f8560ea2e0e8820c9120c84e138b28b8b25c27e2c87e1f8b22f⟩,
  ⟨44,4,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xdf005f00cc000000, 0xf000f000f000f000, 0xff000000ff000000],hints 0x8320eaea0c8560ea2e0e8820c9120ca420e89a0e8360c8920c84e138b28b0701c83a2f0380e8327687e1f8b22f8be308f22f⟩,
  ⟨44,4,[0x5f005f0000000000, 0xcc00cc00cc00cc00, 0xee00aa00ee00aa00, 0xf000f000f000f000, 0xff000000ff000000],hints 0x8320eaea0c0701c83a2f0380e8327683e0e89a0e8360c8920c8c22f8f22f8560ea2e0e8820c9120c87e1f8b22f84e138b28b⟩,
  ⟨44,5,[0x5f005f0000000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00cc00ff00cc00],lhints 5 0x2a1a2e7e9de76972448fe3d8be2c89e26896218821f8721b83a0c2880e 0xc624a44223c569926a489226b9cd29164000526b9cd0b191412a438a02a31933198d⟩,
  ⟨44,4,[0xa0008000ff00cc00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000],hints 0x1384e8ee0c1284a86e130ec3b8960c120488561b0380e832760d83684e2f83a0e86e158960c8820c9de138b2138f62c87e1f⟩,
  ⟨44,5,[0xcc000000cc00, 0x5f005f0000000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000],lhints 5 0xaeaa1a2e7e9de769123d8be2c8962087e1b8560e8301e0700e 0xc93189e448d230848b0006e5b18b2922440da38294f39d4b3112348e4f62d8b54551⟩,
  ⟨44,5,[0x3300000033000000, 0x5f005f0000000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000],lhints 5 0xb16a1a2e779da448fe3c8c22f8b227892218821f8721b84e0e8360c0780e 0x8d1104d618962399860005373e0e51aa648a42295b5421ae212e2b8a949ba6eab6ad⟩,
  ⟨44,6,[0xa000a000a000a000, 0xaa00aa00aa00aa00, 0xcc000000cc000000, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],hints 0x83a15a2e0e882209122ca6a0eaea0e84e138b28ba860e89a96a5aaca84a88b2c78b21b83a60ab270ab2779de1f87e2c9101c0720eaaa76ab2839da94a86769da6629e7627a2cb422c9760e2420e8320c98aa19baa198a6929a658be2f⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xec00a000ec00a000, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x2baab2aaa869aa5a94a2e839de769c66f9aa5c9122f8b2268821f86e1584e0e8301c 0x1126239d69b0b42625e9289c2085d918d33b8902ad7378c5b73192b0005886650529b0852f0⟩,
  ⟨44,5,[0xa000a000a000a000, 0xcc00cc00cc00cc00, 0xee00aa00ee00aa00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],hints 0x83a15a2e0e882209122c8aa0eaea0e87e1f8b2440701c83aaa9daaca0e7684e138b28b83e0e89a0ea5a96ab2a19de76a86762822cc7e2c9760e2220e8320c8be2f98aa19aaa1⟩
]
def nodesBlock9 : Array Node := #[
  ⟨44,5,[0x3300ff0000000000, 0xa000a000a000a000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000],hints 0x21d83a3f8381e07a1b83a779ea849dc1c0720e86e76ab2839da77a86769760e2460e8320c98a77bee778be2f8560ea2e0e882209122c84e138b27787e1f8b2448b25c2a62c⟩,
  ⟨44,4,[0xaa00aa00aa00aa00, 0xb300ff00a000a000, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000],hints 0x8760e8fe0e0781e86e0e9de7aa12778560ea2e0e8320c9122c84e138b2770701c83a1b9da8ea0e769da77a867687e1f8b244⟩,
  ⟨44,6,[0xa000a000a000a000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00cc00ff00cc00, 0xff00ff0000000000],hints 0x8b2c78b0ad86e21a2e1b83a0e882209122c9c2acab2608761b8fe1b8b27e8b277a867786e7789a779ea849de1f87e2c910ac9da7699a1c86e2786e76ab2839da77aaa762862cb822c2ae6f992699761b24a1b8320c98a779ba778be2f⟩,
  ⟨44,5,[0x5f004c005f004c00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],hints 0x86e21a2e1b832149120c832118fe0c8b27e8b27786e7786e268360ca120c87e1f8b22f8721b89e1b0380e832768be30aaa2f8b2718b25c83a0e86e68ab20c8960c9dea19de659da2f8f62f⟩,
  ⟨44,5,[0x5500440055004400, 0xa000a000a000a000, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],hints 0x7048a2c1c882209122c8741c8c41c0d8368b2770801c86c1c9de7aa12778be2cac62c8bc1c22c1c0380e8be309ba2f9122c87e1f86c1c86c1c9da83ab2769da949de768f62f⟩,
  ⟨44,5,[0xa000a000a000a000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00cc0000000000],hints 0x20e8568b83a20882448b21d83a3f83a1384e2c9dc1e07a1b83a779ea849de1f87e2c9101c0720e86e76ab2839da77aaa769722c2ba2cb320e24e0e8320cb46779ba778be2f⟩,
  ⟨44,4,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ec00a000a000],hints 0x83a15a2e0e8320c9122c8760e8fe0e84e138b2770781e86e0e9de7aa127787e1f8b2440701c83a1b9daa7a0e769da77aaa76⟩,
  ⟨44,6,[0xcc000000cc00, 0xa000a000a000a000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],hints 0x83a15a2e0e882209122ca6a0eaea0e8b27e8b27707a7783a779ea849de1f87e2c9101c0720eaaa76ab2839da77aaa7628e2cbb62c9760e2520e8320c98a779ba778be2f8b28b8b28b86e0eab2c5ab2c5a8677aaa76aaa769a6622c26f⟩,
  ⟨44,5,[0xa000ec00a000ec00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0xb16baa868b9fa7a9de769aa689123d8f22f8b2258922087e1b8661583a0c0781c 0x192c3421ea50f035d573086635512939d6e0006e29552939ad5d97680cc310959bce33631d2⟩,
  ⟨44,6,[0x3300000033000000, 0xa000a000a000a000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],hints 0x86e21a2e1b882209122c8761b8fe1b84e138b28b07a1ba8696a5aaca861f87e2c9121c86e2786e76ab2839da94a86762922cbe62c9761b2561b8320c98aa19baa18be2fa2e2ca2e2c83a0eb16acb16ac9de779daaa9daaa9a65d2ca6a⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xb300a000b300a000, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],hints 0x86e21a2e1b882209122c8761b8fe1b84e138b28b0781e86ea1a5a96ab2a1a2e2ca2e2c83a0e9be1b8320cb16ac996a19de7787e1f8b2448721b89e1b9da79a0e769da88a86768be2f9daaa⟩,
  ⟨44,7,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xfa00fa00fa00fa00, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0x2daad2aca92a2a868ba1e86a0e779da719c26f9ba6a9a66698a609764490a3d8f2388c22f8b2258921b8561484e0e8360c350d3344ce328c42e4b62d06b07813 0xc8eb0ecaf551cafb2cc8e54ecb2555ca6ca6ca6555cb294b96438e94a49296538e95d492c8c70ccae550cae71cc8c54c94c6cc94938e9656db94c38c965970c8c98cca854fcadb0fcad555ca8b2822d4811e83811a849216d38e9688e896b8ab96b96b9687e896850d96b30c96b51396830cc96555cb1718cb1555c9671611638e82a4920ea38e8164929657a7c9699696530c956956965869096b5681aa1701ab59816a16⟩,
  ⟨44,6,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xfa00fa00fa00fa00, 0xff000000ff000000, 0xff00aa00ff00aa00, 0xff00ff0000000000],lhints 5 0x2dfb66b5ab2a1a2e87a1a83a06779da709be689825d9122f8b2268921b8561484e1083a0d830b5 0x16d5b467c8d035f9608c64e1c06e099a19042f08fa1d84a55d394a708350e98c50414856d5b58c1deb3986f6bd354⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xfa00fa0000000000, 0xff000000ff000000, 0xff00aa00ff00aa00],lhints 5 0x2d9b2ab5a868b9e6779da709122f8b22789a2486e15852138420e8360c 0x1c4d5ada61484e002a0158002b414842831244422e010200c609ea5b56d0440f7c26f⟩,
  ⟨44,6,[0x5500000055000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xfa00fa00fa00fa00, 0xff000000ff000000, 0xff00ff0000000000],hints 0x83a15a2e0e8b2f88b0b8838b783a5d832149120c8320ebca0cab20c84e138b2778420e89a0e9de87a1e778360c8920c8b2388b22f8d20e8beaa8be0c8bec88be308f22fa2e2ca2e2c86e0e9be6f9c25d9820c9c20c9dea19dea1a1a2f⟩,
  ⟨44,5,[0xfa000000fa00, 0x5500000055000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff00ff0000000000],hints 0x832149120c84e138b2778360c8920c070488b01c070238301c070208681c86e21a2e1b86e0cb160c0781e86ea19d81c83a8b8560e832ac8320e83a268420e8bc1c8381c90a0e⟩
]
def nodesBlock10 : Array Node := #[
  ⟨44,5,[0x5500000055000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xfa00fa0000000000, 0xff000000ff000000],hints 0x21583a8b83a0c83af28320c852448321083a2683a1384e2c9de0d832248301c83a2f87e1f8b22f0380e832c88be308f22f86e0ea2e2ca2e2cb2a0c9c20c9dea19dea19da2f⟩,
  ⟨44,6,[0xaa00aa00aa00aa00, 0xcc000000cc000000, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xfa00fa00fa00fa00, 0xff000000ff000000, 0xff00ff0000000000],hints 0x83a15a2e0e8b2d08b0c2838c183a5d832149120c8320eaea0cab20c84e138b28ba860e89a6ea86a198a0d83224830bf8b2da8b21b838be9be7098a6083270832779de2c8e22c8be0e8d20e8be768be0c8be838be308f22f8be662ea2f⟩,
  ⟨44,5,[0xcc00cc00cc00cc00, 0xee00aa00ee00aa00, 0xf000f000f000f000, 0xfa00fa00fa00fa00, 0xff000000ff000000, 0xff00ff0000000000],hints 0x83a15a2e0e8b31f8b0bd838bc83a27832149120c8320eaea0cab20c8b2388b22f83a1b83a2f9da2f8be6a8322f8328384e138b28b8420e89a0eb5ea1a866a8360c8920c8c22f8f22f⟩,
  ⟨44,4,[0xfa000000fa00, 0xcc00cc00cc00cc00, 0xee00aa00ee00aa00, 0xf000f000f000f000, 0xff00ff0000000000],hints 0x1384e9120c070488b01c070238301c84e138b28b8360c8920c0781c8681c83a8b8560e8329a8320e8bc1c8381c83a2683e0e⟩,
  ⟨44,4,[0xcc00cc00cc00cc00, 0xee00aa00ee00aa00, 0xf000f000f000f000, 0xfa00fa0000000000, 0xff000000ff000000],hints 0x8560ea2e0e8320eaea0c832149120c0701c83a2f87e1f8b22f0380e8327683e0e89a0e84e138b28b8360c8920c8c22f8f22f⟩,
  ⟨44,5,[0x3200fa003200fa00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x2baab2a1a2e87a0e779da7199662972448f2388c22f8b22486e158521383a0d8301e 0x19ae3095c108f4121134000e3105014b12a19c670a83552daa4c92f19c670e431c52d454d50⟩,
  ⟨44,5,[0x3300ff0000000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xfa00fa00fa00fa00, 0xff000000ff000000],lhints 5 0xab28ba1e839de769724490a3c8e2308be2c8921b8561484e0e8360c3001e 0x11044088f15c4002093ad6631244441112589745b1cb392c40a95130a02295536a94b⟩,
  ⟨44,4,[0xaa00aa00aa00aa00, 0xc8000000fa00fa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000],hints 0x1384e90a0c0781e86e0e0ec3b8820c83a1b83a158322083214a1e2c84e131204883a1b0e4398321f0d83687e2f87e2f8b21f⟩,
  ⟨44,5,[0xfa000000fa00, 0xaa00aa00aa00aa00, 0xcc000000cc000000, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff00ff0000000000],hints 0x1384e9120c84e138b28b8360c8920c86e21aa21b86e0c9c20c0781e070488b01c070238301c072308681c0721b2f01c83a8b8560e8329a8320e83a26a860e8a20e8bc1c8381c⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc000000cc000000, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xfa00fa0000000000, 0xff000000ff000000],hints 0x21583a8b83a0c83aba8320c85244832a183a2684e138b28b8360c8920c86e0e9722c30e2cb2a0c9c20c9de770701c83a2f87e1f8b22f0380e832768be308f22f8becf2f62f⟩,
  ⟨44,4,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xfe00fa00cc000000, 0xff000000ff000000],hints 0x8560ea2e0e8320eaea0c832149120ca7e0e89a0e84e138b28b8360c8920c0701c83a2f87e1f8b22f0380e832768be308f22f⟩,
  ⟨44,6,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xfa00fa00fa00fa00, 0xff000000ff000000, 0xff00cc00ff00cc00, 0xff00ff0000000000],lhints 5 0xb82daab2a1a2e87a0e7e9de769c2659924490a3d8e22f8b22889a258861b8520e830c8318c5 0x17c588c7c98845f5619c64051946196031a103199e3d8d765d75535535c62a81a06b6ad8c7398a328d460d97639cc⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xfa00c800fa00c800, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x28ba1e839fa779c65c912428f6388be2c8a2268962186e1483a0c0780e 0x29ac55455018d25111e2115c211ce254d52084a8956b2388e25314b495255b5ab000545b5ab⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xfa00fa0000000000, 0xff000000ff000000, 0xff00cc00ff00cc00],lhints 5 0x2a1a2e779da5c9123f8f62f8b22789a2587e1c86e1483a0c31c0e 0xc615ae0b2cca2420422b84223c54916495cd7240902635ac3154539d6c00051635ac⟩,
  ⟨44,4,[0x5000400ff00cc00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000],hints 0x1384e8ee0c84e1586e130ec3b8960c120488561b0380e832760d83684e2f83a0e86e158960c8820c9de138b2138f62c87e1f⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xfa00fa00fa00fa00, 0xff000000ff000000, 0xff00cc0000000000],lhints 5 0xab28ba1e839de769724490a3c8c22f8b22486e1584e0e8360c3241e 0x10d422429790e43892e1088d154452a62001c919ce231204972544390f05095252d8a⟩
]
def nodesBlock11 : Array Node := #[
  ⟨44,4,[0x3200fa00fa00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000],lhints 4 0xa1e428be2c8821f86e1584e0e8304e1203b0d81e 0x44e5009622b533695b5a11ad69685b5bfc77daca⟩,
  ⟨44,6,[0xcc000000cc00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xfa00fa00fa00fa00, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0xbb6baab2a1a2e87a0e7e9de769c26a98a5d9123d8e2348be2c8961b8561483a0c334cc32c1e 0xa7c955d50ca22c08679085e136455955054b5c62a92248a6a96561574591775b9cb56559414329c5244935572dcb⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xfa003200fa003200, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x28ba1e839fa779123f8f62f8b22587e1b866158520e8301e 0x11242926491184608da108981404284bd2e000c27462e4050139d2a118465a94b0943052d6a⟩,
  ⟨44,5,[0xcc000000cc00, 0xfa000000fa00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff00ff0000000000],lhints 5 0xa869aa2e659123d8be2c896218761c86e158420e8304e12848094230781c 0xc699c258042378404800023800190115520f63a101486204017572d6769ee1581805a288⟩,
  ⟨44,5,[0xcc000000cc00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xfa00fa0000000000, 0xff000000ff000000],lhints 5 0x2baa868b9de769123d8be2c8961f86e158520e8301e0700e 0x189020c9218cad189e45414f48d230848b4214b0006e5b18b391505412348e2f62d8b⟩,
  ⟨44,6,[0x3300000033000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xfa00fa00fa00fa00, 0xff000000ff000000, 0xff00ff0000000000],hints 0x86e21a2e1b8b2f98b0d08a21b8a21b832149120c8321b90a0cab20c84e138b28b07a1ba866ea86a198a0d832248322c8e22c8be2886e2886e768be0c8be838be308f22fa2e2ca2e2c83a0e33e6f9c25d9820c9c20c9de77a1a2fa1a2f⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xc800fa00c800fa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x2c5ab2a1a2e879de76912428f2388c22f8b2288922186e1484e0e8360c0781c 0x3a2a711a2211e0229573084f6189225d57551c8415c58a4ed35b96c0014713052635ec93192⟩,
  ⟨44,5,[0x3300000033000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xfa00fa0000000000, 0xff000000ff000000],lhints 5 0xb2aa1a2e779da709123f8f2308be2c89e2487e1c86e1484e0e8360c0780e 0x30f5388f0108d1104f6295951894241d674a58d000536b9ed212acab2e290a949b66d⟩,
  ⟨44,6,[0xf0000000f000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xfa00fa00fa00fa00, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0x324baad8b16b5ad2aca92a2a868ba1e84a0e809ea779da709be699824490a3d8f2388c22f8b2258921b8561484e0e8360c3481e 0x11e1212c785e7842c4a0b2e5a1a94b2e858154412520894411520860b15f7857cb2d87987c801810060821f10462761d95975671895830b2e348e8cb2cc48c30411b2086c410c2085935cc94c31f31060d41f3cc60c0920a02c68124822c25a64421025a68829420a408a6032a424260250c3026c208c0a66db⟩,
  ⟨44,5,[0xf0000000f000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xfa00fa0000000000, 0xff000000ff000000],lhints 5 0x2ffad6b4a92a2a86809de769c2699123f8f63c8c22f8b2258921f86e1484e0e8360c1381e0700e 0x1bb1e0c3c6f0d31b2915cc2ba53931aed3e707cb5b7c5dc60d921b18ce4a5cd5726ae35ae9b9d9746ef8e60ebbabe910c424c9a6a353991a42748cb959d592e4a3804b008e27ad6⟩,
  ⟨44,6,[0xfa000000fa00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0xc9ec5ad2aeab2a2a868ba1e779da719c26f9ba6899262976448f63c8e2308be2c896248861b8521383a0d830cc304b70781c 0x2a02a438b92080a38a15416238989450538515b16628a99b98528578e22180884e39e81e84a05e10178a2a10e178d19f1457cd31e1453ce3a551194e38f50f3c201d28075874f28a74514f98f3c515d99d3e13d37904e148f78f9ce39c82070e3a78206db1dc28768515b9a36c515a9a65a185779e66185679e60f3da75d68f3d575d⟩,
  ⟨44,6,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xfa00fa0000000000, 0xff000000ff000000],lhints 6 0xb6acfad2a4a8aa1a2e879de769c26b9a65c912428fe3d8f2308be2c8962487e1b8561484e0e8360c368d7358d5348d0334c6308b82d46c0781c0500e 0x3dab158a94923a9b2989a49295081094b49296581f950490950850beb694beb861bd06902aa5832674832275961ea4928a769336aa5332a69a8a7a6796765196841096865896741019b482ba6582166492b9b59691b697bed857bed69abdb85b96640095b940bdb4109668e611ba9bb9e9dc05ea9db9b9db⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xfa00fa0000000000, 0xfe00fe00cc00cc00, 0xff000000ff000000],lhints 5 0x2a4a868b9de76972448fe3d8be2c8962087e1b83a0c0700e 0x10641a0721c1021ac4239c42330441906f7a22d388e2084644a949295090004e4a949⟩,
  ⟨44,5,[0x4000400cc00cc00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xfa00fa0000000000, 0xff000000ff000000],lhints 5 0x2b1a868b9de768fe3d8e22f8b22586e158521383a0c0700e 0x18701886d108b011c6719230409020846752e4a0004e5318a38ce34a502409ef6298a⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xfa00fa0000000000, 0xff000000ff000000, 0xff00fa00ff000000],lhints 5 0xaeab4a92a2a869ea2e809f6779da3c8c22f8b22483a0d830d93600e 0x14a73cdf01ca431cea31b9e3131818b19163e2c20cc342d6842d68436880006b42548⟩,
  ⟨44,4,[0xaa00aa00aa00aa00, 0xcc00c800cc000000, 0xf000f000f000f000, 0xfa00fa0000000000, 0xff000000ff000000],lhints 5 0x2baac6a1a2e849de768e22f8561484e0e8301e0700e 0x391a419203199a310964295cb58d8308488425e80006a42dc8⟩
]
def nodesBlock12 : Array Node := #[
  ⟨44,4,[0x3300320033000000, 0xaa00aa00aa00aa00, 0xf000f000f000f000, 0xfa00fa0000000000, 0xff000000ff000000],lhints 5 0x28b9ea779da398ca2f84e0f83a0c0ec36094200780e 0x486011856129586105012112a000cd385c172609719e66a9aa⟩,
  ⟨44,5,[0x5000000ff000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xfa00fa0000000000, 0xff000000ff000000],lhints 5 0xb6abaa92a1a2e779da709123c8c22f8b22487e158521383a0d8300e 0x1a690ce81095a194212211301050153dea39d2a0002f52d8a18e29a85c184a127a9ea⟩,
  ⟨44,7,[0xa000a000a000a00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0xba6c5ad2aca92a1a2e87a1a849ea779da719c26f9ba6a99a629764490a3f8f63c8e2308be2c8821d86e1584e0e830e6390e1374dc0780e 0xac8948ae738aae7965ac8388aeb58dae838dae8596aeb38e76854c76a20876a554768208ae0389ae6949ae638eae09601a62c11602011202cb0e6208760a20764aa1764a22760aa0acf38eae9591ae938eacf58f64f2086632cb66320864f2cb75d64074f74f75da2864f98f65381065399264f80faeb38eade596ade38eaeb59675720875d2cb74220875c2cb75d747adea077589a675a82075b9a675882075975fade3cf⟩,
  ⟨44,6,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff000a00ff000a00, 0xff00ff0000000000],lhints 6 0x318b16b5ad2aca92a1a2e87a127a9de769c6709be6e9a26699262976448f63c8e2308be2c8a22789a2086e1584e118420e8300e 0xa0c31b4926cc3284920a10a33068e184230269a1c26c2a122243089124a830c91a9276679da06464191a1270829da9e408274c16284588c31d85d99899d51d75576652688b0dd08274b2620827647609de8247dd9dd34c32548f94c30d48d35335c65c71770d64d34209c59c70208d58a71600d90035a35c91c36235174e46240d74d⟩,
  ⟨44,6,[0xa000a000a000a00, 0xaa00aa00aa00aa00, 0xcc000000cc000000, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],hints 0x83a15a2e0e882209122ca6a0eaea0e84e138b28ba860e89a96a5aaca84e08b2e98b21b83a60ab270ab2779de2c8e22c8be0e8d20e8bc0e8beac8be308f22f8be6637e2f8b2448b24483aba83aba8320ca86b5a86b598a7037a6f9da2f⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xce000a00ce000a00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],hints 0x83a15a2e0e882209122c8ae0eaea0e8b2448b24483a1b83aba996ac8320c84e138b28b8420e89a0ea5a96ab2a19de77a86b58b2388b22f83a3483a270380e8beac8be769aa2f8be308f22f⟩,
  ⟨44,5,[0xa000a000a000a00, 0xcc00cc00cc00cc00, 0xee00aa00ee00aa00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0xaeab5ab2a1a6a96a2e769123c8e2308be2c89e268821b856138420e8300e 0x1162239dea98ae25354b1184b00175211511890294ab462dcb53d4f15c490860ba5a96⟩,
  ⟨44,5,[0xa000a000a000a00, 0x3300ff0000000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000],lhints 5 0x2aca868ba127a9de769123f8f2388c22f8b2208761b8561383a0c0780e 0x1c6e184261c65388cc33015652daa28e83421e9211316252a1986610ab1ac60a4bd2f⟩,
  ⟨44,6,[0xa000a000a000a00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00cc00ff00cc00, 0xff00ff0000000000],lhints 5 0xba6aca868ba127e9ea779da709ba6a99262982448fe3d8e22f8b22889a218821d86e0e830e33880e 0x17f588a8e148439e0bb7bd1315e55e978ee0b84e33bc2dab631ce628aa2819e639cc5c1700d2765154518e58ae2ec⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xf500c400f500c400, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x2aca868b9de448fe3d8e22f8b2258921b8561484e1083a0c0700e 0x19e4382e0b40d0311a0210de212a822957120d039c633889225b56c08468639cc00054639cc⟩,
  ⟨44,5,[0xa000a000a000a00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00cc0000000000],lhints 5 0x2d1ab28ba127a9de769ba448fe3c8c22f8b2208761b8561383a0c0780e 0xcb41a10e49c6d19089884261c6538a5c950cc33015552d8a4b92e1986610ad17c60a⟩,
  ⟨44,6,[0xcc000000cc00, 0xa000a000a000a00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x2c5aeaaca869aa2e849fa7a9de769c26e9b2629123d8e2348be2c8821b8560e830e50780e 0x85b90e76a304d911544c3324e969a168491444813a4b1894350d26c9b18dd384e4945d173135cd7333625898b84f⟩,
  ⟨44,5,[0xa00ce000a00ce00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x2c5aeaaaa868b9de448f62f8b2268962087e1c86e1584e0e8360c0780e 0x21a4452a0b592a4295b10858418d714a5ae2208e0017473dee6c9b2254875d8429c6717b9ee⟩,
  ⟨44,6,[0xa000a000a000a00, 0x3300000033000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0xb16b5ab2a1a5a8ba1a779da709be5d9123f8f2388c22f8b228886208761b84e0e830e70780e 0xc9c19088ace6818a55e026d673bd2dcb628ca3019b635ecc2f0b213bbeeed6bb2ec5c5715194618f5cd72ac95053⟩,
  ⟨44,5,[0x3b000a003b000a00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0xb16b5ab2a1a5a8b9de769123f8f2388c22f8b22086e1584e1183a0c0780e 0x19a43421e920dc329532084e39ceb44b12a19c670015052daa4bd2f19c67bd442a5a3182a0a⟩,
  ⟨44,7,[0x5000500050005000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0xbceacaaaa4a8aa1a2e879de769c6709be6e9aa6698a609764490a2f8b2258921f86e158521383a0d830fb3e4f73ccef3b4eb3a46d0781c0540e 0xb4f9cfb6a5d2b6a9e7b4f5cfb4d68db695d1b6969ab4d5cd88d64d71c3cf88c65970d3cdb655d0b689d0b685d7b659e52e84c32a53c32654d32283cf72558e8a634d8a659572534db645d4b6b694b6b5d7b6469a1eb3c27a44c21a43cf7ab4d38a27808a234d7a47a4124a247ab96506ba287a4964b6d69ab635d7b6369ab6d5d771b6597213cf70565971b3cf79e7acb6334d71d9a67209657209a671f9658a2898b63918⟩
]
def nodesBlock13 : Array Node := #[
  ⟨44,6,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff005000ff005000, 0xff00ff0000000000],lhints 6 0xc72c5aeaacaaaa2a868ba1e869de769c6709be6e9a26498a5d912428fe3b8d6348be2c8962487e1484e0e8360c3a80e 0x95145928a65146528a41e3a328a8de79028a5d71106440910a02868114422820970a45e29179025c20900a45e49103c25c26ca15f7857ca29b79b7d67db4db6d46df4df7d035b8cd6d041f8df6c90dd08274921b08268a1e144784a29a45185885a49a6982e154b84131a40c6956a141068201c90070209a91a69f6a16db85f7da6da⟩,
  ⟨44,5,[0x5500000055000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff005000ff005000, 0xff00ff0000000000],hints 0x83a159120e832149120c8320eb160c84e138b2778420e89a0e8360c8920c87e1f8b2340701c83a2f0380e832318d236906348ee2ca2e2c86e0eb160c8fe0c8d63590aa19da34⟩,
  ⟨44,6,[0x5000500050005000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00aa00ff00aa00, 0xff00ff0000000000],lhints 5 0x2b5ab2aaa868ba1e869e6779da709be689825d9122c89e268921b8561484e1083a0d830ec 0x18d63467c0d03099a19042f08c0129594e529c20d43105216358dd4c735d4339d3336b1ac8c64e70e03d86f4bd2d3⟩,
  ⟨44,5,[0x5000500050005000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xff00aa00ff00aa00, 0xff00f000ff00f000, 0xff00ff0000000000],hints 0x832149120c8b23b8b2428321b832f184e138b2778360c8920c8d63590ab58b2448b2448327483227aaa429d275a86749122c9122cab20c90ac58fe3f9ea77a1277a0674⟩,
  ⟨44,6,[0x5000500050005000, 0x5500000055000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0xab2aaa8694a2e879de769c26f9825d9122f8b2268921f86e15852138420e8360c3b8ea0700e 0xcac988989086191087dce6718a46918c7c426e009cd5f77cbf2f59a64a92fbbeed68be2f91846e9317c5e10a52b2⟩,
  ⟨44,5,[0x5000500050005000, 0x5500000055000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xff00f000ff00f000, 0xff00ff0000000000],hints 0x832149120c84e138b2778360c8920c87e1f8b2440380e832aaa5277a86778ee2ca2e2c86e0c8d63590aa19d2429122c9122cab20c9ea77a12778be2f90ac58fe3f⟩,
  ⟨44,6,[0x5000500050005000, 0xaa00aa00aa00aa00, 0xcc000000cc000000, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],hints 0x83a15a2e0e832149120c8320eaea0c84e138b28ba860e89a0d83224830f28b2f38b21b83a6083270832779de1f87e2c9101c0720eaa80e832769da94a86769da663c6769122c9122caea0eaea0eab20cad6a1ad6a198a603c26a8be2f⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xdc005000dc005000, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0xab2a1a2e879de769be62912428fe358be2c89a2487e1b8561484e0e8360c0700e 0x21ee411a22111e28b22c41204c8a62295967116418942ad6d84a5910849000054a49ada5b14⟩,
  ⟨44,5,[0x5000500050005000, 0xcc00cc00cc00cc00, 0xee00aa00ee00aa00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0xaeab5ab2aaa868b9de769be448be2c89a2487e158521383e0e8360c0700e 0x889104770844b89296382125000140c6648a45906250a309c1cc732e4b92a27c1adb4ed3⟩,
  ⟨44,5,[0x3300ff0000000000, 0x5000500050005000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000],lhints 5 0xab2a1a2e879de76912428be2c8921f86e158521383a0d8301e0700e 0xcae188492906b184254807084690715c5a8e51945ad4166538de3319915298f63dec⟩,
  ⟨44,6,[0x5000500050005000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00cc00ff00cc00, 0xff00ff0000000000],lhints 5 0x2f3ab2aaa868ba1e7e9de769be6699260912428be2c89e268962187e1c86e1483a0c3d8f53d00e 0x1de70cead1ca521a2422d6421e04761d7ddcf762c8b2252e88ad6a20ed38096b5f968ba2e0d67281e07e9337cddef⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xaf008c00af008c00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x28ba1e779da4490a3d8f2398d62f8b22789a258861f8721b8520e8300e 0x21ec408e41092215b97423489405015c9721089140501a56953196c2914400033651ec6426c⟩,
  ⟨44,5,[0x5000500050005000, 0x5500440055004400, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x2aca528b9de769964490a3d8e2348c22f8b22487e1b864480e4360801c0440e 0x46b080590002880845d462408205024b4a50240a8038297ad18b7ad8270b00655ac6426c⟩,
  ⟨44,5,[0x5000500050005000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00cc0000000000],lhints 5 0x2acaaa8ba1e779da4490a2f8b22487e1b8561383a0d8301e0700e 0x14f228d6e18cad198cb808482906a1a52b704254006f7c26f72dcb695a5a0e308c18c⟩,
  ⟨44,6,[0xcc000000cc00, 0x5000500050005000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0xaeaacaaaa1a2e879fa779da6f98a609122f8b22587e1b8561483a0c3e01e0700e 0xa7a948669085c91735c8522a88a2252b68425b80918caf16adabc9725c1292a498c5d57541544512d2bc6f173c70⟩,
  ⟨44,5,[0x5000dc005000dc00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x28ba1e779da719724490a3d8e6308be2c8961f86e158520e8301e0700e 0x21ac419603191e353554109e448d234214e0848e00073631d354951790e448d23ad2b474d6b⟩
]
def nodesBlock14 : Array Node := #[
  ⟨44,6,[0x3300000033000000, 0x5000500050005000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0xad6acaaaa1a528b9de769c26c9825d912428be2c89e248861f8721b8521383a0d830fa0780e 0x10bc206788c6880cc676028d106c1a94e8a50d40076b67568ba2e82208e0fbaee9efc3b0e29663a8ef7b6edb9c854⟩,
  ⟨44,5,[0x7300500073005000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x2c5ab2aaa868ba1e779da4490a2f8b2278922187e1c86e1484e0e8360c0780e 0x3aa8711a0211de2295b3084f5189624a5b041d87000518ceb18360d211e7b8b029d6528d9ce⟩,
  ⟨44,6,[0x5000500050005000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xff000000ff000000, 0xff00f000ff00f000, 0xff00ff0000000000],lhints 6 0xc46f1b72c5aeaacaaaa2a868ba1e849ea779da749c2669825d912428fe3b8d62f8b2258921f8521383a0d830ee3b00e 0xd10de2c77914432c341c3a12cb85c7102cb9241500c360b19d70674b2d871874a1180c360a25d0c375035884d61041d85d5cb21f4487cb2d74517c30175405c30df51f7c27d74105c159f4105dd5df6187dd7576179514622cb8914652cb5538220c34904229228903d24cf89b6636188db6a26185553225cc⟩,
  ⟨44,7,[0xaa000000aa000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0xb2ec5aeaaeab2aaa8aa1a2e879de769c6709be6e9aa6899a629825d912428fe3d8f2308be2c89e258922187e1b8521383a0d831164510e43102405003fcfe0780e 0xcd0ad0cf0592cf0aebcd0590ccb74bced58fced75dccb58b78b70b7b24107b271b78b40bce958ececacecec596ce9ae97ac4017a9c417a94107acc6c2a950c26a2cb22a5131e92cbcd7591cee751cee596cd775779779779e4108a289586e2c0857bc08572cb86ebee857b1785aa5885ab19857a57cf3786ce7596ce7ce7cf359679e78dce740d79f7858a52cb7a678489e2cb7a07838a3a697a47828a0a697a17a8ce75d7⟩,
  ⟨44,6,[0xaa00aa00aa00aa00, 0xee00cc00ee00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0x308b16baabaacaaaa2a868ba1e779ba6a9a2669764490a3f8f63c8c22f8b226896248861f86e1a852138360c0780e 0x90770792134992171c90734790250291e34591e5149023425424c25631c75634d25421c291a34491d70491d34d91a71a55d1c155a88155a1c755d89d65a2c365b08265b2ca65a08290e34891f50891f34d90e50e54e3065551c65d730c5ce1c759f08058e80058e08259f81f60e74e61168f61175060e68e⟩,
  ⟨44,6,[0x4400cc004400cc00, 0xaa00aa00aa00aa00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0xcaec5ab2aaa92a2a868ba1e779da6899a629764490a3f8f63c8c22f8b2258921f86e158521383a0d8301e0700e 0x8c57058df3488df71c8c53458c35038de3478de5148c33435434c35621455624d25431438ce34a8e050a8e034d8ce50e54e14155924161914560e2495d90c05ce8405ce0c35d98598da3468dd7068dd34d8da71a59d24259a14259a24959d14559a30459b0c359b30b59a0c359a44f59d38e59d45059a38e⟩,
  ⟨44,6,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xfa00f000fa00f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0xc2ec5aeaaeab2aaa8aa1a2e87a0e779c26f9a2669764490a3f8f63c8c22f8b227896248861f86e1484e0e8360c0780e 0x94774796234996275d94734794250295f34695f5149423426024c26241c46244d26021c295a34595e74595e34d95a75a55e1c155a8c155a1c755e8de65a2c365c08265c2ca65a08294e34896050896034d94e50e54e54e55b1c75db5cc5ce1c766008064e84064e08266086058e78e59168f59179058e68e⟩,
  ⟨44,6,[0x5000f0005000f000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0x32cb16acaaaa4a8aa1a2e879de769a66899a609764490a3f8f63c8c22f8b2258921f86e158521383a0d8301e0700e 0x90574592034892075d90534591b34691e74691e34d91b75b55e24255b14255b24955e14590e34a92150a92134d90e50e54e14155a24161a14560e2495ce78e5d16cf5d17905ce6ce90350391f34791f5149033435434c35631455634d254314358370358c6c458c70b5836c35e23805c368064338366269a⟩,
  ⟨44,6,[0x5500ff0000000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000],lhints 6 0xb2ec5abaacaaaa2a868ba1e779da6899e6697a5d9724490a3f8f63c8c22f8b2258922187e1b8521383a0d8310b4290841d064150440c1e0700e 0x78b6cb7ac34d7ac6da78b34b7a74027a43427a44107a734d2a450c2652cb2255131e42cb7963417a34018a334db564108232c0816a808162cb823aa38169d68199178199d8816916b55ad2b6634db66ae67d534d195a0f75c2cb15ca1c7552cb1269ce75590e0d59d5766924b5ca51b55591b55a5585c596⟩,
  ⟨44,5,[0x5500ff0000000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xdd00ff00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000],lhints 5 0xaf2a8a868b9de769123f8f62f8b2258862087e1b83a0c0700e 0x86c110641a048110641a04813de108c80009ca5ad4a5ad471c866134504c5332952a⟩,
  ⟨44,5,[0x5500ff0000000000, 0x88000000cc00cc00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000],lhints 5 0x2aaa868b9de768fe3d8ee388be2c8961b8521383a0c0700e 0x86d1186619c4710423300027258c4986619c4713dec4b12b1c065140448c14992508⟩,
  ⟨44,5,[0x5500ff0000000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xf500ff00f000f000, 0xff000000ff000000],lhints 5 0x2aaa8a9da2e879de76912428f23b8e6388c22f8b21b83a0c0781c 0x306c1b06c188410906f841ef841e000c8e319ce319c63acca1c4652cdb24a5af41a86⟩,
  ⟨44,5,[0x5500ff0000000000, 0xa0000000f000f000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000],lhints 5 0xa8a9ea1e779da4490a3c8c22f8b22187e1b8521383a0c0781c 0x346d184261c2318000333d4a7a96c5346d188518460a7a9e81c8659a4844c0e74a9c9⟩,
  ⟨44,5,[0x5500ff0000000000, 0xaa00aa00aa00aa00, 0xc000c000c000c000, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000],lhints 5 0x28ba1e779da4490a3d8be2c896248861f86e1484e0e8301e0700e 0xc8f188472486a791e458e7208487000716b9cd6b9cd4928430e03295926420c4218d⟩,
  ⟨44,5,[0x5500ff0000000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xfc00fc00fc00fc00, 0xff000000ff000000],lhints 5 0xa2e879de76972448fe3c8e6308be2c896248862087e1d86e1983a0c4241c 0x1465198711884519475aaeca00065a35b4211746ba0d48ee30b1934224b7b19639d8d⟩,
  ⟨44,4,[0xa8000000fc00fc00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000],hints 0x1384e8fe0e1284a86e0e0ec3b892130701c83a1b0e439852760d83684e2f86e0e86e0e8320c882149de138b2138be2c87e1f⟩
]
def nodesBlock15 : Array Node := #[
  ⟨44,5,[0xc000c000c000c00, 0x5500ff0000000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000],lhints 5 0xaaa8ba1e779da4490a3c8e6308be2c8962187e1b8520e8360c0700e 0x88f1188620e6208486000515b1cb4128428a026a95339d4b310c448a52aaeab54150⟩,
  ⟨44,5,[0x3000300030003000, 0x5500ff0000000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000],lhints 5 0x2baa2e879de769123f8f62f8b2258862087e1d86e1984e0e8360c0781c 0x20902042720d93000873199273dee592a452a2c295b34a5aeb12c410a9373dcfab6ad⟩,
  ⟨44,6,[0xaa000000aa000000, 0xaa00aa00aa00aa00, 0xc000c000c000c000, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0xb26aaa868ba1e779da709ba68996629824490a3d8be2c89e258922187e1b8521383a0c435070780e 0x10ae208791088890c676821477445c9d2745114309bd252e7bd0d0009e7c20f7c20f13bee29664c129abeab61d72f⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xea00c000ea00c000, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0xaaaa1a2e879de6f9aa4490a3d8be2c89e258922187e1b8521383a0c0780e 0x322a611602119e28320c18de650a4221193084d6989229d23339d8d69966000576b9cd6b9cd⟩,
  ⟨44,6,[0xaa000000aa000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xfc00fc00fc00fc00, 0xff000000ff000000, 0xff00ff0000000000],hints 0x86e21a2e1b8b2cb8b11286d1186e5d88220912258761b8fe1b8320c8b2398b28786e3586eb59de77896878921f87e2c8be2f86e274422f8be6686619896aa8be308f22f4222cb7a2c83a0e43e6f99668982259c22598a879ba879da2f⟩,
  ⟨44,5,[0x5400fc005400fc00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x28ba1e779da719a262972448fe3c8e6308be2c896248821f86e19856118420e8301c 0x117424a64b20a2263d99188e25e54a4218d00047319776ba0d65993388e208575c63346ddb7⟩,
  ⟨44,5,[0x5400540054005400, 0xaa000000aa000000, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],hints 0x86e21a2e1b038399100e03a1b8fc0e0d8368b28786e3586e940440e8900e9da2caee2c0701c9d80e9c00e9da789ba768be2c87e1f86e2786e2faa80e8640e8be3c8c22fa1a2f⟩,
  ⟨44,5,[0xfc000000fc00, 0xaa000000aa000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff00ff0000000000],hints 0x1384e912250784a8b01e078258901e87e1f8b22f866198969a8bc1e83c1e83a15a7a0e83a119c20e8381e9b81e0701c86e8b8861b8320c8761ba841e86c1e86e278be1b8a20e⟩,
  ⟨44,5,[0xaa000000aa000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xfc00fc0000000000, 0xff000000ff000000],hints 0x22186e8b86e0c86e3f8320c852448301e07a1bad61384e2c9de0d832248322f86e2787e1f8b22f0380e832aa8be308f22f83a0e9722c44e2cb360c9c20cb3a779ba779da2f⟩,
  ⟨44,4,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xfe00fc00aa000000, 0xff000000ff000000],hints 0x83a0ea2e1b8321b8fe0c832149120c0781e86eb584e138b2778360c8920c8be1b89e1b87e1f8b22f0380e832aa8be308f22f⟩,
  ⟨44,6,[0xc000c000c000c00, 0xaa000000aa000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],hints 0x86e21a2e1b832149120c8321b90a0c8b2398b28786e3586eb5836878321f87e2c8be2f86e270380e832aa8be308f22f42a2cbae2c83a0e9820c9c20c98a879ba879da2f8b2448b24486e4286e428960c9de77aaa2faaa2f9a26c4566f⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xae000c00ae000c00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x2aaa2e879de769aa68912428f2398d6308be2c89e268962187e1c86e1483a0d8300e 0x2a3250926109641641982bcaa1070164d9318cb2a0521bdeb839d8d315650003a6ba2d6db4d⟩,
  ⟨44,6,[0x3000300030003000, 0xaa000000aa000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],hints 0x86e21a2e1b88220912258761b8fe1b84e138b2770781e86ea1836259de1f87e2c8be2f86e2786619896aa8be3d8f62f42e2cbd62c83a0e982259c22598a779ba779da2fa2e2ca2e2caea1baea1b8320ca1e778be3d8be3d9a26c45e6a⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xba003000ba003000, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0xaeaa1a2e87a0e779be629123f8f62f8b227896218821f8761b8661383a0d8301e 0x32ae64a62b39a06211b4000d810974bb6ed18f260866b952d4421ae719862957573dee7b9cf⟩,
  ⟨44,7,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00aa00ff00aa00, 0xff00ff0000000000],lhints 6 0xb7ec5b0ab5ab2a4a8aa1a2e87a1a799de769c6709be6e9aa6899a629825d9122f8b22889e268962486e15852138420e8360c4d1334c5304bd2d4b12b4a92849121475193acb41b85707c16 0xefb861eed8e3eed861efb8e3ed6cd6ef685aef6cf3ed68569e79dbed6b56ed48d4ef5859ef58e3ed48544f7b37a14ad4a14b144b797791445443a5963fa3ba914594eef858ef4cd8ef4861eefcef378ab8a2fa6fa2faaf3389b89348172ef5962af81e93459626f7552325141f275c1af514eee861ef98e3ef9861eee8e3924922eeeb629245969ee9eea28a1f16e5149f1df01315149eedee0eed2e9c2bef040d349eebee⟩,
  ⟨44,6,[0xaa00aa00aa00aa00, 0xc000c000c000c000, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00aa00ff00aa00, 0xff00ff0000000000],hints 0x8b2448b24483a15a2e0e86e0e832149120c9c20c832608320eb160c84e138b2779ba779de628420e89a0e9de0c892448b2448b11c9be689965d8391b83a25832879de2c9122c9122f8be0e9da2783279832769da77a86769da6646a76⟩
]
def nodesBlock16 : Array Node := #[
  ⟨44,5,[0xcc00cc00cc00cc00, 0xea00ea00ea00ea00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00aa00ff00aa00, 0xff00ff0000000000],lhints 5 0x2c5a868b9f6799de769aa609123d8f22f8b22789a2486e15852138420e8360c 0x16f5b846b08e2015e07001000b005d572631d11484a050122117374dad18922081009caf2⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff00aa00ff00aa00, 0xff00c000ff00c000, 0xff00ff0000000000],lhints 5 0xb16a19e6779da6f98a4490a3f8be2c89e268921b8561484e1083a0c 0x257054e534260c00470001a81a00306354841405b26be403814e538310a56b04c118ca91⟩,
  ⟨44,5,[0x3f002a003f002a00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0xad6aca2e879de76912428f6308be2c89e268962486e198561484e1083a0c 0x96a1012200060018d9310541981006458f0c02b01812739f26459109c30058099de746b64f⟩,
  ⟨44,6,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xfc00fc00fc00fc00, 0xff000000ff000000, 0xff00aa00ff00aa00, 0xff00ff0000000000],lhints 5 0x2dfb66d7ad6aca2e87a1a779da68996448e62f8b22889e258922086e1583a0c4811e 0x16e5b864a8ca35e9617c1e050d43319c8b211640f231096d5d2f4a5d4350e52450eb72dcc60e298ce7144d118d311⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xfc00a800fc00a800, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x2d9b5eb5ab28ba1e869de76912398be2c8a227896248821b8560e8301c 0x10e425354d20922295a738ac2084f353151489227be343c4c65354d000485ae0e3c0ee746ae⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xfc00fc0000000000, 0xff000000ff000000, 0xff00aa00ff00aa00],lhints 5 0x2d9b5eb5ab28b9e6779da448be2c89e268921b852138420e8360c 0x184c5298a1405100220150002b01273a4312044229c101c0b589a95314c03c0d6ba6d⟩,
  ⟨44,6,[0xc000c000c000c00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00aa00ff00aa00, 0xff00ff0000000000],lhints 5 0x2c5ad68ba1e799de769c26c9aa6899a60912398be2c8a2278961b8561483a0d8312348817 0x18f63ca7d1505199e3a8c701978363999de73b595652646c7b1ed696ca1e076b641663d8f14e545956548ef78d836⟩,
  ⟨44,5,[0xae00ae00ae00ae00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00aa00ff00aa00, 0xff00ff0000000000],lhints 5 0xb16b5aaaa1a2e87a06799de769be448be2c89a2487e1b866158521383e0e8360c 0x12963846a8902015c03801700b2021194bd29818962081406398e6b60f1405304810846d0⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xf300a200f300a200, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0xad6acaaa8ba1e799de769123f8e62f8b22587e1b8561483a0d8301e 0x196439264919866091a108d81404344ad31000c3ac5ef1062139d2d19866529d30c02e7466e⟩,
  ⟨44,6,[0x3000300030003000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00aa00ff00aa00, 0xff00ff0000000000],lhints 5 0xab2a1a2e87a1a779da6f9ba6c9a262976448be2c89e268962086e1584e1083a0d8312749925 0x1d0740a8d952552a0bead7d5944539dd8ae3123158522f0e83a0f796ed5e577be397dbb6e0da748940518f58cdf37⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff003000ff003000, 0xff00aa00ff00aa00, 0xff00ff0000000000],lhints 5 0x2c5aeaaca868b9de769d26f9123b8d62f8b22789a258821b856138420e8360c 0x16e5bc45a08c2140e77a2c845800c08845cdad9dc624882144d6f5bd8c1484a4451294eb2⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xcf008a00cf008a00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0xaeab5ab28ba1e779da448f63c8e2348be2c89e268962086e1584e1083a0d8300e 0x19ac34224948f236499219c794dc212959420d4310934ad29863d8d1b86b001336c66d6d20d⟩,
  ⟨44,5,[0x3000300030003000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xff00aa00ff00aa00, 0xff00f000ff00f000, 0xff00ff0000000000],lhints 5 0xaeaaca868ba1281a02779da759d2448fe3b8be2c89e2586e1584e0e8360c 0x446090a42c451586344021309705dd0c4304f11d2973aaf8a288002ebbae706b64f⟩,
  ⟨44,6,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00aa00ff00aa00, 0xff00cc00ff00cc00, 0xff00ff0000000000],lhints 5 0x2dfb5ec5ab2a1a2e7e9e6779da6a9a266992629122f8b22889e268961b8520e83129 0x13a4812b4ae107b109aa0422102358425286e10dc28c05344cad26ca4c448c5094295a56f8c5ca522270cc318cb31⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00aa00ff00aa00, 0xff00cc0000000000],lhints 5 0x2d7b46c5ab28b9e6779da649122f8b22789a248821b856138420e8360c 0x2dab688b2118403b413002601500422e0e842a3124410200b6adac609ea0440f7c2cf⟩,
  ⟨44,6,[0xcc000000cc00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00aa00ff00aa00, 0xff00ff0000000000],lhints 5 0xb16baab2a1a2e819fa799de769ba6a9a26698a448be2c8a225856148420e83018 0x10a42845a8b0209141b843708b2144d117c62b1c446098285214948a140c8308441045515739ab388c1306d1641b0⟩
]
def nodesBlock17 : Array Node := #[
  ⟨44,6,[0xaa00aa00aa00aa00, 0xcc008800cc008800, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00aa00ff00aa00, 0xff00ff0000000000],lhints 5 0xb5ac5aeab5ab28b9e6779da719ba6a9a25d912398be2c8a227896158520e83019 0x10b42c44a0ae208d61a843508b0142914b39a711c45094285a16f81c47114250ca485a16948a260cc318d8118e591⟩,
  ⟨44,6,[0x3300220033002200, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00aa00ff00aa00, 0xff00ff0000000000],lhints 5 0x2d7b5ac5ad6aca2e799de769c66a9a25d9123d8e62c8a2278961b8561483a0c 0x10b42c239848100960a0014006c0425136b6a709c25014085a16a5060604810857109a26873c2709c050163183217⟩,
  ⟨44,6,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff00aa00ff00aa00, 0xff00f000ff00f000, 0xff00ff0000000000],lhints 6 0x310b66d8b16c2aeab5a92a1a2e87a12819ea779da749be669764490a3f8ee358be2c8a22789a1b856138420e8312e49cec1641a 0x1941a13898545063864ce3a35118ce3935135c61939ca4c6197597a1452538e95452838e9a61651859d34e55e59534845d268e2207c880e39a7da80d1da18668d2e018689341a8d06934e28e268369e95b7a775a95a64e3a451490e3995149c61999d96461a758c5553d94cf64261c95872771995966064169a020819699⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000a000f000a000, 0xff00aa00ff00aa00, 0xff00f000ff00f000, 0xff00ff0000000000],hints 0x83a159120e8b2448b23f83a1b83aaca022ca2e2c8320c90a3f84e138b2778420e89a0e8ca328feb59de7aa12778b2448b24483a7683a278c6319d274a06769da77a8676⟩,
  ⟨44,6,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00aa00ff00aa00, 0xff00f000ff00f000, 0xff00ff0000000000],lhints 5 0xb62c5ad6a1a2e84a0e819ea799de769c26f9a2669764490a2f8b21383a0c 0xc330c661994b5aa6398c21294c330c005dacabd8e210db46b6956b6b46b68d7c9a330cc96310421d9063a2c6368c⟩,
  ⟨44,6,[0xf0000000f000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00aa00ff00aa00, 0xff00ff0000000000],lhints 5 0x2d9b16b5a868ba12839ea799de769c26f9a2669122f8b22789a1b856138461083a0c 0x12b4ac25b04c15a5697e72e1e424226388c70209c319d6295a56a5060884a90846f05a5697b9eed0400c4711641b0⟩,
  ⟨44,6,[0xf0000000f000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff00aa00ff00aa00, 0xff00ff0000000000],lhints 6 0xcbad9b62c5b0abaad6aca92a2a869ea2e87a06779da6f9a25d912428ee358be2c8aa2889e26896248761b8561484e1083a0d8313216c1d 0x5924a65d59924965d60d70e24888975c34839162c36830d60e46a47121e17c785249c7dc95651c9947165a59a570d11e0c378d31c0c36d24a75d79d249b5d76184db5936c30dd91d7430db9116e16c171c02185b71b1691634898eb8054850a9285585aa9a050c315c15078641c38578565b6c574515b16974f⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000aa00f000aa00, 0xf000f000f000f000, 0xff00aa00ff00aa00, 0xff00ff0000000000],lhints 5 0xad6aca86819de76912428b22a89e268922186e15852138420e8360c0781c 0x4a9e911e22b08492450481056110c67cc214dc6258984291f17c4001504e2349294eb2⟩,
  ⟨44,6,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000a000f000a000, 0xf000f000f000f000, 0xff000000ff000000, 0xff00aa00ff00aa00, 0xff00ff0000000000],lhints 5 0x2d8ad6acaaaa1a2e87a1a779da719c26f9a2669122c89e268821b856138420e8312e 0x14b52c45a88c239d6ac39b8100555554f8684c1042422a5994b2312052a5252a524a5a97788a298ce718ce718cad1⟩,
  ⟨44,6,[0xf000a000f000a00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00aa00ff00aa00, 0xff00ff0000000000],lhints 5 0xb66d8ad6aca868ba1e869de769c6709be68912428be2c89e268821584e1083a0c 0x10b42c24a05412956863ad60e4231a2378c6e2098319ce285a1694860784a50846b042d0b6bc390e0008ce3384a12⟩,
  ⟨44,7,[0xaa000000aa00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0x2ecb16c2aeaaeab2a2a868ba1e869e6779da719c26f9ba6a99a629825d912428fe2f8b2258922186e1484e0e8360c52d4951d445093f4ed384d8210781c 0xc11a11c2c552c2ca28c11551c0c64cc2a550c2a659c0c54c68c60c2ef4512af61768c44cc2454fc29a0fc29555c24a246a9441264b412244516a9b691e450d1a730c16751312430cc23555c2e659c2e555c2365969a74076376369a45176330c766ae576630c763ae3763a6375d924742a69763923c30555c22659c22555c3065974374ec2244e75b30c761aeb76130c760aeb75ca6975e92475fa6975c92469a696c228d6⟩,
  ⟨44,6,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00aa00ff00aa00, 0xff00ff0000000000],lhints 6 0xc6ac5b0ab5ab2a4a8aa1a2e87a1a799de769c6709be6e9aa6899a5d9122f8b22889e268962486e15852138420e8360c4dc22 0x273cf6514593cf9d14447c488f2227df10f11448911910244284f1e145108f0a36230970826028d78c248298412606608409b3c681f1a03cf6df6e45a46d56db51b9159203856c411b38c80411b2c378209e2ca6c209a3cf9514653cf69145449069941410469469450d68209d8dc74209a8da6a06936db02081a6da⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff00aa00ff00aa00, 0xff00f000ff00f000, 0xff00ff0000000000],lhints 5 0x2c5ad6a1a12819ea779da749be4490a3f8ee358be2c89e2686e1584e1083a0c 0x91c142d0d0942f721c8001b863063448413054a6de53ac90e4383109d29842918cad1⟩,
  ⟨44,6,[0xaa000000aa00, 0xaa00aa00aa00aa00, 0xc000c000c000c000, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0xb16a1a2e879e6779da6f99a65912428be2c896248861b8521383a0c4e9390781c 0x109ba08779088710c6650214628453d8f6390e42c96a31ec78268254939d3139c47363d8f2949926714c5211149ad⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xc000ea00c000ea00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x2c5ab2a1a2e879de76912428f63c8be2c8922186e1484e0e8360c0781c 0x3a267119e211dc229551084f41892254d5371c84154569469153d4d00207134508358c5adb0⟩,
  ⟨44,5,[0xaa000000aa00, 0xcc00cc00cc00cc00, 0xea00ea00ea00ea00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x2c5a868b9f6799de7691242906408f63c8be2c8922186e1484e0e8360c0781c 0x3a2c711a2211dc255552002071505229553084ef189229caf25454d2104d1616bbb58c⟩
]
def nodesBlock18 : Array Node := #[
  ⟨44,6,[0xaa000000aa00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xfc00fc00fc00fc00, 0xff000000ff000000, 0xff00ff0000000000],hints 0x86e21a2e1b8b2ec8b13e86d3d86e5d88220912258761b8fe1b8320c8b2398b28786e3586eb59de77896878922c9122c9101c9da1b9da86a1a7689686896769da87ba2768b2448b24483a0e4f26a99666896ac896ac98a879ba878be2f⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xfc005400fc005400, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x2aca868ba1e869de769123f8be2c8921b8561484e0e8360c0700e 0x21e446a9aa41104119a2111821528229551411047be33189225354d084887416b0004e7466e⟩,
  ⟨44,5,[0xaa000000aa00, 0xfc000000fc00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff00ff0000000000],lhints 5 0xba2a1a6a8b996448be2c896248861d8721b856118420e8304e12848094230781c 0xc6a442590423804049000288001c81967b0e77330160580681145a1175210148660432a8⟩,
  ⟨44,5,[0xaa000000aa00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xfc00fc0000000000, 0xff000000ff000000],lhints 5 0x2e8b3ab5ab28b9e6779da6e9123f8be2c8922186e1484e0e8360c0781c 0x20f2388ec108cd10427a14aa80c49101e75354d1444f7c2cf2114d5345314eb07416b⟩,
  ⟨44,6,[0xaa000000aa00, 0xc000c000c000c00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0xb16b5a2e879e6779da6e9b26698a4490a398d62f8b2258861b8520e8360c505400901c 0x109ca087810887916e5e10d468b822e0b802a825c95ae0355c17043d0f512d6954755c1703189b26e38a618c9c853⟩,
  ⟨44,5,[0xc00ae000c00ae00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x2c5ab2aaa868ba1e779da4490a2f8b2278922187e1b8661484e1083a0d8301c 0x42a8809a010a1e1295b321115105614a5b00018809c318ceb16c1b043c630e03794ab373ad1⟩,
  ⟨44,5,[0xaa000000aa00, 0xae00ae00ae00ae00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0xaaaa1a2e879e6779da4490a358be2c8922187e1b86a198521383a0d8301c 0x42aa8096010a1e121194438e710561641900010f0cc318cad14a59018c260ded4b51ad⟩,
  ⟨44,6,[0xaa000000aa00, 0x3000300030003000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x2baab2a1a2e87a1a779da6f9b2669123f8be2c896218821d86e1383a0d831430781c 0xeab9d297ad0771cc6650213e08ba31ec782675d5739d313bb2ecd1f4718ed4aceb363d8f295795e714c51ad8c052⟩,
  ⟨44,5,[0x3000ba003000ba00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x2baab2a1a2e879de769123f8f6388c22f8b2248861b852138460e8360c0781c 0x426a811e22116023197308516189425b96c0024813052636cc5c571c208415c57b4e9363d92⟩,
  ⟨44,6,[0xaa000000aa00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00cc00ff00cc00, 0xff00ff0000000000],lhints 5 0x2ecba2e6aeaaca868b9fa799de769aa6899a6498a448fe2f8b228896218721b8520c51945 0x13c48486b132410d8211ce2111624d533bcc93d1c471258960252796441505294f724b12c8c60d41058161b374d4a⟩,
  ⟨44,5,[0xaa000000aa00, 0x5500440055004400, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x2aca868b9e6779da448f6388c6308be2c8921b8521383a0d8304808c200700e 0x92c12a645185e14219410541315659324c50541996a59de936418d384002e1aebb62d⟩,
  ⟨44,5,[0xaa000000aa00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00cc0000000000],lhints 5 0x2e8b9ad1ab28b9e6779da649123f8be2c892218821b84e0e8360c0781c 0x1912308ed108cc114aa80426a8c49129aa681e61444f7c2cf5354d2105314e907416b⟩,
  ⟨44,6,[0xaa000000aa00, 0xcc000000cc00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0xaeaaca869aa2e7e9e6779da6e9aa6698a448ee2f8b22586e1483a0c520260781c 0x169aa48661096c91344c832ca088225896023924c918c8514d53539d04412f2744714b12c29498261b28494a7be0d⟩,
  ⟨44,5,[0xaa000000aa00, 0xaa00ee00aa00ee00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],hints 0x87222a2e1c832149120c8321c9020c84e138b2770781e86a1a8360c8920c8b27d8b2760701c86e1b83279832769da77a867687e1f8b23d83a0e83219832aaa863d8f23c8be2f⟩,
  ⟨44,6,[0xaa000000aa00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00f000ff00f000, 0xff00ff0000000000],lhints 5 0x2c5a868ba12839ea799de769c26f99a4490a3f8ee358d22f8b21b84e0c52937 0x18561525b1484615851097850c658de31ba10bbc675895856061069e0b84a90846f02b0ac73dee02dd87e2f1bc4c6⟩,
  ⟨44,5,[0xaa000000aa00, 0x5500500055005000, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],hints 0x7048a2c1c832149120c08c1c8fc1c84e138b2770801c8681c8360c8920c9122c9122c86c1c8d01c9da0c9e60c9daa19de7687e1f8b2448381c0380e832aaa5277a86778be2f⟩
]
def nodesBlock19 : Array Node := #[
  ⟨44,6,[0xaa000000aa00, 0xf0000000f000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0xb16b5a868ba12839ea799de769c26f99a4490a2f8b2218761b84e0e8314c0781c 0xc8b1989624f9314a988426bc6758a5896020684a90846f06258959863c47116c0504b12c211d97e6f1bc54a73dee⟩,
  ⟨44,5,[0xaa000000aa00, 0xaa00fa00aa00fa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],hints 0x86e21a2e1b832149120c8321b8c60c84e138b2770781e86e348360c8920c8b27d8b2760701c8d21b83279832769da77a86768b2388b22f83a0e8322f832c58be308f22faaa2f⟩,
  ⟨44,7,[0x5500000055000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0x2f8b16acaaaa4a8aa1a2e879de769c6709be6e9aa6698a60976448f63c8c22f8b22889a258921f86e15852138420e8360c56d5755551539363b4b61c0280700e 0xc8eacecae652caeaebc8e64ec8c78ccad651cad79ec8c64c7cc7cc7f138e7f12f17cc38cca9650cacad0cac659ca9ae97ec60f7e938e7e96177ec38e2a958d26a30c22a5951e930cc9a654caf794caf659c9a79a7df8817df38e7da7da16f30089ac0011a30c8afc2f0dab1a89da5b09db1c89aa5acb2aebca7659ca7aebcb26597df7d3ca738e7e0c717e530c7e6c717df30c7e1a697dfb2c7e4a697e3b2c7c67e8ca769a⟩,
  ⟨44,6,[0x5500000055000000, 0xaa00aa00aa00aa00, 0xc000c000c000c000, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x2c5aaaa1a2e879de769aa65976448f62f8b2268962487e1b8561484e1083a0c5414f0700e 0xa9c948891085e10e77dcc5716e4649f27cca32b498bad6f804b00009b8463084630cbf2f51784e12fabea93156d0⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xd500c000d500c000, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0xb16aaa868b9de4490a3f8f62f8b2268962487e1b8561484e1083a0c0700e 0x19e8311a4210e029364d40e2358ae2295b320d8398942ace754a5ae0846e0005673dee73dee⟩,
  ⟨44,5,[0x5500000055000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff00c000ff00c000, 0xff00ff0000000000],lhints 5 0xb16a1a2e779da4490a408fe3d8be2c89a2487e1b8561484e1083a0c0700e 0x19e4311a4210ee22959420d63a09424a58d0846d000506b9cd8b2ac40ee278a918da6d⟩,
  ⟨44,6,[0x5500000055000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xfc00fc00fc00fc00, 0xff000000ff000000, 0xff00ff0000000000],hints 0x83a15a2e0e8b2f88b1548a20e8a20e88220912258960ebca0e8320c8b2398b2878a20e8a20e9de77896878921f87e2c8bc1c83a2f54e2f8be6686619896aa8be308f22fa2e2ca2e2c86e0e54a6f9965d982259c225a1eb5a1eb59da2f⟩,
  ⟨44,5,[0xa800fc00a800fc00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x2c5ad6a1a2e7a9de769123c8e6308be2c8a2258922087e1b8661583a0c0781c 0x192a34222a50f0363d93085635512939d8d0006d295526ba0d6559558cc310958b4ef36c9b2⟩,
  ⟨44,5,[0x5400540054005400, 0x5500000055000000, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],hints 0x7048a2c1c038399100e0381cbc80e0d8368b2870801c8981c0440e8900e9da2c9f62c86c1c9d80e9e40e9da949e2768be2c87e1f8bc1c8701caa80e8640e8be3c8c22f8be769962f⟩,
  ⟨44,5,[0x5500000055000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xfc00fc0000000000, 0xff000000ff000000],hints 0x22c83a8b83a0c83af28320c852448321083a2683a1384e2c9de0d832248301c83a2f87e1f8b22f0380e832aa8be308f22f86e0ea2e2ca2e2cb360c9c20c9deb59deb59da2f⟩,
  ⟨44,6,[0xc000c000c000c00, 0x5500000055000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0xb16b5aaa8ba1e779da6f9b25d9123c8e6308be2c8a22587e1b8561483a0d831560700e 0xa7c146688c65d8d8f65d65594971a52c684ad000796ba0dc330c41763d8efabeaad645915956550ed6cb72d94c54⟩,
  ⟨44,5,[0x5d000c005d000c00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0xb16b5aaaa1a2e849de769123c8e6308be2c8961f86e158520e8360c0700e 0x21a64115e2112e253551390e418a424214b08487000555b1cb53d4f390e4b89228d236aae0b⟩,
  ⟨44,6,[0x3000300030003000, 0x5500000055000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0xaaaa1a2e879de769c26c9825d9123d8be2c89a258821f86e19856138420e8360c569595601c 0xc9d99ad9b9c619908864e6798aecb190880d1529dd8ca51dc37059aaebbb3ccf311dc370a1846213598ca32a5836⟩,
  ⟨44,5,[0x7500300075003000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x2c5aeaaaa868b9de448f62f8b2268962087e1b8661584e1083a0d8301c 0x19a4352a0b58ea3295b120d83109714a5ae0006e39d7473dee9364d40ea3086cb8ce3373dcf⟩,
  ⟨44,5,[0x5500000055000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff003000ff003000, 0xff00ff0000000000],hints 0x83a15a2e0e88220912258320cb160e84e138b2778420e89a0e8360d8967787e1f8b22f0701c83a3d86619896318be368f62f8ee2ca2e2c86e0eb1625aea258d6359dea19da2f⟩,
  ⟨44,5,[0x3000300030003000, 0x5500000055000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xff00f000ff00f000, 0xff00ff0000000000],hints 0x83a159120e84e138b2778360d8960e87e1f8b22f0701c83aaa8be3d8f62f8ee2ca2e2c86e0e9de3f8fea19da2fa022ca2e2c8320ca12778be3d8be31aea3faea3f⟩
]
def nodesBlock20 : Array Node := #[
  ⟨44,6,[0x5500000055000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff00f000ff00f000, 0xff00ff0000000000],lhints 6 0xc4ef2bc6c5aeaaaa92a1a2e87a127a9de7699a5d912428fe3d8f23b8d6318c22f8b22889a1f86e1584e1083a0c569373b81c 0x1571613488575c53459d75e434d9175e734d9651241446cd1e07c780d35b7db80c19b1456cc2e01456c36de91c7a675b91b38d2a25ca88d34e5ce88500e98038516266288188e90e3a63a29103a03946cf5204ce6ce59f4a334d8df7d634d9982561459a49169565a45666158db45681159b5a382009869638e⟩,
  ⟨44,7,[0xaa00aa00aa00aa00, 0xc000c000c000c000, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0x2c9b16aaa92a2a868ba1e779da719c26f9ba6a99a6598a609764490a3d8be2c8962487e1b8561484e0e8315f5754e4e1194301e0700e 0xa8a90aaa748daa7924a8a48aa89589aa648caa6596a894897c954962928a7e9555609289aa248baa590baa5492aa292266538266228266238e66528a66266265924969a690aaa596aa0492aa0596aaa49265755569e28a64855569928a65d651aa0249659663aa08a2a9348faa858faa8492a9359319328116138112128a0d338e6212407d3a407d3249621a616539536548946549546538936937136546d46541d4693653⟩,
  ⟨44,6,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xea00ea00ea00ea00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0xc7ac5ab2a4a8aa1a2e879de719c26e9b26a9a26598a609764490a3d8f22f8b2258921b8561484e0e8360c5793a4681e 0x19f1a234989f7c634611212134885248434411112418691144418494d35c7df70d3657df4c618328a5c619328a64411b9236c411a92474d1e07c780d35d7dd80a01d18074a2a018674c15510458c2dd10475876061e81881d61d40d36549294d35049040618228a04619028a50411091040411492461839070e6208107504203d874f⟩,
  ⟨44,5,[0xea000000ea00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0xb16baab2a1a2e779da448f63c8be2c8922186e1484e0e8360c0781c 0xe889c4670847a08a5540213c8624894e5340079c4d13ded631515448414c55942505adaf⟩,
  ⟨44,6,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00c000ff00c000, 0xff00ff0000000000],lhints 6 0x316b16aaa8aa1a2e879de769c66f9b26899a6598a4490a3f8f62f8b2258921f8521383a0c5815046c0e 0x8104172cb5d04202cb3db3e02cb81b6cf2cb59614f5c511011d2c77504042c411611f58a7d67c458410f11f59f7cf38458464b19c6c670b2d96d971171955965165c45c70f3d945964f3dc45c65165a10469225910430b21e40878b2cc40c30330d4cd35434c4cc3023183cf60160c3cc60400c7c03041187d831c30d64d35c34c64c⟩,
  ⟨44,5,[0x5500400055004000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0xb16acaaaa1a2e77912428fe3d8c22f8b2268921f86e15852138420e8360c0700e 0x88a904798844888c66d0a4610625894a6b8212380015dcfb3a6d9b52491302c8a96a5a0e⟩,
  ⟨44,7,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xfc00fc00fc00fc00, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0x2dead6acaaaa4a2e879de769c6709be6e9aa66996629764490a3f8f63c8e6308be2c896248821f8761b8661583a0c5a567595625453b4750e1c41c 0xb8ba4bbaa50cbaaa69b8b50bbae514ba5ba5ba5514bae9097e338e9082cb7e438e91d2cbb93711bac511bac71cb935139136cf9072cb9246da9132cb79e78ab9394aba8514bada57bad514ba8a688ad38e7a82cb8a838e7ad2cb9248a7ba89679244d37a87a87df7d2b95510bab710bab514b957151552c01263800e62cb09538e9261a67d58557d59159268269264cd915b0d9154d3926b26795055899a16899898795a15⟩,
  ⟨44,6,[0x5400540054005400, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0xcc2c2ab2a4a8aa1a2e879e2779da719c26e9b26a9a2659764490a3f8be2c8962486e15852138420e8360c5916354d100700e 0x22122440c9218484081941a340b8d45064061931852086d34862068102a284a89042086088d26020880d36220888f1e018680f3a218675042651499041d5140c805d34174820234d74601b9406c619d95d76275a81f6a289d81d9d451c41071452741054d35720810d3552086e595818662595b18662079989e6a08188a259645c751⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff005400ff005400, 0xff00ff0000000000],lhints 5 0x2aca868b9de76996448fe358be2c892218721b8521383a0d8300e 0x1ca728c891863095c10d281099a1211519c633330d3105215394e7c16b39a060003084670⟩,
  ⟨44,5,[0xf0000000f000, 0x5400540054005400, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0xab2a1a2e849e2779da448fe2f8b22486e15852138420e8360c0700e 0x2226431972291245b96e084897c68f72dcb491248425463047709a210d420004f156a2⟩,
  ⟨44,6,[0xf0000000f000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xfc00fc00fc00fc00, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0xc96eab76c5ad6acaaaa4a2e84a02779da709be659123f8f63c8e6308be2c896248821f86e198561183a0c599641c81c 0x15d15e38779d74538594e3a295b88e3a56035c91a214588925714570e3a175184e39c75c84925c14570926114562469c89a3ce29f54a7ce38f54f3c501924064514f24964264f88f3d83d98993c13d37104e448f70f3552e038b81554d38d62350d14562310d8845a184d70d36132370c80f20d64834f360659⟩,
  ⟨44,5,[0xf0000000f000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xfc00fc0000000000, 0xff000000ff000000],lhints 5 0x300baab5abaacaaa809de769c2448fe3d8f2308be2c8962487e1b8521383a0d830731381e0700e 0x1db1e0e3c6f0e39f8a15ce2ba95c39eee47308e39d7c5de70d941b1cef529ee5e68bcb9cfa3de47caf09762fbbebe994e52d0ba72754a15c52f0adb99bc616e5d3c05b00af2ead6⟩,
  ⟨44,6,[0xfc000000fc00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0x328b16b5ab2aaa92a1a2e879ea779da719c26f9ba6c9a2669966498a448f63c8e6308be2c896248821f86e198561183a0c5a13d444740781c 0x1e51e74099e59474073d636940da5658f40f3df22b1c7adfacf1c789042a953a90422962a9d0621c18988aa1c788f3e4ae390f3a2ace45032858ca104115914470211008471d10d184f291a4a44f3e1a6144245589255d511891b1042096581042c9656592e01c778f19cac65cf3deaeb5ea99e8a27aaa978a269145b86115145a861⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xaa00fe00aa00fe00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x2c5aaaa1a2e779da659123c8c22f8b2268921f8721b866158521383a0d8301e 0x66a8c2588423c04846d00060c41585b56d4721a0380e2d4b514a6b8691b8270ddcf83a6e⟩,
  ⟨44,6,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xfc00fc0000000000, 0xff000000ff000000],lhints 6 0xb7acead6aeab2aaa2e879de769c26e9b6659724490a3f8f63c8c22f8b2258922187e1b8521383a0d8316d5b16b5a9665513e481121d41e0700e 0x317a947e73cf2e7aa77d73cf8cd74d8c83cf8e375c8cd3cdb0d78db695d1b6979eb4d5cd8ab482b253c28a5492b2b3cf8655d0b6b9d0b6b5d7b659e58e558eb2634db6659582534d1d83c11a44811643cf1184927d85d32a87932685d77d87988e43408d8a408d834d8e4a64b180d889b95989b89ab18958⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xfc00fc0000000000, 0xfe00fe00aa00aa00, 0xff000000ff000000],lhints 5 0x2dead6b4ac6aeab2aa9de709123f8be2c8921b8521383a0d8301e 0xcc3320701ad011a82c086812bc200186d9cda4221a209c2330cc94a1d10bc2e935cd⟩
]
def nodesBlock21 : Array Node := #[
  ⟨44,5,[0x2000200aa00aa00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xfc00fc0000000000, 0xff000000ff000000],lhints 5 0x2dead2acaaa8b9de6e9123f8e62f8b2248862087e1b83a0d8301e 0x1c701846c084cd080041ad6d7882808c832162d0c8319be2f190644a4320ca8f73d4a⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xfc00fc0000000000, 0xff000000ff000000, 0xff00fc00ff000000],lhints 5 0xb7abaad6aeab2aaaa28ba027e9de769ba3c8c22f8b22483a0d8300e 0xc652c9cf0c6210ca810b5c14ad7592d735b26b10481329463294633a060002a31d06⟩,
  ⟨44,5,[0x3000000ff000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xfc00fc0000000000, 0xff000000ff000000],lhints 5 0xb7abaad6aea2e779da709123c8c22f8b2248861f8521383a0d8300e 0x1e490ca81095a194213211301050153dea3192a0002f52d8a18e29a85c184e137a9ea⟩,
  ⟨44,7,[0xc000c000c000c00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0x2ebb16b5aaaa4a8a8ba1e779da719c26f9b26a99a629764490a3d8f2398c22f8b22587e1b8561483a0d831715bd554fd214502a0700e 0xa8b90baa644daa6924a8b44ba89609aa544caa5618a894497c95c97e92cb7e95d77c92c9aa3451aa8914aa8451aa39236a838e6a32cb6a338e6a82cb75d74a6a36a369a249a9244faa760faa7451a926121922c11613811212cb0d238e7e12407d2a407d22497e1a616926926968d36960956928d2aaa451aa0618aa0451aaa61869938e75a2cb68838e75e2cb69f690aa024969a6a2aa08e269b9e775c4926879e775a492⟩,
  ⟨44,6,[0xaa00aa00aa00aa00, 0xae00ae00ae00ae00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0x301b16acaaaa4a8aa1a2e879de719c26a9a2659764490a2f8b2258921f86e198561484e1083a0d8317050522 0x15b15e3c979b6c53c50d20dd3c87524833c30d10e114585144314368f1dc6c770f3da6da70b19a14568b2dc14570e11a0c368e35c0c388f3d849260f3e24924c51424515451534515c30d78615030d786059c65669959c71669a88f31f48c7cf3e24927c51412cb00515f2cb7c30d784a5c30df85f59c71f69a7dc71669a59641f610⟩,
  ⟨44,5,[0xae000000ae00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0xb16acaaaa1a6a8b9de76912428fe3b8be2c8921f8661484e0e8360c0781c 0x18a9284678853688a554421750624890853c008384714211a414f53c8415c56a46915aeb0⟩,
  ⟨44,6,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff000c00ff000c00, 0xff00ff0000000000],lhints 6 0xc66c5ad6aeaaaa2a868ba1e849de769c6709be6c9a266996629123d8f2398c22f8b22889e268962187e1c86e1483a0d831720ac0e 0xa4f3dd55574f3e95551e21e63ca9a28873c769a1477450d50e43c69155433c30dc0e86e8a172c36c30dc0e81c7a1ca031c37cf3e78929cf3df89f9d68df6df7d67e76e79c71df59f7c71e758c7da1210c385681f0c340f26554994f3d055040241e61e79979061040e21e1c778e3501c7783010a004030dea1e4164147d15014d07d0⟩,
  ⟨44,5,[0x5500040055000400, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x2c5ab2a1a2e779da448f2388c22f8b22486e15852138420e8360c0700e 0x889904780844b08c65c8a4490625096e5b021224001598d7b26b9ad24492c2a8a549522c⟩,
  ⟨44,7,[0x3000300030003000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0xbd6baab2aaa92a1a2e879de769c6709be6e9b26a99a629825d912428fe3d8be2c8962087e1d86e198561383a0d831795dd7455d42491160781c 0xb4b9cbb6950db699e7b4b50bb53652b6b512b6b659b535138936106db2cb8886176d32cbb6550cb689ccb68514b659e58283c17252c18253cf7282cb7df7ca8a24d3725725b55511b6a651b6a514b556551552c01243c00e42cb0953cf6e44ce895ace8954d36e4ae4715a15816956816a16715955b6d9e7b63514b639e7b6d51481ab2c7e12cb807b2c7da2cb71c709b634c98a28a6b6396581d5557e05968065557de596⟩,
  ⟨44,6,[0xaa00aa00aa00aa00, 0xba00ba00ba00ba00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0x304b8eb4ab2a4a8aa1a2e87a1a839de719c26e9b26a9a2659825d912428fe3d8e2308be2c8962486e158521383a0d831765d41e 0x1611643089218453050d30e33078d34c33030d20d514509244314374c1a284688c31d85d88901d14074926214574b1190c39cb29d0c3a0c31c4d370c3284d35051412495c51542496030db9656c30d896562289b75d5a281875d34c3264cf98c30d4cd34515f2497c514d2495430cd94d3430d595e36235a74e6a288d74d65940d70d⟩,
  ⟨44,5,[0xba000000ba00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0xab2a1a2e779da448fe3d8e2308be2c8922186e1484e0e8360c0781c 0xe899c4680847788a5548213d0624894d52c0089c4b1456ca2d505408415455a4a925b971⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xba00ba00ba00ba00, 0xcc00cc00cc00cc00, 0xff000000ff000000, 0xff00f000ff00f000, 0xff00ff0000000000],lhints 5 0xaeaaca868ba12819de448fe3d8ee388c6308be2c8921484e0e8360c 0x11c059a461006333c20281af6ccce33814052adab66f8bcca31c07050e981ce899d87⟩,
  ⟨44,6,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff003000ff003000, 0xff00ff0000000000],lhints 6 0x31db16baab2aaa868ba1e779da719c26f9ba6899a65992629123d8ee358d22f8b2258821f8661383a0d8317856525 0x91e79a2cb69e7a42cb91e3e22cb89e7a42cb6181626852912612c985144a2ca2980e36038d88ca60a2a22a36238e288a60a70b19f7867cb2dc79c7d97dc49c71471f49f7d739c88e71371f89f70a11d8c474a29c8dc30b22044880b2cc44c40240c54c31631055030131b88d6c06cc88c6ca1cc84730a29b85b31f31071041f40c70c⟩,
  ⟨44,5,[0x5500100055001000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x2c5aeaaaa8694a2e779123d8f22f8b2268921f86e15852138420e8360c0700e 0x889904788844b88c66c8a4610625894a6c0212400015a907be6d9b524b9302c0a55955ce⟩,
  ⟨44,6,[0x3000300030003000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xff000000ff000000, 0xff00f000ff00f000, 0xff00ff0000000000],lhints 6 0xc4af4b72c5aeaacaaaa1a2e84a02779da709b25d9123f8f63b8d22f8b2258821f8661383a0d8317656927 0x29125c2c971144a2ca41939d2cb7596502cb82015028558b19a64668b2d665668a1164c458a29a4da69041675659041a75a30b21b4486cb2cc44c6ca1cc70730a29b71b30131540d54054c40c31a30f58f3da3cc58c8595de2cb7996612cb51f0de28349d75e41079d75241051461e59678c31f3cf08c31e3cf⟩,
  ⟨44,7,[0xaa00aa00aa00aa00, 0xcc000000cc000000, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0xb42c5aeab5ab2aaa92a2a868b9de769c6709be6a99a6498a60976448f63c8c22f8b2268962487e1b8561484e0e8360c61985611836097b3bcdd2e4a50700e 0xc4ea0ec6b5d1c6ba28c4e5cec4c70cc6a5d0c6a71cc4c5cc74cbcc77038e770bef74c38cc715cfc69a0fc695d7c71a287e97e97df38e7e07d67e954d7ee30c7ee5547e930cc717cbc655d7c65c65c715d77dd7d2c6538e7de7ca7e330c7e47c97df30c7df7e7c65a67c585d3c6c713c6c5d7c58718758381766bc176638e758bd8166300118b400d830c0a6b667d8a587dbb997dba5a7d8b987d88987df8487df1c67d87d8⟩
]
def nodesBlock22 : Array Node := #[
  ⟨44,6,[0xcc00cc00cc00cc00, 0xee00aa00ee00aa00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0x31fb16baad6acaaaa4a8aa1a2e769aa6498a5d9123d8f2308be2c89e268962487e158521383e0e8360c605805f97c0700e 0x9887489a048c9a075d9884889865c699f48b99f5d798648660690662520862592460620699348d9a15cd9a14929935d361320161c90161c20861391315c1801138800d318609c89c9a648a99e74a99e4929a675d65e44965920865a45065e20865e3c76631866633ce65e1866e35946de4d36de5956e34d3⟩,
  ⟨44,5,[0xcc00cc00cc00cc00, 0xe000a000e000a000, 0xee00aa00ee00aa00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],hints 0x20e8568b83a20882448b29a83aba83a1f87e2c9101c0720eaaa76ab2835f62cc7e2c9760e2220e8320c8be2f84e138b28b83e0e89a0ea5a96ab2a19de76a8676a86629aaa1⟩,
  ⟨44,4,[0x1f005f0000000000, 0xcc00cc00cc00cc00, 0xee00aa00ee00aa00, 0xf000f000f000f000, 0xff000000ff000000],hints 0x8320eaea0c0701c83a2f0380e8327683e0e89a0e8360c8920c8c22f8f22f8560ea2e0e8820c9120c87e1f8b22f84e138b28b⟩,
  ⟨44,5,[0xcc00cc00cc00cc00, 0xee00aa00ee00aa00, 0xf000f000f000f000, 0xfe00fa00fe00fa00, 0xff000000ff000000, 0xff00ff0000000000],hints 0x20e8568b83a2cc7e2c5fe0e2f20e9760c852448320c83aba832ac8322c8e22c8be0e8d20e8be768be0c8be8384e138b28b83e0e89a0eb5ea1a866a8360c8920c8c22f8f22f⟩,
  ⟨44,4,[0xcc00cc00cc00cc00, 0xee00aa00ee00aa00, 0xf000f000f000f000, 0xfe00fa0000000000, 0xff000000ff000000],hints 0x8560ea2e0e8320eaea0c832149120c0701c83a2f87e1f8b22f0380e8327683e0e89a0e84e138b28b8360c8920c8c22f8f22f⟩,
  ⟨44,5,[0xe000a000e000a00, 0xcc00cc00cc00cc00, 0xee00aa00ee00aa00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x2baad6aca869aa5a8b9da448f2388d2308be2c89a208561383e0e8300e 0x8b0118ce4485612188489624813421110188e28c693525a94390e15856085e99d675⟩,
  ⟨44,5,[0x1000500010005000, 0xcc00cc00cc00cc00, 0xee00aa00ee00aa00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0x2baad6acaaaa1a2e779da448be2c89a2487e158521383e0e8360c0700e 0x1111208ee108961252c704249804f31991291641894283e4f731ccb12c4a09adacab2⟩,
  ⟨44,6,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xee00aa00ee00aa00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0xc7ec5aeab5ab2a4a8aa1a2e779c6709aa68992629825d9122f8b22889e268962486e15852138420e8360c3c4df2e8a7 0x19d1a044a81d74644611311f4497d34c44441231241869238c418495145b4d36d14654d35061948cb6061948e354411a86168411586195121e74879146575d7901d61865d039e18678d16210488d31e10489971e65c7997a26629514654d39514654d35061948e35061948cf0c41028610441008616594a56d265e7998a265e7998a2⟩,
  ⟨44,6,[0x2200aa002200aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0xca6c5ab2aaa92a2a868ba1e779da6899a629764490a3f8f63c8c22f8b2258921f86e158521383a0d8301e0700e 0x8c57058df3488df71c8c53458c35038de3478de5148c33435434c35621455624d25431438da3468dd7068dd34d8da71a59d24259a14259a24959d14559a30459b0c359b30b59a0c38ce34a8e050a8e034d8ce50e54e14155924161914560e2495d90c05ce8405ce0c35d985958e74e59168f59175058e68e⟩,
  ⟨44,6,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xfc00f000fc00f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0x30cb16acaaaa4a8aa1a2e849da709be6c98a5d9123f8f63c8ca308be2c89a258921f8561484e0e8360c0700e 0x8846c489e30789e6db8843048824c289d30689d4d38823025c24825e11045e14925c210289a30589c6c589c30c89a6da55c48f55a10455a48b55c10459c28359a08255a28955c08288d30889f4c889f30c88d4cd50d10151948151910450d48d61908060d80060d08261981954d70d55168e55171054d68d⟩,
  ⟨44,6,[0x3000f0003000f000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0xcb6c5aeab5ab2aaa92a2a868b9de76996629825d9123f8f63c8c22f8b2258921f86e158521383a0d8301e0700e 0x8c56858dd3488dd69a8c53458d93468db6868db34d8d969959b24259914259924959b1458ce34a8de4ca8de34d8ce4ce50e14151824151814550e24958e6ce59164f5916d058e64e8c34c38dc3478dc4d38c334350384352214552285250314358380358c6445cc80b5c364355f38054360054338355f618⟩,
  ⟨44,6,[0x3300ff0000000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000],lhints 6 0x2d0b16acaaaa4a8aa1a2e879de7698e6297a5d9724490a3f8f63c8c22f8b2258921f86e158521383a0d8318c62d8a61cf2380bf2a01e0700e 0x78b6cb7ab34d7ab6da78b34b826442823342823451b2634d82350c8242cb8245138232cb7963417a24417a234d7964511a22c0156a801162cb0e2aa28169968198d78199988168d6b15a10b2534db25a257d534d2959cf75c2cb25c9dc7552cbb2598eb158ceb159958658e321ca527555921d5a5575c596⟩,
  ⟨44,5,[0x3300ff0000000000, 0xaa00aa00aa00aa00, 0xbb00ff00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000],lhints 5 0x2b1aaaa1a7a9da56949de448fe2f8b22486e158521383a0d831896201e 0xcad180092906a1952548c430d1f47952548e23ac1f47b1882cca71c86632dee5d576⟩,
  ⟨44,4,[0x3300ff0000000000, 0xaa00aa00aa00aa00, 0xb000f000a000a000, 0xcc00cc00cc00cc00, 0xff000000ff000000],hints 0x781e86e0e8320eaea0c8320d8920c0701c83a1b9da77a86760380e832768560ea7a0e84e138b2778520ca760c87e1f8b276⟩,
  ⟨44,4,[0xb000f000a000a00, 0x3300ff0000000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xff000000ff000000],hints 0x781e86e0e038238380e038118600e1384ea020e0ec3b882770e40e8b00e8321b83a0c832248360c9d80e8300e832208520c⟩,
  ⟨44,5,[0x3300ff0000000000, 0x88000000aa00aa00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000],lhints 5 0x2d0aaaa2a8695a528b9de629123f8ee398be2c8922087e1b83a0d8301e 0x46c080041882708c8320641ac5f378c8320681a39f67a52b1c0660b42a535e5ab508⟩
]
def nodesBlock23 : Array Node := #[
  ⟨44,5,[0x3300ff0000000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xf300ff00f000f000, 0xff000000ff000000],lhints 5 0x2aaa8a9da2e879de76912428f23b8e6388c22f8b21b83a0c0781c 0x306c1b06c188410906f841ef841e000c8e319ce319c63acca1c4652cdb24a5af41a86⟩,
  ⟨44,5,[0x3300ff0000000000, 0xaa00aa00aa00aa00, 0xc0000000f000f000, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000],lhints 5 0xa8a9ea1e779da4490a3c8c22f8b21f86e158521383a0c0781c 0x346d184271c2318346d188518460000cef529ea5b14f529e61c8659a4844c1c94212a⟩,
  ⟨44,7,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00cc00ff00cc00, 0xff00ff0000000000],lhints 6 0xb82c5b0eaeab2aaa8aa1a2e879fa779da719c26f9ba6a99a6498a609764490a3f8f62f8b22889e268962187e1c86e1483a0c64d9163d8e511283cce1310aa1d80e 0xcf35d7ce6ce6ce65d7cf38cbccfacfcf05d2cf0aebccf5cf7df7cdccf98dccc70cced5ceced71cccc5cc8cc94c8139138139538cc78c74c6cc2b23cf2726da74c3ccce85d7cf1ae9cf15d7ce8ae875d76cce89a875d3cf7e87e87e07d48e84d37ea30c8ea4d37e830ccd85d1cee711cee5d7cd87188d82188198998198d98d88587585901e73cf1a75957583cf167300118bc00d830c0a7be77d80588d9a198d98d97d8a18⟩,
  ⟨44,6,[0x5500440055004400, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0xcc6c5ad2aca92a2a868ba1e779c6709ba6a9a2609764490a3f8f6388c22f8b2258921b8561484e1083a0d831453d4ac0700e 0x1e01e33cb8e08073c71561623ca8965853c51551661c79955051c578f26180984f3de81e84c21e1c778c3211c778e19f1457ce35e14540f3e559294f3d05904070443016471d030c0c501090040514292442141b7916e18507909d659d3cf7565a73cf64c31a1c768c3171c762491c14572491814569e7978615de79a8616594dd410⟩,
  ⟨44,6,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00cc00ff00cc00, 0xff00f000ff00f000, 0xff00ff0000000000],lhints 5 0xb86dbb16baaaaa1a2e849fa7a9de769c26f9b26599262912428fe3d8be2c87e1b83190 0x1244909b201cd63904a9042c2124490217e72e464e49922b8c5568a23a8ca9118c85b94b7298c52a205814b0298c5⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00cc0000000000, 0xff00f000ff00f000],lhints 5 0xb6ed1b16aaa2e849ea779da64912428fe3c8ee358d2308be2c87e1383a0c 0x11ad2042924c800348d232ab74216108904219784650a14b418c8529de5794af29945⟩,
  ⟨44,6,[0xf0000000f000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00cc00ff00cc00, 0xff00ff0000000000],lhints 5 0x2eeb16a1a2e849fa7a9de769c26f9966498a4490a3d8be2c89e268861f8761c86e0e83192 0x15c50067c8c42729ca9ef722ec6abaabaa8ea8adb153194b5b18b20d23a2d745b18b729ca7ca3268c217d6155d174⟩,
  ⟨44,5,[0xf0000000f000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00cc0000000000],lhints 5 0x2d1b168ba127a9de769924490a3c8c22f8b21f86e1584e1183a0c0781c 0xcd41b92e492a329531084e38ca714212a000678295052d8a725c968c42b45f154150⟩,
  ⟨44,6,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00cc0000000000],lhints 6 0xb82d1b32c5b0eaeab2aaa2e879de769ba6d9925c912428fe3d8f2308be2c896248821f86e1584e0e8360c6659865d9464990519293d8e3320ad1dc1e0700e 0xc12a52c6c694c6ca69c526928908503eb6973ab861890690bd08102ee4922ae81fbd0490927693c6da53c6d69ac67a67bef542c27482c67555c23492967651c28410968658c2741089b69636a85632a69a89b85bbdb481266541226492bdb5551e640019bac015b410126ae6c1b0db95e9dc95e95dc1b9db⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00cc0000000000, 0xff00ee00aa00aa00],lhints 5 0x2c3b0abbabaacaaa779123f8be2c8921b8561383a0d831966541e 0x3548295053c4a218c23540632b06ea51c6329c0020a41a46b5a9f22a0a81c06f9b9ee⟩,
  ⟨44,4,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000e000a000a000, 0xff000000ff000000, 0xff00cc0000000000],hints 0x83a15aa20e83220ab20c8320eb160c84e138b2770781e86e0e8360c8920c87e1f8b2760701c83a1b0380e832769da77aaa76⟩,
  ⟨44,4,[0xf000e000a000a00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xff000000ff000000, 0xff00cc0000000000],lhints 5 0x2809de768b2248821b8620e8360c1383b08c1e0440e 0x296082116f1094802da000d000052032da632906330e6700c0⟩,
  ⟨44,5,[0x2200aa00aa00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00cc0000000000],lhints 5 0x2e0b0aacaaa8b9de6e9123f8e62f8b2248862087e1b83a0d8301e 0xcf0184cd0846c0ad6d78004188280962d190640c8319be2f4a464190320ca8f73d4a⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00cc0000000000, 0xff00fc00f000f000],lhints 5 0xab2aaa2e879de769724490a3c8ee398c22f8b21b83a0c0781c 0x14a35ac634c4621326d58d637c20f4218f084837c20f718ce3324600064718ce31d46⟩,
  ⟨44,5,[0x3000f000f000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00cc0000000000],lhints 5 0xab2a8a1e779da4490a3c8c22f8b22087e1b8561383a0c0781c 0xcb21a26968da321130084c38463039d2a000667a94f52d8a725a368c428c23053d4f⟩,
  ⟨44,7,[0xcc000000cc00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0x2edb16c3aeaacaaaa4a8aa1a2e879fa779da719c26f9ba6a99a629825d9123d8be2c8961f86e158520e8319d6719b51d2a3dce4328af0b41e0700e 0xb8e94eba8510ba8965b8e50eb8d5cdba750fba75d7b8d50d60dacd32d38e2edaeb60d38dba2514bac963bac514ba29626986826a26a269a38e6a24d36a434d6a44d36a234db95512ba95d2ba9514b955d5615381261ac122138e615ad51e1340195a8015534d121aa16956956968966960d6695895bae514ba0965ba0514bae96569d691ba038e6994d369a34d69f4d369e34d69a6a6ba08a269b59669c55568a59669a555⟩
]
def nodesBlock24 : Array Node := #[
  ⟨44,6,[0xaa00aa00aa00aa00, 0xaa00ee00aa00ee00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0x302b16baab2aaa92a2a868ba1e779c6709ba6a9a260976448f63c8be2c8a2268962487e1c86e198561484e0e8360c5201e 0x11e12140785e7844040940a04068145024020a40a510496490210271015f7857d041c79c7cf01c10070f39f10470d0dd08274d31c08299041b79e6d042679e5441199245c411790958209a96568209696561f7d871c61f7d871c4d02e250b8904135134c410190a5c41139138820938c84c20a28e261f7d37134df4987126184536d1⟩,
  ⟨44,6,[0xcc000000cc00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00f000ff00f000, 0xff00ff0000000000],lhints 5 0xb16baaaaa1a2e849fa7a9de769c26f9ba6c996629764490a3d8ee358d22f8b21f83a0c 0x14350ce3b8c2150d430035b58ea39be7361a7a9d2d310864c90992164491092221041dc77839b04a61b8ef1341104⟩,
  ⟨44,6,[0xcc000000cc00, 0xf0000000f000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 5 0xb16baa868ba127e9ea779da709be6e9b2629123d8be2c87e1b8561183a0c0781c 0x65b0d685a0991a2889064394eb239d09000698a5314a9495a168c0c42649d24c5314591630df9866f2525497b60f⟩,
  ⟨44,7,[0x3300000033000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0xbe6c5ad6aeab2aaa8aa1a2e779da719c26f9ba6a99a629825d912428fe3d8f2308be2c8a227896248861f8721b8521383a0d8319f3e4e6338b10780e 0xbcc9ccbec50fbec9e7bcc50cbc76c7be950bbe96dbbc750770768772e30c72e699707307bef50abe89cabe8514bef9e779c78171c30c7a87a88684487ad1c786d4507a81c7bd550ebea6cebea514bd56d57154cd72530c7254d271530c1651c0115ac00d51c70a5ae5795a15858b56858a17795b55bef9e7be4514be49e7bef51479e789be430971dbae7221c7723bae71c1c7721726be4a2671f96571c555706965720555⟩,
  ⟨44,6,[0xaa00aa00aa00aa00, 0xbb00aa00bb00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0xc16c5b0ab5ab2a4a8aa1a2e869e6789de769c6709ba6a9a2609764490a3f8be2c8962486e158521383a0d8301e 0xdb0de28679b6c328304e05d28574e38128104d0620c388d3010c18ca11c6c470a2a36db70700f0c03c71dc0c37090a004180921c0418ca29538e54a2a338e4830cf1c74430d21c74010547df5010507df49c71382045c5d281758a2a138e84a29638e3c30d61c75830cf1c758105a7d96810567d659c5938184dc7168163cf2d654b⟩,
  ⟨44,7,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf0000000f0000000, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0xb4ac5ab2aaa92a2a868ba1e869de769c6709be6e99a629825d912428fe3d8f2308be2c8962487e1b8561484e0e8360c68478170320781c03806 0xb4a98ab6948db699a6b4a48ab48648b6848cb68659b484887c87c87df28a81a817b6d9a6b61492b619a6b6d4927df7d8b6128a7df7ecb61208b6348bb6798bb67492b639a36a73836a32836a338e6a728a6e34498252088254506e32086a36a36a57256a57a56a3723b5348fb6a64fb6a492b536536932826a23826a228a69338e6e2201813ac18132086e2ae26936936a47646a41e46936931939d31568d41169d50138d3⟩,
  ⟨44,6,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xfa00aa00fa00aa00, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0xc82d9b62aca92a2a868ba1e86a0e779c6709be6e9aa689825d9123f8be2c8962486e158521383a0d8305e0cc1e 0x15c15f3087dc7053058cc3173cf5cc3233cf5451502494851552490cf0de30778f3c33030e10e11454223831438168035430d60e056060c19d70674c31871874901814060925d14561461b4db6d46d84d860b11b0c36cb2980c368c3233cf8cc31a3cf40515a24968515024941035a5cd4430da81a6830d181969d68261805d75a618⟩,
  ⟨44,7,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00f000ff00f000, 0xff00ff0000000000],lhints 6 0xb86c5aeaaaa868ba1e849ea779da719c26f9ba6698a5d912428fe3d8f23b8d6348c22f8b21f84e0e831a36718f5e55b5252f4b4fb1ec5f0d408 0xb6d6dbb62451b626dbb6d451b5aa16b6b451b6ba28b5a45182080eb5a88eb6d6dbb6c451b6c6dbb6d45182080db6c88d82069a82c82c85c859b6444fb69a0fb69451b64a248697e98647648648648697697296952e4ad52a469a729ae9864264867b25867866864b24b52450b6a6d0b6a451b526d286a32a85285285285286a7aa7122121e36941a3163712692863123852b12852852863b230d2a52098913058a57012912⟩,
  ⟨44,6,[0x5500500055005000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0x332b16acaaaa4a8aa1a528ba1e779c6709be6e9aa689764490a3f8be2c8a2268962487e1b8561484e1083a0d8314a1f41c0380a 0x1e01e448b92080748715616348a8d65854851551671c79d55051c579226280989249e81e89121e1c77914221c778f19f1457cf39e145a1236558d9524a85969470845426071e555594505c9c17051659e50e286579e96288079ea1659d4927565a849261531b1c76d55571c772799b1456e79dc14565e79a8a269e7998a271c4dd953⟩,
  ⟨44,7,[0xf0000000f000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0x2eeb16b5aaaa4a868ba1e849ea779da719c26f9ba6698a609764490a3d8f2308be2c87e1b856138460e831a5675915954b4c0d11f8610e01e0700b 0xb8ea0ebaa511baaa28b8e50ebae69abad514bad69abae51482080f82d82d82038eba4510ba9a10ba9514ba4a246e94822e43822a44926e938e724724867b65867266724b64b95513bab693bab514b956956d53812234811e338e6d5492723723855b55855195723b63155a551189160d8a57015915bae69aba2514ba269abae514821819ba238e81b80dba2b4d81db2c82092481fb2c82092481e5558208e380c5558208e3⟩,
  ⟨44,6,[0xaa00aa00aa00aa00, 0xaa00fa00aa00fa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0x303b16b4ab2a4a8aa1a2e879de769c6709be6e9aa689825d9123d8f2388c22f8b2258921b8561484e0e8360c5301e 0x11d1202c781d7442c409109f2c67d14422c20970a31048d78c21026cb15e74578b2db75b78801b1006c821e1046ca0dc08270a25b08290b2d975d64b2e475d4841182086041142084820988e16020928e355e7966db59e7956db30b2e244e88b2cc44c30410120850410c2084c208c8cc3020938e331e3106cd41e3cc6cc5d768c64c⟩,
  ⟨44,7,[0xf0000000f000000, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0x2fcb16baab2aaa8aa1a2e879de769c6709be6e99a629764490a3d8f23b8d6348c22f8b2258921f852138460e8360c6a1a74c48018c3c0380d 0xb19956b2a451b2a965b19451b08688b2744db2769ab084487df7cb7df6597c87c8b2344cb2694cb26451b239636e66556e3a956e36596e6aa682340982420882440f823208b1244eb2868eb28451b126926d26d26e26546e21626d2652822201812a41812208822a621129920d88d30989970128d2b2c7c7b21451b21b21b2c4517db7cab2164a7e07ebb212087dc8e37df9247de8e37df9247dd8a27df4927c68a27df492⟩,
  ⟨44,6,[0xaa00aa00aa00aa00, 0xaf00aa00af00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000],lhints 6 0x306b0aaca92a2a868ba1e799de769c6709be6e9aa689764490a2f8b22889e268962486e15852138420e8360c1943e 0x11e1213c885e7843c40920a03c78124823c20910971045d14421026cf19f7867cf3db79b7ce15b1046ce31f1046cb0dd08274b29b08290f3d949264f3e44924c41134495041134516020988a26020988a255b6d675d59b6d575d68f3e34928cf3da4924c411a45168411344d68209889c60209a89a69f6816db01f7da6da5d741a650⟩,
  ⟨44,6,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xf000ff0000000000, 0xff000000ff000000],lhints 6 0x2fcaeaacaaaa2a868ba1e779da709be5e9765c912428fe3d8f2308be2c8962487e1b8521383a0d831ae6b5aa6a482198400781c0400e 0xa94a54aa434daa4a6479434da8b68b7df34d7df6997cb34b80b6cbaa650faa66dba8b50b76540376234376241076534d72250e2a590e2655147229228224cc8232cb8234d28222cb75534276140276134d7554107155112276d11e75147156d58212c0815a008152cb821a21195955158896118957055895⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xf000ff0000000000, 0xfa00ff00aa00aa00, 0xff000000ff000000],lhints 5 0xbf2b1aaaa1a7a9da56949de709123f8be2c8921b8521383a0d8301e 0xcc3320711ad011a82c086a12c0200186d949a4221a209c2330cc94a2740bc337364d⟩,
  ⟨44,5,[0xa000000aa00aa00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xf000ff0000000000, 0xff000000ff000000],lhints 5 0x2aaa8aa1a5694a2e779123f8ee398be2c8922087e1b83a0d831ac6ac1e 0x34b128cae18d0f180062b18f81069194c531ecf1cc7694290298a6528751d4500c16b⟩
]
def nodesBlock25 : Array Node := #[
  ⟨44,4,[0xaa00aa00aa00aa00, 0xce00cc00ee00ee00, 0xf000f000f000f000, 0xf000ff0000000000, 0xff000000ff000000],hints 0x84e0ea2e0e8320e8fe0c832139120c0781e83aa184e3984e778327a8327783a1a83a0f84e1f84e3c83218832aa8be2f8f277⟩,
  ⟨44,4,[0xaa00aa00aa00aa00, 0xc400cc0044004400, 0xf000f000f000f000, 0xf000ff0000000000, 0xff000000ff000000],hints 0x8ee0ea2e0e8320e8fe0c832149120c0781e86e0e84e13912779de0ca120c0701c83a1b87e1faaa2f0380e832768be778f22f⟩,
  ⟨44,5,[0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xf000ff0000000000, 0xfc00ff00cc00cc00, 0xff000000ff000000],lhints 5 0x2a8a868b9de76972448fe3d8be2c8962087e1b83a0c0700e 0x10641a0721c1021ac4239c42330441906f7a22d388e2084644a949295090004e4a949⟩,
  ⟨44,5,[0xc000000cc00cc00, 0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xf000ff0000000000, 0xff000000ff000000],lhints 5 0x2aaa868b9de768fe3d8ee388be2c8961b8521383a0c0700e 0x2c701886d108b01186619230388e2084664aa490004e4b18930cc3420e2389ef62589⟩,
  ⟨34,4,[0x4400880044008800, 0x5000a0005000a000, 0x5500000055000000, 0x5500aa0000000000],lhints 5 0x2c5a8aa1a2e89a1e819de7491e2c89e25890390d81e0440e 0x3bce94212f71d0703c114122f781000301239e4c500e05a07078e0842deb81c4b609673c18c5982d001a62ac00⟩,
  ⟨31,4,[0x2800280028002800, 0x3000300030003000, 0x3c0000003c000000, 0x3c003c0000000000],lhints 5 0x2baabaaaa2e8aa1a8491a328be2c8a2278904a0d8200780e 0xbc314122f785012bcab4216f715052c8ac08592514214a07078e08425e949c4d085a73242181409601252c18c⟩,
  ⟨36,5,[0x8800880088008800, 0x9000900090009000, 0x9900000099000000, 0x9900990000000000],lhints 5 0xb16baa528b9e259962579465093e308b228895bd6f1bb6e9b96e1b76d9b56d1b36c83608011 0xc4350c72317735a6c230bbf4fbf6316775a5be2fb3f8fb76105779c4be0f44a223ef429ee319cb5234a012e781a6610a4b92265e01cba0ac9efae7b9⟩,
  ⟨36,4,[0x800080008000800, 0x8800880088008800, 0x9000900090009000, 0x9900000099000000, 0x9900990000000000],lhints 4 0x2c5aea9aa2e809e23a8da308b22889411 0x23928393a2b23634252404c39392b2b1174⟩,
  ⟨36,4,[0x1000100010001000, 0x8800880088008800, 0x9000900090009000, 0x9900000099000000, 0x9900990000000000],lhints 4 0xb16baa528b9e2308b2288943608011 0x4584358334a3225711490378585a4a4b366⟩,
  ⟨36,4,[0x880000008800, 0x8800880088008800, 0x9000900090009000, 0x9900000099000000, 0x9900990000000000],lhints 4 0x2c5aea9aa2e7f9ee788ee308b22889420 0x539313911ab1383606b17163939221c1c44⟩,
  ⟨36,4,[0x1100000011000000, 0x8800880088008800, 0x9000900090009000, 0x9900000099000000, 0x9900990000000000],lhints 4 0xb16baa528b9e2308b2288943608011 0x4584358334b3225614600398585a4b3b376⟩,
  ⟨36,4,[0x88008800, 0x8800880088008800, 0x9000900090009000, 0x9900000099000000, 0x9900990000000000],lhints 4 0x2c5aea99a5e94a2e808ee308b22889436 0x2572167112b10872a281918332b2b1c1c44⟩,
  ⟨36,4,[0x1100110000000000, 0x8800880088008800, 0x9000900090009000, 0x9900000099000000, 0x9900990000000000],lhints 4 0xb16baa528b9e2308b2288943608011 0x45a435b334a32561146003785a4a4b3b396⟩,
  ⟨36,4,[0x8800880088008800, 0x9000000090000000, 0x9000900090009000, 0x9900000099000000, 0x9900990000000000],lhints 4 0x2c5aea8ba227895e308b2288943608011 0x45a435a3347a5a5b4c32256114600386996⟩,
  ⟨36,4,[0x8800880088008800, 0x9000900090009000, 0x9900000099000000, 0x9900900099009000, 0x9900990000000000],lhints 4 0xb16baa528ba027895e3b8da308b22889436 0xa3a363a32293a311cd70034b44b45848448⟩,
  ⟨36,4,[0x8800880088008800, 0x9000900000000000, 0x9000900090009000, 0x9900000099000000, 0x9900990000000000],lhints 4 0x2c5aeab6a2e78962308b2288943608011 0x45b435734b395b4b4c32256114600386aa6⟩
]
def nodesBlock26 : Array Node := #[
  ⟨36,4,[0x8800880088008800, 0x9000900090009000, 0x9900000099000000, 0x9900990000000000, 0x9900990090009000],lhints 4 0xb16baa6a94a2e789623b8ea308b22889420 0x332cc22692119d7b2c2844845a400248448⟩,
  ⟨36,4,[0x8800880088008800, 0x9000900090009000, 0x9900000000000000, 0x9900000099000000, 0x9900990000000000],lhints 4 0x2c5b12baa2e78966308b2288943608011 0x45795a435c334c33cc3225611466bb60038⟩,
  ⟨36,4,[0x8800880088008800, 0x9000900090009000, 0x9900000099000000, 0x9900990000000000, 0x9900990099000000],lhints 4 0xb16baa6a94a2e809fe78966308b22889411 0x33229c51dd118911bc1466447a446640016⟩,
  ⟨41,5,[0xa0000a00a0000a00, 0xc0000c00c0000c00, 0xf0000000f0000000, 0xf0000f0000000000],lhints 5 0xaaaa1a6a8ba1e8696e5a95e5494a498b21f87613845ca725c871dc6715c470dc2705c06fc4e09423 0x73f826f662a779ca3e6fcee70cfb9067a735ef9b57a214ede1aee31af9efc6a72c7f9247e733eb9a37de02ea20b69efb7e31bebdabff7b27fde1eb7a⟩,
  ⟨41,4,[0x8000080080000800, 0xa0000a00a0000a00, 0xc0000c00c0000c00, 0xf0000000f0000000, 0xf0000f0000000000],lhints 4 0x2aaa868ba1e8695e2c8ae1d8444e09423 0x22a36a6911436a6800348976a6a5353b9c8⟩,
  ⟨41,4,[0xa0000a00a0000a00, 0xc0000c00c0000c00, 0xe0000e00e0000e00, 0xf0000000f0000000, 0xf0000f0000000000],lhints 4 0xaaaa1a6a8ba1e8695e2c87e1d84e128444e 0xa16a6a1b1b336a214199556a141488cd7⟩,
  ⟨41,4,[0xa0000000a00, 0xa0000a00a0000a00, 0xc0000c00c0000c00, 0xf0000000f0000000, 0xf0000f0000000000],lhints 4 0x2aaa869aa2e87a1a2c876138444e09423 0x22954468115a696707578b7696933b8b8c7⟩,
  ⟨41,4,[0x5000000050000000, 0xa0000a00a0000a00, 0xc0000c00c0000c00, 0xf0000000f0000000, 0xf0000f0000000000],lhints 4 0x2aaa8694a2e87a1a2c8a61f8761784e1284423 0x14b1338a2171668b01ecadab8b851adad99⟩,
  ⟨41,4,[0xa0000a0000000000, 0xa0000a00a0000a00, 0xc0000c00c0000c00, 0xf0000000f0000000, 0xf0000f0000000000],lhints 4 0x2aaa9aa1a2e87a1a5a8b21d8444e09423 0x229389a81143796003478a755b3b3a8a8c7⟩,
  ⟨41,4,[0xa0000a00a0000a00, 0xc0000c00c0000c00, 0xf0000000f0000000, 0xf0000f0000000000, 0xf0000f00a0000a00],lhints 4 0xaaaa1a6a94a2e87a1a5a8b21d85e1384425 0x95411413b18cc822580041775d61414a8c8⟩,
  ⟨41,4,[0xc0000000c00, 0xa0000a00a0000a00, 0xc0000c00c0000c00, 0xf0000000f0000000, 0xf0000f0000000000],lhints 4 0x2aaa869aa2e87a1a2c87e1d8444e09423 0x229369681835567003a78c7696943b8c7c7⟩,
  ⟨41,4,[0x3000000030000000, 0xa0000a00a0000a00, 0xc0000c00c0000c00, 0xf0000000f0000000, 0xf0000f0000000000],lhints 4 0x2aaa8694a2e87a1a2c8aa2387e1e8761384425 0x36b3228b03d558943739cd9b8b811aa9e9e⟩,
  ⟨41,4,[0xa0000a00a0000a00, 0xc0000c0000000000, 0xc0000c00c0000c00, 0xf0000000f0000000, 0xf0000f0000000000],lhints 4 0x2b0aaaa1a2e87a1a5b8b21d8444e09423 0x2293896114355c3c3a879b7003478b77bb7⟩,
  ⟨41,4,[0xa0000a00a0000a00, 0xc0000c00c0000c00, 0xf0000000f0000000, 0xf0000f0000000000, 0xf0000f00c0000c00],lhints 4 0xaaaa1a6a94a2e87a1a5b8b22387e1d84423 0x95122114b1885c621217dd7335700127ac7⟩,
  ⟨41,4,[0xf0000000, 0xa0000a00a0000a00, 0xc0000c00c0000c00, 0xf0000000f0000000, 0xf0000f0000000000],lhints 4 0x2aaa869ca6e9aa2e87a1a2c87e138444e 0x842246a6683345955856b574116b6b5c5c⟩,
  ⟨41,4,[0xf0000000000, 0xa0000a00a0000a00, 0xc0000c00c0000c00, 0xf0000000f0000000, 0xf0000f0000000000],lhints 4 0xaaaa1a6a8ba1e868b21d8444e09423 0x28378a7114368b6003467a65593a7a7b6b6⟩
]
def nodesBlock27 : Array Node := #[
  ⟨43,6,[0xaa00aa0000000000, 0xcc00cc0000000000, 0xf000f00000000000, 0xff00000000000000],lhints 5 0xb16c3b0abaad6b4abaacaaaa4a8aa195a5393a4b7cdef79de2765cc1384a1203b0e436 0x647056ee455ef1864651642a476a4456ab5642506c28275e224de947423064e437e6a34665264eb36ce217da813da316ce9375a007cee034e1075af6⟩,
  ⟨43,5,[0xaa00aa0000000000, 0xcc00cc0000000000, 0xee00ee0000000000, 0xf000f00000000000, 0xff00000000000000],lhints 5 0x2c5aeab5ad2aeab2aaa92a2a865694e4e92dd8759d574dd2745cf7344e 0xea82cf05ab573dc97bd15a9def4d6aa738d6b15ce55acd9356f792526bdad8b56e70e316b9ac5d1a96c1ef64a427be12841ce6462173a1182d738260b6b60c82d6b⟩,
  ⟨43,4,[0xcc00cc0000000000, 0xee00ee0000000000, 0xf000f00000000000, 0xfa00fa0000000000, 0xff00000000000000],lhints 4 0xaeab5ad2aeab2aaa92a2a8653939ce 0x585645b4745b5969624941358363323403a3⟩,
  ⟨43,3,[0xee00ee0000000000, 0xfa00fa0000000000, 0xfc00fc0000000000, 0xff00000000000000],lhints 3 0xae6b3abaaaa92a194e4e 0x4ea75c5117de5909a1⟩,
  ⟨43,4,[0xcc00cc0000000000, 0xee00ee0000000000, 0xf000f00000000000, 0xff00000000000000, 0xff00aa0000000000],lhints 4 0x2c5b0ab5ad2aeab2aaa92a2a865392dd0 0x85744645c469615b514c4b633235033473a3⟩,
  ⟨43,3,[0xee00ee0000000000, 0xf000f00000000000, 0xff00aa0000000000, 0xff00cc0000000000],lhints 4 0xb06bead6b4ab2aaa8aa194e4b 0x242132525334272046403938⟩,
  ⟨43,4,[0xaa00aa0000000000, 0xee00ee0000000000, 0xf000f00000000000, 0xfc00fc0000000000, 0xff00000000000000],lhints 4 0x2baad6b4abaacaaeaaa92a2a8656939ce 0x359385c5435c5b3b318b81595636326706a6⟩,
  ⟨43,4,[0xaa00aa0000000000, 0xee00ee0000000000, 0xf000f00000000000, 0xff00000000000000, 0xff00cc0000000000],lhints 4 0xb16c3ad6b4abaadab2aaa92a2a865692dd0 0x53437349d43b319c914d4c363268064746a6⟩,
  ⟨43,4,[0xaa00aa0000000000, 0xcc00cc0000000000, 0xf000f00000000000, 0xfe00fe0000000000, 0xff00000000000000],lhints 4 0x2c5b0ec2aeab4abaacaaaa4a8aa192dd4 0x40413493c32472b223624745a536352528⟩,
  ⟨43,3,[0xfe0000000000, 0xaa00aa0000000000, 0xcc00cc0000000000, 0xf000f00000000000],lhints 3 0xab2aaa92a2a844e12848 0x2b90a00588a2659c28⟩,
  ⟨43,4,[0xe000e0000000000, 0xaa00aa0000000000, 0xcc00cc0000000000, 0xf000f00000000000, 0xff00000000000000],lhints 4 0x2baad6b4abaaaa92a2a844e0ec39 0x22a5357311935756008636385a5a4439396868⟩,
  ⟨43,4,[0xaa00aa0000000000, 0xcc00cc0000000000, 0xf000f00000000000, 0xff00000000000000, 0xff00ee0000000000],lhints 4 0x2c5b0abaad6b4abaacaaaa4a8aa1939d7 0xa4033134c392247223628547453635252b⟩,
  ⟨43,3,[0xf000e0000000000, 0xaa00aa0000000000, 0xcc00cc0000000000, 0xff00000000000000],lhints 3 0xabaaaa92a2a844e0ec39 0x2b90a80588aa659c20⟩,
  ⟨43,4,[0xee0000000000, 0xaa00aa0000000000, 0xcc00cc0000000000, 0xf000f00000000000, 0xff00000000000000],lhints 4 0xb16c3b0abaad6b4ab2aaa92a2a844e12848 0x22a411c3347300b64746363b554d4d393c686b⟩,
  ⟨43,5,[0xaa00aa0000000000, 0xcc00cc0000000000, 0xf000f00000000000, 0xfa00fa0000000000, 0xff00000000000000],lhints 5 0x2c3aeab5ad2aeab2aaa92a2a865694e4e92de177dde775dc769d37344a 0x97bd1291def4ca4eab94f79ab573dcc545c973640b3c16949af6d8b66adad136cbb354da39d4251ae6cdef64a437be72929509a60a73a6c9a94a9b5aca502d6ce93⟩,
  ⟨43,4,[0xcc00cc0000000000, 0xf000f00000000000, 0xfa00fa0000000000, 0xff00000000000000, 0xff00aa0000000000],lhints 4 0x2c3b0ab5ad2aeab2aaa92a2a864e92ddb 0x8566915b519442450474a33935c3c33b34a3⟩
]
def nodesBlock28 : Array Node := #[
  ⟨43,3,[0xcc00cc0000000000, 0xfa00fa0000000000, 0xff00aa0000000000, 0xff00f00000000000],lhints 4 0x2c1afeb5ad2aeab2aaa8aa193a4b 0x36313530447023828227a229⟩,
  ⟨43,4,[0xaa00aa0000000000, 0xcc00cc0000000000, 0xfa00fa0000000000, 0xfc00fc0000000000, 0xff00000000000000],lhints 4 0xad6b4aceaeab2aaa92a2a865694dce 0x4584585747418585337b7158584a4266990a⟩,
  ⟨43,4,[0x3200320000000000, 0xaa00aa0000000000, 0xcc00cc0000000000, 0xf000f00000000000, 0xff00000000000000],lhints 4 0x2baad2aeab2aaa92a2a844a0ec36 0x45a42285117458564746006958584747339696⟩,
  ⟨43,4,[0xaa00aa0000000000, 0xcc00cc0000000000, 0xfa00fa0000000000, 0xff00000000000000, 0xff00f00000000000],lhints 4 0xb16c3aeab7ad6b4ab2aaa92a2a865692ddb 0x544741bdb134933bc3c33c48428a08663938⟩,
  ⟨43,4,[0xaa00aa0000000000, 0xcc00cc0000000000, 0xf000f00000000000, 0xff00000000000000, 0xff00fa0000000000],lhints 4 0x2c3b0abaad6b4abaacaaaa4a8aa194de0 0x746334a3022124c22392554a48383b2928⟩,
  ⟨43,3,[0x3300320000000000, 0xaa00aa0000000000, 0xf000f00000000000, 0xff00000000000000],lhints 3 0xaeab4a92a2a844a0ec36 0x2b90a80606aa661c18⟩,
  ⟨43,4,[0xfa0000000000, 0xaa00aa0000000000, 0xcc00cc0000000000, 0xf000f00000000000, 0xff00000000000000],lhints 4 0xb16c3b0ab5ad2aeab2aaa92a2a844e12848 0x22d4118334a300b8494b3a3955474d3c3c669b⟩,
  ⟨43,5,[0xaa00aa0000000000, 0xcc00cc0000000000, 0xf000f00000000000, 0xff00000000000000, 0xff00aa0000000000],lhints 5 0x2c5b0ec2ad6aeab2aaa92a2a865694e4e92de6795e478ddf769d673c3b 0xc4c9e97c511729ce23a2a8b92eb3df63d9cf74cd36adad1366b9b52dabdf52d5af6b6209b8138c5ae6a530a26097be8ca2529a39cc8c46e75231a35ac9cc2d6d273⟩,
  ⟨43,4,[0xaa00aa0000000000, 0xcc00cc0000000000, 0xf000f00000000000, 0xff00aa0000000000, 0xff00cc0000000000],lhints 4 0xb0ec2afaaeab2aaa92a2a865694dd0 0x585145747447338b8174745a52664747990a⟩,
  ⟨43,4,[0x3300220000000000, 0xaa00aa0000000000, 0xcc00cc0000000000, 0xf000f00000000000, 0xff00000000000000],lhints 4 0x2c5b0ab5ad2aeab2aaa92a2a844a0ec36 0x45c42285117458564746006a585847473396b6⟩,
  ⟨43,4,[0xaa00aa0000000000, 0xcc00cc0000000000, 0xf000f00000000000, 0xff00aa0000000000, 0xff00f00000000000],lhints 4 0x2c5b0abfaeab5abaaaa92a2a8656939db 0x5751449c913583833838835b5266aa0b3838⟩,
  ⟨43,4,[0xf000a0000000000, 0xaa00aa0000000000, 0xcc00cc0000000000, 0xf000f00000000000, 0xff00000000000000],lhints 4 0xb0ec2aeab5ad2aeab2aaa92a2a844e0ec39 0x22b535d311735b5900973a39585b443a3a66c9⟩,
  ⟨43,5,[0xaa00aa0000000000, 0xcc00cc0000000000, 0xf000f00000000000, 0xfc00fc0000000000, 0xff00000000000000],lhints 5 0x2c2aeab5ad2aeab2aaa92a2a865694e4e92dee7b1eb7a5e8771d374448 0x99490f79e524bdf1ac54f79ab58bdeb5ba29752525bde594a8f7a96da25aa8c68ba2d6b83c16902cf7c250b12d0642028599682a138c6639c2309ae70a420184e93⟩,
  ⟨43,4,[0x5400540000000000, 0xaa00aa0000000000, 0xcc00cc0000000000, 0xf000f00000000000, 0xff00000000000000],lhints 4 0x2baad6aeab2aaa92a2a84480e436 0x45a43583347322581147003985857474939366⟩,
  ⟨43,4,[0xaa00aa0000000000, 0xf000f00000000000, 0xfc00fc0000000000, 0xff00000000000000, 0xff00cc0000000000],lhints 4 0x2c3b0ab5ad2aeab2aaa92a2a864e92dea 0x5533a18c81a772780744966968b6b66b6796⟩,
  ⟨43,3,[0xaa00aa0000000000, 0xfc00fc0000000000, 0xff00cc0000000000, 0xff00f00000000000],lhints 4 0x2c1b02b5ad2acaaaa4a8aa194e4b 0x44613360228056757557a559⟩
]
def nodesBlock29 : Array Node := #[
  ⟨43,4,[0xaa00aa0000000000, 0xcc00cc0000000000, 0xfc00fc0000000000, 0xff00000000000000, 0xff00f00000000000],lhints 4 0xb16c2aeab8ad6b4ab2aaa92a2a865392dea 0x554471bdb179729a093367866bc6c66c8668⟩,
  ⟨43,4,[0xaa00aa0000000000, 0xcc00cc0000000000, 0xf000f00000000000, 0xff00000000000000, 0xff00fc0000000000],lhints 4 0x2c3b0abaad6b4abaacaaaa4a8aa1959ed 0x443367a6227a79696c055157b556858558⟩,
  ⟨43,3,[0x5500540000000000, 0xcc00cc0000000000, 0xf000f00000000000, 0xff00000000000000],lhints 3 0xaeab4abaacaa8480e436 0x2b90a80606aa661c18⟩,
  ⟨43,4,[0xfc0000000000, 0xaa00aa0000000000, 0xcc00cc0000000000, 0xf000f00000000000, 0xff00000000000000],lhints 4 0xb16c3b0ab5ad2aeab2aaa92a2a844e12848 0x22d511c57a7c00566796966985447d33ac6b6b⟩,
  ⟨43,5,[0xaa00aa0000000000, 0xcc00cc0000000000, 0xf000f00000000000, 0xff00000000000000, 0xff00cc0000000000],lhints 5 0x2c5b0ec2ad2aeab2aaa92a2a865694e4e92df27c5f07b1e978dd674839 0xb4be497b90e8aa312c5ca7392eb4a563d9d27252daa5a994aabaa529ac62b738918d5ce99a706420284d938261494a83a4250838138826e742309ae70ac20184eb3⟩,
  ⟨43,4,[0x5500440000000000, 0xaa00aa0000000000, 0xcc00cc0000000000, 0xf000f00000000000, 0xff00000000000000],lhints 4 0x2c5b0eb5ad2aeab2aaa92a2a84480e436 0x45c43583347322581147003985857474a3b366⟩,
  ⟨43,4,[0xaa00aa0000000000, 0xcc00cc0000000000, 0xf000f00000000000, 0xff00cc0000000000, 0xff00f00000000000],lhints 4 0x2c5b0ec0aeab4abaaaa92a2a8653939ea 0x5572449c917b7233aa0b6786866868868668⟩,
  ⟨43,4,[0xf000c0000000000, 0xaa00aa0000000000, 0xcc00cc0000000000, 0xf000f00000000000, 0xff00000000000000],lhints 4 0xb0ec2aeab5ad2aeab2aaa92a2a844e0ec39 0x22b48b8a11a468c600469669558b7433da6969⟩,
  ⟨43,5,[0xaa00aa0000000000, 0xcc00cc0000000000, 0xf000f00000000000, 0xff00000000000000, 0xff00f00000000000],lhints 5 0x2c5b0ec2aeab5ad2aaa92a2a865694e4e92df57d1f17b1eb795df77836 0xa4be697a52eb25c99cecab25296a1b25ca459356d6a5b59cea6ab66d6a9b2b4a44936cd81e11646228c190826149ce83a427082a11b46218c2d08b4109020d6c651⟩,
  ⟨43,4,[0x5500500000000000, 0xaa00aa0000000000, 0xcc00cc0000000000, 0xf000f00000000000, 0xff00000000000000],lhints 4 0xb16c3aeab5ad2aeab2aaa92a2a84480e436 0x45b435c334a322561146003a85b574d4a3a396⟩,
  ⟨43,4,[0x3300300000000000, 0xaa00aa0000000000, 0xcc00cc0000000000, 0xf000f00000000000, 0xff00000000000000],lhints 4 0xb16c2aeab5ad2aeab2aaa92a2a844a0ec36 0x78b72283117368c66796003955b844d7a39696⟩,
  ⟨8,3,[0x800080002000200, 0xc00000003000000, 0xc000c0000000000],lhints 4 0x2aeaaa7e9da138384a0d81c 0x362842866343541761744565730580533787⟩,
  ⟨3,3,[0x82008200, 0xc000c000, 0xc3000000],lhints 4 0x27a9da428f60e8342507011 0x362842866343541761744565730580533787⟩,
  ⟨9,3,[0xa000a0000000000, 0xc000c0000000000, 0xf00000000000000],lhints 4 0x2c3b0aaeaaaa4a844a12036 0x362842866343541761744565730580533787⟩,
  ⟨6,3,[0xaa0000000000, 0xcc0000000000, 0xf00000000000],lhints 4 0x2b5ad2acaaaa2a843b0e436 0x362842866343541761744565730580533787⟩,
  ⟨4,3,[0xa00a0000000, 0xc00c0000000, 0xf0000000000],lhints 3 0xaaaa9a86a0a4e9209423 0x38d92e661107dbc43014727da08⟩
]
def nodesBlock30 : Array Node := #[
  ⟨7,3,[0x800080004000400, 0xa00000005000000, 0xa000a0000000000],lhints 4 0x2a4a867d9de1f86c480d81e 0x362842866343541761744565730580533787⟩,
  ⟨12,3,[0x1000100010001000, 0x1800000018000000, 0x1800180000000000],lhints 3 0xaeab3a2e858de330d820 0x14727da08966275709df4027580⟩,
  ⟨11,3,[0x1000800010008000, 0x1100000011000000, 0x1100880000000000],lhints 3 0xb16bea2e829f2750d811 0x96627570914727da08107dbc430⟩,
  ⟨10,3,[0x1000100080008000, 0x1100000088000000, 0x1100110000000000],lhints 3 0xb16bdaeab2a468f08011 0x38d92e661107dbc43014727da08⟩,
  ⟨14,3,[0x2200220000000000, 0x3000300000000000, 0x3300000000000000],lhints 4 0x2c5b0abaad2a4a884e12039 0x362842866343541761744565730580533787⟩,
  ⟨5,3,[0x880000008800, 0xc0000000c000, 0xcc0000000000],lhints 4 0x2acaaa448f62c8943b0d811 0x362842866343541761744565730580533787⟩,
  ⟨13,3,[0x2000080020000800, 0x3000000030000000, 0x30000c0000000000],lhints 4 0x2afaaa8ba1a2c8a44e0d823 0x362842866343541761744565730580533787⟩,
  ⟨16,3,[0x4000400040004000, 0x5000000050000000, 0x5000500000000000],lhints 4 0x2baad68ba1e449084e0ec25 0x362842866343541761744565730580533787⟩,
  ⟨17,3,[0x4400440000000000, 0x5000500000000000, 0x5500000000000000],lhints 4 0x2c5b0ebaad6aeab04e1283b 0x362842866343541761744565730580533787⟩,
  ⟨15,3,[0x4000080040000800, 0x5000000050000000, 0x50000a0000000000],lhints 4 0x2a5a868ba1e2c8a84e0d825 0x362842866343541761744565730580533787⟩,
  ⟨19,3,[0x8000800008000800, 0x9000000009000000, 0x9000900000000000],lhints 4 0x2baada809e22d8a04e0f420 0x362842866343541761744565730580533787⟩,
  ⟨20,3,[0x8800000000008800, 0x9000000000009000, 0x9900000000000000],lhints 4 0x2c5b123b8c22e8944e13011 0x362842866343541761744565730580533787⟩,
  ⟨18,3,[0x8000080080000800, 0x9000000090000000, 0x9000090000000000],lhints 4 0x29aa528ba222c8ac4e0d827 0x362842866343541761744565730580533787⟩,
  ⟨21,3,[0x8000080040000400, 0xa000000050000000, 0xa0000a0000000000],lhints 4 0x2a6a868ca1e1f874500d825 0x362842866343541761744565730580533787⟩,
  ⟨22,3,[0x8000080020000200, 0xc000000030000000, 0xc0000c0000000000],lhints 4 0x2b0aaa8da1a13844520d823 0x362842866343541761744565730580533787⟩,
  ⟨0,2,[0x10002000, 0x14000000],lhints 2 0xa12810780e 0x235e84⟩
]
def nodesGet (i : Nat) : Option Node :=
  if i < 240 then
    if i < 112 then
      if i < 48 then
        if i < 16 then
          nodesBlock0[(i - 0)]?
        else
          if i < 32 then
            nodesBlock1[(i - 16)]?
          else
            nodesBlock2[(i - 32)]?
      else
        if i < 80 then
          if i < 64 then
            nodesBlock3[(i - 48)]?
          else
            nodesBlock4[(i - 64)]?
        else
          if i < 96 then
            nodesBlock5[(i - 80)]?
          else
            nodesBlock6[(i - 96)]?
    else
      if i < 176 then
        if i < 144 then
          if i < 128 then
            nodesBlock7[(i - 112)]?
          else
            nodesBlock8[(i - 128)]?
        else
          if i < 160 then
            nodesBlock9[(i - 144)]?
          else
            nodesBlock10[(i - 160)]?
      else
        if i < 208 then
          if i < 192 then
            nodesBlock11[(i - 176)]?
          else
            nodesBlock12[(i - 192)]?
        else
          if i < 224 then
            nodesBlock13[(i - 208)]?
          else
            nodesBlock14[(i - 224)]?
  else
    if i < 368 then
      if i < 304 then
        if i < 272 then
          if i < 256 then
            nodesBlock15[(i - 240)]?
          else
            nodesBlock16[(i - 256)]?
        else
          if i < 288 then
            nodesBlock17[(i - 272)]?
          else
            nodesBlock18[(i - 288)]?
      else
        if i < 336 then
          if i < 320 then
            nodesBlock19[(i - 304)]?
          else
            nodesBlock20[(i - 320)]?
        else
          if i < 352 then
            nodesBlock21[(i - 336)]?
          else
            nodesBlock22[(i - 352)]?
    else
      if i < 432 then
        if i < 400 then
          if i < 384 then
            nodesBlock23[(i - 368)]?
          else
            nodesBlock24[(i - 384)]?
        else
          if i < 416 then
            nodesBlock25[(i - 400)]?
          else
            nodesBlock26[(i - 416)]?
      else
        if i < 464 then
          if i < 448 then
            nodesBlock27[(i - 432)]?
          else
            nodesBlock28[(i - 448)]?
        else
          if i < 480 then
            nodesBlock29[(i - 464)]?
          else
            nodesBlock30[(i - 480)]?
def fastViews : Fast.Table View := ⟨46,viewsGet⟩
def fastNodes : Fast.Table Node := ⟨496,nodesGet⟩
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkRoots_0 : Fast.passBlock (Fast.checkRootAt fastViews fastNodes) 0 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkRoots_10 : Fast.passBlock (Fast.checkRootAt fastViews fastNodes) 10 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkRoots_20 : Fast.passBlock (Fast.checkRootAt fastViews fastNodes) 20 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkRoots_30 : Fast.passBlock (Fast.checkRootAt fastViews fastNodes) 30 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkRoots_40 : Fast.passBlock (Fast.checkRootAt fastViews fastNodes) 40 6 = true := by decide +kernel
theorem combineRoots_0_0 : Fast.passBlock (Fast.checkRootAt fastViews fastNodes) 0 20 = true := @Fast.merge_blocks (Fast.checkRootAt fastViews fastNodes) 0 10 10 checkRoots_0 checkRoots_10
theorem combineRoots_0_20 : Fast.passBlock (Fast.checkRootAt fastViews fastNodes) 20 20 = true := @Fast.merge_blocks (Fast.checkRootAt fastViews fastNodes) 20 10 10 checkRoots_20 checkRoots_30
theorem combineRoots_1_0 : Fast.passBlock (Fast.checkRootAt fastViews fastNodes) 0 40 = true := @Fast.merge_blocks (Fast.checkRootAt fastViews fastNodes) 0 20 20 combineRoots_0_0 combineRoots_0_20
theorem combineRoots_2_0 : Fast.passBlock (Fast.checkRootAt fastViews fastNodes) 0 46 = true := @Fast.merge_blocks (Fast.checkRootAt fastViews fastNodes) 0 40 6 combineRoots_1_0 checkRoots_40
theorem certifiedRoots : Fast.passBlock (Fast.checkRootAt fastViews fastNodes) 0 46 = true := combineRoots_2_0
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
theorem checkNodes_130 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 130 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_140 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 140 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_150 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 150 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_160 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 160 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_170 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 170 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_180 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 180 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_190 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 190 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_200 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 200 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_210 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 210 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_220 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 220 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_230 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 230 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_240 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 240 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_250 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 250 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_260 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 260 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_270 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 270 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_280 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 280 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_290 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 290 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_300 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 300 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_310 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 310 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_320 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 320 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_330 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 330 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_340 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 340 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_350 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 350 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_360 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 360 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_370 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 370 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_380 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 380 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_390 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 390 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_400 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 400 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_410 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 410 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_420 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 420 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_430 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 430 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_440 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 440 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_450 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 450 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_460 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 460 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_470 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 470 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_480 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 480 10 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checkNodes_490 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 490 6 = true := by decide +kernel
theorem combineNodes_0_0 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 0 20 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 0 10 10 checkNodes_0 checkNodes_10
theorem combineNodes_0_20 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 20 20 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 20 10 10 checkNodes_20 checkNodes_30
theorem combineNodes_0_40 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 40 20 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 40 10 10 checkNodes_40 checkNodes_50
theorem combineNodes_0_60 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 60 20 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 60 10 10 checkNodes_60 checkNodes_70
theorem combineNodes_0_80 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 80 20 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 80 10 10 checkNodes_80 checkNodes_90
theorem combineNodes_0_100 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 100 20 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 100 10 10 checkNodes_100 checkNodes_110
theorem combineNodes_0_120 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 120 20 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 120 10 10 checkNodes_120 checkNodes_130
theorem combineNodes_0_140 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 140 20 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 140 10 10 checkNodes_140 checkNodes_150
theorem combineNodes_0_160 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 160 20 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 160 10 10 checkNodes_160 checkNodes_170
theorem combineNodes_0_180 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 180 20 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 180 10 10 checkNodes_180 checkNodes_190
theorem combineNodes_0_200 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 200 20 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 200 10 10 checkNodes_200 checkNodes_210
theorem combineNodes_0_220 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 220 20 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 220 10 10 checkNodes_220 checkNodes_230
theorem combineNodes_0_240 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 240 20 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 240 10 10 checkNodes_240 checkNodes_250
theorem combineNodes_0_260 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 260 20 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 260 10 10 checkNodes_260 checkNodes_270
theorem combineNodes_0_280 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 280 20 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 280 10 10 checkNodes_280 checkNodes_290
theorem combineNodes_0_300 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 300 20 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 300 10 10 checkNodes_300 checkNodes_310
theorem combineNodes_0_320 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 320 20 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 320 10 10 checkNodes_320 checkNodes_330
theorem combineNodes_0_340 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 340 20 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 340 10 10 checkNodes_340 checkNodes_350
theorem combineNodes_0_360 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 360 20 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 360 10 10 checkNodes_360 checkNodes_370
theorem combineNodes_0_380 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 380 20 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 380 10 10 checkNodes_380 checkNodes_390
theorem combineNodes_0_400 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 400 20 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 400 10 10 checkNodes_400 checkNodes_410
theorem combineNodes_0_420 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 420 20 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 420 10 10 checkNodes_420 checkNodes_430
theorem combineNodes_0_440 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 440 20 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 440 10 10 checkNodes_440 checkNodes_450
theorem combineNodes_0_460 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 460 20 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 460 10 10 checkNodes_460 checkNodes_470
theorem combineNodes_0_480 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 480 16 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 480 10 6 checkNodes_480 checkNodes_490
theorem combineNodes_1_0 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 0 40 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 0 20 20 combineNodes_0_0 combineNodes_0_20
theorem combineNodes_1_40 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 40 40 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 40 20 20 combineNodes_0_40 combineNodes_0_60
theorem combineNodes_1_80 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 80 40 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 80 20 20 combineNodes_0_80 combineNodes_0_100
theorem combineNodes_1_120 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 120 40 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 120 20 20 combineNodes_0_120 combineNodes_0_140
theorem combineNodes_1_160 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 160 40 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 160 20 20 combineNodes_0_160 combineNodes_0_180
theorem combineNodes_1_200 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 200 40 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 200 20 20 combineNodes_0_200 combineNodes_0_220
theorem combineNodes_1_240 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 240 40 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 240 20 20 combineNodes_0_240 combineNodes_0_260
theorem combineNodes_1_280 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 280 40 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 280 20 20 combineNodes_0_280 combineNodes_0_300
theorem combineNodes_1_320 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 320 40 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 320 20 20 combineNodes_0_320 combineNodes_0_340
theorem combineNodes_1_360 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 360 40 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 360 20 20 combineNodes_0_360 combineNodes_0_380
theorem combineNodes_1_400 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 400 40 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 400 20 20 combineNodes_0_400 combineNodes_0_420
theorem combineNodes_1_440 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 440 40 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 440 20 20 combineNodes_0_440 combineNodes_0_460
theorem combineNodes_2_0 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 0 80 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 0 40 40 combineNodes_1_0 combineNodes_1_40
theorem combineNodes_2_80 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 80 80 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 80 40 40 combineNodes_1_80 combineNodes_1_120
theorem combineNodes_2_160 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 160 80 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 160 40 40 combineNodes_1_160 combineNodes_1_200
theorem combineNodes_2_240 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 240 80 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 240 40 40 combineNodes_1_240 combineNodes_1_280
theorem combineNodes_2_320 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 320 80 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 320 40 40 combineNodes_1_320 combineNodes_1_360
theorem combineNodes_2_400 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 400 80 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 400 40 40 combineNodes_1_400 combineNodes_1_440
theorem combineNodes_3_0 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 0 160 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 0 80 80 combineNodes_2_0 combineNodes_2_80
theorem combineNodes_3_160 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 160 160 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 160 80 80 combineNodes_2_160 combineNodes_2_240
theorem combineNodes_3_320 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 320 160 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 320 80 80 combineNodes_2_320 combineNodes_2_400
theorem combineNodes_4_0 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 0 320 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 0 160 160 combineNodes_3_0 combineNodes_3_160
theorem combineNodes_4_320 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 320 176 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 320 160 16 combineNodes_3_320 combineNodes_0_480
theorem combineNodes_5_0 : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 0 496 = true := @Fast.merge_blocks (Fast.checkNodeAt fastViews fastNodes) 0 320 176 combineNodes_4_0 combineNodes_4_320
theorem certifiedNodes : Fast.passBlock (Fast.checkNodeAt fastViews fastNodes) 0 496 = true := combineNodes_5_0
end SignedProjection

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
def witness : Circuit := ⟨[⟨.and,[3,4]⟩, ⟨.and,[2,0]⟩, ⟨.and,[6,1]⟩, ⟨.and,[5,1]⟩, ⟨.or,[6,9]⟩, ⟨.and,[2,5]⟩, ⟨.or,[0,11]⟩, ⟨.and,[10,12]⟩, ⟨.or,[8,13]⟩, ⟨.or,[7,14]⟩],15⟩

theorem witnessMono : Monotone2 witness := by simp [Monotone2, witness]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem witnessEval : ∀ x, witness.eval (List.ofFn x) = CoreSigned.F x := by decide +kernel

theorem hasNotLonger (gs : List Gate) (hm : ∃ g ∈ gs, g.op = .not) :
    Direct64.binaryCost gs < gs.length := by
  induction gs with
  | nil => simp at hm
  | cons a rest ih =>
    rcases hm with ⟨g,hg,hnot⟩
    by_cases h : a.op = .not
    · have hn : Direct64.isBinary a = false := by simp [Direct64.isBinary,h]
      simp only [Direct64.binaryCost, List.filter_cons, hn, Bool.false_eq_true, if_false, List.length_cons]
      exact Nat.lt_succ_of_le (List.length_filter_le _ _)
    · have ne : g ≠ a := by rintro rfl; exact h hnot
      have lt := ih ⟨g,(List.mem_cons.mp hg).resolve_left ne,hnot⟩
      have hb : Direct64.isBinary a = true := by cases a with | mk op ins => cases op <;> simp_all [Direct64.isBinary]
      simpa [Direct64.binaryCost,hb] using Nat.succ_lt_succ lt

theorem replacement (s : ℕ) (h : HasCircuitSize 6 CoreSigned.F s) :
    ∃ C, Monotone2 C ∧ C.size ≤ s ∧ ∀ x, C.eval (List.ofFn x) = CoreSigned.F x := by
  obtain ⟨C,legal,hs,ev⟩ := h
  by_cases hn : ∃ g ∈ C.gates, g.op = .not
  · have lo := Direct64.low (SevenGlue.from_blocks SignedProjection.fastViews SignedProjection.fastNodes
      SignedProjection.certifiedRoots SignedProjection.certifiedNodes 45 (by decide +kernel)) C.gates C.output legal ev
    have strict := hasNotLonger C.gates hn
    have nine : 10 ≤ s := by change C.gates.length ≤ s at hs; omega
    exact ⟨witness,witnessMono,nine,witnessEval⟩
  · refine ⟨C,?_,hs,ev⟩
    intro g hg
    refine ⟨?_,(legal g hg).2⟩
    rcases (legal g hg).1 with h|h|h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hn ⟨g,hg,h⟩).elim

end PEqualNP.Outside.L_meta_12879
theorem PEqualNP.Outside.L_meta_12879 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676840 * 2 ^ 32 + 4003504288) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676840 * 2 ^ 32 + 4003504288) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := PEqualNP.Outside.L_meta_12879.replacement
