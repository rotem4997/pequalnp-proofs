import PEqualNP.Defs

-- Fixing the sixth input at one saves a binary gate. The five-input
-- restriction needs nine binary gates with free complements. A circuit
-- containing a negation therefore costs at least eleven gates, and an
-- explicit eleven-gate monotone circuit realizes the full table.

namespace PEqualNP.Outside.L_meta_12072

-- The build and live relations are those used in the upstream signed-wire bounds.
-- The original relations and their compression proof appear in L_meta_9136.
def build {α : Type*} [DecidableEq α] (ops : α → α → Finset α) (goal : α) :
    ℕ → Finset α → Prop
  | 0, s => goal ∈ s
  | k+1, s => build ops goal k s ∨ ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z s)

def live {α : Type*} [DecidableEq α] (ops : α → α → Finset α) (goal : α) :
    ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k+1, s => live ops goal k s ∨ ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧
      ∃ z ∈ ops a b, z ∉ s ∧ ∃ rest, s = insert a (insert b rest) ∧
        live ops goal k (insert z rest)

theorem build_subset {α : Type*} [DecidableEq α] {ops : α → α → Finset α} {g : α}
    {k : ℕ} {s t : Finset α} (h : build ops g k s) (sub : s ⊆ t) : build ops g k t := by
  induction k generalizing s t with
  | zero => exact sub h
  | succ k ih =>
    rcases h with h | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · exact Or.inl (ih h sub)
    · exact Or.inr ⟨a, sub ha, b, sub hb, hab, z, hz, ih tail (Finset.insert_subset_insert _ sub)⟩

def zeroCount {α β : Type*} [DecidableEq α] [DecidableEq β] (p : α → β) (zero : β)
    (s : Finset α) := (s.filter fun a => p a = zero).card

def project {α β : Type*} [DecidableEq α] [DecidableEq β] (p : α → β) (zero : β)
    (s : Finset α) := (s.image p).erase zero

theorem zero_insert {α β : Type*} [DecidableEq α] [DecidableEq β] (p : α → β) (zero : β)
    (a : α) (s : Finset α) : zeroCount p zero (insert a s) ≤
    zeroCount p zero s + (if p a = zero then 1 else 0) := by
  by_cases h : p a = zero
  · simp only [zeroCount, Finset.filter_insert, h, if_true]
    exact Finset.card_insert_le _ _
  · simp [zeroCount, Finset.filter_insert, h]

theorem zero_insert_new {α β : Type*} [DecidableEq α] [DecidableEq β] (p : α → β) (zero : β)
    (a : α) (s : Finset α) (hn : a ∉ s) : zeroCount p zero (insert a s) =
    zeroCount p zero s + (if p a = zero then 1 else 0) := by
  by_cases h : p a = zero
  · have h' : a ∉ s.filter (fun u => p u = zero) := fun m => hn (Finset.mem_filter.mp m).1
    simp [zeroCount, Finset.filter_insert, h, Finset.card_insert_of_notMem h']
  · simp [zeroCount, Finset.filter_insert, h]

theorem project_subset {α β : Type*} [DecidableEq α] [DecidableEq β] (p : α → β) (zero : β)
    {s t : Finset α} (h : s ⊆ t) : project p zero s ⊆ project p zero t := by
  exact Finset.erase_subset_erase _ (Finset.image_mono p h)

-- A binary gate collapses when it reads a constant or two copies of one wire.
-- A surviving gate is a legal operation on the two projected inputs.
theorem project_live {α β : Type*} [DecidableEq α] [DecidableEq β]
    (ops : α → α → Finset α) (ops' : β → β → Finset β) (p : α → β) (zero : β)
    (collapse : ∀ a b z, z ∈ ops a b → (p a = zero ∨ p b = zero ∨ p a = p b) →
      p z = zero ∨ p z = p a ∨ p z = p b)
    (preserve : ∀ a b z, z ∈ ops a b → p z ∈ ops' (p a) (p b))
    {g : α} (ng : p g ≠ zero) {k : ℕ} {s : Finset α} (h : live ops g k s) :
    ∃ l, l + zeroCount p zero s ≤ k ∧ build ops' (p g) l (project p zero s) := by
  induction k generalizing s with
  | zero =>
    change s = {g} at h
    subst s
    refine ⟨0, by simp [zeroCount, ng], ?_⟩
    change p g ∈ (Finset.image p {g}).erase zero
    simp [ng]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, _, z, hop, hz, r, hs, tail⟩
    · obtain ⟨l, bound, run⟩ := ih skip
      exact ⟨l, by omega, run⟩
    · obtain ⟨l, bound, run⟩ := ih tail
      have hr : r ⊆ s := by rw [hs]; exact (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
      have hzr : z ∉ r := fun hmem => hz (hr hmem)
      rw [zero_insert_new p zero z r hzr] at bound
      have cntA := zero_insert p zero a (insert b r)
      have cntB := zero_insert p zero b r
      have pbase : project p zero r ⊆ project p zero s := project_subset p zero hr
      have available {w : α} (hw : w ∈ s) (nw : p w ≠ zero) : p w ∈ project p zero s :=
        Finset.mem_erase.mpr ⟨nw, Finset.mem_image_of_mem p hw⟩
      have skipz (simple : p z = zero ∨ p z = p a ∨ p z = p b) :
          build ops' (p g) l (project p zero s) := by
        apply build_subset run
        intro v hv
        obtain ⟨nz, mem⟩ := Finset.mem_erase.mp hv
        rw [Finset.image_insert] at mem
        rcases Finset.mem_insert.mp mem with rfl | old
        · rcases simple with h0 | hA | hB
          · exact (nz h0).elim
          · rw [hA] at nz ⊢
            exact available ha nz
          · rw [hB] at nz ⊢
            exact available hb nz
        · exact pbase (Finset.mem_erase.mpr ⟨nz, old⟩)
      by_cases trivial : p a = zero ∨ p b = zero ∨ p a = p b
      · have simple := collapse a b z hop trivial
        have both (a0 : p a = zero) (b0 : p b = zero) : p z = zero := by
          rcases simple with e | e | e <;> simp_all
        refine ⟨l, ?_, skipz simple⟩
        rw [hs]
        by_cases a0 : p a = zero <;> by_cases b0 : p b = zero <;> by_cases z0 : p z = zero <;>
          first | exact False.elim (z0 (both a0 b0)) | (simp [a0, b0, z0] at cntA cntB bound; omega)
      · have na : p a ≠ zero := fun e => trivial (Or.inl e)
        have nb : p b ≠ zero := fun e => trivial (Or.inr (Or.inl e))
        have ne : p a ≠ p b := fun e => trivial (Or.inr (Or.inr e))
        refine ⟨l+1, ?_, Or.inr ⟨p a, available ha na, p b, available hb nb, ne,
          p z, preserve a b z hop, build_subset run ?_⟩⟩
        · rw [hs]
          simp only [if_neg na, if_neg nb, Nat.add_zero] at cntA cntB
          omega
        · intro v hv
          obtain ⟨nz, m⟩ := Finset.mem_erase.mp hv
          rw [Finset.image_insert] at m
          rcases Finset.mem_insert.mp m with rfl | old
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (pbase (Finset.mem_erase.mpr ⟨nz, old⟩))

end PEqualNP.Outside.L_meta_12072

namespace PEqualNP.Outside.L_meta_12072

-- Generic live-wire lemmas from L_meta_9136 under Apache-2.0.
variable {α : Type*} [DecidableEq α]

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

abbrev W := BitVec 64

def words (a b : W) : List W := [a &&& b, a ||| b, a &&& ~~~b, b &&& ~~~a]
def raw (a b : W) : Finset W := (words a b).toFinset
def clean (a b : W) : Finset W := (raw a b).erase 0

theorem raw_simple {a b z : W} (h : z ∈ raw a b) (e : a = 0 ∨ b = 0 ∨ a = b) :
    z = 0 ∨ z = a ∨ z = b := by
  simp only [raw, words, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases e with rfl | rfl | rfl <;> rcases h with rfl | rfl | rfl | rfl <;> simp
  · exact Or.inr (BitVec.and_allOnes (x := b))
  · exact Or.inr (Or.inl (BitVec.and_allOnes (x := a)))

theorem raw_mask {a b z : W} (h : z ∈ raw a b) (m : W) :
    z &&& m ∈ raw (a &&& m) (b &&& m) := by
  simp only [raw, words, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  rcases h with rfl | rfl | rfl | rfl
  · left; ext i; simp; cases a[i] <;> cases b[i] <;> cases m[i] <;> rfl
  · right; left; ext i; simp; cases a[i] <;> cases b[i] <;> cases m[i] <;> rfl
  · right; right; left; ext i; simp; cases a[i] <;> cases b[i] <;> cases m[i] <;> rfl
  · right; right; right; ext i; simp; cases a[i] <;> cases b[i] <;> cases m[i] <;> rfl

theorem raw_to_clean {g : W} (ng : g ≠ 0) {k : ℕ} {s : Finset W}
    (h : build raw g k s) : build clean g k (s.erase 0) := by
  induction k generalizing s with
  | zero => exact Finset.mem_erase.mpr ⟨ng, h⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, ne, z, hz, tail⟩
    · exact Or.inl (ih skip)
    · have run := ih tail
      by_cases bad : a = 0 ∨ b = 0 ∨ z = 0
      · have simpz : z = 0 ∨ z ∈ s := by
          rcases bad with h0 | h0 | h0
          · rcases raw_simple hz (.inl h0) with h | rfl | rfl
            · exact .inl h
            · exact .inr ha
            · exact .inr hb
          · rcases raw_simple hz (.inr (.inl h0)) with h | rfl | rfl
            · exact .inl h
            · exact .inr ha
            · exact .inr hb
          · exact .inl h0
        apply Or.inl
        apply build_subset run
        intro w hw
        obtain ⟨nz, mem⟩ := Finset.mem_erase.mp hw
        refine Finset.mem_erase.mpr ⟨nz, ?_⟩
        rcases Finset.mem_insert.mp mem with rfl | m
        · exact simpz.resolve_left nz
        · exact m
      · have na : a ≠ 0 := fun h => bad (.inl h)
        have nb : b ≠ 0 := fun h => bad (.inr (.inl h))
        have nz : z ≠ 0 := fun h => bad (.inr (.inr h))
        refine Or.inr ⟨a, Finset.mem_erase.mpr ⟨na,ha⟩, b, Finset.mem_erase.mpr ⟨nb,hb⟩, ne,
          z, Finset.mem_erase.mpr ⟨nz,hz⟩, build_subset run ?_⟩
        intro w hw
        obtain ⟨n0, mem⟩ := Finset.mem_erase.mp hw
        rcases Finset.mem_insert.mp mem with rfl | ms
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨n0,ms⟩)

def maskBank (m : W) (s : Finset W) := project (fun x : W => x &&& m) 0 s
def Hard (y m : W) (req : ℕ) (s : Finset W) : Prop :=
  ∀ t, build raw (y &&& m) t (maskBank m s) → req ≤ t

theorem fits {y m : W} {req k : ℕ} {s : Finset W} (hy : y &&& m ≠ 0)
    (hard : Hard y m req s) (h : live clean y k s) :
    req + zeroCount (fun x : W => x &&& m) 0 s ≤ k := by
  obtain ⟨l, pay, run⟩ := project_live clean raw (fun x : W => x &&& m) 0
    (fun a b z hop => raw_simple (raw_mask (Finset.mem_erase.mp hop).2 m))
    (fun a b z hop => raw_mask (Finset.mem_erase.mp hop).2 m) hy h
  have := hard l run
  omega

def freeAt (m z : W) (ws : List W) : Bool :=
  ((z &&& m) == 0) || ws.any fun w => (w &&& m) == (z &&& m)

theorem nextHard {y m a b z : W} {req : ℕ} {ws kept : List W}
    (old : Hard y m req ws.toFinset) (ha : a ∈ ws) (hb : b ∈ ws) (hop : z ∈ raw a b)
    (sub : kept.toFinset ⊆ ws.toFinset) :
    Hard y m (if freeAt m z ws then req else req-1) (insert z kept.toFinset) := by
  let p : W → W := fun u => u &&& m
  have haveOld {u : W} (hu : u ∈ ws) (hn : p u ≠ 0) : p u ∈ maskBank m ws.toFinset :=
    Finset.mem_erase.mpr ⟨hn, Finset.mem_image_of_mem p (List.mem_toFinset.mpr hu)⟩
  intro t run
  by_cases hf : freeAt m z ws = true
  · rw [if_pos hf]
    apply old t
    apply build_subset run
    intro u hu
    obtain ⟨nz, mem⟩ := Finset.mem_erase.mp hu
    rw [Finset.image_insert] at mem
    rcases Finset.mem_insert.mp mem with rfl | prev
    · simp only [freeAt, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hf
      rcases hf with zero | ⟨w, hw, eq⟩
      · exact (nz zero).elim
      · change p w = p z at eq
        change p z ≠ 0 at nz
        change p z ∈ maskBank m ws.toFinset
        rw [← eq] at nz ⊢
        exact haveOld hw nz
    · exact (project_subset p 0 sub) (Finset.mem_erase.mpr ⟨nz,prev⟩)
  · rw [if_neg hf]
    have new : p z ≠ 0 ∧ ∀ w ∈ ws, p w ≠ p z := by
      simpa [freeAt, p] using hf
    have hz := raw_mask hop m
    have neither : ¬ (p a = 0 ∨ p b = 0 ∨ p a = p b) := by
      intro hh
      rcases raw_simple hz hh with e | e | e
      · exact new.1 e
      · exact new.2 a ha e.symm
      · exact new.2 b hb e.symm
    have run' : build raw (y &&& m) (t+1) (maskBank m ws.toFinset) := by
      refine Or.inr ⟨p a, haveOld ha (fun e => neither (.inl e)), p b,
        haveOld hb (fun e => neither (.inr (.inl e))), fun e => neither (.inr (.inr e)),
        p z, hz, build_subset run ?_⟩
      intro w hw
      obtain ⟨nz, mem⟩ := Finset.mem_erase.mp hw
      rw [Finset.image_insert] at mem
      rcases Finset.mem_insert.mp mem with rfl | prev
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem ((project_subset p 0 sub) (Finset.mem_erase.mpr ⟨nz,prev⟩))
    have := old (t+1) run'
    omega

end PEqualNP.Outside.L_meta_12072

namespace PEqualNP.Outside.L_meta_12072

def atRow (w : W) (i : Fin 64) : Bool := w[i.val]

def fromRows (f : Fin 64 → Bool) : W := (BitVec.ofBoolListLE (List.ofFn f)).setWidth 64

theorem read_fromRows (f : Fin 64 → Bool) (i : Fin 64) : atRow (fromRows f) i = f i := by
  change (fromRows f).getLsbD i.val = _
  rw [fromRows, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofBoolListLE]
  have hi : i.val < (List.ofFn f).length := by simpa only [List.length_ofFn] using i.isLt
  simp only [i.isLt, decide_true, Bool.true_and, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi, Option.getD_some, List.getElem_ofFn]

theorem rows_ext {u v : W} (h : ∀ i : Fin 64, atRow u i = atRow v i) : u = v := by
  ext i hi
  exact h ⟨i,hi⟩

def act (p : Fin 64 → Fin 64) (w : W) : W := fromRows fun i => atRow w (p i)

theorem act_at (p : Fin 64 → Fin 64) (w : W) (i : Fin 64) :
    atRow (act p w) i = atRow w (p i) := read_fromRows _ _

theorem act_inv {p q : Fin 64 → Fin 64} (hp : Function.LeftInverse p q) (w : W) :
    act q (act p w) = w := by
  apply rows_ext; intro i
  simp only [act_at, hp i]

theorem act_zero (p : Fin 64 → Fin 64) : act p 0 = 0 := by
  apply rows_ext; intro i; rw [act_at]; simp [atRow]

theorem act_and (p : Fin 64 → Fin 64) (a b : W) : act p (a &&& b) = act p a &&& act p b := by
  apply rows_ext; intro i; rw [act_at]
  change (a &&& b)[(p i).val] = (act p a &&& act p b)[i.val]
  simp only [BitVec.getElem_and]
  exact congrArg₂ (· && ·) (act_at p a i).symm (act_at p b i).symm

theorem act_op (p : Fin 64 → Fin 64) {a b z : W} (h : z ∈ raw a b) :
    act p z ∈ raw (act p a) (act p b) := by
  simp only [raw, words, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  rcases h with rfl | rfl | rfl | rfl
  · exact .inl (act_and p a b)
  · right; left; apply rows_ext; intro i; rw [act_at]
    change (a ||| b)[(p i).val] = (act p a ||| act p b)[i.val]
    simp only [BitVec.getElem_or]
    exact congrArg₂ (· || ·) (act_at p a i).symm (act_at p b i).symm
  · right; right; left; apply rows_ext; intro i; rw [act_at]
    change (a &&& ~~~b)[(p i).val] = (act p a &&& ~~~act p b)[i.val]
    simp only [BitVec.getElem_and, BitVec.getElem_not]
    exact congrArg₂ (fun x y : Bool => x && !y) (act_at p a i).symm (act_at p b i).symm
  · right; right; right; apply rows_ext; intro i; rw [act_at]
    change (b &&& ~~~a)[(p i).val] = (act p b &&& ~~~act p a)[i.val]
    simp only [BitVec.getElem_and, BitVec.getElem_not]
    exact congrArg₂ (fun x y : Bool => x && !y) (act_at p b i).symm (act_at p a i).symm

theorem map_build {α β : Type*} [DecidableEq α] [DecidableEq β]
    {ops : α → α → Finset α} {ops' : β → β → Finset β} (f : α → β) (inj : Function.Injective f)
    (hom : ∀ a b z, z ∈ ops a b → f z ∈ ops' (f a) (f b))
    {g : α} {k : ℕ} {s : Finset α} (h : build ops g k s) :
    build ops' (f g) k (s.image f) := by
  induction k generalizing s with
  | zero => exact Finset.mem_image_of_mem f h
  | succ k ih =>
    rcases h with skip | ⟨a,ha,b,hb,ne,z,hz,tail⟩
    · exact Or.inl (ih skip)
    · exact Or.inr ⟨f a,Finset.mem_image_of_mem f ha,f b,Finset.mem_image_of_mem f hb,
        fun eq => ne (inj eq), f z, hom a b z hz, by simpa using ih tail⟩

theorem map_live {α β : Type*} [DecidableEq α] [DecidableEq β]
    {ops : α → α → Finset α} {ops' : β → β → Finset β} (f : α → β) (inj : Function.Injective f)
    (hom : ∀ a b z, z ∈ ops a b → f z ∈ ops' (f a) (f b))
    {g : α} {k : ℕ} {s : Finset α} (h : live ops g k s) :
    live ops' (f g) k (s.image f) := by
  induction k generalizing s with
  | zero =>
    change s = {g} at h
    change s.image f = {f g}
    simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a,ha,b,hb,ne,z,hz,hnew,r,hs,tail⟩
    · exact Or.inl (ih skip)
    · refine Or.inr ⟨f a, Finset.mem_image_of_mem f ha, f b, Finset.mem_image_of_mem f hb,
        fun eq => ne (inj eq), f z, hom a b z hz, ?_, r.image f, by simp [hs], by simpa using ih tail⟩
      rintro hm
      obtain ⟨u,hu,eq⟩ := Finset.mem_image.mp hm
      exact hnew (inj eq ▸ hu)

def matching (ws : List W) (j : Fin 64) (p : W) : W :=
  ws.foldl (fun v w => if atRow w j then v &&& w else v &&& ~~~w) p

theorem matching_spec (ws : List W) (i j : Fin 64) (p : W) :
    atRow (matching ws j p) i = true ↔ atRow p i = true ∧
      ∀ w ∈ ws, atRow w i = atRow w j := by
  induction ws generalizing p with
  | nil => simp [matching]
  | cons w ws ih =>
    change atRow (matching ws j (if atRow w j then p &&& w else p &&& ~~~w)) i = true ↔ _
    rw [ih]
    by_cases hj : atRow w j = true
    · rw [if_pos hj]
      unfold atRow at hj ⊢
      simp [hj, List.forall_mem_cons, and_assoc]
    · rw [if_neg hj]
      unfold atRow at hj ⊢
      have jf := Bool.eq_false_iff.mpr hj
      simp [jf, List.forall_mem_cons, and_assoc]

def cutOK (y : W) (neg : List (Fin 64)) (ws : List W) : Bool :=
  neg.all fun j => atRow y j || (matching ws j y == 0)

theorem unequal_predecessor (i j : Fin 64) {a b z : W} (h : z ∈ clean a b)
    (hd : atRow z i ≠ atRow z j) : atRow a i ≠ atRow a j ∨ atRow b i ≠ atRow b j := by
  have hz := (Finset.mem_erase.mp h).2
  simp only [raw, words, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! eq
  rcases eq with ⟨ha,hb⟩
  unfold atRow at *
  rcases hz with rfl | rfl | rfl | rfl <;> simp [ha,hb] at hd

theorem cut_forced {y : W} {k : ℕ} {ws : List W} (h : live clean y k ws.toFinset)
    (neg : List (Fin 64)) : cutOK y neg ws = true := by
  apply List.all_eq_true.mpr
  intro j _
  by_cases hneg : atRow y j = true
  · simp [hneg]
  · have z : matching ws j y = 0 := by
      apply rows_ext; intro i
      by_cases on : atRow (matching ws j y) i = true
      · obtain ⟨hp, same⟩ := (matching_spec ws i j y).mp on
        have opp : atRow y i ≠ atRow y j := fun eq => hneg (eq ▸ hp)
        obtain ⟨u, hu, diff⟩ := live_separates (fun w => atRow w i ≠ atRow w j) opp
          (fun _ _ _ h => unequal_predecessor i j h) h
        exact (diff (same u (List.mem_toFinset.mp hu))).elim
      · simp [atRow] at *
        simpa using on
    simp [hneg,z]

end PEqualNP.Outside.L_meta_12072

namespace PEqualNP.Outside.L_meta_12072

abbrev Debts := List (W × ℕ)

def Feasible (y : W) (k : ℕ) (ws : List W) (ds : Debts) : Prop :=
  ws.Nodup ∧ live clean y k ws.toFinset ∧ ∀ d ∈ ds, Hard y d.1 d.2 ws.toFinset

def debtsAfter (z : W) (ws : List W) (ds : Debts) : Debts := ds.map fun d =>
  (d.1, if freeAt d.1 z ws then d.2 else d.2-1)

theorem after_ok {y a b z : W} {ds : Debts} {ws kept : List W}
    (hard : ∀ d ∈ ds, Hard y d.1 d.2 ws.toFinset)
    (ha : a ∈ ws) (hb : b ∈ ws) (hop : z ∈ clean a b)
    (sub : kept.toFinset ⊆ ws.toFinset) :
    ∀ d ∈ debtsAfter z ws ds, Hard y d.1 d.2 (insert z kept.toFinset) := by
  intro d hd
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd
  exact nextHard (hard c hc) ha hb (Finset.mem_erase.mp hop).2 sub

def debtOK (y : W) (k : ℕ) (ws : List W) (ds : Debts) : Bool :=
  ds.all fun d => ((y &&& d.1) == 0) ||
    decide (d.2 + (ws.filter fun w => (w &&& d.1) == 0).length ≤ k)

theorem valid_debts {y : W} {k : ℕ} {ws : List W} {ds : Debts}
    (f : Feasible y k ws ds) : debtOK y k ws ds = true := by
  obtain ⟨nd, run, hard⟩ := f
  apply List.all_eq_true.mpr
  intro d hd
  by_cases zero : y &&& d.1 = 0
  · simp [zero]
  · have bound := fits zero (hard d hd) run
    have eq : zeroCount (fun w : W => w &&& d.1) 0 ws.toFinset =
        (ws.filter fun w => (w &&& d.1) == 0).length := by
      unfold zeroCount
      rw [← List.toFinset_card_of_nodup (nd.filter _)]
      congr 1
      ext w
      simp only [Finset.mem_filter,List.mem_toFinset,List.mem_filter,beq_iff_eq]
    rw [eq] at bound
    simp only [Bool.or_eq_true,decide_eq_true_eq]
    exact Or.inr bound

theorem present_nonempty {y : W} {k : ℕ} {ws : List W} {ds : Debts} (f : Feasible y k ws ds) :
    ws.length ≤ k+1 := by
  have h := live_card f.2.1
  simpa only [List.toFinset_card_of_nodup f.1] using h

def rotIndex (d : ℕ) (i : Fin 64) : Fin 64 :=
  if h : i.val < 64 - (d % 64) then ⟨d % 64 + i.val, by omega⟩
  else ⟨i.val - (64 - d % 64), by omega⟩

def swapIndex (d l h : ℕ) (i : Fin 64) : Fin 64 :=
  if atRow (BitVec.ofNat 64 l) i then rotIndex d i else
  if atRow (BitVec.ofNat 64 h) i then rotIndex (64-d%64) i else i

def swapBits (d l h : ℕ) (w : W) : W :=
  let lo := BitVec.ofNat 64 l
  let hi := BitVec.ofNat 64 h
  ((w.rotateRight d) &&& lo) ||| ((w.rotateRight (64-d%64)) &&& ~~~lo &&& hi) |||
    (w &&& ~~~(lo ||| hi))

theorem at_rotate (w : W) (d : ℕ) (i : Fin 64) :
    atRow (w.rotateRight d) i = atRow w (rotIndex d i) := by
  unfold atRow rotIndex
  rw [BitVec.getElem_rotateRight]
  split <;> rfl

theorem at_swap (d l h : ℕ) (w : W) (i : Fin 64) :
    atRow (swapBits d l h w) i = atRow w (swapIndex d l h i) := by
  unfold swapBits swapIndex
  by_cases lo : atRow (BitVec.ofNat 64 l) i = true <;>
    by_cases hi : atRow (BitVec.ofNat 64 h) i = true <;>
    simp only [lo,hi,ite_true,ite_false] <;> unfold atRow at * <;>
    simp [lo,hi,← at_rotate,atRow]
  all_goals unfold rotIndex; split <;> rfl

def permRow : List ℕ → Fin 64 → Fin 64
  | d :: l :: h :: rest, i => permRow rest (swapIndex d l h i)
  | _, i => i

def reorderWord (p : List ℕ) (w : W) : W := act (permRow p) w

def fastPerm : List ℕ → W → W
  | d :: l :: h :: rest, w => swapBits d l h (fastPerm rest w)
  | _, w => w

theorem fastPerm_at : ∀ (p : List ℕ) (w : W) (i : Fin 64),
    atRow (fastPerm p w) i = atRow w (permRow p i)
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | [_,_], _, _ => rfl
  | d :: l :: h :: rest, w, i => (at_swap d l h _ i).trans (fastPerm_at rest w _)

def Symmetry (y : W) (p q : List ℕ) : Prop :=
  (∀ i : Fin 64, permRow p (permRow q i) = i ∧ permRow q (permRow p i) = i) ∧
    reorderWord p y = y ∧ reorderWord q y = y

set_option maxHeartbeats 2000000 in
theorem feasible_transport {y : W} {p q : List ℕ} {k : ℕ} {s t : List W} {d e : Debts}
    (ok : Symmetry y p q)
    (nd : t.Nodup) (bank : t.toFinset = s.toFinset.image (reorderWord p))
    (cost : ∀ c ∈ e, (reorderWord q c.1,c.2) ∈ d)
    (f : Feasible y k s d) : Feasible y k t e := by
  obtain ⟨_, run, old⟩ := f
  have inv : Function.LeftInverse (reorderWord q) (reorderWord p) :=
    act_inv (p := permRow p) (q := permRow q) (fun i => (ok.1 i).1)
  have inv' : Function.LeftInverse (reorderWord p) (reorderWord q) :=
    act_inv (p := permRow q) (q := permRow p) (fun i => (ok.1 i).2)
  have co (a b z : W) (hz : z ∈ clean a b) : reorderWord p z ∈ clean (reorderWord p a) (reorderWord p b) := by
    obtain ⟨nz,hop⟩ := Finset.mem_erase.mp hz
    refine Finset.mem_erase.mpr ⟨?_, act_op (permRow p) hop⟩
    intro eq; apply nz
    apply inv.injective
    exact eq.trans (act_zero (permRow p)).symm
  refine ⟨nd, ?_, ?_⟩
  · have live' := map_live (reorderWord p) inv.injective co run
    rw [ok.2.1] at live'
    simpa only [bank] using live'
  · intro c hc l hl
    have prev := old _ (cost c hc)
    apply prev l
    have run' := map_build (ops := raw) (ops' := raw) (reorderWord q) inv'.injective
      (fun _ _ _ h => act_op (permRow q) h) hl
    have out : reorderWord q (y &&& c.1) = y &&& reorderWord q c.1 := by
      rw [reorderWord, act_and]
      change reorderWord q y &&& reorderWord q c.1 = _
      rw [ok.2.2]
    rw [out] at run'
    apply build_subset run'
    rintro w hw
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨nz,mem⟩ := Finset.mem_erase.mp hv
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp mem
    rw [bank] at hu
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hu
    have nz' : reorderWord q (reorderWord p a &&& c.1) ≠ 0 :=
      fun h => nz (inv'.injective (h.trans (act_zero (permRow q)).symm))
    refine Finset.mem_erase.mpr ⟨nz', Finset.mem_image.mpr ⟨a,ha,?_⟩⟩
    change _ = act (permRow q) (reorderWord p a &&& c.1)
    rw [act_and]
    change _ = reorderWord q (reorderWord p a) &&& reorderWord q c.1
    rw [inv a]

end PEqualNP.Outside.L_meta_12072

namespace PEqualNP.Outside.L_meta_12072

-- Pair and liveness choices from the upstream signed-wire checker in L_meta_9136.
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

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

set_option maxRecDepth 100000 in
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

abbrev Entry := ℕ × ℕ × ℕ × ℕ
abbrev Sym := List ℕ × List ℕ
abbrev Level := Array Entry
abbrev Catalogue := ℕ × ℕ × ℕ × ℕ
abbrev Hint := ℕ × ℕ

def rowAt (c : Catalogue) (i : ℕ) (h : Hint) : Entry :=
  ((c.2.2.1 >>> (c.2.1*i)) % (2^c.2.1), (c.2.2.2 >>> (32*i)) % (2^32),h.1,h.2)

def parts (bits word : ℕ) : List ℕ :=
  if word = 0 then [] else (List.range (word.log2 / bits + 1)).map fun i =>
    (word >>> (bits * i)) % (2^bits)

def entryBank (dict : ℕ) (e : Entry) : List W :=
  (parts 10 e.1).map fun i => BitVec.ofNat 64 (dict >>> (64*(i-1)))

def entryDebts (masks : List W) (e : Entry) : Debts :=
  masks.zipIdx.map fun mi => (mi.1, (e.2.1 >>> (4*mi.2)) % 16)

def Banned (y : W) (dict : ℕ) (masks : List W) (c : Catalogue) (k n : ℕ) : Prop :=
  ∀ j, j < n → ¬ Feasible y k (entryBank dict (rowAt c j (0,0))) (entryDebts masks (rowAt c j (0,0)))

def findArc (hints : List ℕ) (tag : ℕ) : Option (ℕ × ℕ) :=
  (hints.find? fun v => v % 1024 == tag).map fun v => ((v >>> 10) % 2048, v >>> 21)

def applyRow (p : List ℕ) (w : W) : W := fastPerm p w

theorem applyRow_eq (p : List ℕ) (w : W) : applyRow p w = reorderWord p w := by
  apply rows_ext; intro i
  exact (fastPerm_at p w i).trans (act_at (permRow p) w i).symm

def routeOK (s : List W) (ds : Debts) (t : List W) (dt : Debts) (q : List ℕ) : Bool :=
  decide ((t.map (applyRow q)).Perm s) &&
    dt.all fun c => ds.contains (applyRow q c.1, c.2)

set_option maxHeartbeats 1000000 in
theorem route_ok {y : W} {k : ℕ} {s t : List W} {ds dt : Debts} {p q : List ℕ}
    (sym : Symmetry y p q) (pass : routeOK s ds t dt q = true)
    (h : Feasible y k s ds) : Feasible y k t dt := by
  simp only [routeOK,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,List.contains_iff_mem] at pass
  have funEq : applyRow q = reorderWord q := funext (applyRow_eq q)
  have perm : (t.map (reorderWord q)).Perm s := funEq ▸ pass.1
  have ok := sym
  have left : Function.LeftInverse (reorderWord q) (reorderWord p) :=
    act_inv (p := permRow p) (q := permRow q) (fun i => (ok.1 i).1)
  have right : Function.LeftInverse (reorderWord p) (reorderWord q) :=
    act_inv (p := permRow q) (q := permRow p) (fun i => (ok.1 i).2)
  apply feasible_transport sym _ _ _ h
  · exact (perm.nodup_iff.mpr h.1).of_map _
  · ext v
    simp only [List.mem_toFinset,Finset.mem_image]
    constructor
    · intro ht
      exact ⟨reorderWord q v, perm.mem_iff.mp (List.mem_map_of_mem ht), right v⟩
    · rintro ⟨a,ha,rfl⟩
      obtain ⟨u,hu,eu⟩ := List.mem_map.mp (perm.mem_iff.mpr ha)
      rw [← eu,right u]
      exact hu
  · intro c hc
    simpa only [applyRow_eq] using pass.2 c hc

def obstruction (y : W) (neg : List (Fin 64)) (which k : ℕ) (s : List W) (ds : Debts) : Bool :=
  match neg[which]? with
  | some j => !(atRow y j || matching s j y == 0)
  | none =>
      match ds[which-neg.length]? with
      | some d => !(((y &&& d.1) == 0) ||
          decide (d.2 + (s.filter fun w => (w &&& d.1) == 0).length ≤ k))
      | none => false

theorem no_obstruction {y : W} {neg : List (Fin 64)} {which k : ℕ} {s : List W} {ds : Debts}
    (f : Feasible y k s ds) : obstruction y neg which k s ds = false := by
  unfold obstruction
  split
  · rename_i j hj
    have hc := cut_forced f.2.1 [j]
    change (((atRow y j || matching s j y == 0) && true) = true) at hc
    simpa only [Bool.and_true,Bool.not_eq_false'] using hc
  · split
    · rename_i d hd
      have h := List.all_eq_true.mp (valid_debts f) d (List.mem_of_getElem? hd)
      simpa only [Bool.not_eq_false'] using h
    · rfl

def checkChild (y : W) (neg : List (Fin 64)) (dict : ℕ) (masks : List W)
    (syms : Array Sym) (prev : Catalogue) (hints : List ℕ) (tag which k : ℕ) (s : List W) (ds : Debts) : Bool :=
  decide (k+1 < s.length) || obstruction y neg which k s ds ||
    match findArc hints tag with
    | none => false
    | some (j,g) =>
        match syms[g]? with
        | some sigma => decide (j < prev.1) &&
            routeOK s ds (entryBank dict (rowAt prev j (0,0))) (entryDebts masks (rowAt prev j (0,0))) sigma.2
        | none => false

theorem child_refuted {y : W} {neg : List (Fin 64)} {dict : ℕ} {masks : List W}
    {syms : Array Sym} {prev : Catalogue} {hints : List ℕ} {tag which k : ℕ} {s : List W} {ds : Debts}
    (symGood : ∀ v ∈ syms, Symmetry y v.1 v.2)
    (smaller : Banned y dict masks prev k prev.1)
    (ok : checkChild y neg dict masks syms prev hints tag which k s ds = true) :
    ¬ Feasible y k s ds := by
  intro f
  have size := present_nonempty f
  simp only [checkChild, Nat.not_lt_of_ge size, decide_false, Bool.false_or, no_obstruction f] at ok
  split at ok
  · contradiction
  · split at ok
    · rename_i v hv
      simp only [Bool.and_eq_true] at ok
      obtain ⟨bound, link⟩ := ok
      exact smaller _ (of_decide_eq_true bound)
        (route_ok (p := v.1) (q := v.2) (symGood v (Array.mem_of_getElem? hv)) link f)
    · contradiction

def patternFor (book groups pair : ℕ) : ℕ :=
  let ix := (groups >>> (11*pair)) % 2048
  (book >>> (80*ix)) % (2^80)

def eachAt {α : Type} (test : ℕ → α → Bool) (start : ℕ) : List α → Bool
  | [] => true
  | x :: xs => test start x && eachAt test (start+1) xs

theorem each_witness {α : Type} {test : ℕ → α → Bool} {start : ℕ} {xs : List α} {x : α}
    (h : eachAt test start xs = true) (mem : x ∈ xs) : ∃ i, test i x = true := by
  induction xs generalizing start with
  | nil => simp at mem
  | cons y ys ih =>
    simp only [eachAt,Bool.and_eq_true] at h
    rcases List.mem_cons.mp mem with rfl | rest
    · exact ⟨start,h.1⟩
    · exact ih h.2 rest

def testPair (y : W) (neg : List (Fin 64)) (dict : ℕ) (masks : List W)
    (syms : Array Sym) (prev : Catalogue) (hints : List ℕ) (book groups k : ℕ) (ws : List W) (ds : Debts)
    (pair : ℕ) (ab : W × W × List W) : Bool :=
  let (a,b,r) := ab
  let pattern := patternFor book groups pair
  eachAt (fun op z => (z == 0) || ws.contains z ||
    eachAt (fun slot kept =>
      let why := (pattern >>> (5*(4*op + slot))) % 32
      checkChild y neg dict masks syms prev hints (1 + 16*pair + 4*op + slot) why
        k (z :: kept) (debtsAfter z ws ds)) 0 (keepChoices a b r)) 0 (words a b)

def checkEntry (y : W) (neg : List (Fin 64)) (dict : ℕ) (masks : List W)
    (syms : Array Sym) (book : ℕ) (prev : Catalogue) (k : ℕ) (e : Entry) : Bool :=
  let ws := entryBank dict e
  let ds := entryDebts masks e
  !ws.contains y && eachAt
    (testPair y neg dict masks syms prev (parts 26 e.2.2.1) book e.2.2.2 k ws ds) 0 (pairs ws)

theorem clean_swap (a b : W) : clean a b = clean b a := by
  have same : raw a b = raw b a := by
    ext z
    simp only [raw,words,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]
    rw [BitVec.and_comm a b,BitVec.or_comm a b]; tauto
  simp only [clean,same]

set_option maxHeartbeats 1000000 in
theorem entry_refuted {y : W} {neg : List (Fin 64)} {dict : ℕ} {masks : List W}
    {syms : Array Sym} {book : ℕ} {prev : Catalogue} {k : ℕ} {e : Entry}
    (symGood : ∀ v ∈ syms, Symmetry y v.1 v.2)
    (smaller : Banned y dict masks prev k prev.1)
    (ok : checkEntry y neg dict masks syms book prev k e = true) :
    ¬ Feasible y (k+1) (entryBank dict e) (entryDebts masks e) := by
  let ws := entryBank dict e
  let ds := entryDebts masks e
  change (!ws.contains y && eachAt (testPair y neg dict masks syms prev (parts 26 e.2.2.1) book e.2.2.2 k ws ds) 0 (pairs ws)) = true at ok
  simp only [Bool.and_eq_true] at ok
  obtain ⟨no, all⟩ := ok
  change ¬ Feasible y (k+1) ws ds
  rintro ⟨nd,run,hard⟩
  rcases first_live run with terminal | ⟨a,ha,b,hb,ne,z,hop,hn,needed,hs,tail⟩
  · have mem : y ∈ ws.toFinset := terminal ▸ Finset.mem_singleton_self _
    have yc := List.contains_iff_mem.mpr (List.mem_toFinset.mp mem)
    rw [yc] at no
    contradiction
  · obtain ⟨r, found, perm⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) ne
    have go {a b : W} (found : (a,b,r) ∈ pairs ws) (perm : ws.Perm (a :: b :: r))
        (hs : ws.toFinset = insert a (insert b needed)) (hop : z ∈ clean a b) : False := by
      obtain ⟨kept, hk, nk, setk⟩ := recover_kept perm nd hs
      have subset : kept.toFinset ⊆ ws.toFinset := by
        rw [setk,hs]
        exact (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
      have lack : z ∉ ws := fun h => hn (List.mem_toFinset.mpr h)
      have hzt : (z :: kept).Nodup := List.nodup_cons.mpr
        ⟨fun mem => hn (subset (List.mem_toFinset.mpr mem)),nk⟩
      have fa : a ∈ ws := perm.mem_iff.mpr (by simp)
      have fb : b ∈ ws := perm.mem_iff.mpr (by simp)
      have cf : Feasible y k (z :: kept) (debtsAfter z ws ds) := by
        refine ⟨hzt, ?_, ?_⟩
        · simpa only [List.toFinset_cons,setk] using tail
        · simpa only [List.toFinset_cons] using after_ok hard fa fb hop subset
      obtain ⟨_,selected⟩ := each_witness all found
      change eachAt _ 0 (words a b) = true at selected
      obtain ⟨_,op⟩ := each_witness selected (List.mem_toFinset.mp (Finset.mem_erase.mp hop).2)
      have nz := (Finset.mem_erase.mp hop).1
      have zs : ws.contains z = false := Bool.eq_false_iff.mpr (fun h => lack (List.contains_iff_mem.mp h))
      simp only [beq_eq_false_iff_ne.mpr nz,zs,Bool.false_or] at op
      obtain ⟨_,link⟩ := each_witness op hk
      exact child_refuted symGood smaller link cf
    rcases found with direct | swapped
    · exact go direct perm hs hop
    · apply go swapped (perm.trans (.swap _ _ _)) (by rw [hs,Finset.insert_comm])
      rwa [← clean_swap]

end PEqualNP.Outside.L_meta_12072

namespace PEqualNP.Outside.L_meta_12072

theorem build_extend {α : Type*} [DecidableEq α] {o : α → α → Finset α} {y : α}
    {s : Finset α} {a b : ℕ} (le : a ≤ b) (h : build o y a s) : build o y b s := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih

def indispensable (y : W) (neg : List (Fin 64)) (base : List W) : Bool :=
  base.sublists.all fun ws => (ws == base) || !cutOK y neg ws

theorem cert_lower {y : W} {neg : List (Fin 64)} {base : List W} {ds : Debts} {budget : ℕ}
    (nz : y ≠ 0) (nd : base.Nodup) (full : indispensable y neg base = true)
    (hard : ∀ d ∈ ds, Hard y d.1 d.2 base.toFinset)
    (denied : ¬ Feasible y budget base ds)
    {k : ℕ} (run : build raw y k base.toFinset) : budget < k := by
  by_contra! small
  have refined := raw_to_clean nz (build_extend small run)
  obtain ⟨s,sub,hr⟩ := compress refined
  classical
  let ws := base.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (Finset.mem_erase.mp (sub hw)).2
  have hrun : live clean y budget ws.toFinset := eq.symm ▸ hr
  have check := List.all_eq_true.mp full ws (List.mem_sublists.mpr (List.filter_sublist ..))
  have cut := cut_forced hrun neg
  have entire : ws = base := by
    simpa only [cut,Bool.not_true,Bool.or_false,beq_iff_eq] using check
  apply denied
  exact ⟨nd,entire ▸ hrun,hard⟩

theorem lower_by_sample {y target : W} {s t : Finset W} {k : ℕ}
    (p : Fin 64 → Fin 64) (out : act p y = target) (nz : target ≠ 0)
    (avail : project (act p) 0 s ⊆ t)
    (lower : ∀ m, build raw target m t → k ≤ m)
    {l : ℕ} (run : build raw y l s) : k ≤ l := by
  obtain ⟨small,sub,hr⟩ := compress run
  have nonzero : act p y ≠ 0 := out ▸ nz
  obtain ⟨m,pay,projected⟩ := project_live raw raw (act p) 0
    (fun _ _ _ op => raw_simple (act_op p op))
    (fun _ _ _ op => act_op p op) nonzero hr
  rw [out] at projected
  have bound := lower m (build_subset projected ((project_subset _ _ sub).trans avail))
  omega

def auditRows (test : Entry → Bool) (c : Catalogue) (start : ℕ) : List Hint → Bool
  | [] => true
  | h :: rest => test (rowAt c start h) && auditRows test c (start+1) rest

theorem extend_rows {y : W} {neg : List (Fin 64)} {dict : ℕ} {masks : List W}
    {syms : Array Sym} {book : ℕ} {prev cur : Catalogue} {k start : ℕ} {rows : List Hint}
    (symGood : ∀ v ∈ syms, Symmetry y v.1 v.2)
    (smaller : Banned y dict masks prev k prev.1)
    (doneRows : Banned y dict masks cur (k+1) start)
    (ok : auditRows (checkEntry y neg dict masks syms book prev k) cur start rows = true) :
    Banned y dict masks cur (k+1) (start+rows.length) := by
  induction rows generalizing start with
  | nil => simpa using doneRows
  | cons h rs ih =>
    simp only [auditRows,Bool.and_eq_true] at ok
    obtain ⟨pass,tail⟩ := ok
    have denied := entry_refuted symGood smaller pass
    have next : Banned y dict masks cur (k+1) (start+1) := by
      intro j hj
      by_cases lt : j < start
      · exact doneRows j lt
      · have eq : j = start := by omega
        subst j
        exact denied
    have rest := ih next tail
    simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm 1] using rest

end PEqualNP.Outside.L_meta_12072

namespace PEqualNP.Outside.L_meta_12072.Clique

def y : W := 0xfee8

def base : List W := [0xaaaa,0xcccc,0xf0f0,0xff00]

def neg : List (Fin 64) := [0,1,2,4,8]

def dict : ℕ := 0xfff0000000000000ffcc000000000000ffc0000000000000ffaa000000000000ffa8000000000000ff88000000000000ff80000000000000ff08000000000000ff00000000000000fefe000000000000fcfc000000000000fcec000000000000fccc000000000000fafa000000000000faf0000000000000faaa000000000000f8f8000000000000f0f0000000000000f000000000000000eeee000000000000eaea000000000000dccc000000000000cccc000000000000aaee000000000000aaaa000000000000aaa8000000000000aa00000000000000a8a80000000000008aaa00000000000088aa0000000000008888000000000000808000000000000055000000000000002aaa0000000000000ff00000000000000ccc0000000000000aaa0000000000000a0a00000000000002aa00000000000000fe00000000000000ee00000000000000aa0000000000000088000000000000000a

def masks : List W := []

def ds : Debts := []

def syms : Array Sym := #[([],[]),([0x4,0xf000f000f000f0,0xf000f000f000f00],[0x4,0xf000f000f000f0,0xf000f000f000f00]),([0x2,0xc0c0c0c0c0c0c0c,0x3030303030303030],[0x2,0xc0c0c0c0c0c0c0c,0x3030303030303030]),([0x6,0xcc00cc00cc00cc,0x3300330033003300,0x2,0xc0c0c0c0c0c0c0c,0x3030303030303030],[0x4,0xf000f000f000f0,0xf000f000f000f00,0x2,0xc0c0c0c0c0c0c0c,0x3030303030303030]),([0x4,0xf000f000f000f0,0xf000f000f000f00,0x2,0xc0c0c0c0c0c0c0c,0x3030303030303030],[0x6,0xcc00cc00cc00cc,0x3300330033003300,0x2,0xc0c0c0c0c0c0c0c,0x3030303030303030]),([0x6,0xcc00cc00cc00cc,0x3300330033003300],[0x6,0xcc00cc00cc00cc,0x3300330033003300]),([0x1,0x2222222222222222,0x4444444444444444],[0x1,0x2222222222222222,0x4444444444444444]),([0x4,0xf000f000f000f0,0xf000f000f000f00,0x1,0x2222222222222222,0x4444444444444444],[0x4,0xf000f000f000f0,0xf000f000f000f00,0x1,0x2222222222222222,0x4444444444444444]),([0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050,0x1,0x2222222222222222,0x4444444444444444],[0x2,0xc0c0c0c0c0c0c0c,0x3030303030303030,0x1,0x2222222222222222,0x4444444444444444]),([0x7,0xaa00aa00aa00aa,0x5500550055005500,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050,0x1,0x2222222222222222,0x4444444444444444],[0x4,0xf000f000f000f0,0xf000f000f000f00,0x2,0xc0c0c0c0c0c0c0c,0x3030303030303030,0x1,0x2222222222222222,0x4444444444444444]),([0x4,0xf000f000f000f0,0xf000f000f000f00,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050,0x1,0x2222222222222222,0x4444444444444444],[0x6,0xcc00cc00cc00cc,0x3300330033003300,0x2,0xc0c0c0c0c0c0c0c,0x3030303030303030,0x1,0x2222222222222222,0x4444444444444444]),([0x7,0xaa00aa00aa00aa,0x5500550055005500,0x1,0x2222222222222222,0x4444444444444444],[0x6,0xcc00cc00cc00cc,0x3300330033003300,0x1,0x2222222222222222,0x4444444444444444]),([0x2,0xc0c0c0c0c0c0c0c,0x3030303030303030,0x1,0x2222222222222222,0x4444444444444444],[0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050,0x1,0x2222222222222222,0x4444444444444444]),([0x6,0xcc00cc00cc00cc,0x3300330033003300,0x2,0xc0c0c0c0c0c0c0c,0x3030303030303030,0x1,0x2222222222222222,0x4444444444444444],[0x4,0xf000f000f000f0,0xf000f000f000f00,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050,0x1,0x2222222222222222,0x4444444444444444]),([0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050],[0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050]),([0x7,0xaa00aa00aa00aa,0x5500550055005500,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050],[0x4,0xf000f000f000f0,0xf000f000f000f00,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050]),([0x6,0xcc00cc00cc00cc,0x3300330033003300,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050],[0x6,0xcc00cc00cc00cc,0x3300330033003300,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050]),([0x2,0xc0c0c0c0c0c0c0c,0x3030303030303030,0x7,0xaa00aa00aa00aa,0x5500550055005500,0x1,0x2222222222222222,0x4444444444444444],[0x6,0xcc00cc00cc00cc,0x3300330033003300,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050,0x1,0x2222222222222222,0x4444444444444444]),([0x4,0xf000f000f000f0,0xf000f000f000f00,0x2,0xc0c0c0c0c0c0c0c,0x3030303030303030,0x1,0x2222222222222222,0x4444444444444444],[0x7,0xaa00aa00aa00aa,0x5500550055005500,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050,0x1,0x2222222222222222,0x4444444444444444]),([0x6,0xcc00cc00cc00cc,0x3300330033003300,0x1,0x2222222222222222,0x4444444444444444],[0x7,0xaa00aa00aa00aa,0x5500550055005500,0x1,0x2222222222222222,0x4444444444444444]),([0x4,0xf000f000f000f0,0xf000f000f000f00,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050],[0x7,0xaa00aa00aa00aa,0x5500550055005500,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050]),([0x7,0xaa00aa00aa00aa,0x5500550055005500],[0x7,0xaa00aa00aa00aa,0x5500550055005500]),([0x6,0xcc00cc00cc00cc,0x3300330033003300,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050,0x1,0x2222222222222222,0x4444444444444444],[0x2,0xc0c0c0c0c0c0c0c,0x3030303030303030,0x7,0xaa00aa00aa00aa,0x5500550055005500,0x1,0x2222222222222222,0x4444444444444444]),([0x2,0xc0c0c0c0c0c0c0c,0x3030303030303030,0x7,0xaa00aa00aa00aa,0x5500550055005500],[0x2,0xc0c0c0c0c0c0c0c,0x3030303030303030,0x7,0xaa00aa00aa00aa,0x5500550055005500])]

def book : ℕ := 0x10862110421106310842108421084211044108422102421084210212108408421084420842108442084210846308421084630842108484084210848408441084210844208421108221084210821108420842108822084210842110842108421084210843084210842108424084210000000000000030000118c6318c6318c6418c6310842108441084210844000000000000001000020842108421084210842208421084210842108423108421084310842108421084210844108421084208421084240842108421084410902109042084211082211042110211084208424084210842108424084210842408421084240846109021090630842118c43190631904218c632104420c8420c422108418c23190631902118c632102420c8420c21210840842108422084210842208421084200842108421108421084010842108421084210842108441084218c6318c6118c6318c6318c6318c6218c6318c63000000000000002000000000000000000010000008421084230842108423210842108421084210842108421084210822108418c6318c6318c6318c631084210842108421084208421084220842108421084210842308421084210844108c2108c42084211082210c4210c211084218c23188631882118c631084210842108431084218c6318c6318c6218c63084210842108421084210842108421084230842121084210842108121084084210842108422084211084210842108411084218c6318c6318c6118c6300000000000000000000

def ck (p c : Catalogue) (k start : ℕ) (hs : List Hint) : Bool :=
  auditRows (checkEntry y neg dict masks syms book p k) c start hs

def c0 : Catalogue := (0,1,0x0,0x0)

def c1 : Catalogue := (0,1,0x0,0x0)

def c2 : Catalogue := (5,26,0x2c08414b017052c08008a822062c08014,0x0)

def r2_0 : List Hint := [(0,0xc01001),
  (0,0xc01004),
  (0,0xc01001),
  (0,0xc01001),
  (0,0xc01001)]

def c3 : Catalogue := (27,36,0x6c1605005901b05813901b05806a01b05814901f05811b02b088146c160500ab0160500a68160500ab01a05808901b02408901b064029c1b05814901b05810941b05814b01d058149c1b0640e902006c089c1c05814a41e05814002c08014901b0580b981b05814901b05808901e05803901b0640e901b05814,0x0)

def r3_0 : List Hint := [(0,0x280300600801001),
  (0x8000096200015,0x280100801803000),
  (0x1800025,0x400700600001001),
  (0,0x280300600801001),
  (0,0x280300600801001),
  (0,0x280300600801001),
  (0,0x2c05009),
  (0,0x10010060380680c),
  (0x1000405,0x28070200040200f),
  (0x845,0x180600600800802),
  (0x8002075000415,0x280100801803011),
  (0,0x100300203407012),
  (0x2000c05,0x28030060080100f),
  (0,0x280300600801001),
  (0x2000005,0x28030200080200f),
  (0x8000096200c15,0x280100800003000),
  (0,0x280300600801001),
  (0x20d4c00015,0x301e00800001),
  (0,0xa01300203c01802),
  (0,0xa0130020180b015),
  (0,0xa01300201401802),
  (0x6000511000104000031,0x180300a02003810),
  (0x6804095e00005,0x100300801800006),
  (0x6804056001005,0x280302000808811)]

def r3_1 : List Hint := [(0,0x280300600801001),
  (0,0x400702005c04007),
  (0,0xa0130260640c818)]

def c4 : Catalogue := (25,46,0x1b0581403003901b0580700e406c1905814901b0581403e406c1605414901b0581403a406c1605001901b05814012408c1b05814901b05814046406c1905803ac2906c16052906c1605003901b0641403800901b0640e901b05814022406c1a05808002406c16022406c1605002901b06016052706c160500e002706c16052406c160500d901b0581400e406c1604803,0x0)

def r4_0 : List Hint := [(0x215440084518010d4000005,0x40070060000881100000800800),
  (0,0x400700605c0200400c0680900e),
  (0x120143d00040d6000c2d6803074600c0d,0x28030060080100100c00000000),
  (0x240080e200202e401c07200701a001805,0xf81e03a0700d80f),
  (0xa116200c3d80090b4002025900207480080d,0x28070200040200f00001800000),
  (0x602c55,0x281a04000c0302103408007020),
  (0xf114003835800d0b4203025,0x28030200080200f0000180300e),
  (0,0xf82301608805009),
  (0x112540040490009116c03815,0x300f02200c0180600400800001),
  (0,0x2803006004020120340680900e),
  (0x88110b8003c2b880b09c002826800609600441e080f06e002c17080a05a201815801303e00480e,0xf81c03601803000),
  (0x801c35280709600501d,0x28010080340680f00c0180000e),
  (0xf460040d,0x10010060000200400003406000),
  (0xe244e0585108160c5005405,0x68030040181281004803802011),
  (0x3c01,0x40070080980180f00c0080780d),
  (0x16154405845a8180f4005c35080e094803815,0x40070200a40881100c0a01380e),
  (0x1a265206491,0x300502200c0880300404401001),
  (0,0x1602b0060ac0100400c0801002a),
  (0,0x400702005c0400100c0180900e),
  (0x44588030f400383580030b4203825,0x28070200040200f00c0180300e),
  (0,0x282d006048100200040081000f),
  (0x2200c3d,0x40030060ac0200401a0680900e),
  (0x401,0x281204000c0180f0040080780d),
  (0xc05,0x400702005c0300400c0200082e)]

def r4_1 : List Hint := [(0x1805005,0x18130260200381101a03007000)]

def c5 : Catalogue := (3,46,0x2406c1605003901b06416052406c160500e,0x0)

def r5_0 : List Hint := [(0x240004e200012cc02c47000b11800284588090fe20203e88070f400183b48050dc00103600030d420083380090be00202e80070b420182b400509c2010260803094000823900107e40001e200103c80000e,0xf81e03a0700d80f00c0180300e),
  (0x220488f001122c204087480f20e00487f08111ec004077400f1ccc0386b280d19ce0385b200d15c80304f200113800383b980d0dc20382b900d09e40301f900107a40300f200c028c02c03000b008002801,0xf8330640c41880f0600c00782f),
  (0xa8181bc00606e000c198000063001716c403857101712c00384718160dc003036b0150bc00482b401409c401823981507c40481b301405c001813181303c00000e,0x1b81e0160d81a83500c0d01980e)]

def c6 : Catalogue := (1,36,0x901b05814,0x0)

def r6_0 : List Hint := [(0x480218100085c80011620000545802140c0084c6801121a000445002100e0083c60010e1800034a8020c000082c18010a0600024a00208020081c1001060400014900204080080c0001020000004,0xf82301608805009)]

end PEqualNP.Outside.L_meta_12072.Clique

namespace PEqualNP.Outside.L_meta_12072.Clique



set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem symGood : ∀ v ∈ syms, Symmetry y v.1 v.2 := by
  have h : ∀ i : Fin syms.size,
      (∀ j : Fin 64, permRow syms[i.val].1 (permRow syms[i.val].2 j) = j ∧
        permRow syms[i.val].2 (permRow syms[i.val].1 j) = j) ∧
      applyRow syms[i.val].1 y = y ∧ applyRow syms[i.val].2 y = y := by decide +kernel
  intro v hv
  obtain ⟨i,hi,rfl⟩ := Array.mem_iff_getElem.mp hv
  simpa only [Symmetry,← applyRow_eq] using h ⟨i,hi⟩

abbrev ban (c : Catalogue) (k n : ℕ) := Banned y dict masks c k n

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem empty (c : Catalogue) (k : ℕ) : ban c k 0 := fun j h => (Nat.not_lt_zero j h).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem more {c p : Catalogue} {k start : ℕ} {rows : List Hint}
    (prior : ban p k p.1) (doneRows : ban c (k+1) start) (ok : ck p c k start rows = true) :
    ban c (k+1) (start+rows.length) := extend_rows symGood prior doneRows ok

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b0 : ban c0 0 c0.1 := empty c0 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b1 : ban c1 1 c1.1 := empty c1 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok2_0 : ck c1 c2 1 0 r2_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b2 : ban c2 2 c2.1 := by
  have p0 := empty c2 2
  have p1 : ban c2 2 5 := more b1 p0 ok2_0
  exact p1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok3_0 : ck c2 c3 2 0 r3_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok3_1 : ck c2 c3 2 24 r3_1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b3 : ban c3 3 c3.1 := by
  have p0 := empty c3 3
  have p1 : ban c3 3 24 := more b2 p0 ok3_0
  have p2 : ban c3 3 27 := more b2 p1 ok3_1
  exact p2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok4_0 : ck c3 c4 3 0 r4_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok4_1 : ck c3 c4 3 24 r4_1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4 : ban c4 4 c4.1 := by
  have p0 := empty c4 4
  have p1 : ban c4 4 24 := more b3 p0 ok4_0
  have p2 : ban c4 4 25 := more b3 p1 ok4_1
  exact p2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok5_0 : ck c4 c5 4 0 r5_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b5 : ban c5 5 c5.1 := by
  have p0 := empty c5 5
  have p1 : ban c5 5 3 := more b4 p0 ok5_0
  exact p1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok6_0 : ck c5 c6 5 0 r6_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b6 : ban c6 6 c6.1 := by
  have p0 := empty c6 6
  have p1 : ban c6 6 1 := more b5 p0 ok6_0
  exact p1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower (k : ℕ) (run : build raw y k base.toFinset) : 7 ≤ k := by
  have denial := b6 0 (by decide +kernel)
  have eqBank : entryBank dict (rowAt c6 0 (0,0)) = base := by decide +kernel
  have eqDebts : entryDebts masks (rowAt c6 0 (0,0)) = ds := by decide +kernel
  rw [eqBank, eqDebts] at denial
  exact cert_lower (by decide +kernel) (by decide +kernel) (neg := neg) (by decide +kernel)
    (by simp [ds]) denial run

end PEqualNP.Outside.L_meta_12072.Clique

namespace PEqualNP.Outside.L_meta_12072.Block

def y : W := 0x8000fee8

def base : List W := [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]

def neg : List (Fin 64) := [0,1,2,4,8,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30]

def dict : ℕ := 0xffff800000000000ffff000200000000ffff000000000000fffefffe00000000fffcfffc00000000fff0fff000000000ffeeffee00000000ffccffcc00000000ffc0ffc000000000ffaaffaa00000000ff88ff8800000000ff22ff2200000000ff0aff0a00000000ff08ff0800000000ff00ff0000000000fefefefe00000000feeefeee00000000fe00fe0000000000fcfcfcfc00000000fcccfccc00000000fc00fc0000000000fafafafa00000000f8f8f8f800000000f2f2f2f200000000f2f0f2f000000000f0f8f0f800000000f0f0f0f000000000f0e0f0e000000000f070f07000000000f050f05000000000f000f00000000000eefeeefe00000000eeeeeeee00000000eeeaeeea00000000eee0eee000000000eecceecc00000000ecececec00000000eaeeeaee00000000eaeaeaea00000000eac0eac000000000eaaaeaaa00000000e6e6e6e600000000e0e0e0e000000000dd00dd0000000000cceeccee00000000cccccccc00000000cc4ccc4c00000000cc44cc4400000000cc00cc0000000000c0c0c0c000000000aeeeaeee00000000aeaeaeae00000000aafeaafe00000000aaeeaaee00000000aaeaaaea00000000aaccaacc00000000aaaeaaae00000000aaaaaaaa00000000aaa8aaa800000000aaa0aaa000000000aa88aa8800000000aa22aa2200000000aa0aaa0a00000000aa00aa0000000000a8fca8fc00000000a8aaa8aa00000000a8a8a8a800000000a888a88800000000a2a2a2a200000000a0a0a0a000000000a000a0000000000099aa99aa0000000098989898000000008ccc8ccc000000008aaa8aaa000000008a8a8a8a0000000088f888f80000000088aa88aa0000000088a888a800000000888a888a000000008888888800000000888088800000000080aa80aa0000000080888088000000008080808000000000800080000000000077007700000000005f005f000000000055aa55aa000000005550555000000000554455440000000055005500000000003f003f00000000003cfc3cfc000000003ccc3ccc000000002aaa2aaa000000000ffa0ffa000000000ff00ff0000000000f000f00000000000eee0eee000000000e0e0e0e000000000c0c0c0c000000000afa0afa000000000ace0ace000000000aaa0aaa000000000a0a0a0a0000000008aa08aa00000000088808880000000003fc03fc0000000002aa02aa0000000000fe00fe0000000000fc00fc0000000000ee00ee0000000000ea00ea0000000000cc00cc0000000000ae00ae0000000000aa00aa0000000000a800a800000000008a008a0000000000880088000000000080008000000000002a002a00000000000e000e00000000000a000a00000000000800080000000000020002000000000000fffe000000000000fefe000000000000feee

def masks : List W := [0xffff]

def ds : Debts := [(0xffff,7)]

def syms : Array Sym := #[([],[]),([0x4,0xf000f000f000f0,0xf000f000f000f00],[0x4,0xf000f000f000f0,0xf000f000f000f00]),([0x2,0xc0c0c0c0c0c0c0c,0x3030303030303030],[0x2,0xc0c0c0c0c0c0c0c,0x3030303030303030]),([0x6,0xcc00cc00cc00cc,0x3300330033003300,0x2,0xc0c0c0c0c0c0c0c,0x3030303030303030],[0x4,0xf000f000f000f0,0xf000f000f000f00,0x2,0xc0c0c0c0c0c0c0c,0x3030303030303030]),([0x4,0xf000f000f000f0,0xf000f000f000f00,0x2,0xc0c0c0c0c0c0c0c,0x3030303030303030],[0x6,0xcc00cc00cc00cc,0x3300330033003300,0x2,0xc0c0c0c0c0c0c0c,0x3030303030303030]),([0x6,0xcc00cc00cc00cc,0x3300330033003300],[0x6,0xcc00cc00cc00cc,0x3300330033003300]),([0x1,0x2222222222222222,0x4444444444444444],[0x1,0x2222222222222222,0x4444444444444444]),([0x4,0xf000f000f000f0,0xf000f000f000f00,0x1,0x2222222222222222,0x4444444444444444],[0x4,0xf000f000f000f0,0xf000f000f000f00,0x1,0x2222222222222222,0x4444444444444444]),([0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050,0x1,0x2222222222222222,0x4444444444444444],[0x2,0xc0c0c0c0c0c0c0c,0x3030303030303030,0x1,0x2222222222222222,0x4444444444444444]),([0x7,0xaa00aa00aa00aa,0x5500550055005500,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050,0x1,0x2222222222222222,0x4444444444444444],[0x4,0xf000f000f000f0,0xf000f000f000f00,0x2,0xc0c0c0c0c0c0c0c,0x3030303030303030,0x1,0x2222222222222222,0x4444444444444444]),([0x4,0xf000f000f000f0,0xf000f000f000f00,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050,0x1,0x2222222222222222,0x4444444444444444],[0x6,0xcc00cc00cc00cc,0x3300330033003300,0x2,0xc0c0c0c0c0c0c0c,0x3030303030303030,0x1,0x2222222222222222,0x4444444444444444]),([0x7,0xaa00aa00aa00aa,0x5500550055005500,0x1,0x2222222222222222,0x4444444444444444],[0x6,0xcc00cc00cc00cc,0x3300330033003300,0x1,0x2222222222222222,0x4444444444444444]),([0x2,0xc0c0c0c0c0c0c0c,0x3030303030303030,0x1,0x2222222222222222,0x4444444444444444],[0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050,0x1,0x2222222222222222,0x4444444444444444]),([0x6,0xcc00cc00cc00cc,0x3300330033003300,0x2,0xc0c0c0c0c0c0c0c,0x3030303030303030,0x1,0x2222222222222222,0x4444444444444444],[0x4,0xf000f000f000f0,0xf000f000f000f00,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050,0x1,0x2222222222222222,0x4444444444444444]),([0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050],[0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050]),([0x7,0xaa00aa00aa00aa,0x5500550055005500,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050],[0x4,0xf000f000f000f0,0xf000f000f000f00,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050]),([0x6,0xcc00cc00cc00cc,0x3300330033003300,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050],[0x6,0xcc00cc00cc00cc,0x3300330033003300,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050]),([0x2,0xc0c0c0c0c0c0c0c,0x3030303030303030,0x7,0xaa00aa00aa00aa,0x5500550055005500,0x1,0x2222222222222222,0x4444444444444444],[0x6,0xcc00cc00cc00cc,0x3300330033003300,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050,0x1,0x2222222222222222,0x4444444444444444]),([0x4,0xf000f000f000f0,0xf000f000f000f00,0x2,0xc0c0c0c0c0c0c0c,0x3030303030303030,0x1,0x2222222222222222,0x4444444444444444],[0x7,0xaa00aa00aa00aa,0x5500550055005500,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050,0x1,0x2222222222222222,0x4444444444444444]),([0x6,0xcc00cc00cc00cc,0x3300330033003300,0x1,0x2222222222222222,0x4444444444444444],[0x7,0xaa00aa00aa00aa,0x5500550055005500,0x1,0x2222222222222222,0x4444444444444444]),([0x4,0xf000f000f000f0,0xf000f000f000f00,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050],[0x7,0xaa00aa00aa00aa,0x5500550055005500,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050]),([0x7,0xaa00aa00aa00aa,0x5500550055005500],[0x7,0xaa00aa00aa00aa,0x5500550055005500]),([0x6,0xcc00cc00cc00cc,0x3300330033003300,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050,0x1,0x2222222222222222,0x4444444444444444],[0x2,0xc0c0c0c0c0c0c0c,0x3030303030303030,0x7,0xaa00aa00aa00aa,0x5500550055005500,0x1,0x2222222222222222,0x4444444444444444]),([0x2,0xc0c0c0c0c0c0c0c,0x3030303030303030,0x7,0xaa00aa00aa00aa,0x5500550055005500],[0x2,0xc0c0c0c0c0c0c0c,0x3030303030303030,0x7,0xaa00aa00aa00aa,0x5500550055005500])]

def book : ℕ := 0xa5294a516ba51eba52941088210c4210c831084218c83188631888218c63084240842108424084212108421093210842109321084210842109321084a5294a5231a5108a529408421088220842108421210242108421021210841098c108421098c108420842108423084220842108421084330842108424085810902109184084211082210862108211086210822108421082110842084210888408821084840861008421086100842118d83190631918418c632120420c8420e0321084a5294a5108a51cea529408461090240906408421184631906319064184631886319063190641886321024208842082121084a5294a51cea5108a529410842108841084210884a5294a5294a5108a529408421090420902108442212042108421210210842124421084212522108410a101084210a101084218e5218c6318e5218c63084210842208422084210842208421084210842218c43184631844118c63084210b0420b02108441084210b0630b02108461210902108421090210844210f421084210f4210821084210932109321084a5294a516aa514aa52940842108442084210844118c231cc631cc2118c63084210cc630cc2108463a5294a514aa51caa5294a5294a514aa5108a5294a5294a51efa5108a52940842108484084210848409024084210842109024084210cc420cc2108442084210cc840cc2108484a5294a51cea514ea5294a5294a51cea510ea5294a5294a5108a518ca52940858c084210858c08421a5294a51efa510fa5294108421084211044108422102424c8424c2121084a5294a516ba5108a52940842108442084210844208421084630842108463a5294a516ba51cba5294a5294a51efa51cfa52942120424c8424e10210842124424c8424e5221084084220842408421084212108421082210842108421084210832108421084210842108f210882108400000000000000300002084210842a084260842142108421084210842104108421084410842108420842108424084210842308421084210842c08423108421084b1084710842739c0739ce739ce739ce5ad6b5ad6b5ad6b5ad635ad6b5ad6b5ad6b5ad620843008422084210842110842108431084210843a5294a5288a5294a52940000100000000010000010844108421084210844a5294a5294a5294a5294084610c0210c063084216302c6398c638216318ca5294a2a0aa5294a5294a5294a2248a5294a5294a5294a2268a5294a529400000000000000400001000000000000004000020004000c0000c42000000002000c0000c210000000020008000082100000a5294a51c8a5108a52940842108c0008c210840108421088000882108401108421040010442108021084c108421084c1084218c7218c6318c7218c63108621104211063108421098211042111841084210a0210c4210e031084218e431886318a4218c63108421084410842108447bde07bdef7bdef7bdef1084210842108531084200000000130001300000084210842608428084217bde87bdef7bdef7bdef084210842108421084230842308421084210842108421084330842108421084210842108421084220842108424084210842108421084210842108424084210842108422084247bdef7bdef7bdef7bde42108421081210842108408430084210842108421084210842108430084240842108421084230842410842108421084310844108421084a1084710842108421085310842108538c6218c6318c6318c6318c6228c6318c6318c6314210b421084210b4210808421084210842c084224210342108421084210808421084210842208422084220842108422084210842108421084320842410843108421084210843108421084210843108534210e421084210e421080842108424084240842110842108441084410842084210842108423084230842108421084240842410842108421085210842739ce739ce739ce739cf0842108423084210842418c6318c6318c6318c645294a5294a5294a5294818c6118c6318c6318c6318c6218c6318c6318c630842108c2108c230842118c6318c6418c6318c6318c6c18c6318c6c18c630000000000000020000118c6318c6818c6918c630842108432084210843221084210882108a21084000000000000003000012108421091210882108400000000000000100003421114210842111421080842108423084230842110842108431084310842108421085310853108424210a421084210a4210810843108421084310842a5294a510aa514aa529418c631b0211b06318c2318c631b0421b06318c43a5294a5108a5228a5294084410c8210c842084211082214c4214c211084208461088210886208421108621044210461108420842b0842108433084210842f08421084330842110842108421084210843739c8739ce739ce739ce08428084210842808421084240842108421084245ad685ad6b5ad6b5ad6b42108421084210842108a5294a5148a5108a529418c43190631904218c632104420c8420c4221084a5294a5168a5108a529418e431cc631ce5218c634210a4210842108421080842308421084230842118c6418c6318c6318c6484210842128421084210421084210e421084210e10842108421084210844421084210842108421140842408421084210842118c6318c6b18c6818c63210842108b21088210840842108421084300842208421084210843208423108421084810847108425ad6b5ad6b5ad6b5ad615ad645ad6b5ad6b5ad6b6318c6318c6318c6318b18c6318c6a18c6818c6394a4894a5294a5294a525294a5294a5294a529440000000000000010000210842108421085010842529485294a5294a5294a108501084210850108428c62a8c6318c6318c63118c6318c6318c7318c63108421084310842108424210c421084210c42108084230842108421084239ce689ce739ce739ce73421144210842108421088421084210842108421094a5294a5294a5294a529ce739ce739ce739ce738c6288c6318c6318c6318c6328c6318c6318c63108432084210843208421421084211142108421110842c084220842108421529425294a5294a5294a739c2739ce739ce739ce421084210f421084210f08421084240842108424739c3739ce739ce739ce7bde37bdef7bdef7bdef6318c6318c6318c6318c210842108421084210845294a5294a5294a5294b21084210842109021084210842108421092210844210842108421084210ba5294a5231a5111a529418c23190631902118c632102420c8420c2121084085810c8210c98c08421086010c8210ca1008421421084210a421084210a084300842108430084217bde47bdef7bdef7bdef421084210b421084210b0842108422084210842208421084230842108423a5294a5108a51c8a5294a5294a5108a5148a529408461090210906308421a5294a514aa510aa5294084410902109042084210844108c2108c4208421a5294a516ba510ba5294108221104211021108421082210c4210c211084218c23188631882118c63084200842108421084215294a5294a5294a529425294a5294a5294a5294108421084210842a0842110842108411084210842421084210842108421005ad615ad6b5ad6b5ad6b4210442108421084210818c6418c6318c6318c635ad605ad6b5ad6b5ad6b10842108401084210842739c4739ce739ce739ce0000000000000030000018c6318c6318c6418c63210842108421083210840000000012000120000018c6318c6318c6c18c63084210843208432084210842108421084310842118c6318c7118c6818c6318c6018c6318c6318c63084210842308421084218c6318c6318c6238c6318c6208c6318c6318c6314210842108421084210118c6318c6018c6318c63084210842c08421084218c6248c6318c6318c6315ad635ad6b5ad6b5ad6b0842108420084210842118c6318c6c18c6318c632108421084210882108400000000000000400000084210842108432084214210842108421084210a08421084210842808421084210842208421084215294a5294a529415294a5ad6b5ad6b5ad625ad6b529435294a5294a5294a210842108421082210841084210842108441084218c6318c6318c6218c6318c6318c6318c6818c631084210842108431084210842108421084c10842421024210842108421080842108421084240842110842108421084e10842739c1739ce739ce739ce7bde27bdef7bdef7bdef4210c4210842108421080842c084210842c08421108421084210842108424210842108421084210318c6318c6318c7218c635294a5294a5294a529430842108421084210842118c6318c6118c6318c6318c6318c6218c6318c63000000000000002000005ad625ad6b5ad6b5ad6b0000000000000010000018c6318c6318c6318c63084210842108422084211084210842108411084242101421084210842108084210842108423084218c6238c6318c6318c631529415294a5294a5294a000000000000012000004210842108421014210842100421084210842108529405294a5294a5294a00000000000000c000000000000000000100000008421084210842c08421084210842108430084212108421084210812108418c6318c6318c6118c6300000000000000000000

def ck (p c : Catalogue) (k start : ℕ) (hs : List Hint) : Bool :=
  auditRows (checkEntry y neg dict masks syms book p k) c start hs

def c0 : Catalogue := (0,1,0x0,0x0)

def c1 : Catalogue := (0,1,0x0,0x0)

def c2 : Catalogue := (0,1,0x0,0x0)

def c3 : Catalogue := (4,37,0xfe318be18f315c3100bf8e02b863cc670c401,0x2000000030000000200000003)

def r3_0 : List Hint := [(0,0x200400600401001),
  (0,0x400800c01c03005),
  (0,0x200400602401002),
  (0,0x380800c01c0300a)]

def c4 : Catalogue := (50,48,0x7f1cc671503a7f1d869150487f1cc6718433801cc6715048671504804c027319c54120037019c54120027315048074027f19854120117319c540fc027f1c0671503f7f19c54120157f1cc6a1503f7319c54120027f19c54120137f1cc67180317f1cc671842e7f1cc67184357f18c54120077f1cc6717c317f1f063184317f1cc670c41e7f1cc67184397319c610c4027f19c610c4137f1cc66184317f1f054120217f1cc7215c317f1cc6713c317f1cc67160317f1cc65184317f1cc670e0197f1d067184317f1cc69150347319c54120017f1cc67150477f1cc7119c317f1cc6e19c377f1cc67178347f1cc50120247f1cc6f16c2d7f1cc6712023811cc67150487f1cc67150377f1d067150487f1cc67150487f19c54120207f1f054120207f18c54120207f1cc6718431,0x300000003000000030000000400000004000000040000000400000004000000030000000400000003000000030000000300000004000000030000000300000003000000030000000300000003000000030000000300000003000000040000000300000003000000030000000300000003000000030000000300000003000000030000000300000004000000030000000300000003000000030000000300000003000000030000000400000003000000030000000300000003000000030000000300000003)

def r4_0 : List Hint := [(0,0x700e01a0300080201601001800),
  (0,0x400b02804c0900101c0440800f),
  (0,0x400b02804c0900103005c0b015),
  (0,0x400b02804c0900101c0340800f),
  (0,0x700e01a02c0801002603c07801),
  (0,0x580e01a0680801003403c07819),
  (0,0x700e01a02c0801002603c07801),
  (0,0x700e01a02c0801002603c07801),
  (0,0x700e01a04c0780f01604008001),
  (0,0x701f0200780780203a0700b81b),
  (0,0x702204204c0782003e04008002),
  (0,0x1100e04802c0801002608c07801),
  (0,0x700b0200380201002603c0080f),
  (0x89,0x70250020380200201601000003),
  (0,0x110220480a41302802609c12026),
  (0x41,0x201002003c0782c0120241582a),
  (0,0x1100e04802c0801002608c07801),
  (0,0x580e01a0300080205c01016811),
  (0,0x700e01a02c0801002603c07801),
  (0,0x701f01a0300080203e0bc01800),
  (0,0x701f01a0300080200e0c006801),
  (0,0x700e01a0300080201601001800),
  (0x2224000471,0x70310240380200001601000003),
  (0,0x400b0280d0090010300cc19015)]

def r4_1 : List Hint := [(0x200451,0x700e0420d40900201601001800),
  (0,0x403902402c018000700cc1b836),
  (0x871,0x6801076010018110120241d02b),
  (0,0x700e01a0300083c01603401837),
  (0,0x700e01a02c1f03e07a00401001),
  (0xc51,0x7029000030090400160bc1f800),
  (0xc71,0x148450880302184200e10420819),
  (0,0x380700c11c0301207005c19846),
  (0,0x70490420300084803e03401802),
  (0,0x580e01a0300080201601017800),
  (0,0x700e01a0300080201601001800),
  (0,0x400702811c090120700cc19846),
  (0,0x681002003c078010120241582a),
  (0,0x702201e02c0800209401007810),
  (0,0x404b02804c0901207004008046),
  (0x1800441,0x40220880a40a01402608c12026),
  (0x1800871,0x681002008c120260120a02102a),
  (0,0x400702811c090120700cc19846),
  (0,0x800f0020ec1604c0120081400e),
  (0,0x681002003c078010120241582a),
  (0,0x681002003c078010120241582a),
  (0,0x800f0020ec1604c0120ac1500e),
  (0,0x110220480a41302802609c12026),
  (0,0x700e01a0300080209c13401800)]

def r4_2 : List Hint := [(0,0x1100e01e02c2801009e08c16033),
  (0,0x400e08802c0a01002603c07801)]

def c5 : Catalogue := (145,57,0x1fc7319c541201afe398ce2a05206ff19c5412029037f8ce2b0a82401bfc7319c540d80dfe398ce2a0900bff1cc6717054123f8e6320a82400dfc7319c541200bfe398ce2a090077f1cc67150480cff8e6338a82601bfc7319c541380dfe3a8ce2a09006ff1cc671544802bf8e6338a62401bfc731a0541200dfe398ce2a08606ff1cc6715048107f8e6338c42a091fc731b06715034fe3d0ea338a8247f1cc6717c54123f8ea338a82400dfc7319c5412040fe398ce2a092247f1cc671502801bf8ce2a0900901bfc7319c5412032fe398ce2a09003ff1cc671504d12398ce308a824005fc671845412013fe398de338a823f31c8671504800800e6338a824005fc7319c5412004fe398ce2a09009ff1c8671504804c00fe338a824027fc7e1cc6715048fe398ce2a09023ff1f47319c5411c00fe398ce2a08ffc7b19c5412011fe398e4338a81fff1cc6715048047f8da338a82401bfc7319c5412014fe398ce2a090067f1cc6718054123f8e6338a82300dfc7319c5409c0dfe398ce2a08a06ff1cc67184540d3f8f83a8ce2a091fc731c86715048fe3c0ce2a09008ff1cc67184540fff8f0338a81301bfc7319c541202efe398ce2a0901aff19c6315048047f8e6338a823063fc7319c541201efe398ce2a090187f1cc6716854123f8e6338a825091fc7319c5512031fe398ce2a0900dff1cc6715048083f8f4338a22401bfc7319c610c40dfe398d8338c218ff1cc6c1503c0c7f8f8338a824041fc6718c5412020003f8ce2a090107f1cc6f14048037f8f8398ce30863fc7c18c5412031fe3e0c62a090037f1cc6718431047f8e6390ce30863fc7319c6115c31fe3e0c62a09010001fc7c1504808000fe318a824041fc7c18c5412019fe338a82405406ff19c5412025037f8e6338a818833fc7319c541202ffe398ce2a09e247f1cc671504805bf8e6338c218815fc67150480ac0afe398ca2a09018ff1d067150480c7f8e6338a81e863fc7319c541202dfe398ce2d8a8247f1cc67150480dff8e6328a824014007f1cc6715037fe398ce2a09002ff1cc671504b123f8e6340a824014007f1d06715048fe398ce2a088057f1cc6b19c610c7f8e6338a824011fc7319c5412010fe398e2338a8247f1cc67150480fbf8e6338a82407ffc7919c541200dfe398dc3389018ff1dc671504802bf8ee338a82401bfc7319c5d12031fe398ce3086216ff1cc6b150480b7f8e6338a81e033fc7319c5412022fe398ce2a09004ff1cc6716454123f8e6338a824059fc7319c5412019fe398ce2a0760cff1cc6718454123f8f0338a82401bfc7319c5412034fe398ce2a090037f1cc671504c123f8e6338a824015fc7319c541080dfe338a82404c06ff19c5410826037f8e6338c224063fc7819c541080d003f8e6338c218ff1cc67150480c7f8e6338a82401a007f1cc6715048,0x4000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000050000000400000004000000050000000500000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004)

def r5_0 : List Hint := [(0,0x2d0590b015c2b0550a814c29051),
  (0,0x4c070240160980805e04e0080105d02e1702d81b),
  (0x55,0x380700d0180981400c0020080886003817c0b81b),
  (0x800203e00040e,0x2d0590b0194320630ae18830800),
  (0,0x4c0700f0160040805e0001a0338660360b01d817),
  (0x2000c1d,0x380700d018004010690580b00880b00800c0001b),
  (0x1800405,0x380581008e1100a0130480983501301e0040b800),
  (0x1800c05,0x380581008e04809013048098350380580ec0d800),
  (0x18000d4001005,0x4c070240160980805e0001a03381300003c00800),
  (0x80060b4201425,0x2c0700d0da0401406c01e0080c8600d605c0b81b),
  (0,0x380700d0160840806f0b61b83701301e03c37011),
  (0,0x1c4380240160981403404e0900086002e05c2d81b),
  (0,0x8807024016040080350860080105d0e41702d81b),
  (0x40f460000d,0x4c0700f0160040805e000008010380000b01d800),
  (0x1,0x380700d0e616c3700b0200400881301e03c0882c),
  (0x1005,0x380700d016040080750221a83a01301e03c00800),
  (0,0x380700d016040080760020082d85d0b81702d81b),
  (0x1c45,0x380700d0160400801301e03c0087a0d61e43c077),
  (0,0x380700d0ba1702e00b0200403e07b0b81700d85b),
  (0x200182d680607460180d,0x380f80d03e0400801e01e03c0087d0d600000000),
  (0,0x380700d0160400807b0b81702d85d0b81702d81b),
  (0x1000094001005,0x380f024016040140800fe05c3a01e01e06c0107e),
  (0x400915620202d,0x380f80d0340980801a00203c0881d0380003c077),
  (0x400919520281d,0x380f80d0180040101f00805c0007d0381e400078)]

def r5_1 : List Hint := [(0x55,0x38110240180981408510820c088820382040b81b),
  (0x40f6602c1d,0x4c070240da0981405e04e0083386605817020011),
  (0x40f600302d980b074a02c0d,0x2c0700d0da0401406c01e0080c82e0000b400000),
  (0x3465,0x384382601c0101400c1080444208603805c2f81b),
  (0x180143d,0x22c450241140980188904e008010880581b83701b),
  (0,0x38110240520981408e1081a03385d0382344601b),
  (0,0x380700d0180981408f0020080c86003817c4601b),
  (0xf3652038c1400e244003401,0x384883b01c0104800b0200440801301e0440782c),
  (0x2401405,0x22c070240160980188904e0080109302e1b837092),
  (0,0x4c0f82403e0980808904e03c0085d02e1702d81b),
  (0x1002411,0x384989612e2580b80c0022544a88203805c4a011),
  (0xa02c352810094001005,0x2c0700d0da0401406c01e0080c81300006c00000),
  (0,0x2b8590b02704d89a13219031898),
  (0x200182d9810074a0400d,0x2c0f80d0da0401406c01e0080c86013a00000000),
  (0,0x380700d0160400186f0b81b83709e0b81b83701b),
  (0x50d4201425,0x2c0f80d0520400803401e03c0c8600000000b81b),
  (0,0x2d0590b015c2b0550a814c29051),
  (0x800c0d4201425,0x2c0f80d0da0401406c01e0080c8600000000b81b),
  (0,0x380700d016040080760020082d85d0b81702d81b),
  (0,0x380700d0de1703700b02000c4f89e0b81b80d86e),
  (0,0x380f80d03e0400801e01e03c0087d0381e43c077),
  (0x55200b094001005,0x380f80d0180981400c0020080881e04606c0007e),
  (0x4455,0x2c0700d0180981400c002008088600382803c077),
  (0x4c5588120f6003035,0x380f80d0180981400c0020080886002e17c0b81b)]

def r5_2 : List Hint := [(0x88120f6002005,0x380581002603c0080b01a0400782e05a05c0d800),
  (0x4c2d081109420501d,0x2c0700d018004010a105e17c350600d605c00017),
  (0x88060f600182d,0x380700d0180981400c0020080c86000800c0b81b),
  (0x3006144005411,0x380700d016040080730b61b81d81301e03c16011),
  (0,0x4c070240160980805e04e0080105d0e41702d81b),
  (0x3015054001805,0x380700d0180981407b14828c0b88f002008088a2),
  (0,0x380581011203c0088b048098138880b816c0d817),
  (0,0x380581006803c008130480981386905816c0d817),
  (0,0x381a0000160400c8760b81fc2d85d0b81ac2d81b),
  (0x800009c000826,0x54857150150538510b2044530a5),
  (0x80000bc00042e,0x2c8570aa1502905115805c558aa),
  (0,0x2b8590000162c41f8131602bc008ae0000004b0ad),
  (0x5895,0x385b0b51682cc350ae03805c0880b0080fc0003f),
  (0x68d900193242060c10016146005c2d,0x384881701c0343500c0021a81d80b00800001811),
  (0,0x2e0070b506a10c0100b07e00c3509302e1b8088b7),
  (0x2006c25,0x22c148000162e4200340481000086002e0002d81b),
  (0x7455801c0f6003435,0x38148000182e42000c1081000886002e2e80b81b),
  (0x7491801f1f4007871,0x2b81481708a05c5d80c02210c2100b07e0fc1f800),
  (0x9021075808015,0x4c0f8b904420c0005e04e0084085d02e1b80d81b),
  (0x10b8000826,0x2c8570aa150290510b22f0530a5),
  (0x2000035,0x2fc590000162f81f81317a2bc0080e02e0440800f),
  (0x200002d,0x2b85f8000162c45f0131602f40081802e3000b015),
  (0,0x380f00f03e0400100e0080000182e03806c0b85f),
  (0,0x386102c01c0340d80c0021086080b00806c01811)]

def r5_3 : List Hint := [(0,0x4c070240180980100b18600c3506902e0b0088b7),
  (0,0x2c070100260004181300203c618660761703581b),
  (0x23140004c1,0x3205700001631c5881318c2c0008ae18a3104b0ad),
  (0,0x3807021016040068340b80080086f0b81b8370c9),
  (0x55,0x8807024018004010850020b00880b00800c3c01b),
  (0,0x338070b508a10c1406019a3306581304603c650ca),
  (0,0x4c0f8b51a033c2f81f17200c1f813046210578b3),
  (0,0x2c0f80d1a4040080d101e03c0087d03817c3c077),
  (0x7051,0x380700d0160400801301e03c160730b61b85b8d3),
  (0x3022154003805,0x1c4380240180981400c086108088d404620c0007e),
  (0x7c39,0x385c00000e0400c84701e1fc0903802e1ac19846),
  (0x8055,0x38248210522e4210341081080889303835c6b0d5),
  (0x21154201425,0x2c0700d0da0401406c01e008088600383600b81b),
  (0x1800805,0x11c07012016048080da0363646c8380360b01d800),
  (0x1,0x38110241682cc1408202036c0881304620c08810),
  (0x40f460000d,0x23c070840160040805e000008010381bc3741d8dc),
  (0x90d900233252038c1,0x384881701c0343500b0201a80801301e1a807801),
  (0x10c18000244809431,0x381482c08a05c5d80b01a0042103407610c21001),
  (0x1,0x880702406a0980100b0200400881301e03c0882c),
  (0x1825054001005,0x4c070240da0981405e04e1a03388f0d6210088a2),
  (0,0x11c07044016050080da08c3646c88f02e2100081b),
  (0x8094352825094001005,0x1c4380240160981403404e0900c8d400000059800),
  (0x300e144008801,0x380700d0e616c3700b00800c7009e0b61b80d8df),
  (0x805094801415,0x1281100d0520401405e01e1a03385d0d63787081b)]

def r5_4 : List Hint := [(0,0x1280700d016040080e201e0080105d0b81702d81b),
  (0,0x4c07024016098080e61ca390720e30d60b01d81b),
  (0,0x2e0070b501610c0801308603c0109302e1b8370e7),
  (0x28364009cc16016146a0982d,0x3818812044034350290201a80801304600012026),
  (0x20a8e9002930400103d,0x94070120160000801300003c010380003741604c),
  (0,0x2d0591d615c4d89a0a83a8748e8),
  (0x240ace96029335a0a4ad80291f6408c3d,0x24411000044000120290000981401300009c12026),
  (0,0x88110240520981405d1da2047605d19e2344601b),
  (0xb0e90023334208cad20231f6408c3d,0x2440700001c0000680b0000400801300003c07801),
  (0,0x2c8571e8150798f21e23c0778ee),
  (0x2d3a520383d,0x244070000160000801300003c008380000ec1604c),
  (0,0x320070f60163d8080131ea03c0089302e1b8370e7),
  (0x2e11400380d,0x88110240520981401304e0901307a02e05c0b800),
  (0,0x7d8a80aa29c290511f43e47c0f7),
  (0xb4e9002b38400a8cd102a2b580a87d,0x5c068000200000800f00003c008091f80241582a),
  (0x180a4c9a827305806051,0x884981b0440903502904c1a83f01304e3f412026),
  (0x6451,0x20398fe0160400001301e000160380661f01604c),
  (0xa8c94028304006851,0x342d8170200400880f01e044160090123fc1582a),
  (0x8c79,0x38070210160840806f1bc1b83701301e03c0086a),
  (0x7cc1,0xa42284401610c210130861080086002e05c2d900),
  (0,0x88110241a40400800c086108008600e44042d81b),
  (0x8c05,0x20038141cc0140510208c0dc230e30660cc0d82c),
  (0x2409805,0x1c820440160500a1030480900b0d402e05c59800),
  (0,0x380700d0160840685d0b61b82d90501e03c2d811)]

def r5_5 : List Hint := [(0,0x880700d0160400808e1ea0080105d0e41702d81b),
  (0x40f480940d,0x1c4380240160041403404e0900083800005c1d800),
  (0x801e304007801,0xa42284415c4186b80b07e0fc1f81315e2bc57812),
  (0x5305a0bc61,0x4280982c0440400790902e4201401a20e09c12067),
  (0x408411,0x888610b01c0540d80b0200080683400206c1d801),
  (0x8ca9,0x38070210e63843700b0200403501301e03c35001),
  (0,0x38110f60523d81401301e0901309303836c6b0e7),
  (0x1005,0x4c380240160981405e04e0080103402e090008a2),
  (0x9810074a0c015,0x4c0f8240340980805e04e0083385d02e17008811),
  (0,0x4c0f82403e0980805e04e0080105d02e1702d81b),
  (0x283009660c41d,0x2c0700d0da0cc010850660b00c80b0d605c0001b),
  (0x103d,0x4c3800f0160041405e04e1a0010381bc0b01d811),
  (0,0x4c070240161f80683504c0080110502e03c2d811),
  (0,0x4c070240161180805e08c0080101302e03c37011),
  (0x2f154801415,0x381100d052098140350021a03505d0382347081b),
  (0,0xd0070b501610c0681e08603c0105d02e1b82d8e7),
  (0x200182d,0x1c41102403e0980806c04e1080086002e0b02d81b),
  (0x2c0c425,0x1c438024016098140e60600900903802e0001d81b),
  (0,0x380700d0de16c3700b0420404f81301e03c0886e),
  (0x220183d,0x8807024016040080350860080105d0581702d81b),
  (0x1805,0x4c1102403e0980805e04e0080108f02e42c008a2),
  (0,0x3809824016040130e602409c0084e0581ac1d81b),
  (0x180041d,0x380581008e0480901301e0041385d0b816c00017),
  (0x1800835,0x11c07044016050080da04e4388685d0001702d81b)]

def r5_6 : List Hint := [(0,0x38110b503e0840801301e090370600b643c37100)]

def c6 : Catalogue := (50,67,0x3f8e6338a82401e06ff1cc67150480700dfe398ce2a0901301a007f19c5412026037f8e6338a82403e06ff1cc67150480600d003f8e6338c22a091fc7319c541484803400fe398ce2a0901a7f1cc671504803406fe398ce2a8a82401a007f1cc671504c123f8e6338a82401a05001fc7319c5412031fe398de338a82401bfc7c1cc6718454123f8f8398ce2a09003001fc7319c5412006fe398ce308a824022007f1cc6715048047f8e6390ce308a824001fc731c86715048fe398de338a82407e007f1cc67150480fff8f4398ce2a09006ff1cc67184541200dfe398d8338c22a091fc781cc671504803400fe3c0ce2a09006ff1cc67150501200dfe3e0e6338a824063fc7319c63150480c7f8e6338a82889006ff1cc67150480c40dfe398d8338a824063fc7319c541203c0c7f8e6338c22a09018801fc7319c611203100000fe398ce30863fc7319c631504806400fe398ce2a0900cff1cc67150480c40a003f8e6338a824015fc731ac67150480c400fe398ce2d8a8247f1cc67150480c42d003f8e6338a82405bfc7319c541204203400fe398ce2a09006801fc7319c541080d,0x500000005000000050000000500000005000000050000000500000005000000050000000500000005000000050000000500000005000000050000000500000005000000050000000500000005000000050000000500000005000000050000000500000005000000050000000500000005000000050000000500000005000000050000000500000005000000050000000500000005000000050000000500000005000000050000000500000005000000050000000500000005000000050000000500000005)

def r6_0 : List Hint := [(0xa8071fc00187e48050dc00103618030d46008070001018000005,0x44c2c8eb0ae26c2a9120004448805400014828800),
  (0xa8071fc001c7e000d1d8002073180e0dc003436b00c0bc002c2b400a09c402423980c07c402c1b300a05c002413180203c00200e,0x44c2c8eb0ae26c2a91923045c8b91602e4548a01b),
  (0x63740010d50007274601445,0x1301c090058260201740005c0b63200005f0e80002e8000b816c00000),
  (0x48140fc004c3b48120dc00443380100be003c2e681007da03c1e181003c603c0e,0x1688e8582381582a9190a61482891b2341e43c077),
  (0x172d6003c8d0016215a0542d181507420240d,0xe03e03406026050030008020221800e01702e06c3e81c0f200000000),
  (0xa8212bc0080ab181f29d2078a3800b27c20049b100e25d0074932001179a02c5a000e158c07452a81c0fd206c33a0190bd006023901a07e40241e901903cc06003,0x1682c858244454908570ac1849005423e4780d91e),
  (0x2219600403d081a0a4005821,0xe1262584b89602e0301309512a0300089512a0443001c0001e43c077),
  (0x482b0dc006836802a0bc00a42e80280b4009c2b402609c0094260824094004c23980c07cc08c1e280c03c008c0e,0x4902c85823826c4d1190c818c4c1230d605c0b81b),
  (0x312d400c09d001a25400bc3d082e0d4e0b42d082d07420b00d,0xb01c03406026050030008020221800b85f0f01dc3006b02e00000000),
  (0xa8371fc205473a0371bc005463903617c00d453b80c0fc00043b180e0dc602433b00c0bc20042b100e09c402423903407c80841b303305c00c813202c03c003c0e,0x1682c8580ae1582a86524c45c9291622a4548a01b),
  (0x38496c0c07d000f1c480ac25,0xe01c05c590110d402c0801007e1d82e05c0ee16c2e85c0b80002d81b),
  (0x121088040421f001047880401d220fc60003e17020f458083c15200fc50083e13000f448003c11220e03000310b0208828081709200e0200831070008818001705200ec10803a03e00e40e,0x2d0590b0194320630ae18830800),
  (0x2a1247f00481ec211c7718461ce81246f08481ac011c67104618e40105f900817a01141f804407a010c1d200d03c80100e,0x1682c8580ca1903192824e49c088570c41840001b),
  (0x240106d20041a601282d,0xe01c0343985b0dc180660cc0221742e05c0220003001c0be0000b81b),
  (0x463144118b568151f400607580150f44060352009034202409001d01400b001,0xe03c090060260502384206a0d42b80e0170220443001c03605c0d800),
  (0x118710047196012c3d,0xe0de1700700d036030130950be0300086a0760443001c00017c0b877),
  (0x120b51037274006495382d0b4013025082c034402c09000c014002401,0x1301c090060260500d4218020d41800d85f02e1dc2e8170b804408800),
  (0x49414c13415,0xb801c2d4058110204a80d85f0d4178218020b64a42e8170b816c0001b),
  (0x40494c0d4b9001b2d400d479301b1d60100658835136006c4580350f6206c3580320b400c829204e094004421,0xe01c05c590110d40305c8b9022030420840220443001702e0000b81b),
  (0x403c60148dd3051346c1489d00512440104658050134009c49801f114013c41,0xae05205c228171760300884308403008843084044300001744ac0b81b),
  (0x108f500363740070d590540740084196053054004c11,0x1303e2d40f8b902e3400d81b022178138020044a42e8170dc1b80001b),
  (0x551fc001c7e180e0fc00043e00000f460140f0004038600c0d,0x1502c8a50ae4b82a91900045c8b8990004b496000),
  (0xa80727401548d000420520140d,0x5d1900000712f18e02c3e0c7020178000000040082e8000001702d800),
  (0x800b335a02cc9005831400acc108572e50158b12057234c158811047084011c01,0xe0de1700700d0361cc2d80002e02c080170060444f05c03637c088df)]

def r6_1 : List Hint := [(0x48186a1342d,0x1301c090399000dc02c1f8100223887285c0d437c2e8170b80005b81b),
  (0x124c1005c274016c91a80a134402c490858114002441985a074816415,0x600260440713004e1140b9080501783502700419c2e8000d61703501b),
  (0xa8611fc614473085b1ac415867205b16c015857a8600fc017c3b485e0dc613c33a0010bc20242b402b09c400823900107c80241b302b05c000813180b03c61740e,0x1682c8eb0ae26c4d11626a4d0999162344c89881b),
  (0x603c2c4617489006321641883d,0xe126330110240d40a41306a0fc2384206a1023b02e81c0002047601b),
  (0x6e36801b4d9486c33c01accb006a32801a4c9006831d219cc348663092194c1086427c21889e20641bc81886e90640be41882e,0x1689b0170b23ec350571501a82a85414e1a829051),
  (0x1c53900704a521bd21800b3342190b940632c4815c8d90570f400f401,0xe12205c0700d0d41cc2d80002e02c080000200440980f00003c0882c),
  (0x40753280148c2585c2b8c15ca6a85c1f8015c7608580dc01903680740bc01cc2b407209d017c23680207c402c1b300a05cc00413180203d802c0b000a01c000403,0x4f42c93c0ae4ec5405427429c9c93802e48490937),
  (0x8876434019105003e18520742d,0xb801c2d4398110dc02c1f8100d404c5780f0d40b0498170dc0005b8d3),
  (0x480a0dc01e436400a09c21e426907807c01b01b307705c009c13201d03c01740e,0x4908e8eb0ae26c4d05427e4f89312302e05c8a01b),
  (0x3f3c401d89d005d24481604500590d4216425,0xae05206c2281b17602c588430840d008843084004300000000002d81b),
  (0x80413c601ccdd007336401a0d5007a344010401,0xae05205c228171761cc000ba25602c1f83f07e044098af15e2bc0882c),
  (0x1d52900614840108b1a87e0f401b039607d0d4017c31b07c0b421ec25987c07481ec15,0x1312606c1102402e0a4130170fc178139291023b02e81700006c0881b),
  (0x240205e200816cc014570005158000c5588100fc00243b482b0dc20b03380100bc20242b402b09c00b023900107e40201e200103c80200e,0x1682c8580ca26c4d0650c818c089232345000b81b),
  (0xc08c7d00821d400644510810f4020035107f074402c0d,0x1301c09036826050178138020ce1740b85c0220443000002e05c00000),
  (0xa8011fc01887b08581dc600873b0881bc221c6b107d19d021863980917c80045b000e15cc0305300850ee41643708840ae41ec27908307cc13013907903d802c0e,0x1682c8580ae5105412222848490854286508a0811),
  (0x260302d2079064020811,0x1301c090499000dc02ca3010022178138022525142e86b0b80000b81b),
  (0x2248d0879214020c45105b07440240d,0x130e009005826050178138680041743581b0b60443000002e16c00000),
  (0xa88d1fc60b473088c1ac01f067207f16c01685788100fc00043b180e0dc20b033b08b0bc22202b408a09c415023900107c402c1b300a05c000813280903ca08c0e,0x1682c8eb0ae26c2a86527e520a411628e4548a01b),
  (0x4224293023084c02815,0x1301c09005946020340800cc0221781380228a4a42e8170b805c00011),
  (0x2202caf00622ac2160a7481d28e002c9f086226c016097401d24c80345f200117a40341f900107a40340f200d028c014030005008000c01,0x1682c858294450908571502a00885414e29c08949),
  (0x108d274020c95188d0f4220c3518090344024090010014002c01,0x1303c090058260501d83f94b0b61800d8170b61a82e81703616c08800),
  (0x212c05,0x3401c090058430201782185c0043200d86a29a5302e86b0b816c0d800),
  (0x3457005515aa0201f000607aa23c07008e019810c05,0x1642b8550a81482895029e5383509925a4b00d800),
  (0x154d50006345812805,0xc801c31c058c70201740005c0b64a80d94d29a1a82e8170b816c0d800)]

def r6_2 : List Hint := [(0x108c1b4021065688c0b4e2102568880344220090890014009c01,0x1303e2d41482601a178138021d81808001b02e1a82e8170dc0440d800),
  (0x107f1b4021465607f0b4c21425600b034402c090062014002401,0xb801c2d422843050178218020ce1800d8cc02e1a82e8170b81a80d800)]

def c7 : Catalogue := (3,57,0x7f1cc6715048037f8e6338c22a091fc7319c5412031,0x60000000600000006)

def r7_0 : List Hint := [(0x48143410050cc00133200048c458112c0c040ac380f2a0e038a45011280e0409c300f260c03894a81120000407c080f1e0203874a0111c020406c000f1a0003864900218240005e200217080005b000d160c03057000c158002c55880a10220243f00080f0001c3b08060e120143708040d0200c33800a0c200242f08080b0201c2b00060a10014270004090000c23900208240041f9000078800810200103c80000e,0x1682c8580ca26c4d0650c818c089232345000b81b),
  (0x4823341008ccc0022322004cc488212c22080af001f2b00078ab081d2a02070a7481b2912068a3802128200809f081f27020789b001d260007097401b2510068935819200c0607c38171e1a03c7450191c0e0606c30171a1803c64201618080545f200117aa0644000180f0205c38180f0d280643008180b0005c28100f092405820901507e40041e901604240540f201603080540a000d010c03003000c008002c01,0x1682c858294450908571502a00885414e29c08949),
  (0xb4d010313304064c8101131040b4b000312b00064a8001129040c0a00030270008c98001425000bc80a82e1fc00b87e00161e000547600021d0000073a02d1c000b06c10181a0404064902d18040b05c001816000405400160e060ac3700150d840a830b0290bc00a02c00200ac409c28402609c409424100708c00a820982907c40a01c102006c009c18302605c009414000704c000810182403c00000e,0x44c2c8eb0ae26c2a91923045c8b91602e4548a01b)]

def c8 : Catalogue := (1,47,0x7f1cc6715048,0x7)

def r8_0 : List Hint := [(0x480220100087c80011e20000745802180c0085c6801161a000545002140e0084c6001121800044a8020c000082c18010a0600024a00208020081c1001060400014900204080080c0001020000004,0x2d0590b015c2b0550a814c29051)]

end PEqualNP.Outside.L_meta_12072.Block

namespace PEqualNP.Outside.L_meta_12072.Block



set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem symGood : ∀ v ∈ syms, Symmetry y v.1 v.2 := by
  have h : ∀ i : Fin syms.size,
      (∀ j : Fin 64, permRow syms[i.val].1 (permRow syms[i.val].2 j) = j ∧
        permRow syms[i.val].2 (permRow syms[i.val].1 j) = j) ∧
      applyRow syms[i.val].1 y = y ∧ applyRow syms[i.val].2 y = y := by decide +kernel
  intro v hv
  obtain ⟨i,hi,rfl⟩ := Array.mem_iff_getElem.mp hv
  simpa only [Symmetry,← applyRow_eq] using h ⟨i,hi⟩

abbrev ban (c : Catalogue) (k n : ℕ) := Banned y dict masks c k n

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem empty (c : Catalogue) (k : ℕ) : ban c k 0 := fun j h => (Nat.not_lt_zero j h).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem more {c p : Catalogue} {k start : ℕ} {rows : List Hint}
    (prior : ban p k p.1) (doneRows : ban c (k+1) start) (ok : ck p c k start rows = true) :
    ban c (k+1) (start+rows.length) := extend_rows symGood prior doneRows ok

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b0 : ban c0 0 c0.1 := empty c0 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b1 : ban c1 1 c1.1 := empty c1 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b2 : ban c2 2 c2.1 := empty c2 2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok3_0 : ck c2 c3 2 0 r3_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b3 : ban c3 3 c3.1 := by
  have p0 := empty c3 3
  have p1 : ban c3 3 4 := more b2 p0 ok3_0
  exact p1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok4_0 : ck c3 c4 3 0 r4_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok4_1 : ck c3 c4 3 24 r4_1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok4_2 : ck c3 c4 3 48 r4_2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4 : ban c4 4 c4.1 := by
  have p0 := empty c4 4
  have p1 : ban c4 4 24 := more b3 p0 ok4_0
  have p2 : ban c4 4 48 := more b3 p1 ok4_1
  have p3 : ban c4 4 50 := more b3 p2 ok4_2
  exact p3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok5_0 : ck c4 c5 4 0 r5_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok5_1 : ck c4 c5 4 24 r5_1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok5_2 : ck c4 c5 4 48 r5_2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok5_3 : ck c4 c5 4 72 r5_3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok5_4 : ck c4 c5 4 96 r5_4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok5_5 : ck c4 c5 4 120 r5_5 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok5_6 : ck c4 c5 4 144 r5_6 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b5 : ban c5 5 c5.1 := by
  have p0 := empty c5 5
  have p1 : ban c5 5 24 := more b4 p0 ok5_0
  have p2 : ban c5 5 48 := more b4 p1 ok5_1
  have p3 : ban c5 5 72 := more b4 p2 ok5_2
  have p4 : ban c5 5 96 := more b4 p3 ok5_3
  have p5 : ban c5 5 120 := more b4 p4 ok5_4
  have p6 : ban c5 5 144 := more b4 p5 ok5_5
  have p7 : ban c5 5 145 := more b4 p6 ok5_6
  exact p7

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok6_0 : ck c5 c6 5 0 r6_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok6_1 : ck c5 c6 5 24 r6_1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok6_2 : ck c5 c6 5 48 r6_2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b6 : ban c6 6 c6.1 := by
  have p0 := empty c6 6
  have p1 : ban c6 6 24 := more b5 p0 ok6_0
  have p2 : ban c6 6 48 := more b5 p1 ok6_1
  have p3 : ban c6 6 50 := more b5 p2 ok6_2
  exact p3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok7_0 : ck c6 c7 6 0 r7_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b7 : ban c7 7 c7.1 := by
  have p0 := empty c7 7
  have p1 : ban c7 7 3 := more b6 p0 ok7_0
  exact p1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok8_0 : ck c7 c8 7 0 r8_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b8 : ban c8 8 c8.1 := by
  have p0 := empty c8 8
  have p1 : ban c8 8 1 := more b7 p0 ok8_0
  exact p1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower (hard : ∀ d ∈ ds, Hard y d.1 d.2 base.toFinset) (k : ℕ) (run : build raw y k base.toFinset) : 9 ≤ k := by
  have denial := b8 0 (by decide +kernel)
  have eqBank : entryBank dict (rowAt c8 0 (0,0)) = base := by decide +kernel
  have eqDebts : entryDebts masks (rowAt c8 0 (0,0)) = ds := by decide +kernel
  rw [eqBank, eqDebts] at denial
  exact cert_lower (by decide +kernel) (by decide +kernel) (neg := neg) (by decide +kernel)
    hard denial run

end PEqualNP.Outside.L_meta_12072.Block

namespace PEqualNP.Outside.L_meta_12072
def sampleRow (code : ℕ) (i : Fin 64) : Fin 64 := ⟨(code >>> (6*i.val)) % 64, Nat.mod_lt _ (by decide)⟩

theorem essential_sample {y target v : W} {s t : List W} {need : ℕ}
    (p : Fin 64 → Fin 64) (i j : Fin 64) (diff : atRow y i ≠ atRow y j)
    (sing : s.all (fun w => (atRow w i == atRow w j) || (w == v)) = true)
    (free : act p v = 0) (out : act p y = target) (nz : target ≠ 0)
    (avail : project (act p) 0 s.toFinset ⊆ t.toFinset)
    (bound : ∀ k, build raw target k t.toFinset → need ≤ k)
    (l : ℕ) (run : build raw y l s.toFinset) : need+1 ≤ l := by
  have hn : y ≠ 0 := by rintro rfl; exact diff (by simp [atRow])
  obtain ⟨bank,sub,live'⟩ := compress (raw_to_clean hn run)
  obtain ⟨u,hu,ev⟩ := live_separates (fun w => atRow w i ≠ atRow w j) diff
    (fun _ _ _ hop => unequal_predecessor i j hop) live'
  have chk := List.all_eq_true.mp sing u (List.mem_toFinset.mp (Finset.mem_erase.mp (sub hu)).2)
  simp only [Bool.or_eq_true,beq_iff_eq] at chk
  have hv : v ∈ bank := chk.resolve_left ev ▸ hu
  have cost : 0 < zeroCount (act p) 0 bank :=
    Finset.card_pos.mpr ⟨v,Finset.mem_filter.mpr ⟨hv,free⟩⟩
  obtain ⟨m,pay,rb⟩ := project_live clean raw (act p) 0
    (fun _ _ _ h => raw_simple (act_op p (Finset.mem_erase.mp h).2))
    (fun _ _ _ h => act_op p (Finset.mem_erase.mp h).2) (out ▸ nz) live'
  rw [out] at rb
  have sub' : bank ⊆ s.toFinset := sub.trans (Finset.erase_subset _ _)
  have lower := bound m (build_subset rb ((project_subset _ _ sub').trans avail))
  omega


namespace Block

theorem startDebts (clique : ∀ k, build raw Clique.y k Clique.base.toFinset → 7 ≤ k) :
    ∀ d ∈ ds, Hard y d.1 d.2 base.toFinset := by
  intro d hd
  simp only [ds,List.mem_singleton] at hd
  subst d
  intro t run
  have hY : y &&& 0xffff = Clique.y := by decide +kernel
  have hS : maskBank 0xffff base.toFinset = Clique.base.toFinset := by decide +kernel
  change build raw (y &&& 0xffff) t (maskBank 0xffff base.toFinset) at run
  rw [hY,hS] at run
  exact clique t run

end Block

namespace Table

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def ops (a b : W) : List W := [a &&& b, a ||| b, a &&& ~~~b, b &&& ~~~a]
def basicOps (a b : W) : Finset W := (ops a b).toFinset
def inputs : List W := [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff,0xff00ff00ff00ff00,0xffffffff]
def basis : List W := [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]
def truth : W := 0xfee88000fee8
def goal : W := ~~~truth
def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4269860864 * 2 ^ 32 + 4261472256) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def circuit : List Gate := [⟨.and,[0,1]⟩, ⟨.and,[2,4]⟩, ⟨.or,[0,1]⟩, ⟨.or,[2,4]⟩, ⟨.and,[8,9]⟩, ⟨.or,[6,7]⟩, ⟨.or,[10,11]⟩, ⟨.and,[3,12]⟩, ⟨.and,[6,7]⟩, ⟨.and,[5,14]⟩, ⟨.or,[13,15]⟩]

theorem monotoneUpper : Monotone2 ⟨circuit,16⟩ ∧
    ∀ x : Fin 6 → Bool, Circuit.eval ⟨circuit,16⟩ (List.ofFn x) = target x := by
  refine ⟨?_, ?_⟩
  · intro g hg
    change g ∈ circuit at hg
    change (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2
    simp only [circuit,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst g <;> simp
  · decide +kernel
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
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

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

theorem source_zero {a b z : W} (h : z ∈ basicOps a b) (one : z[0] = true) :
    a[0] = true ∨ b[0] = true := by
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> simp at one <;> tauto


theorem reduced (lower : ∀ l, build raw Block.y l Block.base.toFinset → 9 ≤ l)
    (k : ℕ) (run : build raw truth k basis.toFinset) : 10 ≤ k := by
  apply essential_sample (v := 0xffffffff00000000) (sampleRow 0x7de75c6da6585d65544d24503ce34c2ca2481c61440c2040)
    31 63 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) lower k run

theorem binary_lower (lower : ∀ l, build raw Block.y l Block.base.toFinset → 9 ≤ l)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs,legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target x) :
    10 ≤ binaryCost gs := by
  have width : inputs.length = 6 := rfl
  have init : ∀ u ∈ inputs, holds basis.toFinset u := by
    intro u hu
    have witnesses : ∀ w ∈ inputs, w ∈ basis.toFinset ∨ ~~~w ∈ basis.toFinset := by
      intro w hw
      simp only [inputs,List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with h | h | h | h | h | h <;> subst w <;> decide +kernel
    rcases witnesses u hu with a | a
    · exact .inr (.inr ⟨u,a,.inl rfl⟩)
    · exact .inr (.inr ⟨~~~u,a,.inr (by simp)⟩)
  have sample : ∀ j : Fin 64, target (fun i => (inputs.getD i.val 0)[j.val]) = bit j (~~~goal) := by
    decide +kernel
  have evaluate (k : Fin 64) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (inputs.getD i.val 0)
    have same : List.ofFn x = inputs.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi _
        have hlt : i < inputs.length := by simpa only [width, List.length_ofFn] using hi
        simp only [List.getElem_ofFn,List.getElem_map,x,List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt,Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (inputs.map (bit k)) = bit k (~~~goal)
    rw [← same,he]
    exact sample k
  obtain ⟨u,hu,run⟩ := compile gs o hg inputs basis.toFinset init evaluate
  rcases hu with rfl | rfl
  · obtain ⟨s,sub,hr⟩ := compress run
    obtain ⟨w,hw,on⟩ := live_separates (fun w : W => w[0] = true)
      (by decide +kernel : goal[0] = true) (fun _ _ _ h => source_zero h) hr
    have none : basis.all (fun w => !w[0]) = true := by decide +kernel
    have no := List.all_eq_true.mp none w (List.mem_toFinset.mp (sub hw))
    simp [on] at no

  · apply reduced lower
    have sameOps : basicOps = raw := rfl
    rw [sameOps] at run
    simpa only [goal,BitVec.not_not] using run

theorem compare (lower : ∀ l, build raw Block.y l Block.base.toFinset → 9 ≤ l)
    (s : ℕ) (h : HasCircuitSize 6 target s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  obtain ⟨C, fits, size, computes⟩ := h
  by_cases has : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g,hm,op⟩ := has
    have less : (C.gates.filter isBinary).length < C.gates.length :=
      List.length_filter_lt_length_iff_exists.mpr ⟨g,hm,by simp [isBinary,op]⟩
    have count := binary_lower lower C.gates C.output (fun g hg => fits g hg) computes
    change 10 ≤ (C.gates.filter isBinary).length at count
    obtain ⟨ok,correct⟩ := monotoneUpper
    refine ⟨⟨circuit,16⟩,ok,?_,correct⟩
    change C.gates.length ≤ s at size
    change 11 ≤ s
    omega
  · refine ⟨C,?_,size,computes⟩
    intro g hm
    obtain ⟨ops',ar⟩ := fits g hm
    refine ⟨?_,ar⟩
    change g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not at ops'
    change g.op = GateOp.and ∨ g.op = GateOp.or
    rcases ops' with a | b | n
    · exact .inl a
    · exact .inr b
    · exact (has ⟨g,hm,n⟩).elim

end Table
end PEqualNP.Outside.L_meta_12072

theorem PEqualNP.Outside.L_meta_12072 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4269860864 * 2 ^ 32 + 4261472256) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4269860864 * 2 ^ 32 + 4261472256) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_12072.Table.compare
    (PEqualNP.Outside.L_meta_12072.Block.lower (PEqualNP.Outside.L_meta_12072.Block.startDebts PEqualNP.Outside.L_meta_12072.Clique.lower))
