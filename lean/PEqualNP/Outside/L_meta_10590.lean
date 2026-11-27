import PEqualNP.Defs

-- A vertex restriction forces the loss of a binary gate. The remaining
-- six-variable function needs eleven binary gates even with free complements.
-- The finite certificates below are checked by the kernel. A size-thirteen
-- monotone witness then handles every circuit that uses a negation.

namespace PEqualNP.Outside.L_meta_10590

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

end PEqualNP.Outside.L_meta_10590

namespace PEqualNP.Outside.L_meta_10590

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

end PEqualNP.Outside.L_meta_10590

namespace PEqualNP.Outside.L_meta_10590

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

end PEqualNP.Outside.L_meta_10590

namespace PEqualNP.Outside.L_meta_10590

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

end PEqualNP.Outside.L_meta_10590

namespace PEqualNP.Outside.L_meta_10590

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

end PEqualNP.Outside.L_meta_10590

namespace PEqualNP.Outside.L_meta_10590

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

end PEqualNP.Outside.L_meta_10590

namespace PEqualNP.Outside.L_meta_10590.Clique

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

end PEqualNP.Outside.L_meta_10590.Clique

namespace PEqualNP.Outside.L_meta_10590.Clique



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

end PEqualNP.Outside.L_meta_10590.Clique

namespace PEqualNP.Outside.L_meta_10590.Universal

def y : W := 0xfffeeca0

def base : List W := [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]

def neg : List (Fin 64) := [0,1,2,3,4,6,8,9,12,16]

def dict : ℕ := 0xffffff0000000000fffffafa00000000fffff0f000000000ffffeeee00000000ffffcccc00000000ffffcc0000000000ffffaaaa00000000ffffa0a000000000ffff888800000000ffff808000000000ffff00cc00000000ffff00aa00000000ffff00a000000000ffff000000000000fffcfcf000000000fffaff0000000000fff0fff000000000fff0ffa000000000fff0ff0000000000fff0fcf000000000fff0f0f000000000ffeeffee00000000ffeeff0000000000ffccffcc00000000ffccff0000000000ffcccccc00000000ffcccc0000000000ffcc00cc00000000ffaaffaa00000000ffaaffa000000000ffaaff2200000000ffaaff0000000000ffa2ffa200000000ffa0ffa000000000ffa0ff0000000000ff88ff0000000000ff80ff8000000000ff33cc0000000000ff32ff3200000000ff30ff3000000000ff22ff2200000000ff22ff0000000000ff20ff2000000000ff0cff0000000000ff0aff0000000000ff02ff0200000000ff00ffa000000000ff00ff2200000000ff00ff0000000000ff00cc0000000000ff00000000000000fefefefe00000000fcfcfcfc00000000fcfcecec00000000fcf0fcf000000000fafafafa00000000fafaf0f000000000fafaaaaa00000000fafa000000000000f5f4f5f400000000f5f0f5f000000000f0f0f0f000000000f0f0a0a000000000eeeeeeee00000000eeeecccc00000000eeeeaaaa00000000eeee000000000000eceeecee00000000ecececec00000000eaeaeaea00000000cfcccfcc00000000cf00cf0000000000cceeccee00000000cccccccc00000000cccccc0000000000cc44cc4400000000cc00cc0000000000bbff000000000000afafaaaa00000000afafa0a000000000afaf000000000000aeaeaeae00000000aaffaaaa00000000aaff000000000000aafaaafa00000000aaeeaaee00000000aaaafafa00000000aaaaeeee00000000aaaaaaaa00000000aaaaa8a800000000aaaaa0aa00000000aaaaa0a000000000aaaa888800000000aaaa22aa00000000aaaa0a0a00000000aaaa00aa00000000aaaa000000000000aa88aa8800000000aa00aa0000000000a8aaa8aa00000000a8a8a8a800000000a2aaa2aa00000000a0f0a0f000000000a0aaaaaa00000000a0aaa0aa00000000a0aaa0a000000000a0a2a0a200000000a0a0aaaa00000000a0a0a0a000000000a0a000000000000088cccccc0000000088cc88cc0000000088aaaaaa0000000088aa88aa000000008888aaaa000000008888888800000000888800000000000080808080000000005555000000000000550055000000000050505050000000003fff00000000000033ff00000000000033cc33cc000000003333000000000000330033000000000030f030f0000000002aaa2aaa0000000022aaaaaa0000000022aa22aa00000000222222220000000020aa20aa000000000fff0000000000000ff00ff0000000000aaaaaaa000000000aaa0aaa000000000a0a0a0a0000000000ffff000000000000ff00ee0000000000ff00cc0000000000ff00aa0000000000ff00000000000000fa00fa0000000000f0f0f00000000000ee00ee0000000000cf00cc0000000000cccccc0000000000cc00cc0000000000cc00000000000000aaaaaa0000000000aaa0aa0000000000aa22aa0000000000aa00aa0000000000aa00000000000000a000a000000000008800880000000000330000000000000022aaaa000000000022002200000000000f000000000000000aaaaa00000000000a000a000000000000fafa000000000000eeee000000000000aaaa000000000000a0a0000000000000888800000000000000cc00000000000000aa

def masks : List W := []

def ds : Debts := []

def syms : Array Sym := #[([],[]),([0x6,0xcc00cc00cc00cc,0x3300330033003300],[0x6,0xcc00cc00cc00cc,0x3300330033003300]),([0x4,0xf000f000f000f0,0xf000f000f000f00,0x1,0x2222222222222222,0x4444444444444444],[0x4,0xf000f000f000f0,0xf000f000f000f00,0x1,0x2222222222222222,0x4444444444444444]),([0x7,0xaa00aa00aa00aa,0x5500550055005500,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050,0x1,0x2222222222222222,0x4444444444444444],[0x4,0xf000f000f000f0,0xf000f000f000f00,0x2,0xc0c0c0c0c0c0c0c,0x3030303030303030,0x1,0x2222222222222222,0x4444444444444444]),([0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050],[0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050]),([0x6,0xcc00cc00cc00cc,0x3300330033003300,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050],[0x6,0xcc00cc00cc00cc,0x3300330033003300,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050]),([0x4,0xf000f000f000f0,0xf000f000f000f00,0x2,0xc0c0c0c0c0c0c0c,0x3030303030303030,0x1,0x2222222222222222,0x4444444444444444],[0x7,0xaa00aa00aa00aa,0x5500550055005500,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050,0x1,0x2222222222222222,0x4444444444444444]),([0x2,0xc0c0c0c0c0c0c0c,0x3030303030303030,0x7,0xaa00aa00aa00aa,0x5500550055005500],[0x2,0xc0c0c0c0c0c0c0c,0x3030303030303030,0x7,0xaa00aa00aa00aa,0x5500550055005500])]

def book : ℕ := 0x1084210842108c61084239d073a4e73a50839ce7318c6324c6324c9318c612442118461184212449420e842508424e7421080852908421085290842131929318c631929318c62112921084211292108410842108421244910842318e7318c6318e7318c61084210c4310c431084218ce31a4631a4e718c63084210a4210a4290842139c673a4e73a46339ce718c631a46918c6318c634a4294a5294a4214a52910482124421248410442084c10a4210a4c60842131846318c631842318c64a5294a529499264a52908442084210844208421210a521084210a52108408481084210848408421318c631cc731cc7318c621024210842102121084084210902408421084214202842108420214210810842108421204810842084210a1290a021085290842108442084210844208421084e708421084e708421084840842108484108421092910842109290842108529084210852939c4739ce739c4239ce71084211d2911c421092939c6739ce739c6339ce729465294a529463294a5294e7294a5294a5294a5108631084210863108420846308421084630842100000000000000200006084230842208421084214a5294a5224a5294a5290000000000000060000200000000000000600009084210842108422084260004002400024420000008461090210906308421210242148421421210841084212400124421080218c63194211946318c234a52948800489294a409294a528c8328ca52948510842108451084510842318c6318c8318c8318c6084210842108421084220842108421084210842910882124421248410842210842248422489210844a52949129491244a52918c6918c6318c6318c63294a5294a9294a5294a54a5294a5264a5294a52939ce739ce339ce739ce7420a841d0841ca54210808429084210842108421088c10a4210a4c608821210e421084210e72108408421091290902108529108421084010842108420000000000000040000900000000000000400001210842108521085210842108421089210842108918c6318c6418c6318c63084210842208425084211084410842108431084221084210882108421088210842108221084210841084210846108421084218c6318c6218c6318c6339ce739ce639ce739ce74a52949d2949d274a52918c6319c6319c6718c6339ce738ce738ce339ce718ca319c6319ca518c6339c673a0e73a06339ce7420e841508414e542108109221184211926108420852109021091240842131926308c630922318c6211242048420521210844a5294a1294a1284a5294a4694a5294a4634a5294a4e94a5294a4e74a529294a9294a5294a5294a539c873a4e73a48439ce74a4a949d2949ca54a52939ce73a0e73a0e839ce7420284250842421421084a4e94a1294a0e74a529420e842108420e7421080842608421084210842118c6318c6718c6318c6342108421014210842108294a5294a2294a5294a542108421064210842108210842108421084210882108421084210842108510842108491084910842084270842108421084272108421084210892108808422084210842208421108431084910842108422108521084210852108408421084290842108421108c212442124c6108424a4a94a5294a4a54a52931846324c632442318c64a44949929498424a5294a4694a1294a0634a529294a52a0a52a0a8294a5421084150841505421080842108423084210842310842108451084210845318c6318c6318c7318c839ce739ce839ce739ce71082212442124211084218ca318463184a118c634a44948529484414a529084610a0210a0630842129425294a529421294a5294652a0a52a063294a5084210952909421085294202841508414214210821084210842108921084318c6318c9318c6318c6210842108921084210844a5294a5294a5284a529294a6294a5294a5294a508421084240842108424318c9318c6318c6318c62108421084210852108808421084260842108426318c7318c6318c6318c6421084210942108421084a5294a5294a5264a529294a5294a7294a5294a50842108421084230842918c6318c6818c6318c6318c6318c6318c6318c68084210842708421084210842108423084210842139ce739ce239ce739ce708421084210842308422294a5294a5294a8294a5421084210842109421081084910842108491084208429084210842908421318c9318c6318c9318c621089210842108921084108421084310843108420842108423084230842118c6318c6318c6918c63318c6318c9318c9318c642108421084210542108318c7318c6318c7318c60842308421084230842110843108421084310842318c6318c7318c7318c6294a5294a5294a3294a5294a7294a5294a5294a5084210842208421084220842108427084210842708427084210842708421318c6318c6318c7318c9318c6318c6318c8318c9294a3294a5294a5294a5108421084210847108420000000000000020000939ce739ce739ce839ce74210842108421074210810842108491084210842108411084210842108421084310842108421084218c6318c6918c6318c6339ce739ce939ce739ce74a5204a5294a5294a529084210842908429084212108421089210892108410842108411084210842294a4294a5294a5294a5084410a4210a44208421084810a4210a484084214a52948d2948d234a529210242248422421210844a52949529495254a5294a42949129490214a52939ce739ce739ce739ce708421084210842908421084210842108428084210842108426084210842121084210842108821084294a5294a5294a5294a5294a5294a5294a1294a539ce739ce739ce639ce7318c6318c6318c9318c618c6318c6118c6318c63294a5294a3294a5294a518c6318c6318c6718c6339ce739ce739ce339ce710842108421084210842000000000000003000000000000000000050000008421084200842108421084210842508421084214a5294a5204a5294a5291084210843108421084218c6318c6018c6318c63318c6318c6318c4318c62108421084210872108408422084210842108421000000000000001000091084210844108421084210842108491084210849108421084210848108421084410842108421084210842108421084510842318c6318c6318c8318c64a5294a5294a5274a529318c6318c6318c1318c60842108421084220842908421084210842708421318c6318c6318c6318c64210842108421084210818c6318c6618c6318c63421084210842101421082108421084210852108921084210842108621084318c6318c6318c3318c6318c6318c6318c5318c6210842108421083210840842108424084210842108421084210842508421318c6318c6318c2318c60000000000000060000000000000000000200000000000000000009000000000000000000040000000000000000000100000084210842108421084214a5294a5214a5294a5294a5294a5244a5294a5291084210842108461084218c6318c6318c6318c634a5294a5294a5294a5290842108421084260842110842108421084310842318c6318c6318c7318c64a5294a5294a5224a52910842108421084910842108421084210844108422108421084210822108408421084210842308421210842108421085210840842108422084210842121084210842108421084084210842908421084294a5294a5294a5244a5294a5294a5294a5234a5294a5294a5294a5254a529084210842108424084212108421084210812108408421084210842208421108421084210841108424a5294a5294a5214a52900000000000000000000

def ck (p c : Catalogue) (k start : ℕ) (hs : List Hint) : Bool :=
  auditRows (checkEntry y neg dict masks syms book p k) c start hs

def c0 : Catalogue := (0,1,0x0,0x0)

def c1 : Catalogue := (0,1,0x0,0x0)

def c2 : Catalogue := (2,28,0xa426c51a41b851,0x0)

def r2_0 : List Hint := [(0,0xc01001),
  (0,0x1402001)]

def c3 : Catalogue := (22,38,0x9c2607414670971804e841b051072709a1803d9c20c600f69095180519c23c6c14690901b051a425860146906c1440da423c6c14688791801ba42486c0a290921cc519c2207219690921b051a41b06314670821804ea41b46014690941b051a426475146709923465,0x0)

def r3_0 : List Hint := [(0,0x280200e00c03806),
  (0,0x280300e00803808),
  (0,0x200500202c05009),
  (0,0x280301a0080080c),
  (0,0x780e0220400780e),
  (0,0x280301a0080080c),
  (0,0x180501a00806001),
  (0,0xa00202600c08812),
  (0,0x180501a00806001),
  (0,0x180501a00806001),
  (0x600005,0xb8030220080b015),
  (0x10d4800415,0x502a0100a801),
  (0,0xe01b0020680c818),
  (0,0x280301a0080080c),
  (0,0x180501a00806001),
  (0,0xe8050380100d801),
  (0,0x280301a0080080c),
  (0x400025,0x100300206801003),
  (0,0xb8200220400f81e),
  (0,0xe01b0020740e01b),
  (0,0xb8200220740f81e),
  (0,0xa00302200809812)]

def c4 : Catalogue := (132,48,0x9c1b060144189c1e46c180409c1e46c180139c22c6c180519c1e46c180129c2306c180519c1e06c180129c2306c1804e781b0601441c9c1b05f1441c9c1e46b180499c1b06014420791b06014420901e46c1441ca9270901b051a52446c180519c1e4711804e9c1e460068149c1e46c05c149c240791b0149c25479144179c22871180519c25479180149c2286c1a451a927095180519c1e471180059c2286c180059c2406c144169c25460144169c1e06c14416a51b051070169c1e46c180399c1f46c180519c1b0601441e9c1e46c1800c9c2686c180519c1e46c1803f9c20c6c180519c2386c180519c2446c180519c1e4721804ea9294921b0516c174510b41c9c1e460168519c1e4701803d9c25c601443d9c1b0601442e9c1b05d1440d9c1e46f1803d9c1e4600f41b9c2486c1442e9c1b05d1442e921b05d1442f9c1e47218004a21e46c180519c1e46c1804c9c1ec6c180519c1e46c1804ea21e46c18049a4270921b051a21e4721803da41b0601441ca21e46c1804ea42486c1805100290921b051791b0601442f9c1e46c180299c21c6c180519c1e46c144179c2486c17428791b0600bc28a41e46c180289c1e4600ac289c220721803d791cc601442fa22206c180519c1e473180289c2206c19451a41e46c144169c1e4721803d9c1e46b18011a21e46c180119c1e46c194119c1e46c1804f9c1e86c180519c1e46c1443b9c1f86c180519c1e46c180429c2006c180519c1e4601543d791b060170519d1e46c180519c1e46c180449c1fc6c180519c1e46c180269c2246c180519c1e46010c119c1e46c178289c1b062180269c1e46c198419c2046c18005a92706d180519c1b460144169c208601443d9c1b0601441f9c1e46c180509c1e46c180099c24c6c180519c1e46c180469c1f06c180519c2286c180519c1e4751804e9c2346c180419c2206c180519c1e4761803d9c2648d1803da42346c180519c23473180519c2346c180289c26479180419c1b060144249c1e46c180239c2186c180519c1e46c18014791b06014430a01e46c180519c1e46c1802a9c2146c180519c1e46c180289c1e46c180419c2046c180519c1e46c18051,0x0)

def r4_0 : List Hint := [(0,0xa00504200c0880d00404c0080c),
  (0,0x100500400c0080d01604c04822),
  (0,0xb80504200c0880d00408c0080c),
  (0,0xa00504200c0880d00408c0080c),
  (0,0xa00504200c0882500404c00824),
  (0,0xa00504200c0880d00404c0080c),
  (0,0xa00504200c0882500404c00824),
  (0,0x1081101a04c0080c02801401802),
  (0,0xb80504200c0880d00404c0080c),
  (0,0xa0050420380880d00804c0080c),
  (0,0xa00504200c0880d00404c0080c),
  (0,0x28030060080100c00a08408813),
  (0,0x282603400c068270040041300c),
  (0,0x100500400c0880d01602814828),
  (0xc00005,0x200500200c0300d0160281482a),
  (0x2154800405,0x100500200c0a80d0160280482a),
  (0x10010d4000005,0x280200e00c038060560680502b),
  (0x400835,0xa02e02200c1682b0340b000003),
  (0,0xa00f06200c0883000404c17812),
  (0,0x100500400c0880d01602814828),
  (0,0xb8200220d41a02b0200cc08832),
  (0,0xb80f0420380880d04604c1b00c),
  (0,0x100506e00c0080d01604c00822),
  (0,0xb80504200c0880d00404c0080c)]

def r4_1 : List Hint := [(0,0xb8390420900880d07004c1b00c),
  (0,0xb80504200c0880d00404c0080c),
  (0,0xb80f0620e80882902604c0380c),
  (0,0xe01e08006c0083f07c0f41e03b),
  (0x400c35,0x28030220080983802c10c21041),
  (0,0x280301a0080080408a1140a844),
  (0x401061,0xd02108e0342300d0460480080c),
  (0,0xb80f0040380080d03404c04822),
  (0,0xb8050420100882e0161200480a),
  (0,0x281706200c068110040040b00c),
  (0,0xa0050420380883000812800849),
  (0,0xb80301c0140780d00405806001),
  (0,0x100500400c0084c01604c0484b),
  (0,0xb80504200c0880d00408c0080c),
  (0,0xa00f06200c0882500404c03824),
  (0,0xa00504200c0880d00408c0080c),
  (0,0xa00506200c0883000404c17812),
  (0,0x1081101a0500280302600406002),
  (0x401435,0xa003022008098120340b006800),
  (0,0xb80f0420380880d02604c1b00c),
  (0,0xb80504200c0880d00404c0080c),
  (0,0xa00504208c0880d00804c0080c),
  (0,0xa005042008098010060440680c),
  (0,0x1f00500400c0080d07c04c00822)]

def r4_2 : List Hint := [(0,0xa00504200c0880d00408c0080c),
  (0,0xb80f06200c0882500405803806),
  (0x3005054e00c05,0xb80506200c088300040580a815),
  (0xa01005,0xb84d02e00c0880d00405800815),
  (0x401835,0xa00202600c088120340b00000d),
  (0x1825,0xa005058008250010060000680c),
  (0x1c15,0xa00f06200c0883000404c0a812),
  (0,0xa00504200c0300d0041280080c),
  (0x402015,0xa00f06200c0883000404c0a812),
  (0,0x1080601a1280080c02801401802),
  (0x10080d4001c05,0xa00202600c0881209c0681584e),
  (0,0xa0030220141080d00408c06001),
  (0x2455,0xa00505800c0a80d0041280080c),
  (0,0x1081101a0500280304600406002),
  (0x2465,0x180501a1040003100403000816),
  (0,0xa005042008098010060440680c),
  (0,0xa00504200c0880d00404c0080c),
  (0,0xa00504200c0880d00404c0080c),
  (0,0x1081101a04c0080c02801401802),
  (0xc17c002c53100a0f8800836300a078000816,0x2a0530a41442804f),
  (0,0x180501a1580a84500403000855),
  (0xc03425300e054e03405,0xb80f062038088300000540a815),
  (0x3019,0xe01e01a06c0080c0340640a818),
  (0x18090b44020251009034602005,0xa00202600c088120341040a82b)]

def r4_3 : List Hint := [(0xf20400307d,0xd01e02a0c42c00d02615c06001),
  (0xc04025300e054e04005,0xb80f062038088300000540a815),
  (0,0xb80f062038088300201280400c),
  (0,0xa00506200c0883000404c17812),
  (0,0xa00504200c0880d00408c0080c),
  (0x401815,0xa00506200c0883000404c0a812),
  (0x401835,0xa00202600c088120000b00000d),
  (0x1815,0x68000620300081300601400002),
  (0,0x281d0380080081b0060342080c),
  (0,0xf0050800080d8010ac0542b03b),
  (0xa194204415,0xb8030220680b80d0040580a801),
  (0x48750812114403c15,0xb80002a0800881502007c0a81e),
  (0x3085,0xe00003806c0081b0340640a818),
  (0,0x281e0800080081b00600c0883b),
  (0x404035,0xa003022008098120340b006800),
  (0x403835,0xa00202600c088120340b00000d),
  (0xc04c3d,0xf81e0221341600d02a04c09059),
  (0x13154204c25,0xe0010360700001b0380000d81d),
  (0x1891,0x185b0b40c41280702609003001),
  (0x401835,0xa00202600c088120340b00000d),
  (0,0xa0050420940880d00804c0080c),
  (0,0x18050ba00c088400041700081b),
  (0x4411,0x100500400c0080d01604c05822),
  (0,0xb8050420380884c0081280080c)]

def r4_4 : List Hint := [(0x4811,0xb8240420800880d04a04c0d80c),
  (0,0xb8050420380880d00804c0080c),
  (0,0xe01e08006c0081b0061581e03b),
  (0,0xb8050420380880d04604c0080c),
  (0,0xb80504200c0880d00404c0080c),
  (0x4c3d,0x2001b002068188130001581d85e),
  (0,0xe8050380080d8010061040680c),
  (0,0x28030800080081b0ac1580a83b),
  (0,0xf0050800080d8010ac0542b03b),
  (0,0xb80f0420380880d02c04c1b00c),
  (0,0xb80f0420380880d02c04c1b00c),
  (0x405061,0xd0210c00782300d02617c0080c),
  (0,0xb80f0420380880d04604c1b00c),
  (0,0x286204200c068610040040980c),
  (0,0xb80f0420380880d04604c1b00c),
  (0,0x2862042008008130060343080c),
  (0,0x18620220140682100403009801),
  (0,0xb80504200c0880d00404c0080c),
  (0,0xb8030220141080d00404c06001),
  (0xc03835,0xb80f062038088300141280000c),
  (0,0x180d0420ac2f04500804c00863),
  (0x3c81,0xd01e08c0843000d02617c06001),
  (0,0x3080d0420300980100613802802),
  (0,0xe01e01a06c0080c02801401802)]

def r4_5 : List Hint := [(0,0xe01e01a06c0080c0280841e013),
  (0x805025100f054a05005,0xb81d03e0800881e0000540a815),
  (0,0xe01d03806c0081b0340641e018),
  (0,0xe01e01a06c0080c02a01401802),
  (0x300d0d4805405,0xb80f062038088300560283202a),
  (0,0x800506200c0880d0040580080c),
  (0,0xb80f0620380883004a04c32812),
  (0,0xb80504200c0880d00408c0080c),
  (0,0x100500400c0080d01604c04822),
  (0,0xb80504200c0880d00408c0080c),
  (0,0xb80f062038088300201280400c),
  (0,0xe01e08006c1b01b0061581e03b)]

def c5 : Catalogue := (133,58,0x1e46c180510b41c9c1e46c180510fa70791b06016c519c1e46c180510de70791b06015c519c1e46c18033015e46c180510cc05a3270791b06014670791b0601444b9c1e46c1805314670791b0601444a9c1e46c1805214670791b06014449a52706c1805107a70791b0601441e002706c1805107a9c9c1e46c1804e9c1e46c18051138009c1e46c1804ea51e46c180510729ca31e46c180519c1e46c1805107670791b0601444da92706c180510728c791b06014405a3270791b0601268c791b060144499c1e46c18051071e4771b0601441c9c1e46c1805105e70791dc6c1441700270791b05105e70791c06c180519c1e47118051124009c2446c180519c1e46c1805105270791dc6c1801400270791b06005270791b068180519c2286c18051124009c2286c180519c1e46c1805101670791b060124059c1b0601441c05a70771b060144169c1e46c18021016949c1e46c144169c1b0601442c05a70791b060164519c1e46c1805100a7c9c1e46c180519c1e46c1805105670791c86c180519c1e46c180510f670791b060144389c1e46c1805414670791b0601440d9c1e46c1805101ea09c1e46c180519c1e46f1b06014670791b0601441b9c1e46c1805112270791c86c18005a9270921b06014670921b060144169c1b0601745107270791b0601243d9c1e472180510f4009c1e4721803d9c1e46c180510bde46c1805d1442f001e46c180510be70791b06014404a2270791b06014688791b0601443d00288791b06014670791b0601443c9c1e46c180510a270791b0601742800270791b0600a270791b065180519c2206c180510f4009c2206c180519c1e46c1805105a70791b05d144169c1e46c180110168c9c1e46c180119c1b0601443204670791b0600c4119c1e46c1803d04670791b06009c119c1e46c1805614670791b060144019e270791b06014670791b060144109c1e46c1a86014670791b0601443a9c1e46c1805514670791b0601440f9c1e46c1805110670791b05e1441100270791b06010670791b0601440b9c1e46c1805814670791b0611441100270811b06014670791b060144369c1e46c1805102a70791b06014406a6270791b06014670791b067180519c1e46c1805102270791b060144199c1e4761b06014670791b060144459c1e46c1a860016a49c2346c180519c1e46c1a86004670992346c180519c2346c1805105a70791d4601443d9c2346c1805104670791b06a144369c1e46c1805109670791b06014403a1270791b06014670791b060144359c1e46c1805108a70791b0601440e9c1e46c1906014670791b060144349c1e46c1805104670791b06011c11,0x0)

def r5_0 : List Hint := [(0x5,0x5c02831006044068120821980900202c00406000),
  (0x3002074200415,0x5c028310060440682e0660240906802c19c1580a),
  (0x601c4d000611460143d00040d4400c1d,0x5002821006044128020260041201a08205800049),
  (0,0x50028210d01b004803022034358480d402405069),
  (0xc0081d,0x500282101c044128040660041206d02c1b400049),
  (0,0x5002831006044068280d40242f8680d80243700a),
  (0x380a0f4002435280a0b4402425300807420200d,0x500282101c044068040260040601608206800000),
  (0,0x68398710e41c4108700b6044128570b608c0086f),
  (0,0x500282100604412802046004378160d81b427049),
  (0,0x1e4300210f0044068780260040601a0ee1d83a874),
  (0xa02c1d,0x50028210080441700b0901ec0500d0f403400049),
  (0xf4c0301d,0x8028020060440682e0820240900b0001f43e016),
  (0x44650810154403c45100e0d440341d,0x50100110ac0d0158020260541501602c0680b041),
  (0x43d,0x10028010060040680b014024258450761140a87e),
  (0x12304004011,0x14020130720684080310009c1802e0fe02809012),
  (0xc04c0d,0x5c0283105c044048031020341580202c19c05049),
  (0x15344405081,0x68098830580c00080d08c2080687f02402804812),
  (0,0x5c0782101c0440083505a0341581a02602405069),
  (0x204815,0x500783101c0441482e00e01c1786d0d82004200a),
  (0x4411,0x504283400a0840a80305a0ac068020260540580c),
  (0x200415,0x980282f006208068021140244488808219c43886),
  (0x3017074205815,0x5c07831006044180040660200606802c06815815),
  (0x38192b40060a528192744060950815154c05415,0x981c8210341040d0240c2034460380260d84580c),
  (0x1b3746068d1101b2f48068b1,0x282082c0340841082b0060440680a00404c00869)]

def r5_1 : List Hint := [(0,0x981c82111a0440688d0260043481a06802432827),
  (0,0x5c02821018184068380260d80601a02a0543a874),
  (0,0x500282101c044128040460043786d0d81b427049),
  (0x1f0ecc07837301d07c807013,0x4a853128150498921222404788e),
  (0xc0081d,0x5c028310080441702e0660240906803419c00049),
  (0,0x50028210060b4068881300244b8020260244b00a),
  (0x10d4200415,0x5c0283101c04412802026024120680002640000a),
  (0x20231ec00307718220b8004c263021038008006,0x5005313e2784e89c0a226c2789a),
  (0x300c0d4200415,0x5c0283101c0441802e0660240906800019c0000a),
  (0x131d4600c3d3025074209015,0x5c028210060440682e082024090680260241580a),
  (0x60a44d00281140048351027074209815,0x5007831006044180020260bc0901a0000681580a),
  (0x200218400a821,0x500282c006044068680d8284370040460880602a),
  (0,0x500282c04001c12802046004378a41461b4270a2),
  (0,0x50028211100d00480305a0341580202602405069),
  (0x5435382e0b440b425302c07420ac15,0x5c0782101c044068230260d80601a00006815815),
  (0,0x1045384d14c1341887001a044068a50b60cc00812),
  (0x303007420bc15,0x5c0783101c044068620660040901a02c19c1580a),
  (0xe0207d,0x5c1802108c1840681a0201d83a85f02600406057),
  (0xc05,0x5c0283101c0441282e1142642700202c19c030a8),
  (0xc885003115480a825281c054000805,0x5c078310060441802a0f20681500202c0540a8a9),
  (0xe07415,0x5c02831006044068ac1560545500202c0040a80a),
  (0x38230b4802c05,0x140180d004008070170620441500b0fa1f005000),
  (0x332c4e07805,0x1041986615c1341881201a0440680a15a05800815),
  (0x81f154002005,0x5c0783101c0440681002c0040a81a066024090a9)]

def r5_2 : List Hint := [(0xd4b510340d4000015,0x500282c05600018002094004090030000340000c),
  (0,0x500282c04020812802094004120a40821b40a8a2),
  (0x2831138403846083102cc03807,0x500b41662784e8b2162270580af),
  (0x3a19440e44d0038114600c3d103707400d815,0x5007831006044180020260540901a0001381582a),
  (0,0x50078311480d0400a406816c1580202601c138b5),
  (0x8220b80034260022038203406,0x500531662784e89c0a226c2789a),
  (0x3e29400f48d003c21400ec6d0037194c04805,0x500282c0060540681a0820681580209400406000),
  (0xd1d420345538020f4c0081d,0x500282100604406868082024158680260240900a),
  (0x41084d18410f4010035303f0b441041d084005440fc0d,0x5002821006044068020260040600008200015800),
  (0x41188f204520c80c87b180f1dca0c84e100f118c1183f00450cc00c82b380f09cc0d41e103506cc110171044058410c15083202cc03c07,0x5005313e2784e8b812a2dc0a8b6),
  (0x4719441084d183c0f400e03530350b440f01d083805440d40d,0x5007831006044180020260540900008200015800),
  (0x8128b110462b48124a1004a104c1183d00490c4412015,0x68538a709a054188700e00441808d02a04c0a812),
  (0x4e194013445184c0f4012c35104c074212c15,0x500283100604418002026054090000820681580a),
  (0,0x5f89d17c240278bd1782ec5d0b9),
  (0x4f35480f4ad003929400f4592039154413415,0xb00a80d0820681584a0020300501400a00c00002),
  (0,0x402c02108c044068570260040601a0ee1d83a874),
  (0x41508f005320c01487b08111dc21484e0011118413c3e004e0ec41203700470d8410c35183e0b800e826105107c41401e103e03820e806,0x5009516e2784e8c2034304000c0),
  (0x104411441542d,0x50010130060440900b1880546181a0580000680a),
  (0x8158752057194a158550049114012805,0x5c0783101c0441800002a0540a80a0940000608b),
  (0x593740118b500540a4416015,0x700f00d0820c40001b0020300981a03205400018),
  (0xf440d01d,0xc0280d04000012802018004120560001580003b),
  (0x170d1105b204016875,0x682f05a0620c0038c50560541281302401800824),
  (0x305d0b4013811,0x5c0780718c0840a80e0220bc0681a0460001100c),
  (0,0x5c0283101c0441280400e0040306d0d81b437049)]

def r5_3 : List Hint := [(0x14861105f074217815,0x5c02862006044068040660880606802c19c158c7),
  (0x6184cd006031441709510611a4218065305c094014c11,0x5c0d041192084508200220ac068c802622c0d80c),
  (0x10622f4c1884d,0x1043982c0000141086b01a0440680019408c0080c),
  (0,0x5c08021040044068100460040601a0d8024370cb),
  (0x150a1,0x5c18821040078068130260040601a02a1d80a874),
  (0,0x500282c00601c06888146024370020d40243480a),
  (0x200415,0x5c028310060440682e00e0242f8680d819c4200a),
  (0xd065104213401344518030f40048351003074204815,0x5007831006044180020260540901a0820681580a),
  (0xd011,0x503406c00a0840a8030221ac068040460541100c),
  (0x1703528640b4418c250864034c18c05,0x500282104a04406804026004060410000680a80a),
  (0x188dd,0x682f0100e40c4160700b6208128cc02612800824),
  (0x41281d,0x500282c09a20812804094004120410821b4000a2),
  (0xc0fc6d,0x128668210180440681a0ee1343a88d02600406057),
  (0x15405,0x140f0400040040d8140580ac250560ac0541d800),
  (0x198d1006533461604d,0x680f81504a0c416024026128008000b610403806),
  (0x40fc05,0x5c0783101c0441801000e0681781a0463380608b),
  (0x6731401a0a520671d4017435,0x28150060542000202a0040d8560001580a83b),
  (0x65354018805,0x70000400360040d81a0320f00c0cf0ac0541d85e),
  (0x691d401a8650869154000005,0x5c0782101c0440680002a0540a8160260d806000),
  (0,0x5c0782101c0440681000e0041781a0d80243700a),
  (0x690ecc1ac37306707c815813,0x500b417e2784e8be1a2240680bd),
  (0x38080f4c1bc2d006e094c1b41d006c05401a40d,0x5c0782101c044068230260d80604e00006815800),
  (0,0x50028211101b00480d0c2034358ca0d80240506e),
  (0,0x5005317e2784e8be0a2240278bd)]

def r5_4 : List Hint := [(0x1c899006d25401c4690070194e05425,0x1881581500a0840d0030c20ac068020260000080c),
  (0,0x5c028210060440682e00e024370680d80243700a),
  (0x8761b841a86b087519c01d066086817c41cc53,0x6905317e0944e8be0a2240278bd),
  (0xc1d84d38700f401b835303f0b4c1c01d086e05401a80d,0x5c0782101c044068230260d80600008200015800),
  (0x8128911068064015c11,0x503406c042084698030221ac068680d80280d06e),
  (0,0x5005317e1444804f13c2745f0d4),
  (0x81c499006f25401c469206f194217025,0x1881581500a0840d002026028008030c20000680c),
  (0,0x500282104004436802026004660a40681b4158a2),
  (0x76294000035,0x108300c20ac068130240040604e00001401802),
  (0,0x5c1802108c184068120260040601a02a1d83a874),
  (0x307713441d025,0x4c0102101c0440680a1882846a80005806806815),
  (0x1e4b13078134c1ac253075054e1ac05,0x104098430361341080c084044068000340540a815),
  (0x4d,0x4c0102101c0440680000e004178000162843e016),
  (0x7a2c400004d,0x1083003c118068130240040600009c0646b018),
  (0x205415,0x5c07821074044128230460d83787a0d81b442049),
  (0,0x5c2603101a184068290660040908502c19c3a8a5),
  (0x4d384416815,0x2c1082303435c0300d0180444505b01401c0a82f),
  (0x7b3840194a9,0x7812821056104038240260040301a02a0c46c013),
  (0x107a23c81e48320331ec2050772833138005046307b0f8011436387d0b801f026306607801cc16307d03821f006,0x500db13e2784e8b81b426c6c89a),
  (0xc1ec8d30661b4016c65004d114e1fc3d007e0d4417025307f07421f815,0x5c0783101c04418013026054090dd0823701580a),
  (0x107a2f4c1884d,0x1046f84a00035c030de0180444500011a1280400c),
  (0,0x298e61ca144278e41c6388708e0),
  (0,0x3a41882c0523a012813094004120e70821b43a8a2),
  (0x61284d,0x3903100016c038cc026004030000bc1587503b)]

def r5_5 : List Hint := [(0x38080f4005435303f0b44170253008074205415,0x5c0782101c044068230260d80601a08206815815),
  (0,0x500282101a04406888068024328480260243480a),
  (0xe0203d3081074220015,0x5002831006044068280660240906802619c1580a),
  (0,0x5026821006044068680d80243700404602406015),
  (0xc0fc2d,0x500283100604418004046338060680d828437015),
  (0x10622f48128b1,0x1043982c0341341086b01a0440680a0b601c0082f),
  (0xc1dc05,0x840880d08006c0f01701e0380a80b1421f005000),
  (0xc1e005,0x7c0e02103c044068411d40646b01a0260d806000),
  (0x10831a4820861,0x502602101a184068850d80683702900e0041780a),
  (0,0x5c0782101c0440682300e004178eb0d80243700a),
  (0x418869,0xb00282101a044068880d8370370ca00e0041780a),
  (0x41084d,0x5c0282101c0440681000e0041780b0d80243700a),
  (0x59344010805,0x840f00d026004060e9060054090150623b0098dd)]

def c6 : Catalogue := (10,58,0x9c1e46c1805107270791b06014405a3270791b06014670791b060144499c1e46c1805105a70791c86c180519c1e46c180510f670791b060144119c1e46c1a86014670791b06014436,0x0)

def r6_0 : List Hint := [(0x300017820005b100a15c002856280913c00204b000711c00184338050fc00103b18030dc40083328050bc40102b200309c000823300107cc0001e080103c20000e,0x280298bf13c2744e05113813c378ed1dc3b427049),
  (0x28192fc0060bb00172dc0058b338152bc0050ab101329c6048a3281527c40509b001325c804893101122c204087080d1fc603073100f1ac203867080b17c20045e001112cc04047000f0ecc03837300d0bc803023300b07cc0041e300b03c202c0a100a00c002802,0x280298bf1ec3d47a0f31e43c4158911e023c050ef),
  (0x2f22c00b887382d1fc00b47e000b1d8000073002c1bc00ac63002a16c003c57382913c00a04b002711c00984308250dc002c3638240bc00542b202309c008823302107c00801e301f07400781b101d05c007016081b054001013081a03c00000e,0x280298b313c2745f0fb1f43e4578f802c3dc1580a),
  (0x410cdf204234c80accb080c31ca0ac9e000c258c10c8f004220c00ac7b280c1dcc0c06e10301ac8104670041198010065082b16c803057103f13c40f84e103d13400f04b003b11c00e846003911400e04318370fc60d83e18350f400883b08340dc00cc3600320d420083330310bcc0c02e103707c40d81e103507420881b003405c20cc160832054000813103103c40c00e,0x2806d89f13c2745c09516e0545b01a0820681580a),
  (0x4130df004b36c0128d7004934c6078cf004832c204cc7184730c8118bb10452dc41109f103127821206e101e1a8004c66104718801184b304511cc1102f30310b8c1101f10440688104130041048010011,0x2807c0ee1fe2fc0a89e13a3f85f0fd1200547e0bd),
  (0x593bc0160e3182c3388034c610572ec0158b708552bc0154ae004429800c0a3382c1f8003476185413c014c4b005211c01444310500dc011036284e0bc40542b204d09c801023104f07c00c01e084e03cc0540b004d01c001003,0x410298c22064085f05117013c5e9010823b40a900),
  (0x306823801688b006b21c01a88630581bc010863306913cc1a04e38610fce1803e385f0f400983b185e0dc017436005c0d420183330670bcc1982e30650b441442b206409c018c26106209400e023306107cc1801e305f07420981b105e05c217416085c054001813005b03c01680e,0x280828bf13c2745f0231203405e81a08206815815),
  (0x6c3bc016cee006f378e0a0da081735861b8d210772fc41d8be10752f4c14cba004a2d881d0b320732c881c8b110712b801c0a6086f238c0a08a001721841b882306d13cc1a44e306d0fc01b03a006b0cc01a832002e0ace04027105606cc11417082e02cc04007,0x1048590a0344245f8fe2102745f00a20e2dc830b6),
  (0x7f23c01f88e006c218016883002f1ec20447700571ac011867082f16c004457007d11c01b046387a0fc00a03b18790dc202033207c0bc414c2b207b09c00f023307a07c20a01b107905c002013007803c01680e,0x280828bf13c2745f10d16e4185b01a1dc3d08600a),
  (0x187f3ac61f8ea006d39c01a0e200842f801c4b600592a8010ca2187813c01a04e187d0dc01b43628810bc00642b208009c809823108307c01301b108205c014413088103c80640b008001c009803,0x4548a0bf2264485f11112013c5e81a02a4408790e)]

def c7 : Catalogue := (1,48,0x9c1e46c18051,0x0)

def r7_0 : List Hint := [(0x928060209c1807260601894100924080208c2007220801884180220080087c28011e0a0007408091c040206c10071a0401864080518000145c1004160400c54280214040084c2001120800044300910000203c00070e000183438020c000082c08010a0200024300508040141c0004060000c14300204020080c0001020000004,0x5005317e2784e8be0a2240278bd)]

end PEqualNP.Outside.L_meta_10590.Universal

namespace PEqualNP.Outside.L_meta_10590.Universal



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
  have p1 : ban c2 2 2 := more b1 p0 ok2_0
  exact p1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok3_0 : ck c2 c3 2 0 r3_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b3 : ban c3 3 c3.1 := by
  have p0 := empty c3 3
  have p1 : ban c3 3 22 := more b2 p0 ok3_0
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
theorem ok4_3 : ck c3 c4 3 72 r4_3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok4_4 : ck c3 c4 3 96 r4_4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok4_5 : ck c3 c4 3 120 r4_5 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4 : ban c4 4 c4.1 := by
  have p0 := empty c4 4
  have p1 : ban c4 4 24 := more b3 p0 ok4_0
  have p2 : ban c4 4 48 := more b3 p1 ok4_1
  have p3 : ban c4 4 72 := more b3 p2 ok4_2
  have p4 : ban c4 4 96 := more b3 p3 ok4_3
  have p5 : ban c4 4 120 := more b3 p4 ok4_4
  have p6 : ban c4 4 132 := more b3 p5 ok4_5
  exact p6

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
theorem b5 : ban c5 5 c5.1 := by
  have p0 := empty c5 5
  have p1 : ban c5 5 24 := more b4 p0 ok5_0
  have p2 : ban c5 5 48 := more b4 p1 ok5_1
  have p3 : ban c5 5 72 := more b4 p2 ok5_2
  have p4 : ban c5 5 96 := more b4 p3 ok5_3
  have p5 : ban c5 5 120 := more b4 p4 ok5_4
  have p6 : ban c5 5 133 := more b4 p5 ok5_5
  exact p6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok6_0 : ck c5 c6 5 0 r6_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b6 : ban c6 6 c6.1 := by
  have p0 := empty c6 6
  have p1 : ban c6 6 10 := more b5 p0 ok6_0
  exact p1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok7_0 : ck c6 c7 6 0 r7_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b7 : ban c7 7 c7.1 := by
  have p0 := empty c7 7
  have p1 : ban c7 7 1 := more b6 p0 ok7_0
  exact p1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower (k : ℕ) (run : build raw y k base.toFinset) : 8 ≤ k := by
  have denial := b7 0 (by decide +kernel)
  have eqBank : entryBank dict (rowAt c7 0 (0,0)) = base := by decide +kernel
  have eqDebts : entryDebts masks (rowAt c7 0 (0,0)) = ds := by decide +kernel
  rw [eqBank, eqDebts] at denial
  exact cert_lower (by decide +kernel) (by decide +kernel) (neg := neg) (by decide +kernel)
    (by simp [ds]) denial run

end PEqualNP.Outside.L_meta_10590.Universal

namespace PEqualNP.Outside.L_meta_10590.Six

def y : W := 0xfffffffefffeeca0

def base : List W := [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]

def neg : List (Fin 64) := [0,1,2,3,4,6,8,9,12,16,32]

def dict : ℕ := 0xffffffffffffffaaffffffffffffff00fffffffffffff0f0ffffffffffffeeeeffffffffffffccccffffffffffffaaaaffffffffffff0000ffffffffffaaffaaffffffffff00ff00ffffffffff00cc00fffffffff0f0f0f0ffffffffeeeeeeeeffffffffeeee0000ffffffffccccccccffffffffcccccc00ffffffffaaaaaaaaffffffff00ff00aaffffffff0000eeeeffffffff00000000ffffffaaffffffaaffffff00ffffff00ffffff00ffeeff22ffffff00ffaaff22ffffff00ffaaff00fffff0f0fffff0f0fffff0f0ff00f000ffffeeeeffffeeeeffffccccffffccccffffaaaaffffaaaaffffaaaaff00aa00ffffaaaacccc8888ffff00ffffff00f0ffff00ffffff00aaffff000ffff00000ffff000fff000000ffff0000ffffffaaffff0000ffffeeeeffff0000ffff0000ffff0000eeee2222ffff0000aaaa00aafffcfffcfffcccccfffafffafffaf0f0fff0fff0fff0fff0fff0fff0fff00000ffeeffeeffeeff00ffeeffeeffeeccccffaaffaaffaaffaaffaaffaaffaaff00ffaaffaaffaa0000ffaa0000ffaa00aaff0fff0fff0fff00ff00ff00ffffffaaff00ff00ff00ff00fefefefefefef0f0f0f0f0f0f0f0f0f0eeeeeeeeeeeeeeeeeeeeeeeeeeee0000cfcfcfcfcfcfccccccccccccffffeeeeccccccccccccccccccccccccccccccaaaaffaaffaaffaaeeaaffaaffaaffaaaaaaaaaaaaffffeeeeaaaaaaaaaaffaa00aaaaaaaaaaff0000aaaaaaaaaaaaccccaaaaaaaaaaaaaaaaaaaa8888bbbb888855555555555500005555550055555500333333333333330033333333222222220f0f0f0f0f0f0e0e0f0f0f0f0f0f0a0a0f0f0f0f0f0f000000ff00ff00ff00ee00ff00ff00ff00cc00ff00ff00ff00aa00ff00ff00ff000000ff00aa00ff00aa00ff00aa00aaaaaa00ff000f00ff000000ff000000ff00aa00ee00ee00ee00cc00cf00cf00cf00ce00cf00cf00cf00cc00aa00aa00ff00aa0033003300330000000f000f000ff0f0000f000f000f000a000f000f000f0000000f0000000ffff00000ffff0000aaaa0000eeee0000eeee000000ff0f0f0000000000ff000000cc000000aa555555aa00000000ffffeeee00000000ffffaaaa00000000eeeeeeee00000000aaffaaaa00000000aaaaeeee0000000000ff00cc0000000000ff00aa000000000000eeee

def masks : List W := [0x5555555555555555,0x3333333333333333,0xf0f0f0f0f0f0f0f,0xff00ff00ff00ff,0xffff0000ffff,0xffffffff,0x505050505050505,0x33003300330033]

def ds : Debts := [(0x5555555555555555,8),(0x3333333333333333,8),(0xf0f0f0f0f0f0f0f,8),(0xff00ff00ff00ff,8),(0xffff0000ffff,8),(0xffffffff,8),(0x505050505050505,7),(0x33003300330033,7)]

def syms : Array Sym := #[([],[]),([0x10,0xffff0000,0xffff00000000],[0x10,0xffff0000,0xffff00000000]),([0x6,0xcc00cc00cc00cc,0x3300330033003300],[0x6,0xcc00cc00cc00cc,0x3300330033003300]),([0x10,0xffff0000,0xffff00000000,0x6,0xcc00cc00cc00cc,0x3300330033003300],[0x10,0xffff0000,0xffff00000000,0x6,0xcc00cc00cc00cc,0x3300330033003300]),([0x4,0xf000f000f000f0,0xf000f000f000f00,0x1,0x2222222222222222,0x4444444444444444],[0x4,0xf000f000f000f0,0xf000f000f000f00,0x1,0x2222222222222222,0x4444444444444444]),([0x10,0xffff0000,0xffff00000000,0x4,0xf000f000f000f0,0xf000f000f000f00,0x1,0x2222222222222222,0x4444444444444444],[0x10,0xffff0000,0xffff00000000,0x4,0xf000f000f000f0,0xf000f000f000f00,0x1,0x2222222222222222,0x4444444444444444]),([0x7,0xaa00aa00aa00aa,0x5500550055005500,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050,0x1,0x2222222222222222,0x4444444444444444],[0x4,0xf000f000f000f0,0xf000f000f000f00,0x2,0xc0c0c0c0c0c0c0c,0x3030303030303030,0x1,0x2222222222222222,0x4444444444444444]),([0x10,0xffff0000,0xffff00000000,0x7,0xaa00aa00aa00aa,0x5500550055005500,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050,0x1,0x2222222222222222,0x4444444444444444],[0x10,0xffff0000,0xffff00000000,0x4,0xf000f000f000f0,0xf000f000f000f00,0x2,0xc0c0c0c0c0c0c0c,0x3030303030303030,0x1,0x2222222222222222,0x4444444444444444]),([0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050],[0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050]),([0x10,0xffff0000,0xffff00000000,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050],[0x10,0xffff0000,0xffff00000000,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050]),([0x6,0xcc00cc00cc00cc,0x3300330033003300,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050],[0x6,0xcc00cc00cc00cc,0x3300330033003300,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050]),([0x10,0xffff0000,0xffff00000000,0x6,0xcc00cc00cc00cc,0x3300330033003300,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050],[0x10,0xffff0000,0xffff00000000,0x6,0xcc00cc00cc00cc,0x3300330033003300,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050]),([0x4,0xf000f000f000f0,0xf000f000f000f00,0x2,0xc0c0c0c0c0c0c0c,0x3030303030303030,0x1,0x2222222222222222,0x4444444444444444],[0x7,0xaa00aa00aa00aa,0x5500550055005500,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050,0x1,0x2222222222222222,0x4444444444444444]),([0x10,0xffff0000,0xffff00000000,0x4,0xf000f000f000f0,0xf000f000f000f00,0x2,0xc0c0c0c0c0c0c0c,0x3030303030303030,0x1,0x2222222222222222,0x4444444444444444],[0x10,0xffff0000,0xffff00000000,0x7,0xaa00aa00aa00aa,0x5500550055005500,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050,0x1,0x2222222222222222,0x4444444444444444]),([0x2,0xc0c0c0c0c0c0c0c,0x3030303030303030,0x7,0xaa00aa00aa00aa,0x5500550055005500],[0x2,0xc0c0c0c0c0c0c0c,0x3030303030303030,0x7,0xaa00aa00aa00aa,0x5500550055005500]),([0x10,0xffff0000,0xffff00000000,0x2,0xc0c0c0c0c0c0c0c,0x3030303030303030,0x7,0xaa00aa00aa00aa,0x5500550055005500],[0x10,0xffff0000,0xffff00000000,0x2,0xc0c0c0c0c0c0c0c,0x3030303030303030,0x7,0xaa00aa00aa00aa,0x5500550055005500])]

def book : ℕ := 0x788c272442124c670842804816a8210a88468421784816a4210a4846842179846624c632442618c6810245a8842282159084790245a484224215908410842725c912449709c2084216a5a90a429685a170ca369c6319ca568c63318c662589324c96198669c67620e73a06361ce7210845a5692248959164714655a0a52a063594a5620e859508414e55a108808c272842128c67084281846628c632842618c6805217a8210a92978421741d0739ce741ce739ce73dcf739ce73dce739ce0b52908421085290b42122d29210842112922c84739ce73842738a5739ce739ce7384273863739ce739ce7bdef739ce739ce739ce84210739ce739ce739ce739ce739c9739ce6b52908421085296b4215ad2921084211295ac8410842125c912449109c2318c632589324c93198613863108421086313842330e7318c6318e7330c68421084042840c68421073863108421086373842630e7318c6318e7630c61084210dc310c43109c2318c631d8731cc731986842028421084210842101084270dc310c43709c28421084021840e784210318c661d8731cc7619868421084021840638421018ce3724631a4e770c634a52970d2948d237252939c67624e73a46361ce74a52961d2949d2762529924499192991842925295ad615ad6b5a9615ad6b785e17bdef78de37bdef641906318c6318c6318c73dcf739ce73dc7739ce5b96e5ad6b5b96b5ad6b84021084420842184042739ce5ad6b5ad6b5ad6b5ad6b5adef5adef5ad6b0c02108442084210c0425a5615ad6b5ad615ad6b5bd6f5ad6b5ad6b5ad6b8421084129842108421061d876318c6318c6318c595655ad6b5ad6b5ad6b641906318c6418c6318c0bc2108484084210bc84842108421084201842107bc2108484084217bc846318c5ad6b5ad6b5ad6b5ad6b5ad8c5ad8c5ad6b0c02108484084210c0845b16c5ad6b5ad6b5ad6b8402108484084218408490a4294a5292a4a94a52631866318c6318c6318c80cc318c6318cc680c63824294a5294a421825297bdef5ad6b5ad6b5ad6b7bdef7bde97bcc67bdef6b5ad6b5a66b5ad6b5ad0842d084210842108421739ce739c6739ce739ce5ad6b5ad6b5b8635ad6b8c6318c6318c4218c63194a52948c6948e794a525b96e5ad6b5b9635ad6b5ad605ad6b5a5695ad6b7c1f07bdef7bdef7bdef084210a5a90a429085a1601806318c625896318c2108422569224892116484210841298420a8421042108421094210942108739ce739c4739ce739ce739ce739c1739ce739ce18c6318c6318c6a18c634a5294a5294a5294a52c294a5294a5294a5294ab6318c6318c631826318c842108420a8421084210641906318c641836318c5ad6b5ad6b5c0215ad6b7bde07bdef785e17bdef5a9635ad6b5ad635ad6b5a9675ad6b5ad675ad6b63d8f6318c6318c6318c839ce84210842108421008421084260842108426210842108821088210848421084200840c6842108c6208c631886218c6310842108da308c23085a18421084042840a5842107bdef7bc427bca57bdef625836318c631836318c21084215652148521164842108404284063842107bdef7bc427bc637bdef6318c63125631856318c94a5292a4a94a5294a5294a529264994a5294a5218c63194211946318c236318c63182631226318c294a528c8328ca529485842108400084084842107bdef7bc007bc847bdef601806318c611846318c842108400084021842107bdef7bc007bc217bdef6318c63000630216318c68c63194211946368c23594a528c8328ca559485739ce73cc6739ce739ce739ce72d08739ce739ce002000000000000000007bdef7bcc67bd087bdef94a4294a5291a4294a5284210840c6840e7842107bdef7bcc67bce77bdef4a5294a4214a5294a4294a5294a4844a5294a489108c212442124c61084231846324c632442318c65a5635ad6b5ad635ad6b5a5675ad6b5ad675ad6b4a5294a4c64a5294a4c97a5297bdef7bdef7bdef739ce739d0739ce739ce5294a5294a5294a5294b39d073a4e73a50839ce718ca319c6319ca518c63420e842508424e742108294652a0a52a063294a57bdef7bd497bde97bdef4a42949129490214a529739ce74210739ce739ce5294a528215294a5282a5294a528845294a5288a08421084260842608421421094210842108421095ad6b5ad635ad6b5ad6b7bdef7bdeb7bdef7bdef642106318c6318c6318c5ad6b5bdef5ad6b5ad6b5c1705ad6b5c1635ad6b63def6318c6318c6318c4a5294a92a4a9294a529631826318c629826318c6298a6318c6318c6318c5ad615ad6b5a5615ad6b5a5695ad6b5ad6b5ad6b5b16c5ad6b5b16b5ad6b108501084210842108421084e108421084210842739ce739ca739ce739ce4a5294a5294a5294a53010847108421084710842739ce739cf739ce739ce7bdef7bdef7bde37bdef1084a108421084210842741d0739ce741ca739ce5a1615ad6b5a5615ad6b5c1705ad6b5c16b5ad6b842108420a8412984210842108425284242842107ad6b7bdef7bdef7bdef739c6739ce739ce739ce84210842108420a8421008422084210842a0842108427084210842108427739c8739ce739ce739ce739ce739c8739ce739ce739ce740c6739ce739ce109e21084210842108427bdef7bdef7a5c97bdef73dcf739ce73dc9739ce89e278c631886218c631739ce7392973842739ce72168739ce739ce739ce5b96e5ad6b5b9685ad6b210892108421084210848421084206842108421039cea39ce739ce739cea7bde57bdef7bdef7bdef5294a5294a5294a5294f18c6318c6a18c6318c630842408421084210842408422084210842108422631806318c61d876318c5a9615ad6b5ad615ad6b5b16c5ad6b5b1675ad6b5ad6b5ad6b5b18c5ad6b08426084210842608421108c212842128c610842799e67bdef7bde97bdef5ad625ad6b5a1685ad6b4a5294a4424a5294a4497bde97bdef785e17bdef108c210c4210cc3108425294a50d4a50d435294a7bdef7bc217bce77bdef3184631cc631c42318c65294a51d4a51d475294a7bdef7bc217bc637bdef4a44949929498424a5298c6318c4218c4638c6315ad6b5ad6b5bdef5ad6b584215ad6b5ad6b5ad6b18c6319c4219c6318c4339ce738cc338ce739cc77bdef739ce739ce739ce84210739ce739ce739ce842107bdef7bdef7bdef39d076a4e73a50869ce74a52969d2949d276a5295294a69d4a51d476a94a92a4a94a5291a4694a5291a4394a529224394a52420e85a508424e75a1084a5295a1294a1285a5295294a5a14a521485a94a8a42989129890218a52994a52948c5948e594a52799e67bdef785e17bdef741d0739ce741c7739ce84210842318422a8421084210840e784021842105b9ce5ad6b5ad6b5ad6b318c6318c6318c6318d039ce939ce739ce739ce7108421084e108421084221084210892108421089210842108a210842108a21084210842108521089741d0739ce741c6739ce73dcf739ce73dc6739ce6b9ae6b5ad6b9a56b5ad84210842528424584210739ce7398073842739ce6b5ad6b6526b6436b5ad7bdef7be317be277bdef739ce73a3173a23739ce4a5294a5294b9294a5294a5294a5294b5294a5298c6318c4848c5298c63139ce739ce939ce939ce7294a5294a9294a9294a5108421084910849108428420f8421084210842107c2107bdef7bdef7bdef83def84210842108421094a529484294a5294a528c6318c4218c6318c6315ad6b5b18c5ad6b5ad6b6318c62d6b6318c6318c5ad625ad6b5ad6b5ad6b08421084210842308432318c6318c9318c9318c6421084210b42108421082108f2108421084210847bdef7bdf07bdef7bdef7bdef7be527be467bdef63d8f6318c63d896318c5bd6f5ad6b5bd695ad6b08421084210bc21084217bdef7bdef7c1297bdef8298a8421084210842108296a842108421084210210902108421084210845294f5294a5294a5294a08421084240842908421084210842108421084300842108421084210842f10849108421084210849084210842208421084227bdef7bde07bc217bdef108421084a108421084a641906318c6418a6318c8421083d4a842108421094a529494a9484294a52842108314a84210842108421082d4a84210842101084a10842108421084a21204210842108421084211e421084210842108494a5294a5290a4294a52842108425284247842108c6318c631886218c6318421084231842258421061d826318c629826318c31986318c6318c6318c663d8f6318c63d8c6318c595615ad6b5a9615ad6b211242048420521210840018000000000000000061d826318c631826318c001600000000000000000842108484084210848159ce75ad6b5ad6b5ad6b001e000000000000000092a4294a5291a4294a525a1615ad6b5ad615ad6b10962108421084210842739ce73def739ce739ce6318a6318c6318c6318c1084210844108421084439ce739ce739ce739cec7c1f07bdef7c1ea7bdef7bdef7be527be477bdef842108408484042842107bdef7bd4a7bc217bdef63d8f6318c63d836318c94a52948429486394a528c6318c54a8c4218c6316318c63185630e56318c5ad6a5ad6b5ad6b5ad6b318c6318c6318c6318d24210842108421084210b08601084210842108421085e10842108421084218421084129840c6842107bdef7bd4a7bcc67bdef94a4394a5291a4394a527bde97bdef7a9e97bdef421084290a42908421087bdef7bd4a7bdef7bdef91a4694a529264994a529264394a5291a4394a525a1675ad6b5ad675ad6b5ad635ad6b5a1635ad6b5bd6f5ad6b5bd6b5ad6b108421084410849108420842108421084220842a5ad675ad6b5ad6b5ad6b1084210842108421084f631856318c6318c6318c842108408484129842108421084252842468421092a4a94a5290a4294a527bdef7be317be257bdef5c1705ad6b5c16a5ad6b5a96a5ad6b595655ad6b5bd6f5ad6b5bd635ad6b08421084210c021084215ace75ad6b5ad6b5ad6b7bdef7bde97bc427bdef62d6b6318c6318c6318c318c6318c6318c6318cf0842108421084230842a10a021084210842108428421084021840c6842107bde97bdef799e67bdef842108423184228842107bdef7be317be287bdef842108425284243842107bdef7be527be497bdef211242088420922210849264994a5290a4294a525c2105ad6b5ad6b5ad6b5282a5294a528215294a5ad675ad6b595655ad6b595615ad6b5ad615ad6b5b18c5ad6b5ad6b5ad6b1084210884108421088294a52949299484294a528c6318c5298c4218c631614a56318c6318c6318c84210840c68410884210791e47bdef7a1e87bdef7c1f07bdef7c1ef7bdef6b5ad6b5ad6b5ad6b5ad842108420a840c6842107bdef7bde97bc847bdef84210842528424a842107bdef7be527be457bdef8421084231842278421042028421084202142108785e17bdef7bde97bdef1082212842128211084272d6b739ce739ce739ce7bdef7bde97bc217bdef886218c6318aa2a8c6318aa2a8c631886218c6317bdef7be317be297bdef91a4294a5292a4294a527bdef7be527be437bdef9264294a5291a4294a5218c6318c4218c6318c4358c635ad6b5ad6b5ad6b5ad6b5ad6b5b9ce5ad6b94a52948c39492394a52084210842d08421084216b5ae6b5ad6b5ad6b5ad6b5ad6b5a06b5ad6b5ad6318c6318c631836318c6c1b06b5ad6c1a46b5ad6bdaf6b5ad6bda46b5ad6358d6318c635836318c842108423184221842107bdef7be317be217bdef6b5ad6b5606b4216b5ad6318c63231632216318c842108400084042842107bdef7bc007bc427bdef6318c6318c614636318c8c6318c4838c4a38c6317bdef7bdef7bdef7bdef4a5254a5294a5294a5296318f6318c6318c6318c8c6298c6318c6318c63118c6318c6318c6418c635ad6b5ad6b5ad625ad6b084230842108423084216318c631856318c6318c00000000010000100000631826318c6318c6318c5ad645ad6b5ad6b5ad6b4a5294a5294a5294a5245ad6c5ad6b5ad6b5ad6b8c6318c6318c6318c6318420e8421084210842104a5294a5294a5294a5210842108421084210842939ce739ce739ce739ce294a5294a4094a5294a52294a5294a3294a5294a5739ce739c7739ce739ce5ad6e5ad6b5ad6b5ad6b318c6318c4318c6318c618c6318c6118c6318c635ad705ad6b5ad6b5ad6b4a5294a52f4a5294a52f4a5294a5294a5294a52b739ce739ce739c3739ce4a5224a5294a5294a5294a52a4a5294a5294a529318c6318cc318c9318c65ac635ad6b5ad6b5ad6b90a4294a529264994a5290a4294a5290e4394a52886218c63188e238c631619826318c625826318c842108318c8421084210649826318c649826318c591615ad6b5a5615ad6b7bdef7ad6b7bdef7bdef5c9725ad6b5c9635ad6b4a5294a5294a5294a52a739ce739c0739ce739ce8c6218c6318c6318c6315ad6b5ad6b5ad675ad6b5ad6b5ad6b5ad695ad6b318c7318c6318c7318c67bdef7bde87bdef7bdef10849108421084210842631816318c6318c6318c5ad6b5ad625ad6b5ad6b10842108431084310842842108420784210842107bdef7bde57bdef7bdef739d0739ce739ce739ce4a5294a5284a5294a5297bde47bdef7bdef7bdef0000000007000070000094a5294a4394a5294a5200002000000000200000084210842308423084212108421085210852108410842108521084210842084230842108421084237bdef7bdef7bde77bdef0842108424084210842418c6318c6418c6318c63631906318c6318c6318c5ad6b5ad6b5ad615ad6b842108420184210842100842a0842108421084210842308421084210842118c6318c6318c6718c63421084210a42108421088421084202842108421018c6318c6318c6318c665294a529435294a5294a6318c6318c6318c6318c18c6318c6718c6318c63529475294a5294a5294a7bde07bdef7bdef7bdef0842108421084210842b42108421064210842108108421084510845108427bde27bdef7bdef7bdef5294a5294a529475294a18c6318c6318c6318c6739ce739ce639ce739ce77bde87bdef7bdef7bdef08427084210842708421108421084a1084a10842318c6318c7318c7318c65ad615ad6b5ad6b5ad6b084210842708421084275bdef5ad6b5ad6b5ad6b709c2739ce729ca739ce739ce73a3173a25739ce91a4694a5291e4794a52739ce7394a73842739ce5ac215ad6b5ad6b5ad6b18c6318c631b86318c6394a52948c69492994a521084310842108431084239ce739ce139ce739ce77bde37bdef7bdef7bdef08421084270842708421318ca318c6318c6318ca18c6918c6318c6318c6318c6318c6318c6318c6a6b5ad6b5a26b5ad6b5ad10842108421084210852842108421084209842107bdef7bdef7bde17bdef84210842098421084210000000000900009000002108421089210892108494a4294a5294a5294a52318c6318cc318c6318c6318c6318c9318c6318c6318c6318ca318c6318c6210842108b21084210842108421089210842108494a5294a4994a5294a52108421084910842108495ad665ad6b5ad6b5ad6b631846318c6318c6318c7bde77bdef7bdef7bdef842078421084210842105ad6b5ad6c5ad6b5ad6b6318c6318b6318c6318c8421084084840c6842107bdef7bc847bcc67bdef641906318c641856318c63d8f6318c63d856318c631826318c619826318c5c1705ad6b5c1675ad6b5bd6f5ad6b5bd675ad6b94a5292d6b94a5294a5239ce739cea39ce739ce75ad655ad6b5ad6b5ad6b4a5294a5294a52e4a529739c1739ce739ce739ce2108621084210842109142108421084210a4210810852108421084210842084310842108421084215ad6b5ad695ad6b5ad6b6318c631896318c6318c94a5294a4294a5294a520842908422084210842184201842108421084210318c9318c6318c9318c62108921084210892108408421084210843008421084210842a0842a084217bdef7bdef7bdea7bdef318c6318ca318ca318c6210842108a2108a210847bdef7bde47bdef7bdef8421084204842108421018c6318c6a18c6a18c63739c2739ce739ce739ce084230842908421084217bdf07bdef7bdef7bdef00001000000000100000084210842108421084317c1f07bdef7c1e97bdef842108423184224842107bdef7be317be247bdef641906318c641826318c63d8f6318c63d826318c645916318c645836318c5c1705ad6b5c1615ad6b5bd6f5ad6b5bd615ad6b5b16c5ad6b5b1655ad6b94a529280094a5294a5294a529240094a5294a528c6318c4e78c4218c6316318c63000631296318c94a5290c8394a5294a5284210842108421084210084290842108421084240842508421084210842108422084210842108421108411084210842108425294a529425294a5294a294a5294a5294a7294a508421084210842108422318c6318c1318c6318c6318c6318c7318c6318c6739ce739c2739ce739ce08429084210842108422529435294a5294a5294a0842708421084210842108423084320842108421294a5294a5294a1294a50000000000000020000a7bdef7bdef7bde97bdef8420a84210842108421039ce739ce939ce739ce75ad605ad6b5ad6b5ad6b739ce739ce739ce739ce39ce739ce439ce739ce739ce739ce739ce739cea084210842108422084294a5294a52f4a5294a52939ce739ce739ce739ce9084210842a08421084215294a529505294a5294a5294a529465294a5294a5294a5294a529505294a5294a5294a5294e5294a4210842102421084210818c6318c6318c6618c63318c6318c6318d0318c6318c9318c6318c6318c610848108421084210842294a5294a7294a5294a539ce939ce739ce939ce76b5a26b5ad6b5ad6b5ad421084210942108421082108421084210852109239ce739ce739cea39ce7529415294a5294a5294a529465294a5294a5294a529445294a5294a5294a10842108421084a108425ad6b5ad6b5ad635ad6b7bdef7bde27bdef7bdef7bde97bdef7bdef7bdef318c9318c6318c6318c9108421084a10842108427bdef7a5e97bdef7bdef74210739ce739ce739ce7bd297bdef7bdef7bdef886218c6318a6298c6318a6298c631886218c631886218c63189e278c63191a4394a529264394a5292a4394a5291a4394a528c6318c6528c6438c6315a1615ad6b5a9615ad6b211642108421084210845a9635ad6b5a1635ad6b5c5615ad6b5c5615ad6b5c9725ad6b5c9675ad6b084210842a084210842218c6618c6318c6318c63294a5294a5294a5294aa210852108421084210844210842108421084210a318c8318c6318c6318c6318ca318c6318c6318c65294a5294a529465294a318c7318c6318c6318c6294a5294a9294a5294a521084210842108521086294a529ca729ca5294a5294a52a4a92a4a5294a56c2106b5ad6b5ad6b5ad73def739ce739ce739ce91a4594a529264594a529264594a5291a4594a5291a4694a529224894a529264994a5291a4694a52892248c6318a6298c631892248c6318a2288c6318aa2a8c631892248c6318a6298c631892248c6318ca328c6318ca258c6315294a5294a529455294a0842108421084210842a084210842a084210842a0842608421084210843108421084210842a084214210842108421014210808429084210842108429631806318c6318c6318c0842a0842208421084215294a529475294a5294a084210842108421084230842a08421084210842a08429084230842108421318c6318c6318c6318c6294a5294a5294a5294a721084210882108421084294a5294aa294a5294a5529425294a5294a5294a318c6318c6318c8318c62108521089210842108421089210842108421089210882108421084210846318c6318c6318f6318c5294a529405294a5294a0000000000000010000a108421084210842108495294a529445294a5294a18c6318c6318c6918c6339ce739ce039ce739ce7000090000000009000001084210842108421084121084210842108a210845ad635ad6b5ad6b5ad6b4a5294a52a4a5294a529084290842108429084215294a529495294a5294a4a5294a5294a5234a5294a5294a5294a5304a52918c6318c6018c6318c634a5204a5294a5294a5294a5294a5294a5294a5224a5294a5294a5274a5294a5294a5294a52f4a52918c6318c6618c6318c63210842108021084210847bde17bdef7bdef7bdef4a5294a5294a5244a5295294a5294a529445294a94a5294a5294a5294a524a5294a5254a5294a5295294a529455294a5294a5ad6b5ad6b5ad6b5ad6b4a5244a5294a5294a529294a5294a5294a3294a51084210842108451084239ce739ce739ce139ce75ad6f5ad6b5ad6b5ad6b4a5294a5274a5294a529318c6318c6318c3318c618c6318c6318c6318c610000000000000030000010842108441084210842108421084310842108420000000000000020000942108421084210942108318c6318c6318ca318c64a5294a5294a5284a5295294a5294a529485294a00000000000000600000000000000000005000004a5294a5204a5294a5290000000000000020000008421084210842108425108421084210849108421084910842108491084208421084290842908421210842108a210842108400000000000000100009294a5294a4294a5294a52108721084210872108408421084290842108429084210842108427084214a5294a5294a5264a52918c6318c6818c6318c6339ce739ce739ce939ce700000000000000200012421084210842108421085294a5294a529435294a210842108421083210841084210842108421084218c6318c6218c6318c63084210842108428084215294a5294a529425294a5294a5294a5294a5294a10840108421084210842294a7294a5294a5294a51084210842108421084439ce739ce739ce739ce718c6318c6318c6518c6339ce739ce739ce439ce74a5294a5294a5254a529294a6294a5294a5294a521084210842108821084294a5294a5294a5294a55294a529415294a5294a210842108421084210844a5294a5294a52a4a5295294a5294a529495294a1084210842108441084221084210842108621084318c6318c6318c4318c64a5294a5294a5294a529318c5318c6318c6318c621087210842108421084294a5294a1294a5294a50842108429084210842139ce739ce239ce739ce710842108401084210842108421084910842108421084210845108421084218c6318c6318c6318c6921084210842108221084318c6318c6318c1318c610842108411084210842084210842508421084214a5294a5264a5294a52918c6318c6318c6318c6810842108421084810842318c6318c6318c7318c60842108422084210842118c6318c6318c6318c634a5294a5224a5294a529084210842708421084214a5294a5234a5294a52918c6318c6918c6318c63084200842108421084212108421084210812108418c6318c6318c6318c620842108426084210842108421084230842108421000000000000009000000000000000000040000000000000000000100000084210842108429084214a5294a5214a5294a5294a5294a5244a5294a52908421084200842108421084210842408421084211084210842108461084239ce739ce739ce839ce794a4094a5294a5294a52318c6318c6318c9318c64210842108421074210808421084210842108421294a5294a5294a8294a5421084210842105421080000000000000010001121084210842108921084084210842108426084210842108421084240842108421084210842208421108421084210841108424a5294a5294a5214a5291084210842108471084208421084210842508421318c6318c6318c5318c64a5294a5294a5224a5290842108421084230842121084210842108721084108421084210843108425294a5294a529415294a2108421084210852108400000000000000000000

def ck (p c : Catalogue) (k start : ℕ) (hs : List Hint) : Bool :=
  auditRows (checkEntry y neg dict masks syms book p k) c start hs

def c0 : Catalogue := (0,1,0x0,0x0)

def c1 : Catalogue := (0,1,0x0,0x0)

def c2 : Catalogue := (0,1,0x0,0x0)

def c3 : Catalogue := (0,1,0x0,0x0)

def c4 : Catalogue := (8,47,0xb8228681382590540d02f09f20aa1a05e13e40d8340bc19d23008a2104fa0621144209f20a61a05e13e41885210827,0x4143423232443233324432332344322443434432434344323244422343444432)

def r4_0 : List Hint := [(0,0x480801001c0300500800c01001),
  (0,0x700d0100300300501600c05001),
  (0,0x40130240140301102000c07801),
  (0,0x401302e058028150060280a001),
  (0,0xc00d0100300300501600c05001),
  (0,0xd00d0160300500503400c05019),
  (0,0xd00d0160300500503400c05019),
  (0,0x1001f03e0780f00a03a0740e01b)]

def c5 : Catalogue := (58,57,0x320681784e0500760450bc270801dba228681382401d8148450bc2705330681784e0500784450d02f09c1dcc228681382401d81142f09c20056c08a1784e1083b60450d8340b827d02c08a1784e0a64158340bc2704f20861b0681784f90560d02f09c05c83008a1784e0a640d8340bc2702f20981b0681784f90370d02f09c1ab02a88a1a05e13e4110360d02f09ec08a1b06817813905b158340bc1ac8300a41784e0ee4158340bc2909f209e1b0681384d90560d02f09c02ba2786c1a04e00d8114340bc2707ac08a1f06a1784f60450f43409c16b02286c1784e08e9160451042f09f48b02287a1a04f60450f8340bc27b01b0681784e07581142f09c2107af08a1b0681784f60450ec340bc27c83108a2085e13e4188450f43409ee88a1f0681984f90560f0340bc07d23008a1f85e13e416c3c0d02f06ac0a6228681784f90570d02f09c02c82d8ae1a05e0d5f13c360d027006c89e1b0681380d9052144400bc27c8310a41784e07e4188520fc2f09f10a42007e1784f744e0d83403006ba2706c1a06600e40f0340bc1a01f209c1e0681780568450f0340bc07,0x42554343444444445254435344444543425543434254434352544353444444444444444443444344444445434355533433554334435553344454454333554433335533444355533443444344335533443444433544555335445545434355533443553354435553344355335443444344444444445344534434444533444454345344534443444344334544334444444433543344434453344454543453545344535443544455533544545533445553354344533443555334445553354355335443553354445555334455553344555533445555334455335544553355445553354455533544545335)

def r5_0 : List Hint := [(0,0x940182604a0740582400a0180282304402c11021),
  (0,0x2c0582d01a0080580c0580180282b0540a414027),
  (0,0x2c0680b0180180281a0520a00102b05a0bc1602e),
  (0,0x41980300a0c8040040020180502b0620a01802a),
  (0,0x41980300a0c80401a0740a01c83806e0d81a834),
  (0,0x202000807e0f81e80c0180f00080b0160ec02001),
  (0x154a00015,0x24040080861082080700c0141e8040060081e801),
  (0,0x600680800201802804006008008450521101781b),
  (0,0x342304b01a1282400c0921200300b08e11801801),
  (0,0x902703309c0140404e09a00c0104c0340a018031),
  (0,0x10198330640140400009a00c010450560a018031),
  (0,0x1480582d0a2028058050581400282205c13c14027),
  (0x20043d,0x2c0680b018140028520a60281602b0000a01382e),
  (0x4d5,0x382981801a0202000c00c0cc0280b00615001001),
  (0,0xc80d02d0a2028058050581400282b05c15414002),
  (0x3154800815,0x200981708605c2c05700a0542b0030140502b001),
  (0,0x600c05508016c050330aa168028320b206c1782c),
  (0,0x3c1981800a0f8040070bc0d82e04d0ba00c2e043),
  (0x4002115000025,0xb42986202a01820861010104028560061800085f),
  (0x6003115a00025,0xb42986202e0202081500c1040285600618005001),
  (0,0x18c0c01808010004033066018028540a800c2f801),
  (0,0x740703f01a0f80400c00e1400280b00800c01001),
  (0,0x803286503c0783381e03c0783301e03c19832864),
  (0,0x1a00f8670181943280b03c0780080d01a0340600b)]

def r5_1 : List Hint := [(0,0x3c0c01807c0f80400700e0180280400800c2f801),
  (0x40030d5200c25,0x14c2986c02c1ac0a8080d41a4028030ac1580085f),
  (0x60020d5a00825,0x14c2986c01005c0b8570d6054028030ac15805001),
  (0,0x80340680ca1943681e03c00c0080d01a02002866),
  (0,0x18c32865080100380030060782f86f0de0f41886e),
  (0,0x3c1f83f07c0f80400700e1b40280400800c2f801),
  (0,0x800f81f0ca1943801e03c0283381a0340c03306e),
  (0,0x3c198330e41c80400100200c050710e20d81a86e),
  (0,0x60200760661400280905a028160750e81cc1781b),
  (0,0xcc0705001a1c804024022150050770960a40e01b),
  (0x1c0107d,0x6020008066140028130f20701785400602800878),
  (0,0x2004007f0021f83e80f0fc1f40f07c0f61e83306e),
  (0,0xc80702d0a20283b005058140028810361543982f),
  (0,0x800c06801a07c2000c0ca0cc0280b01600c33001),
  (0x14c5,0x680703d01a0280400c1060183901a10400c05007),
  (0x14d5,0x680980b01a02c0680c0140200281a00606401019),
  (0,0x680680b0182140285205a0281601a1080a01382e),
  (0,0x140708801a2200408610e0183908610415005011),
  (0,0x1a00f8080ca0180281e006028008130520701781b),
  (0,0x340008a0021c02080f0141040f05e0622243306e),
  (0,0x6020008066140028090aa0284183811822c1781b),
  (0x401875,0x680708801a0283b00c07a0180281a1040b40502c),
  (0,0x38068760181400283205a028160750e81cc1781b),
  (0,0xf0e00040081011a03c0f0310bc1783306e)]

def r5_2 : List Hint := [(0,0x740700e01a0342d81a0340281901a0340640502c),
  (0,0x803286503c0780f01e03c078330650ca1981b88e),
  (0,0x803286503c0783281e03c2404781a0341981b87c),
  (0x401c4d,0x3807603c00c050131220700d80006c0c437026),
  (0x401c19,0x800f8760ca0984401e0060282400c08811027892),
  (0,0x1c00008803c028240130620d0370130620d037093),
  (0,0x7c078000ca1c00081e12803c0f00c0621783306e),
  (0,0x1943801f03c0780507c12a1104907c06e0c43707c),
  (0,0x803286503c0780f01e03c068330650ca1981b871),
  (0,0x7c1007003c0280f00c0882544900c0381980d896)]

def c6 : Catalogue := (176,67,0xc82286c1a05e1380b9058114340bc27052c08a1c0681784e0dd8114340bc2707c14b0228681885e138280058114340bc27053206c1a05e1381a03e4114360d02f0ac27c82286c1784e1000f90450d02f09c1d00ec08a1b05e138400dd8114360d02f0a027ca2c08a1a05e1383b90450d8340bc2501ee88a1b0681784e0258158450d02f09c139c1b0681784e0680f6c450d82f09c2001ee88a1a05e1383a01d813c450d02707412b62286c1a05e1280f60561143409c2306e708a1b0681784a03d8158450d02f0b027ca1b0681784e0680f94450d82f09c2001f308a1a05e1383a01e6160450d02707412b02286c1784e1002160450d02f0b427076c08a1b05e138400e65160450d02f09c1ecc2c08a1a05e1383d9c58114340bc2707748b0228681784e0e65114360d02f09407d22c08a1a04e11837a458114340bc2c09f209e1b0681785613e4114360d02f09c02c82786c1a05e1380f905b114340bc2707720c4228681784e0e64138360d02f09407c83108a1a05e1604f885a114360d02f09f10b02286e1a05e13e41384c0d8340bc2700320981b0681784f9062138340bc2706ec08a1b05e138400d58114360d02f0a827c81b0681784e0d00f904e0d8340bc2700ac0982286c1a05e13da114360d02f09c07c42c08a1a05e1383190450d8340bc2909f206c1a05e138340158114370d02f09c1ab02286e1a05e1380568450d8340bc2700ac08a1b0681784e015b114360d02f09c08b02708a1a05e1383d604f114340bc2707ac0ac228681784e0e58114440d8340bc27ca2286c1a05e138116050114340bc27077209c1b0681784e0464140360d02f09c07b62286c1a05e138036c46114360d02f09ec0ae2688a1a05e13e418857138340bc27b62788a1b0681380d6c450d83409c2201ae88a1b068138440364160560d02f09c1ab62c0ac2286817835604e114340bc2406b10b02508a1a05e13db138360d02f03407c8300a41b05e138379464188560d02f09ed88a1b0681783403e416c4e0d8340bc1a00320b61b06817835604f114360d02709ac0ac228681784e015d13c450d83409c08b62808a1b0681780f906215c560d02f09ee89e2286c1a04e0358114400e0340bc27b0228701a05e1381f9c58114360d02f09f20b22286c1a05e13e4114360d02f09c08c82c08a1a05e1383d90581143e0d02f09ec08a1f0681985e13d8114360d02f09c01b02287c1a0641784e00581143e0d02f09f208a1b0681985e03e9160450e8340bc27d2340b0228801784f60450d8340c82f09ec08a1e0681784e0bd9114360d02f09c06b22286c1a05e1380360450d0330bc2707ac08a1b0681784e07d81143c0d02f09c1cbe2286c1a0641784f6049114360d02f09f20be2806c1a05e13d81143c0d02f0901ac82c0781a05e1383514360d03309c2201ac094228781a05e13df114360d02f09c08b02808a1a05e1383d6057114340bc27073388a1b0681784e0467160450d02f09c1e002c08a1a05e1383da858114340bc2707320a01b0681784e045f114360d02f09c01be2308a1b0681784f905815c340bc2706af88a1b06813844035815c450d02f0901ac62c094228681784f60450f0390d02f09ec08a1e0681780e015b114360d0330bc07b02b08a1a05e1381f604f114340cc27076c09c228781a05e0e65114360d0330bc07d22c08a1a05e1381f9858114340cc2707728b0228781a05e0e64138360d0330bc07c83108a1a05e1381f90621143a0d02f09f108a1e0741a05e13e919060114400bc27c42c090228681784f604f0d83409c06006c08a1e0681784e015d114360d03309c08c8318ac1e0681784f6c581143c0d02f06af89e2286c1a04e035815c450d02f09c02ba2808a1b06813810006418c560d02f09ed8b02b88a1a05e0d5d114360d02703006ba2808a1b0681380d74450d8340cc27007108e228781a05e13d814851114400bc2700320c4290801784f744e114360d03301ac08a1e0681783403e5160450f0340bc1ac82c09c1e068178356c450d8340cc2201ac09c228781a05e01601604b114400bc27,0x4465544554555554545565445455555454555554545555543466444544654455356545455365545445555545445544555455545535654446446544555455644534664445356545455365545463555464356544466355645435654446545564453466444535654545536554546355546445555545545554554555554554555455545554555455545554556445356544466355645454556445446644554465544544664455546554555465644535664446546564454465544554556445446644554466445554666445455555454455544544665445446654454455445544655445545565444465544544665445545564455455644544655445445554454465445554555455545554555455644544554455446544555455545544664455446644554465445544654455545564455466644554654465546444655464446554566445555564465545644654556445356644464566564454666445456554464566544645665446545544655455644554654465456544565466644554654465545565445455654444554455446544554465445554555455545554555455545544554455545554555455545545654456545564455555664444554455545564454465445544654455545554554455554454556445446544554455554444664455554564465456644554644465545564454465445554555455545564454465445554555455545554555455644544664455446544554465445554566445546444655545644654556445545564455555644645654456545565446455546555556446456544565455654464555465555564464566445654656544546564455465644555656644545565445456446554556445546544655466644555556446546544655455644554654465546664455555644654654465546544655465446554656445555566445566664455654466555564465555644655566446556444665555644655556644)

def r6_0 : List Hint := [(0x120011d,0x9f13c2742188d0260244e09b0fa268008990020184c08d12e03c01801),
  (0x535,0x2c09627c0c02d04c1005081d0160cc1600500c0140982a0500a4140a0),
  (0,0xb0060385300d0102940105000410c158a404228c1d0190500e44f8a2),
  (0x24a4000449,0x1314e1b01304205a074210a10160142102c00c014140910540a4140a0),
  (0,0x5313e0741680a04c2a45401d0160b00280500c014150280500a4140a0),
  (0x25140000a5,0x9f0300982001d0160cc0280600a27c14029050280098a705a2a81602e),
  (0x4224000c39,0x4d00a14c198030b60145081d010010560ab0a00081c06e0540d81a845),
  (0x380133d0004ca280830c0020c200072fd400cba00062cc0014b2,0x2d85b8b91702dc5b0b51682cc590b11602bc570ad),
  (0x2115,0x3a02412c2b01308c03825048176030248ba0020180584708c03c01801),
  (0x6024f9,0x5201c14c018c013e0345f8510040cc5f00517a014290bc0640f42e02c),
  (0x80a354000c95,0xf0660fc0283e01001027850004134608030b80f41c01306c0d42286e),
  (0x202839,0x401810c198500b6014010080101342780b0061701c0450a60d81a86e),
  (0x4354202445,0xf0660fc0283e010134278030b8010098500042b01c04f06c0d4370c2),
  (0x2d05,0x5305a310618130000285400b0a20b00285000a0141702809e08814027),
  (0x4028ea080c33de02c3f,0x348688d019e338668cc16432c650c919031c630c5),
  (0x202839,0x401813c198500b6014010080101342780b0060281c0450a634c1a86e),
  (0xc4d420344d,0x1813e0002000b0a20cc2800500a0b0298810140b0098000440a01382e),
  (0x2839,0x405204c198500c60c802876010000268030060081e82b0a60a018031),
  (0x3925,0x5306404c168c4016298540510160b0028050a001417028056154140a0),
  (0x100a465e0384d,0xd601c3544f83d0aa1440505b14c0142d0551a8014190000b213c2e02c),
  (0,0xc06616c0280801001001050004134058030b80f41c06f1a60d46106e),
  (0,0xd803002c200510160cc0285000a0b0190530b80b00982b1ae0a05002e),
  (0xa294002455,0xf07e0cc1f00501023426803004000020060141200003806c0d437045),
  (0,0x7a370048db1b60204d0db01a1b4358da0180140182c1b202c05001)]

def r6_1 : List Hint := [(0x3810474003cd1,0x431c205c0009f1c037c6f0830823743609a0821682306c0fc1043f001),
  (0x10111d5001445,0x63006398728e409e034200a61340cc198e313e014290e20860b02e02c),
  (0x132d4004875600f155001835,0x2d0a61884f8421d01840404109e0540304109e0142b0030c039c2f801),
  (0x1cf5,0x180861884d0081d60540304100a0b0018410be004258291d40f474892),
  (0x1002274400409,0xb01c154068020103c020806014030778ee00a27c1584505222c768ec),
  (0,0x9f13e0741682604c2a45401d0160b00280500c014150280500a4140a0),
  (0,0x18c028760ec3c85d8bb0140c0018030b810c788d306c0c41486e),
  (0x100505d,0x540409a13415c3581500a00c1602c0be004000580b00f41781b),
  (0,0x616c0581d0100cc798060141bc028ee00a27c228390563ac76021),
  (0,0x3203a27c0582d04c1445081d0160141600500c0141582e0500a4140a0),
  (0,0xc0c60000f8050ec028790bb01402c180030b810c060f406c0c41486e),
  (0,0x1802a000068081340047b01500a0100182c0be0040e0f50b00f41781b),
  (0,0xb00616c0581d0100cc010500041bc028ee00a27c7b82b0563ac77821),
  (0x55,0xd80300982001d0160cc0280600a12c5382d1540b0000280520a05002a),
  (0,0x1d03002c2905207a1000680b1f20cc060501f00141602b0a60b82e02c),
  (0,0x1f80887d8a80a602c288f903a018028fa00a0142988105c3ac0102c),
  (0,0xb03a0000680b0a20301980500a3f8298e50383f4158430440a013859),
  (0,0x1e0ca0380f00d0100000580300410c159010424004f8190500c0188ff),
  (0xb254003049,0x1301626c288420160142105000a2041e8530140b01103d09e0a01382e),
  (0,0xd520a10c198f90b60c8820080100008180c0a00140010205600c0104d),
  (0x28d5200a25400545d,0xf0660fc1903e0100002785000a00027803004134000130500c015831),
  (0x100c065803009,0x2401c140068020100302780600a02c278030141340c90611622c1e83d),
  (0,0x74058510a215c0280500a14c408810140b0788220440a01382e),
  (0,0x450899122224408790e21a3188610b21442484107)]

def r6_2 : List Hint := [(0x591d,0x748a8080100000600c00a10c0580b014134788280500c01486e),
  (0,0x6616c190080100000600600a00005803014134830390500c015831),
  (0,0xb03a0002880b0a20147b00500a0c8298810140b0158fc0440a01382e),
  (0,0x11603a0000f8a10100300000c00a02c2180b0141340d0f40500c01486e),
  (0,0x2406616c190080100000605000a000058030041348b8190500c015831),
  (0,0x2b03a14c059190041447c81d0160148c00500c0141902e1d614c2e02c),
  (0,0xe01a0200f06503c02c0185c0000681201a0084000c82806027c188ff),
  (0x3895,0x1301626c288420160142105000a0c86f0530b80b01591a0aa0a00102e),
  (0,0x1d01602c068510160300283300a3f87f0791143f4158220f20a050079),
  (0,0x11c2363542d8060a0020050020100301e84f1dc0141583d09e00c2e04d),
  (0,0x7f24046c0c11f0120348f8080100048f00c0da0140211d01600c2f801),
  (0x1605ced,0xf0660fc1903e0100009085b01027c2f031018030218f00160ac0584d),
  (0,0x1d01602c288510160140286d00a0c8190530b80b01582b1ae0a05002e),
  (0,0xf0300600680d0100040086d00a010020030be0043f92407a0f491922),
  (0,0x2003e07c8b1160b80300600500002c0585c0861340d01a0604989286e),
  (0,0xf0660fc1903e0100100780600a00407803014134830130500c015831),
  (0x9354802495,0x240660fc1903e0100102785000a004278030041348b8190500c015831),
  (0,0x1d03002c200510160cc0285000a0b0190530b80b02902b1ae0a05002e),
  (0x183148060b5,0xf07e0fc1f03e0101fc9212a25201c0386d00a4a00200400617c93801),
  (0,0xe108627c2189f0d837c9686a0d23744d12b0d81682312c2561b03f001),
  (0x1806d1d001a2d4006475400f115203c35,0x530a61b00012b0d80203506907a15c3581507a014018560ac4b82f801),
  (0x404095,0x30104200410100cc208060141bc980ee00a27c7b92f0060a40d84d),
  (0x40706f,0x4509c1372264486693626a4d0879332644c46310c),
  (0x74b5,0xf07e0fc1f03e0104f09d8f125201c0386d00a4e80200400617c9c801)]

def r6_3 : List Hint := [(0,0xf07e0fc1f03e0102340780600a234078030141340981327e1709f13d),
  (0x11294204495,0xf0300601f03e0101742e9400b812c258ee00a27c2e85d0061702184d),
  (0x101929440489518122158068556013115a04c35,0x43086354a304208218421041010514a214300c014a11410c000c2f801),
  (0,0x35430842082520210410e051c2104101419ca008b1120c03306e),
  (0,0x7e1041f04101003c2080600a03c20803014134a514911622c1781b),
  (0,0x11c02652c2d806082020050410100304184100c0140584808200c0504d),
  (0x1e4748078ed,0x43086074a605b0b64540400801027c0600c00c0142180b01600c0504d),
  (0,0xf0300600680d0100040085700a010020030be0042c0581e20f41781b),
  (0,0xf1e63cc1f83f29a0f81f0131c20040085a1ba268020040fc1184c001),
  (0x7c39,0xf29e04c198500c61c82a876010004560030060080514e0a60d81a86e),
  (0x407d3900204a5c02c2d,0x15320c418a995209e268418a12a20542d1502a00141606a0861e40502c),
  (0,0x3301613c018500b602c0101d0101bc4f80500c0147b84b0560ac75821),
  (0x7c39,0xf29e04c198500c61c82a876010004560030060281494e0a634c1a86e),
  (0x8135,0x1813e000200761340cc2801500a0241682c0140b0098740b01cc1781b),
  (0x8535,0x330a6000070500c603439076010090089540a80280e04b0ee0a40e01b),
  (0x1e0884f38210fc002c26,0x570ad95b19e338ad0cc2b2560651571a055884955),
  (0x2cf5,0x522c6588b096009e074050a10ec0144195f0a0014af0d509e0a8ae923),
  (0,0xc30305940581d0ec0cc0285000a18c0102a004104538222a23ac10964),
  (0x813d0820474808ced,0x9f1e254c789532cc4542c0832ca57c2c05a17a014218f308410405083),
  (0,0x1682d01fc091672ce1b0350690da1b03f07d006004218d51e80f491922),
  (0,0x16a1101540500201020cb280600a14c2202b0720840e0530563ac10969),
  (0,0x1f83700e8db0a61d84d16b03a018358da00a0141682c1b20980502c),
  (0,0xb03a0000680b03a0301980500a060168910ec198158430500a013884),
  (0x9105,0x5305a5841604b000028540761340b00285002a0140d96c0aa1603982f)]

def r6_4 : List Hint := [(0x24254008049,0x1303026c4d0420ec0542105000a0b01e82d0140b02c03d0aa1cc1781b),
  (0,0x650ca0383800d01019c058030045b4809012dc1e8b686f06c0d43716d),
  (0,0x1e0e00380f00d0100000105500410c1590104228c1901a034088b78a2),
  (0,0x404e04c2a0500c60c802876010000b29540aa0080502104c0a01c834),
  (0xc425c0903d,0xe2e25c01903d09e1442d802142014440bd2be0144088800015805083),
  (0x1c0952d,0x182e40002c0530b61000585b0a20cc2808800a014290430b2204408a7),
  (0,0x17501610c2a0f90b60c8ba008010010b980c00c0140014e05615401165),
  (0x807c95,0xf0a80fc1903e0100100780600a00027855004594bb0130500e41094e),
  (0x2826134403019,0x2401c140068020100304f80600a02c2788801420c1580005222c1e87b),
  (0x1808009,0x2401c15406802010014b280600a5e02288801420c0c97711622c1783d),
  (0,0x11603a0000f8a10100300000c00a02c2182b0140c0060f40180c40e06e),
  (0,0xa816c1901d0100100280600a0001308801420cbb8390503ac10834),
  (0x26514009cf5,0x132945780c00e2f81000697b0102180417a0a01c80197923800c01007),
  (0,0x1802a000288761340147b01500a2041682c0140b0148fc0b01cc1781b),
  (0,0x17f0c60000f97e0ec01800026110078be8030141200d12606c0c01486e),
  (0,0x11603a0000f8a103a194c08050e00282182601420c0d1800500c033027),
  (0,0x240a816c190080100100600600a00001055004594bb0190503ac1094e),
  (0,0xd8030060200510ec0cc0285000a0244082d0140b00995e05457491982),
  (0,0xb030060058510ec0cc0285000a0244082d0140b0830220260a01082e),
  (0,0xd803002c200510160cc0285000a0244082d0140b0098221e20a01382e),
  (0xa145,0x9f01602c200510160cc0285000a0b04082d0140b0290221f80a01382e),
  (0xc25400a045,0x1801a1d80605000a1481680a05802c00002082104158000e60bcc1906),
  (0x8925,0x3013c200410100cc2085000a04c3a0290380bc2a07800602800878),
  (0,0x301ac0409a1341b43581500a00c1602c0140048b8dc08811074892)]

def r6_5 : List Hint := [(0x85,0xb0065940581d0ec0cc0285000a18c1304f01420cc20220563ac10834),
  (0xa535,0x1890546200c18701c100bf00d010218c30720a01c82a18510c15005011),
  (0x3125000121440a44d,0xb03013c068020ec030b285000a1482b18a01420c158000541cc178ed),
  (0x235400a045,0x1801a1d80605000a1482780a10602c150020821041584f1160bcc1984),
  (0,0xd80300602009a0ec0cc0a85000a638af18d2c26302a1470ee0280098b),
  (0,0x1d0d0060328050a00c840818058068111010420708b0f205448cc818f),
  (0x1001c09,0x180585504d0080040540316500a58c4404301420c098291d411074991),
  (0x160a8ef,0x66ccd19919e6605699732c654879943266486310c),
  (0x1402005,0x2400a13c0719e110034ce888010218ce0870a01c829043104220050e3),
  (0,0x1301c1accf93000416c4d0510042203580517a0142c82c1021a40502c),
  (0,0xfc01c0c80993017a16c190512ca0140a80517a0142c82c1021a40502c),
  (0x82c22480ac79,0x180261884d0080820540304100a0501484f09e3a4c608808202841843),
  (0,0xf20b61540e802010014b280600a14c448290380bc1c84305222c179a0),
  (0x208039,0x180261884d0760820540304100a0b0168410140b06e02909e28c74892),
  (0x1008c85,0xf20006840e80a082014050410e03ac2184f0040083e0271120c43316e),
  (0x404065682d134408019,0x33030140200550101bc4f80611000c208880140f40587905222c1e81b),
  (0x8125,0x3013c200410ec0cc2085000a0242082d0140b03a0740541cc1781b),
  (0x102e1a580a04d,0xc01c1400685501068c258061101bcd108b1160f40583d00602824043),
  (0x80bc79,0x540409a13415c3581500a2300a01407a0bcaa0832ca02841843),
  (0,0x540f89a1340781602c0145b4a19441fc690788580b00700d87c),
  (0,0xe016c0f01d0101940280600a14c488290380bc218390563ac10826),
  (0,0x543b09a13415c3581500a0b41602c0140b0d28580b01cc1781b),
  (0x3147440c05d,0x748a8080100000600c00a10c1582b0140c00000c0180c40e06e),
  (0,0x18cbf0760ec000130261105f401803014120d28d306c0c01486e)]

def r6_6 : List Hint := [(0x80c51d,0x748a8a803a604028050e010c1302601420c3e0280500c033027),
  (0,0x1d030060028050da2044081805808811151042070c819005448cc81a6),
  (0x80c8c9,0x2003e07c328650e06a0d411522c02c0580a01410c0600c34623c299a7),
  (0,0x200d01a0328650da0780f0680ca0c8191a92c623c8b11605448c47813),
  (0x3326420cc89,0x18c380760ec078018030143c4298530621b83e0911220700d83d),
  (0xd49900331e400d05d,0xe01d8000261100780180a09004c2784409e248000360620d037053),
  (0,0xe016c3280500c0001308810614c1c82b042070830390560841a0ab),
  (0,0x7003c0203280600a0004400a10614c158390420d02982b1d60841a1aa),
  (0x80d879,0xe02a000288081340147b01500a0a47e01407a0bc4085531802841843),
  (0,0xe016c0f01d0101940280600a18c488180800cc218390563ac109ab),
  (0,0x6802a0004d01f1340b00f02c01450c7a1441fc690331900b00700d87c),
  (0,0x1e0e016c0f01d0101940280600a1e4221010883a43c8eb0563ac10879),
  (0x20dc89,0x650c60000f8700ec0780f0030140dcd60530621b8330f51220700d83d),
  (0xdc79,0x650e007c000500aa0780f00a1581f04a84409e2483e03706253837053),
  (0,0x1e0e016c3280500c000010552ca6b41c82b042110d681a056084a71ad),
  (0,0x7003c0203280600a0004400a10602c0d01a03408c2982b1d60840e0ff),
  (0xb935,0x1813e000068761340302801500a0c81682c0140b0148740b01cc1781b),
  (0,0x540660383900d0100002a8500aa0047b8030042b0d706f06c0d4a706e),
  (0,0xd01040f8410101942080600a14c448290380bc121b0006198009af),
  (0xe11d,0x748a8a803a6c8028050e010c1c839014028d880500a0c433027),
  (0,0x911ca394db1b6010218430061106d4da93f3684f82a05400617cbe9b3),
  (0,0x15030060358150da0b0160700ca0b01602b042198c819007a48c479b7),
  (0xe499,0x3e104100410e00782080a03c1f02784412a248dc1b80381980d853),
  (0,0xd01043284100c080208881066b44482b0420703a0740520bc33191)]

def r6_7 : List Hint := [(0,0x1c104068410100142080600a46ca488b1160bc7b9b900602826843),
  (0,0x6803e0203280600a0804400a1066e8808891d2224dd0291160bc459ba),
  (0,0x450e29c4222440e19c2382700df9be37a6f0841bb),
  (0,0x6301a034e39c738c5e0bc08800000c0185f2fa1203786f0623c41486e),
  (0xbc85,0xf01a034008010e02340785f03c71ce380011e4882f05e0621983707c),
  (0,0x150300604d09a0101ac0a85700a0b0160030be0042c0583900701781b),
  (0xbd15002b41420acf5,0x354e48391d6520210410e051c210410be078d888b1120c43306e),
  (0xb125,0x3013c200410100cc2085000a18c2088801420c3a07405222c1781b)]

def c7 : Catalogue := (109,77,0x160450d8340bc2707c1bc82c08a1b0681785813d8114360d02f09c1b03ec08a1b06817858138360058114360d02f0b027ca3208a1b0681784e0380190450d8340bc2701f30c82c08a1a05e1383a0064160450d02f09c1dc82c08a1b0681784e0e65160450d8340bc2706f30ca2c08a1b0681784fa464160450d02f09c1bb02788a1b0681785613d8114360d02f09c0700ac08a1b0681805e1380e0058114360d02f0ac27ca2708a1b0681784e03e516c450d8340bc2701c00b62286c1a05e1380f985813c450d02f09c1d002c09e228681784e0ed8138450d8340bc2707348b02b08a1a05e138360058158450d02f09c1b003288a1b0681784e038019858114340bc2707400002c08a1a05e1383b9458114360d02f09c1c002c08a1b0681784e0e6719458114360d02f09c00d22c08a1a05e138360064138360d02f09c07c82d88a1b0681784e0de61905b114360d02f09c00c83108a1a05e138378858114360d02f09c02b0270982286c1a05e13801604c114360d02f09c00c82e89c1b0681784f60450d8340bc2706807ca2c08a1b0681784e0d641604e0d8340bc2706ac09c2286c1a05e138056c58128450d8340bc2700320b01b0681784e0d58114360d02f09c1a00800b02286c1a05e138056858114360d02f09c1a002c0942286c1a05e13d8138450d8340bc2702338b02708a1b0681784f6050114360d02f09c07ca2c0a02286c1a05e13e417c5b114360d02f09ef8b62286c1a05e1380c005b114360d02f09c06c42c0ae2708a1a05e13d815c4e114340bc2706ac0ae2b08a1a05e138340058158450d02f09c1a002d89c2286c1a05e038000064188560d02f09ed8b02708a1b06817834005b160450d8340bc1ac42c0ae2b08a1a05e13e4160450d8340bc2703ec08a2006c1a05e1381e0058114360d02f09c0fc82c08a1b0681784e00e719058114360d02f09f20b02286c1a0641784f60450d8340cc320bc27002c08a1b0681905e13e9190581143c0d02f09ec08a1b0681784e0600d60450d8340cc2f09c01b02308a1b0681985e13d8114360d02f09c0600400b02286c1a05e138036046114360d02f09c06002c08c2286c1a05e13d8114360d0330bc2702338b02286c1a0661784f905f114360d0330bc27b02808a1b0681784e035f16050114360d02f09ef88a1b0681985e1380d60571143c0d02f09c1a002c08a1e0681784e0d58140450d8340bc2702000b02286c1a05e138119c58140450d8340bc2700338b02286c1a05e13801905f114360d02f09c00be2286c1a05e1380c005815c450d02f09c1ab02708a1b0681985e0380160450d8340cc2f01f48b02b08a1e0681784e0069160450f0340bc2700320c4228781a05e13d813c450d8340cc2701800b02788a1b0681380d8c58158450f0340bc2700318b02b08a1a05e1380174450d8340cc2701800c42c0a4228801784e0058138450f0340bc1a,0x55666655556665565566665555666556556665564576555645765556646665656466656555666556556665565566556664667555556655665566655655665566556655664576555645765556457655566466656564666565556665566466755564667555457655566466656564666565556665565566655655665566646675554577555655766556557655666476755555666556556655665566556655775566556665565566655655676556556665565566655655676556556665565566655655666556556665565566556655665566556655665566556655765566557555665575556665667556655675566556755665567556467655576477755556666557566665576566755655666655556666555566665555665566556655665566556655665566556655666566755655665566556655665566556655665566556655665566556655665566556655665566556655765566556655665566556655755566655675566556755655665566556655665566556655665566557655665575556665567556566655675666556765667556656675566576755665665576656655766566755665667556657555766666775566567557)

def r7_0 : List Hint := [(0x552c00114700034dc6008fa000116d200057,0x1d83ae1e4eb1d53a874ce91d119c740ac9cf39c328e68f139872c849ca),
  (0xe0053f40014e8a0213300084c8001d055006369e018ba,0xf1172784f01df3bc2dcee8b63b82d0ed8b33b42c8581d915e744570ad),
  (0xc36c002cd720022bc001897000a12c402447,0x1ec3d6668cc0cf15a7a8f49e43c67a0f399218c5b4f31e53c878c831e2),
  (0x40454f08104fc603d1f000e415e0345f,0x1f31a07c8f89df1e2338f80cd3de2c8f70cb3da3286410e18e4c8630c5),
  (0x8156b460518d00135d4404549180b4a5e0486d,0xa66e8071f513e04c1e9061187d4530510b6268530d400a7d00a8d400a0001905905813c2e02c),
  (0x4456581713c00583a,0x2002285b4ff9fe3da44ccc1fd15a7f0fd9fa324318fc9f83ee790f19f6),
  (0x114542030f92006314202849,0x2448140983f40818c1f0050ec0201ea034044fc2e0c109a00c0185c09e04d01a0227e1701ea01),
  (0x381c4bd006d1f100a4680069130019448204cf6080e3d5806057780313d001c35,0xb620c835061ea41633c669d119c829049ed1643290420740c3c4630c5),
  (0xc0814f38204fd007d1f101e2bdc0745f,0x212422450cda1041e334f81ef19c838ed9ed164329039332643c4630c5),
  (0x3020664e0918d40235744088cd70211b5c0104d,0x260a82580002a13c3c85a42a378a889a2a2268052140d65400a85a00a84c1621305810c2e02c),
  (0x8056682607c40940a,0x21d3fe870899d115a86d0d1e43c64450c99521e1e4fc95c43085c68216),
  (0x206d40071a510052f4400409,0xa60ac2781830e16c200a103a0210fa201e60180521f43c0147700513e04c2295e2a82a86aa1e),
  (0x2a4dc60a52f000d29c00a09f001016c209c57,0x1d63ae894e99d23de741121cf19488d1110d18c314e68f1398424e5221),
  (0x293bc0044d720292bc804497002c12c00ac47,0x22b3d6668670cf15a8a91499521e8a0f399218c430832273c878d131e2),
  (0x2c52820b52f182a27c403885682a13d803835,0xd220c834cd1eb3da33c671d115a8bd1722d32a43d160c840c6486310c),
  (0x3153c20c53f003047c00bd1d20303bc80bced102e2bd80b85f,0x23546845119a324388c5181fd15a8b88891032a43c6410e21a6486310c),
  (0x3166420d18d003357480cd1d103233580c86d,0x864188300003a13ca605b46c16c8a8081420200400001813c0600600a0000584f01600c0504d),
  (0xc456,0x21d3fe870899fd15a8ec8819521e7f08699218c430fca3a47285d1c237),
  (0xc5b5002d694003d15200f31420b0491010065804009,0x20c0642783f46c16c1f0a10100201d84f018018028c109e02c0180a09a04c831064782a883106),
  (0xdd4718364a80048a7001516c20d457,0x1d73ac8f4e99ef19c740e79ce19488c868f118c314e69cc396424e5221),
  (0x60d99d18295a400e0bd,0x47c0740023e0a66e8068a10a22980615000a350028320000c81e85c0580ac3c8220f20a05002e),
  (0x3647480d8cd,0x480cc0703201a0208317927e1700000c1dc0142780001600c2e04f09a4180c82806041815831),
  (0xd199083463400e575,0x8645d20a4002610d1f85b46c16c530081420200403d01813c060ee00a0f40584f01600c2e04d),
  (0xb454802cc5583a17420b049,0x2449082183f46c16c1f0a10100201e84f0183b80283d09e02c0185c09a04c0024027e17101a01)]

def r7_1 : List Hint := [(0xb119003b44400e4f518372f4404ca56837175804c45,0x23804cd085b00c1040400a082020099064864fc2e00c0004c07700509e02c0009c0061702784d),
  (0xf98d203e57540f51d103c33580f06d,0x8610c0e94c0b616c8a8080100200005c1544fc2e0000180307700507a0000580b0061701e84d),
  (0xd15500144548050c51015065805409,0x11a0fc2d83e010021220aa27e1701d80c1dc0141e8c101600c2e03d09a04c8da3c15445c83106),
  (0x20fd2f,0x2472288d0ff9fe43844ce91fd15a8ed2311032a43cfe24521a6486310c),
  (0x2b19420fc49,0x1ea9082183f46c16c1f0a1010020468f40181400288d1e802c0180209a000dd1ba27e17101a01),
  (0x3f15820fc46,0x1143fe92c8991215a8ed2519521e7f12499218c430fca483c878cf31f6),
  (0x5945201641400b0c5083f2d4010065,0x1e0fc1f83e07c0204684f0a00144684f006008268003744fc2e2034020000993f0b880d009ba),
  (0x2b4542100f910093144104bd600919581045d,0x2940742183f46c16c1f0a10100212224c4804fc2e03b20c0307700507a3048300b0061701e84d),
  (0xb155082c514002915080a4148028c5280a2d401082d,0x1e0fc1f83e07c0212224d27e1701d83b1dc0141e8c118200c2e03d09a04c0993f0b800101a01),
  (0xc554203145200c454a031050040314210055,0x1e0fc1f83e07c0201e84f1dc0141e84f00617026a440264fc2e20340204d2693f0b880d00917),
  (0xc115ad3845635007d4d0044505010c554018115206035,0x1e20004f80013e3552883d0841042d8610841040525049e1082085a00a165270de2e210c2e02c),
  (0x473180118c520472d88118b5,0x1143fe92c8991215a95d2b2554a84d89a99521e94c999323243192910c),
  (0xed55083b5140124f520493940120dd10193146064b56019195a06455,0x1e0fc1f83e07c0212224d27e1703f9242544a40003b0763b80289f274304608030b810c9c84d),
  (0x140f51d004a3948128d510443144068b5181a295811065601a155a06845,0x8610c6aa5908410430842082020001174b04a89494528850c36805250508a086000617c93801),
  (0x121bd004c6b421318d004b574812d1d,0x9800026354a62590841048a8610841040409f4b61082080600a10d2d04208200c0504d),
  (0x13865004d154213445,0x8610c6aa59084104308420820212d84208201802a5a0841040180a09a0000000027e1709f13d),
  (0x4f0d8813c26,0x1144cc994e29c44c898ced2624c27653025f3802b52ba564bc974aaa5c),
  (0x141384500500d4814025,0x1e9a53403f07e14c1f03e026384008011a899c4d004008260230980021fc9200000000091922),
  (0x7d85001b5d4206d65201f554806d45281b4d541086d,0x8610c6aa6a06c34ce48391d6021278420821b4029470841040185f0020006a8f407a0f491922),
  (0x556a441519930535e401494518514f5c0343d,0x264193615209613d3589f00004c4189a1425444d05a0d6540a801500a1a8160430f20b00502c),
  (0x15d25385617c003426,0x794e277cada704ca339379ef2b4564f71cf2b03286826e4da55884955),
  (0x1659900585d4003535,0xa65882594f02627cb016109e584050a81420743b08300a57c0285000a354ae84f2bc0a8ae923),
  (0x205b3010168b838582c0e15cae48522a10038a63058280c15c9e4052261203896605b1400168487858101e15c3e08520e000383670580c1c15c2e00520a0203826,0x9f93ea7c4f69e93ca0a1649e13ba764ea9d139a72),
  (0x1713f0059438414d061059278014c96,0x2575161e545289510338e91d119aa1d43285508a0d41106502a010ba7f)]

def r7_2 : List Hint := [(0x18137005f29dc1789f005516c217457,0x28f51c3c4e98cd3de741121ed19488d4693218c3154626d4da424aaa21),
  (0x61857d705e2f400a0ad,0x47ca402981500004c068a12a2268061502a0054028320001e41600a0580a4789ba0b01cc17983),
  (0x18625f40178bd,0x168f87881d00027c0680b142074060502be0140280a0001581300a1060ac788f10500a013827),
  (0x4189006560401914518634f5c17c4d,0x265c0b882a3183c42d84b00027c2d89a0042840e8880d62f4af80500a220c60000ac09805083),
  (0x188ef006335c814497006712c019847,0x22b332668670cf15aa511499521e4194999218ca4948a273c878d131f6),
  (0x1891d00294348184cd,0x86a594aa3f30e038530a601a0200016d0181400280008a0082a8022ca1e43c8190500e41094e),
  (0x19db908695f421a16d182a2b46190956860175a14835,0x3745781e813530a602da3f30e1040e8a614c1040400513e5b42785000aa5c0004509e15401165),
  (0x1ad99206a47440c8cd,0xa65dd2085303a13cc385b46c16c8a8a81420740421e00a27c0280600a1141304f04c22005083),
  (0x68694014cc5286c174404019,0x43e14c2781846c16c200a103a0210f89f00a0180285309e0984400a10604c0015e2a82a90f299),
  (0x1a1c5ad087063401bd5d206e47581b46d,0x860011f00003a14ca605b30e16c8a8081420740409f018a680280600a0000504504c22005083),
  (0x1adb500696948150c50867125815409,0x4880642983f30e16c1f0a103a02046a9a00a01802a9c08a0984400a10604cbb9064782a94d906),
  (0x21c92f,0x2a4228a8d332a25427c1501d12b47b9051cf53e3288729e21aa74630c5),
  (0x72164209c35,0xa6aa80eaa9550061538a80a21d92780500a14002aa60142041680a0584188315e00057491aa5),
  (0x7215801cc36,0x21d4cc994899ef2b4ab0e79581944cc86a9d18c314fc95c2ac424aaaab),
  (0x756d401c8c5001029401d045,0x13e0600c0400a21d8198050a00141608105a028161062bc000ae92354a04caf0002ba48c6a906),
  (0x57255e1d85f007512800a836,0x1ba2b6ac067a6f2b4330ed958194abd5729d18c314abaad2ac424aaa21),
  (0x878634009d556077135000025,0x13eaccd324015014d35161564074530a854e0743b15f00a93c0280600a1594b8f1004ac401165),
  (0x7a694004175000125441e45d,0x56812c4f8184d4584200a103a1d81995f00a14002ab40ac098c500a10604c0015e054574918d5),
  (0x1ed99002a5940160b5000325401e859,0x265795a9612c013c0e8421421d8028422be1400282607a158c500a1065795a84f05457491ab3),
  (0x1f55d0004255e1f06d,0xa627c0e9602c25948a8a803a1d8af80500a140028561e60982780a106000ae95e05457491ab6),
  (0x1edb500594540014f5007831401d045,0x13e060b284003a1d8198050a00144f82609e02841ab82bc0a8ae92356c04caf2b7154630b1184),
  (0x687a4bc41e92a288048c020122007f48441f8af106421c603885687e17da19047600e115401c05,0x2bf3d4af8cd1eb33233ccc1d215aaf4832bc32a43d5daba374648632b9),
  (0x1fd35,0x2c23beb04ff99949644ccc11215a444cb21932a43d6019321a6486310c),
  (0x107167402018510652d5402005,0x2a86240002a086b100c18730e16c200a12fc0740408628a618da0500e455021ac304c220050e3)]

def r7_3 : List Hint := [(0x4138650082154020435,0xa6b18358532602f4a889a0a25946a06b00a2f402ac50582043480a0580000015e00057491982),
  (0xe2112f407e3d801f886001b0ad020c27401b02c020c07,0xb620c83567ace596828e71ed4eeb35662cb5949c878a21592b20aaac7),
  (0x60886b4a21d8d008657582146d605a0d5406005,0x261e5288000a6684a6091110104bf0910141040409f04c10820806110b414b84309e1540104f),
  (0x21f965405b295806c09,0x27c27cd097230e34c2c00a0820202c0830821b40293008613caa0022ca04c6aad107a22891ad0),
  (0x1ed2e106849841ecde00683580210af101c21c007067007a0ecc22437107a06c822417,0x1ea5aea24679d219ab5943284506aecdd2d518cb50ae10651885d69ad2),
  (0xc2314f388c4fc022cef001f0ad022827401f02c022807,0x2de44a451671e15bab70ed9ed4eeb316dada5949c878a21592b64aaad8),
  (0x1adad086b63402415d208f47482390d102e2f582346d,0x2da000298000a6074a61870b616c8a9151500740409f2da0140280600a0002282604c22005083),
  (0xb836,0x1144cc994f81ef2b47b8e7a6219443886a9d18c315522e02ac424aaadf),
  (0x2e61402455d001d255807c09,0x13e27c0e8f12c25848a8a803a1d8af80500a1b40285604c098c500a1063c4d31a6054574918f1),
  (0x20930b10248286093030024808,0x451742e7222441732e55c89cd719be37ab88842e1),
  (0x209653ca2593f2091479023916108b3bd0078b760912b80238a6001e19802544a08950e802501a,0x2de44a4517aaf45e68a8889105e4bc5782ef594bb878aed5d8bad752e9),
  (0x25d4f009647c0230af102021c008067,0x225514a217b1d119aa1d42a845068a086ad518cb508328150085d3fad2),
  (0xc2654a00230ad026027402302c026007,0x2f72283c4f0ace5ba76d121ed4eeb6d662da5949c910a21592b64aaad8),
  (0x30996f4c23199389b63402691d,0x14c8300002a13ca889a2a22690a06b2a005402af8058be01600a0023c4179ba0b00701781b),
  (0xc9750021255808c09,0x5f20744f8184d4584288a103a1d80295f00a1b40280a0ac098c500a1063f1689a6054574918f1),
  (0x207d43901a90640222dd81f49e006a258008866089d0e802701a,0x1be2285b5742f55e6444dd2fb5e4b9578aef594bb885afa5d8bad752e9),
  (0x825999289e63442691d,0x418830000c613cbf0762fc1d80000609e0984417d0065f40180a0903c4698f406c0c41486e),
  (0x227d4f102421c009067,0x2fe514a20671d119aa1d42a8450641886afd18cbf14128150085d3faab),
  (0x89f6b4025d9d009e574026ccd,0xa6000dd18730e16c8a8a603a020af95f00a0180280007a0082a8022ca1e43c8eb0563ac1094e),
  (0x9f6b40264cd,0x20c0002780330e16c058a103a0201995f00a0180280009e0984400a106418830390563ac1081c),
  (0x181cc0f,0x21d3fe870899fd15ac008819521ebfd1d23942e8e08710d324318860c8),
  (0x41cc19,0x1b00602d84003a021813014782a90f80500c0144f8d804c220050f41060a8af1541545b4b6a99),
  (0x94f5007329401e065,0x1b0060b284003a1d8198050a00146c02609e0284184b2bc3c45518c2c4000af02a2ba48c6a8f1),
  (0x896942284a910a01e581d05d,0x3680a80980e46c18c0697e0ec020da04b04c018441763444191e0aa20c3dd8180300602824043)]

def r7_4 : List Hint := [(0x30a26b4e2898d,0x1e20004f80013e354040610841042ba4f0841040280328e1082080a0023c47888b1120701781b),
  (0x28d5d20a34344234bd608d1b5410c05,0x35c04c298130a6244a618760a244bf11560a2440409f608098130061106802182604c2200503d),
  (0x2955d30a41b5807c09,0x13e27c2c1872e45c88a8dc0b0020af8dc0b01b4028431e63ccaa00a1060018330607a228919a0),
  (0x2358500855d42215650088164222049,0x2604c6aa6a06c34c308420821d9278420821b402b080841041680a058694788f105457491b07),
  (0x20a5479028d1640864192218f660a52b8028ca6008625822188600a612822983a,0x1ba20cc3586309596c2d1da4a5ccc2984acb594b8c3e2ed5d8bac842e9),
  (0x829dad28a7634422d0d,0x2da000298000a6354bf0610841040016d0841044417d28e1082080a0903c43e08b1120c41486e),
  (0x421d2600873580288af104521c01146700880ecc2a037108806c82a017,0x1065aeb2c679d119ab5965a84506c3924ad518cb50ae15c51885d69ad2),
  (0xa96b4029d5d00a23340230bd,0xa6000099874b21048a861082020afa4f082018028000f21044400a1066e8dd07405222c1788b),
  (0x82ac7a20aa1e5813c0f,0x1144cc994f81ef2b47b8e7a62194a9170312622c408710d61e318628c8),
  (0x82b0e9008a115813c09,0x2a0600c09a134020358150da01589b131ae454c60832ca55005083086c198300011448c3c879),
  (0x7ca5204f25402b445,0x2a0600c09a134020358150da0141602c00617c00b0760e000ef1232443547a00007a48c911de),
  (0x2298500835d4220d6500af2e422bca920ae22582b46d,0x2604c6aa6a06c34c30842082021278420821b4029a51e23c46b9153186802104111002841843),
  (0xad29482b435,0xd80480901702e0209586c0da0149586c00617c00b1562aadc1e923244c1d8383d62848c911c8)]

def c8 : Catalogue := (19,77,0x64160450d8340bc2706c00b02286c1a05e138379464160450d8340bc27b02708a1b0681784e0380160450d8340bc2701f28b02708a1b0681784e0065160450d8340bc2700320b62286c1a05e13dd1604e114360d02f09ec09c2286c1a05e138340058114360d02f09c1ab02809c2286c1a05e138018858158450d02f09f20b02286c1a0661784f60450d8340cc2f09c06002c08a1b0681784e0358140450d8340cc2f09c00b02808a1b0681784e0058158450f0340bc27,0x65777666657776665677666756776667567766675677666756776667568766676677667766677667666776676667667775778666667766776676667766766677666766776667667776678667)

def r8_0 : List Hint := [(0x300b530c0294b000952000214708074dc40191c100546c001118000345c6008fa480115dc0004f,0x31951c3c58c31762c74c669ef19c740659ed16432911a072643c4630c5),
  (0x1253000454b0010520003d47080e4dc20352f180329c40309f680315d80304f,0x31c3ae6098d9fe43874ce91fd15a8a58d11032a43cf39b021a6486310c),
  (0x1a6ec0065b7081869c20559f001746c00591708153e82034f9180431c4050bf10132f5a01067601417d804c5d,0x63c75d1a31b3fc870e99d23fa2b58f1ba374790f1a292da440ca90f0f279c3c90d324318b6b1d),
  (0x14d7200525c003456001e13000744b001c120006c47,0x2003fe668898cf15a8ed1499521e7f0f399218c431913213c878d9031f),
  (0x5556000d55400854b001751c000915000641c8008c520062dc005466002016c007c57,0x4007fccd11319e2b4833233c878d9222932a43c3caae3ce6486316d63a7e5919e43c6418f31f6),
  (0x502a47d40a51e5028474009d1b0020468007519002645c006516000f4540095130024448008d11001841800390508183d82038f5102231c4020c510072d4601ca5602219d8020656007155a01c45,0x3744198699a3b67b467a6f3a22b400327416790f1b266488b4ca90f0f2c9557206324318b6b1d),
  (0xc0bd2a382f47c00b905382d3c0e0b0ee482b3a1000ce6302d340c0b0ce402b321200cc6782d181e0b05e082b160000c56702d101c0b03e002b0e0200c36,0xf14f8774f89df1e29e8f0a795ba2c8eda783da9dd3aadb4e8b6939a72),
  (0x3a6ec00e5b700386ac00dda7083661c20d57f08345f440ccc710322fc40c8af100c2b580ac67603117d80c05d,0x63cca8b69d73741e58d9fe332870e99d23a474456a2945c5b50c99521eca43c9ba65064863292),
  (0xfd47002c29c00f85c003d16c00f058083b15c003036,0x1d72b6994e99ef2b4740e795819488c86a9d18c31596b2c33e424aab2b),
  (0x446ec010db7004269c00c977000c5d400b4c7000025401046b084019c00c836,0x65475c3c95b1e2cbce99d23a2568e815939e56065329374ca1970c618aca878a6d2ac424aaa21),
  (0x68416bda121ae683d6b44121ab10416a840f5a9283969c00e5a6000f694a11da300476880119a100455d440cca71803295a0cc676003195400405,0x2da001783313be1e4f59db332870cc2303a474456906660af10c99521eae9601ba650648632b9),
  (0x21312f004b480412918084244020fd0e103642040390618453d8412cb0004a2a06108a0183f27800d898000e258211486604917d80b835700709d801c07,0x31720c8359bb3659633c671d119acd59a2cb666a0d9910640cbf4632fc),
  (0x14d4f08534fc014120004f478413918100f4588148ef20513b44140b0104f2b80138a8000f29981345f700809d802007,0x33c2cc4519db3a5108c5379d119ace59c285666a0cd810e21ab54632d4),
  (0x16dbf005b668014d99085a63c21658d005657840e55600434f840dd36205847c815d1d105633800e4c610432b800dca660551bd81506d700909d802407,0x3e6418831ba2281e59f33a67ca2118a6f3a474466b3d670cf542a845061e4871ba650b54632d4),
  (0x402887000a19c014c56005e0f000f43b105d0e0c17037105e07040f41b005d060817017,0x21d682a20899d119a86d42b335067f086ad518cb519131768085d9fb2b),
  (0x16db600536d40131a500445f840e176104443800e106002f314402c97000b1dc016c6600410ecc17c37104106c817c17,0x20c77c3cb4167ca20899d23a23350db3d50aa1141aae374ca16a8c65a87e48315c68685da12ab),
  (0x19daf00666b4219d8f0866634018d5e102655801894e1061518c12936384a49881951f2064474418cce00263184188be00612d88128a6284a25981806f606017d81345d702209d808807,0xf2418dd1ba20cc359f345612b2d188cf4de74466b3d688c2565a845063203c9fc492b54632d4),
  (0x13436006a0b000a02b40690a101a027406a03100a00b006902001a007,0x1144cc994f0add69876cf6a624eeb6d6d34b4e69c9a5349690d1caab46),
  (0x18187004d614012575084959401b15e4062559012d46484b4d901b0ce0062318012cb6084b298018036002a0ad01ac27402a02c01ac07,0x374419868f16a0d3d86309596d31051db3da9893bb0a612b2da5aca4e43c510ac94bcd38aab4d)]

def c9 : Catalogue := (3,67,0x19058114360d02f09ec09c2286c1a05e13d8114360d0330bc27,0x668877776778777877777788)

def r9_0 : List Hint := [(0x154800043b0000ceb08023a02004e70804370200cdb00023600004d7180029c400097680015d800047,0x351636668e98cf15ac71909e43c68a51499521e1e4f39e7324318b6b1d),
  (0xf53000394b000d520003147080b4dc402918000944000210e1007420400506000a2a04024a01008278001c980001259801857700009d800007,0x32d3ae1e5a9b3b51074ce91d119ad499ca85666a0d949ba650b54632d4),
  (0x1248000451e3010460c03116300b418e02cf620123c08044ee40103a10030e6400b359202cc650052e04048b010112b88040a8200c298802c96280b219001468601218180445e0010160003056000b118202c3610050a0001408,0x1ba20cc35adb09596d6984acb6b2d6184acb666d5dab309596d5539b54)]

def c10 : Catalogue := (1,57,0x160450d8340bc27,0x77888888)

def r10_0 : List Hint := [(0x8e83801360c004c848012e10004a85000260a0048820011e1000058080112000043810000a0000008,0xd45a9b616c0d7dacb526bcccdabb5d6b8d5539b54)]

end PEqualNP.Outside.L_meta_10590.Six

namespace PEqualNP.Outside.L_meta_10590.Six



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
theorem b3 : ban c3 3 c3.1 := empty c3 3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok4_0 : ck c3 c4 3 0 r4_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4 : ban c4 4 c4.1 := by
  have p0 := empty c4 4
  have p1 : ban c4 4 8 := more b3 p0 ok4_0
  exact p1

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
theorem b5 : ban c5 5 c5.1 := by
  have p0 := empty c5 5
  have p1 : ban c5 5 24 := more b4 p0 ok5_0
  have p2 : ban c5 5 48 := more b4 p1 ok5_1
  have p3 : ban c5 5 58 := more b4 p2 ok5_2
  exact p3

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
theorem ok6_3 : ck c5 c6 5 72 r6_3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok6_4 : ck c5 c6 5 96 r6_4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok6_5 : ck c5 c6 5 120 r6_5 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok6_6 : ck c5 c6 5 144 r6_6 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok6_7 : ck c5 c6 5 168 r6_7 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b6 : ban c6 6 c6.1 := by
  have p0 := empty c6 6
  have p1 : ban c6 6 24 := more b5 p0 ok6_0
  have p2 : ban c6 6 48 := more b5 p1 ok6_1
  have p3 : ban c6 6 72 := more b5 p2 ok6_2
  have p4 : ban c6 6 96 := more b5 p3 ok6_3
  have p5 : ban c6 6 120 := more b5 p4 ok6_4
  have p6 : ban c6 6 144 := more b5 p5 ok6_5
  have p7 : ban c6 6 168 := more b5 p6 ok6_6
  have p8 : ban c6 6 176 := more b5 p7 ok6_7
  exact p8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok7_0 : ck c6 c7 6 0 r7_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok7_1 : ck c6 c7 6 24 r7_1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok7_2 : ck c6 c7 6 48 r7_2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok7_3 : ck c6 c7 6 72 r7_3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok7_4 : ck c6 c7 6 96 r7_4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b7 : ban c7 7 c7.1 := by
  have p0 := empty c7 7
  have p1 : ban c7 7 24 := more b6 p0 ok7_0
  have p2 : ban c7 7 48 := more b6 p1 ok7_1
  have p3 : ban c7 7 72 := more b6 p2 ok7_2
  have p4 : ban c7 7 96 := more b6 p3 ok7_3
  have p5 : ban c7 7 109 := more b6 p4 ok7_4
  exact p5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok8_0 : ck c7 c8 7 0 r8_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b8 : ban c8 8 c8.1 := by
  have p0 := empty c8 8
  have p1 : ban c8 8 19 := more b7 p0 ok8_0
  exact p1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok9_0 : ck c8 c9 8 0 r9_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b9 : ban c9 9 c9.1 := by
  have p0 := empty c9 9
  have p1 : ban c9 9 3 := more b8 p0 ok9_0
  exact p1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok10_0 : ck c9 c10 9 0 r10_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b10 : ban c10 10 c10.1 := by
  have p0 := empty c10 10
  have p1 : ban c10 10 1 := more b9 p0 ok10_0
  exact p1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower (hard : ∀ d ∈ ds, Hard y d.1 d.2 base.toFinset) (k : ℕ) (run : build raw y k base.toFinset) : 11 ≤ k := by
  have denial := b10 0 (by decide +kernel)
  have eqBank : entryBank dict (rowAt c10 0 (0,0)) = base := by decide +kernel
  have eqDebts : entryDebts masks (rowAt c10 0 (0,0)) = ds := by decide +kernel
  rw [eqBank, eqDebts] at denial
  exact cert_lower (by decide +kernel) (by decide +kernel) (neg := neg) (by decide +kernel)
    hard denial run

end PEqualNP.Outside.L_meta_10590.Six

namespace PEqualNP.Outside.L_meta_10590

def sampleRow (code : ℕ) (i : Fin 64) : Fin 64 := ⟨(code >>> (6*i.val)) % 64, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

namespace Private

def y : W := 0xfffefea0

def base : List W := [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]



set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fromClique (cl : ∀ k, build raw Clique.y k Clique.base.toFinset → 7 ≤ k)
    (k : ℕ) (run : build raw y k base.toFinset) : 8 ≤ k := by
  apply essential_sample (v := 0xcccccccc) (sampleRow 0x75c65855445034c248144040)
    8 10 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) cl k run

end Private

namespace Six



set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem h0 (lower : ∀ k, build raw Private.y k Private.base.toFinset → 8 ≤ k) :
    Hard y 0x5555555555555555 8 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0xfbceb8db4cb0bacaa89a48a079c69859449038c288184080)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem h1 (lower : ∀ k, build raw Private.y k Private.base.toFinset → 8 ≤ k) :
    Hard y 0x3333333333333333 8 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0xf7cd74e78c70b6c964a6886075c55465845034c144248040)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem h2 (lower : ∀ k, build raw Private.y k Private.base.toFinset → 8 ≤ k) :
    Hard y 0xf0f0f0f0f0f0f0f 8 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0xef9eb8cf1cb0ae9aa88e18a06d96984d14902c92880c1080)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem h3 (lower : ∀ k, build raw Private.y k Private.base.toFinset → 8 ≤ k) :
    Hard y 0xff00ff00ff00ff 8 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0xdf6d74cf2c709e69648e28605d65544d24501c61440c2040)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem h4 (lower : ∀ k, build raw Universal.y k Universal.base.toFinset → 8 ≤ k) :
    Hard y 0xffff0000ffff 8 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0xbeeb6caeaa689e69648e28603ce34c2ca2481c61440c2040)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem h5 (lower : ∀ k, build raw Universal.y k Universal.base.toFinset → 8 ≤ k) :
    Hard y 0xffffffff 8 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0x7de75c6da6585d65544d24503ce34c2ca2481c61440c2040)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem h6 (lower : ∀ k, build raw Clique.y k Clique.base.toFinset → 7 ≤ k) :
    Hard y 0x505050505050505 7 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0xeb8cb0aa88a0698490288080)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem h7 (lower : ∀ k, build raw Clique.y k Clique.base.toFinset → 7 ≤ k) :
    Hard y 0x33003300330033 7 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0xd74c70964860554450144040)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem startDebts (cl : ∀ k, build raw Clique.y k Clique.base.toFinset → 7 ≤ k)
    (un : ∀ k, build raw Universal.y k Universal.base.toFinset → 8 ≤ k) :
    ∀ d ∈ ds, Hard y d.1 d.2 base.toFinset := by
  intro d hd
  simp only [ds,List.mem_cons,List.not_mem_nil,or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0 (Private.fromClique cl)
  · exact h1 (Private.fromClique cl)
  · exact h2 (Private.fromClique cl)
  · exact h3 (Private.fromClique cl)
  · exact h4 un
  · exact h5 un
  · exact h6 cl
  · exact h7 cl

end Six

end PEqualNP.Outside.L_meta_10590

namespace PEqualNP.Outside.L_meta_10590.Seven

-- Signed gate compilation from L_meta_9136 and its upstream predecessors.
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev V := BitVec 128
def ops (a b : V) : List V := [a &&& b, a ||| b, a &&& ~~~b, b &&& ~~~a]
abbrev basicOps (a b : V) : Finset V := (ops a b).toFinset
def inputs : List V := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000]
def truth : V := 0xfffffffefffefefafffffffefffeeca0
def goal : V := ~~~truth
def extra : V := 0xffffffffffffffff0000000000000000
def six : W := 0xfffffffefffeeca0
def sixInputs : List W := [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]
def es : List ℕ := [0,2,1,3,0,4,2,4,0,5,1,5,2,5,3,5,0,6,1,6,2,6,3,6,5,6]

def target (x : Fin 7 → Bool) : Bool := decide (∃ i < es.length / 2,
  (List.ofFn x).getD (es.getD (2 * i) 0) false = true ∧
  (List.ofFn x).getD (es.getD (2 * i + 1) 0) false = true)

def circuit : List Gate :=
  [⟨.or, [0,2]⟩, ⟨.or, [1,3]⟩, ⟨.or, [5,6]⟩,
   ⟨.and, [0,2]⟩, ⟨.and, [1,3]⟩, ⟨.and, [5,6]⟩,
   ⟨.and, [4,7]⟩, ⟨.or, [7,8]⟩, ⟨.and, [9,14]⟩,
   ⟨.or, [10,11]⟩, ⟨.or, [12,13]⟩, ⟨.or, [15,16]⟩, ⟨.or, [17,18]⟩]

theorem monotoneUpper : circuit.length = 13 ∧
    (∀ g ∈ circuit, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
    ∀ x : Fin 7 → Bool, Circuit.eval ⟨circuit, 19⟩ (List.ofFn x) = target x := by
  refine ⟨rfl, ?_, ?_⟩
  · intro g hg
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst g <;> simp
  · decide +kernel


def holds (av : Finset V) (z : V) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

set_option maxRecDepth 100000 in
theorem holds_insert {av : Finset V} {z a : V} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

set_option maxRecDepth 100000 in
theorem holds_not {av : Finset V} {z : V} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset V) (z : V) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

set_option maxRecDepth 100000 in
theorem reachable_not {av : Finset V} {z : V} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 100000 in
theorem and_reach {av : Finset V} {x y : V} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : V) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : V) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 128 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : V) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 128)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : V) (hw : w ∈ basicOps a b) (z : V) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

set_option maxRecDepth 100000 in
theorem or_reach {av : Finset V} {x y : V} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 128) (z : V) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

set_option maxRecDepth 100000 in
private theorem read_bit (w : List V) (i : ℕ) (k : Fin 128) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List V) (g : Gate) : V := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 100000 in
theorem action_spec (w : List V) (g : Gate) (hg : legal g) (k : Fin 128) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : V)[k.val] = false := by change (0#128)[k.val] = false; simp
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
theorem available_read {av : Finset V} {w : List V} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 100000 in
theorem gate_reach (w : List V) (av : Finset V) (hw : ∀ u ∈ w, holds av u)
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
    show ∀ x : V, x ||| (0 : V) = x from fun x => BitVec.or_zero,
    show ∀ x : V, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
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
    (w : List V) (av : Finset V) (hw : ∀ u ∈ w, holds av u)
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
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : V => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (~~~goal) := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset V) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
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


def trunc (v : V) : W := v.setWidth 64

theorem trunc_op {a b z : V} (h : z ∈ basicOps a b) : trunc z ∈ raw (trunc a) (trunc b) := by
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at h
  simp only [raw,words,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]
  rcases h with rfl | rfl | rfl | rfl
  · left; ext i hi; simp [trunc,hi]
  · right; left; ext i hi; simp [trunc,hi]
  · right; right; left; ext i hi; simp [trunc,hi]
  · right; right; right; ext i hi; simp [trunc,hi]

theorem diff128 (i j : Fin 128) {a b z : V} (h : z ∈ basicOps a b)
    (diff : z[i.val] ≠ z[j.val]) : a[i.val] ≠ a[j.val] ∨ b[i.val] ≠ b[j.val] := by
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at h
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  rcases h with rfl | rfl | rfl | rfl <;> simp [ha,hb] at diff

theorem source_zero {a b z : V} (h : z ∈ basicOps a b) (one : z[0] = true) :
    a[0] = true ∨ b[0] = true := by
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> simp at one <;> tauto

theorem project_at_four {k : ℕ} (lower : ∀ l, build raw six l sixInputs.toFinset → 11 ≤ l)
    (run : build basicOps truth k inputs.toFinset) : 12 ≤ k := by
  obtain ⟨s,sub,live'⟩ := compress run
  have difference : truth[1] ≠ truth[65] := by decide +kernel
  obtain ⟨v,hv,ev⟩ := live_separates (fun w : V => w[1] ≠ w[65]) difference
    (fun _ _ _ hop => diff128 1 65 hop) live'
  have classify : inputs.all (fun w => (w[1] == w[65]) || (w == extra)) = true := by decide +kernel
  have cls := List.all_eq_true.mp classify v (List.mem_toFinset.mp (sub hv))
  simp only [Bool.or_eq_true,beq_iff_eq] at cls
  have extraIn : extra ∈ s := cls.resolve_left ev ▸ hv
  have positive : 0 < zeroCount trunc 0 s := Finset.card_pos.mpr
    ⟨extra,Finset.mem_filter.mpr ⟨extraIn,by decide +kernel⟩⟩
  have eq : trunc truth = six := by decide +kernel
  obtain ⟨l,pay,smaller⟩ := project_live basicOps raw trunc 0
    (fun _ _ _ hop => raw_simple (trunc_op hop)) (fun _ _ _ hop => trunc_op hop)
    (by decide +kernel : trunc truth ≠ 0) live'
  rw [eq] at smaller
  have permitted : project trunc 0 inputs.toFinset ⊆ sixInputs.toFinset := by decide +kernel
  have bound := lower l (build_subset smaller ((project_subset trunc 0 sub).trans permitted))
  omega

theorem binary_lower (lower : ∀ l, build raw six l sixInputs.toFinset → 11 ≤ l)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs,legal g)
    (he : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target x) :
    12 ≤ binaryCost gs := by
  have width : inputs.length = 7 := rfl
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := fun u hu =>
    .inr (.inr ⟨u,List.mem_toFinset.mpr hu,.inl rfl⟩)
  have sample : ∀ j : Fin 128, target (fun i => (inputs.getD i.val 0)[j.val]) = bit j (~~~goal) := by
    decide +kernel
  have evaluate (k : Fin 128) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 7) : Bool := bit k (inputs.getD i.val 0)
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
  obtain ⟨u,hu,run⟩ := compile gs o hg inputs inputs.toFinset init evaluate
  rcases hu with rfl | rfl
  · obtain ⟨s,sub,hr⟩ := compress run
    obtain ⟨w,hw,on⟩ := live_separates (fun w : V => w[0] = true)
      (by decide +kernel : goal[0] = true) (fun _ _ _ h => source_zero h) hr
    have none : inputs.all (fun w => !w[0]) = true := by decide +kernel
    have no := List.all_eq_true.mp none w (List.mem_toFinset.mp (sub hw))
    simp [on] at no
  · apply project_at_four lower
    simpa only [goal,BitVec.not_not] using run

theorem comparison (lower : ∀ l, build raw six l sixInputs.toFinset → 11 ≤ l)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs,legal g)
    (he : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target x) :
    ∃ (ms : List Gate) (mo : ℕ),
      (∀ g ∈ ms, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      ms.length ≤ gs.length ∧ ∀ x : Fin 7 → Bool, Circuit.eval ⟨ms,mo⟩ (List.ofFn x) = target x := by
  by_cases has : ∃ g ∈ gs, g.op = GateOp.not
  · obtain ⟨g,hm,op⟩ := has
    have less : (gs.filter isBinary).length < gs.length :=
      List.length_filter_lt_length_iff_exists.mpr ⟨g,hm,by simp [isBinary,op]⟩
    have count := binary_lower lower gs o hg he
    change 12 ≤ (gs.filter isBinary).length at count
    obtain ⟨len,legal',correct⟩ := monotoneUpper
    exact ⟨circuit,19,legal',by omega,correct⟩
  · refine ⟨gs,o,?_,le_rfl,he⟩
    intro g hm
    obtain ⟨ops',size⟩ := hg g hm
    exact ⟨by rcases ops' with a | b | n; exact .inl a; exact .inr b; exact (has ⟨g,hm,n⟩).elim,size⟩

end PEqualNP.Outside.L_meta_10590.Seven

theorem PEqualNP.Outside.L_meta_10590 :
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fits _ computes
  exact PEqualNP.Outside.L_meta_10590.Seven.comparison
    (PEqualNP.Outside.L_meta_10590.Six.lower (PEqualNP.Outside.L_meta_10590.Six.startDebts
      PEqualNP.Outside.L_meta_10590.Clique.lower PEqualNP.Outside.L_meta_10590.Universal.lower))
    gates o fits computes
