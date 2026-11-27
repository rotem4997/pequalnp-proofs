import PEqualNP.Defs

-- Setting input 4 to true yields a seven-variable restriction requiring ten binary gates.

-- The live-set compression proof is adapted from L-meta-9136 and its credited sources.
namespace PEqualNP.Outside.L_meta_14794.SignedCert
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

abbrev W := BitVec 128

def phase (b : Bool) (a : W) : W := if b then ~~~a else a
def norm (m w : W) : W :=
  if (m &&& w).toNat ≤ (m &&& ~~~w).toNat then m &&& w else m &&& ~~~w
def opList (m a b : W) : List W :=
  [norm m (a &&& b), norm m (a &&& ~~~b), norm m (~~~a &&& b), norm m (~~~a &&& ~~~b)]
def ops (m a b : W) : Finset W := (opList m a b).toFinset

theorem mask_neg (m a : W) : m &&& ~~~(m &&& a) = m &&& ~~~a := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_and,BitVec.getElem_not]
  cases m[i] <;> simp

theorem mask_pair (m a b : W) : (m &&& a) &&& (m &&& b) = m &&& (a &&& b) := by
  rw [show (m &&& a) &&& (m &&& b) = (m &&& m) &&& (a &&& b) by ac_rfl, BitVec.and_self]

theorem norm_of_mask {m a b : W} (h : m &&& a = m &&& b) : norm m a = norm m b := by
  have hh : m &&& ~~~a = m &&& ~~~b := by
    simpa only [mask_neg] using congrArg (fun x : W => m &&& ~~~x) h
  simp only [norm,h,hh]

theorem norm_neg (m a : W) : norm m (~~~a) = norm m a := by
  simp only [norm, BitVec.not_not]
  split <;> split <;> first | rfl | apply BitVec.eq_of_toNat_eq <;> omega

theorem norm_cases (m a : W) : ∃ t : Bool, norm m a = m &&& phase t a := by
  by_cases h : (m &&& a).toNat ≤ (m &&& ~~~a).toNat
  · exact ⟨false,if_pos h⟩
  · exact ⟨true,if_neg h⟩

theorem phase_cancel (t : Bool) (m a : W) :
    m &&& phase t (m &&& phase t a) = m &&& a := by
  cases t <;> simp [phase,mask_neg,← BitVec.and_assoc]

theorem proj_norm (m q a : W) (h : q &&& m = q) : norm q (norm m a) = norm q a := by
  obtain ⟨t, ht⟩ := norm_cases m a
  rw [ht]
  have e : q &&& (m &&& phase t a) = q &&& phase t a := by rw [← BitVec.and_assoc, h]
  rw [norm_of_mask e]
  cases t <;> simp [phase, norm_neg]

theorem norm_idem (m a : W) : norm m (norm m a) = norm m a := proj_norm m m a (by simp)

theorem op_mem (m a b : W) (s t : Bool) :
    norm m (phase s a &&& phase t b) ∈ ops m a b := by
  cases s <;> cases t <;> simp [phase,ops,opList]

theorem op_cases {m a b z : W} (h : z ∈ ops m a b) :
    ∃ s t : Bool, z = norm m (phase s a &&& phase t b) := by
  simp only [ops, opList, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl
  · exact ⟨false,false,rfl⟩
  · exact ⟨false,true,rfl⟩
  · exact ⟨true,false,rfl⟩
  · exact ⟨true,true,rfl⟩

theorem recover (m a : W) (s : Bool) :
    ∃ t : Bool, m &&& phase t (norm m a) = m &&& phase s a := by
  obtain ⟨u,e⟩ := norm_cases m a
  refine ⟨xor s u, ?_⟩
  rw [e]
  cases s <;> cases u <;> simp [phase, mask_neg,← BitVec.and_assoc]

theorem norm_gate (m a b : W) (s t : Bool) :
    norm m (phase s a &&& phase t b) ∈ ops m (norm m a) (norm m b) := by
  obtain ⟨s',hs⟩ := recover m a s
  obtain ⟨t',ht⟩ := recover m b t
  have e : m &&& (phase s a &&& phase t b) =
      m &&& (phase s' (norm m a) &&& phase t' (norm m b)) := by
    calc
      _ = (m &&& phase s a) &&& (m &&& phase t b) := (mask_pair _ _ _).symm
      _ = (m &&& phase s' (norm m a)) &&& (m &&& phase t' (norm m b)) := by rw [hs,ht]
      _ = _ := mask_pair _ _ _
  rw [norm_of_mask e]
  exact op_mem _ _ _ _ _

theorem proj_op {m q a b z : W} (hsub : q &&& m = q) (hz : z ∈ ops m a b) :
    norm q z ∈ ops q (norm q a) (norm q b) := by
  obtain ⟨s,t,rfl⟩ := op_cases hz
  rw [proj_norm _ _ _ hsub]
  exact norm_gate _ _ _ _ _

end PEqualNP.Outside.L_meta_14794.SignedCert

namespace PEqualNP.Outside.L_meta_14794.SignedCert

theorem norm_zero (m : W) : norm m 0 = 0 := by
  change norm m (0#128) = 0#128
  simp [norm]

theorem op_swap (m a b : W) : ops m a b = ops m b a := by
  ext z
  constructor
  all_goals
    intro hz
    obtain ⟨s,t,rfl⟩ := op_cases hz
    rw [BitVec.and_comm]
    exact op_mem _ _ _ _ _

theorem op_flat {m a z : W} (hz : z ∈ ops m 0 a) : z = 0 ∨ z = norm m a := by
  obtain ⟨s,t,rfl⟩ := op_cases hz
  have h1 (v : W) : (~~~(0 : W)) &&& v = v := @BitVec.allOnes_and _ v
  have h2 (v : W) : (0 : W) &&& v = 0 := @BitVec.zero_and _ v
  cases s
  · left
    change norm m ((0 : W) &&& phase t a) = 0
    rw [h2,norm_zero]
  · right
    change norm m ((~~~(0 : W)) &&& phase t a) = norm m a
    rw [h1]
    cases t
    · rfl
    · exact norm_neg _ _

theorem op_same {m a z : W} (hz : z ∈ ops m a a) : z = 0 ∨ z = norm m a := by
  obtain ⟨s,t,rfl⟩ := op_cases hz
  cases s <;> cases t
  · right; exact congrArg (norm m) BitVec.and_self
  · left; exact (congrArg (norm m) (BitVec.and_not_self a)).trans (norm_zero m)
  · left; exact (congrArg (norm m) (BitVec.not_and_self a)).trans (norm_zero m)
  · right; exact (congrArg (norm m) BitVec.and_self).trans (norm_neg m a)

theorem more {α : Type} [DecidableEq α] {o : α → α → Finset α} {g : α} {k l : ℕ} {s : Finset α}
    (hkl : k ≤ l) (hh : build o g k s) : build o g l s := by
  induction hkl with
  | refl => exact hh
  | step _ ih => exact Or.inl ih

theorem enlarge {α : Type} [DecidableEq α] {o : α → α → Finset α} {g : α} {k : ℕ} {s b : Finset α}
    (hsub : s ⊆ b) (hh : build o g k s) : build o g k b := by
  induction k generalizing s b with
  | zero => exact hsub hh
  | succ k ih =>
    rcases hh with skip | ⟨a,ha,c,hc,hn,z,hz,tail⟩
    · exact Or.inl (ih hsub skip)
    · exact Or.inr ⟨a,hsub ha,c,hsub hc,hn,z,hz,ih (Finset.insert_subset_insert _ hsub) tail⟩

def bank (q : W) (S : Finset W) : Finset W := insert 0 (S.image (norm q))
def flat (q : W) (S : Finset W) : Bool := decide (0 ∈ S.image (norm q))

theorem tailBank {z a b : W} {r A : Finset W} {q : W}
    (h : bank q (insert a (insert b r)) ⊆ A) (hz : norm q z ∈ A) :
    bank q (insert z r) ⊆ A := by
  intro x hx
  simp only [bank,Finset.image_insert,Finset.mem_insert] at hx
  rcases hx with rfl | rfl | hr
  · exact h (by simp [bank])
  · exact hz
  · exact h (by simp [bank,hr])

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem projected {m q g : W} {k : ℕ} {S : Finset W} (sub : q &&& m = q)
    (nz : norm q g ≠ 0) (run : live (ops m) g k S) {A : Finset W} (ha : bank q S ⊆ A) :
    build (ops q) (norm q g) (k - (flat q S).toNat) A := by
  induction k generalizing S A with
  | zero =>
    change S = {g} at run
    subst S
    rw [Nat.zero_sub]
    exact ha (show norm q g ∈ bank q {g} by simp [bank])
  | succ k ih =>
    rcases run with skip | ⟨a,ham,b,hbm,hab,z,hz,hnew,r,hs,tail⟩
    · exact more (by omega) (ih skip ha)
    subst S
    have za := proj_op sub hz
    have am : norm q a ∈ A := ha (by simp [bank])
    have bm : norm q b ∈ A := ha (by simp [bank])
    by_cases free : norm q z ∈ A
    · have h := ih tail (tailBank ha free)
      apply more _ h
      cases flat q (insert a (insert b r)) <;> simp <;> omega
    · have zne : norm q z ≠ 0 := fun e => free (e ▸ ha (by simp [bank]))
      have an : norm q a ≠ 0 := by
        intro e
        rw [e] at za
        rcases op_flat za with zz | zz
        · exact zne zz
        · exact free (by rw [zz,norm_idem]; exact bm)
      have bn : norm q b ≠ 0 := by
        intro e
        rw [op_swap q, e] at za
        rcases op_flat za with zz | zz
        · exact zne zz
        · exact free (by rw [zz,norm_idem]; exact am)
      have ne : norm q a ≠ norm q b := by
        intro e
        rw [e] at za
        rcases op_same za with zz | zz
        · exact zne zz
        · exact free (by rw [zz,norm_idem]; exact bm)
      have liftA := Finset.subset_insert (norm q z) A
      have htail := ih tail (tailBank (ha.trans liftA) (Finset.mem_insert_self ..))
      have eflat : flat q (insert z r) = flat q (insert a (insert b r)) := by
        simp only [flat, Finset.image_insert, Finset.mem_insert, Ne.symm zne, Ne.symm an, Ne.symm bn, false_or]
      rw [eflat] at htail
      have step : build (ops q) (norm q g) ((k - (flat q (insert a (insert b r))).toNat) + 1) A :=
        Or.inr ⟨_,am,_,bm,ne,_,za,htail⟩
      have hkpos : 0 < k ∨ flat q (insert a (insert b r)) = false := by
        cases k with
        | zero =>
          right
          change insert z r = {g} at tail
          have h : flat q (insert z r) = false := by rw [tail]; simp only [flat, Finset.image_singleton, Finset.mem_singleton, Ne.symm nz, decide_false]
          exact eflat ▸ h
        | succ => exact Or.inl (by omega)
      apply more _ step
      rcases hkpos with h | h
      · cases flat q (insert a (insert b r)) <;> simp <;> omega
      · simp [h]

end PEqualNP.Outside.L_meta_14794.SignedCert

namespace PEqualNP.Outside.L_meta_14794.SignedCert

abbrev Recipe := W × W × W
structure Bound where
  mask : W
  inputs : List W
  goal : W
  cost : ℕ

def Valid (b : Bound) : Prop := ∀ k < b.cost, ¬build (ops b.mask) b.goal k b.inputs.toFinset

def recipe (q : W) (raw : List W) : List Recipe → List W → ℕ → Bool
  | [], need, _ => need.all (fun v => raw.contains v)
  | (z,a,b)::rest, need, credit =>
    let out := norm q z
    let u := norm q a
    let v := norm q b
    if need.contains out && !raw.contains out && out != u && out != v &&
        u != v && (opList q u v).contains out then
      credit != 0 && recipe q raw rest (u :: v :: need.filter (· != out)) (credit-1)
    else recipe q raw rest need credit

theorem recipe_sound {q g : W} {raw need : List W} {h : List Recipe} {d n : ℕ}
    (ok : recipe q raw h need d = true) (run : build (ops q) g n need.toFinset) :
    build (ops q) g (n+d) raw.toFinset := by
  induction h generalizing n d need with
  | nil =>
    have sub : need.toFinset ⊆ raw.toFinset := by
      intro x hx
      exact List.mem_toFinset.mpr (List.contains_iff_mem.mp (List.all_eq_true.mp ok x (List.mem_toFinset.mp hx)))
    exact more (by omega) (enlarge sub run)
  | cons hd rest ih =>
    obtain ⟨z,a,b⟩ := hd
    simp only [recipe] at ok
    split at ok
    · rename_i yes
      simp only [Bool.and_eq_true, bne_iff_ne, List.contains_iff_mem] at yes ok
      let u := norm q a
      let v := norm q b
      let out := norm q z
      let newPool := (u :: v :: need.filter (· != out)).toFinset
      have hu : u ∈ newPool := by simp [newPool]
      have hv : v ∈ newPool := by simp [newPool]
      have uv : u ≠ v := yes.1.2
      have gate : out ∈ ops q u v := List.mem_toFinset.mpr yes.2
      have cover : need.toFinset ⊆ insert out newPool := by
        intro x hx
        by_cases e : x = out
        · simp [e]
        · exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨List.mem_toFinset.mp hx, bne_iff_ne.mpr e⟩))))
      have step : build (ops q) g (n+1) newPool :=
        Or.inr ⟨u,hu,v,hv,uv,out,gate,enlarge cover run⟩
      have r := ih ok.2 step
      have dc := ok.1
      have e : n + 1 + (d - 1) = n + d := by omega
      rw [e] at r
      exact r
    · exact ih ok run

def cut (m g : W) (b : Bound) (k : ℕ) (ws : List W) (h : List Recipe) : Bool :=
  let q := b.mask
  let left := k - (ws.any (fun a => norm q a == 0)).toNat
  ((q &&& m) == q) && ((norm q g) == b.goal) && (b.goal != 0) && decide (left < b.cost) &&
    recipe q b.inputs h (0 :: ws.map (norm q)) (b.cost-1-left)

set_option maxRecDepth 10000 in
theorem cut_sound {m g : W} {b : Bound} (hb : Valid b) {k : ℕ} {ws : List W} {h : List Recipe}
    (yes : cut m g b k ws h = true) (run : live (ops m) g k ws.toFinset) : False := by
  simp only [cut, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, decide_eq_true_eq] at yes
  obtain ⟨⟨⟨⟨sub,eq⟩,nz⟩,small⟩,rec⟩ := yes
  have flat_eq : flat b.mask ws.toFinset = ws.any (fun a => norm b.mask a == 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [flat,decide_eq_true_eq,Finset.mem_image,List.mem_toFinset,List.any_eq_true,beq_iff_eq]
  have bank_eq : bank b.mask ws.toFinset = (0 :: ws.map (norm b.mask)).toFinset := by
    ext v
    simp [bank]
  have p := projected sub (eq ▸ nz) run (A := bank b.mask ws.toFinset) (fun _ h => h)
  rw [flat_eq,bank_eq,eq] at p
  have bad := recipe_sound rec p
  exact hb _ (by omega) bad

end PEqualNP.Outside.L_meta_14794.SignedCert

namespace PEqualNP.Outside.L_meta_14794.SignedCert

def sep : List W → W → W → Bool
  | [], p, n => p == 0 || n == 0
  | x::r, p, n => (p == 0 || n == 0) ||
    (sep r (p &&& x) (n &&& x) && sep r (p &&& ~~~x) (n &&& ~~~x))

theorem some_bit {x : W} (hn : x ≠ 0) : ∃ i : Fin 128, x[i.val] = true := by
  by_contra! h
  apply hn
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simpa using h ⟨i,hi⟩

theorem sep_ok {ws : List W} {p n : W}
    (h : ∀ i j : Fin 128, p[i.val] = true → n[j.val] = true → ∃ w ∈ ws, w[i.val] ≠ w[j.val]) :
    sep ws p n = true := by
  induction ws generalizing p n with
  | nil =>
    by_cases hp : p = 0
    · simp [sep,hp]
    by_cases hn : n = 0
    · simp [sep,hn]
    obtain ⟨i,hi⟩ := some_bit hp
    obtain ⟨j,hj⟩ := some_bit hn
    obtain ⟨w,hw,_⟩ := h i j hi hj
    simp at hw
  | cons a ws ih =>
    simp only [sep,Bool.or_eq_true,Bool.and_eq_true]
    right
    constructor
    all_goals
      apply ih
      intro i j hi hj
      simp only [BitVec.getElem_and,BitVec.getElem_not,Bool.and_eq_true,Bool.not_eq_true'] at hi hj
      obtain ⟨w,hw,hd⟩ := h i j hi.1 hj.1
      rcases List.mem_cons.mp hw with e | hm
      · subst w
        exact (hd (hi.2.trans hj.2.symm)).elim
      · exact ⟨w,hm,hd⟩

theorem op_agree {m a b z : W} {i j : Fin 128} (hm : m[i.val] = m[j.val])
    (ha : a[i.val] = a[j.val]) (hb : b[i.val] = b[j.val]) (hz : z ∈ ops m a b) :
    z[i.val] = z[j.val] := by
  obtain ⟨s,t,rfl⟩ := op_cases hz
  obtain ⟨u,e⟩ := norm_cases m (phase s a &&& phase t b)
  rw [e]
  cases s <;> cases t <;> cases u <;> simp only [phase,ite_true,Bool.false_eq_true,ite_false,
    BitVec.getElem_and,BitVec.getElem_not,hm,ha,hb]

theorem sep_live {k : ℕ} {m g : W} {ws : List W} (hr : live (ops m) g k ws.toFinset) :
    sep ws (m &&& g) (m &&& ~~~g) = true := by
  apply sep_ok
  intro i j hi hj
  simp only [BitVec.getElem_and,BitVec.getElem_not,Bool.and_eq_true,Bool.not_eq_true'] at hi hj
  obtain ⟨w,hw,hd⟩ := live_separates (D := fun w : W => w[i.val] ≠ w[j.val])
    (by simp [hi.2,hj.2]) (fun a b z hz h => by
      by_contra! fail
      exact h (op_agree (hi.1.trans hj.1.symm) fail.1 fail.2 hz)) hr
  exact ⟨w,List.mem_toFinset.mp hw,hd⟩

def Canon (m : W) (s : Finset W) : Prop := ∀ w ∈ s, norm m w = w

theorem op_canon {m a b z : W} (h : z ∈ ops m a b) : norm m z = z := by
  obtain ⟨s,t,rfl⟩ := op_cases h
  exact norm_idem .. 

theorem no_zero {k : ℕ} {m g : W} {s : Finset W} (ng : g ≠ 0) (ca : Canon m s)
    (h : live (ops m) g k s) : 0 ∉ s := by
  induction k generalizing s with
  | zero => change s = {g} at h; rw [h]; simpa using Ne.symm ng
  | succ k ih =>
    rcases h with skip | ⟨a,ha,b,hb,_,z,hz,hout,r,hs,tail⟩
    · exact ih ca skip
    intro h0
    rw [hs] at h0
    rcases Finset.mem_insert.mp h0 with e | h0
    · rw [← e] at hz
      rcases op_flat hz with he | he
      · exact hout (he ▸ e ▸ ha)
      · exact hout ((he.trans (ca b hb)) ▸ hb)
    rcases Finset.mem_insert.mp h0 with e | h0
    · rw [op_swap,← e] at hz
      rcases op_flat hz with he | he
      · exact hout (he ▸ e ▸ hb)
      · exact hout ((he.trans (ca a ha)) ▸ ha)
    have cr : Canon m (insert z r) := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hm
      · exact op_canon hz
      · exact ca _ (hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    exact ih cr tail (Finset.mem_insert_of_mem h0)

end PEqualNP.Outside.L_meta_14794.SignedCert

namespace PEqualNP.Outside.L_meta_14794.SignedCert
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

set_option maxRecDepth 100000 in
theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

abbrev Node := List W × List Recipe
def next (m : W) (ws : List W) (h : List Recipe) : List Node :=
  (pairs ws).flatMap fun (a,b,r) =>
    (opList m a b).flatMap fun z =>
      if ws.contains z then [] else
        (keepChoices a b r).map (fun kept => (z::kept, (z,a,b)::h))

def allowed (m g : W) (bounds : List Bound) (k : ℕ) (ws : List W) (h : List Recipe) : Bool :=
  decide (ws.length ≤ k+1) && !ws.contains 0 && sep ws (m &&& g) (m &&& ~~~g) &&
    !bounds.any (fun b => decide (k ≤ b.cost) && cut m g b k ws h)

def walk (m g : W) (bounds : List Bound) : ℕ → List W → List Recipe → Bool
  | 0, ws, _ => ws == [g]
  | k+1, ws, h => ws == [g] || (allowed m g bounds (k+1) ws h &&
      (next m ws h).any (fun st => walk m g bounds k st.1 st.2))

theorem allowed_live {m g : W} {bounds : List Bound} (bv : ∀ b ∈ bounds, Valid b) (gn : g ≠ 0)
    {k : ℕ} {ws : List W} (ca : Canon m ws.toFinset) (nd : ws.Nodup) (h : List Recipe)
    (run : live (ops m) g k ws.toFinset) : allowed m g bounds k ws h = true := by
  have card := live_card run
  rw [List.toFinset_card_of_nodup nd] at card
  have nz := no_zero gn ca run
  have no : bounds.any (fun b => decide (k ≤ b.cost) && cut m g b k ws h) = false := by
    apply List.any_eq_false.mpr
    intro b hb
    by_cases hcut : cut m g b k ws h = true
    · exact (cut_sound (bv b hb) hcut run).elim
    · simp [Bool.eq_false_iff.mpr hcut]
  simp [allowed,card,sep_live run,no]
  exact fun h => nz (List.mem_toFinset.mpr h)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem walk_live {m g : W} {bounds : List Bound} (bv : ∀ b ∈ bounds, Valid b) (gn : g ≠ 0)
    {k : ℕ} {ws : List W} (ca : Canon m ws.toFinset) (nd : ws.Nodup) (h : List Recipe)
    (run : live (ops m) g k ws.toFinset) : walk m g bounds k ws h = true := by
  induction k generalizing ws h with
  | zero =>
    have hs : ws = [g] := singleton_list nd run
    simp [walk,hs]
  | succ k ih =>
    rcases first_live run with done | ⟨a,ha,b,hb,hab,z,hz,hout,need,hs,tail⟩
    · simp [walk,singleton_list nd done]
    have ok := allowed_live bv gn ca nd h run
    simp only [walk,ok,Bool.true_and,Bool.or_eq_true,List.any_eq_true]
    right
    obtain ⟨r,hm,hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
    have go {a b : W} (pm : (a,b,r) ∈ pairs ws) (perm : ws.Perm (a::b::r))
        (hset : ws.toFinset = insert a (insert b need)) (hop : z ∈ ops m a b) :
        ∃ n ∈ next m ws h, walk m g bounds k n.1 n.2 = true := by
      obtain ⟨kept,hk,hnk,hfin⟩ := recover_kept perm nd hset
      have hznew : z ∉ kept := fun hu => hout (hset ▸ Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu)))
      have hnd : (z::kept).Nodup := List.nodup_cons.mpr ⟨hznew,hnk⟩
      have newCa : Canon m (z::kept).toFinset := by
        intro u hu
        rcases List.mem_cons.mp (List.mem_toFinset.mp hu) with rfl | hu
        · exact op_canon hop
        · exact ca _ (hset ▸ Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu)))
      refine ⟨(z::kept,(z,a,b)::h),?_,ih newCa hnd _ (by simpa [hfin] using tail)⟩
      apply List.mem_flatMap.mpr
      refine ⟨(a,b,r),pm,List.mem_flatMap.mpr ⟨z,List.mem_toFinset.mp hop,?_⟩⟩
      have hzws : z ∉ ws := fun hh => hout (List.mem_toFinset.mpr hh)
      simp only [List.contains_iff_mem,hzws,ite_false,List.mem_map]
      exact ⟨kept,hk,rfl⟩
    rcases hm with direct | swap
    · exact go direct hp hs hz
    · exact go swap (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (op_swap m a b ▸ hz)

def verify (m g : W) (bs : List Bound) (k : ℕ) (raw : List W) : Bool :=
  !raw.sublists.any (fun ws => walk m g bs k ws [])

theorem lower_of_verify {m g : W} {bs : List Bound} {raw : List W} {b : ℕ}
    (bv : ∀ c ∈ bs, Valid c) (gn : g ≠ 0) (nd : raw.Nodup) (ca : Canon m raw.toFinset)
    (v : verify m g bs (b-1) raw = true) : Valid ⟨m,raw,g,b⟩ := by
  intro k hk run
  change k < b at hk
  change build (ops m) g k raw.toFinset at run
  have run' := more (show k ≤ b-1 by omega) run
  obtain ⟨s,hs,hl⟩ := compress run'
  classical
  let ws := raw.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have walks :=  walk_live bv gn (ws := ws) (fun w hw => ca w (hs (eq ▸ hw))) (nd.filter _) []
    (eq.symm ▸ hl)
  have yes : raw.sublists.any (fun u => walk m g bs (b-1) u []) = true :=
    List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),walks⟩
  simp [verify,yes] at v

theorem canon_checked {m : W} {xs : List W} (h : xs.all (fun x => norm m x == x) = true) :
    Canon m xs.toFinset := fun w hw => beq_iff_eq.mp (List.all_eq_true.mp h w (List.mem_toFinset.mp hw))

end PEqualNP.Outside.L_meta_14794.SignedCert

namespace PEqualNP.Outside.L_meta_14794.SignedCert.Source
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

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
  · change reachable av (BitVec.allOnes 128 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 128)
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

def bit (k : Fin 128) (z : W) : Bool := z[k.val]
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

set_option maxRecDepth 100000 in
private theorem read_bit (w : List W) (i : ℕ) (k : Fin 128) :
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
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 128) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#128)[k.val] = false; simp
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
theorem compile (goal : W) (nz : ~~~goal ≠ 0) (no : ~~~goal ≠ ~~~0) (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
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
    · exact False.elim (nz zero)
    · exact False.elim (no ones)
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


theorem source_op {m a b z : W} (hz : z ∈ basicOps a b) :
    norm m z ∈ PEqualNP.Outside.L_meta_14794.SignedCert.ops m (norm m a) (norm m b) := by
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact norm_gate m a b false false
  · have h := norm_gate m a b true true
    change norm m (~~~a &&& ~~~b) ∈ _ at h
    simpa only [← BitVec.not_or,norm_neg] using h
  · exact norm_gate m a b false true
  · rw [BitVec.and_comm]
    exact norm_gate m a b true false

theorem to_canonical {m t : W} {k : ℕ} {S : Finset W} (run : build basicOps t k S) :
    build (PEqualNP.Outside.L_meta_14794.SignedCert.ops m) (norm m t) k (bank m S) := by
  induction k generalizing S with
  | zero => exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ run)
  | succ k ih =>
    rcases run with skip | ⟨a,ha,b,hb,_,z,hz,tail⟩
    · exact Or.inl (ih skip)
    have next := ih tail
    have eq : bank m (insert z S) = insert (norm m z) (bank m S) := by
      simp only [bank,Finset.image_insert,Finset.insert_comm (0 : W) (norm m z)]
    rw [eq] at next
    have am : norm m a ∈ bank m S := Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ ha)
    have bm : norm m b ∈ bank m S := Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hb)
    have op := source_op (m := m) hz
    by_cases he : norm m a = norm m b
    · rw [he] at op
      have mem : norm m z ∈ bank m S := by
        rcases op_same op with zz | zz
        · rw [zz]; exact Finset.mem_insert_self ..
        · rw [zz,norm_idem]; exact bm
      rw [Finset.insert_eq_of_mem mem] at next
      exact Or.inl next
    · exact Or.inr ⟨_,am,_,bm,he,_,op,next⟩

theorem binary_lb {b : Bound} (valid : Valid b) (w : W) (raw : List W) (F : (Fin 8 → Bool) → Bool)
    (nz : w ≠ 0) (no : w ≠ ~~~0) (dim : raw.length = 8)
    (stk : bank b.mask raw.toFinset ⊆ b.inputs.toFinset) (tg : norm b.mask w = b.goal)
    (rows : ∀ k : Fin 128, F (fun i => bit k (raw.getD i.val 0)) = bit k w)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (evals : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = F x) : b.cost ≤ binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ raw, holds raw.toFinset u := fun u hu =>
    .inr (.inr ⟨u,List.mem_toFinset.mpr hu,.inl rfl⟩)
  have eval (k : Fin 128) :
      (gs.foldl step (raw.map (bit k))).getD o false = bit k (~~~(~~~w)) := by
    let x (i : Fin 8) := bit k (raw.getD i.val 0)
    have same : List.ofFn x = raw.map (bit k) := by
      apply List.ext_getElem
      · simp [dim]
      · intro i hi hj
        have hi' : i < raw.length := by simpa using hj
        simp only [List.getElem_ofFn,List.getElem_map,x,List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hi',Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (raw.map (bit k)) = _
    rw [← same,evals,BitVec.not_not]
    exact rows k
  obtain ⟨t,ht,run⟩ := compile (~~~w) (by simpa only [BitVec.not_not] using nz)
    (by simpa only [BitVec.not_not] using no) gs o hg raw raw.toFinset init eval
  have can := enlarge stk (to_canonical (m := b.mask) run)
  rcases ht with rfl | rfl <;> simp only [BitVec.not_not,norm_neg,tg] at can
  all_goals exact valid _ low can

end PEqualNP.Outside.L_meta_14794.SignedCert.Source

namespace PEqualNP.Outside.L_meta_14794.SignedCert
abbrev Cell := ℕ × List W
def Closed (m g : W) (c : Cell) : Prop := c.2.Nodup → Canon m c.2.toFinset → ¬live (ops m) g c.1 c.2.toFinset

theorem has_child {m g : W} {k : ℕ} {ws : List W} (ca : Canon m ws.toFinset) (nd : ws.Nodup)
    (h : List Recipe) (neq : ws ≠ [g]) (run : live (ops m) g (k+1) ws.toFinset) :
    ∃ n ∈ next m ws h, n.1.Nodup ∧ Canon m n.1.toFinset ∧ live (ops m) g k n.1.toFinset := by
    rcases first_live run with done | ⟨a,ha,b,hb,hab,z,hz,hout,need,hs,tail⟩
    · exact (neq (singleton_list nd done)).elim
    obtain ⟨r,hm,hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
    have go {a b : W} (pm : (a,b,r) ∈ pairs ws) (perm : ws.Perm (a::b::r))
        (hset : ws.toFinset = insert a (insert b need)) (hop : z ∈ ops m a b) :
        ∃ n ∈ next m ws h, n.1.Nodup ∧ Canon m n.1.toFinset ∧ live (ops m) g k n.1.toFinset := by
      obtain ⟨kept,hk,hnk,hfin⟩ := recover_kept perm nd hset
      have hznew : z ∉ kept := fun hu => hout (hset ▸ Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu)))
      have hnd : (z::kept).Nodup := List.nodup_cons.mpr ⟨hznew,hnk⟩
      have newCa : Canon m (z::kept).toFinset := by
        intro u hu
        rcases List.mem_cons.mp (List.mem_toFinset.mp hu) with rfl | hu
        · exact op_canon hop
        · exact ca _ (hset ▸ Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu)))
      refine ⟨(z::kept,(z,a,b)::h),?_,hnd,newCa,(by simpa [hfin] using tail)⟩
      apply List.mem_flatMap.mpr
      refine ⟨(a,b,r),pm,List.mem_flatMap.mpr ⟨z,List.mem_toFinset.mp hop,?_⟩⟩
      have hzws : z ∉ ws := fun hh => hout (List.mem_toFinset.mpr hh)
      simp only [List.contains_iff_mem,hzws,ite_false,List.mem_map]
      exact ⟨kept,hk,rfl⟩
    rcases hm with direct | swap
    · exact go direct hp hs hz
    · exact go swap (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (op_swap m a b ▸ hz)

def trivialClose (g : W) (k : ℕ) (ws : List W) : Bool :=
  (k == 0 && ws != [g]) || decide (k+1 < ws.length) || ws.contains 0

theorem trivial_sound {m g : W} {k : ℕ} {ws : List W} (gn : g ≠ 0)
    (yes : trivialClose g k ws = true) : Closed m g (k,ws) := by
  intro nd ca run
  change ws.Nodup at nd
  simp only [trivialClose,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,bne_iff_ne,
    List.contains_iff_mem,decide_eq_true_eq] at yes
  rcases yes with (⟨rfl,hn⟩ | size) | hzro
  · exact hn (singleton_list nd run)
  · have card := live_card run
    change ws.toFinset.card ≤ k+1 at card
    rw [List.toFinset_card_of_nodup nd] at card
    omega
  · exact no_zero gn ca run (List.mem_toFinset.mpr hzro)

def clash (m g : W) (ws : List W) (t : ℕ) : Bool :=
  let i := t % 128
  let j := t / 128 % 128
  (m.getLsbD i == m.getLsbD j) && (g.getLsbD i != g.getLsbD j) &&
    ws.all (fun x => x.getLsbD i == x.getLsbD j)

theorem clash_sound {m g : W} {ws : List W} {t k : ℕ}
    (yes : clash m g ws t = true) : Closed m g (k,ws) := by
  intro _ _ run
  let i : Fin 128 := ⟨t%128,Nat.mod_lt _ (by decide)⟩
  let j : Fin 128 := ⟨t/128%128,Nat.mod_lt _ (by decide)⟩
  simp only [clash,Bool.and_eq_true,beq_iff_eq,bne_iff_ne] at yes
  have hm : m[i.val] = m[j.val] := yes.1.1
  have hg : g[i.val] ≠ g[j.val] := yes.1.2
  obtain ⟨w,hw,hd⟩ := live_separates (D := fun w : W => w[i.val] ≠ w[j.val]) hg
    (fun a b z hz hh => by
      by_contra! fail
      exact hh (op_agree hm fail.1 fail.2 hz)) run
  exact hd (beq_iff_eq.mp (List.all_eq_true.mp yes.2 w (List.mem_toFinset.mp hw)))

def sameCell (k : ℕ) (ws : List W) (c : Cell) : Bool :=
  k == c.1 && ws.all (fun w => c.2.contains w) && c.2.all (fun w => ws.contains w)

theorem same_sound {m g : W} {k : ℕ} {ws : List W} {c : Cell} (v : Closed m g c)
    (nd : c.2.Nodup) (yes : sameCell k ws c = true) : Closed m g (k,ws) := by
  intro _ ca run
  simp only [sameCell,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,List.contains_iff_mem] at yes
  have eq : ws.toFinset = c.2.toFinset := by
    ext w
    simpa only [List.mem_toFinset] using Iff.intro (yes.1.2 w) (yes.2 w)
  apply v nd
  · change Canon m ws.toFinset at ca
    rwa [← eq]
  · change live (ops m) g k ws.toFinset at run
    rwa [← yes.1.1, ← eq]

def tag (m g : W) (bs : List Bound) (seen : List Cell) (k : ℕ) (n : Node) (t : ℕ) : Bool :=
  if t = 0 then trivialClose g k n.1
  else if t ≤ 16384 then clash m g n.1 (t-1)
  else if t < 32768 then (bs[t-16385]?).any (fun b => cut m g b k n.1 n.2)
  else (seen[t-32768]?).any (sameCell k n.1)

theorem tag_sound {m g : W} {bs : List Bound} {seen : List Cell} {k : ℕ} {n : Node} {t : ℕ}
    (gn : g ≠ 0) (bv : ∀ b ∈ bs, Valid b) (sv : ∀ c ∈ seen, c.2.Nodup ∧ Closed m g c)
    (h : tag m g bs seen k n t = true) : Closed m g (k,n.1) := by
  unfold tag at h
  split at h
  · exact trivial_sound gn h
  split at h
  · exact clash_sound h
  split at h
  · cases eq : bs[t-16385]? with
    | none => simp [eq] at h
    | some b =>
      rw [eq] at h
      exact fun _ _ => cut_sound (bv b (List.mem_of_getElem? eq)) h
  · cases eq : seen[t-32768]? with
    | none => simp [eq] at h
    | some c =>
      rw [eq] at h
      have ok := sv c (List.mem_of_getElem? eq)
      exact same_sound ok.2 ok.1 h

def tags (check : Node → ℕ → Bool) : List Node → ℕ → Bool
  | [], _ => true
  | n::ns, p => check n (p % 65536) && tags check ns (p >>> 16)

theorem tags_all {check : Node → ℕ → Bool} {P : Node → Prop} (sound : ∀ n t, check n t = true → P n)
    {ns : List Node} {p : ℕ} (ok : tags check ns p = true) : ∀ n ∈ ns, P n := by
  induction ns generalizing p with
  | nil => simp
  | cons n ns ih =>
    simp only [tags,Bool.and_eq_true] at ok
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact sound _ _ ok.1
    · exact ih ok.2 _ hx

theorem cell_of_tags {m g : W} {bs : List Bound} {seen : List Cell} {k : ℕ} {ws : List W}
    (gn : g ≠ 0) (bv : ∀ b ∈ bs, Valid b) (sv : ∀ c ∈ seen, c.2.Nodup ∧ Closed m g c)
    (h : List Recipe) (p : ℕ) (neq : ws ≠ [g])
    (ok : tags (tag m g bs seen k) (next m ws h) p = true) : Closed m g (k+1,ws) := by
  intro nd ca run
  obtain ⟨n,hn,hd,hc,liveN⟩ := has_child ca nd h neq run
  exact tags_all (fun _ _ yes => tag_sound gn bv sv yes) ok n hn hd hc liveN

theorem bound_of_tags {m g : W} {bs : List Bound} {seen : List Cell} {b : ℕ} {raw : List W}
    (gn : g ≠ 0) (bv : ∀ c ∈ bs, Valid c) (sv : ∀ c ∈ seen, c.2.Nodup ∧ Closed m g c)
    (nd : raw.Nodup) (ca : Canon m raw.toFinset) (p : ℕ)
    (ok : tags (tag m g bs seen (b-1)) (raw.sublists.map (fun ws => (ws,[]))) p = true) :
    Valid ⟨m,raw,g,b⟩ := by
  intro k hk run
  change k < b at hk
  change build (ops m) g k raw.toFinset at run
  obtain ⟨s,hs,hl⟩ := compress (more (show k ≤ b-1 by omega) run)
  classical
  let ws := raw.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have mem : (ws,([] : List Recipe)) ∈ raw.sublists.map (fun us => (us,[])) :=
    List.mem_map.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),rfl⟩
  exact tags_all (fun _ _ yes => tag_sound gn bv sv yes) ok _ mem (nd.filter _)
    (fun w hw => ca w (hs (eq ▸ hw))) (eq.symm ▸ hl)

theorem familyNil {α : Type} {P : α → Prop} : ∀ x ∈ ([] : List α), P x := by simp

theorem familyCons {α : Type} {P : α → Prop} {a : α} {xs : List α} (v : P a)
    (vs : ∀ x ∈ xs, P x) : ∀ x ∈ a::xs, P x := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact v
  · exact vs x hx

end PEqualNP.Outside.L_meta_14794.SignedCert

namespace PEqualNP.Outside.L_meta_14794.SignedCert

def smallTag (m g : W) (bs : List Bound) (seen : List Cell) (k : ℕ) (n : Node) (t : ℕ) : Bool :=
  if t = 0 then trivialClose g k n.1 || !sep n.1 (m &&& g) (m &&& ~~~g)
  else if t ≤ bs.length then (bs[t-1]?).any (fun b => cut m g b k n.1 n.2)
  else (seen[t-(bs.length+1)]?).any (sameCell k n.1)

theorem small_sound {m g : W} {bs : List Bound} {seen : List Cell} {k : ℕ} {n : Node} {t : ℕ}
    (gn : g ≠ 0) (bv : ∀ b ∈ bs, Valid b) (sv : ∀ c ∈ seen, c.2.Nodup ∧ Closed m g c)
    (h : smallTag m g bs seen k n t = true) : Closed m g (k,n.1) := by
  unfold smallTag at h
  split at h
  · rcases Bool.or_eq_true_iff.mp h with close | sepFail
    · exact trivial_sound gn close
    · intro _ _ run
      simp [sep_live run] at sepFail
  split at h
  · cases eq : bs[t-1]? with
    | none => simp [eq] at h
    | some b =>
      rw [eq] at h
      exact fun _ _ => cut_sound (bv b (List.mem_of_getElem? eq)) h
  · cases eq : seen[t-(bs.length+1)]? with
    | none => simp [eq] at h
    | some c =>
      rw [eq] at h
      have ok := sv c (List.mem_of_getElem? eq)
      exact same_sound ok.2 ok.1 h
def smallTags (width : ℕ) (check : Node → ℕ → Bool) : List Node → ℕ → Bool
  | [], _ => true
  | n::ns, p => check n (p % (2^width)) && smallTags width check ns (p >>> width)

theorem smallTags_all {width : ℕ} {check : Node → ℕ → Bool} {P : Node → Prop} (sound : ∀ n t, check n t = true → P n)
    {ns : List Node} {p : ℕ} (ok : smallTags width check ns p = true) : ∀ n ∈ ns, P n := by
  induction ns generalizing p with
  | nil => simp
  | cons n ns ih =>
    simp only [smallTags,Bool.and_eq_true] at ok
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact sound _ _ ok.1
    · exact ih ok.2 _ hx

theorem small_cell {m g : W} {bs : List Bound} {seen : List Cell} {k : ℕ} {ws : List W}
    (gn : g ≠ 0) (bv : ∀ b ∈ bs, Valid b) (sv : ∀ c ∈ seen, c.2.Nodup ∧ Closed m g c)
    (h : List Recipe) (width p : ℕ) (neq : ws ≠ [g])
    (ok : smallTags width (smallTag m g bs seen k) (next m ws h) p = true) : Closed m g (k+1,ws) := by
  intro nd ca run
  obtain ⟨n,hn,hd,hc,liveN⟩ := has_child ca nd h neq run
  exact smallTags_all (fun _ _ yes => small_sound gn bv sv yes) ok n hn hd hc liveN

theorem small_bound {m g : W} {bs : List Bound} {seen : List Cell} {b : ℕ} {raw : List W}
    (gn : g ≠ 0) (bv : ∀ c ∈ bs, Valid c) (sv : ∀ c ∈ seen, c.2.Nodup ∧ Closed m g c)
    (nd : raw.Nodup) (ca : Canon m raw.toFinset) (width p : ℕ)
    (ok : smallTags width (smallTag m g bs seen (b-1)) (raw.sublists.map (fun ws => (ws,[]))) p = true) :
    Valid ⟨m,raw,g,b⟩ := by
  intro k hk run
  change k < b at hk
  change build (ops m) g k raw.toFinset at run
  obtain ⟨s,hs,hl⟩ := compress (more (show k ≤ b-1 by omega) run)
  classical
  let ws := raw.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have mem : (ws,([] : List Recipe)) ∈ raw.sublists.map (fun us => (us,[])) :=
    List.mem_map.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),rfl⟩
  exact smallTags_all (fun _ _ yes => small_sound gn bv sv yes) ok _ mem (nd.filter _)
    (fun w hw => ca w (hs (eq ▸ hw))) (eq.symm ▸ hl)


end PEqualNP.Outside.L_meta_14794.SignedCert

namespace PEqualNP.Outside.L_meta_14794.SignedCert

def keepBudget (k : ℕ) (a b : W) (r : List W) : List (List W) :=
  if r.length+2 ≤ k then [r,a::r,b::r,a::b::r]
  else if r.length+1 ≤ k then [r,a::r,b::r]
  else if r.length ≤ k then [r] else []

theorem mem_keepBudget {k : ℕ} {a b : W} {r kept : List W} (hk : kept.length ≤ k)
    (h : kept ∈ keepChoices a b r) : kept ∈ keepBudget k a b r := by
  simp only [keepChoices,List.mem_cons,List.not_mem_nil,or_false] at h
  unfold keepBudget
  split
  · simpa only [List.mem_cons,List.not_mem_nil,or_false] using h
  split
  · rcases h with rfl | rfl | rfl | rfl <;> simp_all <;> omega
  split
  · rcases h with rfl | rfl | rfl | rfl <;> simp_all <;> omega
  · rcases h with rfl | rfl | rfl | rfl <;> simp_all <;> omega

def budgetNext (m : W) (k : ℕ) (ws : List W) (h : List Recipe) : List Node :=
  (pairs ws).flatMap fun (a,b,r) =>
    let kept := keepBudget k a b r
    (opList m a b).flatMap fun z =>
      if ws.contains z then [] else kept.map (fun w => (z::w,(z,a,b)::h))

theorem mem_budgetNext {m : W} {k : ℕ} {ws : List W} {h : List Recipe} {n : Node}
    (mem : n ∈ next m ws h) (nd : n.1.Nodup) {g : W} (run : live (ops m) g k n.1.toFinset) :
    n ∈ budgetNext m k ws h := by
  have size := live_card run
  rw [List.toFinset_card_of_nodup nd] at size
  obtain ⟨⟨a,b,r⟩,ha,hn⟩ := List.mem_flatMap.mp mem
  obtain ⟨z,hz,hn⟩ := List.mem_flatMap.mp hn
  split at hn
  · contradiction
  · rename_i miss
    obtain ⟨kept,hk,rfl⟩ := List.mem_map.mp hn
    apply List.mem_flatMap.mpr
    refine ⟨(a,b,r),ha,List.mem_flatMap.mpr ⟨z,hz,?_⟩⟩
    simp only [miss,Bool.false_eq_true,ite_false,List.mem_map]
    exact ⟨kept,mem_keepBudget (by simpa using size) hk,rfl⟩

end PEqualNP.Outside.L_meta_14794.SignedCert

namespace PEqualNP.Outside.L_meta_14794.SignedCert

abbrev ColorPair := W × W
def mixed : List W → W → W → List ColorPair
  | [], p, n => if p==0 || n==0 then [] else [(p,n)]
  | w::r, p, n => if p==0 || n==0 then [] else
      mixed r (p &&& w) (n &&& w) ++ mixed r (p &&& ~~~w) (n &&& ~~~w)

def resolves (z : W) (c : ColorPair) : Bool :=
  ((c.1 &&& z) == 0 || (c.2 &&& z) == 0) && ((c.1 &&& ~~~z) == 0 || (c.2 &&& ~~~z) == 0)

theorem mixed_resolves (r : List W) (z p n : W) :
    (mixed r p n).all (resolves z) = sep (r++[z]) p n := by
  induction r generalizing p n with
  | nil =>
    simp only [List.nil_append,mixed,sep]
    cases e : (p==0 || n==0) <;> simp [e,resolves]
  | cons w r ih =>
    simp only [mixed,List.cons_append,sep]
    cases e : (p==0 || n==0) <;> simp [e,List.all_append,ih]

def smartNext (m g : W) (k : ℕ) (ws : List W) (h : List Recipe) : List Node :=
  (pairs ws).flatMap fun (a,b,r) =>
    let pools := (keepBudget k a b r).map (fun kept => (kept,mixed kept (m &&& g) (m &&& ~~~g)))
    (opList m a b).flatMap fun z =>
      if ws.contains z || z == 0 then [] else
        (pools.filter (fun v => v.2.all (resolves z))).map (fun v => (z::v.1,(z,a,b)::h))

theorem mem_smartNext {m g : W} {k : ℕ} {ws : List W} {h : List Recipe} {n : Node}
    (gn : g ≠ 0) (mem : n ∈ budgetNext m k ws h) (ca : Canon m n.1.toFinset)
    (run : live (ops m) g k n.1.toFinset) : n ∈ smartNext m g k ws h := by
  obtain ⟨⟨a,b,r⟩,ha,hn⟩ := List.mem_flatMap.mp mem
  obtain ⟨z,hz,hn⟩ := List.mem_flatMap.mp hn
  split at hn
  · contradiction
  · rename_i miss
    obtain ⟨kept,hk,rfl⟩ := List.mem_map.mp hn
    have nz : z ≠ 0 := by
      intro e
      apply no_zero gn ca run
      simp [e]
    have eq : (kept++[z]).toFinset = (z::kept).toFinset := by ext w; simp [or_comm]
    have good := sep_live (ws := kept++[z]) (m := m) (g := g) (k := k)
      (by rw [eq]; exact run)
    rw [← mixed_resolves] at good
    apply List.mem_flatMap.mpr
    refine ⟨(a,b,r),ha,List.mem_flatMap.mpr ⟨z,hz,?_⟩⟩
    simp only [miss,beq_iff_eq.mpr,beq_eq_false_iff_ne.mpr nz,Bool.false_or,Bool.false_eq_true,ite_false,List.mem_map]
    refine ⟨(kept,mixed kept (m &&& g) (m &&& ~~~g)),List.mem_filter.mpr ⟨?_,good⟩,rfl⟩
    exact List.mem_map.mpr ⟨kept,hk,rfl⟩

end PEqualNP.Outside.L_meta_14794.SignedCert

namespace PEqualNP.Outside.L_meta_14794.SignedCert

def evalWord {α : Type} (w : W) (f : W → α) : α :=
  Nat.rec (f 0) (fun j _ => f (BitVec.ofNat 128 (j+1))) w.toNat

theorem evalWord_eq {α : Type} (w : W) (f : W → α) : evalWord w f = f w := by
  unfold evalWord
  generalize h : w.toNat = t
  cases t with
  | zero =>
    change f 0 = f w
    apply congrArg f
    exact BitVec.eq_of_toNat_eq (by simpa using h.symm)
  | succ t =>
    change f (BitVec.ofNat 128 (t+1)) = f w
    rw [← h]
    simp

def cachedMixed : List W → W → W → List ColorPair
  | [], p, n => evalWord p (fun pp => evalWord n (fun nn => if pp==0 || nn==0 then [] else [(pp,nn)]))
  | w::r, p, n => evalWord p (fun pp => evalWord n (fun nn =>
      if pp==0 || nn==0 then [] else
        cachedMixed r (pp &&& w) (nn &&& w) ++ cachedMixed r (pp &&& ~~~w) (nn &&& ~~~w)))

theorem cached_eq (r : List W) (p n : W) : cachedMixed r p n = mixed r p n := by
  induction r generalizing p n <;> simp [cachedMixed,mixed,evalWord_eq, *]

def cachedNext (m g : W) (k : ℕ) (ws : List W) (h : List Recipe) : List Node :=
  (pairs ws).flatMap fun (a,b,r) =>
    let pools := (keepBudget k a b r).map (fun kept => (kept,cachedMixed kept (m &&& g) (m &&& ~~~g)))
    (opList m a b).flatMap fun w => evalWord w (fun z =>
      if ws.contains z || z == 0 then [] else
        (pools.filter (fun v => v.2.all (resolves z))).map (fun v => (z::v.1,(z,a,b)::h)))

theorem cachedNext_eq (m g : W) (k : ℕ) (ws : List W) (h : List Recipe) :
    cachedNext m g k ws h = smartNext m g k ws h := by simp [cachedNext,smartNext,cached_eq,evalWord_eq]
end PEqualNP.Outside.L_meta_14794.SignedCert

namespace PEqualNP.Outside.L_meta_14794.SignedCert

def flatCount (q : W) (s : Finset W) := (s.filter (fun w => norm q w = 0)).card

theorem count_nonzero {q w : W} {s : Finset W} (nw : norm q w ≠ 0) :
    flatCount q (insert w s) = flatCount q s := by simp only [flatCount,Finset.filter_insert,if_neg nw]
theorem count_zero {q w : W} {s : Finset W} (nz : norm q w = 0) (fresh : w ∉ s) :
    flatCount q (insert w s) = flatCount q s + 1 := by simp [flatCount,Finset.filter_insert,nz,fresh]
theorem count_step (q w : W) (s : Finset W) : flatCount q (insert w s) ≤ flatCount q s + 1 := by
  by_cases inside : w ∈ s
  · simp [Finset.insert_eq_of_mem inside]
  by_cases flat : norm q w = 0
  · rw [count_zero flat inside]
  · rw [count_nonzero flat]; omega

theorem count_saved {m q g : W} {k : ℕ} {s : Finset W} (sub : q &&& m = q) (nz : norm q g ≠ 0)
    (run : live (ops m) g k s) {A : Finset W} (hs : bank q s ⊆ A) :
    ∃ t, t + flatCount q s ≤ k ∧ build (ops q) (norm q g) t A := by
  induction k generalizing s A with
  | zero =>
    change s = {g} at run
    subst s
    refine ⟨0,?_,hs (by simp [bank])⟩
    simp [flatCount]
    exact nz
  | succ k ih =>
    rcases run with skip | ⟨a,ha,b,hb,_,z,hz,hnew,r,he,tail⟩
    · obtain ⟨t,h,got⟩ := ih skip hs
      exact ⟨t,by omega,got⟩
    subst s
    have op := proj_op sub hz
    have am : norm q a ∈ A := hs (by simp [bank])
    have bm : norm q b ∈ A := hs (by simp [bank])
    have zero : (0 : W) ∈ A := hs (by simp [bank])
    have fresh : z ∉ r := fun h => hnew (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    by_cases free : norm q z ∈ A
    · obtain ⟨t,ht,hbuild⟩ := ih tail (tailBank hs free)
      refine ⟨t,?_,hbuild⟩
      have h1 := count_step q a (insert b r)
      have h2 := count_step q b r
      have mono : flatCount q r ≤ flatCount q (insert z r) := Finset.card_le_card
        (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
      by_cases af : norm q a = 0
      · by_cases bf : norm q b = 0
        · rw [af,bf] at op
          have zf : norm q z = 0 := by
            rcases op_flat op with s | s
            · exact s
            · simpa only [norm_zero] using s
          rw [count_zero zf fresh] at ht
          omega
        · rw [count_nonzero bf] at h1
          omega
      · rw [count_nonzero af]
        omega
    · have zn : norm q z ≠ 0 := fun e => free (e ▸ zero)
      have an : norm q a ≠ 0 := by
        intro e
        rw [e] at op
        rcases op_flat op with eq | eq
        · exact zn eq
        · exact free (by rw [eq,norm_idem]; exact bm)
      have bn : norm q b ≠ 0 := by
        intro e
        rw [op_swap q,e] at op
        rcases op_flat op with eq | eq
        · exact zn eq
        · exact free (by rw [eq,norm_idem]; exact am)
      have ne : norm q a ≠ norm q b := by
        intro e
        rw [e] at op
        rcases op_same op with eq | eq
        · exact zn eq
        · exact free (by rw [eq,norm_idem]; exact bm)
      obtain ⟨t,ht,hbld⟩ := ih tail (tailBank (hs.trans (Finset.subset_insert (norm q z) A)) (Finset.mem_insert_self ..))
      rw [count_nonzero zn] at ht
      refine ⟨t+1,?_,Or.inr ⟨_,am,_,bm,ne,_,op,hbld⟩⟩
      rw [count_nonzero an,count_nonzero bn]; omega

def multiCut (m g : W) (b : Bound) (k : ℕ) (ws : List W) (h : List Recipe) : Bool :=
  let q := b.mask
  let left := k - (ws.filter (fun a => norm q a == 0)).length
  ((q &&& m) == q) && ((norm q g) == b.goal) && (b.goal != 0) && decide (left < b.cost) &&
    recipe q b.inputs h (0 :: ws.map (norm q)) (b.cost-1-left)

theorem multi_sound {m g : W} {b : Bound} {k : ℕ} {ws : List W} {h : List Recipe} (vb : Valid b)
    (ok : multiCut m g b k ws h = true) (nd : ws.Nodup) (run : live (ops m) g k ws.toFinset) : False := by
  simp only [multiCut,Bool.and_eq_true,beq_iff_eq,bne_iff_ne,decide_eq_true_eq] at ok
  obtain ⟨⟨⟨⟨sub,eq⟩,nz⟩,low⟩,rec⟩ := ok
  have fc : flatCount b.mask ws.toFinset = (ws.filter (fun a => norm b.mask a == 0)).length := by
    have same : ws.toFinset.filter (fun a => norm b.mask a = 0) = (ws.filter (fun a => norm b.mask a == 0)).toFinset := by
      ext a; simp
    rw [flatCount,same,List.toFinset_card_of_nodup (nd.filter _)]
  have bank_eq : bank b.mask ws.toFinset = (0 :: ws.map (norm b.mask)).toFinset := by ext v; simp [bank]
  obtain ⟨t,small,proj⟩ := count_saved sub (eq ▸ nz) run (A := bank b.mask ws.toFinset) (fun _ h => h)
  rw [fc] at small
  rw [bank_eq,eq] at proj
  have rebuilt := recipe_sound rec proj
  exact vb _ (by omega) rebuilt
end PEqualNP.Outside.L_meta_14794.SignedCert

namespace PEqualNP.Outside.L_meta_14794.SignedCert

abbrev RecordPage := Array (ℕ × ℕ)
abbrev Records := Array RecordPage

def getRecord (rs : Records) (i : ℕ) : Option (ℕ × ℕ) :=
  (rs[i/32]?).bind (fun page => page[i%32]?)

theorem below_capacity {rs : Records} {i : ℕ} {r : ℕ × ℕ} (h : getRecord rs i = some r) :
    i < rs.size * 32 := by
  unfold getRecord at h
  cases eq : rs[i/32]? with
  | none => simp [eq] at h
  | some a =>
    have bound := (Array.getElem?_eq_some_iff.mp eq).1
    omega

def materialize {α : Type} (w : W) (f : W → α) : α :=
  Nat.rec (f 0) (fun j _ => f (BitVec.ofNat 128 (j+1))) w.toNat

def initialWords : List W → ℕ → List W
  | [], _ => []
  | w::ws, p => if p%2=1 then w :: initialWords ws (p >>> 1) else initialWords ws (p >>> 1)

def replayOne (m : W) (n : Node) (tok : ℕ) : Node :=
  let a := n.1.getD (tok % 16) 0
  let b := n.1.getD (tok >>> 4 % 16) 0
  let z := (opList m a b).getD (tok >>> 8 % 4) 0
  let r := (n.1.erase a).erase b
  let kept := (keepChoices a b r).getD (tok >>> 10 % 4) []
  materialize z (fun value => (value::kept,(value,a,b)::n.2))

def replayTail (m : W) : ℕ → ℕ → Node → Node
  | 0, _, n => n
  | d+1, p, n => replayTail m d (p >>> 12) (replayOne m n (p % 4096))

def replay (b : Bound) (k p : ℕ) : Node :=
  replayTail b.mask (b.cost-1-k) (p >>> 8) (initialWords b.inputs (p % 256),[])

def recorded (b : Bound) (k : ℕ) (rs : Records) (i : ℕ) : Option Cell :=
  (getRecord rs i).map (fun r => (k,(replay b k r.1).1))

def LayerOK (b : Bound) (k : ℕ) (rs : Records) : Prop :=
  ∀ i c, recorded b k rs i = some c → c.2.Nodup ∧ Closed b.mask b.goal c

def cheap (m g : W) (k : ℕ) (ws : List W) : Bool :=
  trivialClose g k ws || !sep ws (m &&& g) (m &&& ~~~g)

theorem cheap_sound {m g : W} {k : ℕ} {ws : List W} (gn : g ≠ 0)
    (ok : cheap m g k ws = true) : Closed m g (k,ws) := by
  rcases Bool.or_eq_true_iff.mp ok with stop | fail
  · exact trivial_sound gn stop
  · intro _ _ run
    simp [sep_live run] at fail

def skipNode (checkSep : Bool) (b : Bound) (k : ℕ) (ws : List W) : Bool :=
  if checkSep then cheap b.mask b.goal k ws else trivialClose b.goal k ws

def sparse (checkSep : Bool) (b : Bound) (bs : Array Bound) (k : ℕ) (old : Records) (cw rw : ℕ) :
    List Node → ℕ → Bool
  | [], _ => true
  | n::ns, p =>
    if skipNode checkSep b k n.1 then sparse checkSep b bs k old cw rw ns p
    else if p % 2 = 0 then
      (bs[(p >>> 1) % 2^cw]?).any (fun s => multiCut b.mask b.goal s k n.1 n.2) &&
        sparse checkSep b bs k old cw rw ns (p >>> (cw+1))
    else
      (recorded b k old ((p >>> 1) % 2^rw)).any (sameCell k n.1) &&
        sparse checkSep b bs k old cw rw ns (p >>> (rw+1))

theorem sparse_sound {checkSep : Bool} {b : Bound} {bs : Array Bound} {old : Records} {k cw rw : ℕ}
    (gn : b.goal ≠ 0) (bv : ∀ s ∈ bs, Valid s) (prev : LayerOK b k old)
    {ns : List Node} {p : ℕ} (ok : sparse checkSep b bs k old cw rw ns p = true) :
    ∀ n ∈ ns, Closed b.mask b.goal (k,n.1) := by
  induction ns generalizing p with
  | nil => simp
  | cons a ns ih =>
    have comb (ha : Closed b.mask b.goal (k,a.1)) {p' : ℕ} (rest : sparse checkSep b bs k old cw rw ns p' = true) :
        ∀ n ∈ a::ns, Closed b.mask b.goal (k,n.1) := by
      intro n h
      rcases List.mem_cons.mp h with rfl | h
      · exact ha
      · exact ih rest n h
    simp only [sparse] at ok
    split at ok
    · rename_i cc
      cases checkSep with
      | false => exact comb (trivial_sound gn cc) ok
      | true => exact comb (cheap_sound gn cc) ok
    split at ok
    · simp only [Bool.and_eq_true] at ok
      apply comb _ ok.2
      obtain ⟨yes,_⟩ := ok
      generalize ee : bs[(p >>> 1) % 2^cw]? = x at yes
      cases x with
      | none => contradiction
      | some s => exact fun nd _ => multi_sound (bv s (Array.mem_of_getElem? ee)) yes nd
    · simp only [Bool.and_eq_true] at ok
      apply comb _ ok.2
      obtain ⟨yes,_⟩ := ok
      generalize ee : recorded b k old ((p >>> 1) % 2^rw) = x at yes
      cases x with
      | none => contradiction
      | some c =>
        have h := prev _ _ ee
        exact same_sound h.2 h.1 yes

def rowCheck (b : Bound) (bs : Array Bound) (k : ℕ) (old : Records) (cw rw : ℕ) (rec : ℕ × ℕ) : Bool :=
  let n := replay b (k+1) rec.1
  decide n.1.Nodup && n.1 != [b.goal] && sparse false b bs k old cw rw (cachedNext b.mask b.goal k n.1 n.2) rec.2

theorem row_sound {b : Bound} {bs : Array Bound} {old : Records} {k cw rw : ℕ}
    (gn : b.goal ≠ 0) (bv : ∀ s ∈ bs, Valid s) (prev : LayerOK b k old)
    {r : ℕ × ℕ} (ok : rowCheck b bs k old cw rw r = true) :
    (replay b (k+1) r.1).1.Nodup ∧ Closed b.mask b.goal (k+1,(replay b (k+1) r.1).1) := by
  simp only [rowCheck,Bool.and_eq_true,decide_eq_true_eq,bne_iff_ne] at ok
  refine ⟨ok.1.1,fun nd ca run => ?_⟩
  obtain ⟨n,hn,hd,hc,hr⟩ := has_child ca nd (replay b (k+1) r.1).2 ok.1.2 run
  exact sparse_sound gn bv prev ok.2 n ((cachedNext_eq ..) ▸ mem_smartNext gn (mem_budgetNext hn hd hr) hc hr) hd hc hr

def checkBlock (f : ℕ → Bool) : ℕ → ℕ → Bool
  | 0, _ => true
  | k+1, s => f s && checkBlock f k (s+1)

theorem block_at {f : ℕ → Bool} {s n i : ℕ} (ok : checkBlock f n s = true)
    (lo : s ≤ i) (hi : i < s+n) : f i = true := by
  induction n generalizing s with
  | zero => omega
  | succ n ih =>
    simp only [checkBlock,Bool.and_eq_true] at ok
    by_cases e : i = s
    · exact e ▸ ok.1
    · exact ih ok.2 (by omega) (by omega)

theorem block_merge {f : ℕ → Bool} {s l r : ℕ} (a : checkBlock f l s = true)
    (b : checkBlock f r (s+l) = true) : checkBlock f (l+r) s = true := by
  induction l generalizing s with
  | zero => simpa using b
  | succ l ih =>
    rw [Nat.succ_add]
    simp only [checkBlock,Bool.and_eq_true] at a ⊢
    exact ⟨a.1,ih a.2 (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using b)⟩

def testAt (b : Bound) (bs : Array Bound) (k : ℕ) (old now : Records) (cw rw i : ℕ) : Bool :=
  (getRecord now i).all (rowCheck b bs k old cw rw)

theorem layer_of_block {b : Bound} {bs : Array Bound} {old now : Records} {k cw rw : ℕ}
    (gn : b.goal ≠ 0) (bv : ∀ s ∈ bs, Valid s) (prev : LayerOK b k old)
    (ok : checkBlock (testAt b bs k old now cw rw) (now.size*32) 0 = true) : LayerOK b (k+1) now := by
  intro i c h
  cases ee : getRecord now i with
  | none => simp [recorded,ee] at h
  | some r =>
    have mem := below_capacity ee
    have v := block_at ok (Nat.zero_le i) (by simpa using mem)
    simp only [testAt,ee,Option.all_some] at v
    simp only [recorded,ee,Option.map_some,Option.some.injEq] at h
    subst c
    exact row_sound gn bv prev v

theorem emptyOK (b : Bound) (k : ℕ) : LayerOK b k #[] := by
  intro i c h
  simp [recorded,getRecord] at h

theorem bound_of_layers {b : Bound} {bs : Array Bound} {last : Records} {cw rw : ℕ}
    (gn : b.goal ≠ 0) (bv : ∀ s ∈ bs, Valid s) (prev : LayerOK b (b.cost-1) last)
    (nd : b.inputs.Nodup) (ca : Canon b.mask b.inputs.toFinset) (p : ℕ)
    (ok : sparse true b bs (b.cost-1) last cw rw (b.inputs.sublists.map (fun ws => (ws,[]))) p = true) : Valid b := by
  intro k hk run
  obtain ⟨s,hs,hl⟩ := compress (more (show k ≤ b.cost-1 by omega) run)
  classical
  let ws := b.inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have mem : (ws,([] : List Recipe)) ∈ b.inputs.sublists.map (fun us => (us,[])) :=
    List.mem_map.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),rfl⟩
  exact sparse_sound gn bv prev ok _ mem (nd.filter _) (fun w hw => ca w (hs (eq ▸ hw))) (eq.symm ▸ hl)

end PEqualNP.Outside.L_meta_14794.SignedCert

namespace PEqualNP.Outside.L_meta_14794.SignedCert.GraphT
def T121 : Bound := ⟨0x500050000000000050005, [0x0, 0x100010000000000010001, 0x50000000000000005, 0x50005], 0x10000000000010005, 4⟩
def bsT121 : Array Bound := [].toArray
theorem vbsT121 : ∀ s ∈ bsT121, Valid s := by
  intro s hs
  simp only [bsT121,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T121r3p0 : RecordPage := #[
(0xe, 0x0)]
def T121r3 : Records := #[T121r3p0]
def testT121r3 : ℕ → Bool := testAt T121 bsT121 2 (#[] : Records) T121r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T121r3c0 : checkBlock testT121r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT121r3 : LayerOK T121 3 T121r3 := by
  apply layer_of_block (bs := bsT121) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT121 (emptyOK _ _)
  exact @block_merge testT121r3 0 1 31 T121r3c0 (show checkBlock testT121r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT121 : Valid T121 := by
  apply bound_of_layers (bs := bsT121) (last := T121r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT121 vT121r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_14794.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14794.SignedCert.GraphT
def T122 : Bound := ⟨0x1100110000000000110011, [0x0, 0x100010000000000010001, 0x110000000000000011, 0x110011], 0x10000000000010011, 4⟩
def bsT122 : Array Bound := [].toArray
theorem vbsT122 : ∀ s ∈ bsT122, Valid s := by
  intro s hs
  simp only [bsT122,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T122r3p0 : RecordPage := #[
(0xe, 0x0)]
def T122r3 : Records := #[T122r3p0]
def testT122r3 : ℕ → Bool := testAt T122 bsT122 2 (#[] : Records) T122r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T122r3c0 : checkBlock testT122r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT122r3 : LayerOK T122 3 T122r3 := by
  apply layer_of_block (bs := bsT122) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT122 (emptyOK _ _)
  exact @block_merge testT122r3 0 1 31 T122r3c0 (show checkBlock testT122r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT122 : Valid T122 := by
  apply bound_of_layers (bs := bsT122) (last := T122r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT122 vT122r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_14794.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14794.SignedCert.GraphT
def T123 : Bound := ⟨0x110011000000000011001100000000, [0x0, 0x10001000000000001000100000000, 0x11000000000000001100000000, 0x11001100000000], 0x1000000000001001100000000, 4⟩
def bsT123 : Array Bound := [].toArray
theorem vbsT123 : ∀ s ∈ bsT123, Valid s := by
  intro s hs
  simp only [bsT123,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T123r3p0 : RecordPage := #[
(0xe, 0x0)]
def T123r3 : Records := #[T123r3p0]
def testT123r3 : ℕ → Bool := testAt T123 bsT123 2 (#[] : Records) T123r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T123r3c0 : checkBlock testT123r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT123r3 : LayerOK T123 3 T123r3 := by
  apply layer_of_block (bs := bsT123) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT123 (emptyOK _ _)
  exact @block_merge testT123r3 0 1 31 T123r3c0 (show checkBlock testT123r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT123 : Valid T123 := by
  apply bound_of_layers (bs := bsT123) (last := T123r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT123 vT123r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_14794.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14794.SignedCert.GraphT
def T257 : Bound := ⟨0x55005500550055, [0x0, 0x11001100110011, 0x5000500050005, 0x5500000055, 0x550055], 0x1001100010055, 4⟩
def bsT257 : Array Bound := [].toArray
theorem vbsT257 : ∀ s ∈ bsT257, Valid s := by
  intro s hs
  simp only [bsT257,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T257r3p0 : RecordPage := #[
(0x1e, 0x0)]
def T257r3 : Records := #[T257r3p0]
def testT257r3 : ℕ → Bool := testAt T257 bsT257 2 (#[] : Records) T257r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T257r3c0 : checkBlock testT257r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT257r3 : LayerOK T257 3 T257r3 := by
  apply layer_of_block (bs := bsT257) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT257 (emptyOK _ _)
  exact @block_merge testT257r3 0 1 31 T257r3c0 (show checkBlock testT257r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT257 : Valid T257 := by
  apply bound_of_layers (bs := bsT257) (last := T257r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT257 vT257r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_14794.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14794.SignedCert.GraphT
def T259 : Bound := ⟨0x55000000550000005500000055, [0x0, 0x11000000110000001100000011, 0x5000000050000000500000005, 0x550000000000000055, 0x5500000055], 0x1000000010000001100000055, 4⟩
def bsT259 : Array Bound := [].toArray
theorem vbsT259 : ∀ s ∈ bsT259, Valid s := by
  intro s hs
  simp only [bsT259,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T259r3p0 : RecordPage := #[
(0x1e, 0x0)]
def T259r3 : Records := #[T259r3p0]
def testT259r3 : ℕ → Bool := testAt T259 bsT259 2 (#[] : Records) T259r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T259r3c0 : checkBlock testT259r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT259r3 : LayerOK T259 3 T259r3 := by
  apply layer_of_block (bs := bsT259) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT259 (emptyOK _ _)
  exact @block_merge testT259r3 0 1 31 T259r3c0 (show checkBlock testT259r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT259 : Valid T259 := by
  apply bound_of_layers (bs := bsT259) (last := T259r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT259 vT259r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_14794.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14794.SignedCert.GraphT
def T260 : Bound := ⟨0x1111000011110000111100001111, [0x0, 0x101000001010000010100000101, 0x11000000110000001100000011, 0x11110000000000001111, 0x111100001111], 0x1000000010000001100001111, 4⟩
def bsT260 : Array Bound := [].toArray
theorem vbsT260 : ∀ s ∈ bsT260, Valid s := by
  intro s hs
  simp only [bsT260,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T260r3p0 : RecordPage := #[
(0x1e, 0x0)]
def T260r3 : Records := #[T260r3p0]
def testT260r3 : ℕ → Bool := testAt T260 bsT260 2 (#[] : Records) T260r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T260r3c0 : checkBlock testT260r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT260r3 : LayerOK T260 3 T260r3 := by
  apply layer_of_block (bs := bsT260) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT260 (emptyOK _ _)
  exact @block_merge testT260r3 0 1 31 T260r3c0 (show checkBlock testT260r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT260 : Valid T260 := by
  apply bound_of_layers (bs := bsT260) (last := T260r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT260 vT260r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_14794.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14794.SignedCert.GraphT
def T262 : Bound := ⟨0x1010101010101010101010101010101, [0x0, 0x10001000100010001000100010001, 0x101000001010000010100000101, 0x10101010000000001010101, 0x101010101010101], 0x1000000010001000101010101, 4⟩
def bsT262 : Array Bound := [].toArray
theorem vbsT262 : ∀ s ∈ bsT262, Valid s := by
  intro s hs
  simp only [bsT262,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T262r3p0 : RecordPage := #[
(0x1e, 0x0)]
def T262r3 : Records := #[T262r3p0]
def testT262r3 : ℕ → Bool := testAt T262 bsT262 2 (#[] : Records) T262r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T262r3c0 : checkBlock testT262r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT262r3 : LayerOK T262 3 T262r3 := by
  apply layer_of_block (bs := bsT262) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT262 (emptyOK _ _)
  exact @block_merge testT262r3 0 1 31 T262r3c0 (show checkBlock testT262r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT262 : Valid T262 := by
  apply bound_of_layers (bs := bsT262) (last := T262r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT262 vT262r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_14794.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14794.SignedCert.GraphT
def T265 : Bound := ⟨0x5500550000000000550055, [0x0, 0x1100110000000000110011, 0x500050000000000050005, 0x550000000000000055, 0x550055], 0x10000000000010055, 5⟩
def bsT265 : Array Bound := [T121].toArray
theorem vbsT265 : ∀ s ∈ bsT265, Valid s := by
  intro s hs
  simp only [bsT265,List.mem_toArray] at hs
  exact (familyCons vT121 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT265 : Valid T265 := by
  apply bound_of_layers (bs := bsT265) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT265 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_14794.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14794.SignedCert.GraphT
def T266 : Bound := ⟨0x50505050000000005050505, [0x0, 0x10101010000000001010101, 0x500050000000000050005, 0x5050000000000000505, 0x5050505], 0x10000000001010505, 5⟩
def bsT266 : Array Bound := [T121].toArray
theorem vbsT266 : ∀ s ∈ bsT266, Valid s := by
  intro s hs
  simp only [bsT266,List.mem_toArray] at hs
  exact (familyCons vT121 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT266 : Valid T266 := by
  apply bound_of_layers (bs := bsT266) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT266 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_14794.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14794.SignedCert.GraphT
def T267 : Bound := ⟨0x111111110000000011111111, [0x0, 0x10101010000000001010101, 0x1100110000000000110011, 0x11110000000000001111, 0x11111111], 0x10000000001011111, 5⟩
def bsT267 : Array Bound := [T122].toArray
theorem vbsT267 : ∀ s ∈ bsT267, Valid s := by
  intro s hs
  simp only [bsT267,List.mem_toArray] at hs
  exact (familyCons vT122 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT267 : Valid T267 := by
  apply bound_of_layers (bs := bsT267) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT267 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_14794.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14794.SignedCert.GraphT
def T268 : Bound := ⟨0x50005000500050005000500050005, [0x0, 0x10001000100010001000100010001, 0x5000000050000000500000005, 0x500050000000000050005, 0x5000500050005], 0x1000000010001000100010005, 5⟩
def bsT268 : Array Bound := [T121].toArray
theorem vbsT268 : ∀ s ∈ bsT268, Valid s := by
  intro s hs
  simp only [bsT268,List.mem_toArray] at hs
  exact (familyCons vT121 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT268 : Valid T268 := by
  apply bound_of_layers (bs := bsT268) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT268 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_14794.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14794.SignedCert.GraphT
def T270 : Bound := ⟨0x550055000000000055005500000000, [0x0, 0x110011000000000011001100000000, 0x50005000000000005000500000000, 0x55000000000000005500000000, 0x55005500000000], 0x1000000000001001100000000, 5⟩
def bsT270 : Array Bound := [T123].toArray
theorem vbsT270 : ∀ s ∈ bsT270, Valid s := by
  intro s hs
  simp only [bsT270,List.mem_toArray] at hs
  exact (familyCons vT123 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT270 : Valid T270 := by
  apply bound_of_layers (bs := bsT270) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT270 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_14794.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14794.SignedCert.GraphT
def T271 : Bound := ⟨0x11111111000000001111111100000000, [0x0, 0x1010101000000000101010100000000, 0x110011000000000011001100000000, 0x1111000000000000111100000000, 0x1111111100000000], 0x1000000000001001100000000, 5⟩
def bsT271 : Array Bound := [T123].toArray
theorem vbsT271 : ∀ s ∈ bsT271, Valid s := by
  intro s hs
  simp only [bsT271,List.mem_toArray] at hs
  exact (familyCons vT123 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT271 : Valid T271 := by
  apply bound_of_layers (bs := bsT271) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT271 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_14794.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14794.SignedCert.GraphT
def T319 : Bound := ⟨0x5555555555555555, [0x0, 0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555], 0x1001101015555, 5⟩
def bsT319 : Array Bound := [T257].toArray
theorem vbsT319 : ∀ s ∈ bsT319, Valid s := by
  intro s hs
  simp only [bsT319,List.mem_toArray] at hs
  exact (familyCons vT257 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT319 : Valid T319 := by
  apply bound_of_layers (bs := bsT319) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT319 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_14794.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14794.SignedCert.GraphT
def T322 : Bound := ⟨0x5555000055550000555500005555, [0x0, 0x1111000011110000111100001111, 0x505000005050000050500000505, 0x55000000550000005500000055, 0x55550000000000005555, 0x555500005555], 0x1000000010000001100005555, 5⟩
def bsT322 : Array Bound := [T259].toArray
theorem vbsT322 : ∀ s ∈ bsT322, Valid s := by
  intro s hs
  simp only [bsT322,List.mem_toArray] at hs
  exact (familyCons vT259 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT322 : Valid T322 := by
  apply bound_of_layers (bs := bsT322) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT322 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_14794.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14794.SignedCert.GraphT
def T328 : Bound := ⟨0x555555550000000055555555, [0x0, 0x111111110000000011111111, 0x50505050000000005050505, 0x5500550000000000550055, 0x55550000000000005555, 0x55555555], 0x10000000001015555, 6⟩
def bsT328 : Array Bound := [T265].toArray
theorem vbsT328 : ∀ s ∈ bsT328, Valid s := by
  intro s hs
  simp only [bsT328,List.mem_toArray] at hs
  exact (familyCons vT265 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT328 : Valid T328 := by
  apply bound_of_layers (bs := bsT328) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT328 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_14794.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14794.SignedCert.GraphT
def T331 : Bound := ⟨0x5050505050505050505050505050505, [0x0, 0x1010101010101010101010101010101, 0x50005000500050005000500050005, 0x505000005050000050500000505, 0x50505050000000005050505, 0x505050505050505], 0x1000000010001000101010505, 6⟩
def bsT331 : Array Bound := [T266].toArray
theorem vbsT331 : ∀ s ∈ bsT331, Valid s := by
  intro s hs
  simp only [bsT331,List.mem_toArray] at hs
  exact (familyCons vT266 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT331 : Valid T331 := by
  apply bound_of_layers (bs := bsT331) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT331 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_14794.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14794.SignedCert.GraphT
def T333 : Bound := ⟨0x55555555000000005555555500000000, [0x0, 0x11111111000000001111111100000000, 0x5050505000000000505050500000000, 0x550055000000000055005500000000, 0x5555000000000000555500000000, 0x5555555500000000], 0x1000000000001001100000000, 6⟩
def bsT333 : Array Bound := [T270].toArray
theorem vbsT333 : ∀ s ∈ bsT333, Valid s := by
  intro s hs
  simp only [bsT333,List.mem_toArray] at hs
  exact (familyCons vT270 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT333 : Valid T333 := by
  apply bound_of_layers (bs := bsT333) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT333 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_14794.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14794.SignedCert.GraphT
def T334 : Bound := ⟨0x550055005500550055005500550055, [0x0, 0x110011001100110011001100110011, 0x50005000500050005000500050005, 0x55000000550000005500000055, 0x5500550000000000550055, 0x55005500550055], 0x1000000010001001100010055, 7⟩
def bsT334 : Array Bound := [T122, T257, T259, T265, T268, T270].toArray
theorem vbsT334 : ∀ s ∈ bsT334, Valid s := by
  intro s hs
  simp only [bsT334,List.mem_toArray] at hs
  exact (familyCons vT122 <| familyCons vT257 <| familyCons vT259 <| familyCons vT265 <| familyCons vT268 <| familyCons vT270 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T334r4p0 : RecordPage := #[
(0x240c423e, 0x0)]
def T334r4 : Records := #[T334r4p0]
def testT334r4 : ℕ → Bool := testAt T334 bsT334 3 (#[] : Records) T334r4 3 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T334r4c0 : checkBlock testT334r4 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT334r4 : LayerOK T334 4 T334r4 := by
  apply layer_of_block (bs := bsT334) (k := 3) (old := (#[] : Records)) (cw := 3) (rw := 1) (by decide +kernel) vbsT334 (emptyOK _ _)
  exact @block_merge testT334r4 0 1 31 T334r4c0 (show checkBlock testT334r4 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T334r5p0 : RecordPage := #[
(0xc423e, 0x4d51)]
def T334r5 : Records := #[T334r5p0]
def testT334r5 : ℕ → Bool := testAt T334 bsT334 4 T334r4 T334r5 3 0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T334r5c0 : checkBlock testT334r5 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT334r5 : LayerOK T334 5 T334r5 := by
  apply layer_of_block (bs := bsT334) (k := 4) (old := T334r4) (cw := 3) (rw := 0) (by decide +kernel) vbsT334 vT334r4
  exact @block_merge testT334r5 0 1 31 T334r5c0 (show checkBlock testT334r5 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T334r6p0 : RecordPage := #[
(0x3e, 0xccccd448566666a8888666688880000666a660000888880)]
def T334r6 : Records := #[T334r6p0]
def testT334r6 : ℕ → Bool := testAt T334 bsT334 5 T334r5 T334r6 3 0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T334r6c0 : checkBlock testT334r6 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT334r6 : LayerOK T334 6 T334r6 := by
  apply layer_of_block (bs := bsT334) (k := 5) (old := T334r5) (cw := 3) (rw := 0) (by decide +kernel) vbsT334 vT334r5
  exact @block_merge testT334r6 0 1 31 T334r6c0 (show checkBlock testT334r6 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT334 : Valid T334 := by
  apply bound_of_layers (bs := bsT334) (last := T334r6) (cw := 3) (rw := 0) (by decide +kernel) vbsT334 vT334r6 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_14794.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14794.SignedCert.GraphT
def T335 : Bound := ⟨0x11111111111111111111111111111111, [0x0, 0x1010101010101010101010101010101, 0x110011001100110011001100110011, 0x1111000011110000111100001111, 0x111111110000000011111111, 0x1111111111111111], 0x1000000010001001101011111, 7⟩
def bsT335 : Array Bound := [T122, T260, T262, T267, T271].toArray
theorem vbsT335 : ∀ s ∈ bsT335, Valid s := by
  intro s hs
  simp only [bsT335,List.mem_toArray] at hs
  exact (familyCons vT122 <| familyCons vT260 <| familyCons vT262 <| familyCons vT267 <| familyCons vT271 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T335r4p0 : RecordPage := #[
(0x240c403e, 0x0), (0x230c423e, 0x0)]
def T335r4 : Records := #[T335r4p0]
def testT335r4 : ℕ → Bool := testAt T335 bsT335 3 (#[] : Records) T335r4 3 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T335r4c0 : checkBlock testT335r4 2 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT335r4 : LayerOK T335 4 T335r4 := by
  apply layer_of_block (bs := bsT335) (k := 3) (old := (#[] : Records)) (cw := 3) (rw := 1) (by decide +kernel) vbsT335 (emptyOK _ _)
  exact @block_merge testT335r4 0 2 30 T335r4c0 (show checkBlock testT335r4 30 2 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T335r5p0 : RecordPage := #[
(0xc203e, 0x2), (0xc403e, 0x9), (0xd403e, 0x68), (0xc423e, 0x13),
(0xd423e, 0x68)]
def T335r5 : Records := #[T335r5p0]
def testT335r5 : ℕ → Bool := testAt T335 bsT335 4 T335r4 T335r5 3 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T335r5c0 : checkBlock testT335r5 5 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT335r5 : LayerOK T335 5 T335r5 := by
  apply layer_of_block (bs := bsT335) (k := 4) (old := T335r4) (cw := 3) (rw := 1) (by decide +kernel) vbsT335 vT335r4
  exact @block_merge testT335r5 0 5 27 T335r5c0 (show checkBlock testT335r5 27 5 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T335r6p0 : RecordPage := #[
(0x3e, 0x66666822976666000066686600004453666624210000)]
def T335r6 : Records := #[T335r6p0]
def testT335r6 : ℕ → Bool := testAt T335 bsT335 5 T335r5 T335r6 3 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T335r6c0 : checkBlock testT335r6 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT335r6 : LayerOK T335 6 T335r6 := by
  apply layer_of_block (bs := bsT335) (k := 5) (old := T335r5) (cw := 3) (rw := 3) (by decide +kernel) vbsT335 vT335r5
  exact @block_merge testT335r6 0 1 31 T335r6c0 (show checkBlock testT335r6 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT335 : Valid T335 := by
  apply bound_of_layers (bs := bsT335) (last := T335r6) (cw := 3) (rw := 0) (by decide +kernel) vbsT335 vT335r6 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_14794.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14794.SignedCert.GraphT
def T348 : Bound := ⟨0x55555555555555555555555555555555, [0x0, 0x11111111111111111111111111111111, 0x5050505050505050505050505050505, 0x550055005500550055005500550055, 0x5555000055550000555500005555, 0x555555550000000055555555, 0x5555555555555555], 0x1000000010001001101015555, 9⟩
def bsT348 : Array Bound := [T266, T319, T322, T328, T331, T333, T334, T335].toArray
theorem vbsT348 : ∀ s ∈ bsT348, Valid s := by
  intro s hs
  simp only [bsT348,List.mem_toArray] at hs
  exact (familyCons vT266 <| familyCons vT319 <| familyCons vT322 <| familyCons vT328 <| familyCons vT331 <| familyCons vT333 <| familyCons vT334 <| familyCons vT335 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T348r4p0 : RecordPage := #[
(0x41430030f537e, 0x0)]
def T348r4 : Records := #[T348r4p0]
def testT348r4 : ℕ → Bool := testAt T348 bsT348 3 (#[] : Records) T348r4 3 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T348r4c0 : checkBlock testT348r4 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT348r4 : LayerOK T348 4 T348r4 := by
  apply layer_of_block (bs := bsT348) (k := 3) (old := (#[] : Records)) (cw := 3) (rw := 1) (by decide +kernel) vbsT348 (emptyOK _ _)
  exact @block_merge testT348r4 0 1 31 T348r4c0 (show checkBlock testT348r4 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T348r5p0 : RecordPage := #[
(0x220860c317e, 0x0), (0x61a60c317e, 0x0), (0x31861c317e, 0x0), (0x31961d317e, 0x0),
(0x452240c537e, 0x0), (0x552240c537e, 0x0), (0x40740c537e, 0x0), (0x430030f537e, 0x1),
(0x530030f537e, 0x0), (0x440030f537e, 0x1)]
def T348r5 : Records := #[T348r5p0]
def testT348r5 : ℕ → Bool := testAt T348 bsT348 4 T348r4 T348r5 3 0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T348r5c0 : checkBlock testT348r5 10 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT348r5 : LayerOK T348 5 T348r5 := by
  apply layer_of_block (bs := bsT348) (k := 4) (old := T348r4) (cw := 3) (rw := 0) (by decide +kernel) vbsT348 vT348r4
  exact @block_merge testT348r5 0 10 22 T348r5c0 (show checkBlock testT348r5 22 10 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T348r6p0 : RecordPage := #[
(0x860c317e, 0x1), (0xa60c317e, 0x3), (0x861c317e, 0x52), (0x862c317e, 0x58),
(0xa62c317e, 0x0), (0x865c317e, 0x43), (0xa60d317e, 0x1), (0x961d317e, 0xe1),
(0x862d317e, 0x78), (0x865d317e, 0x0), (0xa50c517e, 0x0), (0x852c517e, 0x58),
(0xa52c517e, 0x0), (0x462c517e, 0x8), (0xa50d517e, 0x1), (0x852d517e, 0x78),
(0x240c537e, 0x33969ee), (0x640c537e, 0x8), (0xa40c537e, 0x0), (0x740c537e, 0x1a1),
(0x462c537e, 0x1092), (0x562c537e, 0x10b), (0xa10d537e, 0x101), (0xa40d537e, 0x0),
(0xa40e537e, 0x0), (0x462e537e, 0x0), (0x562e537e, 0x0), (0x30f537e, 0x11111264e2f),
(0x40f537e, 0xce222224ee), (0x840f537e, 0x0), (0x50f537e, 0xee2222ee)]
def T348r6 : Records := #[T348r6p0]
def testT348r6 : ℕ → Bool := testAt T348 bsT348 5 T348r5 T348r6 3 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T348r6c0 : checkBlock testT348r6 16 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T348r6c1 : checkBlock testT348r6 15 16 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT348r6 : LayerOK T348 6 T348r6 := by
  apply layer_of_block (bs := bsT348) (k := 5) (old := T348r5) (cw := 3) (rw := 4) (by decide +kernel) vbsT348 vT348r5
  exact @block_merge testT348r6 0 31 1 (@block_merge testT348r6 0 16 15 T348r6c0 T348r6c1) (show checkBlock testT348r6 1 31 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T348r7p0 : RecordPage := #[
(0xc317e, 0x2f3891e05ee888420c816a6acccceeee8884), (0xd317e, 0x4f391183f33ba22108d246a6acccceeee8884), (0xc517e, 0xce06d95e05ccee88826a6a45501cccceeee8882), (0xd517e, 0x338089f83fba220981a8a9a91d22cccceeee8882),
(0xc537e, 0x33bbaba5f5fbb3111fb89109a9ab33322789638601eeee4422), (0xd537e, 0x33bb88899ee2242626a2a6acccc8be0bbbb88ad2), (0xe537e, 0x33bbb5cf3109ee22446a6acccc8c613bbbad422), (0xf537e, 0xceee2222246a626a2acccccc2f60a0a3b2e7bbbbb8b72242),
(0x8547e, 0x333322132f3333bbbb33333bbbbbb88b3a73333320a1beeeeeeaaaacccacc8a8aeeee666), (0xa547e, 0xcccc8800cccceeeeccccceeeeeee22d6bcccc8080eeee6666cccc6666eeee6a6)]
def T348r7 : Records := #[T348r7p0]
def testT348r7 : ℕ → Bool := testAt T348 bsT348 6 T348r6 T348r7 3 5
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T348r7c0 : checkBlock testT348r7 10 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT348r7 : LayerOK T348 7 T348r7 := by
  apply layer_of_block (bs := bsT348) (k := 6) (old := T348r6) (cw := 3) (rw := 5) (by decide +kernel) vbsT348 vT348r6
  exact @block_merge testT348r7 0 10 22 T348r7c0 (show checkBlock testT348r7 22 10 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T348r8p0 : RecordPage := #[
(0x7e, 0x19a75517b5696a6acccccccccccc88395a1aa2061cccceeeeeeeeeeeeccccceeeeeee)]
def T348r8 : Records := #[T348r8p0]
def testT348r8 : ℕ → Bool := testAt T348 bsT348 7 T348r7 T348r8 3 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T348r8c0 : checkBlock testT348r8 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT348r8 : LayerOK T348 8 T348r8 := by
  apply layer_of_block (bs := bsT348) (k := 7) (old := T348r7) (cw := 3) (rw := 4) (by decide +kernel) vbsT348 vT348r7
  exact @block_merge testT348r8 0 1 31 T348r8c0 (show checkBlock testT348r8 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT348 : Valid T348 := by
  apply bound_of_layers (bs := bsT348) (last := T348r8) (cw := 3) (rw := 0) (by decide +kernel) vbsT348 vT348r8 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_14794.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14794.SignedCert.GraphT
def rootT : Bound := ⟨0xffffffffffffffffffffffffffffffff, [0x0, 0x55555555555555555555555555555555, 0x33333333333333333333333333333333, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, 0xff00ff00ff00ff00ff00ff00ff00ff, 0xffff0000ffff0000ffff0000ffff, 0xffffffff00000000ffffffff, 0xffffffffffffffff], 0x1000000010001001101015555, 10⟩
def bsrootT : Array Bound := [T348].toArray
theorem vbsrootT : ∀ s ∈ bsrootT, Valid s := by
  intro s hs
  simp only [bsrootT,List.mem_toArray] at hs
  exact (familyCons vT348 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vrootT : Valid rootT := by
  apply bound_of_layers (bs := bsrootT) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsrootT (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_14794.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14794.SignedCert.GraphT
open PEqualNP.CircuitLowerBounds
def columns : List W := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00, 0xffffffffffffffffffffffffffffffff, 0xffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000]
def funValue (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 4, 1, 5, 2, 5, 1, 6, 3, 6, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 1, 6, 3, 6, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 1, 6, 3, 6, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def network : List Gate := [
  ⟨.or, [1,3]⟩,
  ⟨.or, [1,2]⟩,
  ⟨.or, [8,9]⟩,
  ⟨.and, [9,5]⟩,
  ⟨.or, [10,5]⟩,
  ⟨.and, [0,4]⟩,
  ⟨.or, [13,11]⟩,
  ⟨.and, [12,7]⟩,
  ⟨.or, [14,15]⟩,
  ⟨.and, [8,6]⟩,
  ⟨.or, [17,16]⟩]

theorem legal_network : ∀ g ∈ network, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [network,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem correct_network : ∀ x : Fin 8 → Bool, (Circuit.mk network 18).eval (List.ofFn x) = funValue x := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem lower (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, Source.legal g)
    (correct : ∀ x : Fin 8 → Bool, (Circuit.mk gs o).eval (List.ofFn x) = funValue x) :
    10 ≤ Source.binaryCost gs := by
  apply Source.binary_lb vrootT 0xfffffffefffffffefffeffeefefeaaaa columns funValue (by decide +kernel) (by decide +kernel) (by rfl) _ (by decide +kernel) _ gs o legal correct
  · decide +kernel
  · decide +kernel

end PEqualNP.Outside.L_meta_14794.SignedCert.GraphT

theorem PEqualNP.Outside.L_meta_14794 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 1, 6, 3, 6, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 1, 6, 3, 6, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 1, 6, 3, 6, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 1, 6, 3, 6, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 1, 6, 3, 6, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 1, 6, 3, 6, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fits _ computes
  by_cases hasNot : ∃ g ∈ gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : PEqualNP.Outside.L_meta_14794.SignedCert.Source.binaryCost gates < gates.length :=
      (List.length_filter_lt_length_iff_exists (p := PEqualNP.Outside.L_meta_14794.SignedCert.Source.isBinary)).mpr
        ⟨g, mem, by simp [PEqualNP.Outside.L_meta_14794.SignedCert.Source.isBinary, op]⟩
    have hb := PEqualNP.Outside.L_meta_14794.SignedCert.GraphT.lower gates o (fun g hg => fits g hg) computes
    have hl : PEqualNP.Outside.L_meta_14794.SignedCert.GraphT.network.length = 11 := rfl
    exact ⟨PEqualNP.Outside.L_meta_14794.SignedCert.GraphT.network, 18, PEqualNP.Outside.L_meta_14794.SignedCert.GraphT.legal_network, by omega, PEqualNP.Outside.L_meta_14794.SignedCert.GraphT.correct_network⟩
  · refine ⟨gates, o, fun g hg => ⟨?_, (fits g hg).2⟩, le_refl _, computes⟩
    rcases (fits g hg).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hasNot ⟨g,hg,h⟩).elim
