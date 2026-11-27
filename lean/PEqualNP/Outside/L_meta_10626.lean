import PEqualNP.Defs

-- The live-set compression proof is adapted from L-meta-9136 and its credited sources.
namespace PEqualNP.Outside.L_meta_10626.SignedCert
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

end PEqualNP.Outside.L_meta_10626.SignedCert

namespace PEqualNP.Outside.L_meta_10626.SignedCert

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

end PEqualNP.Outside.L_meta_10626.SignedCert

namespace PEqualNP.Outside.L_meta_10626.SignedCert

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

end PEqualNP.Outside.L_meta_10626.SignedCert

namespace PEqualNP.Outside.L_meta_10626.SignedCert

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

end PEqualNP.Outside.L_meta_10626.SignedCert

namespace PEqualNP.Outside.L_meta_10626.SignedCert
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

end PEqualNP.Outside.L_meta_10626.SignedCert

namespace PEqualNP.Outside.L_meta_10626.SignedCert.Source
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
    norm m z ∈ PEqualNP.Outside.L_meta_10626.SignedCert.ops m (norm m a) (norm m b) := by
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
    build (PEqualNP.Outside.L_meta_10626.SignedCert.ops m) (norm m t) k (bank m S) := by
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

theorem binary_lb {b : Bound} (valid : Valid b) (w : W) (raw : List W) (F : (Fin 7 → Bool) → Bool)
    (nz : w ≠ 0) (no : w ≠ ~~~0) (dim : raw.length = 7)
    (stk : bank b.mask raw.toFinset ⊆ b.inputs.toFinset) (tg : norm b.mask w = b.goal)
    (rows : ∀ k : Fin 128, F (fun i => bit k (raw.getD i.val 0)) = bit k w)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (evals : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = F x) : b.cost ≤ binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ raw, holds raw.toFinset u := fun u hu =>
    .inr (.inr ⟨u,List.mem_toFinset.mpr hu,.inl rfl⟩)
  have eval (k : Fin 128) :
      (gs.foldl step (raw.map (bit k))).getD o false = bit k (~~~(~~~w)) := by
    let x (i : Fin 7) := bit k (raw.getD i.val 0)
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

end PEqualNP.Outside.L_meta_10626.SignedCert.Source

namespace PEqualNP.Outside.L_meta_10626.SignedCert
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

end PEqualNP.Outside.L_meta_10626.SignedCert

namespace PEqualNP.Outside.L_meta_10626.SignedCert

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


end PEqualNP.Outside.L_meta_10626.SignedCert

namespace PEqualNP.Outside.L_meta_10626.SignedCert

def shifted (p : ℕ) (w : W) : W :=
  (BitVec.ofBoolListLE (List.ofFn (fun i : Fin 128 => w.getLsbD ((p >>> (7*i.val)) % 128)))).cast List.length_ofFn

theorem shifted_bit (p : ℕ) (w : W) {i : ℕ} (hi : i < 128) :
    (shifted p w).getLsbD i = w.getLsbD ((p >>> (7*i)) % 128) := by
  simp only [shifted,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn,hi,↓reduceDIte,Option.getD_some]

theorem shifted_and (p : ℕ) (x y : W) : shifted p (x &&& y) = shifted p x &&& shifted p y := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  change (shifted p (x &&& y)).getLsbD i = (shifted p x &&& shifted p y).getLsbD i
  simp only [BitVec.getLsbD_and,shifted_bit _ _ hi]

theorem shifted_neg (p : ℕ) (x : W) : shifted p (~~~x) = ~~~(shifted p x) := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  change (shifted p (~~~x)).getLsbD i = (~~~(shifted p x)).getLsbD i
  rw [shifted_bit _ _ hi,BitVec.getLsbD_not,BitVec.getLsbD_not,shifted_bit _ _ hi]
  simp only [hi,decide_true,Nat.mod_lt _ (by decide : 0 < 128),Bool.true_and]

theorem shifted_phase (p : ℕ) (s : Bool) (x : W) : shifted p (phase s x) = phase s (shifted p x) := by
  cases s <;> simp [phase,shifted_neg]

theorem shifted_norm {p : ℕ} {m q : W} (sub : q &&& shifted p m = q) (x : W) :
    norm q (shifted p (norm m x)) = norm q (shifted p x) := by
  obtain ⟨s,e⟩ := norm_cases m x
  rw [e,shifted_and,shifted_phase]
  have cut : q &&& (shifted p m &&& phase s (shifted p x)) = q &&& phase s (shifted p x) := by
    rw [← BitVec.and_assoc,sub]
  rw [norm_of_mask cut]
  cases s <;> simp [phase,norm_neg]

theorem shifted_op {p : ℕ} {m q a b z : W} (sub : q &&& shifted p m = q)
    (hz : z ∈ ops m a b) : norm q (shifted p z) ∈ ops q (norm q (shifted p a)) (norm q (shifted p b)) := by
  obtain ⟨s,t,rfl⟩ := op_cases hz
  rw [shifted_norm sub,shifted_and,shifted_phase,shifted_phase]
  exact norm_gate .. 

theorem shifted_build {p : ℕ} {m q g : W} {k : ℕ} {S A : Finset W}
    (sub : q &&& shifted p m = q) (run : build (ops m) g k S) (zero : (0 : W) ∈ A)
    (stock : ∀ w ∈ S, norm q (shifted p w) ∈ A) : build (ops q) (norm q (shifted p g)) k A := by
  induction k generalizing S A with
  | zero => exact stock g run
  | succ k ih =>
    rcases run with skip | ⟨a,ha,b,hb,_,z,hz,tail⟩
    · exact Or.inl (ih skip zero stock)
    have hA := stock a ha
    have hB := stock b hb
    have hZ := shifted_op sub hz
    by_cases e : norm q (shifted p a) = norm q (shifted p b)
    · rw [e] at hZ
      have hzA : norm q (shifted p z) ∈ A := by
        rcases op_same hZ with h | h
        · rwa [h]
        · rwa [h,norm_idem]
      apply Or.inl (ih tail zero ?_)
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact hzA
      · exact stock _ hw
    · refine Or.inr ⟨_,hA,_,hB,e,_,hZ,ih tail (Finset.mem_insert_of_mem zero) ?_⟩
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact Finset.mem_insert_self ..
      · exact Finset.mem_insert_of_mem (stock _ hw)

theorem transfer {src dest : Bound} (v : Valid src) (p : ℕ) (le : dest.cost ≤ src.cost)
    (sub : src.mask &&& shifted p dest.mask = src.mask)
    (eq : norm src.mask (shifted p dest.goal) = src.goal)
    (zero : (0 : W) ∈ src.inputs)
    (stock : dest.inputs.all (fun w => src.inputs.contains (norm src.mask (shifted p w))) = true) :
    Valid dest := by
  intro k hk run
  have moved := shifted_build sub run (List.mem_toFinset.mpr zero)
    (fun w hw => List.mem_toFinset.mpr (List.contains_iff_mem.mp
      (List.all_eq_true.mp stock w (List.mem_toFinset.mp hw))))
  rw [eq] at moved
  exact v _ (lt_of_lt_of_le hk le) moved

end PEqualNP.Outside.L_meta_10626.SignedCert

namespace PEqualNP.Outside.L_meta_10626.SignedCert.GraphB
open Source PEqualNP.CircuitLowerBounds
def rootB : Bound := ⟨0xffffffffffffffffffffffffffffffff, [0x0, 0x55555555555555555555555555555555, 0x33333333333333333333333333333333, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, 0xff00ff00ff00ff00ff00ff00ff00ff, 0xffff0000ffff0000ffff0000ffff, 0xffffffff00000000ffffffff, 0xffffffffffffffff], 0x1000100110105135f, 12⟩
def cols : List W := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000]
def graph (x : Fin 7 → Bool) : Bool := (x 0 && x 2) || (x 1 && x 3) || (x 0 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem edge_eq : ∀ x : Fin 7 → Bool, decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) = graph x := by
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem size_lb (h : Valid rootB) (gs : List Gate) (o : ℕ)
    (hg : ∀ g ∈ gs, Source.legal g) (ev : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = graph x) :
    12 ≤ binaryCost gs := by
  apply binary_lb h 0xfffffffffffffffefffeffeefefaeca0 cols graph (by decide +kernel) (by decide +kernel) (by rfl) _ (by decide +kernel) _ gs o hg ev
  · decide +kernel
  · decide +kernel
end PEqualNP.Outside.L_meta_10626.SignedCert.GraphB

namespace PEqualNP.Outside.L_meta_10626.SignedCert.GraphB
def B0 : Bound := ⟨0x330033, [0x0, 0x110011, 0x30003, 0x33], 0x10013, 4⟩
def B0n0 : Cell := (3, [0x110011, 0x30003, 0x33])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB0n0 : B0n0.2.Nodup ∧ Closed B0.mask B0.goal B0n0 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 2) (bs := []) (seen := []) (h := []) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB0 : Valid B0 := by
  apply small_bound (bs := []) (seen := [B0n0]) (width := 1) (p := 0x4000)
  · decide +kernel
  · exact familyNil
  · exact familyCons vB0n0 <| familyNil
  · decide +kernel
  · apply canon_checked; decide +kernel
  · decide +kernel
end PEqualNP.Outside.L_meta_10626.SignedCert.GraphB

namespace PEqualNP.Outside.L_meta_10626.SignedCert.GraphB
def B1 : Bound := ⟨0xcc00cc, [0x0, 0x440044, 0xc000c, 0xcc], 0x4004c, 4⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB1 : Valid B1 := by
  apply transfer vB0 0xb9600009920000000000000000003860000182 <;> decide +kernel
end PEqualNP.Outside.L_meta_10626.SignedCert.GraphB

namespace PEqualNP.Outside.L_meta_10626.SignedCert.GraphB
def B3 : Bound := ⟨0x50500000505, [0x0, 0x10100000101, 0x500000005, 0x505], 0x100000105, 4⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB3 : Valid B3 := by
  apply transfer vB0 0x152800011200000000000000000005080000100 <;> decide +kernel
end PEqualNP.Outside.L_meta_10626.SignedCert.GraphB

namespace PEqualNP.Outside.L_meta_10626.SignedCert.GraphB
def B6 : Bound := ⟨0x330000000000000033, [0x0, 0x110000000000000011, 0x30000000000000003, 0x33], 0x10000000000000013, 4⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB6 : Valid B6 := by
  apply transfer vB0 0x22c400020c00000000000000000002840000080 <;> decide +kernel
end PEqualNP.Outside.L_meta_10626.SignedCert.GraphB

namespace PEqualNP.Outside.L_meta_10626.SignedCert.GraphB
def B7 : Bound := ⟨0x5050000000000000505, [0x0, 0x1010000000000000101, 0x50000000000000005, 0x505], 0x10000000000000105, 4⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB7 : Valid B7 := by
  apply transfer vB0 0x254800021400000000000000000005080000100 <;> decide +kernel
end PEqualNP.Outside.L_meta_10626.SignedCert.GraphB

namespace PEqualNP.Outside.L_meta_10626.SignedCert.GraphB
def B8 : Bound := ⟨0x300030000000000030003, [0x0, 0x100010000000000010001, 0x30000000000000003, 0x30003], 0x10000000000010003, 4⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB8 : Valid B8 := by
  apply transfer vB0 0x28d000020c00000000000000000008900000080 <;> decide +kernel
end PEqualNP.Outside.L_meta_10626.SignedCert.GraphB

namespace PEqualNP.Outside.L_meta_10626.SignedCert.GraphB
def B9 : Bound := ⟨0x1100110000000000110011, [0x0, 0x100010000000000010001, 0x110000000000000011, 0x110011], 0x10000000000010011, 4⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB9 : Valid B9 := by
  apply transfer vB0 0x2a500002240000000000000000000a100000200 <;> decide +kernel
end PEqualNP.Outside.L_meta_10626.SignedCert.GraphB

namespace PEqualNP.Outside.L_meta_10626.SignedCert.GraphB
def B10 : Bound := ⟨0x3000000030000000300000003, [0x0, 0x1000000010000000100000001, 0x30000000000000003, 0x300000003], 0x10000000100000003, 4⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB10 : Valid B10 := by
  apply transfer vB0 0x30e000020c00000000000000000010a00000080 <;> decide +kernel
end PEqualNP.Outside.L_meta_10626.SignedCert.GraphB

namespace PEqualNP.Outside.L_meta_10626.SignedCert.GraphB
def B125 : Bound := ⟨0xff000000ff, [0x0, 0x5500000055, 0x3300000033, 0xf0000000f, 0xff], 0x110000005f, 4⟩
def B125n0 : Cell := (3, [0x5500000055, 0x3300000033, 0xf0000000f, 0xff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB125n0 : B125n0.2.Nodup ∧ Closed B125.mask B125.goal B125n0 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 2) (bs := []) (seen := []) (h := []) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB125 : Valid B125 := by
  apply small_bound (bs := []) (seen := [B125n0]) (width := 1) (p := 0x40000000)
  · decide +kernel
  · exact familyNil
  · exact familyCons vB125n0 <| familyNil
  · decide +kernel
  · apply canon_checked; decide +kernel
  · decide +kernel
end PEqualNP.Outside.L_meta_10626.SignedCert.GraphB

namespace PEqualNP.Outside.L_meta_10626.SignedCert.GraphB
def B126 : Bound := ⟨0x333300003333, [0x0, 0x111100001111, 0x30300000303, 0x3300000033, 0x3333], 0x1100001313, 4⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB126 : Valid B126 := by
  apply transfer vB125 0x5a354894a1508100000000000000000000000000000000000000000058314084811000 <;> decide +kernel
end PEqualNP.Outside.L_meta_10626.SignedCert.GraphB

namespace PEqualNP.Outside.L_meta_10626.SignedCert.GraphB
def B131 : Bound := ⟨0xcccccccc, [0x0, 0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc], 0x4004c, 5⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB131 : Valid B131 := by
  apply small_bound (bs := [B1]) (seen := []) (width := 1) (p := 0x40000000)
  · decide +kernel
  · exact familyCons vB1 <| familyNil
  · exact familyNil
  · decide +kernel
  · apply canon_checked; decide +kernel
  · decide +kernel
end PEqualNP.Outside.L_meta_10626.SignedCert.GraphB

namespace PEqualNP.Outside.L_meta_10626.SignedCert.GraphB
def B133 : Bound := ⟨0xf0f00000f0f, [0x0, 0x50500000505, 0x30300000303, 0xf0000000f, 0xf0f], 0x10000030f, 5⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB133 : Valid B133 := by
  apply small_bound (bs := [B3]) (seen := []) (width := 1) (p := 0x40000000)
  · decide +kernel
  · exact familyCons vB3 <| familyNil
  · exact familyNil
  · decide +kernel
  · apply canon_checked; decide +kernel
  · decide +kernel
end PEqualNP.Outside.L_meta_10626.SignedCert.GraphB

namespace PEqualNP.Outside.L_meta_10626.SignedCert.GraphB
def B134 : Bound := ⟨0xf0f00000f0f0, [0x0, 0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0], 0x1000001050, 5⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB134 : Valid B134 := by
  apply transfer vB131 0x5eb40004e940005cb00004c900001e340000e140001c300000c10000 <;> decide +kernel
end PEqualNP.Outside.L_meta_10626.SignedCert.GraphB

namespace PEqualNP.Outside.L_meta_10626.SignedCert.GraphB
def B141 : Bound := ⟨0xff00000000000000ff, [0x0, 0x550000000000000055, 0x330000000000000033, 0xf000000000000000f, 0xff], 0x1000000000000005f, 5⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB141 : Valid B141 := by
  apply transfer vB133 0x8f1634400000008706140000000000000000000000000000000000000e1430400000000604100 <;> decide +kernel
end PEqualNP.Outside.L_meta_10626.SignedCert.GraphB

namespace PEqualNP.Outside.L_meta_10626.SignedCert.GraphB
def B142 : Bound := ⟨0xf0f0000000000000f0f, [0x0, 0x5050000000000000505, 0x3030000000000000303, 0xf000000000000000f, 0xf0f], 0x1000000000000030f, 5⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB142 : Valid B142 := by
  apply transfer vB133 0x972a4c80000000870a0c000000000000000000000000000000000000162848800000000608080 <;> decide +kernel
end PEqualNP.Outside.L_meta_10626.SignedCert.GraphB

namespace PEqualNP.Outside.L_meta_10626.SignedCert.GraphB
def B143 : Bound := ⟨0x33330000000000003333, [0x0, 0x11110000000000001111, 0x3030000000000000303, 0x330000000000000033, 0x3333], 0x10000000000001313, 5⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB143 : Valid B143 := by
  apply transfer vB133 0x9b1664400000009306440000000000000000000000000000000000001a1460400000001204400 <;> decide +kernel
end PEqualNP.Outside.L_meta_10626.SignedCert.GraphB

namespace PEqualNP.Outside.L_meta_10626.SignedCert.GraphB
def B144 : Bound := ⟨0x55550000000000005555, [0x0, 0x11110000000000001111, 0x5050000000000000505, 0x550000000000000055, 0x5555], 0x10000000000001155, 5⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB144 : Valid B144 := by
  apply transfer vB133 0x9d2a64800000008d0a240000000000000000000000000000000000001c2860800000000c08200 <;> decide +kernel
end PEqualNP.Outside.L_meta_10626.SignedCert.GraphB

namespace PEqualNP.Outside.L_meta_10626.SignedCert.GraphB
def B152 : Bound := ⟨0xf0000000f0000000f0000000f, [0x0, 0x5000000050000000500000005, 0x3000000030000000300000003, 0xf000000000000000f, 0xf0000000f], 0x1000000010000000f, 5⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB152 : Valid B152 := by
  apply small_bound (bs := [B10]) (seen := []) (width := 1) (p := 0x40000000)
  · decide +kernel
  · exact familyCons vB10 <| familyNil
  · exact familyNil
  · decide +kernel
  · apply canon_checked; decide +kernel
  · decide +kernel
end PEqualNP.Outside.L_meta_10626.SignedCert.GraphB

namespace PEqualNP.Outside.L_meta_10626.SignedCert.GraphB
def B153 : Bound := ⟨0x33000000330000003300000033, [0x0, 0x11000000110000001100000011, 0x3000000030000000300000003, 0x330000000000000033, 0x3300000033], 0x10000001100000013, 5⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB153 : Valid B153 := by
  apply transfer vB152 0xcb862c10000000000000000000000000000000000000000000000000c98224000000000000000000000000000000000000000000000000004a8428100000000000000000000000000000000000000000000000004880200 <;> decide +kernel
end PEqualNP.Outside.L_meta_10626.SignedCert.GraphB

namespace PEqualNP.Outside.L_meta_10626.SignedCert.GraphB
def B154 : Bound := ⟨0x55000000550000005500000055, [0x0, 0x11000000110000001100000011, 0x5000000050000000500000005, 0x550000000000000055, 0x5500000055], 0x10000001100000055, 5⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB154 : Valid B154 := by
  apply transfer vB133 0xcd8b26000000008d0a240000000000000000000000000000000000004c8922000000000c08200 <;> decide +kernel
end PEqualNP.Outside.L_meta_10626.SignedCert.GraphB

namespace PEqualNP.Outside.L_meta_10626.SignedCert.GraphB
def B163 : Bound := ⟨0x3300330000000000330033, [0x0, 0x1100110000000000110011, 0x300030000000000030003, 0x330000000000000033, 0x330033], 0x10000000000010013, 7⟩
def B163n0 : Cell := (3, [0x330032, 0x330000000000000033, 0x1100110000000000110011, 0x300030000000000030003])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n0 : B163n0.2.Nodup ∧ Closed B163.mask B163.goal B163n0 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 2) (bs := []) (seen := []) (h := [(0x330032, 0x10000000000000001, 0x330033), (0x10000000000000001, 0x100010000000000010001, 0x330000000000000033), (0x100010000000000010001, 0x1100110000000000110011, 0x300030000000000030003)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B163n1 : Cell := (4, [0x10000000000000001, 0x330000000000000033, 0x1100110000000000110011, 0x300030000000000030003, 0x330033])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n1 : B163n1.2.Nodup ∧ Closed B163.mask B163.goal B163n1 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := [B0]) (seen := [B163n0]) (h := [(0x10000000000000001, 0x100010000000000010001, 0x330000000000000033), (0x100010000000000010001, 0x1100110000000000110011, 0x300030000000000030003)]) (width := 2) (p := 0x1020000000000000000)
  · decide +kernel
  · exact familyCons vB0 <| familyNil
  · exact familyCons vB163n0 <| familyNil
  · decide +kernel
  · decide +kernel
def B163n2 : Cell := (4, [0x320000000000000032, 0x330000000000000033, 0x1100110000000000110011, 0x300030000000000030003, 0x330033])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n2 : B163n2.2.Nodup ∧ Closed B163.mask B163.goal B163n2 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := []) (seen := []) (h := [(0x320000000000000032, 0x100010000000000010001, 0x330000000000000033), (0x100010000000000010001, 0x1100110000000000110011, 0x300030000000000030003)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B163n3 : Cell := (3, [0x330000000000000032, 0x330033, 0x1100110000000000110011, 0x300030000000000030003])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n3 : B163n3.2.Nodup ∧ Closed B163.mask B163.goal B163n3 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 2) (bs := []) (seen := []) (h := [(0x330000000000000032, 0x10001, 0x330000000000000033), (0x10001, 0x100010000000000010001, 0x330033), (0x100010000000000010001, 0x1100110000000000110011, 0x300030000000000030003)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B163n4 : Cell := (4, [0x10001, 0x330033, 0x1100110000000000110011, 0x300030000000000030003, 0x330000000000000033])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n4 : B163n4.2.Nodup ∧ Closed B163.mask B163.goal B163n4 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := [B6]) (seen := [B163n3]) (h := [(0x10001, 0x100010000000000010001, 0x330033), (0x100010000000000010001, 0x1100110000000000110011, 0x300030000000000030003)]) (width := 2) (p := 0x1020000000000000000)
  · decide +kernel
  · exact familyCons vB6 <| familyNil
  · exact familyCons vB163n3 <| familyNil
  · decide +kernel
  · decide +kernel
def B163n5 : Cell := (4, [0x320032, 0x330033, 0x1100110000000000110011, 0x300030000000000030003, 0x330000000000000033])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n5 : B163n5.2.Nodup ∧ Closed B163.mask B163.goal B163n5 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := []) (seen := []) (h := [(0x320032, 0x100010000000000010001, 0x330033), (0x100010000000000010001, 0x1100110000000000110011, 0x300030000000000030003)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B163n6 : Cell := (3, [0x30000000000000003, 0x110000000000000011, 0x100010000000000010001, 0x330033])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n6 : B163n6.2.Nodup ∧ Closed B163.mask B163.goal B163n6 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 2) (bs := [B6, B8]) (seen := []) (h := [(0x30000000000000003, 0x330000000000000033, 0x300030000000000030003), (0x110000000000000011, 0x1100110000000000110011, 0x330000000000000033), (0x100010000000000010001, 0x1100110000000000110011, 0x300030000000000030003)]) (width := 2) (p := 0x1000000000000000100000002000000)
  · decide +kernel
  · exact familyCons vB6 <| familyCons vB8 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B163n7 : Cell := (4, [0x110000000000000011, 0x330000000000000033, 0x100010000000000010001, 0x300030000000000030003, 0x330033])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n7 : B163n7.2.Nodup ∧ Closed B163.mask B163.goal B163n7 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := [B6, B8]) (seen := [B163n6]) (h := [(0x110000000000000011, 0x1100110000000000110011, 0x330000000000000033), (0x100010000000000010001, 0x1100110000000000110011, 0x300030000000000030003)]) (width := 2) (p := 0x3010000000000000002000000010000000000)
  · decide +kernel
  · exact familyCons vB6 <| familyCons vB8 <| familyNil
  · exact familyCons vB163n6 <| familyNil
  · decide +kernel
  · decide +kernel
def B163n8 : Cell := (3, [0x30003, 0x110011, 0x100010000000000010001, 0x330000000000000033])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n8 : B163n8.2.Nodup ∧ Closed B163.mask B163.goal B163n8 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 2) (bs := [B0, B8]) (seen := []) (h := [(0x30003, 0x330033, 0x300030000000000030003), (0x110011, 0x1100110000000000110011, 0x330033), (0x100010000000000010001, 0x1100110000000000110011, 0x300030000000000030003)]) (width := 2) (p := 0x1000000000000000100000002000000)
  · decide +kernel
  · exact familyCons vB0 <| familyCons vB8 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B163n9 : Cell := (4, [0x110011, 0x330033, 0x100010000000000010001, 0x300030000000000030003, 0x330000000000000033])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n9 : B163n9.2.Nodup ∧ Closed B163.mask B163.goal B163n9 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := [B0, B8]) (seen := [B163n8]) (h := [(0x110011, 0x1100110000000000110011, 0x330033), (0x100010000000000010001, 0x1100110000000000110011, 0x300030000000000030003)]) (width := 2) (p := 0x3010000000000000002000000010000000000)
  · decide +kernel
  · exact familyCons vB0 <| familyCons vB8 <| familyNil
  · exact familyCons vB163n8 <| familyNil
  · decide +kernel
  · decide +kernel
def B163n10 : Cell := (4, [0x30000000000000003, 0x330000000000000033, 0x100010000000000010001, 0x1100110000000000110011, 0x330033])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n10 : B163n10.2.Nodup ∧ Closed B163.mask B163.goal B163n10 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := [B6, B9]) (seen := [B163n6]) (h := [(0x30000000000000003, 0x300030000000000030003, 0x330000000000000033), (0x100010000000000010001, 0x1100110000000000110011, 0x300030000000000030003)]) (width := 2) (p := 0x3010000000000000002000000010000000000)
  · decide +kernel
  · exact familyCons vB6 <| familyCons vB9 <| familyNil
  · exact familyCons vB163n6 <| familyNil
  · decide +kernel
  · decide +kernel
def B163n11 : Cell := (4, [0x30003, 0x330033, 0x100010000000000010001, 0x1100110000000000110011, 0x330000000000000033])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n11 : B163n11.2.Nodup ∧ Closed B163.mask B163.goal B163n11 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := [B0, B9]) (seen := [B163n8]) (h := [(0x30003, 0x300030000000000030003, 0x330033), (0x100010000000000010001, 0x1100110000000000110011, 0x300030000000000030003)]) (width := 2) (p := 0x3010000000000000002000000010000000000)
  · decide +kernel
  · exact familyCons vB0 <| familyCons vB9 <| familyNil
  · exact familyCons vB163n8 <| familyNil
  · decide +kernel
  · decide +kernel
def B163n12 : Cell := (5, [0x100010000000000010001, 0x1100110000000000110011, 0x300030000000000030003, 0x330000000000000033, 0x330033])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n12 : B163n12.2.Nodup ∧ Closed B163.mask B163.goal B163n12 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B0, B6, B8, B9]) (seen := [B163n1, B163n2, B163n4, B163n5, B163n7, B163n9, B163n10, B163n11]) (h := [(0x100010000000000010001, 0x1100110000000000110011, 0x300030000000000030003)]) (width := 4) (p := 0x30000000c000000030000000b000000040000000a000000040000000900033300400300010008000100070002000600020005000340000003300000)
  · decide +kernel
  · exact familyCons vB0 <| familyCons vB6 <| familyCons vB8 <| familyCons vB9 <| familyNil
  · exact familyCons vB163n1 <| familyCons vB163n2 <| familyCons vB163n4 <| familyCons vB163n5 <| familyCons vB163n7 <| familyCons vB163n9 <| familyCons vB163n10 <| familyCons vB163n11 <| familyNil
  · decide +kernel
  · decide +kernel
def B163n13 : Cell := (5, [0x1000100000000000100010, 0x1100110000000000110011, 0x300030000000000030003, 0x330000000000000033, 0x330033])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n13 : B163n13.2.Nodup ∧ Closed B163.mask B163.goal B163n13 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B0, B6, B8]) (seen := []) (h := [(0x1000100000000000100010, 0x1100110000000000110011, 0x300030000000000030003)]) (width := 2) (p := 0x3000300030003000000000000000000c3c3010301030203020303c003c00)
  · decide +kernel
  · exact familyCons vB0 <| familyCons vB6 <| familyCons vB8 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B163n14 : Cell := (5, [0x200020000000000020002, 0x1100110000000000110011, 0x300030000000000030003, 0x330000000000000033, 0x330033])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n14 : B163n14.2.Nodup ∧ Closed B163.mask B163.goal B163n14 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B0, B6, B8, B9]) (seen := []) (h := [(0x200020000000000020002, 0x1100110000000000110011, 0x300030000000000030003)]) (width := 3) (p := 0x1000001000001000001000c00d80200401000401000801000801000e00000d8000)
  · decide +kernel
  · exact familyCons vB0 <| familyCons vB6 <| familyCons vB8 <| familyCons vB9 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B163n15 : Cell := (5, [0x1300130000000000130013, 0x1100110000000000110011, 0x300030000000000030003, 0x330000000000000033, 0x330033])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n15 : B163n15.2.Nodup ∧ Closed B163.mask B163.goal B163n15 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B0, B6, B8]) (seen := []) (h := [(0x1300130000000000130013, 0x1100110000000000110011, 0x300030000000000030003)]) (width := 2) (p := 0x300c3f10301d3f20302e3f003c003c)
  · decide +kernel
  · exact familyCons vB0 <| familyCons vB6 <| familyCons vB8 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B163n16 : Cell := (4, [0x300020000000000030002, 0x300030000000000030003, 0x1100110000000000110011, 0x330000000000000033, 0x330033])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n16 : B163n16.2.Nodup ∧ Closed B163.mask B163.goal B163n16 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := []) (seen := []) (h := [(0x300020000000000030002, 0x110000000000000011, 0x300030000000000030003), (0x110000000000000011, 0x1100110000000000110011, 0x330000000000000033)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B163n17 : Cell := (3, [0x300030000000000030002, 0x330033, 0x1100110000000000110011, 0x330000000000000033])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n17 : B163n17.2.Nodup ∧ Closed B163.mask B163.goal B163n17 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 2) (bs := []) (seen := []) (h := [(0x300030000000000030002, 0x11, 0x300030000000000030003), (0x11, 0x110000000000000011, 0x330033), (0x110000000000000011, 0x1100110000000000110011, 0x330000000000000033)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B163n18 : Cell := (4, [0x11, 0x330033, 0x1100110000000000110011, 0x330000000000000033, 0x300030000000000030003])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n18 : B163n18.2.Nodup ∧ Closed B163.mask B163.goal B163n18 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := [B8]) (seen := [B163n17]) (h := [(0x11, 0x110000000000000011, 0x330033), (0x110000000000000011, 0x1100110000000000110011, 0x330000000000000033)]) (width := 2) (p := 0x1020000000000000000)
  · decide +kernel
  · exact familyCons vB8 <| familyNil
  · exact familyCons vB163n17 <| familyNil
  · decide +kernel
  · decide +kernel
def B163n19 : Cell := (4, [0x330022, 0x330033, 0x1100110000000000110011, 0x330000000000000033, 0x300030000000000030003])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n19 : B163n19.2.Nodup ∧ Closed B163.mask B163.goal B163n19 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := []) (seen := []) (h := [(0x330022, 0x110000000000000011, 0x330033), (0x110000000000000011, 0x1100110000000000110011, 0x330000000000000033)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B163n20 : Cell := (3, [0x33, 0x110011, 0x110000000000000011, 0x300030000000000030003])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n20 : B163n20.2.Nodup ∧ Closed B163.mask B163.goal B163n20 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 2) (bs := [B0, B6]) (seen := []) (h := [(0x33, 0x330033, 0x330000000000000033), (0x110011, 0x1100110000000000110011, 0x330033), (0x110000000000000011, 0x1100110000000000110011, 0x330000000000000033)]) (width := 2) (p := 0x1000000000000000100000002000000)
  · decide +kernel
  · exact familyCons vB0 <| familyCons vB6 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B163n21 : Cell := (4, [0x110011, 0x330033, 0x110000000000000011, 0x330000000000000033, 0x300030000000000030003])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n21 : B163n21.2.Nodup ∧ Closed B163.mask B163.goal B163n21 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := [B0, B6]) (seen := [B163n20]) (h := [(0x110011, 0x1100110000000000110011, 0x330033), (0x110000000000000011, 0x1100110000000000110011, 0x330000000000000033)]) (width := 2) (p := 0x3010000000000000002000000010000000000)
  · decide +kernel
  · exact familyCons vB0 <| familyCons vB6 <| familyNil
  · exact familyCons vB163n20 <| familyNil
  · decide +kernel
  · decide +kernel
def B163n22 : Cell := (4, [0x30000000000000003, 0x300030000000000030003, 0x110000000000000011, 0x1100110000000000110011, 0x330033])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n22 : B163n22.2.Nodup ∧ Closed B163.mask B163.goal B163n22 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := [B8, B9]) (seen := [B163n6]) (h := [(0x30000000000000003, 0x330000000000000033, 0x300030000000000030003), (0x110000000000000011, 0x1100110000000000110011, 0x330000000000000033)]) (width := 2) (p := 0x3010000000000000002000000010000000000)
  · decide +kernel
  · exact familyCons vB8 <| familyCons vB9 <| familyNil
  · exact familyCons vB163n6 <| familyNil
  · decide +kernel
  · decide +kernel
def B163n23 : Cell := (4, [0x33, 0x330033, 0x110000000000000011, 0x1100110000000000110011, 0x300030000000000030003])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n23 : B163n23.2.Nodup ∧ Closed B163.mask B163.goal B163n23 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := [B0, B9]) (seen := [B163n20]) (h := [(0x33, 0x330000000000000033, 0x330033), (0x110000000000000011, 0x1100110000000000110011, 0x330000000000000033)]) (width := 2) (p := 0x3010000000000000002000000010000000000)
  · decide +kernel
  · exact familyCons vB0 <| familyCons vB9 <| familyNil
  · exact familyCons vB163n20 <| familyNil
  · decide +kernel
  · decide +kernel
def B163n24 : Cell := (5, [0x110000000000000011, 0x1100110000000000110011, 0x330000000000000033, 0x300030000000000030003, 0x330033])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n24 : B163n24.2.Nodup ∧ Closed B163.mask B163.goal B163n24 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B0, B6, B8, B9]) (seen := [B163n1, B163n7, B163n16, B163n18, B163n19, B163n21, B163n22, B163n23]) (h := [(0x110000000000000011, 0x1100110000000000110011, 0x330000000000000033)]) (width := 4) (p := 0x20000000c000000020000000b000000040000000a000000040000000600022200400200010009000100080003000700030005000240000002200000)
  · decide +kernel
  · exact familyCons vB0 <| familyCons vB6 <| familyCons vB8 <| familyCons vB9 <| familyNil
  · exact familyCons vB163n1 <| familyCons vB163n7 <| familyCons vB163n16 <| familyCons vB163n18 <| familyCons vB163n19 <| familyCons vB163n21 <| familyCons vB163n22 <| familyCons vB163n23 <| familyNil
  · decide +kernel
  · decide +kernel
def B163n25 : Cell := (5, [0x1100000000000000110000, 0x1100110000000000110011, 0x330000000000000033, 0x300030000000000030003, 0x330033])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n25 : B163n25.2.Nodup ∧ Closed B163.mask B163.goal B163n25 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B0, B6]) (seen := []) (h := [(0x1100000000000000110000, 0x1100110000000000110011, 0x330000000000000033)]) (width := 2) (p := 0x200020002000200000000000000000082820102010202020202028002800)
  · decide +kernel
  · exact familyCons vB0 <| familyCons vB6 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B163n26 : Cell := (5, [0x220000000000000022, 0x1100110000000000110011, 0x330000000000000033, 0x300030000000000030003, 0x330033])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n26 : B163n26.2.Nodup ∧ Closed B163.mask B163.goal B163n26 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B0, B6, B8, B9]) (seen := []) (h := [(0x220000000000000022, 0x1100110000000000110011, 0x330000000000000033)]) (width := 3) (p := 0x1000001000001000001000800900200401000401000c01000c01000a0000090000)
  · decide +kernel
  · exact familyCons vB0 <| familyCons vB6 <| familyCons vB8 <| familyCons vB9 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B163n27 : Cell := (5, [0x1100330000000000110033, 0x1100110000000000110011, 0x330000000000000033, 0x300030000000000030003, 0x330033])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n27 : B163n27.2.Nodup ∧ Closed B163.mask B163.goal B163n27 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B0, B6]) (seen := []) (h := [(0x1100330000000000110033, 0x1100110000000000110011, 0x330000000000000033)]) (width := 2) (p := 0x20082a1020192a20202a2a00280028)
  · decide +kernel
  · exact familyCons vB0 <| familyCons vB6 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B163n28 : Cell := (4, [0x300030000000000020002, 0x300030000000000030003, 0x1100110000000000110011, 0x330033, 0x330000000000000033])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n28 : B163n28.2.Nodup ∧ Closed B163.mask B163.goal B163n28 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := []) (seen := []) (h := [(0x300030000000000020002, 0x110011, 0x300030000000000030003), (0x110011, 0x1100110000000000110011, 0x330033)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B163n29 : Cell := (4, [0x330000000000000022, 0x330000000000000033, 0x1100110000000000110011, 0x330033, 0x300030000000000030003])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n29 : B163n29.2.Nodup ∧ Closed B163.mask B163.goal B163n29 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := []) (seen := []) (h := [(0x330000000000000022, 0x110011, 0x330000000000000033), (0x110011, 0x1100110000000000110011, 0x330033)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B163n30 : Cell := (4, [0x30003, 0x300030000000000030003, 0x110011, 0x1100110000000000110011, 0x330000000000000033])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n30 : B163n30.2.Nodup ∧ Closed B163.mask B163.goal B163n30 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := [B8, B9]) (seen := [B163n8]) (h := [(0x30003, 0x330033, 0x300030000000000030003), (0x110011, 0x1100110000000000110011, 0x330033)]) (width := 2) (p := 0x3010000000000000002000000010000000000)
  · decide +kernel
  · exact familyCons vB8 <| familyCons vB9 <| familyNil
  · exact familyCons vB163n8 <| familyNil
  · decide +kernel
  · decide +kernel
def B163n31 : Cell := (4, [0x33, 0x330000000000000033, 0x110011, 0x1100110000000000110011, 0x300030000000000030003])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n31 : B163n31.2.Nodup ∧ Closed B163.mask B163.goal B163n31 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := [B6, B9]) (seen := [B163n20]) (h := [(0x33, 0x330033, 0x330000000000000033), (0x110011, 0x1100110000000000110011, 0x330033)]) (width := 2) (p := 0x3010000000000000002000000010000000000)
  · decide +kernel
  · exact familyCons vB6 <| familyCons vB9 <| familyNil
  · exact familyCons vB163n20 <| familyNil
  · decide +kernel
  · decide +kernel
def B163n32 : Cell := (5, [0x110011, 0x1100110000000000110011, 0x330033, 0x300030000000000030003, 0x330000000000000033])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n32 : B163n32.2.Nodup ∧ Closed B163.mask B163.goal B163n32 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B0, B6, B8, B9]) (seen := [B163n4, B163n9, B163n18, B163n21, B163n28, B163n29, B163n30, B163n31]) (h := [(0x110011, 0x1100110000000000110011, 0x330033)]) (width := 4) (p := 0x10000000c000000010000000b000000040000000800000004000000060001110040010002000a000200070003000900030005000140000001100000)
  · decide +kernel
  · exact familyCons vB0 <| familyCons vB6 <| familyCons vB8 <| familyCons vB9 <| familyNil
  · exact familyCons vB163n4 <| familyCons vB163n9 <| familyCons vB163n18 <| familyCons vB163n21 <| familyCons vB163n28 <| familyCons vB163n29 <| familyCons vB163n30 <| familyCons vB163n31 <| familyNil
  · decide +kernel
  · decide +kernel
def B163n33 : Cell := (5, [0x1100110000000000000000, 0x1100110000000000110011, 0x330033, 0x300030000000000030003, 0x330000000000000033])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n33 : B163n33.2.Nodup ∧ Closed B163.mask B163.goal B163n33 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B0]) (seen := []) (h := [(0x1100110000000000000000, 0x1100110000000000110011, 0x330033)]) (width := 1) (p := 0x404040400000000264444444446060)
  · decide +kernel
  · exact familyCons vB0 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B163n34 : Cell := (5, [0x220022, 0x1100110000000000110011, 0x330033, 0x300030000000000030003, 0x330000000000000033])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n34 : B163n34.2.Nodup ∧ Closed B163.mask B163.goal B163n34 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B0, B6, B8, B9]) (seen := []) (h := [(0x220022, 0x1100110000000000110011, 0x330033)]) (width := 3) (p := 0x1000001000001000001000400480200801000801000c01000c0100060000048000)
  · decide +kernel
  · exact familyCons vB0 <| familyCons vB6 <| familyCons vB8 <| familyCons vB9 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B163n35 : Cell := (5, [0x1100110000000000330033, 0x1100110000000000110011, 0x330033, 0x300030000000000030003, 0x330000000000000033])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n35 : B163n35.2.Nodup ∧ Closed B163.mask B163.goal B163n35 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B0]) (seen := []) (h := [(0x1100110000000000330033, 0x1100110000000000110011, 0x330033)]) (width := 1) (p := 0x427447744770606)
  · decide +kernel
  · exact familyCons vB0 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B163n36 : Cell := (4, [0x1100100000000000110010, 0x1100110000000000110011, 0x300030000000000030003, 0x330000000000000033, 0x330033])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n36 : B163n36.2.Nodup ∧ Closed B163.mask B163.goal B163n36 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := []) (seen := []) (h := [(0x1100100000000000110010, 0x30000000000000003, 0x1100110000000000110011), (0x30000000000000003, 0x300030000000000030003, 0x330000000000000033)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B163n37 : Cell := (3, [0x1100110000000000110010, 0x330033, 0x300030000000000030003, 0x330000000000000033])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n37 : B163n37.2.Nodup ∧ Closed B163.mask B163.goal B163n37 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 2) (bs := []) (seen := []) (h := [(0x1100110000000000110010, 0x3, 0x1100110000000000110011), (0x3, 0x30000000000000003, 0x330033), (0x30000000000000003, 0x300030000000000030003, 0x330000000000000033)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B163n38 : Cell := (4, [0x3, 0x330033, 0x300030000000000030003, 0x330000000000000033, 0x1100110000000000110011])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n38 : B163n38.2.Nodup ∧ Closed B163.mask B163.goal B163n38 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := [B9]) (seen := [B163n37]) (h := [(0x3, 0x30000000000000003, 0x330033), (0x30000000000000003, 0x300030000000000030003, 0x330000000000000033)]) (width := 2) (p := 0x1020000000000000000)
  · decide +kernel
  · exact familyCons vB9 <| familyNil
  · exact familyCons vB163n37 <| familyNil
  · decide +kernel
  · decide +kernel
def B163n39 : Cell := (4, [0x330030, 0x330033, 0x300030000000000030003, 0x330000000000000033, 0x1100110000000000110011])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n39 : B163n39.2.Nodup ∧ Closed B163.mask B163.goal B163n39 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := []) (seen := []) (h := [(0x330030, 0x30000000000000003, 0x330033), (0x30000000000000003, 0x300030000000000030003, 0x330000000000000033)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B163n40 : Cell := (3, [0x33, 0x30003, 0x30000000000000003, 0x1100110000000000110011])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n40 : B163n40.2.Nodup ∧ Closed B163.mask B163.goal B163n40 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 2) (bs := [B0, B6]) (seen := []) (h := [(0x33, 0x330033, 0x330000000000000033), (0x30003, 0x300030000000000030003, 0x330033), (0x30000000000000003, 0x300030000000000030003, 0x330000000000000033)]) (width := 2) (p := 0x1000000000000000100000002000000)
  · decide +kernel
  · exact familyCons vB0 <| familyCons vB6 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B163n41 : Cell := (4, [0x30003, 0x330033, 0x30000000000000003, 0x330000000000000033, 0x1100110000000000110011])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n41 : B163n41.2.Nodup ∧ Closed B163.mask B163.goal B163n41 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := [B0, B6]) (seen := [B163n40]) (h := [(0x30003, 0x300030000000000030003, 0x330033), (0x30000000000000003, 0x300030000000000030003, 0x330000000000000033)]) (width := 2) (p := 0x3010000000000000002000000010000000000)
  · decide +kernel
  · exact familyCons vB0 <| familyCons vB6 <| familyNil
  · exact familyCons vB163n40 <| familyNil
  · decide +kernel
  · decide +kernel
def B163n42 : Cell := (4, [0x33, 0x330033, 0x30000000000000003, 0x300030000000000030003, 0x1100110000000000110011])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n42 : B163n42.2.Nodup ∧ Closed B163.mask B163.goal B163n42 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := [B0, B8]) (seen := [B163n40]) (h := [(0x33, 0x330000000000000033, 0x330033), (0x30000000000000003, 0x300030000000000030003, 0x330000000000000033)]) (width := 2) (p := 0x3010000000000000002000000010000000000)
  · decide +kernel
  · exact familyCons vB0 <| familyCons vB8 <| familyNil
  · exact familyCons vB163n40 <| familyNil
  · decide +kernel
  · decide +kernel
def B163n43 : Cell := (5, [0x30000000000000003, 0x300030000000000030003, 0x330000000000000033, 0x1100110000000000110011, 0x330033])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n43 : B163n43.2.Nodup ∧ Closed B163.mask B163.goal B163n43 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B0, B6, B8, B9]) (seen := [B163n1, B163n10, B163n22, B163n36, B163n38, B163n39, B163n41, B163n42]) (h := [(0x30000000000000003, 0x300030000000000030003, 0x330000000000000033)]) (width := 4) (p := 0x20000000c0000000200000007000000030000000b00000003000000060002220030020001000a000100090004000800040005000230000002200000)
  · decide +kernel
  · exact familyCons vB0 <| familyCons vB6 <| familyCons vB8 <| familyCons vB9 <| familyNil
  · exact familyCons vB163n1 <| familyCons vB163n10 <| familyCons vB163n22 <| familyCons vB163n36 <| familyCons vB163n38 <| familyCons vB163n39 <| familyCons vB163n41 <| familyCons vB163n42 <| familyNil
  · decide +kernel
  · decide +kernel
def B163n44 : Cell := (5, [0x300000000000000030000, 0x300030000000000030003, 0x330000000000000033, 0x1100110000000000110011, 0x330033])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n44 : B163n44.2.Nodup ∧ Closed B163.mask B163.goal B163n44 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B0, B6]) (seen := []) (h := [(0x300000000000000030000, 0x300030000000000030003, 0x330000000000000033)]) (width := 2) (p := 0x200020002000200000000000000000082820102010202020202028002800)
  · decide +kernel
  · exact familyCons vB0 <| familyCons vB6 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B163n45 : Cell := (5, [0x300000000000000030, 0x300030000000000030003, 0x330000000000000033, 0x1100110000000000110011, 0x330033])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n45 : B163n45.2.Nodup ∧ Closed B163.mask B163.goal B163n45 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B0, B6, B8]) (seen := []) (h := [(0x300000000000000030, 0x300030000000000030003, 0x330000000000000033)]) (width := 2) (p := 0x3000300030003020280c10301030303030302c002800)
  · decide +kernel
  · exact familyCons vB0 <| familyCons vB6 <| familyCons vB8 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B163n46 : Cell := (5, [0x300330000000000030033, 0x300030000000000030003, 0x330000000000000033, 0x1100110000000000110011, 0x330033])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n46 : B163n46.2.Nodup ∧ Closed B163.mask B163.goal B163n46 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B0, B6]) (seen := []) (h := [(0x300330000000000030033, 0x300030000000000030003, 0x330000000000000033)]) (width := 2) (p := 0x20082a1020192a20202a2a00280028)
  · decide +kernel
  · exact familyCons vB0 <| familyCons vB6 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B163n47 : Cell := (4, [0x1100110000000000100010, 0x1100110000000000110011, 0x300030000000000030003, 0x330033, 0x330000000000000033])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n47 : B163n47.2.Nodup ∧ Closed B163.mask B163.goal B163n47 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := []) (seen := []) (h := [(0x1100110000000000100010, 0x30003, 0x1100110000000000110011), (0x30003, 0x300030000000000030003, 0x330033)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B163n48 : Cell := (4, [0x330000000000000030, 0x330000000000000033, 0x300030000000000030003, 0x330033, 0x1100110000000000110011])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n48 : B163n48.2.Nodup ∧ Closed B163.mask B163.goal B163n48 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := []) (seen := []) (h := [(0x330000000000000030, 0x30003, 0x330000000000000033), (0x30003, 0x300030000000000030003, 0x330033)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B163n49 : Cell := (4, [0x33, 0x330000000000000033, 0x30003, 0x300030000000000030003, 0x1100110000000000110011])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n49 : B163n49.2.Nodup ∧ Closed B163.mask B163.goal B163n49 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := [B6, B8]) (seen := [B163n40]) (h := [(0x33, 0x330033, 0x330000000000000033), (0x30003, 0x300030000000000030003, 0x330033)]) (width := 2) (p := 0x3010000000000000002000000010000000000)
  · decide +kernel
  · exact familyCons vB6 <| familyCons vB8 <| familyNil
  · exact familyCons vB163n40 <| familyNil
  · decide +kernel
  · decide +kernel
def B163n50 : Cell := (5, [0x30003, 0x300030000000000030003, 0x330033, 0x1100110000000000110011, 0x330000000000000033])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n50 : B163n50.2.Nodup ∧ Closed B163.mask B163.goal B163n50 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B0, B6, B8, B9]) (seen := [B163n4, B163n11, B163n30, B163n38, B163n41, B163n47, B163n48, B163n49]) (h := [(0x30003, 0x300030000000000030003, 0x330033)]) (width := 4) (p := 0x10000000c0000000100000007000000030000000900000003000000060001110030010002000b000200080004000a00040005000130000001100000)
  · decide +kernel
  · exact familyCons vB0 <| familyCons vB6 <| familyCons vB8 <| familyCons vB9 <| familyNil
  · exact familyCons vB163n4 <| familyCons vB163n11 <| familyCons vB163n30 <| familyCons vB163n38 <| familyCons vB163n41 <| familyCons vB163n47 <| familyCons vB163n48 <| familyCons vB163n49 <| familyNil
  · decide +kernel
  · decide +kernel
def B163n51 : Cell := (5, [0x300030000000000000000, 0x300030000000000030003, 0x330033, 0x1100110000000000110011, 0x330000000000000033])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n51 : B163n51.2.Nodup ∧ Closed B163.mask B163.goal B163n51 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B0]) (seen := []) (h := [(0x300030000000000000000, 0x300030000000000030003, 0x330033)]) (width := 1) (p := 0x404040400000000264444444446060)
  · decide +kernel
  · exact familyCons vB0 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B163n52 : Cell := (5, [0x300030, 0x300030000000000030003, 0x330033, 0x1100110000000000110011, 0x330000000000000033])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n52 : B163n52.2.Nodup ∧ Closed B163.mask B163.goal B163n52 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B0, B6, B8]) (seen := []) (h := [(0x300030, 0x300030000000000030003, 0x330033)]) (width := 2) (p := 0x3000300030003010140c20302030303030301c001400)
  · decide +kernel
  · exact familyCons vB0 <| familyCons vB6 <| familyCons vB8 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B163n53 : Cell := (5, [0x300030000000000330033, 0x300030000000000030003, 0x330033, 0x1100110000000000110011, 0x330000000000000033])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n53 : B163n53.2.Nodup ∧ Closed B163.mask B163.goal B163n53 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B0]) (seen := []) (h := [(0x300030000000000330033, 0x300030000000000030003, 0x330033)]) (width := 1) (p := 0x427447744770606)
  · decide +kernel
  · exact familyCons vB0 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B163n54 : Cell := (4, [0x1100110000000000110000, 0x1100110000000000110011, 0x330000000000000033, 0x330033, 0x300030000000000030003])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n54 : B163n54.2.Nodup ∧ Closed B163.mask B163.goal B163n54 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := []) (seen := []) (h := [(0x1100110000000000110000, 0x33, 0x1100110000000000110011), (0x33, 0x330000000000000033, 0x330033)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B163n55 : Cell := (4, [0x300030000000000030000, 0x300030000000000030003, 0x330000000000000033, 0x330033, 0x1100110000000000110011])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n55 : B163n55.2.Nodup ∧ Closed B163.mask B163.goal B163n55 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := []) (seen := []) (h := [(0x300030000000000030000, 0x33, 0x300030000000000030003), (0x33, 0x330000000000000033, 0x330033)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B163n56 : Cell := (5, [0x33, 0x330000000000000033, 0x330033, 0x1100110000000000110011, 0x300030000000000030003])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n56 : B163n56.2.Nodup ∧ Closed B163.mask B163.goal B163n56 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B0, B6, B8, B9]) (seen := [B163n18, B163n23, B163n31, B163n38, B163n42, B163n49, B163n54, B163n55]) (h := [(0x33, 0x330000000000000033, 0x330033)]) (width := 4) (p := 0x10000000a0000000100000007000000020000000900000002000000060001110020010003000c000300080004000b00040005000120000001100000)
  · decide +kernel
  · exact familyCons vB0 <| familyCons vB6 <| familyCons vB8 <| familyCons vB9 <| familyNil
  · exact familyCons vB163n18 <| familyCons vB163n23 <| familyCons vB163n31 <| familyCons vB163n38 <| familyCons vB163n42 <| familyCons vB163n49 <| familyCons vB163n54 <| familyCons vB163n55 <| familyNil
  · decide +kernel
  · decide +kernel
def B163n57 : Cell := (5, [0x330000000000000000, 0x330000000000000033, 0x330033, 0x1100110000000000110011, 0x300030000000000030003])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n57 : B163n57.2.Nodup ∧ Closed B163.mask B163.goal B163n57 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B0]) (seen := []) (h := [(0x330000000000000000, 0x330000000000000033, 0x330033)]) (width := 1) (p := 0x404040400000000264444444446060)
  · decide +kernel
  · exact familyCons vB0 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B163n58 : Cell := (5, [0x330000, 0x330000000000000033, 0x330033, 0x1100110000000000110011, 0x300030000000000030003])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n58 : B163n58.2.Nodup ∧ Closed B163.mask B163.goal B163n58 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B0, B6]) (seen := []) (h := [(0x330000, 0x330000000000000033, 0x330033)]) (width := 2) (p := 0x20002000200020101408202020202020202018001400)
  · decide +kernel
  · exact familyCons vB0 <| familyCons vB6 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B163n59 : Cell := (5, [0x330000000000330033, 0x330000000000000033, 0x330033, 0x1100110000000000110011, 0x300030000000000030003])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n59 : B163n59.2.Nodup ∧ Closed B163.mask B163.goal B163n59 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B0]) (seen := []) (h := [(0x330000000000330033, 0x330000000000000033, 0x330033)]) (width := 1) (p := 0x427447744770606)
  · decide +kernel
  · exact familyCons vB0 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B163n60 : Cell := (6, [0x1100110000000000110011, 0x300030000000000030003, 0x330000000000000033, 0x330033])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163n60 : B163n60.2.Nodup ∧ Closed B163.mask B163.goal B163n60 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := []) (seen := [B163n12, B163n13, B163n14, B163n15, B163n24, B163n25, B163n26, B163n27, B163n32, B163n33, B163n34, B163n35, B163n43, B163n44, B163n45, B163n46, B163n50, B163n51, B163n52, B163n53, B163n56, B163n57, B163n58, B163n59]) (h := []) (width := 5) (p := 0xc0000b8000b0000a8000a000098000900008800080000780007000068000600005800050000480004000038000300002800020000180001000008000)
  · decide +kernel
  · exact familyNil
  · exact familyCons vB163n12 <| familyCons vB163n13 <| familyCons vB163n14 <| familyCons vB163n15 <| familyCons vB163n24 <| familyCons vB163n25 <| familyCons vB163n26 <| familyCons vB163n27 <| familyCons vB163n32 <| familyCons vB163n33 <| familyCons vB163n34 <| familyCons vB163n35 <| familyCons vB163n43 <| familyCons vB163n44 <| familyCons vB163n45 <| familyCons vB163n46 <| familyCons vB163n50 <| familyCons vB163n51 <| familyCons vB163n52 <| familyCons vB163n53 <| familyCons vB163n56 <| familyCons vB163n57 <| familyCons vB163n58 <| familyCons vB163n59 <| familyNil
  · decide +kernel
  · decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB163 : Valid B163 := by
  apply small_bound (bs := []) (seen := [B163n60]) (width := 1) (p := 0x40000000)
  · decide +kernel
  · exact familyNil
  · exact familyCons vB163n60 <| familyNil
  · decide +kernel
  · apply canon_checked; decide +kernel
  · decide +kernel
end PEqualNP.Outside.L_meta_10626.SignedCert.GraphB

namespace PEqualNP.Outside.L_meta_10626.SignedCert.GraphB
def B164 : Bound := ⟨0x505000005050000050500000505, [0x0, 0x101000001010000010100000101, 0x5000000050000000500000005, 0x5050000000000000505, 0x50500000505], 0x10000000100000105, 7⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB164 : Valid B164 := by
  apply transfer vB163 0x3568000316000000000000000000254800021400000000000000000000000000000000000000000000000000000000000000000000000000152800011200000000000000000005080000100 <;> decide +kernel
end PEqualNP.Outside.L_meta_10626.SignedCert.GraphB

namespace PEqualNP.Outside.L_meta_10626.SignedCert.GraphB
def B217 : Bound := ⟨0xffff0000ffff, [0x0, 0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff], 0x110000135f, 7⟩
def B217n0 : Cell := (5, [0x111100001111, 0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB217n0 : B217n0.2.Nodup ∧ Closed B217.mask B217.goal B217n0 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B133, B134]) (seen := []) (h := [(0x111100001111, 0x555500005555, 0x333300003333)]) (width := 2) (p := 0x100000000000000000000000000000102000000000000)
  · decide +kernel
  · exact familyCons vB133 <| familyCons vB134 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B217n1 : Cell := (5, [0x444400004444, 0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB217n1 : B217n1.2.Nodup ∧ Closed B217.mask B217.goal B217n1 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B133, B134]) (seen := []) (h := [(0x444400004444, 0x555500005555, 0x333300003333)]) (width := 2) (p := 0x102000000000000)
  · decide +kernel
  · exact familyCons vB133 <| familyCons vB134 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B217n2 : Cell := (5, [0x222200002222, 0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB217n2 : B217n2.2.Nodup ∧ Closed B217.mask B217.goal B217n2 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B3, B133]) (seen := []) (h := [(0x222200002222, 0x555500005555, 0x333300003333)]) (width := 2) (p := 0x200000000000000000000010100000000000000000000)
  · decide +kernel
  · exact familyCons vB3 <| familyCons vB133 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B217n3 : Cell := (5, [0x777700007777, 0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB217n3 : B217n3.2.Nodup ∧ Closed B217.mask B217.goal B217n3 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := []) (seen := []) (h := [(0x777700007777, 0x555500005555, 0x333300003333)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B217n4 : Cell := (5, [0x5500000055, 0x555500005555, 0xff000000ff, 0x333300003333, 0xf0f00000f0f, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB217n4 : B217n4.2.Nodup ∧ Closed B217.mask B217.goal B217n4 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B133, B134]) (seen := []) (h := [(0x5500000055, 0x555500005555, 0xff000000ff)]) (width := 2) (p := 0x10000000000000000000000000000010200000000000000000000)
  · decide +kernel
  · exact familyCons vB133 <| familyCons vB134 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B217n5 : Cell := (5, [0x550000005500, 0x555500005555, 0xff000000ff, 0x333300003333, 0xf0f00000f0f, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB217n5 : B217n5.2.Nodup ∧ Closed B217.mask B217.goal B217n5 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B133, B134]) (seen := []) (h := [(0x550000005500, 0x555500005555, 0xff000000ff)]) (width := 2) (p := 0x10200000000000000000000)
  · decide +kernel
  · exact familyCons vB133 <| familyCons vB134 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B217n6 : Cell := (5, [0xaa000000aa, 0x555500005555, 0xff000000ff, 0x333300003333, 0xf0f00000f0f, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB217n6 : B217n6.2.Nodup ∧ Closed B217.mask B217.goal B217n6 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B3, B133]) (seen := []) (h := [(0xaa000000aa, 0x555500005555, 0xff000000ff)]) (width := 2) (p := 0x20000000000000000000000000000000000000101000000000000)
  · decide +kernel
  · exact familyCons vB3 <| familyCons vB133 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B217n7 : Cell := (5, [0x55ff000055ff, 0x555500005555, 0xff000000ff, 0x333300003333, 0xf0f00000f0f, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB217n7 : B217n7.2.Nodup ∧ Closed B217.mask B217.goal B217n7 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := []) (seen := []) (h := [(0x55ff000055ff, 0x555500005555, 0xff000000ff)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B217n8 : Cell := (5, [0x5555, 0x555500005555, 0xffff, 0x333300003333, 0xf0f00000f0f, 0xff000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB217n8 : B217n8.2.Nodup ∧ Closed B217.mask B217.goal B217n8 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B133, B134]) (seen := []) (h := [(0x5555, 0x555500005555, 0xffff)]) (width := 2) (p := 0x20000000000000000000000000000000000000000000000010200000000000000000000)
  · decide +kernel
  · exact familyCons vB133 <| familyCons vB134 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B217n9 : Cell := (5, [0x555500000000, 0x555500005555, 0xffff, 0x333300003333, 0xf0f00000f0f, 0xff000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB217n9 : B217n9.2.Nodup ∧ Closed B217.mask B217.goal B217n9 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B133, B134]) (seen := []) (h := [(0x555500000000, 0x555500005555, 0xffff)]) (width := 2) (p := 0x20000000000000000010000000000000000000000000000010200000000000000000000)
  · decide +kernel
  · exact familyCons vB133 <| familyCons vB134 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B217n10 : Cell := (5, [0xaaaa, 0x555500005555, 0xffff, 0x333300003333, 0xf0f00000f0f, 0xff000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB217n10 : B217n10.2.Nodup ∧ Closed B217.mask B217.goal B217n10 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B133, B134]) (seen := []) (h := [(0xaaaa, 0x555500005555, 0xffff)]) (width := 2) (p := 0x1020000000000000000)
  · decide +kernel
  · exact familyCons vB133 <| familyCons vB134 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B217n11 : Cell := (5, [0x55550000ffff, 0x555500005555, 0xffff, 0x333300003333, 0xf0f00000f0f, 0xff000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB217n11 : B217n11.2.Nodup ∧ Closed B217.mask B217.goal B217n11 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B3, B133, B134]) (seen := []) (h := [(0x55550000ffff, 0x555500005555, 0xffff)]) (width := 2) (p := 0x20000000000000000000000000101000002030000010100000000)
  · decide +kernel
  · exact familyCons vB3 <| familyCons vB133 <| familyCons vB134 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B217n12 : Cell := (5, [0x3300000033, 0x333300003333, 0xff000000ff, 0x555500005555, 0xf0f00000f0f, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB217n12 : B217n12.2.Nodup ∧ Closed B217.mask B217.goal B217n12 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B125]) (seen := []) (h := [(0x3300000033, 0x333300003333, 0xff000000ff)]) (width := 1) (p := 0x1000000000000000000)
  · decide +kernel
  · exact familyCons vB125 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B217n13 : Cell := (5, [0x330000003300, 0x333300003333, 0xff000000ff, 0x555500005555, 0xf0f00000f0f, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB217n13 : B217n13.2.Nodup ∧ Closed B217.mask B217.goal B217n13 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := []) (seen := []) (h := [(0x330000003300, 0x333300003333, 0xff000000ff)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B217n14 : Cell := (5, [0xcc000000cc, 0x333300003333, 0xff000000ff, 0x555500005555, 0xf0f00000f0f, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB217n14 : B217n14.2.Nodup ∧ Closed B217.mask B217.goal B217n14 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := []) (seen := []) (h := [(0xcc000000cc, 0x333300003333, 0xff000000ff)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B217n15 : Cell := (5, [0x33ff000033ff, 0x333300003333, 0xff000000ff, 0x555500005555, 0xf0f00000f0f, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB217n15 : B217n15.2.Nodup ∧ Closed B217.mask B217.goal B217n15 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B3, B125, B133, B134]) (seen := []) (h := [(0x33ff000033ff, 0x333300003333, 0xff000000ff)]) (width := 3) (p := 0x2000000002002000000003004000000001002000000000000)
  · decide +kernel
  · exact familyCons vB3 <| familyCons vB125 <| familyCons vB133 <| familyCons vB134 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B217n16 : Cell := (4, [0xff000000cc, 0x333300003333, 0xffff, 0x555500005555, 0xf0f00000f0f])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB217n16 : B217n16.2.Nodup ∧ Closed B217.mask B217.goal B217n16 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := []) (seen := []) (h := [(0xff000000cc, 0x3333, 0xff000000ff), (0x3333, 0x333300003333, 0xffff)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B217n17 : Cell := (5, [0x3333, 0x333300003333, 0xffff, 0x555500005555, 0xf0f00000f0f, 0xff000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB217n17 : B217n17.2.Nodup ∧ Closed B217.mask B217.goal B217n17 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B125]) (seen := [B217n16]) (h := [(0x3333, 0x333300003333, 0xffff)]) (width := 2) (p := 0x1020000000000000000000000000000)
  · decide +kernel
  · exact familyCons vB125 <| familyNil
  · exact familyCons vB217n16 <| familyNil
  · decide +kernel
  · decide +kernel
def B217n18 : Cell := (5, [0x333300000000, 0x333300003333, 0xffff, 0x555500005555, 0xf0f00000f0f, 0xff000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB217n18 : B217n18.2.Nodup ∧ Closed B217.mask B217.goal B217n18 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B133, B134]) (seen := []) (h := [(0x333300000000, 0x333300003333, 0xffff)]) (width := 2) (p := 0x10200000000000000000000)
  · decide +kernel
  · exact familyCons vB133 <| familyCons vB134 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B217n19 : Cell := (5, [0xcccc, 0x333300003333, 0xffff, 0x555500005555, 0xf0f00000f0f, 0xff000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB217n19 : B217n19.2.Nodup ∧ Closed B217.mask B217.goal B217n19 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := []) (seen := []) (h := [(0xcccc, 0x333300003333, 0xffff)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B217n20 : Cell := (5, [0x33330000ffff, 0x333300003333, 0xffff, 0x555500005555, 0xf0f00000f0f, 0xff000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB217n20 : B217n20.2.Nodup ∧ Closed B217.mask B217.goal B217n20 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B3, B125, B126, B133, B134]) (seen := []) (h := [(0x33330000ffff, 0x333300003333, 0xffff)]) (width := 3) (p := 0x2003000000004005000000001003000000000000)
  · decide +kernel
  · exact familyCons vB3 <| familyCons vB125 <| familyCons vB126 <| familyCons vB133 <| familyCons vB134 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B217n21 : Cell := (4, [0x333300003300, 0xff000000ff, 0xffff, 0x555500005555, 0xf0f00000f0f])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB217n21 : B217n21.2.Nodup ∧ Closed B217.mask B217.goal B217n21 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := []) (seen := []) (h := [(0x333300003300, 0xff, 0x333300003333), (0xff, 0xff000000ff, 0xffff)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B217n22 : Cell := (5, [0xff, 0xff000000ff, 0xffff, 0x555500005555, 0x333300003333, 0xf0f00000f0f])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB217n22 : B217n22.2.Nodup ∧ Closed B217.mask B217.goal B217n22 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B126]) (seen := [B217n21]) (h := [(0xff, 0xff000000ff, 0xffff)]) (width := 2) (p := 0x10200000000000000000000)
  · decide +kernel
  · exact familyCons vB126 <| familyNil
  · exact familyCons vB217n21 <| familyNil
  · decide +kernel
  · decide +kernel
def B217n23 : Cell := (5, [0xff00000000, 0xff000000ff, 0xffff, 0x555500005555, 0x333300003333, 0xf0f00000f0f])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB217n23 : B217n23.2.Nodup ∧ Closed B217.mask B217.goal B217n23 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B133, B134]) (seen := []) (h := [(0xff00000000, 0xff000000ff, 0xffff)]) (width := 2) (p := 0x1020000000000000000000000000000)
  · decide +kernel
  · exact familyCons vB133 <| familyCons vB134 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B217n24 : Cell := (5, [0xff00, 0xff000000ff, 0xffff, 0x555500005555, 0x333300003333, 0xf0f00000f0f])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB217n24 : B217n24.2.Nodup ∧ Closed B217.mask B217.goal B217n24 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := []) (seen := []) (h := [(0xff00, 0xff000000ff, 0xffff)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B217n25 : Cell := (5, [0xff0000ffff, 0xff000000ff, 0xffff, 0x555500005555, 0x333300003333, 0xf0f00000f0f])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB217n25 : B217n25.2.Nodup ∧ Closed B217.mask B217.goal B217n25 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B3, B125, B133, B134]) (seen := []) (h := [(0xff0000ffff, 0xff000000ff, 0xffff)]) (width := 3) (p := 0x3004000000002002000000001002000000000000)
  · decide +kernel
  · exact familyCons vB3 <| familyCons vB125 <| familyCons vB133 <| familyCons vB134 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B217n26 : Cell := (6, [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB217n26 : B217n26.2.Nodup ∧ Closed B217.mask B217.goal B217n26 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B133, B134]) (seen := [B217n0, B217n1, B217n2, B217n3, B217n4, B217n5, B217n6, B217n7, B217n8, B217n9, B217n10, B217n11, B217n12, B217n13, B217n14, B217n15, B217n17, B217n18, B217n19, B217n20, B217n22, B217n23, B217n24, B217n25]) (h := []) (width := 5) (p := 0xd0000c8000c0000b80000800008400080000880008000080000800008000b0000a8000a000098000900008800080000780000800008000080000800070000680006000058000500004800040000380000802008040080000800030000280002000018000)
  · decide +kernel
  · exact familyCons vB133 <| familyCons vB134 <| familyNil
  · exact familyCons vB217n0 <| familyCons vB217n1 <| familyCons vB217n2 <| familyCons vB217n3 <| familyCons vB217n4 <| familyCons vB217n5 <| familyCons vB217n6 <| familyCons vB217n7 <| familyCons vB217n8 <| familyCons vB217n9 <| familyCons vB217n10 <| familyCons vB217n11 <| familyCons vB217n12 <| familyCons vB217n13 <| familyCons vB217n14 <| familyCons vB217n15 <| familyCons vB217n17 <| familyCons vB217n18 <| familyCons vB217n19 <| familyCons vB217n20 <| familyCons vB217n22 <| familyCons vB217n23 <| familyCons vB217n24 <| familyCons vB217n25 <| familyNil
  · decide +kernel
  · decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB217 : Valid B217 := by
  apply small_bound (bs := []) (seen := [B217n26]) (width := 1) (p := 0x4000000000000000)
  · decide +kernel
  · exact familyNil
  · exact familyCons vB217n26 <| familyNil
  · decide +kernel
  · apply canon_checked; decide +kernel
  · decide +kernel
end PEqualNP.Outside.L_meta_10626.SignedCert.GraphB

namespace PEqualNP.Outside.L_meta_10626.SignedCert.GraphB
def B221 : Bound := ⟨0xff000000ff000000ff000000ff, [0x0, 0x55000000550000005500000055, 0x33000000330000003300000033, 0xf0000000f0000000f0000000f, 0xff00000000000000ff, 0xff000000ff], 0x1000000110000005f, 7⟩
def B221n0 : Cell := (6, [0x55000000550000005500000055, 0x33000000330000003300000033, 0xf0000000f0000000f0000000f, 0xff00000000000000ff, 0xff000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB221n0 : B221n0.2.Nodup ∧ Closed B221.mask B221.goal B221n0 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B141, B152, B153, B154]) (seen := []) (h := []) (width := 3) (p := 0x200200200200400400400400200240200240600600600600200200200200400400400400800800800800200200200200400400400400600600618620)
  · decide +kernel
  · exact familyCons vB141 <| familyCons vB152 <| familyCons vB153 <| familyCons vB154 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB221 : Valid B221 := by
  apply small_bound (bs := []) (seen := [B221n0]) (width := 1) (p := 0x4000000000000000)
  · decide +kernel
  · exact familyNil
  · exact familyCons vB221n0 <| familyNil
  · decide +kernel
  · apply canon_checked; decide +kernel
  · decide +kernel
end PEqualNP.Outside.L_meta_10626.SignedCert.GraphB

namespace PEqualNP.Outside.L_meta_10626.SignedCert.GraphB
def B222 : Bound := ⟨0x3333000033330000333300003333, [0x0, 0x1111000011110000111100001111, 0x303000003030000030300000303, 0x33000000330000003300000033, 0x33330000000000003333, 0x333300003333], 0x10000001100001313, 7⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB222 : Valid B222 := by
  apply transfer vB221 0xdb374c9cb170c1000000000000000000000000000000000000000000d933448c9130400000000000000000000000000000000000000000005a354894a1508100000000000000000000000000000000000000000058314084811000 <;> decide +kernel
end PEqualNP.Outside.L_meta_10626.SignedCert.GraphB

namespace PEqualNP.Outside.L_meta_10626.SignedCert.GraphB
def B225 : Bound := ⟨0xffff000000000000ffff, [0x0, 0x55550000000000005555, 0x33330000000000003333, 0xf0f0000000000000f0f, 0xff00000000000000ff, 0xffff], 0x1000000000000135f, 8⟩
def B225n0 : Cell := (5, [0x1010000000000000101, 0xf0f0000000000000f0f, 0x55550000000000005555, 0x33330000000000003333, 0xff00000000000000ff, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n0 : B225n0.2.Nodup ∧ Closed B225.mask B225.goal B225n0 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B142]) (seen := []) (h := [(0x1010000000000000101, 0x11110000000000001111, 0xf0f0000000000000f0f), (0x11110000000000001111, 0x55550000000000005555, 0x33330000000000003333)]) (width := 1) (p := 0x100000000000000000)
  · decide +kernel
  · exact familyCons vB142 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n1 : Cell := (5, [0xe0e0000000000000e0e, 0xf0f0000000000000f0f, 0x55550000000000005555, 0x33330000000000003333, 0xff00000000000000ff, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n1 : B225n1.2.Nodup ∧ Closed B225.mask B225.goal B225n1 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B142]) (seen := []) (h := [(0xe0e0000000000000e0e, 0x11110000000000001111, 0xf0f0000000000000f0f), (0x11110000000000001111, 0x55550000000000005555, 0x33330000000000003333)]) (width := 1) (p := 0x10000)
  · decide +kernel
  · exact familyCons vB142 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n2 : Cell := (5, [0x110000000000000011, 0xff00000000000000ff, 0x55550000000000005555, 0x33330000000000003333, 0xf0f0000000000000f0f, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n2 : B225n2.2.Nodup ∧ Closed B225.mask B225.goal B225n2 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B141]) (seen := []) (h := [(0x110000000000000011, 0x11110000000000001111, 0xff00000000000000ff), (0x11110000000000001111, 0x55550000000000005555, 0x33330000000000003333)]) (width := 1) (p := 0x1000000000000000000000)
  · decide +kernel
  · exact familyCons vB141 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n3 : Cell := (5, [0xee00000000000000ee, 0xff00000000000000ff, 0x55550000000000005555, 0x33330000000000003333, 0xf0f0000000000000f0f, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n3 : B225n3.2.Nodup ∧ Closed B225.mask B225.goal B225n3 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B141]) (seen := []) (h := [(0xee00000000000000ee, 0x11110000000000001111, 0xff00000000000000ff), (0x11110000000000001111, 0x55550000000000005555, 0x33330000000000003333)]) (width := 1) (p := 0x100000000)
  · decide +kernel
  · exact familyCons vB141 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n4 : Cell := (4, [0xf0f0000000000000e0e, 0xffff, 0x55550000000000005555, 0x33330000000000003333, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n4 : B225n4.2.Nodup ∧ Closed B225.mask B225.goal B225n4 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := []) (seen := []) (h := [(0xf0f0000000000000e0e, 0x1111, 0xf0f0000000000000f0f), (0x1111, 0x11110000000000001111, 0xffff), (0x11110000000000001111, 0x55550000000000005555, 0x33330000000000003333)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n5 : Cell := (4, [0xff00000000000000ee, 0xffff, 0x55550000000000005555, 0x33330000000000003333, 0xf0f0000000000000f0f])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n5 : B225n5.2.Nodup ∧ Closed B225.mask B225.goal B225n5 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := []) (seen := []) (h := [(0xff00000000000000ee, 0x1111, 0xff00000000000000ff), (0x1111, 0x11110000000000001111, 0xffff), (0x11110000000000001111, 0x55550000000000005555, 0x33330000000000003333)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n6 : Cell := (5, [0x1111, 0xffff, 0x55550000000000005555, 0x33330000000000003333, 0xf0f0000000000000f0f, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n6 : B225n6.2.Nodup ∧ Closed B225.mask B225.goal B225n6 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B141, B142]) (seen := [B225n4, B225n5]) (h := [(0x1111, 0x11110000000000001111, 0xffff), (0x11110000000000001111, 0x55550000000000005555, 0x33330000000000003333)]) (width := 3) (p := 0x1004000000002003000000000000000000000000)
  · decide +kernel
  · exact familyCons vB141 <| familyCons vB142 <| familyNil
  · exact familyCons vB225n4 <| familyCons vB225n5 <| familyNil
  · decide +kernel
  · decide +kernel
def B225n7 : Cell := (5, [0x11110000000000000000, 0xffff, 0x55550000000000005555, 0x33330000000000003333, 0xf0f0000000000000f0f, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n7 : B225n7.2.Nodup ∧ Closed B225.mask B225.goal B225n7 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := []) (seen := []) (h := [(0x11110000000000000000, 0x11110000000000001111, 0xffff), (0x11110000000000001111, 0x55550000000000005555, 0x33330000000000003333)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n8 : Cell := (5, [0xeeee, 0xffff, 0x55550000000000005555, 0x33330000000000003333, 0xf0f0000000000000f0f, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n8 : B225n8.2.Nodup ∧ Closed B225.mask B225.goal B225n8 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := []) (seen := []) (h := [(0xeeee, 0x11110000000000001111, 0xffff), (0x11110000000000001111, 0x55550000000000005555, 0x33330000000000003333)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n9 : Cell := (4, [0x1010000000000000f0f, 0xffff, 0x55550000000000005555, 0x33330000000000003333, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n9 : B225n9.2.Nodup ∧ Closed B225.mask B225.goal B225n9 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := []) (seen := []) (h := [(0x1010000000000000f0f, 0x1111000000000000ffff, 0xf0f0000000000000f0f), (0x1111000000000000ffff, 0x11110000000000001111, 0xffff), (0x11110000000000001111, 0x55550000000000005555, 0x33330000000000003333)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n10 : Cell := (4, [0x1100000000000000ff, 0xffff, 0x55550000000000005555, 0x33330000000000003333, 0xf0f0000000000000f0f])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n10 : B225n10.2.Nodup ∧ Closed B225.mask B225.goal B225n10 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := []) (seen := []) (h := [(0x1100000000000000ff, 0x1111000000000000ffff, 0xff00000000000000ff), (0x1111000000000000ffff, 0x11110000000000001111, 0xffff), (0x11110000000000001111, 0x55550000000000005555, 0x33330000000000003333)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n11 : Cell := (5, [0x1111000000000000ffff, 0xffff, 0x55550000000000005555, 0x33330000000000003333, 0xf0f0000000000000f0f, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n11 : B225n11.2.Nodup ∧ Closed B225.mask B225.goal B225n11 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B141, B142, B143, B144]) (seen := [B225n9, B225n10]) (h := [(0x1111000000000000ffff, 0x11110000000000001111, 0xffff), (0x11110000000000001111, 0x55550000000000005555, 0x33330000000000003333)]) (width := 3) (p := 0x1006000000002005000000000004000000000003000000)
  · decide +kernel
  · exact familyCons vB141 <| familyCons vB142 <| familyCons vB143 <| familyCons vB144 <| familyNil
  · exact familyCons vB225n9 <| familyCons vB225n10 <| familyNil
  · decide +kernel
  · decide +kernel
def B225n12 : Cell := (5, [0x50500000000000005050, 0xf0f0000000000000f0f, 0x11110000000000001111, 0x33330000000000003333, 0xff00000000000000ff, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n12 : B225n12.2.Nodup ∧ Closed B225.mask B225.goal B225n12 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B142]) (seen := []) (h := [(0x50500000000000005050, 0x55550000000000005555, 0xf0f0000000000000f0f), (0x11110000000000001111, 0x55550000000000005555, 0x33330000000000003333)]) (width := 1) (p := 0x100000)
  · decide +kernel
  · exact familyCons vB142 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n13 : Cell := (5, [0x550000000000000055, 0xff00000000000000ff, 0x11110000000000001111, 0x33330000000000003333, 0xf0f0000000000000f0f, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n13 : B225n13.2.Nodup ∧ Closed B225.mask B225.goal B225n13 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B141]) (seen := []) (h := [(0x550000000000000055, 0x55550000000000005555, 0xff00000000000000ff), (0x11110000000000001111, 0x55550000000000005555, 0x33330000000000003333)]) (width := 1) (p := 0x10000000000000000000100000)
  · decide +kernel
  · exact familyCons vB141 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n14 : Cell := (5, [0x5555, 0xffff, 0x11110000000000001111, 0x33330000000000003333, 0xf0f0000000000000f0f, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n14 : B225n14.2.Nodup ∧ Closed B225.mask B225.goal B225n14 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B142, B143]) (seen := []) (h := [(0x5555, 0x55550000000000005555, 0xffff), (0x11110000000000001111, 0x55550000000000005555, 0x33330000000000003333)]) (width := 2) (p := 0x100000000000000020000000000)
  · decide +kernel
  · exact familyCons vB142 <| familyCons vB143 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n15 : Cell := (5, [0x3030000000000000303, 0xf0f0000000000000f0f, 0x11110000000000001111, 0x55550000000000005555, 0xff00000000000000ff, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n15 : B225n15.2.Nodup ∧ Closed B225.mask B225.goal B225n15 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B142]) (seen := []) (h := [(0x3030000000000000303, 0x33330000000000003333, 0xf0f0000000000000f0f), (0x11110000000000001111, 0x55550000000000005555, 0x33330000000000003333)]) (width := 1) (p := 0x10000000000000000000100000)
  · decide +kernel
  · exact familyCons vB142 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n16 : Cell := (5, [0x33000000000000003300, 0xff00000000000000ff, 0x11110000000000001111, 0x55550000000000005555, 0xf0f0000000000000f0f, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n16 : B225n16.2.Nodup ∧ Closed B225.mask B225.goal B225n16 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B141]) (seen := []) (h := [(0x33000000000000003300, 0x33330000000000003333, 0xff00000000000000ff), (0x11110000000000001111, 0x55550000000000005555, 0x33330000000000003333)]) (width := 1) (p := 0x100000)
  · decide +kernel
  · exact familyCons vB141 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n17 : Cell := (5, [0x3333, 0xffff, 0x11110000000000001111, 0x55550000000000005555, 0xf0f0000000000000f0f, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n17 : B225n17.2.Nodup ∧ Closed B225.mask B225.goal B225n17 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B141, B144]) (seen := []) (h := [(0x3333, 0x33330000000000003333, 0xffff), (0x11110000000000001111, 0x55550000000000005555, 0x33330000000000003333)]) (width := 2) (p := 0x10000000000000000000000020000000000)
  · decide +kernel
  · exact familyCons vB141 <| familyCons vB144 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n18 : Cell := (6, [0x11110000000000001111, 0x55550000000000005555, 0x33330000000000003333, 0xf0f0000000000000f0f, 0xff00000000000000ff, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n18 : B225n18.2.Nodup ∧ Closed B225.mask B225.goal B225n18 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B141, B142, B143, B144]) (seen := [B225n0, B225n1, B225n2, B225n3, B225n6, B225n7, B225n8, B225n11, B225n12, B225n13, B225n14, B225n15, B225n16, B225n17]) (h := [(0x11110000000000001111, 0x55550000000000005555, 0x33330000000000003333)]) (width := 5) (p := 0xc00000000480000c000000004400000000000000c00000000400000000010000000003c00000000100000000038000100000000034000000000c600008000c000300002c00028000240000400020000040001c000080001800008000140000c800000000c6000000)
  · decide +kernel
  · exact familyCons vB141 <| familyCons vB142 <| familyCons vB143 <| familyCons vB144 <| familyNil
  · exact familyCons vB225n0 <| familyCons vB225n1 <| familyCons vB225n2 <| familyCons vB225n3 <| familyCons vB225n6 <| familyCons vB225n7 <| familyCons vB225n8 <| familyCons vB225n11 <| familyCons vB225n12 <| familyCons vB225n13 <| familyCons vB225n14 <| familyCons vB225n15 <| familyCons vB225n16 <| familyCons vB225n17 <| familyNil
  · decide +kernel
  · decide +kernel
def B225n19 : Cell := (6, [0x44440000000000004444, 0x55550000000000005555, 0x33330000000000003333, 0xf0f0000000000000f0f, 0xff00000000000000ff, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n19 : B225n19.2.Nodup ∧ Closed B225.mask B225.goal B225n19 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B141, B142, B143]) (seen := []) (h := [(0x44440000000000004444, 0x55550000000000005555, 0x33330000000000003333)]) (width := 2) (p := 0x30003030003000003000300000000000000000000000000c3c3030303030103010302e3f20303c003c00)
  · decide +kernel
  · exact familyCons vB141 <| familyCons vB142 <| familyCons vB143 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n20 : Cell := (6, [0x22220000000000002222, 0x55550000000000005555, 0x33330000000000003333, 0xf0f0000000000000f0f, 0xff00000000000000ff, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n20 : B225n20.2.Nodup ∧ Closed B225.mask B225.goal B225n20 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B141, B142, B143, B144]) (seen := []) (h := [(0x22220000000000002222, 0x55550000000000005555, 0x33330000000000003333)]) (width := 3) (p := 0x1000001000001000001001000001000000c00d80201001001001000611240401000801000801000e00000d8000)
  · decide +kernel
  · exact familyCons vB141 <| familyCons vB142 <| familyCons vB143 <| familyCons vB144 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n21 : Cell := (6, [0x77770000000000007777, 0x55550000000000005555, 0x33330000000000003333, 0xf0f0000000000000f0f, 0xff00000000000000ff, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n21 : B225n21.2.Nodup ∧ Closed B225.mask B225.goal B225n21 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B141, B142, B143]) (seen := []) (h := [(0x77770000000000007777, 0x55550000000000005555, 0x33330000000000003333)]) (width := 2) (p := 0x300c3c303030301030103020302030003c003c)
  · decide +kernel
  · exact familyCons vB141 <| familyCons vB142 <| familyCons vB143 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n22 : Cell := (5, [0x32320000000000003232, 0x33330000000000003333, 0x55550000000000005555, 0xf0f0000000000000f0f, 0xff00000000000000ff, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n22 : B225n22.2.Nodup ∧ Closed B225.mask B225.goal B225n22 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B7, B141, B142]) (seen := []) (h := [(0x32320000000000003232, 0x5050000000000000505, 0x33330000000000003333), (0x5050000000000000505, 0x55550000000000005555, 0xf0f0000000000000f0f)]) (width := 2) (p := 0x300000000000000000000000000000000000000000000000201000000000000000000000000)
  · decide +kernel
  · exact familyCons vB7 <| familyCons vB141 <| familyCons vB142 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n23 : Cell := (5, [0x50000000000000005, 0xff00000000000000ff, 0x55550000000000005555, 0xf0f0000000000000f0f, 0x33330000000000003333, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n23 : B225n23.2.Nodup ∧ Closed B225.mask B225.goal B225n23 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B142]) (seen := []) (h := [(0x50000000000000005, 0x5050000000000000505, 0xff00000000000000ff), (0x5050000000000000505, 0x55550000000000005555, 0xf0f0000000000000f0f)]) (width := 1) (p := 0x1000000000000000000000000000000000)
  · decide +kernel
  · exact familyCons vB142 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n24 : Cell := (5, [0xfa00000000000000fa, 0xff00000000000000ff, 0x55550000000000005555, 0xf0f0000000000000f0f, 0x33330000000000003333, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n24 : B225n24.2.Nodup ∧ Closed B225.mask B225.goal B225n24 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B7, B142, B143]) (seen := []) (h := [(0xfa00000000000000fa, 0x5050000000000000505, 0xff00000000000000ff), (0x5050000000000000505, 0x55550000000000005555, 0xf0f0000000000000f0f)]) (width := 2) (p := 0x200000000000000000000000000000000000000000000000301000000000000000000000000)
  · decide +kernel
  · exact familyCons vB7 <| familyCons vB142 <| familyCons vB143 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n25 : Cell := (5, [0x505, 0xffff, 0x55550000000000005555, 0xf0f0000000000000f0f, 0x33330000000000003333, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n25 : B225n25.2.Nodup ∧ Closed B225.mask B225.goal B225n25 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B7]) (seen := []) (h := [(0x505, 0x5050000000000000505, 0xffff), (0x5050000000000000505, 0x55550000000000005555, 0xf0f0000000000000f0f)]) (width := 1) (p := 0x101000)
  · decide +kernel
  · exact familyCons vB7 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n26 : Cell := (5, [0x5050000000000000000, 0xffff, 0x55550000000000005555, 0xf0f0000000000000f0f, 0x33330000000000003333, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n26 : B225n26.2.Nodup ∧ Closed B225.mask B225.goal B225n26 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B142]) (seen := []) (h := [(0x5050000000000000000, 0x5050000000000000505, 0xffff), (0x5050000000000000505, 0x55550000000000005555, 0xf0f0000000000000f0f)]) (width := 1) (p := 0x1000000000000000000000000000000000)
  · decide +kernel
  · exact familyCons vB142 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n27 : Cell := (5, [0xfafa, 0xffff, 0x55550000000000005555, 0xf0f0000000000000f0f, 0x33330000000000003333, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n27 : B225n27.2.Nodup ∧ Closed B225.mask B225.goal B225n27 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := []) (seen := []) (h := [(0xfafa, 0x5050000000000000505, 0xffff), (0x5050000000000000505, 0x55550000000000005555, 0xf0f0000000000000f0f)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n28 : Cell := (5, [0x505000000000000ffff, 0xffff, 0x55550000000000005555, 0xf0f0000000000000f0f, 0x33330000000000003333, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n28 : B225n28.2.Nodup ∧ Closed B225.mask B225.goal B225n28 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B7, B141, B142, B143, B144]) (seen := []) (h := [(0x505000000000000ffff, 0x5050000000000000505, 0xffff), (0x5050000000000000505, 0x55550000000000005555, 0xf0f0000000000000f0f)]) (width := 3) (p := 0x3000000000000000000000000000000000000000000000000000000000000000002001000000004001000000000005000000000003000000)
  · decide +kernel
  · exact familyCons vB7 <| familyCons vB141 <| familyCons vB142 <| familyCons vB143 <| familyCons vB144 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n29 : Cell := (5, [0x5555, 0xffff, 0x5050000000000000505, 0xf0f0000000000000f0f, 0x33330000000000003333, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n29 : B225n29.2.Nodup ∧ Closed B225.mask B225.goal B225n29 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B7, B142]) (seen := []) (h := [(0x5555, 0x55550000000000005555, 0xffff), (0x5050000000000000505, 0x55550000000000005555, 0xf0f0000000000000f0f)]) (width := 2) (p := 0x100000000000000000000000002000000020000000000)
  · decide +kernel
  · exact familyCons vB7 <| familyCons vB142 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n30 : Cell := (5, [0xf0f, 0xffff, 0x5050000000000000505, 0x55550000000000005555, 0x33330000000000003333, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n30 : B225n30.2.Nodup ∧ Closed B225.mask B225.goal B225n30 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B7, B144]) (seen := []) (h := [(0xf0f, 0xf0f0000000000000f0f, 0xffff), (0x5050000000000000505, 0x55550000000000005555, 0xf0f0000000000000f0f)]) (width := 2) (p := 0x100000000000000000000000002000000020000000000)
  · decide +kernel
  · exact familyCons vB7 <| familyCons vB144 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n31 : Cell := (6, [0x5050000000000000505, 0x55550000000000005555, 0xf0f0000000000000f0f, 0x33330000000000003333, 0xff00000000000000ff, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n31 : B225n31.2.Nodup ∧ Closed B225.mask B225.goal B225n31 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B141, B142, B143, B144]) (seen := [B225n0, B225n22, B225n23, B225n24, B225n25, B225n26, B225n27, B225n28, B225n29, B225n30]) (h := [(0x5050000000000000505, 0x55550000000000005555, 0xf0f0000000000000f0f)]) (width := 4) (p := 0x20000000e00000000000000000000000000000000000000040000000d00000000000000000000000000000000000222004002000c000b000a000900010008000100070003000600030005000240000002200000)
  · decide +kernel
  · exact familyCons vB141 <| familyCons vB142 <| familyCons vB143 <| familyCons vB144 <| familyNil
  · exact familyCons vB225n0 <| familyCons vB225n22 <| familyCons vB225n23 <| familyCons vB225n24 <| familyCons vB225n25 <| familyCons vB225n26 <| familyCons vB225n27 <| familyCons vB225n28 <| familyCons vB225n29 <| familyCons vB225n30 <| familyNil
  · decide +kernel
  · decide +kernel
def B225n32 : Cell := (5, [0x550000000000000055, 0xff00000000000000ff, 0x50500000000000005050, 0xf0f0000000000000f0f, 0x33330000000000003333, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n32 : B225n32.2.Nodup ∧ Closed B225.mask B225.goal B225n32 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B141]) (seen := []) (h := [(0x550000000000000055, 0x55550000000000005555, 0xff00000000000000ff), (0x50500000000000005050, 0x55550000000000005555, 0xf0f0000000000000f0f)]) (width := 1) (p := 0x100000)
  · decide +kernel
  · exact familyCons vB141 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n33 : Cell := (5, [0x55550000000000000000, 0xffff, 0x50500000000000005050, 0xf0f0000000000000f0f, 0x33330000000000003333, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n33 : B225n33.2.Nodup ∧ Closed B225.mask B225.goal B225n33 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B142]) (seen := []) (h := [(0x55550000000000000000, 0x55550000000000005555, 0xffff), (0x50500000000000005050, 0x55550000000000005555, 0xf0f0000000000000f0f)]) (width := 1) (p := 0x10000000000000000100000)
  · decide +kernel
  · exact familyCons vB142 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n34 : Cell := (6, [0x50500000000000005050, 0x55550000000000005555, 0xf0f0000000000000f0f, 0x33330000000000003333, 0xff00000000000000ff, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n34 : B225n34.2.Nodup ∧ Closed B225.mask B225.goal B225n34 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B141, B142, B144]) (seen := [B225n12, B225n32, B225n33]) (h := [(0x50500000000000005050, 0x55550000000000005555, 0xf0f0000000000000f0f)]) (width := 3) (p := 0x800000800000000000000000000000000c00001800000000c00001400000c0000100010090080080080080080040080040080080080080080090000090000)
  · decide +kernel
  · exact familyCons vB141 <| familyCons vB142 <| familyCons vB144 <| familyNil
  · exact familyCons vB225n12 <| familyCons vB225n32 <| familyCons vB225n33 <| familyNil
  · decide +kernel
  · decide +kernel
def B225n35 : Cell := (5, [0x3030000000000000303, 0x33330000000000003333, 0xa0a0000000000000a0a, 0x55550000000000005555, 0xff00000000000000ff, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n35 : B225n35.2.Nodup ∧ Closed B225.mask B225.goal B225n35 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B143]) (seen := []) (h := [(0x3030000000000000303, 0xf0f0000000000000f0f, 0x33330000000000003333), (0xa0a0000000000000a0a, 0x55550000000000005555, 0xf0f0000000000000f0f)]) (width := 1) (p := 0x100000)
  · decide +kernel
  · exact familyCons vB143 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n36 : Cell := (5, [0xf000000000000000f, 0xff00000000000000ff, 0xa0a0000000000000a0a, 0x55550000000000005555, 0x33330000000000003333, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n36 : B225n36.2.Nodup ∧ Closed B225.mask B225.goal B225n36 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B141]) (seen := []) (h := [(0xf000000000000000f, 0xf0f0000000000000f0f, 0xff00000000000000ff), (0xa0a0000000000000a0a, 0x55550000000000005555, 0xf0f0000000000000f0f)]) (width := 1) (p := 0x100000)
  · decide +kernel
  · exact familyCons vB141 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n37 : Cell := (5, [0xf0f0000000000000000, 0xffff, 0xa0a0000000000000a0a, 0x55550000000000005555, 0x33330000000000003333, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n37 : B225n37.2.Nodup ∧ Closed B225.mask B225.goal B225n37 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B144]) (seen := []) (h := [(0xf0f0000000000000000, 0xf0f0000000000000f0f, 0xffff), (0xa0a0000000000000a0a, 0x55550000000000005555, 0xf0f0000000000000f0f)]) (width := 1) (p := 0x10000000000000000100000)
  · decide +kernel
  · exact familyCons vB144 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n38 : Cell := (6, [0xa0a0000000000000a0a, 0x55550000000000005555, 0xf0f0000000000000f0f, 0x33330000000000003333, 0xff00000000000000ff, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n38 : B225n38.2.Nodup ∧ Closed B225.mask B225.goal B225n38 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B141, B142, B143, B144]) (seen := [B225n35, B225n36, B225n37]) (h := [(0xa0a0000000000000a0a, 0x55550000000000005555, 0xf0f0000000000000f0f)]) (width := 3) (p := 0x800001c00000000800001800000800001400001000001000000000000000000000000000800900201001001001000401000401000c01000c01000a0000090000)
  · decide +kernel
  · exact familyCons vB141 <| familyCons vB142 <| familyCons vB143 <| familyCons vB144 <| familyNil
  · exact familyCons vB225n35 <| familyCons vB225n36 <| familyCons vB225n37 <| familyNil
  · decide +kernel
  · decide +kernel
def B225n39 : Cell := (6, [0x5f5f0000000000005f5f, 0x55550000000000005555, 0xf0f0000000000000f0f, 0x33330000000000003333, 0xff00000000000000ff, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n39 : B225n39.2.Nodup ∧ Closed B225.mask B225.goal B225n39 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B141, B142, B144]) (seen := []) (h := [(0x5f5f0000000000005f5f, 0x55550000000000005555, 0xf0f0000000000000f0f)]) (width := 2) (p := 0x20002000002000200020002030003000003000300030003020082a20202a2a1020192a20202a2a00280028)
  · decide +kernel
  · exact familyCons vB141 <| familyCons vB142 <| familyCons vB144 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n40 : Cell := (5, [0x33220000000000003322, 0x33330000000000003333, 0x55550000000000005555, 0xff00000000000000ff, 0xf0f0000000000000f0f, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n40 : B225n40.2.Nodup ∧ Closed B225.mask B225.goal B225n40 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B143]) (seen := []) (h := [(0x33220000000000003322, 0x550000000000000055, 0x33330000000000003333), (0x550000000000000055, 0x55550000000000005555, 0xff00000000000000ff)]) (width := 1) (p := 0x100000000)
  · decide +kernel
  · exact familyCons vB143 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n41 : Cell := (5, [0xf0a0000000000000f0a, 0xf0f0000000000000f0f, 0x55550000000000005555, 0xff00000000000000ff, 0x33330000000000003333, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n41 : B225n41.2.Nodup ∧ Closed B225.mask B225.goal B225n41 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B141]) (seen := []) (h := [(0xf0a0000000000000f0a, 0x550000000000000055, 0xf0f0000000000000f0f), (0x550000000000000055, 0x55550000000000005555, 0xff00000000000000ff)]) (width := 1) (p := 0x10000)
  · decide +kernel
  · exact familyCons vB141 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n42 : Cell := (4, [0x33330000000000003322, 0xffff, 0x55550000000000005555, 0xff00000000000000ff, 0xf0f0000000000000f0f])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n42 : B225n42.2.Nodup ∧ Closed B225.mask B225.goal B225n42 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := []) (seen := []) (h := [(0x33330000000000003322, 0x55, 0x33330000000000003333), (0x55, 0x550000000000000055, 0xffff), (0x550000000000000055, 0x55550000000000005555, 0xff00000000000000ff)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n43 : Cell := (4, [0xf0f0000000000000f0a, 0xffff, 0x55550000000000005555, 0xff00000000000000ff, 0x33330000000000003333])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n43 : B225n43.2.Nodup ∧ Closed B225.mask B225.goal B225n43 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := []) (seen := []) (h := [(0xf0f0000000000000f0a, 0x55, 0xf0f0000000000000f0f), (0x55, 0x550000000000000055, 0xffff), (0x550000000000000055, 0x55550000000000005555, 0xff00000000000000ff)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n44 : Cell := (5, [0x55, 0xffff, 0x55550000000000005555, 0xff00000000000000ff, 0x33330000000000003333, 0xf0f0000000000000f0f])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n44 : B225n44.2.Nodup ∧ Closed B225.mask B225.goal B225n44 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B142, B143]) (seen := [B225n42, B225n43]) (h := [(0x55, 0x550000000000000055, 0xffff), (0x550000000000000055, 0x55550000000000005555, 0xff00000000000000ff)]) (width := 3) (p := 0x1004000000002003000000000000000000000000)
  · decide +kernel
  · exact familyCons vB142 <| familyCons vB143 <| familyNil
  · exact familyCons vB225n42 <| familyCons vB225n43 <| familyNil
  · decide +kernel
  · decide +kernel
def B225n45 : Cell := (5, [0x550000000000000000, 0xffff, 0x55550000000000005555, 0xff00000000000000ff, 0x33330000000000003333, 0xf0f0000000000000f0f])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n45 : B225n45.2.Nodup ∧ Closed B225.mask B225.goal B225n45 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := []) (seen := []) (h := [(0x550000000000000000, 0x550000000000000055, 0xffff), (0x550000000000000055, 0x55550000000000005555, 0xff00000000000000ff)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n46 : Cell := (5, [0xffaa, 0xffff, 0x55550000000000005555, 0xff00000000000000ff, 0x33330000000000003333, 0xf0f0000000000000f0f])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n46 : B225n46.2.Nodup ∧ Closed B225.mask B225.goal B225n46 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := []) (seen := []) (h := [(0xffaa, 0x550000000000000055, 0xffff), (0x550000000000000055, 0x55550000000000005555, 0xff00000000000000ff)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n47 : Cell := (4, [0x110000000000003333, 0xffff, 0x55550000000000005555, 0xff00000000000000ff, 0xf0f0000000000000f0f])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n47 : B225n47.2.Nodup ∧ Closed B225.mask B225.goal B225n47 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := []) (seen := []) (h := [(0x110000000000003333, 0x55000000000000ffff, 0x33330000000000003333), (0x55000000000000ffff, 0x550000000000000055, 0xffff), (0x550000000000000055, 0x55550000000000005555, 0xff00000000000000ff)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n48 : Cell := (4, [0x50000000000000f0f, 0xffff, 0x55550000000000005555, 0xff00000000000000ff, 0x33330000000000003333])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n48 : B225n48.2.Nodup ∧ Closed B225.mask B225.goal B225n48 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := []) (seen := []) (h := [(0x50000000000000f0f, 0x55000000000000ffff, 0xf0f0000000000000f0f), (0x55000000000000ffff, 0x550000000000000055, 0xffff), (0x550000000000000055, 0x55550000000000005555, 0xff00000000000000ff)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n49 : Cell := (5, [0x55000000000000ffff, 0xffff, 0x55550000000000005555, 0xff00000000000000ff, 0x33330000000000003333, 0xf0f0000000000000f0f])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n49 : B225n49.2.Nodup ∧ Closed B225.mask B225.goal B225n49 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B141, B142, B143, B144]) (seen := [B225n47, B225n48]) (h := [(0x55000000000000ffff, 0x550000000000000055, 0xffff), (0x550000000000000055, 0x55550000000000005555, 0xff00000000000000ff)]) (width := 3) (p := 0x2006000000003005000000000004000000000001000000)
  · decide +kernel
  · exact familyCons vB141 <| familyCons vB142 <| familyCons vB143 <| familyCons vB144 <| familyNil
  · exact familyCons vB225n47 <| familyCons vB225n48 <| familyNil
  · decide +kernel
  · decide +kernel
def B225n50 : Cell := (5, [0x5555, 0xffff, 0x550000000000000055, 0xff00000000000000ff, 0x33330000000000003333, 0xf0f0000000000000f0f])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n50 : B225n50.2.Nodup ∧ Closed B225.mask B225.goal B225n50 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B141, B142]) (seen := []) (h := [(0x5555, 0x55550000000000005555, 0xffff), (0x550000000000000055, 0x55550000000000005555, 0xff00000000000000ff)]) (width := 2) (p := 0x20000000000000000000000010000000000)
  · decide +kernel
  · exact familyCons vB141 <| familyCons vB142 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n51 : Cell := (5, [0xcc00000000000000cc, 0x33330000000000003333, 0x550000000000000055, 0x55550000000000005555, 0xf0f0000000000000f0f, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n51 : B225n51.2.Nodup ∧ Closed B225.mask B225.goal B225n51 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B143]) (seen := []) (h := [(0xcc00000000000000cc, 0xff00000000000000ff, 0x33330000000000003333), (0x550000000000000055, 0x55550000000000005555, 0xff00000000000000ff)]) (width := 1) (p := 0x100000)
  · decide +kernel
  · exact familyCons vB143 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n52 : Cell := (5, [0xf000000000000000f, 0xf0f0000000000000f0f, 0x550000000000000055, 0x55550000000000005555, 0x33330000000000003333, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n52 : B225n52.2.Nodup ∧ Closed B225.mask B225.goal B225n52 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B142]) (seen := []) (h := [(0xf000000000000000f, 0xff00000000000000ff, 0xf0f0000000000000f0f), (0x550000000000000055, 0x55550000000000005555, 0xff00000000000000ff)]) (width := 1) (p := 0x10000000000000000000100000)
  · decide +kernel
  · exact familyCons vB142 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n53 : Cell := (5, [0xff, 0xffff, 0x550000000000000055, 0x55550000000000005555, 0x33330000000000003333, 0xf0f0000000000000f0f])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n53 : B225n53.2.Nodup ∧ Closed B225.mask B225.goal B225n53 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B143, B144]) (seen := []) (h := [(0xff, 0xff00000000000000ff, 0xffff), (0x550000000000000055, 0x55550000000000005555, 0xff00000000000000ff)]) (width := 2) (p := 0x100000000000000020000000000)
  · decide +kernel
  · exact familyCons vB143 <| familyCons vB144 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n54 : Cell := (6, [0x550000000000000055, 0x55550000000000005555, 0xff00000000000000ff, 0x33330000000000003333, 0xf0f0000000000000f0f, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n54 : B225n54.2.Nodup ∧ Closed B225.mask B225.goal B225n54 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B141, B142, B143, B144]) (seen := [B225n2, B225n13, B225n23, B225n32, B225n40, B225n41, B225n44, B225n45, B225n46, B225n49, B225n50, B225n51, B225n52, B225n53]) (h := [(0x550000000000000055, 0x55550000000000005555, 0xff00000000000000ff)]) (width := 5) (p := 0x4000000004800000000040000000044000040000000040000000000000010000000003c00010000000002000000000000001000000000180000420000800040003800034000300002c0000800028000080001c0000c000240000c000140000480000000042000000)
  · decide +kernel
  · exact familyCons vB141 <| familyCons vB142 <| familyCons vB143 <| familyCons vB144 <| familyNil
  · exact familyCons vB225n2 <| familyCons vB225n13 <| familyCons vB225n23 <| familyCons vB225n32 <| familyCons vB225n40 <| familyCons vB225n41 <| familyCons vB225n44 <| familyCons vB225n45 <| familyCons vB225n46 <| familyCons vB225n49 <| familyCons vB225n50 <| familyCons vB225n51 <| familyCons vB225n52 <| familyCons vB225n53 <| familyNil
  · decide +kernel
  · decide +kernel
def B225n55 : Cell := (6, [0x55000000000000005500, 0x55550000000000005555, 0xff00000000000000ff, 0x33330000000000003333, 0xf0f0000000000000f0f, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n55 : B225n55.2.Nodup ∧ Closed B225.mask B225.goal B225n55 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B141]) (seen := []) (h := [(0x55000000000000005500, 0x55550000000000005555, 0xff00000000000000ff)]) (width := 1) (p := 0x404040440400000000000002644444774444446060)
  · decide +kernel
  · exact familyCons vB141 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n56 : Cell := (6, [0xaa00000000000000aa, 0x55550000000000005555, 0xff00000000000000ff, 0x33330000000000003333, 0xf0f0000000000000f0f, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n56 : B225n56.2.Nodup ∧ Closed B225.mask B225.goal B225n56 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B141, B142, B143, B144]) (seen := []) (h := [(0xaa00000000000000aa, 0x55550000000000005555, 0xff00000000000000ff)]) (width := 3) (p := 0x1000001001000001000000001000001000400480201001001001000801000801000e31240c0100060000048000)
  · decide +kernel
  · exact familyCons vB141 <| familyCons vB142 <| familyCons vB143 <| familyCons vB144 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n57 : Cell := (6, [0x55ff00000000000055ff, 0x55550000000000005555, 0xff00000000000000ff, 0x33330000000000003333, 0xf0f0000000000000f0f, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n57 : B225n57.2.Nodup ∧ Closed B225.mask B225.goal B225n57 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B141]) (seen := []) (h := [(0x55ff00000000000055ff, 0x55550000000000005555, 0xff00000000000000ff)]) (width := 1) (p := 0x4264444444444440606)
  · decide +kernel
  · exact familyCons vB141 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n58 : Cell := (5, [0x55550000000000000000, 0x5555, 0xffff, 0x33330000000000003333, 0xf0f0000000000000f0f, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n58 : B225n58.2.Nodup ∧ Closed B225.mask B225.goal B225n58 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B7, B141]) (seen := []) (h := [(0x55550000000000000000, 0x5555, 0x55550000000000005555), (0x5555, 0x55550000000000005555, 0xffff)]) (width := 2) (p := 0x100000000000000000000000000000000000000000000000200)
  · decide +kernel
  · exact familyCons vB7 <| familyCons vB141 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n59 : Cell := (5, [0x33330000000000002222, 0x33330000000000003333, 0x55550000000000005555, 0xffff, 0xf0f0000000000000f0f, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n59 : B225n59.2.Nodup ∧ Closed B225.mask B225.goal B225n59 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := []) (seen := []) (h := [(0x33330000000000002222, 0x5555, 0x33330000000000003333), (0x5555, 0x55550000000000005555, 0xffff)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n60 : Cell := (5, [0xf0f0000000000000a0a, 0x55550000000000005555, 0xffff, 0x33330000000000003333, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n60 : B225n60.2.Nodup ∧ Closed B225.mask B225.goal B225n60 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := []) (seen := []) (h := [(0xf0f0000000000000a0a, 0x5555, 0xf0f0000000000000f0f), (0x5555, 0x55550000000000005555, 0xffff)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n61 : Cell := (5, [0xf0f0000000000000a0a, 0x5555, 0x55550000000000005555, 0xffff, 0x33330000000000003333, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n61 : B225n61.2.Nodup ∧ Closed B225.mask B225.goal B225n61 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B142]) (seen := []) (h := [(0xf0f0000000000000a0a, 0x5555, 0xf0f0000000000000f0f), (0x5555, 0x55550000000000005555, 0xffff)]) (width := 1) (p := 0x10)
  · decide +kernel
  · exact familyCons vB142 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n62 : Cell := (5, [0xf0f0000000000000a0a, 0xf0f0000000000000f0f, 0x55550000000000005555, 0xffff, 0x33330000000000003333, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n62 : B225n62.2.Nodup ∧ Closed B225.mask B225.goal B225n62 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := []) (seen := []) (h := [(0xf0f0000000000000a0a, 0x5555, 0xf0f0000000000000f0f), (0x5555, 0x55550000000000005555, 0xffff)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n63 : Cell := (5, [0xf0f0000000000005f5f, 0x5555, 0x55550000000000005555, 0xffff, 0x33330000000000003333, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n63 : B225n63.2.Nodup ∧ Closed B225.mask B225.goal B225n63 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B7]) (seen := []) (h := [(0xf0f0000000000005f5f, 0x5555, 0xf0f0000000000000f0f), (0x5555, 0x55550000000000005555, 0xffff)]) (width := 1) (p := 0x10000000000000000001)
  · decide +kernel
  · exact familyCons vB7 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n64 : Cell := (5, [0xff00000000000000aa, 0xff00000000000000ff, 0x55550000000000005555, 0xffff, 0x33330000000000003333, 0xf0f0000000000000f0f])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n64 : B225n64.2.Nodup ∧ Closed B225.mask B225.goal B225n64 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := []) (seen := []) (h := [(0xff00000000000000aa, 0x5555, 0xff00000000000000ff), (0x5555, 0x55550000000000005555, 0xffff)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n65 : Cell := (5, [0xf0f, 0xf0f0000000000000f0f, 0x5555, 0x55550000000000005555, 0x33330000000000003333, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n65 : B225n65.2.Nodup ∧ Closed B225.mask B225.goal B225n65 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B7, B142]) (seen := []) (h := [(0xf0f, 0xffff, 0xf0f0000000000000f0f), (0x5555, 0x55550000000000005555, 0xffff)]) (width := 2) (p := 0x100000000000000000000000000000000020000000000)
  · decide +kernel
  · exact familyCons vB7 <| familyCons vB142 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n66 : Cell := (5, [0xf0f0000000000000000, 0xf0f0000000000000f0f, 0x5555, 0x55550000000000005555, 0x33330000000000003333, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n66 : B225n66.2.Nodup ∧ Closed B225.mask B225.goal B225n66 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B142, B144]) (seen := []) (h := [(0xf0f0000000000000000, 0xffff, 0xf0f0000000000000f0f), (0x5555, 0x55550000000000005555, 0xffff)]) (width := 2) (p := 0x2000100000000000000000000000000000000000000)
  · decide +kernel
  · exact familyCons vB142 <| familyCons vB144 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n67 : Cell := (6, [0x5555, 0x55550000000000005555, 0xffff, 0x33330000000000003333, 0xf0f0000000000000f0f, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n67 : B225n67.2.Nodup ∧ Closed B225.mask B225.goal B225n67 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B141, B142, B143, B144]) (seen := [B225n6, B225n14, B225n25, B225n29, B225n44, B225n50, B225n58, B225n59, B225n60, B225n61, B225n62, B225n63, B225n64, B225n65, B225n66]) (h := [(0x5555, 0x55550000000000005555, 0xffff)]) (width := 5) (p := 0x4c00000000480000000000000000000000000000100000000028000000001000000000200000000010000000001800010800008002c000040004400004000240000a0203dcd0080001c0000c000300000c000140001080000000116000000)
  · decide +kernel
  · exact familyCons vB141 <| familyCons vB142 <| familyCons vB143 <| familyCons vB144 <| familyNil
  · exact familyCons vB225n6 <| familyCons vB225n14 <| familyCons vB225n25 <| familyCons vB225n29 <| familyCons vB225n44 <| familyCons vB225n50 <| familyCons vB225n58 <| familyCons vB225n59 <| familyCons vB225n60 <| familyCons vB225n61 <| familyCons vB225n62 <| familyCons vB225n63 <| familyCons vB225n64 <| familyCons vB225n65 <| familyCons vB225n66 <| familyNil
  · decide +kernel
  · decide +kernel
def B225n68 : Cell := (4, [0xdd00000000000000cc, 0x33330000000000003333, 0x55550000000000005555, 0xffff, 0xf0f0000000000000f0f])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n68 : B225n68.2.Nodup ∧ Closed B225.mask B225.goal B225n68 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := []) (seen := []) (h := [(0xdd00000000000000cc, 0x22220000000000003333, 0xff00000000000000ff), (0x22220000000000003333, 0x55550000000000000000, 0x33330000000000003333), (0x55550000000000000000, 0x55550000000000005555, 0xffff)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n69 : Cell := (5, [0x22220000000000003333, 0x33330000000000003333, 0x55550000000000005555, 0xffff, 0xf0f0000000000000f0f, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n69 : B225n69.2.Nodup ∧ Closed B225.mask B225.goal B225n69 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B141]) (seen := [B225n68]) (h := [(0x22220000000000003333, 0x55550000000000000000, 0x33330000000000003333), (0x55550000000000000000, 0x55550000000000005555, 0xffff)]) (width := 2) (p := 0x10200000000000000000000000000000000)
  · decide +kernel
  · exact familyCons vB141 <| familyNil
  · exact familyCons vB225n68 <| familyNil
  · decide +kernel
  · decide +kernel
def B225n70 : Cell := (5, [0xa0a0000000000000f0f, 0xf0f0000000000000f0f, 0x55550000000000005555, 0xffff, 0x33330000000000003333, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n70 : B225n70.2.Nodup ∧ Closed B225.mask B225.goal B225n70 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B142]) (seen := []) (h := [(0xa0a0000000000000f0f, 0x55550000000000000000, 0xf0f0000000000000f0f), (0x55550000000000000000, 0x55550000000000005555, 0xffff)]) (width := 1) (p := 0x10000)
  · decide +kernel
  · exact familyCons vB142 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n71 : Cell := (4, [0x33110000000000003300, 0xff00000000000000ff, 0x55550000000000005555, 0xffff, 0xf0f0000000000000f0f])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n71 : B225n71.2.Nodup ∧ Closed B225.mask B225.goal B225n71 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := []) (seen := []) (h := [(0x33110000000000003300, 0xaa00000000000000ff, 0x33330000000000003333), (0xaa00000000000000ff, 0x55550000000000000000, 0xff00000000000000ff), (0x55550000000000000000, 0x55550000000000005555, 0xffff)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n72 : Cell := (5, [0xaa00000000000000ff, 0xff00000000000000ff, 0x55550000000000005555, 0xffff, 0x33330000000000003333, 0xf0f0000000000000f0f])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n72 : B225n72.2.Nodup ∧ Closed B225.mask B225.goal B225n72 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B143]) (seen := [B225n71]) (h := [(0xaa00000000000000ff, 0x55550000000000000000, 0xff00000000000000ff), (0x55550000000000000000, 0x55550000000000005555, 0xffff)]) (width := 2) (p := 0x102000000000000000000000000)
  · decide +kernel
  · exact familyCons vB143 <| familyNil
  · exact familyCons vB225n71 <| familyNil
  · decide +kernel
  · decide +kernel
def B225n73 : Cell := (5, [0xf0f, 0xf0f0000000000000f0f, 0x55550000000000000000, 0x55550000000000005555, 0x33330000000000003333, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n73 : B225n73.2.Nodup ∧ Closed B225.mask B225.goal B225n73 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B142, B144]) (seen := []) (h := [(0xf0f, 0xffff, 0xf0f0000000000000f0f), (0x55550000000000000000, 0x55550000000000005555, 0xffff)]) (width := 2) (p := 0x100000000000000000000000000000200000000000000)
  · decide +kernel
  · exact familyCons vB142 <| familyCons vB144 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n74 : Cell := (5, [0xf0f0000000000000000, 0xf0f0000000000000f0f, 0x55550000000000000000, 0x55550000000000005555, 0x33330000000000003333, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n74 : B225n74.2.Nodup ∧ Closed B225.mask B225.goal B225n74 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B142]) (seen := []) (h := [(0xf0f0000000000000000, 0xffff, 0xf0f0000000000000f0f), (0x55550000000000000000, 0x55550000000000005555, 0xffff)]) (width := 1) (p := 0x10000000000000000000100000)
  · decide +kernel
  · exact familyCons vB142 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n75 : Cell := (6, [0x55550000000000000000, 0x55550000000000005555, 0xffff, 0x33330000000000003333, 0xf0f0000000000000f0f, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n75 : B225n75.2.Nodup ∧ Closed B225.mask B225.goal B225n75 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B141, B142, B143, B144]) (seen := [B225n7, B225n26, B225n33, B225n45, B225n58, B225n69, B225n70, B225n72, B225n73, B225n74]) (h := [(0x55550000000000000000, 0x55550000000000005555, 0xffff)]) (width := 4) (p := 0xe0000000d00000000000000000000000000000000000400000007000000000000000000000000400440090001000c000100080002000b000200060003000a00030005000440000004900000)
  · decide +kernel
  · exact familyCons vB141 <| familyCons vB142 <| familyCons vB143 <| familyCons vB144 <| familyNil
  · exact familyCons vB225n7 <| familyCons vB225n26 <| familyCons vB225n33 <| familyCons vB225n45 <| familyCons vB225n58 <| familyCons vB225n69 <| familyCons vB225n70 <| familyCons vB225n72 <| familyCons vB225n73 <| familyCons vB225n74 <| familyNil
  · decide +kernel
  · decide +kernel
def B225n76 : Cell := (6, [0xaaaa, 0x55550000000000005555, 0xffff, 0x33330000000000003333, 0xf0f0000000000000f0f, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n76 : B225n76.2.Nodup ∧ Closed B225.mask B225.goal B225n76 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B141, B142, B143, B144]) (seen := []) (h := [(0xaaaa, 0x55550000000000005555, 0xffff)]) (width := 3) (p := 0x1000001000001000001000001000001001001200200401000401000801000801000c01000c0100120000120000)
  · decide +kernel
  · exact familyCons vB141 <| familyCons vB142 <| familyCons vB143 <| familyCons vB144 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n77 : Cell := (6, [0x5555000000000000ffff, 0x55550000000000005555, 0xffff, 0x33330000000000003333, 0xf0f0000000000000f0f, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n77 : B225n77.2.Nodup ∧ Closed B225.mask B225.goal B225n77 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B141, B142, B143, B144]) (seen := []) (h := [(0x5555000000000000ffff, 0x55550000000000005555, 0xffff)]) (width := 3) (p := 0x1000001000000000000000001000201200401000611240801000a21240c01000e3124000120000120)
  · decide +kernel
  · exact familyCons vB141 <| familyCons vB142 <| familyCons vB143 <| familyCons vB144 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n78 : Cell := (5, [0x54540000000000005454, 0x55550000000000005555, 0x33330000000000003333, 0xf0f0000000000000f0f, 0xff00000000000000ff, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n78 : B225n78.2.Nodup ∧ Closed B225.mask B225.goal B225n78 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B143]) (seen := []) (h := [(0x54540000000000005454, 0x3030000000000000303, 0x55550000000000005555), (0x3030000000000000303, 0x33330000000000003333, 0xf0f0000000000000f0f)]) (width := 1) (p := 0x100000000)
  · decide +kernel
  · exact familyCons vB143 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n79 : Cell := (5, [0x30000000000000003, 0xff00000000000000ff, 0x33330000000000003333, 0xf0f0000000000000f0f, 0x55550000000000005555, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n79 : B225n79.2.Nodup ∧ Closed B225.mask B225.goal B225n79 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B141]) (seen := []) (h := [(0x30000000000000003, 0x3030000000000000303, 0xff00000000000000ff), (0x3030000000000000303, 0x33330000000000003333, 0xf0f0000000000000f0f)]) (width := 1) (p := 0x100000000000000000)
  · decide +kernel
  · exact familyCons vB141 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n80 : Cell := (5, [0xfc00000000000000fc, 0xff00000000000000ff, 0x33330000000000003333, 0xf0f0000000000000f0f, 0x55550000000000005555, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n80 : B225n80.2.Nodup ∧ Closed B225.mask B225.goal B225n80 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B141]) (seen := []) (h := [(0xfc00000000000000fc, 0x3030000000000000303, 0xff00000000000000ff), (0x3030000000000000303, 0x33330000000000003333, 0xf0f0000000000000f0f)]) (width := 1) (p := 0x10000)
  · decide +kernel
  · exact familyCons vB141 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n81 : Cell := (4, [0x55550000000000005454, 0xffff, 0x33330000000000003333, 0xf0f0000000000000f0f, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n81 : B225n81.2.Nodup ∧ Closed B225.mask B225.goal B225n81 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := []) (seen := []) (h := [(0x55550000000000005454, 0x303, 0x55550000000000005555), (0x303, 0x3030000000000000303, 0xffff), (0x3030000000000000303, 0x33330000000000003333, 0xf0f0000000000000f0f)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n82 : Cell := (4, [0xff00000000000000fc, 0xffff, 0x33330000000000003333, 0xf0f0000000000000f0f, 0x55550000000000005555])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n82 : B225n82.2.Nodup ∧ Closed B225.mask B225.goal B225n82 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := []) (seen := []) (h := [(0xff00000000000000fc, 0x303, 0xff00000000000000ff), (0x303, 0x3030000000000000303, 0xffff), (0x3030000000000000303, 0x33330000000000003333, 0xf0f0000000000000f0f)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n83 : Cell := (5, [0x303, 0xffff, 0x33330000000000003333, 0xf0f0000000000000f0f, 0x55550000000000005555, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n83 : B225n83.2.Nodup ∧ Closed B225.mask B225.goal B225n83 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B141, B144]) (seen := [B225n81, B225n82]) (h := [(0x303, 0x3030000000000000303, 0xffff), (0x3030000000000000303, 0x33330000000000003333, 0xf0f0000000000000f0f)]) (width := 3) (p := 0x1004000000002003000000000000000000000000)
  · decide +kernel
  · exact familyCons vB141 <| familyCons vB144 <| familyNil
  · exact familyCons vB225n81 <| familyCons vB225n82 <| familyNil
  · decide +kernel
  · decide +kernel
def B225n84 : Cell := (5, [0x3030000000000000000, 0xffff, 0x33330000000000003333, 0xf0f0000000000000f0f, 0x55550000000000005555, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n84 : B225n84.2.Nodup ∧ Closed B225.mask B225.goal B225n84 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := []) (seen := []) (h := [(0x3030000000000000000, 0x3030000000000000303, 0xffff), (0x3030000000000000303, 0x33330000000000003333, 0xf0f0000000000000f0f)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n85 : Cell := (5, [0xfcfc, 0xffff, 0x33330000000000003333, 0xf0f0000000000000f0f, 0x55550000000000005555, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n85 : B225n85.2.Nodup ∧ Closed B225.mask B225.goal B225n85 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := []) (seen := []) (h := [(0xfcfc, 0x3030000000000000303, 0xffff), (0x3030000000000000303, 0x33330000000000003333, 0xf0f0000000000000f0f)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n86 : Cell := (4, [0x1010000000000005555, 0xffff, 0x33330000000000003333, 0xf0f0000000000000f0f, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n86 : B225n86.2.Nodup ∧ Closed B225.mask B225.goal B225n86 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := []) (seen := []) (h := [(0x1010000000000005555, 0x303000000000000ffff, 0x55550000000000005555), (0x303000000000000ffff, 0x3030000000000000303, 0xffff), (0x3030000000000000303, 0x33330000000000003333, 0xf0f0000000000000f0f)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n87 : Cell := (4, [0x300000000000000ff, 0xffff, 0x33330000000000003333, 0xf0f0000000000000f0f, 0x55550000000000005555])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n87 : B225n87.2.Nodup ∧ Closed B225.mask B225.goal B225n87 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := []) (seen := []) (h := [(0x300000000000000ff, 0x303000000000000ffff, 0xff00000000000000ff), (0x303000000000000ffff, 0x3030000000000000303, 0xffff), (0x3030000000000000303, 0x33330000000000003333, 0xf0f0000000000000f0f)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n88 : Cell := (5, [0x303000000000000ffff, 0xffff, 0x33330000000000003333, 0xf0f0000000000000f0f, 0x55550000000000005555, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n88 : B225n88.2.Nodup ∧ Closed B225.mask B225.goal B225n88 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B141, B142, B143, B144]) (seen := [B225n86, B225n87]) (h := [(0x303000000000000ffff, 0x3030000000000000303, 0xffff), (0x3030000000000000303, 0x33330000000000003333, 0xf0f0000000000000f0f)]) (width := 3) (p := 0x1006000000004005000000000003000000000002000000)
  · decide +kernel
  · exact familyCons vB141 <| familyCons vB142 <| familyCons vB143 <| familyCons vB144 <| familyNil
  · exact familyCons vB225n86 <| familyCons vB225n87 <| familyNil
  · decide +kernel
  · decide +kernel
def B225n89 : Cell := (5, [0x33000000000000003300, 0xff00000000000000ff, 0x3030000000000000303, 0xf0f0000000000000f0f, 0x55550000000000005555, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n89 : B225n89.2.Nodup ∧ Closed B225.mask B225.goal B225n89 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B141]) (seen := []) (h := [(0x33000000000000003300, 0x33330000000000003333, 0xff00000000000000ff), (0x3030000000000000303, 0x33330000000000003333, 0xf0f0000000000000f0f)]) (width := 1) (p := 0x100000)
  · decide +kernel
  · exact familyCons vB141 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n90 : Cell := (5, [0x3333, 0xffff, 0x3030000000000000303, 0xf0f0000000000000f0f, 0x55550000000000005555, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n90 : B225n90.2.Nodup ∧ Closed B225.mask B225.goal B225n90 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B141, B142]) (seen := []) (h := [(0x3333, 0x33330000000000003333, 0xffff), (0x3030000000000000303, 0x33330000000000003333, 0xf0f0000000000000f0f)]) (width := 2) (p := 0x10000000000000000000000020000000000)
  · decide +kernel
  · exact familyCons vB141 <| familyCons vB142 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n91 : Cell := (5, [0xf000000000000000f, 0xff00000000000000ff, 0x3030000000000000303, 0x33330000000000003333, 0x55550000000000005555, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n91 : B225n91.2.Nodup ∧ Closed B225.mask B225.goal B225n91 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B141]) (seen := []) (h := [(0xf000000000000000f, 0xf0f0000000000000f0f, 0xff00000000000000ff), (0x3030000000000000303, 0x33330000000000003333, 0xf0f0000000000000f0f)]) (width := 1) (p := 0x10000000000000000000100000)
  · decide +kernel
  · exact familyCons vB141 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n92 : Cell := (5, [0xf0f, 0xffff, 0x3030000000000000303, 0x33330000000000003333, 0x55550000000000005555, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n92 : B225n92.2.Nodup ∧ Closed B225.mask B225.goal B225n92 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B143, B144]) (seen := []) (h := [(0xf0f, 0xf0f0000000000000f0f, 0xffff), (0x3030000000000000303, 0x33330000000000003333, 0xf0f0000000000000f0f)]) (width := 2) (p := 0x200000000000000010000000000)
  · decide +kernel
  · exact familyCons vB143 <| familyCons vB144 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n93 : Cell := (6, [0x3030000000000000303, 0x33330000000000003333, 0xf0f0000000000000f0f, 0x55550000000000005555, 0xff00000000000000ff, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n93 : B225n93.2.Nodup ∧ Closed B225.mask B225.goal B225n93 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B141, B142, B143, B144]) (seen := [B225n0, B225n15, B225n35, B225n78, B225n79, B225n80, B225n83, B225n84, B225n85, B225n88, B225n89, B225n90, B225n91, B225n92]) (h := [(0x3030000000000000303, 0x33330000000000003333, 0xf0f0000000000000f0f)]) (width := 5) (p := 0x800000000480000000008000000004400008000000001c00000000000000c00000000400000c000000003c00000000000000c00000000180000840000600080003800034000300002c00004000280000400024000100002000010000140000860000000084000000)
  · decide +kernel
  · exact familyCons vB141 <| familyCons vB142 <| familyCons vB143 <| familyCons vB144 <| familyNil
  · exact familyCons vB225n0 <| familyCons vB225n15 <| familyCons vB225n35 <| familyCons vB225n78 <| familyCons vB225n79 <| familyCons vB225n80 <| familyCons vB225n83 <| familyCons vB225n84 <| familyCons vB225n85 <| familyCons vB225n88 <| familyCons vB225n89 <| familyCons vB225n90 <| familyCons vB225n91 <| familyCons vB225n92 <| familyNil
  · decide +kernel
  · decide +kernel
def B225n94 : Cell := (6, [0x30300000000000003030, 0x33330000000000003333, 0xf0f0000000000000f0f, 0x55550000000000005555, 0xff00000000000000ff, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n94 : B225n94.2.Nodup ∧ Closed B225.mask B225.goal B225n94 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B141, B142]) (seen := []) (h := [(0x30300000000000003030, 0x33330000000000003333, 0xf0f0000000000000f0f)]) (width := 2) (p := 0x200020002000202000200000000000000000000000000008282020202020192a10202020202028002800)
  · decide +kernel
  · exact familyCons vB141 <| familyCons vB142 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n95 : Cell := (6, [0xc0c0000000000000c0c, 0x33330000000000003333, 0xf0f0000000000000f0f, 0x55550000000000005555, 0xff00000000000000ff, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n95 : B225n95.2.Nodup ∧ Closed B225.mask B225.goal B225n95 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B141, B142, B143]) (seen := []) (h := [(0xc0c0000000000000c0c, 0x33330000000000003333, 0xf0f0000000000000f0f)]) (width := 2) (p := 0x300030300030000030003020280c30303030103010303f3f30302c002800)
  · decide +kernel
  · exact familyCons vB141 <| familyCons vB142 <| familyCons vB143 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n96 : Cell := (6, [0x3f3f0000000000003f3f, 0x33330000000000003333, 0xf0f0000000000000f0f, 0x55550000000000005555, 0xff00000000000000ff, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n96 : B225n96.2.Nodup ∧ Closed B225.mask B225.goal B225n96 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B141, B142]) (seen := []) (h := [(0x3f3f0000000000003f3f, 0x33330000000000003333, 0xf0f0000000000000f0f)]) (width := 2) (p := 0x20082820202020102010202020202000280028)
  · decide +kernel
  · exact familyCons vB141 <| familyCons vB142 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n97 : Cell := (5, [0x55440000000000005544, 0x55550000000000005555, 0x33330000000000003333, 0xff00000000000000ff, 0xf0f0000000000000f0f, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n97 : B225n97.2.Nodup ∧ Closed B225.mask B225.goal B225n97 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B6, B141, B142]) (seen := []) (h := [(0x55440000000000005544, 0x330000000000000033, 0x55550000000000005555), (0x330000000000000033, 0x33330000000000003333, 0xff00000000000000ff)]) (width := 2) (p := 0x200000000000000000000000000000000000000000000000301000000000000000000000000)
  · decide +kernel
  · exact familyCons vB6 <| familyCons vB141 <| familyCons vB142 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n98 : Cell := (5, [0xf0c0000000000000f0c, 0xf0f0000000000000f0f, 0x33330000000000003333, 0xff00000000000000ff, 0x55550000000000005555, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n98 : B225n98.2.Nodup ∧ Closed B225.mask B225.goal B225n98 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B6, B141, B144]) (seen := []) (h := [(0xf0c0000000000000f0c, 0x330000000000000033, 0xf0f0000000000000f0f), (0x330000000000000033, 0x33330000000000003333, 0xff00000000000000ff)]) (width := 2) (p := 0x200000000000000000000000000000000000000000000000301000000000000000000000000)
  · decide +kernel
  · exact familyCons vB6 <| familyCons vB141 <| familyCons vB144 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n99 : Cell := (5, [0x33, 0xffff, 0x33330000000000003333, 0xff00000000000000ff, 0x55550000000000005555, 0xf0f0000000000000f0f])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n99 : B225n99.2.Nodup ∧ Closed B225.mask B225.goal B225n99 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B6]) (seen := []) (h := [(0x33, 0x330000000000000033, 0xffff), (0x330000000000000033, 0x33330000000000003333, 0xff00000000000000ff)]) (width := 1) (p := 0x101000)
  · decide +kernel
  · exact familyCons vB6 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n100 : Cell := (5, [0x330000000000000000, 0xffff, 0x33330000000000003333, 0xff00000000000000ff, 0x55550000000000005555, 0xf0f0000000000000f0f])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n100 : B225n100.2.Nodup ∧ Closed B225.mask B225.goal B225n100 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B141]) (seen := []) (h := [(0x330000000000000000, 0x330000000000000033, 0xffff), (0x330000000000000033, 0x33330000000000003333, 0xff00000000000000ff)]) (width := 1) (p := 0x1000000000000000000000000000000000)
  · decide +kernel
  · exact familyCons vB141 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n101 : Cell := (5, [0xffcc, 0xffff, 0x33330000000000003333, 0xff00000000000000ff, 0x55550000000000005555, 0xf0f0000000000000f0f])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n101 : B225n101.2.Nodup ∧ Closed B225.mask B225.goal B225n101 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := []) (seen := []) (h := [(0xffcc, 0x330000000000000033, 0xffff), (0x330000000000000033, 0x33330000000000003333, 0xff00000000000000ff)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n102 : Cell := (5, [0x33000000000000ffff, 0xffff, 0x33330000000000003333, 0xff00000000000000ff, 0x55550000000000005555, 0xf0f0000000000000f0f])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n102 : B225n102.2.Nodup ∧ Closed B225.mask B225.goal B225n102 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B6, B141, B142, B143, B144]) (seen := []) (h := [(0x33000000000000ffff, 0x330000000000000033, 0xffff), (0x330000000000000033, 0x33330000000000003333, 0xff00000000000000ff)]) (width := 3) (p := 0x2000000000000000000000000000000000000000000000000000000000000000003001000000005001000000000004000000000002000000)
  · decide +kernel
  · exact familyCons vB6 <| familyCons vB141 <| familyCons vB142 <| familyCons vB143 <| familyCons vB144 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n103 : Cell := (5, [0x3333, 0xffff, 0x330000000000000033, 0xff00000000000000ff, 0x55550000000000005555, 0xf0f0000000000000f0f])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n103 : B225n103.2.Nodup ∧ Closed B225.mask B225.goal B225n103 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B6, B141]) (seen := []) (h := [(0x3333, 0x33330000000000003333, 0xffff), (0x330000000000000033, 0x33330000000000003333, 0xff00000000000000ff)]) (width := 2) (p := 0x100000000000000000000000002000000020000000000)
  · decide +kernel
  · exact familyCons vB6 <| familyCons vB141 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n104 : Cell := (5, [0xff, 0xffff, 0x330000000000000033, 0x33330000000000003333, 0x55550000000000005555, 0xf0f0000000000000f0f])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n104 : B225n104.2.Nodup ∧ Closed B225.mask B225.goal B225n104 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B6, B143]) (seen := []) (h := [(0xff, 0xff00000000000000ff, 0xffff), (0x330000000000000033, 0x33330000000000003333, 0xff00000000000000ff)]) (width := 2) (p := 0x100000000000000000000000002000000020000000000)
  · decide +kernel
  · exact familyCons vB6 <| familyCons vB143 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n105 : Cell := (6, [0x330000000000000033, 0x33330000000000003333, 0xff00000000000000ff, 0x55550000000000005555, 0xf0f0000000000000f0f, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n105 : B225n105.2.Nodup ∧ Closed B225.mask B225.goal B225n105 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B141, B142, B143, B144]) (seen := [B225n2, B225n79, B225n97, B225n98, B225n99, B225n100, B225n101, B225n102, B225n103, B225n104]) (h := [(0x330000000000000033, 0x33330000000000003333, 0xff00000000000000ff)]) (width := 4) (p := 0x10000000e00000000000000000000000000000000000000030000000d00000000000000000000000000000000000111003001000c000b000a000900020008000200060004000700040005000130000001100000)
  · decide +kernel
  · exact familyCons vB141 <| familyCons vB142 <| familyCons vB143 <| familyCons vB144 <| familyNil
  · exact familyCons vB225n2 <| familyCons vB225n79 <| familyCons vB225n97 <| familyCons vB225n98 <| familyCons vB225n99 <| familyCons vB225n100 <| familyCons vB225n101 <| familyCons vB225n102 <| familyCons vB225n103 <| familyCons vB225n104 <| familyNil
  · decide +kernel
  · decide +kernel
def B225n106 : Cell := (5, [0x33330000000000000000, 0xffff, 0x33000000000000003300, 0xff00000000000000ff, 0x55550000000000005555, 0xf0f0000000000000f0f])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n106 : B225n106.2.Nodup ∧ Closed B225.mask B225.goal B225n106 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B141]) (seen := []) (h := [(0x33330000000000000000, 0x33330000000000003333, 0xffff), (0x33000000000000003300, 0x33330000000000003333, 0xff00000000000000ff)]) (width := 1) (p := 0x10000000000000000100000)
  · decide +kernel
  · exact familyCons vB141 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n107 : Cell := (6, [0x33000000000000003300, 0x33330000000000003333, 0xff00000000000000ff, 0x55550000000000005555, 0xf0f0000000000000f0f, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n107 : B225n107.2.Nodup ∧ Closed B225.mask B225.goal B225n107 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B141, B143]) (seen := [B225n16, B225n89, B225n106]) (h := [(0x33000000000000003300, 0x33330000000000003333, 0xff00000000000000ff)]) (width := 3) (p := 0x400000400000000000000000000000000800001400000000800001000000800000c0008048040040040040040040040040040040040040040048000048000)
  · decide +kernel
  · exact familyCons vB141 <| familyCons vB143 <| familyNil
  · exact familyCons vB225n16 <| familyCons vB225n89 <| familyCons vB225n106 <| familyNil
  · decide +kernel
  · decide +kernel
def B225n108 : Cell := (5, [0xf000000000000000f, 0xf0f0000000000000f0f, 0xcc00000000000000cc, 0x33330000000000003333, 0x55550000000000005555, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n108 : B225n108.2.Nodup ∧ Closed B225.mask B225.goal B225n108 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B142]) (seen := []) (h := [(0xf000000000000000f, 0xff00000000000000ff, 0xf0f0000000000000f0f), (0xcc00000000000000cc, 0x33330000000000003333, 0xff00000000000000ff)]) (width := 1) (p := 0x100000)
  · decide +kernel
  · exact familyCons vB142 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n109 : Cell := (5, [0xff0000000000000000, 0xffff, 0xcc00000000000000cc, 0x33330000000000003333, 0x55550000000000005555, 0xf0f0000000000000f0f])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n109 : B225n109.2.Nodup ∧ Closed B225.mask B225.goal B225n109 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B143]) (seen := []) (h := [(0xff0000000000000000, 0xff00000000000000ff, 0xffff), (0xcc00000000000000cc, 0x33330000000000003333, 0xff00000000000000ff)]) (width := 1) (p := 0x10000000000000000100000)
  · decide +kernel
  · exact familyCons vB143 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n110 : Cell := (6, [0xcc00000000000000cc, 0x33330000000000003333, 0xff00000000000000ff, 0x55550000000000005555, 0xf0f0000000000000f0f, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n110 : B225n110.2.Nodup ∧ Closed B225.mask B225.goal B225n110 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B141, B142, B143]) (seen := [B225n51, B225n108, B225n109]) (h := [(0xcc00000000000000cc, 0x33330000000000003333, 0xff00000000000000ff)]) (width := 3) (p := 0x400001800000000400001400000400001000000c00000c00000000000000000000000000400480180c00c00c00c00800c00800c00c00c00c00c0058000048000)
  · decide +kernel
  · exact familyCons vB141 <| familyCons vB142 <| familyCons vB143 <| familyNil
  · exact familyCons vB225n51 <| familyCons vB225n108 <| familyCons vB225n109 <| familyNil
  · decide +kernel
  · decide +kernel
def B225n111 : Cell := (6, [0x33ff00000000000033ff, 0x33330000000000003333, 0xff00000000000000ff, 0x55550000000000005555, 0xf0f0000000000000f0f, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n111 : B225n111.2.Nodup ∧ Closed B225.mask B225.goal B225n111 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B141, B143]) (seen := []) (h := [(0x33ff00000000000033ff, 0x33330000000000003333, 0xff00000000000000ff)]) (width := 2) (p := 0x10001000001000100010001020002000002000200020002010041510101515101015151010151500140014)
  · decide +kernel
  · exact familyCons vB141 <| familyCons vB143 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n112 : Cell := (5, [0x33330000000000000000, 0x3333, 0xffff, 0x55550000000000005555, 0xf0f0000000000000f0f, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n112 : B225n112.2.Nodup ∧ Closed B225.mask B225.goal B225n112 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B6, B141]) (seen := []) (h := [(0x33330000000000000000, 0x3333, 0x33330000000000003333), (0x3333, 0x33330000000000003333, 0xffff)]) (width := 2) (p := 0x10000000000000000000000000000000000000000000000000000000200)
  · decide +kernel
  · exact familyCons vB6 <| familyCons vB141 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n113 : Cell := (5, [0x55550000000000004444, 0x55550000000000005555, 0x33330000000000003333, 0xffff, 0xf0f0000000000000f0f, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n113 : B225n113.2.Nodup ∧ Closed B225.mask B225.goal B225n113 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := []) (seen := []) (h := [(0x55550000000000004444, 0x3333, 0x55550000000000005555), (0x3333, 0x33330000000000003333, 0xffff)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n114 : Cell := (5, [0xf0f0000000000000c0c, 0xf0f0000000000000f0f, 0x33330000000000003333, 0xffff, 0x55550000000000005555, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n114 : B225n114.2.Nodup ∧ Closed B225.mask B225.goal B225n114 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := []) (seen := []) (h := [(0xf0f0000000000000c0c, 0x3333, 0xf0f0000000000000f0f), (0x3333, 0x33330000000000003333, 0xffff)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n115 : Cell := (5, [0xff00000000000000cc, 0x33330000000000003333, 0xffff, 0x55550000000000005555, 0xf0f0000000000000f0f])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n115 : B225n115.2.Nodup ∧ Closed B225.mask B225.goal B225n115 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := []) (seen := []) (h := [(0xff00000000000000cc, 0x3333, 0xff00000000000000ff), (0x3333, 0x33330000000000003333, 0xffff)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n116 : Cell := (5, [0xff00000000000000cc, 0x3333, 0x33330000000000003333, 0xffff, 0x55550000000000005555, 0xf0f0000000000000f0f])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n116 : B225n116.2.Nodup ∧ Closed B225.mask B225.goal B225n116 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B141]) (seen := []) (h := [(0xff00000000000000cc, 0x3333, 0xff00000000000000ff), (0x3333, 0x33330000000000003333, 0xffff)]) (width := 1) (p := 0x10)
  · decide +kernel
  · exact familyCons vB141 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n117 : Cell := (5, [0xff00000000000000cc, 0xff00000000000000ff, 0x33330000000000003333, 0xffff, 0x55550000000000005555, 0xf0f0000000000000f0f])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n117 : B225n117.2.Nodup ∧ Closed B225.mask B225.goal B225n117 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := []) (seen := []) (h := [(0xff00000000000000cc, 0x3333, 0xff00000000000000ff), (0x3333, 0x33330000000000003333, 0xffff)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n118 : Cell := (5, [0xff00000000000033ff, 0x3333, 0x33330000000000003333, 0xffff, 0x55550000000000005555, 0xf0f0000000000000f0f])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n118 : B225n118.2.Nodup ∧ Closed B225.mask B225.goal B225n118 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B6]) (seen := []) (h := [(0xff00000000000033ff, 0x3333, 0xff00000000000000ff), (0x3333, 0x33330000000000003333, 0xffff)]) (width := 1) (p := 0x10000000000000000001)
  · decide +kernel
  · exact familyCons vB6 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n119 : Cell := (5, [0xff, 0xff00000000000000ff, 0x3333, 0x33330000000000003333, 0x55550000000000005555, 0xf0f0000000000000f0f])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n119 : B225n119.2.Nodup ∧ Closed B225.mask B225.goal B225n119 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B6, B141]) (seen := []) (h := [(0xff, 0xffff, 0xff00000000000000ff), (0x3333, 0x33330000000000003333, 0xffff)]) (width := 2) (p := 0x100000000000000000000000000000000020000000000)
  · decide +kernel
  · exact familyCons vB6 <| familyCons vB141 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n120 : Cell := (5, [0xff0000000000000000, 0xff00000000000000ff, 0x3333, 0x33330000000000003333, 0x55550000000000005555, 0xf0f0000000000000f0f])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n120 : B225n120.2.Nodup ∧ Closed B225.mask B225.goal B225n120 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B141, B143]) (seen := []) (h := [(0xff0000000000000000, 0xffff, 0xff00000000000000ff), (0x3333, 0x33330000000000003333, 0xffff)]) (width := 2) (p := 0x2000100000000000000000000000000000000000000)
  · decide +kernel
  · exact familyCons vB141 <| familyCons vB143 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n121 : Cell := (6, [0x3333, 0x33330000000000003333, 0xffff, 0x55550000000000005555, 0xf0f0000000000000f0f, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n121 : B225n121.2.Nodup ∧ Closed B225.mask B225.goal B225n121 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B141, B142, B143, B144]) (seen := [B225n6, B225n17, B225n83, B225n90, B225n99, B225n103, B225n112, B225n113, B225n114, B225n115, B225n116, B225n117, B225n118, B225n119, B225n120]) (h := [(0x3333, 0x33330000000000003333, 0xffff)]) (width := 5) (p := 0x4c00000000480000000000000000000000000000000000000000000000000c0000000028000000000c0000000020000000000c00000000180000c600006002c0000621041ee004000240000800034000080001c000100003000010000140000c600000000d6000000)
  · decide +kernel
  · exact familyCons vB141 <| familyCons vB142 <| familyCons vB143 <| familyCons vB144 <| familyNil
  · exact familyCons vB225n6 <| familyCons vB225n17 <| familyCons vB225n83 <| familyCons vB225n90 <| familyCons vB225n99 <| familyCons vB225n103 <| familyCons vB225n112 <| familyCons vB225n113 <| familyCons vB225n114 <| familyCons vB225n115 <| familyCons vB225n116 <| familyCons vB225n117 <| familyCons vB225n118 <| familyCons vB225n119 <| familyCons vB225n120 <| familyNil
  · decide +kernel
  · decide +kernel
def B225n122 : Cell := (4, [0xb0b0000000000000a0a, 0x55550000000000005555, 0x33330000000000003333, 0xffff, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n122 : B225n122.2.Nodup ∧ Closed B225.mask B225.goal B225n122 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := []) (seen := []) (h := [(0xb0b0000000000000a0a, 0x44440000000000005555, 0xf0f0000000000000f0f), (0x44440000000000005555, 0x33330000000000000000, 0x55550000000000005555), (0x33330000000000000000, 0x33330000000000003333, 0xffff)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n123 : Cell := (5, [0x44440000000000005555, 0x55550000000000005555, 0x33330000000000003333, 0xffff, 0xf0f0000000000000f0f, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n123 : B225n123.2.Nodup ∧ Closed B225.mask B225.goal B225n123 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B142]) (seen := [B225n122]) (h := [(0x44440000000000005555, 0x33330000000000000000, 0x55550000000000005555), (0x33330000000000000000, 0x33330000000000003333, 0xffff)]) (width := 2) (p := 0x102000000000000000000000000)
  · decide +kernel
  · exact familyCons vB142 <| familyNil
  · exact familyCons vB225n122 <| familyNil
  · decide +kernel
  · decide +kernel
def B225n124 : Cell := (4, [0x51510000000000005050, 0xf0f0000000000000f0f, 0x33330000000000003333, 0xffff, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n124 : B225n124.2.Nodup ∧ Closed B225.mask B225.goal B225n124 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := []) (seen := []) (h := [(0x51510000000000005050, 0xc0c0000000000000f0f, 0x55550000000000005555), (0xc0c0000000000000f0f, 0x33330000000000000000, 0xf0f0000000000000f0f), (0x33330000000000000000, 0x33330000000000003333, 0xffff)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n125 : Cell := (5, [0xc0c0000000000000f0f, 0xf0f0000000000000f0f, 0x33330000000000003333, 0xffff, 0x55550000000000005555, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n125 : B225n125.2.Nodup ∧ Closed B225.mask B225.goal B225n125 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B144]) (seen := [B225n124]) (h := [(0xc0c0000000000000f0f, 0x33330000000000000000, 0xf0f0000000000000f0f), (0x33330000000000000000, 0x33330000000000003333, 0xffff)]) (width := 2) (p := 0x102000000000000000000000000)
  · decide +kernel
  · exact familyCons vB144 <| familyNil
  · exact familyCons vB225n124 <| familyNil
  · decide +kernel
  · decide +kernel
def B225n126 : Cell := (5, [0xcc00000000000000ff, 0xff00000000000000ff, 0x33330000000000003333, 0xffff, 0x55550000000000005555, 0xf0f0000000000000f0f])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n126 : B225n126.2.Nodup ∧ Closed B225.mask B225.goal B225n126 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B141]) (seen := []) (h := [(0xcc00000000000000ff, 0x33330000000000000000, 0xff00000000000000ff), (0x33330000000000000000, 0x33330000000000003333, 0xffff)]) (width := 1) (p := 0x10000)
  · decide +kernel
  · exact familyCons vB141 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n127 : Cell := (5, [0xff, 0xff00000000000000ff, 0x33330000000000000000, 0x33330000000000003333, 0x55550000000000005555, 0xf0f0000000000000f0f])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n127 : B225n127.2.Nodup ∧ Closed B225.mask B225.goal B225n127 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B141, B143]) (seen := []) (h := [(0xff, 0xffff, 0xff00000000000000ff), (0x33330000000000000000, 0x33330000000000003333, 0xffff)]) (width := 2) (p := 0x100000000000000000000000000000200000000000000)
  · decide +kernel
  · exact familyCons vB141 <| familyCons vB143 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n128 : Cell := (5, [0xff0000000000000000, 0xff00000000000000ff, 0x33330000000000000000, 0x33330000000000003333, 0x55550000000000005555, 0xf0f0000000000000f0f])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n128 : B225n128.2.Nodup ∧ Closed B225.mask B225.goal B225n128 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B141]) (seen := []) (h := [(0xff0000000000000000, 0xffff, 0xff00000000000000ff), (0x33330000000000000000, 0x33330000000000003333, 0xffff)]) (width := 1) (p := 0x10000000000000000000100000)
  · decide +kernel
  · exact familyCons vB141 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n129 : Cell := (6, [0x33330000000000000000, 0x33330000000000003333, 0xffff, 0x55550000000000005555, 0xf0f0000000000000f0f, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n129 : B225n129.2.Nodup ∧ Closed B225.mask B225.goal B225n129 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B141, B142, B143, B144]) (seen := [B225n7, B225n84, B225n100, B225n106, B225n112, B225n123, B225n125, B225n126, B225n127, B225n128]) (h := [(0x33330000000000000000, 0x33330000000000003333, 0xffff)]) (width := 4) (p := 0xe0000000d000000000000000000000000000000000003000000080000000000000000000000000000000000000000300330090001000c000100070002000b000200060004000a00040005000330000003900000)
  · decide +kernel
  · exact familyCons vB141 <| familyCons vB142 <| familyCons vB143 <| familyCons vB144 <| familyNil
  · exact familyCons vB225n7 <| familyCons vB225n84 <| familyCons vB225n100 <| familyCons vB225n106 <| familyCons vB225n112 <| familyCons vB225n123 <| familyCons vB225n125 <| familyCons vB225n126 <| familyCons vB225n127 <| familyCons vB225n128 <| familyNil
  · decide +kernel
  · decide +kernel
def B225n130 : Cell := (6, [0xcccc, 0x33330000000000003333, 0xffff, 0x55550000000000005555, 0xf0f0000000000000f0f, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n130 : B225n130.2.Nodup ∧ Closed B225.mask B225.goal B225n130 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B141, B142, B143]) (seen := []) (h := [(0xcccc, 0x33330000000000003333, 0xffff)]) (width := 2) (p := 0x3000300030003000300030303c0c1030103020302030303030303c003c00)
  · decide +kernel
  · exact familyCons vB141 <| familyCons vB142 <| familyCons vB143 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n131 : Cell := (6, [0x3333000000000000ffff, 0x33330000000000003333, 0xffff, 0x55550000000000005555, 0xf0f0000000000000f0f, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n131 : B225n131.2.Nodup ∧ Closed B225.mask B225.goal B225n131 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B141, B142, B143]) (seen := []) (h := [(0x3333000000000000ffff, 0x33330000000000003333, 0xffff)]) (width := 2) (p := 0x300030000000000000000000300c3c10301d3f20302e3f30303f3f003c003c)
  · decide +kernel
  · exact familyCons vB141 <| familyCons vB142 <| familyCons vB143 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n132 : Cell := (5, [0x55500000000000005550, 0x55550000000000005555, 0xf0f0000000000000f0f, 0xff00000000000000ff, 0x33330000000000003333, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n132 : B225n132.2.Nodup ∧ Closed B225.mask B225.goal B225n132 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B141]) (seen := []) (h := [(0x55500000000000005550, 0xf000000000000000f, 0x55550000000000005555), (0xf000000000000000f, 0xf0f0000000000000f0f, 0xff00000000000000ff)]) (width := 1) (p := 0x10000)
  · decide +kernel
  · exact familyCons vB141 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n133 : Cell := (5, [0x33300000000000003330, 0x33330000000000003333, 0xf0f0000000000000f0f, 0xff00000000000000ff, 0x55550000000000005555, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n133 : B225n133.2.Nodup ∧ Closed B225.mask B225.goal B225n133 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B142]) (seen := []) (h := [(0x33300000000000003330, 0xf000000000000000f, 0x33330000000000003333), (0xf000000000000000f, 0xf0f0000000000000f0f, 0xff00000000000000ff)]) (width := 1) (p := 0x100000000)
  · decide +kernel
  · exact familyCons vB142 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n134 : Cell := (4, [0x55550000000000005550, 0xffff, 0xf0f0000000000000f0f, 0xff00000000000000ff, 0x33330000000000003333])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n134 : B225n134.2.Nodup ∧ Closed B225.mask B225.goal B225n134 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := []) (seen := []) (h := [(0x55550000000000005550, 0xf, 0x55550000000000005555), (0xf, 0xf000000000000000f, 0xffff), (0xf000000000000000f, 0xf0f0000000000000f0f, 0xff00000000000000ff)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n135 : Cell := (4, [0x33330000000000003330, 0xffff, 0xf0f0000000000000f0f, 0xff00000000000000ff, 0x55550000000000005555])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n135 : B225n135.2.Nodup ∧ Closed B225.mask B225.goal B225n135 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := []) (seen := []) (h := [(0x33330000000000003330, 0xf, 0x33330000000000003333), (0xf, 0xf000000000000000f, 0xffff), (0xf000000000000000f, 0xf0f0000000000000f0f, 0xff00000000000000ff)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n136 : Cell := (5, [0xf, 0xffff, 0xf0f0000000000000f0f, 0xff00000000000000ff, 0x55550000000000005555, 0x33330000000000003333])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n136 : B225n136.2.Nodup ∧ Closed B225.mask B225.goal B225n136 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B143, B144]) (seen := [B225n134, B225n135]) (h := [(0xf, 0xf000000000000000f, 0xffff), (0xf000000000000000f, 0xf0f0000000000000f0f, 0xff00000000000000ff)]) (width := 3) (p := 0x1004000000002003000000000000000000000000)
  · decide +kernel
  · exact familyCons vB143 <| familyCons vB144 <| familyNil
  · exact familyCons vB225n134 <| familyCons vB225n135 <| familyNil
  · decide +kernel
  · decide +kernel
def B225n137 : Cell := (5, [0xf0000000000000000, 0xffff, 0xf0f0000000000000f0f, 0xff00000000000000ff, 0x55550000000000005555, 0x33330000000000003333])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n137 : B225n137.2.Nodup ∧ Closed B225.mask B225.goal B225n137 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := []) (seen := []) (h := [(0xf0000000000000000, 0xf000000000000000f, 0xffff), (0xf000000000000000f, 0xf0f0000000000000f0f, 0xff00000000000000ff)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n138 : Cell := (5, [0xfff0, 0xffff, 0xf0f0000000000000f0f, 0xff00000000000000ff, 0x55550000000000005555, 0x33330000000000003333])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n138 : B225n138.2.Nodup ∧ Closed B225.mask B225.goal B225n138 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := []) (seen := []) (h := [(0xfff0, 0xf000000000000000f, 0xffff), (0xf000000000000000f, 0xf0f0000000000000f0f, 0xff00000000000000ff)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n139 : Cell := (4, [0x50000000000005555, 0xffff, 0xf0f0000000000000f0f, 0xff00000000000000ff, 0x33330000000000003333])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n139 : B225n139.2.Nodup ∧ Closed B225.mask B225.goal B225n139 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := []) (seen := []) (h := [(0x50000000000005555, 0xf000000000000ffff, 0x55550000000000005555), (0xf000000000000ffff, 0xf000000000000000f, 0xffff), (0xf000000000000000f, 0xf0f0000000000000f0f, 0xff00000000000000ff)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n140 : Cell := (4, [0x30000000000003333, 0xffff, 0xf0f0000000000000f0f, 0xff00000000000000ff, 0x55550000000000005555])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n140 : B225n140.2.Nodup ∧ Closed B225.mask B225.goal B225n140 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := []) (seen := []) (h := [(0x30000000000003333, 0xf000000000000ffff, 0x33330000000000003333), (0xf000000000000ffff, 0xf000000000000000f, 0xffff), (0xf000000000000000f, 0xf0f0000000000000f0f, 0xff00000000000000ff)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n141 : Cell := (5, [0xf000000000000ffff, 0xffff, 0xf0f0000000000000f0f, 0xff00000000000000ff, 0x55550000000000005555, 0x33330000000000003333])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n141 : B225n141.2.Nodup ∧ Closed B225.mask B225.goal B225n141 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B141, B142, B143, B144]) (seen := [B225n139, B225n140]) (h := [(0xf000000000000ffff, 0xf000000000000000f, 0xffff), (0xf000000000000000f, 0xf0f0000000000000f0f, 0xff00000000000000ff)]) (width := 3) (p := 0x3006000000004005000000000002000000000001000000)
  · decide +kernel
  · exact familyCons vB141 <| familyCons vB142 <| familyCons vB143 <| familyCons vB144 <| familyNil
  · exact familyCons vB225n139 <| familyCons vB225n140 <| familyNil
  · decide +kernel
  · decide +kernel
def B225n142 : Cell := (5, [0xf0f, 0xffff, 0xf000000000000000f, 0xff00000000000000ff, 0x55550000000000005555, 0x33330000000000003333])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n142 : B225n142.2.Nodup ∧ Closed B225.mask B225.goal B225n142 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B141, B144]) (seen := []) (h := [(0xf0f, 0xf0f0000000000000f0f, 0xffff), (0xf000000000000000f, 0xf0f0000000000000f0f, 0xff00000000000000ff)]) (width := 2) (p := 0x200000000000000010000000000)
  · decide +kernel
  · exact familyCons vB141 <| familyCons vB144 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n143 : Cell := (5, [0xff, 0xffff, 0xf000000000000000f, 0xf0f0000000000000f0f, 0x55550000000000005555, 0x33330000000000003333])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n143 : B225n143.2.Nodup ∧ Closed B225.mask B225.goal B225n143 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B142, B143]) (seen := []) (h := [(0xff, 0xff00000000000000ff, 0xffff), (0xf000000000000000f, 0xf0f0000000000000f0f, 0xff00000000000000ff)]) (width := 2) (p := 0x20000000000000000000000010000000000)
  · decide +kernel
  · exact familyCons vB142 <| familyCons vB143 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n144 : Cell := (6, [0xf000000000000000f, 0xf0f0000000000000f0f, 0xff00000000000000ff, 0x55550000000000005555, 0x33330000000000003333, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n144 : B225n144.2.Nodup ∧ Closed B225.mask B225.goal B225n144 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B141, B142, B143, B144]) (seen := [B225n23, B225n36, B225n52, B225n79, B225n91, B225n108, B225n132, B225n133, B225n136, B225n137, B225n138, B225n141, B225n142, B225n143]) (h := [(0xf000000000000000f, 0xf0f0000000000000f0f, 0xff00000000000000ff)]) (width := 5) (p := 0x40000000048000040000000028000000000000004000000001c000000000800000000440000000008000000002400008000000001800000000042000040004000400003c00038000340000c000300000c00020000100002c00010000140000440000000042000000)
  · decide +kernel
  · exact familyCons vB141 <| familyCons vB142 <| familyCons vB143 <| familyCons vB144 <| familyNil
  · exact familyCons vB225n23 <| familyCons vB225n36 <| familyCons vB225n52 <| familyCons vB225n79 <| familyCons vB225n91 <| familyCons vB225n108 <| familyCons vB225n132 <| familyCons vB225n133 <| familyCons vB225n136 <| familyCons vB225n137 <| familyCons vB225n138 <| familyCons vB225n141 <| familyCons vB225n142 <| familyCons vB225n143 <| familyNil
  · decide +kernel
  · decide +kernel
def B225n145 : Cell := (6, [0xf000000000000000f00, 0xf0f0000000000000f0f, 0xff00000000000000ff, 0x55550000000000005555, 0x33330000000000003333, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n145 : B225n145.2.Nodup ∧ Closed B225.mask B225.goal B225n145 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B141]) (seen := []) (h := [(0xf000000000000000f00, 0xf0f0000000000000f0f, 0xff00000000000000ff)]) (width := 1) (p := 0x404404004040000000000002644444444477446060)
  · decide +kernel
  · exact familyCons vB141 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n146 : Cell := (6, [0xf000000000000000f0, 0xf0f0000000000000f0f, 0xff00000000000000ff, 0x55550000000000005555, 0x33330000000000003333, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n146 : B225n146.2.Nodup ∧ Closed B225.mask B225.goal B225n146 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B141, B142]) (seen := []) (h := [(0xf000000000000000f0, 0xf0f0000000000000f0f, 0xff00000000000000ff)]) (width := 2) (p := 0x2000200020002020002000101408202020202a2a20202020202018001400)
  · decide +kernel
  · exact familyCons vB141 <| familyCons vB142 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n147 : Cell := (6, [0xfff0000000000000fff, 0xf0f0000000000000f0f, 0xff00000000000000ff, 0x55550000000000005555, 0x33330000000000003333, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n147 : B225n147.2.Nodup ∧ Closed B225.mask B225.goal B225n147 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B141]) (seen := []) (h := [(0xfff0000000000000fff, 0xf0f0000000000000f0f, 0xff00000000000000ff)]) (width := 1) (p := 0x4264444444444440606)
  · decide +kernel
  · exact familyCons vB141 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n148 : Cell := (5, [0xf0f0000000000000000, 0xf0f, 0xffff, 0x55550000000000005555, 0x33330000000000003333, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n148 : B225n148.2.Nodup ∧ Closed B225.mask B225.goal B225n148 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B7, B141]) (seen := []) (h := [(0xf0f0000000000000000, 0xf0f, 0xf0f0000000000000f0f), (0xf0f, 0xf0f0000000000000f0f, 0xffff)]) (width := 2) (p := 0x1000000000000000000000000000000000000000200)
  · decide +kernel
  · exact familyCons vB7 <| familyCons vB141 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n149 : Cell := (5, [0x55550000000000005050, 0xf0f0000000000000f0f, 0xffff, 0x33330000000000003333, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n149 : B225n149.2.Nodup ∧ Closed B225.mask B225.goal B225n149 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := []) (seen := []) (h := [(0x55550000000000005050, 0xf0f, 0x55550000000000005555), (0xf0f, 0xf0f0000000000000f0f, 0xffff)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n150 : Cell := (5, [0x55550000000000005050, 0xf0f, 0xf0f0000000000000f0f, 0xffff, 0x33330000000000003333, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n150 : B225n150.2.Nodup ∧ Closed B225.mask B225.goal B225n150 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B144]) (seen := []) (h := [(0x55550000000000005050, 0xf0f, 0x55550000000000005555), (0xf0f, 0xf0f0000000000000f0f, 0xffff)]) (width := 1) (p := 0x10)
  · decide +kernel
  · exact familyCons vB144 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n151 : Cell := (5, [0x55550000000000005050, 0x55550000000000005555, 0xf0f0000000000000f0f, 0xffff, 0x33330000000000003333, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n151 : B225n151.2.Nodup ∧ Closed B225.mask B225.goal B225n151 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := []) (seen := []) (h := [(0x55550000000000005050, 0xf0f, 0x55550000000000005555), (0xf0f, 0xf0f0000000000000f0f, 0xffff)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n152 : Cell := (5, [0x55550000000000005f5f, 0xf0f, 0xf0f0000000000000f0f, 0xffff, 0x33330000000000003333, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n152 : B225n152.2.Nodup ∧ Closed B225.mask B225.goal B225n152 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B7]) (seen := []) (h := [(0x55550000000000005f5f, 0xf0f, 0x55550000000000005555), (0xf0f, 0xf0f0000000000000f0f, 0xffff)]) (width := 1) (p := 0x10000000000000000001)
  · decide +kernel
  · exact familyCons vB7 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n153 : Cell := (5, [0x33330000000000003030, 0x33330000000000003333, 0xf0f0000000000000f0f, 0xffff, 0x55550000000000005555, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n153 : B225n153.2.Nodup ∧ Closed B225.mask B225.goal B225n153 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := []) (seen := []) (h := [(0x33330000000000003030, 0xf0f, 0x33330000000000003333), (0xf0f, 0xf0f0000000000000f0f, 0xffff)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n154 : Cell := (5, [0xff00000000000000f0, 0xff00000000000000ff, 0xf0f0000000000000f0f, 0xffff, 0x55550000000000005555, 0x33330000000000003333])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n154 : B225n154.2.Nodup ∧ Closed B225.mask B225.goal B225n154 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := []) (seen := []) (h := [(0xff00000000000000f0, 0xf0f, 0xff00000000000000ff), (0xf0f, 0xf0f0000000000000f0f, 0xffff)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n155 : Cell := (6, [0xf0f, 0xf0f0000000000000f0f, 0xffff, 0x55550000000000005555, 0x33330000000000003333, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n155 : B225n155.2.Nodup ∧ Closed B225.mask B225.goal B225n155 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B141, B142, B143, B144]) (seen := [B225n25, B225n30, B225n65, B225n73, B225n83, B225n92, B225n136, B225n142, B225n148, B225n149, B225n150, B225n151, B225n152, B225n153, B225n154]) (h := [(0xf0f, 0xf0f0000000000000f0f, 0xffff)]) (width := 5) (p := 0x20000000001c000000000800000000300000000008000000002800000000080000000018000084000040034000040004c000040002c0000c000480000c000240001224041ee01000014000084000000009a000000)
  · decide +kernel
  · exact familyCons vB141 <| familyCons vB142 <| familyCons vB143 <| familyCons vB144 <| familyNil
  · exact familyCons vB225n25 <| familyCons vB225n30 <| familyCons vB225n65 <| familyCons vB225n73 <| familyCons vB225n83 <| familyCons vB225n92 <| familyCons vB225n136 <| familyCons vB225n142 <| familyCons vB225n148 <| familyCons vB225n149 <| familyCons vB225n150 <| familyCons vB225n151 <| familyCons vB225n152 <| familyCons vB225n153 <| familyCons vB225n154 <| familyNil
  · decide +kernel
  · decide +kernel
def B225n156 : Cell := (5, [0x50500000000000005555, 0x55550000000000005555, 0xf0f0000000000000f0f, 0xffff, 0x33330000000000003333, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n156 : B225n156.2.Nodup ∧ Closed B225.mask B225.goal B225n156 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B144]) (seen := []) (h := [(0x50500000000000005555, 0xf0f0000000000000000, 0x55550000000000005555), (0xf0f0000000000000000, 0xf0f0000000000000f0f, 0xffff)]) (width := 1) (p := 0x10000)
  · decide +kernel
  · exact familyCons vB144 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n157 : Cell := (4, [0xcf00000000000000cc, 0x33330000000000003333, 0xf0f0000000000000f0f, 0xffff, 0x55550000000000005555])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n157 : B225n157.2.Nodup ∧ Closed B225.mask B225.goal B225n157 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := []) (seen := []) (h := [(0xcf00000000000000cc, 0x30300000000000003333, 0xff00000000000000ff), (0x30300000000000003333, 0xf0f0000000000000000, 0x33330000000000003333), (0xf0f0000000000000000, 0xf0f0000000000000f0f, 0xffff)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n158 : Cell := (5, [0x30300000000000003333, 0x33330000000000003333, 0xf0f0000000000000f0f, 0xffff, 0x55550000000000005555, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n158 : B225n158.2.Nodup ∧ Closed B225.mask B225.goal B225n158 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B141]) (seen := [B225n157]) (h := [(0x30300000000000003333, 0xf0f0000000000000000, 0x33330000000000003333), (0xf0f0000000000000000, 0xf0f0000000000000f0f, 0xffff)]) (width := 2) (p := 0x10200000000000000000000000000000000)
  · decide +kernel
  · exact familyCons vB141 <| familyNil
  · exact familyCons vB225n157 <| familyNil
  · decide +kernel
  · decide +kernel
def B225n159 : Cell := (4, [0x33030000000000003300, 0xff00000000000000ff, 0xf0f0000000000000f0f, 0xffff, 0x55550000000000005555])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n159 : B225n159.2.Nodup ∧ Closed B225.mask B225.goal B225n159 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := []) (seen := []) (h := [(0x33030000000000003300, 0xf000000000000000ff, 0x33330000000000003333), (0xf000000000000000ff, 0xf0f0000000000000000, 0xff00000000000000ff), (0xf0f0000000000000000, 0xf0f0000000000000f0f, 0xffff)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n160 : Cell := (5, [0xf000000000000000ff, 0xff00000000000000ff, 0xf0f0000000000000f0f, 0xffff, 0x55550000000000005555, 0x33330000000000003333])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n160 : B225n160.2.Nodup ∧ Closed B225.mask B225.goal B225n160 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B143]) (seen := [B225n159]) (h := [(0xf000000000000000ff, 0xf0f0000000000000000, 0xff00000000000000ff), (0xf0f0000000000000000, 0xf0f0000000000000f0f, 0xffff)]) (width := 2) (p := 0x10200000000000000000000000000000000)
  · decide +kernel
  · exact familyCons vB143 <| familyNil
  · exact familyCons vB225n159 <| familyNil
  · decide +kernel
  · decide +kernel
def B225n161 : Cell := (6, [0xf0f0000000000000000, 0xf0f0000000000000f0f, 0xffff, 0x55550000000000005555, 0x33330000000000003333, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n161 : B225n161.2.Nodup ∧ Closed B225.mask B225.goal B225n161 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B141, B142, B143, B144]) (seen := [B225n26, B225n37, B225n66, B225n74, B225n84, B225n137, B225n148, B225n156, B225n158, B225n160]) (h := [(0xf0f0000000000000000, 0xf0f0000000000000f0f, 0xffff)]) (width := 4) (p := 0x80000000700000000000000000000000000000000000200000006000000002002200b0001000e0001000a0003000d000300090004000c00040005000220000002b00000)
  · decide +kernel
  · exact familyCons vB141 <| familyCons vB142 <| familyCons vB143 <| familyCons vB144 <| familyNil
  · exact familyCons vB225n26 <| familyCons vB225n37 <| familyCons vB225n66 <| familyCons vB225n74 <| familyCons vB225n84 <| familyCons vB225n137 <| familyCons vB225n148 <| familyCons vB225n156 <| familyCons vB225n158 <| familyCons vB225n160 <| familyNil
  · decide +kernel
  · decide +kernel
def B225n162 : Cell := (6, [0xf0f0, 0xf0f0000000000000f0f, 0xffff, 0x55550000000000005555, 0x33330000000000003333, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n162 : B225n162.2.Nodup ∧ Closed B225.mask B225.goal B225n162 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B141, B142]) (seen := []) (h := [(0xf0f0, 0xf0f0000000000000f0f, 0xffff)]) (width := 2) (p := 0x200020002000200020002020280810201020202020202020202028002800)
  · decide +kernel
  · exact familyCons vB141 <| familyCons vB142 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n163 : Cell := (6, [0xf0f000000000000ffff, 0xf0f0000000000000f0f, 0xffff, 0x55550000000000005555, 0x33330000000000003333, 0xff00000000000000ff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n163 : B225n163.2.Nodup ∧ Closed B225.mask B225.goal B225n163 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B141, B142]) (seen := []) (h := [(0xf0f000000000000ffff, 0xf0f0000000000000f0f, 0xffff)]) (width := 2) (p := 0x200020002008281020192a20202a2a20202a2a00280028)
  · decide +kernel
  · exact familyCons vB141 <| familyCons vB142 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n164 : Cell := (5, [0xff0000000000000000, 0xff, 0xffff, 0x55550000000000005555, 0x33330000000000003333, 0xf0f0000000000000f0f])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n164 : B225n164.2.Nodup ∧ Closed B225.mask B225.goal B225n164 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B6, B141]) (seen := []) (h := [(0xff0000000000000000, 0xff, 0xff00000000000000ff), (0xff, 0xff00000000000000ff, 0xffff)]) (width := 2) (p := 0x100000000000000000000000000000000000000000000000200)
  · decide +kernel
  · exact familyCons vB6 <| familyCons vB141 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n165 : Cell := (5, [0x55550000000000005500, 0x55550000000000005555, 0xff00000000000000ff, 0xffff, 0x33330000000000003333, 0xf0f0000000000000f0f])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n165 : B225n165.2.Nodup ∧ Closed B225.mask B225.goal B225n165 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := []) (seen := []) (h := [(0x55550000000000005500, 0xff, 0x55550000000000005555), (0xff, 0xff00000000000000ff, 0xffff)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n166 : Cell := (5, [0x33330000000000003300, 0xff00000000000000ff, 0xffff, 0x55550000000000005555, 0xf0f0000000000000f0f])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n166 : B225n166.2.Nodup ∧ Closed B225.mask B225.goal B225n166 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := []) (seen := []) (h := [(0x33330000000000003300, 0xff, 0x33330000000000003333), (0xff, 0xff00000000000000ff, 0xffff)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n167 : Cell := (5, [0x33330000000000003300, 0xff, 0xff00000000000000ff, 0xffff, 0x55550000000000005555, 0xf0f0000000000000f0f])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n167 : B225n167.2.Nodup ∧ Closed B225.mask B225.goal B225n167 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B143]) (seen := []) (h := [(0x33330000000000003300, 0xff, 0x33330000000000003333), (0xff, 0xff00000000000000ff, 0xffff)]) (width := 1) (p := 0x10)
  · decide +kernel
  · exact familyCons vB143 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n168 : Cell := (5, [0x33330000000000003300, 0x33330000000000003333, 0xff00000000000000ff, 0xffff, 0x55550000000000005555, 0xf0f0000000000000f0f])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n168 : B225n168.2.Nodup ∧ Closed B225.mask B225.goal B225n168 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := []) (seen := []) (h := [(0x33330000000000003300, 0xff, 0x33330000000000003333), (0xff, 0xff00000000000000ff, 0xffff)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n169 : Cell := (5, [0x333300000000000033ff, 0xff, 0xff00000000000000ff, 0xffff, 0x55550000000000005555, 0xf0f0000000000000f0f])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n169 : B225n169.2.Nodup ∧ Closed B225.mask B225.goal B225n169 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B6]) (seen := []) (h := [(0x333300000000000033ff, 0xff, 0x33330000000000003333), (0xff, 0xff00000000000000ff, 0xffff)]) (width := 1) (p := 0x10000000000000000001)
  · decide +kernel
  · exact familyCons vB6 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n170 : Cell := (5, [0xf0f0000000000000f00, 0xf0f0000000000000f0f, 0xff00000000000000ff, 0xffff, 0x55550000000000005555, 0x33330000000000003333])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n170 : B225n170.2.Nodup ∧ Closed B225.mask B225.goal B225n170 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := []) (seen := []) (h := [(0xf0f0000000000000f00, 0xff, 0xf0f0000000000000f0f), (0xff, 0xff00000000000000ff, 0xffff)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n171 : Cell := (6, [0xff, 0xff00000000000000ff, 0xffff, 0x55550000000000005555, 0x33330000000000003333, 0xf0f0000000000000f0f])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n171 : B225n171.2.Nodup ∧ Closed B225.mask B225.goal B225n171 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B141, B142, B143, B144]) (seen := [B225n44, B225n53, B225n99, B225n104, B225n119, B225n127, B225n136, B225n143, B225n164, B225n165, B225n166, B225n167, B225n168, B225n169, B225n170]) (h := [(0xff, 0xff00000000000000ff, 0xffff)]) (width := 5) (p := 0x28000000002400000000000000000000000000000400000000300000000004000000002000000000040000000018000042000020034000080004c000080002c0000e430460f00c0001c00010000380001000014000042000000005a000000)
  · decide +kernel
  · exact familyCons vB141 <| familyCons vB142 <| familyCons vB143 <| familyCons vB144 <| familyNil
  · exact familyCons vB225n44 <| familyCons vB225n53 <| familyCons vB225n99 <| familyCons vB225n104 <| familyCons vB225n119 <| familyCons vB225n127 <| familyCons vB225n136 <| familyCons vB225n143 <| familyCons vB225n164 <| familyCons vB225n165 <| familyCons vB225n166 <| familyCons vB225n167 <| familyCons vB225n168 <| familyCons vB225n169 <| familyCons vB225n170 <| familyNil
  · decide +kernel
  · decide +kernel
def B225n172 : Cell := (4, [0xa0f0000000000000a0a, 0x55550000000000005555, 0xff00000000000000ff, 0xffff, 0x33330000000000003333])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n172 : B225n172.2.Nodup ∧ Closed B225.mask B225.goal B225n172 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := []) (seen := []) (h := [(0xa0f0000000000000a0a, 0x55000000000000005555, 0xf0f0000000000000f0f), (0x55000000000000005555, 0xff0000000000000000, 0x55550000000000005555), (0xff0000000000000000, 0xff00000000000000ff, 0xffff)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n173 : Cell := (5, [0x55000000000000005555, 0x55550000000000005555, 0xff00000000000000ff, 0xffff, 0x33330000000000003333, 0xf0f0000000000000f0f])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n173 : B225n173.2.Nodup ∧ Closed B225.mask B225.goal B225n173 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B142]) (seen := [B225n172]) (h := [(0x55000000000000005555, 0xff0000000000000000, 0x55550000000000005555), (0xff0000000000000000, 0xff00000000000000ff, 0xffff)]) (width := 2) (p := 0x10200000000000000000000000000000000)
  · decide +kernel
  · exact familyCons vB142 <| familyNil
  · exact familyCons vB225n172 <| familyNil
  · decide +kernel
  · decide +kernel
def B225n174 : Cell := (5, [0x33000000000000003333, 0x33330000000000003333, 0xff00000000000000ff, 0xffff, 0x55550000000000005555, 0xf0f0000000000000f0f])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n174 : B225n174.2.Nodup ∧ Closed B225.mask B225.goal B225n174 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B143]) (seen := []) (h := [(0x33000000000000003333, 0xff0000000000000000, 0x33330000000000003333), (0xff0000000000000000, 0xff00000000000000ff, 0xffff)]) (width := 1) (p := 0x10000)
  · decide +kernel
  · exact familyCons vB143 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n175 : Cell := (4, [0x50550000000000005050, 0xf0f0000000000000f0f, 0xff00000000000000ff, 0xffff, 0x33330000000000003333])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n175 : B225n175.2.Nodup ∧ Closed B225.mask B225.goal B225n175 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 3) (bs := []) (seen := []) (h := [(0x50550000000000005050, 0xf000000000000000f0f, 0x55550000000000005555), (0xf000000000000000f0f, 0xff0000000000000000, 0xf0f0000000000000f0f), (0xff0000000000000000, 0xff00000000000000ff, 0xffff)]) (width := 0) (p := 0x0)
  · decide +kernel
  · exact familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n176 : Cell := (5, [0xf000000000000000f0f, 0xf0f0000000000000f0f, 0xff00000000000000ff, 0xffff, 0x55550000000000005555, 0x33330000000000003333])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n176 : B225n176.2.Nodup ∧ Closed B225.mask B225.goal B225n176 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 4) (bs := [B144]) (seen := [B225n175]) (h := [(0xf000000000000000f0f, 0xff0000000000000000, 0xf0f0000000000000f0f), (0xff0000000000000000, 0xff00000000000000ff, 0xffff)]) (width := 2) (p := 0x102000000000000000000000000)
  · decide +kernel
  · exact familyCons vB144 <| familyNil
  · exact familyCons vB225n175 <| familyNil
  · decide +kernel
  · decide +kernel
def B225n177 : Cell := (6, [0xff0000000000000000, 0xff00000000000000ff, 0xffff, 0x55550000000000005555, 0x33330000000000003333, 0xf0f0000000000000f0f])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n177 : B225n177.2.Nodup ∧ Closed B225.mask B225.goal B225n177 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B141, B142, B143, B144]) (seen := [B225n45, B225n100, B225n109, B225n120, B225n128, B225n137, B225n164, B225n173, B225n174, B225n176]) (h := [(0xff0000000000000000, 0xff00000000000000ff, 0xffff)]) (width := 4) (p := 0x900000008000000000000000000000000000000000001000000070000000000000000000000001001100b0002000e0002000a0003000d000300060004000c00040005000110000001b00000)
  · decide +kernel
  · exact familyCons vB141 <| familyCons vB142 <| familyCons vB143 <| familyCons vB144 <| familyNil
  · exact familyCons vB225n45 <| familyCons vB225n100 <| familyCons vB225n109 <| familyCons vB225n120 <| familyCons vB225n128 <| familyCons vB225n137 <| familyCons vB225n164 <| familyCons vB225n173 <| familyCons vB225n174 <| familyCons vB225n176 <| familyNil
  · decide +kernel
  · decide +kernel
def B225n178 : Cell := (6, [0xff00, 0xff00000000000000ff, 0xffff, 0x55550000000000005555, 0x33330000000000003333, 0xf0f0000000000000f0f])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n178 : B225n178.2.Nodup ∧ Closed B225.mask B225.goal B225n178 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B141]) (seen := []) (h := [(0xff00, 0xff00000000000000ff, 0xffff)]) (width := 1) (p := 0x404040404044624444444444446060)
  · decide +kernel
  · exact familyCons vB141 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n179 : Cell := (6, [0xff000000000000ffff, 0xff00000000000000ff, 0xffff, 0x55550000000000005555, 0x33330000000000003333, 0xf0f0000000000000f0f])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n179 : B225n179.2.Nodup ∧ Closed B225.mask B225.goal B225n179 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B141]) (seen := []) (h := [(0xff000000000000ffff, 0xff00000000000000ff, 0xffff)]) (width := 1) (p := 0x404000004264477447744770606)
  · decide +kernel
  · exact familyCons vB141 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B225n180 : Cell := (7, [0x55550000000000005555, 0x33330000000000003333, 0xf0f0000000000000f0f, 0xff00000000000000ff, 0xffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225n180 : B225n180.2.Nodup ∧ Closed B225.mask B225.goal B225n180 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 6) (bs := []) (seen := [B225n18, B225n19, B225n20, B225n21, B225n31, B225n34, B225n38, B225n39, B225n54, B225n55, B225n56, B225n57, B225n67, B225n75, B225n76, B225n77, B225n93, B225n94, B225n95, B225n96, B225n105, B225n107, B225n110, B225n111, B225n121, B225n129, B225n130, B225n131, B225n144, B225n145, B225n146, B225n147, B225n155, B225n161, B225n162, B225n163, B225n171, B225n177, B225n178, B225n179]) (h := []) (width := 6) (p := 0xa000009c00009800009400009000008c00008800008400008000007c00007800007400007000006c00006800006400006000005c00005800005400005000004c00004800004400004000003c00003800003400003000002c00002800002400002000001c00001800001400001000000c0000080000040000)
  · decide +kernel
  · exact familyNil
  · exact familyCons vB225n18 <| familyCons vB225n19 <| familyCons vB225n20 <| familyCons vB225n21 <| familyCons vB225n31 <| familyCons vB225n34 <| familyCons vB225n38 <| familyCons vB225n39 <| familyCons vB225n54 <| familyCons vB225n55 <| familyCons vB225n56 <| familyCons vB225n57 <| familyCons vB225n67 <| familyCons vB225n75 <| familyCons vB225n76 <| familyCons vB225n77 <| familyCons vB225n93 <| familyCons vB225n94 <| familyCons vB225n95 <| familyCons vB225n96 <| familyCons vB225n105 <| familyCons vB225n107 <| familyCons vB225n110 <| familyCons vB225n111 <| familyCons vB225n121 <| familyCons vB225n129 <| familyCons vB225n130 <| familyCons vB225n131 <| familyCons vB225n144 <| familyCons vB225n145 <| familyCons vB225n146 <| familyCons vB225n147 <| familyCons vB225n155 <| familyCons vB225n161 <| familyCons vB225n162 <| familyCons vB225n163 <| familyCons vB225n171 <| familyCons vB225n177 <| familyCons vB225n178 <| familyCons vB225n179 <| familyNil
  · decide +kernel
  · decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB225 : Valid B225 := by
  apply small_bound (bs := []) (seen := [B225n180]) (width := 1) (p := 0x4000000000000000)
  · decide +kernel
  · exact familyNil
  · exact familyCons vB225n180 <| familyNil
  · decide +kernel
  · apply canon_checked; decide +kernel
  · decide +kernel
end PEqualNP.Outside.L_meta_10626.SignedCert.GraphB

namespace PEqualNP.Outside.L_meta_10626.SignedCert.GraphB
def B226 : Bound := ⟨0xff00ff0000000000ff00ff, [0x0, 0x5500550000000000550055, 0x3300330000000000330033, 0xf000f00000000000f000f, 0xff00000000000000ff, 0xff00ff], 0x1000000000005005f, 8⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB226 : Valid B226 := by
  apply small_bound (bs := [B163]) (seen := []) (width := 1) (p := 0x4000000000000000)
  · decide +kernel
  · exact familyCons vB163 <| familyNil
  · exact familyNil
  · decide +kernel
  · apply canon_checked; decide +kernel
  · decide +kernel
end PEqualNP.Outside.L_meta_10626.SignedCert.GraphB

namespace PEqualNP.Outside.L_meta_10626.SignedCert.GraphB
def B227 : Bound := ⟨0xf0f0f0f000000000f0f0f0f, [0x0, 0x50505050000000005050505, 0x30303030000000003030303, 0xf000f00000000000f000f, 0xf0f0000000000000f0f, 0xf0f0f0f], 0x1000000000105030f, 8⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB227 : Valid B227 := by
  apply transfer vB225 0xb76acd8972a4c8a74a8d0870a0c00000000000000000000000000000000000000000000000000000000000000000000000000000000000003668c98162848826488900608080 <;> decide +kernel
end PEqualNP.Outside.L_meta_10626.SignedCert.GraphB

namespace PEqualNP.Outside.L_meta_10626.SignedCert.GraphB
def B228 : Bound := ⟨0x333333330000000033333333, [0x0, 0x111111110000000011111111, 0x30303030000000003030303, 0x3300330000000000330033, 0x33330000000000003333, 0x33333333], 0x10000000001011313, 8⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB228 : Valid B228 := by
  apply transfer vB226 0xbb72ad4b3628d0000000000000009b322c493220c000000000000000000000000000000000000000000000000000000000000000000000003a70a943260890000000000000001a302841220080 <;> decide +kernel
end PEqualNP.Outside.L_meta_10626.SignedCert.GraphB

namespace PEqualNP.Outside.L_meta_10626.SignedCert.GraphB
def B229 : Bound := ⟨0x555555550000000055555555, [0x0, 0x111111110000000011111111, 0x50505050000000005050505, 0x5500550000000000550055, 0x55550000000000005555, 0x55555555], 0x10000000001051155, 8⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB229 : Valid B229 := by
  apply transfer vB225 0xbd72d58ad529509d325488d121400000000000000000000000000000000000000000000000000000000000000000000000000000000000003c70d182c509101c305080c10100 <;> decide +kernel
end PEqualNP.Outside.L_meta_10626.SignedCert.GraphB

namespace PEqualNP.Outside.L_meta_10626.SignedCert.GraphB
def B230 : Bound := ⟨0xf0f00000f0f00000f0f00000f0f, [0x0, 0x505000005050000050500000505, 0x303000003030000030300000303, 0xf0000000f0000000f0000000f, 0xf0f0000000000000f0f, 0xf0f00000f0f], 0x1000000010000030f, 8⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB230 : Valid B230 := by
  apply small_bound (bs := [B164]) (seen := []) (width := 1) (p := 0x4000000000000000)
  · decide +kernel
  · exact familyCons vB164 <| familyNil
  · exact familyNil
  · decide +kernel
  · apply canon_checked; decide +kernel
  · decide +kernel
end PEqualNP.Outside.L_meta_10626.SignedCert.GraphB

namespace PEqualNP.Outside.L_meta_10626.SignedCert.GraphB
def B231 : Bound := ⟨0x5555000055550000555500005555, [0x0, 0x1111000011110000111100001111, 0x505000005050000050500000505, 0x55000000550000005500000055, 0x55550000000000005555, 0x555500005555], 0x10000001100001155, 8⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB231 : Valid B231 := by
  apply transfer vB226 0xddb3568cd93160000000000000009d325488d1214000000000000000000000000000000000000000000000000000000000000000000000005cb15284c91120000000000000001c305080c10100 <;> decide +kernel
end PEqualNP.Outside.L_meta_10626.SignedCert.GraphB

namespace PEqualNP.Outside.L_meta_10626.SignedCert.GraphB
def B244 : Bound := ⟨0xffffffff00000000ffffffff, [0x0, 0x555555550000000055555555, 0x333333330000000033333333, 0xf0f0f0f000000000f0f0f0f, 0xff00ff0000000000ff00ff, 0xffff000000000000ffff, 0xffffffff], 0x1000000000105135f, 10⟩
def B244n0 : Cell := (9, [0x555555550000000055555555, 0x333333330000000033333333, 0xf0f0f0f000000000f0f0f0f, 0xff00ff0000000000ff00ff, 0xffff000000000000ffff, 0xffffffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB244n0 : B244n0.2.Nodup ∧ Closed B244.mask B244.goal B244n0 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 8) (bs := [B225, B226, B227, B228, B229]) (seen := []) (h := []) (width := 3) (p := 0x200200200200400400400400200200200200600600600600200200200200400400400400800800800800200200200200400400400400600600600600a00a00a00a00200200200200400400400400600600600600800800800800)
  · decide +kernel
  · exact familyCons vB225 <| familyCons vB226 <| familyCons vB227 <| familyCons vB228 <| familyCons vB229 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB244 : Valid B244 := by
  apply small_bound (bs := []) (seen := [B244n0]) (width := 1) (p := 0x40000000000000000000000000000000)
  · decide +kernel
  · exact familyNil
  · exact familyCons vB244n0 <| familyNil
  · decide +kernel
  · apply canon_checked; decide +kernel
  · decide +kernel
end PEqualNP.Outside.L_meta_10626.SignedCert.GraphB

namespace PEqualNP.Outside.L_meta_10626.SignedCert.GraphB
def B245 : Bound := ⟨0xffff0000ffff0000ffff0000ffff, [0x0, 0x5555000055550000555500005555, 0x3333000033330000333300003333, 0xf0f00000f0f00000f0f00000f0f, 0xff000000ff000000ff000000ff, 0xffff000000000000ffff, 0xffff0000ffff], 0x1000000110000135f, 10⟩
def B245n0 : Cell := (6, [0xffcc0000ffcc, 0x3300000033, 0x3333000033330000333300003333, 0xff000000ff000000ff000000ff, 0x5555000055550000555500005555, 0xf0f00000f0f00000f0f00000f0f, 0xffff000000000000ffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB245n0 : B245n0.2.Nodup ∧ Closed B245.mask B245.goal B245n0 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B225]) (seen := []) (h := [(0xffcc0000ffcc, 0x3300000033, 0xffff0000ffff), (0x3300000033, 0x33000000330000003300000033, 0xffff0000ffff), (0x33000000330000003300000033, 0x3333000033330000333300003333, 0xff000000ff000000ff000000ff)]) (width := 1) (p := 0x10)
  · decide +kernel
  · exact familyCons vB225 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B245n1 : Cell := (6, [0x3333000033330000330000003300, 0x3300000033, 0xffff0000ffff, 0xff000000ff000000ff000000ff, 0x5555000055550000555500005555, 0xf0f00000f0f00000f0f00000f0f, 0xffff000000000000ffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB245n1 : B245n1.2.Nodup ∧ Closed B245.mask B245.goal B245n1 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B225]) (seen := []) (h := [(0x3333000033330000330000003300, 0x3300000033, 0x3333000033330000333300003333), (0x3300000033, 0x33000000330000003300000033, 0xffff0000ffff), (0x33000000330000003300000033, 0x3333000033330000333300003333, 0xff000000ff000000ff000000ff)]) (width := 1) (p := 0x10)
  · decide +kernel
  · exact familyCons vB225 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B245n2 : Cell := (6, [0xff000000ff000000cc000000cc, 0x3300000033, 0xffff0000ffff, 0x3333000033330000333300003333, 0x5555000055550000555500005555, 0xf0f00000f0f00000f0f00000f0f, 0xffff000000000000ffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB245n2 : B245n2.2.Nodup ∧ Closed B245.mask B245.goal B245n2 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B225]) (seen := []) (h := [(0xff000000ff000000cc000000cc, 0x3300000033, 0xff000000ff000000ff000000ff), (0x3300000033, 0x33000000330000003300000033, 0xffff0000ffff), (0x33000000330000003300000033, 0x3333000033330000333300003333, 0xff000000ff000000ff000000ff)]) (width := 1) (p := 0x10)
  · decide +kernel
  · exact familyCons vB225 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B245n3 : Cell := (7, [0x3300000033, 0xffff0000ffff, 0x3333000033330000333300003333, 0xff000000ff000000ff000000ff, 0x5555000055550000555500005555, 0xf0f00000f0f00000f0f00000f0f, 0xffff000000000000ffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB245n3 : B245n3.2.Nodup ∧ Closed B245.mask B245.goal B245n3 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 6) (bs := [B217, B221, B222, B225, B230, B231]) (seen := [B245n0, B245n1, B245n2]) (h := [(0x3300000033, 0x33000000330000003300000033, 0xffff0000ffff), (0x33000000330000003300000033, 0x3333000033330000333300003333, 0xff000000ff000000ff000000ff)]) (width := 4) (p := 0x4000000040000000000000000000000000000000000000004000000040000000000000000000000000000000000000004000000040000000000000000000000000000000000000000000000000000000400000004000000000000000000000000000000000000000000000000000000000000000000040004000400040005000500050005000600060006000600029000000380000001700000)
  · decide +kernel
  · exact familyCons vB217 <| familyCons vB221 <| familyCons vB222 <| familyCons vB225 <| familyCons vB230 <| familyCons vB231 <| familyNil
  · exact familyCons vB245n0 <| familyCons vB245n1 <| familyCons vB245n2 <| familyNil
  · decide +kernel
  · decide +kernel
def B245n4 : Cell := (6, [0x3333000033330000330000003300, 0x33000000330000003300000033, 0xffff0000ffff, 0xff000000ff000000ff000000ff, 0x5555000055550000555500005555, 0xf0f00000f0f00000f0f00000f0f, 0xffff000000000000ffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB245n4 : B245n4.2.Nodup ∧ Closed B245.mask B245.goal B245n4 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B221, B225]) (seen := []) (h := [(0x3333000033330000330000003300, 0x3300000033, 0x3333000033330000333300003333), (0x3300000033, 0x33000000330000003300000033, 0xffff0000ffff), (0x33000000330000003300000033, 0x3333000033330000333300003333, 0xff000000ff000000ff000000ff)]) (width := 2) (p := 0x10000000000000002000000)
  · decide +kernel
  · exact familyCons vB221 <| familyCons vB225 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B245n5 : Cell := (6, [0xff000000ff000000cc000000cc, 0x33000000330000003300000033, 0xffff0000ffff, 0x3333000033330000333300003333, 0x5555000055550000555500005555, 0xf0f00000f0f00000f0f00000f0f, 0xffff000000000000ffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB245n5 : B245n5.2.Nodup ∧ Closed B245.mask B245.goal B245n5 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B221, B225]) (seen := []) (h := [(0xff000000ff000000cc000000cc, 0x3300000033, 0xff000000ff000000ff000000ff), (0x3300000033, 0x33000000330000003300000033, 0xffff0000ffff), (0x33000000330000003300000033, 0x3333000033330000333300003333, 0xff000000ff000000ff000000ff)]) (width := 2) (p := 0x10000000000000002000000)
  · decide +kernel
  · exact familyCons vB221 <| familyCons vB225 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B245n6 : Cell := (7, [0x3300000033, 0x33000000330000003300000033, 0xffff0000ffff, 0x3333000033330000333300003333, 0xff000000ff000000ff000000ff, 0x5555000055550000555500005555, 0xf0f00000f0f00000f0f00000f0f, 0xffff000000000000ffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB245n6 : B245n6.2.Nodup ∧ Closed B245.mask B245.goal B245n6 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 6) (bs := [B217, B221]) (seen := [B245n0, B245n4, B245n5]) (h := [(0x3300000033, 0x33000000330000003300000033, 0xffff0000ffff), (0x33000000330000003300000033, 0x3333000033330000333300003333, 0xff000000ff000000ff000000ff)]) (width := 3) (p := 0x2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001003000000000000000000000000000000000000000005000004000000000001000)
  · decide +kernel
  · exact familyCons vB217 <| familyCons vB221 <| familyNil
  · exact familyCons vB245n0 <| familyCons vB245n4 <| familyCons vB245n5 <| familyNil
  · decide +kernel
  · decide +kernel
def B245n7 : Cell := (7, [0x33000000330000000000000000, 0x33000000330000003300000033, 0xffff0000ffff, 0x3333000033330000333300003333, 0xff000000ff000000ff000000ff, 0x5555000055550000555500005555, 0xf0f00000f0f00000f0f00000f0f, 0xffff000000000000ffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB245n7 : B245n7.2.Nodup ∧ Closed B245.mask B245.goal B245n7 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 6) (bs := [B217, B221]) (seen := []) (h := [(0x33000000330000000000000000, 0x33000000330000003300000033, 0xffff0000ffff), (0x33000000330000003300000033, 0x3333000033330000333300003333, 0xff000000ff000000ff000000ff)]) (width := 2) (p := 0x200000000000000000000000000000000000000000000000000000000000000000000000000000101000000000000000000000000000100010000000100)
  · decide +kernel
  · exact familyCons vB217 <| familyCons vB221 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B245n8 : Cell := (7, [0xffcc0000ffcc, 0xffff0000ffff, 0x3333000033330000333300003333, 0xff000000ff000000ff000000ff, 0x5555000055550000555500005555, 0xf0f00000f0f00000f0f00000f0f, 0xffff000000000000ffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB245n8 : B245n8.2.Nodup ∧ Closed B245.mask B245.goal B245n8 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 6) (bs := [B217, B221, B222, B225, B230, B231]) (seen := [B245n0]) (h := [(0xffcc0000ffcc, 0x33000000330000003300000033, 0xffff0000ffff), (0x33000000330000003300000033, 0x3333000033330000333300003333, 0xff000000ff000000ff000000ff)]) (width := 3) (p := 0x1000001000000000000000000000000000001000001000000000000000000000000000001000001000000000000000000000000000000000000000000000000000000000000000000000000000000400000800000400000c0100100100100140140140140180180180180040040040080040040040080078000)
  · decide +kernel
  · exact familyCons vB217 <| familyCons vB221 <| familyCons vB222 <| familyCons vB225 <| familyCons vB230 <| familyCons vB231 <| familyNil
  · exact familyCons vB245n0 <| familyNil
  · decide +kernel
  · decide +kernel
def B245n9 : Cell := (6, [0x333300003333, 0xffcc0000ffcc, 0x33000000330000003300000033, 0xff000000ff000000ff000000ff, 0x5555000055550000555500005555, 0xf0f00000f0f00000f0f00000f0f, 0xffff000000000000ffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB245n9 : B245n9.2.Nodup ∧ Closed B245.mask B245.goal B245n9 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B222]) (seen := []) (h := [(0x333300003333, 0xffff0000ffff, 0x3333000033330000333300003333), (0xffcc0000ffcc, 0x33000000330000003300000033, 0xffff0000ffff), (0x33000000330000003300000033, 0x3333000033330000333300003333, 0xff000000ff000000ff000000ff)]) (width := 1) (p := 0x100000000000000000000000000)
  · decide +kernel
  · exact familyCons vB222 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B245n10 : Cell := (6, [0xff000000ff, 0xffcc0000ffcc, 0x33000000330000003300000033, 0x3333000033330000333300003333, 0x5555000055550000555500005555, 0xf0f00000f0f00000f0f00000f0f, 0xffff000000000000ffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB245n10 : B245n10.2.Nodup ∧ Closed B245.mask B245.goal B245n10 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B221]) (seen := []) (h := [(0xff000000ff, 0xffff0000ffff, 0xff000000ff000000ff000000ff), (0xffcc0000ffcc, 0x33000000330000003300000033, 0xffff0000ffff), (0x33000000330000003300000033, 0x3333000033330000333300003333, 0xff000000ff000000ff000000ff)]) (width := 1) (p := 0x100000000000000000000000000)
  · decide +kernel
  · exact familyCons vB221 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B245n11 : Cell := (7, [0xffcc0000ffcc, 0x33000000330000003300000033, 0xffff0000ffff, 0x3333000033330000333300003333, 0xff000000ff000000ff000000ff, 0x5555000055550000555500005555, 0xf0f00000f0f00000f0f00000f0f, 0xffff000000000000ffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB245n11 : B245n11.2.Nodup ∧ Closed B245.mask B245.goal B245n11 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 6) (bs := [B217, B221, B222]) (seen := [B245n0, B245n9, B245n10]) (h := [(0xffcc0000ffcc, 0x33000000330000003300000033, 0xffff0000ffff), (0x33000000330000003300000033, 0x3333000033330000333300003333, 0xff000000ff000000ff000000ff)]) (width := 3) (p := 0x2000000000000000000000000000000000000000000000000000006000000000005000000000000000000000000000000000000000000000000000001004000000000000000000000000000000000000000000001003000000001002000000001000)
  · decide +kernel
  · exact familyCons vB217 <| familyCons vB221 <| familyCons vB222 <| familyNil
  · exact familyCons vB245n0 <| familyCons vB245n9 <| familyCons vB245n10 <| familyNil
  · decide +kernel
  · decide +kernel
def B245n12 : Cell := (7, [0x33000000330000ffff0000ffff, 0x33000000330000003300000033, 0xffff0000ffff, 0x3333000033330000333300003333, 0xff000000ff000000ff000000ff, 0x5555000055550000555500005555, 0xf0f00000f0f00000f0f00000f0f, 0xffff000000000000ffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB245n12 : B245n12.2.Nodup ∧ Closed B245.mask B245.goal B245n12 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 6) (bs := [B217, B221, B225, B230, B231]) (seen := []) (h := [(0x33000000330000ffff0000ffff, 0x33000000330000003300000033, 0xffff0000ffff), (0x33000000330000003300000033, 0x3333000033330000333300003333, 0xff000000ff000000ff000000ff)]) (width := 3) (p := 0x2000000000000000000000000000000000000000000000000000001000000000001000000000000000000000000000000000000000000000000000001001000000003001000000004001000000005001000000001001000000001001000000000001)
  · decide +kernel
  · exact familyCons vB217 <| familyCons vB221 <| familyCons vB225 <| familyCons vB230 <| familyCons vB231 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B245n13 : Cell := (6, [0xff000000ff000000cc000000cc, 0x333300003333, 0xffff0000ffff, 0x33000000330000003300000033, 0x5555000055550000555500005555, 0xf0f00000f0f00000f0f00000f0f, 0xffff000000000000ffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB245n13 : B245n13.2.Nodup ∧ Closed B245.mask B245.goal B245n13 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B221, B222]) (seen := []) (h := [(0xff000000ff000000cc000000cc, 0x333300003333, 0xff000000ff000000ff000000ff), (0x333300003333, 0x3333000033330000333300003333, 0xffff0000ffff), (0x33000000330000003300000033, 0x3333000033330000333300003333, 0xff000000ff000000ff000000ff)]) (width := 2) (p := 0x20100)
  · decide +kernel
  · exact familyCons vB221 <| familyCons vB222 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B245n14 : Cell := (6, [0xff000000ff, 0x333300003333, 0x33000000330000003300000033, 0x5555000055550000555500005555, 0xf0f00000f0f00000f0f00000f0f, 0xffff000000000000ffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB245n14 : B245n14.2.Nodup ∧ Closed B245.mask B245.goal B245n14 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B217, B221, B222, B225, B230, B231]) (seen := []) (h := [(0xff000000ff, 0xffff0000ffff, 0xff000000ff000000ff000000ff), (0x333300003333, 0x3333000033330000333300003333, 0xffff0000ffff), (0x33000000330000003300000033, 0x3333000033330000333300003333, 0xff000000ff000000ff000000ff)]) (width := 3) (p := 0x1000001000000000000000000000000000001000001000001400001400001800001800001000001000000000000000000000000000480080800000001000001000000000000000000000000000480080c00000920100c0000)
  · decide +kernel
  · exact familyCons vB217 <| familyCons vB221 <| familyCons vB222 <| familyCons vB225 <| familyCons vB230 <| familyCons vB231 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B245n15 : Cell := (7, [0x333300003333, 0xffff0000ffff, 0x33000000330000003300000033, 0xff000000ff000000ff000000ff, 0x5555000055550000555500005555, 0xf0f00000f0f00000f0f00000f0f, 0xffff000000000000ffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB245n15 : B245n15.2.Nodup ∧ Closed B245.mask B245.goal B245n15 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 6) (bs := [B217, B221, B222, B225, B230, B231]) (seen := [B245n9, B245n13, B245n14]) (h := [(0x333300003333, 0x3333000033330000333300003333, 0xffff0000ffff), (0x33000000330000003300000033, 0x3333000033330000333300003333, 0xff000000ff000000ff000000ff)]) (width := 4) (p := 0x400000004000000000000000000000000000000000000000400000004000000000000000000000000000000000000000400000004000000050000000500000006000000060002300000000004000000040000000000000000000000000000000000000001000010021901100010070000000000040000000400000000000000000000000000000000000222008002000000011100100200000001300000)
  · decide +kernel
  · exact familyCons vB217 <| familyCons vB221 <| familyCons vB222 <| familyCons vB225 <| familyCons vB230 <| familyCons vB231 <| familyNil
  · exact familyCons vB245n9 <| familyCons vB245n13 <| familyCons vB245n14 <| familyNil
  · decide +kernel
  · decide +kernel
def B245n16 : Cell := (6, [0x3333000033330000330000003300, 0xff000000ff, 0xffff0000ffff, 0x33000000330000003300000033, 0x5555000055550000555500005555, 0xf0f00000f0f00000f0f00000f0f, 0xffff000000000000ffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB245n16 : B245n16.2.Nodup ∧ Closed B245.mask B245.goal B245n16 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B221, B222]) (seen := []) (h := [(0x3333000033330000330000003300, 0xff000000ff, 0x3333000033330000333300003333), (0xff000000ff, 0xff000000ff000000ff000000ff, 0xffff0000ffff), (0x33000000330000003300000033, 0x3333000033330000333300003333, 0xff000000ff000000ff000000ff)]) (width := 2) (p := 0x10200)
  · decide +kernel
  · exact familyCons vB221 <| familyCons vB222 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B245n17 : Cell := (7, [0xff000000ff, 0xffff0000ffff, 0x33000000330000003300000033, 0x3333000033330000333300003333, 0x5555000055550000555500005555, 0xf0f00000f0f00000f0f00000f0f, 0xffff000000000000ffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB245n17 : B245n17.2.Nodup ∧ Closed B245.mask B245.goal B245n17 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 6) (bs := [B217, B221, B222, B225, B230, B231]) (seen := [B245n10, B245n14, B245n16]) (h := [(0xff000000ff, 0xff000000ff000000ff000000ff, 0xffff0000ffff), (0x33000000330000003300000033, 0x3333000033330000333300003333, 0xff000000ff000000ff000000ff)]) (width := 4) (p := 0x400000004000000000000000000000000000000000000000400000004000000000000000000000000000000000000000400000004000000050000000500000006000000060002200000000004000000040000000000000000000000000000000000000001000010031801100010070000000000040000000400000000000000000000000000000000000333009003000000011100100300000001200000)
  · decide +kernel
  · exact familyCons vB217 <| familyCons vB221 <| familyCons vB222 <| familyCons vB225 <| familyCons vB230 <| familyCons vB231 <| familyNil
  · exact familyCons vB245n10 <| familyCons vB245n14 <| familyCons vB245n16 <| familyNil
  · decide +kernel
  · decide +kernel
def B245n18 : Cell := (8, [0x33000000330000003300000033, 0x3333000033330000333300003333, 0xff000000ff000000ff000000ff, 0x5555000055550000555500005555, 0xf0f00000f0f00000f0f00000f0f, 0xffff000000000000ffff, 0xffff0000ffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB245n18 : B245n18.2.Nodup ∧ Closed B245.mask B245.goal B245n18 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 7) (bs := [B217, B221, B222, B225, B230, B231]) (seen := [B245n3, B245n6, B245n7, B245n8, B245n11, B245n12, B245n15, B245n17]) (h := [(0x33000000330000003300000033, 0x3333000033330000333300003333, 0xff000000ff000000ff000000ff)]) (width := 4) (p := 0x4000400040004000500050005000500040004400400044006000600060006000400040004000400050005000500050002000220020002e004000440040004400500050005000500060006000600060003000330030003d00400044004000440050005000500050006000600060006000222220302200c100ba00910087004400440044004400550055005500550066006600660066002230000022200000)
  · decide +kernel
  · exact familyCons vB217 <| familyCons vB221 <| familyCons vB222 <| familyCons vB225 <| familyCons vB230 <| familyCons vB231 <| familyNil
  · exact familyCons vB245n3 <| familyCons vB245n6 <| familyCons vB245n7 <| familyCons vB245n8 <| familyCons vB245n11 <| familyCons vB245n12 <| familyCons vB245n15 <| familyCons vB245n17 <| familyNil
  · decide +kernel
  · decide +kernel
def B245n19 : Cell := (8, [0x3300000033000000330000003300, 0x3333000033330000333300003333, 0xff000000ff000000ff000000ff, 0x5555000055550000555500005555, 0xf0f00000f0f00000f0f00000f0f, 0xffff000000000000ffff, 0xffff0000ffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB245n19 : B245n19.2.Nodup ∧ Closed B245.mask B245.goal B245n19 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 7) (bs := [B217, B221, B222, B225, B230, B231]) (seen := []) (h := [(0x3300000033000000330000003300, 0x3333000033330000333300003333, 0xff000000ff000000ff000000ff)]) (width := 3) (p := 0x800800800800a00a00a00a00800900800900c00c00c00c00800800800800a00a00a00a00400480400480800900800900a00a00a00a00c00c00c00c00600600600600800800800800a00a00a00a00c00d80c00d80410490480440480440480900900900900b40b40b40b40d80d80d80d80490000490000)
  · decide +kernel
  · exact familyCons vB217 <| familyCons vB221 <| familyCons vB222 <| familyCons vB225 <| familyCons vB230 <| familyCons vB231 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B245n20 : Cell := (8, [0xcc000000cc000000cc000000cc, 0x3333000033330000333300003333, 0xff000000ff000000ff000000ff, 0x5555000055550000555500005555, 0xf0f00000f0f00000f0f00000f0f, 0xffff000000000000ffff, 0xffff0000ffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB245n20 : B245n20.2.Nodup ∧ Closed B245.mask B245.goal B245n20 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 7) (bs := [B217, B221, B222, B225, B230, B231]) (seen := []) (h := [(0xcc000000cc000000cc000000cc, 0x3333000033330000333300003333, 0xff000000ff000000ff000000ff)]) (width := 3) (p := 0x800800800800a00a00a00a00800900800900c00c00c00c00800800800800a00a00a00a00400400400400800800800800a00a00a00a00c00d80c00d806006c06006c0800900800900a00a00a00a00c00c00c00c004804904186406c06406c0900900900900b40b40b40b40d80d80d80d80498000490000)
  · decide +kernel
  · exact familyCons vB217 <| familyCons vB221 <| familyCons vB222 <| familyCons vB225 <| familyCons vB230 <| familyCons vB231 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B245n21 : Cell := (8, [0x33ff000033ff000033ff000033ff, 0x3333000033330000333300003333, 0xff000000ff000000ff000000ff, 0x5555000055550000555500005555, 0xf0f00000f0f00000f0f00000f0f, 0xffff000000000000ffff, 0xffff0000ffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB245n21 : B245n21.2.Nodup ∧ Closed B245.mask B245.goal B245n21 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 7) (bs := [B217, B221, B222, B225, B230, B231]) (seen := []) (h := [(0x33ff000033ff000033ff000033ff, 0x3333000033330000333300003333, 0xff000000ff000000ff000000ff)]) (width := 3) (p := 0x800800800800a00a00a00a00800900800900c00c00c00c00800800800800a00a00a00a00400400400400800800800800a00a00a00a00c00d80c00d80600600600600800800800800a00a00a00a00c00d80c00d80480410492440480451492900900924912b40b40b6db52d80d80db6d92000490000490)
  · decide +kernel
  · exact familyCons vB217 <| familyCons vB221 <| familyCons vB222 <| familyCons vB225 <| familyCons vB230 <| familyCons vB231 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B245n22 : Cell := (6, [0x3333000033330000330000003300, 0x333300003333, 0xff000000ff000000ff000000ff, 0xffff0000ffff, 0x5555000055550000555500005555, 0xf0f00000f0f00000f0f00000f0f, 0xffff000000000000ffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB245n22 : B245n22.2.Nodup ∧ Closed B245.mask B245.goal B245n22 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B225]) (seen := []) (h := [(0x3333000033330000330000003300, 0x3300000033, 0x3333000033330000333300003333), (0x3300000033, 0x333300003333, 0xff000000ff000000ff000000ff), (0x333300003333, 0x3333000033330000333300003333, 0xffff0000ffff)]) (width := 1) (p := 0x1000)
  · decide +kernel
  · exact familyCons vB225 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B245n23 : Cell := (6, [0xffcc0000ffcc, 0x333300003333, 0xff000000ff000000ff000000ff, 0x3333000033330000333300003333, 0x5555000055550000555500005555, 0xf0f00000f0f00000f0f00000f0f, 0xffff000000000000ffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB245n23 : B245n23.2.Nodup ∧ Closed B245.mask B245.goal B245n23 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B225]) (seen := []) (h := [(0xffcc0000ffcc, 0x3300000033, 0xffff0000ffff), (0x3300000033, 0x333300003333, 0xff000000ff000000ff000000ff), (0x333300003333, 0x3333000033330000333300003333, 0xffff0000ffff)]) (width := 1) (p := 0x1000)
  · decide +kernel
  · exact familyCons vB225 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B245n24 : Cell := (7, [0x3300000033, 0x333300003333, 0xff000000ff000000ff000000ff, 0x3333000033330000333300003333, 0xffff0000ffff, 0x5555000055550000555500005555, 0xf0f00000f0f00000f0f00000f0f, 0xffff000000000000ffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB245n24 : B245n24.2.Nodup ∧ Closed B245.mask B245.goal B245n24 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 6) (bs := [B221]) (seen := [B245n2, B245n22, B245n23]) (h := [(0x3300000033, 0x333300003333, 0xff000000ff000000ff000000ff), (0x333300003333, 0x3333000033330000333300003333, 0xffff0000ffff)]) (width := 3) (p := 0x1002000000000000000000000000000000000000000004000003000000000001000)
  · decide +kernel
  · exact familyCons vB221 <| familyNil
  · exact familyCons vB245n2 <| familyCons vB245n22 <| familyCons vB245n23 <| familyNil
  · decide +kernel
  · decide +kernel
def B245n25 : Cell := (7, [0x330000003300, 0x333300003333, 0xff000000ff000000ff000000ff, 0x3333000033330000333300003333, 0xffff0000ffff, 0x5555000055550000555500005555, 0xf0f00000f0f00000f0f00000f0f, 0xffff000000000000ffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB245n25 : B245n25.2.Nodup ∧ Closed B245.mask B245.goal B245n25 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 6) (bs := [B221]) (seen := []) (h := [(0x330000003300, 0x333300003333, 0xff000000ff000000ff000000ff), (0x333300003333, 0x3333000033330000333300003333, 0xffff0000ffff)]) (width := 1) (p := 0x11000000000000010100010)
  · decide +kernel
  · exact familyCons vB221 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B245n26 : Cell := (7, [0xff000000ff000000cc000000cc, 0xff000000ff000000ff000000ff, 0x3333000033330000333300003333, 0xffff0000ffff, 0x5555000055550000555500005555, 0xf0f00000f0f00000f0f00000f0f, 0xffff000000000000ffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB245n26 : B245n26.2.Nodup ∧ Closed B245.mask B245.goal B245n26 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 6) (bs := [B217, B221, B222, B225, B230, B231]) (seen := [B245n2]) (h := [(0xff000000ff000000cc000000cc, 0x333300003333, 0xff000000ff000000ff000000ff), (0x333300003333, 0x3333000033330000333300003333, 0xffff0000ffff)]) (width := 3) (p := 0x1000001000000000000000000000000000001000001000000000000000000000000000001000001000000000000000000000000000000000000001000001000000000000000000001800001800000400000400000800000c01001001001001401401401401801801801800400400400400800400400400b8000)
  · decide +kernel
  · exact familyCons vB217 <| familyCons vB221 <| familyCons vB222 <| familyCons vB225 <| familyCons vB230 <| familyCons vB231 <| familyNil
  · exact familyCons vB245n2 <| familyNil
  · decide +kernel
  · decide +kernel
def B245n27 : Cell := (6, [0xff000000ff, 0xff000000ff000000cc000000cc, 0x333300003333, 0x3333000033330000333300003333, 0x5555000055550000555500005555, 0xf0f00000f0f00000f0f00000f0f, 0xffff000000000000ffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB245n27 : B245n27.2.Nodup ∧ Closed B245.mask B245.goal B245n27 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B217]) (seen := []) (h := [(0xff000000ff, 0xff000000ff000000ff000000ff, 0xffff0000ffff), (0xff000000ff000000cc000000cc, 0x333300003333, 0xff000000ff000000ff000000ff), (0x333300003333, 0x3333000033330000333300003333, 0xffff0000ffff)]) (width := 1) (p := 0x100000000000000000000000000)
  · decide +kernel
  · exact familyCons vB217 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B245n28 : Cell := (7, [0xff000000ff000000cc000000cc, 0x333300003333, 0xff000000ff000000ff000000ff, 0x3333000033330000333300003333, 0xffff0000ffff, 0x5555000055550000555500005555, 0xf0f00000f0f00000f0f00000f0f, 0xffff000000000000ffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB245n28 : B245n28.2.Nodup ∧ Closed B245.mask B245.goal B245n28 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 6) (bs := [B217, B221, B222]) (seen := [B245n2, B245n13, B245n27]) (h := [(0xff000000ff000000cc000000cc, 0x333300003333, 0xff000000ff000000ff000000ff), (0x333300003333, 0x3333000033330000333300003333, 0xffff0000ffff)]) (width := 3) (p := 0x6000000000005000000000000000000000000000000000000000000000000000002004000000000000000000000000000000000000000000001003000000001001000000002000)
  · decide +kernel
  · exact familyCons vB217 <| familyCons vB221 <| familyCons vB222 <| familyNil
  · exact familyCons vB245n2 <| familyCons vB245n13 <| familyCons vB245n27 <| familyNil
  · decide +kernel
  · decide +kernel
def B245n29 : Cell := (7, [0xff000000ff000033ff000033ff, 0x333300003333, 0xff000000ff000000ff000000ff, 0x3333000033330000333300003333, 0xffff0000ffff, 0x5555000055550000555500005555, 0xf0f00000f0f00000f0f00000f0f, 0xffff000000000000ffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB245n29 : B245n29.2.Nodup ∧ Closed B245.mask B245.goal B245n29 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 6) (bs := [B217, B221, B225, B230, B231]) (seen := []) (h := [(0xff000000ff000033ff000033ff, 0x333300003333, 0xff000000ff000000ff000000ff), (0x333300003333, 0x3333000033330000333300003333, 0xffff0000ffff)]) (width := 3) (p := 0x2000000000002000000000000000000000000000000000000000000000000000002002000000003002000000004002000000005002000000001002000000002001000000000002)
  · decide +kernel
  · exact familyCons vB217 <| familyCons vB221 <| familyCons vB225 <| familyCons vB230 <| familyCons vB231 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B245n30 : Cell := (6, [0x3333000033330000330000003300, 0xff000000ff, 0xff000000ff000000ff000000ff, 0x333300003333, 0x5555000055550000555500005555, 0xf0f00000f0f00000f0f00000f0f, 0xffff000000000000ffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB245n30 : B245n30.2.Nodup ∧ Closed B245.mask B245.goal B245n30 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B217]) (seen := []) (h := [(0x3333000033330000330000003300, 0xff000000ff, 0x3333000033330000333300003333), (0xff000000ff, 0xffff0000ffff, 0xff000000ff000000ff000000ff), (0x333300003333, 0x3333000033330000333300003333, 0xffff0000ffff)]) (width := 1) (p := 0x100)
  · decide +kernel
  · exact familyCons vB217 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B245n31 : Cell := (7, [0xff000000ff, 0xff000000ff000000ff000000ff, 0x333300003333, 0x3333000033330000333300003333, 0x5555000055550000555500005555, 0xf0f00000f0f00000f0f00000f0f, 0xffff000000000000ffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB245n31 : B245n31.2.Nodup ∧ Closed B245.mask B245.goal B245n31 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 6) (bs := [B217, B221, B222, B225, B230, B231]) (seen := [B245n14, B245n27, B245n30]) (h := [(0xff000000ff, 0xffff0000ffff, 0xff000000ff000000ff000000ff), (0x333300003333, 0x3333000033330000333300003333, 0xffff0000ffff)]) (width := 4) (p := 0x400000004000000000000000000000000000000000000000400000004000000050000000500000006000000060000000400000004000000000000000000000000000000000001100000000004000000040000000500000005000000060000000600000002000020032702200020080000000000040000000400000000000000000000000000000000000330009003000000022200200300000001100000)
  · decide +kernel
  · exact familyCons vB217 <| familyCons vB221 <| familyCons vB222 <| familyCons vB225 <| familyCons vB230 <| familyCons vB231 <| familyNil
  · exact familyCons vB245n14 <| familyCons vB245n27 <| familyCons vB245n30 <| familyNil
  · decide +kernel
  · decide +kernel
def B245n32 : Cell := (8, [0x333300003333, 0x3333000033330000333300003333, 0xffff0000ffff, 0x5555000055550000555500005555, 0xf0f00000f0f00000f0f00000f0f, 0xff000000ff000000ff000000ff, 0xffff000000000000ffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB245n32 : B245n32.2.Nodup ∧ Closed B245.mask B245.goal B245n32 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 7) (bs := [B217, B221, B222, B225, B230, B231]) (seen := [B245n3, B245n15, B245n24, B245n25, B245n26, B245n28, B245n29, B245n31]) (h := [(0x333300003333, 0x3333000033330000333300003333, 0xffff0000ffff)]) (width := 4) (p := 0x40004000400040004000440040004400500050005000500040004000400040006000600060006000500050005000500040004400400044001000110010001e005000500050005000600060006000600040004400400044003000330030003800500055005000550060006600600066001110103011004400440044004400d200cb00a2009700550055005500550066006600660066001130000011100000)
  · decide +kernel
  · exact familyCons vB217 <| familyCons vB221 <| familyCons vB222 <| familyCons vB225 <| familyCons vB230 <| familyCons vB231 <| familyNil
  · exact familyCons vB245n3 <| familyCons vB245n15 <| familyCons vB245n24 <| familyCons vB245n25 <| familyCons vB245n26 <| familyCons vB245n28 <| familyCons vB245n29 <| familyCons vB245n31 <| familyNil
  · decide +kernel
  · decide +kernel
def B245n33 : Cell := (8, [0x3333000033330000000000000000, 0x3333000033330000333300003333, 0xffff0000ffff, 0x5555000055550000555500005555, 0xf0f00000f0f00000f0f00000f0f, 0xff000000ff000000ff000000ff, 0xffff000000000000ffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB245n33 : B245n33.2.Nodup ∧ Closed B245.mask B245.goal B245n33 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 7) (bs := [B217, B222, B225, B230, B231]) (seen := []) (h := [(0x3333000033330000000000000000, 0x3333000033330000333300003333, 0xffff0000ffff)]) (width := 3) (p := 0x6006006006006006c06006c0800800800800600600600600a00a00a00a008008008008006006c06006c0200240200240800800800800a00a00a00a00600600600600400400400400800800800800a00a00a00a002082482406c06c06c06c0240240240240900900900900b40b40b40b40248000248000)
  · decide +kernel
  · exact familyCons vB217 <| familyCons vB222 <| familyCons vB225 <| familyCons vB230 <| familyCons vB231 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B245n34 : Cell := (8, [0xcccc0000cccc, 0x3333000033330000333300003333, 0xffff0000ffff, 0x5555000055550000555500005555, 0xf0f00000f0f00000f0f00000f0f, 0xff000000ff000000ff000000ff, 0xffff000000000000ffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB245n34 : B245n34.2.Nodup ∧ Closed B245.mask B245.goal B245n34 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 7) (bs := [B217, B221, B222, B225, B230, B231]) (seen := []) (h := [(0xcccc0000cccc, 0x3333000033330000333300003333, 0xffff0000ffff)]) (width := 3) (p := 0x800800800800800900800900a00a00a00a00800800800800c00c00c00c00a00a00a00a00800800800800200200200200a00a00a00a00c00c00c00c008009008009006006c06006c0a00b40a00b40c00d80c00d802402482189009009009006806c06806c0b40b40b40b40d80d80d80d80258000248000)
  · decide +kernel
  · exact familyCons vB217 <| familyCons vB221 <| familyCons vB222 <| familyCons vB225 <| familyCons vB230 <| familyCons vB231 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B245n35 : Cell := (8, [0x3333000033330000ffff0000ffff, 0x3333000033330000333300003333, 0xffff0000ffff, 0x5555000055550000555500005555, 0xf0f00000f0f00000f0f00000f0f, 0xff000000ff000000ff000000ff, 0xffff000000000000ffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB245n35 : B245n35.2.Nodup ∧ Closed B245.mask B245.goal B245n35 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 7) (bs := [B217, B222, B225, B230, B231]) (seen := []) (h := [(0x3333000033330000ffff0000ffff, 0x3333000033330000333300003333, 0xffff0000ffff)]) (width := 3) (p := 0x6006006006006006c06006c0800800800800600600600600a00a00a00a00800800800800600600600600200200200200800800800800a00a00a00a00600600600600400400400400800800800800a00a00a00a002402082486c06c06db6c9240240249249900900924909b40b40b6db49000248000248)
  · decide +kernel
  · exact familyCons vB217 <| familyCons vB222 <| familyCons vB225 <| familyCons vB230 <| familyCons vB231 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B245n36 : Cell := (6, [0xff000000ff000000cc000000cc, 0xff000000ff, 0x3333000033330000333300003333, 0xffff0000ffff, 0x5555000055550000555500005555, 0xf0f00000f0f00000f0f00000f0f, 0xffff000000000000ffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB245n36 : B245n36.2.Nodup ∧ Closed B245.mask B245.goal B245n36 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B225]) (seen := []) (h := [(0xff000000ff000000cc000000cc, 0x3300000033, 0xff000000ff000000ff000000ff), (0x3300000033, 0xff000000ff, 0x3333000033330000333300003333), (0xff000000ff, 0xff000000ff000000ff000000ff, 0xffff0000ffff)]) (width := 1) (p := 0x1000)
  · decide +kernel
  · exact familyCons vB225 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B245n37 : Cell := (6, [0xffcc0000ffcc, 0xff000000ff, 0x3333000033330000333300003333, 0xff000000ff000000ff000000ff, 0x5555000055550000555500005555, 0xf0f00000f0f00000f0f00000f0f, 0xffff000000000000ffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB245n37 : B245n37.2.Nodup ∧ Closed B245.mask B245.goal B245n37 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 5) (bs := [B225]) (seen := []) (h := [(0xffcc0000ffcc, 0x3300000033, 0xffff0000ffff), (0x3300000033, 0xff000000ff, 0x3333000033330000333300003333), (0xff000000ff, 0xff000000ff000000ff000000ff, 0xffff0000ffff)]) (width := 1) (p := 0x1000)
  · decide +kernel
  · exact familyCons vB225 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B245n38 : Cell := (7, [0x3300000033, 0xff000000ff, 0x3333000033330000333300003333, 0xff000000ff000000ff000000ff, 0xffff0000ffff, 0x5555000055550000555500005555, 0xf0f00000f0f00000f0f00000f0f, 0xffff000000000000ffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB245n38 : B245n38.2.Nodup ∧ Closed B245.mask B245.goal B245n38 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 6) (bs := [B222]) (seen := [B245n1, B245n36, B245n37]) (h := [(0x3300000033, 0xff000000ff, 0x3333000033330000333300003333), (0xff000000ff, 0xff000000ff000000ff000000ff, 0xffff0000ffff)]) (width := 3) (p := 0x1002000000000000000000000000000000000000000004000003000000000001000)
  · decide +kernel
  · exact familyCons vB222 <| familyNil
  · exact familyCons vB245n1 <| familyCons vB245n36 <| familyCons vB245n37 <| familyNil
  · decide +kernel
  · decide +kernel
def B245n39 : Cell := (7, [0xcc000000cc, 0xff000000ff, 0x3333000033330000333300003333, 0xff000000ff000000ff000000ff, 0xffff0000ffff, 0x5555000055550000555500005555, 0xf0f00000f0f00000f0f00000f0f, 0xffff000000000000ffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB245n39 : B245n39.2.Nodup ∧ Closed B245.mask B245.goal B245n39 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 6) (bs := [B222]) (seen := []) (h := [(0xcc000000cc, 0xff000000ff, 0x3333000033330000333300003333), (0xff000000ff, 0xff000000ff000000ff000000ff, 0xffff0000ffff)]) (width := 1) (p := 0x11000000000000010100010)
  · decide +kernel
  · exact familyCons vB222 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B245n40 : Cell := (7, [0x3333000033330000330000003300, 0x3333000033330000333300003333, 0xff000000ff000000ff000000ff, 0xffff0000ffff, 0x5555000055550000555500005555, 0xf0f00000f0f00000f0f00000f0f, 0xffff000000000000ffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB245n40 : B245n40.2.Nodup ∧ Closed B245.mask B245.goal B245n40 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 6) (bs := [B217, B221, B222, B225, B230, B231]) (seen := [B245n1]) (h := [(0x3333000033330000330000003300, 0xff000000ff, 0x3333000033330000333300003333), (0xff000000ff, 0xff000000ff000000ff000000ff, 0xffff0000ffff)]) (width := 3) (p := 0x1000001000000000000000000000000000001000001000000000000000000000000000001000001000000000000000000000000000000000000001000001000000000000000000001800001800000400000400000800000801001001001001401401401401801801801800400400400400800400400400f8000)
  · decide +kernel
  · exact familyCons vB217 <| familyCons vB221 <| familyCons vB222 <| familyCons vB225 <| familyCons vB230 <| familyCons vB231 <| familyNil
  · exact familyCons vB245n1 <| familyNil
  · decide +kernel
  · decide +kernel
def B245n41 : Cell := (7, [0x3333000033330000330000003300, 0xff000000ff, 0x3333000033330000333300003333, 0xff000000ff000000ff000000ff, 0xffff0000ffff, 0x5555000055550000555500005555, 0xf0f00000f0f00000f0f00000f0f, 0xffff000000000000ffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB245n41 : B245n41.2.Nodup ∧ Closed B245.mask B245.goal B245n41 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 6) (bs := [B217, B221, B222]) (seen := [B245n1, B245n16, B245n30]) (h := [(0x3333000033330000330000003300, 0xff000000ff, 0x3333000033330000333300003333), (0xff000000ff, 0xff000000ff000000ff000000ff, 0xffff0000ffff)]) (width := 3) (p := 0x6000000000005000000000000000000000000000000000000000000000000000003004000000000000000000000000000000000000000000001002000000001001000000003000)
  · decide +kernel
  · exact familyCons vB217 <| familyCons vB221 <| familyCons vB222 <| familyNil
  · exact familyCons vB245n1 <| familyCons vB245n16 <| familyCons vB245n30 <| familyNil
  · decide +kernel
  · decide +kernel
def B245n42 : Cell := (7, [0x333300003333000033ff000033ff, 0xff000000ff, 0x3333000033330000333300003333, 0xff000000ff000000ff000000ff, 0xffff0000ffff, 0x5555000055550000555500005555, 0xf0f00000f0f00000f0f00000f0f, 0xffff000000000000ffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB245n42 : B245n42.2.Nodup ∧ Closed B245.mask B245.goal B245n42 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 6) (bs := [B217, B221, B222, B225, B230, B231]) (seen := []) (h := [(0x333300003333000033ff000033ff, 0xff000000ff, 0x3333000033330000333300003333), (0xff000000ff, 0xff000000ff000000ff000000ff, 0xffff0000ffff)]) (width := 3) (p := 0x3000000000003000000000000000000000000000000000000000000000000000003003000000004003000000005003000000006003000000001002000000002001000000000003)
  · decide +kernel
  · exact familyCons vB217 <| familyCons vB221 <| familyCons vB222 <| familyCons vB225 <| familyCons vB230 <| familyCons vB231 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B245n43 : Cell := (8, [0xff000000ff, 0xff000000ff000000ff000000ff, 0xffff0000ffff, 0x5555000055550000555500005555, 0x3333000033330000333300003333, 0xf0f00000f0f00000f0f00000f0f, 0xffff000000000000ffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB245n43 : B245n43.2.Nodup ∧ Closed B245.mask B245.goal B245n43 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 7) (bs := [B217, B221, B222, B225, B230, B231]) (seen := [B245n3, B245n17, B245n31, B245n38, B245n39, B245n40, B245n41, B245n42]) (h := [(0xff000000ff, 0xff000000ff000000ff000000ff, 0xffff0000ffff)]) (width := 4) (p := 0x4000440040004400400040004000400050005000500050004000400040004000500050005000500060006000600060004000440040004400500050005000500010001100100019006000600060006000400044004000440050005500500055002000220020002800600066006000660011101020110044004400440044005500550055005500e300dc00b300a70066006600660066001120000011100000)
  · decide +kernel
  · exact familyCons vB217 <| familyCons vB221 <| familyCons vB222 <| familyCons vB225 <| familyCons vB230 <| familyCons vB231 <| familyNil
  · exact familyCons vB245n3 <| familyCons vB245n17 <| familyCons vB245n31 <| familyCons vB245n38 <| familyCons vB245n39 <| familyCons vB245n40 <| familyCons vB245n41 <| familyCons vB245n42 <| familyNil
  · decide +kernel
  · decide +kernel
def B245n44 : Cell := (8, [0xff000000ff0000000000000000, 0xff000000ff000000ff000000ff, 0xffff0000ffff, 0x5555000055550000555500005555, 0x3333000033330000333300003333, 0xf0f00000f0f00000f0f00000f0f, 0xffff000000000000ffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB245n44 : B245n44.2.Nodup ∧ Closed B245.mask B245.goal B245n44 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 7) (bs := [B217, B221, B225, B230, B231]) (seen := []) (h := [(0xff000000ff0000000000000000, 0xff000000ff000000ff000000ff, 0xffff0000ffff)]) (width := 3) (p := 0x6006c06006c0600600600600800800800800600600600600800800800800a00a00a00a006006c06006c0800800800800200240200240a00a00a00a00600600600600800800800800400400400400a00a00a00a002082482406c06c06c06c0900900900900240240240240b40b40b40b40248000248000)
  · decide +kernel
  · exact familyCons vB217 <| familyCons vB221 <| familyCons vB225 <| familyCons vB230 <| familyCons vB231 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B245n45 : Cell := (8, [0xff000000ff00, 0xff000000ff000000ff000000ff, 0xffff0000ffff, 0x5555000055550000555500005555, 0x3333000033330000333300003333, 0xf0f00000f0f00000f0f00000f0f, 0xffff000000000000ffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB245n45 : B245n45.2.Nodup ∧ Closed B245.mask B245.goal B245n45 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 7) (bs := [B217, B221, B225, B230, B231]) (seen := []) (h := [(0xff000000ff00, 0xff000000ff000000ff000000ff, 0xffff0000ffff)]) (width := 3) (p := 0x6006c06006c0600600600600800800800800600600600600800800800800a00a00a00a00600600600600800800800800200200200200a00a00a00a006006c06006c0800900800900400480400480a00b40a00b402402482106c06c06c06c0900900900900480480480480b40b40b40b40250000248000)
  · decide +kernel
  · exact familyCons vB217 <| familyCons vB221 <| familyCons vB225 <| familyCons vB230 <| familyCons vB231 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B245n46 : Cell := (8, [0xff000000ff0000ffff0000ffff, 0xff000000ff000000ff000000ff, 0xffff0000ffff, 0x5555000055550000555500005555, 0x3333000033330000333300003333, 0xf0f00000f0f00000f0f00000f0f, 0xffff000000000000ffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB245n46 : B245n46.2.Nodup ∧ Closed B245.mask B245.goal B245n46 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 7) (bs := [B217, B221, B225, B230, B231]) (seen := []) (h := [(0xff000000ff0000ffff0000ffff, 0xff000000ff000000ff000000ff, 0xffff0000ffff)]) (width := 3) (p := 0x6006c06006c0600600600600800800800800600600600600800800800800a00a00a00a00600600600600800800800800200200200200a00a00a00a00600600600600800800800800400400400400a00a00a00a002402082486c06c06db6c9900900924909240240249249b40b40b6db49000248000248)
  · decide +kernel
  · exact familyCons vB217 <| familyCons vB221 <| familyCons vB225 <| familyCons vB230 <| familyCons vB231 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
def B245n47 : Cell := (9, [0x5555000055550000555500005555, 0x3333000033330000333300003333, 0xf0f00000f0f00000f0f00000f0f, 0xff000000ff000000ff000000ff, 0xffff000000000000ffff, 0xffff0000ffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB245n47 : B245n47.2.Nodup ∧ Closed B245.mask B245.goal B245n47 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 8) (bs := [B225, B230, B231]) (seen := [B245n18, B245n19, B245n20, B245n21, B245n32, B245n33, B245n34, B245n35, B245n43, B245n44, B245n45, B245n46]) (h := []) (width := 4) (p := 0x1000100010001000f000e000d000c0001000100010001000200020002000200010001100100011002000200020002000b000a0009000800010001000100010007000600050004000200020002000200030003000300030001000100010001000300030003000300020002000200020003000300030003000)
  · decide +kernel
  · exact familyCons vB225 <| familyCons vB230 <| familyCons vB231 <| familyNil
  · exact familyCons vB245n18 <| familyCons vB245n19 <| familyCons vB245n20 <| familyCons vB245n21 <| familyCons vB245n32 <| familyCons vB245n33 <| familyCons vB245n34 <| familyCons vB245n35 <| familyCons vB245n43 <| familyCons vB245n44 <| familyCons vB245n45 <| familyCons vB245n46 <| familyNil
  · decide +kernel
  · decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB245 : Valid B245 := by
  apply small_bound (bs := []) (seen := [B245n47]) (width := 1) (p := 0x40000000000000000000000000000000)
  · decide +kernel
  · exact familyNil
  · exact familyCons vB245n47 <| familyNil
  · decide +kernel
  · apply canon_checked; decide +kernel
  · decide +kernel
end PEqualNP.Outside.L_meta_10626.SignedCert.GraphB

namespace PEqualNP.Outside.L_meta_10626.SignedCert.GraphB
def B246 : Bound := ⟨0xff00ff00ff00ff00ff00ff00ff00ff, [0x0, 0x550055005500550055005500550055, 0x330033003300330033003300330033, 0xf000f000f000f000f000f000f000f, 0xff000000ff000000ff000000ff, 0xff00ff0000000000ff00ff, 0xff00ff00ff00ff], 0x1000100110005005f, 10⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB246 : Valid B246 := by
  apply transfer vB245 0xef5f9d3eb578d1cf1f1c3cb170c10000000000000000000000000000ed5b952e953850cd1b142c91304000000000000000000000000000006e5d9936a558914e1d1834a1508100000000000000000000000000006c5991268518104c191024811000 <;> decide +kernel
end PEqualNP.Outside.L_meta_10626.SignedCert.GraphB

namespace PEqualNP.Outside.L_meta_10626.SignedCert.GraphB
def B247 : Bound := ⟨0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, [0x0, 0x5050505050505050505050505050505, 0x3030303030303030303030303030303, 0xf000f000f000f000f000f000f000f, 0xf0f00000f0f00000f0f00000f0f, 0xf0f0f0f000000000f0f0f0f, 0xf0f0f0f0f0f0f0f], 0x1000100010105030f, 10⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB247 : Valid B247 := by
  apply transfer vB245 0xf7ebcf8d7ab4e8e7cb8f0c78b0e00000000000000000000000000000b76acd8972a4c8a74a8d0870a0c0000000000000000000000000000076e9cb856a94a866c98b046890a000000000000000000000000000003668c98162848826488900608080 <;> decide +kernel
end PEqualNP.Outside.L_meta_10626.SignedCert.GraphB

namespace PEqualNP.Outside.L_meta_10626.SignedCert.GraphB
def B248 : Bound := ⟨0x33333333333333333333333333333333, [0x0, 0x11111111111111111111111111111111, 0x3030303030303030303030303030303, 0x330033003300330033003300330033, 0x3333000033330000333300003333, 0x333333330000000033333333, 0x3333333333333333], 0x10001001101011313, 10⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB248 : Valid B248 := by
  apply transfer vB245 0xfb77cd9eb578d1db374c9cb170c10000000000000000000000000000f973c58e953850d933448c91304000000000000000000000000000007a75c996a558915a354894a1508100000000000000000000000000007871c18685181058314084811000 <;> decide +kernel
end PEqualNP.Outside.L_meta_10626.SignedCert.GraphB

namespace PEqualNP.Outside.L_meta_10626.SignedCert.GraphB
def B249 : Bound := ⟨0x55555555555555555555555555555555, [0x0, 0x11111111111111111111111111111111, 0x5050505050505050505050505050505, 0x550055005500550055005500550055, 0x5555000055550000555500005555, 0x555555550000000055555555, 0x5555555555555555], 0x10001001101051155, 10⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vB249 : Valid B249 := by
  apply transfer vB244 0xfdf3d78edd3970ddb3568cd93160bd72d58ad529509d325488d12140000000000000000000000000000000000000000000000000000000007cf1d386cd19305cb15284c911203c70d182c509101c305080c10100 <;> decide +kernel
end PEqualNP.Outside.L_meta_10626.SignedCert.GraphB

namespace PEqualNP.Outside.L_meta_10626.SignedCert.GraphB
def rootBn0 : Cell := (11, [0x55555555555555555555555555555555, 0x33333333333333333333333333333333, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, 0xff00ff00ff00ff00ff00ff00ff00ff, 0xffff0000ffff0000ffff0000ffff, 0xffffffff00000000ffffffff, 0xffffffffffffffff])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vrootBn0 : rootBn0.2.Nodup ∧ Closed rootB.mask rootB.goal rootBn0 := by
  refine ⟨by decide +kernel, ?_⟩
  apply small_cell (k := 10) (bs := [B244, B245, B246, B247, B248, B249]) (seen := []) (h := []) (width := 3) (p := 0x200200200200400400400400200200200200600600600600200200200200400400400400800800800800200200200200400400400400600600600600a00a00a00a00200200200200400400400400600600600600800800800800c00c00c00c00200200200200400400400400600600600600800800800800a00a00a00a00)
  · decide +kernel
  · exact familyCons vB244 <| familyCons vB245 <| familyCons vB246 <| familyCons vB247 <| familyCons vB248 <| familyCons vB249 <| familyNil
  · exact familyNil
  · decide +kernel
  · decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem vrootB : Valid rootB := by
  apply small_bound (bs := []) (seen := [rootBn0]) (width := 1) (p := 0x4000000000000000000000000000000000000000000000000000000000000000)
  · decide +kernel
  · exact familyNil
  · exact familyCons vrootBn0 <| familyNil
  · decide +kernel
  · apply canon_checked; decide +kernel
  · decide +kernel
end PEqualNP.Outside.L_meta_10626.SignedCert.GraphB

namespace PEqualNP.Outside.L_meta_10626.CircuitWitness
open PEqualNP.CircuitLowerBounds

def gates : List Gate := [
  ⟨.or, [2, 5]⟩,
  ⟨.or, [4, 7]⟩,
  ⟨.and, [2, 4]⟩,
  ⟨.or, [6, 9]⟩,
  ⟨.or, [0, 10]⟩,
  ⟨.and, [8, 11]⟩,
  ⟨.and, [1, 3]⟩,
  ⟨.or, [12, 13]⟩,
  ⟨.or, [0, 1]⟩,
  ⟨.or, [3, 15]⟩,
  ⟨.or, [5, 6]⟩,
  ⟨.and, [16, 17]⟩,
  ⟨.or, [14, 18]⟩]

theorem size : gates.length = 13 := rfl

theorem legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [gates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem computes : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates, 19⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  decide +kernel

end PEqualNP.Outside.L_meta_10626.CircuitWitness

theorem PEqualNP.Outside.L_meta_10626 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fits _ computes
  by_cases hasNot : ∃ g ∈ gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : PEqualNP.Outside.L_meta_10626.SignedCert.Source.binaryCost gates < gates.length :=
      (List.length_filter_lt_length_iff_exists (p := PEqualNP.Outside.L_meta_10626.SignedCert.Source.isBinary)).mpr
        ⟨g, mem, by simp [PEqualNP.Outside.L_meta_10626.SignedCert.Source.isBinary, op]⟩
    have hb := PEqualNP.Outside.L_meta_10626.SignedCert.GraphB.size_lb PEqualNP.Outside.L_meta_10626.SignedCert.GraphB.vrootB gates o (fun g hg => fits g hg) (fun x => (computes x).trans (PEqualNP.Outside.L_meta_10626.SignedCert.GraphB.edge_eq x))
    have hl : PEqualNP.Outside.L_meta_10626.CircuitWitness.gates.length = 13 := rfl
    exact ⟨PEqualNP.Outside.L_meta_10626.CircuitWitness.gates, 19, PEqualNP.Outside.L_meta_10626.CircuitWitness.legal, by omega, PEqualNP.Outside.L_meta_10626.CircuitWitness.computes⟩
  · refine ⟨gates, o, fun g hg => ⟨?_, (fits g hg).2⟩, le_refl _, computes⟩
    rcases (fits g hg).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hasNot ⟨g, hg, h⟩).elim
