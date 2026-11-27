import Mathlib.Data.Nat.Notation



namespace PEqualNP.Outside.L_meta_7737.Core
abbrev Op := Bool × Nat × Nat
def baseWords : List (BitVec 58) := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752]
def step (ws : List (BitVec 58)) (g : Op) : List (BitVec 58) :=
  ws ++ [if g.1 = true then ws.getD g.2.1 0 &&& ws.getD g.2.2 0 else
    ws.getD g.2.1 0 ||| ws.getD g.2.2 0]

end PEqualNP.Outside.L_meta_7737.Core

namespace PEqualNP.Outside.L_meta_7737.DAG
abbrev Word := BitVec 58
theorem in_getD {X : Type} (P : X → Prop) {xs : List X} {d : X} (h : ∀ x ∈ xs, P x)
    (hd : P d) (i : Nat) : P (xs.getD i d) := by
  induction xs generalizing i with
  | nil => exact hd
  | cons a xs ih =>
    cases i with
    | zero => exact h a (by simp)
    | succ i => exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) i

def MaskOK (w : Word) := w &&& (288230376149614591 : Word) = 2097151
theorem bits_of_mask {w} (h : MaskOK w) :
    (∀ i, i < 21 → w.getLsbD i = true) ∧ (∀ j, j < 36 → w.getLsbD (22+j) = false) := by
  have bit (k : Nat) := congrArg (fun x : Word => x.getLsbD k) h
  have yy : ∀ i : Fin 21, (288230376149614591 : Word).getLsbD i.val = true ∧
    (2097151 : Word).getLsbD i.val = true := by decide +kernel
  have nn : ∀ j : Fin 36, (288230376149614591 : Word).getLsbD (22+j.val) = true ∧
    (2097151 : Word).getLsbD (22+j.val) = false := by decide +kernel
  constructor
  · intro i hi
    have mh : (288230376149614591 : Word).getLsbD i = true := (yy ⟨i,hi⟩).1
    have th : (2097151 : Word).getLsbD i = true := (yy ⟨i,hi⟩).2
    simpa only [BitVec.getLsbD_and, mh, th, Bool.and_true] using bit i
  · intro j hj
    have mh : (288230376149614591 : Word).getLsbD (22+j) = true := (nn ⟨j,hj⟩).1
    have th : (2097151 : Word).getLsbD (22+j) = false := (nn ⟨j,hj⟩).2
    simpa only [BitVec.getLsbD_and, mh, th, Bool.and_true] using bit (22+j)

end PEqualNP.Outside.L_meta_7737.DAG

namespace PEqualNP.Outside.L_meta_7737.Slicing

variable {α : Type} [DecidableEq α]

def Build (G : α → α → α → Prop) (goal : α) : Nat → List α → Prop
  | 0, bank => goal ∈ bank
  | k+1, bank => Build G goal k bank ∨
    ∃ a ∈ bank, ∃ b ∈ bank, ∃ z, G a b z ∧ Build G goal k (z::bank)

def predList (a b z : α) (next : List α) :=
  ((next.erase z).insert b).insert a

inductive Flow (G : α → α → α → Prop) (goal : α) : Nat → List α → Prop where
  | done : Flow G goal 0 [goal]
  | step {k : Nat} {next : List α} (a b z : α) (hgate : G a b z)
         (hz : z ∈ next) (hf : z ∉ predList a b z next)
         (tail : Flow G goal k next) : Flow G goal (k+1) (predList a b z next)

variable {G : α → α → α → Prop} {goal : α}

private theorem nd_insert (a : α) {xs : List α} (h : xs.Nodup) : (xs.insert a).Nodup := by
  by_cases ha : a ∈ xs <;> simp [ha,h]

private theorem perm_sum {xs ys : List Nat} (hp : xs.Perm ys) : xs.sum = ys.sum := by
  induction hp with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap _ _ _ => simp [Nat.add_left_comm]
  | trans _ _ h1 h2 => exact h1.trans h2

theorem Flow.nodup {k s} (h : Flow G goal k s) : s.Nodup := by
  induction h with
  | done => simp
  | step a b z _ hz hf tail ih =>
    exact nd_insert a (nd_insert b (ih.erase z))

theorem compress {k bank} (h : Build G goal k bank) :
    ∃ j ≤ k, ∃ s ⊆ bank, Flow G goal j s := by
  induction k generalizing bank with
  | zero =>
    exact ⟨0, Nat.le_refl _, [goal], by simpa [Build] using h, .done⟩
  | succ k ih =>
    rcases h with skip | ⟨a,ha,b,hb,z,hg,tail⟩
    · obtain ⟨j,hj,s,hs,hf⟩ := ih skip
      exact ⟨j, by omega, s, hs, hf⟩
    · obtain ⟨j,hj,t,ht,flow⟩ := ih tail
      by_cases hs : t ⊆ bank
      · exact ⟨j, by omega, t, hs, flow⟩
      · have zt : z ∈ t := by
          apply Classical.byContradiction
          intro hn
          apply hs
          intro x hx
          rcases List.mem_cons.mp (ht hx) with rfl | yes
          · exact False.elim (hn hx)
          · exact yes
        have zb : z ∉ bank := by
          intro hz
          apply hs
          intro x hx
          exact (List.mem_cons.mp (ht hx)).elim (fun e => e ▸ hz) id
        have hpre : predList a b z t ⊆ bank := by
          intro x hx
          simp only [predList, List.mem_insert_iff] at hx
          rcases hx with rfl | rfl | hr
          · exact ha
          · exact hb
          · have hn : x ≠ z := by
              intro ee
              subst x
              exact (flow.nodup.not_mem_erase) hr
            exact (List.mem_cons.mp (ht (List.mem_of_mem_erase hr))).resolve_left hn
        exact ⟨j+1, by omega, _, hpre, .step a b z hg zt (fun hh => zb (hpre hh)) flow⟩

theorem Flow.covers {k s} (h : Flow G goal k s) (D : α → Prop) (hgoal : D goal)
    (pull : ∀ a b z, G a b z → D z → D a ∨ D b) : ∃ x ∈ s, D x := by
  induction h with
  | done => exact ⟨_, by simp, hgoal⟩
  | step a b z hg hz hf tail ih =>
    obtain ⟨x,hx,hd⟩ := ih
    rcases List.mem_cons.mp ((List.perm_cons_erase hz).mem_iff.mp hx) with rfl | hr
    · rcases pull a b x hg hd with da | db
      · exact ⟨a, by simp [predList], da⟩
      · exact ⟨b, by simp [predList], db⟩
    · exact ⟨x, by simp [predList,hr], hd⟩

theorem width_insert (a : α) (xs : List α) : (xs.insert a).length ≤ xs.length+1 := by
  by_cases ha : a ∈ xs <;> simp [List.insert,ha]

theorem Flow.width {k s} (h : Flow G goal k s) : s.length ≤ k+1 := by
  induction h with
  | done => simp
  | @step n t a b z _ hz _ tail ih =>
    have e := (List.perm_cons_erase hz).length_eq
    simp only [List.length_cons] at e
    have h1 := width_insert b (t.erase z)
    have h2 := width_insert a ((t.erase z).insert b)
    unfold predList
    omega

def mass (cost : α → Nat) (xs : List α) := (xs.map cost).sum

theorem mass_subset (cost : α → Nat) {xs pool : List α} (hn : xs.Nodup) (hs : xs ⊆ pool) :
    mass cost xs ≤ mass cost pool := by
  induction xs generalizing pool with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hs (List.mem_cons_self (a:=a) (l:=xs))
    have hsub : xs ⊆ pool.erase a := by
      intro y hy
      have hp := hs (List.mem_cons_of_mem a hy)
      have he := (List.perm_cons_erase ha).mem_iff.mp hp
      rcases List.mem_cons.mp he with rfl | hr
      · exact False.elim ((List.nodup_cons.mp hn).1 hy)
      · exact hr
    have htail := ih (List.nodup_cons.mp hn).2 hsub
    have e := perm_sum ((List.perm_cons_erase ha).map cost)
    simp only [List.map_cons, List.sum_cons] at e
    simp only [mass, List.map_cons, List.sum_cons] at *
    omega

theorem Flow.linear {k s} (h : Flow G goal k s) (cost : α → Nat)
    (hgate : ∀ a b z, G a b z → cost z ≤ cost a + cost b)
    (tight : k+1 ≤ s.length) : cost goal ≤ mass cost s := by
  induction h with
  | done => simp [mass]
  | @step n t a b z hg hz hf tail ih =>
    have perm := List.perm_cons_erase hz
    have lr := perm.length_eq
    simp only [List.length_cons] at lr
    have hs1 := width_insert b (t.erase z)
    have hs2 := width_insert a ((t.erase z).insert b)
    change n + 1 + 1 ≤ (((t.erase z).insert b).insert a).length at tight
    have htt := tail.width
    have tbound := ih (by omega)
    have aa : a ∉ (t.erase z).insert b := by
      intro ha
      rw [List.insert_of_mem ha] at tight
      omega
    have bb : b ∉ t.erase z := by
      intro hb
      rw [List.insert_of_mem hb] at tight
      have := width_insert a (t.erase z)
      omega
    have e := perm_sum (perm.map cost)
    simp only [List.map_cons, List.sum_cons] at e
    have hw := hgate a b z hg
    unfold predList
    rw [List.insert_of_not_mem aa, List.insert_of_not_mem bb]
    simp only [mass, List.map_cons, List.sum_cons] at tbound ⊢
    omega

end PEqualNP.Outside.L_meta_7737.Slicing

namespace PEqualNP.Outside.L_meta_7737.Slicing

variable {α β : Type} [DecidableEq α] [DecidableEq β]
variable {G : α → α → α → Prop} {H : β → β → β → Prop}

theorem Build.mono {n : Nat} {goal : β} {xs ys : List β}
    (h : Build H goal n xs) (sub : xs ⊆ ys) : Build H goal n ys := by
  induction n generalizing xs ys with
  | zero => exact sub h
  | succ n ih =>
    rcases h with skip | ⟨a,ha,b,hb,z,hg,tail⟩
    · exact .inl (ih skip sub)
    · exact .inr ⟨a,sub ha,b,sub hb,z,hg,ih tail (fun v hv => by
        rcases List.mem_cons.mp hv with rfl | hx
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem z (sub hx))⟩

theorem mass_insert_le (cost : α → Nat) (a : α) (xs : List α) :
    mass cost (xs.insert a) ≤ cost a + mass cost xs := by
  by_cases h : a ∈ xs <;> simp [mass,h]

theorem mass_move (cost : α → Nat) {z : α} {xs : List α} (hz : z ∈ xs) :
    mass cost xs = cost z + mass cost (xs.erase z) := by
  have h := (List.perm_cons_erase hz).map cost
  have sums {x y : List Nat} (hp : x.Perm y) : x.sum = y.sum := by
    induction hp with
    | nil => rfl
    | cons _ _ ih => simp [ih]
    | swap _ _ _ => simp [Nat.add_left_comm]
    | trans _ _ u v => exact u.trans v
  simpa only [mass,List.map_cons,List.sum_cons] using sums h


theorem Flow.project {goal : α} {n : Nat} {s : List α} (h : Flow G goal n s)
    (p : α → β) (base : List β) (c : α → Bool)
    (emit : ∀ a b z, G a b z → H (p a) (p b) (p z))
    (fold : ∀ a b z, G a b z → (c a || c b) = true →
       p z ∈ p a :: p b :: base)
    (both : ∀ a b z, G a b z → c a = true → c b = true → c z = true) :
    ∃ k, Build H (p goal) k (s.map p ++ base) ∧
      k + mass (fun w => (c w).toNat) s ≤ n + (c goal).toNat := by
  induction h with
  | done => exact ⟨0, List.mem_append_left _ (by simp), by simp [mass]⟩
  | @step j next a b z hg hz hf tail ih =>
    let prev := predList a b z next
    let start := prev.map p ++ base
    let wt := fun w => (c w).toNat
    obtain ⟨k,run,num⟩ := ih
    have ha : a ∈ prev := by simp [prev,predList]
    have hb : b ∈ prev := by simp [prev,predList]
    have aa : p a ∈ start := List.mem_append_left _ (List.mem_map_of_mem ha)
    have bb : p b ∈ start := List.mem_append_left _ (List.mem_map_of_mem hb)
    have includeNext : next.map p ++ base ⊆ p z :: start := by
      intro x hx
      rcases List.mem_append.mp hx with hm | hu
      · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hm
        rcases List.mem_cons.mp ((List.perm_cons_erase hz).mem_iff.mp hv) with rfl | hr
        · exact List.mem_cons_self
        · have hvp : v ∈ prev := by simp [prev,predList,hr]
          exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map_of_mem hvp))
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ hu)
    have stepCost : mass wt prev ≤ wt a + wt b + mass wt (next.erase z) := by
      have a1 := mass_insert_le wt b (next.erase z)
      have a2 := mass_insert_le wt a ((next.erase z).insert b)
      change mass wt (((next.erase z).insert b).insert a) ≤ _
      omega
    have after := mass_move wt hz
    by_cases dead : (c a || c b) = true
    · have free : p z ∈ start := by
        rcases List.mem_cons.mp (fold a b z hg dead) with hit | rest
        · exact hit ▸ aa
        · rcases List.mem_cons.mp rest with hit | inBase
          · exact hit ▸ bb
          · exact List.mem_append_right _ inBase
      have comp : Build H (p goal) k start := run.mono (fun x hx => by
        rcases List.mem_cons.mp (includeNext hx) with rfl | hx
        · exact free
        · exact hx)
      have limit : wt a + wt b ≤ wt z + 1 := by
        cases ea : c a <;> cases eb : c b <;> simp [wt,ea,eb,both a b z hg] at * <;> omega
      exact ⟨k,comp,by change k + mass wt prev ≤ _; change k + mass wt next ≤ _ at num; omega⟩
    · have sum0 : wt a + wt b = 0 := by
        cases ea : c a <;> cases eb : c b <;> simp_all [wt]
      refine ⟨k+1,Or.inr ⟨p a,aa,p b,bb,p z,emit a b z hg,run.mono includeNext⟩,?_⟩
      change k+1 + mass wt prev ≤ _
      change k + mass wt next ≤ _ at num
      omega

end PEqualNP.Outside.L_meta_7737.Slicing

namespace PEqualNP.Outside.L_meta_7737.Restriction
open PEqualNP.Outside.L_meta_7737.Slicing

abbrev I := Fin 14
abbrev Assignment := I → Bool
abbrev V := Assignment → Bool
noncomputable local instance : DecidableEq V := Classical.typeDecidableEq V

def raw (i : I) : V := fun u => u i
def constant (b : Bool) : V := fun _ => b
def eval (o : Bool) (a b : V) : V := fun u => if o then a u || b u else a u && b u
def G (a b z : V) : Prop := ∃ o, z = eval o a b
def base (active : List I) : List V := constant false :: constant true :: active.map raw
def changeBit (i : I) (b : Bool) (u : Assignment) : Assignment := fun j => if j=i then b else u j
def proj (i : I) (b : Bool) (v : V) : V := fun u => v (changeBit i b u)
def IsConst (v : V) := v = constant false ∨ v = constant true
noncomputable def fixed (i : I) (b : Bool) (v : V) : Bool := @decide (IsConst (proj i b v)) (Classical.propDecidable _)

def Essential (v : V) (i : I) : Prop :=
  ∃ u w : Assignment, v u ≠ v w ∧ ∀ j, j ≠ i → u j = w j

def LB (active : List I) (f : V) (n : Nat) : Prop :=
  ∀ k, Build G f k (base active) → n ≤ k

theorem raw_inj {i j : I} (h : raw i = raw j) : i = j := by
  have ht := congrFun h (fun k => decide (k = i))
  exact (show j = i by simpa [raw] using ht.symm).symm

theorem essential_nonconst {v : V} {i : I} (h : Essential v i) : ¬IsConst v := by
  obtain ⟨u,w,e,_⟩ := h
  rintro (rfl|rfl) <;> exact e rfl

theorem proj_raw (i : I) (b : Bool) (j : I) :
    proj i b (raw j) = if j=i then constant b else raw j := by
  by_cases h : j=i <;> funext u <;> simp [proj,raw,constant,changeBit,h]

theorem proj_const (i : I) (b d : Bool) : proj i b (constant d) = constant d := rfl

theorem proj_eval (i : I) (b o : Bool) (u v : V) :
    proj i b (eval o u v) = eval o (proj i b u) (proj i b v) := by cases o <;> rfl

theorem op_base (o b : Bool) (v : V) :
    eval o (constant b) v = if o == b then constant b else v := by
  cases o <;> cases b <;> funext u <;> simp [eval,constant]

theorem op_swap (o : Bool) (u v : V) : eval o u v = eval o v u := by
  cases o <;> funext w <;> simp [eval,Bool.and_comm,Bool.or_comm]

theorem const_in_base (l : List I) (b : Bool) : constant b ∈ base l := by
  cases b <;> simp [base]

theorem fixed_eq {i : I} {b : Bool} {v : V} : fixed i b v = true ↔ IsConst (proj i b v) := by
  simp [fixed]

theorem projection {f : V} {n : Nat} {s : List V} (h : Flow G f n s) (i : I) (b : Bool) :
    ∃ k, Build G (proj i b f) k (s.map (proj i b) ++ [constant false,constant true]) ∧
      k + mass (fun w => (fixed i b w).toNat) s ≤ n + (fixed i b f).toNat := by
  apply h.project (proj i b) [constant false,constant true] (fixed i b)
  · rintro a c z ⟨o,rfl⟩
    exact ⟨o,proj_eval _ _ _ _ _⟩
  · rintro a c z ⟨o,rfl⟩ dead
    rw [proj_eval]
    rcases Bool.or_eq_true_iff.mp dead with ha | hc
    · rcases fixed_eq.mp ha with hz | ho
      · rw [hz,op_base]
        cases o <;> simp
      · rw [ho,op_base]
        cases o <;> simp
    · rw [op_swap]
      rcases fixed_eq.mp hc with hz | ho
      · rw [hz,op_base]
        cases o <;> simp
      · rw [ho,op_base]
        cases o <;> simp
  · rintro a c z ⟨o,rfl⟩ ha hc
    apply fixed_eq.mpr
    rw [proj_eval]
    rcases fixed_eq.mp ha with ha | ha <;> rcases fixed_eq.mp hc with hc | hc <;>
      rw [ha,hc] <;> cases o <;> first | exact Or.inl rfl | exact Or.inr rfl

theorem sep_op (u v : Assignment) (a b z : V) (hg : G a b z) (hz : z u ≠ z v) :
    a u ≠ a v ∨ b u ≠ b v := by
  apply Classical.byContradiction
  intro hn
  simp only [not_or,Classical.not_not] at hn
  obtain ⟨o,rfl⟩ := hg
  exact hz (by simp [eval,hn.1,hn.2])

theorem raw_needed {f} {s : List V} {k} (h : Flow G f k s)
    {i : I} {A : List I} (e : Essential f i) (inc : s ⊆ base A) : raw i ∈ s := by
  obtain ⟨u,v,sep,agree⟩ := e
  obtain ⟨x,m,hx⟩ := h.covers (fun x => x u ≠ x v) sep (sep_op u v)
  rcases List.mem_cons.mp (inc m) with rfl | m1
  · exact False.elim (hx rfl)
  rcases List.mem_cons.mp m1 with rfl | m2
  · exact False.elim (hx rfl)
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp m2
  by_cases eq : j=i
  · exact eq ▸ m
  · exact False.elim (hx (agree j eq))

theorem count_vars {k f A} (h : Build G f k (base A)) (hn : A.Nodup)
    (ess : ∀ i ∈ A, Essential f i) : A.length ≤ k+1 := by
  obtain ⟨j,hj,s,sub,flow⟩ := compress h
  have hin : A.map raw ⊆ s := by
    intro w hw
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hw
    exact raw_needed flow (ess i hi) sub
  have nodup : (A.map raw).Nodup := by
    apply List.Pairwise.map _ _ hn
    intro x y xy eq
    exact xy (raw_inj eq)
  have size := List.Nodup.length_le_of_subset nodup hin
  have width := flow.width
  simp only [List.length_map] at size
  omega

theorem base_proj (A : List I) (i : I) (b : Bool) {v : V} (h : v ∈ base A) :
    proj i b v ∈ base (A.erase i) := by
  rcases List.mem_cons.mp h with rfl | h
  · exact const_in_base _ _
  rcases List.mem_cons.mp h with rfl | h
  · exact const_in_base _ _
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp h
  rw [proj_raw]
  by_cases eq : j=i
  · simpa [eq] using const_in_base (A.erase i) b
  · rw [if_neg eq]
    have hk : j ∈ A.erase i := (List.mem_erase_of_ne eq).mpr hj
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hk))

theorem projection_bank {s t : List V} {i : I} {b : Bool}
    (hs : ∀ w ∈ s, proj i b w ∈ t) (h0 : constant false ∈ t) (h1 : constant true ∈ t) :
    s.map (proj i b) ++ [constant false,constant true] ⊆ t := by
  intro w hw
  rcases List.mem_append.mp hw with in1 | in2
  · obtain ⟨u,hu,rfl⟩ := List.mem_map.mp in1
    exact hs u hu
  · rcases List.mem_cons.mp in2 with rfl | h
    · exact h0
    · simpa using (List.mem_singleton.mp h ▸ h1)

theorem one_essential {A : List I} {f : V} {k n} {i : I} {b : Bool}
    (h : Build G f k (base A)) (ei : Essential f i) (non : ¬IsConst (proj i b f))
    (lower : LB (A.erase i) (proj i b f) n) : n+1 ≤ k := by
  obtain ⟨j,hj,s,sub,flow⟩ := compress h
  have hi := raw_needed flow ei sub
  obtain ⟨n',model,cost⟩ := projection flow i b
  have child := lower n' (model.mono (projection_bank
    (fun w hw => base_proj A i b (sub hw)) (const_in_base _ false) (const_in_base _ true)))
  have target : fixed i b f = false := by simp [fixed,non]
  have root : fixed i b (raw i) = true := by
    apply fixed_eq.mpr
    rw [proj_raw]
    cases b <;> simp [IsConst]
  have one := mass_subset (fun w => (fixed i b w).toNat) (xs:=[raw i]) (by simp)
    (show [raw i] ⊆ s by simpa using hi)
  simp only [target,Bool.toNat_false,Nat.add_zero] at cost
  simp [mass,root] at one
  unfold mass at cost
  omega

end PEqualNP.Outside.L_meta_7737.Restriction

namespace PEqualNP.Outside.L_meta_7737.States
open PEqualNP.Outside.L_meta_7737.Restriction PEqualNP.Outside.L_meta_7737.Slicing
abbrev M := BitVec 14
def positive : List M := [129, 257, 1025, 130, 514, 8194, 260, 4100, 8196, 136, 2056, 4104, 1040, 2064, 8208, 544, 1056, 4128, 320, 576, 2112]
def negative : List M := [244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256]
def knownTrue (m : M) := positive.any fun r => r &&& m == r
def knownFalse (m : M) := negative.any fun r => r &&& m == m
def assignment (m : M) : Assignment := fun i => m.getLsbD i.val
def Partial (f : V) := (∀ m, knownTrue m = true → f (assignment m) = true) ∧
  (∀ m, knownFalse m = true → f (assignment m) = false)
def unit (i : I) : M := BitVec.twoPow 14 i.val
def dropped (a : M) (i : I) : M := a &&& ~~~unit i
def added (s : M) (i : I) (b : Bool) := if b then s ||| unit i else s
def indices (a : M) := (List.finRange 14).filter (fun i => a.getLsbD i.val)
def slice (f : V) (s a : M) : V := fun u => f (fun j => s.getLsbD j.val || (a.getLsbD j.val && u j))
def seeds : List M := 0 :: (List.finRange 14).map unit

theorem unit_bit (i j : I) : (unit i).getLsbD j.val = decide (i=j) := by
  simp [unit,Fin.ext_iff,eq_comm]

@[simp] theorem unit_get (i j : I) : (unit i)[j.val] = decide (j=i) := by
  simp [unit,Fin.ext_iff]

theorem index_mem {i : I} {a : M} : i ∈ indices a ↔ a.getLsbD i.val = true := by
  simp [indices,List.mem_finRange]

theorem index_nodup (a : M) : (indices a).Nodup := (List.nodup_finRange _).filter _

theorem index_drop (a : M) (i : I) : indices (dropped a i) = (indices a).erase i := by
  rw [(index_nodup a).erase_eq_filter]
  unfold indices
  rw [List.filter_filter]
  apply List.filter_congr
  intro j _
  simp only [dropped,BitVec.getLsbD_and,BitVec.getLsbD_not,unit_bit]
  by_cases eq : j=i <;> simp [eq,j.isLt,Ne.symm]

theorem slice_proj (f : V) (s a : M) (i : I) (b : Bool) (hi : i ∈ indices a) :
    proj i b (slice f s a) = slice f (added s i b) (dropped a i) := by
  have ai := index_mem.mp hi
  have av : a[i.val] = true := ai
  funext u
  apply congrArg f
  funext j
  by_cases eq : j=i
  · subst j
    cases b <;> simp [changeBit,added,dropped,av,i.isLt,unit_get]
  · cases b <;> simp [changeBit,added,dropped,eq,Ne.symm eq,j.isLt,unit_bit]

theorem slice_at (f : V) (s a m : M) : slice f s a (assignment m) = f (assignment (s ||| (a &&& m))) := by
  apply congrArg f
  funext j
  simp [assignment]

def witnesses (s a : M) (i : I) := seeds.any fun m =>
  knownFalse (s ||| (a &&& m)) && knownTrue (s ||| (a &&& (m ||| unit i)))

theorem witnesses_sound {f : V} (hf : Partial f) {s a : M} {i : I} (ok : witnesses s a i = true) :
    Essential (slice f s a) i := by
  obtain ⟨m,hm,h⟩ := List.any_eq_true.mp ok
  obtain ⟨hn,hp⟩ := Bool.and_eq_true_iff.mp h
  refine ⟨assignment m, assignment (m ||| unit i),?_,?_⟩
  · rw [slice_at,slice_at,hf.2 _ hn,hf.1 _ hp]
    decide
  · intro j hji
    simp [assignment,hji]

def essentialList (s a : M) := (indices a).filter (witnesses s a)
def CountBound (s a : M) (n : Nat) : Prop :=
  ∀ f, Partial f → LB (indices a) (slice f s a) n

theorem width_bound (s a : M) (n : Nat) (h : n+1 ≤ (essentialList s a).length) : CountBound s a n := by
  intro f hf k hk
  classical
  obtain ⟨j,hj,ws,sub,flow⟩ := compress hk
  have inc : (essentialList s a).map raw ⊆ ws := by
    intro v hv
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hv
    exact raw_needed flow (witnesses_sound hf (List.mem_filter.mp hi).2) sub
  have nd : (essentialList s a).Nodup := (index_nodup a).filter _
  have nr : ((essentialList s a).map raw).Nodup := List.Pairwise.map _ (fun x y xy e => xy (raw_inj e)) nd
  have bound := List.Nodup.length_le_of_subset nr inc
  have width := flow.width
  simp only [List.length_map] at bound
  omega

theorem nonconst_of_witnesses {f : V} (hf : Partial f) {s a : M}
    (h : (indices a).any (witnesses s a) = true) : ¬IsConst (slice f s a) := by
  obtain ⟨i,_,hi⟩ := List.any_eq_true.mp h
  exact essential_nonconst (witnesses_sound hf hi)

end PEqualNP.Outside.L_meta_7737.States

namespace PEqualNP.Outside.L_meta_7737.Restriction
open PEqualNP.Outside.L_meta_7737.Slicing

noncomputable local instance : DecidableEq V := Classical.typeDecidableEq V

structure First (f : V) (A : List I) (k : Nat) where
  x : I
  y : I
  xmem : x ∈ A
  ymem : y ∈ A
  xy : x ≠ y
  o : Bool
  z : V
  gate : z = eval o (raw x) (raw y)
  zx : z ≠ raw x
  zy : z ≠ raw y
  t : List V
  n : Nat
  ht : Flow G f n t
  hz : z ∈ t
  sub : t ⊆ z::base A
  cap : n+1 ≤ k

private theorem source {a b z : V} (o : Bool) (hg : z = eval o a b) (za : z ≠ a) (zb : z ≠ b) :
    ¬ IsConst a := by
  rintro (rfl|rfl) <;> rw [op_base] at hg <;>
    cases o <;> first | exact za hg | exact zb hg

private theorem raw_of_nconst {v : V} {A : List I} (h : v ∈ base A) (nc : ¬IsConst v) :
    ∃ i ∈ A, v = raw i := by
  rcases List.mem_cons.mp h with rfl | h
  · exact False.elim (nc (.inl rfl))
  rcases List.mem_cons.mp h with rfl | h
  · exact False.elim (nc (.inr rfl))
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
  exact ⟨i,hi,rfl⟩

theorem first_exists {f : V} {A : List I} {k : Nat}
    (h : Build G f k (base A)) (hn : A.Nodup) (pop : 2 ≤ A.length)
    (ess : ∀ i ∈ A, Essential f i) : Nonempty (First f A k) := by
  obtain ⟨j,hj,s,hs,flow⟩ := compress h
  cases flow with
  | done =>
    have hin : A.map raw ⊆ [f] := by
      intro w hw
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hw
      exact raw_needed (.done) (ess i hi) hs
    have nd : (A.map raw).Nodup := List.Pairwise.map _ (fun x y xy e => xy (raw_inj e)) hn
    have c := List.Nodup.length_le_of_subset nd hin
    simp at c
    omega
  | @step n t a b z hgate hz fresh tail =>
    obtain ⟨o,hg⟩ := hgate
    have ha : a ∈ predList a b z t := by simp [predList]
    have hb : b ∈ predList a b z t := by simp [predList]
    have za : z ≠ a := fun eq => fresh (eq.symm ▸ ha)
    have zb : z ≠ b := fun eq => fresh (eq.symm ▸ hb)
    obtain ⟨i,hi,rfl⟩ := raw_of_nconst (hs ha) (source o hg za zb)
    obtain ⟨u,hu,rfl⟩ := raw_of_nconst (hs hb) (source o (hg.trans (op_swap _ _ _)) zb za)
    have ne : i ≠ u := by
      rintro rfl
      apply za
      rw [hg]
      cases o <;> funext w <;> simp [eval]
    have sub : t ⊆ z::base A := by
      intro w hw
      rcases List.mem_cons.mp ((List.perm_cons_erase hz).mem_iff.mp hw) with rfl | hr
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem z (hs (by simp [predList,hr]))
    exact ⟨⟨i,u,hi,hu,ne,o,z,hg,za,zb,t,n,tail,hz,sub,hj⟩⟩

def First.swap {f A k} (p : First f A k) : First f A k :=
  ⟨p.y,p.x,p.ymem,p.xmem,p.xy.symm,p.o,p.z,p.gate.trans (op_swap _ _ _),p.zy,p.zx,
    p.t,p.n,p.ht,p.hz,p.sub,p.cap⟩

theorem First.cofactor_gate {f A k} (p : First f A k) (b : Bool) :
    proj p.x b p.z = if p.o == b then constant b else raw p.y := by
  rw [p.gate,proj_eval,proj_raw,proj_raw]
  simp [p.xy.symm,op_base]

theorem First.survives {f A k} (p : First f A k) (e : Essential (proj p.y p.o f) p.x) :
    raw p.x ∈ p.t := by
  obtain ⟨u,v,diff,agree⟩ := e
  let u' := changeBit p.y p.o u
  let v' := changeBit p.y p.o v
  obtain ⟨w,hw,sw⟩ := p.ht.covers (fun q => q u' ≠ q v') diff (sep_op u' v')
  rcases List.mem_cons.mp (p.sub hw) with rfl | wb
  · have atU := congrFun (p.swap.cofactor_gate p.o) u
    have atV := congrFun (p.swap.cofactor_gate p.o) v
    change proj p.y p.o p.z u = _ at atU
    change proj p.y p.o p.z v = _ at atV
    have uu : proj p.y p.o p.z u = p.o := by simpa [First.swap,constant] using atU
    have vv : proj p.y p.o p.z v = p.o := by simpa [First.swap,constant] using atV
    exact False.elim (sw (uu.trans vv.symm))
  rcases List.mem_cons.mp wb with rfl | wb
  · exact False.elim (sw rfl)
  rcases List.mem_cons.mp wb with rfl | wb
  · exact False.elim (sw rfl)
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp wb
  by_cases eq : j=p.x
  · exact eq ▸ hw
  · exact False.elim (sw (by
      by_cases jy : j=p.y <;> simp [raw,u',v',changeBit,jy,agree j eq]))

theorem First.lower {f A k} (p : First f A k) (b dup : Bool) {n : Nat}
    (ed : dup = true → Essential (proj p.y p.o f) p.x)
    (nc : ¬IsConst (proj p.x b f)) (lower : LB (A.erase p.x) (proj p.x b f) n) :
    n + 1 + dup.toNat + (p.o == b).toNat ≤ k := by
  let new := base (A.erase p.x)
  obtain ⟨j,runJ,cost⟩ := projection p.ht p.x b
  have pin : ∀ w ∈ p.t, proj p.x b w ∈ new := by
    intro w hw
    rcases List.mem_cons.mp (p.sub hw) with rfl|h
    · rw [p.cofactor_gate]
      split
      · exact const_in_base _ _
      · change raw p.y ∈ base (A.erase p.x)
        have hy : p.y ∈ A.erase p.x := (List.mem_erase_of_ne p.xy.symm).mpr p.ymem
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hy))
    · exact base_proj _ _ _ h
  have low := lower j (runJ.mono (projection_bank pin (const_in_base _ _) (const_in_base _ _)))
  have fzero : fixed p.x b f = false := by simp [fixed,nc]
  rw [fzero] at cost
  let c := fun w => (fixed p.x b w).toNat
  have cf : c (raw p.x) = 1 := by
    have e : fixed p.x b (raw p.x) = true := fixed_eq.mpr (by
      rw [proj_raw]
      cases b <;> simp [IsConst])
    simp [c,e]
  have cz (eq : (p.o == b) = true) : c p.z = 1 := by
    have e : fixed p.x b p.z = true := fixed_eq.mpr (by
      rw [p.cofactor_gate,eq]
      cases b <;> simp [IsConst])
    simp [c,e]
  have dupcost : dup.toNat + (p.o == b).toNat ≤ mass c p.t := by
    cases dup with
    | false =>
      cases eq : (p.o == b) with
      | false => simp
      | true =>
        have v := mass_subset c (xs:=[p.z]) (by simp) (show [p.z] ⊆ p.t by simpa using p.hz)
        simpa [mass,cz eq] using v
    | true =>
      have rx := p.survives (ed rfl)
      cases eq : (p.o == b) with
      | false =>
        have v := mass_subset c (xs:=[raw p.x]) (by simp) (show [raw p.x] ⊆ p.t by simpa using rx)
        simpa [mass,cf] using v
      | true =>
        have nd : [p.z,raw p.x].Nodup := by simp [p.zx]
        have sub : [p.z,raw p.x] ⊆ p.t := by simp [p.hz,rx]
        have v := mass_subset c nd sub
        simpa [mass,cz eq,cf] using v
  change j + mass c p.t ≤ p.n + Bool.false.toNat at cost
  simp only [Bool.toNat_false,Nat.add_zero] at cost
  have cap := p.cap
  omega

end PEqualNP.Outside.L_meta_7737.Restriction

namespace PEqualNP.Outside.L_meta_7737.States
open PEqualNP.Outside.L_meta_7737.Slicing PEqualNP.Outside.L_meta_7737.Restriction

theorem build_map {α β : Type} [DecidableEq α] [DecidableEq β] {H : α → α → α → Prop}
    {J : β → β → β → Prop} {f n s} (h : Build H f n s) (p : α → β)
    (mapG : ∀ a b z, H a b z → J (p a) (p b) (p z)) : Build J (p f) n (s.map p) := by
  induction n generalizing s with
  | zero => exact List.mem_map_of_mem h
  | succ n ih =>
    rcases h with skip | ⟨a,ha,b,hb,z,hg,tail⟩
    · exact .inl (ih skip)
    · exact .inr ⟨p a,List.mem_map_of_mem ha,p b,List.mem_map_of_mem hb,p z,mapG a b z hg,ih tail⟩

theorem zero_bound (s a : M) : CountBound s a 0 := fun _ _ _ _ => Nat.zero_le _

theorem weaken {s a : M} {k m : Nat} (h : CountBound s a k) (sm : m ≤ k) : CountBound s a m :=
  fun f hf n hn => Nat.le_trans sm (h f hf n hn)

theorem fix_one {s a : M} {k : Nat} (i : I) (b : Bool) (hi : i ∈ indices a)
    (child : CountBound (added s i b) (dropped a i) k) : CountBound s a k := by
  intro f hf n hn
  classical
  have h := build_map hn (proj i b) (J:=G) (fun x y z h => by
    obtain ⟨o,rfl⟩ := h; exact ⟨o,proj_eval _ _ _ _ _⟩)
  rw [slice_proj f s a i b hi] at h
  apply child f hf n (h.mono ?_)
  intro w hw
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hw
  rw [index_drop]
  exact base_proj _ _ _ hu

theorem fix_essential {s a : M} {k : Nat} (i : I) (b : Bool) (hi : i ∈ indices a)
    (ei : witnesses s a i = true) (other : (indices (dropped a i)).any (witnesses (added s i b) (dropped a i)) = true)
    (child : CountBound (added s i b) (dropped a i) k) : CountBound s a (k+1) := by
  intro f hf n hn
  apply one_essential (b:=b) hn (witnesses_sound hf ei)
  · rw [slice_proj f s a i b hi]
    exact nonconst_of_witnesses hf other
  · rw [slice_proj f s a i b hi,← index_drop]
    exact child f hf

structure Choice where
  flip : Bool
  bit : Bool
  dup : Bool
  lower : Nat
  deriving DecidableEq

def branchX (c : Choice) (i j : I) := if c.flip then j else i
def branchY (c : Choice) (i j : I) := if c.flip then i else j

def GoodChoice (s a : M) (need : Nat) (i j : I) (o : Bool) (c : Choice) : Prop :=
  let x := branchX c i j
  let y := branchY c i j
  (c.dup = true → witnesses (added s y o) (dropped a y) x = true) ∧
  (indices (dropped a x)).any (witnesses (added s x c.bit) (dropped a x)) = true ∧
  need ≤ c.lower + 1 + c.dup.toNat + (o == c.bit).toNat

def Child (s a : M) (i j : I) (c : Choice) :=
  let x := branchX c i j
  CountBound (added s x c.bit) (dropped a x) c.lower

theorem first_rule {s a : M} {m : Nat} (pop : 2 ≤ (indices a).length)
    (all : ∀ i ∈ indices a, witnesses s a i = true)
    (policy : ∀ i ∈ indices a, ∀ j ∈ indices a, i ≠ j → ∀ o : Bool,
      ∃ c, GoodChoice s a m i j o c ∧ Child s a i j c) : CountBound s a m := by
  intro f hf k h
  obtain ⟨p⟩ := first_exists h (index_nodup a) pop (fun i hi => witnesses_sound hf (all i hi))
  obtain ⟨c,hc,child⟩ := policy p.x p.xmem p.y p.ymem p.xy p.o
  let q := if c.flip then p.swap else p
  have qx : q.x = branchX c p.x p.y := by cases e : c.flip <;> simp [q,e,branchX,First.swap]
  have qy : q.y = branchY c p.x p.y := by cases e : c.flip <;> simp [q,e,branchY,First.swap]
  have qo : q.o = p.o := by cases e : c.flip <;> simp [q,e,First.swap]
  change (c.dup = true → witnesses (added s _ _) (dropped a _) _ = true) ∧ _ at hc
  rcases hc with ⟨de,nn,le⟩
  change CountBound (added s _ _) (dropped a _) c.lower at child
  rw [← qx,← qy,← qo] at de
  rw [← qx] at nn child
  have bound := q.lower c.bit c.dup (n:=c.lower) (fun hd => by
    rw [slice_proj f s a q.y q.o q.ymem]; exact witnesses_sound hf (de hd)) (by
    rw [slice_proj f s a q.x c.bit q.xmem]; exact nonconst_of_witnesses hf nn) (by
    rw [slice_proj f s a q.x c.bit q.xmem,← index_drop]; exact child f hf)
  rw [qo] at bound
  exact Nat.le_trans le bound

end PEqualNP.Outside.L_meta_7737.States

namespace PEqualNP.Outside.L_meta_7737.States
open PEqualNP.Outside.L_meta_7737.Restriction PEqualNP.Outside.L_meta_7737.Slicing

def rename (p : I → I) (f : V) : V := fun u => f (fun i => u (p i))
def encode (u : Assignment) : M := (BitVec.ofBoolListLE (List.ofFn u)).setWidth 14

private theorem decode (u : Assignment) (i : I) : (encode u).getLsbD i.val = u i := by
  simp only [encode,BitVec.getLsbD_setWidth,i.isLt,decide_true,Bool.true_and,BitVec.getLsbD_ofBoolListLE]
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by simpa using i.isLt)]
  simp only [Option.getD_some,List.getElem_ofFn]

def subMask (x y : M) : Prop := ∀ i : I, assignment x i = true → assignment y i = true

theorem subMask_eq {x y : M} : subMask x y ↔ x &&& y = x := by
  constructor
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have e := h ⟨i,hi⟩
    change x.getLsbD i = true → y.getLsbD i = true at e
    rw [BitVec.getLsbD_and]
    cases hx : x.getLsbD i <;> simp [hx,e]
  · intro h i e
    have bit := congrArg (fun z : M => z.getLsbD i.val) h
    change x.getLsbD i.val = true at e
    simpa [assignment,e] using bit

def Pulls (rows : List M) (p : I → I) : Prop :=
  ∀ x ∈ rows, ∃ y ∈ rows, ∀ i : I, assignment y i = assignment x (p i)

def Sym (p : I → I) := Pulls positive p ∧ Pulls negative p

theorem sym_comp {p q : I → I} (hp : Sym p) (hq : Sym q) : Sym (fun i => p (q i)) := by
  have aux {rs : List M} (a : Pulls rs p) (b : Pulls rs q) : Pulls rs (fun i => p (q i)) := by
    intro x hx
    obtain ⟨y,hy,ey⟩ := a x hx
    obtain ⟨z,hz,ez⟩ := b y hy
    exact ⟨z,hz,fun i => (ez i).trans (ey (q i))⟩
  exact ⟨aux hp.1 hq.1,aux hp.2 hq.2⟩

theorem rename_partial {f : V} (h : Partial f) {p : I → I} (sym : Sym p) : Partial (rename p f) := by
  constructor
  · intro m hm
    obtain ⟨x,hx,sub⟩ := List.any_eq_true.mp hm
    obtain ⟨y,hy,ey⟩ := sym.1 _ hx
    let v := fun j => assignment m (p j)
    have eq : assignment (encode v) = v := funext (decode v)
    change f v = true
    rw [←eq]
    apply h.1
    apply List.any_eq_true.mpr
    refine ⟨y,hy,beq_iff_eq.mpr (subMask_eq.mp ?_)⟩
    intro i ei
    rw [eq]
    exact subMask_eq.mpr (eq_of_beq sub) (p i) ((ey i).symm ▸ ei)
  · intro m hm
    obtain ⟨x,hx,sub⟩ := List.any_eq_true.mp hm
    obtain ⟨y,hy,ey⟩ := sym.2 _ hx
    let v := fun j => assignment m (p j)
    have eq : assignment (encode v) = v := funext (decode v)
    change f v = false
    rw [←eq]
    apply h.2
    apply List.any_eq_true.mpr
    refine ⟨y,hy,beq_iff_eq.mpr (BitVec.and_comm _ _ |>.trans (subMask_eq.mp ?_))⟩
    intro i ei
    rw [ey]
    apply subMask_eq.mpr (BitVec.and_comm _ _ |>.trans (eq_of_beq sub)) (p i)
    change v i = true
    rwa [eq] at ei

theorem transfer {s a t u : M} {n : Nat} {p : I → I} (pr : Sym p)
    (hs : ∀ i : I, assignment s i = assignment t (p i))
    (ha : ∀ i : I, assignment a i = assignment u (p i))
    (bound : CountBound t u n) : CountBound s a n := by
  classical
  intro f hf k hk
  apply bound (rename p f) (rename_partial hf pr) k
  have mapped := build_map hk (rename p) (J:=G) (fun x y z hg => by
    obtain ⟨o,rfl⟩ := hg; exact ⟨o,by cases o <;> rfl⟩)
  have sl : rename p (slice f s a) = slice (rename p f) t u := by
    funext v
    apply congrArg f
    funext i
    change (assignment s i || (assignment a i && v (p i))) = (assignment t (p i) || (assignment u (p i) && v (p i)))
    rw [hs,ha]
  rw [sl] at mapped
  apply mapped.mono
  intro w hw
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hw
  rcases List.mem_cons.mp hx with rfl|hx
  · exact const_in_base _ _
  rcases List.mem_cons.mp hx with rfl|hx
  · exact const_in_base _ _
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
  have hu : p i ∈ indices u := index_mem.mpr ((ha i).symm.trans (index_mem.mp hi))
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hu))

end PEqualNP.Outside.L_meta_7737.States

namespace PEqualNP.Outside.L_meta_7737.States
open PEqualNP.Outside.L_meta_7737.Restriction PEqualNP.Outside.L_meta_7737.Slicing

def Witnessed (s a m : M) : Prop :=
  ∀ i : I, m.getLsbD i.val = true → i ∈ indices a ∧ witnesses s a i = true

theorem witnessed_empty (s a : M) : Witnessed s a 0 := by
  intro i h
  simp at h

theorem witnessed_nonzero {s a m : M} (h : Witnessed s a m) (hm : m ≠ 0) :
    (indices a).any (witnesses s a) = true := by
  apply Classical.byContradiction
  intro hn
  apply hm
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  cases e : m.getLsbD i with
  | false => simp
  | true =>
    have ⟨mem,wi⟩ := h ⟨i,hi⟩ e
    exact False.elim (hn (List.any_eq_true.mpr ⟨_,mem,wi⟩))

structure Row where
  i : I
  b : Bool
  m : M
  k : Nat
  deriving Repr, DecidableEq

def RowOK (s a : M) (r : Row) := Witnessed (added s r.i r.b) (dropped a r.i) r.m ∧
  CountBound (added s r.i r.b) (dropped a r.i) r.k

def RowsOK (s a : M) (rs : List Row) := ∀ r ∈ rs, RowOK s a r

theorem rows_nil (s a : M) : RowsOK s a [] := by simp [RowsOK]
theorem rows_cons {s a : M} {r : Row} {rs : List Row}
    (w : RowOK s a r) (t : RowsOK s a rs) : RowsOK s a (r::rs) := by
  intro k h
  rcases List.mem_cons.mp h with rfl|inr
  · exact w
  · exact t k inr

def getRow (i : I) (b : Bool) : List Row → M × Nat
  | [] => (0,0)
  | r::rs => if i == r.i && b == r.b then (r.m,r.k) else getRow i b rs

theorem row_sound {s a : M} {rs : List Row} (h : RowsOK s a rs) (i : I) (b : Bool) :
    Witnessed (added s i b) (dropped a i) (getRow i b rs).1 ∧ CountBound (added s i b) (dropped a i) (getRow i b rs).2 := by
  induction rs with
  | nil => exact ⟨witnessed_empty _ _,zero_bound _ _⟩
  | cons r rs ih =>
    unfold getRow
    split <;> rename_i e
    · obtain ⟨l,rh⟩ := Bool.and_eq_true_iff.mp e
      have l' := eq_of_beq l
      have r' := eq_of_beq rh
      subst i; subst b
      exact h r (List.mem_cons_self)
    · exact ih (fun z hz => h z (List.mem_cons_of_mem _ hz))

def proposals (rs : List Row) (i j : I) (o : Bool) : List Choice :=
  [false,true].flatMap fun flip => [false,true].map fun b =>
    let x := if flip then j else i
    let y := if flip then i else j
    ⟨flip,b,(getRow y o rs).1.getLsbD x.val,(getRow x b rs).2⟩

def accepted (rs : List Row) (n : Nat) (i j : I) (o : Bool) (c : Choice) : Bool :=
  let x := branchX c i j
  let y := branchY c i j
  (getRow x c.bit rs).1 != 0 && ((getRow x c.bit rs).2 == c.lower) &&
    (!c.dup || (getRow y o rs).1.getLsbD x.val) &&
    decide (n ≤ c.lower + 1 + c.dup.toNat + (o == c.bit).toNat)

def works (rs : List Row) (n : Nat) (i j : I) (o : Bool) :=
  (proposals rs i j o).any (accepted rs n i j o)

theorem rule_tables {s a : M} {n : Nat} {rs : List Row} (h : RowsOK s a rs)
    (pa : 2 ≤ (indices a).length) (wa : Witnessed s a a)
    (hw : ∀ i ∈ indices a, ∀ j ∈ indices a, i ≠ j → ∀ o, works rs n i j o = true) : CountBound s a n := by
  apply first_rule pa (fun i hi => (wa i (index_mem.mp hi)).2)
  intro i hi j hj ij o
  obtain ⟨c,_,hc⟩ := List.any_eq_true.mp (hw i hi j hj ij o)
  let x := branchX c i j
  let y := branchY c i j
  have a1 := row_sound h x c.bit
  have a2 := row_sound h y o
  change (((_ && _) && _) && _) = true at hc
  simp only [Bool.and_eq_true_iff,Bool.or_eq_true_iff,Bool.not_eq_true',
    decide_eq_true_eq,bne_iff_ne,beq_iff_eq] at hc
  rcases hc with ⟨⟨⟨non,eq⟩,cop⟩,min⟩
  refine ⟨c,⟨?_,witnessed_nonzero a1.1 non,min⟩,?_⟩
  · intro d
    have e : (getRow y o rs).1.getLsbD x.val = true := cop.resolve_left (by simp [d])
    exact (a2.1 _ e).2
  · change CountBound (added s x c.bit) (dropped a x) c.lower
    rw [←eq]
    exact a1.2

end PEqualNP.Outside.L_meta_7737.States

namespace PEqualNP.Outside.L_meta_7737.States
open PEqualNP.Outside.L_meta_7737.Restriction

theorem width_of_mask {s a e : M} {k : Nat} (w : Witnessed s a e)
    (sz : k+1 ≤ (indices e).length) : CountBound s a k := by
  apply width_bound
  apply Nat.le_trans sz
  apply List.Nodup.length_le_of_subset (index_nodup e)
  intro i hi
  exact List.mem_filter.mpr (w i (index_mem.mp hi))

private theorem select_in {X : Type} {xs : List X} {x : X} (h : x ∈ xs) (i : Nat) :
    xs.getD i x ∈ xs := by
  by_cases hi : i < xs.length
  · simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]
    exact List.getElem_mem _
  · simp [List.getD, List.getElem?_eq_none (by omega : xs.length ≤ i),h]

def packedWitness (s a : M) (i : I) (code : Nat) : Bool :=
  let spec := code >>> (16 * i.val)
  let seed := seeds.getD (spec % 16) 0
  let neg := negative.getD ((spec >>> 4) % 64) 244
  let pos := positive.getD ((spec >>> 10) % 32) 129
  let lo := s ||| (a &&& seed)
  let hi := s ||| (a &&& (seed ||| unit i))
  neg &&& lo == lo && pos &&& hi == pos

theorem witness_check {s a mask : M} (code : Nat)
    (checked : ∀ i : I, mask.getLsbD i.val = true →
      a.getLsbD i.val = true ∧ packedWitness s a i code = true) : Witnessed s a mask := by
  intro i hi
  obtain ⟨active,cert⟩ := checked i hi
  refine ⟨index_mem.mpr active,?_⟩
  let c := code >>> (16*i.val)
  let seed := seeds.getD (c % 16) 0
  let neg := negative.getD ((c >>> 4)%64) 244
  let pos := positive.getD ((c >>> 10)%32) 129
  have ns : seed ∈ seeds := select_in (by exact List.mem_cons_self) _
  have nn : neg ∈ negative := select_in (by exact List.mem_cons_self) _
  have pp : pos ∈ positive := select_in (by exact List.mem_cons_self) _
  obtain ⟨h1,h2⟩ := Bool.and_eq_true_iff.mp cert
  apply List.any_eq_true.mpr
  refine ⟨seed,ns,Bool.and_eq_true_iff.mpr ⟨?_,?_⟩⟩
  · exact List.any_eq_true.mpr ⟨neg,nn,h1⟩
  · exact List.any_eq_true.mpr ⟨pos,pp,h2⟩

def permCode (n : Nat) (i : I) : I := ⟨((n >>> (4*i.val)) % 16) % 14, Nat.mod_lt _ (by decide)⟩

end PEqualNP.Outside.L_meta_7737.States

namespace PEqualNP.Outside.L_meta_7737.States
open PEqualNP.Outside.L_meta_7737.Restriction

def pullsCheck (rows : List M) (p : I → I) :=
  rows.all fun r => rows.contains (encode (fun i => assignment r (p i)))

theorem pulls_of_check {rows : List M} {p : I → I} (h : pullsCheck rows p = true) : Pulls rows p := by
  intro r hr
  let v := fun i => assignment r (p i)
  have mem : encode v ∈ rows := List.contains_iff_mem.mp (List.all_eq_true.mp h r hr)
  refine ⟨encode v,mem,?_⟩
  intro i
  change (encode v).getLsbD i.val = v i
  simp only [encode,BitVec.getLsbD_setWidth,i.isLt,decide_true,Bool.true_and,BitVec.getLsbD_ofBoolListLE]
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by simp)]
  simp only [Option.getD_some,List.getElem_ofFn]

theorem sym_from_check (p : I → I) (a : pullsCheck positive p = true) (b : pullsCheck negative p = true) :
    Sym p := ⟨pulls_of_check a,pulls_of_check b⟩

theorem fixE {s a e t : M} {k : Nat} (i : I) (b : Bool) (w : Witnessed s a e)
    (bit : e.getLsbD i.val = true) (w' : Witnessed (added s i b) (dropped a i) t) (nt : t ≠ 0)
    (child : CountBound (added s i b) (dropped a i) k) : CountBound s a (k+1) :=
  fix_essential i b (w i bit).1 (w i bit).2 (witnessed_nonzero w' nt) child

end PEqualNP.Outside.L_meta_7737.States

namespace PEqualNP.Outside.L_meta_7737.States
open PEqualNP.Outside.L_meta_7737.Restriction PEqualNP.Outside.L_meta_7737.Slicing PEqualNP.Outside.L_meta_7737.Core PEqualNP.Outside.L_meta_7737.DAG

def primary : List V := (List.finRange 14).map raw
def vstep (ms : List V) (g : Op) : List V :=
  ms ++ [eval (!g.1) (ms.getD g.2.1 (constant false)) (ms.getD g.2.2 (constant false))]
def bstep (ms : List Bool) (g : Op) : List Bool :=
  ms ++ [if g.1 then ms.getD g.2.1 false && ms.getD g.2.2 false
                else ms.getD g.2.1 false || ms.getD g.2.2 false]
def vout (gs : List Op) (out : Nat) : V := (gs.foldl vstep primary).getD out (constant false)

private theorem project_get {X Y : Type} (p : X → Y) (ms : List X) (d : X) (i : Nat) :
    (ms.map p).getD i (p d) = p (ms.getD i d) := by
  induction ms generalizing i with
  | nil => rfl
  | cons x xs ih => cases i with
    | zero => rfl
    | succ i => exact ih i

private theorem bfold {X : Type} (ls : List Op) (pool : List X) (p : X → Bool)
    (s : List X → Op → List X)
    (comm : ∀ ms g, (s ms g).map p = bstep (ms.map p) g) :
    (ls.foldl s pool).map p = ls.foldl bstep (pool.map p) := by
  induction ls generalizing pool with
  | nil => rfl
  | cons g gs ih => simp only [List.foldl_cons,ih,comm]

private theorem prog_eval (gs : List Op) (out : Nat) (m : M) (r : Nat)
    (inputs : primary.map (fun v => v (assignment m)) = baseWords.map (fun w => w.getLsbD r)) :
    vout gs out (assignment m) = ((gs.foldl step baseWords).getD out 0).getLsbD r := by
  let p := fun (v : V) => v (assignment m)
  let q := fun (w : BitVec 58) => w.getLsbD r
  have commV (ms : List V) (g : Op) : (vstep ms g).map p = bstep (ms.map p) g := by
    have eq (i : Nat) : (ms.map p).getD i false = p (ms.getD i (constant false)) := project_get p ms (constant false) i
    obtain ⟨b,i,j⟩ := g
    cases b <;> simp only [vstep,bstep,List.map_append,List.map_cons,List.map_nil,eq] <;> rfl
  have commW (ms : List (BitVec 58)) (g : Op) : (step ms g).map q = bstep (ms.map q) g := by
    have eq (i : Nat) : (ms.map q).getD i false = q (ms.getD i 0) := by simpa [q] using project_get q ms 0 i
    obtain ⟨b,i,j⟩ := g
    cases b <;> simp only [step,bstep,List.map_append,List.map_cons,List.map_nil,eq,Bool.false_eq_true,ite_true,ite_false,q,BitVec.getLsbD_and,BitVec.getLsbD_or]
  have hs : (gs.foldl vstep primary).map p = (gs.foldl step baseWords).map q := by
    rw [bfold gs primary p vstep commV,bfold gs baseWords q step commW]
    exact congrArg (List.foldl bstep · gs) inputs
  change p ((gs.foldl vstep primary).getD out (constant false)) = q ((gs.foldl step baseWords).getD out 0)
  rw [←project_get p _ _ out,←project_get q _ _ out,hs]
  simp [p,q,constant]

def PosMon (f : V) : Prop := ∀ u v : Assignment, (∀ i, u i = true → v i = true) → f u = true → f v = true

private theorem mon_output (gs : List Op) (xs : List V) (h : ∀ x ∈ xs, PosMon x)
    (out : Nat) : PosMon ((gs.foldl vstep xs).getD out (constant false)) := by
  have hz : PosMon (constant false) := fun _ _ _ h => h
  induction gs generalizing xs with
  | nil => exact in_getD PosMon h hz out
  | cons g gs ih =>
    apply ih (vstep xs g)
    intro x hx
    rcases List.mem_append.mp hx with hin | hg
    · exact h _ hin
    · rw [List.mem_singleton.mp hg]
      have ha := in_getD PosMon h hz g.2.1
      have hb := in_getD PosMon h hz g.2.2
      intro u v sub hh
      cases e : (!g.1) <;> simp only [eval,e,Bool.false_eq_true,ite_false,ite_true,
        Bool.and_eq_true_iff,Bool.or_eq_true_iff] at hh ⊢
      · exact ⟨ha u v sub hh.1,hb u v sub hh.2⟩
      · exact hh.elim (fun e=>.inl (ha u v sub e)) (fun e=>.inr (hb u v sub e))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem correspondence : (∀ i : Fin 21, primary.map (fun v => v (assignment (positive.getD i 0))) =
    baseWords.map (fun w => w.getLsbD i.val)) ∧
    (∀ i : Fin 36, primary.map (fun v => v (assignment (negative.getD i 0))) =
    baseWords.map (fun w => w.getLsbD (22+i.val))) := by decide +kernel

theorem posted_partial (gs : List Op) (out : Nat) (hm : MaskOK ((gs.foldl step baseWords).getD out 0)) :
    Partial (vout gs out) := by
  obtain ⟨pp,nn⟩ := bits_of_mask hm
  have mono : PosMon (vout gs out) := mon_output gs primary (by
    intro x hx
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
    exact fun _ _ h => h i) out
  have order (x y : M) (h : x &&& y = x) : ∀ i : I, assignment x i = true → assignment y i = true := by
    intro i e
    have bit := congrArg (fun z : M => z.getLsbD i.val) h
    change x.getLsbD i.val = true at e
    simpa [assignment,e] using bit
  constructor
  · intro m hi
    obtain ⟨x,hx,sub⟩ := List.any_eq_true.mp hi
    obtain ⟨i,hlen,he⟩ := List.mem_iff_getElem.mp hx
    have sz : i < 21 := hlen
    have get : positive.getD i 0 = x := by simpa [List.getD,hlen] using he
    have pos := prog_eval gs out _ _ (correspondence.1 ⟨i,sz⟩)
    rw [get, pp i sz] at pos
    exact mono _ _ (order x m (eq_of_beq sub)) pos
  · intro m hi
    obtain ⟨x,hx,sub⟩ := List.any_eq_true.mp hi
    obtain ⟨i,hlen,he⟩ := List.mem_iff_getElem.mp hx
    have sz : i < 36 := hlen
    have get : negative.getD i 0 = x := by simpa [List.getD,hlen] using he
    have neg := prog_eval gs out _ _ (correspondence.2 ⟨i,sz⟩)
    rw [get, nn i sz] at neg
    cases e : vout gs out (assignment m) with
    | false => rfl
    | true =>
      have wrong := mono _ _ (order m x (by simpa [BitVec.and_comm] using eq_of_beq sub)) e
      simp [neg] at wrong

theorem physical_build (gs : List Op) (ms pool : List V) (hs : ms ⊆ pool)
    (hz : constant false ∈ pool) (out : Nat) :
    Build G ((gs.foldl vstep ms).getD out (constant false)) gs.length pool := by
  induction gs generalizing ms pool with
  | nil => exact in_getD (· ∈ pool) (fun _ h => hs h) hz out
  | cons g gs ih =>
    let a := ms.getD g.2.1 (constant false)
    let b := ms.getD g.2.2 (constant false)
    let z := eval (!g.1) a b
    refine Or.inr ⟨a, in_getD (· ∈ pool) (fun _ h => hs h) hz _, b,
      in_getD (· ∈ pool) (fun _ h => hs h) hz _, z, ⟨!g.1,rfl⟩, ?_⟩
    apply ih (vstep ms g) (z::pool) _ (List.mem_cons_of_mem z hz)
    intro x hx
    rcases List.mem_append.mp hx with hm | hm
    · exact List.mem_cons_of_mem z (hs hm)
    · have eq : x = z := by simpa [z,a,b] using hm
      simp [eq]

theorem posted_lower_of_count {n : Nat} (h : CountBound 0 16383 n) (gs : List Op) (out : Nat)
    (ok : MaskOK ((gs.foldl step baseWords).getD out 0)) : n ≤ gs.length := by
  have lb := h (vout gs out) (posted_partial gs out ok)
  have full : indices 16383 = List.finRange 14 := by decide +kernel
  have sl : slice (vout gs out) 0 16383 = vout gs out := by
    funext u
    apply congrArg (vout gs out)
    funext i
    have ones : ∀ i : I, (16383 : M).getLsbD i.val = true := by decide +kernel
    change ((0 : M).getLsbD i.val || ((16383 : M).getLsbD i.val && u i)) = u i
    rw [ones i]
    simp
  apply lb gs.length
  rw [sl,full]
  exact physical_build gs primary _ (fun _ hw => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw))
    List.mem_cons_self out

end PEqualNP.Outside.L_meta_7737.States

namespace PEqualNP.Outside.L_meta_7737.States
open PEqualNP.Outside.L_meta_7737.Restriction PEqualNP.Outside.L_meta_7737.Slicing

noncomputable local instance : DecidableEq V := Classical.typeDecidableEq V

private theorem own_bit (i : I) (u : Assignment) : changeBit i (u i) u = u := by
  funext j
  by_cases h : j=i <;> simp [changeBit,h]

theorem const_canalizing_redundant (i : I) (o : Bool) (w : V) (mon : PosMon w)
    (hc : IsConst (proj i o w)) : eval o (raw i) w = raw i ∨ eval o (raw i) w = w := by
  cases o with
  | false =>
    rcases hc with h0|h1
    · right
      funext u
      cases hu : u i with
      | false =>
        have hh : w (changeBit i false u) = false := congrFun h0 u
        rw [←hu,own_bit] at hh
        simp [eval,raw,hu,hh]
      | true => simp [eval,raw,hu]
    · left
      funext u
      have hh : w (changeBit i false u) = true := congrFun h1 u
      have inc : ∀ j, changeBit i false u j = true → u j = true := by
        intro j; by_cases e : j=i <;> simp [changeBit,e]
      have := mon _ _ inc hh
      simp [eval,raw,this]
  | true =>
    rcases hc with h0|h1
    · left
      funext u
      have hh : w (changeBit i true u) = false := congrFun h0 u
      have inc : ∀ j, u j = true → changeBit i true u j = true := by
        intro j; by_cases e : j=i <;> simp [changeBit,e]
      have ew : w u = false := by
        cases e : w u with
        | false => rfl
        | true => have := mon _ _ inc e; simp [hh] at this
      simp [eval,raw,ew]
    · right
      funext u
      cases hu : u i with
      | false => simp [eval,raw,hu]
      | true =>
        have hh : w (changeBit i true u) = true := congrFun h1 u
        rw [←hu,own_bit] at hh
        simp [eval,raw,hu,hh]

theorem mon_gate {a b z : V} (g : G a b z) (ma : PosMon a) (mb : PosMon b) : PosMon z := by
  obtain ⟨o,rfl⟩ := g
  intro u v sub h
  cases o <;> simp only [eval,Bool.false_eq_true,ite_false,ite_true,
    Bool.and_eq_true_iff,Bool.or_eq_true_iff] at h ⊢
  · exact ⟨ma _ _ sub h.1,mb _ _ sub h.2⟩
  · exact h.elim (fun e => .inl (ma _ _ sub e)) (fun e => .inr (mb _ _ sub e))

private theorem simpl_gate {i : I} {v : Bool} {a b z : V} (g : G a b z)
    (dead : (fixed i v a || fixed i v b) = true) :
    proj i v z ∈ proj i v a :: proj i v b :: [constant false,constant true] := by
  obtain ⟨o,rfl⟩ := g
  rw [proj_eval]
  rcases Bool.or_eq_true_iff.mp dead with ha|hb
  · rcases fixed_eq.mp ha with h|h <;> rw [h,op_base] <;> cases o <;> simp
  · rw [op_swap]
    rcases fixed_eq.mp hb with h|h <;> rw [h,op_base] <;> cases o <;> simp

private theorem two_fixed {i : I} {v : Bool} {a b z : V} (g : G a b z)
    (ha : fixed i v a = true) (hb : fixed i v b = true) : fixed i v z = true := by
  obtain ⟨o,rfl⟩ := g
  apply fixed_eq.mpr
  rw [proj_eval]
  rcases fixed_eq.mp ha with ha|ha <;> rcases fixed_eq.mp hb with hb|hb <;>
    rw [ha,hb] <;> cases o <;> first | exact Or.inl rfl | exact Or.inr rfl

def Credit (f : V) (n : Nat) (s : List V) (i : I) (v : Bool) (e : Nat) :=
  ∃ k, Build G (proj i v f) k (s.map (proj i v) ++ [constant false,constant true]) ∧
    k + mass (fun w => (fixed i v w).toNat) s + e ≤ n + (fixed i v f).toNat

private theorem lift_credit {f : V} {n : Nat} {t : List V} {a b z : V} {e m : Nat} {i : I} {v : Bool}
    (g : G a b z) (hz : z ∈ t) (tail : Credit f n t i v e)
    (pay : (fixed i v a || fixed i v b) = true →
      (fixed i v a).toNat + (fixed i v b).toNat + m ≤ (fixed i v z).toNat + 1)
    (plain : (fixed i v a || fixed i v b) ≠ true → m = 0) :
    Credit f (n+1) (predList a b z t) i v (e+m) := by
  let prev := predList a b z t
  let p := proj i v
  let base := [constant false,constant true]
  let start := prev.map p ++ base
  let wt := fun w => (fixed i v w).toNat
  obtain ⟨k,run,num⟩ := tail
  have ha : a ∈ prev := by simp [prev,predList]
  have hb : b ∈ prev := by simp [prev,predList]
  have aa : p a ∈ start := List.mem_append_left _ (List.mem_map_of_mem ha)
  have bb : p b ∈ start := List.mem_append_left _ (List.mem_map_of_mem hb)
  have inc : t.map p ++ base ⊆ p z :: start := by
    intro x hx
    rcases List.mem_append.mp hx with hm | hu
    · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
      rcases List.mem_cons.mp ((List.perm_cons_erase hz).mem_iff.mp hw) with rfl | hr
      · exact List.mem_cons_self
      · have eh : w ∈ prev := by simp [prev,predList,hr]
        exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map_of_mem eh))
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ hu)
  have ec : mass wt prev ≤ wt a + wt b + mass wt (t.erase z) := by
    have a1 := mass_insert_le wt b (t.erase z)
    have a2 := mass_insert_le wt a ((t.erase z).insert b)
    change mass wt (((t.erase z).insert b).insert a) ≤ _
    omega
  have er := mass_move wt hz
  change k + mass wt t + e ≤ _ at num
  by_cases dead : (fixed i v a || fixed i v b) = true
  · have free : p z ∈ start := by
      rcases List.mem_cons.mp (simpl_gate g dead) with hit|rest
      · change p z = p a at hit
        rw [hit]; exact aa
      rcases List.mem_cons.mp rest with hit|inBase
      · change p z = p b at hit
        rw [hit]; exact bb
      · exact List.mem_append_right _ inBase
    have comp : Build G (p f) k start := run.mono (fun x hx => by
      rcases List.mem_cons.mp (inc hx) with rfl|hx
      · exact free
      · exact hx)
    have push : wt a + wt b + m ≤ wt z + 1 := pay dead
    refine ⟨k,comp,?_⟩
    change k + mass wt prev + (e+m) ≤ _
    omega
  · have sum : wt a + wt b = 0 := by
      cases ea : fixed i v a <;> cases eb : fixed i v b <;> simp_all [wt]
    have zero := plain dead
    obtain ⟨o,eq⟩ := g
    refine ⟨k+1, Or.inr ⟨p a,aa,p b,bb,p z,⟨o,eq ▸ proj_eval _ _ _ _ _⟩,run.mono inc⟩,?_⟩
    change k+1 + mass wt prev + (e+m) ≤ _
    omega

private theorem no_charge {i : I} {v : Bool} {a b z : V} (g : G a b z) :
    (fixed i v a || fixed i v b) = true →
    (fixed i v a).toNat + (fixed i v b).toNat + 0 ≤ (fixed i v z).toNat + 1 := by
  intro _
  cases ha : fixed i v a <;> cases hb : fixed i v b <;> simp
  rw [two_fixed g ha hb]; decide

private theorem extreme {i : I} {q : Bool} {b z : V} (g : z = eval q (raw i) b)
    (za : z ≠ raw i) (zb : z ≠ b) (mb : PosMon b) :
    fixed i q (raw i) = true ∧ fixed i q b = false ∧ fixed i q z = true := by
  have left : fixed i q (raw i) = true := fixed_eq.mpr (by
    rw [proj_raw]; cases q <;> simp [IsConst])
  have middle : fixed i q b = false := by
    cases e : fixed i q b with
    | false => rfl
    | true =>
      rcases const_canalizing_redundant i q b mb (fixed_eq.mp e) with h|h
      · exact False.elim (za (g.trans h))
      · exact False.elim (zb (g.trans h))
  have right : fixed i q z = true := fixed_eq.mpr (by
    rw [g,proj_eval,proj_raw]
    simp only [ite_true]
    rw [op_base]
    cases q <;> simp [IsConst])
  exact ⟨left,middle,right⟩

theorem second_read {f : V} {n : Nat} {s : List V} {i : I}
    (h : Flow G f n s) (hs : ∀ w ∈ s, PosMon w) (rawIn : raw i ∈ s) (nf : f ≠ raw i) :
    ∃ v, Credit f n s i v 1 := by
  induction h with
  | done => exact False.elim (nf (List.mem_singleton.mp rawIn).symm)
  | @step n t a b z g hz fresh tail ih =>
    have ha : a ∈ predList a b z t := by simp [predList]
    have hb : b ∈ predList a b z t := by simp [predList]
    by_cases next : raw i ∈ t
    · have mt : ∀ w ∈ t, PosMon w := by
        intro w hw
        rcases List.mem_cons.mp ((List.perm_cons_erase hz).mem_iff.mp hw) with rfl|hr
        · exact mon_gate g (hs _ ha) (hs _ hb)
        · exact hs _ (by simp [predList,hr])
      obtain ⟨v,hv⟩ := ih mt next
      exact ⟨v,lift_credit g hz hv (no_charge g) (fun _ => rfl)⟩
    · have which : raw i = a ∨ raw i = b := by
        simp only [predList,List.mem_insert_iff] at rawIn
        exact rawIn.elim Or.inl (fun h => h.elim Or.inr (fun hr => False.elim (next (List.mem_of_mem_erase hr))))
      obtain ⟨q,eq⟩ := g
      have norm : Credit f n t i q 0 := by
        simpa only [Credit,Nat.add_zero] using projection tail i q
      rcases which with rfl|rfl
      · obtain ⟨aa,bb,zz⟩ := extreme eq (fun e=>fresh (e ▸ ha)) (fun e=>fresh (e ▸ hb)) (hs _ hb)
        exact ⟨q,lift_credit ⟨q,eq⟩ hz norm (m:=1) (by simp [aa,bb,zz]) (by simp [aa])⟩
      · obtain ⟨aa,bb,zz⟩ := extreme (eq.trans (op_swap _ _ _)) (fun e=>fresh (e ▸ hb)) (fun e=>fresh (e ▸ ha)) (hs _ ha)
        exact ⟨q,lift_credit ⟨q,eq⟩ hz norm (m:=1) (by simp [aa,bb,zz]) (by simp [aa])⟩

end PEqualNP.Outside.L_meta_7737.States

namespace PEqualNP.Outside.L_meta_7737.States
open PEqualNP.Outside.L_meta_7737.Slicing PEqualNP.Outside.L_meta_7737.Restriction

private theorem base_mono (A : List I) {x : V} (h : x ∈ base A) : PosMon x := by
  rcases List.mem_cons.mp h with rfl|h
  · exact fun _ _ _ h => h
  rcases List.mem_cons.mp h with rfl|h
  · exact fun _ _ _ h => h
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp h
  exact fun _ _ sub => sub i

theorem extra_first {f : V} {A : List I} {k : Nat} (p : First f A k)
    (surv : Essential (proj p.y p.o f) p.x)
    (nc : ∀ b, ¬ IsConst (proj p.x b f))
    (lb : Bool → Nat) (low : ∀ b, LB (A.erase p.x) (proj p.x b f) (lb b)) :
    ∃ b, lb b + 3 + (p.o == b).toNat ≤ k := by
  classical
  have rx := p.survives surv
  have allMon : ∀ w ∈ p.t, PosMon w := by
    intro w hw
    rcases List.mem_cons.mp (p.sub hw) with rfl|h
    · exact mon_gate ⟨p.o,p.gate⟩ (fun _ _ sub => sub p.x) (fun _ _ sub => sub p.y)
    · exact base_mono _ h
  have nf : f ≠ raw p.x := by
    intro eq
    apply nc false
    have he := congrArg (proj p.x false) eq
    exact .inl (he.trans (by simp [proj_raw]))
  obtain ⟨b,j,run,cost⟩ := second_read p.ht allMon rx nf
  let new := base (A.erase p.x)
  have pin : ∀ w ∈ p.t, proj p.x b w ∈ new := by
    intro w hw
    rcases List.mem_cons.mp (p.sub hw) with rfl|h
    · rw [p.cofactor_gate]
      split
      · exact const_in_base _ _
      · change raw p.y ∈ base (A.erase p.x)
        have hy : p.y ∈ A.erase p.x := (List.mem_erase_of_ne p.xy.symm).mpr p.ymem
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hy))
    · exact base_proj _ _ _ h
  have cut := low b j (run.mono (projection_bank pin (const_in_base _ _) (const_in_base _ _)))
  have fzero : fixed p.x b f = false := by simp [fixed,nc b]
  let c := fun w => (fixed p.x b w).toNat
  have cf : c (raw p.x) = 1 := by
    have e : fixed p.x b (raw p.x) = true := fixed_eq.mpr (by
      rw [proj_raw]; cases b <;> simp [IsConst])
    simp [c,e]
  have cz (eq : (p.o == b) = true) : c p.z = 1 := by
    have e : fixed p.x b p.z = true := fixed_eq.mpr (by
      rw [p.cofactor_gate,eq]; cases b <;> simp [IsConst])
    simp [c,e]
  have massLB : 1 + (p.o == b).toNat ≤ mass c p.t := by
    cases eq : (p.o == b) with
    | false =>
      have v := mass_subset c (xs:=[raw p.x]) (by simp)
        (show [raw p.x] ⊆ p.t by simpa using rx)
      simpa [mass,cf] using v
    | true =>
      have nd : [p.z,raw p.x].Nodup := by simp [p.zx]
      have sub : [p.z,raw p.x] ⊆ p.t := by simp [p.hz,rx]
      have v := mass_subset c nd sub
      simpa [mass,cz eq,cf] using v
  change j + mass c p.t + 1 ≤ p.n + (fixed p.x b f).toNat at cost
  rw [fzero] at cost
  simp only [Bool.toNat_false,Nat.add_zero] at cost
  have cap := p.cap
  exact ⟨b,by omega⟩

end PEqualNP.Outside.L_meta_7737.States

namespace PEqualNP.Outside.L_meta_7737.States

open PEqualNP.Outside.L_meta_7737.Restriction

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm1 : Sym (permCode 61863585619522576) := by
  exact sym_from_check _ (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm2 : Sym (permCode 44113344757904656) := by
  exact sym_from_check _ (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm3 : Sym (permCode 43851652369036816) := by
  have eq : (fun i : I => permCode 61863585619522576 (permCode 44113344757904656 i)) = permCode 43851652369036816 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm1 perm2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm4 : Sym (permCode 61285436010815776) := by
  exact sym_from_check _ (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm12 : Sym (permCode 61300760991912256) := by
  have eq : (fun i : I => permCode 61863585619522576 (permCode 61285436010815776 i)) = permCode 61300760991912256 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm1 perm4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm16 : Sym (permCode 44394738918768976) := by
  have eq : (fun i : I => permCode 44113344757904656 (permCode 61285436010815776 i)) = permCode 44394738918768976 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm2 perm4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm20 : Sym (permCode 44414460873744736) := by
  have eq : (fun i : I => permCode 43851652369036816 (permCode 61285436010815776 i)) = permCode 44414460873744736 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm3 perm4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm6 : Sym (permCode 61809915973428256) := by
  have eq : (fun i : I => permCode 61285436010815776 (permCode 61863585619522576 i)) = permCode 61809915973428256 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm4 perm1

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm7 : Sym (permCode 56778619465458976) := by
  have eq : (fun i : I => permCode 61285436010815776 (permCode 44113344757904656 i)) = permCode 56778619465458976 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm4 perm2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm13 : Sym (permCode 62091314194371136) := by
  have eq : (fun i : I => permCode 61300760991912256 (permCode 61863585619522576 i)) = permCode 62091314194371136 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm12 perm1

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm15 : Sym (permCode 52292603937510976) := by
  have eq : (fun i : I => permCode 61300760991912256 (permCode 44113344757904656 i)) = permCode 52292603937510976 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm12 perm2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm19 : Sym (permCode 43865878104720976) := by
  have eq : (fun i : I => permCode 44394738918768976 (permCode 61863585619522576 i)) = permCode 43865878104720976 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm16 perm1

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm17 : Sym (permCode 57904236474876496) := by
  have eq : (fun i : I => permCode 44394738918768976 (permCode 44113344757904656 i)) = permCode 57904236474876496 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm16 perm2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm23 : Sym (permCode 44147292448564576) := by
  have eq : (fun i : I => permCode 44414460873744736 (permCode 61863585619522576 i)) = permCode 44147292448564576 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm20 perm1

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm22 : Sym (permCode 53418237069829216) := by
  have eq : (fun i : I => permCode 44414460873744736 (permCode 44113344757904656 i)) = permCode 53418237069829216 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm20 perm2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm5 : Sym (permCode 57309670649717536) := by
  have eq : (fun i : I => permCode 61809915973428256 (permCode 44113344757904656 i)) = permCode 57309670649717536 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm6 perm2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm14 : Sym (permCode 53085347510637376) := by
  have eq : (fun i : I => permCode 62091314194371136 (permCode 44113344757904656 i)) = permCode 53085347510637376 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm13 perm2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm18 : Sym (permCode 57377566031496016) := by
  have eq : (fun i : I => permCode 43865878104720976 (permCode 44113344757904656 i)) = permCode 57377566031496016 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm19 perm2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm21 : Sym (permCode 53157639866295136) := by
  have eq : (fun i : I => permCode 44147292448564576 (permCode 44113344757904656 i)) = permCode 53157639866295136 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm23 perm2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm8 : Sym (permCode 57872487274582576) := by
  have eq : (fun i : I => permCode 57309670649717536 (permCode 61285436010815776 i)) = permCode 57872487274582576 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm5 perm4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm9 : Sym (permCode 53366765914559536) := by
  have eq : (fun i : I => permCode 53085347510637376 (permCode 61285436010815776 i)) = permCode 53366765914559536 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm14 perm4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm10 : Sym (permCode 56814765646943536) := by
  have eq : (fun i : I => permCode 57377566031496016 (permCode 61285436010815776 i)) = permCode 56814765646943536 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm18 perm4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm11 : Sym (permCode 52313425137899056) := by
  have eq : (fun i : I => permCode 53157639866295136 (permCode 61285436010815776 i)) = permCode 52313425137899056 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm21 perm4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm24 : Sym (permCode 39610651371778561) := by
  exact sym_from_check _ (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm25 : Sym (permCode 48353830364328961) := by
  have eq : (fun i : I => permCode 61863585619522576 (permCode 39610651371778561 i)) = permCode 48353830364328961 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm1 perm24

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm26 : Sym (permCode 48622094084486401) := by
  have eq : (fun i : I => permCode 44113344757904656 (permCode 39610651371778561 i)) = permCode 48622094084486401 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm2 perm24

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm27 : Sym (permCode 39351149463221761) := by
  have eq : (fun i : I => permCode 43851652369036816 (permCode 39610651371778561 i)) = permCode 39351149463221761 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm3 perm24

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm48 : Sym (permCode 34265925617410306) := by
  have eq : (fun i : I => permCode 61285436010815776 (permCode 39610651371778561 i)) = permCode 34265925617410306 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm4 perm24

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm120 : Sym (permCode 35391671472701701) := by
  have eq : (fun i : I => permCode 44394738918768976 (permCode 39610651371778561 i)) = permCode 35391671472701701 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm16 perm24

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm144 : Sym (permCode 35408301034512646) := by
  have eq : (fun i : I => permCode 44414460873744736 (permCode 39610651371778561 i)) = permCode 35408301034512646 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm20 perm24

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm50 : Sym (permCode 48304283870127106) := by
  have eq : (fun i : I => permCode 61809915973428256 (permCode 39610651371778561 i)) = permCode 48304283870127106 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm6 perm24

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm51 : Sym (permCode 47777613536847106) := by
  have eq : (fun i : I => permCode 56778619465458976 (permCode 39610651371778561 i)) = permCode 47777613536847106 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm7 perm24

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm97 : Sym (permCode 39577460617400836) := by
  have eq : (fun i : I => permCode 62091314194371136 (permCode 39610651371778561 i)) = permCode 39577460617400836 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm13 perm24

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm99 : Sym (permCode 38788002709919236) := by
  have eq : (fun i : I => permCode 52292603937510976 (permCode 39610651371778561 i)) = permCode 38788002709919236 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm15 perm24

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm121 : Sym (permCode 39891916679430661) := by
  have eq : (fun i : I => permCode 57904236474876496 (permCode 39610651371778561 i)) = permCode 39891916679430661 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm17 perm24

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm147 : Sym (permCode 48655010899436806) := by
  have eq : (fun i : I => permCode 44147292448564576 (permCode 39610651371778561 i)) = permCode 48655010899436806 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm23 perm24

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm146 : Sym (permCode 48916703288304646) := by
  have eq : (fun i : I => permCode 53418237069829216 (permCode 39610651371778561 i)) = permCode 48916703288304646 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm22 perm24

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm49 : Sym (permCode 34794786431001346) := by
  have eq : (fun i : I => permCode 57309670649717536 (permCode 39610651371778561 i)) = permCode 34794786431001346 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm5 perm24

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm98 : Sym (permCode 35076120225338116) := by
  have eq : (fun i : I => permCode 53085347510637376 (permCode 39610651371778561 i)) = permCode 35076120225338116 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm14 perm24

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm145 : Sym (permCode 35142227794666246) := by
  have eq : (fun i : I => permCode 53157639866295136 (permCode 39610651371778561 i)) = permCode 35142227794666246 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm21 perm24

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm72 : Sym (permCode 39859136720409091) := by
  have eq : (fun i : I => permCode 57872487274582576 (permCode 39610651371778561 i)) = permCode 39859136720409091 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm8 perm24

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm73 : Sym (permCode 48867293767472131) := by
  have eq : (fun i : I => permCode 53366765914559536 (permCode 39610651371778561 i)) = permCode 48867293767472131 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm9 perm24

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm74 : Sym (permCode 47810667325166851) := by
  have eq : (fun i : I => permCode 56814765646943536 (permCode 39610651371778561 i)) = permCode 47810667325166851 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm10 perm24

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm75 : Sym (permCode 38804700758414851) := by
  have eq : (fun i : I => permCode 52313425137899056 (permCode 39610651371778561 i)) = permCode 38804700758414851 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm11 perm24

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm28 : Sym (permCode 39047814681346081) := by
  have eq : (fun i : I => permCode 39610651371778561 (permCode 61285436010815776 i)) = permCode 39047814681346081 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm24 perm4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm36 : Sym (permCode 47509587450208321) := by
  have eq : (fun i : I => permCode 48353830364328961 (permCode 61285436010815776 i)) = permCode 47509587450208321 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm25 perm4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm40 : Sym (permCode 47496460952166481) := by
  have eq : (fun i : I => permCode 48622094084486401 (permCode 61285436010815776 i)) = permCode 47496460952166481 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm26 perm4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm44 : Sym (permCode 39069735119376481) := by
  have eq : (fun i : I => permCode 39351149463221761 (permCode 61285436010815776 i)) = permCode 39069735119376481 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm27 perm4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm52 : Sym (permCode 34547311775531026) := by
  have eq : (fun i : I => permCode 34265925617410306 (permCode 61285436010815776 i)) = permCode 34547311775531026 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm48 perm4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm124 : Sym (permCode 33984644179517461) := by
  have eq : (fun i : I => permCode 35391671472701701 (permCode 61285436010815776 i)) = permCode 33984644179517461 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm120 perm4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm148 : Sym (permCode 34564078185959446) := by
  have eq : (fun i : I => permCode 35408301034512646 (permCode 61285436010815776 i)) = permCode 34564078185959446 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm144 perm4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm60 : Sym (permCode 47178638792396866) := by
  have eq : (fun i : I => permCode 48304283870127106 (permCode 61285436010815776 i)) = permCode 47178638792396866 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm50 perm4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm64 : Sym (permCode 47214784966570066) := by
  have eq : (fun i : I => permCode 47777613536847106 (permCode 61285436010815776 i)) = permCode 47214784966570066 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm51 perm4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm104 : Sym (permCode 38170417318727716) := by
  have eq : (fun i : I => permCode 39577460617400836 (permCode 61285436010815776 i)) = permCode 38170417318727716 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm97 perm4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm116 : Sym (permCode 38225186202464356) := by
  have eq : (fun i : I => permCode 38788002709919236 (permCode 61285436010815776 i)) = permCode 38225186202464356 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm99 perm4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm128 : Sym (permCode 38203471099736101) := by
  have eq : (fun i : I => permCode 39891916679430661 (permCode 61285436010815776 i)) = permCode 38203471099736101 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm121 perm4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm164 : Sym (permCode 47247975603507286) := by
  have eq : (fun i : I => permCode 48655010899436806 (permCode 61285436010815776 i)) = permCode 47247975603507286 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm147 perm4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm56 : Sym (permCode 34513364084412466) := by
  have eq : (fun i : I => permCode 34794786431001346 (permCode 61285436010815776 i)) = permCode 34513364084412466 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm49 perm4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm108 : Sym (permCode 33950491153096756) := by
  have eq : (fun i : I => permCode 35076120225338116 (permCode 61285436010815776 i)) = permCode 33950491153096756 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm98 perm4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm156 : Sym (permCode 34579403167055926) := by
  have eq : (fun i : I => permCode 35142227794666246 (permCode 61285436010815776 i)) = permCode 34579403167055926 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm145 perm4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm80 : Sym (permCode 39014897748955171) := by
  have eq : (fun i : I => permCode 39859136720409091 (permCode 61285436010815776 i)) = permCode 39014897748955171 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm72 perm4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm84 : Sym (permCode 47460246291308611) := by
  have eq : (fun i : I => permCode 48867293767472131 (permCode 61285436010815776 i)) = permCode 47460246291308611 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm73 perm4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm88 : Sym (permCode 47529240918499411) := by
  have eq : (fun i : I => permCode 47810667325166851 (permCode 61285436010815776 i)) = permCode 47529240918499411 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm74 perm4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm92 : Sym (permCode 39086090859200611) := by
  have eq : (fun i : I => permCode 38804700758414851 (permCode 61285436010815776 i)) = permCode 39086090859200611 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm75 perm4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm31 : Sym (permCode 39309507069756961) := by
  have eq : (fun i : I => permCode 39047814681346081 (permCode 61863585619522576 i)) = permCode 39309507069756961 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm28 perm1

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm30 : Sym (permCode 57059747924493601) := by
  have eq : (fun i : I => permCode 39047814681346081 (permCode 44113344757904656 i)) = permCode 57059747924493601 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm28 perm2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm38 : Sym (permCode 48562928226411841) := by
  have eq : (fun i : I => permCode 47509587450208321 (permCode 61863585619522576 i)) = permCode 48562928226411841 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm36 perm1

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm43 : Sym (permCode 48281538008212561) := by
  have eq : (fun i : I => permCode 47496460952166481 (permCode 61863585619522576 i)) = permCode 48281538008212561 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm40 perm1

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm41 : Sym (permCode 56496951482606161) := by
  have eq : (fun i : I => permCode 47496460952166481 (permCode 44113344757904656 i)) = permCode 56496951482606161 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm40 perm2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm45 : Sym (permCode 39590929416344161) := by
  have eq : (fun i : I => permCode 39069735119376481 (permCode 61863585619522576 i)) = permCode 39590929416344161 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm44 perm1

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm125 : Sym (permCode 61003639174750741) := by
  have eq : (fun i : I => permCode 33984644179517461 (permCode 44113344757904656 i)) = permCode 61003639174750741 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm124 perm2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm150 : Sym (permCode 35088558148571926) := by
  have eq : (fun i : I => permCode 34564078185959446 (permCode 61863585619522576 i)) = permCode 35088558148571926 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm148 perm1

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm151 : Sym (permCode 61581977995858966) := by
  have eq : (fun i : I => permCode 34564078185959446 (permCode 44113344757904656 i)) = permCode 61581977995858966 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm148 perm2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm62 : Sym (permCode 47702023459575106) := by
  have eq : (fun i : I => permCode 47178638792396866 (permCode 61863585619522576 i)) = permCode 47702023459575106 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm60 perm1

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm61 : Sym (permCode 51677788813792066) := by
  have eq : (fun i : I => permCode 47178638792396866 (permCode 44113344757904656 i)) = permCode 51677788813792066 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm60 perm2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm66 : Sym (permCode 48264839967028306) := by
  have eq : (fun i : I => permCode 47214784966570066 (permCode 61863585619522576 i)) = permCode 48264839967028306 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm64 perm1

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm105 : Sym (permCode 56183445747208996) := by
  have eq : (fun i : I => permCode 38170417318727716 (permCode 44113344757904656 i)) = permCode 56183445747208996 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm104 perm2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm118 : Sym (permCode 39541314442768996) := by
  have eq : (fun i : I => permCode 38225186202464356 (permCode 61863585619522576 i)) = permCode 39541314442768996 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm116 perm1

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm129 : Sym (permCode 60722220888240421) := by
  have eq : (fun i : I => permCode 38203471099736101 (permCode 44113344757904656 i)) = permCode 60722220888240421 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm128 perm2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm167 : Sym (permCode 48827986712990806) := by
  have eq : (fun i : I => permCode 47247975603507286 (permCode 61863585619522576 i)) = permCode 48827986712990806 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm164 perm1

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm57 : Sym (permCode 34244005178921266) := by
  have eq : (fun i : I => permCode 34513364084412466 (permCode 61863585619522576 i)) = permCode 34244005178921266 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm56 perm1

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm58 : Sym (permCode 52522011544933426) := by
  have eq : (fun i : I => permCode 34513364084412466 (permCode 44113344757904656 i)) = permCode 52522011544933426 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm56 perm2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm109 : Sym (permCode 34211088246530356) := by
  have eq : (fun i : I => permCode 33950491153096756 (permCode 61863585619522576 i)) = permCode 34211088246530356 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm108 perm1

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm157 : Sym (permCode 35369956369514806) := by
  have eq : (fun i : I => permCode 34579403167055926 (permCode 61863585619522576 i)) = permCode 35369956369514806 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm156 perm1

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm82 : Sym (permCode 61528171501147171) := by
  have eq : (fun i : I => permCode 39014897748955171 (permCode 44113344757904656 i)) = permCode 61528171501147171 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm80 perm2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm86 : Sym (permCode 60965362996437571) := by
  have eq : (fun i : I => permCode 47460246291308611 (permCode 44113344757904656 i)) = permCode 60965362996437571 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm84 perm2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm90 : Sym (permCode 48844274083570771) := by
  have eq : (fun i : I => permCode 47529240918499411 (permCode 61863585619522576 i)) = permCode 48844274083570771 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm88 perm1

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm94 : Sym (permCode 39872263210680931) := by
  have eq : (fun i : I => permCode 39086090859200611 (permCode 61863585619522576 i)) = permCode 39872263210680931 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm92 perm1

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm29 : Sym (permCode 57325821054239521) := by
  have eq : (fun i : I => permCode 39309507069756961 (permCode 44113344757904656 i)) = permCode 57325821054239521 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm31 perm2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm37 : Sym (permCode 53068649469453121) := by
  have eq : (fun i : I => permCode 48562928226411841 (permCode 44113344757904656 i)) = permCode 53068649469453121 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm38 perm2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm42 : Sym (permCode 57295171091587921) := by
  have eq : (fun i : I => permCode 48281538008212561 (permCode 44113344757904656 i)) = permCode 57295171091587921 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm43 perm2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm127 : Sym (permCode 61797477932753941) := by
  have eq : (fun i : I => permCode 48281538008212561 (permCode 39610651371778561 i)) = permCode 61797477932753941 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm43 perm24

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm46 : Sym (permCode 53108093372093281) := by
  have eq : (fun i : I => permCode 39590929416344161 (permCode 44113344757904656 i)) = permCode 53108093372093281 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm45 perm2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm149 : Sym (permCode 62113029180117526) := by
  have eq : (fun i : I => permCode 39590929416344161 (permCode 39610651371778561 i)) = permCode 62113029180117526 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm45 perm24

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm63 : Sym (permCode 52209935182927426) := by
  have eq : (fun i : I => permCode 47702023459575106 (permCode 44113344757904656 i)) = permCode 52209935182927426 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm62 perm2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm106 : Sym (permCode 56712306450699556) := by
  have eq : (fun i : I => permCode 47702023459575106 (permCode 39610651371778561 i)) = permCode 56712306450699556 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm62 perm24

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm130 : Sym (permCode 61776656739677221) := by
  have eq : (fun i : I => permCode 48264839967028306 (permCode 39610651371778561 i)) = permCode 61776656739677221 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm66 perm24

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm162 : Sym (permCode 62058260295922246) := by
  have eq : (fun i : I => permCode 39541314442768996 (permCode 39610651371778561 i)) = permCode 62058260295922246 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm118 perm24

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm59 : Sym (permCode 52263604821710386) := by
  have eq : (fun i : I => permCode 34244005178921266 (permCode 44113344757904656 i)) = permCode 52263604821710386 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm57 perm2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm81 : Sym (permCode 61268669482946851) := by
  have eq : (fun i : I => permCode 34244005178921266 (permCode 39610651371778561 i)) = permCode 61268669482946851 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm57 perm24

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm85 : Sym (permCode 61234721791828291) := by
  have eq : (fun i : I => permCode 34211088246530356 (permCode 39610651371778561 i)) = permCode 61234721791828291 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm109 perm24

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm158 : Sym (permCode 57888706041037366) := by
  have eq : (fun i : I => permCode 35369956369514806 (permCode 44113344757904656 i)) = permCode 57888706041037366 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm157 perm2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm32 : Sym (permCode 56481626508821041) := by
  have eq : (fun i : I => permCode 57325821054239521 (permCode 61285436010815776 i)) = permCode 56481626508821041 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm29 perm4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm33 : Sym (permCode 52505861147722801) := by
  have eq : (fun i : I => permCode 53068649469453121 (permCode 61285436010815776 i)) = permCode 52505861147722801 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm37 perm4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm34 : Sym (permCode 57013772988056881) := by
  have eq : (fun i : I => permCode 57295171091587921 (permCode 61285436010815776 i)) = permCode 57013772988056881 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm42 perm4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm136 : Sym (permCode 60671848977924421) := by
  have eq : (fun i : I => permCode 61797477932753941 (permCode 61285436010815776 i)) = permCode 60671848977924421 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm127 perm4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm152 : Sym (permCode 60706002004345126) := by
  have eq : (fun i : I => permCode 62113029180117526 (permCode 61285436010815776 i)) = permCode 60706002004345126 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm149 perm4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm113 : Sym (permCode 56430912289833556) := by
  have eq : (fun i : I => permCode 56712306450699556 (permCode 61285436010815776 i)) = permCode 56430912289833556 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm106 perm4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm137 : Sym (permCode 60932446071358021) := by
  have eq : (fun i : I => permCode 61776656739677221 (permCode 61285436010815776 i)) = permCode 60932446071358021 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm130 perm4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm154 : Sym (permCode 61495459911369766) := by
  have eq : (fun i : I => permCode 62058260295922246 (permCode 61285436010815776 i)) = permCode 61495459911369766 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm162 perm4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm76 : Sym (permCode 60987283442237971) := by
  have eq : (fun i : I => permCode 61268669482946851 (permCode 61285436010815776 i)) = permCode 60987283442237971 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm81 perm4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem perm77 : Sym (permCode 61516144255829011) := by
  have eq : (fun i : I => permCode 61234721791828291 (permCode 61285436010815776 i)) = permCode 61516144255829011 := funext (by decide +kernel)
  exact eq ▸ sym_comp perm85 perm4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_131_131 : Witnessed 0 131 131 := witness_check 254422546068206553797994320333635592 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_133_129 : Witnessed 0 133 129 := witness_check 254422546068206553797994320131784712 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_259_1 : Witnessed 0 259 1 := witness_check 1049 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_385_129 : Witnessed 0 385 129 := witness_check 254422546068206553797994320131784712 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_385_385 : Witnessed 0 385 385 := witness_check 365123234128713039502754751768607422677000 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_386_2 : Witnessed 0 386 2 := witness_check 201850880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_386_130 : Witnessed 0 386 130 := witness_check 16044197292872617372159233657491947520 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_387_387 : Witnessed 0 387 387 := witness_check 365123234128713039502754751768607624527880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_405_1 : Witnessed 0 405 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_407_2 : Witnessed 0 407 2 := witness_check 201850880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_407_391 : Witnessed 0 407 391 := witness_check 365123234128713039502754751795103277776904 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_409_1 : Witnessed 0 409 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_413_4 : Witnessed 0 413 4 := witness_check 26495653249024 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_423_391 : Witnessed 0 423 391 := witness_check 365123234128713039502754751795103277776904 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_462_462 : Witnessed 0 462 462 := witness_check 2091731755122615803052515346432458211459072 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_643_1 : Witnessed 0 643 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_679_163 : Witnessed 0 679 163 := witness_check 254422564707424840616346935953457160 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_807_39 : Witnessed 0 807 39 := witness_check 18639218286818379111545308185 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_899_1 : Witnessed 0 899 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_899_256 : Witnessed 0 899 256 := witness_check 365122979706166971296200953774287290892288 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_903_519 : Witnessed 0 903 519 := witness_check 91745265746754983604277944973675385731458531336 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_903_903 : Witnessed 0 903 903 := witness_check 91745630869989112317317447728427154338881208328 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_907_8 : Witnessed 0 907 8 := witness_check 2596325185179090944 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_907_907 : Witnessed 0 907 907 := witness_check 91745630869989112317317447731023453028407050248 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_910_4 : Witnessed 0 910 4 := witness_check 26495653249024 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_931_259 : Witnessed 0 931 259 := witness_check 365122979706166971296200953774287492743176 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_933_1 : Witnessed 0 933 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_934_2 : Witnessed 0 934 2 := witness_check 201850880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_935_1 : Witnessed 0 935 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_935_935 : Witnessed 0 935 935 := witness_check 91745630869989112335956666015245506954501029896 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_940_940 : Witnessed 0 940 940 := witness_check 342675342484287072005639642607748974373219860480 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_943_8 : Witnessed 0 943 8 := witness_check 2596325185179090944 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_951_1 : Witnessed 0 951 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_959_8 : Witnessed 0 959 8 := witness_check 2596325185179090944 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_959_943 : Witnessed 0 959 943 := witness_check 91745630869989112335956666017841832139680120840 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_990_2 : Witnessed 0 990 2 := witness_check 201850880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_991_1 : Witnessed 0 991 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_994_930 : Witnessed 0 994 930 := witness_check 91751540229362836100117581797039379882766237696 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1006_2 : Witnessed 0 1006 2 := witness_check 201850880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1007_1 : Witnessed 0 1007 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1022_494 : Witnessed 0 1022 494 := witness_check 2091731755122634442270802164785073831280640 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1155_1 : Witnessed 0 1155 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1175_147 : Witnessed 0 1175 147 := witness_check 254422546068435201190787950225915912 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1303_21 : Witnessed 0 1303 21 := witness_check 228647392820125545530393 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1411_256 : Witnessed 0 1411 256 := witness_check 365122979706166971296200953774287290892288 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1413_1 : Witnessed 0 1413 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1415_2 : Witnessed 0 1415 2 := witness_check 201850880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1415_1031 : Witnessed 0 1415 1031 := witness_check 3064768933482903419473127094206045492244986397720584 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1415_1415 : Witnessed 0 1415 1415 := witness_check 3064768933848026653601840133708800244013593820397576 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1427_259 : Witnessed 0 1427 259 := witness_check 365122979706166971296200953774287492743176 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1429_129 : Witnessed 0 1429 129 := witness_check 254422546068206553797994320131784712 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1430_2 : Witnessed 0 1430 2 := witness_check 201850880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1430_1430 : Witnessed 0 1430 1430 := witness_check 17966239629800521327138199256336650424567240984100864 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1431_1 : Witnessed 0 1431 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1431_1431 : Witnessed 0 1431 1431 := witness_check 3064768933848026653601840133937447636807223712677896 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1433_1 : Witnessed 0 1433 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1437_1 : Witnessed 0 1437 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1437_4 : Witnessed 0 1437 4 := witness_check 26495653249024 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1439_2 : Witnessed 0 1439 2 := witness_check 201850880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1469_1 : Witnessed 0 1469 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1471_2 : Witnessed 0 1471 2 := witness_check 201850880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1471_63 : Witnessed 0 1471 63 := witness_check 19936624341253995031006019592 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1506_386 : Witnessed 0 1506 386 := witness_check 6274482607852477200418536545668031542984704 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1534_1534 : Witnessed 0 1534 1534 := witness_check 17966239629800521328600533388258121164706186934091776 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1667_1 : Witnessed 0 1667 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1675_1673 : Witnessed 0 1675 1673 := witness_check 3064860678748650428879277440357575561897231456927752 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1683_1681 : Witnessed 0 1683 1681 := witness_check 3064860678748650428879277440586220358365676170117128 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1722_1722 : Witnessed 0 1722 1722 := witness_check 17966331372974552372658813438590549802694702537375744 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1727_699 : Witnessed 0 1727 699 := witness_check 91745265747009406168985598464280824986628259848 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1762_194 : Witnessed 0 1762 194 := witness_check 16045743351235920726443034074138804224 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1787_1787 : Witnessed 0 1787 1787 := witness_check 3064860678748650430425354443107864056843893817737224 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1790_250 : Witnessed 0 1790 250 := witness_check 16045743369875367663250505504829997056 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1826_2 : Witnessed 0 1826 2 := witness_check 272236544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1855_567 : Witnessed 0 1855 567 := witness_check 91745265746754983622917391907886531977041019929 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1890_2 : Witnessed 0 1890 2 := witness_check 272236544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1918_118 : Witnessed 0 1918 118 := witness_check 1462332834972711090136782128939008 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1923_1 : Witnessed 0 1923 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1923_256 : Witnessed 0 1923 256 := witness_check 365122979706166971296200953774287290892288 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1931_1 : Witnessed 0 1931 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1931_8 : Witnessed 0 1931 8 := witness_check 2596325185179090944 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1935_4 : Witnessed 0 1935 4 := witness_check 26495653249024 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1943_1 : Witnessed 0 1943 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1943_512 : Witnessed 0 1943 512 := witness_check 91745265746754983604277944973675359235603431424 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1951_8 : Witnessed 0 1951 8 := witness_check 2596325185179090944 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1951_31 : Witnessed 0 1951 31 := witness_check 228649989145310926471176 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1954_128 : Witnessed 0 1954 128 := witness_check 16044197292872617372159233657290096640 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1954_1698 : Witnessed 0 1954 1698 := witness_check 23954103581119261628539310198000511345106243094577152 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1966_2 : Witnessed 0 1966 2 := witness_check 201850880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1966_4 : Witnessed 0 1966 4 := witness_check 26495653249024 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1967_1 : Witnessed 0 1967 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1967_1039 : Witnessed 0 1967 1039 := witness_check 3064768933482903419473127094206048088570171576811528 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1975_135 : Witnessed 0 1975 135 := witness_check 254422546068206553798020815986884616 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1977_1 : Witnessed 0 1977 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1979_2 : Witnessed 0 1979 2 := witness_check 201850880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1979_259 : Witnessed 0 1979 259 := witness_check 365122979706166971296200953774287492743176 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1981_1 : Witnessed 0 1981 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1982_2 : Witnessed 0 1982 2 := witness_check 201850880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1982_4 : Witnessed 0 1982 4 := witness_check 26495653249024 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1982_62 : Witnessed 0 1982 62 := witness_check 18639446936807497926546292736 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1983_1 : Witnessed 0 1983 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1983_1727 : Witnessed 0 1983 1727 := witness_check 3064860678748650428879296079804509773069972824129544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1983_1983 : Witnessed 0 1983 1983 := witness_check 3064860679113773408585463051100710726844260115021832 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_1986_898 : Witnessed 0 1986 898 := witness_check 91751540229362836081478363510221027267146416128 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_2014_30 : Witnessed 0 2014 30 := witness_check 228649989145310926471168 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_2015_1759 : Witnessed 0 2015 1759 := witness_check 3064860678748650430341591636111999833681397895659528 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_2016_1824 : Witnessed 0 2016 1824 := witness_check 23954354515378686014568790213086307411670624945307648 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_2018_2 : Witnessed 0 2018 2 := witness_check 201850880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_2018_2018 : Witnessed 0 2018 2018 := witness_check 23954103587393728193656808721327452610504657836965888 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_2022_4 : Witnessed 0 2022 4 := witness_check 26495653249024 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_2026_2 : Witnessed 0 2026 2 := witness_check 201850880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_2028_4 : Witnessed 0 2028 4 := witness_check 26495653249024 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_2030_2 : Witnessed 0 2030 2 := witness_check 201850880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_2030_4 : Witnessed 0 2030 4 := witness_check 26495653249024 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_2030_1038 : Witnessed 0 2030 1038 := witness_check 23954011835853498829358394408219881288512415413567488 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_2031_1 : Witnessed 0 2031 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_2038_134 : Witnessed 0 2038 134 := witness_check 16044197292872617372159260153145196544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_2042_258 : Witnessed 0 2042 258 := witness_check 6274466563655184327801164386434374252888064 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_2044_4 : Witnessed 0 2044 4 := witness_check 26495653249024 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_2046_2 : Witnessed 0 2046 2 := witness_check 201850880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_2046_2046 : Witnessed 0 2046 2046 := witness_check 17966331375066268083584136369025690393568318077796352 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_2047_1 : Witnessed 0 2047 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_2047_1791 : Witnessed 0 2047 1791 := witness_check 3064860678748650430341610275330286652034013515481096 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_2699_641 : Witnessed 0 2699 641 := witness_check 91745265747009406150346151527473353555735216136 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_2707_641 : Witnessed 0 2707 641 := witness_check 91745265747009406150346151527473353555735216136 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_2746_698 : Witnessed 0 2746 698 := witness_check 91745265762799180915790029371146360593488281600 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_2811_763 : Witnessed 0 2811 763 := witness_check 91745265747010952227348921907068921672976826376 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3007_703 : Witnessed 0 3007 703 := witness_check 91745265747009406168985618552785147751983218696 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3039_735 : Witnessed 0 3039 735 := witness_check 91745265747010868464541926042845759177054748680 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3071_767 : Witnessed 0 3071 767 := witness_check 91745265747010868483181144329664111792674570248 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3203_1 : Witnessed 0 3203 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3211_1 : Witnessed 0 3211 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3211_131 : Witnessed 0 3211 131 := witness_check 254422546068206553797994320333635592 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3219_131 : Witnessed 0 3219 131 := witness_check 254422546068206553797994320333635592 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3258_186 : Witnessed 0 3258 186 := witness_check 16044197312809241713413202192642867200 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3323_251 : Witnessed 0 3323 251 := witness_check 256058786017075482151944725146894344 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3519_191 : Witnessed 0 3519 191 := witness_check 254422566004830895051989351137804296 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3551_223 : Witnessed 0 3551 223 := witness_check 255884860263960980666103671749607432 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3583_255 : Witnessed 0 3583 255 := witness_check 255884880200356671930953391829155848 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3595_1 : Witnessed 0 3595 1 := witness_check 2155 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3603_1 : Witnessed 0 3603 1 := witness_check 2155 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3642_58 : Witnessed 0 3642 58 := witness_check 18639446937141863703295688704 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3707_123 : Witnessed 0 3707 123 := witness_check 1546077002750291425664119942547563 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3715_512 : Witnessed 0 3715 512 := witness_check 91745265746754983604277944973675359235603431424 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3715_1667 : Witnessed 0 3715 1667 := witness_check 3064860678748650428879277440357572965572046479687688 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3721_3201 : Witnessed 0 3721 3201 := witness_check 982715830349184713325963926833298176594806674910909300744 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3722_2690 : Witnessed 0 3722 2690 := witness_check 982712765671996496185089212057286326341351054993330274304 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3723_1 : Witnessed 0 3723 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3723_512 : Witnessed 0 3723 512 := witness_check 91745265746754983604277944973675359235603431424 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3723_3723 : Witnessed 0 3723 3723 := witness_check 982715830440929979072718910437576121571078359331893673992 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3729_3201 : Witnessed 0 3729 3201 := witness_check 1275518259625873603326055605708204124989962018443113791496 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3730_2 : Witnessed 0 3730 2 := witness_check 201850880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3730_3730 : Witnessed 0 3730 3730 := witness_check 1275533161188313094974754368829841084651059822534177849344 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3731_1 : Witnessed 0 3731 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3731_2 : Witnessed 0 3731 2 := witness_check 201850880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3731_3731 : Witnessed 0 3731 3731 := witness_check 1275518259717618869072810589312482298611030171308811354120 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3738_26 : Witnessed 0 3738 26 := witness_check 228649989118815273222144 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3754_10 : Witnessed 0 3754 10 := witness_check 2596325185380941824 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3762_2 : Witnessed 0 3762 2 := witness_check 201850880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3768_8 : Witnessed 0 3768 8 := witness_check 2596325185179090944 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3770_2 : Witnessed 0 3770 2 := witness_check 201850880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3770_3770 : Witnessed 0 3770 3770 := witness_check 982730731911624204974662689973574354545319156802772271104 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3771_1 : Witnessed 0 3771 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3771_59 : Witnessed 0 3771 59 := witness_check 18639446936807471430893043720 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3774_2 : Witnessed 0 3774 2 := witness_check 201850880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3775_1 : Witnessed 0 3775 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3775_3771 : Witnessed 0 3775 3771 := witness_check 982715830440929979072718910456215568505289505577405775880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3779_1 : Witnessed 0 3779 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3803_27 : Witnessed 0 3803 27 := witness_check 228649989118815273222152 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3807_3803 : Witnessed 0 3807 3803 := witness_check 982715830440929979072720456495939653572754953378432811016 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3819_11 : Witnessed 0 3819 11 := witness_check 2596325185380941832 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3827_3 : Witnessed 0 3827 3 := witness_check 201850888 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3833_1 : Witnessed 0 3833 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3834_2 : Witnessed 0 3834 2 := witness_check 201850880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3835_3835 : Witnessed 0 3835 3835 := witness_check 982715830440929979072720456514578871859573305994052632584 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3839_3835 : Witnessed 0 3839 3835 := witness_check 982715830440929979072720456514578871859573305994052632584 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3903_63 : Witnessed 0 3903 63 := witness_check 18639446937141890198948938777 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3905_1 : Witnessed 0 3905 1 := witness_check 1049 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3935_95 : Witnessed 0 3935 95 := witness_check 1462314195754427202501624020468761 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3967_127 : Witnessed 0 3967 127 := witness_check 1462332834972714020854239640290329 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3979_1 : Witnessed 0 3979 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3979_256 : Witnessed 0 3979 256 := witness_check 365122979706166971296200953774287290892288 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3983_4 : Witnessed 0 3983 4 := witness_check 26495653249024 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3983_3973 : Witnessed 0 3983 3973 := witness_check 982715830440930344195698616604547417769435834929456873480 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3987_1 : Witnessed 0 3987 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3987_256 : Witnessed 0 3987 256 := witness_check 365122979706166971296200953774287290892288 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3991_2 : Witnessed 0 3991 2 := witness_check 201850880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3991_4 : Witnessed 0 3991 4 := witness_check 26495653249024 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3991_3973 : Witnessed 0 3991 3973 := witness_check 1275518259717619234195790295479453366164591178461661364232 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3995_2 : Witnessed 0 3995 2 := witness_check 201850880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3995_8 : Witnessed 0 3995 8 := witness_check 2596325185179090944 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3998_2 : Witnessed 0 3998 2 := witness_check 201850880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3998_256 : Witnessed 0 3998 256 := witness_check 2091715709463008734909363711883079195820032 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3999_1 : Witnessed 0 3999 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3999_23 : Witnessed 0 3999 23 := witness_check 228647392820125747380232 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3999_27 : Witnessed 0 3999 27 := witness_check 228649989118815273222152 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3999_512 : Witnessed 0 3999 512 := witness_check 91745265746754983604277944973675359235603431424 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_3999_3485 : Witnessed 0 3999 3485 := witness_check 982715830349185078448943633000269701445749594508924813320 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_4015_11 : Witnessed 0 4015 11 := witness_check 2596325185380941832 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_4015_1959 : Witnessed 0 4015 1959 := witness_check 3064860679113773408585463050872060737725445043650568 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_4023_3 : Witnessed 0 4023 3 := witness_check 201850888 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_4025_1 : Witnessed 0 4025 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_4027_2 : Witnessed 0 4027 2 := witness_check 201850880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_4027_256 : Witnessed 0 4027 256 := witness_check 365122979706166971296200953774287290892288 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_4027_315 : Witnessed 0 4027 315 := witness_check 365122979706185610743137761245718183936008 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_4029_1 : Witnessed 0 4029 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_4030_2 : Witnessed 0 4030 2 := witness_check 201850880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_4030_256 : Witnessed 0 4030 256 := witness_check 2091715709463008734909363711883079195820032 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_4031_59 : Witnessed 0 4031 59 := witness_check 18639446936807471430893043720 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_4031_4031 : Witnessed 0 4031 4031 := witness_check 982715830440930344195698616623186864706243306360349917192 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_4033_1 : Witnessed 0 4033 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_4033_128 : Witnessed 0 4033 128 := witness_check 254422546068206553797994320131784704 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_4035_1 : Witnessed 0 4035 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_4035_256 : Witnessed 0 4035 256 := witness_check 365122979706166971296200953774287290892288 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_4037_1 : Witnessed 0 4037 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_4037_4 : Witnessed 0 4037 4 := witness_check 26495653249024 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_4039_2 : Witnessed 0 4039 2 := witness_check 201850880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_4039_4 : Witnessed 0 4039 4 := witness_check 26495653249024 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_4045_1 : Witnessed 0 4045 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_4047_2 : Witnessed 0 4047 2 := witness_check 201850880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_4047_7 : Witnessed 0 4047 7 := witness_check 26495855099912 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_4054_2 : Witnessed 0 4054 2 := witness_check 201850880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_4055_1 : Witnessed 0 4055 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_4055_87 : Witnessed 0 4055 87 := witness_check 1462314195754424271784166438731784 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_4058_2 : Witnessed 0 4058 2 := witness_check 201850880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_4059_1 : Witnessed 0 4059 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_4059_259 : Witnessed 0 4059 259 := witness_check 365122979706166971296200953774287492743176 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_4061_1 : Witnessed 0 4061 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_4062_2 : Witnessed 0 4062 2 := witness_check 201850880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_4063_1 : Witnessed 0 4063 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_4063_27 : Witnessed 0 4063 27 := witness_check 228649989118815273222152 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_4063_4063 : Witnessed 0 4063 4063 := witness_check 982715830440930344195700078918743172196303917785421447176 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_4079_11 : Witnessed 0 4079 11 := witness_check 2596325185380941832 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_4087_3 : Witnessed 0 4087 3 := witness_check 201850888 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_4090_2 : Witnessed 0 4090 2 := witness_check 201850880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_4091_1 : Witnessed 0 4091 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_4091_379 : Witnessed 0 4091 379 := witness_check 365122981168499806268914640209758875287560 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_4093_1 : Witnessed 0 4093 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_4094_2 : Witnessed 0 4094 2 := witness_check 201850880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_4095_4095 : Witnessed 0 4095 4095 := witness_check 982715830440930344195700078937382390483122270401041268744 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_6031_1933 : Witnessed 0 6031 1933 := witness_check 3064860679113773408585444411653776515698014401069064 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_6039_1937 : Witnessed 0 6039 1937 := witness_check 3064860679113773408585444411882421312139963461009416 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_6047_1437 : Witnessed 0 6047 1437 := witness_check 3064768933848026653601840133937450233132408689917960 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_6063_6063 : Witnessed 0 6063 6063 := witness_check 45013096547522748436580219362407638920742054226302221714718728 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_6079_1983 : Witnessed 0 6079 1983 := witness_check 3064860679113773408585463051100710726844260115021832 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_6143_2047 : Witnessed 0 6143 2047 := witness_check 3064860679113773410047777246626487605808300806373384 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_7047_1 : Witnessed 0 7047 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_7055_901 : Witnessed 0 7055 901 := witness_check 91745630869989112317317447728427154338679357448 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_7063_897 : Witnessed 0 7063 897 := witness_check 91745630869989112317317447728427127843026108424 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_7071_413 : Witnessed 0 7071 413 := witness_check 365123234128713039751493245210187849007112 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_7087_935 : Witnessed 0 7087 935 := witness_check 91745630869989112335956666015245506954501029896 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_7103_959 : Witnessed 0 7103 959 := witness_check 91745630869989112335956914753738922039274110984 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_7167_1023 : Witnessed 0 7167 1023 := witness_check 91745630869990574650152440530617886079965462536 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_7567_391 : Witnessed 0 7567 391 := witness_check 365123234128713039502754751795103277776904 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_7575_387 : Witnessed 0 7575 387 := witness_check 365123234128713039502754751768607624527880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_7583_7583 : Witnessed 0 7583 7583 := witness_check 45014079260288236942544894897455176139571436641846100618641416 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_7599_423 : Witnessed 0 7599 423 := witness_check 365123234128732975898446016644823357325320 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_7615_447 : Witnessed 0 7615 447 := witness_check 365123234128732976127096005763638428696584 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_7679_511 : Witnessed 0 7679 511 := witness_check 365123235591047171652872884727679120048136 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_7819_1 : Witnessed 0 7819 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_7823_133 : Witnessed 0 7823 133 := witness_check 254422546068206553798026261803565064 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_7831_129 : Witnessed 0 7831 129 := witness_check 254422546068206553797994320131784712 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_7839_157 : Witnessed 0 7839 157 := witness_check 254422546068435203787145076874936328 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_7855_167 : Witnessed 0 7855 167 := witness_check 254422564707424840616378877625237512 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_7871_191 : Witnessed 0 7871 191 := witness_check 254422564707653490605497692696608776 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_7935_255 : Witnessed 0 7935 255 := witness_check 255968623070956844889298109343465480 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_7949_1 : Witnessed 0 7949 1 := witness_check 1049 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_7951_5 : Witnessed 0 7951 5 := witness_check 26495653250073 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_7959_1 : Witnessed 0 7959 1 := witness_check 1049 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_7965_1 : Witnessed 0 7965 1 := witness_check 1049 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_7967_29 : Witnessed 0 7967 29 := witness_check 228650323537583056880665 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_7977_1 : Witnessed 0 7977 1 := witness_check 1049 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_7983_39 : Witnessed 0 7983 39 := witness_check 18639218286818379111545308185 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_7999_63 : Witnessed 0 7999 63 := witness_check 18639446937141890198948938777 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_8063_127 : Witnessed 0 8063 127 := witness_check 1462332834972714020854239640290329 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_8071_1024 : Witnessed 0 8071 1024 := witness_check 3064768933482903419473127094206045492218490542620672 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_8071_6021 : Witnessed 0 8071 6021 := witness_check 45013096547522748436580219362407620281523764811624420713955336 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_8071_6023 : Witnessed 0 8071 6023 := witness_check 45013096547522748436580219362407620281523764811624420915806216 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_8075_1 : Witnessed 0 8075 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_8075_256 : Witnessed 0 8075 256 := witness_check 365122979706166971296200953774287290892288 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_8077_128 : Witnessed 0 8077 128 := witness_check 254422546068206553797994320131784704 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_8077_7565 : Witnessed 0 8077 7565 := witness_check 45014079260288236942544894897455176139342789249052470524510216 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_8078_7046 : Witnessed 0 8078 7046 := witness_check 45014079257223559756054346752497241891105695955216159671320576 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_8079_4 : Witnessed 0 8079 4 := witness_check 26495653249024 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_8079_7 : Witnessed 0 8079 7 := witness_check 26495855099912 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_8079_13 : Witnessed 0 8079 13 := witness_check 2596351680832339976 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_8079_8079 : Witnessed 0 8079 8079 := witness_check 45014079260288328687810641652438780417287762924411706329792520 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_8083_3971 : Witnessed 0 8083 3971 := witness_check 1275518259717619234195790295479453366164591151966209966088 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_8085_7553 : Witnessed 0 8085 7553 := witness_check 45014372062717513631434894989134051045291181808044321896661000 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_8086_8086 : Witnessed 0 8086 8086 := witness_check 45014372077619076072653136417654014445864005663983700518895616 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_8087_5 : Witnessed 0 8087 5 := witness_check 26495653249032 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_8087_8087 : Witnessed 0 8087 8087 := witness_check 45014372062717605376700641744117655323464802876223683247472648 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_8091_1 : Witnessed 0 8091 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_8093_128 : Witnessed 0 8093 128 := witness_check 254422546068206553797994320131784704 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_8093_7581 : Witnessed 0 8093 7581 := witness_check 45014079260288236942544894897455176139571436641846100416790536 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_8094_2 : Witnessed 0 8094 2 := witness_check 201850880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_8095_31 : Witnessed 0 8095 31 := witness_check 228649989145310926471176 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_8095_8095 : Witnessed 0 8095 8095 := witness_check 45014079260288328687810641652438780417516410317205336222072840 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_8103_6055 : Witnessed 0 8103 6055 := witness_check 45013096547522748436580219362407638920742051629977036535627784 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_8105_1 : Witnessed 0 8105 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_8105_128 : Witnessed 0 8105 128 := witness_check 254422546068206553797994320131784704 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_8107_2 : Witnessed 0 8107 2 := witness_check 201850880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_8107_3 : Witnessed 0 8107 3 := witness_check 201850888 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_8109_1 : Witnessed 0 8109 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_8110_2 : Witnessed 0 8110 2 := witness_check 201850880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_8111_1 : Witnessed 0 8111 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_8111_15 : Witnessed 0 8111 15 := witness_check 2596351681034190856 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_8111_8111 : Witnessed 0 8111 8111 := witness_check 45014079260288328687810641652438799056506049742764321949614088 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_8119_7 : Witnessed 0 8119 7 := witness_check 26495855099912 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_8123_3 : Witnessed 0 8123 3 := witness_check 201850888 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_8125_1 : Witnessed 0 8125 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_8126_2 : Witnessed 0 8126 2 := witness_check 201850880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_8127_63 : Witnessed 0 8127 63 := witness_check 18639446936807497926546292744 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_8127_8127 : Witnessed 0 8127 8127 := witness_check 45014079260288328687810641652438799056734697135557951841894408 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_8159_31 : Witnessed 0 8159 31 := witness_check 228649989145310926471176 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_8174_2 : Witnessed 0 8174 2 := witness_check 201850880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_8175_1 : Witnessed 0 8175 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_8175_15 : Witnessed 0 8175 15 := witness_check 2596351681034190856 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_8183_7 : Witnessed 0 8183 7 := witness_check 26495855099912 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_8187_3 : Witnessed 0 8187 3 := witness_check 201850888 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_8189_1 : Witnessed 0 8189 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_8190_2 : Witnessed 0 8190 2 := witness_check 201850880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_8191_8191 : Witnessed 0 8191 8191 := witness_check 45014079260288328687810641653901113252260474014521992533245960 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_16191_1 : Witnessed 0 16191 1 := witness_check 1049 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew0_16319_128 : Witnessed 0 16319 128 := witness_check 254422546068206553797994320131784704 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_386_128 : Witnessed 1 386 128 := witness_check 249230249209671726169463823802564608 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_386_384 : Witnessed 1 386 384 := witness_check 364782946569495242504463748630679325245440 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_518_514 : Witnessed 1 518 514 := witness_check 94956573055343393336659088404936723292736847872 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_578_578 : Witnessed 1 578 578 := witness_check 94956573055344939395022391759220523709383704576 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_642_642 : Witnessed 1 642 642 := witness_check 94956573055592623585868760131106187116539412480 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_934_928 : Witnessed 1 934 928 := witness_check 94956937838289962850540811155503706587409678336 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_1430_1408 : Witnessed 1 1430 1408 := witness_check 3063307432210355463124418651877792957829513935323136 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_1982_1920 : Witnessed 1 1982 1920 := witness_check 3063402388783410806517755310966197894552806399934464 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_2114_64 : Witnessed 1 2114 64 := witness_check 1636220012244587099981869662339072 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_2562_514 : Witnessed 1 2562 514 := witness_check 94956573055343393336659088404936723292736847872 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_2618_58 : Witnessed 1 2618 58 := witness_check 18639467025646159972997398528 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_2618_2618 : Witnessed 1 2618 2618 := witness_check 985777756756939581194350118569734937793336823610064109568 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_2624_576 : Witnessed 1 2624 576 := witness_check 439748394569826903786306131972636840953074679808 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_2624_2624 : Witnessed 1 2624 2624 := witness_check 1986784688201069181377776427797485094210355941668978425856 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_2626_2 : Witnessed 1 2626 2 := witness_check 272236544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_2626_2626 : Witnessed 1 2626 2626 := witness_check 1986784687856277359863294463406201353996939624425287450624 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_2636_8 : Witnessed 1 2636 8 := witness_check 2930717457511350272 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_2638_2 : Witnessed 1 2638 2 := witness_check 272236544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_2640_16 : Witnessed 1 2640 16 := witness_check 248735897089899593990144 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_2642_2642 : Witnessed 1 2642 2642 := witness_check 1280112681574494360052801690511515280436645636607967887360 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_2664_2664 : Witnessed 1 2664 2664 := witness_check 985777757008224378091394726186922465907925271576232067072 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_2768_128 : Witnessed 1 2768 128 := witness_check 249230249209671726169463823802564608 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_2770_2770 : Witnessed 1 2770 2770 := witness_check 1280112681574494360053050920760724952162815100431770451968 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_2882_256 : Witnessed 1 2882 256 := witness_check 364782697339246032832737579166855522680832 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_2888_8 : Witnessed 1 2888 8 := witness_check 2930717457511350272 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_2890_2 : Witnessed 1 2890 2 := witness_check 272236544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_2954_2954 : Witnessed 1 2954 2954 := witness_check 985777756756939945977296688046337975234370011774175543296 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_3650_2 : Witnessed 1 3650 2 := witness_check 272236544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_3722_2 : Witnessed 1 3722 2 := witness_check 272236544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_3722_3722 : Witnessed 1 3722 3722 := witness_check 985780820064371426767115903723714515826000043753262940160 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_3730_2 : Witnessed 1 3730 2 := witness_check 272236544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_3730_3730 : Witnessed 1 3730 3730 := witness_check 1280115744881926205625565929625771022137740498849733672960 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_3778_128 : Witnessed 1 3778 128 := witness_check 249230249209671726169463823802564608 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_3778_3778 : Witnessed 1 3778 3778 := witness_check 1986787751163709205436060248578820399052318287083700092928 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_3792_16 : Witnessed 1 3792 16 := witness_check 248735897089899593990144 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_3794_2 : Witnessed 1 3794 2 := witness_check 272236544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_3834_3712 : Witnessed 1 3834 3712 := witness_check 985780820064371426767115903723714515823069326295479353344 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_4030_2874 : Witnessed 1 4030 2874 := witness_check 985777756756939945977047457815767770530915990465586790400 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_4062_1818 : Witnessed 1 4062 1818 := witness_check 3063402388783410557287506101543210552896339974946816 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_4094_3968 : Witnessed 1 4094 3968 := witness_check 985780820064371791549813242969747348560648493151002034176 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_4666_4650 : Witnessed 1 4666 4650 := witness_check 71031683237635774480138848456411308462920949210881829308596224 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_4712_616 : Witnessed 1 4712 616 := witness_check 346241369952388000972486083545486864680522612736 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6184_8 : Witnessed 1 6184 8 := witness_check 2930717457511350272 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6202_4152 : Witnessed 1 6202 4152 := witness_check 71031683237635679523565793113017974535044706365162292934344704 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6248_104 : Witnessed 1 6248 104 := witness_check 1636241382426303358499248454762496 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6670_512 : Witnessed 1 6670 512 := witness_check 94956573055343393336659088404936723292464611328 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6678_6658 : Witnessed 1 6678 6658 := witness_check 45315677540438022928490616646280597009571250418332156875636736 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6678_6678 : Witnessed 1 6678 6678 := witness_check 45315677540438022928490616646280597009819986315453998141407232 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6682_26 : Witnessed 1 6682 26 := witness_check 248738827807357377576960 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6696_8 : Witnessed 1 6696 8 := witness_check 2930717457511350272 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6696_40 : Witnessed 1 6696 40 := witness_check 18639218289749070073131171840 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6696_512 : Witnessed 1 6696 512 := witness_check 346241369952386454895483561901138460741851938816 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6696_6696 : Witnessed 1 6696 6696 := witness_check 71032669015392687747943884506198081723776807851026174133141504 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6698_2 : Witnessed 1 6698 2 := witness_check 272236544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6698_2050 : Witnessed 1 6698 2050 := witness_check 985777756661983008139006725214436382362753940344874336256 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6698_6698 : Witnessed 1 6698 6698 := witness_check 71032669015392436463146987463136522899303311649288725018050560 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6700_4 : Witnessed 1 6700 4 := witness_check 31941671780352 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6700_6700 : Witnessed 1 6700 6700 := witness_check 45315383205513456658508655239316272417005457595088966405586944 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6702_2 : Witnessed 1 6702 2 := witness_check 272236544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6706_18 : Witnessed 1 6706 18 := witness_check 248735897089899866226688 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6708_4 : Witnessed 1 6708 4 := witness_check 31941671780352 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6712_520 : Witnessed 1 6712 520 := witness_check 346241369952386454895483561904069178199363289088 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6714_2 : Witnessed 1 6714 2 := witness_check 272236544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6714_6714 : Witnessed 1 6714 6714 := witness_check 71032669015392436463146987463136522899552047546378624612040704 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6716_4 : Witnessed 1 6716 4 := witness_check 31941671780352 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6718_2 : Witnessed 1 6718 2 := witness_check 272236544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6718_6718 : Witnessed 1 6718 6718 := witness_check 45315383205513205373711758196254713592780697290441416884486144 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6728_8 : Witnessed 1 6728 8 := witness_check 2930717457511350272 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6752_32 : Witnessed 1 6752 32 := witness_check 18639218286818352615619821568 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6760_8 : Witnessed 1 6760 8 := witness_check 2930717457511350272 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6760_6760 : Witnessed 1 6760 6760 := witness_check 71032669015392687747943884507744140087080162134826590779998208 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6762_2 : Witnessed 1 6762 2 := witness_check 272236544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6764_4 : Witnessed 1 6764 4 := witness_check 31941671780352 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6766_2 : Witnessed 1 6766 2 := witness_check 272236544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6772_4 : Witnessed 1 6772 4 := witness_check 31941671780352 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6780_4 : Witnessed 1 6780 4 := witness_check 31941671780352 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6782_2 : Witnessed 1 6782 2 := witness_check 272236544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6782_6782 : Witnessed 1 6782 6782 := witness_check 45315383205513205373711758197800771956084051574241833531342848 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6824_8 : Witnessed 1 6824 8 := witness_check 2930717457511350272 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6824_128 : Witnessed 1 6824 128 := witness_check 249230249209671726169463823802564608 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6836_128 : Witnessed 1 6836 128 := witness_check 249230249209671726169463823802564608 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6840_8 : Witnessed 1 6840 8 := witness_check 2930717457511350272 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6840_16 : Witnessed 1 6840 16 := witness_check 248735897089899593990144 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6842_128 : Witnessed 1 6842 128 := witness_check 249230249209671726169463823802564608 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6844_4 : Witnessed 1 6844 4 := witness_check 31941671780352 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6846_2 : Witnessed 1 6846 2 := witness_check 272236544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6880_32 : Witnessed 1 6880 32 := witness_check 18639218286818352615619821568 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6880_128 : Witnessed 1 6880 128 := witness_check 249230249209671726169463823802564608 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6884_4 : Witnessed 1 6884 4 := witness_check 31941671780352 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6888_8 : Witnessed 1 6888 8 := witness_check 2930717457511350272 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6888_128 : Witnessed 1 6888 128 := witness_check 249230249209671726169463823802564608 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6892_4 : Witnessed 1 6892 4 := witness_check 31941671780352 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6896_16 : Witnessed 1 6896 16 := witness_check 248735897089899593990144 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6900_4 : Witnessed 1 6900 4 := witness_check 31941671780352 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6900_128 : Witnessed 1 6900 128 := witness_check 249230249209671726169463823802564608 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6902_2 : Witnessed 1 6902 2 := witness_check 272236544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6904_8 : Witnessed 1 6904 8 := witness_check 2930717457511350272 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6908_4 : Witnessed 1 6908 4 := witness_check 31941671780352 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6952_8 : Witnessed 1 6952 8 := witness_check 2930717457511350272 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6962_2 : Witnessed 1 6962 2 := witness_check 272236544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6970_2 : Witnessed 1 6970 2 := witness_check 272236544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_6990_2 : Witnessed 1 6990 2 := witness_check 272236544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_7016_8 : Witnessed 1 7016 8 := witness_check 2930717457511350272 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_7080_8 : Witnessed 1 7080 8 := witness_check 2930717457511350272 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_7080_128 : Witnessed 1 7080 128 := witness_check 249230249209671726169463823802564608 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_7082_2 : Witnessed 1 7082 2 := witness_check 272236544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_7090_128 : Witnessed 1 7090 128 := witness_check 249230249209671726169463823802564608 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_7096_16 : Witnessed 1 7096 16 := witness_check 248735897089899593990144 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_7098_2 : Witnessed 1 7098 2 := witness_check 272236544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_7098_128 : Witnessed 1 7098 128 := witness_check 249230249209671726169463823802564608 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_7102_4 : Witnessed 1 7102 4 := witness_check 31941671780352 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_7118_2 : Witnessed 1 7118 2 := witness_check 272236544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_7118_128 : Witnessed 1 7118 128 := witness_check 249230249209671726169463823802564608 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_7134_16 : Witnessed 1 7134 16 := witness_check 248735897089899593990144 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_7144_8 : Witnessed 1 7144 8 := witness_check 2930717457511350272 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_7144_128 : Witnessed 1 7144 128 := witness_check 249230249209671726169463823802564608 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_7160_8 : Witnessed 1 7160 8 := witness_check 2930717457511350272 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_7160_16 : Witnessed 1 7160 16 := witness_check 248735897089899593990144 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_7162_2 : Witnessed 1 7162 2 := witness_check 272236544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_7950_2 : Witnessed 1 7950 2 := witness_check 272236544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_7994_2 : Witnessed 1 7994 2 := witness_check 272236544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_8078_2 : Witnessed 1 8078 2 := witness_check 272236544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_8078_128 : Witnessed 1 8078 128 := witness_check 249230249209671726169463823802564608 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_8086_8086 : Witnessed 1 8086 8086 := witness_check 45315677543501330360700972109405015661697779273283512076730368 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_8094_7958 : Witnessed 1 8094 7958 := witness_check 45315383208576512805922113410148864395768474329737033886072832 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_8110_3854 : Witnessed 1 8110 3854 := witness_check 985780820064371791549564012720537676837409778726654836736 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_8122_128 : Witnessed 1 8122 128 := witness_check 249230249209671726169463823802564608 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_8126_2838 : Witnessed 1 8126 2838 := witness_check 985777756756939945977047457797128552241166952334127398912 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_8190_22 : Witnessed 1 8190 22 := witness_check 248735897121841538007040 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_10774_2566 : Witnessed 1 10774 2566 := witness_check 1280112681574494360052800144453151728346464783185496113152 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_10814_2622 : Witnessed 1 10814 2622 := witness_check 985777756756939581194350118569734937793336860503833182208 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_10878_2686 : Witnessed 1 10878 2686 := witness_check 985777756756939581194351664628098241147620660920480038912 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_12822_530 : Witnessed 1 12822 530 := witness_check 94956573055343393336659360199263905329270358016 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_12862_574 : Witnessed 1 12862 574 := witness_check 94956573055343393355298578489328540792965955584 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_12926_638 : Witnessed 1 12926 638 := witness_check 94956573055344939413661881843612341209612812288 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_14342_2 : Witnessed 1 14342 2 := witness_check 361627648 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_14350_2 : Witnessed 1 14350 2 := witness_check 361627648 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_14358_2 : Witnessed 1 14358 2 := witness_check 361627648 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_14394_2 : Witnessed 1 14394 2 := witness_check 361627648 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_14398_62 : Witnessed 1 14398 62 := witness_check 21370430452155639220419821568 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_14462_126 : Witnessed 1 14462 126 := witness_check 1636241382675039255621090082160640 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_14854_512 : Witnessed 1 14854 512 := witness_check 94956573055343393336659088404936723292464611328 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_14854_12806 : Witnessed 1 14854 12806 := witness_check 2172934082340080335209027509186170871310219641878032550651395440640 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_14862_512 : Witnessed 1 14862 512 := witness_check 94956573055343393336659088404936723292464611328 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_14866_10754 : Witnessed 1 14866 10754 := witness_check 2172888769222765260240131165619781486282854438915606955843565256704 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_14868_14340 : Witnessed 1 14868 14340 := witness_check 3391018832177215789298824660516362940403523417949881344201456615424 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_14870_2 : Witnessed 1 14870 2 := witness_check 272236544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_14870_512 : Witnessed 1 14870 512 := witness_check 94956573055343393336659088404936723292464611328 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_14870_14870 : Witnessed 1 14870 14870 := witness_check 2172934083620193016688565296183627622426712530555457663549979623424 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_14878_8 : Witnessed 1 14878 8 := witness_check 2930717457511350272 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_14878_26 : Witnessed 1 14878 26 := witness_check 248738827807357377576960 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_14894_10 : Witnessed 1 14894 10 := witness_check 2930717457783586816 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_14900_4 : Witnessed 1 14900 4 := witness_check 31941671780352 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_14902_2 : Witnessed 1 14902 2 := witness_check 272236544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_14904_8 : Witnessed 1 14904 8 := witness_check 2930717457511350272 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_14906_2 : Witnessed 1 14906 2 := witness_check 272236544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_14906_58 : Witnessed 1 14906 58 := witness_check 18639467025646159972997398528 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_14906_512 : Witnessed 1 14906 512 := witness_check 94956573055343393336659088404936723292464611328 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_14908_4 : Witnessed 1 14908 4 := witness_check 31941671780352 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_14910_2 : Witnessed 1 14910 2 := witness_check 272236544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_14910_62 : Witnessed 1 14910 62 := witness_check 18639467025646191914669178880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_14910_14910 : Witnessed 1 14910 14910 := witness_check 2172934083325858091871010517325177596543295491266432650968722702336 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_14942_30 : Witnessed 1 14942 30 := witness_check 248738827839299049357312 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_14958_14 : Witnessed 1 14958 14 := witness_check 2930749399455367168 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_14964_4 : Witnessed 1 14964 4 := witness_check 31941671780352 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_14966_2 : Witnessed 1 14966 2 := witness_check 272236544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_14966_6 : Witnessed 1 14966 6 := witness_check 31941944016896 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_14970_2 : Witnessed 1 14970 2 := witness_check 272236544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_14972_4 : Witnessed 1 14972 4 := witness_check 31941671780352 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_14974_2 : Witnessed 1 14974 2 := witness_check 272236544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_14974_14974 : Witnessed 1 14974 14974 := witness_check 2172934083325858091871010517325179142601658794620716451385369559040 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_14998_2 : Witnessed 1 14998 2 := witness_check 272236544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_14998_128 : Witnessed 1 14998 128 := witness_check 249230249209671726169463823802564608 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_15028_128 : Witnessed 1 15028 128 := witness_check 249230249209671726169463823802564608 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_15030_32 : Witnessed 1 15030 32 := witness_check 18639218286818352615619821568 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_15036_4 : Witnessed 1 15036 4 := witness_check 31941671780352 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_15038_2 : Witnessed 1 15038 2 := witness_check 272236544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_15092_4 : Witnessed 1 15092 4 := witness_check 31941671780352 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_15092_128 : Witnessed 1 15092 128 := witness_check 249230249209671726169463823802564608 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_15094_2 : Witnessed 1 15094 2 := witness_check 272236544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_15094_128 : Witnessed 1 15094 128 := witness_check 249230249209671726169463823802564608 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_15100_4 : Witnessed 1 15100 4 := witness_check 31941671780352 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_15102_2 : Witnessed 1 15102 2 := witness_check 272236544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_15102_128 : Witnessed 1 15102 128 := witness_check 249230249209671726169463823802564608 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_15126_2 : Witnessed 1 15126 2 := witness_check 272236544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_15130_2 : Witnessed 1 15130 2 := witness_check 272236544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_15154_2 : Witnessed 1 15154 2 := witness_check 272236544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_15162_2 : Witnessed 1 15162 2 := witness_check 272236544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_15166_2 : Witnessed 1 15166 2 := witness_check 272236544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_15230_2 : Witnessed 1 15230 2 := witness_check 272236544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_15254_2 : Witnessed 1 15254 2 := witness_check 272236544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_15254_128 : Witnessed 1 15254 128 := witness_check 249230249209671726169463823802564608 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_15258_128 : Witnessed 1 15258 128 := witness_check 249230249209671726169463823802564608 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_15262_8 : Witnessed 1 15262 8 := witness_check 2930717457511350272 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_15282_128 : Witnessed 1 15282 128 := witness_check 249230249209671726169463823802564608 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_15286_32 : Witnessed 1 15286 32 := witness_check 18639218286818352615619821568 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_15290_128 : Witnessed 1 15290 128 := witness_check 249230249209671726169463823802564608 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_15294_128 : Witnessed 1 15294 128 := witness_check 249230249209671726169463823802564608 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_15358_128 : Witnessed 1 15358 128 := witness_check 249230249209671726169463823802564608 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_16254_2 : Witnessed 1 16254 2 := witness_check 272236544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1_16382_128 : Witnessed 1 16382 128 := witness_check 249230249209671726169463823802564608 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew2_385_1 : Witnessed 2 385 1 := witness_check 1049 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew2_933_901 : Witnessed 2 933 901 := witness_check 91701067506996536369229625352942068318206952473 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew2_1429_1 : Witnessed 2 1429 1 := witness_check 1049 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew2_1981_1941 : Witnessed 2 1981 1941 := witness_check 3228548817931471542848309025324269525281903086666777 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew2_2016_32 : Witnessed 2 2016 32 := witness_check 19936395691264849720079548416 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew2_2044_1428 : Witnessed 2 2044 1428 := witness_check 17989623656030482870669274589082939658134192792797184 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew2_3721_1 : Witnessed 2 3721 1 := witness_check 2155 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew2_3729_1 : Witnessed 2 3729 1 := witness_check 2155 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew2_3768_8 : Witnessed 2 3768 8 := witness_check 2930717457511350272 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew2_3833_3713 : Witnessed 2 3833 3713 := witness_check 982715994129068758659228078157081655518739117232445458539 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew2_3989_1 : Witnessed 2 3989 1 := witness_check 1049 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew2_3993_1 : Witnessed 2 3993 1 := witness_check 1049 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew2_4029_1 : Witnessed 2 4029 1 := witness_check 1049 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew2_4061_1 : Witnessed 2 4061 1 := witness_check 1049 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew2_4093_3973 : Witnessed 2 4093 3973 := witness_check 982715994129069161893832879469160859617648950373429281817 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew2_8077_1 : Witnessed 2 8077 1 := witness_check 1049 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew2_8085_1 : Witnessed 2 8085 1 := witness_check 1049 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew2_8093_1 : Witnessed 2 8093 1 := witness_check 1049 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew2_8109_1 : Witnessed 2 8109 1 := witness_check 1049 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew2_8125_1 : Witnessed 2 8125 1 := witness_check 1049 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew2_8189_1 : Witnessed 2 8189 1 := witness_check 1049 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew3_1284_1280 : Witnessed 3 1284 1280 := witness_check 3226995615629527965828127251378188442599512617254912 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew3_2368_2368 : Witnessed 3 2368 2368 := witness_check 1986784687761321189702273594622331947460354281799128449024 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew3_2624_64 : Witnessed 3 2624 64 := witness_check 1636220012244587099981869662339072 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew3_3408_3408 : Witnessed 3 3408 3408 := witness_check 1300038350506409971684082726816710530840011302869250605056 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew3_6428_6428 : Witnessed 3 6428 6428 := witness_check 46018732857243267474425222699232263084095070698035936730546176 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew3_6712_40 : Witnessed 3 6712 40 := witness_check 21370181716258517378792423424 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew3_7472_7472 : Witnessed 3 7472 7472 := witness_check 110315085936036034153621847404542147665050760820131863398973440 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew3_14868_4 : Witnessed 3 14868 4 := witness_check 31941671780352 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew3_14908_14848 : Witnessed 3 14908 14848 := witness_check 2172112034396849219006945314869025796539530465301051843614007623680 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew3_14972_14848 : Witnessed 3 14972 14848 := witness_check 2172112034396849219006945314869025796539530465301051843614007623680 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew4_906_2 : Witnessed 4 906 2 := witness_check 201850880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew4_931_1 : Witnessed 4 931 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew4_1427_3 : Witnessed 4 1427 3 := witness_check 201850888 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew4_1962_2 : Witnessed 4 1962 2 := witness_check 201850880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew4_1978_2 : Witnessed 4 1978 2 := witness_check 201850880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew4_1979_1 : Witnessed 4 1979 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew4_2042_66 : Witnessed 4 2042 66 := witness_check 1546058363303354283800416848707584 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew4_4027_59 : Witnessed 4 4027 59 := witness_check 18639446936807471430893043720 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew4_4059_91 : Witnessed 4 4059 91 := witness_check 1546058363532004272919231920078856 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew4_4091_65 : Witnessed 4 4091 65 := witness_check 1546058363303354283800416646856712 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew4_8075_1 : Witnessed 4 8075 1 := witness_check 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew4_8075_11 : Witnessed 4 8075 11 := witness_check 2596325185380941832 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew4_8083_3 : Witnessed 4 8083 3 := witness_check 201850888 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew4_8091_3 : Witnessed 4 8091 3 := witness_check 201850888 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew4_8107_3 : Witnessed 4 8107 3 := witness_check 201850888 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew4_8123_3 : Witnessed 4 8123 3 := witness_check 201850888 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew4_8187_3 : Witnessed 4 8187 3 := witness_check 201850888 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew5_14866_2 : Witnessed 5 14866 2 := witness_check 272236544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew5_14906_14906 : Witnessed 5 14906 14906 := witness_check 3389784684633584753884567936318970025355029415595398594581243756544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew5_14970_14850 : Witnessed 5 14970 14850 := witness_check 3389784684633584753884567936318970025336389948569752434608518594560 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew8_1975_7 : Witnessed 8 1975 7 := witness_check 26495925486617 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew8_2038_6 : Witnessed 8 2038 6 := witness_check 26495925485568 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew8_3715_3 : Witnessed 8 3715 3 := witness_check 272238699 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew8_3762_2 : Witnessed 8 3762 2 := witness_check 272236544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew8_3827_3715 : Witnessed 8 3827 3715 := witness_check 982332706555713506905810185732713866385372897157467211883 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew8_4023_3 : Witnessed 8 4023 3 := witness_check 272237593 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew8_4055_3 : Witnessed 8 4055 3 := witness_check 272237593 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew8_4087_3975 : Witnessed 8 4087 3975 := witness_check 982332706555713872028789891899685162586326697940411352089 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew8_8071_3 : Witnessed 8 8071 3 := witness_check 272237593 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew8_8087_7959 : Witnessed 8 8087 7959 := witness_check 70806689907868314729939685548389778865497136539503768249173017 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew8_8103_7 : Witnessed 8 8103 7 := witness_check 26495925486617 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew8_8119_2839 : Witnessed 8 8119 2839 := witness_check 982329641786780389077435134174597656521633730968401085465 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew8_8183_23 : Witnessed 8 8183 23 := witness_check 228647392820125817766937 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew9_6706_6658 : Witnessed 9 6706 6658 := witness_check 71007560225327260803783251229778059335317705848726441929867264 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew9_6752_32 : Witnessed 9 6752 32 := witness_check 18639218286818352615619821568 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew9_14902_14850 : Witnessed 9 14902 14850 := witness_check 3391044524059900678631656526206289831202508252810248429837575913472 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew9_14966_14854 : Witnessed 9 14966 14854 := witness_check 3391044524059900678631656526206289831202508252810248466731344986112 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew16_1415_7 : Witnessed 16 1415 7 := witness_check 26495855099912 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew16_1967_45 : Witnessed 16 1967 45 := witness_check 18639218289414704296452161544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew16_2030_46 : Witnessed 16 2030 46 := witness_check 18639218289414704296654012416 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew16_3715_3 : Witnessed 16 3715 3 := witness_check 201850888 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew16_3754_10 : Witnessed 16 3754 10 := witness_check 2596325185380941824 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew16_3819_3723 : Witnessed 16 3819 3723 := witness_check 1275054249024284318036213019618627809986606160496961257480 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew16_4015_11 : Witnessed 16 4015 11 := witness_check 2596325185380941832 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew16_4047_11 : Witnessed 16 4047 11 := witness_check 2596325185380941832 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew16_4079_3983 : Witnessed 16 4079 3983 := witness_check 1275054249024284683159192725785599106187559961279905398792 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew16_8071_7 : Witnessed 16 8071 7 := witness_check 26495855099912 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew16_8079_7 : Witnessed 16 8079 7 := witness_check 26495855099912 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew16_8111_7 : Witnessed 16 8111 7 := witness_check 26495855099912 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew16_8175_7 : Witnessed 16 8175 7 := witness_check 26495855099912 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew17_6698_10 : Witnessed 17 6698 10 := witness_check 3246250906676232192 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew17_14854_6 : Witnessed 17 14854 6 := witness_check 31941944016896 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew17_14894_14858 : Witnessed 17 14894 14858 := witness_check 5917279703804118460757817952363700652890530701406311158393769426944 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew17_14958_14862 : Witnessed 17 14958 14862 := witness_check 5917279703804118460757817952363700652890530701406311190335441207296 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew32_903_7 : Witnessed 32 903 7 := witness_check 26495855099912 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew32_1951_1935 : Witnessed 32 1951 1935 := witness_check 23945585365878998282981732591167598572443766012510216 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew32_1986_2 : Witnessed 32 1986 2 := witness_check 201850880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew32_2014_1422 : Witnessed 32 2014 1422 := witness_check 23945242828121245165509473906750319461511216304226304 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew32_3738_26 : Witnessed 32 3738 26 := witness_check 248738493415084974931968 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew32_3803_3739 : Witnessed 32 3803 3739 := witness_check 982736711165616706185968211580647976231076162624857571336 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew32_3999_27 : Witnessed 32 3999 27 := witness_check 248738493415084974931976 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew32_4063_3999 : Witnessed 32 4063 3999 := witness_check 982736711165617109420573012892727180329985995765841395720 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew32_8079_3855 : Witnessed 32 8079 3855 := witness_check 982736711165617109419737053098502824345895495957242970120 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew32_8095_2847 : Witnessed 32 8095 2847 := witness_check 982712765922791079906325203926203849500798543058052841480 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew32_8159_31 : Witnessed 32 8159 31 := witness_check 248738493441580628181000 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew33_6682_6680 : Witnessed 33 6682 6680 := witness_check 110277141247436573933306794314196224825557729526183998701699072 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew33_6728_8 : Witnessed 33 6728 8 := witness_check 2930717457511350272 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew33_14878_14874 : Witnessed 33 14878 14874 := witness_check 2172999045083900015239570112361295538054528268298668393550901542912 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew33_14942_14878 : Witnessed 33 14942 14878 := witness_check 2172999045083900015239570112361295538054528268298668430444670615552 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew64_1954_34 : Witnessed 64 1954 34 := witness_check 19936395691264849720281399296 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew64_1982_1466 : Witnessed 64 1982 1466 := witness_check 17966239633980890620145696899166111620454629404835840 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew64_3771_3771 : Witnessed 64 3771 3771 := witness_check 1961597661503495085013856878400234175818779210871839653896 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew64_3999_1819 : Witnessed 64 3999 1819 := witness_check 3369195163618398425350073017131315760129551813312520 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew64_4031_4027 : Witnessed 64 4031 4027 := witness_check 1961597661503501357098443965137992732739543393223513210888 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew64_8127_63 : Witnessed 64 8127 63 := witness_check 19936624341254000477024550920 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew65_2562_512 : Witnessed 65 2562 512 := witness_check 439592289353435643365952078590444502005885960192 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew65_6696_40 : Witnessed 65 6696 40 := witness_check 21370181716574050827685068800 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew65_14910_14910 : Witnessed 65 14910 14910 := witness_check 2212454020093896470683400530352570360252492030061218690364435464192 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_259_3 : Witnessed 128 259 3 := witness_check 201326592 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_276_260 : Witnessed 128 276 260 := witness_check 2091715709463008734909363711909643568545792 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_324_324 : Witnessed 128 324 324 := witness_check 2091715710926590581035368820275180963102720 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_580_64 : Witnessed 128 580 64 := witness_check 1547326013903582513201913350062080 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_772_260 : Witnessed 128 772 260 := witness_check 2091715709463008734909363711909643568545792 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_807_37 : Witnessed 128 807 37 := witness_check 18658561099932213246787846144 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_807_807 : Witnessed 128 807 807 := witness_check 342675342436331018220231317441158819227080065024 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_832_320 : Witnessed 128 832 320 := witness_check 6274466565118766173927169494799911445594112 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_832_832 : Witnessed 128 832 832 := witness_check 434045678265566636969883611910049859902342430720 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_836_836 : Witnessed 128 836 836 := witness_check 434041495514712444794290720109375335171859939328 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_846_846 : Witnessed 128 846 846 := witness_check 434041495514712444794290720111969408557426671616 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_868_868 : Witnessed 128 868 868 := witness_check 342675342436332481802077443446267184764273295360 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_880_32 : Witnessed 128 880 32 := witness_check 18658561099932186682415120384 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_884_4 : Witnessed 128 884 4 := witness_check 26564372725760 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_884_868 : Witnessed 128 884 868 := witness_check 342675342436332481802077443446267184764273295360 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_1303_23 : Witnessed 128 1303 23 := witness_check 228942540725373819158528 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_1303_1303 : Witnessed 128 1303 1303 := witness_check 17966239629800505282940906383719573413238831765782528 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_1396_116 : Witnessed 128 1396 116 := witness_check 1463601802093452027774697887236096 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_1396_1396 : Witnessed 128 1396 1396 := witness_check 17966239629800505284404508185584082900288155833860096 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_1632_32 : Witnessed 128 1632 32 := witness_check 18658561099932186682415120384 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_1648_1648 : Witnessed 128 1648 1648 := witness_check 17966582300959510196580435159121869661440684656164864 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_1652_624 : Witnessed 128 1652 624 := witness_check 342673250720623102537510540602500810305905360896 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_1844_4 : Witnessed 128 1844 4 := witness_check 26564372725760 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_1844_52 : Witnessed 128 1844 52 := witness_check 18658790042472912056032952320 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_1844_1844 : Witnessed 128 1844 1844 := witness_check 17966582303051225904496117880127650860148414874648576 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_1852_4 : Witnessed 128 1852 4 := witness_check 26564372725760 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_1854_2 : Witnessed 128 1854 2 := witness_check 201326592 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_1855_1 : Witnessed 128 1855 1 := witness_check 0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_1855_29 : Witnessed 128 1855 29 := witness_check 228945134798758983237632 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_1876_20 : Witnessed 128 1876 20 := witness_check 228942540725373617831936 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_1888_32 : Witnessed 128 1888 32 := witness_check 18658561099932186682415120384 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_1888_256 : Witnessed 128 1888 256 := witness_check 6274466563655184327801164386434374051037184 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_1890_2 : Witnessed 128 1890 2 := witness_check 201326592 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_1890_98 : Witnessed 128 1890 98 := witness_check 1463600504687105040552220011003904 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_1892_4 : Witnessed 128 1892 4 := witness_check 26564372725760 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_1892_1028 : Witnessed 128 1892 1028 := witness_check 23954011835853498829358394408219878692187298752102400 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_1892_1892 : Witnessed 128 1892 1892 := witness_check 23954354511195935161840196485663324959345498652672000 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_1896_8 : Witnessed 128 1896 8 := witness_check 2594073385365405696 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_1900_4 : Witnessed 128 1900 4 := witness_check 26564372725760 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_1904_16 : Witnessed 128 1904 16 := witness_check 228942540698809245106176 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_1904_272 : Witnessed 128 1904 272 := witness_check 6274466563655184328030106927133183296143360 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_1908_4 : Witnessed 128 1908 4 := witness_check 26564372725760 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_1908_1652 : Witnessed 128 1908 1652 := witness_check 17966582300959510196496690991344292256630873073385472 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_1908_1908 : Witnessed 128 1908 1908 := witness_check 17966582303051225905959699726253655968513952269205504 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_1912_8 : Witnessed 128 1912 8 := witness_check 2594073385365405696 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_1916_4 : Witnessed 128 1916 4 := witness_check 26564372725760 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_1917_1 : Witnessed 128 1917 1 := witness_check 0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_1918_2 : Witnessed 128 1918 2 := witness_check 201326592 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_1918_30 : Witnessed 128 1918 30 := witness_check 228945134798759184564224 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_2372_4 : Witnessed 128 2372 4 := witness_check 26564372725760 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_2672_624 : Witnessed 128 2672 624 := witness_check 342673250720623102537510560691005106575607070720 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_2884_512 : Witnessed 128 2884 512 := witness_check 434039403799001518203709684740555059990896836608 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_2896_16 : Witnessed 128 2896 16 := witness_check 249031044995078946816000 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_2900_4 : Witnessed 128 2900 4 := witness_check 26564372725760 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_2928_16 : Witnessed 128 2928 16 := witness_check 249031044995078946816000 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_2932_4 : Witnessed 128 2932 4 := witness_check 26564372725760 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_2932_628 : Witnessed 128 2932 628 := witness_check 342673250720623018793342783113600296764024291328 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_2933_1 : Witnessed 128 2933 1 := witness_check 0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_2934_2 : Witnessed 128 2934 2 := witness_check 201326592 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_2935_1 : Witnessed 128 2935 1 := witness_check 0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_3120_16 : Witnessed 128 3120 16 := witness_check 228942540698809245106176 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_3184_112 : Witnessed 128 3184 112 := witness_check 1637507618812262248765962485497856 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_3380_3364 : Witnessed 128 3380 3364 := witness_check 1275533161096569920927664650961380941525923029441633583104 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_3444_116 : Witnessed 128 3444 116 := witness_check 1463601802093452027774697887236096 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_3444_3444 : Witnessed 128 3444 3444 := witness_check 1275533161096569920927666114543227296473572093788273246208 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_3595_11 : Witnessed 128 3595 11 := witness_check 2594073385566732288 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_3603_2067 : Witnessed 128 3603 2067 := witness_check 1275515194856940120422381710035041941333212504441885818880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_3632_16 : Witnessed 128 3632 16 := witness_check 228942540698809245106176 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_3632_48 : Witnessed 128 3632 48 := witness_check 18658790042472885491660226560 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_3632_512 : Witnessed 128 3632 512 := witness_check 342673250720621555192837846977514722900895072256 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_3632_3632 : Witnessed 128 3632 3632 := witness_check 1275533161439241079932576743144186930677820044403745488896 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_3633_1 : Witnessed 128 3633 1 := witness_check 0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_3634_2 : Witnessed 128 3634 2 := witness_check 201326592 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_3634_3634 : Witnessed 128 3634 3634 := witness_check 1275533161439241079932576743144186930677820044403946815488 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_3640_8 : Witnessed 128 3640 8 := witness_check 2594073385365405696 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_3642_2 : Witnessed 128 3642 2 := witness_check 201326592 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_3642_58 : Witnessed 128 3642 58 := witness_check 18658790045066958877226958848 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_3664_16 : Witnessed 128 3664 16 := witness_check 228942540698809245106176 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_3680_32 : Witnessed 128 3680 32 := witness_check 18658561099932186682415120384 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_3696_16 : Witnessed 128 3696 16 := witness_check 228942540698809245106176 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_3696_3696 : Witnessed 128 3696 3696 := witness_check 1275533161439241079932578290470200834260333246317095550976 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_3697_1 : Witnessed 128 3697 1 := witness_check 0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_3698_2 : Witnessed 128 3698 2 := witness_check 201326592 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_3699_1 : Witnessed 128 3699 1 := witness_check 0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_3700_3696 : Witnessed 128 3700 3696 := witness_check 1275533161439241079932578290470200834260333246317095550976 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_3706_2 : Witnessed 128 3706 2 := witness_check 201326592 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_3707_1 : Witnessed 128 3707 1 := witness_check 0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_3892_4 : Witnessed 128 3892 4 := witness_check 26564372725760 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_3892_52 : Witnessed 128 3892 52 := witness_check 18658790042472912056032952320 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_3903_2879 : Witnessed 128 3903 2879 := witness_check 1275515195199615462858712728255273258776965397054129963008 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_3920_16 : Witnessed 128 3920 16 := witness_check 228942540698809245106176 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_3920_256 : Witnessed 128 3920 256 := witness_check 6274466563655184327801164386434374051037184 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_3924_4 : Witnessed 128 3924 4 := witness_check 26564372725760 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_3924_20 : Witnessed 128 3924 20 := witness_check 228942540725373617831936 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_3935_1887 : Witnessed 128 3935 1887 := witness_check 17966673669204304285922691939530321670737745422581760 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_3936_32 : Witnessed 128 3936 32 := witness_check 18658561099932186682415120384 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_3940_4 : Witnessed 128 3940 4 := witness_check 26564372725760 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_3952_16 : Witnessed 128 3952 16 := witness_check 228942540698809245106176 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_3952_256 : Witnessed 128 3952 256 := witness_check 6274466563655184327801164386434374051037184 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_3952_272 : Witnessed 128 3952 272 := witness_check 6274466563655184328030106927133183296143360 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_3956_4 : Witnessed 128 3956 4 := witness_check 26564372725760 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_3956_3956 : Witnessed 128 3956 3956 := witness_check 1275533161439243171648287669734767966046640319584708591616 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_3958_2 : Witnessed 128 3958 2 := witness_check 201326592 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_3959_1 : Witnessed 128 3959 1 := witness_check 0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_3964_4 : Witnessed 128 3964 4 := witness_check 26564372725760 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_3966_2 : Witnessed 128 3966 2 := witness_check 201326592 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_3967_1 : Witnessed 128 3967 1 := witness_check 0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_3967_5 : Witnessed 128 3967 5 := witness_check 26564372725760 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_5428_1332 : Witnessed 128 5428 1332 := witness_check 17966239629800505282940926339458077791922618439303168 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_5492_1396 : Witnessed 128 5492 1396 := witness_check 17966239629800505284404508185584082900288155833860096 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_6452_292 : Witnessed 128 6452 292 := witness_check 2091715709463030124433890153543631644917760 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_6516_372 : Witnessed 128 6516 372 := witness_check 2091715710926611970808926306904247986290688 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_7204_4 : Witnessed 128 7204 4 := witness_check 32010391257088 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_7220_36 : Witnessed 128 7220 36 := witness_check 19955738504378715797266104320 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_7284_116 : Witnessed 128 7284 116 := witness_check 1637507618812262248797972876754944 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_7444_4 : Witnessed 128 7444 4 := witness_check 26564372725760 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_7444_7444 : Witnessed 128 7444 7444 := witness_check 45014372077618984327387373618473117295301954977296055495819264 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_7460_256 : Witnessed 128 7460 256 := witness_check 2091715709463008734909363711883079195820032 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_7460_5412 : Witnessed 128 7460 5412 := witness_check 45013096568411899595411660492643598968737737675005756314746880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_7472_7216 : Witnessed 128 7472 7216 := witness_check 109310725153184755389265648970926255616267522461715304317714432 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_7476_4 : Witnessed 128 7476 4 := witness_check 26564372725760 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_7476_52 : Witnessed 128 7476 52 := witness_check 19955967446919409160492679168 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_7476_7476 : Witnessed 128 7476 7476 := witness_check 45014372077618984327387373618473137251040459355979842370666496 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_7478_2 : Witnessed 128 7478 2 := witness_check 201326592 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_7479_1 : Witnessed 128 7479 1 := witness_check 0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_7486_2 : Witnessed 128 7486 2 := witness_check 201326592 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_7487_1 : Witnessed 128 7487 1 := witness_check 0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_7508_20 : Witnessed 128 7508 20 := witness_check 228942540725373617831936 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_7524_4 : Witnessed 128 7524 4 := witness_check 26564372725760 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_7536_16 : Witnessed 128 7536 16 := witness_check 228942540698809245106176 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_7540_4 : Witnessed 128 7540 4 := witness_check 26564372725760 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_7540_7540 : Witnessed 128 7540 7540 := witness_check 45014372077618984327387373619936719097166464464345379765223424 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_7542_2 : Witnessed 128 7542 2 := witness_check 201326592 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_7543_1 : Witnessed 128 7543 1 := witness_check 0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_7550_2 : Witnessed 128 7550 2 := witness_check 201326592 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_7551_1 : Witnessed 128 7551 1 := witness_check 0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_7776_32 : Witnessed 128 7776 32 := witness_check 18658561099932186682415120384 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_7796_4 : Witnessed 128 7796 4 := witness_check 32010391257088 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_7951_15 : Witnessed 128 7951 15 := witness_check 2594099949939458048 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_7959_6166 : Witnessed 128 7959 6166 := witness_check 45014372059652744697586868335532210911811324104782597750521856 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_7967_7455 : Witnessed 128 7967 7455 := witness_check 45014372077618984327387373618473117295301957571369441062551552 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_7983_1839 : Witnessed 128 7983 1839 := witness_check 23954354511195935160376614639537322445053346824847360 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_7988_4 : Witnessed 128 7988 4 := witness_check 26564372725760 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_7988_512 : Witnessed 128 7988 512 := witness_check 342673250720621555192837846977514722900895072256 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_7989_1 : Witnessed 128 7989 1 := witness_check 0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_7990_2 : Witnessed 128 7990 2 := witness_check 201326592 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_7991_1 : Witnessed 128 7991 1 := witness_check 0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_7996_4 : Witnessed 128 7996 4 := witness_check 26564372725760 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_7997_1 : Witnessed 128 7997 1 := witness_check 0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_7999_2879 : Witnessed 128 7999 2879 := witness_check 1275515195199615462858712728255273258776965397054129963008 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_8032_32 : Witnessed 128 8032 32 := witness_check 18658561099932186682415120384 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_8032_256 : Witnessed 128 8032 256 := witness_check 6274466563655184327801164386434374051037184 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_8036_4 : Witnessed 128 8036 4 := witness_check 26564372725760 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_8036_512 : Witnessed 128 8036 512 := witness_check 342673250720621555192837846977514722900895072256 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_8038_2 : Witnessed 128 8038 2 := witness_check 201326592 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_8039_1 : Witnessed 128 8039 1 := witness_check 0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_8048_16 : Witnessed 128 8048 16 := witness_check 228942540698809245106176 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_8052_4 : Witnessed 128 8052 4 := witness_check 26564372725760 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_8052_256 : Witnessed 128 8052 256 := witness_check 2091715709463008734909363711883079195820032 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_8052_8052 : Witnessed 128 8052 8052 := witness_check 45014372077619327000638094241491910637836037532571176200568832 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_8053_1 : Witnessed 128 8053 1 := witness_check 0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_8054_2 : Witnessed 128 8054 2 := witness_check 201326592 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_8055_1 : Witnessed 128 8055 1 := witness_check 0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_8063_127 : Witnessed 128 8063 127 := witness_check 1463600504916050175350978994241536 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_12148_3956 : Witnessed 128 12148 3956 := witness_check 1275533161439243171648287669734767966046640319584708591616 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_14196_1908 : Witnessed 128 14196 1908 := witness_check 17966582303051225905959699726253655968513952269205504 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_15220_884 : Witnessed 128 15220 884 := witness_check 342675342436332481802077692477312179843220111360 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_15732_372 : Witnessed 128 15732 372 := witness_check 2091715710926610537002815739657777083056128 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_15924_4 : Witnessed 128 15924 4 := witness_check 32010391257088 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_15988_116 : Witnessed 128 15988 116 := witness_check 1547344672693624986119415401545728 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_16180_52 : Witnessed 128 16180 52 := witness_check 18658790042472912056032952320 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_16180_256 : Witnessed 128 16180 256 := witness_check 2091715709463008734909363711883079195820032 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_16212_20 : Witnessed 128 16212 20 := witness_check 228942540725373617831936 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_16228_4 : Witnessed 128 16228 4 := witness_check 26564372725760 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_16240_16 : Witnessed 128 16240 16 := witness_check 228942540698809245106176 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_16244_4 : Witnessed 128 16244 4 := witness_check 26564372725760 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_16244_16244 : Witnessed 128 16244 16244 := witness_check 3371272476183898498191993750858613338994017940754329316211663306752 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_16245_1 : Witnessed 128 16245 1 := witness_check 0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_16246_2 : Witnessed 128 16246 2 := witness_check 201326592 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_16247_1 : Witnessed 128 16247 1 := witness_check 0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_16254_2 : Witnessed 128 16254 2 := witness_check 201326592 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew128_16255_1 : Witnessed 128 16255 1 := witness_check 0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_515_3 : Witnessed 132 515 3 := witness_check 201326592 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_560_32 : Witnessed 132 560 32 := witness_check 18658561099932186682415120384 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_560_544 : Witnessed 132 560 544 := witness_check 342673250720621555211496408077446909583310192640 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_832_64 : Witnessed 132 832 64 := witness_check 1547326013903582513201913350062080 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_832_832 : Witnessed 132 832 832 := witness_check 434041494493865427775643107296656322688138084352 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_1072_1072 : Witnessed 132 1072 1072 := witness_check 17966239627708789573477917604548714080012974870757376 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_1552_16 : Witnessed 132 1552 16 := witness_check 228942540698809245106176 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_1552_1040 : Witnessed 132 1552 1040 := witness_check 17966239627708789573477897648810209701329187995910144 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_1568_1056 : Witnessed 132 1568 1056 := witness_check 23954011835853498829358413066780978624347416794497024 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_1568_1568 : Witnessed 132 1568 1568 := witness_check 23954354509104219450913605904627956139070317689569280 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_1571_1571 : Witnessed 132 1571 1571 := witness_check 23954354509104219450913605904627956139070317890895872 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_1584_16 : Witnessed 132 1584 16 := witness_check 228942540698809245106176 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_1584_1584 : Witnessed 132 1584 1584 := witness_check 17966582300959510195033109145218287148238771306102784 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_1592_8 : Witnessed 132 1592 8 := witness_check 2594073385365405696 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_1594_1594 : Witnessed 132 1594 1594 := witness_check 17966582300959510195033109145218289742312156872835072 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_1619_1619 : Witnessed 132 1619 1619 := witness_check 17966673667112588576543427372398532769591092444135424 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_1632_32 : Witnessed 132 1632 32 := witness_check 18658561099932186682415120384 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_1648_1648 : Witnessed 132 1648 1648 := witness_check 17966582300959510196580435159121869661440684656164864 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_1840_16 : Witnessed 132 1840 16 := witness_check 228942540698809245106176 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_1840_256 : Witnessed 132 1840 256 := witness_check 2090694862362245919518973588060783891185664 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_1848_8 : Witnessed 132 1848 8 := witness_check 2594073385365405696 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_1888_32 : Witnessed 132 1888 32 := witness_check 18658561099932186682415120384 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_1888_256 : Witnessed 132 1888 256 := witness_check 2090694862362245919518973588060783891185664 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_1904_16 : Witnessed 132 1904 16 := witness_check 228942540698809245106176 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_2640_16 : Witnessed 132 2640 16 := witness_check 249031044995078946816000 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_2672_624 : Witnessed 132 2672 624 := witness_check 342673250720623102537510560691005106575607070720 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_2896_256 : Witnessed 132 2896 256 := witness_check 2090694862362245919518973588060783891185664 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_3120_16 : Witnessed 132 3120 16 := witness_check 228942540698809245106176 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_3184_112 : Witnessed 132 3184 112 := witness_check 1637507618812262248765962485497856 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_3632_16 : Witnessed 132 3632 16 := witness_check 228942540698809245106176 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_3632_48 : Witnessed 132 3632 48 := witness_check 18658790042472885491660226560 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_3632_512 : Witnessed 132 3632 512 := witness_check 342673250720621555192837846977514722900895072256 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_3632_3632 : Witnessed 132 3632 3632 := witness_check 1275533161439241079932576743144186930677820044403745488896 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_3633_1 : Witnessed 132 3633 1 := witness_check 0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_3634_2 : Witnessed 132 3634 2 := witness_check 201326592 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_3640_8 : Witnessed 132 3640 8 := witness_check 2594073385365405696 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_3642_2 : Witnessed 132 3642 2 := witness_check 201326592 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_3643_1 : Witnessed 132 3643 1 := witness_check 0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_3664_16 : Witnessed 132 3664 16 := witness_check 228942540698809245106176 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_3680_32 : Witnessed 132 3680 32 := witness_check 18658561099932186682415120384 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_3696_16 : Witnessed 132 3696 16 := witness_check 228942540698809245106176 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_3696_3696 : Witnessed 132 3696 3696 := witness_check 1275533161439241079932578290470200834260333246317095550976 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_3697_1 : Witnessed 132 3697 1 := witness_check 0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_3698_2 : Witnessed 132 3698 2 := witness_check 201326592 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_3699_1 : Witnessed 132 3699 1 := witness_check 0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_3706_2 : Witnessed 132 3706 2 := witness_check 201326592 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_3707_1 : Witnessed 132 3707 1 := witness_check 0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_3888_16 : Witnessed 132 3888 16 := witness_check 228942540698809245106176 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_3888_256 : Witnessed 132 3888 256 := witness_check 2090694862362245919518973588060783891185664 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_3920_256 : Witnessed 132 3920 256 := witness_check 2090694862362245919518973588060783891185664 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_3952_16 : Witnessed 132 3952 16 := witness_check 228942540698809245106176 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_3952_256 : Witnessed 132 3952 256 := witness_check 2090694862362245919518973588060783891185664 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_4384_4352 : Witnessed 132 4384 4352 := witness_check 44994265239251727717265633447914798790140657413978983279624192 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_4960_4960 : Witnessed 132 4960 4960 := witness_check 44994265239252070390516354071017336300452317374090479939878912 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_5728_32 : Witnessed 132 5728 32 := witness_check 18658561099932186682415120384 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_5984_32 : Witnessed 132 5984 32 := witness_check 18658561099932186682415120384 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_5984_256 : Witnessed 132 5984 256 := witness_check 2090694862362245919518973588060783891185664 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_6000_16 : Witnessed 132 6000 16 := witness_check 228942540698809245106176 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_7216_16 : Witnessed 132 7216 16 := witness_check 228942540698809245106176 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_7472_16 : Witnessed 132 7472 16 := witness_check 228942540698809245106176 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_7472_256 : Witnessed 132 7472 256 := witness_check 2090694862362245919518973588060783891185664 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_7472_7472 : Witnessed 132 7472 7472 := witness_check 44995540772412824285094845403102751436401762165797590589767680 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_7504_16 : Witnessed 132 7504 16 := witness_check 228942540698809245106176 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_7520_7520 : Witnessed 132 7520 7520 := witness_check 44996227527964847019684206494882277590959155633481631865503744 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_7536_16 : Witnessed 132 7536 16 := witness_check 228942540698809245106176 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_7536_32 : Witnessed 132 7536 32 := witness_check 19955738504378683786874847232 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_7728_16 : Witnessed 132 7728 16 := witness_check 228942540698809245106176 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_7792_16 : Witnessed 132 7792 16 := witness_check 228942540698809245106176 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_7984_16 : Witnessed 132 7984 16 := witness_check 228942540698809245106176 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_7984_256 : Witnessed 132 7984 256 := witness_check 2090694862362245919518973588060783891185664 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_8048_256 : Witnessed 132 8048 256 := witness_check 2090694862362245919518973588060783891185664 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_15984_16 : Witnessed 132 15984 16 := witness_check 228942540698809245106176 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_16240_16 : Witnessed 132 16240 16 := witness_check 228942540698809245106176 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew132_16240_256 : Witnessed 132 16240 256 := witness_check 2090694862362245919518973588060783891185664 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew144_1892_4 : Witnessed 144 1892 4 := witness_check 26564372725760 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew144_3680_32 : Witnessed 144 3680 32 := witness_check 18658561099932186682415120384 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew144_3940_4 : Witnessed 144 3940 4 := witness_check 26564372725760 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew144_7460_4 : Witnessed 144 7460 4 := witness_check 26564372725760 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew144_7524_4 : Witnessed 144 7524 4 := witness_check 26564372725760 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew144_16228_4 : Witnessed 144 16228 4 := witness_check 26564372725760 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew148_832_832 : Witnessed 148 832 832 := witness_check 434041494493865427775643107296656322688138084352 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew148_1568_32 : Witnessed 148 1568 32 := witness_check 18658561099932186682415120384 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew148_3104_3072 : Witnessed 148 3104 3072 := witness_check 1275054248932539052289203613468281658456536481755845099520 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew148_3680_32 : Witnessed 148 3680 32 := witness_check 18658561099932186682415120384 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew148_3680_3680 : Witnessed 148 3680 3680 := witness_check 1275054249275212303009826716005791970116496593252505354240 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew160_1876_1796 : Witnessed 160 1876 1796 := witness_check 23945585367567478551683635022765612584785174211854336 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew160_3664_16 : Witnessed 160 3664 16 := witness_check 249031044995078946816000 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew160_3924_20 : Witnessed 160 3924 20 := witness_check 249031045021643319541760 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew160_7444_20 : Witnessed 160 7444 20 := witness_check 249031045021643319541760 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew160_7508_20 : Witnessed 160 7508 20 := witness_check 249031045021643319541760 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew160_16212_20 : Witnessed 160 16212 20 := witness_check 249031045021643319541760 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew164_1552_512 : Witnessed 164 1552 512 := witness_check 342539446249430371453988632667878832731859189760 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew164_3664_16 : Witnessed 164 3664 16 := witness_check 249031044995078946816000 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew192_772_256 : Witnessed 192 772 256 := witness_check 6272084587086737758556920764182351673556992 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew192_1844_1840 : Witnessed 192 1844 1840 := witness_check 17966673517279456772368497082040347490716786899288064 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew192_3632_48 : Witnessed 192 3632 48 := witness_check 19955967446919382596119953408 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew192_3892_3888 : Witnessed 192 3892 3888 := witness_check 1961612258981855018155456563249477795379476793181910073344 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew192_7476_52 : Witnessed 192 7476 52 := witness_check 19955967446919414606511210496 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew192_16180_52 : Witnessed 192 16180 52 := witness_check 19955967446919414606511210496 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew196_3632_48 : Witnessed 196 3632 48 := witness_check 19955967446919382596119953408 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew256_131_131 : Witnessed 256 131 131 := witness_check 16044197292872617372159233657494045712 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew256_679_165 : Witnessed 256 679 165 := witness_check 16044197311550521285205280863499060240 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew256_1175_151 : Witnessed 256 1175 151 := witness_check 16044197292872846609847864103090521104 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew256_1727_157 : Witnessed 256 1727 157 := witness_check 16044197292872846612453196487320405008 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew256_1762_226 : Witnessed 256 1762 226 := witness_check 16045658912692584433705180105500262400 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew256_1790_158 : Witnessed 256 1790 158 := witness_check 16044197292872846612453196487524352000 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew256_3742_2 : Witnessed 256 3742 2 := witness_check 203948032 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew256_3774_2 : Witnessed 256 3774 2 := witness_check 203948032 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew256_3775_63 : Witnessed 256 3775 63 := witness_check 18678133153339983579444675600 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew256_3807_31 : Witnessed 256 3807 31 := witness_check 229240293962830234256400 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew256_3839_133 : Witnessed 256 3839 133 := witness_check 16044197292872617372159260114288641040 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew256_7823_2703 : Witnessed 256 7823 2703 := witness_check 982712765671996496185089212057286326343956413834764747792 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew256_7831_2710 : Witnessed 256 7831 2710 := witness_check 1277047690489551275043539237959342813157813768093316939776 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew256_7839_23 : Witnessed 256 7839 23 := witness_check 229237688630445800424464 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew256_7855_15 : Witnessed 256 7855 15 := witness_check 2605358841636324368 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew256_7871_23 : Witnessed 256 7871 23 := witness_check 229237688630445800424464 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew256_7935_255 : Witnessed 256 7935 255 := witness_check 16045658912692813673999142935530570768 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew384_522_10 : Witnessed 384 522 10 := witness_check 2603080584823570432 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew384_560_32 : Witnessed 384 560 32 := witness_check 18968046109753531751139901440 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew384_560_544 : Witnessed 384 560 544 := witness_check 343386874566974535152335036071993002220226347008 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew384_580_68 : Witnessed 384 580 68 := witness_check 1462868792663376729353721217024000 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew384_1072_1072 : Witnessed 384 1072 1072 := witness_check 18013007680103378466860436060802666465340856859623424 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew384_1552_16 : Witnessed 384 1552 16 := witness_check 237206682043831124230144 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew384_1552_1040 : Witnessed 384 1552 1040 := witness_check 18013007680103378466860415563465394899303199716409344 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew384_1568_1056 : Witnessed 384 1568 1056 := witness_check 24000779888248087722740931290912909502321475360653312 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew384_1568_1568 : Witnessed 384 1568 1568 := witness_check 24001123275122654697276064657902871741791944447098880 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew384_1584_1584 : Witnessed 384 1584 1584 := witness_check 18013351066977945441395567898501466892305419942756352 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew384_1594_1594 : Witnessed 384 1594 1594 := witness_check 18013351066977945441395567898501469495386004766326784 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew384_1652_20 : Witnessed 384 1652 20 := witness_check 237206682070356842250240 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew384_2618_2618 : Witnessed 384 2618 2618 := witness_check 1278580186282058772706072939241677621766508465347859841024 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew384_3120_16 : Witnessed 384 3120 16 := witness_check 237206682043831124230144 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew384_3632_16 : Witnessed 384 3632 16 := witness_check 237206682043831124230144 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew384_3632_512 : Witnessed 384 3632 512 := witness_check 343386874566974535133366989962239470469086445568 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew384_3634_2 : Witnessed 384 3634 2 := witness_check 203423744 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew384_3640_8 : Witnessed 384 3640 8 := witness_check 2603080584620146688 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew384_3642_2 : Witnessed 384 3642 2 := witness_check 203423744 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew384_3696_16 : Witnessed 384 3696 16 := witness_check 237206682043831124230144 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew384_3696_64 : Witnessed 384 3696 64 := witness_check 1462868792663376729327195499003904 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew384_3700_4 : Witnessed 384 3700 4 := witness_check 26525718020096 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew384_3700_52 : Witnessed 384 3700 52 := witness_check 18968283316435602107982151680 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew384_4650_4650 : Witnessed 384 4650 4650 := witness_check 109510316875556375992753749251816100630357767680202351161901056 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew384_5168_16 : Witnessed 384 5168 16 := witness_check 237206682043831124230144 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew384_5680_16 : Witnessed 384 5680 16 := witness_check 237206682043831124230144 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew384_5680_512 : Witnessed 384 5680 512 := witness_check 343386874566974535133366989962239470469086445568 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew384_5682_2 : Witnessed 384 5682 2 := witness_check 203423744 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew384_5688_8 : Witnessed 384 5688 8 := witness_check 2603080584620146688 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew384_5690_2 : Witnessed 384 5690 2 := witness_check 203423744 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew384_7220_52 : Witnessed 384 7220 52 := witness_check 20497574478248108013985464320 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew384_7284_116 : Witnessed 384 7284 116 := witness_check 1462889290237854977435209484468224 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew384_15988_116 : Witnessed 384 15988 116 := witness_check 1462887760946693164929303481155584 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew400_522_10 : Witnessed 400 522 10 := witness_check 2603080584823570432 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew400_1568_32 : Witnessed 400 1568 32 := witness_check 18968046109753531751139901440 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew400_1568_1568 : Witnessed 400 1568 1568 := witness_check 18006043558791290926804549474100678795163309155811328 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew400_3104_3072 : Witnessed 400 3104 3072 := witness_check 1278119286782323224594813690040496923744830588990053679104 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew400_4650_4650 : Witnessed 400 4650 4650 := witness_check 109510316875556375992753749251816100630357767680202351161901056 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew416_1552_512 : Witnessed 416 1552 512 := witness_check 343253070095783351394517775652603580300050563072 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew512_423_421 : Witnessed 512 423 421 := witness_check 365123234128731666631783374001701826592840 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew512_1471_413 : Witnessed 512 1471 413 := witness_check 365123234128713039732290202644129593163848 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew512_1506_98 : Witnessed 512 1506 98 := witness_check 1545284708807240262630805351694336 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew512_1534_1534 : Witnessed 512 1534 1534 := witness_check 18036391708408770300379457911526491372759974316867584 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew512_3211_11 : Witnessed 512 3211 11 := witness_check 2614339583960154184 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew512_3219_147 : Witnessed 512 3219 147 := witness_check 254422546068436086634503488354123848 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew512_3258_186 : Witnessed 512 3258 186 := witness_check 48122207303528141025293695054995521536 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew512_3323_129 : Witnessed 512 3323 129 := witness_check 254422546068206553797994320131784776 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew512_3487_1 : Witnessed 512 3487 1 := witness_check 72 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew512_3519_319 : Witnessed 512 3519 319 := witness_check 365122979706185598654765026856133605720136 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew512_3551_287 : Witnessed 512 3551 287 := witness_check 365122979706166971525736404649809732960328 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew512_3583_389 : Witnessed 512 3583 389 := witness_check 365123234128713039502754751795377953833032 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew512_7567_143 : Witnessed 512 7567 143 := witness_check 254422546068206556412360674623094856 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew512_7575_151 : Witnessed 512 7575 151 := witness_check 254422546068436086634530258885279816 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew512_7583_407 : Witnessed 512 7583 407 := witness_check 365123234128713039732287588304546176172104 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew512_7599_271 : Witnessed 512 7599 271 := witness_check 365122979706166971296203568140641782202440 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew512_7615_279 : Witnessed 512 7615 279 := witness_check 365122979706166971525733790310226044387400 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew512_7679_511 : Witnessed 512 7679 511 := witness_check 365123235673997748539530465274934944858184 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew513_2114_66 : Witnessed 513 2114 66 := witness_check 1545266081678211640424481478934528 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew513_6158_2 : Witnessed 513 6158 2 := witness_check 271581184 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew513_6202_18 : Witnessed 513 6202 18 := witness_check 249621340805437924048896 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew513_6248_104 : Witnessed 513 6248 104 := witness_check 1545284708807243206859061473574912 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew513_14358_22 : Witnessed 513 14358 22 := witness_check 249621340837585754259456 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew513_14398_2 : Witnessed 513 14398 2 := witness_check 271581184 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew513_14462_2 : Witnessed 513 14462 2 := witness_check 271581184 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew640_324_324 : Witnessed 640 324 324 := witness_check 2113493782492482528849459556612491595218944 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew640_1396_276 : Witnessed 640 1396 276 := witness_check 2113493780945948796802323410726757752373248 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew640_3184_112 : Witnessed 640 3184 112 := witness_check 1546552378981585329806612646330368 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew640_3444_1332 : Witnessed 640 3444 1332 := witness_check 18059775734611461141188900921149274420655506853986304 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew640_15732_372 : Witnessed 640 15732 372 := witness_check 2113493782492501175552605016593126330990592 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew644_1072_1072 : Witnessed 644 1072 1072 := witness_check 18059775732497967360242952124578254733868993169326080 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew644_3184_112 : Witnessed 644 3184 112 := witness_check 1546552378981585329806612646330368 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew896_1072_1072 : Witnessed 896 1072 1072 := witness_check 18433920151654678507303095751244535966349567681626112 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1024_407_407 : Witnessed 1024 407 407 := witness_check 2124399276268460383033874594505688557815904 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1024_959_925 : Witnessed 1024 959 925 := witness_check 93531449761913701915983836312709584227001174112 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1024_994_482 : Witnessed 1024 994 482 := witness_check 6307150131931843648522112524284504407801856 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1024_1022_414 : Witnessed 1024 1022 414 := witness_check 2124399276268460383033877222356071128498176 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1024_2699_523 : Witnessed 1024 2699 523 := witness_check 93529325362637433455600802438115078538861742176 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1024_2707_659 : Witnessed 1024 2707 659 := witness_check 93529325379097014497156434462407510339005974624 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1024_2746_698 : Witnessed 1024 2746 698 := witness_check 93529325379097014517079531972284449520734437376 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1024_2811_641 : Witnessed 1024 2811 641 := witness_check 93529325379097014497156206017928901519709571168 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1024_3007_3007 : Witnessed 1024 3007 3007 := witness_check 990375243378112124475995468231794243733568830737521051744 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1024_3039_799 : Witnessed 1024 3039 799 := witness_check 93531449745454120874428432730267910863582660704 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1024_3071_901 : Witnessed 1024 3071 901 := witness_check 93531449761913701915983607865603125025343277152 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1024_7055_911 : Witnessed 1024 7055 911 := witness_check 93531449761913701915983607868230975408123152480 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1024_7063_5014 : Witnessed 1024 7063 5014 := witness_check 45615698311055102642244443652152027829652127096653983444893696 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1024_7071_791 : Witnessed 1024 7071 791 := witness_check 93531449745454120874428432727640060481011976288 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1024_7087_783 : Witnessed 1024 7087 783 := witness_check 93531449745454120874428204285789302044495448160 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1024_7103_3007 : Witnessed 1024 7103 3007 := witness_check 990375243378112124475995468231794243733568830737521051744 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1024_7167_1023 : Witnessed 1024 7167 1023 := witness_check 93531449761915173123656661194443447543981934688 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1152_884_788 : Witnessed 1152 884 788 := witness_check 436539217088571506149404731188386134747357642752 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1152_2672_624 : Witnessed 1152 2672 624 := witness_check 436537087261238509285674860340117731721045082112 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1152_2932_308 : Witnessed 1152 2932 308 := witness_check 2129827334558173785486321657381133744078848 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1152_6452_308 : Witnessed 1152 6452 308 := witness_check 2129827334558173785486321657381133744078848 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1152_6516_372 : Witnessed 1152 6516 372 := witness_check 2129827336063588101419858335996062344413184 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1152_15220_884 : Witnessed 1152 15220 884 := witness_check 436539217088573011583663105045427672541911056384 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1156_560_48 : Witnessed 1156 560 48 := witness_check 19942669059989436864393117696 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1156_2672_624 : Witnessed 1156 2672 624 := witness_check 436537087261238509285674860340117731721045082112 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1408_522_10 : Witnessed 1408 522 10 := witness_check 2751699372561399808 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew1408_560_48 : Witnessed 1408 560 48 := witness_check 20484276091318135756540608512 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew2048_1675_1547 : Witnessed 2048 1675 1547 := witness_check 3228552073437019889705276454558677054483005456253112 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew2048_1683_1555 : Witnessed 2048 1683 1555 := witness_check 3228552073437019889705276454807188663304262744801464 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew2048_1722_1722 : Witnessed 2048 1722 1722 := witness_check 24187947054399515431552379975070374999848161405042688 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew2048_1787_1665 : Witnessed 2048 1787 1665 := witness_check 3228552073437020725665070678665922320553156456480952 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew2048_1983_831 : Witnessed 2048 1983 831 := witness_check 94956976289948194667571187439266751246019068088 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew2048_2015_2015 : Witnessed 2048 2015 2015 := witness_check 3228552073840255332101652032412954621818573573062840 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew2048_2047_1925 : Witnessed 2048 2047 1925 := witness_check 3228552073840255330466382757870021230387053354549432 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew2048_6031_5775 : Witnessed 2048 6031 5775 := witness_check 46017432825348308753117192987200473175112293011286003042222264 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew2048_6039_1559 : Witnessed 2048 6039 1559 := witness_check 3228552073437019889705276454807188663331514312294584 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew2048_6047_1815 : Witnessed 2048 6047 1815 := witness_check 3228552073840254494506588534011287573138159642869944 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew2048_6063_6031 : Witnessed 2048 6063 6031 := witness_check 46017432825348308753520427592001785254316391921092648372797624 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew2048_6079_791 : Witnessed 2048 6079 791 := witness_check 94956976289948194648738541018382718204655435960 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew2048_6143_2047 : Witnessed 2048 6143 2047 := witness_check 3228552073840255332101670865059372578511857145872568 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew2049_578_578 : Witnessed 2049 578 578 := witness_check 94956573055345028605933382820864654039882268672 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew2049_4666_530 : Witnessed 2049 4666 530 := witness_check 94956573055343393336659336919472884307826704384 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew2049_4712_616 : Witnessed 2049 4712 616 := witness_check 346241369952388090183590502737950424530350505984 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew2049_12822_534 : Witnessed 2049 12822 534 := witness_check 94956573055343393336659336919472916661815345152 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew2049_12862_514 : Witnessed 2049 12862 514 := witness_check 94956573055343393336659088404936723292747333632 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew2049_12926_514 : Witnessed 2049 12926 514 := witness_check 94956573055343393336659088404936723292747333632 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew2176_1648_1648 : Witnessed 2176 1648 1648 := witness_check 24211582722205613307543664483386836030214559888310272 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew2176_1908_1844 : Witnessed 2176 1908 1844 := witness_check 24211582724357218711948221462971109515701943688757248 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew2176_5428_308 : Witnessed 2176 5428 308 := witness_check 2151605406041114015208736616242143308021760 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew2176_5492_1396 : Witnessed 2176 5492 1396 := witness_check 24211236126175343150639893878881325277194565653102592 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew2176_14196_1908 : Witnessed 2176 14196 1908 := witness_check 24211582724357218713584758387865753673034187526897664 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew2180_1648_1648 : Witnessed 2180 1648 1648 := witness_check 24211582722205613307543664483386836030214559888310272 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew4096_3983_1935 : Witnessed 4096 3983 1935 := witness_check 3368858371928228675238666601075678118354191002370328 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew4096_3991_2839 : Witnessed 4096 3991 2839 := witness_check 1300035123607892222652229621349865106345166120885736177944 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew4096_3999_3863 : Witnessed 4096 3999 3863 := witness_check 1300038492369166270383456080843404517377526427810247737624 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew4096_4015_1967 : Witnessed 4096 4015 1967 := witness_check 3368858371928228675238687955541355791163933012263192 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew4096_4031_4031 : Witnessed 4096 4031 4031 := witness_check 1300038492369166270384790501157402433758974166840573952280 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew4096_4095_4095 : Witnessed 4096 4095 4095 := witness_check 1300038492369166270384791985021658163415752956325219795224 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew4097_2618_2578 : Witnessed 4097 2618 2578 := witness_check 1300035123607891786750517595627693428965354549636532666368 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew4097_2664_2664 : Witnessed 4097 2664 2664 := witness_check 1986784688201069181377776448101249163542941767089946361856 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew4097_10774_2582 : Witnessed 4097 10774 2582 := witness_check 1300035123607891786750517595627693428965354581522369871872 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew4097_10814_2562 : Witnessed 4097 10814 2562 := witness_check 1300035123607891786750517595627693176687682597584704765952 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew4097_10878_2562 : Witnessed 4097 10878 2562 := witness_check 1300035123607891786750517595627693176687682597584704765952 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew4224_3380_3124 : Witnessed 4224 3380 3124 := witness_check 1301585982819733293809640838817894093715505256737743568896 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew4224_3444_3444 : Witnessed 4224 3444 3444 := witness_check 1301585982819739660833009782897040887031022505030800375808 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew4224_12148_3956 : Witnessed 4224 12148 3956 := witness_check 1301585983259844867326011630595248287141737919351323885568 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew8193_6678_22 : Witnessed 8193 6678 22 := witness_check 271536072801838600028160 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew8193_6718_6658 : Witnessed 8193 6718 6658 := witness_check 73141807380888975663625659748542992860862658598050560154271744 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew8193_6782_6658 : Witnessed 8193 6782 6658 := witness_check 73141807380888975663625659748542992860862658598050560154271744 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem ew8320_8052_8052 : Witnessed 8320 8052 8052 := witness_check 111822290915864924331502525502036865546812204321691599556837376 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_133_1 : CountBound 0 133 1 := by
  exact width_of_mask ew0_133_129 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_385_1 : CountBound 0 385 1 := by
  exact width_of_mask ew0_385_385 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_386_1 : CountBound 0 386 1 := by
  exact width_of_mask ew0_386_130 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_386_1 : CountBound 1 386 1 := by
  exact width_of_mask ew1_386_384 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_518_1 : CountBound 1 518 1 := by
  exact width_of_mask ew1_518_514 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_642_1 : CountBound 1 642 1 := by
  exact width_of_mask ew1_642_642 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_2562_1 : CountBound 1 2562 1 := by
  exact width_of_mask ew1_2562_514 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_2624_1 : CountBound 1 2624 1 := by
  exact width_of_mask ew1_2624_2624 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb3_1284_1 : CountBound 3 1284 1 := by
  exact width_of_mask ew3_1284_1280 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb3_2368_1 : CountBound 3 2368 1 := by
  exact width_of_mask ew3_2368_2368 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_259_1 : CountBound 128 259 1 := by
  exact width_of_mask ew128_259_3 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_276_1 : CountBound 128 276 1 := by
  exact width_of_mask ew128_276_260 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_772_1 : CountBound 128 772 1 := by
  exact width_of_mask ew128_772_260 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_832_1 : CountBound 128 832 1 := by
  exact width_of_mask ew128_832_832 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb132_515_1 : CountBound 132 515 1 := by
  exact width_of_mask ew132_515_3 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb132_560_1 : CountBound 132 560 1 := by
  exact width_of_mask ew132_560_544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb132_832_1 : CountBound 132 832 1 := by
  exact width_of_mask ew132_832_832 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb132_1552_1 : CountBound 132 1552 1 := by
  exact width_of_mask ew132_1552_1040 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb132_1568_1 : CountBound 132 1568 1 := by
  exact width_of_mask ew132_1568_1568 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb132_4384_1 : CountBound 132 4384 1 := by
  exact width_of_mask ew132_4384_4352 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb148_832_1 : CountBound 148 832 1 := by
  exact width_of_mask ew148_832_832 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb148_3104_1 : CountBound 148 3104 1 := by
  exact width_of_mask ew148_3104_3072 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb384_522_1 : CountBound 384 522 1 := by
  exact width_of_mask ew384_522_10 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb384_560_1 : CountBound 384 560 1 := by
  exact width_of_mask ew384_560_544 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb384_1552_1 : CountBound 384 1552 1 := by
  exact width_of_mask ew384_1552_1040 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb384_1568_1 : CountBound 384 1568 1 := by
  exact width_of_mask ew384_1568_1568 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb400_522_1 : CountBound 400 522 1 := by
  exact width_of_mask ew400_522_10 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb400_1568_1 : CountBound 400 1568 1 := by
  exact width_of_mask ew400_1568_1568 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb400_3104_1 : CountBound 400 3104 1 := by
  exact width_of_mask ew400_3104_3072 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1408_522_1 : CountBound 1408 522 1 := by
  exact width_of_mask ew1408_522_10 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_387_4 : CountBound 0 387 4 := by
  let rs : List Row := [⟨0,false,2,1⟩, ⟨0,true,128,1⟩, ⟨1,false,129,1⟩, ⟨1,true,1,1⟩, ⟨7,false,1,1⟩, ⟨7,true,3,1⟩, ⟨8,false,131,0⟩, ⟨8,true,131,0⟩]
  apply rule_tables (rs:=rs) ?_ (by decide +kernel) ew0_387_387 ?_
  · unfold rs
    refine rows_cons ⟨ew0_386_2, lb0_386_1⟩ ?_
    refine rows_cons ⟨ew1_386_128, lb1_386_1⟩ ?_
    refine rows_cons ⟨ew0_385_129, lb0_385_1⟩ ?_
    refine rows_cons ⟨ew2_385_1, (transfer (s:=2) (a:=385) (t:=1) (u:=642) perm26 (by decide +kernel) (by decide +kernel) lb1_642_1)⟩ ?_
    refine rows_cons ⟨ew0_259_1, (transfer (s:=0) (a:=259) (t:=0) (u:=133) perm4 (by decide +kernel) (by decide +kernel) lb0_133_1)⟩ ?_
    refine rows_cons ⟨ew128_259_3, lb128_259_1⟩ ?_
    refine rows_cons ⟨ew0_131_131, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew256_131_131, (zero_bound _ _)⟩ ?_
    exact rows_nil _ _
  · unfold rs; decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_2626_4 : CountBound 1 2626 4 := by
  let rs : List Row := [⟨1,false,576,1⟩, ⟨1,true,64,1⟩, ⟨6,false,514,1⟩, ⟨6,true,512,1⟩, ⟨9,false,64,1⟩, ⟨9,true,66,1⟩, ⟨11,false,578,0⟩, ⟨11,true,578,0⟩]
  apply rule_tables (rs:=rs) ?_ (by decide +kernel) ew1_2626_2626 ?_
  · unfold rs
    refine rows_cons ⟨ew1_2624_576, lb1_2624_1⟩ ?_
    refine rows_cons ⟨ew3_2624_64, (transfer (s:=3) (a:=2624) (t:=3) (u:=2368) perm26 (by decide +kernel) (by decide +kernel) lb3_2368_1)⟩ ?_
    refine rows_cons ⟨ew1_2562_514, lb1_2562_1⟩ ?_
    refine rows_cons ⟨ew65_2562_512, (transfer (s:=65) (a:=2562) (t:=3) (u:=1284) perm29 (by decide +kernel) (by decide +kernel) lb3_1284_1)⟩ ?_
    refine rows_cons ⟨ew1_2114_64, (transfer (s:=1) (a:=2114) (t:=1) (u:=518) perm5 (by decide +kernel) (by decide +kernel) lb1_518_1)⟩ ?_
    refine rows_cons ⟨ew513_2114_66, (transfer (s:=513) (a:=2114) (t:=132) (u:=515) perm50 (by decide +kernel) (by decide +kernel) lb132_515_1)⟩ ?_
    refine rows_cons ⟨ew1_578_578, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew2049_578_578, (zero_bound _ _)⟩ ?_
    exact rows_nil _ _
  · unfold rs; decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_836_4 : CountBound 128 836 4 := by
  let rs : List Row := [⟨2,false,320,1⟩, ⟨2,true,64,1⟩, ⟨6,false,260,1⟩, ⟨6,true,256,1⟩, ⟨8,false,64,1⟩, ⟨8,true,68,1⟩, ⟨9,false,324,0⟩, ⟨9,true,324,0⟩]
  apply rule_tables (rs:=rs) ?_ (by decide +kernel) ew128_836_836 ?_
  · unfold rs
    refine rows_cons ⟨ew128_832_320, lb128_832_1⟩ ?_
    refine rows_cons ⟨ew132_832_64, lb132_832_1⟩ ?_
    refine rows_cons ⟨ew128_772_260, lb128_772_1⟩ ?_
    refine rows_cons ⟨ew192_772_256, (transfer (s:=192) (a:=772) (t:=132) (u:=4384) perm74 (by decide +kernel) (by decide +kernel) lb132_4384_1)⟩ ?_
    refine rows_cons ⟨ew128_580_64, (transfer (s:=128) (a:=580) (t:=128) (u:=276) perm25 (by decide +kernel) (by decide +kernel) lb128_276_1)⟩ ?_
    refine rows_cons ⟨ew384_580_68, (transfer (s:=384) (a:=580) (t:=384) (u:=522) perm21 (by decide +kernel) (by decide +kernel) lb384_522_1)⟩ ?_
    refine rows_cons ⟨ew128_324_324, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew640_324_324, (zero_bound _ _)⟩ ?_
    exact rows_nil _ _
  · unfold rs; decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb132_1584_4 : CountBound 132 1584 4 := by
  let rs : List Row := [⟨4,false,1056,1⟩, ⟨4,true,32,1⟩, ⟨5,false,16,1⟩, ⟨5,true,512,1⟩, ⟨9,false,1072,0⟩, ⟨9,true,1072,0⟩, ⟨10,false,32,1⟩, ⟨10,true,48,1⟩]
  apply rule_tables (rs:=rs) ?_ (by decide +kernel) ew132_1584_1584 ?_
  · unfold rs
    refine rows_cons ⟨ew132_1568_1056, lb132_1568_1⟩ ?_
    refine rows_cons ⟨ew148_1568_32, (transfer (s:=148) (a:=1568) (t:=148) (u:=832) perm1 (by decide +kernel) (by decide +kernel) lb148_832_1)⟩ ?_
    refine rows_cons ⟨ew132_1552_16, lb132_1552_1⟩ ?_
    refine rows_cons ⟨ew164_1552_512, (transfer (s:=164) (a:=1552) (t:=148) (u:=3104) perm8 (by decide +kernel) (by decide +kernel) lb148_3104_1)⟩ ?_
    refine rows_cons ⟨ew132_1072_1072, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew644_1072_1072, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew132_560_32, lb132_560_1⟩ ?_
    refine rows_cons ⟨ew1156_560_48, (transfer (s:=1156) (a:=560) (t:=400) (u:=522) perm22 (by decide +kernel) (by decide +kernel) lb400_522_1)⟩ ?_
    exact rows_nil _ _
  · unfold rs; decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb384_1584_4 : CountBound 384 1584 4 := by
  let rs : List Row := [⟨4,false,1056,1⟩, ⟨4,true,32,1⟩, ⟨5,false,16,1⟩, ⟨5,true,512,1⟩, ⟨9,false,1072,0⟩, ⟨9,true,1072,0⟩, ⟨10,false,32,1⟩, ⟨10,true,48,1⟩]
  apply rule_tables (rs:=rs) ?_ (by decide +kernel) ew384_1584_1584 ?_
  · unfold rs
    refine rows_cons ⟨ew384_1568_1056, lb384_1568_1⟩ ?_
    refine rows_cons ⟨ew400_1568_32, lb400_1568_1⟩ ?_
    refine rows_cons ⟨ew384_1552_16, lb384_1552_1⟩ ?_
    refine rows_cons ⟨ew416_1552_512, (transfer (s:=416) (a:=1552) (t:=400) (u:=3104) perm8 (by decide +kernel) (by decide +kernel) lb400_3104_1)⟩ ?_
    refine rows_cons ⟨ew384_1072_1072, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew896_1072_1072, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew384_560_32, lb384_560_1⟩ ?_
    refine rows_cons ⟨ew1408_560_48, (transfer (s:=1408) (a:=560) (t:=1408) (u:=522) perm17 (by decide +kernel) (by decide +kernel) lb1408_522_1)⟩ ?_
    exact rows_nil _ _
  · unfold rs; decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_403_4 : CountBound 0 403 4 := by
  exact fix_one 4 false (by decide +kernel) lb0_387_4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_899_5 : CountBound 0 899 5 := by
  exact fixE 8 false ew0_899_256 (by decide +kernel) ew0_643_1 (by decide +kernel) (transfer (s:=0) (a:=643) (t:=0) (u:=387) perm25 (by decide +kernel) (by decide +kernel) lb0_387_4)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_901_4 : CountBound 0 901 4 := by
  exact fix_one 9 false (by decide +kernel) (transfer (s:=0) (a:=389) (t:=0) (u:=387) perm4 (by decide +kernel) (by decide +kernel) lb0_387_4)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_1411_5 : CountBound 0 1411 5 := by
  exact fixE 8 false ew0_1411_256 (by decide +kernel) ew0_1155_1 (by decide +kernel) (transfer (s:=0) (a:=1155) (t:=0) (u:=387) perm1 (by decide +kernel) (by decide +kernel) lb0_387_4)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_2630_4 : CountBound 1 2630 4 := by
  exact fix_one 2 false (by decide +kernel) lb1_2626_4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_2642_4 : CountBound 1 2642 4 := by
  exact width_of_mask ew1_2642_2642 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_2768_5 : CountBound 1 2768 5 := by
  exact fixE 7 false ew1_2768_128 (by decide +kernel) ew1_2640_16 (by decide +kernel) (transfer (s:=1) (a:=2640) (t:=1) (u:=2626) perm13 (by decide +kernel) (by decide +kernel) lb1_2626_4)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_2882_5 : CountBound 1 2882 5 := by
  exact fixE 8 false ew1_2882_256 (by decide +kernel) ew1_2626_2 (by decide +kernel) lb1_2626_4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_6668_4 : CountBound 1 6668 4 := by
  exact fix_one 9 false (by decide +kernel) (transfer (s:=1) (a:=6156) (t:=1) (u:=2626) perm4 (by decide +kernel) (by decide +kernel) lb1_2626_4)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_6696_4 : CountBound 1 6696 4 := by
  exact width_of_mask ew1_6696_6696 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_6696_5 : CountBound 1 6696 5 := by
  exact fixE 9 false ew1_6696_512 (by decide +kernel) ew1_6184_8 (by decide +kernel) (transfer (s:=1) (a:=6184) (t:=1) (u:=2626) perm7 (by decide +kernel) (by decide +kernel) lb1_2626_4)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb3_3408_4 : CountBound 3 3408 4 := by
  exact width_of_mask ew3_3408_3408 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_852_4 : CountBound 128 852 4 := by
  exact fix_one 4 false (by decide +kernel) lb128_836_4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_868_4 : CountBound 128 868 4 := by
  exact width_of_mask ew128_868_868 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_1840_4 : CountBound 128 1840 4 := by
  exact fix_one 8 false (by decide +kernel) (transfer (s:=128) (a:=1584) (t:=128) (u:=836) perm1 (by decide +kernel) (by decide +kernel) lb128_836_4)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_1888_5 : CountBound 128 1888 5 := by
  exact fixE 8 false ew128_1888_256 (by decide +kernel) ew128_1632_32 (by decide +kernel) (transfer (s:=128) (a:=1632) (t:=128) (u:=836) perm25 (by decide +kernel) (by decide +kernel) lb128_836_4)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_2884_5 : CountBound 128 2884 5 := by
  exact fixE 9 false ew128_2884_512 (by decide +kernel) ew128_2372_4 (by decide +kernel) (transfer (s:=128) (a:=2372) (t:=128) (u:=836) perm8 (by decide +kernel) (by decide +kernel) lb128_836_4)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_3632_4 : CountBound 128 3632 4 := by
  exact width_of_mask ew128_3632_3632 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_3632_5 : CountBound 128 3632 5 := by
  exact fixE 9 false ew128_3632_512 (by decide +kernel) ew128_3120_16 (by decide +kernel) (transfer (s:=128) (a:=3120) (t:=128) (u:=836) perm9 (by decide +kernel) (by decide +kernel) lb128_836_4)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb132_1571_4 : CountBound 132 1571 4 := by
  exact width_of_mask ew132_1571_1571 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb132_1592_5 : CountBound 132 1592 5 := by
  exact fixE 3 false ew132_1592_8 (by decide +kernel) ew132_1584_16 (by decide +kernel) lb132_1584_4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb132_1648_4 : CountBound 132 1648 4 := by
  exact width_of_mask ew132_1648_1648 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb132_1840_5 : CountBound 132 1840 5 := by
  exact fixE 8 false ew132_1840_256 (by decide +kernel) ew132_1584_16 (by decide +kernel) lb132_1584_4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb132_1888_5 : CountBound 132 1888 5 := by
  exact fixE 8 false ew132_1888_256 (by decide +kernel) ew132_1632_32 (by decide +kernel) (transfer (s:=132) (a:=1632) (t:=132) (u:=1584) perm24 (by decide +kernel) (by decide +kernel) lb132_1584_4)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb132_2896_5 : CountBound 132 2896 5 := by
  exact fixE 8 false ew132_2896_256 (by decide +kernel) ew132_2640_16 (by decide +kernel) (transfer (s:=132) (a:=2640) (t:=132) (u:=1584) perm76 (by decide +kernel) (by decide +kernel) lb132_1584_4)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb132_3632_4 : CountBound 132 3632 4 := by
  exact width_of_mask ew132_3632_3632 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb132_3632_5 : CountBound 132 3632 5 := by
  exact fixE 9 false ew132_3632_512 (by decide +kernel) ew132_3120_16 (by decide +kernel) (transfer (s:=132) (a:=3120) (t:=132) (u:=1584) perm8 (by decide +kernel) (by decide +kernel) lb132_1584_4)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb132_4960_4 : CountBound 132 4960 4 := by
  exact width_of_mask ew132_4960_4960 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb148_3680_4 : CountBound 148 3680 4 := by
  exact width_of_mask ew148_3680_3680 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb384_3632_5 : CountBound 384 3632 5 := by
  exact fixE 9 false ew384_3632_512 (by decide +kernel) ew384_3120_16 (by decide +kernel) (transfer (s:=384) (a:=3120) (t:=384) (u:=1584) perm5 (by decide +kernel) (by decide +kernel) lb384_1584_4)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb384_4650_4 : CountBound 384 4650 4 := by
  exact width_of_mask ew384_4650_4650 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb384_5680_5 : CountBound 384 5680 5 := by
  exact fixE 9 false ew384_5680_512 (by decide +kernel) ew384_5168_16 (by decide +kernel) (transfer (s:=384) (a:=5168) (t:=384) (u:=1584) perm4 (by decide +kernel) (by decide +kernel) lb384_1584_4)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb400_4650_4 : CountBound 400 4650 4 := by
  exact width_of_mask ew400_4650_4650 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_407_5 : CountBound 0 407 5 := by
  exact fixE 1 false ew0_407_2 (by decide +kernel) ew0_405_1 (by decide +kernel) (transfer (s:=0) (a:=405) (t:=0) (u:=403) perm4 (by decide +kernel) (by decide +kernel) lb0_403_4)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_413_5 : CountBound 0 413 5 := by
  exact fixE 2 false ew0_413_4 (by decide +kernel) ew0_409_1 (by decide +kernel) (transfer (s:=0) (a:=409) (t:=0) (u:=403) perm11 (by decide +kernel) (by decide +kernel) lb0_403_4)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_462_5 : CountBound 0 462 5 := by
  exact width_of_mask ew0_462_462 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_903_5 : CountBound 0 903 5 := by
  exact width_of_mask ew0_903_903 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_907_5 : CountBound 0 907 5 := by
  exact width_of_mask ew0_907_907 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_907_6 : CountBound 0 907 6 := by
  exact fixE 3 false ew0_907_8 (by decide +kernel) ew0_899_1 (by decide +kernel) lb0_899_5

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_910_6 : CountBound 0 910 6 := by
  exact fixE 2 true ew0_910_4 (by decide +kernel) ew4_906_2 (by decide +kernel) (transfer (s:=4) (a:=906) (t:=1) (u:=2768) perm92 (by decide +kernel) (by decide +kernel) lb1_2768_5)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_940_5 : CountBound 0 940 5 := by
  exact width_of_mask ew0_940_940 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_1415_5 : CountBound 0 1415 5 := by
  exact width_of_mask ew0_1415_1415 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_1415_6 : CountBound 0 1415 6 := by
  exact fixE 1 false ew0_1415_2 (by decide +kernel) ew0_1413_1 (by decide +kernel) (transfer (s:=0) (a:=1413) (t:=0) (u:=1411) perm4 (by decide +kernel) (by decide +kernel) lb0_1411_5)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_1430_5 : CountBound 0 1430 5 := by
  exact width_of_mask ew0_1430_1430 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_1923_6 : CountBound 0 1923 6 := by
  exact fixE 8 false ew0_1923_256 (by decide +kernel) ew0_1667_1 (by decide +kernel) (transfer (s:=0) (a:=1667) (t:=0) (u:=899) perm1 (by decide +kernel) (by decide +kernel) lb0_899_5)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_1954_5 : CountBound 0 1954 5 := by
  exact fixE 7 false ew0_1954_128 (by decide +kernel) ew0_1826_2 (by decide +kernel) (transfer (s:=0) (a:=1826) (t:=0) (u:=901) perm30 (by decide +kernel) (by decide +kernel) lb0_901_4)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_3715_5 : CountBound 0 3715 5 := by
  exact fixE 9 false ew0_3715_512 (by decide +kernel) ew0_3203_1 (by decide +kernel) (transfer (s:=0) (a:=3203) (t:=0) (u:=901) perm6 (by decide +kernel) (by decide +kernel) lb0_901_4)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_3730_5 : CountBound 0 3730 5 := by
  exact width_of_mask ew0_3730_3730 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_2618_5 : CountBound 1 2618 5 := by
  exact width_of_mask ew1_2618_2618 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_2638_5 : CountBound 1 2638 5 := by
  exact fixE 1 false ew1_2638_2 (by decide +kernel) ew1_2636_8 (by decide +kernel) (transfer (s:=1) (a:=2636) (t:=1) (u:=2630) perm8 (by decide +kernel) (by decide +kernel) lb1_2630_4)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_2770_5 : CountBound 1 2770 5 := by
  exact width_of_mask ew1_2770_2770 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_2890_6 : CountBound 1 2890 6 := by
  exact fixE 1 false ew1_2890_2 (by decide +kernel) ew1_2888_8 (by decide +kernel) (transfer (s:=1) (a:=2888) (t:=1) (u:=2882) perm8 (by decide +kernel) (by decide +kernel) lb1_2882_5)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_2954_5 : CountBound 1 2954 5 := by
  exact width_of_mask ew1_2954_2954 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_3722_5 : CountBound 1 3722 5 := by
  exact width_of_mask ew1_3722_3722 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_3730_5 : CountBound 1 3730 5 := by
  exact width_of_mask ew1_3730_3730 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_3778_5 : CountBound 1 3778 5 := by
  exact width_of_mask ew1_3778_3778 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_3778_6 : CountBound 1 3778 6 := by
  exact fixE 7 false ew1_3778_128 (by decide +kernel) ew1_3650_2 (by decide +kernel) (transfer (s:=1) (a:=3650) (t:=1) (u:=2768) perm13 (by decide +kernel) (by decide +kernel) lb1_2768_5)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_6670_6 : CountBound 1 6670 6 := by
  exact fixE 9 true ew1_6670_512 (by decide +kernel) ew513_6158_2 (by decide +kernel) (transfer (s:=513) (a:=6158) (t:=132) (u:=1592) perm58 (by decide +kernel) (by decide +kernel) lb132_1592_5)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_6678_5 : CountBound 1 6678 5 := by
  exact width_of_mask ew1_6678_6678 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_6698_5 : CountBound 1 6698 5 := by
  exact width_of_mask ew1_6698_6698 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_6698_6 : CountBound 1 6698 6 := by
  exact fixE 1 false ew1_6698_2 (by decide +kernel) ew1_6696_8 (by decide +kernel) lb1_6696_5

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_6700_5 : CountBound 1 6700 5 := by
  exact width_of_mask ew1_6700_6700 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_6700_6 : CountBound 1 6700 6 := by
  exact fixE 2 false ew1_6700_4 (by decide +kernel) ew1_6696_8 (by decide +kernel) lb1_6696_5

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_6760_6 : CountBound 1 6760 6 := by
  exact fixE 3 false ew1_6760_8 (by decide +kernel) ew1_6752_32 (by decide +kernel) (transfer (s:=1) (a:=6752) (t:=1) (u:=6696) perm4 (by decide +kernel) (by decide +kernel) lb1_6696_5)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_6760_7 : CountBound 1 6760 7 := by
  let rs : List Row := [⟨3,false,32,4⟩, ⟨3,true,32,4⟩, ⟨5,false,8,4⟩, ⟨5,true,8,4⟩, ⟨6,false,40,4⟩, ⟨6,true,40,4⟩, ⟨9,false,104,4⟩, ⟨9,true,104,4⟩, ⟨11,false,616,4⟩, ⟨11,true,616,4⟩, ⟨12,false,2664,0⟩, ⟨12,true,2664,0⟩]
  apply rule_tables (rs:=rs) ?_ (by decide +kernel) ew1_6760_6760 ?_
  · unfold rs
    refine rows_cons ⟨ew1_6752_32, (transfer (s:=1) (a:=6752) (t:=1) (u:=6696) perm4 (by decide +kernel) (by decide +kernel) lb1_6696_4)⟩ ?_
    refine rows_cons ⟨ew9_6752_32, (transfer (s:=9) (a:=6752) (t:=3) (u:=3408) perm32 (by decide +kernel) (by decide +kernel) lb3_3408_4)⟩ ?_
    refine rows_cons ⟨ew1_6728_8, (transfer (s:=1) (a:=6728) (t:=1) (u:=6696) perm1 (by decide +kernel) (by decide +kernel) lb1_6696_4)⟩ ?_
    refine rows_cons ⟨ew33_6728_8, (transfer (s:=33) (a:=6728) (t:=3) (u:=3408) perm30 (by decide +kernel) (by decide +kernel) lb3_3408_4)⟩ ?_
    refine rows_cons ⟨ew1_6696_40, lb1_6696_4⟩ ?_
    refine rows_cons ⟨ew65_6696_40, (transfer (s:=65) (a:=6696) (t:=3) (u:=3408) perm29 (by decide +kernel) (by decide +kernel) lb3_3408_4)⟩ ?_
    refine rows_cons ⟨ew1_6248_104, (transfer (s:=1) (a:=6248) (t:=1) (u:=2642) perm5 (by decide +kernel) (by decide +kernel) lb1_2642_4)⟩ ?_
    refine rows_cons ⟨ew513_6248_104, (transfer (s:=513) (a:=6248) (t:=132) (u:=1571) perm58 (by decide +kernel) (by decide +kernel) lb132_1571_4)⟩ ?_
    refine rows_cons ⟨ew1_4712_616, (transfer (s:=1) (a:=4712) (t:=1) (u:=2642) perm10 (by decide +kernel) (by decide +kernel) lb1_2642_4)⟩ ?_
    refine rows_cons ⟨ew2049_4712_616, (transfer (s:=2049) (a:=4712) (t:=132) (u:=1571) perm63 (by decide +kernel) (by decide +kernel) lb132_1571_4)⟩ ?_
    refine rows_cons ⟨ew1_2664_2664, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew4097_2664_2664, (zero_bound _ _)⟩ ?_
    exact rows_nil _ _
  · unfold rs; decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_6824_6 : CountBound 1 6824 6 := by
  exact fixE 7 false ew1_6824_128 (by decide +kernel) ew1_6696_8 (by decide +kernel) lb1_6696_5

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_6880_6 : CountBound 1 6880 6 := by
  exact fixE 7 false ew1_6880_128 (by decide +kernel) ew1_6752_32 (by decide +kernel) (transfer (s:=1) (a:=6752) (t:=1) (u:=6696) perm4 (by decide +kernel) (by decide +kernel) lb1_6696_5)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_14854_5 : CountBound 1 14854 5 := by
  exact fixE 9 false ew1_14854_512 (by decide +kernel) ew1_14342_2 (by decide +kernel) (transfer (s:=1) (a:=14342) (t:=1) (u:=6668) perm5 (by decide +kernel) (by decide +kernel) lb1_6668_4)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb3_6428_5 : CountBound 3 6428 5 := by
  exact width_of_mask ew3_6428_6428 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb3_7472_5 : CountBound 3 7472 5 := by
  exact width_of_mask ew3_7472_7472 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_807_5 : CountBound 128 807 5 := by
  exact width_of_mask ew128_807_807 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_846_5 : CountBound 128 846 5 := by
  exact width_of_mask ew128_846_846 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_884_5 : CountBound 128 884 5 := by
  exact fixE 2 false ew128_884_4 (by decide +kernel) ew128_880_32 (by decide +kernel) (transfer (s:=128) (a:=880) (t:=128) (u:=852) perm26 (by decide +kernel) (by decide +kernel) lb128_852_4)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_1303_5 : CountBound 128 1303 5 := by
  exact width_of_mask ew128_1303_1303 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_1396_5 : CountBound 128 1396 5 := by
  exact width_of_mask ew128_1396_1396 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_1844_5 : CountBound 128 1844 5 := by
  exact width_of_mask ew128_1844_1844 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_1844_6 : CountBound 128 1844 6 := by
  exact fixE 2 true ew128_1844_4 (by decide +kernel) ew132_1840_16 (by decide +kernel) lb132_1840_5

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_1890_6 : CountBound 128 1890 6 := by
  exact fixE 1 false ew128_1890_2 (by decide +kernel) ew128_1888_32 (by decide +kernel) lb128_1888_5

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_1892_5 : CountBound 128 1892 5 := by
  exact width_of_mask ew128_1892_1892 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_1892_6 : CountBound 128 1892 6 := by
  exact fixE 2 false ew128_1892_4 (by decide +kernel) ew128_1888_32 (by decide +kernel) lb128_1888_5

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_1896_6 : CountBound 128 1896 6 := by
  exact fixE 3 false ew128_1896_8 (by decide +kernel) ew128_1888_32 (by decide +kernel) lb128_1888_5

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_2900_6 : CountBound 128 2900 6 := by
  exact fixE 2 false ew128_2900_4 (by decide +kernel) ew128_2896_16 (by decide +kernel) (transfer (s:=128) (a:=2896) (t:=128) (u:=2884) perm34 (by decide +kernel) (by decide +kernel) lb128_2884_5)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_3633_6 : CountBound 128 3633 6 := by
  exact fixE 0 false ew128_3633_1 (by decide +kernel) ew128_3632_16 (by decide +kernel) lb128_3632_5

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_3634_5 : CountBound 128 3634 5 := by
  exact width_of_mask ew128_3634_3634 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_3634_6 : CountBound 128 3634 6 := by
  exact fixE 1 false ew128_3634_2 (by decide +kernel) ew128_3632_16 (by decide +kernel) lb128_3632_5

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_3696_7 : CountBound 128 3696 7 := by
  let rs : List Row := [⟨4,false,32,4⟩, ⟨4,true,32,4⟩, ⟨5,false,16,4⟩, ⟨5,true,16,4⟩, ⟨6,false,48,4⟩, ⟨6,true,48,4⟩, ⟨9,false,112,4⟩, ⟨9,true,112,4⟩, ⟨10,false,624,4⟩, ⟨10,true,624,4⟩, ⟨11,false,1648,0⟩, ⟨11,true,1648,0⟩]
  apply rule_tables (rs:=rs) ?_ (by decide +kernel) ew128_3696_3696 ?_
  · unfold rs
    refine rows_cons ⟨ew128_3680_32, (transfer (s:=128) (a:=3680) (t:=128) (u:=3632) perm24 (by decide +kernel) (by decide +kernel) lb128_3632_4)⟩ ?_
    refine rows_cons ⟨ew144_3680_32, (transfer (s:=144) (a:=3680) (t:=132) (u:=4960) perm1 (by decide +kernel) (by decide +kernel) lb132_4960_4)⟩ ?_
    refine rows_cons ⟨ew128_3664_16, (transfer (s:=128) (a:=3664) (t:=128) (u:=3632) perm32 (by decide +kernel) (by decide +kernel) lb128_3632_4)⟩ ?_
    refine rows_cons ⟨ew160_3664_16, (transfer (s:=160) (a:=3664) (t:=132) (u:=4960) perm9 (by decide +kernel) (by decide +kernel) lb132_4960_4)⟩ ?_
    refine rows_cons ⟨ew128_3632_48, lb128_3632_4⟩ ?_
    refine rows_cons ⟨ew192_3632_48, (transfer (s:=192) (a:=3632) (t:=132) (u:=4960) perm25 (by decide +kernel) (by decide +kernel) lb132_4960_4)⟩ ?_
    refine rows_cons ⟨ew128_3184_112, (transfer (s:=128) (a:=3184) (t:=128) (u:=868) perm9 (by decide +kernel) (by decide +kernel) lb128_868_4)⟩ ?_
    refine rows_cons ⟨ew640_3184_112, (transfer (s:=640) (a:=3184) (t:=384) (u:=4650) perm50 (by decide +kernel) (by decide +kernel) lb384_4650_4)⟩ ?_
    refine rows_cons ⟨ew128_2672_624, (transfer (s:=128) (a:=2672) (t:=128) (u:=868) perm73 (by decide +kernel) (by decide +kernel) lb128_868_4)⟩ ?_
    refine rows_cons ⟨ew1152_2672_624, (transfer (s:=1152) (a:=2672) (t:=384) (u:=4650) perm6 (by decide +kernel) (by decide +kernel) lb384_4650_4)⟩ ?_
    refine rows_cons ⟨ew128_1648_1648, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew2176_1648_1648, (zero_bound _ _)⟩ ?_
    exact rows_nil _ _
  · unfold rs; decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_3920_6 : CountBound 128 3920 6 := by
  exact fixE 8 false ew128_3920_256 (by decide +kernel) ew128_3664_16 (by decide +kernel) (transfer (s:=128) (a:=3664) (t:=128) (u:=3632) perm32 (by decide +kernel) (by decide +kernel) lb128_3632_5)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_7444_5 : CountBound 128 7444 5 := by
  exact width_of_mask ew128_7444_7444 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_7460_5 : CountBound 128 7460 5 := by
  exact fixE 8 false ew128_7460_256 (by decide +kernel) ew128_7204_4 (by decide +kernel) (transfer (s:=128) (a:=7204) (t:=128) (u:=1840) perm33 (by decide +kernel) (by decide +kernel) lb128_1840_4)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb132_1594_5 : CountBound 132 1594 5 := by
  exact width_of_mask ew132_1594_1594 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb132_1619_5 : CountBound 132 1619 5 := by
  exact width_of_mask ew132_1619_1619 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb132_1848_6 : CountBound 132 1848 6 := by
  exact fixE 3 false ew132_1848_8 (by decide +kernel) ew132_1840_16 (by decide +kernel) lb132_1840_5

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb132_1904_6 : CountBound 132 1904 6 := by
  exact fixE 4 false ew132_1904_16 (by decide +kernel) ew132_1888_32 (by decide +kernel) lb132_1888_5

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb132_3633_6 : CountBound 132 3633 6 := by
  exact fixE 0 false ew132_3633_1 (by decide +kernel) ew132_3632_16 (by decide +kernel) lb132_3632_5

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb132_3634_6 : CountBound 132 3634 6 := by
  exact fixE 1 false ew132_3634_2 (by decide +kernel) ew132_3632_16 (by decide +kernel) lb132_3632_5

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb132_3696_6 : CountBound 132 3696 6 := by
  exact fixE 4 false ew132_3696_16 (by decide +kernel) ew132_3680_32 (by decide +kernel) (transfer (s:=132) (a:=3680) (t:=132) (u:=3632) perm24 (by decide +kernel) (by decide +kernel) lb132_3632_5)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb132_3696_7 : CountBound 132 3696 7 := by
  let rs : List Row := [⟨4,false,32,4⟩, ⟨4,true,32,4⟩, ⟨5,false,16,4⟩, ⟨5,true,16,4⟩, ⟨6,false,48,4⟩, ⟨6,true,48,4⟩, ⟨9,false,112,4⟩, ⟨9,true,112,4⟩, ⟨10,false,624,4⟩, ⟨10,true,624,4⟩, ⟨11,false,1648,0⟩, ⟨11,true,1648,0⟩]
  apply rule_tables (rs:=rs) ?_ (by decide +kernel) ew132_3696_3696 ?_
  · unfold rs
    refine rows_cons ⟨ew132_3680_32, (transfer (s:=132) (a:=3680) (t:=132) (u:=3632) perm24 (by decide +kernel) (by decide +kernel) lb132_3632_4)⟩ ?_
    refine rows_cons ⟨ew148_3680_32, lb148_3680_4⟩ ?_
    refine rows_cons ⟨ew132_3664_16, (transfer (s:=132) (a:=3664) (t:=132) (u:=3632) perm32 (by decide +kernel) (by decide +kernel) lb132_3632_4)⟩ ?_
    refine rows_cons ⟨ew164_3664_16, (transfer (s:=164) (a:=3664) (t:=148) (u:=3680) perm8 (by decide +kernel) (by decide +kernel) lb148_3680_4)⟩ ?_
    refine rows_cons ⟨ew132_3632_48, lb132_3632_4⟩ ?_
    refine rows_cons ⟨ew196_3632_48, (transfer (s:=196) (a:=3632) (t:=148) (u:=3680) perm24 (by decide +kernel) (by decide +kernel) lb148_3680_4)⟩ ?_
    refine rows_cons ⟨ew132_3184_112, (transfer (s:=132) (a:=3184) (t:=132) (u:=1648) perm8 (by decide +kernel) (by decide +kernel) lb132_1648_4)⟩ ?_
    refine rows_cons ⟨ew644_3184_112, (transfer (s:=644) (a:=3184) (t:=400) (u:=4650) perm50 (by decide +kernel) (by decide +kernel) lb400_4650_4)⟩ ?_
    refine rows_cons ⟨ew132_2672_624, (transfer (s:=132) (a:=2672) (t:=132) (u:=1648) perm72 (by decide +kernel) (by decide +kernel) lb132_1648_4)⟩ ?_
    refine rows_cons ⟨ew1156_2672_624, (transfer (s:=1156) (a:=2672) (t:=400) (u:=4650) perm6 (by decide +kernel) (by decide +kernel) lb400_4650_4)⟩ ?_
    refine rows_cons ⟨ew132_1648_1648, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew2180_1648_1648, (zero_bound _ _)⟩ ?_
    exact rows_nil _ _
  · unfold rs; decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb132_3888_6 : CountBound 132 3888 6 := by
  exact fixE 8 false ew132_3888_256 (by decide +kernel) ew132_3632_16 (by decide +kernel) lb132_3632_5

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb132_3920_6 : CountBound 132 3920 6 := by
  exact fixE 8 false ew132_3920_256 (by decide +kernel) ew132_3664_16 (by decide +kernel) (transfer (s:=132) (a:=3664) (t:=132) (u:=3632) perm32 (by decide +kernel) (by decide +kernel) lb132_3632_5)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb132_5984_6 : CountBound 132 5984 6 := by
  exact fixE 8 false ew132_5984_256 (by decide +kernel) ew132_5728_32 (by decide +kernel) (transfer (s:=132) (a:=5728) (t:=132) (u:=2896) perm32 (by decide +kernel) (by decide +kernel) lb132_2896_5)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb132_7472_5 : CountBound 132 7472 5 := by
  exact width_of_mask ew132_7472_7472 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb132_7472_6 : CountBound 132 7472 6 := by
  exact fixE 8 false ew132_7472_256 (by decide +kernel) ew132_7216_16 (by decide +kernel) (transfer (s:=132) (a:=7216) (t:=132) (u:=1888) perm32 (by decide +kernel) (by decide +kernel) lb132_1888_5)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb132_7520_5 : CountBound 132 7520 5 := by
  exact width_of_mask ew132_7520_7520 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb384_1594_5 : CountBound 384 1594 5 := by
  exact width_of_mask ew384_1594_1594 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb384_2618_5 : CountBound 384 2618 5 := by
  exact width_of_mask ew384_2618_2618 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb384_3634_6 : CountBound 384 3634 6 := by
  exact fixE 1 false ew384_3634_2 (by decide +kernel) ew384_3632_16 (by decide +kernel) lb384_3632_5

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb384_3696_6 : CountBound 384 3696 6 := by
  exact fixE 6 false ew384_3696_64 (by decide +kernel) ew384_3632_16 (by decide +kernel) lb384_3632_5

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb384_5682_6 : CountBound 384 5682 6 := by
  exact fixE 1 false ew384_5682_2 (by decide +kernel) ew384_5680_16 (by decide +kernel) lb384_5680_5

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_935_7 : CountBound 0 935 7 := by
  exact fixE 0 false ew0_935_1 (by decide +kernel) ew0_934_2 (by decide +kernel) (transfer (s:=0) (a:=934) (t:=0) (u:=910) perm149 (by decide +kernel) (by decide +kernel) lb0_910_6)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_935_8 : CountBound 0 935 8 := by
  let rs : List Row := [⟨0,false,2,6⟩, ⟨0,true,928,0⟩, ⟨1,false,1,6⟩, ⟨1,true,901,0⟩, ⟨2,false,259,5⟩, ⟨2,true,1,5⟩, ⟨5,false,519,5⟩, ⟨5,true,7,5⟩, ⟨7,false,39,5⟩, ⟨7,true,37,5⟩, ⟨8,false,163,5⟩, ⟨8,true,165,5⟩, ⟨9,false,391,5⟩, ⟨9,true,421,5⟩]
  apply rule_tables (rs:=rs) ?_ (by decide +kernel) ew0_935_935 ?_
  · unfold rs
    refine rows_cons ⟨ew0_934_2, (transfer (s:=0) (a:=934) (t:=0) (u:=910) perm149 (by decide +kernel) (by decide +kernel) lb0_910_6)⟩ ?_
    refine rows_cons ⟨ew1_934_928, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_933_1, (transfer (s:=0) (a:=933) (t:=0) (u:=910) perm46 (by decide +kernel) (by decide +kernel) lb0_910_6)⟩ ?_
    refine rows_cons ⟨ew2_933_901, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_931_259, (transfer (s:=0) (a:=931) (t:=0) (u:=903) perm26 (by decide +kernel) (by decide +kernel) lb0_903_5)⟩ ?_
    refine rows_cons ⟨ew4_931_1, (transfer (s:=4) (a:=931) (t:=1) (u:=2770) perm44 (by decide +kernel) (by decide +kernel) lb1_2770_5)⟩ ?_
    refine rows_cons ⟨ew0_903_519, lb0_903_5⟩ ?_
    refine rows_cons ⟨ew32_903_7, (transfer (s:=32) (a:=903) (t:=1) (u:=2770) perm151 (by decide +kernel) (by decide +kernel) lb1_2770_5)⟩ ?_
    refine rows_cons ⟨ew0_807_39, (transfer (s:=0) (a:=807) (t:=0) (u:=462) perm29 (by decide +kernel) (by decide +kernel) lb0_462_5)⟩ ?_
    refine rows_cons ⟨ew128_807_37, lb128_807_5⟩ ?_
    refine rows_cons ⟨ew0_679_163, (transfer (s:=0) (a:=679) (t:=0) (u:=413) perm50 (by decide +kernel) (by decide +kernel) lb0_413_5)⟩ ?_
    refine rows_cons ⟨ew256_679_165, (transfer (s:=256) (a:=679) (t:=128) (u:=846) perm46 (by decide +kernel) (by decide +kernel) lb128_846_5)⟩ ?_
    refine rows_cons ⟨ew0_423_391, (transfer (s:=0) (a:=423) (t:=0) (u:=413) perm5 (by decide +kernel) (by decide +kernel) lb0_413_5)⟩ ?_
    refine rows_cons ⟨ew512_423_421, (transfer (s:=512) (a:=423) (t:=128) (u:=846) perm149 (by decide +kernel) (by decide +kernel) lb128_846_5)⟩ ?_
    exact rows_nil _ _
  · unfold rs; decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_1431_8 : CountBound 0 1431 8 := by
  let rs : List Row := [⟨0,false,2,5⟩, ⟨0,true,1408,0⟩, ⟨1,false,129,5⟩, ⟨1,true,1,6⟩, ⟨2,false,259,5⟩, ⟨2,true,3,6⟩, ⟨4,false,1031,5⟩, ⟨4,true,7,6⟩, ⟨7,false,21,5⟩, ⟨7,true,23,5⟩, ⟨8,false,147,5⟩, ⟨8,true,151,5⟩, ⟨10,false,391,5⟩, ⟨10,true,407,5⟩]
  apply rule_tables (rs:=rs) ?_ (by decide +kernel) ew0_1431_1431 ?_
  · unfold rs
    refine rows_cons ⟨ew0_1430_2, lb0_1430_5⟩ ?_
    refine rows_cons ⟨ew1_1430_1408, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_1429_129, (transfer (s:=0) (a:=1429) (t:=0) (u:=1415) perm12 (by decide +kernel) (by decide +kernel) lb0_1415_5)⟩ ?_
    refine rows_cons ⟨ew2_1429_1, (transfer (s:=2) (a:=1429) (t:=1) (u:=2890) perm144 (by decide +kernel) (by decide +kernel) lb1_2890_6)⟩ ?_
    refine rows_cons ⟨ew0_1427_259, (transfer (s:=0) (a:=1427) (t:=0) (u:=1415) perm1 (by decide +kernel) (by decide +kernel) lb0_1415_5)⟩ ?_
    refine rows_cons ⟨ew4_1427_3, (transfer (s:=4) (a:=1427) (t:=1) (u:=2890) perm148 (by decide +kernel) (by decide +kernel) lb1_2890_6)⟩ ?_
    refine rows_cons ⟨ew0_1415_1031, lb0_1415_5⟩ ?_
    refine rows_cons ⟨ew16_1415_7, (transfer (s:=16) (a:=1415) (t:=1) (u:=2890) perm150 (by decide +kernel) (by decide +kernel) lb1_2890_6)⟩ ?_
    refine rows_cons ⟨ew0_1303_21, (transfer (s:=0) (a:=1303) (t:=0) (u:=407) perm12 (by decide +kernel) (by decide +kernel) lb0_407_5)⟩ ?_
    refine rows_cons ⟨ew128_1303_23, lb128_1303_5⟩ ?_
    refine rows_cons ⟨ew0_1175_147, (transfer (s:=0) (a:=1175) (t:=0) (u:=407) perm1 (by decide +kernel) (by decide +kernel) lb0_407_5)⟩ ?_
    refine rows_cons ⟨ew256_1175_151, (transfer (s:=256) (a:=1175) (t:=128) (u:=1303) perm4 (by decide +kernel) (by decide +kernel) lb128_1303_5)⟩ ?_
    refine rows_cons ⟨ew0_407_391, lb0_407_5⟩ ?_
    refine rows_cons ⟨ew1024_407_407, (transfer (s:=1024) (a:=407) (t:=128) (u:=1303) perm6 (by decide +kernel) (by decide +kernel) lb128_1303_5)⟩ ?_
    exact rows_nil _ _
  · unfold rs; decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_1437_7 : CountBound 0 1437 7 := by
  exact fixE 2 false ew0_1437_4 (by decide +kernel) ew0_1433_1 (by decide +kernel) (transfer (s:=0) (a:=1433) (t:=0) (u:=1415) perm10 (by decide +kernel) (by decide +kernel) lb0_1415_6)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_1931_7 : CountBound 0 1931 7 := by
  exact fixE 3 false ew0_1931_8 (by decide +kernel) ew0_1923_1 (by decide +kernel) lb0_1923_6

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_2018_8 : CountBound 0 2018 8 := by
  let rs : List Row := [⟨1,false,1824,5⟩, ⟨1,true,32,5⟩, ⟨5,false,898,5⟩, ⟨5,true,2,5⟩, ⟨6,false,1698,5⟩, ⟨6,true,34,5⟩, ⟨7,false,2,5⟩, ⟨7,true,98,6⟩, ⟨8,false,194,5⟩, ⟨8,true,226,6⟩, ⟨9,false,386,5⟩, ⟨9,true,98,0⟩, ⟨10,false,930,5⟩, ⟨10,true,482,6⟩]
  apply rule_tables (rs:=rs) ?_ (by decide +kernel) ew0_2018_2018 ?_
  · unfold rs
    refine rows_cons ⟨ew0_2016_1824, (transfer (s:=0) (a:=2016) (t:=0) (u:=1954) perm21 (by decide +kernel) (by decide +kernel) lb0_1954_5)⟩ ?_
    refine rows_cons ⟨ew2_2016_32, (transfer (s:=2) (a:=2016) (t:=1) (u:=2954) perm146 (by decide +kernel) (by decide +kernel) lb1_2954_5)⟩ ?_
    refine rows_cons ⟨ew0_1986_898, (transfer (s:=0) (a:=1986) (t:=0) (u:=1954) perm1 (by decide +kernel) (by decide +kernel) lb0_1954_5)⟩ ?_
    refine rows_cons ⟨ew32_1986_2, (transfer (s:=32) (a:=1986) (t:=1) (u:=2954) perm151 (by decide +kernel) (by decide +kernel) lb1_2954_5)⟩ ?_
    refine rows_cons ⟨ew0_1954_1698, lb0_1954_5⟩ ?_
    refine rows_cons ⟨ew64_1954_34, (transfer (s:=64) (a:=1954) (t:=1) (u:=2954) perm149 (by decide +kernel) (by decide +kernel) lb1_2954_5)⟩ ?_
    refine rows_cons ⟨ew0_1890_2, (transfer (s:=0) (a:=1890) (t:=0) (u:=907) perm158 (by decide +kernel) (by decide +kernel) lb0_907_5)⟩ ?_
    refine rows_cons ⟨ew128_1890_98, lb128_1890_6⟩ ?_
    refine rows_cons ⟨ew0_1762_194, (transfer (s:=0) (a:=1762) (t:=0) (u:=907) perm146 (by decide +kernel) (by decide +kernel) lb0_907_5)⟩ ?_
    refine rows_cons ⟨ew256_1762_226, (transfer (s:=256) (a:=1762) (t:=128) (u:=1890) perm18 (by decide +kernel) (by decide +kernel) lb128_1890_6)⟩ ?_
    refine rows_cons ⟨ew0_1506_386, (transfer (s:=0) (a:=1506) (t:=0) (u:=1430) perm2 (by decide +kernel) (by decide +kernel) lb0_1430_5)⟩ ?_
    refine rows_cons ⟨ew512_1506_98, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_994_930, (transfer (s:=0) (a:=994) (t:=0) (u:=907) perm147 (by decide +kernel) (by decide +kernel) lb0_907_5)⟩ ?_
    refine rows_cons ⟨ew1024_994_482, (transfer (s:=1024) (a:=994) (t:=128) (u:=1890) perm17 (by decide +kernel) (by decide +kernel) lb128_1890_6)⟩ ?_
    exact rows_nil _ _
  · unfold rs; decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_3723_7 : CountBound 0 3723 7 := by
  exact fixE 9 false ew0_3723_512 (by decide +kernel) ew0_3211_1 (by decide +kernel) (transfer (s:=0) (a:=3211) (t:=0) (u:=907) perm9 (by decide +kernel) (by decide +kernel) lb0_907_6)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_3723_8 : CountBound 0 3723 8 := by
  let rs : List Row := [⟨0,false,2690,5⟩, ⟨0,true,2,5⟩, ⟨1,false,3201,5⟩, ⟨1,true,1,5⟩, ⟨3,false,1667,5⟩, ⟨3,true,3,5⟩, ⟨7,false,1,5⟩, ⟨7,true,11,0⟩, ⟨9,false,131,5⟩, ⟨9,true,11,6⟩, ⟨10,false,641,5⟩, ⟨10,true,523,6⟩, ⟨11,false,1673,5⟩, ⟨11,true,1547,6⟩]
  apply rule_tables (rs:=rs) ?_ (by decide +kernel) ew0_3723_3723 ?_
  · unfold rs
    refine rows_cons ⟨ew0_3722_2690, (transfer (s:=0) (a:=3722) (t:=0) (u:=3715) perm72 (by decide +kernel) (by decide +kernel) lb0_3715_5)⟩ ?_
    refine rows_cons ⟨ew1_3722_2, lb1_3722_5⟩ ?_
    refine rows_cons ⟨ew0_3721_3201, (transfer (s:=0) (a:=3721) (t:=0) (u:=3715) perm8 (by decide +kernel) (by decide +kernel) lb0_3715_5)⟩ ?_
    refine rows_cons ⟨ew2_3721_1, (transfer (s:=2) (a:=3721) (t:=1) (u:=3722) perm24 (by decide +kernel) (by decide +kernel) lb1_3722_5)⟩ ?_
    refine rows_cons ⟨ew0_3715_1667, lb0_3715_5⟩ ?_
    refine rows_cons ⟨ew8_3715_3, (transfer (s:=8) (a:=3715) (t:=1) (u:=3722) perm32 (by decide +kernel) (by decide +kernel) lb1_3722_5)⟩ ?_
    refine rows_cons ⟨ew0_3595_1, (transfer (s:=0) (a:=3595) (t:=0) (u:=940) perm58 (by decide +kernel) (by decide +kernel) lb0_940_5)⟩ ?_
    refine rows_cons ⟨ew128_3595_11, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_3211_131, (transfer (s:=0) (a:=3211) (t:=0) (u:=907) perm9 (by decide +kernel) (by decide +kernel) lb0_907_5)⟩ ?_
    refine rows_cons ⟨ew512_3211_11, (transfer (s:=512) (a:=3211) (t:=128) (u:=3633) perm97 (by decide +kernel) (by decide +kernel) lb128_3633_6)⟩ ?_
    refine rows_cons ⟨ew0_2699_641, (transfer (s:=0) (a:=2699) (t:=0) (u:=907) perm73 (by decide +kernel) (by decide +kernel) lb0_907_5)⟩ ?_
    refine rows_cons ⟨ew1024_2699_523, (transfer (s:=1024) (a:=2699) (t:=128) (u:=3633) perm13 (by decide +kernel) (by decide +kernel) lb128_3633_6)⟩ ?_
    refine rows_cons ⟨ew0_1675_1673, (transfer (s:=0) (a:=1675) (t:=0) (u:=907) perm1 (by decide +kernel) (by decide +kernel) lb0_907_5)⟩ ?_
    refine rows_cons ⟨ew2048_1675_1547, (transfer (s:=2048) (a:=1675) (t:=128) (u:=3633) perm113 (by decide +kernel) (by decide +kernel) lb128_3633_6)⟩ ?_
    exact rows_nil _ _
  · unfold rs; decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_3731_7 : CountBound 0 3731 7 := by
  exact fixE 1 true ew0_3731_2 (by decide +kernel) ew2_3729_1 (by decide +kernel) (transfer (s:=2) (a:=3729) (t:=1) (u:=3778) perm24 (by decide +kernel) (by decide +kernel) lb1_3778_6)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_3731_8 : CountBound 0 3731 8 := by
  let rs : List Row := [⟨0,false,2,5⟩, ⟨0,true,2,5⟩, ⟨1,false,3201,5⟩, ⟨1,true,1,5⟩, ⟨4,false,1667,5⟩, ⟨4,true,3,5⟩, ⟨7,false,1,6⟩, ⟨7,true,2067,0⟩, ⟨9,false,131,5⟩, ⟨9,true,147,5⟩, ⟨10,false,641,6⟩, ⟨10,true,659,0⟩, ⟨11,false,1681,5⟩, ⟨11,true,1555,5⟩]
  apply rule_tables (rs:=rs) ?_ (by decide +kernel) ew0_3731_3731 ?_
  · unfold rs
    refine rows_cons ⟨ew0_3730_2, lb0_3730_5⟩ ?_
    refine rows_cons ⟨ew1_3730_2, lb1_3730_5⟩ ?_
    refine rows_cons ⟨ew0_3729_3201, (transfer (s:=0) (a:=3729) (t:=0) (u:=3715) perm13 (by decide +kernel) (by decide +kernel) lb0_3715_5)⟩ ?_
    refine rows_cons ⟨ew2_3729_1, (transfer (s:=2) (a:=3729) (t:=1) (u:=3778) perm24 (by decide +kernel) (by decide +kernel) lb1_3778_5)⟩ ?_
    refine rows_cons ⟨ew0_3715_1667, lb0_3715_5⟩ ?_
    refine rows_cons ⟨ew16_3715_3, (transfer (s:=16) (a:=3715) (t:=1) (u:=3778) perm45 (by decide +kernel) (by decide +kernel) lb1_3778_5)⟩ ?_
    refine rows_cons ⟨ew0_3603_1, (transfer (s:=0) (a:=3603) (t:=0) (u:=910) perm82 (by decide +kernel) (by decide +kernel) lb0_910_6)⟩ ?_
    refine rows_cons ⟨ew128_3603_2067, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_3219_131, (transfer (s:=0) (a:=3219) (t:=0) (u:=903) perm6 (by decide +kernel) (by decide +kernel) lb0_903_5)⟩ ?_
    refine rows_cons ⟨ew512_3219_147, (transfer (s:=512) (a:=3219) (t:=128) (u:=3634) perm125 (by decide +kernel) (by decide +kernel) lb128_3634_5)⟩ ?_
    refine rows_cons ⟨ew0_2707_641, (transfer (s:=0) (a:=2707) (t:=0) (u:=910) perm77 (by decide +kernel) (by decide +kernel) lb0_910_6)⟩ ?_
    refine rows_cons ⟨ew1024_2707_659, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_1683_1681, (transfer (s:=0) (a:=1683) (t:=0) (u:=903) perm1 (by decide +kernel) (by decide +kernel) lb0_903_5)⟩ ?_
    refine rows_cons ⟨ew2048_1683_1555, (transfer (s:=2048) (a:=1683) (t:=128) (u:=3634) perm137 (by decide +kernel) (by decide +kernel) lb128_3634_5)⟩ ?_
    exact rows_nil _ _
  · unfold rs; decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_4033_7 : CountBound 0 4033 7 := by
  exact fixE 7 false ew0_4033_128 (by decide +kernel) ew0_3905_1 (by decide +kernel) (transfer (s:=0) (a:=3905) (t:=0) (u:=1923) perm29 (by decide +kernel) (by decide +kernel) lb0_1923_6)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_3794_7 : CountBound 1 3794 7 := by
  exact fixE 1 false ew1_3794_2 (by decide +kernel) ew1_3792_16 (by decide +kernel) (transfer (s:=1) (a:=3792) (t:=1) (u:=3778) perm13 (by decide +kernel) (by decide +kernel) lb1_3778_6)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_6702_7 : CountBound 1 6702 7 := by
  exact fixE 1 false ew1_6702_2 (by decide +kernel) ew1_6700_4 (by decide +kernel) lb1_6700_6

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_6714_8 : CountBound 1 6714 8 := by
  let rs : List Row := [⟨1,false,520,5⟩, ⟨1,true,40,5⟩, ⟨3,false,18,6⟩, ⟨3,true,6658,0⟩, ⟨4,false,2050,5⟩, ⟨4,true,10,5⟩, ⟨5,false,26,6⟩, ⟨5,true,6680,0⟩, ⟨9,false,4152,5⟩, ⟨9,true,18,5⟩, ⟨11,false,4650,5⟩, ⟨11,true,530,5⟩, ⟨12,false,58,5⟩, ⟨12,true,2578,5⟩]
  apply rule_tables (rs:=rs) ?_ (by decide +kernel) ew1_6714_6714 ?_
  · unfold rs
    refine rows_cons ⟨ew1_6712_520, (transfer (s:=1) (a:=6712) (t:=1) (u:=6698) perm13 (by decide +kernel) (by decide +kernel) lb1_6698_5)⟩ ?_
    refine rows_cons ⟨ew3_6712_40, (transfer (s:=3) (a:=6712) (t:=3) (u:=6428) perm26 (by decide +kernel) (by decide +kernel) lb3_6428_5)⟩ ?_
    refine rows_cons ⟨ew1_6706_18, (transfer (s:=1) (a:=6706) (t:=1) (u:=6670) perm6 (by decide +kernel) (by decide +kernel) lb1_6670_6)⟩ ?_
    refine rows_cons ⟨ew9_6706_6658, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew1_6698_2050, lb1_6698_5⟩ ?_
    refine rows_cons ⟨ew17_6698_10, (transfer (s:=17) (a:=6698) (t:=3) (u:=6428) perm38 (by decide +kernel) (by decide +kernel) lb3_6428_5)⟩ ?_
    refine rows_cons ⟨ew1_6682_26, (transfer (s:=1) (a:=6682) (t:=1) (u:=6670) perm1 (by decide +kernel) (by decide +kernel) lb1_6670_6)⟩ ?_
    refine rows_cons ⟨ew33_6682_6680, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew1_6202_4152, (transfer (s:=1) (a:=6202) (t:=1) (u:=2638) perm6 (by decide +kernel) (by decide +kernel) lb1_2638_5)⟩ ?_
    refine rows_cons ⟨ew513_6202_18, (transfer (s:=513) (a:=6202) (t:=132) (u:=1594) perm59 (by decide +kernel) (by decide +kernel) lb132_1594_5)⟩ ?_
    refine rows_cons ⟨ew1_4666_4650, (transfer (s:=1) (a:=4666) (t:=1) (u:=2638) perm1 (by decide +kernel) (by decide +kernel) lb1_2638_5)⟩ ?_
    refine rows_cons ⟨ew2049_4666_530, (transfer (s:=2049) (a:=4666) (t:=132) (u:=1594) perm63 (by decide +kernel) (by decide +kernel) lb132_1594_5)⟩ ?_
    refine rows_cons ⟨ew1_2618_58, lb1_2618_5⟩ ?_
    refine rows_cons ⟨ew4097_2618_2578, (transfer (s:=4097) (a:=2618) (t:=132) (u:=1619) perm61 (by decide +kernel) (by decide +kernel) lb132_1619_5)⟩ ?_
    exact rows_nil _ _
  · unfold rs; decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_6762_7 : CountBound 1 6762 7 := by
  exact fixE 1 false ew1_6762_2 (by decide +kernel) ew1_6760_8 (by decide +kernel) lb1_6760_6

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_6762_8 : CountBound 1 6762 8 := by
  exact fixE 1 false ew1_6762_2 (by decide +kernel) ew1_6760_8 (by decide +kernel) lb1_6760_7

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_6836_7 : CountBound 1 6836 7 := by
  exact fixE 7 false ew1_6836_128 (by decide +kernel) ew1_6708_4 (by decide +kernel) (transfer (s:=1) (a:=6708) (t:=1) (u:=6670) perm13 (by decide +kernel) (by decide +kernel) lb1_6670_6)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_6840_7 : CountBound 1 6840 7 := by
  exact fixE 4 false ew1_6840_16 (by decide +kernel) ew1_6824_8 (by decide +kernel) lb1_6824_6

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_6884_7 : CountBound 1 6884 7 := by
  exact fixE 2 false ew1_6884_4 (by decide +kernel) ew1_6880_32 (by decide +kernel) lb1_6880_6

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_6888_7 : CountBound 1 6888 7 := by
  exact fixE 3 false ew1_6888_8 (by decide +kernel) ew1_6880_32 (by decide +kernel) lb1_6880_6

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_6888_8 : CountBound 1 6888 8 := by
  exact fixE 7 false ew1_6888_128 (by decide +kernel) ew1_6760_8 (by decide +kernel) lb1_6760_7

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_7080_7 : CountBound 1 7080 7 := by
  exact fixE 7 false ew1_7080_128 (by decide +kernel) ew1_6952_8 (by decide +kernel) (transfer (s:=1) (a:=6952) (t:=1) (u:=6880) perm4 (by decide +kernel) (by decide +kernel) lb1_6880_6)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_14862_7 : CountBound 1 14862 7 := by
  exact fixE 9 false ew1_14862_512 (by decide +kernel) ew1_14350_2 (by decide +kernel) (transfer (s:=1) (a:=14350) (t:=1) (u:=6698) perm2 (by decide +kernel) (by decide +kernel) lb1_6698_6)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_14870_7 : CountBound 1 14870 7 := by
  exact fixE 9 false ew1_14870_512 (by decide +kernel) ew1_14358_2 (by decide +kernel) (transfer (s:=1) (a:=14358) (t:=1) (u:=6700) perm5 (by decide +kernel) (by decide +kernel) lb1_6700_6)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_14870_8 : CountBound 1 14870 8 := by
  let rs : List Row := [⟨1,false,14340,5⟩, ⟨1,true,4,5⟩, ⟨2,false,10754,5⟩, ⟨2,true,2,5⟩, ⟨4,false,12806,5⟩, ⟨4,true,6,5⟩, ⟨9,false,2,5⟩, ⟨9,true,22,6⟩, ⟨11,false,530,5⟩, ⟨11,true,534,6⟩, ⟨12,false,2566,5⟩, ⟨12,true,2582,6⟩, ⟨13,false,6658,5⟩, ⟨13,true,22,0⟩]
  apply rule_tables (rs:=rs) ?_ (by decide +kernel) ew1_14870_14870 ?_
  · unfold rs
    refine rows_cons ⟨ew1_14868_14340, (transfer (s:=1) (a:=14868) (t:=1) (u:=14854) perm12 (by decide +kernel) (by decide +kernel) lb1_14854_5)⟩ ?_
    refine rows_cons ⟨ew3_14868_4, (transfer (s:=3) (a:=14868) (t:=3) (u:=7472) perm25 (by decide +kernel) (by decide +kernel) lb3_7472_5)⟩ ?_
    refine rows_cons ⟨ew1_14866_10754, (transfer (s:=1) (a:=14866) (t:=1) (u:=14854) perm1 (by decide +kernel) (by decide +kernel) lb1_14854_5)⟩ ?_
    refine rows_cons ⟨ew5_14866_2, (transfer (s:=5) (a:=14866) (t:=3) (u:=7472) perm36 (by decide +kernel) (by decide +kernel) lb3_7472_5)⟩ ?_
    refine rows_cons ⟨ew1_14854_12806, lb1_14854_5⟩ ?_
    refine rows_cons ⟨ew17_14854_6, (transfer (s:=17) (a:=14854) (t:=3) (u:=7472) perm38 (by decide +kernel) (by decide +kernel) lb3_7472_5)⟩ ?_
    refine rows_cons ⟨ew1_14358_2, (transfer (s:=1) (a:=14358) (t:=1) (u:=6700) perm5 (by decide +kernel) (by decide +kernel) lb1_6700_5)⟩ ?_
    refine rows_cons ⟨ew513_14358_22, (transfer (s:=513) (a:=14358) (t:=132) (u:=3633) perm50 (by decide +kernel) (by decide +kernel) lb132_3633_6)⟩ ?_
    refine rows_cons ⟨ew1_12822_530, (transfer (s:=1) (a:=12822) (t:=1) (u:=6700) perm10 (by decide +kernel) (by decide +kernel) lb1_6700_5)⟩ ?_
    refine rows_cons ⟨ew2049_12822_534, (transfer (s:=2049) (a:=12822) (t:=132) (u:=3633) perm62 (by decide +kernel) (by decide +kernel) lb132_3633_6)⟩ ?_
    refine rows_cons ⟨ew1_10774_2566, (transfer (s:=1) (a:=10774) (t:=1) (u:=6700) perm8 (by decide +kernel) (by decide +kernel) lb1_6700_5)⟩ ?_
    refine rows_cons ⟨ew4097_10774_2582, (transfer (s:=4097) (a:=10774) (t:=132) (u:=3633) perm60 (by decide +kernel) (by decide +kernel) lb132_3633_6)⟩ ?_
    refine rows_cons ⟨ew1_6678_6658, lb1_6678_5⟩ ?_
    refine rows_cons ⟨ew8193_6678_22, (zero_bound _ _)⟩ ?_
    exact rows_nil _ _
  · unfold rs; decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_1852_7 : CountBound 128 1852 7 := by
  exact fixE 2 true ew128_1852_4 (by decide +kernel) ew132_1848_8 (by decide +kernel) lb132_1848_6

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_1900_7 : CountBound 128 1900 7 := by
  exact fixE 2 false ew128_1900_4 (by decide +kernel) ew128_1896_8 (by decide +kernel) lb128_1896_6

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_1908_7 : CountBound 128 1908 7 := by
  exact fixE 2 false ew128_1908_4 (by decide +kernel) ew128_1904_16 (by decide +kernel) (transfer (s:=128) (a:=1904) (t:=128) (u:=1892) perm1 (by decide +kernel) (by decide +kernel) lb128_1892_6)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_1908_8 : CountBound 128 1908 8 := by
  let rs : List Row := [⟨2,false,272,5⟩, ⟨2,true,16,6⟩, ⟨4,false,1028,5⟩, ⟨4,true,4,6⟩, ⟨5,false,20,6⟩, ⟨5,true,1796,0⟩, ⟨6,false,52,5⟩, ⟨6,true,1840,0⟩, ⟨8,false,624,5⟩, ⟨8,true,20,5⟩, ⟨9,false,116,5⟩, ⟨9,true,276,5⟩, ⟨10,false,868,5⟩, ⟨10,true,788,5⟩]
  apply rule_tables (rs:=rs) ?_ (by decide +kernel) ew128_1908_1908 ?_
  · unfold rs
    refine rows_cons ⟨ew128_1904_272, (transfer (s:=128) (a:=1904) (t:=128) (u:=1892) perm1 (by decide +kernel) (by decide +kernel) lb128_1892_5)⟩ ?_
    refine rows_cons ⟨ew132_1904_16, lb132_1904_6⟩ ?_
    refine rows_cons ⟨ew128_1892_1028, lb128_1892_5⟩ ?_
    refine rows_cons ⟨ew144_1892_4, (transfer (s:=144) (a:=1892) (t:=132) (u:=1904) perm1 (by decide +kernel) (by decide +kernel) lb132_1904_6)⟩ ?_
    refine rows_cons ⟨ew128_1876_20, (transfer (s:=128) (a:=1876) (t:=128) (u:=1844) perm1 (by decide +kernel) (by decide +kernel) lb128_1844_6)⟩ ?_
    refine rows_cons ⟨ew160_1876_1796, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew128_1844_52, lb128_1844_5⟩ ?_
    refine rows_cons ⟨ew192_1844_1840, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew128_1652_624, (transfer (s:=128) (a:=1652) (t:=128) (u:=884) perm1 (by decide +kernel) (by decide +kernel) lb128_884_5)⟩ ?_
    refine rows_cons ⟨ew384_1652_20, (transfer (s:=384) (a:=1652) (t:=384) (u:=1594) perm21 (by decide +kernel) (by decide +kernel) lb384_1594_5)⟩ ?_
    refine rows_cons ⟨ew128_1396_116, lb128_1396_5⟩ ?_
    refine rows_cons ⟨ew640_1396_276, (transfer (s:=640) (a:=1396) (t:=384) (u:=2618) perm146 (by decide +kernel) (by decide +kernel) lb384_2618_5)⟩ ?_
    refine rows_cons ⟨ew128_884_868, lb128_884_5⟩ ?_
    refine rows_cons ⟨ew1152_884_788, (transfer (s:=1152) (a:=884) (t:=384) (u:=1594) perm22 (by decide +kernel) (by decide +kernel) lb384_1594_5)⟩ ?_
    exact rows_nil _ _
  · unfold rs; decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_2932_7 : CountBound 128 2932 7 := by
  exact fixE 2 false ew128_2932_4 (by decide +kernel) ew128_2928_16 (by decide +kernel) (transfer (s:=128) (a:=2928) (t:=128) (u:=2900) perm26 (by decide +kernel) (by decide +kernel) lb128_2900_6)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_3642_7 : CountBound 128 3642 7 := by
  exact fixE 1 false ew128_3642_2 (by decide +kernel) ew128_3640_8 (by decide +kernel) (transfer (s:=128) (a:=3640) (t:=128) (u:=3634) perm8 (by decide +kernel) (by decide +kernel) lb128_3634_6)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_3697_8 : CountBound 128 3697 8 := by
  exact fixE 0 false ew128_3697_1 (by decide +kernel) ew128_3696_16 (by decide +kernel) lb128_3696_7

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_3700_7 : CountBound 128 3700 7 := by
  exact fix_one 2 false (by decide +kernel) lb128_3696_7

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_3892_7 : CountBound 128 3892 7 := by
  exact fixE 2 true ew128_3892_4 (by decide +kernel) ew132_3888_16 (by decide +kernel) lb132_3888_6

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_3924_7 : CountBound 128 3924 7 := by
  exact fixE 2 false ew128_3924_4 (by decide +kernel) ew128_3920_16 (by decide +kernel) lb128_3920_6

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_3952_7 : CountBound 128 3952 7 := by
  exact fixE 4 false ew128_3952_16 (by decide +kernel) ew128_3936_32 (by decide +kernel) (transfer (s:=128) (a:=3936) (t:=128) (u:=3920) perm8 (by decide +kernel) (by decide +kernel) lb128_3920_6)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_3952_8 : CountBound 128 3952 8 := by
  exact fixE 8 false ew128_3952_256 (by decide +kernel) ew128_3696_16 (by decide +kernel) lb128_3696_7

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_7476_7 : CountBound 128 7476 7 := by
  exact fixE 2 true ew128_7476_4 (by decide +kernel) ew132_7472_16 (by decide +kernel) lb132_7472_6

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_7476_8 : CountBound 128 7476 8 := by
  let rs : List Row := [⟨2,false,7216,5⟩, ⟨2,true,16,5⟩, ⟨4,false,5412,5⟩, ⟨4,true,4,5⟩, ⟨5,false,4,5⟩, ⟨5,true,20,5⟩, ⟨8,false,36,5⟩, ⟨8,true,52,6⟩, ⟨10,false,292,6⟩, ⟨10,true,308,0⟩, ⟨11,false,1332,5⟩, ⟨11,true,308,6⟩, ⟨12,false,3364,5⟩, ⟨12,true,3124,0⟩]
  apply rule_tables (rs:=rs) ?_ (by decide +kernel) ew128_7476_7476 ?_
  · unfold rs
    refine rows_cons ⟨ew128_7472_7216, (transfer (s:=128) (a:=7472) (t:=128) (u:=7460) perm77 (by decide +kernel) (by decide +kernel) lb128_7460_5)⟩ ?_
    refine rows_cons ⟨ew132_7472_16, lb132_7472_5⟩ ?_
    refine rows_cons ⟨ew128_7460_5412, lb128_7460_5⟩ ?_
    refine rows_cons ⟨ew144_7460_4, (transfer (s:=144) (a:=7460) (t:=132) (u:=7472) perm77 (by decide +kernel) (by decide +kernel) lb132_7472_5)⟩ ?_
    refine rows_cons ⟨ew128_7444_4, lb128_7444_5⟩ ?_
    refine rows_cons ⟨ew160_7444_20, (transfer (s:=160) (a:=7444) (t:=132) (u:=7520) perm2 (by decide +kernel) (by decide +kernel) lb132_7520_5)⟩ ?_
    refine rows_cons ⟨ew128_7220_36, (transfer (s:=128) (a:=7220) (t:=128) (u:=1892) perm32 (by decide +kernel) (by decide +kernel) lb128_1892_5)⟩ ?_
    refine rows_cons ⟨ew384_7220_52, (transfer (s:=384) (a:=7220) (t:=384) (u:=3634) perm4 (by decide +kernel) (by decide +kernel) lb384_3634_6)⟩ ?_
    refine rows_cons ⟨ew128_6452_292, (transfer (s:=128) (a:=6452) (t:=128) (u:=1844) perm34 (by decide +kernel) (by decide +kernel) lb128_1844_6)⟩ ?_
    refine rows_cons ⟨ew1152_6452_308, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew128_5428_1332, (transfer (s:=128) (a:=5428) (t:=128) (u:=1892) perm10 (by decide +kernel) (by decide +kernel) lb128_1892_5)⟩ ?_
    refine rows_cons ⟨ew2176_5428_308, (transfer (s:=2176) (a:=5428) (t:=384) (u:=3634) perm154 (by decide +kernel) (by decide +kernel) lb384_3634_6)⟩ ?_
    refine rows_cons ⟨ew128_3380_3364, (transfer (s:=128) (a:=3380) (t:=128) (u:=1844) perm8 (by decide +kernel) (by decide +kernel) lb128_1844_5)⟩ ?_
    refine rows_cons ⟨ew4224_3380_3124, (zero_bound _ _)⟩ ?_
    exact rows_nil _ _
  · unfold rs; decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_8032_7 : CountBound 128 8032 7 := by
  exact fixE 8 false ew128_8032_256 (by decide +kernel) ew128_7776_32 (by decide +kernel) (transfer (s:=128) (a:=7776) (t:=128) (u:=3920) perm32 (by decide +kernel) (by decide +kernel) lb128_3920_6)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb132_3642_7 : CountBound 132 3642 7 := by
  exact fixE 1 false ew132_3642_2 (by decide +kernel) ew132_3640_8 (by decide +kernel) (transfer (s:=132) (a:=3640) (t:=132) (u:=3634) perm8 (by decide +kernel) (by decide +kernel) lb132_3634_6)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb132_3697_7 : CountBound 132 3697 7 := by
  exact fixE 0 false ew132_3697_1 (by decide +kernel) ew132_3696_16 (by decide +kernel) lb132_3696_6

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb132_3697_8 : CountBound 132 3697 8 := by
  exact fixE 0 false ew132_3697_1 (by decide +kernel) ew132_3696_16 (by decide +kernel) lb132_3696_7

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb132_3952_8 : CountBound 132 3952 8 := by
  exact fixE 8 false ew132_3952_256 (by decide +kernel) ew132_3696_16 (by decide +kernel) lb132_3696_7

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb132_6000_7 : CountBound 132 6000 7 := by
  exact fixE 4 false ew132_6000_16 (by decide +kernel) ew132_5984_32 (by decide +kernel) lb132_5984_6

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb132_7536_7 : CountBound 132 7536 7 := by
  exact fixE 5 false ew132_7536_32 (by decide +kernel) ew132_7504_16 (by decide +kernel) (transfer (s:=132) (a:=7504) (t:=132) (u:=7472) perm76 (by decide +kernel) (by decide +kernel) lb132_7472_6)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb132_7984_7 : CountBound 132 7984 7 := by
  exact fixE 8 false ew132_7984_256 (by decide +kernel) ew132_7728_16 (by decide +kernel) (transfer (s:=132) (a:=7728) (t:=132) (u:=3920) perm76 (by decide +kernel) (by decide +kernel) lb132_3920_6)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb384_3642_7 : CountBound 384 3642 7 := by
  exact fixE 1 false ew384_3642_2 (by decide +kernel) ew384_3640_8 (by decide +kernel) (transfer (s:=384) (a:=3640) (t:=384) (u:=3634) perm8 (by decide +kernel) (by decide +kernel) lb384_3634_6)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb384_3700_7 : CountBound 384 3700 7 := by
  exact fixE 2 false ew384_3700_4 (by decide +kernel) ew384_3696_16 (by decide +kernel) lb384_3696_6

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb384_5690_7 : CountBound 384 5690 7 := by
  exact fixE 1 false ew384_5690_2 (by decide +kernel) ew384_5688_8 (by decide +kernel) (transfer (s:=384) (a:=5688) (t:=384) (u:=5682) perm11 (by decide +kernel) (by decide +kernel) lb384_5682_6)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_943_9 : CountBound 0 943 9 := by
  exact fixE 3 false ew0_943_8 (by decide +kernel) ew0_935_1 (by decide +kernel) lb0_935_8

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_951_8 : CountBound 0 951 8 := by
  exact fix_one 4 false (by decide +kernel) lb0_935_8

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_1439_8 : CountBound 0 1439 8 := by
  exact fixE 1 false ew0_1439_2 (by decide +kernel) ew0_1437_1 (by decide +kernel) lb0_1437_7

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_1935_8 : CountBound 0 1935 8 := by
  exact fixE 2 false ew0_1935_4 (by decide +kernel) ew0_1931_1 (by decide +kernel) lb0_1931_7

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_1943_9 : CountBound 0 1943 9 := by
  exact fixE 9 false ew0_1943_512 (by decide +kernel) ew0_1431_1 (by decide +kernel) lb0_1431_8

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_1966_8 : CountBound 0 1966 8 := by
  exact fixE 2 true ew0_1966_4 (by decide +kernel) ew4_1962_2 (by decide +kernel) (transfer (s:=4) (a:=1962) (t:=1) (u:=6884) perm88 (by decide +kernel) (by decide +kernel) lb1_6884_7)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_2022_9 : CountBound 0 2022 9 := by
  exact fixE 2 false ew0_2022_4 (by decide +kernel) ew0_2018_2 (by decide +kernel) lb0_2018_8

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_3770_9 : CountBound 0 3770 9 := by
  exact fixE 1 false ew0_3770_2 (by decide +kernel) ew0_3768_8 (by decide +kernel) (transfer (s:=0) (a:=3768) (t:=0) (u:=3731) perm94 (by decide +kernel) (by decide +kernel) lb0_3731_8)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_3770_10 : CountBound 0 3770 10 := by
  let rs : List Row := [⟨1,false,8,7⟩, ⟨1,true,8,7⟩, ⟨3,false,2,7⟩, ⟨3,true,2,7⟩, ⟨4,false,10,7⟩, ⟨4,true,10,7⟩, ⟨5,false,26,7⟩, ⟨5,true,26,7⟩, ⟨7,false,58,7⟩, ⟨7,true,58,7⟩, ⟨9,false,186,7⟩, ⟨9,true,186,7⟩, ⟨10,false,698,7⟩, ⟨10,true,698,7⟩, ⟨11,false,1722,0⟩, ⟨11,true,1722,0⟩]
  apply rule_tables (rs:=rs) ?_ (by decide +kernel) ew0_3770_3770 ?_
  · unfold rs
    refine rows_cons ⟨ew0_3768_8, (transfer (s:=0) (a:=3768) (t:=0) (u:=3731) perm94 (by decide +kernel) (by decide +kernel) lb0_3731_7)⟩ ?_
    refine rows_cons ⟨ew2_3768_8, (transfer (s:=2) (a:=3768) (t:=1) (u:=3794) perm72 (by decide +kernel) (by decide +kernel) lb1_3794_7)⟩ ?_
    refine rows_cons ⟨ew0_3762_2, (transfer (s:=0) (a:=3762) (t:=0) (u:=3731) perm86 (by decide +kernel) (by decide +kernel) lb0_3731_7)⟩ ?_
    refine rows_cons ⟨ew8_3762_2, (transfer (s:=8) (a:=3762) (t:=1) (u:=3794) perm76 (by decide +kernel) (by decide +kernel) lb1_3794_7)⟩ ?_
    refine rows_cons ⟨ew0_3754_10, (transfer (s:=0) (a:=3754) (t:=0) (u:=3731) perm72 (by decide +kernel) (by decide +kernel) lb0_3731_7)⟩ ?_
    refine rows_cons ⟨ew16_3754_10, (transfer (s:=16) (a:=3754) (t:=1) (u:=3794) perm94 (by decide +kernel) (by decide +kernel) lb1_3794_7)⟩ ?_
    refine rows_cons ⟨ew0_3738_26, (transfer (s:=0) (a:=3738) (t:=0) (u:=3731) perm76 (by decide +kernel) (by decide +kernel) lb0_3731_7)⟩ ?_
    refine rows_cons ⟨ew32_3738_26, (transfer (s:=32) (a:=3738) (t:=1) (u:=3794) perm86 (by decide +kernel) (by decide +kernel) lb1_3794_7)⟩ ?_
    refine rows_cons ⟨ew0_3642_58, (transfer (s:=0) (a:=3642) (t:=0) (u:=935) perm82 (by decide +kernel) (by decide +kernel) lb0_935_7)⟩ ?_
    refine rows_cons ⟨ew128_3642_58, lb128_3642_7⟩ ?_
    refine rows_cons ⟨ew0_3258_186, (transfer (s:=0) (a:=3258) (t:=0) (u:=935) perm154 (by decide +kernel) (by decide +kernel) lb0_935_7)⟩ ?_
    refine rows_cons ⟨ew512_3258_186, (transfer (s:=512) (a:=3258) (t:=128) (u:=3642) perm149 (by decide +kernel) (by decide +kernel) lb128_3642_7)⟩ ?_
    refine rows_cons ⟨ew0_2746_698, (transfer (s:=0) (a:=2746) (t:=0) (u:=935) perm73 (by decide +kernel) (by decide +kernel) lb0_935_7)⟩ ?_
    refine rows_cons ⟨ew1024_2746_698, (transfer (s:=1024) (a:=2746) (t:=128) (u:=3642) perm13 (by decide +kernel) (by decide +kernel) lb128_3642_7)⟩ ?_
    refine rows_cons ⟨ew0_1722_1722, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew2048_1722_1722, (zero_bound _ _)⟩ ?_
    exact rows_nil _ _
  · unfold rs; decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_3979_8 : CountBound 0 3979 8 := by
  exact fixE 8 false ew0_3979_256 (by decide +kernel) ew0_3723_1 (by decide +kernel) lb0_3723_7

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_3979_9 : CountBound 0 3979 9 := by
  exact fixE 8 false ew0_3979_256 (by decide +kernel) ew0_3723_1 (by decide +kernel) lb0_3723_8

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_3987_9 : CountBound 0 3987 9 := by
  exact fixE 8 false ew0_3987_256 (by decide +kernel) ew0_3731_1 (by decide +kernel) lb0_3731_8

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_3994_8 : CountBound 0 3994 8 := by
  exact fix_one 8 false (by decide +kernel) (transfer (s:=0) (a:=3738) (t:=0) (u:=3731) perm76 (by decide +kernel) (by decide +kernel) lb0_3731_8)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_4035_9 : CountBound 0 4035 9 := by
  exact fixE 8 false ew0_4035_256 (by decide +kernel) ew0_3779_1 (by decide +kernel) (transfer (s:=0) (a:=3779) (t:=0) (u:=3731) perm24 (by decide +kernel) (by decide +kernel) lb0_3731_8)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_4037_8 : CountBound 0 4037 8 := by
  exact fixE 2 false ew0_4037_4 (by decide +kernel) ew0_4033_1 (by decide +kernel) lb0_4033_7

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_6718_8 : CountBound 1 6718 8 := by
  exact fixE 1 false ew1_6718_2 (by decide +kernel) ew1_6716_4 (by decide +kernel) (transfer (s:=1) (a:=6716) (t:=1) (u:=6702) perm13 (by decide +kernel) (by decide +kernel) lb1_6702_7)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_6766_8 : CountBound 1 6766 8 := by
  exact fixE 1 false ew1_6766_2 (by decide +kernel) ew1_6764_4 (by decide +kernel) (transfer (s:=1) (a:=6764) (t:=1) (u:=6762) perm4 (by decide +kernel) (by decide +kernel) lb1_6762_7)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_6766_9 : CountBound 1 6766 9 := by
  exact fixE 1 false ew1_6766_2 (by decide +kernel) ew1_6764_4 (by decide +kernel) (transfer (s:=1) (a:=6764) (t:=1) (u:=6762) perm4 (by decide +kernel) (by decide +kernel) lb1_6762_8)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_6842_9 : CountBound 1 6842 9 := by
  exact fixE 7 false ew1_6842_128 (by decide +kernel) ew1_6714_2 (by decide +kernel) lb1_6714_8

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_6844_8 : CountBound 1 6844 8 := by
  exact fixE 2 false ew1_6844_4 (by decide +kernel) ew1_6840_8 (by decide +kernel) lb1_6840_7

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_6892_8 : CountBound 1 6892 8 := by
  exact fixE 2 false ew1_6892_4 (by decide +kernel) ew1_6888_8 (by decide +kernel) lb1_6888_7

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_6900_8 : CountBound 1 6900 8 := by
  exact fixE 2 false ew1_6900_4 (by decide +kernel) ew1_6896_16 (by decide +kernel) (transfer (s:=1) (a:=6896) (t:=1) (u:=6884) perm1 (by decide +kernel) (by decide +kernel) lb1_6884_7)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_6900_9 : CountBound 1 6900 9 := by
  exact fixE 7 false ew1_6900_128 (by decide +kernel) ew1_6772_4 (by decide +kernel) (transfer (s:=1) (a:=6772) (t:=1) (u:=6714) perm4 (by decide +kernel) (by decide +kernel) lb1_6714_8)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_7082_8 : CountBound 1 7082 8 := by
  exact fixE 1 false ew1_7082_2 (by decide +kernel) ew1_7080_8 (by decide +kernel) lb1_7080_7

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_7090_8 : CountBound 1 7090 8 := by
  exact fixE 7 false ew1_7090_128 (by decide +kernel) ew1_6962_2 (by decide +kernel) (transfer (s:=1) (a:=6962) (t:=1) (u:=6836) perm4 (by decide +kernel) (by decide +kernel) lb1_6836_7)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_7096_8 : CountBound 1 7096 8 := by
  exact fixE 4 false ew1_7096_16 (by decide +kernel) ew1_7080_8 (by decide +kernel) lb1_7080_7

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_7144_9 : CountBound 1 7144 9 := by
  exact fixE 7 false ew1_7144_128 (by decide +kernel) ew1_7016_8 (by decide +kernel) (transfer (s:=1) (a:=7016) (t:=1) (u:=6888) perm4 (by decide +kernel) (by decide +kernel) lb1_6888_8)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_14878_9 : CountBound 1 14878 9 := by
  exact fixE 3 false ew1_14878_8 (by decide +kernel) ew1_14870_2 (by decide +kernel) lb1_14870_8

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_14906_8 : CountBound 1 14906 8 := by
  exact fixE 1 false ew1_14906_2 (by decide +kernel) ew1_14904_8 (by decide +kernel) (transfer (s:=1) (a:=14904) (t:=1) (u:=14862) perm22 (by decide +kernel) (by decide +kernel) lb1_14862_7)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_14906_9 : CountBound 1 14906 9 := by
  exact fixE 9 false ew1_14906_512 (by decide +kernel) ew1_14394_2 (by decide +kernel) (transfer (s:=1) (a:=14394) (t:=1) (u:=6714) perm3 (by decide +kernel) (by decide +kernel) lb1_6714_8)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_14998_8 : CountBound 1 14998 8 := by
  exact fixE 7 false ew1_14998_128 (by decide +kernel) ew1_14870_2 (by decide +kernel) lb1_14870_7

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_14998_9 : CountBound 1 14998 9 := by
  exact fixE 7 false ew1_14998_128 (by decide +kernel) ew1_14870_2 (by decide +kernel) lb1_14870_8

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_15028_8 : CountBound 1 15028 8 := by
  exact fixE 7 false ew1_15028_128 (by decide +kernel) ew1_14900_4 (by decide +kernel) (transfer (s:=1) (a:=14900) (t:=1) (u:=14862) perm13 (by decide +kernel) (by decide +kernel) lb1_14862_7)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_1854_8 : CountBound 128 1854 8 := by
  exact fixE 1 false ew128_1854_2 (by decide +kernel) ew128_1852_4 (by decide +kernel) lb128_1852_7

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_1916_8 : CountBound 128 1916 8 := by
  exact fixE 2 false ew128_1916_4 (by decide +kernel) ew128_1912_8 (by decide +kernel) (transfer (s:=128) (a:=1912) (t:=128) (u:=1900) perm1 (by decide +kernel) (by decide +kernel) lb128_1900_7)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_2933_8 : CountBound 128 2933 8 := by
  exact fixE 0 false ew128_2933_1 (by decide +kernel) ew128_2932_4 (by decide +kernel) lb128_2932_7

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_3699_9 : CountBound 128 3699 9 := by
  exact fixE 0 false ew128_3699_1 (by decide +kernel) ew128_3698_2 (by decide +kernel) (transfer (s:=128) (a:=3698) (t:=128) (u:=3697) perm24 (by decide +kernel) (by decide +kernel) lb128_3697_8)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_3956_9 : CountBound 128 3956 9 := by
  exact fixE 2 false ew128_3956_4 (by decide +kernel) ew128_3952_16 (by decide +kernel) lb128_3952_8

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_3956_10 : CountBound 128 3956 10 := by
  let rs : List Row := [⟨2,false,272,7⟩, ⟨2,true,16,8⟩, ⟨4,false,4,7⟩, ⟨4,true,4,7⟩, ⟨5,false,20,7⟩, ⟨5,true,20,7⟩, ⟨6,false,52,7⟩, ⟨6,true,3888,0⟩, ⟨8,false,3696,7⟩, ⟨8,true,52,7⟩, ⟨9,false,116,8⟩, ⟨9,true,1332,0⟩, ⟨10,false,628,7⟩, ⟨10,true,308,7⟩, ⟨11,false,1652,8⟩, ⟨11,true,1844,0⟩]
  apply rule_tables (rs:=rs) ?_ (by decide +kernel) ew128_3956_3956 ?_
  · unfold rs
    refine rows_cons ⟨ew128_3952_272, lb128_3952_7⟩ ?_
    refine rows_cons ⟨ew132_3952_16, lb132_3952_8⟩ ?_
    refine rows_cons ⟨ew128_3940_4, (transfer (s:=128) (a:=3940) (t:=128) (u:=3924) perm8 (by decide +kernel) (by decide +kernel) lb128_3924_7)⟩ ?_
    refine rows_cons ⟨ew144_3940_4, (transfer (s:=144) (a:=3940) (t:=132) (u:=6000) perm1 (by decide +kernel) (by decide +kernel) lb132_6000_7)⟩ ?_
    refine rows_cons ⟨ew128_3924_20, lb128_3924_7⟩ ?_
    refine rows_cons ⟨ew160_3924_20, (transfer (s:=160) (a:=3924) (t:=132) (u:=6000) perm9 (by decide +kernel) (by decide +kernel) lb132_6000_7)⟩ ?_
    refine rows_cons ⟨ew128_3892_52, lb128_3892_7⟩ ?_
    refine rows_cons ⟨ew192_3892_3888, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew128_3700_3696, lb128_3700_7⟩ ?_
    refine rows_cons ⟨ew384_3700_52, lb384_3700_7⟩ ?_
    refine rows_cons ⟨ew128_3444_116, (transfer (s:=128) (a:=3444) (t:=128) (u:=1908) perm8 (by decide +kernel) (by decide +kernel) lb128_1908_8)⟩ ?_
    refine rows_cons ⟨ew640_3444_1332, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew128_2932_628, lb128_2932_7⟩ ?_
    refine rows_cons ⟨ew1152_2932_308, (transfer (s:=1152) (a:=2932) (t:=384) (u:=5690) perm6 (by decide +kernel) (by decide +kernel) lb384_5690_7)⟩ ?_
    refine rows_cons ⟨ew128_1908_1652, lb128_1908_8⟩ ?_
    refine rows_cons ⟨ew2176_1908_1844, (zero_bound _ _)⟩ ?_
    exact rows_nil _ _
  · unfold rs; decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_7478_9 : CountBound 128 7478 9 := by
  exact fixE 1 false ew128_7478_2 (by decide +kernel) ew128_7476_4 (by decide +kernel) lb128_7476_8

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_7540_9 : CountBound 128 7540 9 := by
  exact fixE 2 false ew128_7540_4 (by decide +kernel) ew128_7536_16 (by decide +kernel) (transfer (s:=128) (a:=7536) (t:=128) (u:=7476) perm3 (by decide +kernel) (by decide +kernel) lb128_7476_8)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_7540_10 : CountBound 128 7540 10 := by
  let rs : List Row := [⟨2,false,16,7⟩, ⟨2,true,16,7⟩, ⟨4,false,4,7⟩, ⟨4,true,4,7⟩, ⟨5,false,20,7⟩, ⟨5,true,20,7⟩, ⟨6,false,52,7⟩, ⟨6,true,52,7⟩, ⟨8,false,116,7⟩, ⟨8,true,116,7⟩, ⟨10,false,372,7⟩, ⟨10,true,372,7⟩, ⟨11,false,1396,7⟩, ⟨11,true,1396,7⟩, ⟨12,false,3444,0⟩, ⟨12,true,3444,0⟩]
  apply rule_tables (rs:=rs) ?_ (by decide +kernel) ew128_7540_7540 ?_
  · unfold rs
    refine rows_cons ⟨ew128_7536_16, (transfer (s:=128) (a:=7536) (t:=128) (u:=7476) perm3 (by decide +kernel) (by decide +kernel) lb128_7476_7)⟩ ?_
    refine rows_cons ⟨ew132_7536_16, lb132_7536_7⟩ ?_
    refine rows_cons ⟨ew128_7524_4, (transfer (s:=128) (a:=7524) (t:=128) (u:=7476) perm2 (by decide +kernel) (by decide +kernel) lb128_7476_7)⟩ ?_
    refine rows_cons ⟨ew144_7524_4, (transfer (s:=144) (a:=7524) (t:=132) (u:=7536) perm1 (by decide +kernel) (by decide +kernel) lb132_7536_7)⟩ ?_
    refine rows_cons ⟨ew128_7508_20, (transfer (s:=128) (a:=7508) (t:=128) (u:=7476) perm1 (by decide +kernel) (by decide +kernel) lb128_7476_7)⟩ ?_
    refine rows_cons ⟨ew160_7508_20, (transfer (s:=160) (a:=7508) (t:=132) (u:=7536) perm2 (by decide +kernel) (by decide +kernel) lb132_7536_7)⟩ ?_
    refine rows_cons ⟨ew128_7476_52, lb128_7476_7⟩ ?_
    refine rows_cons ⟨ew192_7476_52, (transfer (s:=192) (a:=7476) (t:=132) (u:=7536) perm3 (by decide +kernel) (by decide +kernel) lb132_7536_7)⟩ ?_
    refine rows_cons ⟨ew128_7284_116, (transfer (s:=128) (a:=7284) (t:=128) (u:=1908) perm32 (by decide +kernel) (by decide +kernel) lb128_1908_7)⟩ ?_
    refine rows_cons ⟨ew384_7284_116, (transfer (s:=384) (a:=7284) (t:=384) (u:=3642) perm4 (by decide +kernel) (by decide +kernel) lb384_3642_7)⟩ ?_
    refine rows_cons ⟨ew128_6516_372, (transfer (s:=128) (a:=6516) (t:=128) (u:=1908) perm34 (by decide +kernel) (by decide +kernel) lb128_1908_7)⟩ ?_
    refine rows_cons ⟨ew1152_6516_372, (transfer (s:=1152) (a:=6516) (t:=384) (u:=3642) perm6 (by decide +kernel) (by decide +kernel) lb384_3642_7)⟩ ?_
    refine rows_cons ⟨ew128_5492_1396, (transfer (s:=128) (a:=5492) (t:=128) (u:=1908) perm10 (by decide +kernel) (by decide +kernel) lb128_1908_7)⟩ ?_
    refine rows_cons ⟨ew2176_5492_1396, (transfer (s:=2176) (a:=5492) (t:=384) (u:=3642) perm154 (by decide +kernel) (by decide +kernel) lb384_3642_7)⟩ ?_
    refine rows_cons ⟨ew128_3444_3444, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew4224_3444_3444, (zero_bound _ _)⟩ ?_
    exact rows_nil _ _
  · unfold rs; decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_7988_8 : CountBound 128 7988 8 := by
  exact fixE 2 true ew128_7988_4 (by decide +kernel) ew132_7984_16 (by decide +kernel) lb132_7984_7

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_7988_9 : CountBound 128 7988 9 := by
  exact fixE 9 false ew128_7988_512 (by decide +kernel) ew128_7476_4 (by decide +kernel) lb128_7476_8

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_8036_8 : CountBound 128 8036 8 := by
  exact fixE 2 false ew128_8036_4 (by decide +kernel) ew128_8032_32 (by decide +kernel) lb128_8032_7

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_8036_9 : CountBound 128 8036 9 := by
  exact fixE 9 false ew128_8036_512 (by decide +kernel) ew128_7524_4 (by decide +kernel) (transfer (s:=128) (a:=7524) (t:=128) (u:=7476) perm2 (by decide +kernel) (by decide +kernel) lb128_7476_8)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb132_3643_8 : CountBound 132 3643 8 := by
  exact fixE 0 false ew132_3643_1 (by decide +kernel) ew132_3642_2 (by decide +kernel) lb132_3642_7

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb132_3699_8 : CountBound 132 3699 8 := by
  exact fixE 0 false ew132_3699_1 (by decide +kernel) ew132_3698_2 (by decide +kernel) (transfer (s:=132) (a:=3698) (t:=132) (u:=3697) perm24 (by decide +kernel) (by decide +kernel) lb132_3697_7)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb132_3699_9 : CountBound 132 3699 9 := by
  exact fixE 0 false ew132_3699_1 (by decide +kernel) ew132_3698_2 (by decide +kernel) (transfer (s:=132) (a:=3698) (t:=132) (u:=3697) perm24 (by decide +kernel) (by decide +kernel) lb132_3697_8)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb132_8048_9 : CountBound 132 8048 9 := by
  exact fixE 8 false ew132_8048_256 (by decide +kernel) ew132_7792_16 (by decide +kernel) (transfer (s:=132) (a:=7792) (t:=132) (u:=3952) perm32 (by decide +kernel) (by decide +kernel) lb132_3952_8)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_959_9 : CountBound 0 959 9 := by
  exact fixE 3 false ew0_959_8 (by decide +kernel) ew0_951_1 (by decide +kernel) lb0_951_8

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_991_9 : CountBound 0 991 9 := by
  exact fixE 0 false ew0_991_1 (by decide +kernel) ew0_990_2 (by decide +kernel) (transfer (s:=0) (a:=990) (t:=0) (u:=951) perm147 (by decide +kernel) (by decide +kernel) lb0_951_8)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_1007_10 : CountBound 0 1007 10 := by
  exact fixE 0 false ew0_1007_1 (by decide +kernel) ew0_1006_2 (by decide +kernel) (transfer (s:=0) (a:=1006) (t:=0) (u:=943) perm147 (by decide +kernel) (by decide +kernel) lb0_943_9)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_1471_9 : CountBound 0 1471 9 := by
  exact fixE 1 false ew0_1471_2 (by decide +kernel) ew0_1469_1 (by decide +kernel) (transfer (s:=0) (a:=1469) (t:=0) (u:=1439) perm17 (by decide +kernel) (by decide +kernel) lb0_1439_8)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_1951_10 : CountBound 0 1951 10 := by
  exact fixE 3 false ew0_1951_8 (by decide +kernel) ew0_1943_1 (by decide +kernel) lb0_1943_9

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_1967_9 : CountBound 0 1967 9 := by
  exact fixE 0 false ew0_1967_1 (by decide +kernel) ew0_1966_2 (by decide +kernel) lb0_1966_8

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_1979_9 : CountBound 0 1979 9 := by
  exact fixE 1 false ew0_1979_2 (by decide +kernel) ew0_1977_1 (by decide +kernel) (transfer (s:=0) (a:=1977) (t:=0) (u:=1935) perm22 (by decide +kernel) (by decide +kernel) lb0_1935_8)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_1982_10 : CountBound 0 1982 10 := by
  exact fixE 2 true ew0_1982_4 (by decide +kernel) ew4_1978_2 (by decide +kernel) (transfer (s:=4) (a:=1978) (t:=1) (u:=6900) perm88 (by decide +kernel) (by decide +kernel) lb1_6900_9)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_2030_9 : CountBound 0 2030 9 := by
  exact fixE 1 false ew0_2030_2 (by decide +kernel) ew0_2028_4 (by decide +kernel) (transfer (s:=0) (a:=2028) (t:=0) (u:=1966) perm21 (by decide +kernel) (by decide +kernel) lb0_1966_8)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_2030_10 : CountBound 0 2030 10 := by
  exact fixE 2 false ew0_2030_4 (by decide +kernel) ew0_2026_2 (by decide +kernel) (transfer (s:=0) (a:=2026) (t:=0) (u:=2022) perm21 (by decide +kernel) (by decide +kernel) lb0_2022_9)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_3771_10 : CountBound 0 3771 10 := by
  exact fixE 0 false ew0_3771_1 (by decide +kernel) ew0_3770_2 (by decide +kernel) lb0_3770_9

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_3771_11 : CountBound 0 3771 11 := by
  exact fixE 0 false ew0_3771_1 (by decide +kernel) ew0_3770_2 (by decide +kernel) lb0_3770_10

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_3774_10 : CountBound 0 3774 10 := by
  exact fix_one 2 false (by decide +kernel) lb0_3770_10

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_3983_10 : CountBound 0 3983 10 := by
  exact fixE 2 false ew0_3983_4 (by decide +kernel) ew0_3979_1 (by decide +kernel) lb0_3979_9

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_3991_9 : CountBound 0 3991 9 := by
  exact fixE 1 true ew0_3991_2 (by decide +kernel) ew2_3989_1 (by decide +kernel) (transfer (s:=2) (a:=3989) (t:=1) (u:=7096) perm73 (by decide +kernel) (by decide +kernel) lb1_7096_8)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_3991_10 : CountBound 0 3991 10 := by
  exact fixE 2 false ew0_3991_4 (by decide +kernel) ew0_3987_1 (by decide +kernel) lb0_3987_9

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_3995_9 : CountBound 0 3995 9 := by
  exact fixE 1 true ew0_3995_2 (by decide +kernel) ew2_3993_1 (by decide +kernel) (transfer (s:=2) (a:=3993) (t:=1) (u:=7082) perm73 (by decide +kernel) (by decide +kernel) lb1_7082_8)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_3995_10 : CountBound 0 3995 10 := by
  exact fixE 3 false ew0_3995_8 (by decide +kernel) ew0_3987_1 (by decide +kernel) lb0_3987_9

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_3998_10 : CountBound 0 3998 10 := by
  exact fixE 8 true ew0_3998_256 (by decide +kernel) ew256_3742_2 (by decide +kernel) (transfer (s:=256) (a:=3742) (t:=128) (u:=7478) perm12 (by decide +kernel) (by decide +kernel) lb128_7478_9)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_4026_10 : CountBound 0 4026 10 := by
  exact fix_one 8 false (by decide +kernel) lb0_3770_10

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_4039_9 : CountBound 0 4039 9 := by
  exact fixE 1 false ew0_4039_2 (by decide +kernel) ew0_4037_1 (by decide +kernel) lb0_4037_8

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_4039_10 : CountBound 0 4039 10 := by
  exact fixE 2 false ew0_4039_4 (by decide +kernel) ew0_4035_1 (by decide +kernel) lb0_4035_9

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_8071_9 : CountBound 0 8071 9 := by
  exact fixE 10 false ew0_8071_1024 (by decide +kernel) ew0_7047_1 (by decide +kernel) (transfer (s:=0) (a:=7047) (t:=0) (u:=3994) perm77 (by decide +kernel) (by decide +kernel) lb0_3994_8)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_8075_9 : CountBound 0 8075 9 := by
  exact fixE 8 false ew0_8075_256 (by decide +kernel) ew0_7819_1 (by decide +kernel) (transfer (s:=0) (a:=7819) (t:=0) (u:=3979) perm32 (by decide +kernel) (by decide +kernel) lb0_3979_8)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_8077_9 : CountBound 0 8077 9 := by
  exact fixE 7 false ew0_8077_128 (by decide +kernel) ew0_7949_1 (by decide +kernel) (transfer (s:=0) (a:=7949) (t:=0) (u:=3994) perm29 (by decide +kernel) (by decide +kernel) lb0_3994_8)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_8105_10 : CountBound 0 8105 10 := by
  exact fixE 7 false ew0_8105_128 (by decide +kernel) ew0_7977_1 (by decide +kernel) (transfer (s:=0) (a:=7977) (t:=0) (u:=3987) perm30 (by decide +kernel) (by decide +kernel) lb0_3987_9)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_6782_10 : CountBound 1 6782 10 := by
  exact fixE 1 false ew1_6782_2 (by decide +kernel) ew1_6780_4 (by decide +kernel) (transfer (s:=1) (a:=6780) (t:=1) (u:=6766) perm12 (by decide +kernel) (by decide +kernel) lb1_6766_9)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_6846_9 : CountBound 1 6846 9 := by
  exact fixE 1 false ew1_6846_2 (by decide +kernel) ew1_6844_4 (by decide +kernel) lb1_6844_8

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_6902_9 : CountBound 1 6902 9 := by
  exact fixE 1 false ew1_6902_2 (by decide +kernel) ew1_6900_4 (by decide +kernel) lb1_6900_8

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_6908_9 : CountBound 1 6908 9 := by
  exact fixE 2 false ew1_6908_4 (by decide +kernel) ew1_6904_8 (by decide +kernel) (transfer (s:=1) (a:=6904) (t:=1) (u:=6892) perm1 (by decide +kernel) (by decide +kernel) lb1_6892_8)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_7098_10 : CountBound 1 7098 10 := by
  exact fixE 7 false ew1_7098_128 (by decide +kernel) ew1_6970_2 (by decide +kernel) (transfer (s:=1) (a:=6970) (t:=1) (u:=6900) perm4 (by decide +kernel) (by decide +kernel) lb1_6900_9)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_7118_10 : CountBound 1 7118 10 := by
  exact fixE 7 false ew1_7118_128 (by decide +kernel) ew1_6990_2 (by decide +kernel) (transfer (s:=1) (a:=6990) (t:=1) (u:=6842) perm12 (by decide +kernel) (by decide +kernel) lb1_6842_9)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_7160_10 : CountBound 1 7160 10 := by
  exact fixE 4 false ew1_7160_16 (by decide +kernel) ew1_7144_8 (by decide +kernel) lb1_7144_9

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_8078_9 : CountBound 1 8078 9 := by
  exact fixE 7 false ew1_8078_128 (by decide +kernel) ew1_7950_2 (by decide +kernel) (transfer (s:=1) (a:=7950) (t:=1) (u:=7090) perm12 (by decide +kernel) (by decide +kernel) lb1_7090_8)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_14910_10 : CountBound 1 14910 10 := by
  exact fixE 1 false ew1_14910_2 (by decide +kernel) ew1_14908_4 (by decide +kernel) (transfer (s:=1) (a:=14908) (t:=1) (u:=14878) perm17 (by decide +kernel) (by decide +kernel) lb1_14878_9)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_14910_11 : CountBound 1 14910 11 := by
  let rs : List Row := [⟨1,false,4,9⟩, ⟨1,true,14848,0⟩, ⟨2,false,58,8⟩, ⟨2,true,14906,0⟩, ⟨3,false,2,9⟩, ⟨3,true,14850,0⟩, ⟨4,false,10,9⟩, ⟨4,true,14858,0⟩, ⟨5,false,26,9⟩, ⟨5,true,14874,0⟩, ⟨9,false,62,8⟩, ⟨9,true,2,8⟩, ⟨11,false,574,8⟩, ⟨11,true,514,8⟩, ⟨12,false,2622,8⟩, ⟨12,true,2562,8⟩, ⟨13,false,6718,0⟩, ⟨13,true,6658,8⟩]
  apply rule_tables (rs:=rs) ?_ (by decide +kernel) ew1_14910_14910 ?_
  · unfold rs
    refine rows_cons ⟨ew1_14908_4, (transfer (s:=1) (a:=14908) (t:=1) (u:=14878) perm17 (by decide +kernel) (by decide +kernel) lb1_14878_9)⟩ ?_
    refine rows_cons ⟨ew3_14908_14848, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew1_14906_58, lb1_14906_8⟩ ?_
    refine rows_cons ⟨ew5_14906_14906, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew1_14902_2, (transfer (s:=1) (a:=14902) (t:=1) (u:=14878) perm6 (by decide +kernel) (by decide +kernel) lb1_14878_9)⟩ ?_
    refine rows_cons ⟨ew9_14902_14850, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew1_14894_10, (transfer (s:=1) (a:=14894) (t:=1) (u:=14878) perm8 (by decide +kernel) (by decide +kernel) lb1_14878_9)⟩ ?_
    refine rows_cons ⟨ew17_14894_14858, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew1_14878_26, lb1_14878_9⟩ ?_
    refine rows_cons ⟨ew33_14878_14874, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew1_14398_62, (transfer (s:=1) (a:=14398) (t:=1) (u:=6766) perm2 (by decide +kernel) (by decide +kernel) lb1_6766_8)⟩ ?_
    refine rows_cons ⟨ew513_14398_2, (transfer (s:=513) (a:=14398) (t:=132) (u:=3699) perm51 (by decide +kernel) (by decide +kernel) lb132_3699_8)⟩ ?_
    refine rows_cons ⟨ew1_12862_574, (transfer (s:=1) (a:=12862) (t:=1) (u:=6766) perm10 (by decide +kernel) (by decide +kernel) lb1_6766_8)⟩ ?_
    refine rows_cons ⟨ew2049_12862_514, (transfer (s:=2049) (a:=12862) (t:=132) (u:=3699) perm62 (by decide +kernel) (by decide +kernel) lb132_3699_8)⟩ ?_
    refine rows_cons ⟨ew1_10814_2622, (transfer (s:=1) (a:=10814) (t:=1) (u:=6718) perm8 (by decide +kernel) (by decide +kernel) lb1_6718_8)⟩ ?_
    refine rows_cons ⟨ew4097_10814_2562, (transfer (s:=4097) (a:=10814) (t:=132) (u:=3643) perm60 (by decide +kernel) (by decide +kernel) lb132_3643_8)⟩ ?_
    refine rows_cons ⟨ew1_6718_6718, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew8193_6718_6658, (transfer (s:=8193) (a:=6718) (t:=132) (u:=3643) perm52 (by decide +kernel) (by decide +kernel) lb132_3643_8)⟩ ?_
    exact rows_nil _ _
  · unfold rs; decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_15030_10 : CountBound 1 15030 10 := by
  exact fixE 5 false ew1_15030_32 (by decide +kernel) ew1_14998_2 (by decide +kernel) lb1_14998_9

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_15092_10 : CountBound 1 15092 10 := by
  exact fixE 7 false ew1_15092_128 (by decide +kernel) ew1_14964_4 (by decide +kernel) (transfer (s:=1) (a:=14964) (t:=1) (u:=14906) perm4 (by decide +kernel) (by decide +kernel) lb1_14906_9)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_15254_9 : CountBound 1 15254 9 := by
  exact fixE 7 false ew1_15254_128 (by decide +kernel) ew1_15126_2 (by decide +kernel) (transfer (s:=1) (a:=15126) (t:=1) (u:=14998) perm4 (by decide +kernel) (by decide +kernel) lb1_14998_8)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_15254_10 : CountBound 1 15254 10 := by
  exact fixE 7 false ew1_15254_128 (by decide +kernel) ew1_15126_2 (by decide +kernel) (transfer (s:=1) (a:=15126) (t:=1) (u:=14998) perm4 (by decide +kernel) (by decide +kernel) lb1_14998_9)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_15258_9 : CountBound 1 15258 9 := by
  exact fixE 7 false ew1_15258_128 (by decide +kernel) ew1_15130_2 (by decide +kernel) (transfer (s:=1) (a:=15130) (t:=1) (u:=15028) perm12 (by decide +kernel) (by decide +kernel) lb1_15028_8)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_15282_9 : CountBound 1 15282 9 := by
  exact fixE 7 false ew1_15282_128 (by decide +kernel) ew1_15154_2 (by decide +kernel) (transfer (s:=1) (a:=15154) (t:=1) (u:=15028) perm4 (by decide +kernel) (by decide +kernel) lb1_15028_8)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_1855_9 : CountBound 128 1855 9 := by
  exact fixE 0 false ew128_1855_1 (by decide +kernel) ew128_1854_2 (by decide +kernel) lb128_1854_8

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_1917_9 : CountBound 128 1917 9 := by
  exact fixE 0 false ew128_1917_1 (by decide +kernel) ew128_1916_4 (by decide +kernel) lb128_1916_8

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_1918_9 : CountBound 128 1918 9 := by
  exact fixE 1 false ew128_1918_2 (by decide +kernel) ew128_1916_4 (by decide +kernel) lb128_1916_8

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_2935_9 : CountBound 128 2935 9 := by
  exact fixE 0 false ew128_2935_1 (by decide +kernel) ew128_2934_2 (by decide +kernel) (transfer (s:=128) (a:=2934) (t:=128) (u:=2933) perm26 (by decide +kernel) (by decide +kernel) lb128_2933_8)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_3707_10 : CountBound 128 3707 10 := by
  exact fixE 0 false ew128_3707_1 (by decide +kernel) ew128_3706_2 (by decide +kernel) (transfer (s:=128) (a:=3706) (t:=128) (u:=3699) perm72 (by decide +kernel) (by decide +kernel) lb128_3699_9)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_3958_10 : CountBound 128 3958 10 := by
  exact fixE 1 false ew128_3958_2 (by decide +kernel) ew128_3956_4 (by decide +kernel) lb128_3956_9

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_3958_11 : CountBound 128 3958 11 := by
  exact fixE 1 false ew128_3958_2 (by decide +kernel) ew128_3956_4 (by decide +kernel) lb128_3956_10

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_7479_10 : CountBound 128 7479 10 := by
  exact fixE 0 false ew128_7479_1 (by decide +kernel) ew128_7478_2 (by decide +kernel) lb128_7478_9

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_7542_10 : CountBound 128 7542 10 := by
  exact fixE 1 false ew128_7542_2 (by decide +kernel) ew128_7540_4 (by decide +kernel) lb128_7540_9

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_7542_11 : CountBound 128 7542 11 := by
  exact fixE 1 false ew128_7542_2 (by decide +kernel) ew128_7540_4 (by decide +kernel) lb128_7540_10

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_7989_9 : CountBound 128 7989 9 := by
  exact fixE 0 false ew128_7989_1 (by decide +kernel) ew128_7988_4 (by decide +kernel) lb128_7988_8

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_7989_10 : CountBound 128 7989 10 := by
  exact fixE 0 false ew128_7989_1 (by decide +kernel) ew128_7988_4 (by decide +kernel) lb128_7988_9

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_7990_9 : CountBound 128 7990 9 := by
  exact fixE 1 false ew128_7990_2 (by decide +kernel) ew128_7988_4 (by decide +kernel) lb128_7988_8

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_7990_10 : CountBound 128 7990 10 := by
  exact fixE 1 false ew128_7990_2 (by decide +kernel) ew128_7988_4 (by decide +kernel) lb128_7988_9

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_8038_9 : CountBound 128 8038 9 := by
  exact fixE 1 false ew128_8038_2 (by decide +kernel) ew128_8036_4 (by decide +kernel) lb128_8036_8

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_8038_10 : CountBound 128 8038 10 := by
  exact fixE 1 false ew128_8038_2 (by decide +kernel) ew128_8036_4 (by decide +kernel) lb128_8036_9

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_8052_10 : CountBound 128 8052 10 := by
  exact fixE 2 false ew128_8052_4 (by decide +kernel) ew128_8048_16 (by decide +kernel) (transfer (s:=128) (a:=8048) (t:=128) (u:=8036) perm1 (by decide +kernel) (by decide +kernel) lb128_8036_9)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_8052_11 : CountBound 128 8052 11 := by
  exact fixE 8 false ew128_8052_256 (by decide +kernel) ew128_7796_4 (by decide +kernel) (transfer (s:=128) (a:=7796) (t:=128) (u:=3956) perm32 (by decide +kernel) (by decide +kernel) lb128_3956_10)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_16180_10 : CountBound 128 16180 10 := by
  exact fixE 8 false ew128_16180_256 (by decide +kernel) ew128_15924_4 (by decide +kernel) (transfer (s:=128) (a:=15924) (t:=128) (u:=8036) perm24 (by decide +kernel) (by decide +kernel) lb128_8036_9)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb132_3707_10 : CountBound 132 3707 10 := by
  exact fixE 0 false ew132_3707_1 (by decide +kernel) ew132_3706_2 (by decide +kernel) (transfer (s:=132) (a:=3706) (t:=132) (u:=3699) perm72 (by decide +kernel) (by decide +kernel) lb132_3699_9)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb132_16240_10 : CountBound 132 16240 10 := by
  exact fixE 8 false ew132_16240_256 (by decide +kernel) ew132_15984_16 (by decide +kernel) (transfer (s:=132) (a:=15984) (t:=132) (u:=8048) perm24 (by decide +kernel) (by decide +kernel) lb132_8048_9)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_1983_11 : CountBound 0 1983 11 := by
  exact fixE 0 false ew0_1983_1 (by decide +kernel) ew0_1982_2 (by decide +kernel) lb0_1982_10

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_1983_12 : CountBound 0 1983 12 := by
  let rs : List Row := [⟨0,false,2,10⟩, ⟨0,true,1920,0⟩, ⟨1,false,1,10⟩, ⟨1,true,1941,0⟩, ⟨2,false,259,9⟩, ⟨2,true,1,9⟩, ⟨3,false,135,9⟩, ⟨3,true,7,9⟩, ⟨4,false,1039,9⟩, ⟨4,true,45,9⟩, ⟨5,false,31,10⟩, ⟨5,true,1935,0⟩, ⟨7,false,567,9⟩, ⟨7,true,29,9⟩, ⟨8,false,699,9⟩, ⟨8,true,157,9⟩, ⟨9,false,63,9⟩, ⟨9,true,413,9⟩, ⟨10,false,943,9⟩, ⟨10,true,925,9⟩]
  apply rule_tables (rs:=rs) ?_ (by decide +kernel) ew0_1983_1983 ?_
  · unfold rs
    refine rows_cons ⟨ew0_1982_2, lb0_1982_10⟩ ?_
    refine rows_cons ⟨ew1_1982_1920, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_1981_1, (transfer (s:=0) (a:=1981) (t:=0) (u:=1951) perm17 (by decide +kernel) (by decide +kernel) lb0_1951_10)⟩ ?_
    refine rows_cons ⟨ew2_1981_1941, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_1979_259, lb0_1979_9⟩ ?_
    refine rows_cons ⟨ew4_1979_1, (transfer (s:=4) (a:=1979) (t:=1) (u:=6908) perm88 (by decide +kernel) (by decide +kernel) lb1_6908_9)⟩ ?_
    refine rows_cons ⟨ew0_1975_135, (transfer (s:=0) (a:=1975) (t:=0) (u:=1967) perm17 (by decide +kernel) (by decide +kernel) lb0_1967_9)⟩ ?_
    refine rows_cons ⟨ew8_1975_7, (transfer (s:=8) (a:=1975) (t:=1) (u:=6846) perm77 (by decide +kernel) (by decide +kernel) lb1_6846_9)⟩ ?_
    refine rows_cons ⟨ew0_1967_1039, lb0_1967_9⟩ ?_
    refine rows_cons ⟨ew16_1967_45, (transfer (s:=16) (a:=1967) (t:=1) (u:=6846) perm90 (by decide +kernel) (by decide +kernel) lb1_6846_9)⟩ ?_
    refine rows_cons ⟨ew0_1951_31, lb0_1951_10⟩ ?_
    refine rows_cons ⟨ew32_1951_1935, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_1855_567, (transfer (s:=0) (a:=1855) (t:=0) (u:=959) perm17 (by decide +kernel) (by decide +kernel) lb0_959_9)⟩ ?_
    refine rows_cons ⟨ew128_1855_29, lb128_1855_9⟩ ?_
    refine rows_cons ⟨ew0_1727_699, (transfer (s:=0) (a:=1727) (t:=0) (u:=991) perm1 (by decide +kernel) (by decide +kernel) lb0_991_9)⟩ ?_
    refine rows_cons ⟨ew256_1727_157, (transfer (s:=256) (a:=1727) (t:=128) (u:=1917) perm18 (by decide +kernel) (by decide +kernel) lb128_1917_9)⟩ ?_
    refine rows_cons ⟨ew0_1471_63, lb0_1471_9⟩ ?_
    refine rows_cons ⟨ew512_1471_413, (transfer (s:=512) (a:=1471) (t:=128) (u:=2935) perm146 (by decide +kernel) (by decide +kernel) lb128_2935_9)⟩ ?_
    refine rows_cons ⟨ew0_959_943, lb0_959_9⟩ ?_
    refine rows_cons ⟨ew1024_959_925, (transfer (s:=1024) (a:=959) (t:=128) (u:=1855) perm17 (by decide +kernel) (by decide +kernel) lb128_1855_9)⟩ ?_
    exact rows_nil _ _
  · unfold rs; decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_2031_11 : CountBound 0 2031 11 := by
  exact fixE 0 false ew0_2031_1 (by decide +kernel) ew0_2030_2 (by decide +kernel) lb0_2030_10

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_2046_11 : CountBound 0 2046 11 := by
  exact fixE 1 false ew0_2046_2 (by decide +kernel) ew0_2044_4 (by decide +kernel) (transfer (s:=0) (a:=2044) (t:=0) (u:=1982) perm21 (by decide +kernel) (by decide +kernel) lb0_1982_10)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_2046_12 : CountBound 0 2046 12 := by
  let rs : List Row := [⟨1,false,4,10⟩, ⟨1,true,1428,0⟩, ⟨2,false,258,9⟩, ⟨2,true,66,9⟩, ⟨3,false,134,9⟩, ⟨3,true,6,9⟩, ⟨4,false,1038,9⟩, ⟨4,true,46,9⟩, ⟨5,false,30,10⟩, ⟨5,true,1422,0⟩, ⟨6,false,62,10⟩, ⟨6,true,1466,0⟩, ⟨7,false,118,9⟩, ⟨7,true,30,9⟩, ⟨8,false,250,9⟩, ⟨8,true,158,9⟩, ⟨9,false,1534,0⟩, ⟨9,true,1534,0⟩, ⟨10,false,494,9⟩, ⟨10,true,414,9⟩]
  apply rule_tables (rs:=rs) ?_ (by decide +kernel) ew0_2046_2046 ?_
  · unfold rs
    refine rows_cons ⟨ew0_2044_4, (transfer (s:=0) (a:=2044) (t:=0) (u:=1982) perm21 (by decide +kernel) (by decide +kernel) lb0_1982_10)⟩ ?_
    refine rows_cons ⟨ew2_2044_1428, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_2042_258, (transfer (s:=0) (a:=2042) (t:=0) (u:=2030) perm1 (by decide +kernel) (by decide +kernel) lb0_2030_9)⟩ ?_
    refine rows_cons ⟨ew4_2042_66, (transfer (s:=4) (a:=2042) (t:=1) (u:=6902) perm88 (by decide +kernel) (by decide +kernel) lb1_6902_9)⟩ ?_
    refine rows_cons ⟨ew0_2038_134, (transfer (s:=0) (a:=2038) (t:=0) (u:=2030) perm17 (by decide +kernel) (by decide +kernel) lb0_2030_9)⟩ ?_
    refine rows_cons ⟨ew8_2038_6, (transfer (s:=8) (a:=2038) (t:=1) (u:=6902) perm76 (by decide +kernel) (by decide +kernel) lb1_6902_9)⟩ ?_
    refine rows_cons ⟨ew0_2030_1038, lb0_2030_9⟩ ?_
    refine rows_cons ⟨ew16_2030_46, (transfer (s:=16) (a:=2030) (t:=1) (u:=6902) perm90 (by decide +kernel) (by decide +kernel) lb1_6902_9)⟩ ?_
    refine rows_cons ⟨ew0_2014_30, (transfer (s:=0) (a:=2014) (t:=0) (u:=1982) perm1 (by decide +kernel) (by decide +kernel) lb0_1982_10)⟩ ?_
    refine rows_cons ⟨ew32_2014_1422, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_1982_62, lb0_1982_10⟩ ?_
    refine rows_cons ⟨ew64_1982_1466, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_1918_118, (transfer (s:=0) (a:=1918) (t:=0) (u:=959) perm158 (by decide +kernel) (by decide +kernel) lb0_959_9)⟩ ?_
    refine rows_cons ⟨ew128_1918_30, lb128_1918_9⟩ ?_
    refine rows_cons ⟨ew0_1790_250, (transfer (s:=0) (a:=1790) (t:=0) (u:=959) perm146 (by decide +kernel) (by decide +kernel) lb0_959_9)⟩ ?_
    refine rows_cons ⟨ew256_1790_158, (transfer (s:=256) (a:=1790) (t:=128) (u:=1918) perm18 (by decide +kernel) (by decide +kernel) lb128_1918_9)⟩ ?_
    refine rows_cons ⟨ew0_1534_1534, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew512_1534_1534, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_1022_494, (transfer (s:=0) (a:=1022) (t:=0) (u:=959) perm147 (by decide +kernel) (by decide +kernel) lb0_959_9)⟩ ?_
    refine rows_cons ⟨ew1024_1022_414, (transfer (s:=1024) (a:=1022) (t:=128) (u:=1918) perm17 (by decide +kernel) (by decide +kernel) lb128_1918_9)⟩ ?_
    exact rows_nil _ _
  · unfold rs; decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_3775_11 : CountBound 0 3775 11 := by
  exact fixE 0 false ew0_3775_1 (by decide +kernel) ew0_3774_2 (by decide +kernel) lb0_3774_10

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_3835_13 : CountBound 0 3835 13 := by
  let rs : List Row := [⟨0,false,2,11⟩, ⟨0,true,3712,0⟩, ⟨1,false,1,11⟩, ⟨1,true,3713,0⟩, ⟨3,false,3,11⟩, ⟨3,true,3715,0⟩, ⟨4,false,11,11⟩, ⟨4,true,3723,0⟩, ⟨5,false,27,11⟩, ⟨5,true,3739,0⟩, ⟨6,false,59,10⟩, ⟨6,true,3771,0⟩, ⟨7,false,123,10⟩, ⟨7,true,1,10⟩, ⟨9,false,251,10⟩, ⟨9,true,129,10⟩, ⟨10,false,763,10⟩, ⟨10,true,641,10⟩, ⟨11,false,1787,0⟩, ⟨11,true,1665,10⟩]
  apply rule_tables (rs:=rs) ?_ (by decide +kernel) ew0_3835_3835 ?_
  · unfold rs
    refine rows_cons ⟨ew0_3834_2, (transfer (s:=0) (a:=3834) (t:=0) (u:=3771) perm149 (by decide +kernel) (by decide +kernel) lb0_3771_11)⟩ ?_
    refine rows_cons ⟨ew1_3834_3712, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_3833_1, (transfer (s:=0) (a:=3833) (t:=0) (u:=3771) perm45 (by decide +kernel) (by decide +kernel) lb0_3771_11)⟩ ?_
    refine rows_cons ⟨ew2_3833_3713, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_3827_3, (transfer (s:=0) (a:=3827) (t:=0) (u:=3771) perm41 (by decide +kernel) (by decide +kernel) lb0_3771_11)⟩ ?_
    refine rows_cons ⟨ew8_3827_3715, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_3819_11, (transfer (s:=0) (a:=3819) (t:=0) (u:=3771) perm24 (by decide +kernel) (by decide +kernel) lb0_3771_11)⟩ ?_
    refine rows_cons ⟨ew16_3819_3723, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_3803_27, (transfer (s:=0) (a:=3803) (t:=0) (u:=3771) perm32 (by decide +kernel) (by decide +kernel) lb0_3771_11)⟩ ?_
    refine rows_cons ⟨ew32_3803_3739, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_3771_59, lb0_3771_10⟩ ?_
    refine rows_cons ⟨ew64_3771_3771, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_3707_123, (transfer (s:=0) (a:=3707) (t:=0) (u:=1007) perm58 (by decide +kernel) (by decide +kernel) lb0_1007_10)⟩ ?_
    refine rows_cons ⟨ew128_3707_1, lb128_3707_10⟩ ?_
    refine rows_cons ⟨ew0_3323_251, (transfer (s:=0) (a:=3323) (t:=0) (u:=1007) perm6 (by decide +kernel) (by decide +kernel) lb0_1007_10)⟩ ?_
    refine rows_cons ⟨ew512_3323_129, (transfer (s:=512) (a:=3323) (t:=128) (u:=3707) perm97 (by decide +kernel) (by decide +kernel) lb128_3707_10)⟩ ?_
    refine rows_cons ⟨ew0_2811_763, (transfer (s:=0) (a:=2811) (t:=0) (u:=1007) perm50 (by decide +kernel) (by decide +kernel) lb0_1007_10)⟩ ?_
    refine rows_cons ⟨ew1024_2811_641, (transfer (s:=1024) (a:=2811) (t:=128) (u:=3707) perm13 (by decide +kernel) (by decide +kernel) lb128_3707_10)⟩ ?_
    refine rows_cons ⟨ew0_1787_1787, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew2048_1787_1665, (transfer (s:=2048) (a:=1787) (t:=128) (u:=3707) perm113 (by decide +kernel) (by decide +kernel) lb128_3707_10)⟩ ?_
    exact rows_nil _ _
  · unfold rs; decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_3999_11 : CountBound 0 3999 11 := by
  exact fixE 0 false ew0_3999_1 (by decide +kernel) ew0_3998_2 (by decide +kernel) lb0_3998_10

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_3999_12 : CountBound 0 3999 12 := by
  exact fixE 9 true ew0_3999_512 (by decide +kernel) ew512_3487_1 (by decide +kernel) (transfer (s:=512) (a:=3487) (t:=128) (u:=3958) perm149 (by decide +kernel) (by decide +kernel) lb128_3958_11)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_4027_11 : CountBound 0 4027 11 := by
  exact fixE 1 false ew0_4027_2 (by decide +kernel) ew0_4025_1 (by decide +kernel) (transfer (s:=0) (a:=4025) (t:=0) (u:=3995) perm17 (by decide +kernel) (by decide +kernel) lb0_3995_10)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_4027_12 : CountBound 0 4027 12 := by
  exact fixE 8 false ew0_4027_256 (by decide +kernel) ew0_3771_1 (by decide +kernel) lb0_3771_11

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_4030_12 : CountBound 0 4030 12 := by
  exact fixE 8 true ew0_4030_256 (by decide +kernel) ew256_3774_2 (by decide +kernel) (transfer (s:=256) (a:=3774) (t:=128) (u:=7542) perm4 (by decide +kernel) (by decide +kernel) lb128_7542_11)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_4047_11 : CountBound 0 4047 11 := by
  exact fixE 1 false ew0_4047_2 (by decide +kernel) ew0_4045_1 (by decide +kernel) (transfer (s:=0) (a:=4045) (t:=0) (u:=4039) perm8 (by decide +kernel) (by decide +kernel) lb0_4039_10)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_4055_11 : CountBound 0 4055 11 := by
  exact fixE 0 false ew0_4055_1 (by decide +kernel) ew0_4054_2 (by decide +kernel) (transfer (s:=0) (a:=4054) (t:=0) (u:=3991) perm149 (by decide +kernel) (by decide +kernel) lb0_3991_10)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_4059_11 : CountBound 0 4059 11 := by
  exact fixE 0 false ew0_4059_1 (by decide +kernel) ew0_4058_2 (by decide +kernel) (transfer (s:=0) (a:=4058) (t:=0) (u:=3995) perm162 (by decide +kernel) (by decide +kernel) lb0_3995_10)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_8079_11 : CountBound 0 8079 11 := by
  exact fixE 2 true ew0_8079_4 (by decide +kernel) ew4_8075_1 (by decide +kernel) (transfer (s:=4) (a:=8075) (t:=1) (u:=15254) perm36 (by decide +kernel) (by decide +kernel) lb1_15254_10)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_8079_12 : CountBound 0 8079 12 := by
  let rs : List Row := [⟨0,false,7046,9⟩, ⟨0,true,2,9⟩, ⟨1,false,7565,9⟩, ⟨1,true,1,9⟩, ⟨2,false,1,9⟩, ⟨2,true,11,9⟩, ⟨3,false,6021,9⟩, ⟨3,true,3,9⟩, ⟨7,false,5,10⟩, ⟨7,true,15,0⟩, ⟨8,false,133,10⟩, ⟨8,true,2703,0⟩, ⟨9,false,391,9⟩, ⟨9,true,143,9⟩, ⟨10,false,901,9⟩, ⟨10,true,911,9⟩, ⟨11,false,1933,9⟩, ⟨11,true,5775,9⟩, ⟨12,false,3973,10⟩, ⟨12,true,1935,0⟩]
  apply rule_tables (rs:=rs) ?_ (by decide +kernel) ew0_8079_8079 ?_
  · unfold rs
    refine rows_cons ⟨ew0_8078_7046, (transfer (s:=0) (a:=8078) (t:=0) (u:=8071) perm76 (by decide +kernel) (by decide +kernel) lb0_8071_9)⟩ ?_
    refine rows_cons ⟨ew1_8078_2, lb1_8078_9⟩ ?_
    refine rows_cons ⟨ew0_8077_7565, lb0_8077_9⟩ ?_
    refine rows_cons ⟨ew2_8077_1, (transfer (s:=2) (a:=8077) (t:=1) (u:=15258) perm25 (by decide +kernel) (by decide +kernel) lb1_15258_9)⟩ ?_
    refine rows_cons ⟨ew0_8075_1, lb0_8075_9⟩ ?_
    refine rows_cons ⟨ew4_8075_11, (transfer (s:=4) (a:=8075) (t:=1) (u:=15254) perm36 (by decide +kernel) (by decide +kernel) lb1_15254_9)⟩ ?_
    refine rows_cons ⟨ew0_8071_6021, lb0_8071_9⟩ ?_
    refine rows_cons ⟨ew8_8071_3, (transfer (s:=8) (a:=8071) (t:=1) (u:=8078) perm76 (by decide +kernel) (by decide +kernel) lb1_8078_9)⟩ ?_
    refine rows_cons ⟨ew0_7951_5, (transfer (s:=0) (a:=7951) (t:=0) (u:=3998) perm29 (by decide +kernel) (by decide +kernel) lb0_3998_10)⟩ ?_
    refine rows_cons ⟨ew128_7951_15, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_7823_133, (transfer (s:=0) (a:=7823) (t:=0) (u:=3983) perm32 (by decide +kernel) (by decide +kernel) lb0_3983_10)⟩ ?_
    refine rows_cons ⟨ew256_7823_2703, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_7567_391, (transfer (s:=0) (a:=7567) (t:=0) (u:=4039) perm4 (by decide +kernel) (by decide +kernel) lb0_4039_9)⟩ ?_
    refine rows_cons ⟨ew512_7567_143, (transfer (s:=512) (a:=7567) (t:=128) (u:=8038) perm125 (by decide +kernel) (by decide +kernel) lb128_8038_9)⟩ ?_
    refine rows_cons ⟨ew0_7055_901, (transfer (s:=0) (a:=7055) (t:=0) (u:=3995) perm77 (by decide +kernel) (by decide +kernel) lb0_3995_9)⟩ ?_
    refine rows_cons ⟨ew1024_7055_911, (transfer (s:=1024) (a:=7055) (t:=128) (u:=7989) perm13 (by decide +kernel) (by decide +kernel) lb128_7989_9)⟩ ?_
    refine rows_cons ⟨ew0_6031_1933, (transfer (s:=0) (a:=6031) (t:=0) (u:=3995) perm1 (by decide +kernel) (by decide +kernel) lb0_3995_9)⟩ ?_
    refine rows_cons ⟨ew2048_6031_5775, (transfer (s:=2048) (a:=6031) (t:=128) (u:=7989) perm137 (by decide +kernel) (by decide +kernel) lb128_7989_9)⟩ ?_
    refine rows_cons ⟨ew0_3983_3973, lb0_3983_10⟩ ?_
    refine rows_cons ⟨ew4096_3983_1935, (zero_bound _ _)⟩ ?_
    exact rows_nil _ _
  · unfold rs; decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_8087_12 : CountBound 0 8087 12 := by
  let rs : List Row := [⟨0,false,8086,0⟩, ⟨0,true,8086,0⟩, ⟨1,false,7553,9⟩, ⟨1,true,1,9⟩, ⟨2,false,3971,9⟩, ⟨2,true,3,9⟩, ⟨4,false,6023,9⟩, ⟨4,true,7,9⟩, ⟨7,false,1,10⟩, ⟨7,true,6166,0⟩, ⟨8,false,129,10⟩, ⟨8,true,2710,0⟩, ⟨9,false,387,9⟩, ⟨9,true,151,9⟩, ⟨10,false,897,10⟩, ⟨10,true,5014,0⟩, ⟨11,false,1937,9⟩, ⟨11,true,1559,9⟩, ⟨12,false,3973,9⟩, ⟨12,true,2839,9⟩]
  apply rule_tables (rs:=rs) ?_ (by decide +kernel) ew0_8087_8087 ?_
  · unfold rs
    refine rows_cons ⟨ew0_8086_8086, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew1_8086_8086, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_8085_7553, (transfer (s:=0) (a:=8085) (t:=0) (u:=8071) perm12 (by decide +kernel) (by decide +kernel) lb0_8071_9)⟩ ?_
    refine rows_cons ⟨ew2_8085_1, (transfer (s:=2) (a:=8085) (t:=1) (u:=15282) perm25 (by decide +kernel) (by decide +kernel) lb1_15282_9)⟩ ?_
    refine rows_cons ⟨ew0_8083_3971, (transfer (s:=0) (a:=8083) (t:=0) (u:=8071) perm1 (by decide +kernel) (by decide +kernel) lb0_8071_9)⟩ ?_
    refine rows_cons ⟨ew4_8083_3, (transfer (s:=4) (a:=8083) (t:=1) (u:=15282) perm36 (by decide +kernel) (by decide +kernel) lb1_15282_9)⟩ ?_
    refine rows_cons ⟨ew0_8071_6023, lb0_8071_9⟩ ?_
    refine rows_cons ⟨ew16_8071_7, (transfer (s:=16) (a:=8071) (t:=1) (u:=15282) perm38 (by decide +kernel) (by decide +kernel) lb1_15282_9)⟩ ?_
    refine rows_cons ⟨ew0_7959_1, (transfer (s:=0) (a:=7959) (t:=0) (u:=3998) perm81 (by decide +kernel) (by decide +kernel) lb0_3998_10)⟩ ?_
    refine rows_cons ⟨ew128_7959_6166, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_7831_129, (transfer (s:=0) (a:=7831) (t:=0) (u:=3998) perm76 (by decide +kernel) (by decide +kernel) lb0_3998_10)⟩ ?_
    refine rows_cons ⟨ew256_7831_2710, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_7575_387, (transfer (s:=0) (a:=7575) (t:=0) (u:=3991) perm4 (by decide +kernel) (by decide +kernel) lb0_3991_9)⟩ ?_
    refine rows_cons ⟨ew512_7575_151, (transfer (s:=512) (a:=7575) (t:=128) (u:=7990) perm125 (by decide +kernel) (by decide +kernel) lb128_7990_9)⟩ ?_
    refine rows_cons ⟨ew0_7063_897, (transfer (s:=0) (a:=7063) (t:=0) (u:=3998) perm77 (by decide +kernel) (by decide +kernel) lb0_3998_10)⟩ ?_
    refine rows_cons ⟨ew1024_7063_5014, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_6039_1937, (transfer (s:=0) (a:=6039) (t:=0) (u:=3991) perm1 (by decide +kernel) (by decide +kernel) lb0_3991_9)⟩ ?_
    refine rows_cons ⟨ew2048_6039_1559, (transfer (s:=2048) (a:=6039) (t:=128) (u:=7990) perm130 (by decide +kernel) (by decide +kernel) lb128_7990_9)⟩ ?_
    refine rows_cons ⟨ew0_3991_3973, lb0_3991_9⟩ ?_
    refine rows_cons ⟨ew4096_3991_2839, (transfer (s:=4096) (a:=3991) (t:=128) (u:=7990) perm129 (by decide +kernel) (by decide +kernel) lb128_7990_9)⟩ ?_
    exact rows_nil _ _
  · unfold rs; decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_8093_11 : CountBound 0 8093 11 := by
  exact fixE 7 false ew0_8093_128 (by decide +kernel) ew0_7965_1 (by decide +kernel) (transfer (s:=0) (a:=7965) (t:=0) (u:=4026) perm29 (by decide +kernel) (by decide +kernel) lb0_4026_10)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_8107_11 : CountBound 0 8107 11 := by
  exact fixE 1 false ew0_8107_2 (by decide +kernel) ew0_8105_1 (by decide +kernel) lb0_8105_10

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_7102_11 : CountBound 1 7102 11 := by
  exact fixE 2 false ew1_7102_4 (by decide +kernel) ew1_7098_2 (by decide +kernel) lb1_7098_10

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_7134_11 : CountBound 1 7134 11 := by
  exact fixE 4 false ew1_7134_16 (by decide +kernel) ew1_7118_2 (by decide +kernel) lb1_7118_10

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_7162_11 : CountBound 1 7162 11 := by
  exact fixE 1 false ew1_7162_2 (by decide +kernel) ew1_7160_8 (by decide +kernel) lb1_7160_10

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_8122_11 : CountBound 1 8122 11 := by
  exact fixE 7 false ew1_8122_128 (by decide +kernel) ew1_7994_2 (by decide +kernel) (transfer (s:=1) (a:=7994) (t:=1) (u:=7098) perm13 (by decide +kernel) (by decide +kernel) lb1_7098_10)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_14974_13 : CountBound 1 14974 13 := by
  let rs : List Row := [⟨1,false,4,11⟩, ⟨1,true,14848,0⟩, ⟨2,false,2,11⟩, ⟨2,true,14850,0⟩, ⟨3,false,6,11⟩, ⟨3,true,14854,0⟩, ⟨4,false,14,11⟩, ⟨4,true,14862,0⟩, ⟨5,false,30,11⟩, ⟨5,true,14878,0⟩, ⟨6,false,62,10⟩, ⟨6,true,14910,0⟩, ⟨9,false,126,10⟩, ⟨9,true,2,10⟩, ⟨11,false,638,10⟩, ⟨11,true,514,10⟩, ⟨12,false,2686,10⟩, ⟨12,true,2562,10⟩, ⟨13,false,6782,0⟩, ⟨13,true,6658,10⟩]
  apply rule_tables (rs:=rs) ?_ (by decide +kernel) ew1_14974_14974 ?_
  · unfold rs
    refine rows_cons ⟨ew1_14972_4, (transfer (s:=1) (a:=14972) (t:=1) (u:=14910) perm20 (by decide +kernel) (by decide +kernel) lb1_14910_11)⟩ ?_
    refine rows_cons ⟨ew3_14972_14848, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew1_14970_2, (transfer (s:=1) (a:=14970) (t:=1) (u:=14910) perm3 (by decide +kernel) (by decide +kernel) lb1_14910_11)⟩ ?_
    refine rows_cons ⟨ew5_14970_14850, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew1_14966_6, (transfer (s:=1) (a:=14966) (t:=1) (u:=14910) perm4 (by decide +kernel) (by decide +kernel) lb1_14910_11)⟩ ?_
    refine rows_cons ⟨ew9_14966_14854, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew1_14958_14, (transfer (s:=1) (a:=14958) (t:=1) (u:=14910) perm2 (by decide +kernel) (by decide +kernel) lb1_14910_11)⟩ ?_
    refine rows_cons ⟨ew17_14958_14862, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew1_14942_30, (transfer (s:=1) (a:=14942) (t:=1) (u:=14910) perm1 (by decide +kernel) (by decide +kernel) lb1_14910_11)⟩ ?_
    refine rows_cons ⟨ew33_14942_14878, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew1_14910_62, lb1_14910_10⟩ ?_
    refine rows_cons ⟨ew65_14910_14910, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew1_14462_126, (transfer (s:=1) (a:=14462) (t:=1) (u:=6782) perm2 (by decide +kernel) (by decide +kernel) lb1_6782_10)⟩ ?_
    refine rows_cons ⟨ew513_14462_2, (transfer (s:=513) (a:=14462) (t:=132) (u:=3707) perm50 (by decide +kernel) (by decide +kernel) lb132_3707_10)⟩ ?_
    refine rows_cons ⟨ew1_12926_638, (transfer (s:=1) (a:=12926) (t:=1) (u:=6782) perm10 (by decide +kernel) (by decide +kernel) lb1_6782_10)⟩ ?_
    refine rows_cons ⟨ew2049_12926_514, (transfer (s:=2049) (a:=12926) (t:=132) (u:=3707) perm62 (by decide +kernel) (by decide +kernel) lb132_3707_10)⟩ ?_
    refine rows_cons ⟨ew1_10878_2686, (transfer (s:=1) (a:=10878) (t:=1) (u:=6782) perm8 (by decide +kernel) (by decide +kernel) lb1_6782_10)⟩ ?_
    refine rows_cons ⟨ew4097_10878_2562, (transfer (s:=4097) (a:=10878) (t:=132) (u:=3707) perm60 (by decide +kernel) (by decide +kernel) lb132_3707_10)⟩ ?_
    refine rows_cons ⟨ew1_6782_6782, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew8193_6782_6658, (transfer (s:=8193) (a:=6782) (t:=132) (u:=3707) perm48 (by decide +kernel) (by decide +kernel) lb132_3707_10)⟩ ?_
    exact rows_nil _ _
  · unfold rs; decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_15038_11 : CountBound 1 15038 11 := by
  exact fixE 1 false ew1_15038_2 (by decide +kernel) ew1_15036_4 (by decide +kernel) (transfer (s:=1) (a:=15036) (t:=1) (u:=15030) perm8 (by decide +kernel) (by decide +kernel) lb1_15030_10)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_15094_11 : CountBound 1 15094 11 := by
  exact fixE 1 false ew1_15094_2 (by decide +kernel) ew1_15092_4 (by decide +kernel) lb1_15092_10

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_15094_12 : CountBound 1 15094 12 := by
  exact fixE 7 false ew1_15094_128 (by decide +kernel) ew1_14966_2 (by decide +kernel) (transfer (s:=1) (a:=14966) (t:=1) (u:=14910) perm4 (by decide +kernel) (by decide +kernel) lb1_14910_11)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_15262_11 : CountBound 1 15262 11 := by
  exact fixE 3 false ew1_15262_8 (by decide +kernel) ew1_15254_2 (by decide +kernel) lb1_15254_10

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_15286_11 : CountBound 1 15286 11 := by
  exact fixE 5 false ew1_15286_32 (by decide +kernel) ew1_15254_2 (by decide +kernel) lb1_15254_10

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_15290_11 : CountBound 1 15290 11 := by
  exact fixE 7 false ew1_15290_128 (by decide +kernel) ew1_15162_2 (by decide +kernel) (transfer (s:=1) (a:=15162) (t:=1) (u:=15092) perm4 (by decide +kernel) (by decide +kernel) lb1_15092_10)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_3959_11 : CountBound 128 3959 11 := by
  exact fixE 0 false ew128_3959_1 (by decide +kernel) ew128_3958_2 (by decide +kernel) lb128_3958_10

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_3966_11 : CountBound 128 3966 11 := by
  exact fixE 1 false ew128_3966_2 (by decide +kernel) ew128_3964_4 (by decide +kernel) (transfer (s:=128) (a:=3964) (t:=128) (u:=3958) perm8 (by decide +kernel) (by decide +kernel) lb128_3958_10)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_3966_12 : CountBound 128 3966 12 := by
  exact fixE 1 false ew128_3966_2 (by decide +kernel) ew128_3964_4 (by decide +kernel) (transfer (s:=128) (a:=3964) (t:=128) (u:=3958) perm8 (by decide +kernel) (by decide +kernel) lb128_3958_11)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_7487_11 : CountBound 128 7487 11 := by
  exact fixE 0 false ew128_7487_1 (by decide +kernel) ew128_7486_2 (by decide +kernel) (transfer (s:=128) (a:=7486) (t:=128) (u:=7479) perm77 (by decide +kernel) (by decide +kernel) lb128_7479_10)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_7543_11 : CountBound 128 7543 11 := by
  exact fixE 0 false ew128_7543_1 (by decide +kernel) ew128_7542_2 (by decide +kernel) lb128_7542_10

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_7543_12 : CountBound 128 7543 12 := by
  exact fixE 0 false ew128_7543_1 (by decide +kernel) ew128_7542_2 (by decide +kernel) lb128_7542_11

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_7991_11 : CountBound 128 7991 11 := by
  exact fixE 0 false ew128_7991_1 (by decide +kernel) ew128_7990_2 (by decide +kernel) lb128_7990_10

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_7997_11 : CountBound 128 7997 11 := by
  exact fixE 0 false ew128_7997_1 (by decide +kernel) ew128_7996_4 (by decide +kernel) (transfer (s:=128) (a:=7996) (t:=128) (u:=7989) perm77 (by decide +kernel) (by decide +kernel) lb128_7989_10)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_8039_11 : CountBound 128 8039 11 := by
  exact fixE 0 false ew128_8039_1 (by decide +kernel) ew128_8038_2 (by decide +kernel) lb128_8038_10

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_8053_11 : CountBound 128 8053 11 := by
  exact fixE 0 false ew128_8053_1 (by decide +kernel) ew128_8052_4 (by decide +kernel) lb128_8052_10

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_8054_11 : CountBound 128 8054 11 := by
  exact fixE 1 false ew128_8054_2 (by decide +kernel) ew128_8052_4 (by decide +kernel) lb128_8052_10

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_8054_12 : CountBound 128 8054 12 := by
  exact fixE 1 false ew128_8054_2 (by decide +kernel) ew128_8052_4 (by decide +kernel) lb128_8052_11

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_16244_13 : CountBound 128 16244 13 := by
  let rs : List Row := [⟨2,false,16,10⟩, ⟨2,true,16,10⟩, ⟨4,false,4,10⟩, ⟨4,true,4,10⟩, ⟨5,false,20,10⟩, ⟨5,true,20,10⟩, ⟨6,false,52,10⟩, ⟨6,true,52,10⟩, ⟨8,false,116,11⟩, ⟨8,true,116,0⟩, ⟨9,false,372,11⟩, ⟨9,true,372,0⟩, ⟨10,false,884,11⟩, ⟨10,true,884,0⟩, ⟨11,false,1908,11⟩, ⟨11,true,1908,0⟩, ⟨12,false,3956,11⟩, ⟨12,true,3956,0⟩, ⟨13,false,8052,0⟩, ⟨13,true,8052,0⟩]
  apply rule_tables (rs:=rs) ?_ (by decide +kernel) ew128_16244_16244 ?_
  · unfold rs
    refine rows_cons ⟨ew128_16240_16, (transfer (s:=128) (a:=16240) (t:=128) (u:=16180) perm3 (by decide +kernel) (by decide +kernel) lb128_16180_10)⟩ ?_
    refine rows_cons ⟨ew132_16240_16, lb132_16240_10⟩ ?_
    refine rows_cons ⟨ew128_16228_4, (transfer (s:=128) (a:=16228) (t:=128) (u:=16180) perm2 (by decide +kernel) (by decide +kernel) lb128_16180_10)⟩ ?_
    refine rows_cons ⟨ew144_16228_4, (transfer (s:=144) (a:=16228) (t:=132) (u:=16240) perm1 (by decide +kernel) (by decide +kernel) lb132_16240_10)⟩ ?_
    refine rows_cons ⟨ew128_16212_20, (transfer (s:=128) (a:=16212) (t:=128) (u:=16180) perm1 (by decide +kernel) (by decide +kernel) lb128_16180_10)⟩ ?_
    refine rows_cons ⟨ew160_16212_20, (transfer (s:=160) (a:=16212) (t:=132) (u:=16240) perm2 (by decide +kernel) (by decide +kernel) lb132_16240_10)⟩ ?_
    refine rows_cons ⟨ew128_16180_52, lb128_16180_10⟩ ?_
    refine rows_cons ⟨ew192_16180_52, (transfer (s:=192) (a:=16180) (t:=132) (u:=16240) perm3 (by decide +kernel) (by decide +kernel) lb132_16240_10)⟩ ?_
    refine rows_cons ⟨ew128_15988_116, (transfer (s:=128) (a:=15988) (t:=128) (u:=8052) perm24 (by decide +kernel) (by decide +kernel) lb128_8052_11)⟩ ?_
    refine rows_cons ⟨ew384_15988_116, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew128_15732_372, (transfer (s:=128) (a:=15732) (t:=128) (u:=8052) perm2 (by decide +kernel) (by decide +kernel) lb128_8052_11)⟩ ?_
    refine rows_cons ⟨ew640_15732_372, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew128_15220_884, (transfer (s:=128) (a:=15220) (t:=128) (u:=8052) perm26 (by decide +kernel) (by decide +kernel) lb128_8052_11)⟩ ?_
    refine rows_cons ⟨ew1152_15220_884, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew128_14196_1908, (transfer (s:=128) (a:=14196) (t:=128) (u:=8052) perm10 (by decide +kernel) (by decide +kernel) lb128_8052_11)⟩ ?_
    refine rows_cons ⟨ew2176_14196_1908, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew128_12148_3956, (transfer (s:=128) (a:=12148) (t:=128) (u:=8052) perm8 (by decide +kernel) (by decide +kernel) lb128_8052_11)⟩ ?_
    refine rows_cons ⟨ew4224_12148_3956, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew128_8052_8052, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew8320_8052_8052, (zero_bound _ _)⟩ ?_
    exact rows_nil _ _
  · unfold rs; decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_2047_13 : CountBound 0 2047 13 := by
  exact fixE 0 false ew0_2047_1 (by decide +kernel) ew0_2046_2 (by decide +kernel) lb0_2046_12

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_3839_13 : CountBound 0 3839 13 := by
  exact fix_one 2 false (by decide +kernel) lb0_3835_13

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_4031_14 : CountBound 0 4031 14 := by
  let rs : List Row := [⟨0,false,2,12⟩, ⟨0,true,2874,0⟩, ⟨1,false,1,11⟩, ⟨1,true,1,11⟩, ⟨2,false,315,11⟩, ⟨2,true,59,11⟩, ⟨3,false,3,11⟩, ⟨3,true,3,11⟩, ⟨4,false,11,11⟩, ⟨4,true,11,11⟩, ⟨5,false,27,11⟩, ⟨5,true,27,11⟩, ⟨7,false,63,12⟩, ⟨7,true,2879,0⟩, ⟨8,false,3771,11⟩, ⟨8,true,63,11⟩, ⟨9,false,191,11⟩, ⟨9,true,319,11⟩, ⟨10,false,703,11⟩, ⟨10,true,3007,0⟩, ⟨11,false,1727,11⟩, ⟨11,true,831,11⟩]
  apply rule_tables (rs:=rs) ?_ (by decide +kernel) ew0_4031_4031 ?_
  · unfold rs
    refine rows_cons ⟨ew0_4030_2, lb0_4030_12⟩ ?_
    refine rows_cons ⟨ew1_4030_2874, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_4029_1, (transfer (s:=0) (a:=4029) (t:=0) (u:=3999) perm17 (by decide +kernel) (by decide +kernel) lb0_3999_11)⟩ ?_
    refine rows_cons ⟨ew2_4029_1, (transfer (s:=2) (a:=4029) (t:=1) (u:=7102) perm73 (by decide +kernel) (by decide +kernel) lb1_7102_11)⟩ ?_
    refine rows_cons ⟨ew0_4027_315, lb0_4027_11⟩ ?_
    refine rows_cons ⟨ew4_4027_59, (transfer (s:=4) (a:=4027) (t:=1) (u:=15094) perm28 (by decide +kernel) (by decide +kernel) lb1_15094_11)⟩ ?_
    refine rows_cons ⟨ew0_4023_3, (transfer (s:=0) (a:=4023) (t:=0) (u:=3999) perm13 (by decide +kernel) (by decide +kernel) lb0_3999_11)⟩ ?_
    refine rows_cons ⟨ew8_4023_3, (transfer (s:=8) (a:=4023) (t:=1) (u:=7102) perm77 (by decide +kernel) (by decide +kernel) lb1_7102_11)⟩ ?_
    refine rows_cons ⟨ew0_4015_11, (transfer (s:=0) (a:=4015) (t:=0) (u:=3999) perm8 (by decide +kernel) (by decide +kernel) lb0_3999_11)⟩ ?_
    refine rows_cons ⟨ew16_4015_11, (transfer (s:=16) (a:=4015) (t:=1) (u:=7102) perm90 (by decide +kernel) (by decide +kernel) lb1_7102_11)⟩ ?_
    refine rows_cons ⟨ew0_3999_27, lb0_3999_11⟩ ?_
    refine rows_cons ⟨ew32_3999_27, (transfer (s:=32) (a:=3999) (t:=1) (u:=7102) perm82 (by decide +kernel) (by decide +kernel) lb1_7102_11)⟩ ?_
    refine rows_cons ⟨ew0_3903_63, (transfer (s:=0) (a:=3903) (t:=0) (u:=2046) perm29 (by decide +kernel) (by decide +kernel) lb0_2046_12)⟩ ?_
    refine rows_cons ⟨ew128_3903_2879, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_3775_3771, lb0_3775_11⟩ ?_
    refine rows_cons ⟨ew256_3775_63, (transfer (s:=256) (a:=3775) (t:=128) (u:=7543) perm4 (by decide +kernel) (by decide +kernel) lb128_7543_11)⟩ ?_
    refine rows_cons ⟨ew0_3519_191, (transfer (s:=0) (a:=3519) (t:=0) (u:=1983) perm8 (by decide +kernel) (by decide +kernel) lb0_1983_11)⟩ ?_
    refine rows_cons ⟨ew512_3519_319, (transfer (s:=512) (a:=3519) (t:=128) (u:=3966) perm149 (by decide +kernel) (by decide +kernel) lb128_3966_11)⟩ ?_
    refine rows_cons ⟨ew0_3007_703, (transfer (s:=0) (a:=3007) (t:=0) (u:=2046) perm42 (by decide +kernel) (by decide +kernel) lb0_2046_11)⟩ ?_
    refine rows_cons ⟨ew1024_3007_3007, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_1983_1727, lb0_1983_11⟩ ?_
    refine rows_cons ⟨ew2048_1983_831, (transfer (s:=2048) (a:=1983) (t:=128) (u:=3966) perm162 (by decide +kernel) (by decide +kernel) lb128_3966_11)⟩ ?_
    exact rows_nil _ _
  · unfold rs; decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_4063_13 : CountBound 0 4063 13 := by
  exact fixE 0 false ew0_4063_1 (by decide +kernel) ew0_4062_2 (by decide +kernel) (transfer (s:=0) (a:=4062) (t:=0) (u:=3999) perm162 (by decide +kernel) (by decide +kernel) lb0_3999_12)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_4063_14 : CountBound 0 4063 14 := by
  let rs : List Row := [⟨0,false,2,12⟩, ⟨0,true,1818,0⟩, ⟨1,false,1,11⟩, ⟨1,true,1,11⟩, ⟨2,false,259,11⟩, ⟨2,true,91,11⟩, ⟨3,false,87,11⟩, ⟨3,true,3,11⟩, ⟨4,false,7,11⟩, ⟨4,true,11,11⟩, ⟨6,false,23,12⟩, ⟨6,true,1819,0⟩, ⟨7,false,95,12⟩, ⟨7,true,1887,0⟩, ⟨8,false,3803,11⟩, ⟨8,true,31,11⟩, ⟨9,false,223,11⟩, ⟨9,true,287,11⟩, ⟨10,false,735,11⟩, ⟨10,true,799,11⟩, ⟨11,false,1759,11⟩, ⟨11,true,2015,0⟩]
  apply rule_tables (rs:=rs) ?_ (by decide +kernel) ew0_4063_4063 ?_
  · unfold rs
    refine rows_cons ⟨ew0_4062_2, (transfer (s:=0) (a:=4062) (t:=0) (u:=3999) perm162 (by decide +kernel) (by decide +kernel) lb0_3999_12)⟩ ?_
    refine rows_cons ⟨ew1_4062_1818, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_4061_1, (transfer (s:=0) (a:=4061) (t:=0) (u:=4047) perm162 (by decide +kernel) (by decide +kernel) lb0_4047_11)⟩ ?_
    refine rows_cons ⟨ew2_4061_1, (transfer (s:=2) (a:=4061) (t:=1) (u:=7162) perm73 (by decide +kernel) (by decide +kernel) lb1_7162_11)⟩ ?_
    refine rows_cons ⟨ew0_4059_259, lb0_4059_11⟩ ?_
    refine rows_cons ⟨ew4_4059_91, (transfer (s:=4) (a:=4059) (t:=1) (u:=15038) perm36 (by decide +kernel) (by decide +kernel) lb1_15038_11)⟩ ?_
    refine rows_cons ⟨ew0_4055_87, lb0_4055_11⟩ ?_
    refine rows_cons ⟨ew8_4055_3, (transfer (s:=8) (a:=4055) (t:=1) (u:=7134) perm77 (by decide +kernel) (by decide +kernel) lb1_7134_11)⟩ ?_
    refine rows_cons ⟨ew0_4047_7, lb0_4047_11⟩ ?_
    refine rows_cons ⟨ew16_4047_11, (transfer (s:=16) (a:=4047) (t:=1) (u:=7162) perm167 (by decide +kernel) (by decide +kernel) lb1_7162_11)⟩ ?_
    refine rows_cons ⟨ew0_3999_23, lb0_3999_12⟩ ?_
    refine rows_cons ⟨ew64_3999_1819, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_3935_95, (transfer (s:=0) (a:=3935) (t:=0) (u:=1983) perm29 (by decide +kernel) (by decide +kernel) lb0_1983_12)⟩ ?_
    refine rows_cons ⟨ew128_3935_1887, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_3807_3803, (transfer (s:=0) (a:=3807) (t:=0) (u:=3775) perm32 (by decide +kernel) (by decide +kernel) lb0_3775_11)⟩ ?_
    refine rows_cons ⟨ew256_3807_31, (transfer (s:=256) (a:=3807) (t:=128) (u:=7487) perm12 (by decide +kernel) (by decide +kernel) lb128_7487_11)⟩ ?_
    refine rows_cons ⟨ew0_3551_223, (transfer (s:=0) (a:=3551) (t:=0) (u:=2031) perm5 (by decide +kernel) (by decide +kernel) lb0_2031_11)⟩ ?_
    refine rows_cons ⟨ew512_3551_287, (transfer (s:=512) (a:=3551) (t:=128) (u:=3959) perm149 (by decide +kernel) (by decide +kernel) lb128_3959_11)⟩ ?_
    refine rows_cons ⟨ew0_3039_735, (transfer (s:=0) (a:=3039) (t:=0) (u:=2031) perm42 (by decide +kernel) (by decide +kernel) lb0_2031_11)⟩ ?_
    refine rows_cons ⟨ew1024_3039_799, (transfer (s:=1024) (a:=3039) (t:=128) (u:=3959) perm13 (by decide +kernel) (by decide +kernel) lb128_3959_11)⟩ ?_
    refine rows_cons ⟨ew0_2015_1759, (transfer (s:=0) (a:=2015) (t:=0) (u:=1983) perm1 (by decide +kernel) (by decide +kernel) lb0_1983_11)⟩ ?_
    refine rows_cons ⟨ew2048_2015_2015, (zero_bound _ _)⟩ ?_
    exact rows_nil _ _
  · unfold rs; decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_4091_13 : CountBound 0 4091 13 := by
  exact fixE 0 false ew0_4091_1 (by decide +kernel) ew0_4090_2 (by decide +kernel) (transfer (s:=0) (a:=4090) (t:=0) (u:=4027) perm149 (by decide +kernel) (by decide +kernel) lb0_4027_12)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_8095_14 : CountBound 0 8095 14 := by
  let rs : List Row := [⟨0,false,2,12⟩, ⟨0,true,7958,0⟩, ⟨1,false,7581,11⟩, ⟨1,true,1,11⟩, ⟨2,false,1,11⟩, ⟨2,true,3,11⟩, ⟨3,false,5,12⟩, ⟨3,true,7959,0⟩, ⟨4,false,13,11⟩, ⟨4,true,7,11⟩, ⟨7,false,29,12⟩, ⟨7,true,7455,0⟩, ⟨8,false,157,11⟩, ⟨8,true,23,11⟩, ⟨9,false,7583,0⟩, ⟨9,true,407,11⟩, ⟨10,false,413,11⟩, ⟨10,true,791,11⟩, ⟨11,false,1437,11⟩, ⟨11,true,1815,11⟩, ⟨12,false,3485,11⟩, ⟨12,true,3863,11⟩]
  apply rule_tables (rs:=rs) ?_ (by decide +kernel) ew0_8095_8095 ?_
  · unfold rs
    refine rows_cons ⟨ew0_8094_2, (transfer (s:=0) (a:=8094) (t:=0) (u:=8087) perm76 (by decide +kernel) (by decide +kernel) lb0_8087_12)⟩ ?_
    refine rows_cons ⟨ew1_8094_7958, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_8093_7581, lb0_8093_11⟩ ?_
    refine rows_cons ⟨ew2_8093_1, (transfer (s:=2) (a:=8093) (t:=1) (u:=15290) perm25 (by decide +kernel) (by decide +kernel) lb1_15290_11)⟩ ?_
    refine rows_cons ⟨ew0_8091_1, (transfer (s:=0) (a:=8091) (t:=0) (u:=8079) perm1 (by decide +kernel) (by decide +kernel) lb0_8079_11)⟩ ?_
    refine rows_cons ⟨ew4_8091_3, (transfer (s:=4) (a:=8091) (t:=1) (u:=15286) perm36 (by decide +kernel) (by decide +kernel) lb1_15286_11)⟩ ?_
    refine rows_cons ⟨ew0_8087_5, lb0_8087_12⟩ ?_
    refine rows_cons ⟨ew8_8087_7959, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_8079_13, lb0_8079_11⟩ ?_
    refine rows_cons ⟨ew16_8079_7, (transfer (s:=16) (a:=8079) (t:=1) (u:=15286) perm38 (by decide +kernel) (by decide +kernel) lb1_15286_11)⟩ ?_
    refine rows_cons ⟨ew0_7967_29, (transfer (s:=0) (a:=7967) (t:=0) (u:=4030) perm29 (by decide +kernel) (by decide +kernel) lb0_4030_12)⟩ ?_
    refine rows_cons ⟨ew128_7967_7455, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_7839_157, (transfer (s:=0) (a:=7839) (t:=0) (u:=3999) perm76 (by decide +kernel) (by decide +kernel) lb0_3999_11)⟩ ?_
    refine rows_cons ⟨ew256_7839_23, (transfer (s:=256) (a:=7839) (t:=128) (u:=7991) perm12 (by decide +kernel) (by decide +kernel) lb128_7991_11)⟩ ?_
    refine rows_cons ⟨ew0_7583_7583, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew512_7583_407, (transfer (s:=512) (a:=7583) (t:=128) (u:=8054) perm125 (by decide +kernel) (by decide +kernel) lb128_8054_11)⟩ ?_
    refine rows_cons ⟨ew0_7071_413, (transfer (s:=0) (a:=7071) (t:=0) (u:=3999) perm77 (by decide +kernel) (by decide +kernel) lb0_3999_11)⟩ ?_
    refine rows_cons ⟨ew1024_7071_791, (transfer (s:=1024) (a:=7071) (t:=128) (u:=7991) perm13 (by decide +kernel) (by decide +kernel) lb128_7991_11)⟩ ?_
    refine rows_cons ⟨ew0_6047_1437, (transfer (s:=0) (a:=6047) (t:=0) (u:=3999) perm1 (by decide +kernel) (by decide +kernel) lb0_3999_11)⟩ ?_
    refine rows_cons ⟨ew2048_6047_1815, (transfer (s:=2048) (a:=6047) (t:=128) (u:=7991) perm137 (by decide +kernel) (by decide +kernel) lb128_7991_11)⟩ ?_
    refine rows_cons ⟨ew0_3999_3485, lb0_3999_11⟩ ?_
    refine rows_cons ⟨ew4096_3999_3863, (transfer (s:=4096) (a:=3999) (t:=128) (u:=7991) perm136 (by decide +kernel) (by decide +kernel) lb128_7991_11)⟩ ?_
    exact rows_nil _ _
  · unfold rs; decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_8111_13 : CountBound 0 8111 13 := by
  exact fixE 0 false ew0_8111_1 (by decide +kernel) ew0_8110_2 (by decide +kernel) (transfer (s:=0) (a:=8110) (t:=0) (u:=8079) perm129 (by decide +kernel) (by decide +kernel) lb0_8079_12)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_8111_14 : CountBound 0 8111 14 := by
  let rs : List Row := [⟨0,false,2,12⟩, ⟨0,true,3854,0⟩, ⟨1,false,1,11⟩, ⟨1,true,1,11⟩, ⟨2,false,3,11⟩, ⟨2,true,3,11⟩, ⟨3,false,6055,11⟩, ⟨3,true,7,11⟩, ⟨5,false,7,12⟩, ⟨5,true,3855,0⟩, ⟨7,false,39,12⟩, ⟨7,true,1839,0⟩, ⟨8,false,167,11⟩, ⟨8,true,15,11⟩, ⟨9,false,423,11⟩, ⟨9,true,271,11⟩, ⟨10,false,935,11⟩, ⟨10,true,783,11⟩, ⟨11,false,6063,0⟩, ⟨11,true,6031,11⟩, ⟨12,false,1959,12⟩, ⟨12,true,1967,0⟩]
  apply rule_tables (rs:=rs) ?_ (by decide +kernel) ew0_8111_8111 ?_
  · unfold rs
    refine rows_cons ⟨ew0_8110_2, (transfer (s:=0) (a:=8110) (t:=0) (u:=8079) perm129 (by decide +kernel) (by decide +kernel) lb0_8079_12)⟩ ?_
    refine rows_cons ⟨ew1_8110_3854, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_8109_1, (transfer (s:=0) (a:=8109) (t:=0) (u:=8107) perm129 (by decide +kernel) (by decide +kernel) lb0_8107_11)⟩ ?_
    refine rows_cons ⟨ew2_8109_1, (transfer (s:=2) (a:=8109) (t:=1) (u:=15262) perm73 (by decide +kernel) (by decide +kernel) lb1_15262_11)⟩ ?_
    refine rows_cons ⟨ew0_8107_3, lb0_8107_11⟩ ?_
    refine rows_cons ⟨ew4_8107_3, (transfer (s:=4) (a:=8107) (t:=1) (u:=15262) perm60 (by decide +kernel) (by decide +kernel) lb1_15262_11)⟩ ?_
    refine rows_cons ⟨ew0_8103_6055, (transfer (s:=0) (a:=8103) (t:=0) (u:=8093) perm6 (by decide +kernel) (by decide +kernel) lb0_8093_11)⟩ ?_
    refine rows_cons ⟨ew8_8103_7, (transfer (s:=8) (a:=8103) (t:=1) (u:=8122) perm77 (by decide +kernel) (by decide +kernel) lb1_8122_11)⟩ ?_
    refine rows_cons ⟨ew0_8079_7, lb0_8079_12⟩ ?_
    refine rows_cons ⟨ew32_8079_3855, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_7983_39, (transfer (s:=0) (a:=7983) (t:=0) (u:=3999) perm105 (by decide +kernel) (by decide +kernel) lb0_3999_12)⟩ ?_
    refine rows_cons ⟨ew128_7983_1839, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_7855_167, (transfer (s:=0) (a:=7855) (t:=0) (u:=4047) perm32 (by decide +kernel) (by decide +kernel) lb0_4047_11)⟩ ?_
    refine rows_cons ⟨ew256_7855_15, (transfer (s:=256) (a:=7855) (t:=128) (u:=8039) perm4 (by decide +kernel) (by decide +kernel) lb128_8039_11)⟩ ?_
    refine rows_cons ⟨ew0_7599_423, (transfer (s:=0) (a:=7599) (t:=0) (u:=4047) perm152 (by decide +kernel) (by decide +kernel) lb0_4047_11)⟩ ?_
    refine rows_cons ⟨ew512_7599_271, (transfer (s:=512) (a:=7599) (t:=128) (u:=8039) perm125 (by decide +kernel) (by decide +kernel) lb128_8039_11)⟩ ?_
    refine rows_cons ⟨ew0_7087_935, (transfer (s:=0) (a:=7087) (t:=0) (u:=4027) perm34 (by decide +kernel) (by decide +kernel) lb0_4027_11)⟩ ?_
    refine rows_cons ⟨ew1024_7087_783, (transfer (s:=1024) (a:=7087) (t:=128) (u:=7997) perm13 (by decide +kernel) (by decide +kernel) lb128_7997_11)⟩ ?_
    refine rows_cons ⟨ew0_6063_6063, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew2048_6063_6031, (transfer (s:=2048) (a:=6063) (t:=128) (u:=8053) perm137 (by decide +kernel) (by decide +kernel) lb128_8053_11)⟩ ?_
    refine rows_cons ⟨ew0_4015_1959, (transfer (s:=0) (a:=4015) (t:=0) (u:=3999) perm8 (by decide +kernel) (by decide +kernel) lb0_3999_12)⟩ ?_
    refine rows_cons ⟨ew4096_4015_1967, (zero_bound _ _)⟩ ?_
    exact rows_nil _ _
  · unfold rs; decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_15102_13 : CountBound 1 15102 13 := by
  exact fixE 1 false ew1_15102_2 (by decide +kernel) ew1_15100_4 (by decide +kernel) (transfer (s:=1) (a:=15100) (t:=1) (u:=15094) perm8 (by decide +kernel) (by decide +kernel) lb1_15094_12)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_15102_14 : CountBound 1 15102 14 := by
  exact fixE 7 false ew1_15102_128 (by decide +kernel) ew1_14974_2 (by decide +kernel) lb1_14974_13

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_15294_13 : CountBound 1 15294 13 := by
  exact fixE 7 false ew1_15294_128 (by decide +kernel) ew1_15166_2 (by decide +kernel) (transfer (s:=1) (a:=15166) (t:=1) (u:=15094) perm4 (by decide +kernel) (by decide +kernel) lb1_15094_12)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_3967_13 : CountBound 128 3967 13 := by
  exact fixE 0 false ew128_3967_1 (by decide +kernel) ew128_3966_2 (by decide +kernel) lb128_3966_12

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_7551_13 : CountBound 128 7551 13 := by
  exact fixE 0 false ew128_7551_1 (by decide +kernel) ew128_7550_2 (by decide +kernel) (transfer (s:=128) (a:=7550) (t:=128) (u:=7543) perm76 (by decide +kernel) (by decide +kernel) lb128_7543_12)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_8055_13 : CountBound 128 8055 13 := by
  exact fixE 0 false ew128_8055_1 (by decide +kernel) ew128_8054_2 (by decide +kernel) lb128_8054_12

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_16245_14 : CountBound 128 16245 14 := by
  exact fixE 0 false ew128_16245_1 (by decide +kernel) ew128_16244_4 (by decide +kernel) lb128_16244_13

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_4095_16 : CountBound 0 4095 16 := by
  let rs : List Row := [⟨0,false,2,14⟩, ⟨0,true,3968,0⟩, ⟨1,false,1,14⟩, ⟨1,true,3973,0⟩, ⟨2,false,379,13⟩, ⟨2,true,65,13⟩, ⟨3,false,3,14⟩, ⟨3,true,3975,0⟩, ⟨4,false,11,14⟩, ⟨4,true,3983,0⟩, ⟨5,false,27,14⟩, ⟨5,true,3999,0⟩, ⟨6,false,59,14⟩, ⟨6,true,4027,0⟩, ⟨7,false,127,13⟩, ⟨7,true,5,13⟩, ⟨8,false,3835,13⟩, ⟨8,true,133,13⟩, ⟨9,false,255,13⟩, ⟨9,true,389,13⟩, ⟨10,false,767,13⟩, ⟨10,true,901,13⟩, ⟨11,false,1791,13⟩, ⟨11,true,1925,13⟩]
  apply rule_tables (rs:=rs) ?_ (by decide +kernel) ew0_4095_4095 ?_
  · unfold rs
    refine rows_cons ⟨ew0_4094_2, (transfer (s:=0) (a:=4094) (t:=0) (u:=4031) perm149 (by decide +kernel) (by decide +kernel) lb0_4031_14)⟩ ?_
    refine rows_cons ⟨ew1_4094_3968, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_4093_1, (transfer (s:=0) (a:=4093) (t:=0) (u:=4063) perm17 (by decide +kernel) (by decide +kernel) lb0_4063_14)⟩ ?_
    refine rows_cons ⟨ew2_4093_3973, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_4091_379, lb0_4091_13⟩ ?_
    refine rows_cons ⟨ew4_4091_65, (transfer (s:=4) (a:=4091) (t:=1) (u:=15102) perm28 (by decide +kernel) (by decide +kernel) lb1_15102_13)⟩ ?_
    refine rows_cons ⟨ew0_4087_3, (transfer (s:=0) (a:=4087) (t:=0) (u:=4063) perm13 (by decide +kernel) (by decide +kernel) lb0_4063_14)⟩ ?_
    refine rows_cons ⟨ew8_4087_3975, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_4079_11, (transfer (s:=0) (a:=4079) (t:=0) (u:=4063) perm8 (by decide +kernel) (by decide +kernel) lb0_4063_14)⟩ ?_
    refine rows_cons ⟨ew16_4079_3983, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_4063_27, lb0_4063_14⟩ ?_
    refine rows_cons ⟨ew32_4063_3999, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_4031_59, lb0_4031_14⟩ ?_
    refine rows_cons ⟨ew64_4031_4027, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_3967_127, (transfer (s:=0) (a:=3967) (t:=0) (u:=2047) perm29 (by decide +kernel) (by decide +kernel) lb0_2047_13)⟩ ?_
    refine rows_cons ⟨ew128_3967_5, lb128_3967_13⟩ ?_
    refine rows_cons ⟨ew0_3839_3835, lb0_3839_13⟩ ?_
    refine rows_cons ⟨ew256_3839_133, (transfer (s:=256) (a:=3839) (t:=128) (u:=7551) perm4 (by decide +kernel) (by decide +kernel) lb128_7551_13)⟩ ?_
    refine rows_cons ⟨ew0_3583_255, (transfer (s:=0) (a:=3583) (t:=0) (u:=2047) perm5 (by decide +kernel) (by decide +kernel) lb0_2047_13)⟩ ?_
    refine rows_cons ⟨ew512_3583_389, (transfer (s:=512) (a:=3583) (t:=128) (u:=3967) perm149 (by decide +kernel) (by decide +kernel) lb128_3967_13)⟩ ?_
    refine rows_cons ⟨ew0_3071_767, (transfer (s:=0) (a:=3071) (t:=0) (u:=2047) perm42 (by decide +kernel) (by decide +kernel) lb0_2047_13)⟩ ?_
    refine rows_cons ⟨ew1024_3071_901, (transfer (s:=1024) (a:=3071) (t:=128) (u:=3967) perm13 (by decide +kernel) (by decide +kernel) lb128_3967_13)⟩ ?_
    refine rows_cons ⟨ew0_2047_1791, lb0_2047_13⟩ ?_
    refine rows_cons ⟨ew2048_2047_1925, (transfer (s:=2048) (a:=2047) (t:=128) (u:=3967) perm162 (by decide +kernel) (by decide +kernel) lb128_3967_13)⟩ ?_
    exact rows_nil _ _
  · unfold rs; decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_8127_16 : CountBound 0 8127 16 := by
  let rs : List Row := [⟨0,false,2,14⟩, ⟨0,true,2838,0⟩, ⟨1,false,1,13⟩, ⟨1,true,1,13⟩, ⟨2,false,3,13⟩, ⟨2,true,3,13⟩, ⟨3,false,7,14⟩, ⟨3,true,2839,0⟩, ⟨4,false,15,13⟩, ⟨4,true,7,13⟩, ⟨5,false,31,14⟩, ⟨5,true,2847,0⟩, ⟨7,false,63,14⟩, ⟨7,true,2879,0⟩, ⟨8,false,191,13⟩, ⟨8,true,23,13⟩, ⟨9,false,447,13⟩, ⟨9,true,279,13⟩, ⟨10,false,959,14⟩, ⟨10,true,3007,0⟩, ⟨11,false,1983,13⟩, ⟨11,true,791,13⟩, ⟨12,false,4031,0⟩, ⟨12,true,4031,0⟩]
  apply rule_tables (rs:=rs) ?_ (by decide +kernel) ew0_8127_8127 ?_
  · unfold rs
    refine rows_cons ⟨ew0_8126_2, (transfer (s:=0) (a:=8126) (t:=0) (u:=8095) perm129 (by decide +kernel) (by decide +kernel) lb0_8095_14)⟩ ?_
    refine rows_cons ⟨ew1_8126_2838, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_8125_1, (transfer (s:=0) (a:=8125) (t:=0) (u:=8111) perm13 (by decide +kernel) (by decide +kernel) lb0_8111_13)⟩ ?_
    refine rows_cons ⟨ew2_8125_1, (transfer (s:=2) (a:=8125) (t:=1) (u:=15294) perm26 (by decide +kernel) (by decide +kernel) lb1_15294_13)⟩ ?_
    refine rows_cons ⟨ew0_8123_3, (transfer (s:=0) (a:=8123) (t:=0) (u:=8111) perm77 (by decide +kernel) (by decide +kernel) lb0_8111_13)⟩ ?_
    refine rows_cons ⟨ew4_8123_3, (transfer (s:=4) (a:=8123) (t:=1) (u:=15294) perm60 (by decide +kernel) (by decide +kernel) lb1_15294_13)⟩ ?_
    refine rows_cons ⟨ew0_8119_7, (transfer (s:=0) (a:=8119) (t:=0) (u:=8095) perm6 (by decide +kernel) (by decide +kernel) lb0_8095_14)⟩ ?_
    refine rows_cons ⟨ew8_8119_2839, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_8111_15, lb0_8111_13⟩ ?_
    refine rows_cons ⟨ew16_8111_7, (transfer (s:=16) (a:=8111) (t:=1) (u:=15294) perm38 (by decide +kernel) (by decide +kernel) lb1_15294_13)⟩ ?_
    refine rows_cons ⟨ew0_8095_31, lb0_8095_14⟩ ?_
    refine rows_cons ⟨ew32_8095_2847, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_7999_63, (transfer (s:=0) (a:=7999) (t:=0) (u:=4031) perm30 (by decide +kernel) (by decide +kernel) lb0_4031_14)⟩ ?_
    refine rows_cons ⟨ew128_7999_2879, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_7871_191, (transfer (s:=0) (a:=7871) (t:=0) (u:=4063) perm76 (by decide +kernel) (by decide +kernel) lb0_4063_13)⟩ ?_
    refine rows_cons ⟨ew256_7871_23, (transfer (s:=256) (a:=7871) (t:=128) (u:=8055) perm4 (by decide +kernel) (by decide +kernel) lb128_8055_13)⟩ ?_
    refine rows_cons ⟨ew0_7615_447, (transfer (s:=0) (a:=7615) (t:=0) (u:=4063) perm6 (by decide +kernel) (by decide +kernel) lb0_4063_13)⟩ ?_
    refine rows_cons ⟨ew512_7615_279, (transfer (s:=512) (a:=7615) (t:=128) (u:=8055) perm125 (by decide +kernel) (by decide +kernel) lb128_8055_13)⟩ ?_
    refine rows_cons ⟨ew0_7103_959, (transfer (s:=0) (a:=7103) (t:=0) (u:=4031) perm34 (by decide +kernel) (by decide +kernel) lb0_4031_14)⟩ ?_
    refine rows_cons ⟨ew1024_7103_3007, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_6079_1983, (transfer (s:=0) (a:=6079) (t:=0) (u:=4063) perm1 (by decide +kernel) (by decide +kernel) lb0_4063_13)⟩ ?_
    refine rows_cons ⟨ew2048_6079_791, (transfer (s:=2048) (a:=6079) (t:=128) (u:=8055) perm137 (by decide +kernel) (by decide +kernel) lb128_8055_13)⟩ ?_
    refine rows_cons ⟨ew0_4031_4031, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew4096_4031_4031, (zero_bound _ _)⟩ ?_
    exact rows_nil _ _
  · unfold rs; decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_8175_15 : CountBound 0 8175 15 := by
  exact fixE 0 false ew0_8175_1 (by decide +kernel) ew0_8174_2 (by decide +kernel) (transfer (s:=0) (a:=8174) (t:=0) (u:=8111) perm149 (by decide +kernel) (by decide +kernel) lb0_8111_14)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_15358_15 : CountBound 1 15358 15 := by
  exact fixE 7 false ew1_15358_128 (by decide +kernel) ew1_15230_2 (by decide +kernel) (transfer (s:=1) (a:=15230) (t:=1) (u:=15102) perm4 (by decide +kernel) (by decide +kernel) lb1_15102_14)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_16247_15 : CountBound 128 16247 15 := by
  exact fixE 0 false ew128_16247_1 (by decide +kernel) ew128_16246_2 (by decide +kernel) (transfer (s:=128) (a:=16246) (t:=128) (u:=16245) perm24 (by decide +kernel) (by decide +kernel) lb128_16245_14)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_8191_18 : CountBound 0 8191 18 := by
  let rs : List Row := [⟨0,false,2,16⟩, ⟨0,true,22,0⟩, ⟨1,false,1,15⟩, ⟨1,true,1,15⟩, ⟨2,false,3,15⟩, ⟨2,true,3,15⟩, ⟨3,false,7,16⟩, ⟨3,true,23,0⟩, ⟨4,false,15,15⟩, ⟨4,true,7,15⟩, ⟨5,false,31,16⟩, ⟨5,true,31,0⟩, ⟨6,false,63,16⟩, ⟨6,true,63,0⟩, ⟨7,false,127,16⟩, ⟨7,true,127,0⟩, ⟨8,false,255,16⟩, ⟨8,true,255,0⟩, ⟨9,false,511,16⟩, ⟨9,true,511,0⟩, ⟨10,false,1023,16⟩, ⟨10,true,1023,0⟩, ⟨11,false,2047,16⟩, ⟨11,true,2047,0⟩, ⟨12,false,4095,0⟩, ⟨12,true,4095,0⟩]
  apply rule_tables (rs:=rs) ?_ (by decide +kernel) ew0_8191_8191 ?_
  · unfold rs
    refine rows_cons ⟨ew0_8190_2, (transfer (s:=0) (a:=8190) (t:=0) (u:=8127) perm149 (by decide +kernel) (by decide +kernel) lb0_8127_16)⟩ ?_
    refine rows_cons ⟨ew1_8190_22, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_8189_1, (transfer (s:=0) (a:=8189) (t:=0) (u:=8175) perm12 (by decide +kernel) (by decide +kernel) lb0_8175_15)⟩ ?_
    refine rows_cons ⟨ew2_8189_1, (transfer (s:=2) (a:=8189) (t:=1) (u:=15358) perm25 (by decide +kernel) (by decide +kernel) lb1_15358_15)⟩ ?_
    refine rows_cons ⟨ew0_8187_3, (transfer (s:=0) (a:=8187) (t:=0) (u:=8175) perm1 (by decide +kernel) (by decide +kernel) lb0_8175_15)⟩ ?_
    refine rows_cons ⟨ew4_8187_3, (transfer (s:=4) (a:=8187) (t:=1) (u:=15358) perm36 (by decide +kernel) (by decide +kernel) lb1_15358_15)⟩ ?_
    refine rows_cons ⟨ew0_8183_7, (transfer (s:=0) (a:=8183) (t:=0) (u:=8127) perm4 (by decide +kernel) (by decide +kernel) lb0_8127_16)⟩ ?_
    refine rows_cons ⟨ew8_8183_23, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_8175_15, lb0_8175_15⟩ ?_
    refine rows_cons ⟨ew16_8175_7, (transfer (s:=16) (a:=8175) (t:=1) (u:=15358) perm38 (by decide +kernel) (by decide +kernel) lb1_15358_15)⟩ ?_
    refine rows_cons ⟨ew0_8159_31, (transfer (s:=0) (a:=8159) (t:=0) (u:=8127) perm1 (by decide +kernel) (by decide +kernel) lb0_8127_16)⟩ ?_
    refine rows_cons ⟨ew32_8159_31, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_8127_63, lb0_8127_16⟩ ?_
    refine rows_cons ⟨ew64_8127_63, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_8063_127, (transfer (s:=0) (a:=8063) (t:=0) (u:=4095) perm29 (by decide +kernel) (by decide +kernel) lb0_4095_16)⟩ ?_
    refine rows_cons ⟨ew128_8063_127, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_7935_255, (transfer (s:=0) (a:=7935) (t:=0) (u:=4095) perm32 (by decide +kernel) (by decide +kernel) lb0_4095_16)⟩ ?_
    refine rows_cons ⟨ew256_7935_255, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_7679_511, (transfer (s:=0) (a:=7679) (t:=0) (u:=4095) perm4 (by decide +kernel) (by decide +kernel) lb0_4095_16)⟩ ?_
    refine rows_cons ⟨ew512_7679_511, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_7167_1023, (transfer (s:=0) (a:=7167) (t:=0) (u:=4095) perm34 (by decide +kernel) (by decide +kernel) lb0_4095_16)⟩ ?_
    refine rows_cons ⟨ew1024_7167_1023, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_6143_2047, (transfer (s:=0) (a:=6143) (t:=0) (u:=4095) perm1 (by decide +kernel) (by decide +kernel) lb0_4095_16)⟩ ?_
    refine rows_cons ⟨ew2048_6143_2047, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew0_4095_4095, (zero_bound _ _)⟩ ?_
    refine rows_cons ⟨ew4096_4095_4095, (zero_bound _ _)⟩ ?_
    exact rows_nil _ _
  · unfold rs; decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb0_16319_17 : CountBound 0 16319 17 := by
  exact fixE 7 false ew0_16319_128 (by decide +kernel) ew0_16191_1 (by decide +kernel) (transfer (s:=0) (a:=16191) (t:=0) (u:=8127) perm30 (by decide +kernel) (by decide +kernel) lb0_8127_16)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb1_16382_16 : CountBound 1 16382 16 := by
  exact fixE 7 false ew1_16382_128 (by decide +kernel) ew1_16254_2 (by decide +kernel) (transfer (s:=1) (a:=16254) (t:=1) (u:=15358) perm12 (by decide +kernel) (by decide +kernel) lb1_15358_15)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem lb128_16255_16 : CountBound 128 16255 16 := by
  exact fixE 0 false ew128_16255_1 (by decide +kernel) ew128_16254_2 (by decide +kernel) (transfer (s:=128) (a:=16254) (t:=128) (u:=16247) perm72 (by decide +kernel) (by decide +kernel) lb128_16247_15)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem root_bound_0 (i : I) : CountBound (added 0 i false) (dropped 16383 i) 17 := by
  have split_i : ∀ i : I, i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 := by decide +kernel
  rcases split_i i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact (transfer (s:=0) (a:=16382) (t:=0) (u:=16319) perm144 (by decide +kernel) (by decide +kernel) lb0_16319_17)
  · exact (transfer (s:=0) (a:=16381) (t:=0) (u:=16319) perm20 (by decide +kernel) (by decide +kernel) lb0_16319_17)
  · exact (transfer (s:=0) (a:=16379) (t:=0) (u:=16319) perm3 (by decide +kernel) (by decide +kernel) lb0_16319_17)
  · exact (transfer (s:=0) (a:=16375) (t:=0) (u:=16319) perm4 (by decide +kernel) (by decide +kernel) lb0_16319_17)
  · exact (transfer (s:=0) (a:=16367) (t:=0) (u:=16319) perm2 (by decide +kernel) (by decide +kernel) lb0_16319_17)
  · exact (transfer (s:=0) (a:=16351) (t:=0) (u:=16319) perm1 (by decide +kernel) (by decide +kernel) lb0_16319_17)
  · exact lb0_16319_17
  · exact weaken (transfer (s:=0) (a:=16255) (t:=0) (u:=8191) perm28 (by decide +kernel) (by decide +kernel) lb0_8191_18) (by decide +kernel)
  · exact weaken (transfer (s:=0) (a:=16127) (t:=0) (u:=8191) perm24 (by decide +kernel) (by decide +kernel) lb0_8191_18) (by decide +kernel)
  · exact weaken (transfer (s:=0) (a:=15871) (t:=0) (u:=8191) perm2 (by decide +kernel) (by decide +kernel) lb0_8191_18) (by decide +kernel)
  · exact weaken (transfer (s:=0) (a:=15359) (t:=0) (u:=8191) perm26 (by decide +kernel) (by decide +kernel) lb0_8191_18) (by decide +kernel)
  · exact weaken (transfer (s:=0) (a:=14335) (t:=0) (u:=8191) perm10 (by decide +kernel) (by decide +kernel) lb0_8191_18) (by decide +kernel)
  · exact weaken (transfer (s:=0) (a:=12287) (t:=0) (u:=8191) perm8 (by decide +kernel) (by decide +kernel) lb0_8191_18) (by decide +kernel)
  · exact weaken lb0_8191_18 (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem root_bound_1 (i : I) : CountBound (added 0 i true) (dropped 16383 i) 16 := by
  have split_i : ∀ i : I, i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 := by decide +kernel
  rcases split_i i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact lb1_16382_16
  · exact (transfer (s:=2) (a:=16381) (t:=1) (u:=16382) perm24 (by decide +kernel) (by decide +kernel) lb1_16382_16)
  · exact (transfer (s:=4) (a:=16379) (t:=1) (u:=16382) perm28 (by decide +kernel) (by decide +kernel) lb1_16382_16)
  · exact (transfer (s:=8) (a:=16375) (t:=1) (u:=16382) perm32 (by decide +kernel) (by decide +kernel) lb1_16382_16)
  · exact (transfer (s:=16) (a:=16367) (t:=1) (u:=16382) perm31 (by decide +kernel) (by decide +kernel) lb1_16382_16)
  · exact (transfer (s:=32) (a:=16351) (t:=1) (u:=16382) perm30 (by decide +kernel) (by decide +kernel) lb1_16382_16)
  · exact (transfer (s:=64) (a:=16319) (t:=1) (u:=16382) perm29 (by decide +kernel) (by decide +kernel) lb1_16382_16)
  · exact lb128_16255_16
  · exact (transfer (s:=256) (a:=16127) (t:=128) (u:=16255) perm4 (by decide +kernel) (by decide +kernel) lb128_16255_16)
  · exact (transfer (s:=512) (a:=15871) (t:=128) (u:=16255) perm50 (by decide +kernel) (by decide +kernel) lb128_16255_16)
  · exact (transfer (s:=1024) (a:=15359) (t:=128) (u:=16255) perm6 (by decide +kernel) (by decide +kernel) lb128_16255_16)
  · exact (transfer (s:=2048) (a:=14335) (t:=128) (u:=16255) perm62 (by decide +kernel) (by decide +kernel) lb128_16255_16)
  · exact (transfer (s:=4096) (a:=12287) (t:=128) (u:=16255) perm60 (by decide +kernel) (by decide +kernel) lb128_16255_16)
  · exact (transfer (s:=8192) (a:=8191) (t:=128) (u:=16255) perm48 (by decide +kernel) (by decide +kernel) lb128_16255_16)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem root_child_all (i : I) (b : Bool) : Witnessed (added 0 i b) (dropped 16383 i) (dropped 16383 i) := by
  have split_i : ∀ i : I, i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 := by decide +kernel
  rcases split_i i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · cases b
    · exact witness_check 2113695617958364350947441678131244161122698879083135616481092960256 (by decide +kernel)
    · exact witness_check 2172934083325861155178442727680642267020310672413674280899304882176 (by decide +kernel)
  · cases b
    · exact witness_check 3371272475891081167444608908379892319785192267194650630693085773832 (by decide +kernel)
    · exact witness_check 2112873468281455607265160386979210840312971677026647739900023014425 (by decide +kernel)
  · cases b
    · exact witness_check 2113721435677787094894727382238468277895545908868290910542119829512 (by decide +kernel)
    · exact witness_check 3370038328644850047585539967916221349423635541163608192280129175560 (by decide +kernel)
  · cases b
    · exact witness_check 2113695618251151878753434615636662303638482428272906874810846937096 (by decide +kernel)
    · exact witness_check 2113721410568997029462787854728401860360017989273163697007208563737 (by decide +kernel)
  · cases b
    · exact witness_check 2113695617958349449476745725636570624763576251232955062833929256968 (by decide +kernel)
    · exact witness_check 5897533347810801161995451699890692220152429062672899759769123291144 (by decide +kernel)
  · cases b
    · exact witness_check 2113695617958349449476745725636570624744937261593529503848201715720 (by decide +kernel)
    · exact witness_check 2113759876648835483652411877837770397914218435316775524190621532168 (by decide +kernel)
  · cases b
    · exact witness_check 2113695617958349449476745725636569162449380954103468892423130185736 (by decide +kernel)
    · exact witness_check 2146605710083655401382416122190461521063841539449440608494937440264 (by decide +kernel)
  · cases b
    · exact witness_check 2113695617958349449476745725636316202217508273326884254416092398617 (by decide +kernel)
    · exact witness_check 3371272476183898498191993750858613338994017940756923389597230039040 (by decide +kernel)
  · cases b
    · exact witness_check 2113695617958349449476745360513591002340772961256798923998504681480 (by decide +kernel)
    · exact witness_check 2113721435677802019749447440311879041791875945756048575781772198928 (by decide +kernel)
  · cases b
    · exact witness_check 2113695617958349449385000459889815641160595712311118994332677832712 (by decide +kernel)
    · exact witness_check 3391018831882883929250203729684568061626309905947064723030884221000 (by decide +kernel)
  · cases b
    · exact witness_check 2113695617958346384707812242733151151636482293923359934242980626440 (by decide +kernel)
    · exact witness_check 2146606311714199580378380217803799123281368723644073457132200527968 (by decide +kernel)
  · cases b
    · exact witness_check 2113695616975636683896494495214280593603440715884831394363586641928 (by decide +kernel)
    · exact witness_check 2172934785375477926974390325994574978903064216309484087245998129336 (by decide +kernel)
  · cases b
    · exact witness_check 2113650604861804991588988259190616802587706609889455604872329560072 (by decide +kernel)
    · exact witness_check 2212380878618400016046522336333149738970946534760101082597424627992 (by decide +kernel)
  · cases b
    · exact witness_check 45014079260288328687810641653901113252260474014521992533245960 (by decide +kernel)
    · exact witness_check 73141807384444809147731206404052475454038729937074583272161688 (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem root_all : Witnessed 0 16383 16383 := witness_check 2113695617958349449476745725636570624763576479880347856463821537288 (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem fano_no_nineteen : CountBound 0 16383 20 := by
  intro f hf k h
  have pop : 2 ≤ (indices 16383).length := by decide +kernel
  have es : ∀ i ∈ indices 16383, Essential (slice f 0 16383) i :=
    fun i hi => witnesses_sound hf (root_all i (index_mem.mp hi)).2
  obtain ⟨p⟩ := first_exists h (index_nodup _) pop es
  have survive : Essential (proj p.y p.o (slice f 0 16383)) p.x := by
    rw [slice_proj f 0 16383 p.y p.o p.ymem]
    apply witnesses_sound hf
    have rest : p.x ∈ indices (dropped 16383 p.y) := by
      rw [index_drop]
      exact (List.mem_erase_of_ne p.xy).mpr p.xmem
    exact (root_child_all p.y p.o p.x (index_mem.mp rest)).2
  have nc (b : Bool) : ¬IsConst (proj p.x b (slice f 0 16383)) := by
    rw [slice_proj f 0 16383 p.x b p.xmem]
    have nn : ∀ x : I, dropped 16383 x ≠ 0 := by decide +kernel
    exact nonconst_of_witnesses hf (witnessed_nonzero (root_child_all p.x b) (nn p.x))
  let lb := fun (b : Bool) => if b then 16 else 17
  have low (b : Bool) : LB ((indices 16383).erase p.x) (proj p.x b (slice f 0 16383)) (lb b) := by
    rw [slice_proj f 0 16383 p.x b p.xmem,←index_drop]
    cases b with
    | false => exact root_bound_0 p.x f hf
    | true => exact root_bound_1 p.x f hf
  cases e : p.o with
  | false =>
    have low0 := p.lower false true (n:=17) (fun _=>survive) (nc false) (low false)
    simpa [e] using low0
  | true =>
    obtain ⟨b,num⟩ := extra_first p survive nc lb low
    cases b <;> simpa [e,lb] using num

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem posted_gate_lower_20 (gs : List PEqualNP.Outside.L_meta_7737.Core.Op) (out : Nat)
    (ok : PEqualNP.Outside.L_meta_7737.DAG.MaskOK ((gs.foldl PEqualNP.Outside.L_meta_7737.Core.step PEqualNP.Outside.L_meta_7737.Core.baseWords).getD out 0)) :
    20 ≤ gs.length := posted_lower_of_count fano_no_nineteen gs out ok

end PEqualNP.Outside.L_meta_7737.States

theorem PEqualNP.Outside.L_meta_7737 : ¬ (have x1 : List (BitVec (58 : ℕ)) := [(95229015649943559 : BitVec (58 : ℕ)), (63038587666488 : BitVec (58 : ℕ)), (256462815680 : BitVec (58 : ℕ)), (4292497062759936 : BitVec (58 : ℕ)), (8521481482240 : BitVec (58 : ℕ)), (14003410187812864 : BitVec (58 : ℕ)), (55389823207997440 : BitVec (58 : ℕ)), (189297016294081033 : BitVec (58 : ℕ)), (155696362464477250 : BitVec (58 : ℕ)), (218994303132270608 : BitVec (58 : ℕ)), (183565875465490436 : BitVec (58 : ℕ)), (229736628138025984 : BitVec (58 : ℕ)), (270286071508633728 : BitVec (58 : ℕ)), (288160007407550752 : BitVec (58 : ℕ))]; ∃ (x2 : List (Bool × ℕ × ℕ)), x2.length = (19 : ℕ) ∧ (∀ (x3 : Fin x2.length), (x2.getD ↑x3 (Bool.false, (0 : ℕ), (0 : ℕ))).2.1 < (x2.getD ↑x3 (Bool.false, (0 : ℕ), (0 : ℕ))).2.2 ∧ (x2.getD ↑x3 (Bool.false, (0 : ℕ), (0 : ℕ))).2.2 < (14 : ℕ) + ↑x3) ∧ (List.foldl (fun (x3 : List (BitVec (58 : ℕ))) (x4 : Bool × ℕ × ℕ) => x3 ++ [if x4.1 = Bool.true then x3.getD x4.2.1 (0 : BitVec (58 : ℕ)) &&& x3.getD x4.2.2 (0 : BitVec (58 : ℕ)) else x3.getD x4.2.1 (0 : BitVec (58 : ℕ)) ||| x3.getD x4.2.2 (0 : BitVec (58 : ℕ))]) x1 x2).getD (32 : ℕ) (0 : BitVec (58 : ℕ)) &&& (288230376149614591 : BitVec (58 : ℕ)) = (2097151 : BitVec (58 : ℕ))) := by
  rintro ⟨gs,len,_,yes⟩
  have bound := PEqualNP.Outside.L_meta_7737.States.posted_gate_lower_20 gs 32 yes
  omega
