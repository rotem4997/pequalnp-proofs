import PEqualNP.Defs

-- The Live/Run/Forest verification framework and subgraph lower bounds
-- (known383 and dead) are adapted from PressF10, pequalnp-proofs PR 4332,
-- licensed under Apache-2.0.
namespace PEqualNP.Outside.L_meta_3853
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
private theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]

inductive Live (target : Sig) : Nat → Nat → Finset Sig → Prop
  | stop (hp : proper target) : Live target 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)) :
      Live target (k+1) (t+1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)) :
      Live target (k+1) t (insert a (insert b U))

private lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h with
  | stop hp => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩


def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v

private lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)

private lemma bin_laws (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  simp only [bin,one,zero,Bool.false_eq_true,ite_false,ite_true,BitVec.and_allOnes,BitVec.or_zero,BitVec.and_zero,BitVec.or_allOnes,BitVec.and_self,BitVec.or_self,and_self] <;> simp

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

private lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩ := bin_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩)

private lemma gate_rep (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ witness w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  have nx (a : Sig) (ha : represented w a) : represented w (neg a) ∨ witness w (neg a) := by
    rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · exact nx _ (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_rep false (get_rep w i) (get_rep w j)
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_rep true (get_rep w i) (get_rep w j)
        · exact nx _ (get_rep w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
private lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live target k t S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live target k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live target k t (insert (neg a) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live target k t (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hp : proper target) (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ Live target k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
    exact ⟨l,u,T,by simp; omega,hu,hT⟩

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [bit,bin]

private lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _

private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]




abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (pool : List (Wire R)) (v : Wire R) : Prop := v ∈ pool ∨ Constant v

def supply {R} (pool xs : List (Wire R)) := ∀ a ∈ xs, Available pool a

inductive Reach {R} (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | start : Reach roots 0 roots
  | one {p bank a} : Reach roots p bank → Available bank a →
      Reach roots (p+1) (inv a :: bank)
  | two {p bank a b} (op : Bool) : Reach roots p bank → Available bank a →
      Available bank b → Reach roots (p+1) (combine op a b :: bank)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

inductive Run {R} (goal : Wire R) : Nat → List (Wire R) → Prop
  | stop : Run goal 0 [goal]
  | perm {s xs zs} : xs.Perm zs → Run goal s xs → Run goal s zs
  | one {s a rest} (save : Bool) : Run goal s (inv a :: kept save a rest) →
      Run goal (s+1) (a::rest)
  | two {s a b rest} (op ka kb : Bool) :
      Run goal s (combine op a b :: kept ka a (kept kb b rest)) →
      Run goal (s+1) (a::b::rest)

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available bank a) (hb : Available bank b) :
    Available bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩

theorem available_cons {R} {bank v} (w : Wire R) (h : Available bank v) :
    Available (w::bank) v := by
  exact h.elim (fun h => Or.inl (List.mem_cons_of_mem _ h)) Or.inr

theorem extend_one {R} (roots : List (Wire R)) {p bank a} (hp : Reach roots p bank)
    (ha : Available bank a) :
    ∃ q next, Reach roots q next ∧ Available next (inv a) ∧
        (∀ v, Available bank v → Available next v) ∧ q+cost a ≤ p+1+cost (inv a) := by
  classical
  by_cases c : Constant a
  · exact ⟨p,bank,hp,Or.inr (inv_constant c),fun _ h => h,by simp [cost,c,inv_constant c]⟩
  · exact ⟨p+1,_,Reach.one hp ha,Or.inl (by simp),fun _ h => available_cons _ h,by simp [cost,c]⟩

theorem extend_two {R} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) :
    ∃ q next, Reach roots q next ∧ Available next (combine op a b) ∧
        (∀ v, Available bank v → Available next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach roots p bank) (hs : supply bank ws) :
    ∃ q next, Reach roots q next ∧ Available next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @one s a rest save _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_one roots hp (hs a (by simp))
    have ht : supply T (inv a :: kept save a rest) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · exact inc v (hs v (List.mem_cons.mpr (mem_kept hh)))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a rest save
    rw [mass_cons] at hl ⊢
    exact ⟨q,W,hW,hv,by omega⟩
  | @two s a b rest op ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_two roots op hp (hs a (by simp)) (hs b (by simp))
    have ht : supply T (combine op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)

theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]

theorem restrict_run {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws) :
    Run (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | one save _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    exact Run.one save ih
  | two op ka kb _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    cases op
    · exact Run.two false ka kb ih
    · exact Run.two true ka kb ih

theorem projected_bound {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach roots p bank) (hs : supply bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach roots q bs → Available bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega


abbrev Row := Fin 512
def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩

theorem observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r

theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact bit_neg _ _

theorem obs_bin (d : Bool) (a b : Sig) :
    observe (bin d a b) = combine d (observe a) (observe b) := by
  funext r
  cases d <;> exact bit_bin _ _ _ _

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {T : Sig} {k u S} (h : Live T k u S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run (observe T) k (v.map observe) := by
  classical
  induction h generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @unary k u U a ha fresh _ ih =>
    let rest := (U.erase a).toList
    let save := decide (a ∈ U)
    let tail := kept save a rest
    have er : rest.toFinset = U.erase a := by simp [rest]
    have hm : a ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have ht : tail.toFinset = U := by
      rw [show tail=kept save a rest by rfl,kept_fin,er]
      by_cases hh : a ∈ U <;> simp [save,hh]
    have nd := kept_nd save a rest hr hm
    have hf : neg a ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz))
    have progress := ih (neg a::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    rw [List.map_cons,map_kept,obs_neg] at progress
    have perm : (a::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (List.nodup_cons.mpr ⟨hm,hr⟩) hv
      simp [er,eqv]
    exact Run.perm (perm.map _) (Run.one save progress)
  | @binary k u U a b d ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d ka kb progress)


theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_bin (d : Bool) (f g : Wire Row) :
    table (combine d f g) = bin d (table f) (table g) := by
  rw [←table_observe (bin d (table f) (table g)),obs_bin,observe_table,observe_table]

theorem available_rep {bank : List (Wire Row)} {a} (h : Available bank a) :
    represented (bank.map table) (table a) := by
  rcases h with hm | ⟨b,rfl⟩
  · exact Or.inl (List.mem_map_of_mem hm)
  · apply Or.inr
    cases b
    · have z : table (fun _ => false) = zero := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_zero ⟨j,hj⟩).symm
      exact fun hp => hp.1 z
    · have z : table (fun _ => true) = one := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_one ⟨j,hj⟩).symm
      exact fun hp => hp.2 z

theorem inv_rep {w a} (ha : represented w a) :
    represented w (neg a) ∨ witness w (neg a) := by
  rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
  · exact Or.inl (Or.inr fun h => h.2 neg_laws.1)
  · exact Or.inl (Or.inr fun h => h.1 neg_laws.2)
  · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)

theorem pull_cons {w : List Sig} {z : Sig} {T k t S} (h : Live T k t S)
    (hz : represented w z ∨ witness w z) (hs : ∀ a ∈ S, a ∈ z::w) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live T k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  apply pull_gate h hz
  intro a hm
  simpa [or_comm] using hs a hm

theorem reach_live_sub {roots : List (Wire Row)} {p bank}
    (h : Reach roots p bank) {T k t S} (run : Live T k t S)
    (sub : ∀ a ∈ S, a ∈ bank.map table) :
    ∃ l v U, l ≤ p+k ∧ Live T l v U ∧ ∀ a ∈ U, a ∈ roots.map table := by
  induction h generalizing k t S with
  | start => exact ⟨k,t,S,by omega,run,sub⟩
  | @one p bank a h ha ih =>
    rw [List.map_cons,table_inv] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (inv_rep (available_rep ha)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,table_bin] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (bin_rep d (available_rep ha) (available_rep hb)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩

theorem reach_live {roots : List Sig} {p bank T} (hp : proper T)
    (h : Reach (roots.map observe) p bank) (hit : Available bank (observe T)) :
    ∃ k t S, k ≤ p ∧ Live T k t S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,v,U,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,v,U,by omega,hr,?_⟩
  simpa [List.map_map,Function.comp_def,table_observe] using hs

theorem live_row_difference {T k t S} (h : Live T k t S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @unary k t U a hp hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · refine ⟨a,by simp,?_⟩
      exact fun he => hd (by rw [bit_neg,bit_neg,he])
    · exact ⟨v,Finset.mem_insert_of_mem hu,hd⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {T k t S} (h : Live T k t S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def seed4 : Sig := neg (inputs.getD 4 zero)

def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem seed4_table : ∀ r : Row, bit r seed4 = !(sample r 4) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem seed4_nonzero : seed4 ≠ zero := by decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl

theorem table_eval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl

theorem exec_extends (gs : List Gate) (ws : List Sig) : ∃ l, execute gs ws = ws ++ l := by
  induction gs generalizing ws with
  | nil => exact ⟨[],by simp [execute]⟩
  | cons g gs ih =>
    obtain ⟨l,hl⟩ := ih (ws++[gv ws g])
    exact ⟨gv ws g::l,by simpa [execute,List.append_assoc] using hl⟩

def neighbor (i : Fin 9) : Nat := [4,2,1,2,3,0,1,2,3].getD i.val 0
def absentRow (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< neighbor i)
def presentRow (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor i))

def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_neg (f : Row → Row) (a : Sig) : rename f (neg a) = neg (rename f a) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (neg a)) = bit ⟨j,hj⟩ (neg (rename f a))
  rw [bit_rename,bit_neg,bit_neg,bit_rename]
theorem rename_bin (f : Row → Row) (d : Bool) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (bin d a b)) = bit ⟨j,hj⟩ (bin d (rename f a) (rename f b))
  rw [bit_rename,bit_bin,bit_bin,bit_rename,bit_rename]
theorem rename_inj (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [bit_rename,bit_rename,hr] at he
  exact he
theorem rename_constants (f : Row → Row) : rename f zero = zero ∧ rename f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (bit_rename f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
theorem live_rename {T k t S} (h : Live T k t S) (f : Row → Row) (onto : Function.Surjective f) :
    Live (rename f T) k t (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @unary k t U a hp hf _ ih =>
    have fresh : rename f (neg a) ∉ (insert a U).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_neg] at fresh ih ⊢
    exact Live.unary (pp _ hp) fresh ih
  | @binary k t U a b d ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {T k t S} (h : Live T k t S) (none : t=0) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | unary _ _ _ _ => omega
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih none
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      cases d <;> cases p : bit r a <;> cases q : bit s a <;>
        cases u : bit r b <;> cases z : bit s b <;> simp_all
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map observe) p bank → Available bank (observe T) → L ≤ p

def Impossible (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k t, k ≤ cap → ¬Live T k t S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {roots T L} (hp : proper T)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible T L roots.toFinset) : Lower roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,t,S,hk,run,hs⟩ := reach_live hp h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k t (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : represented ([] : List Sig) v := by
    have avail : Available ([] : List (Wire Row)) (observe v) := Or.inr ⟨b,h⟩
    simpa only [List.map_nil,table_observe] using available_rep avail
  exact (hr.resolve_left (by simp)) hv

theorem mass_append {R} (a b : List (Wire R)) : mass (a++b) = mass a + mass b := by
  simp [mass]
theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega

theorem lower_slice {roots other : List Sig} {T G : Sig} (pT : proper T) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower other G L) : Lower roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live pT hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact raw_required run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := list_run run front nd fe
  have gc : restrictRows r (observe T) = observe G := (observe_rename _ _).symm.trans (congrArg observe eq)
  have supp : supply (other.map observe) ((front.map observe).map (restrictRows r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←observe_rename]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)) := by
    simp only [front,List.map_append,mass_append]
    let xs := (singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←observe_rename]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]
    omega
  omega



def childOne (ws : List Sig) (a : Sig) (keep : Bool) : List Sig :=
  neg a :: kept keep a (ws.erase a)
def childTwo (ws : List Sig) (a b : Sig) (d ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (oneStep : ∀ a ∈ ws, ∀ keep, neg a ∉ ws → proper (neg a) →
      (childOne ws a keep).length ≤ cap →
      Impossible T (cap-1) (childOne ws a keep).toFinset)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible T cap ws.toFinset := by
  classical
  intro k t hk h
  generalize he : ws.toFinset = S at h
  cases h with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @unary k t U a ha hf tail =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have fresh : neg a ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let keep := decide (a ∈ U)
    have er := erase_fin hn a
    have rest : (kept keep a (ws.erase a)).toFinset = U := by
      rw [kept_fin,er,he]
      by_cases hm : a ∈ U <;> simp [keep,hm]
    have nd : (childOne ws a keep).Nodup := by
      have na : a ∉ ws.erase a := hn.not_mem_erase
      have nk := kept_nd keep a (ws.erase a) (hn.erase _) na
      refine List.nodup_cons.mpr ⟨?_,nk⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (rest ▸ List.mem_toFinset.mpr h))
    have eq : (childOne ws a keep).toFinset = insert (neg a) U := by simp [childOne,rest]
    have sc := (live_size tail).2
    have len : (childOne ws a keep).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact oneStep a am keep fresh hz len k t (by omega) (eq.symm ▸ tail)
  | @binary k t U a b d ha hb hab hf tail =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := (live_size tail).2
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d ka kb hab fresh hz len k t (by omega) (eq.symm ▸ tail)

def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i, bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
  ∀ w i, (asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w

def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2

def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws

theorem covered_bit {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (column oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]

theorem cover_sound {T k t S} (h : Live T k t S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → t=0) :
    covered oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (covered_bit (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := live_row_difference h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := mono_row_difference h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]

theorem cover_required {T cap ws k t} (h : Live T k t (List.toFinset ws))
    (hk : k ≤ cap) (hn : ws.Nodup) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (decide (ws.length=cap+1)) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  intro hh
  have eq := of_decide_eq_true hh
  have bound := (live_size h).2
  rw [List.toFinset_card_of_nodup hn] at bound
  omega



def Slice (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach (roots.map observe) p bank → Available bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m)

theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = masked d b) :
    restrictRows f (observe a) = restrictRows f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h

theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = zero) : restrictRows f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

def poolSupply (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available bank (restrictRows f (observe a))

theorem availableB_sound {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply f bank pool)
    (check : availableB d pool a = true) : Available bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with (hz | ho) | ⟨v,hv,he⟩
  · exact Or.inr ⟨false,masked_zero dom hz⟩
  · exact Or.inr ⟨true,masked_one dom ho⟩
  · exact masked_eq dom he ▸ supplyB v hv

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) :=
  if c.1=2 then neg c.2.1 else bin (c.1==1) c.2.1 c.2.2
def choiceOK (d : Sig) (pool : List Sig) (c : Choice) :=
  availableB d pool c.2.1 && (c.1==2 || availableB d pool c.2.2)

theorem pay_choice {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (c : Choice) (valid : choiceOK d pool c = true) :
    ∃ next, Reach roots (q+1) next ∧ poolSupply f next (choiceVal c :: pool) := by
  have ok : availableB d pool c.2.1 = true ∧ (c.1==2 || availableB d pool c.2.2) = true := by simpa only [choiceOK,Bool.and_eq_true] using valid
  have ha := availableB_sound dom hs ok.1
  let z := restrictRows f (observe (choiceVal c))
  have hz : Reach roots (q+1) (z::bank) := by
    by_cases unary : c.1=2
    · change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_pos unary,obs_neg]
      exact Reach.one hp ha
    · have hb : availableB d pool c.2.2 = true := by simpa [unary] using ok.2
      have hz' := Reach.two (c.1==1) hp ha (availableB_sound dom hs hb)
      change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_neg unary,obs_bin]
      have comm (b : Bool) (v w : Wire Row) : restrictRows f (combine b v w) = combine b (restrictRows f v) (restrictRows f w) := by cases b <;> rfl
      rw [comm]
      exact hz'
  refine ⟨_,hz,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact Or.inl (by simp [z])
  · exact available_cons _ (hs _ hm)

def makePool (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK d pool c then makePool d (choiceVal c::pool) cs else none

theorem makePool_sound {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (cs : List Choice) {result} (ok : makePool d pool cs = some result) :
    ∃ next, Reach roots (q+cs.length) next ∧ poolSupply f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction

def isMaskedConstant (d a : Sig) := masked d a == zero || masked d a == d
theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (isMaskedConstant d) ≤ mass ((ws.map observe).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,mass_cons]
    cases h : isMaskedConstant d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observe a)) := by
        have hh : masked d a = zero ∨ masked d a = d := by simpa only [isMaskedConstant,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,masked_zero dom hz⟩
        · exact ⟨true,masked_one dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih

def poolCut (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB d pool)

theorem poolCut_sound {raw T d L} (slice : Slice raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut d L cap cs.length pool ws = true) :
    Impossible T cap ws.toFinset := by
  intro k t hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply bank ((ws.map observe).map (restrictRows f)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact availableB_sound dom hs (List.all_eq_true.mp all a ha)
  have b := projected_bound f (list_run h ws nd rfl) nc hr coveredS lo
  have massLo := count_constants dom ws
  have hu := ineq
  simp only [Nat.zero_add] at b
  omega



abbrev Move := Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 512 (512-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [shifted,h,r.isLt]

theorem bool_mux (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp

theorem bit_mux (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact bool_mux _ _ _

theorem bit_move (r : Row) (m : Move) (a : Sig) : bit r (wordMove m a) = bit (rowMove m r) a := by
  simp only [wordMove,bit_mux,bit_shift,rowMove]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl

def movedRow (ms : List Move) (r : Row) := ms.foldl (fun j m => rowMove m j) r
def movedWord (ms : List Move) (a : Sig) := ms.foldr wordMove a
theorem bit_moved (ms : List Move) (a : Sig) (r : Row) :
    bit r (movedWord ms a) = bit (movedRow ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)
theorem moved_eq_rename (ms : List Move) (a : Sig) : movedWord ms a = rename (movedRow ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (bit_moved ms a ⟨j,hj⟩).trans (bit_rename _ _ ⟨j,hj⟩).symm

def freeWord (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w
theorem freeWord_ok {roots w} (ok : freeWord roots w = true) :
    Available (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr ⟨false,funext bit_zero⟩
  · exact Or.inr ⟨true,funext bit_one⟩
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

theorem lower_map {ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (pG : proper G) (hL : Lower base G L) : Lower raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

theorem slice_correct {ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower base G L) :
    Slice raw T d L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  have obs : restrictRows (movedRow ms) (observe T) = observe G :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←bit_moved,all,bit_one]
  · intro a ha
    rw [←observe_rename]
    exact supp a ha
  · rw [obs]
    exact observe_proper properG
  · rw [obs]
    exact hL

def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
theorem witnessB_sound {T roots a rs} (ok : witnessB T roots a rs = true) : Essential T roots a := by
  simp only [witnessB,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩

def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok _ hm)

theorem lower_count {raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live properT hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := (live_size run).2
  omega

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

theorem lift_ok {ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower base G L) :
    Lower raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT properG _ eq supp _ (essential_ok ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,moved_eq_rename] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext bit_zero⟩
  · rw [h]
    exact ⟨true,funext bit_one⟩



def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def vertex (m j : Nat) := if m.testBit j then (if m.testBit 9 && j == 4 then neg (inputs.getD 4 zero) else inputs.getD j zero) else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
def cube0 : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def cube3 : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def cube6 : Nat → Nat
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
  | 6 => 0x10000000000000001
  | _ => 0x1
def subcube (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)
def fixRows (z o : Nat) : List Move :=
  (List.range 9).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)

def supportPairs (baseRow mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) => (a,Fin.ofNat 512 baseRow,Fin.ofNat 512 (baseRow ^^^ (1 <<< i)))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  let base := if m.testBit 9 && m.testBit 4 then 16 else 0
  (selected m).map fun (i,a) =>
    let r := base ^^^ (1 <<< ((hints >>> (4*i)) &&& 15))
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ^^^ (1 <<< i)))

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
def assertSize (m hints L : Nat) :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs &&
    decide (L ≤ (xs.map Prod.fst).toFinset.card-1)
theorem size_of {m hints L} (h : assertSize m hints L = true) :
    Lower (vars m) (graphGoal m) L := by
  simp only [assertSize,Bool.and_eq_true,decide_eq_true_eq] at h
  intro p bank hr ha
  exact h.2.trans (lower_count (proper_of _ h.1.1) _ h.1.2 p bank hr ha)

abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := (m &&& 511) ^^^ ((m &&& 511) &&& (z ||| o))
def chartGoal (m : Nat) : Sig := graphGoal m
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let baseRow := if m.testBit 9 && free.testBit 4 then 16 else 0
  let xs := supportPairs baseRow s
  let count := (xs.map Prod.fst).toFinset.card
  let drop := colFree free q 0
  let lz := if m.testBit 9 && drop.testBit 4 then drop &&& (511 ^^^ 16) else drop
  let lo := if m.testBit 9 && drop.testBit 4 then 16 else 0
  properB G && checkMap ms (vars m) (chartGoal m) (vars free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (vars free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows lz lo) G (vars free) (vars q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice (vars m) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  obtain ⟨z,o,q,s,L⟩ := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let baseRow := if m.testBit 9 && free.testBit 4 then 16 else 0
  let xs := supportPairs baseRow s
  change (((properB G && checkMap ms (vars m) (chartGoal m) (vars free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) _ hh.1 p bank hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (proper_of _ ok.1.1.1) (proper_of _ hh.1.1) (valid q) p bank hr ha)

def relabelOK (old rep : Nat) (swaps : List Nat) :=
  properB (graphGoal old) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (vars old) (graphGoal old) (vars rep) (graphGoal rep)
theorem relabel_of {old rep L swaps} (ok : relabelOK old rep swaps = true)
    (h : Lower (vars rep) (graphGoal rep) L) : Lower (vars old) (graphGoal old) L := by
  simp only [relabelOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1) (proper_of _ ok.1.2) h

def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower (vars e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower (vars q) (graphGoal q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he


structure BoundPool where
  domain : Sig
  bound : Nat
  paid : Nat
  wires : List Sig

def ValidPool (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach (roots.map observe) q ws → Available ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach (roots.map observe) c.paid bank ∧ poolSupply f bank c.wires ∧ True

theorem build_valid {raw T d lb} (h : Slice raw T d lb) (cs : List Choice) {ws}
    (build : makePool d raw cs = some ws) : ValidPool raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa using hr,hs,trivial⟩

theorem valid_exclude {raw T c} (valid : ValidPool raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB c.domain c.wires a = true)
    (buy : if paid then choiceOK c.domain c.wires choice = true
       else availableB c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible T k (choiceVal choice :: rest).toFinset := by
  intro t num ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach (roots.map observe) n out)
      (zs : poolSupply f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply out ((ws.map observe).map (restrictRows f)) := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b := projected_bound f (list_run run ws nd rfl) nc reach covered lo
    have cm := count_constants dom ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (isMaskedConstant c.domain) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact availableB_sound dom hs buy
    · exact availableB_sound dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩ := pay_choice dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have avail := availableB_sound dom hs (known _ hm)
      rcases avail with mem | con
      · have ha : availableB c.domain c.wires a = true := known _ hm
        have point : ∀ u ∈ c.wires, Available out (restrictRows f (observe u)) :=
          fun u hu => hc u (List.mem_cons_of_mem _ hu)
        exact availableB_sound dom point ha
      · exact Or.inr con

def scalarPoolCut (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB c.domain c.wires)) && (!extra || choiceOK c.domain c.wires op)

theorem scalarPoolCut_sound {raw T c} (valid : ValidPool raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut c k rest op = true) :
    Impossible T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1

def materialize (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {raw T d L cs c} (slice : Slice raw T d L)
    (h : materialize raw cs d L = some c) : ValidPool raw T c := by
  unfold materialize at h
  cases he : makePool d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he


abbrev Bits := BitVec 768
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 768 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 768 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 768 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 768 → Row) (x : Decor) := x.2 = pairSig r s x.1
def dneg (x : Decor) : Decor := (neg x.1,~~~x.2.1,~~~x.2.2)
def dbin (d : Bool) (x y : Decor) : Decor :=
  if d then (bin d x.1 y.1,x.2.1 ||| y.2.1,x.2.2 ||| y.2.2)
  else (bin d x.1 y.1,x.2.1 &&& y.2.1,x.2.2 &&& y.2.2)

theorem ofRows_neg (r : Fin 768 → Row) (a : Sig) : ofRows r (neg a) = ~~~ofRows r a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (neg a) ⟨j,hj⟩
  rw [bit_neg,←ofRows_bit r a ⟨j,hj⟩] at h
  simpa only [BitVec.getLsbD_not,hj,decide_true,Bool.true_and] using h
theorem ofRows_bin (r : Fin 768 → Row) (d : Bool) (a b : Sig) :
    ofRows r (bin d a b) = if d then ofRows r a ||| ofRows r b else ofRows r a &&& ofRows r b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  cases d <;> simpa only [Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_or] using h
theorem faithful_neg {r s x} (h : faithful r s x) : faithful r s (dneg x) := by
  change x.2 = _ at h
  simp only [faithful,dneg,pairSig,ofRows_neg, h]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  cases d <;> simp only [faithful,dbin,Bool.false_eq_true,ite_false,ite_true,pairSig,ofRows_bin,hx,hy]

def codeDecor (op : Nat) (x y : Decor) := if op=2 then dneg x else dbin (op==1) x y
def defaultDecor : Decor := (zero,0,0)
theorem faithful_default (r s) : faithful r s defaultDecor := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : Bits).getLsbD j = (ofRows r zero).getLsbD j
    rw [show (ofRows r zero).getLsbD j = bit (r ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
  · change (0 : Bits).getLsbD j = (ofRows s zero).getLsbD j
    rw [show (ofRows s zero).getLsbD j = bit (s ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
theorem faithful_get {r s ws} (all : ∀ v ∈ ws, faithful r s v) (i : Nat) :
    faithful r s (List.getD ws i defaultDecor) := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact faithful_default _ _
  | some v => exact all _ (List.mem_of_getElem? e)
def decodeBank (n : Nat) (bits : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 15) defaultDecor
    let b := ws.getD ((bits >>> 4) &&& 15) defaultDecor
    decodeBank k (bits >>> 10) (ws++[codeDecor ((bits >>> 8) &&& 3) a b])
theorem decode_faithful (n bits) (ws) (r s) (base : ∀ v ∈ ws, faithful r s v) :
    ∀ v ∈ decodeBank n bits ws, faithful r s v := by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl := List.mem_singleton.mp hz
      unfold codeDecor
      split
      · exact faithful_neg (faithful_get base _)
      · exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def asRow (cols : Nat → Bits) (i : Fin 768) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem coordinate0 : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel
theorem coordinate1 : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel
theorem coordinate2 : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel
theorem coordinate3 : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel
theorem coordinate4 : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel
theorem coordinate5 : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel
theorem coordinate6 : ∀ r : Row, bit r (inputs.getD 6 zero) = r.val.testBit 6 := by decide +kernel
theorem coordinate7 : ∀ r : Row, bit r (inputs.getD 7 zero) = r.val.testBit 7 := by decide +kernel
theorem coordinate8 : ∀ r : Row, bit r (inputs.getD 8 zero) = r.val.testBit 8 := by decide +kernel
theorem input_coords : ∀ (j : Fin 9) (r : Row),
    bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j r
  fin_cases j
  · exact coordinate0 r
  · exact coordinate1 r
  · exact coordinate2 r
  · exact coordinate3 r
  · exact coordinate4 r
  · exact coordinate5 r
  · exact coordinate6 r
  · exact coordinate7 r
  · exact coordinate8 r
theorem asRow_bit (cols : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<9 ∧ a=inputs.getD j zero := by
  obtain ⟨v,hv,hh⟩ := List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction
theorem raw_faithful (m) (p q : Nat → Bits) :
    ∀ a ∈ rawDecor m p q, faithful (asRow p) (asRow q) a := by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hj,rfl⟩ := selected_entry hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (asRow_bit p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
  · exact (asRow_bit q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm

def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then (if m.testBit 9 && j == 4 then ~~~(v 4) else v j) else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then (if m.testBit 9 && j.val == 4 then ~~~(v 4) else v j.val) else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · by_cases hf : (m.testBit 9 && j.val == 4) = true
    · have hj4 : j.val = 4 := by
        simp only [Bool.and_eq_true, beq_iff_eq] at hf; exact hf.2
      simp only [vertex, hh, hf, ite_true, bit_neg, BitVec.getLsbD_not, i.isLt, decide_true, Bool.true_and]
      exact congrArg Bool.not (asRow_bit v i ⟨4, by decide⟩)
    · simpa [vertex, hh, hf] using asRow_bit v i j
  · simp [vertex, hh, bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then (if m.testBit 9 && j == 4 then ~~~(v 4) else v j) else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
abbrev Cov := Bits × Bits × Bits

def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Decor) : Cov :=
  v.foldr (fun a c => addCov (column d a.2) c) (0,0,0)

def takeOne (c : Cov) (a : Bits) : Bits := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private theorem cov_one (c : Cov) (a : Bits) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private theorem cov_two (c : Cov) (a b : Bits) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem add_swap (c : Cov) (a b : Bits) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem cov_perm (d : Bool) {l r : List Decor} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (column d a.2)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2



theorem cov_word (d : Bool) (v : List Decor) {r s} (good : ∀ a ∈ v, faithful r s a) :
    (coverage d v).1 = covered d (pairSig r s) (v.map Prod.fst) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column d a.2 ||| (coverage d v).1) = column d (pairSig r s a.1) ||| _
    rw [show a.2=pairSig r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]

def delOne (ws : List Decor) (a : Decor) (keep : Bool) :=
  if keep then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) :=
  delOne (delOne ws a ka) b kb

theorem delOne_perm {ws : List Decor} (a : Decor) (ha : a ∈ ws) :
    ws.Perm (a::ws.erase a) := List.perm_cons_erase ha

theorem cover_one {ws : List Decor} (d : Bool) (a : Decor) (ha : a ∈ ws) (keep : Bool) :
    (coverage d (delOne ws a keep)).1 =
      (if keep then (coverage d ws).1 else takeOne (coverage d ws) (column d a.2)) := by
  cases keep
  · change (coverage d (ws.erase a)).1 = takeOne (coverage d ws) _
    rw [cov_perm d (delOne_perm a ha)]
    exact (cov_one _ _).symm
  · rfl
theorem delTwo_perm {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (delOne_perm a ha).trans (List.Perm.cons _ (delOne_perm b hm))

theorem cover_two {ws : List Decor} (d : Bool) (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (ka kb : Bool) :
    (coverage d (delTwo ws a b ka kb)).1 =
      (if ka then (if kb then (coverage d ws).1 else takeOne (coverage d ws) (column d b.2))
       else if kb then takeOne (coverage d ws) (column d a.2)
       else takeTwo (coverage d ws) (column d a.2) (column d b.2)) := by
  cases ka <;> cases kb
  · change (coverage d ((ws.erase a).erase b)).1 = takeTwo (coverage d ws) _ _
    rw [cov_perm d (delTwo_perm a b ha hb ne)]
    exact (cov_two _ _ _).symm
  · exact cover_one d a ha false
  · exact cover_one d b hb false
  · rfl

def sameWords (a b : List Sig) := (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))
theorem sameWords_sound {xs ys} (h : sameWords xs ys = true) : xs.toFinset=ys.toFinset := by
  simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩


def keyWord (v : Sig) :=
  let n := v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def closeChild (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut p k rest op)

theorem closeChild_sound {raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

abbrev CovPair := Cov × Cov
def preCov (ws : List Decor) : CovPair := (coverage false ws,coverage true ws)
def getCov (c : CovPair) (d : Bool) := if d then c.2 else c.1
theorem get_preCov (ws) (d : Bool) : getCov (preCov ws) d = coverage d ws := by cases d <;> rfl
def restCov (v : Cov) (a b : Bits) (un ka kb : Bool) :=
  if un then (if ka then v.1 else takeOne v a) else
    if ka then (if kb then v.1 else takeOne v b)
    else if kb then takeOne v a else takeTwo v a b
def opKeep (un ka kb : Bool) (a b : Decor) (ws : List Decor) :=
  if un then delOne ws a ka else delTwo ws a b ka kb

theorem rest_coverage {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws)
    (un ka kb d : Bool) (ne : un=false → a≠b) :
    (coverage d (opKeep un ka kb a b ws)).1 =
      restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) un ka kb := by
  rw [get_preCov]
  cases un
  · exact cover_two d a b ha hb (ne rfl) ka kb
  · exact cover_one d a ha ka

theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    (opKeep un ka kb a b ws).Sublist ws := by
  cases un
  · exact (delOne_sub _ _ _).trans (delOne_sub _ _ _)
  · exact delOne_sub _ _ _
theorem len_keep (ws : List Decor) (a b : Decor) (un ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : un=false → a≠b) :
    (opKeep un ka kb a b ws).length =
      ws.length - (if ka then 0 else 1) - (if un || kb then 0 else 1) := by
  cases un
  · have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm (ne rfl))).mpr hb
    cases ka <;> cases kb <;> simp [opKeep,delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]
  · cases ka <;> cases kb <;> simp [opKeep,delOne,List.length_erase_of_mem ha]

def movedDecor (op : Nat) (a b : Decor) := codeDecor op a b
def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)
theorem moved_full (op) (a b : Decor) :
    (movedDecor op a b).1 = choiceVal (movedChoice op a b) := by
  by_cases h : op=2
  · simp [movedDecor,codeDecor,h,dneg,choiceVal,movedChoice]
  · cases hh : op==1 <;> simp [movedDecor,codeDecor,h,hh,dbin,choiceVal,movedChoice]
theorem moved_faithful {r s a b} (ha : faithful r s a) (hb : faithful r s b) (op : Nat) :
    faithful r s (movedDecor op a b) := by
  unfold movedDecor codeDecor
  split
  · exact faithful_neg ha
  · exact faithful_bin _ ha hb

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let un := op==2
  let len := 1+(n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  if len>cap then true else
    let d := len==cap
    let rs := restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 768 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (opKeep un ka kb a b ws).map Prod.fst
      closeChild pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (movedDecor op a b).1 :: (opKeep (op==2) ka kb a b ws).map Prod.fst
theorem evalMove_sound {raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false → a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov ws,pools,links) op a b (movedDecor op a b) ka kb = true) :
    Impossible T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := movedDecor op a b
  let rest := opKeep (op==2) ka kb a b ws
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k t hk h
  have hsz := (live_size h).2
  change child.toFinset.card + t ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h hk ndc (pair_sep pairs)
  have ce : cap-1+1=cap := by omega
  rw [ce] at sep
  let d := child.length==cap
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz := rest_coverage ha hb (op==2) ka kb d ne
  have hf := moved_faithful (faith _ ha) (faith _ hb) op
  have deq : decide (child.length=cap) = (child.length==cap) := by by_cases he : child.length=cap <;> simp [he]
  change covered (decide (child.length = cap)) (pairSig r s) child = BitVec.allOnes 768 at sep
  rw [deq] at sep
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2) != BitVec.allOnes 768) = false := by simp [sep]
  change (if (_ != _) then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  have val := moved_full op a b
  change z.1 = _ at val
  change Live T k t child.toFinset at h
  have nd' := ndc
  change (z.1::rest.map Prod.fst).Nodup at nd'
  change Live T k t (z.1::rest.map Prod.fst).toFinset at h
  rw [val] at nd' h
  exact closeChild_sound pv lv nd' test k t hk h


def testPair (ctx : NodeContext) (a b : Decor) (d : Bool) :=
  let op := if d then 1 else 0
  let z := movedDecor op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
  let z := movedDecor 2 a a
  evalMove ctx 2 a a z false false && evalMove ctx 2 a a z true true &&
    bs.all (fun b => testPair ctx a b false && testPair ctx a b true)
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_unary {ctx ws} (h : testAll ctx ws=true) {a : Decor} (ha : a∈ws) (keep : Bool) :
    evalMove ctx 2 a a (movedDecor 2 a a) keep keep=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow] at h
    rcases List.mem_cons.mp ha with rfl | hm
    · cases keep
      · exact h.1.1.1
      · exact h.1.1.2
    · exact ih h.2 hm

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) (d : Bool) : testPair ctx a b d=true ∨ testPair ctx b a d=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      left
      cases d <;> first | exact (h.1.2 b bm).1 | exact (h.1.2 b bm).2
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · right
        cases d <;> first | exact (h.1.2 a haTail).1 | exact (h.1.2 a haTail).2
      · exact ih h.2 haTail hbTail

theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) ka kb = true := by
  simp only [testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]

theorem unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (eq : a.1=b.1) : a=b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
    · exact ih ht haTail hbTail

theorem kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (un ka kb : Bool) (v : Sig) :
    v ∈ (opKeep un ka kb a b ws).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (un=true ∨ v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  cases un <;> simp only [opKeep,Bool.false_eq_true,ite_false,ite_true,delTwo,List.mem_map,
    mem_delone wn,mem_delone dn,or_false,false_or,true_or,and_true] <;> constructor
  all_goals
    first
    | rintro ⟨w,hw,rfl⟩
      first
      | exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
      | exact ⟨⟨_,hw.1,rfl⟩,hw.2.imp (fun ne eq => ne (unique_value nd hw.1 ha eq)) id⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
      exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1⟩
      exact ⟨w,⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem unary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a : Decor} (ha : a∈ws)
    (keep : Bool) :
    (moveFront ws 2 a a keep keep).toFinset = (childOne (ws.map Prod.fst) a.1 keep).toFinset := by
  ext v
  simp only [moveFront,childOne,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha ha,keep_mem,nd.mem_erase_iff,movedDecor,codeDecor,dneg,ite_true,
    Nat.reduceBEq,true_or,and_true]
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  by_cases e : v=a.1 <;> cases keep <;> simp_all

theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d ka kb : Bool) :
    (moveFront ws (if d then 1 else 0) a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv := List.mem_map_of_mem (f:=Prod.fst) hb
  cases d <;> simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,movedDecor,codeDecor,dbin,
    Bool.false_eq_true,Nat.reduceBEq,ite_true,ite_false,false_or]
  all_goals by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem childTwo_swap (v : List Sig) (nd : v.Nodup) (a b : Sig) (d ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a d kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_comm d b a]
  tauto

theorem node_sound {raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov ws,pools,links) ws = true) :
    Impossible T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k t hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    cases h
    exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  · intro v hv keep fresh pro len
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
    have hf := unary_front nd ha keep
    rw [←hf]
    exact evalMove_sound pairs faith nd ha ha (by simp) hc' pv lv pro fresh (all_unary checks ha keep)
  · intro a ha b hb d ka kb ne fresh pro len
    obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
    obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
    have ab : a≠b := fun e => ne (congrArg Prod.fst e)
    have one (a b : Decor) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
        (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
        (test : testPair (cap,ws.length,ws,preCov ws,pools,links) a b d = true) :
        Impossible T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
      rw [←binary_front nd aa bb ne']
      have eq : (movedDecor (if d then 1 else 0) a b).1 = bin d a.1 b.1 := by cases d <;> rfl
      exact evalMove_sound pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' pv lv
        (eq ▸ pr) (eq ▸ fr) (testPair_at test ka kb)
    rcases all_binary checks haW hbW ab d with hh | hh
    · exact one a b haW hbW ne ka kb pro fresh hh
    · rw [childTwo_swap _ nd]
      exact one b a hbW haW (Ne.symm ne) kb ka (bin_comm d a.1 b.1 ▸ pro)
        (bin_comm d a.1 b.1 ▸ fresh) hh


theorem agree_inputs (r s : Row) (h : ∀ a ∈ inputs, bit r a = bit s a) : r=s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<9
  · let i : Fin 9 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 512 ≤ 2^j := by
      change 2^9 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm

def composedOK (p q : List Move) := inputs.all (fun a => movedWord p (movedWord q a) == a)
theorem composed_id {p q} (h : composedOK p q = true) (r : Row) :
    movedRow q (movedRow p r) = r := by
  apply agree_inputs
  intro a ha
  rw [←bit_moved,←bit_moved]
  have eq := beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]

def autoOK (T : Sig) (p : List Move) :=
  (movedWord p T == T) && composedOK p p.reverse && composedOK p.reverse p
theorem rotate_excluded {T n} {ws : List Sig} (hi : Impossible T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k t hk h
  have run := live_rename h (movedRow p) onto
  have goal : rename (movedRow p) T = T := (moved_eq_rename p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [bit_rename,bit_moved,composed_id ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k t hk run

abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing := (0,0,0,0,0,0,0,fun _ => 0)
def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)


def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh)%slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots)%16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none


inductive IndexTree (α : Type) where
  | leaf (items : List α)
  | fork (pivot : Nat) (left right : IndexTree α)
def IndexTree.read {α} : IndexTree α → Nat → Option α
  | .leaf xs,i => xs[i]?
  | .fork pivot a b,i => if i<pivot then a.read i else b.read (i-pivot)
def IndexTree.values {α} : IndexTree α → List α
  | .leaf xs => xs
  | .fork _ a b => a.values ++ b.values
theorem IndexTree.read_mem {α} (tree : IndexTree α) {i x} (e : tree.read i=some x) :
    x ∈ tree.values := by
  induction tree generalizing i with
  | leaf xs => exact List.mem_of_getElem? e
  | fork pivot a b ia ib =>
    simp only [IndexTree.read] at e
    split at e
    · exact List.mem_append_left _ (ia e)
    · exact List.mem_append_right _ (ib e)

abbrev ExtraFactory := Nat → Nat → List Decor → Nat → Nat → Option BoundPool
def noFactory : ExtraFactory := fun _ _ _ _ _ => none
def FactorySound (m : Nat) (f : ExtraFactory) := ∀ ops d bank idx paid c,
  f ops d bank idx paid = some c → ValidPool (vars m) (chartGoal m) c
theorem noFactorySound (m : Nat) : FactorySound m noFactory := by
  intro ops d bank idx paid c h
  contradiction

structure Forest where
  mask : Nat
  cap : Nat
  samples : Nat → Bits × Bits
  cols : IndexTree ColumnInfo
  autos : Array (List Nat)
  levels : Nat → Packing
  index : Nat → Nat → Option (Nat × Nat)
  bonus : ExtraFactory
  safe : FactorySound mask bonus

def wiresOf (g : Forest) :=
  rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a :=
  raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) := liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val :=
  bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 768) (hq : chartSamples m q = 0) :
    properPairs (chartGoal m) (asRow p) (asRow q) := by
  intro i
  simp only [chart_bit,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
def selectLive {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1 == 1 then w::selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws
theorem selectLive_sub {α : Type} (bits : Nat) (ws : List α) : (selectLive bits ws).Sublist ws := by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold selectLive
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)

def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := packedAt data (i*width) width
  let stored := recp &&& ((1 <<< len)-1)
  let ops := stored
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)

def getFieldV (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)
def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more := chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 8 2,(bank.getD (ops &&& 15) defaultDecor).1,
        (bank.getD (getFieldV ops 4 4) defaultDecor).1) :: more

def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  match g.bonus ops d bank idx paid with
  | some c => some c
  | none => (g.cols.read idx).bind fun ci =>
      materialize (vars g.mask) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases eb : g.bonus ops depth bank i paid with
  | some c' =>
    rw [eb] at h
    cases h
    exact g.safe _ _ _ _ _ _ eb
  | none =>
      rw [eb] at h
      cases e : g.cols.read i with
      | none => simp [e] at h
      | some ci =>
        simp only [e,Option.bind_some] at h
        apply materialize_sound _ h
        exact cols ci (g.cols.read_mem e)

def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)

def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)

theorem linkedSet_sound (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair = some out) :
    Impossible (targetOf g) k out.toFinset := by
  unfold linkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (by simpa using Array.mem_of_getElem? e))

def extra3853 (g : Forest) (k tag : Nat) : List (Nat × Nat) :=
  if g.mask=191 && g.cap=11 && k=9 && tag=5119942909039037862 then [(575,0)] else
  if g.mask=191 && g.cap=11 && k=9 && tag=5119817798203851252 then [(78,0)] else
  []
def ifUseful3853 {α} (flag : Bool) (xs : List α) : List α :=
  if flag then xs else []
theorem ifUseful3853_mem {α} {flag : Bool} {x : α} {xs : List α} :
    x ∈ ifUseful3853 flag xs → x ∈ xs := by
  cases flag <;> simp [ifUseful3853]

def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ifUseful3853 (iw != 63 || nl != 0)
    (((g.index k tag).bind (linkedSet g (k-1))).toList ++ (extra3853 g k tag).filterMap (linkedSet g (k-1)))
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov ws,rules,ls) ws)

theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i = true) : Impossible (targetOf g) k (stateSet g k i).toFinset := by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t u lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    cases h
    exact hT (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound g cols h
  · intro tag xs hx
    rcases List.mem_append.mp (ifUseful3853_mem hx) with h | h
    · have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa using h
      obtain ⟨pair,_,v⟩ := Option.bind_eq_some_iff.mp e
      exact linkedSet_sound g _ names (prior (by omega)) v
    · obtain ⟨pair,_,v⟩ := List.mem_filterMap.mp h
      exact linkedSet_sound g _ names (prior (by omega)) v


def block (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerified g k (start+n) && block g k start n
theorem block_at {g k start n} (h : block g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    nodeVerified g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [block,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem block_merge {g k start a b} (h : block g k start a=true)
    (h' : block g k (start+a) b=true) : block g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩

def checkedTables (g : Forest) (top : Nat) :=
  ∀ k ≤ top, block g k 0 (g.levels k).1 = true
def graphValid (g : Forest) (prior : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 768) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.values.all (fun c => colCheck g.mask c prior) &&
  g.autos.toList.all (fun p => autoOK (targetOf g) (p.map swapRows))

theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact block_at (rows _ hk) i (by omega) (by omega)

def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws
theorem root_index {g top prior k i ws} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1

theorem lower_forest {g prior i hints} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

theorem lower_discard {g prior ci hints} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck g.mask ci prior = true)
    (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask)
    (nd : (vars g.mask).Nodup)
    (cut : poolCut (subcube ci.1 ci.2.1) ci.2.2.2.2 g.cap 0 (vars g.mask) (vars g.mask)=true) :
    Lower (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) _ (poolCut_sound (col_sound ci prior low ok) [] rfl nd cut)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def Known (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower (vars e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (relabels : List (Nat × List Nat)) :=
  relabels.map (fun v => (v.1,L)) ++ old
theorem extendKnown_ok {old L m relabels} (previous : Known old)
    (main : Lower (vars m) (graphGoal m) L)
    (ok : relabels.all (fun v => relabelOK v.1 m v.2) = true) :
    Known (extendKnown old L relabels) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact relabel_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known [] := by simp [Known]
def lanePlace (v : Nat) (upper : Nat) := 2^769*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^769 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem lanes_and {α} (f g : α → Bits) (xs) :
    combineLanes f xs &&& combineLanes g xs = combineLanes (fun x => f x &&& g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_and,ih]
theorem lanes_or {α} (f g : α → Bits) (xs) :
    combineLanes f xs ||| combineLanes g xs = combineLanes (fun x => f x ||| g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_or,ih]
theorem lanes_xor {α} (f g : α → Bits) (xs) :
    combineLanes f xs ^^^ combineLanes g xs = combineLanes (fun x => f x ^^^ g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_xor,ih]
theorem broadcast {α} (a : Bits) (xs : List α) :
    units xs.length * a.toNat = combineLanes (fun _ => a) xs := by
  induction xs with
  | nil => simp [units,combineLanes]
  | cons v xs ih => simp only [List.length_cons,units,combineLanes,lanePlace,Nat.add_mul,Nat.mul_assoc,ih,Nat.one_mul]

def fullMarks (r packed : Nat) := ((packed+r) >>> 768) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (769*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^769)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 769*(i+1)-769=769*i := by omega
      have ge : ¬769*(i+1)<769 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 768 = (a==BitVec.allOnes 768) := by
  by_cases h : a=BitVec.allOnes 768
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^768-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^768 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (769*i) =
      (f xs[i]==BitVec.allOnes 768) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^769*u+x+(2^769*v+1)=2^769*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^769 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬769*(i+1)+768<769 := by omega
      have di : 769*(i+1)+768-769=769*i+768 := by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)


abbrev PackedSig := Nat × Nat
abbrev PackedCov := Nat × Nat × Nat

def packedSig {α} (s : α → Signals) (xs : List α) : PackedSig :=
  (combineLanes (fun x => (s x).1) xs,combineLanes (fun x => (s x).2) xs)
def packedCov {α} (c : α → Cov) (xs : List α) : PackedCov :=
  (combineLanes (fun x => (c x).1) xs,combineLanes (fun x => (c x).2.1) xs,
   combineLanes (fun x => (c x).2.2) xs)
def packedColumn (d : Bool) (a : PackedSig) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2

theorem xor_meet (a b : Bits) : a ^^^ (a &&& b) = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem packed_column {α} (s : α → Signals) (xs : List α) (d : Bool) :
    packedColumn d (packedSig s xs) = combineLanes (fun x => column d (s x)) xs := by
  cases d <;> simp only [packedColumn,packedSig,column,Bool.false_eq_true,ite_false,ite_true,lanes_and,lanes_xor,xor_meet]

def packedOp (full : Nat) (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=2 then (full ^^^ a.1,full ^^^ a.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else (a.1 &&& b.1,a.2 &&& b.2)
theorem top_xor (a : Bits) : BitVec.allOnes 768 ^^^ a = ~~~a := BitVec.allOnes_xor
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp (units xs.length*(BitVec.allOnes 768).toNat) op
      (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (movedDecor op (a x) (b x)).2) xs := by
  by_cases un : op=2
  · simp only [packedOp,un,ite_true,packedSig,broadcast,lanes_xor,top_xor,movedDecor,codeDecor,dneg]
  · by_cases one : op=1 <;> simp [packedOp,un,one,packedSig,lanes_or,lanes_and,movedDecor,codeDecor,dbin]

def takePacked (c : PackedCov) (a b : Nat) (un ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if un then (if ka then c.1 else without1 a)
  else if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2

theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (un ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) un ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) un ka kb) xs := by
  cases un <;> cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]

def contextWire (c : NodeContext) (i : Nat) := c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  evalMove c op a b (movedDecor op a b) ka kb
def combField (c : NodeContext) (d un ka kb : Bool) (op i j : Nat) :=
  let a := contextWire c i
  let b := contextWire c j
  restCov (getCov c.2.2.2.1 d) (column d a.2) (column d b.2) un ka kb |||
    column d (movedDecor op a b).2

def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 769) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (769*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0 := by intro e; simp [e] at bitOn
    simp only [onMarks,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
    cases i with
    | zero =>
      have nonzero : mask &&& 1 ≠ 0 := by
        intro he
        have at0 := congrArg (fun n : Nat => n.testBit 0) he
        simp only [Nat.testBit_and] at at0
        change mask.testBit 0=true at bitOn
        simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i =>
      apply ih (mask:=mask >>> 769) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn

abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs,packedCov (fun c => c.2.2.2.1.2) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]

def availableMasked (p : BoundPool) (m : Sig) :=
  m==zero || m==p.domain || (p.wires.map (masked p.domain)).any (fun v => v==m)
theorem available_mask (p : BoundPool) (x : Sig) :
    availableB p.domain p.wires x = availableMasked p (masked p.domain x) := rfl

def constantLoss (p : Decor → Bool) (a : Decor) (keep : Bool) :=
  if keep then 0 else (p a).toNat
theorem lossBound (p : Decor → Bool) (ws : List Decor) (a : Decor) (keep : Bool) :
    ws.countP p ≤ (delOne ws a keep).countP p + constantLoss p a keep := by
  cases keep
  · simp only [delOne,Bool.false_eq_true,ite_false,constantLoss,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [delOne,constantLoss]

theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b (un || kb) ≤
    (opKeep un ka kb a b ws).countP p := by
  have h1 := lossBound p ws a ka
  have h2 := lossBound p (delOne ws a ka) b kb
  cases un <;> simp only [opKeep,delTwo,Bool.false_eq_true,ite_false,ite_true,
    Bool.false_or,Bool.true_or] <;> first | omega | simp [constantLoss]; omega

abbrev QuickPool := BoundPool × Nat × Bool
def summarizePool (ws : List Decor) (p : BoundPool) : QuickPool :=
  (p,ws.countP (fun w => isMaskedConstant p.domain w.1),
     ws.all (fun w => availableB p.domain p.wires w.1))
def fastCost (s : QuickPool) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) :=
  if !s.2.2 then false else
  let p := s.1
  let un := op==2
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := choiceVal (movedChoice op a b)
  let zm := masked p.domain z
  let zc := isMaskedConstant p.domain z
  let cm := s.2.1 - constantLoss const a ka - constantLoss const b (un || kb) + zc.toNat
  let free := zc || zm==masked p.domain a.1 || zm==masked p.domain b.1
  decide (k+p.paid+(!free).toNat < p.bound+cm)

theorem fastCost_good {p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws)
    (h : fastCost (summarizePool ws p) k a b op ka kb=true) :
    scalarPoolCut p k ((opKeep (op==2) ka kb a b ws).map Prod.fst) (movedChoice op a b)=true := by
  let z := choiceVal (movedChoice op a b)
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let free := isMaskedConstant p.domain z || masked p.domain z==masked p.domain a.1 ||
      masked p.domain z==masked p.domain b.1
  let rest := opKeep (op==2) ka kb a b ws
  have ck := keptCount const ws a b (op==2) ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b ((op==2) || kb) ≤ rest.countP const at ck
  by_cases all : ws.all (fun w => availableB p.domain p.wires w.1)=true
  · have hav := List.all_eq_true.mp all
    have ready : free=true → availableB p.domain p.wires z=true := by
      intro f
      simp only [free,Bool.or_eq_true,beq_iff_eq] at f
      rcases f with (zc|za)|zb
      · simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
        exact Or.inl zc
      · rw [available_mask,za,←available_mask]
        exact hav _ ha
      · rw [available_mask,zb,←available_mask]
        exact hav _ hb
    have extra : (!availableB p.domain p.wires z).toNat ≤ (!free).toNat := by
      cases hf : free <;> cases he : availableB p.domain p.wires z <;> simp_all
    have hs : (rest.map Prod.fst).all (availableB p.domain p.wires)=true := by
      apply List.all_eq_true.mpr
      intro _ hm
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
      exact hav w ((keep_sub ws a b (op==2) ka kb).subset hw)
    have opOK : choiceOK p.domain p.wires (movedChoice op a b)=true := by
      simp [choiceOK,movedChoice,hav _ ha,hav _ hb]
    simp only [fastCost,summarizePool,all,Bool.not_true,Bool.false_eq_true,ite_false,decide_eq_true_eq] at h
    change k+p.paid+(!free).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b ((op==2)||kb)+(isMaskedConstant p.domain z).toNat) at h
    dsimp only [rest] at hs
    simp only [scalarPoolCut,hs,opOK,Bool.or_true,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
    change k+p.paid+(!availableB p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
    cases hc : isMaskedConstant p.domain z <;> simp [hc] at h ⊢ <;> omega
  · simp [fastCost,summarizePool,all] at h

def quickAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  (c.2.2.2.2.1.map (summarizePool c.2.2.1)).any (fun s => fastCost s (c.1-1) a b op ka kb)

theorem quickAt_good {c i j op ka kb} (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length)
    (h : quickAt c i j op ka kb=true) : checkAt c i j op ka kb=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
  have closed := fastCost_good (mem _ hi) (mem _ hj) ok
  have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut p (c.1-1)
      ((opKeep (op==2) ka kb (contextWire c i) (contextWire c j) c.2.2.1).map Prod.fst)
      (movedChoice op (contextWire c i) (contextWire c j)))=true :=
    List.any_eq_true.mpr ⟨p,hp,closed⟩
  simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
  repeat' split
  all_goals rfl

def fallbackAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  (if i<c.2.2.1.length ∧ j<c.2.2.1.length then quickAt c i j op ka kb else false) ||
    checkAt c i j op ka kb
theorem fallback_sound {c i j op ka kb} (h : fallbackAt c i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true] at h
  rcases h with h | h
  · split at h
    next yes => exact quickAt_good yes.1 yes.2 h
    next => contradiction
  · exact h
def batchMove (b : Batch) (xs : List NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,u,v) := b
  let un := op==2
  let len := 1+(n-(if ka then 0 else 1)-(if un || kb then 0 else 1))
  if len>k then true else
    let d := len==k
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp (r*(BitVec.allOnes 768).toNat) op a b'
    let cov := if d then v else u
    let mask := fullMarks r (takePacked cov (packedColumn d a) (packedColumn d b') un ka kb ||| packedColumn d z)
    onMarks (fun c => fallbackAt c i j op ka kb) mask xs

theorem batchMove_at (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n)
    (pass : batchMove (makeBatch k n xs) xs i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1))
  let d := len==k
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] d (op==2) ka kb op i j != BitVec.allOnes 768 then true
      else if !properB (movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((opKeep (op==2) ka kb (contextWire xs[q] i) (contextWire xs[q] j) xs[q].2.2.1).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt,evalMove,budget,arity,len,d,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := if d then packedCov (fun c : NodeContext => c.2.2.2.1.2) xs
            else packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn d a) (packedColumn d b) (op==2) ka kb |||
        packedColumn d (packedOp (r*(BitVec.allOnes 768).toNat) op a b))) xs) = true at pass
    rw [if_neg small] at pass
    have chosen : cov = packedCov (fun c => getCov c.2.2.2.1 d) xs := by
      dsimp only [cov]
      cases d <;> rfl
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,chosen,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] d (op==2) ka kb op i j = BitVec.allOnes 768
    · apply fallback_sound
      apply marked_ok _ _ _ q hq _ pass
      rw [mark_at _ _ _ hq]
      exact beq_iff_eq.mpr hit
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]


def batchPair (b : Batch) (xs : List NodeContext) (i j op : Nat) :=
  let f := batchMove b xs i j op
  f false false && f true false && f false true && f true true
def batchRow (b : Batch) (xs : List NodeContext) (i : Nat) (js : List Nat) :=
  batchMove b xs i i 2 false false && batchMove b xs i i 2 true true &&
    js.all (fun j => batchPair b xs i j 0 && batchPair b xs i j 1)
def batchRows (b : Batch) (xs : List NodeContext) : List Nat → Bool
  | [] => true
  | i::js => batchRow b xs i js && batchRows b xs js

theorem batchRows_at (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows (makeBatch k n xs) xs js=true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    have check := @batchMove_at k n xs
    refine ⟨⟨⟨check hi hi hq budget arity allRows.1.1.1,check hi hi hq budget arity allRows.1.1.2⟩,?_⟩,
      ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    have both := allRows.1.2 j hj
    have opCheck (d : Bool) (pass : batchPair (makeBatch k n xs) xs i j (if d then 1 else 0)=true) :
        testPair xs[q] (contextWire xs[q] i) (contextWire xs[q] j) d=true := by
      simp only [batchPair,Bool.and_eq_true] at pass
      simp only [testPair,Bool.and_eq_true]
      exact ⟨⟨⟨check hi hj' hq budget arity pass.1.1.1,check hi hj' hq budget arity pass.1.1.2⟩,
        check hi hj' hq budget arity pass.1.2⟩,check hi hj' hq budget arity pass.2⟩
    exact ⟨opCheck false both.1,opCheck true both.2⟩

def runBatch (k n : Nat) (xs : List NodeContext) :=
    batchRows (makeBatch k n xs) xs (List.range n)
theorem runBatch_at {k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hn : xs[q].2.2.1.length=n)
    (pass : runBatch k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (contextWire xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [contextWire,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all

def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ifUseful3853 (iw != 63 || nl != 0)
    (((g.index k tag).bind (linkedSet g (k-1))).toList ++ (extra3853 g k tag).filterMap (linkedSet g (k-1)))
  (k,ws.length,ws,preCov ws,rules,ls)


def prelim (T : Sig) (c : NodeContext) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
theorem from_context (g : Forest) (k i : Nat) :
    nodeVerified g k i = (prelim (targetOf g) (contextOf g k i) &&
      (if k=0 then true else testAll (contextOf g k i) (contextOf g k i).2.2.1)) := rfl

theorem makeBlock {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → nodeVerified g k i = true) :
    block g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩

def contexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (contextOf g k)
def header (g : Forest) (k start n ar : Nat) :=
  (contexts g k start n).all (fun c => c.2.1==ar && prelim (targetOf g) c)
def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  (List.range len).all (fun d =>
    let i := lo+d
    batchRow b xs i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (makeBatch k ar (contexts g k start n)) (contexts g k start n)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha

theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)

theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (makeBatch k ar xs) xs (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := rowCut_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)

theorem cutsBlock {g k start n ar} (hd : header g k start n ar=true)
    (h : rowCut g k start n ar 0 ar=true) : block g k start n=true := by
  apply makeBlock
  intro i lo hi
  let xs := contexts g k start n
  have hm : contextOf g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hn (cutsRun h)

def boxes (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d ∧ boxes g k start n ar (lo+num/2) (num-num/2) d
theorem boxesCut {g k start n ar lo num d} (h : boxes g k start n ar lo num d) :
    rowCut g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := rowCut_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v

def cells (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true ∧ boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d ∧ cells g k (start+n/2) (n-n/2) ar rows d
theorem cellsBlock {g k start n ar rows d} (h : cells g k start n ar rows d) :
    block g k start n=true := by
  induction d generalizing start n with
  | zero => exact cutsBlock h.1 (boxesCut h.2)
  | succ d ih =>
    have v := block_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v

def listPieces {α} (f : α → Bool) (xs : List α) : Nat → Prop
  | 0 => xs.all f=true
  | d+1 => listPieces f (xs.take (xs.length/2)) d ∧ listPieces f (xs.drop (xs.length/2)) d
theorem listPieces_all {α f xs d} (h : @listPieces α f xs d) : xs.all f=true := by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap : ((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true := by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap
def g15d3 (i : Nat) : Nat := 0xf
def g15l3 : Packing := (1,0,0,0,1,0,0,g15d3)
def g15samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbaf3ea78de4d799d,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff450cc90c3c245919),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdf7ff8fe9f9b7ed5,0x20812421801324c4),(0xefbdbf97f9f6bf6a,0x102a401415600a0a),(0xf3a9d7437375f5ba,0xfc028ab620235b0),(0,0),(0,0),(0,0),(0,0),(0,0)]
def g15columns : IndexTree ColumnInfo := (.leaf [])
def g15autos : Array (List Nat) := #[[],[33,48]]
def g15levels : Nat → Packing
  | 3 => g15l3
  | _ => emptyPacking
def g15index : Nat → Nat → Option (Nat × Nat)
  | 3 => fun _ => none
  | _ => fun _ => none
def g15 : Forest := ⟨15,3,fun j => g15samples[j]?.getD (0,0),g15columns,g15autos,g15levels,g15index,noFactory,noFactorySound 15⟩
def key31l6 (i : Nat) : Nat := 0x820007028af371d000003180048302e380000000003819155875690d58000003d
def g31d5 (i : Nat) : Nat := 0x84001e90fd02fd01fa00
def g31l5 : Packing := (3,1,3,0,4,4,0,g31d5)
def g31d6 (i : Nat) : Nat := 0x11a20bf
def g31l6 : Packing := (1,0,3,2,4,0,0,g31d6)
def g31samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdafffab2d55fb9f999d9ceeefacb357b78f9ce2bb554a3bac97b2a9d65,0x250142092220460600407048c382809c2160e048740030a88143281c44),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffef5dfed46f26fea572a7ba9effd7341aff97ad1ab5bd2d547d6793334b,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff90aa211010d10141c4300836206168204010183680184d04682483210b),(0x73ef3f3c8ff8df3fe567b556c9567ffcd665219778a6bd6e36bfd946ac,0xc10d0c3000214920a0d648109801012344d60802686b04210115006a4),(0x7c7fd57b7ffa3476e74d6f3fc4bddbd44dc213c5eb8bdea95bf6ee7492,0x38022048645c06490200044a25241818912934541000824c322ae5002),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8fe76ff6451fda6ff84b6daf38f5bb6f6a5ee88a4d6be3f71c64aa3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8076989008882001270e063010011622500c04308a174300141c40a239),(0,0),(0,0),(0,0),(0,0)]
def g31columns : IndexTree ColumnInfo := (.fork 2 (.leaf [(1,0,30,0,4),(2,0,29,0,4)]) (.leaf [(4,0,27,0,4),(8,0,23,0,4),(16,0,15,0,4)]))
def g31autos : Array (List Nat) := #[[],[50,65],[66,16],[67,50,33,16],[67,32],[67,66,49,32],[33,48],[67,50,65,48],[67,66,65,64],[49,64]]
def g31levels : Nat → Packing
  | 5 => g31l5
  | 6 => g31l6
  | _ => emptyPacking
def g31index : Nat → Nat → Option (Nat × Nat)
  | 5 => fun _ => none
  | 6 => lookupWord 5 25 2 10 2 4 (key31l6)
  | _ => fun _ => none
def g31 : Forest := ⟨31,6,fun j => g31samples[j]?.getD (0,0),g31columns,g31autos,g31levels,g31index,noFactory,noFactorySound 31⟩
def g47samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffddffff5cfaafae7dd35b9ce7bbffd6b6b7b7cfbb8d3b7ad85ddf257b56b575,0x2200a042011011800c00803812181c2009c1061c0107200c09440143143444),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeebefed537937fcb8ab173daa7df7f7691aff9776b2b7dcb92a3f3678b2b59,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9149112428688034a38448020d64a21d120601022ea84882b022a624830919),(0x77db9fef67fc77f3ffe6e3dd55f86b6fffcab66472f7c57fb768dabfad4eae,0x820641080010508440806b120004c020121a4ec1002247c020840112806a4),(0x78ebe4ae9ffd0d576de696b3cff805db7d426c00d8ded437ed436ff6f66c92,0x71419416322f057a950700411b6b328381c4110e8d4580325370f22d66812),(0,0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0bf9ebdb2287acd4afec26dbb6d98eabb3768bb508ca4b7f1fdd1c709a3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80f74f1424444852a26637058ca3a012d22680c12e48c8e17411561c608a3b),(0,0),(0,0),(0,0)]
def g47columns : IndexTree ColumnInfo := (.leaf [(8,0,39,0,4)])
def g47autos : Array (List Nat) := #[[],[83,32]]
def g47levels : Nat → Packing
  | _ => emptyPacking
def g47index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g47 : Forest := ⟨47,4,fun j => g47samples[j]?.getD (0,0),g47columns,g47autos,g47levels,g47index,noFactory,noFactorySound 47⟩
def g55samples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffdf7defdfafbfd3fcebcfdeffcebffefe76de77fed7f1773f95eb2ebeb,0x400028000010005000000400701010180030103060043200102204010904888),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdb7fbfbb9ad3afd94caf0b9db5bbdf7f7d39bfcdadcf77ec9eccd2fb9cf16b5,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2484444214284026a4e002420468a8a43140a00408d944460a4082569431231),(0xeda5e7e7b2fc29de4ffc371dba2bf0775ff12db9b18bb528fedad96afcd3c5e,0x12589919410293410206d0396285445a082c5d2bf0022b20f0895d2048c2c4e),(0,0),(0xf1cd79264efe956afa7a64bb677ab40beba463600362eda36f3357b7d763926,0xe3a8651b1a36a0acc57538a080f6ea703078a0c13c28dc34c91f3868663126),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe05fe74eda341d5872cbf684d5e2ed19e7e3bba5e964550dd792aec724f479,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01fb53db1204342a549861b60b6727a22d48ac0b14da4445855161ae724b471),(0,0),(0,0),(0,0)]
def g55columns : IndexTree ColumnInfo := (.leaf [(16,0,39,0,4)])
def g55autos : Array (List Nat) := #[[],[84]]
def g55levels : Nat → Packing
  | _ => emptyPacking
def g55index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g55 : Forest := ⟨55,4,fun j => g55samples[j]?.getD (0,0),g55columns,g55autos,g55levels,g55index,noFactory,noFactorySound 55⟩
def g63samples : Array (Bits × Bits) := #[(0xdabffdfdbdf61bfbfc7dcbe34f7f1b17917df75df7edd9eff77b6dbd3dcebed3cfbfaddba50fcabded46bc9b579eb7bd3d92776566ad4ad3debe36d74deb7f9faf189ad76da7dc1a6b4eaf21eb254de4ae1f7451bb34d9456fd18e934db17349,0x4400202400040800310000100084000ac0000102800a1100490002240004b2800a001b4000190000008108000574009200040400000594000190004218c0010840002890800550053044a00410008802d0060013000c004400188120c206208),(0xb6678efeffcbf5a9cad5bfd527a7a5bd74d1314b7915f5b2ffdec2fc5d978f8ab3b44b2b5add5b771711b15ce99bf2b3f5bce975ef94cd59a34e76ab937848a94ef6be6c9579db5905539ea703c87a7d4ae11fe2ae423fade4a3c3299b0724e7,0x499461811a200a55004cf88854029340027a680613c002ec00233c1096d01045025d0203d400243150030b7e4900b00499e023395882049d0206ec00041398010bbb1000b7310ad00cc0858112c8207810e917400e423d0034024309910504e5),(0xbfdd27bedf8fade4776ebf9d185bc5bd76aeffb29711f77d628e86e5fffdff6d1a52bff6da987348e3e147dcecdbcc68d1accc4e7d7d77b9734cfbbcefbc022d72eff5a31a72e32584dd5a72accb1256ede309af577ea6b3ab2be572a2769632,0x20983204990108b1910222a2810c12a8041040402e00006394000908008912a582448429aad10a21a0240190b504314209040621245140c82010e8812042049440841100c0c52080310832a5111106e902488a012c82618908a42202729212),(0x77ddb87389d95f9f7bbe7e8eb89e6e76fbf75ca7fd5bb3758b555b578affe964ae7e7fa493e06d03bebc4fb5cff51e46b2dd5bdbb1eab66f60f7d916b9c6944fd85b6f0fc30a2ae7d2afc9dc369ef80bb1b0b2dd52e9331e786f7a5d38e8c8b4,0x1482478012444200420888514440810c402202189081ecc814422aa4c048408050190921c0450c000a080254044021081134422900082c11250884167012813a48094aca870a3283708e41084282480000c012150640581c30655a55288040a4),(0xdca768aafb78ce8d2db2ec3fbdddfa4ec963339dbac7a8e05eccbf0bb99ddf5febcef6dc7762a4a79d9ad8f70324ba6e724754bded1eed86f695f276b70acbd73dc66e39a88d0cfed920a0ee10b5a4dd5893bba709bff6dc1ece388c561e1ed5,0x210938550593284a984457082a220ca002159526023c0223a02100100d271046aa46f2022bb0201ea5730921b3008e848a002106a7520082d20653c8040064810364a00030c5086c0c2084761035a077101508a009ba22e00b822088521e1c51),(0x77dad76bd4ced656e7ec247a694c9eb5b66dc4de71aac18acebb177a9bac7a62d6f3e3996dd9d62d6ecf7b18557229a30b5ebb1ef46b568a8f3400a7c2d3365caade63d0f2234a24623735bcfaee29c0664eddfc63b2a86915f817ca03dc41fa,0x88252894b2b3256598a758928465236453b27d28c68c4c28a24dcc0d24d500d4a845700845b04bd175706d345a20a0a24d641d897dd822a1d52444cad2629c8e732b305273362844202335b73c8d8150424e93e44a78286995ec17c803dc01f2),(0,0),(0,0),(0,0)]
def g63columns : IndexTree ColumnInfo := (.leaf [(32,0,31,0,7)])
def g63autos : Array (List Nat) := #[[],[50,65]]
def g63levels : Nat → Packing
  | _ => emptyPacking
def g63index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g63 : Forest := ⟨63,7,fun j => g63samples[j]?.getD (0,0),g63columns,g63autos,g63levels,g63index,noFactory,noFactorySound 63⟩
def g111d6 (i : Nat) : Nat := 0x120ff
def g111l6 : Packing := (1,0,2,0,1,0,0,g111d6)
def g111samples : Array (Bits × Bits) := #[(0xeafcc7b96fc59ffd26c5e2bb3d7bd378fb35ff5dcb26f92afa5f57eff59a73b7aaa379b2fc8d7a99e2ef9efcf4defd4efabc9c89733cebade5579ad5abbcd64d8557ad3d63bd1c6a75510ce3b9bf05e462ee0edf6dfb2914efc74c7d31727465,0x4d00310a2003881269402d0c00406ccc142a8012908082d00025ac006a88036948003229000032d4001bf20024ec2018680000aaf2500325400423a6f02003840040a8016ea8106822700071012c01d500600ad401ea0010f407087831504444),(0xf771ad34ff2bcf4fbd7f5f5de52efaeb7ebbabfffefbf2eab7c7cf56f8ecea565ddfabcf87cb61db9d6ef4aecff7cebd76fe679cfb9935e6adabc77cdcdb677ed3da5e4f56b4cbe39cfd7aed1f519a6b999796b48a51f4f7b8ad91a66cc6d9cb,0x1204940050200482000010001c10308054448009004424020800871400ac0690000402004e0508404004081210450414000904018220d090010808000a44280600460810104d92040818880c1010088d8400200a10a1400808810604821909),(0xf5be76df5e79b8b5d13f5f6e3ecd176fbeee538a7cfb9f7f6b7fad9b13bb7fed97560ecd71f29f3f1e3ef959a338e3a9e32bd5e7cfc7b51df73d7e9e165479b3baa9a0d59e62e11eead3ad5c624777de8699f96d3766d64d1f3fa2ca8f3d2e52,0x8e4d19200884440101e4a802e100a0c04000830eb000289800c49240c1c411082c325a6812b0485430294040c52402008322a4b0e00c0021216842103a050a9080848145264020288841a770220547500211500d95204c05521120880b352452),(0xde2ebbc73c1cf83c4cedbed77297d7f5b666582db23d5c5d7bf4a54b37a75f4992f88d683d388ea5bafb57791a5deb9b257390777cf70e9d329773c24416edd93fe3d2909bc3b81d7e62dd94d70a759eb42b6b51587d63da2e7eea6ce78912bc,0x10b22099c5638280b403142808691e02bd9d04d1097a9640ce2041351e20e64283892100494815238b12089820999d9858901b4e1903515e001721098578a5416f515492d981d895722018845902b08a5c4a2a2248dd03d08c66ca64e48812ac),(0,0),(0x4a99db5e74fdf3bbfb83b4b12e735e58f515867b75942dba656f9eeac55739b971685432ece5b39368c30fbbb9f895ca9efa5eceda2fea7be4766f052ba5def635ccf928215f7640050f6846acafb2ca6efbba0bffbfdb9043d87d111c3c3ebd,0x12d68401de50564414b80023f49c0203c0413d800068400bbb08034f0177ac0427f40400f6de0023bcc009fc1201950403ff4900082ea08a2fc908010c8a4053de0011e801464d050407f806ac13f8026d9b800bfa055d40038875010c2c3ab9),(0x107b7e8791b6519a9ebd6f37d374faa298392ebad8b5e4afe6bd267679568b3365bebaabdf6ef4e9035a918e8ca50ef74769b2b74aea726a09a6c5e9463715fb76745a9b1b6212a1b9add6dec52a9ba55b57e399ab660ca6d0f217384af881fe,0xadc48a6a24248ac9294916cc74a18dce4988890976a839d0a90054480a8f001149b409fd5690d8d50882129489ae3083c83b5253565cd02541ca4550f495b985581508b28aaa022919a1e755a00eaaa54243a315f06a0c87d4f216384a7880f6),(0,0),(0,0)]
def g111columns : IndexTree ColumnInfo := (.leaf [(4,8,99,0,4),(1,32,78,0,4),(64,0,47,0,5)])
def g111autos : Array (List Nat) := #[[],[83,32]]
def g111levels : Nat → Packing
  | 6 => g111l6
  | _ => emptyPacking
def g111index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | _ => fun _ => none
def g111 : Forest := ⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index,noFactory,noFactorySound 111⟩
def g119samples : Array (Bits × Bits) := #[(0xfab75f3dfbfa3756f92d9ff7baf5ff7dbfebb9b33bef7dcdf77fbffe7bbbf75546cedccfd6f7eb762bef3ffdd2ede7abbef7e4e4b775eb9be6ab6f4d5fde77f2b955ece57b3feb97c6d99b5cdd2fdd2ea315de5f3efbf8d44ddcaa7566eda9cd,0x20100000802449000a820000c1900042800052080010000098c000620802429000050a2000012e00000be20013404000082000047420011240000c8b8000110080002480036500158018000c4009400c9000c0062803a0400e00885042a10888),(0xaf7efcd6de9febfb57d6f5ddedde36f3db7fffeed79fdbfafcf255738c743cbbbff3e3b86b8f9fb9f5bdf54fbff79bd74f5afb3f7fba34f5bf5f9afae879ab5feefe93fa9ee6566f7bbee6bf67d426d75cfb2bace9344fabf72bd58e999b76b3,0x9300010000091004000400382060802420900110020801010208161810541520000000800198110400c004084880812115000049028020c0800220200009220a01801050108206a8408406120184808104430800802442850101410609083421),(0xd3aee9d1a16b8afb579b1b1a2ede96c634714fced4ed35afb8d86696aabedb2eada373270f48f3a9b93de8a90d87d8f6684756adef8eb40bf672fc78b9342c9c7aaa652b2aec9422dd38b32b2a5255bdcc3d35b2da5f372953f3c4ba3a70d996,0x2c07b23e74020fd2aa41748155856818d263d681015680dac92709c7448b08586eaf3a512642c64b613a9091954b38c222671d26711d023332d48951dd0691952839212f8b6888039910b9ac2a42653c283c65315b1b95185ae084b83270c996),(0,0),(0x759a506bc07865de6f37bc2fabe39a5e2705b6a3eec6bd3cca572e3ed72f0325f632aa43d8e0e833eaeab6f86ad5fa72dbaf9c83b9e70faa212acf122e177ae733d8fa39a0b0bb12b7915f7134c3b9a9ed98d75362b1d9c725676c3caf04637c,0x16e5f59c6d01a255c44806523c0cddb5529a2196d082e7c24415d298c0f10d071e6090549dc090f8ed501938009f3fb2169588d90b0b506d102e01343cb84ad135f45369a498be0a36011e712702bb816af81651c4b05c0701a6642cad046374),(0x6339c3e76f77dc41ec6c9766b8b0f93592cd6e58a17db2abb9eea5cd269eeae2dc2c1c9ec755bae6a2821f6b678c3538a75edaf56c57e97ff4e8b90d55c4e75ce36b37ac511be4c610c6f229b9ab77956345b3a117ef6f3608dd37697870ba61,0x84ef690f5888a6bc0049f9381c0ba0115db000874a075d2102333605e754184fe100105f739880fb92c019ec481f2d2102dbf2480954a0ad3f922114724920d57f80032e5018c6a22083e62199863ec06b43378157e41d3d00d937293850b261),(0xd5cc96ab2735f4eedbcfece9fd4d847149d75b8aa71ff3959066dc7566c66ecb75975abde9bb8d684d89311f3151135dd1ce4d97acd9737d0b4d97b62b1596cf57b51ab1b6b408593b67d5bb928b32dabad66fc43367241aeaae177095e247ea,0x481560b0cd924918c5323d4303992d88d1232e6a49f254a2454320824e8122936522ef3572424e688310332525616c12e023da92a435d213539c9243b254cc21b63548a8e4258841b361f1c95a017252ba1c47902bc1245a7a8e167094e243ca),(0,0),(0,0)]
def g119columns : IndexTree ColumnInfo := (.leaf [(4,0,115,0,5)])
def g119autos : Array (List Nat) := #[[],[84],[98],[84,98],[101,66,16],[101,100,66,16],[101,84,82,16],[100,82,16]]
def g119levels : Nat → Packing
  | _ => emptyPacking
def g119index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g119 : Forest := ⟨119,5,fun j => g119samples[j]?.getD (0,0),g119columns,g119autos,g119levels,g119index,noFactory,noFactorySound 119⟩
def key189l7 (i : Nat) : Nat := 0xa81337040d4b600002948880000590cc33d41450272020001b1
def g189d6 (i : Nat) : Nat := 0x82000f487f40bfa03fa00
def g189l6 : Packing := (3,1,3,0,4,4,0,g189d6)
def g189d7 (i : Nat) : Nat := 0x1f5859bf
def g189l7 : Packing := (1,0,3,2,4,0,0,g189d7)
def g189samples : Array (Bits × Bits) := #[(0x76b7b935ad7f6fd4d735f26d2df10ff4361bcad97bdde979efcd6e58b7554d7ea7eff73e73de92e56562d7533a4ef3de34b1f6acf1d6e216666babd43dbaabce3ad8d545ed4e53771cb4e6d84ab365f9722155b0decf672135d0ab0e8aab3265,0x8404642124899480a2a81184400c4494a40542200633c0114901482008a100b4c40690c02a500485280025a8300be5004d078022244028e4a0122910034dd0088624c002500565400b4701a401901a06a801c60d40e430038408b0c08aa0264),(0,0),(0xb725f7b34edfbeffaf8e64c99fca263eeb8ebd6e6efba6759d07fff35f0d57cf0f1af1c8e8596f2d9f9a363b65aade972ff9af593499366f72b4e55d5e6f961954d5fce693a74e66d370dbbd59357a0ab5d8c2e2b4913d9ddc0ac963246654eb,0x2019084c910042485050a84580141012107000421c10cd02a29a004c0424911090cb1414ac1a4012048a60a1130c00921224ba8854044c203120d1318881010110848d88109408245548f0845c253042044cc0e02091152804424943044214c9),(0x6b3b37beb0d3b3db67cafb77eb9e1dd789aebdb18d1db77732f653e35977f97f4dd313687fb67a399a5d29e7c5c2df2ae361e9d1a8a6a7bdf9b41bf76bf3c59c972736ba642a6ec8e10ddd388a5d8a2fef454b2f6c5cd8cb4dafd1a5458caf32,0x84c42401462a8882042c15880121e0040f09501440a3008044047580824b00c92204cb801220a2e8d004050a8c13a8082552010080e322ce0002224042220e86c96110212062d680201609100358082de8010e0a0c4e080169249024018caa32),(0xeed4ecfef66eeb7efebdd9aee7077cf1671b7b7a97dfdfd372d0ed94ede3ade9c50737565e265d36d07689d4ac4faafe5abbfdc5676e89f79f8f9a623b38502f3db98ff0fa982b81b88d0790fae9d8d74f74351d5187af7a955e769667c1914c,0x112b0124099000041080680538580102a03620812918016ca82b084951200b0011391441e40a1406003a00a460640102802906c05910d52121d05c00b8012058249003c452192901d049060038a0e052051c011422a1a0780618649266411108),(0xd9cafe65094bbf5f7264b7bbce3ffbefdc6762cbb35969c8ac2ddbae62ff5a5f3ee2cea13be5ccd265ed5a725a1921f7f9e712e69e98fb2d45e97fd5f2e0abe4f3f7676b375491bf662220c7ec1235aaa52f7b260bfdf8f023b73c589c1c3f19,0x2215018860a440b0408528403b942810a5b0009c1c080302094a000184016510830b02e2ac10b810014a60046c8c012e120b028809b84c0105208c4e88802201101131880274018a550300819c02301e012cc3000b90a8a80382305084143519),(0,0),(0xe9cbc8feffb7f8e7b8d17ff4f26deb6af5fadcfef4fa8da189aed6c66eadfbba567e7aa58acda76b57bfee9d03799233ac5e277f4fab9af55d736c18d65d30adcab7ab9d1b9dcbcc02d24b67373e9182d29baedd99bcc115aa3d04dc337a48be,0x1420360100482d00252a00a2440945244a022b202187302c44004bb2035a00002400090800450025fa000d1a80010240a950404582409154ca522280124a1c0c672a40054909a2500214036203d800a092812c0514244211e81d048c33284826),(0,0)]
def g189columns : IndexTree ColumnInfo := (.fork 4 (.leaf [(1,0,188,0,5),(12,0,177,0,4),(16,0,173,0,5),(17,0,172,0,4)]) (.leaf [(24,0,165,0,4),(33,0,156,0,4),(132,0,57,0,4),(160,0,29,0,4)]))
def g189autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32],[82,48],[84,115,82,48],[117,116,115,114,64],[83,114,64],[116,50,80],[117,84,67,50,80],[84,115,66,112],[66,112]]
def g189levels : Nat → Packing
  | 6 => g189l6
  | 7 => g189l7
  | _ => emptyPacking
def g189index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 5 18 5 10 2 4 (key189l7)
  | _ => fun _ => none
def g189 : Forest := ⟨189,7,fun j => g189samples[j]?.getD (0,0),g189columns,g189autos,g189levels,g189index,noFactory,noFactorySound 189⟩
def g127samples : Array (Bits × Bits) := #[(0x27ec63be833e95d9cd8b1b0f8c7b949b955ab7ff06f2f46fb53d19a8b89e2cf938ea5b637a679113a99b1a558cf5d3757100e2a2d92956b1df648864a3a84cf9f5aafcc4980f547cd2d2abacb351593072ded0ca36876c216b176a15583d3069,0x215000b22a840210400a1040082a19401000220004808d00802008c02014082088420800402688520818425544410445400040805130408104600820a3600c001020e0440008143510802b10a111102142440000168440214816081150281060),(0xd1272c7d4d43f0bd72e56dab39ddfe7c6a407c139e413a8c95b2f6c7134bd9d2e6151acc0f6f6e61aecc859cb80ab9d38d1f9c08bbd08127631b9fb156aefb042a9049abe4f27cdb8815184a3fa2b5dede495570df2830da3c38c46cf1426d13,0x806000d540888802080408280406213088804000000320c048631024209804006241648090164a10080940a08001912a8109004a2408004431a0101080453200880088a80c0004a880100481a02008819080040c10830122428406420422c11),(0x3757a63bdee4ba3fd3e2275cd925bbac4327c3605b6a92ba668b6b375f5956a61c0ee4c8b6382a0c726a8d674c1d24e187c7697b46618e9a3259ec9e635cb1935494676727a9c6a3df6b34450ca72f271676b8367562d5a985429aaa9a64d626,0xe190134200c030558e6885084d0788a40161e860830e0412a109c61098d030850809a9902628890c322a09e446182064058721691005078a1841cc5c6248a09654242521162044855722240404692506023498262462c48981029a8a9a244222),(0x7c12f7ae7cb67a121957d4766ab145360dad0baa714fd5dd4ad95b9245e39e4cff88a61691dd24ee5570ea624367b54a6aea5375c626bc6f4082772e38770d5a1955fa1dcb198b20afa8d659c70c9ab5dbb42b955b55e374e0f839c3068a9694,0x100b203118264280010702e3020864421484020c18c0438c4090018044060d7096401604915660c20151c00201478d0220604290c2020821402022221025140809114a0c4919231288809339110498f1918002911b15216460582041008a9494),(0x5f0ed2cab79191489f9794fa9f865222c0c45f4f23977137ba6ec87e2fb718cbcb3281372d8190b9e5b2713c276012285f3b185c628f375c96ee95cada25845527c7ad5b31bc018c667be7de6cdf9480211b73e5e0fc0e1e03a683a80feb2399,0x4e04900c0410144f3ce0e018c1840020605099a3823d30032c4ce03413c1e08c412481b32c810028f486342022205010179b1c44008d375c030cd5d908008055e282051134c40088667900c444ea04000013f960e0680e1a03a083a80f412309),(0x64ed11ab034e6565aa5f6f0a73fb2abb553e90eaf5f2056f4f2ad1a6a7112f3107edc462d825611a42150349a39be3bcbdfa3bf68749fd950e410251758bd0aaed7e1f93ab81b400f6cd22629068e5bc2da9dbde283bbf115009f3b1a197a662,0x46299909050b25a18c71e62a5095c63ecb8f04a3c26b60b927cda532c109201915ade64b3091412042050108b390e3bab9cb9877060097580a090251508bf2aae7571e1ba185a2088a6c00621068c596ada8d9f5a83bbf101009f3a0a197a602),(0xed72aa63cb994444b8dcf183254b4e7cee24db3ad729ab4a1ba98c700af5e5480459e832e1cc5750368c89edf172492ed4565f186db3259850f427f3943aea1f7b1d745054d56ed5059c9e36e00b68fdae413f628aa9c64ad98b04d0b38dd9ac,0x4400b2628be723745844a119668f0ccc9303b92a933d014173710ec9a0c0658c41596832a4cc13563c0629c5d4a2402c44020f584d31651810e10cda143b2c95631f726414156f15141896b3a1182c75a6e53b222aa1c648d9830490938dd1ac),(0,0),(0,0)]
def g127columns : IndexTree ColumnInfo := (.leaf [(32,0,95,0,8)])
def g127autos : Array (List Nat) := #[[],[101,66,16]]
def g127levels : Nat → Packing
  | _ => emptyPacking
def g127index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g127 : Forest := ⟨127,8,fun j => g127samples[j]?.getD (0,0),g127columns,g127autos,g127levels,g127index,noFactory,noFactorySound 127⟩
def key191l10 (i : Nat) : Nat := 0xa2d43b28d7001ab368009df79a6668d8a485480048c00a24000002900046192841e000000005078511fa7b8000001d8000000000050332001c2200008044
def key191l9 (i : Nat) : Nat := 0xb5d65558d2140ea31b806b286019a820212fb2e35aa613228a5a077246e6fc20ca1a41bb2d080a9c3e39f318874648000323b01b537426ceae26842215792e4b19e71cc72290229e7cad73d5f333056000d205f83e366a30000000d49821b1f1088000bb771a5c8c0000000000eb0000e0cb6ac6bec3c000c1b800347e18451880000012040006004d1cd8e0000001866e151a0000282800081e2a5e9518b100010bc00000030815564ae0000000000000ba722a1a34000000e6c5a954a6f09e6780014941d61a7112de27d595e7f09e40be3dc9678ab0bf3d70002c438a3dd4912345fe50900b4e481ecbbcceb07786be83e621d46430465b9b583a98309000098f882ae3a444b1d707c001bdad01b2c800179a0001f6d90464c82da1658b094500004b589e042e51604dd58429e06b90ff614389938aaeb6d12bb049522a72f25c09129e0463116174d50c3960b150c0a182d435d81d03dcbc0b346f3525916e494182a5649d22c9002ab560902d0004c5bd2828ce425700001e0842090d9c2ec56f6a2934aac61902201440c3800d7464005040d9808000b00120008008026140608781000c78f2e086830a0c98000580830000a023a002141e004000c001040a00380
def key191l8 (i : Nat) : Nat := 0x18cd14b25011e7225b26001876a3412158c6fc726c2320d6e3243bdd05603f1613ebb0007f7c604089b00125f5892200bf9421800b5e245039f1cf3cb8436d7f2000047800310000002025492575bf0012c00000042000001b8021c00800c01d000c080081
def key191l7 (i : Nat) : Nat := 0x2c
def g191d6 (i : Nat) : Nat := 0x47d6448788a00
def g191l6 : Packing := (1,4,6,0,2,0,0,g191d6)
def g191d7 (i : Nat) : Nat := 0x1021aae2c480c58812165850610304200048200685020d100000000000200100000fce5cec0b2a49f918c877974664f4a45403b36312c2722140f0a0500fd51548d13edd3641903fd51544d03fe92540d02df57305d02ff10305d02df4179dd02bf5819dd02df5819dd029fd819dd02df5155cd019fe885c901fe92440901ff114409019fc8788a009bd849dd039f5819dd02ed6668ce11f56558ce119f47840a11f3a5591200eda668ce00f5a558ce00bb9841ca00fca3388a00fb24484600fd23384600fe22284600
def g191l7 : Packing := (28,3,6,0,2,8,0,g191d7)
def g191d8 (i : Nat) : Nat := 0x850910304081c2440c0e2128f09183458e0d563c424bf1e12406128b1c7846402045834a31022c1244b4112285081c2449f022410c0418818084041a2060210127868c180849614f082043003c28008103c00a001050011a0c10d03085c404064a2030a0610180108a409488504804aab1e40a0610805408d7f063c2499716b62841c098f1800a084818401971629005810a08556544b736241080077f04053c18a8a2824181120efe78c80844603045000e102828008e8b070510443840106263000efe5858a100024042202241d09811e292070e043021810a5c588002801000c0052e2c5001418110006003021810c08516144821810a085042001810afc7897e3c49e14f0a7850604482184f83a8258107f37d67c179c77f77274572070b6f66e16cc6bf6aa69568066b64e63962c61f61a60d5f85e35ce5b95ac59758256d55053b50e4f94d44bf4a247d45843b4264113e43d73ca3b53a039338635934432f3122d52c02b328e27925c24f22a21d1f81db1be1b11a419718217516815b14e13912c11710a0fd0f00e30d60c10b40a709a08d08007305e04903c02f02200d000ffa4c91ffd0548ffe93227ff41513ffa4c81ffd1640ffe83207ff49503ffa2a81ffd0540ffea2a05ff4d502ffae6817fd2340bfe89a05ff40d02ffa2e817fe7740bfe9b203ff51501ffa6a80ffd24407fe91a03ff5cd01ffa0680ffd72407fe81203ff4da00ffa47007fd13803fe89401ff88a00bfceea2dfe774d6febb247f74d923bfcee91dfd7644efebaa27fd45513bfcee89fdd2344efebb207f74d903bfaea81fdd3540eff3ba07f744d03fba4d19fdd168cfee83467f749633fba2b19fdd058cefeb9a05fe40d02fbc66817f41740aff3ba057f5cc02fbc66015fd7100afeba203fd45101f7c8880dfd73407ef19a037f5c901ff20480dfe77407faa2c23fd4d611fea4708ff503847fa81423fd00a11ff209007be44803fc81c01f78ce00ff205007f901803fb08c01fe4da00ff28b007f935803fc92401fe45200ff247007f913803fc89401fe1ca00ff445006de668cfaf2ac67f58ce11f7489007da33803f511401fc84600
def g191l8 : Packing := (100,2,6,5,2,12,0,g191d8)
def g191d9 (i : Nat) : Nat := 0x180327c7c11a70600f8f1304b1c05f0c3c541303017c38f1204e0ef8f13040180df9e0e080325463418a006077cbcf0238c0ef961b3c041381be3e0900df9e30006fcf825f86eb1755933dd9099319085000ff517fd35ff48ffd13ff40ffd02ff00bfd01ff803de33fd847fa00
def g191l9 : Packing := (12,1,6,7,2,9,0,g191d9)
def g191d10 (i : Nat) : Nat := 0x1f3c11ff
def g191l10 : Packing := (1,0,6,4,2,0,0,g191d10)
def g191samples : Array (Bits × Bits) := #[(0x6acfda3c2cb83a92b793db4cbe83faea9cb2634793e21db352fb83fe8df2bc07a86d83614e9e1d6652f73c866931a299021d0d35cea03b8bca899a3ae9b0852968ae39aed598c502d3cc66c95e3918558ba9636cd1546c95b4522b12e41c6251,0x8027018c1220821109402382a0c04040242201142810004800310a01021028020024504420900008134444101889108100844480011218a0808a088000429588a002494484002118004005c4110108908c2000154441190520210a0142200),(0x7913ceb593e8bd03514889e55f4c93639759259376fb3230720c9a865196f27cc74c193b9b758265cc3f7b6a39d891145642471fe1a3e402ed12036d66f3fc532a7d00122732be1cd6f8a0d631223ddb153772d463789a2c383ce02e7842d163,0x88036081c60419a2c82401d04754b2b302101402821d5c654204040641a4c69d42c491108805a675482c4b1a3210132646402113b58224122512010966d1b044833550122312b410427aa086012a6ec1101538c042289a0c282ca02a5842d161),(0x557693cafd0fd9424efb95e75ddf8ed5bd78c8ecb52fa208a8d45cb3574ccaab77d93b1e650b4399e9518160864e914bee471a4d6078d8cd3710b8c5462d299957d5836e24a95a7b253cdb2e6196070b78eaa32a2b4a267149c447650cd138a6,0x10c082401088400012d0c4008000004018ca8080142020182010002082500860100b028600824082a011044180428040210612040030c884904098c2002801191040822880a108c8040449084010010648220108084220210140474504110882),(0x9c642d62a2f2f7ba22bc048df67d49f5212576be5994f8cdc5e270babb8959b792802cb3e87f90d4054ae918d4ab1ce241d9cf541d5d16b72277276810cef58c9e0f2a3137066d66292bcd81a96583d025d9fd03afbb585aa2b81e898b063d44,0x8024093988519a8e002822a41919198600217873085849c0c483198871885081c08060615e498874054ab3104029780240914c50140c132321226228088464808a9608100702c12708ba84812c642a102598ac01a5195852a098180889063544),(0xd23eefb5d75806b89dcda38864b64661c9f5e2babc176a70b2d3a56f26f32e727e31fe7789e6e58a36284c9dbcb30e74d59821a10b67441120e71511dbf31ab50b42210b3baf1a3e4c47734dcff8958cfd1109f7ce27c18a062741ac46d7cd91,0x7413208444084451d48501104604c068b3980408840422121160844600658c78341c18180024668a9220480b8c940760b50821038273441010c51501633a18440140258228a50a1044455344031a81ae1001013e42228188062541a446c1c891),(0x44ee3263ec00331534507b30f50239085a477dc26fc97fafdd3677e1adedabf5a6627a917685fed951e16b05c441608531a6eebab7bf0ffa2c9d6923c000425ae070ded9cbf43ff0702d561449016826463c1cddf881bbc98109fdb0912bda0a,0x5c9601812402000310c10a308504200a188ca4d220b13a418220c4ac1700cc49329049900289169c4a408a09044020043184b638a739649c2011540242004250a0701ac901871eb02048c310010048264632184cec01aac801096da0110b580a),(0,0),(0x3ab08ab4b6d74c50e56bc9651caf5894b179e03465572acbdca5615696769c27053d6dc580568c9318a62a712d4d06df8fcf0933a8a96615b24c8891d85dee28deccf746ecda09546a23c7138dbf2215a9d969340b49504d34d905859a5a4fc,0x8020482e4971b288ed202044508b9ca5050108094844412451461041282e3192c9648008d0242841110660a6538444294c484083188002614b0e00011891a8820d8e45006648e00548a230c32acf32918089829300b41504d204901848a4a474),(0,0)]
def g191columns : IndexTree ColumnInfo := (.fork 19 (.fork 9 (.fork 4 (.leaf [(1,0,190,0,7),(2,0,189,0,8),(3,0,188,0,5),(4,0,187,0,7)]) (.fork 2 (.leaf [(6,0,185,0,5),(8,0,183,0,8)]) (.leaf [(0,8,163,20,6),(10,0,181,0,5),(12,0,179,0,5)]))) (.fork 5 (.fork 2 (.leaf [(4,8,163,16,5),(14,0,177,0,4)]) (.leaf [(16,0,175,0,8),(0,16,166,9,6),(1,16,166,8,5)])) (.fork 2 (.leaf [(19,0,172,0,4),(24,0,167,0,7)]) (.leaf [(16,8,163,4,5),(8,16,166,1,5),(25,0,166,0,4)])))) (.fork 9 (.fork 4 (.leaf [(9,16,166,0,4),(20,8,163,0,4),(32,0,159,0,8),(1,32,30,128,5)]) (.fork 2 (.leaf [(35,0,156,0,4),(40,0,151,0,5)]) (.leaf [(48,0,143,0,5),(56,0,135,0,4),(128,0,63,0,8)]))) (.fork 5 (.fork 2 (.leaf [(130,0,61,0,5),(4,128,27,32,5)]) (.leaf [(136,0,55,0,5),(160,0,31,0,7),(128,32,30,1,5)])) (.fork 2 (.leaf [(32,128,27,4,5),(161,0,30,0,4)]) (.leaf [(129,32,30,0,4),(164,0,27,0,4),(36,128,27,0,4)])))))
def g191autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32]]
def g191levels : Nat → Packing
  | 6 => g191l6
  | 7 => g191l7
  | 8 => g191l8
  | 9 => g191l9
  | 10 => g191l10
  | _ => emptyPacking
def g191index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 1 3 0 6 0 2 (key191l7)
  | 8 => lookupWord 17 64 6 11 5 2 (key191l8)
  | 9 => lookupWord 68 242 7 13 7 2 (key191l9)
  | 10 => lookupWord 9 46 4 10 4 2 (key191l10)
  | _ => fun _ => none
def g191 : Forest := ⟨191,10,fun j => g191samples[j]?.getD (0,0),g191columns,g191autos,g191levels,g191index,noFactory,noFactorySound 191⟩
def g251samples : Array (Bits × Bits) := #[(0x7c5b1073c997e37379da30f398119ee6fb6b9ec3f472bcb960b6e16b764eab308775a6f93b85666e9d3190b2b24d642ca5712b6de7ab3f7906c1699135342a691b3ae0a5aa4ef7bb316cf861cfcc30541d6a6cc4992b1a999615c8e8d911c1e1,0x2118206040004a02130d09680103a002090a061080141a8c00302460220208340600a251588102029c90b010225400202065234404234e080480294178042009180840240246b20a0024c060c50410001a48a084882a181106058840c1114140),(0xcce5a5f376b735aeaefe578ced15d32ecca61663a9af3bd1860bc21b19116b79223f9d41251db7915d2d676e62aaa4f819f9d341f91890478f7c179edecb18b88452ff03ce59b2503e9c1117dab8cd95ebc956b7a216470f30e3a2b3ec2d18bb,0x4842cb022293909020208080c0985104462050200a232050248f580a09002349282c0500277025a04229050a00aa2098018840837118b0c40a78400806c358a084123a0140090810bc8810142aa8e601010152222014470a10a222b02c2818b9),(0,0),(0x615f43b7c5899d56d0ed540d07e5651da134ed341e9bc1f74f237fc0ae8a342e74d0d54381c29b89aafb968c73300f2ad24e70d94c925aaf7c71d97b8e42ee34b1eb0d1c78f57307cdbb8ab0333b96f243ce283ea4988c525a6cf93575cb22d6,0x600508638c1a9f0381c44ce96aa5f40532886e32158a42c5402a7e6c4a89343c9410964685c08b09acb0120c353c06229a6c00c94c92de87444159522882ae0499430c1549527146cd2ac810537252985246622c84980c521a4cf835558922d2),(0x743743261165c64a5893c74b56706899b56f313d76fa70640bd59bea9f4cd6cd40c9796a92725dcea2baccf628444b5fc70e36349d152cf473b98c6d967cf8571ea4949a30a5a9a67c52f2db3fa12e66e966315b35ec80fa603e034c2e56ad7c,0x8e228200012500a04432a202145800c8c044118122412020998581138524c38140cb492802205484420a48e00002411d45001410a1402070b13084088559515204a0a28a24a10ca03050168720812c4621201151314480a8603203082a468c2c),(0xf3d9bb1a8ffcdc97c518eaf4c8cf14e122f0fafd99d5fdca7ef0f64eebb658a39d280ab679b66835384c18039df39cc970c09cab32e75b6d986af50aa1e14f67f56dcf6f41924d79e9e39f3990e7fa0a34138f4a5e417d209f607f101fc4fe09,0x9201861738918010c41062040c8818244620088911c0e1638783100880a45083c120082600262524204640020401ded90000982b30080131d06c4002816148a041658f0100904561e8880e0910f0e60220020e2216414120916065101cc4aa09),(0x8c34b489b6743f0cbbb4f14fa7d16d9fa49b993f9ba2b3789eb911d5e1cd7a6f64e2a177140a8013c504eb6dd8b5e7f7e94f5a351463882a81261e97691b96dcefd6ddbc37c1e3432aa0876640524995f6a595fd43d7d81429dbe94302afe942,0x269c30c1984c0e0408d2577d35632830a8c6a4165540daa693102041644d9ca647426045188a80110514e824d9155760ee46136c04410a2a918614976910825e2b85c52c35a0b36b4200852245520814f6b484dd43c398142959c9430287e142),(0x1bb2ab4aa0e85ba9e596de5ec3ce129b01134cce9757f2d674620576a8bd96bf3a893c9457f0a28da9ccac591d7731877093a6c205d64d4c2bcaa6363cd0b55e770f7a466dfb2a9c82572d4ce3aa90cf64d9c30549ce2fe50b809671629a567c,0xd9639e04222012901869c59f133e18908110146a61f169c201c69140019863c2e851098d7d900098988b54119762026501322c440c64c4e0e9086343c860556368a70222d632a1a145321c6e30c00cc44fdf181498e2ec50a809261621a5474),(0,0)]
def g251columns : IndexTree ColumnInfo := (.leaf [(8,0,243,0,7)])
def g251autos : Array (List Nat) := #[[],[84,115],[99,65],[118,84,115,65],[118,81],[118,84,99,81]]
def g251levels : Nat → Packing
  | _ => emptyPacking
def g251index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g251 : Forest := ⟨251,7,fun j => g251samples[j]?.getD (0,0),g251columns,g251autos,g251levels,g251index,noFactory,noFactorySound 251⟩
def g255samples : Array (Bits × Bits) := #[(0x9b665c544a8481c32c829a3849d25a0c2e734bceaece0410b1910c9246b692285657c973ca335d593cb00f0546b90059eb43e97a932728851785431870f031165ac8b80393ba6e576270cc58c906b870841734e15dc89803598ab05c2460a6b1,0x104454110880808228020a2041d8002c08600a02808c02009111060244ac12008614a1024802115108904700443200508241c8821224200116051018407029164080a01212302c0942400010c90428108414142154888803090a9048202086a0),(0xf315668af28fdb1ca228365b7ccc05a0011317731e21482f697635c521d4e57b4580944cacd08190116899ef79421d834fcee4e488905930903982805fb1c61927af17aaf49049a676974192f0d0160363a1bd03830701b0dc1f8281c2dc6123,0x83112a82400c43108201140b24040542001210600e014836084820c40800442b4181104024900000902098cc210099010006246088901220003082011981800902040620cc814002101041843090160043212902810201b054050081825c2101),(0x380526282fa13ac851f4c9c505254980d6e8ec3804b3594a769d93b950ebc251b0d8e2a15610b8154799066089743516386914b45de9a6e1e91c2d64aa4bec2945782990b2d68e61aa4d3cd1b24a6ab680984b4c1298da14a63264e421a50a46,0x184000082381184051a442400021c800c760240c008201086414493150c8805030586481420228050588002082640402084818905528808149002d00020c144045280184104604602a043c40824a60b20098024012185a048212646400810a02),(0x96903da21572f2b1f1c959078994a771bc47364121282ac5966e24786e0f6b8886ae49c27124b27b7242ff2e0094e0b4b1b582696d3c94568c371a6b03b30075a8d6353ad9672c0089eb12ba6325f80dd24d451b8459a7c113618d0b812f118c,0x86100cb01034a2a12848198388d4226018030240202c8a411a0a044824066a838a240842212092185a40cf0a0080e094a530c6680a1400448645526011312024a0c7343889210800016b021a61259805924545098441a1c11120810b812e1184),(0xca830c6ee5a1c1ac77b2c4bb013b84b271c7189edce77b42164b82b2ec44ccc2202552493f52e619512b4f09e2177ba801c291327039cbf4fba1fd7ca29d36ceca40c4508827295a1b45be11b7c00687be220f65622167c80c13fe90c415919,0x1282044674a181cc515204830038803270c71014e5265b22464b9241a4004482002443590d10ca0850630203a411b2a000c201185038c3861ba0d078200d6480c204804048212d4a89449e11258006869a220d60222163c80c12ea00c414819),(0xadcb89db333a54791fc5b16de6a74b1fbdaa5224c4caa060c8434905e130b3e50875189fa3aee40ebf67487ce98db2673644923b555505294552488c144494c2312ef3656d2d51ee39b1b44e04f3d3ec4d148000ab72771f011403179f478e82,0xa991884a13221d3803c5e045a0014312e78660240442614040424905201081f109410899826ca6043646807ca808b20b342020284941850001124c8410049440302c118d6904416438b533460072d3ec490080008b50771c0014031517470802),(0xccf1d170b069949f14600d7679a83ea985e068495997ad010287ff4ea745b576050c4fa9e8e0fabd2497448bd27a5aa8acea4ac0268e4d44dc2df9de452a225ad1457b3d721818b9bf9e05034d50ecb938aed67098a522a72856072e55b8d214,0xce85130b040942f1560095449a91aad8dc0e80b5196a18140955b282345b194266c47298868eeb9221d4601c27a00e8acf04a8036004c04cc8c58ecc43a23d68161791d311c0cb9abcc24434d40e8b9388ed67018a522072852072e55a0d214),(0x442aa5b9d884c622461c21eaaaf556fac8da8923687abbfb99c9c28096422e0eb83cb34c1d8918aec8c55d99f53bc2670104934ee2f27258616b2c55a56fa8970e02486406e9b92b5242282d15890d903f02672424a3e96d3ce1d022fa0aa8e8,0x460a679588446000a40a01aa08c414e80818810338389a92898982c08602320ec02091061180118a88016c815113416481048146a2821250206d8051a4632a958802cc600689381b004a400915810c003602652424a380613ce19002e808a0e8),(0,0)]
def g255columns : IndexTree ColumnInfo := (.leaf [(64,0,191,0,11)])
def g255autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32]]
def g255levels : Nat → Packing
  | _ => emptyPacking
def g255index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g255 : Forest := ⟨255,11,fun j => g255samples[j]?.getD (0,0),g255columns,g255autos,g255levels,g255index,noFactory,noFactorySound 255⟩
def key383l12 (i : Nat) : Nat := 0xf8400002630000023000000000000000000b83d5688000000000341000030000000000814000015d0000000210344000018d003b10000000000e080000000e70005c3803500091000000000008
def key383l11 (i : Nat) : Nat := 0x404c001fd7a0dd080d1200990f207c017043e0ac430a491c9aec7438f32422a414035a0e000e6f384202824e3e5491f317a0090ee161490000d0e481ce32000c4b9104c1860ad6100030920000000003c06000000722ae38f1200000035c780290bd08d23d219503209024ec0512fd44dc0985ef07266b48508d728f004824e9809324688ad260642ee33843c9e425582082c2260138002f8f81ac0c0002216a57414583e222000012800202204f00400024f34c01300e78608380c041012080080846040
def key383l10 (i : Nat) : Nat := 0x8a7028008f8208641c25de616202731427f0aa3ea6a9bc18603a40bac46606be46000184a7c7d25a0000000b98af69a264a6b01ac3b3a21709000001146294f5b28f5117b2b2368000000119a0000000503689a2858e10b056a96282c8039064ce4000005a1824c4b68b4a1ca0160003a96c1c5108908a005faaaa16a13000042ba8544116a040004b6aa18802880c23178071841517e2559911705a04117c6495c00000000085d314e242a96a0880000a01fc56687256502c84968668866a1180000003d68390f815a1fa922000012b8020000c2a6caf0234475dcf201fa032887c28e092c47a60725df80221bc02a000007a61e192100d1c1f61f683d817642e40874ab202e012c0cd05141d60b104cb094626909c0000000c0e573a858d7326a6285e00010ac0007468e22e50bc16f60921b5c8f41249001273800322800110cb04e0005728622182280ff076809bc29a93800081a596455d1053c0607cc3a5870000108081400524002801c04219100c0821c60cc13c0c2030a201001e00285000001f020030024000800c08280
def key383l9 (i : Nat) : Nat := 0x6977b1303806491384c288005f480044300b4273a470aef249bb09d0238c000000000000000603688ce51876813ab9e6c881d7b37687df408050502a181c84000606800000000000000424bbbaa9612800409100800346576b8a520800702905aa985610b9a10486080010008502020c0020a18085
def g383d8 (i : Nat) : Nat := 0x7c610014028800000000000000302080140040000000a09b827d78736e69645f5a55504b4637322d1e19140f0a0500cef45d94a2103afbaa93760801f7445d0744d03aaf69017618038fb68a9960d01ad76949760c01af34a89760c01af64289760c01adb6943760801aeb69037608018fb6683760801af94683760801afa42837608018ef690988ce009fcaa9190de009fa68a9944e009deaa99504e009deaa99520e009ee690988ce00be6690178ce00be6690918ce00be6690988ce00bf84a83784600bbc6989384600f749de3384600
def g383l8 : Packing := (25,4,6,0,3,8,0,g383d8)
def g383d9 (i : Nat) : Nat := 0x2dd0028c0601f18c02041010022160ac183c0004580028bb3c71c058816e807460680741c30700441602883bd0180c08009e92a09189248391a905315048c4c0a178c440a1c344e20480c5e3ec8c4124f1f67a1c70097c7d918050801b86cae3f18d8123489e81e3f187030392c68303e84a0683078305e30e0607e38f83c60f060a511f174250341f8c5e031010ee21078c3c161c0cee22050c28801004142c00504800c7c3000f402160a08ae97100120112003c70a082689408970b120030209083000c003000838e14007c610001c70838e1020020212004000023e3ec8cb8e14489e2f1a14a23e23d15c47a2b88f457115cca2f195c5e3ecf438e4f9debbcbf80ec1d2799709dd3b93626add2d9db38e63c8786afd5e3b876b2cad6ca75446864ec9992b24646c8990d60abf57bcf1dd3b7e6bccf98f3075e0b6565abd55ea85452734dc95d24a3b45a858ff9f13c6754e39b9356698cc18a2f85dcb916d2be568a61472724d08e918226438650b3138214370570800a4005ff65c1840f7fa2f442077fd9720d01dfe9bd1080dffa6537006ffd329bc017fd9704e009fe44a2e81ddf6541840f7ea300c2077bd94a2103ddeca51081cff6468840ffb20e89a07fd41844d03def4422681cff6241700f5fa2ec3007afc1761803d7e8cb0c01cff65d8100f7ea2ec08073fe99604039fe44a6e80cff65d834067fd32c1a03bdd8320d019fec4a0680cff64e884067fb121b8033fd9760c01dee9bb0600ef70dd830067fd32c1803bdd9760c01dee4bb0600ef7a65830077da6ec1003bec37608019fe44a6f005ef65037802fda521bc017f5190de00bfc8486f004ff22513802efb2a09c017f90904e00bfccba07007f644d03803fb20719c013fc988ce00bfcc9a03007fc406118027f93108c017f8894de00bfd4ca6f005fe46437802ff32e89c01ff11744e00bfc44a27005fea6513802ff32e09c017f99720e00fec89907005fe64483803fb26f19c01fd9138ce00bfc4c467007f645e33803fb02f19c01fd8918ce00fec4c467005fe64c81803fb46640c01ff11384600fed19c23005fe26211803fe26f08c01ff03784600ff849c23007fc8ce11803fe13108c013bd94a210397f4cb0c01cf7a6583006f73281bc017e9290de00bf88c86f005de65413802ef32a41c01fd23384600
def g383l9 : Packing := (91,3,6,5,3,11,0,g383d9)
def g383d10 (i : Nat) : Nat := 0xb1c029771ece80316e3a8b78f40771ca00d1002da03a69a8d16d01d28d4d3292968b98ba7f8c288f4271a30301042b0c2ce3d9d0c753d16f1a58de8639cbb8c715c8d44b554a1a9a3e0a89a12200921586544f91de7c3c6840c59058fc73e70a427a578082339c40459aa8af185209a7d34148d4cb55354aae60605689f215010071ece816c5e382c02c0800b78f67401b1c150a01655c62e06083462ae3d9d02d06c70541505820071ece801e380c14030a8b4a07c8d48497c63f8e66a4b4202e31fc73a14025b571ece863a00201e95c8d50005c7b3a084978e980d957652718d2b8da90a038f655cc3ed026a4b80d9d0683120b8d0ca07c4503e24b0080e3d9d0c73a100400171ece863a2041f8deb9e05d31c9dc29ad59e194d8397a571169d5a94d53c132d2591c5050edce08cf4b60acc9f89047f075c62859452044c3f83242b025c208114003ff45d03ffd1840fff06103ffe8840fff44d03ffd1700fff05c03ffd37407ff60d01ffc83407ff40d01ffe88407ff4dc01ffc37007ff4de00ffc37803ff44e00ffc13803ff8ce00ffe11802ffa2103fdd1340eff60403bfd83406ffa2101bfd83007fe40e00ff901803fe4de00ff837803fe44e00ff813803fe20e00ffa33803fe20600ffa11802bf61803bdd83006fb60801fda33803fc84600
def g383l10 : Packing := (41,2,6,7,3,12,0,g383d10)
def g383d11 (i : Nat) : Nat := 0x540b1d9a02e3804632e686a85e3b342382008507c4a8582c71cf98063b342397069da95ca003fe81ffc03ffa03ff007ff007fa00
def g383l11 : Packing := (6,1,6,6,3,8,0,g383d11)
def g383d12 (i : Nat) : Nat := 0x11b280e4ff
def g383l12 : Packing := (1,0,6,3,3,0,0,g383d12)
def g383samples : Array (Bits × Bits) := #[(0x22c0d3a3723e453b61b292904161c19166ba4156452239cb2ce776d1285888036922ca069735ba1c39466bb49cb80c880d6801ee650cd2ea8938a452f08d3169a1612a59384753bad95626662c63076161205bac29b905015369815a61884cb1,0x22a042a308281022412222104041018102a0455c0820218028210490004898014122a802062510400900403480940c80084001804506910881200012c0203148e041211030641239500420000c630440212052a0291101014268811220880c80),(0x3e4782180591e1e8ca415c93fb0e30440ddb7b080a80044a5e58703417b0ed0da2975b6df4e0151155ba1024096257dc7280e61c3739c9924483ab0a0d0a407f268250f5cf15b48886f76ba0ccf46838068d8de07060e07838bc1a040b61c283,0x9028018810161088ac0504223081040850928000290004c425070241b00400822080144b0c0241004a20000482053184202c40808184882448102000d0800b3040a404084018c8080110220c214483800898940502040781814120409604201),(0xc3b0d0243e2c92704a6d0bb89a642e3e324709614c855ba1b03c2574c53f0c84bca3b709607618aaaaca1686a79e094292d1a5b2e1a729d1ef4c761d2455891cd68664af136132ce19aaa19e6c55a2caed1460758145348a6cc923aa16a49516,0xc22070243c088a32102908b09820ae3610c20125cc051d809026055084360c62d8a3320940364922a8484682858e00c384d420b061233141a94434152055010c599024a50348105611a2a11e2441a2c2e41460350145348264c921aa12049512),(0x4138264952b1d12493a4452d72585b389605825093cff11edb60090262cf75191c382db2876b8a708e04945dba40fc5c0117030382d504a579e551698e39d387601c521a9a75d96750089c8958b895e01b82b803f01d0be08606741604bc230c,0x1080c0b03b031008084040c42504188060180103100c00a0a40008040890111041009902b010250040410442a404c140103030210c08ca050a00048c0a8c022200c1018d83149210000148108b815200b021800b00809600202141404b82204),(0x7a0c641d50044e150338db871c0d9c6d8b49b017941b1c71c485efc79a14e6ae159b09d8c200cd085276a758cd18f3623c4db7d00870524c281de7f5fe3e2adc1756b294808a0882ea6a1f2df107bc01d0df010f4d40469e2105ef94c107b239,0xd004201450464809021899a3188eb82288483003841b1c31c500f247991664ae92090048c000c90e723223084509b040f48cd45008304046281cf3843e140e8407928284000804822b6a8b24f004a801d0dd010f4440469e21056a80c1079039),(0xcc62da0a5fa8f5e2c996caf343c42faac6de9a345ff56a94813a6425060416282f4d23c281526277465dd835f65817a533b901ad51024edaaa84a94a69219208d911c25be8aad34a7f39eda22807bafd8e8540012ec5ecf42900c6dcd341c02,0x8452d0021128d5c8c9144a91d1c007ab845a00141d69e1982122246c02041428290423d28902225305595421e41c17a5023985a908040a15a0c4800269208200d9018058b1aa90485c38f99a2803baf58c8040010ec1ece00900c4d4d341002),(0xdaef1c77688221978d1e0c4ad4cf460c43747468370c9781a044ccfb808507cfc7550e6f05834be93d3c1e4e94918217a4e0da637baa95002472c84f89f63e421033ad28de7ab208228bfb0281a229d272553696158289b300da2c9976c32464,0x92e959624882001701040c005417432c02544069252c9701a0048cc280a00e56d4150e31071309c931151f4c9213080304e00a4233c09500a002c04d90b29c403071012c5a3a310c128ab91220a221c27244349605808983008a2c9966812464),(0,0),(0x941a1aee99450a81362f36506691ad42486aa7b56b55a36c2710c35afdccd2f0604110c2892f54d343a9228b60c516b3ea6e18394813263b179331842a516d8adc29c7c000c846f164b52014130d4016a078833106127956c94690a3b81ad1d8,0x4120210904c02803268a2402080b401402a07040a01006405204110294490a020401002d0205402c22800a1400c2280a20c04a14813021a0411310009012188c000460020c0069060300020050540108030832102126010c94480229002c198)]
def g383columns : IndexTree ColumnInfo := (.fork 29 (.fork 14 (.fork 7 (.fork 3 (.leaf [(1,0,382,0,9),(0,1,332,50,7),(2,0,381,0,9)]) (.leaf [(0,2,312,69,7),(3,0,380,0,6),(2,1,332,48,6),(1,2,312,68,6)])) (.fork 3 (.leaf [(4,0,379,0,11),(5,0,378,0,7),(7,0,376,0,5)]) (.leaf [(5,2,312,64,5),(8,0,375,0,9),(0,8,99,276,7),(12,0,371,0,8)]))) (.fork 7 (.fork 3 (.leaf [(13,0,354,0,4),(14,0,369,0,5),(16,0,367,0,11)]) (.leaf [(17,0,366,0,8),(18,0,365,0,7),(19,0,364,0,5),(18,1,332,32,5)])) (.fork 4 (.leaf [(24,0,359,0,8),(25,0,358,0,5),(28,0,355,0,7),(20,8,99,256,5)]) (.leaf [(32,0,351,0,11),(33,0,350,0,8),(32,1,332,18,6),(35,0,348,0,5)])))) (.fork 15 (.fork 7 (.fork 3 (.leaf [(34,1,332,16,5),(44,0,339,0,5),(49,0,334,0,7)]) (.leaf [(48,1,332,2,5),(33,16,326,8,5),(56,0,327,0,5),(64,0,319,0,11)])) (.fork 4 (.leaf [(65,0,318,0,7),(66,0,317,0,8),(67,0,316,0,5),(65,2,312,4,5)]) (.leaf [(70,0,313,0,7),(34,64,29,256,5),(256,0,127,0,9),(0,256,23,104,7)]))) (.fork 7 (.fork 3 (.leaf [(264,0,119,0,6),(256,8,99,20,6),(8,256,23,96,6)]) (.leaf [(268,0,115,0,5),(260,8,99,16,5),(280,0,103,0,5),(272,8,99,4,5)])) (.fork 4 (.leaf [(288,0,95,0,8),(289,0,94,0,5),(40,256,23,64,5),(304,0,79,0,5)]) (.leaf [(320,0,63,0,8),(322,0,61,0,5),(258,64,61,0,5),(352,0,31,0,7)])))))
def g383autos : Array (List Nat) := #[[],[84,131,98],[101,66,16],[100,131,82,16],[82,129,48],[101,100,131,98,129,48],[100,49,128],[101,84,131,66,49,128]]
def g383levels : Nat → Packing
  | 8 => g383l8
  | 9 => g383l9
  | 10 => g383l10
  | 11 => g383l11
  | 12 => g383l12
  | _ => emptyPacking
def g383index : Nat → Nat → Option (Nat × Nat)
  | 8 => fun _ => none
  | 9 => lookupWord 17 68 7 12 5 3 (key383l9)
  | 10 => lookupWord 57 200 7 14 7 3 (key383l10)
  | 11 => lookupWord 30 108 6 13 6 3 (key383l11)
  | 12 => lookupWord 6 61 1 10 3 3 (key383l12)
  | _ => fun _ => none
def g383 : Forest := ⟨383,12,fun j => g383samples[j]?.getD (0,0),g383columns,g383autos,g383levels,g383index,noFactory,noFactorySound 383⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low3 : Lower (vars 3) (graphGoal 3) 1 := size_of (hints:=1) (by decide +kernel)
def maps3 : List (Nat × List Nat) := []
def known3 := extendKnown [] 1 maps3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid3 : Known known3 := extendKnown_ok baseKnown low3 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low7 : Lower (vars 7) (graphGoal 7) 2 := size_of (hints:=257) (by decide +kernel)
def maps7 : List (Nat × List Nat) := []
def known7 := extendKnown known3 2 maps7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid7 : Known known7 := extendKnown_ok valid3 low7 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom15 : graphValid g15 (boundsBefore known7) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s15_3_0 : block g15 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl15_3 : block g15 3 0 1 = true := s15_3_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables15 : checkedTables g15 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g15 0 0 0 = true)
  · exact (rfl : block g15 1 0 0 = true)
  · exact (rfl : block g15 2 0 0 = true)
  · exact bl15_3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low15 : Lower (vars 15) (graphGoal 15) 4 :=
  lower_forest (g:=g15) (i:=0) (hints:=8449) (before_sound known7 valid7) geom15 tables15 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps15 : List (Nat × List Nat) := [(15,[]),(23,[32,67]),(27,[16,66]),(29,[65,50]),(30,[64,65,66,67]),(39,[32,67,84]),(57,[32,65,82,83]),(78,[64,33,67,84,101]),(99,[16,33,66,83,100,101]),(135,[67,84,101,118]),(156,[64,81,83,101,118]),(163,[16,66,83,100,101,118]),(165,[65,50,83,100,101,118]),(166,[64,65,66,83,100,118]),(172,[64,81,82,67,100,101,118]),(177,[16,65,82,99,118]),(198,[64,83,100,117]),(281,[65,82,83,101,118,135]),(305,[16,65,82,99,118,135]),(312,[64,81,98,83,118,135]),(326,[64,66,83,100,117,135]),(330,[64,65,82,100,117,135]),(332,[64,81,66,83,100,117,118,135]),(344,[64,81,98,83,117,118,135]),(353,[65,82,99,116,117,135]),(354,[64,65,82,99,116,101,118,135]),(396,[64,81,82,83,100,117,134,135]),(424,[64,81,98,67,116,101,134]),(480,[64,81,98,115,132,101,134])]
def known15 := extendKnown known7 4 maps15
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid15 : Known known15 := extendKnown_ok valid7 low15 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low45 : Lower (vars 45) (graphGoal 45) 3 := size_of (hints:=8965) (by decide +kernel)
def maps45 : List (Nat × List Nat) := []
def known45 := extendKnown known15 3 maps45
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid45 : Known known45 := extendKnown_ok valid15 low45 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low51 : Lower (vars 51) (graphGoal 51) 3 := size_of (hints:=1) (by decide +kernel)
def maps51 : List (Nat × List Nat) := []
def known51 := extendKnown known45 3 maps51
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid51 : Known known51 := extendKnown_ok valid45 low51 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom31 : graphValid g31 (boundsBefore known51) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_0 : block g31 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_1 : block g31 5 1 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl31_5 : block g31 5 0 3 = true := (@block_merge g31 5 0 1 2 s31_5_0 s31_5_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_6_0 : block g31 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl31_6 : block g31 6 0 1 = true := s31_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables31 : checkedTables g31 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g31 0 0 0 = true)
  · exact (rfl : block g31 1 0 0 = true)
  · exact (rfl : block g31 2 0 0 = true)
  · exact (rfl : block g31 3 0 0 = true)
  · exact (rfl : block g31 4 0 0 = true)
  · exact bl31_5
  · exact bl31_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low31 : Lower (vars 31) (graphGoal 31) 7 :=
  lower_forest (g:=g31) (i:=0) (hints:=8449) (before_sound known51 valid51) geom31 tables31 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps31 : List (Nat × List Nat) := [(31,[]),(167,[83,100,101,118]),(313,[81,98,99,84,118,135]),(334,[80,81,82,83,100,117,135]),(355,[82,99,116,117,118,135]),(428,[80,97,82,99,116,101,134])]
def known31 := extendKnown known51 7 maps31
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid31 : Known known31 := extendKnown_ok valid51 low31 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low47 : Lower (vars 47) (graphGoal 47) 5 :=
  lower_discard (g:=g47) (ci:=(8,0,39,0,4)) (hints:=8449) (before_sound known31 valid31) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps47 : List (Nat × List Nat) := [(47,[]),(61,[65,50]),(94,[64,65,66,67,101]),(151,[67,84,101,118]),(173,[48,65,50,83,100,118]),(181,[65,50,99,84,118]),(185,[16,65,98,83,101,118]),(188,[64,97,98,67,84,118]),(227,[16,66,99,116,117,118]),(230,[64,65,66,99,116,101]),(301,[48,65,82,100,118,135]),(331,[80,81,66,100,117,118,135]),(339,[66,99,84,117,118,135]),(345,[80,65,98,67,84,117,118,135]),(346,[64,49,98,67,84,117,135]),(358,[64,65,82,99,116,101,118,135]),(369,[65,98,115,84,118,135]),(422,[64,81,66,99,116,117,134]),(440,[64,97,114,67,84,117,134]),(454,[64,66,99,116,133,118,135]),(460,[64,97,66,99,116,133,135]),(482,[64,49,98,115,132,133,135]),(484,[64,97,82,115,132,101,118,135])]
def known47 := extendKnown known31 5 maps47
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid47 : Known known47 := extendKnown_ok valid31 low47 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low55 : Lower (vars 55) (graphGoal 55) 5 :=
  lower_discard (g:=g55) (ci:=(16,0,39,0,4)) (hints:=257) (before_sound known47 valid47) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps55 : List (Nat × List Nat) := [(55,[]),(79,[64,65,66,67,101]),(103,[16,66,100,101]),(115,[50,99]),(143,[32,67,101,118]),(174,[48,65,50,83,100,118]),(179,[65,50,99,84,118]),(206,[48,50,67,100,117]),(286,[48,33,101,118,135]),(316,[48,97,66,84,118,135]),(327,[64,65,82,100,117,135]),(348,[48,97,66,84,117,118,135]),(364,[48,97,99,116,118,135]),(376,[48,97,114,99,116,118,135]),(398,[48,65,50,67,100,117,134]),(433,[16,49,98,115,100,117,134,135])]
def known55 := extendKnown known47 5 maps55
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid55 : Known known55 := extendKnown_ok valid47 low55 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low63 : Lower (vars 63) (graphGoal 63) 8 :=
  lower_discard (g:=g63) (ci:=(32,0,31,0,7)) (hints:=8449) (before_sound known55 valid55) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps63 : List (Nat × List Nat) := [(63,[]),(95,[16,66,101]),(159,[32,67,101,118]),(175,[32,83,100,118]),(183,[99,84,118]),(231,[16,66,99,116,117,118]),(317,[32,97,82,83,100,118,135]),(350,[96,33,99,84,117,135]),(359,[16,82,99,116,118,135]),(366,[96,49,116,118,135]),(371,[98,115,84,135]),(377,[48,97,114,99,116,117,118,135]),(429,[80,97,116,134,135]),(430,[96,81,98,83,116,134]),(441,[16,97,114,116,101,134,135]),(444,[96,113,114,99,84,101,134]),(462,[96,98,67,116,133,135]),(492,[96,113,115,132,133,134])]
def known63 := extendKnown known55 8 maps63
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid63 : Known known63 := extendKnown_ok valid55 low63 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom111 : graphValid g111 (boundsBefore known63) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s111_6_0 : block g111 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl111_6 : block g111 6 0 1 = true := s111_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables111 : checkedTables g111 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g111 0 0 0 = true)
  · exact (rfl : block g111 1 0 0 = true)
  · exact (rfl : block g111 2 0 0 = true)
  · exact (rfl : block g111 3 0 0 = true)
  · exact (rfl : block g111 4 0 0 = true)
  · exact (rfl : block g111 5 0 0 = true)
  · exact bl111_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low111 : Lower (vars 111) (graphGoal 111) 7 :=
  lower_forest (g:=g111) (i:=0) (hints:=16785665) (before_sound known63 valid63) geom111 tables111 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps111 : List (Nat × List Nat) := [(187,[16,97,66,83,100,101,118]),(190,[64,97,98,67,84,118]),(215,[67,84,117]),(222,[64,65,66,67,117,118]),(238,[64,65,66,99,116,101]),(243,[16,66,115,100,101]),(318,[64,81,66,83,100,118,135]),(349,[80,65,98,67,84,117,118,135]),(365,[48,65,82,116,135]),(378,[64,49,114,67,84,101,118,135]),(413,[48,65,50,67,117,134]),(437,[65,50,115,84,134]),(455,[96,98,67,116,133,135]),(476,[64,113,66,115,100,133,118,135]),(490,[64,49,114,99,132,133,118,135]),(497,[65,114,131,84,134,135]),(504,[64,113,130,67,84,133,135])]
def known111 := extendKnown known63 7 maps111
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid111 : Known known111 := extendKnown_ok valid63 low111 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low119 : Lower (vars 119) (graphGoal 119) 6 :=
  lower_discard (g:=g119) (ci:=(4,0,115,0,5)) (hints:=16777473) (before_sound known111 valid111) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps119 : List (Nat × List Nat) := [(119,[]),(207,[64,65,66,67,117,118]),(380,[48,113,66,84,101,135]),(414,[48,65,50,67,117,134])]
def known119 := extendKnown known111 6 maps119
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid119 : Known known119 := extendKnown_ok valid111 low119 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom189 : graphValid g189 (boundsBefore known119) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_0 : block g189 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_1 : block g189 6 1 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl189_6 : block g189 6 0 3 = true := (@block_merge g189 6 0 1 2 s189_6_0 s189_6_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_7_0 : block g189 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl189_7 : block g189 7 0 1 = true := s189_7_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables189 : checkedTables g189 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g189 0 0 0 = true)
  · exact (rfl : block g189 1 0 0 = true)
  · exact (rfl : block g189 2 0 0 = true)
  · exact (rfl : block g189 3 0 0 = true)
  · exact (rfl : block g189 4 0 0 = true)
  · exact (rfl : block g189 5 0 0 = true)
  · exact bl189_6
  · exact bl189_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low189 : Lower (vars 189) (graphGoal 189) 8 :=
  lower_forest (g:=g189) (i:=0) (hints:=536879876) (before_sound known119 valid119) geom189 tables189 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps189 : List (Nat × List Nat) := [(189,[]),(347,[65,66,115,84,101,118,135]),(486,[16,66,99,132,133,134,135])]
def known189 := extendKnown known119 8 maps189
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid189 : Known known189 := extendKnown_ok valid119 low189 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low250 : Lower (vars 250) (graphGoal 250) 5 := size_of (hints:=1366507616) (by decide +kernel)
def maps250 : List (Nat × List Nat) := []
def known250 := extendKnown known189 5 maps250
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid250 : Known known250 := extendKnown_ok valid189 low250 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low127 : Lower (vars 127) (graphGoal 127) 9 :=
  lower_discard (g:=g127) (ci:=(32,0,95,0,8)) (hints:=16785665) (before_sound known250 valid250) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps127 : List (Nat × List Nat) := [(127,[]),(223,[64,65,66,67,117,118]),(247,[115,84]),(375,[98,115,84,135]),(381,[48,113,82,135]),(382,[112,49,66,115,84,101,135]),(415,[48,65,50,67,117,134]),(446,[112,81,114,83,100,134,135]),(478,[112,65,114,67,100,133,135]),(493,[80,113,50,132,135]),(499,[65,114,131,84,134,135]),(505,[64,113,130,131,132,133,135]),(508,[112,129,66,115,84])]
def known127 := extendKnown known250 9 maps127
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid127 : Known known127 := extendKnown_ok valid250 low127 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom191 : graphValid g191 (boundsBefore known127) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_6_0 : block g191 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_6 : block g191 6 0 1 = true := s191_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_0 : block g191 7 0 13=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_1 : block g191 7 13 15=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_7 : block g191 7 0 28 = true := (@block_merge g191 7 0 13 15 s191_7_0 s191_7_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_0 : block g191 8 0 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_1 : block g191 8 7 61=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_2 : block g191 8 68 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_8 : block g191 8 0 100 = true := (@block_merge g191 8 0 68 32 (@block_merge g191 8 0 7 61 s191_8_0 s191_8_1) s191_8_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_0 : block g191 9 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_1 : block g191 9 3 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_9 : block g191 9 0 12 = true := (@block_merge g191 9 0 3 9 s191_9_0 s191_9_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_10_0 : block g191 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_10 : block g191 10 0 1 = true := s191_10_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables191 : checkedTables g191 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g191 0 0 0 = true)
  · exact (rfl : block g191 1 0 0 = true)
  · exact (rfl : block g191 2 0 0 = true)
  · exact (rfl : block g191 3 0 0 = true)
  · exact (rfl : block g191 4 0 0 = true)
  · exact (rfl : block g191 5 0 0 = true)
  · exact bl191_6
  · exact bl191_7
  · exact bl191_8
  · exact bl191_9
  · exact bl191_10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low191 : Lower (vars 191) (graphGoal 191) 11 :=
  lower_forest (g:=g191) (i:=0) (hints:=536879361) (before_sound known127 valid127) geom191 tables191 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps191 : List (Nat × List Nat) := [(191,[]),(319,[65,50,135]),(351,[64,65,66,67,101,135]),(367,[80,81,66,100,117,118,135]),(379,[81,98,118,135]),(431,[48,65,50,83,100,134,135]),(445,[48,97,82,134]),(487,[16,66,99,132,133,134,135]),(494,[96,65,98,67,132,117,134])]
def known191 := extendKnown known127 11 maps191
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid191 : Known known191 := extendKnown_ok valid127 low191 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low251 : Lower (vars 251) (graphGoal 251) 8 :=
  lower_discard (g:=g251) (ci:=(8,0,243,0,7)) (hints:=1358970881) (before_sound known191 valid191) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps251 : List (Nat × List Nat) := [(251,[]),(254,[32,67,117]),(471,[16,66,67,100,133,134,135]),(501,[16,33,50,131,100,133,118]),(506,[32,49,130,100])]
def known251 := extendKnown known191 8 maps251
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid251 : Known known251 := extendKnown_ok valid191 low251 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low255 : Lower (vars 255) (graphGoal 255) 12 :=
  lower_discard (g:=g255) (ci:=(64,0,191,0,11)) (hints:=553656577) (before_sound known251 valid251) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps255 : List (Nat × List Nat) := [(255,[]),(479,[64,65,66,67,133,134,135]),(503,[16,66,131,100,101,135]),(507,[81,130,118]),(509,[48,129,82]),(510,[128,65,130,67,100,117])]
def known255 := extendKnown known251 12 maps255
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid255 : Known known255 := extendKnown_ok valid251 low255 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom383 : graphValid g383 (boundsBefore known255) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_0 : block g383 8 0 23=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_1 : block g383 8 23 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_8 : block g383 8 0 25 = true := (@block_merge g383 8 0 23 2 s383_8_0 s383_8_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_0 : block g383 9 0 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_1 : block g383 9 9 75=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_2 : block g383 9 84 7=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_9 : block g383 9 0 91 = true := (@block_merge g383 9 0 84 7 (@block_merge g383 9 0 9 75 s383_9_0 s383_9_1) s383_9_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_0 : block g383 10 0 5=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_1 : block g383 10 5 16=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_2 : block g383 10 21 20=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_10 : block g383 10 0 41 = true := (@block_merge g383 10 0 21 20 (@block_merge g383 10 0 5 16 s383_10_0 s383_10_1) s383_10_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_0 : block g383 11 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_1 : block g383 11 1 5=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_11 : block g383 11 0 6 = true := (@block_merge g383 11 0 1 5 s383_11_0 s383_11_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_12_0 : block g383 12 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_12 : block g383 12 0 1 = true := s383_12_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables383 : checkedTables g383 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g383 0 0 0 = true)
  · exact (rfl : block g383 1 0 0 = true)
  · exact (rfl : block g383 2 0 0 = true)
  · exact (rfl : block g383 3 0 0 = true)
  · exact (rfl : block g383 4 0 0 = true)
  · exact (rfl : block g383 5 0 0 = true)
  · exact (rfl : block g383 6 0 0 = true)
  · exact (rfl : block g383 7 0 0 = true)
  · exact bl383_8
  · exact bl383_9
  · exact bl383_10
  · exact bl383_11
  · exact bl383_12
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low383 : Lower (vars 383) (graphGoal 383) 13 :=
  lower_forest (g:=g383) (i:=0) (hints:=12901687553) (before_sound known255 valid255) geom383 tables383 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps383 : List (Nat × List Nat) := [(383,[]),(447,[65,50,131,84,118,135]),(495,[80,81,82,83,116,133,118])]
def known383 := extendKnown known255 13 maps383
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid383 : Known known383 := extendKnown_ok valid255 low383 (by decide +kernel)
def hashdeadl14 (i : Nat) : Nat := 0x4592c8500000000002800049a6c68a83340e9800000aa00684000000054a001bcc7001e180000682000000000000001d46a1840000003a00000001c
def hashdeadl13 (i : Nat) : Nat := 0x301a0007b2f00e0aa2992094818000e2e0000000269e056438000000000d33e40e4a200074d00000000000003b10001e0240a9bd45d962582900000000000001430001e1400000fc03b84a000614e69108a1108000810000d04c9d0000000408800000160f24180010b9d040003080001e0c000000000001997f401183740ee12000000000080d312c00102c00000000012070000000001d35000308c000a4c0001b30000000cb3800183000070f0000001abcc008002c8cc133000000000000000000000020b000000064ec0a00000f8000cc5000105d8204160001a38001c1c467309c000000a7700000016de30f80000008380b08e000d3001
def hashdeadl12 (i : Nat) : Nat := (if i<1 then 0x7b02c3200425d610a000042a0327300000000106b33757005e04600006037d811679d009461963480703e1077f067f2582384275d80a540a20109b59b4006305d00000000ab6dfb0bf59ec084c806986b30597776440b146b100c50a956520000878e0000747c463e108bc029e7600000395ef090d06800000000f0550000d0b1e4af00000000f324d141840ca4380000000051505017000067300000e779907b0000e77730641201ea62a089a48ff0924111e9a7a041b2a180aee462f29d9b47b01eb0427030e02a5973605b9086f08d5081d04bb014363000006038c0b6d110106cc731308e0023a07fb1305601ba1839b4c088a10b88011043e427e75a600831464016903d3ba52b1ec095000ec050b011b0730478f11a0000755e331ef63db004a00a000069a91680e225f60f90092a9d0000764650a40000c591f95ac03baa33c5a1283d11871a6d2772c01c1057280f201f5012328b908232a5505e000fe02b507cf0809817c267c05c9528506d997696872194b206264030ad402d007d586d7228701d30605840f67838625a51443ce034d47ed45f704cb08730a1794e1252000070330000b56f0000b0b4000000000000a842e047609d406ae26b67b08a4de12aa0a34019000000000000b664342c50b50000c0af924dc9aa401870366002b26d00000000841e0000000060986614000000000000783ae10d980ee051d0ab4022a615808f0000a0832619a148d81500007000e007d616b032d01b483f163f00104028276b2015141030631049a027580cd0a7a05ab977802fb09ff07a97899053b0a80816e83be0790a1b809b8b460a4f0000178b0000847be03cf139a1170000b07850b3605408416262696b908af0aa7b1f5b446070d024601a42492101d496f4b4e035922127ab0000e18600008284831c00440000f031500310656013b071b045b25b4113766b5b4c6b0800008291b4888a50000000000000e38b0000225eb04d807230618425c0b097ae226f809e00000000f00d93480485e88728040000b11c3039204e9432711f445c905f004a300b97ada05680211292f09a7b1a696f3106704f19748066703f00000204d074ba20a118f025458794596091a06f000065946020913b783e342dd08c819b5b452076c21dc075e0991a4a183c3b19d7a750a68058c8379643a487b408d0523762d062b422e0b2d47fc0ac224a46231a5dca3b6069a4390000768a5433e07e0000da410b00003102090604000a010a1f88080000080d030b0c310304001300040113030203141f0c0001000232030b0801010a010007110002020208010605020401010119010b0304070203070506000210070d110100150b0a0504051d050002020b05000c0402003d0e1500260200020108040b03090500060204000d0602010100180501000001030f04 else 0xe0a0512830933085c048e216509713746026a02ec09cb040548400000268f701103ac254729fc29e8096145a39ab47552144806e00019612b7b4491ea44bc1)
def hashdeadl11 (i : Nat) : Nat := 0x5b144463e05aea749a36008e0000f05f008fc82400000000057a08357304bb42c02b0000807cd1701823000007095811411b96631031e07218223334c77b980e8010305dd000180820521064ca3ef0420000409b626cd483a833f03ac022e048a008f80a513f0000db73410f3393ca38834018881012b081c465a02c6142704300002631809700000000715300007115b00dd054b2886014000054161b183099000000000129f0870000a24110110427972915960000477d5b457113518aa01a00007134a023d08a1053002d678ef06b604a6076520f5468b025698fe62d5060c1370000e07eb793c95be02a510198285417000000000000000000005b72220ea00f9098e036e09602120000503908396112556c56084a3a211d0342f0784635707b4293308d0624205556235211962a72516903a0190235010e7765e07d5784f16feb3c248834149073d088b0134091f720f0803275f0052809446ed494b01b1b0305939136b20cf495111aba390000db890950e9807026e609a0205015880ba66b8778d4967988f077f007110cd289d0160000e278401d0000000000000000f032027400000000a08c6209804c4030102eb368a33f3b1d798e0000538a70215061a44e228300000000000000000000d01710838075e4517067406f00000000609a00003253a089a4002093b00a8125000090790000c0599583180c00000000c0411830f1160047224900000000906992725046700b000050511a67544b00000407c35bb06d0000504d3821ca470002762e0000cb1760948827b10a603b4009e06552019464444f9688a0286169097ab82524185057db2feb3d000e6303670ac01e70822426b090d664c05cf764008be03c365d6a2549347068706a71244461f086277c5780380d698dd120b27c20626037d807f403502fe1110000ea6e5071301cb0388044704f411c809595011003b20deb1a98372208b0561092820a91190049704bb03ec070670890335001a03f64504063613c50294b430832441aba46e146c8120193598c103df8314066401fd460e0745084044c100c7760b24b824f4006205b0000563070507a7c9058000000006a440000506e3040e97d006cd027646a6207807fb0450138e56fa018704e8482e0356085662f762c5b3be05eb81f1004f836000000000000000046203a6ac89692730000b034807a613d00008145702433536a79b0407805012a04e80082c50a0c0e782286421a0e4c00400004833a1491a02243880c0851202004211c6408c1835c192e081800c39681005000c04e408002001860c34c8040000000400008087400400100892c38005148410524200800478080001438126000000020022
def hashdeadl10 (i : Nat) : Nat := 0x1c05302000382d2ecf474c3a08f618409ea54931a0a2272b385214e934380040192451090d15cc0564307983441ce005970002c06068f08a82680cc070001a2c5d4a1440400018207150002808001022205d856c41e1700072d518800084a2900000a334a12801820030b1a27
def hashdeadl9 (i : Nat) : Nat := 0x202e0
abbrev knownPrev_g539 := known383
def g539d3 (i : Nat) : Nat := 0xf
def g539l3 : Packing := (1,0,0,0,0,0,0,g539d3)
def g539samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdffce7fff1c3ff27,0x200a0a0a20914a22),(0xebff073ffe038fc4,0x1510b454d42615c4),(0,0),(0xf33ff8387ffc0cf8,0xca286a669304cb0),(0x83c0003f80000f00,0x7ebbdfff6dbb6fb2),(0,0),(0,0),(0,0),(0,0)]
def g539columns : IndexTree ColumnInfo := (.leaf [])
def g539autos : Array (List Nat) := #[[]]
def g539levels : Nat → Packing
  | 3 => g539l3
  | _ => emptyPacking
def g539index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g539 : Forest := ⟨539,3,fun j => g539samples[j]?.getD (0,0),g539columns,g539autos,g539levels,g539index,noFactory,noFactorySound 539⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geomg539 : graphValid g539 (boundsBefore knownPrev_g539) = true := by
  unfold graphValid
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel, by decide +kernel⟩, ?_⟩, by decide +kernel⟩
  apply listPieces_all (d:=0)
  simp only [listPieces,IndexTree.values,List.length_append,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceDiv,List.take,List.drop]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg539_3_0 : block g539 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg539_3 : block g539 3 0 1=true := sg539_3_0
theorem tablesg539 : checkedTables g539 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g539 0 0 0 = true)
  · exact (rfl : block g539 1 0 0 = true)
  · exact (rfl : block g539 2 0 0 = true)
  · exact allg539_3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low539 : Lower (vars 539) (graphGoal 539) 4 :=
  lower_forest (g:=g539) (i:=0) (hints:=16385) (before_sound known383 valid383) geomg539 tablesg539 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps539 : List (Nat × List Nat) := [(539,[]),(541,[118,133,33,48]),(569,[118,130,81]),(793,[82,129,48])]
def known539 := extendKnown known383 4 maps539
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid539 : Known known539 := extendKnown_ok valid383 low539 (by decide +kernel)
abbrev knownPrev_g535 := known539
def g535d3 (i : Nat) : Nat := 0xf
def g535l3 : Packing := (1,0,0,0,0,0,0,g535d3)
def g535samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffef9f9ff87e3ff99f,0x1041440c48128912),(0xf7ffe73fffc70fe4,0x8820850928414c4),(0xbbe7f83f8ff80e78,0x451445a54d20aa38),(0,0),(0xc3f8003ff0000f80,0x3e5776fe69b6cf92),(0,0),(0,0),(0,0),(0,0)]
def g535columns : IndexTree ColumnInfo := (.leaf [])
def g535autos : Array (List Nat) := #[[]]
def g535levels : Nat → Packing
  | 3 => g535l3
  | _ => emptyPacking
def g535index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g535 : Forest := ⟨535,3,fun j => g535samples[j]?.getD (0,0),g535columns,g535autos,g535levels,g535index,noFactory,noFactorySound 535⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geomg535 : graphValid g535 (boundsBefore knownPrev_g535) = true := by
  unfold graphValid
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel, by decide +kernel⟩, ?_⟩, by decide +kernel⟩
  apply listPieces_all (d:=0)
  simp only [listPieces,IndexTree.values,List.length_append,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceDiv,List.take,List.drop]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg535_3_0 : block g535 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg535_3 : block g535 3 0 1=true := sg535_3_0
theorem tablesg535 : checkedTables g535 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g535 0 0 0 = true)
  · exact (rfl : block g535 1 0 0 = true)
  · exact (rfl : block g535 2 0 0 = true)
  · exact allg535_3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low535 : Lower (vars 535) (graphGoal 535) 4 :=
  lower_forest (g:=g535) (i:=0) (hints:=257) (before_sound known539 valid539) geomg535 tablesg535 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps535 : List (Nat × List Nat) := [(535,[]),(542,[118,133,33,48]),(817,[118,130,81]),(824,[82,129,48])]
def known535 := extendKnown known539 4 maps535
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid535 : Known known535 := extendKnown_ok valid539 low535 (by decide +kernel)
def g606 : Forest := ⟨606,4,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none,noFactory,noFactorySound 606⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low606 : Lower (vars 606) (graphGoal 606) 5 :=
  lower_discard (g:=g606) (ci:=(0,16,78,0,4)) (hints:=16982304) (before_sound known535 valid535) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps606 : List (Nat × List Nat) := [(606,[]),(663,[118,133,33,48]),(881,[82,129,48]),(952,[118,130,81])]
def known606 := extendKnown known535 5 maps606
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid606 : Known known606 := extendKnown_ok valid535 low606 (by decide +kernel)
def g693 : Forest := ⟨693,4,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none,noFactory,noFactorySound 693⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low693 : Lower (vars 693) (graphGoal 693) 5 :=
  lower_discard (g:=g693) (ci:=(0,16,165,0,4)) (hints:=536872708) (before_sound known606 valid606) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps693 : List (Nat × List Nat) := [(693,[]),(700,[82,129,48]),(851,[118,130,81]),(858,[118,133,33,48])]
def known693 := extendKnown known606 5 maps693
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid693 : Known known693 := extendKnown_ok valid606 low693 (by decide +kernel)
def g627 : Forest := ⟨627,4,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none,noFactory,noFactorySound 627⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low627 : Lower (vars 627) (graphGoal 627) 5 :=
  lower_discard (g:=g627) (ci:=(0,16,99,0,4)) (hints:=16777217) (before_sound known693 valid693) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps627 : List (Nat × List Nat) := [(627,[]),(691,[118,130,81]),(860,[82,129,48])]
def known627 := extendKnown known693 5 maps627
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid627 : Known known627 := extendKnown_ok valid693 low627 (by decide +kernel)
def g573 : Forest := ⟨573,4,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none,noFactory,noFactorySound 573⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low573 : Lower (vars 573) (graphGoal 573) 5 :=
  lower_discard (g:=g573) (ci:=(4,0,569,0,4)) (hints:=8964) (before_sound known627 valid627) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps573 : List (Nat × List Nat) := [(573,[])]
def known573 := extendKnown known627 5 maps573
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid573 : Known known573 := extendKnown_ok valid627 low573 (by decide +kernel)
def g567 : Forest := ⟨567,4,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none,noFactory,noFactorySound 567⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low567 : Lower (vars 567) (graphGoal 567) 5 :=
  lower_discard (g:=g567) (ci:=(0,16,39,0,4)) (hints:=257) (before_sound known573 valid573) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps567 : List (Nat × List Nat) := [(567,[]),(798,[118,133,33,48]),(828,[82,129,48])]
def known567 := extendKnown known573 5 maps567
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid567 : Known known567 := extendKnown_ok valid573 low567 (by decide +kernel)
abbrev knownPrev_g543 := known567
def keyg543l6 (i : Nat) : Nat := 0xa00b508000738000000
def g543d5 (i : Nat) : Nat := 0xa50be44f611fa00
def g543l5 : Packing := (3,1,0,0,0,4,0,g543d5)
def g543d6 (i : Nat) : Nat := 0x3f
def g543l6 : Packing := (1,0,0,0,0,0,0,g543d6)
def g543samples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed4defc739b9f071fe3fc3c1e3e3c7ff1c1f83e38e3838ffece621f,0x12a010b062520c0510830098510494600584a1830412204b0ca4212),(0x77b1fff83e3e6f81fffffc01fc03f8f8e01ffffc0fc03f1c10fec64,0x884a010580a090c86204482282292181220946340a844a103052c44),(0xb9fe77ffc03f8ffe3fc7fffe0003ff00ffe3fc1ff0003fe01f39078,0x46010a102d402511041191080552102a48a22889a000b4814a29038),(0xfe3f87ffffc00fffc007fffffffc0000fffc001fffffc0001fc1f80,0x1c054240035584031262231120024c4931043124d26000215c0b00),(0xc03ff80000000ffffff8000000000000ffffffe0000000001ffe000,0x3fe957bef7fffe6db9b73bbddb9fbef7ffdff3d36db726db9ffeb12),(0,0),(0,0),(0,0),(0,0)]
def g543columns : IndexTree ColumnInfo := (.leaf [(0,16,15,0,4)])
def g543autos : Array (List Nat) := #[[],[33,48]]
def g543levels : Nat → Packing
  | 5 => g543l5
  | 6 => g543l6
  | _ => emptyPacking
def g543index : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 4 11 4 7 2 1 (keyg543l6)
  | _ => fun _ => none
def g543 : Forest := ⟨543,6,fun j => g543samples[j]?.getD (0,0),g543columns,g543autos,g543levels,g543index,noFactory,noFactorySound 543⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geomg543 : graphValid g543 (boundsBefore knownPrev_g543) = true := by
  unfold graphValid
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel, by decide +kernel⟩, ?_⟩, by decide +kernel⟩
  apply listPieces_all (d:=0)
  simp only [listPieces,IndexTree.values,List.length_append,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceDiv,List.take,List.drop]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg543_5_0 : block g543 5 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg543_5 : block g543 5 0 3=true := sg543_5_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg543_6_0 : block g543 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg543_6 : block g543 6 0 1=true := sg543_6_0
theorem tablesg543 : checkedTables g543 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g543 0 0 0 = true)
  · exact (rfl : block g543 1 0 0 = true)
  · exact (rfl : block g543 2 0 0 = true)
  · exact (rfl : block g543 3 0 0 = true)
  · exact (rfl : block g543 4 0 0 = true)
  · exact allg543_5
  · exact allg543_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low543 : Lower (vars 543) (graphGoal 543) 7 :=
  lower_forest (g:=g543) (i:=0) (hints:=8449) (before_sound known567 valid567) geomg543 tablesg543 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps543 : List (Nat × List Nat) := [(543,[]),(825,[118,130,81])]
def known543 := extendKnown known567 7 maps543
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid543 : Known known543 := extendKnown_ok valid567 low543 (by decide +kernel)
def g631 : Forest := ⟨631,5,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none,noFactory,noFactorySound 631⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low631 : Lower (vars 631) (graphGoal 631) 6 :=
  lower_discard (g:=g631) (ci:=(4,0,627,0,5)) (hints:=16777473) (before_sound known543 valid543) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps631 : List (Nat × List Nat) := [(631,[]),(892,[82,129,48]),(926,[118,133,33,48])]
def known631 := extendKnown known543 6 maps631
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid631 : Known known631 := extendKnown_ok valid543 low631 (by decide +kernel)
abbrev knownPrev_g755 := known631
def g755d6 (i : Nat) : Nat := 0x7f
def g755l6 : Packing := (1,0,0,0,0,0,0,g755d6)
def g755samples : Array (Bits × Bits) := #[(0xbdc3c79cfe37f9fe3fbfffe003f800fe07c0fe3fc1fe1fffe07ffc1fff1fe1ffffffffffe0001fc0007f01f80ff007e07fc03ffffc07ff81fffc01ff00ffffffffffffffe007001c1f078060e03fff83f83fc0380ffffffffffe10c81f330fff,0x4218102209480409404040028013020540220120902120401102084800841208009200400a00092048148012008812004088088440820801088205020840a20052101420100404100a0490008022910220124420088680260542108812210912),(0xf6dc0fe33fc7e63fc7ce79e0fc001ffff83f003ffe001ffc1f83ffe07ffffe0fc1fc0ffe001fe0007ffffe07f00007ff80003ffe03f81ffe03ffffffff01fc07e01fffc0007807ffe0f8007f003fe07c1fc3fffff03c0e0ffe001f319ccdf25c,0x923620c401009501830821c0924a41824404c41008a421062189102920880b213005000b088a00902a10c80144264a109114518850882a41114484c4403043480a4a104602800a520582275048d220c0940914a60184a4978040a318c88a24c),(0,0),(0,0),(0x28a00803c00707c0060f819f00001f00003fffc000001f001ffc00007fe0000ffe000f801fe000007f800007fffff80000003f0003ffe00003fffe000001fff8001fc0001f8007e000ffff80003e007fe003ffc0003ff00fc0039c3e18f1c398,0xd75fb6f63bfc7d3be9f85e66fad7caadeea6152bbbedecd5b52a7b7b249dbf5cb1b6ba57faba9b365b74d536add8b68b52bdaeadcb96ba1d6bda9516ddd5eb51d6db3569b584a5731aaff69489379536e533fda0a9afd8af8d4b9cbe1af1cb9a),(0xcffff003fff807fff80ffe1fffffe000003fffffffffe0001fffffff8000000ffffff0001fffffff80000007ffffffffffffc00003fffffffc0000000001ffffffe000001ffff80000ffffffffc0007ffffc0000003ffff00003e03fe0fe03e0,0x30010f581005b800029000a810609c50b30828060848061ac01020020e21c4610020028a60c2c24312002840c16140c6070504101020d30830503828161850a304818182c299280000310726238000595da4090142316dc11011402540de02e0),(0xf3ffffc000007fffff0001fffffffffffc00000000000001ffffffffffffff0000000001ffffffffffffff8000000000000000003fffffffffffffffffe0000000000001fffffffff0000000000007fffffffffffc000000003ffc000fffc00,0xf0c80403bdaed021000b6de0a0811060c23cb1b42d7198e31843425048111009a43b2b6d431313a41c46b064898d8014642628c162c51c51c26321b0989062c2071206331b57b65a5304440012201863963b2e358f0181020063f5c000775c00),(0xf03ffffffffff8000000001fffffffffffffffffffffffffe000000000000000000000001ffffffffffffffffffffffffffffffffc0000000000000000000000000000001fffffffffffffffffffff8000000000000000000003ffffff000000,0xfd20000210007bdb56df750c30600810430c038318110801e63839c70de198e39c3cc719c1c1c386078c1870e0e0718783830e1830600618383c1c0e0e18304181c383c1c66c79f9cc67858dc39de02000230060c02000c2182bfdabf000000),(0,0)]
def g755columns : IndexTree ColumnInfo := (.leaf [(0,16,227,0,5)])
def g755autos : Array (List Nat) := #[[],[118,81]]
def g755levels : Nat → Packing
  | 6 => g755l6
  | _ => emptyPacking
def g755index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g755 : Forest := ⟨755,6,fun j => g755samples[j]?.getD (0,0),g755columns,g755autos,g755levels,g755index,noFactory,noFactorySound 755⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geomg755 : graphValid g755 (boundsBefore knownPrev_g755) = true := by
  unfold graphValid
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel, by decide +kernel⟩, ?_⟩, by decide +kernel⟩
  apply listPieces_all (d:=0)
  simp only [listPieces,IndexTree.values,List.length_append,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceDiv,List.take,List.drop]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg755_6_0 : block g755 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg755_6 : block g755 6 0 1=true := sg755_6_0
theorem tablesg755 : checkedTables g755 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g755 0 0 0 = true)
  · exact (rfl : block g755 1 0 0 = true)
  · exact (rfl : block g755 2 0 0 = true)
  · exact (rfl : block g755 3 0 0 = true)
  · exact (rfl : block g755 4 0 0 = true)
  · exact (rfl : block g755 5 0 0 = true)
  · exact allg755_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low755 : Lower (vars 755) (graphGoal 755) 7 :=
  lower_forest (g:=g755) (i:=0) (hints:=1358954497) (before_sound known631 valid631) geomg755 tablesg755 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps755 : List (Nat × List Nat) := [(755,[]),(988,[118,133,33,48])]
def known755 := extendKnown known631 7 maps755
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid755 : Known known755 := extendKnown_ok valid631 low755 (by decide +kernel)
abbrev knownPrev_g727 := known755
def g727d6 (i : Nat) : Nat := 0x7f
def g727l6 : Packing := (1,0,0,0,0,0,0,g727d6)
def g727samples : Array (Bits × Bits) := #[(0x6e01cf19ff86f9fc7cf3f1e0001f81fc1f80fc7ffe07f07ff03f0ff03ffe0ffc1ffe0ffff000003fc07f03f807f007ff81ff00fffc03fc01f80fffe03fff80fffc0ffffff0000f0707c3e01f8781ff83e030ff03ff81ff07ffff206cc7a3399f,0x915c14a402698412830886052a01388a8452022244908ca90880a821904950814048582405490012a41480924049118a01122488a0a09224a108a4411214129088290a9109100a040282a49105009143222054029490e4048aa3204c82a22912),(0xf77e0fe67ff8f7ff8f7ffe61ffe001ffe07f007ffff8007e0fffffffc1fff0fffffff03f800fffc0007ffc07f80007fffe0000fc03fffffffff03fffc03ffffffff01fe0001ff007f83c001ff801e07fffff07fc07fffff83c003990e4fccfe4,0x8816008800200203080009800484210108048800802110011080244028005200080014028002840082109000a02203084204111050504400a2008880060a021120030021002a00148140806c8112204484101480143099030041110641084c4),(0xbf9ff0078fff067ff07cff9e0ffffe00007fff83ffffff800fc00ffffe0000ffe0ffffc00ff01fffff800007fffff81fffffff0003fc0001ffffc000003fff01ffffe0000fe07ff8003fffe0fffe007c003ff80007fe07ffc003c61f38c70e78,0x40640dd05420b88005010021c28208a12d1410287051040b60063080801a62080510400590520284c50010a0d0914083181c1400282850393141050246891414e0a200a1616013280008c1a0118c0059043a9810a6342667002a840a10c70a38),(0,0),(0x4e00007f0000780007f001ff0000000007ffffc000000000ffff000000000ffff0000000fffe00000000007ffffffe00000000003fffffe00000000003ffffe000000000fff8000003fffff0000007fffc0000007fff8000003f81fc0f80f80,0xfb5fbefc4effdc77dfc8bfed6fd77ddbde5a2a3adddfafedba92a9edf5ddfbd354dafaeefd6b5a36b774ead6e6e9b5da2d56f6bbb3b3daada1eba6dbb73e5adcbabb5ad5bbb58aa4c6affddb4525956ffea8d42ad7f9f4359ab3f85fc2fa2f92),(0,0),(0x38fffff8000007ffff80001fffffffffff800000000000000fffffffffffff00000000000ffffffffffffff8000000000000000003ffffffffffffffffc00000000000000fffffffffc000000000007ffffffffff80000000003ffe000fff000,0xc70808876f75e842005fdb618b0410e1887cb3736165ce71cc240d092111409a761d6cb7518393272646b0e484cdc500519898c2c2c26331c58e3713240c1c98c0c38319cdd95fb694c2911000481873973ce6b3e420404600c3eee000ef7000),(0xc0fffffffffff8000000001ffffffffffffffffffffffffff000000000000000000000000ffffffffffffffffffffffffffffffffc0000000000000000000000000000000fffffffffffffffffffff8000000000000000000003ffffff000000,0x3f1100000840077b6aeeedd00c1861021060c043818608400f38ce0e39e18ce398e18f386e0c1c383878c307070e061c61e0e0e3030383c0060c381c383060e1030c1c1e0e1e6cc7e7331e1ce671de02180000c30041808023017bf5ef000000),(0,0)]
def g727columns : IndexTree ColumnInfo := (.leaf [(16,0,198,1,5)])
def g727autos : Array (List Nat) := #[[]]
def g727levels : Nat → Packing
  | 6 => g727l6
  | _ => emptyPacking
def g727index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g727 : Forest := ⟨727,6,fun j => g727samples[j]?.getD (0,0),g727columns,g727autos,g727levels,g727index,noFactory,noFactorySound 727⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geomg727 : graphValid g727 (boundsBefore knownPrev_g727) = true := by
  unfold graphValid
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel, by decide +kernel⟩, ?_⟩, by decide +kernel⟩
  apply listPieces_all (d:=0)
  simp only [listPieces,IndexTree.values,List.length_append,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceDiv,List.take,List.drop]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg727_6_0 : block g727 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg727_6 : block g727 6 0 1=true := sg727_6_0
theorem tablesg727 : checkedTables g727 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g727 0 0 0 = true)
  · exact (rfl : block g727 1 0 0 = true)
  · exact (rfl : block g727 2 0 0 = true)
  · exact (rfl : block g727 3 0 0 = true)
  · exact (rfl : block g727 4 0 0 = true)
  · exact (rfl : block g727 5 0 0 = true)
  · exact allg727_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low727 : Lower (vars 727) (graphGoal 727) 7 :=
  lower_forest (g:=g727) (i:=0) (hints:=553648385) (before_sound known755 valid755) geomg727 tablesg727 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps727 : List (Nat × List Nat) := [(727,[]),(734,[118,133,33,48]),(1009,[118,130,81]),(1016,[82,129,48])]
def known727 := extendKnown known755 7 maps727
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid727 : Known known727 := extendKnown_ok valid755 low727 (by decide +kernel)
abbrev knownPrev_g702 := known727
def g702d6 (i : Nat) : Nat := 0x7f
def g702l6 : Packing := (1,0,0,0,0,0,0,g702d6)
def g702samples : Array (Bits × Bits) := #[(0,0),(0x650839e1867c39c0fc37cce000f000fc07f03f001f83fc07c0fc00fff03f07ff07ff80f1f0001fe0003fc01fc0fe0003fc07e03f01fc003fff03f807ffe03ffff00ff007f007f007870f801f031f07801ff0f81ff81ff87f00ff18ca649b39b3,0x9a77425a6992c31d12cc33157a0b680acd2544ce522d4a2a252ab6a62350ac92a8225b0b494900bd2012ec9254a493106712b41a9329152495a310ce4934ac9d20548b2caa05b447850aa515430ba4a212d05c89c896687a09ab18ca64932932),(0xbf37c1fe3fffc1ffffc7ff607f01ff0007ffc007fffffff800ffffffffc007ffffffff01f01fe0000fc0001fff0001ffffffffc001fffffffffc0007fffffffffff00007f078000807f001ffffe007ffffff001fffffff8000fc210f87fc3fc3,0x40882c0080201c000010008a00a4022110400910840090804a40000040051004000400340200220241400104820824248840428004508041220841108241010241001051001800880250082214200118a52501121128950002502101024c14c1),(0xcec7fe00387ffe073ff8ff9f8001fffff8000007e003ffffff001f07fffff83ff87ffffe0fe000000fffffe0000001fc0007fffffe000fc07ffffff81fffc01ffffffff80f80000ff80001e003fff803e07fffe0ffe03fffff03c00c78e7ce7c,0x312101dd45420168a205006054492410450a34e211492124208a50948920818005484801505214948a24a44000a14052222491145102091444922442141424548a4909002a848905500001508292900250489440e6822254a803c00c50a28a28),(0x8f800003f800007c000f01ffffe000000000007fffc000000001ff80000003fff8000000ffffffff0000000000001fffff8000000000fff800000001fffffe0000000000ffffff0000001fffc000003ff800000ffffc0000003fe0f80f80f80,0xf727b7ffe5776ffcb77f0fe35669b6dbe7efbefb596b3bb6b3ef7ad5ebb6dde8a56eeddffb7b56d4eb36b6562af5f97af2b699b6d99badb674dab5e3df9eb654eb6dad9dbfeeddd5504a51fbda9ad44b79ccd658ffdf2356ac1bfe0fd0fa8fa8),(0xfffffffc0000007ffff001ffffffffffffffff80000000000001fffffffffc0000000000ffffffffffffffffffffe000000000000000fffffffffffe0000000000000000ffffffffffffe0000000003ffffffff000000000003fff000fff000,0xf002208837fbb7b0000055ac18803861818318439e71c1c73c7184010204010e318f0e6663838707038707870c387060c0c002186060c61878e0c183070707870381c1e1c330e1e99b631c00100000139e7ee79c430c04183062b5a000fff000),(0,0),(0xf0fffffffffffff80000001fffffffffffffffffffffffffffffe00000000000000000000ffffffffffffffffffffffffffffffffffff0000000000000000000000000000ffffffffffffffffffffffc00000000000000000003ffffff000000,0xf04011000000006fbaeaa506001c082060c208400020200008218e60c38e630c67070898c1c18180c38381830c1818303071c208183082000030604181838180c0e0e060c470e06648c619ce3dce6600000000084100060c0814a5efd000000),(0,0)]
def g702columns : IndexTree ColumnInfo := (.leaf [(0,16,174,0,5)])
def g702autos : Array (List Nat) := #[[]]
def g702levels : Nat → Packing
  | 6 => g702l6
  | _ => emptyPacking
def g702index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g702 : Forest := ⟨702,6,fun j => g702samples[j]?.getD (0,0),g702columns,g702autos,g702levels,g702index,noFactory,noFactorySound 702⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geomg702 : graphValid g702 (boundsBefore knownPrev_g702) = true := by
  unfold graphValid
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel, by decide +kernel⟩, ?_⟩, by decide +kernel⟩
  apply listPieces_all (d:=0)
  simp only [listPieces,IndexTree.values,List.length_append,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceDiv,List.take,List.drop]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg702_6_0 : block g702 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg702_6 : block g702 6 0 1=true := sg702_6_0
theorem tablesg702 : checkedTables g702 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g702 0 0 0 = true)
  · exact (rfl : block g702 1 0 0 = true)
  · exact (rfl : block g702 2 0 0 = true)
  · exact (rfl : block g702 3 0 0 = true)
  · exact (rfl : block g702 4 0 0 = true)
  · exact (rfl : block g702 5 0 0 = true)
  · exact allg702_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low702 : Lower (vars 702) (graphGoal 702) 7 :=
  lower_forest (g:=g702) (i:=0) (hints:=544416032) (before_sound known727 valid727) geomg702 tablesg702 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps702 : List (Nat × List Nat) := [(702,[]),(890,[118,130,81]),(949,[82,129,48])]
def known702 := extendKnown known727 7 maps702
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid702 : Known known702 := extendKnown_ok valid727 low702 (by decide +kernel)
def g695 : Forest := ⟨695,7,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none,noFactory,noFactorySound 695⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low695 : Lower (vars 695) (graphGoal 695) 8 :=
  lower_discard (g:=g695) (ci:=(0,16,167,0,7)) (hints:=536871169) (before_sound known702 valid702) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps695 : List (Nat × List Nat) := [(695,[]),(862,[118,133,33,48]),(883,[118,130,81]),(956,[82,129,48])]
def known695 := extendKnown known702 8 maps695
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid695 : Known known695 := extendKnown_ok valid702 low695 (by decide +kernel)
abbrev knownPrev_g701 := known695
def keyg701l7 (i : Nat) : Nat := 0x130939a60200000d4000020
def g701d6 (i : Nat) : Nat := 0x7a8a0bf2af78cfec23fa00
def g701l6 : Packing := (4,1,0,0,0,5,0,g701d6)
def g701d7 (i : Nat) : Nat := 0x7f
def g701l7 : Packing := (1,0,0,0,0,0,0,g701d7)
def g701samples : Array (Bits × Bits) := #[(0xffffffffffffffff57a21e78c7e7333fc67fb807803f07e0fe01e3f01f0f8787fffc1fc3ffe3f878fe0007f8007e07e1f8001f81f81e07e07e07fffff87e07fffe07e01fe07ff80780421c03c047878787fff870fff01c3c07ff882c867e3c4f,0xa855c8953008448129c041506802a44a19240428c41148504088c92650110485811220344023044112118244b40524491862524030442146211440c890c50404a04010225242c505048c601022919828214c882c84540c4a),(0,0),(0x9de5e07f0ff83ccff877d8780fc007ff001fffffe00ff87878ffe003e1ffff80f007f8001f8007fe001fffffffe007ff81f81f81ff8007807fffffe0007e00780083e03ffff807f878780f80f0ffffc00780113f19992f8c,0x621a5b005083c11002802605308848822a48814245640283011043480240201b024028928280216420a2a490194009850a29409499104a0a8a228240a31028180482a084868801b028312a84b422ae800e05110a11192a8c),(0xe6d9ff8009ffc0f3ff87e7800ffff800001e03fffff0007f80fffffc01ffffff01f800001ffff800001fe001fffff80001ffe001fffff8007fffffffff80078000fc003c007ff8007f800fff00fffffff800e030e1e1cff0,0x19248076a5001e0a2058186249042414d18054849009514054a29020d40244009c148525144b1001050512492488a41051440a492249201451051492100514844868002a2064d0041502445200cd1132a008e030c0e08560),(0x1e00000e0000fc000607fff0000000001ffc000000007fff00000001fc000001ffffffe0000000001ffffe0000000001fffffe000000007ff80000000007ffff00003fff8000007ffff00000ffe0000000fe3f01fe0f00,0xfff5fdfff5bdff8b7ff9fb736fb6f7dffdf556eef6bdfdf574fafbbeff936fefff5eb5bdd66bd55dd7d7d76db6ddb6dddd777b6db76d775f7dd5d6faddd7dfefed68933ff766f5575fdf765aaaffd9bab34efe3fc5fe8f6a),(0xf8fffffff00000fffff807ffffffffffffe000000000007ffffffffffe00000001ffffffffffffffffe000000000000001ffffffffffffff80000000000007ffffffffc0000000007fffffffff0000000000ffc001fff000,0x70010200fd6ab000002ac04021841046019990718c626020040020080c471322660c1c2070c6188618604300100c10620818c11c430441818620703061861310e8ec5800400002062638f6ccc060200c410558001abf000),(0,0),(0xff1fffffffffff00000007ffffffffffffffffffffffff80000000000000000001fffffffffffffffffffffffffffffffe0000000000000000000000000007ffffffffffffffffff80000000000000000000fffffe000000,0xe10044000000efb56d50400c208618810002080008406466831c33191b8644c98706041871861186181841c611061841061060004180606184181c1861864670711a333877664604040000008800230060aa75ee000000),(0,0)]
def g701columns : IndexTree ColumnInfo := (.leaf [(0,16,173,0,5)])
def g701autos : Array (List Nat) := #[[],[82,48]]
def g701levels : Nat → Packing
  | 6 => g701l6
  | 7 => g701l7
  | _ => emptyPacking
def g701index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 3 11 4 7 2 1 (keyg701l7)
  | _ => fun _ => none
def g701 : Forest := ⟨701,7,fun j => g701samples[j]?.getD (0,0),g701columns,g701autos,g701levels,g701index,noFactory,noFactorySound 701⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geomg701 : graphValid g701 (boundsBefore knownPrev_g701) = true := by
  unfold graphValid
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel, by decide +kernel⟩, ?_⟩, by decide +kernel⟩
  apply listPieces_all (d:=0)
  simp only [listPieces,IndexTree.values,List.length_append,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceDiv,List.take,List.drop]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg701_6_0 : block g701 6 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg701_6 : block g701 6 0 4=true := sg701_6_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg701_7_0 : block g701 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg701_7 : block g701 7 0 1=true := sg701_7_0
theorem tablesg701 : checkedTables g701 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g701 0 0 0 = true)
  · exact (rfl : block g701 1 0 0 = true)
  · exact (rfl : block g701 2 0 0 = true)
  · exact (rfl : block g701 3 0 0 = true)
  · exact (rfl : block g701 4 0 0 = true)
  · exact (rfl : block g701 5 0 0 = true)
  · exact allg701_6
  · exact allg701_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low701 : Lower (vars 701) (graphGoal 701) 8 :=
  lower_forest (g:=g701) (i:=0) (hints:=536879876) (before_sound known695 valid695) geomg701 tablesg701 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps701 : List (Nat × List Nat) := [(701,[]),(859,[118,130,81])]
def known701 := extendKnown known695 8 maps701
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid701 : Known known701 := extendKnown_ok valid695 low701 (by decide +kernel)
def g607 : Forest := ⟨607,7,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none,noFactory,noFactorySound 607⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low607 : Lower (vars 607) (graphGoal 607) 8 :=
  lower_discard (g:=g607) (ci:=(64,0,543,0,7)) (hints:=16785665) (before_sound known701 valid701) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps607 : List (Nat × List Nat) := [(607,[]),(671,[118,133,33,48]),(889,[82,129,48]),(953,[118,130,81])]
def known607 := extendKnown known701 8 maps607
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid607 : Known known607 := extendKnown_ok valid701 low607 (by decide +kernel)
def g575 : Forest := ⟨575,7,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none,noFactory,noFactorySound 575⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low575 : Lower (vars 575) (graphGoal 575) 8 :=
  lower_discard (g:=g575) (ci:=(32,0,543,0,7)) (hints:=8449) (before_sound known607 valid607) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps575 : List (Nat × List Nat) := [(575,[]),(829,[82,129,48])]
def known575 := extendKnown known607 8 maps575
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid575 : Known known575 := extendKnown_ok valid607 low575 (by decide +kernel)
def g763 : Forest := ⟨763,7,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none,noFactory,noFactorySound 763⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low763 : Lower (vars 763) (graphGoal 763) 8 :=
  lower_discard (g:=g763) (ci:=(8,0,755,0,7)) (hints:=1358970881) (before_sound known575 valid575) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps763 : List (Nat × List Nat) := [(763,[])]
def known763 := extendKnown known575 8 maps763
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid763 : Known known763 := extendKnown_ok valid575 low763 (by decide +kernel)
def g766 : Forest := ⟨766,7,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none,noFactory,noFactorySound 766⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low766 : Lower (vars 766) (graphGoal 766) 8 :=
  lower_discard (g:=g766) (ci:=(32,0,734,0,7)) (hints:=561193248) (before_sound known763 valid763) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps766 : List (Nat × List Nat) := [(766,[]),(983,[118,133,33,48]),(1013,[82,129,48]),(1018,[118,130,81])]
def known766 := extendKnown known763 8 maps766
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid766 : Known known766 := extendKnown_ok valid763 low766 (by decide +kernel)
def g639 : Forest := ⟨639,8,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none,noFactory,noFactorySound 639⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low639 : Lower (vars 639) (graphGoal 639) 9 :=
  lower_discard (g:=g639) (ci:=(32,0,607,0,8)) (hints:=16785665) (before_sound known766 valid766) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps639 : List (Nat × List Nat) := [(639,[]),(893,[82,129,48]),(927,[118,133,33,48])]
def known639 := extendKnown known766 9 maps639
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid639 : Known known639 := extendKnown_ok valid766 low639 (by decide +kernel)
def g735 : Forest := ⟨735,8,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none,noFactory,noFactorySound 735⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low735 : Lower (vars 735) (graphGoal 735) 9 :=
  lower_discard (g:=g735) (ci:=(128,0,607,0,8)) (hints:=553656577) (before_sound known639 valid639) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps735 : List (Nat × List Nat) := [(735,[]),(1017,[118,130,81])]
def known735 := extendKnown known639 9 maps735
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid735 : Known known735 := extendKnown_ok valid639 low735 (by decide +kernel)
def g759 : Forest := ⟨759,8,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none,noFactory,noFactorySound 759⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low759 : Lower (vars 759) (graphGoal 759) 9 :=
  lower_discard (g:=g759) (ci:=(0,16,231,0,8)) (hints:=553648385) (before_sound known735 valid735) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps759 : List (Nat × List Nat) := [(759,[]),(990,[118,133,33,48]),(1011,[118,130,81]),(1020,[82,129,48])]
def known759 := extendKnown known735 9 maps759
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid759 : Known known759 := extendKnown_ok valid735 low759 (by decide +kernel)
def g887 : Forest := ⟨887,8,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none,noFactory,noFactorySound 887⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low887 : Lower (vars 887) (graphGoal 887) 9 :=
  lower_discard (g:=g887) (ci:=(4,0,883,0,8)) (hints:=21491613953) (before_sound known759 valid759) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps887 : List (Nat × List Nat) := [(887,[]),(894,[82,129,48]),(958,[118,133,33,48])]
def known887 := extendKnown known759 9 maps887
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid887 : Known known887 := extendKnown_ok valid759 low887 (by decide +kernel)
abbrev knownPrev_g703 := known887
def keyg703l7 (i : Nat) : Nat := 0x14680039000000000
def keyg703l8 (i : Nat) : Nat := 0xb8d156525b9aa7c65a7647030c8b9480dd9bc109fa2c05c83361e9400000124593b3792b504d255521f8f4b60012a02780000067110a890000000000070af041d60366e00180e08047b31689029a8a7c00386c68448000499620038a800a2da004bfbe000111539b50010ed613ad44a11608a1a2640bf0ec8e015cf005d400010f765e902668e2d33b09a043f55873400101262c20000046032818007060428048092001608000
def keyg703l9 (i : Nat) : Nat := 0x5d99fa943971c10a07d3a684510c16324c79680ee349bdaf5bdd9100d5782d5a888cf8e18721245177540000000000000006a04f5d60420d3017c6bfd972b8000000474f019b8000cfc0000c6027c96f4a49000018701a75fe9ba7fd1c00000000086c00000350e88dedaefc00358363264365c00000000210018d428000001200d2b66aaae0c0002f37068000000694ee80025c1ca840773912c1b0a14b066dca5be4b0869a483b61d93c0028cab500029a8d9891800229374c2b18d4c7f43f657809c568ee4b0451222358d66e521e7150000000000a3c0023651c8740003de15e8000dfc000ab72c321b2340005b400024771ae0f481834558e0bb3ce2a8f000000326c00346400084800000132c001cfb84668e211da372330c5de315b1201c69c94ea7aaf82276f4733c4e48a6cc9551c5d9e8585d2ce9ad1b4758a8ba0aec62905b0967432baa9cbd2ed4d0534e4d49d50a1226e4ca366622caa5273401f1c16b2f32388da16f2c58e642c5f62c9c4114bdf11770a545d9efa601cdf624b48de4319465d4d5c18100000408030b80402020d8001801020f41000008006c0b0009040000482c0c05020000209060000605028001600080000a0f0202c1007000440202158147e00010040a08058001606298002c1b0007c5203
def keyg703l10 (i : Nat) : Nat := 0x1e2233dfa7f245547c78900000018e7800001ad004d49e007b59648000458431d4fc8000087a580058e00041400041c0000
def g703d6 (i : Nat) : Nat := 0x14a12bd69a215291267ab3442c1224ed4668848244
def g703l6 : Packing := (3,4,4,0,0,4,0,g703d6)
def g703d7 (i : Nat) : Nat := 0xa84a0498400281000054202a10532820140b5282000984a049840000099411528200000000000000000000000000010000000000cc1cc1cc10520800870800e60e60e60e6080004200210010801482042000000021a7a92a1a819f2709ae6698655942448fe2c89e1b822037f9f2799da755d072dc66cda066d966458c61d825f5785cd6e5a56457d5a5555052d465053c4c12b49921471174490d420fc3c0e437cd331cbb2bca325c8b1fc7a1d4691905814c471083d0c4250801b0581103000fb96048244fad2148244fad5248244bbe8858a44bbe8854a44ebd6258644bbe8858644bbe8854244bbe8854644fb56148644bbd6848644bbd5848644bbe8848644ebd6158244bbe8858244f3d5154244f3d5254644bbd2844244bbd5844244bbd6844244fb92044244fb55144244bbd5808244bbd6808244bbe8848244fb41848244bbd6848244bbd5848244f365591211eb666912119f47848211bb4484c211f4e558ce22ece668ce22eae6691222fe22284600fb24484600f725584600ef26684600fca3388a00faa4488a00f6a5588a00eea6688a00f5a558ce00eda668ce00f2e5591222eba6691200b795809e0097d5809e00bb8484c200fc63388a11fa64488a11f665588a11ee66688a11f56558ce11ed6668ce11f3a559120097d5809d639f51809d639f90809d638fd689dd529dd3811d6197d5809d619dd3809d619f90809d619ec2859d318fd6809d3197d5809d319f90809d3197d589dd60fd233846009bc4855d309be8811d309bc484dd209f5189dd209bc484dd10abc484c266b3c484c2559dd3811e229bc4841e22bac484c222bcd3811e22bac4841e22aed6801e22bcd3801e229bc4859d30
def g703l7 : Packing := (86,3,4,0,0,10,0,g703d7)
def g703d8 (i : Nat) : Nat := (if i<1 then 0xb7db69b3db29b15b01aedad9ac5ab1a85a71a5da49a35a21a0d9f99e59d19a599196595193d9298fd8e98d58a989588186d8598458318057f17ad7817557296e56b968d66164d6215f55b159d5595154e94a549146543940d3f93b538935d3313052d92ad28126d2412152011d51a917d16913d0f90cd08905d031004f90f7cf38f0ceb0e84e70e5ce30e04dd8dacd80d6cd40d14d00cbcca8c94c80c6cc58c44c30c04bf0bdcbc8bb4b70b44b18aecac0a94a68a3c9f89b497092c9008d48a88648207f47b079c7887747486ec69061c5c059455050c4b043c3c83542f82b42581fc1a01440d005c003f6b1445fb54a22fd885117ed3288bf690c45fb48222fd841115fd6788afeabc457f11e22bfa6f1177d21956fe83c45bf99a22efcab117be4488bef19c45fb58e22fdaa7117ed6188bf6a8c45fb4c622fdac1117ed5088afe8bc45df10255efa612af7d20957be104abdf44255f7ac5227bd52913deb0c89ef54644f7a43227bd60913ee88467ef48244f7841227bd10913eeb1467f754a33fbac319fdd518cfee90c67f758233fbaa119fdd208cfee10467ef54244ff261007f920803fc884017f11e00bf84f006fe66803bf2ac01ef91200fbc67007ee22803fb08c01fb10222ff2a7007f962803fca9401fe10a00ff265007f961803fca8c01fe4c600ff243007f847803fc13c01fe88a00ff2c7007ed3088bf688445fb59e22fdaaf117ec4788bf69bc45fb45e22fda0f117ec0788bf73bc45fd58e11ff2a1007f562847faa9423fd10a11fea6508ff560847faa8423fd10211fea6108ff520847fa10423fd88a11ff2c1007f553847ee99263fd54531bface98dfd574c6fe13a637f9dd31feac290ff531486feb3a437f55d21bf88e90dfd27102ff3ba43bf58d60dfac2b05fc47582fe13ac17f9dd60efaa2a85fc47542fe13aa17f9dd50bface205fd57102fe9ba437f9dd63bf84ea9dfe7754f7eb1ac57f11d62bfceeb177d5354afe23aa57f9dd52bface215fd5710afe8b8857f9dd51bfcee217dd634cafeb3a657f55d32bfcee996fd62586fe23ac37f09d61bfceeb0f7d52546fe23aa37f09d51bfa0e215fd67082feab8417f4dc20bfa2e107f551443fc902217f59d10bfaae885fc47442fe9ba217f49d10bf84e887f9200837e214cdbf4ca66dfa63336fd2199b7e204cdbf4c266dfa41336fc2099b7e884cddf10a55efa652adfc2758eff3ba217f09d30bfcee987ed52483f6212417f55d30bfa2e205fd674c3ee98a61f754d30fbac6987ed21483fcb0241ef11d30bface905fd57482fe23a417f4dd20efa632aff417482ff3ba41fe4c120df4cd0077a55803dd22401f68ce00fe423007ea22802de23a61bb99a22f5c89116be669139f2ac89f38ce22fcc4508fd633847db22423dd95611deccd08ede668cfaf2ac67db95622 else 0x2a10000a04000400a4158200c010012c72014a411c00000004c200020028100184e66d4662090c2b336a3310485184e6019882428c2b300cc412154e66d98823b09cc029104702a9ccda9104798a89924c5080a840002610281030acc02910470281024108010012c605322411c000000054200000000120800000000001308120800054200261000000013080418530660cc112614c1142b040285208910811ac28c4124114010040a4100200e2144158330660cc15829040b05208220c41882088228c29822cc2982205208810a0100a88248220400e20800b04a086110218409056080400400000000140800000b308a0cc198218520cc18821cc21061063085184204508e10c410a2092088b080002c1624506c48a0d64a4508b48a0d40c8a0ab044c48a0d64a4508c4caa846264d422d228390412d20835a4106c4820d89041b1348a1189a4508c48a0e98695a94693291e8f28de8b288685a82e81a7d67c27ae6f26de6ca6b66a268e67a64e63a60e5fa5e65ba5a65924be3ea3162421860ca0b5ff9f85f41f2df01eeded9ec5e99e85e59e45d89d75d49d35d09cc5cb1c9dbe1bcdbb9ba5b91)
def g703l8 : Packing := (218,2,4,0,0,12,0,g703d8)
def g703d9 (i : Nat) : Nat := 0xa35a4923567ba146b2264a28d7221649124a35924628c865956440e45591122146b4c886225065948940ccb32c89448ab22503918a3224c528c8932ccb4a2442ad281c886324451a4cb21b159cb744910896e8521912dd064362b3350443e2b3351643e2b396e843e2b396c86d0f0cbbadfaf29ea02679122680de5709a46056350131438e12f89b1cc4b08c00ff803fe22ff443fc20ff483fd30ff543fd60ff487fd63ff54ffd62ff54bfc42ff4cbfd61ff547fc40ff4c7fa00bf99b7e55ef913de33fb88bf611
def g703l9 : Packing := (26,1,4,0,0,10,0,g703d9)
def g703d10 (i : Nat) : Nat := 0x8532b437f
def g703l10 : Packing := (1,0,4,0,0,0,0,g703d10)
def g703samples : Array (Bits × Bits) := #[(0x7e00fc07f00fffe01fe01ffffff80fc0fc07f803f03fffff003f803fffe007fff007e007fc01ff800fe01ffffff80003c00080860e0001e01f91c1e043c1ff07c0ffff8860e060fff07807fc03fc70e03c01c0ffff90402d99071cf80ece621f,0x48850042244430188411110c80001800804102040040a180610208911001200c00440620808842010405110c80200024800800008020124889080a8028092044010c300002000202048622421306040281100214c1040299102089000ca4212),(0x8000fff8000fe000001fe03ff007f000fff80003ffc1fc00ffc0003ffffffffffff80007fffe00000fffe03ff00001fc000f0707f0003e001fe1fe007c01e0003f0f80707f007f0e0f8007ffffff80ffc001ff0f8061864e1e249323350fec64,0x511186510419882a0292242112915028571240c51c91902148424912663644d11e90008dd12008ccaa928065024c816c108f050750942a081361561264112482250b08506b12290a4c80854ac6c680be80226a0e00e186460e24922325052c44),(0xfffffff0001fe01fffc00007ffff00000003fffe0000ffffffc03ffff801fffffff8000000000fffffc000001e00001007f80007ffffe07e00007ffe00f83ff0007f80007ff00ffff81ffc03ff000001fff000020873e038e3c439f39078,0x218a0c1400140a4414044412224c20040810a6108204a128482010840800461228220000205014504440050900600011002a800204441a002000008cc00280a60112a800452b08111281128113a00000594c005020801401041c418a29038),(0xffff00000000001fffe000000007fffffffffffc00000000ffffffffc0000001fffffffffffffffff00000000007e000001ff8000007c000007fffff800000ffc000007fffff80000fffffe00003fffffffe0000007c007c07c0fc07c1fc1f80,0x48580204080c1213108a09098a4449249a26246004008090a42a6824031226498a4514c6a2492864000081018826a122220ad0000006a1101859a53900001096a008224452b100000e66c780406244d532b00000087c007c0580bc02815c0b00),(0x1ffffffffffff800000000000000000000fffffffffffffffe0000000000000000000000000007ffffffe000000007ffffff800000000000ffffffff80000000000ffffffffffc000000000000007ff07ff800fff801ffe000,0x6ddcd3366f6edb9bdefb9dbdee774db6dab735f347acdafcff3f7dbfbf9b376dca75d6f6bb6dae7671d6f5b5ed3ffbb7fbaad0214947f7fdddd9b5bd22a59adff3bdfbc65ab918a92ffff7fff3fa66d5bab906634e7ff07ffd82fffa81ffeb12),(0x1fffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000007fffffffffffffff8000000000000000000fffffffffffffffffff00000000000000000000000007fff800000fffffe000000,0x6000c08181040c070c0e0e03878e38e0c3c1838630e0e0380c0e060c03c07003820700c07030078607060601c0cc3883d31bb26270000100000000000800e33cce3c7f7cde7ccdc40301018080080600c01884104b2d000000f76ffe000000),(0,0),(0xffffffffffffffe00000000000000000000000000000000000000000000000000000000000000000000000000007ffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000007fffffffff000000000000,0x7180e3070e0e1810181010300c0000000304060008010300c0307038301c07800c0418070381c078081818380e0711c33c0ce4458d87399e1e7df9de7331dc0400004000000000000844060203000018230020086034d2febfef000000000000),(0,0)]
def g703columns : IndexTree ColumnInfo := (.fork 6 (.fork 3 (.leaf [(12,16,163,0,4),(16,0,166,9,6),(0,16,175,0,8)]) (.leaf [(32,0,671,0,8),(2,0,701,0,8),(128,0,575,0,8)])) (.fork 3 (.leaf [(8,16,167,0,7),(0,24,163,4,5),(160,0,543,0,7)]) (.leaf [(1,0,702,0,7),(3,16,172,0,4),(8,0,695,0,8)])))
def g703autos : Array (List Nat) := #[[]]
def g703levels : Nat → Packing
  | 6 => g703l6
  | 7 => g703l7
  | 8 => g703l8
  | 9 => g703l9
  | 10 => g703l10
  | _ => emptyPacking
def g703index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 3 9 4 6 2 0 (keyg703l7)
  | 8 => lookupWord 29 103 7 11 7 0 (keyg703l8)
  | 9 => lookupWord 74 262 9 12 8 0 (keyg703l9)
  | 10 => lookupWord 10 37 6 9 5 0 (keyg703l10)
  | _ => fun _ => none
def g703 : Forest := ⟨703,10,fun j => g703samples[j]?.getD (0,0),g703columns,g703autos,g703levels,g703index,noFactory,noFactorySound 703⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geomg703 : graphValid g703 (boundsBefore knownPrev_g703) = true := by
  unfold graphValid
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel, by decide +kernel⟩, ?_⟩, by decide +kernel⟩
  apply listPieces_all (d:=2)
  simp only [listPieces,IndexTree.values,List.length_append,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceDiv,List.take,List.drop]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg703_6_0 : block g703 6 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg703_6 : block g703 6 0 3=true := sg703_6_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg703_7_0 : block g703 7 0 32=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg703_7_32 : block g703 7 32 26=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg703_7_58 : block g703 7 58 28=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg703_7 : block g703 7 0 86=true := (@block_merge g703 7 0 58 28 (@block_merge g703 7 0 32 26 sg703_7_0 sg703_7_32) sg703_7_58)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg703_8_0 : block g703 8 0 20=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg703_8_20 : block g703 8 20 32=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg703_8_52 : block g703 8 52 32=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg703_8_84 : block g703 8 84 32=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg703_8_116 : block g703 8 116 32=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg703_8_148 : block g703 8 148 32=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg703_8_180 : block g703 8 180 32=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg703_8_212 : block g703 8 212 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg703_8 : block g703 8 0 218=true := (@block_merge g703 8 0 212 6 (@block_merge g703 8 0 180 32 (@block_merge g703 8 0 148 32 (@block_merge g703 8 0 116 32 (@block_merge g703 8 0 84 32 (@block_merge g703 8 0 52 32 (@block_merge g703 8 0 20 32 sg703_8_0 sg703_8_20) sg703_8_52) sg703_8_84) sg703_8_116) sg703_8_148) sg703_8_180) sg703_8_212)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg703_9_0 : block g703 9 0 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg703_9_7 : block g703 9 7 19=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg703_9 : block g703 9 0 26=true := (@block_merge g703 9 0 7 19 sg703_9_0 sg703_9_7)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg703_10_0 : block g703 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg703_10 : block g703 10 0 1=true := sg703_10_0
theorem tablesg703 : checkedTables g703 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g703 0 0 0 = true)
  · exact (rfl : block g703 1 0 0 = true)
  · exact (rfl : block g703 2 0 0 = true)
  · exact (rfl : block g703 3 0 0 = true)
  · exact (rfl : block g703 4 0 0 = true)
  · exact (rfl : block g703 5 0 0 = true)
  · exact allg703_6
  · exact allg703_7
  · exact allg703_8
  · exact allg703_9
  · exact allg703_10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low703 : Lower (vars 703) (graphGoal 703) 11 :=
  lower_forest (g:=g703) (i:=0) (hints:=536879361) (before_sound known887 valid887) geomg703 tablesg703 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps703 : List (Nat × List Nat) := [(703,[]),(863,[118,133,33,48]),(891,[118,130,81]),(957,[82,129,48])]
def known703 := extendKnown known887 11 maps703
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid703 : Known known703 := extendKnown_ok valid887 low703 (by decide +kernel)
abbrev knownPrev_g831 := known703
def keyg831l7 (i : Nat) : Nat := 0x20d00000470038a00346f1145c0b8900257a22017003
def keyg831l8 (i : Nat) : Nat := 0xf96e4d807a33bc4423d0001838c76809a1f001102d0a5a6470d9c39e26d190a2800189990618e2d7a000b0e98fcc16219000781e42a000d0a588c000000654f06384841a6a1985c00000000042e800074a110492a0536bbd13a00c03db3e4c50000000000b5b120479b21f723780147800062480000012350000001703a900003cecd99e1bba6e8484a362c81688dc4a5ec7b203d30649e39a05520e634634c4b710550fe13b2822a2c60eabf4ee121c1a000a03591e82110ab00c0c490d211027d52e086e2f41d4114e3622be8ad32fc05e4e5507cdbd358333a7311084224c6cc800049762a0003a0800124200060b880a828fdb3f1e603808000000000082505000901000007000001020200030701000405000c050e00020101030900001701021e0908021e000a3012000003
def keyg831l9 (i : Nat) : Nat := 0x180e413a4d1c3f5888a197ca7600c2fa326e60b408e643526085448648a873ebcbed34f8a7e04b0f501112f12318ecfa0e621b5b7949e81f808420790c2b049eef00858477306ca3e1e80e183cd832537d05d6a6e0acc0b8001e850000dbac2db0a280002180001d3a80012028000706283d415989b0390001d0dc4cc60702dc48f000000000002b30001e0d8001a16f82aa908001f1e00000000000506800080a0001a16000143fcaac000480750514172364825ab9a8af592d2cee37a8f7439d08d88b90c1e28b0b09bec01b40468d361f3480e09e816e21808ad8de0712335289131206dd2f003a0326048ea5409d834484a6ae40344b8787881472d822674ca6b2a6195ba106900c18a081cb8c5d08000098718e200022a8000603fe0214e800070aa5b7088002488e8205000172b8001ab0d0fa0005074e1354dc00070940005441a10920142e4ea8806000103c0000000100c0000001617feeda8c90ce78800001215a0a58bf8f982d9a9600000000000000110d273eae80019297896000000040b58bb2b78000b33f4fc00032aec3b12e502d3076ebf08a4f0726e1824106a1b5b8db4a73883fb280019385062ab8906fe2f3220010000541498d5301d43c22faa6a8a978dc109840311ac8efa9d20d72a9ee3c000000163a9a365b3589ec9880000003a2dd3ca08e88080b290f8900902b486832d06607008041208028200202000280400000000200000002a00000084a12008040208018000e00040000003058144a05000105e070100c1206030083614008000005028043a05040081210008400a090988006010000014110107c0e00
def keyg831l10 (i : Nat) : Nat := 0x4164df314b60800d8026000e9b764a20083b064755ac80006c0000008d7bd190484725326ebfc71bedb6a585b51540020014b107140008042005
def g831d6 (i : Nat) : Nat := 0x656d11bcca87942811be991213744275a52042c3224e74e408546449d694810a8c891bd790215191237af344261224ed46688482449dc04ab08bc8993d5849c0791333a4e9c00f2266d49d1801e44
def g831l6 : Packing := (11,4,3,0,0,6,0,g831d6)
def g831d7 (i : Nat) : Nat := 0x30d10000b0911a1202698201a1342030202031061b020006170203020000040620061000000000030200000000610228080000020800000030800000610034080000c2000610c2184308610061002729865c95e52906368ae1a8560a7fdfa7bdea765ce70dbe6e5ae68d9e64d8e625845fd6e5a55e5655453d4a515404ed364ad264851c45d12435023f4ec39ce2374d8334c830cbe2e4b42a4a427c9a2548a214801d4701ac6616c56144460ec300941a0540a01400bbe8858644bbc0854644dbc784c244bbe884c244bbd180c244fad6248244fad5248244fb93048244bbd6848244bbe8848244fb55144244bbd6844244bbd5844244bbc0858644bbe8844244fb53145e44fb51045e44dbd6745e44bbd6845e44bbd5845e44fb93041e44dbd1741e44bbd3841e44bbd2841e44bbd1841e44dbd2701e44bbd2801e44bbc089de44bbd3844244fba449de00bbe8811d309fe8811d30dbe8811d30dbd7891200bbe8854644bbc4858644bbc4854644bbc0850644bbd3810244bbd2810244dbc4791200dbd1791200dbd2791200dbe4441e44bbc4844244bbd1810244fb8404c244bbc484c244dbd3791200bbc4848244bf1180de00bd83851e00eb666912119f5180de00f9a448ce00eea6688a00faa4488a00ef26684600f7255846009dc3851e00fb24484600bb8484c200f3655912119ed2801d619bd4801d519dd3801d519ed2801d519ed289dd419bc484dc40f9843101309be8811d309bd489dd30fd233846009bc484dd109dd3801e449ed2801e449f51801e449bc784c244b9d3801e44bad2801e44bb51801e44bb4484c2119f5189dd20
def g831l7 : Packing := (83,3,3,0,0,10,0,g831d7)
def g831d8 (i : Nat) : Nat := 0x184681306240d831846118461184090800d0800005020485a16890c194616890c220cc1b448191a243065105a860c8d120646890321c4619014080004a0406a183405010000c08000002a28506500041080402808320181000000006100004080610000308081a04811042018ca018c81010a2214430008100820605a24308d121832b4481b0a01040100062014250800210061104020d0222840129044188006c284236142121420c1460a8c1228c1a182b055ceb2550a8d4f299528a3d46687d0aa0b3ee7b4f19d939e6ecd899d3125349c9071be2b43885d055fe3e3794f15ddbb6762eb1ceb98708de9b836b6ccd85abb5269ad21a1b3e640c6d8b30c5fabe16fada5a0b2d632c1578add592a8546a794ca8f514a013da764e299d3125849c9111d226424821019f43c076ceb1cc38e6f4dc1ae32a5dcac9542945009d92c24e4748990e1fe3e8780e61c235c640be1682944b0911181cc2d0460820c81180f001ff41e44ffa4f227fd10913fe90489ff4c244ff881227fe44803fea8c89ff58644feac708ff553847faa1c23fd10e11feac108ff550847faa0423fd4c211fe86108ff644847fa20423fd55211feac908fbe77912fe03c89ef41e44f7a2f227bd10913de90489ef0c244f7a61227bd51913deb0c89ef01e44ff467007fa44803fc8bc01fe49e00ff06f007f937803fc23c01fe51e00ff263007f941803fca8c01fe58600ff265007f942803fcb1401fe50200ff287007f611803f711401ef91200bfa2f005fd27802fe1bc017f4de00bf88f005fd47803fc88401fe48200ff061007f930803fc20401fe10e00bf88e987bc474c2fea3a61fe10130bfcee205fd17102fe938817f4dc40ff280207bd40103dea1081ef10c40bfceea05fe774c3dea0a817f9dd41bf80ea0dfc37506feaba837f59d41f7ac8a0dfe77546fe03aa37f0dd51bf88ea8dfe77586fe03ac3fe9de00bf86ea05fc47586fe8bc89ef10244f7a81227bd41912ff3ba217f0dd10bfa6e885fc47442fea3a217f55d10bface887f551442ff3ba417f0dd20bfa0f225fd470c2fe238617f45c30bfcee187ed62483f6a9241fe4c120bface905fd47483fc980617f11d20deccd08f7655847db224236f11d30f7489007da33803f511401fc84600
def g831l8 : Packing := (129,2,3,0,0,11,0,g831d8)
def g831d9 (i : Nat) : Nat := 0x5041a820d4c108a08645041a820d41088a025041bb69461b631410db1884d041ec62120af46fb2972a849a18ea581d8982a00ff587fd51ff507fd40ff103fd30ff0c3fd20ff443fe44ff803be44fd847fa00
def g831l9 : Packing := (14,1,3,0,0,9,0,g831d9)
def g831d10 (i : Nat) : Nat := 0x1441ff
def g831l10 : Packing := (1,0,3,0,0,0,0,g831d10)
def g831samples : Array (Bits × Bits) := #[(0x7f003f80fffff807f007ffffff01f80fc0fe01f80ffffff003f803fffe003fff007f003f807fc00ff803ffffffc0003c00001c18380003c000f98870707fff0781ffff8860e060fff0f00ff007f8e0e0700e03ffff9080464c1f1cf80ece621f,0x42220a400a10c0642042221900003000800410200840a180610409211100a00c00420301024200181009110c800200248000100020080248a0890050402922008110c300002000202090c1904260c040208802214c1080464812089000ca4212),(0x80003fff03f800000ff807fe00fe000fff0001fff01fc00ffc0003ffffffffffff80003fff80000ffffc03ff00000fc00071e01fc0007c003ffe0f807f83c0007e0f80707f007f0e0f000fffffff00ff800ffc0f804306187d649323350fec64,0x844508a40620a8144888422522a02856290628b211902148420924a62320d116900047a48044ca2a2500650125006c10870a01d4120341105320d82148244844a0b08506b12290a49010a258d8d00bd0112a80e00c306182544922325052c44),(0x3ffffc0007f80ffff80000fffff0000001ffffe0000ffffffc07ffffc01fffffffc00000000ffffffc000003f0000181ffe0000f80003f07f0007ffc00f87ff0007f80007ff00ffff0fff807ff00000ffff0001c18607278e3c439f39078,0x5080a3543284542a2854088924449c20082085344c8204a92a4d202485442046927491000082914d448a4005a482b02211815ea0024a82202a85d004694c28281560112a800452b082aa50ca50227a00002d53c0051c1860523841c418a29038),(0xffffc000000007fff000000000fffffffffffe000000000ffffffff80000001ffffffffffffffff000000000003c000001fe0000000fffffc007ffff800000ff8000007fffff80000fffff000007fffffff000000060007f8380fc07c1fc1f80,0x4160000000080c04281213048892249848830010008090240a080803011049824082614121404000010101801140200202400000001188380000111000000954008224452b100000c458c0080c484ca45800000086000150000bc02815c0b00),(0x7ffffffffffff000000000000000000000fffffffffffffffe0000000000000000000000000003ffffffe000000000ffffffff80000000000ffffffff80000000000ffffffffff8000000000000007fe07ffc00fff801ffe000,0x66f73a669b36e6f77ee7b7bdcee9b36d96ccf9a1eacdafcff3f6dbf7f999b6dc274eb7975b57267876df5b5ec9ff5b7fba241285248ddffbf3d945594c6b32dfe7bdfbc65ab918a92fffefffe7f4c6cb65c81a634e7fe07ffc12fffa81ffeb12),(0x7fffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000003ffffffffffffffff0000000000000000000fffffffffffffffffff00000000000000000000000007fff800000fffffe000000,0x180018204103038301c1c070f1c38e18f0c1c1830e0e0380c0e0c0c01e0700381038181c18078180e060600e1863883cb664c988e0100200000000000000e678ce3c7f7cde7ccdc80608030100080c06006084106a55000000f76ffe000000),(0,0),(0,0),(0xfffffffffffff800000000000000000000000000000000000000000000000000000000000000000000000000003fffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000007fffffffff000000000000,0x78e03c60c38604040c06060180000400200100060c10300c0307030701e03800c060c0206060380e07038380f0238c33c1499b16370e633c3ce7ee6e7e73bc0001004000000000000088008c06001010080183086015aaeaffff000000000000)]
def g831columns : IndexTree ColumnInfo := (.fork 4 (.leaf [(6,0,825,0,7),(256,0,575,0,8),(264,16,39,0,4),(256,16,47,0,5)]) (.leaf [(2,0,829,0,8),(288,0,543,0,7),(2,16,301,0,5),(288,16,15,0,4)]))
def g831autos : Array (List Nat) := #[[],[130,81],[133,33,48],[82,129,48]]
def g831levels : Nat → Packing
  | 6 => g831l6
  | 7 => g831l7
  | 8 => g831l8
  | 9 => g831l9
  | 10 => g831l10
  | _ => emptyPacking
def g831index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 4 16 4 10 4 2 (keyg831l7)
  | 8 => lookupWord 46 158 8 13 7 2 (keyg831l8)
  | 9 => lookupWord 81 289 9 14 8 2 (keyg831l9)
  | 10 => lookupWord 14 38 6 10 4 2 (keyg831l10)
  | _ => fun _ => none
def g831 : Forest := ⟨831,10,fun j => g831samples[j]?.getD (0,0),g831columns,g831autos,g831levels,g831index,noFactory,noFactorySound 831⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geomg831 : graphValid g831 (boundsBefore knownPrev_g831) = true := by
  unfold graphValid
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel, by decide +kernel⟩, ?_⟩, by decide +kernel⟩
  apply listPieces_all (d:=1)
  simp only [listPieces,IndexTree.values,List.length_append,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceDiv,List.take,List.drop]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg831_6_0 : block g831 6 0 11=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg831_6 : block g831 6 0 11=true := sg831_6_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg831_7_0 : block g831 7 0 32=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg831_7_32 : block g831 7 32 1=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg831_7_33 : block g831 7 33 32=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg831_7_65 : block g831 7 65 18=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg831_7 : block g831 7 0 83=true := (@block_merge g831 7 0 65 18 (@block_merge g831 7 0 33 32 (@block_merge g831 7 0 32 1 sg831_7_0 sg831_7_32) sg831_7_33) sg831_7_65)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg831_8_0 : block g831 8 0 8=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg831_8_8 : block g831 8 8 32=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg831_8_40 : block g831 8 40 32=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg831_8_72 : block g831 8 72 32=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg831_8_104 : block g831 8 104 16=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg831_8_120 : block g831 8 120 9=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg831_8 : block g831 8 0 129=true := (@block_merge g831 8 0 120 9 (@block_merge g831 8 0 104 16 (@block_merge g831 8 0 72 32 (@block_merge g831 8 0 40 32 (@block_merge g831 8 0 8 32 sg831_8_0 sg831_8_8) sg831_8_40) sg831_8_72) sg831_8_104) sg831_8_120)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg831_9_0 : block g831 9 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg831_9_3 : block g831 9 3 11=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg831_9 : block g831 9 0 14=true := (@block_merge g831 9 0 3 11 sg831_9_0 sg831_9_3)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg831_10_0 : block g831 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg831_10 : block g831 10 0 1=true := sg831_10_0
theorem tablesg831 : checkedTables g831 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g831 0 0 0 = true)
  · exact (rfl : block g831 1 0 0 = true)
  · exact (rfl : block g831 2 0 0 = true)
  · exact (rfl : block g831 3 0 0 = true)
  · exact (rfl : block g831 4 0 0 = true)
  · exact (rfl : block g831 5 0 0 = true)
  · exact allg831_6
  · exact allg831_7
  · exact allg831_8
  · exact allg831_9
  · exact allg831_10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low831 : Lower (vars 831) (graphGoal 831) 11 :=
  lower_forest (g:=g831) (i:=0) (hints:=12884910337) (before_sound known703 valid703) geomg831 tablesg831 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps831 : List (Nat × List Nat) := [(831,[])]
def known831 := extendKnown known703 11 maps831
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid831 : Known known831 := extendKnown_ok valid703 low831 (by decide +kernel)
def g767 : Forest := ⟨767,11,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none,noFactory,noFactorySound 767⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low767 : Lower (vars 767) (graphGoal 767) 12 :=
  lower_discard (g:=g767) (ci:=(64,0,703,0,11)) (hints:=553656577) (before_sound known831 valid831) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps767 : List (Nat × List Nat) := [(767,[]),(991,[118,133,33,48]),(1019,[118,130,81]),(1021,[82,129,48])]
def known767 := extendKnown known831 12 maps767
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid767 : Known known767 := extendKnown_ok valid831 low767 (by decide +kernel)
def g1015 : Forest := ⟨1015,11,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none,noFactory,noFactorySound 1015⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1015 : Lower (vars 1015) (graphGoal 1015) 12 :=
  lower_discard (g:=g1015) (ci:=(0,16,487,0,11)) (hints:=22028484865) (before_sound known767 valid767) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps1015 : List (Nat × List Nat) := [(1015,[]),(1022,[118,133,33,48])]
def known1015 := extendKnown known767 12 maps1015
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1015 : Known known1015 := extendKnown_ok valid767 low1015 (by decide +kernel)
abbrev knownPrev_g895 := known1015
def keyg895l9 (i : Nat) : Nat := 0xdaed2613d617b13000000311000723032e46e2b73a90e0005c0a2010304c61d13cc3f630c2e04d0002a7e87344804539c0100014e28814a2c534953850910fd2f535328a4010a0059ca73b925000a33d37000fad642c1582aeb3916621c84000bc12ab745000f4b000d3630c88cc8e000c180001c4d27e8211b00000022d61e00000000003e686d22500810041000292ec8c2cd316297bf31c8cb000548000690f0de0b5ac31a507dbcc91202147724e19706334b14c08c12a1fb4310187201c4820100000001604607220820b081428000280000a304040024100
def keyg895l10 (i : Nat) : Nat := 0x96baa7526f5ea11379f3099437c1f781910f0e0048fa439f7e7b57d23340000c5321802dc2e000b6fceedc29ec3d06183566deb1d4fd93da843f48478001c1d87da530000ca630765bf97841200053a9e2d9463a601c4dbae2689c18c0000f01ef1e8839a587824ad64f95c068ef97645a34000000000508d33e384cbd79b005f89b0000000000000000511cd2b175000236a8b00006ccdbdc00000000000033340009b08000000000868a8400000000001bc29a91e900010b00003f30004cbf23b6de771800000000082b0000000e3b00076561ca5f294baada148a252df90a5b158c6520e0b6dbade560402b4c72af206e0003c1588689ad25011c000cde1a26c225c4000000370c6dba82e0653c400005fc8fe4742c713c0002dde0000000000001683ba20000834f979756ae556a4723f6d96d438881b598da6444000c52c994a00e440000a08001ae6e613f0bd9daec479fce6b7dc0114d29f852ccbd3dd42a403ee5061ac076fa3c12c4c5acaaec82801741561db6ab4773010bf04180002df22e10d819dafc75c34e45e19a7bed92aef5c7aef8c8ad900072bc000150000597fda6729a7a5b887f28032344923ef6ad531802331ce661426c1035786493620000000f94d19d3d80b9ed0000011776d312e302884fd8d343157f740000000004ec28e2e02c1e8000cf47cd213e9b80007e84a30e61d249d685d78833ea0a8774c06df390990f191dbd54e730818878001867f49973bf73e075386daec85eb47500e218e979dbb23816427af5c65199ba51eac3da80010db06ae123b584b4c5238bf22b91085167c6ac16700003188002608714c1b7305f2d6791001165542000742432c000000000622f94f0e81660000056446237d202fc30858f779af0c444b4b8a5e19d647782ea8cb19e5afb0a8405da5d1155152f842c87f52a503e09d0632e85b002141101018000a008081a0300018240b0a034140300840260c0000418190080808000000c0802020140a000000004010e8000a01058a00401010041605038001008010481a0403004082602814020302808340001008021b03000000200044800600004460100000261100804062a0085804000380000050006c160104004281e118183405020240e02
def keyg895l11 (i : Nat) : Nat := 0xa15000061033f48bd664dc034e2000412000f11000000955316589f028b052415be2740e9605ce000b5801393c400d3fe34000d190006358cdc6300000095002b000e37000da4310000122ca9000c6435fb4100025cab5000c90a56b8e7cb745e3e00005a3201179b8000453000f99438f2800030da47000c0f000000a5dcaa000b66ea011eae45983440000a6000854000000000d3a0004d1168a40cd44a712346505e72d94c5c3a433d7a59000bab84ff911db38f000000f9c91b3c4000000739000fbc000508000000000ca1846a1fb255a8000000f36e4b00000000022a7622e574900000000b000000b06932000000fd3000a0453b000b2c4420677d26217317a3b0172f63d2d8c0550c3b744e23082ebd525751481dbc06bd51ab1c107051d5280a1186b6000729bc579712600000044a7091bb000000000d0100000208000100000a00010000010b0318011a0003001400060c000e0202000802010c02020202012c010000020100001f07
def keyg895l12 (i : Nat) : Nat := 0x6a6c001628c123f3c628802960000000000000000154900002c200002c9ce05618026a006980001e4000000180000002000000001040
def g895d8 (i : Nat) : Nat := 0x1c61f0041400800000000000140080000000000000000000000000000003c01f007c0100043e00f802010f803e00f803e0080820108103e008043e00f8020f007c01f007c01f007c01f007c01f007c01f007c01f007c01f007c01f007c01f006eeb82dbb36c8b0ebeae6b4abeaaa96a0a6e8da22839fa799d26f9aa659825b95a519324790a3d8e2338ba298921f86a15842027d1e6785d3715b76a59b6357f5c563555474e52b4750f428fc3b8e0348c42d8a82688c1f87018854118380a81c03800cef5c699121308df568899de009ee12939442009eeaa8494c2009ee129794c200b3d5a8899de11b3d5a8099de11b3d5a8309de11b6d129309de119bd5a8899de11b6e129309de009bdaa9690e2119f9aa9291e2119bdaa9690c2119edaa8494c2119ed129794c2119f9aa9291c2119dd56a995c2119fcaa9091ce119ed1293902211bbc5a83984600bf84a87984600bdc5683884600bf84a87384600bdc5687384600bbc5a87384600b5e568899de00b5e568199de00b5e568389de00a5f568899de009de568899de009deaa9590e2009deaa9590c6009fa4aa994c6009be5aa995c6009fcaa9191ce00bec1293084600be6129308ce00f749de3384600b5e568319de00a5f568395e010a3f5a8395e0108fb4aa994e1108efaa8494e1108ef129794e1108df56a995e1108bf5aa995e1108ef129894c1108bf5a8899de11a9f568195a030a3f5e8195a0308bf269715a030ccf1215906130acf56819121308ef6687112130f745c5315c1308ef129891c530adb568314a070abb4a8195a0309ed12939442118fb668734a010afa428734a010af9468734a010adb568734a010abb5a8734a010af6428794e010af5468794e010af34a8794e010a7b4a8395e010ab75a8794e010af34a8734e010ab75a8734e010add4687356010adb4a87356010a9f5a873560108bf668735a010abd468735a010a7d468395e010ad7568794e010
def g895l8 : Packing := (79,4,5,0,0,10,0,g895d8)
def g895d9 (i : Nat) : Nat := (if i<1 then 0xa8487108dfd5e408846fea7204423df5739de11efab84ef08dfd5e530847bf0713bc01df8189de00efc1ccef0077e06677803bf1133bc01fd9738ce00fec98c67005fe22633803bf4ef19c01fd9718ce00fec38c67007f61e633803fb03319c013fc898ce00ff8b8c23007fc4c611802ff11308c01dfa7784600fed19c23007fc5ce11803fe0e708c01ff07884600ff81c423007fc1e611803fe07308c01ff08984600ff93bc23007fc8ce11803fb11319c01ff110846009fe44c23007fc5c211803fe26108c01bf48984600efb3bc23005fe22573802ff532b9c017f9191ce00bfc44ae3005fea6571802ff27238c01ff1714c600bfcbca630077e0c677802ff53298c017f9790c600efcb88f1005fe4e478802ff2323c401fd9310e200bfcbc871005fe46438802ff2f20c4017f93906200efcb9cef0077e5c677802ff1133bc01df9319de00bfc44a63005fe424714c27fb1238a61df9715c130fec98ae0987f60e5704c2ff532b8261fb97012130bdf4c890986ef5c4484c3778e224261bbd7012130dde8c890986ef064484c377d3224261bf57146030bde24a30987f54c4184c3778900c261bf51806130bbeac830986ef122884c37f2e1442613fd19a21309fec48e2185fda65738475f8e2b4061afd195a030d7e0cad0186bfa65680c3778908c261bf90802171bf694810b8dbf5a6885c75fad3442e33fd09a21719ff4ca1038f7e025715c2bfd32b8ae1df5714c5709fe44a62b85ef125385c37ba701c2e16fd690e170efab8830b84ff225714c2efab3442e19fd71a2170dbeacd10b84ff4e6885c27fa33442e13fd890c470dee98a70384ffa65381c37da62940e1bec314a070df69ca50386fb465281c37ea628c0e13fd39460709ff4ca30386fd460185c33f872bc0219fe995e010d7eb9ad0086bf1cd680436fae6ac021b7c7356010deeb9a70086f71cd380427faf29c0213fe994e010deebca70086f71e5380437bd329c0219fd395e010df639a50084ff22573846dfad239c2377d591ce11bf6948e708dfd46473846ff21239c237f5794c611efab8ae108cff22570846fda52384237f5191c211fea98a6108efb5cd280435fae2b40613fe99460309fe44ae6884ff62570442f7892982213fd894c1109ff4caf08867f5e078442f78929c2213fd794e110dde24a70884ffa65384437ba701c2213fd39a21109fec48e60867f5cd780433f8e6bc0213fd79a21109ff4caf0084ff5e5180c25fad3442e3779590c600bdc24a610047fa65780425fd32b4061df27784600fe919c23005bd5a473846eeab239c237e5291ce11bbcac871005bd5a43884677d32242617e5291c2119beacd10b85fc46473802778929c2213de994e010bda24a6108df94a478846df2d239c016f5690c211bbcac8e7004fba65281c2fd25239c017f1091ce11 else (if i<2 then 0x400000000000541232510000000000008c24a1031840ca1003f00b803c01e0080092082100402c8c9a033184382cc08265041240088100680611c026004102200840e00b0041c01e0083803c0123e017006941040e3e0101f00b803c01e00801c01e00f302081cdc02070041b8040e00f007803c0108e01700447805c01e00f004238040bc02e0083803c01e00f007803c0108e017007803c01e00f007803c01e00f007803c01e00f007802464a2280f0078020280f007803c01e008183700c1020bc02e0080102060c0bc04e504170041c01080ae0184700b803c01e0081f00b9b83958c9c7c053ca4f806e3e6e540271f372c3c4701b9a27962380bc7cdc1cb8140c07e3e6e0e5c0a0603f37014f296978f80a794b0a55c7cdc0565e329e5e027314f2f0103f8f9b27943b2281055c7cdc051806e3e0e56621571f37014f2e01f8f9b94049c7cdcb0f11c06e3e6e54021571f370139b80a794b4bcdc053ca51806e3e029e52c2c571f3447014ab8f9b80aca55c7cdc053cb807ef7ef2eedee8ee3ed6ec9ebceafea2e95e88e83e76e69e64e57e4ae3de38e23e16e09dfcdf7df2dedde8ddbdcedc1dbcda7d9ad8dd80d7bd76d71d6cd67d5ad55d50d4bd3ed39d34d2fd2ad25d20d1bd0ed09d04cf7ceace5ce0cdbcd6cd1ccccbfcb2cadca0c93c8ec81c74c67c5ac55c50c4bc46c29c1cc17c12c0dc08c03bfebf1becbdfbd2bcdbc8bc3bbebb9bb4bafbaaba5b98b83b7eb79b74b6fb6ab65b60b5bb56b49b3cb37b2ab25b18b13afeaf1ae4ad7ad2acdab8a83a76a69a54a3fa2aa0d9f89e39de9c99c49b79aa9a599898b98697996c95794a93593091b9068f98ec8df8da8d58c88bb8a68a188c88787a86586085384683982c81780a7f57e87db7ce7b97a479779278577876b75e75174472f7227157086fb6ee6e16d46c76ba6ad6a069368667966465764a63d63862b61e6116045f75da5cd5b85ab5a659957455f55254d54052350e5014f44e74d24ad47845341e3f13b437734a31d2f02cb2a626122c2071ca1a517014b1260f90c409706a03d000efa984ef08f7d0c277847be8733bc23df4099de11efa44cef08cff22573802dfad239c0177d591ce00bf6948e7005fd46473802ff21239c013fc895c600bfc848e3005ef12530846efab218c017f9090c600efcb8ae1007f64c530802ff2f298401fb8494c200bfcbca21005fe4e510803bf2e13bc013fc899de00efc984ef0077e442778033f9133bc01fd9308ce009fe44a63004ff22530846dfad2184237f5190c211bfabca2108dfd4e510847beae33bc233fc899de11bfa44ae708dfd42473846fe912b84237f6995c211bfa9c8e108ffc5c130846fe9133bc23fb4494c211bfa44a6108dfda6530846feaf218423df5701e211bfa9c8f108dfd42478847faa601c4237f5790e211bf else 0x7007803c01e00f007803c0100707802008084049820232611285983c0100000e00f00780202326112858c3c0100000015040001004000000001304006609304000000065090040c6160081803c01630b2840000181209c6c01000000018020e00b30))
def g895l9 : Packing := (252,3,5,0,0,12,0,g895d9)
def g895d10 (i : Nat) : Nat := (if i<1 then 0x13308c03cc20560263469b0123074623015288c0311805192e01e30f8068f0083e0126122b0112e0108c02102700f187158091d4aa501f1e6c19602a42a529c463cd832c052852a83e3cd832c04c852a9388c79b06580a0f8f360caa0c1f1e6c195498463cd832a7307c79b0655460f8f360539541d4a714231e6c1960255290e231e6c196024463cd832a9308c79b065546118f360539539e4c755231e6c1950253a954231e6c19602442ac79b0654e74ea9488c79b065809118f360539551e5494f231e6c1950254aa4e231e6c19602552712231e6c1960263871328508c79b2e0509158f360ca1ce1c463cd8329a408121e50ac79b2e0507158f360ca20e24563cd83288389158f360ca69125063cd9421c548101e489c79b2e050ac79b009ca20e271e6c194a2b1e6c194a284c8111c3e3cd970284e3cd8328710790a93a9118f360cb0142b1e6c1943883a854a43e3cd832c0487c79b029caa8ea55280f8f360cb012a540a0f8f360cb012a94090f8f360cb0121d563cd832a838754a5463cd832c04a7918f365c080ea6463cd970203aa918f365c080e2b1e6c020899063cd272c8363cd804122e6c0272882e3cd83287106c783287265cd83288285c79b0650e20caa3e3cd970203c65e2ed16a8a4c4a220f0ed869c2ca14d093843c1b609903280fc015fc8fca7d4be59ef8f627a7bcb9e28efa7703afdd58e9273c395dc7ae1c6fdb74db72da66c635c9abed4c695b461a0aceb66531fd868bf05d2add968eb18574aacd4dea2b4fe273532e953487a36512a85f40d9f5cf267483891b8cd3066231617f4b8e57c2a314789ec4ab23a90a87e83b01bd0cd85e42ae13c08d03fc1c80c9058c26810c07202d411a06501b0003ff1c430ffe11803ff5cd10ffd71443ff4c510ffd70443ff4c110ffd78443ff8ce00ffc78443ff4e110ffc38443ffa2110ffe77803ff5c430ffc73043ff0c600ffd31803ff1c600ffd71803ff5ce11ffc73847ff1ce00ffd73803ff5c211ffc70847ff4c211ffc30847ff9de11ffd73043ff4e170ffc385c3ff46170ffc185c3ffa2170ffd085c7ff5c570ffd311c3ff0c470ffd315c3ff02171ffd714c3ff1c530ffd704c3ff46130ffc184c3ffa2130ffe885c7fd9de11ffa33803fd4c211ffa77803fd02211ff438847fe06200ff478847fd0c211ff970803fe44200ff838803fe1e200ff8318037f9de00ff931803fe1c600ff971803fe1ce00ff611803fe5ce00ff930802ffa2171bfd081c77f5c570bfe885c2ff4e070bfd181c3fe5c130fbc484c2ffa2130bfd180c2ff5e110bfd38442ffa2110bfd78043fe84600bfd38043fd5c211ff473847fd5ce11ff571847fd4c611ff470847fd44211ff211803f68ce00dfa77802fb4a070bbc484c2fb4a010afd680c2f74e010b7d58042bf5a0109fd780437d9de11 else 0x2300a4271180980229188c04129446020a4c1f010487c03469b00e429118098029700b004407c0390a84602231180623008407c0312944602080f80629188c040f8041c56018815806230085260f8081c4601890f8061c4601c7541f0104601664d807985601e6469b0)
def g895l10 : Packing := (105,2,5,0,0,13,0,g895d10)
def g895d11 (i : Nat) : Nat := 0x2482a39a09474151cd04a39891ca8e682521054734129062878e68099484473404ca418a2639a09472111cd04a39062891c88e68254144903c73412a078e696000c44734b00067fdd66857850d1a394bc21c520a400ffae3ff1c7feb87fc70ffa61ff0c3fe887fc10ffc23ff803fb08ffa00
def g895l11 : Packing := (12,1,5,0,0,10,0,g895d11)
def g895d12 (i : Nat) : Nat := 0x3300a4ff
def g895l12 : Packing := (1,0,5,0,0,0,0,g895d12)
def g895samples : Array (Bits × Bits) := #[(0xfffff0000800001f800207810f0000007800001c0c1c0000f8000f98870707fff00ff007001fc0f800007c007043c060ff80fe03f01fffff8830700c0fffc3f003ff003fe381c0f003807fffff058c01080464c1f0d984e4a2331cf80ece621f,0x6430000000091016908205000a0008004900001000100200a90a089005040292200190010004002182086420604148402a00640110144343000010000100839032390219830080a02200510a98058c010804648120910064a222089000ca4212),(0xf8000000700001e000043801f000001f800071e00fe0001f0003ffe0f807f83c0ff0007803e0ff0007ffffff807c007f03ff00000fe03e00703f800ff0703c0003fffffffc01ff0003ff807c00001024306187d643260b07f84c9323350fec64,0x80809000500000a0200410019020400d820870a00ea0880d02105320d821482440b000180020450000a08a0d000c000100c6004084a02c08503582449051240041424c6634017a0044a500700100102430618254420402021008922325052c44),(0xf8001fe0000183ffe00000fe0000181fff00003e00003f07f0007ffc000000f8003ff0007f81f8000ff80007ffc0001fc0fffc0007fc0000fff803ffffc1fffc01ffe000003ffff800051e0c1c18607278c384c78c470e3c439f39078,0x2d15220d8101761241182fda00440b604411815ed00112a08402a85d004694c28404858042d71042a81b2040ba80027acc082894095d80112d40008b2d820aaa941cb28089f400000b5a7e000a51e0c1c186052388384c50c47041c418a29038),(0x30003e0000001fc0000001f0000001fe00000003fffffc007ffff8000000000ffffc000007ffe00000ffffff80000001fff00000007ffffff000003fffffe000001ffffffffc000000008600060007f8380fc0707f0780fc07c1fc1f80,0xc0204420001a0004020280000000d00400202400000000463078000011100000088908552800000516c04084446a69000000414ba400202242295a200000314563800403120994c560000000108600060001500007c0202f0300bc02815c0b00),(0xfc0003fffffffe000000001fffffffe0000000003ffffffff80000000000ffff00000000007ffffffff00000000000001ffffffffff8000000000003fffffffffffe00000000000000000e7ff07fe07ffc00fff807ff800fff801ffe000,0xf63a7ee4023fbb7ff7a285488a89fdb6ff7a241242922377ff7f3d945594c6b32dddfc55aa1424a7dffdffee666b6d486a1275effe7ef7fbc32d5b218544bffffbffff3fd30d96e57203531a9ce7ff07fe07ffc12fffa07ffb22fffa81ffeb12),(0xfffffc00000000000000001fffffffffffffffffc0000000000000000000ffffffffffffff80000000000000000000001ffffffffffffffffffffffc00000000000000000000000000000f80007fff800000fffff800000fffffe000000,0x438776bb502000040000100010e1c7107cb664e4c4780400200000000000000eee2efecf79f6ce0490010808003010802481f2cf8b38bc7fbe6fcfce6f20018100180400101801800c042020f80006a55000000f6eff800000f76ffe000000),(0xffffffffffffffffffffffe0000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffe0000000000000000000000000000000000000000000000000000fffff8000000000fffffffffff000000000000,0x7c07b72b9c3c4707cac99c231c8100004000008000400020400000000000000f0fcf67f39eb8f7e71e71f0ff73be7cf338f983080c00c004000c0208080186020820080020008600101800c0ff4a90000000000dfbfdfdeff7000000000000),(0,0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000fffffffffffffff00000000000000000000000,0x78008084421c19878153661cce10e186781499b0b1b8398c783ce7ee6e7e73bc0000000000000000000020000000000004000000010010000000000000002080010c03000402008006060430000b5695aaeaffff00000000000000000000000)]
def g895columns : IndexTree ColumnInfo := (.fork 10 (.fork 5 (.fork 2 (.leaf [(0,16,367,0,11),(16,0,358,9,7)]) (.leaf [(25,0,358,0,5),(64,0,831,0,11),(0,17,332,34,6)])) (.fork 2 (.leaf [(4,0,891,0,11),(32,0,863,0,11)]) (.leaf [(2,0,893,0,9),(1,0,894,0,9),(8,0,887,0,9)]))) (.fork 5 (.fork 2 (.leaf [(256,0,639,0,9),(12,0,883,0,8)]) (.leaf [(288,0,607,0,8),(320,0,575,0,8),(2,17,332,32,5)])) (.fork 3 (.leaf [(256,24,99,4,5),(0,24,99,260,6),(5,0,890,0,7)]) (.leaf [(6,0,889,0,8),(33,0,862,0,8),(66,0,829,0,8)]))))
def g895autos : Array (List Nat) := #[[],[82,129,48]]
def g895levels : Nat → Packing
  | 8 => g895l8
  | 9 => g895l9
  | 10 => g895l10
  | 11 => g895l11
  | 12 => g895l12
  | _ => emptyPacking
def g895index : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 36 125 7 12 7 1 (keyg895l9)
  | 10 => lookupWord 121 419 9 13 8 1 (keyg895l10)
  | 11 => lookupWord 53 213 8 12 7 1 (keyg895l11)
  | 12 => lookupWord 9 46 6 9 4 1 (keyg895l12)
  | _ => fun _ => none
def g895 : Forest := ⟨895,12,fun j => g895samples[j]?.getD (0,0),g895columns,g895autos,g895levels,g895index,noFactory,noFactorySound 895⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geomg895 : graphValid g895 (boundsBefore knownPrev_g895) = true := by
  unfold graphValid
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel, by decide +kernel⟩, ?_⟩, by decide +kernel⟩
  apply listPieces_all (d:=3)
  simp only [listPieces,IndexTree.values,List.length_append,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceDiv,List.take,List.drop]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg895_8_0 : block g895 8 0 32=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg895_8_32 : block g895 8 32 32=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg895_8_64 : block g895 8 64 14=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg895_8_78 : block g895 8 78 1=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg895_8 : block g895 8 0 79=true := (@block_merge g895 8 0 78 1 (@block_merge g895 8 0 64 14 (@block_merge g895 8 0 32 32 sg895_8_0 sg895_8_32) sg895_8_64) sg895_8_78)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg895_9_0 : block g895 9 0 26=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg895_9_26 : block g895 9 26 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg895_9_58 : block g895 9 58 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg895_9_90 : block g895 9 90 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg895_9_122 : block g895 9 122 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg895_9_154 : block g895 9 154 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg895_9_186 : block g895 9 186 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg895_9_218 : block g895 9 218 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg895_9_250 : block g895 9 250 2=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg895_9 : block g895 9 0 252=true := (@block_merge g895 9 0 250 2 (@block_merge g895 9 0 218 32 (@block_merge g895 9 0 186 32 (@block_merge g895 9 0 154 32 (@block_merge g895 9 0 122 32 (@block_merge g895 9 0 90 32 (@block_merge g895 9 0 58 32 (@block_merge g895 9 0 26 32 sg895_9_0 sg895_9_26) sg895_9_58) sg895_9_90) sg895_9_122) sg895_9_154) sg895_9_186) sg895_9_218) sg895_9_250)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg895_10_0 : block g895 10 0 12=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg895_10_12 : block g895 10 12 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg895_10_44 : block g895 10 44 13=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg895_10_57 : block g895 10 57 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg895_10_89 : block g895 10 89 16=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg895_10 : block g895 10 0 105=true := (@block_merge g895 10 0 89 16 (@block_merge g895 10 0 57 32 (@block_merge g895 10 0 44 13 (@block_merge g895 10 0 12 32 sg895_10_0 sg895_10_12) sg895_10_44) sg895_10_57) sg895_10_89)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg895_11_0 : block g895 11 0 2=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg895_11_2 : block g895 11 2 10=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg895_11 : block g895 11 0 12=true := (@block_merge g895 11 0 2 10 sg895_11_0 sg895_11_2)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg895_12_0 : block g895 12 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg895_12 : block g895 12 0 1=true := sg895_12_0
theorem tablesg895 : checkedTables g895 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g895 0 0 0 = true)
  · exact (rfl : block g895 1 0 0 = true)
  · exact (rfl : block g895 2 0 0 = true)
  · exact (rfl : block g895 3 0 0 = true)
  · exact (rfl : block g895 4 0 0 = true)
  · exact (rfl : block g895 5 0 0 = true)
  · exact (rfl : block g895 6 0 0 = true)
  · exact (rfl : block g895 7 0 0 = true)
  · exact allg895_8
  · exact allg895_9
  · exact allg895_10
  · exact allg895_11
  · exact allg895_12
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low895 : Lower (vars 895) (graphGoal 895) 13 :=
  lower_forest (g:=g895) (i:=0) (hints:=12901687553) (before_sound known1015 valid1015) geomg895 tablesg895 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps895 : List (Nat × List Nat) := [(895,[]),(959,[118,130,81])]
def known895 := extendKnown known1015 13 maps895
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid895 : Known known895 := extendKnown_ok valid1015 low895 (by decide +kernel)

theorem two_count {α : Type} (p : α → Bool) : ∀ (l : List α) (i j : Fin l.length), i ≠ j →
    p (l.get i) = true → p (l.get j) = true → 2 ≤ l.countP p := by
  intro l
  induction l with
  | nil => intro i; exact i.elim0
  | cons a l ih =>
    intro i j hne hi hj
    have pos : ∀ k : Fin l.length, p (l.get k) = true → 1 ≤ l.countP p := fun k hk =>
      List.countP_pos_iff.2 ⟨l.get k, List.get_mem l k, hk⟩
    rw [List.countP_cons]
    refine Fin.cases (motive := fun i => i ≠ j → p ((a :: l).get i) = true → _) ?_ ?_ i hne hi
    · intro hne hi
      refine Fin.cases (motive := fun j => (0 : Fin (l.length + 1)) ≠ j → p ((a :: l).get j) = true → _) ?_ ?_ j hne hj
      · intro h; exact absurd rfl h
      · intro k _ hk
        have := pos k hk
        have ha : p a = true := hi
        simp only [ha, ite_true]; omega
    · intro m hne hm
      refine Fin.cases (motive := fun j => m.succ ≠ j → p ((a :: l).get j) = true → _) ?_ ?_ j hne hj
      · intro _ ha
        have := pos m hm
        have ha : p a = true := ha
        simp only [ha, ite_true]; omega
      · intro k hne hk
        have := ih m k (fun e => hne (congrArg Fin.succ e)) hm hk
        omega


def primary3853 (i : Nat) := inputs.getD i zero
def plus3853 := primary3853 0
def minus3853 := neg plus3853
def bank3853 (b : Fin 9) : List Sig :=
  List.ofFn (fun i : Fin 9 => if i=4 then zero else primary3853 i.val) ++
    [minus3853, if b=4 then zero else primary3853 b.val]
def row3853 (r : Row) (i : Fin 9) := if i=4 then false else sample r i
def flip3853 : Move := (~~~(primary3853 4), primary3853 4, Fin.ofNat 512 16)
def perm3853 : List Move := flip3853 :: [83,114,99,33,16,64].map swapRows
def all3853 := vars 495 ++ [minus3853]
def minusBank3853 := vars 494 ++ [minus3853]

theorem lower3853 (m L : Nat) (hv : boundsBefore known895 m = L) :
    Lower (vars m) (graphGoal m) L := by
  rw [← hv]; exact before_sound known895 valid895 _
theorem plain3853 : Slice (vars 495) (graphGoal 495) one 13 :=
  slice_correct (ms:=[]) (base:=vars 495) (G:=graphGoal 495) (by decide +kernel)
    (by rfl) (by unfold proper; decide +kernel) (lower3853 495 13 (by decide +kernel))
theorem flipped3853 : Slice minusBank3853 (graphGoal 495) one 13 :=
  slice_correct (ms:=perm3853) (base:=vars 895) (G:=graphGoal 895) (by decide +kernel)
    (by decide +kernel) (by unfold proper; decide +kernel) (lower3853 895 13 (by decide +kernel))
theorem doubled3853 : Slice all3853 (graphGoal 495) (subcube 1 0) 11 :=
  slice_correct (ms:=fixRows 1 0) (base:=vars 494) (G:=graphGoal 494) (by decide +kernel)
    (by decide +kernel) (by unfold proper; decide +kernel) (lower3853 494 11 (by decide +kernel))

theorem useSlice3853 {T bank d L k t S} (run : Live T k t S)
    (sl : Slice bank T d L)
    (av : ∀ w ∈ S, availableB d bank w = true)
    (lt : k < L + S.toList.countP (isMaskedConstant d)) : False := by
  have cut : poolCut d L k 0 bank S.toList = true := by
    simp only [poolCut,Nat.add_zero,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true]
    exact ⟨lt,fun w hw => av w (by simpa using hw)⟩
  have h := poolCut_sound sl [] (by rfl) S.nodup_toList cut k t (Nat.le_refl k)
  exact h (by simpa using run)

theorem eliminate3853 (b : Fin 9) {k t S} (run : Live (graphGoal 495) k t S)
    (hk : k ≤ 12) (sub : ∀ w ∈ S, w ∈ bank3853 b) : False := by
  have pkg : ∀ b : Fin 9, (bank3853 b).all (fun w =>
      (availableB (subcube 1 0) all3853 w) &&
      (decide (w = minus3853) || availableB one (vars 495) w) &&
      (decide (w = plus3853) || availableB one minusBank3853 w)) = true := by decide +kernel
  have prop (w) (hw : w ∈ S) := List.all_eq_true.mp (pkg b) w (sub w hw)
  simp only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at prop
  by_cases hn : minus3853 ∈ S
  · by_cases hp : plus3853 ∈ S
    · apply useSlice3853 run doubled3853 (fun w hw => (prop w hw).1.1)
      obtain ⟨i,hi⟩ := List.mem_iff_get.mp (by simpa using hp : plus3853 ∈ S.toList)
      obtain ⟨j,hj⟩ := List.mem_iff_get.mp (by simpa using hn : minus3853 ∈ S.toList)
      have neq : plus3853 ≠ minus3853 := by decide +kernel
      have ne : i ≠ j := by intro e; apply neq; exact hi.symm.trans ((congrArg S.toList.get e).trans hj)
      have ci : isMaskedConstant (subcube 1 0) (S.toList.get i) = true := by rw [hi]; decide +kernel
      have cj : isMaskedConstant (subcube 1 0) (S.toList.get j) = true := by rw [hj]; decide +kernel
      have count := two_count _ _ i j ne ci cj
      omega
    · exact useSlice3853 run flipped3853
        (fun w hw => (prop w hw).2.resolve_left (fun e => hp (e ▸ hw))) (by omega)
  · exact useSlice3853 run plain3853
      (fun w hw => (prop w hw).1.2.resolve_left (fun e => hn (e ▸ hw))) (by omega)

def p191xr6 (i : Nat) : Nat := 0xe020701000000000000c020d282edaaf528ce972202e65a21956154633b9c68065585518cf07c972156158233e635d163608438039997458d8010e0087d6849760e228029e4a2619714c600a3d698825c5318029f1a0209714c60087d68497a2121802f81a210d414c600
def l191xr6 : Packing := (11,5,6,63,0,7,1,p191xr6)
def p191xr7 (i : Nat) : Nat := (if i < 1 then 0x4844c2009dc4c48898401b988458d30802db32c19261005d6654324c200bccca064984017d1910c9308037310898a61006ec212114c20097d4cb0c18401a7986954308035e30d08861006ec9108148200de91990290401be222205208027e13108a41004eea658404200d9cc2c88084013da9960c108036b4aac1821006e69118304200d6cc346608401b59858cc108037330919821004faa658204200dd52230408401bca33608108036e30a98821006ec6113104200df0c1262084013799520974802f332643489005e664c81912009bcca904b9c013b994209738027e532c08e7006dc955811ce009f8c890eb1c013b994209638027e322412c7004ee6508254e009f94cb0229c012fa99618438026f532c28870065e61e5510e00d3cc34aa21c01ab986550438036b30ab1887004faa658210e00db52ab0421c01ba97460843803752a8c1087006f258d8210e009f94cb0221c01b725560443802f332843c67005f4644768ce00bccca10b19c015d99719633802f332832c67005f2648658ce00be8c88cb19c01e9a6691233803e34ab22467005e6650818ce009dcca10f19c01b5a5520d728027b13119ae5006b621a335ca009dd4cb0839401b3985610728036730b220e5006d6616331ca00dccc2466394013d993a214280277130ba285006b69988350a00dad2a906a1401b997420d42803732a841a85004f62623350a009bd4cb0a21401a7a66614428036730aa1085004bea65860ca00c7cc3ccc1940137a99614328034f4ccc28650065e61e550ca00d3cc34aa19401aba6661032803674aac2065006b6619320ca009f94cb0219401af266604328036e4aac0865006f44c9810ca00bf0c890f114017e1911ce22802fc32229c450057a65c4388a00bb4ca887114017e19110e22803d94cd19c45007d29563388a00fc522467114013f19121e22802f9126b9445005ea6507288a00be449a85114017699510a22802bd32e19445005ba6583288a00bb4ca865114017a9940ca22802fc32219445004ee650825c6008fc4bb0aa0c017a99210d418026f32a41283005e624d42506009f44930c98c017c99210d318025f32c41263004de654824c6009dcca10498c01f90435053180277532c20430066e61e4408600d9cc2c8810c013da9960c218036b4aac1843006e69118308600cecc3c6610c01ad9868cc218036b30b19843006e66123308600cf4c3c4410c01ba984888218037930711043006f460d7108600d78c328210c01bd183504218037a30690843007cc9564484600af8cb88708c016f19610e11802ee32a21c23005f86484384600f693346708c01f52558ce11803f248919c23005f424d7284600bd8ca0e508c017d09350a11802ee32a214230057c65c3284600b78cb06508c01771950ca11802f632819423007f08ce2284600 else (if i < 2 then 0x146f46d46b46a869c69068467866c66065464863c6306246045f85ec5e05d45b45a859c5905705505445385184f84ec4e04d44c84bc4b04a449848c48047446845c45044443842c4204144083fc3f03e43d83cc3c03a039438837c37036435834c3403343142f42d42b42942742542342141f41d41c81bc1b01a419818c18017416815c1501441381180f80d80cc0c00b40a809c09008407806c06005404803c03002401800c0019f491600728ce3fb2243ac519c7f6408758a3397ecb510a94671fd9121d528ce3fb2043aa519c7f6408758633b76c90cab0c676f990195618ceedb2432aa319dde6406554633b3e4b2a4a8c675f497585518cfce8cab0aa319c7f6408748633d7ac32a210c67bd583544218cf7e2a2c004319c7f661211c233cf6c12423846737d95a21608ce3fb2243ac119d9f6546258233b6ec98c4b04676f591189608ce9f92eb0ac119e9f2156158233d3ec32a428467b3d84548508cf6eaa4c08a119cfd64688482338fec890e904679f487205208cebf3223824119f7c2047048233ef4908e0904671fd981c9108cebf3203922119edd6156104233ddac22c208467be582584108cebeb223b0e90047f6488758e008fec890eb1c013f59121d638027eb22412c7004fe6408258e00eceba2c621c01bcd636084380337ae8c1087006f658d8010e00cfa48b0039401b3d85610728023f92ec32650067721d634ca008fec890f114019f59121e228023f92ec1c450047f25d8088a008fe4c444b8c015f59188971802afb2a392830047f25d864c6009f64930c98c012fd96209318027f320412630067d619714c600cfa412e298c01dd5325c5318033e90ea8a630047f25e8848600cfac1ae210c0157d951c94080373908b1a61004fd64688482008fecc0e4884015bd941c910802beb22392210057e6407244200b4eca0cab1c676cd92195638cedb32032ac719cd76548258e339ceca104b1c673d591209638ce7b320412c719ce76508254e3396ecb100a9c671bd9421d518ce79924c326319cb7658824c6339aeca90498c6739d94209318ce7b3204126319cb7658804c633d2e42ac6b0467b55854c4108cf72b089882119ef160931042338fac890eb1c019ad7460843803372e8c008700567650878ce008deca10f19c011be996107280327b0b220e500657616331ca00ccec24663940199d7420d428023eb2243c450067560d7108600cf8b8b0010c015b5941ca118025f532c3081004dea658510200d3d3330a20401a7986954408035b4ccc1881006d695583102009f54cb0420401aea66608408036d4aac1081006ae6194210200d9cc2a8420401b9983508408027e532c0881006bc9998110200db92ab0220401bb142604408035e30d08881006dc6161110200de8c1c2220401be18284440803574cc42261006ce95 else 0x20800002080208390839093780c44de031602083808390802080000000008000be08be08be0c100be08be08be08000000000000820e020e020e02000008006378280618103370c8a0b370800000000410410000f034de0b160b0c00f4220c220820400014d82000000008020e0a0e0a0e0a08060806080608060806080008120e020e020e020e020e0208000d0a0a000a000a000812281d148a0745228202000c000c000c000b01228405000802400500020000000000000200089e089e0800002782000000000040a089e0906089e089e0d020800000000000000000000000000008002800280030002001000300020000f02018201820182000000020a080a08003000c0a080a080000000000000000048a080000000608000003024002000c0030282000000000000000000000000000000000000001f302000000000000040008180e030e020e020e020e030e020e020e020c0308000000000000000000140020082008200000000000000000000000000175174572571970d6ed6cd6ad68d6596256055e55c55a559958d58157555554953d51d4fd4dd4d14c54a548546545944d44143542941d4113f13d13b139138536535934d3052f92ed2cd2ad28d28127526925d25124523922d2212152091e91b519518916914912911d1111050f90d90cd0c10b5095075055035014ff4fd4fb4f94f74f54f34f14ef4ed4eb4e94e74e54e34e14df4de8db4d80d60d54d34d14cf4cd4ca0c94c74c40c20c14c08bfcbf0be4bd8bccbc0bb4b94b74b54b48b3cb30b10b04af8aecae0ad4ac8abca9ca7ca5ca3ca1c9fc9f09e49d89cc9c09b49a899c99098497896c96095494893c9309249188f88d88b889888c8808608408348288087e87c87a879c79078477876c74c72c7207))
def l191xr7 : Packing := (295,4,6,63,0,12,1,p191xr7)
def p191xi7 (i : Nat) : Nat := 0x66540001b14169ea00c201ac25d3ae0c
def p191xr8 (i : Nat) : Nat := (if i < 3 then (if i < 1 then 0x9831ca00fda331ca00df9721ca00bf9811ca00bfa8850a00bf88750a00efa6650a00bf98550a00f7a5550a00fb97450a00fb96450a00fb95450a00fba4450a00fd88350a00fb94350a00fda3350a00fe87250a00bf98610a00efa6610a00bf98510a00f7a5510a00fb94210a00bf98110a00bfa884ca00bf8874ca00bf9864ca00efa664ca00bf9854ca00f7a554ca00bf9844ca00fba444ca00fd9634ca00fda334ca00fe9424ca00bf9860ca00efa660ca00bf9850ca00f7a550ca00fd9320ca00bf9810ca00fe98788a00fe88788a00fe98388a00fe88388a00fe97388a00fe87388a00fe96388a00fe86388a00fe95388a00fe85388a00fe94388a00fe84388a00fea3388a00bf88788a00bf98488a00fba4488a00bf98388a00fda3388a00fe97288a00fe87288a00fe94288a00fe84288a00fe93288a00fe83288a00bf98188a00fba445c600fda335c600bf8825c600fea225c600bf9841c600fba441c600bf9831c600fda331c600bf9821c600fea221c600bfa8850600bf88750600efa6650600bf98550600f7a5550600fb87450600fba4450600fb84350600fda3350600bf88250600fb94250600ff07150600bf98610600efa6610600bf98510600f7a5510600bf98210600bfa884c600bf8874c600bf9864c600efa664c600bf9854c600f7a554c600bf9844c600fba444c600fd8734c600fd8434c600fda334c600bf8824c600fd9324c600fea224c600ff1714c600ff1514c600ff1414c600bf9860c600efa660c600bf9850c600f7a550c600bf9820c600fea220c600bfa8848600bf88748600bf98448600fba4448600bf98348600fda3348600fe87248600fea2248600ff13148600bf98408600fba4408600bf98308600fda3308600fea2208600ff17108600ff14108600ff12108600ff08784600ff08484600ff17484600ff07484600ff15484600ff05484600ff24484600ff08384600ff17384600ff07384600ff16384600ff06384600ff15384600ff05384600ff14384600ff04384600ff23384600ff08284600ff17284600ff07284600ff14284600ff04284600ff13284600ff03284600ff22284600bf88784600fba4484600fda3384600bf88284600fea2284600ff17184600ff14184600ff13184600ff121846009bd841ca00af98610200b798510200bd98310200be98210200bf18110200bb8844c200af9860c200bf08148200bb98404200bd98304200be98204200f3a5591200bf1811ce00bf18114e009f98710e00af98610e00b798510e00be98210e00bf18110e00eda668ce00f5a558ce00f9a448ce00bd8835ca00bb9841ca00bd88350a00b798510a009f9870ca00af9860ca00b79850ca00bb9840ca00bf1810ca00fca3388a009f98708600bb98408600bd98308600fb24484600fd23384600fe22284600 else (if i < 2 then 0x1ca00bbd841ca00bf9801ca009fc8750a00dbd7450a00bdc8350a00dec7250a00b7d8510a00bf98010a009fc874ca00afd860ca00b7d850ca00bbd840ca00bf5810ca00bf9800ca009fc8788a00dbe445c600dde335c600bf9801c6009fc8750600bf980106009fc874c600df5714c600bf9800c6009fc8748600dec7248600bbd8408600bdd8308600df57108600bf98008600df48784600df57484600fb64484600df57384600fd63384600df57284600df47284600ff080846009fc8784600df57184600efa6650200bf98550200f7a5550200fb95450200fba4450200df97350200fda3350200bf88250200fb94150200ff21150200bf98610200efa6610200bf98510200f7a5510200bf98210200fb94210200bf98110200ff21110200bf9864c200efa664c200bf9854c200f7a554c200bf9844c200fb8844c200df9744c200fba444c200fd9634c200fd9534c200fd9434c200fda334c200bf8824c200df9724c200fd8324c200fd9314c200ff2114c200bbc844c200bf9860c200efa660c200bf9850c200f7a550c200bf9820c200bf9810c200ff2110c200bf88748200bf98448200fba4448200bf98348200df97348200fda3348200fe94248200fea2248200ff08148200df97148200fe92148200ff21148200bf48148200bf98408200fba4408200bf98308200fda3308200fea2208200bf98108200ff21108200bf98444200fba4444200bf98344200fda3344200bf98244200bf88244200df97244200ff14144200ff21144200bf98404200fba4404200bf98304200fda3304200bf98204200ff13104200bf8825d200bf9861d200bf9851d200bf9821d200bf9811d200bfa8855200bf88755200fb87455200bf88255200bf98215200bf98115200fb88791200fb88691200fb88591200fb97591200fb87591200fb88291200fb88191200bf88791200f7a5591200fb97491200fb95491200bf88291200f7a555ce00fba445ce00bf8825ce00bf9861ce00bf9851ce00f7a551ce00bf9821ce00bf9811ce00bfa8858e00bf88758e00fba4458e00fd87358e00bf88258e00bf98218e00bf98118e00bfa8854e00bf88754e00f7a5554e00f795454e00fba4454e00fd87354e00fd96354e00bf88254e00bf98214e00bf98114e00bf98650e00bf98550e00f7a5550e00bf98610e00bf98510e00f7a5510e00fb97410e00fb95410e00fd96310e00bf98210e00bf98110e00fd8878ce00fd8868ce00fd9768ce00fd8768ce00fd8858ce00fd9758ce00fd8758ce00fd9658ce00fd8658ce00fda558ce00fd9748ce00fd9648ce00fd9548ce00fd8828ce00fd8818ce00bf8878ce00efa668ce00f7a558ce00fd9738ce00fd9638ce00fd9538ce00bf8828ce00fba445ca00fda335ca00bfa881ca00bf9841ca00fb9841ca00fba441ca00bf else 0xca00fdd634ca00dfd724ca00bfd860ca00bfd810ca00bfd8388a00bfd8088a00dfd635c600dfd325c600dfe225c600bfd831c600bfd821c600dfc7250600bfd8610600bfd8210600bfe884c600bfc874c600bfd864c600dfd764c600dfd754c600dfd744c600fdc734c600bfc824c600dfd724c600fdd324c600dfd714c600ff5514c600bfd860c600bfd820c600bfe8848600dfd8748600bfc8748600dfd7448600bfd8348600dfd7348600dfd7248600fec7248600dfd7148600ff53148600bfd8308600bfc8284600dfc7250200bfd864c200fdd634c200fdd314c200bfe8848200bfd8348200ff48148200fed2148200ff93048200bfd8344200bfd8244200dfc7244200ff920442009fc8799a33bbd8419633bdd8319633bed8219633bf58119633bf98019633e7e66956339fc8795633bde8858e33ede6658e33edc6558e33f5e5558e33bdc8258e33bdc8058e33bde8854e33bdd8654e33ede6654e33f5e5554e33bdc8254e33bdc8054e339fd861ca33cfe661ca339fd851ca33d7e551ca339fd811ca339fd801ca339fc8758a33edd6358a33b7d8518a33bbd8418a33bdd8318a33bf58118a33bf98018a339fc8754a33afc8654a33f5d5354a33bbd8414a33bdd8314a33bdd864ca33ede664ca33bdd854ca33f5e554ca33bdc804ca339fc8758633bdd83186339fc8754633bdd8314633bde884c633bdd864c633ede664c633bdd854c633f5e554c633bdc824c633fd5514c633bdc804c6339fc8748633bdd8348633fd53148633afd8608633b7d8508633bbd8408633bdd8308633bf98008633df48784633ef66684633f765584633fd56384633fd55384633df47284633fd532846339fc8784633fd531846339fd861c233cfe661c2339fd851c233d7e551c2339fd821c2339fd811c233df6111c2339fc8758233b7c8558233edd6358233bdd83182339fc8754233afd8614233bbd8414233bdd8314233bed8214233bf58114233bdd864c233ede664c233bdd854c233f5e554c233bdc824c233ddc724c233fd6114c2339fc8748233bdd8348233bf48148233df87048233fd93048233bdd83082339fc8744233bdd8344233afd8604233b7d8504233bbd8404233bdd8304233bed8204233fd53104233bf9801d2009fc8755200bf98015200dbc8791200dbd7591200f3e5591200fb880912009fc8791200dbd7491200d7e555ce00dbe445ce00bf5811ce00bf9801ce009fc8758e00bf98018e009fc8754e00bf58114e00bf98014e00afd8610e00b7d8510e00dbd7410e00bed8210e00bf58110e00bf98010e00ddc878ce00ddd768ce00ede668ce00ddd758ce00f5e558ce00ddd748ce00f9e448ce00fd8808ce009fc878ce00ddd738ce00dbe445ca00dde335ca009fd841ca00dbe441ca009fd831ca00dde331ca009fd811ca009fd8)) else (if i < 5 then (if i < 4 then 0xe3ea0f903e28f7b3db0f5d3d14f3f3cc0f213c48f033bd0ee53b58ec73ae0ea03a44e8239cce64390ce343894e1f3864e133834e073804dfb37b0de63780dda372cdc536fcdb03684d923630d743594d56351cd4134c8d0833e4cea336cccc3318cae32a0c993204c693168c4b30f0c2d309cc183024bfa2facbdc2f34bbe2ebcba92e8cb9d2e5cb912e2cb852dfcb702da8b642d78b582d48b4c2cf4b372cc4b2b2c94b1f2c40b012becada2b2cabc2ab4a9e2a60a922a0ca742994a5f28f8a3828a4a1127e49ea276c9c326f49ae267c999262897b25d4966255c94824e4933246c915241890023a08e223288bb22b089d223888821e487321b4867218485b215484f212484320f483720c482b209481620408011fec7f51fbc7e91f8c7dd1f5c7c81f087bc1eb47a71e607921e0c77d1db87681d6474a1d107351cbc7201c6870b1c146ed1b546c61adc6b11a8869c1a3467e1998657194464218f062d189c618182460317645c116ec5a3162c573159055e153c54914e8534149451613f84f813a44e313504ce12d84a7126048911e84741194456114044a111043e10e043210b0426108041a102c4050ffc3f90fa83e40f543cf0f243c30ef43b70ec43ab0e703960e1c3810dec36c0d983600d683540d383090be82eb0b702cd0af82af0a802910a08273099024308d021c08101ec07501bc0690183058814104c811a042c0fc03b40de033c0c002c40900204072018c0420084000bfd8219633bfd8119633bfd8019633bfe8858a33bfd8018a33bfe8854a33bfd8654a33efc8654a33f7d6554a33fed6254a33bfd8014a33bfe8858633efc6558633efd6258633bfd8018633bfe8854633bfd8654633f7c6554633dfc7254633f7d5254633ff56154633bfd8014633bfd8648633bfd8548633ff56148633bfd8608633bfd8508633ff55108633bfd8008633dfd621c233dfd611c233dfd211c233bfe8858233f7c8558233efd6558233efc6258233efd6158233bfd8218233bfd8118233bfe8854233bfd8654233dfc7254233f7d5154233ff96054233bfd8214233f7d5214233bfd8114233bfe8848233dfc8748233bfd8648233bfd8548233fed5248233ff48148233fed2148233ff96048233bfd8608233bfd8508233bfe8844233bfd8644233bfd8544233bfd8244233dfc7244233ff55144233ff92044233bfd8604233bfd8504233ff56104233dfc761d200bfc8255200bfd8215200bfd861ce00bfd821ce00bfd811ce00bfe8858e00bfc8758e00dfd7458e00fdc7358e00bfc8258e00bfd8218e00bfd8118e00bfc8254e00bfd8214e00bfd8610e00fdd6310e00bfd8210e00bfc828ce00dfd635ca00dfd541ca00fbd841ca00bfd831ca00bfd811ca00bfd8610a00bfe884ca00bfc874ca00bfd864ca00dfd764ca00dfd754ca00dfd744 else 0xa1400304060c00304aa0c081060a0820182820414b6101050402d8142008b050806096e101825586040820400000400000400400400304001820410410010204100000420004100020800104080820d04080c2002c102030810120c44180c401040208001040008301040e450a030810104080820014180c20002024122c8418084011500111402111403100410002080010408082040602450808082000c1008a010802092e100824586040420186000000000000000820800004104020c200104104001061008208000041000000003a038003008240a4e4f849f093e127c24f849f093e120c2418483090612595617193e12f93e22591622591622591622591622591622296e0b1914ab058c8a4b82c64f840700889f093e127c24f849f093e127c2e622a16320c2418483090497018c824580c641b34063e0737fbdf477b9de87789ddc7759dd2b729dc476f9dbab6dbdb0f6abda4f67bd96b642d8cf61bd80f5d9d72b5b2d66b58bd5ab552d4eb52bd44f4fbd38f4cbd2f34a4d233474d173444d0b3414cff33e4cf333b4ce97372cd23327cc63300cba32d0cae32a0c9ff267c93f240c8a3219c7e31cec6ff1a7c61b16ec55b13ec49b10ec4230e7c33f08ac1cb05ac0c3018c002fdfbefafa6be3af6dbd7af46bcbaf16bbfaef8bba6ed1bae6e98ba02e5fb91ee26b83adf6b77adbdb6bad96b5fad5db516d2db456d06b396ccdb2d6c94b216c49b0a2c10afe2bceaedab9eae3eb77adc6b59ad06b29abfeaf0ab62aaeaa5aa7ea99aa45a892a03a7f69dca7129aca652973a592955a4f6925a3ca8daa29e87da12a844a0b281da05e808a00a7ea9f4a7c39ed27ae9ea27909e067459cda70c9bf66ca9a3a664995663498725fb976a5c2968656e957e54794e2529948e50b94164f693324bd924e48491d64669182451912e433906e40c8f663ca8eca3918de63618d0231f8c4230a8c122fe8be22e98b8e2cb8b162928a0e26b897222987da1e7871a18a85ee16384e60f4832a0b281fe04c80ae01c8011ff57f75fc57ed9f8c7dadf267bf1eed7b79eb47a71e607891de87741d8b75cdd647531d3d74b9d1f7465d1373edcec7375cce7249c7a7141c4170a5bf66f9dbb46e4db7b6cfdb156b65aca6aedab56a99aa06a45a8b6a15a6d6979a3d6895a0d67d59dd673999b651191a64098e16301884618d83060857ee5ec97765ce97075b516745995656591d62f58815e4570d5b4560554e54494d652f948251cd464517944f512542850654134f5d3c84f093b34eb53954e3d3804de936b4d4d34d4cf932f4c813114c092f34b912d54ad12ae4a592904a05272496925448f122448311fd47b91d646f91a6468116d457914f450113a44ad11c445910743990e042fd0b042a9092423107d419504d411d0023fccfed3f78fd83f48fc33ef4fa) else (if i < 6 then 0x20180022280020392e001810101424100041e04841bc08344811940c8f0848552d85f1f2e2c4817c288551216c2f8f9400c02428282041610006058800050a0a0c1410000181620042150581402000e8c0304021b878584018216060760a049436160a8043b0f982c0c4281a442825bc282630484c22da140d196f0a098f0a09083a8f034703c085b1e5f950a0e1412100c182820414b610000042c8f04872400821d0605c1320041208301840808204040b101402100210e8581885024b01040a01088209c7c7850485850484410323e3208271f19041000000018200180e10015058040a1d1400085c2c100010e8002c0d04ca1d0b0360a02940008591e098f161dc0c030a5f990b0a140c1074128f0b881fc587702002ae1672a8901d85910a090b1781000930a2957160212616582954961c3c18292c287820302848307850f043a164781a44292c821e6f2b8b81c030a411c3a16428364428200043a170483848092c20e6571600026146cde2c08410be166cde5408410761664281820266f2b8b001070b381601100010c834205824b040008000301c10001000200040e1e0c03c110018004b080c131187a4028218118407cd8541012140a087b2a08c084c504038461d141d102337952583827366f2a0807099bca92c100e09cc4584000800004000020000609440004011b8286008dc40c0a040005c408080400842c0c0e82409286c2a0b028581a010e826904010480d100041080614068603400463cde560781278366018401a185b378501838501821d0b018260a943d950280f0212982d9b0280f02129b379501e040a0d9b379502810252e6f2a03c084850e86c2a0c058180a010b00ea000200040008341c100410e8580a060982a60701501180410e8581806024a160e824060d941b9bcae140602180f9b019042e0e9900418b3785019042e0e9882080010000080004da1430042006c2a0b0280c043000102160800005840000100060801021000004b7080012ac200049f0800120c3052a92c3820a4b0a082830504004b0a000016200014200014227820304000508004f8800818a0cde54124f074a0004b60800180000800180010a2c8a410e04292c821800180008b0a04082002084004085066f2b8bc2c0e00411c00080000400000081010408092c202020c04100020000840000125c200048b090418042008416082c105914205830b041a082c10192caa182c14082040000001012c1000000608000021028205060028002028305043d080050400032296e4028281060a08581008b0508002825502840322c40505020c14182820014102825585010c16102c24505020c00010400000116100000002022c2000000000c127c3000caa4b0c06080e125c20306000060c2e106c3042cb6450e040425b05845505c44f050a0915 else 0x5bc28903032070a186cab850b880503058504840503440503058512040904aa9b8a860504840503041c841208140410140c10140c126e03100c02160e020988ab08140410140c10140c5b808809070a090b0a09080309070a020c3a0008001d080108140d16144410483e104cbf110610281820280820281820281820b00c220a0422aa6c2c289022f8262c280820281a20042050326caa41140a062d9044092542c1e16120a0624d824202824202824201018202818aa18140c10140c100a10905c20482064de1430325403851039082c1b100c960d0c001408001e0800080a00070800060a00012c3d18003c111636162dc141a039c0008080e1208064582834400020207078202a6c4719141c088c000308001e0806160687008400080800040800240800060800042000404000404082584432da6e20026c0a18483c101424040c008588aa4b88001e88000820c600840f0008000408060106c6000e040002040003048004009b82c6000384074004800383834002030b1060a4506cc9b03a0032082a200014222a012b0590001c08000408010a6d0a1000002040005040002040000a6d0a200010000c222c010a09100407880003081803883c552586054d80230283a001c00825904381c)))
def l191xr8 : Packing := (712,3,6,63,0,14,1,p191xr8)
def p191xi8 (i : Nat) : Nat := 0x3c7e112029b1e95605cc030f23c03a4879621a211dead80006adac06d6144000283c821be39b8499a07a0cd02628398a6290240003068ec16000082a14553a1fe0fc000147a38c9b10e0001464000081fea99b93218bb00000083002e0790001e856c63802ee04ee15e8780a35a230c2f00005892d516c423c71301f813282b847b5058000148440237072d4f5424594390d951db81d6003308bb526b0b901fda2005066296c451002a1aa837ec08010f0000000002d20342000013700980000000e3b045c489c2017a094033807890e2c489466a0e4502800034746433212c000145882bc707522fc00028ba321ca469d1a2909612e8960c69685fa1fd214a88cd80e0000000242b406b022a41ddc5610fbd0c8a092070a0d4b5be00cb40e6089d0bce98fc361061000040f893428400001828788a38be0149e8000007c39e222e21502449138083616c0000076320e833208840b500000000c57910a71a180cc0274c15f031c23200ea2b8043ac0bfc6eb07f1088c8b0c7ba8210001085244800a7000103e9e178000d0d082ad06060cb408e0000c71d06f3054497b02a791d80d281f40004a8ad1ae625443a304922178253d30b03d722522340000ae96073c3180004084708600020777c3b51eae4878436016005690c000000000000606f83680000000000284448eac08bc02304131233013a84c0003a940000c41000028040000000240cc0f8501a02b505e8000c43323bf44f10c311612380000000080b2446d011a28d911ec1ec00b809ac57a4339c6d8000603ce1eb80504004167847012c8000642cc2d08932103f18a4130462021b500743adc67da86201f6033040986ab059e13cc40508380c0000304ebc32b16ec0a583198e5bc0000001050ade81408405c8b78dc1144a3cf83800a90001a004000191f0000a29880d000031fb609800060c1d0cae0dc0006815f0a1030b83e7208206a000000060d89063a10a41de06eb195a0b7c7caa8fd1ac826f02508e781e3c34e06f312580a7ea1742ad022e97c90b608071021050428f45b090cb1b4497082ef43c70c58418082f924100e40e0859484b8023827e48ba05c84ca0d686044c58006041810c24206701c896113408e14204012004100240010c040401b041400308081063600680041018700180120e10188001c203001428d0e144801c151391c103040008406222820b1020400181ed834c00008024400a5a08a82044072a001039d
def p191xr9 (i : Nat) : Nat := (if i < 1 then 0x50e00090713b26c5a54362c1014000a95b9b1655950d4b8b45850400b0026e140c5d043a75b9b55954b8b458504004102b02e6e560400344a7059b950981160012a16e6d56552e2d1615060458340c02e019b958b85160d0002a6556e063e49b55818f9155046c3e45b41150f907410903c0e55b5541030f956d54043e49b95418f905824885c3c0265b5541000f946c540c048858305d3c02a009b95814f946c542c0c04345888243802b009b95814f94542c046c14344858883802b041d00241403986c542c140c344858883802b009b958b8541992d6d551504002e7004f89156d552d0400167004f896d552d1504000e70085056d552d14000670041896d552d1504026004f88002c356d2d5515068005f4f8d6d55053e45b554b45410098013e200554b455b41e69c017d3e30005165b4b455541a0017d3e3004f88012d1635b55414f916d552d1504026035b554b4541009c002c356d55152d068004f88016d552d15079a7004f88016d552d15079a75b554b454100980106200010d5b5545414ba001053e3005b554b4145e69c01053e3005b554b4541e69c010625b554b454197993e2e64f8b9a1e6418b0e1842c0a5f1af11762b8e5bdad71692b2a58bac015e2ac254faa214daa56517a8713fa9e24e3a6a132296e4a3a4311da8ca459a2510da8424079fa0f927923b79cb0e226f23699a80cf264631397d0baa5b22bb9540a7a52a28b94109da4d626192c092a47e22990f081a3f61e38eb06fa3621a18ce063230e1778ba05922be1518a604ea26612988e045a20e0ff877039a1c20d9868030a1660a184e023210e07783501920a604b81e00d204a01f80a003a0120058001ff99a33ffacb19ffc658cfff2ac67ff58a33ff8c519ffd528cffe29467ff58633ff8c319ffd518cffe28c67ff48633ff84319ffe118cffeb0467ff18233ffaa119ffc508cffe90467ff08233ffa2119ffc108cffe3a401ff55200ff8a9007fe44803fe39c01ff58e00ff8c7007fd53803fe29c01ff50e00ff887007fe33803fe39401ff50a00ff885007fd32803fe19401ff88a00ff8e3007fd41803fe20c01ff4c600ff863007fd21803fe10c01ff84600ffa81007fd30803fe90401ff44200dfccd19f7e558cfeeb1c67f754e33bf8e519fdd328cfee98c67fd84633bf8e119fdd308cefeba401ef91200bfae7007de33802feb94017f1ca00bfae3007f611803fca0401fe10200ff261007f830803fc90401fe08200ff221007f810803fcba401fe1d200ff2a9007f854803fd22401fe5ce00ff0e7007f963803fc31c01fe54e00ff0a7007f943803fc21c01fe8ce00ff2e5007f872803fca1401fe10a00ff265007f832803fd11401fe5c600ff0e3007f941803fc20c01fe4c600ff063007f921803fc10c01fe84600f7489007da33803f511401fc84600 else 0x55081d418112225b8fa47604597e3e52455178f5b956c210604485891563e91b55418112248f9c263d7c2a45b1541811216248fa0263d7c2a45595081d121c8f9c0a3d7c2a45b9b080112178f9c0a3d7c2a49b95018f0a95063c2635b9b55958b080402124185ac6d54207506048a3e80524815f12956e6c21045e3e60524815f12956e6d56540d0604023e9008f090a916e6d5654200a3e79b9501008f0a98643c5000343a6150b41810023139c00513d7c3a59b95851481004b0da078603c201c5835140291d1b55954b8b05418113231e0900b85a5422046c004a74b8b094181050023a000205d7c4a5009b9509814f0d9c026c5a544c212d143a95b9b5595084181004512a96d552c511421041090583402c5b9b55950341810013a4026c5a540d3c3a75b9b1655954b8b418106130800b4026c5a540e05144a85b1d9b1655950d4b8b45098541810300c0701c10005c3a69b950b01000e139c026c5a54113c0a75b9b1655958b)
def l191xr9 : Packing := (113,2,6,63,0,13,1,p191xr9)
def p191xi9 (i : Nat) : Nat := (if i < 1 then 0x225458301e22344025984107f1d50000d20ee06580228183c205a0275101149ce27e0000f166417bd03761dfe18c955e615b725dc290610b74b0c1080000000094f1000020042c06e0e584df947db45a5193823b203b31760000309fe484000060770000000061250000456e92720105a0690000203d000030b2000000005067257ad2a731c5a1698044b56021335c98000002974276d194605be260c179102424ad922b325e0000703a02ae91290000763fb1c7820b00000000d22980f0416510a60000921fd51c143884fbe286000000000000311ac1d1421439bf60133038420611500000442da0a97664b0580000006200000000c52bb10660457250901a6225f4c2245ca24f6085255d3a61e140c048e1b381cb02be52bca4390000a055e27b00008806812300008cfbc510a43bb1feb0e4d1caf05f000021e0d0bc21e9b03634f701884cdf30710000853841f40012516100006888925330a1b18bb17f88a0000075b9927f590e8079308ca446c54aa195045621a3a0bd90da5096000040bbf2660000000042ba0000f24a0000e28932b3607a745512750000320f000040b7b66592007068c030d19be16b709d84a0415350fd95a00000f052b22c00000000c28200004c9f000081e751cd60fc0000a23af1f151c9a21de64400004247416021bda2230000000080c6105722c5f02c00f64112a0d56173d11c71352025d0f1e50e24ba709bf1ac88d0806a306131e64280d0420000189340b1f50c8032e18ad0d421d89228911ec258d100d635629121d4f25ce0b3824b054590d7c1743431a43491a800000000c1a5b12e30e7614145283075cc5ad89e20c3c09a6059ca5d641ca21c3245f4476056310ed26c645718c0a46dc514649814d20000f2b692b100008211815f808a607f7163f1a0f40350cbc0aa8098064500003571d00b284c0000f03181fdb1710251e49b00000000a8a1512f0000d138b050000b020e176b030f021d0d1b1404070606030236070216080a020304000d120e172710121602041400050005076404090109040b5a1a01050a0822080515030000041101051402011103090b0000001c00030610130301000016252200120502001b00012c02130000023b000a011c0b0a410300070b050c110f000a0a0a0505090d043a1517000c0619074a02001601451d0e030b081a00052a04010820020009343500051a63002e0501030e00051c01110009001a2a17061c0b0b0026205804131005080005040021051b050a000f1f58030007080a010190051b00040c09000b460e2a0004001400040408020f090f00012a2d2a060e0018100baa0804020115002f000400000002021f041112002b0a0406100500012d03020200000112091d1504001402230009000704060f002f03080001000d2e0e1309060000050c04051d11 else (if i < 2 then 0xe63db261302120b47a60b2b272650a39218071d371b7315e1192327c82221288f03cc238e25b9006d003328522bb9674f01581a96e61421a8231549f70bf21e5e2c3d54c36534433f07361597293408100007278000020aff4f3b1eb0000926ee2373124628a00000000a047c0ff000021b031fa41f0665ee552e22f321e906d6089190db5777208565a813b966161fb446c3264120a755c70c7b1b531a630c182407654c507001041842267924da02a006420bee186b13c1218115142a6e17a007d61ec20ef3119022474c1d2a2716e74cef26221ad0122c428000080337035144a0000125794e5f1f32023600e000000000000b1d7f120712a0000529e7501a053b26a00000000f07c0000617eb145910a923571f22895705400e61005000000000000b15d21780000000020c4d19a255700000000e17c0000814874068589a22e1090d008c2b542b72667f009559d616f5279d182b539048b74763542f863019f66682199728430c5f16220a8d00ac132c039f1a78217905ca15a4137c29a620c65687543788c81af588e0000d29260463103659c50dce220f44560805252889d924ef1278566f2a8f13691a44236a22a21c2066f0000f1bb0000e461601bd42952c7c06f814f10784474805a70e96532f0b5f11641cce4d850fbb432489f8147e4113242948fb227e0b81207f19832acc16de54460f7601eb29b607b608b81dca0402502142671cfd43ad0ab409c80c0d4cd02abe18950c92117b0f9c21945be818e40f39910f01d70e0706cb63bd23042a3d28f2593d13fb126b19d1185e028d531459e4226067ba017096da19730ecd01f91bf81095454e121109e80d1618ff088846b1130a2bd04b838949093d48570e360a41463819ec43cc2c690eaa04d929681b98087c09101676583e4cc0638e03fe59f62a120ee011b81c4912b5241940e9146d402c20131f734fac852d536d08f91e8810231da71119187525680b6c404826bb1a2c27d506e75a6789624e1e17081ce80f20442b02034dc4144b5403299f13aa0caf450c018607230ebe15cc51530cd1099b29d45277441a12c618dc00061de00d3b2a0828c32210547e26d71d6a1ba51c1b578f16a11c62156e1495104a4bce049f1f9e0d8010c313141bc585a04a90270557fc4cf91d21118665c400d00cf5007e14ad10d4ca174c6f157000050ac008495265139a53714e274a171c3b8a2d2c2a213d1ffe1b8764c12819283227301ee31ed64d152a50000d88f2c631246a1b65134e255d890406bb0f5766ee462f1ef12ade2b950d06579e1f5048ed0fa8271300222c10000b1910000602dd2940000512d00000000f0a0249a941d000000003181e44e414e256f6287767c7113864fa23441585244b114400f101cc274b1527493e842006030d951b280f8c5293063844dd11d0000210f else 0xa13dd5882472f1a1a59b70c800000000e49942b80000d1bec29f00001ca0e04ad02f80a36564723e225a244fd451129561aab530687bf09291aee05ee496eca2c4d7b24c12a9823d01d082771495b54f014b82024001509711fc41e35243140f8486f4b1000070c2216c31c00000043fc28b5154819c72b03233329cd2c046466269c0e2b25971c830de54ee707ef21674d59164a4dd6628e249611f40ce527ad0b0f2af60d291553541b0db104c211054f2e2b462099128620470d6888de2bf95a7023c4263b14d18987203e0e851e1c1e23143617d463451dd522d50a26248a190521584b2121b01ea51ab6640548a61b124cba142a2a4d1e4e019a47ff28e5115e0ad508311f6d5a9a0e12094d28d10edd8822212725f405d00cc252f152430ba4076709504ebb066e490c08eb1db521072987082b1d9e42eb1b4748db2680000e239e0fe764d40a7804fd1770000513e857e0000000034a2000090dd74e0800c02aa0000d0f404940000000000009016000074ecf23200002401b0b90000220d54e6f05100004487d26f00000000f19600004041a029d1f80000308da0110000d02b0000000030ae0000402ec034345e000000000000e04b9014e026e08614e32172b074a2c4e4a760a554c40000c03e0168f17530430000d0df00008070314c0000))
def p191xr10 (i : Nat) : Nat := 0x1b2a047c86ca8b0a0404d9a1f4d03fe33ff803fa00
def l191xr10 : Packing := (3,1,6,63,0,6,1,p191xr10)
def p191xi10 (i : Nat) : Nat := 0x616486003e00e016aeac018c58283bd7f20a61fb0a9922ad984bd32f17c65016aa0c74a2e23b2ee07855c807802803fc6a06ea58d29892c2ca0470818c81ecf6190002c3b487557d12000000000000259a4a4dc260002d28e540000000000000c4ef14c110263601016e8c9e6aa1ec93a4bd26b333ea24000660b37b194001843020c085cb0a1582921c394268a8648344c6e4c3d1ca9b400126820dd0050afc0b825580f492a2012342a4457e3c822c90a53942ce66526c001ca0c33489e9a000000070e00018103670000e3a40832b000182e690f0078a51acc26553f0d9848000c0b4312c5a25f000520958aa11e172a0c034000c34e0ce91fa4f0005b1b45f804e30c0d0829c3a84a8000c1be5c0001435418000811311cc77c98a2af048000000000787cc9666c9220000c4a0a8e09b8654c542814c0c06021450000002640900468c60091400820ea0420410ce0072d128045d3c70022006c56007d7
def l191x : Nat → Packing
  | 6 => l191xr6
  | 7 => l191xr7
  | 8 => l191xr8
  | 9 => l191xr9
  | 10 => l191xr10
  | _ => emptyPacking
def i191x : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 3 15 3 8 4 0 p191xi7
  | 8 => lookupWord 119 419 7 15 9 2 p191xi8
  | 9 => lookupWord 324 1104 8 16 10 2 p191xi9
  | 10 => lookupWord 54 191 6 13 7 2 p191xi10
  | _ => fun _ => none
def s191chart : Forest := ⟨191,11,g191.samples,.fork 38 g191columns (.leaf [(0,0,191,0,11)]),g191autos,l191x,i191x,noFactory,noFactorySound 191⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geos191chart : graphValid s191chart (boundsBefore known383) = true := by
  unfold graphValid
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel, by decide +kernel⟩, ?_⟩, by decide +kernel⟩
  apply listPieces_all (d:=3)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cka_6_0 : block s191chart 6 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cka_6_1 : block s191chart 6 1 10 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem lka_6 : block s191chart 6 0 11 = true := (@block_merge s191chart 6 0 1 10 cka_6_0 cka_6_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cka_7_0 : block s191chart 7 0 64 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cka_7_64 : block s191chart 7 64 64 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cka_7_128 : block s191chart 7 128 64 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cka_7_192 : block s191chart 7 192 24 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cka_7_216 : block s191chart 7 216 64 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cka_7_280 : block s191chart 7 280 15 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem lka_7 : block s191chart 7 0 295 = true := (@block_merge s191chart 7 0 280 15 (@block_merge s191chart 7 0 216 64 (@block_merge s191chart 7 0 192 24 (@block_merge s191chart 7 0 128 64 (@block_merge s191chart 7 0 64 64 cka_7_0 cka_7_64) cka_7_128) cka_7_192) cka_7_216) cka_7_280)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cka_8_0 : block s191chart 8 0 39 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cka_8_39 : block s191chart 8 39 64 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cka_8_103 : block s191chart 8 103 64 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cka_8_167 : block s191chart 8 167 64 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cka_8_231 : block s191chart 8 231 64 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cka_8_295 : block s191chart 8 295 64 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cka_8_359 : block s191chart 8 359 64 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cka_8_423 : block s191chart 8 423 64 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cka_8_487 : block s191chart 8 487 64 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cka_8_551 : block s191chart 8 551 10 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cka_8_561 : block s191chart 8 561 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cka_8_625 : block s191chart 8 625 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cka_8_689 : block s191chart 8 689 23 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem lka_8 : block s191chart 8 0 712 = true := (@block_merge s191chart 8 0 689 23 (@block_merge s191chart 8 0 625 64 (@block_merge s191chart 8 0 561 64 (@block_merge s191chart 8 0 551 10 (@block_merge s191chart 8 0 487 64 (@block_merge s191chart 8 0 423 64 (@block_merge s191chart 8 0 359 64 (@block_merge s191chart 8 0 295 64 (@block_merge s191chart 8 0 231 64 (@block_merge s191chart 8 0 167 64 (@block_merge s191chart 8 0 103 64 (@block_merge s191chart 8 0 39 64 cka_8_0 cka_8_39) cka_8_103) cka_8_167) cka_8_231) cka_8_295) cka_8_359) cka_8_423) cka_8_487) cka_8_551) cka_8_561) cka_8_625) cka_8_689)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cka_9_0 : block s191chart 9 0 4 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cka_9_4 : block s191chart 9 4 56 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cka_9_60 : block s191chart 9 60 53 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem lka_9 : block s191chart 9 0 113 = true := (@block_merge s191chart 9 0 60 53 (@block_merge s191chart 9 0 4 56 cka_9_0 cka_9_4) cka_9_60)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cka_10_0 : block s191chart 10 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cka_10_1 : block s191chart 10 1 2 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem lka_10 : block s191chart 10 0 3 = true := (@block_merge s191chart 10 0 1 2 cka_10_0 cka_10_1)
theorem taba : checkedTables s191chart 10 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact lka_6
  · exact lka_7
  · exact lka_8
  · exact lka_9
  · exact lka_10
def offered3853 := vars 383 ++ [minus3853]
def alt3853 := vars 382 ++ [minus3853]
def ord3853 : List (Fin 9) := [1,2,3,4,5,6,8]


def primSigned0 := primary3853 0
def negSigned0 := neg primSigned0
def unsignedList0 := primSigned0 :: vars 190
def signedList0 := unsignedList0 ++ [negSigned0]
def signedAlt0 := vars 190 ++ [negSigned0]
def witnessesSigned0 := graphPairs 190 13438755108

theorem allSigned0 {k t S} (run : Live (graphGoal 191) k t S)
    (sub : ∀ w ∈ S, w ∈ signedList0) : ∀ w ∈ vars 190, w ∈ S := by
  have eq : (witnessesSigned0.map Prod.fst) = vars 190 := by decide +kernel
  have h : checkEssential (graphGoal 191) signedList0 witnessesSigned0 = true := by decide +kernel
  intro w hw
  obtain ⟨r,s,hd,hi⟩ := essential_ok h w (List.mem_toFinset.mpr (eq.symm ▸ hw))
  exact raw_required run _ _ sub r s hd hi
theorem smallLower0 : Lower signedList0 (graphGoal 191) 11 := by
  intro p bank reach target
  by_contra! bad
  have pro : proper (graphGoal 191) := by unfold proper; decide +kernel
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live pro reach target
  have small : k ≤ 10 := by omega
  have all := allSigned0 run sub
  have raw : unsignedList0 = primSigned0 :: vars 190 := by decide +kernel
  by_cases negIn : negSigned0 ∈ S
  · by_cases posIn : primSigned0 ∈ S
    · have eq : S = signedList0.toFinset := by
        ext w
        simp only [List.mem_toFinset]
        refine ⟨sub w, ?_⟩
        rw [signedList0,raw]
        simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
        rintro ((rfl|h)|rfl)
        · exact posIn
        · exact all _ h
        · exact negIn
      rw [eq] at run
      exact root_index (g:=s191chart) (before_sound known383 valid383) geos191chart
        taba (k:=10) (by decide) (i:=1) (ws:=signedList0) (by decide +kernel) k t small run
    · have eq : S = signedAlt0.toFinset := by
        ext w
        simp only [signedAlt0,List.mem_toFinset,List.mem_append,List.mem_singleton]
        constructor
        · intro h
          have d := sub w h
          simp only [signedList0,raw,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at d
          rcases d with (rfl|hv)|rfl
          · exact False.elim (posIn h)
          · exact Or.inl hv
          · exact Or.inr rfl
        · rintro (h|rfl)
          · exact all _ h
          · exact negIn
      rw [eq] at run
      exact root_index (g:=s191chart) (before_sound known383 valid383) geos191chart
        taba (k:=10) (by decide) (i:=0) (ws:=signedAlt0) (by decide +kernel) k t small run
  · have sl : Slice (unsignedList0) (graphGoal 191) one 11 :=
      slice_correct (ms:=[]) (base:=vars 191) (G:=graphGoal 191) (by decide +kernel)
        rfl pro (lower3853 191 11 (by decide +kernel))
    apply useSlice3853 run sl _ (by omega)
    intro w hw
    have rawIn := sub w hw
    simp only [signedList0,List.mem_append,List.mem_singleton] at rawIn
    have mem := rawIn.resolve_right (fun e => negIn (e ▸ hw))
    have hv : (unsignedList0).all (availableB one (unsignedList0)) = true := by decide +kernel
    exact List.all_eq_true.mp hv w mem


def primSigned3 := primary3853 3
def negSigned3 := neg primSigned3
def unsignedList3 := primSigned3 :: vars 183
def signedList3 := unsignedList3 ++ [negSigned3]
def signedAlt3 := vars 183 ++ [negSigned3]
def witnessesSigned3 := graphPairs 183 13438755108

theorem allSigned3 {k t S} (run : Live (graphGoal 191) k t S)
    (sub : ∀ w ∈ S, w ∈ signedList3) : ∀ w ∈ vars 183, w ∈ S := by
  have eq : (witnessesSigned3.map Prod.fst) = vars 183 := by decide +kernel
  have h : checkEssential (graphGoal 191) signedList3 witnessesSigned3 = true := by decide +kernel
  intro w hw
  obtain ⟨r,s,hd,hi⟩ := essential_ok h w (List.mem_toFinset.mpr (eq.symm ▸ hw))
  exact raw_required run _ _ sub r s hd hi
theorem smallLower3 : Lower signedList3 (graphGoal 191) 11 := by
  intro p bank reach target
  by_contra! bad
  have pro : proper (graphGoal 191) := by unfold proper; decide +kernel
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live pro reach target
  have small : k ≤ 10 := by omega
  have all := allSigned3 run sub
  have raw : unsignedList3 = primSigned3 :: vars 183 := by decide +kernel
  by_cases negIn : negSigned3 ∈ S
  · by_cases posIn : primSigned3 ∈ S
    · have eq : S = signedList3.toFinset := by
        ext w
        simp only [List.mem_toFinset]
        refine ⟨sub w, ?_⟩
        rw [signedList3,raw]
        simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
        rintro ((rfl|h)|rfl)
        · exact posIn
        · exact all _ h
        · exact negIn
      rw [eq] at run
      exact root_index (g:=s191chart) (before_sound known383 valid383) geos191chart
        taba (k:=10) (by decide) (i:=2) (ws:=signedList3) (by decide +kernel) k t small run
    · have eq : S = signedAlt3.toFinset := by
        ext w
        simp only [signedAlt3,List.mem_toFinset,List.mem_append,List.mem_singleton]
        constructor
        · intro h
          have d := sub w h
          simp only [signedList3,raw,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at d
          rcases d with (rfl|hv)|rfl
          · exact False.elim (posIn h)
          · exact Or.inl hv
          · exact Or.inr rfl
        · rintro (h|rfl)
          · exact all _ h
          · exact negIn
      rw [eq] at run
      have sl : Slice signedAlt3 (graphGoal 191) one 11 :=
        slice_correct (ms:=flip3853 :: [117, 67, 32].map swapRows) (base:=vars 703)
          (G:=graphGoal 703) (by decide +kernel) (by decide +kernel)
          (by unfold proper; decide +kernel) (lower3853 703 11 (by decide +kernel))
      apply useSlice3853 run sl _ (by omega)
      have av : signedAlt3.all (availableB one signedAlt3) = true := by decide +kernel
      exact fun w hw => List.all_eq_true.mp av w (List.mem_toFinset.mp hw)
  · have sl : Slice (unsignedList3) (graphGoal 191) one 11 :=
      slice_correct (ms:=[]) (base:=vars 191) (G:=graphGoal 191) (by decide +kernel)
        rfl pro (lower3853 191 11 (by decide +kernel))
    apply useSlice3853 run sl _ (by omega)
    intro w hw
    have rawIn := sub w hw
    simp only [signedList3,List.mem_append,List.mem_singleton] at rawIn
    have mem := rawIn.resolve_right (fun e => negIn (e ▸ hw))
    have hv : (unsignedList3).all (availableB one (unsignedList3)) = true := by decide +kernel
    exact List.all_eq_true.mp hv w mem


def domSigned2 := subcube 4 0
theorem sliceSigned2 : Slice offered3853 (graphGoal 383) domSigned2 11 :=
  slice_correct (ms:=[130, 50, 81, 115, 98, 65].map swapRows ++ fixRows 4 0)
    (base:=signedList0) (G:=graphGoal 191) (by decide +kernel) (by decide +kernel)
    (by unfold proper; decide +kernel) smallLower0

def domSigned4 := subcube 16 0
theorem sliceSigned4 : Slice offered3853 (graphGoal 383) domSigned4 11 :=
  slice_correct (ms:=[128, 16, 64, 100, 80, 113, 33, 48].map swapRows ++ fixRows 16 0)
    (base:=signedList3) (G:=graphGoal 191) (by decide +kernel) (by decide +kernel)
    (by unfold proper; decide +kernel) smallLower3

def domSigned5 := subcube 32 0
theorem sliceSigned5 : Slice offered3853 (graphGoal 383) domSigned5 11 :=
  slice_correct (ms:=[133, 117, 101, 33, 48].map swapRows ++ fixRows 32 0)
    (base:=signedList3) (G:=graphGoal 191) (by decide +kernel) (by decide +kernel)
    (by unfold proper; decide +kernel) smallLower3

def domSigned6 := subcube 64 0
theorem sliceSigned6 : Slice offered3853 (graphGoal 383) domSigned6 11 :=
  slice_correct (ms:=[135, 50, 65].map swapRows ++ fixRows 64 0)
    (base:=signedList0) (G:=graphGoal 191) (by decide +kernel) (by decide +kernel)
    (by unfold proper; decide +kernel) smallLower0

def extraFactory3853 : ExtraFactory := fun ops depth bank idx paid =>
  if idx == 60 then materialize offered3853 (chosenSteps bank ops paid depth) domSigned2 11 else
  if idx == 61 then materialize offered3853 (chosenSteps bank ops paid depth) domSigned4 11 else
  if idx == 62 then materialize offered3853 (chosenSteps bank ops paid depth) domSigned5 11 else
  if idx == 63 then materialize offered3853 (chosenSteps bank ops paid depth) domSigned6 11 else
  none

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem extraFactorySound3853 : FactorySound 383 extraFactory3853 := by
  intro ops depth bank idx paid c h
  unfold extraFactory3853 at h
  change ValidPool offered3853 (graphGoal 383) c
  split at h
  · exact materialize_sound (raw:=offered3853) (T:=graphGoal 383) (d:=domSigned2) (L:=11) (sliceSigned2) h
  · split at h
    · exact materialize_sound (raw:=offered3853) (T:=graphGoal 383) (d:=domSigned4) (L:=11) (sliceSigned4) h
    · split at h
      · exact materialize_sound (raw:=offered3853) (T:=graphGoal 383) (d:=domSigned5) (L:=11) (sliceSigned5) h
      · split at h
        · exact materialize_sound (raw:=offered3853) (T:=graphGoal 383) (d:=domSigned6) (L:=11) (sliceSigned6) h
        · contradiction

def p383xr8 (i : Nat) : Nat := (if i < 1 then 0x2bd8da140c88e70057e1b2281911ce00877b685432119c010fb6caaa64c818021f6d91514ca630061bd97690870c600a67b6843b2a18c0155e6dca065431802b3cdb140ca863005739b4281950c600aed3645032a18c011deaeda5261308023f55db444ba610055e9b225d734c2008ef576d2922984019d669633245308023dc5cb4838a610056dabb65a330c200cd732cd20e2184013dc6d4a14c110802b6cdb14ec9821005759b529d9304200af336853b26084015f26c8a764c108023dcdd32839821006739a56507304200ceb34ac98e6084019e6691931cc108032f4cbb4439821006769956887304200cf5328d10e6084019f264da21cc108033d8ca342398210067d19368473042008fd37439b24084015ba6d87364810802bb4da8e6c90210057a9b41cd9204200afc36239b24084011eeaeda425d83802b3cdb14eca907005739b429d9520e00aed36453b2a41c015dc6c4a765483802b9cda10eca907005759b321d9520e008f736854532b9c0136e6d0a760d738023f95db424c0e70047d9b9aa9731ce00ceb554caae639c0157aaed73648738031f955330c88e70067b2aa651911ce00cfc554c932239c013e6aeda4262338027cd5db4848c670047b9b42a1978ce009f336854b0719c013e66d0a760e338023dcda152c1c67004f5abb694838ce009db576d30e719c013d6aeda51ce338036cd3bb4839c67006dca77688738ce009fa576d08e719c01b749dda11ce338023dd5db4848c6700477abb6949360600af336854c66c0c015e66d0978cd818023dcda15319b030047e9b2aa99320600af336854c6640c011ee6d0a8a65318023f4d91514ca630047e9b2aa9974c6008f7576d212e98c0157a6ca999dd31802adcda12eb9a63005799b42a6334c600af33684bc6698c011deaeda5260318032dccbb4843863005579b5262770c600a6f37053b2a18c0159e6d8a765431802b9cda14eca863005769b229d950c600ae736843b2a18c0195eaaa7765431802bad5db2b198630047d9b9aa9310c6008fe3735526218c013f4aeca3662118027d8da14ec1c23004f71b52a483846009ee576d290708c012fc2e2aa1ce118031f8d4b5039c23004fb1b42a073846009fc364540e708c013f8aeda21ce118036f0b9b4439c230067e1a96887384600d7c350d10e708c01bb8699a21ce118037b0d2b4439c23006fa1a46887384600bf23685446708c013f42e9988ce11802ee85bb3119c23005f91b421e3384600bea36a41c6708c016f46e0738ce11802fa8da8e719c23005fc1b21ce33846008df576d312708c015f26c8a98ce11802be4d912f19c23005f91b428633846008fd36454c6708c013dc6d4a3606118027f0d955498c23004ef1b62a531846009f636853a6308c013dcaeda50c6118036b93bb4a18c23006f51a58cc3184600 else 0xe8e0818540e84001d04002808144413000980040000000300098004c00260010000000241020300040c000e000700038001a000d0006800340016000b00058002c0016000b000700038001c000e00070002060b07058382c1c160d0006800200410000000000000000020800480040000000000000000a000e020400020801040182000000000014100c0038081c040e020402820000000000000000000000000000000000000000000000502040000000000b2960ebed61ab752aa2533a5b47285cfa9e93ba744e29b932e5d4a993124a464869011ea34c638a51321dc2a833021fbbe67aaf11d9ba2722e01b7b5e69acf195b1a612c0d792e15a0afd5729d518a194027a4e89b9342624b89592823f4728cd1121c42c841052043fc7e0f91ec3cc780e79be37069ccb1852fe5e4b996d2ce584a814a2724a08b9061ea3bc748e31ba35c688cb18a2fc5c8b315a29c5089b12a23c448830fa1dc3886b0ca17c2c85309a11c2083b0540900f01802403003000a7db6439b2040c012df6d4a89dd318031f64c34439c2300527db629d9520e00a67b6853b2a41c014db6c8a7654838029bad894eca907005379b029d9520e00a67b6843b2a41c014d76cc876548380)
def l383xr8 : Packing := (140,5,6,63,0,11,1,p383xr8)
def p383xr9 (i : Nat) : Nat := (if i < 4 then (if i < 2 then (if i < 1 then 0x770c600d7e262770c600d7e65e770c600ddeaa9950c600dde6a1950c600dde2a1950c600dde69d950c600dde29d950c600dde61d950c600dde21d950c600dde9dd950c600bdeaa9950c600dde661950c600dde65d950c600f5e9dd950c600dde655830c600dde655730c600df665e330c600dde655810c600dde655710c600bf6aa9310c600bfcaa9310c600dfc65d310c600f7c9dd310c600dde655310c600bfc28d9884600bfcaa89884600bfc68c9884600bfc2a58384600bfc29d8384600bfc2a48384600bfc69c8384600fdc6948384600ff424c8384600efc60c8384600bfcaa97384600bfc2a17384600bfcaa87384600efc6a07384600bfc2a07384600ff45cc7384600ff86887384600ff46a23384600ff42a23384600ff46623384600ff42623384600ff469e3384600ff429e3384600ff461e3384600ff421e3384600bfc69e3384600bfc29e3384600ff460e3384600ff420e3384600ff45ce3384600ff41ce33846009fe68c98846009fe2a193846009fe69c93846009fe6849384600bbe6989384600bfc68493846009fe2a58384600bde6948384600bfc68483846009fe2a57384600afe6a07384600bee6907384600bfa6887384600bfc6847384600df62a63384600df62623384600df665e3384600df625e3384600f769de3384600ff46863384600ff428633846009fe2a63384600df664e3384600bfc6863384600bfc2a58184600bfc28d8184600ff48cd81846009fe2a58184600bfc68c8184600ff48cc8184600bfcaa93184600bfc2a53184600bfc2a13184600bfc69d3184600bfc29d3184600dfc65d3184600f7c9dd3184600ff420d3184600ff48cd3184600bfc69c3184600f7c9dc3184600ff48cc31846008dfaa99520e008ef690988ce009de694984c2009fa688974c2009de694914c2009beaa9960c200db665a330c2009f6aa993042009faaa99204200df464e1104200df864a11042009ee6909760e009deaa99520e008fe2a2991ce009fc286991ce009ee690981ce009fa688981ce009fc684981ce009eeaa9941ce00cee661941ce00dce655941ce00dd6655731ce009faaa9921ce00d7a5cd921ce00cfa661921ce00dba659921ce00dda655921ce00dea651921ce009fcaa9911ce00cfc661911ce00dec651911ce00df8649911ce00be6690988ce00be6690918ce009ee690988ce00bd6694838ce00af66a0738ce00bb6698738ce00bd6694738ce00be6690738ce00bf2688738ce00bf4684738ce009ee690918ce009de69493606009fa68a994c6009ee690974c6009fc2a5714c6009de694980c6009ee690970c6009fa688970c6009deaa9950c600d5e9dd950c600dd6656330c600bf428d9884600bdc6948384600afc6a07384600bf86887384600f749de33846009be6989384600bdc6943184600 else 0x9fe2a5835ce00cfe261835ce00b7e29d835ce00bde694835ce00dfc644915ce009fe2a2991ce009fe684981ce00dee6a1941ce00dee685941ce00dee661941ce00dde655831ce00dee651831ce00bf6aa9731ce00cfe661731ce00dee651731ce00dfa6a1921ce00dfa61d921ce00dfa60d921ce00dfa5cd921ce00dfa685921ce00dfa661921ce00dfcaa9911ce00dfc6a1911ce00dfc2a1911ce00dfc60d911ce00dfc5cd911ce009feaa9911ce009fe2a1911ce00bfcaa9911ce00dfc661911ce00cfe661911ce00dee651911ce00dfa649911ce00bf6285988ce00bf6aa8988ce00fe6690988ce00bf6684988ce00bf62a1918ce00df6261918ce00bf629d918ce00bf669c918ce00fe6690918ce00df6644918ce009fe69c988ce00dee690988ce009fe684988ce00bee690988ce009fe2a1978ce009fe684978ce00bf668c978ce009fe2a5878ce00cfe261878ce00bee690878ce00bf668c878ce009fe2a6778ce00bf62a5838ce00bf629d838ce00bf6285838ce009fe2a5838ce00bf669c838ce00bf6684838ce00bf62a5738ce00bf62a1738ce00f769dd738ce00bf6285738ce00f769dc738ce00bf6684738ce009fe2a1918ce009fe69c918ce00bee690918ce00bf668c918ce009fe69c93606009fe2a57360600bee6907360600bfa6887360600bfc6847360600df62a63360600df625e33606009fe2a633606009feaa993206009fe6a48320600bde6948320600df664c8320600bfc68483206009fe6a573206009fe6a47320600bee6907320600bfa6887320600bfc6847320600df62a63320600df6a663320600df665e3320600df664e3320600ef68cd81206009fe2a2994c6009fe69e994c600df668e994c600dfa68a994c600dfc686994c600bfa68a994c6009feaa8984c6009fe69c984c600cfe660984c600bf628c984c6009feaa9974c6009fe2a1974c600d7e65c974c600bee690974c6009fe2a5874c600bf628d874c6009fe6a4874c600bee690874c600bfc684874c600d7ea66774c600d7e262774c6009fe2a6774c600bfc286774c6009fe2a5834c600cfe261834c600bfc285834c600bf6aa8834c600df6a64834c600f769dc834c600fd6694834c600bde694834c6009fe2a5734c600d7e25d734c600bfc285734c600afe6a0734c600bbe698734c600bde694734c600bee690734c600bfa688734c600df62a6334c600bf62a2334c600df6262334c600df665e334c600df625e334c6009fe2a5814c600cfe261814c600bf628d814c600dfc2a5714c600dfca65714c600ff428d714c600ff420d714c600ff48cd714c6009fe6a5714c6009fe2a5714c600bf628d714c6009fe2a2990c6009fe69c980c6009feaa9970c6009fe2a1970c6009fe68d970c6009fe6a4870c600d7e65c870c600bee690870c600d7ea66) else (if i < 3 then 0x1950c600cdf661950c600cdf655830c600cdf655810c600cfe61d900c600df64c5900c600dde655900c6008ff68c98846008ff2a58384600adf6948384600afd68483846008ff2a19084600bee692994c200cfe2a1974c2009fe684974c200d7e65c974c200bfa688974c200afe2a5874c200bee690874c200bf668c874c2009fe2a6774c200afe2a2774c200bde694834c200afe2a1734c200d7e25d734c200bbe698734c200bde694734c200bee690734c200bfa688734c200bfc684734c200bf6686334c2009fe69c914c200df68cc914c200bde694914c200dfc644914c200bf668c814c2009fe2a5714c2009fe6a4714c200bee690714c200bf668c714c200bf6aa9314c200ef62a1314c200ef661d314c200ff4245314c200ff45c5314c200afe2a1314c200dfc245314c200bde694314c2009fe2a6114c200bf628e114c200ff44c6114c2009ef692994c2008ff2a1974c2009fb688974c200aef690874c200af768c874c200afe680874c2009df694914c200af768c814c2009fe6a5704c2009fe2a5704c200bf628d704c2009feaa9970c200d7e65e770c200dbe69d960c200dbe9dd960c200dbe685960c200dbe659730c2009feaa9910c200df68cd910c2009fe6a5710c200d7e65d710c200dbe659710c200dfc645710c2009fe6a4710c200dbe658710c200bee690710c200dbe659310c200dbe65a110c200dfc646110c200cfe2a193442009fe69c9344200df664c9344200bde6948344200bfc68483442009fe6a573442009fe2a573442009fe6a47344200bee6907344200bfa6887344200bfc68473442009fe2a63344200df664e3344200afe2a13144200df624d3144200bde6943144200dfc64e1144200dfc24e11442008ff2a193442008ff6a48344200adf6948344200afd68483442009fe6a530442009fe2a53044200df624d3044200bfc2853044200df6aa99304200df669d9304200df629d93042009feaa993042009fe6a57304200dee6517304200df664d73042009fe6a47304200bee6907304200dee6507304200df664c7304200bfa6887304200bfc6847304200d7e65e3304200dde6563304200dee6523304200df664e3304200dfa69d9204200dfa9dd9204200dfa68d9204200dfa5cd9204200dfa1cd9204200dfa8cd9204200d7e65d3104200dbe6593104200dde6553104200dee6513104200df664d3104200dfa6493104200dfc64e11042009fe6849760e009fe69c9160e009feaa99720e009fe6a48720e00bf668c8720e00ddeaa99520e00dde69d9520e00dde29d9520e00dde21d9520e00dde6859520e00dde2859520e00bdeaa99520e00dde65d9520e00cfe65d8320e009feaa99120e00dde6559120e009fe2a2995ce00df668e995ce009fe686995ce009feaa8985ce009fe684985ce00cfe660985ce0 else 0xdfb681921ce00dfd5cd911ce00def651911ce00dfb649911ce00dfe5cd901ce00dfe645901ce009ff69c918ce00bef690918ce00affaa97360600affaa97320600cff5cd9020600cff1cd9020600aff69c8320600bef6907320600bfb68873206009ff69e994c600bef690974c600aff680874c600bef690874c600aff2a2774c600cff262774c600ef79dc834c600bdf694834c6009ff2a5734c600aff2a1734c600cff261734c600bbf698734c600bdf694734c600bef690734c600bfb688734c600bfe680734c6009ff69c980c6009ffaa9970c6009ff68d970c600cff661970c600ddf69d950c600ddf9dd950c600ddf65d950c600cff65d830c600ddf655730c600cff65d810c600ddf655710c600ddf655310c600aff69c8384600cff2617384600cff2607384600bfb6887384600cff26233846009ff69c914c200aff69c814c2009ff69c9344200aff69c8344200bef6907344200bfb6887344200cdfaa99520e00cdf69d9520e00cdf29d9520e00cdf6859520e00cdf2859520e00cdf6819520e00af768c8720e009dfaa99520e00cdf21d9520e00dde6819520e008ff684985ce009fe680915ce008ff2a2991ce009fd286991ce009ef690981ce009fb688981ce009fd684981ce009efaa9941ce00cef6a1941ce00dee681941ce00cef661941ce00dcf655941ce00cdf655831ce00cef651831ce00dd7655731ce009fbaa9921ce00cfb6a1921ce00cfb61d921ce00cfb60d921ce00d7b5cd921ce00dfa681921ce00cfb661921ce00dbb659921ce00ddb655921ce00deb651921ce009fdaa9911ce00cfd6a1911ce00cfd2a1911ce00cfd60d911ce00dfc681911ce00dfc281911ce008ff2a1911ce00cfd661911ce00ded651911ce00df9649911ce00cfe60d901ce00cfe661901ce00dee651901ce00dfa649901ce00dfc645901ce00cef690988ce008ff2a1918ce009ef690918ce009fe680918ce008ff2a1908ce00bfa688908ce008ff2a57360600aef6907360600afb6887360600afd6847360600afe68073606008ffaa993206008ff6a573206008ff6a47320600aef6907320600afb6887320600afd6847320600afe6807320600cf764e3320600adf6948320600cf764c8320600afd68483206008ff2a2994c6009fb68a994c6008ffaa8984c6008ff69c984c6008ff2a1974c6009ef690974c6009fe680974c6008ff2a5874c6008ff6a4874c600aef690874c600afd684874c600cf7a64834c600bf6680834c6009fd2a5714c600ef520d714c600bbe698904c6008ff2a2990c6009df694980c6008ff2a1970c6009ef690970c6009fb688970c6009fe680970c6008ff6a4870c600c7f65c870c600aef690870c6009dfaa9950c600cdf6a1950c600cdf2a1950c600cdf61d950c600cdf21d950c600dde681950c600dde28)) else (if i < 6 then (if i < 5 then 0x78c0b3026c05afc0be4af5abc8af12bb1aeacb9aae5ab92ae26b76ada2b5aad14b2fac86b13ac16aff2be2af22bb8ae7ab8ead5ab14ab4aa86a9b2a52a8429eca6d297ca58a92aa4428d8a2d289aa1628169ff27c49eaa7689d6273e9bf26c49a5a68699da62a981a5ec974a5b8962a570955a53c943a4e092ca4a291fa45090623ea8f6a3c08e9a35a8d023308caa31a8b622be89f226c894a23888a2218884a20287ca1d887221b886a218e85fa178857a14484aa11083da0f083820da832a0c482d20a4822a07a818205a812a03a80d2024805200e7fd1fe47f51fc47ea9f727ce9ef87b51ea67a09e5e78e9e207869e0a7811df47791dd47711db476b9d947611d6a7569d4a74e9d2a7441d0073e9cea7369cd47311cb471f1c6c7171c4c70f1c227049bf86fa1be26f49bb86ec9b986d31b146bc1acc6af1ab66ac1aa06a41a8069c1a606941a406899a1668199f667999d667199b66699996661997665999566519936647190263a18ce62d189a625188461a985a612983a60a981a60017f05f817d05f017b05ea979a5e2977a5dd17645d517445cf972e5ca17225c4970c5bf16ec5b716cc5af16a25a2168259c9662592162e585160457d15e457515c456d159a562957a55815505501530548151054294fa53d14ee53a14e253714d653414ca52e94aa526948a51e9460516944a511143450b941e506140850093f24fb13e64f813da4f513ce4f213c24ec93a24e493824dc93624d493424ca13224c7130c4bf12ec4b712cc4af129849f926e497924e492124248c9222487120c47f11f647991e047191b64671196461917645991604541140449910c43c90ce43210c242c90a2422108241f107641c106a416904040c102a409100a3fc0fd63ef0fa23e70f963e40f763d98f563d40f403cc0f2a3c90f143c10ee03b40eca3ae8eaa3a68e8a39e8e6a3968e4a38e8e3438b8e1e3838dfe37b8dd436e8daa3668d8a35e8d6a3590d4a34e8d343490d0a3410cfe33e0cf23360cd23330cc63300cb032a8ca43278c8e3220c8231f0c4e3120c3830c8c2c3070c162fa0be22f70bd62f18bc02ee8bb42e90b9e2e60b922e08b722d88b482ce0b282c60b082c08af22b88ad22b08ab22ab0aa62a58a902a28a7a29d0a642950a4428f8a3828c8a222848a0c2818a0027e89e027689d427109be26b89a8268899c25e092c24208e423288a6220885420c080c1fa07c41e807721d107161ba06ba1a5866818e860c17a05ba163055e14c050213504a611e044a10984020f503b00e0835e0ce830c0b782b00a58272091022007c81ce0680172053812a04180e202f809001b003e00680009ffaa99720e00ddf69d9520e00ddf65d9520e00aff684985ce00bdf694835ce00aff2a1915ce00cff261915ce00def651731ce00dfb5cd921ce00dfb685921ce else 0xc38005011c38001020800180018021800140014001400112d008b00850085008700870085000500050005000600060006000600060086000500b1c2402c70900b1c2402c70900b1c231d000808001800630a0b06000600860b060b060b3662402182c10141164102c100030405040184000c1004100c10080040800b040004100c16001e1c16001a02c70a80b1c281000787058012c2601e308c76002a1c1a1c1600100c160010181601c70b870403040112c210a160010181e1c161c100d0040000000000001604010403064b0401840318c200800402a8103870602021008084000000002000010402048204c70600050007000700044bc002820402180a180018001800180014086311c34084b0b0207020502060016305470400061e1c1000304011c030801040618c2008004038401040ef01200120347080311c22ab47084b00f470e003870402048011c20000000005040bd1c20081800203470b87d1c2e1f470b87d1c251d870a000058d47084b848004020011dc1000018112c18086311c38081000104020602040106020405040584058559060020205800405060206023662601e308058602045905800402040a02c70902040a00100ae30a08000002b1c20000002021800008004000038cd9340c792010a182078c181e3765d071e400001e306000071c1800800404010602040211c2808131c12001014101020480070207020502060015906001e306040a1540138c1020008004c704082000e331c2800b1c102c7040820efe158363047beef030efc1d03a7efe1113631dfbd1ce3ef4688a1a847bc8d1a4444d8fbf86a11ef2486a111a23469111a23469111a2386bbc1de3effbdef231dc551cc4d9055194731344154771cc4d90771547313641dc551cc4d93bfef8578c551dc731364154771cc4d9073ef7bc1de4effbe15e3effbe1544d90771547313641dc551cc4d9077154731364154771cc4d93bfefbbdef241dc551cc4d90551dc7313641dc551cc4d93bfefbbc8fbfefbbc8c11effbeef24efc551363efc9a2444d93be1544d8fbf1544d8c55effbe1364137bfef85593bfef8551364ef8688bbf8444d8cc7effbeef641dfbc1ce31dc551cc4d9055134658c551cc4d1944154731346513bfef7bc8fbfef7bc8fbf1544d8c9a244688fbfef7bc8fbf26bbc2464effbeef63effbeef7bc13be1544d8fbd1a22f17bc44f0abc10efdbbdcef0bba8ee3bb74ed6bb40ec9bb0cebcbad8eafbaa4ea2ba70e95ba32e863a08e7e39dee6eb982e57b93ae483910e3b38d2e29388ae19b842e07b7fadf5b7bcde8b788ddbb754dceb720dbf36e2db236a4da03666d933628d8635fed7935b6d673582d5a354ed4334cad24b45ad0b33f4cf1b3b6cdfb364cd2b33acc83306cbb32d2cae32a8c97324cc7db1bec5cb126c483110c3130) else (if i < 7 then 0x1081603c20000508040142000050806004200404080400c018c060042c001c001000010821ef00f0c0f26747018051600d1c050c03007478c060042014180347014300005080300480d1c4408010b00d1c0f0f00d1c0f0f00d1c0f0d47c000f0d00d1c050c000042000010800004200005098007426000509800142002872a83a000508000142a02e30143a02c701430080308040042010030063c0210100108000142058a3d400110000042004040b02c002c0b00082c78dd00160d06c6741c701500efc2e1bbf3660d8541d9615efc358341d142eefe0d05040b1e371d1101450e61a84405910007bf06d110bc059500740200c05080104160502010050a800042a00010a80004260010a81168d99608576007e1c12402a68d9902d8760980201e0aba303c1614990aaa3a4282a1e801c900aaa3a6682a1e801c060010a9a3665906080b600721d996400b609a360070a9a366590608876007028704870a9a36659002d826008e643703c16101e0aba303c16142ae8f9903c161580042a68d996400b61d801c0f01820a9a36659061c0618030580840b004060c2a68d996400b61c061c2ae8f9903c16142ae8f9903c16140b0a9a3665906098720080a9a36659002d8261c80202ae8f9903c16142ae8f9903c16142ae8f9903c161401038200406080501020041004168880042900d1a4442f142ac8f19c1c15c0060ab23c671003700182ac8f19c430702f001d00014203c0a88190400c01c23028602c0f01830bb25087be03e50bb25efbbd03e540806082ec940f06c14160041c20bbbf03e1106c509c01028300406082b09c1b0500402a60b7a3e6790c2c0a180600420641000023028500406082ae8f0be1f020846004103c0608230641001c000306d8f470c0210c8502c27d1c0a10800480042ae8f99e400be1c061d0b09c0a0c800202004040a8000420a41b0bc141005010201404080101020a41d0bc1410290742f05242dc1d0bc1491800426074160c2e0a41e05046400b61da307050a41d0bc14920205803662600050899aaaa3a4002a1e801c05a00220010002042a08c1904007010600c04081bd8f50d1c2c014680010040408500042004100c103bd0416045580028001e1c10001803500801060e1f500b87d402543870987d402e1f50080008183bd0408001e1c10045008828400208200050500040018100410082d402208120814001c0001082900d1a4442f1799e410d0e30014150ab63d1e1a050603211014302c1a044051002c00058c00018010e00164500e000042020004080018001800140018001010018c240010910009000500050087008500b1c240010001078704080018001004631645011c501010041e1c161c1000030804055051c200410002055051c2000101820a82306403040070047d8f470b21106c5d8c01 else 0x1090006c200700088220020068008822002b8ec70a800b026002c098003c20358009800b020580f081603c2200)))
def l383xr9 : Packing := (640,4,6,63,0,14,1,p383xr9)
def p383xi9 (i : Nat) : Nat := 0x34442029441a000202bb838d09d40d5944ee4000008586002711b60f518f80a7000080e60000b84184160db7c25a3938557059417a611028b407e253280eb140361b8193783e01ca057a0e8423f84b0001806a8848031d00380448350000f0e40000000184ad10ea86ac29095ba06ca20450640240000a59400000000001e59c0000000c02961e74c0f14370511d0dc38587c92bce1ef03fe084f00a814d80448347285e00c0005843c2c9045f01e3389103e400903750218820000000008424112000000000001440203498cb05870b820cac2d4d41a021c0e404329100716c01a442a026a0e8c164836708bc21c7d248335911809adc29837f83d52c088154a58082a401e1f8000085fc0a2e62880f3a0e00000002501c1696e61e20fc3c493fd067c0aa41f38304408001fc066865405b805649a7850543041da438e700a405a13e400685b71010039397907db077a1dc0001941d024419fcb4111c24fa413101100006036210209d0000f0c3608c80c5189f2be20dc407e72580c178040c0421efe7fe1ac013a07530338124409d820508a0001221385d409000010c580629416c46400018090001681c000000080a940b9c452069e42c415bc0b680ac2ba8c63c129c13d05e0000000486832a7a02d8319017f088e11ab9e8208141591634812121418d0a082052614282543c18002c00030a09300000020a0224999064402b0018004980c08136040050208387003810200103a5560030f
def p383xr10 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0xcc9a21007fe24d10803ff10688401ff97344200ffc39a21007fe8cd10803ff10288401ff93144200ffc18a21005ffa6510802ffb26884017fc9344200dfe41a21007fd84510803ff26088401ff97304200ffc39821007fe8cc10803ff26208401ff99720e00ffc43907007fe64483803ff532b9c01ff9985ce00ffc4c2e7007fe60d73803ff106b9c01ff9915ce00ffc48ae7007fe66073803ff30639c01ff9731ce00ffcc88e7007fe26233803ff12f19c01ff9878ce00ffc43c67007fe9de33803ff30719c01ff9738ce00ffc48c67007fe5cd81803ff0e6c0c01ffa3360600ffcc9903007fe20c81803ff2e640c01ff87320600ffd19903007fea6531803ff33098c01ff8984c600ffccba63007fe25d31803ff30e98c01ff8874c600ffd3ba63007fe60d31803ff10698c01ff9734c600ffc39a63007fe8cd31803ff30298c01ff8814c600ffcb8a63007fe66031803ff32e18c01ff9870c600ffc43863007fe9dc31803ff30618c01ff9730c600ffcc0863007fe5c431803ff26218c01ff89884600ffc49c23007fe60e11803ff10708c01ff97384600ffc39c23007fe8ce11803ff30308c01ff931846009fecb907004ff644838027fb2041c0177d9520e00bfcc8107004ff26173802f7b2839c017ed921ce00bfac88e7005fe640738027f93119c013fd93206009fec8103005fe640818027f93098c01bdc834c600bbeca863005fe640318027f93108c017f8984c200bfccba61005fe25d308037f30e98401fda334c200bfc48a61007f64c530802ff32e18401fda330c200bfcc8861005fe26110802ff326884017f89344200ff908a21005fe64c10803fe422084017f89760e00bfc48b07005fea6483802ff32e41c01f799520e00dfcc1907005fe64483802ff532b9c017f8985ce00bfc48ae7005fea64738037f33039c017f8981ce00fdcca0e7007f65cc73803fd32439c017f9911ce00ff8c88e7007f666233803fb13119c01fd9918ce00fec48c67005fe26233802ff32f19c017f8978ce00fecc1c67007f620e33803fb2e719c01fd8738ce00bfcc8c67005fe24633802ff126c0c01fda3360600bfd4c903005fe64c81803fb46640c01bf98120600bfd4ca63005fe26131802ff32e98c017f8974c600efd3ba63007f620d31803fb46698c01ff1714c600bfd4c863005fe26031802ff32e18c017f8970c600efd3b863007de65431803fb46618c01fd9310c600ff898863007fc66211803fe13108c01ff18384600ff841c23007fc5ce11803fe0e708c01ff23384600bfc4c423005fe64e11802ff12708c01fda3384600ff8c0c23007fc20611803fe26308c01ff031846009beca907005be65830802f7328084017d99304200bf4c9021005de654838027f33039c017b9941ce00bf4c90e7005fc64473802ef32a18c01fd23384600 else 0x4483114c4110fcc39f0c5429d08941f507141a7062415904a410b036c0bd01ec039006bfeaff33f8afdb3f4efc7bf00fb8beb2fa53e52f843dcef67bd6ef543d32f40bcd2f28bc72f10bc00eefbb7cecebb1cebb3aceea33a4ae8239c6e65b966e4db8f4e313894e14b834e05b7d4de93762dccb714dbdb6c6da5b666d923606d713594d54b510d3cb4b0d053378cb73264c7b312cc242fe2bcd2e74b68ad2ab282c28ad5aabaa832970a2328389f4a76c9bd267c98a259e949a4d2916a4188eca34c8b5225c886a1c686120fa81c200a7ed9f2c7a41e187711d167309c6e7069bc66dc9ae86a51a40672197463f184e5fa17825cb96da59415ea5611530537148850413864c392cc48c11b845490ec41d0ffc3dc8efa3a50e4036d8d503360c9630c0bee2e68b102a60a44273095423708641ed87621bf068418c05ee159051012f04440f783780c902ac08d01bc05100cc0150001ffd9720e00fff4cae7007ff26173803ff906b9c01ffd915ce00ffe48ae7007ff64173803ffae639c01ffd911ce00ffe48c67007ff5cc81803ff8e640c01ffe3320600ffe4ba63007ff21d31803ffcee98c01ffc834c600ffeb9a63007ff1cd31803ffb2e18c01ffe770c600ffeb9863007ff5c431803ffa6218c01ffd7384600ffe39c23007ff8ce11803ffcee98401ffd734c200ffeb8a61007ff4c530803ffae688401ffc7344200fff19a21005ff65c838037f90e41c01f7d9520e00bfec8907005ffa65738037fb30b9c017fc985ce00dfe4c2e7006ff60d73802ff922b9c01ff9905ce00ffc482e7005ffa64738037fb3039c017fc981ce00fdeca0e7006ff60c73803fbae639c01fed921ce00bfec88e7007fd64473802ffb2039c01ff9901ce00bfec8c67005ff24633802ffb2119c01ff8908ce00dfeb9b03006ff1cd818037fc66c0c01bfd7320600dfe39903006ff8cc81802ffb2640c01bfc8320600bff4ca63006ff66131802ff93098c01bfc984c600bfecba63005ff25d318037fb0e98c01bfc874c600dfec1a63007f720d318037fb0298c01ff5714c600ffcc8263007fe24131802ffd3218c01bfd980c600bfe4c063005ff65c31802ff92e18c01bfd870c600dfe43863007df654318037fb0618c01bfd810c600fee98863007fd4c431802ffb2018c01ff9900c600dfec1c23006ff20e11802ffb2108c01ff89084600ffd4ca61007fe65d30803ff12e98401ff8874c200ffd3ba61007fe20d30803ff2e698401ff8734c200ffcc8a61007fe24530803ff10298401ff9714c200ffc38a61007fe4c530803ff06298401ffa114c200bff4ca61005ff65d30802ff92e98401bfc874c200fef19a61005ff245308037f90298401fdd314c200ffcb8261007fe9dc30803ff2e618401ff9710c200ffc38861007fe4c430803ff42218401ffa9944200ff) else (if i < 3 then 0xfbc109e8af42f06816deefb7f9f3d15e91a05b7fbedeef0f4272bd24200200d5bdde6fb7e1d2bd4001500901bcde95f7fbe18052b156fb7b1f190a261502c02040d0445139a897bf0d6f02330a8040b0001b7801dfefb7a0fac1e0002eff7c150303685f0737bbc02efcae1334526a258037dbfde90b794000540b020077dbd01eff78684fd9bf0d0449b210b7fbcdeefa53bef401bc39ca6a05ef37e1a08cd0025eff7dbcdecdbede800d1202c85bfdf0037bbc9c844bdf86b78119b7f1a8893643512f7e1ade04660d044d119ab7fbede6f65dfef8aa0026cb00216ff7dbdde4c6a216fc35bc08cd1a889a23de068227790341134466a8010b7e4ddf15670010897bfdeefb793afa01bf269565df868224d90006a25efb7fbdde4e00259a885bddfefb79410801bfde6f77d30037dbd3448632c9408e423b954e64da4ee553993643b954e64d90aa77399364deef0ee73909a77399564001a897bfdf6f77939dcaa7326c89adfa449b220097bfdf6f37b36f8abbf26c88025eff7dbdde4c003512c85bf406fb79bda48455dfef89b2800efbdde1ce5dfa6b7891937fbe2a93644012cd5bfdf6f7793a037fbe2a9365356f8abbf26ca00df6f4d126fc341126c9bf8d6f22321a89700df6f4d13000d442df6ff7bbc9c9700dfef37dbd9834113446003510897bedfef77941a801bfdf6f37b30037dbddfef25001df7bbc39ca6a806fb7fbdde4c00216ff7dbdde4d002590b7dbfdeef273512f7dbddfef26351577c4d32cbbe2a934cb20009642df6ff7bbc9c005539934cb29aa01bfdf6f77931549a658e01bfdf1549b2efb7a688f7fbe2a936471b65a0c74d244d13a0085bfdf6f77936fd35bc48c842406ff79bedecc42406f77fbede4c42406ff7dbdde4c42406ff7dbdde4c003512c8480dfef37dbda4d5bede9a24006f8abbf26ca4b806ff7dbdde4dbf4d6f12326fb7a688d004225efb7bbfde4e80df6f4d124002bbf06c8bf126f0344d08cdbfde044d01a977fbc0d1a0232efc346808c8bedeef201bf2bcc6a25efc35bc08ccbddfefb787a2bccbcdfefb7a7a2bcdbfdf6f7787a2bccbe25eff79bd344dbfdf6f779277c5ddc7753dc8f6cfd9ef615d74f591d4f74fbd2e7477d08f3cfce3734bcbdf2a3c9871fbc69f141c36f099c15f015bebef5bbb8ee7db8a6dc3b5bece5b1b6c19af5eae1a9169dfa59e8a7a0be7ed9f3e6eb99ce60d969e51d94464bd90863bb8de6313887619383de0d9813dfd77c15e7b780dd6772e5c416e4db096b65a73668590560cd7a95b1567156c553954254d950653b34d3528d485518b44dd0e341ad0053f9cfdb3e64f7b3b34e433804de33684d713504cff32f4c7b30e4bf72f1cb972d54b252b44a7d2934a0b26dc93f231c861207c7b91d046ed1aac67b197462d183c5df16bc56d14ac50d13744d1128 else (if i < 4 then 0x65800180b1c000c058e000602c61685d40030014020ba8400485b8ea01603014605d418e05800a04810060020120406800065024080300100c42166fe35bc88ce0bdf868222f02cdbf26c440b20000a068c962b35018840c008b37fbedeef0016a8d0e820278fb2800c11bfde269220594180118eff7c2f9947634cd650e82020a9001828001c099940a099b0ed96846800747992811c840f001a8c6592685ac4101934774893663ba689a9102ca4d3b83ce616945482036fd349126cf01dc1e730b48003578fb3d025f1c0d403cee4d3985a5058042c1934ee0f3985a5350b34659cc9432047c3800c64b035a000e01826650282673518ca047211650001a017080c842cdfc6b79119c062adfef234169a54e391c6600c783908680b0b562b0080019bedeca27170064bbede83e6058e05c00df6f64a0fa0d42d0791fb3d00009c1548085dbf0d0441f30b443902142c4fbe0002a943f8fb3d0040b41438040d102c4fbc0782a55518cb3992864216470009c1558004390de0181e771a50003528d3359485428e0b1382aba38016e06182cc653a8ec699aca42a087a3808002d051827000141522a93290a851c6800058284e52ab33908589c1533437912001111a8c6500311c845900014095195349102826532a69220104ca061592c73be006ff7bbc02d4000e04cca0504cc2b51899340b4882675b8745e149026650282645521c4c9a48826632a69220504ca028400101002180a15528d32904021c0406025202160a6c61d468527400040d180a1258037b1b677b10037b1002a06a8f0f50354601a800230061ea118030f508d8fbd8801bd8801502146e3a844420020aa12002a0c705c882a84482a810a325c00021690c6472146a2201980c38de468ee169834055b84461282ea0000e340532c441328e0181a08aa003302c000602881a0881633540228042e38045008600c78885008884010006016831e302420025c5012c01112e1008002000098f180a121400020410d4632c9408e01034e2c13468171104cc2cdf868228d02cc020004006845008601092e0114018f112e125802225c387259a834038d8f18b2163a02205c38771b1e341424b858e808b0f092e14012e225c2e325a023352a8971e1cd44b8d8e4b88d44b08970c02125c02225c0226390822100222140a22100205190a044b8c844bde4680638223de42e3de45bc85c74740466a5551e3c3d1cd51b1e8e808c17478b0f478b0f4788854725874740454721040271d1e32142428484e340464202c442811aa34031e28142808404e38804c789004208850b1c84808c0a4b21470221444b8110a38112c85190a125b1c84180a002b166fc2bbe06d02a01c037dbf0a8141b40a8042d02efc340d08d0be258777fbc88cc6a216fc35bc08cc0b1500801bcdeeff7c2f0a54340b6fb7 else 0x180444b35030582200100a02240019c6c79100820201441620002d9680a80800b23030581f1a01040525c80600c0038001803181803000c5bbc0303e40051c0a06920147034601a3a0238002e8e069201470303e4400080b19a901008101654001601029101000138c0b2a0200026381)))
def l383xr10 : Packing := (333,3,6,63,0,14,1,p383xr10)
def p383xi10 (i : Nat) : Nat := (if i < 1 then 0xc00d416af044803ad41a2c0e4e09e218c6b8a4c454b08eaf4424217a868c1004024bc99be234f05c30481b07a0a0220a7628331063c647f0c9f04b202a385668c4980000000110fb7014c9556443ca15352d15079983cb886cd42c88947840ca00a000058203b826801e52ac880880000816388fbd82b46208c5c500002892840a1465a70a941318c4fd60fff42e188af402d616b002d173d80000e0b6a050009cf0cbb84c5000000000000165480000709f5823f422c5084796c4000060f40000589380891823e126ed0428000040334046600e1838d8141612fb0956c227019c30a8685840000e0d6d8b0520f2c0bf606bae7c002aa08ce41b840585f9bd41c2e13862210104a83b4000000003867542dba1d440ca7f56341b380edd2bbe179300c800009313b02bd83a5e8776054106c958e8a045b0710f5f7ccbca130a02bd86b1cac1a610a134015e042d20000a067390c40000e564b086000024022625a20ae80000000160b93090f04a8c1d105b3613fa837c84f041c81a606063883e7623530ffe880982dc022582b1f06d6829f7d1340a3583cbb143622e31027061ccb439c3cde70681d0c29bf1d0204e2883d443f414c90d492003846d21e3903340855014d0185502e000000000a14bb12c201bc00016065cb30786428334026218af084ff000fa0fe00003e950c110a1c508be089adc01da1b120133832000010004f2417888401760000200d4966c0000000000d180000c42ca4ba70f080003c04fe0b2507ec18dd4b00e0cbe8dc016cbc2dea1b94e03d83e4000000000000000013ac3602b0000603f34252a058f058800030ab5c217d04794465148e00000000406d203a0826400def0764c3440000d0f480000908f611c00000060400014417302580002637424a9a0ec685fd03ea24747010107068081a20b48ba892a8c02940902024d84924c1ee27410aaf8913823301fd24d4700b58b7d0441c2386865fc4b7243210d78000203740000f12b800000000e19500001f1500001658ca07980002410a0168400081800009292064800b10002000c080840200002044820102384a2562848204110810c40c958800041046c88506358120a016a8041000010cc90000700872802d82043c00966149801e6c1895c2cb87186c90012041810220203126c2804ca008a3614080001c090003800f34042d202001ae08040830a000830a085140e0c581384020c060550000000035c2c2040e006801220003020c28114080000030008000c103800938400086270834900031c70072041053c285040208087060010c0c9c120000050704988842060e0708380910c101972a1c2bb38041012800a010e254c50420021060428450000002a086162204007080843300004170218081040812400141000b0800a020089e324108074300017214081 else (if i < 2 then 0x8b09074d4a0c0226c093196b1825f6242504b902ff0350f89be4fab02b2c06b451b5011d80b8818b8556208d7064743b700a9100be12e74aeae5e330298000082ed84567400b035543d7483e6034404e648ff40d30000608b484dba032f270504f54290c17aa2abf80c7f96ae0a13038573d342c1666360c0217bb0c0de1edc29668259c0857cfa427200001c2642123503fc9329c032849eb2784908f007a6613e0ab6148803cea1891060f0275c0c286293107703e3818e20f65439c849dc1cc81ad009a60758c132e115101b582d4006962080236c8040482d6103725658093c012283fd0e610417c99920ab029341586427780f50e7ae038f0ba26403000000000782d60dec0cc898ac0462207e102f7f04a431710fd9f37063ec021281e2903000002eb896122900580001025105c3b0b9487be409e7c3f9c43505727822a25eb06d909e5cacb1c51704c782ea807d2252e3399a16ac41922207e4620814003720e7f119905a102b4627ba0db788270360c51a032da07e9c4d8a862306c518c2447a0000e43b0015488985e0b0000000008cc80000b12a292ee8225c45a500ef041241b86228f087a81dc4002a1981048d8696827d40c6f00fd80e6720865050271987d20cd12c31f066e026e8116f1d1d13b309c88c8c4237b224b01c7049330e06129d85f90031e17da0c17086b480d4241602cb17b4ca98067860b8897fc807e004700abc181544de803a12ef9698572b90528013394683c4452619b10c3856f013ef853f87cd72c502f9111601373f18ac094402f000020804c3bce1f1f031d02058908000000000000203f6e85800004080fc01fe142f0e2583114087e26610e12195f4c404000d0f2409dc034ec84400af981774423e08a90ff00003839e01dd9255981e390c7e24dd0a2e17bc0000a0441078d81a881920000e0f6000011087206de0263c15a494c00003076619123af946720000000000000000080bab07e284e000004c20f87a27abc0000f072c086641444e47f42141719826328720000715a6909dda60910a5116408596475faccf06fac2f7c03012334841d03b84079625c5850000000000443ca01594042c1bce0ebca00d83ee1254400430033410c8667a041383817a2541654037677d503062015000018872c38762690f05780a101a560ae4105392c80001e14ac0d7619de848e8046c138e97f809da01c0208c7820e8288c238303d800000c73a1fc401e6824c425c00007046b830800003cc20000084404179655c000000000814780eeb043e713e402640be64c56046c0001e03bb225914e9c3aba09480e6987d80001006970b3a13f243c000001088800000000624ca0310000181df426a108a2909b4b7e01ce000059054a229040b127d506fd232712083095b09ebc4f80000f0d04c056c97a3d0990d53035d else 0x2147e236307c3a1c2224388849f15c0000c4f8c039e01508a5ce186d29fb881e8449c00d807d41705821d812d12a8a06ee4308a22740d3702d000001cfd611cd071c0000052a213a808ec0001423af0d2507c920dff597b0c6f87e4000141ca60c4088a502e80037320ed0144c9bf604e111fb874484554072d2124830d60294263000000002c26ce1438122e0008814944213c638915443420000806ec027b84606158b06000002833c0000000000001020400008320a0649c090a06c004a987b8016f417880c50857984b9d07302bfe009644470869c08f6859b20d9a0cfb00e6098560a6210d710df819f88e2dca9a10e98351c025a5681042000000000223268af8000380b7618f0000283a80ae4c1b7e428480ab8c25209ad125fe3200001e86db2dd8090378ab117db33178725032da076c839000000001e0d03205000034bd200000000784cc0000843d00001836900a40000a0028000083d40000d03d10329b138c9a7e128000038479306e3052800008366f8f97265800028082b0a1b123672c942e00000000000003c11c016c107d90407019961640000501374424819f503eb94c3c9e3e11754c4b9852eb87e4621311214c7c8cbe41cd312481d40001a159aa4e5045838a0c17330aa7187bc006d06d643a494e45009e49c7e88ea1190357fc56e108209678166ec0343200742b90c2a4adf09bb095a42ee6106c0a49058b383578c0a0c618835049e2265d214600b1414f0860403e4631943be20bd612ef884d8856e0f0e07bf872c826be179113010400424b213ad117a89234336e0e9b))
def p383xr11 (i : Nat) : Nat := 0x16f2fc69344662a0b00bebdbfbc9fa02c59a802f6f2fafcd15ea0b0016bdbebcbf579fa41afef069a04660b0200bcbebfbd0aa008012efef016faf67da2a02000605bebdbfbc689fa82c5816fef068467020604bfbc1a119ca80afc6af046600bf0dbe1594a82c6afef0466bebd1f28902efaf6fef07e64bbf1abc11940afaf6fef07e6bfbc1a681196fc6af046400bcbdbfbe579802fefaf6f25006abdbcbfbe579c02f6f2fef95e6bf1abc1192fef2faf47da2600bebfbdbc94012efef2faf5a2700bfbcbebd689afefaf6f24bfbebdbc932f618b855d29f4f8945132073d0734db19b3105b4ab13b2484447b0df180294490770c010413013000ffc83803ff5ce00ffc73803ff8ce00ffc81803ff4c600ffc31803ff84600ffd30803ff44200bfd83802ff20e00bfd81802ff20600ff930803fe0c200ff910803fe04200ff983803fe20e00ff973803fe1ce00ffa33803fe60600ff881803fe4c600ff831803fe84600fda33803fc84600
def l383xr11 : Packing := (30,2,6,63,0,11,1,p383xr11)
def p383xi11 (i : Nat) : Nat := (if i < 1 then 0x20b3813a88955ccacc435811b4096c2cea04283d383c480884134839f84ed0016fcaf8d02c3a404e4ccc883c3c2c9032681250117e35fc25f00700c898909833cd2fa0511cb2d01db8b92045ecafec203028049fd08c6c11d048a8258881cb8ee030b03ac000024480000c393033413a400034b354b2440ca043ec46441498250c41c0837c19cc05c000200800001842f4a13c4148418030500cd44468495c822cb4582904cf7c3ce802dc2fec35552e844634b6c8026d03641e2b895026682874ba804db8271488bc23c41b2c4e942120c20446b02dc0003c10f4c68c18c0cbcc0c683b3431283fbfc4a4206011141648342018644838b8d1baacab9489e829a00db41fc4aed8cedc3bb81f3048d443b050cc9e9c1e981df44f8c3d9c297c2bbf8e2c28e43e18830c27ac1d6b8cc00ec0172852ccb860424832300e60aa6cb62031cccea4527d0bfc01044c042618144caf181c960e1536041a404a04158d032c51e034b82a1c1ad323c0ab7425444758b74b840c052820d78d14019cce1c45942c2830ed0480003b8e702a5439705028198000089b684fc8031817fcae4b876c87cca68000209e48c6c0000c0f10a6e047c0826821e41bbc949c8d4c478445120e4c04c4904407ee0d0480fcaf70b16ab8f423641568a8e01600274c9a0000384a9c2bdc0fac039436a0484838f0cde005a88b441abc8400b8044c8c318213800028c00cc65c17643bc0001c4984129014dc07664ad0219012300ebc1ecf8d40003c44148480001cc28c12c0003418b03e944ac000000014057844800008862e0c3406640e35b6143d648c2c2b204dd40400003c3dc000178f000000000000000b5806340480000000340d4000304f44508837811effa7e803e11d10150444d84d000000002019409fa60d5fa2908d00000000284b400008bdc8068000388b88023d86302a84405851b42280002828802d680d34adb4329e0f2833b4371d06243f500458c34000143feccc4bc4c02d1c4b200a54a4280a38b31c85ec0dc000240900bcd250301f4c35a4208426d6443046fc0c3434c00000000000301b6250e408d44710216c5168a0e6434db240388c4ce81d220b5c9dac0f5422385048a5fc0bc823081c3ca83029f880000000001007811d80cc00000c190c9ec00018403010383000002cb0880a800000003f9d80000000320ec00000000000243a80000c001042109f0200380040421b200801e4c24a8700b049226284a73a0898b4b701811804009080828000cc300000000940f41816c001801028d3f000071912142817c04484089410e1c2011a007c0b710042000008c05060508d0a240041e31201660028f922c1910024aa9047001418040a308f800b0a7429c00589080e019181a54d310018082004c6801c247080044000121c049263c1001c280000154003 else 0x380b2c24580add3a30347c238836f0a9393270d2511e142f401a34c6303ef810b505fc2fa401f72090a3d000f42ee44f20139bd0d010444b851df84c5cad78178a00000030c04c224c5280a7349b000000002f288000103314b19ba97822f0a23e34cfb0b445503840bf6035c0000000002e8c1f84b1c49d0cb73449c00005baf2297fa81c84400000000eb380002630b03a000000002035210458085642981cd416b409a806f836501e402424a31c5224975a2d9042bc27d8007c268cb5181c462880000000002f004a643b54b00000382adc376c0bac16e53af0362c15f42c702b589530cd802e600356281485004930398c133ca028a0a80fdc09c000203143ada8009ca47c13ec4126cc4585da4c8000244bc00014811f8c84cfbc2e282d9840841beca27424ae44c8bd2802a832c03cb0531490d43e543f18bc3c37e8c27e446c24e04d6443144e18a2c4381040c41420bae418)
def p383xr12 (i : Nat) : Nat := 0xf9ebf787e57ef9ebc92203ff007fa00
def l383xr12 : Packing := (2,1,6,63,0,6,1,p383xr12)
def p383xi12 (i : Nat) : Nat := 0x61144241b00b424a1d000604b1c90fb0e413206f3d10942f32e937e19d0d317f16287118b3a0000e7a0840541a402a0000000000031252af38907000f23d0c903932801000f2b000810f3500000000a33312781452131578ba0500600b81f06421
def l383x : Nat → Packing
  | 8 => l383xr8
  | 9 => l383xr9
  | 10 => l383xr10
  | 11 => l383xr11
  | 12 => l383xr12
  | _ => emptyPacking
def i383x : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 73 253 7 15 8 3 p383xi9
  | 10 => lookupWord 323 1104 7 17 10 3 p383xi10
  | 11 => lookupWord 178 605 7 16 9 3 p383xi11
  | 12 => lookupWord 16 58 5 12 5 3 p383xi12
  | _ => fun _ => none
def g3853 : Forest := ⟨383,13,g383.samples,.fork 59 g383columns (.leaf [(0,0,383,0,13)]),g383autos,l383x,i383x,extraFactory3853,extraFactorySound3853⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geog3853 : graphValid g3853 (boundsBefore known383) = true := by
  unfold graphValid
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel, by decide +kernel⟩, ?_⟩, by decide +kernel⟩
  apply listPieces_all (d:=3)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ckb_8_0 : block g3853 8 0 64 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ckb_8_64 : block g3853 8 64 64 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ckb_8_128 : block g3853 8 128 9 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ckb_8_137 : block g3853 8 137 3 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem lkb_8 : block g3853 8 0 140 = true := (@block_merge g3853 8 0 137 3 (@block_merge g3853 8 0 128 9 (@block_merge g3853 8 0 64 64 ckb_8_0 ckb_8_64) ckb_8_128) ckb_8_137)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ckb_9_0 : block g3853 9 0 60 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ckb_9_60 : block g3853 9 60 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ckb_9_124 : block g3853 9 124 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ckb_9_188 : block g3853 9 188 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ckb_9_252 : block g3853 9 252 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ckb_9_316 : block g3853 9 316 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ckb_9_380 : block g3853 9 380 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ckb_9_444 : block g3853 9 444 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ckb_9_508 : block g3853 9 508 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ckb_9_572 : block g3853 9 572 4 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ckb_9_576 : block g3853 9 576 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem lkb_9 : block g3853 9 0 640 = true := (@block_merge g3853 9 0 576 64 (@block_merge g3853 9 0 572 4 (@block_merge g3853 9 0 508 64 (@block_merge g3853 9 0 444 64 (@block_merge g3853 9 0 380 64 (@block_merge g3853 9 0 316 64 (@block_merge g3853 9 0 252 64 (@block_merge g3853 9 0 188 64 (@block_merge g3853 9 0 124 64 (@block_merge g3853 9 0 60 64 ckb_9_0 ckb_9_60) ckb_9_124) ckb_9_188) ckb_9_252) ckb_9_316) ckb_9_380) ckb_9_444) ckb_9_508) ckb_9_572) ckb_9_576)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ckb_10_0 : block g3853 10 0 12 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ckb_10_12 : block g3853 10 12 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ckb_10_76 : block g3853 10 76 40 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ckb_10_116 : block g3853 10 116 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ckb_10_180 : block g3853 10 180 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ckb_10_244 : block g3853 10 244 55 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ckb_10_299 : block g3853 10 299 34 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem lkb_10 : block g3853 10 0 333 = true := (@block_merge g3853 10 0 299 34 (@block_merge g3853 10 0 244 55 (@block_merge g3853 10 0 180 64 (@block_merge g3853 10 0 116 64 (@block_merge g3853 10 0 76 40 (@block_merge g3853 10 0 12 64 ckb_10_0 ckb_10_12) ckb_10_76) ckb_10_116) ckb_10_180) ckb_10_244) ckb_10_299)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ckb_11_0 : block g3853 11 0 2 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ckb_11_2 : block g3853 11 2 18 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ckb_11_20 : block g3853 11 20 10 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem lkb_11 : block g3853 11 0 30 = true := (@block_merge g3853 11 0 20 10 (@block_merge g3853 11 0 2 18 ckb_11_0 ckb_11_2) ckb_11_20)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ckb_12_0 : block g3853 12 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ckb_12_1 : block g3853 12 1 1 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem lkb_12 : block g3853 12 0 2 = true := (@block_merge g3853 12 0 1 1 ckb_12_0 ckb_12_1)
theorem tables3853 : checkedTables g3853 12 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact lkb_8
  · exact lkb_9
  · exact lkb_10
  · exact lkb_11
  · exact lkb_12
theorem required3853 {k t S} (run : Live (graphGoal 383) k t S)
    (sub : ∀ w ∈ S, w ∈ offered3853) : ∀ w ∈ vars 382, w ∈ S := by
  have data : ∀ i ∈ ord3853,
      (bit (absentRow i) (graphGoal 383) != bit (presentRow i) (graphGoal 383)) &&
      (offered3853.all fun w => w == primary3853 i.val ||
        bit (absentRow i) w == bit (presentRow i) w) = true := by decide +kernel
  have ord : vars 382 = ord3853.map (fun i => primary3853 i.val) := by decide +kernel
  intro w hw
  rw [ord] at hw
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hw
  have dat := data i hi
  simp only [Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at dat
  exact raw_required run offered3853 _ sub _ _ dat.1
    (fun u hu hn => (dat.2 u hu).resolve_left hn)

theorem fullLower3853 : Lower offered3853 (graphGoal 383) 13 := by
  intro p bank reach target
  by_contra! bad
  have pro : proper (graphGoal 383) := by unfold proper; decide +kernel
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live pro reach target
  have small : k ≤ 12 := by omega
  have all := required3853 run sub
  have raw : vars 383 = plus3853 :: vars 382 := by decide +kernel
  by_cases negIn : minus3853 ∈ S
  · by_cases posIn : plus3853 ∈ S
    · have eq : S = offered3853.toFinset := by
        ext w
        simp only [List.mem_toFinset]
        refine ⟨sub w, ?_⟩
        rw [offered3853,raw]
        simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
        rintro ((rfl|h)|rfl)
        · exact posIn
        · exact all _ h
        · exact negIn
      rw [eq] at run
      exact root_index (g:=g3853) (before_sound known383 valid383) geog3853
        tables3853 (k:=12) (by decide) (i:=1) (ws:=offered3853) (by decide +kernel) k t small run
    · have eq : S = alt3853.toFinset := by
        ext w
        simp only [alt3853,List.mem_toFinset,List.mem_append,List.mem_singleton]
        constructor
        · intro h
          have d := sub w h
          simp only [offered3853,raw,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at d
          rcases d with (rfl|hv)|rfl
          · exact False.elim (posIn h)
          · exact Or.inl hv
          · exact Or.inr rfl
        · rintro (h|rfl)
          · exact all _ h
          · exact negIn
      rw [eq] at run
      exact root_index (g:=g3853) (before_sound known383 valid383) geog3853
        tables3853 (k:=12) (by decide) (i:=0) (ws:=alt3853) (by decide +kernel) k t small run
  · have sl : Slice (vars 383) (graphGoal 383) one 13 :=
      slice_correct (ms:=[]) (base:=vars 383) (G:=graphGoal 383) (by decide +kernel)
        rfl pro (lower3853 383 13 (by decide +kernel))
    apply useSlice3853 run sl _ (by omega)
    intro w hw
    have rawIn := sub w hw
    simp only [offered3853,List.mem_append,List.mem_singleton] at rawIn
    have mem := rawIn.resolve_right (fun e => negIn (e ▸ hw))
    have hv : (vars 383).all (availableB one (vars 383)) = true := by decide +kernel
    exact List.all_eq_true.mp hv w mem

theorem fourLower3853 : Lower all3853 (graphGoal 495) 13 := by
  intro p bank reach target
  by_contra! bad
  have pro : proper (graphGoal 495) := by unfold proper; decide +kernel
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live pro reach target
  have package : all3853.all (fun w => (bank3853 0).contains w) = true := by decide +kernel
  apply eliminate3853 0 run (by omega)
  intro w hw
  simpa only [List.contains_eq_mem,decide_eq_true_eq] using List.all_eq_true.mp package w (sub w hw)

def public3853 (a b : Fin 9) := inputs ++ [minus3853, bin true (primary3853 a.val) (primary3853 b.val)]
def permSix3853 : List Move := [81,130,118].map swapRows ++ fixRows 64 0

theorem slices3853 (a b : Fin 9) (ha : a=4 ∨ a=6) :
    Slice (public3853 a b) graph (subcube (1 <<< a.val) 0) 13 := by
  rcases ha with rfl|rfl
  · have cert : ∀ b : Fin 9, checkMap (fixRows 16 0) (public3853 4 b) graph all3853 (graphGoal 495)=true := by decide +kernel
    exact slice_correct (cert b) (by decide +kernel) (by unfold proper; decide +kernel) fourLower3853
  · have cert : ∀ b : Fin 9, checkMap permSix3853 (public3853 6 b) graph offered3853 (graphGoal 383)=true := by decide +kernel
    exact slice_correct (cert b) (by decide +kernel) (by unfold proper; decide +kernel) fullLower3853

def legal3853 (a b : Fin 9) := a=4 ∧ b ∈ [1,2,3,6] ∨ a=6 ∧ b ∈ [1,2,3,5,7,8]
def witness3853 (a b : Fin 9) : Nat :=
  if a=4 then (if b=1 then 10 else if b=2 then 5 else if b=3 then 8 else 65)
  else (if b=1 then 2 else if b=2 then 260 else if b=3 then 10 else if b=5 then 34 else if b=7 then 130 else 256)
def wr3853 (a b : Fin 9) : Row := Fin.ofNat 512 (witness3853 a b)
def ws3853 (a b : Fin 9) : Row := Fin.ofNat 512 (witness3853 a b ||| (1 <<< a.val))

theorem end3853 (a b : Fin 9) (hab : legal3853 a b) (C : Circuit)
    (hf : PEqualNP.MetaComplexity.FanInTwo C) (hs : C.size ≤ 13)
    (corr : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0,x a || x b]) = edge x) : False := by
  have vals : ∀ r : Row, (public3853 a b).map (bit r) =
      List.ofFn (sample r) ++ [!(sample r 0),sample r a || sample r b] := by
    intro r
    rw [sampled]
    simp [public3853,minus3853,plus3853,primary3853,bit_neg,bit_bin,sample]
  have eq : (execute C.gates (public3853 a b)).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    change bit r ((execute C.gates (public3853 a b)).getD C.output zero) = bit r graph
    rw [←b_read,execute_bits _ _ _ (fun g hg => (hf g hg).1),vals,edge_table]
    exact corr (sample r)
  have hout := get_rep (execute C.gates (public3853 a b)) C.output
  rw [eq] at hout
  obtain ⟨k,t,S,hk,run,sub⟩ := extract C.gates _ hf graph_proper (hout.resolve_right (fun n => n graph_proper))
  have ha : a=4 ∨ a=6 := hab.imp And.left And.left
  have tests : ∀ a b : Fin 9, legal3853 a b →
      (bit (wr3853 a b) graph != bit (ws3853 a b) graph) &&
      ((public3853 a b).all fun w => w == primary3853 a.val ||
        bit (wr3853 a b) w == bit (ws3853 a b) w) = true := by
    unfold legal3853; decide +kernel
  have dat := tests a b hab
  simp only [Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at dat
  have liveA := raw_required run _ (primary3853 a.val) sub _ _ dat.1
    (fun u hu hn => (dat.2 u hu).resolve_left hn)
  have avail : ∀ a b : Fin 9, (public3853 a b).all
      (availableB (subcube (1 <<< a.val) 0) (public3853 a b)) = true := by decide +kernel
  apply useSlice3853 run (slices3853 a b ha) (fun w hw => List.all_eq_true.mp (avail a b) w (sub w hw))
  have hz : ∀ a : Fin 9, isMaskedConstant (subcube (1 <<< a.val) 0) (primary3853 a.val) = true := by decide +kernel
  have hp : 0 < S.toList.countP (isMaskedConstant (subcube (1 <<< a.val) 0)) :=
    List.countP_pos_iff.mpr ⟨_,by simpa using liveA,hz a⟩
  have := hk.trans hs
  omega

end PEqualNP.Outside.L_meta_3853

theorem PEqualNP.Outside.L_meta_3853 : ∀ (x1 x2 : Fin (9 : ℕ)),   x1 = (4 : Fin (9 : ℕ)) ∧ x2 ∈ [(1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))] ∨ x1 = (6 : Fin (9 : ℕ)) ∧ x2 ∈ [(1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))] →     ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x4 →         x4.size ≤ (13 : ℕ) →           have x7 : (Fin (9 : ℕ) → Bool) → Bool → Bool → Bool := fun (x7 : Fin (9 : ℕ) → Bool) (x8 x9 : Bool) => x4.eval (List.ofFn x7 ++ [x8, x9]);           have x8 : (Fin (9 : ℕ) → Bool) → Bool := fun (x8 : Fin (9 : ℕ) → Bool) => x8 x1 || x8 x2;           (∀ x9 ∈ [x1, x2], ∃ (x11 : Fin (9 : ℕ) → Bool), x11 x9 = Bool.false ∧ x8 x11 = Bool.true ∧ x7 x11 (!x11 (0 : Fin (9 : ℕ))) Bool.false ≠ x7 x11 (!x11 (0 : Fin (9 : ℕ))) Bool.true) → (∃ (x10 : Fin (9 : ℕ) → Bool), x10 (0 : Fin (9 : ℕ)) = Bool.false ∧ x7 x10 Bool.false (x8 x10) ≠ x7 x10 Bool.true (x8 x10)) → ∃ (x11 : Fin (9 : ℕ) → Bool), x7 x11 (!x11 (0 : Fin (9 : ℕ))) (x8 x11) ≠ (x11 (0 : Fin (9 : ℕ)) && x11 (1 : Fin (9 : ℕ)) || x11 (1 : Fin (9 : ℕ)) && x11 (2 : Fin (9 : ℕ)) || x11 (2 : Fin (9 : ℕ)) && x11 (3 : Fin (9 : ℕ)) || x11 (3 : Fin (9 : ℕ)) && x11 (4 : Fin (9 : ℕ)) || x11 (4 : Fin (9 : ℕ)) && x11 (0 : Fin (9 : ℕ)) || x11 (0 : Fin (9 : ℕ)) && x11 (5 : Fin (9 : ℕ)) || x11 (1 : Fin (9 : ℕ)) && x11 (6 : Fin (9 : ℕ)) || x11 (2 : Fin (9 : ℕ)) && x11 (7 : Fin (9 : ℕ)) || x11 (3 : Fin (9 : ℕ)) && x11 (8 : Fin (9 : ℕ)) || x11 (5 : Fin (9 : ℕ)) && x11 (7 : Fin (9 : ℕ)) || x11 (6 : Fin (9 : ℕ)) && x11 (8 : Fin (9 : ℕ)) || x11 (8 : Fin (9 : ℕ)) && x11 (5 : Fin (9 : ℕ))) := by
  intro a b hab C hf hs _ _ _ _
  by_contra! h
  exact PEqualNP.Outside.L_meta_3853.end3853 a b hab C hf hs h
