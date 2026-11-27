import PEqualNP.Defs

-- The switch lower bound and its finite certificate are adapted from JLDC, PR 5691.
-- The final theorem applies that bound to the output of its first circuit.

-- One switch gate realizes both cofactors on nine inputs. Its control is input 4
-- or its complement, according to the forced value. All finite
-- lower bounds below count every gate, including each subsequent negation.
-- The positive graph bounds and restriction checker are adapted from PressF10's L-meta-1667.
namespace PEqualNP.Outside.L_meta_3061_aux

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

lemma live_size {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
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

lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
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

lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
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

lemma gate_rep (w : List Sig) (g : Gate)
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
lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live target k t S)
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

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [bit,bin]

lemma b_read (i) (w : List Sig) (j : Nat) :
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

lemma execute_bits (gs : List Gate) (i) (w : List Sig)
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
def seed : Sig := 0x88888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888

theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl

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
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
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

def supportPairs (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) => (a,0,Fin.ofNat 512 (1 <<< i))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

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
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig :=
  if m=1023 then graphGoal m &&& ~~~seed else graphGoal m
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (vars m) (chartGoal m) (vars free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (vars free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (vars free) (vars q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice (vars m) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  obtain ⟨z,o,q,s,L⟩ := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs s
  change (((properB G && checkMap ms (vars m) (chartGoal m) (vars free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) xs hh.1 p bank hr ha)
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
  let x := fun j => if m.testBit j then v j else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
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

structure Forest where
  mask : Nat
  cap : Nat
  samples : Nat → Bits × Bits
  cols : IndexTree ColumnInfo
  autos : Array (List Nat)
  levels : Nat → Packing
  index : Nat → Nat → Option (Nat × Nat)

def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  let nonedge := dneg (dbin false (ws.getD 0 defaultDecor) (ws.getD 1 defaultDecor))
  if g.mask=1023 then ws.map (fun w => dbin false w nonedge) else ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  have base := raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  intro a ha
  unfold wiresOf at ha
  split at ha
  · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp ha
    exact faithful_bin false (base w hw) (faithful_neg (faithful_bin false
      (faithful_get base 0) (faithful_get base 1)))
  · exact base _ ha

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  if m=1023 then liftGoal m v &&& ~~~(v 0 &&& v 1) else liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  by_cases e : m=1023
  · have u := asRow_bit v i (0 : Fin 9)
    have w := asRow_bit v i (1 : Fin 9)
    have h := bit_liftGoal m v i
    change (inputs.getD 0 zero).getLsbD (asRow v i).val = (v 0).getLsbD i.val at u
    change (inputs.getD 1 zero).getLsbD (asRow v i).val = (v 1).getLsbD i.val at w
    have seedEq : seed = inputs.getD 0 zero &&& inputs.getD 1 zero := by decide +kernel
    simp only [chartGoal,chartSamples,e,ite_true,bit,seedEq,BitVec.getLsbD_and,
      BitVec.getLsbD_not,(asRow v i).isLt,i.isLt,decide_true,Bool.true_and,u,w] at h ⊢
    rw [h]
  · simpa only [chartGoal,chartSamples,e,ite_false] using bit_liftGoal m v i
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
  (g.cols.read idx).bind fun ci =>
    materialize (vars g.mask) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
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
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
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
    have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact linkedSet_sound g _ names (prior (by omega)) h


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
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
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
def g15 : Forest := ⟨15,3,fun j => g15samples[j]?.getD (0,0),g15columns,g15autos,g15levels,g15index⟩
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
def g31 : Forest := ⟨31,6,fun j => g31samples[j]?.getD (0,0),g31columns,g31autos,g31levels,g31index⟩
def g47samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffddffff5cfaafae7dd35b9ce7bbffd6b6b7b7cfbb8d3b7ad85ddf257b56b575,0x2200a042011011800c00803812181c2009c1061c0107200c09440143143444),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeebefed537937fcb8ab173daa7df7f7691aff9776b2b7dcb92a3f3678b2b59,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9149112428688034a38448020d64a21d120601022ea84882b022a624830919),(0x77db9fef67fc77f3ffe6e3dd55f86b6fffcab66472f7c57fb768dabfad4eae,0x820641080010508440806b120004c020121a4ec1002247c020840112806a4),(0x78ebe4ae9ffd0d576de696b3cff805db7d426c00d8ded437ed436ff6f66c92,0x71419416322f057a950700411b6b328381c4110e8d4580325370f22d66812),(0,0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0bf9ebdb2287acd4afec26dbb6d98eabb3768bb508ca4b7f1fdd1c709a3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80f74f1424444852a26637058ca3a012d22680c12e48c8e17411561c608a3b),(0,0),(0,0),(0,0)]
def g47columns : IndexTree ColumnInfo := (.leaf [(8,0,39,0,4)])
def g47autos : Array (List Nat) := #[[],[83,32]]
def g47levels : Nat → Packing
  | _ => emptyPacking
def g47index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g47 : Forest := ⟨47,4,fun j => g47samples[j]?.getD (0,0),g47columns,g47autos,g47levels,g47index⟩
def g55samples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffdf7defdfafbfd3fcebcfdeffcebffefe76de77fed7f1773f95eb2ebeb,0x400028000010005000000400701010180030103060043200102204010904888),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdb7fbfbb9ad3afd94caf0b9db5bbdf7f7d39bfcdadcf77ec9eccd2fb9cf16b5,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2484444214284026a4e002420468a8a43140a00408d944460a4082569431231),(0xeda5e7e7b2fc29de4ffc371dba2bf0775ff12db9b18bb528fedad96afcd3c5e,0x12589919410293410206d0396285445a082c5d2bf0022b20f0895d2048c2c4e),(0,0),(0xf1cd79264efe956afa7a64bb677ab40beba463600362eda36f3357b7d763926,0xe3a8651b1a36a0acc57538a080f6ea703078a0c13c28dc34c91f3868663126),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe05fe74eda341d5872cbf684d5e2ed19e7e3bba5e964550dd792aec724f479,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01fb53db1204342a549861b60b6727a22d48ac0b14da4445855161ae724b471),(0,0),(0,0),(0,0)]
def g55columns : IndexTree ColumnInfo := (.leaf [(16,0,39,0,4)])
def g55autos : Array (List Nat) := #[[],[84]]
def g55levels : Nat → Packing
  | _ => emptyPacking
def g55index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g55 : Forest := ⟨55,4,fun j => g55samples[j]?.getD (0,0),g55columns,g55autos,g55levels,g55index⟩
def g63samples : Array (Bits × Bits) := #[(0xdabffdfdbdf61bfbfc7dcbe34f7f1b17917df75df7edd9eff77b6dbd3dcebed3cfbfaddba50fcabded46bc9b579eb7bd3d92776566ad4ad3debe36d74deb7f9faf189ad76da7dc1a6b4eaf21eb254de4ae1f7451bb34d9456fd18e934db17349,0x4400202400040800310000100084000ac0000102800a1100490002240004b2800a001b4000190000008108000574009200040400000594000190004218c0010840002890800550053044a00410008802d0060013000c004400188120c206208),(0xb6678efeffcbf5a9cad5bfd527a7a5bd74d1314b7915f5b2ffdec2fc5d978f8ab3b44b2b5add5b771711b15ce99bf2b3f5bce975ef94cd59a34e76ab937848a94ef6be6c9579db5905539ea703c87a7d4ae11fe2ae423fade4a3c3299b0724e7,0x499461811a200a55004cf88854029340027a680613c002ec00233c1096d01045025d0203d400243150030b7e4900b00499e023395882049d0206ec00041398010bbb1000b7310ad00cc0858112c8207810e917400e423d0034024309910504e5),(0xbfdd27bedf8fade4776ebf9d185bc5bd76aeffb29711f77d628e86e5fffdff6d1a52bff6da987348e3e147dcecdbcc68d1accc4e7d7d77b9734cfbbcefbc022d72eff5a31a72e32584dd5a72accb1256ede309af577ea6b3ab2be572a2769632,0x20983204990108b1910222a2810c12a8041040402e00006394000908008912a582448429aad10a21a0240190b504314209040621245140c82010e8812042049440841100c0c52080310832a5111106e902488a012c82618908a42202729212),(0x77ddb87389d95f9f7bbe7e8eb89e6e76fbf75ca7fd5bb3758b555b578affe964ae7e7fa493e06d03bebc4fb5cff51e46b2dd5bdbb1eab66f60f7d916b9c6944fd85b6f0fc30a2ae7d2afc9dc369ef80bb1b0b2dd52e9331e786f7a5d38e8c8b4,0x1482478012444200420888514440810c402202189081ecc814422aa4c048408050190921c0450c000a080254044021081134422900082c11250884167012813a48094aca870a3283708e41084282480000c012150640581c30655a55288040a4),(0xdca768aafb78ce8d2db2ec3fbdddfa4ec963339dbac7a8e05eccbf0bb99ddf5febcef6dc7762a4a79d9ad8f70324ba6e724754bded1eed86f695f276b70acbd73dc66e39a88d0cfed920a0ee10b5a4dd5893bba709bff6dc1ece388c561e1ed5,0x210938550593284a984457082a220ca002159526023c0223a02100100d271046aa46f2022bb0201ea5730921b3008e848a002106a7520082d20653c8040064810364a00030c5086c0c2084761035a077101508a009ba22e00b822088521e1c51),(0x77dad76bd4ced656e7ec247a694c9eb5b66dc4de71aac18acebb177a9bac7a62d6f3e3996dd9d62d6ecf7b18557229a30b5ebb1ef46b568a8f3400a7c2d3365caade63d0f2234a24623735bcfaee29c0664eddfc63b2a86915f817ca03dc41fa,0x88252894b2b3256598a758928465236453b27d28c68c4c28a24dcc0d24d500d4a845700845b04bd175706d345a20a0a24d641d897dd822a1d52444cad2629c8e732b305273362844202335b73c8d8150424e93e44a78286995ec17c803dc01f2),(0,0),(0,0),(0,0)]
def g63columns : IndexTree ColumnInfo := (.leaf [(32,0,31,0,7)])
def g63autos : Array (List Nat) := #[[],[50,65]]
def g63levels : Nat → Packing
  | _ => emptyPacking
def g63index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g63 : Forest := ⟨63,7,fun j => g63samples[j]?.getD (0,0),g63columns,g63autos,g63levels,g63index⟩
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
def g111 : Forest := ⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index⟩
def g119samples : Array (Bits × Bits) := #[(0xfab75f3dfbfa3756f92d9ff7baf5ff7dbfebb9b33bef7dcdf77fbffe7bbbf75546cedccfd6f7eb762bef3ffdd2ede7abbef7e4e4b775eb9be6ab6f4d5fde77f2b955ece57b3feb97c6d99b5cdd2fdd2ea315de5f3efbf8d44ddcaa7566eda9cd,0x20100000802449000a820000c1900042800052080010000098c000620802429000050a2000012e00000be20013404000082000047420011240000c8b8000110080002480036500158018000c4009400c9000c0062803a0400e00885042a10888),(0xaf7efcd6de9febfb57d6f5ddedde36f3db7fffeed79fdbfafcf255738c743cbbbff3e3b86b8f9fb9f5bdf54fbff79bd74f5afb3f7fba34f5bf5f9afae879ab5feefe93fa9ee6566f7bbee6bf67d426d75cfb2bace9344fabf72bd58e999b76b3,0x9300010000091004000400382060802420900110020801010208161810541520000000800198110400c004084880812115000049028020c0800220200009220a01801050108206a8408406120184808104430800802442850101410609083421),(0xd3aee9d1a16b8afb579b1b1a2ede96c634714fced4ed35afb8d86696aabedb2eada373270f48f3a9b93de8a90d87d8f6684756adef8eb40bf672fc78b9342c9c7aaa652b2aec9422dd38b32b2a5255bdcc3d35b2da5f372953f3c4ba3a70d996,0x2c07b23e74020fd2aa41748155856818d263d681015680dac92709c7448b08586eaf3a512642c64b613a9091954b38c222671d26711d023332d48951dd0691952839212f8b6888039910b9ac2a42653c283c65315b1b95185ae084b83270c996),(0,0),(0x759a506bc07865de6f37bc2fabe39a5e2705b6a3eec6bd3cca572e3ed72f0325f632aa43d8e0e833eaeab6f86ad5fa72dbaf9c83b9e70faa212acf122e177ae733d8fa39a0b0bb12b7915f7134c3b9a9ed98d75362b1d9c725676c3caf04637c,0x16e5f59c6d01a255c44806523c0cddb5529a2196d082e7c24415d298c0f10d071e6090549dc090f8ed501938009f3fb2169588d90b0b506d102e01343cb84ad135f45369a498be0a36011e712702bb816af81651c4b05c0701a6642cad046374),(0x6339c3e76f77dc41ec6c9766b8b0f93592cd6e58a17db2abb9eea5cd269eeae2dc2c1c9ec755bae6a2821f6b678c3538a75edaf56c57e97ff4e8b90d55c4e75ce36b37ac511be4c610c6f229b9ab77956345b3a117ef6f3608dd37697870ba61,0x84ef690f5888a6bc0049f9381c0ba0115db000874a075d2102333605e754184fe100105f739880fb92c019ec481f2d2102dbf2480954a0ad3f922114724920d57f80032e5018c6a22083e62199863ec06b43378157e41d3d00d937293850b261),(0xd5cc96ab2735f4eedbcfece9fd4d847149d75b8aa71ff3959066dc7566c66ecb75975abde9bb8d684d89311f3151135dd1ce4d97acd9737d0b4d97b62b1596cf57b51ab1b6b408593b67d5bb928b32dabad66fc43367241aeaae177095e247ea,0x481560b0cd924918c5323d4303992d88d1232e6a49f254a2454320824e8122936522ef3572424e688310332525616c12e023da92a435d213539c9243b254cc21b63548a8e4258841b361f1c95a017252ba1c47902bc1245a7a8e167094e243ca),(0,0),(0,0)]
def g119columns : IndexTree ColumnInfo := (.leaf [(4,0,115,0,5)])
def g119autos : Array (List Nat) := #[[],[84],[98],[84,98],[101,66,16],[101,100,66,16],[101,84,82,16],[100,82,16]]
def g119levels : Nat → Packing
  | _ => emptyPacking
def g119index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g119 : Forest := ⟨119,5,fun j => g119samples[j]?.getD (0,0),g119columns,g119autos,g119levels,g119index⟩
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
def g189 : Forest := ⟨189,7,fun j => g189samples[j]?.getD (0,0),g189columns,g189autos,g189levels,g189index⟩
def g127samples : Array (Bits × Bits) := #[(0x27ec63be833e95d9cd8b1b0f8c7b949b955ab7ff06f2f46fb53d19a8b89e2cf938ea5b637a679113a99b1a558cf5d3757100e2a2d92956b1df648864a3a84cf9f5aafcc4980f547cd2d2abacb351593072ded0ca36876c216b176a15583d3069,0x215000b22a840210400a1040082a19401000220004808d00802008c02014082088420800402688520818425544410445400040805130408104600820a3600c001020e0440008143510802b10a111102142440000168440214816081150281060),(0xd1272c7d4d43f0bd72e56dab39ddfe7c6a407c139e413a8c95b2f6c7134bd9d2e6151acc0f6f6e61aecc859cb80ab9d38d1f9c08bbd08127631b9fb156aefb042a9049abe4f27cdb8815184a3fa2b5dede495570df2830da3c38c46cf1426d13,0x806000d540888802080408280406213088804000000320c048631024209804006241648090164a10080940a08001912a8109004a2408004431a0101080453200880088a80c0004a880100481a02008819080040c10830122428406420422c11),(0x3757a63bdee4ba3fd3e2275cd925bbac4327c3605b6a92ba668b6b375f5956a61c0ee4c8b6382a0c726a8d674c1d24e187c7697b46618e9a3259ec9e635cb1935494676727a9c6a3df6b34450ca72f271676b8367562d5a985429aaa9a64d626,0xe190134200c030558e6885084d0788a40161e860830e0412a109c61098d030850809a9902628890c322a09e446182064058721691005078a1841cc5c6248a09654242521162044855722240404692506023498262462c48981029a8a9a244222),(0x7c12f7ae7cb67a121957d4766ab145360dad0baa714fd5dd4ad95b9245e39e4cff88a61691dd24ee5570ea624367b54a6aea5375c626bc6f4082772e38770d5a1955fa1dcb198b20afa8d659c70c9ab5dbb42b955b55e374e0f839c3068a9694,0x100b203118264280010702e3020864421484020c18c0438c4090018044060d7096401604915660c20151c00201478d0220604290c2020821402022221025140809114a0c4919231288809339110498f1918002911b15216460582041008a9494),(0x5f0ed2cab79191489f9794fa9f865222c0c45f4f23977137ba6ec87e2fb718cbcb3281372d8190b9e5b2713c276012285f3b185c628f375c96ee95cada25845527c7ad5b31bc018c667be7de6cdf9480211b73e5e0fc0e1e03a683a80feb2399,0x4e04900c0410144f3ce0e018c1840020605099a3823d30032c4ce03413c1e08c412481b32c810028f486342022205010179b1c44008d375c030cd5d908008055e282051134c40088667900c444ea04000013f960e0680e1a03a083a80f412309),(0x64ed11ab034e6565aa5f6f0a73fb2abb553e90eaf5f2056f4f2ad1a6a7112f3107edc462d825611a42150349a39be3bcbdfa3bf68749fd950e410251758bd0aaed7e1f93ab81b400f6cd22629068e5bc2da9dbde283bbf115009f3b1a197a662,0x46299909050b25a18c71e62a5095c63ecb8f04a3c26b60b927cda532c109201915ade64b3091412042050108b390e3bab9cb9877060097580a090251508bf2aae7571e1ba185a2088a6c00621068c596ada8d9f5a83bbf101009f3a0a197a602),(0xed72aa63cb994444b8dcf183254b4e7cee24db3ad729ab4a1ba98c700af5e5480459e832e1cc5750368c89edf172492ed4565f186db3259850f427f3943aea1f7b1d745054d56ed5059c9e36e00b68fdae413f628aa9c64ad98b04d0b38dd9ac,0x4400b2628be723745844a119668f0ccc9303b92a933d014173710ec9a0c0658c41596832a4cc13563c0629c5d4a2402c44020f584d31651810e10cda143b2c95631f726414156f15141896b3a1182c75a6e53b222aa1c648d9830490938dd1ac),(0,0),(0,0)]
def g127columns : IndexTree ColumnInfo := (.leaf [(32,0,95,0,8)])
def g127autos : Array (List Nat) := #[[],[101,66,16]]
def g127levels : Nat → Packing
  | _ => emptyPacking
def g127index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g127 : Forest := ⟨127,8,fun j => g127samples[j]?.getD (0,0),g127columns,g127autos,g127levels,g127index⟩
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
def g191 : Forest := ⟨191,10,fun j => g191samples[j]?.getD (0,0),g191columns,g191autos,g191levels,g191index⟩
def g251samples : Array (Bits × Bits) := #[(0x7c5b1073c997e37379da30f398119ee6fb6b9ec3f472bcb960b6e16b764eab308775a6f93b85666e9d3190b2b24d642ca5712b6de7ab3f7906c1699135342a691b3ae0a5aa4ef7bb316cf861cfcc30541d6a6cc4992b1a999615c8e8d911c1e1,0x2118206040004a02130d09680103a002090a061080141a8c00302460220208340600a251588102029c90b010225400202065234404234e080480294178042009180840240246b20a0024c060c50410001a48a084882a181106058840c1114140),(0xcce5a5f376b735aeaefe578ced15d32ecca61663a9af3bd1860bc21b19116b79223f9d41251db7915d2d676e62aaa4f819f9d341f91890478f7c179edecb18b88452ff03ce59b2503e9c1117dab8cd95ebc956b7a216470f30e3a2b3ec2d18bb,0x4842cb022293909020208080c0985104462050200a232050248f580a09002349282c0500277025a04229050a00aa2098018840837118b0c40a78400806c358a084123a0140090810bc8810142aa8e601010152222014470a10a222b02c2818b9),(0,0),(0x615f43b7c5899d56d0ed540d07e5651da134ed341e9bc1f74f237fc0ae8a342e74d0d54381c29b89aafb968c73300f2ad24e70d94c925aaf7c71d97b8e42ee34b1eb0d1c78f57307cdbb8ab0333b96f243ce283ea4988c525a6cf93575cb22d6,0x600508638c1a9f0381c44ce96aa5f40532886e32158a42c5402a7e6c4a89343c9410964685c08b09acb0120c353c06229a6c00c94c92de87444159522882ae0499430c1549527146cd2ac810537252985246622c84980c521a4cf835558922d2),(0x743743261165c64a5893c74b56706899b56f313d76fa70640bd59bea9f4cd6cd40c9796a92725dcea2baccf628444b5fc70e36349d152cf473b98c6d967cf8571ea4949a30a5a9a67c52f2db3fa12e66e966315b35ec80fa603e034c2e56ad7c,0x8e228200012500a04432a202145800c8c044118122412020998581138524c38140cb492802205484420a48e00002411d45001410a1402070b13084088559515204a0a28a24a10ca03050168720812c4621201151314480a8603203082a468c2c),(0xf3d9bb1a8ffcdc97c518eaf4c8cf14e122f0fafd99d5fdca7ef0f64eebb658a39d280ab679b66835384c18039df39cc970c09cab32e75b6d986af50aa1e14f67f56dcf6f41924d79e9e39f3990e7fa0a34138f4a5e417d209f607f101fc4fe09,0x9201861738918010c41062040c8818244620088911c0e1638783100880a45083c120082600262524204640020401ded90000982b30080131d06c4002816148a041658f0100904561e8880e0910f0e60220020e2216414120916065101cc4aa09),(0x8c34b489b6743f0cbbb4f14fa7d16d9fa49b993f9ba2b3789eb911d5e1cd7a6f64e2a177140a8013c504eb6dd8b5e7f7e94f5a351463882a81261e97691b96dcefd6ddbc37c1e3432aa0876640524995f6a595fd43d7d81429dbe94302afe942,0x269c30c1984c0e0408d2577d35632830a8c6a4165540daa693102041644d9ca647426045188a80110514e824d9155760ee46136c04410a2a918614976910825e2b85c52c35a0b36b4200852245520814f6b484dd43c398142959c9430287e142),(0x1bb2ab4aa0e85ba9e596de5ec3ce129b01134cce9757f2d674620576a8bd96bf3a893c9457f0a28da9ccac591d7731877093a6c205d64d4c2bcaa6363cd0b55e770f7a466dfb2a9c82572d4ce3aa90cf64d9c30549ce2fe50b809671629a567c,0xd9639e04222012901869c59f133e18908110146a61f169c201c69140019863c2e851098d7d900098988b54119762026501322c440c64c4e0e9086343c860556368a70222d632a1a145321c6e30c00cc44fdf181498e2ec50a809261621a5474),(0,0)]
def g251columns : IndexTree ColumnInfo := (.leaf [(8,0,243,0,7)])
def g251autos : Array (List Nat) := #[[],[84,115],[99,65],[118,84,115,65],[118,81],[118,84,99,81]]
def g251levels : Nat → Packing
  | _ => emptyPacking
def g251index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g251 : Forest := ⟨251,7,fun j => g251samples[j]?.getD (0,0),g251columns,g251autos,g251levels,g251index⟩
def g255samples : Array (Bits × Bits) := #[(0x9b665c544a8481c32c829a3849d25a0c2e734bceaece0410b1910c9246b692285657c973ca335d593cb00f0546b90059eb43e97a932728851785431870f031165ac8b80393ba6e576270cc58c906b870841734e15dc89803598ab05c2460a6b1,0x104454110880808228020a2041d8002c08600a02808c02009111060244ac12008614a1024802115108904700443200508241c8821224200116051018407029164080a01212302c0942400010c90428108414142154888803090a9048202086a0),(0xf315668af28fdb1ca228365b7ccc05a0011317731e21482f697635c521d4e57b4580944cacd08190116899ef79421d834fcee4e488905930903982805fb1c61927af17aaf49049a676974192f0d0160363a1bd03830701b0dc1f8281c2dc6123,0x83112a82400c43108201140b24040542001210600e014836084820c40800442b4181104024900000902098cc210099010006246088901220003082011981800902040620cc814002101041843090160043212902810201b054050081825c2101),(0x380526282fa13ac851f4c9c505254980d6e8ec3804b3594a769d93b950ebc251b0d8e2a15610b8154799066089743516386914b45de9a6e1e91c2d64aa4bec2945782990b2d68e61aa4d3cd1b24a6ab680984b4c1298da14a63264e421a50a46,0x184000082381184051a442400021c800c760240c008201086414493150c8805030586481420228050588002082640402084818905528808149002d00020c144045280184104604602a043c40824a60b20098024012185a048212646400810a02),(0x96903da21572f2b1f1c959078994a771bc47364121282ac5966e24786e0f6b8886ae49c27124b27b7242ff2e0094e0b4b1b582696d3c94568c371a6b03b30075a8d6353ad9672c0089eb12ba6325f80dd24d451b8459a7c113618d0b812f118c,0x86100cb01034a2a12848198388d4226018030240202c8a411a0a044824066a838a240842212092185a40cf0a0080e094a530c6680a1400448645526011312024a0c7343889210800016b021a61259805924545098441a1c11120810b812e1184),(0xca830c6ee5a1c1ac77b2c4bb013b84b271c7189edce77b42164b82b2ec44ccc2202552493f52e619512b4f09e2177ba801c291327039cbf4fba1fd7ca29d36ceca40c4508827295a1b45be11b7c00687be220f65622167c80c13fe90c415919,0x1282044674a181cc515204830038803270c71014e5265b22464b9241a4004482002443590d10ca0850630203a411b2a000c201185038c3861ba0d078200d6480c204804048212d4a89449e11258006869a220d60222163c80c12ea00c414819),(0xadcb89db333a54791fc5b16de6a74b1fbdaa5224c4caa060c8434905e130b3e50875189fa3aee40ebf67487ce98db2673644923b555505294552488c144494c2312ef3656d2d51ee39b1b44e04f3d3ec4d148000ab72771f011403179f478e82,0xa991884a13221d3803c5e045a0014312e78660240442614040424905201081f109410899826ca6043646807ca808b20b342020284941850001124c8410049440302c118d6904416438b533460072d3ec490080008b50771c0014031517470802),(0xccf1d170b069949f14600d7679a83ea985e068495997ad010287ff4ea745b576050c4fa9e8e0fabd2497448bd27a5aa8acea4ac0268e4d44dc2df9de452a225ad1457b3d721818b9bf9e05034d50ecb938aed67098a522a72856072e55b8d214,0xce85130b040942f1560095449a91aad8dc0e80b5196a18140955b282345b194266c47298868eeb9221d4601c27a00e8acf04a8036004c04cc8c58ecc43a23d68161791d311c0cb9abcc24434d40e8b9388ed67018a522072852072e55a0d214),(0x442aa5b9d884c622461c21eaaaf556fac8da8923687abbfb99c9c28096422e0eb83cb34c1d8918aec8c55d99f53bc2670104934ee2f27258616b2c55a56fa8970e02486406e9b92b5242282d15890d903f02672424a3e96d3ce1d022fa0aa8e8,0x460a679588446000a40a01aa08c414e80818810338389a92898982c08602320ec02091061180118a88016c815113416481048146a2821250206d8051a4632a958802cc600689381b004a400915810c003602652424a380613ce19002e808a0e8),(0,0)]
def g255columns : IndexTree ColumnInfo := (.leaf [(64,0,191,0,11)])
def g255autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32]]
def g255levels : Nat → Packing
  | _ => emptyPacking
def g255index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g255 : Forest := ⟨255,11,fun j => g255samples[j]?.getD (0,0),g255columns,g255autos,g255levels,g255index⟩
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
def g383 : Forest := ⟨383,12,fun j => g383samples[j]?.getD (0,0),g383columns,g383autos,g383levels,g383index⟩
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
def deadd8 (i : Nat) : Nat := 0xa24b7baf6624ad253281df927589c4d52540d02
def deadl8 : Packing := (2,6,7,0,4,3,0,deadd8)
def deadd9 (i : Nat) : Nat := 0x17a6100d01602e1f830400f202c200003405840f980801c0010720e8006a183c001d000f8007c00200001509fc5a0b0071b79b2bc5ba99429c459e8d258238d84a14078280a00a7becc495a4a6503c6fdb66689a4d50287fcbc661a544d029ef9c6aed1840d02bed9c626d3540d02ff49184d52540d02ff489c4d52540d02d7f11826d1540d02ffc1184951340d029f6cbc4a1354950195fdc7aed2564d01ff49384d52540901ff61384951540901ef4935496aa40d02df49b54951340d02f7493549503a6502bf62cc4951540901ef6125456aa40901f7612545502a6501fb61284612545600fbc1284612344e009dd9c7aed258ce009ee9c6aed1888a009df1c7aed2584600ff42558ce2284600
def deadl9 : Packing := (25,5,7,1,4,9,0,deadd9)
def deadd10 (i : Nat) : Nat := (if i<1 then 0x2693540b3fecd1349aa055ff26d1a4d502cffb30d2a26815ffabb4610340bfec8c26a81a05ff626d3540d02ffd23092a06817ff1184550340abff5da6b4ca059ff4d5a1a65029ff9569426a80cffdb8aa9354067fed95549aa03fdb4a13549501affb7092b2680e7fda849593407bf69424ac9a035ffaed2564d01cffab15532680e7fd25aa993406bfedc26ac92035ffaed3564901cffab0d1b2480e7fd38aa9924073fe9ad54c92037fe6e13540901fef2b09aa0480ffd9384d502406ffd5da6a81203ffa4e12540901ffe2708aa0480f7f95864d02406bff5da714ca03df74e135a6501affd769ad3280d7febb49699407bbe9aa4b4ca035ff6e123a6501efda5091d3280d7fdb548e99406bff5da474ca039ef495a4a65038ffb63553308167f9b0aa998408bff5dd54cc2053bf6daaa461028ffb6a4d2268157fabb6610340bbf4cc24a81a055fe26d1540d02cff33155206816fd935aa90340b7f492d5481a057f66d51340d02ff924a89a06816fdaaa44d0340b3fcd42074ca05df64d503a6502efd24a81d328157fabb40e9940bbec89a074ca059fd461a1a65029bfb6f5524a80c7febb6a1934063fedc554c9a031ff6d6aa64d01cf7b695532680c7fdb2aa9934073fcd8554c9a031ffaeda8649018ffb6ad1b2480c7febb68d92406ff55da4a81203fda4d52540901fee34a8aa0480f7e92564d02406bfd5db2681203bfa496aa40901dfe22b5520480e7f993aa902407bf492a054ca03dfc45502a65019ff36755251004ff9b1aa928802ff55da5092c01efa4a11849600dfd2515524b007f692849515803fb88c24a8ac017deaed2545600def55492a2b004ffabb6a123802ff55da5091c01efa4a11848e00dfd25155247004ffabb6a1138027fc55a5089c01afe6a12844e00bfe5768c227007bf128461138027fd5db4a89c01bde6952544e00dfe23155227004ff9b8aa9138027fcdad5489c013fe6caaa44e00ff925091a27007fd11848d13802fed5da4689c01bf6aa92344e00bfb57692c67005fdabb45633803fac92a2b19c013feaeda844a009ff370d2a25004ffabb695128027fcdc346894013fe6d5a344a009ff576d1a25006ff1a844d12802ff95da2689401bf66963344a00dfe22755225006fda33aa912802ff55da71114017faaed1888a00bfd3709ac45007fc9384d622802ff55da6b114017fa6e11388a00ffc23089c45007bea8844e22802ff4daa27114017faaed1388a00bfe5769c423007fd1384d611802ff95da6b08c017fcaed2584600fee26a92c23005ff1b848e11803ff09424708c017fc6d52384600bfe57691c23007fd1588ce11803fe89446708c01ff44963384600ffc27111423007fe13588a11803fa49aa4a81a05fd849515409019bf36f5524b007bd2888ce11803df14444508c01ff08ce2284600 else 0x4000888405e986c113905805080340b02e1f06087905c2003f080d05c2010004400c0288128f50060048004020800804100127c503a3f6c170230c990618643002074409038882341900e30020304004060800870140c00228180045c08224a09086c45817020801a183810008ad48702001100108e2b0c1c0800456383810230b0200117dff6de0be2c10281f00a20021f8a108140c707c503e3f8bed83901520010dd505020c988c1183426000e000e00086905c20a40d058002020340034003c1834002fd2040bdb798060306e1b00c84f01a5f8a10bc3024202bf0c090605c00880505210010fc506e1cc0693effc5f6de600097e28190cc11092183f1414080603412860a40cc6004380038003800340034003c003c0020e00107000f000801c0020e00100f78ee2192287800ec3041c003c00361820e001f8a1e001e001e00100000b0411ef1dc4377ae886cc5917b60fc50f000d8e083e2840000016a420f6c1b1c100000b521002c30416383f1420003e284000100c4aca220cd523db61a02c91b20b40600a0dbf169c61a02c9f6de60578fe2fb6f303f8bedbcc0fe2fb6f303d0acfaceacb9c93c83c68c63c53c38c1dc02bd1bb6b9bb96b70b4ab24b09aeeac8aada92a77a5ca41a31a169fb9eb9e69e19d19b69a698b97096094593591a8ff8c38a889887284c81b80b7f07bf7af79f78f7747597497397297197096f96de6b867c64b62560a5ef5df5ae5725415315164fb4d54c54b54a549548547546545545044043b42b41b4164114013fc3ec3e73cc3a639639138137136135c34c33c32c31c30c3073022fd2f82e82cd2b229728727726725725224223d23823322e2292192142041f41ef1ea1e51e01d01cb1c61b61b11a119118c18718217216d16810009807204c026000affd7692d3281defdb6)
def deadl10 : Packing := (156,4,7,5,4,12,0,deadd10)
def deadd11 (i : Nat) : Nat := (if i<1 then 0x86120d08111f407ad1db072b1c206d11ab867718d8613174859115b85231388497118042910183c50e603570c082b709d822b07a8195055010902a80410003ffd1849503fff6692540fffd2546503fff4613540bffd9a4d502fff2693540bffd1a4d502fff4619340bffd3546502fff4d69940bffd9a4e101fff6a135407ffd284d501fff4a935407ffd9a4d501fffaa935407ffd3849501fff4e925407ffd9a49501fff56123407ffd9a48d01fff56193407ffd2864d01fff49593407ffd5864901fff4e192407ffd3564901bff6a11940f7fd9846503dff6551940effeaa46503dff4a51940f7fd25a6503bffaa99840b7fd1a66102dffaa99840b7fd9a46102bffaa91840bbfd9846102dff6619340affda564d02dff6559340affeaa64d02bff6951340bfdd9344d02ffe6a10340bff99840d02ffe4610340bff9a540d02ffe6550340bff91540d02ffe4690340affda846502dff6611940affda346502dff64d1940bff90346502dff6629940b7fd93a6502ffe40e9940b7fd18a6502dff4d69940b7fd13a6502dff66935406ffeaa4d501dff66925406ffeaa49501fdf4d525406ffda864d01dff66193406ffeaa64d01dff561934077fda864d01dff4a1934077fda564d01dff495934077fd2a64d01dffaa993406ffda864901dff66192406ffda564901dff65592406ffda364901dff64d924077fd3864901dff6a1924077fd3564901dff68d92407ff95840901ffe4e102407ff9a840901ffe66102407ff93540901ffe69502407ff99540901ffe68d02407ff99340901dff4e2994077fd35a6501dff496994077fd23a6501ffe4e928803ff91a4a200ffeaa928803ff9a849600ffe46125803ff93a49600ffe46925803ff92845600ffe4e915803ff92a45600ffe6a123803ff91848e00ffe69523803ff91548e00ffe46923803ff9a844e00ffe4a113803ff9a544e00ffe49513803ff92a44e00ffeaa913803ff95844a00ffe4e112803ff9a844a00ffe4d512803ff9a544a00ffe68d128027feaa661029ff2693540a7fc9a44d02dfe6610340bfd93540d02ffa4950340affaaa40d02ff644d0340a7fda8a6502dfe40e9940a7fda3a65029ff6869940a7fda864d019ffaa9934067fda8649019ff68d924067feaa64901ffa49502407ff11540901dfe64d02406ffaaa40901dfe40a99406ffaaa4a200ffa4a125802ffaaa49600bfeaa915803f792545600bfe6a123803fe92848e00bfeaa923802ff9a844e00ffc46113802ff9a544e00bfeaa913803fd92344e00ff649633803fd9158ce00bfe6a112802ff9a544a00bfe68d12803ff11344a00ff68cd12802ffaaa44a00ffa4e222803fe91888a00ffa4d622803fe91388a00ffc4e211803ff13584600ffc49611803ff123846009ef6929940fbea8888a00ff48ce11803fe22284600 else (if i<2 then 0x6718d1b071686b63b38c6ac837ab208143ea5f4a804c20460a84911c7405186a093027a82ae19d57d066c694fa70dcc0ac4ea478ce31a1ecaeaf303c8c241ac2f19b38c69c83fbee47302190238ea2305424c6856399d2085637d12388c0c16cbeff1d208076416c80b40c0049e29d5208144b23f46802b201800c183275231bc58d5919c2ba9ed854030806003067bf9c352078df64634afd056e600c20020b418eaf319c182b832c8683382f1c2de703e3ac80ac412003efc19433aad06707f7f38754282036168bdf159a0ce09fa590158824f17a919786904bef86bc33ab209458f7dd8e39c8904deff5232b9120958e0b701b7e8611b1e288d8776dd9609e2b1c2f1582105b80098e0b90124824976d090cd009250909820be81c002d484d8f144c3068ea08444c12222609117812260911961224208de83785dd4e900b63480dfc5edb981b80c307224fbfd4f301f09477d2a0d202e2010188cddb353cc69017202256222f7fb60add5a80164f6c116903054660bb98d200c6e0e18f8afa73037818602100ed9a0d20beff8bdb752d00186f7fc5ea78e6e01e33bfe2f534770c056718d202388c2401066f7fc5ea68ee1b388131a6862ef8df646718d182bf7fa963ac8ce31a3fbfe2f6dd4f31c70187010d8f7c2b7561a05a04ce121581816fbfdb3530d74005590a1982b682c8ce0be2f6dcc0184f14410307c705b875e98d59067d2d5c686717058176d8d1b06f7c92f17b6e602d3634e457030b7007d2a0b20be2be9500fdf0b7b6c68d029b1803bfe2d415c1bc57d2a01fbfc3600ead415c1bdf363c5c6a8eae0d8d3915c0fdfe0b00ed9a9a81c83fbfc3600ead40dc1ba9e3b0e77f1ab22b839c4d4e356457053ab00682c8ae0bdb341640fdfea700682c8ae0dd49c58d1bc4ea782c02c87d1a03753c751d873bf64634dc23dfe0a86c03b6755a03fbfd4e0164340dc1a82ea786c03c57d1a03fbfc36015c3aad01bdfe3a8ec3ab86a71a7211eff5380570d03906f7fc5edba9e1b82040ec751d87590fa7538d71ddc2586a198ec1bdff16b8ea71ae195efb915c7ab8d74068ed23878d423198bda2f18b3a2a189fa24788e221f881a1e387521a785ea14384820fd83ba0cb82a2071816203f8099ff97ee1f8b7d29f137b21e9179b9e377829ddd76c1d8d7581d3373c9cb17239c6170f9bfd6f41ba36e01b536c99af96b31a9f69c9a4568619f5665990f63618ab610981f5f517935dc17435c0969959b163558495c7566954f54b14f552f949151914374f393a14ce130b4b2929349c124347e11cb46c9185456112143a90a941c9063415103b4088ff53f70fc33ea8f9b3e30f7d3d68f4b3cc8f233c50f053bd8edd3b38eb53a70e8339d0e5b3930e3d37a0da73570d2f3368c7b3160c0d2f30b952d50b132af8a3727d89ab2580901226 else 0x6c244e0445e2e80648bc5050262048e47300a0565ed8f60346f5d8ae98260a0c0068580a0c27015b807c906026158e08c030604c2b2a82103cee10cc378bc503c5a1a381a3a2d03cb121b082409e29104f14d80b00b29b02601632490481068e0401093981802127303093987200a0aca00c1820060c1003060ba9e62b81ec8b40d15c753cc0a26ae1d5e606624740ac47cc0483c9bdf72398ae02b28b1eff6cec705e2c44719c65bd0520ccbd4b702a0c67030651f4282f8a37f6c0f90083dbc507c95c01a2901847d2a015c7efbab500764fd1d5a800524460a84613d40171bdf12bb67568e07cc1703e060df4d22a00b883dd40220c2777c2ed22a06e0defe90110884fd1d5a800526915008831e748a802e219d5c0560f91f4ea40c1509ef89ad00884fd0566800c25702b3400611df1500c10c813b1c0f00a44001e0b8625494a83ec3b7532876c0fa40c07c018307cf7fb66a40f0d782d231a682c8a82a1e8185ce3c519b1a206a008183e7be5a8cd9c5ab50287af14281809827bfc7))
def deadl11 : Packing := (183,3,7,8,4,14,0,deadd11)
def deadd12 (i : Nat) : Nat := 0x226c48bbfb654c3991828d28cddfe2ea731865c0891b87a0bb538ea405a3487b1d9bfa906e3a90b8064694310477f6ca947523051a4f7f6c2ed4a3a91828d23bfa90b0351c15a42e0191a577f8ab8d4e631c0c3f7e91b6d4c6b1c0c3811c4dfe2ea51d869c41234a020c7bed54772271048d2408d8efaa71cc89c4123490277f528e4932271048d27e9c5d4a830c011d1fe8c8d4907400c377f8bb6d4e1b04223bd3538ea46e23461177f6da950523047efedb538ea4608191a477f8ba94761a711a3f7f538e644e0191a3f7f5398d032019383963e9c516e8018413c39e9a98d63991b83b6205dfdb2a635a0646093df6ac6b41c816ae0f00efedb52a0493230488077f8ba95061970704f7f531ac732112b842091d02eff176da98d61b04a4140bbec8db6a6358ec1250d06eff1571a98d6830c994a8fd8b08517fb7ae74f70b6c76686125bc5665224e74a34684243d739334f30b2c728322d1e919c15810b0ac056000ffe92a07ffd1940fffb30817ff46102ffe9aa05ffd9340bffa26817ff46502fff4ca05ffd38407ffa6a80fff49501ffe91a03ffd93407ffb2480dffa6503bfecc205ff90340affd32815ff64d01bfec9203ff902406ffd3280ffe4a200ffc92c01ff915803ff247007fe44e00ffc89401fda33803fd445007fc84600
def deadl12 : Packing := (32,2,7,8,4,12,0,deadd12)
def deadd13 (i : Nat) : Nat := 0x22dfc5b6a90e86821a4efdb54c724410d1f7f16a63a18e01069005bf8b6d52351d0d049cf924d00ffd03ffd02ffd01ffa00
def deadl13 : Packing := (4,1,7,5,4,8,0,deadd13)
def deadd14 (i : Nat) : Nat := 0x17e2b6526070604013ff
def deadl14 : Packing := (1,0,7,2,4,0,0,deadd14)
def deadsamples : Array (Bits × Bits) := #[(0xf854605d026923a5a16008862c9d18d42fd85e54d221898f1e440284a107a02910c3e03c06c40d2642ca74f54627022c11e389d9b43b30c961ca72386ce81500aa210d1ba1a121108a6c99348979d054ac200727ac054c0970110780155ad581,0x6844620d0040231585204884208800c4270824141201090814040082a10700282003e02402c4084602ca04a440240a1091218919100a2084314a220840a00480aa210819a02120100a4409048968c05484200702a805440920100380144a9480),(0x80b20c31f72bfc4e1481d27000d43c9c5bd438a9c5e0286040f054f111d001ce10920229bde170b8d339029e2bcac4cd494fb74d1052452141a61c5b9ca1e642f40c600258428f0e5c00df481e03202a204cd465e10fe01206e82c7b03150603,0x80100c30e6089040109182600012282018c41889c5e0204002b0604000c009861080028b1c2120a0d12000120908c00d005a724402504200402010501c01c208540860025840090e1400964816012008204cd0254102a00206a0247b01150201),(0x12ce100c308544478a85796a2341d206e4242e31335abb35943abb40be28c8e05c4c115123137950052a02a9ba0d31c096458c656cc338623e92230683d8962194d5145c2aa62229438824d8e06246d0cd124850733918c390189888a426380a,0x10ca0000108540870900790a0240900460282200221a991490081a0028289000cc41010021184410080a0a28a20020c0200184206c0128621092200a03d8103080d5145c02a2022143880090804206d04d100840322918c190088800a4221002),(0x8628ebbd17000228c83c0291b729e17b3643984a392a815889878936d04e41b82b8e28807cc302855ead3105d9868885c748c2b0724ae81086518e259124cd4278a18b4aa01db88524c3a3435a0814469349110c18f0c24c2a8052bd88818268,0xc2206a1d05000020401c0090e509051303449848110100480001811490070429238c000818c508010485900541c68805c240409012420000024186258024450270208b02a00da0842041a3414a08100690490104085040042a8052bc00818028),(0xbc8ccda8781e4d8151cd3cf93a4a0a01509a42078c1bc4a783ea4aec6c7bbbd02ef85be130b1750bcd872a062d01842a34826040203d5b99ac8899721d47b82106b4f88001d04ee6f42e103eb14e0a090b95e84905a08ef7a2230402e2b14bc5,0x148981a0109a5c8210c1a4690a42220050930202c418c4a7837a48680e50b9d00c601bc02020f518c9002a002c1124282402304220255b598c9019921c51b8010494708001d04e62d42a103a30060a090b94e84905a08af280230402e2304b45),(0xd3b19712becef4647857054f8773c68492608a46265cd6cd0106c449284294958830b40e8328a4102841c46a63b66493288c7290c714876750b08cb0eb0a532e014ce7e24f9c08720240400006971f885be46b00080a21145aa7f52cf42a8012,0x92218c003e8654007015040a0c73c50280c0084821449285810a8400004080918c301008002824100801c000230200c0688c40804110046300b00cb28307502a0004c5624f9c086200004000021315805bc46800000a00145205f42ce0200002),(0x3145d24845746a93b60987114c89950ee90ab5809889781e716b0d141d9e036fea797f20c896480c8b565809c5575a81eabcad03980701be24b7e8d7401960b32336416db2f0c4c050f169960250e8b311988b92828b0074bd455ad232c2112c,0x2307720c00346283a400011d4c09950fa108a4001a095004514a0014181e2261ab3d3060c0d6480a2ac41009e4571880ea848181d90321bc24d38a860208103323340169a2b084c040f169960050c8b211800b9082890074b8455a803282012c),(0x49615339cc24bb41a658244591d020101222d0f578b5376254a121290a30cd5c4e2ad1d6dabfa9e032f022500c91031b32331a7a9ace0ca4e96243014a4009cd0d2a3210b66014de852533c420acc80ff443ad9cc5d0f4808cd621151170ac54,0x4900539a4030aa408668006591882010120251355ca1242200a1212102144d6e020a42d6d2878b6832b420400cb9813312321a4a924e408ce04943054c0001c10d2a2200b040149c8425334420acc80fa003859cc5d0e4000cd201111150ac54),(0x2108654280dbc21c532263cad6a2ab60a053058994f658a43b3dd89384745a04932387065124c385d01899e2cc083e3c1e3327061d61ca921a4965c8583262f4485320b5c04953298d1f02098424a39520b6148b236021a80528c3236c545ab4,0xc0001428049001c03a04a4012802a200013019184320c200a34088304a0580410028702010083a440180cc2080827381411260a0400ca0098085048489022c408432094004053098d0e0008842422012032140b21202188052801030c545a90)]
def deadcolumns : IndexTree ColumnInfo := (.fork 63 (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(1,0,510,0,12),(0,1,460,50,8),(2,0,509,0,12)]) (.leaf [(0,2,440,69,8),(3,0,508,0,9),(2,1,460,48,7),(4,0,507,0,12)])) (.fork 4 (.leaf [(0,4,369,138,8),(5,0,506,0,8),(6,0,505,0,9),(4,2,440,65,7)]) (.leaf [(2,4,369,136,7),(7,0,504,0,7),(5,2,440,64,6),(8,0,503,0,12)]))) (.fork 8 (.fork 4 (.leaf [(0,8,227,276,8),(9,0,486,0,8),(10,0,501,0,8),(12,0,499,0,9)]) (.leaf [(8,4,369,130,7),(4,8,227,272,7),(14,0,497,0,7),(10,4,369,128,6)])) (.fork 4 (.leaf [(15,0,480,0,4),(16,0,495,0,13),(0,16,486,9,10),(17,0,494,0,11)]) (.leaf [(16,1,460,34,7),(19,0,492,0,8),(16,4,353,138,7),(21,0,490,0,7)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(21,2,424,64,5),(24,0,487,0,11),(8,16,486,1,9),(25,0,486,0,8)]) (.leaf [(9,16,486,0,8),(27,0,484,0,5),(11,16,484,0,5),(24,4,353,130,6)])) (.fork 4 (.leaf [(29,0,482,0,5),(26,4,353,128,5),(32,0,479,0,12),(0,32,94,385,8)]) (.leaf [(32,1,460,18,7),(1,32,94,384,7),(35,0,476,0,7),(34,1,460,16,6)]))) (.fork 8 (.fork 4 (.leaf [(36,0,347,0,8),(39,0,344,0,4),(40,0,471,0,8),(49,0,462,0,8)]) (.leaf [(48,1,460,2,6),(50,1,460,0,5),(56,0,455,0,7),(64,0,447,0,13)])) (.fork 4 (.leaf [(0,64,189,258,10),(66,0,445,0,11),(2,64,189,256,9),(67,0,444,0,8)]) (.leaf [(66,1,396,48,6),(70,0,441,0,8),(69,2,440,0,5),(74,0,437,0,7)]))))) (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(74,4,305,128,5),(80,0,431,0,11),(83,0,428,0,7)]) (.leaf [(96,0,415,0,9),(96,1,396,18,6),(98,1,396,16,5),(128,0,383,0,13)])) (.fork 4 (.leaf [(128,1,332,50,7),(3,128,344,36,6),(132,0,379,0,11),(4,128,347,32,9)]) (.leaf [(133,0,378,0,7),(134,0,377,0,8),(132,2,312,65,6),(133,2,312,64,5)]))) (.fork 8 (.fork 4 (.leaf [(136,0,375,0,9),(128,8,99,276,7),(140,0,371,0,8),(132,8,99,272,6)]) (.leaf [(138,4,369,0,5),(144,0,367,0,11),(152,4,353,2,5),(160,0,351,0,11)])) (.fork 4 (.leaf [(160,1,332,18,6),(162,1,332,16,5),(164,0,347,0,8),(36,128,347,0,8)]) (.leaf [(172,0,339,0,5),(176,1,332,2,5),(180,0,331,0,5),(192,0,319,0,11)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(198,0,313,0,7),(256,0,255,0,12),(258,0,189,0,8),(260,0,251,0,8)]) (.leaf [(264,0,247,0,9),(256,8,227,20,7),(8,256,151,96,7),(268,0,243,0,7)])) (.fork 4 (.leaf [(260,8,227,16,6),(273,0,238,0,7),(280,0,231,0,8),(276,8,227,0,5)]) (.leaf [(288,0,223,0,9),(256,32,94,129,7),(32,256,151,72,7),(257,32,94,128,6)]))) (.fork 8 (.fork 4 (.leaf [(296,0,215,0,7),(40,256,151,64,6),(304,0,207,0,6),(288,16,198,9,6)]) (.leaf [(273,32,78,128,5),(56,256,135,64,5),(320,0,191,0,11),(256,64,189,2,9)])) (.fork 4 (.leaf [(322,0,189,0,8),(258,64,189,0,8),(324,0,187,0,7),(324,8,163,16,5)]) (.leaf [(321,32,30,128,5),(388,8,99,16,5),(168,256,23,64,5),(224,256,23,8,5)]))))))
def deadautos : Array (List Nat) := #[[],[118,130,81],[100,131,82,16],[118,133,100,131,50,33,16],[116,83,32],[118,116,83,130,49,32],[118,133,33,48],[82,129,48],[118,133,116,83,82,81,80],[116,50,129,80],[100,49,128],[118,100,83,130,81,128]]
def deadlevels : Nat → Packing
  | 8 => deadl8
  | 9 => deadl9
  | 10 => deadl10
  | 11 => deadl11
  | 12 => deadl12
  | 13 => deadl13
  | 14 => deadl14
  | _ => emptyPacking
def deadindex : Nat → Nat → Option (Nat × Nat)
  | 8 => fun _ => none
  | 9 => lookupWord 1 3 0 9 1 4 (hashdeadl9)
  | 10 => lookupWord 17 61 5 13 5 4 (hashdeadl10)
  | 11 => lookupWord 124 434 7 16 8 4 (hashdeadl11)
  | 12 => lookupWord 137 475 8 16 8 4 (hashdeadl12)
  | 13 => lookupWord 26 148 3 13 5 4 (hashdeadl13)
  | 14 => lookupWord 7 47 1 10 2 4 (hashdeadl14)
  | _ => fun _ => none
def dead : Forest := ⟨511,14,fun j => deadsamples[j]?.getD (0,0),deadcolumns,deadautos,deadlevels,deadindex⟩
set_option maxHeartbeats 0 in
theorem geomdead : graphValid dead (boundsBefore known383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=5) ?_⟩,listPieces_all (d:=3) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead8_0 : block dead 8 0 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead8 : block dead 8 0 2=true := sdead8_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead9_0 : block dead 9 0 12=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead9_12 : block dead 9 12 13=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead9 : block dead 9 0 25=true := (@block_merge dead 9 0 12 13 sdead9_0 sdead9_12)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_0 : block dead 10 0 6=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_6 : block dead 10 6 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_42 : block dead 10 42 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_78 : block dead 10 78 35=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_113 : block dead 10 113 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_149 : block dead 10 149 7=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead10 : block dead 10 0 156=true := (@block_merge dead 10 0 149 7 (@block_merge dead 10 0 113 36 (@block_merge dead 10 0 78 35 (@block_merge dead 10 0 42 36 (@block_merge dead 10 0 6 36 sdead10_0 sdead10_6) sdead10_42) sdead10_78) sdead10_113) sdead10_149)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_0 : block dead 11 0 4=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_4 : block dead 11 4 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_40 : block dead 11 40 15=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_55 : block dead 11 55 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_91 : block dead 11 91 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_127 : block dead 11 127 29=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_156 : block dead 11 156 27=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead11 : block dead 11 0 183=true := (@block_merge dead 11 0 156 27 (@block_merge dead 11 0 127 29 (@block_merge dead 11 0 91 36 (@block_merge dead 11 0 55 36 (@block_merge dead 11 0 40 15 (@block_merge dead 11 0 4 36 sdead11_0 sdead11_4) sdead11_40) sdead11_55) sdead11_91) sdead11_127) sdead11_156)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_0 : block dead 12 0 3=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_3 : block dead 12 3 14=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_17 : block dead 12 17 15=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead12 : block dead 12 0 32=true := (@block_merge dead 12 0 17 15 (@block_merge dead 12 0 3 14 sdead12_0 sdead12_3) sdead12_17)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead13_0 : block dead 13 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead13_1 : block dead 13 1 3=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead13 : block dead 13 0 4=true := (@block_merge dead 13 0 1 3 sdead13_0 sdead13_1)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead14_0 : block dead 14 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead14 : block dead 14 0 1=true := sdead14_0
theorem tablesdead : checkedTables dead 14 := by
  intro k hk
  interval_cases k
  · exact (rfl : block dead 0 0 0 = true)
  · exact (rfl : block dead 1 0 0 = true)
  · exact (rfl : block dead 2 0 0 = true)
  · exact (rfl : block dead 3 0 0 = true)
  · exact (rfl : block dead 4 0 0 = true)
  · exact (rfl : block dead 5 0 0 = true)
  · exact (rfl : block dead 6 0 0 = true)
  · exact (rfl : block dead 7 0 0 = true)
  · exact alldead8
  · exact alldead9
  · exact alldead10
  · exact alldead11
  · exact alldead12
  · exact alldead13
  · exact alldead14
theorem dead_start {prior : Nat → Nat}
    (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid dead prior=true) (checks : checkedTables dead 14) :
    Impossible graph 14 inputs.toFinset := by
  have noRun := root_index (g:=dead) low geometry checks (k:=14) (by decide)
    (i:=0) (ws:=inputs) (by decide +kernel)
  have tgt : targetOf dead=graph := by decide +kernel
  exact tgt ▸ noRun

def control := inputs.getD 4 zero
def signWord (w : Sig) := if w = control then neg w else w
def signedRoots (m : Nat) := (vars m).map signWord
def signedPairs (xs : List (Sig × Row × Row)) := xs.map fun (w,r,s) => (signWord w,r,s)
def obstructs (T : Sig) (raw : List Sig) (r s : Row) :=
  bit r T && !(bit s T) && raw.all (fun w => !(bit r w) || bit s w)

def countCheck (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) (r s : Row) (L : Nat) :=
  let n := (xs.map Prod.fst).toFinset.card
  checkEssential T raw xs &&
    (decide (L ≤ n-1) || (decide (L ≤ n) && obstructs T raw r s))

theorem countChecked {T raw xs r s L} (h : countCheck T raw xs r s L = true)
    (hp : proper T) : Lower raw T L := by
  simp only [countCheck,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at h
  rcases h with ⟨ess,short | ⟨le,flip⟩⟩
  · exact fun p bank hr hit => short.trans (lower_count hp xs ess p bank hr hit)
  intro p bank hr hit
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live hp hr hit
  have enough : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨i,j,diff,isolated⟩ := essential_ok ess a ha
    exact raw_required run raw a sub i j diff isolated
  have nt : t ≠ 0 := by
    intro none
    simp only [obstructs,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true,
      Bool.or_eq_true] at flip
    obtain ⟨a,ha,pos,zeroRow⟩ := mono_row_difference run none flip.1.1 flip.1.2
    rcases flip.2 a (sub a ha) with h | h <;> simp_all
  have bound := (live_size run).2
  omega

def signedColumnOK (m z o q s base L : Nat) :=
  let free := colFree m z o
  let g := movedWord (fixRows z o) (graphGoal m)
  let xs := signedPairs (supportPairs s)
  properB g && checkMap (fixRows z o) (signedRoots m) (graphGoal m) (signedRoots free) g &&
    (movedWord (fixRows z o) (subcube z o) == one) &&
    (if q=0 then countCheck g (signedRoots free) xs 16 0 L
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) g (signedRoots free)
         (signedRoots q) (graphGoal q) xs &&
       decide (L ≤ base+(xs.map Prod.fst).toFinset.card))

theorem signedColumn {m z o q s base L : Nat}
    (prior : Lower (signedRoots q) (graphGoal q) base)
    (h : signedColumnOK m z o q s base L = true) :
    Slice (signedRoots m) (graphGoal m) (subcube z o) L := by
  simp only [signedColumnOK,Bool.and_eq_true,beq_iff_eq] at h
  apply slice_correct h.1.1.2 h.1.2 (proper_of _ h.1.1.1)
  by_cases empty : q=0
  · exact countChecked (by simpa only [empty,ite_true] using h.2) (proper_of _ h.1.1.1)
  · have e := h.2
    simp only [empty,ite_false,Bool.and_eq_true,decide_eq_true_eq] at e
    exact fun p w hp hit => e.2.trans
      (lift_ok e.1.2 (proper_of _ h.1.1.1) (proper_of _ e.1.1) prior p w hp hit)

theorem finishLower {raw T cap} (xs : List (Sig × Row × Row))
    (ess : checkEssential T raw xs = true) (all : xs.map Prod.fst = raw)
    (hp : proper T) (h : Impossible T cap raw.toFinset) : Lower raw T (cap+1) := by
  apply lower_impossible hp _ h
  intro w hw
  apply essential_ok ess
  rw [all]
  exact List.mem_toFinset.mpr hw

abbrev SliceCode := Nat × Nat × Nat
def cutDomain (c : SliceCode) := subcube c.1 c.2.1
def certifiedCuts (m : Nat) (cs : List SliceCode) :=
  ∀ c ∈ cs, Slice (signedRoots m) (graphGoal m) (cutDomain c) c.2.2

def decorateSigned (m : Nat) (p q : Nat → Bits) :=
  (rawDecor m p q).map (fun w => if w.1=control then dneg w else w)

theorem decorateSigned_ok (m) (p q : Nat → Bits) :
    ∀ w ∈ decorateSigned m p q, faithful (asRow p) (asRow q) w := by
  intro w hw
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
  split
  · exact faithful_neg (raw_faithful m p q _ hv)
  · exact raw_faithful m p q _ hv

abbrev CaseCode := Nat × Nat × List (Nat × Nat) × List Nat
abbrev Cases := Nat × (Nat → CaseCode)
def emptyCases : Cases := (0,fun _ => default)
def caseBank (seed : List Decor) (depth : Nat) (c : CaseCode) := decodeBank depth c.1 seed
def caseWires (seed : List Decor) (depth : Nat) (c : CaseCode) :=
  selectLive c.2.1 (caseBank seed depth c)
def caseValues (seed : List Decor) (depth : Nat) (c : CaseCode) :=
  (caseWires seed depth c).map Prod.fst
def casePool (m : Nat) (cuts : List SliceCode) (bank : List Decor) (ops depth : Nat)
    (rule : Nat × Nat) : Option BoundPool :=
  cuts[rule.1]?.bind fun c =>
    materialize (signedRoots m) (chosenSteps bank ops rule.2 depth) (cutDomain c) c.2.2

theorem casePool_ok {m cuts bank ops depth rule p} (hc : certifiedCuts m cuts)
    (h : casePool m cuts bank ops depth rule=some p) :
    ValidPool (signedRoots m) (graphGoal m) p := by
  unfold casePool at h
  cases e : cuts[rule.1]? with
  | none => simp [e] at h
  | some v =>
    simp only [e,Option.bind_some] at h
    exact materialize_sound (hc v (List.mem_of_getElem? e)) h

def nextCases (seed : List Decor) (depth : Nat) (xs : Cases) (ids : List Nat) :=
  ids.filterMap fun i => if i<xs.1 then
    let ws := caseValues seed (depth+1) (xs.2 i)
    some (keySet ws,ws)
  else none

def caseContext (m : Nat) (seed : List Decor) (cuts : List SliceCode)
    (k depth : Nat) (below : Cases) (c : CaseCode) : NodeContext :=
  let bank := caseBank seed depth c
  let ws := selectLive c.2.1 bank
  let rules := c.2.2.1.filterMap (casePool m cuts bank c.1 depth)
  let candidates := nextCases seed depth below c.2.2.2
  let links := fun tag => candidates.filterMap fun (h,ys) => if h=tag then some ys else none
  (k,ws.length,ws,preCov ws,rules,links)

def caseCheck (m : Nat) (seed : List Decor) (cuts : List SliceCode)
    (k depth : Nat) (below : Cases) (c : CaseCode) :=
  let ctx := caseContext m seed cuts k depth below c
  prelim (graphGoal m) ctx && testAll ctx ctx.2.2.1

def caseLevel (T : Sig) (seed : List Decor) (k depth : Nat) (xs : Cases) :=
  ∀ i, i < xs.1 → Impossible T k (caseValues seed depth (xs.2 i)).toFinset

theorem caseCheck_ok {m p q seed cuts k depth below c}
    (pairs : properPairs (graphGoal m) (asRow p) (asRow q))
    (faith : ∀ w ∈ seed, faithful (asRow p) (asRow q) w)
    (good : certifiedCuts m cuts)
    (prev : caseLevel (graphGoal m) seed (k-1) (depth+1) below)
    (ok : caseCheck m seed cuts k depth below c=true) :
    Impossible (graphGoal m) k (caseValues seed depth c).toFinset := by
  simp only [caseCheck,Bool.and_eq_true] at ok
  have checks := ok.1
  simp only [prelim,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checks
  apply node_sound (raw:=signedRoots m) pairs _ checks.1 (by simpa using checks.2) _ _ ok.2
  · intro w hw
    exact decode_faithful _ _ _ _ _ faith w ((selectLive_sub _ _).subset hw)
  · intro v hv
    obtain ⟨rule,_,hit⟩ := List.mem_filterMap.mp hv
    exact casePool_ok good hit
  · intro tag ws h
    obtain ⟨⟨a,ys⟩,hy,hval⟩ := List.mem_filterMap.mp h
    change (if a=tag then some ys else none) = some ws at hval
    split at hval <;> simp_all only [Option.some.injEq,reduceCtorEq]
    subst ws
    obtain ⟨i,_,lookup⟩ := List.mem_filterMap.mp hy
    split at lookup
    next valid =>
      simp only [Option.some.injEq,Prod.mk.injEq] at lookup
      rw [←lookup.2]
      exact prev i valid
    next => contradiction

def caseSpan (p : Nat → Bool) : Nat → Nat → Bool
  | 0,_ => true
  | n+1,i => p i && caseSpan p n (i+1)

theorem spanValid {p n i} (h : caseSpan p n i=true) (j : Nat)
    (lo : i ≤ j) (hi : j < i+n) : p j=true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    simp only [caseSpan,Bool.and_eq_true] at h
    by_cases e : j=i
    · simpa [e] using h.1
    · exact ih h.2 (by omega) (by omega)

def rangeCases (m : Nat) (seed : List Decor) (cs : List SliceCode) (k depth : Nat)
    (below layer : Cases) (start n : Nat) :=
  caseSpan (fun i => caseCheck m seed cs k depth below (layer.2 i)) n start

theorem concatChecks {p n a b} (h : caseSpan p a n=true)
    (h' : caseSpan p b (n+a)=true) : caseSpan p (a+b) n=true := by
  induction a generalizing n with
  | zero => simpa using h'
  | succ a ih =>
    simp only [caseSpan,Bool.and_eq_true] at h
    rw [Nat.succ_add]
    simp only [caseSpan,Bool.and_eq_true]
    exact ⟨h.1,ih h.2 (by simpa only [Nat.succ_add,Nat.add_succ] using h')⟩

theorem joinRange {m seed cs k depth below layer start a b}
    (x : rangeCases m seed cs k depth below layer start a=true)
    (y : rangeCases m seed cs k depth below layer (start+a) b=true) :
    rangeCases m seed cs k depth below layer start (a+b)=true := concatChecks x y

theorem caseLevel_ok {m p q seed cs k depth below layer n}
    (pairs : properPairs (graphGoal m) (asRow p) (asRow q))
    (faith : ∀ w ∈ seed, faithful (asRow p) (asRow q) w)
    (good : certifiedCuts m cs)
    (prev : caseLevel (graphGoal m) seed (k-1) (depth+1) below)
    (sz : layer.1 ≤ n)
    (h : rangeCases m seed cs k depth below layer 0 n=true) :
    caseLevel (graphGoal m) seed k depth layer := by
  intro i hi
  have ok := spanValid h i (Nat.zero_le _) (by omega)
  exact caseCheck_ok pairs faith good prev ok

def scuts312 : List SliceCode := []
theorem scert312 : certifiedCuts 312 scuts312 := by intro c h; cases h
def sgSamples312 : Array (Bits × Bits) := #[(0x0,0x0),(0x0,0x0),(0x0,0x0),(0xdffff0fff8bcdf8edffff0fff8bcdf8edffff0fff8bcdf8edffff0fff8bcdf8edffff0fff8bcdf8edffff0fff8bcdf8edffff0fff8bcdf8edffff0fff8bcdf8edffff0fff8bcdf8edffff0fff8bcdf8edffff0fff8bcdf8edffff0fff8bcdf8e,0x20480a401889870220480a401889870220480a401889870220480a401889870220480a401889870220480a401889870220480a401889870220480a401889870220480a401889870220480a401889870220480a401889870220480a4018898702),(0x7adedcdb7e64cca77adedcdb7e64cca77adedcdb7e64cca77adedcdb7e64cca77adedcdb7e64cca77adedcdb7e64cca77adedcdb7e64cca77adedcdb7e64cca77adedcdb7e64cca77adedcdb7e64cca77adedcdb7e64cca77adedcdb7e64cca7,0x85914109407678a585914109407678a585914109407678a585914109407678a585914109407678a585914109407678a585914109407678a585914109407678a585914109407678a585914109407678a585914109407678a585914109407678a5),(0xf11d7febd7c326f1f11d7febd7c326f1f11d7febd7c326f1f11d7febd7c326f1f11d7febd7c326f1f11d7febd7c326f1f11d7febd7c326f1f11d7febd7c326f1f11d7febd7c326f1f11d7febd7c326f1f11d7febd7c326f1f11d7febd7c326f1,0x8e708231219e6b008e708231219e6b008e708231219e6b008e708231219e6b008e708231219e6b008e708231219e6b008e708231219e6b008e708231219e6b008e708231219e6b008e708231219e6b008e708231219e6b008e708231219e6b0),(0x0,0x0),(0x0,0x0),(0xbffd3f25fffb337dbffd3f25fffb337dbffd3f25fffb337dbffd3f25fffb337dbffd3f25fffb337dbffd3f25fffb337dbffd3f25fffb337dbffd3f25fffb337dbffd3f25fffb337dbffd3f25fffb337dbffd3f25fffb337dbffd3f25fffb337d,0x4100d000e406104d4100d000e406104d4100d000e406104d4100d000e406104d4100d000e406104d4100d000e406104d4100d000e406104d4100d000e406104d4100d000e406104d4100d000e406104d4100d000e406104d4100d000e406104d)]
def sgP312 (j : Nat) := (sgSamples312[j]?.getD (0,0)).1
def sgN312 (j : Nat) := (sgSamples312[j]?.getD (0,0)).2
def sgBase312 := decorateSigned 312 sgP312 sgN312
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sgPairs312 : properPairs (graphGoal 312) (asRow sgP312) (asRow sgN312) :=
  chart_pairs (m:=312) (p:=sgP312) (q:=sgN312) (by decide +kernel) (by decide +kernel)

def sl312_3b0 : Array CaseCode := #[(529,29,[],[])]
def sl312_3 : Cases := (1,fun i => (sl312_3b0)[i % 16]?.getD default)
def scan312_3 := rangeCases 312 sgBase312 scuts312 3 1 emptyCases sl312_3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck312_3_0 : scan312_3 0 1=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sv312_3 : caseLevel (graphGoal 312) sgBase312 3 1 sl312_3 :=
  caseLevel_ok sgPairs312 (decorateSigned_ok 312 _ _) scert312 (by intro i h; exact (Nat.not_lt_zero i h).elim) (by decide +kernel) ck312_3_0

def sl312_4b0 : Array CaseCode := #[(0,15,[],[0])]
def sl312_4 : Cases := (1,fun i => (sl312_4b0)[i % 16]?.getD default)
def scan312_4 := rangeCases 312 sgBase312 scuts312 4 0 sl312_3 sl312_4
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck312_4_0 : scan312_4 0 1=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sv312_4 : caseLevel (graphGoal 312) sgBase312 4 0 sl312_4 :=
  caseLevel_ok sgPairs312 (decorateSigned_ok 312 _ _) scert312 sv312_3 (by decide +kernel) ck312_4_0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem signedLow312 : Lower (signedRoots 312) (graphGoal 312) 5 := by
  apply finishLower (signedPairs (graphPairs 312 12893503488)) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel)
  let root := sl312_4.2 0
  have eq : (caseValues sgBase312 0 root).toFinset=(signedRoots 312).toFinset := by decide +kernel
  exact eq ▸ sv312_4 0 (by decide)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem signedLow305 : Lower (signedRoots 305) (graphGoal 305) 5 :=
  lower_map (ms:=([48,133] : List Nat).map swapRows) (base:=signedRoots 312) (G:=graphGoal 312) (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) signedLow312

def scuts281 : List SliceCode := []
theorem scert281 : certifiedCuts 281 scuts281 := by intro c h; cases h
def sgSamples281 : Array (Bits × Bits) := #[(0xbe8bd7edbe6b0d56be8bd7edbe6b0d56be8bd7edbe6b0d56be8bd7edbe6b0d56be8bd7edbe6b0d56be8bd7edbe6b0d56be8bd7edbe6b0d56be8bd7edbe6b0d56be8bd7edbe6b0d56be8bd7edbe6b0d56be8bd7edbe6b0d56be8bd7edbe6b0d56,0x40548ccc2413ec5440548ccc2413ec5440548ccc2413ec5440548ccc2413ec5440548ccc2413ec5440548ccc2413ec5440548ccc2413ec5440548ccc2413ec5440548ccc2413ec5440548ccc2413ec5440548ccc2413ec5440548ccc2413ec54),(0x0,0x0),(0x0,0x0),(0xdbfeef7ecdf4feb9dbfeef7ecdf4feb9dbfeef7ecdf4feb9dbfeef7ecdf4feb9dbfeef7ecdf4feb9dbfeef7ecdf4feb9dbfeef7ecdf4feb9dbfeef7ecdf4feb9dbfeef7ecdf4feb9dbfeef7ecdf4feb9dbfeef7ecdf4feb9dbfeef7ecdf4feb9,0x244002d08021ce80244002d08021ce80244002d08021ce80244002d08021ce80244002d08021ce80244002d08021ce80244002d08021ce80244002d08021ce80244002d08021ce80244002d08021ce80244002d08021ce80244002d08021ce80),(0xf677f7fb777f4b4ff677f7fb777f4b4ff677f7fb777f4b4ff677f7fb777f4b4ff677f7fb777f4b4ff677f7fb777f4b4ff677f7fb777f4b4ff677f7fb777f4b4ff677f7fb777f4b4ff677f7fb777f4b4ff677f7fb777f4b4ff677f7fb777f4b4f,0x9084120424c110b09084120424c110b09084120424c110b09084120424c110b09084120424c110b09084120424c110b09084120424c110b09084120424c110b09084120424c110b09084120424c110b09084120424c110b09084120424c110b),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x79fbcaf5ef80b4be79fbcaf5ef80b4be79fbcaf5ef80b4be79fbcaf5ef80b4be79fbcaf5ef80b4be79fbcaf5ef80b4be79fbcaf5ef80b4be79fbcaf5ef80b4be79fbcaf5ef80b4be79fbcaf5ef80b4be79fbcaf5ef80b4be79fbcaf5ef80b4be,0x801a35210d1e303e801a35210d1e303e801a35210d1e303e801a35210d1e303e801a35210d1e303e801a35210d1e303e801a35210d1e303e801a35210d1e303e801a35210d1e303e801a35210d1e303e801a35210d1e303e801a35210d1e303e)]
def sgP281 (j : Nat) := (sgSamples281[j]?.getD (0,0)).1
def sgN281 (j : Nat) := (sgSamples281[j]?.getD (0,0)).2
def sgBase281 := decorateSigned 281 sgP281 sgN281
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sgPairs281 : properPairs (graphGoal 281) (asRow sgP281) (asRow sgN281) :=
  chart_pairs (m:=281) (p:=sgP281) (q:=sgN281) (by decide +kernel) (by decide +kernel)

def sl281_3b0 : Array CaseCode := #[(546,27,[],[])]
def sl281_3 : Cases := (1,fun i => (sl281_3b0)[i % 16]?.getD default)
def scan281_3 := rangeCases 281 sgBase281 scuts281 3 1 emptyCases sl281_3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck281_3_0 : scan281_3 0 1=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sv281_3 : caseLevel (graphGoal 281) sgBase281 3 1 sl281_3 :=
  caseLevel_ok sgPairs281 (decorateSigned_ok 281 _ _) scert281 (by intro i h; exact (Nat.not_lt_zero i h).elim) (by decide +kernel) ck281_3_0

def sl281_4b0 : Array CaseCode := #[(0,15,[],[0])]
def sl281_4 : Cases := (1,fun i => (sl281_4b0)[i % 16]?.getD default)
def scan281_4 := rangeCases 281 sgBase281 scuts281 4 0 sl281_3 sl281_4
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck281_4_0 : scan281_4 0 1=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sv281_4 : caseLevel (graphGoal 281) sgBase281 4 0 sl281_4 :=
  caseLevel_ok sgPairs281 (decorateSigned_ok 281 _ _) scert281 sv281_3 (by decide +kernel) ck281_4_0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem signedLow281 : Lower (signedRoots 281) (graphGoal 281) 5 := by
  apply finishLower (signedPairs (graphPairs 281 12884918276)) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel)
  let root := sl281_4.2 0
  have eq : (caseValues sgBase281 0 root).toFinset=(signedRoots 281).toFinset := by decide +kernel
  exact eq ▸ sv281_4 0 (by decide)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem signedLow57 : Lower (signedRoots 57) (graphGoal 57) 5 :=
  lower_map (ms:=([133,48] : List Nat).map swapRows) (base:=signedRoots 281) (G:=graphGoal 281) (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) signedLow281

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem signedLow297 : Lower (signedRoots 297) (graphGoal 297) 4 :=
  lower_map (ms:=([130,81] : List Nat).map swapRows) (base:=vars 15) (G:=graphGoal 15) (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) low15

def scuts313 : List SliceCode := [(1,0,5),(8,0,5),(16,0,4),(32,0,5),(256,0,5)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem scert313 : certifiedCuts 313 scuts313 := by
  intro c hc
  simp only [scuts313,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · exact signedColumn (m:=313) (z:=1) (o:=0) (q:=312) (s:=0) (base:=5) (L:=5) signedLow312 (by decide +kernel)
  · exact signedColumn (m:=313) (z:=8) (o:=0) (q:=305) (s:=0) (base:=5) (L:=5) signedLow305 (by decide +kernel)
  · exact signedColumn (m:=313) (z:=16) (o:=0) (q:=297) (s:=0) (base:=4) (L:=4) signedLow297 (by decide +kernel)
  · exact signedColumn (m:=313) (z:=32) (o:=0) (q:=281) (s:=0) (base:=5) (L:=5) signedLow281 (by decide +kernel)
  · exact signedColumn (m:=313) (z:=256) (o:=0) (q:=57) (s:=0) (base:=5) (L:=5) signedLow57 (by decide +kernel)
def sgSamples313 : Array (Bits × Bits) := #[(0xfffb2b12c5a2a7964677d6f3dd6defdd76e0dfc6137379ef6fdefc50e1fff656258b454f2c8cefade7badbdfbaedc1bf8c26e6f3dedfbdf8a1c3ffecac4b168a9e5919df5bcf75b7bf75db837f184dcde7bdbf7bf14387ffd958962d153cb23,0x92a244a31a807844788240d01901024828408128c2244a450008850c01254489463500f088f10481a032020490508102518448948a00110a18024a89128c6a01e111e209034064040920a10204a308912914002214300495122518d403c223),(0x0,0x0),(0x0,0x0),(0xf19dff4ad10593ba8b397f70efbaf77ce9a7e87bbafffde1da93b15f45e33bfe95a20b27751672fee1df75eef9d34fd0f775fffbc3b52762be8bc677fd2b44164eea2ce5fdc3beebddf3a69fa1eeebfff7876a4ec57d178ceffa56882c9dd459,0x900d22145912d21a0926808b91000084505898b50801084810c0204641201a4428b225a434124d011722000108a0b1316a100210902180408c8240348851644b4868249a022e44000211416262d4200421204300811904806910a2c89690d049),(0x7b2cf7533414b9c706bf9ada997fedfc65b8eee69a7f0f57f77ccebadef659eea66829738e0d7f35b532ffdbf8cb71ddcd34fe1eafeef99d75bdecb3dd4cd052e71c1afe6b6a65ffb7f196e3bb9a69fc3d5fddf33aeb7bd967ba99a0a5ce3835,0x6120142b04e52985028065242a00820883810548441802258a10c23002c240285609ca530a0500ca485401041107020a908830044b1421846005848050ac1394a6140a019490a80208220e04152110600896284308c00b0900a15827294c2814),(0xf6eb6ca40aea471778dbaceff6bfeb2f725fbf096f9c66bbf7c78ae5f3edd6d94815d48e2ef1b759dfed7fd65ee4bf7e12df38cd77ef8f15cbe7dbadb2902ba91c5de36eb3bfdaffacbdc97efc25be719aefdf1e2b97cfb75b6520575238bbc6,0x520840985cc44707280450182940103024d10858500588940243824080a4108130b9888e0e5008a0305280206049a210b0a00b112804870481014821026173111c1ca0114060a50040c09344216140162250090e090202904204c2e622383940),(0x0,0x0),(0x0,0x0),(0xdc321f8cc3a14cec99d7f39dff7d52eee8f39fb367f0dcff2b9a73f7bdb8643f19874299d933afe73bfefaa5ddd1e73f66cfe1b9fe5734e7ef7b70c87e330e8533b2675fce77fdf54bbba3ce7ecd9fc373fcae69cfdef6e190fc661d0a6764ce,0xc201d63a22908e090c80c400088ee018102010082fa2620252001811418403ac7445211c1219018800111dc030204020105f44c404a400302283080758e88a42382432031000223b806040804020be8988094800604506100eb1d1148470486)]
def sgP313 (j : Nat) := (sgSamples313[j]?.getD (0,0)).1
def sgN313 (j : Nat) := (sgSamples313[j]?.getD (0,0)).2
def sgBase313 := decorateSigned 313 sgP313 sgN313
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sgPairs313 : properPairs (graphGoal 313) (asRow sgP313) (asRow sgN313) :=
  chart_pairs (m:=313) (p:=sgP313) (q:=sgN313) (by decide +kernel) (by decide +kernel)

def sl313_4b0 : Array CaseCode := #[(643909904,155,[],[])]
def sl313_4 : Cases := (1,fun i => (sl313_4b0)[i % 16]?.getD default)
def scan313_4 := rangeCases 313 sgBase313 scuts313 4 3 emptyCases sl313_4
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck313_4_0 : scan313_4 0 1=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sv313_4 : caseLevel (graphGoal 313) sgBase313 4 3 sl313_4 :=
  caseLevel_ok sgPairs313 (decorateSigned_ok 313 _ _) scert313 (by intro i h; exact (Nat.not_lt_zero i h).elim) (by decide +kernel) ck313_4_0

def sl313_5b0 : Array CaseCode := #[(524834,122,[(0,1)],[]),
(279074,123,[(2,0)],[]),
(344610,123,[],[]),
(311842,123,[],[]),
(328226,123,[(3,1)],[]),
(542242,121,[(0,1)],[]),
(345634,123,[],[]),
(312866,123,[(4,1)],[]),
(329250,123,[],[]),
(316962,123,[(0,1)],[]),
(333346,123,[(1,1)],[]),
(577058,115,[(0,1)],[]),
(331298,123,[],[]),
(594466,107,[(0,1)],[]),
(542208,124,[],[]),
(577024,118,[],[])]
def sl313_5b16 : Array CaseCode := #[(594432,110,[],[]),
(84240,91,[],[0]),
(577041,117,[],[]),
(594449,109,[],[]),
(594483,103,[],[])]
def sl313_5 : Cases := (21,fun i => ((if i<16 then sl313_5b0 else sl313_5b16))[i % 16]?.getD default)
def scan313_5 := rangeCases 313 sgBase313 scuts313 5 2 sl313_4 sl313_5
theorem j313_5 (o a b : Nat) (x : scan313_5 o a=true) (y : scan313_5 (o+a) b=true) : scan313_5 o (a+b)=true := @joinRange 313 sgBase313 scuts313 5 2 sl313_4 sl313_5 o a b x y
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck313_5_0 : scan313_5 0 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck313_5_8 : scan313_5 8 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck313_5_16 : scan313_5 16 5=true := by decide +kernel
theorem ck313_5_0m16 : scan313_5 0 16=true := j313_5 0 8 8 ck313_5_0 ck313_5_8
theorem ck313_5_0m21 : scan313_5 0 21=true := j313_5 0 16 5 ck313_5_0m16 ck313_5_16
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sv313_5 : caseLevel (graphGoal 313) sgBase313 5 2 sl313_5 :=
  caseLevel_ok sgPairs313 (decorateSigned_ok 313 _ _) scert313 sv313_4 (by decide +kernel) ck313_5_0m21

def sl313_6b0 : Array CaseCode := #[(546,63,[(2,0),(0,1),(1,1),(3,1),(4,1)],[]),
(546,59,[(0,1),(1,1),(3,1),(4,1),(2,0),(0,0)],[0,1,2,3,4,5,6,7,8,9,10,11,12,13]),
(258,63,[(2,0)],[]),
(274,63,[(2,0)],[]),
(306,63,[(2,0),(4,0)],[]),
(322,63,[(2,0),(3,0)],[]),
(512,62,[(0,0)],[0,14,15,16]),
(272,63,[],[1,17]),
(304,63,[],[3]),
(320,63,[(3,0)],[4]),
(529,61,[(0,0)],[5,14,18,19]),
(305,63,[(4,0)],[7]),
(321,63,[],[8]),
(563,55,[(0,0)],[11,15,18,20]),
(323,63,[],[12]),
(580,47,[(0,0)],[13,16,19,20])]
def sl313_6 : Cases := (16,fun i => (sl313_6b0)[i % 16]?.getD default)
def scan313_6 := rangeCases 313 sgBase313 scuts313 6 1 sl313_5 sl313_6
theorem j313_6 (o a b : Nat) (x : scan313_6 o a=true) (y : scan313_6 (o+a) b=true) : scan313_6 o (a+b)=true := @joinRange 313 sgBase313 scuts313 6 1 sl313_5 sl313_6 o a b x y
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck313_6_0 : scan313_6 0 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck313_6_8 : scan313_6 8 8=true := by decide +kernel
theorem ck313_6_0m16 : scan313_6 0 16=true := j313_6 0 8 8 ck313_6_0 ck313_6_8
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sv313_6 : caseLevel (graphGoal 313) sgBase313 6 1 sl313_6 :=
  caseLevel_ok sgPairs313 (decorateSigned_ok 313 _ _) scert313 sv313_5 (by decide +kernel) ck313_6_0m16

def sl313_7b0 : Array CaseCode := #[(0,31,[(0,0),(1,0),(3,0),(4,0)],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15])]
def sl313_7 : Cases := (1,fun i => (sl313_7b0)[i % 16]?.getD default)
def scan313_7 := rangeCases 313 sgBase313 scuts313 7 0 sl313_6 sl313_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck313_7_0 : scan313_7 0 1=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sv313_7 : caseLevel (graphGoal 313) sgBase313 7 0 sl313_7 :=
  caseLevel_ok sgPairs313 (decorateSigned_ok 313 _ _) scert313 sv313_6 (by decide +kernel) ck313_7_0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem signedLow313 : Lower (signedRoots 313) (graphGoal 313) 8 := by
  apply finishLower (signedPairs (graphPairs 313 12884918276)) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel)
  let root := sl313_7.2 0
  have eq : (caseValues sgBase313 0 root).toFinset=(signedRoots 313).toFinset := by decide +kernel
  exact eq ▸ sv313_7 0 (by decide)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem signedLow428 : Lower (signedRoots 428) (graphGoal 428) 7 :=
  lower_map (ms:=([130,116,83,49,32] : List Nat).map swapRows) (base:=vars 31) (G:=graphGoal 31) (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) low31

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem signedLow156 : Lower (signedRoots 156) (graphGoal 156) 5 :=
  lower_map (ms:=([130,117] : List Nat).map swapRows) (base:=signedRoots 312) (G:=graphGoal 312) (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) signedLow312

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem signedLow420 : Lower (signedRoots 420) (graphGoal 420) 4 :=
  lower_map (ms:=([113,82,131,32] : List Nat).map swapRows) (base:=vars 15) (G:=graphGoal 15) (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) low15

def scuts444 : List SliceCode := [(0,16,5),(16,0,7),(132,0,5),(288,0,5)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem scert444 : certifiedCuts 444 scuts444 := by
  intro c hc
  simp only [scuts444,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact signedColumn (m:=444) (z:=0) (o:=16) (q:=420) (s:=8) (base:=4) (L:=5) signedLow420 (by decide +kernel)
  · exact signedColumn (m:=444) (z:=16) (o:=0) (q:=428) (s:=0) (base:=7) (L:=7) signedLow428 (by decide +kernel)
  · exact signedColumn (m:=444) (z:=132) (o:=0) (q:=312) (s:=0) (base:=5) (L:=5) signedLow312 (by decide +kernel)
  · exact signedColumn (m:=444) (z:=288) (o:=0) (q:=156) (s:=0) (base:=5) (L:=5) signedLow156 (by decide +kernel)
def sgSamples444 : Array (Bits × Bits) := #[(0x0,0x0),(0x0,0x0),(0xbab6fd5b6abcfc875abd95cdfe95bbbd2f667dd7e4175962e59cddebdf8cbc8ecfdd6afd4cf4eec5498687b275b3f9825925a1920b78fcda3eb977f78e7dfc9a5fb0960cde5adbef9269d521b4e8d537dd0873ff518ba4c522c0964dd3275922,0x141028580100b5940422a108101905030d544288542309c1b52863422300a1ce019ca8418bc01200b250102a30341bc0c43d3100034041a3081060a304a4a884c08908c50c81315a2790532a0c811268710227d410398feb0008644c3075120),(0xf07fbfce77ffa27c6efdce7b95f7dbbeb36fce3f44effbcf5f61ef8ef3fffe2ffe62272bc9d914fa99fddfaff77fdbfd9faeedc7c5f86fdc9b6f1fa05bac6ef4c461bdeb4c597d9cc5f4a904c7212f55a6ecb532affeb1a273536dbea2910d9a,0xe824020308014800008102908040089400000141a1008018000000114000100020025200341d8010040466804100002202000091008a12042220020022000000061000100100c080004a00406000840002810028288060003ff412a20100c82),(0xbc5ec1fd13fdd2745b3a5d3bb54972fd45c3a29892f48bdd24d5f4de7f5a535c35a3cd623d0d159a9a7fb5fc0c775a5c5ddee55e6e018dd7c1b023be807a57b7eefdabb3235333a5e65aa6c3688df7598ea45de1cf60000250037450c9fce518,0x412196024c07ea45a88721d4833207228e535660650f37b41f0a4526680f3803d4981204408e27188235399720e87e44554e206283b01c43a81497d0809bf2ed489a82b0326333a4ed510683e0dfe619c3c42de51c2239fffc003450c9ece118),(0x777ffe73a7f37dd4bb1b6ba7f28e3ee7fcbdf7223ba977b9ed72f777b6e23dfa0768b9b5fe97e91c362b77f93befc6ede1f513baf0376129e466ea5ff5d3db3d78df5a7461a45f683c0eeada3b5fdfacb3b30e2dc08eca188c2cc16e0d4af34d,0x890420c190692ab46100e4000008819084008258043b88c240600001800011b9108640059306908403204613006c12c0388200f102905121014802a7a00809010894a0041a14920b80888202ac105003290083cc00a940ea30dc14e0102a30c),(0x0,0x0),(0x4d9743dbddfacd83bf435ab99bb7ea51fdf593e5ef37ded435bf9ee3fc04bbfc759d78cfa57ff78ffba41a72e892fae3e4fd90e3fb4797abf1b7dd1fe6e94043dbd8475df2a6a3c746e77eed6bb28aa358c9d8cfd2e90c4d04a812e35cf622b3,0xb22cac2264a10004182d9106564a0422020ab01002204043400000c1844f740004020049a40086c71440680c4c900040702408a0cd00a080c66059940095012480500551820400c2048262414132aa894848500038e063014cf210a11cf00093),(0x6796cf64778f13ab4550f3acfffcfdeaae4b2d1e9f2836f9ffdaeb7fd861313fb6d9af139e761bed0e5aec95da5d6f54e7330e795cff0b0b264bb7c2759bfbceb5e7c58ba7042c7539891756774ffa6fe15fefa92114d33089148f907569d0d4,0xa04834d38208484098824094149320628205f2c0018441025961878203dee0c06c4488cb240204d2ab0c819083092a108c1000004654004ca4c07cd0049163470806059a24482057010110531102f2adc141e5c1252569f15c000e9054695050)]
def sgP444 (j : Nat) := (sgSamples444[j]?.getD (0,0)).1
def sgN444 (j : Nat) := (sgSamples444[j]?.getD (0,0)).2
def sgBase444 := decorateSigned 444 sgP444 sgN444
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sgPairs444 : properPairs (graphGoal 444) (asRow sgP444) (asRow sgN444) :=
  chart_pairs (m:=444) (p:=sgP444) (q:=sgN444) (by decide +kernel) (by decide +kernel)

def sl444_5b0 : Array CaseCode := #[(661919762,315,[],[]),
(662001682,315,[],[])]
def sl444_5 : Cases := (2,fun i => (sl444_5b0)[i % 16]?.getD default)
def scan444_5 := rangeCases 444 sgBase444 scuts444 5 3 emptyCases sl444_5
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck444_5_0 : scan444_5 0 2=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sv444_5 : caseLevel (graphGoal 444) sgBase444 5 3 sl444_5 :=
  caseLevel_ok sgPairs444 (decorateSigned_ok 444 _ _) scert444 (by intro i h; exact (Nat.not_lt_zero i h).elim) (by decide +kernel) ck444_5_0

def sl444_6b0 : Array CaseCode := #[(628754,187,[(0,0),(1,0)],[]),
(268306,187,[],[0]),
(350226,187,[],[1]),
(524306,250,[],[]),
(541714,249,[],[]),
(576530,243,[],[]),
(593938,235,[],[]),
(611346,219,[],[]),
(542208,252,[],[]),
(577024,246,[],[]),
(611840,222,[],[]),
(100624,187,[(0,0)],[]),
(577041,245,[],[]),
(594449,237,[],[]),
(611857,221,[],[]),
(100657,187,[(0,0)],[])]
def sl444_6b16 : Array CaseCode := #[(100673,187,[(0,0)],[]),
(100689,187,[(0,0)],[]),
(594483,231,[],[]),
(611908,207,[],[])]
def sl444_6 : Cases := (20,fun i => ((if i<16 then sl444_6b0 else sl444_6b16))[i % 16]?.getD default)
def scan444_6 := rangeCases 444 sgBase444 scuts444 6 2 sl444_5 sl444_6
theorem j444_6 (o a b : Nat) (x : scan444_6 o a=true) (y : scan444_6 (o+a) b=true) : scan444_6 o (a+b)=true := @joinRange 444 sgBase444 scuts444 6 2 sl444_5 sl444_6 o a b x y
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck444_6_0 : scan444_6 0 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck444_6_8 : scan444_6 8 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck444_6_16 : scan444_6 16 4=true := by decide +kernel
theorem ck444_6_0m16 : scan444_6 0 16=true := j444_6 0 8 8 ck444_6_0 ck444_6_8
theorem ck444_6_0m20 : scan444_6 0 20=true := j444_6 0 16 4 ck444_6_0m16 ck444_6_16
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sv444_6 : caseLevel (graphGoal 444) sgBase444 6 2 sl444_6 :=
  caseLevel_ok sgPairs444 (decorateSigned_ok 444 _ _) scert444 sv444_5 (by decide +kernel) ck444_6_0m20

def sl444_7b0 : Array CaseCode := #[(18,123,[(0,0)],[0,1,2,3,4,5,6,7]),
(512,126,[(1,1),(2,0),(1,0)],[3,8,9,10]),
(272,127,[(1,1)],[11]),
(304,127,[(1,1),(2,0)],[]),
(336,127,[(1,1),(1,0)],[]),
(529,127,[(1,1),(1,0)],[4]),
(529,125,[(1,1),(1,0)],[8,12,13,14]),
(305,127,[(1,1),(3,0)],[15]),
(321,127,[(1,1),(2,0)],[16]),
(337,127,[(1,1)],[17]),
(563,119,[(1,1),(1,0),(3,0)],[5,9,12,18]),
(323,127,[(1,1)],[]),
(580,111,[(1,1),(1,0),(2,0)],[6,13,18,19]),
(340,127,[(1,1),(3,0)],[]),
(597,95,[(3,0),(1,1),(1,0)],[7,10,14,19])]
def sl444_7 : Cases := (15,fun i => (sl444_7b0)[i % 16]?.getD default)
def scan444_7 := rangeCases 444 sgBase444 scuts444 7 1 sl444_6 sl444_7
theorem j444_7 (o a b : Nat) (x : scan444_7 o a=true) (y : scan444_7 (o+a) b=true) : scan444_7 o (a+b)=true := @joinRange 444 sgBase444 scuts444 7 1 sl444_6 sl444_7 o a b x y
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck444_7_0 : scan444_7 0 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck444_7_8 : scan444_7 8 7=true := by decide +kernel
theorem ck444_7_0m15 : scan444_7 0 15=true := j444_7 0 8 7 ck444_7_0 ck444_7_8
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sv444_7 : caseLevel (graphGoal 444) sgBase444 7 1 sl444_7 :=
  caseLevel_ok sgPairs444 (decorateSigned_ok 444 _ _) scert444 sv444_6 (by decide +kernel) ck444_7_0m15

def sl444_8b0 : Array CaseCode := #[(0,63,[(1,0),(2,0),(3,0)],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14])]
def sl444_8 : Cases := (1,fun i => (sl444_8b0)[i % 16]?.getD default)
def scan444_8 := rangeCases 444 sgBase444 scuts444 8 0 sl444_7 sl444_8
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck444_8_0 : scan444_8 0 1=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sv444_8 : caseLevel (graphGoal 444) sgBase444 8 0 sl444_8 :=
  caseLevel_ok sgPairs444 (decorateSigned_ok 444 _ _) scert444 sv444_7 (by decide +kernel) ck444_8_0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem signedLow444 : Lower (signedRoots 444) (graphGoal 444) 9 := by
  apply finishLower (signedPairs (graphPairs 444 13429318400)) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel)
  let root := sl444_8.2 0
  have eq : (caseValues sgBase444 0 root).toFinset=(signedRoots 444).toFinset := by decide +kernel
  exact eq ▸ sv444_8 0 (by decide)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem signedLow177 : Lower (signedRoots 177) (graphGoal 177) 5 :=
  lower_map (ms:=([135,48,117] : List Nat).map swapRows) (base:=signedRoots 312) (G:=graphGoal 312) (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) signedLow312

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem signedLow29 : Lower (signedRoots 29) (graphGoal 29) 5 :=
  lower_map (ms:=([130] : List Nat).map swapRows) (base:=signedRoots 281) (G:=graphGoal 281) (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) signedLow281

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem signedLow172 : Lower (signedRoots 172) (graphGoal 172) 4 :=
  lower_map (ms:=([114,33,83,48] : List Nat).map swapRows) (base:=vars 15) (G:=graphGoal 15) (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) low15

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem signedLow165 : Lower (signedRoots 165) (graphGoal 165) 4 :=
  lower_map (ms:=([114,81,50] : List Nat).map swapRows) (base:=vars 15) (G:=graphGoal 15) (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) low15

def scuts189 : List SliceCode := [(12,0,5),(17,0,4),(24,0,4),(33,0,5),(132,0,5),(160,0,5)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem scert189 : certifiedCuts 189 scuts189 := by
  intro c hc
  simp only [scuts189,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact signedColumn (m:=189) (z:=12) (o:=0) (q:=177) (s:=0) (base:=5) (L:=5) signedLow177 (by decide +kernel)
  · exact signedColumn (m:=189) (z:=17) (o:=0) (q:=172) (s:=0) (base:=4) (L:=4) signedLow172 (by decide +kernel)
  · exact signedColumn (m:=189) (z:=24) (o:=0) (q:=165) (s:=0) (base:=4) (L:=4) signedLow165 (by decide +kernel)
  · exact signedColumn (m:=189) (z:=33) (o:=0) (q:=156) (s:=0) (base:=5) (L:=5) signedLow156 (by decide +kernel)
  · exact signedColumn (m:=189) (z:=132) (o:=0) (q:=57) (s:=0) (base:=5) (L:=5) signedLow57 (by decide +kernel)
  · exact signedColumn (m:=189) (z:=160) (o:=0) (q:=29) (s:=0) (base:=5) (L:=5) signedLow29 (by decide +kernel)
def sgSamples189 := g189samples
def sgP189 (j : Nat) := (sgSamples189[j]?.getD (0,0)).1
def sgN189 (j : Nat) := (sgSamples189[j]?.getD (0,0)).2
def sgBase189 := decorateSigned 189 sgP189 sgN189
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sgPairs189 : properPairs (graphGoal 189) (asRow sgP189) (asRow sgN189) :=
  chart_pairs (m:=189) (p:=sgP189) (q:=sgN189) (by decide +kernel) (by decide +kernel)

def sl189_5b0 : Array CaseCode := #[(661753120,311,[],[])]
def sl189_5 : Cases := (1,fun i => (sl189_5b0)[i % 16]?.getD default)
def scan189_5 := rangeCases 189 sgBase189 scuts189 5 3 emptyCases sl189_5
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck189_5_0 : scan189_5 0 1=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sv189_5 : caseLevel (graphGoal 189) sgBase189 5 3 sl189_5 :=
  caseLevel_ok sgPairs189 (decorateSigned_ok 189 _ _) scert189 (by intro i h; exact (Nat.not_lt_zero i h).elim) (by decide +kernel) ck189_5_0

def sl189_6b0 : Array CaseCode := #[(524851,246,[(3,1)],[]),
(279091,247,[],[]),
(295475,247,[(1,0)],[]),
(344627,247,[(3,1)],[]),
(542259,245,[(3,1)],[]),
(362035,247,[(0,1)],[]),
(329267,247,[(4,1)],[]),
(559667,243,[(3,1)],[]),
(330291,247,[],[]),
(346675,247,[(0,1)],[]),
(334387,247,[(3,1)],[]),
(350771,247,[],[]),
(594483,231,[(3,1)],[]),
(611891,215,[(3,1)],[]),
(542208,252,[],[]),
(559616,250,[],[])]
def sl189_6b16 : Array CaseCode := #[(611840,222,[],[]),
(101664,183,[],[0]),
(594449,237,[],[]),
(594466,235,[],[]),
(611874,219,[],[])]
def sl189_6 : Cases := (21,fun i => ((if i<16 then sl189_6b0 else sl189_6b16))[i % 16]?.getD default)
def scan189_6 := rangeCases 189 sgBase189 scuts189 6 2 sl189_5 sl189_6
theorem j189_6 (o a b : Nat) (x : scan189_6 o a=true) (y : scan189_6 (o+a) b=true) : scan189_6 o (a+b)=true := @joinRange 189 sgBase189 scuts189 6 2 sl189_5 sl189_6 o a b x y
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck189_6_0 : scan189_6 0 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck189_6_8 : scan189_6 8 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck189_6_16 : scan189_6 16 5=true := by decide +kernel
theorem ck189_6_0m16 : scan189_6 0 16=true := j189_6 0 8 8 ck189_6_0 ck189_6_8
theorem ck189_6_0m21 : scan189_6 0 21=true := j189_6 0 16 5 ck189_6_0m16 ck189_6_16
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sv189_6 : caseLevel (graphGoal 189) sgBase189 6 2 sl189_6 :=
  caseLevel_ok sgPairs189 (decorateSigned_ok 189 _ _) scert189 sv189_5 (by decide +kernel) ck189_6_0m21

def sl189_7b0 : Array CaseCode := #[(563,127,[(1,0),(3,1),(0,1),(4,1)],[]),
(563,119,[(3,1),(0,1),(4,1),(1,0),(2,0),(3,0),(5,1)],[0,1,2,3,4,5,6,7,8,9,10,11,12,13]),
(259,127,[(1,0)],[]),
(275,127,[(1,0)],[]),
(291,127,[(1,0)],[]),
(323,127,[(1,0)],[]),
(339,127,[(1,0),(0,0),(3,0)],[]),
(512,126,[(3,0)],[0,14,15,16]),
(272,127,[],[1]),
(288,127,[],[2,17]),
(336,127,[(3,0)],[3]),
(529,125,[(3,0),(0,0),(4,0)],[4,14,18]),
(321,127,[(4,0)],[6]),
(546,123,[(3,0),(0,0)],[7,15,19,20]),
(322,127,[],[8]),
(338,127,[(0,0)],[9])]
def sl189_7b16 : Array CaseCode := #[(580,111,[(3,0),(5,0)],[12,18,19]),
(597,95,[(3,0),(4,0),(5,0)],[13,16,20])]
def sl189_7 : Cases := (18,fun i => ((if i<16 then sl189_7b0 else sl189_7b16))[i % 16]?.getD default)
def scan189_7 := rangeCases 189 sgBase189 scuts189 7 1 sl189_6 sl189_7
theorem j189_7 (o a b : Nat) (x : scan189_7 o a=true) (y : scan189_7 (o+a) b=true) : scan189_7 o (a+b)=true := @joinRange 189 sgBase189 scuts189 7 1 sl189_6 sl189_7 o a b x y
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck189_7_0 : scan189_7 0 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck189_7_8 : scan189_7 8 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck189_7_16 : scan189_7 16 2=true := by decide +kernel
theorem ck189_7_0m16 : scan189_7 0 16=true := j189_7 0 8 8 ck189_7_0 ck189_7_8
theorem ck189_7_0m18 : scan189_7 0 18=true := j189_7 0 16 2 ck189_7_0m16 ck189_7_16
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sv189_7 : caseLevel (graphGoal 189) sgBase189 7 1 sl189_7 :=
  caseLevel_ok sgPairs189 (decorateSigned_ok 189 _ _) scert189 sv189_6 (by decide +kernel) ck189_7_0m18

def sl189_8b0 : Array CaseCode := #[(0,63,[(3,0),(0,0),(4,0),(5,0)],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])]
def sl189_8 : Cases := (1,fun i => (sl189_8b0)[i % 16]?.getD default)
def scan189_8 := rangeCases 189 sgBase189 scuts189 8 0 sl189_7 sl189_8
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck189_8_0 : scan189_8 0 1=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sv189_8 : caseLevel (graphGoal 189) sgBase189 8 0 sl189_8 :=
  caseLevel_ok sgPairs189 (decorateSigned_ok 189 _ _) scert189 sv189_7 (by decide +kernel) ck189_8_0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem signedLow189 : Lower (signedRoots 189) (graphGoal 189) 9 := by
  apply finishLower (signedPairs (graphPairs 189 536879876)) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel)
  let root := sl189_8.2 0
  have eq : (caseValues sgBase189 0 root).toFinset=(signedRoots 189).toFinset := by decide +kernel
  exact eq ▸ sv189_8 0 (by decide)

def scuts437 : List SliceCode := [(0,4,6),(0,16,5),(17,0,4),(132,0,5),(260,0,5)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem scert437 : certifiedCuts 437 scuts437 := by
  intro c hc
  simp only [scuts437,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · exact signedColumn (m:=437) (z:=0) (o:=4) (q:=305) (s:=128) (base:=5) (L:=6) signedLow305 (by decide +kernel)
  · exact signedColumn (m:=437) (z:=0) (o:=16) (q:=420) (s:=1) (base:=4) (L:=5) signedLow420 (by decide +kernel)
  · exact signedColumn (m:=437) (z:=17) (o:=0) (q:=420) (s:=0) (base:=4) (L:=4) signedLow420 (by decide +kernel)
  · exact signedColumn (m:=437) (z:=132) (o:=0) (q:=305) (s:=0) (base:=5) (L:=5) signedLow305 (by decide +kernel)
  · exact signedColumn (m:=437) (z:=260) (o:=0) (q:=177) (s:=0) (base:=5) (L:=5) signedLow177 (by decide +kernel)
def sgSamples437 : Array (Bits × Bits) := #[(0x1dc9afcaf8bffcbbbf27e2da2f7c76d597dfdfabfc56d9fe97797a3e7f8772ac4bbff4f64bfd3b90a671db3659fcc2f9b7bf487ffec787bbcc2379dd5afdf5e43f61963b0fd62e38ee9cb4756b527fedd5a9889993f1d3447912f02e312f5b1b,0x122451a00101a890c118348482a0012059602000c2b80a0321b0891914084a0004780050082c80114100f4000151c22010120a443a5341829064c4070ada804036701410018e861148940061024603650829489310f090c3e232800e1124531a),(0x0,0x0),(0x57fd4453396fed70a2cafce7e1e7f67eeddcb594f92f5e2ff24f69c12802ffcca5e22bab9fe8d25d8cbfb639774fddd5b9d1fe626d96cf05f199e6ccff79bb3de31d5a35f1ea87c42175371ec73f2f539cbb3794aa68083200275a904989b7de,0x21cc66344672580823a41640323801221e00d1cc2651211c0d3016294242732d5140609a9c02c8400cc4a701599128c161814820108d7e816a2a083df080a31c83180a7380e8804240318316f75aa81984aa27518aea05ab3d9758904889325e),(0x0,0x0),(0x38bff3bb36ffbff25d3eeceb86b89ef0fb53718b7c9508d7dd8dd6de4fe6ecc249d2fedf08cf7ceebc6c19a053817abeec8f8b57bfe1f2be24cf53f6fbddb48c4867cb9b9e006d9e6e6b52f73cdbbf8bf5a1282c997cb0440913ef22ba0b7461,0xe5c00e08b094446422c503035c1732170005d6ed1d42a408c4484000ca7224828987770bb68318c0886303cbd628005d4e0544128584a41c0082038004015e8c810f438b9a0131ce226a12863c31dc98d706302c8500273c1dcd6f20aa0b2461),(0xe7a65fe7def1cfbdff9133f7fee7ebafb3f71e7bb6edf706fbb2fef6d6790337bebf2423f57f85767f3de7debff5b61b4efffdadbfbe3ad7ebeebaaf6706c75e95cefdc72bd5d0279be7cf881b80f874327ceb77cfc77789f6c95dcdcef40839,0x18020400420640080000180204860045e4204400a80208108082002409a00110a8044100040481090040a019004089400a04241000088839a80400000a8108c88b081110060100c40a99006000140002408a0640081c055c40c4800801),(0x0,0x0),(0x61fed5ddbf6b3c7d5edf9d3937a5ea5edf3bf1ece73bb7bbeefe01cfb35effdb295a4f5b7eadeeed5ab684ff257acf6e7bb3da0845b9fd7d7bddf5099f2e1a3b6efb3cb0f52f23d7a8f26b8bccbf1282e95fd6d4a708ecb20665061237f6a7e6,0xd8211000888886808018e00600c6b00121122a13182a1c428000a85600b188000812850042383609c030403a2608c4020a26a3d443528020804580000b1414a168c3150035040311a84028a100a412a62915d00c65100254c2680202337685a0),(0xc348d8bc2e95d7e7cea8c2a7f2f3ffe92d2f1cfee1cdc945376497abe43f5ab7b4799d3ec603396b47ee7751d617b6bec25dadddf16caf0cd1e9cabeba81437fc04467c50f9adbe8f1b108a1551297dc6a94773f586eb809808aa9d5f94c26b0,0x39926320c54bb8206914577e9fc3605320c4a00b08329503f053ca56780d89a00f40aa520a205eb00a2e86d0261562189f36ad6530082666d551c0121240f33472c62144972ec8f0e0a900644212975d6b94501f6048bff7e3faa195394c26b0)]
def sgP437 (j : Nat) := (sgSamples437[j]?.getD (0,0)).1
def sgN437 (j : Nat) := (sgSamples437[j]?.getD (0,0)).2
def sgBase437 := decorateSigned 437 sgP437 sgN437
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sgPairs437 : properPairs (graphGoal 437) (asRow sgP437) (asRow sgN437) :=
  chart_pairs (m:=437) (p:=sgP437) (q:=sgN437) (by decide +kernel) (by decide +kernel)

def sl437_6b0 : Array CaseCode := #[(546,123,[(2,0),(3,1),(0,1),(1,0),(4,1)],[]),
(2,123,[(1,0)],[]),
(306,123,[(2,0)],[]),
(512,126,[],[]),
(336,95,[(2,0)],[]),
(563,119,[],[])]
def sl437_6 : Cases := (6,fun i => (sl437_6b0)[i % 16]?.getD default)
def scan437_6 := rangeCases 437 sgBase437 scuts437 6 1 emptyCases sl437_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck437_6_0 : scan437_6 0 6=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sv437_6 : caseLevel (graphGoal 437) sgBase437 6 1 sl437_6 :=
  caseLevel_ok sgPairs437 (decorateSigned_ok 437 _ _) scert437 (by intro i h; exact (Nat.not_lt_zero i h).elim) (by decide +kernel) ck437_6_0

def sl437_7b0 : Array CaseCode := #[(0,63,[(3,0),(0,0),(4,0),(1,0)],[0,1,2,3,4,5])]
def sl437_7 : Cases := (1,fun i => (sl437_7b0)[i % 16]?.getD default)
def scan437_7 := rangeCases 437 sgBase437 scuts437 7 0 sl437_6 sl437_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck437_7_0 : scan437_7 0 1=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sv437_7 : caseLevel (graphGoal 437) sgBase437 7 0 sl437_7 :=
  caseLevel_ok sgPairs437 (decorateSigned_ok 437 _ _) scert437 sv437_6 (by decide +kernel) ck437_7_0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem signedLow437 : Lower (signedRoots 437) (graphGoal 437) 8 := by
  apply finishLower (signedPairs (graphPairs 437 22011709188)) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel)
  let root := sl437_7.2 0
  have eq : (caseValues sgBase437 0 root).toFinset=(signedRoots 437).toFinset := by decide +kernel
  exact eq ▸ sv437_7 0 (by decide)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem signedLow396 : Lower (signedRoots 396) (graphGoal 396) 4 :=
  lower_map (ms:=([130,33,131,112] : List Nat).map swapRows) (base:=vars 15) (G:=graphGoal 15) (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) low15

def scuts413 : List SliceCode := [(0,128,6),(16,1,4),(17,0,4),(132,0,5),(257,0,5)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem scert413 : certifiedCuts 413 scuts413 := by
  intro c hc
  simp only [scuts413,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · exact signedColumn (m:=413) (z:=0) (o:=128) (q:=281) (s:=4) (base:=5) (L:=6) signedLow281 (by decide +kernel)
  · exact signedColumn (m:=413) (z:=16) (o:=1) (q:=396) (s:=0) (base:=4) (L:=4) signedLow396 (by decide +kernel)
  · exact signedColumn (m:=413) (z:=17) (o:=0) (q:=396) (s:=0) (base:=4) (L:=4) signedLow396 (by decide +kernel)
  · exact signedColumn (m:=413) (z:=132) (o:=0) (q:=281) (s:=0) (base:=5) (L:=5) signedLow281 (by decide +kernel)
  · exact signedColumn (m:=413) (z:=257) (o:=0) (q:=156) (s:=0) (base:=5) (L:=5) signedLow156 (by decide +kernel)
def sgSamples413 : Array (Bits × Bits) := #[(0x524c5b96f4e9ce4e7b78ca67ee46cf8d1ba32ed7769c9a1c6bfb76d45bc9cb7acdff190370792b9b76b33df9343d79c1eabe27267d8c64cbfffe6abee8ef1768cf2ba82aec3623bd1d7ab215d0ab7518d38fd70dfa1fd0026a01391e10ae6ef6,0xa10200a9a960b34051062810b38dd14b41c8d0184161d5e49181a94814d9921cae52b910491845120405420b05156083041aa1cfcb0a20814078a512322b0748c7211032282633351bb22a11808ab053c38d5aa4c02855d9792d280e00aa4ef6),(0x0,0x0),(0xf7fe1cb1bf7335ff35a586d598af1d3bffaeaf60c67faeb7ffb9ee3d76aca39bb2f0bcf41b9fbce4dbce2c58f8971627fbafcbdd7bd5b5ffc37fc76f7b9f4dd4e269fefb91c2af0fc31576eaad71b85d5858a6ce76acf2f0043ed70345db06af,0x4a810010024303048048412c5f5060c06250001008001828d85201181a280510040001450182808a422125000460a0634ba082897050aa5a03485c081100c2442b6ca4160d40880f030124408161181c101894c0142429021cfa930104da060c),(0xfbb3ffeac3febfffda87b5ffdfb4e6fda6fbfbaaeffcebef3cbedb7ffdb69cadf2125f3effc3c6d94bcffb26cf56ed9f76f97c73cd7feef87e7f7550d5edf923d1bd1704e3ebd37627cdcdddaefd9eb6af65e8f161d84f9d91d9a4e3aa3a9979,0x240a0820200040000923080120000111102280045081059000002806409520048a4100002a501111208e000001030100a401404408200084081601100048008140011000c20712301000c994240482008340282520084019200524c202201061),(0xbe4b273df8fecf0d6efb5a3da077e3df6579755df6add36d97f528f6a37b475a9f0fbeade26debfb2539cff96be9baeb5753c45fecb967c7bf9e7af28da3765f3e876d282f1e6ce3587ef733fa3a5f28bda69d6998172d076a80fbbd5e84e340,0x50c4c042461900b00008052440500420821524a02e1a2a094e285421a3200461502440cc80032a48d1200d5428e00044580016000481c6789680404188900016088629c805180842604c102219704d241c30804819170a2686d0d3315c04a100),(0x0,0x0),(0x0,0x0),(0xe6ec31d3fe5b9bda871c7b0f1ef9b91bfe16e41d86e3b77fe1485f1e527ab75ffeede1eee497b727985416331aef43e0bdf7d798f2d51174f67ba79f769b89bfb072f1f3d3134e89f9697a7a4d8a60e34f5d0a4f16aab0600427664ecf45ac86,0x841acf0d8c04600b5a07828020840124958148626729e480268dd8e4e186a00b6b73e2226069041015dc0232a00d061094572030892d0125b4930207cac121aa909250e1c21a44b038485aaa588c03434dc4481f8288d6fde305644ecb05a882),(0x95f5f967102d92e1dd0b6b4a7f92135f3b2ab9b3fd96e5e9ba92f937cee5b8bf486ecbc2bf2d2c960d7779b65d624dbb44df37b8a7778bda18f81c798f7a873267b8a68c47715c94acf03b6d8ad429a3c37df592cf7e08089143c364b1a2f89c,0x88045092dfd2128722d455acc448c84ec69d6e208214586a45a5c1d91c0a506b402a8b0c50ad24c20b01dd6958fc0e8211801e3ab314705885295c26ac12c17c21eaa68f0500c4c2a4f2324b8a5021b31415d590c3331fe6dffac324b182e89c)]
def sgP413 (j : Nat) := (sgSamples413[j]?.getD (0,0)).1
def sgN413 (j : Nat) := (sgSamples413[j]?.getD (0,0)).2
def sgBase413 := decorateSigned 413 sgP413 sgN413
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sgPairs413 : properPairs (graphGoal 413) (asRow sgP413) (asRow sgN413) :=
  chart_pairs (m:=413) (p:=sgP413) (q:=sgN413) (by decide +kernel) (by decide +kernel)

def sl413_6b0 : Array CaseCode := #[(563,119,[(4,1),(3,1),(1,0),(0,1),(2,0)],[]),
(259,126,[(2,0)],[]),
(288,126,[(1,0)],[]),
(546,123,[],[])]
def sl413_6 : Cases := (4,fun i => (sl413_6b0)[i % 16]?.getD default)
def scan413_6 := rangeCases 413 sgBase413 scuts413 6 1 emptyCases sl413_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck413_6_0 : scan413_6 0 4=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sv413_6 : caseLevel (graphGoal 413) sgBase413 6 1 sl413_6 :=
  caseLevel_ok sgPairs413 (decorateSigned_ok 413 _ _) scert413 (by intro i h; exact (Nat.not_lt_zero i h).elim) (by decide +kernel) ck413_6_0

def sl413_7b0 : Array CaseCode := #[(0,63,[(4,0),(3,0),(0,0),(2,0)],[0,1,2,3])]
def sl413_7 : Cases := (1,fun i => (sl413_7b0)[i % 16]?.getD default)
def scan413_7 := rangeCases 413 sgBase413 scuts413 7 0 sl413_6 sl413_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck413_7_0 : scan413_7 0 1=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sv413_7 : caseLevel (graphGoal 413) sgBase413 7 0 sl413_7 :=
  caseLevel_ok sgPairs413 (decorateSigned_ok 413 _ _) scert413 sv413_6 (by decide +kernel) ck413_7_0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem signedLow413 : Lower (signedRoots 413) (graphGoal 413) 8 := by
  apply finishLower (signedPairs (graphPairs 413 13421781764)) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel)
  let root := sl413_7.2 0
  have eq : (caseValues sgBase413 0 root).toFinset=(signedRoots 413).toFinset := by decide +kernel
  exact eq ▸ sv413_7 0 (by decide)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem signedLow424 : Lower (signedRoots 424) (graphGoal 424) 4 :=
  lower_map (ms:=([129,82,115,48] : List Nat).map swapRows) (base:=vars 15) (G:=graphGoal 15) (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) low15

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem signedLow300 : Lower (signedRoots 300) (graphGoal 300) 4 :=
  lower_map (ms:=([130,81,83,32] : List Nat).map swapRows) (base:=vars 15) (G:=graphGoal 15) (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) low15

def scuts445 : List SliceCode := [(0,4,7),(0,16,6),(0,128,7),(1,0,9),(8,0,8),(8,4,6),(8,16,5),(16,1,5),(17,0,7),(21,0,4),(25,0,4),(32,0,8),(32,128,6),(36,128,5),(48,1,4),(49,0,4),(132,0,8),(133,0,5),(136,4,5),(140,0,5),(145,0,4),(164,0,5),(256,0,9),(268,0,5),(273,0,4),(280,0,4),(289,0,5),(388,0,5),(416,0,5)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem scert445 : certifiedCuts 445 scuts445 := by
  intro c hc
  simp only [scuts445,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact signedColumn (m:=445) (z:=0) (o:=4) (q:=305) (s:=136) (base:=5) (L:=7) signedLow305 (by decide +kernel)
  · exact signedColumn (m:=445) (z:=0) (o:=16) (q:=420) (s:=9) (base:=4) (L:=6) signedLow420 (by decide +kernel)
  · exact signedColumn (m:=445) (z:=0) (o:=128) (q:=281) (s:=36) (base:=5) (L:=7) signedLow281 (by decide +kernel)
  · exact signedColumn (m:=445) (z:=1) (o:=0) (q:=444) (s:=0) (base:=9) (L:=9) signedLow444 (by decide +kernel)
  · exact signedColumn (m:=445) (z:=8) (o:=0) (q:=437) (s:=0) (base:=8) (L:=8) signedLow437 (by decide +kernel)
  · exact signedColumn (m:=445) (z:=8) (o:=4) (q:=305) (s:=128) (base:=5) (L:=6) signedLow305 (by decide +kernel)
  · exact signedColumn (m:=445) (z:=8) (o:=16) (q:=420) (s:=1) (base:=4) (L:=5) signedLow420 (by decide +kernel)
  · exact signedColumn (m:=445) (z:=16) (o:=1) (q:=396) (s:=32) (base:=4) (L:=5) signedLow396 (by decide +kernel)
  · exact signedColumn (m:=445) (z:=17) (o:=0) (q:=428) (s:=0) (base:=7) (L:=7) signedLow428 (by decide +kernel)
  · exact signedColumn (m:=445) (z:=21) (o:=0) (q:=424) (s:=0) (base:=4) (L:=4) signedLow424 (by decide +kernel)
  · exact signedColumn (m:=445) (z:=25) (o:=0) (q:=420) (s:=0) (base:=4) (L:=4) signedLow420 (by decide +kernel)
  · exact signedColumn (m:=445) (z:=32) (o:=0) (q:=413) (s:=0) (base:=8) (L:=8) signedLow413 (by decide +kernel)
  · exact signedColumn (m:=445) (z:=32) (o:=128) (q:=281) (s:=4) (base:=5) (L:=6) signedLow281 (by decide +kernel)
  · exact signedColumn (m:=445) (z:=36) (o:=128) (q:=281) (s:=0) (base:=5) (L:=5) signedLow281 (by decide +kernel)
  · exact signedColumn (m:=445) (z:=48) (o:=1) (q:=396) (s:=0) (base:=4) (L:=4) signedLow396 (by decide +kernel)
  · exact signedColumn (m:=445) (z:=49) (o:=0) (q:=396) (s:=0) (base:=4) (L:=4) signedLow396 (by decide +kernel)
  · exact signedColumn (m:=445) (z:=132) (o:=0) (q:=313) (s:=0) (base:=8) (L:=8) signedLow313 (by decide +kernel)
  · exact signedColumn (m:=445) (z:=133) (o:=0) (q:=312) (s:=0) (base:=5) (L:=5) signedLow312 (by decide +kernel)
  · exact signedColumn (m:=445) (z:=136) (o:=4) (q:=305) (s:=0) (base:=5) (L:=5) signedLow305 (by decide +kernel)
  · exact signedColumn (m:=445) (z:=140) (o:=0) (q:=305) (s:=0) (base:=5) (L:=5) signedLow305 (by decide +kernel)
  · exact signedColumn (m:=445) (z:=145) (o:=0) (q:=300) (s:=0) (base:=4) (L:=4) signedLow300 (by decide +kernel)
  · exact signedColumn (m:=445) (z:=164) (o:=0) (q:=281) (s:=0) (base:=5) (L:=5) signedLow281 (by decide +kernel)
  · exact signedColumn (m:=445) (z:=256) (o:=0) (q:=189) (s:=0) (base:=9) (L:=9) signedLow189 (by decide +kernel)
  · exact signedColumn (m:=445) (z:=268) (o:=0) (q:=177) (s:=0) (base:=5) (L:=5) signedLow177 (by decide +kernel)
  · exact signedColumn (m:=445) (z:=273) (o:=0) (q:=172) (s:=0) (base:=4) (L:=4) signedLow172 (by decide +kernel)
  · exact signedColumn (m:=445) (z:=280) (o:=0) (q:=165) (s:=0) (base:=4) (L:=4) signedLow165 (by decide +kernel)
  · exact signedColumn (m:=445) (z:=289) (o:=0) (q:=156) (s:=0) (base:=5) (L:=5) signedLow156 (by decide +kernel)
  · exact signedColumn (m:=445) (z:=388) (o:=0) (q:=57) (s:=0) (base:=5) (L:=5) signedLow57 (by decide +kernel)
  · exact signedColumn (m:=445) (z:=416) (o:=0) (q:=29) (s:=0) (base:=5) (L:=5) signedLow29 (by decide +kernel)
def sgSamples445 : Array (Bits × Bits) := #[(0x55bbf7649404a5c8c8cf52dde1bfecd5bc03fea1393cc10f4487b9cbbb722537cce7f7976892bbc68a0b4e803706077615f8bd15da8bc6dbe703688b34f60e5961319428a8204e6cfb92954556e10151052440348221a32aae21dc82cf069e2a,0x18dbc161902202004004002f2174881204012628104401010c0f888410370097480233966810ab269c084900250241341048e4e082b0e44b6200684314040859001100292222006cf262954552b04ca5343ce34f0021a32a0a001c82cf021a0a),(0x0,0x0),(0xbbc38dc82dc3d02eda67a2da1ed7bd49a79de33e6bcc9363fcacbcded4217df4ff0c2e119536b47a2118ddd5a63a9940e327ee8dc5a80432b870124ecde58bec2fd8a28490aea6c0eaac7cba77b7420a380090c841370333427ca2412f396730,0x20082e88b00280208f0a28928a133cc008c402162911a108485e11d0d002a0a4e1340641907080780148c5d0061811004b20280f810204108670224c494103e4aec82400111ea600aaa6903606a3b58297835199e02703110078a0402e116730),(0x645edcd2e97b5d73fbc0d565132cefe385cb2b7670a91f0420407ef59bfda7056b8893654f416395e616a30a615b0cc3522b4729a611bc62784e1ea7231d4092119c624bde5392976f5542d7cd9ee2a4a2c0160b49ecb037194e0d3740d88243,0x45281400c000002001050640104431483012000500010842500240106650001028010044e0041806c12020820c20063104846202410202028080c8320040013011000018001009001102040d11c081d202022401f88b0260104050740488042),(0xf4b5ff67420d0dbdea692eb8e3bb3f9a21efdc05c3d5eefe3547425a5388c078f47e449877f55f51a7cf140e9635163fd438081c48974b99a11fd7a002b96653de5c3ff2107c38148e039dd32d4180b585c0002488186ed0b56b92f2a4053451,0x4324360c20d915398a482b1040083088203ad917071022509200426aa980c268347c44001141144102411466901c0688c220081c494703048197132088bb5624dc4c17d64054bc000c0108922401b342cbc31cb0e0104cd0b46b827020052411),(0xabf4a215621ab7d8c3519c62917b17c5b270c8b953737d5bb3695b33ac6da8f0215408f493ad4a479ed8e349a9ee10f29fdb34a3747910c86bca53d7d463128e5eb79d9255c55291019030aa0ad1d40403f6910360a5dcd00e0646c380f89ae,0xc0800680023255000022204030210424301b400b30012500a00000002144009810210c0614400000208000b29310308110300008480062041023420258e30c005186401001c00002000201a018100107f8a10c100e0606c000d8020),(0x0,0x0),(0xc1513188bab4e2bd0316f33a7ede9812d294932ebf6e78f0fabcfeba447b74611284bf32da0c2e0f465370fd08e4782cf4463ce864ecdfc101c9d570f79ce96c3e729815c1cc78ed40f03bf8733a140a1810a8c02453c84eca1103df032270d7,0x9543117403342087301082251088c01a3428e509006c00810081a42201c8540100c0a912600d2f070613302d41a46a24844614e064e8db8009089903a69c000a00318927e0411124404023c811104a65687cae660050c80eca010393012210c7),(0x4a49ecbfe2df0663b5bce8e5e9187eac71aaaafc157874535bd9e529737eeb9924f9f5fe10e920bc51b8280fe5659d998f0026e3b9446c76d174e95cd89893dcd4aac1e86e4709561bca0fdf82812800420b070310f59e80b888a980f9e3411d,0xea2d7821e0c12280b3040280b4300c88208808280c7a4143085001283102b362056b8cf000e1a83710885804c125bc80060020d700440f561044e05c9891814cd820c1286a460964aec20fbf008157e0de5eddaf80750e00b8088880b9a2411d)]
def sgP445 (j : Nat) := (sgSamples445[j]?.getD (0,0)).1
def sgN445 (j : Nat) := (sgSamples445[j]?.getD (0,0)).2
def sgBase445 := decorateSigned 445 sgP445 sgN445
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sgPairs445 : properPairs (graphGoal 445) (asRow sgP445) (asRow sgN445) :=
  chart_pairs (m:=445) (p:=sgP445) (q:=sgN445) (by decide +kernel) (by decide +kernel)

def sl445_6b0 : Array CaseCode := #[(398737591537203,2231,[],[]),
(398170920618547,2231,[],[]),
(113963873714498,3127,[],[])]
def sl445_6 : Cases := (3,fun i => (sl445_6b0)[i % 16]?.getD default)
def scan445_6 := rangeCases 445 sgBase445 scuts445 6 5 emptyCases sl445_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_6_0 : scan445_6 0 3=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sv445_6 : caseLevel (graphGoal 445) sgBase445 6 5 sl445_6 :=
  caseLevel_ok sgPairs445 (decorateSigned_ok 445 _ _) scert445 (by intro i h; exact (Nat.not_lt_zero i h).elim) (by decide +kernel) ck445_6_0

def sl445_7b0 : Array CaseCode := #[(382596058675,1767,[(22,1)],[]),
(714382282291,1271,[],[0]),
(113086860851,1719,[],[]),
(387964767795,1271,[],[]),
(380415053363,1779,[(22,1)],[]),
(387931246131,1271,[],[]),
(346122423859,1767,[],[]),
(380442316339,2019,[],[]),
(113080602163,1959,[],[]),
(353398720051,1271,[(22,1)],[]),
(387758491187,1271,[],[]),
(158210524723,1525,[(16,9)],[]),
(371120735795,1247,[],[]),
(353398785587,1271,[(22,1)],[]),
(111806843443,1719,[],[]),
(387758492211,1271,[],[])]
def sl445_7b16 : Array CaseCode := #[(388300606003,1215,[],[]),
(353398770227,1271,[(22,1)],[]),
(387758508595,1271,[],[]),
(302401276467,1277,[],[]),
(353398786611,1271,[(22,1)],[]),
(284600898099,1270,[],[]),
(284600898099,1510,[(8,2)],[]),
(284679312947,1270,[(6,0)],[]),
(586818257459,2032,[],[]),
(623325479475,2020,[],[]),
(659832701491,1972,[],[]),
(623343305267,2018,[],[]),
(641596916275,2002,[],[]),
(659850527283,1970,[],[]),
(641632567859,1990,[],[]),
(659886178867,1958,[],[])]
def sl445_7b32 : Array CaseCode := #[(659904004659,1942,[],[]),
(363277353523,2006,[(16,3),(8,8)],[]),
(379400258099,1974,[(4,5),(8,8)],[]),
(346081755699,2019,[(5,1)],[]),
(386917499443,1719,[(16,1)],[]),
(382590026291,2019,[(14,0)],[]),
(113080828467,1971,[(3,13)],[]),
(405480440371,1143,[],[]),
(379400290867,1974,[(22,1)],[]),
(379334263347,1973,[(22,1)],[]),
(379367817779,1973,[(11,9),(16,3)],[]),
(387957752371,1463,[(3,1)],[]),
(382590091827,1959,[(14,0),(22,1)],[]),
(623343322675,2017,[],[]),
(659850544691,1969,[],[]),
(659886196275,1957,[],[])]
def sl445_7b48 : Array CaseCode := #[(351450547763,1909,[(3,7),(16,9)],[]),
(380442576435,2019,[(5,1)],[]),
(113080862259,1959,[(16,13)],[]),
(371120735795,1239,[],[]),
(380442609203,1971,[(5,1),(22,1)],[]),
(147711363635,1271,[],[1]),
(301797509683,1521,[(4,9)],[]),
(404876724787,1395,[(4,9)],[]),
(641632602675,1987,[],[]),
(659886213683,1955,[],[]),
(659904039475,1939,[],[]),
(383702649395,1847,[(22,1)],[]),
(112072133171,1719,[(8,10)],[]),
(112073181747,1719,[(16,11)],[]),
(351468325427,2019,[(12,1)],[]),
(382606838323,2019,[(12,1)],[])]
def sl445_7b64 : Array CaseCode := #[(112023898675,1971,[(16,11)],[]),
(351485102643,2019,[(6,0)],[]),
(385844841011,1971,[(6,0),(22,1)],[]),
(112012364339,1959,[(8,10)],[]),
(112079473203,1719,[(3,11)],[]),
(383699454515,1959,[(12,1),(22,1)],[]),
(388300606003,1463,[(22,1)],[]),
(112348957235,1719,[],[1]),
(388300606003,1271,[],[]),
(388300606003,1719,[],[]),
(388300606003,1207,[],[]),
(112030190131,1719,[(16,11)],[]),
(714416130611,1271,[],[1]),
(147746785843,1207,[],[1]),
(383702616627,1943,[(16,5),(4,9)],[]),
(386923842099,1719,[(8,0)],[])]
def sl445_7b80 : Array CaseCode := #[(302401276467,1269,[],[]),
(383702605363,1847,[(3,13),(11,5)],[]),
(383703653939,1719,[(16,1)],[]),
(383682715187,1943,[(22,1)],[]),
(284584120883,1510,[(4,1)],[]),
(370483466803,1479,[(4,1)],[]),
(659904074291,1927,[],[]),
(158184250403,1143,[(1,0)],[]),
(158217804835,1143,[(1,0)],[]),
(388300610595,1087,[],[0]),
(147746790435,1087,[],[]),
(158192664611,1522,[],[]),
(158209441827,1522,[],[]),
(284668006691,1150,[(8,2)],[]),
(284668006691,1390,[],[]),
(130567128387,1341,[],[])]
def sl445_7b96 : Array CaseCode := #[(130567145795,1339,[],[]),
(130567180611,1327,[],[]),
(130567198019,1311,[],[]),
(623343322624,2024,[],[]),
(659850544640,1976,[],[]),
(659886196224,1964,[],[]),
(371120735744,1246,[],[]),
(301797509632,1528,[],[]),
(641632602624,1994,[],[]),
(659886213632,1962,[],[]),
(659904039424,1946,[],[]),
(388300605952,1214,[],[]),
(147746785792,1214,[],[]),
(302401276416,1276,[],[]),
(370483466752,1486,[],[]),
(659904074240,1934,[],[])]
def sl445_7b112 : Array CaseCode := #[(714175978768,1143,[],[]),
(622907923728,1639,[],[]),
(659415145744,1591,[],[]),
(568689020192,1653,[(16,7)],[]),
(310990982432,1655,[],[]),
(345350720800,1655,[(16,7)],[]),
(379710459168,1655,[],[]),
(586942631200,1651,[(16,7)],[]),
(346424462624,1655,[(22,7)],[]),
(363604331808,1655,[(16,7)],[]),
(380784200992,1655,[],[]),
(623449853216,1639,[(16,7)],[]),
(365751815456,1655,[],[]),
(382931684640,1655,[],[]),
(641703464224,1623,[(16,7)],[]),
(384005426464,1655,[],[])]
def sl445_7b128 : Array CaseCode := #[(659957075232,1591,[(16,7)],[]),
(586817850656,1905,[],[]),
(623325072672,1893,[],[]),
(659832294688,1845,[],[]),
(623342898464,1891,[],[]),
(641596509472,1875,[],[]),
(659850120480,1843,[],[]),
(641632161056,1863,[],[]),
(659885772064,1831,[],[]),
(659903597856,1815,[],[]),
(382590091552,1962,[(14,0)],[]),
(158183474464,1397,[],[]),
(158217028896,1397,[],[]),
(158183491872,1395,[],[]),
(158200269088,1395,[],[]),
(158217046304,1395,[],[])]
def sl445_7b144 : Array CaseCode := #[(111806848288,1591,[(7,0)],[]),
(714176011552,1143,[],[]),
(622907956512,1639,[],[]),
(641161567520,1623,[],[]),
(659415178528,1591,[],[]),
(388300610848,1087,[(7,0)],[]),
(158217870624,1143,[(1,0)],[]),
(147746790688,1087,[],[]),
(714176027936,1143,[],[]),
(659415194912,1591,[],[]),
(714176044320,1143,[],[]),
(622907989280,1639,[],[]),
(641161600288,1623,[],[]),
(284600950080,1150,[(8,2)],[]),
(387747187024,1339,[],[]),
(432794012177,1521,[],[])]
def sl445_7b160 : Array CaseCode := #[(659886213649,1961,[],[]),
(388300605969,1213,[],[]),
(147746785809,1213,[],[]),
(284600898065,1276,[],[]),
(284600898065,1516,[],[]),
(284584120849,1516,[],[]),
(147746790689,1087,[],[]),
(659638836545,1567,[],[]),
(388300605986,1211,[],[]),
(147746785826,1211,[],[]),
(387747222050,1087,[],[1]),
(387747222050,1327,[],[]),
(641429741090,1747,[],[]),
(659683352098,1715,[],[]),
(659571154466,1721,[],[]),
(284600898082,1274,[],[])]
def sl445_7b176 : Array CaseCode := #[(284600898082,1514,[],[]),
(387747222050,1451,[],[]),
(659904074274,1931,[],[]),
(284679312930,1274,[],[]),
(714176053570,1271,[],[2]),
(110733148482,1591,[],[2]),
(130567180610,1327,[],[]),
(284600950082,1150,[(1,0)],[]),
(387680165186,1087,[(1,0)],[]),
(641402002754,1567,[],[]),
(147746807106,1087,[],[]),
(130567198018,1311,[],[]),
(284679312722,1246,[(6,0)],[]),
(659571727698,1597,[],[]),
(714176053602,1271,[],[]),
(641300749892,1630,[],[])]
def sl445_7b192 : Array CaseCode := #[(659554360900,1598,[],[]),
(714315193924,1262,[],[]),
(641300749892,1742,[],[]),
(659554360900,1710,[],[]),
(714315177540,1262,[],[]),
(641300733508,1742,[],[]),
(659554344516,1710,[],[]),
(659638230596,1679,[],[]),
(284600950116,1150,[(1,0)],[]),
(714315255141,1150,[],[])]
def sl445_7 : Cases := (202,fun i => ((if i<96 then (if i<48 then (if i<16 then sl445_7b0 else (if i<32 then sl445_7b16 else sl445_7b32)) else (if i<64 then sl445_7b48 else (if i<80 then sl445_7b64 else sl445_7b80))) else (if i<144 then (if i<112 then sl445_7b96 else (if i<128 then sl445_7b112 else sl445_7b128)) else (if i<176 then (if i<160 then sl445_7b144 else sl445_7b160) else (if i<192 then sl445_7b176 else sl445_7b192)))))[i % 16]?.getD default)
def scan445_7 := rangeCases 445 sgBase445 scuts445 7 4 sl445_6 sl445_7
theorem j445_7 (o a b : Nat) (x : scan445_7 o a=true) (y : scan445_7 (o+a) b=true) : scan445_7 o (a+b)=true := @joinRange 445 sgBase445 scuts445 7 4 sl445_6 sl445_7 o a b x y
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_7_0 : scan445_7 0 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_7_8 : scan445_7 8 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_7_16 : scan445_7 16 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_7_24 : scan445_7 24 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_7_32 : scan445_7 32 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_7_40 : scan445_7 40 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_7_48 : scan445_7 48 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_7_56 : scan445_7 56 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_7_64 : scan445_7 64 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_7_72 : scan445_7 72 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_7_80 : scan445_7 80 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_7_88 : scan445_7 88 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_7_96 : scan445_7 96 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_7_104 : scan445_7 104 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_7_112 : scan445_7 112 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_7_120 : scan445_7 120 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_7_128 : scan445_7 128 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_7_136 : scan445_7 136 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_7_144 : scan445_7 144 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_7_152 : scan445_7 152 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_7_160 : scan445_7 160 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_7_168 : scan445_7 168 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_7_176 : scan445_7 176 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_7_184 : scan445_7 184 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_7_192 : scan445_7 192 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_7_200 : scan445_7 200 2=true := by decide +kernel
theorem ck445_7_0m16 : scan445_7 0 16=true := j445_7 0 8 8 ck445_7_0 ck445_7_8
theorem ck445_7_16m16 : scan445_7 16 16=true := j445_7 16 8 8 ck445_7_16 ck445_7_24
theorem ck445_7_32m16 : scan445_7 32 16=true := j445_7 32 8 8 ck445_7_32 ck445_7_40
theorem ck445_7_48m16 : scan445_7 48 16=true := j445_7 48 8 8 ck445_7_48 ck445_7_56
theorem ck445_7_64m16 : scan445_7 64 16=true := j445_7 64 8 8 ck445_7_64 ck445_7_72
theorem ck445_7_80m16 : scan445_7 80 16=true := j445_7 80 8 8 ck445_7_80 ck445_7_88
theorem ck445_7_96m16 : scan445_7 96 16=true := j445_7 96 8 8 ck445_7_96 ck445_7_104
theorem ck445_7_112m16 : scan445_7 112 16=true := j445_7 112 8 8 ck445_7_112 ck445_7_120
theorem ck445_7_128m16 : scan445_7 128 16=true := j445_7 128 8 8 ck445_7_128 ck445_7_136
theorem ck445_7_144m16 : scan445_7 144 16=true := j445_7 144 8 8 ck445_7_144 ck445_7_152
theorem ck445_7_160m16 : scan445_7 160 16=true := j445_7 160 8 8 ck445_7_160 ck445_7_168
theorem ck445_7_176m16 : scan445_7 176 16=true := j445_7 176 8 8 ck445_7_176 ck445_7_184
theorem ck445_7_192m10 : scan445_7 192 10=true := j445_7 192 8 2 ck445_7_192 ck445_7_200
theorem ck445_7_0m32 : scan445_7 0 32=true := j445_7 0 16 16 ck445_7_0m16 ck445_7_16m16
theorem ck445_7_32m32 : scan445_7 32 32=true := j445_7 32 16 16 ck445_7_32m16 ck445_7_48m16
theorem ck445_7_64m32 : scan445_7 64 32=true := j445_7 64 16 16 ck445_7_64m16 ck445_7_80m16
theorem ck445_7_96m32 : scan445_7 96 32=true := j445_7 96 16 16 ck445_7_96m16 ck445_7_112m16
theorem ck445_7_128m32 : scan445_7 128 32=true := j445_7 128 16 16 ck445_7_128m16 ck445_7_144m16
theorem ck445_7_160m32 : scan445_7 160 32=true := j445_7 160 16 16 ck445_7_160m16 ck445_7_176m16
theorem ck445_7_0m64 : scan445_7 0 64=true := j445_7 0 32 32 ck445_7_0m32 ck445_7_32m32
theorem ck445_7_64m64 : scan445_7 64 64=true := j445_7 64 32 32 ck445_7_64m32 ck445_7_96m32
theorem ck445_7_128m64 : scan445_7 128 64=true := j445_7 128 32 32 ck445_7_128m32 ck445_7_160m32
theorem ck445_7_0m128 : scan445_7 0 128=true := j445_7 0 64 64 ck445_7_0m64 ck445_7_64m64
theorem ck445_7_128m74 : scan445_7 128 74=true := j445_7 128 64 10 ck445_7_128m64 ck445_7_192m10
theorem ck445_7_0m202 : scan445_7 0 202=true := j445_7 0 128 74 ck445_7_0m128 ck445_7_128m74
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sv445_7 : caseLevel (graphGoal 445) sgBase445 7 4 sl445_7 :=
  caseLevel_ok sgPairs445 (decorateSigned_ok 445 _ _) scert445 sv445_6 (by decide +kernel) ck445_7_0m202

def sl445_8b0 : Array CaseCode := #[(293637683,759,[(0,1),(8,4),(16,1),(16,3),(3,1),(11,1),(22,1)],[]),
(343969331,759,[(8,4),(16,1),(8,0),(22,1),(3,1),(5,1),(0,1),(2,1)],[0,1,2,3]),
(360746547,759,[(16,3),(8,4),(16,1),(2,1),(3,1),(11,1),(22,1)],[]),
(377523763,759,[(8,4),(16,1),(22,1),(3,1),(5,1),(0,1),(22,3),(11,1),(2,1),(23,1)],[3]),
(554733107,1013,[(16,3)],[]),
(342920755,887,[(4,5),(3,2)],[]),
(608210483,1015,[(4,1),(11,1)],[]),
(608210483,999,[(16,3)],[]),
(356552243,1015,[(4,1),(2,1)],[]),
(373329459,1015,[(4,1)],[0,3]),
(626036275,983,[(16,3)],[]),
(374378035,1015,[(2,1),(22,1),(4,1)],[]),
(643862067,951,[(16,3)],[]),
(293670451,759,[(8,4),(16,3),(0,1),(16,1),(3,1),(4,1),(22,1),(5,1)],[]),
(310447667,759,[(8,4),(16,1),(8,0),(3,1),(16,7),(0,1),(12,1),(6,0),(2,1),(22,1)],[4,5]),
(360779315,759,[(8,4),(2,1),(16,1),(16,3),(3,1),(4,1),(22,1)],[])]
def sl445_8b16 : Array CaseCode := #[(377556531,759,[(8,4),(16,1),(22,1),(3,1),(0,1),(4,1),(22,3),(12,1),(2,1),(26,1)],[5,6]),
(554765875,1013,[(16,3)],[]),
(303107635,1015,[(11,1),(0,1)],[]),
(370216499,1015,[(0,1),(11,1)],[]),
(572591667,1011,[(16,3)],[]),
(337710643,999,[(8,4),(5,1),(12,1),(8,0)],[6,7,8]),
(371265075,1015,[(11,1)],[4,5,7]),
(626069043,983,[(16,3)],[]),
(643894835,951,[(16,3)],[]),
(573064755,1017,[],[]),
(388515379,893,[],[]),
(343426611,893,[(3,2)],[]),
(376981043,893,[],[]),
(608716339,1005,[],[]),
(644367923,957,[],[]),
(137659955,759,[(16,1),(16,5),(8,2),(19,1),(3,1),(11,1),(22,1),(23,1)],[9])]
def sl445_8b32 : Array CaseCode := #[(370443827,1021,[(23,1),(22,1)],[]),
(679773747,767,[(0,1),(8,0)],[]),
(344229427,767,[(16,5),(1,0),(8,0),(16,1),(22,1)],[]),
(377783859,767,[(23,1),(8,0)],[]),
(608552499,879,[],[]),
(644204083,831,[],[]),
(137692723,759,[(8,2),(16,1),(16,5),(6,0),(21,1),(3,1),(4,1),(22,1)],[10]),
(370476595,1021,[(16,1),(22,1)],[11]),
(337970739,1007,[(16,5),(6,0),(16,1)],[]),
(679806515,767,[(0,1),(8,0)],[12]),
(377816627,767,[(1,0),(8,0),(16,1)],[]),
(137725491,759,[(16,5),(23,1),(8,2),(16,1),(3,1),(4,1),(11,1),(22,5)],[11,13]),
(371557939,959,[(23,1),(16,1)],[]),
(679839283,767,[(0,1),(8,0)],[]),
(137923123,759,[(8,0),(8,2),(16,1),(10,0),(3,1),(0,1),(11,1),(2,1),(22,1)],[]),
(388532787,891,[],[])]
def sl445_8b48 : Array CaseCode := #[(137923123,1011,[(8,2)],[]),
(343444019,891,[(3,2)],[]),
(360221235,891,[],[]),
(376998451,891,[],[]),
(608733747,1003,[],[]),
(626559539,987,[],[]),
(644385331,955,[],[]),
(344312371,639,[(8,4),(3,0),(22,0)],[]),
(377866803,639,[(22,3)],[]),
(608553523,879,[],[]),
(626379315,863,[],[]),
(644205107,831,[],[]),
(403769907,767,[(16,3),(19,1),(8,0)],[]),
(394332723,639,[(8,2)],[]),
(360778291,767,[(16,3),(19,1),(8,0)],[]),
(137693747,1015,[(8,2)],[14])]
def sl445_8b64 : Array CaseCode := #[(137693747,759,[(8,2),(16,1),(8,0),(1,0),(3,1),(0,1),(2,1),(22,1)],[15]),
(354748979,1019,[(12,1),(16,3),(16,1)],[]),
(371526195,1019,[(22,3),(22,1)],[7]),
(343214643,879,[(8,2),(8,0)],[]),
(373623347,1007,[(6,0),(22,1)],[]),
(679807539,767,[(1,0),(8,0)],[16]),
(361040435,767,[(1,0),(8,0),(16,1),(22,1)],[]),
(109382195,959,[(8,6)],[8,14]),
(377817651,767,[(1,0),(8,0)],[]),
(137710131,759,[(8,2),(16,1),(16,5),(19,1),(3,1),(11,1),(22,1)],[17,18]),
(374688307,991,[(22,3),(6,0),(16,1),(22,1)],[]),
(679823923,767,[(2,1),(8,0)],[19]),
(377834035,767,[(22,3),(1,0),(8,0),(16,1)],[]),
(137726515,759,[(8,2),(16,1),(22,5),(22,1),(23,1),(3,1),(0,1),(11,1),(2,1)],[20]),
(376801843,831,[(22,1),(8,0)],[]),
(608509491,879,[(3,4)],[])]
def sl445_8b80 : Array CaseCode := #[(377822771,639,[(22,3),(3,0)],[]),
(626335283,863,[(3,4)],[]),
(644161075,831,[(3,4)],[]),
(644177459,831,[],[]),
(608542259,879,[],[]),
(626368051,863,[],[]),
(374709811,831,[(16,3),(16,0)],[]),
(59314739,759,[(8,0),(8,2),(16,1),(3,1),(1,0),(0,1),(4,1),(6,0),(2,1),(22,1),(15,0)],[21]),
(59314739,999,[(8,2)],[22]),
(626594355,975,[],[]),
(644420147,943,[],[]),
(137712179,759,[(8,2),(16,1),(16,5),(21,1),(3,1),(4,1),(6,0),(22,1),(28,1)],[]),
(374690355,991,[(22,3),(22,1)],[]),
(679825971,767,[(2,1),(8,0)],[]),
(377836083,767,[(28,1),(8,0)],[]),
(137728563,759,[(8,2),(16,1),(6,0),(22,5),(22,1),(26,1),(3,1),(0,1),(4,1),(2,1),(28,1)],[])]
def sl445_8b96 : Array CaseCode := #[(374706739,959,[(28,1),(16,1)],[]),
(679842355,767,[(1,0),(8,0)],[]),
(644437555,927,[],[]),
(137729587,759,[(16,1),(16,5),(27,1),(8,2),(6,0),(3,1),(4,1),(11,1),(28,1)],[23]),
(679843379,767,[(2,1),(8,0)],[]),
(555221555,1012,[(16,3),(16,1),(16,2)],[24,25,26]),
(303563315,1014,[(16,1)],[]),
(337117747,1014,[(16,1),(16,3)],[]),
(370672179,1014,[(16,1)],[]),
(573047347,1014,[(16,5)],[]),
(573047347,1010,[(16,3),(16,5),(16,6)],[24,27,28,29]),
(69730867,1014,[(16,5)],[]),
(338166323,1014,[(16,5),(22,3)],[]),
(354943539,1014,[(16,1),(16,3)],[]),
(371720755,1014,[(16,5)],[]),
(608698931,1014,[(16,5)],[])]
def sl445_8b112 : Array CaseCode := #[(608698931,998,[(16,3),(16,5),(16,6)],[25,27,30,31]),
(357040691,1014,[(16,1)],[]),
(373817907,1014,[(16,5)],[]),
(626524723,982,[(16,3),(16,1),(16,2)],[28,30,32]),
(374866483,1014,[(16,1)],[]),
(644350515,950,[(16,3),(16,5),(16,6)],[26,29,31,32]),
(302268979,1014,[(8,0),(16,5),(5,1),(16,1),(11,5),(14,0)],[]),
(336871987,1013,[(16,1),(5,1),(8,4),(3,1),(4,5),(3,5),(0,1)],[]),
(679756339,759,[(16,1),(16,5),(17,1),(4,1),(5,1),(8,0),(8,4),(11,1),(22,1)],[]),
(310657587,759,[(8,4),(0,1),(16,5),(8,0),(11,1),(16,1),(22,1)],[]),
(344212019,759,[(16,5),(0,1),(8,4),(16,1),(4,1),(8,0),(22,1)],[]),
(377766451,759,[(0,1),(5,1),(4,1),(8,0),(8,4),(11,1),(16,1),(16,5)],[]),
(572801587,1011,[(16,1)],[]),
(337920563,1015,[(14,0),(5,1),(17,1),(0,1),(22,3)],[]),
(371474995,1015,[(17,1),(0,1)],[]),
(608453171,999,[(16,1)],[])]
def sl445_8b128 : Array CaseCode := #[(373572147,1015,[(17,1),(0,1)],[]),
(644104755,951,[(16,1)],[]),
(352617011,1014,[(8,0),(16,3),(14,0),(7,0),(16,1),(11,3)],[33]),
(369394227,1014,[(8,0),(22,3),(14,0),(7,0),(22,1),(5,1),(11,3)],[34]),
(554992179,1013,[(16,3),(8,4)],[]),
(303333939,1015,[(16,1),(16,3),(8,4)],[]),
(336888371,1015,[(5,1),(3,1),(16,1),(8,4),(21,1),(0,1),(16,3)],[35]),
(370442803,1015,[(5,1),(4,1),(8,4),(23,1),(0,1)],[34,36]),
(572817971,1011,[(16,3),(8,4)],[]),
(337936947,1015,[(3,1),(8,4),(3,5),(22,3)],[]),
(337936947,1011,[(14,0),(8,4),(3,5),(3,1),(12,1)],[35,37,38]),
(354714163,1015,[(16,3),(8,4),(16,1)],[33]),
(371491379,1015,[(8,4),(3,1),(3,5)],[]),
(679772723,759,[(16,1),(10,0),(16,3),(3,5),(0,1),(3,1),(8,0),(8,4),(7,0),(11,1),(2,1),(22,1)],[39]),
(344228403,759,[(7,0),(8,4),(16,1),(8,0),(22,1),(0,1),(2,1)],[]),
(361005619,759,[(16,3),(8,4),(2,1),(16,1),(8,0),(12,1),(11,1),(22,1)],[])]
def sl445_8b144 : Array CaseCode := #[(377782835,759,[(8,4),(16,1),(8,0),(7,0),(0,1),(14,0),(11,1),(2,1)],[36]),
(608469555,999,[(16,3),(8,4)],[]),
(356811315,1015,[(14,0),(3,1),(8,4),(21,1),(2,1)],[]),
(373588531,1015,[(14,0),(3,1),(8,4),(26,1),(7,0)],[37]),
(626295347,983,[(16,3),(8,4)],[]),
(374637107,1015,[(7,0),(8,4),(22,1),(27,1),(2,1)],[]),
(644121139,951,[(16,3),(8,4)],[]),
(352649779,1014,[(16,3),(12,1),(8,0),(16,1),(7,0)],[]),
(369426995,1014,[(8,0),(22,3),(22,1),(7,0),(26,1),(12,1)],[40]),
(555024947,1013,[(16,3)],[]),
(303366707,1015,[(26,1),(0,1)],[]),
(336921139,1015,[(16,3),(16,1)],[]),
(370475571,1015,[(22,1),(26,1),(0,1)],[40]),
(572850739,1015,[(26,1),(4,1)],[]),
(572850739,1011,[(16,3)],[]),
(337969715,1015,[(3,1),(3,5),(22,3)],[])]
def sl445_8b160 : Array CaseCode := #[(354746931,1015,[(12,1),(16,3),(16,1),(26,1),(2,1)],[]),
(371524147,1015,[(26,1),(7,0)],[]),
(608502323,999,[(16,3)],[]),
(356844083,1015,[(12,1),(16,1),(16,3)],[]),
(679805491,759,[(16,1),(26,1),(16,3),(3,5),(0,1),(4,1),(8,0),(8,4),(3,1),(2,1),(22,1)],[]),
(361038387,759,[(2,1),(16,1),(16,3),(4,1),(8,0),(8,4),(22,1)],[]),
(377815603,759,[(16,1),(0,1),(4,1),(7,0),(8,0),(8,4),(2,1),(26,1)],[]),
(626328115,983,[(16,3)],[]),
(374669875,1015,[(12,1),(26,1),(2,1)],[]),
(644153907,951,[(16,3)],[]),
(572867123,1015,[(3,1),(16,1),(17,1),(4,1)],[]),
(572867123,1011,[(16,1)],[]),
(337986099,1015,[(12,1),(2,1),(14,0),(7,0),(11,1),(17,1),(22,3)],[]),
(354763315,983,[(16,1),(3,5),(12,1),(8,4),(2,1),(3,1),(11,5)],[33]),
(371540531,1015,[(17,1),(2,1)],[]),
(608518707,999,[(16,1)],[])]
def sl445_8b176 : Array CaseCode := #[(356860467,983,[(16,1),(3,5),(2,1),(3,1),(14,0),(12,1),(8,4)],[]),
(373637683,1015,[(12,1),(17,1),(2,1)],[]),
(679821875,759,[(16,1),(16,5),(17,1),(4,1),(8,0),(8,4),(11,1),(12,1),(22,1)],[]),
(377831987,759,[(2,1),(16,5),(12,1),(8,4),(11,1),(7,0),(3,5),(16,1),(22,3),(4,1),(8,0)],[]),
(644170291,951,[(16,1)],[]),
(555057715,1013,[(16,3)],[]),
(303399475,1015,[(22,1),(26,1),(0,1)],[41]),
(336953907,1015,[(0,1),(11,1),(16,3),(26,1)],[42,43]),
(370508339,951,[(16,3),(16,1),(3,5),(4,3),(8,4),(11,5)],[34,36,40,41,42,43]),
(572883507,1015,[(3,1),(4,3),(26,1),(4,1)],[]),
(572883507,1011,[(16,3)],[]),
(338002483,1015,[(14,0),(7,0),(22,1),(26,1)],[44]),
(354779699,1015,[(2,1),(16,3),(22,1),(26,1)],[]),
(608535091,999,[(16,3)],[]),
(356876851,1015,[(2,1),(26,1)],[]),
(373654067,951,[(3,5),(3,1),(14,0),(26,1),(4,3),(8,4),(12,1)],[43,44])]
def sl445_8b192 : Array CaseCode := #[(626360883,983,[(16,3)],[]),
(679838259,759,[(16,1),(26,1),(16,3),(3,5),(0,1),(4,1),(8,0),(8,4),(11,1),(2,1),(3,1)],[]),
(573064755,1013,[(16,5)],[]),
(573064755,1009,[(16,5),(16,1),(16,4)],[24,45,46]),
(388515379,1013,[(16,5)],[]),
(69748275,1013,[(16,5)],[]),
(338183731,1013,[(16,5),(22,3)],[]),
(371738163,1013,[(16,5)],[]),
(343426611,1013,[(16,5),(3,3)],[]),
(376981043,1013,[(16,5)],[]),
(608716339,1013,[(16,5)],[]),
(608716339,997,[(16,5),(16,1),(16,4)],[25,45,47]),
(373835315,1013,[(16,5)],[]),
(644367923,949,[(16,5),(16,1),(16,4)],[26,46,47]),
(387221043,1013,[(16,1),(8,2),(8,0),(0,1),(3,7),(5,1),(6,0)],[]),
(370443827,1013,[(16,1),(0,1),(22,1),(22,3),(5,1)],[41])]
def sl445_8b208 : Array CaseCode := #[(572818995,1011,[(16,1)],[]),
(388269619,1015,[(5,1),(16,1),(16,5)],[]),
(337937971,1015,[(16,1),(16,5),(22,3)],[]),
(679773747,759,[(19,1),(16,1),(16,5),(3,1),(8,0),(11,1),(22,1)],[]),
(394561075,759,[(0,1),(3,1),(8,2),(11,1),(16,1),(16,5),(22,1)],[]),
(344229427,759,[(0,1),(16,5),(16,1),(22,1),(3,1),(8,0)],[]),
(377783859,759,[(0,1),(3,1),(8,0),(11,1),(16,1),(16,5)],[]),
(343180851,1015,[(3,3),(6,0),(8,0),(19,1),(0,1)],[]),
(376735283,1015,[(0,1),(19,1)],[]),
(608470579,1015,[(19,1),(11,1)],[]),
(608470579,999,[(16,1)],[]),
(373589555,1015,[(26,1),(0,1)],[]),
(644122163,951,[(16,1)],[]),
(336971315,1013,[(16,1),(8,4),(5,1),(0,1),(8,0),(3,7),(4,5)],[48]),
(572900915,1011,[(16,1)],[]),
(388351539,887,[(5,1),(16,5),(8,0),(16,1),(3,3),(1,0)],[])]
def sl445_8b224 : Array CaseCode := #[(338019891,1015,[(5,1),(0,1),(4,1),(6,0),(1,0),(9,0),(22,3)],[]),
(371574323,1015,[(5,1),(23,1),(0,1)],[]),
(343262771,887,[(8,0),(16,5),(3,3),(6,0),(1,0),(16,1),(4,5)],[48]),
(344311347,759,[(8,4),(0,1),(16,5),(3,1),(16,1),(5,1),(4,1),(22,1)],[]),
(377865779,759,[(0,1),(16,5),(8,4),(5,1),(4,1),(3,7),(3,1),(1,0),(22,3),(11,1),(16,1)],[]),
(608552499,1015,[(16,1),(8,0),(9,0),(11,1)],[]),
(608552499,999,[(16,1)],[]),
(373671475,1015,[(26,1),(0,1)],[]),
(644204083,951,[(16,1)],[]),
(370476595,1013,[(16,1),(0,1),(22,3),(5,1),(22,1),(4,3)],[42]),
(572851763,1011,[(16,1),(16,5)],[]),
(388302387,1015,[(5,1),(16,1),(21,1),(0,1),(16,5)],[]),
(337970739,1015,[(16,1),(16,5),(22,3)],[]),
(337970739,999,[(16,5),(5,1),(16,1)],[35,49,50]),
(371525171,1015,[(5,1),(16,1),(16,5),(23,1),(0,1)],[49]),
(343213619,1015,[(16,5),(3,3),(16,1)],[48])]
def sl445_8b240 : Array CaseCode := #[(376768051,1015,[(0,1),(16,5),(22,1),(21,1)],[]),
(608503347,999,[(16,1),(16,5)],[]),
(373622323,1015,[(16,5),(16,1)],[]),
(679806515,759,[(16,1),(21,1),(16,5),(3,1),(4,1),(5,1),(8,0),(0,1),(22,1)],[51]),
(377816627,759,[(0,1),(16,5),(16,1),(3,1),(5,1),(4,1),(8,0)],[43]),
(644154931,951,[(16,1),(16,5)],[]),
(572884531,1011,[(16,1)],[]),
(388335155,1015,[(5,1),(23,1),(0,1)],[]),
(338003507,1015,[(5,1),(0,1),(22,1),(23,1)],[52]),
(371557939,951,[(5,1),(16,5),(16,1),(11,3)],[36,52]),
(343246387,1015,[(3,3),(1,0),(22,1),(23,1),(0,1)],[]),
(608536115,1015,[(16,1),(11,3),(23,1),(11,1)],[]),
(608536115,999,[(16,1)],[]),
(679839283,759,[(16,1),(23,1),(16,5),(3,1),(4,1),(5,1),(8,0),(11,1)],[]),
(388532787,1011,[(16,5)],[]),
(338201139,1011,[(16,5),(22,3)],[])]
def sl445_8b256 : Array CaseCode := #[(354978355,1011,[(16,1),(16,3)],[]),
(371755571,1011,[(16,5)],[]),
(608733747,1015,[(4,1)],[53]),
(608733747,999,[(16,3)],[]),
(357075507,1015,[(21,1),(4,1)],[]),
(373852723,1015,[(11,1),(26,1),(4,1)],[]),
(626559539,983,[(16,3)],[]),
(374901299,1015,[(16,1),(4,5),(27,1),(4,1)],[]),
(644385331,951,[(16,3)],[]),
(76057139,1011,[(4,1)],[54,55]),
(343444019,1011,[(16,5),(3,3)],[]),
(360221235,1011,[(16,1)],[]),
(376998451,1011,[(16,5)],[]),
(608733747,1011,[(16,5)],[]),
(608733747,995,[(16,3),(16,5),(16,6)],[27,45,56,57]),
(357075507,1011,[(16,1)],[])]
def sl445_8b272 : Array CaseCode := #[(373852723,1011,[(16,5)],[]),
(626559539,979,[(16,3),(16,1),(16,2)],[28,56,58]),
(374901299,1011,[(16,1)],[]),
(644385331,947,[(16,3),(16,5),(16,6)],[29,46,57,58]),
(338020915,1015,[(8,0),(8,4),(22,3)],[]),
(354798131,1015,[(16,3),(16,1)],[]),
(376818227,887,[(8,0),(22,1),(22,3),(3,5),(5,1),(6,0),(1,0)],[59]),
(344312371,759,[(1,0),(8,4),(3,1),(16,1),(22,1),(0,1),(2,1)],[]),
(361089587,759,[(16,3),(2,1),(8,4),(16,1),(3,1),(11,1),(22,1)],[]),
(377866803,759,[(16,1),(1,0),(3,1),(8,4),(0,1),(11,1),(2,1)],[]),
(608553523,1015,[(10,0),(11,1)],[]),
(608553523,999,[(16,3)],[]),
(356895283,1015,[(21,1),(2,1)],[]),
(373672499,1015,[(26,1),(1,0)],[]),
(626379315,983,[(16,3)],[]),
(374721075,1015,[(22,1),(27,1),(2,1)],[59])]
def sl445_8b288 : Array CaseCode := #[(644205107,951,[(16,3)],[]),
(402721331,759,[(3,3),(26,1),(8,2),(16,1),(3,1),(5,1),(12,1),(0,1),(8,0),(2,1),(22,1)],[]),
(403769907,759,[(0,1),(16,3),(16,1),(3,1),(8,0),(22,1)],[]),
(394332723,759,[(8,2),(16,1),(8,0),(1,0),(3,1),(5,1),(0,1),(12,1),(4,1),(2,1),(22,1)],[]),
(360778291,759,[(2,1),(16,3),(16,1),(3,1),(8,0),(22,1)],[]),
(377555507,759,[(26,1),(16,1),(22,3),(22,1),(3,1),(5,1),(0,1),(6,0),(8,0),(1,0),(12,1),(2,1)],[]),
(626068019,983,[(16,3)],[]),
(643893811,951,[(16,3)],[]),
(402983475,1015,[(8,2),(22,3)],[60]),
(404032051,1015,[(16,3),(22,3)],[61]),
(354748979,1015,[(16,3),(16,1),(22,5)],[]),
(354748979,1011,[(16,3),(12,1),(16,1)],[62,63,64]),
(371526195,1015,[(22,1),(22,3)],[]),
(371526195,1011,[(22,3),(22,1),(14,0),(12,1)],[49,52,65,66]),
(343214643,1015,[(8,0),(3,3),(8,2),(22,5)],[]),
(343214643,999,[(8,2),(6,0),(8,0),(5,1)],[62,65,67])]
def sl445_8b304 : Array CaseCode := #[(410323507,1015,[(3,3),(22,3)],[68]),
(359991859,1015,[(12,1),(6,0),(20,0),(2,1),(22,5)],[]),
(376769075,1015,[(6,0),(1,0),(22,1),(24,0)],[66]),
(608504371,999,[(16,3),(22,5)],[]),
(356846131,1015,[(16,1),(16,3),(22,5)],[]),
(373623347,1015,[(22,1),(22,3)],[]),
(373623347,999,[(22,3),(22,1),(5,1),(6,0)],[37,44,63,69]),
(679807539,1015,[(11,1),(4,1)],[70,71]),
(679807539,759,[(16,1),(16,3),(3,1),(7,0),(0,1),(11,1),(8,0),(1,0),(4,1),(2,1),(22,1)],[72,73,74]),
(361040435,1015,[(16,3),(22,3)],[75]),
(361040435,759,[(2,1),(16,3),(16,1),(22,1),(3,1),(8,0)],[]),
(109382195,951,[(22,3),(16,7),(3,7),(8,6)],[38,50,60,61,64,67,68,71,75]),
(377817651,1015,[(22,3)],[]),
(377817651,759,[(16,1),(3,1),(7,0),(0,1),(8,0),(1,0),(2,1)],[76]),
(626330163,983,[(16,3),(22,5)],[]),
(374671923,1015,[(12,1),(2,1),(22,1),(27,1)],[69])]
def sl445_8b320 : Array CaseCode := #[(644155955,951,[(16,3)],[77]),
(371542579,1015,[(16,5),(16,1)],[]),
(343231027,1015,[(3,3),(16,5),(12,1),(8,0),(16,1),(19,1),(2,1)],[62]),
(360008243,983,[(16,1),(8,2),(12,1),(8,0),(11,3),(2,1)],[]),
(376785459,1015,[(2,1),(16,5),(4,1),(19,1)],[78,79]),
(608520755,999,[(16,1),(16,5)],[]),
(373639731,1015,[(16,5),(12,1),(16,1),(26,1),(2,1)],[63]),
(374688307,983,[(16,1),(2,1),(22,3),(12,1),(22,1),(11,3)],[78]),
(679823923,759,[(16,1),(19,1),(16,5),(3,1),(2,1),(8,0),(11,1),(12,1),(22,1)],[80]),
(377834035,759,[(2,1),(16,5),(16,1),(3,1),(12,1),(8,0),(11,1)],[79]),
(644172339,951,[(16,1),(16,5)],[]),
(403016243,1015,[(8,2)],[]),
(343247411,1015,[(3,3),(6,0),(8,0),(23,1),(1,0)],[65]),
(360024627,1015,[(23,1),(2,1)],[]),
(376801843,951,[(8,2),(6,0),(8,0),(3,7),(5,1),(11,5)],[66,79]),
(608537139,1015,[(4,1),(23,1),(11,1)],[])]
def sl445_8b336 : Array CaseCode := #[(608537139,999,[(16,3)],[]),
(356878899,1015,[(23,1),(2,1)],[]),
(407210547,1015,[],[]),
(626362931,983,[(16,3)],[]),
(408259123,1015,[(16,3)],[]),
(679840307,759,[(23,1),(16,1),(16,3),(3,1),(0,1),(22,1),(8,0),(11,1),(2,1),(22,5)],[]),
(359996979,887,[(8,0),(16,3),(12,1),(16,1),(6,0),(4,3)],[]),
(376774195,887,[(8,0),(22,3),(3,5),(1,0),(6,0),(22,1),(4,3),(12,1)],[81]),
(608509491,999,[(16,3),(3,5)],[]),
(356851251,1015,[(3,5),(16,1),(16,3)],[]),
(373628467,1015,[(3,5),(22,1),(22,3)],[]),
(361045555,759,[(8,4),(2,1),(3,1),(16,3),(16,1),(4,1),(22,1)],[]),
(377822771,759,[(8,4),(3,1),(16,1),(1,0),(0,1),(6,0),(4,1),(2,1)],[82]),
(626335283,983,[(16,3),(3,5)],[]),
(374677043,1015,[(3,5),(12,1),(11,1),(27,1),(2,1)],[81,82]),
(644161075,951,[(16,3),(3,5)],[])]
def sl445_8b352 : Array CaseCode := #[(608525875,999,[(16,1)],[]),
(373644851,1015,[(26,1),(2,1)],[]),
(377839155,759,[(2,1),(3,1),(8,4),(16,1),(16,5),(4,1),(12,1),(11,1)],[]),
(644177459,951,[(16,1)],[]),
(608542259,1015,[(8,0),(11,3),(24,0),(11,1)],[]),
(608542259,999,[(16,3)],[]),
(356884019,1015,[(22,1),(21,1),(2,1)],[83]),
(626368051,983,[(16,3)],[]),
(374709811,951,[(16,3),(16,1),(3,7),(8,4),(4,5),(11,3)],[59,78,79,81,82,83]),
(357110323,999,[(16,1)],[]),
(373887539,999,[(16,5)],[]),
(626594355,983,[(16,3)],[]),
(644420147,951,[(16,3)],[]),
(42537523,999,[(4,1)],[84,85]),
(626594355,967,[(16,3),(16,1),(16,2)],[30,56,86]),
(374936115,999,[(16,1)],[])]
def sl445_8b368 : Array CaseCode := #[(644420147,935,[(16,3),(16,5),(16,6)],[31,47,57,86]),
(374690355,983,[(16,1),(2,1),(22,3),(22,1),(12,1)],[83]),
(679825971,759,[(21,1),(16,1),(16,5),(3,1),(4,1),(8,0),(22,1)],[]),
(377836083,759,[(2,1),(3,1),(16,1),(16,5),(4,1),(8,0)],[]),
(644174387,951,[(16,1)],[]),
(404066867,1015,[(16,3)],[]),
(405115443,1015,[],[]),
(410358323,1015,[(3,3)],[]),
(626364979,983,[(16,3)],[]),
(374706739,951,[(12,1),(16,3),(16,1),(4,5)],[69,82]),
(679842355,759,[(26,1),(16,1),(16,3),(3,1),(0,1),(4,1),(8,0),(22,1),(2,1),(22,5)],[]),
(644437555,919,[(16,5),(16,1),(16,4)],[32,58,86]),
(679843379,759,[(16,1),(27,1),(16,5),(3,1),(4,1),(8,0),(11,1),(12,1)],[]),
(572866819,1018,[(16,4)],[]),
(354763011,990,[(8,4),(16,0),(16,1)],[]),
(608518403,1006,[(16,4)],[])]
def sl445_8b384 : Array CaseCode := #[(356860163,990,[(8,4),(3,0)],[]),
(679821571,766,[],[]),
(377831683,766,[(8,4),(27,0),(11,1)],[]),
(644169987,958,[(16,4)],[]),
(555057411,1020,[(22,4)],[]),
(370508035,958,[(8,4)],[]),
(572883203,1018,[(22,4)],[]),
(608534787,1006,[(22,4)],[]),
(373653763,958,[(8,4),(3,0)],[]),
(626360579,990,[(22,4)],[]),
(679837955,766,[],[]),
(573064451,1017,[],[]),
(608716035,1005,[],[]),
(644367619,957,[],[]),
(126388483,639,[(8,2)],[]),
(126388483,891,[],[])]
def sl445_8b400 : Array CaseCode := #[(608733443,1003,[],[]),
(626559235,987,[],[]),
(644385027,955,[],[]),
(141887747,639,[(8,2)],[]),
(59314435,759,[],[]),
(126423299,639,[(11,1),(8,2)],[]),
(59314435,999,[(11,1)],[]),
(126423299,879,[(11,1)],[]),
(626594051,975,[],[]),
(644419843,943,[],[]),
(644437251,927,[],[]),
(608733459,1003,[],[]),
(644385043,955,[],[]),
(141887763,639,[(8,2),(16,0)],[]),
(59314451,759,[],[]),
(126423315,639,[(8,2)],[])]
def sl445_8b416 : Array CaseCode := #[(59314451,999,[],[]),
(126423315,879,[],[]),
(644419859,943,[],[]),
(352590883,894,[(8,0),(16,0)],[]),
(369368099,894,[(8,0),(22,0)],[]),
(679746595,639,[(8,4)],[]),
(344202275,639,[(8,4),(22,0)],[87]),
(377756707,639,[(8,4)],[88]),
(554966051,893,[(3,5)],[]),
(608443427,879,[(3,5)],[]),
(626269219,863,[(3,5)],[]),
(644095011,831,[(3,5)],[]),
(338975779,887,[],[]),
(537156643,894,[],[]),
(608459811,879,[],[]),
(70589475,879,[(8,2)],[])]
def sl445_8b432 : Array CaseCode := #[(137698339,639,[(8,2)],[]),
(537205795,894,[(22,4)],[]),
(302324771,891,[(8,2)],[]),
(555031587,893,[(22,4)],[]),
(608508963,879,[(22,4)],[]),
(373627939,879,[(22,0)],[0]),
(679812131,639,[],[1,89]),
(109386787,831,[],[2]),
(377822243,639,[],[3]),
(626334755,863,[(22,4)],[]),
(644160547,831,[],[90]),
(537222179,894,[(16,4)],[]),
(644176931,831,[(16,4)],[]),
(339057699,887,[],[]),
(537238563,894,[],[]),
(608541731,879,[],[])]
def sl445_8b448 : Array CaseCode := #[(626367523,863,[],[]),
(310447139,763,[(8,4)],[]),
(555027491,1013,[],[]),
(608504867,999,[],[]),
(626330659,983,[],[]),
(644156451,951,[],[]),
(555221027,1020,[],[]),
(608698403,1006,[],[]),
(626524195,990,[],[]),
(644349987,958,[],[]),
(352616483,1018,[(8,0)],[91]),
(369393699,1018,[(8,0)],[92]),
(554991651,1017,[(3,5)],[]),
(679772195,763,[(8,0),(3,5)],[]),
(608469027,1003,[(3,5)],[]),
(626294819,987,[(3,5)],[])]
def sl445_8b464 : Array CaseCode := #[(644120611,955,[(3,5)],[]),
(137691171,759,[],[87]),
(137707555,759,[(2,0)],[91]),
(137723939,759,[],[88,92]),
(608715811,1005,[],[]),
(59314211,759,[(11,0)],[]),
(59314211,999,[(11,0)],[]),
(626593827,975,[],[]),
(644419619,943,[],[]),
(644437027,927,[],[]),
(573064483,1017,[],[]),
(608716067,1005,[],[]),
(644367651,957,[],[]),
(608733475,1003,[],[]),
(626559267,987,[],[]),
(644385059,955,[],[])]
def sl445_8b480 : Array CaseCode := #[(137693475,759,[],[]),
(126423331,639,[(8,2)],[93]),
(126423331,879,[],[94]),
(626594083,975,[],[]),
(644419875,943,[],[]),
(644437283,927,[],[]),
(310647875,639,[(8,4)],[87]),
(554966083,893,[],[]),
(572791875,891,[],[]),
(626269251,863,[],[]),
(537156675,894,[],[]),
(644111427,831,[],[]),
(537173059,894,[],[]),
(302292035,891,[(8,2),(3,0)],[]),
(554998851,893,[],[]),
(572824643,891,[],[])]
def sl445_8b496 : Array CaseCode := #[(371498051,891,[(22,0)],[4]),
(679779395,639,[(6,0)],[]),
(377789507,639,[],[5]),
(626302019,863,[],[]),
(644127811,831,[],[]),
(537222211,894,[],[]),
(572873795,891,[],[]),
(555064387,893,[],[]),
(572890179,891,[],[]),
(338009155,879,[],[6]),
(555221059,1020,[],[]),
(573046851,1018,[],[]),
(338165827,1006,[],[]),
(626524227,990,[],[]),
(137658435,759,[(1,0)],[87]),
(337936451,1003,[(8,4)],[])]
def sl445_8b512 : Array CaseCode := #[(344227907,751,[(8,4)],[]),
(555024451,1005,[],[]),
(572850243,1003,[],[]),
(626327619,975,[],[]),
(573064259,1017,[],[]),
(338183235,1005,[],[]),
(644367427,957,[],[]),
(338200643,1003,[],[]),
(626559043,987,[],[]),
(644384835,955,[],[]),
(371525699,1003,[],[7]),
(679807043,751,[],[]),
(109381699,943,[],[8]),
(626329667,975,[],[]),
(644155459,943,[],[]),
(573064515,1017,[(22,6)],[])]
def sl445_8b528 : Array CaseCode := #[(608716099,1005,[(22,6)],[]),
(644367683,957,[],[95]),
(137659715,759,[],[]),
(126388547,639,[(8,2),(8,0)],[]),
(126388547,891,[(8,2)],[]),
(608733507,1003,[(22,6)],[]),
(626559299,987,[(22,6)],[]),
(644385091,955,[],[96]),
(137693507,759,[],[]),
(137709891,759,[],[]),
(137726275,759,[],[]),
(626594115,975,[(22,6)],[]),
(644419907,943,[],[97]),
(644437315,927,[],[98]),
(126458179,575,[(8,2),(8,0)],[95,96,97,98]),
(126388563,639,[(8,2)],[])]
def sl445_8b544 : Array CaseCode := #[(126388563,891,[],[]),
(608733523,1003,[(16,6)],[]),
(644385107,955,[(16,6)],[]),
(126159187,639,[(8,2)],[]),
(644419923,943,[(16,6)],[]),
(573064547,1017,[],[]),
(608716131,1005,[],[]),
(137922915,759,[],[]),
(126388579,639,[(8,2)],[]),
(137922915,1011,[],[]),
(126388579,891,[],[]),
(608733539,1003,[],[]),
(626559331,987,[],[]),
(126159203,639,[(22,0),(8,2)],[]),
(59314531,759,[],[]),
(126423395,639,[(8,2)],[])]
def sl445_8b560 : Array CaseCode := #[(59314531,999,[],[]),
(126423395,879,[],[]),
(626594147,975,[],[]),
(573064704,1020,[],[]),
(573064704,1016,[(16,5),(16,1),(16,4)],[24,99,100]),
(69748224,1020,[],[]),
(338183680,1020,[(22,3)],[]),
(371738112,1020,[],[]),
(608716288,1020,[],[]),
(608716288,1004,[(16,5),(16,1),(16,4)],[25,99,101]),
(373835264,1020,[],[]),
(644367872,956,[(16,5),(16,1),(16,4)],[26,100,101]),
(137659904,766,[],[]),
(370443776,1020,[(22,1)],[]),
(572818944,1018,[],[]),
(679773696,766,[],[])]
def sl445_8b576 : Array CaseCode := #[(344229376,766,[(16,1),(22,1)],[]),
(377783808,766,[],[]),
(608470528,1006,[],[]),
(644122112,958,[],[]),
(137692672,766,[],[]),
(370476544,1020,[(16,1),(22,1)],[]),
(572851712,1018,[(16,5)],[]),
(337970688,1006,[(16,1)],[]),
(608503296,1006,[(16,5)],[]),
(679806464,766,[],[102]),
(377816576,766,[(16,1)],[]),
(644154880,958,[(16,5)],[]),
(137725440,766,[],[]),
(572884480,1018,[],[]),
(371557888,958,[(16,1)],[]),
(608536064,1006,[],[])]
def sl445_8b592 : Array CaseCode := #[(679839232,766,[],[]),
(137923072,766,[],[]),
(338201088,1018,[(22,3)],[]),
(354978304,1018,[(16,3)],[]),
(371755520,1018,[],[]),
(608733696,1006,[],[]),
(626559488,990,[],[]),
(644385280,958,[],[]),
(137923072,1018,[],[]),
(76057088,1018,[(8,2)],[103]),
(608733696,1018,[],[]),
(608733696,1002,[(16,3),(16,5),(16,6)],[27,99,104,105]),
(357075456,1018,[],[]),
(373852672,1018,[],[]),
(626559488,986,[(16,3),(16,1),(16,2)],[28,104,106]),
(374901248,1018,[],[])]
def sl445_8b608 : Array CaseCode := #[(644385280,954,[(16,3),(16,5),(16,6)],[29,100,105,106]),
(403769856,766,[],[]),
(360778240,766,[],[]),
(626067968,990,[],[]),
(137693696,766,[],[]),
(354748928,1018,[(16,1)],[]),
(371526144,1018,[(22,1)],[]),
(608504320,1006,[(22,5)],[]),
(373623296,1006,[(22,1)],[]),
(679807488,766,[],[107]),
(361040384,766,[(16,1),(22,1)],[]),
(109382144,958,[],[]),
(377817600,766,[],[]),
(626330112,990,[(22,5)],[]),
(644155904,958,[],[108]),
(137710080,766,[],[])]
def sl445_8b624 : Array CaseCode := #[(608520704,1006,[(16,5)],[]),
(374688256,990,[(16,1),(22,1)],[]),
(679823872,766,[],[109]),
(377833984,766,[(16,1)],[]),
(644172288,958,[(16,5)],[]),
(137726464,766,[],[]),
(608537088,1006,[],[]),
(626362880,990,[],[]),
(679840256,766,[],[]),
(59314688,766,[(3,0)],[]),
(357110272,1006,[],[]),
(626594304,990,[],[]),
(59314688,1006,[(3,2)],[]),
(42537472,1006,[(3,2)],[110]),
(626594304,974,[(16,3),(16,1),(16,2)],[30,104,111]),
(374936064,1006,[],[])]
def sl445_8b640 : Array CaseCode := #[(644420096,942,[(16,3),(16,5),(16,6)],[31,101,105,111]),
(137712128,766,[],[]),
(374690304,990,[(22,1)],[]),
(679825920,766,[],[]),
(377836032,766,[],[]),
(644174336,958,[],[]),
(626364928,990,[],[]),
(374706688,958,[(16,1)],[]),
(644437504,926,[(16,5),(16,1),(16,4)],[32,106,111]),
(137729536,766,[(3,0)],[]),
(679843328,766,[],[]),
(310496528,639,[(8,4),(0,0)],[]),
(344050960,639,[(8,4)],[]),
(377605392,639,[(8,4)],[]),
(302107920,894,[(8,0),(5,0)],[]),
(336710928,893,[(8,4)],[])]
def sl445_8b656 : Array CaseCode := #[(572640528,891,[],[]),
(608292112,879,[],[]),
(643943696,831,[],[]),
(137658640,1014,[(7,0),(16,6)],[]),
(337936656,1018,[(14,0),(5,0)],[]),
(679772432,766,[],[]),
(608469264,1006,[(16,4)],[]),
(644120848,958,[(16,4)],[]),
(137692432,765,[(8,2)],[]),
(608503056,1005,[(3,4)],[]),
(644154640,957,[(3,4)],[]),
(608820496,879,[],[]),
(644472080,831,[],[]),
(137665808,639,[(1,0),(8,2)],[]),
(137665808,631,[(16,6),(1,0),(3,6),(5,0)],[112,113,114]),
(608476432,879,[],[113])]
def sl445_8b672 : Array CaseCode := #[(644128016,831,[],[114]),
(137698576,639,[(8,2)],[]),
(608509200,879,[(16,4)],[]),
(644160784,831,[(16,4)],[]),
(137731344,639,[(8,2)],[]),
(608541968,879,[],[]),
(608733456,1003,[],[]),
(644385040,955,[],[]),
(126423312,879,[],[]),
(644419856,943,[],[]),
(679595296,759,[(7,0),(3,6),(16,7),(8,0),(4,6),(14,0),(8,4),(10,0),(22,7)],[]),
(352439584,1014,[(7,0),(16,3)],[]),
(369216800,1014,[(7,0),(22,3)],[]),
(554814752,1013,[],[]),
(387042592,887,[(7,0)],[]),
(572640544,1011,[],[])]
def sl445_8b688 : Array CaseCode := #[(337759520,1011,[(14,0),(3,2)],[]),
(661769504,887,[(7,0),(8,0)],[]),
(74566944,887,[(10,0),(3,2)],[]),
(343002400,887,[(7,0),(22,3)],[]),
(359779616,887,[(7,0),(16,3)],[]),
(376556832,887,[(7,0)],[]),
(608292128,999,[],[]),
(626117920,983,[],[]),
(643943712,951,[],[]),
(679595296,639,[(8,4),(3,6),(16,7),(1,0),(22,7)],[]),
(344050976,639,[(8,4),(22,0)],[87]),
(377605408,639,[(8,4),(22,3)],[]),
(554814752,893,[],[]),
(572640544,891,[],[]),
(608292128,879,[],[]),
(626117920,863,[],[])]
def sl445_8b704 : Array CaseCode := #[(643943712,831,[],[]),
(679595296,887,[(3,6),(7,0),(16,7),(1,0),(22,7)],[]),
(679595296,631,[(3,6),(16,7),(1,0),(22,7),(4,6),(8,4),(16,3),(7,0),(14,0)],[115,116,117,118,119,120,121,122,123,124,125,126,127,128]),
(293719328,887,[(7,0)],[]),
(75615520,887,[(3,2),(1,0)],[]),
(344050976,887,[(7,0),(22,3)],[]),
(360828192,887,[(7,0),(16,3)],[]),
(377605408,887,[(7,0)],[]),
(554814752,885,[(16,3),(3,6)],[115,129,130,131]),
(303156512,887,[],[116]),
(336710944,887,[(16,3)],[117]),
(370265376,887,[],[118]),
(572640544,883,[(16,3),(3,6)],[119,129,132,133,134]),
(337759520,887,[(22,3)],[120]),
(354536736,887,[(16,3)],[121]),
(371313952,887,[],[122])]
def sl445_8b720 : Array CaseCode := #[(608292128,887,[(14,0)],[]),
(608292128,871,[(16,3),(3,6)],[123,130,132,135,136]),
(356633888,887,[],[124]),
(373411104,887,[],[125]),
(626117920,855,[(16,3),(3,6)],[126,133,135,137]),
(374459680,887,[],[127]),
(643943712,823,[(16,3),(3,6)],[128,131,134,136,137]),
(137707808,766,[(8,0)],[91]),
(572866848,1018,[(16,4)],[]),
(337985824,1018,[(14,0),(11,1)],[]),
(354763040,990,[(16,1),(16,0),(3,0)],[33]),
(661995808,894,[(8,0)],[]),
(343228704,894,[(7,0),(16,0)],[]),
(608518432,1006,[(16,4)],[]),
(356860192,990,[(14,0),(3,0)],[]),
(679821600,766,[],[])]
def sl445_8b736 : Array CaseCode := #[(377831712,766,[(7,0),(4,0),(11,1)],[]),
(644170016,958,[(16,4)],[]),
(137724192,766,[(8,0)],[92]),
(555057440,1020,[(22,4)],[]),
(370508064,958,[(4,2)],[34]),
(572883232,1018,[(22,4)],[]),
(338002208,1018,[(14,0)],[138]),
(662012192,894,[(8,0)],[]),
(343245088,894,[(7,0),(22,0)],[]),
(608534816,1006,[(22,4)],[]),
(373653792,958,[(14,0),(3,0)],[138]),
(626360608,990,[(22,4)],[]),
(679837984,766,[],[]),
(573064480,1017,[],[129]),
(338183456,1017,[(3,2)],[]),
(662193440,893,[(8,2)],[])]
def sl445_8b752 : Array CaseCode := #[(343426336,893,[(22,2)],[139]),
(376980768,893,[],[140]),
(608716064,1005,[],[130]),
(644367648,957,[],[131]),
(137741600,759,[(7,0),(16,5)],[]),
(337970464,1003,[(5,0)],[35]),
(376800544,831,[(16,0)],[36]),
(137922848,763,[],[]),
(343443744,891,[(22,2)],[141]),
(360220960,891,[(16,2)],[142]),
(376998176,891,[],[143]),
(608733472,1003,[],[132]),
(626559264,987,[],[133]),
(644385056,955,[],[134]),
(137693472,763,[(8,2),(3,6)],[]),
(661981472,891,[],[])]
def sl445_8b768 : Array CaseCode := #[(74778912,1003,[],[]),
(376768800,891,[(14,0),(11,0)],[]),
(608504096,1003,[(3,4)],[]),
(373623072,1003,[],[37,138]),
(679807264,763,[],[]),
(109381920,955,[(3,6)],[38]),
(626329888,987,[(3,4)],[]),
(644155680,955,[(3,4)],[]),
(138009888,639,[(8,2)],[]),
(406445344,887,[(8,2)],[]),
(344579360,639,[(10,0)],[]),
(378133792,639,[(10,0)],[]),
(608820512,879,[(8,4)],[]),
(626646304,863,[(8,4)],[]),
(644472096,831,[(8,4)],[]),
(342957344,879,[],[])]
def sl445_8b784 : Array CaseCode := #[(137698592,759,[(7,0),(8,0)],[]),
(137698592,887,[(7,0)],[144]),
(137698592,639,[(1,0),(8,2)],[]),
(137698592,631,[(1,0),(3,6)],[139,141,145,146,147,148]),
(608509216,879,[(22,4)],[146]),
(679812384,639,[(8,0),(7,0)],[149]),
(109387040,831,[(7,0)],[144]),
(377822496,639,[(7,0)],[150]),
(626335008,863,[(22,4)],[147]),
(644160800,831,[],[148,151]),
(137714976,759,[(7,0),(16,5)],[]),
(137714976,639,[(1,0),(8,2)],[]),
(137714976,631,[(16,5),(1,0),(3,6),(12,0)],[142,152,153]),
(644177184,831,[(16,4)],[153]),
(137731360,759,[(7,0),(22,5)],[]),
(137731360,887,[(7,0)],[])]
def sl445_8b800 : Array CaseCode := #[(137731360,639,[(1,0),(8,2)],[]),
(137731360,631,[(1,0),(3,6),(22,5)],[140,143,154,155,156]),
(608541984,879,[],[155]),
(626367776,863,[],[156]),
(679845152,639,[(8,0),(7,0)],[]),
(126423328,639,[(4,0),(10,0)],[]),
(42537248,1003,[],[]),
(126423328,879,[(4,2)],[]),
(626594080,975,[],[135]),
(644419872,943,[],[136]),
(644437280,927,[],[137]),
(310496576,639,[(8,4)],[87]),
(554814784,893,[],[]),
(572640576,891,[],[]),
(626117952,863,[],[]),
(572866880,1018,[(16,4)],[])]
def sl445_8b816 : Array CaseCode := #[(661995840,894,[],[]),
(644170048,958,[(16,4)],[]),
(555057472,1020,[(22,4)],[]),
(370508096,958,[(22,0)],[40]),
(572883264,1018,[(22,4)],[]),
(626360640,990,[(22,4)],[]),
(573064512,1017,[],[]),
(608716096,1005,[],[]),
(662193472,893,[],[]),
(376980800,893,[],[]),
(644367680,957,[],[]),
(126388544,891,[],[]),
(608733504,1003,[],[]),
(662210880,891,[],[]),
(360220992,891,[],[]),
(376998208,891,[],[])]
def sl445_8b832 : Array CaseCode := #[(626559296,987,[],[]),
(644385088,955,[],[]),
(137742656,759,[(7,0)],[]),
(59314496,751,[],[]),
(626594112,975,[],[]),
(59366720,639,[(8,2)],[157]),
(626646336,863,[],[]),
(137715008,639,[(8,2)],[]),
(644177216,831,[],[]),
(626367808,863,[],[]),
(644437312,927,[],[]),
(310496592,639,[(8,4),(2,0)],[]),
(344051024,639,[(8,4)],[]),
(377605456,639,[(8,4)],[]),
(572640592,891,[(16,4)],[]),
(354536784,863,[(16,0),(8,4)],[])]
def sl445_8b848 : Array CaseCode := #[(608292176,879,[(16,4)],[]),
(643943760,831,[(16,4)],[]),
(354978128,987,[(16,2),(3,2)],[]),
(126388560,891,[],[158]),
(608733520,1003,[],[]),
(357075280,987,[(3,2)],[]),
(662210896,891,[],[]),
(376998224,891,[(11,2)],[]),
(644385104,955,[],[]),
(137709904,735,[(8,2)],[]),
(644172112,927,[(16,4),(3,4)],[]),
(644419920,943,[],[]),
(137711952,735,[(8,2)],[]),
(644174160,927,[(3,4)],[]),
(644472144,831,[],[]),
(137731408,639,[(27,0),(8,2)],[])]
def sl445_8b864 : Array CaseCode := #[(310496608,639,[(8,4)],[88]),
(554814816,893,[(22,4)],[]),
(572640608,891,[(22,4)],[]),
(626117984,863,[(22,4)],[]),
(573064544,1017,[],[]),
(608716128,1005,[],[]),
(373835104,957,[(3,2)],[]),
(662193504,893,[],[]),
(370443616,957,[(22,0)],[41]),
(370476384,957,[(11,4),(16,1)],[42]),
(377816416,703,[(3,0)],[43]),
(137725280,703,[(8,2)],[]),
(572884320,955,[(16,4)],[]),
(608535904,943,[(16,4)],[]),
(662013280,831,[],[]),
(679839072,703,[],[])]
def sl445_8b880 : Array CaseCode := #[(126388576,891,[(3,2)],[]),
(608733536,1003,[],[]),
(373852512,955,[(3,2)],[]),
(626559328,987,[],[]),
(662210912,891,[],[]),
(373623136,943,[(22,0)],[44,138]),
(137742688,759,[(7,0)],[]),
(626594144,975,[],[]),
(626364768,927,[(3,4)],[]),
(662263136,863,[],[]),
(59366752,639,[(8,2)],[]),
(137923089,765,[],[]),
(338201105,1017,[(22,3)],[]),
(608733713,1005,[],[]),
(137923089,1017,[],[]),
(76057105,1017,[(16,2)],[159])]
def sl445_8b896 : Array CaseCode := #[(608733713,1017,[],[]),
(608733713,1001,[(16,6),(16,2),(16,4)],[45,99,160]),
(373852689,1017,[],[]),
(644385297,953,[(16,6),(16,2),(16,4)],[46,100,160]),
(402721297,765,[],[]),
(137693713,765,[],[]),
(371526161,1017,[(22,1)],[]),
(608504337,1005,[(22,5)],[]),
(373623313,1005,[(22,1)],[]),
(679807505,765,[],[161]),
(109382161,957,[],[]),
(377817617,765,[],[]),
(644155921,957,[],[162]),
(608537105,1005,[],[]),
(59314705,765,[],[163]),
(373887505,1005,[],[])]
def sl445_8b912 : Array CaseCode := #[(644420113,957,[],[]),
(59314705,1005,[],[164]),
(42537489,1005,[(13,0)],[165]),
(644420113,941,[(16,6),(16,2),(16,4)],[47,101,160]),
(137728529,765,[],[]),
(679842321,765,[],[]),
(276942113,639,[(8,1),(3,3)],[]),
(344050977,639,[(22,0)],[9]),
(608292129,879,[],[]),
(608535841,1005,[(22,4)],[]),
(608733473,1003,[],[]),
(608820513,879,[],[]),
(137698593,639,[(1,0)],[]),
(608509217,879,[(16,4),(22,4)],[]),
(644160801,831,[(16,4)],[166]),
(608541985,879,[],[])]
def sl445_8b928 : Array CaseCode := #[(126423329,879,[],[]),
(644419873,943,[],[]),
(276942145,639,[(8,1)],[]),
(310496577,639,[(6,0)],[]),
(377605441,639,[],[10]),
(572640577,891,[],[]),
(337759553,879,[(6,0)],[]),
(643943745,831,[],[]),
(137725249,765,[(16,4)],[11]),
(608535873,1005,[(16,4),(22,4)],[]),
(608733505,1003,[(16,6)],[]),
(644385089,955,[(16,6)],[]),
(371525953,1003,[(5,0)],[49]),
(679807297,751,[],[]),
(109381953,943,[(16,6)],[50]),
(644155713,943,[(16,4)],[])]
def sl445_8b944 : Array CaseCode := #[(377033025,879,[(16,2)],[]),
(644419905,943,[(16,6)],[]),
(361356609,607,[(16,2),(5,0),(16,0)],[12,51,102,167]),
(644472129,831,[],[167]),
(137731393,639,[(1,0)],[]),
(276942177,639,[(8,1)],[]),
(344051041,639,[(22,0)],[13]),
(608292193,879,[],[]),
(608733537,1003,[],[]),
(371525985,955,[(5,0),(22,0)],[52]),
(608536929,943,[(16,4)],[]),
(126423393,879,[(16,2)],[]),
(662245729,879,[],[]),
(276942370,639,[(8,1)],[]),
(344051234,639,[(10,0)],[]),
(377605666,639,[(10,0)],[])]
def sl445_8b960 : Array CaseCode := #[(608292386,879,[],[]),
(626118178,863,[],[]),
(643943970,831,[],[]),
(137693730,763,[],[]),
(608504354,1003,[(22,5)],[]),
(373623330,1003,[(22,1)],[]),
(679807522,763,[],[168]),
(361040418,763,[(16,1),(22,1)],[]),
(109382178,955,[],[]),
(377817634,763,[],[]),
(626330146,987,[(22,5)],[]),
(644155938,955,[],[169]),
(608520738,1003,[(16,5)],[]),
(374688290,987,[(16,1),(22,1)],[]),
(377834018,763,[(16,1)],[]),
(644172322,955,[(16,5)],[])]
def sl445_8b976 : Array CaseCode := #[(608537122,1003,[],[]),
(626362914,987,[],[]),
(126423586,639,[],[53,170]),
(126423586,879,[],[171]),
(626594338,975,[],[]),
(644420130,943,[],[]),
(644437538,927,[],[]),
(276942370,763,[],[]),
(344051234,763,[],[]),
(360828450,763,[],[]),
(377605666,763,[],[]),
(608292386,1003,[],[]),
(626118178,987,[],[]),
(643943970,955,[],[]),
(405872162,755,[(8,1),(8,0),(11,1)],[159,172,173]),
(276897314,763,[],[])]
def sl445_8b992 : Array CaseCode := #[(293674530,761,[(4,4),(5,0),(11,1),(18,0)],[54,103,174]),
(360783394,763,[],[]),
(377560610,763,[],[]),
(373366306,1003,[],[]),
(626073122,987,[(18,0)],[172]),
(643898914,955,[],[173,174]),
(59314722,763,[],[175]),
(357110306,1003,[],[]),
(373887522,1003,[],[]),
(626594338,987,[],[]),
(644420130,955,[],[]),
(59314722,1003,[],[176]),
(126423586,1003,[],[177]),
(626594338,971,[(16,3),(16,1),(16,2)],[56,104,178]),
(374936098,1003,[],[]),
(644420130,939,[(16,3),(16,5),(16,6)],[57,105,160,178])]
def sl445_8b1008 : Array CaseCode := #[(137712162,763,[],[]),
(141906466,763,[],[]),
(374690338,987,[(22,1)],[]),
(679825954,763,[],[]),
(377836066,763,[],[]),
(644174370,955,[],[]),
(137728546,763,[],[]),
(141922850,763,[],[]),
(626364962,987,[],[]),
(374706722,955,[(16,1)],[]),
(679842338,763,[],[]),
(644437538,923,[(16,5),(16,1),(16,4)],[58,106,178]),
(137729570,763,[],[179]),
(141923874,763,[(16,1)],[]),
(679843362,763,[],[]),
(626376770,863,[],[])]
def sl445_8b1024 : Array CaseCode := #[(389139778,887,[],[]),
(108121410,831,[],[14]),
(679595330,639,[(1,0)],[]),
(276942146,639,[(8,1),(3,3)],[]),
(377605442,639,[],[15]),
(608292162,879,[],[]),
(626117954,863,[],[]),
(643943746,831,[],[]),
(108383554,831,[(8,5)],[]),
(137740610,759,[],[180,181]),
(108380482,831,[],[60,181]),
(108381506,831,[(16,5)],[61]),
(373639490,1003,[(12,0)],[63]),
(661997890,891,[],[]),
(108349762,955,[(16,5)],[64]),
(644172098,955,[(16,4)],[])]
def sl445_8b1040 : Array CaseCode := #[(608536898,1003,[(22,4)],[]),
(662014274,891,[],[]),
(626362690,987,[(22,4)],[]),
(679840066,763,[],[]),
(59314498,751,[],[]),
(108597570,943,[],[]),
(377033026,879,[],[]),
(626594114,975,[(22,6)],[]),
(644419906,943,[],[182]),
(137728322,751,[(6,0)],[]),
(662016322,879,[],[]),
(626364738,975,[(22,4)],[]),
(374706498,943,[(12,0),(22,0)],[69]),
(679842114,751,[],[]),
(378133826,703,[(22,0)],[70]),
(108649794,831,[],[71,170])]
def sl445_8b1056 : Array CaseCode := #[(59366722,639,[(1,0)],[183,184]),
(277470530,639,[(7,0)],[]),
(378133826,639,[],[72]),
(378133826,831,[],[73]),
(378133826,575,[(22,1)],[16,74,107,161,168,171,185]),
(626646338,863,[],[185]),
(644472130,831,[(22,0)],[]),
(108354882,831,[(16,5)],[75]),
(137715010,639,[(1,0)],[]),
(644177218,831,[(16,4)],[186]),
(626105666,927,[],[]),
(137731394,639,[(1,0)],[]),
(626367810,863,[],[]),
(679845186,639,[],[76,170]),
(644437314,927,[],[187]),
(126458178,703,[],[])]
def sl445_8b1072 : Array CaseCode := #[(126458178,575,[],[77,108,162,169,170,182,187]),
(276942162,639,[(8,1),(3,3)],[]),
(344051026,639,[(22,0)],[17]),
(377605458,639,[],[18]),
(608292178,879,[],[]),
(643943762,831,[],[]),
(644419922,943,[(16,6)],[]),
(137729362,735,[(6,0)],[188]),
(294247762,637,[(16,2),(16,0),(12,0)],[19,80,109,189]),
(644472146,831,[],[189]),
(137731410,639,[(1,0)],[]),
(276942178,639,[(8,1),(3,3)],[]),
(344051042,639,[(22,0)],[20]),
(608292194,879,[],[]),
(626117986,863,[],[]),
(137740642,759,[],[190])]
def sl445_8b1088 : Array CaseCode := #[(42537314,1003,[],[]),
(126423394,879,[],[]),
(626594146,975,[],[]),
(662245730,879,[],[]),
(662263138,863,[],[]),
(59366754,639,[(1,0)],[]),
(276880964,639,[(8,1)],[]),
(276880964,894,[(1,0)],[]),
(276880964,638,[(8,1),(8,0),(11,4)],[21,163,175,191,192]),
(310435396,639,[(6,0),(11,0)],[]),
(377544260,639,[(15,0)],[]),
(626056772,863,[],[191]),
(643882564,831,[],[192]),
(276880964,751,[],[]),
(276880964,1006,[],[]),
(276880964,750,[(11,4)],[22,164,176,193,194,195])]
def sl445_8b1104 : Array CaseCode := #[(293658180,751,[],[]),
(310435396,751,[(11,0)],[]),
(377544260,751,[],[]),
(626056772,975,[],[194]),
(643882564,943,[],[195]),
(276864580,751,[],[]),
(276864580,750,[(4,0),(4,1)],[84,165,196,197,198]),
(293641796,751,[],[]),
(360750660,719,[(4,0),(13,0),(4,1),(12,0)],[85,110,199]),
(377527876,751,[],[]),
(626040388,975,[(16,1)],[197]),
(643866180,943,[],[198,199]),
(644437572,911,[(16,5),(16,1),(16,4)],[86,111,178]),
(276942164,639,[(8,1)],[]),
(310496596,639,[(6,0)],[]),
(310496612,639,[(6,0)],[])]
def sl445_8b1120 : Array CaseCode := #[(59366756,639,[(1,0)],[200]),
(276942181,639,[(8,1)],[]),
(276942181,638,[(16,6),(8,1),(28,0),(22,6)],[23,179,188,201]),
(310496613,639,[(6,0)],[])]
def sl445_8 : Cases := (1124,fun i => ((if i<560 then (if i<272 then (if i<128 then (if i<64 then (if i<32 then (if i<16 then sl445_8b0 else sl445_8b16) else (if i<48 then sl445_8b32 else sl445_8b48)) else (if i<96 then (if i<80 then sl445_8b64 else sl445_8b80) else (if i<112 then sl445_8b96 else sl445_8b112))) else (if i<192 then (if i<160 then (if i<144 then sl445_8b128 else sl445_8b144) else (if i<176 then sl445_8b160 else sl445_8b176)) else (if i<224 then (if i<208 then sl445_8b192 else sl445_8b208) else (if i<240 then sl445_8b224 else (if i<256 then sl445_8b240 else sl445_8b256))))) else (if i<416 then (if i<336 then (if i<304 then (if i<288 then sl445_8b272 else sl445_8b288) else (if i<320 then sl445_8b304 else sl445_8b320)) else (if i<368 then (if i<352 then sl445_8b336 else sl445_8b352) else (if i<384 then sl445_8b368 else (if i<400 then sl445_8b384 else sl445_8b400)))) else (if i<480 then (if i<448 then (if i<432 then sl445_8b416 else sl445_8b432) else (if i<464 then sl445_8b448 else sl445_8b464)) else (if i<512 then (if i<496 then sl445_8b480 else sl445_8b496) else (if i<528 then sl445_8b512 else (if i<544 then sl445_8b528 else sl445_8b544)))))) else (if i<848 then (if i<704 then (if i<624 then (if i<592 then (if i<576 then sl445_8b560 else sl445_8b576) else (if i<608 then sl445_8b592 else sl445_8b608)) else (if i<656 then (if i<640 then sl445_8b624 else sl445_8b640) else (if i<672 then sl445_8b656 else (if i<688 then sl445_8b672 else sl445_8b688)))) else (if i<768 then (if i<736 then (if i<720 then sl445_8b704 else sl445_8b720) else (if i<752 then sl445_8b736 else sl445_8b752)) else (if i<800 then (if i<784 then sl445_8b768 else sl445_8b784) else (if i<816 then sl445_8b800 else (if i<832 then sl445_8b816 else sl445_8b832))))) else (if i<992 then (if i<912 then (if i<880 then (if i<864 then sl445_8b848 else sl445_8b864) else (if i<896 then sl445_8b880 else sl445_8b896)) else (if i<944 then (if i<928 then sl445_8b912 else sl445_8b928) else (if i<960 then sl445_8b944 else (if i<976 then sl445_8b960 else sl445_8b976)))) else (if i<1056 then (if i<1024 then (if i<1008 then sl445_8b992 else sl445_8b1008) else (if i<1040 then sl445_8b1024 else sl445_8b1040)) else (if i<1088 then (if i<1072 then sl445_8b1056 else sl445_8b1072) else (if i<1104 then sl445_8b1088 else (if i<1120 then sl445_8b1104 else sl445_8b1120))))))))[i % 16]?.getD default)
def scan445_8 := rangeCases 445 sgBase445 scuts445 8 3 sl445_7 sl445_8
theorem j445_8 (o a b : Nat) (x : scan445_8 o a=true) (y : scan445_8 (o+a) b=true) : scan445_8 o (a+b)=true := @joinRange 445 sgBase445 scuts445 8 3 sl445_7 sl445_8 o a b x y
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_0 : scan445_8 0 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_8 : scan445_8 8 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_16 : scan445_8 16 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_24 : scan445_8 24 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_32 : scan445_8 32 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_40 : scan445_8 40 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_48 : scan445_8 48 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_56 : scan445_8 56 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_64 : scan445_8 64 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_72 : scan445_8 72 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_80 : scan445_8 80 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_88 : scan445_8 88 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_96 : scan445_8 96 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_104 : scan445_8 104 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_112 : scan445_8 112 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_120 : scan445_8 120 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_128 : scan445_8 128 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_136 : scan445_8 136 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_144 : scan445_8 144 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_152 : scan445_8 152 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_160 : scan445_8 160 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_168 : scan445_8 168 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_176 : scan445_8 176 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_184 : scan445_8 184 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_192 : scan445_8 192 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_200 : scan445_8 200 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_208 : scan445_8 208 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_216 : scan445_8 216 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_224 : scan445_8 224 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_232 : scan445_8 232 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_240 : scan445_8 240 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_248 : scan445_8 248 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_256 : scan445_8 256 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_264 : scan445_8 264 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_272 : scan445_8 272 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_280 : scan445_8 280 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_288 : scan445_8 288 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_296 : scan445_8 296 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_304 : scan445_8 304 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_312 : scan445_8 312 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_320 : scan445_8 320 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_328 : scan445_8 328 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_336 : scan445_8 336 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_344 : scan445_8 344 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_352 : scan445_8 352 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_360 : scan445_8 360 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_368 : scan445_8 368 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_376 : scan445_8 376 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_384 : scan445_8 384 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_392 : scan445_8 392 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_400 : scan445_8 400 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_408 : scan445_8 408 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_416 : scan445_8 416 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_424 : scan445_8 424 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_432 : scan445_8 432 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_440 : scan445_8 440 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_448 : scan445_8 448 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_456 : scan445_8 456 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_464 : scan445_8 464 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_472 : scan445_8 472 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_480 : scan445_8 480 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_488 : scan445_8 488 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_496 : scan445_8 496 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_504 : scan445_8 504 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_512 : scan445_8 512 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_520 : scan445_8 520 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_528 : scan445_8 528 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_536 : scan445_8 536 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_544 : scan445_8 544 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_552 : scan445_8 552 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_560 : scan445_8 560 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_568 : scan445_8 568 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_576 : scan445_8 576 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_584 : scan445_8 584 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_592 : scan445_8 592 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_600 : scan445_8 600 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_608 : scan445_8 608 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_616 : scan445_8 616 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_624 : scan445_8 624 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_632 : scan445_8 632 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_640 : scan445_8 640 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_648 : scan445_8 648 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_656 : scan445_8 656 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_664 : scan445_8 664 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_672 : scan445_8 672 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_680 : scan445_8 680 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_688 : scan445_8 688 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_696 : scan445_8 696 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_704 : scan445_8 704 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_712 : scan445_8 712 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_720 : scan445_8 720 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_728 : scan445_8 728 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_736 : scan445_8 736 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_744 : scan445_8 744 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_752 : scan445_8 752 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_760 : scan445_8 760 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_768 : scan445_8 768 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_776 : scan445_8 776 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_784 : scan445_8 784 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_792 : scan445_8 792 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_800 : scan445_8 800 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_808 : scan445_8 808 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_816 : scan445_8 816 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_824 : scan445_8 824 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_832 : scan445_8 832 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_840 : scan445_8 840 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_848 : scan445_8 848 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_856 : scan445_8 856 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_864 : scan445_8 864 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_872 : scan445_8 872 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_880 : scan445_8 880 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_888 : scan445_8 888 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_896 : scan445_8 896 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_904 : scan445_8 904 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_912 : scan445_8 912 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_920 : scan445_8 920 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_928 : scan445_8 928 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_936 : scan445_8 936 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_944 : scan445_8 944 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_952 : scan445_8 952 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_960 : scan445_8 960 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_968 : scan445_8 968 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_976 : scan445_8 976 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_984 : scan445_8 984 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_992 : scan445_8 992 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_1000 : scan445_8 1000 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_1008 : scan445_8 1008 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_1016 : scan445_8 1016 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_1024 : scan445_8 1024 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_1032 : scan445_8 1032 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_1040 : scan445_8 1040 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_1048 : scan445_8 1048 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_1056 : scan445_8 1056 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_1064 : scan445_8 1064 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_1072 : scan445_8 1072 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_1080 : scan445_8 1080 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_1088 : scan445_8 1088 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_1096 : scan445_8 1096 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_1104 : scan445_8 1104 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_1112 : scan445_8 1112 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_8_1120 : scan445_8 1120 4=true := by decide +kernel
theorem ck445_8_0m16 : scan445_8 0 16=true := j445_8 0 8 8 ck445_8_0 ck445_8_8
theorem ck445_8_16m16 : scan445_8 16 16=true := j445_8 16 8 8 ck445_8_16 ck445_8_24
theorem ck445_8_32m16 : scan445_8 32 16=true := j445_8 32 8 8 ck445_8_32 ck445_8_40
theorem ck445_8_48m16 : scan445_8 48 16=true := j445_8 48 8 8 ck445_8_48 ck445_8_56
theorem ck445_8_64m16 : scan445_8 64 16=true := j445_8 64 8 8 ck445_8_64 ck445_8_72
theorem ck445_8_80m16 : scan445_8 80 16=true := j445_8 80 8 8 ck445_8_80 ck445_8_88
theorem ck445_8_96m16 : scan445_8 96 16=true := j445_8 96 8 8 ck445_8_96 ck445_8_104
theorem ck445_8_112m16 : scan445_8 112 16=true := j445_8 112 8 8 ck445_8_112 ck445_8_120
theorem ck445_8_128m16 : scan445_8 128 16=true := j445_8 128 8 8 ck445_8_128 ck445_8_136
theorem ck445_8_144m16 : scan445_8 144 16=true := j445_8 144 8 8 ck445_8_144 ck445_8_152
theorem ck445_8_160m16 : scan445_8 160 16=true := j445_8 160 8 8 ck445_8_160 ck445_8_168
theorem ck445_8_176m16 : scan445_8 176 16=true := j445_8 176 8 8 ck445_8_176 ck445_8_184
theorem ck445_8_192m16 : scan445_8 192 16=true := j445_8 192 8 8 ck445_8_192 ck445_8_200
theorem ck445_8_208m16 : scan445_8 208 16=true := j445_8 208 8 8 ck445_8_208 ck445_8_216
theorem ck445_8_224m16 : scan445_8 224 16=true := j445_8 224 8 8 ck445_8_224 ck445_8_232
theorem ck445_8_240m16 : scan445_8 240 16=true := j445_8 240 8 8 ck445_8_240 ck445_8_248
theorem ck445_8_256m16 : scan445_8 256 16=true := j445_8 256 8 8 ck445_8_256 ck445_8_264
theorem ck445_8_272m16 : scan445_8 272 16=true := j445_8 272 8 8 ck445_8_272 ck445_8_280
theorem ck445_8_288m16 : scan445_8 288 16=true := j445_8 288 8 8 ck445_8_288 ck445_8_296
theorem ck445_8_304m16 : scan445_8 304 16=true := j445_8 304 8 8 ck445_8_304 ck445_8_312
theorem ck445_8_320m16 : scan445_8 320 16=true := j445_8 320 8 8 ck445_8_320 ck445_8_328
theorem ck445_8_336m16 : scan445_8 336 16=true := j445_8 336 8 8 ck445_8_336 ck445_8_344
theorem ck445_8_352m16 : scan445_8 352 16=true := j445_8 352 8 8 ck445_8_352 ck445_8_360
theorem ck445_8_368m16 : scan445_8 368 16=true := j445_8 368 8 8 ck445_8_368 ck445_8_376
theorem ck445_8_384m16 : scan445_8 384 16=true := j445_8 384 8 8 ck445_8_384 ck445_8_392
theorem ck445_8_400m16 : scan445_8 400 16=true := j445_8 400 8 8 ck445_8_400 ck445_8_408
theorem ck445_8_416m16 : scan445_8 416 16=true := j445_8 416 8 8 ck445_8_416 ck445_8_424
theorem ck445_8_432m16 : scan445_8 432 16=true := j445_8 432 8 8 ck445_8_432 ck445_8_440
theorem ck445_8_448m16 : scan445_8 448 16=true := j445_8 448 8 8 ck445_8_448 ck445_8_456
theorem ck445_8_464m16 : scan445_8 464 16=true := j445_8 464 8 8 ck445_8_464 ck445_8_472
theorem ck445_8_480m16 : scan445_8 480 16=true := j445_8 480 8 8 ck445_8_480 ck445_8_488
theorem ck445_8_496m16 : scan445_8 496 16=true := j445_8 496 8 8 ck445_8_496 ck445_8_504
theorem ck445_8_512m16 : scan445_8 512 16=true := j445_8 512 8 8 ck445_8_512 ck445_8_520
theorem ck445_8_528m16 : scan445_8 528 16=true := j445_8 528 8 8 ck445_8_528 ck445_8_536
theorem ck445_8_544m16 : scan445_8 544 16=true := j445_8 544 8 8 ck445_8_544 ck445_8_552
theorem ck445_8_560m16 : scan445_8 560 16=true := j445_8 560 8 8 ck445_8_560 ck445_8_568
theorem ck445_8_576m16 : scan445_8 576 16=true := j445_8 576 8 8 ck445_8_576 ck445_8_584
theorem ck445_8_592m16 : scan445_8 592 16=true := j445_8 592 8 8 ck445_8_592 ck445_8_600
theorem ck445_8_608m16 : scan445_8 608 16=true := j445_8 608 8 8 ck445_8_608 ck445_8_616
theorem ck445_8_624m16 : scan445_8 624 16=true := j445_8 624 8 8 ck445_8_624 ck445_8_632
theorem ck445_8_640m16 : scan445_8 640 16=true := j445_8 640 8 8 ck445_8_640 ck445_8_648
theorem ck445_8_656m16 : scan445_8 656 16=true := j445_8 656 8 8 ck445_8_656 ck445_8_664
theorem ck445_8_672m16 : scan445_8 672 16=true := j445_8 672 8 8 ck445_8_672 ck445_8_680
theorem ck445_8_688m16 : scan445_8 688 16=true := j445_8 688 8 8 ck445_8_688 ck445_8_696
theorem ck445_8_704m16 : scan445_8 704 16=true := j445_8 704 8 8 ck445_8_704 ck445_8_712
theorem ck445_8_720m16 : scan445_8 720 16=true := j445_8 720 8 8 ck445_8_720 ck445_8_728
theorem ck445_8_736m16 : scan445_8 736 16=true := j445_8 736 8 8 ck445_8_736 ck445_8_744
theorem ck445_8_752m16 : scan445_8 752 16=true := j445_8 752 8 8 ck445_8_752 ck445_8_760
theorem ck445_8_768m16 : scan445_8 768 16=true := j445_8 768 8 8 ck445_8_768 ck445_8_776
theorem ck445_8_784m16 : scan445_8 784 16=true := j445_8 784 8 8 ck445_8_784 ck445_8_792
theorem ck445_8_800m16 : scan445_8 800 16=true := j445_8 800 8 8 ck445_8_800 ck445_8_808
theorem ck445_8_816m16 : scan445_8 816 16=true := j445_8 816 8 8 ck445_8_816 ck445_8_824
theorem ck445_8_832m16 : scan445_8 832 16=true := j445_8 832 8 8 ck445_8_832 ck445_8_840
theorem ck445_8_848m16 : scan445_8 848 16=true := j445_8 848 8 8 ck445_8_848 ck445_8_856
theorem ck445_8_864m16 : scan445_8 864 16=true := j445_8 864 8 8 ck445_8_864 ck445_8_872
theorem ck445_8_880m16 : scan445_8 880 16=true := j445_8 880 8 8 ck445_8_880 ck445_8_888
theorem ck445_8_896m16 : scan445_8 896 16=true := j445_8 896 8 8 ck445_8_896 ck445_8_904
theorem ck445_8_912m16 : scan445_8 912 16=true := j445_8 912 8 8 ck445_8_912 ck445_8_920
theorem ck445_8_928m16 : scan445_8 928 16=true := j445_8 928 8 8 ck445_8_928 ck445_8_936
theorem ck445_8_944m16 : scan445_8 944 16=true := j445_8 944 8 8 ck445_8_944 ck445_8_952
theorem ck445_8_960m16 : scan445_8 960 16=true := j445_8 960 8 8 ck445_8_960 ck445_8_968
theorem ck445_8_976m16 : scan445_8 976 16=true := j445_8 976 8 8 ck445_8_976 ck445_8_984
theorem ck445_8_992m16 : scan445_8 992 16=true := j445_8 992 8 8 ck445_8_992 ck445_8_1000
theorem ck445_8_1008m16 : scan445_8 1008 16=true := j445_8 1008 8 8 ck445_8_1008 ck445_8_1016
theorem ck445_8_1024m16 : scan445_8 1024 16=true := j445_8 1024 8 8 ck445_8_1024 ck445_8_1032
theorem ck445_8_1040m16 : scan445_8 1040 16=true := j445_8 1040 8 8 ck445_8_1040 ck445_8_1048
theorem ck445_8_1056m16 : scan445_8 1056 16=true := j445_8 1056 8 8 ck445_8_1056 ck445_8_1064
theorem ck445_8_1072m16 : scan445_8 1072 16=true := j445_8 1072 8 8 ck445_8_1072 ck445_8_1080
theorem ck445_8_1088m16 : scan445_8 1088 16=true := j445_8 1088 8 8 ck445_8_1088 ck445_8_1096
theorem ck445_8_1104m16 : scan445_8 1104 16=true := j445_8 1104 8 8 ck445_8_1104 ck445_8_1112
theorem ck445_8_0m32 : scan445_8 0 32=true := j445_8 0 16 16 ck445_8_0m16 ck445_8_16m16
theorem ck445_8_32m32 : scan445_8 32 32=true := j445_8 32 16 16 ck445_8_32m16 ck445_8_48m16
theorem ck445_8_64m32 : scan445_8 64 32=true := j445_8 64 16 16 ck445_8_64m16 ck445_8_80m16
theorem ck445_8_96m32 : scan445_8 96 32=true := j445_8 96 16 16 ck445_8_96m16 ck445_8_112m16
theorem ck445_8_128m32 : scan445_8 128 32=true := j445_8 128 16 16 ck445_8_128m16 ck445_8_144m16
theorem ck445_8_160m32 : scan445_8 160 32=true := j445_8 160 16 16 ck445_8_160m16 ck445_8_176m16
theorem ck445_8_192m32 : scan445_8 192 32=true := j445_8 192 16 16 ck445_8_192m16 ck445_8_208m16
theorem ck445_8_224m32 : scan445_8 224 32=true := j445_8 224 16 16 ck445_8_224m16 ck445_8_240m16
theorem ck445_8_256m32 : scan445_8 256 32=true := j445_8 256 16 16 ck445_8_256m16 ck445_8_272m16
theorem ck445_8_288m32 : scan445_8 288 32=true := j445_8 288 16 16 ck445_8_288m16 ck445_8_304m16
theorem ck445_8_320m32 : scan445_8 320 32=true := j445_8 320 16 16 ck445_8_320m16 ck445_8_336m16
theorem ck445_8_352m32 : scan445_8 352 32=true := j445_8 352 16 16 ck445_8_352m16 ck445_8_368m16
theorem ck445_8_384m32 : scan445_8 384 32=true := j445_8 384 16 16 ck445_8_384m16 ck445_8_400m16
theorem ck445_8_416m32 : scan445_8 416 32=true := j445_8 416 16 16 ck445_8_416m16 ck445_8_432m16
theorem ck445_8_448m32 : scan445_8 448 32=true := j445_8 448 16 16 ck445_8_448m16 ck445_8_464m16
theorem ck445_8_480m32 : scan445_8 480 32=true := j445_8 480 16 16 ck445_8_480m16 ck445_8_496m16
theorem ck445_8_512m32 : scan445_8 512 32=true := j445_8 512 16 16 ck445_8_512m16 ck445_8_528m16
theorem ck445_8_544m32 : scan445_8 544 32=true := j445_8 544 16 16 ck445_8_544m16 ck445_8_560m16
theorem ck445_8_576m32 : scan445_8 576 32=true := j445_8 576 16 16 ck445_8_576m16 ck445_8_592m16
theorem ck445_8_608m32 : scan445_8 608 32=true := j445_8 608 16 16 ck445_8_608m16 ck445_8_624m16
theorem ck445_8_640m32 : scan445_8 640 32=true := j445_8 640 16 16 ck445_8_640m16 ck445_8_656m16
theorem ck445_8_672m32 : scan445_8 672 32=true := j445_8 672 16 16 ck445_8_672m16 ck445_8_688m16
theorem ck445_8_704m32 : scan445_8 704 32=true := j445_8 704 16 16 ck445_8_704m16 ck445_8_720m16
theorem ck445_8_736m32 : scan445_8 736 32=true := j445_8 736 16 16 ck445_8_736m16 ck445_8_752m16
theorem ck445_8_768m32 : scan445_8 768 32=true := j445_8 768 16 16 ck445_8_768m16 ck445_8_784m16
theorem ck445_8_800m32 : scan445_8 800 32=true := j445_8 800 16 16 ck445_8_800m16 ck445_8_816m16
theorem ck445_8_832m32 : scan445_8 832 32=true := j445_8 832 16 16 ck445_8_832m16 ck445_8_848m16
theorem ck445_8_864m32 : scan445_8 864 32=true := j445_8 864 16 16 ck445_8_864m16 ck445_8_880m16
theorem ck445_8_896m32 : scan445_8 896 32=true := j445_8 896 16 16 ck445_8_896m16 ck445_8_912m16
theorem ck445_8_928m32 : scan445_8 928 32=true := j445_8 928 16 16 ck445_8_928m16 ck445_8_944m16
theorem ck445_8_960m32 : scan445_8 960 32=true := j445_8 960 16 16 ck445_8_960m16 ck445_8_976m16
theorem ck445_8_992m32 : scan445_8 992 32=true := j445_8 992 16 16 ck445_8_992m16 ck445_8_1008m16
theorem ck445_8_1024m32 : scan445_8 1024 32=true := j445_8 1024 16 16 ck445_8_1024m16 ck445_8_1040m16
theorem ck445_8_1056m32 : scan445_8 1056 32=true := j445_8 1056 16 16 ck445_8_1056m16 ck445_8_1072m16
theorem ck445_8_1088m32 : scan445_8 1088 32=true := j445_8 1088 16 16 ck445_8_1088m16 ck445_8_1104m16
theorem ck445_8_0m64 : scan445_8 0 64=true := j445_8 0 32 32 ck445_8_0m32 ck445_8_32m32
theorem ck445_8_64m64 : scan445_8 64 64=true := j445_8 64 32 32 ck445_8_64m32 ck445_8_96m32
theorem ck445_8_128m64 : scan445_8 128 64=true := j445_8 128 32 32 ck445_8_128m32 ck445_8_160m32
theorem ck445_8_192m64 : scan445_8 192 64=true := j445_8 192 32 32 ck445_8_192m32 ck445_8_224m32
theorem ck445_8_256m64 : scan445_8 256 64=true := j445_8 256 32 32 ck445_8_256m32 ck445_8_288m32
theorem ck445_8_320m64 : scan445_8 320 64=true := j445_8 320 32 32 ck445_8_320m32 ck445_8_352m32
theorem ck445_8_384m64 : scan445_8 384 64=true := j445_8 384 32 32 ck445_8_384m32 ck445_8_416m32
theorem ck445_8_448m64 : scan445_8 448 64=true := j445_8 448 32 32 ck445_8_448m32 ck445_8_480m32
theorem ck445_8_512m64 : scan445_8 512 64=true := j445_8 512 32 32 ck445_8_512m32 ck445_8_544m32
theorem ck445_8_576m64 : scan445_8 576 64=true := j445_8 576 32 32 ck445_8_576m32 ck445_8_608m32
theorem ck445_8_640m64 : scan445_8 640 64=true := j445_8 640 32 32 ck445_8_640m32 ck445_8_672m32
theorem ck445_8_704m64 : scan445_8 704 64=true := j445_8 704 32 32 ck445_8_704m32 ck445_8_736m32
theorem ck445_8_768m64 : scan445_8 768 64=true := j445_8 768 32 32 ck445_8_768m32 ck445_8_800m32
theorem ck445_8_832m64 : scan445_8 832 64=true := j445_8 832 32 32 ck445_8_832m32 ck445_8_864m32
theorem ck445_8_896m64 : scan445_8 896 64=true := j445_8 896 32 32 ck445_8_896m32 ck445_8_928m32
theorem ck445_8_960m64 : scan445_8 960 64=true := j445_8 960 32 32 ck445_8_960m32 ck445_8_992m32
theorem ck445_8_1024m64 : scan445_8 1024 64=true := j445_8 1024 32 32 ck445_8_1024m32 ck445_8_1056m32
theorem ck445_8_1088m36 : scan445_8 1088 36=true := j445_8 1088 32 4 ck445_8_1088m32 ck445_8_1120
theorem ck445_8_0m128 : scan445_8 0 128=true := j445_8 0 64 64 ck445_8_0m64 ck445_8_64m64
theorem ck445_8_128m128 : scan445_8 128 128=true := j445_8 128 64 64 ck445_8_128m64 ck445_8_192m64
theorem ck445_8_256m128 : scan445_8 256 128=true := j445_8 256 64 64 ck445_8_256m64 ck445_8_320m64
theorem ck445_8_384m128 : scan445_8 384 128=true := j445_8 384 64 64 ck445_8_384m64 ck445_8_448m64
theorem ck445_8_512m128 : scan445_8 512 128=true := j445_8 512 64 64 ck445_8_512m64 ck445_8_576m64
theorem ck445_8_640m128 : scan445_8 640 128=true := j445_8 640 64 64 ck445_8_640m64 ck445_8_704m64
theorem ck445_8_768m128 : scan445_8 768 128=true := j445_8 768 64 64 ck445_8_768m64 ck445_8_832m64
theorem ck445_8_896m128 : scan445_8 896 128=true := j445_8 896 64 64 ck445_8_896m64 ck445_8_960m64
theorem ck445_8_1024m100 : scan445_8 1024 100=true := j445_8 1024 64 36 ck445_8_1024m64 ck445_8_1088m36
theorem ck445_8_0m256 : scan445_8 0 256=true := j445_8 0 128 128 ck445_8_0m128 ck445_8_128m128
theorem ck445_8_256m256 : scan445_8 256 256=true := j445_8 256 128 128 ck445_8_256m128 ck445_8_384m128
theorem ck445_8_512m256 : scan445_8 512 256=true := j445_8 512 128 128 ck445_8_512m128 ck445_8_640m128
theorem ck445_8_768m256 : scan445_8 768 256=true := j445_8 768 128 128 ck445_8_768m128 ck445_8_896m128
theorem ck445_8_0m512 : scan445_8 0 512=true := j445_8 0 256 256 ck445_8_0m256 ck445_8_256m256
theorem ck445_8_512m512 : scan445_8 512 512=true := j445_8 512 256 256 ck445_8_512m256 ck445_8_768m256
theorem ck445_8_0m1024 : scan445_8 0 1024=true := j445_8 0 512 512 ck445_8_0m512 ck445_8_512m512
theorem ck445_8_0m1124 : scan445_8 0 1124=true := j445_8 0 1024 100 ck445_8_0m1024 ck445_8_1024m100
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sv445_8 : caseLevel (graphGoal 445) sgBase445 8 3 sl445_8 :=
  caseLevel_ok sgPairs445 (decorateSigned_ok 445 _ _) scert445 sv445_7 (by decide +kernel) ck445_8_0m1124

def sl445_9b0 : Array CaseCode := #[(36403,503,[(8,0),(4,1),(16,3),(3,3),(22,3),(16,1),(5,1),(3,1),(22,1),(3,2),(16,2)],[0,1,2,3,4,5,6,7,8,9,10,11,12]),
(69171,503,[(8,0),(11,1),(16,3),(3,3),(22,3),(16,1),(12,1),(3,1),(4,1),(22,1),(6,0),(16,2)],[13,14,15,16,17,18,19,20,21,22,23,24]),
(542259,509,[(16,1),(8,2),(16,0),(3,3),(22,3),(3,2),(22,2)],[4,17,25,26,27,28,29,30]),
(296499,511,[(8,2),(16,1),(8,0),(0,0),(3,3),(4,1),(19,1),(22,3),(3,1),(11,1),(22,1)],[18,31,32,33,34,35]),
(378419,383,[(16,1),(8,0),(0,0),(16,0),(3,3),(3,0),(5,0),(4,0),(11,0),(22,0)],[36,37]),
(329267,511,[(16,1),(8,2),(8,0),(0,0),(3,3),(5,1),(11,1),(21,1),(22,3),(3,1),(4,1),(22,1)],[34,38,39,40,41,42]),
(362035,511,[(8,2),(16,1),(8,0),(22,1),(3,3),(5,1),(23,1),(3,1),(4,1),(0,0),(11,1)],[19,32,35,39,42,43,44,45]),
(559667,511,[(8,2),(4,1),(8,0),(16,3),(16,1),(3,3),(6,0),(22,3),(3,1),(4,0),(11,1),(22,1)],[46,47]),
(559667,507,[(8,2),(16,3),(16,2),(3,3),(22,3),(16,1),(4,0),(3,2),(5,0),(22,2)],[20,25,48,49,50,51,52,53,54]),
(379443,383,[(8,0),(4,1),(16,0),(3,0),(0,0),(4,0),(11,0),(2,0),(22,0)],[26,47,55,56,57,58,59]),
(68147,511,[(8,2),(4,1),(8,0),(16,3),(16,1),(3,3),(11,1),(22,3),(3,1),(22,1),(25,0)],[60,61,62]),
(330291,511,[(8,2),(8,0),(16,3),(16,1),(22,1),(3,3),(4,1),(11,1),(22,3),(3,1)],[21,34,40,55,63,64,65,66,67,68,69,70,71,72]),
(346675,511,[(16,1),(8,2),(8,0),(2,0),(3,3),(4,1),(12,1),(19,1),(22,3),(3,1),(11,1),(22,1)],[65,70,73,74,75,76]),
(363059,511,[(8,2),(22,1),(8,0),(16,3),(16,1),(3,3),(4,1),(23,1),(3,1),(11,1),(25,0)],[22,35,44,56,66,72,76,77,78]),
(335411,383,[(8,0),(11,1),(3,0),(16,0),(0,0),(4,0),(11,0),(2,0),(22,0)],[5,27,49,55,67,79,80,81,82]),
(351795,383,[(16,1),(8,0),(2,0),(16,0),(3,0),(4,0),(12,0),(11,0),(22,0)],[50,83])]
def sl445_9b16 : Array CaseCode := #[(368179,383,[(22,1),(8,0),(22,0),(16,0),(3,3),(3,0),(0,0),(4,0),(11,0),(2,0)],[28,51,56,78,80,84,85,86]),
(594483,511,[(8,2),(11,1),(8,0),(16,1),(16,3),(3,1),(4,1),(11,0),(22,1),(3,3),(22,3)],[6,79,87]),
(594483,495,[(8,2),(16,3),(16,2),(16,1),(11,0),(3,3),(22,3),(3,2),(12,0),(22,2)],[7,29,36,52,57,84,88,89,90]),
(348723,511,[(8,2),(16,1),(8,0),(3,3),(11,1),(21,1),(22,3),(3,1),(4,1),(2,0),(22,1)],[8,70,91,92,93,94]),
(365107,511,[(8,2),(8,0),(16,3),(22,1),(16,1),(3,3),(11,1),(26,1),(3,1),(4,1)],[9,42,68,72,80,94,95,96,97]),
(611891,479,[(16,1),(8,2),(16,0),(3,3),(22,3),(3,2),(22,2)],[10,23,53,58,81,85,89,98]),
(366131,511,[(8,2),(16,1),(22,1),(8,0),(3,3),(12,1),(27,1),(3,1),(4,1),(2,0),(11,1)],[11,74,76,86,92,94,96,99,100]),
(629299,447,[(8,2),(22,1),(16,3),(16,2),(16,1),(22,0),(3,3),(3,2)],[12,24,30,37,54,59,82,83,90,98]),
(524851,502,[(16,3),(3,1),(8,0),(22,3),(16,1),(16,2)],[101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117]),
(279091,503,[(16,1),(3,1),(8,0),(22,3),(0,1),(5,1),(4,1),(17,1),(11,1),(22,1),(16,0),(14,0)],[118,119,120,121,122,123,124,125,126,127,128,129]),
(295475,503,[(16,3),(3,1),(8,0),(7,0),(22,3),(16,1),(4,1),(10,0),(11,1),(22,1),(16,2),(14,0)],[118,121,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150]),
(328243,503,[(16,3),(3,1),(8,0),(22,3),(26,1),(7,0),(16,1),(11,1),(4,1),(16,2),(22,1)],[122,142,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169]),
(344627,503,[(16,1),(3,1),(8,0),(22,3),(2,1),(12,1),(17,1),(4,1),(16,0),(11,1),(22,1)],[130,143,151,165,170,171,172,173,174,175,176,177,178,179,180]),
(361011,503,[(16,3),(3,1),(8,0),(22,1),(26,1),(7,0),(16,1),(4,1),(16,2),(11,1)],[123,131,144,152,166,179,181,182,183,184,185,186,187,188,189,190,191,192,193]),
(542259,501,[(16,1),(3,3),(22,3),(8,2),(16,0)],[101,132,153,181,194,195,196,197,198,199,200,201,202,203,204,205]),
(296499,503,[(16,1),(3,3),(0,1),(22,3),(8,2),(4,1),(3,1),(23,1),(8,0),(19,1),(11,1),(22,1),(16,0)],[102,121,133,154,182,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220])]
def sl445_9b32 : Array CaseCode := #[(378419,503,[(16,1),(8,0),(3,3),(22,3),(5,1),(0,1),(3,1),(4,1),(9,0),(11,1),(22,1)],[206,212,221,222,223,224,225,226,227,228,229,230,231,232]),
(329267,503,[(16,1),(3,3),(0,1),(22,3),(8,2),(5,1),(11,1),(3,1),(4,1),(16,0),(8,0),(22,1)],[103,119,122,134,155,183,213,221,227,233,234,235,236,237,238,239,240,241,242,243,244,245]),
(362035,503,[(16,1),(22,1),(3,3),(0,1),(8,2),(5,1),(3,1),(4,1),(16,0),(8,0),(23,1),(11,1)],[104,123,135,156,184,207,214,228,233,244,246,247,248,249,250,251,252,253]),
(559667,503,[(4,1),(16,3),(3,3),(8,2),(22,3),(5,1),(6,0),(16,1),(3,1),(8,0),(11,1),(22,1),(16,2)],[105,136,157,170,185,194,208,254,255,256,257,258,259,260,261,262,263,264]),
(559667,499,[(16,3),(4,1),(3,3),(8,2),(22,3),(16,1),(16,2)],[106,124,158,171,186,195,222,234,246,265,266,267,268,269,270,271,272,273,274,275]),
(379443,503,[(8,0),(16,3),(3,3),(1,0),(22,3),(16,1),(4,1),(3,1),(25,0),(10,0),(11,1),(22,1)],[46,196,209,212,223,235,247,254,276,277,278,279,280,281,282,283,284,285,286,287,288]),
(68147,503,[(16,3),(4,1),(11,1),(3,3),(8,2),(22,3),(5,1),(12,1),(16,1),(3,1),(26,1),(8,0),(22,1),(16,2),(6,0)],[107,197,289,290,291,292,293,294,295]),
(330291,503,[(16,3),(3,3),(8,2),(22,3),(4,1),(16,1),(11,1),(22,1),(3,1),(16,2),(8,0)],[108,125,137,138,142,159,172,187,198,210,213,224,236,237,248,255,276,279,296,297,298,299,300,301,302,303,304,305,306,307,308,309,310,311,312,313,314,315,316,317,318,319,320]),
(346675,503,[(16,1),(3,3),(2,1),(22,3),(8,2),(4,1),(12,1),(3,1),(16,0),(8,0),(11,1),(22,1)],[109,139,143,160,173,188,256,277,280,298,299,314,321,322,323,324,325,326,327,328,329,330]),
(363059,503,[(16,3),(22,1),(3,3),(8,2),(23,1),(16,1),(4,1),(25,0),(3,1),(16,2),(8,0),(11,1)],[110,126,140,144,161,174,199,214,225,238,249,257,281,300,301,317,321,329,331,332,333,334,335,336,337,338,339,340,341]),
(335411,503,[(8,0),(16,3),(3,3),(1,0),(22,3),(3,1),(16,1),(6,0),(11,1),(4,1),(22,1)],[87,200,215,226,227,239,250,266,279,302,303,322,332,342,343,344,345,346,347,348,349,350,351]),
(351795,503,[(16,1),(8,0),(3,3),(22,3),(12,1),(2,1),(6,0),(3,1),(4,1),(11,1),(22,1)],[267,280,305,323,333,342,347,352,353,354,355]),
(368179,503,[(22,1),(16,3),(8,0),(3,3),(1,0),(6,0),(16,1),(3,1),(4,1),(24,0),(11,1)],[201,216,228,240,268,278,281,306,324,334,343,348,354,356,357,358,359,360]),
(594483,503,[(11,1),(16,3),(3,3),(8,2),(22,3),(12,1),(16,1),(14,0),(3,1),(4,1),(8,0),(22,1),(26,1),(16,2)],[111,162,202,217,229,241,251,258,269,282,307,335,344,356,361,362,363,364]),
(594483,487,[(16,3),(11,1),(3,3),(8,2),(22,3),(16,1),(16,2)],[112,127,145,175,189,203,218,230,252,259,270,283,325,336,352,357,365,366,367,368]),
(348723,503,[(16,1),(3,3),(2,1),(22,3),(8,2),(11,1),(3,1),(21,1),(4,1),(16,0),(8,0),(28,1),(22,1)],[113,146,163,165,176,190,260,271,284,308,314,337,345,347,358,361,369,370,371,372])]
def sl445_9b48 : Array CaseCode := #[(365107,503,[(16,3),(22,1),(3,3),(8,2),(26,1),(16,1),(11,1),(28,1),(3,1),(4,1),(16,2),(8,0)],[114,128,147,166,177,191,204,219,231,242,244,261,272,285,309,310,317,326,346,348,353,362,371,373,374,375,376,377,378]),
(611891,471,[(16,1),(3,3),(22,3),(8,2),(16,0)],[115,148,167,192,262,273,286,294,318,339,349,359,363,366,376,379]),
(366131,503,[(16,1),(22,1),(3,3),(2,1),(8,2),(12,1),(3,1),(27,1),(4,1),(16,0),(8,0),(11,1)],[116,149,168,179,263,274,287,319,327,329,350,354,360,367,369,371,377,380]),
(629299,439,[(16,3),(22,1),(3,3),(8,2),(16,1),(16,2)],[117,129,150,169,180,205,220,232,245,264,275,288,295,320,330,351,355,364,368,372,379]),
(344323,510,[(8,0),(16,1),(16,0),(17,0),(11,1)],[381,382,383,384,385,386,387]),
(360707,510,[(8,0),(22,1),(22,0),(26,0),(11,1)],[386,388,389,390,391,392,393,394]),
(541955,509,[(8,2),(16,1),(3,2),(16,0),(4,2),(11,2),(22,2)],[388,395,396,397]),
(296195,511,[(8,2),(16,0),(19,0),(8,0)],[]),
(328963,511,[(8,2),(3,0),(16,0),(21,0),(8,0),(16,1)],[]),
(361731,511,[(8,2),(23,0),(8,0)],[389]),
(559363,511,[(8,2),(8,0),(4,0)],[398]),
(559363,507,[(8,2),(3,2),(16,2),(16,1),(11,2),(22,2)],[381,390,395,399,400,401,402]),
(67843,511,[(8,0),(8,2),(4,0)],[]),
(329987,511,[(8,2),(3,0),(11,0),(8,0),(22,1)],[403]),
(346371,511,[(8,2),(16,0),(19,0),(8,0),(16,1)],[382]),
(362755,511,[(8,2),(22,0),(23,0),(8,0)],[])]
def sl445_9b64 : Array CaseCode := #[(594179,511,[(8,2),(11,1),(8,0),(3,2),(11,0)],[404,405]),
(594179,495,[(8,2),(3,2),(16,2),(16,1),(11,1),(4,2),(22,2)],[383,391,396,400,406,407,408,409]),
(348419,511,[(8,2),(3,0),(21,0),(8,0)],[384]),
(364803,511,[(8,2),(3,0),(26,0),(8,0)],[392]),
(611587,479,[(8,2),(16,1),(3,2),(16,0),(4,2),(11,2),(22,2)],[393,401,408,410]),
(365827,511,[(8,2),(22,0),(27,0),(8,0)],[386]),
(628995,447,[(8,2),(3,2),(16,2),(16,1),(22,1),(22,0),(4,2),(11,2)],[387,397,402,409,410]),
(559379,507,[(8,2),(16,2),(5,0),(3,3),(16,0),(3,2),(11,2),(22,2)],[411,412]),
(330003,511,[(8,0),(8,2),(11,0),(22,1)],[413]),
(362771,511,[(8,2),(22,0),(23,0),(8,0)],[]),
(594195,511,[(8,2),(8,0),(11,0)],[414,415]),
(594195,495,[(8,2),(16,2),(16,0),(3,3),(3,2),(4,2),(22,2)],[411,416,417,418]),
(364819,511,[(8,2),(26,0),(8,0)],[]),
(629011,447,[(8,2),(16,2),(16,0),(22,1),(22,0),(3,3),(3,2),(4,2),(11,2)],[412,418]),
(269347,383,[(3,1),(8,0),(3,0),(16,0),(5,0),(0,0),(11,0),(2,0),(22,0),(4,0)],[419,420,421,422,423,424,425,426,427]),
(285731,383,[(16,1),(0,0),(16,0),(4,0),(8,2),(3,3),(3,0),(11,0),(22,0),(23,0)],[0,428,429,430])]
def sl445_9b80 : Array CaseCode := #[(334883,383,[(4,0),(8,0),(16,0),(22,0),(8,2),(3,0),(5,0),(0,0),(2,0)],[1,422,431,432,433,434,435,436,437,438,439,440,441,442]),
(351267,383,[(16,1),(2,0),(16,0),(12,0),(8,2),(3,0),(4,0),(11,0),(22,0)],[2,443,444]),
(367651,383,[(22,1),(4,0),(22,0),(23,0),(16,0),(8,2),(3,3),(3,0),(5,0),(0,0),(11,0),(2,0)],[3,423,440,445,446,447,448]),
(68643,511,[(4,0),(8,0)],[431,432,449]),
(330787,503,[(8,0),(4,2),(12,0),(3,1)],[428,445,450,451,452,453]),
(524323,510,[(8,0),(4,2),(3,1),(16,2),(3,0),(22,2),(16,1)],[429,433,443,446,454,455,456,457]),
(294947,507,[(3,1),(8,0),(4,0),(3,0),(5,0)],[434,458,459,460,461,462,463,464]),
(327715,511,[(4,0),(8,0)],[422,465]),
(344099,511,[(2,0),(4,0),(8,0)],[419,458,466]),
(360483,511,[(22,0),(4,0),(8,0)],[420,423,459,467]),
(541731,509,[(4,2),(16,1),(16,0),(23,0),(3,2),(22,2),(3,3),(8,2)],[4,424,435,450,454,460,468]),
(593955,511,[(4,0),(11,0),(4,2)],[6,436,451,469]),
(593955,495,[(4,2),(16,2),(16,1),(11,0),(3,2),(12,0),(22,2),(3,3),(8,2)],[7,425,430,447,455,462,468,470,471,472]),
(348195,511,[(4,0),(2,0)],[8]),
(364579,511,[(4,0)],[9,437,440]),
(611363,479,[(16,1),(4,2),(16,0),(3,2),(22,2),(3,3),(8,2)],[10,426,441,448,452,456,463,471,473])]
def sl445_9b96 : Array CaseCode := #[(365603,511,[(2,0),(22,0),(4,0)],[11]),
(628771,447,[(4,2),(16,2),(23,0),(16,1),(22,1),(22,0),(3,2),(3,3),(8,2)],[12,427,442,444,453,457,464,472,473]),
(541987,509,[(8,2),(16,1),(16,0),(4,2),(3,2),(11,2),(22,2)],[474,475,476]),
(296227,511,[(16,0),(8,2),(19,0),(16,1)],[]),
(328995,511,[(8,2),(16,0),(21,0),(8,0),(16,1)],[]),
(361763,511,[(8,0),(8,2),(4,0),(23,0)],[]),
(559395,507,[(8,2),(16,2),(16,1),(4,0),(3,2),(11,2),(22,2)],[474,477,478,479]),
(330019,511,[(11,0),(8,2),(8,0),(22,1)],[480]),
(346403,511,[(16,1),(16,0),(8,2),(19,0)],[]),
(362787,511,[(22,0),(8,2),(23,0),(22,1)],[]),
(594211,511,[(8,2),(8,0),(11,0)],[481]),
(594211,495,[(8,2),(16,2),(16,1),(4,2),(3,2),(22,2)],[475,477,482,483,484]),
(348451,511,[(8,2),(21,0),(8,0)],[]),
(364835,511,[(8,2),(26,0),(8,0)],[]),
(611619,479,[(8,2),(16,1),(16,0),(4,2),(3,2),(11,2),(22,2)],[478,483,485]),
(365859,511,[(8,2),(22,0),(27,0),(8,0)],[])]
def sl445_9b112 : Array CaseCode := #[(629027,447,[(8,2),(22,1),(16,2),(16,1),(22,0),(4,2),(3,2),(11,2)],[476,479,484,485]),
(269379,383,[(3,1),(26,0),(8,0),(3,0),(16,0),(12,0),(0,0),(4,0),(2,0),(22,0),(11,0)],[486,487,488,489]),
(285763,383,[(16,1),(0,0),(16,0),(11,0),(5,0),(8,2),(3,0),(4,0),(22,0)],[13,490,491]),
(302147,383,[(8,0),(16,0),(11,0),(8,2),(3,0),(16,3),(0,0),(12,0),(4,0),(2,0),(22,0)],[14,432,449,486,492,493,494,495,496,497,498,499,500]),
(351299,383,[(16,1),(2,0),(16,0),(11,0),(8,2),(3,0),(4,0),(22,0),(28,0)],[15,501,502]),
(367683,383,[(22,1),(26,0),(11,0),(22,0),(16,0),(8,2),(3,0),(0,0),(4,0),(28,0),(12,0),(2,0)],[16,498,503,504,505]),
(524355,510,[(8,0),(11,2),(3,1),(16,2),(26,0),(3,0),(4,2),(22,2),(16,1)],[490,492,501,506,507,508,509]),
(278595,511,[(0,0),(11,0),(8,0)],[]),
(294979,511,[(3,0),(11,0),(8,0)],[486,493,510,511,512]),
(327747,495,[(8,0),(26,0),(11,0),(3,0),(3,1),(12,0)],[512,513,514,515]),
(541763,509,[(16,1),(11,2),(16,0),(3,2),(4,2),(22,2),(8,2)],[17,487,494,503,506,513,516,517,518]),
(296003,511,[(11,0),(0,0)],[18]),
(361539,511,[(0,0),(11,0)],[19]),
(559171,511,[(11,0),(4,0),(6,0)],[495,519]),
(559171,507,[(11,2),(16,2),(4,0),(3,2),(5,0),(22,2),(8,2),(16,1)],[20,488,502,504,507,514,516,520,521]),
(329795,495,[(11,0),(5,0),(4,0),(8,2),(8,0),(12,0)],[21,505,508,511,512,517,519,522,523,524,525,526])]
def sl445_9b128 : Array CaseCode := #[(362563,511,[(11,0)],[22,496,498,522]),
(611395,479,[(16,1),(11,2),(16,0),(28,0),(3,2),(4,2),(22,2),(8,2)],[23,489,499,509,515,520,525]),
(628803,447,[(11,2),(26,0),(16,2),(28,0),(16,1),(22,1),(22,0),(3,2),(4,2),(8,2)],[24,491,500,518,521,526]),
(542019,509,[(8,2),(16,1),(16,0),(22,2),(11,2),(3,2),(4,2)],[450,527,528,529]),
(296259,511,[(8,2),(16,0),(19,0),(8,0),(22,2)],[530]),
(329027,511,[(16,0),(16,1),(8,2),(21,0),(22,2)],[]),
(361795,511,[(8,0),(8,2),(22,0),(23,0)],[]),
(559427,511,[(8,2),(8,0),(4,1),(4,0),(22,2)],[531]),
(559427,507,[(8,2),(16,2),(22,2),(11,2),(16,1),(3,2)],[527,532,533,534,535]),
(330051,511,[(4,0),(8,2),(8,0),(22,2),(22,1)],[536]),
(346435,511,[(8,2),(16,1),(16,0),(19,0),(8,0),(22,2)],[537]),
(362819,511,[(8,2),(22,0),(23,0),(8,0)],[538]),
(594243,495,[(8,2),(16,2),(22,2),(16,1),(11,0),(3,2),(4,2)],[451,528,533,539,540]),
(348483,511,[(16,0),(8,2),(21,0),(16,1),(22,2)],[]),
(364867,511,[(22,0),(8,2),(26,0),(22,1)],[]),
(611651,479,[(8,2),(16,1),(16,0),(22,2),(11,2),(3,2),(4,2)],[452,534,539,541])]
def sl445_9b144 : Array CaseCode := #[(365891,511,[(8,0),(8,2),(22,0),(27,0)],[]),
(629059,447,[(8,2),(22,1),(16,2),(16,1),(22,0),(11,2),(3,2),(4,2)],[453,529,535,540,541,542]),
(559443,511,[(8,2),(8,0),(16,2),(4,0)],[543]),
(559443,507,[(16,2),(8,2),(16,0),(3,2),(11,2),(22,2)],[544,545,546]),
(330067,511,[(8,2),(16,2),(11,0),(8,0),(22,1)],[547]),
(362835,511,[(8,2),(16,2),(22,0),(23,0),(8,0)],[]),
(594259,495,[(16,2),(8,2),(12,0),(16,0),(3,2),(4,2),(22,2)],[545,548]),
(364883,511,[(8,2),(16,2),(26,0),(8,0)],[]),
(629075,447,[(16,2),(8,2),(16,0),(22,1),(22,0),(3,2),(4,2),(11,2)],[546,548]),
(542051,509,[(8,2),(16,1),(22,2),(16,0),(3,3),(3,2),(4,2),(11,2)],[549,550]),
(296291,511,[(8,2),(16,0),(19,0),(8,0)],[]),
(329059,511,[(8,2),(16,0),(11,0),(16,1),(21,0),(8,0)],[]),
(559459,511,[(8,2),(8,0),(4,0)],[551,552]),
(559459,507,[(8,2),(22,2),(16,2),(3,3),(16,1),(3,2),(11,2)],[549,553,554,555,556]),
(67939,511,[(8,0),(8,2),(4,0)],[]),
(330083,511,[(8,0),(8,2),(11,0),(22,0)],[557])]
def sl445_9b160 : Array CaseCode := #[(346467,511,[(8,2),(16,1),(16,0),(19,0),(8,0)],[]),
(594275,511,[(8,2),(8,0),(11,0)],[558,559]),
(594275,495,[(8,2),(22,2),(16,2),(16,1),(3,3),(3,2),(4,2)],[550,555,560,561,562]),
(348515,511,[(8,2),(21,0),(8,0)],[]),
(611683,479,[(8,2),(16,1),(22,2),(16,0),(3,3),(3,2),(4,2),(11,2)],[556,562]),
(542208,508,[(16,1),(3,2),(8,2),(22,3),(16,0)],[101,454,506,563,564,565,566,567,568,569,570,571]),
(296448,510,[(16,1),(8,0),(16,0),(3,2),(3,0),(11,1),(22,1)],[102,572,573,574,575,576,577,578,579]),
(329216,510,[(16,1),(8,0),(16,0),(3,2),(3,0),(4,1),(22,1)],[103,576,580,581,582,583,584,585,586,587]),
(361984,510,[(16,1),(3,2),(22,1),(8,0),(16,0),(3,0),(4,1),(11,1)],[104,573,577,581,586,588,589,590,591,592]),
(559616,510,[(4,1),(3,2),(16,1),(16,3),(8,0),(8,2),(3,0),(11,1),(22,1),(16,2),(22,3)],[105,563,574,593,594,595,596,597,598,599]),
(559616,506,[(16,3),(3,2),(8,2),(22,3),(4,1),(16,1),(16,2)],[106,507,564,582,589,600,601,602,603,604,605,606,607,608]),
(68096,510,[(4,1),(16,1),(26,0),(11,1),(8,0),(16,2),(3,2),(3,0),(22,1)],[107,565,609,610,611]),
(330240,510,[(3,2),(16,1),(22,1),(8,0),(16,2),(3,0),(11,1),(4,1)],[108,508,566,576,583,594,612,613,614,615,616,617,618,619,620,621,622]),
(346624,510,[(16,1),(8,0),(16,0),(3,2),(3,0),(11,1),(22,1)],[109,595,613,618,623,624,625,626,627,628]),
(363008,510,[(22,1),(16,1),(8,0),(16,2),(3,2),(3,0),(11,1)],[110,567,577,590,596,614,620,627,629,630,631,632]),
(594432,510,[(11,1),(3,2),(16,1),(16,3),(26,0),(8,0),(3,0),(4,1),(22,1),(8,2),(16,2),(22,3)],[111,568,584,602,615,633,634,635])]
def sl445_9b176 : Array CaseCode := #[(594432,494,[(16,3),(3,2),(8,2),(11,1),(22,3),(16,1),(16,2)],[112,455,569,578,591,597,603,624,630,636,637,638,639,640]),
(348672,510,[(16,1),(8,0),(16,0),(3,2),(3,0),(4,1),(22,1)],[113,604,618,634,641,642,643,644,645]),
(365056,510,[(26,0),(22,1),(3,2),(16,1),(8,0),(16,2),(3,0),(4,1)],[114,570,586,605,616,620,644,646,647]),
(611840,478,[(16,1),(3,2),(8,2),(22,3),(16,0)],[115,456,509,598,606,611,621,631,635,638,646,648]),
(366080,510,[(16,1),(22,1),(8,0),(16,0),(3,2),(3,0),(4,1),(11,1)],[116,607,625,627,639,642,644,647,649,650]),
(629248,446,[(16,3),(3,2),(22,1),(8,2),(26,0),(16,1),(16,2)],[117,457,571,579,587,599,608,622,628,640,645,648]),
(118032,383,[(16,2),(16,0),(8,0),(3,2),(17,0),(4,0),(11,0),(22,0),(5,0)],[651,652,653,654,655,656,657,658]),
(295184,510,[(16,2),(5,0),(16,0),(8,0),(4,0),(11,2)],[118,654,659,660,661,662,663]),
(328976,509,[(16,0),(0,0),(3,2),(5,0),(3,0),(8,2),(4,2),(11,0)],[119,655,664,665,666]),
(646416,383,[(16,2),(16,0),(5,0),(0,0),(17,0),(8,2),(8,0),(3,2),(4,0),(11,0),(22,0)],[120,667,668]),
(302352,383,[(16,2),(0,0),(8,2),(8,0),(3,2),(5,0),(11,0),(16,0),(22,0)],[121,669,670,671,672]),
(335120,383,[(16,2),(0,0),(16,0),(8,2),(8,0),(3,2),(5,0),(4,0),(22,0)],[122,673,674,675]),
(367888,383,[(0,0),(16,2),(5,0),(8,2),(8,0),(3,2),(4,0),(11,0),(16,0),(22,1)],[123,676,677]),
(559376,507,[(16,2),(5,0),(3,2),(8,2),(16,0),(4,0),(11,2),(22,2)],[124,656,678,679]),
(330000,511,[(5,0),(17,0),(0,0),(22,1)],[125,660]),
(362768,511,[(17,0),(0,0)],[126])]
def sl445_9b192 : Array CaseCode := #[(594192,511,[(11,0),(16,0),(17,0),(14,0)],[665,674]),
(594192,495,[(16,2),(16,0),(11,0),(8,2),(3,2),(4,2),(22,2)],[127,657,662,667,671,677,678,680,681]),
(364816,511,[(17,0),(0,0)],[128]),
(629008,447,[(16,2),(16,0),(22,1),(22,0),(8,2),(3,2),(4,2),(11,2)],[129,658,663,666,668,672,675,679,681]),
(118048,511,[(3,2),(8,0),(7,0),(3,0)],[]),
(118048,503,[(3,2),(16,3),(7,0),(22,3)],[659,682,683,684,685,686,687,688,689,690,691,692,693,694,695,696]),
(118048,383,[(8,0),(3,2),(3,0),(16,0),(16,3),(1,0),(0,0),(11,0),(2,0),(22,0),(22,3)],[510,697,698,699,700,701,702,703,704]),
(118048,375,[(3,2),(16,3),(22,3),(4,2)],[705,706,707,708,709,710,711,712,713,714,715,716,717,718,719,720,721,722,723,724,725,726]),
(344352,510,[(16,1),(16,0),(8,0),(17,0),(4,0),(11,1)],[130,458,683,727,728,729,730,731,732,733,734,735,736,737]),
(360736,510,[(22,1),(22,0),(8,0),(5,0),(26,0),(4,0),(11,1)],[131,459,684,736,738,739,740,741,742,743,744,745,746,747,748]),
(541984,509,[(16,1),(3,2),(16,0),(8,2),(11,2),(22,2)],[132,460,685,700,712,739,749,750,751,752,753,754,755]),
(296224,511,[(16,0),(3,0),(16,1)],[133,713]),
(378144,511,[(7,0),(16,1)],[686,756]),
(328992,511,[(5,0),(3,0),(16,0),(21,0),(0,0),(16,1)],[134,714,757]),
(361760,511,[(5,0),(4,0),(23,0),(0,0)],[135,715,740,758]),
(559392,507,[(3,2),(3,0),(4,0),(5,0),(16,2),(8,2),(16,1),(11,2),(22,2)],[136,687,701,716,728,741,749,759,760,761,762,763,764,765])]
def sl445_9b208 : Array CaseCode := #[(330016,511,[(3,0),(11,0),(3,2),(22,1)],[137,717]),
(330016,507,[(3,2),(3,0),(8,2),(11,0),(12,0)],[138,511,660,688,729,742,750,757,766,767,768,769,770,771,772,773,774,775]),
(346400,511,[(16,1),(16,0),(3,0)],[139,718,730]),
(362784,511,[(3,0),(22,0),(3,2)],[140,719]),
(646432,511,[(7,0),(8,0),(4,0),(3,0)],[689]),
(646432,383,[(3,2),(8,0),(16,0),(8,2),(16,1),(4,2),(0,0),(3,0),(11,0),(2,0),(22,0)],[141,461,661,731,743,751,767,776,777,778,779,780,781,782]),
(72992,511,[(3,0),(10,0)],[690,768,783]),
(335136,511,[(7,0),(22,1)],[691,783,784]),
(335136,383,[(3,2),(16,0),(22,0),(8,2),(8,0),(0,0),(2,0)],[142,512,732,744,752,760,785,786,787,788,789,790,791,792,793]),
(351520,511,[(16,1),(7,0)],[692,794]),
(351520,383,[(16,1),(2,0),(16,0),(12,0),(8,2),(8,0),(3,2),(11,0),(22,0)],[143,761,795,796,797]),
(367904,511,[(7,0),(22,1)],[693,798]),
(367904,383,[(22,1),(16,0),(8,2),(8,0),(3,2),(0,0),(11,0),(2,0)],[144,753,758,762,769,791,799,800,801,802,803,804]),
(594208,511,[(11,0),(11,1),(4,0),(14,0),(3,2)],[720,770,788,805]),
(594208,495,[(3,2),(16,2),(16,1),(11,1),(11,0),(8,2),(12,0),(22,2)],[145,462,662,671,694,702,721,733,745,754,763,780,802,806,807,808,809]),
(348448,511,[(3,0),(21,0),(2,0)],[146,722,734])]
def sl445_9b224 : Array CaseCode := #[(364832,511,[(3,0),(26,0)],[147,723,746,771,791]),
(611616,479,[(16,1),(3,2),(16,0),(8,2),(11,2),(22,2)],[148,463,695,703,724,747,764,774,781,792,803,808,810]),
(365856,511,[(22,0),(27,0),(2,0)],[149,725,736]),
(629024,447,[(3,2),(16,2),(16,1),(22,1),(22,0),(8,2),(11,2)],[150,464,663,672,696,704,726,737,755,765,775,782,793,797,809,810]),
(118080,383,[(8,0),(26,0),(3,2),(3,0),(16,0),(0,0),(4,0),(2,0),(22,0)],[465,811,812,813,814]),
(344384,510,[(12,0),(16,1),(16,0),(8,0),(11,0)],[151,732,815,816,817]),
(360768,510,[(26,0),(22,1),(22,0),(8,0),(11,0),(12,0)],[152,744,818,819,820,821]),
(542016,509,[(16,1),(3,2),(16,0),(8,2),(4,2),(22,2)],[153,513,752,812,818,822,823,824,825,826]),
(296256,511,[(26,0),(0,0)],[154]),
(329024,511,[(16,0),(16,1),(3,0)],[155]),
(378176,511,[(16,1),(7,0)],[]),
(361792,511,[(22,0),(26,0),(0,0)],[156,819]),
(559424,511,[(4,0),(26,0)],[157,760]),
(559424,507,[(3,2),(16,2),(8,2),(16,1),(4,0),(5,0),(22,2)],[158,514,813,815,820,822,827,828,829,830,831,832,833]),
(330048,511,[(3,0),(4,0),(3,2),(22,1)],[159]),
(379200,511,[(7,0),(26,0),(22,1)],[834])]
def sl445_9b240 : Array CaseCode := #[(346432,511,[(12,0),(16,1),(16,0),(26,0),(2,0)],[160]),
(362816,511,[(26,0)],[161,791]),
(594240,495,[(26,0),(3,2),(3,0),(12,0),(16,2),(16,1),(11,0),(8,2),(4,2),(22,2)],[162,674,788,823,828,835,836]),
(348480,511,[(16,0),(12,0),(3,0),(16,1)],[163]),
(646464,383,[(3,2),(26,0),(16,0),(16,1),(8,0),(11,2),(0,0),(4,0),(3,0),(2,0),(22,0),(8,2)],[164,816,824,829,837,838]),
(351552,511,[(7,0),(16,1)],[]),
(351552,383,[(16,1),(2,0),(8,2),(8,0),(3,2),(16,0),(4,0),(12,0),(22,0)],[165,830,839,840]),
(367936,383,[(26,0),(16,0),(8,2),(8,0),(3,2),(0,0),(4,0),(2,0),(22,1)],[166,791,825,831,841]),
(611648,479,[(16,1),(3,2),(16,0),(8,2),(4,2),(22,2)],[167,515,792,814,821,832,836,838,841,842]),
(365888,511,[(12,0),(26,0),(2,0)],[168]),
(629056,447,[(3,2),(26,0),(16,2),(16,1),(22,1),(22,0),(8,2),(4,2)],[169,675,793,817,826,833,840,842]),
(118096,383,[(16,2),(16,0),(8,0),(3,2),(17,0),(4,0),(11,0),(22,0)],[466,727,843,844,845,846,847,848,849]),
(559440,511,[(4,0),(3,0),(16,0),(17,0)],[170,728,761,850]),
(559440,507,[(16,2),(3,2),(8,2),(16,0),(4,0),(11,2),(22,2)],[171,381,815,830,846,851,852,853,854,855,856]),
(330064,511,[(12,0),(2,0),(11,0),(17,0),(22,1)],[172,729,732]),
(346448,479,[(16,0),(2,0),(3,2),(12,0),(3,0),(8,2),(4,0),(11,2)],[173,382,730,847,850,857,858])]
def sl445_9b256 : Array CaseCode := #[(362832,511,[(17,0),(2,0)],[174]),
(594256,495,[(16,2),(12,0),(3,2),(16,0),(11,0),(8,2),(4,2),(22,2)],[175,383,733,848,852,859]),
(348496,479,[(2,0),(16,0),(3,2),(3,0),(12,0),(8,2),(11,0)],[176,384,734,853,860,861]),
(364880,511,[(12,0),(17,0),(2,0)],[177]),
(646480,383,[(16,2),(16,0),(2,0),(12,0),(17,0),(8,0),(4,0),(11,0),(3,2),(22,0),(8,2)],[178,385,735,854,862]),
(367952,383,[(2,0),(16,2),(22,1),(12,0),(11,0),(8,2),(8,0),(3,2),(16,0),(4,0)],[179,386,736,855,863]),
(629072,447,[(16,2),(16,0),(22,1),(22,0),(8,2),(3,2),(4,2),(11,2)],[180,387,737,797,817,840,849,856,858,859,861,862]),
(118112,383,[(3,2),(8,0),(26,0),(22,2),(3,0),(16,0),(22,0),(0,0),(4,0),(11,0),(2,0)],[467,738,864,865,866,867]),
(542048,509,[(16,1),(22,2),(3,2),(16,0),(8,2),(4,2),(11,2)],[181,388,739,753,818,825,865,868,869,870,871]),
(296288,511,[(22,0),(26,0),(0,0)],[182,872]),
(329056,511,[(0,0),(11,0),(16,1),(26,0)],[183,873,874]),
(361824,447,[(16,1),(16,0),(3,2),(8,2),(3,0),(4,1),(11,2)],[184,389,740,758,819,872,873,874,875,876,877,878,879]),
(378208,511,[(7,0),(16,1)],[]),
(559456,511,[(4,0),(3,0),(4,1),(26,0),(22,2)],[185,741,762]),
(559456,507,[(3,2),(22,2),(16,2),(8,2),(16,1),(4,1),(4,0),(5,0),(11,2)],[186,390,820,831,855,866,868,876,880,881,882,883,884]),
(330080,511,[(22,0),(26,0)],[187,742,744,769,791,885])]
def sl445_9b272 : Array CaseCode := #[(346464,511,[(2,0),(16,1),(22,0),(26,0)],[188]),
(379232,511,[(7,0),(26,0)],[886]),
(594272,495,[(3,2),(22,2),(26,0),(16,2),(16,1),(11,0),(8,2),(4,2),(12,0)],[189,391,677,745,802,869,877,881,887]),
(348512,511,[(2,0),(26,0)],[190]),
(364896,447,[(26,0),(3,2),(3,0),(8,2),(4,1),(11,0),(12,0)],[191,392,746,870,874,882,885,888]),
(611680,479,[(16,1),(22,2),(3,2),(16,0),(8,2),(4,2),(11,2)],[192,393,747,803,821,841,867,883,887,888,889]),
(382304,511,[(7,0),(26,0),(16,1)],[]),
(646496,383,[(3,2),(26,0),(22,2),(16,0),(16,1),(8,0),(0,0),(4,0),(11,0),(2,0),(3,0),(8,2)],[193,394,748,871,878,884,889,890]),
(559633,509,[(16,2),(4,1),(16,0),(23,0),(8,1),(3,1),(11,1),(22,1),(3,3),(22,3)],[194,474,563,749,891,892,893]),
(559633,505,[(16,2),(3,3),(4,1),(22,3),(16,0)],[25,195,395,516,527,549,564,822,868,894,895,896,897,898,899]),
(68113,509,[(4,1),(16,2),(16,0),(23,0),(11,1),(8,1),(3,1),(22,1)],[197,565,900]),
(330257,509,[(16,2),(16,0),(22,1),(8,1),(3,1),(11,1),(4,1)],[198,517,566,750,752,892,901,902,903,904,905,906,907,908]),
(363025,509,[(16,2),(22,1),(23,0),(16,0),(8,1),(3,1),(11,1)],[199,567,753,902,907,909]),
(594449,509,[(16,2),(11,1),(16,0),(8,1),(3,1),(4,1),(22,1),(3,3),(22,3)],[202,528,568,823,896,903,910,911,912]),
(594449,493,[(16,2),(3,3),(11,1),(22,3),(16,0)],[29,203,396,468,475,550,569,754,869,893,897,909,913,914,915]),
(365073,509,[(16,2),(22,1),(16,0),(8,1),(3,1),(4,1)],[204,570,825,870,898,904,907,911,916,917])]
def sl445_9b288 : Array CaseCode := #[(629265,445,[(16,2),(22,1),(3,3),(23,0),(16,0)],[30,205,397,476,518,529,571,755,826,899,908,912,915]),
(118049,383,[(16,2),(19,0),(16,0),(23,0),(3,0),(11,0),(22,0),(8,1),(3,3)],[31,530,572,918,919,920]),
(361761,509,[(16,0),(0,0),(22,1),(22,0),(5,0),(23,0),(4,0)],[32,207,573,872,921]),
(559393,507,[(16,2),(5,0),(16,0),(19,0),(8,2),(4,0),(3,2),(11,2),(22,2),(23,0)],[208,574,922]),
(330017,511,[(16,0),(11,0),(16,2),(22,1)],[210]),
(646433,383,[(16,2),(16,0),(19,0),(0,0),(8,0),(3,0),(4,2),(11,0),(22,0),(23,0)],[33,211,575,923]),
(335137,383,[(16,2),(0,0),(16,0),(22,0),(8,0),(3,0),(5,0)],[34,213,576,924,925,926]),
(367905,383,[(0,0),(16,2),(23,0),(8,0),(3,0),(5,0),(11,0),(16,0),(22,1)],[35,214,577,927]),
(594209,511,[(11,0),(19,0)],[217,925]),
(594209,495,[(16,2),(16,0),(11,0),(8,2),(3,2),(22,2)],[218,578,671,920,921,922,923,927,928,929]),
(364833,511,[(26,0),(0,0)],[219]),
(629025,447,[(16,2),(23,0),(16,0),(22,1),(22,0),(8,2),(3,2),(11,2)],[220,579,672,926,929]),
(118081,383,[(16,2),(21,0),(16,0),(3,0),(4,0),(22,0),(8,1)],[38,580,664,930,931,932,933,934,935]),
(361793,509,[(16,0),(0,0),(22,1),(5,0),(22,0),(4,1),(11,0)],[39,233,581,873,936,937]),
(559425,507,[(16,2),(5,0),(8,2),(16,0),(4,1),(4,0),(3,2),(22,2)],[234,582,933,938,939]),
(330049,511,[(16,0),(16,2),(4,0),(22,1)],[236])]
def sl445_9b304 : Array CaseCode := #[(330049,495,[(16,2),(5,0),(16,0),(4,0)],[40,237,583,757,934,940,941,942,943]),
(362817,511,[(5,0),(16,0),(16,2),(23,0),(0,0)],[238,940]),
(594241,495,[(16,2),(16,0),(11,0),(21,0),(8,2),(3,2),(4,2),(22,2)],[241,584,665,674,925,937,938,944,945]),
(364865,511,[(16,0),(16,2),(22,0)],[242]),
(646465,383,[(16,2),(0,0),(16,0),(5,0),(21,0),(8,0),(3,0),(11,2),(4,0),(22,0)],[41,243,585,946,947]),
(367937,383,[(16,2),(0,0),(5,0),(22,1),(16,0),(8,0),(3,0),(4,0)],[42,244,586,874,944,948]),
(629057,447,[(16,2),(16,0),(22,1),(22,0),(8,2),(3,2),(4,2)],[245,587,666,675,926,935,939,943,945,947]),
(118113,383,[(16,2),(23,0),(16,0),(22,2),(3,0),(4,0),(11,0),(8,1)],[43,588,875,936,949,950,951]),
(559457,507,[(16,2),(5,0),(22,2),(23,0),(8,2),(16,0),(4,0),(3,2),(11,2)],[246,589,876,952]),
(330081,511,[(5,0),(0,0),(22,0),(23,0)],[248,953]),
(362849,447,[(16,2),(5,0),(16,0),(23,0),(4,0),(11,1)],[44,249,590,758,953,954]),
(594273,511,[(11,0),(16,0),(11,1),(23,0),(22,2)],[251,937,944]),
(594273,495,[(16,2),(16,0),(11,1),(11,0),(8,2),(3,2),(4,2),(22,2)],[252,591,677,877,921,927,951,952,954,955,956]),
(646497,383,[(16,2),(16,0),(0,0),(5,0),(23,0),(22,2),(8,0),(3,0),(4,0),(11,0)],[45,253,592,879,956]),
(118306,383,[(8,1),(8,0),(16,0),(4,0),(3,0),(0,0),(11,0),(2,0),(22,0),(5,0)],[46,551,593,759,891,957,958,959,960,961,962]),
(330274,507,[(4,0),(11,0),(5,0),(16,1),(22,1),(8,1),(16,2),(3,1)],[255,519,594,760,892,963,964,965,966,967,968,969,970,971])]
def sl445_9b320 : Array CaseCode := #[(346658,507,[(16,1),(16,0),(4,0),(19,0),(8,1),(3,1),(11,1),(22,1)],[256,595,761,850,967,972,973,974,975]),
(363042,507,[(22,1),(23,0),(4,0),(22,0),(5,0),(16,1),(8,1),(16,2),(3,1),(11,1)],[257,596,762,969,974,976,977]),
(594466,511,[(4,0),(4,2),(11,1),(11,0)],[258,964,978]),
(594466,495,[(4,2),(16,2),(16,3),(16,1),(11,1),(8,2),(3,2),(22,2),(3,3),(22,3)],[259,477,597,763,893,922,960,972,976,979,980,981]),
(348706,511,[(4,0),(21,0)],[260,967]),
(365090,511,[(4,0),(11,0),(26,0)],[261,965,969]),
(611874,479,[(16,1),(4,2),(16,0),(8,2),(3,2),(11,2),(22,2),(3,3),(22,3)],[262,478,598,764,961,970,977,980,982]),
(366114,511,[(4,0),(16,0),(4,2),(27,0),(22,1)],[263,973,974]),
(629282,447,[(4,2),(22,1),(16,2),(23,0),(16,3),(16,1),(22,0),(8,2),(3,2),(11,2),(3,3)],[264,479,599,765,962,971,975,981,982]),
(118306,507,[(4,0),(16,1),(5,0),(3,1),(11,1),(22,1),(8,1)],[47,48,553,600,894,983,984,985,986,987,988,989]),
(73250,507,[(11,1),(4,0),(16,1),(5,0),(8,1),(3,1),(22,1)],[265,601,895,990,991,992,993,994,995,996,997]),
(594466,507,[(11,1),(16,1),(16,3),(8,1),(4,0),(3,1),(22,1),(16,2),(4,2),(3,3),(22,3)],[269,533,602,828,896,938,966,998,999,1000,1001,1002]),
(594466,491,[(16,3),(4,2),(11,1),(3,3),(22,3),(16,1),(16,2)],[52,270,400,411,545,555,603,678,852,881,897,952,987,1003,1004,1005,1006,1007]),
(348706,507,[(16,1),(8,1),(16,0),(4,0),(3,1),(22,1)],[271,604,830,853,999,1008,1009,1010,1011,1012,1013]),
(365090,507,[(22,1),(16,1),(8,1),(16,2),(4,0),(3,1),(5,0)],[272,605,831,882,898,995,1000,1012,1014,1015,1016,1017,1018]),
(611874,475,[(16,1),(3,3),(4,2),(22,3),(16,0)],[53,273,401,520,534,556,606,832,883,988,996,1001,1005,1016,1019])]
def sl445_9b336 : Array CaseCode := #[(366114,507,[(16,1),(22,1),(8,1),(16,0),(4,2),(4,0),(3,1),(11,1)],[274,607,855,1006,1010,1012,1017,1020,1021,1022]),
(629282,443,[(16,3),(22,1),(3,3),(4,2),(16,1),(16,2)],[54,275,402,412,521,535,546,608,679,833,856,899,939,989,997,1002,1007,1013,1019]),
(376898,383,[(3,1),(26,0),(16,0),(3,0),(11,0),(8,1),(8,0),(5,0),(12,0),(0,0),(4,0),(2,0),(22,0)],[289,900,1023]),
(377922,383,[(16,1),(0,0),(16,0),(4,0),(19,0),(8,0),(3,0),(22,0),(11,0),(23,0)],[60,290,609]),
(351298,383,[(16,1),(2,0),(16,0),(11,0),(19,0),(8,0),(3,0),(4,0),(22,0),(28,0)],[62,292,610]),
(367682,383,[(22,1),(26,0),(16,0),(4,0),(11,0),(22,0),(25,0),(8,0),(3,0),(23,0),(5,0),(0,0),(28,0),(12,0),(2,0)],[293]),
(611394,479,[(16,1),(4,2),(16,0),(28,0),(11,2),(8,2),(3,2),(22,2)],[294,611,1023]),
(628802,447,[(4,2),(26,0),(23,0),(16,2),(28,0),(11,2),(16,1),(22,1),(22,0),(8,2),(3,2)],[295]),
(118082,511,[(11,0)],[63,1024,1025]),
(118082,383,[(16,0),(8,0),(3,0),(0,0),(11,0),(4,0),(2,0),(22,0),(8,1),(3,3)],[64,480,536,612,766,901,963,1026,1027,1028,1029,1030,1031]),
(380226,511,[(8,1),(22,1)],[1024,1032]),
(377154,511,[(3,1),(22,1)],[296,1033,1034]),
(378178,511,[(16,1),(22,1)],[297,1035]),
(346434,511,[(16,1),(16,0),(11,0),(22,2)],[298]),
(346434,507,[(16,1),(12,0),(16,0),(11,0)],[65,299,613,1036,1037,1038,1039]),
(362818,511,[(22,0),(4,0),(11,0),(22,1)],[300])]
def sl445_9b352 : Array CaseCode := #[(362818,507,[(22,1),(22,0),(23,0),(11,0),(12,0)],[66,301,522,614,769,902,940,953,1040,1041,1042,1043]),
(594242,495,[(11,0),(4,0),(16,2),(12,0),(22,2),(16,1),(4,2),(8,2),(3,2)],[307,615,770,788,903,925,964,979,1029,1040,1044,1045,1046,1047,1048]),
(348482,511,[(16,0),(4,0),(16,1),(22,2)],[308]),
(364866,511,[(22,0),(11,0),(4,0),(22,1)],[309]),
(364866,495,[(22,1),(22,0),(5,0),(26,0),(4,0)],[68,310,616,771,885,904,965,1036,1049,1050,1051,1052,1053]),
(646466,511,[(11,0),(4,0)],[311,1054,1055]),
(646466,383,[(16,0),(11,2),(4,2),(16,1),(8,0),(3,0),(0,0),(11,0),(4,0),(2,0),(22,0)],[69,312,523,617,772,905,941,966,979,1037,1041,1050,1056,1057,1058,1059,1060,1061,1062]),
(351554,511,[(16,1),(22,1)],[313,1063]),
(351554,383,[(2,0),(16,1),(16,0),(22,0),(8,0),(3,0),(12,0)],[70,314,618,967,1064,1065]),
(105794,447,[(22,1),(16,3),(3,3),(11,2),(4,2)],[71,315,524,619,773,906,942,968,1025,1032,1034,1035,1038,1045,1055,1063,1066]),
(367938,511,[(22,1)],[316]),
(367938,383,[(16,0),(8,0),(3,0),(0,0),(2,0),(22,1)],[72,317,620,791,907,969,1046,1067,1068,1069]),
(611650,479,[(16,1),(16,0),(22,2),(8,2),(3,2),(11,2),(4,2)],[318,525,621,774,792,970,1030,1042,1047,1051,1061,1066,1068,1070]),
(365890,511,[(12,0),(2,0),(22,0),(27,0)],[319,1052]),
(629058,447,[(22,1),(16,2),(16,1),(22,0),(8,2),(3,2),(11,2),(4,2)],[320,526,622,775,793,908,926,943,971,1031,1039,1048,1062,1065,1070,1071,1072]),
(118098,383,[(16,2),(19,0),(16,0),(3,0),(11,0),(22,0),(8,1),(3,3)],[73,537,623,857,1073,1074,1075,1076,1077])]
def sl445_9b368 : Array CaseCode := #[(362834,511,[(16,2),(16,0),(22,0)],[321]),
(594258,495,[(16,2),(12,0),(16,0),(11,1),(11,0),(8,2),(3,2),(22,2)],[325,624,972,1076,1078]),
(364882,511,[(16,2),(12,0),(16,0),(26,0),(2,0)],[326,1036]),
(365906,479,[(16,0),(22,1),(2,0),(12,0),(22,0),(4,0),(11,1)],[74,327,625,973,1079]),
(646482,383,[(16,2),(2,0),(16,0),(12,0),(19,0),(8,0),(3,0),(11,0),(4,2),(22,0)],[75,328,626,1080,1081]),
(367954,383,[(16,2),(22,1),(2,0),(16,0),(12,0),(8,0),(3,0),(11,0)],[76,329,627,974,1082]),
(629074,447,[(16,2),(16,0),(22,1),(22,0),(8,2),(3,2),(11,2)],[330,628,797,858,975,1039,1065,1077,1078,1081]),
(118114,383,[(23,0),(22,2),(16,0),(22,0),(3,0),(0,0),(11,0),(2,0),(8,1),(3,3)],[77,538,629,1083,1084,1085,1086]),
(380258,511,[(8,1),(23,0)],[]),
(377186,511,[(3,1)],[331,1087]),
(594274,511,[(11,0),(4,0),(23,0)],[335,1040,1046]),
(594274,495,[(22,2),(16,2),(16,1),(11,0),(8,2),(3,2),(12,0)],[336,630,802,909,927,954,976,1085,1088,1089,1090,1091]),
(348514,511,[(23,0),(2,0)],[337]),
(381282,511,[(23,0)],[338]),
(611682,479,[(16,1),(22,2),(16,0),(8,2),(3,2),(11,2)],[339,631,803,977,1042,1068,1086,1090,1092]),
(382306,511,[(16,1)],[340])]
def sl445_9b384 : Array CaseCode := #[(646498,383,[(22,2),(23,0),(16,0),(16,1),(8,0),(3,0),(0,0),(22,0),(11,0),(2,0),(4,2),(25,0)],[341,632,1043,1091,1092,1093]),
(56900,383,[(8,1),(8,0),(16,0),(11,0),(3,0),(0,0),(4,0),(2,0),(22,0),(12,0)],[87,404,414,469,558,633,835,910,998,1044,1094,1095,1096,1097,1098,1099,1100]),
(348740,495,[(16,1),(12,0),(16,0),(11,0),(21,0),(8,1),(3,1),(4,1),(22,1),(28,0)],[361,634,999]),
(365124,495,[(26,0),(22,1),(11,0),(22,0),(16,1),(12,0),(16,2),(8,1),(3,1),(4,1),(28,0)],[362,911,944,1000,1046]),
(611908,479,[(16,1),(11,2),(16,0),(28,0),(8,2),(3,2),(4,2),(22,2),(3,3),(22,3)],[363,539,635,836,1001,1047,1099]),
(629316,447,[(11,2),(22,1),(16,2),(26,0),(16,3),(28,0),(16,1),(22,0),(8,2),(3,2),(4,2),(3,3)],[364,540,912,945,1002,1048,1100]),
(56900,495,[(11,0),(16,1),(12,0),(3,1),(4,1),(22,1),(8,1)],[79,88,406,416,470,560,636,913,1003,1101,1102,1103,1104,1105,1106,1107,1108]),
(40516,495,[(4,1),(16,1),(12,0),(8,1),(3,1),(22,1),(4,0),(11,0)],[365,637,806,914,1088,1109,1110,1111,1112,1113,1114,1115]),
(611908,463,[(16,1),(3,3),(11,2),(22,3),(16,0)],[89,366,408,471,483,562,638,808,887,980,1005,1090,1107,1114,1116]),
(366148,495,[(16,1),(12,0),(22,1),(16,0),(11,0),(28,0),(8,1),(3,1),(4,1)],[367,639,1006]),
(629316,431,[(16,3),(22,1),(3,3),(11,2),(16,1),(16,2)],[90,368,409,418,472,484,548,640,681,809,859,915,929,981,1007,1078,1108,1115,1116]),
(118100,383,[(16,2),(21,0),(16,0),(28,0),(3,0),(4,0),(22,0),(8,1)],[91,641,860,1008,1117,1118]),
(365908,479,[(22,1),(2,0),(16,0),(22,0),(12,0),(11,0)],[92,369,642,1010]),
(646484,383,[(16,2),(16,0),(2,0),(21,0),(8,0),(3,0),(4,0),(11,2),(22,0),(28,0)],[93,370,643,1011]),
(367956,383,[(2,0),(16,2),(28,0),(8,0),(3,0),(16,0),(4,0),(12,0),(22,1)],[94,371,644,1012]),
(629076,447,[(16,2),(28,0),(16,0),(22,1),(22,0),(8,2),(3,2),(4,2)],[372,645,840,861,1013,1065])]
def sl445_9b400 : Array CaseCode := #[(118116,383,[(26,0),(22,2),(16,0),(22,0),(28,0),(3,0),(0,0),(4,0),(2,0),(8,1)],[95,916,1014,1049,1119]),
(380260,511,[(8,1),(26,0)],[]),
(378212,511,[(16,1)],[373]),
(379236,511,[(26,0)],[374]),
(611684,479,[(16,1),(28,0),(22,2),(16,0),(8,2),(3,2),(4,2)],[376,646,841,888,1016,1051,1068]),
(365924,447,[(12,0),(16,1),(16,0),(28,0),(4,2),(11,0)],[96,377,647,1017,1052]),
(646500,383,[(22,2),(26,0),(16,0),(28,0),(16,1),(8,0),(3,0),(0,0),(4,0),(22,0),(2,0),(11,2)],[97,378,917,1018,1053,1120]),
(629333,415,[(16,2),(22,1),(3,3),(28,0),(16,0)],[98,379,410,473,485,541,648,810,842,982,1019,1070,1116]),
(118117,383,[(16,2),(16,0),(27,0),(28,0),(22,2),(3,0),(4,0),(11,0),(8,1)],[99,649,1020,1079,1121,1122,1123]),
(646501,383,[(16,2),(16,0),(2,0),(12,0),(22,2),(27,0),(8,0),(3,0),(4,0),(11,0)],[100,380,650,1022])]
def sl445_9 : Cases := (410,fun i => ((if i<208 then (if i<96 then (if i<48 then (if i<16 then sl445_9b0 else (if i<32 then sl445_9b16 else sl445_9b32)) else (if i<64 then sl445_9b48 else (if i<80 then sl445_9b64 else sl445_9b80))) else (if i<144 then (if i<112 then sl445_9b96 else (if i<128 then sl445_9b112 else sl445_9b128)) else (if i<176 then (if i<160 then sl445_9b144 else sl445_9b160) else (if i<192 then sl445_9b176 else sl445_9b192)))) else (if i<304 then (if i<256 then (if i<224 then sl445_9b208 else (if i<240 then sl445_9b224 else sl445_9b240)) else (if i<272 then sl445_9b256 else (if i<288 then sl445_9b272 else sl445_9b288))) else (if i<352 then (if i<320 then sl445_9b304 else (if i<336 then sl445_9b320 else sl445_9b336)) else (if i<384 then (if i<368 then sl445_9b352 else sl445_9b368) else (if i<400 then sl445_9b384 else sl445_9b400))))))[i % 16]?.getD default)
def scan445_9 := rangeCases 445 sgBase445 scuts445 9 2 sl445_8 sl445_9
theorem j445_9 (o a b : Nat) (x : scan445_9 o a=true) (y : scan445_9 (o+a) b=true) : scan445_9 o (a+b)=true := @joinRange 445 sgBase445 scuts445 9 2 sl445_8 sl445_9 o a b x y
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_0 : scan445_9 0 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_8 : scan445_9 8 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_16 : scan445_9 16 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_24 : scan445_9 24 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_32 : scan445_9 32 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_40 : scan445_9 40 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_48 : scan445_9 48 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_56 : scan445_9 56 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_64 : scan445_9 64 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_72 : scan445_9 72 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_80 : scan445_9 80 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_88 : scan445_9 88 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_96 : scan445_9 96 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_104 : scan445_9 104 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_112 : scan445_9 112 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_120 : scan445_9 120 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_128 : scan445_9 128 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_136 : scan445_9 136 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_144 : scan445_9 144 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_152 : scan445_9 152 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_160 : scan445_9 160 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_168 : scan445_9 168 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_176 : scan445_9 176 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_184 : scan445_9 184 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_192 : scan445_9 192 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_200 : scan445_9 200 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_208 : scan445_9 208 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_216 : scan445_9 216 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_224 : scan445_9 224 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_232 : scan445_9 232 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_240 : scan445_9 240 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_248 : scan445_9 248 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_256 : scan445_9 256 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_264 : scan445_9 264 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_272 : scan445_9 272 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_280 : scan445_9 280 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_288 : scan445_9 288 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_296 : scan445_9 296 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_304 : scan445_9 304 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_312 : scan445_9 312 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_320 : scan445_9 320 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_328 : scan445_9 328 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_336 : scan445_9 336 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_344 : scan445_9 344 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_352 : scan445_9 352 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_360 : scan445_9 360 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_368 : scan445_9 368 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_376 : scan445_9 376 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_384 : scan445_9 384 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_392 : scan445_9 392 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_400 : scan445_9 400 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_9_408 : scan445_9 408 2=true := by decide +kernel
theorem ck445_9_0m16 : scan445_9 0 16=true := j445_9 0 8 8 ck445_9_0 ck445_9_8
theorem ck445_9_16m16 : scan445_9 16 16=true := j445_9 16 8 8 ck445_9_16 ck445_9_24
theorem ck445_9_32m16 : scan445_9 32 16=true := j445_9 32 8 8 ck445_9_32 ck445_9_40
theorem ck445_9_48m16 : scan445_9 48 16=true := j445_9 48 8 8 ck445_9_48 ck445_9_56
theorem ck445_9_64m16 : scan445_9 64 16=true := j445_9 64 8 8 ck445_9_64 ck445_9_72
theorem ck445_9_80m16 : scan445_9 80 16=true := j445_9 80 8 8 ck445_9_80 ck445_9_88
theorem ck445_9_96m16 : scan445_9 96 16=true := j445_9 96 8 8 ck445_9_96 ck445_9_104
theorem ck445_9_112m16 : scan445_9 112 16=true := j445_9 112 8 8 ck445_9_112 ck445_9_120
theorem ck445_9_128m16 : scan445_9 128 16=true := j445_9 128 8 8 ck445_9_128 ck445_9_136
theorem ck445_9_144m16 : scan445_9 144 16=true := j445_9 144 8 8 ck445_9_144 ck445_9_152
theorem ck445_9_160m16 : scan445_9 160 16=true := j445_9 160 8 8 ck445_9_160 ck445_9_168
theorem ck445_9_176m16 : scan445_9 176 16=true := j445_9 176 8 8 ck445_9_176 ck445_9_184
theorem ck445_9_192m16 : scan445_9 192 16=true := j445_9 192 8 8 ck445_9_192 ck445_9_200
theorem ck445_9_208m16 : scan445_9 208 16=true := j445_9 208 8 8 ck445_9_208 ck445_9_216
theorem ck445_9_224m16 : scan445_9 224 16=true := j445_9 224 8 8 ck445_9_224 ck445_9_232
theorem ck445_9_240m16 : scan445_9 240 16=true := j445_9 240 8 8 ck445_9_240 ck445_9_248
theorem ck445_9_256m16 : scan445_9 256 16=true := j445_9 256 8 8 ck445_9_256 ck445_9_264
theorem ck445_9_272m16 : scan445_9 272 16=true := j445_9 272 8 8 ck445_9_272 ck445_9_280
theorem ck445_9_288m16 : scan445_9 288 16=true := j445_9 288 8 8 ck445_9_288 ck445_9_296
theorem ck445_9_304m16 : scan445_9 304 16=true := j445_9 304 8 8 ck445_9_304 ck445_9_312
theorem ck445_9_320m16 : scan445_9 320 16=true := j445_9 320 8 8 ck445_9_320 ck445_9_328
theorem ck445_9_336m16 : scan445_9 336 16=true := j445_9 336 8 8 ck445_9_336 ck445_9_344
theorem ck445_9_352m16 : scan445_9 352 16=true := j445_9 352 8 8 ck445_9_352 ck445_9_360
theorem ck445_9_368m16 : scan445_9 368 16=true := j445_9 368 8 8 ck445_9_368 ck445_9_376
theorem ck445_9_384m16 : scan445_9 384 16=true := j445_9 384 8 8 ck445_9_384 ck445_9_392
theorem ck445_9_400m10 : scan445_9 400 10=true := j445_9 400 8 2 ck445_9_400 ck445_9_408
theorem ck445_9_0m32 : scan445_9 0 32=true := j445_9 0 16 16 ck445_9_0m16 ck445_9_16m16
theorem ck445_9_32m32 : scan445_9 32 32=true := j445_9 32 16 16 ck445_9_32m16 ck445_9_48m16
theorem ck445_9_64m32 : scan445_9 64 32=true := j445_9 64 16 16 ck445_9_64m16 ck445_9_80m16
theorem ck445_9_96m32 : scan445_9 96 32=true := j445_9 96 16 16 ck445_9_96m16 ck445_9_112m16
theorem ck445_9_128m32 : scan445_9 128 32=true := j445_9 128 16 16 ck445_9_128m16 ck445_9_144m16
theorem ck445_9_160m32 : scan445_9 160 32=true := j445_9 160 16 16 ck445_9_160m16 ck445_9_176m16
theorem ck445_9_192m32 : scan445_9 192 32=true := j445_9 192 16 16 ck445_9_192m16 ck445_9_208m16
theorem ck445_9_224m32 : scan445_9 224 32=true := j445_9 224 16 16 ck445_9_224m16 ck445_9_240m16
theorem ck445_9_256m32 : scan445_9 256 32=true := j445_9 256 16 16 ck445_9_256m16 ck445_9_272m16
theorem ck445_9_288m32 : scan445_9 288 32=true := j445_9 288 16 16 ck445_9_288m16 ck445_9_304m16
theorem ck445_9_320m32 : scan445_9 320 32=true := j445_9 320 16 16 ck445_9_320m16 ck445_9_336m16
theorem ck445_9_352m32 : scan445_9 352 32=true := j445_9 352 16 16 ck445_9_352m16 ck445_9_368m16
theorem ck445_9_384m26 : scan445_9 384 26=true := j445_9 384 16 10 ck445_9_384m16 ck445_9_400m10
theorem ck445_9_0m64 : scan445_9 0 64=true := j445_9 0 32 32 ck445_9_0m32 ck445_9_32m32
theorem ck445_9_64m64 : scan445_9 64 64=true := j445_9 64 32 32 ck445_9_64m32 ck445_9_96m32
theorem ck445_9_128m64 : scan445_9 128 64=true := j445_9 128 32 32 ck445_9_128m32 ck445_9_160m32
theorem ck445_9_192m64 : scan445_9 192 64=true := j445_9 192 32 32 ck445_9_192m32 ck445_9_224m32
theorem ck445_9_256m64 : scan445_9 256 64=true := j445_9 256 32 32 ck445_9_256m32 ck445_9_288m32
theorem ck445_9_320m64 : scan445_9 320 64=true := j445_9 320 32 32 ck445_9_320m32 ck445_9_352m32
theorem ck445_9_0m128 : scan445_9 0 128=true := j445_9 0 64 64 ck445_9_0m64 ck445_9_64m64
theorem ck445_9_128m128 : scan445_9 128 128=true := j445_9 128 64 64 ck445_9_128m64 ck445_9_192m64
theorem ck445_9_256m128 : scan445_9 256 128=true := j445_9 256 64 64 ck445_9_256m64 ck445_9_320m64
theorem ck445_9_0m256 : scan445_9 0 256=true := j445_9 0 128 128 ck445_9_0m128 ck445_9_128m128
theorem ck445_9_256m154 : scan445_9 256 154=true := j445_9 256 128 26 ck445_9_256m128 ck445_9_384m26
theorem ck445_9_0m410 : scan445_9 0 410=true := j445_9 0 256 154 ck445_9_0m256 ck445_9_256m154
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sv445_9 : caseLevel (graphGoal 445) sgBase445 9 2 sl445_9 :=
  caseLevel_ok sgPairs445 (decorateSigned_ok 445 _ _) scert445 sv445_8 (by decide +kernel) ck445_9_0m410

def sl445_10b0 : Array CaseCode := #[(563,255,[(8,0),(16,1),(3,1),(22,1),(16,0),(3,0),(22,0)],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23]),
(563,247,[(16,1),(3,1),(8,0),(22,1),(16,0)],[24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51]),
(259,255,[(8,0),(16,1),(3,0),(22,1),(16,0),(4,0),(11,0),(22,0)],[52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70]),
(275,255,[(16,0),(8,0),(3,1),(22,1),(5,0),(3,0),(4,0),(11,0),(22,0)],[71,72,73,74,75,76,77]),
(35,255,[(4,0),(16,1),(8,0),(3,1),(22,1),(5,0),(16,0),(3,0),(22,0)],[0,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97]),
(291,255,[(8,0),(16,1),(3,1),(22,1),(4,0),(16,0),(3,0),(11,0),(22,0)],[98,99,100,101,102,103,104,105,106,107,108,109,110,111,112]),
(67,255,[(11,0),(16,1),(8,0),(3,1),(22,1),(12,0),(16,0),(3,0),(4,0),(22,0),(26,0)],[1,83,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130]),
(323,255,[(8,0),(16,1),(3,1),(22,1),(11,0),(16,0),(22,0),(3,0),(4,0)],[84,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145]),
(339,255,[(16,0),(8,0),(3,1),(22,1),(12,0),(3,0),(4,0),(11,0),(22,0)],[146,147,148,149,150,151,152]),
(355,255,[(8,0),(16,1),(22,0),(3,1),(16,0),(3,0),(4,0),(11,0)],[153,154,155,156,157,158,159,160,161,162,163,164]),
(512,254,[(16,1),(3,0),(8,0),(22,1),(16,0)],[24,85,118,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181]),
(272,255,[(16,0),(3,0),(8,0),(22,1),(5,0),(0,0),(17,0),(4,0),(11,0),(22,0)],[25,119,182,183,184,185,186,187,188,189,190,191,192,193,194,195]),
(288,255,[(16,1),(3,0),(8,0),(22,1),(4,0),(16,0),(11,0),(22,0)],[26,86,120,183,186,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227]),
(320,255,[(16,1),(3,0),(8,0),(26,0),(22,1),(11,0),(16,0),(4,0),(22,0)],[27,87,121,187,216,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250]),
(336,255,[(16,0),(3,0),(8,0),(22,1),(12,0),(2,0),(17,0),(4,0),(11,0),(22,0)],[28,52,88,200,218,229,246,251,252,253,254,255,256,257,258,259,260,261,262]),
(352,255,[(16,1),(3,0),(22,0),(26,0),(8,0),(16,0),(4,0),(11,0)],[29,53,89,188,201,220,230,247,261,263,264,265,266,267,268,269,270,271,272,273,274,275,276,277,278,279])]
def sl445_10b16 : Array CaseCode := #[(529,253,[(16,0),(3,1),(22,1)],[2,30,54,90,98,122,131,153,165,202,231,264,280,281,282,283,284,285,286,287,288]),
(289,255,[(16,0),(3,1),(0,0),(22,1),(4,0),(19,0),(8,0),(3,0),(23,0),(11,0),(22,0)],[3,31,55,99,123,132,154,166,186,203,232,265,289,290,291,292,293,294,295,296,297,298,299]),
(321,255,[(16,0),(3,1),(0,0),(22,1),(5,0),(11,0),(21,0),(8,0),(3,0),(4,0),(22,0)],[5,33,56,100,133,155,167,184,187,205,233,266,294,300,301,302,303,304,305,306,307,308,309,310]),
(353,255,[(16,0),(22,0),(3,1),(0,0),(5,0),(23,0),(8,0),(3,0),(4,0),(11,0)],[6,34,57,101,124,134,168,188,206,235,267,290,295,301,309,311,312,313,314,315,316,317]),
(546,255,[(4,0),(16,1),(3,1),(22,1),(5,0),(16,0),(8,0),(3,0),(11,0),(22,0)],[7,35,58,102,125,135,146,156,169,207,236,252,269,280,291,318,319,320,321,322,323,324,325,326,327,328]),
(546,251,[(16,1),(4,0),(3,1),(22,1),(16,0)],[8,36,59,71,126,136,147,157,170,189,237,253,270,281,302,312,329,330,331,332,333,334,335,336,337]),
(66,255,[(4,0),(16,1),(11,0),(3,1),(22,1),(5,0),(12,0),(16,0),(8,0),(3,0),(26,0),(22,0)],[10,38,60,158,171,282,338,339,340,341,342,343]),
(322,255,[(16,1),(3,1),(22,1),(4,0),(11,0),(16,0),(22,0),(8,0),(3,0)],[11,39,61,72,103,127,137,148,159,172,190,208,209,216,238,254,271,283,292,294,303,304,313,319,344,345,346,347,348,349,350,351,352,353,354,355,356,357,358,359,360,361,362,363,364,365,366]),
(338,255,[(16,0),(3,1),(2,0),(22,1),(4,0),(12,0),(19,0),(8,0),(3,0),(11,0),(22,0)],[12,40,62,104,138,160,173,210,218,240,255,272,320,349,350,360,367,368,369,370,371,372,373,374]),
(354,255,[(16,1),(22,0),(3,1),(23,0),(4,0),(16,0),(8,0),(3,0),(11,0)],[13,41,63,73,105,128,139,149,174,191,211,220,241,256,284,295,305,314,321,351,352,363,368,373,375,376,377,378,379,380,381,382,383,384]),
(580,255,[(11,0),(16,1),(3,1),(22,1),(12,0),(16,0),(8,0),(3,0),(4,0),(22,0),(26,0)],[17,45,64,74,91,106,140,161,175,192,221,242,285,296,306,315,322,331,353,378,385,386,387,388,389]),
(580,239,[(16,1),(11,0),(3,1),(22,1),(16,0)],[18,46,65,75,92,107,150,162,176,193,222,257,274,286,297,316,323,332,369,379,390,391,392,393,394]),
(340,255,[(16,0),(3,1),(2,0),(22,1),(11,0),(21,0),(8,0),(3,0),(4,0),(28,0),(22,0)],[19,47,66,93,108,141,163,177,223,243,246,258,275,324,333,354,360,380,386,395,396,397,398,399]),
(356,255,[(16,1),(22,0),(3,1),(26,0),(11,0),(16,0),(28,0),(8,0),(3,0),(4,0)],[20,48,67,76,94,109,142,151,178,194,224,247,259,276,287,298,307,309,325,334,355,356,363,370,387,398,400,401,402,403,404,405,406]),
(597,223,[(16,0),(3,1),(22,1)],[21,49,68,95,110,129,143,164,179,225,248,277,326,335,342,364,382,388,392,404,407]),
(357,255,[(16,0),(22,0),(3,1),(2,0),(12,0),(27,0),(8,0),(3,0),(4,0),(11,0)],[22,50,69,96,111,144,180,226,249,261,327,336,365,371,373,393,396,398,405,408,409])]
def sl445_10b32 : Array CaseCode := #[(614,191,[(16,1),(22,0),(3,1),(16,0)],[23,51,70,77,97,112,130,145,152,181,195,227,250,262,288,299,310,328,337,343,366,374,389,394,399,407])]
def sl445_10 : Cases := (33,fun i => ((if i<16 then sl445_10b0 else (if i<32 then sl445_10b16 else sl445_10b32)))[i % 16]?.getD default)
def scan445_10 := rangeCases 445 sgBase445 scuts445 10 1 sl445_9 sl445_10
theorem j445_10 (o a b : Nat) (x : scan445_10 o a=true) (y : scan445_10 (o+a) b=true) : scan445_10 o (a+b)=true := @joinRange 445 sgBase445 scuts445 10 1 sl445_9 sl445_10 o a b x y
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_10_0 : scan445_10 0 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_10_8 : scan445_10 8 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_10_16 : scan445_10 16 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_10_24 : scan445_10 24 8=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_10_32 : scan445_10 32 1=true := by decide +kernel
theorem ck445_10_0m16 : scan445_10 0 16=true := j445_10 0 8 8 ck445_10_0 ck445_10_8
theorem ck445_10_16m16 : scan445_10 16 16=true := j445_10 16 8 8 ck445_10_16 ck445_10_24
theorem ck445_10_0m32 : scan445_10 0 32=true := j445_10 0 16 16 ck445_10_0m16 ck445_10_16m16
theorem ck445_10_0m33 : scan445_10 0 33=true := j445_10 0 32 1 ck445_10_0m32 ck445_10_32
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sv445_10 : caseLevel (graphGoal 445) sgBase445 10 1 sl445_10 :=
  caseLevel_ok sgPairs445 (decorateSigned_ok 445 _ _) scert445 sv445_9 (by decide +kernel) ck445_10_0m33

def sl445_11b0 : Array CaseCode := #[(0,127,[(16,0),(3,0),(22,0)],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32])]
def sl445_11 : Cases := (1,fun i => (sl445_11b0)[i % 16]?.getD default)
def scan445_11 := rangeCases 445 sgBase445 scuts445 11 0 sl445_10 sl445_11
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck445_11_0 : scan445_11 0 1=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sv445_11 : caseLevel (graphGoal 445) sgBase445 11 0 sl445_11 :=
  caseLevel_ok sgPairs445 (decorateSigned_ok 445 _ _) scert445 sv445_10 (by decide +kernel) ck445_11_0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem signedLow445 : Lower (signedRoots 445) (graphGoal 445) 12 := by
  apply finishLower (signedPairs (graphPairs 445 13421781764)) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel)
  let root := sl445_11.2 0
  have eq : (caseValues sgBase445 0 root).toFinset=(signedRoots 445).toFinset := by decide +kernel
  exact eq ▸ sv445_11 0 (by decide)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem signedLow379 : Lower (signedRoots 379) (graphGoal 379) 12 :=
  lower_map (ms:=([118,133,48,33] : List Nat).map swapRows) (base:=signedRoots 445) (G:=graphGoal 445) (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) signedLow445

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem signedLow495 : Lower (signedRoots 495) (graphGoal 495) 13 :=
  lower_map (ms:=([128,49,118,100,83,32] : List Nat).map swapRows) (base:=vars 383) (G:=graphGoal 383) (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) low383

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem signedLow351 : Lower (signedRoots 351) (graphGoal 351) 12 :=
  lower_map (ms:=([81,118,130] : List Nat).map swapRows) (base:=signedRoots 445) (G:=graphGoal 445) (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) signedLow445

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem signedLow191 : Lower (signedRoots 191) (graphGoal 191) 12 :=
  lower_map (ms:=([82,48,129] : List Nat).map swapRows) (base:=signedRoots 445) (G:=graphGoal 445) (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) signedLow445

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem signedLow494 : Lower (signedRoots 494) (graphGoal 494) 11 :=
  lower_map (ms:=([128,100,49] : List Nat).map swapRows) (base:=vars 191) (G:=graphGoal 191) (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) low191

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem signedLow487 : Lower (signedRoots 487) (graphGoal 487) 11 :=
  lower_map (ms:=([128,32,133,100,118,50,16] : List Nat).map swapRows) (base:=vars 191) (G:=graphGoal 191) (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) low191

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem signedLow486 : Lower (signedRoots 486) (graphGoal 486) 8 :=
  lower_map (ms:=([135,115,101,82,66,16] : List Nat).map swapRows) (base:=vars 189) (G:=graphGoal 189) (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) low189

def scuts511 : List SliceCode := [(0,16,10),(1,16,9),(16,0,13),(17,0,11),(24,0,11),(25,0,8),(66,0,12),(132,0,12),(160,0,12),(320,0,12)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem scert511 : certifiedCuts 511 scuts511 := by
  intro c hc
  simp only [scuts511,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact signedColumn (m:=511) (z:=0) (o:=16) (q:=486) (s:=9) (base:=8) (L:=10) signedLow486 (by decide +kernel)
  · exact signedColumn (m:=511) (z:=1) (o:=16) (q:=486) (s:=8) (base:=8) (L:=9) signedLow486 (by decide +kernel)
  · exact signedColumn (m:=511) (z:=16) (o:=0) (q:=495) (s:=0) (base:=13) (L:=13) signedLow495 (by decide +kernel)
  · exact signedColumn (m:=511) (z:=17) (o:=0) (q:=494) (s:=0) (base:=11) (L:=11) signedLow494 (by decide +kernel)
  · exact signedColumn (m:=511) (z:=24) (o:=0) (q:=487) (s:=0) (base:=11) (L:=11) signedLow487 (by decide +kernel)
  · exact signedColumn (m:=511) (z:=25) (o:=0) (q:=486) (s:=0) (base:=8) (L:=8) signedLow486 (by decide +kernel)
  · exact signedColumn (m:=511) (z:=66) (o:=0) (q:=445) (s:=0) (base:=12) (L:=12) signedLow445 (by decide +kernel)
  · exact signedColumn (m:=511) (z:=132) (o:=0) (q:=379) (s:=0) (base:=12) (L:=12) signedLow379 (by decide +kernel)
  · exact signedColumn (m:=511) (z:=160) (o:=0) (q:=351) (s:=0) (base:=12) (L:=12) signedLow351 (by decide +kernel)
  · exact signedColumn (m:=511) (z:=320) (o:=0) (q:=191) (s:=0) (base:=12) (L:=12) signedLow191 (by decide +kernel)
def sgSamples511 := deadsamples
def sgP511 (j : Nat) := (sgSamples511[j]?.getD (0,0)).1
def sgN511 (j : Nat) := (sgSamples511[j]?.getD (0,0)).2
def sgBase511 := decorateSigned 511 sgP511 sgN511
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sgPairs511 : properPairs (graphGoal 511) (asRow sgP511) (asRow sgN511) :=
  chart_pairs (m:=511) (p:=sgP511) (q:=sgN511) (by decide +kernel) (by decide +kernel)

def sl511_11b0 : Array CaseCode := #[(715280688,2543,[(6,7),(7,7),(8,7),(9,7),(3,4),(2,5),(2,1)],[])]
def sl511_11 : Cases := (1,fun i => (sl511_11b0)[i % 16]?.getD default)
def scan511_11 := rangeCases 511 sgBase511 scuts511 11 3 emptyCases sl511_11
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511_11_0 : scan511_11 0 1=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sv511_11 : caseLevel (graphGoal 511) sgBase511 11 3 sl511_11 :=
  caseLevel_ok sgPairs511 (decorateSigned_ok 511 _ _) scert511 (by intro i h; exact (Nat.not_lt_zero i h).elim) (by decide +kernel) ck511_11_0

def sl511_12b0 : Array CaseCode := #[(577024,2038,[(6,3),(7,3),(2,3),(8,3),(9,3),(3,2),(2,1),(2,2)],[]),
(151856,2031,[(6,3),(7,3),(8,3),(9,3),(2,1),(3,0),(5,0),(4,0),(1,0)],[]),
(151856,1519,[(6,3),(7,3),(8,3),(9,3),(2,1),(3,0),(4,0),(0,0)],[0]),
(681264,1535,[(6,3),(7,3),(2,3),(8,3),(3,2),(9,3),(2,0),(6,0),(7,0),(2,1),(4,2),(3,0),(8,0),(9,0)],[])]
def sl511_12 : Cases := (4,fun i => (sl511_12b0)[i % 16]?.getD default)
def scan511_12 := rangeCases 511 sgBase511 scuts511 12 2 sl511_11 sl511_12
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511_12_0 : scan511_12 0 4=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sv511_12 : caseLevel (graphGoal 511) sgBase511 12 2 sl511_12 :=
  caseLevel_ok sgPairs511 (decorateSigned_ok 511 _ _) scert511 sv511_11 (by decide +kernel) ck511_12_0

def sl511_13b0 : Array CaseCode := #[(512,1022,[(6,1),(7,1),(2,1),(8,1),(9,1),(3,0),(2,0),(4,1)],[0]),
(304,1023,[(6,1),(7,1),(2,1),(8,1),(9,1),(3,0),(6,0),(7,0),(4,0),(2,0),(5,0),(8,0),(9,0)],[1,2,3]),
(563,1015,[(6,1),(7,1),(2,1),(8,1),(9,1),(3,1),(2,0),(4,0)],[0])]
def sl511_13 : Cases := (3,fun i => (sl511_13b0)[i % 16]?.getD default)
def scan511_13 := rangeCases 511 sgBase511 scuts511 13 1 sl511_12 sl511_13
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511_13_0 : scan511_13 0 3=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sv511_13 : caseLevel (graphGoal 511) sgBase511 13 1 sl511_13 :=
  caseLevel_ok sgPairs511 (decorateSigned_ok 511 _ _) scert511 sv511_12 (by decide +kernel) ck511_13_0

def sl511_14b0 : Array CaseCode := #[(0,511,[(6,0),(7,0),(2,0),(8,0),(9,0),(3,0),(4,0)],[0,1,2])]
def sl511_14 : Cases := (1,fun i => (sl511_14b0)[i % 16]?.getD default)
def scan511_14 := rangeCases 511 sgBase511 scuts511 14 0 sl511_13 sl511_14
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511_14_0 : scan511_14 0 1=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sv511_14 : caseLevel (graphGoal 511) sgBase511 14 0 sl511_14 :=
  caseLevel_ok sgPairs511 (decorateSigned_ok 511 _ _) scert511 sv511_13 (by decide +kernel) ck511_14_0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem signedLow511 : Lower (signedRoots 511) (graphGoal 511) 15 := by
  apply finishLower (signedPairs (graphPairs 511 13438558465)) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel)
  let root := sl511_14.2 0
  have eq : (caseValues sgBase511 0 root).toFinset=(signedRoots 511).toFinset := by decide +kernel
  exact eq ▸ sv511_14 0 (by decide)

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def stocked (bank : List (Wire Row)) (ws : List Sig) :=
  ∀ a ∈ ws, Available bank (observe a)

theorem stockRead {bank ws a} (sup : stocked bank ws) (r : represented ws a) :
    Available bank (observe a) := by
  rcases r with hm | hn
  · exact sup a hm
  · apply Or.inr
    by_cases az : a=zero
    · subst a
      exact ⟨false, by funext i; change bit i zero = false; simp [bit,zero]⟩
    · have eq : a=one := by by_contra h; exact hn ⟨az,h⟩
      subst a
      refine ⟨true,?_⟩
      funext i
      change bit i one = true
      unfold bit one
      rw [BitVec.getLsbD_allOnes]
      simp

theorem addLegalGate {roots bank k ws} (reach : Reach roots k bank) (supply : stocked bank ws)
    (g : Gate) (ok : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    ∃ q bs, q≤k+1 ∧ Reach roots q bs ∧ Available bs (observe (gv ws g)) ∧
      ∀ a, Available bank a → Available bs a := by
  rcases gate_rep ws g ok with same | (⟨a,ha,_,ev⟩ | ⟨d,a,b,ha,hb,_,_,_,ev⟩)
  · exact ⟨k,bank,by omega,reach,stockRead supply same,fun _ h => h⟩
  · rw [ev,obs_neg]
    exact ⟨_,_,le_rfl,Reach.one reach (supply _ ha),Or.inl (List.mem_cons_self),
      fun _ h => available_cons _ h⟩
  · rw [ev,obs_bin]
    exact ⟨_,_,le_rfl,Reach.two d reach (supply _ ha) (supply _ hb),Or.inl (List.mem_cons_self),
      fun _ h => available_cons _ h⟩

theorem stockGates {roots bank k ws} (gs : List Gate)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (reach : Reach roots k bank) (supply : stocked bank ws) :
    ∃ q bs, q≤k+gs.length ∧ Reach roots q bs ∧ stocked bs (execute gs ws) ∧
      ∀ a, Available bank a → Available bs a := by
  induction gs generalizing k ws bank with
  | nil => exact ⟨k,bank,by simp,reach,supply,fun _ h => h⟩
  | cons g gs ih =>
    obtain ⟨p,next,le,hr,hg,keep⟩ := addLegalGate reach supply g (legal _ (by simp))
    have supply' : stocked next (ws++[gv ws g]) := by
      intro a ha
      rcases List.mem_append.mp ha with old | new
      · exact keep _ (supply a old)
      · simpa using (List.mem_singleton.mp new) ▸ hg
    obtain ⟨q,bs,ls,hs,st,inc⟩ := ih (fun g hg => legal g (by simp [hg])) hr supply'
    exact ⟨q,bs,by simp; omega,hs,st,fun a h => inc _ (keep a h)⟩

abbrev Eight := Fin 8 → Bool
def lo8 (x : Eight) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
  (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)
def hi8 (x : Eight) := lo8 x || x 0 || x 3
def eightInputs := vars 495
def sample8 (r : Row) (j : Fin 8) := bit r (eightInputs.getD j.val zero)
theorem list8 (r : Row) : List.ofFn (sample8 r) = eightInputs.map (bit r) := by
  have id8 : List.ofFn (fun j : Fin 8 => eightInputs.getD j.val zero)=eightInputs := rfl
  calc
    List.ofFn (sample8 r) = (List.ofFn (fun j : Fin 8 => eightInputs.getD j.val zero)).map (bit r) := by
      rw [List.map_ofFn]; rfl
    _ = _ := congrArg (List.map (bit r)) id8

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem splitGraph : ∀ r : Row, bit r graph =
    if bit r control then hi8 (sample8 r) else lo8 (sample8 r) := by decide +kernel

def switchBase (d : Bool) := if d then inputs else signedRoots 511
def switchControl (d : Bool) := if d then control else neg control
theorem looseInputs (d : Bool) : eightInputs ⊆ switchBase d ∧ switchControl d ∈ switchBase d := by
  cases d <;> decide +kernel

theorem switchValue (r : Row) (d : Bool) (u : Sig) :
    bit r (bin d (switchControl d) u) = if bit r control then d else bit r u := by
  rw [bit_bin]
  cases d <;> simp only [switchControl,Bool.false_eq_true,ite_false,ite_true,bit_neg] <;>
    cases h : bit r control <;> simp

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem positiveNine : Lower inputs graph 15 :=
  finishLower (graphPairs 511 13438558465) (by decide +kernel) (by decide +kernel) graph_proper
    (dead_start (before_sound known383 valid383) geomdead tablesdead)

theorem switchedBound (negative : Lower (signedRoots 511) (graphGoal 511) 15)
    (P T : Circuit) (i : Nat) (d : Bool) (hp : FanInTwo P) (ht : FanInTwo T)
    (small : P.size+T.size≤13)
    (low : ∀ x : Eight, let w := P.wires (List.ofFn x); T.eval (w++[w.getD i false])=lo8 x) :
    ∃ x : Eight, T.eval (P.wires (List.ofFn x)++[d])≠hi8 x := by
  by_contra! high
  let w := execute P.gates eightInputs
  let u := w.getD i zero
  let z := bin d (switchControl d) u
  let out := (execute T.gates (w++[z])).getD T.output zero
  have pre (r : Row) : w.map (bit r) = P.wires (List.ofFn (sample8 r)) := by
    rw [list8]
    exact execute_bits _ _ _ (fun g hg => (hp g hg).1)
  have ubit (r : Row) : bit r u = (P.wires (List.ofFn (sample8 r))).getD i false := by
    rw [←pre r]
    exact (b_read r w i).symm
  have readOut (r : Row) : bit r out =
      T.eval (P.wires (List.ofFn (sample8 r))++[if bit r control then d else bit r u]) := by
    change bit r ((execute T.gates (w++[z])).getD T.output zero) = _
    rw [←b_read,execute_bits _ _ _ (fun g hg => (ht g hg).1)]
    rw [List.map_append,List.map_singleton,pre]
    rw [show bit r z = _ from switchValue r d u]
    rfl
  have outEq : out=graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    change bit r out = bit r graph
    rw [readOut,splitGraph,ubit]
    cases h : bit r control
    · exact low (sample8 r)
    · exact high (sample8 r)
  let roots := (switchBase d).map observe
  have initial : stocked roots eightInputs := fun a ha =>
    Or.inl (List.mem_map_of_mem ((looseInputs d).1 ha))
  have controlIn : Available roots (observe (switchControl d)) :=
    Or.inl (List.mem_map_of_mem (looseInputs d).2)
  obtain ⟨p,bank,hpSize,hpRun,hpStock,preserve⟩ := stockGates P.gates hp Reach.start initial
  have hu : Available bank (observe u) := stockRead hpStock (get_rep w i)
  let extended := combine d (observe (switchControl d)) (observe u)::bank
  have he : Reach roots (p+1) extended := Reach.two d hpRun (preserve _ controlIn) hu
  have stock : stocked extended (w++[z]) := by
    intro a ha
    rcases List.mem_append.mp ha with old | last
    · exact available_cons _ (hpStock a old)
    · have e := List.mem_singleton.mp last
      rw [e,show observe z = _ from obs_bin d (switchControl d) u]
      exact Or.inl List.mem_cons_self
  obtain ⟨n,final,htSize,hr,hs,_⟩ := stockGates T.gates ht he stock
  have hit : Available final (observe out) := stockRead hs (get_rep _ _)
  rw [outEq] at hit
  have lower : Lower (switchBase d) graph 15 := by
    cases d
    · have e : graphGoal 511=graph := by decide +kernel
      exact e ▸ negative
    · exact positiveNine
  have bound := lower n final hr hit
  change P.gates.length+T.gates.length≤13 at small
  omega

end PEqualNP.Outside.L_meta_3061_aux

theorem PEqualNP.Outside.L_meta_3061 : have x1 : (Fin (8 : ℕ) → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)); have x2 : (Fin (8 : ℕ) → Bool) → Bool := fun (x2 : Fin (8 : ℕ) → Bool) => x1 x2 || x2 (0 : Fin (8 : ℕ)) || x2 (3 : Fin (8 : ℕ)); ∀ (x3 x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Bool), PEqualNP.MetaComplexity.FanInTwo x3 → PEqualNP.MetaComplexity.FanInTwo x4 → x3.output + (1 : ℕ) = (8 : ℕ) + x3.size → (10 : ℕ) + List.countP (fun (x9 : PEqualNP.CircuitLowerBounds.Gate) => (if x9.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x9.inputs else x9.inputs).contains ((8 : ℕ) + x3.size)) x4.gates ≤ x3.size + x4.size → (∀ (x10 : Fin (8 : ℕ)), (PEqualNP.MetaComplexity.circuitFun (8 : ℕ) x3 ≠ fun (x11 : Fin (8 : ℕ) → Bool) => x11 x10) ∧ PEqualNP.MetaComplexity.circuitFun (8 : ℕ) x3 ≠ fun (x11 : Fin (8 : ℕ) → Bool) => !x11 x10) → (∀ (x11 : Fin (8 : ℕ) → Bool), x1 x11 ≠ x2 x11 → PEqualNP.MetaComplexity.circuitFun (8 : ℕ) x3 x11 = !x5) → (∀ (x12 : Fin (8 : ℕ) → Bool), x4.eval (x3.wires (List.ofFn x12) ++ [PEqualNP.MetaComplexity.circuitFun (8 : ℕ) x3 x12]) = x1 x12) → (∀ (x13 : Fin (8 : ℕ) → Bool), x4.eval (x3.wires (List.ofFn x13) ++ [x5]) = x2 x13) → (14 : ℕ) ≤ x3.size + x4.size := by
  dsimp
  intro P T d hp ht _ _ _ _ low high
  by_contra h
  have small : P.size + T.size ≤ 13 := by omega
  obtain ⟨x, hx⟩ := PEqualNP.Outside.L_meta_3061_aux.switchedBound
    PEqualNP.Outside.L_meta_3061_aux.signedLow511 P T P.output d hp ht small low
  exact hx (high x)
