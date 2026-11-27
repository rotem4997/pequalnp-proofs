import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_3275
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
def seed : Sig := 0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00
def seed01 : Sig := 0x88888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888
def seed02 : Sig := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0
def seed04 : Sig := inputs.getD 0 zero &&& inputs.getD 4 zero
def seed14 : Sig := inputs.getD 1 zero &&& inputs.getD 4 zero
def seed64 : Sig := inputs.getD 6 zero &&& inputs.getD 4 zero

def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem seed_table : ∀ r : Row, bit r seed = (sample r 0 && sample r 3) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem seed_nonzero : seed ≠ zero := by decide +kernel
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

theorem seed_witness : ∀ i : Fin 9,
    (bit (absentRow i) graph != bit (presentRow i) graph) &&
    ((inputs++[seed]).all fun w => w == inputs.getD i.val zero ||
      bit (absentRow i) w == bit (presentRow i) w) = true := by decide +kernel

theorem all_roots {k t S} (h : Live graph k t S) (sub : ∀ v ∈ S, v ∈ inputs++[seed]) :
    S=inputs.toFinset ∨ S=(inputs++[seed]).toFinset := by
  have all (i : Fin 9) : inputs.getD i.val zero ∈ S := by
    have cut := seed_witness i
    simp only [Bool.and_eq_true,Bool.not_eq_true',bne_iff_ne,List.all_eq_true,
      Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at cut
    apply raw_required h _ _ sub (absentRow i) (presentRow i) cut.1
    exact fun v hv hne => (cut.2 v hv).resolve_left hne
  have needed : inputs.toFinset ⊆ S := by
    intro v hv
    have hm := List.mem_toFinset.mp hv
    rw [←input_list,List.mem_ofFn] at hm
    obtain ⟨i,rfl⟩ := hm
    exact all i
  by_cases hseed : seed ∈ S
  · right
    ext w
    constructor
    · exact fun hw => List.mem_toFinset.mpr (sub w hw)
    · intro hw
      have hx := List.mem_toFinset.mp hw
      simp only [List.mem_append,List.mem_singleton] at hx
      exact hx.elim (fun h => needed (List.mem_toFinset.mpr h)) (fun e => e ▸ hseed)
  · left
    exact Finset.Subset.antisymm (fun w hw => by
      have hx := sub w hw
      simp only [List.mem_append,List.mem_singleton] at hx
      rcases hx with hin | rfl
      · exact List.mem_toFinset.mpr hin
      · exact False.elim (hseed hw)) needed

theorem initial_live (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (first : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 3))
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) (small : C.size ≤ 15) :
    ∃ k t, k ≤ 14 ∧ (Live graph k t inputs.toFinset ∨ Live graph k t (inputs++[seed]).toFinset) := by
  have headEq : (execute C.gates inputs).getD 9 zero = seed := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal 9 r).trans ((first (sample r)).trans (seed_table r).symm)
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal C.output r).trans ((congrFun computes (sample r)).trans (edge_table r).symm)
  have out := get_rep (execute C.gates inputs) C.output
  rw [goalEq] at out
  have targetIn := out.resolve_right (fun hn => hn graph_proper)
  cases hgs : C.gates with
  | nil =>
    rw [hgs] at headEq
    exact False.elim (seed_nonzero headEq.symm)
  | cons g gs =>
    have eq0 : gv inputs g = seed := by
      rw [hgs] at headEq
      change (execute gs (inputs++[gv inputs g])).getD 9 zero = seed at headEq
      obtain ⟨l,hl⟩ := exec_extends gs (inputs++[gv inputs g])
      rw [hl] at headEq
      exact headEq
    rw [hgs] at targetIn
    change graph ∈ execute gs (inputs++[gv inputs g]) at targetIn
    rw [eq0] at targetIn
    have tailLegal : ∀ gate ∈ gs, gate.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ gate.inputs.length≤2 := by
      intro gate hg
      apply legal
      rw [hgs]
      exact List.mem_cons_of_mem _ hg
    obtain ⟨k,t,S,hk,run,hs⟩ := extract gs _ tailLegal graph_proper targetIn
    have len : gs.length+1 ≤ 15 := by simpa [Circuit.size,hgs] using small
    refine ⟨k,t,by omega,?_⟩
    rcases all_roots run hs with h | h
    · exact Or.inl (h ▸ run)
    · exact Or.inr (h ▸ run)


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



def apart (m j : Nat) : Bool := m.testBit 9 && (j==0 || j==3)
def word (m j : Nat) : Sig := if apart m j then inputs.getD j zero &&& ~~~seed else inputs.getD j zero
def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,word m i) else none
def vars (m : Nat) := (selected m).map Prod.snd
def vertex (m j : Nat) := if m.testBit j then word m j else zero
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
def colFree (m z o : Nat) :=
  let f := m ^^^ (m &&& (z ||| o))
  if f.testBit 9 && ((z ||| o) &&& 9) != 0 then f ^^^ 512
  else if m == 1535 || m == 2559 then f &&& 511
  else f
def chartGoal (m : Nat) : Sig :=
  if m=1535 then graphGoal m &&& ~~~seed01
  else if m=2559 then graphGoal m &&& ~~~seed02
  else graphGoal m
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
def wordCol (m : Nat) (v : Nat → Bits) (j : Nat) : Bits :=
  if apart m j then v j &&& ~~~(v 0 &&& v 3) else v j
theorem seed_word : seed = inputs.getD 0 zero &&& inputs.getD 3 zero := by decide +kernel
theorem word_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow v i) (word m j.val) = (wordCol m v j.val).getLsbD i.val := by
  by_cases h : apart m j.val = true
  · have e := asRow_bit v i j
    have u := asRow_bit v i (0 : Fin 9)
    have w := asRow_bit v i (3 : Fin 9)
    change (inputs.getD j.val zero).getLsbD (asRow v i).val = _ at e
    change (inputs.getD 0 zero).getLsbD (asRow v i).val = (v 0).getLsbD i.val at u
    change (inputs.getD 3 zero).getLsbD (asRow v i).val = (v 3).getLsbD i.val at w
    rw [word,wordCol,if_pos h,if_pos h,seed_word]
    simp only [bit,BitVec.getLsbD_and,BitVec.getLsbD_not,(asRow v i).isLt,i.isLt,decide_true,Bool.true_and,e,u,w]
  · rw [word,wordCol,if_neg h,if_neg h]
    exact asRow_bit v i j
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,wordCol m p j,wordCol m q j))
theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<9 ∧ a=word m j := by
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
  · exact (word_bit m p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
  · exact (word_bit m q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm

def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then wordCol m v j else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then wordCol m v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using word_bit m v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then wordCol m v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
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
  if g.mask=1535 then
    let nonedge := dneg (dbin false (ws.getD 0 defaultDecor) (ws.getD 1 defaultDecor))
    ws.map (fun w => dbin false w nonedge)
  else if g.mask=2559 then
    let nonedge := dneg (dbin false (ws.getD 0 defaultDecor) (ws.getD 2 defaultDecor))
    ws.map (fun w => dbin false w nonedge)
  else ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  have base := raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  intro a ha
  unfold wiresOf at ha
  split at ha
  · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp ha
    exact faithful_bin false (base w hw) (faithful_neg (faithful_bin false
      (faithful_get base 0) (faithful_get base 1)))
  · split at ha
    · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp ha
      exact faithful_bin false (base w hw) (faithful_neg (faithful_bin false
        (faithful_get base 0) (faithful_get base 2)))
    · exact base _ ha

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  if m=1535 then liftGoal m v &&& ~~~(v 0 &&& v 1)
  else if m=2559 then liftGoal m v &&& ~~~(v 0 &&& v 2)
  else liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  by_cases e1 : m=1535
  · have u := asRow_bit v i (0 : Fin 9)
    have w := asRow_bit v i (1 : Fin 9)
    have h := bit_liftGoal m v i
    change (inputs.getD 0 zero).getLsbD (asRow v i).val = (v 0).getLsbD i.val at u
    change (inputs.getD 1 zero).getLsbD (asRow v i).val = (v 1).getLsbD i.val at w
    have seedEq : seed01 = inputs.getD 0 zero &&& inputs.getD 1 zero := by decide +kernel
    simp only [chartGoal,chartSamples,e1,ite_true,bit,seedEq,BitVec.getLsbD_and,
      BitVec.getLsbD_not,(asRow v i).isLt,i.isLt,decide_true,Bool.true_and,u,w] at h ⊢
    rw [h]
  · by_cases e2 : m=2559
    · have u := asRow_bit v i (0 : Fin 9)
      have w := asRow_bit v i (2 : Fin 9)
      have h := bit_liftGoal m v i
      change (inputs.getD 0 zero).getLsbD (asRow v i).val = (v 0).getLsbD i.val at u
      change (inputs.getD 2 zero).getLsbD (asRow v i).val = (v 2).getLsbD i.val at w
      have seedEq : seed02 = inputs.getD 0 zero &&& inputs.getD 2 zero := by decide +kernel
      have ne12 : (2559 : Nat) ≠ 1535 := by decide
      simp only [chartGoal,chartSamples,e2,ne12,ite_false,ite_true,bit,seedEq,BitVec.getLsbD_and,
        BitVec.getLsbD_not,(asRow v i).isLt,i.isLt,decide_true,Bool.true_and,u,w] at h ⊢
      rw [h]
    · simpa only [chartGoal,chartSamples,e1,e2,ite_false] using bit_liftGoal m v i
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
def g813key4 (i : Nat) : Nat := 0x40000
def g813d4 (i : Nat) : Nat := 0x1f
def g813l4 : Packing := (1,0,1,1,1,0,0,g813d4)
def g813d3 (i : Nat) : Nat := 0xb940
def g813l3 : Packing := (1,1,1,1,1,0,0,g813d3)
def g813samples : Array (Bits × Bits) := #[(0x50505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505,0x30303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303),(0x0,0x0),(0x222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222,0x676767676767676767676767676767676767676767676767676767676767676767676767676767676767676767676767676767676767676767676767676767676767676767676767676767676767676767676767676767676767676767676767),(0x3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a3a,0x80808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808),(0x0,0x0),(0xc5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5,0x646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464646464),(0x0,0x0),(0x0,0x0),(0xd8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8,0x939393939393939393939393939393939393939393939393939393939393939393939393939393939393939393939393939393939393939393939393939393939393939393939393939393939393939393939393939393939393939393939393)]
def g813columns : IndexTree ColumnInfo := (.leaf [])
def g813autos : Array (List Nat) := #[[]]
def g813levels : Nat → Packing
  | 3 => g813l3
  | 4 => g813l4
  | _ => emptyPacking
def g813index : Nat → Nat → Option (Nat × Nat)
  | 3 => fun _ => none
  | 4 => lookupWord 1 4 1 6 1 1 (g813key4)
  | _ => fun _ => none
def g813 : Forest := ⟨813,4,fun j => g813samples[j]?.getD (0,0),g813columns,g813autos,g813levels,g813index⟩
set_option maxHeartbeats 0 in
theorem geom813 : graphValid g813 (boundsBefore known383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s813_4_0 : block g813 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl813_4 : block g813 4 0 1 = true := s813_4_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s813_3_0 : block g813 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl813_3 : block g813 3 0 1 = true := s813_3_0
theorem tables813 : checkedTables g813 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g813 0 0 0 = true)
  · exact (rfl : block g813 1 0 0 = true)
  · exact (rfl : block g813 2 0 0 = true)
  · exact bl813_3
  · exact bl813_4
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low813 : Lower (vars 813) (graphGoal 813) 5 :=
  lower_forest (g:=g813) (i:=0) (hints:=12884910853) (before_sound known383 valid383) geom813 tables813 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps813 : List (Nat × List Nat) := [(813,[])]
def known813 := extendKnown known383 5 maps813
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid813 : Known known813 := extendKnown_ok valid383 low813 (by decide +kernel)
def g559d4 (i : Nat) : Nat := 0x3f
def g559l4 : Packing := (1,0,1,1,1,0,0,g559d4)
def g559samples : Array (Bits × Bits) := #[(0x9a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a6,0x82082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082082),(0x3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf,0x145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145),(0x659659659659659659659659659659659659659659659659659659659659659659659659659659659659659659659659659659659659659659659659659659659659659659659659659659659659659659659659659659659659659659659659,0xe38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38),(0x410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410,0x145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145),(0x0,0x0),(0x820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820820,0xf7df7df7df7df7df7df7df7df7df7df7df7df7df7df7df7df7df7df7df7df7df7df7df7df7df7df7df7df7df7df7df7df7df7df7df7df7df7df7df7df7df7df7df7df7df7df7df7df7df7df7df7df7df7df7df7df7df7df7df7df7df7df7df7d),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g559columns : IndexTree ColumnInfo := (.leaf [(8,0,39,0,4)])
def g559autos : Array (List Nat) := #[[]]
def g559levels : Nat → Packing
  | 4 => g559l4
  | _ => emptyPacking
def g559index : Nat → Nat → Option (Nat × Nat)
  | 4 => fun _ => none
  | _ => fun _ => none
def g559 : Forest := ⟨559,4,fun j => g559samples[j]?.getD (0,0),g559columns,g559autos,g559levels,g559index⟩
set_option maxHeartbeats 0 in
theorem geom559 : graphValid g559 (boundsBefore known813) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s559_4_0 : block g559 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl559_4 : block g559 4 0 1 = true := s559_4_0
theorem tables559 : checkedTables g559 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g559 0 0 0 = true)
  · exact (rfl : block g559 1 0 0 = true)
  · exact (rfl : block g559 2 0 0 = true)
  · exact (rfl : block g559 3 0 0 = true)
  · exact bl559_4
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low559 : Lower (vars 559) (graphGoal 559) 5 :=
  lower_forest (g:=g559) (i:=0) (hints:=8449) (before_sound known813 valid813) geom559 tables559 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps559 : List (Nat × List Nat) := [(559,[])]
def known559 := extendKnown known813 5 maps559
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid559 : Known known559 := extendKnown_ok valid813 low559 (by decide +kernel)
def g937d4 (i : Nat) : Nat := 0x3f
def g937l4 : Packing := (1,0,1,1,1,0,0,g937d4)
def g937samples : Array (Bits × Bits) := #[(0x451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451,0x41041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041),(0x0,0x0),(0x0,0x0),(0x104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104104,0x79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e),(0x0,0x0),(0xefbefbefbefbefbefbefbefbefbefbefbefbefbefbefbefbefbefbefbefbefbefbefbefbefbefbefbefbefbefbefbefbefbefbefbefbefbefbefbefbefbefbefbefbefbefbefbefbefbefbefbefbefbefbefbefbefbefbefbefbefbefbefbefb,0xcb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2),(0x0,0x0),(0x28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a,0x34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d),(0x924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924,0x41041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041041)]
def g937columns : IndexTree ColumnInfo := (.leaf [(1,0,424,0,4)])
def g937autos : Array (List Nat) := #[[]]
def g937levels : Nat → Packing
  | 4 => g937l4
  | _ => emptyPacking
def g937index : Nat → Nat → Option (Nat × Nat)
  | 4 => fun _ => none
  | _ => fun _ => none
def g937 : Forest := ⟨937,4,fun j => g937samples[j]?.getD (0,0),g937columns,g937autos,g937levels,g937index⟩
set_option maxHeartbeats 0 in
theorem geom937 : graphValid g937 (boundsBefore known559) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s937_4_0 : block g937 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl937_4 : block g937 4 0 1 = true := s937_4_0
theorem tables937 : checkedTables g937 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g937 0 0 0 = true)
  · exact (rfl : block g937 1 0 0 = true)
  · exact (rfl : block g937 2 0 0 = true)
  · exact (rfl : block g937 3 0 0 = true)
  · exact bl937_4
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low937 : Lower (vars 937) (graphGoal 937) 5 :=
  lower_forest (g:=g937) (i:=0) (hints:=14227111941) (before_sound known559 valid559) geom937 tables937 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps937 : List (Nat × List Nat) := [(937,[])]
def known937 := extendKnown known559 5 maps937
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid937 : Known known937 := extendKnown_ok valid559 low937 (by decide +kernel)
def g815key6 (i : Nat) : Nat := 0x7800004fad404
def g815d6 (i : Nat) : Nat := 0x7f
def g815l6 : Packing := (1,0,1,1,1,0,0,g815d6)
def g815key5 (i : Nat) : Nat := 0x90088
def g815d5 (i : Nat) : Nat := 0xa2faa1ed20
def g815l5 : Packing := (2,1,1,1,1,3,0,g815d5)
def g815d4 (i : Nat) : Nat := 0xda54120
def g815l4 : Packing := (1,2,1,1,1,0,0,g815d4)
def g815samples : Array (Bits × Bits) := #[(0x2b4015a00ad0056802b4015a00ad0056802b4015a00ad0056802b4015a00ad0056802b4015a00ad0056802b4015a00ad0056802b4015a00ad0056802b4015a00ad0056802b4015a00ad0056802b4015a00ad0056802b4015a00ad0056802b40,0xe090704838241c120e090704838241c120e090704838241c120e090704838241c120e090704838241c120e090704838241c120e090704838241c120e090704838241c120e090704838241c120e090704838241c120e090704838241c120e0907),(0x26c59362c9b164d8b26c59362c9b164d8b26c59362c9b164d8b26c59362c9b164d8b26c59362c9b164d8b26c59362c9b164d8b26c59362c9b164d8b26c59362c9b164d8b26c59362c9b164d8b26c59362c9b164d8b26c59362c9b164d8b26c59,0x17058b82c5c162e0b17058b82c5c162e0b17058b82c5c162e0b17058b82c5c162e0b17058b82c5c162e0b17058b82c5c162e0b17058b82c5c162e0b17058b82c5c162e0b17058b82c5c162e0b17058b82c5c162e0b17058b82c5c162e0b17058),(0xac5ad62d6b16b58b5ac5ad62d6b16b58b5ac5ad62d6b16b58b5ac5ad62d6b16b58b5ac5ad62d6b16b58b5ac5ad62d6b16b58b5ac5ad62d6b16b58b5ac5ad62d6b16b58b5ac5ad62d6b16b58b5ac5ad62d6b16b58b5ac5ad62d6b16b58b5ac5ad,0xa87254392a1c950e4a87254392a1c950e4a87254392a1c950e4a87254392a1c950e4a87254392a1c950e4a87254392a1c950e4a87254392a1c950e4a87254392a1c950e4a87254392a1c950e4a87254392a1c950e4a87254392a1c950e4a8725),(0x89094484a2425121289094484a2425121289094484a2425121289094484a2425121289094484a2425121289094484a2425121289094484a2425121289094484a2425121289094484a2425121289094484a2425121289094484a2425121289094,0xd000680034001a000d000680034001a000d000680034001a000d000680034001a000d000680034001a000d000680034001a000d000680034001a000d000680034001a000d000680034001a000d000680034001a000d000680034001a000d0),(0x0,0x0),(0x5072a839541caa0e55072a839541caa0e55072a839541caa0e55072a839541caa0e55072a839541caa0e55072a839541caa0e55072a839541caa0e55072a839541caa0e55072a839541caa0e55072a839541caa0e55072a839541caa0e55072a,0x86284314218a10c5086284314218a10c5086284314218a10c5086284314218a10c5086284314218a10c5086284314218a10c5086284314218a10c5086284314218a10c5086284314218a10c5086284314218a10c5086284314218a10c508628),(0x0,0x0),(0x0,0x0),(0x510328819440ca206510328819440ca206510328819440ca206510328819440ca206510328819440ca206510328819440ca206510328819440ca206510328819440ca206510328819440ca206510328819440ca206510328819440ca20651032,0xd7806bc035e01af00d7806bc035e01af00d7806bc035e01af00d7806bc035e01af00d7806bc035e01af00d7806bc035e01af00d7806bc035e01af00d7806bc035e01af00d7806bc035e01af00d7806bc035e01af00d7806bc035e01af00d7806)]
def g815columns : IndexTree ColumnInfo := (.leaf [(264,0,39,0,4)])
def g815autos : Array (List Nat) := #[[],[48,33,133]]
def g815levels : Nat → Packing
  | 4 => g815l4
  | 5 => g815l5
  | 6 => g815l6
  | _ => emptyPacking
def g815index : Nat → Nat → Option (Nat × Nat)
  | 4 => fun _ => none
  | 5 => lookupWord 2 6 1 6 1 1 (g815key5)
  | 6 => lookupWord 3 9 1 6 1 1 (g815key6)
  | _ => fun _ => none
def g815 : Forest := ⟨815,6,fun j => g815samples[j]?.getD (0,0),g815columns,g815autos,g815levels,g815index⟩
set_option maxHeartbeats 0 in
theorem geom815 : graphValid g815 (boundsBefore known937) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s815_6_0 : block g815 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl815_6 : block g815 6 0 1 = true := s815_6_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s815_5_0 : block g815 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl815_5 : block g815 5 0 2 = true := s815_5_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s815_4_0 : block g815 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl815_4 : block g815 4 0 1 = true := s815_4_0
theorem tables815 : checkedTables g815 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g815 0 0 0 = true)
  · exact (rfl : block g815 1 0 0 = true)
  · exact (rfl : block g815 2 0 0 = true)
  · exact (rfl : block g815 3 0 0 = true)
  · exact bl815_4
  · exact bl815_5
  · exact bl815_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low815 : Lower (vars 815) (graphGoal 815) 7 :=
  lower_forest (g:=g815) (i:=0) (hints:=12884910337) (before_sound known937 valid937) geom815 tables815 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps815 : List (Nat × List Nat) := [(815,[])]
def known815 := extendKnown known937 7 maps815
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid815 : Known known815 := extendKnown_ok valid937 low815 (by decide +kernel)
def g877key6 (i : Nat) : Nat := 0x10000
def g877d6 (i : Nat) : Nat := 0x30ff
def g877l6 : Packing := (1,0,2,1,1,0,0,g877d6)
def g877d5 (i : Nat) : Nat := 0x305f950
def g877l5 : Packing := (1,1,2,1,1,0,0,g877d5)
def g877samples : Array (Bits × Bits) := #[(0x124112411241124112411241124112411241124112411241124112411241124112411241124112411241124112411241124112411241124112411241124112411241124112411241124112411241124112411241124112411241124112411241,0x540954095409540954095409540954095409540954095409540954095409540954095409540954095409540954095409540954095409540954095409540954095409540954095409540954095409540954095409540954095409540954095409),(0x0,0x0),(0x493e493e493e493e493e493e493e493e493e493e493e493e493e493e493e493e493e493e493e493e493e493e493e493e493e493e493e493e493e493e493e493e493e493e493e493e493e493e493e493e493e493e493e493e493e493e493e493e,0xc17ac17ac17ac17ac17ac17ac17ac17ac17ac17ac17ac17ac17ac17ac17ac17ac17ac17ac17ac17ac17ac17ac17ac17ac17ac17ac17ac17ac17ac17ac17ac17ac17ac17ac17ac17ac17ac17ac17ac17ac17ac17ac17ac17ac17ac17ac17ac17a),(0x698669866986698669866986698669866986698669866986698669866986698669866986698669866986698669866986698669866986698669866986698669866986698669866986698669866986698669866986698669866986698669866986,0xa840a840a840a840a840a840a840a840a840a840a840a840a840a840a840a840a840a840a840a840a840a840a840a840a840a840a840a840a840a840a840a840a840a840a840a840a840a840a840a840a840a840a840a840a840a840a840a84),(0x0,0x0),(0x93e593e593e593e593e593e593e593e593e593e593e593e593e593e593e593e593e593e593e593e593e593e593e593e593e593e593e593e593e593e593e593e593e593e593e593e593e593e593e593e593e593e593e593e593e593e593e593e5,0x83c483c483c483c483c483c483c483c483c483c483c483c483c483c483c483c483c483c483c483c483c483c483c483c483c483c483c483c483c483c483c483c483c483c483c483c483c483c483c483c483c483c483c483c483c483c483c483c4),(0x71807180718071807180718071807180718071807180718071807180718071807180718071807180718071807180718071807180718071807180718071807180718071807180718071807180718071807180718071807180718071807180718,0x1b081b081b081b081b081b081b081b081b081b081b081b081b081b081b081b081b081b081b081b081b081b081b081b081b081b081b081b081b081b081b081b081b081b081b081b081b081b081b081b081b081b081b081b081b081b081b081b08),(0x0,0x0),(0xa4b8a4b8a4b8a4b8a4b8a4b8a4b8a4b8a4b8a4b8a4b8a4b8a4b8a4b8a4b8a4b8a4b8a4b8a4b8a4b8a4b8a4b8a4b8a4b8a4b8a4b8a4b8a4b8a4b8a4b8a4b8a4b8a4b8a4b8a4b8a4b8a4b8a4b8a4b8a4b8a4b8a4b8a4b8a4b8a4b8a4b8a4b8a4b8,0x243224322432243224322432243224322432243224322432243224322432243224322432243224322432243224322432243224322432243224322432243224322432243224322432243224322432243224322432243224322432243224322432)]
def g877columns : IndexTree ColumnInfo := (.leaf [(64,0,813,512,5),(33,0,332,0,4),(8,4,353,0,4)])
def g877autos : Array (List Nat) := #[[]]
def g877levels : Nat → Packing
  | 5 => g877l5
  | 6 => g877l6
  | _ => emptyPacking
def g877index : Nat → Nat → Option (Nat × Nat)
  | 5 => fun _ => none
  | 6 => lookupWord 1 4 1 6 1 1 (g877key6)
  | _ => fun _ => none
def g877 : Forest := ⟨877,6,fun j => g877samples[j]?.getD (0,0),g877columns,g877autos,g877levels,g877index⟩
set_option maxHeartbeats 0 in
theorem geom877 : graphValid g877 (boundsBefore known815) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s877_6_0 : block g877 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl877_6 : block g877 6 0 1 = true := s877_6_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s877_5_0 : block g877 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl877_5 : block g877 5 0 1 = true := s877_5_0
theorem tables877 : checkedTables g877 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g877 0 0 0 = true)
  · exact (rfl : block g877 1 0 0 = true)
  · exact (rfl : block g877 2 0 0 = true)
  · exact (rfl : block g877 3 0 0 = true)
  · exact (rfl : block g877 4 0 0 = true)
  · exact bl877_5
  · exact bl877_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low877 : Lower (vars 877) (graphGoal 877) 7 :=
  lower_forest (g:=g877) (i:=0) (hints:=13019128581) (before_sound known815 valid815) geom877 tables877 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps877 : List (Nat × List Nat) := [(877,[]),(939,[48,33,133,118])]
def known877 := extendKnown known815 7 maps877
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid877 : Known known877 := extendKnown_ok valid815 low877 (by decide +kernel)
def g623key6 (i : Nat) : Nat := 0x1800
def g623d6 (i : Nat) : Nat := 0x48ff
def g623l6 : Packing := (1,0,2,1,1,0,0,g623d6)
def g623d5 (i : Nat) : Nat := 0x505dd31
def g623l5 : Packing := (1,1,2,1,1,0,0,g623d5)
def g623samples : Array (Bits × Bits) := #[(0x70ac70ac70ac70ac70ac70ac70ac70ac70ac70ac70ac70ac70ac70ac70ac70ac70ac70ac70ac70ac70ac70ac70ac70ac70ac70ac70ac70ac70ac70ac70ac70ac70ac70ac70ac70ac70ac70ac70ac70ac70ac70ac70ac70ac70ac70ac70ac70ac,0x222822282228222822282228222822282228222822282228222822282228222822282228222822282228222822282228222822282228222822282228222822282228222822282228222822282228222822282228222822282228222822282228),(0x952795279527952795279527952795279527952795279527952795279527952795279527952795279527952795279527952795279527952795279527952795279527952795279527952795279527952795279527952795279527952795279527,0x910591059105910591059105910591059105910591059105910591059105910591059105910591059105910591059105910591059105910591059105910591059105910591059105910591059105910591059105910591059105910591059105),(0xaf90af90af90af90af90af90af90af90af90af90af90af90af90af90af90af90af90af90af90af90af90af90af90af90af90af90af90af90af90af90af90af90af90af90af90af90af90af90af90af90af90af90af90af90af90af90af90af9,0x4ab84ab84ab84ab84ab84ab84ab84ab84ab84ab84ab84ab84ab84ab84ab84ab84ab84ab84ab84ab84ab84ab84ab84ab84ab84ab84ab84ab84ab84ab84ab84ab84ab84ab84ab84ab84ab84ab84ab84ab84ab84ab84ab84ab84ab84ab84ab84ab8),(0xe520e520e520e520e520e520e520e520e520e520e520e520e520e520e520e520e520e520e520e520e520e520e520e520e520e520e520e520e520e520e520e520e520e520e520e520e520e520e520e520e520e520e520e520e520e520e520e52,0x154215421542154215421542154215421542154215421542154215421542154215421542154215421542154215421542154215421542154215421542154215421542154215421542154215421542154215421542154215421542154215421542),(0x0,0x0),(0x60c860c860c860c860c860c860c860c860c860c860c860c860c860c860c860c860c860c860c860c860c860c860c860c860c860c860c860c860c860c860c860c860c860c860c860c860c860c860c860c860c860c860c860c860c860c860c860c8,0xccc4ccc4ccc4ccc4ccc4ccc4ccc4ccc4ccc4ccc4ccc4ccc4ccc4ccc4ccc4ccc4ccc4ccc4ccc4ccc4ccc4ccc4ccc4ccc4ccc4ccc4ccc4ccc4ccc4ccc4ccc4ccc4ccc4ccc4ccc4ccc4ccc4ccc4ccc4ccc4ccc4ccc4ccc4ccc4ccc4ccc4ccc4ccc4),(0x855285528552855285528552855285528552855285528552855285528552855285528552855285528552855285528552855285528552855285528552855285528552855285528552855285528552855285528552855285528552855285528552,0x4da04da04da04da04da04da04da04da04da04da04da04da04da04da04da04da04da04da04da04da04da04da04da04da04da04da04da04da04da04da04da04da04da04da04da04da04da04da04da04da04da04da04da04da04da04da04da04da),(0x0,0x0),(0x0,0x0)]
def g623columns : IndexTree ColumnInfo := (.leaf [(64,0,559,512,5),(1,32,78,0,4),(12,0,99,0,4)])
def g623autos : Array (List Nat) := #[[]]
def g623levels : Nat → Packing
  | 5 => g623l5
  | 6 => g623l6
  | _ => emptyPacking
def g623index : Nat → Nat → Option (Nat × Nat)
  | 5 => fun _ => none
  | 6 => lookupWord 1 4 1 6 1 1 (g623key6)
  | _ => fun _ => none
def g623 : Forest := ⟨623,6,fun j => g623samples[j]?.getD (0,0),g623columns,g623autos,g623levels,g623index⟩
set_option maxHeartbeats 0 in
theorem geom623 : graphValid g623 (boundsBefore known877) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s623_6_0 : block g623 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl623_6 : block g623 6 0 1 = true := s623_6_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s623_5_0 : block g623 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl623_5 : block g623 5 0 1 = true := s623_5_0
theorem tables623 : checkedTables g623 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g623 0 0 0 = true)
  · exact (rfl : block g623 1 0 0 = true)
  · exact (rfl : block g623 2 0 0 = true)
  · exact (rfl : block g623 3 0 0 = true)
  · exact (rfl : block g623 4 0 0 = true)
  · exact bl623_5
  · exact bl623_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low623 : Lower (vars 623) (graphGoal 623) 7 :=
  lower_forest (g:=g623) (i:=0) (hints:=16785665) (before_sound known877 valid877) geom623 tables623 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps623 : List (Nat × List Nat) := [(623,[]),(911,[48,33,133,118])]
def known623 := extendKnown known877 7 maps623
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid623 : Known known623 := extendKnown_ok valid877 low623 (by decide +kernel)
def g879key9 (i : Nat) : Nat := 0x900000001200b50000130024010000001
def g879d9 (i : Nat) : Nat := 0x831642ff
def g879l9 : Packing := (1,0,4,3,1,0,0,g879d9)
def g879key8 (i : Nat) : Nat := 0x16008628001e100002d02300000000000001936400001cfe612800000085688060
def g879d8 (i : Nat) : Nat := 0x3968021cc519016a20e5b50450da830da830da83875a3c281400ff597fd61ff546fe66df957f611
def g879l8 : Packing := (6,1,4,4,1,8,0,g879d8)
def g879key7 (i : Nat) : Nat := 0x10000
def g879d7 (i : Nat) : Nat := 0x2040000232c21141006080100000cd86e5180bd51f283c505017f5c165bfceeb0f7c755877eb2ac37f5cd61bfae0b0dfd76546feb9aa3fd58551bfae0a8e7e669577b33423dd95611
def g879l7 : Packing := (13,2,4,1,1,7,0,g879d7)
def g879d6 (i : Nat) : Nat := 0x97d859dd61
def g879l6 : Packing := (1,3,4,1,1,0,0,g879d6)
def g879samples : Array (Bits × Bits) := #[(0x44858a08890b141112162822242c50444858a08890b141112162822242c50444858a08890b141112162822242c50444858a08890b141112162822242c50444858a08890b141112162822242c50444858a08890b141112162822242c50444858a,0x4210a0a0842141410842828210850504210a0a0842141410842828210850504210a0a0842141410842828210850504210a0a0842141410842828210850504210a0a0842141410842828210850504210a0a0842141410842828210850504210a),(0x93a477512748eea24e91dd449d23ba893a477512748eea24e91dd449d23ba893a477512748eea24e91dd449d23ba893a477512748eea24e91dd449d23ba893a477512748eea24e91dd449d23ba893a477512748eea24e91dd449d23ba893a477,0x328455d06508aba0ca1157419422ae8328455d06508aba0ca1157419422ae8328455d06508aba0ca1157419422ae8328455d06508aba0ca1157419422ae8328455d06508aba0ca1157419422ae8328455d06508aba0ca1157419422ae8328455),(0x9d3b90073a77200e74ee401ce9dc8039d3b90073a77200e74ee401ce9dc8039d3b90073a77200e74ee401ce9dc8039d3b90073a77200e74ee401ce9dc8039d3b90073a77200e74ee401ce9dc8039d3b90073a77200e74ee401ce9dc8039d3b90,0x8d2b80031a57000634ae000c695c0018d2b80031a57000634ae000c695c0018d2b80031a57000634ae000c695c0018d2b80031a57000634ae000c695c0018d2b80031a57000634ae000c695c0018d2b80031a57000634ae000c695c0018d2b80),(0x2a1270265424e04ca849c09950938132a1270265424e04ca849c09950938132a1270265424e04ca849c09950938132a1270265424e04ca849c09950938132a1270265424e04ca849c09950938132a1270265424e04ca849c09950938132a1270,0x2254302444a860488950c09112a18122254302444a860488950c09112a18122254302444a860488950c09112a18122254302444a860488950c09112a18122254302444a860488950c09112a18122254302444a860488950c09112a1812225430),(0x0,0x0),(0x424abc4884957891092af1221255e24424abc4884957891092af1221255e24424abc4884957891092af1221255e24424abc4884957891092af1221255e24424abc4884957891092af1221255e24424abc4884957891092af1221255e24424abc,0x4242b40084856801090ad0021215a004242b40084856801090ad0021215a004242b40084856801090ad0021215a004242b40084856801090ad0021215a004242b40084856801090ad0021215a004242b40084856801090ad0021215a004242b4),(0x613a9900c275320184ea640309d4c80613a9900c275320184ea640309d4c80613a9900c275320184ea640309d4c80613a9900c275320184ea640309d4c80613a9900c275320184ea640309d4c80613a9900c275320184ea640309d4c80613a9,0x73a80000e7500001cea000039d4000073a80000e7500001cea000039d4000073a80000e7500001cea000039d4000073a80000e7500001cea000039d4000073a80000e7500001cea000039d4000073a80000e7500001cea000039d4000073a8),(0x0,0x0),(0x34c947e069928fc0d3251f81a64a3f034c947e069928fc0d3251f81a64a3f034c947e069928fc0d3251f81a64a3f034c947e069928fc0d3251f81a64a3f034c947e069928fc0d3251f81a64a3f034c947e069928fc0d3251f81a64a3f034c947,0x158843d02b1087a056210f40ac421e8158843d02b1087a056210f40ac421e8158843d02b1087a056210f40ac421e8158843d02b1087a056210f40ac421e8158843d02b1087a056210f40ac421e8158843d02b1087a056210f40ac421e8158843)]
def g879columns : IndexTree ColumnInfo := (.fork 4 (.fork 2 (.leaf [(328,0,39,0,4),(256,0,623,512,7)]) (.leaf [(66,0,813,512,5),(64,0,815,512,7)])) (.fork 2 (.leaf [(33,0,334,0,7),(0,32,78,769,6)]) (.leaf [(12,0,355,0,7),(0,4,353,522,6),(2,0,877,512,7)])))
def g879autos : Array (List Nat) := #[[]]
def g879levels : Nat → Packing
  | 6 => g879l6
  | 7 => g879l7
  | 8 => g879l8
  | 9 => g879l9
  | _ => emptyPacking
def g879index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 1 4 1 6 1 1 (g879key7)
  | 8 => lookupWord 7 29 2 9 4 1 (g879key8)
  | 9 => lookupWord 4 16 1 8 3 1 (g879key9)
  | _ => fun _ => none
def g879 : Forest := ⟨879,9,fun j => g879samples[j]?.getD (0,0),g879columns,g879autos,g879levels,g879index⟩
set_option maxHeartbeats 0 in
theorem geom879 : graphValid g879 (boundsBefore known623) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s879_9_0 : block g879 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl879_9 : block g879 9 0 1 = true := s879_9_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s879_8_0 : block g879 8 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s879_8_3 : block g879 8 3 3=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl879_8 : block g879 8 0 6 = true := (@block_merge g879 8 0 3 3 s879_8_0 s879_8_3)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s879_7_0 : block g879 7 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s879_7_3 : block g879 7 3 10=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl879_7 : block g879 7 0 13 = true := (@block_merge g879 7 0 3 10 s879_7_0 s879_7_3)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s879_6_0 : block g879 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl879_6 : block g879 6 0 1 = true := s879_6_0
theorem tables879 : checkedTables g879 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g879 0 0 0 = true)
  · exact (rfl : block g879 1 0 0 = true)
  · exact (rfl : block g879 2 0 0 = true)
  · exact (rfl : block g879 3 0 0 = true)
  · exact (rfl : block g879 4 0 0 = true)
  · exact (rfl : block g879 5 0 0 = true)
  · exact bl879_6
  · exact bl879_7
  · exact bl879_8
  · exact bl879_9
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low879 : Lower (vars 879) (graphGoal 879) 10 :=
  lower_forest (g:=g879) (i:=0) (hints:=12901687553) (before_sound known623 valid623) geom879 tables879 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps879 : List (Nat × List Nat) := [(879,[]),(943,[48,33,133,118])]
def known879 := extendKnown known623 10 maps879
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid879 : Known known879 := extendKnown_ok valid623 low879 (by decide +kernel)
def g1007key12 (i : Nat) : Nat := 0x22a0014c8bb2c99c43cae8483dd100000001c70000000129c004d001a1000000000090400124e3e3b200a32d52b22b0b460000000000c40c5003883988b0000000030100100d
def g1007d12 (i : Nat) : Nat := 0x1686704ff
def g1007l12 : Packing := (1,0,5,5,1,0,0,g1007d12)
def g1007key11 (i : Nat) : Nat := (if i<1 then 0x562c0011874d09f7400000000000032b39e48b32535f8489b0000000000000926e8d8dae00000000000014a600000018d8d44b32dc840012c500055480000008646c606e3d3ae6b0538001f05000024f7813d669f3014000000e0a90840000000007c280000006a0000000000092185c1d3453854ea91fc820000003c2ea0c00025dd078001a10e61237b330000f2c20440009126e538ff8bd96d389800000021400015f1138f3f19ec9d74454d131e0193059ce4c5412c65800004e3424454862aa3e7dd400000000000021b7f4191480000009b809e39480016610000002832b5e810000000000000026a009dfc7baf80007836398b5800033a000550b2279a491e3b132b541c9162e199ec000b61ac506b6d0a000557806fd2ec98ebb000000000000000019b91ce000000000000000076f3740f67f83eecac1963d080c5cf36620b513034fd05484c33340b2bbf2d000648c22e0000000000000b2f9055cc668fd03754febf8db4185478220f03a5333938b58814762c10000000b97b091c7400104a22618c4000ad53a1feea24b4e159cb51800109600000000008440007ea40000005140002a220000000000001b8f1b238cfcbb2c6ea28000000f63da58000000536865aaded7b9270006db12560000000002b46000eaa9f44722c593c24d276386d87170001dbb27d4a7d06b0fe5df0000003d8f2a3cecdf83559b60e66c0e8360e8ec4f5dd092af4a11c50cb9662370002d6c001f28fc280000013cf282531336e5d272d876becbf30ca81ae7652a07933f47f21cba70d595453a0e2f760e49215c589eb76289a77f08341db65d1442783c1a64d9f3c52044cbbcae000f25ccb2c7cb6a424c54e62a5379bcee680013ccfdf000051a000968000250099f0005c3cd5400000019b800000000071c40000000005efc000000bb4000101a0000004970917e73abd800000000000000036b8000615c8c375d1b90007dbd4d700ffd2e62139774c93cd9dfcd291a0000153d0c000866000000000000000000000007529f8a9be09f137fb0fc09393ccf3c34f54ec9e28ff34000d341950002ef547a543a80fc4ad58eaa2328000e5525a42acd7ccb83930918001a02f8cf5e28d51a20004b94001190000000000095a00010774e000000032c00000000007f9448a992000385e306a680000002a37922f7100000000000000000004100200000000004404218400100004000000a0421001010001050090400050010410c008000100000108104c0050400020040823000000001000c00800040004420000010000d924300a0000410490421800010c100004008010600a1800000880400442010001c004300000000514104004024034000f00004304000008000000024310400008000100000104304000f0001ca08100f0050020000c1000000024000 else 0x16136baf40e2fe4690e06a10000000000049000001200000025a7b280000005f6282600050b51d00008a70000c800000007d880000008420006ad40000000000000000c7eb0e0000000000011b25000058cd719019db4d1412804d62ae0006bb8003babfbd0000000000fb500066b00000000001ad8001756f27da413b8a00000918b0c6000f461969d797d400016dac7781f82b0002da8000c5015200000000006e1a34d4240e9d17c0000000000000001f3273000034900004b9000000000000028d6793ece00005f8000000e59)
def g1007d11 (i : Nat) : Nat := 0x21640ee55e0b192a9dcf058c62c616c770590e456578e4b190a9c323c16658e2f0578e46404a8c318f439e1538b460370a919386e55e0b3f0a9632c6e7854e32a708b18e3f854cb2b871c8c6436e782ca861cf0a966b90a31851df6d9815a935460e9348a92606f11823003feb2ffd74ff8e9ff593feaa7fe44ffae3ff1c7feb0ffd51ffa83ff107fe90ffc21ffc23df957df227f611
def g1007l11 : Packing := (18,1,5,8,1,10,0,g1007d11)
def g1007key10 (i : Nat) : Nat := (if i<2 then (if i<1 then 0x24ac4b1e5d806053e336ac355aac7d20c00000004d3c000000004ee81fe0000f74527580002ae6000000009fa9ca2000022c000014fcc5140d7b658c22c000000000001baa92e6e2c80004139c73541acd2e00000001927c0bf81b008340002d5a1c444278ea85662b08c07bd84c75b9000014ed2c231db9214c36c509946aa966000000034550000000156225bd846a0002c279ce8706e00016326977c09a25eba1c2273b90d984b0e20000e1dc0000b25c113bd42000346a800000000001274800000001b6c0000000f4f927a053400002c724525abe203fed3306fe3502649f08b62bb61100000001b99c0007d259ac73b022e6d4ddd2e39762603d04413cfc1798c1d1730000000000066af290041eb08680000000cb6cb3874ecfb420002605989afb062364a68be4ce16bc806717ec7fe979621d4993ad60000000000000000000692f0e501d941bfba080000000949c4195914451f0000307c0000000d930c68a09b8000b44983ecf54da9800000003a5b1abf92eb5100000000000000000e8546964314000291db47600012027d3080000000f8022d65cd344200001a1b906900017055b3d00008cd00000000114ad4b000022a70000000000015381c339015a1df821dcf80201c5026c70000a48370a4eb800009a1f474de97a57dbd76e66c120000c0040000031433000000020000050421402c004000000f0c10000000003000030011c50010420000410010c004300204008000308014000004108b2c00012030040021000802c00440030040410c20c300000318010500000100a0470800022cd5400020400040d000000000008000900000c0841c00c308b00404a1811c40000000a204204200300010500000008220b3cc0030010050000800410000910040040010010400000000450812000000410451822c50010810880070000410081800840000800802c30020470830020c01000000820000000000401002c04000010021021c51090480001410c60040000400400c00400010c418c0020000000c904000308000004000a0000000c048208000100000904500000000000134404200224000e0401000001420040400020820c705e3800020000010c008000010108008128018a0020400400000000000000001450021420010801010010030001420001800000c10870000c20000040000c418400000000000000c0001c10001c10c504100100000500008200000534008200108000200000104b2410820040400800000400000000400400000802000050010001000000801011031010050400410000020430000020400000091000000020030040450010412844400000c100958100000508200100704100004900400000d0400c108000f00004808008100140000000010100020204000008a1c41830011c0040001002040003 else 0x201300000003f589e573cb60318000758b9b46b13e7088dfb00000000000084ca242d6052492450c12e00000000c13f180000000000001bbe00000001a961bcc0000098e656ca94000274000002b9320d36d0263c9b1e1128c8269332d6a00000000000f01d572342acd269c9a0000000000058b9b06a440800000000002b157888000121a0e030d3db32b87aa8126d6500000000000000054f400029148da4000000000004ed55162918000000000000000115e800040ed8898ede7e4f038c0001b2e3ab0000000000006697a5480001d410000000000000007e7e0000000391fb88e00019880880d9c1016e00000cbb9c80001c41c0000000000000000005da769b25290e6a09725161819800000000332f9180006a09b4dc00017581806000155080af8e65819e7453879800000000002b2c85bf9aed27c107ce6cb52b293a86b3b02c7b0a3184c74b16cd566d3224fdca87000000000000000f18300ac00000000000000014f0000000148d1618ce6df8120000000000000000001816e14e3b1a00018e8a289000198ec00009447584308c00061bcac0ed25b14ff5cb000000000000cdb34cd5710a63004b000000000000000b59d0a9920eb27700000001d0f800000000000ac40000e4a00000000000091d400016e0614d0000000000064f99a1b9b7a81071e33b0e52c26258a86315220d89428000000000000000000735747aff20f237f00e00006950000c58c0001aca0000000000004f0e26d00007230000000031f0c1fb001e1fd2c0b08302b52aba00000003349deb2ba8e3a8dd702511059319c76cb6c7900011b4c27e80008414d1108df349a34f7694c000019a4d1ea47e0d034c72346767aa17148ef9dc000266ab5f2c5900001cb5ca9c0001ba48000105cf404000162f00000000000221900000000d5980000000000000013510c6c000000000007a250000d2c86e5795dad03d0ec000445714aa680c0002246000000000000000ec2c00000001d48f903a250000000031880003edb52e284340000000000062e0b70c00079ded3aa628af5d6df45ad184b9859b826633cf5606cc0c7df802f387b11d6023470e73d6c80cc5dc21d7382df0961806425b6ce48000a38400024c400002c31ba6d82d95e0047c0003216e6c79321d2a00000cbae17d0b73c72b8d78564764be07823d000102940006858299a0ab80006a20e2060003c3dae144c3a9210000084882d5aa30a90cde1cbde00030db62940000000000000008988c29800000000000000000000000000e65000000000493f536319e60ed42e205133df8a470c932980004eb600000002eae80000000d8f40000000cd1a0002ea36c52b9433794456c2312c6fc03368235d96d89e01000070ac0000681617080000000298c00050f000009a45560024c000172c400020852) else (if i<3 then 0x1a0658b789b37d8600000007242d824000116ca02200000000000157700019857334800000000001e1e8000ccf876940000000000000000000000a58710fd44b00000001d32c0000000dae9d688e81c9a5bb8d20f3805b2c1f475a9490dd52d2321de0a2e56a4747502b5d441c11581c140001e86192d98d0b580a78707261e8000120a2a8e0001e9754017621b00003474ad0de8dc8ab278716b6a46b3538686bf0000000160554bfc4192bfa00000005219cda0000351519d8531ed81800000005355530800061082542000205c8c3ee105b66f2fc80000000000000074731a817b080000ad0a3b8000380b0000000000000000ebf000162e80002099000000026208edd00000002762d9988ba0bb3e4498000c1a4000000061ccb3febab00004c1c0527215f76cd564f2572a41c7200000001e20c000000000002b3c00000000000000000000002d7b19400000000000174b16f4a221117ac1b800016bc000000008fa0000000042369389c870000092b520706200002a6400000000000000000000000000f07aafb3e431b3b25d02ff55245b5c27942e2ddff199cb50723c69e414df5095d1c85ad4595a84a818296758da13ffc8f50e009a112b127dbcf414ca09d10aa0d59607ab399cbca2cb35160001698c22c22d30702d57d178000147530c7000008a600000000000585e0000000106c000000000000000000082a8c4300000a6106a00006d790000000000000004c8919d66c98cf10000971ef0200003b2ef22776b3e014304000000055b000001380cfcbe35c120137800000000001fa6144f80000000c9f78aa800000001b3a569800010233584000047a81500000000000000018522a9a5420c034000080f000092b79a17817fd56d9df6108000000000016041cdab485fdb0b54eea8fcae6190c4f05042c90000000000000000e993c99c0000000289073e8f1d54971230650a414800070e1b9986f180000000f0f3e4112ab3cc2d0b147425b124ae00000001add703e0002a34800060fbd7d40002927621fb250000648b0001686f0c8d18000d40003c0e80008a05098800035910000000312fb2846a17837400000000000ca7400000000000000000000006109e16543c7421000000000005dc1695e896a4e5a856cc4e000000062a9000141c40007c35a30b66b80f9d631e8cb44e4903ed3a00010a88000159ff197a5f64ab00006a40e3f0000620ea101f45d14509bb5b55eb7b43ceedc351169ab045951e1b2a7460339592439c7b4b60763a2b0000000154db46e887591c710ac4185cbc00032bf80000000c3840000000000000002edbe1ebda47b69d17e57aa122c17f568a8cce11889d64ce7c0543adfa220f94c7bdd6800000000840bd140000f3e94100409782000000000001f1d40000d8699274a37a8c8ecc9b640000 else (if i<4 then 0x749d256e00000001a3be6a7ccb40003699c4300000b9d9b5530decb1332f464dc9d20000000229bddf3bb746637c9100000000000104a80000001baa00000000000000036dbfe8c000166c027bbcc191d7528992400000000000000070c90000f7740000000852400000000000334e0000000791d3d72000146b00000000e6b4af5000000010b6800000001b3369d8e5a00001054fa552230000d823c1447196e1f60fe0003af239630000000241f6e4e10de7673b204936426b895bab59e8469b92415768b112b416551000000004bb4e4a00006cbebc5600000000000000097b3526bcc3a28ea14eed7ecdf00000000000000010c645ec00000000000446400015d764d8253d062b186000000022396cb8000000000000000333e00014fabdb8b8001a706ae68e34143a5b80005d32000000000000000339c000325544b7d8bb6a6aa8b7d05d3c0a70cb120134c54ff16a9667a8fc27678e00000000bdae00000000000a037a0ec0000000d93e0003d6fe21e6d7c00036f68000c260671fa9c5264a1f400000000000e98179fe2d9800000000002cf75df8000000024d080007c7d214b0933d82d09200000003ab10001f91e03580000000000306a5a1c382e6964171e26b00010128c9c5ad584a80001ceb800092d0000000065bb0000000242e8000630315bc343e86d62205035f536ab7756a955389f2c08b22808cc62f80004befd82c00031b20000178be260000d57c06b3128d9299ae2000169c80000000e9a60730000000172a40000000e1ea000000064e2294000000006157000166c7f0610500000000253055f0000000000006ab8d83614d40000000a1e4834c96bc9110001b15800022149d3554880006d4c00000000000000014782062228900dc52e397789190cd000000004578000d2b9ea45485fa2d4c363b80a8300002576000000000000000d0390a58000f558f1c000000001a1de3f80000000219c00000004e0f0000a45ce275d10ca7cc69000000004d21977000029e9102400000006184855bf2ac237f5e74a516020812ecb5830e00019115428a88bc0c58be58a38b85d109aa58000b3ef7601747292f79078a8161a4501d1ee00000000000322a000000045d4c46d085800000007353d53f8170000a568c014000753f0d3bda25c44f5fc04ff1982306800000001a2c15b1a305aafe8c80007102316c9b2213978dc00000003e8eb5a600000002afd00005932000147e809bf14f67430e2cd69000126980005a2340cfbb054dce017dbdd3b5245a0e6419231b1800021f6cbd60002a4680000000919c00000000000b1fbd66f164e82c0003651800032a7d9b3c86740a888f13328a0d20f23d8ba97b6480f6e8c7b5c800000001abf903305032aa7286e00543a6a44ac615ae3a35a19d9c12000208d98f1ed94534a0bb048a else 0x196c45d6e9e60002d6a0000c93a0003063d25ebba7f23df70a93f80752150f4f684edcbe335b41c9da8e184592048d4cf2000000019175d5edc2e18b944900007b9e0001d003eb70000000000028bbf487b10c00000000001e77c0001ecd0000e768294cd452114900b423c25c352b464c6c60c5b84f2980c0000000b37a0000884f8e2000000014a9566a0371d188000000000000003e4e0000aaf0a168e7ae07c54f00000000357b000000012f88000128c00008950000f04fb58a6a90000ca4e00000000000000153680005663f9cb15b2923f14cfc7f5223f43618b958ba2f3b4a71e6c313b48e212681c38f9d9aee65508fdc322632c8e3d8a2ba503280002227343ac10475988b2d2fd27b52018000fd5b696eb41fe4a0067c1ce952a8c3e32cd0130b079fce507733c00000000001f3f8b4fc8ffa5460000000056d92c5194f31a1c49287258a36ad8a11aa6dca00000319273f179dc000000000000003e538000000191500005075cdbf135e0b30a060000dabb2a4e8da00000000000189d000000000000000736e0002a95b1200001b3d8a8d8000492a00008680000000000022daed1a0000b19800030eff3c46860cda300f000000000000000189a639d55ced4305508185e89e4363b690594c5c28ed000064f4122c15000000000000000000000001caf3021fca4b403c5582bc6046a54)))
def g1007d10 (i : Nat) : Nat := (if i<1 then 0xd3870dfb374cdb23628d4633eccc531e8c52308cc022fd8bea2ed0ba12d90b432c88b162bb8ac629eca4528209d926e098925a0947247c91323748a7221887a212c82320407e11e3c7591ce07021b306a41a60677195862717e05c91684587157c53714904f512fc4ac11f446310b440c0fac3ca0e6c3880d2c3230c082e10a90283095021708101f107781af063815804f812404440fe03ac0b501fc05e00bc000ffd84597ff60565ffe885d3ff61574ffd655d3ff60574ffc815d3ff5d564ffd87553ff61954ffd76553ff5d154ffd82553ff60554ffe77913ff5d644ffe885c7ff61971ffd765c7ff61571ffd655c7ff61171ffc845c7ff5d171ffd645c7ff55171ffe445c7ff60971ffc825c7ff50971ffd641c7ff91071ffd421c7ff10871ffd87587ff9dd61ffd85587ff5d561ffd84587ff5d161ffd54587ff60961ffd52587ff50961ffd71587ff5d951ffd74547ff59151ffe44547ff58951ffd42547ff10951ffe88507ff61d41ffc87507ff9dd41ffd86507ff5d941ffd85507ff5d541ffd65507ff5d141ffd54507ff60941ffc82507ff5c941ffd62507ff54941ffd42507ff5c541ffd61507ff9dc41ffd72107ff1c841ffe88487ff61521ffd65487ff61121ffc84487ff5d121ffc74487ff59121ffd54487ff91121ffd71487ff58521ffd41487ff5d021ffc74087ff91021ffe77847ff5da11ffd74847ff1d211ffd64847ff91211ffd72847ff1ca11ffd62847ff50a11ffc42847ff88a11bfe88596ff60165bfe885d3df95574bfd805d2ff60474f7e55592ff60d64bfe88552ff61d54bfd86553bf99954f7d75553df59554fbd74552ff60d54bfd80553df95644fbd74913ef55244fbc87913ef9de44fbd76913ef5d644fbd65913ef20a44fbc81912ffa2171dfe775c7bf99971f7c855c77f5d571f7e555c7ef91171bfd835c6ff60171bfd861c7bf99871bfd841c7ef91071bfd821c6ffa2161bfd875877f9dd61efd76587bf59561f7e55587ef91161bfd83586ff60161bfd875477f9dd51bfd86547bf99951fbe44546ff60d51f7d52547fd5c551bfe88506ff61d41dfe77506ff61941efe66506ff61541f7e55507ef55141fbe44506ff60d41fbd42507fd5c541ff561506ff60141bfd871077f9dc41bfd83106ff60841bfe88486ff61521f7e55486ff61121fbe44487fd58521bfd80486ff61021fbe440877f9de11efe66847ef91211ff571847fd58611ff541847fd48611ff487847fd9de11ff576847fd5d611ff565847fd21211ff574847fd1d211ff564847fd55211ff644847fd20a11ff572847fd1ca11ff562847fd54a11ff542847fd10a11ff6228479f99a55b7d851d2fd60474bf9801d36f9de44ebe66913cf95644afd861c6f760c41b7d85086ef61021bf9800877d9de11ef666847dd95611fb644847f988a11 else (if i<2 then 0xf04818c008242428218ac1804c98c485801cacde08a61a301802a8f02530300345ab415572c7062461c3490caa68c3859230e120c600aa482ce4821214756703282c2893d51e343a604280854f8140c10c24382811eaf0167121804ad540c0e0878a0a6162428f191851ea8f1a2558b4c10525c0a9618a8c30f04b890528f1d185ae1861e1630b2a30c3c5ae2428b547ae1c4861878e161bc09f214425c8478e971808b0de7c0300b2b3a5f90c57211c4858620b0de2591c041822a382f9f0008a478e1613cd5001915878ef0197051681e3bc568c2cc0fc950018a57c2e0a2ca142790018ae02e4256706f046599aaef09810b378164462d309aae96085f94c76ab9378165161bca62366abbc2616616b85e05b51f01e3aac6161bc85f0481b27791f2c316b0f1c1bc8b8de1050892e00ca863f006549062ce9654312b559c1bc8b8de10e02e422431504417547c620e0200a8628b05563105871818a9470c1648379f0247a680ef22c302f04848354e17e25f90d40f5470b0c0bc8ff0984a8585f024a9674bf14031534ef118591c05c8471217c01950c70d544c070b0c17c092a80c0bc5520b0de2a91c049780a30a949700c0ca9478eab2c37917e090050e07e4af80048f66ace17e2586f281c18078242cc3bc4616404487780054c1bc4e2a425e001524ef03e30b2b80951de3c921800e2c303f3e0012380f048591c84703f05428b30b05e2acb286702121bc0c1654c2c1559c34a8ef3e090c597260bc051854f2c3782a40de45f8243001eace1de45c6f071a27c921c57210400a8e20e17567107cb4de275530e171bc0faa61eae3789d54cafc025c54be0a8f1a6f02d7152f81cad3152954c2aab81795698cac1795de0ab03954c260b95f84c54de0aab18f5c1bcab4de0e08aab4c41e2fc2b226f0b8a92aae17e132b3155c2703d706f2ad37840f05e572628f17e57115a6f0548c07ae17e55a6f081e2d72b2551cad3795c616c1779abe15c640b0c21618418588586f3e25a63765de0590336f2d7c4b4c7045430cb951631c544547087151300d57878f298e2d8795d57c2b3f04de0a9180bf357c2b3301de7c555c69606567951a52c93a24b29262462912242e90523fa8f663b18e0a3538cca3118bc22c88a662788942221875a1bc863616c85120f983620b7823e06e81360027fa1fab7e45f547c41ef67b71ec27a69e5d78b9df87709d8c7521d2773fdcd772bdc807199c30703dbe06e8db746d4db2b6c0dab86a25a5368919f567519b3662d96a652592f63ad8b5623585060317dd5e817635cd171a5bad6a75a35657584d5c8562d55c54994e252cd48b517142d50153d64e493864cd130c4c012df4af92b249b923147d11c54675175453514144d5106435d0bd42a9074413102b3ff0fe93f3cf763d38f113b6ceb33a48e553924e3 else 0x8121462028918b04040103040036ab8481002028b0c96a4970b0c0c01c6040231218283012d31c3040a35c2c28c1030030c1000c59100148b85910014b2c5a6040c0185869c5530330f0414190330240c8184820640c141120655c244032a14c5558324422195850659c19715160cde2b120a0230b06255a88830a32225715160cc4832e0642a51705245f3e2b302430485060140a301004042c20024608086002821a10090a8f4c249e47870a3930300281287a6123a1386090c0caa640b14247e07ce02486031681f3810900301951691c3448c7921831e3048ca894c3c91582b0024a920d55020015241aa9890b121405556712141ae2b5489c90e18242d55c7f0484806030a85aa916b89922791e2c5002f92a980122f916985002d90eb8a86006162800fc1212085830074c5490024e06003262a614257080014a8b44e16b8a860062b38880279242d7002f92ab85122d971e7c12182838300a191890e5c2cde0a0800542923c64c5470b0064c085862a48c2e30f2441608181217962c603289041409078e1a3085498c18d18ac4a61014a8e4951cad3002430fe41ab2634a340f9))
def g1007l10 : Packing := (230,2,5,10,1,14,0,g1007d10)
def g1007key9 (i : Nat) : Nat := 0x52360851e734000000437800325000000000295000000000000000000459730089ac2bdf8007e18002f57a396cce7d8b2f08000001b8ef35d47e58000ae1ca105316ebb592ed10b3cce64780cdba06c79869668919ecfb3190447d547a231fd48000000000000001c6dcd7bc80075d3e600000056500000000042272b657721800000000566cb9800000500481a470005068000000eb1ee80068d0000000000000f4da48006688000000007cb8000da04fe49d4480026380014ddd01dbd58b0fb970000000000001110000002fbb790a9febd8100074080000000032d4aab8ef2e9e371252f4361e47cc27200000000000000048bd2c0df00049580077c980d06303db0cd33c61f1e109b5ad839313aa6105e3dd964dc32f386af56a683fa88a8000000004a8000000000000159ce9000000276e7880041b5848003208003f2d9dbcf00000060431cbc00da80000000047453c0002abfafe1acb1441dcb5dcd53b79adb4494a58ca9ee699e26d938b6a07b2899f445d60000756000575b7c0006670007200003295c200035780000004c80003371480000000040c000000000000782f8265261c6f78000007a7d9022cf245b4bf600011449bc8e0000007d18000002d280a0b70004ed7178aa0007210001c55e2205d780c8ab92480000b2b4e81fa8dcd0df00007ed8229f1000000783011800000000288fa67072f77386b53188add5c6bb80028f23279a05589d4270000004ea000040020088000e2000022804108080100010140000122000e000040000200040218861000200902000088088201002088000014c0080000000001c200840200cc501800080200804301801
def g1007d9 (i : Nat) : Nat := (if i<3 then (if i<1 then 0xf3bc8908faf99a448467f930b94237f5911ca11bfcc80e508cff26142846efb2a214237f59110a119fe4c44508f7d9dd71847decccb8c23fb6445c611bfac9ae308f7d5c971846feb2eb0c23df67758611f7abb2c308fed91161846feb26b0c23ef56258611bfacba8308f7d9dd41846feb2ca0c23ef66650611fdb2228308dfd64d41847f6a84a0c237f59748611efb3ba4308dfd65921847deccc90c237f59448611fdb2224308dfd64d21847fcc4490c237f59621e11bfaca10f08dfd64887846fe9313bc23df4989de11efa4a4ef08f7d24a77846fed32bb4237f4985da11efb3baed08dfd64d76846feb20bb423ef48799a11f7b3bccd08fbd99975846fed32b2c237f59759611efb3bacb08fbd5d965846feb26b2c23f757695611bfacb90908f7d9dc84846feb26424237f59221211bfb4cae908dfd26174847beceeba423df5765d211f7b332e908fdd95574846feb26ba4237f5905d211dfacc0e908dfd64874846feb2eb2423df67759211f7abb2c908fdd95564846feb26b24237f69955211bfacbaa908f7d9dd54846feb2caa423ef66655211fbabaaa908fdd59554847f6ae8aa4237f59355211bfa4c48908f7d9de44847eecab22423fb57491211fdaaa48908fed26244847f692f22423fb48791211fdb3bc8908fed5da44847f6aeb22423fb56591211fda4948908dfd65c82847becee414237f59420a11fdb2210508dfda6572846fe930b9423df4875ca11efb3bae508f7d5d972847decccb9423f76555ca11fdb222e508dfd64d72846feb20b94237f5941ca11fdb220e508dfd64072846feb2eb1423df67758a11fbb2aac508fed91162846feb20b14237f69954a11bfacbaa508f7d9dd52846feb2ca9423ef66654a11fbab2aa508fdd55152847f6c88a94237f59354a11ff2b92a508dfda6542846fe930a14237f59750a11efb3ba8508dfd65942847de92ca1423ef66650a11bfacaa8508fdd95542847f6908a1423fb56450a11fdb2228508dfd64d42847fcae4a1423fe56250a11bfac828508dfd65c42847becee214237f59510a11fbb2a88508dfd26222847becef11423f765588a11fdb2244508ff95ca22847fcaa511423fe54288a11ff24c44508ff959622847fc92911423fe48488a11ff2ba44508ff91d222847fcac911423fe55488a11ff32244508cfda65811d3a7cef2ac89e3e6695644bdcc8105225af658819126fb2b442e337c989557197f4cb0c38eaf61a441c67f321442833de9960c41cef3bb0620cefa658408737b0f22043abd8691021d9ec2c8810e7e9dd8008777488c00437f19021e11e7b3bccd08f5d9de55847ceccd2ac237759521211b7acb0e908ddd65474846fab263a4237e5921d211bf8c80e908f6d9de44847d6ccd22423f365591211bf8c80e508ddd65442847eccab11423fa64488a11 else (if i<2 then 0x22e2a8fdd54971546ff321442833fd97a21419fecb510a0cff656885067fb27442833fd92a2141dfcc8510a0cff642885067fd32c3a83b7c9561d419fec9b0ea0cff641875073fb0e43a836fd9621d419fe4c4eea0e7f61e775073f9313ba839fe889dd41cfec1ceea0f7d246775073fb013ba833fe9961941cff3bb0ca0cff64d865067fb30bb283afd865d941d7f444cca0ebf61e665079fcef33283afd83999419ff4cb0aa0e7f9dd855075fcccc2a833fd93615419fecc2eaa0cff661655076fd112aa83b7d8795541ebf3bcaaa0edf61a55507cfccd2aa83b7d8395541bdf4caa8a0eefa215450777b0eaa283dbe7755141f5f332a8a0fcf5d554507e7acaaa283bbd8791141edf3bc88a0eef61644507e7cab22283bbd8391141bbeca904a0efb608825067f930b9283b7d8554941f9eaa2a4a0defa654250777d10a1283dbe7750941f5e4b284a0eef61942507d7ccca12837bd9550941f9f2aa84a0eef60d42507f5904a1283fad6250941fda48a84a0def641425067fb30b8a837f6995c541dfb442e2a0f7d21d71507beceeb8a83ef6665c541fba4aae2a0efd61571507beaeab8a83f76555c541fda4a2e2a0fed55171507f6c88b8a83bf5835c541efab92e2a0fed50971506feb20b8a837f69958541dfb442c2a0dfd65d61507beceeb0a83ef57658541f7ab2ac2a0fdd95561507f6aa8b0a83ef56258541fdaa12c2a0cffa65871067fb26c38839fd879dc41cfec1cee20ef765d831077bceec1883bdd9260c419ff4cb0420e7f9dd821067fb26c10833fd985c841cfec3ae420ef760d721077db04b90833fd981c841bfcc80e420cff656884867fb29442433fd90a21219ff4cb0a90cff64d854867fb30b2a43b7e8895521dbec34aa90f9f99a554876fb072aa433fe9961121d7e4b30890ebf999844876fcaac22433fd93611219fec830890eef610844867fb30ba2433fc985d1219fecc0e890ddf65474486feb223a2437f9901d1219fecc2c890cff661544867f93122243bbd8491121dde4c48890eefa224448777b0f22243dbe7791121ddec348890faf99a4448777b0b22243f3e5591121ddec1c8890eef60244486fed32b0a43bf68858521efb3bac290fbd5d961487deacab0a43f765558521dfac22c290fed91161487fcaa4b0a433fd98505219ff4cb0810eefa658408777b2ec2043bbc97610219fecc2e810edf6157408777b08ba0433fd981d021bbeca8e810edf6147408777b083a0437f5911d021bfcc80e810e7f61e440875fb0d22043b7d8591021ddec248810def6624408777b0f22043dbe7791021dfd3bb0010efe5d1800877f0e8c0043bfa44600219fe4c4ef08e7f262778479fcef334233fc985d211b7ecb0e908ddf65474846fbb263a4237ed921d211bfac88e908dfe640748467f93122423bbc9891211ed else 0xc290ffd55161486ffd32ba0437fd985d021bfec82e810dffa6576846ffb26bb4237fd905da11bff4cae908f7f5d974846ffb26ba4237fd905d211bfecbac908fbf5d964846ffb26b24237fd941ca11bfecb88508cff656885d27fb23442e93fd90a2174dbf444aaba79f99a555d36fb012aae9bf581205749ff4cb023a6fda65811d37eb24c08e9bf49260474dbec1caab24ffa65875527fb20c3aa93fe99619549fec9b0caa4ff661765535fd11332a9afd8799954d7ec1cccaa6dfa2175553cfcccbaaa977d905d554bbf4cacaaa6dfa2165552efb2eb2aa9e7d7659554bdf4cae8aa6efa2174553b7aecba2a9ebe665d154f9eb2ae8aa4ff26277913b7ceeba489f3e555d244bdec9ae9225ef65d54913e7aeaaa4897bd9355244bdec910f225ef64487912f79313bc89dbc989de44bdf4caed2276f9dd76912f7b26bb489ebe7799a44f5f332eb225ef64175912f7d32b2c897bd9759644edf3bacb227af5d965912f7b26b2c89f3d7695644bdecb9052276f9dc82912f7b2a41489f3e5520a44bdec8905225ef65c81913b7cee40c897bd9320644bdec9103225df656885c67fb2d442e3b7d95a21719fecad10b8cff652885c67fb27442e33fd92a21719fec8510b8e7f602775c75f931332e3afe8899971e7f3bcccb8ebf60e665c75fb01332e3b7e8821571dbec310ab8f9f998855c73fd10baae3cfe665d571bbe4c4aab8edfa22555c7cfccd2aae3b7c8561171ddec2108b8df764c845c7afaeaaa2e33fc9891171dde4c488b8eefa22445c7b7cef222e3ebe6691171f9e42c88b8f6f5d6445c7e7cab222e3bbd8391171fda48c88b8eef602445c76f90ac12e3bed8220971bfcc8104b8cff261425c75fb28c30e3afd92618719ff4cb0838ebf999841c67fb30b20e3afd8659071d7ec348838eef612441c777b0d220e3ebe66910719ff4cb0438ebf999821c777c88c10e33fd9850871d7ec328438eef611421c77db04a10e33fd9810871bbeca88438cffa65875876f92ac3ac33fd9361d619fec830eb0e7f61e775873f9313bac39fe889dd61cfec1ceeb0e7f60277586dfd32bb2c3afe885d961e7f3baecb0ebf60d76586dfb20bb2c36fe9959561d7f442cab0dbf65d655875fb0eb2ac3cfe7759561dbf444aab0edf61e55587afcef2aac3e7d7695561dbec1caab0f3f5d974587cfacaaa2c3bbe8891161ddec3c88b0f6f9de44587d7aed222c3ebd6591161f9f2ac88b0eef60e44587cfacaa92c33fd985c5619ff4cb0ea8cffa65865473fceec32a33fd93619519fecc2eca8ebf619765475fb0f332a3cfe7799951d7ec1ccca8eef61e44547b7cef222a3bbd8691151f5f33488a8eef60e44546efd32a92a3d7e7754951dbec32a4a8f9f99952547e7c88a92a3b7d83549519fecc084a8ddf65442546fed32b8aa3ef6665c551fdb2)) else (if i<5 then (if i<4 then 0x44a3c28dca2a2894a10282c9fe27e49ec277c9d227149c026ec9b626a499c265c98a25d497025ac966256494c251c9322494920244c90e24048f4239c8da23548c022ec8b622a489c221c87a21b4868214c84e2104834209c82220548101fec7e61f447bc1ebc7aa1e947a01e6c7961e4478c1e1c7821df47781dcc75e1d647441cfc7321c947181c2c6f61ba46dc1b3c6c21ab46a01a6c68e19e467419bc66a197465018ec63618a4624183c5fa17d45e8174c5c616e45a4165c58a15f4578158c5561524534149c51213f44e8134c4c613044b4129c49a1254490122c47e11e446c119c4621174458114c43e10e443410bc4120fd43d80f0c3ae0dc43540cdc31a0bb42d00acc29609e425c08fc22208141f0070c1ae064417c057c142049410803ac0be0284084019c04a00b4000bff4cacaba6ffa21655d2ffb2440ae9bfd8120574bfec82eab25ff648845c77fd10b22e3f7c8559171efebaac8b8dff64d645c77fb06b22e3bfd8059171bfeca104b8effa21425c7ef90aa12e3fbd6450971bfec8284b8eff601425c77fac8c10e3bfe4460871dff444eeb0eff60e775877fb013bac3bfe885d561dfec1aeab0dffa65745877fd10ba2c3efd765d161f7eb2ae8b0dff64d745877fb06ba2c37fe9955161dff442a8b0dff65d54587dfaecaa2c3f7d7555161fdeba2a8b0dff64d545877fb06aa2c3f7d5454961f7ebb2e2b0dffa6576546ffb20bb2a37fe995d151dfec32e8a8f7f5d974546ffb20ba2a37fd9759151dfec3ac8a8fbf5d964546ffb26b22a3bfd8359151dfec1c88a8dff64162547efaeca92a3f7d7454951fbeb22a4a8fdf91152546ffd32a12a3bfd8750951bfecb284a8fbf25942547f7ac8a12a37fd9350951dfec1a84a8dff64142546ffb2e212a3ff5645c551ffab12e2a8ffd50971546ffb2443a837fd935d941dff442eaa0eff619755077fb06baa837fe9959541dff442caa0dff65d655077fb0eb2a83efd7659541bfec9acaa0eff60d65506ffb2e41283bfe885c941fdeaa2e4a0dff641725077fb00b9283bfe8858941bfecbac4a0eff61d625077fb0ab1283fbd5458941dfec1ac4a0dff65d52506ffb2ca9283f7d6554941fbeaa2a4a0dff64d52507f7aeaa1283fbd6550941ffab2ae2a0ffd58971507dfaecb0a83ff57558541ffab92c2a0eff9dd82106ffd32b2a43bfe8859521dfeb2b0890dff65c844877fb08422437fe995d121dff442e890eff61574486ffb20ba243bfd805d121dfecc0e890effa20744877fb003a243bfe8859121dfec3ac890eff615644877fb00b22437fe9955121dff442a890dff65d54486ffb2caa243bfd8655121fbebaaa890fdf59554487f7ae8aa2437fd9355121dfec1aa890effa22444877fb0b22243bfd8391121dfec048890fbf5d961487feceeb0a43ff57558521ffaba2 else 0x2262b195a3137cfc142fe0ac64df0aa3022e2618597158c9be15465c9657f3f05d1df462d137440d0cf416d0073eccf7f3d2cf173b8ce6f37ecd6733cccbf322cc372f8cb8f2cecb072acca5f282c9b7260c90f236c88720cc7df1e2c7171a8c62f17ec5c7154c4ff12ac457100c3af0d6c3270b4c27f092c217078c1af05ec10702cc07f00abfd6fd8bf0efaebe86f94be1ef7abd96f58bd2ef2ebc46f04bbbeed2bb16eb0ba6ee7eb986e4cb8fee32b856df8b78edceb706dacb61ed6ab556d38b4aecfeb386cccb2decaab256c80b1aec56b106c24b01ebf2af76bc8aeceb9eae46b7cad9eb52ad16b38acaeb0eabe6ae4ab1eab2aa96a90a9eea66a946a3ca89ea0aa7b69d8a72e9b6a686994a61e97aa596950a4ce916a3e68eca35e8c2a2d68a0a22e876a1a685ca11e832a0968109fee7e69f267b49e9e7a29e567909dee7669d267349c9e7129c166e89b6e6c69ae66ac9a5e68a99d6668996e64e98e6624985e60a97d65e0972e5b696c65ac967e5929616570956e54694e6534949e5229456510942e4fe93c64e4937e4ca92f64b892ae4a69266494921e47a91d6468916e43e90a64148ffe3ea8f563c08eae3968e2637c8dbe35a8d163308c6e30e8c062ec8b7e2ca8b162a88a8e28689c625c893e24288d6228886e20688061ec877e1ca86b61a8862e176858614c84de12a84560f8838e0d683260bc829e09a8236070814e03e80a600c7fbdfd27ef5fb07e8df8e7e05f747d7df527d15f387cadf1e7c45f047bddee27b35eb87aade9e7a65e8479bde5278b5e20782de0677c5ddc775ddc276b5da0760dd6e7585d5474fdd2a7475d18742dcfe73e5cec739dcda7335cb8728dc8e71e5c6c715dc3a70b5c18700dbee6f45bbc6e9db926df5b686d4db3e6c85afc6bbdae26b75ac06aada966a25a7c699da5a6935a38688da1667e59e4675d9c266d59a0660d96e656594c64bd91264158f0638d8ce63058ac627d89261d5860612d836608580c5ffd7ea5f757c85ead7a65e257745d5d74a5cf57285c4d6fe5ba56d45afd6b25ab56985a4d68659a565c593d64a58d5620582d5f657855cc571d5b2567559055ed566556554c54fd52a54554f8538d4ce52e54a4523d47a51b5460514d43e50a54144ffd3f24f953c84ecd3964e053644d1d3324c553004bad2de4b252bc4abd2aa4a75280496d24648c5224485d21247d51d846ed18645a5134445d0fa43750c842ed0ae4265094421d08241d5070418d056412503c409d0123ff4fe83f2cfb63e84f843dbcf5a3cf4f283c2ced63ae4e9439fce6a3954e4038ace0e37c4dd436fcdaa3674d8835acd363484d0433bcce23374cc0328cc8631a4c4c30dcc1a3014bf82fccbee2f64bcc2edcba22e34b802dacb5e2d44b442cbcb1a2c14b002bccaee2b64acc2adcaaa2a54a8829eca6629) else (if i<6 then 0x3010010004002161070c101040821e06003020900181000808304081a02307040118004818c240c4f017908301080821214e2610484082041020bc05e420a1050830488182440c0a2090810400c0424e2617c05848c2c18241481214602101180848c0a2027130824144a010912031848288142f01030910104880c20050818400a1002841431c0a20e05107028a38144f01130510385828c0c206042860310309082c2800600142000910902880de04081420a001003c880c480062a2406004780bc841f21400303001002a880020014b0010004002140028b0013c042c1848604122000802a8a2c2160020c05001c580082c004f010b070018584828c00296002950a580092c296002000800418140060c002860010280081400400aa28b085800a2c216002f90a12180141c2861c0a2151205180040031c0020e001070008380041e0028e0013c0401800203c842c18486001000800800404002061210109080c4840c002000090a18004f0112031090009e4200100081090808004160012312091040008480042412209001018089e020210308201880c0441a1820c0910485e020c140630b0310b85018c08304120a02309040118902880c0034600f22130513c0404144181090809820a180030c0b08002058008022c4f01790802c18006081a02303010c1959304828180181804486564c120a060060b030018185800c14340060016200086040d184009080142026095842421210902107048814244121020200091858488483041606003090010480099834006120a2030d001aaa7090604829850340061c04120a40905104828824144120a2090510284818e9814246240a1230900102a7080c3168c20a09051cac7090604829824144cc0a1230503101840080224307010518380828c1c041460e020a3120510380828c280040010001c30404112051060488481441410d0c113065432a1260311701889808400f080b91841e1001514a84ac0045612b0958008b8004064c20048400056202304000100081040c2000000200100104ac004000014204101301081420010800c212100080840560020000020010026101040020260010000200100080002026001158008980044c002000800000000000000130188056002001841c2041260958108b824c1b808184980c4001000049808400002420a1260310014202b05115828800a1260310004242005c2b00800400202b0015804242560022b095800898004560022b001008400612608604000170405c10000002a97080000145c30c1be498617f09630b2e17c1a8bc01be417e0480ce062a0c30295861812aa30c2c2be04800a2f2b1630b958b1874ac70c39553861caa9c30e4e55187474a8c3a3a546044c22b2602f9f82ca93089be2547f056202262b18115930c08ac98604564c30 else 0x1001008008040042a17908882818c040040a062460bc05e02f211405001d801800c4ac0140c9ac18043790bc84040040200203001413c09e420806226781000488040040410805031bc0499e040012203051000508140800608001230503021bc05e0224141232602101800801e440200201091048409e4202002010010285e02f01780bc843108246271c209089848814005601200313001048008202f01780bc84040c4001020b801800fe41c006f01030012582000de0200122050010005048c242000612002780bc07e41c0c770060030305125bc89e421200226000a09206a3048c34244248c0a3780ca9302850194142824600122150a13c0448144120a2030510100082428412040032e0c09180018820144100a2080910180880420200201001008009e42f212608906860cade44020020100461808009e4206002030510200083414400062260411584840c98140c606f0278080800804004f017908784ac004120422b090019584800c0c040069c155791018009e031ef2201001050009e02f2101001028089e0200022030110182881c0c04600f22000800020120510902880c04486120a2000820009e42120a00378084828800200102001000408004f21000800408144060a200080040c00404002000510080080000080044424c00226021130108002000080082000184142041013010814200008014208b0800400a18b08302818c241440a062050310182880de04020a200791030188082061460a30189180c40a0621203101840c30c06203083018802b5c24300882818c540c4060020008185183ac1030a3018808c062000a301881aac0c601405121848288040041a122010010004040040402)))
def g1007l9 : Packing := (740,3,5,7,1,14,0,g1007d9)
def g1007d8 (i : Nat) : Nat := (if i<1 then 0x1840000204101840000002000040000800212080c002048004000800000002000000000000000000000000000000000006100002001840000040000000008000000003080000080000000000000cfb30caf1dc6313c3b00beef6bc6ecb9ee2b76d8b4eceb26c4afebaad6b0aaea6a869ca5e92a3688a0e759c2629765894e4e902328b62888e15842027f5ef785d36f1a565d926358860d755c16b59961571575494d521434f9394d12f4a9254811b4591143107408fd3e0f33b8e036ccd320ba2d4b02889d26093238891ec761c46c19c621744f128450dc320b42808c1e0641403c0a01400adf6968859171adf6968850971f2f5d97455161cf764d83551619bf69a9950951afe682885d541afe6828859541afe682885c941afe6828858941cdfa21951d121cdf60d951d121cdf601951d121cfe6a1901d121cfea21901d121cfe60d901d121fd95515258521cdfa65855d021cdf64d855d021cdf641855d021afeaa97460021afe6a57460021afe68d7460021abd6989260474add6949260474af568c9260474afc6809260474f0f5d9655d154f0f9de66956449eeaa99020a44d6e9dd9020a44dce9559020a449afaa99620644d2f9dd9620644a9f6968899971c9f2626695571acf6968891171acf2a25591171aafaa98691071c9f61995108718df6969961d61a7768c989dd618df2a587955618fe68d90a21418df6969961d418fe6829961d41a7e682889dd418fe6829961941abe68288999418fe6829961541ade68288955418df2a58795541f4d5d5545c541f695c9425c541f8d5955458541fa95894258541c77a667760c41cf660d901c8418bf69a99611218fe68299611218bf2a66661121f995955258521aaf6989761021acf6949761021ae768c9761021aee68097610218df6a5851d021c9f659851d021caf659841d021ccf655841d021c7d61d911d021cbd619911d021cdd615911d021ced611911d021c7e61d901d021cbe619901d021cde615901d021cee611901d021a6faa98791021e4f9dd85910218fe6a47460021abe6987460021ade6947460021af668c7460021afa6887460021afc6847460021e6e9de44600218df694989de11a5f694989de118fe6809891211aee68098912119fcaa99021e119dd694989de11b5d694989de11b5d694929de119fc680985da11bbc6808799a11f1d9de66956119ddaa99521211d5d9dd95212119f9aa9921d2119fc6809891211bec6809891211bec6808791211f2d9de6691211f4d9de5591211f8d99a5591211bec68092912119f568e995ca119fcaa9901ca11dec911901ca119bd69a9950a119bd2a66650a119ddaa99510a11d5d9dd9510a11f9999a5588a11bf168c9488a11bd96948488a11bd96947488a11bf86807488a11f699de4488a11fa999a4488a11fc99564488a11 else 0x360101e020003701000000000000000000000000000000000c2)
def g1007l8 : Packing := (122,4,5,1,1,10,0,g1007d8)
def g1007samples : Array (Bits × Bits) := #[(0x2a09052e62a50400441e21420a590e18c49054120a5cc54a0800883c428414b21c318920a82414b98a94100110788508296438631241504829731528200220f10a1052c870c62482a09052e62a50400441e21420a590e18c49054120a5cc54a0,0xa0901a622850400441401021a580f1884101412034c450a08008828020434b01e310820282406988a1410011050040869603c62104050480d311428200220a00810d2c078c42080a0901a622850400441401021a580f1884101412034c450a0),(0x20e853034871f946c6cce63349808c086b2241d0a60690e3f28d8d99cc6693011810d64483a14c0d21c7e51b1b3398cd26023021ac890742981a438fca363667319a4c04604359120e853034871f946c6cce63349808c086b2241d0a60690e3f,0x24c012115470f1c6824a262160828007620249802422a8e1e38d04944c42c105000ec4049300484551c3c71a09289885820a001d88092600908aa3878e341251310b0414003b10124c012115470f1c6824a262160828007620249802422a8e1e),(0xda663d1023ce09089971c84c95b281a49c21b4cc7a20479c121132e390992b65034938436998f4408f38242265c7213256ca06927086d331e8811e704844cb8e4264ad940d24e10da663d1023ce09089971c84c95b281a49c21b4cc7a20479c1,0xc8242d02038c0808098088c8953441a00c3590485a0407181010130111912a688340186b2090b4080e3020202602232254d1068030d6412168101c6040404c044644a9a20d0061ac8242d02038c0808098088c8953441a00c3590485a0407181),(0x1542e0d19d12224f0161140d14061101130a2a85c1a33a24449e02c2281a280c22022614550b83467448893c05845034501844044c28aa17068ce89112780b08a068a03088089851542e0d19d12224f0161140d14061101130a2a85c1a33a244,0x1542c0599c022246006914040002100153022a8580b33804448c00d2280800042002a604550b01667008891801a45010000840054c08aa1602cce01112300348a0200010800a9811542c0599c022246006914040002100153022a8580b338044),(0x0,0x0),(0x4d070669856c9870227e07c0660302d203b09a0e0cd30ad930e044fc0f80cc0605a40761341c19a615b261c089f81f01980c0b480ec26838334c2b64c38113f03e03301816901d84d070669856c9870227e07c0660302d203b09a0e0cd30ad93,0x45824619916888600aeb04c0a58300c001a08b048c3322d110c015d609814b06018003411609186645a221802bac1302960c030006822c1230cc8b444300575826052c1806000d045824619916888600aeb04c0a58300c001a08b048c3322d11),(0x92404d8b0e4c800380187080586400a5c60124809b161c9900070030e100b0c8014b8c024901362c3932000e0061c20161900297180492026c587264001c00c38402c320052e30092404d8b0e4c800380187080586400a5c60124809b161c9,0x20bc84c890e0c00218010d48218050885c404179099121c1800430021a904300a110b88082f21322438300086004352086014221710105e4264487060010c0086a410c028442e2020bc84c890e0c00218010d48218050885c404179099121c1),(0xc64088c0ec83f7003c00078108600064c64b8c811181d907ee0078000f0210c000c98c9719022303b20fdc00f0001e0421800193192e32044607641fb801e0003c0843000326325c64088c0ec83f7003c00078108600064c64b8c811181d907e,0x125980c06c0377043400033108480815c24a24b30180d806ee08680006621090102b849449660301b00ddc10d0000cc421202057092892cc0603601bb821a0001988424040ae125125980c06c0377043400033108480815c24a24b30180d806e),(0x11492a4729977ffc0001801f07c7887084c02292548e532efff80003003e0f8f10e109804524a91ca65dfff00006007c1f1e21c213008a4952394cbbffe0000c00f83e3c438426011492a4729977ffc0001801f07c7887084c02292548e532e,0x883410a26291518910002a295864e806080910682144c522a31220005452b0c9d00c101220d042898a4546244000a8a56193a018202441a08513148a8c488001514ac3274030404883410a26291518910002a295864e806080910682144c522a)]
def g1007columns : IndexTree ColumnInfo := (.fork 13 (.fork 6 (.fork 3 (.leaf [(385,32,78,0,4),(417,0,78,0,4),(384,0,623,512,7)]) (.leaf [(104,256,135,0,4),(360,0,135,0,4),(266,64,165,0,4)])) (.fork 3 (.leaf [(328,0,167,0,7),(268,0,227,0,5),(192,0,815,512,7)]) (.fork 2 (.leaf [(37,128,330,0,4),(163,0,332,0,4)]) (.leaf [(161,0,334,0,7),(138,4,353,0,4)])))) (.fork 6 (.fork 3 (.leaf [(142,0,353,0,4),(140,0,355,0,7),(130,0,877,512,7)]) (.leaf [(128,0,879,512,10),(96,0,911,512,7),(69,2,424,0,4)])) (.fork 3 (.leaf [(70,0,937,512,5),(68,0,939,512,7),(67,0,428,0,7)]) (.fork 2 (.leaf [(64,0,943,512,10),(40,0,455,0,7)]) (.leaf [(8,0,487,0,11),(1,0,494,0,11)])))))
def g1007autos : Array (List Nat) := #[[],[48,33,133,118]]
def g1007levels : Nat → Packing
  | 8 => g1007l8
  | 9 => g1007l9
  | 10 => g1007l10
  | 11 => g1007l11
  | 12 => g1007l12
  | _ => emptyPacking
def g1007index : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 721 2164 6 15 10 1 (g1007key10)
  | 11 => lookupWord 219 657 6 13 8 1 (g1007key11)
  | 12 => lookupWord 16 53 3 10 5 1 (g1007key12)
  | 8 => fun _ => none
  | 9 => lookupWord 119 357 5 12 7 1 (g1007key9)
  | _ => fun _ => none
def g1007 : Forest := ⟨1007,12,fun j => g1007samples[j]?.getD (0,0),g1007columns,g1007autos,g1007levels,g1007index⟩
set_option maxHeartbeats 0 in
theorem geom1007 : graphValid g1007 (boundsBefore known879) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_12_0 : block g1007 12 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl1007_12 : block g1007 12 0 1 = true := s1007_12_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_11_0 : block g1007 11 0 3=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_11_3 : block g1007 11 3 15=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl1007_11 : block g1007 11 0 18 = true := (@block_merge g1007 11 0 3 15 s1007_11_0 s1007_11_3)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_10_0 : block g1007 10 0 17=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_10_17 : block g1007 10 17 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_10_53 : block g1007 10 53 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_10_89 : block g1007 10 89 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_10_125 : block g1007 10 125 3=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_10_128 : block g1007 10 128 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_10_164 : block g1007 10 164 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_10_200 : block g1007 10 200 30=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl1007_10 : block g1007 10 0 230 = true := (@block_merge g1007 10 0 200 30 (@block_merge g1007 10 0 164 36 (@block_merge g1007 10 0 128 36 (@block_merge g1007 10 0 125 3 (@block_merge g1007 10 0 89 36 (@block_merge g1007 10 0 53 36 (@block_merge g1007 10 0 17 36 s1007_10_0 s1007_10_17) s1007_10_53) s1007_10_89) s1007_10_125) s1007_10_128) s1007_10_164) s1007_10_200)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_0 : block g1007 9 0 35=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_35 : block g1007 9 35 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_71 : block g1007 9 71 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_107 : block g1007 9 107 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_143 : block g1007 9 143 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_179 : block g1007 9 179 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_215 : block g1007 9 215 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_251 : block g1007 9 251 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_287 : block g1007 9 287 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_323 : block g1007 9 323 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_359 : block g1007 9 359 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_395 : block g1007 9 395 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_431 : block g1007 9 431 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_467 : block g1007 9 467 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_503 : block g1007 9 503 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_539 : block g1007 9 539 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_575 : block g1007 9 575 8=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_583 : block g1007 9 583 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_619 : block g1007 9 619 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_655 : block g1007 9 655 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_691 : block g1007 9 691 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_727 : block g1007 9 727 13=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl1007_9 : block g1007 9 0 740 = true := (@block_merge g1007 9 0 727 13 (@block_merge g1007 9 0 691 36 (@block_merge g1007 9 0 655 36 (@block_merge g1007 9 0 619 36 (@block_merge g1007 9 0 583 36 (@block_merge g1007 9 0 575 8 (@block_merge g1007 9 0 539 36 (@block_merge g1007 9 0 503 36 (@block_merge g1007 9 0 467 36 (@block_merge g1007 9 0 431 36 (@block_merge g1007 9 0 395 36 (@block_merge g1007 9 0 359 36 (@block_merge g1007 9 0 323 36 (@block_merge g1007 9 0 287 36 (@block_merge g1007 9 0 251 36 (@block_merge g1007 9 0 215 36 (@block_merge g1007 9 0 179 36 (@block_merge g1007 9 0 143 36 (@block_merge g1007 9 0 107 36 (@block_merge g1007 9 0 71 36 (@block_merge g1007 9 0 35 36 s1007_9_0 s1007_9_35) s1007_9_71) s1007_9_107) s1007_9_143) s1007_9_179) s1007_9_215) s1007_9_251) s1007_9_287) s1007_9_323) s1007_9_359) s1007_9_395) s1007_9_431) s1007_9_467) s1007_9_503) s1007_9_539) s1007_9_575) s1007_9_583) s1007_9_619) s1007_9_655) s1007_9_691) s1007_9_727)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_8_0 : block g1007 8 0 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_8_36 : block g1007 8 36 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_8_72 : block g1007 8 72 28=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_8_100 : block g1007 8 100 22=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl1007_8 : block g1007 8 0 122 = true := (@block_merge g1007 8 0 100 22 (@block_merge g1007 8 0 72 28 (@block_merge g1007 8 0 36 36 s1007_8_0 s1007_8_36) s1007_8_72) s1007_8_100)
theorem tables1007 : checkedTables g1007 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g1007 0 0 0 = true)
  · exact (rfl : block g1007 1 0 0 = true)
  · exact (rfl : block g1007 2 0 0 = true)
  · exact (rfl : block g1007 3 0 0 = true)
  · exact (rfl : block g1007 4 0 0 = true)
  · exact (rfl : block g1007 5 0 0 = true)
  · exact (rfl : block g1007 6 0 0 = true)
  · exact (rfl : block g1007 7 0 0 = true)
  · exact bl1007_8
  · exact bl1007_9
  · exact bl1007_10
  · exact bl1007_11
  · exact bl1007_12
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1007 : Lower (vars 1007) (graphGoal 1007) 13 :=
  lower_forest (g:=g1007) (i:=0) (hints:=13438558465) (before_sound known879 valid879) geom1007 tables1007 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps1007 : List (Nat × List Nat) := [(1007,[])]
def known1007 := extendKnown known879 13 maps1007
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1007 : Known known1007 := extendKnown_ok valid879 low1007 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem apartLower : Lower (vars 1023) (graphGoal 1023) 14 :=
  lift_ok (ms:=fixRows 16 0) (xs:=[(inputs.getD 4 zero,1,17)]) (by decide +kernel)
    (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low1007
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem seedSlice : Slice inputs graph (~~~seed) 14 :=
  slice_correct (ms:=[(zero,seed,9)]) (base:=vars 1023) (G:=graphGoal 1023) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide +kernel)) apartLower

theorem completedRoots (deadCase : Impossible graph 14 inputs.toFinset) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 3)) →
      PEqualNP.MetaComplexity.circuitFun 9 C = edge → 16 ≤ C.size := by
  intro C legal first h
  by_contra! small
  obtain ⟨k,t,hk,hdead | hlive⟩ := initial_live C legal first h (by omega)
  · exact deadCase k t hk hdead
  · have noRun := poolCut_sound seedSlice [] (by rfl) (ws:=inputs++[seed])
      (by decide +kernel) (cap:=14) (by decide +kernel)
    exact noRun k t hk hlive
theorem dead_start {prior : Nat → Nat}
    (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid dead prior=true) (checks : checkedTables dead 14) :
    Impossible graph 14 inputs.toFinset := by
  have noRun := root_index (g:=dead) low geometry checks (k:=14) (by decide)
    (i:=0) (ws:=inputs) (by decide +kernel)
  have tgt : targetOf dead=graph := by decide +kernel
  exact tgt ▸ noRun


-- Generalized root-preservation and initial-live extraction for any seed s = x u && x v
theorem all_roots_gen {k t S} {s : Sig} {nbr : Fin 9 → Nat}
    (wit : ∀ i : Fin 9,
      let ar := Fin.ofNat 512 (1 <<< nbr i)
      let pr := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< nbr i))
      (bit ar graph != bit pr graph) &&
      ((inputs++[s]).all fun w => w == inputs.getD i.val zero || bit ar w == bit pr w) = true)
    (h : Live graph k t S) (sub : ∀ v ∈ S, v ∈ inputs++[s]) :
    S=inputs.toFinset ∨ S=(inputs++[s]).toFinset := by
  have all (i : Fin 9) : inputs.getD i.val zero ∈ S := by
    have cut := wit i
    simp only [Bool.and_eq_true,bne_iff_ne,List.all_eq_true,
      Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at cut
    apply raw_required h _ _ sub _ _ cut.1
    exact fun v hv hne => (cut.2 v hv).resolve_left hne
  have needed : inputs.toFinset ⊆ S := by
    intro v hv
    have hm := List.mem_toFinset.mp hv
    rw [←input_list,List.mem_ofFn] at hm
    obtain ⟨i,rfl⟩ := hm
    exact all i
  by_cases hseed : s ∈ S
  · right
    ext w
    constructor
    · exact fun hw => List.mem_toFinset.mpr (sub w hw)
    · intro hw
      have hx := List.mem_toFinset.mp hw
      simp only [List.mem_append,List.mem_singleton] at hx
      exact hx.elim (fun h => needed (List.mem_toFinset.mpr h)) (fun e => e ▸ hseed)
  · left
    exact Finset.Subset.antisymm (fun w hw => by
      have hx := sub w hw
      simp only [List.mem_append,List.mem_singleton] at hx
      rcases hx with hin | rfl
      · exact List.mem_toFinset.mpr hin
      · exact False.elim (hseed hw)) needed

theorem initial_live_gen (u v : Fin 9) (s : Sig) (nbr : Fin 9 → Nat)
    (st : ∀ r : Row, bit r s = (sample r u && sample r v))
    (snz : s ≠ zero)
    (wit : ∀ i : Fin 9,
      let ar := Fin.ofNat 512 (1 <<< nbr i)
      let pr := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< nbr i))
      (bit ar graph != bit pr graph) &&
      ((inputs++[s]).all fun w => w == inputs.getD i.val zero || bit ar w == bit pr w) = true)
    (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (first : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y u && y v))
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) (small : C.size ≤ 15) :
    ∃ k t, k ≤ 14 ∧ (Live graph k t inputs.toFinset ∨ Live graph k t (inputs++[s]).toFinset) := by
  have headEq : (execute C.gates inputs).getD 9 zero = s := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal 9 r).trans ((first (sample r)).trans (st r).symm)
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal C.output r).trans ((congrFun computes (sample r)).trans (edge_table r).symm)
  have out := get_rep (execute C.gates inputs) C.output
  rw [goalEq] at out
  have targetIn := out.resolve_right (fun hn => hn graph_proper)
  cases hgs : C.gates with
  | nil =>
    rw [hgs] at headEq
    exact False.elim (snz headEq.symm)
  | cons g gs =>
    have eq0 : gv inputs g = s := by
      rw [hgs] at headEq
      change (execute gs (inputs++[gv inputs g])).getD 9 zero = s at headEq
      obtain ⟨l,hl⟩ := exec_extends gs (inputs++[gv inputs g])
      rw [hl] at headEq
      exact headEq
    rw [hgs] at targetIn
    change graph ∈ execute gs (inputs++[gv inputs g]) at targetIn
    rw [eq0] at targetIn
    have tailLegal : ∀ gate ∈ gs, gate.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ gate.inputs.length≤2 := by
      intro gate hg
      apply legal
      rw [hgs]
      exact List.mem_cons_of_mem _ hg
    obtain ⟨k,t,S,hk,run,hs⟩ := extract gs _ tailLegal graph_proper targetIn
    have len : gs.length+1 ≤ 15 := by simpa [Circuit.size,hgs] using small
    refine ⟨k,t,by omega,?_⟩
    rcases all_roots_gen wit run hs with h | h
    · exact Or.inl (h ▸ run)
    · exact Or.inr (h ▸ run)

def clipBy (m : Sig) (r : Row) : Row := if bit r m then 0 else r
theorem clip_general (a m : Sig) (origin : bit 0 a = false) :
    rename (clipBy m) a = a &&& ~~~m := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let r : Row := ⟨j,hj⟩
  change bit r (rename (clipBy m) a) = _
  rw [bit_rename]
  have e : (a &&& ~~~m).getLsbD j = (bit r a && !(bit r m)) := by
    simp only [bit,r,BitVec.getLsbD_and,BitVec.getLsbD_not,hj,decide_true,Bool.true_and]
  rw [e]
  by_cases h : bit r m=true
  · simp only [clipBy,h,ite_true,origin,Bool.not_true,Bool.and_false]
  · have v := Bool.eq_false_iff.mpr h
    simp only [clipBy,v,Bool.false_eq_true,ite_false,Bool.not_false,Bool.and_true]

theorem seedSlice_clipped (s : Sig) (h0s : bit 0 s = false)
    (hp : proper (graph &&& ~~~s))
    (lower : Lower (inputs.map (fun a => a &&& ~~~s)) (graph &&& ~~~s) 14) :
    Slice inputs graph (~~~s) 14 := by
  have gg := clip_general graph s (by decide +kernel)
  have go : restrictRows (clipBy s) (observe graph) = observe (graph &&& ~~~s) :=
    (observe_rename _ _).symm.trans (congrArg observe gg)
  refine ⟨clipBy s, inputs.map (fun a => a &&& ~~~s), ?_, ?_, ?_, ?_⟩
  · intro r
    by_cases h : bit r s = true
    · rw [clipBy, if_pos h]
      simp only [bit, BitVec.getLsbD_not, Fin.is_lt, decide_true, Bool.true_and]
      simpa only [bit, Bool.not_false] using congrArg Bool.not h0s
    · have e : bit r s = false := Bool.eq_false_iff.mpr h
      rw [clipBy, if_neg h]
      simpa only [bit, BitVec.getLsbD_not, r.isLt, decide_true, Bool.true_and, Bool.not_false] using congrArg Bool.not e
  · intro a ha
    have orig : inputs.all (fun w => !(bit 0 w)) = true := by decide +kernel
    have z : bit 0 a = false := by simpa using (List.all_eq_true.mp orig a ha)
    rw [←observe_rename, clip_general a s z]
    exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem ha))
  · rw [go]
    exact observe_proper hp
  · rw [go]
    exact lower

-- Orbit 1: (0,1) restricted tables (from L_meta_1667)
def hashr01l13 (i : Nat) : Nat := 0x3266d629c3000cc09800002c5a916a703a921aa561d5132e8d2800000381db0ef80ad078788712ce0036333c001b9c02082090848
def hashr01l12 (i : Nat) : Nat := 0x62203295be14261132f30f3f1b40f70c8570ea66463a299d46c1ba2855693691546f740aeb454505f848713832723d0330abaef704500000000000000000002246c7f88ca8ddb1706419d9dfb457c0dd31f15082e0960004df3cf70400398003d17a2e309f11f451c7ee3c12b621bf3c50e3a1244b5ac092482789280c6564dc983c8302b1b20b118a5000015fc042239f2935ba13ff30f307a60f4e277ab838768f4897601ade5b3cc02721800000040b41f3cd8ce1d764963e1314d739b00162400126810b794f6be00053524d7cba0002ad8002c0325551ae8fc431233c90982be9e00000000034280009902110cb80007548254000000f1d800124d8a5e47463801066bfc798d0000b73042ca022e292214900000004943bd408c0000000005cc584c000c8b8002534e7c000622267486115380024940580007aa1947a4c4a8696fd33d25c0d7104063e0ecbc168c6eab8544eeabead2c83731524e6b306c0d0e1c4a7181079a312f870459c1949b742b43a40fe50dc8574d5a519b98ac54ed289cdc149c2f696baac46c504797113ed0d22df2d4cbc0010484160000231227702a9c9c08c67c09295f541c2a112421e513a8f00011e703768da14b1f5e046066c37470001c9cc81a1a4000000510127b5220000000000d36c76a3a000140e000bcd80000011496038b063a005800610001005489e36724000a60786185c2900f1439b5a08b00124c018022858000b4043180008626004825c0c3870a0401806148870c0c2800a1c3000204301042c184
def hashr01l11 (i : Nat) : Nat := (if i<1 then 0xc1b5add011e81124450c3ea5c13b407274e85915c39d0c00d88150e791cb40c5ed0c9bc327aa27eaf919d389c944f96acc45d60131309832800061abc19ca1a4c1d63eea14d209bd4671f0d0b02441110c09b33efc4f51da0000b07025cc9514b49258c00031997106d7b9cd81924a9f310828f818760000e191c99000000000003c6748ccd83f61af88250ca20c7406f80b840f38420000000618f13b1c0566de0000e0c0f76ea068c9f000000000000000b08f84d10dfb9e83925f70bca615e2916002e24fa61bb0372c1d143f64027237829967ee939f3dee31c00000e3f34eb15d470c5b700000003c68d44dc92200014ab7042d2b40002c5ec1ff9a2ec6a9e74800083ceb3624fb000061a6c4ac00059eef16e8007671adcac30eb5bd44cb886a986177d43778cf48a98407230706a6381a2a4e0870d21b38c202425f0cdc306c2712be900000018364000007f2891b2c60fdf0b1a1cd902ce4381890000855c08ef965c0cc21740a2f4a348d6e07a85f392de2e6000149d2d3c000144d5e0630336149c066c3cd9e95ad1b67f882f84c000b65da09869a8f057d379cd3000000002510000140453188564caf59619bc2000369a8000c22253d988b398a005575548da85f7716bc3218e73813c182a76446dd8bf43ba17b6c90096b702db0228032040c0c46358cb8bc47313502614e601de5b0da634c5098b3d23e76a7ce32992c358a4312add05b207d43b38d0dd44437a8171cfed8fee80cc26d4ca95887173c2ca02fb9afe15dc41d44ec075e091c7240149046b82904568723010ba66a4ba894c0456ab1c6db691e07c012216d5cc7716e489624da25f10c3c24324eea150da582970791c75507ab0d0516b857f474403ec610805485443c005e6ceb945c12a7e10e8113db9f2db12a8ca42cb503e6e25842b8da6d070768b8c409b113c3201f6cec1500369116ee5dcc944a3b4074c6b8968081c2034cd1d146a225225e894190a10d356ae8cb006f71f900334282c7f239bf02a25269a27017a59c0128832000041c02040080e1472868001f0095000440200c2e060a23e1e005200c0c055409c08522004856221b00800010195c12050880408001100434080d8d800061a01000260d84c0003100100400038ac1c0a0a0000409080440a022e0282057090000001028000a080007824001401400103284c4e0e0a02c0605000241603010201c1e008006225018000a080180c060509814027800018060a2000002061e00c00010080000161e014000100008cc10010000a01030080002020381c160703000080300002b8040086e0400020041a038003e00000000a000100c001a039241a07000402a7604800063c080001c004301c040f000300200098100600010200a000081000010180c0412060cc0200018040e08050000001068180000 else 0x489ce72c899bc2511f5c1598b925a35b9ae653cb109e5f402873f05291c33b2dd1ba2b6d9035bb923a18bec0ad407ba22110058442b66676ea4108c651182690038402ca031f4d80b491c40a3727d44a979ad13a17254c75e93ff0e4e65eef998f768124661089d034b11a87c7828f51a321333cb64b81be00b2129ac5a0170712a40b400000000001a53445400000001b4502d89885f28e923caf479d40000d3110c58c620001f240000753db8dbc4946fdf181221bd1bf8babcafc094d39843624b4f1bd94788e50000301f27058ba44660001d1c00001cbad8d40001cb7c9a0000112c9496087342b1e5fc000692a7a4184bc0003cb6104800008ce8000836e72b000000004ba957fac930000000000032f1d0c5f23803d80003cc7f335832c00041eb71de067000079ea03d822d80006835233dc7b4000503a49700000c4954b3e03560ee879104993000000ca4c8413189253f4d991d6d9efc5524075090b051280a447e014c0b40002c53d17800000003087800049dcf396a1f60ddc21ce1e00000000c184d3a800010e900000002470685e000000000fce531d04d437148021dfa8eb66e0885a4dcc079f0884aed1f8a07f03f400048a0c17702b26451117000023d544a295bd262b1104c298208b0682f2a90bc6c892731940004027c8c7e48b20da14a721000022af8000a0aba186c8304f34bf3d2f1010999f71ddc1630d934f49b00a6426e20000ba30000346f80002008000286d7464e2870608cd2f4bd0000000000079ba000016f80000000c1b0927000058c90000621f8bdd037d1e733d6e3ba082eb7a822fc11b17a4025122e838d138d3a5455745d7d272283a5b30a161e2fbc083eee308503f1f327572e1d893ab8060bf20f01f2f24f1236696b1c5c011c48ce4cc036ec0165a90e8d530a234e13e83da05241e285f24e4111831e1b51523991c2f327f39d252c456c941f6502004db6000187980000000b0ee948800000005357678ca7800000000c6b8c1c882ea0386539ecf301100000001cc8f1fcd38e83fde75ecf1abe2f41a87118c0000190aeec2f1fa000000020518000e2c9022a2c680007281149409be19b209c000000000006885379cc5500000233e3d1c4249a92102f5834c300000144561000064237b7e00024b30000193794a64558000f061f2c306a10d07278000222619776930d7158ee717e0000000062f800081daa581caffc2419bb1128eda70027a4975bb8ff388e6b8f)
def hashr01l10 (i : Nat) : Nat := 0x3152b8edb964ef3fc0c002b256fa5d1f878a5d56740ea51c00022340dc4b0003eac9d5d400034d790510dc3c33ad4d0068cfa54001d0b28349000000028fd024f40021a241478b668000000001477eb62bc002881a5da7ace99448e01871c5990982c65871cf9d2f86b194c5fc400c91340004a92c29a5821daad648c28861ca11953c15e698c6e253a761981b76a800224763097b968001588202eeaef5917ad12ca0445b0d624b699e17cca2e5869d4db060a6c71f89b576931cd3c481bc45192bcfecad02fcbbce7eb208fc78418c4ec10acc8584024ed827ad8c3689f94815a526513438b200000000034f2c1c91c00197045400023c0018bc002228c8ba964c4003c7f5ae16de0982a13b1cf40912358e097e240012c6831a900002189a4bd0790f1b806700364004104b99f041082101206060007acd0010810466420400010000c0002
def r01d9 (i : Nat) : Nat := (if i<1 then 0x1a30c230c230c020c23080128141000884160711871185118416842b0371056085608000a42010200000000000000000000000000000000000007800f800b8008000f001078008000078008000000000001e002000000000000000000388e0f7ede774dbf6ad9760d6f56d4741cf32cc7317c4b0dc2303bfaf9bd2efbaae5b56c5ad6a5a56909d6709825090230882107d5e5755d072dbb6ada66859c65d926358860d7e5e5745bd6a5956056d565454c51d424f5384cd2e4a52447d1a455053d4e5380db358c6304b12b0a72889d2348820c7e1e4741bc6a1946016c4b118410f0370c82d0a023078190500f028050029ff5da70cc04f4ffaed3a66027aefd769c32a13f57d784e19509e3ff5db50c984f5f7aed3864c27ebbaf09c32613d7debb6a19309faeebc350c984f5fdaed3846427ebeaf09c23213d7fabb4e10909f5ee9c35014a6b57faed3825d258ffb704d26e92e5fda825c394972febd2714ca4b1ffaeda864c25f3daf0942ae91fdcd784a13748fde69c2509aa474ffaed5866023a7fd76ad33011d5febb5619708ebfb5dab08c8475feaed58424238ffb7054a6b1155ecb7695290e2abf5daf0ca84f577aed7864c27cbbaf15532613d5f6bb5e11909e6f75da541c4ef1fe42c9a5e135b79a564c2709ac5fc9b69c384962fedd0704ba4b56f6d03825d25abda561c12e92d5f90b0e097497da69c2509aa4b5d726d374d525fa9a6e93a6a92f55c970e535496ee6db874942477f146c3a4a123f39af09426e91c5fcab9dd9548e2febdd54caa4747f6dc5a66023a5fb6c2d33011d3dd3b1699808e9fa8d8b4cc0474fe42c5a660238bfb742c32e11d5dd3b1619708eabedb8b0ca84755f6dca865423acfb6c5432a11d75d3b2a19508ebb695950ca8475dd46ca865423aef2165432a11d5bdb71619408eb5edb0b0ca0475e74ec5865023af5a562c32811d5f5b71611908eb7adb0b08c8475f54ec5846423afca562c23211d7f10b1611908eafcdb8b0848475be6d85842423afb2762c21211c7f9ab1610908ebf4958b0848475fc46c5842423b3bb702ba6f19ddcd2b15d378ceeec858ae9bc673f3aed2a1623397bd76d40af19cbdebb6a0278cf6aebc34a13c67ad7a21a509e33dbaaf08d04f19ebd688468278cf5ed4421413c67a77a20a7496339bb9573ba4b19cddd7baa9258ce2febd9532ac4537baeda7226229f9d769d0b1114deebb69c3888a7b75db4a1c44573b6d8389de22badb6a1c4ef115dadb40e27788aef28d8713bc4577a42c389de229bdaf654cab115d6d7b2a65588aeb6db8752ac457da6c03a95622badb6e1c4ab115f2db40e25588afb4858712ac457736dc898ce22bf8b6244c67115dcdb71623388af66db0b119c457f146c588ce22bf92162c4671179ce889de3388bda7444ab19c45f539de558ce22 else 0x490802b042484000000000)
def r01l9 : Packing := (118,4,7,0,1,10,0,r01d9)
def r01d10 (i : Nat) : Nat := (if i<2 then (if i<1 then 0xefdd2a16233bf72a5288cfbdc894a233ff30a5288cefdeaa4a233ef75e1288cefdda50a233bf72a6888cfbdd78a2233ef7562888cfbdd28a2233ef72a6888cfbdc7aa2233ef716a888cfbdc2aa2233bf76a1578cfddd7855e33bf76a0578cefdda849e33ef7a21278cfddd7809e33bf76a0278cfbde8809e33bf72a6778cfddd789de33ef7a22778cfddca99de33f77226778cfddc8a9de33f77562778cfddd289de33f77a22778cefdca949633fd7165258cefdda849633ff34a1258cfbde8849633bf769d258cfddca749633fd755d258cffcd2749633f779dd258cefdeaa49633bf76a0258cfbde8809633b7f69c5888aefda616222bef5285888afdd3a16222bfb4a85888aff51a16222bfe4285888a7fca94e222efb4e12888a7fca9a2222efb4a28888b3fca9a22229ff2a53588afeda849622efba212588bf6d35496229ff2a65588bf6d2595622bfb6a12388bbee8848e22bfb6952388bfcd288ce22ef7a223388bfcd258ce22bfb6948988afeda322622bfb6a05988afeda316622bfb6a03988afeda50e622bfbaa97888afeca956222bfbaa95888bbed7856222bfb4e85888afeca94e222efb2253888afeeaa4e222bfb69c3888afeda50e222bfb2a68888bbed78a2222efb5628888bbed38a2222efb2a68888bbec59a2222efb0e68888bbec5aa2222efb0ea8888afeda855e22f7b5e15788bbee8855e22bfb6a13788bded784de22efba213788afeeaa4de22f7b5627788bded389de22f7b0e27788bdee889de22bfb2a53588bf6c594d622bfb6a13588bf6d584d622ff34e13588bbee884d622bfb69d3588bfcd374d622f7b9dd3588afeeaa4d622bfb6a03588bbee880d622bfb2a65588bf6d5895622efba225588bf6d3595622fdb2a65588bf6c8a95622fdb0ea5588bf6d3895622fdb0e25588bf6d3795622ff34e23388bbee888ce22ff34de3388bdee778ce22ff34d63388bf6e558ce22ff32263388bfcc598ce22ff322a3388bfcc5a8ce22ff35e23388bfcd588ce22ff31623388bfce888ce22ff355e3388bfce558ce2297faa9970e27eeaa4a4388ffaa99809f57d7865427d775e19309e7deaa64c27d7d5e11909edbda40e277b7b4a8389dedf90a0e27797f26a774965fd7aa65258ffaa99808e77eaa65423bf5468788ceddda716233bb7698588cefcd2a16233bf5468588cefd90a16233af76a0578ceedda615e33bf34a8578cefd51a15e33bf6428578cebdda809e33bb7698278cef5da509e33bf5468278cefd90a09e33e77a22778ceddca749633bb7698258cededa722622bf96848988adeda716222bbb6985888afad4a16222bf34e85888afe51a16222bfa4285888adeda70e222bbb6983888af6da50e222beb6903888afe51a0e222bfa4283888b9ee889de22f5b9de5588bbce888ce22f739de3388bf4e558ce22 else 0x7b7f69c3849eefda60e127bdf6943849efbda40e127bfb4a83849eff51a0e127bfe4283849edfeaa4dd27b7faa97809e7feaa66027cff4e19809f3fd3a66027cffaa99809f77d3865427d7f5e19309e7fda864c27df74e19309f7dda864c27dfd4e11909f7f938424279ff2a5389dedfda70e277bef690389defed2a0e277bfe428389dedfda84de77b7f6a0399dedfca94e277b7faa9389dedfd2a0e2779ff269784d73fd9826135b7f69c984d6efda626135bfb4a8984d6ff51a26135bfe428984d7f5c5a4e135bf7aa9384d7bdc984e1359ff269284d7bdd384a135d7f5e1974d67feaa65d35bf76a1374d7ddd784dd35bf7aa9374d7ddd3749d35f774e2774d6efda60a535dfb4a4294d67fd8aa65359ff5ea994d67fd2aa6535df74e2994d77dd37a6535d7f9de994d73fd984a0359ff6a1290d77ed284a4359ff26938496dfda70e1259ff6a438496fbda40e125bfb4a838496ff90a0e1259ffaa9974975fd3825d25d7f0e0974967fc9a4dd25f7b4dd27496dfc9a9dd25d7f25d394975fc970e525df74e439496dfd7aa6525d7f25e994967fd7aa6525d7f5ea994967fd3aa6525dfb49e994975fe77a6525fd74e135497f6d284d525bdf69d35497d7c974d525fd74dd35497f6d274d525f5f9dd35497f6c2a4d525bdfaa935497f5c394d525ddfa65354967fda864c25df74e1930967feaa661239ff6692848ffcc3a4a123bfbaa92848fbed784a123efb4e12848e7fda865d239ffaa99748fddd784dd23ff34a13748efdeaa4dd23d7f6627748fded289dd239ff6a19548f7ed28655239ff69d9548f5fca765523df74dd9548f5fe77655239ffaa99548e7fd9a49523dfb4a29948f7dd37a6523d7f9de9948e7fd9a160239ffaa99808f3fd5866023cff1619808f3fd5a66023cff1699808f3feaa66023d7f5619708f5fc5865c239ff6a19508f77d5865423ddf1619508e7feaa65423ddf6a19508f77ca865423ddfaa99508f7bd5865023def1619408f7f55846423dfd1611908f7f95842423dfe1610908e7fca95e233bf74e8788ceff51a1e233b7f69c588ceefda616233bf74e8588cefed2a16233bfd468588ceff90a162339ff2a5288cfbdd384a2339ff2a6888cfbdd38a2233aff6a0578ceefda615e33bf74e8578cefed2a15e33bfd468578ceff90a15e33bf76a1378cfddd784de33f7715d378cfddd3749e339ff2a6778cfddd379de33d7f2a6778cfddd389de33bf76a1358cff5d584d633bf769d358cfdde774d6339ff2a5258cedfca749633fd74d5258cefdda848e33ff34a1238cefdda748e33f779dd238cefdda548e33bf769c898cefdda522633bf7688898cefdda81e633bf76a0598cefdda216633bf76a0298cefdda50a633bf72a5788cfddc795e233bf7aa9788cefdca956233fd7165588cefdeaa56233ef75e1588c) else (if i<3 then 0x30e3d38b8e1f3840e0137c8de33750dc536d8da73660d8935e8d613548d4334d0d253458cfd33b8cdf3368cd53340ccb3318cc132c8ca33228c7b31b0c673138c3f3098c173048c0d3020c032ff8bf92fd0bef2f80bd12ee0b9f2e68b8b2df0b632d28b452cd8b272c38aeb2b20aa52a08a692918a2327d89e727389c926e8997262097925a8951250893324b891f246891524188f723a08d923288bb22b089d223887f2198857212083920a881b20307fd1fe07f31fb87e91f907df1f687d51f187ad1ea07991e0077b1db07671d887531d3873f1cc07211c206ef1ba86db1b086bd1ab869f1a6868b1a1868119f067719c866d19a064f1928645190063b18d863118b0627188861d183860918105eb17985e117705c316a8591156852314284d312e84a11220465109040b0fc83cf0ed839d0e1036b0d483390c582fd0b902cb0ac828f09d825d091022b08481ef07581b30668181057814504b011303e80e103200af025807d019004b00c80190002ffeaa5e538bffaa9294e37fd794a538dff565294e37fd590a538bff694294e37fd79a6538dff4a6994e37fc7aa6538dff0aa994e2ffd5a26137bffaa9384df7fd984e137f7f5e1384df7fd38a6537dff6693849effeaa4e127bff6943849fdfd384dd27dff6693809effeaa4e027f7f5e13809f7fd3a66027dff4e19809effeaa4e277bff4a8984d6ffeaa4e135ff75e9384d7fdc9a4e135ff74a9384d7fdc2a4e135ff7aa9384d7fdd384a135dff4e1974d6ffda84dd35f7f5e1374d7fdd384dd35bffaa9374d7fdd284dd35bff6a1274d7fdd3849d35f7f4dd274d77fd980a535ff74e0294d6ffda80a535dff4e2994d77fd28a6535dff4de994d77fd27a6535dff66938496ffeaa4e125dff4e197497dfd3825d25ffb4e127496ffda80e525dff4e299497f7d384d525dff66938096ffeaa4e025bffaa97848f7fc5a66123dff5e19848effeaa4e123dff6613848ffec5a4a123ffb5e12848ffed384a123f7f5e15748f7fd9855d23ffb4a15748f7fd5865d23dff4e19748effda84dd23f7f5e13748ffdd384dd23ff75613748f7fd3865523bff6a13548ff7d584d523dff6613548ffdd384d523ffb4a13548effda74d523dff65d3548ffdd374d523bffaa93548f7fd78a6523dff5629948f7fd57a6523bffaa95808f7fd5a66023dff5619808effeaa5e233bffaa9588cfbfd7856233bff6a1578cfdfd7855e33bff6a0578ceffeaa56222bff4e85888affeaa4e222bff6a13588bf7d584d622ff74e13588affeaa4d622d7f5e4794e37ed290a5389ff5ea994e27fd2aa65389ffaa9970e35fd2a65c38d7faa9970e37eda74a438dfb695290e27feaa66137cff660984deff51a26137e7f261784de7fd9a4e1379ff62a994de7fd5aa65379ff4aa994df5fd78a65379ffaa9980de7fda90e12 else (if i<4 then 0x620b02410380083800c161e00200d80e144216098320e03170010183c0040544502e003c007800f001e003c0078009501e003c007800f001e003c0048f83c5c007800f001e003c0048380c5c00780080000000678780091f078b800f001019ea78b80099f060b80080000000007001e00254450223e0f103800f00120e03111f07881c00780099f0608c41041419880e1723334b403466267e0a0c360105918a00a0cc40533f1a7e1d88c07120308a007081c004160502d1c5018a0301843603849407800822808009407800f001e003c007800f001e003c00780091f078b800f001e003c007800f001e0020000000001c0048f83c40e00245c1620700100026083800f001e00245c16223e0f10380091f07881c0078008380080000000023d031000000000000046040040c8c1000093a0b149d058a188e4424c0d0c04e1c95ce81a1809c392c311c88ce81a1809c39299c4588ce22c44599c20443f0e46140ac16a51cbf1068fe0b147f0588ce2fcb9199c5c88ce2e44671722338b911726708bf24c467950498cbf24c45f926224cbf11305c88cf20cb919305c88982e445c9302e5f88117e5c88cf20cb9199dc4082833b88199c5c88ce2e445899c460cce2e446717222e4ce119c4588ce22c46711623388b119c45888b3385cbf102e5f88172fc40b97e205cbf102b01abedaf7abc5aedab9dae12b6bad72b4dacd2b1bac5ab07abbaae9ab42ab7aaa2aa3aa02a71a9b2a5da912a2ba84aa03a7d29dba6e299fa61a977a5a294fa502927a43a8eba34a8b9a282873a16a841a0a280f9fda7e79f3a7b59e4a7799d5a73d9c9271f9bf26e39b7a6cf9ada6b19a3a67f99c26619922639988261197e25df96f259995da55d953a535944a50393d24e5935a4bd929248b91ca44f912a43b908a4098fea3e18f4a3b98e823878dba3558d1a3238c2a3058c022dd8aea2a18a2226f895a23387f21f7872a1c5868a18985c2157852212584320f3836a0c182a208f81da05d813a0358049ff97f81fbd7e91f777d79f457cb1f137be9ed77af9e9b79e1e557919e3778a1e197829ddd7761dbf7671d797581d3d74e1d297469ccf7211c6b7121c257031bfd6f91bcb6ea1ba36dd9b5d6ce9b2b6c71b0d6bd1adb6ae1a9569c9a4f68d9a0967999cd66d1991659194b64f192364018fb63618bf629988d61d1865615983360698015f797c55eb17935de976b5d7174d5cd171b5b916cb5b196b75a7967b596163f587160357d15e557315b3566958155a154554d951353c14e153494c3528147d519144150a14054f893c94e9938d4d8133d4c9130b4ba12cf4ab128949c124d48d121147911d546c918f45b1149449910343810b3426907741c90454088fff3f70fb93e58f873de0f693d40f373cc8f233c78f0f3c00ef13bb0ed33ac0e973a20e7939a8e6539 else 0x582a8a06140454040420c50584361244d1848200804108c11482160642c8c24100050848160800204c2050071406100052788e333c2080c391848205007161e0809310a1e143e4e10162486c301446121e248a310c6210502414621c3c10106e1688140cc071a1e2b081401c467c18243ccf030492028248810050402092204014100808092308081b08040d840880e248e0f15841b00e248c3601050180e200052788e3010061012808040208067a19278e0b080a12c4202562242c20205828a020105a280c2d12070185a328e230dc622446038c04008402840403c447a07018c490a5012c4294040201040240c281804140c020a4f0404b18203080a1208050404588405154458870b1544010082c0c141004020802010403848f1220f18040208000600f118610846230c2c0ac41601c20b02b1058070a446742d18581e0aa0b0565019dc40ac161000482a1b8c220b0419858209c0e14161118188c461601c24a0351650070b2803859401c24a00e1250070b2803840304cf93c402028280e188e450c47220c05063c71cc30209f970e60624311c8a188e450c47228623914311c893ee203718581208c40683a18941662a34544a0b07c007800f001e003c00448010570508015814132e2b0283e045605062b0282e04141586002c2060424b3c0c13f0c1401438182786e67a1803892711037109820c62303c560dc62b06e202c254078243e0f119e540283004601029cb90320ac41189c0a0c0b08161e0020285a20882d100b0285a3147880d861be3a168c2e1241b18a6168845317150b486203e168c3603851fc7220401b0c071f8581bf1040c42d10081a7856127e08516302720d822304804105a12081103841b00e200c294040715b88180e2b0802158501c0c2b0c560dc4038ac240e0312062b080608ac140c31fc26284e3f10480e021c001c50802f10003085bcb880533c2d182bc406a30b00414061bf1030b788100c1e00285c1620b8191088168b971304210ac208c290dc7c004241301b18880c972300c3018780099e8606c31183186071fc162e5e0c0e071fc162e5e0c0e061c08cca8e3f82c5cbc181c0c1a0ec40340cca8764e5e0c0e060a02020683b172f0607030501010971fc163e5e0c0e071fc162a5e0c0e071fc162833970e07cba162a85a4e002250598a8cb1140141e462802833133f05066201c218f231401419880a67e308c480540e21070188180c4461803d128bd0b08251460e0c57c0c141e9c5881c315d030507a7172160f800c161830241c0)))
def r01l10 : Packing := (515,3,7,7,1,14,0,r01d10)
def r01d11 (i : Nat) : Nat := (if i<1 then 0x40b1f899d0bcbe2090b58aa32f882b3a5197c411623fc40d1f28cbe209280365f1048001fe07eb9f857d4df337be1ec6799de3e7879df57731dac75a1d4874a1cf67335c8970cdbf86f61b8b6d89b396c41ae76af9a716945a3168219df66d998d654990562bd86b61098195fe57d05ec17875d317115b7d6b65a5963758155c1561953053d54b15245456506d3d74e713734cbd2f44ac127548a11f646ed17744850cb428907940f90153fd4fcc3eb0f713d20f043b24ea039dce2137bcdc6362cd6234e4d1032e8c6d3110c092f38b9c2da8b412bf4acb2a88a79291ca15278c9b1264497a256893a248c8f1232089621b483b20487e01f007971ddc74e1c946f31b28698199863418505e217085ab165056b14e451013784b5120c46c110c4110fc43bf0e343640cec3120ba42c90aa42800980240088020007801c9068018905c815204ec12404340f6033409b01c805200a4000ffebca71ffc794e3ffa529c7ff0a538fff4ca71ffd984dfff9309bfff5e137ffe9c26fffd594dfffa529bfffa6537ffe9c24fffc3849fffa7013fff4e277ffe1c4efffd784d7ffb309afff26135ffe9c26bffd284d7ffb2e9afff4dd35ffe93a6bffd294d7ff8529afffa6535ffe9406bffd38497ff87092fff65d25ffe9ba4bffd39497ff87292fffa6525ffe9aa4bffd38097ffaf091fff56123ffecc247ffd3848fffa5091fff55d23ffecba47ffd3748fffb2a91fff4d523ffe92a47ffd5808fff8b011fff5e233ffe3c467ffd588cfff8b119fff4a233fff44467ffd578cfff8af19fff49e33fff3bc67ffd258cfffab1117ff16222ffe9c445ffe8888bffa6b117ff95622bff4ca717fd970e2ffa521c5ff66137efebc26f7fe994deffb301bf7f4dd27efebc04f7fd9809effb2613f7f4de77efe1ccefdfd389dfbf8713bff74e135bfecba6bfdd374d7bfcee9adffa6535bfecc06b7fd290d6ffb2e92f7f25d25ff693a4bdfe77496ffd3292fdf4d525bfec984b7fd9848ffda5091dff65d23fee9ba47dfe7748effb2a91dffa6523bfecc0477fd9508ffba7119ff74de33eff3bc67fdd358cffba4719ff722633fee3cc67fdc598cffb85319ff75e233fee3c467fdd588cffb8b119ff74a233fee14467fde888cffbaaf19ff715e33fee93c67fdc278cffbcef19ff749633fee12c67fed2888b7fd11117fb49622ff691c45fde3388bfd913117fb16622ff61cc45fed7888bfdab1117fb16222ff69c445fec3888bfdd11117fb55e22ff69bc45fed3588bfd86b117fb95622ff719c455fd970e2f7b281c5fb4a438bfc848717f9090de7fb3013dbf65827bbeca84f7bd9409efbb2613dfd46427bfc8484f5fc97496f7b2812cff66023afecb8476fd9608eefb2a11def65023bfa8c8477f90908f7bd1119f779de33df744445dee7788bedcab117f38ce22 else 0xb1546232e4232fd72347aa3102dcb941846862fc8b12201b10512b3b103718319d0cc0158586059399d0b1b94482847b389d0f940b711975338a83915107e33160c0b23198b088f87e227e49422c3634a93c188c0333e727234fe723670b272341c0f2e56c4150797248ec80c09c4f2f0c2b050e1018a0d9c4e98c0f2e0b4850a1971695b106541507236720e9d03188b72e0b40429cbf1c9072989c95880c862fc28402c3cac142123119716914637919180e56cbe210ce260b46391b06c623518dc5a41c952722d20fc6c1bc4100436878b481805926308b1c992a4827831180667ce500647810485687c1b103f481853060815711973a551e2f03116397c40188b920018604242e47e41f8b0083168ff1006233c7f3fc00bc0c667afa9e1003620cce1f8280d80293c213f85906ccf860c0c832a8c5630316c2e0d9750160ace162e4a2d543209128cbc2ce0741b39630386192605829399c0341c4c5a958a0d9d3181c2cc832465d7303858b4ec8862fc68fa72fe1f0b07199c83a72c6070b33380b05a704d262d392116c885e227e61b1463093223d9e4f87947113f3a3d16ce87c2e506675391e0f0a4ff1076722e9cb985c0cc0f1302e9c4685e5f108240dc0c4e059450a8271200d88303c04ce858df2f883938168f81b3a1637cbe2124805892622d85ca32f884918623f0590662c1fe2084f67c1a30271c98a0060c0e4997030e46ce028fc724188fd1634789916cecbe20d2311b391642703d9c5687e5f107221255197858e4c56cb8dc724a740f2e392110040b98958290bcbe212481881b2e0b29232e061c9088052481c7e3931240e3f1c90ac071f8e494e858fc724220140656988b60797c42416032b0b51703cbe21048cb81872407b385b28cbe20c4e670b40d97c4189033160ff105160dc523fc4169d0f1fe20844141585b28cbe20e489465c0d88283c8c3f059088491f82c8b1419132e0b2b3906b1cb82cb4e87aa32f0b2b39508fcb82cb97036206ce05880abf5c8d6397060d7e0b101962cecbe20a05672fd724032c59d97c414190c672e48b10333b2f8828159cbfc411628385b3b10502e5d723064317e9320157f88183218985c919d0b5fae48ce032c72f88283218985c911e44030ff1056743e173fc4159c8f030ff1051f81b103a743e7e06c4159c28c40c30b910fd162478187f88201962cecbe20a0381b39724588199d97c41407036722c8b10340d9d8828fd7226723c7f8823380cb1cbe20b97032e46ce0340f2eb92b39639703620a4803138164240189c0b21200c4e0590900b03138831058fc6060c0e464f0300c724030607231886018303060723030607231c8183031f8e4448078fc1841f82c43f05889e28058c7e0b10fc1621f82c)
def r01l11 : Packing := (176,2,7,10,1,14,0,r01d11)
def r01d12 (i : Nat) : Nat := 0x3ca1382e5e20c900c9c1644e310b2897883189f858cc4fe2060c307234e0b3f39227019885cbc41920c41a5c2ca9c1662512f10648061839227079405834bc41cfc2c49c1e500d2e1664e0f0b063f88318944bc4102e5e206512f103ab68894e36865fc75da25d54046cde3249417c3a07400ffd38ffc38ffd37ffc37ffd27ffc27ffe77ffd35ffc35ffd25ffc25ffd23ffc23ffe33ffe22dfe77fde33fee22
def r01l12 : Packing := (18,1,7,8,1,10,0,r01d12)
def r01d13 (i : Nat) : Nat := 0x2e205ff
def r01l13 : Packing := (1,0,7,5,1,0,0,r01d13)
def r01samples : Array (Bits × Bits) := #[(0x2453cb22a70c5210332d0323c4f091816008074685802218b0a040a85951203063c7820104a00f4044043c0602103430189d328898110230252a1a6191091910c502400a210d1b4342404213601a4179a0a93080184c00604b808838014ab4c0,0x84128080840952001208020380d091886008062614812210808040a8305120204205020002a00e0040803c0202102130188110809050921021000841098909008000200a21081b40424040122002416980a910801848002049008038014aa440),(0x38010540050a06740823408020148308f61f898520749c00206114422a45c041810382a7111a00398010040dd85c2c526408c5726262906d880208a40048627203c90b40c6000b0851c396005a40e024054013342210f0090374147b0214101,0x30050440000a12440023000220000308e40a080424609800044204402245c041000b83040018013180000518c848205240004142600200dc88120840004002020388234086000b08010386001a40e00401001334021070010350107b0014100),(0xe954138d16845cf0809c381bcb25b8406312488e2a15e5a88e390bb438c73756cd651d5dc0be5191c164c22c934de58064809b70398e12c2329e6270c5f2098d1f128854d5145c554c44a51c436c70628da1b449233338c61c80c4c88a458e05,0x685c0791148440500214091b4121a8000112410c2401e4280a100198280223524524040d0028512003642020116110808082994001060400121e0250c48208041f020c00d5145c054404851c404840420da0b440221228c60c8044400a448401),(0x85270525d40a6c09749a92e59c0c63aee160045320f00a46ddbcfce3812b9150562263c4b6d09c8360d8c5103c0c0a29d54c43b6144438c50f1929d0223a671b289950b8a18b49403b7214a61aa1aa08288d4d244898f212615402abd8906134,0x942200200008240930889060188441a8606000410070024394a28c0481211020120000c094900e084498c0000c1420085164028714403841050120000018631b008840b0208b01401b4210820aa0a208200d412408085000215402abc0106014),(0x4c090356ee92181ea517e38363793336c7875b054734f3e4eac1054a481cc37929e0f5256c6cf777a0f78b7898c5d45cf1ca845c0c2146a180081eb7336124b42cf70846b4f88003a09f9be1701f594e14122e57a285a277bd1118002e3453e2,0x4009031663968806814725886229260681157908430691a42a4501430808431929e0dd24680ea173a06603781083d4c4a00a805849210480c04816b6b26204c42637004494708003a09d8b61501d180614122e53a285a257940118002e2413a2),(0x187a486011fd20dd6eb1403434a7465c1bdbe8c1e15c153e1f7b0250891a679bb3404362492885293643168343a2908288713cc6d324e527cd33850ecc862651d94acb814ce7e09f3811c812040006963f10ef91b8080d08a2d53f92cf46a009,0x12484020116400532c91c0101424463003d36801c0541028337a8a0001221492a1604542000081012663020000a090808070004400060d2704108008c406065518ea0a8004c5609f38118800040002122b00ef11a0000c00a2902f82ce040001),(0x286a13a9ae4e707b0fcc4b105629749446e552ed8261c4530b29b8ab601892e079c5586941d3c06dfd7afe064592064ab960b8d5ad43d7eb06406037d26fc6e832c2cc336416f65e18b01478e4b0251d16646623d428c03a5ea2aed23388496,0x4466211a82440403a8b5c4a114461dc86006450e9000047530b29e88b001a12a0114450014183c44c6dbe6086059205299040bc958c41d6204348243792a654c11020cc334016b45610b01078e4b0051916446003d028803a5c22ae803308096),(0xf03632c8e85288ac990e2cf6aa92c54cccc2b6869960911646040052c3d78aa7d8953090a90a619ab1729a3f6efea7031e08a01a4818e6586b656c194b4c11829401734d2a32116cc02b7a292ae210ad901fd10eada5d3a40466b111510c2a2a,0x80209040a81a888c900a0424a292014e5404948219a001964484004244d5c82508803090a102289ad810885f6a1e2d431708201aec09e25868612c811b09518a8000704d2a220160802a72212aa210ad901f000e0da5d3200066901111082a2a),(0x888ae064ca397c1d040714a93422195181dc4314c898f2b5955e28316254eca290edeec1384e8b4121a30e329930e2d0226759821f183d898c6b39524d95ae0a24cbd285320b78092a4a628f884c425472a02d844c3610d4029463236c9175a,0x8809e056c8191804042290ac1180005180800300e812900480520030644424108029a04030540b0100010e101020e2002032410213982889842019402c110208204b1084320940080a4262870044424440200c840c1210c4029401030c91748)]
def r01columns : IndexTree ColumnInfo := (.fork 44 (.fork 22 (.fork 11 (.fork 5 (.fork 2 (.leaf [(1,0,510,0,12),(2,0,509,0,12)]) (.leaf [(5,0,506,0,8),(6,0,505,0,9),(2,4,369,136,7)])) (.fork 3 (.leaf [(9,0,486,0,8),(14,0,497,0,7),(10,4,369,128,6)]) (.leaf [(17,0,494,0,11),(18,0,493,0,9),(18,4,353,136,6)]))) (.fork 5 (.fork 2 (.leaf [(25,0,486,0,8),(9,16,486,0,8)]) (.leaf [(13,16,482,0,5),(26,4,353,128,5),(33,0,478,0,9)])) (.fork 3 (.leaf [(1,32,94,384,7),(37,0,346,0,5),(39,0,344,0,4)]) (.leaf [(49,0,462,0,8),(57,0,454,0,5),(65,0,446,0,9)])))) (.fork 11 (.fork 5 (.fork 2 (.leaf [(1,64,188,258,7),(66,0,445,0,11)]) (.leaf [(70,0,441,0,8),(66,4,305,136,6),(78,0,433,0,5)])) (.fork 3 (.leaf [(74,4,305,128,5),(14,64,177,256,5),(81,0,430,0,8)]) (.leaf [(82,0,429,0,8),(89,0,422,0,5),(97,0,414,0,6)]))) (.fork 5 (.fork 2 (.leaf [(98,0,413,0,7),(113,0,398,0,5)]) (.leaf [(129,0,382,0,9),(1,128,346,36,7),(130,1,332,48,6)])) (.fork 3 (.leaf [(133,0,378,0,7),(5,128,346,32,6),(134,0,377,0,8)]) (.leaf [(130,4,369,8,6),(6,128,345,32,6),(7,128,344,32,5)]))))) (.fork 22 (.fork 11 (.fork 5 (.fork 2 (.leaf [(142,0,369,0,5),(138,4,369,0,5)]) (.leaf [(145,0,366,0,8),(146,4,353,8,5),(153,0,358,0,5)])) (.fork 3 (.leaf [(161,0,350,0,8),(129,32,94,256,6),(33,128,346,4,6)]) (.leaf [(162,0,349,0,7),(35,128,344,4,5),(165,0,346,0,5)]))) (.fork 5 (.fork 2 (.leaf [(37,128,346,0,5),(166,0,345,0,5)]) (.leaf [(177,0,334,0,7),(161,16,326,8,5),(145,32,78,256,5)])) (.fork 3 (.leaf [(49,128,330,4,5),(193,0,318,0,7),(194,0,317,0,8)]) (.leaf [(198,0,313,0,7),(194,4,305,8,5),(70,128,281,32,5)])))) (.fork 11 (.fork 5 (.fork 2 (.leaf [(210,0,301,0,5),(225,0,286,0,5)]) (.leaf [(257,0,254,0,8),(273,0,238,0,7),(281,0,230,0,5)])) (.fork 3 (.leaf [(265,16,230,0,5),(289,0,222,0,7),(257,32,94,128,6)]) (.leaf [(305,0,206,0,5),(289,16,198,8,5),(273,32,78,128,5)]))) (.fork 5 (.fork 2 (.leaf [(321,0,190,0,7),(322,0,189,0,8)]) (.leaf [(258,64,189,0,8),(326,0,185,0,5),(330,0,181,0,5)])) (.fork 3 (.leaf [(266,64,181,0,5),(337,0,174,0,5),(321,32,30,128,5)]) (.leaf [(417,0,94,0,5),(385,32,94,0,5),(450,0,61,0,5)]))))))
def r01autos : Array (List Nat) := #[[],[100,131,82,16]]
def r01levels : Nat → Packing
  | 9 => r01l9
  | 10 => r01l10
  | 11 => r01l11
  | 12 => r01l12
  | 13 => r01l13
  | _ => emptyPacking
def r01index : Nat → Nat → Option (Nat × Nat)
  | 9 => fun _ => none
  | 10 => lookupWord 55 190 6 12 7 1 (hashr01l10)
  | 11 => lookupWord 252 872 9 15 10 1 (hashr01l11)
  | 12 => lookupWord 84 301 7 13 8 1 (hashr01l12)
  | 13 => lookupWord 10 37 5 10 5 1 (hashr01l13)
  | _ => fun _ => none
def r01 : Forest := ⟨1535,13,fun j => r01samples[j]?.getD (0,0),r01columns,r01autos,r01levels,r01index⟩
set_option maxHeartbeats 0 in
theorem geomr01 : graphValid r01 (boundsBefore known383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=5) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr019_0 : block r01 9 0 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr019_36 : block r01 9 36 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr019_72 : block r01 9 72 19=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr019_91 : block r01 9 91 27=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allr019 : block r01 9 0 118=true := (@block_merge r01 9 0 91 27 (@block_merge r01 9 0 72 19 (@block_merge r01 9 0 36 36 sr019_0 sr019_36) sr019_72) sr019_91)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0110_0 : block r01 10 0 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0110_36 : block r01 10 36 16=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0110_52 : block r01 10 52 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0110_88 : block r01 10 88 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0110_124 : block r01 10 124 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0110_160 : block r01 10 160 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0110_196 : block r01 10 196 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0110_232 : block r01 10 232 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0110_268 : block r01 10 268 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0110_304 : block r01 10 304 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0110_340 : block r01 10 340 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0110_376 : block r01 10 376 34=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0110_410 : block r01 10 410 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0110_446 : block r01 10 446 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0110_482 : block r01 10 482 33=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allr0110 : block r01 10 0 515=true := (@block_merge r01 10 0 482 33 (@block_merge r01 10 0 446 36 (@block_merge r01 10 0 410 36 (@block_merge r01 10 0 376 34 (@block_merge r01 10 0 340 36 (@block_merge r01 10 0 304 36 (@block_merge r01 10 0 268 36 (@block_merge r01 10 0 232 36 (@block_merge r01 10 0 196 36 (@block_merge r01 10 0 160 36 (@block_merge r01 10 0 124 36 (@block_merge r01 10 0 88 36 (@block_merge r01 10 0 52 36 (@block_merge r01 10 0 36 16 sr0110_0 sr0110_36) sr0110_52) sr0110_88) sr0110_124) sr0110_160) sr0110_196) sr0110_232) sr0110_268) sr0110_304) sr0110_340) sr0110_376) sr0110_410) sr0110_446) sr0110_482)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0111_0 : block r01 11 0 27=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0111_27 : block r01 11 27 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0111_63 : block r01 11 63 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0111_99 : block r01 11 99 9=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0111_108 : block r01 11 108 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0111_144 : block r01 11 144 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allr0111 : block r01 11 0 176=true := (@block_merge r01 11 0 144 32 (@block_merge r01 11 0 108 36 (@block_merge r01 11 0 99 9 (@block_merge r01 11 0 63 36 (@block_merge r01 11 0 27 36 sr0111_0 sr0111_27) sr0111_63) sr0111_99) sr0111_108) sr0111_144)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0112_0 : block r01 12 0 3=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0112_3 : block r01 12 3 15=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allr0112 : block r01 12 0 18=true := (@block_merge r01 12 0 3 15 sr0112_0 sr0112_3)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0113_0 : block r01 13 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allr0113 : block r01 13 0 1=true := sr0113_0
theorem tablesr01 : checkedTables r01 13 := by
  intro k hk
  interval_cases k
  · exact (rfl : block r01 0 0 0 = true)
  · exact (rfl : block r01 1 0 0 = true)
  · exact (rfl : block r01 2 0 0 = true)
  · exact (rfl : block r01 3 0 0 = true)
  · exact (rfl : block r01 4 0 0 = true)
  · exact (rfl : block r01 5 0 0 = true)
  · exact (rfl : block r01 6 0 0 = true)
  · exact (rfl : block r01 7 0 0 = true)
  · exact (rfl : block r01 8 0 0 = true)
  · exact allr019
  · exact allr0110
  · exact allr0111
  · exact allr0112
  · exact allr0113

def clippedInputs01 := inputs.map (fun a => a &&& ~~~seed01)
def clippedGraph01 := graph &&& ~~~seed01
def clippedPairs01 : List (Sig × Row × Row) := List.ofFn (fun i : Fin 9 =>
  (clippedInputs01.getD i.val zero, absentRow i, presentRow i))
theorem clippedLower01 (impossible : Impossible clippedGraph01 13 clippedInputs01.toFinset) :
    Lower clippedInputs01 clippedGraph01 14 := by
  apply lower_impossible (by unfold proper; decide +kernel) _ impossible
  have es : checkEssential clippedGraph01 clippedInputs01 clippedPairs01=true := by decide +kernel
  have all : clippedPairs01.map Prod.fst = clippedInputs01 := by decide +kernel
  intro a ha
  apply essential_ok es a
  exact List.mem_toFinset.mpr (all.symm ▸ ha)
theorem r01_start : Impossible clippedGraph01 13 clippedInputs01.toFinset := by
  have noRun := root_index (g:=r01) (before_sound known383 valid383) geomr01 tablesr01 (k:=13) (by decide)
    (i:=0) (ws:=clippedInputs01) (by decide +kernel)
  have tgt : targetOf r01 = clippedGraph01 := by decide +kernel
  exact tgt ▸ noRun
theorem bound01 (deadCase : Impossible graph 14 inputs.toFinset) :
    ∀ C : Circuit, PEqualNP.MetaComplexity.FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 1)) →
      PEqualNP.MetaComplexity.circuitFun 9 C = edge → 16 ≤ C.size := by
  intro C legal first h
  by_contra! small
  obtain ⟨k,t,hk,hdead | hlive⟩ := initial_live_gen 0 1 seed01 neighbor (by decide +kernel) (by decide +kernel) (by decide +kernel) C legal first h (by omega)
  · exact deadCase k t hk hdead
  · have sl := seedSlice_clipped seed01 (by decide +kernel) (by unfold proper; decide +kernel) (clippedLower01 r01_start)
    have noRun := poolCut_sound sl [] (by rfl) (ws:=inputs++[seed01])
      (by decide +kernel) (cap:=14) (by decide +kernel)
    exact noRun k t hk hlive

-- Orbit 2: (0,2) restricted tables (from L_meta_1668)
def hashr02l13 (i : Nat) : Nat := 0x7a000000f4000000000000000000000014c24e8e00186184000b000a1c0023cc57086b350000018b246cd2030ac4035d2400706c845400612831482e00000000003b400043202000000000000
def hashr02l12 (i : Nat) : Nat := (if i<1 then 0x600000053451c6000f3b800084e000b0bc2070558475ae52c7e0e7995e67a76c7600000000014940000005ae40000001cc0001dd2000f540001161a11928000000018f1be820ad4f2a16b792e93b509ba2eafac00120692db0a4000000000195b9860000006c4804000000032b4000000753572da1d8140002c080000000000001527e3dc9ed37b81720e3bdca80f76b55422c16991a0df300472000000075f09d4d13c6374b7213fd46bdd3900002ba0004064154000000e8ecb14000c7bf12f482e660c61a2c36e5d8000000000082c0003dfe3240014cb2050876dce210ec3800037a0007459b3ada622e0004250000000418f0cc00000000000004b90080000bb400147f00000000000009e480011ac4020000000000000a74323f706000e0080000004c400000000014d297810ac0006bfa20246cf85a603b26960001ca31e0172be898cc537b15c00000066080009cc4dcf3a0b5000177a6320001c36000000000000000000000008fa0000000000000000ad78000ab7e1e0000baf41e8e03abf7535444767a631a9090711e3d7f9bcd80d524a9eaa1d5b53cad13294ccb4fd5780000006b8e400000bae00000000000000000000000000000029997b67504fa3484d400000000000035b582c294dc980002d865500000000000000000001cc0c4858a0000000000000000000000006cdd76000339800000000000000008060000007cd02a9751002e46400000000000115333a971e79095351d9c5940f8001c62a438000ca96dd00078670daab50000002c4c000d495a7819aa79d0fc0de672a236715f1d10618c74e1342c120000000003152f94b6c80019560000a5be8c001e4c00059474c2000000431dc480000000000001c5f1d160e7f62f17f61525db2a000521ded687ebc6000350000032bc3e0000000b13fa553c700f870c3f4a9000146b3270000c43db0d985ad3e2104100020b4000000809950fc8c000096000105e0000005e9c000000e1b68c8000000000000000000058d0000001086c0ac13716600000000000001210f7c0694b3552f52c9b80000000003af0000000c1a80000000005ac80000000000000000001a520000002a284e1d185861cf1deca678000001bdb37700020ca000672f8e9868000f4ff24400000040e000000024400908e050acacc6b800196c000da3fd62d10000d388000000000d4500022a0a670040403404000080000001c00034040100900c000200200c010100001401024000080500002004000000a0000300c0000401010000000000800000030000300001010010080004403000040000401c0000000000010000700000004020080000001000060040800400004000180100c0601c0100800008000080200000000010040100c0100000000010000000001000040000100c00008010080000000 else 0x3ddf6e40006124000000bdc800000000000000000018c80004ca9a1b789b5762ddb89c68c470000000000ee9000241a000f46000000000011100011300000000002c9)
def hashr02l11 (i : Nat) : Nat := (if i<1 then 0x41c021e40003103554e0001800c2e5ca2a217c208000038a9d00c00014c14850d8a5212f0ff225ed2be000390e2dd40000a502c73000091cb896400025c8333d48129425a91639800000000000e279e904c9c0000000109756bd00900000000000065c253e8d5194c330a2c4b004bf9002975e37c0000000000000010842d14607b1910000000000006048a430000000008585171cf22c64f078a3e444b80430000000000000000000000148580000440000000020ae000000005075681000125240000207c3bb4579c1280000001c1d000000000000000000068b9f1b8520c00000000001b7f3c1bb000a50072605118000d96ca6cfa5fe9ae2449a59887d68d24ca4472e042a853942a11588ddd9580a89004b897191f000288c14c8b08081d7e3060893863224774fb6377066e83086be130257dfa4dfa4ef3cc8222b8329d2cb700008330c72000000008082a63aaef310f59cf64654211910b8dae752867c12c0001e8b7ef8a431848e866646419adc3e10a480588000525440b20e2800070c80003d27845941a04632530824c0001247581ce66c0001527d47630915071265cc36d17e000023ded38fe41000180c4000000054a7c7c4000494583e449550818000816a071d078495ba02c000000000000000000080ab9fc00000001041e19b1506a3540000000e89989bf926e1720001a2ac000426523ea0000000000059126607e5318ad30b9a2970eab4ea9526e4f7417e23ed176085882b608b000000010c7a0a80000d4d800000005b6a000021c694d3c8e8794ec4a5a10000864c453c8e3b4f400000001a2c837ac570d1e59de1872e374936da4674c9b0a967130e701201c0780200c010088010220500380001801c010040020240080c00c00000007008000058010060000200200a0140380100206c05801000010038040000000000100003c08015000008020030240000200001400402800000000010030080040000300201803800000004020020020480000600000c0080d01a018000000020000080400000000004002014070080000080080000800800802006018000000000000080100402400807000000098040020000180101e000008020000080280001400800002004008008020040100280201209c02800000028008000000040000000202400801006000058000000340080400200c0000200001000001000000008070060000080304000400007006028038030100080080101a0540680200c01c0080800400800001004004010000080200000101a0440180000c018000060020040000500e03c00803004000030170080080080100a02400000002004000000000000100200804c010010040140000000000c008000060280000000c0040580100601400002006000018000000000000100000c0400200001401012 else (if i<2 then 0x100ec67968e800000000c49385faa0a0000000206a130eb24f23ad0bd1142c9aac0a0000000081d4000062a000000028a751ca213c0000837525a000006288db0a382ce80000000748ad89c021cc91481ef3c46926aa2e410920ac1bcc8e55df3004000342704e9c3829095049c070ab8e00000000a34e132321a13b585a6c17b745d40b4629237e67d63bad120000000000000000000a9480000000000168240000000000000000000000004e0786e30edce000000000000000429800000000000000000000001834000000000001203b21a000083000000000b2722a40000727400000005d400001971400019e31c860000000503300000003a9d880d0001c2370bb68f4000165900000000e06c886b107c873942436a9af0000064d9c5ad408e0ac10cf333b01a8d394b2b27cf44d000034156853e8e80486329c4a3e03d68223b9772550dd1a00001d585534fa630000290c04568c5000006d00006ceecc57e1280000000e3f4000049008080000e1d802339140001c110525011e440b95a107ee979b24e6218000024410a443a70efc60770ef485ec92e27780c4282dafef065643e539a300cd54712b359c0004649e2c600000d1a1962877051b8dc80000001569f1190000000000024e8341d000000014930000d4a20000cfd8202813b63280000000e17541e40006dc4000000024f0548e00000003d1bc9b10b22000046d625479f0000009d8000626e0002336800000000002c14025f597000038cef80e0000859741199390000e3bb10e8000a3b0735a447000000000000000108974030250000000038ab68b8623c26ed39240100848000920409e00002a8c2bb4c8af88c5d439ab40000000752ce18c000140e8000d2d5676c000358e0001e6900000000f181c5a16be5ddd19f20001c170000000000038fe80000001205facf80000000a7abce17e4f000000028855967000147b000061ed0001a547d3df28a00000003ae6a97f0001b1fae1b5100bb24000000000000000526c0000000437ec84c0000000027e00026cdd0050001d6e800079eb42c1e507a2a000000000000000405489e9f524000719062a889fc00014db0001a6c82f379d2d03312df28161a2b374e2e0000213303619a50000000074f9287a4768000000187e487ad28d50aa03e30bdd13e007fc7674b8f030916924afa6989e6b1fe0a08c23e87e8288c4d4000752fd286a73ff0df0c4908ad698000547b9118058a208d11100000000ee65476000059616f20000000000000000000347ef3a0000000000000000000383e00000002cacf173a95de2900000000e13909f8547d2674bb686f12a5a1d7050b770c000609b33ec59e34cab15a039b54fc0000000000000025210000b1080000069fcc90000505cce1f0c3000000000000000e0fed44000000000000000 else 0x71ec000327d80000000486000000000000a95d23fc20d44ebc96dca40000b33536e4b459c587d11c1c6030a0cef1b600000ce428e4284c8850bbfa3600000003e996984a0bc00004065961d38c341f6ab0000210581eb0dbd955a31791e8f468000b13fc09b6e80000e13000000000000f8cc83840000000204290180006040e2f824c7e72690e0000000201e81070000000000000000000000000000000000e3588552a56000140afd3822688098000000000000000000000000000000000000065d30001d42000019c4d44e34b40000000000014c40000000798e0003911628b980b08d554a0000842289cc0000851000031e0298664bd48bf903a3ea913d035c0a94a57de71a0c67b800008e2d210c61400052483354c1f4f1945b881bee79fc9270fbd09e000000010b2d93a65e3c2c2101102000000007992100f66adcab24fc0834a8e80832a88647ba9f40001934eb2727dc0007d4c0001b52aec6b8c9c234069c000316d0001d73c8a5f569895f828e240f91744960001d4808ea34e444540799d38503647bc00000004d14d45ba9a2a62425b6973ab05226347617968e8a818a0d6d50869980000000e8cd295ae2fe1e3463500f8000116dc25a40e2147e3a7e7ffcd4240f000000014992566c3d200000000000a8f86574506000079ae04a742480000001ea240007a290000c4c2cc408c730f000016bf7a660000000000000000000d9300c0016c2371e02906b8000114042c2cc1e9d61b47e540000703a309a00000e76a8789c00000abdadeb0001c55f8bd00008ab261cac9b180bdd0a7240000000013f0000000020de61c95825c6ca009019a42bc00079ac734270640b48000a50dc896b3d4869134dd21ec6a00cc1184e3bc0000000c9bd4204000098900d0000212878cb7bede5d2409ede2f2dfd41242cecd0934ba363d17d0b3336ba2de08b48bc614c053c47e5d8c58418223b41a88f148069e5c2e80000001e48607f4970705a0003af0b00f0001e8655358000e0d9a4100006032f472e2fc8ed0000346381f0000000082a714b96dd800000000003aa08000000000001047029f2a400000000000000000000006a4e31a3016c87000000866615c00049a900000003a09697d9ac800018f4000))
def hashr02l10 (i : Nat) : Nat := 0x920000000000d36000000000080439c0c3e21b41f000263328261609f8a2600073ad04a6e1a0913950948da000e2d8001847a100000000001a4d3344ca8000000822c1a80000000000000001c2f00000030d6000727101fd0c00000000000000000000000000000000000000000000035d5a14000643b2040000000000000001493c1100b54ee00000038510943050000a00001462b06c25000020241d21088ae332998b8a00be66e000083c000e40d0c0000700000000580e43a0000000000470c4c81bd1e00001540004168078186000000001400023e7478cd2000000581aefe00054780008ca000ca091f444d8157c800038a2000fafa84c000b776c7a1800000001ac8000000a191ca90cd84e00000060abc34e1efac419810be74749709000a0000005ca4001f1400000010f547b51c800000000064c2c2191305ec18505b486855b3200032b60009a6800013573600050a78020000000000cac0000000002c8d40be466a5a8f262072200038e389914850b800144f496391c00183124ac140000000ac3fe30001659c1a0923114041b46d9fd8c3258cc400016c000042e000000120c3a400000000000001c5871508b0005124c6a0000000003e2aa883398000001755e48f40800084b00000030ec09719100000000000000003809e63c0e704587b86f2a5414d4a9389629000000122ba070000000000000000250800000000000000000000000000c3bd8e8003c00000000000186405d000220c22f98e8bb619ce13c360006a3a87e7104108003ef9417000040204010301002010000000008000000018040000018080204020000000000000800008080005000040601010040002018080002030000000018081403008040204010200c04010081201000080000000040200
def hashr02l9 (i : Nat) : Nat := 0x2c000a4a01
def r02d8 (i : Nat) : Nat := 0x1e080f062082fcca6d5636606192f8c86d56364061
def r02l8 : Packing := (2,5,7,0,1,5,0,r02d8)
def r02d9 (i : Nat) : Nat := (if i<1 then 0x69a996063fe5d4234caa71ff2ea11661538ff974a9d32c0c7fcba5469960e7fa5d4aa98b031ff2ea5564d81c7fb02d4532a9c7fdba5869954f57ec0b4c4c2a7afe605a026153bd3b6842c67334fd5ba216118cebeadc90b08c677e56d08584633b5eb6c54c2344575db921a558cef8eda10d2ac677c76d08195633aebb7230cab19df1db4186558ce97e5c2a64b3030ff6e2aa659538df974c332ca9e2fca89999654edceda130c1aa76f36c89860d538fb974cb306a9e75e55aa993186b7a5b302c88a72f72e1a654e338dfb6d55326c0e2fca6a219360637e5b34ac9b039b729a3364d819eb974c2acb19cedcb66a1518ce76e5d306a9ccd1bf2e5a84c666cde9524b262c0e6f4a9999316063fa5cb4a98b039dd2a6554c581f5ab0cb1a62c0c7f5b9aa9812061fe5c34ac9ac31fd2e99360561cd7b29552c630cafcb869563187b1eca4aab18c3cb76618358c61ed3b28c1ac630e3f5a9a20838466fadb950b1c233ed6d0a858e119de974c32c708cef5b62a5538463fadc950a9c233ed6d0a854e119fa974c1aa708c3fcb969953a2355ed22c630d113b72d9a1262339db974b2b0d19c7f6bb6849854f1fcc0b404c2a79fc845a026153c7ec225432ca9f756558cd9121b9af444aac98c3d9e99a5564083c5fb02d3130a9e6f6116989854f33f554ccca907d979563325981e7e51108b2041f6f2668459020fbb92ac22c81078fdaaa8864483cded553332241f2de33a20966073bb554aac8907d9d99a5564483ceed5508b2a41f376888459520fb3b33422ca907dd560e1165483cebd552ab264352febb58d9818717f552c6cc0c34bf6d56366061e5bb46b1b3030c6febb69a9960717f4434d4cb030ff2e1a959563b5eb624c30cb1db9db42618358ede6d9130c1ac71bf2d9a1a65538dfb6c54c22a9cbddba186888ce9eedc8c3444676e76d061a22339dbb7442c673356ddb92163399b36f19b4d4cb039bd845a6a6581ccfd552ab2c41c6febb2a58199b17f44152c0ccd9b78cca960666fcacab19c233363deaa8cd9818796eb2c66cc0c3cd79563366061cfe422d0130b1e6f6aa8459620f97b44422cb107d9d9561165883edab0708b2c41f63e669559420e3fb5db424c2c73bdaeda624e11d5ed10d312708ee76556989384799f2ad10ca0c39f9845a226163e76d1108b2841f6b6668459420fb9b2ac22ca1079dd845a526163adf576b2b2030f2fa8859590187b3cc2acac80c3cdea225564061f5ac2319d113356fabb58d9018797d442c6c80c35be6d56364061ecf4aab1b2030f6d98358d901878fb44422cb907d3d99a1165c83e7b51119b2030f6d9658cd90187bad2ac66c80c3d9b99a5564883f4bccd444ab19fb5611a22558cfbad2ac66c810dcf9a221164883edcccd08b2441f766558459220f1ef44554c98c31bf2d9a864453 else 0x15081808001142008a105c100000000000000f07c0f80100b0f80080002c2006e1f00104a1f0010141f001f001f001f00102e103c1f0010161f00106e1000b080b0f80081e0f800f800742018107800f800f800f8008050f800f80082e0f800f800f800f80081d0a42b001f0010000074290bc0040000000000000000007800f800f8108a28140e85e003e00202c2000005041284000001e003e002004a100000f001058008000003c00400003c0040007800e800e800c1007c200340074007c084516800c0a07420001a002000000000000141d53a934fe8fcff9eb3ae65cc19432063bc6d8c716627c458770c613c1d7faf1dd3b876fadcda9b49652c2574ac9552a2534a49452824f49c9352624b495f27e47c7f8df17e2243485f07e07bff7def7de7bbf75ee7dc7b7f6ded51a233465eca992b0a5f4bd5782eb5ccb856e2d75a4b35642c357cae55a2af53ea3d3a2594928e514a2443e869051fa3ea7c0f59e63c2744e09bc35869cd119d330620c19732dc5a4b215f2b4528a29402764d89312123845c838f71ce330638c2164288438770b815c2904d07a0e01982e0520900f81a02a0400066fd53)
def r02l9 : Packing := (155,4,7,1,1,11,0,r02d9)
def r02d10 (i : Nat) : Nat := (if i<3 then (if i<1 then 0x6ff5a854e11bfd2a153846ff5a654e11ff560d53846ff5a814e11bfd69853846ff4a88ce11bfd29633847fd5838ce11ff558e33847fd5538ce11aff68c96a22bfca399a88aff28593a22bfda624e88aff69493a22bfda124e88affaa963a22bfca958e88ebf25963a23afe6658e88aff29563a23bdc9358e88aff69463a22bfeaa54e88aff2a553a22bfda654e88aff29953a23bdc9354e88aff28553a22bfda614e88aff68453a22bfca68ce88aff29633a23bdd638ce88ef754e33a22bfca18ce88aff68c91a22bfda318688ebf58c61a22bfeaa4c688aff2a531a22bfda64c688aff69531a22bfca54c688ef758d31a23bde334c688efd24531a22bfda50c688aff2a611a22bfca384688efd64611a23bf53184688bf7698988cefdda526233bf7684988cefdca6a2233bf7296888cfbdd85a2233bf7286888cfbdd81a2233bf76a0968cefdda525a33bf7aa9868cefdca961a33ef7a21868cfedc9661a33bf7695868cefdca561a33fb7595868cefdda161a33ef7605868cefdda521a33bf72a6668cefdca899a33fb761a668cefdca599a33fb7596668cefdda825633bf7698958cff5d8525633bf7684958cf7dda864c61df7695931877dd8564c61dfe5959020f7f98164083dfe5859020f7f95164083dfd6a19120f7f5a664483dfd6959120f7f56564483df76959321bbdca6a2233ef725a888cfbde66a2233ef7296888cfbdc95a2233cfda219121a7f5a126153be7690818ce7f9a0261539f76a4618cef9da418633dcf955941873de8864c618ff2a19654f7d63364486ef58ce11a2375e5564c61cfea219020e7dca960d53dbe9999020e5fda7261319dfaa99520f77a5564083cdfa219520e7bda4261539bf6989854e7dca960d63fd5846558cf67e6665483db78cc966077f211640839fdaa99120f75d8365483cfda219120e3feaa660619bf6a48399b6f666644838ff6a461a236bd9458c61cbfa2096607e5e6695633ddd9559120e7deaa64c86cf7a219321b6dd8664c86ddd8459520f75e5564c869bfaa99620f2fe8865883cbf58d981866fda6a6581d9f9559620f6dd83658839bf2a58658e6fca960666ebd8468899bed633846669fd6a4838473de3366061cefa219420f6be66650839fe6809858f6f61165883dcf9559420f1fe8865c839fd6849858eef5a624e11d3f9999720f3be88650619bf299936067f4a94c581cefa219421a7eda2261639ef6909858f73e5565086cefa219420773e5565081cfea21901877b611650839df6949858e7dda92163397f69c9858ef9da421633dbe5959018777a5564061eb78ce8899b6f96364061d7d8459720e7dda921a33df68cd90186f9da421a33cfba219220f6ee6664883cfea219021b76e5564883dde9559021bb5e8895633df68cd9021a7bda426131df98459220e7deaa64c61 else (if i<2 then 0x39ffaa99654e7fda8659539ff2a19654f3fca865953dbf6199654f6fe6665953bf7aa98354efdca960d53df7a658354fbdc9860d53ef7a218354f7dd9660d53fd76158354e7feaa645539ff2a19154f7f611645539ffaa99614e7fda865853dbf6199614f6fe66658539ff6a19114e7fda664453dfd6059114e7fda126233bf76a1638cfedd8658e33fb7999638cefdca558e33bf76a1538cefdda654e33bf7299538cff5d8554e33fd7955538cefdda54c6339ff69a996076fda6a65819ff68e996067fca3a65819ff686996077f5a1a6581aff69a886076fe9925981ebfa20966076fd9325981dbf24c96606bfeaa61981cffa6586607afd63619819ffaa9936073fe8864d81dbf299936067fda564d819ff295936077dd6364d81df78cd93606fdeaa61633bf72a5858cefdca661633bf7285858cefdda621633bf7684858cefdeaa59633bf72a5658cefdca859633fd7615658cefdda819633bf72a6558cefdca895633bf729a558cff5d8595633fd7596558cefdca195633bf76a0918cefdda524633bf7aa9818cefdca960633fb7299818cefdca560633ff5245818cefdeaa54633bf72a5518cefdda854633bf72a1518cff5d6554633fd7955518cefdda814633bf72a2118cefdca584633ff5546118ceefda326266bbf28e8899aefda824e66bbf6949399aefeaa60e66bbf2a58399bafe8860e66bbf2958399bedc9360e66bbf6948399aefda120e66bbfaa95399aefca954e66bbf6a15399aefca854e66fb760d5399aefda814e66bbf6845399aefca98ce66bbf2a23399aefca58ce66fb760e3399bedd538ce66bbfaa98199b6fca960666ebfa218199aefca360666bbfaa93199aefda84c666bbf2a13199aefda54c666bbf2953199bede334c666bfd6a093846ff5a524e11bfdaa9316077f6994c581efda2131607ef4964c581efd61931607ef6664c581bfd69531607f76554c581ff524d31607fd5634c581ff58cd31606ff4a884581efda22116077f59384581ff58ce116067fda564c81ddf955932077dd5364c81bfdaa9812067feaa66161cffa21985867fca3661619ffaa9935867fda864d619ff2a1935867fda564d619ff2959358777e5564d61df78cd93586ff6aa60561efda21815877f59360561ff58cd815873fd8366061df78cd981867fda864c619ff6959318777e5564c61df760d931877dd5364c61bbfaa9631876fd9858c61bbf69563187e7e5558c61fb760d63186ff6aa26211bfd68c98846ff4a9a2211efd26288846ff5a6a2211bfd68e88846ff4a3a2211bfdaa986847bf68861a11bfd28d86846ff6aa60e11bfd2a583847bf68860e11bfd29583847bf68820e11bfd69883846ff5a520e11ff560c83846ff6aa58e11bfd6a163846ff4a858e11fbd61963846ff4a558e11ff560d63846ff6aa54e11bfd2a55384 else 0x1a7fda564c86df754d9321a7fca6a65839ff2969960e7fca1a6583dbf5959620f6fd61658839ff6999520f77d6565483ddf5459520e7fda864483cffa219120e7fda6644839ff6959120f7f56164483dfd5459120e7fda8a65639ff2a29958e7fda5a65639ff2969958e7fda1a65639ffaa99858f3fe88661639ff2959858e7fda126163bbfaa98658eefca961963dbfa658658fafc9861963ebfa218658f6fd9899963dbf2566658efdeaa60d63bf72a58358f7de9960d63ef72618358fbde8860d63fb76198358fede6660d63bf7aa93158f7de994c563fb76193158e7feaa654639ff6a19518f77d8565463ddf9559518e7fda8a65539ff2a29954e7fda6a65539ff29a9954e7fda1a65539ff2869954e7feaa66153cffa219854e7fca6661539ff2859854e7fca999983bf728e6660e7fca94c586cff6609854eefda626153bef6909854eff5a126153bfe6809854e7fca9a2153bf728e8854ebfca865953bbf2999160f6fd9625953aff6a091a227fca961953bef6908654e7fca9999539ff6a58354e7fca9545839ff2a56354f6fc9658d53bdf2956354f7f591245539ff2a61154e7fca984583bbf299984c77bd9454c619ff2a5868cf6fc9661a339ff2a6668ce7fca94c688dfd24531a227fca961633ddf255858ce7fca9596339ff2a6558cf7bd9460c61def651532067fca954633bbf69a99606ff5a1a6581ef7596888cfbdc65a2233ef7956888cfbdca1a2233ef7246888cfbdd61a2233ef7186888cfbdd51a2233ef7146888cfbde11a2233dfe615901877f98364061dfe54d901877ed6564883dfb6059220f7ed6164883dfb5459220fedca98ce66fb72a23399bedc988ce66fb7a223399bedca58ce66fb72563399bedd858ce66fb72163399bede558ce66fb76063399bedd518ce66ff52a2118cffd49884633ff5a22118cffd58684633ff5296118cffd49584633ff5616118cffd48584633ff5596118cffd65584633def5959420f7bd8165083def5859420f7bd5165083efd2a611a23bf59684688efd28e11a23bf59384688efd24e11a23bf56384688efd54e11a23bf45384688efd8ce11a2377da665483ddf6859520f77d8165483ddf5859520f6fda565883dbf6859620f6fd8165883dbf5459620f5fd8165c83d7f5859720f7f95364086dfd54d9121bef68884666fbd60e1199bef48384666fbd54e1199bef45384666fbd8ce1199bf5ca995633fd7262558cff5e8895633fd725a558cff5d8695633fd721a558cff5e6695633fd7246558cff5d8195633fd7206558cff5d6195633fd7186558cff5e1195633cff68d981873fd5366061def61594187afca3a2266ebf24e8899bafd53a2266ebf14e8899bafe33a2266ebf4c68899b6fd8325981dbf54c966076fc5325981dbf8cc966067fca9545639ff6849854f3fd812615)) else (if i<5 then (if i<4 then 0x8971e9c617121c257059c076fe1be96f41bc16ea1b856dd9b676d11b2b6c71b036ba9adb6ae1aa96a69a8b69f1a6d6979a4f6901a316889a1368119f567999d767499cd66f99af668199166099736591955651993764a1919642990563d98e763618d363118b56299897622187961d1865615984760e1829606980b5ff17ed5f797cf5f017b15e8979d5e617895de97755d997575d217395ca971b5c597075be16e95b696cb5af16a35a5168559d9671596164958e962b587160d57d15e557315c756b959f5641577557954f54d9527546150953e94eb53714cd52a949b51e1455511942350013f14ee93a14e493794da935b4d313474ce13294c6930b4c192f74ba12d94b512c54b012b14a8929d4a3927f49c1261494924348d1225485920747e11e947691cb46f11ad46a11a3467918f4601171458915345111354499117444910343d10e543590c742e10a9426908b41f106d417904f412904540d902740610093fe8feb3f70fcd3ef8faf3ea8f9b3e30f7d3db8f693d90f553d18f373ca0f193c50f053c00ef13b88ed33b10ebf3ac0ea13a48e8339d0e653958e4738e0e333890e1f3840e0137c8de33700d9d3610d6b34f8d253408ce93340cb73278c7b31d8c7131b0c673160c2b2fa8bdb2e68b8b2df0b632d28b1d2be8ae12b20a9b2a30a692968a3728509e72760997262096f25309332468901232889d21e886b212082f20808071fb87cb1ea077b1d1072b1c206e51ae0681195063117e85eb17205af165858715b854114784dd13104a111f843310683f70f783cf0f0039d0d7034d0ca83070b902c10aa025d093823f08c01f907801c7064017705a014f050011303c00c3028007d019004100c80190003fdd8160d53bff68d5158f7fd53a6581bff29633606ffca884553dff5469960f7fc9661633bff68d5160f7fc9161633bff2961160ffde1160d53bff6a5536077fd9154583eff2a153606ffda154d81dff25a558ceffda126153dff615931877fd85a6531dff956994c7ff55360561dff54d98586ffca1a2153dff261518ceffca58cd61bff6a55160fff6554c581ffd615316077fe5564d81dff6069954f7fd61a6553dff8469954f7fd8564d81bff2a61154fbfd5361981fbf54c966077fd8166153dff5859854f7fe1166153ff75858354f7fc954c688d7f65d5120e7fca98cd81bfd28633606efca664d81df764c936067fda960d819ff2a5636067fca954d819ff2a611a22bfca884688cff6609858edfda726163bdf6949858efbda426163bfb6889858eff5a126163bfe6809858e7fda9545319ff2a68858eefca6a2163bf728e8858e7fda961963aff2a19558f77d95255639ff2a58558efbda4215639ff6a56558e7fca959563bf728d6558e7fca8a65319ff296994c67fda865431ddf615950c67fca164e889ff28e996 else 0xe003c007800f001e0020e0020e003c007800f00107001e003c007800f00123c3c007800f0010700107001e003c007800c142b0743e0e0516062d07c216452103d1083a291046104447c102d8c3f13841c86821504e10b229081b1545818000021810741be0e20203dc183a1ef040d980c083cc17062983a0d980808181e0e20170710081d0cb8307080df07100f83e085c1c4020781de0e0c2012107b83830603041de0e0c183bc1c1830781de0e0c200810781de0c35e081b30141e0f8217060fc183e0e201707060b8383040f03a0df060e141e0778383080f707100c0a083dc1c183e0ca010181e0e201707c1081de0e0c1f060dc4030741be0e20203a0df041183c5e0e0c103bc1c403e0c1f83060f03bc1c1840781915383834a26f07c109640778383060f03a0df060e1408082fc18403e0f821707c108050f0710081e0778383080f707060c1ee0c1dc8c1c06cdc1c1820778383060f41d060c1d06f8209c55e0c1e3f0646081e81a0c1f0710080a081010762383060f3060e83628838601020ef07100c1d88e0c183bc1c40307b838807c1c18206f820743915783078e040406081810781a14a0d848bc1c402e0f82103c0c8a9c1c1a581a0c10101e0e20101810781d84e0c203d09c1830741b84623203b09c1830761188c7c1f04206e1188c60206138305c1c402c4bb11fc443101c3cb0e3c3530c5c2db0a7c263089c1eb06bc17304dc0d301bc00aff3bf6afc1becafa3be52f85bddaf67bd62f3fbcc2f21bc22ef9bb5aebdba92e8bb9f2e6db97ae4fb88ae13b812dffb772db9b682d87b5e2d73b56ad41b4cad19b402ce7b33acb5b29ac97b1fac65b182c51b10ac29b06ac15b01abf7af7abc5aedaba7ae3ab6bad72b4dacfab1bac0aae9ab1aaa3aa52a85a9b2a53a8eaa17a7fa9efa75a9c7a6ba995a61a977a552945a4da927a48a913a4128f5a39a8d7a3228c3a2d289ba23287da1ba855a0f2823a02a7fb9f8a7d39eea7ab9e4a7839daa75b9d3273d9cba71f9c4270b9bca6e39b2a6b19a6268999c2657994a64398d262598325f397925d597425cb971a5a3965258595da567956253f94c2521944a50393aa4d1930a4b3929248191ca46d91a2463917a44f912a445910243b90da4138fc23cd8eaa3878dba34b8d1a3418cf23378ca23238c7a3198c5230f8c2a3058c022fb8bda2f18b8a2dd8b622d38b3a2ab8a2226f8932247890a23d88e223388ba229889221f87f21d986da19d85ea16184fa11b83ba0d582f2099825208f820207b81da07181b2067818a05d8162053813a03f80ea03580c202b809a0037f81fc77f09fbd7ee1fb37eb9fa97e41f6d7d51f3b7cb1f137be9ee17b21eb97a81e8779e1e697969e4b7919e377879e057789dd37711dab7649d7975a9d5174e1d1f73f1ced7379cd97329cbb72b1c9d7239c) else (if i<6 then 0x8b2115445131e16142180b220d822b864228c4b11442908a20a58f130a1104284840e08a9c1f04291005081e102349189c31522314c6200a020fc4e17001011c29885114c406045114c41c0a620e053109227082f1584050408089019884814c40074206078314c40404005840908aa1d8a070b0402840808aa2c0b8383c5818141024202878383052192021083b1485c1c18290d8f8205b180a1e0021c86821504e111e1a0a0b84c4e18942b080b0e462b080908482b08171585c00409083a9189c3e0020407800801b0f001e003c0040a0f0010036106c5312141e003c0078214840b09e2058551410160b80085c28080b085228080a088e280805082c2a8b800814101420d840808321006c2c080c086c2c08361604170a0202022a8b021583a1008f083c10302518aa21543a1034102420000552484e1836103c206041e0814105c561032101420e84090856290816140406040c0834143c3113860584000010c08000002101503e1c14290743e0c1a16060e8b2290c1e88454187221098f8205b1800001181000000000000008604000001d16452183d108a8364042131f040b630000000000003a1d8a4363e0816c60f4422a0d9010840e8b2290c3910840f4422a0e1e8205b183d1083a29118f10442a8b0206c5516060041e100000000000010c080000020a1483a1f060d0b031543e1000000002b0742e0e0f16062b09e20a856103410fc4e103a29083b1485c1866202c3c18a62e043f17001e0020487800801b0f002c081b16c40c092270c0b0f00105c4f102e2b0a080905c0045213841c868282037103c1f89c3e00304041c007800f001e00304041c0041713841886821538314c604040b0f00143c21889c2e0022589c2137831307c007800860080a831484e1700112c4e170627080908608789c3e003c007800f001e003c007800f001e0020d87800f001e003c0078008004287800f001e003c007800f001e003c0050c0f00106c247841c007800912107001e003c007800f001e0020e003c007800f001e003c00780083c1e003c007800f001e00244840083c214041c007800f0010783c00780083800f001e003c0041b086e10c837170010dc3c00401809c2220205860f0c1e183c22a8b02e003028862008c270b80081010e44e10ae1a080b08921a08090f001e003c0060f086e183c3028a42c0e0a0c142b0743e0e051607c006051583a1f07028b03e0022a03c0cf062997811145c0060a1605c007800f00107001e003c00780083800f001e0020e0020e003c0041c007800c1e1e003c0060f0f001e003c007800f001e003c007800f00122420003800f001e003c007800f001e003c00780083800f001e003c007800f001e003c007800f001e003c0048908004287800f001e003c007800f001e003c0048f083800f001e00244040 else 0x8a0d8a0f08a4122420d861b0a14106028284890a34105420a8445082a142821b05c28642910610c89890c1e208857098442841d0912106028e841b0)))
def r02l10 : Packing := (661,3,7,8,1,14,0,r02d10)
def r02d11 (i : Nat) : Nat := (if i<1 then 0x81d7c7241c106e41ac869219a4649188060917a45ae163856e153852514144ee13384ae125c46e113842e10383dc0ea83780d3c32f0c182dd0aac279094022707d41d5068c17104fc11603b40d602b407b01240200003ffb06b1fff64563ffea8ac7ffd3158fffb22c37ff61983fff33307ffd8518fffd32a9fff65583ffecc2a7ffd3161bff930a9fff61583fff442a7ffd9654fffb22c1fff25953ffe48d11ffd8654fff90ca9fff99953ffec1aa7ffd5160fffac6a9fff64553ffe28b07ffc9154fffa62c1fff4c553fff08aa7ffe1160fffb3098fff61853fff330a7ffd53587ffaa630fff20d61ffec3467ffe668cfffa63447ff61633ffeb2c67ffc658cfffcab19fff60d61fff442c3ffd83187ffaa640fff54633fff19ac3ffe99607ffa62c0fffa2181ffea8907ffd96607ffc66c0fff14d81ffec3303ffe9958fffb26c0fff14d61ffe49b03ffd9858fffb06c0fff20d81ffeb1b03ffd53607ffc23447ff26163ffea8a63ffe8858fffb0cb1fff65931ffec9b0dffd9558fff92ab1fff65531ffec2ac7ffc8558fffacab1fff65983bff4ca637fc984c6ff92a98dff66031bfeca8637fc98846ff92708ffd4c611bfecb5117fc96a22ffb27445ff24e88bfec8d117fc91a22ffd32c36ffa2186bfe49b0dbfe8821bdfb0c435ff64c86bfe4c4cdefd8699aff927335ffa6583dff443077fc9660eff92ac1dff24583dff441077fd9620effb2a41ff760c83bfec89077fe9958effb30b1dff26163f7ec32c7efe6658eff92ab1ff760d63fee98ac77fd9818effb2a31dffa6553bfecc2a77fc9854effb2ca9dff25953feec1aa77fd9154eff922a9dff66053bfecb0a77fd9114eff93119dff25a33bfe4ac67fdd838cffbac719ff754e33bfe48c67fdd318ceffd32c0effa2181f7e4b303bfd86606ffb26c0dff24d81feec2c67fdc858cffbacb19ff719633fef2ac67fdc918cffbb0319ff720633feeb0c67fdc618cffbaa319ff714633fef08c67efc9899bdfd11337bf24e66f7ec1ccdefc8399bdfaa7337bf14e66f7f19ccdefd8199bdfa63337fd24e11ffa98b03ff6116077fd1040dff64c81ffac09037fd98586ffb26b0ffd60561bfecc0c37fd93187dfac630ffd26211ffb44423ff586847feb0708ffd20e11ffab1c23ff553847fe8a708ffd8ce11dfecb511bfc96a237fccd446ff64e88dfe49d11bfd63a237f8c7446ff54e88dfe29d11bfe33a237fb23446ff24688dfeb0d11bfc61a237fa63446ff0c688dff08d11fdc988cffbd1119ff725a33feec3467fdc868cffbccd19ff725633beec98c37f99020efeb2241df764c86def444677bd9421af7b2840dfe64061bf6c9107ede3399bfac2319def65083dfb08d1177d9520edfb2c41d7f65c83bfcc810d7f59121bdec23337d7956339fecc0c37bd941875fd11335bf25981 else (if i<2 then 0x8aa230f1b04230f0c1012a94b07820d9707820d8c14104840a10ee0c3f0c20d4421e1950421d186c421f0e930654c10648188443ca983c1144e1887950af82c194cf0f0ee083655c1878e3007c20a81e2be0b0653487a1183101012185060a81bc160ca672a60c9420211706200d90362e0988081884c208b82c1940e162ae0f0458287b058329874366479485382c194cc0a0956121bc160cb6583a3c3245c160c9c60284a41d108c361904950425290883230f074a8130e14141048707820d8c361947e004250d865138010940a1c1e083232943f0454c1938c1d0dc3f0782293497831010a852c18808188794b058327181014486f0782206f048e1a26108fc160cb0847280708c0a8860c09a8061b47e0f044c186d4038460d4038460d40344c211f83c116108e500c3383500f04230f0e1f82c187882346083c8887e0f045c187d18344a221f83c1161489508e1f80508f0620160c40207a844300d864a582c1938e1a0ce0c4040ee0c3720206b06200d9307820e86c3c5221070620206089831010a852c18808450ce08461e2878358308864a1e0c953070d2868338310121f83c10f062012221f83c1120b83460f06201225110fc1e08a1a5088330fc028488f0e86f05830f181783500c3d83500c3c1d0de0c38505e014230da3f0782206d26a01a243783c1103aa1106f00a1187b061d51e0836605e0d4030f60d4030f60d4030da3f0782206d26a01e0d402c1e08363c1e0836309a8041b47e0f044c186d4038460d403060214430f06833831014321e060744250c87b001d10943a1bc188081bc1e0861d0de0c4040e86f062020783419c1880a190f6003a212a221f83c110328fc1e088190f6003a212a3f078218643d800e884a190f6003a2128643d800e884a1d0d8444640e86f0620260c40244c23078220783419c1880a1e0d0330620287a1f83c1103d83100e3f68f5a3b68e3636d8d3632d8c362e48b122ad8a36276891221b87ee1d286ca18985a61408482100831609c81f2065813a0257ff1fca7ea9f8a7dcdf4a7c61ef87b61eb87a19e5478d1e1477addb07641d5e74d5d15738dcc3728dc7a70fdc1f6ffdbdf6f21b9f6dd9b5f6d21b316c69af16b45aa86991a3b686d9fb67499b26649972654993264498e963258a0620184e604d8055f717b35e2977c5d717215c4d6d85b2968659e163d587560f57995b4562d55054c152253c14d053094b4529947d517543d50513eb4e9d3634c7d2c94a81292493922547f11d3463d15d44890e74365095416904c40b0ffa3f68fa83e68f8c3db0f3a3c20efa3b68e9f39b4e44386cde03748da93624d5734dcd1733dccce32b8c8e31b8c3c3070bfc2f70bb32e70b6a2d28b182be0ad82b04aaa2a4ca4f28989fd27509a225e4950249c8f5230c89121a084820c48081fa07d11e7c78 else 0x560d8f0a44078e4a63c108ca831c8b44052203c8c321878b0521a2882581c3e425c1c2610362c1036551d0caa58160064581940b022210437832a94a5830e96088f1616061bc014874447940b03c1e083a52223cb858186c7c8f2c12288f2c0caa1b2c0d1e452a14b0782323f01142c110a2c2c0d4655128caa2c006c3258260f00192c10a5098460d405c1a34a430c9489c39114848a20c309e4208a853839017061a2c0c8923298e1847290c54268428cac5c186f00522c1483132a8d290c290e10474814089a8c9551308281b0720290c881ec1c80a45c194a1e58260c34581a68a48fc0484a93901487051f93861a118649c40f41707820e948c450c96c60f23138783461486a2290b06591014890a840e0a64291384a2290942541120a62c186f0452207942541e0c40572a121e302a9488b83c11ca983469488442894c61a0c938644c186ca642407ca63078e49c30f12066344e0ca63c1144a83250649c31860b0654206d1c531a261183299036561e0f065291e083250f077065a0e064c09086b06200d90360f1086881dc186c404040706200c8f061e0ea8f041b302821b0f074a5830e181010e86f04272ae0c3c70287043222c83061e360b061e182021dc186e4040f60c3a200d943b831006c81d0de))
def r02l11 : Packing := (242,2,7,10,1,14,0,r02d11)
def r02d12 (i : Nat) : Nat := 0x20643e0e08a3634264041a19832020f0e8dc1c114783e0e0883a37064041e83201840dc1c110647a007484a101f070441b13201848441c1106c64248483633004240f838218e8dc190120c8043c3433064050f83821c1c108220e0861f07043b46aca1e5a8d6107cdce6857c57d3a454f034cae2646c13c3a07400ffd31ffc31ffe11ffe88ffd86ffc86ffe66ffd83ffc83ffd63ffc63ffd53ffc53ffe33ffd81ffc81ffd61ffc61ff611bfe88fde33efe66
def r02l12 : Packing := (22,1,7,8,1,10,0,r02d12)
def r02d13 (i : Nat) : Nat := 0x6085ff
def r02l13 : Packing := (1,0,7,5,1,0,0,r02d13)
def r02samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffff800080201e00000000000080000000180f800000000003fff0000000000000001d0000fc03807e00e0001800000000807f8001ffffff808000000ffff0000003fff0000003ffffff,0x880201f820111000000c1008022080fe111202200013e50800000000010001d00807402806e00a0000c00100100807580013fc609000000000ee63081008afc5800004296b012),(0xffffffffffffffffffffffffffffffffffffffffffffffff858080002000000060803f00000000a3f000000000fffffff008fc60fe00000801c000fc8c7f801f007fffffffffe100007fffe000007f000003fc000f000003ffffffffffffffff,0x59000002104000262803d4200148483d042200444a856c1a008bc70f742a158000000888467801b0073d79c06b268000010aad000226f520a5510000680011103ad50298b610564),(0x31003c00000000007c000000000240000000000fffc000007000100000000e2ffff00700000001f8060000000017f807ffe00000000000003f0000ffffffc000ffffffc000000,0x11003c12802440407c05405210824004400410857a8000005000000000000e2d83f00500000801d8024002004016d806f5410104400000082e00089f65620000a8d5212000200),(0x41fc203c0000000000f80000000000c7ffffffffff0000000618007e0000000f030000037f8001e01fff800000007e7fff80000000007ffffffc00000ffffffffff0000000000000,0x40bc243c0500241800e8084028063001e3c07d8670001014c608107e2c08c580010500112f920820021f040a431832123f008892a488150053180404268989c06ac80220e2022438),(0x41c0000000007f000000000000f80000000000000000081007800000000ffc000003800001ffe000000000007f800000000000007ffffffffffff00000000000000000000000,0x100049c2013088007f049058103800f00048020800612080091027804193000fe0101202c04401df4400051084204d240049101000006afface3f119c0d21200000b044302400040),(0x6007e00000000007fffffffffffff0000000000000000000fe007fffffffff000000003fffffe000000000000007fffffffffffffff800000000000000000000000000000000000,0x7e08810030602ff1de401e3fc0008040040f8005c001022000260e0007e000402403fd1f1002080a040307c07f3f0a0de0d038f01c00cf004011049c1c000308087c02004780),(0x78007fffffffffff800000000000000000000000000000000ffff8000000000000000003ffffffffffffffffffff8000000000000000000000000000000000000000000000000000,0x58207efcc700ff80084100405fc00000014047f0000600060ff34105081c0602480638237b983de46f0c2c23f80010382c0e00133f001084f000805e009fe0004c080f8002047800),(0x7fff800000000000000000000000000000000000000000000ffffffffffffffffffffffc000000000000000000000000000000000000000000000000000000000000000000000000,0x7ffe809011c0c00000000060600000010a707800008003180ddaffd9f1fff80f1d27c0fc020021080050063c000000003000001bc00020670000026000800002700c100003878000),(0x7ffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x2743810339ff0000500620ff800000fe0c7f800000f803e00004820081e0000492b800c000604010906057c0000000c04070011c0000407800030b8008e00003800fe00003f80000)]
def r02columns : IndexTree ColumnInfo := (.fork 46 (.fork 23 (.fork 11 (.fork 5 (.fork 2 (.leaf [(1,0,510,0,12),(4,0,507,0,12)]) (.leaf [(17,0,494,0,11),(132,0,379,0,11),(1,16,486,8,9)])) (.fork 3 (.leaf [(3,0,508,0,9),(4,128,347,32,9),(6,0,505,0,9)]) (.leaf [(12,0,499,0,9),(33,0,478,0,9),(65,0,446,0,9)]))) (.fork 6 (.fork 3 (.leaf [(257,0,254,0,8),(9,16,486,0,8),(19,0,492,0,8)]) (.leaf [(36,128,347,0,8),(67,0,444,0,8),(70,0,441,0,8)])) (.fork 3 (.leaf [(81,0,430,0,8),(134,0,377,0,8),(140,0,371,0,8)]) (.leaf [(161,0,350,0,8),(1,2,440,68,7),(1,32,94,384,7)])))) (.fork 11 (.fork 5 (.fork 2 (.leaf [(1,64,188,258,7),(4,8,227,272,7)]) (.leaf [(14,0,497,0,7),(35,0,476,0,7),(268,0,243,0,7)])) (.fork 3 (.leaf [(273,0,238,0,7),(289,0,222,0,7),(321,0,190,0,7)]) (.leaf [(324,0,187,0,7),(83,0,428,0,7),(156,0,355,0,7)]))) (.fork 6 (.fork 3 (.leaf [(177,0,334,0,7),(198,0,313,0,7),(3,64,188,256,6)]) (.leaf [(5,2,440,64,6),(12,64,177,258,6),(17,2,424,68,6)])) (.fork 3 (.leaf [(65,2,440,4,6),(65,32,30,384,6),(68,8,163,272,6)]) (.leaf [(97,0,414,0,6),(129,32,94,256,6),(132,8,99,272,6)]))))) (.fork 23 (.fork 11 (.fork 5 (.fork 2 (.leaf [(257,32,94,128,6),(257,64,188,2,6)]) (.leaf [(260,8,227,16,6),(259,0,188,0,5),(14,64,177,256,5)])) (.fork 3 (.leaf [(19,64,172,256,5),(21,2,424,64,5),(35,64,156,256,5)]) (.leaf [(41,16,454,0,5),(69,2,440,0,5),(73,16,422,0,5)]))) (.fork 6 (.fork 3 (.leaf [(78,0,433,0,5),(84,8,163,256,5),(145,32,78,256,5)]) (.leaf [(148,8,99,256,5),(193,2,312,4,5),(193,32,30,256,5)])) (.fork 3 (.leaf [(259,64,188,0,5),(262,64,185,0,5),(268,64,177,2,5)]) (.leaf [(273,64,172,2,5),(276,8,227,0,5),(289,64,156,2,5)])))) (.fork 12 (.fork 6 (.fork 3 (.leaf [(321,32,30,128,5),(323,0,188,0,5),(324,8,163,16,5)]) (.leaf [(332,0,179,0,5),(385,32,94,0,5),(388,8,99,16,5)])) (.fork 3 (.leaf [(270,0,177,0,4),(275,0,172,0,4),(291,0,156,0,4)]) (.leaf [(85,2,424,0,4),(102,128,281,0,4),(169,16,326,0,4)]))) (.fork 6 (.fork 3 (.leaf [(206,0,305,0,4),(270,64,177,0,4),(275,64,172,0,4)]) (.leaf [(291,64,156,0,4),(297,16,198,0,4),(329,16,166,0,4)])) (.fork 3 (.leaf [(334,0,177,0,4),(340,8,163,0,4),(355,0,156,0,4)]) (.leaf [(356,128,27,0,4),(401,32,78,0,4),(449,32,30,0,4)]))))))
def r02autos : Array (List Nat) := #[[],[32,83,116]]
def r02levels : Nat → Packing
  | 8 => r02l8
  | 9 => r02l9
  | 10 => r02l10
  | 11 => r02l11
  | 12 => r02l12
  | 13 => r02l13
  | _ => emptyPacking
def r02index : Nat → Nat → Option (Nat × Nat)
  | 8 => fun _ => none
  | 9 => lookupWord 2 11 4 6 1 1 (hashr02l9)
  | 10 => lookupWord 76 348 9 13 8 1 (hashr02l10)
  | 11 => lookupWord 300 1308 11 15 10 1 (hashr02l11)
  | 12 => lookupWord 126 574 10 13 8 1 (hashr02l12)
  | 13 => lookupWord 12 55 6 10 5 1 (hashr02l13)
  | _ => fun _ => none
def r02 : Forest := ⟨2559,13,fun j => r02samples[j]?.getD (0,0),r02columns,r02autos,r02levels,r02index⟩
set_option maxHeartbeats 0 in
theorem geomr02 : graphValid r02 (boundsBefore known383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=5) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr028_0 : block r02 8 0 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allr028 : block r02 8 0 2=true := sr028_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr029_0 : block r02 9 0 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr029_36 : block r02 9 36 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr029_72 : block r02 9 72 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr029_108 : block r02 9 108 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr029_144 : block r02 9 144 11=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allr029 : block r02 9 0 155=true := (@block_merge r02 9 0 144 11 (@block_merge r02 9 0 108 36 (@block_merge r02 9 0 72 36 (@block_merge r02 9 0 36 36 sr029_0 sr029_36) sr029_72) sr029_108) sr029_144)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0210_0 : block r02 10 0 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0210_36 : block r02 10 36 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0210_72 : block r02 10 72 24=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0210_96 : block r02 10 96 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0210_132 : block r02 10 132 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0210_168 : block r02 10 168 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0210_204 : block r02 10 204 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0210_240 : block r02 10 240 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0210_276 : block r02 10 276 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0210_312 : block r02 10 312 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0210_348 : block r02 10 348 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0210_384 : block r02 10 384 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0210_420 : block r02 10 420 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0210_456 : block r02 10 456 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0210_492 : block r02 10 492 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0210_528 : block r02 10 528 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0210_564 : block r02 10 564 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0210_600 : block r02 10 600 20=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0210_620 : block r02 10 620 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0210_656 : block r02 10 656 5=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allr0210 : block r02 10 0 661=true := (@block_merge r02 10 0 656 5 (@block_merge r02 10 0 620 36 (@block_merge r02 10 0 600 20 (@block_merge r02 10 0 564 36 (@block_merge r02 10 0 528 36 (@block_merge r02 10 0 492 36 (@block_merge r02 10 0 456 36 (@block_merge r02 10 0 420 36 (@block_merge r02 10 0 384 36 (@block_merge r02 10 0 348 36 (@block_merge r02 10 0 312 36 (@block_merge r02 10 0 276 36 (@block_merge r02 10 0 240 36 (@block_merge r02 10 0 204 36 (@block_merge r02 10 0 168 36 (@block_merge r02 10 0 132 36 (@block_merge r02 10 0 96 36 (@block_merge r02 10 0 72 24 (@block_merge r02 10 0 36 36 sr0210_0 sr0210_36) sr0210_72) sr0210_96) sr0210_132) sr0210_168) sr0210_204) sr0210_240) sr0210_276) sr0210_312) sr0210_348) sr0210_384) sr0210_420) sr0210_456) sr0210_492) sr0210_528) sr0210_564) sr0210_600) sr0210_620) sr0210_656)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0211_0 : block r02 11 0 24=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0211_24 : block r02 11 24 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0211_60 : block r02 11 60 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0211_96 : block r02 11 96 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0211_132 : block r02 11 132 28=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0211_160 : block r02 11 160 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0211_196 : block r02 11 196 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0211_232 : block r02 11 232 10=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allr0211 : block r02 11 0 242=true := (@block_merge r02 11 0 232 10 (@block_merge r02 11 0 196 36 (@block_merge r02 11 0 160 36 (@block_merge r02 11 0 132 28 (@block_merge r02 11 0 96 36 (@block_merge r02 11 0 60 36 (@block_merge r02 11 0 24 36 sr0211_0 sr0211_24) sr0211_60) sr0211_96) sr0211_132) sr0211_160) sr0211_196) sr0211_232)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0212_0 : block r02 12 0 4=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0212_4 : block r02 12 4 18=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allr0212 : block r02 12 0 22=true := (@block_merge r02 12 0 4 18 sr0212_0 sr0212_4)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sr0213_0 : block r02 13 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allr0213 : block r02 13 0 1=true := sr0213_0
theorem tablesr02 : checkedTables r02 13 := by
  intro k hk
  interval_cases k
  · exact (rfl : block r02 0 0 0 = true)
  · exact (rfl : block r02 1 0 0 = true)
  · exact (rfl : block r02 2 0 0 = true)
  · exact (rfl : block r02 3 0 0 = true)
  · exact (rfl : block r02 4 0 0 = true)
  · exact (rfl : block r02 5 0 0 = true)
  · exact (rfl : block r02 6 0 0 = true)
  · exact (rfl : block r02 7 0 0 = true)
  · exact allr028
  · exact allr029
  · exact allr0210
  · exact allr0211
  · exact allr0212
  · exact allr0213

def clippedInputs02 := inputs.map (fun a => a &&& ~~~seed02)
def clippedGraph02 := graph &&& ~~~seed02
def clippedPairs02 : List (Sig × Row × Row) := List.ofFn (fun i : Fin 9 =>
  (clippedInputs02.getD i.val zero, absentRow i, presentRow i))
theorem clippedLower02 (impossible : Impossible clippedGraph02 13 clippedInputs02.toFinset) :
    Lower clippedInputs02 clippedGraph02 14 := by
  apply lower_impossible (by unfold proper; decide +kernel) _ impossible
  have es : checkEssential clippedGraph02 clippedInputs02 clippedPairs02=true := by decide +kernel
  have all : clippedPairs02.map Prod.fst = clippedInputs02 := by decide +kernel
  intro a ha
  apply essential_ok es a
  exact List.mem_toFinset.mpr (all.symm ▸ ha)
theorem r02_start : Impossible clippedGraph02 13 clippedInputs02.toFinset := by
  have noRun := root_index (g:=r02) (before_sound known383 valid383) geomr02 tablesr02 (k:=13) (by decide)
    (i:=0) (ws:=clippedInputs02) (by decide +kernel)
  have tgt : targetOf r02 = clippedGraph02 := by decide +kernel
  exact tgt ▸ noRun
theorem bound02 (deadCase : Impossible graph 14 inputs.toFinset) :
    ∀ C : Circuit, PEqualNP.MetaComplexity.FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 2)) →
      PEqualNP.MetaComplexity.circuitFun 9 C = edge → 16 ≤ C.size := by
  intro C legal first h
  by_contra! small
  obtain ⟨k,t,hk,hdead | hlive⟩ := initial_live_gen 0 2 seed02 neighbor (by decide +kernel) (by decide +kernel) (by decide +kernel) C legal first h (by omega)
  · exact deadCase k t hk hdead
  · have sl := seedSlice_clipped seed02 (by decide +kernel) (by unfold proper; decide +kernel) (clippedLower02 r02_start)
    have noRun := poolCut_sound sl [] (by rfl) (ws:=inputs++[seed02])
      (by decide +kernel) (cap:=14) (by decide +kernel)
    exact noRun k t hk hlive

-- Orbits 4, 5, 6: (0,4), (1,4), (6,4) via low1007 and slice4
def d4 : Sig := ~~~(inputs.getD 4 zero)
def ms4 : List Move := fixRows 16 0 ++ [(zero,seed,9)]
def nbr04 (i : Fin 9) : Nat := [1,2,1,2,3,0,1,2,3].getD i.val 0

theorem slice4 : Slice inputs graph d4 13 :=
  slice_correct (ms:=ms4) (base:=vars 1007) (G:=graphGoal 1007) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide +kernel)) low1007

theorem bound04 (deadCase : Impossible graph 14 inputs.toFinset) :
    ∀ C : Circuit, PEqualNP.MetaComplexity.FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 4)) →
      PEqualNP.MetaComplexity.circuitFun 9 C = edge → 16 ≤ C.size := by
  intro C legal first h
  by_contra! small
  obtain ⟨k,t,hk,hdead | hlive⟩ := initial_live_gen 0 4 seed04 nbr04 (by decide +kernel) (by decide +kernel) (by decide +kernel) C legal first h (by omega)
  · exact deadCase k t hk hdead
  · have noRun := poolCut_sound slice4 [] (by rfl) (ws:=inputs++[seed04])
      (by decide +kernel) (cap:=14) (by decide +kernel)
    exact noRun k t hk hlive

theorem bound14 (deadCase : Impossible graph 14 inputs.toFinset) :
    ∀ C : Circuit, PEqualNP.MetaComplexity.FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 1 && y 4)) →
      PEqualNP.MetaComplexity.circuitFun 9 C = edge → 16 ≤ C.size := by
  intro C legal first h
  by_contra! small
  obtain ⟨k,t,hk,hdead | hlive⟩ := initial_live_gen 1 4 seed14 neighbor (by decide +kernel) (by decide +kernel) (by decide +kernel) C legal first h (by omega)
  · exact deadCase k t hk hdead
  · have noRun := poolCut_sound slice4 [] (by rfl) (ws:=inputs++[seed14])
      (by decide +kernel) (cap:=14) (by decide +kernel)
    exact noRun k t hk hlive

theorem bound64 (deadCase : Impossible graph 14 inputs.toFinset) :
    ∀ C : Circuit, PEqualNP.MetaComplexity.FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 6 && y 4)) →
      PEqualNP.MetaComplexity.circuitFun 9 C = edge → 16 ≤ C.size := by
  intro C legal first h
  by_contra! small
  obtain ⟨k,t,hk,hdead | hlive⟩ := initial_live_gen 6 4 seed64 neighbor (by decide +kernel) (by decide +kernel) (by decide +kernel) C legal first h (by omega)
  · exact deadCase k t hk hdead
  · have noRun := poolCut_sound slice4 [] (by rfl) (ws:=inputs++[seed64])
      (by decide +kernel) (cap:=14) (by decide +kernel)
    exact noRun k t hk hlive

-- Swap first two gates and route all 21 pairs via Petersen-9 automorphisms
def pairs21 : List (Fin 12 × Fin 12) :=
  [(0,1),(0,2),(0,3),(0,4),(0,6),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,3),(2,4),(2,6),(2,7),(2,8),(3,4),(3,6),(4,6),(6,7)]

def autPerms : List (List (Fin 9)) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8],
   [0, 5, 8, 3, 4, 1, 7, 6, 2],
   [1, 0, 5, 8, 6, 2, 4, 7, 3],
   [1, 2, 3, 8, 6, 0, 7, 4, 5],
   [2, 1, 0, 5, 7, 3, 6, 4, 8],
   [2, 3, 8, 5, 7, 1, 4, 6, 0],
   [3, 2, 1, 0, 4, 8, 7, 6, 5],
   [3, 8, 5, 0, 4, 2, 6, 7, 1],
   [5, 0, 1, 2, 7, 8, 4, 6, 3],
   [5, 8, 3, 2, 7, 0, 6, 4, 1],
   [8, 3, 2, 1, 6, 5, 4, 7, 0],
   [8, 5, 0, 1, 6, 3, 7, 4, 2]]

def autFn (j : Fin 12) (i : Fin 9) : Fin 9 := (autPerms.getD j.val []).getD i.val 0

def repList : List (Fin 9 × Fin 9) := [(0,1),(0,2),(0,3),(0,4),(1,4),(6,4)]

def mkVec (b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool) : Fin 9 → Bool
  | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3 | 4 => b4 | 5 => b5 | 6 => b6 | 7 => b7 | 8 => b8

theorem aut_preserves_bits : ∀ (j : Fin 12) (b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool),
    edge (mkVec b0 b1 b2 b3 b4 b5 b6 b7 b8 ∘ autFn j) = edge (mkVec b0 b1 b2 b3 b4 b5 b6 b7 b8) := by
  decide +kernel

theorem aut_preserves (j : Fin 12) (x : Fin 9 → Bool) : edge (x ∘ autFn j) = edge x := by
  have hx : x = mkVec (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) := by
    funext i; fin_cases i <;> rfl
  rw [hx]
  exact aut_preserves_bits j _ _ _ _ _ _ _ _ _

theorem route_exists : ∀ p ∈ pairs21,
    p.1.val < 9 ∧ p.2.val < 9 ∧
    ∃ j : Fin 12, ∃ q ∈ repList,
      (autFn j (Fin.ofNat 9 p.1.val) = q.1 ∧ autFn j (Fin.ofNat 9 p.2.val) = q.2) ∨
      (autFn j (Fin.ofNat 9 p.1.val) = q.2 ∧ autFn j (Fin.ofNat 9 p.2.val) = q.1) := by
  decide +kernel

theorem wires_relabel (f : Nat → Nat) (gs : List Gate) (W V : List Bool)
    (hlen : W.length = V.length) (hge : 11 ≤ W.length)
    (hf : ∀ i, 11 ≤ i → f i = i)
    (hf_lt : ∀ i, i < W.length → f i < V.length)
    (hagree : ∀ i, W.getD i false = V.getD (f i) false) :
    ∀ i, ((Circuit.mk gs 0).wires W).getD i false =
      ((Circuit.mk (gs.map fun g => ⟨g.op, g.inputs.map f⟩) 0).wires V).getD (f i) false := by
  induction gs generalizing W V with
  | nil => exact hagree
  | cons g gs ih =>
    let v := g.op.eval (g.inputs.map fun i => W.getD i false)
    have hv : g.op.eval ((g.inputs.map f).map fun i => V.getD i false) = v := by
      apply congrArg g.op.eval
      simp only [List.map_map, Function.comp_def]
      exact List.map_congr_left (fun i _ => (hagree i).symm)
    change ∀ i, ((Circuit.mk gs 0).wires (W ++ [v])).getD i false =
      ((Circuit.mk (gs.map fun g => ⟨g.op, g.inputs.map f⟩) 0).wires (V ++ [_])).getD (f i) false
    rw [hv]
    apply ih (W ++ [v]) (V ++ [v]) (by simp [hlen]) (by simp; omega)
    · intro i hi
      by_cases h1 : i < W.length
      · exact Nat.lt_trans (hf_lt i h1) (by simp)
      · have hge11 : 11 ≤ i := by omega
        rw [hf i hge11]
        simp only [List.length_append, List.length_singleton] at hi ⊢
        omega
    · intro i
      by_cases h1 : i < W.length
      · have h2 : f i < V.length := hf_lt i h1
        rw [List.getD_append _ _ _ _ h1, List.getD_append _ _ _ _ h2]
        exact hagree i
      · have hge11 : 11 ≤ i := by omega
        rw [hf i hge11, List.getD_append_right _ _ _ _ (by omega),
            List.getD_append_right _ _ _ _ (by omega), hlen]

theorem getD_ofFn9 (z : Fin 9 → Bool) (i : Fin 9) : (List.ofFn z).getD i.val false = z i := by
  rw [List.getD_eq_getElem _ _ (by simp [i.isLt]), List.getElem_ofFn]

theorem deadReady : Impossible graph 14 inputs.toFinset :=
  dead_start (before_sound known383 valid383) geomdead tablesdead

theorem core3275 : ∀ x1 ∈ [((0 : Fin (12 : ℕ)), (1 : Fin (12 : ℕ))), ((0 : Fin (12 : ℕ)), (2 : Fin (12 : ℕ))), ((0 : Fin (12 : ℕ)), (3 : Fin (12 : ℕ))), ((0 : Fin (12 : ℕ)), (4 : Fin (12 : ℕ))), ((0 : Fin (12 : ℕ)), (6 : Fin (12 : ℕ))), ((1 : Fin (12 : ℕ)), (2 : Fin (12 : ℕ))), ((1 : Fin (12 : ℕ)), (3 : Fin (12 : ℕ))), ((1 : Fin (12 : ℕ)), (4 : Fin (12 : ℕ))), ((1 : Fin (12 : ℕ)), (5 : Fin (12 : ℕ))), ((1 : Fin (12 : ℕ)), (6 : Fin (12 : ℕ))), ((1 : Fin (12 : ℕ)), (7 : Fin (12 : ℕ))), ((1 : Fin (12 : ℕ)), (8 : Fin (12 : ℕ))), ((2 : Fin (12 : ℕ)), (3 : Fin (12 : ℕ))), ((2 : Fin (12 : ℕ)), (4 : Fin (12 : ℕ))), ((2 : Fin (12 : ℕ)), (6 : Fin (12 : ℕ))), ((2 : Fin (12 : ℕ)), (7 : Fin (12 : ℕ))), ((2 : Fin (12 : ℕ)), (8 : Fin (12 : ℕ))), ((3 : Fin (12 : ℕ)), (4 : Fin (12 : ℕ))), ((3 : Fin (12 : ℕ)), (6 : Fin (12 : ℕ))), ((4 : Fin (12 : ℕ)), (6 : Fin (12 : ℕ))), ((6 : Fin (12 : ℕ)), (7 : Fin (12 : ℕ)))],   ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),     PEqualNP.MetaComplexity.FanInTwo x3 →       x3.size ≤ (13 : ℕ) →         ∃ (x6 : Fin (9 : ℕ) → Bool),           have x7 : List Bool := List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))];           have x8 : Fin (12 : ℕ) → Bool := fun (x8 : Fin (12 : ℕ)) => if x8 = (11 : Fin (12 : ℕ)) then Bool.true else x7.getD (↑x8) Bool.false;           x3.eval (x7 ++ [x8 x1.1 && x8 x1.2]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro x1 hx1 x3 hfan hsize
  by_contra hnot
  have heq : ∀ x6 : Fin 9 → Bool,
      have x7 : List Bool := List.ofFn x6 ++ [!x6 0]
      have x8 : Fin 12 → Bool := fun x8 => if x8 = 11 then true else x7.getD x8.val false
      x3.eval (x7 ++ [x8 x1.1 && x8 x1.2]) = edge x6 := by
    intro x6
    by_contra hne
    exact hnot ⟨x6, hne⟩
  obtain ⟨ha, hb, j, q, hq, hmap⟩ := route_exists x1 hx1
  let a : Fin 9 := Fin.ofNat 9 x1.1.val
  let b : Fin 9 := Fin.ofNat 9 x1.2.val
  have ha_val : a.val = x1.1.val := Nat.mod_eq_of_lt ha
  have hb_val : b.val = x1.2.val := Nat.mod_eq_of_lt hb
  let f : Nat → Nat := fun i =>
    if h : i < 9 then (autFn j ⟨i, h⟩).val
    else if i = 9 then 10
    else if i = 10 then 9
    else i
  let g0 : Gate := ⟨GateOp.and, [q.1.val, q.2.val]⟩
  let g1 : Gate := ⟨GateOp.not, [(autFn j 0).val]⟩
  let C' : Circuit := ⟨g0 :: g1 :: x3.gates.map (fun g => ⟨g.op, g.inputs.map f⟩), f x3.output⟩
  have hfan' : PEqualNP.MetaComplexity.FanInTwo C' := by
    intro g hg
    simp only [C', List.mem_cons, List.mem_map] at hg
    rcases hg with rfl | rfl | ⟨g', hg', rfl⟩
    · exact ⟨by simp [g0], by simp [g0]⟩
    · exact ⟨by simp [g1], by simp [g1]⟩
    · obtain ⟨hop, hlen⟩ := hfan g' hg'
      exact ⟨hop, by simpa using hlen⟩
  have hsize' : C'.size ≤ 15 := by
    simp only [Circuit.size, C', List.length_cons, List.length_map]
    change x3.gates.length ≤ 13 at hsize
    omega
  have hv0_fn (x : Fin 9 → Bool) :
      g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false) = (x q.1 && x q.2) := by
    simp only [g0, List.map_cons, List.map_nil, getD_ofFn9]
    change (x q.1 && (x q.2 && true)) = (x q.1 && x q.2)
    simp only [Bool.and_true]
  have hget9 (x : Fin 9 → Bool) : (C'.wires (List.ofFn x)).getD 9 false = (x q.1 && x q.2) := by
    change ((Circuit.mk (g1 :: x3.gates.map (fun g => ⟨g.op, g.inputs.map f⟩)) 0).wires
      (List.ofFn x ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false)])).getD 9 false = _
    rw [hv0_fn x]
    have hext : ∀ (gs : List Gate) (ws : List Bool), ∃ l, (Circuit.mk gs 0).wires ws = ws ++ l := by
      intro gs
      induction gs with
      | nil => intro ws; exact ⟨[], by simp [Circuit.wires]⟩
      | cons g gs ih =>
        intro ws
        obtain ⟨l, hl⟩ := ih (ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)])
        exact ⟨_ :: l, by simpa [Circuit.wires, List.append_assoc] using hl⟩
    obtain ⟨l, hl⟩ := hext (g1 :: x3.gates.map (fun g => ⟨g.op, g.inputs.map f⟩)) (List.ofFn x ++ [x q.1 && x q.2])
    rw [hl, List.getD_append _ _ _ _ (by simp), List.getD_append_right _ _ _ _ (by simp)]
    simp
  have hfun' : PEqualNP.MetaComplexity.circuitFun 9 C' = edge := by
    funext x
    let y : Fin 9 → Bool := x ∘ autFn j
    have hy := heq y
    have hv0 := hv0_fn x
    have hv1 : g1.op.eval (g1.inputs.map fun i => (List.ofFn x ++ [x q.1 && x q.2]).getD i false) = !(y 0) := by
      have hlt : (autFn j 0).val < (List.ofFn x).length := by simp [(autFn j 0).isLt]
      simp only [g1, List.map_cons, List.map_nil, List.getD_append _ _ _ _ hlt, getD_ofFn9]
      rfl
    have hq_eq : (x q.1 && x q.2) = (y a && y b) := by
      change (x q.1 && x q.2) = (x (autFn j a) && x (autFn j b))
      rcases hmap with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]
      · rw [h1, h2, Bool.and_comm]
    have hx8_1 : (if x1.1 = 11 then true else (List.ofFn y ++ [!y 0]).getD x1.1.val false) = y a := by
      have hne : x1.1 ≠ 11 := fun e => by have := congrArg Fin.val e; change x1.1.val = 11 at this; omega
      rw [if_neg hne, ←ha_val, List.getD_append _ _ _ _ (by simp [a.isLt]), getD_ofFn9]
    have hx8_2 : (if x1.2 = 11 then true else (List.ofFn y ++ [!y 0]).getD x1.2.val false) = y b := by
      have hne : x1.2 ≠ 11 := fun e => by have := congrArg Fin.val e; change x1.2.val = 11 at this; omega
      rw [if_neg hne, ←hb_val, List.getD_append _ _ _ _ (by simp [b.isLt]), getD_ofFn9]
    have hagree (i : Nat) :
        (List.ofFn y ++ [!y 0] ++ [y a && y b]).getD i false =
        (List.ofFn x ++ [x q.1 && x q.2] ++ [!y 0]).getD (f i) false := by
      by_cases h9 : i < 9
      · simp only [f, dif_pos h9]
        rw [List.append_assoc, List.getD_append _ _ _ _ (by simp [h9]),
            List.append_assoc, List.getD_append _ _ _ _ (by simp [(autFn j ⟨i, h9⟩).isLt])]
        have hgi : (List.ofFn y).getD i false = y ⟨i, h9⟩ := getD_ofFn9 y ⟨i, h9⟩
        rw [hgi, getD_ofFn9]
        rfl
      · by_cases hi9 : i = 9
        · subst hi9
          simp [f]
        · by_cases hi10 : i = 10
          · subst hi10
            simp [f, hq_eq]
          · have hge : 11 ≤ i := by omega
            have hfi : f i = i := by simp [f, h9, hi9, hi10]
            rw [hfi, List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    have hrel := wires_relabel f x3.gates
      (List.ofFn y ++ [!y 0] ++ [y a && y b])
      (List.ofFn x ++ [x q.1 && x q.2] ++ [!y 0])
      (by simp) (by simp)
      (fun i hi => by simp [f, show ¬i < 9 by omega, show i ≠ 9 by omega, show i ≠ 10 by omega])
      (fun i hi => by
        by_cases h9 : i < 9
        · simp only [f, dif_pos h9, List.length_append, List.length_ofFn, List.length_singleton]
          have := (autFn j ⟨i, h9⟩).isLt; omega
        · by_cases hi9 : i = 9
          · subst hi9; simp [f]
          · by_cases hi10 : i = 10
            · subst hi10; simp [f]
            · simp only [List.length_append, List.length_ofFn, List.length_singleton] at hi; omega)
      hagree x3.output
    have hev : PEqualNP.MetaComplexity.circuitFun 9 C' x =
        ((Circuit.mk (x3.gates.map fun g => ⟨g.op, g.inputs.map f⟩) 0).wires
          (List.ofFn x ++ [x q.1 && x q.2] ++ [!y 0])).getD (f x3.output) false := by
      change (C'.wires (List.ofFn x)).getD (f x3.output) false = _
      simp only [C', Circuit.wires, List.foldl_cons]
      rw [hv0, hv1]
    rw [hev, ←hrel]
    have hy' : x3.eval (List.ofFn y ++ [!y 0] ++ [y a && y b]) = edge y := by
      simpa only [hx8_1, hx8_2] using hy
    exact hy'.trans (aut_preserves j x)
  have hge16 : 16 ≤ C'.size := by
    simp only [repList, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound01 deadReady C' hfan' hget9 hfun'
    · exact bound02 deadReady C' hfan' hget9 hfun'
    · exact completedRoots deadReady C' hfan' hget9 hfun'
    · exact bound04 deadReady C' hfan' hget9 hfun'
    · exact bound14 deadReady C' hfan' hget9 hfun'
    · exact bound64 deadReady C' hfan' hget9 hfun'
  omega

end PEqualNP.Outside.L_meta_3275

theorem PEqualNP.Outside.L_meta_3275 : ∀ x1 ∈ [((0 : Fin (12 : ℕ)), (1 : Fin (12 : ℕ))), ((0 : Fin (12 : ℕ)), (2 : Fin (12 : ℕ))), ((0 : Fin (12 : ℕ)), (3 : Fin (12 : ℕ))), ((0 : Fin (12 : ℕ)), (4 : Fin (12 : ℕ))), ((0 : Fin (12 : ℕ)), (6 : Fin (12 : ℕ))), ((1 : Fin (12 : ℕ)), (2 : Fin (12 : ℕ))), ((1 : Fin (12 : ℕ)), (3 : Fin (12 : ℕ))), ((1 : Fin (12 : ℕ)), (4 : Fin (12 : ℕ))), ((1 : Fin (12 : ℕ)), (5 : Fin (12 : ℕ))), ((1 : Fin (12 : ℕ)), (6 : Fin (12 : ℕ))), ((1 : Fin (12 : ℕ)), (7 : Fin (12 : ℕ))), ((1 : Fin (12 : ℕ)), (8 : Fin (12 : ℕ))), ((2 : Fin (12 : ℕ)), (3 : Fin (12 : ℕ))), ((2 : Fin (12 : ℕ)), (4 : Fin (12 : ℕ))), ((2 : Fin (12 : ℕ)), (6 : Fin (12 : ℕ))), ((2 : Fin (12 : ℕ)), (7 : Fin (12 : ℕ))), ((2 : Fin (12 : ℕ)), (8 : Fin (12 : ℕ))), ((3 : Fin (12 : ℕ)), (4 : Fin (12 : ℕ))), ((3 : Fin (12 : ℕ)), (6 : Fin (12 : ℕ))), ((4 : Fin (12 : ℕ)), (6 : Fin (12 : ℕ))), ((6 : Fin (12 : ℕ)), (7 : Fin (12 : ℕ)))],   ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),     PEqualNP.MetaComplexity.FanInTwo x3 →       x3.size ≤ (13 : ℕ) →         ∃ (x6 : Fin (9 : ℕ) → Bool),           have x7 : List Bool := List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))];           have x8 : Fin (12 : ℕ) → Bool := fun (x8 : Fin (12 : ℕ)) => if x8 = (11 : Fin (12 : ℕ)) then Bool.true else x7.getD (↑x8) Bool.false;           x3.eval (x7 ++ [x8 x1.1 && x8 x1.2]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) :=
  PEqualNP.Outside.L_meta_3275.core3275
