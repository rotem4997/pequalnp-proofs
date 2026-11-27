import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_2946
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
def seed : Sig := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0

def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem seed_table : ∀ r : Row, bit r seed = (sample r 0 && sample r 2) := by decide +kernel
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
    (first : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 2))
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



def apart (m j : Nat) : Bool := m.testBit 9 && (j==0 || j==2)
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
  if f.testBit 9 && ((z ||| o) &&& 5) != 0 then f ^^^ 512 else f
def chartGoal (m : Nat) : Sig := graphGoal m
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
  if apart m j then v j &&& ~~~(v 0 &&& v 2) else v j
theorem seed_word : seed = inputs.getD 0 zero &&& inputs.getD 2 zero := by decide +kernel
theorem word_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow v i) (word m j.val) = (wordCol m v j.val).getLsbD i.val := by
  by_cases h : apart m j.val = true
  · have e := asRow_bit v i j
    have u := asRow_bit v i (0 : Fin 9)
    have w := asRow_bit v i (2 : Fin 9)
    change (inputs.getD j.val zero).getLsbD (asRow v i).val = _ at e
    change (inputs.getD 0 zero).getLsbD (asRow v i).val = (v 0).getLsbD i.val at u
    change (inputs.getD 2 zero).getLsbD (asRow v i).val = (v 2).getLsbD i.val at w
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
  rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a :=
  raw_faithful g.mask _ _

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) := liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := bit_liftGoal m v i
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
def g559d4 (i : Nat) : Nat := 0x1f
def g559l4 : Packing := (1,0,1,1,1,0,0,g559d4)
def g559samples : Array (Bits × Bits) := #[(0x145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145,0x861861861861861861861861861861861861861861861861861861861861861861861861861861861861861861861861861861861861861861861861861861861861861861861861861861861861861861861861861861861861861861861861),(0x3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf,0x186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186),(0xebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaeba,0x618618618618618618618618618618618618618618618618618618618618618618618618618618618618618618618618618618618618618618618618618618618618618618618618618618618618618618618618618618618618618618618618),(0xc30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30,0x9e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e7),(0x0,0x0),(0x0,0x79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g559columns : IndexTree ColumnInfo := (.leaf [])
def g559autos : Array (List Nat) := #[[],[32,83]]
def g559levels : Nat → Packing
  | 4 => g559l4
  | _ => emptyPacking
def g559index : Nat → Nat → Option (Nat × Nat)
  | 4 => fun _ => none
  | _ => fun _ => none
def g559 : Forest := ⟨559,4,fun j => g559samples[j]?.getD (0,0),g559columns,g559autos,g559levels,g559index⟩
set_option maxHeartbeats 0 in
theorem geom559 : graphValid g559 (boundsBefore known383) = true := by
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
  lower_forest (g:=g559) (i:=0) (hints:=8449) (before_sound known383 valid383) geom559 tables559 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps559 : List (Nat × List Nat) := [(559,[])]
def known559 := extendKnown known383 5 maps559
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid559 : Known known559 := extendKnown_ok valid383 low559 (by decide +kernel)
def g623d6 (i : Nat) : Nat := 0x48ff
def g623l6 : Packing := (1,0,2,1,1,0,0,g623d6)
def g623samples : Array (Bits × Bits) := #[(0x634563456345634563456345634563456345634563456345634563456345634563456345634563456345634563456345634563456345634563456345634563456345634563456345634563456345634563456345634563456345634563456345,0x284128412841284128412841284128412841284128412841284128412841284128412841284128412841284128412841284128412841284128412841284128412841284128412841284128412841284128412841284128412841284128412841),(0x858b858b858b858b858b858b858b858b858b858b858b858b858b858b858b858b858b858b858b858b858b858b858b858b858b858b858b858b858b858b858b858b858b858b858b858b858b858b858b858b858b858b858b858b858b858b858b858b,0x818281828182818281828182818281828182818281828182818281828182818281828182818281828182818281828182818281828182818281828182818281828182818281828182818281828182818281828182818281828182818281828182),(0x1c321c321c321c321c321c321c321c321c321c321c321c321c321c321c321c321c321c321c321c321c321c321c321c321c321c321c321c321c321c321c321c321c321c321c321c321c321c321c321c321c321c321c321c321c321c321c321c32,0x162016201620162016201620162016201620162016201620162016201620162016201620162016201620162016201620162016201620162016201620162016201620162016201620162016201620162016201620162016201620162016201620),(0x193819381938193819381938193819381938193819381938193819381938193819381938193819381938193819381938193819381938193819381938193819381938193819381938193819381938193819381938193819381938193819381938,0x299829982998299829982998299829982998299829982998299829982998299829982998299829982998299829982998299829982998299829982998299829982998299829982998299829982998299829982998299829982998299829982998),(0x0,0x0),(0x625c625c625c625c625c625c625c625c625c625c625c625c625c625c625c625c625c625c625c625c625c625c625c625c625c625c625c625c625c625c625c625c625c625c625c625c625c625c625c625c625c625c625c625c625c625c625c625c,0xc23cc23cc23cc23cc23cc23cc23cc23cc23cc23cc23cc23cc23cc23cc23cc23cc23cc23cc23cc23cc23cc23cc23cc23cc23cc23cc23cc23cc23cc23cc23cc23cc23cc23cc23cc23cc23cc23cc23cc23cc23cc23cc23cc23cc23cc23cc23cc23c),(0x829882988298829882988298829882988298829882988298829882988298829882988298829882988298829882988298829882988298829882988298829882988298829882988298829882988298829882988298829882988298829882988298,0x525852585258525852585258525852585258525852585258525852585258525852585258525852585258525852585258525852585258525852585258525852585258525852585258525852585258525852585258525852585258525852585258),(0x0,0x0),(0x0,0x0)]
def g623columns : IndexTree ColumnInfo := (.leaf [(64,0,559,512,5),(1,32,78,0,4),(4,8,99,0,4)])
def g623autos : Array (List Nat) := #[[],[32,83]]
def g623levels : Nat → Packing
  | 6 => g623l6
  | _ => emptyPacking
def g623index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | _ => fun _ => none
def g623 : Forest := ⟨623,6,fun j => g623samples[j]?.getD (0,0),g623columns,g623autos,g623levels,g623index⟩
set_option maxHeartbeats 0 in
theorem geom623 : graphValid g623 (boundsBefore known559) = true := by
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
theorem tables623 : checkedTables g623 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g623 0 0 0 = true)
  · exact (rfl : block g623 1 0 0 = true)
  · exact (rfl : block g623 2 0 0 = true)
  · exact (rfl : block g623 3 0 0 = true)
  · exact (rfl : block g623 4 0 0 = true)
  · exact (rfl : block g623 5 0 0 = true)
  · exact bl623_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low623 : Lower (vars 623) (graphGoal 623) 7 :=
  lower_forest (g:=g623) (i:=0) (hints:=16785665) (before_sound known559 valid559) geom623 tables623 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps623 : List (Nat × List Nat) := [(623,[])]
def known623 := extendKnown known559 7 maps623
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid623 : Known known623 := extendKnown_ok valid559 low623 (by decide +kernel)
def g535d3 (i : Nat) : Nat := 0xf
def g535l3 : Packing := (1,0,1,1,1,0,0,g535d3)
def g535samples : Array (Bits × Bits) := #[(0x5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5a,0x84210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108),(0xef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef,0xc6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6),(0xa5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5,0x318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c631),(0x0,0x0),(0x108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210,0xf7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g535columns : IndexTree ColumnInfo := (.leaf [])
def g535autos : Array (List Nat) := #[[]]
def g535levels : Nat → Packing
  | 3 => g535l3
  | _ => emptyPacking
def g535index : Nat → Nat → Option (Nat × Nat)
  | 3 => fun _ => none
  | _ => fun _ => none
def g535 : Forest := ⟨535,3,fun j => g535samples[j]?.getD (0,0),g535columns,g535autos,g535levels,g535index⟩
set_option maxHeartbeats 0 in
theorem geom535 : graphValid g535 (boundsBefore known623) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s535_3_0 : block g535 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl535_3 : block g535 3 0 1 = true := s535_3_0
theorem tables535 : checkedTables g535 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g535 0 0 0 = true)
  · exact (rfl : block g535 1 0 0 = true)
  · exact (rfl : block g535 2 0 0 = true)
  · exact bl535_3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low535 : Lower (vars 535) (graphGoal 535) 4 :=
  lower_forest (g:=g535) (i:=0) (hints:=257) (before_sound known623 valid623) geom535 tables535 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps535 : List (Nat × List Nat) := [(535,[]),(647,[32,83,116])]
def known535 := extendKnown known623 4 maps535
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid535 : Known known535 := extendKnown_ok valid623 low535 (by decide +kernel)
def g543d5 (i : Nat) : Nat := 0x85f
def g543l5 : Packing := (1,0,1,1,1,0,0,g543d5)
def g543samples : Array (Bits × Bits) := #[(0xd2a69534a9a54d2a69534a9a54d2a69534a9a54d2a69534a9a54d2a69534a9a54d2a69534a9a54d2a69534a9a54d2a69534a9a54d2a69534a9a54d2a69534a9a54d2a69534a9a54d2a69534a9a54d2a69534a9a54d2a69534a9a54d2a69534a9,0x93049824c126093049824c126093049824c126093049824c126093049824c126093049824c126093049824c126093049824c126093049824c126093049824c126093049824c126093049824c126093049824c126093049824c126093049824c1),(0xb49da4ed27693b49da4ed27693b49da4ed27693b49da4ed27693b49da4ed27693b49da4ed27693b49da4ed27693b49da4ed27693b49da4ed27693b49da4ed27693b49da4ed27693b49da4ed27693b49da4ed27693b49da4ed27693b49da4ed27,0x289944ca26513289944ca26513289944ca26513289944ca26513289944ca26513289944ca26513289944ca26513289944ca26513289944ca26513289944ca26513289944ca26513289944ca26513289944ca26513289944ca26513289944ca26),(0x25512a89544aa25512a89544aa25512a89544aa25512a89544aa25512a89544aa25512a89544aa25512a89544aa25512a89544aa25512a89544aa25512a89544aa25512a89544aa25512a89544aa25512a89544aa25512a89544aa25512a8954,0x444222111088844422211108884442221110888444222111088844422211108884442221110888444222111088844422211108884442221110888444222111088844422211108884442221110888444222111088844422211108884442221110),(0x9484a425212909484a425212909484a425212909484a425212909484a425212909484a425212909484a425212909484a425212909484a425212909484a425212909484a425212909484a425212909484a425212909484a425212909484a4252,0x11988cc46623311988cc46623311988cc46623311988cc46623311988cc46623311988cc46623311988cc46623311988cc46623311988cc46623311988cc46623311988cc46623311988cc46623311988cc46623311988cc46623311988cc466),(0x4e2a71538a9c54e2a71538a9c54e2a71538a9c54e2a71538a9c54e2a71538a9c54e2a71538a9c54e2a71538a9c54e2a71538a9c54e2a71538a9c54e2a71538a9c54e2a71538a9c54e2a71538a9c54e2a71538a9c54e2a71538a9c54e2a71538a,0x6c63631b18d8c6c63631b18d8c6c63631b18d8c6c63631b18d8c6c63631b18d8c6c63631b18d8c6c63631b18d8c6c63631b18d8c6c63631b18d8c6c63631b18d8c6c63631b18d8c6c63631b18d8c6c63631b18d8c6c63631b18d8c6c63631b18),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g543columns : IndexTree ColumnInfo := (.leaf [(4,0,27,0,4),(1,0,30,0,4)])
def g543autos : Array (List Nat) := #[[]]
def g543levels : Nat → Packing
  | 5 => g543l5
  | _ => emptyPacking
def g543index : Nat → Nat → Option (Nat × Nat)
  | 5 => fun _ => none
  | _ => fun _ => none
def g543 : Forest := ⟨543,5,fun j => g543samples[j]?.getD (0,0),g543columns,g543autos,g543levels,g543index⟩
set_option maxHeartbeats 0 in
theorem geom543 : graphValid g543 (boundsBefore known535) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s543_5_0 : block g543 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl543_5 : block g543 5 0 1 = true := s543_5_0
theorem tables543 : checkedTables g543 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g543 0 0 0 = true)
  · exact (rfl : block g543 1 0 0 = true)
  · exact (rfl : block g543 2 0 0 = true)
  · exact (rfl : block g543 3 0 0 = true)
  · exact (rfl : block g543 4 0 0 = true)
  · exact bl543_5
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low543 : Lower (vars 543) (graphGoal 543) 6 :=
  lower_forest (g:=g543) (i:=0) (hints:=8449) (before_sound known535 valid535) geom543 tables543 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps543 : List (Nat × List Nat) := [(543,[]),(679,[32,83,116])]
def known543 := extendKnown known535 6 maps543
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid543 : Known known543 := extendKnown_ok valid535 low543 (by decide +kernel)
def g527d3 (i : Nat) : Nat := 0xf
def g527l3 : Packing := (1,0,1,1,1,0,0,g527d3)
def g527samples : Array (Bits × Bits) := #[(0xa5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5,0x318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c631),(0xef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef,0xc6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6),(0x5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5a,0x84210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108),(0x108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210,0xf7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g527columns : IndexTree ColumnInfo := (.leaf [])
def g527autos : Array (List Nat) := #[[]]
def g527levels : Nat → Packing
  | 3 => g527l3
  | _ => emptyPacking
def g527index : Nat → Nat → Option (Nat × Nat)
  | 3 => fun _ => none
  | _ => fun _ => none
def g527 : Forest := ⟨527,3,fun j => g527samples[j]?.getD (0,0),g527columns,g527autos,g527levels,g527index⟩
set_option maxHeartbeats 0 in
theorem geom527 : graphValid g527 (boundsBefore known543) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s527_3_0 : block g527 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl527_3 : block g527 3 0 1 = true := s527_3_0
theorem tables527 : checkedTables g527 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g527 0 0 0 = true)
  · exact (rfl : block g527 1 0 0 = true)
  · exact (rfl : block g527 2 0 0 = true)
  · exact bl527_3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low527 : Lower (vars 527) (graphGoal 527) 4 :=
  lower_forest (g:=g527) (i:=0) (hints:=8449) (before_sound known543 valid543) geom527 tables527 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps527 : List (Nat × List Nat) := [(527,[]),(551,[32,83,116])]
def known527 := extendKnown known543 4 maps527
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid527 : Known known527 := extendKnown_ok valid543 low527 (by decide +kernel)
def g575key7 (i : Nat) : Nat := 0xd250202d05338112214d00000000000030700004d180014c00000014480a730cf90000c40000020300304025
def g575d7 (i : Nat) : Nat := 0x18d13f
def g575l7 : Packing := (1,0,3,5,1,0,0,g575d7)
def g575key6 (i : Nat) : Nat := 0x1a92300001a2000000044c06208a410020e4e00488
def g575d6 (i : Nat) : Nat := 0x311004201101180904062023110040202240100504401a1100001c7c2b9b0a39685786b62594c3f362920130e0900fea17f4cbfa83fd31fea07f4c3fa41fd10beaa6f913bc677d52dea17b88afaa3f611ee987e483da41fa00
def g575l6 : Packing := (20,1,3,4,1,8,0,g575d6)
def g575key5 (i : Nat) : Nat := 0x564ac0001e400000002
def g575d5 (i : Nat) : Nat := 0x6100000080610848108634178dd6a83c50500cf55142cf59542e718d42eb50932dd54531e719130e750930f650130eb50920f64c120
def g575l5 : Packing := (10,2,3,2,1,7,0,g575d5)
def g575key4 (i : Nat) : Nat := 0x58000
def g575d4 (i : Nat) : Nat := 0xfa50c3aca31a85665c06350ac6b90c898789424c120
def g575l4 : Packing := (4,3,3,1,1,4,0,g575d4)
def g575d3 (i : Nat) : Nat := 0x3065957018d42
def g575l3 : Packing := (1,4,3,1,1,0,0,g575d3)
def g575samples : Array (Bits × Bits) := #[(0x4714c568e298ad1c5315a38a62b4714c568e298ad1c5315a38a62b4714c568e298ad1c5315a38a62b4714c568e298ad1c5315a38a62b4714c568e298ad1c5315a38a62b4714c568e298ad1c5315a38a62b4714c568e298ad1c5315a38a62b471,0x432080486410090c82012190402432080486410090c82012190402432080486410090c82012190402432080486410090c82012190402432080486410090c82012190402432080486410090c82012190402432080486410090c82012190402432),(0x74c2928e985251d30a4a3a6149474c2928e985251d30a4a3a6149474c2928e985251d30a4a3a6149474c2928e985251d30a4a3a6149474c2928e985251d30a4a3a6149474c2928e985251d30a4a3a6149474c2928e985251d30a4a3a6149474c,0x34801b06900360d2006c1a400d834801b06900360d2006c1a400d834801b06900360d2006c1a400d834801b06900360d2006c1a400d834801b06900360d2006c1a400d834801b06900360d2006c1a400d834801b06900360d2006c1a400d8348),(0x986b12930d625261ac4a4c35894986b12930d625261ac4a4c35894986b12930d625261ac4a4c35894986b12930d625261ac4a4c35894986b12930d625261ac4a4c35894986b12930d625261ac4a4c35894986b12930d625261ac4a4c35894986,0x85e04810bc090217812042f024085e04810bc090217812042f024085e04810bc090217812042f024085e04810bc090217812042f024085e04810bc090217812042f024085e04810bc090217812042f024085e04810bc090217812042f024085),(0xeea9281dd52503baa4a07754940eea9281dd52503baa4a07754940eea9281dd52503baa4a07754940eea9281dd52503baa4a07754940eea9281dd52503baa4a07754940eea9281dd52503baa4a07754940eea9281dd52503baa4a07754940eea,0xe621231cc4246398848c7310918e621231cc4246398848c7310918e621231cc4246398848c7310918e621231cc4246398848c7310918e621231cc4246398848c7310918e621231cc4246398848c7310918e621231cc4246398848c7310918e62),(0x31822c26304584c608b098c116131822c26304584c608b098c116131822c26304584c608b098c116131822c26304584c608b098c116131822c26304584c608b098c116131822c26304584c608b098c116131822c26304584c608b098c1161318,0x10921ca212439442487288490e510921ca212439442487288490e510921ca212439442487288490e510921ca212439442487288490e510921ca212439442487288490e510921ca212439442487288490e510921ca212439442487288490e5109),(0x325c41464b8828c97105192e20a325c41464b8828c97105192e20a325c41464b8828c97105192e20a325c41464b8828c97105192e20a325c41464b8828c97105192e20a325c41464b8828c97105192e20a325c41464b8828c97105192e20a325,0x30596b860b2d70c165ae182cb5c30596b860b2d70c165ae182cb5c30596b860b2d70c165ae182cb5c30596b860b2d70c165ae182cb5c30596b860b2d70c165ae182cb5c30596b860b2d70c165ae182cb5c30596b860b2d70c165ae182cb5c305),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g575columns : IndexTree ColumnInfo := (.fork 2 (.leaf [(36,0,27,0,4),(1,32,30,0,4)]) (.leaf [(32,0,543,512,6),(24,0,551,512,4),(6,0,57,0,4)]))
def g575autos : Array (List Nat) := #[[]]
def g575levels : Nat → Packing
  | 3 => g575l3
  | 4 => g575l4
  | 5 => g575l5
  | 6 => g575l6
  | 7 => g575l7
  | _ => emptyPacking
def g575index : Nat → Nat → Option (Nat × Nat)
  | 3 => fun _ => none
  | 4 => lookupWord 1 4 1 6 1 1 (g575key4)
  | 5 => lookupWord 3 10 2 7 2 1 (g575key5)
  | 6 => lookupWord 6 18 2 9 4 1 (g575key6)
  | 7 => lookupWord 11 33 2 10 5 1 (g575key7)
  | _ => fun _ => none
def g575 : Forest := ⟨575,7,fun j => g575samples[j]?.getD (0,0),g575columns,g575autos,g575levels,g575index⟩
set_option maxHeartbeats 0 in
theorem geom575 : graphValid g575 (boundsBefore known527) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=2) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s575_7_0 : block g575 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl575_7 : block g575 7 0 1 = true := s575_7_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s575_6_0 : block g575 6 0 12=true := by
  apply cellsBlock (ar:=6) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s575_6_12 : block g575 6 12 8=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl575_6 : block g575 6 0 20 = true := (@block_merge g575 6 0 12 8 s575_6_0 s575_6_12)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s575_5_0 : block g575 5 0 10=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl575_5 : block g575 5 0 10 = true := s575_5_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s575_4_0 : block g575 4 0 4=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl575_4 : block g575 4 0 4 = true := s575_4_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s575_3_0 : block g575 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl575_3 : block g575 3 0 1 = true := s575_3_0
theorem tables575 : checkedTables g575 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g575 0 0 0 = true)
  · exact (rfl : block g575 1 0 0 = true)
  · exact (rfl : block g575 2 0 0 = true)
  · exact bl575_3
  · exact bl575_4
  · exact bl575_5
  · exact bl575_6
  · exact bl575_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low575 : Lower (vars 575) (graphGoal 575) 8 :=
  lower_forest (g:=g575) (i:=0) (hints:=8449) (before_sound known527 valid527) geom575 tables575 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps575 : List (Nat × List Nat) := [(575,[]),(687,[32,83,116])]
def known575 := extendKnown known527 8 maps575
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid575 : Known known575 := extendKnown_ok valid527 low575 (by decide +kernel)
def g813d4 (i : Nat) : Nat := 0x1f
def g813l4 : Packing := (1,0,1,1,1,0,0,g813d4)
def g813samples : Array (Bits × Bits) := #[(0x0,0xf1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e),(0x0,0x0),(0x8b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b1,0xc183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c1),(0xdbb76eddbb76eddbb76eddbb76eddbb76eddbb76eddbb76eddbb76eddbb76eddbb76eddbb76eddbb76eddbb76eddbb76eddbb76eddbb76eddbb76eddbb76eddbb76eddbb76eddbb76eddbb76eddbb76eddbb76eddbb76eddbb76eddbb76eddbb,0x93264c993264c993264c993264c993264c993264c993264c993264c993264c993264c993264c993264c993264c993264c993264c993264c993264c993264c993264c993264c993264c993264c993264c993264c993264c993264c993264c9932),(0x0,0x0),(0x244891224489122448912244891224489122448912244891224489122448912244891224489122448912244891224489122448912244891224489122448912244891224489122448912244891224489122448912244891224489122448912244,0xe1c3870e1c3870e1c3870e1c3870e1c3870e1c3870e1c3870e1c3870e1c3870e1c3870e1c3870e1c3870e1c3870e1c3870e1c3870e1c3870e1c3870e1c3870e1c3870e1c3870e1c3870e1c3870e1c3870e1c3870e1c3870e1c3870e1c3870e1),(0x0,0x0),(0x0,0x0),(0x74e9d3a74e9d3a74e9d3a74e9d3a74e9d3a74e9d3a74e9d3a74e9d3a74e9d3a74e9d3a74e9d3a74e9d3a74e9d3a74e9d3a74e9d3a74e9d3a74e9d3a74e9d3a74e9d3a74e9d3a74e9d3a74e9d3a74e9d3a74e9d3a74e9d3a74e9d3a74e9d3a74e,0x60c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c)]
def g813columns : IndexTree ColumnInfo := (.leaf [])
def g813autos : Array (List Nat) := #[[],[32,83]]
def g813levels : Nat → Packing
  | 4 => g813l4
  | _ => emptyPacking
def g813index : Nat → Nat → Option (Nat × Nat)
  | 4 => fun _ => none
  | _ => fun _ => none
def g813 : Forest := ⟨813,4,fun j => g813samples[j]?.getD (0,0),g813columns,g813autos,g813levels,g813index⟩
set_option maxHeartbeats 0 in
theorem geom813 : graphValid g813 (boundsBefore known575) = true := by
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
theorem tables813 : checkedTables g813 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g813 0 0 0 = true)
  · exact (rfl : block g813 1 0 0 = true)
  · exact (rfl : block g813 2 0 0 = true)
  · exact (rfl : block g813 3 0 0 = true)
  · exact bl813_4
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low813 : Lower (vars 813) (graphGoal 813) 5 :=
  lower_forest (g:=g813) (i:=0) (hints:=12884910853) (before_sound known575 valid575) geom813 tables813 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps813 : List (Nat × List Nat) := [(813,[])]
def known813 := extendKnown known575 5 maps813
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid813 : Known known813 := extendKnown_ok valid575 low813 (by decide +kernel)
def g815key7 (i : Nat) : Nat := 0x14a00000240000000016a0000001486c70002e13a3300001eb000000000004ec51361519d6600c16e00099d6c87860000001620000b204000
def g815d7 (i : Nat) : Nat := 0x120ff
def g815l7 : Packing := (1,0,2,4,1,0,0,g815d7)
def g815key6 (i : Nat) : Nat := 0xec0
def g815d6 (i : Nat) : Nat := 0x800020020800020202001a73a4c178dd7aa4a74a8d1003fa87fd51fe98ff543fa81fd30fe907f443fc017e55ef19fd847da41fa00
def g815l6 : Packing := (14,1,2,1,1,7,0,g815d6)
def g815d5 (i : Nat) : Nat := 0xbb18931
def g815l5 : Packing := (1,2,2,1,1,0,0,g815d5)
def g815samples : Array (Bits × Bits) := #[(0x82ade95055bd2a0ab7a54156f4a82ade95055bd2a0ab7a54156f4a82ade95055bd2a0ab7a54156f4a82ade95055bd2a0ab7a54156f4a82ade95055bd2a0ab7a54156f4a82ade95055bd2a0ab7a54156f4a82ade95055bd2a0ab7a54156f4a82a,0x321b9006437200c86e40190dc80321b9006437200c86e40190dc80321b9006437200c86e40190dc80321b9006437200c86e40190dc80321b9006437200c86e40190dc80321b9006437200c86e40190dc80321b9006437200c86e40190dc8032),(0xd4f1cc9a9e399353c7326a78e64d4f1cc9a9e399353c7326a78e64d4f1cc9a9e399353c7326a78e64d4f1cc9a9e399353c7326a78e64d4f1cc9a9e399353c7326a78e64d4f1cc9a9e399353c7326a78e64d4f1cc9a9e399353c7326a78e64d4f,0xc4d044589a088b1341116268222c4d044589a088b1341116268222c4d044589a088b1341116268222c4d044589a088b1341116268222c4d044589a088b1341116268222c4d044589a088b1341116268222c4d044589a088b1341116268222c4d),(0x790206af2040d5e4081abc81035790206af2040d5e4081abc81035790206af2040d5e4081abc81035790206af2040d5e4081abc81035790206af2040d5e4081abc81035790206af2040d5e4081abc81035790206af2040d5e4081abc81035790,0x380a0287014050e0280a1c05014380a0287014050e0280a1c05014380a0287014050e0280a1c05014380a0287014050e0280a1c05014380a0287014050e0280a1c05014380a0287014050e0280a1c05014380a0287014050e0280a1c05014380),(0xbd331217a66242f4cc485e99890bd331217a66242f4cc485e99890bd331217a66242f4cc485e99890bd331217a66242f4cc485e99890bd331217a66242f4cc485e99890bd331217a66242f4cc485e99890bd331217a66242f4cc485e99890bd,0x391196072232c0e446581c88cb0391196072232c0e446581c88cb0391196072232c0e446581c88cb0391196072232c0e446581c88cb0391196072232c0e446581c88cb0391196072232c0e446581c88cb0391196072232c0e446581c88cb039),(0x0,0x0),(0x6e9c02cdd38059ba700b374e0166e9c02cdd38059ba700b374e0166e9c02cdd38059ba700b374e0166e9c02cdd38059ba700b374e0166e9c02cdd38059ba700b374e0166e9c02cdd38059ba700b374e0166e9c02cdd38059ba700b374e0166e9,0x689e40cd13c819a27903344f206689e40cd13c819a27903344f206689e40cd13c819a27903344f206689e40cd13c819a27903344f206689e40cd13c819a27903344f206689e40cd13c819a27903344f206689e40cd13c819a27903344f206689),(0x0,0x0),(0x0,0x0),(0xb45037168a06e2d140dc5a281b8b45037168a06e2d140dc5a281b8b45037168a06e2d140dc5a281b8b45037168a06e2d140dc5a281b8b45037168a06e2d140dc5a281b8b45037168a06e2d140dc5a281b8b45037168a06e2d140dc5a281b8b45,0x9440a6128814c25102984a205309440a6128814c25102984a205309440a6128814c25102984a205309440a6128814c25102984a205309440a6128814c25102984a205309440a6128814c25102984a205309440a6128814c25102984a20530944)]
def g815columns : IndexTree ColumnInfo := (.leaf [(288,0,527,512,4),(264,0,551,512,4),(2,0,813,512,5)])
def g815autos : Array (List Nat) := #[[],[32,83]]
def g815levels : Nat → Packing
  | 5 => g815l5
  | 6 => g815l6
  | 7 => g815l7
  | _ => emptyPacking
def g815index : Nat → Nat → Option (Nat × Nat)
  | 5 => fun _ => none
  | 6 => lookupWord 2 6 1 6 1 1 (g815key6)
  | 7 => lookupWord 12 46 3 9 4 1 (g815key7)
  | _ => fun _ => none
def g815 : Forest := ⟨815,7,fun j => g815samples[j]?.getD (0,0),g815columns,g815autos,g815levels,g815index⟩
set_option maxHeartbeats 0 in
theorem geom815 : graphValid g815 (boundsBefore known813) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s815_7_0 : block g815 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl815_7 : block g815 7 0 1 = true := s815_7_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s815_6_0 : block g815 6 0 5=true := by
  apply cellsBlock (ar:=6) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s815_6_5 : block g815 6 5 9=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl815_6 : block g815 6 0 14 = true := (@block_merge g815 6 0 5 9 s815_6_0 s815_6_5)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s815_5_0 : block g815 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl815_5 : block g815 5 0 1 = true := s815_5_0
theorem tables815 : checkedTables g815 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g815 0 0 0 = true)
  · exact (rfl : block g815 1 0 0 = true)
  · exact (rfl : block g815 2 0 0 = true)
  · exact (rfl : block g815 3 0 0 = true)
  · exact (rfl : block g815 4 0 0 = true)
  · exact bl815_5
  · exact bl815_6
  · exact bl815_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low815 : Lower (vars 815) (graphGoal 815) 8 :=
  lower_forest (g:=g815) (i:=0) (hints:=12884910337) (before_sound known813 valid813) geom815 tables815 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps815 : List (Nat × List Nat) := [(815,[])]
def known815 := extendKnown known813 8 maps815
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid815 : Known known815 := extendKnown_ok valid813 low815 (by decide +kernel)
def g877key6 (i : Nat) : Nat := 0x3002200000
def g877d6 (i : Nat) : Nat := 0x48ff
def g877l6 : Packing := (1,0,2,1,1,0,0,g877d6)
def g877key5 (i : Nat) : Nat := 0x600
def g877d5 (i : Nat) : Nat := 0x43f950
def g877l5 : Packing := (1,1,2,1,1,0,0,g877d5)
def g877d4 (i : Nat) : Nat := 0xdc54550
def g877l4 : Packing := (1,2,2,1,1,0,0,g877d4)
def g877samples : Array (Bits × Bits) := #[(0xc6896344b1a258d12c6896344b1a258d12c6896344b1a258d12c6896344b1a258d12c6896344b1a258d12c6896344b1a258d12c6896344b1a258d12c6896344b1a258d12c6896344b1a258d12c6896344b1a258d12c6896344b1a258d12c6896,0xd18c68c634631a318d18c68c634631a318d18c68c634631a318d18c68c634631a318d18c68c634631a318d18c68c634631a318d18c68c634631a318d18c68c634631a318d18c68c634631a318d18c68c634631a318d18c68c634631a318d18c6),(0x0,0x0),(0x2056902b4815a40ad2056902b4815a40ad2056902b4815a40ad2056902b4815a40ad2056902b4815a40ad2056902b4815a40ad2056902b4815a40ad2056902b4815a40ad2056902b4815a40ad2056902b4815a40ad2056902b4815a40ad20569,0x2a7215390a9c854e42a7215390a9c854e42a7215390a9c854e42a7215390a9c854e42a7215390a9c854e42a7215390a9c854e42a7215390a9c854e42a7215390a9c854e42a7215390a9c854e42a7215390a9c854e42a7215390a9c854e42a721),(0xe04cf02678133c099e04cf02678133c099e04cf02678133c099e04cf02678133c099e04cf02678133c099e04cf02678133c099e04cf02678133c099e04cf02678133c099e04cf02678133c099e04cf02678133c099e04cf02678133c099e04cf,0xc404e202710138809c404e202710138809c404e202710138809c404e202710138809c404e202710138809c404e202710138809c404e202710138809c404e202710138809c404e202710138809c404e202710138809c404e202710138809c404e),(0x0,0x0),(0x46d3a369d1b4e8da746d3a369d1b4e8da746d3a369d1b4e8da746d3a369d1b4e8da746d3a369d1b4e8da746d3a369d1b4e8da746d3a369d1b4e8da746d3a369d1b4e8da746d3a369d1b4e8da746d3a369d1b4e8da746d3a369d1b4e8da746d3a,0x6518328c19460ca306518328c19460ca306518328c19460ca306518328c19460ca306518328c19460ca306518328c19460ca306518328c19460ca306518328c19460ca306518328c19460ca306518328c19460ca306518328c19460ca306518),(0x19640cb20659032c819640cb20659032c819640cb20659032c819640cb20659032c819640cb20659032c819640cb20659032c819640cb20659032c819640cb20659032c819640cb20659032c819640cb20659032c819640cb20659032c819640,0x89c544e2a2715138a89c544e2a2715138a89c544e2a2715138a89c544e2a2715138a89c544e2a2715138a89c544e2a2715138a89c544e2a2715138a89c544e2a2715138a89c544e2a2715138a89c544e2a2715138a89c544e2a2715138a89c54),(0x0,0x0),(0x993a4c9d264e93274993a4c9d264e93274993a4c9d264e93274993a4c9d264e93274993a4c9d264e93274993a4c9d264e93274993a4c9d264e93274993a4c9d264e93274993a4c9d264e93274993a4c9d264e93274993a4c9d264e93274993a4,0x302a18150c0a86054302a18150c0a86054302a18150c0a86054302a18150c0a86054302a18150c0a86054302a18150c0a86054302a18150c0a86054302a18150c0a86054302a18150c0a86054302a18150c0a86054302a18150c0a86054302a1)]
def g877columns : IndexTree ColumnInfo := (.leaf [(64,0,813,512,5),(33,0,332,0,4),(12,0,353,0,4)])
def g877autos : Array (List Nat) := #[[],[32,83]]
def g877levels : Nat → Packing
  | 4 => g877l4
  | 5 => g877l5
  | 6 => g877l6
  | _ => emptyPacking
def g877index : Nat → Nat → Option (Nat × Nat)
  | 4 => fun _ => none
  | 5 => lookupWord 1 4 1 6 1 1 (g877key5)
  | 6 => lookupWord 2 6 1 6 1 1 (g877key6)
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
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s877_4_0 : block g877 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl877_4 : block g877 4 0 1 = true := s877_4_0
theorem tables877 : checkedTables g877 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g877 0 0 0 = true)
  · exact (rfl : block g877 1 0 0 = true)
  · exact (rfl : block g877 2 0 0 = true)
  · exact (rfl : block g877 3 0 0 = true)
  · exact bl877_4
  · exact bl877_5
  · exact bl877_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low877 : Lower (vars 877) (graphGoal 877) 7 :=
  lower_forest (g:=g877) (i:=0) (hints:=13019128581) (before_sound known815 valid815) geom877 tables877 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps877 : List (Nat × List Nat) := [(877,[])]
def known877 := extendKnown known815 7 maps877
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid877 : Known known877 := extendKnown_ok valid815 low877 (by decide +kernel)
def g879key10 (i : Nat) : Nat := 0xc0644000000000000739c9ec828bab4454060001c10000091d0f0000d0000c00000000000000042fd4886d3e9aac003c84c400b29e980c0044800f0886b8e45000000037204002093020
def g879d10 (i : Nat) : Nat := 0x6b91ff
def g879l10 : Packing := (1,0,4,5,1,0,0,g879d10)
def g879key9 (i : Nat) : Nat := (if i<1 then 0x7e3780002acceddcf4dcc7d0000000000030e0000000e7931d122a6e00000000000b05bc0dbc957bc3a000073e96a172c51da3002907e2c36a6ead4e6e82d65455142a200024e8000000000e4280012b40000006788b0d029000470c0017cec6b2e757681b6d99f28fbb997784f8a3223e000841a2e000148e00023634ee66c02aca79256e2a540c2a8c0e1d848102fc8a9e65000000248e0000003d54000000000540c000000000456f06800082d8002988930d178001f649a32439132985a2c9e4370ac78d2af02ef2b4ba79e1e2080f48254b73de15c232c589045926a280000000000001904f580001e5c0000000459ce04787708002b7bad191c09f80000000006754000000000000000000000022b0000f834dd981260a000b5d3f3dc2d8884448003523686998c368000725ea99e13888000de280000017b3f8038dd686000df500000012a50000000000000fb8d8500000000006adc001e428589aec001aa0f494c60636000600745400076a0004d1e15600036db9700012c095100015825b959dc0aed2abc91a400014c3db59f1f92c00001800067070ec00000a80005c16e80112a2c000000000600800000000035500010300000002e9200000000008bc7a2d577ec166c4ce00061b824000086f80016203b80000000000000e2f9b1a31a00000034f13d162e000638800000000000007ac71e5a5000000000000059c95cc0000004390217bd796471ab065d44000435fb26000bb9d0f9e236260006c7283d3350001630000000d091abd108000b6668c4000000489c6c40000000000000000000f270000000000f9200000006ca0000000ca4b29a3a8002033a2814d610164c006a86584c14fda1975f4e5dc78cdf22d63c000000cdd4da0ce971a006a1a00000000000000000000000000000000078325f1e2e0000000002f380250002a600000e9435d1f5e50000fb6b13561179af1ed1b4000000010c1a5d9e000007f25ee1240e91b486b82e6dc00030418c799092400000006d000002d18e32a900002da98a98ea4da2fb10149929a0dbc275e1bc37f32446785011d8366c3e420a90af4c1a680b6126c28f5e32d000000000101100000000018730000242c874cbd1a8003d2c000ec2e67c00099b00000029268940004e67d1b16e1e58000000000f323d77a98a8f00006f80000004b179880000000000f87ecbc27b060b7820e201ec8d49e4474bdca87b1cd5a43916aa290ed2dbfeea514d4cc85696a00002948046081002800b1804008c000804000005084c01200558c000108411401b0c62188400000f0006300c4a0006000020004041800b004402800000440294070010000e3058d4209806020054800a524200800b000c01000000401080001a06330020080a600022100601088102c2b100014880000c2002c002144008400 else 0x50f93f5a4bc796ec3aa65e33200000010f9fa5c41092ba595560000000000000fa74dac0000000000003f247db00052cc5386a60000000000752dd200018cfa46b2cfaf3812378cac0001d6467f59c4b9623a00083027)
def g879d9 (i : Nat) : Nat := 0x34c15a4430112d5a7793040869923c8567691233642b434e62584b4a1ab49ac4de5030b44a2188b4ecd929d46226c3cad0622d25565a86997616d276ac9b324cd398961a56869888b2d273117666d273589bc977930ed958cd66ef255d923b6d23b56a8a0253899f9759ae605544b109370b42306e168460a014003fe66ff597fd63ff54ffd43ff587fc61ff547fd31ff847fd60ff543fd30ff483fd10bf99b7e55f78cff611fb483fa00
def g879l9 : Packing := (21,1,4,8,1,10,0,g879d9)
def g879key8 (i : Nat) : Nat := 0xe2dc24ea1b08cd170000000000873000000380644f6b90002af60000000000c160000000000000000000191c91400000030c0000e211b4800303f461e908000e3b5612098a1400000000000000000001260000891f0c00f4dc22165255af28d8646b33b05190800013f91980000f825d000080383633d68b0002cfbd087c00003804000841dd04cfc463b9c25a1e4943f93600026e3e22f879a0103ac2f08514406a44120000000000000000000000071c40d2d800000000000000001146f81908d0edf6cf3c2e19068c08c18f86000036b00025e400000000069d40afb2bc0c953000146b000409000dd070000003080000a2680000000000a6f4ee82a6640002845ade0000000001038000813800000000000001e90c00003060000001e8471d559c02ee8bab359dc2b9f02603f9b98cd67443d8d43857511a2b000020ca69000000241c000d9480036d40000001d1c105e05c137d94001f140000000000000c04800000145200065392dc000b2280008a800000000022c827088aa0e3a1c000000000000000052c98f26ba0000000ca002c0000000002d100000000000a64000829c0bb85295f000395563705bf16150aac720d643b1bf04a0000000002627e04000000000000000000000012434220002e8bd3022d5dd0ee77842a4f17a0d5585a33f8c8a5a220214743547be68f38a5b5e80f816aa51404b80000950003aea000000213a2fb479f32ec24000681c2c092a23f33c336e2240000004b10001ca2920000000000000000000000000006a180006025780004c6800133e00000008e5d2f01d800000000068c0000000000f938000e3244b40808a88fe000ebb80000000000000001a72000000697c000000407d62000114f79148502ec00000030d6402c370000000001a393933104000f7a00038f823dc623044200c000200002c8001060094a0100a001c220004100002380602806000000180250000308c8018c6108ca00800319465382e009400004201802b00c8b280003006000046000001844000000
def g879d8 (i : Nat) : Nat := (if i<1 then 0xa7b97a27917747637467297127076fc6f16e06d56c46b96ae6a369868d68266b65a6496386155fe5ed5ca5a759c57956e54b5345295064f54d84cd4b64ab48e47d47244f4384033f83c33b83ad38a37f37436335834d34834333e33933432f32431931430f30a2ff2e82b92ae29728c27526a24d22a21f2081eb1e01d51ca1bf1ae1a319218717c16b1601551441331221111000ef0de0c70b60a509408306c055044033022011000ffae2b2ffd70597feb22c7ff59153ffacaa1ffe77587febaac3ff59561ffae6b0ffd63587fea9ac3ff50d61ffae0b0ffd76547ff332a3ff5cd51ffac6a8ffd43547feb0aa3ff5c151ffaca98ffd644c7feaa263ff58531ffaa298ffd414c7ff33423ff59611ffac708ffd53847fea1c23ff5d560ffacab07fd73583feb1ac1ff54d60ffae4b07fd62583feb8ac1ff58560ffaa2b07fd31583ff08ac1ff9dd50ffaeca87fc76543ff332a1ff5cd50ffac6a87fd72543feb12a1ff5c550ff8e2a87fd61543fe30aa1ff4c550ffc22a87fd654c3feb0a61ff54530ffc22987fd76483ff33241ff5d520ffaca907fd71483feb0a41ff18520ffaa2907fe11483febb221ff99910ffaea887fd65443feb9a21ff58d10ffaa6887fd72443feb1221ff54910ffac2887fd51443fe98a21ff48510df8e3335fe775977f332cbdf99a55bfceeb1efe6658fbf2aac77f9dd53bfaeca9efe6654fbeb2aa7f758d53bfceea1dfd7650f7f332877f5d543efcaaa1fdd6350fef33467f759633fbac919fdd548ceff3bac3bf99961ef8eab0efd65587bf2aac3f78cd61bfaea30f7e55186feb98c3f78cc61bfae030dfe77546febb2a3bf99951fbc66a8ff561546ff3ba637f5d931dfccc98dfd754c7bf2aa637f5d131f7c8898fdd534c7eea1a63fd58531dfccd08f7e55847ef19c23fd58611feaa308ff531847fa3b423fd99a11feacb08ff563847faa9c23fd50e11bfceeb06fe66583bf2aac1f78cd60dfac4b06fd61583fb08ac17f9dd50bfaeca86fe66543bea9aa1f78cd50efaa4a877d51543fb08aa1fe58150bfcee985fd764c37f332617f5d530efcaa987dd534c3ee98a61fd84530ff2c0985fe77482febb241bf99920bfaea9077e55483fb08a41fe58120ff2a0907ee77483f6bb241fb1d920fdccc907ed75483f6b2a41fb5cd20fdac6907ed53483f6b8a41fb1c520fdac2907ec61483f6a8a41fb4c520fdc22905fe77442febb221bf99910bfaea8877e55442feb9a21f78cd10bfae4887f521443fb08a21fe54110ff240887fa66803fcb2c01fe58e00ff2a7007f962803fca9401fe58600ff0c3007f951803fc98c01fe48600ff4230067e669576f33467d795633f3c8919ef666847bb2ac23f58ce11bdcee906ee66483b72aa41f38cd20fcc22907e960483f490221be99a00ef4ab007da33803f511401fc84600 else 0x40084004200210a009608016d610608810c43cc2061159584000513610c110a1085082b2831d65063ac30075ac1944ac50c75b2484400228020c111408821c549220034922a4304748418dba491b748a92561d2b043a421365521845769142204008908c124210060c1181b180180918430400b6506324614638625870c628620c7116408020400020348586004508a4089584600200016c218220c1101b0c42856104285b243180408450030020043044084108608810c4084404318808631c21062843082b0a206114208810630020040080110308a00b3082ef958632c2103308214100600410c400490c218638a30831c6284508610d310a0c458c100196b0c458e18eb0c44805844ac3116b0c190b6490c958818c508a1142b082142d8620020040082104210402821d210a9085484210309ba4a48548e908430611401690c908a28c128909ba4a305ba430862d2484318368630449470c448a00640c228018c30d2b0c19090c4186d10908328a0903acba4928308042c13560c2acaa4042c15836865d6494609612c911612420000000161582000090940183a491810c200eb0421c31ac12c00c6b043081008dd218469560ac31230cb6c9200100208410b618860ac208008a16c314c114230825ab12d58ab644b08258614cd8ab2e91ad4896a44b5225a9116112330b246b5225a9137489ba44b522fd1fc6fb5fa4f93f82f77f6cf5bf4af39f16f05f00eefee4ed3ec2eb7eb2e9be84e6de50e39e1ce11e00defddedcddbcdb1da0d89d72d5bd4ad33d1cd0bce8ccbcbacafca4c93c8ec77c72c5bc56c45c3ac2fc18c01bf0bd9bc8bb7ba6b95b90b85b80b69b5eb53b42b31b20b1bb10b05af4ae3adeacdac2ab1aa6a8fa8aa7fa68a5da52a41a36a2ba1aa099fe9e79d09bf9a899d97a96f95894d94293792c9098f88e18d08c58b489d89288187685f84883182681b7fe7ed7c)
def g879l8 : Packing := (236,2,4,8,1,12,0,g879d8)
def g879key7 (i : Nat) : Nat := 0x2975d2a88b952bcb6c95000010c0000000b6f4608000000002300000006a00110e10834e6380003211b00
def g879d7 (i : Nat) : Nat := (if i<1 then 0xe10a10030800004100208108209b14200000005085080004004104104d8a1024821024831024821030830420000143882840002142b64801ab9225a104100100008008010308018400400001021000001010a1360c4006100000000004000001076ab920c11400000000000000000000000000000000c10800000000000000000000009432724bc9291b206374628bb1622644085b0a20e410808ffdf9bee7d2f91ec3d378eeedd7b9c72ee49c6b88706dddb5b666b4d39a1336646c7985b065e6bb96dacf578add592ad534a3944a7d4e295d222384588810da0f4147dcf59e63b4738e49c43706b0d39a233a660c61802da5a0ae1572a4534a414327c4c896928246478890ea1ca3806d8d61a2330638c217a2e0598ae1522904f89a12a240458861021f03b8720da1682a8500961182083c06e0c8168280460780c81401e02802800b7d859dd61d7d859dd619fd859dd619fd809dd61d7e771d561d7c755cd61e7d6554d61d7c755c1619fe885d9519fd8758551f748558531ef56558531f9d43505319fc8799a119fd87595609fd8758960e7c8558560ef56154560ef5614c5609fd869dd509fd829dd509fd819dd509fe885d950bed821d9509fc8799950d7d7654d50f5d6354d50d7d7254d50bf4815c950afd861c550bbd841c550bdd831c550bed821c5509fc8758550cfd76585509fd8718550b7d8518550bf98018550f756154550b7d854c550f5d534c5509fc8784550f795358150ef96258150f795258150ef96158150f795158150ef961581309fe885d920bf4815d5209fe885d520df4815d5209fd8759520cfd76585209fd8718520bf98018520d7d7554520df97558120fe96258120ef961581209fe885d910d7c855d9109fe885d5109fd87595109fe885c9109fd8758910cfd76589109fd8754910d7d75549109fd87585109fd87545109fd8748510df97654110f795354110f795254110ff08154110f795154110ff12154110df97648110bf98548110fe96248110fe92148110add831c666e5e6695633e9e6691233f1e559123397d859dd6197c87955619ed829dd31bf1801da11e766695611ed6668ce11f56558ce11f96448ce119bd849dd60ee96258120cee7799920be4815d520d6e7795520e6e6695520dce778cd20ece668cd20f4e558cd20aed861c520b6d851c520bad841c520bcd831c520be980185209ec874c520de67784520ee66684520f665584520fc63384520bea8858120dea7758120ee87658120eea6658120f6a5558120fca3358120ee96158120fe21158120fe12148110bea8848110dea7748110de97648110eea6648110f6a5548110fca3348110fe08148110fe21148110e7a6695600eda668ce00f5a558ce00be88788a00eea6688a00f6a5588a00ef26684600f725584600fd23384600fe22284600 else 0x2000016c20c08800400001061566440001)
def g879l7 : Packing := (140,3,4,4,1,11,0,g879d7)
def g879d6 (i : Nat) : Nat := 0x1b4200000000223f74d58233c64a0f1414045f6548799a118f6c910eb0aa1e696254960543ce2c2a8ac0a847d646885d520e74baac4b024117d95a2176442f632840aa0885f86488154110fb0a9242a8221ce976589204437c30a90a40885e86508148110
def g879l6 : Packing := (13,4,4,1,1,7,0,g879d6)
def g879samples : Array (Bits × Bits) := #[(0x2961e028a1570051f684900a58780a2855c0147da12402961e028a1570051f684900a58780a2855c0147da12402961e028a1570051f684900a58780a2855c0147da12402961e028a1570051f684900a58780a2855c0147da12402961e028a157,0x2c2163088067004140c4a10b0858c22019c01050312842c2163088067004140c4a10b0858c22019c01050312842c2163088067004140c4a10b0858c22019c01050312842c2163088067004140c4a10b0858c22019c01050312842c2163088067),(0x50cec00f0f8282ce8e08e2d433b003c3e0a0b3a38238b50cec00f0f8282ce8e08e2d433b003c3e0a0b3a38238b50cec00f0f8282ce8e08e2d433b003c3e0a0b3a38238b50cec00f0f8282ce8e08e2d433b003c3e0a0b3a38238b50cec00f0f82,0xd04480b60d8092889e18407411202d836024a22786101d04480b60d8092889e18407411202d836024a22786101d04480b60d8092889e18407411202d836024a22786101d04480b60d8092889e18407411202d836024a22786101d04480b60d80),(0x96881c43522804a008030e25a20710d48a01280200c3896881c43522804a008030e25a20710d48a01280200c3896881c43522804a008030e25a20710d48a01280200c3896881c43522804a008030e25a20710d48a01280200c3896881c435228,0x2881c4142184c2400021a00a2071050861309000086802881c4142184c2400021a00a2071050861309000086802881c4142184c2400021a00a2071050861309000086802881c4142184c2400021a00a2071050861309000086802881c414218),(0xee008340bcab072900138cbb8020d02f2ac1ca4004e32ee008340bcab072900138cbb8020d02f2ac1ca4004e32ee008340bcab072900138cbb8020d02f2ac1ca4004e32ee008340bcab072900138cbb8020d02f2ac1ca4004e32ee008340bcab,0xe4238138b8a302090c0184f908e04e2e28c0824300613e4238138b8a302090c0184f908e04e2e28c0824300613e4238138b8a302090c0184f908e04e2e28c0824300613e4238138b8a302090c0184f908e04e2e28c0824300613e4238138b8a3),(0x0,0x0),(0x83302875f8d01831f12450a0cc0a1d7e34060c7c4914283302875f8d01831f12450a0cc0a1d7e34060c7c4914283302875f8d01831f12450a0cc0a1d7e34060c7c4914283302875f8d01831f12450a0cc0a1d7e34060c7c4914283302875f8d0,0xc312007178900830b10250b0c4801c5e24020c2c40942c312007178900830b10250b0c4801c5e24020c2c40942c312007178900830b10250b0c4801c5e24020c2c40942c312007178900830b10250b0c4801c5e24020c2c40942c31200717890),(0x4071481b80fe03e01c821c101c5206e03f80f807208704071481b80fe03e01c821c101c5206e03f80f807208704071481b80fe03e01c821c101c5206e03f80f807208704071481b80fe03e01c821c101c5206e03f80f807208704071481b80f,0x6330501b01b003621c426818cc1406c06c00d887109a06330501b01b003621c426818cc1406c06c00d887109a06330501b01b003621c426818cc1406c06c00d887109a06330501b01b003621c426818cc1406c06c00d887109a06330501b01b),(0x0,0x0),(0x68115f9447c5ffc001f0411a0457e511f17ff0007c10468115f9447c5ffc001f0411a0457e511f17ff0007c10468115f9447c5ffc001f0411a0457e511f17ff0007c10468115f9447c5ffc001f0411a0457e511f17ff0007c10468115f9447c5,0x18485a840744f580403809061216a101d13d60100e02418485a840744f580403809061216a101d13d60100e02418485a840744f580403809061216a101d13d60100e02418485a840744f580403809061216a101d13d60100e02418485a840744)]
def g879columns : IndexTree ColumnInfo := (.fork 7 (.fork 3 (.leaf [(352,0,527,512,4),(328,0,551,512,4),(257,32,78,0,4)]) (.fork 2 (.leaf [(260,8,99,0,4),(256,0,623,512,7)]) (.leaf [(66,0,813,512,5),(64,0,815,512,8)]))) (.fork 3 (.leaf [(41,0,326,0,4),(37,0,330,0,4),(33,0,334,0,7)]) (.fork 2 (.leaf [(14,0,353,0,4),(12,0,355,0,7)]) (.leaf [(3,0,364,0,5),(2,0,877,512,7)]))))
def g879autos : Array (List Nat) := #[[],[32,83]]
def g879levels : Nat → Packing
  | 6 => g879l6
  | 7 => g879l7
  | 8 => g879l8
  | 9 => g879l9
  | 10 => g879l10
  | _ => emptyPacking
def g879index : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 16 53 4 10 5 1 (g879key10)
  | 6 => fun _ => none
  | 7 => lookupWord 11 33 4 9 4 1 (g879key7)
  | 8 => lookupWord 124 409 5 13 8 1 (g879key8)
  | 9 => lookupWord 202 606 5 13 8 1 (g879key9)
  | _ => fun _ => none
def g879 : Forest := ⟨879,10,fun j => g879samples[j]?.getD (0,0),g879columns,g879autos,g879levels,g879index⟩
set_option maxHeartbeats 0 in
theorem geom879 : graphValid g879 (boundsBefore known877) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s879_10_0 : block g879 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl879_10 : block g879 10 0 1 = true := s879_10_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s879_9_0 : block g879 9 0 6=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s879_9_6 : block g879 9 6 15=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl879_9 : block g879 9 0 21 = true := (@block_merge g879 9 0 6 15 s879_9_0 s879_9_6)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s879_8_0 : block g879 8 0 19=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s879_8_19 : block g879 8 19 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s879_8_55 : block g879 8 55 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s879_8_91 : block g879 8 91 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s879_8_127 : block g879 8 127 25=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s879_8_152 : block g879 8 152 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s879_8_188 : block g879 8 188 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s879_8_224 : block g879 8 224 12=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl879_8 : block g879 8 0 236 = true := (@block_merge g879 8 0 224 12 (@block_merge g879 8 0 188 36 (@block_merge g879 8 0 152 36 (@block_merge g879 8 0 127 25 (@block_merge g879 8 0 91 36 (@block_merge g879 8 0 55 36 (@block_merge g879 8 0 19 36 s879_8_0 s879_8_19) s879_8_55) s879_8_91) s879_8_127) s879_8_152) s879_8_188) s879_8_224)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s879_7_0 : block g879 7 0 36=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s879_7_36 : block g879 7 36 22=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s879_7_58 : block g879 7 58 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s879_7_94 : block g879 7 94 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s879_7_130 : block g879 7 130 10=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl879_7 : block g879 7 0 140 = true := (@block_merge g879 7 0 130 10 (@block_merge g879 7 0 94 36 (@block_merge g879 7 0 58 36 (@block_merge g879 7 0 36 22 s879_7_0 s879_7_36) s879_7_58) s879_7_94) s879_7_130)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s879_6_0 : block g879 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s879_6_1 : block g879 6 1 12=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl879_6 : block g879 6 0 13 = true := (@block_merge g879 6 0 1 12 s879_6_0 s879_6_1)
theorem tables879 : checkedTables g879 10 := by
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
  · exact bl879_10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low879 : Lower (vars 879) (graphGoal 879) 11 :=
  lower_forest (g:=g879) (i:=0) (hints:=12901687553) (before_sound known877 valid877) geom879 tables879 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps879 : List (Nat × List Nat) := [(879,[])]
def known879 := extendKnown known877 11 maps879
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid879 : Known known879 := extendKnown_ok valid877 low879 (by decide +kernel)
def g783d4 (i : Nat) : Nat := 0x1f
def g783l4 : Packing := (1,0,1,1,1,0,0,g783d4)
def g783samples : Array (Bits × Bits) := #[(0x252525252525252525252525252525252525252525252525252525252525252525252525252525252525252525252525252525252525252525252525252525252525252525252525252525252525252525252525252525252525252525252525,0x818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181),(0x6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f,0x666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666),(0xdadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadadada,0x181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818),(0x909090909090909090909090909090909090909090909090909090909090909090909090909090909090909090909090909090909090909090909090909090909090909090909090909090909090909090909090909090909090909090909090,0x878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878787878)]
def g783columns : IndexTree ColumnInfo := (.leaf [])
def g783autos : Array (List Nat) := #[[]]
def g783levels : Nat → Packing
  | 4 => g783l4
  | _ => emptyPacking
def g783index : Nat → Nat → Option (Nat × Nat)
  | 4 => fun _ => none
  | _ => fun _ => none
def g783 : Forest := ⟨783,4,fun j => g783samples[j]?.getD (0,0),g783columns,g783autos,g783levels,g783index⟩
set_option maxHeartbeats 0 in
theorem geom783 : graphValid g783 (boundsBefore known879) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s783_4_0 : block g783 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl783_4 : block g783 4 0 1 = true := s783_4_0
theorem tables783 : checkedTables g783 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g783 0 0 0 = true)
  · exact (rfl : block g783 1 0 0 = true)
  · exact (rfl : block g783 2 0 0 = true)
  · exact (rfl : block g783 3 0 0 = true)
  · exact bl783_4
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low783 : Lower (vars 783) (graphGoal 783) 5 :=
  lower_forest (g:=g783) (i:=0) (hints:=12884910337) (before_sound known879 valid879) geom783 tables783 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps783 : List (Nat × List Nat) := [(783,[]),(807,[32,83,116])]
def known783 := extendKnown known879 5 maps783
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid783 : Known known783 := extendKnown_ok valid879 low783 (by decide +kernel)
def g823key6 (i : Nat) : Nat := 0x0
def g823d6 (i : Nat) : Nat := 0xc0ff
def g823l6 : Packing := (1,0,2,1,1,0,0,g823d6)
def g823d5 (i : Nat) : Nat := 0x83ed20
def g823l5 : Packing := (1,1,2,1,1,0,0,g823d5)
def g823samples : Array (Bits × Bits) := #[(0x66c866c866c866c866c866c866c866c866c866c866c866c866c866c866c866c866c866c866c866c866c866c866c866c866c866c866c866c866c866c866c866c866c866c866c866c866c866c866c866c866c866c866c866c866c866c866c866c8,0x464046404640464046404640464046404640464046404640464046404640464046404640464046404640464046404640464046404640464046404640464046404640464046404640464046404640464046404640464046404640464046404640),(0x18d618d618d618d618d618d618d618d618d618d618d618d618d618d618d618d618d618d618d618d618d618d618d618d618d618d618d618d618d618d618d618d618d618d618d618d618d618d618d618d618d618d618d618d618d618d618d618d6,0x909490949094909490949094909490949094909490949094909490949094909490949094909490949094909490949094909490949094909490949094909490949094909490949094909490949094909490949094909490949094909490949094),(0x193219321932193219321932193219321932193219321932193219321932193219321932193219321932193219321932193219321932193219321932193219321932193219321932193219321932193219321932193219321932193219321932,0x292a292a292a292a292a292a292a292a292a292a292a292a292a292a292a292a292a292a292a292a292a292a292a292a292a292a292a292a292a292a292a292a292a292a292a292a292a292a292a292a292a292a292a292a292a292a292a292a),(0x0,0x0),(0x632063206320632063206320632063206320632063206320632063206320632063206320632063206320632063206320632063206320632063206320632063206320632063206320632063206320632063206320632063206320632063206320,0x293829382938293829382938293829382938293829382938293829382938293829382938293829382938293829382938293829382938293829382938293829382938293829382938293829382938293829382938293829382938293829382938),(0x853f853f853f853f853f853f853f853f853f853f853f853f853f853f853f853f853f853f853f853f853f853f853f853f853f853f853f853f853f853f853f853f853f853f853f853f853f853f853f853f853f853f853f853f853f853f853f853f,0x3e003e003e003e003e003e003e003e003e003e003e003e003e003e003e003e003e003e003e003e003e003e003e003e003e003e003e003e003e003e003e003e003e003e003e003e003e003e003e003e003e003e003e003e003e003e003e003e),(0x0,0x0),(0x0,0x0),(0xa1e5a1e5a1e5a1e5a1e5a1e5a1e5a1e5a1e5a1e5a1e5a1e5a1e5a1e5a1e5a1e5a1e5a1e5a1e5a1e5a1e5a1e5a1e5a1e5a1e5a1e5a1e5a1e5a1e5a1e5a1e5a1e5a1e5a1e5a1e5a1e5a1e5a1e5a1e5a1e5a1e5a1e5a1e5a1e5a1e5a1e5a1e5a1e5,0xf1c1f1c1f1c1f1c1f1c1f1c1f1c1f1c1f1c1f1c1f1c1f1c1f1c1f1c1f1c1f1c1f1c1f1c1f1c1f1c1f1c1f1c1f1c1f1c1f1c1f1c1f1c1f1c1f1c1f1c1f1c1f1c1f1c1f1c1f1c1f1c1f1c1f1c1f1c1f1c1f1c1f1c1f1c1f1c1f1c1f1c1f1c1f1c1)]
def g823columns : IndexTree ColumnInfo := (.leaf [(32,256,535,512,4),(16,0,807,512,5),(6,0,305,0,4)])
def g823autos : Array (List Nat) := #[[]]
def g823levels : Nat → Packing
  | 5 => g823l5
  | 6 => g823l6
  | _ => emptyPacking
def g823index : Nat → Nat → Option (Nat × Nat)
  | 5 => fun _ => none
  | 6 => lookupWord 1 4 1 6 1 1 (g823key6)
  | _ => fun _ => none
def g823 : Forest := ⟨823,6,fun j => g823samples[j]?.getD (0,0),g823columns,g823autos,g823levels,g823index⟩
set_option maxHeartbeats 0 in
theorem geom823 : graphValid g823 (boundsBefore known783) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s823_6_0 : block g823 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl823_6 : block g823 6 0 1 = true := s823_6_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s823_5_0 : block g823 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl823_5 : block g823 5 0 1 = true := s823_5_0
theorem tables823 : checkedTables g823 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g823 0 0 0 = true)
  · exact (rfl : block g823 1 0 0 = true)
  · exact (rfl : block g823 2 0 0 = true)
  · exact (rfl : block g823 3 0 0 = true)
  · exact (rfl : block g823 4 0 0 = true)
  · exact bl823_5
  · exact bl823_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low823 : Lower (vars 823) (graphGoal 823) 7 :=
  lower_forest (g:=g823) (i:=0) (hints:=21474836737) (before_sound known783 valid783) geom823 tables823 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps823 : List (Nat × List Nat) := [(823,[]),(911,[32,83,116])]
def known823 := extendKnown known783 7 maps823
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid823 : Known known823 := extendKnown_ok valid783 low823 (by decide +kernel)
def g797d4 (i : Nat) : Nat := 0x3f
def g797l4 : Packing := (1,0,1,1,1,0,0,g797d4)
def g797samples : Array (Bits × Bits) := #[(0x186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186186,0x28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a),(0x0,0x0),(0x451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451451,0x145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145),(0xe79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79,0xc30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30),(0x9a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a6,0x145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145145),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208,0x3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf)]
def g797columns : IndexTree ColumnInfo := (.leaf [(4,0,281,0,4)])
def g797autos : Array (List Nat) := #[[]]
def g797levels : Nat → Packing
  | 4 => g797l4
  | _ => emptyPacking
def g797index : Nat → Nat → Option (Nat × Nat)
  | 4 => fun _ => none
  | _ => fun _ => none
def g797 : Forest := ⟨797,4,fun j => g797samples[j]?.getD (0,0),g797columns,g797autos,g797levels,g797index⟩
set_option maxHeartbeats 0 in
theorem geom797 : graphValid g797 (boundsBefore known823) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s797_4_0 : block g797 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl797_4 : block g797 4 0 1 = true := s797_4_0
theorem tables797 : checkedTables g797 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g797 0 0 0 = true)
  · exact (rfl : block g797 1 0 0 = true)
  · exact (rfl : block g797 2 0 0 = true)
  · exact (rfl : block g797 3 0 0 = true)
  · exact bl797_4
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low797 : Lower (vars 797) (graphGoal 797) 5 :=
  lower_forest (g:=g797) (i:=0) (hints:=12884910852) (before_sound known823 valid823) geom797 tables797 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps797 : List (Nat × List Nat) := [(797,[]),(933,[32,83,116])]
def known797 := extendKnown known823 5 maps797
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid797 : Known known797 := extendKnown_ok valid823 low797 (by decide +kernel)
def g799key7 (i : Nat) : Nat := 0x311634c3d16c20034f0000021c0e1280092c000039042646d02d20010c00000d0400d228400000000008254c
def g799d7 (i : Nat) : Nat := 0x210d17f
def g799l7 : Packing := (1,0,3,5,1,0,0,g799d7)
def g799key6 (i : Nat) : Nat := 0xf1001345b2000054f0008
def g799d6 (i : Nat) : Nat := 0x40421101204c040a01184002200804c45462008040000d550ca45bf3cb631af28a41f99128e098704807f50ffa85fd32fea0ff4c7fa81fd30fe907f442faa9be44ef19df54b7a85ee22fb08fe483da41fa00
def g799l6 : Packing := (19,1,3,3,1,8,0,g799d6)
def g799key5 (i : Nat) : Nat := 0x38000
def g799d5 (i : Nat) : Nat := 0x28118461a23794280cf55142cf59542eb50932cf55141db54920eb50920
def g799l5 : Packing := (6,2,3,1,1,6,0,g799d5)
def g799d4 (i : Nat) : Nat := 0x51c7359542
def g799l4 : Packing := (1,3,3,1,1,0,0,g799d4)
def g799samples : Array (Bits × Bits) := #[(0x2a4acc8a92b322a4acc8a92b322a4acc8a92b322a4acc8a92b322a4acc8a92b322a4acc8a92b322a4acc8a92b322a4acc8a92b322a4acc8a92b322a4acc8a92b322a4acc8a92b322a4acc8a92b322a4acc8a92b322a4acc8a92b322a4acc8a92,0x2852060a148182852060a148182852060a148182852060a148182852060a148182852060a148182852060a148182852060a148182852060a148182852060a148182852060a148182852060a148182852060a148182852060a148182852060a14),(0x1fa00d47e80351fa00d47e80351fa00d47e80351fa00d47e80351fa00d47e80351fa00d47e80351fa00d47e80351fa00d47e80351fa00d47e80351fa00d47e80351fa00d47e80351fa00d47e80351fa00d47e80351fa00d47e80351fa00d47e8,0x17809905e026417809905e026417809905e026417809905e026417809905e026417809905e026417809905e026417809905e026417809905e026417809905e026417809905e026417809905e026417809905e026417809905e026417809905e0),(0xc43401710d005c43401710d005c43401710d005c43401710d005c43401710d005c43401710d005c43401710d005c43401710d005c43401710d005c43401710d005c43401710d005c43401710d005c43401710d005c43401710d005c43401710d,0x402c60500b181402c60500b181402c60500b181402c60500b181402c60500b181402c60500b181402c60500b181402c60500b181402c60500b181402c60500b181402c60500b181402c60500b181402c60500b181402c60500b181402c60500b),(0xfb97323ee5cc8fb97323ee5cc8fb97323ee5cc8fb97323ee5cc8fb97323ee5cc8fb97323ee5cc8fb97323ee5cc8fb97323ee5cc8fb97323ee5cc8fb97323ee5cc8fb97323ee5cc8fb97323ee5cc8fb97323ee5cc8fb97323ee5cc8fb97323ee5,0xbb11142ec4450bb11142ec4450bb11142ec4450bb11142ec4450bb11142ec4450bb11142ec4450bb11142ec4450bb11142ec4450bb11142ec4450bb11142ec4450bb11142ec4450bb11142ec4450bb11142ec4450bb11142ec4450bb11142ec4),(0x14ccd0c53334314ccd0c53334314ccd0c53334314ccd0c53334314ccd0c53334314ccd0c53334314ccd0c53334314ccd0c53334314ccd0c53334314ccd0c53334314ccd0c53334314ccd0c53334314ccd0c53334314ccd0c53334314ccd0c533,0x48ce9c1233a7048ce9c1233a7048ce9c1233a7048ce9c1233a7048ce9c1233a7048ce9c1233a7048ce9c1233a7048ce9c1233a7048ce9c1233a7048ce9c1233a7048ce9c1233a7048ce9c1233a7048ce9c1233a7048ce9c1233a7048ce9c123),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x254762c951d8b254762c951d8b254762c951d8b254762c951d8b254762c951d8b254762c951d8b254762c951d8b254762c951d8b254762c951d8b254762c951d8b254762c951d8b254762c951d8b254762c951d8b254762c951d8b254762c951,0x44e63c11398f044e63c11398f044e63c11398f044e63c11398f044e63c11398f044e63c11398f044e63c11398f044e63c11398f044e63c11398f044e63c11398f044e63c11398f044e63c11398f044e63c11398f044e63c11398f044e63c113)]
def g799columns : IndexTree ColumnInfo := (.fork 2 (.leaf [(272,0,527,512,4),(8,256,535,512,4)]) (.leaf [(256,0,543,512,6),(6,0,281,0,4),(1,0,286,0,5)]))
def g799autos : Array (List Nat) := #[[]]
def g799levels : Nat → Packing
  | 4 => g799l4
  | 5 => g799l5
  | 6 => g799l6
  | 7 => g799l7
  | _ => emptyPacking
def g799index : Nat → Nat → Option (Nat × Nat)
  | 4 => fun _ => none
  | 5 => lookupWord 1 4 1 6 1 1 (g799key5)
  | 6 => lookupWord 4 13 1 8 3 1 (g799key6)
  | 7 => lookupWord 10 33 2 10 5 1 (g799key7)
  | _ => fun _ => none
def g799 : Forest := ⟨799,7,fun j => g799samples[j]?.getD (0,0),g799columns,g799autos,g799levels,g799index⟩
set_option maxHeartbeats 0 in
theorem geom799 : graphValid g799 (boundsBefore known797) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=2) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s799_7_0 : block g799 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl799_7 : block g799 7 0 1 = true := s799_7_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s799_6_0 : block g799 6 0 10=true := by
  apply cellsBlock (ar:=6) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s799_6_10 : block g799 6 10 9=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl799_6 : block g799 6 0 19 = true := (@block_merge g799 6 0 10 9 s799_6_0 s799_6_10)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s799_5_0 : block g799 5 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl799_5 : block g799 5 0 6 = true := s799_5_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s799_4_0 : block g799 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl799_4 : block g799 4 0 1 = true := s799_4_0
theorem tables799 : checkedTables g799 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g799 0 0 0 = true)
  · exact (rfl : block g799 1 0 0 = true)
  · exact (rfl : block g799 2 0 0 = true)
  · exact (rfl : block g799 3 0 0 = true)
  · exact bl799_4
  · exact bl799_5
  · exact bl799_6
  · exact bl799_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low799 : Lower (vars 799) (graphGoal 799) 8 :=
  lower_forest (g:=g799) (i:=0) (hints:=12884910337) (before_sound known797 valid797) geom799 tables799 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps799 : List (Nat × List Nat) := [(799,[]),(935,[32,83,116])]
def known799 := extendKnown known797 8 maps799
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid799 : Known known799 := extendKnown_ok valid797 low799 (by decide +kernel)
def g831key9 (i : Nat) : Nat := 0x84030016c0000002d0
def g831d9 (i : Nat) : Nat := 0x96425073ff
def g831l9 : Packing := (1,0,4,2,1,0,0,g831d9)
def g831key8 (i : Nat) : Nat := 0x243361000000000000f00045d2008
def g831d8 (i : Nat) : Nat := 0x8a0c272c815baab4902e5ad249396b4902e5b4f0f00ff4c3de33fb483fa00
def g831l8 : Packing := (4,1,4,3,1,7,0,g831d8)
def g831key7 (i : Nat) : Nat := 0x200
def g831d7 (i : Nat) : Nat := 0x75c40002580f28502ff3ba617f5d130bfae4985ee77483e719a41f68ce00
def g831l7 : Packing := (6,2,4,1,1,6,0,g831d7)
def g831d6 (i : Nat) : Nat := 0x9bd849dd30
def g831l6 : Packing := (1,3,4,1,1,0,0,g831d6)
def g831samples : Array (Bits × Bits) := #[(0x459490e459490e459490e459490e459490e459490e459490e459490e459490e459490e459490e459490e459490e459490e459490e459490e459490e459490e459490e459490e459490e459490e459490e459490e459490e459490e459490e459,0x49891204989120498912049891204989120498912049891204989120498912049891204989120498912049891204989120498912049891204989120498912049891204989120498912049891204989120498912049891204989120498912049),(0xbc2154dbc2154dbc2154dbc2154dbc2154dbc2154dbc2154dbc2154dbc2154dbc2154dbc2154dbc2154dbc2154dbc2154dbc2154dbc2154dbc2154dbc2154dbc2154dbc2154dbc2154dbc2154dbc2154dbc2154dbc2154dbc2154dbc2154dbc2,0x382044d382044d382044d382044d382044d382044d382044d382044d382044d382044d382044d382044d382044d382044d382044d382044d382044d382044d382044d382044d382044d382044d382044d382044d382044d382044d382044d382),(0xa063270a063270a063270a063270a063270a063270a063270a063270a063270a063270a063270a063270a063270a063270a063270a063270a063270a063270a063270a063270a063270a063270a063270a063270a063270a063270a063270a06,0x814702081470208147020814702081470208147020814702081470208147020814702081470208147020814702081470208147020814702081470208147020814702081470208147020814702081470208147020814702081470208147020814),(0x52baf1152baf1152baf1152baf1152baf1152baf1152baf1152baf1152baf1152baf1152baf1152baf1152baf1152baf1152baf1152baf1152baf1152baf1152baf1152baf1152baf1152baf1152baf1152baf1152baf1152baf1152baf1152b,0x42a0f1942a0f1942a0f1942a0f1942a0f1942a0f1942a0f1942a0f1942a0f1942a0f1942a0f1942a0f1942a0f1942a0f1942a0f1942a0f1942a0f1942a0f1942a0f1942a0f1942a0f1942a0f1942a0f1942a0f1942a0f1942a0f1942a0f1942a),(0xbb00486bb00486bb00486bb00486bb00486bb00486bb00486bb00486bb00486bb00486bb00486bb00486bb00486bb00486bb00486bb00486bb00486bb00486bb00486bb00486bb00486bb00486bb00486bb00486bb00486bb00486bb00486bb0,0xb900084b900084b900084b900084b900084b900084b900084b900084b900084b900084b900084b900084b900084b900084b900084b900084b900084b900084b900084b900084b900084b900084b900084b900084b900084b900084b900084b90),(0xfac40a0fac40a0fac40a0fac40a0fac40a0fac40a0fac40a0fac40a0fac40a0fac40a0fac40a0fac40a0fac40a0fac40a0fac40a0fac40a0fac40a0fac40a0fac40a0fac40a0fac40a0fac40a0fac40a0fac40a0fac40a0fac40a0fac40a0fac,0xf244080f244080f244080f244080f244080f244080f244080f244080f244080f244080f244080f244080f244080f244080f244080f244080f244080f244080f244080f244080f244080f244080f244080f244080f244080f244080f244080f24),(0x0,0x0),(0x0,0x0),(0xd588e70d588e70d588e70d588e70d588e70d588e70d588e70d588e70d588e70d588e70d588e70d588e70d588e70d588e70d588e70d588e70d588e70d588e70d588e70d588e70d588e70d588e70d588e70d588e70d588e70d588e70d588e70d5,0xd180660d180660d180660d180660d180660d180660d180660d180660d180660d180660d180660d180660d180660d180660d180660d180660d180660d180660d180660d180660d180660d180660d180660d180660d180660d180660d180660d1)]
def g831columns : IndexTree ColumnInfo := (.fork 5 (.fork 2 (.leaf [(288,0,543,512,6),(0,256,535,552,6)]) (.leaf [(256,0,575,512,8),(0,32,30,769,6),(32,0,799,512,8)])) (.fork 2 (.leaf [(16,0,815,512,8),(8,0,823,512,7)]) (.leaf [(6,0,313,0,7),(0,2,312,517,6),(1,0,318,0,7)])))
def g831autos : Array (List Nat) := #[[]]
def g831levels : Nat → Packing
  | 6 => g831l6
  | 7 => g831l7
  | 8 => g831l8
  | 9 => g831l9
  | _ => emptyPacking
def g831index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 1 4 1 6 1 1 (g831key7)
  | 8 => lookupWord 4 14 1 8 3 1 (g831key8)
  | 9 => lookupWord 3 11 1 7 2 1 (g831key9)
  | _ => fun _ => none
def g831 : Forest := ⟨831,9,fun j => g831samples[j]?.getD (0,0),g831columns,g831autos,g831levels,g831index⟩
set_option maxHeartbeats 0 in
theorem geom831 : graphValid g831 (boundsBefore known799) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s831_9_0 : block g831 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl831_9 : block g831 9 0 1 = true := s831_9_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s831_8_0 : block g831 8 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s831_8_3 : block g831 8 3 1=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl831_8 : block g831 8 0 4 = true := (@block_merge g831 8 0 3 1 s831_8_0 s831_8_3)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s831_7_0 : block g831 7 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s831_7_3 : block g831 7 3 3=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl831_7 : block g831 7 0 6 = true := (@block_merge g831 7 0 3 3 s831_7_0 s831_7_3)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s831_6_0 : block g831 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl831_6 : block g831 6 0 1 = true := s831_6_0
theorem tables831 : checkedTables g831 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g831 0 0 0 = true)
  · exact (rfl : block g831 1 0 0 = true)
  · exact (rfl : block g831 2 0 0 = true)
  · exact (rfl : block g831 3 0 0 = true)
  · exact (rfl : block g831 4 0 0 = true)
  · exact (rfl : block g831 5 0 0 = true)
  · exact bl831_6
  · exact bl831_7
  · exact bl831_8
  · exact bl831_9
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low831 : Lower (vars 831) (graphGoal 831) 10 :=
  lower_forest (g:=g831) (i:=0) (hints:=12884910337) (before_sound known799 valid799) geom831 tables831 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps831 : List (Nat × List Nat) := [(831,[]),(943,[32,83,116])]
def known831 := extendKnown known799 10 maps831
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid831 : Known known831 := extendKnown_ok valid799 low831 (by decide +kernel)
def g855d6 (i : Nat) : Nat := 0x108ff
def g855l6 : Packing := (1,0,2,1,1,0,0,g855d6)
def g855samples : Array (Bits × Bits) := #[(0xab6356c6ad8d5b1ab6356c6ad8d5b1ab6356c6ad8d5b1ab6356c6ad8d5b1ab6356c6ad8d5b1ab6356c6ad8d5b1ab6356c6ad8d5b1ab6356c6ad8d5b1ab6356c6ad8d5b1ab6356c6ad8d5b1ab6356c6ad8d5b1ab6356c6ad8d5b1ab6356c6ad8d,0x3a227444e889d113a227444e889d113a227444e889d113a227444e889d113a227444e889d113a227444e889d113a227444e889d113a227444e889d113a227444e889d113a227444e889d113a227444e889d113a227444e889d113a227444e889),(0x664ccc999933326664ccc999933326664ccc999933326664ccc999933326664ccc999933326664ccc999933326664ccc999933326664ccc999933326664ccc999933326664ccc999933326664ccc999933326664ccc999933326664ccc999933,0x444888911122224444888911122224444888911122224444888911122224444888911122224444888911122224444888911122224444888911122224444888911122224444888911122224444888911122224444888911122224444888911122),(0x41c0838107020e041c0838107020e041c0838107020e041c0838107020e041c0838107020e041c0838107020e041c0838107020e041c0838107020e041c0838107020e041c0838107020e041c0838107020e041c0838107020e041c08381070,0x194032806500ca0194032806500ca0194032806500ca0194032806500ca0194032806500ca0194032806500ca0194032806500ca0194032806500ca0194032806500ca0194032806500ca0194032806500ca0194032806500ca019403280650),(0x0,0x0),(0x89b5136a26d44da89b5136a26d44da89b5136a26d44da89b5136a26d44da89b5136a26d44da89b5136a26d44da89b5136a26d44da89b5136a26d44da89b5136a26d44da89b5136a26d44da89b5136a26d44da89b5136a26d44da89b5136a26d4,0x819d033a06740ce819d033a06740ce819d033a06740ce819d033a06740ce819d033a06740ce819d033a06740ce819d033a06740ce819d033a06740ce819d033a06740ce819d033a06740ce819d033a06740ce819d033a06740ce819d033a0674),(0x0,0x0),(0xd093a127424e849d093a127424e849d093a127424e849d093a127424e849d093a127424e849d093a127424e849d093a127424e849d093a127424e849d093a127424e849d093a127424e849d093a127424e849d093a127424e849d093a127424e,0x8a8315062a0c5418a8315062a0c5418a8315062a0c5418a8315062a0c5418a8315062a0c5418a8315062a0c5418a8315062a0c5418a8315062a0c5418a8315062a0c5418a8315062a0c5418a8315062a0c5418a8315062a0c5418a8315062a0c),(0x0,0x0),(0x10d621ac435886b10d621ac435886b10d621ac435886b10d621ac435886b10d621ac435886b10d621ac435886b10d621ac435886b10d621ac435886b10d621ac435886b10d621ac435886b10d621ac435886b10d621ac435886b10d621ac4358,0x147428e851d0a3a147428e851d0a3a147428e851d0a3a147428e851d0a3a147428e851d0a3a147428e851d0a3a147428e851d0a3a147428e851d0a3a147428e851d0a3a147428e851d0a3a147428e851d0a3a147428e851d0a3a147428e851d0)]
def g855columns : IndexTree ColumnInfo := (.leaf [(64,256,535,512,4),(1,16,326,0,4),(4,0,339,0,5)])
def g855autos : Array (List Nat) := #[[]]
def g855levels : Nat → Packing
  | 6 => g855l6
  | _ => emptyPacking
def g855index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | _ => fun _ => none
def g855 : Forest := ⟨855,6,fun j => g855samples[j]?.getD (0,0),g855columns,g855autos,g855levels,g855index⟩
set_option maxHeartbeats 0 in
theorem geom855 : graphValid g855 (boundsBefore known831) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s855_6_0 : block g855 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl855_6 : block g855 6 0 1 = true := s855_6_0
theorem tables855 : checkedTables g855 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g855 0 0 0 = true)
  · exact (rfl : block g855 1 0 0 = true)
  · exact (rfl : block g855 2 0 0 = true)
  · exact (rfl : block g855 3 0 0 = true)
  · exact (rfl : block g855 4 0 0 = true)
  · exact (rfl : block g855 5 0 0 = true)
  · exact bl855_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low855 : Lower (vars 855) (graphGoal 855) 7 :=
  lower_forest (g:=g855) (i:=0) (hints:=25786581249) (before_sound known831 valid831) geom855 tables855 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps855 : List (Nat × List Nat) := [(855,[]),(967,[32,83,116])]
def known855 := extendKnown known831 7 maps855
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid855 : Known known855 := extendKnown_ok valid831 low855 (by decide +kernel)
def g861d5 (i : Nat) : Nat := 0x7f
def g861l5 : Packing := (1,0,1,1,1,0,0,g861d5)
def g861samples : Array (Bits × Bits) := #[(0x810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810,0x72e5cb972e5cb972e5cb972e5cb972e5cb972e5cb972e5cb972e5cb972e5cb972e5cb972e5cb972e5cb972e5cb972e5cb972e5cb972e5cb972e5cb972e5cb972e5cb972e5cb972e5cb972e5cb972e5cb972e5cb972e5cb972e5cb972e5cb972e),(0x0,0x0),(0x489122448912244891224489122448912244891224489122448912244891224489122448912244891224489122448912244891224489122448912244891224489122448912244891224489122448912244891224489122448912244891224489,0xc183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c1),(0x7af5ebd7af5ebd7af5ebd7af5ebd7af5ebd7af5ebd7af5ebd7af5ebd7af5ebd7af5ebd7af5ebd7af5ebd7af5ebd7af5ebd7af5ebd7af5ebd7af5ebd7af5ebd7af5ebd7af5ebd7af5ebd7af5ebd7af5ebd7af5ebd7af5ebd7af5ebd7af5ebd7af,0x70e1c3870e1c3870e1c3870e1c3870e1c3870e1c3870e1c3870e1c3870e1c3870e1c3870e1c3870e1c3870e1c3870e1c3870e1c3870e1c3870e1c3870e1c3870e1c3870e1c3870e1c3870e1c3870e1c3870e1c3870e1c3870e1c3870e1c3870e),(0xa142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a14,0x8d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1),(0x0,0x0),(0x40810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040,0xfdfbf7efdfbf7efdfbf7efdfbf7efdfbf7efdfbf7efdfbf7efdfbf7efdfbf7efdfbf7efdfbf7efdfbf7efdfbf7efdfbf7efdfbf7efdfbf7efdfbf7efdfbf7efdfbf7efdfbf7efdfbf7efdfbf7efdfbf7efdfbf7efdfbf7efdfbf7efdfbf7efdf),(0x0,0x0),(0x162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162,0x20408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020)]
def g861columns : IndexTree ColumnInfo := (.leaf [(64,0,797,512,5)])
def g861autos : Array (List Nat) := #[[]]
def g861levels : Nat → Packing
  | 5 => g861l5
  | _ => emptyPacking
def g861index : Nat → Nat → Option (Nat × Nat)
  | 5 => fun _ => none
  | _ => fun _ => none
def g861 : Forest := ⟨861,5,fun j => g861samples[j]?.getD (0,0),g861columns,g861autos,g861levels,g861index⟩
set_option maxHeartbeats 0 in
theorem geom861 : graphValid g861 (boundsBefore known855) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s861_5_0 : block g861 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl861_5 : block g861 5 0 1 = true := s861_5_0
theorem tables861 : checkedTables g861 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g861 0 0 0 = true)
  · exact (rfl : block g861 1 0 0 = true)
  · exact (rfl : block g861 2 0 0 = true)
  · exact (rfl : block g861 3 0 0 = true)
  · exact (rfl : block g861 4 0 0 = true)
  · exact bl861_5
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low861 : Lower (vars 861) (graphGoal 861) 6 :=
  lower_forest (g:=g861) (i:=0) (hints:=13019128580) (before_sound known855 valid855) geom861 tables861 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps861 : List (Nat × List Nat) := [(861,[]),(997,[32,83,116])]
def known861 := extendKnown known855 6 maps861
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid861 : Known known861 := extendKnown_ok valid855 low861 (by decide +kernel)
def g863key9 (i : Nat) : Nat := 0x11e4e50000000000005300d6b200008
def g863d9 (i : Nat) : Nat := 0x54332ff
def g863l9 : Packing := (1,0,3,3,1,0,0,g863d9)
def g863key8 (i : Nat) : Nat := 0x20000036a2352100f3003400000000c0
def g863d8 (i : Nat) : Nat := 0xfcc6026e63012a535988723984c1cc1d63a0eb250759259f560eca85403fd63ff587fd31ff846fe66f78cff611
def g863l8 : Packing := (7,1,3,3,1,8,0,g863d8)
def g863key7 (i : Nat) : Nat := 0x58000
def g863d7 (i : Nat) : Nat := 0x14102c6200016c6f1e50a05fe774c6febaa637f5c931bfae098ede668cf7b33423f58ce11
def g863l7 : Packing := (7,2,3,1,1,6,0,g863d7)
def g863d6 (i : Nat) : Nat := 0x9ed829dd31
def g863l6 : Packing := (1,3,3,1,1,0,0,g863d6)
def g863samples : Array (Bits × Bits) := #[(0x129652341296523412965234129652341296523412965234129652341296523412965234129652341296523412965234129652341296523412965234129652341296523412965234129652341296523412965234129652341296523412965234,0x328250143282501432825014328250143282501432825014328250143282501432825014328250143282501432825014328250143282501432825014328250143282501432825014328250143282501432825014328250143282501432825014),(0x852d44ad852d44ad852d44ad852d44ad852d44ad852d44ad852d44ad852d44ad852d44ad852d44ad852d44ad852d44ad852d44ad852d44ad852d44ad852d44ad852d44ad852d44ad852d44ad852d44ad852d44ad852d44ad852d44ad852d44ad,0x8d0584298d0584298d0584298d0584298d0584298d0584298d0584298d0584298d0584298d0584298d0584298d0584298d0584298d0584298d0584298d0584298d0584298d0584298d0584298d0584298d0584298d0584298d0584298d058429),(0x61082dc061082dc061082dc061082dc061082dc061082dc061082dc061082dc061082dc061082dc061082dc061082dc061082dc061082dc061082dc061082dc061082dc061082dc061082dc061082dc061082dc061082dc061082dc061082dc0,0x401829804018298040182980401829804018298040182980401829804018298040182980401829804018298040182980401829804018298040182980401829804018298040182980401829804018298040182980401829804018298040182980),(0xf827815bf827815bf827815bf827815bf827815bf827815bf827815bf827815bf827815bf827815bf827815bf827815bf827815bf827815bf827815bf827815bf827815bf827815bf827815bf827815bf827815bf827815bf827815bf827815b,0xa867405aa867405aa867405aa867405aa867405aa867405aa867405aa867405aa867405aa867405aa867405aa867405aa867405aa867405aa867405aa867405aa867405aa867405aa867405aa867405aa867405aa867405aa867405aa867405a),(0x219bf900219bf900219bf900219bf900219bf900219bf900219bf900219bf900219bf900219bf900219bf900219bf900219bf900219bf900219bf900219bf900219bf900219bf900219bf900219bf900219bf900219bf900219bf900219bf90,0x18af800018af800018af800018af800018af800018af800018af800018af800018af800018af800018af800018af800018af800018af800018af800018af800018af800018af800018af800018af800018af800018af800018af800018af80),(0x0,0x0),(0x4e02bda04e02bda04e02bda04e02bda04e02bda04e02bda04e02bda04e02bda04e02bda04e02bda04e02bda04e02bda04e02bda04e02bda04e02bda04e02bda04e02bda04e02bda04e02bda04e02bda04e02bda04e02bda04e02bda04e02bda,0x6023d2006023d2006023d2006023d2006023d2006023d2006023d2006023d2006023d2006023d2006023d2006023d2006023d2006023d2006023d2006023d2006023d2006023d2006023d2006023d2006023d2006023d2006023d2006023d2),(0x0,0x0),(0x98c23c2798c23c2798c23c2798c23c2798c23c2798c23c2798c23c2798c23c2798c23c2798c23c2798c23c2798c23c2798c23c2798c23c2798c23c2798c23c2798c23c2798c23c2798c23c2798c23c2798c23c2798c23c2798c23c2798c23c27,0x50889c2550889c2550889c2550889c2550889c2550889c2550889c2550889c2550889c2550889c2550889c2550889c2550889c2550889c2550889c2550889c2550889c2550889c2550889c2550889c2550889c2550889c2550889c2550889c25)]
def g863columns : IndexTree ColumnInfo := (.fork 4 (.fork 2 (.leaf [(320,0,543,512,6),(8,256,535,576,5)]) (.leaf [(64,0,799,512,8),(17,0,334,0,7)])) (.fork 2 (.leaf [(0,16,326,521,6),(8,0,855,512,7)]) (.leaf [(4,0,347,0,8),(2,0,861,512,6)])))
def g863autos : Array (List Nat) := #[[]]
def g863levels : Nat → Packing
  | 6 => g863l6
  | 7 => g863l7
  | 8 => g863l8
  | 9 => g863l9
  | _ => emptyPacking
def g863index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 1 4 1 6 1 1 (g863key7)
  | 8 => lookupWord 4 16 2 8 3 1 (g863key8)
  | 9 => lookupWord 4 15 1 8 3 1 (g863key9)
  | _ => fun _ => none
def g863 : Forest := ⟨863,9,fun j => g863samples[j]?.getD (0,0),g863columns,g863autos,g863levels,g863index⟩
set_option maxHeartbeats 0 in
theorem geom863 : graphValid g863 (boundsBefore known861) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=2) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s863_9_0 : block g863 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl863_9 : block g863 9 0 1 = true := s863_9_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s863_8_0 : block g863 8 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s863_8_3 : block g863 8 3 4=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl863_8 : block g863 8 0 7 = true := (@block_merge g863 8 0 3 4 s863_8_0 s863_8_3)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s863_7_0 : block g863 7 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s863_7_3 : block g863 7 3 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl863_7 : block g863 7 0 7 = true := (@block_merge g863 7 0 3 4 s863_7_0 s863_7_3)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s863_6_0 : block g863 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl863_6 : block g863 6 0 1 = true := s863_6_0
theorem tables863 : checkedTables g863 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g863 0 0 0 = true)
  · exact (rfl : block g863 1 0 0 = true)
  · exact (rfl : block g863 2 0 0 = true)
  · exact (rfl : block g863 3 0 0 = true)
  · exact (rfl : block g863 4 0 0 = true)
  · exact (rfl : block g863 5 0 0 = true)
  · exact bl863_6
  · exact bl863_7
  · exact bl863_8
  · exact bl863_9
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low863 : Lower (vars 863) (graphGoal 863) 10 :=
  lower_forest (g:=g863) (i:=0) (hints:=12901687553) (before_sound known861 valid861) geom863 tables863 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps863 : List (Nat × List Nat) := [(863,[]),(999,[32,83,116])]
def known863 := extendKnown known861 10 maps863
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid863 : Known known863 := extendKnown_ok valid861 low863 (by decide +kernel)
def g1007key12 (i : Nat) : Nat := 0x3b42c000003b8420014f82f4f08b0630c0000000000004836909a85800002ad8d915acb040021f098000000000000a88000000064d3b4a9862a71cc3b918830000200b003000500
def g1007d12 (i : Nat) : Nat := 0x1cbc3c4ff
def g1007l12 : Packing := (1,0,5,5,1,0,0,g1007d12)
def g1007key11 (i : Nat) : Nat := (if i<1 then 0xe600000002d723416ab2309eaed8fa4642870eba195125258aea57a8b8442800009100006e060616a3a21c00018b0c9080012435b8b0d62133c05d398000000043bd25e0003a0600000000000001681000000020ad83a7877aa580000001b29432cb5a00058bc00012d9473708ea4a5ab90cb80002aa0000ab800000005a5401781ab0610001ae24108429a1d200000014c08000ac7b8f2ce110f1ca70000877a06a04e7b36c706a08c6d0000000592e00073aa0004b62000532c2af88d0888c38f2400000670800180ef25d6be8000000328a6b0b065aea0186af780018ce8001cb2b974000000000011ea00040286f03a4d49b23d00de335561ba8d600059c800059a58df4ad00000000000000143103660004089c5ff931e207ac5471c37100481e7a6ee08dab8eb3000000000002350af5ea8200068a3a55800000000010e0d0580678000000000000000000000000000000000000000007047eb5e966c08000027e92c98088001c9a8001cc52275c1c8000000714600042588b9f8f40000000000700c000603200008c06c8d85cab7e3beaaf209c66699ac4576269e4f114200048cf08580010f130272eefb4c0c48bb4ee590fc6d0a23d88b804be01214c6dbd9e3221f8ed0bf995485cd8b3ef51ab2a3480008c60001c1fa153e80a06987b41f0c8da1b127ff24a00031138c2cb600000000000387d2580001e9f406200028084b3b9204a483cb2907b76000183781261a82ce51a0000739a0000000000000000041b2c4d000168a8000000000042e8000000000104432566117a100000000000000080680000004316000000000028c383e0000000309363880000003aefce1eaddc0700000000001858c3c20000000aa30001cab912c2008001a56d8f780c00000002273c45dbcc0deb2fc2e78098000327800049360000001cb489dd271094e00000012500000ca68000000000080900014a011022c712332c9084c4cf927041029f5ec30b3d85b3105e4ff9fd8295af74b1b852000117645f601e4a18196402dbb84738adb89e8000000000068b21b786f2b34e69e8b660b4082066000066bc8dc0006ba62320001adc8a84221121f075ab912ecd00e2268000000621200049886768000000000083980004d18b9cc1e00000007000000398c0007a0c00078fe00069278adea3a0005b6c624000000013e42864978000000009db843448844000080108e00980008400520012002100000104401006100001214c000081100200080008000000020000000420301e0000e00004011800000000000200080400020044118023080210100028002004200180200c84120a1000e00000708c6310005001110200202001081200806000c0030004100000000001f25094600040120000180260000008cd700061082807840001500010401880078040 else 0x12793b27446ba9f67b800000060e40007bc8e27eb4e00011b80000001abc000000000006a202f3452800000000000004a0e0007229add731a63780000007b3200032a600059cbc138001e7c800000013b709223ce000497000030b5cbb00006ec000000000000005806000000044aa0cc0000001c6500000000000cca819c01d782e00000000002a6742800006a55b10464ca7eadae3d8491d1448765018a0d296e00000004e30001a4700000000000000000145650d400062b14f1800000000000000000a0fd261cd580004f4cab400068c600019696040001aa8a97ae1b4106e1453e3688698e00063658a443a2845000142a8001c8500960005b49896c2d400000dbcf84aea48e0bdacb02b93a6fd305ebe6253c154a270780814000634a4eb8a632aae1a3075088a0938bad00f1aa52d10000abd385b8600001862a9f9047f23fa8d293a000507b8c00001880316a2384b0e8da0000000000042a00016e50000000482a00002e50c833dc00000000000b06c86c1f68250000000716400041e800058578dff1d1e940000000635289923bc04679246e838d8ea8000143aa0bf219800088282300e978380005a6e00000000001983aa62acde438000000735e88923)
def g1007d11 (i : Nat) : Nat := 0x163cd230f8a3ac461f14558ff30f8a34e41468cf4574cafb058d4ac794c22698d59cc0ff883ac79187c9996298713c3e3cd4b8b1b815f1e7f8a3c66ae561f2c79d640adf0f8f35089e68d3f8f1ac695bfc799734ff0afb059046052c44cac1623c51fe61f2c6a1858d19a53987cb1e734ac3e58f31eb08d28ff3058c878561f1574cafb058c879be1f1a6713c3e3ca86f87c7950f3ec162ef81e394720228c3a7fef59d3b7e686c517eace532a0935a4241a7c0e999e30e5609791e1ea348548800ba0e80b800ffcefff5d7feba7fc74ffaa9ff913feb9ffd53ffa87ff5cbfe397fd52ffa85ff10bfe997fe22ffae3ff1c7fea8ffd41ff883ff4c7fe90ffc21ffc237f9dfbf2afbe44fbc67fb88bfb08ff920
def g1007l11 : Packing := (32,1,5,9,1,11,0,g1007d11)
def g1007key10 (i : Nat) : Nat := (if i<4 then (if i<2 then (if i<1 then 0x4375000000000807023321992e4c9a632b33f5c15bc0001448b628100000000100f8f10700000000003fda08bf896c0000e5a8834b616dc00000000606300003c07381d8b3ae91c80000021ac000040fcc0fd48636000000001898e00000000000000001002b000000000000086e8040ab0eea87af26b22134485f90e9b45d800c380000000125c3f1d951c6f8cb6a4f1d299f156b833103e90000000008ca08486c1eb593fc46e884d271df318b8cf420000000000002c7e5a7ffb29c18e4400000000000071f5e8f93c20603ea49aa48921243232116855904ea45fed3cd995748b53a2a60400000001400020000020000000010c00c02000000000001000050800400000000001400450400410001410020840020010000400000c00c00010c21c50020000050850021000c00481400000440c000000018414000008004000008004100800000400000010000004008600010b0060000840000030402030030010020c02800000400020000001021000c00000011010c01011c52800070420001842400000420010910400000801400010090000c00000010000000010000010010420413070420010410860c20001800020000000020400400800001000c23050020032c000108000104004010410300100314000d0880450010011800400830840000410400000000440020540030410c300100004000500e0010001000000000420810800820c0ac02000400011840002000c00000c310000101000800404508404000000c0001013062400010000010800400401010000c00c00000000000800001c10400000460460000000000801850000410852000010820801450020040c018500000004000208400c0000010000011403000810c50010411830030060430400000c004000010008028000208000a0030410000030800001c30060070070800830410000413c40810410410410c10001811040811000002400010800400c30410020030010800810021400400000410c10840c30000c40000130030c00400c200004115824400508008e00200000000004000008c0400840001492c10810400000030000400003050011c20000000810411410001400003060000020000400000000050c00000020c000a0050400400c10000010800810014800001c10001030c72400022000420020050800813490050020000400410920010c00400c70000c04000001400120003460410010010011400000c008300000104000000010608100300004004004600100d0010010410410000c00400000000500080470800001c00000020000400440411820824800c00820000010800001020080410000401000400020800000412020c00c004000008000400d0000821400007c5001383080042004003001002001000080001000040080100000046040241 else 0x305880266a10f6184c00000000e11cc1468c3db025331227086241e666f2a25e6880ccdfae5c641f069194036c00003272e98e40001a586c21c000038bf0477cd21471f8dc47902c34419a16f4c93c84e2116809be8027c0000000039b4c000180a8a03280003873ba7e7539fb08aa0feda5da000001cc40bad4525000008a038f940000b265300ec0000a793e35e898fc000141b40000480f80000000050d080000000000004356b106308b6000011a72942000000000a2a9e80108f56000000000000000000000f14ef023c0000a3490000320900000000040d0499254acfe4b1e0f9a83214c100000000049d0a8706a80a022be9a9400000000403cd884c00000000c13029fba434b64d6506b300a38a6ee1c3000000000000000000000119684708000000003844a8ad5442551ede1fcfc0e6e1faf30c58445872b43a700000000000000000c29ad1b7ac59c0000a08380002d068e05d728cc8028c54bc163000000000000047b9d03ee9560000105f4938ec8a3b8c5b243dd3b4307ef06c4000000000000246080000000041eb889fb665ea1f690d0e04ed668fe11f39bfc8d7fe1420000000038b0e00000000000000001a7cf5026d1c1d04000000c138114e400000000638a91acd90600000b02f80000000141134216095df0e244688203480002c714c61223ab80000829a00000000000008d9507a820690000309ba641ee0b480000000180fa70519007c000000000000790bbc7e8000062808000000000000000000002cafc2015000000000000000000000684754a0f42afa1ccb9f740000a1090000396980000a0c00239c02604caae137815e00000472ca3e46122c8fabcf284541a3db4081d8d040000000030b8c0001207a617f80000000161a661435910b0b8326ce0000687d400000000309f901208168678643c5000000001e1bb00000000000000000e37b205a2c792841231fcc1c100717c7be93d620e958ab20000000000000000000000000000000001433b00000000000000000000000000cc382529907b9130fc03b21aa61bd01fb44bb7a2df714559d4b835c406700000000006d523750000000000001639c000008dcbc806027e108e000020b04c5b983402210503476554936689906099da49a41ec00140c080c3f8d08d3065dcdf0425e036f89802c333670d000018d2d440a00000000000000001c64f000000000000107cbe23e9923400000000000049346c71ac80b72cfd1f1c0000000000001178c0000a77000000000000018315306d61d568b4aa5a0e40d800024d082662b312c982d802800b011c601e4ac7f8036521be780330121e094724cf1610c5c840f51128f8420c6b0c2ef83118000288b00000c0ff800000c1a0000b03031cd6c2f063ade2dc30d4e09d0863ac0b700000000140c7000000000000000) else (if i<3 then 0xc000000000c1b763c500000000180d0000000000000000000000b20661cf3832ae43e21d330bf7425a06edb387994a1c1df0658000071ca5903e00000000000008318631e818e28007ccca0180d0f3d0ec00001a58500006901c000000000000000024db044f80000000028d744481b1f3e949800000000536d0000000000000a37a800014c8000000000702540000000080c6907ac8e2d02e09187d089000000000305c70452493000000000000008e1127c0000070a8c00000345036200000c01aa227f01891bf80001e1d6a37711462c1d9c34a41d200705cadc02010000308584b942341000000002068000007162e1e900000854e8323000028cbbc0c9000050740000000000000000000001425ab0a50145600c7e2bde06b800000000e32d0000616ec0000a2c8c23708a9e490a00000000402ac0000e40523d5518f80001206c40ae90ac907a400000000791f1421ec776024e9941a0c876406a04fa8bc1415c61db616dd96300000000062fbe1d6c048c00006287800024c516698a41cb0cd10f4a0000000000000453c812a1093800000000851bd1a3d11980000227322ae79e20001600001364093ec000046d9000078fe88b12608253f789fdd8b8f652a61ece87fbca7fe7bd541f311a0c1dc218853e309eb742bf037de12ab04e78b462158b062f124e0f6e039e0000000038aec0000000071a490956000092f6a9d9d8c3a8329000049fe40000474832b2f105782dac052402e30ae1479d2645000000000103ce77ed33af99cb016f636b701a184940000000090b90000000000000f0a8906f1489d83b640c4d8b3dc8bda2def345c80880001c6d1700150723c09e03d4c013000000000000000005158000000000d11a70f7e4ea6227fd3ac19d3c0001e5570000499d08c6ae4e7d3b5606e80bcba5430000000008bf400002365a1a314b75827de3dd0000000000000315080000000140be62ec8000000000000a04340bd2cb43e3fbf03370553c1c8038f93a8e9bdec4960000218cc1a5e82500000000000002471c0000d20d5826e02a00000b0b5d904fcb8485c4102d00002828a0000a2dac099000000000f3a2283c1ca920000a2227890606b640ce34213093d8b280000000000000ce6c0000b12b3139285b9a32000007987e8cf2c43c0000000020419625f82f650a668566609c92310000000016312d27091e580000659a10c7000000000c513802cf829c000088220000088704925c3a02135a9e640b4ea5ad000000000434f03920000120b4cf820093000021470000186e2e31828cbc000000c18409800008ba6a124524440153cf3e0000d41a80000000000000000000038384000000000816046208417f36e80000000000000000616bb8537c470c191096c8000000000000400da8ee664316112b9a91c6c0000082bc000 else 0x40001617f0000000038bd6000000006840b8f9a464cb2a2506af0af705d7730d89ed00001280d208c80000cc444479607a79af10de061f8d072c148c0000c7ce8099507680000000000000000000000000c2f700000899a60d3723580003029d6033211400003c7ba000000000000347a3e2cc00002864000000000d408c1c8a03afc43f00005a0ec000000000000000010f0fa7d500e2800008cfba8360000118cac96c43fe026671cd00f1e045c301eb0db60f04000092c88072e491866f31395b89a54628000053b90000000000000000009483ceb40000d3faa20380001a3bd000059f4c02180000a2e8f08e8000046e7000001948017a45f600000000000000000000021b80058c05beb2db794424bfb000752f100b240001a4aac0a000000065c4085d00900000000181e492f500003c66a63260000099200000476f039400fd800000000d10dd85dd896ec703304f3981a852ba66ba042105edc8b2000081b9800000a6da80fb070f9f12cd998258310100001002f82ca00005092800000000000041dfc000000000000286c5035200000000288d6c75c272d90d870a130cc720bc104b50c63c8be0000d10880003c8ec48020000586cc00000000340b7925c400b8593016b496ad48c1e4b951df8926cca9864b381f861c32099600000000791dc48a664d48214c95a74584e1e1c1cfe914a8188e4c4b1c0392450698a7598415ea0bc000000000000315f18ba400004119f20220e9281de0099f18bd86cfa626e3ec80002007ea5b042e800000000061ef00003022dd07f4807f343b1972c984c5ce23076958546aac30cc2439159189abe54641a11823941f383c1b02f284db8c04c68ae030c80be4ae74261d0b37085ecb2fa75650f2e9a6589fd62c0012e500678a8ec176832b9094a0f2e401bd035316cd0801672c13f818498481d215792827000c8480038130a1b16a88e4d63640000509ea8d4ea3e6a1558000000000000540d0000088480000641000000095f855082e7d82e800000000a2cc00001055d218652c1e833d89d60000c0cff9fc98eeb070ad0e48000000000000000000000000000000000613e40000000011e38000000000000a13bd0347867be7b2530ca0c5a8ca80000c2c6800014e2200000000617a3c2ea62f30000481ac000000000000000018f66000090fb000000001a3dec3b278ae80000000063418912c0da000000000000004868000000000000000000000326c80002045b42d8d1a7c15580282c437633670fd74877e230b2e6a0e40c7684795713ca1a27ce00000001ffb8a4d4e8641c661bb49e3289d20000b18180000000000000000000000000000060800000000000000c1d9800038e7701ec00000000000000000000051dec100301f9e2fca94898a6402ee52978000245e4059e3247d96580000275)) else (if i<6 then (if i<5 then 0x3192084c340c4807100000937acfc80000000000003c85b057da3b3718900000276b203a889b0000000000000000000001a29100003913e500c0000828280001c2c025b4127578f080001a13b00000000289de00004251c0880000127e2315df059546556595000049f0c4e9400000000000000001476e00003936c00000000300d000000001404b716b9149d80ee2081213a60411c1b1e3a3b37cb1d800000000010fe80000cfbe6173f01539ff54cff880361cd000000000e61e000008ce186e0000041d500002812427b5c348920940000000073a01029206b80000000020a2e837a0000a226b9dd0c334e214f2251115a8887829852f3d164a494247bfa2088000000000000441331e8384d5e35003e100002023c00000000000000000000070392934e49e80000033450c1c00002832000000000000000000000000000001665f2138a8874057200000000000000001a7275041e931443d4a250000000000000007d84264518c645efe1ca00002131800000000000040a480001639b0000308668dae467ce0c180003c75000004010703f38ec2022ed0fa51ef0000185d5000061fa3844d235fc33d303af868861c703fdf0da0000000000000000034c140000a21b000000000000003b6180c98dc80000306600000000000000000080b400002118000060d34000000005315800034890c653d1500000381340000f40218a360aa3046d03238000383a2e2e5f3f4d9ddc4e280000428b814fb83e0230e728f113c0c705e311140038f68000086140000285a94b0101be117c0000383c6000000000000000000000000000000000047b00000000000000e4143399c8f1a8a1be38692c55118dc2e2e1dd727989b1683e2c025436ae0e5fc97cc06f23a2a94eb4e5c0000f34df1adc00000000a0855888c0000000000000000245b2a47fd17b11f6d80f0e099438989810cbc20030b259293f34f4ee3eb338d08628000000004235000000000a599000000000cf1ca33c00000000000000000000012060457da2fee383089f14a9761cf000000003c262c42af193800034e7045818045010cc000000000000000000000000041410000002b924270000098300001474cd34d194ac4b382724a0f4b11d400000000000000003c4340000000078dfc000000000000000000000000000000000000000000000000000861a055b000028c7c000001b700006150a03020000000011deb82400000e28580003cc2a0000000079d7c87c5e48e00000000000000000000008a240001a3520000114844fc244fa619fa100400000000c10409a8c000046b9a1e229d1800000000418000002c46ca40bb1bde02cc0c9400000000617904f53042bd23a18f3000000000000028df90f16e0f221eac838947580673000009e628058660100005168800016027000010e8 else 0x43bb231e000008912000000005825dcc0a00003276f098e4ac5073d835f00000025e0000741b800004cf600000000697ec00000000c0530000000000000b25300001401da548018be8ce501f6a31df27a8a0640001a72502cee0523c299813a637a0000106b40000025ee8486001385df000078ad4000041237228800000000000012e28032c00000000e230f9ac08c7662f5e2015a08400000000000000003885e00003141800004cac000000000000000000000a2fe000034bd2000000000000000000000e173191b3c1d064e3c2e060710000000002074f0693c6e324234136800024d82a3a26224c8ec40d6800000000000024d27c02e0000000000000000043a871f7b8ce2000040fbe1291c7b8624d000040d4488df4138000019a86414a00000000000000000a20f0000000000000000000000000000000000b0550913000000000814e00000000000000000000000000000060b870887cf91e11f9174a8144c2b56666336a10c280811683c0000000014f1240ace009b8bebc4ae00000000607640001c651629820ab009a06781000010bb5c33d40e6f376005bc000000000000000014293254d0000000000000c29681de50ddc000120ff037dc86bc0000c42133272a05c0000000061cc28b058753828c131980002c04607d0d029800000000849c4088000000000000000000000000002231e0f300003870e262000000000000000000e2b58000000000000234f000034a1540de00000000000012705b0b0c91a40fd80791d06c8000206dc651200000000205d4c78d319bb9300000163cd335c61b6ccba9a04e00000000343c00000412750de400000000b0dad82bec185670b50ee009ec000121d50000493040000258f302a800038efa00000000599d94d416087000000002441400000000487bb08a9e41cc08349e8dc6ac27d1000000002c59602a80000000000000e0c33281a866d0ef1457f102199bbe82ab00ad921ab8b4e4a760000000000000000087650000208f442160000000062053cf5e000063728000000000000c24500001ccdf82970000000028bea24eed05ce9ada839dc7d231697137202bda6cf338b8a0770634050ee310a06c8896ae2430199a04d546a80000000061aae809226290000281f24f06604193ee51ab84ae2000070ef80ac18c1fa77933f0000028510000012b1c85650b78c28fd2e4000000000013d107e8000000010472725280002899fa55252020859d82566590134e00354895a00000000000024c060000000000001803906e372b4000000000000000003127e46bc00000000000028d02a7d60000290800001647e42b9319de8e9cc1a843c21138247d1c2bf941180001c4c42074c036c8aa80000420b00000000000000000825048f000001c771000048d7401d40000e2a2800000001867e) else (if i<7 then 0x6e48b884d840000000000001881a0000000000000000003460000000000000000070870000089010024000000001850f2357208a8000306c2c52c50a30052d83a40000e13780003408a0000501e582a4000000006348310580000c0b20000003538950062a0000000000000419411fb800000001428500001a0b00000c24200000000201000566c3f88000000000000000000000000007b132af394d182f803e36192b9c08c2f526aa926c718580001847bd3ce40b47c7560000000061e00ce9665f20000000000000e0a20000000018a800000a39cc15b08268058e417d88ee50fb400000000597700abfe15b63fe69c7800000000000028b9c430ac21f0000203b5d02400000000000000000c609a353710e8452906ebb1370985f422d84ec11f701099c6d94044603b1945987a00000b0dc895d40000000000000000000000000c39500000c00d27b8a07f38f3e4fcd2153615200003403c00004298d8ed648e3c500923389d7ac0ddc147d0bce08ac00000000a08d800030279027800000000000000000000000003cb9200000000000000000000000007819000000000629741106431e0000c1db800000000a6b55333b92a5435a0000b21801a5308154378810809e88c675254a000000000492ae5dd8181106084df9a730d41c000008d3e0000000010f0c41ce46440000188dd8d440000920f8000000000000622d61ab14b37c3ef00007897400000000000000001cb1600000000000014338000000000000000018389914ff186845f8a144b15ba19ab4974236f23fa39b584a3b20570004799864143066d22238000243440000f19869c7000000000e3d300003c491a82a0000000008408a73e00000000345f3c79e000000003ce4200000000002320928000080ea00000ca294309540e409640001e4a2c1ca3065ac55be1294370800000812000000000000000000000000038d6546100000000029abc0000000023885015984e400000000612c20a79c0dd019f008bc0001a6c6000010e4d881e6455620eb0d8d8bcc000000000000000010496c3304053c0562c3f1000001cc80001668692bd61fe800008638f0f40000385c20000d3aa01103ce7544b80000000030cb22162e14099f974b49c23862790000044cae0d0f19949fe1413a00000000000000000000020650000000000000000000000000142e86296800000001a47ab25a61b4a4d8ea66ed3e60000089ee0000000048223006a00000000192ff00fe000021963084800000000a01c0000085d867192391800018909620960f118a8800004763628fd10e643e4000000003153c87caa089216a00000402d06c30000000000000c08d40be99c244e3e612e0000308fc0000000000000000000000000303de06e0000042491182d8000000000001404800000000262c00004989c else 0x1018b805fe84348a23e6c9219b402da4141a642934eaa0b9012363669190a0c184ed364ae90b64a09fc0b743d393c800f290c6e0000000000000000004a7b01b80000000005e0e27b30da400000000000000000000000000000000000000000000000000205ba0000401080001c62720bbb26d011920eda02479380800000ae800000000717fdc9cc46b10000000014b5fc00fe2df80000000000000000000038bde000000000911400000000009600002c3a663b8000069557100ac38500000000000010840000000000000120cdf11600000000182b60000000024dcc2831e2f8000004202000003a080002c9ae0000e1e400000000100df618dc91e0000000000000000004d1c0000f28480002432762670000000000001c1fc9175da0a01052253d0000000000001a5de000000000000000005342800000001045dc081d98f58c6800000000488a60052a67820dfe20f4000000000000000000000822200000000208a0450c0000597ce488c4331826f8000000004105000000000000000000000109505020c30b739780003c08e0000120cf8bc4000122da00000000000000388316691b70000000000000000028e30000040210000000000000520df15b6895820f60000288ca0b5820e3d070682c4016be122c35da1eec0001a611c180b0f2c00000000c1d78000000000192000000000000005f1325de90400000000003cec8ca1c907e1740000000000000a2b4e387000000000000041638000000000000b106c88568f8a80f15334e9d8b05216610a34691b01009885b1b241701f8855361ccd008a88ec0001e29ab00c09bc40001057921a4000000000c04a000000000000103e17303a9e164d2a86e913a3d20eb008c000060c2699c05018c73790ce91620c020e1cd02e62949000000000b16ae172d47d8c4c980e0080e9c6460000f12621e68000000000000415c282c80000000061ff8c2a400000000000034d50e191e)))
def g1007d10 (i : Nat) : Nat := (if i<3 then (if i<1 then 0x3ef9de44fbd75913ef20a44fbc81912ffa2173dfe775ceff61973f7e555cfef91173bfd805ceff61d53dfe7754eff61953f7d7554fef91153fdd7354eff60153bfe8850eff61d43dfe7750eff61943bfd8550fdf95543fbd7450fef91143fdd7350eff60143fde778cff75d633fdd748cff71d233fdd548cff791233bfe885cb7f9dd72bfd865cbdf95572fbe445cbf720d72dfd735cbf78cd72bfd805caff61072fbe441caff60472bfd801caffa2152bfd8754b7f9dd52bfd8654bdf55152fbe4454bdf54d52fde3354bfb5c952bfd8054affa2142bfd8750b7f9dd42bfd8650aff61542f7e5550bef1d142fbd5450bef91142fbd4350bf78cd42fed7250aff60142bfd8710b7f9dc42bfd8510bdf95442bfd8110aff61d32dfe774caff61532f7e554caff61132fbe444cbfb5c932bfd804cb7f9de22f7e5588bef91222fed7288bfb54a22fed4288bfb21e22fee7788bfb5d622fec8488bfb5d222fec7488bfb55222fee4488bfb5ce22fed5388bfb50e22fec8188affa2171dfe775c6ff61971f7c855c77f5d571f7e555c7ef91171fde335c77f5c971fee225c6ff60171bfd861c6ff61071fbe441c6ff60c71fde331c6ff60871fee221c6ff61d51dfe77546ff61951fbe44547f78cd51f7d52547fb88951ff571546ffa2141bfd875077f9dd41bfd86506ff61541f7e55507ef55141fbe44507f78cd41fbd42507fb88941ff571506ff60141bfd871077f9dc41bfd83107f78cc41bfd82107fb88841bfe884c6ff61d31dfe774c6ff61931bfd854c7df95531bfd844c7ef91131fdd534c7f750d31fdd324c7fb88931ff5714c6ff60131bfe88486ff61d21dfe77486ff61921bfd85487df95521bfd84487ef91121bfd83487f78cd21fed52487fb88921ff531486ff60121bfd870877f9dc21bfd84087ef91021dfe77847ef91211fde33847fb88a11ff571847fd50611ff531847fd48611ff487847fd9de11ff575847fd21211ff574847fd1d211ff554847fd91211ff573847fd54e11ff543847fd20a11ff572847fd1ca11ff552847fd50a11ff442847fd4ca11ff622847fea2120ff987483fe21d20ffa77483fe61520ff975483fe61120ff884483fe5d120ff874483fe55120ffa44483fe60d20ff973483fe54d20ff943483fe5c920ff952483fe50920ff981483fe20520ff971483fe1c520ff951483fe50520ff841483fe4c520ff921483fe84520d7e77956bf61874b7d851d2f760c74bed821d2fd60474bf9801d36f9de44f3e55913779de33f5e558cfe791233bf9801cadf61442bf98010b7b9de22f6e5588beb91222fce3388abf61871bdd831067f61c21afd86086df61421bbd84086f760c21bf9800877d9de11f7655847ed91211fd633847f988a11bfa884837e9dd20f7a55483ee91120fda33483fa88920fe921483fc84520 else (if i<2 then 0xa1b0435686920cf519b632946458c78188430846000bd817442e205a90b3f16042b685590a7514a828cc50209d5134c26304ab0920120c235c462088e10e820f840787ee0f9a1ee83cc87710e921ca037906d10d2819cc32c86230c1217a02e0058a0ac41520297051409f41380263049008a610901fa83bf074a0e2c1b8834206180b5815e029b050209b812d8248046a088810781d9037006080a9812401ea0350056008400e201240108000ffe885d3ff61574ffd835d3ff60974ffc825d3ff60574ffc815d3ff61d54ffd74553ff60d54ffd82553ff60554ffe77913ff5d644ffd845cfff5d173ffd545cfff91173ffd825cfff60573ffd7454fff91153ffd8750fff9dd43ffd8550fff5d543ffd7450fff55143ffd8250fff60543ffe885cbff61572ffd845cbff21172ffd745cbff55172ffe445cbff60d72ffd735cbff54d72ffd435cbff60572ffc815cbff91072ffe8854bff61d52ffd8454bff21152ffd7454bff91152ffd8354bff5cd52ffd4354bff5c952ffd8154bffa2142ffd8750bff21d42ffe7750bff61542ffd7550bff5d142ffd5450bff60d42ffd7350bff54d42ffd4350bff5c942ffd5250bff60542ffc8150bff9dc42ffd7510bff9dd32ffd754cbff5d132ffc744cbff55132ffe444cbff9de22ffd7588bff5d222ffc7488bff55222ffe4488bffa2171ffd855c7ff61171ffc845c7ff5d171ffd545c7ff91171ffd835c7ff5cd71ffd535c7ff50d71ffd825c7ff20971ffd725c7ff54971ffd425c7ff10971ffd325c7ff88971ffe441c7ff50c71ffd421c7ff10871ffd321c7ff88871ffd74547ff91151ffd73547ff50d51ffd72547ff50951ffc42547ff4c951ffe22547ffa2141ffd87507ff21d41ffe77507ff61541ffd75507ff5d141ffd54507ff60d41ffd73507ff54d41ffd43507ff60941ffc82507ff5c941ffc72507ff54941ffd42507ff4c941ffe22507ff5c541ffe77107ff5cc41ffd72107ff1c841ffd32107ff88841ffe884c7ff61d31ffc874c7ff9dd31ffd854c7ff5d531ffd844c7ff21131ffd744c7ff1d131ffd544c7ff91131ffd824c7ff5c931ffd524c7ff50931ffd714c7ff50531ffe88487ff61d21ffc87487ff9dd21ffd85487ff5d521ffd84487ff21121ffd74487ff1d121ffd54487ff91121ffd83487ff5cd21ffd53487ff50d21ffd72487ff54921ffd42487ff5c521ffd41487ff4c521ffe77087ff5d021ffc74087ff91021ffe77847ff5d211ffc74847ff91211ffd73847ff50e11ffd72847ff1ca11ffd42847ff10a11ffd32847ff88a11dfc849df7f20a77dfc819deff61975bfd805d6ffa2174dfe775d2ff61974f7e555d2ff60174bfd831d2ff60874bfd811d2ffa2154bfd875537f9dd54bfd86553df5d554fbd74552ff60154dfe77913df95644fbd74913ef55244fbc8791 else 0xd3161aa8790e8d2c3c8cc788e96543c83411d2c3ca586aa6e3ca58eaa1e4bc5b80f3a3551cf702c74875b96e13c6aa1e8e0095162709e58674b4f1bc150f38c1a586746aa1e41c34eaa1e53a386aae03cb1eb08e1f851440a1a3102868c40a1a3102868c40a1a3102868c68af9c3f2a9a714dd9f055f9b4d40fb9c27fe1066c2384ffc4cc3ee70a7fa7ad38b143c64478d1911a3c63c57055fa798537e0abf369e71e37877fd3d69d9fe1e314201962182c3463cb08b0f10f2c21e5845878879613014abe7ee158ecd5702c46037e70fd5969c7bce1fab2f3301fc3f565e6bc7bbf03b3cc3f82a9e46e5b82a9e51fdf80d9e5663c57869dee3ca7af0f2dc0a3f8169e4a8154fc29eb53a7a71b4d5e9a25323a6134b8695cd291a4c548b2905d1eaa393464e8b9514aa24543b2865d0a3a105418682050269ffd3f767dacf8d9ecb3cf6783ceca9d2939ce725ce2a9c13376a6d94d919ae1353e6974cff996931de62ecc35980d2f7a5e24b9c96e92d3258b4ae79539299a51f4a1d93a526564ba493091d922f644ac87490a720763fe47bf8f3d1d6a39246d98d39196231145d78b2715ca2a545298a03132e258c47b88a710ae20543c6873d0df61a04326859b0a96130c22b841507c20e441a7830d057a08d40dd818701fe01a3fe97f90fe65fb53f427e26fbadf5e3e9b7cbcf8a1f03bddf7b28f55de9b3d0e79ccf26de39bc44782aef61dd13b6c7696eca9d813ae17564ea0dd313a337424e771ce1399a72f2e50dc78b8d07118e13dc1ab80d6fd8debdbb9373c6e36db95b65b6806cccd8a5af9b5d96b46d57da9134ec69a4d255a2fb42267cacf119c3b3516636cc05969328e64dac8dd8f9b1b6631cc529886b0c260eec13d7feafdc5f4cbda57ab2f3c5e44bc597852eb85d12b9f572aae495c5eb8016ec2d945aa0b4a168e2ced597cb2c9641ac5b5874b09d60a2bde576cae8d5c82b535672acb5589aadd55a2aa895442a7c548ca8794f429dc5330a55148f29125180a22942328334fde9f8d3da279a4ec89d2938a26ec4d34999132c26294bd896f52ce257b4ade950128c24e949ac92112202411480a8f211c5a35c465a8bf917922a044c6887d109a1cf4316857108c20e941748265031a057405e8038ff69fcc3f487db8fa69f103dec7b00f4f9e7e3ce4790cf0a1de53b7a761ceaf9d453a107380e669c9738ec7100e089bf037ac6ed4dd11b5736506c70d731abe352c6964d0e19df33446658cc1994d324a63f4c7198ad310a613cc1a982930105fb8be317a52efa5c90b7716b12d4a59bcb2716262c0a5720ac215472a225414a6e94bc293651e8a2c943827cc4e889b2935926384bb494d9265246c47c88e511a922e6459c88e10df21524274833904620123f4c7ce8f7c1e9a3c9477e8ef11da03abc7470e6d1c7c383c6f00da)) else (if i<4 then 0x68f11f82004be0b61fc16fe106e1f840db0fb9c1688fc71e2168db0f11c16fe2676c3c4185a52c367ca0c3c570fc0822eb70b83e6fe1476012c4f84dfc28d72b0d15c27cafc8302017e083cc0bf041e49b5bf0f23e0960203f0a1e61a0ff4a9e52837f0a123cc35f08b0d293c78afd5f8090cb2c3478615fb809089ac2384dfc28cc025850fe047f4f128ad3e50ae037f574160c4ff091e6ad34413fc3cc1bf701424219f04b0fef378081b3ff0c00b545a78fe1f8004456a13c6aa9a23f704b00966e206f0fd3c480496a13d5379a23f7048c0c0012a1a654d8791e1fa7b7009ad3d50f9434c61506fc00798456fc3c8a868afdc00043be096021078d28d073e69048d1e448288cf9a41c20a0f1a52c34108fc1079c783fd3c85898d0e23f091e827fa78d6832c1bf001e71e37f4f202fc10791f047cd555bf4f3169a21bfe9e6ac3d6cafd3ccb41fe6c3cad96aa11f9b8f3aa1bf9b0f2fe1ea86da78f07c3f2d548e03c47e5451eb44d85701ea96fe3831ea969150a6dc3f0f6e76d3c78d54b4cb7f361e4fc3d98d57e6c3c83db08683ac3e516fdc0a045702d3ff4d1466012228414e010b1c514e010b1784d153cb16bd6e02a7ca1bf91589f01ef2688fc8acbcb0ffdc0a04457adc050f9537f21f046b010f03c05080058fc06839558a178022c20bc04561880dc068a0458fc07839558a345141fc02163f015586c03c068aac4e04eb0ca7012bcb1780f1558828a700858bf0c961f5844d1bc3f1400c003cb7ee05021ef569e3784d11f90c020ca701ecc016388e13cb10a33e000b14b4f943486eb0f1bc2688fc8ad28b0fe1f9794009bd586f01f2a6fe40d15c0a7e0010ef823c0842c34a341d69a40c34b1820f315a69040e1a5883c6d69a4ac3419629c07dcfc3832c78a11706fee05022784f1eaae4d11f90c024c78d240f8062c8e13c4139a58d707ade02278dfc503005f09e3e50dfd70e48793e018b187aaac58c70fcb432477e0c507966cafc3c83c45cfdc0a043be08d075a7961fc3f141ca9ea8693fdc0a044569e3f84d11f8ec0254c03e0267963f09a20b11688e037f4f28011587f09f286fe38e1a2037e283cf3447e1e42a3ca09e058c5a6cafc3ca3837e283caf823420f2c41e2a7d6203003cb1078d9f588c26aae13eb1982d95c27d630f10f384dac660bc7cae136b1f82d06bcb1782a1abcb1782f54b443c2c7e0bd50f5a58dc15161d607c17adfca8fc0b2a1965a22c2b82f54b7f1c19654b48ab82f2c4ac357aa5a5e0bc416fcb5e1f8332c31aab82f2df9e1cb2f13c2cb45705eabf20b03fca97957aae0b4b14b301abd52dfdc10586af5a42c3ff2f2561eb557e5e62c3f82a1a74c5b80d3aa879b82a3a33a58682e03d51cb4f1eab80d6e7e01950cb0d3aab80f30d3a23a5a78de0a879c12a1a33a5a7aae03db9ce96183d5 else (if i<5 then 0xf84070c41eb407e0c1074f4035a083107866c1007e260a7a47b608b414f307fd3c78e120462a10095f860910507cd0c8ac38606fc5028f9e9283c4865a4411db8e19f848628447cf5569e3c72d1a1c28c4960624a105090610a14b2d085084568a1210bfa78a5e58684391082464578c2cb46843bc14bc2142fe16084042f01010490c1427c0506fc00225e0a5e50214b2f12509f9e0b065878a088145048eb8f1a5184ae1f8609001184568d0850a4c4949bf83041ebd35c60a080c7943831a14010b000c394241880051c0c30120304683101811e54114b705a240120852b24b2d1820215ac45052b08194e059784004c4d649627c030428b490aaca2c5064a60009701359435795284283c4865f58c3cb2d1158a1bf161a64017f2f085801430d16a8c8028b04bcb080066658a00270100c2000ca8b2278d14bc2160072d3c88027e1af0a002f01018d9929f820200a9a238000c1199640d0c60013f141abc014e965e64a1435e79c0c9409f810052f1620a002f09a00b072865f28b0f1a00c3c01b281bf025e83abc1001a3ca1d78a080c6962871a0c2012089a14210c099a3421418e0a049584980838d18a8d1e3828c31610683109cf085168630e1e68313f16540d6810c72c4830d5089a58314b145a18860b0c5a1091a3f09e3c0dc29f87040c0165168d0c423c27891c182002c91e38606080169840f34187f8a4d1e18b347940c49438606fc00a0f42d14242031e58a22e160c0078d2872c3c7142169eb55041e50e007151f012b437e080070854a2c54a0ca70100c304545905a7aa003d6943841c5460787e281070038c540ca090c1002d491545380e0800b2062a080070d5a71e38a0d68b1df8414083d05040608cc796398543bf1408007a168b282bf042c3d054b0f28494a8a0dfc00b0f4165a282031e50e5a7aa003c69438f1c5063c6000608498a0c080278f121ab244830c3095a7842c3438c3d62cb40aa06381094f0125278e025ab20b2d1a08496b16183952d1a14ca448808b4a022d590f382d0c24014305ab2b80a1211e145a08b5650302587092b01e34a0e120380c2d59634b0e2849a24b0f0c38d1eb165a2578f283902968bf0a5e3e029b0d805f04b0f9b280881bc3f0008be1586fe9e28cc025b84ffc28af82086881960c2010a1a61e20a0a1a52c2c48fe013f002290a5850fe1f8484009adc27fe14560113c3f041400c2787e0a28019f06b4f1aa844d3169e208cd2b65e0c69069112a1a29a0db705ff951f80d11f95146af10d6c22c3c2701a0bf08470fc206c03c3f081f09e22b7e1b70ef82242709ff841b87e1036011424304e1f841c688e1fa99450909c07fe1077c11e10196e1f8300309b814796e013f060099e37803adfae1d80478a1258303e013f1300b2d3c4709bf899c2841570c70fc180246981180dc0 else 0xd0604010505003781400de365e342003140a046d8a2f1a28200385022140028920a0a006445000824a446805e24a344af2200b346aa06100186890c226aa087fc2028627e101421387e10108d810d10b42843fe1008213f0b0420217808fc1421460910186ad087300028620006602062930800313f080818834c05004261000cc361e1801469800189f87830410bf878a0c10bf9b0f5a10a6052d0410bfae566c3c68439323c0509fc00220c566c3d68d087fc3c10427e1e084042fe1018213f180c109fa78a1ed821bf0f0cd811418d0a0083c4061241e2830924f1eb449088f18b431435629c07fe121400614aac30b00081d69140f0e2462bf0f1018a6007e123c318a7e143c314b15123e03c68c005e0d820f0051a0d50c0056c2418f542001dbf01ad998030c11404fee00030454aac34536083c01c4841a44015b331e009586886c33f0200107a84060027f04663d158798004ac29b0009f86861e96c506aa13f9b961e9e13c78d6c00dc07896c30a34184024113428427e1c3d6830418f)))
def g1007l10 : Packing := (500,2,5,12,1,15,0,g1007d10)
def g1007key9 (i : Nat) : Nat := (if i<1 then 0x143c8cb24904829c853549d0115811126e380b50a40001e1da85880000000000185680000045839a0daa14b31c1081c015000000000003ce3b21a00000001c77717d1353c395c278000c19be867ca64958621a4601044f1f952a2a2ae00ab8b7817c05018c151724331a78505e491183d8451587bc84490b4000000000002385600b81241aa40eac2a203f00002210000000000000000000184671e9000000000b6800000000003c6d302001a8a796860e206921643d105f80bd0000a118000394831aa219802b80000001680c0000000b00c00038b80000000147994cae16e10f1272f0277812000084bc8688127c295a0ba4163142d133a8578c8788b000102e244880008160000400000000000232dc80801db28ea3fbc7de01cd07c000000078ec000000010b980000000000000078a50006000242600000000000040a41fd000023db06000000000828000039490000000000000000000000047ed8d2007380d64630000632764b00006906523a67070bca150c008e25e81491b600002645063800020d885bec2da12ba3b56728000000000000000000315422a60002c9980000000216742c0000733c000000048e11379e60d8388000000000008b4d0fc1103801c00021d9319e06140000000000000000000000c12000000007a01330dc0c1064f16cc2ba0000862612d000000008d35083e3dc0000000186970e0000000079c90000000040f0000508600028ae593e5236e84c8a261e840dd0680065006762b5c14a0af01f773094144000418d000000000000000000166880007936c28200024d8a0210000e362104f05f108a00034ee800073b8245c000089e0000623784b000000000000d0651970000a04c00078e963b600000000000000000000000000000000000000000a3a3e20901929b24388a8080d199ac73d7444dc87e9b9a39ca2da03cb20df33f47c8c9c400f4018e4c1447a8a6b42865800afb1f33184c4dc8acf9dfe268c7db89208a912cba178cbd798a30a6c3e34b1e18140dac56d03d1065a0f9c700825b1ba320f018fcb38000000000000000000000000000000000509a00034ba30282287e75143a02082399e1514fad8b320d563e787f814682d600000000000000027230d2000004110000a0400410000051020060c000c0460400080400000051000050ca0000060030400000401c210500800008200500000014100000000300200018010000204f0030052800c200001104100004810101400204200004204114004008708048004500000004300002b00520200400104300000704074f04201100000000400054000b10000000018b0000440030901800850000422000000830010000c000418000604904510600000e0472c20010011422c10c01000000001c004028000000008b08510000008000e else 0x2019b1a1a33980dd04ae93291de000246bd9fb630f074c00000000000482d09fa9f081a044780ef19adc030000000041523351c2880000000e0c200038eba0eb000100e0000703c000185a901a3994000000000000000539ea2ba0ccc0800001421b83d8000314fa7f343241d60001006acdb887700000000000402d5421a2e546dc931731f04eece1d0ede34a871a0df6935332d0371c5d199b63dec4634bb8000f25c0002485791a00000002c04c8cc743182aa0470000000000034578000a3aa00000000000841c23c40000000d03683748424a12b22c4450835800040bac6efc4c189da1aca127490805cb115a10a418f2003076a3230f6894f2368e7f98b0a925d04a84a40000000f2ae00020866005b25585fe061f1263409e7aa8ec0000835f262d86f80000001e7880000000f2ea669c487000031ea0000000618c00006316c880000000045d984399bf42240000000000003f480340050000c08ee73400000000001837acf3800093fec4a0000784891f5e5f0c8000f000000000ce2820ff361238fce86862d1cf8621cf029562366e14104d000e000165c5808e00b01240000000602302fd04f507209e40000409a07441abe1d4000285900000000685c83e800070ac0000000318900014128c000000008341a1ccec0556146224c04e101050e5825383798f301a6a26c0000000000121cc908f027542da2d40002819000000000000000000000000000000b3c6438889ca07f000000008bd8000f415c40b8158000000042840000000000147d00000000831dc5a000010b400000000000000012aaa05c0000000000000000004085707a0000000399a00000000c040000423e000008280003247a59ace921190000000101d2040e1b20003884d1f8b0c1433bc5dc93c006d627f0b128ac73e2e6f400001920000e6b9881c82f00000001c91791c803f20fd8bc41200000a81400000000000000)
def g1007d9 (i : Nat) : Nat := (if i<10 then (if i<5 then (if i<2 then (if i<1 then 0xd2aa42905fe65121483f748890a41fe97248520ff4a9242907fa50921483fd53290a41fea8848520ff4cba42907fa25d21483fd30e90a41fe88748520ff53ba42907fa65521483fd30a90a41fe97548520ff4ca242907fa25121483fd30890a41fe88448520ff4ba242907fa1d121483fd2a890a41fea4448520ff4c9a42907fa60d21483fd2e690a41fe95348520ff4a1a42907fa5c521483fd28290a41fe93148520dfd444229077e9de11483f748908a41fda3384520ff511422907fc60611483fe2e308a41ff14184520ff898c22907fc48611483fe13108a41ff28884520ff84bc22907fc61e11483fe10f08a41ff27784520ff8c2c22907fc5d611483fe12908a41ff18484520ff842422907fc5d211483fe0e908a41ff15484520ff922422907fc60e11483fe2e708a41ff15384520ff8a1c22907fc5ca11483fe2a508a41ff14284520abeca9053bd6f650829debf320414ef5dd93206779ef4cb063a4fba65821d37d320c10e93f69960474e9f3bcab225ee64082912d7b2c40c89d5e7795633b6ecb0e919dd7654748cef9b243a4677d5911d233becc80e919f679de448cfe3cab224673dd93a21729ee4c466b94fea65801cb77488c00e52fd96a2142b5ecb0e8a15cf6547450af3b263a2857b5911d142bdcc80e8a14dfa658510b2fceec28859fa7760042dbd2ab00215bb6588788badcef2ac457cd9321222b76cb0e9115db6547488af9b263a4457e5911d222bf4c80e91176b9de4488be5cab22445dce778ce22fa72ac67117e39123388a6fb2b442e337c989557197f4cb0c38eaf61a441c75bb0d198e3aed86888719fcc8510a0cf7a65831073bceec1883bcd83888418ff4cb0e10e3f9dd860872fceec28433be9961021cdf3bb0810e6f61e4408757b0d22043b3d8591021cef3bb0610ee7911830873f4eec0043bba4460021bf8c810f08f5d9de55846eeb2a424236f5961d211bbaca8e908df564c74846fcb243a4237f1901d211edb3bc8908fcd95644847bacef19c23f56558ce11fcb2246708dfc64082846fe320394237759510a11bf8c808508f799de22847eccab11423fa64488a11fe319c4508e7ea2277482fe122c2a41b7a8895520ebd3bcaa905de654844827f3303a2416f9961d120bbcca8e8905f664c74482fd3243a2417f1911d120ddd444889076e9de44483e74ab22241bda888cd20eed3bc66907d695633483f348919a41dea7788920fb52ac44907ea91222482bf32e40a416f99620520bbcca902905ee65081482fb32640a416f9961c520bf4c90e2904fe26141482fb32620a417e99210520bf54ca42906faa2121483bd4ee90a41f6a5548520fd522242907f28cd21483fc10290a41fe13148520ff090c22906fca2211483be4ef08a41f725584520fd922422907f48ce11483fc12508a41fe22284520 else 0xb2e8907de95574482ff3303a241bfa881d120bfcc98e8905fe64874482ff3223a2417fa9955120bfccc2a8906fea2154482ff32eaa241dfa7755120bfccb2a8907de61554483ef2eaaa241fb97455120dfd444889077e9de44483ef4ab22241fb98491120fdcba488907ee55244483f713122241fba8891120fdc4bc88907ee61e44483f710f22241fba7791120fdcc2c88907ee5d644483f7123222417fa9960d20dfd44306906fe61d83483bf4eec1a41f7a5560d20fdd22306905fea6573482ff330b9a41bfa885cd20efd3bae6907de95573483f7488b9a417f99854d20dfd442a6905fe65d53483bf4eea9a41f798554d20fbcbaaa6907ee91153483fb2e6a9a417fa9950d20bfccc286906fea2143482ff32ea1a41dfa7750d20bfccaa86907de95543483f72e8a1a41fba4450d20fecb9a86907f6a2233483fb30f19a41fd8878cd20fed3bc66907f661633483fb2eb19a41fd9848cd20fec42466907f65d233483fb0e919a41fd9548cd20fed22466905fea6572482ff330b9241bfa885c920efd3bae4907de95572483f7488b92417fa9954920dfd442a4905fe65d52483bf4eea9241f795454920fdd222a4907fa5c952482ff532a12417f99850920dfd44284905fe65d42483bf4eea12417f99550920fbd2aa84907ee1d142483f72a8a1241fba4450920ff4b9284907fa61e22483fd4ef11241fe98588920ff4bac44907fa61222483fd2e911241fe87488920ff4aa444907fa91222482ff532c0a41bfa8860520efd3bb02905fe659814837f30ac0a41f7a5560520fdd22302907f68cd81483fd444c0a417f99720520dfcc39029077e9dc81482ff32c40a417f99420520fdd22102905fe64c81483fb46640a417fa995c520bfccc2e2906fea2171483bf30eb8a41dfa775c520bfccb2e2907de25571483bf2eab8a41f7a555c520fdd222e2907f68cd71483bf2e4b8a41fea225c520ff840ae2905fe660714837f51038a417f9961c520bfcca0e2907ee91071482ff32638a41fda331c520bfcc90e2907fa88871482ff330a8a41bfa8854520bfccbaa29077e9dd51482ff32ca8a41f798554520fdd222a2907f68cd51483ef2a4a8a41fea2254520ff8b8aa2905fea6541482ff330a0a41bf89850520dfd44282905fe65d41483bf4eea0a417f99650520bfccaa82907de95541483f7308a0a41fb95450520fdd22282907f68cd41483f7284a0a41fea2250520ff8b8a82905fe660414837f51020a417f99710520efd3b882905fe64c41483fb46620a417f99210520ff511082905fea6531482ff33098a41bfa884c520bfccba629077e9dd31482ff32a98a41f7a554c520bfcca262907ee91131483fb30698a41fd9534c520feca1a62907fc5c531482ff53290a417f99848520dfd44242905fe65d21483bf4ee90a417f99548520fb) else (if i<3 then 0x4308f7d9dd21846feb2c90c237f59448611fdb2224308dfd64d21847fac6690c23fe62248611bfacb10f08dfd65087846feb2643c237f59221e11bfa4c4ef08f7d26277847be9293bc23df4929de11bfacb2eb08dfd65c84847becee424237f59321211bfac910908dfda6574846fe930ba423df6775d211bfacb2e908fdd95574846feb20ba423bf5981d211bfac98e908dfd64874846fed32aa4237f59755211efb3baa908dfd65954847eeaeaaa423fb57455211bfa4c48908f7d9de44847eecab22423fb57491211fdaaa48908fed26244847f692f22423fb48791211fdb3bc8908fed5d644847f6925224237f6995ce11bfa4c2e708f7d9dd73846feb2cb9c23f76555ce11fdb222e708dfd64173846feb2ea9c23df67754e11bfacb2a708fdd5d553847f6c88a9c23fd57354e11bfb4ca8708dfd26143846feb2ea1c23df67750e11bfacb28708dfd65543847eecaaa1c23fb57450e11fdb2228708ff55cd43846feb20a1c23fd4878ce11feb3bc6708ff55d633847fa90919c23fd5748ce11fea3a46708ff555233847fac8919c237f59720a11efb3b90508dfd65082847f6c88414237f6995ca11bfa4c2e508f7d21d72847beceeb94237f5965ca11fbb2aae508fed91172847fa926b9423df5735ca11feb19ae508dfd64172846feb2839423fb6441ca11bfac80e508dfda6552846feb2ea9423df67754a11bfacb2a508fdd55152847f6c88a9423f755354a11feb19aa508ff95c952846fed32a14237f49850a11bfacba8508f7d9dd42846feb2ca14237f59550a11fbb2aa8508fed21142847f68e8a1423fb55450a11fdb2228508fed50d42847fac66a1423fe57250a11bfac828508dfd65c42847becee214237f59510a11fbb2a88508dfd65d32847becee994237f5954ca11fbb2aa6508dfd65132847f6c8899423fe5724ca11bfac826508dfd26222847becef11423f765588a11fdb2244508ff95ca22847fcaa511423fe54288a11ff24c44508ff925e22847fc90f11423fe67788a11ff2bac4508ff925222847fc90911423fe57488a11ff23a44508ff955222847fcc8911423fe57388a11ff2a9c4508ff950e228477f12f44241bf894a2120dfc48d10905fea65874837f510c3a417f99661d20fec49b0e906fe61c87482ff32c43a417f99421d20bfcc990e905fe644874837f5113ba41df9879dd20efc4c4ee9077ea2277483bf1293ba41df8919dd20bfd4cb0a906fea21854837f30ec2a41dfa7761520bfccb30a907fc24585482ff330baa41bfa885d520bfccb2ea907dea2255483ef30f2aa417fa9961120dfd44308906fe61d84483bf4eec22417f99661120fbd2ab08905fe65c84483bf4ee422417f99521120dfcc2908907de95484482ff326422417f99121120bfd4cae8905fe661744837f510ba241dfa775d120bfcc else (if i<4 then 0x98f7d5d5714c7eecaab8a63bf5845c531fdb222e298ff554d714c7faa86b8a63df5725c531fea992e298ff9889714c67fb30a0a633fd97a21219fecb51090cff656884867fb29442433fd93a21219fec851090cffa65874867fb2cc3a43b7c9561d21dee49b0e90cff641874873fb0e43a433fc989dd21cfec3cee90e7f262774873fd113ba439fd869dd21cfec04ee90cffa65854873fceec2a433fd96615219fecc2ea90edfa22554876fb0f2aa43d7e7795521dbec34aa90cffa65844873fceec22433fd9661121dbf2ab0890cff6418448777b08422433fd985d1219fe4c2e890cff66074486dfb2c3a24377d951d121beec98e890dfb64874486feb223a2437f9901d1219fecc2a890eef611544867f93122243bbd8491121dde4c48890eefa224448777b0f22243dbe7791121ddec348890eef61644487e7cab22243bbd80911219ff4cb0690e7f9dd834876fcaac1a43bbe4460d219fec830690cff661734867fb30a9a433fd9850d21def4446690ef761e33487bbcef19a43bdd858cd21faf2ac6690ef761233487f3c8919a43bdd808cd21bf74caa490efba21524877db0ea9243dee7754921fb6aa2a490feb91152487edaa6a9243fce3354921df6c3c4490f7b9de224877db0b11243f6e5588921df6c244490feb912224877db01112433fd985c5219fecc28290dfda65314877ed1098a43bf5874c521efb3ba6290fdd95531487f6c8898a43fd5534c521feaa1a6290ff954931486feb2098a433fe9961c21cff4cb0e10e7f651870873f928c38439fd879dc21afecc4ee10ebf9dd860876fceec28433fe9961021cff3bb0810eefa658408777b2ec2043bbc9761021ddf3bb0810cff661740873fb0eba043afd865d021dbec2ae810eef611740867fb303a0439fd871d021b7ecb0e810ebf61874086efb2a3a043b7d851d021ddec20e810df764c74086fdb243a0437f5911d021bfcc80e810e7f61e440875fb0d22043b7d8591021ddec248810def6624408777b0f22043dbe7791021def3bb0610ef75d1830877b8e8c1843bde4460c21dfd3bb0010efe5d1800877f0e8c0043bfa44600219fe4c4ef08e7f262778467f930ba4236fd961d211bbeca8e908df764c74846fdb243a4237f5911d211bfcc80e908cff262448477793122423dbe7791211dee4c46708f779de33847f3c8919c233fc985ca11bfac88e508dfe640728467f930a142377d9510a11bfac888508dfe640428467f93111423bec9888a11ef73bc4508feb91222847f9c6711423df6775c611bfacb2e308fed91171847fac66b8c23df5725c611ff3112e308dfd65d41847beceea0c237f59650611fdb2228308ff58cd41847f6a84a0c23fe62250611bfacba6308f7d9dd31846feb2c98c237f5944c611fdb2226308ff550d31847faa6498c23fe6224c611bfacba else 0xfcf956445077b93119a83bde888cd41deec3c66a0f779de335077bb0d19a83bdd858cd41faf2ac66a0fe755233507f3c8919a83bdd808cd41bbeca904a0efb60882506ff320412833fc985c9419fecc0e4a0def65072506feb22392837f9901c9419fe4c2a4a0edf61552507e7aa8a92837be9950941ddf44284a0f6f9dd4250777b0ca12837bd9550941ddec2a84a0fcf95542507f3c66a1283fac8250941fd6b9284a0fed24542506f7b20a1283bbd80509419fe4c444a0feb50a225077d93111283bee8888941df6c3c44a0f7b9de225077db0d11283bed8588941fb72ac44a0feb25222507f5aa911283fae4488941fe719c44a0efb602225067fb30b8a837f6995c541dfb442e2a0f7d21d71507beceeb8a837f5965c541fba4aae2a0efd61571507beaeab8a83f76555c541fda4a2e2a0fed55171507f6c88b8a83fd6335c541efab92e2a0fed50971507fcc44b8a837f5905c5419ff4cb0e20e7f61e771073fceec1883bdd9760c41def3bb0620ef7649831067fb30b9883bdd835cc41deec3c6620f779de331067fd32c10839fe7760841def19b0420cff661721073fb0eb9083bdd835c841df6c12e420cff660721077bb06390837f9901c8419fecc26420ef760d321077bb0711083bed8288841df6c3c4420f7b9de221077db0711083fce33888419fecbd1098cff65a884c67fb2b442633fd94a21319fec951098cff642884c67fd32c3a633fd9661d31dbe4ab0e98cff641874c73fb0e43a636fd9621d319fe4c4ee98e7f61e774c73f9313ba639fe889dd31cfec34ee98f7d246774c73fb013ba633fe9961531cff3bb0a98cff659854c67fb30baa63b7e8895531dbec3caa98f5f9de554c76fb0d2aa633fe9961131cff3bb0898cff659844c76fcaac22633fd9061131ddec210898cff661744c67f930ba2633fd981d131b7ecb0e898ddf654744c6fbb263a2637ed921d131bfac88e898dfe640744c67fb30aa2633fc9891131ddec248898eef262444c777d1122263bbd8791131edf3bc8898eef61a444c777b0b22263f3e5591131ddec048898ef7a21534c77bb0ea9a63dde7754d31deec32a698fd75d5534c7f3c88a9a637de9950d31def4428698ef761d434c7bbceea1a63bdd8650d31beecaa8698fd7955434c7f3908a1a63f9d7450d31fcf2228698df7641434c77bb00a1a633fc985c931cfec3ae498cff261524c76fb0aa9263f5d53549319fe4c28498eef611424c7f3a86a1263bde884c931eef3ba6498df7655324c7ebcaa992637dd944c931fcf2226498ff35c9324c6fbb2099263bdd804c931df74444498efb61e224c7bdcef11263bed8588931fb72ac4498efb612224c7f5c8911263fcd5388931fe6a1c4498efb602224c67fb30b8a637f6995c531dfb442e298f7d21d714c7beceeb8a63f74955c531dfac2ae2))) else (if i<7 then (if i<6 then 0x35cd4388afdb20a1c45fce778ce22fe6bac67117f35d23388bf98e919c45fcd548ce22fe722467115fb65c8188bbdcee40c457ed9420622fd722103115df656885c67fb2d442e3b7d95a21719fecad10b8cff652885c67fb27442e33fd92a21719fec8510b8e7f61a775c73fb013bae3b7e8821571cff442eab8ddf262555c76fd112aae3b7d8695571dbe42b08b8eef610845c6fbb26422e3d7d75551719fe4c488b8eef262445c777d11222e3dbe7791171ddec3488b8fcf216445c7b7aeb222e3f3e5591171fda48c88b8eef602445c76f90ac1ae3d7d7554d71dee4c466b8ef7a22335c7bbcef19ae3bdd868cd71fae42c66b8f775d6335c7ebcab19ae3f9e448cd71deec0466b8edf215825c76f90a412e3bed8220971bfcc8104b8d7fa65725c73fd10b92e39fd865c971ebe42ae4b8f5f955725c7b7c88b92e3ddc935c971eef19ae4b8f7b209725c7be922b92e35fd905c971cfec02e4b8cff261525c6bfb2ea92e3ded72549719fe4c284b8f7b5c9425c67fb30212e35fd9710971bbeca884b8dfd644425c6ff320212e3ded724c9719fe4c444b8f7b5ca225c77d931112e3bee8888971ef64bc44b8f7b9de225c77db0d112e3f6c8588971ef6bac44b8fdb956225c7f5c89112e3fce3388971df6c0444b8ebf651861c75fb26c30e3afd92618719ff4cb0838cff659841c75fb0d220e3bbd8491071ddec348838cff659831c777c88c18e33fd9850c71d7ec328638eef611431c77bb06a18e3bdd868cc71deec246638fe7912331c67fd32c10e33fd9660871ddf2230438ef78cd821c67fb30a10e3afd8650871ddec228438efb609421c67fb30210e3afd8610871bbeca88438dfe640421c67fb30990e3afd864c871deec1a6438efb609321c75fb0d110e3bed8288871df6c344438efb612221c7f5c89110e3bed8388871fe719c4438cffa65875467fb2cc3aa39fd869dd51ddec3c88a8f6f9de4454777b0d222a3bdd878cd51eef3bc66a8ef761a33547f3c8919aa377e9954951ebf3baa4a8edf61952547e7c88a92a3f5e3354951fb6b92a4a8cff66042546efb2a212a37f99010951fb6a9444a8efb61e22547bdcef112a3bed8688951fd722444a8ff38ce22546fed32b8aa3fb6445c551feb19ae2a8f7d5c971547eeaa4b8aa3fe6225c551bfcc8510a0cff65e885067fb2d442833fd95a21419fec9d10a0cff64a885077f321442833fd90a21419ff4cb0ea0cff659875076f92ac3a833fd9061d41cfec390ea0dbf658875067f9313ba839fd879dd41cfe4c4eea0e7fa22775073fb0d3ba83df4919dd41cfec04eea0cffa65855073fceec2a833fd96615419fecc2eaa0edfa22555076fb0f2aa83d7e7795541dbec34aaa0defa655450777d10aa283bbd8755141edf3baa8a0fcf5d55450777b0f22283dbe7791141ddec2c88a0 else 0x25550b77d103a285bbd871d142bdec98e8a15ef6447450af7d32aa285bbe8855142ddec3aa8a176f9dd5450af7b2caa285f3d7555142bdec82a8a16ef61e4450bb7cef22285bbd8591142f9f2ac88a15efa654350b77d10a1a85bbd8750d42edf3ba86a15ef6554350be7caaa1a85f9d7350d42bdec8286a16f7a223350b7bb0f19a85dde778cd42deec2c66a17d79563350bf38e919a85f9d548cd42fcf22466a16f76023350a7fb30b92857ee995c942df7442e4a177b21d7250bbdceeb92857ed965c942df6c2ae4a17db9557250bf5928b9285fad545c942fd7222e4a17f324d7250bbdae6b9285fad435c942fe719ae4a15fb6417250b7db00b92853fd9854942f9eaa2a4a15f764c8150b7eb0240a853fe9961c42cfec3cee2167f9dd8510b6fb2ec2885b7e7761442dbec8b0a214ff6617510b6fb0aba885b7d8795442ebf3bcaa214ffa658110b3fceec0885b7e5560442dfd3bb00216fe5d58010a7fd32c3a653fd9061d32cfec3cee9967f602774ca7fd32c2a659fe77615329fec830a994ff661754cb6fb0f2aa65d7e7795532dbec04aa994ffa65844cb3fceec2265b7e55611329fec8308994ff661744ca7fb303a2656fd961d132bbeca8e8995f764c744cafdb243a2657f5911d132bfcc80e8994ff661544cb77b0922265bbd8791132edf3bc88996ef616444cbe7cab22265bbd8091132bf74cae49977b9dd724cb7db0ab9265f6e555c932df6c22e4997eb911724cafdb20b9265bed805c9329fe4c4ef1167f2627788b6f9312ac45d7e77956229fe4c2e9115bf6587488aefb2a3a4457dd931d222bf6c90e9115fd6447488aff3203a4453fc9891222dde4c4891176f9de4488be7cab22445dee775ca22fb72aae5117eb9117288afdb20b94457ed9754a22ef73baa5117db5515288bf5c88a94457ed9054a22bf6cba851177b9dd4288afdb2aa1445f6e5550a22fd63a285117eb5514288bf5c88a14457ed9050a22bf6ca10f115fb6448788afdb2043c457ec989de22ef64c4ef1177b2527788bbd9233bc457ed965d622bf6c82eb115fb65c8488bbdcee424457ed9521222fb72a909115fb6448488afdd32ba4457ec985d222ef73bae9115fb6597488bedcaaba4457ed905d222df6cc0e9115fb64c7488afdb223a4457ee9955222bf64c2a9115fb65d5488bbdceeaa4457ed9655222fb6baaa9117eb2115488bf5ae8aa4457ed9055222bf64c4891177b9de4488bedcab22445fad7491222fd6aa489117eb2624488bf592f22445fac8791222fd73bc89117eb5d64488bf5923224457ee995ce22ef73bae7117db9557388bf5c88b9c457ed905ce22bf6cbaa71177b9dd5388bedaeaa9c45fae4454e22fe6b9aa7115fb6415388afdd32a1c457ed9750e22ef73ba87115fb6554388bedcaaa1c45fad7450e22fd722287117f) else (if i<8 then 0x8550e7fb20c2a873fd985d543dbec2aeaa1edfa225550f6fb0f2aa87d7e7795543dbec34aaa1edf6025550e7fb30ba2877be995d143ddf442e8a1f6f9dd7450f77b0aba287f3e555d143ddec3c88a1f6f9de4450f77b0b22287f3e5591143bef4cae6a1ef7a217350fbbceeb9a877dd965cd43deec2ae6a1fd79557350ff3ae8b9a87f9e445cd43beec82e6a1f77252778cfbb9233bc677dd965d633beec82eb19df7a65748cefb930ba467dde775d233beecb2e919fd7955748cefbb20ba4677dd921d233beec88e919df7a65548cefbb2eaa467dde7755233beecb2a919fd75d5548cff3ae8aa4677dd9055233eef3bc8919fd7956448cff3ae922467f9d5491233fce4bc8919fe79de448cff3aeb22467f9c9191233beec9d10b94ff65a885ca7fb2b442e53fd94a2172deec9d10b94ff64e885ca7fb23442e53fd90a2172cfec34eeb967f602775cb6fd112aae5b7d8695572dbec04aab95df654845cb77b08422e57f990211729fe4c488b96ef262445cb77d11222e5dbe7791172ddec3488b97cf956445cbf5925222e5bbd8091172def44106b97779dc835cb7bb0a41ae5f5e5520d72deec2106b97e7910835cabfd32b9ae59fe885cd72ebf2aae6b976f911735cabfb20b9ae5ddd7354d72eeeb9a86b95f7262335cb7bd1119ae5dde778cd72faf2ac66b97e7912335cb7bb0119ae5bdc8360572b7ecb102b96f720c815cb7eb0240ae53fe99610729fec8308396ef612441cb77b01220e53fe9960472ddf22302394ff641811cb7f328c00e5bfa4460072dfcc8b00394ff65e8854a7fb2d442a53fd94a21529fec9d10a94ff6468854a7fb21442a53fe9961d529fecb30ea96f724d8754a7fb20c3aa59fe889dd52cfec34eea967f6027754b77b08422a53fc985d152bbf4caa8a96dfa215454b6fb0eaa2a5d7e7755152bbecb2a8a96df6195454be7908aa2a5f3d7455152bbec82a8a96df6015454a7f931222a5f3d5491152dde4c488a96efa224454b77b0f222a5dbe7791152ddec3488a96ef6024454b6fd10a9aa5b7d8754d52ebf3baa6a97cf9115354bebae6a9aa577d9054d52dbec02a6a95df6554354b7bd1119aa5bdd878cd52eef3bc66a97d75523354bf3c8919aa5bdd808cd52bf74cae4a96fba217254bedaa8b92a5fae445c952fe649ae4a977b5cd7254bedaa6b92a5fce335c952bf6c82e4a96fb6017254adfb2d442853fd97a2142d7ecb510a14ff65a8850a7fb2b442853fd93a21429fec8d10a14ff6428850a7fd32c3a853fd9661d42dee49b0ea14ff6418750b3fb0e43a857f99021d429fe4c4eea167f61e7750b3f9313ba859fe889dd42cfec34eea177b24a7750b3fb013ba853fe9961542cff3bb0aa14ff6598550a7fb20c2a853fd985d542dbe4c4aaa16dfa225550b6fb0f2aa85d7e7795542dbec34aaa16df6 else (if i<9 then 0x4877fb0b22243bfd8091121dfeba30690eff551834877fc88c1a437fe995cd21dff442e690eff615734877fb08b9a437fd905cd21dfec02e690effa2153486ffb2ea9a43f7d7554d21dfec22a690ff75cd53486ffd32a1a43bfe8850d21bfecba8690dff655434877fb0aa1a43fbd7450d21feeb9a8690dff641434877fb00a1a437fe995c921dff442e490eff615724877fb08b92437fd905c921dfec02e490dff65d52487efaa8a9243fed7254921ff6ba2a490ffb91152487fdae6a9243fed4354921bff4ca8490effa2142486ffb2ea1243bfd8750921bfecaa8490eff61542487f78e8a1243fbd5450921ff6b928490ffb54942486ffb20a1243bfd8050921feea1a6290ffd5d131487feaa898a43ff6444c521bff4cae810dff66174086ffb24ba0437fd905d021bff4cae908dff65974846ffb20ba4237fd931d211bfec90e908dffa6573846ffb2cb9c237fd905ce11bff4ca8708dff65d43846ffb2ca1c23fbd7450e11feeb9a8708dff64143846ffd32b94237fd965ca11fee49ae508f7f5cd72846ffb20b94237fd941ca11bff4ca8508dff65d42846ffb2ca1423fbc7450a11fdea1a8508ffb5c942846ffb20a14237fd9710a11bfecba6508dff65132847fdae4994235fd9321277afec91093bd7f644849debfb28414ef5fd9120a77afec81053bd7f658819debfb2840cef5fd9320677afec91033bcff65a885d27fb2b442e93fd93a21749fec9510ba4ff646885d27fb21442e99fd869dd74cfec04eeba6dfa22555d36fb0d2aae9b7d8095574df6c1104ba5fe640825d37eb0240ae9bdd9260c74deec8b063a4ffa65821d37f320c10e9bee9960874df6c9b043a6fb645821d37d922c10e93fe9960474dfb4cb023a6fd64d811d37eb24c08e9bf492604749ff4cb0eaa4ff659875527fb20c3aa99fe889dd54cfec34eeaa67f602775536fd10baaa977d965d554bbec82eaaa5efa657455377d10ba2a93fc989de44cfe4c4ef2275f9de55913b7ceeba489f3e555d244bdecbaa92276f9dd54913e7aeaaa4897bd9321e44bdec910f225ef64487912f79313bc89dbc989de44ede494ef2276f24677912f7b2cbac897bd905d644bdecb9052276f9dc82912f7b2a41489f3e5520a44bdec8905225ef65c81913b7cee40c897bd9320644bdec91032267f61a775cf3fb013bae7b7d8695573dbec04aab9eef262445cf77d11222e7dbe7791173ddec3488b9fcf956445cf77b01222e73fd9661d539fec830ea9e7f61a7754f3fb013baa777d905d553ddec3c88a9f6f9de4454f77b0d222a7f3d7591153ddec0488a9df76597354ff3c88b9aa77dd905cd539ff4cb0ea1cff6598750e7fb20c3a879fd879dd43cfe4c4eea1e7fa227750f3fb0d3ba87dbc949dd43cfec04eea1d7f25d8550e7fd32c2a879fc9761543cff3bb0aa1cff659 else 0x77fd10a12e37fd9650971fbe42a84b8f7f5d5425c7f7908a12e3fbd5450971fdea1a84b8f7f5c9425c6ffb20a12e3bfd8050971dff44264b8eff619325c7ef90a992e3dfd754c971bfeca264b8eff609325c6ffb20992e3bfd804c971dfeca30438eff911821c77fb06a10e3bfd8250871dfec226438eff612221c6ffd32ba2a37fd965d151dfec32e8a8dff64174546ffb2cb9aa3bfd865cd51bfec82e6a8dffa6543546ffb2ea1aa37fd9650d51dfec3286a8fef5d143547fbae6a1aa37fd9050d51bff4cae4a8dff659725477fb0cb92a3fdc935c951efeb9ae4a8dff64172547efae8a92a3f7e4454951fbeb9aa4a8fdf50d52547efae4a92a37fe9950951bfecba84a8eff61d42546ffb2ca12a3fbd4350951ff6b9284a8fdf54942546ffb20a12a37fd9710951bfecba64a8eff61d325477fb0c992a37fd944c951dfec1264a8ffb5c932546ffb20992a3ff5425c551ffa992e2a8dff64c87506ffb2443a83bfe885d541bfecb2eaa0eff61975506ffd32b9a83bfe885cd41bfecb2e6a0eff619735077fb0ab9a83fbd545cd41bfec82e6a0eff601735077fd10a9a837fd9754d41bfecb2a6a0eff61953507efaeaa9a83fdd7354d41bfecb904a0dffa65725077fd10b92837fd965c941dfec32e4a0eff61572507f7aa8b9283fdc935c941efeb9ae4a0dff641725077fb00b92837fd9754941bfecb2a4a0fdf55152507efaa6a9283fed7254941fdebaa84a0fef5cd42507f7aa6a1283fbd7250941dff44264a0dff65d325077fb0e99283bfd864c941bfecaa64a0eff61532507f7aa899283bfd824c941ff6b9264a0dff641325077fb0099283ff5325c541dfecbb0420eff9dd821077fae6c1083bfd825c841dfec3a6420eff61e22106ffb2843a637fd965d531bfecb90898dffa65744c77fd10ba2637fd965d131dfec32e898eff615744c6ffb20ba263bfd805d131bff4caa898effa21544c6ffb2eaa2637fd9655131dfec32a898fdf5d5544c7f7ae8aa263bfe8891131dfec2c8898eff602444c7fbae8a9a63fde4454d31feeba28698ff7551434c6ffb20b9263f7d5454931bff4ca8498effa21424c6ffb2ea1263bfd8750931bfecaa8498eff615424c7f7aa8a1263fdd9350931feea9a8498ff750d424c7fdae4a12637fd9050931dfec028498ff75d1324c7fbaa899263fde444c931feea1ae298ffd509714c7fba86a0a63bfd8721d21bfeca10e90effa22774877fb0d3ba43bfd809dd21dff442ea90dff659754877fb0cbaa43bfd7561121bfecb90890eff61084486ffd32ba243bfe885d121bfecb2e890eff619744877fb0aba2437fd905d121dfec02e890eff660744877fd103a2437fd931d121bfec90e890eff60074486ffd32aa243bfe8855121bfecbaa890dff659544877fb0caa243f7d7555121fdeba2a890effa2244)))) else (if i<15 then (if i<12 then (if i<11 then 0x209ab89a909a2899c0995898f09848982097f897509728970096d896309608956094f8945093689300921891f0910890e090b89090902890008f188eb08e088da08d788d508d288d008c988c308c088be08bb88b508b288ac08a5889f08988892088b888908828880087d88770870886a08678861085e885c085988570854884e084b884908428840083d883b083888360833882d082a88240819880b080087f607eb87dd07ce87c007ad87a30798878a077f8775076a87600755873f072c8712070386f506e686cc06b18697067c866206478639062a861c060d85ff05ec85e205d385c505b685a805998583056c855e054f854105268514050984fb04f084e204c784b904aa849c048d847f0470846204538445043684280419840b03fc83ee03e383d503ca83bc03ad839f03908382036b835d0346833803218317030882fa02eb82d502c682b002a1828f0280826e02638259024a823c022d821f0210820201ef81e101d281c401b981af01a48192017f816d015e8154014581370128811a010780fd00ee80e000cd80bf00b080a60097808d007e80700061804f004080360027801d001280006ff608825d2ffb22412e97fd9220574dfec1102ba6ff604815d37fb22c10e97fd9655173bfec82a8b9eff6197454f7fb00ba2a7bfd8091153bfec8908b95ff659545caffb20aa2e57fd9420572dfec2102b96ff604815cb7fc88c08e57fe995d152dff442e8a95ff6597454b7fb0cba2a57fd905d152dfec02e8a97df5d15454b7fd11222a5bfd8091152fbeaa2e6a96ff6017354befae8a9aa5f7e4454d52fbeaa286a96ff6014354befaa8b92a57fd905c952dfec02e4a96ff2458750affb2643a857fd9121d42dff442eaa16ff6197550affb20baa85bfd805d542bff4cae6a16ffa217350b7fb0ab9a85fbd545cd42bfec82e6a16ff6017350b7fd10a9a857fd9754d42fbebaaa6a17f75cd5350affb20a9a85bfd8054d42bff4cae4a16ffa217250b7fb0ab9285fbd545c942bfec82e4a16ff6017250bfd930b9285fec915c942bff4caa4a16ffa215250affb2ea9285bfd8754942fbeaa2a4a17fb5c95250affb20a9285bfd8054942bfecb902a16ff61c8150affb2640a85bfd8320542fdea1902a17fb5c88150b7fb0240a85bfe7760442dfebab02215ff659754caffb20baa65bfc9161132bff4cae8995ff659744cb7fb0aba2657fd925d132bfec82e8996ff601744caffb223a2657fe9955132bfecbaa8995ff659544cbefaeaaa265fbd7455132bfec92a8995ff641544cb7fb00aa265bfd8591132dfec0488995ff6417588affd32ba4457fc985d222bfec92e9115ff6417488affd32aa4457fc9855222bfecbaa9117df5d55488bf7ae8aa4457fd9255222bfec82a9115ff648845c6ffb2ca1ae37fd9050d71bfeca104b8dffa65425c else 0x2165f96551652964c1645963f163096261613960915fa95f015e595e315dc95da15cf95cd15c695b415a5959f1598958a157f9575156a955c154d953f1538952e15239511150294f814ed94df14d094c614bf94b514a694981489947b1468944e143394251412940413f993eb13e093d213c393b913aa93a0139593871378936a135f9355134e93441335931b130c92fe12ef92d512c692b812ad92a71298928a127b926d125e92541245923b12349232122b9229122692181211920711f491ea11e391e111d691d011cd91cb11c891c211b791b111aa91a01199918f1188917e1177917111669160115591531148913e113b9131112691241119911711109106110390fd10fa90f810f190eb10e490de10d790d510d290d010c990c310c090ba10b390ad10a690a4109d909b1094908a1083907d10769070106d9067105c9052104b9049104690441041903f103c903a103790351032902c10259023101c901a10179011100a900810018ff70ff48fea0fe38fdd0fd68fd40fcd8fc30fc08fb60fb38fa90fa28fa00f9d8f9b0f988f960f8b8f890f868f7c0f798f6f0f6c8f660f5f8f590f528f480f418f3b0f348f2a0f278f1d0f168f140f058eff0ef48ef20eeb8ee10ede8ed40ed18ec70ec08eba0eaf8ea90ea28e980e918e8b0e848e7a0e738e690e628e580e4d8e470e448e3e0e378e310e2e8e280e258e1b0e188e0e0e078e010dfe8dfc0df98df30df08dea0de78de50de28de00ddd8ddb0dd88dd60dcb8dc90dc68dc40dc18dbf0dbc8dba0db78db10daa8da40da18d9f0d9c8d9a0d978d950d928d8c0d898d830d808d7e0d778d750d6e8d6c0d658d630d588d560d538d4d0d468d400d398d330d2c8d2a0d238d210d1e8d1c0d198d130d108d0a0d078d010cfe8cfc0cf98cf70cf48cee0ceb8ce10cde8cdc0cd18ccf0ccc8cca0cc78cc10cba8cb40cb18caf0cac8ca60ca38ca10c9e8c980c958c8f0c8c8c8a0c878c850c828c7c0c798c730c708c6e0c6b8c690c668c640c618c5f0c5c8c560c538c510c4e8c480c418c3f0c388c360c2f8c2d0c2a8c280c218c1f0c188c160c0f8c090c068c040c018bff0bfc8bf60bf38bf10bea8be80be58bdb0bd48bce0bc78bc10bba8bb80bb58baf0bac8ba60ba38b9d0b9a8b940b8d8b870b808b7a0b738b6d0b628b5c0b518b470b448b3e0b3b8b310b2e8b280b258b230b1c8b1a0b178b150b0e8b0c0b098b070b008afe0af78aed0ae68ae00ad98ad70ad08ace0ac78ac10aba8ab40aad8aab0aa48aa20a9b8a950a8e8a880a818a7f0a7c8a7a0a778a750a728a700a698a630a608a5e0a5b8a590a568a500a4d8a4b0a448a420a3b8a390a328a300a2d8a230a208a1a0a138a110a0a8a040a0189ff09f489ee09e789e509e289e009dd89db09d489ce09c789c509c289c009b989b709b489b) else (if i<13 then 0x6292fa9292926a9202915a90f2904a8fa28f3a8f128eea8ec28e9a8e728e4a8e228dfa8dd28daa8d428d1a8cf28cca8c628bfa8bd28b2a8b028a5a89f2898a892288fa8852882a8782875a86b2864a862285fa85d2856a8542851a8472844a83a2837a829281ea8142809a7ff27f0a7e627dba7d127c6a7bc27b5a7af27a4a79a278ba789277aa7702765a75f2758a7522747a7412736a734272da7232714a70626ffa6f926f2a6e826e1a6db26d8a6d226c7a6b526a2a6a02695a68f2688a6822673a669265ea6502645a6432640a63a2633a619260aa60025f1a5df25d0a5c225b3a5a925a2a5902585a57b2574a56e2567a5612556a5502545a543253ca536252ba5212512a50824fda4f724eca4e624dfa4d924d2a4c824b9a4ab249ca496248fa48d247ea4782471a46b245ca44e2443a439242aa41c2411a40f2404a3fa23eba3dd23cea3c823c1a3bb23b8a3b223afa39d2396a3902389a3872380a37a2377a371236ea368235da357234ca3422333a329231aa318230da3072304a2fe22fba2f922f2a2e822e1a2d722c8a2be22afa2a5229aa2902281a277226ca2622253a24d223ea2382235a227221ca212220ba20521faa1f421eda1df21d4a1ce21bfa1b921aea1a8219da1972190a1822177a16d2162a15c2151a14b2144a13e2133a12d2122a1182111a1072100a0fa20eba0e920e2a0d420c5a0bb20b0a0a2208ba07d206ea0682061a0572050a0462037a02d2022a0202011a00f2008a0021ff39fe91fde9fd81fcd9fc71fbc9fb21fab9fa51f9a9f941f8d9f871f789f721f6b9f691f5e9f581f4d9f431f389f2e1f2b9f211f169f0c1f019ef31ee89ee21ed79ed11eca9ebc1eb19ea71e989e861e7f9e791e6a9e641e5d9e471e389e261e179e091dfa9dec1de19dd31dc49dbe1db79db51dae9da81d9d9d931d889d7a1d6f9d651d569d501d419d3b1d389d2e1d1b9d151d0a9d041cf99cf31cec9ce21cdb9cd51cca9cc41cbd9cbb1cb09ca21c979c911c869c801c7d9c6f1c609c521c439c351c269c181c099bfb1bec9bde1bd39bcd1bc69bbc1bb99baf1ba89ba61b9f9b991b8a9b841b7d9b6f1b649b5e1b579b491b3e9b381b259b1b1b189b061aff9af91af29adc1acd9ab31aa89a9e1a879a7d1a6a9a641a599a4b1a409a321a279a151a0e9a081a0199f719f499ee19eb99e119de99d419c999c319bc99b619af99ad19a69998198d9983197c99721967995d194a99401935992b19249916190b990118f698e818dd98cf18c898b618a3989d189a988c1881987b1874986e1867985d18569850183d9837182c982a18239815180a980417f997f317f097e217d397c517aa9790177597571748972e171f9711170296f816f196eb16e096de16d796d116ce96c816bd96b716b096aa16a39695168a967c1675966b1668966 else (if i<14 then 0xe3ac3bab53aaabaa03a91ba8b3a80ba763a6bba653a5eba543a49ba3f3a38ba323a27ba1d3a16ba0c3a01b9fb39f0b9e639dbb9d539ceb9c439b9b9af39a8b9a23997b9893982b978396db95f3954b94e3943b9393932b92c3921b91b3914b90e3907b8fd38f2b8e438d9b8cf38c4b8be38b7b8b138aab8a438a1b89f389cb88e387fb871386ab85c384db8333824b81a380fb80137f2b7e837ddb7d737d0b7ca37c3b7b937b2b7ac37a5b79f3798b78e3787b7853782b7803779b7773770b76a375fb755374eb74c3745b743373cb736372fb72d3726b724371db7173714b70e3707b70136fab6f436edb6e736e0b6de36d7b6d536ceb6c836c1b6bb36b4b6ae36a7b6a5369eb694368db687367cb676366bb665365eb6583651b64b3644b63e3637b629361eb6103609b60335fcb5f235e3b5dd35d6b5d435cdb5c735c0b5ba35b3b5ad359eb5983591b58f3584b582357bb575356eb5683559b5533544b53e3537b535352eb5283521b51b3514b512350bb5093502b4fc34f5b4ef34e8b4e634dfb4d934d2b4c834c5b4c334c0b4be34bbb4b934b6b4b434a1b497348cb4823473b461344eb4443439b42f3428b41e3413b40133feb3f433e9b3e333dcb3d633cbb3c533beb3b433a5b39f3390b38a3373b36d3366b3603359b34f3348b33a332bb325331ab3183315b3133308b2f632e3b2d532d2b2c832c1b2bb32acb2a2329bb295328ab2803275b26b3260b2523243b239322eb224321db213320cb20631ffb1f531f2b1e431ddb1d731ccb1c231bbb1b531b2b1a4319db1973188b182317bb175316ab1683161b1573150b142313bb1313122b11c3115b10330fcb0f630f3b0e930e6b0dc30d5b0cf30c0b0b6309fb0913082b07c3075b06f3060b056304bb0413032b0243019b00f2ffcaff62fe7afe12fdeafd02fc1afb72facafa62f9faf992f8eaf7c2f71af6b2f64af562f4faf492f3eaf382f31af272f20af1a2f0baef52eeeaee82ed9aecf2ec8aebe2eb7aead2ea6ae9c2e95ae8f2e88ae7a2e6fae5d2e52ae442e3dae372e2cae262e1bae152e0eae042dfdadf32de0adda2dd3add12dc6adc02db1ada72d98ad8a2d7fad6d2d5ead502d45ad3f2d38ad322d13acfd2cfaacec2ce5acdf2cd4acca2cbfacb52ca6aca02c99ac8f2c88ac822c7fac7d2c6eac682c61ac5b2c50ac4a2c43ac392c32ac302c29ac1b2c10ac062bffabf12be2abd42bc5abb32ba0ab922b83ab752b6aab642b61ab5b2b58ab522b4bab452b32ab2c2b19ab0f2b08ab022af3aaed2ae6aae42acdaabb2aa8aa962a83aa752a62aa582a51aa4f2a4caa462a3faa392a2eaa242a21aa172a14aa0a29ffa9f929eea9e829dda9d329cca9c229bba9b529aea9a829a5a9a329a0a99a2993a9892986a980297da973296ca9662963a95d295aa9542949a943293ca93 else 0xe5a3c61f1f2c30f8f96187c7cb0c3d3d5861eac9e30f4f56187cb478c3e5a3c61f1f2c30f8f961f8150bc0aa5861a5a2032a2d18195168c0ca8b4606545a3032a2d1f816a5157f17c0a9587e05e5411fc5f02a561f817a696ff1458bc406545e30d2f2d18696978fc0bd28abf8be054ac3f02f4d2dfe287ff178fc23f797881de02c3f08fde16278150834744041a543022a0d18106950c0834a8604541a3020d2a1f847ef0693c034a87e01a5439b1b8f187c7883e3c41f1e2de0f2a8f26f07954793783c363c9e03a2c3161d1780e8b0fc058747e02c3a32a02161f815010b13c07440c1a2c30c0d161c78587f8103c77c073c1fe03f01610786f80c6c3c43be02c31d0e0f1f80e8b0fc23f78589e09e543f01617827868c3d3c42c9e2de0f4d4f249414936c92c4925c91f491cc916490fc9094902c8fc48edc8e748e0c8d648cbc8c148b6c8ac48a1c89b4894c88e4883c87d4872c8684859c8534848c83e4837c82d481ec8184811c80b4800c7f247e7c7e147dac7d447c9c7bf47b4c7a6479fc799478ec7804775c763475cc756474bc73d472ec7204719c7134704c6f646e7c6dd46cec6c046b5c6a7469cc6964687c67d466ec6644659c647463cc6324627c621461ac6104605c5ff45f4c5ea45e3c5dd45d2c5c845bdc5b745b0c5aa459fc5994592c5884581c57b4570c56e4563c55d4552c54c4541c537452cc522451bc50d4506c50044f5c4e744d8c4d244bbc4ad449ec490447dc46f4468c4624457c4514442c43c4429c41f4418c412440bc40143f6c3ec43e1c3d743ccc3c643bfc3b943b2c3ac43a5c39b4390c38a4383c37d4376c3704365c35f4358c34e4347c3414336c32c4325c31f4310c30642f7c2e942e2c2dc42cdc2bf42b8c2ae42a3c2994292c2844279c26f4268c25a424fc2414232c2284221c21b420cc20241fbc1f541e6c1e041d5c1cf41c4c1ba41b3c1ad419ac1904181c1734164c15e4157c13d412ec1204115c10b4104c0f240ebc0e140d2c0c840bdc0b740b0c0a24097c089407ec078406dc063405cc04e403fc035402ec024401dc0134008bffe3ff3bfe93fdebfd83fcdbfc33fb8bfb23fa7bf9d3f96bf903f85bf7b3f70bf6a3f5fbf513f46bf3c3f31bf2b3f20bf163f0fbf093f02befc3ef1bee73edcbec63ebbbead3e9ebe943e81be773e6cbe663e5fbe553e4ebe443e39be273e1cbe163e0bbe013dfabdf43de9bde33ddcbdce3dc3bdbd3db2bda83da1bd9b3d90bd8a3d83bd7d3d72bd683d5dbd533d48bd3e3d33bd2d3d26bd183d09bcff3cf4bcee3ce3bcd93ccebcc43cb9bcaf3ca0bc9a3c93bc853c7abc6c3c5dbc4f3c44bc3a3c2fbc1d3c12bc043bf9bbf33becbbe23bd7bbc93bb6bbb03ba9bb9f3b94bb863b77bb6d3b5ebb543b49bb3f3b34bb223b17bb093b02baf83ae9badb3ad4bac))) else (if i<17 then (if i<16 then 0xc241c006ac2c1c08414560c02090630a2b0601048318581c0061e0c0618409040c183060824183060c18209060c18483060c183040004123060c10306082410306120e18309070c1860008093c40418d4a10601048c525830082418c120c18309070c18601048c525830082418c120c18309070c18204881020a0228301020918081048c04082460204123091410081048c64004001003040000021418184502440c081828414091068401c2820e080002a095018a5826612f0414b04005852c12d00116865825e00296095020805e0c22d00100b41845e0c200219880181002d1001820000040020410208204000018404200408604002021000040001002a1010408200100080002540022a00100040000000000000208104004100010208100304a810402a041000410200100004a800402a00100a80040010000002b1788002f02100b4004002081040837812f0211986f020412f02100bc10400103f16800c1825e08200484b424402f06100a81040010c080178ac020012d00158043020012a0011684bc0045e12a001003f0804200409504082006080b400402a02103043820000bc202f080000000002b178800000000002c31e17008000000004f0802c2000b0402c10380402c1e20013429e10d0c7843431e10478400000a8201d0803c20000001d08034084000b0688000003425412a080000d080000d0813c20000001b0803c20000000000016080000f0950405410068400015040541015053420000000f08001e1000300841e18f0c7863c31e10003c200d080a8200d0c7843c31e10d0c7840831e5420d08795083ca8402a0803c34400f08002c100002c100002c104f0678a84e011d08684036101986dc22c12a09504054105b84cc21e1b708b040000000001043c20000001608001e10150401a100074a8407008e8402c12a08009e3a21d095040000001e10c0878400015040000e8402c12a08684a82182a200050cc400023c34400f2a115043c3441e281c31d08b0a078c13c1e2c300002c100b0a078d3421e2c20d0800000704582000058200f0c7863c31e10f0a78402c10003c29e14d0813c20000004f08002c1000000013c204f0ff178a2bf8bc7145e2f03610446880e2a346041b143038a8d1f804157f10bc3441a6c2f0fe08184168820b44105a2082d104168bc0b52823f8be010a7fc40f06f0fe02043017f078e282e3c607151e30df74ffe0c00301000615030698080030a81834c040018540c1a602140c2a060d301000615030698363e3461b1f1a30d8d8f186c6c78ff83ca87e011fc5440d2d10195168c0ca8b4606545a3032a2d18195168fc0b528abf8be05a9455fc50ffe8f187ff478c3ffa3c61413fde028086f00a0416201cb09280d58610ac24a03561fe068cf80a0018365a3461b2d1a30d564d187c7cb0c3 else 0x4022a370081040820624003030c0018180080c0041a0c0230e0501183008800c3421a0612b01830d580c186022a0430208004002002080503010248e0109082040121040802420090c78489c031e1220f0917801048c54244021e123007848810200908000818a04104045010428141238a041058c800c0064400e021409102010c8c5064432002007e1020a000dc022c0e0037e0802c1c006080020056100040021600200080041850006160027008581000c0029a002960a6800800200108090018400082400400ac28d086800a3420c1000802b0a6c29a0024d0012b04200049a10008e810a0c03a106190218583800c0c004062820b070018b07860c8314503c2462c2812300080063c004e01160010a07800e3c0041e00200a01000c0fc17e0858c8a0c3c0045e9a2000802b0b7829a0024d0012b04342940024d0ad840022c042830008004006002700840a080c504082820800100005051400208001020a0a2800507140027e08200880420818d05041820088681849a0a0834d03050420084202000a1830c086053424200010a9a1a083184d060422686820c1438046120a0230c050118d0308346818612180c30c0808400810f0830d0801c040c12204031a1830d0801f841808283700e7820a0df8201a0610d0b030210202ac082060a783081020c1120910305c0202282060820409e0c20406001858009c031a0027e08020345060a1c0232d010619680830cb4041865a1a0c32d010619686830cb404186160c003090e0018680080020c14a041013c1840c10030418210120c3080b804a824187140c20608307f8341871a0c27008895048312341840f0fe2a0620c05f82fc102001a0f0628a07820c583c30005018c1e122090610b07820906143c00419fc1e0c4060c7830858241871e0c2fe16061c7830853f83c188fc17e08305281040060813400404a061268308182b81040820401010804141818a08501041010314145020810505fc54080c4140410a030a28104b81020115180380850244042a21501061803f083010506e01cf08140420402010a11f8200c150418204081021c10c0968454244121700848400021038210082006041850006011a2700804689f8200d080018287008c080450618120c5a080060c09062d04003060483168200183000241034b418e10022830c09062d040030106800c2050006121c003000d1000438208a620060424202d0870a081820c1060bf04200450602122040d0018704201040090800134402d084842421012283090810a780b0492282442c1e123090810229880121000268805a11408000420682000c1820c10804141840308201851e0c20806141ff07830c3c18506fc10409102048a582438108120818304091012788300824618041230c001000430004120e00309060c18483000) else (if i<18 then 0x40017f02010ff81810088280210044007e1040108201040410802104020860b408108018021020008002041dc0a781094c20014f0417f02010c083fc0c083020ff078736821408204102084063c084fc1fe0f041ff07820c082100420000fc082fe08ad0427f031b01103ed80860010013f04002fc1a003140910185f820200201001048a082450400e0208021418a00830c2450400fc206091380418244fc1060848425f840140601184842421a1228d0913805c020f00a091bf05f82280c00311080041829e0820048425f840c1080609184063c18414120c37e0bf043c28241880c104081342440097e1020410214081238a04107847f0302143ff810612080c308084040c20618003000c106000801c041204183090c06182860801f842802080047008789000df820030c0018782000c013c49e002000800400200fc2060409002018009c02fc1090f0018484002009e2d00800401f840012a08683010ca834300850a0010008402000c20004e012a0013f04013c51a10d00146840020010806001840008a82018008100022a06001bf040029a0028f0a6800a3c200108001268401f8412061000400080040060027008182000c20004049a0832a04001c5000bf8603c109fc1e0830604001840009f820613709b067f0a0783479fc024d81830a0020401180841020a122040110a848814244060a1230108404385041a10d0801fc080437e081041820e122060bf0404244041003045018006060028d0013f040c480065a040c32d020619681030cb40c081885a06040c42d020619681030c240c0061a00202080182006081042020806120c4080820180031228084101030ff02010c0820c100a27800280943024440881812220440c0911022060482011050440861a12101840c0010004008f0c7863c21e0820f04100b42440097e100078a3c25a0028f0878008a80045a1007e100040c2fc102080000308204b4044004080b434400101080002000080150808206100082040020000950008102540027e001000400000000000002080000408204054082015020818200100080a800402a00100a800400100001e1000a810402d00100202450600e02040910204881000412080c314091003f08200c41008204091020410210082700310b578a0c02212083160410200080020814a0a501881029408200005281050608283f016041820410210108031020420209308402085022b41082c295e1240048a081020817008b0a020e3c1051e082fe0f041878208007e0bf04503018005824c2c12083090410306048c53fbc010810022832d0d04188848a0c0c504221142ffe042048a083c104121040818528294062040a502081ae1530a502080400418040c3020c1008009c02020020008005c02041050010280030c0c1800606000c3000800400 else (if i<19 then 0x502031050bc306fc17e0830109c020e0c083060848201831008184fc17e081040400404002000210080080004402002700b805f82e01700bf04100040a002700b8042021017e0820109c02e01020410405f822b1e2150c10104182285e043090010900178ec000306e011408402000c50bc306fc10104102010810084e01122d00183010820104fc170040018201082c080061604003040013805c033608003040013805c02160400304085bf09f8200122050913805c02120a08004009610e81020f78100077808003700b804cc2c24100800c66120835b02041ad97882df84fc12f04190923804645845e2c0c3140910a03080820c1142f02183000a6c08006340c27008c8488006840c14d00021cd82000c00684fc10402107040010404082040e1008208080441c0c2700808408001840200270096b80804004fc17e082048810244001c270096b8081410186080c201001008009f820c102080410c04242fc1060830708381840c1c28f4a06040c287030a3c300071e940c30f0c109250783103c304080c27e0bf063c3841210e0c10304893c10001885a1a205080800810004e017e0828209c02e01058d00182008804202002010013805c02020027e0bf04a821c282020610a0108b5f840800209041028009c02e012a050019504820c04004020027e08080080010402002040210201081008416000437e0bf0424101860a0822a06051a684820ca8241460800204061028008a82418108000822a06041950289f82fc10402100070a3c100871e16000447e0bf04103842c28206043319504820ca810454120830906100060804384001c28f0f0011200070a3c300062814a1411502000c3ca8446fc17e087968838181060c0820e0410200800d3c2049e2567e1008009c02fc10602104810810084e017e082000814004e0109041048289f820804202701020108502fc10001104800850384e01140878a082410006fc104011020108503c386120420008180082c0040018a0bf05880c2001040c50401c040812206040118900881c04400fc2000800400200100080008d02061c680830c242030604109080c1c681030c30241a341000c000412314091048a0a34041860402283060c1028009c02fc10008005f8004001700bf0400200101001000400000040221020978108a80c4001026840061040800400c1046840020060c6840820810208204002041001040081700bf041820c17e0820400c14a0410305c03140827e0828009c02fc10008004002001000800410001860800204000618005c02fc1050010184830c00200100004002b810008004202060c0030808004094002000040021017008180030c2020010083180bf04010103082040020210000400010208184002001000042021017e00100000000007f0401021001c04081220 else 0x82020020100107045420700bf05c02fc17e08c01020dc02fc10200102010818d840200200091008009c02e017e084bf08442020022d7e10302010df820c10207041030425f851e080437e0bf043820004203000c1820009c02fc17e082010810004080420400021bf05f82000c28f00071c780083c1410008fc17e080810a3c100471e000438f00021bf05f8230000430402001c780800c241051e003034d00071a686083c1800612fc27e0f806020c003841c180c34d06106030bc02410008126c200041028209c02fc10e061008009c0202002000213f05f82040c204001010009c02041020800109f82fc1010013f05f82020020008109f820400206082800808144040a2040213f044424106e017e084800b5c1000760080037008a08d804821452c1286229408300110418c2)))))
def g1007l9 : Packing := (2115,3,5,10,1,16,0,g1007d9)
def g1007key8 (i : Nat) : Nat := 0x163003114e00000011f0b56b044005000000169965214400f30000000c54b90311
def g1007d8 (i : Nat) : Nat := (if i<2 then (if i<1 then 0x8555120e6ea227791120bec2858591120ecea225591120f4e9de5591120bae6989191120bea6889191120bdc2858554d209f62a5878cd20e76a22778cd20bf4285858cd20ed6a22558cd20f569de558cd20bd6694848cd20af66a0748cd20bb6698748cd20bd6694748cd20bf2688748cd20bf4684748cd20ee6a22448cd20f669de448cd20fc6956448cd209f668e995c9209be69a9950920bae6987450920bce6947450920be668c7450920bec6847450920bf82858588920f5a9de5588920afa6a07488920bba6987488920bda6947488920bf268c7488920bf86847488920f6a9de4488920fca956448892097eaa997205209beaa99620520d3e9dd9620520cde61d9520520d5e9dd95205209eeaa99420520cee61d9420520d6e9dd9420520d6e65e4420520dae65a4420520dce65644205209f6aa99320520cf661d9320520d769dd9320520de69119320520d7665e3320520db665a3320520dd66563320520de665233205209de696995c5209de2a6555c520e7c61c815c520bdc694815c520bec690815c520bf468c815c5209beaa9961c520cbea21961c520dae65a441c520db665a331c5209faaa9921c520cfaa21921c520dea911921c520df28cd921c520dba65a221c5208fe6a299505208fe2a68850520c7e2627750520cde2625550520cee2624450520cf62623350520cfc26171505209f6aa99310520cf6a219310520d769dd93105209faaa99210520cfaa219210520d7a9dd9210520df28cd9210520df264e2210520cfaa668848520d7aa667748520e7aa227748520ddaa665548520edaa225548520f5a9de5548520bda69484485209fa6a47448520afa6a07448520bba6987448520bda6947448520bf268c7448520bf86847448520deaa664448520eeaa224448520f6a9de4448520fca9564448520df2a663348520ef2a223348520f729de3348520fd29563348520fe29123348520df8a648148520f789dc8148520bf86988148520fe89108148520bf868c8148520ff08cc8148520afa2a14148520bf8aa93148520df8a653148520ef8a213148520f789dd3148520fd89553148520fe89113148520ff060d3148520ff054d3148520ff050d31485209fa2a62284520afc2a14184520ef8a212184520f789dd2184520fe89112184520ff08cd2184520afc6a09784520e7ca2277845209fc2a58584520edca225584520f5c9de5584520bdc6949484520bdc6948484520afc6a07484520bbc6987484520bdc6947484520bf468c7484520bf86887484520eeca224484520f6c9de4484520fcc9564484520ef4a223384520f749de3384520fd49563384520fe49123384520ef8a209284520f789dc9284520fe89109284520bf82a62284520f789de2284520fd89562284520fe89122284520bb86988148520bf068c8148520 else 0x18fe68299611318bf6989891131aaf69898911318bf698985c931cd72615354931f555d5535c531f715c9325c5318df6969961d218f768e9961d218df2a587955218bf69a99611218fe68299611218f72a5878cd21fd154d524c521a3f6989461c21a5f6949461c21a7768c9461c21a7e6809461c21aaf6989761021acf6949761021ae768c9761021aee6809761021c6fa667761021c3f61d961d0218bf6a5861d021c5f61d951d021c9f619951d0218df6a5851d021c9f659851d021caf659841d021ccf655841d021c7761d931d021cb7619931d021cd7615931d021ce7611931d021c7b61d921d021cbb619921d021cdb615921d021ceb611921d021c7d61d911d021cbd619911d021cdd615911d021ced611911d021c7e61d901d021cbe619901d021cde615901d021cee611901d021a6faa98791021e2f9dd8691021e4f9dd85910218f76a47460c21ab76987460c21ad76947460c21af36887460c21af56847460c21af66807460c21e679de4460c218fe6a47460021abe6987460021ade6947460021af668c7460021afa6887460021afc6847460021e6e9de44600218df694989de11a5f694989de118fe6809891211aee68098912118fe680985ca119fcaa99021e119dd694989de11b5d694989de11b5d694929de11b6d690929de11b7c680929de119ddaa99521211d5d9dd95212119f5aa9931d2119f9aa9921d211df8681921d2119fc6809891211bec6809891211bec6808791211f4d9de5591211bec68092912119dd6949850e11bf4680878ce11f559de558ce11bd5694848ce11bb5698748ce11bd5694748ce11bf1688748ce11bf4680748ce11f659de448ce11fc5956448ce119fcaa99020a11d7c9dd9020a11dec9119020a119f568e995ca119fc680985ca11b7c680875ca119f52a6335ca119fcaa9901ca11dec911901ca119bd69a9950a11bcd6948450a11bad6987450a11bcd6947450a11be568c7450a11bec6807450a119ddaa99510a11d5d9dd9510a11d7c9dd9010a11ddc9559010a11bb96989788a11bf86808788a11f599de5588a11bf168c9488a11bd96948488a11bb96987488a11bd96947488a11bf168c7488a11bf86807488a11f699de4488a11fc99564488a11f719de3388a11fd19563388a11fe19123388a11abe69897a2120afa68897a2120afc68497a2120af668c94a2120afa68894a2120afa68891a21209f668e9961d20b5e694989dd20b7668c919dd20b7a688919dd209fc6869961520cfca209161520cfc61c9161520d7c9dc9161520e5ea2277955209be69a99611209deaa99521120d5e9dd9521120afc28585211208feaa9981d120cbea21961d120cdea21951d1209f6aa9931d120cf6a21931d1209faaa9921d120cfaa21921d1209fcaa9911d120cfca21911d120df8689911d120bdc285) else (if i<3 then 0x5855d021cdf649855d021cdf641855d021af7aa97460c21af76897460c21af76817460c21afeaa97460021afe6a57460021afe68974600219f768e995ca119bf69a9950a11baf6987450a11bcf6947450a11be768c7450a11bee6807450a11bfaaa97250920bfaaa97248520dfaa65424852095faa99520a7796faa99420a7797eaa99020a77977aa993206778fb6829960874abb6989160874adb6949160874af368c9160874afa6809160874afaaa99060874cfaa659060874cfa6459060874abd6989260474add6949260474af568c9260474afc6809260474b4f694929de44b6e680929de44b6768c919de449eeaa99020a44d6e9dd9020a44dce9559020a449afaa99620644d2f9dd962064487f69e996154387f2a677615439f3aa9921d233df2681921d2339f5aa9911d233f479de5591233ba76989191233ad768e8895572ccf6558421172ae768e8891172c77262778cd72cd7262558cd72ce7262448cd72cb76588320572ceea6644600728f768e9961d528fe6809891152aee68098911528f72a5878cd52f535cd535c9528bf68196a21428bf69a9961d428f768e9961d42c7e61d9021d42a3f69a889dd428bf69a9961542a9f69a8895542cafa21961d142ccfa21951d142ccf61d951d1429e7aa9931d142ce7a21931d142ce761d931d1429edaa9911d142ceda21911d142ceea21901d142ab769a888cd428f72a5878cd42ba7698748cd42bc7694748cd42be5684748cd42be6680748cd42b7a680875c942bcb694945c942bea680945c942f635cd435c942c5fa667761442e5e9de55600428bf69a99611328f768c989de22a7768c989de228bf6989891222aaf6989891222bab6987450a22bcb6947450a22be368c7450a22be96847450a22bea6807450a229bbaa99621e229bb6819621e229f368c989de22b7368c989de22b7368c919de229f3aa99321222d739dd9321222dd395593212229f3aa9931d2229f9aa9911d222cfa6a1901d2229f368c98552229bb6989891222bab6989891222bab6988791222f4b9de5591222bab6989191222f539de558ce22bb3698748ce22bd3694748ce22bf1684748ce22bf2680748ce22f639de448ce22fc3956448ce22acf6968891171acf2a25591171ad7696888cd71ad72a2558cd71cde21590209718fe6809854971adb6968888971adb2a25588971aafaa98691071ab7aa9868cc71ea761a448cc71c9f6199510871cbe6199010871abbaa98688871eab61a4488871eb361a3388871f595c9525c5518df6969961d418fe6829961d41a7e682889dd418fe6829961541ade68288955418df2a58795541af6682888cd41aee6828850941afa6828888941f4d5d5545c541f695c9425c541c77a667760c41cf660d901c841af3aa98388841e739dd83888418df6969961d318df2a5879553 else (if i<4 then 0xfa57aab9d5b2acb5632b05578ab75592ab5550aa354f2a65528a86540a9cd4dca60524a8ed46ca31516289d432a14507a82940a9ee4f0276d39a9c84dd26b133c9994c5a5f52ba9584a9a53929293b496a4a123490c47aa3791a08b9455a27511e881439a19509c840419209102c8083fd1fb0fbc7d93e59ef4f5e7a13c99e14eee7693ad9d34e7e7313919c54e0e6f93759b74d9e6c13599a94d2e68934219fccf466c32f1940c846343131884c266052fb97a4bb65cd2e416e8b585a72cc9650b1e5812be15dcae456d2b4158cabc5592aa1518a8253c29b94c8a4851f28d1454a2050b28314049f84f727913b49d04da26a931c9844bd25c12a893848e24011c88c845f22d11548a044b223110487843721910b485042320f106482840f20510148003fb1fb0fc47d83e71f10f747b03d31e70f247883bf1dd0ed47603ab1d30e847383971c90e347103831bf0de46e836f1b50d946c035b1ab0d446983471a10cf46703331970ca464831f18d0c5462030b1830c045e62e516b8b245882bf15d0ad45602ab1530a845382971490a3451028313f09e44e826f13509944c025b12b094449824712108f44702331170880436216108883040e2020fe87e03e61ee0f487903be1da0ea87403961c60e086f036e1b20d686a034619e0cc865031e18a0c286002f61760b885b02ce1620ae85602a614e0a4851027e13a09a84c0256126090847022e11208684202060fe07c83d01de0e106e035c1a40cd064030c17c0b905a02bc1540a5050026c12c091046021c10407d03c01cc0dc069032017c0b4055028012c08c04101e00dc040000afbaa99160874afb6819160874cbf6059620572cbf6598420572cf76508320572abf69a885d542abf69a885cd42abf69a8854d429f768e995c942abf69a885c942beb684945c942bbb698915c942df324c915c942abf69a8854942dcf65d5454942ecf61d5454942bcf6815454942dcf6415454942fcb5517254942cf761d9320542cf76059320542df364d7220542cdf21594209719bf69a9950971adf6968850971be768c8450971f4f5d55450971adf696884c9719f768e995c951fd328d7254951f5b5cd72549519bf69a9950951afe682885d541afe682885cd41afe6828854d419f768e995c941afe682885c941fe328d7250941f6b5cd7250941afe682884c941cdf26154549319bf69a9950931afb68a8850931afb2a17250931cbfa21961d121cbf601961d121cdfa21951d121cdf601951d121cf7a21931d121cf7601931d121cfb6a1921d121cfba21921d121cfb601921d121cfe6a1901d121cfea21901d1219f768e995c9219bf69a9950921baf6987450921bcf6947450921be768c7450921bee6807450921fcb5515250921fd9551524c521cbfa65865d021cbf649865d021cbf641865d021cdfa6 else 0xe10104000000414784081010408100082020bf82fe0c3c04207059a1f801840eb876010301044a08000408000003bc1de0408021000060801c011018182000000000000040000000000941030400208000208000208000010400000000008200000000041210484121048400003020c083020c08000000000000200080000000410008200003410024200004081048104fe080020008000100040010004001000020008000100040010004001000400100040010134040418000041000000ff8042010400100040010004001000400100002020800000000000408100040000000000000010200204014085012202040000002100000048104000800010000200080020000412102000283000000484081000020008181820302440908500820484281020400100040810305040c083020c0830200080020008002006041810604181060418100040010604181060400104841210484001060418106040010604181060400100000c083020c082420c08302006041810604181048418100242040800010000810000000000000020000004080000000000000000820010400000020c0800200080020008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001040410104041000000000000000000000000000000000000000160800000000000000000000000000000000000000000000000000000000000000000000000000002c100000000000000000000000000000000000000000003a1610742df01c7023771ad8cfc66a32b1908c5c5f62df1618a9c516281132892445a2110f1871c35617d0b9855c27610d078839c1ba0c105b82b414609904781cc0ae02900f8053ff1feefe07e4bf11f7efba7dabec1f56fa67d0be4df1cf897c23dfdef4f757b83dadebaf4f7a53cf1e6ef327923c7de34f0c783bc09dfaeef7753b95dc0edb76b3b45d98ebe75cbad1d5eeaa752ba5dd12e7b736b97dcb4e557283909c68e2670c384dc1ce0970237fdbf4df56f83789ba8dcf6e53715b80dbb6d6b6a1b34d956c8362dafad786b53595aaed496993491a2cd08681b3d59cecd9665b2f5970caa64e325d912c7b636b17d8a2c4361ab09d832c145fa2fbd7b0bd35e72f01752b9b5c6adfd6e2b635aaad1d672b345932c61626b0e584ac115fea)))
def g1007l8 : Packing := (539,4,5,4,1,13,0,g1007d8)
def g1007d7 (i : Nat) : Nat := 0x82010400000000000000000ab1a0bc6ec96a84678c941e28280cd9b4c49922b92851f32e9935c88150a7e4d9d54b9284904fc9b3aa97248520d2e30ed2902b8a41a6c61da4205714834e8c3b4640ae2904ee2bb6988148520cdc532d310290a41b389dda620521483750d348840a42904fc2bb68c8148520cf8532d190290a41b709dda3205214837c12234640a42906ec1a68cc8148520
def g1007l7 : Packing := (16,5,5,1,1,7,0,g1007d7)
def g1007samples : Array (Bits × Bits) := #[(0x11008410d00b58102581000c10817900800dc0a119a11008410d00b58102581000c10817900800dc0a119a11008410d00b58102581000c10817900800dc0a119a11008410d00b58102581000c10817900800dc0a119a11008410d00b58102581,0x1200411504a580105802024428040000202c00009201200411504a580105802024428040000202c00009201200411504a580105802024428040000202c00009201200411504a580105802024428040000202c00009201200411504a58010580),(0x588ef79009178106b178081e8cf8c309cc910967282588ef79009178106b178081e8cf8c309cc910967282588ef79009178106b178081e8cf8c309cc910967282588ef79009178106b178081e8cf8c309cc910967282588ef79009178106b178,0x1cccf2a2011184c2b070085a801886888c8109872001cccf2a2011184c2b070085a801886888c8109872001cccf2a2011184c2b070085a801886888c8109872001cccf2a2011184c2b070085a801886888c8109872001cccf2a2011184c2b070),(0x20a7034b2450262d484ec111230e860742620e4024420a7034b2450262d484ec111230e860742620e4024420a7034b2450262d484ec111230e860742620e4024420a7034b2450262d484ec111230e860742620e4024420a7034b2450262d484e,0x401309480420022c400f4101014120070004226884c401309480420022c400f4101014120070004226884c401309480420022c400f4101014120070004226884c401309480420022c400f4101014120070004226884c401309480420022c400f),(0xa3291070ec001c80bb9201e2130f04720d32b010204a3291070ec001c80bb9201e2130f04720d32b010204a3291070ec001c80bb9201e2130f04720d32b010204a3291070ec001c80bb9201e2130f04720d32b010204a3291070ec001c80bb92,0xab2c1090e9c015c0ab9010e2ba0e045025320014312ab2c1090e9c015c0ab9010e2ba0e045025320014312ab2c1090e9c015c0ab9010e2ba0e045025320014312ab2c1090e9c015c0ab9010e2ba0e045025320014312ab2c1090e9c015c0ab90),(0x0,0x0),(0xcd484808da90c05a8a9f0e03dc0ff81b918c418cd38cd484808da90c05a8a9f0e03dc0ff81b918c418cd38cd484808da90c05a8a9f0e03dc0ff81b918c418cd38cd484808da90c05a8a9f0e03dc0ff81b918c418cd38cd484808da90c05a8a9f,0xe8408b088d9085988a1b0a831c1f1003a0380384d68e8408b088d9085988a1b0a831c1f1003a0380384d68e8408b088d9085988a1b0a831c1f1003a0380384d68e8408b088d9085988a1b0a831c1f1003a0380384d68e8408b088d9085988a1b),(0xc11028840b2c23388cab70001ff0008026300112151c11028840b2c23388cab70001ff0008026300112151c11028840b2c23388cab70001ff0008026300112151c11028840b2c23388cab70001ff0008026300112151c11028840b2c23388cab,0xe30008144ae423180c8b52001fe40000233a0410154e30008144ae423180c8b52001fe40000233a0410154e30008144ae423180c8b52001fe40000233a0410154e30008144ae423180c8b52001fe40000233a0410154e30008144ae423180c8b),(0x800c1c83024cb24377e08003e000001c07c08605220800c1c83024cb24377e08003e000001c07c08605220800c1c83024cb24377e08003e000001c07c08605220800c1c83024cb24377e08003e000001c07c08605220800c1c83024cb24377e0,0xc1483024c304335e08000e000001807c08401200000c1483024c304335e08000e000001807c08401200000c1483024c304335e08000e000001807c08401200000c1483024c304335e08000e000001807c08401200000c1483024c304335e0),(0xe50542f00a918ae5474fffc000000e03800f819c410e50542f00a918ae5474fffc000000e03800f819c410e50542f00a918ae5474fffc000000e03800f819c410e50542f00a918ae5474fffc000000e03800f819c410e50542f00a918ae5474,0x4914423100b08275064a500000020880801f84b00104914423100b08275064a500000020880801f84b00104914423100b08275064a500000020880801f84b00104914423100b08275064a500000020880801f84b00104914423100b08275064)]
def g1007columns : IndexTree ColumnInfo := (.fork 15 (.fork 7 (.fork 3 (.leaf [(385,32,78,0,4),(417,0,78,0,4),(396,0,99,0,4)]) (.fork 2 (.leaf [(384,0,623,512,7),(104,256,647,512,4)]) (.leaf [(360,0,647,512,4),(324,8,163,0,4)]))) (.fork 4 (.fork 2 (.leaf [(332,0,163,0,4),(328,0,679,512,6)]) (.leaf [(259,64,172,0,4),(320,0,687,512,8)])) (.fork 2 (.leaf [(257,0,238,0,7),(37,128,330,0,4)]) (.leaf [(161,0,334,0,7),(142,0,353,0,4)])))) (.fork 8 (.fork 4 (.fork 2 (.leaf [(140,0,355,0,7),(128,0,879,512,11)]) (.leaf [(96,0,911,512,7),(74,0,933,512,5)])) (.fork 2 (.leaf [(72,0,935,512,8),(69,2,424,0,4)]) (.leaf [(71,0,424,0,4),(67,0,428,0,7)]))) (.fork 4 (.fork 2 (.leaf [(64,0,943,512,10),(40,0,967,512,7)]) (.leaf [(35,0,460,0,5),(15,0,480,0,4)])) (.fork 2 (.leaf [(9,0,486,0,8),(8,0,999,512,10)]) (.leaf [(5,0,490,0,7),(1,0,494,0,11)])))))
def g1007autos : Array (List Nat) := #[[]]
def g1007levels : Nat → Packing
  | 7 => g1007l7
  | 8 => g1007l8
  | 9 => g1007l9
  | 10 => g1007l10
  | 11 => g1007l11
  | 12 => g1007l12
  | _ => emptyPacking
def g1007index : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 1058 3333 6 17 12 1 (g1007key10)
  | 11 => lookupWord 251 753 5 14 9 1 (g1007key11)
  | 12 => lookupWord 17 53 3 10 5 1 (g1007key12)
  | 7 => fun _ => none
  | 8 => lookupWord 9 28 2 9 4 1 (g1007key8)
  | 9 => lookupWord 270 811 6 15 10 1 (g1007key9)
  | _ => fun _ => none
def g1007 : Forest := ⟨1007,12,fun j => g1007samples[j]?.getD (0,0),g1007columns,g1007autos,g1007levels,g1007index⟩
set_option maxHeartbeats 0 in
theorem geom1007 : graphValid g1007 (boundsBefore known863) = true := by
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
theorem s1007_11_0 : block g1007 11 0 7=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_11_7 : block g1007 11 7 25=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl1007_11 : block g1007 11 0 32 = true := (@block_merge g1007 11 0 7 25 s1007_11_0 s1007_11_7)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_10_0 : block g1007 10 0 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_10_36 : block g1007 10 36 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_10_40 : block g1007 10 40 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_10_76 : block g1007 10 76 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_10_112 : block g1007 10 112 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_10_148 : block g1007 10 148 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_10_184 : block g1007 10 184 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_10_220 : block g1007 10 220 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_10_256 : block g1007 10 256 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_10_292 : block g1007 10 292 6=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_10_298 : block g1007 10 298 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_10_334 : block g1007 10 334 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_10_370 : block g1007 10 370 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_10_406 : block g1007 10 406 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_10_442 : block g1007 10 442 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_10_478 : block g1007 10 478 22=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl1007_10 : block g1007 10 0 500 = true := (@block_merge g1007 10 0 478 22 (@block_merge g1007 10 0 442 36 (@block_merge g1007 10 0 406 36 (@block_merge g1007 10 0 370 36 (@block_merge g1007 10 0 334 36 (@block_merge g1007 10 0 298 36 (@block_merge g1007 10 0 292 6 (@block_merge g1007 10 0 256 36 (@block_merge g1007 10 0 220 36 (@block_merge g1007 10 0 184 36 (@block_merge g1007 10 0 148 36 (@block_merge g1007 10 0 112 36 (@block_merge g1007 10 0 76 36 (@block_merge g1007 10 0 40 36 (@block_merge g1007 10 0 36 4 s1007_10_0 s1007_10_36) s1007_10_40) s1007_10_76) s1007_10_112) s1007_10_148) s1007_10_184) s1007_10_220) s1007_10_256) s1007_10_292) s1007_10_298) s1007_10_334) s1007_10_370) s1007_10_406) s1007_10_442) s1007_10_478)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_0 : block g1007 9 0 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_36 : block g1007 9 36 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_72 : block g1007 9 72 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_108 : block g1007 9 108 28=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_136 : block g1007 9 136 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_172 : block g1007 9 172 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_208 : block g1007 9 208 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_244 : block g1007 9 244 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_280 : block g1007 9 280 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_316 : block g1007 9 316 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_352 : block g1007 9 352 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_388 : block g1007 9 388 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_424 : block g1007 9 424 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_460 : block g1007 9 460 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_496 : block g1007 9 496 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_532 : block g1007 9 532 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_568 : block g1007 9 568 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_604 : block g1007 9 604 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_640 : block g1007 9 640 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_676 : block g1007 9 676 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_712 : block g1007 9 712 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_748 : block g1007 9 748 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_784 : block g1007 9 784 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_820 : block g1007 9 820 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_856 : block g1007 9 856 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_892 : block g1007 9 892 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_928 : block g1007 9 928 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_964 : block g1007 9 964 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_1000 : block g1007 9 1000 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_1036 : block g1007 9 1036 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_1072 : block g1007 9 1072 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_1108 : block g1007 9 1108 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_1144 : block g1007 9 1144 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_1180 : block g1007 9 1180 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_1216 : block g1007 9 1216 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_1252 : block g1007 9 1252 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_1288 : block g1007 9 1288 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_1324 : block g1007 9 1324 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_1360 : block g1007 9 1360 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_1396 : block g1007 9 1396 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_1432 : block g1007 9 1432 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_1468 : block g1007 9 1468 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_1504 : block g1007 9 1504 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_1540 : block g1007 9 1540 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_1576 : block g1007 9 1576 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_1612 : block g1007 9 1612 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_1648 : block g1007 9 1648 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_1684 : block g1007 9 1684 25=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_1709 : block g1007 9 1709 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_1745 : block g1007 9 1745 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_1781 : block g1007 9 1781 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_1817 : block g1007 9 1817 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_1853 : block g1007 9 1853 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_1889 : block g1007 9 1889 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_1925 : block g1007 9 1925 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_1961 : block g1007 9 1961 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_1997 : block g1007 9 1997 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_2033 : block g1007 9 2033 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_2069 : block g1007 9 2069 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_9_2105 : block g1007 9 2105 10=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl1007_9 : block g1007 9 0 2115 = true := (@block_merge g1007 9 0 2105 10 (@block_merge g1007 9 0 2069 36 (@block_merge g1007 9 0 2033 36 (@block_merge g1007 9 0 1997 36 (@block_merge g1007 9 0 1961 36 (@block_merge g1007 9 0 1925 36 (@block_merge g1007 9 0 1889 36 (@block_merge g1007 9 0 1853 36 (@block_merge g1007 9 0 1817 36 (@block_merge g1007 9 0 1781 36 (@block_merge g1007 9 0 1745 36 (@block_merge g1007 9 0 1709 36 (@block_merge g1007 9 0 1684 25 (@block_merge g1007 9 0 1648 36 (@block_merge g1007 9 0 1612 36 (@block_merge g1007 9 0 1576 36 (@block_merge g1007 9 0 1540 36 (@block_merge g1007 9 0 1504 36 (@block_merge g1007 9 0 1468 36 (@block_merge g1007 9 0 1432 36 (@block_merge g1007 9 0 1396 36 (@block_merge g1007 9 0 1360 36 (@block_merge g1007 9 0 1324 36 (@block_merge g1007 9 0 1288 36 (@block_merge g1007 9 0 1252 36 (@block_merge g1007 9 0 1216 36 (@block_merge g1007 9 0 1180 36 (@block_merge g1007 9 0 1144 36 (@block_merge g1007 9 0 1108 36 (@block_merge g1007 9 0 1072 36 (@block_merge g1007 9 0 1036 36 (@block_merge g1007 9 0 1000 36 (@block_merge g1007 9 0 964 36 (@block_merge g1007 9 0 928 36 (@block_merge g1007 9 0 892 36 (@block_merge g1007 9 0 856 36 (@block_merge g1007 9 0 820 36 (@block_merge g1007 9 0 784 36 (@block_merge g1007 9 0 748 36 (@block_merge g1007 9 0 712 36 (@block_merge g1007 9 0 676 36 (@block_merge g1007 9 0 640 36 (@block_merge g1007 9 0 604 36 (@block_merge g1007 9 0 568 36 (@block_merge g1007 9 0 532 36 (@block_merge g1007 9 0 496 36 (@block_merge g1007 9 0 460 36 (@block_merge g1007 9 0 424 36 (@block_merge g1007 9 0 388 36 (@block_merge g1007 9 0 352 36 (@block_merge g1007 9 0 316 36 (@block_merge g1007 9 0 280 36 (@block_merge g1007 9 0 244 36 (@block_merge g1007 9 0 208 36 (@block_merge g1007 9 0 172 36 (@block_merge g1007 9 0 136 36 (@block_merge g1007 9 0 108 28 (@block_merge g1007 9 0 72 36 (@block_merge g1007 9 0 36 36 s1007_9_0 s1007_9_36) s1007_9_72) s1007_9_108) s1007_9_136) s1007_9_172) s1007_9_208) s1007_9_244) s1007_9_280) s1007_9_316) s1007_9_352) s1007_9_388) s1007_9_424) s1007_9_460) s1007_9_496) s1007_9_532) s1007_9_568) s1007_9_604) s1007_9_640) s1007_9_676) s1007_9_712) s1007_9_748) s1007_9_784) s1007_9_820) s1007_9_856) s1007_9_892) s1007_9_928) s1007_9_964) s1007_9_1000) s1007_9_1036) s1007_9_1072) s1007_9_1108) s1007_9_1144) s1007_9_1180) s1007_9_1216) s1007_9_1252) s1007_9_1288) s1007_9_1324) s1007_9_1360) s1007_9_1396) s1007_9_1432) s1007_9_1468) s1007_9_1504) s1007_9_1540) s1007_9_1576) s1007_9_1612) s1007_9_1648) s1007_9_1684) s1007_9_1709) s1007_9_1745) s1007_9_1781) s1007_9_1817) s1007_9_1853) s1007_9_1889) s1007_9_1925) s1007_9_1961) s1007_9_1997) s1007_9_2033) s1007_9_2069) s1007_9_2105)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_8_0 : block g1007 8 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_8_2 : block g1007 8 2 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_8_38 : block g1007 8 38 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_8_74 : block g1007 8 74 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_8_110 : block g1007 8 110 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_8_146 : block g1007 8 146 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_8_182 : block g1007 8 182 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_8_218 : block g1007 8 218 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_8_254 : block g1007 8 254 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_8_290 : block g1007 8 290 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_8_326 : block g1007 8 326 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_8_362 : block g1007 8 362 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_8_398 : block g1007 8 398 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_8_434 : block g1007 8 434 21=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_8_455 : block g1007 8 455 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_8_491 : block g1007 8 491 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_8_527 : block g1007 8 527 12=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl1007_8 : block g1007 8 0 539 = true := (@block_merge g1007 8 0 527 12 (@block_merge g1007 8 0 491 36 (@block_merge g1007 8 0 455 36 (@block_merge g1007 8 0 434 21 (@block_merge g1007 8 0 398 36 (@block_merge g1007 8 0 362 36 (@block_merge g1007 8 0 326 36 (@block_merge g1007 8 0 290 36 (@block_merge g1007 8 0 254 36 (@block_merge g1007 8 0 218 36 (@block_merge g1007 8 0 182 36 (@block_merge g1007 8 0 146 36 (@block_merge g1007 8 0 110 36 (@block_merge g1007 8 0 74 36 (@block_merge g1007 8 0 38 36 (@block_merge g1007 8 0 2 36 s1007_8_0 s1007_8_2) s1007_8_38) s1007_8_74) s1007_8_110) s1007_8_146) s1007_8_182) s1007_8_218) s1007_8_254) s1007_8_290) s1007_8_326) s1007_8_362) s1007_8_398) s1007_8_434) s1007_8_455) s1007_8_491) s1007_8_527)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_7_0 : block g1007 7 0 12=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s1007_7_12 : block g1007 7 12 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl1007_7 : block g1007 7 0 16 = true := (@block_merge g1007 7 0 12 4 s1007_7_0 s1007_7_12)
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
  · exact bl1007_7
  · exact bl1007_8
  · exact bl1007_9
  · exact bl1007_10
  · exact bl1007_11
  · exact bl1007_12
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1007 : Lower (vars 1007) (graphGoal 1007) 13 :=
  lower_forest (g:=g1007) (i:=0) (hints:=13438558465) (before_sound known863 valid863) geom1007 tables1007 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps1007 : List (Nat × List Nat) := [(1007,[]),(895,[32,83,116])]
def known1007 := extendKnown known863 13 maps1007
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1007 : Known known1007 := extendKnown_ok valid863 low1007 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem apartLower : Lower (vars 1023) (graphGoal 1023) 14 :=
  lift_ok (ms:=fixRows 16 0) (xs:=[(inputs.getD 4 zero,1,17)]) (by decide +kernel)
    (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low1007
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem seedSlice : Slice inputs graph (~~~seed) 14 :=
  slice_correct (ms:=[(zero,seed,5)]) (base:=vars 1023) (G:=graphGoal 1023) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide +kernel)) apartLower

theorem completedRoots (deadCase : Impossible graph 14 inputs.toFinset) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 2)) →
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

end PEqualNP.Outside.L_meta_2946

open PEqualNP.Outside.L_meta_2946 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_2946 : ∀ (x1 : Fin (9 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (0 : ℕ) < x2.size → x2.size ≤ (13 : ℕ) → ∃ (x6 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)), !x6 x1]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro i C legal _ small
  by_contra none
  push_neg at none
  have whole := completedRoots (dead_start (before_sound known383 valid383) geomdead tablesdead)
    ⟨⟨GateOp.and,[0,2]⟩::⟨GateOp.not,[i.val]⟩::C.gates,C.output⟩
  have start (y : Fin 9 → Bool) :
      ([⟨GateOp.and,[0,2]⟩,⟨GateOp.not,[i.val]⟩] : List Gate).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun a => w.getD a false)]) (List.ofFn y) =
      List.ofFn y ++ [y 0 && y 2,!y i] := by
    fin_cases i <;> simp [List.ofFn_succ,GateOp.eval] <;> rfl
  have value (y : Fin 9 → Bool) :
      (⟨⟨GateOp.and,[0,2]⟩::⟨GateOp.not,[i.val]⟩::C.gates,C.output⟩ : Circuit).wires (List.ofFn y) =
      C.wires (List.ofFn y ++ [y 0 && y 2,!y i]) := by
    rw [←start y]
    rfl
  have bound := whole ?_ ?_ ?_
  · change 16 ≤ C.gates.length+1+1 at bound
    change C.gates.length ≤ 13 at small
    omega
  · intro g hg
    simp only [List.mem_cons] at hg
    rcases hg with rfl | rfl | hg
    · simp
    · simp
    · exact legal g hg
  · intro y
    rw [value]
    obtain ⟨l,hl⟩ : ∃ l, C.wires (List.ofFn y ++ [y 0 && y 2,!y i]) =
        (List.ofFn y ++ [y 0 && y 2,!y i]) ++ l := by
      have grow : ∀ (gs : List Gate) (w : List Bool), ∃ l,
          gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun a => w.getD a false)]) w = w ++ l := by
        intro gs
        induction gs with
        | nil => exact fun w => ⟨[],by simp⟩
        | cons g gs ih =>
          intro w
          obtain ⟨l,hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun a => w.getD a false)])
          exact ⟨g.op.eval (g.inputs.map fun a => w.getD a false)::l,by
            rw [List.foldl_cons,hl,List.append_assoc]; rfl⟩
      exact grow C.gates _
    rw [hl]
    simp [List.ofFn_succ]
  · funext y
    have hv := none y
    change (Circuit.wires _ (List.ofFn y)).getD C.output false = edge y
    rw [value]
    exact hv
