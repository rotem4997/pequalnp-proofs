import PEqualNP.Defs

-- The live-wire verifier and the certificates for proper induced graphs are from
-- L-meta-1667 and L-meta-3350. The new search starts from the disjunction
-- of vertices zero and four followed by the negation of any available wire.
namespace PEqualNP.Outside.L_meta_2750
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
def seed : Sig := 0x88888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888

def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
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
def deadsamples : Array (Bits × Bits) := #[(0xf854605d026923a5a16008862c9d18d42fd85e54d221898f1e440284a107a02910c3e03c06c40d2642ca74f54627022c11e389d9b43b30c961ca72386ce81500aa210d1ba1a121108a6c99348979d054ac200727ac054c0970110780155ad581,0x6844620d0040231585204884208800c4270824141201090814040082a10700282003e02402c4084602ca04a440240a1091218919100a2084314a220840a00480aa210819a02120100a4409048968c05484200702a805440920100380144a9480),(0x80b20c31f72bfc4e1481d27000d43c9c5bd438a9c5e0286040f054f111d001ce10920229bde170b8d339029e2bcac4cd494fb74d1052452141a61c5b9ca1e642f40c600258428f0e5c00df481e03202a204cd465e10fe01206e82c7b03150603,0x80100c30e6089040109182600012282018c41889c5e0204002b0604000c009861080028b1c2120a0d12000120908c00d005a724402504200402010501c01c208540860025840090e1400964816012008204cd0254102a00206a0247b01150201),(0x12ce100c308544478a85796a2341d206e4242e31335abb35943abb40be28c8e05c4c115123137950052a02a9ba0d31c096458c656cc338623e92230683d8962194d5145c2aa62229438824d8e06246d0cd124850733918c390189888a426380a,0x10ca0000108540870900790a0240900460282200221a991490081a0028289000cc41010021184410080a0a28a20020c0200184206c0128621092200a03d8103080d5145c02a2022143880090804206d04d100840322918c190088800a4221002),(0x8628ebbd17000228c83c0291b729e17b3643984a392a815889878936d04e41b82b8e28807cc302855ead3105d9868885c748c2b0724ae81086518e259124cd4278a18b4aa01db88524c3a3435a0814469349110c18f0c24c2a8052bd88818268,0xc2206a1d05000020401c0090e509051303449848110100480001811490070429238c000818c508010485900541c68805c240409012420000024186258024450270208b02a00da0842041a3414a08100690490104085040042a8052bc00818028),(0xbc8ccda8781e4d8151cd3cf93a4a0a01509a42078c1bc4a783ea4aec6c7bbbd02ef85be130b1750bcd872a062d01842a34826040203d5b99ac8899721d47b82106b4f88001d04ee6f42e103eb14e0a090b95e84905a08ef7a2230402e2b14bc5,0x148981a0109a5c8210c1a4690a42220050930202c418c4a7837a48680e50b9d00c601bc02020f518c9002a002c1124282402304220255b598c9019921c51b8010494708001d04e62d42a103a30060a090b94e84905a08af280230402e2304b45),(0xd3b19712becef4647857054f8773c68492608a46265cd6cd0106c449284294958830b40e8328a4102841c46a63b66493288c7290c714876750b08cb0eb0a532e014ce7e24f9c08720240400006971f885be46b00080a21145aa7f52cf42a8012,0x92218c003e8654007015040a0c73c50280c0084821449285810a8400004080918c301008002824100801c000230200c0688c40804110046300b00cb28307502a0004c5624f9c086200004000021315805bc46800000a00145205f42ce0200002),(0x3145d24845746a93b60987114c89950ee90ab5809889781e716b0d141d9e036fea797f20c896480c8b565809c5575a81eabcad03980701be24b7e8d7401960b32336416db2f0c4c050f169960250e8b311988b92828b0074bd455ad232c2112c,0x2307720c00346283a400011d4c09950fa108a4001a095004514a0014181e2261ab3d3060c0d6480a2ac41009e4571880ea848181d90321bc24d38a860208103323340169a2b084c040f169960050c8b211800b9082890074b8455a803282012c),(0x49615339cc24bb41a658244591d020101222d0f578b5376254a121290a30cd5c4e2ad1d6dabfa9e032f022500c91031b32331a7a9ace0ca4e96243014a4009cd0d2a3210b66014de852533c420acc80ff443ad9cc5d0f4808cd621151170ac54,0x4900539a4030aa408668006591882010120251355ca1242200a1212102144d6e020a42d6d2878b6832b420400cb9813312321a4a924e408ce04943054c0001c10d2a2200b040149c8425334420acc80fa003859cc5d0e4000cd201111150ac54),(0x2108654280dbc21c532263cad6a2ab60a053058994f658a43b3dd89384745a04932387065124c385d01899e2cc083e3c1e3327061d61ca921a4965c8583262f4485320b5c04953298d1f02098424a39520b6148b236021a80528c3236c545ab4,0xc0001428049001c03a04a4012802a200013019184320c200a34088304a0580410028702010083a440180cc2080827381411260a0400ca0098085048489022c408432094004053098d0e0008842422012032140b21202188052801030c545a90)]
def deadcolumns : IndexTree ColumnInfo := (.fork 63 (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(1,0,510,0,12),(0,1,460,50,8),(2,0,509,0,12)]) (.leaf [(0,2,440,69,8),(3,0,508,0,9),(2,1,460,48,7),(4,0,507,0,12)])) (.fork 4 (.leaf [(0,4,369,138,8),(5,0,506,0,8),(6,0,505,0,9),(4,2,440,65,7)]) (.leaf [(2,4,369,136,7),(7,0,504,0,7),(5,2,440,64,6),(8,0,503,0,12)]))) (.fork 8 (.fork 4 (.leaf [(0,8,227,276,8),(9,0,486,0,8),(10,0,501,0,8),(12,0,499,0,9)]) (.leaf [(8,4,369,130,7),(4,8,227,272,7),(14,0,497,0,7),(10,4,369,128,6)])) (.fork 4 (.leaf [(15,0,480,0,4),(16,0,495,0,13),(0,16,486,9,10),(17,0,494,0,11)]) (.leaf [(16,1,460,34,7),(19,0,492,0,8),(16,4,353,138,7),(21,0,490,0,7)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(21,2,424,64,5),(24,0,487,0,11),(8,16,486,1,9),(25,0,486,0,8)]) (.leaf [(9,16,486,0,8),(27,0,484,0,5),(11,16,484,0,5),(24,4,353,130,6)])) (.fork 4 (.leaf [(29,0,482,0,5),(26,4,353,128,5),(32,0,479,0,12),(0,32,94,385,8)]) (.leaf [(32,1,460,18,7),(1,32,94,384,7),(35,0,476,0,7),(34,1,460,16,6)]))) (.fork 8 (.fork 4 (.leaf [(36,0,347,0,8),(39,0,344,0,4),(40,0,471,0,8),(49,0,462,0,8)]) (.leaf [(48,1,460,2,6),(50,1,460,0,5),(56,0,455,0,7),(64,0,447,0,13)])) (.fork 4 (.leaf [(0,64,189,258,10),(66,0,445,0,11),(2,64,189,256,9),(67,0,444,0,8)]) (.leaf [(66,1,396,48,6),(70,0,441,0,8),(69,2,440,0,5),(74,0,437,0,7)]))))) (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(74,4,305,128,5),(80,0,431,0,11),(83,0,428,0,7)]) (.leaf [(96,0,415,0,9),(96,1,396,18,6),(98,1,396,16,5),(128,0,383,0,13)])) (.fork 4 (.leaf [(128,1,332,50,7),(3,128,344,36,6),(132,0,379,0,11),(4,128,347,32,9)]) (.leaf [(133,0,378,0,7),(134,0,377,0,8),(132,2,312,65,6),(133,2,312,64,5)]))) (.fork 8 (.fork 4 (.leaf [(136,0,375,0,9),(128,8,99,276,7),(140,0,371,0,8),(132,8,99,272,6)]) (.leaf [(138,4,369,0,5),(144,0,367,0,11),(152,4,353,2,5),(160,0,351,0,11)])) (.fork 4 (.leaf [(160,1,332,18,6),(162,1,332,16,5),(164,0,347,0,8),(36,128,347,0,8)]) (.leaf [(172,0,339,0,5),(176,1,332,2,5),(180,0,331,0,5),(192,0,319,0,11)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(198,0,313,0,7),(256,0,255,0,12),(258,0,189,0,8),(260,0,251,0,8)]) (.leaf [(264,0,247,0,9),(256,8,227,20,7),(8,256,151,96,7),(268,0,243,0,7)])) (.fork 4 (.leaf [(260,8,227,16,6),(273,0,238,0,7),(280,0,231,0,8),(276,8,227,0,5)]) (.leaf [(288,0,223,0,9),(256,32,94,129,7),(32,256,151,72,7),(257,32,94,128,6)]))) (.fork 8 (.fork 4 (.leaf [(296,0,215,0,7),(40,256,151,64,6),(304,0,207,0,6),(288,16,198,9,6)]) (.leaf [(273,32,78,128,5),(56,256,135,64,5),(320,0,191,0,11),(256,64,189,2,9)])) (.fork 4 (.leaf [(322,0,189,0,8),(258,64,189,0,8),(324,0,187,0,7),(324,8,163,16,5)]) (.leaf [(321,32,30,128,5),(388,8,99,16,5),(168,256,23,64,5),(224,256,23,8,5)]))))))

def words13 (i : Nat) : Nat := 0x3415b043011005bea9416da411a641dbea94300a35c59010500008682b67a71640b88d183010c078bb6104689b690322344e2c81711a206820008602180d7e530e8340a8b360d203018f22e88212739815cd654a91c438e52f093214771a45b03800fff4ca81ffe66503ffc88a07ff8cd40fff11281ffe11503ffc00a05ffa6540f7f33281fbe44502ffc88a07f78cd40ff711281ff611503ff400a05ff801407ff002817be44502ff400a01ff80140
def lvl13 : Packing := (20,2,7,0,0,10,0,words13)
def idx14 (i : Nat) : Nat := 0xc178000000603520d03dc0e209122000285700e808e0180000005448204001832c00c4100000000000000c0be2e000709b400f013608908c158026065023d8900b00030434269410002124408d44b13c034d056123420501a9060080600006000100
def words12 (i : Nat) : Nat := (if i < 1 then 0x485c206c7b21d9c73a1bbc6c21a2c66818ec5dc166c54614144d812ac45610a43f20e4c3660c6c2ee0adc27608841cc060413603ac096012c000fffa2222503ffd8688940fff61622503ffc8588940fff59622503ffd8388940fff58e22503ffd5388940fff60622503ffc8188940fff54622503ffc5188940fff4c622503ffe8884540fff61e11503ffd8584540fff21611503ffd7584540fff95611503ffd8384540fff5ce11503ffd5384540fff60a11503ffc8284540fff5ca11503ffd5284540fff14a11503ffd3284540fff88a11503efd8799940fbf61666503efd7599940fbf60e66503efd7399940fbf54e66503efd8299940fbf5ca66503efd5299940fbf14a66503efd3299940fbf60666503efd7199940fbf54666503efd3199940fbf48666503fdd768cd40ff760a33503fdc828cd40ff758a33503fdd818cd40ff720633503fdd718cd40ff754633503fdc518cd40ff748633503fdc218cd40dff662225037fd9688940fbf99a225037fd9588940fef55222503fde3388940ffb60a22503fed6288940ffb54a22503fed3288940dff64622503fbd4188940ffb48622503ff93088940ffb2a222503fee8888940ffb61e22503fed8688940ffb5da22503feca588940ffb61622503fec8588940ffb5d622503fed6588940ffb60e22503fed7388940ffb58e22503fed5388940ffb28622503fed8188940ffb20622503fed7188940ffb54622503fec5188940ffb4c6225037fd9884540effa22115037fd9784540f7f9de115037fd9584540fef552115037fd9384540ff78ce115037fd9284540ffb88a11503ff58184540ffd5c611503ff55184540ffd4c611503ff52184540ffe4c211503ff4a884540ffda2211503ff58784540ffd61a11503ff57684540ffd29611503ff58584540ffd21611503ff57584540ffd59611503ff65584540ffd60e11503ff57384540ffd58e11503ff55384540ffd28a11503ff58284540ffd20a11503ff57284540ffd58a11503ff55284540ffd14a11503ff53284540ffd88a115036fd9899940dbf65e66503cfe7799940dbf65666503ebd5499940dbf64e665036fd9299940dbf64666503ebd4199940fbe4c2665037dd968cd40fb799a335037dd928cd40df764633503f9d418cd40dfb64a225037ed9888940efba22225037ed9788940f7b9de225037ed9688940fbb99a225037ed9588940feb55222503fce3388940dfb64622503fad4188940ffa4c2225037f59184540fed506115037f59884540efda22115037f59784540f7d9de115037f59684540fbd99a115037f59584540fdd95611503fb55484540dfd64e11503fd63384540dfd64a11503fe62284540ffc4c2115037f98280140dfe4ca005037f98180140dfe546005037f93180140dfe486005037da3380140dfa88a005037f21180140 else (if i < 2 then 0xb7ea986a8ea1a0254e4145beaf8648cd0c8378a996402b882bb7c32a193275521104f6fabf54a52112334320de2a44900ae20b6dfaa61ab2202482413dbeafd529483e0f232874402bb9029082db7ea9a39c886809904ed4b1c6fb902095df525a963986714413bbec730cea882577da972120104aefb52c73902096dfaa6c84892015c413bbe2089a9639c8a0b1a7d0c3ba92d4b1cc3570e2e3480e5f410461cbba208dd51053218eeefb52c73915c634780882755f44c8b413ab8d0ddf639c80e4412bbec730c8d570eaa6471dda9722b84831a33bea4b52c338b5c2418d21df6a5c80e520104cefb915c2418d15c810443bbbed4b1ce45718d1e827d1c8c689413918d0ddf639d50e4412bbeacb52c730ce2d718d2282721321bbeead7090634577da963ab8c69c832528720c8d78a209e891c8094a506bd3203751a5644145e8eab915c6406ee3474c90e41ab6bd11a7552310535b2657a3ab5c2428d1d2941922ad91abd119f1520105494a1d7a23420b9091c808bd3c5c804122017a78a900825adaf4f1522482b8468eafb6c94a0c813babb84686d9f4f16206e31a32be94a05db39011995f4a506f15b808cc8078adc046457d294390207bb6484c84692872042ca42fa5908d1f207d2c8c688afa05db6408d0b26757b6c80c8c68aafb6c872042ca34bba4764282a6d9f4c82c86e31a32beea89287205db26490d908d2859757b64cac84851a3f6c905918d110e5d05946923b21413a43642828d13b648920b211a2f8b900823403c548041207294a1c833e9e2a349188291dfc577f20ae31a3252830eee2e408d2b220a1c575720722b8c68de2e403b88247d3c5c8041221c830ee99234eaa4620a320756b8c688993ab5c2428d1529418774891a467c5480414f8a905718d112943877469c848c413e40e45718d111af1523105202e5387604ba2910d1912d7f29c090ecd9488690bb6538760c8168b0d2e880b75fc3b0655538868fafe538321da2a710d1f5fca70e521388695e3ebf94e0d8121da2e6d0d235fca70ec0b365221a3ebf94e1d8368a9c4347ca1f232c777192c4cf0cac186fe4be16f44bbbeeb8b966df0b646d3cb3eeca6b0f6bd4ad5eaeeaa3ea58a83699aa58e8f0a26e846a03e7ec9eae7569c566de9aee65c98e65f89706576952651293964b891b64368f863828d7e30a8afe292891e21a86ee14883f609481260087f1df727cc5ef079f5e3277c5d9275bdd2e73b5cca7275c7a70bdbf86f2db766cfdaf46a7da5e68ed9e6670d98264dd914637586060557c05dad6f85ab5626576d55454254d2521d45050653e24e5d37e4cf52e84b152a249fd23447f51da468d158445d0c2420504a40c4fe63ee4f963d7cf0a3b9ceb039bce1036ecd703444cc63174c082f6cba42d64b042b0ca822904a1426d496a24f48fc231 else 0x2a96a68260869c831a7d2c848f35483f47504fa63564201fa0982edb203ab1ab2100fd1d410d2fa590991d3707d827d320111b6c6ac84d52d483f41305db0d234635642aa96a41f051f46e1206db1ab2156fbbe1a83e0a504c176c54a418d590c5dea96a5b6c831a3d2c807d354d1c34bbf642826b7ddf46bb6c8032b201f45bf4710c6c2825b7ea96a4157d041482c807d354b534330d0178b90634efc82a37c47869d5723208095390534330d011d5903ab8d4828a18e2a09d54c84435be6ad1d434058d4822ba2df77e8661a02c81d54ca1c111554b530d50cc378a9040434482ab7ddf148ce11e1a755c8809c54824165beef86b0d50cc3404eaa4120aaa96a60237f2002dc8c6a414bbe4103c6f03e5b7ea9a3a02c69c8904f6fbbeac9b0e2e4005c04e406520ac8207ccb4c8442dbeefd52d4c34490170139090482b77da963a0207f1a722414292d4b1cc33047a1bb8d218e609c83d31a2d6ceae3436a582721203d31a33bea4b52c3304901bb8d21df609c8ad920c68cc7304ea9e98d16b67231a1bbeacb52c730cc138b5b6349ad9c84c86efb04ead6c9063466a58e3d1c8104aefa92d4b1cc338a209ddf639c81048efb52e42402095df639d5104810d1ceee34477da9085c86e220c68e10be8e46343415df4dc21609d5881b6c690bbbbed4842c1390db4418d24211a1411a92d4842c33e91038b8d21df6a5c86e0218831a3c1c10baaa091df6a421721b88831a3c1c10b90a09067aa529a0815485f446ac84abe20b6d54a520aa34bba46a0d90bb7ea9a3a826db1ab20f6fabe195040af6c8d26491d90ab7e82ed9324851ab20f6fd535c2418d59066a58e609f43231a33be9bb52c7304db1918d21df639b82a4c8c68cefb52dc240646346b7d36aa529070650291a48d41b2176fd5206a42a0a35641ddf6a58e6e0c8c68d6fd5341241db24434a356424c8c69f41b52c730564634fa19a9638496e0c8c68d433e98d0c49a1b1a77488d190990ddf165a9639b8b231a3c0c433aafa264512686c69d523be2ca6ec73056436d8d21a96e2c84831a2bbed4b7024a4064634777d376a582b21206db1a43be2cb71642418d1902321411aeeefb52c7304db5918d228677d411b52c73e8249918d19df165a9639b8b231a3d0ceaa8236a5f4b2120c68a33d5294a330c50c8378aefe402b882caa68e809dfb231a904f6fabe94a0ce2e40ac8828))
def lvl12 : Packing := (184,3,7,0,0,14,0,words12)
def idx13 (i : Nat) : Nat := 0xb0aa301bb0490000c045201e00003056000000570000260d0000908d00000000615b206b0000000000371073f079507100003058814bf01d0000a070205d40826048100af0a9000000a1e969b0286066e186409b703a600f405cb184000070a540863024e08020394106109200008369f05a109870a3000061295072e0220000c06ed06a000060adb0b3000090323009910700004050e0a70000b00740afa006509c6097000030b20000000080900000104101040000a047708f70850000000081550000e02e0000f02a902640ac000080b183a600009043b002706d71158142e11cd095c0385027c044702f30783053603f909f8029209d1088a004c113b096000041018034012a4013c02c0000505f504d808e0000e09e40193036205211210000000030a4802d01874181b15970310000503da04b305e4127f180c17a900b906ca1037099e1701126a0b0708c4076a068d012701770ae30811089507a803e5128f07e907420634030300ce0a6d0773018309ad06990037008ea493051900050757065807d608b4094c0156011000000000000000060592067701f73444656000050213185f03b30330000306240b5a025200d0000910cc0b740abb0542046104ef03c0000407c204fe0b40000303581aa3016107b908a2010000000a0e04a004cf00e50879064a0a2507f802b505530a8f100a549401c506100006042e06f6091e0144060d0935084e020801a6040a001e05b0000d023e0b60000000000007083c00534000202090c3e23041b0e1a0205170308432d86101e0507010a152a16000023030604300000001b2f15520b030802041d06000602040b000417090200
def words11 (i : Nat) : Nat := (if i < 10 then (if i < 5 then (if i < 2 then (if i < 1 then 0x662115023fe5d32f08a811ff2e99284540e7ed10c8c22a075f67764611503beb19b2308a81df98899184540afeb72c0c22a057f5b95c611502bfadcaa308a81ded6614184540f76d10a0c22a07db67750611502fdadaa8308a81fe58cd4184540ef6b24a0c22a07fa62250611502bfadca6308a815fd6e52184540ff628298422a07fd1314c211502bfadc95108a815fdaed9884540afe974cc422a073f598a2211502bfb5db2f08a815fd2e99784540e7ed10cbc22a057f5b961e11503afacc4ef08a81e7da227784540ebeceecb422a076f59899a11503d7b444cd08a81dbd65e6684540f9ecef33422a057f5b929611502f7adb14b08a817ed6d0a584540afed76cac22a057f4ba656115039fb4432b08a81d7d9dd9584540edeccccac22a057f5b961611502bfadc90b08a8177d6dc8584540bdeb6c42c22a05fb5b421611502fead990b08a817f96c88584540bfe36042c22a057f5b95d611503bbacb4ab08a81f9d99a5584540eeeb2b2ac22a05fb6bb55211502fda5d2a908a81ded6615484540f76d10aa422a077b59755211503edb3baa908a81fad9995484540fe6caaaa422a057f6bb64e11502bfa5d32708a81cfda219384540ebeceec9c22a076f66664e11503bbb2ab2708a815fd6e58384540afeb72b9c22a075f5975ce11502bfadcaa708a81fcd5515384540efab3119c22a07bd6888ce11503beacbc6708a81f759de3384540efab2d19c22a07ed6668ce11503beacac6708a81fd59563384540ff2aa919c22a057f5b928a11502bfb5db2508a815fd2e99284540e7ed10c9422a075f67764a11503b7b3332508a81ddd9559284540ef6aa8c9422a077d63364a11502bfadcb0508a815fd6e48284540afeb72b9422a057f5b954a11502bfadc8a508a817bd6d85284540bf6b6829422a057f5b94ca11503bf2cc44508a81ef9a222284540efcb2f11422a07de67788a11503bf2cb44508a81fb999a2284540efcb2b11422a07f665588a11503fd2aa44508a81df964e2284540ff8c6711422a077e59288a11502ff95da6108a81dfc6613084540f7e51098422a07df2774c211503f793326108a81fdc9553084540ff62a898422a07fd1534c211503bf8c926108a81ff88893084540aff576c1400a057fabb4ca00502bfcdc26500281dfa6093280140aff576c0c00a077da33606005039fcc130300281dfa8898180140aff576a8c00a077da3354600503bf8c0aa3002815feaed3180140aff37098c00a073fa884c600502bfcdaa6300281df64c93180140efd44498c00a077f1814c600502bfd5da43002815fe6e12180140e7f51090c00a057f9b548600502bfcd9a4300281df68cd2180140efe26290c00a077f18384600503bf8c142300281dfc54a1180140efe26508c00a073ea8888a00503be919c2300281df888a1180140 else 0x81dfe6d53180140eff36498c00a077f9824c600503bfca926300281dfe6e12180140eff36a90c00a077f98548600503bfcd9a4300281dfe60d2180140eff2a690c00a056febb66266502b7f5db2f332815bf6e58799940adfd76caccca056fdb961666502b7edcaeb332817afaed5499940ed7b30aa4cca076bd9755266502b7f5db2733281d3f9dd9399940adfb72b9ccca074fd975ce66503f1eaa2a7332815bfaed9299940e9fceec94cca076bd5464a66502b7edcb05332815bf6e57299940adfb72a94cca056fdb914a66502f5eda0a5332815bf6e53299940e9fceec8ccca04efcba60666502b7edcb03332815bf6e57199940adfb72a8ccca076bd9850666503e5f3ba83332817af6d54199940ed7b24a0ccca056fdb94c666503f5aa0a63332815bf6e52199940bdf576984cca076f9984c266503e7d3ba6133281fae5513099940fdb2a6984cca076f9924c266503f5ca0a6133281fb64c53099940edbb2f33466a07cde7799a33503aef3bb2519a81db7999928cd40ebbceec8c66a076de6664633502eeedb90319a81f679dd418cd40fd3ccca0c66a05bddb808633502eeedb84319a817b76d8218cd40bebb6a10c66a05fd9b0086335023fe5d33111281dbb9999288940ef5aa8c9444a077ce3364a22502bf6dcb05112815fb6e56288940afdb72a9444a077ad9250622502bf6dca4311281dfa6493088940afdb7254444a05dedb72a222502bf75db31112815fb2e99888940e7db3144444a075ed989de22502bf75db2d112815fb2e99688940e7dd10cb444a075ee7765a22502bf6dcb0d11281dbb6626688940f5dd1133444a076ed9799a22503e773bccd112815fb6e4a588940bf5b6852c44a057eebb65622502bf65d32b11281d7b9dd9588940eddccccac44a057edb961622502bf6dc90b1128177b6dc8588940bddb6c42c44a05fadb421622502fe6d990b112817f96c48588940bfd36042c44a057edb959622502fd75daa911281deb6615488940fb5ceeaa444a07eae6655222503b76cb2c711281fcb5515388940ef9b3119c44a07bce888ce22503be6cbc6711281f739de3388940ef9b2d19c44a07ece668ce22503be6cac6711281fe35523388940afdb7250c44a05fadb428622502bf75db23112815fb2e99188940e7dd10c8c44a075ee7764622503b773332311281df38cd9188940afdb72c0c44a057edb920622502ef6db903112817eb6d08188940afdb72a8c44a057edb914622502fd6da0a3112817ebaed4188940ef5b30a0c44a07bae8850622503ed73ba8311281deb6594188940fd5ccca0c44a05fadb550622503fc719a8311281fe95053188940bfd57698444a077e9984c222503df54426111281f7a9dd3088940fdd4cc98444a07fa9544c222503fe4a9a6111281fea5053088940ff926298444a047fcba) else (if i < 3 then 0x6c1422a07fd63360a11503bfac930508a817fd6d48284540efeb2a41422a07f765520a11503fdaaa10508a817fd6cc8284540efeb2641422a07fd63320a11503bfacc2e508a81efda217284540fdecccb9422a07df5735ca11503feb19ae508a817fdaed6284540bfeb70b1422a077f59858a11503dfb442c508a817fd6dd6284540efeb2eb1422a07df67758a11503f7abb2c508a81dfd6556284540fdeacab1422a07f765558a11503fdaaa2c508a81dfd64d6284540fdeac6b1422a07fd63358a11503bfac92c508a81ff96096284540bfed76a9422a05ff4ba54a11503bfadcaa508a817fd6e15284540efeb30a9422a07bf68854a11502ffadbaa508a81f7d2dd5284540fbeceea9422a05ff5b654a11503bfacb2a508a81fbd9995284540fee94aa9422a077f59554a11503fbabaaa508a81fdd9555284540ff6aa8a9422a077f59354a11503fbaa9aa508a81ff58cd5284540efeb24a9422a07fe58254a11502ffadc0a508a81dfd6605284540f7ed1029422a05ff5b614a11503bfacb0a508a81fbd9985284540bfeb6629422a077f59314a11503feb198a508a817fdaed3284540bfe97499422a077f5b94ca11502ffadc26508a81dfd6613284540f7ed1099422a05ff5b74ca11503bfacba6508a81f7d9dd3284540bfeb6c99422a077f5964ca11503f7b3326508a817fd6d53284540efeb2a99422a07f76554ca11503fdaaa26508a81ff55cd3284540efeb2499422a07fe5824ca11503ff25d44508a81ff92e22284540ffc95111422a07fe68888a11503ff2c3c4508a81ff961a2284540ffcaed11422a07fe4b588a11503ff252c4508a81ff96162284540ffc90b11422a07fe57588a11503ff2b2c4508a81ff99562284540ffcb0711422a07fe57388a11503ff2b1c4508a81ff954e2284540bfe97511422a077f59888a11503dfb4444508a81dfd65a2284540fdeccd11422a077f59588a11503fbb2ac4508a81fed5522284540efeb2711422a07fd63388a11503ff2c144508a81ff958a2284540ffcaa511422a07fe53288a11503ff8dc26108a81ffc2a13084540ffe51098422a07ff1b74c211503ff8c3a6108a81ffc6d93084540ffe30c98422a07ff1764c211503ff8daa6108a81ffc2953084540ffe30a98422a07ff0854c211503ff8baa6108a81ffc5953084540ffe4aa98422a07ff1b24c211503ff85126108a81ffc6093084540ffe10498422a07ff1724c211503ff8b126108a81ffc5493084540ffe0a498422a07ff2224c211503bfd5db0500281dfe6cd8280140eff362c1400a077f9b84ca00503bfcdaa6500281dfe6c53280140eff36ac0c00a077f9b360600503bfcd930300281dfe5498180140eff264c0c00a077f9b354600503bfcd92a300281dfe6095180140eff264a8c00a077fabb4c600503bfcdc263002 else (if i < 4 then 0x1503dfac3b0b08a81f7d9dd8584540fdecccc2c22a077f59561611502ffad990b08a817fd6c88584540bfeb70bac22a077f5985d611503dfb442eb08a81f7d61d7584540efeb2cbac22a07ef6665d611502ffb5dacb08a817fd6e16584540efeb30b2c22a07bf68859611502ffadbacb08a81dfd65d6584540fbeceeb2c22a07ef58659611503f7abb2cb08a81dfd6556584540feeb0ab2c22a07f74ba95611503fbabb4ab08a81fdd2ca5584540bfe9752ac22a077f59895611503dfb444ab08a81dfd65a5584540fdeccd2ac22a07f758595611503fbab2cab08a81fed2a15484540ff6d10aa422a07fb58755211503fdac32a908a81fed5d95484540ff6b0aaa422a07fb56555211503bfa5432708a81dfda219384540efeb0ec9c22a077f58664e11503bfabb32708a81dfd2959384540efeb0ac9c22a077f48564e11503bfabab2708a81dfd5959384540efecaac9c22a05ff6bb60e11502ffa5d30708a81dfd6e58384540efeb30c1c22a07bf68860e11503bfacbb0708a81f7d9dd8384540fdecccc1c22a077f59560e11503fdaaa30708a817fdaed7384540bfe974b9c22a05ff5b85ce11503bfacc2e708a81efda217384540fbeb0eb9c22a077f5965ce11503f7b332e708a81dfd6557384540ff6aa8b9c22a05ff6bb58e11502ffadc2c708a81dfd6616384540f7ed10b1c22a05ff5b758e11503bfacbac708a81f7d9dd6384540fdeb0cb1c22a077f59558e11503fbb2aac708a81fed5516384540ffab06b1c22a05ff6bb54e11502ffa5d2a708a81dfd6e55384540bfeb70a9c22a077f59854e11503dfb442a708a817fd6dd5384540efeb2ea9c22a07df67754e11502ffadb2a708a81dfd6595384540fdeccca9c22a077f59554e11503fbac2aa708a81fdd9555384540ff6aa8a9c22a07fd58354e11503feab9aa708a81ff52a23384540ffad1119c22a07fd5878ce11503feac346708a81ff55da3384540ffa94b19c22a07fd5858ce11503fea42c6708a81ff55d63384540ffaacb19c22a07fd6558ce11502ffadc14508a81dfd660a284540f7ed1051422a05ff5b528a11503bfaca94508a81fdd954a284540ff6aa851422a05ff5b328a11503bfac994508a81ff58cca284540efe974c9422a077f4b864a11503bfa5432508a81dfda219284540efeb0ec9422a077f58664a11503bfabb32508a81dfd2d59284540efe94ac9422a077f58564a11503bfa42b2508a81dfd5d59284540efeacac9422a077f65564a11503bfac1b2508a81dfd5cd9284540efeac6c9422a077f55364a11502ffb5db0508a817fd2e98284540efeb72c1422a07bf4a860a11503bfacc30508a81efda218284540efeb2ec1422a07bf58760a11503efb3bb0508a81fbd9998284540efeb2ac1422a07f765560a11503fdaaa30508a81dfd64d8284540f7eb else 0xb64a2284540efed10c8c22a077f58764611503bfac2b2308a81dfd2159184540efeaeac8c22a077f65564611503bfac1b2308a81dfd5cd9184540efeaa6c8c22a077f58264611503bfa4132308a81dfd5499184540efe8a4c8c22a077f53264611503bfb1132308a81dfd6e58184540efeb30c0c22a07bf68860611503bfacbb0308a81f7d9dd8184540efeb2ac0c22a07fb55460611503bfac9b0308a81ff58cd8184540efeb24c0c22a07bf58260611503ff31130308a817fd6e17184540efeb30b8c22a07bf6885c611503efac3ae308a81dfd6557184540ff6aa8b8c22a077f5935c611503feb19ae308a81dfd6497184540ffcc44b8c22a077f5b954611502ffadc2a308a81dfd6615184540f7ed10a8c22a05ff5b754611503bfacbaa308a81f7d9dd5184540efeb2aa8c22a07f765554611503fdada2a308a81fed5515184540efeb26a8c22a07fd63354611503bfac92a308a81fdd5495184540ffcc44a8c22a07fb68850611503fdac3a8308a81fed6154184540ff690aa0c22a07fb57550611503fdb2aa8308a81fed60d4184540ff6ae6a0c22a07fb55350611503fdac128308a81fed2094184540ff6ae4a0c22a07fb55250611503fda2928308a81fed4c94184540ff6c44a0c22a077f5b94c611502ffadc26308a81dfd6613184540f7ed1098c22a05ff5b74c611503bfacba6308a81f7d9dd3184540bfeb6a98c22a077f5954c611503fdaaa26308a81dfd6493184540ffaa6498c22a07fe6224c611503bfadca4308a817fd6e12184540efeb3090c22a07bf68848611502ffadba4308a81dfd65d2184540fbecee90c22a05ff5b548611503bfacaa4308a81fed5512184540bfeb6690c22a077f59348611503feb19a4308a81dfd6492184540ffcc4490c22a05ffabb4c211503bfccc26108a81efea213084540fbf4ee98422a07fb9544c211503feca9a6108a81dfe6493084540ffd44498422a07ff1b14c211503ff8c0a6108a81ffc5c53084540ffe2a298422a07ff1214c211502ffadb95108a817fd6d4a884540bfeb6654422a05ff5b22a211503bfa5d33108a81dfd2d59884540efe964cc422a07bf4baa2211503dfa5ad1108a81efd2ca8884540bfe97544422a077f4ba65e11503bfa5c32f08a81dfd2a19784540efed10cbc22a05ff6bb61e11502ffa5d30f08a81dfd6618784540f7ed10c3c22a07df4a89de11503efb444ef08a81dfd65d8684540fbeceec3422a05ff5b85da11503bfacc2ed08a81efda217684540fbeb0ebb422a07ef58799a11502ffadc14b08a81dfd660a584540f7ed1052c22a05ff5b329611502ffad914b08a81dfd2a19584540efed10cac22a077f58765611503bfac332b08a81dfd5d99584540bfed76c2c22a05ff4ba61611503bfadcb0b08a81dfd6618584540f7ed10c2c22a077f5976161))) else (if i < 7 then (if i < 6 then 0xc44a05feebb54622502ff65d2a311281dfb6e55188940bfdb70a8c44a077ed9854622503df7442a3112817fb6dd5188940fbdceea8c44a077ed9654622503f77332a311281fdb2955188940efdb2aa8c44a07f6d6554622503fd6da2a311281feb5515188940ff9c66a8c44a077ed9154622503ff2c0aa311281ff95c55188940bfdb7028c44a077ed9814622503df7440a3112817fb6cc5188940ff9c6628c44a07faca850622503fd74428311281feb61d4188940ff5b0ca0c44a07fad7650622503fd652a8311281feb6154188940ff590aa0c44a07fad7550622503fd6b2a8311281feb60d4188940ff5ae6a0c44a07fad6350622503fd6a9a8311281feb6054188940ff5ae2a0c44a07fad5150622502ff75da63112817fb2e93188940efdb7298c44a05fedb84c622503bf6cc26311281efba213188940bfdb6e98c44a077ed974c622503ef73ba6311281dfb6593188940fddccc98c44a05fedb54c622503bf6caa6311281feb5513188940ff9ac698c44a07fe4a14c622503bf6c8a6311281ff96053188940ff5a8298c44a07fe9b84c222503ff45426111281ffaa213088940ffd36e98444a07fe9874c222503ff4db26111281ffa6193088940ffd2ec98444a07fe9b54c222503ff452a6111281ffa6153088940ffd10a98444a07fe9754c222503ff4b2a6111281ffa6c53088940ffd14298444a07fe9814c222503ff440a6111281ffa5c53088940ffd2a298444a07fe8514c222502bff5db3108a81aff2ea88845409ff97544422a073fd98a2211502bff5db2f08a819ff2e99784540e7fd10cbc22a04ffcba61e11502bfedcb0f08a81d7f6627784540f3fd113bc22a057febb656115039ff4432b08a81d7f9dd95845409ff974c2c22a057fdb961611502bfedc90b08a8177f6dc8584540bdfb6c42c22a05fbdb421611502feed990b08a817fb6c88584540bfeb6242c22a05ff9b021611502bfedcaeb08a813ff2ea5584540bf7d76aa422a077bd9855211503ddf442a908a81def65d5484540fb7ceeaa422a057febb64e11503aff3bb2708a815ff6e583845409ff974b9c22a057fdb95ce11503afecbae708a813ff2e95384540affb72a9c22a07f3d5454e11503beecc46708a81ef7a223384540efbb2f19c22a07dde778ce11503beecac6708a81fe75523384540affd76c9422a073fe8864a11503aff3bb2508a81def5519284540efbc66c9422a04ffcba60a11502bfedcb0508a815ff6e48284540bfeb6241422a057fdb95ca115027fe5d2a508a815ff6e55284540affb7229422a05efdb614a11502fdeda0a508a817fd6c452845409ff97499422a057fdb94ca115037f65d44508a81dfb6622284540f7dd1111422a077ed9788a11503ef73bc4508a81dfb6562284540ff5aa911422a07fce3388a115027fe5d44508a81df else 0xbf6cc14b11281efba20a588940bfdb6c52c44a077ed9629622503f773314b112817fb6cca588940bfdb6252c44a077eca865622503bf74432b11281dfb61d9588940efdaeccac44a05feebb61622502ff65d30b11281dfb6e58588940efdb30c2c44a07bee8861622503df6c3b0b11281f7b9dd8588940efdb2cc2c44a07eee6661622503bf6cab0b112817fb6cc8588940bfdb6242c44a05fedb85d622503bf6cc2eb11281f7b61d7588940efdb2cbac44a07eee665d622502ff75dacb112817fb2e96588940bfdb70b2c44a077ed9859622502ff6dbacb11281f7b9dd6588940fddaecb2c44a077ed9559622503fb6c2acb11281feb2a15488940ff5d10aa444a07fad8755222503fd6c32a911281feb5d95488940ff5b0aaa444a07fad6555222502ff75db07112817fb2e98388940efdb72c1c44a07beca860e22503bf6cc30711281efba218388940efdb2ec1c44a07dee7760e22503bf6cb30711281fbb9998388940efdb2ac1c44a07fad5460e22502ff75dae7112817fb6e17388940efdb30b9c44a07ded875ce22503bf6cb2e711281fbb9997388940efdb2ab9c44a07fad545ce22502ff75dac7112817fb2e96388940efdb30b1c44a07bee8858e22502ff6dbac711281dfb65d6388940fbdceeb1c44a077ed9558e22503fd6aa2c711281ff360d6388940bfdd76a9c44a05fecba54e22503bf6dcaa7112817fb6e15388940efdb30a9c44a05fedb754e22503ef73baa7112817fb6d95388940efdb2ca9c44a07eee6654e22503fb652aa711281dfb6555388940fedb0aa9c44a07fad5454e22503fe6c1aa711281ff35cd5388940ff995119c44a07fce888ce22503fe6c3c6711281ff35da3388940ff994b19c44a07fcd858ce22503fe642c6711281ff35d63388940ff9acb19c44a05fedb828622503bf6cc14311281efba20a188940bfdb6a50c44a077ed9528622503fd6aa143112817fb6cca188940ff9c6650c44a077eca864622503bf74432311281dfb61d9188940efdb0cc8c44a077ed7664622503bf652b2311281dfb6159188940efd90ac8c44a077ed7564622503bf6b2b2311281dfb60d9188940efdae6c8c44a077ed6364622503bf6a9b23112817fbaed8188940bfd974c0c44a077edb960622503df65430311281dfb6618188940f7dd10c0c44a077ed9760622503ef73bb0311281fbb2d98188940fddcccc0c44a077ed9560622503fd6aa30311281ff38cd8188940efdb22c0c44a05fedb720622503bf6cb90311281f7b9dc8188940bfdb6a40c44a077ed9520622503fd6aa103112817fb6cc8188940ff9c6640c44a05feebb5c622502ff6dc2e311281dfb6617188940f7dd10b8c44a07ded875c622503bf6cb2e311281f7b5d97188940fddcccb8c44a077ed955c622503fd6aa2e311281ff38cd7188940efdb22b8) else (if i < 8 then 0x9688940affb72c3444a076fd9899a22502bff5db2b11281dbf99995889409ff974c2c44a057fdb961622502bfedc90b1128177f6dc8588940bdfb6c42c44a05fbdb421622502feed990b112817fb6c88588940bfeb6242c44a05ff9b0216225027fe5d2cb112815ff6e56588940bf7d76aa444a077bd9855222503f5f332a9112813ff2e96388940edfb2cb1c44a04ffcba54e22503f9eaa2a711281df76623388940efbb2d19c44a07ede668ce22503beecac6711281fe75523388940efdd10c9444a077ed8564a22503bf642b2511281dfb5959288940efdb06c9444a077ed6364a22503bf6a9b2511281dfb6e58288940efdb30c1444a07bee8860a22503bf6cb30511281fbb9998288940efdb2ac1444a07fad5460a22503df6c1b0511281ff38cd8288940bfdb70b1444a077ed9858a22503bf6caac511281fbb5956288940ff5aa8b1444a07eed6358a22503fe719ac511281dfb6e55288940bfdb70a9444a077ed9854a22502ff6db2a511281dfb6595288940fddccca9444a077ed9554a22503fd6aa2a511281fdb54d5288940ff9c66a9444a077edb94ca22502ff6dc26511281dfb6613288940bfdb6c99444a077ed964ca22503f7733265112817fb6d53288940efdb2a99444a07fad544ca22502bff5db2311281dbf9999188940efbc66c8c44a077ed8264622503bf6b132311281dfb5499188940efda64c8c44a04ffcba60622502bfedcb0311281dfb6498188940f7db04c0c44a057fdb920622502efedb903112817ef6d08188940bfdb6440c44a077ed92206225027fe5d2a3112815ff6e55188940efdb24a8c44a07f6d5254622502bfedc8a3112817ef6d05188940bfdb6428c44a077ed9214622502fdf5da8311281def6614188940ef7b2ca0c44a07ebe6650622502fdedaa8311281fe78cd4188940ff5b04a0c44a07fad6250622503fd6a928311281feb4c941889409ff97498c44a077ed924c622503fe69926311281fed5053188940efdb7290c44a05fedb848622503bf6cc24311281dfb6592188940fddccc90c44a05fedb548622503bf6caa4311281feb5512188940bfdb6690c44a07fce3348622503bf6c8a4311281feb5052188940ffca6290c44a05ffabb4c222503bfccc26111281fbe9993088940ff72a898444a07fd9534c222503ff4d926111281ffa6093088940ffd2c498444a07fe9524c222503fdca0a6111281ff64c53088940ffd24298444a05fedb52a222502ff6d9951112817fb6c4a888940efd974cc444a077ecb566222503bf658b3111281efb2ea8888940bfd97544444a077ee8865e22502ff75db0f11281dfb6618788940f7dd10c3c44a07dee889de22503bf6c3b2d11281f7b9dd8688940bfdb70bb444a077ed985da22503df7442ed11281f7b61d7688940fddb0f33444a05fedb829622503 else (if i < 9 then 0x7ebdb454666503f5eaa2a333281dbf64d5199940edfb24a8ccca07e7d5254666503f7ac0aa333281fbd5c55199940fd7b0ea0ccca07ebd8550666503f5ebaa8333281faf60d4199940fd7ae6a0ccca07ebd5350666503f5ec128333281faf5c94199940fd7aa4a0ccca07ebc5250666503f5e99283332817bfaed3199940edfb7298ccca05efdb84c666503b7ecc263332817bf6dd3199940edfb2e98ccca07cfe774c666502f7edaa6333281dbf6553199940fd7aa898ccca076fd924c666503f6e9926333281fbd6053199940bdfd7690ccca076fdb948666502f7edc24333281dbf6612199940bdfb6e90ccca076fd9748666503e7f3ba43332817bf6d52199940edfb2a90ccca07ebd5448666502f7ed9a4333281dbf64d2199940edfb2490ccca07ef57148666503f7a98a4333281fbe6e13099940fdf36e984cca07ef9874c266503f7cdaa6133281fbe6153099940fdf2ea984cca07ef9b24c266503f7cc126133281fbe5c93099940fdf2a4984cca07ef8524c266503f7cd8a6133281fbe6053099940fdf2e2984cca07ef9514c266503f7c90a6133281df75d9928cd40bfbd76c1466a077ddb960a33503beecb30519a81fb7999828cd40efbb24c1466a05fddb120a33502fef5dac519a81df7661628cd40efbb2eb1466a07dde7758a33503f6ebb2c519a81df7649628cd40ff9b04b1466a077dd8764633503beebb32319a81df7609918cd40efb904c8c66a077dd6264633502fef5db0319a81df76e5818cd40efbb30c0c66a077dd9760633503eef3bb0319a81fb72d9818cd40fdbcccc0c66a077dd9560633503beec930319a81ef7609818cd40efbb22c0c66a05fddb720633503beecb90319a81f779dc818cd40bfbb6a40c66a077dd9520633502feed910319a81df7648818cd40bfbd76b8c66a05fddb85c633503beecc2e319a81f7761d718cd40efbb2cb8c66a07ddd765c633503f6f332e319a81df7655718cd40efbb24b8c66a077dd915c633502fef5daa319a81df76e5518cd40efbb2ca8c66a07ede6654633503fceda2a319a81df7649518cd40efbb22a8c66a07fd58154633503feab8aa319a817f76c8518cd40efbb2428c66a07f9d8750633503fcebb28319a81fe7595418cd40ff3b04a0c66a07f9c8250633503fceb128319a81fe7549418cd40ff38a4a0c66a07f9d8150633503fceb8a8319a81fe7545418cd40bfbd7690c66a077ddb948633502feedc24319a81df7661218cd40efbb2e90c66a07dde7748633503beecb24319a81fb7999218cd40bfbb6a90c66a077dd9548633503fceaa24319a81df7649218cd40ff9ac490c66a077dd9148633503feab8a4319a81fe7505218cd40bfbb7010c66a077dd9808633502feeda84319a81df7654218cd40ff3aa810c66a057febb662225027fe5d511112815ffaed else 0x990508a81dff64c8284540effb30b9422a07dfd735ca11502fff5daa508a817ff6e15284540effb30a9422a05ffdb754a11503efe5baa508a81dff6555284540fefaeaa9422a07fbd5454a11503bfec9aa508a81fdf54d5284540ffdb04a9422a05ffdb814a11502ffed98a508a817ffaed3284540bffb7099422a077fd984ca11502ffedba6508a81dff65d3284540bffb6a99422a077fd954ca11503fdeaa26508a81ff75cd3284540ffdb0499422a077fd9888a11503bfecac4508a81fef5522284540effb2711422a07ffa884c211503ffcc3a6108a81ffe6153084540fff30498422a07ff8824c211503ffcb926108a81ffe5493084540fff44498422a076fcb566266503b7e59331332817bfaed8799940edfb0ecaccca05efebb61666503b7edcb0b33281dbf65d8599940f5fb0ec2ccca076fd9561666503f5ec3aa933281faf6155499940bdfd76c1ccca076fdb960e66503b7ecbb0733281dbf6558399940fd7aa8c1ccca05efebb5ce66502f7edc2e733281dbf6617399940f9fb0eb9ccca076fd955ce66503f5eaa2e7332817bfaed5399940edfb72a9ccca05efdb854e66503b7ecc2a733281dbf65d5399940edfb2aa9ccca07e7d8554e66503f5eaa2a733281fb760d5399940fdbae6a9ccca076fd8764a66503b7e5ab2533281dbf6159299940edfaeac94cca076fd8364a66503b7eb9b2533281dbf54d9299940bdfd76c14cca076fdb960a66503b7ecbb0533281ebf61d8299940f9fceec14cca076fd9560a66503f5eaa30533281ebf60d8299940edfb24c14cca076fd985ca66503e7eb9ae5332817bfaed5299940edfb72a94cca05efdb854a66503b7ecc2a5332817bf6dd5299940f9f96ea94cca076fd9554a66503f5eaa2a533281dbf64d5299940fcfaa6a94cca076fd9254a66503f76c12a5332817bf6e05299940edfb30294cca05efdb314a66503b7ec98a5332817bf6c45299940bdfd76994cca076fdb94ca66502f7edc26533281dbf6613299940bdfb6e994cca076fd974ca66503e7f3ba65332817bf6d53299940edfb2a994cca07ebd544ca66503f6eb9a6533281dbf6493299940fddb04994cca076fd8764666503b7ec2b2333281dbf5d59199940edfb06c8ccca076fd7364666503b7ea9b2333281dbf6099199940edfaa4c8ccca076fc5264666503b7e99323332817bfaed8199940ddf974c0ccca076fdb960666503b7ecbb0333281f3f9dd8199940edfb2ac0ccca07ebd5460666503b7ec9b0333281dbf6498199940f5fb04c0ccca05efebb5c666502f7edc2e333281dbf6617199940f9fb0eb8ccca076fd955c666503f5eaa2e333281dbf64d7199940edfb24b8ccca05efebb54666503b7edcaa3332817bf6e15199940edfb30a8ccca05efdb754666503b7ecbaa333281f3f9dd5199940edfb2aa8ccca)))) else (if i < 15 then (if i < 12 then (if i < 11 then 0xd108b6089b08800865084a082f081407f907bd07810745071f06e30691066b062405dd05960570052904e204900449042303dc03b60385033e02f702bb027f0238021201c00179013200eb00a400520000eff96acc444a077fcb166222502fff5db0b11281dff6e58588940effb30c2c44a077fd9661622503bfecab0b112817ff6cc8588940bffd76b2c44a05ffdb859622503bfecc2cb11281dff6556588940fefb0ab2c44a07fbd8655222503fdec2aa911281fef5955488940bffd76c1c44a077fd9860e22503bfecb30711281dff6558388940ff7aa8c1c44a05ffebb58e225037fe5d2c711281dff6616388940effb2ab1c44a07fbd5458e22503feec1ac7112817ffaed5388940bffb70a9c44a077fd9854e22502ffedb2a711281dff6595388940effb2aa9c44a07f7d8554e22503fdeaa2a711281ff760d5388940effd10c8c44a077fd8664622503bfec2b2311281dff2159188940effacac8c44a077fd8364622503bfeb1b2311281dff54d9188940effb30c0c44a077fd9560622503fdeaa303112817ff6d48188940effb2a40c44a07fbd5420622502ffed990311281dff6615188940effb2ca8c44a077fd9554622503fbeb2aa311281fef5515188940bffb7028c44a077fd9814622502ffed98a311281fefa214188940ff7b0ca0c44a07fbd8550622503fde42a8311281fef5954188940ff7b06a0c44a07fbd6350622503fdea9a8311281dff6613188940effb2c98c44a077fd954c622503fdeaa26311281ff758d3188940fff30c98444a07ff9854c222503ffcb2a6111281ffe6053088940fff2a298444a07ff8514c222503bfe5933108a81dff2e19784540effd10cbc22a05ffebb61e115037fe5d30f08a81dff6618784540effd10cac22a077fd8765611502fff5db0b08a81dff6e58584540effb30c2c22a077fd9761611503dfec3b0b08a81dff6558584540bffb6642c22a05ffdb221611502ffedc2eb08a81f7f61d7584540ff7d10aa422a07fbd8755211503fdec2aa908a81dffa219384540effb0ec9c22a077fd8564e11502fff5db0708a81dff6e58384540effb30c1c22a077fd9760e11503bfecab0708a81fef5518384540bffd76b9c22a05ffdb85ce11503bfecc2e708a81f7f61d7384540effb2ab9c22a07fbd545ce11502fff5daa708a81dff6e55384540bffb70a9c22a077fd9854e11502ffedbaa708a81dff65d5384540effb2aa9c22a07f7d8554e11503fdeaa2a708a81ff760d5384540ffbae6a9c22a077fe8864a11503bfec3b2508a81dff6159284540effb06c9422a077fd5364a11502fff5db0508a81bff2e98284540effb30c1422a077fd9760a11503dfec3b0508a81dff6558284540ff7aa8c1422a077fd9360a11503dfec1b0508a817ff6d48284540effb2a41422a07fbd5420a11502ffed else 0xe749cc49b149a14986496b49504935491a48ff48e448c948ae48934878485d484d4832481747fc47ec47d147c147b1479647704760473a471f470f46ff46ef46df46cf46b44699467e46634648462d461245f745dc45c145a6458b45704555453a452a450444e944d944be44a34488446d445d444d44324422440743ec43d143c143a64380435a433f431942fe42e342c842ad42924277425c424142314216420641f641e641d641c641a041904175414f413f4124410940ee40d340c340a8408d40724057403c402c401c40013fe63fcb3fb03f8a3f6f3f543f393f1e3f0e3ee83ecd3eb23ea23e7c3e613e463e363e263e0b3df03dd53daf3d7e3d633d483d383d283d023cdc3cc13cb13c8b3c7b3c603c453c143c043bde3bb83b9d3b823b673b573b3c3b163b063aeb3ad03ab53a9a3a7f3a6f3a543a393a293a0e39f339e339c839ad399d3977395c394c393c39213911390138e638d638c638ab38903875385a384a383a382a380f37f437d937be37ae379337783768374d373d372236fc36e136c636ab369b368036653655363a361f360f35ff35e435d435c435b435a4359435843569354e353e3518350834f834e834d834bd34a2348734773467344c34313421340633f633e633d633c633b6339b33803365333f33243314330432e932ce32b332a3329332833273325832483238321d320d31f231d731b1318b314f3134310e30e830cd30a730813066301f2ff92fd32fb82f872f402f252ee92ec32e9d2e772e462e202e052ddf2da32d722d412d1b2d002ce52cca2c992c7e2c4d2c3d2c172bfc2be12bc62bab2b902b802b442b1e2ae22abc2a962a7b2a552a3a2a1f29f929d329ad29872961292528de28b8287c2840280427de27b827872761272526ff26ce26922656261a25f425d925a82556253024e924ce249d2482245c2436241b23f523ae2367234c231b22ea22b922882257222621f521cf21b42199217e2163213d212220fc20e120b0209520592033200d1ff21fcc1fa61f8b1f701f341ef81edd1eb71e911e6b1e451e1f1df91dd31dad1d921d771d5c1d4c1d1b1d001ce51cca1caf1c941c791c5e1c431c281c0d1bf21bd71bbc1b751b231ae71acc1ab11a961a7b1a551a2419f319d819bd19a21987196c19511936190518d418b9189318621831180b17cf17a917781731170016b916931678163c162115da15bf158e156815421527150114d014891458143d140c13db13aa13791348131712e612c012a5128a12641249122e1213120311dd11c211b21197117c1156111a10d31097105b1035100f0fe90fc30fa80f770f510f150eef0ed40eb90e930e620e470e160de50db40d780d260cf50cb90c9e0c6d0c310bf50bcf0ba90b830b5d0b370b060aca0aa40a730a580a3d0a2209e609c009a50969094e090708ec08) else (if i < 13 then 0x5d81428132811780fc80e180c680ab809b80808065804a802f80147fee7fd37fc37fb37fa37f937f787f687f4d7f3d7f2d7f1d7f0d7ef27ed77ec77eb77ea77e977e7c7e6c7e517e417e267e167dfb7de07dc57daa7d8f7d747d597d3e7d187cfd7ced7cd27cb77ca77c977c7c7c6c7c517c367c1b7c0b7bf07be07bc57bb57b8f7b747b647b497b397b297b197afe7ae37ac87aad7a927a777a5c7a417a1b7a0079e579ca79af799f79847969794e7933791878fd78e278bc78a17886786b7845781f780477de77c377a877827767774c77317716770676e076c5769f7684767476647633761875f275d775bc7596757b75607545752a750f74f474d974b3748d74727457743c742c741173eb73db73c073b07395737a736a73447329731972fe72ee72d372c372b37298728872787268724d72327217720771ec71d171c171a6718b71707160715071357125710a70fa70d470c470b470a4709470797069704e703e702e70136ff86fe86fc26fa76f976f7c6f616f516f2b6f1b6f006ee56ed56eba6e9f6e8f6e7f6e6f6e5f6e446e346e246e146e046df46de46dc96dae6d9e6d786d686d586d3d6d226d076cec6cdc6cc16ca66c546c396c136bf86bc76b966b866b3f6b036ae86acd6a916a766a5b6a1f69d8699c6960692468e868ac6870683467f867bc678b6770671e670366d266b7667b6660662f65e865b76586653f650364c764a16486646b6450642a640463d363b8639d6356633062e962a26266624b620f61de618c615b612a60ee60d36097605b60406025600a5fef5fd45fb95f9e5f835f5d5f425f275f0c5ef15ed65ebb5ea05e855e6a5e4f5e345e195df35dd85dbd5da25d875d6c5d5c5d365d265d005cf05cca5caf5c895c795c695c4e5c285c185c085be25bd25bac5b915b765b5b5b4b5b305b0a5afa5adf5ac45ab45a995a895a6e5a535a2d5a1259ec59dc59cc59bc59ac599c598159715956594659365926590b58f058e058c558aa589a588a587a585f58445834580e57f357e357c857ad579d5782577257625747572c570656f656db56c056b0568a566456545639561355f855dd55cd55b2557655665556550454c8548154715461545154415426541653fb53e053c553aa539a538a537a535f534f533f53245314530452e952d952be52a35293528352735258523d5222520751ec51d151c151b15196517b516b51505135511a50ff50d950be50a35088506d505d50425032501750074ff74fe74fcc4fb14f964f7b4f604f504f404f254f154efa4edf4ec44ea94e8e4e734e584e484e384e284e184dfd4de24dd24db74d9c4d814d5b4d404d304d154cfa4cea4ccf4cbf4caf4c9f4c8f4c744c594c334c184bfd4be24bbc4b964b7b4b554b3a4b1f4b044af44ae44ad44ab94aa94a994a7e4a6e4a484a2d4a1249f749 else (if i < 14 then 0x3beddbeb7be86be6bbe3abe09bdd8bda7bd81bd5bbd35bd0fbcdebcadbc7cbc4bbc1abbe9bbb8bb9dbb82bb5cbb2bbaefbabeba8dba67ba41ba10b9eab9b9b988b94cb926b8f5b8c4b888b857b826b7f5b7cfb79eb762b73cb70bb6e5b6bfb68eb65db62cb5fbb5bfb58eb55db537b506b4d5b4a4b47eb463b43db422b3fcb3e1b3bbb3a0b37ab354b339b329b319b2feb2d8b2bdb2adb292b282b272b257b247b22cb21cb201b1e6b1d6b1b0b195b17ab15fb144b129b10eb0feb0e3b0d3b0adb09db08db07db06db052b037b027b001afe6afcbafb0af95af7aaf5faf44af34af24aefeaee3aed3aec3aea8ae8dae72ae57ae31ae00ade5add5adafad94ad63ad53ad2dad1dad02acdcacc1ac9bac80ac65ac55ac3aac1fac04abe9abd9abb3ab98ab88ab6dab5dab4dab32ab17aafcaae1aac6aaabaa90aa6aaa4faa34aa19aa09a9f9a9d3a9c3a99da98da967a941a931a916a8fba8d5a8c5a89fa88fa869a84ea833a823a808a7eda7d2a7c2a7b2a7a2a792a782a75ca741a731a721a711a701a6f1a6e1a6d1a6c1a6b1a696a686a66ba650a640a625a615a5faa5dfa5b9a59ea58ea573a558a548a52da51da50da4f2a4e2a4c7a4a1a486a46ba45ba435a40fa3ffa3e4a3bea3aea39ea38ea37ea36ea35ea343a333a323a313a2f8a2e8a2cda2b2a297a287a277a25ca24ca231a216a206a1eba1d0a1b5a19aa17fa164a149a12ea11ea10ea0fea0e3a0c8a0ada092a077a05ca041a01b9ff59fcf9fbf9fa49f7e9f589f3d9f229f079ee19ebb9ea09e859e6a9e4f9e349e0e9df39dd89dbd9dad9d929d779d5c9d4c9d319d219d069ceb9cdb9ccb9cb09c959c859c6a9c4f9c3f9c2f9c1f9c049be99bce9bb39b989b7d9b6d9b5d9b429b329b0c9af19ad69abb9aa09a859a5f9a449a349a199a0999ee99de99ce99b39998997d99629947990098a398729836982697ea97cf9788974c971b96d4968d965c961595c3957c9535950494d394b8947c946c940f93c89376932f931492ee92d392ad929292779251922b920591ea91c4919e9178915d914d9132912290fc90e190d190b6909b9075904f903f902f90148ff98fde8fb88f928f6c8f468f2b8f108ef58ee58ebf8eaf8e948e798e5e8e438e338e0d8df28de28da68d8b8d658d3f8d248cfe8ce38cb28c6b8c3a8c2a8bf98bb28b818b668b4b8b1a8ade8ab88aa88a778a468a2b8a1089f589b989728962891b890088e588ca88af889f886e88538843880787f787d187ab87908780875a87348724870986ee86d386c386b38698865c864c861085df85cf85b485a485898537850684f684db84c084a5849584858475845a843f8424840983f983de83c383a88398837d836283478337831c830182e682d682bb82a082908275825a823f8224820981ee81d381b881a8818d817d816d81 else 0x857caacb8246408248c40889004119df2b12e09190a4839a3448c8564a80411b2961c7d12f31a28392b248c7714b51120824b8b0e694962879468c4d8949232b24472ca58d30e47954cd5153bf1a1c418ee23e8ca58734808256bf1044d7de2b2961cc182099a2c4111d59704849910ea83926433aa104918c9912311495704c870e4b145ea3443ab46a87477878d4cd57e8754808240bc48c4754fa1322464c04754fa13226023aa7d09910ea9f426448c9808ea9f42644c04754fa13226023aa7d09910ba15924634829dc54a52088eaa392643a3448c4ae0990894923151a09593aa48c67568d082084ea93211192442292ae0910e1cd202d517a8d1694d20a351de1e353355fa53482a40412d208ee5662f51a29362b048c65d0919591b1aa40564657c2f1231b1a2462653c612f123250e4efc686d7de2b2947848cb43925f1a1a774822a1c9044d7d2f1231b29a1d80b8d118d123116a3912e09190a4839a3448c857cac94e08248734a4b145ea3453910e694d1aa1d1d9a99eafd0eaaa104943a3b9598bd468a4a4918b8c574aaa48c85178c10e28448ca4a78c1f439048ca5d0ac923195f2ba48c67209912318393904c8672099123195f28a50891911cb0e2b21798d1683277e34361cdd18d159204be3424829dc54192088a4b0e4ee1798d1701159e3432b2c684c813b9590bcc68a0578d091cb2961c9d8e431a37182462a4048c54828d0a8d520151aa402a35480543891889151a15202462a41468443816d74c35520bcd894976c34540b43816b74a91868bd15ba5201f452525430d1762d5fa5341987745c354e0f869a45381d29a1d409a461aae86e30418b4745e6c0b4d57e8330eaab86a9c1b0d5556e832be56300745a71480cd7e87158e8b86a9c1a94d06a05803a2b74a4072bf43883355a71868d86a9c3481d5fa53801a4538a406e8b481ba0c94962c345788d7c9490ea9186a9c1a94d0ea05869ba54833292c54e30d5482b0e2d55229c61a2d5fa52c3aa461aa706e6cc82a40dafb2960d803a2d386407652c3a81348c34dd0cd7d94b0ec354e1a419afb29c00d229c3203729e1dc09ba548c346ebfca78330ee8b4e30d1faff29e1cd229c15ec347d2b6d285d254d239d208d1ccd19bd16ad139d113d0e2d0b1d08bd065d03fd019cff3cfc2cf86cf4acf24cef3cec2ce91ce60ce3ace09cdd8cdb2cd76cd3accfecccdcca7cc81cc50cc1fcbeecbb2cb76cb45cb09cae3caa7ca60ca19c9e8c9b7c97bc955c92fc909c8d8c8a7c88cc866c835c804c7d3c7b8c787c761c73bc715c6efc6bec698c65cc620c5efc5c9c5a3c57dc562c53cc50bc4dac4b4c499c47ec463c432c417c3f1c3c0c384c353c338c307c2d6c2b0c28ac259c228c1f7c1d1c1b6c190c16ac139c108c0ccc09bc080c05ac029bfedbfc7bf96bf65bf29bf))) else (if i < 18 then (if i < 16 then 0x2c6804898d058d05aff1a11496342472c6848e58d098d058d058d04c321c11496342472c684ca78d098d058d149131a472263412342245618346a830820a39b0c3a3541844cac30a8d506131a0922b0c2a354184c6828e58d09e2b1a11120f180921e302a341e301e301e301e301e301247c6044878c0b8c0541121e303e301e301a401e301243c604486900890f1817180f180bc5e302243c605468257e830987059c048904a805810594f36130ee6c260dcd84561a2f361912e6c261c1690105b800444b00088750213740b290b060e00095869022781296121380044242427000884e0011499e848c60d8ac9231cf42520e491959293224629e852c918c3b959246326448c4bd09492319593aa48c6464910aafd29a410f28d2dd30772465646c6a901591b1a24622920da8d1232529a3543a3b1c8c80625248c53d08715507248ca1dcac92318750bc48c67209912319a9390c689190aa877246328b10442dc7a0411cf49700dcac123295f97048cac90af94897048c8bd25c1231d00882208248c52e09188afcb82b048c8c689188af95597048c848c2bd0871231d20a342a1c48c448a8d088712310412462082178aca5831774465a6c93b8d0eafd293914e21196aa9778463ae8566118e1094111490d0504740a1188dc423160e3905047838e41411e0e3905047838e41411e0e39050460dc392c807e19caeda94d0e2ed3228d1a641292463abf4a69c4c824652524389c4c8246525240a641232ee52ed320918d6410224632be50a64123210e59048c64a4811f499048ca124fa71a193709346891909b94202b4696415871f44b29798d1594b0e670c6a6414ba921282359050454a62851a2ee4abf6da94d0ea05469641caa97724633e8c6987259497500c1e38d098731a2ee964817b8d0a64132246390c754918c9912311375904c8757cead0ea71469641aafc49a3543a25b40305e24623aa7d09912321d50927d09913031d53e84c887d0eab1a2464c0c754fa13226063aa7d09913031d53e84c88514919771932246225248c47568d0a2cd1a131aa405dc6c68918994a5e24630cbc684d7d9c25924640a1c684d7ddb32949648cacda0971a1b5f4bc48c6c68918a6412128239906e0918c9094112c828222ea5d22cc50a345a5343aba51a590589250455d2aa92319292ba48c677ca092319df092504677ca0923195f2ba48c67549094119d528248c6484a088811231177a342a3412ee504dc12325002822a3448c546891898d123151a246221c48c54828d0a9051a1520a34223448c448a8d088d1231122a342093c803904c57019cc17c01dc5042094ac84138490ae1495c01e295f882228b10444862088a4c41115897048c657c908412b242be5225c12324b82462a01104540220882092314b8246297048c54022088af95897048c else (if i < 17 then 0x199042904178b2084466410a8d068d0411048cc4111210222a34123261b8d0c08921151a0919e3420224844c682044908a41040a840f60011198822232027000e04848cf1a10092922812138a4678d0c8c809c0036341233c68446404e001921812203d2084024248e900890af4d914801a16900690076f832243b209004404a706bbd36451a0685dbfb149083fa400d0d4803c6021043c6024868d0b8c048cf1a1119e342233c6844678d0941048c848c843031a131a0b060919e34250412321232f7c4f7c24678d088cf1a15c50d1a0b1a0b5fe3422337d050e68d088cf1a1119bba287346847742c6824678d0ad4919151a0919e342233c684465ef88993df11322338006465fa088cbdd1119e342233c68580024a58d0a8d04b515913c50d1a0d1a09326342233c6844678d088cf1a1119baa2a3413aa10828e4546824678d088cf1a11421ee287346844678d08ac9421439a3423e8178a1b6c1b6c105ac6848e58d0983048cf1a1518b522a53c6841051cda91d29e3426341472c6844668d0a8d048c9d5151a0d1a0d1a0d1a09197be2244f7c44888ce0019197e82232f744465d48891119c003504ea48c8c8cbd511222338006489d4888cf1a1119e342c001a401a3412c44845468346824c890898d04a4919e343233c6844678d08a7121151a0921a40208248454682538908890b1a11191722233c6840f8908a8d4391119e34207c484546a1c8890d2011322422a350e44c6830e6db088cf1a1119e342c001233c684484346824678d08ac9292423a3413be4678d0c20921151a0d200d200d1a0b1a09a9c0022b2f1444858d0890f1a11216342242c6844858d098d1211121634243848444858d0890b1a1121e342233c684466c30a8304e2919e343233618541824658d088cf1a1119b0c22434184a0824642465ef89ef848cbc511197e82232f7444642ea48c88b5119c003504ea48c8c8cbd511422338006c61d488b1121114e242207c484443890888cf1a1119e34261d8004a0824198d0a8d04a485e2868d068d0499119c003a341232c6844888ce001b200921a3422bec6844678d088cd86150609196342233c684466c30890d061119b902a341a341242c8044868d088cf1a1119e342078466db0e1cd1a1119e34207852450e68d09e28499119c00330d80050e68d098d0491119c003242c8044868d0adb06db048cf1a1119e34268b80047148cf1a1dc5233800ac12e2d1a1119e342e341a34138a4678d0ee28414723b8b4684a0837148331a1bc50dc5a342b8ac68571491119c0046401b8a4868d0ee2929634335380044678d088cd8615060937e3422324191c8c20848cf1a1119b0c2a0c484444b8d088cf1a16000919e342224484546824678d0889149151a0919e342224484546827148cf1a19122422a3416341292f145480348 else 0x7c4471ef888e119c0032325044464a0888cba9111c2338006a19d491919197aa2238465db0c8e121111c242226c470908c8e1211119e342233c684cdb00094306db1026343b6d46845dadb2491db6a342e341a341b6c4c88ce0025b66342b6c4868d0c8c9411049e342232409248ce2d02171a23222336084c688c888cf1a15022422233c6846d88cf1a184b23380071268d08c160011191bc276c189346844c88cdc51b1a0921a342b8a1233c685c688c8b0004db119e343c00464546824678d0a8d04a0939151a0a860902634276c163416341a3448444718d08d4e0013c50919e342233608540824678d0a811211119a342a341a341233468546824668d0a8d054351a2323a341a341a341a34124346854682eda8d0a8d068d040af1a1119e342c00136c4678d0c0a921151a0919e34202a484546824e40a9211d1a0919e34202a4844c6824e5db089088215200d200b1a0f180921e302a341e301e301e301e301e301247c6044878c0b8c0543121e303e301e301247c6044878c09db7181121e302e30124346844878c0805e860ce4642bc4104a7433c6840687b01f1867d042dbfae0ac82522dff6c564129341043d872b8a0652081f34df253ae0ac8252e18d042c05c685bd364119264094b0cb410a1968210c90329043881f2cdf233a183e85e04a61bfb20909320885c043886c71a0885c0438b6471a0885d904647b13204a5c0438b6471a0885c043886c71a08854044678d01f0885c0438b6431a0885dbe57f5c15904a50320680f844213223225be0c894919d0c1f4129e1951a1686de875412921951a16d52441e48c8242c22d0420f612c90844207c0e40655c0ce03e60c11a0a484426df4825641290378c9032ae01a81f315f0f612c908442edf06bb21208252e18404484780b8d0890e821602e342464487410d19121634303c4640281f2618d042c31a0840c88c80cde8360129b0c40224230e43240c86948207cd37f0c011b9048422180101e23207c22148c88916df2bfae0ac82528195703600f936f95f28a466eaa1c07e72644640f8442602e3407c22100f11901207c12948c8891072032ae06801f2edf0c1720908442a1a1122c31a08580b8d08a4e821602e342465a0848c98d0b0171a101a1bc07c607b41088cc1c1119838223307044660e088cc1c1119838223307044660e088cc1c11198382232e184f148cc1c191970c22330704071c30833cb81067970288210c04665c0e208499119970308212444665c0c90c4110602332e0720831042466208825919c003a3419041264466e28d8d0491119c00324346844646588a4d1a10320919882205b8008c8e8d048cf1a102d2b22a341065208546820c98d081931a11222338007468908816e0023239041a341a3419041904123320852082072410a8d068d068d048cc8211)) else (if i < 19 then 0x660e407c168210d27d16471a4071d90484a093549292efb20919743076feb8d904c891961968610b703e0656471a0e269be4e0226c824651ec4c86c123268ed041a4fa71a1b06d1da08349f4e34360c3d98d0d8246406ba08349f4e34360c467476820d27d38d0d83e1ad1c1a4fa0d803e6d1da08349f4264360c0656471a088495248f64177241a23225be4a4226c82465a341b6c07c0c87205a1a56471a4041d5243b641232ee60de2dc0f819591c681a9f6f835d70c6b641233121d0c2482487430f0d6061232243a1864858d080f3df101e23380060788cc86181e233800607890880f10e242303c438908c33b0ec0030cf21854682504ba8a8d0499119c003232c68521824868d088cf1a103c2336d864c88ce001c860b1a0921640224346840ca6408e2919e343233320178ce2919e34305e466640ee2d1a10329902b8ac685218371490d1a18220919e34202448444678d0809121141209c5233c68604890898d076fed52425040f960e6861121839a1864708ce0019191782238465640c0912112c80323d80f909b1290e3b209083d35b6233800bb1143047511c2463789a38349df1b3c686f187531a246378846444888cd82101a03207c2b90af871d904841e940f600232350c1dbe4c8918de26df06448c6f108c8891119b0428344644b7c81044d9048cbb7c20902daa4841e9a8d076fec50894689081f3121a3422334684464dc09e2d1a151a081902207c12900a92112860edf435b549083d281c09b6233c68646404e0018092722812138a4678d0c8c809c0036341233c68448604880e48610890c860923a342d8a438221210d25a341dbe468226c82465d8bae01906927180921a402e30178bc605b7f54d0e01a10764123380ddaa10434938c048cf1a1119e342233c684a182464246421858d088cf1a115f8922233c68571431268d09aff1a11412ea2a341233c684466ee8a24d1a11dd0a496342233c684466d48a8d048cf1a1119b522a341233c685c688c888cbdf11327be226436444c86c888cf1a1119e342c001252c6854682f1434682504ba8a8d049931a1119e342233c6844678d088cdd511d50919baa289346844678d088cf1a1119e342284467000c8cf1a151a0bc50db60db60919a342a341232754546834683468346824678d088cf1a16000a860d200d1a09622422a3412825d4546824c890898d048c8c91119e34229c48444869008a0921151a892229c48444858d089b919e343233c6844843468ba888cf1a11210d1a0932242263412eb6d844678d088cf1a16000919e3422421233c685468277c8cf1a19412422a341242a18548034802c6826a7000924bc511216342243c6844858d0890b1a131a2422242c684c694312119216342242c684464a0888cd8215020f1a232223360844658d088cf1a15022422232f else (if i < 20 then 0x5c68807f01057e3440e45601902d0ae503e0174171a200b15fa0b8d106c5c506487098080fe1a18d8065208ea9254a222448082b970101fc3435be6a70143220050e3c68605417027181f00ba0b8d100f805d05c68986089482242403e0174171a20d029244a41121281fc0415f8d111911290448488ca4721c1949c0407f0d116fe1ac0548098600580ad04401602b410c06a1c100b015a086468b40962a82a40350548041a402d2018052d02504b22900d54857a4031254684464246424678d0899119c003233c68580025a8ac89e2867a048c9d5151a0919e342c0012c448444c890898d04a4919e343233c684538908890d20114e2422242c6844678d0b00048cf1a11210959252484748034802c682bd02565e2888cbc51119096a2338006465ea88b1121114e242221c48444678d09876001078292278a1a341264467000c8cb1a13200cf40919b902242c8044678d09a2e0011c5233c6877148ce002b04233c685c6837148331a1dc56342b8a4888ce0023200dc5252c686bd024678d0a5b119b0c3233c6852d88cd861f1a2322225c68580024678d08891211119e342224524546827148cf1a191224226341292f1454803480246620888cc4111198822238484447090888e1211119882278a466208c8cc4111122422233104438023dc21d88ce001d1a09322338006c6824888ce0018762332e072e024678d088cf1a114b23380072e024c88cdc51b1a092223380064646f088cf1a16000919e342c0046444678d08ac868d065c058d058d0491119c003c0046452e02bd02f1434683468346834683468346824668d0a8d05e2d1a11199702a341233c68580024678d081f121111930dc6860f8908a8d048cf1a11322422634107c48452e0348024278d0b00048cf1a111921380064678d0884949151a09c5233c68646484e001b1a0919e342232427000e5c05e28590078c078c078c0491f1817180f180f180921a402e30178bc604487200891f1817180f180921a342e3012bb08444678d0b0004a0a211421a3422bec6844678d088cf1a113c442227888450868d09e286db06db048e421111c84222390844465c3088e4211119e34266d80056d88131a1976b6c88476da10d1a1f1a0c21a342b6c4c9108edb17644233058004464a088a4f1a11492048846716814211f1a232220488444678d08812211119e34236c4678d0ca5a211182c0022968844ed830868d08a5a21114b4422b8a1233c6858002505108a8d421131a0a21091c63423538004f1424678d0881221151a0d1a0d1a0919a3422334684464dc09e2d1a1500842276d4685468346824278d0b0004db119e3432128844425108a10d1a1109442284346847148cf1a190944226341204c684ed824198d09e2858d048cf1a11024422233c68440910898022114df26e07c226c824 else 0x67232a1815908c80b50c01481c88cf1ad0c41d5a1843a88c87205e40e2904a0919d0c51d40c98d686261ad0c5a034905b919e35a1884678d68619422321c8219061032d0d6d8986b035b61af450d46863a94351a1a86a3430864678d6861867029a18b41234241283218ba95191320291a3431643068634316e4678d686213750dc680a125b48607e48492d80a03fd0c496d2198d0cbae1ac0c7d081c88cf1ad0c4029c6b430c3485a0e41bc9094efab6029c6b43152094195205343141a814d0c4c89868c70691835d0cc686b7cd4e0686448384700568622f4014507431038c1c23802b43160e11980cea405142180a2822f090708e00a4d1a18a028a08bc1aa98384700568628f6b6c02a4306701269bf6d919132015a18d37edb486634410dc688c82e20d90164674358228d923247060783482418722320b8602a4314105c40652198d02e2044282290c0b58d0c8c886e341c4802c8ce86b04410c1a4120152286a3425e84654351a207150d46864649900d1a860894686a183451a1ab62420f68d1154a86a3430d32181281624252732181281624250152180b025248604ac6864e41e9411af450d46861a68d0943043a3435beed834d1a21210d20ba8d10908692383d0419c4b7f410802e82101f00ba0b8d1023a1c1067d0554c70c899005d04458b0c899005d04503e0174171a20ead0421d44a433a1c20712d401741130d6026a631d40c90e0f0d6022d00b898086c02ee34403e0174171a26023ab86870ca0e0a191d505c31d40ca0e0e1112200ba089088910050f640e308891005d04503e0174171a20e2d0420ce870b40e3416200ba0891a11913200ba08a1a11921c181f00ba0b8d100f805d05c6881f0a7482a40484b80890e1a1a3200a14868c890a1c181f00ba0b8d101ae82101f00ba0b8d103782e0e4484807c02e82e3442b24a6411212035264870663b0161a182e06a87066a70161a195935380b0d130c00503fa0880152981f1964c300140fe82261800a07f41101732003e484807c02e82e344016870419d0e0a6f805d04303f86b0135324df4644c802e822cdf4644650e111112200a19898080fe1a18050e3c68602802d86d04490c094068c89005d0409c802802d86d04409986002e82b90503f8680b0c0f805d0)))))
def lvl11 : Packing := (1688,4,7,0,0,16,0,words11)
def idx12 (i : Nat) : Nat := (if i < 3 then (if i < 1 then 0xc674e028a009ef803908072d8474e665b01940c336c850f0000000003c27d30371901eda0178418f300c5d13d80000000007030f91410a0cd40000604f20000040599c348d86830000000000000000000b04e000002c2697a538e138c00003c0c3800000000040ea682111001a508b9c1a2401faa055d30202e1345851850376f05d782b6dc07a881edc086d40a1400000a1a95104ce306081220017d000014123e41b0000000000102f718111582370000160c6f80e2a846300000e0a5440f95821af17bce04b4018a1052c902c98036900b84841a00001a104c0000403a54139c627ef191fc84ad00000000000000084ed00000413cc0000083828049c619748058902f80013da1300428290218000000000300eb8848ed04ba0000240010332a102880000284966867600c49c18c98226b86155983e218f400005a54bc049240f3ac31fa84b6807ac629f000d6e8677e0032014f901287019620d1c00001833e23327907904225800002800380c5e000018218b8111106f4a2d0180f4303c49a8220000045a200c285172f616b800006032be0622206288259800ddc0c760000101084888e40cea40d64d8008000000000628a181f4388de2188521739c1493039670a1460ab1c04cd04dcc057c21193822a484d80000000002029b784ecc078fa167f41a818094010209080a110d281301073308140d510619002907544d001d02165c0d1a042b0403294d00030031000c0d676d0202090904c92500060001002819370d02122100002a02126b3311000f011104040119021e160b0b0d3613a41b01753f0011361b40060e01370907080420010507140902032f070006011a090308020204190104030a020609170c3501010d1501b2231c0291870000031e280c09006518090058000722103b04691d0100007312100516060d07092829030a07022f0207020908020a0202341b0223210ad648000f00040a1d770125087618001406357c0b050704020c01390e000c01061f2a02030400001c0101140d0f010e000f23030b21060a030008160c151e0301040012080403021166041e0102300000060a12060f00050b0a1c06000302350003170e010406040d0e2d051823010d1a1a07051c2a000d020a0e1e03021e020416040a06050f02000e01000304120e0b1003092801180b5200041d0811020a210102090116021d03240506020f2000031005185203110c061b1b0906075102050102180d03390103110b00020a040b07260e03012e0e0a0003000505601d0c00101017005104060401000d6c06000105050000000901100001001b05000c0e042107070200001b131b040c01040204110819070b2f0811012e020000000200030120010506071b0100000e150622031600131800020407030102120405020004040102000300010c00000301 else (if i < 2 then 0x48d09c0c2dc202c415e1009d1025000001c4dec85d591760c21ff4308601a11122681808c463a00a8919e18a7a84335b844c40734000028238905884064cc17ea4000085e0d1bd5a0ba201c928263a550180077c232a0499207e7222dc067f381a8d020c017d200924090d00c94014ba403b5821ee0b38e0b5a00022060ff0a7e60c5c852540118c0bb800002c1ae78847402b7214d282a92057590ce76188e428e48865000004149e4333800009097c022a940c1e8bd91378d6139b407b90d23d0108c2d300000103bab0a12e08e3c4260031de647a60f79c03c000000000180720c4044065a404b7a0ff4823e60d2bc0d2e0199882e1d802320c56a195d0800d02603017b40e6d82c19849800000000024252208128039200000000060647b0bc7610f800342014b70b9800000000020692e04a2211044008702b200771a28c8000000000b07efc18a0c15f800008a837402f2827b00000b08d9267f1c2dba0256502cb20204413988123003cc00003c2576082740603402720180704c980bda809d8417e8024fd03c260cc0c0b380000e0003a05028693501ef20b91c086781d3a003c00000000000000381d300333e10460123d8491c0cb2205c742c10820da013f20aec12d92055cc1683e0aa6414c4800c919f8813a040e58088fa0298e98094224900d0b109b80f6cc277dd38320af1a0db742c3205ba7070b414f7040e3847ed020e63441cca888685e0224000001522f8ce3e0a77a33e7832ae8cb74066f214ddc1af3851a310bbe17b102b81027e7031c8181e01d00000037ad9212a1445049a6200000c16aa0035f8549f0af9406c582dc5031a912d2665c900f2d02fba000f61512444bb0d27e1a1180268830930c067052f4ccb282b1e02ba2093f4060205a500d30603bce034dc0356039970070e30ab8028203afb08ecc0b92c2f0b8492f02d182870000000000c022000000000010296001e5c0319c25e708df007e1c02cf804b689fd317ae0000001fdd868750a31e05080000301fb70beba16a5815400000108bdc159dc22aa0ca840861e156ac081e801821033a0b8e8310809bae03a34062400000056cf0650000000000001bf4027284003419f8000000001e3445c1fd10252c04b4610f400003038fa071a40515823c0038100001e04bd01fc108b6d08de000014109c00c1602152c22781b54054c000000000181825064e00000010d742b9a0684a0cf1814338079983f670abdc055a8021603770000161048014622560000000102b0116500bb00001c06a7065c789d800001c296b009e202d7d01a4e29af02d38000091152c0a1f0dab60bdab0b0be16c36a1fa8146754b801064000000000d07b980e8c000071c21a072aa0c43425600000d164b0089c0000185740000022c87047d988f8b05a800003408b08b8ff084001061 else 0x3006a9c020c000058514e03f240a27410e783471159280f8e81c400000b08a60000000000027a01570ec14c00007819f60916868e502d1186520ace42019700ee285f8f05b80000101f240089807a760283805c20071200b200002d828d02af202ecb45e000000821500001e0a229c8a4056b90c9b0189a4160b1b7e602af4036cc27728642f04dc000000000508ffa0ca2ad8c8c1bf58672b00bf20652c1f1081af64586a267000007803940859208f5c47ee82f1103e800000057978686e05bf40c38c1c898543e08db0089ac2ebf81619083640437810180000c0c6c6145f8024f049b8094b402a84241282dd3083c821de006a7019d20d262852900db80163f0947e401602211836200000c09f7819f00000b0944000014023800000000061a4340b50000000000001c983460000060d17820d241e068688705462119d404390186304e2c13140000000008088ba007c00001000aa0a78a125001a9183b2e038de04658160200a5c14e6e34a98110200a20000080347c063d01d8f0afee009181af8040780305348f8c5fb482e6b0738a0094000028365a048a0063c4235788bcf1498a065400003018550172000000000602cff083e830e140068085740ba1618e7a52f1834d40d2ba180584273021ba091922ee4000010bd4e0066000034036505ea4646e00002c71bc4c2000001019e9c22180000202b3c0fbec0872034c4017d617c882ff98177301580000241f048383a093800002260f68842e06cd62710c170984f02059ce176902ea782724039d2c6d340d6780c9b0961a0edaeb27c89a7412cae131801f700000809fbc17635156e8d2220c128018c414f382fe200de018e0c0f1105f10000001494c68ca84da601bf4179ac02d902aeb0ba6e0b6e006441a5e00000e049d02c3a04b4609d56f5e2826a5822480a25e04f7828ea0cf68078a20f76403fc8535901260000101dac805c4077c00003c0c8788c0d6483e0d248162384af6067020ff1c3219816db06ea427d002800814d60c316051d00e51014ec054ba1776c10bc02b8d0b8c6185c8111c00a750897c18dc41ad1804df102bc09f300c08000040146667928004e85c740b42002fc4169283569008c000029969e80d8e045740c62842f80452a0873c16630d7fc0132d181100b15c723a816900000a16670050a0105b072ec091802f3a390aea436817164040085a3f1a349306705f9e056500000e182c00000000060751421f041bda0036d606c624c6415b8000090269a19d1c18ac8a49e043fa0c4800004006e31a59407484d081034b805010075002c98000080400410e0c50ff033b90b624ca9b83056056e70abf609664578781625087600002c460d8257a0346414591afef01f5763a0202c3424d281f3b5017a0ce802f800000108a0a0e1282a730372e01afa341302a0)) else (if i < 5 then (if i < 4 then 0x5c00001802a200e300000a78e0000030192e1317807c4000000000000010184f40e61029bb0535e082400c27820a00000000030202000006004de109800005b2ed00001800b8c0cc00000a0114419ec00000000070b2400000c2e14055790262a128541510000010cc40000000006851b60915207e1d82ab0207e0594c0b7842f278120b0c1d400c202eb280c0f04da605b802c51049d84c0fa167641e480479404b90127a0330280cdd084200002c0e1482c220175a0a800100d81a0e0c22000000000181b860062a0048000028cb9c123660dfd827480000e05abe0c2000007025ef00940000140479017e3074860a0780aeb01b9a08812069141cfa850e90b2901611c0bc9807e60366601c141bc80bdd11978e20bb0d6d501b5e04d5c1803015898286b084e80a2e40d7200d571577a17100000283b100000c1364c324a80796060f0101541f31893900777833bcc007582310000000630c14ef8028d02b883386802e8000080c902c153c036e0017e04502056a033fa01370000000003015a50361104f3400eec14cc01bbf0118000000329b3239419cca17f9428ff8d14a06820000382e89040280205c030edb044846ed0b120000241aea8e1ab1507a0a37c12019b3500000201208206c821640b030197bc235f867ea0769202a4000008100f08f761482812f9838e70cb040a0f822e90551e128600000c3410000000001621e540d2a05fca0d1e0000101028833100001c055005b6c80d970c0b4043340568000030a7026e628d2f800006b383409d000000002da04eaa0c4c000020321d153ec04da803118060b098ec03b60283481d5819af00bbf42da30503a0a0420f9c41ac5054d70a56c17afc0e3e00200000000003408470425b032f40f2800000824800000617b9d2d8a020ff03c78080a06c26815ee09e2207de41ca30483b064002eedc08fa8c975800b40f0bc17700ce7906464043dc21938d0af06ceb27f000004040c0000000001026270414d129e00544050100000e01f00966f02f128564411b3a1071d2f2c0566f005380556c2a0ab057a1556006f1825900000c0234e2622c025900abe06f0000010421c817a409f8a216e00eb202e2b0291013ed80eda030a50323e0bd140e8121c530b4b6100d816c280de30678602628288882ab10b5a026a880ecb8027201b9336b0c26f581f0f09c0a019381db80000105ce00003c1ec2835700000816a0000000000c058f4125e00c5f00fe00000c04e2401789acab07fea103c000070468e01ac4c8e0c3020000000000d35ca82bbf0a19c1863c024b82b179c1f000016197c00000000080bd342bfac2d998121000000000000006022580345a0a3fc2c6038561026a00b3400003813a6018400003c222680221057ac0018000049003d054ca124084db78521b0a60000004313902d else 0x2f7801f8000000000e33e000000000000000000000034b847a00000006c80000286817045ea066a051be8415943854099fc2719017b4006ba1058000000000d0b5fe18f000006843a0082f608e495389045f0000182e1d80cf503bf19b7e61704827580000c060c00ba400001899700000a2788002610058e0b360c8e8c0d580000d01d4000030316a84ce904780000102074026200000621c7c4410000090ab7a0735831a903537064800003832a60629709baa01680000680f000000c06d88104282a41016a2152800000301650088c09e182b8f834200000618b0417d2827f6984242cc70170704bfe0596746ffc0415842e30c6600b1a81e1bd22160327414bd42c8783eb2168600000000000000c0a100000340d30058b3b01e216fe44060020b00000000000322605a600000a039c0000582f22a6b8000018432000009009e35a2800006043c00000000000000601534011dc0f300000332e2c19f5801470294e8016b003cc0c1400002861fc053fe102f80659860ce021200000000000000d046d0238bc1b718548505d8a1879024ae08d4660ade0f4982f9880e1c024a61299c102236330000063102826b30d998001020057019628d06b07b50115e46a48823e0000141205c08b90a4d301c40000241a000000a05a3e149a04c8b0477400eec152d82a7a8011000018187540b90860610d1a8121d04278015f607a361508000040849f0773c1023826a981da10854c03e8807e0000000001c2d1c4338b0805402b1aa95b01061855400001c39ce0269981750000180187813bf05bb00000a1903553fb8b20407be015a282a98803d004c3017bf426428e5c00001800d2d8cf48656a0ae5c19bac07a081e9d12e120d14002b28400e0ccbe34a00000203e150543606a9c2e58032f716454148c417500000000000000000003d15757a89c198f833cc864600000015ec000000000d0120218b800001848611a4b0176cc1a8c0528c05ea40154c291305f640c7ca0cf4000038b7013bfe00003a001f8d5600000c08b840efc8469f01d10026c02b5104df60056000000000000000000000001408a800001014de2100000038291d14a00000000000031600000a067201de389fa904cc001ec0121a04a9b1340a132d055028634d00f5812dc0000584f8000008132ac25e900755086f6151680fe001527069cc08a400004aa7ef07b38343800005817840a32c0dd3008f6822d401d2a19c0423348073a0c36c042e00fff85bd70cd9021f7411ff86250000100e1981470804ec10e062c8e003a2064b0000000eb8000050a8c0000000f3701be0033340bbc0000042b05062000001c78e4000000000702396310c0000000007075b40a10c53f9844ab165e603bd4304588db9015f0172580a4c8332f07000c8f800005000f7031061638822d80000115) else (if i < 6 then 0x121404000000000804a600f42012a0893240b3c000000000681336025200a700000102d03092682d800000000000000160dae0045d8255719e600003415390a81619e8000034400d05be000000000268f518484e00a40000382c7e85c010b220000140dd585e593c424c71c00005017cf0484e1479813780000e10c66149182085823a106134010081ea380fb70a2060b0dc2caf83f200000816d8c07eb83b300000a183400004004160a67212000000104cf9008a00000000038539a30ccc2fa7058f2a1c1d19f6000034164d0456f071400000000000000303870138840f0683341083aa0bf303324812b607e2a136e81fc80000f6c1dc0df7430d7832ad04960000000d800ae6a34b20000000000000000001ac58d0250605fdf09c380f3f80b79001410369a169040ba20cec1179b811cdc13dab30e706d9c2a1c0000281eb90605007ba05c2a031c84bea0000301a18000000000000024033d023430c9f215608066185bc30af5c06f80330d02f0a0573e0635c2c6c03ea100afe14c7803ef814160afc00dcc00005811d40a65617ed0690e85760000000003d30320550000000000281860000000001e86f0000000000000000000000006028220b940000301e340515b19eb6032ac25c8000090464e166a82bcb0322b0b6a40bdc000000000874800000000006847d0000000003404280000c04d6c0ce70289800007089000002c197486034a016833dc00000000000000a05cc0000000000000120930825c00000804c80000000001045100000e1222423f8568eb0226e05b000006054730d00c03b1469680000412b6e046f41d58000000000613d00000483480000121748000068258f040c0000141a5605f9000007596d80ff0856fd0027616b1c3457832500000a0293c47190a8d208b000000c05bc024100454000000000602352071741188000000000d0d2c40c9c0000285cf30a8c00000000078434d080ce0d198176d04cc00851015b68010800000000060218867ff82f6b02fe82c2ec0b0202b3c011a00002c01900000407e8618c4000050122305e6000034186b8389f0cb80000185073838c20b40000008108a814ae0a1a0000000007000bf09a000003405a2b23cf029f203ba80d3d0369e01d622c0d0403381f6d09cf02b38000030433000018292d072180000f039ef4f2f8148003550000020e1f01585092be1649c96b1824288368f0110e0c6640298880a10730e0e9b03346cbeac0b018345942238cc228165ac01f280fed8303ea94ee07b2068df03ed20797019f580de9218ac64768230c0000585b200001e10a482f4304c10000180929c164400b200001216e48185b03e95163a000010048c842bb05f30803e8212502cc608120000000000000000526000000000604f900000e00b10322c89820000102 else 0x1c4eae0694f0a74a155bc015589fe0000080ca40569402d971009812eb0295283ac000000000302ef80000d0a5a000000527419a1f0b9a415a642720000011035c13f886098000000001811640000004d7d06e18141d8227981e430bb200001c17fd849600001e0c7c007f80000d63e3c066d821fe00cfe012f81335807ca82aab019c000010078800009085a412240000404b5d70038190542b0881e760aaa2045000000000000c44a13d5409330a57e0782000020326503d500001412c401b7e83aab0c32e280302380066fd091b4010e2000a9a6300000000000000602daa0745612af8033083bdf049b008c00000285f70000160d3ec1b2100c4f043be0cdb8501a81c4b04d080e780000384c3919d000774825560813d02860000346714042310cb76113ac0a8205ab00001415f441d0f055900c6000001c196a82b6802d6604fa827fa034400000000020156a84e5ba501207e90253e1a602016c800fa823000ba78012a4165d433520ad829b200000082858000050529200e881d860669201c1c311800001035bb01cde29a3c0e0c83eca1a3e80f96c23a90221e0c2800001800280000009840000240f54039300001a336a669d80401802080000101cee02b5308c200000467900000610f60000281ebf001c00000e08ec8172c82147015c00002822350212c07fc0000000000000080277404a802392813079acb409a7c217f8390119b04291c000000000000000006c06902026c504ca208384119f850490b2ca1873022d0012c5126f60d8c0000101c0e0c75012ecc09700000e6324c18a9c01b80000d1422e04fc0)))
def words10 (i : Nat) : Nat := (if i < 5 then (if i < 2 then (if i < 1 then 0xb7e5c954a2284540b7e5c94ca2284540dbf2bba213084540f3f198a213084540ddf2bb9dd3084540f5f1989dd3084540f9f2889dd3084540def2bb9993084540f6f1989993084540faf2889993084540fcf2779993084540bef1c62953084540bfd1c329530845409ff1cb2153084540bdf1c72153084540bef1c62153084540bfd1c32153084540bfe1c22153084540df72bb9553084540fe72669553084540bfb0ca5513084540fbb2885513084540fdb2775513084540feb2665513084540ff32555513084540bfd2cc54d3084540dfd2bb54d3084540bfd0ca54d3084540f7d19854d3084540fbd28854d3084540fdd27754d3084540fed26654d3084540ff518554d3084540ff525554d3084540ff915454d3084540f3f2886493084540f5f2776493084540f6f2666493084540f772556493084540f7d1536493084540ff51535493084540bef1c61493084540bfd1c31493084540dfe2bb8893084540f7e1988893084540fbe2888893084540fde2778893084540fee2668893084540ff62558893084540ffa1548893084540ffc1538893084540f7e192889308454097f9c3aed828014097f9c1aed828014097facc6e13280140b7eacc6093280140d7eabb6093280140d7dabb8cd8180140b3facc6098180140d3fabb6098180140f3e9825498180140f3e9824c98180140d7eabb8898180140d7dabb8cd5180140b7f2cc6055180140d7f2bb6055180140f7d2336055180140f3f1826055180140f77152605518014097f9c8aed318014097f9c5aed318014097f9c2aed318014097facc6e13180140d3fabba21318014097facc6d5318014097f8cb6093180140d3f9b86093180140b7dacc4c93180140d7dabb4c93180140f7c9824c93180140d7eabb8893180140f3ea888893180140d7e9b58893180140b7f2cc6053180140d7f2bb6053180140d7f1b56053180140f3f1826053180140f7d1326053180140f7e222605318014097facc6e12180140d3fabba21218014097facc6d52180140d3fa886d5218014097f9cb615218014097facc6cd2180140d3fa886cd218014097f9cb60d218014097f9cb54d2180140d7dabb8cd2180140d7d9b58cd2180140b7f2cc4c52180140d7f2bb4c52180140d7f1b84c52180140f3f2884c52180140b7f2cc60e1180140b7f2cc60a1180140f3f18360a1180140f7d23360a1180140b7f2cc54a1180140f7d23354a1180140f7e18254a1180140b7f2cc4ca1180140b7f1c84ca1180140f3f2884ca1180140b7f1c54ca1180140f7e1824ca1180140f7e18388a1180140f7e15388a118014096bdc4aed9399940fe195454d3099940fe91414c53099940ff095454d3088940ff81414c53088940ff115454d308454096f9c6aed8180140f3d2888ce1180140f3e28888a1180140f7c23388a1180140 else 0xf4f6779999284540b6f5c62959284540b7e5c22959284540b5f5c72159284540b6f5c62159284540b7d5c32159284540b7e5c22159284540b7f1c02159284540d774cb9559284540d776bb9559284540d774ba9559284540f576779559284540f67666955928454097f4cb9559284540b7b4ca5519284540f3b6885519284540f5b6775519284540f6b6665519284540f73655551928454097f4cb54d9284540d7d4ba8cd9284540f3d6888cd9284540f5d6778cd9284540f6d6668cd9284540f756558cd928454097f4ca6e58284540d3f5b9a21828454097f4cb65d8284540d5f5b99dd8284540d6f5b99998284540d775b9955828454097f4ca6e48284540d775b9954828454097f4ca6e57284540d3f5b9a217284540d6f5b999972845409df5c7aed528454097f4ca6e55284540d3f5b9a215284540d5f5b92dd52845409df4cb9dd5284540d5f5b99dd5284540d6f5b99995284540d775b99555284540d3f5b9a2052845409ef6cc6d85284540d6f5986d85284540daf6886d85284540d6f5b99985284540dbb6886d05284540deb6666d05284540d6f5b664c5284540ded5b68cc528454097f4ca6e53284540d3f5b9a213284540d5f5b99dd3284540d6f5b99993284540d775b99553284540b7e5c92e22284540bde5c72e22284540b7e5c92a22284540b7e6cc6622284540b7e4cb6622284540b7e4ca6622284540f3e598a222284540b7e4ca65e2284540f3e68865e2284540f5e5989de2284540f9e6889de2284540f5e67765a2284540f6e59899a2284540fae68899a2284540f6e59799a2284540fce67799a2284540b7e5c92d62284540bfa5c42d62284540b7e5c92962284540bee5c62962284540bfa5c42962284540b7e6cc6562284540b7e4cb6562284540b7e4ca6562284540f3e6886562284540f5e6776562284540f6e6666562284540b7e5c96162284540b7e5c92162284540bde5c72162284540bee5c62162284540bfa5c42162284540bfc5c32162284540bfe1c02162284540f765989562284540fb66889562284540fd66779562284540f765969562284540fe66669562284540f765959562284540bfa6cc5522284540bfa4ca5522284540f7a5985522284540fba6885522284540fda6775522284540fea6665522284540ff26555522284540b7e6cc64e2284540b7e4ca64e2284540f6e66664e2284540f7665564e2284540b7e5c954e2284540ff255454e2284540f7c5988ce2284540fbc6888ce2284540f7c5978ce2284540fdc6778ce2284540f7c5968ce2284540fec6668ce2284540f7c5958ce2284540ff46558ce2284540ff85548ce228454097f4cb6622284540b7e4ca64a2284540f3e68864a2284540f6e66664a2284540f7665564a2284540f7a55464a2284540f7c63364a2284540b7e5c960a2284540) else (if i < 3 then 0xf1f6889dd9584540d6f6bb9999584540f2f6889999584540f4f677999958454097f4ca6e58584540d3f5b9a218584540d5f5b99dd8584540d6f5b999985845409fd6cc6cc8584540d7d5c96cc8584540dfd1c06cc85845409fe6cc6c88584540d7e5c96c8858454097f4ca6e57584540d3f5b9a217584540d6f5b99997584540f6759799a5584540fc767799a5584540b775c92ca558454097f4cb6625584540f376886565584540f676666565584540b775c96165584540d7b4ba6615484540dbb6bba215484540dbb4baa215484540f3b598a215484540f3b68865d5484540ddb6bb9dd5484540ddb4ba9dd5484540f5b5989dd5484540f9b6889dd5484540deb6bb9995484540f6b5989995484540fab6889995484540f6b5979995484540fcb6779995484540f735989555484540fb36889555484540fe3666955548454097f5c82e9938454097f5c52e9938454097f5c22e99384540d3f6bba219384540d3f4baa219384540d5f6bb9dd9384540d5f4ba9dd9384540f1f6889dd9384540d6f6bb9999384540f2f6889999384540f4f6779999384540b6f5c62959384540b5f5c72159384540b6f5c62159384540b7d5c32159384540b7e5c22159384540b7f1c02159384540d776bb9559384540d774ba9559384540f67666955938454097f4ca6e58384540d3f5b9a218384540d5f5b99dd8384540d6f5b9999838454097f4ca6e57384540d3f5b9a217384540f1f68865d7384540d6f5b99997384540f4f59799973845409ef5c62e9538454097f4ca6e5538454097f4cb661538454097f4cb65d5384540d5f5b99dd5384540d6f5b99995384540d775b99555384540df36bb5515384540fb36885515384540fd36775515384540fe36665515384540ff155460d5384540ff15545cd5384540b7d4ca6623384540f3d598a223384540b7d4ca65e3384540f3d68865e3384540f5d5989de3384540f9d6889de3384540f5d67765a3384540f6d59899a3384540fad68899a3384540f6d59799a3384540fcd67799a3384540bed5c62963384540b7d4ca6563384540f3d6886563384540f5d6776563384540f6d6666563384540bdd5c72163384540bed5c62163384540bfc5c22163384540bfd1c02163384540f755969563384540fe56669563384540f755959563384540bf94ca5523384540fb96885523384540fd96775523384540fe96665523384540ff16555523384540d3f5b9a20a284540d775b9954a28454097f5c8aed928454097f5c5aed928454097f6cc2e9928454097f5c82e9928454097f5c52e9928454097f5c32e99284540d3f4cba219284540d3f6bba219284540d3f4baa21928454097f4cba21928454097f4cb61d9284540d5f6bb9dd9284540d5f4ba9dd9284540f1f6889dd9284540d6f6bb9999284540f2f6889999284540 else (if i < 4 then 0x87fcca6e5838454087fcca6e573845408efdc62e9538454087fcca6e55384540a7dcca6623384540a7dcca65e338454087fdc82e9928454087fdc52e9928454087fdc32e99284540c3fcbaa219284540c5fcba9dd9284540c7dcba8cd928454087fcca6e5828454087fcca6e5728454087fcca6e5528454087fcca6e53284540a7ecca6622284540a7ecca65e2284540f1f6889dd9184540b5f5c72159184540b6f5c62159184540b7d5c32159184540b7e5c22159184540b7f1c02159184540f3d6888cd9184540f5d6778cd9184540b6f5c61499184540f3e6888899184540f5e6778899184540f7c6338899184540d3f5b9a218184540d5f5b99dd8184540a7f4ca6498184540d7e5b98898184540d3f5b9a217184540d3f5b9a215184540d5f5b99dd5184540d775b99555184540d7e5b98895184540f3b598a214184540f5b5989dd4184540f9b6889dd4184540dbb6886d54184540ddb6776d54184540bdb5c72154184540beb5c62154184540bf95c32154184540bfa5c22154184540bfb1c02154184540df35b59554184540fb96888cd4184540fd96778cd4184540f3b6886494184540f5b6776494184540beb5c61494184540f7a5988894184540fba6888894184540fda6778894184540dfa5b58894184540ff86338894184540f7a5928894184540d5f5b99dd3184540d3f5b9a212184540d5f5b99dd2184540d7e5b98892184540afd8ca54d3084540ff195454d3084540fbb2885053084540fdb2775053084540ff91535053084540ffa2225053084540dfd2bb4c53084540f7d1984c53084540fbd2884c53084540fdd2774c53084540bfd1c54c53084540ff91544c53084540f7d1924c53084540ffc2224c5308454097f5c5aed988454097f5c2aed988454097f6cc2e9988454097f5c52e9988454097f5c32e9988454097f5c22e99884540baf5c62ea8884540b3f5c92d68884540bbb5c42d68884540b3f5c92ca8884540baf5c62ca88845409ef5c62ea8884540b3f4ca662888454097f5c8aed978454097f6cc2e9978454097f5c82e9978454097f5c52e99784540d776552e9978454097f5c32e9978454097f5c22e99784540d3f4cba219784540d3f6bba219784540d3f4baa21978454097f4cba21978454097f4ca6e58784540d3f5b9a218784540b5f5c92a27784540b5f6cc6627784540b5f4ca6627784540f1f598a227784540b6f6cc6626684540b6f6cc65e6684540f2f68865e6684540b6f5c961e6684540f4f5989de6684540f8f6889de6684540d3f5b9a20a5845409ef6cc6d8a584540d6f5986d8a584540daf6886d8a584540dbb6886d0a58454097f5c82e9958454097f5c32e9958454097f5c22e99584540d3f4cba219584540d3f6bba219584540d3f4baa219584540d5f6bb9dd9584540d5f4ba9dd9584540 else 0x97edc32e99188940b5edc72a19188940d3eccba219188940d3eebba219188940d3ecbaa219188940d5eebb9dd9188940f1ee889dd9188940f2ee889999188940f4ee779999188940b5edc72159188940b6edc62159188940b7cdc32159188940b7e5c12159188940b7e9c02159188940d7ccba8cd9188940f3ce888cd9188940f5ce778cd9188940f6ce668cd91889409eedc6aed818894097ecca6e58188940d3edb9a218188940d5edb99dd8188940d6edb92d981889409eeccb9998188940d6edb999981889409deecc6dc8188940d5edb99dc8188940d5edb76548188940ddae776d08188940ddadb75508188940ddcdb78cc818894097ecca6e5518894097eccb6615188940d3edb9a215188940d5edb99dd5188940d6edb99995188940d3edb9a205188940dbae886d05188940bdadc72a14188940bfa5c12a14188940b7acca6614188940dbaebba214188940f3ad98a214188940ddaebb9dd4188940f5ad989dd4188940f9ae889dd4188940f5ae776594188940f6ad989994188940faae889994188940fcae779994188940dbae886d54188940ddae776d54188940deae666d54188940bdadc72154188940beadc62154188940bf8dc32154188940bfa5c12154188940bfa9c02154188940fb8e888cd4188940fd8e778cd4188940fe8e668cd41889408fecca6dd3188940dfa6bb5053188940fba6885053188940fda6775053188940fea6665053188940ff85635053188940bde9c72a13088940b7e8ca6613088940dbeabba213088940f3e998a213088940ddeabb9dd3088940f5e9989dd3088940deeabb9993088940f6e9989993088940faea889993088940fcea779993088940bfc9c329530889409fe9cb2153088940bde9c72153088940bee9c62153088940bfc9c32153088940bfe1c12153088940fdaa775513088940feaa665513088940bfcacc54d3088940dfcabb54d3088940f7c99854d3088940fdca7754d3088940feca6654d3088940ff48a554d3088940ff498554d3088940ff895454d3088940bfc9c32853088940bde9c72053088940bfc9c32053088940bfc9c31453088940fbaa885053088940fdaa775053088940feaa665053088940ff89535053088940bfcacc4c53088940dfcabb4c53088940f7c9984c53088940fbca884c53088940fdca774c53088940feca664c53088940bfc9c54c53088940ff89544c53088940ffc0a14c53088940ffc1814c53088940ff89414c5308894087fdc52e9988454087fdc32e9988454087fdc22e99884540aafdc62ea88845408efdc62ea888454087fdc82e9978454087fdc52e99784540c77e552e9978454087fdc32e9978454087fdc22e99784540c3fcbaa21978454087fcca6e58784540a5fcca662778454087fcca6e5858454087fcca6e5758454097bdc4aed9384540))) else (if i < 8 then (if i < 6 then 0xde9db6550218cd40df1db5550218cd40d7d9986c0218cd40d7d9956c0218cd40df99546c0218cd4087fdc52e9988894087fdc32e9988894087fdc12e9988894087fcca6e58688940a6fcca662668894087fcca6e5858894087fcca6e56588940a7bcca6615488940a7dcca6623388940b5edc72159288940b6edc62159288940b7cdc32159288940b7e5c12159288940b7e9c02159288940f6ae665519288940f6ce668cd9288940d3edb9a218288940d6edb99998288940d6edb9999528894087fcca6e58188940d5edb7648818894087fcca6e55188940a7bcca6614188940f6ae666494188940ff85325053188940d6edb99992188940a7f8ca6613088940ff195454d3088940f6ea666493088940f7c9536493088940ff49535493088940f7c9924c53088940ff91414c53088940ffc13148530889409deecc6dca88894097edc5aed988894097edc1aed988894097eecc2e9988894097edc52e9988894097edc32e9988894097edc12e99888940b3ecca662888894097eccba219788940b5eecc6627788940f1ed98a22778894097edc82e9968894097edc52e9968894097edc32e99688940d3ecbaa219688940d5eebb9dd968894097ecca6e58688940d5edb99dd8688940b6eecc6626688940b6ecca6626688940f2ee8865e6688940f4ed989de6688940f8ee889de6688940d3edb9a20a588940d6edb9998a588940dbae886d0a588940deae666d0a58894097edc82e9958894097edc32e9958894097edc12e99588940b5edc72a19588940d5eebb9dd9588940d6eebb9999588940d6ecba9999588940f4ee77999958894097ecca6e58588940d3edb9a218588940d5edb99dd8588940d6edb999985889409fcecc6cc8588940d7cdc96cc8588940dfc9c06cc85889409fe6cc6c48588940d7e5c96c48588940dfa5c46c4858894097ecca6e56588940d5edb99dd6588940bdadc72a15488940b7acca6615488940f3ad98a215488940ddaebb9dd5488940f5ad989dd5488940deaebb9995488940f6ad989995488940fcae77999548894097eccb661638894097eccb65d6388940b6ecca6596388940f4ee77659638894097eccb6615388940df2ebb5515388940fd2e775515388940fe2e665515388940ff0d5460d5388940ff0d545cd5388940bdcdc72a23388940b7ccca6623388940f3cd98a223388940f5cd989de3388940b7ccca65a3388940f3ce8865a3388940f5ce7765a3388940f6cd9899a3388940face8899a3388940f6cd9799a3388940fcce7799a3388940b7ccca6563388940f5ce776563388940f6ce666563388940bdcdc72163388940becdc62163388940bfc5c12163388940bfc9c02163388940fd8e775523388940fe8e665523388940d3edb9a20a188940dbae886d0a18894097edc82e9918894097edc52e99188940 else (if i < 7 then 0xc7fcba6159284540c7fcba60d9284540c7fcba54d92845408ffdc32e98284540c7fcba661828454097fccb65d8284540a7fcca65d8284540c7fcba65d8284540c7fcba6558284540cfbcba55182845409dfdc7aed52845408ffdc82e952845408ffdc32e95284540c7fcba6615284540c7fcba64d52845408ffdc82e93284540a7fcca6613284540c7fcba6613284540a7fcca65d3284540c7fcba6553284540cfbcba5513284540c7fcba6622284540c7fcba6562284540cfbcba5522284540c7fcba64e2284540aff8caa213084540aff8ca61d3084540aff8ca6153084540ff598554d3084540aff8ca5493084540ff59535493084540aff8ca889308454096fdc5aed989994096fdc2aed989994096fdc1aed989994096fdc8aed979994096fdc1aed9799940d4fe77aed9599940dcbe77aed5499940d4febb9dd939994096fccb661539994096fccb65d5399940de3ebb5515399940fe1d5460d5399940fe1d545cd539994096fdc8aed929994096fdc5aed929994096fdc1aed929994096fccb61d9299940d4febb9dd929994096fccb54d9299940d4fdb99dd82999409cfdc7aed5299940d4fdb92dd5299940c6fdc92e98199940c6fcba6e58199940c6fcba65d8199940ccfcba9dd8199940d4fdb99dd8199940c6fcba6558199940cebcba5518199940c6fcba64d8199940c6fcba64981999408efcca6e171999408efcca6e1519994096fccb661519994096fccb65d5199940d4fdb99dd519994096fccb6495199940f4bd989dd4199940dcbe776d54199940f4be7764941999408efcca6e13199940d4fdb99dd3199940deb6bb5053199940fcb6775053199940fe953250531999408efcca6e12199940d4fdb99dd2199940dcfabb9dd3099940bedacc54d3099940dedabb54d3099940f6d99854d3099940fe598554d3099940fe995454d3099940f4fa776493099940f6d9536493099940fe59535493099940bed9c31493099940aef8ca6053099940fcba775053099940fe99535053099940bedacc4c53099940dedabb4c53099940f6d9984c53099940fcda774c53099940bed9c54c53099940fe99544c53099940f6d9924c53099940fed1814c53099940fed1314853099940f4de77999928cd40a7dcca6e5828cd40f4de77999918cd409eddc6aed818cd40d6ddb92d9818cd409edccb999818cd409ddecc6dc818cd40d5ddb7654818cd40d5ddb7648818cd4097dccb649518cd40fc9e77999418cd40be9dc6149418cd409bdecc6e0218cd40d3ddc96e0218cd40d3ddb8660218cd40d5dd986dc218cd40d6dd986d8218cd409f5ecc6d4218cd40d75dc96d4218cd40d75d986d4218cd40df1dc46d4218cd40d3ddb8654218cd40d5ddb7654218cd40d6ddb6654218cd40d75db5654218cd40db9db8550218cd40dd9db7550218cd40 else 0xc94b142c3cb0a2c14b002becaea2b64ac82adcaa62a54a8429fca6e29a4a64294ca4228c4a20286ca0a27e49e8278c9de27349c8270c9b22684990262c97a25d497025ac966258495c255c9522534948250c93e24e493424bc92a2494920246c916244490023ec8f623948e0236c8d623448cc231c8c222f48b822cc8a2227488c221c88221f487821cc86e21a4864214c84220c4820203c80a20148001fec7f61fc47ec1f9c7e21f747d81f4c7ce1f247b81e9c7a21e747981e4c7821df476c1d6c7561d447401cec72a1c647141c0c6f21b846d01afc6ae1a7468c19ec66a1994654190c632188461017fc5fa17a45d8171c5c216f45b8169c5a2164458015bc55e1534530147c50e13f44f8139c4d613144b4128c492123447c11ac45a112444410fc43a10d4430107c40e10244040ffc3fa0fa43d80f1c3b60e943940ddc3720d843380c9c3220c7430c0c1c3020bf42f80bcc2e20b442c00abc2920a34270097c24208c422c086c20a08141f407bc1ea07641c8070c1be06b41a8068c192060417c05dc1720584150052c14604d411803ec0de03040a401ec05200a400097fdc5aed98889408ffdc32ea88889408ffdc32e98588940a7fcca6e585889408ffdc82e965889408ffdc32e965889408ffcca6e165889408ffccaaed83889408ffecc2e963889408ffdc82e96388940c7fcba6616388940c7fcba6556388940cfbcba55163889408ffdc82e953889408ffcca6e153889408ffcca6d95388940c7fcba6595388940af7cca6155388940ff1d5460d5388940a7fccaa219188940b5fdc72159188940b6fdc62159188940b7ddc32159188940b7edc22159188940b7f9c02159188940a7fcca58d9188940a7fcca54d9188940c7fcba6558188940cfbcba551818894097fccb6615188940afbccaa214188940bdbdc72154188940bebdc62154188940bf9dc32154188940bfadc22154188940bfb9c02154188940afbcca58d4188940afbcca54d4188940afdcca58d3188940aff8ca6153088940ff995454d3088940aff8ca6053088940ff99535053088940ff99544c5308894097fdc8aed9784540c7fcba2e1978454097fccba219784540a7fccaa219784540c7fcbaa2197845408ffdc32e98784540c7fcba6618784540a7fccaa219584540a7fcca61d95845408ffdc32e98584540a7fcca6e58584540a7fcca65d8584540afbccaa215484540afbcca61d5484540a7fccaa219384540a7fcca6e58384540a7fcca65d83845408ffdc82e97384540a7fcca6617384540cdfcba61d7384540c7fcba6557384540cfbcba55173845408ffdc82e95384540a7fcca6e5538454097fccb661538454097fccb65d5384540a7fcca65d5384540c7fcba65d5384540ff1d5460d5384540ff1d545cd5384540c7fcbaa219284540c7fcba61d9284540)) else (if i < 9 then 0xa96aa46a8ca9eea6aa996a60a96ea4aa8e6a28a85ea06a7a69d8a71e9b6a696994a63e97ea58695ca52e93aa4a6918a41e902a3c68eca36e8caa3168c0a2be89ea23687ca1ae866a156844a0ce822a07680c9fee7ea9f667c89ede7a69e567849dce7629d467409cbe7069ba66cc9a8e69299a6640988e61298065f0977e5ce96f65ac969e5969616574955e54694a650093be4de93664bc91ee46a913643c90ae3f68f963e08f3e3be8eb639c8e2e37a8dd63648d7e35a8d263388c9e3228c7630c8c1e3028bf62f88bce2ee8ba62e48b4e2c28ac62a08a3e27e89e627489be26a8966254893e24a8916234888e21e88361fc87ae1e687561c486ce1ae8676198861e1768596154850e132848611c845e11284060f083ae0e683860dc835e0d283360c8830e0be82e60b482be0aa82960a0826e08a81e6068818e0528106030807e00e80260047ffdffa7fd5ff07fadfda7f25fb87e9df967e45f8c7e1df827dc5f607d3df3e7cb5f287c5df127c35efc7badeda7b55ec47a9dea27a75e987a4de8279c5e60793de4a78e5e34788de127805df0777ddce76f5dac766dd8a75e5d68755dd4674d5d24744dd0273f5cf873cdcee7375ccc72edcb67295ca0723dc8a71e5c68715dc4670d5c24704dc026fc5be06f3dbca6ee5ba86e8db9e6e05b706d7db4e6cf5b2c6c6db0a6be5ae86b5dad26b05aa46a7da9a6a55a8469cda566915a34685d9fa67759cc66bd986657594c648d90663d58d8631d8aa6235864611d82a60057e45f4d7c25e657705d1d7365c957145bdd6da5af56a05a3d67e59e5668595d64658d5624587d61a582560457fd5fa57a55d856ed5aa56955a0566d596564558055bd55e553553c54ad51a54254f8539d4d653154b4528d4925205470517d44e50f542c506d416504540c501d3ea4ea53984e1d3764d953604d3d34a4d153344c8d3124c352fc4bad2da4b252b84a9d2a24a7528c4a1d28249c526c496d24a48e5228488d21248051fc47dd1f247851d046fd1ba46d51b046ad1a6468519c462d186460517c45dd166458515044fd12e4475118444d10e442510443fd0fa43d50f0437d0da43550d0432d0ba42a50a4424d08241f507841cd06e41a5058414d04e412503840cd02e407500c401d0023fc4fe03f6cfca3ee4fa83e5cf863dd4f643d4cf423cc4f2c3c9cf223c74f183c4cf0e3c24ef83b9ced63b14eb43a8ce9e3a64e943a0ce7e39e4e74398ce5e3934e4838dce263854e0437ccdee37a4de4377cdda3754dd036fcdae36a4da4367cd9a3654d90362cd863604d7c35dcd7235b4d68358cd5e3564d54353cd3e34e4d3434bcd2a3464d0833dcce63384cdc332ccba32a4c9831ecc6a3194c60316cc4a30e4c3430bcc2a3094c20306cc0a2fe4be82f5cbc62ed4ba42e7cb9a2e54b902e2cb7a2da4b582d1cb362 else (if i < 10 then 0xe80040d816009460be0bc04a30020270341d8006c003600100501f100280f8801407c400a03e2d000e80041c001e000f000780028381003800200014d82a6c1db6003129b0400000080414020e800640032001c820e410720839041c820a80074003a0018020c010720828041d000e80054003a00140208000000f81a0bb7c0d7b21104094ba1c1d0e0e00074382092008018001c000e00041c001e000d4106a0835041a8208006001002a0820e000d4106a0835041054106a08200038002d04152908000000003290800006410412001a820d4106a0820000000000068208000070007c6020e000b4104000001c0010000d0410014a4325210014a43a0010294874002a521d000894874003a001a820d4106a08200000000015041e000f00074683c001d2008000682080006820824382050e0d4105a083c001e000800000000e000890840000000000000000000000018c0400002c0036001b000d800400e000f0006a0835041145a821541040007000780020000000541074683c001e000f00074682752100000070005a08325219290c94844a43c001000000341054383c00150e0a87054382d04103410400e000b41055143c00100a4855142a8a1003800200480064003c001034104000000000000000000000000006001000c002000000000000180040630100000000003290d8006c0036001b000800000000000000000e001e0008000000604061c13450800a1c10287074382050e0e87074383e301a820f8c07c603e301f180f8c041a1c1b180e87074383a1c1d0e08048c2d04112108000c00083000321c190e0c87064382242a402c000f8c070002050e0e87074383a1c1d0e0e87040a1c1e000f00078002000000e000f0004000024a43c001e000f0007d143c001137e00103800229224360c3b060801c0010000005af878003c00190e089bf00080293c00294508a2f9b0b80020f360fa2840a8a1002c38320c1000c182005a284ca420000d14261c10004402a34246251a123128d0918946848c4a342462f45f185381fa2f9b78c0fd17cdbc607e8be6de303ddbf752dcd7724dc1f6eadb376b0da4f676d96763cd8af60ed7c75d4d6df5a6d657578d56f53ed487504d39f4cad2b7490d1ff456d117434d08f412d0073f0cf4f3c2cec7394cddf366cd57344cc9f316cbe72dccaff2a2ca47274c95f23ac8a720cc7ef1dec7071b0c64f176c567154c4df126c4270f8c36f0bec287084c1ff06ec147034c05effabf76fc0bebef92bdd6f58bceef1ebc06ee4bb1eeaaba36e70b94ee36b866dfcb7aedceb6c6da0b60ed72b556d44b4ced22b416cf4b38ecd2b306cb0b27ec9ab256c90b1fec6eb1a6c58b11ec36b096c14b00ebfeafb6bdcaf2ebbaaea6b98ae4eb8eadf6b78ad9eb62ad46b40acbeb12ac06afcab7eaceaaf6aacaa6e else 0x602b10348098804c0044d0c100101e10218098801c004400e0022014001100080f0801c004400e0022b1a080d0008801c004400e00220070011034841c8200e0022c1cc06160e6030b073018400e80c241c02f10038008801c004400e0022b00088c8030168c02c3a341d1a0e8d0402c2a34103d00b1005840f420d3a1c2e86032100f840c82038100300213410400c00840060022005003100d0008887020060022003001100d00089a08200a0062d00080ce800800c0044d041005003100d0008800c0944000104c1580040680044d04103502e10018010801400c4006002200908401400c400a83c200500310028018801400c4034002221c08018010801400c40060022003001100cd800b80b8684034002201a00110018008800c0044034002200500310018008801400c40060022b0008018008800c004560010030011687074380045a1c1e180e870407f8605a1c1e000f00078003c001e0008000e000f00041c0011210f00078003c001e000838002a1c1e000f00042dc200610010dc20b0008007c203e101f088cf000b80020119e001281064003204101f08000e00080f840000918448438001c000c870448548058001c000e87074383800100918448648040c000e000448438001c0008001c20e000f000400e000f00048843a001d1a0838002b041e000f00041c001e000b8d078003c001e000ac106c6836341b1a0d8d066083304131a080702f0390c03c0a0401603e202a6c80281e80040ddb200a060c8d9005036c81231680078003c001e000f0004ea4325210287054382a8a100701f17000401c07c446ed0c24639020f000402420d22ec541aeb81210692c8704485480580011210890f6a8208349300020e000f0006a18350c1a860801841c001002a18350c1a860800d0c100000000009000c8006a18350c10030d430400001a18200001c001f180838002e3416860834682d0c15290814a4205290e80074803c0016860c8707800200038002242100000000000000000000018c06c0036001048004504350c1a860d430400000000700078003c001d1a09d484000038002d0c15360a9b07800201370801c0019000d8d040d0c1119e00100000480074683a341686081408205020e80064082a041d000e8006400320019000e8d074683a341d1a0a8d074003a001d00080f84000004843e3016860814382050e0814383a1c1d0e0f8c07c603e301f180f8c07c603a1c1d0e08048c22421000485a1858001c00094107c6038001f180e87074383a1c1c0008048c2243240200018001c0008909410b0003800105e025102f01a080280d0550410e001f101481e0128c17c0f00946e00105f03c034180501a0ac00200a03e2d00080280f8801407c40f608602e300501f100280f883d40d407c600a03e2d00))))
def lvl10 : Packing := (972,5,7,0,0,14,0,words10)
def idx11 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0xa0000000009147c81fc0000181640000186899029c027270631000d00000405520309811c4009f0233000018148700bdc634b02d9c26850b9a40ca50d5dc0e140e1c0000303b043c100001c0cf7b02fc131d0cd001be20c4806a2a0c1f825340256018540c5405152034d01049173445e78048dc5d800be10146b06d500fba0c1b82ef00003c39a00003804900e1280285508f4031a009a835000001039900003c3c47051000000000301fe2124c0000b02c400000000180bb000018558a0d7b01abf09448341a0deb8688b652f82f241171401f80d6640f560821c32a000000000b0e540000a0aa4000060d2b856900000c128c17839d4f00003867df083b807bb051c8354d0dac82ba10e0c000020c84822800003c3bc30b6e06b3c0d1440d700003073106cd8000000000000050db0c1d300001c0b2d653400a6605fa022b000000000b1a56805e000004183504d580ff20383c21c10964c2b700000036a3028f8565d060003a4502aa41d13187841022105c02ebf045600bdb076c83c0c0887c0ab1081b435d00e404015f0b2985ca000ba8187220280000e078dc1b3c1eb404e707325c3b60062c004ca0491d895901f90122f01dc83a3a1007011eb0799c09810cb1061630cf840e64044c0363e7cd9441310277c31f211db40b780d92821e1034a80ad2026840046a063c1a670c6ec281d0aac0227d13be035c70b19412a70e7dc24bf001fc1ef70d4c451db01ae437050779c27d41ee1813340281437300000c349209cc823130eb544a1b1945826c60e0b01fb70480824d60a52034d203f9881210284411960c9e41c7f08c00000c138c6012d0905073400001989240bf842ac0750901a491472100b60735426d90d38010590e844045203bb8518a01f100c5508bb0302000000275004dc03207199645521096b01e9d03c258405203ac3bf20038000000000000000002c0f4508278392d042800000704000b04052f3f020900022a01000e01000d0c0005293002100b0006181a0907700112004916050e133f4f2c06000d333c01ae001e0105056202195f01015c0236030903013a01030142393300000301042c16091c2f0205226e09480a0b0e00050504047e030000137b0626070a031a08030007230200010030460a063014011f1a000c1965120f2b06040b2c000000022c004b240403000b081e270103050106120c00001c2d51000d0c1101400902364305280815001532051401470819041101250007001f0101030f0009040e0019080a1206000000010006010805031b01010002042703340009060013110207140013030b0d08082b0302070000010b001e01020f020212060f13000118030830080302062040010106161012060b0204000a0302009200000601120205140401000b0002061b00025b03000406000a3a0b031100 else 0x2301e46037ec18230cdf8328002c340e99065a41dc21ad000007012c072ad0d84858320e7405cba0a3381ffc161241b06005dc2d64075183b880f2a42f4309830056511e4000000df4c22660a1e42900046d45c020b9ec224d097d402a9079c0000406560042f05d18531908528204011498332c06ed419d71120001be185e193500001008e713c3502ef06384298000020416d03d900dde02228193b0a4f426590d19009f41179c6cf90017857c50eedc0f2a705102ee0000d808ae80340000011e9428840a5543b2016a7c29e80eb280320000382c040beec0251082cc0c0104630082e03e4801200003c0a2e0e380000d0dd0000080293d87e00000080f9008c0000218fd41c461397829b00003438100000012de0eab8329c122640539037302fc00002c2aab01da42c1d008386277004000006054540658011dc06da085840d50000205640000303a00000144d69150783012144c434b000000000f0b3300d970d88c1c3d0330003e0000183059068101dd504694292b062bc0f3e043ec15e80988000051575c17660b7f801ea128f036630bc1c28d60596c3bed15e8026400000018fa0b14000040769c56b00001470f00dd4868f000000186b065c442d00000000050b440000d1a434313d08e2069e118e2401861044000000000000000000805b0000102f57014400000000105172092a994900000000000000000050d0cc0f80000000000000000000000182c7615bc0000d0e44427800001820a20c6a8725916d941aff00040000004e2024800000000000003865da097542b810ed3836d0000341d8513cec3474650743440000300026084fc4ea019f3c2f35043781d2b0b89069200e7842ec0000000009056da01020717835f8096c4203e1a2d43a600000c163c039400001038a826f70df90254911844325d084180e40001a4258008f442fac05fec0d090a3904bb90552433921654c284e053d0160805dec28a105f0415a00001400fcb0be200fe1916830e80dc64239000d2c22d46321429cd04bdc0d410f0d41f800001426330705c1e060c25806cb0320466a619c0c36ec19540000014a9406e50cf500f150e5a474e60b9181f430139c17901424c1f2c053b0220b08161894a090ec1d60000000001113c0000f631b80afe08d7810730d4b4525b0207047bd02e5424500002409c700b183b300000000000001c0300000246c7480331948806b9811650d0000008202fc2bc10ebc000010f20000000001c0c3a0cba43b0c017c000080bc645db6205646aad06de02e3813b582f9a06e681b431a9d0060a08bfc1737004600bf204b9c261a40028289000024141f01880000a012b8202a049840d8000000000000014433c15fde8253068dc4ad40032c201307940000720040000b057000008149881f170a97819e00001412c00002427) else (if i < 3 then 0x8380c7783cb40c5bc5c110026c18dc0175c127c03128050008d8834c30b4bc35800002c18851450c54450a3c0000e019c0000c175c0000000000000107ad80e700002445b00801c32d000000000d004c00005026e40c9510b8000001128e57000003000b6134e061d0000144d05014ac23a10a5b425c31b380000d64f30246000000000215b4830d20dbe81a8d7534000000002015600000054500b614467604f3c1b800001405a3069d80a980e4cc561306e884cb90d6d410e813d3401670199022c104fa03b1c0720c483b000204238097b839c01a50413660526433100001c1896044282a000001843ec0f240398d0738c2ff80b5d441c00e9680eb2060681a100003426ee07b40000b0200c5a8200d7e011d13dac3030013c833570576053df18b202706057c005c00001c475e0b0c4167b0874000051c8383c6302668178b0c02d02f3118b02a11127c8256280580000f05f40114b02b00000d06420096505ebc14580100000010d9701f38a0380000e0896817590b38000000002038fe031cc24c71932c71a30c10000000002011f605bb0506507840000a07b905ddb02500000a0718040d000000000910f000000000198937032cc2cf5083005285065241f79042c0000d021ac07a0000041c200003c31970731c1fa0000081bfb123c82ae00000000000003c1fde03bc00000000000000000085049015c000060ac3014070379847d0000002e8316ec000000000000050b240000b0418000030eae86c4408a7c19ae06640000b19af4360f1377838ce05b5c2bba05a9c142815350286000678593400fc42cb00003804d20bb682a30000141ca00000000020dff838010cafc024b5004000000002c52931772c69b205ef836780c90000020ee7824761cd9823b505adc27c00002c05940242080d915a88022109ed42a7602cc02e920236c40aa11a601d000000c014314800000603680000603de4041d04c90322a08d3c172204c08158000000000c0955020fb0e2682fd20420425070d6a835170407003bd05674567604e684f2f0a758046674f240b5805be405831ad8e00ed111485d4607b3032f708ff84ce4140241b61409cc4a0000000000004fe00210000341a90135100c650231027e5164240b8005a7c09250a0f803dc07abc2dad05a18654c0af5030cd0925049780a88c3ae70ac400001024e00296049540c120c7082a6501a502d53193c000000000000000002c2ea518df00dbc0a66c678c0d2042d9d654802b60000084c6a0121c68451c404078804ef031020de5006400000000000000c13dd1c600000d073e4033b07d7007d0000000003090a819f10ab79d3561787c24e00001826a000018336c0cecd81261a1d432300002dd44f07e4000060ace833800b21c5a6404028252c0862001a306b0000070b86c16231ceac04340c else 0xe02fb8412d00de82c210c5f40a8f103e00cda156d452cb088f40d650e5c000000002807030338000010e358291b04ac0000b0c3c000000002811d906a8c1cb80c994008d077c82cd3029745bc00000000010e9c0000a04d1046a71a34857980a5dc502602d30597000000000304eb038802044c3940000000002086dc49e00002a01400000833000001c16100003c3c70000000000000200fc080541940a1a2bd94ad09c70097e0a0300756055718cc30dec82e0212140000701e7009190da38219e16d70038f6072459c51b0e4222c14218157a08f9822ae0345009e007a04369904495947a14d3c33c806c4c191e075c0000209dfcd70e066d4240d09e705d570ad780fae0e2ac31e519eb02f7809fdc0ed000004117f146442b90000003330000102de000004087d0f08c55960e2f4044e1057c31850a93c285c0b118652e13dc00005022f600bf18e743a900002c14a0195b40e30000101bd40e88008f0144a4342c200d0459806b4000050028c4bde19e4c1b291a44c17040d3d02d4a02ba8355407008063000028152b01524267e05c400000000359c2b00ae0074500f082a8d093e42af0000241f680765c28b90acb0211409ad458dd0537c21a000000000302138085475018686000020068b08c902b49095c000000000c29fb03ab855a80540c06ab0ef501a2a1a1418c7f040c85236091000e8f0b94000010cff859b1194c0000a08de818400003421fb0eddc1219059800000000000000000202dc00000000000001435621d14000000000000000001038630431dc3d8078a437290c280000a06f00000d0b400000b64da0663410f443b500000000030c44053290b4c846c81a9483142050d83c5000000000664d0058e00000c49a0000000610000240bc00002414c10e17064000002c11156dc4803a000025814c1ce081d580a0ac16cf0426c2be415b083a8206700000e0663437610c2e057d604a4000080b75c1920000101f060afc0000509d8c6c9f01c70633b02250527d107c000010a6845d651478c378700748072a11f14377d08540000a107b423c917b400004754cc33a501bc002d2135f85a700002c07f101cc0000700d941a50052d00394054f421200001c20d5007243ba9081e0217709a680ba503f582f6b10aac27400003994cf0725426600003839bf13660560b146c0000f14dbc37c1146a40))
def words9 (i : Nat) : Nat := 0x1d000801d0e08380010001c0008000000000038001000000001e000f8002007dfb726fed6461d8d653d14845c340be3bb936b431a8a623a11e9c19970e05028049bf758caa219784540937eeb1954432b08a812ebdd632a88552115024dfbac65510c9c22a051bf758ba65d5384540977ceb1954426108a8154bdd4aee7764e665026db1b8cc2a6984cca06f86b315454d3099940df496628298a6133281fc9277505314c2665026f91b8cc2a698444a06fc2b315454d3088940fe853baa8a9a6111281fe0a66551534c2225037f0598a0a6298444a07ee0a21414c53088940fec13ba8298a6111281fe8266505314c222502ab6ba95dceec9c22a055ad752bb99993845409be86e330a9a6108a81bf12cc551534c211503f62510aa2a698422a07f449dd5454d3084540ff09332a8a9a6108a81ff015454e224c211502adb3ad5dc66c0c00a055ba75abb8898180140f9b0c12a4c0aa300281f3c1824c9814c6005026be3af662a508c00a07dd09563388a1180140
def lvl9 : Packing := (33,6,7,0,0,8,0,words9)
def idx10 (i : Nat) : Nat := 0x358180b70808804a6c4080d8039401e13000495a83a011004d05c001e0670d481cc2bc85d0cf9275832487064a00414000000200f40ae50642093c000000009003c03d416fe60003c39d8d0023853004218000482000061fb00b934000000706c904800816dc981860034
def newLevels : Nat → Packing
  | 13 => lvl13
  | 12 => lvl12
  | 11 => lvl11
  | 10 => lvl10
  | 9 => lvl9
  | _ => emptyPacking
def newIndex : Nat → Nat → Option (Nat × Nat)
  | 14 => lookupWord 19 53 5 13 5 4 (idx14)
  | 13 => lookupWord 61 275 8 16 8 4 (idx13)
  | 12 => lookupWord 535 2610 8 19 11 4 (idx12)
  | 11 => lookupWord 326 1602 8 18 10 4 (idx11)
  | 10 => lookupWord 14 61 5 13 6 3 (idx10)
  | _ => fun _ => none
def newForest : Forest := ⟨511,13,fun j => deadsamples[j]?.getD (0,0),deadcolumns,#[[],[118,130,81],[100,131,82,16],[118,133,100,131,50,33,16],[116,83,32],[118,116,83,130,49,32],[118,133,33,48],[82,129,48],[118,133,116,83,82,81,80],[116,50,129,80],[100,49,128],[118,100,83,130,81,128]],newLevels,newIndex⟩
set_option maxHeartbeats 0 in
theorem geometry : graphValid newForest (boundsBefore known383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=5) ?_⟩,listPieces_all (d:=3) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel


set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check13_0 : block newForest 13 0 3 = true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check13_3 : block newForest 13 3 10 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check13_13 : block newForest 13 13 7 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all13 : block newForest 13 0 20 = true := (@block_merge newForest 13 0 3 17 check13_0 (@block_merge newForest 13 3 10 7 check13_3 check13_13))
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check12_0 : block newForest 12 0 3 = true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check12_3 : block newForest 12 3 24 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check12_27 : block newForest 12 27 24 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check12_51 : block newForest 12 51 2 = true := by
  decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check12_53 : block newForest 12 53 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check12_77 : block newForest 12 77 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check12_101 : block newForest 12 101 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check12_125 : block newForest 12 125 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check12_149 : block newForest 12 149 6 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check12_155 : block newForest 12 155 24 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check12_179 : block newForest 12 179 5 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all12 : block newForest 12 0 184 = true := (@block_merge newForest 12 0 77 107 (@block_merge newForest 12 0 27 50 (@block_merge newForest 12 0 3 24 check12_0 check12_3) (@block_merge newForest 12 27 24 26 check12_27 (@block_merge newForest 12 51 2 24 check12_51 check12_53))) (@block_merge newForest 12 77 72 35 (@block_merge newForest 12 77 24 48 check12_77 (@block_merge newForest 12 101 24 24 check12_101 check12_125)) (@block_merge newForest 12 149 6 29 check12_149 (@block_merge newForest 12 155 24 5 check12_155 check12_179))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_0 : block newForest 11 0 3 = true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_3 : block newForest 11 3 24 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_27 : block newForest 11 27 24 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_51 : block newForest 11 51 24 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_75 : block newForest 11 75 24 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_99 : block newForest 11 99 24 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_123 : block newForest 11 123 24 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_147 : block newForest 11 147 24 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_171 : block newForest 11 171 24 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_195 : block newForest 11 195 24 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_219 : block newForest 11 219 24 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_243 : block newForest 11 243 24 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_267 : block newForest 11 267 24 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_291 : block newForest 11 291 8 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_299 : block newForest 11 299 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_323 : block newForest 11 323 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_347 : block newForest 11 347 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_371 : block newForest 11 371 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_395 : block newForest 11 395 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_419 : block newForest 11 419 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_443 : block newForest 11 443 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_467 : block newForest 11 467 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_491 : block newForest 11 491 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_515 : block newForest 11 515 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_539 : block newForest 11 539 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_563 : block newForest 11 563 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_587 : block newForest 11 587 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_611 : block newForest 11 611 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_635 : block newForest 11 635 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_659 : block newForest 11 659 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_683 : block newForest 11 683 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_707 : block newForest 11 707 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_731 : block newForest 11 731 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_755 : block newForest 11 755 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_779 : block newForest 11 779 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_803 : block newForest 11 803 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_827 : block newForest 11 827 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_851 : block newForest 11 851 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_875 : block newForest 11 875 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_899 : block newForest 11 899 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_923 : block newForest 11 923 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_947 : block newForest 11 947 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_971 : block newForest 11 971 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_995 : block newForest 11 995 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_1019 : block newForest 11 1019 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_1043 : block newForest 11 1043 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_1067 : block newForest 11 1067 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_1091 : block newForest 11 1091 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_1115 : block newForest 11 1115 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_1139 : block newForest 11 1139 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_1163 : block newForest 11 1163 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_1187 : block newForest 11 1187 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_1211 : block newForest 11 1211 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_1235 : block newForest 11 1235 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_1259 : block newForest 11 1259 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_1283 : block newForest 11 1283 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_1307 : block newForest 11 1307 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_1331 : block newForest 11 1331 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_1355 : block newForest 11 1355 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_1379 : block newForest 11 1379 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_1403 : block newForest 11 1403 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_1427 : block newForest 11 1427 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_1451 : block newForest 11 1451 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_1475 : block newForest 11 1475 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_1499 : block newForest 11 1499 8 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_1507 : block newForest 11 1507 24 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_1531 : block newForest 11 1531 24 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_1555 : block newForest 11 1555 24 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_1579 : block newForest 11 1579 24 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_1603 : block newForest 11 1603 24 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_1627 : block newForest 11 1627 24 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_1651 : block newForest 11 1651 24 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check11_1675 : block newForest 11 1675 13 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all11 : block newForest 11 0 1688 = true := (@block_merge newForest 11 0 827 861 (@block_merge newForest 11 0 395 432 (@block_merge newForest 11 0 195 200 (@block_merge newForest 11 0 75 120 (@block_merge newForest 11 0 27 48 (@block_merge newForest 11 0 3 24 check11_0 check11_3) (@block_merge newForest 11 27 24 24 check11_27 check11_51)) (@block_merge newForest 11 75 48 72 (@block_merge newForest 11 75 24 24 check11_75 check11_99) (@block_merge newForest 11 123 24 48 check11_123 (@block_merge newForest 11 147 24 24 check11_147 check11_171)))) (@block_merge newForest 11 195 96 104 (@block_merge newForest 11 195 48 48 (@block_merge newForest 11 195 24 24 check11_195 check11_219) (@block_merge newForest 11 243 24 24 check11_243 check11_267)) (@block_merge newForest 11 291 32 72 (@block_merge newForest 11 291 8 24 check11_291 check11_299) (@block_merge newForest 11 323 24 48 check11_323 (@block_merge newForest 11 347 24 24 check11_347 check11_371))))) (@block_merge newForest 11 395 216 216 (@block_merge newForest 11 395 96 120 (@block_merge newForest 11 395 48 48 (@block_merge newForest 11 395 24 24 check11_395 check11_419) (@block_merge newForest 11 443 24 24 check11_443 check11_467)) (@block_merge newForest 11 491 48 72 (@block_merge newForest 11 491 24 24 check11_491 check11_515) (@block_merge newForest 11 539 24 48 check11_539 (@block_merge newForest 11 563 24 24 check11_563 check11_587)))) (@block_merge newForest 11 611 96 120 (@block_merge newForest 11 611 48 48 (@block_merge newForest 11 611 24 24 check11_611 check11_635) (@block_merge newForest 11 659 24 24 check11_659 check11_683)) (@block_merge newForest 11 707 48 72 (@block_merge newForest 11 707 24 24 check11_707 check11_731) (@block_merge newForest 11 755 24 48 check11_755 (@block_merge newForest 11 779 24 24 check11_779 check11_803)))))) (@block_merge newForest 11 827 432 429 (@block_merge newForest 11 827 216 216 (@block_merge newForest 11 827 96 120 (@block_merge newForest 11 827 48 48 (@block_merge newForest 11 827 24 24 check11_827 check11_851) (@block_merge newForest 11 875 24 24 check11_875 check11_899)) (@block_merge newForest 11 923 48 72 (@block_merge newForest 11 923 24 24 check11_923 check11_947) (@block_merge newForest 11 971 24 48 check11_971 (@block_merge newForest 11 995 24 24 check11_995 check11_1019)))) (@block_merge newForest 11 1043 96 120 (@block_merge newForest 11 1043 48 48 (@block_merge newForest 11 1043 24 24 check11_1043 check11_1067) (@block_merge newForest 11 1091 24 24 check11_1091 check11_1115)) (@block_merge newForest 11 1139 48 72 (@block_merge newForest 11 1139 24 24 check11_1139 check11_1163) (@block_merge newForest 11 1187 24 48 check11_1187 (@block_merge newForest 11 1211 24 24 check11_1211 check11_1235))))) (@block_merge newForest 11 1259 216 213 (@block_merge newForest 11 1259 96 120 (@block_merge newForest 11 1259 48 48 (@block_merge newForest 11 1259 24 24 check11_1259 check11_1283) (@block_merge newForest 11 1307 24 24 check11_1307 check11_1331)) (@block_merge newForest 11 1355 48 72 (@block_merge newForest 11 1355 24 24 check11_1355 check11_1379) (@block_merge newForest 11 1403 24 48 check11_1403 (@block_merge newForest 11 1427 24 24 check11_1427 check11_1451)))) (@block_merge newForest 11 1475 104 109 (@block_merge newForest 11 1475 32 72 (@block_merge newForest 11 1475 24 8 check11_1475 check11_1499) (@block_merge newForest 11 1507 24 48 check11_1507 (@block_merge newForest 11 1531 24 24 check11_1531 check11_1555))) (@block_merge newForest 11 1579 48 61 (@block_merge newForest 11 1579 24 24 check11_1579 check11_1603) (@block_merge newForest 11 1627 24 37 check11_1627 (@block_merge newForest 11 1651 24 13 check11_1651 check11_1675)))))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check10_0 : block newForest 10 0 10 = true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check10_10 : block newForest 10 10 24 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check10_34 : block newForest 10 34 24 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check10_58 : block newForest 10 58 24 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check10_82 : block newForest 10 82 24 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check10_106 : block newForest 10 106 24 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check10_130 : block newForest 10 130 24 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check10_154 : block newForest 10 154 24 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check10_178 : block newForest 10 178 24 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check10_202 : block newForest 10 202 24 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check10_226 : block newForest 10 226 24 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check10_250 : block newForest 10 250 24 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check10_274 : block newForest 10 274 24 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check10_298 : block newForest 10 298 24 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check10_322 : block newForest 10 322 24 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check10_346 : block newForest 10 346 24 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check10_370 : block newForest 10 370 24 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check10_394 : block newForest 10 394 24 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check10_418 : block newForest 10 418 24 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check10_442 : block newForest 10 442 24 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check10_466 : block newForest 10 466 24 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check10_490 : block newForest 10 490 24 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check10_514 : block newForest 10 514 24 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check10_538 : block newForest 10 538 24 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check10_562 : block newForest 10 562 24 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check10_586 : block newForest 10 586 24 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check10_610 : block newForest 10 610 24 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check10_634 : block newForest 10 634 24 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check10_658 : block newForest 10 658 24 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check10_682 : block newForest 10 682 24 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check10_706 : block newForest 10 706 24 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check10_730 : block newForest 10 730 24 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check10_754 : block newForest 10 754 24 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check10_778 : block newForest 10 778 24 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check10_802 : block newForest 10 802 24 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check10_826 : block newForest 10 826 24 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check10_850 : block newForest 10 850 14 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check10_864 : block newForest 10 864 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check10_888 : block newForest 10 888 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check10_912 : block newForest 10 912 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check10_936 : block newForest 10 936 24 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check10_960 : block newForest 10 960 12 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all10 : block newForest 10 0 972 = true := (@block_merge newForest 10 0 490 482 (@block_merge newForest 10 0 226 264 (@block_merge newForest 10 0 106 120 (@block_merge newForest 10 0 34 72 (@block_merge newForest 10 0 10 24 check10_0 check10_10) (@block_merge newForest 10 34 24 48 check10_34 (@block_merge newForest 10 58 24 24 check10_58 check10_82))) (@block_merge newForest 10 106 48 72 (@block_merge newForest 10 106 24 24 check10_106 check10_130) (@block_merge newForest 10 154 24 48 check10_154 (@block_merge newForest 10 178 24 24 check10_178 check10_202)))) (@block_merge newForest 10 226 120 144 (@block_merge newForest 10 226 48 72 (@block_merge newForest 10 226 24 24 check10_226 check10_250) (@block_merge newForest 10 274 24 48 check10_274 (@block_merge newForest 10 298 24 24 check10_298 check10_322))) (@block_merge newForest 10 346 72 72 (@block_merge newForest 10 346 24 48 check10_346 (@block_merge newForest 10 370 24 24 check10_370 check10_394)) (@block_merge newForest 10 418 24 48 check10_418 (@block_merge newForest 10 442 24 24 check10_442 check10_466))))) (@block_merge newForest 10 490 240 242 (@block_merge newForest 10 490 120 120 (@block_merge newForest 10 490 48 72 (@block_merge newForest 10 490 24 24 check10_490 check10_514) (@block_merge newForest 10 538 24 48 check10_538 (@block_merge newForest 10 562 24 24 check10_562 check10_586))) (@block_merge newForest 10 610 48 72 (@block_merge newForest 10 610 24 24 check10_610 check10_634) (@block_merge newForest 10 658 24 48 check10_658 (@block_merge newForest 10 682 24 24 check10_682 check10_706)))) (@block_merge newForest 10 730 120 122 (@block_merge newForest 10 730 48 72 (@block_merge newForest 10 730 24 24 check10_730 check10_754) (@block_merge newForest 10 778 24 48 check10_778 (@block_merge newForest 10 802 24 24 check10_802 check10_826))) (@block_merge newForest 10 850 62 60 (@block_merge newForest 10 850 14 48 check10_850 (@block_merge newForest 10 864 24 24 check10_864 check10_888)) (@block_merge newForest 10 912 24 36 check10_912 (@block_merge newForest 10 936 24 12 check10_936 check10_960))))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check9_0 : block newForest 9 0 24 = true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check9_24 : block newForest 9 24 3 = true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem check9_27 : block newForest 9 27 6 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all9 : block newForest 9 0 33 = true := (@block_merge newForest 9 0 24 9 check9_0 (@block_merge newForest 9 24 3 6 check9_24 check9_27))
theorem tables : checkedTables newForest 13 := by
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
  · rfl
  · exact all9
  · exact all10
  · exact all11
  · exact all12
  · exact all13


open PEqualNP.CircuitLowerBounds

def firstWire : Sig := bin true (inputs.getD 0 zero) (inputs.getD 4 zero)
def firstBank := inputs ++ [firstWire]

def coloredBank : List Decor :=
  let pool := wiresOf newForest
  pool ++ [dbin true (pool.getD 0 defaultDecor) (pool.getD 4 defaultDecor)]

def initialBank (j : Fin 11) : List Decor :=
  coloredBank ++ [dneg (coloredBank.getD j.val defaultDecor)]

theorem initial_values (j : Fin 11) :
    (initialBank j).map Prod.fst = firstBank ++ [neg (firstBank.getD j.val zero)] := by
  fin_cases j <;> rfl

theorem firstWire_table (r : Row) :
    bit r firstWire = (sample r 0 || sample r 4) := by
  exact bit_bin r true _ _

def linkRoot (ws : List Decor) : Bool :=
  let sig := ws.map Prod.fst
  let entry := newIndex 14 (keySet sig)
  ((entry.bind (linkedSet newForest 13)).toList).any (sameWords sig)

def rootTest (ws : List Decor) : Bool :=
  !(ws.all fun a => properB a.1) || (coverage false ws).1 != BitVec.allOnes 768 || linkRoot ws

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem initial_checked (j : Fin 11) : (initialBank j).sublists.all rootTest = true := by
  fin_cases j <;> decide +kernel

set_option maxRecDepth 8192 in
theorem excluded (blocks : checkedTables newForest 13) (j : Fin 11)
    {k t S} (short : k ≤ 13) (run : Live graph k t S)
    (sub : ∀ v ∈ S, v ∈ (initialBank j).map Prod.fst) : False := by
  classical
  let ws := (initialBank j).filter fun w => decide (w.1 ∈ S)
  have inside : ws.Sublist (initialBank j) := List.filter_sublist
  have eq : (ws.map Prod.fst).toFinset = S := by
    ext a
    simp only [List.mem_toFinset,List.mem_map,ws,List.mem_filter,decide_eq_true_eq]
    constructor
    · rintro ⟨w,⟨_,hm⟩,rfl⟩
      exact hm
    · intro ha
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp (sub _ ha)
      exact ⟨w,⟨hw,ha⟩,rfl⟩
  have valid := geometry
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at valid
  have same : targetOf newForest = graph := by decide +kernel
  have samples := chart_pairs valid.1.1.1 valid.1.1.2
  let p := asRow fun i => (newForest.samples i).1
  let q := asRow fun i => (newForest.samples i).2
  have faith : ∀ a ∈ ws, faithful p q a := by
    have basic : ∀ a ∈ wiresOf newForest, faithful p q a := wires_faithful newForest
    have first : ∀ a ∈ coloredBank, faithful p q a := by
      intro a ha
      rcases List.mem_append.mp ha with h | h
      · exact basic _ h
      · obtain rfl := List.mem_singleton.mp h
        exact faithful_bin _ (faithful_get basic _) (faithful_get basic _)
    intro a ha
    rcases List.mem_append.mp (inside.subset ha) with h | h
    · exact first _ h
    · obtain rfl := List.mem_singleton.mp h
      exact faithful_neg (faithful_get first _)
  have cover : (coverage false ws).1 = BitVec.allOnes 768 := by
    rw [cov_word false ws faith]
    apply cover_sound run eq (pair_sep (same ▸ samples))
    intro h
    contradiction
  have props : (ws.all fun a => properB a.1) = true := by
    apply List.all_eq_true.mpr
    intro a ha
    have haS : a.1 ∈ S := eq ▸ List.mem_toFinset.mpr (List.mem_map.mpr ⟨a,ha,rfl⟩)
    simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using live_proper run a.1 haS
  have test := List.all_eq_true.mp (initial_checked j) ws (List.mem_sublists.mpr inside)
  have link : linkRoot ws = true := by
    unfold rootTest at test
    rw [props,cover] at test
    simpa only [bne_self_eq_false,Bool.not_true,Bool.false_or] using test
  obtain ⟨xs,hx,he⟩ := List.any_eq_true.mp link
  have opt := Option.mem_toList.mp hx
  obtain ⟨entry,_,out⟩ := Option.bind_eq_some_iff.mp opt
  have tables_ok := forest_all newForest 13 _ (before_sound known383 valid383) geometry blocks 13 (by omega)
  have impossible := linkedSet_sound newForest 13 valid.2 tables_ok out
  rw [same,←sameWords_sound he,eq] at impossible
  exact impossible k t short run

theorem conclusion (blocks : checkedTables newForest 13) (C : Circuit)
    (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (first : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 4))
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge)
    (second : C.gates[1]?.map Gate.op = some GateOp.not) : 16 ≤ C.size := by
  by_contra small
  have headEq : (execute C.gates inputs).getD 9 zero = firstWire := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal 9 r).trans ((first (sample r)).trans (firstWire_table r).symm)
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal C.output r).trans ((congrFun computes (sample r)).trans (edge_table r).symm)
  have out := get_rep (execute C.gates inputs) C.output
  rw [goalEq] at out
  have targetIn := out.resolve_right (fun hn => hn graph_proper)
  cases hgs : C.gates with
  | nil => simp [hgs] at second
  | cons g gs =>
    have eq0 : gv inputs g = firstWire := by
      rw [hgs] at headEq
      change (execute gs (inputs++[gv inputs g])).getD 9 zero = firstWire at headEq
      obtain ⟨l,hl⟩ := exec_extends gs (inputs++[gv inputs g])
      rw [hl] at headEq
      exact headEq
    cases gs with
    | nil => simp [hgs] at second
    | cons h tail =>
      have hn : h.op = GateOp.not := by simpa [hgs] using second
      have column : ∃ j : Fin 11, gv firstBank h = neg (firstBank.getD j.val zero) := by
        obtain ⟨op,ls⟩ := h
        change op = GateOp.not at hn
        subst op
        cases ls with
        | nil => exact ⟨10,rfl⟩
        | cons i rest =>
          by_cases hi : i < 10
          · exact ⟨⟨i,by omega⟩,rfl⟩
          · refine ⟨10,?_⟩
            change neg (firstBank.getD i zero) = neg zero
            rw [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by change 10 ≤ i; omega)]
            rfl
      obtain ⟨j,hj⟩ := column
      rw [hgs] at targetIn
      change graph ∈ execute (h :: tail) (inputs ++ [gv inputs g]) at targetIn
      rw [eq0] at targetIn
      change graph ∈ execute tail (firstBank ++ [gv firstBank h]) at targetIn
      rw [hj,←initial_values j] at targetIn
      obtain ⟨k,t,S,hk,run,hs⟩ := extract tail _
        (fun gate hg => legal gate (by rw [hgs]; simp [hg])) graph_proper targetIn
      have bound : tail.length + 2 < 16 := by simpa [Circuit.size,hgs] using Nat.lt_of_not_ge small
      exact excluded blocks j (by omega) run hs

end PEqualNP.Outside.L_meta_2750

theorem PEqualNP.Outside.L_meta_2750 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → Option.map (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.op) x1.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.not → Option.map (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op) x1.gates[(2 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.or → (16 : ℕ) ≤ x1.size := by
  intro C legal first computes second _
  exact PEqualNP.Outside.L_meta_2750.conclusion PEqualNP.Outside.L_meta_2750.tables C legal first computes second
