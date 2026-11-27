import PEqualNP.Defs

-- The Live/Run/Forest checker derives from PressF10, pequalnp-proofs PR 4332,
-- and its extension in L_meta_3853, licensed under Apache-2.0.
namespace PEqualNP.Outside.L_meta_10668
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
def vertex (m j : Nat) := if m.testBit j then (if m.testBit 9 && j == 4 then neg (inputs.getD 4 zero) else inputs.getD j zero) else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 0 &&& x 7) ||| (x 2 &&& x 7) ||| (x 4 &&& x 7) ||| (x 1 &&& x 8) ||| (x 3 &&& x 8) ||| (x 4 &&& x 8) ||| (x 7 &&& x 8)
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


abbrev Bits := BitVec 512
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 512 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 512 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 512 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 512 → Row) (x : Decor) := x.2 = pairSig r s x.1
def dneg (x : Decor) : Decor := (neg x.1,~~~x.2.1,~~~x.2.2)
def dbin (d : Bool) (x y : Decor) : Decor :=
  if d then (bin d x.1 y.1,x.2.1 ||| y.2.1,x.2.2 ||| y.2.2)
  else (bin d x.1 y.1,x.2.1 &&& y.2.1,x.2.2 &&& y.2.2)

theorem ofRows_neg (r : Fin 512 → Row) (a : Sig) : ofRows r (neg a) = ~~~ofRows r a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (neg a) ⟨j,hj⟩
  rw [bit_neg,←ofRows_bit r a ⟨j,hj⟩] at h
  simpa only [BitVec.getLsbD_not,hj,decide_true,Bool.true_and] using h
theorem ofRows_bin (r : Fin 512 → Row) (d : Bool) (a b : Sig) :
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

def asRow (cols : Nat → Bits) (i : Fin 512) : Row :=
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 512) (j : Fin 9) :
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
  (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 0 &&& x 7) ||| (x 2 &&& x 7) ||| (x 4 &&& x 7) ||| (x 1 &&& x 8) ||| (x 3 &&& x 8) ||| (x 4 &&& x 8) ||| (x 7 &&& x 8)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 512) (j : Fin 9) :
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
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 512) :
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
    if (rs ||| column d z.2) != BitVec.allOnes 512 then true else
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
  change covered (decide (child.length = cap)) (pairSig r s) child = BitVec.allOnes 512 at sep
  rw [deq] at sep
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2) != BitVec.allOnes 512) = false := by simp [sep]
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
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 512) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val :=
  bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 512) (hq : chartSamples m q = 0) :
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
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 512) &&
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
def lanePlace (v : Nat) (upper : Nat) := 2^513*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^513 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<513 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<513 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<513 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
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

def fullMarks (r packed : Nat) := ((packed+r) >>> 512) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (513*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^513)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 513*(i+1)-513=513*i := by omega
      have ge : ¬513*(i+1)<513 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 512 = (a==BitVec.allOnes 512) := by
  by_cases h : a=BitVec.allOnes 512
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^512-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^512 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (513*i) =
      (f xs[i]==BitVec.allOnes 512) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^513*u+x+(2^513*v+1)=2^513*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^513 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬513*(i+1)+512<513 := by omega
      have di : 513*(i+1)+512-513=513*i+512 := by omega
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
theorem top_xor (a : Bits) : BitVec.allOnes 512 ^^^ a = ~~~a := BitVec.allOnes_xor
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp (units xs.length*(BitVec.allOnes 512).toNat) op
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
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 513) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (513*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
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
      apply ih (mask:=mask >>> 513) (i:=i) (by simpa using hi) _ ok.2
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
    let z := packedOp (r*(BitVec.allOnes 512).toNat) op a b'
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
      if len>k then true else if combField xs[q] d (op==2) ka kb op i j != BitVec.allOnes 512 then true
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
        packedColumn d (packedOp (r*(BitVec.allOnes 512).toNat) op a b))) xs) = true at pass
    rw [if_neg small] at pass
    have chosen : cov = packedCov (fun c => getCov c.2.2.2.1 d) xs := by
      dsimp only [cov]
      cases d <;> rfl
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,chosen,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] d (op==2) ka kb op i j = BitVec.allOnes 512
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

def edge10669 : (Fin 9 → Bool) → Bool := fun x : Fin 9 → Bool => (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 4 && x 8) || (x 7 && x 8)
def sample10669 (r : Row) (i : Fin 9) := bit r (inputs.getD i.val zero)
theorem raw10669 : List.ofFn (fun i : Fin 9 => inputs.getD i.val zero) = vars 511 := by decide +kernel
theorem samples10669 (r : Row) : List.ofFn (sample10669 r) = (vars 511).map (bit r) := by
  rw [←raw10669,List.map_ofFn]
  rfl
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem edge10669_table : ∀ r : Row, bit r (graphGoal 511) = edge10669 (sample10669 r) := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem conclude10669 (absent : Impossible (graphGoal 511) 13 (vars 511).toFinset) :
    ∀ t, PEqualNP.MetaComplexity.HasCircuitSize 9 edge10669 t → 14 ≤ t := by
  intro t hs
  obtain ⟨C,hf,hsize,correct⟩ := hs
  by_contra! bad
  have hp : proper (graphGoal 511) := by unfold proper; decide +kernel
  have he : (execute C.gates (vars 511)).getD C.output zero = graphGoal 511 := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    change bit r ((execute C.gates (vars 511)).getD C.output zero) = bit r (graphGoal 511)
    rw [←b_read,execute_bits _ _ _ (fun g hg => (hf g hg).1),←samples10669,edge10669_table]
    exact correct (sample10669 r)
  have hout := get_rep (execute C.gates (vars 511)) C.output
  rw [he] at hout
  obtain ⟨k,u,S,hk,run,sub⟩ := extract C.gates _ hf hp (hout.resolve_right (fun h => h hp))
  have all : ∀ a ∈ vars 511, Essential (graphGoal 511) (vars 511) a := by
    have valid : checkEssential (graphGoal 511) (vars 511) (graphPairs 511 4329006677) = true := by decide +kernel
    have ident : (graphPairs 511 4329006677).map Prod.fst = vars 511 := by decide +kernel
    intro a ha
    apply essential_ok valid a
    rw [ident]
    exact List.mem_toFinset.mpr ha
  have eq : S=(vars 511).toFinset := by
    ext a
    constructor
    · exact fun ha => List.mem_toFinset.mpr (sub a ha)
    · intro ha
      obtain ⟨r,s,diff,sep⟩ := all a (List.mem_toFinset.mp ha)
      exact raw_required run _ a sub r s diff sep
  rw [eq] at run
  change C.gates.length ≤ t at hsize
  exact absent k u (by omega) run
def packed400r3 (i : Nat) : Nat := 0x7
def layer400r3 : Packing := (1,0,0,63,0,0,1,packed400r3)
def samples400 : Array (Bits × Bits) := #[(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x3f,0x49),(0x0,0x0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc7,0x92),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff24)]
def cols400 : IndexTree ColumnInfo := (.leaf [])
def levels400 : Nat → Packing
  | 3 => layer400r3
  | _ => emptyPacking
def index400 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g400 : Forest := ⟨400,3,fun j => samples400[j]?.getD (0,0),cols400,#[[]],levels400,index400,noFactory,noFactorySound 400⟩
def packed163r3 (i : Nat) : Nat := 0xf
def layer163r3 : Packing := (1,0,0,63,0,0,1,packed163r3)
def samples163 : Array (Bits × Bits) := #[(0x7fc1f,0x11c43),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffb07e0,0xb556a),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc07ff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff48294),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffee318),(0x0,0x0)]
def cols163 : IndexTree ColumnInfo := (.leaf [])
def levels163 : Nat → Packing
  | 3 => layer163r3
  | _ => emptyPacking
def index163 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g163 : Forest := ⟨163,3,fun j => samples163[j]?.getD (0,0),cols163,#[[]],levels163,index163,noFactory,noFactorySound 163⟩
def packed401r4 (i : Nat) : Nat := 0x1f
def layer401r4 : Packing := (1,0,0,63,0,0,1,packed401r4)
def samples401 : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0c10f,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9e5ab),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0xfff0,0x14732),(0x0,0x0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01ff,0x20844),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe00,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcb088)]
def cols401 : IndexTree ColumnInfo := (.leaf [(1,0,400,0,4)])
def levels401 : Nat → Packing
  | 4 => layer401r4
  | _ => emptyPacking
def index401 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g401 : Forest := ⟨401,4,fun j => samples401[j]?.getD (0,0),cols401,#[[]],levels401,index401,noFactory,noFactorySound 401⟩
def packed167r4 (i : Nat) : Nat := 0x1f
def layer167r4 : Packing := (1,0,0,63,0,0,1,packed167r4)
def samples167 : Array (Bits × Bits) := #[(0x1903fe703f,0x9090e3083),(0x6e03039fc0,0x2e4b4a94d2),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8ffc03e000,0x8b1c1be28a),(0x0,0x0),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00003ffff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd090914b2c),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff74e2e00c30),(0x0,0x0)]
def cols167 : IndexTree ColumnInfo := (.leaf [])
def levels167 : Nat → Packing
  | 4 => layer167r4
  | _ => emptyPacking
def index167 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g167 : Forest := ⟨167,4,fun j => samples167[j]?.getD (0,0),cols167,#[[]],levels167,index167,noFactory,noFactorySound 167⟩
def packed419r5 (i : Nat) : Nat := 0x2080202020182000408020080200803f3968c56294884f19283c50500fd43fd42fd32fd41fd31fd21fd40fd30fd20fd10be44de33ee22f611fa00
def layer419r5 : Packing := (15,1,3,63,0,7,1,packed419r5)
def keys419k6 (i : Nat) : Nat := 0x28c010803633003b80334020443d800140000000000011fe80001e7ae5348
def packed419r6 (i : Nat) : Nat := 0x23444bf
def layer419r6 : Packing := (1,0,3,63,0,0,1,packed419r6)
def samples419 : Array (Bits × Bits) := #[(0x403c01ffc07f,0x509d1051d123),(0x804ffec07f80,0x82843ac5458a),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff007007007fff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff246245282a54),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8007ff8000,0x18700678e0c18),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe787b80303060)]
def cols419 : IndexTree ColumnInfo := (.fork 2 (.leaf [(1,0,418,0,4),(2,0,417,0,4)]) (.leaf [(32,0,387,0,4),(128,0,291,0,4),(256,0,163,0,4)]))
def levels419 : Nat → Packing
  | 5 => layer419r5
  | 6 => layer419r6
  | _ => emptyPacking
def index419 : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 5 29 2 8 4 0 keys419k6
  | _ => fun _ => none
def g419 : Forest := ⟨419,6,fun j => samples419[j]?.getD (0,0),cols419,#[[]],levels419,index419,noFactory,noFactorySound 419⟩
def packed433r5 (i : Nat) : Nat := 0x20441204c100401007cca8794280fd43fe33fd41fd31be44de33f611
def layer433r5 : Packing := (7,1,3,63,0,6,1,packed433r5)
def keys433k6 (i : Nat) : Nat := 0x6d000000000e804686000000000000000004900d1
def packed433r6 (i : Nat) : Nat := 0x6a47f
def layer433r6 : Packing := (1,0,3,63,0,0,1,packed433r6)
def samples433 : Array (Bits × Bits) := #[(0x803c0180ffff,0xa11d10a246a3),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0xcffeff0180,0x3443a870d8a),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00f0070001ff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff4ae26754a95c),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0007fffe00,0x10c0045183010),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffef0bb8060c060)]
def cols433 : IndexTree ColumnInfo := (.fork 2 (.leaf [(0,32,400,1,5),(32,0,401,0,5)]) (.leaf [(16,0,417,0,4),(256,0,177,0,4),(1,32,400,0,4)]))
def levels433 : Nat → Packing
  | 5 => layer433r5
  | 6 => layer433r6
  | _ => emptyPacking
def index433 : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 23 1 7 3 0 keys433k6
  | _ => fun _ => none
def g433 : Forest := ⟨433,6,fun j => samples433[j]?.getD (0,0),cols433,#[[]],levels433,index433,noFactory,noFactorySound 433⟩
def packed403r5 (i : Nat) : Nat := 0x3f
def layer403r5 : Packing := (1,0,0,63,0,0,1,packed403r5)
def samples403 : Array (Bits × Bits) := #[(0x20b060907f,0x31b9729933),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0c07fe060,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc5c327e56a),(0x0,0x0),(0x0,0x0),(0xff80ff80,0x1d182b182),(0x0,0x0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc60204464c),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000,0x382c580810)]
def cols403 : IndexTree ColumnInfo := (.leaf [(1,0,402,0,5)])
def levels403 : Nat → Packing
  | 5 => layer403r5
  | _ => emptyPacking
def index403 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g403 : Forest := ⟨403,5,fun j => samples403[j]?.getD (0,0),cols403,#[[]],levels403,index403,noFactory,noFactorySound 403⟩
def packed235r5 (i : Nat) : Nat := 0x7f
def layer235r5 : Packing := (1,0,0,63,0,0,1,packed235r5)
def samples235 : Array (Bits × Bits) := #[(0x8793fff93cc02700ff,0x280a8391cc2a30a0b),(0x3666d9801cf0039ff00,0x166259ab14f16a95b5a),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc7871e0060ffffe0000,0x42871e192054cfe3232),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff807e0007f0003fffff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe805a0506a02814a4a4),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800007ffffc00000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbd7800625fab300c8c8),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd7f57c0003c00f0f0),(0x0,0x0)]
def cols235 : IndexTree ColumnInfo := (.leaf [(0,8,163,64,5)])
def levels235 : Nat → Packing
  | 5 => layer235r5
  | _ => emptyPacking
def index235 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g235 : Forest := ⟨235,5,fun j => samples235[j]?.getD (0,0),cols235,#[[]],levels235,index235,noFactory,noFactorySound 235⟩
def packed231r6 (i : Nat) : Nat := 0xe413f
def layer231r6 : Packing := (1,0,2,63,0,0,1,packed231r6)
def samples231 : Array (Bits × Bits) := #[(0x9e1901ff279809c07f,0xa09148b239928c913),(0x3586e018039e00e7f80,0x1582e55aa29e32a59b2),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc618ffe00c1ffff8000,0x8b0e0640a87f850a),(0x0,0x0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff81f00000fe000fffff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe81d08844d40445264c),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe000000fffff00000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe00d068bf57803870),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff574e1700006003060),(0x0,0x0)]
def cols231 : IndexTree ColumnInfo := (.leaf [(0,2,197,32,5),(0,64,163,4,5),(2,0,229,0,5),(64,0,167,0,5)])
def levels231 : Nat → Packing
  | 6 => layer231r6
  | _ => emptyPacking
def index231 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g231 : Forest := ⟨231,6,fun j => samples231[j]?.getD (0,0),cols231,#[[]],levels231,index231,noFactory,noFactorySound 231⟩
def packed245r6 (i : Nat) : Nat := 0x90ff
def layer245r6 : Packing := (1,0,2,63,0,0,1,packed245r6)
def samples245 : Array (Bits × Bits) := #[(0xc60d0101fccf301fff,0x420515142c47324a93),(0x0,0x0),(0x1093601fe0333fff980,0x1160d0e191150f98a),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe71c7fe0003c3c01e00,0x251473e3c7bc3c6de3a),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff81f8000003fc001fff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff81f8a8a953b80c956c),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe00000003ffffe000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe00b0b162eeaf0070),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdaca8c0c18000080040),(0x0,0x0)]
def cols245 : IndexTree ColumnInfo := (.leaf [(16,0,229,0,5),(1,32,212,0,4),(4,64,177,0,4)])
def levels245 : Nat → Packing
  | 6 => layer245r6
  | _ => emptyPacking
def index245 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g245 : Forest := ⟨245,6,fun j => samples245[j]?.getD (0,0),cols245,#[[]],levels245,index245,noFactory,noFactorySound 245⟩
def packed438r7 (i : Nat) : Nat := 0x7f
def layer438r7 : Packing := (1,0,0,63,0,0,1,packed438r7)
def samples438 : Array (Bits × Bits) := #[(0x0,0x0),(0x2003901ff0760301fff,0x22409148b0364b24a93),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe4032e018099803ff980,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe50f2e8dc6899198f9ca),(0x0,0x0),(0x3cffe00e1ffc01e00,0xd4b0e06a1a1c0de0a),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff803f00000fe00001fff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff94bf0a854fc190c956c),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000000ffffffe000,0xa70003018564e270030),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff582b4c1600010080040)]
def cols438 : IndexTree ColumnInfo := (.leaf [(4,0,434,0,7)])
def levels438 : Nat → Packing
  | 7 => layer438r7
  | _ => emptyPacking
def index438 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g438 : Forest := ⟨438,7,fun j => samples438[j]?.getD (0,0),cols438,#[[]],levels438,index438,noFactory,noFactorySound 438⟩
def packed437r7 (i : Nat) : Nat := 0x7f
def layer437r7 : Packing := (1,0,0,63,0,0,1,packed437r7)
def samples437 : Array (Bits × Bits) := #[(0x5001f980068080fffff,0x5420b9a202a2a246aa3),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe60199e009b00ff01980,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe6c799e668b66e7cd9ea),(0x0,0x0),(0x1e1fffe3ff0001e00,0x6a0a87a387060de0a),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff801fe000fc000001fff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff895f404cfc5454a955c),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe00000fffffffe000,0x8180000854181830010),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7e15f570006060c0060)]
def cols437 : IndexTree ColumnInfo := (.leaf [(4,0,433,0,7)])
def levels437 : Nat → Packing
  | 7 => layer437r7
  | _ => emptyPacking
def index437 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g437 : Forest := ⟨437,7,fun j => samples437[j]?.getD (0,0),cols437,#[[]],levels437,index437,noFactory,noFactorySound 437⟩
def packed423r7 (i : Nat) : Nat := 0x7f
def layer423r7 : Packing := (1,0,0,63,0,0,1,packed423r7)
def samples423 : Array (Bits × Bits) := #[(0x4806f3001901ff9c07f,0x4a1273440944a38d123),(0x10093ffe6e0180e7f80,0x1050150e2e158aa458a),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe600e3c018ffe00f8000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe661e3cc48bc662fb162),(0x0,0x0),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800fc001f00000fffff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff848d8091d0a05052a54),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00001ffffff00000,0x90e0001974391c00c18),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe00000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff6f0feae000c06003060)]
def cols423 : IndexTree ColumnInfo := (.leaf [(4,0,419,0,7)])
def levels423 : Nat → Packing
  | 7 => layer423r7
  | _ => emptyPacking
def index423 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g423 : Forest := ⟨423,7,fun j => samples423[j]?.getD (0,0),cols423,#[[]],levels423,index423,noFactory,noFactorySound 423⟩
def packed435r5 (i : Nat) : Nat := 0x4ed7299954
def layer435r5 : Packing := (1,3,3,63,0,0,1,packed435r5)
def keys435k6 (i : Nat) : Nat := 0x70
def packed435r6 (i : Nat) : Nat := 0x80000000002479848c180bf99954bb58854bd58454be58054cf95644d795633e791233
def layer435r6 : Packing := (7,2,3,63,0,6,1,packed435r6)
def keys435k7 (i : Nat) : Nat := 0x15000001645801b7a4122
def packed435r7 (i : Nat) : Nat := 0xa8420c321cc54b5306b2b210828d5311d4c475311c4372a1b1209007f957faa9fc54ff225f9577c89de33
def layer435r7 : Packing := (7,1,3,63,0,8,1,packed435r7)
def keys435k8 (i : Nat) : Nat := 0x1579000000000d00000000000248678049
def packed435r8 (i : Nat) : Nat := 0x468897f
def layer435r8 : Packing := (1,0,3,63,0,0,1,packed435r8)
def samples435 : Array (Bits × Bits) := #[(0x1001d806001900ffe700ff,0x1410da1684094250e34243),(0x20026007fe6e00c039ff00,0x20906052162e12c4a91312),(0x0,0x0),(0x0,0x0),(0xc7ff8018fff003e0000,0x3468380c8b0701be0a0a),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00f800001f000003fffff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc92f04a129d0a42914acac),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000001ffffffc00000,0x61c000c03174388e003030),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9e0b9705c000c03000c0c0)]
def cols435 : IndexTree ColumnInfo := (.fork 3 (.leaf [(1,0,434,0,7),(2,0,433,0,7),(16,0,419,0,7)]) (.leaf [(0,32,400,3,6),(32,0,403,0,6),(128,0,307,0,5),(256,0,179,0,5)]))
def levels435 : Nat → Packing
  | 5 => layer435r5
  | 6 => layer435r6
  | 7 => layer435r7
  | 8 => layer435r8
  | _ => emptyPacking
def index435 : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 keys435k6
  | 7 => lookupWord 2 11 2 7 3 0 keys435k7
  | 8 => lookupWord 2 19 0 7 3 0 keys435k8
  | _ => fun _ => none
def g435 : Forest := ⟨435,8,fun j => samples435[j]?.getD (0,0),cols435,#[[]],levels435,index435,noFactory,noFactorySound 435⟩
def packed251r6 (i : Nat) : Nat := 0xff
def layer251r6 : Packing := (1,0,0,63,0,0,1,packed251r6)
def samples251 : Array (Bits × Bits) := #[(0x640f02649003fffc993cccc009ce7003ff,0x240500249029502c891cccc128c6304813),(0x1b8cc0db8e0033000e1cf0f000e739ffc00,0xb8cc04b8e52b3528a14f0f152a52954d52),(0x0,0x0),(0x600f0ce3f0003c003060fffffff83e00000,0x20050ce3f031bc3190205554c7f83e328ca),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff83f00f03ffffc0003f80ff0000ffc000000,0x82d00502db07c007bf80ff0036ffc00e83a),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000ffc000000003fff000000fffffffff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff4000fb400a500a5356a0002a45294ab2ac),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000003fffffffff000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdffaf00000c600c62fdfaaab380000cc330),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000000000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7d2faafd24f82af800000003c00000f03c0),(0x0,0x0)]
def cols251 : IndexTree ColumnInfo := (.leaf [(0,8,179,64,6)])
def levels251 : Nat → Packing
  | 6 => layer251r6
  | _ => emptyPacking
def index251 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g251 : Forest := ⟨251,6,fun j => samples251[j]?.getD (0,0),cols251,#[[]],levels251,index251,noFactory,noFactorySound 251⟩
def packed239r7 (i : Nat) : Nat := 0xff
def layer239r7 : Packing := (1,0,0,63,0,0,1,packed239r7)
def samples239 : Array (Bits × Bits) := #[(0x103c2193e401ffc13acc019802739c01ff,0x140091641482c11acc25984a318c2413),(0x6cb0c6e338018001ccf001e0039ce7fe00,0x2cb042e33955aa814cf165e2ca94a566b2),(0x80c318fc3ffe00260f0001ffffe0f80000,0x108b42c0e01a20f000ca81fe0f8140a),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0f03e0ffc00000380ffffe0003ff000000,0x10503e0ffc0cc19a80f54ce019bff00d46a),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff003ff000000003ff000000003ffffffff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd003bd000288513ea0028805114a52994c),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00000000003ffffffffffc00000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefafc000003106215f0ab31566000032190),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeaf74a93e17c000003c007800003c1e0),(0x0,0x0)]
def cols239 : IndexTree ColumnInfo := (.leaf [(2,0,237,0,7)])
def levels239 : Nat → Packing
  | 7 => layer239r7
  | _ => emptyPacking
def index239 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g239 : Forest := ⟨239,7,fun j => samples239[j]?.getD (0,0),cols239,#[[]],levels239,index239,noFactory,noFactorySound 239⟩
def packed247r7 (i : Nat) : Nat := 0xff
def layer247r7 : Packing := (1,0,0,63,0,0,1,packed247r7)
def samples247 : Array (Bits × Bits) := #[(0x643c06a402403ff264f333009ce700ff,0x241402a42a4290b2247333128c631213),(0x1b8b01b3803803003873c3c00e739ff00,0xb8b00b392b92b4a2853c3c52a5295352),(0x200c263c003ffc00c183ffffff83e0000,0x223c01ac1c06408155507f83e0a0a),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc3f0383fffc00000fe03fc000ffc00000,0x42d0283ec7c0781efe03fc036ffc03a3a),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc003fc000000000fffc00000ffffffff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff4003f4025025094d5a8000a45294acac),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00000000000fffffffff00000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000360360d8bf7eaaaf80000f0f0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbd2e95c1381382e00000000c00000c0c0),(0x0,0x0)]
def cols247 : IndexTree ColumnInfo := (.leaf [(2,0,245,0,7)])
def levels247 : Nat → Packing
  | 7 => layer247r7
  | _ => emptyPacking
def index247 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g247 : Forest := ⟨247,7,fun j => samples247[j]?.getD (0,0),cols247,#[[]],levels247,index247,noFactory,noFactorySound 247⟩
def packed487r7 (i : Nat) : Nat := 0x41000101000000000000000cd82a4e90f1b305490f182430300bfceeb2dfe775837eb2ac17f9dd50bfaeca87f9605433f334abb799a33ebcab19ef666847bb2ac23f58ce11df4cd0077a55803ed19c01fc84600
def layer487r7 : Packing := (16,2,4,63,0,7,1,packed487r7)
def keys487k8 (i : Nat) : Nat := 0x4ca8378032234f000008f98ead8402805166055be080
def packed487r8 (i : Nat) : Nat := 0xe41882bace418820aa0752082aa4649061aa86520620d4c3a88308aab1d072083530e81ad320d67310620a6b3a081aa8552061aac6ac35845586b0d61dee52e14c91be9a2a83f9807831108581600ff597fe55ff58ffd53ff587fd51ff4c7fd60ff543fd30ff442fe66df957de33fd847fa00
def layer487r8 : Packing := (16,1,4,63,0,9,1,packed487r8)
def keys487k9 (i : Nat) : Nat := 0xe44aeea1cc027002fc00038146775400031800000338000328005d500060
def packed487r9 (i : Nat) : Nat := 0x8642b2ff
def layer487r9 : Packing := (1,0,4,63,0,0,1,packed487r9)
def samples487 : Array (Bits × Bits) := #[(0x1048003cc6f30004f0c801ffe4f30027003ff,0x104a861cc2735180504a8ca8e47352a35294b),(0x20100040f93fffdac3700180073c0039ffc00,0x20101600501503cac1702d82c53c06a906c1a),(0x260018f0e3c00230c7ffe00183ffffe00000,0x26182850e3c308004598618481530fe308c2),(0x0,0x0),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc38001f00fc0003c0f8000001fc0003ffffff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc38521e00d80a4340e8540541a80a814a92a4),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0001fff000003ff00000001fffffc000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc06357af000c73ff006686697eacf00ce338),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe000000003fffffffffe000000000000,0x649038000000063faba0710700000c000c030),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000000000000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9b6fc1ffafeaf800000780780000f000f03c0)]
def cols487 : IndexTree ColumnInfo := (.fork 6 (.fork 3 (.leaf [(64,0,423,0,8),(1,0,486,0,7),(2,0,485,0,7)]) (.leaf [(32,0,455,0,7),(256,0,231,0,7),(4,64,419,0,7)])) (.fork 3 (.leaf [(0,2,197,288,6),(0,32,452,3,6),(128,0,359,0,6)]) (.leaf [(1,32,452,2,5),(2,32,452,1,5),(256,2,197,32,5)])))
def levels487 : Nat → Packing
  | 7 => layer487r7
  | 8 => layer487r8
  | 9 => layer487r9
  | _ => emptyPacking
def index487 : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 5 20 3 8 4 0 keys487k8
  | 9 => lookupWord 5 29 2 8 4 0 keys487k9
  | _ => fun _ => none
def g487 : Forest := ⟨487,9,fun j => samples487[j]?.getD (0,0),cols487,#[[]],levels487,index487,noFactory,noFactorySound 487⟩
def packed502r6 (i : Nat) : Nat := 0xc609ed829dd65e6d6558952c6d655c865
def layer502r6 : Packing := (3,3,4,63,0,4,1,packed502r6)
def keys502k7 (i : Nat) : Nat := 0x36640a00
def packed502r7 (i : Nat) : Nat := 0x20000004840004847860cf2c70933cb1c04cf2c70100000b4aea8a296908a7e726c4e30120c0600bfceeb2fec72596feb90cb7f9dd62dfacab15fe7754afebb2a5df59552fdac4a967d65196f6b90cb7d5c465bf2e032e7e669577733445db95622
def layer502r7 : Packing := (16,2,4,63,0,8,1,packed502r7)
def keys502k8 (i : Nat) : Nat := 0x143a0000a96e80002780000c9b004d005a8e0380670021881d800300
def packed502r8 (i : Nat) : Nat := 0xe415aa81896ac76a9e341076a9c6392d59104ada4acad1da758ed58af29e49b950e8944003fe66ff597fc65ff957fd62ff54afe66df957ee22
def layer502r8 : Packing := (9,1,4,63,0,8,1,packed502r8)
def keys502k9 (i : Nat) : Nat := 0x34d90da0401940000008a0001e00000000000dc0000c
def packed502r9 (i : Nat) : Nat := 0x8cb1ff
def layer502r9 : Packing := (1,0,4,63,0,0,1,packed502r9)
def samples502 : Array (Bits × Bits) := #[(0x0,0x0),(0x204000c30e400fff1e40ec00c0033cc00ffff,0x204250410242a42b0e406c4ac4a11cc525453),(0x480030ccb800c0020733000fffccffffcc00,0x4903104cb906d0600113106507445507cd0a),(0x0,0x0),(0xc70f3fff000c79c3fff000f0f000f000,0xf45052c1f01e4294341f01ef0f036f03a),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc7000f80fc000000f81fc000000ff0000ffff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc734af80fc354354f01f8394394ee03a4abac),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000fff00000000ffe00000000ffffff0000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff826cefb00278278ffe002d82d8bbaaf802f0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000fffffffffff0000000000,0x6947000000060060bd6ac8e08e00000c000c0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff96b80baead380b80000003003000003000300)]
def cols502 : IndexTree ColumnInfo := (.fork 4 (.leaf [(0,32,468,2,8),(0,64,434,4,8),(32,0,470,0,8),(64,0,438,0,8)]) (.fork 2 (.leaf [(16,0,486,0,7),(2,32,468,0,7)]) (.leaf [(4,64,434,0,7),(128,0,374,0,6),(256,0,246,0,6)])))
def levels502 : Nat → Packing
  | 6 => layer502r6
  | 7 => layer502r7
  | 8 => layer502r8
  | 9 => layer502r9
  | _ => emptyPacking
def index502 : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 5 0 6 2 0 keys502k7
  | 8 => lookupWord 5 26 3 8 4 0 keys502k8
  | 9 => lookupWord 3 23 2 8 4 0 keys502k9
  | _ => fun _ => none
def g502 : Forest := ⟨502,9,fun j => samples502[j]?.getD (0,0),cols502,#[[]],levels502,index502,noFactory,noFactorySound 502⟩
def packed501r6 (i : Nat) : Nat := 0x40c9809ed829dd658fd869dd52e6d6558952
def layer501r6 : Packing := (3,3,3,63,0,5,1,packed501r6)
def keys501k7 (i : Nat) : Nat := 0xa4d40
def packed501r7 (i : Nat) : Nat := 0x10001004100428600001423840000d796ac574d17283a48606017f9dd65fd8e4b2dfd76956feb94abbf59562bfceea95fd7654b7e3b2a5df59552fdac4a967e669577733445db95622
def layer501r7 : Packing := (13,2,3,63,0,7,1,packed501r7)
def keys501k8 (i : Nat) : Nat := 0x100b70079125b1cc6280000739400b500fa60021
def packed501r8 (i : Nat) : Nat := 0x65b92194c6e4c5b8d2196e49b916e4c49b917cbd219241c03fd65ff957fd62ff54afe66df957ee22
def layer501r8 : Packing := (7,1,3,63,0,7,1,packed501r8)
def keys501k9 (i : Nat) : Nat := 0x4900d3a800000000842274b0001
def packed501r9 (i : Nat) : Nat := 0xd5927f
def layer501r9 : Packing := (1,0,3,63,0,0,1,packed501r9)
def samples501 : Array (Bits × Bits) := #[(0x20a0003cc0fcc000c60d001001ffccf3001ffff,0x20aa141cc05cd4504205515514a2c473524aa93),(0x0,0x0),(0x4c000c0fccf00010936001ffe00333ffff9800,0x4c60c405ccf0c30011630d30e61911530f998a),(0x0,0x0),(0x30f0f0ffffe71c7ffe000003c3c001e000,0x3d05050540fa514703e03c07bc3c06de03a),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc70003f00ff0000781f8000000003fc0001ffff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc714abe00fa029a781f8aa8aa9553b80ac9556c),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80003fff0000007fe00000000003fffffe0000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff818b3bfa00031c7fe00cb0cb1962eeacf00670),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000000007ffffffffffffc0000000000,0x4900c00000000105aca80c00c01800000800040),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800000000000000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffb6ff02fafafabe000000f00f01e00000f000780)]
def cols501 : IndexTree ColumnInfo := (.fork 3 (.leaf [(32,0,469,0,8),(64,0,437,0,8),(16,0,485,0,7)]) (.leaf [(256,0,245,0,7),(1,32,468,0,7),(4,64,433,0,7),(272,0,229,0,5)]))
def levels501 : Nat → Packing
  | 6 => layer501r6
  | 7 => layer501r7
  | 8 => layer501r8
  | 9 => layer501r9
  | _ => emptyPacking
def index501 : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 5 0 6 2 0 keys501k7
  | 8 => lookupWord 4 19 3 8 4 0 keys501k8
  | 9 => lookupWord 2 23 1 7 3 0 keys501k9
  | _ => fun _ => none
def g501 : Forest := ⟨501,9,fun j => samples501[j]?.getD (0,0),cols501,#[[]],levels501,index501,noFactory,noFactorySound 501⟩
def packed445r8 (i : Nat) : Nat := 0xff
def layer445r8 : Packing := (1,0,0,63,0,0,1,packed445r8)
def samples445 : Array (Bits × Bits) := #[(0x280003eb301980009a501380fffffff,0x2a10016b3459a2000a5451a246aaaa3),(0x0,0x0),(0x2300b3333c01e00936c601cff0199980,0x2363b3333ccde66912c6cd4e7cd999ea),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc400c3c3c001fffe38f801f0001e1e00,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc40bc143c01ca8fe38f82df162de1e1a),(0xfc03fffe000fc0fffe00001fe000,0x3d403d50e006b40ef0e0060dfe00a),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800fffc0000000fff000000001fffff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff84affe8009804cfff00a8054a95555c),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000fffffffffffe00000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcc0c000000100084ad1030a183000010),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000,0x33f02abc2ae157000000c0060c000060)]
def cols445 : IndexTree ColumnInfo := (.leaf [(4,0,441,0,8)])
def levels445 : Nat → Packing
  | 8 => layer445r8
  | _ => emptyPacking
def index445 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g445 : Forest := ⟨445,8,fun j => samples445[j]?.getD (0,0),cols445,#[[]],levels445,index445,noFactory,noFactorySound 445⟩
def packed431r8 (i : Nat) : Nat := 0xff
def layer431r8 : Packing := (1,0,0,63,0,0,1,packed431r8)
def samples431 : Array (Bits × Bits) := #[(0x90006ecb00cc002193e403ff9ce700ff,0x941026cb42cd0800916509438c634243),(0x22000930c00fffcc6e3380300e739ff00,0x22090030c0a542c42e3384b12a5291312),(0x10c00ce3f000f00318fc3ffc00f83e0000,0x10cc3ce3f0c6f31908b42f1cc6f83ecaca),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe3000f03ffff0003e0ffc00000ffc00000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe301b5035d1f007be0ffc0d836ffc03a3a),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000ffc00000003ff00000000ffffffff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc092fd800940253bd000290a45294acac),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000003ffffffffff00000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe721c00000180062f74a90e23800003030),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000000000000000000,0x18de0afca2e0ab8000000300c00000c0c0)]
def cols431 : IndexTree ColumnInfo := (.leaf [(4,0,427,0,8)])
def levels431 : Nat → Packing
  | 8 => layer431r8
  | _ => emptyPacking
def index431 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g431 : Forest := ⟨431,8,fun j => samples431[j]?.getD (0,0),cols431,#[[]],levels431,index431,noFactory,noFactorySound 431⟩
def packed439r9 (i : Nat) : Nat := 0xff
def layer439r9 : Packing := (1,0,0,63,0,0,1,packed439r9)
def samples439 : Array (Bits × Bits) := #[(0x90006ecb00cc0006a402403ff9ce700ff,0x941026cb42cd0802a50a509438c634243),(0x2000930c00fffc1b380380300e739ff00,0x2090030c0a542c0b384b84b12a5291312),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcc00ce3f000f00263c003ffc00f83e0000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffccc3ce3f0c6f31a23c31af1cc6f83ecaca),(0x0,0x0),(0xf03ffff000383fffc00000ffc00000,0x35035d07001a83ec1c01806ffc00a0a),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000ffc00000003fc000000000ffffffff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff092fd800940253f40290290a45294acac),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000003fffffffffff00000000,0x121c000001800615c10e10e23800003030),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffede0afca2e0ab80000300300c00000c0c0)]
def cols439 : IndexTree ColumnInfo := (.leaf [(4,0,435,0,9)])
def levels439 : Nat → Packing
  | 9 => layer439r9
  | _ => emptyPacking
def index439 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g439 : Forest := ⟨439,9,fun j => samples439[j]?.getD (0,0),cols439,#[[]],levels439,index439,noFactory,noFactorySound 439⟩
def packed255r8 (i : Nat) : Nat := 0x1ff
def layer255r8 : Packing := (1,0,0,63,0,0,1,packed255r8)
def samples255 : Array (Bits × Bits) := #[(0x1900f0021a92a40093e400fff04c13accccacc00cc009ce739ce7003ff,0x90050000a92a40a91640a40b04411accccacc12cc128c6318c6304813),(0x6e32c00c6ce33800e33800c000701ccf0f0cf000f000e739ce739ffc00,0x2e32c0042ce3394ae3394ad4a05014cf0f0cf152f152a5294a52954d52),(0x800309318f03c000fc3fff00098260f00fff0000fffff83e0f83e00000,0x9108f03c006b42c0700688220f0055f00065407f83e0f83e0280a),(0x3003c0e3e0ffc0000ffc000000e0380fff00fffff0000ffc00ffc000000,0x100140e3e0ffc00c6ffc0c60c6a0280f5500f54c700c6ffc00ffc0328ca),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0fc00fc00fffffff000000000ffc00fffff000000000fffff000000000,0x40b400b400fb7ec1f00001e01effc00fffff000360036fffff00000e83a),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000000000000000fffff00000000000000ffffffffffffff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd0000ffbd0000294000294294fabea00000002a402a45294a5294ab2ac),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000fffffffffffffffffff00000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffebf0000000031800031831857d5f0aaaa0ab38ab38000000000cc330),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbf4bfa4af704813e04a93e0be00000000000003c003c0000000000f03c0),(0x0,0x0)]
def cols255 : IndexTree ColumnInfo := (.leaf [(2,0,253,0,8)])
def levels255 : Nat → Packing
  | 8 => layer255r8
  | _ => emptyPacking
def index255 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g255 : Forest := ⟨255,8,fun j => samples255[j]?.getD (0,0),cols255,#[[]],levels255,index255,noFactory,noFactorySound 255⟩
def packed495r7 (i : Nat) : Nat := 0x83f6a2995d876
def layer495r7 : Packing := (1,4,4,63,0,0,1,packed495r7)
def keys495k8 (i : Nat) : Nat := 0xf0
def packed495r8 (i : Nat) : Nat := 0x2003003801c00a004003003801c00a0040000928c86796c5f524c46392c1f120c06009fe4c4ef3353fa65761db8faec3b4ab75d931da55bb6c90ed2addd64476956ef3203b4abc7e7799a55e5ebb0ed225e764c76912f5b243b4897b5911da44bdcc80ed2272f9de66913a7cef2ac89e3e6695644
def layer495r8 : Packing := (16,3,4,63,0,8,1,packed495r8)
def keys495k9 (i : Nat) : Nat := 0x50900ec3800931e76c2ed00dfa04a77000000d400002100007b0c0a0
def packed495r9 (i : Nat) : Nat := 0x248088849049207185133cb1c2a4012018014018018018211d4823801801821195823801cf2c70225df4232c70367df4273c702e7df4233cb0327df4273cb12a7cf2c70933cb1c24cf2c70933cb1c24cf2c70933cb1c24a9a9aa3a4c902348a21c842047e1e0751c86f1a46617451114390b4258781683c07800ffe885dbff9de66dfc869deffa2176dfe775dbbf21e66efe7799b7f9de66efd7699bdf9de55f7d76957df1da55f7e66957ef9de44fbd76913ef1da44fbe669133f5d876bdd831dafb60876bf5811dafe60076cfe7799b5f9de55e7e669576f9de44ebe66913cf95644
def layer495r9 : Packing := (28,2,4,63,0,10,1,packed495r9)
def keys495k10 (i : Nat) : Nat := 0x6bf1a00000000000818000000e64adc0000002af2004080001a60000000000000000000066aa4005c00001967a8000000dbd6d9c000042400000000191548219c0031000014a000074c00004114000c0
def packed495r10 (i : Nat) : Nat := 0x45ab7a4e51826a4a2d5bd2728c2a25cb44ce51822a4dab7a4e51822a4dab7a4e518528b56f49ca30a6d42ce5184f7a92728c27b04a1e0b8429485200ffcefff5dbfe3b7fe66bfcefbf99bbf2afbe44
def layer495r10 : Packing := (8,1,4,63,0,9,1,packed495r10)
def keys495k11 (i : Nat) : Nat := 0x7b71b80c5d898000000491000000
def packed495r11 (i : Nat) : Nat := 0x195d0c8428ff
def layer495r11 : Packing := (1,0,4,63,0,0,1,packed495r11)
def samples495 : Array (Bits × Bits) := #[(0x80480003b301bb2c00198000103c2193e4001fffc13acc00198002739c001fff,0x804a8141b3009b2d4159a8280014009165414a82c11acd4259a84a318d424a13),(0x10110000403c24c30001ffffc6cb0c6e33800180001ccf0001e00039ce7ffe000,0x10110154001400c300b4a816c2cb042e33815582a814cf0165e02ca94a41660b2),(0x86000183c338fc0001e000080c318fc3fffe000260f00001fffffe0f8000000,0x86180c814338fc0c0de1818000108b42cc0e181a20f00c0ca981fe0f8c1460a),(0x11800020c03c0fffffe000030f03e0ffc0000000380fffffe00003ff00000000,0x11800cc000140d7406e000d90503e0ffc00cc019a80f540ce0019bff000d406a),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe1e00003f003ff00000000003f003ff00000000003ff00000000003ffffffffff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe1e0528be003f600294805293d003bd0002a885513ea002a88055114a52a9954c),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe000003fffc0000000000003fffc0000000000003ffffffffffffc0000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0063137ebc0000319006322fafc00000331066215f0ab331566600003321990),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00000000000000003ffffffffffffffffc00000000000000000000000,0x333903e00000000001e0003c3ffeaf74a903e107c0000003c00078000003c01e0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000000000000000000000000000000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffccc6fc03ffeabf28be0157c000000000003c00780000003c00078000003c01e00)]
def cols495 : IndexTree ColumnInfo := (.fork 7 (.fork 3 (.leaf [(1,0,494,0,10),(2,0,493,0,10),(4,0,491,0,10)]) (.leaf [(8,0,487,0,10),(0,32,460,3,9),(0,64,419,12,9),(32,0,463,0,9)])) (.fork 3 (.leaf [(64,0,431,0,9),(128,0,367,0,8),(256,0,239,0,8)]) (.leaf [(129,0,366,0,7),(132,0,363,0,7),(258,0,237,0,7),(264,0,231,0,7)])))
def levels495 : Nat → Packing
  | 7 => layer495r7
  | 8 => layer495r8
  | 9 => layer495r9
  | 10 => layer495r10
  | 11 => layer495r11
  | _ => emptyPacking
def index495 : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 2 0 4 0 0 keys495k8
  | 9 => lookupWord 5 30 4 8 4 0 keys495k9
  | 10 => lookupWord 9 69 2 9 5 0 keys495k10
  | 11 => lookupWord 2 19 0 7 3 0 keys495k11
  | _ => fun _ => none
def g495 : Forest := ⟨495,11,fun j => samples495[j]?.getD (0,0),cols495,#[[]],levels495,index495,noFactory,noFactorySound 495⟩
def packed503r7 (i : Nat) : Nat := 0x930c08f768c989de6683f6a2995d876a37aa97660c76d275d9931da44
def layer503r7 : Packing := (4,4,4,63,0,5,1,packed503r7)
def keys503k8 (i : Nat) : Nat := 0x1fc95b00
def packed503r8 (i : Nat) : Nat := 0x3060e9c0280060080c01000c00e00700380183043801c00e0040e5c46f893d7a38b3b230ad6be8a725a25f1bd89713d08d4a088037bb27442ed7dd93a21769fe4c4ef334f764e885da9fd32bb0ed9dd7660c769f74cb043b67b5d9821da7f532c00ed9f97660076c7ec390f335b764c7699addb243b4cd6f5911da66b7cc80ed3372f5d876912f3b263b4897ad921da44bdac88ed225ee6407691397cef334898dd7660c76
def layer503r8 : Packing := (22,3,4,63,0,8,1,packed503r8)
def keys503k9 (i : Nat) : Nat := 0x35000000000000000000000021b330000122e800000017400204074fb271745ee248b10f46282a9002b0000001d20009450
def packed503r9 (i : Nat) : Nat := 0xb2738cbd0226488b2644c4270089171cf2e0b1cb247173cb1e288d00a05308b0860047183081d0b1e4c024e00958108e00538221e04235300b2c78cc994bd72c4de262cad37d49cf2c58a8bd73c4ce26d4e273cb89b8cf2c74973cb1e24e33cb1d25beae8b5ab8a9a769022e8a216829fe739bc6a992619745714a498fc2e8901984209000ffe885dbff21e66ffe7799bff5da66dfc869deff21a77bfe885db7f9dd76dfd761dbbf61e66efc8799bbf9de66bfd8799b7f9de66efd7699bbf1da66fbe77913ef5da44fbc76913ef99a44cfd761daf760c76bed821dafd60476bf9801db3f9de66dbe77913af99a44
def layer503r9 : Packing := (28,2,4,63,0,10,1,packed503r9)
def keys503k10 (i : Nat) : Nat := 0xb6c30000000001e000538000102000000000000017600000000000007a0016a848000000babad5e00fd002020000000015700000ec0000000e4000000000000078289c6000000000000000000f8e6000000000001190034c00009748d6800000000a00000000000000000100
def packed503r10 (i : Nat) : Nat := 0x17ace514e274deb28cf1395759ca29c5095d2f59ca38a537ace51c4f4bd6728e272ce51c4bf7a548e2903e01ff9dffebb7fc76ffccd7f9df7f337be44
def layer503r10 : Packing := (7,1,4,63,0,8,1,packed503r10)
def keys503k11 (i : Nat) : Nat := 0xf86fb0042d690000000009000000
def packed503r11 (i : Nat) : Nat := 0x1d4c8626ff
def layer503r11 : Packing := (1,0,4,63,0,0,1,packed503r11)
def samples503 : Array (Bits × Bits) := #[(0x10480003b3301bb2c00330000643c06a40024003fff264f3330009ce7000fff,0x104a8281b33009b2d42b350a0241402a542a542950b22473335128c63512513),(0x20100004c03c24c30003ffff1b8b01b3800380030003873c3c000e739fff000,0x20101280c01400c300a9502b0b8b00b3812b812b04a2853c3c052a529053052),(0x260001803c338fc0003c000200c263c0003fffc000c183fffffff83e000000,0x2618188014338fc0c1bc3060000223c0c1acc1c3064081555307f83e30a30a),(0x0,0x0),(0x60fc03c0fffffc0000c3f0383ffffc0000000fe03fc0000ffc0000000,0x7a0d40140d7407c001e42d0283ec07c007801efe03fc0036ffc003a03a),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc380007f0003ff0000000000fc003fc000000000000fffc000000ffffffffff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc385257e0003f60029500a54f4003f402a502a50a94d5a8000aa45294aacaac),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00007ffffc000000000000ffffc00000000000000ffffffffff0000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc063677febc000031e00c78ffffc00033603360cd8bf7eaaacf80000cf0cf0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800000000000000000fffffffffffffffffff00000000000000000000,0x649038000000000001800060bd2e95c1038103820e000000000c000000c00c0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9b6fc05f2beabf28be02af80000000003c003c00f000000000f000000f00f00)]
def cols503 : IndexTree ColumnInfo := (.fork 7 (.fork 3 (.leaf [(0,64,435,4,10),(1,0,502,0,10),(2,0,501,0,10)]) (.leaf [(16,0,487,0,10),(64,0,439,0,10),(0,32,468,3,9),(4,0,435,0,9)])) (.fork 4 (.leaf [(32,0,471,0,9),(4,64,435,0,9),(256,0,247,0,8),(0,4,307,192,7)]) (.leaf [(128,0,375,0,7),(258,0,245,0,7),(272,0,231,0,7),(129,0,374,0,6)])))
def levels503 : Nat → Packing
  | 7 => layer503r7
  | 8 => layer503r8
  | 9 => layer503r9
  | 10 => layer503r10
  | 11 => layer503r11
  | _ => emptyPacking
def index503 : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 5 0 6 2 0 keys503k8
  | 9 => lookupWord 7 41 4 9 5 0 keys503k9
  | 10 => lookupWord 9 101 1 9 5 0 keys503k10
  | 11 => lookupWord 2 19 0 7 3 0 keys503k11
  | _ => fun _ => none
def g503 : Forest := ⟨503,11,fun j => samples503[j]?.getD (0,0),cols503,#[[]],levels503,index503,noFactory,noFactorySound 503⟩
def packed447r10 (i : Nat) : Nat := 0x1ff
def layer447r10 : Packing := (1,0,0,63,0,0,1,packed447r10)
def samples447 : Array (Bits × Bits) := #[(0x900001baab2c02cb00cc000086a4a90093e403ff9ce739ce700ff,0x9410009aab2d0acb42cd080002a4a942916509438c6318c634243),(0x22000024ccc30030c00fffc031b38ce00e3380300e739ce739ff00,0x22090000ccc302b0c0a542c010b38ce12e3384b12a5294a5291312),(0x10c00b338f0fc003f000f0024c63c0f000fc3ffc00f83e0f83e0000,0x10cc3b338f0fc31bf0c6f31a4423c0f0c6b42f1cc6f83e0f83ecaca),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe3000c3c0ff00003ffff00038f83ff0000ffc00000ffc00ffc00000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe301bc140ff0007b5d1f007b8f83ff0036ffc0d836ffc00ffc03a3a),(0xfc00ffffffc00000003f003ffffff00000000fffff00000000,0x3d400ffd741c0006001ad003edfb0700001806fffff00000a0a),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000ffff000000000000003fffc00000000000000fffffffffffff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc092fff6000025000940253fef40000a4000290a45294a5294acac),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000003ffffffffffffffffff0000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe721c00000000060001800612bdc1204384a90e2380000000003030),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000000000000000000000000000000,0x18de02abf0028b80a2e0ab8000000000c0000300c0000000000c0c0)]
def cols447 : IndexTree ColumnInfo := (.leaf [(4,0,443,0,10)])
def levels447 : Nat → Packing
  | 10 => layer447r10
  | _ => emptyPacking
def index447 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g447 : Forest := ⟨447,10,fun j => samples447[j]?.getD (0,0),cols447,#[[]],levels447,index447,noFactory,noFactorySound 447⟩
def packed511r8 (i : Nat) : Nat := 0x6330d80bd5d2dd68b1572ad50a55127d38994b24d208d4521d08813f1ecf075391bcd8693318cc05d2d15ca8512712c9045210fc78391b0cc602d1509c48210f06c30150903c18090300c00c9bdb86dda4a658787bdcaaed8765087979dc4aed8764c8797adc4aed876488797b5c4aed876448797b9c4aed876408787bdc42e5a7a2277c1bdc46e6aa61c87c1bdb96d2aa61c8790fdc9aed8765887917dc9aed8765487c1bdcaaed8765087a1bdcaaed8765087a1bccbaa98765087c1bebbaa9876508791bdc9aed8765087b0becc61d9665087b13ecc61d956508791ddc9aed8764c87b0decc61d9664c87b19ecc61d9464c8791edc9aed8764887b0eecc61d9664887b1aecc61d9464887b1cecc61d936488791f5c9aed8764487b176cc61d9564487b1b6cc61d9464487b1e6cc61d926448791f9c9aed8764087b17acc61d9564087b1bacc61d9464087b1dacc61d9364087b1f2cc61d916408781fdca2e68821e77a1bcc9a21a421e7788fdcaaed8721e6688fccbaa98721e66a8becc61da421e66c8bebb61da421e66e83d87695a421e66e89d87691a321e66e8ad87691a221e66e8cd8768da221e66e87587695a121e66e8b587691a121e66e8e587689a121e66e87987695a021e66e8b987691a021e66e8d98768da021e66e8f187685a021e66897dcaaed8721e55897ccbaa98721e55a93ecc61da421e55c93ebb61da421e55e83d87699a421e55e85d87699a321e55e91d87691a321e55e86d87699a221e55e92d87691a221e55e94d8768da221e55e93587691a121e55e96587689a121e55e93987691a021e55e9598768da021e55e97187685a021e55d83d876d08799a55
def layer511r8 : Packing := (67,5,5,63,0,9,1,packed511r8)
def keys511k9 (i : Nat) : Nat := 0xd7447b5ec1df70d0042c16e5fab00069cd4a0204530f935aca540000014810300ba620015f8000008f846907e370458800002ea7c004a2f69809c9037743e60867a6847406c18ae784001db139226cc114aad001c53608aa03383959dbc313c54d203b056411daf272010020b258658000600200b046001082
def packed511r9 (i : Nat) : Nat := (if i < 1 then 0xaa98721e8fe5d532c390f0ff6e6aa61c878bfb735530e43d8febb61d9621ecbf5db0eca90fc6faed8765087a77d76c3b2843d5bebb61d9421ecdf5db0eca10f577aed8764c87b3bd76c3b2643e3eeaaa219221e9f75db0ec910f67baed8764887abed76c3b2243d9f6bb61d9121f1fd55510c810f4feaed8764087b3f576c3b2043e1fda92a6889decdeda153444ef4ef6d0a9a22778f7b6854d113be1fd9869e889de6deda554c3cef47f2e68821e77d37d10d210f3bcddebb68c879df4ef4434643cefa7ba21a221e779bed76d090f3be9f688684879df4fd4434043cefa3f69ca7a22669d7b695530f3358febb61c8799b47f5530e43ccde1f61da521e669d7d76d210f336abe886908799b55ec3b4843ccdb2f61da421e66f17b0ed210f336e3da56908799a76f5db4643ccdab7a21a321e66d9bb0ed190f3378dd8768c8799b72ed2b4643ccdba7691a321e669ddd76d110f336aee886888799b576c3b4443ccde3b61da221e66dcdb4ad110f336eada46888799b766d1b4443ccd3bdaeda121e66d5ed10d090f336cf5876848799bc7ac3b4243ccdb9d695a121e66dd6b48d090f336ed5a36848799b772d134243ccd3beaeda021e66d5f510d010f336af9876808799bc7cc3b4043ccdb9e695a021e66dd7348d010f336ed9a36808799b774d134043ccdbbc685a021e66d1fb50544ef335cbdb421e7799ae6ed990f3bccd73b6c8879de66b9eb6243cef335cf9b021e7799b4bed394f444ab3cf6d2aa61e55b2fd76c390f2ae97eaa61c87957c3ec3b4c43cab3cfaeda421e55d67d10d210f2aeb3d876908795769ec3b4843cabe4f61da421e55dc7b4cd210f2acf5ebb68c879575af4434643cabb5761da321e55f2bb0ed190f2aee5da668c8795778ed234643cab3dbaeda221e55d6dd10d110f2aeb6d8768887957cb6c3b4443cabb9b699a221e55de5b48d110f2aef4da3688879567bb5db4243cabadda21a121e55daeb0ed090f2af975876848795773ad334243cabbcd691a121e55deab46d090f2aef65a2684879567bd5db4043cabadea21a021e55d6f30ed010f2af979876808795773cd334043cabbce691a021e55deb346d010f2aef69a2680879577b8d0b4043caba5f6a0a89de55ba7b6843cef2add5db321e77956eb6d910f3bcab75d6c4879de55baf36043cef2af87d8721e66956f1eda10f334ab7976cc8799a55bcdb6443ccd2ade75b121e66956f3cd810f334abe1fa227799a5583fb735530e43c1fcbaa658721e8df5db0eca10f86faa98765087e17b0ecb32843f13d876559421f86ec3b2cc990fc6761d9464c87e1db0ecb32443f1ad876519221f8e6c3b26c910fc5d61d9564487e36b0eca32243f1e5876499121f8bcc3b2ac810fc6e61d9464087e3b30ec9b2043f1f1876459021f45ec3b4843ccda4f61da421e55 else 0x6484c90b8017003071b8b1410410400010010410792183c80800410692100080080002002000080003c00810700182000000000003800c1041000001c8878108000107001e042000041c007810f021000020e043c087800f021000020a0434086810d001a04200000000007001820820000038f0f021000020e043c084000083810f021e042000041c007810f001e0420000414006810d021a0034084000000002080000000004f93c7e2f0f826f1f8bc3e0f24be3f1787c1278fc5e1f04966f1f8bc3e006cd65f1f8bc3e006cc0fb378bc3e0f24c0ff1787c00d941966f1f87c1e49819e3f0f801b283c19e1f0792507597c7e2f079260778fc5e006ca0e0678fc1e4941765f1f8bc3e49817e3f17841b283c17e2f0f9250702fc7e2f24b64f1f8bc3e096c9e3f1787c12cb94b64b34b04ad4a5c9e496c8f48c48047d47a47747447146e46b46846546245f45c454c51c4a44744444143e436c33c30c2dc2ac27c24c21c1ec1bc18c15c12c0fc0cc09c023ff3fc3f4bf1beebebbe8be5be2bdfbdcbd9bd23cf3cc3c93c63c33c03bd3b5bae3ab3a83a53a239ab9339038d38a38737fb78370b6db6ab67b64b5d355b4e346b43b40b3db3ab3332bb2431cb1531230f30c3093063033002f8af5af2aefaecae9ae6ae3adc2d4ad1aceacbac8ac12b9ab6ab3ab0aadaa629ea9729429128e28b283a7c274a6d26a267264261259a5224aa4323ba38a35a32a2fa2ca29a26a23a20a1da1aa17a149f69dd1c81b319517715913f9219080ee8d08b709d87f86604c83301980067bdb86929961f3dedbb494cb0f9ef6a1a4a6587cf7b4ed2532c3e9fda869e9961f5dedc3494cb0fb6f6dda4a6587d77b50d2532c3edbda76929961e3fedcd54c390f3ef6d2aa61c87af7d76c3b2843d7debb61d9321ebf75db0ec910f5fdaed8764487aff576c3b2043e7bdb42a6889debdeda153444ef1ff2e5a7a22779f7b695530f3bc9fdb9aa98721f0fedcd54c390fa6f6d2aa61c87a3fb735530e43d9bdb4)
def layer511r9 : Packing := (179,4,5,63,0,12,1,packed511r9)
def keys511k10 (i : Nat) : Nat := 0xcc704eed6f002ed33484162291e46cd63d20adad5f127430aebac8c8acee80049291923384bad46ab15c02a950e202e331b50e0010c089f867872748a8c44942ec915384ca645efc0001430ad337b2d95ac686478e6803a6521063e4f1062d16a7f90753bcb8aba83d8c4e14e198fa83ba08287d564a74378d046e000f2e001ac3824c74217c0647a6a3013b3f90d05191485801e6a469db3c001564000c70000001960a56000a5242c2e489949400062889a10364221b0ae000a540004cc001b12ee8531e0e00174e4d84f7d2bd08000001a816fe4f2ab1838cce8b6e82904000000000000000c05461c5bf4000cab5d54a26ab38f90796a0001c76128c7c21c0006f4485d59634546cdc33250b8a9ebc48f94b89794cee0953c6a84ca5d00b8dfd25d1df10cd25440018894bfe5e7227cd0d1040b02100c1092378000020451c000801844102000200082100208f0a1018430f400006a0406004818794140048e24789
def packed511r10 (i : Nat) : Nat := (if i < 1 then 0x42e215509c847412206502c8134062014ffc7f73f81fa4fcc7e33f01f64fa47cf3e41ef4f747b33d41e94f147633a61cc4e246f33661ac4d3467b32e18f4c345f72f01724b5c5932b81534a5c51728013949944a7242118488442b20a0fe47bc3bb1cc0de46ac3371900c245dc2d31580a344d424b11408243dc1d70e006a432417b0b0053427412708a04041d40cf05e02a412c083038016408402b00037fda8a6587dff69e9961fbfda8a6587f7f69e9961ffbda4a6587bffaa98721f7fca9a2277dff662889deffda7a2277bffaa9879df3fd9725e88aff6a097a233fda8a6587d7f69e9961f7bda4a6587bef6929961f3fca9a2187e7faa98721ebfeaa61c87b7faa98721f7bd8765087df761d9321f7ed8764887dfd61d9121f7f98764087d7f660989df9fda9a2277e7f2a6889df9fd98a2277e7f262889de7fda726277b7f69c989df3fca9a2277e7f69e889df9fca7a22779ff2a6889df3fd98a2277b7f69e889dedfeaa61e77b7f2a5879df9fe8861e77e7fa20879dfafda7a2266ebf29e8899aefda7a2266bbf29e8899aefeaa61e66ebfa218799aefeaa21e66ebfa208799bafd8721e66f3f61c8799be7da521e66faf6908799bedda321e66fbb6888799bef5a121e66fbe6808799bcfda89de66f3f2a27799bcfe889de66bbf6a27799aefca89de66ebfa227799bcfd879de66f3f21e7799bb7da7a2255edf29e88956f7da7a2255bdf29e88956f7eaa61e55edfa2187956f7eaa21e55edfa2087957b7d8721e55f5f61c87957e7da621e55fcf69087957f5da321e55fdb68887957f75a121e55fde68087957d7da89de55f5f2a277957d7e889de55bdf6a277956f7ca89de55edfa2277957d7d879de55f5f21e77957e7e8899a55f9f61e66957e7c8799a55f9f9de669571fd9725e889ef6929961e9feaa61c87c7fa658721f8fd8765887e5f61d9521f67d96654879efaa99421f3be8865087cef61d9421f5bd8765087e6f61d9421f6bd9665087dcf6559421e7deaa64c87cf7a219321f5dd8764c87e7761d9321f6dd9664c87dd76559321f79d9464c879fbaa99221f3ee8864887cfb61d9221f9ed8764887dbb6599221f76d9564887deb6519221f7cd93648879fdaa99121f3f68864487d7d61d9121f9f58764487dbd6599121f7759564487ded6519121f7d59364487df96499121e7faaa64087cfea219021f3f98764087e7e61d9021f6f99664087dde6559021f7b99464087df664d9021f7e99264087dfc6459021f1fd9826277b6f690879deddda321e77b7b688879dedf5a121e77b7e680879df8fd8721e66baf6908799aedda321e66bbb6888799aef5a121e66bbe6808799b8fe889de66e5f61c87956f3da421e55bd768c87956f6da221e55bdd68487956f79a021e55e5fa2277957a7e8899a55f1f9de669571bd8765087 else 0x1040c10b042c90e362c50410400127005c10f043d1cfcdcbc7c5c3c147473f372b271f170f052140f243040d0cecccbc7c5c3c1494b433b332d1f170f07252d0cecccbc745c3c1c94b433b332f1f150f07252d0cecccbc7c5c341c9480d0cec8c6c4c2c13c000012100e0c0bc7c5c3c1c95127005c10800050403830284f271f170f057410e0438108482134815352c5041800e003810d2024e0c48464443804144452c5041910e443910e443910e4430400600380080c80a432c5041800e003810d202500a484644438041443d3450418f0e3c38f0e3c38f0e3c30400600380080c80a3b34403242508f10013c9c7c5c3c1373f3327472f1f170f053c7c5c3c1c92f1f170f07204cd4dc3c1c7c5c8133d2f1f170f07204ce1412cd4bc9c7c5c3c04f1f170f00806cdc7c5c3c0212f372f1f170f006cfcdcbc7c5c3c0213f372f1f170f006cfcacdc7c5c3c0141b47332f1f170f00506d1c9c5c3c01f2f27170f007cbcdc3c5c1c81f37370f1707207cdcacdc9c5c3c0121f47304b2f27170f007d1d1cbc5c3c01e1b3f271f0f0064a15c9c7c3c12f37071f0f2064dcdc1c7c3c819372b37271f0f0050651cc14cbc9c7c3c0194747286f1f0f0050651d1cbc9c3c01e193f271f170074bc9c7c5c01d2f2f1f17072074dcbc7c5c1c81d37284b37271f1700751cccbc9c7c5c0121d47472f1f1700706cfd1ca1e13c9c5c01d47472f271f007064fc9c7c5c2172857271f170cbcbc5c7c3c817372f171f0f205cdca14cdc9c7c5c21747332f271f1708505d1d1ca1bc7c5c2141747472f271708785cfd1ca1815c9c7c21747472f271f10705ce13c9c7c5c3c1371f170f006ca13c9c5c3c12f271f0f0064a13c9c7c5c12f271f17085cb91c7c5c3c1c9371f170f049c9c5c3c127271f0f049c9c7c5c127271f170c9c9c7c5c3c12e3f1f170f0724dc7c5c3c12727170f049c9c7c3c127271f17049c9c7c5c327271f170f04bc9c7c5c3c12f271f170f04a1bcfcd49d1cbc7c5c3c155a82d3568cb3f59c2cb5654b275922c8563cb135862c155c4abb55a2ab5554aa75402965464a0b4f227853849bf4de26e531c9834be25e52ec9474a024e526492b490245522490f48424051f48f346823151848bf45c22c51548a344e225512488f44622150fc87b43a21a50cc863)
def layer511r10 : Packing := (165,3,5,63,0,13,1,packed511r10)
def keys511k11 (i : Nat) : Nat := 0x1e58656aee877e0652f466082cffc3e2fab0930600baaba386000004e2c5a000f1f54090fc7c268e8591c7200016b32e928046eb2400000022508dc7ee0e3456022ed88b3304b82c2901edcf328a76df0cb9174174bde4f41e0d3c1cee0608a3c29a9468ae8211392a292a00061ad14000000a7a000505926000611a13c5f6fc00180c0000700ceeb000000082bd128220010b753502929e001a8e000894cebc2c5236d7ebac72890001a272c400090c31a0000010f20002a902ec05845e64ce52f7a75b0a001046718000242000ad044db10e18849eb493db370ad6935420f9a5dca0c6c0f4e61cbfaf0ac68da478cc164bc96c410cc88852de3293ea3a687ee7850e5314829d2d52d98c952963506a830e54e1453a4a4e36702862898282801be8304000640f000c302001018a001c804100c00016035b1b4b400c0c167010611c05040000f00f83250000014
def packed511r11 (i : Nat) : Nat := 0x992e8cf8b064c784554284e8cf9b2e3c587064ae4288e9e345138f161c19055aa13a64b1a2e3c587064136264ba33e3c39316013548511d3c64d1528a13931e2c382f90a23a74c94563c587064136a84f931e2c380550294274c97160c98f0d597466cf8f0e4c580555a33e6cb8b064c7844d4284e7cda32e3c587064ac5488f1a289c78b0e0c9587119b38ac98f161c026b8d17263c58700aa3365c787160c8268cd97160c78720aa32a615931e2c3804d39928ac98f161c0269cf9b28ac78b0e01b4e7cd944e4c58700fa73e6ca2b263c3806539f36513931e2c03a9cf9b28ac98f161174a84f931e2c3804d0254274c971e1c98b05427467cd97263c58705597466cf8b064c7844d5a33e6cb8f0e4c5805542b467cd97263c587054254274c94563c587064ad325c98f161c0268cf96364c78b0e0a13a58d8f161c19284e97263c587048a33e58d931e2c3828d19a2e4c78b0e0a14268b8f161c1928509b263c587047a34668b931e2c3828139f368cb8f161c192ace90566ca371e2c382ace8c4e6ca3f262c382ace88566ca33263c382ace844e6ca3b263c582ace80566ca2f263c586acf9b465c98f161c14e7cb1b263c5870519f2c6c98f161c1468cd17263c587051a3345c98f161c14268b931e2c3827e59e06da5d4bcffc90c2fbf1ba5b59b0dabaa67a149d699895a9158d088b8468017bc7777396ed6a16556095bd56a52c4ee4b04724343f63b837a33c2f02a425820c1c017412f0f10b3075037000ffe4bd11ffe9961fffd10c3fff61c87ffe4c4efffe889dfffb0f3beff65e88dfe4bd117fd97a22ff92f445ffa6587dff4430f7fe9921f7fd1043eff61c87efec390fefd9621fefb2a43fef65087feec990ffed9221ffeb2243ffe64087efecc4efdfc989dfbfd113bdff66277bfe4c4efbfe889dfbfb0f3bf7f21e77f7f444cdefd8799bdf90f337bf9de66fbf444abf7d87957ef90f2afdf9de55cfec390f7bd9421efbb2643dfb64887bfac890f7f99021f3fd113bebfa2266e7f3bccdb7e88957afcef2af9f99a55
def layer511r11 : Packing := (52,2,5,63,0,12,1,packed511r11)
def keys511k12 (i : Nat) : Nat := 0x442a20b7471c00042a5e8a2890036f895cc23ae6000e0834006100090800c76dc97ed362df1002b32152ac18a75a7d2545d9e3d18c93d7a207275bc3602d5152e30036e4b000d6d6b868e120610076800cf00e841940401001
def packed511r12 (i : Nat) : Nat := 0x2a79a89648e2860aa79a89638a1824a4a1852679a89648e2860b499e6a259238a182a9e6a259238a18299e6a259238a18299e51a48e2860a289859238a1828db5ea4ce4541b06c00ffe88ffd87ffc87ffe77bfe88dfe77efe66f7e55
def layer511r12 : Packing := (8,1,5,63,0,9,1,packed511r12)
def keys511k13 (i : Nat) : Nat := 0x15683c03a9dac00000010e0
def packed511r13 (i : Nat) : Nat := 0x3990520c41053ff
def layer511r13 : Packing := (1,0,5,63,0,0,1,packed511r13)
def samples511 : Array (Bits × Bits) := #[(0x402400003b2cc001baab2c000b2c000cc00001900f0021a92a400093e4000ffff04c13accccacc000cc0009ce739ce70003fff,0x402540501b2cc0009aab2d40ab2d40acd40a0090050000a92a540a916540a540b04411accccacd412cd4128c6318c635049413),(0x808800004c00f0024ccc30000c30000fffff06e32c00c6ce338000e338000c0000701ccf0f0cf0000f0000e739ce739fffc000,0x80880a500c0050000ccc300aac300aa540ab02e32c0042ce33814ae33814ac14a05014cf0f0cf0152f0152a5294a529054c152),(0x4300001800f0b338f0fc0000fc0000f00000800309318f03c0000fc3ffff000098260f00fff00000ffffff83e0f83e0000000,0x430c03080050b338f0fc0c06fc0c06f0c060000009108f03c0c06b42cc070c0688220f0055f00c0654c07f83e0f83e3028c0a),(0x8c0000200300c3c0ff000000ffffff000003003c0e3e0ffc00000ffc00000000e0380fff00ffffff00000ffc00ffc00000000,0x8c0063000000c140ff000066d7406700066100140e3e0ffc000c6ffc00c600c6a0280f5500f540c7000c6ffc00ffc003280ca),(0xc0fc00fc00ffffffff00000000000c0fc00fc00ffffffff00000000000ffc00fffff00000000000fffff00000000000,0xf40d400d400ffd7401f00001e0001e40b400b400fb7ec01f000001e001effc00fffff00003600036fffff000000e803a),(0xffffffffffffffffffffffffff0f00000ff0000ffff0000000000000000000ff0000ffff0000000000000000000fffff0000000000000000ffffffffffffffff,0xffffffffffffffffffffffffff0f0294afe0000fff60000295400295402954fd0000ffbd00002a940002a942a94fabea00000002aa402aa45294a5294aab2aac),(0xfffffffffffffffffffffffffff000000ffffff00000000000000000000000ffffff00000000000000000000000fffffffffffffffffffff0000000000000000,0xfffffffffffffffffffffffffff00318cf7ffaf00000000319800319803198effebf0000000033180003318331857d5f0aaaa0ab338ab338000000000ccc3330),(0xfffffffffffffffffffffffffffffffff00000000000000000000000000000fffffffffffffffffffffffffffff0000000000000000000000000000000000000,0x199c81f00000000000000001e00001e0001e0bf4bfa4af7048103e04a903e083e000000000000003c0003c00000000000f003c0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000,0xfffffffffffffffffffffffffe6637e00bf2bfa2abf0028be0028be00abe00000000000000003c000003c003c000000000000003c0003c00000000000f003c00)]
def cols511 : IndexTree ColumnInfo := (.fork 8 (.fork 4 (.leaf [(1,0,510,0,12),(2,0,509,0,12),(4,0,507,0,12),(8,0,503,0,12)]) (.leaf [(16,0,495,0,12),(0,32,476,3,11),(0,64,435,12,11),(32,0,479,0,11)])) (.fork 4 (.leaf [(64,0,447,0,11),(128,0,383,0,9),(256,0,255,0,9),(129,0,382,0,8)]) (.fork 2 (.leaf [(132,0,379,0,8),(144,0,367,0,8)]) (.leaf [(258,0,253,0,8),(264,0,247,0,8),(272,0,239,0,8)]))))
def levels511 : Nat → Packing
  | 8 => layer511r8
  | 9 => layer511r9
  | 10 => layer511r10
  | 11 => layer511r11
  | 12 => layer511r12
  | 13 => layer511r13
  | _ => emptyPacking
def index511 : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 22 76 6 11 7 0 keys511k9
  | 10 => lookupWord 59 203 7 12 8 0 keys511k10
  | 11 => lookupWord 55 190 7 12 8 0 keys511k11
  | 12 => lookupWord 17 61 6 10 6 0 keys511k12
  | 13 => lookupWord 2 19 0 7 3 0 keys511k13
  | _ => fun _ => none
def g511 : Forest := ⟨511,13,fun j => samples511[j]?.getD (0,0),cols511,#[[]],levels511,index511,noFactory,noFactorySound 511⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom400 : graphValid g400 (boundsBefore []) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice400k3p0 : block g400 3 0 1 = true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK400k3 : block g400 3 0 1=true := slice400k3p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked400 : checkedTables g400 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g400 0 0 0=true)
  · exact (rfl : block g400 1 0 0=true)
  · exact (rfl : block g400 2 0 0=true)
  · exact layerOK400k3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low400 : Lower (vars 400) (graphGoal 400) 4 :=
  lower_forest (g:=g400) (i:=0) (hints:=18254069760) (before_sound [] baseKnown) geom400 checked400 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps400 : List (Nat × List Nat) := [(400,[])]
def known400 := extendKnown [] 4 maps400
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid400 : Known known400 := extendKnown_ok baseKnown low400 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom163 : graphValid g163 (boundsBefore known400) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice163k3p0 : block g163 3 0 1 = true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK163k3 : block g163 3 0 1=true := slice163k3p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked163 : checkedTables g163 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g163 0 0 0=true)
  · exact (rfl : block g163 1 0 0=true)
  · exact (rfl : block g163 2 0 0=true)
  · exact layerOK163k3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low163 : Lower (vars 163) (graphGoal 163) 4 :=
  lower_forest (g:=g163) (i:=0) (hints:=85) (before_sound known400 valid400) geom163 checked163 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps163 : List (Nat × List Nat) := [(163,[]),(177,[117,65,49,33]),(197,[117,101,32,16]),(212,[117,101,65,49,32]),(291,[135,16]),(387,[80,133,101,112,16]),(417,[129,117,97,65,49,33]),(418,[81,129,117,97,65,49,16,32]),(452,[81,113,133,97,65,49,32])]
def known163 := extendKnown known400 4 maps163
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid163 : Known known163 := extendKnown_ok valid400 low163 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom401 : graphValid g401 (boundsBefore known163) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice401k4p0 : block g401 4 0 1 = true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK401k4 : block g401 4 0 1=true := slice401k4p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked401 : checkedTables g401 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g401 0 0 0=true)
  · exact (rfl : block g401 1 0 0=true)
  · exact (rfl : block g401 2 0 0=true)
  · exact (rfl : block g401 3 0 0=true)
  · exact layerOK401k4
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low401 : Lower (vars 401) (graphGoal 401) 5 :=
  lower_forest (g:=g401) (i:=0) (hints:=17180327943) (before_sound known163 valid163) geom401 checked401 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps401 : List (Nat × List Nat) := [(401,[]),(402,[135,16])]
def known401 := extendKnown known163 5 maps401
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid401 : Known known401 := extendKnown_ok valid163 low401 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom167 : graphValid g167 (boundsBefore known401) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice167k4p0 : block g167 4 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK167k4 : block g167 4 0 1=true := slice167k4p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked167 : checkedTables g167 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g167 0 0 0=true)
  · exact (rfl : block g167 1 0 0=true)
  · exact (rfl : block g167 2 0 0=true)
  · exact (rfl : block g167 3 0 0=true)
  · exact layerOK167k4
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low167 : Lower (vars 167) (graphGoal 167) 5 :=
  lower_forest (g:=g167) (i:=0) (hints:=1877) (before_sound known401 valid401) geom167 checked167 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps167 : List (Nat × List Nat) := [(167,[]),(179,[66,50]),(229,[32,16,97,65,114,49,80]),(307,[135,66,50,16])]
def known167 := extendKnown known401 5 maps167
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid167 : Known known167 := extendKnown_ok valid401 low167 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom419 : graphValid g419 (boundsBefore known167) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice419k5p0 : block g419 5 0 5 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice419k5p5 : block g419 5 5 10 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK419k5 : block g419 5 0 15=true := (@block_merge g419 5 0 5 10 slice419k5p0 slice419k5p5)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice419k6p0 : block g419 6 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK419k6 : block g419 6 0 1=true := slice419k6p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked419 : checkedTables g419 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g419 0 0 0=true)
  · exact (rfl : block g419 1 0 0=true)
  · exact (rfl : block g419 2 0 0=true)
  · exact (rfl : block g419 3 0 0=true)
  · exact (rfl : block g419 4 0 0=true)
  · exact layerOK419k5
  · exact layerOK419k6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low419 : Lower (vars 419) (graphGoal 419) 7 :=
  lower_forest (g:=g419) (i:=0) (hints:=4294967381) (before_sound known167 valid167) geom419 checked419 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps419 : List (Nat × List Nat) := [(419,[]),(460,[101,49,32])]
def known419 := extendKnown known167 7 maps419
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid419 : Known known419 := extendKnown_ok valid167 low419 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom433 : graphValid g433 (boundsBefore known419) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice433k5p0 : block g433 5 0 3 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice433k5p3 : block g433 5 3 4 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK433k5 : block g433 5 0 7=true := (@block_merge g433 5 0 3 4 slice433k5p0 slice433k5p3)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice433k6p0 : block g433 6 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK433k6 : block g433 6 0 1=true := slice433k6p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked433 : checkedTables g433 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g433 0 0 0=true)
  · exact (rfl : block g433 1 0 0=true)
  · exact (rfl : block g433 2 0 0=true)
  · exact (rfl : block g433 3 0 0=true)
  · exact (rfl : block g433 4 0 0=true)
  · exact layerOK433k5
  · exact layerOK433k6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low433 : Lower (vars 433) (graphGoal 433) 7 :=
  lower_forest (g:=g433) (i:=0) (hints:=17180327941) (before_sound known419 valid419) geom433 checked433 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps433 : List (Nat × List Nat) := [(433,[]),(434,[135,16]),(468,[101,32,16])]
def known433 := extendKnown known419 7 maps433
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid433 : Known known433 := extendKnown_ok valid419 low433 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom403 : graphValid g403 (boundsBefore known433) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice403k5p0 : block g403 5 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK403k5 : block g403 5 0 1=true := slice403k5p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked403 : checkedTables g403 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g403 0 0 0=true)
  · exact (rfl : block g403 1 0 0=true)
  · exact (rfl : block g403 2 0 0=true)
  · exact (rfl : block g403 3 0 0=true)
  · exact (rfl : block g403 4 0 0=true)
  · exact layerOK403k5
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low403 : Lower (vars 403) (graphGoal 403) 6 :=
  lower_forest (g:=g403) (i:=0) (hints:=4295426183) (before_sound known433 valid433) geom403 checked403 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps403 : List (Nat × List Nat) := [(403,[])]
def known403 := extendKnown known433 6 maps403
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid403 : Known known403 := extendKnown_ok valid433 low403 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom235 : graphValid g235 (boundsBefore known403) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice235k5p0 : block g235 5 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK235k5 : block g235 5 0 1=true := slice235k5p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked235 : checkedTables g235 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g235 0 0 0=true)
  · exact (rfl : block g235 1 0 0=true)
  · exact (rfl : block g235 2 0 0=true)
  · exact (rfl : block g235 3 0 0=true)
  · exact (rfl : block g235 4 0 0=true)
  · exact layerOK235k5
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low235 : Lower (vars 235) (graphGoal 235) 6 :=
  lower_forest (g:=g235) (i:=0) (hints:=50356309) (before_sound known403 valid403) geom235 checked235 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps235 : List (Nat × List Nat) := [(246,[117,101,65,49,32]),(359,[135,50,16]),(374,[133,117,65,49,16,32])]
def known235 := extendKnown known403 6 maps235
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid235 : Known known235 := extendKnown_ok valid403 low235 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom231 : graphValid g231 (boundsBefore known235) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice231k6p0 : block g231 6 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK231k6 : block g231 6 0 1=true := slice231k6p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked231 : checkedTables g231 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g231 0 0 0=true)
  · exact (rfl : block g231 1 0 0=true)
  · exact (rfl : block g231 2 0 0=true)
  · exact (rfl : block g231 3 0 0=true)
  · exact (rfl : block g231 4 0 0=true)
  · exact (rfl : block g231 5 0 0=true)
  · exact layerOK231k6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low231 : Lower (vars 231) (graphGoal 231) 7 :=
  lower_forest (g:=g231) (i:=0) (hints:=33556053) (before_sound known235 valid235) geom231 checked231 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps231 : List (Nat × List Nat) := [(231,[]),(237,[101,49,32]),(363,[135,50,16]),(366,[135,101,33,48]),(486,[112,97,128,64,81,33,48])]
def known231 := extendKnown known235 7 maps231
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid231 : Known known231 := extendKnown_ok valid235 low231 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom245 : graphValid g245 (boundsBefore known231) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice245k6p0 : block g245 6 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK245k6 : block g245 6 0 1=true := slice245k6p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked245 : checkedTables g245 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g245 0 0 0=true)
  · exact (rfl : block g245 1 0 0=true)
  · exact (rfl : block g245 2 0 0=true)
  · exact (rfl : block g245 3 0 0=true)
  · exact (rfl : block g245 4 0 0=true)
  · exact (rfl : block g245 5 0 0=true)
  · exact layerOK245k6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low245 : Lower (vars 245) (graphGoal 245) 7 :=
  lower_forest (g:=g245) (i:=0) (hints:=34014725) (before_sound known231 valid231) geom245 checked245 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps245 : List (Nat × List Nat) := [(245,[]),(455,[128,48,49,81,64]),(485,[132])]
def known245 := extendKnown known231 7 maps245
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid245 : Known known245 := extendKnown_ok valid231 low245 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom438 : graphValid g438 (boundsBefore known245) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice438k7p0 : block g438 7 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK438k7 : block g438 7 0 1=true := slice438k7p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked438 : checkedTables g438 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g438 0 0 0=true)
  · exact (rfl : block g438 1 0 0=true)
  · exact (rfl : block g438 2 0 0=true)
  · exact (rfl : block g438 3 0 0=true)
  · exact (rfl : block g438 4 0 0=true)
  · exact (rfl : block g438 5 0 0=true)
  · exact (rfl : block g438 6 0 0=true)
  · exact layerOK438k7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low438 : Lower (vars 438) (graphGoal 438) 8 :=
  lower_forest (g:=g438) (i:=0) (hints:=4833347408) (before_sound known245 valid245) geom438 checked438 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps438 : List (Nat × List Nat) := [(438,[]),(441,[135,50,16]),(470,[135,101,33])]
def known438 := extendKnown known245 8 maps438
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid438 : Known known438 := extendKnown_ok valid245 low438 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom437 : graphValid g437 (boundsBefore known438) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice437k7p0 : block g437 7 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK437k7 : block g437 7 0 1=true := slice437k7p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked437 : checkedTables g437 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g437 0 0 0=true)
  · exact (rfl : block g437 1 0 0=true)
  · exact (rfl : block g437 2 0 0=true)
  · exact (rfl : block g437 3 0 0=true)
  · exact (rfl : block g437 4 0 0=true)
  · exact (rfl : block g437 5 0 0=true)
  · exact (rfl : block g437 6 0 0=true)
  · exact layerOK437k7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low437 : Lower (vars 437) (graphGoal 437) 8 :=
  lower_forest (g:=g437) (i:=0) (hints:=17180329733) (before_sound known438 valid438) geom437 checked437 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps437 : List (Nat × List Nat) := [(437,[]),(469,[101,32])]
def known437 := extendKnown known438 8 maps437
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid437 : Known known437 := extendKnown_ok valid438 low437 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom423 : graphValid g423 (boundsBefore known437) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice423k7p0 : block g423 7 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK423k7 : block g423 7 0 1=true := slice423k7p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked423 : checkedTables g423 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g423 0 0 0=true)
  · exact (rfl : block g423 1 0 0=true)
  · exact (rfl : block g423 2 0 0=true)
  · exact (rfl : block g423 3 0 0=true)
  · exact (rfl : block g423 4 0 0=true)
  · exact (rfl : block g423 5 0 0=true)
  · exact (rfl : block g423 6 0 0=true)
  · exact layerOK423k7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low423 : Lower (vars 423) (graphGoal 423) 8 :=
  lower_forest (g:=g423) (i:=0) (hints:=4294969173) (before_sound known437 valid437) geom423 checked423 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps423 : List (Nat × List Nat) := [(423,[]),(427,[135,50,16])]
def known423 := extendKnown known437 8 maps423
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid423 : Known known423 := extendKnown_ok valid437 low423 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom435 : graphValid g435 (boundsBefore known423) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice435k5p0 : block g435 5 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK435k5 : block g435 5 0 1=true := slice435k5p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice435k6p0 : block g435 6 0 6 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice435k6p6 : block g435 6 6 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK435k6 : block g435 6 0 7=true := (@block_merge g435 6 0 6 1 slice435k6p0 slice435k6p6)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice435k7p0 : block g435 7 0 3 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice435k7p3 : block g435 7 3 4 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK435k7 : block g435 7 0 7=true := (@block_merge g435 7 0 3 4 slice435k7p0 slice435k7p3)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice435k8p0 : block g435 8 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK435k8 : block g435 8 0 1=true := slice435k8p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked435 : checkedTables g435 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g435 0 0 0=true)
  · exact (rfl : block g435 1 0 0=true)
  · exact (rfl : block g435 2 0 0=true)
  · exact (rfl : block g435 3 0 0=true)
  · exact (rfl : block g435 4 0 0=true)
  · exact layerOK435k5
  · exact layerOK435k6
  · exact layerOK435k7
  · exact layerOK435k8
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low435 : Lower (vars 435) (graphGoal 435) 9 :=
  lower_forest (g:=g435) (i:=0) (hints:=4295426133) (before_sound known423 valid423) geom435 checked435 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps435 : List (Nat × List Nat) := [(435,[]),(476,[101,49,32])]
def known435 := extendKnown known423 9 maps435
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid435 : Known known435 := extendKnown_ok valid423 low435 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom251 : graphValid g251 (boundsBefore known435) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice251k6p0 : block g251 6 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK251k6 : block g251 6 0 1=true := slice251k6p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked251 : checkedTables g251 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g251 0 0 0=true)
  · exact (rfl : block g251 1 0 0=true)
  · exact (rfl : block g251 2 0 0=true)
  · exact (rfl : block g251 3 0 0=true)
  · exact (rfl : block g251 4 0 0=true)
  · exact (rfl : block g251 5 0 0=true)
  · exact layerOK251k6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low251 : Lower (vars 251) (graphGoal 251) 7 :=
  lower_forest (g:=g251) (i:=0) (hints:=50815061) (before_sound known435 valid435) geom251 checked251 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps251 : List (Nat × List Nat) := [(375,[135,50,16])]
def known251 := extendKnown known435 7 maps251
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid251 : Known known251 := extendKnown_ok valid435 low251 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom239 : graphValid g239 (boundsBefore known251) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice239k7p0 : block g239 7 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK239k7 : block g239 7 0 1=true := slice239k7p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked239 : checkedTables g239 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g239 0 0 0=true)
  · exact (rfl : block g239 1 0 0=true)
  · exact (rfl : block g239 2 0 0=true)
  · exact (rfl : block g239 3 0 0=true)
  · exact (rfl : block g239 4 0 0=true)
  · exact (rfl : block g239 5 0 0=true)
  · exact (rfl : block g239 6 0 0=true)
  · exact layerOK239k7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low239 : Lower (vars 239) (graphGoal 239) 8 :=
  lower_forest (g:=g239) (i:=0) (hints:=33580629) (before_sound known251 valid251) geom239 checked239 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps239 : List (Nat × List Nat) := [(239,[]),(367,[135,50,16])]
def known239 := extendKnown known251 8 maps239
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid239 : Known known239 := extendKnown_ok valid251 low239 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom247 : graphValid g247 (boundsBefore known239) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice247k7p0 : block g247 7 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK247k7 : block g247 7 0 1=true := slice247k7p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked247 : checkedTables g247 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g247 0 0 0=true)
  · exact (rfl : block g247 1 0 0=true)
  · exact (rfl : block g247 2 0 0=true)
  · exact (rfl : block g247 3 0 0=true)
  · exact (rfl : block g247 4 0 0=true)
  · exact (rfl : block g247 5 0 0=true)
  · exact (rfl : block g247 6 0 0=true)
  · exact layerOK247k7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low247 : Lower (vars 247) (graphGoal 247) 8 :=
  lower_forest (g:=g247) (i:=0) (hints:=34014805) (before_sound known239 valid239) geom247 checked247 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps247 : List (Nat × List Nat) := [(247,[]),(253,[101,49,32]),(379,[135,50,16]),(382,[135,101,33,48])]
def known247 := extendKnown known239 8 maps247
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid247 : Known known247 := extendKnown_ok valid239 low247 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom487 : graphValid g487 (boundsBefore known247) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=2) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice487k7p0 : block g487 7 0 10 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice487k7p10 : block g487 7 10 6 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK487k7 : block g487 7 0 16=true := (@block_merge g487 7 0 10 6 slice487k7p0 slice487k7p10)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice487k8p0 : block g487 8 0 5 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice487k8p5 : block g487 8 5 11 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK487k8 : block g487 8 0 16=true := (@block_merge g487 8 0 5 11 slice487k8p0 slice487k8p5)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice487k9p0 : block g487 9 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK487k9 : block g487 9 0 1=true := slice487k9p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked487 : checkedTables g487 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g487 0 0 0=true)
  · exact (rfl : block g487 1 0 0=true)
  · exact (rfl : block g487 2 0 0=true)
  · exact (rfl : block g487 3 0 0=true)
  · exact (rfl : block g487 4 0 0=true)
  · exact (rfl : block g487 5 0 0=true)
  · exact (rfl : block g487 6 0 0=true)
  · exact layerOK487k7
  · exact layerOK487k8
  · exact layerOK487k9
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low487 : Lower (vars 487) (graphGoal 487) 10 :=
  lower_forest (g:=g487) (i:=0) (hints:=4328523349) (before_sound known247 valid247) geom487 checked487 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps487 : List (Nat × List Nat) := [(487,[]),(491,[135,50,16]),(493,[101,49,32]),(494,[135,101,33,48])]
def known487 := extendKnown known247 10 maps487
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid487 : Known known487 := extendKnown_ok valid247 low487 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom502 : graphValid g502 (boundsBefore known487) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=2) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice502k6p0 : block g502 6 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice502k6p1 : block g502 6 1 2 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK502k6 : block g502 6 0 3=true := (@block_merge g502 6 0 1 2 slice502k6p0 slice502k6p1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice502k7p0 : block g502 7 0 7 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice502k7p7 : block g502 7 7 9 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK502k7 : block g502 7 0 16=true := (@block_merge g502 7 0 7 9 slice502k7p0 slice502k7p7)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice502k8p0 : block g502 8 0 3 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice502k8p3 : block g502 8 3 6 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK502k8 : block g502 8 0 9=true := (@block_merge g502 8 0 3 6 slice502k8p0 slice502k8p3)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice502k9p0 : block g502 9 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK502k9 : block g502 9 0 1=true := slice502k9p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked502 : checkedTables g502 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g502 0 0 0=true)
  · exact (rfl : block g502 1 0 0=true)
  · exact (rfl : block g502 2 0 0=true)
  · exact (rfl : block g502 3 0 0=true)
  · exact (rfl : block g502 4 0 0=true)
  · exact (rfl : block g502 5 0 0=true)
  · exact layerOK502k6
  · exact layerOK502k7
  · exact layerOK502k8
  · exact layerOK502k9
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low502 : Lower (vars 502) (graphGoal 502) 10 :=
  lower_forest (g:=g502) (i:=0) (hints:=4866901584) (before_sound known487 valid487) geom502 checked502 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps502 : List (Nat × List Nat) := [(502,[])]
def known502 := extendKnown known487 10 maps502
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid502 : Known known502 := extendKnown_ok valid487 low502 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom501 : graphValid g501 (boundsBefore known502) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice501k6p0 : block g501 6 0 3 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK501k6 : block g501 6 0 3=true := slice501k6p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice501k7p0 : block g501 7 0 3 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice501k7p3 : block g501 7 3 10 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK501k7 : block g501 7 0 13=true := (@block_merge g501 7 0 3 10 slice501k7p0 slice501k7p3)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice501k8p0 : block g501 8 0 3 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice501k8p3 : block g501 8 3 4 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK501k8 : block g501 8 0 7=true := (@block_merge g501 8 0 3 4 slice501k8p0 slice501k8p3)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice501k9p0 : block g501 9 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK501k9 : block g501 9 0 1=true := slice501k9p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked501 : checkedTables g501 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g501 0 0 0=true)
  · exact (rfl : block g501 1 0 0=true)
  · exact (rfl : block g501 2 0 0=true)
  · exact (rfl : block g501 3 0 0=true)
  · exact (rfl : block g501 4 0 0=true)
  · exact (rfl : block g501 5 0 0=true)
  · exact layerOK501k6
  · exact layerOK501k7
  · exact layerOK501k8
  · exact layerOK501k9
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low501 : Lower (vars 501) (graphGoal 501) 10 :=
  lower_forest (g:=g501) (i:=0) (hints:=17213883909) (before_sound known502 valid502) geom501 checked501 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps501 : List (Nat × List Nat) := [(501,[])]
def known501 := extendKnown known502 10 maps501
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid501 : Known known501 := extendKnown_ok valid502 low501 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom445 : graphValid g445 (boundsBefore known501) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice445k8p0 : block g445 8 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK445k8 : block g445 8 0 1=true := slice445k8p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked445 : checkedTables g445 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g445 0 0 0=true)
  · exact (rfl : block g445 1 0 0=true)
  · exact (rfl : block g445 2 0 0=true)
  · exact (rfl : block g445 3 0 0=true)
  · exact (rfl : block g445 4 0 0=true)
  · exact (rfl : block g445 5 0 0=true)
  · exact (rfl : block g445 6 0 0=true)
  · exact (rfl : block g445 7 0 0=true)
  · exact layerOK445k8
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low445 : Lower (vars 445) (graphGoal 445) 9 :=
  lower_forest (g:=g445) (i:=0) (hints:=12885395205) (before_sound known501 valid501) geom445 checked445 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps445 : List (Nat × List Nat) := [(471,[101,49,32])]
def known445 := extendKnown known501 9 maps445
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid445 : Known known445 := extendKnown_ok valid501 low445 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom431 : graphValid g431 (boundsBefore known445) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice431k8p0 : block g431 8 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK431k8 : block g431 8 0 1=true := slice431k8p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked431 : checkedTables g431 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g431 0 0 0=true)
  · exact (rfl : block g431 1 0 0=true)
  · exact (rfl : block g431 2 0 0=true)
  · exact (rfl : block g431 3 0 0=true)
  · exact (rfl : block g431 4 0 0=true)
  · exact (rfl : block g431 5 0 0=true)
  · exact (rfl : block g431 6 0 0=true)
  · exact (rfl : block g431 7 0 0=true)
  · exact layerOK431k8
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low431 : Lower (vars 431) (graphGoal 431) 9 :=
  lower_forest (g:=g431) (i:=0) (hints:=4295001941) (before_sound known445 valid445) geom431 checked431 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps431 : List (Nat × List Nat) := [(431,[]),(463,[101,49,32])]
def known431 := extendKnown known445 9 maps431
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid431 : Known known431 := extendKnown_ok valid445 low431 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom439 : graphValid g439 (boundsBefore known431) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice439k9p0 : block g439 9 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK439k9 : block g439 9 0 1=true := slice439k9p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked439 : checkedTables g439 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g439 0 0 0=true)
  · exact (rfl : block g439 1 0 0=true)
  · exact (rfl : block g439 2 0 0=true)
  · exact (rfl : block g439 3 0 0=true)
  · exact (rfl : block g439 4 0 0=true)
  · exact (rfl : block g439 5 0 0=true)
  · exact (rfl : block g439 6 0 0=true)
  · exact (rfl : block g439 7 0 0=true)
  · exact (rfl : block g439 8 0 0=true)
  · exact layerOK439k9
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low439 : Lower (vars 439) (graphGoal 439) 10 :=
  lower_forest (g:=g439) (i:=0) (hints:=4295427925) (before_sound known431 valid431) geom439 checked439 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps439 : List (Nat × List Nat) := [(439,[]),(443,[135,50,16])]
def known439 := extendKnown known431 10 maps439
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid439 : Known known439 := extendKnown_ok valid431 low439 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom255 : graphValid g255 (boundsBefore known439) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k8p0 : block g255 8 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK255k8 : block g255 8 0 1=true := slice255k8p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked255 : checkedTables g255 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g255 0 0 0=true)
  · exact (rfl : block g255 1 0 0=true)
  · exact (rfl : block g255 2 0 0=true)
  · exact (rfl : block g255 3 0 0=true)
  · exact (rfl : block g255 4 0 0=true)
  · exact (rfl : block g255 5 0 0=true)
  · exact (rfl : block g255 6 0 0=true)
  · exact (rfl : block g255 7 0 0=true)
  · exact layerOK255k8
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low255 : Lower (vars 255) (graphGoal 255) 9 :=
  lower_forest (g:=g255) (i:=0) (hints:=34039381) (before_sound known439 valid439) geom255 checked255 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps255 : List (Nat × List Nat) := [(255,[]),(383,[135,50,16])]
def known255 := extendKnown known439 9 maps255
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid255 : Known known255 := extendKnown_ok valid439 low255 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom495 : graphValid g495 (boundsBefore known255) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=2) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice495k7p0 : block g495 7 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK495k7 : block g495 7 0 1=true := slice495k7p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice495k8p0 : block g495 8 0 15 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice495k8p15 : block g495 8 15 1 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK495k8 : block g495 8 0 16=true := (@block_merge g495 8 0 15 1 slice495k8p0 slice495k8p15)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice495k9p0 : block g495 9 0 11 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice495k9p11 : block g495 9 11 15 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice495k9p26 : block g495 9 26 2 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK495k9 : block g495 9 0 28=true := (@block_merge g495 9 0 26 2 (@block_merge g495 9 0 11 15 slice495k9p0 slice495k9p11) slice495k9p26)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice495k10p0 : block g495 10 0 4 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice495k10p4 : block g495 10 4 4 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK495k10 : block g495 10 0 8=true := (@block_merge g495 10 0 4 4 slice495k10p0 slice495k10p4)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice495k11p0 : block g495 11 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK495k11 : block g495 11 0 1=true := slice495k11p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked495 : checkedTables g495 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g495 0 0 0=true)
  · exact (rfl : block g495 1 0 0=true)
  · exact (rfl : block g495 2 0 0=true)
  · exact (rfl : block g495 3 0 0=true)
  · exact (rfl : block g495 4 0 0=true)
  · exact (rfl : block g495 5 0 0=true)
  · exact (rfl : block g495 6 0 0=true)
  · exact layerOK495k7
  · exact layerOK495k8
  · exact layerOK495k9
  · exact layerOK495k10
  · exact layerOK495k11
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low495 : Lower (vars 495) (graphGoal 495) 12 :=
  lower_forest (g:=g495) (i:=0) (hints:=4328547925) (before_sound known255 valid255) geom495 checked495 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps495 : List (Nat × List Nat) := [(495,[])]
def known495 := extendKnown known255 12 maps495
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid495 : Known known495 := extendKnown_ok valid255 low495 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom503 : graphValid g503 (boundsBefore known495) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=2) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice503k7p0 : block g503 7 0 3 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice503k7p3 : block g503 7 3 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK503k7 : block g503 7 0 4=true := (@block_merge g503 7 0 3 1 slice503k7p0 slice503k7p3)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice503k8p0 : block g503 8 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice503k8p1 : block g503 8 1 18 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice503k8p19 : block g503 8 19 3 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK503k8 : block g503 8 0 22=true := (@block_merge g503 8 0 19 3 (@block_merge g503 8 0 1 18 slice503k8p0 slice503k8p1) slice503k8p19)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice503k9p0 : block g503 9 0 8 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice503k9p8 : block g503 9 8 16 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice503k9p24 : block g503 9 24 4 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK503k9 : block g503 9 0 28=true := (@block_merge g503 9 0 24 4 (@block_merge g503 9 0 8 16 slice503k9p0 slice503k9p8) slice503k9p24)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice503k10p0 : block g503 10 0 3 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice503k10p3 : block g503 10 3 4 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK503k10 : block g503 10 0 7=true := (@block_merge g503 10 0 3 4 slice503k10p0 slice503k10p3)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice503k11p0 : block g503 11 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK503k11 : block g503 11 0 1=true := slice503k11p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked503 : checkedTables g503 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g503 0 0 0=true)
  · exact (rfl : block g503 1 0 0=true)
  · exact (rfl : block g503 2 0 0=true)
  · exact (rfl : block g503 3 0 0=true)
  · exact (rfl : block g503 4 0 0=true)
  · exact (rfl : block g503 5 0 0=true)
  · exact (rfl : block g503 6 0 0=true)
  · exact layerOK503k7
  · exact layerOK503k8
  · exact layerOK503k9
  · exact layerOK503k10
  · exact layerOK503k11
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low503 : Lower (vars 503) (graphGoal 503) 12 :=
  lower_forest (g:=g503) (i:=0) (hints:=4328982101) (before_sound known495 valid495) geom503 checked503 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps503 : List (Nat × List Nat) := [(503,[]),(507,[135,50,16]),(509,[101,49,32]),(510,[135,101,33,48])]
def known503 := extendKnown known495 12 maps503
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid503 : Known known503 := extendKnown_ok valid495 low503 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom447 : graphValid g447 (boundsBefore known503) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice447k10p0 : block g447 10 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK447k10 : block g447 10 0 1=true := slice447k10p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked447 : checkedTables g447 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g447 0 0 0=true)
  · exact (rfl : block g447 1 0 0=true)
  · exact (rfl : block g447 2 0 0=true)
  · exact (rfl : block g447 3 0 0=true)
  · exact (rfl : block g447 4 0 0=true)
  · exact (rfl : block g447 5 0 0=true)
  · exact (rfl : block g447 6 0 0=true)
  · exact (rfl : block g447 7 0 0=true)
  · exact (rfl : block g447 8 0 0=true)
  · exact (rfl : block g447 9 0 0=true)
  · exact layerOK447k10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low447 : Lower (vars 447) (graphGoal 447) 11 :=
  lower_forest (g:=g447) (i:=0) (hints:=4295460693) (before_sound known503 valid503) geom447 checked447 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps447 : List (Nat × List Nat) := [(447,[]),(479,[101,49,32])]
def known447 := extendKnown known503 11 maps447
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid447 : Known known447 := extendKnown_ok valid503 low447 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom511 : graphValid g511 (boundsBefore known447) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k8p0 : block g511 8 0 60 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k8p60 : block g511 8 60 7 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK511k8 : block g511 8 0 67=true := (@block_merge g511 8 0 60 7 slice511k8p0 slice511k8p60)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k9p0 : block g511 9 0 20 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k9p20 : block g511 9 20 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k9p84 : block g511 9 84 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k9p148 : block g511 9 148 11 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k9p159 : block g511 9 159 20 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK511k9 : block g511 9 0 179=true := (@block_merge g511 9 0 159 20 (@block_merge g511 9 0 148 11 (@block_merge g511 9 0 84 64 (@block_merge g511 9 0 20 64 slice511k9p0 slice511k9p20) slice511k9p84) slice511k9p148) slice511k9p159)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p0 : block g511 10 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p1 : block g511 10 1 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p65 : block g511 10 65 6 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p71 : block g511 10 71 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p135 : block g511 10 135 20 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p155 : block g511 10 155 10 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK511k10 : block g511 10 0 165=true := (@block_merge g511 10 0 155 10 (@block_merge g511 10 0 135 20 (@block_merge g511 10 0 71 64 (@block_merge g511 10 0 65 6 (@block_merge g511 10 0 1 64 slice511k10p0 slice511k10p1) slice511k10p65) slice511k10p71) slice511k10p135) slice511k10p155)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k11p0 : block g511 11 0 12 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k11p12 : block g511 11 12 33 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k11p45 : block g511 11 45 7 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK511k11 : block g511 11 0 52=true := (@block_merge g511 11 0 45 7 (@block_merge g511 11 0 12 33 slice511k11p0 slice511k11p12) slice511k11p45)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k12p0 : block g511 12 0 4 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k12p4 : block g511 12 4 4 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK511k12 : block g511 12 0 8=true := (@block_merge g511 12 0 4 4 slice511k12p0 slice511k12p4)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k13p0 : block g511 13 0 1 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK511k13 : block g511 13 0 1=true := slice511k13p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked511 : checkedTables g511 13 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g511 0 0 0=true)
  · exact (rfl : block g511 1 0 0=true)
  · exact (rfl : block g511 2 0 0=true)
  · exact (rfl : block g511 3 0 0=true)
  · exact (rfl : block g511 4 0 0=true)
  · exact (rfl : block g511 5 0 0=true)
  · exact (rfl : block g511 6 0 0=true)
  · exact (rfl : block g511 7 0 0=true)
  · exact layerOK511k8
  · exact layerOK511k9
  · exact layerOK511k10
  · exact layerOK511k11
  · exact layerOK511k12
  · exact layerOK511k13
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low511 : Lower (vars 511) (graphGoal 511) 14 :=
  lower_forest (g:=g511) (i:=0) (hints:=4329006677) (before_sound known447 valid447) geom511 checked511 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps511 : List (Nat × List Nat) := [(511,[])]
def known511 := extendKnown known447 14 maps511
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid511 : Known known511 := extendKnown_ok valid447 low511 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exactLower : ∀ t, PEqualNP.MetaComplexity.HasCircuitSize 9 edge10669 t → 14 ≤ t :=
  conclude10669 (root_index (g:=g511) (before_sound known447 valid447) geom511 checked511 (k:=13) (by decide) (i:=0) (by decide +kernel))

end PEqualNP.Outside.L_meta_10668

theorem PEqualNP.Outside.L_meta_10668 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 4 && x 8) || (x 7 && x 8)) t → 14 ≤ t := PEqualNP.Outside.L_meta_10668.exactLower
