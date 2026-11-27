import PEqualNP.Defs

-- The Live/Run/Forest checker derives from PressF10, pequalnp-proofs PR 4332,
-- and its extension in L_meta_3853, licensed under Apache-2.0.
namespace PEqualNP.Outside.L_meta_8531
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
  (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 2) ||| (x 3 &&& x 5) ||| (x 4 &&& x 6) ||| (x 5 &&& x 6) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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


abbrev Bits := BitVec 256
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 256 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 256 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 256 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 256 → Row) (x : Decor) := x.2 = pairSig r s x.1
def dneg (x : Decor) : Decor := (neg x.1,~~~x.2.1,~~~x.2.2)
def dbin (d : Bool) (x y : Decor) : Decor :=
  if d then (bin d x.1 y.1,x.2.1 ||| y.2.1,x.2.2 ||| y.2.2)
  else (bin d x.1 y.1,x.2.1 &&& y.2.1,x.2.2 &&& y.2.2)

theorem ofRows_neg (r : Fin 256 → Row) (a : Sig) : ofRows r (neg a) = ~~~ofRows r a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (neg a) ⟨j,hj⟩
  rw [bit_neg,←ofRows_bit r a ⟨j,hj⟩] at h
  simpa only [BitVec.getLsbD_not,hj,decide_true,Bool.true_and] using h
theorem ofRows_bin (r : Fin 256 → Row) (d : Bool) (a b : Sig) :
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

def asRow (cols : Nat → Bits) (i : Fin 256) : Row :=
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 256) (j : Fin 9) :
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
  (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 2) ||| (x 3 &&& x 5) ||| (x 4 &&& x 6) ||| (x 5 &&& x 6) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 256) (j : Fin 9) :
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
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 256) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then (if m.testBit 9 && j == 4 then ~~~(v 4) else v j) else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide)]
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
    if (rs ||| column d z.2) != BitVec.allOnes 256 then true else
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
  change covered (decide (child.length = cap)) (pairSig r s) child = BitVec.allOnes 256 at sep
  rw [deq] at sep
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2) != BitVec.allOnes 256) = false := by simp [sep]
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
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 256) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val :=
  bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 256) (hq : chartSamples m q = 0) :
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
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 256) &&
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
def lanePlace (v : Nat) (upper : Nat) := 2^257*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^257 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<257 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<257 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<257 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
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

def fullMarks (r packed : Nat) := ((packed+r) >>> 256) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (257*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^257)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 257*(i+1)-257=257*i := by omega
      have ge : ¬257*(i+1)<257 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 256 = (a==BitVec.allOnes 256) := by
  by_cases h : a=BitVec.allOnes 256
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^256-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^256 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (257*i) =
      (f xs[i]==BitVec.allOnes 256) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^257*u+x+(2^257*v+1)=2^257*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^257 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬257*(i+1)+256<257 := by omega
      have di : 257*(i+1)+256-257=257*i+256 := by omega
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
theorem top_xor (a : Bits) : BitVec.allOnes 256 ^^^ a = ~~~a := BitVec.allOnes_xor
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp (units xs.length*(BitVec.allOnes 256).toNat) op
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
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 257) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (257*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
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
      apply ih (mask:=mask >>> 257) (i:=i) (by simpa using hi) _ ok.2
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
    let z := packedOp (r*(BitVec.allOnes 256).toNat) op a b'
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
      if len>k then true else if combField xs[q] d (op==2) ka kb op i j != BitVec.allOnes 256 then true
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
        packedColumn d (packedOp (r*(BitVec.allOnes 256).toNat) op a b))) xs) = true at pass
    rw [if_neg small] at pass
    have chosen : cov = packedCov (fun c => getCov c.2.2.2.1 d) xs := by
      dsimp only [cov]
      cases d <;> rfl
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,chosen,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] d (op==2) ka kb op i j = BitVec.allOnes 256
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

def edge8531 : (Fin 8 → Bool) → Bool := fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6) || (x 5 && x 7) || (x 6 && x 7)
def sample8531 (r : Row) (i : Fin 8) := bit r (inputs.getD i.val zero)
theorem raw8531 : List.ofFn (fun i : Fin 8 => inputs.getD i.val zero) = vars 255 := by decide +kernel
theorem samples8531 (r : Row) : List.ofFn (sample8531 r) = (vars 255).map (bit r) := by
  rw [←raw8531,List.map_ofFn]
  rfl
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem edge8531_table : ∀ r : Row, bit r (graphGoal 255) = edge8531 (sample8531 r) := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem conclude8531 (absent : Impossible (graphGoal 255) 12 (vars 255).toFinset) :
    ∀ t, PEqualNP.MetaComplexity.HasCircuitSize 8 edge8531 t → 13 ≤ t := by
  intro t hs
  obtain ⟨C,hf,hsize,correct⟩ := hs
  by_contra! bad
  have hp : proper (graphGoal 255) := by unfold proper; decide +kernel
  have he : (execute C.gates (vars 255)).getD C.output zero = graphGoal 255 := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    change bit r ((execute C.gates (vars 255)).getD C.output zero) = bit r (graphGoal 255)
    rw [←b_read,execute_bits _ _ _ (fun g hg => (hf g hg).1),←samples8531,edge8531_table]
    exact correct (sample8531 r)
  have hout := get_rep (execute C.gates (vars 255)) C.output
  rw [he] at hout
  obtain ⟨k,u,S,hk,run,sub⟩ := extract C.gates _ hf hp (hout.resolve_right (fun h => h hp))
  have all : ∀ a ∈ vars 255, Essential (graphGoal 255) (vars 255) a := by
    have valid : checkEssential (graphGoal 255) (vars 255) (graphPairs 255 1412431873) = true := by decide +kernel
    have ident : (graphPairs 255 1412431873).map Prod.fst = vars 255 := by decide +kernel
    intro a ha
    apply essential_ok valid a
    rw [ident]
    exact List.mem_toFinset.mpr ha
  have eq : S=(vars 255).toFinset := by
    ext a
    constructor
    · exact fun ha => List.mem_toFinset.mpr (sub a ha)
    · intro ha
      obtain ⟨r,s,diff,sep⟩ := all a (List.mem_toFinset.mp ha)
      exact raw_required run _ a sub r s diff sep
  rw [eq] at run
  change C.gates.length ≤ t at hsize
  exact absent k u (by omega) run
def packed7r3 (i : Nat) : Nat := 0x7
def layer7r3 : Packing := (1,0,0,63,0,0,1,packed7r3)
def samples7 : Array (Bits × Bits) := #[(0x3f,0x49),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc7,0x92),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff24),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def cols7 : IndexTree ColumnInfo := (.leaf [])
def levels7 : Nat → Packing
  | 3 => layer7r3
  | _ => emptyPacking
def index7 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g7 : Forest := ⟨7,3,fun j => samples7[j]?.getD (0,0),cols7,#[[]],levels7,index7,noFactory,noFactorySound 7⟩
def packed43r3 (i : Nat) : Nat := 0xf
def layer43r3 : Packing := (1,0,0,63,0,0,1,packed43r3)
def samples43 : Array (Bits × Bits) := #[(0x41fff,0x50929),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffff81c1f,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa5696),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe7e0,0x864c4),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffff79b18),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def cols43 : IndexTree ColumnInfo := (.leaf [])
def levels43 : Nat → Packing
  | 3 => layer43r3
  | _ => emptyPacking
def index43 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g43 : Forest := ⟨43,3,fun j => samples43[j]?.getD (0,0),cols43,#[[]],levels43,index43,noFactory,noFactorySound 43⟩
def packed15r4 (i : Nat) : Nat := 0x1f
def layer15r4 : Packing := (1,0,0,63,0,0,1,packed15r4)
def samples15 : Array (Bits × Bits) := #[(0x7e0ff,0x2111),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa1f0f,0xa8a46),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc1ff0,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffff514a8),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd8cc),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def cols15 : IndexTree ColumnInfo := (.leaf [(8,0,7,0,4)])
def levels15 : Nat → Packing
  | 4 => layer15r4
  | _ => emptyPacking
def index15 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g15 : Forest := ⟨15,4,fun j => samples15[j]?.getD (0,0),cols15,#[[]],levels15,index15,noFactory,noFactorySound 15⟩
def packed103r5 (i : Nat) : Nat := 0x3f
def layer103r5 : Packing := (1,0,0,63,0,0,1,packed103r5)
def samples103 : Array (Bits × Bits) := #[(0x3003cf00ffff,0x322145242525),(0xc00cf3ff00ff,0xc4449249484a),(0xffffffffffffffffffffffffffffffffffffffffffffffffffff000f3cffff00,0xffffffffffffffffffffffffffffffffffffffffffffffffffff088a28929290),(0x0,0x0),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffff03f000000,0x150f03f1c1c1c),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffeaf0fc0e0e0e0),(0x0,0x0),(0x0,0x0)]
def cols103 : IndexTree ColumnInfo := (.leaf [(0,32,7,64,5)])
def levels103 : Nat → Packing
  | 5 => layer103r5
  | _ => emptyPacking
def index103 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g103 : Forest := ⟨103,5,fun j => samples103[j]?.getD (0,0),cols103,#[[]],levels103,index103,noFactory,noFactorySound 103⟩
def packed107r4 (i : Nat) : Nat := 0x1f
def layer107r4 : Packing := (1,0,0,63,0,0,1,packed107r4)
def samples107 : Array (Bits × Bits) := #[(0x181f207fff,0x1a452a2555),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffff6013c0703f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffff6492d45a2a),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffff801cff9fc0,0xffffffffffffffffffffffffffffffffffffffffffffffffffffff84185098a0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0ffe000,0x28e0a7630c),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffd71f180c30),(0x0,0x0),(0x0,0x0)]
def cols107 : IndexTree ColumnInfo := (.leaf [])
def levels107 : Nat → Packing
  | 4 => layer107r4
  | _ => emptyPacking
def index107 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g107 : Forest := ⟨107,4,fun j => samples107[j]?.getD (0,0),cols107,#[[]],levels107,index107,noFactory,noFactorySound 107⟩
def packed121r5 (i : Nat) : Nat := 0x202608000902208000020080200803f3b6cc5729487ce19283c50500fd43fd42fd32fd41fd31fd21fd40fd30fd20fd10be44de33ee22f611fa00
def layer121r5 : Packing := (15,1,3,63,0,7,1,packed121r5)
def keys121k6 (i : Nat) : Nat := 0x30806eebea866980000000730070006a3105ad472c0cd019
def packed121r6 (i : Nat) : Nat := 0x23444bf
def layer121r6 : Packing := (1,0,3,63,0,0,1,packed121r6)
def samples121 : Array (Bits × Bits) := #[(0xc01019c07fff,0xd21488d414a9),(0x0,0x0),(0x0,0x0),(0x100601e7fc07f,0x120e85221e246),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffe007fe7807f80,0xfffffffffffffffffffffffffffffffffffffffffffffffffffe04a167094b14),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffff8007ff8000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffe470185ce0c18),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000000,0x1b85e18303060),(0x0,0x0),(0x0,0x0)]
def cols121 : IndexTree ColumnInfo := (.fork 2 (.leaf [(1,0,120,0,4),(8,0,113,0,4)]) (.leaf [(16,0,105,0,4),(32,0,89,0,4),(64,0,57,0,4)]))
def levels121 : Nat → Packing
  | 5 => layer121r5
  | 6 => layer121r6
  | _ => emptyPacking
def index121 : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 5 22 3 8 4 0 keys121k6
  | _ => fun _ => none
def g121 : Forest := ⟨121,6,fun j => samples121[j]?.getD (0,0),cols121,#[[]],levels121,index121,noFactory,noFactorySound 121⟩
def packed47r5 (i : Nat) : Nat := 0x204813044100401007cca8794280fd21fd20fd10fe00ee22f611fa00
def layer47r5 : Packing := (7,1,3,63,0,6,1,packed47r5)
def keys47k6 (i : Nat) : Nat := 0x2800000e40000020000005259a83
def packed47r6 (i : Nat) : Nat := 0x6a47f
def layer47r6 : Packing := (1,0,3,63,0,0,1,packed47r6)
def samples47 : Array (Bits × Bits) := #[(0x200f3fe03fff,0x240502240891),(0xc033d01fc07f,0xc89254895226),(0xffffffffffffffffffffffffffffffffffffffffffffffffffff003ce01fff80,0xffffffffffffffffffffffffffffffffffffffffffffffffffff1128a912a548),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffc0ffe00000,0x141c0f1c3060c),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffebe3f0e1c3870),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def cols47 : IndexTree ColumnInfo := (.fork 2 (.leaf [(0,32,7,8,5),(32,0,15,0,5)]) (.leaf [(2,0,45,0,4),(4,0,43,0,4),(8,32,7,0,4)]))
def levels47 : Nat → Packing
  | 5 => layer47r5
  | 6 => layer47r6
  | _ => emptyPacking
def index47 : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 16 0 7 3 0 keys47k6
  | _ => fun _ => none
def g47 : Forest := ⟨47,6,fun j => samples47[j]?.getD (0,0),cols47,#[[]],levels47,index47,noFactory,noFactorySound 47⟩
def packed248r5 (i : Nat) : Nat := 0x3f
def layer248r5 : Packing := (1,0,0,63,0,0,1,packed248r5)
def samples248 : Array (Bits × Bits) := #[(0x0,0x0),(0x0,0x0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffd82408307f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffdd268e3c39),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffe038103fe0,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffe47a5499f4),(0x3fffc07f,0x4870c146),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffc01fff80,0x9808b2608),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe00000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffff637040810),(0x0,0x0)]
def cols248 : IndexTree ColumnInfo := (.leaf [(8,0,240,0,5)])
def levels248 : Nat → Packing
  | 5 => layer248r5
  | _ => emptyPacking
def index248 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g248 : Forest := ⟨248,5,fun j => samples248[j]?.getD (0,0),cols248,#[[]],levels248,index248,noFactory,noFactorySound 248⟩
def packed31r5 (i : Nat) : Nat := 0x3f
def layer31r5 : Packing := (1,0,0,63,0,0,1,packed31r5)
def samples31 : Array (Bits × Bits) := #[(0xe7e7e0ff,0x202111),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff5a1a1f0f,0x14a8a8a46),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff9c1c1ff0,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffe951514a8),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffe01fe000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffe19fd8cc),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe00000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc198cc),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def cols31 : IndexTree ColumnInfo := (.leaf [(8,0,23,0,5)])
def levels31 : Nat → Packing
  | 5 => layer31r5
  | _ => emptyPacking
def index31 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g31 : Forest := ⟨31,5,fun j => samples31[j]?.getD (0,0),cols31,#[[]],levels31,index31,noFactory,noFactorySound 31⟩
def packed126r5 (i : Nat) : Nat := 0x7f
def layer126r5 : Packing := (1,0,0,63,0,0,1,packed126r5)
def samples126 : Array (Bits × Bits) := #[(0x0,0x0),(0x48c00c300f33300ffff,0x48d24c34a5313525555),(0xfffffffffffffffffffffffffffffffffffffffffffff930030c00fc3c00ffff,0xfffffffffffffffffffffffffffffffffffffffffffff9324b0c94ac2ca4aaaa),(0x1c003f000cfcfff3300,0x1c30ff0c6c545c733cc),(0xfffffffffffffffffffffffffffffffffffffffffffffe0003ffff0ff0003c00,0xfffffffffffffffffffffffffffffffffffffffffffffe006d551f0ff0363c3c),(0xfffffffffffffffffffffffffffffffffffffffffffffffffc00000fffffc000,0xfffffffffffffffffffffffffffffffffffffffffffffe147000180aba38c030),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000,0x1eb82aae0f000c000c0),(0x0,0x0),(0x0,0x0)]
def cols126 : IndexTree ColumnInfo := (.leaf [(0,2,120,4,5)])
def levels126 : Nat → Packing
  | 5 => layer126r5
  | _ => emptyPacking
def index126 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g126 : Forest := ⟨126,5,fun j => samples126[j]?.getD (0,0),cols126,#[[]],levels126,index126,noFactory,noFactorySound 126⟩
def packed183r6 (i : Nat) : Nat := 0x7f
def layer183r6 : Packing := (1,0,0,63,0,0,1,packed183r6)
def samples183 : Array (Bits × Bits) := #[(0x3003cf3cf3ff00ffff,0x322045045025242525),(0x30c00d33d33d00ff00ff,0x30c4451251254849484a),(0xffffffffffffffffffffffffffffffffffffffffffffc3000e3ce3ce00ffff00,0xffffffffffffffffffffffffffffffffffffffffffffc3088a28a28a90929290),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffc000fc0fc0fff000000,0xfffffffffffffffffffffffffffffffffffffffffffffc0ccf80f80fdad8d8d8),(0xfffffffffffffffffffffffffffffffffffffffffffffffff000fff000000000,0x5550f000fff01c1c1c1c),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000,0xffffffffffffffffffffffffffffffffffffffffffffaaaf0fff0000e0e0e0e0),(0x0,0x0)]
def cols183 : IndexTree ColumnInfo := (.leaf [(0,32,23,128,6)])
def levels183 : Nat → Packing
  | 6 => layer183r6
  | _ => emptyPacking
def index183 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g183 : Forest := ⟨183,6,fun j => samples183[j]?.getD (0,0),cols183,#[[]],levels183,index183,noFactory,noFactorySound 183⟩
def packed231r6 (i : Nat) : Nat := 0x30aa479848c180db95622eb91222f38ce22dd95611ed91211f58ce11de95600ee91200f68ce00
def layer231r6 : Packing := (9,2,4,63,0,6,1,packed231r6)
def keys231k7 (i : Nat) : Nat := 0x300001ca008400016f2c0108c7c38007
def packed231r7 (i : Nat) : Nat := 0x7ba27b62736262e262a25aa2a1018202002fcabbe44ef19fb88bec23fa00
def layer231r7 : Packing := (6,1,4,63,0,7,1,packed231r7)
def keys231k8 (i : Nat) : Nat := 0x4c200013400060a8019
def packed231r8 (i : Nat) : Nat := 0x9175438260abf
def layer231r8 : Packing := (1,0,4,63,0,0,1,packed231r8)
def samples231 : Array (Bits × Bits) := #[(0x300018003c300079e003fffff,0x3222191214324428a49092925),(0xc0006000ccc0019e7ffc007ff,0xc444622448c4889249252424a),(0xfffffffffffffffffffffffffffffffffffffff00018000f30001e79fffff800,0xfffffffffffffffffffffffffffffffffffffff08898448a3091145124a49490),(0x0,0x0),(0x0,0x0),(0x1ffff03fffe07e00000000,0xea80f01501e07e0700e01c),(0xffffffffffffffffffffffffffffffffffffffffffe000003fffff8000000000,0x150f0007002a1e1f80380700e0),(0xffffffffffffffffffffffffffffffffffffffffffffffffc000000000000000,0xffffffffffffffffffffffffffffffffffffffeaf015780fc0e00001c0380700),(0x0,0x0)]
def cols231 : IndexTree ColumnInfo := (.fork 8 (.fork 4 (.leaf [(0,1,224,6,6),(0,2,224,5,6),(0,4,224,3,6),(0,64,7,160,6)]) (.leaf [(0,128,7,96,6),(1,0,230,0,6),(2,0,229,0,6),(4,0,227,0,6)])) (.fork 4 (.leaf [(32,0,199,0,6),(64,0,167,0,6),(1,2,224,4,5),(1,4,224,2,5)]) (.leaf [(2,4,224,1,5),(32,64,7,128,5),(32,128,7,64,5),(64,128,7,32,5)])))
def levels231 : Nat → Packing
  | 6 => layer231r6
  | 7 => layer231r7
  | 8 => layer231r8
  | _ => emptyPacking
def index231 : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 3 15 3 8 4 0 keys231k7
  | 8 => lookupWord 2 11 0 7 3 0 keys231k8
  | _ => fun _ => none
def g231 : Forest := ⟨231,8,fun j => samples231[j]?.getD (0,0),cols231,#[[]],levels231,index231,noFactory,noFactorySound 231⟩
def packed111r7 (i : Nat) : Nat := 0x7f
def layer111r7 : Packing := (1,0,0,63,0,0,1,packed111r7)
def samples111 : Array (Bits × Bits) := #[(0x1801e78400f3ff00ffff,0x19102284905025242525),(0x460069998033d00ff00ff,0x46222891921254849484a),(0xfffffffffffffffffffffffffffffffffffffffffff980071e6003ce00ffff00,0xfffffffffffffffffffffffffffffffffffffffffff984451462428a90929290),(0xfffffffffffffffffffffffffffffffffffffffffffe0007e07ffc0fff000000,0xfffffffffffffffffffffffffffffffffffffffffffe0607c02b040fc2c0c0c0),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffff8007ffff000000000,0xa87800547bf01c1c1c1c),(0xffffffffffffffffffffffffffffffffffffffffffffffffff80000000000000,0xffffffffffffffffffffffffffffffffffffffffffff5787ff838000e0e0e0e0),(0x0,0x0),(0x0,0x0)]
def cols111 : IndexTree ColumnInfo := (.leaf [(64,0,47,0,7)])
def levels111 : Nat → Packing
  | 7 => layer111r7
  | _ => emptyPacking
def index111 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g111 : Forest := ⟨111,7,fun j => samples111[j]?.getD (0,0),cols111,#[[]],levels111,index111,noFactory,noFactorySound 111⟩
def packed63r7 (i : Nat) : Nat := 0x7f
def layer63r7 : Packing := (1,0,0,63,0,0,1,packed63r7)
def samples63 : Array (Bits × Bits) := #[(0x3c200f39ff3fe03fff,0x42405001102240891),(0xcd0c033d680d01fc07f,0xc50c89252a454895226),(0xfffffffffffffffffffffffffffffffffffffffffffff0e3003ce700e01fff80,0xfffffffffffffffffffffffffffffffffffffffffffff0a31128a548a912a548),(0xffffffffffffffffffffffffffffffffffffffffffffff03ffc0f800ffe00000,0x150141c0f80cf1c3060c),(0xfffffffffffffffffffffffffffffffffffffffffffffffc0000ffff00000000,0xfffffffffffffffffffffffffffffffffffffffffffffff81980ffee0d9b366c),(0xffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000,0xffffffffffffffffffffffffffffffffffffffffffffeafebe3f00700e1c3870),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def cols63 : IndexTree ColumnInfo := (.leaf [(16,0,47,0,7)])
def levels63 : Nat → Packing
  | 7 => layer63r7
  | _ => emptyPacking
def index63 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g63 : Forest := ⟨63,7,fun j => samples63[j]?.getD (0,0),cols63,#[[]],levels63,index63,noFactory,noFactorySound 63⟩
def packed123r7 (i : Nat) : Nat := 0x7f
def layer123r7 : Packing := (1,0,0,63,0,0,1,packed123r7)
def samples123 : Array (Bits × Bits) := #[(0xc00101f0e407ffffff,0xd201485025421494a9),(0xffffffffffffffffffffffffffffffffffffffffffffeb0066013c980740407f,0xffffffffffffffffffffffffffffffffffffffffffffeb24e6952c9a956a6a56),(0x0,0x0),(0xc007801cf1ff9807f80,0xc20f885850a19a26344),(0xfffffffffffffffffffffffffffffffffffffffffffff0007ffe0fe001ff8000,0xfffffffffffffffffffffffffffffffffffffffffffff004aa160fc091cb0a14),(0xffffffffffffffffffffffffffffffffffffffffffffffff80000ffffe000000,0xfffffffffffffffffffffffffffffffffffffffffffff14700180af4e60c0c18),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000,0xeb855e1f00300303060),(0x0,0x0),(0x0,0x0)]
def cols123 : IndexTree ColumnInfo := (.leaf [(2,0,121,0,7)])
def levels123 : Nat → Packing
  | 7 => layer123r7
  | _ => emptyPacking
def index123 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g123 : Forest := ⟨123,7,fun j => samples123[j]?.getD (0,0),cols123,#[[]],levels123,index123,noFactory,noFactorySound 123⟩
def packed249r5 (i : Nat) : Nat := 0x47d7599943
def layer249r5 : Packing := (1,3,3,63,0,0,1,packed249r5)
def keys249k6 (i : Nat) : Nat := 0xd0
def packed249r6 (i : Nat) : Nat := 0x80000000002479848c180bf999439f59443bb58843bd58443e791233ee91200f68ce00
def layer249r6 : Packing := (7,2,3,63,0,6,1,packed249r6)
def keys249k7 (i : Nat) : Nat := 0x460305168f7b3a
def packed249r7 (i : Nat) : Nat := 0xa8420c321cc54b5306b2b210828d5311d4c475311c4372a1b1209007f913fa87fc43ff19ef913bc67fa00
def layer249r7 : Packing := (7,1,3,63,0,8,1,packed249r7)
def keys249k8 (i : Nat) : Nat := 0xcdd6e007400000800000000e4180
def packed249r8 (i : Nat) : Nat := 0x468897f
def layer249r8 : Packing := (1,0,3,63,0,0,1,packed249r8)
def samples249 : Array (Bits × Bits) := #[(0xc00300f980100ce01ffff,0xd2434a29a915246a85555),(0x0,0x0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffb0024009a00600f3ff00ff,0xffffffffffffffffffffffffffffffffffffffffffb24249092506a09143a0a2),(0xffffffffffffffffffffffffffffffffffffffffffc003800e4007ff3c01ff00,0xffffffffffffffffffffffffffffffffffffffffffc20b884c44228539118a88),(0x3fff07ff8003ffe0000,0xc90704838062e1c0c0c),(0xfffffffffffffffffffffffffffffffffffffffffffffc00007fffffc0000000,0x1470018031c538c0603030),(0xffffffffffffffffffffffffffffffffffffffffffffffffff80000000000000,0xffffffffffffffffffffffffffffffffffffffffffeb836e0f8600c00180c0c0),(0x0,0x0)]
def cols249 : IndexTree ColumnInfo := (.fork 3 (.leaf [(8,0,241,0,7),(16,0,233,0,7),(128,0,121,0,7)]) (.leaf [(0,1,224,24,6),(1,0,248,0,6),(32,0,217,0,5),(64,0,185,0,5)]))
def levels249 : Nat → Packing
  | 5 => layer249r5
  | 6 => layer249r6
  | 7 => layer249r7
  | 8 => layer249r8
  | _ => emptyPacking
def index249 : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 keys249k6
  | 7 => lookupWord 2 11 0 7 3 0 keys249k7
  | 8 => lookupWord 2 16 0 7 3 0 keys249k8
  | _ => fun _ => none
def g249 : Forest := ⟨249,8,fun j => samples249[j]?.getD (0,0),cols249,#[[]],levels249,index249,noFactory,noFactorySound 249⟩
def packed254r7 (i : Nat) : Nat := 0xff
def layer254r7 : Packing := (1,0,0,63,0,0,1,packed254r7)
def samples254 : Array (Bits × Bits) := #[(0x0,0x0),(0x48c300462300ff48c00c300f33300ffff,0x48c34946234a5548d48c3525313545555),(0xfffffffffffffffffffffffffffffff930c00984c00ff930030c00fc3c00ffff,0xfffffffffffffffffffffffffffffff930c92984c94aa932930ca4ac2ca8aaaa),(0xfffffffffffffffffffffffffffffffe3f000e07000cc1c003f000cfcfff3300,0xfffffffffffffffffffffffffffffffe3f0d8e070d8cc1c3c3f0f0c545f133f0),(0xffffffffffffffffffffffffffffffffc0000ff8000f0e0003ffff0ff0003c00,0xffffffffffffffffffffffffffffffffc00c3ff80c6f0e031955c70ff0cc3ccc),(0xffffff00ffffc00000fffffc000,0x30a850700e141c00060aba0ec00c),(0xfffffffffffffffffffffffffffffffffffff00000000ffffffffff000000000,0x1551c000018001e8e2aa38f000300030),(0xfffffffffffffffffffffffffffffffffffffffffffff0000000000000000000,0xffffffffffffffffffffffffffffffffeaae0f57ae0ff0030000c00000c000c0),(0x0,0x0)]
def cols254 : IndexTree ColumnInfo := (.leaf [(0,2,248,4,7)])
def levels254 : Nat → Packing
  | 7 => layer254r7
  | _ => emptyPacking
def index254 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g254 : Forest := ⟨254,7,fun j => samples254[j]?.getD (0,0),cols254,#[[]],levels254,index254,noFactory,noFactorySound 254⟩
def packed191r8 (i : Nat) : Nat := 0xff
def layer191r8 : Packing := (1,0,0,63,0,0,1,packed191r8)
def samples191 : Array (Bits × Bits) := #[(0x1801cf3cf00f0801e73ff3ff00ffff,0x1910010450010920a0025025242525),(0x8c46006b4d3333430067ad00d00ff00ff,0x8c462229451231432424a54854849484a),(0xfffffffffffffffffffffffffffffff309800738e3cc38c0079ce00e00ffff00,0xfffffffffffffffffffffffffffffff309844528a28c28c48514a90a90929290),(0xfffffffffffffffffffffffffffffffc0e0007c0fc0fc0fff81f000fff000000,0xfffffffffffffffffffffffffffffffc0e0607c0f8054056081f0c0fc2c0c0c0),(0xfffffffffffffffffffffffffffffffff00007ff000fff00001ffff000000000,0xfffffffffffffffffffffffffffffffff00667fe000ffe06c01ffda0d8d8d8d8),(0xfffffffffffffffffffffffffffffffffffff800000fffffffe0000000000000,0x150a87800000abfa8f7e001c01c1c1c1c),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffff000000000000000000000,0xfffffffffffffffffffffffffffffffeaf5787fffff0000700000e00e0e0e0e0),(0x0,0x0)]
def cols191 : IndexTree ColumnInfo := (.leaf [(16,0,175,0,8)])
def levels191 : Nat → Packing
  | 8 => layer191r8
  | _ => emptyPacking
def index191 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g191 : Forest := ⟨191,8,fun j => samples191[j]?.getD (0,0),cols191,#[[]],levels191,index191,noFactory,noFactorySound 191⟩
def packed127r6 (i : Nat) : Nat := 0x7282e506c80b9017282e506c80b9010000008172635445362718120c0600cceaa306382859b5546047050b33b08b18e09967558d811c132cceaa306382839ad546087050733b08b18e098e7358d821c1319f0c8900a12413e191201324827c32440282884f8648804c510
def layer127r6 : Packing := (12,4,5,63,0,8,1,packed127r6)
def keys127k7 (i : Nat) : Nat := 0xc10056829733d0248bbaa90000d8c564a0
def packed127r7 (i : Nat) : Nat := 0x8765038c00219900a38765038c00219900a30000000006503c00d900b0030006503c10d900b043a50408169020dc3e08c370f0630dc2e08c370b0630000000dc3c08c370f0230dc2c08c370b023000000020800820000000000000000000b4accb1aa8a2a849fa6096a5493a4890a3c87a007e9f4759b86898c5b9504c91443908408fc378c0288841f8781c86c1986016854138481083c0d8300a824078180480c01800dbd541c1429fd831c1429fd841c132ddd631c132dbd541c1419fd831c1419fd841c131ddd631c1319fd839dd409fd849dd309fe885d130f9d43501309fd849dd209fd839dd20fad5450920fcd634c9209fd849dd109fd839dd10fb55450510fd5634c510dbd7455200ddd7358e009dd831c1429f5811c1429bd841c1329f5811c132e6e6695622f2e5591222ece668ce22f8e448ce229dd831c1419ed821c1419bd841c1319ed821c131e766695611f365591211ed6668ce11f96448ce119f5819dd20be88050920be8804c9209ed829dd10bf08050510bf0804c510e7a6695600f3a5591200eda668ce00f9a448ce00eea6688a00f6a5588a00faa4488a00fca3388a00ef26684600f725584600fb24484600fd23384600
def layer127r7 : Packing := (56,3,5,63,0,10,1,packed127r7)
def keys127k8 (i : Nat) : Nat := 0x2d1a74008a1e0000001c1eee4dc65d80040cf2c2c1618d94000004d000000007a85b2240048987fa624c49ad9728a09ba519db1e310f003735d68d206c047fda8573766157ab161078d9b4142abf2bc3945e100800eb074410c7986000045740041
def packed127r8 (i : Nat) : Nat := (if i < 1 then 0x348192408214082105080a40c1604108284072060b020848c4158d1082b1870d205c9060050600414202902c5830020a101c8162c180123105234420a4695223448500c9128495204901460a5801220524009102841800c0050828414008004002801400a00500214223040400d9d00214203440400d9d0021420304a060c8010a10182502c6400a38012280140060030100484004aa4c5294c4aa4c4aa4c4aa444a6444aa444a6444aa444a6444aa444a6444aa1530aa854c2a21510f7df7af7476a763f59f4ff4cf4673c735f2bf25717f06ef5ee86daecd6bfeb26a4e93e82e75667e5a64ce3f635627e1a610602df55eb5e15ccdb85aada459358cd7856ad6455354cd3bd27520d16d0cd064f1cdd4cfcc94b84b1c9d48fc89478471c60c4c445c3bc31c2b42141740d4033dd3d6bc23bbbaaba439338cb66b6034133ab2631530eafdaf72e62dc2d22bdab3a9f295287a7a26925f255240a36a2221820a9fd1e51db1d11ca9c41ba1b39a99a319c99618f98918297c17596f16896215b9551399331179110f90f28da8d40ca0c00b98b30a909f09508b08107706d06305904f04503b03102702081a01380d0068007fe77503feb9a81ff5c940ffa64a07fd71503fe98a81ff9dd30ffae8987fd724c3fea1261ff5c530ffa82987fd404c3feb2a41ff55120ffac6907fd43483feb0241ff54120ffa80907fd30483feb2a21ff55110ffac6887fd43443feb0221ff54110ffa80887fd30443feb2c01ff55200ffac7007fd43803feb0401ff54200ffa81007fd30802fe382c57f1c152bfceea177e5550bdeaa285f78cd42bf8e0a15fe774cb7f332657f5d132f7c88997dd634cafe38265fb59622fdaa9117ed6388bf6a1c457f1c161bf8e0a8dfe77507bf2aa83ef55141fbc66a0dfc70506ff3ba63bf99931bfae898fbe444c7eeb1a637f1c131feacb08ff554847fab1c23fd50e11fdc44b07f611583f7112a1fd84550bfceea077e55503dea1a81f78cd40f7a84a07ee22503dea0a81fd84540bfcee986fe664c2feba261ef91130fba86987dd324c3f711261f74c530fec22985fe774837f33241df95520bfae8907be44482feb9a41f78cd20fda84907ed32482ff3ba21bf99910efcaa885fd74443df222217f5cd10fbc66887f541443fa98a21fe9de00ff2ed007f975803fcb2c01fe5d200ff2a9007f973803fcb1c01fe50e00ff2e5007f962803fca9401fe50a00ff265007f971803fcb0c01fe54600ff283007f9318037f33401df95600bfae9007be44802feb9c01f78ce00bfae5007ee22802feb8c01fd84600ff2c1007f950803fca0401fe4c200ff241007f9108033f334abcf95644dbccd19f9e448cf7733445db95622f5c89117ce3388b7b33423dd95611f6c8908fd6338477d33401de95600f7489007da33803f511401fc84600 else 0x683080400972a12104b1408682080400992a12104c140a1424c3400c325806a40e9201b90840181a3810434502086560410cac0821930d0430c9609a903a4826e421045868e0c00d141801948300329060064c3041929a8c3a43718d201070a8c30c1110634184341043a5061b2051f2438d902c132543820a94c2a4490410e1a1c81b2c12e543820e05524a89041549c4c89038685206ca9014b002490024408e94186c8147c90e3640b00c140e002a530a912400438687206cb00b140e003215492824005527132240e1a1481b2a4052c009240091030d0050d0050900509004305870c1420202021d48012a5230a452a00631514a04400c62829408801182c3860a10181010aa4008c161c30508040508012a52389472c72a254088018e504a8110021c)
def layer127r8 : Packing := (163,2,5,63,0,12,1,packed127r8)
def keys127k9 (i : Nat) : Nat := 0x1a6ccf95d1669cd8db8c928a24e8140408bc22f9c20a9673db62780004e7469552188d1d8fc83560c8e9cddd6a9bd5c8d8587a274000dc6a7c0000025808530709dc43e04d85ddec000000002104158e5f597c8fa6461e927e208ed8f800250b96cd30c9086e1d3c999d59fe635201c800000d2a280030474f39a8000003c015f7a164baa81193d03e0963394488510fd77cd40000000000024e1d35618a6aa1254e624e5a8a001f68458e63dc971f1e429f98078b6913a069d9818000003c0c0006575e59b89a287c003d3b652928a49998cf4421408002121515c2edeb51999f13c14066ce6000107612f96345b42a89c0028a45b05e000000217c012866573c5583b639c620adc31cb044b026089d565ac64517bcc1d48001cc43820004e0004002001e18f9800000810440601160c080003800016180000200881241c13304543020c18002081a091
def packed127r9 (i : Nat) : Nat := 0x1a82894e5146a09725107a0a765a0a25091538a2119553c921294f56928894e56a24895438a2119543c921294f52928894e52a24894ea0a4643e825290fa682a43aaa09907195aa92261c652aa48987195a94a689d2a682a446aa0990fa682a43aaa0992aa488eaa488c0aa9a24d2324c02e2afa9a9da528ba0a799c2691865a14a480f6318a82286c1383607800ff597fd54ff58ffd43ff58bfd52ff50bfd32ff587fd51ff507fd31ff583fd50ff503fd30ff483fd10ff802fe66df957be44f78cfee22fd847fa00
def layer127r9 : Packing := (26,1,5,63,0,10,1,packed127r9)
def keys127k10 (i : Nat) : Nat := 0x80000000036000ea12b5f49572e4b0ad84799d861caedc41c455fd8000000002e5b1a28cd862749023a82
def packed127r10 (i : Nat) : Nat := 0x52511ff
def layer127r10 : Packing := (1,0,5,63,0,0,1,packed127r10)
def samples127 : Array (Bits × Bits) := #[(0x1800004003cf00f080079cfff3ffc00fffff,0x191000488045001092028009102449024491),(0x24600061800d3333430019eb400d003ff003ff,0x24622261912512314324492952454912549126),(0xffffffffffffffffffffffffffc9800186000e3cc38c001e73800e003ffffc00,0xffffffffffffffffffffffffffc9844586224a28c28c489452a48a9224a92a48),(0xe0001f8000fc0fc0fffe07c000fffc0000000,0xe0607f8306f80540560e07c30cfc3b0cc330c),(0xfffffffffffffffffffffffffff00001fffff000fff000007ffff00000000000,0xfffffffffffffffffffffffffff00066aa837000ffe00cc07fc6e01b06c1b06c),(0xfffffffffffffffffffffffffffffffe00000000ffffffff8000000000000000,0xfffffffffffffffffffffffffff0a87800038000abfa8f1f8007001c0701c070),(0xffffffffffffffffffffffffffffffffffffffff000000000000000000000000,0xf5781557c0fff00007000003800e0380e0380),(0x0,0x0),(0x0,0x0)]
def cols127 : IndexTree ColumnInfo := (.fork 15 (.fork 7 (.fork 3 (.leaf [(2,0,125,0,8),(4,0,123,0,8),(8,0,119,0,8)]) (.leaf [(16,0,111,0,8),(32,0,95,0,8),(64,0,63,0,8),(0,32,23,72,7)])) (.fork 4 (.leaf [(0,64,15,48,7),(6,0,121,0,7),(40,0,87,0,7),(80,0,47,0,7)]) (.leaf [(0,2,120,5,6),(0,4,120,3,6),(1,0,126,0,6),(8,64,7,48,6)]))) (.fork 7 (.fork 3 (.leaf [(16,32,7,72,6),(24,0,103,0,6),(32,64,15,16,6)]) (.leaf [(64,32,23,8,6),(96,0,31,0,6),(1,2,120,4,5),(1,4,120,2,5)])) (.fork 4 (.leaf [(10,0,117,0,5),(12,0,115,0,5),(18,0,109,0,5),(20,0,107,0,5)]) (.leaf [(48,0,15,0,5),(72,0,23,0,5),(48,64,15,0,5),(72,32,23,0,5)]))))
def levels127 : Nat → Packing
  | 6 => layer127r6
  | 7 => layer127r7
  | 8 => layer127r8
  | 9 => layer127r9
  | 10 => layer127r10
  | _ => emptyPacking
def index127 : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 4 15 4 8 4 0 keys127k7
  | 8 => lookupWord 18 67 6 10 6 0 keys127k8
  | 9 => lookupWord 54 189 7 12 8 0 keys127k9
  | 10 => lookupWord 8 36 4 9 5 0 keys127k10
  | _ => fun _ => none
def g127 : Forest := ⟨127,10,fun j => samples127[j]?.getD (0,0),cols127,#[[]],levels127,index127,noFactory,noFactorySound 127⟩
def packed239r7 (i : Nat) : Nat := 0x84f1b305490f182430300eae6691222f2e5591222eb66691211f365591211eba6691200f3a5591200eea6688a00f6a5588a00faa4488a00ef26684600f725584600fb24484600
def layer239r7 : Packing := (12,3,5,63,0,7,1,packed239r7)
def keys239k8 (i : Nat) : Nat := 0x1ea00007900b32700340000c2ab00c80000760090e58
def packed239r8 (i : Nat) : Nat := 0x140a8e088502a4822060b04326151c210985490840c16106182a30c305481870a1234812446140051a4092230a0030610506105061050a0850a0850a0848d20491185001400a005002ab044ab044aa4e08d549c11c9c112a93823552704727044ab044ab0458215382253822cf71bc02deaf2a1a1a6b95e438be22839fa7b5d9715b1675895d561535404cd26465053c4d62eca723071174490d42805000ffac8907fd54483ff22241ff59110ffaa8887fe44443feb2401ff55200ffc89007ed6488bf6aa445fb91222feac908ff554847fb22423bf99920efcaa907be444837f33221df95510f7c88887f964803fcaa401fe91200dfccd0077e55803df22401af99a44e7cab226ee6688bb72ac45eb91222deccd08f7655847db22423be99a00ef4ab007ba44803f511401fc84600
def layer239r8 : Packing := (40,2,5,63,0,10,1,packed239r8)
def keys239k9 (i : Nat) : Nat := 0x18db4745000d700000b818326800628000018ef8b46003480000000364001c027400294000000054349000679540057d12c65c10001300121002dbc600058f0bf1000000d6c7014f3d8261c0099ade5300015600000000140a00
def packed239r9 (i : Nat) : Nat := 0x1e98062a51e98062a5190a603e528981030528980f3054898113052898102c528980f2c54898112c538a80d40538a80d3c548e81134540c80f2c522a80526522a80526514caa02e5412a602a53d1a602a5190a8fa6098c3aa80994b36a80994530baa9826c02dcae2949c24c8a204781bc661745412c420e43009c1c84e0a800ff593fd54ff913fd62ff54bfd42ff587fd51ff507fd60ff543fd40ff103fd20ff443fe00bf99b7e55ef913ee22fd847fa00
def layer239r9 : Packing := (22,1,5,63,0,10,1,packed239r9)
def keys239k10 (i : Nat) : Nat := 0x1490049c016c001509c000048a0200cad4c5a00000028c0065800016f200012000a57c9a263220000a00a40000030000
def packed239r10 (i : Nat) : Nat := 0x52411ff
def layer239r10 : Packing := (1,0,5,63,0,0,1,packed239r10)
def samples239 : Array (Bits × Bits) := #[(0x600006000f3c06000f3c2000f3ffe003fffff,0x6444064481140648811424905024a49092925),(0x618001180034cd180034ccc0033d001ffc007ff,0x6188891889144918911448c921254909252424a),(0xfffffffffffffffffffffffff860002600038f2600038f30003ce001fffff800,0xfffffffffffffffffffffffff861112611228a2612228a312428a92124a49490),(0xffffffffffffffffffffffffff8000380003f0380003f03fffc0fffe00000000,0xffffffffffffffffffffffffff8198381983e0381b03e015b040fd85b03606c0),(0x0,0x0),(0x3ffffc003ffffc003fffff000000000000,0x1c2a03c0002a03c002a07bf00380700e01c),(0xffffffffffffffffffffffffffffffc00000003fffffffc00000000000000000,0xaaa1e0001c0003d43c3ffc0380001c0380700e0),(0xffffffffffffffffffffffffffffffffffffffc0000000000000000000000000,0xfffffffffffffffffffffffff555e03d5e03ffc01c000001c0000e01c0380700),(0x0,0x0)]
def cols239 : IndexTree ColumnInfo := (.fork 10 (.fork 5 (.fork 2 (.leaf [(8,0,231,0,9),(2,0,237,0,8)]) (.leaf [(4,0,235,0,8),(64,0,175,0,8),(128,0,111,0,8)])) (.fork 2 (.leaf [(0,1,224,14,7),(0,32,7,200,7)]) (.leaf [(1,0,238,0,7),(32,0,207,0,7),(6,0,233,0,7)]))) (.fork 5 (.fork 2 (.leaf [(192,0,47,0,7),(1,2,232,4,6)]) (.leaf [(1,4,232,2,6),(2,1,224,12,6),(4,1,224,10,6)])) (.fork 3 (.leaf [(32,64,15,128,6),(32,128,15,64,6),(64,32,7,136,6)]) (.leaf [(128,32,7,72,6),(3,0,232,0,5),(5,0,232,0,5)]))))
def levels239 : Nat → Packing
  | 7 => layer239r7
  | 8 => layer239r8
  | 9 => layer239r9
  | 10 => layer239r10
  | _ => emptyPacking
def index239 : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 4 23 1 8 4 0 keys239k8
  | 9 => lookupWord 13 64 6 10 6 0 keys239k9
  | 10 => lookupWord 7 47 3 9 5 0 keys239k10
  | _ => fun _ => none
def g239 : Forest := ⟨239,10,fun j => samples239[j]?.getD (0,0),cols239,#[[]],levels239,index239,noFactory,noFactorySound 239⟩
def packed251r9 (i : Nat) : Nat := 0xff
def layer251r9 : Packing := (1,0,0,63,0,0,1,packed251r9)
def samples251 : Array (Bits × Bits) := #[(0xc0000c03ff03000201f0e403fffffff,0xd2400d2825035202a45025510aa5555),(0xffffffffffffffffffffffffffffffeb3002cb00293ac00cc013c9803a0100ff,0xffffffffffffffffffffffffffffffeb324acb25292aca4cd492c9aa2b51a8aa),(0x0,0x0),(0xfffffffffffffffffffffffffffffff3c0030c0031c3000f001cf1ffcc01ff00,0xfffffffffffffffffffffffffffffff3c2430c2431830a0f141850a84d41a2a0),(0xfffffffffffffffffffffffffffffffc0003f0003e0c000fffe0fe000ffe0000,0xfffffffffffffffffffffffffffffffc020bf0213c0c084550a0fc220f148888),(0x3ffffc00ffff00000fffff0000000,0xc5141c00c507000c0af43b0180c0c),(0xfffffffffffffffffffffffffffffffffffc0000000fffffffff000000000000,0x1547000060003a38aa71f000c00603030),(0xfffffffffffffffffffffffffffffffffffffffffff000000000000000000000,0xfffffffffffffffffffffffffffffffeab83aeb83ff00c00180000300180c0c0),(0x0,0x0)]
def cols251 : IndexTree ColumnInfo := (.leaf [(2,0,249,0,9)])
def levels251 : Nat → Packing
  | 9 => layer251r9
  | _ => emptyPacking
def index251 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g251 : Forest := ⟨251,9,fun j => samples251[j]?.getD (0,0),cols251,#[[]],levels251,index251,noFactory,noFactorySound 251⟩
def packed255r7 (i : Nat) : Nat := 0x34707470747040000d1c1d1c1d1c1000000000000aea8a29282726c66605040302a241e18120c0600a3eb634432e32a414ed6c688650654829ead8d10c98ca9061f5b72a19119520c76b685432232a418f56cca8644654828f6d9510cb8ca8853adb2a219419510a79b654432632a2187b6dca8648654431d6da150c90ca8863cdb32a192195108cdb73552ca32c4591baa9975946588a33adcd54b28cb08e476aa65d65196118cf373552ca32c0191eaa99759465803634d3aca32c45006c71a75946584600
def layer255r7 : Packing := (20,5,5,63,0,8,1,packed255r7)
def keys255k8 (i : Nat) : Nat := 0x2420000000004000000a03243e18000c99e95483196ba0002b0000093ef007b80000c19891400000000005c28
def packed255r8 (i : Nat) : Nat := 0x386081a20412082812088e08200012080001c4040d1020a04140904470410000a040000000000000e0030700183400f10109787c14793400e801e18213f0f828f2680100003800c0000041000000041000000001e2f0f8035244517e1f049c7f0f8063271fc3e018c9e1f00c63e137ede372db366d5f51d0b33c4b0cc1b00beaebb96dfb66cab12b5a9a859fe799ce6d97a5894a4c91a408ea348ba2886613811fe7bde06d9a76618957d50529444f92f4a523475174450b414ff3e4f33b4e7384db354cf3249f1d44b084008ffaa898549608ffaa898545608ffaa898589508ffaa89858550afd68688999208ff6a4862152097f69e99595208ffaa89859520afd68688595208ff6a68819520afd6868819520c7fa219719520cefa219419520cf7a2193195209fd2a19119520cfda219119520afd6868895520afb68a88999108ff6a4862151097f69e99595108ffaa89859510afb68a88595108ff6a68819510afb68a8819510c7fa219719510cefa219419510cf7a2193195109fb2a19219510cfba219219510afb68a889551097f69e9959600a7f69c6560a00aef6906560a00af768c6560a00a7f69c6560600aef6906560600af768c6560600e1f61c905946597b69e9959622b9baa9651962297d69e9959611b9daa96519611abd6868899920d1f65d65195208fd2a19119520add6868895520abb68a8899910d1f65d65195108fb2a19219510adb68a8895510bae6909899a00e9e9998521600dae999942160097e69e9959600b9eaa96519600bd668c9895600e9e6188695600bd668c8695600b7a69c6588a00f9a5946588a00bea6906588a00bf268c6588a00bf86846588a00f9a99a5588a00b7c69c6584600f9c5946584600bec6906584600bf468c6584600bf86886584600f9c99a5584600d1f65d651960089f6a29959465c1fa658759465d1b65d6519622d1d65d6519611d1e65d6519600
def layer255r8 : Packing := (76,4,5,63,0,10,1,packed255r8)
def keys255k9 (i : Nat) : Nat := 0x3a9512ca009184e68c77d1d8e00112e4069805c000e0087000002d093f53e6e1502bba358d64c83046f0a80000010725ac4146001e7824e27001a3400214d90b140000076746f5eb324580421d43e0004d85c80a819e9802fc20054f2034240006ae0bc22000f0dc992f05bb1c4acca588e4400b8b382c3ed8fa53384001002802001040004190044415184
def packed255r9 (i : Nat) : Nat := (if i < 1 then 0xecb10a886ff21885442ffd32b2a217fc9859510dfe4c2ca886ffa21654437fd1032a217fc9895510dff444aa885ffa65658037f930b2c01bfe6660a00dfeb2b05006ff195828037fcaac1401bfe6660600dfeb2b03006ff195818037fcaac0c016fd9220266b7ec8901336bf99880597cf920b28cb77d9220255bbec89012addf241659575fccc402c5b7e5520162d7f33100a96df9548054bdd92b33445eec9099a22bf74cacb117bb9996588bed92d2ac45f6e6695622fb6484ab117bb99a5588bedacb2ac45afe6620161dbf2a900b0ebf998805476fcaa402a3ef49599a11f7a484cd08dfda6565847decccb2c23f749695611fbb334ab08fdd24255847deccd2ac23f7565956119fe4c2a4b07bb99a22583edcab112c13fc9854560f7b33422b07dd956115836fcaac10c1bed8588860fb72ac44306df955811837eb0b088c1f765584460f3f2aac0304ff26162543ddccd112a1f6e55889509fe4c2c2a87bd99a11543eecab08aa1afe6660850df6c3444287bb99a221435fcccc08a1bf58684450f7b334222879f999501435fd11332413fc9859520afecb8ca9079f59465482f7b2832a417dd9319520bfac88ca906dfa2255483cfccd2aa41afe88999109fe4c2ca8857f65c65443cfaca32a217bd9419510beec98ca885fb648654436fd112aa21e7e6695510bfcca90d007be26266803df12b33401ef98699a00f7d3330b005fe65885803df4cc42c017fa9959600f7d332cb007de26255803ef12d2ac01f798695600fbc434ab007de99a55803df4cd2ac01f798595600fbcb2cab007be99982803ef4aac1401efa6658a00fbd2aac5007be99952803ef4aaa9401fea6688a00ff4b2c45007fa19622803fd4ab11401efa6660600fbd2ab03007be99961803ef4aab0c01efa6654600fbd2aaa3007fc99a11803fe2cb08c01ff06584600ff92ac23007be24266802bfb2e32c01e7d6519600bdeca0cb005f764c65803cfccd2ac01f789095600d7f33305006df95582803ddccd11401f6e5588a00d7f33303006df95581803deccd08c01f765584600f7d332c1007de95560802ff32a30401f7a5518200f7d332a1007de95550802ff32c28401efa6614200f7d33241007de95520803df4cc88401f7a55442008fecbd10b2d9fa65651967dd32c10cb3f699604659fd4cb0032d7b65c6588bcdaca32c457ad9419622be6c98cb115f96446588afd32032c45e6e6695622afacb8cb08f9d59465846f6b2832c237d59319611bf2c90cb08dfc64065847ceccd2ac233bd94a21609eec9d10a84fd646884827db2544221af98621a00becc990d006de61485802f732842c013f99819600afccb8cb0079e59465802f732832c017d99319600bf4c90cb005fc64465803cf4cd2ac01eea6688a00fb52ac45007bc99a11803ee4ab08c0187d8759465 else (if i < 2 then 0xa309088b1c108058838222e20430182160a620c4820142a40b0508301821409620c4c20142640b050b801e00580183801e0070016006118028460098012604981c0868812504025040620580183600a0d80260049812607021a2049410094101881e2e1e0a71397041c1078b87829c4a5c107041600680101801a0040038b87829c4e5c007001e2e1e0a71297001c005801a00406006801000c48418178b87831e6110d2625e1e0c79f12125e2e030c7949b8b84bf1e52625e2e1e0129b121c4c30b0e10605e2e1e0c7984434989787831e7c384978b80c31e526e2e12fc79498978b87804e6c387130c2e0060260408380183021a2060250608000006206901a404000000062844c922028c1a30400000006284488e2000110dc4c32625e1e0a20c4c325e2e0309b130c9b8b84be600060058010006005801000a106841c0040a006801c0040a3068c1a4069010c0b0de7e1e09b87802f8a16515138685e2e1e01c5c4a1a178b8780716148685e2e1e01f1f878098c65c7e1e0e225971c978b80c25c726e2e12f945c98978b8782616c72625e2e1e01f1f8b87824c7e1e02631971f878388965c725e2e030971c9b8b84be5152625e2e1e098531c98978b87807c7e2e1e091845b8b80685066016e2e11b141824238b87811e60a08e2e1e047984c4b8b87809a618161426e2e1984c4b8b878096619161425e2e0984c489b8b8780947e1e026319387838896425e2e030909b8b84be4132625e2e1e0984898978b87826e2e1e08e9f8b87824a7e2e1e0929f8b87824a7e2e1e0922f9f87804659e74ee274538c9bf4da26a53449934c626152ec96b4b2256529c94749e24c525491b48a24351fc8f347623851ac8cf46222d514489744621f50d485f42c214509484742020e506482b410205501c8074001fe4fe47eb3f41f84fbc7d73e81f14f747b33d61e94f3c7973c81e34f0c7833be1d94ebc7573a01ce4e6472b3921c84e347133881c34dec6ef3741b44d946c335e1ad4d646ab3521a84d3c69733e1974cac63f3141834c0c5fb2fa1764b745b32ce1614ad45632ac1544a9c5472a21504a7453729814a4a4c51f28e1464a2c5132881424a044fb27c13d49e44ef27613949b44d7268132498c4c326012f49744b3254129494447f23e118488c44322010e486442f216109483c41b20c10448144032000fe47e43eb1f40f847b43d31e60ec473437b1ae0cf464c30f17c0b8458c2a714a09f44cc24f11c08743fc1eb0e806d433417f0b2052425c11307a038419c0bb05402340e406302800f40540170002ffd32402cb7fd9220165bfec8900b2dff65486482ff93133241bfe8899920bfecb10a906ff21885482ffd32b2a417fc9859520dfe4c2ca906ffa21654837fd1032a417fc9895520dff444aa905ff65486442ff93133221bfe8899910bf else 0x8e20b89902e2630b1c962c704201a2c726881610b08c38f1c1e2042c228a30a088b1c108058b1c962c704201a2c726881610b08c48f1c1e2042c228))
def layer255r9 : Packing := (218,3,5,63,0,13,1,packed255r9)
def keys255k10 (i : Nat) : Nat := 0x4d2152d07bc60a18b2e9402fb6575ea69bc2f9244ad8fe1d25ac16eade64c6100314fe01f4580d631ed9a7396e00072a6be090000e74fa3927d960a7fbfe9aed548dd859a5b827987b5eca69d54d81734350a426b2df6c0058a910069c411fa4514d9715f9c32b8338280134b8b00098800000000038638c00018933d353eaa87fac867cc47dd7d1c7b4b1590efbb80b84005005be4699f0000005329ce6c022100001ae3a956bb60377d1e2c90f5597d6e66872ea6258c9904b813870e091c73c1c6bab152245131b32e493e04667c0294e29174408e000b410000007065280000001ac00015c000084471e8149ed420009127af97dbaef6a13f0785c53b92a2c830951d0749fb3b7ec1097bdcbb20000919000976139457f35000ebc17500000041e0009d3e87a481548d4000000b0890cabd000000dccc6fd5d000924e25cab52b0000007d83332687a06c95233b771fc77518aa897a89b7624607bac3b33c76d063ac4336e4c2295b01cd679c55000e30dcfa8ad3e300140400001210a2c1963c2818600041b30c3812302180060000103440c0020e0c003086400c002808408142811c08209400001802343460a00081047888e
def packed255r10 (i : Nat) : Nat := (if i < 1 then 0x88f161c09684c97161c0393ce97161c09c9cc9b161c09c9cc992e2c3807279d2e2c38139299362c381392989e0c584d1218d8c8a9b263c5870524f0e2c06c90c685c64b931e2c38290c17161c0393ce9f161c0589cc182e2c3807279d3e2c380a1298da52d8b061293a6278b0e02531a4c5b161c05274a4f161c04a64c97161c0213ce992e2c3804279f3e1c0188ca2f3e1c1882cd9c2e2c0425ce1b1611f2e30c149e2c3827c818292c58704e20305cf8b0e09cd9acf8b0e099362c3823ca97161c11e54d8b0e08f2a5c58704795367c58704a973e2c38252c4f161c09e6284b161c09e6f7dfaf7cffe41f01f74fb0fd57e85f337903c51e02ef57713b4bd7fea5f45f9e3cbde52f2458f2c56e1f707f808be8de6aed5741b8c5bbed7f68fb2fd8bec0d5cfacfd5a2a7f50fa6c52868d542c9facefa71d35e99acbfa59d29793748fa40f1d08ccc56e2490ed85ec21a0ad0267f7befdf10f4a790bb8dd66e75722b855bcadae6bf351da2ece065831e5884c045edae756dab2f57fab3d530a68518a8053949934b1a4b11f88c544721790407e93dc9db4e6c6f83609a44cc262a2fd1728b34555292938095247922110487b63ab1ba0d1061a2d615689f44a822b0fa06f430c15609684101b60b20448180060000ffc80597ff54960ffd51583ff58950ffd61543ff21920ffe66483ff21520ffd65483ff19520ffe55483ff21910ffe66443ff21510ffd65443ff19510ffe55443ff99a00ffd65803ff19600ffe55803bf21666efc8099aff20266bfe88597bf99965bfc80596ff60865bfd81196ff60065f7c86957df99a55f7c80957bf99a55f7d65956ff20255bfe8858bbf99962f7e5558aff20162bfe8854aff61952efe6654bdf95552fed6254aff20152fee6688bfb59622fec6588bfb95622bfe88587bf99961f7e55586ff20161bfe88546ff61951efe66547df95551ff561546ff20151ff666847fd59611ff465847fd95611bfe88583bf99960f7e55583bf58960fee22583bf58560ff611582ff61460f7e55182ff60860fee22182ff60460ff611183bf58060bfe88542ff61950efe66543df95550f7d52543fb88950f7d51543fd84550ff960542ff61850efe66142ff60850fee22142ff60450ff611143df54050bfe88482ff61920efe66482ff61520f7e55482ffa2110bfd86443bf99910bfd85443df95510ff986803fe21a00ffa66803fe61600ff885803fe59600ff865803fe95600ff982803fe58a00ff952803fe60600ff961803fe54600bfd86803bf99a00bfd85803df95600bfd82803fb88a00bfd81803fd84600ff960803fe18200ff950803fe14200ff920803fe442009fd871979f59465bbd84196f760c65bed82196fd60465bf9801979f99a55eee6688bdb95622ef666847dd95611efa66803de95600fea22803fc84600 else 0x182e4c787062174060b8b027c24cb50182e2c09f092294060b8b0a7c04cb50182e2c29f01229462c3813088f31b1d1528cc5870474d562c3812888f30e181828b11870628f50a4d88461c11d2d0687464c2f161c11d2d58b0e04c223cc6c7454a33161c11d3558b0e04a223cc386060a2c461c18a3d42536211870474b41a1d1930bc5870474b51b19152c4490d18e118b0e04d71318182c4490d18b104b0e0c5744864c426c5870124b51a1719344490d18e118b0e04b706c58702537306c18b09a949e0c58491a18509119f161c0305d3121e1c188d4d1460b278b0e0254060b8b0e04e4c70c17161c09c90e18296c5870141c2e2c38131a9b161c098d4a170e2c06e5c587045372a4478706235313c38b01236347c58701a26306c18b0c735360c58639a9459ac58700e8f3c7c58701b2630c1787047c44c7c38b04737285c38b04737305c587007344c7186f161c03a3ce4d2e2c3823a69cb134c970e08f8a82c9b161c11d2ce4d362c3823a59e3e2c380d1218360c58639a9b062c31cd4a2cd62c3807479e3e2c380d921860bc3823e2243e1c58239b942e1c58239b982e2c38039a2438c378b0e01d1e72497161c11d34e509264b87047c54144d8b0e08e967249b161c11d2ce5b161c050d4d12186c58309a9e243c18b09a9b062c29c99a1a345c49f0612d3e0c585392343468b893e0c2527264b161c19c30ba02e2c38234a6c286c587027274278d8b0e02731b0a1b161c09c9509e362c38094d889e1c04844c5b161c050dcc30596c5870141e243c38b01b9a2430b8b0e0373e1c581393363468b893e1c05a7c38b027246c68d17127c380a4e17116c380d141c992c5870670a3280d8b0e08b29a0c17161c09c9d09e2e2c3809cc68305c587027254278b8b0e02536227870121130c178b0e0111e7118b0618e6861914de2c3823ce23161c11cd8c2e31ac5870479c60bc5870088f388c5830c73430c8a6f161c11e7118b0e08e6c61718d62c3823ce99293c5870129d3622d8701498425488f161c09a84c949e2c38094e97116c380a4c4c4264a91192c3831544c926c5870259c4264)
def layer255r10 : Packing := (148,2,5,63,0,13,1,packed255r10)
def keys255k11 (i : Nat) : Nat := 0x12cb4d186c42a944900040a00019200028279d98420909ba8ebb5928d2200040162fdc61b20af0000bb0005976866c0a0b52510680810e0b34a703dbb62bf2b6eb50007b81286bc249d3c80000028b899f23308f85424738f3bb42fa1a2d09f6b2bb4731a09e39e14505d9d396b24e950b1447a41e45d0491c81a687b11922997eb7b030c843a0a59ab53ebae0acba6c02d0ab46e80581d9c0438c244028c39edbfcb3fb03c140dbadeb080000000000020fc9629fc3700d69163a8bd10cd44bc531309392c31a9200430007a98002190000005be73900031e60f798b488005158006a1490710800420dae80038700042671b6473a7eaaaa3c8382a700f94eab8b058c010820451d34002822a08124000431a0e004830030f000624b0876e00871800009280010102e8007
def packed255r11 (i : Nat) : Nat := 0x1a15b9e28601a814c18b9e1822a271a28601666c66a78a1805a054e08a16879c64e18a06c79c54a08a16879c64a18a06c79c51889e281a8684db4a78a1806a061489e285b8284da4a78a1805a061532228601e81854888a1807a061532278a1812a469e28609459e28609628601e48a18079278a1824de342c62e2aca8294a227b1b66014a450de2887e1683c07800ffccdff597fe32ffe55ffac5ff54bfeb0ffd51ffac1ff183fea87fc50ffa41ff443ff006fe66efcabfb88bfb08ffa00
def layer255r11 : Packing := (20,1,5,63,0,10,1,packed255r11)
def keys255k12 (i : Nat) : Nat := 0x3a2000000000000014800283280000000000227e045b33a000f26885e00470000000b199f02c90000000000000000007543401660a4300
def packed255r12 (i : Nat) : Nat := 0xe20824ff
def layer255r12 : Packing := (1,0,5,63,0,0,1,packed255r12)
def samples255 : Array (Bits × Bits) := #[(0xc0000006000e79e7801800002000f3c03c2000f39fff3ffe003fffff,0xc8880006448008228019220024881140042490500125024a49092925),(0x48c3000231180035a699a4600030c0034cccd0c0033d6800d001ffc007ff,0x48c3111231188914a28924624430c911448c50c921252a4854909252424a),(0xffff930c0004c2600039c71e498000c300038f30e30003ce7000e001fffff800,0xffff930c2224c26112294514498488c312228a30a312428a5490a92124a49490),(0xffffe3f000070380003e07e00e0000fc0003f03f03fffc0f8000fffe00000000,0xffffe3f033070381983e07c00e06c0fc1b03e015015b040f86c0fd85b03606c0),(0xfffffc000007fc00003ff800700000fffffc003ffc00000fffff000000000000,0xfffffc003037fc01833ff00070060c555834003ff818600ffe1a0c318630c618),(0x7ffffffc000007fffff000000003ffffffff00000000000000000,0x38542a03c0000070a80f000038002afea07bf0001c00380700e01c),(0xfffffffffff80000000000007fffffffffffffc0000000000000000000000000,0x15543c000001c0000000f50f0aaa3c3ffc00003800000e001c0380700e0),(0xffffffffffffffffffffffff8000000000000000000000000000000000000000,0xfffffeaabc07abd5e03fffff800700001c000000001c000007000e01c0380700),(0x0,0x0)]
def cols255 : IndexTree ColumnInfo := (.fork 14 (.fork 7 (.fork 3 (.leaf [(8,0,247,0,11),(16,0,239,0,11),(128,0,127,0,11)]) (.leaf [(2,0,253,0,10),(4,0,251,0,10),(32,0,223,0,9),(64,0,191,0,9)])) (.fork 3 (.leaf [(6,0,249,0,9),(0,1,224,30,8),(0,2,248,5,8)]) (.leaf [(0,4,248,3,8),(0,32,23,200,8),(0,64,15,176,8),(0,128,31,96,8)]))) (.fork 7 (.fork 3 (.leaf [(1,0,254,0,8),(40,0,215,0,8),(80,0,175,0,8)]) (.leaf [(160,0,95,0,8),(1,2,248,4,7),(1,4,248,2,7),(2,1,224,28,7)])) (.fork 3 (.leaf [(2,4,248,1,7),(4,1,224,26,7),(4,2,248,1,7)]) (.leaf [(8,1,224,22,7),(16,1,224,14,7),(32,64,15,144,7),(64,32,23,136,7)]))))
def levels255 : Nat → Packing
  | 7 => layer255r7
  | 8 => layer255r8
  | 9 => layer255r9
  | 10 => layer255r10
  | 11 => layer255r11
  | 12 => layer255r12
  | _ => emptyPacking
def index255 : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 6 37 5 9 5 0 keys255k8
  | 9 => lookupWord 25 90 5 11 7 0 keys255k9
  | 10 => lookupWord 72 250 7 12 8 0 keys255k10
  | 11 => lookupWord 49 171 7 12 8 0 keys255k11
  | 12 => lookupWord 6 47 4 9 5 0 keys255k12
  | _ => fun _ => none
def g255 : Forest := ⟨255,12,fun j => samples255[j]?.getD (0,0),cols255,#[[]],levels255,index255,noFactory,noFactorySound 255⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom7 : graphValid g7 (boundsBefore []) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice7k3p0 : block g7 3 0 1 = true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK7k3 : block g7 3 0 1=true := slice7k3p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked7 : checkedTables g7 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g7 0 0 0=true)
  · exact (rfl : block g7 1 0 0=true)
  · exact (rfl : block g7 2 0 0=true)
  · exact layerOK7k3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low7 : Lower (vars 7) (graphGoal 7) 4 :=
  lower_forest (g:=g7) (i:=0) (hints:=1) (before_sound [] baseKnown) geom7 checked7 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps7 : List (Nat × List Nat) := [(7,[]),(224,[33,32,113,96,82,65,48])]
def known7 := extendKnown [] 4 maps7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid7 : Known known7 := extendKnown_ok baseKnown low7 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom43 : graphValid g43 (boundsBefore known7) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice43k3p0 : block g43 3 0 1 = true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK43k3 : block g43 3 0 1=true := slice43k3p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked43 : checkedTables g43 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g43 0 0 0=true)
  · exact (rfl : block g43 1 0 0=true)
  · exact (rfl : block g43 2 0 0=true)
  · exact layerOK43k3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low43 : Lower (vars 43) (graphGoal 43) 4 :=
  lower_forest (g:=g43) (i:=0) (hints:=3145729) (before_sound known7 valid7) geom43 checked43 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps43 : List (Nat × List Nat) := [(43,[]),(45,[33]),(57,[65,33]),(89,[101,49,65,33]),(105,[83,99,48,64,32,16]),(113,[99,64,32,16]),(120,[48,83,49,96,65,32])]
def known43 := extendKnown known7 4 maps43
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid43 : Known known43 := extendKnown_ok valid7 low43 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom15 : graphValid g15 (boundsBefore known43) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice15k4p0 : block g15 4 0 1 = true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK15k4 : block g15 4 0 1=true := slice15k4p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked15 : checkedTables g15 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g15 0 0 0=true)
  · exact (rfl : block g15 1 0 0=true)
  · exact (rfl : block g15 2 0 0=true)
  · exact (rfl : block g15 3 0 0=true)
  · exact layerOK15k4
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low15 : Lower (vars 15) (graphGoal 15) 5 :=
  lower_forest (g:=g15) (i:=0) (hints:=1) (before_sound known43 valid43) geom15 checked15 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps15 : List (Nat × List Nat) := [(15,[]),(23,[67]),(232,[33,16,112,98,81,64]),(240,[32,48,115,98,81,64])]
def known15 := extendKnown known43 5 maps15
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid15 : Known known15 := extendKnown_ok valid43 low15 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom103 : graphValid g103 (boundsBefore known15) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice103k5p0 : block g103 5 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK103k5 : block g103 5 0 1=true := slice103k5p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked103 : checkedTables g103 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g103 0 0 0=true)
  · exact (rfl : block g103 1 0 0=true)
  · exact (rfl : block g103 2 0 0=true)
  · exact (rfl : block g103 3 0 0=true)
  · exact (rfl : block g103 4 0 0=true)
  · exact layerOK103k5
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low103 : Lower (vars 103) (graphGoal 103) 6 :=
  lower_forest (g:=g103) (i:=0) (hints:=90177537) (before_sound known15 valid15) geom103 checked103 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps103 : List (Nat × List Nat) := [(103,[]),(167,[118]),(199,[101,117]),(227,[114,66,50,97,80]),(229,[33,113,65,98,49,80]),(230,[33,16,112,64,98,81,48])]
def known103 := extendKnown known15 6 maps103
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid103 : Known known103 := extendKnown_ok valid15 low103 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom107 : graphValid g107 (boundsBefore known103) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice107k4p0 : block g107 4 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK107k4 : block g107 4 0 1=true := slice107k4p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked107 : checkedTables g107 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g107 0 0 0=true)
  · exact (rfl : block g107 1 0 0=true)
  · exact (rfl : block g107 2 0 0=true)
  · exact (rfl : block g107 3 0 0=true)
  · exact layerOK107k4
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low107 : Lower (vars 107) (graphGoal 107) 5 :=
  lower_forest (g:=g107) (i:=0) (hints:=87031809) (before_sound known103 valid103) geom107 checked107 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps107 : List (Nat × List Nat) := [(107,[]),(109,[33]),(115,[101,67]),(117,[101,67,33]),(185,[118,65,33]),(217,[101,117,49,65,33])]
def known107 := extendKnown known103 5 maps107
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid107 : Known known107 := extendKnown_ok valid103 low107 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom121 : graphValid g121 (boundsBefore known107) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice121k5p0 : block g121 5 0 5 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice121k5p5 : block g121 5 5 10 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK121k5 : block g121 5 0 15=true := (@block_merge g121 5 0 5 10 slice121k5p0 slice121k5p5)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice121k6p0 : block g121 6 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK121k6 : block g121 6 0 1=true := slice121k6p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked121 : checkedTables g121 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g121 0 0 0=true)
  · exact (rfl : block g121 1 0 0=true)
  · exact (rfl : block g121 2 0 0=true)
  · exact (rfl : block g121 3 0 0=true)
  · exact (rfl : block g121 4 0 0=true)
  · exact layerOK121k5
  · exact layerOK121k6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low121 : Lower (vars 121) (graphGoal 121) 7 :=
  lower_forest (g:=g121) (i:=0) (hints:=70254595) (before_sound known107 valid107) geom121 checked121 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps121 : List (Nat × List Nat) := [(121,[])]
def known121 := extendKnown known107 7 maps121
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid121 : Known known121 := extendKnown_ok valid107 low121 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom47 : graphValid g47 (boundsBefore known121) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice47k5p0 : block g47 5 0 3 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice47k5p3 : block g47 5 3 4 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK47k5 : block g47 5 0 7=true := (@block_merge g47 5 0 3 4 slice47k5p0 slice47k5p3)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice47k6p0 : block g47 6 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK47k6 : block g47 6 0 1=true := slice47k6p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked47 : checkedTables g47 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g47 0 0 0=true)
  · exact (rfl : block g47 1 0 0=true)
  · exact (rfl : block g47 2 0 0=true)
  · exact (rfl : block g47 3 0 0=true)
  · exact (rfl : block g47 4 0 0=true)
  · exact layerOK47k5
  · exact layerOK47k6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low47 : Lower (vars 47) (graphGoal 47) 7 :=
  lower_forest (g:=g47) (i:=0) (hints:=3145729) (before_sound known121 valid121) geom47 checked47 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps47 : List (Nat × List Nat) := [(47,[]),(87,[101,67]),(233,[33,113,98,65,80]),(241,[32,16,49,115,98,65,80])]
def known47 := extendKnown known121 7 maps47
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid47 : Known known47 := extendKnown_ok valid121 low47 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom248 : graphValid g248 (boundsBefore known47) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice248k5p0 : block g248 5 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK248k5 : block g248 5 0 1=true := slice248k5p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked248 : checkedTables g248 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g248 0 0 0=true)
  · exact (rfl : block g248 1 0 0=true)
  · exact (rfl : block g248 2 0 0=true)
  · exact (rfl : block g248 3 0 0=true)
  · exact (rfl : block g248 4 0 0=true)
  · exact layerOK248k5
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low248 : Lower (vars 248) (graphGoal 248) 6 :=
  lower_forest (g:=g248) (i:=0) (hints:=1412845568) (before_sound known47 valid47) geom248 checked248 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps248 : List (Nat × List Nat) := [(248,[])]
def known248 := extendKnown known47 6 maps248
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid248 : Known known248 := extendKnown_ok valid47 low248 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom31 : graphValid g31 (boundsBefore known248) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice31k5p0 : block g31 5 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK31k5 : block g31 5 0 1=true := slice31k5p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked31 : checkedTables g31 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g31 0 0 0=true)
  · exact (rfl : block g31 1 0 0=true)
  · exact (rfl : block g31 2 0 0=true)
  · exact (rfl : block g31 3 0 0=true)
  · exact (rfl : block g31 4 0 0=true)
  · exact layerOK31k5
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low31 : Lower (vars 31) (graphGoal 31) 6 :=
  lower_forest (g:=g31) (i:=0) (hints:=1) (before_sound known248 valid248) geom31 checked31 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps31 : List (Nat × List Nat) := [(31,[])]
def known31 := extendKnown known248 6 maps31
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid31 : Known known31 := extendKnown_ok valid248 low31 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom126 : graphValid g126 (boundsBefore known31) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice126k5p0 : block g126 5 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK126k5 : block g126 5 0 1=true := slice126k5p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked126 : checkedTables g126 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g126 0 0 0=true)
  · exact (rfl : block g126 1 0 0=true)
  · exact (rfl : block g126 2 0 0=true)
  · exact (rfl : block g126 3 0 0=true)
  · exact (rfl : block g126 4 0 0=true)
  · exact layerOK126k5
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low126 : Lower (vars 126) (graphGoal 126) 6 :=
  lower_forest (g:=g126) (i:=0) (hints:=70668576) (before_sound known31 valid31) geom126 checked126 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps126 : List (Nat × List Nat) := [(126,[])]
def known126 := extendKnown known31 6 maps126
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid126 : Known known126 := extendKnown_ok valid31 low126 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom183 : graphValid g183 (boundsBefore known126) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice183k6p0 : block g183 6 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK183k6 : block g183 6 0 1=true := slice183k6p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked183 : checkedTables g183 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g183 0 0 0=true)
  · exact (rfl : block g183 1 0 0=true)
  · exact (rfl : block g183 2 0 0=true)
  · exact (rfl : block g183 3 0 0=true)
  · exact (rfl : block g183 4 0 0=true)
  · exact (rfl : block g183 5 0 0=true)
  · exact layerOK183k6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low183 : Lower (vars 183) (graphGoal 183) 7 :=
  lower_forest (g:=g183) (i:=0) (hints:=1349517313) (before_sound known126 valid126) geom183 checked183 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps183 : List (Nat × List Nat) := [(207,[101,67]),(238,[16,96,64,114,81,48])]
def known183 := extendKnown known126 7 maps183
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid183 : Known known183 := extendKnown_ok valid126 low183 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom231 : graphValid g231 (boundsBefore known183) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=2) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice231k6p0 : block g231 6 0 9 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK231k6 : block g231 6 0 9=true := slice231k6p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice231k7p0 : block g231 7 0 6 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK231k7 : block g231 7 0 6=true := slice231k7p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice231k8p0 : block g231 8 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK231k8 : block g231 8 0 1=true := slice231k8p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked231 : checkedTables g231 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g231 0 0 0=true)
  · exact (rfl : block g231 1 0 0=true)
  · exact (rfl : block g231 2 0 0=true)
  · exact (rfl : block g231 3 0 0=true)
  · exact (rfl : block g231 4 0 0=true)
  · exact (rfl : block g231 5 0 0=true)
  · exact layerOK231k6
  · exact layerOK231k7
  · exact layerOK231k8
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low231 : Lower (vars 231) (graphGoal 231) 9 :=
  lower_forest (g:=g231) (i:=0) (hints:=1432354817) (before_sound known183 valid183) geom231 checked231 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps231 : List (Nat × List Nat) := [(231,[])]
def known231 := extendKnown known183 9 maps231
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid231 : Known known231 := extendKnown_ok valid183 low231 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom111 : graphValid g111 (boundsBefore known231) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice111k7p0 : block g111 7 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK111k7 : block g111 7 0 1=true := slice111k7p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked111 : checkedTables g111 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g111 0 0 0=true)
  · exact (rfl : block g111 1 0 0=true)
  · exact (rfl : block g111 2 0 0=true)
  · exact (rfl : block g111 3 0 0=true)
  · exact (rfl : block g111 4 0 0=true)
  · exact (rfl : block g111 5 0 0=true)
  · exact (rfl : block g111 6 0 0=true)
  · exact layerOK111k7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low111 : Lower (vars 111) (graphGoal 111) 8 :=
  lower_forest (g:=g111) (i:=0) (hints:=87031809) (before_sound known231 valid231) geom111 checked111 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps111 : List (Nat × List Nat) := [(111,[]),(119,[101,67]),(175,[118]),(215,[101,117,67]),(235,[114,66,97,80]),(237,[33,113,98,65,80])]
def known111 := extendKnown known231 8 maps111
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid111 : Known known111 := extendKnown_ok valid231 low111 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom63 : graphValid g63 (boundsBefore known111) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice63k7p0 : block g63 7 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK63k7 : block g63 7 0 1=true := slice63k7p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked63 : checkedTables g63 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g63 0 0 0=true)
  · exact (rfl : block g63 1 0 0=true)
  · exact (rfl : block g63 2 0 0=true)
  · exact (rfl : block g63 3 0 0=true)
  · exact (rfl : block g63 4 0 0=true)
  · exact (rfl : block g63 5 0 0=true)
  · exact (rfl : block g63 6 0 0=true)
  · exact layerOK63k7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low63 : Lower (vars 63) (graphGoal 63) 8 :=
  lower_forest (g:=g63) (i:=0) (hints:=3145729) (before_sound known111 valid111) geom63 checked63 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps63 : List (Nat × List Nat) := [(63,[]),(95,[101,67])]
def known63 := extendKnown known111 8 maps63
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid63 : Known known63 := extendKnown_ok valid111 low63 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom123 : graphValid g123 (boundsBefore known63) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice123k7p0 : block g123 7 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK123k7 : block g123 7 0 1=true := slice123k7p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked123 : checkedTables g123 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g123 0 0 0=true)
  · exact (rfl : block g123 1 0 0=true)
  · exact (rfl : block g123 2 0 0=true)
  · exact (rfl : block g123 3 0 0=true)
  · exact (rfl : block g123 4 0 0=true)
  · exact (rfl : block g123 5 0 0=true)
  · exact (rfl : block g123 6 0 0=true)
  · exact layerOK123k7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low123 : Lower (vars 123) (graphGoal 123) 8 :=
  lower_forest (g:=g123) (i:=0) (hints:=70254593) (before_sound known63 valid63) geom123 checked123 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps123 : List (Nat × List Nat) := [(123,[]),(125,[33])]
def known123 := extendKnown known63 8 maps123
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid123 : Known known123 := extendKnown_ok valid63 low123 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom249 : graphValid g249 (boundsBefore known123) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice249k5p0 : block g249 5 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK249k5 : block g249 5 0 1=true := slice249k5p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice249k6p0 : block g249 6 0 6 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice249k6p6 : block g249 6 6 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK249k6 : block g249 6 0 7=true := (@block_merge g249 6 0 6 1 slice249k6p0 slice249k6p6)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice249k7p0 : block g249 7 0 3 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice249k7p3 : block g249 7 3 4 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK249k7 : block g249 7 0 7=true := (@block_merge g249 7 0 3 4 slice249k7p0 slice249k7p3)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice249k8p0 : block g249 8 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK249k8 : block g249 8 0 1=true := slice249k8p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked249 : checkedTables g249 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g249 0 0 0=true)
  · exact (rfl : block g249 1 0 0=true)
  · exact (rfl : block g249 2 0 0=true)
  · exact (rfl : block g249 3 0 0=true)
  · exact (rfl : block g249 4 0 0=true)
  · exact layerOK249k5
  · exact layerOK249k6
  · exact layerOK249k7
  · exact layerOK249k8
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low249 : Lower (vars 249) (graphGoal 249) 9 :=
  lower_forest (g:=g249) (i:=0) (hints:=1412431875) (before_sound known123 valid123) geom249 checked249 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps249 : List (Nat × List Nat) := [(249,[])]
def known249 := extendKnown known123 9 maps249
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid249 : Known known249 := extendKnown_ok valid123 low249 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom254 : graphValid g254 (boundsBefore known249) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice254k7p0 : block g254 7 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK254k7 : block g254 7 0 1=true := slice254k7p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked254 : checkedTables g254 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g254 0 0 0=true)
  · exact (rfl : block g254 1 0 0=true)
  · exact (rfl : block g254 2 0 0=true)
  · exact (rfl : block g254 3 0 0=true)
  · exact (rfl : block g254 4 0 0=true)
  · exact (rfl : block g254 5 0 0=true)
  · exact (rfl : block g254 6 0 0=true)
  · exact layerOK254k7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low254 : Lower (vars 254) (graphGoal 254) 8 :=
  lower_forest (g:=g254) (i:=0) (hints:=1412845856) (before_sound known249 valid249) geom254 checked254 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps254 : List (Nat × List Nat) := [(254,[])]
def known254 := extendKnown known249 8 maps254
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid254 : Known known254 := extendKnown_ok valid249 low254 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom191 : graphValid g191 (boundsBefore known254) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice191k8p0 : block g191 8 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK191k8 : block g191 8 0 1=true := slice191k8p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked191 : checkedTables g191 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g191 0 0 0=true)
  · exact (rfl : block g191 1 0 0=true)
  · exact (rfl : block g191 2 0 0=true)
  · exact (rfl : block g191 3 0 0=true)
  · exact (rfl : block g191 4 0 0=true)
  · exact (rfl : block g191 5 0 0=true)
  · exact (rfl : block g191 6 0 0=true)
  · exact (rfl : block g191 7 0 0=true)
  · exact layerOK191k8
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low191 : Lower (vars 191) (graphGoal 191) 9 :=
  lower_forest (g:=g191) (i:=0) (hints:=1345323009) (before_sound known254 valid254) geom191 checked191 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps191 : List (Nat × List Nat) := [(191,[]),(223,[101,67])]
def known191 := extendKnown known254 9 maps191
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid191 : Known known191 := extendKnown_ok valid254 low191 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom127 : graphValid g127 (boundsBefore known191) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice127k6p0 : block g127 6 0 4 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice127k6p4 : block g127 6 4 8 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK127k6 : block g127 6 0 12=true := (@block_merge g127 6 0 4 8 slice127k6p0 slice127k6p4)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice127k7p0 : block g127 7 0 34 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice127k7p34 : block g127 7 34 22 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK127k7 : block g127 7 0 56=true := (@block_merge g127 7 0 34 22 slice127k7p0 slice127k7p34)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice127k8p0 : block g127 8 0 18 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice127k8p18 : block g127 8 18 64 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice127k8p82 : block g127 8 82 44 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice127k8p126 : block g127 8 126 37 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK127k8 : block g127 8 0 163=true := (@block_merge g127 8 0 126 37 (@block_merge g127 8 0 82 44 (@block_merge g127 8 0 18 64 slice127k8p0 slice127k8p18) slice127k8p82) slice127k8p126)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice127k9p0 : block g127 9 0 7 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice127k9p7 : block g127 9 7 19 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK127k9 : block g127 9 0 26=true := (@block_merge g127 9 0 7 19 slice127k9p0 slice127k9p7)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice127k10p0 : block g127 10 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK127k10 : block g127 10 0 1=true := slice127k10p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked127 : checkedTables g127 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g127 0 0 0=true)
  · exact (rfl : block g127 1 0 0=true)
  · exact (rfl : block g127 2 0 0=true)
  · exact (rfl : block g127 3 0 0=true)
  · exact (rfl : block g127 4 0 0=true)
  · exact (rfl : block g127 5 0 0=true)
  · exact layerOK127k6
  · exact layerOK127k7
  · exact layerOK127k8
  · exact layerOK127k9
  · exact layerOK127k10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low127 : Lower (vars 127) (graphGoal 127) 11 :=
  lower_forest (g:=g127) (i:=0) (hints:=70254593) (before_sound known191 valid191) geom127 checked127 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps127 : List (Nat × List Nat) := [(127,[])]
def known127 := extendKnown known191 11 maps127
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid127 : Known known127 := extendKnown_ok valid191 low127 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom239 : graphValid g239 (boundsBefore known127) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice239k7p0 : block g239 7 0 12 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK239k7 : block g239 7 0 12=true := slice239k7p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice239k8p0 : block g239 8 0 13 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice239k8p13 : block g239 8 13 18 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice239k8p31 : block g239 8 31 9 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK239k8 : block g239 8 0 40=true := (@block_merge g239 8 0 31 9 (@block_merge g239 8 0 13 18 slice239k8p0 slice239k8p13) slice239k8p31)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice239k9p0 : block g239 9 0 6 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice239k9p6 : block g239 9 6 16 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK239k9 : block g239 9 0 22=true := (@block_merge g239 9 0 6 16 slice239k9p0 slice239k9p6)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice239k10p0 : block g239 10 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK239k10 : block g239 10 0 1=true := slice239k10p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked239 : checkedTables g239 10 := by
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
  · exact layerOK239k8
  · exact layerOK239k9
  · exact layerOK239k10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low239 : Lower (vars 239) (graphGoal 239) 11 :=
  lower_forest (g:=g239) (i:=0) (hints:=1429209089) (before_sound known127 valid127) geom239 checked239 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps239 : List (Nat × List Nat) := [(239,[]),(247,[101,67])]
def known239 := extendKnown known127 11 maps239
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid239 : Known known239 := extendKnown_ok valid127 low239 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom251 : graphValid g251 (boundsBefore known239) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice251k9p0 : block g251 9 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK251k9 : block g251 9 0 1=true := slice251k9p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked251 : checkedTables g251 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g251 0 0 0=true)
  · exact (rfl : block g251 1 0 0=true)
  · exact (rfl : block g251 2 0 0=true)
  · exact (rfl : block g251 3 0 0=true)
  · exact (rfl : block g251 4 0 0=true)
  · exact (rfl : block g251 5 0 0=true)
  · exact (rfl : block g251 6 0 0=true)
  · exact (rfl : block g251 7 0 0=true)
  · exact (rfl : block g251 8 0 0=true)
  · exact layerOK251k9
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low251 : Lower (vars 251) (graphGoal 251) 10 :=
  lower_forest (g:=g251) (i:=0) (hints:=1412431873) (before_sound known239 valid239) geom251 checked251 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps251 : List (Nat × List Nat) := [(251,[]),(253,[33])]
def known251 := extendKnown known239 10 maps251
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid251 : Known known251 := extendKnown_ok valid239 low251 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom255 : graphValid g255 (boundsBefore known251) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k7p0 : block g255 7 0 8 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k7p8 : block g255 7 8 12 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK255k7 : block g255 7 0 20=true := (@block_merge g255 7 0 8 12 slice255k7p0 slice255k7p8)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k8p0 : block g255 8 0 5 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k8p5 : block g255 8 5 34 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k8p39 : block g255 8 39 37 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK255k8 : block g255 8 0 76=true := (@block_merge g255 8 0 39 37 (@block_merge g255 8 0 5 34 slice255k8p0 slice255k8p5) slice255k8p39)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k9p0 : block g255 9 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k9p1 : block g255 9 1 39 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k9p40 : block g255 9 40 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k9p104 : block g255 9 104 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k9p168 : block g255 9 168 13 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k9p181 : block g255 9 181 37 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK255k9 : block g255 9 0 218=true := (@block_merge g255 9 0 181 37 (@block_merge g255 9 0 168 13 (@block_merge g255 9 0 104 64 (@block_merge g255 9 0 40 64 (@block_merge g255 9 0 1 39 slice255k9p0 slice255k9p1) slice255k9p40) slice255k9p104) slice255k9p168) slice255k9p181)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k10p0 : block g255 10 0 16 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k10p16 : block g255 10 16 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k10p80 : block g255 10 80 47 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k10p127 : block g255 10 127 21 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK255k10 : block g255 10 0 148=true := (@block_merge g255 10 0 127 21 (@block_merge g255 10 0 80 47 (@block_merge g255 10 0 16 64 slice255k10p0 slice255k10p16) slice255k10p80) slice255k10p127)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k11p0 : block g255 11 0 5 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k11p5 : block g255 11 5 15 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK255k11 : block g255 11 0 20=true := (@block_merge g255 11 0 5 15 slice255k11p0 slice255k11p5)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k12p0 : block g255 12 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK255k12 : block g255 12 0 1=true := slice255k12p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked255 : checkedTables g255 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g255 0 0 0=true)
  · exact (rfl : block g255 1 0 0=true)
  · exact (rfl : block g255 2 0 0=true)
  · exact (rfl : block g255 3 0 0=true)
  · exact (rfl : block g255 4 0 0=true)
  · exact (rfl : block g255 5 0 0=true)
  · exact (rfl : block g255 6 0 0=true)
  · exact layerOK255k7
  · exact layerOK255k8
  · exact layerOK255k9
  · exact layerOK255k10
  · exact layerOK255k11
  · exact layerOK255k12
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low255 : Lower (vars 255) (graphGoal 255) 13 :=
  lower_forest (g:=g255) (i:=0) (hints:=1412431873) (before_sound known251 valid251) geom255 checked255 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps255 : List (Nat × List Nat) := [(255,[])]
def known255 := extendKnown known251 13 maps255
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid255 : Known known255 := extendKnown_ok valid251 low255 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exactLower : ∀ t, PEqualNP.MetaComplexity.HasCircuitSize 8 edge8531 t → 13 ≤ t :=
  conclude8531 (root_index (g:=g255) (before_sound known251 valid251) geom255 checked255 (k:=12) (by decide) (i:=0) (by decide +kernel))

end PEqualNP.Outside.L_meta_8531

theorem PEqualNP.Outside.L_meta_8531 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6) || (x 5 && x 7) || (x 6 && x 7)) t → 13 ≤ t := PEqualNP.Outside.L_meta_8531.exactLower
