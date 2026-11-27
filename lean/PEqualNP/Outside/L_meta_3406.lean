import PEqualNP.Defs

-- The Live/Run/Forest verification framework and subgraph lower bounds
-- (known383 and known895) are adapted from PressF10, pequalnp-proofs PR 4332 (and L_meta_1920),
-- licensed under Apache-2.0.
namespace PEqualNP.Outside.L_meta_3406
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
def flipBit (m j : Nat) : Bool := (m.testBit 9 && j == 4) || (m.testBit 10 && j == 1)
def vertex (m j : Nat) := if m.testBit j then (if flipBit m j then neg (inputs.getD j zero) else inputs.getD j zero) else zero
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
  let base := (if m.testBit 9 && m.testBit 4 then 16 else 0) ||| (if m.testBit 10 && m.testBit 1 then 2 else 0)
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
  let baseRow := (if m.testBit 9 && free.testBit 4 then 16 else 0) ||| (if m.testBit 10 && free.testBit 1 then 2 else 0)
  let xs := supportPairs baseRow s
  let count := (xs.map Prod.fst).toFinset.card
  let drop := colFree free q 0
  let lz0 := if m.testBit 9 && drop.testBit 4 then drop &&& (511 ^^^ 16) else drop
  let lz := if m.testBit 10 && drop.testBit 1 then lz0 &&& (511 ^^^ 2) else lz0
  let lo := (if m.testBit 9 && drop.testBit 4 then 16 else 0) ||| (if m.testBit 10 && drop.testBit 1 then 2 else 0)
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
  let baseRow := (if m.testBit 9 && free.testBit 4 then 16 else 0) ||| (if m.testBit 10 && free.testBit 1 then 2 else 0)
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
  let x := fun j => if m.testBit j then (if flipBit m j then ~~~(v j) else v j) else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then (if flipBit m j.val then ~~~(v j.val) else v j.val) else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · by_cases hf : flipBit m j.val = true
    · simp only [vertex, hh, hf, ite_true, bit_neg, BitVec.getLsbD_not, i.isLt, decide_true, Bool.true_and]
      exact congrArg Bool.not (asRow_bit v i j)
    · simpa [vertex, hh, hf] using asRow_bit v i j
  · simp [vertex, hh, bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then (if flipBit m j then ~~~(v j) else v j) else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
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
def g539 : Forest := ⟨539,3,fun j => g539samples[j]?.getD (0,0),g539columns,g539autos,g539levels,g539index⟩
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
def g535 : Forest := ⟨535,3,fun j => g535samples[j]?.getD (0,0),g535columns,g535autos,g535levels,g535index⟩
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
def g606 : Forest := ⟨606,4,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low606 : Lower (vars 606) (graphGoal 606) 5 :=
  lower_discard (g:=g606) (ci:=(0,16,78,0,4)) (hints:=16982304) (before_sound known535 valid535) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps606 : List (Nat × List Nat) := [(606,[]),(663,[118,133,33,48]),(881,[82,129,48]),(952,[118,130,81])]
def known606 := extendKnown known535 5 maps606
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid606 : Known known606 := extendKnown_ok valid535 low606 (by decide +kernel)
def g693 : Forest := ⟨693,4,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low693 : Lower (vars 693) (graphGoal 693) 5 :=
  lower_discard (g:=g693) (ci:=(0,16,165,0,4)) (hints:=536872708) (before_sound known606 valid606) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps693 : List (Nat × List Nat) := [(693,[]),(700,[82,129,48]),(851,[118,130,81]),(858,[118,133,33,48])]
def known693 := extendKnown known606 5 maps693
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid693 : Known known693 := extendKnown_ok valid606 low693 (by decide +kernel)
def g627 : Forest := ⟨627,4,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low627 : Lower (vars 627) (graphGoal 627) 5 :=
  lower_discard (g:=g627) (ci:=(0,16,99,0,4)) (hints:=16777217) (before_sound known693 valid693) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps627 : List (Nat × List Nat) := [(627,[]),(691,[118,130,81]),(860,[82,129,48])]
def known627 := extendKnown known693 5 maps627
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid627 : Known known627 := extendKnown_ok valid693 low627 (by decide +kernel)
def g573 : Forest := ⟨573,4,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low573 : Lower (vars 573) (graphGoal 573) 5 :=
  lower_discard (g:=g573) (ci:=(4,0,569,0,4)) (hints:=8964) (before_sound known627 valid627) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps573 : List (Nat × List Nat) := [(573,[])]
def known573 := extendKnown known627 5 maps573
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid573 : Known known573 := extendKnown_ok valid627 low573 (by decide +kernel)
def g567 : Forest := ⟨567,4,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
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
def g543 : Forest := ⟨543,6,fun j => g543samples[j]?.getD (0,0),g543columns,g543autos,g543levels,g543index⟩
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
def g631 : Forest := ⟨631,5,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
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
def g755 : Forest := ⟨755,6,fun j => g755samples[j]?.getD (0,0),g755columns,g755autos,g755levels,g755index⟩
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
def g727 : Forest := ⟨727,6,fun j => g727samples[j]?.getD (0,0),g727columns,g727autos,g727levels,g727index⟩
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
def g702 : Forest := ⟨702,6,fun j => g702samples[j]?.getD (0,0),g702columns,g702autos,g702levels,g702index⟩
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
def g695 : Forest := ⟨695,7,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
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
def g701 : Forest := ⟨701,7,fun j => g701samples[j]?.getD (0,0),g701columns,g701autos,g701levels,g701index⟩
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
def g607 : Forest := ⟨607,7,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low607 : Lower (vars 607) (graphGoal 607) 8 :=
  lower_discard (g:=g607) (ci:=(64,0,543,0,7)) (hints:=16785665) (before_sound known701 valid701) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps607 : List (Nat × List Nat) := [(607,[]),(671,[118,133,33,48]),(889,[82,129,48]),(953,[118,130,81])]
def known607 := extendKnown known701 8 maps607
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid607 : Known known607 := extendKnown_ok valid701 low607 (by decide +kernel)
def g575 : Forest := ⟨575,7,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low575 : Lower (vars 575) (graphGoal 575) 8 :=
  lower_discard (g:=g575) (ci:=(32,0,543,0,7)) (hints:=8449) (before_sound known607 valid607) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps575 : List (Nat × List Nat) := [(575,[]),(829,[82,129,48])]
def known575 := extendKnown known607 8 maps575
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid575 : Known known575 := extendKnown_ok valid607 low575 (by decide +kernel)
def g763 : Forest := ⟨763,7,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low763 : Lower (vars 763) (graphGoal 763) 8 :=
  lower_discard (g:=g763) (ci:=(8,0,755,0,7)) (hints:=1358970881) (before_sound known575 valid575) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps763 : List (Nat × List Nat) := [(763,[])]
def known763 := extendKnown known575 8 maps763
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid763 : Known known763 := extendKnown_ok valid575 low763 (by decide +kernel)
def g766 : Forest := ⟨766,7,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low766 : Lower (vars 766) (graphGoal 766) 8 :=
  lower_discard (g:=g766) (ci:=(32,0,734,0,7)) (hints:=561193248) (before_sound known763 valid763) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps766 : List (Nat × List Nat) := [(766,[]),(983,[118,133,33,48]),(1013,[82,129,48]),(1018,[118,130,81])]
def known766 := extendKnown known763 8 maps766
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid766 : Known known766 := extendKnown_ok valid763 low766 (by decide +kernel)
def g639 : Forest := ⟨639,8,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low639 : Lower (vars 639) (graphGoal 639) 9 :=
  lower_discard (g:=g639) (ci:=(32,0,607,0,8)) (hints:=16785665) (before_sound known766 valid766) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps639 : List (Nat × List Nat) := [(639,[]),(893,[82,129,48]),(927,[118,133,33,48])]
def known639 := extendKnown known766 9 maps639
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid639 : Known known639 := extendKnown_ok valid766 low639 (by decide +kernel)
def g735 : Forest := ⟨735,8,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low735 : Lower (vars 735) (graphGoal 735) 9 :=
  lower_discard (g:=g735) (ci:=(128,0,607,0,8)) (hints:=553656577) (before_sound known639 valid639) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps735 : List (Nat × List Nat) := [(735,[]),(1017,[118,130,81])]
def known735 := extendKnown known639 9 maps735
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid735 : Known known735 := extendKnown_ok valid639 low735 (by decide +kernel)
def g759 : Forest := ⟨759,8,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low759 : Lower (vars 759) (graphGoal 759) 9 :=
  lower_discard (g:=g759) (ci:=(0,16,231,0,8)) (hints:=553648385) (before_sound known735 valid735) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps759 : List (Nat × List Nat) := [(759,[]),(990,[118,133,33,48]),(1011,[118,130,81]),(1020,[82,129,48])]
def known759 := extendKnown known735 9 maps759
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid759 : Known known759 := extendKnown_ok valid735 low759 (by decide +kernel)
def g887 : Forest := ⟨887,8,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
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
def g703 : Forest := ⟨703,10,fun j => g703samples[j]?.getD (0,0),g703columns,g703autos,g703levels,g703index⟩
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
def g831 : Forest := ⟨831,10,fun j => g831samples[j]?.getD (0,0),g831columns,g831autos,g831levels,g831index⟩
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
def g767 : Forest := ⟨767,11,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low767 : Lower (vars 767) (graphGoal 767) 12 :=
  lower_discard (g:=g767) (ci:=(64,0,703,0,11)) (hints:=553656577) (before_sound known831 valid831) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps767 : List (Nat × List Nat) := [(767,[]),(991,[118,133,33,48]),(1019,[118,130,81]),(1021,[82,129,48])]
def known767 := extendKnown known831 12 maps767
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid767 : Known known767 := extendKnown_ok valid831 low767 (by decide +kernel)
def g1015 : Forest := ⟨1015,11,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
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
def g895 : Forest := ⟨895,12,fun j => g895samples[j]?.getD (0,0),g895columns,g895autos,g895levels,g895index⟩
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
theorem known_at {entries : List (Nat × Nat)} (h : Known entries) (q L : Nat)
    (heq : boundsBefore entries q = L) : Lower (vars q) (graphGoal q) L :=
  heq ▸ before_sound entries h q

def mapsExt_1 : List (Nat × List Nat) := [(420,[64,81,66,99,116,117,134])]
def knownExt_1 := extendKnown known383 4 mapsExt_1
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validExt_1 : Known knownExt_1 := extendKnown_ok valid383 (known_at valid383 15 4 (by decide +kernel)) (by decide +kernel)
def mapsExt_2 : List (Nat × List Nat) := [(91,[16,66,101]),(157,[48,65,50,67,101,118]),(283,[81,66,67,84,101,118,135])]
def knownExt_2 := extendKnown knownExt_1 5 mapsExt_2
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validExt_2 : Known knownExt_2 := extendKnown_ok validExt_1 (known_at valid383 47 5 (by decide +kernel)) (by decide +kernel)
def mapsExt_3 : List (Nat × List Nat) := [(488,[48,97,114,67,132,101])]
def knownExt_3 := extendKnown knownExt_2 5 mapsExt_3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validExt_3 : Known knownExt_3 := extendKnown_ok validExt_2 (known_at valid383 55 5 (by decide +kernel)) (by decide +kernel)
def mapsExt_4 : List (Nat × List Nat) := [(483,[16,33,98,115,132,101,118])]
def knownExt_4 := extendKnown knownExt_3 8 mapsExt_4
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validExt_4 : Known knownExt_4 := extendKnown_ok validExt_3 (known_at valid383 63 8 (by decide +kernel)) (by decide +kernel)
def mapsExt_5 : List (Nat × List Nat) := [(435,[65,50,115,84,134]),(489,[32,49,114,67,132,133,134,135])]
def knownExt_5 := extendKnown knownExt_4 6 mapsExt_5
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validExt_5 : Known knownExt_5 := extendKnown_ok validExt_4 (known_at valid383 119 6 (by decide +kernel)) (by decide +kernel)
def mapsExt_6 : List (Nat × List Nat) := [(443,[81,114,134,135]),(491,[32,49,114,83,132,134,135])]
def knownExt_6 := extendKnown knownExt_5 9 mapsExt_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validExt_6 : Known knownExt_6 := extendKnown_ok validExt_5 (known_at valid383 127 9 (by decide +kernel)) (by decide +kernel)
def mapsExt_7 : List (Nat × List Nat) := [(123,[65,115,84,118]),(427,[64,49,115,100,101,134]),(485,[16,33,50,99,132,101,118,135])]
def knownExt_7 := extendKnown knownExt_6 7 mapsExt_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validExt_7 : Known knownExt_7 := extendKnown_ok validExt_6 (known_at valid383 187 7 (by decide +kernel)) (by decide +kernel)
def mapsExt_8 : List (Nat × List Nat) := [(477,[48,33,133,118])]
def known383_ext := extendKnown knownExt_7 8 mapsExt_8
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid383_ext : Known known383_ext := extendKnown_ok validExt_7 (known_at valid383 251 8 (by decide +kernel)) (by decide +kernel)
def maps1519_1 : List (Nat × List Nat) := [(1191,[65,50,83,100,101,118]),(1358,[80,65,82,67,100,117,135]),(1379,[65,82,99,116,117,135])]
def known1519_1 := extendKnown known895 7 maps1519_1
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1519_1 : Known known1519_1 := extendKnown_ok valid895 (known_at valid895 543 _ (by decide +kernel)) (by decide +kernel)
def maps1519_2 : List (Nat × List Nat) := [(1199,[48,65,50,83,100,118]),(1486,[96,65,98,67,116,133,118,135])]
def known1519_2 := extendKnown known1519_1 8 maps1519_2
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1519_2 : Known known1519_2 := extendKnown_ok valid1519_1 (known_at valid895 575 _ (by decide +kernel)) (by decide +kernel)
def maps1519_3 : List (Nat × List Nat) := [(1387,[48,65,82,99,116,135]),(1390,[80,65,50,116,101,135]),(1507,[65,82,115,132,133,118])]
def known1519_3 := extendKnown known1519_2 8 maps1519_3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1519_3 : Known known1519_3 := extendKnown_ok valid1519_2 (known_at valid895 607 _ (by decide +kernel)) (by decide +kernel)
def maps1519_4 : List (Nat × List Nat) := [(1510,[16,65,66,99,132,117])]
def known1519_4 := extendKnown known1519_3 8 maps1519_4
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1519_4 : Known known1519_4 := extendKnown_ok valid1519_3 (known_at valid895 701 _ (by decide +kernel)) (by decide +kernel)
def maps1519_5 : List (Nat × List Nat) := [(1455,[48,65,50,83,100,134,135]),(1518,[96,65,98,67,132,117,134])]
def known1519_5 := extendKnown known1519_4 11 maps1519_5
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1519_5 : Known known1519_5 := extendKnown_ok valid1519_4 (known_at valid895 703 _ (by decide +kernel)) (by decide +kernel)
def maps1519_6 : List (Nat × List Nat) := [(1451,[65,50,115,84,134,135])]
def known1519_6 := extendKnown known1519_5 7 maps1519_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1519_6 : Known known1519_6 := extendKnown_ok valid1519_5 (known_at valid895 727 _ (by decide +kernel)) (by decide +kernel)
def maps1519_7 : List (Nat × List Nat) := [(1515,[65,82,115,132,133,118])]
def known1519 := extendKnown known1519_6 9 maps1519_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1519 : Known known1519 := extendKnown_ok valid1519_6 (known_at valid895 735 _ (by decide +kernel)) (by decide +kernel)

def known1519_all := known1519 ++ known383_ext
theorem valid1519_all : Known known1519_all := fun e he => (List.mem_append.mp he).elim (valid1519 e) (valid383_ext e)

abbrev knownPrev_f509 := known383_ext
def keyf509l7 (i : Nat) : Nat := 0x38f0
def keyf509l8 (i : Nat) : Nat := 0x123a0f17c00194bfa1c0000f9d2e4a0000000068fddc288d98005df937eb6f877388000025d1600591d8fc00124a1c000004a
def keyf509l9 (i : Nat) : Nat := 0xf8d423000907000000000347ed1058f88000000a10b1d9a10860000000009dd8c25a37a828c25525e000000000000000e9c000f13f9addca051d50006e83d8a256d60000000a9b08000000fa4000c8914d00079f000d1a000567000511cc9b82e4c4c63063cc602dc56a50002175910006a2cd2928000000be3c091de4c8d488e470f0e95264a0856b1ba04c5f0662980cb761f9e0873e054f727ccabd4b5a54548ad991182935c750341e31214e99da2140bfdfc0c24218b8c499675d184cda64b7699923a772944a263e57f4414389400092462000000000000000030ddd90009e5d85000000000000c51a5c000000000000a15000000900ea6000b682db000b22962197214c4699521685b000000f490000006e74e6000000c50ccd0004594192e2953000000000b4000000000000000000000000a30e0000006d7ae1000000000000b41052000000000000000b64000000f54f9b860000000e0191c9650008d331f011c11090400030001160027020007051a09000400001b05050504000900010205010004012d020301010001000b02010304000d00
def keyf509l10 (i : Nat) : Nat := (if i<1 then 0xc000000000045d22725d1cc160000000b03770e09d00009224383000000081340000000000000000038bc00034a80000001d530001c090001a70000000000000000001d4f740eb4f5da400000000000002f0db0bc00036380007ccce0aa5f993509f8000a1bdd4b00000000001f38000000000000006156c42386c000000161159ddf149d74c3e40dc0000000000a973f5b0003469000000065740009581538e06000000018534c00000f654638000113bc1680000001d0800000000000000144b394d25fc59000147441e716c00000000000000b50803000021020000000f188593e558c8b14f00930001c7f8200000e0180000000000000276269ec0000002c26715dc2a148c0000003e047a0f61d7d1277a0000000000262ca8d35846220000000000000035310000000a87e3800001f7f00000000000000216d692e84c000c8f40000000000764468d4dd0f790000000000010551e8000ec7c000618df3b2458b01585347be60d807551218a00001710000000000097d15e4000153400000000000000d0b0003a7dd9e6a5f0003a5300000000002408000071580c697ca02a235ce080009a0264b0000742d0ac92011a8d2e000000000000000000000cda858d00000000000000000351f000178b00000000000000000075c0000000719400069e800000000000003c3390976940001e76f80c00099d4000d44778db10105600030431dc400031200002c8c98c00010450000f68bd3400000000000000643b403792763d8134162f2ef0500007045296606ef1864c000000000000002a0d000000000001221c9a44fee630000001c9500039707564000f6400000000000000000000000000001d6d6c4df11000124ee038000e863e0100000001cb1f770000b48adc182c6175867000269300000003d14000e17b50a000000000000000002121000378a0000543000156800021610001b21d468a5b0544000000053fd5ad9133a30d7ac945c46f905632d8fce8ba8ee3915848146000063c0002691b4ca887000373900000000000000000047041baa404578d1c000201f7438000801400000000000000000c65277bcd94000000167fe4b00502c0000003000070000200002014000100100800024000000102000000030100701c000000100801028000300100c000000a00c020000000003004100080001403024030080000803000020040000c06014030040400c040100000400000000040200802004000080f000000040000000004000000300c010040000c0700809004040000000401048060040700001000080040000400000010000e00001000010080a008000000000c0000000004020000000c0500402000010080000801004030100000000014030000100003010050040600001004000000200400000000000000801004000000100000 else 0xfa28c780001164b1f1a810659e71689a616a82cc2906000006c2800098ac000000000000000000001d57000000000000009909a6995380006d2c0000001f6e0000000dce8000a8b80004a5e12400000000002540457c000a4d1b1900038200000926f43000000000008171c6c00000005d38312000000065d4000000333d00000007932e8281c7731d46400000000005d4122581b5137661d2980000000888602300000004855402143400000033520000000362c000465df672801958a4f882ee23df6000000009d5800000000005c6c00000000000000000d548000f4ce66a58d800000000000000000e085a902994000b2343990dcbf35000000000000000000c73000343c000000000000006c8ab530000000a66387700000000003d856210b20000000000000000001b3e0000000000170400000007cdf9658db065d4228000c5b920f40695366e100005840e6744f696f2c2db8c049cb08c0900000000000387896a0002e85d0d073c000000028c40000000244812c0000000b73ae4000000000005cbc000d5fc000e604736ac7132bb07800000024470001d182198000000085204a61016e5b01db05c1737dd53340003f8985a4a991968000c9cfe2400000000d84000a9b0f7e6474060f95ef036873092b0e642260ea05f0dd80000000000000341c30fc52f00008960000f7ce618000e13897b69a2d4a99895670003819146e1726041c0ca9840000000000f9640000002f1600000000000000000000058640000001e8e14544356c409991569725c992a7cb4b556350c800044a0b02f4240000000000009c0000000000e8080005504000c2380000000f2dee5c00000034982cffc6bdd680000001125000147e35300002d9244c845c449f215e080001c82551c00078cf577024464d00020750514000cd7d050257074cd8df2455a27051c9bd95bd88c000c1a026e000000000000000000000000346430efc0fb983a22a527e58c43c000fd079760003510464ae3a7d6236fdc90000dd640002e3a763d0100004110000c18400000000000002393c0f40000000250f264000a02c00018e4000fc3dc7d7624b1efd5dc150003a0ef049d040000155a5e2f510000000000089064ea881e620000d0b4000acc22522106b66e998000159b44a0000000000000000014940002548c589684f23282891cb106d95800000000000002b815920150f60b385f1500000000000d451d2b14e4000e41e88321d8c03793ed1efc740006df400078800000000000000000098b540100d988600000000000000000000080e3340e98f6300cc8000dd0d63e291)
def keyf509l11 (i : Nat) : Nat := 0x68b000000000000000000000000000162acb000000000000000036a0a600000250127062c0800232000002377095180000005600000000000f9be15518000000000000048800000243d02e0f2150ff1de00005ae000ea0003d500000000000000000006a27c7a54006e70001d8670000000000000015400000000000003d08003c400356d758e56480036b00000000000000cd5a66840000000072b00000000000000002a90000004531780000000186f103de003b62f4a14ea5b080096c000006a500000000450000003520000000000048600000000000822000000000000000000000151c000000010c0000000000000036500000000000001d04000000000000000000000000000001e23f8000000a4c00000000b3c00000768003d63640000020b000000a1c0000000000000000000000000000015b400000000000000000408000004010000000100000000020101020200020000010002
def f509d6 (i : Nat) : Nat := 0x3b4250d2029d9550930
def f509l6 : Packing := (1,6,6,0,0,0,0,f509d6)
def f509d7 (i : Nat) : Nat := 0x1850400704100000ba99143ca140c2fb0253b28a926185f608a7651524c3f84daa84a1a409865792029d9454930dad24053b2aa126185f660a7655424c329ebb3484baa49874e5765c59218530
def f509l7 : Packing := (8,5,6,0,0,6,0,f509d7)
def f509d8 (i : Nat) : Nat := 0x608200580030800009018042850400fe8021138b08c60d0181168016083a0074008302098560604205c200038b08921000130804808000120223716118c22f001882c172f800c02e3e2f83a1f0ae14463417e002e3a6694a3e769c66c99e589263a8d61c7e5f476dcc6f5ae67d9a605685655453d4a4ed2c49d2244d0e3fcfa3d4f0384be21c6408c00dde481959dd30cdf605959dd30cdf6099454930edb5c95260930cdf609959dd30dcf6959408530dbd5c49650530df55059308530dd75519308530cdf6059454930f5b5c57254930edb60572549309df6909754930d5f5d89754930fd350d7254930edb6a17254930dde4819454930edb6117254930edb6197254930d9f5489650530fda5895248130fda5c95248130fda5095248130fea5d14248130fda6954248130cdf6559850930b5f29d9550930f3d185765c530dcf55194085309bf69a9950530fea5054248130dbb5d99218530d7d5059708530d5f5519708530d9f5519608530df95c59218530dbd50596085309cf69097549309f62a543481308f768e996093095f29d9454930fe25094348130
def f509l8 : Packing := (42,4,6,0,0,10,0,f509d8)
def f509d9 (i : Nat) : Nat := (if i<1 then 0x28414099f4cf027653a49c24dda6e3351998cc6a5f52e3961ca8e519263921c8b24191f58ef471e34f1878b3c51e22b0fe86ac2fa12b07e82640b203cffe7ef3f1df72f997b83d65e84f107783b65d72e9973cb965c72e2270a3819bccdbd6ca3541a84d1066632698f4c3f618affd7e2be35cb2d91664b005792b6d588aad5392949488a3651427b534096e4aba52521c8f745e22b90c282f4031f2cf2074c3889b34d366573099760b4c5742a1141c9aa49122b104879c39c1b08cbc5e82cb15e8abc4d625d127890441e2010f987943421540a304e026612e06c02bc1540a5035010406602e0148003ff2e890261ff97648130ffcb9240987ef505424c2ffd32a1261f7c6454930fbeb92a4987df591524c3efaeca9261f7d7454930bfecb884987fe589204c3ff28490261ff97148130ffab88c2987fb5c9424c2ffb22a1261f7d9550930dfecc284985ff65d424c3efac4a9261bfd4260930dfeb8b04986ff589824c37fae8c1261bfd7260930dff3bb04986ff5d9814c37fae8c0a61bfd6160930dfea0b04987df505524c37fceec0a61f7d6154930fbea12a4987df5c5524c37faecc1261bfd7260530dfea1302987df999524c3efc88a9261ff96148130dfeb930e987fb589214c37fa84c3a617fd9710530efebb2e2985ffa65714c2ffb2c39261ff5415c530ffa90ae2985ff650714c2ffb2e10a61efc9650530bff4ca82986ff505874c37fae2c3a61ff54108530bfeca042986ff585874c2ffb22b92617fd941c930ffca0a40987fe9dd204c3bfae2b9261bfd985c930bff4cae4985ff659724c2ffb2e30a613fd9660530dfb08b04984ff649814c36faa4c0a61f795248130ff4a1240986fe481874c37ec22c3a61bf98148130df71130e9867f9dd874c27fd32c3a61b7d54605309feca302987f650d204c377c88c0a61efa6648130fdd22240987fc845204c37f30c90261f795448130df711302986fd845814c35fcccc0a613fe99605309fec8b0e986fd505814c3fd444902619fe77605309fec930e9877e9dd204c36faa4c3a617fa9948130bdeca0e4985f764c724c2feb22392613fd981c930b7ecb0e4985df654724c2ff320392617ed9218530bfcc80c2984ff660424c27fb3030a615fd9718530bbeca8c29857f65c214c2dfb2c10a6177d9508530b7e4b282984ff660714c27fb3010a617bd94085309fecc082985df654414c2fbb2620a617dd9308530bfcc8042985df656774c3edc44a9261f7611549309feca3049875f9dd524c3cfccca9261f3e4454930dbeaa304986bf999824c377c88c1261bee2260930dbea9304984ffa65824c33fceec1261d7d959dd30ef7114ee9877d9de114c2efb2a212617f99010930fd722444987bd99a114c2efb28a9261f6d7254930bbf4caa4987ed912114c3fcc4508a6177c9754930 else 0x42e05c0184a05c01c0b8022284c40dc5f006446185c7400be2c1440be2c4230be2c6230be2c924c585f8038109850b8105c61281700224248492106e2c863c58400dc5f0078b0509870b03881a1de00c0619103435c01c2c0dc01b184820686c07c0203435c018359020e0540a3c584c4c6128826c815031617188c278b183437c018343fc018942e0a09860ac3c5884687c5a08812810a160ae01248430b085049e005c30506e2f80321841b8b220f160f418c8c0e111820dc592478b0ba1b804c583840dc5883815e001c1c58581780324060444c585c60d6470060dc5f0078b2485c70b0a84c70b81088a1e0041b8b220c1b8be011498b0aa1b80403700300d09838247e0040c03e00602651081a07070b82826711c2c2e130897810b0c0c15c00b8601612370020ae006016132f003c0083c09c00c05c1c0585a04e0681c283050300f801809940202e00602e5e00781021702042e040840ae005c300b09184f0b0c0f801e0078011283f801809c2cc03e00601a0a0983824803f002818099781021700203e00602e0d029b81021042070724c142e6e007178324f002e13c284508b248370a112e2c921708900607248340a11362c921709e1422660113161709e142274585c944909614c26e007832450ae2cfc00c0988a8b281807c0060441a05381887c00c05c8a123e2f801e131142a60ce2c8a490a97818b0b914225e062c2e4508948c44c585c8a1137003d8b24054a0303834144922848e0601f008a18089b1786c1f002e45089c0c03e00302e45091c8c44c5914305c360f800c2285cdc006a2c8a112e1b07c0089143062311317852500340081807c00c05c1a053d003400d002270340c31052f003c00f002230340c2f0709c14e2407f00301707016168e00580100088464305f060c09e14229e0030221220018bc1a1e1449c29a8049c5e14940080046a062c464aabd4dea41509a74d326941489a34d1)
def f509l9 : Packing := (154,3,6,0,0,13,0,f509d9)
def f509d10 (i : Nat) : Nat := 0x1190f00322c5d144e14044568c863980221d16748498b262602445c09123005d162c44c8780182316928b0a8d02a864883c02645183e045930d0c30443b022e04e8c878019168b024c84926138b112a1866022c5c09b00789a2d1454c3d80184c27162274643c0458b28560458d1b022c68b81163234944268b2920301838f0c02e0130c85ac94180c1c78602883004c39142da483c301625804c74603071e180a05c026190b5cd69331d227c1a78ae21b5b2e5d2af143a5242a7a0e59ae3225908389a0ba003ff88930ffd414c3ff1c530ffd614c3ff08530ffe774c3ff10530ffd214c3ff5c530ffe114c3ff1c930ffd724c3ff18530ffc424c3ff50930fee224c37f9dd30ff6114c3df54930bfd824c2ff60530ff9204c2ff61d30
def f509l10 : Packing := (23,2,6,0,0,11,0,f509d10)
def f509d11 (i : Nat) : Nat := 0x200b17fd30
def f509l11 : Packing := (1,1,6,0,0,0,0,f509d11)
def f509samples : Array (Bits × Bits) := #[(0x2003ca2046cc1e3e012c9030515b4611112d8329201018939c3603007318310e1742b001a,0x1b4a2c460400b1812c0420c15f0e50500f032f04041812341e26431508200e95c2b630a),(0,0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc46404cd877200c018bbe2a52a3c605002415364d821d907720a048a044006720c5502725,0x6804188807f2014000d684340e3c41600240428058877a871603000a082012620059a2124),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80204062790de1056fe1030750c89c8ecb02015cd42010044056db6b0c00e69064d444345,0x98604068080007232138005040388c01020155a020002041f4532000006511448214241),(0x6001830016e1fe1c2454915a1201830bb825f00004500011183098202a90900c0382c0012,0xd20859010e20008045081da02008100aa30f48002500009080188906a929840020040010),(0x382498208380027bbd38968847245382118009123da04eec6c1030451860901100839808,0x102010400818220620d1b95a322041a801000010b8d804acc261d10040100b11000801800),(0x181ff0508008007a00200404010b800014c8ac02402462000100201080290000802000080,0x2502450300a440660a11a0a017c18a0b5488117f22c0f400406080200010400531100000),(0x47c4060f701600c1020868c0aa04204428e452300b89894820c8048000c2006308010ac20,0x44347004880103080080c083b004eca618600200814020800480a1c2c008000008400),(0x181831bdeb640100d01a04084da01ba444922c8a0047e6300b056055802d6880e028050c0,0x44000ba407e510f8040e40a500800040409022880003d01028000058926c00a4800000080)]
def f509columns : IndexTree ColumnInfo := (.fork 20 (.fork 10 (.fork 5 (.fork 2 (.leaf [(64,0,445,0,11),(1,0,508,0,9)]) (.leaf [(16,0,493,0,9),(128,0,381,0,9),(0,64,189,256,9)])) (.fork 2 (.leaf [(4,0,505,0,9),(320,0,189,0,8)]) (.leaf [(32,0,477,0,8),(132,0,377,0,8),(256,64,189,0,8)]))) (.fork 5 (.fork 2 (.leaf [(8,0,501,0,8),(17,0,492,0,8)]) (.leaf [(33,0,476,0,7),(0,16,484,9,7),(0,4,369,136,7)])) (.fork 2 (.leaf [(0,128,345,36,7),(72,0,437,0,7)]) (.leaf [(24,0,485,0,7),(0,1,460,48,7),(8,4,369,128,6)])))) (.fork 10 (.fork 5 (.fork 2 (.leaf [(128,4,369,8,6),(128,1,332,48,6)]) (.leaf [(4,128,345,32,6),(8,16,484,1,6),(32,1,460,16,6)])) (.fork 2 (.leaf [(4,16,480,9,6),(288,64,157,0,5)]) (.leaf [(384,64,61,0,5),(36,128,345,0,5),(324,0,185,0,5)]))) (.fork 5 (.fork 2 (.leaf [(160,1,332,16,5),(328,0,181,0,5)]) (.leaf [(136,4,369,0,5),(72,4,305,128,5),(48,1,460,0,5)])) (.fork 3 (.leaf [(72,16,420,1,5),(25,0,484,0,5),(21,0,488,0,5)]) (.leaf [(12,16,480,1,5),(96,1,396,16,5),(273,64,172,0,4)])))))
def f509autos : Array (List Nat) := #[[],[32,83,116],[64,114,83],[112,66]]
def f509levels : Nat → Packing
  | 6 => f509l6
  | 7 => f509l7
  | 8 => f509l8
  | 9 => f509l9
  | 10 => f509l10
  | 11 => f509l11
  | _ => emptyPacking
def f509index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 5 3 6 1 1 (keyf509l7)
  | 8 => lookupWord 10 39 6 9 3 2 (keyf509l8)
  | 9 => lookupWord 53 237 8 12 6 2 (keyf509l9)
  | 10 => lookupWord 189 991 10 14 8 2 (keyf509l10)
  | 11 => lookupWord 26 235 8 11 5 2 (keyf509l11)
  | _ => fun _ => none
def f509 : Forest := ⟨509,11,fun j => f509samples[j]?.getD (0,0),f509columns,f509autos,f509levels,f509index⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geomf509 : graphValid f509 (boundsBefore knownPrev_f509) = true := by
  unfold graphValid
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel, by decide +kernel⟩, ?_⟩, by decide +kernel⟩
  apply listPieces_all (d:=3)
  simp only [listPieces,IndexTree.values,List.length_append,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceDiv,List.take,List.drop]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf509_6_0 : block f509 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem blf509_6 : block f509 6 0 1 = true := sf509_6_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf509_7_0 : block f509 7 0 8=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem blf509_7 : block f509 7 0 8 = true := sf509_7_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf509_8_0 : block f509 8 0 5=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf509_8_5 : block f509 8 5 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf509_8_37 : block f509 8 37 5=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem blf509_8 : block f509 8 0 42 = true := (@block_merge f509 8 0 37 5 (@block_merge f509 8 0 5 32 sf509_8_0 sf509_8_5) sf509_8_37)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf509_9_0 : block f509 9 0 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf509_9_32 : block f509 9 32 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf509_9_64 : block f509 9 64 21=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf509_9_85 : block f509 9 85 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf509_9_117 : block f509 9 117 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf509_9_149 : block f509 9 149 5=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem blf509_9 : block f509 9 0 154 = true := (@block_merge f509 9 0 149 5 (@block_merge f509 9 0 117 32 (@block_merge f509 9 0 85 32 (@block_merge f509 9 0 64 21 (@block_merge f509 9 0 32 32 sf509_9_0 sf509_9_32) sf509_9_64) sf509_9_85) sf509_9_117) sf509_9_149)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf509_10_0 : block f509 10 0 8=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf509_10_8 : block f509 10 8 15=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem blf509_10 : block f509 10 0 23 = true := (@block_merge f509 10 0 8 15 sf509_10_0 sf509_10_8)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf509_11_0 : block f509 11 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem blf509_11 : block f509 11 0 1 = true := sf509_11_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tablesf509 : checkedTables f509 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block f509 0 0 0 = true)
  · exact (rfl : block f509 1 0 0 = true)
  · exact (rfl : block f509 2 0 0 = true)
  · exact (rfl : block f509 3 0 0 = true)
  · exact (rfl : block f509 4 0 0 = true)
  · exact (rfl : block f509 5 0 0 = true)
  · exact blf509_6
  · exact blf509_7
  · exact blf509_8
  · exact blf509_9
  · exact blf509_10
  · exact blf509_11

abbrev knownPrev_f507 := known383_ext
def keyf507l7 (i : Nat) : Nat := 0x11d297bb95200a20000000000004c640000000000006a7054002000300400
def keyf507l8 (i : Nat) : Nat := 0x1b80000000003000000000000007e300000058752bc98400030344f6c8003aa00000000000000000006859c0002873330013e0000000cc00326bd1001e340000095ddb000000f4600000000001eb400000000000000000000000000000000000000513e52dc000c584469400021fd1c000000016641c800000000000009a08d9f5faf0013a80000063000000667000001bb257184003a43169530c7ec15969c2028580000000000000e117b634355001bc80000090ffbc00000da800000000000000b98c0000ad400443296000004a0001a2a260b75ca00000000000003958020001a400145000001ba8000011242529778c7c0000006a608a823a4000bdc00456000000314f10000000000000000400141c2a0033c800000003d280014c000090000018180000018833ec9800000000000000000000000002040000060c00000000050000010000010201000001000000040000000000020101
def keyf507l9 (i : Nat) : Nat := (if i<1 then 0x71d48000345c0000000000000210f0000000000000000000000000a7900000004c6c000000000000000001105e2571080000001f4000039217e7c538ad5986cb194b92a0b000090ad85f127c000f23b28911ce4890003077261c0003e8000050a7b9065a4000a212887000215400000000000a7e62831862dbc000625c00011f400058000000000f75000078c91b8c5daa779366c3ae33346367a31e5691364f812121a8331c3c04428b1f3580e80000000000011c000a0f156e64187360655a7400039908082e29fc54000d16c000000000000000000000000019825789cc0000001e14000361a6d4dd50b5c2e8630ec9880000000914ff29b96098ea810b3fe5a800000027699010000a20de3cee1f9965d4316b222027d309618d6cd3361820b42e9d9b42ddc98000000088d00000000002d7f9c5304e000117cf0d91370cae19a00000000003e0f000386dec10000000280a7c19419359629b80359397431813fc16d0929b0000766068a05cc000f9dce7f44fc00000000004e79d3a0002a8178e0910d5b0000a8a800074880000000000ed30000000363a89a3a39c4eea37dc62c350003984858573e0000000cd73520b1fb17a40d0000145ad0b6d0c0000000185000175e0d6f5726da8000dd55d33383a891394c33b8530000640b90ab5f4f2588cbe3fc56e3572a3426dad081a03d94d64dc28672f17bd663e12b9908228750002b3d0002f190000000de28000000314bfc4a29400000000001e52ea0800000000004671d0d00000000003b9c7561823b007e76ace4000000000014f00006e50b4be98caa07411643607d58018c314a00036900000000116b72195d80003414000b0e5f0800000000000000f65e40cf492c310a3dc2700000009cbc24c00000000270000d8b500f1c0db0c28fa5787087292791915c1a7c000885800021a90060000000000164825040005dfa71d0002a3b85080008204000284976ba8d77410000000e971788000301d0000000ccea97ef1600003269b2d119f65579088153d52c38f46f748886724e6a3821ce58c407758903e560af95a0081604c070080000c0300009004070040000400048080000100c0301006014000081800402008040041c004000000700805020010041d0000203c020001a018010041e0041201c010180000c0405c06000000000d00001020060000a00c0100000000000040300c020040100c0200800044020000100805000040000a010000080300406004070080404002004010080300003004060000600018034000000d0000100004004040280000809000030000001c000040200c0e018060000102c01010100000000003010020040001800000090280000001004030000200c010040300000008020000001008000000000e0140000000004010000000402000020000000c01 else 0x61eec9d6053a5de49ed29692f90edde2a93fa1e9590002b73d57a39891c83898e2c000f89e1750002337826f700de141470000000425658ba450749a5599920003b0b0510000b8aca36000000000000000000d99110d06099a400000000000000000f068000000169500016851c400000000d5539bc000982c0000000000000255300000000000000000000000000000000000000000000026990000983b4b078eb4b6b9b8c8b87fdc06641000000051dbf6c0000b2c4a6980e0000000000152a24bef7a84c00000001713f950000000000014b8000605c000000000000000000001519c495b6098f72110003a409ccea34de02160f9e17090c9fc4faccaa9828a1379051ae1f3136108956be1e512b603a85d8630001a59ec440000000000000000000000000001d4eca5cf510000000140d48f00000008d8df930000000253c00000009579189c54766d51d1925032422cd77a89152b000000000000008828f705a2c000562a19fb148000c1840006dff545d1000000002f4eda10000384c0002cc0000b62400000000000000e0d000000000012025a7a949e060870000000000000000000000000227c787578d6c933200000000a448000c0bc0006cba61b427827500035790002316fa03c6f00000005650000000131e1a200000003a51d25800028240003e0d29c22339238021a21059c307d881b640003a1500014930003898d93c0000000000000204bf079f3c31e9c469d1fa6a0002a6b0002894cd3f400141c474000030234440000001796000000000015510000000000000059c112864540000001899a44c000e4d7c92a025a66215c43d3c8fc05107228cd97c91f34d0c3f0000d32000101144797771dbb02800000000002c551d1000044f95400000a7100000000000000000077da8c48684e5d374b1f34850000000f13000000023860000b68a994471f19109048998306984b0dc059b727d28201050c59e89eec1b099188a3c7e72a7ce2346d1272185a0f80b4499b28f1147590000152c5bd13d1e0811a691000010a9256297b62e69b9376a83365b00000000002606c203a104814a96a52024d581c4370000056e40437c1d89c592d9ca22e093b584145623c98197401e1500b94039a65a1345100d0262929422d9178100003e62000000000010486c5e06bb8bc000b17286901400000000000e91dd8c0c68000000326)
def keyf507l10 (i : Nat) : Nat := (if i<1 then 0x1551000000005665393c000000000011c3000032d40000d2d5eb9d0336a160002511de6bd2e1cd8000038250862f11e3650000000000000003e1881740001f9508c7a1ac00002a1c88f2ee16430f76b4c4daad41682a67a7f18f99433b5007152cfc00023a81cf10000000240f0000290200032bc3c9e8c800000000101941d98c19266cf74e695c44d8b75c15c45e3326e9d80004e91d0900000000000000000000311545039ab6402c7dc251d1911103570f2336db72bbd5030001535322000009a22d1e986a111e0000000000000000000b4c4000000068b34301e1700be84b05584c84a209acc9813c000412600004a464b390c6763498b712ecaf755e800000b4160bb127c190000315d0de9f8577afbf40a614f2d0000000000a01d00101000000000100300200300101300100000100100001000700400b00100200000600700100100400000001e00b00f01200200400000000e00700400200b00b00200200100d00100801100601300000200300100000100800000300100201500100300000000500a00000f00000700b00400700700400c00002100100000000c00000100000200500100200e00000600000000000000300600300201101300000100900700200000400400300200100101200000100000400100000200001a00100601700200001100100200200000400a00201300a00000b00100100400600000200a00300900200000800100100000000000000800200c00000000300100200200100500c00f00700000000300001100000700500200000101000000600000100000100000800000800100102300200000000200a01100300e00000200000700000700300000700400300400400100000400600100200700700a00100000600700100000000200100000000000900600800000000400a00301200400200400500500400500200000000300800200000000200300600000000000200400500000900900100700301500800000000400200200700100100000400400500300400300000000000000000100000000000200000300000900b00b00100100100100000000000000000400000000100200100100200f00200000300300000100000000000000100100000200100000100500100000100a00000000100400600000000600100800300600000100000f00600000000000400000000000100000f00100000f00000a00100f00000400000900601400000000500000000200400000400000000300300000e00100000400000100100100200000100000100300200401200000000500000100100500000600200500c00100000000100100e00000200000000a00100000000200300400100000701800300100100000000000f00000000200101700400000500000100000000700200a001000004000007002000 else (if i<2 then 0xa000000000000000000220c8000a2a40003d302022b62692400000c6c0000914632518f60001fb5800032c16d96840c00064fa0001c8a40000000b55600000000000ac7fe24000042e0c9e80003d90800000000002c31b62c1ca14daa655000000007cd800044883ebcb0e000000006c11f8a4000000000019a480000000f2740d1e69626c60000000000000000001855519f74391d512ad5615800070c40002920a0351a50000000000000000000269c8000194c00000003554d20ecd8c0002eab4d282ab6a02cab0dd486573d82593661a23a0df690000d037ed2c527000061d5025c000544b0000fa46a10800000000000000157400000000c3e783bb1964cfc0000000000000000004620e1120001643ea0e2c730408c4d8000753b81cb4411b5b0001e10e19ab430e62400000002286de00d8a80005abd71f96d517b88000be840003880a6ebe1d74238000000000000003b0280000001551c0001a26b2219083a97a4a07c8ed0fe6297c773dbf35b6183d549c01600005318000b528b1aec3b30e100000003605f05b89d248b400054a76dc00002448c9640001dd700000000686c5020000000000008a88000521300018bf4000000065ab2bd91715c4100000003bbc00000d3a6bef0b90000000000000005b4171d0b54c000000059b0bc0fca8094f1ab60003287a200d8f6a018a5ed65600000000d3997142dafa90936ee509bc00e82eebc800058eb6814a7666262a0a0003833290bfde7e45248b692100008845a7c883cbe4200107aa167d5524d975d1cf10fedf912c49a88000000103340000caf82b634cfe12ac226a29e5300000000258e08f800069627a30549ce5748b029af9250440bf4f712845cd1859d02f48b5b080005a5b61f7f4780001ec381f253bf58b54785666a4b635ac27400001ac11a2a91800000000000614ba16200000000000000085500000000e23a00000000000e69975ba9a4def50000a2e62560000000000001409f6caea7d9940004eb6e511e8d4ba500000001a33c0007247889ef99c000001c1244000317683750000d2914a22a14000091c400000009d385c3b40b72180000000000048585d8b99780000000000000000002a77604800031843f2e057c000000036760e020002536e93585e12de00004ac9494aecc0c76f0a40000231056eff380adf510d2150000000039d1a7ee74b000144540000000093e00000007f2d1d76000000006c70e7d255b0619e0ab1c143f4404a501400a000263c80002a2c000000000007e3bf3574166b5f94b8e998430955da0c15b9b44d0000c567c4e456000000001d840000000000007b400005455d4cb2aa34190039796529e1c7496e729bfe594fb9c03758768abba7378afcc6279073595d1d00001dc800070e500000001d1880000000000175c80000001bd1800 else (if i<3 then 0x462864600000000000000009226722976099172ce80001f56f5b82cda3408000e1b4b010000221e6e9809a2a54274d695a139c95252eca5f5f564166451b24421171c5a2d5c6aa303bc000000038bb43fe32fc801a436080f6229aea82b4292383acd3e61b8e3080000f1e000000000000000a0d200000001e80f9fcabcc0000000fc3fbc4fc3800000cb6b94c79843379c1adae0000689cc997bdb984468b5000151c229750440000a19c0005856e506cd55859e44d45deb484000561926b18c0e0998000459693480001cdeb6036ba473beee238240003a94800085ea0001ca15a5e35c2d4f2c62c2ffe6ac00006898d4f05a2e36c0007c0e481585d4000626100004a5ec6c00000000000000074605d0c00000000000cdfeed200000000b2d321f400038b66486cd93e080000167800000000000000000000006a9b00000000000000000000002506000000000000000000078d105ac0001c98fa564840000745b0000c34e30d0e0c0a218ddf9b764be000000020a68000240c00011742b460000000000000000001acf400051305e880000000000000000003d650000e92c4b9ea54e41ac629c8f298f764b12221945f71ea04e60af26c0000000000000000000a758a54000000000000000317f60180000001bcc800000000001eaa40000ec40000000276d0000490c00000000000f9b20000000000090f3edcc00000007cc6d54ae71ec2fcd920000000000000000000000000000000003996805368e62280ba4907800007d692607f3d5cde3b780000000b688032ad8ec176b908e9e7c01ae69419c903c139000049836357a70327d000104c812b00000000000023ffc8d22ae000000000005ed71db561320a6b1cc0003011ea1c0ce5438ca47bc99ae4f31bd8343d37165e6ce05528000000070d40003ac4d1329c0955d8000000000010a000003569a0680002f410070d92769a0000540200005b5fa76cae3d871616e8b800000002e0a4d4825866a98000576ae096cc3fc16e8490000000017ca467000073b644260cc000113ce2af4028ded3a59bd1c163b954181fa7ac3f0fa56ffd9519c8d22b1a0ec3916fc012c11628200001d4ac5bc00031807174d44f909cf8e69252838000000000000a004ac40001c769d3061ac000560e7432718c77c8000fe220000f58a02b9080000351f80003acc000000022ebcca4a8df1b36ab9da71e473f74df79f976000000076ae0000412ad72cd197a3fedb00003632098d384bca7573c00000001a9300aa79e4584e62bee9f462bfb01696f2164cc1dbcb8ac2c93fc84ecee47822823ace13729b87c58323e73ac32bba332c12d2f2c901ccaf0ee0262f97ee6c861853899a0001fd83e417d30a26cfad1b788e14c470774b4710bda1372368279a940000b31ea85093c0000000b2d46d3d9311a2e09 else (if i<4 then 0xc61c4b25264abfba4809243a3dacfcdd1ad34000000000000000000128d2918000162b76030e1a48ee27e4831748c79e5807e95edd209a58f3abd639df40000000143dbc7000000000800000000000000000000000000000000455e000000004e8465c00000000000000000027569d46000000000000710d03a9418000000000002151f530000000000015617e61da0e00000000000bdfa00000007c5300000000000000000014c9641a6324e8cd19b4ab636370e493554105045e5d184893886a05d0001d81d27ff8f148465bd9c3500007986000000000006875728400071370000000244fe00cfa1d1cd799a0000b46c00000002cb8cd46f0ca8b66971558ac080000646e9eee0000e6880006800b25c000000000005008000508a69c9399800002b2a86e000230d8ab67eaee4a7591bf330001757c75b8000000070240004aa300000002c7bc65acdb93bdc000000000000000251264c25b57cde2148000daa000000000000dd7fc9a4d50bd23e1240099f31108ccd67623579052d0c83709ab042866ec6b52bfb384217781b215afc833ea700000003eb1709dd9ef0b58e9a8000f07a0002282645a593a0003f66800044a400000000000000151387a74a9a3d4305bee0f58590000add8000482a2e12d36a690000002931121236850800002dc93554a67cc8605e4516513be248dc1bd9160d7000021c61730000e12a5dbd0693cb7000194940003ae3000000000002d4e0ab495d40000000000051a707c0000000018af2676855b5b652cd2a280004263486986e8000228beb6000070df605d18d00004900a03154340007a0dadf69ce40000000000000028548000302f128c0000046dc9a0000e4100000001b1cbc79717800018d5e53d286d8e4420a530e885700014d9472316010d6948adeb06148543fc132c55f06c1255fc480000000e090000000000006eba000038fa4955dab1b6c000000000000000000393edce20000ca380008ddc21d147f000064819469b70b2aa612c00000003558588873b8000631f70bdad640000000025e0002d4800003a24000000028f3f53e947000000000001aae8000634e00000002c0108c80000000000054502e52b95400000000001785c00000000000aa67b4a800006396946a709752ea153d4432a6a7c7074931eb7248f486400001f4d80000000da1059380000000000292f800000000000b4400000000b9c35096eaf00002a1309a1b531e77f05f75e80002e5000000000000655998e9d643883e9ec2a9cb4ccef87aae0003d5e0000693909af0a576f0f6860001312000005c9dbc5b399a70000000000005f31000031940002b5c8c05b8b80590000b1ea00028b6c48ed9f00003f66000089563811417f682601ba1ee43780000000601d5b7907a00019c2c0006105c80e0003c085449bc4e8ca80 else 0x13504614171af147811fd1956e5dc89450ceb44c0108a9638b93dfa8c82c712d8000289e16a03c17186ecf5000139e80004ea900000000584e725c47bf1d00000000114e50601b10000000000030565759000133400528000000084ffa72ca0f188c0a1c00059170001d9fdc8dc8a2498a00000000000000000000006c7e62c00000000011212c2000000007430000203aa9800000d74000000000000001fc2803280000000000000000000000513000000008652b87849c4e68143a00005790000000178bdf6c0648000082f4d2ba4c2a1f4000203998bb000178cc0003a15ecf6085cd2510bc4e4d2be0241873ad9ba9ba800073684d9c00018296a3410a3a912631000000000003009f10eb1c80000000126ece68000000000003e09c9500002af10001133d7270b5d000169b2a06000000010a58000000000000000ea5fc3389d44ca3c211540c04e000161a000000000001a5d53264db2b0b24187c8a9eaa000000074d3d010000354e4e58183be41036a00504283228600a000060220000000000000000002a250000817e00000001ed100004c09410884e00019970000483fcc4b892c0002cdb0001081cb3c66bc0000ba5c81f3532659df45665c800000002da4000274500000001e9b288661ce21151af0c6106e90429915487f282c75a8351000000000000928154d00007d9316b800095dc42000000000000115c8b76140d3c78fb040000295125c43b80007f6800006b1800010ad0000000105400000000000165800000000b5a400002d9b15d3d9afbafc6a19220003f03763e7ac82a00020c53d95700002493c2d274a75359443bc3cb9e0f45ea5fff62000158474057108002a0001db8885c040598580005e7c000184af6b2d91ad5a6c9bce03214634aa5ab167df6feed0e0134a1f08de806c00028affa7ed2a361b8000000022a600000000000349a0000000775b0000d2480002271f59b9dd8000623a9183d045d8856d316a400032663f3f000043257078000027b2de4310c13c4dde0002891a71655f9c897f5f0000000178d40006959000054e8000726400000003b1e8000000098d80001f63000174fc2bb20b7c))))
def keyf507l11 (i : Nat) : Nat := 0x1c4d5962a4363281c9e2c000000a76e7d2d0000000000003b7eb38000000ea400133c0016c4000c5ef8b000000003a1800000000197c00344f55588400000000000046bd6a64d840e680000007d66cc003200000002db8000000000000003358000003cbc00000000000212c000002d4b5c000000000000248c001241f1f49ea24e44c6400120d0c8000003598001bd3195b44001d8881c000000d04000000000001054000000000000000000001b735300000002a9cce26c4b0000000000000000000000003f680039ae54c0026c8000002b08000000d8dd500000000000000029281a71471ce8a4000000f2687f9d7cbb3c8870000000824000eb3c3f7b4108003038000002b9f4c513ad81e9db543c6123a92c8800293fa646c0000001dd3abc0007bc4793784980000019a078fc6c052166c618a800000000000000000000000136c000000003f10000000000000432e8c003b90000000002a7317800000156c0000008ac002b42d0ea62611ca1c93d63819fa0000003828000000000000044059a3e412c9663ae58c0a30e749937020609127bcf32eb6761d2ac003474001574606e98016d42a5191dfad68379638018784bb9800000202e51a774000000000d5fc80000002e32500000000000001fb8000f631712bbcb40031bc000003b30000d100014d400300400000374c6556940000000000000c2223aa2a36a78db53b1f06f200032d59913a77c3736e1631a6b47023500000024d299c000002c0c1b064a2881003000001e0d0100006000080c16020000c04000000008000000008040380410010000000000180000020b0040212018480400008040202000040000000040001000041005008040001010040000
def f507d6 (i : Nat) : Nat := 0x3c104162831a66c5a050c945d930e2998768143251764c31a650db02a5425d930
def f507l6 : Packing := (3,6,6,0,0,5,0,f507d6)
def f507d7 (i : Nat) : Nat := 0x7081702188ce084e102000222062204c584007041e040b8491020d041d040b8407081408e0858102070410046f042b255273299247e350a7d3a9cae0682d54aa0481d4e060228d460200d80334e98948cbac09866b9202919758130e53b0ea1928bb2618af614a465d604c315ec1148cbac09862bd812919758130dd8aecd10a298a61b356d9a7145314c36aaaa34e28a6298569db150c945d930dda2ecd00a298a61bd4551a0145314c315ec3948cbac09864bda45d89754930e9aa62bb32e28a6192f551a7251604c3c6a98ae2c3aec98669d432a5425d9308df36054a84bb2619b64c5a0251764c35aac394ab8a62986e5576295714c530cd7282d0128bb2618be61da0251764c317cc0b404a2ec986699a050c945d930
def f507l7 : Packing := (26,5,6,0,0,9,0,f507d7)
def f507d8 (i : Nat) : Nat := (if i<1 then 0x9758130cfd61d911d130df64c5901d130fba5092058130fba5492058130ebe61d4058130daf55094581309bf69c9458130fa75097650d30fb6481764c530bbe6894058130ebe6154058130ebe6054058130ebe6094058130cfe605901d130df550d911d530cfd611911d530cdf61d951d130cbf5d9981d530df650d901d530cfe611901d530dbd5d9911d530cfd61d911d530dd74c5951d130df34c5921d130cfb605921d130cfe61d901d130dbd5d89161530cbf605961d130cbf61d961d130cfb61d921d130db74c5961d130e3f609745d930f2f551745d930e3f605745d930f2f509745d930abfaa9875d930cbf641875d930e3f615745d930e3f6a1745d930f374c5745d930cbf5d99814530db74c4945d930cbf5d99761130cbf6457661130cbf61c945d930f3e481745d930daf504945d930cbf604945d930eb74c5875d930fd5550514c530fb55d8514c530fb55d9714c530ef561d714c530fb64817650d30db76457650d30bf569c514c530fb55d9214c530ff4481714c530ebb289875d930eb750d875d930e3f5c5875d930abf685875d930bb769d604c530fb55d9104c530e3f5d1875d930fb6501604c530fe35c94250d30fe65c14050d30ff25094348130ff254943481309fe68097509309df6949750930baf291965c130fda5415248130db75d9931c5308ff6929961d30cdf61c955c530cbf5d9981c530ff25493148130cbfa657660530cbf5d9985cd30ff25093148130abf6a0955d9308ff2a64461d30cef611941d5309bf2a5545d930abf6a0915d9309bf2a5415d9309bf2a5425d930bb768c915d9309ef6909754930d3f5d89754930d3f5d997145309fe680975493097f29d9255130de750d941d5309fe68097551309fb6889755130d9f5d8955c530dbe5d99014530db75d99314530dde5519014530db75d9931d530dbb5d99214530d5f5519714530dbe4819691130db74c59691130cbf5d99844130d3f6999714530daf5d99414530cfb611921d530dbb5d9921d530df350d921d530dbe5d9901d530cfe61d901d530cfb61d921d530cef61d941d530cef6a1941d530daf5d9941d530cbf61d961d530de768d941d530cbf61d9691130dd750c955c530cbf6159691130cdf610955c530ddd5509154130dbd5d89154130cbf6099691130cbf6059691130fa650d405813093f69c94581309be680945d930db55d9910c130cf561d910c130d759dd910c130de5911910c130dd5955910c130da75d9940c130ce761d940c1309e7aa9940c130dc7955940c130d679dd940c130fe25094348130bd5295714c5308fd2a61161530bf2688904c530bf26889050d309af29197581308f768e99609308fd68699615308fb2a58788930da750c945d9308fb68a9961d30ff0481214c530bf4680514c530bf1688514c530b7569c514c530 else 0x1840b02103041610340876198e810cc4036800eb04400478608a36082e1202170b4020433180da0308301b40100da00a460b0c1f002c1040c30643f00406082c20584081820800c104530b081d0020d002c105c208834107406105a03042d01841488161340138101080e0e81233043d01810b86c60740918442504291032206040808c109010e82e1a1611101c30c61705010d44001a82110941088320858204003681410ec0c10181a181124300f80280420087020b858607010d052207c00b04820810086820404180420014321f80200014105c231038105c2c082e1488100434104222182008418206010c8610fc3218412207e26042c204122041e0040c306010b04114c2c107c008182084a160820c05840f808208000034012433e08182e19c188dc207650b03c0ab82e10a0608200000c104000403e005c312204f038230c180d4e078400c328ae0f82e10463045e003a307bc006060884460f03a1845e003a30bbc0102e61f801a1052070c3f002105cc61f800b8684bd6bc7bb8bb3ba4b95b72b59b2cb27b04aebad2aafa8ca73a5aa4ba3ca2da1ea19a0a9f19ec9dd9ce9bf9ba9ab9a69a199298397496596095193892991a9018e88cf8c08a788e87f85c83982a8117f87e97da7cb7b278f78075d74e7357307176fe6e56d66d16ae68b67c66d65464563661d60e5f55e65d75be5b95a059b58c57d57856955054b5465415285195004e74d84c94b04a149248d47e46f46045144243d4244154064013f23ed3de3d93ca3bb3ac39d38e37f37a36b35c34d33e32f31631130c3073022cb29425d25824924423f23a23522622121c2171f41a919a19519014f12c1090fa0d70b409b06e02d000cbf6099758130cbf6159758130dbe4819758130cbf605)
def f507l8 : Packing := (161,4,6,0,0,12,0,f507d8)
def f507d9 (i : Nat) : Nat := (if i<1 then 0xf4cb04985f7a65434c35faecc2a61f9e4450d30fed00286987f5845434c3ebcaaa1a61bbe44a2130df711510987f3889434c3f3a80a1a617dd9150d30fcea1286987b75d8304c37f400c1261bdd870c130fcf22060986bf581854c3ebcaa182617dd940c130eef3b860986fd845824c377c88c1261bdd43a21309feca30a9867f9dd824c36fcaac1261bdd3161530fec48286987b7581434c36faa4c2a61bf49161530ff4a1240987be5d9204c36fcaac2a61fe952481309fec8b049867f9dd854c37dc44c0a61bf61160530dfcc3a40986fe801814c27fb2ac12613fd9460930dfd0030a984ff65d824c35faecc1261fd94348130ddf2230a986f78cd854c37ec22c2a61bee2261530ddf22302986f74c6884c37f241442613fe99615309ff4cb02986bf581814c33fcef44261b7e55a21309fecbb02984ff651814c35faecc0a61fe92148130bfd4ca40987f64c5204c33fceec0a61afd6060930ff908a40986bf5da884c3f748890261dfa7748130fbd2aa409875f956774c33f9313ba61b7d87955309feca10e9877b9de224c37db0f112613fd9121d30dbe4c4aa984ff661734c27fb30a1a617dd93151309fecc2a69867f9dd874c27fd32c3a61bec9261d30fb72ac44987fa88a004c3ef4ab00261dfa7780130ff908c00986ef21e444c377b0f22261bbc9891130dfcc3c00986fd21e114c37eb0f08a61bf49884530fea49c22987f988a114c3eecab08a61df67784530beec98e2985bf658714c27fb3038a6177c955c530bfa48aa0985bf65a444c27fb30882617dd9310530bdeca0a2985bf658514c2bfb2e28a617dd93145309fecc082985fe640514c2fdb2428a613fd981d130beec98ea985ef650754c2dfb2c3aa617ed921d5309fecc0a8985fe640754c2feb223aa613fd981d530beec98e8985df654744c2dfb2c3a2617ed921d130bfa48b0a985fe640744c2feb223a261ebd9691130f3f2aac09873f9dd604c2dfd32b0261ebe4458130deec3a62987bd845604c3ddc44b0261ef92058130b7ecbac0986fe801844c37ec22c2261afd8758130f7ca02c0986bf611604c2df928b0261edd764c530fe711262987e7911314c3ebcaa98a61fd6114c530f6ebb286986f761d434c3fb40098a61dde774c530fea90a62987f5145314c3faae298a61fd8904c530bef4ca62987f5441314c3dbac098a61fd6118cd30fcf22466987d7956334c35fb0ebb2616fe995d930e7eba2ec985bf251764c3bbcef19a61f3e5591130edf3bc88987e724e444c3f5c4522261bdd878cd30fdd00488987ed846444c39fceebb2619fe77611309ff4cb08984ff660514c36fcaac2261bee2261130def19b08986ef911844c35faecc2261e7e555d930f6f19aec987af911764c3ddc44bb261efa005d9309fecbb08987bd845764c2f3b28182617d5910c130 else (if i<2 then 0xa1c306fe1bc06b51a9c699199c62c1878610175459a157c52413ec4e413344b612a0491117c44810c43ff0f5839b0e583880d583240c7c31a0c542d10b0c2880958251093024708e42340874218084c20507dc1aa05bc161054c14504dc0ea03700ce03000b2029007201900320003dfaa2bb261efc715d930f7eb8aec987bf4c5764c3dfa82bb261efc515d930f7ea92ec987bf609764c3dfaa6bb261efd815d930f7e48aec987bf509764c3dfa42bb261efe115d930f7f2aaec987fe5d1204c37f8eac2261bfd7561130dff22302987bf481764c3dfaa0bb261efd705d930f7f3baec987fe551204c3dfa20bb261bfd52a2130dfea1510986ff9de884c37faa944261fdd7550d30dfeb9510986ff911874c37fcaac3a61bfe7761d30dfeba30a986ff509854c37fae0c2a61bfd74a2130f7e3aaec987bf615764c3df92abb261efd735d930f7eaa2ec987bf5d1764c3ff28290261ffa4448130dfebad10987bf61d764c3ff2e290261ff95148130feea9262987f75c9314c3fbaa898a61fdd7050d30feea8286987f7509314c3fbceea1a61fde5550d30f7f3bac0987f71d1314c3fbae898a61fdd754c530feeb8262987f75c9434c3fbaa4a1a61fdd4250d30fee3aa86987f75d1434c3fbaa8a1a61fdd5150d30feea0262987f7505434c3fbc8898a61fde774c530feeb8a86986ff5c1844c37fa82c2261bfe7760530dfea0302986ff9dd844c37faa0c2261bfd7261130dfeaa308986ff5d1844c37fae2c2261bfd4261130dfea9308986ff955844c3dfaa8b0261efd7458130f7ebaac0987bf509604c3dfaa4b0261efd7258130dfea9302986ff509814c37fae0c0a61bfd7460530dfe3a302986ff5c9814c37fa80c2a617fe995d130efeb82e8985ff641744c37fa82c12617fd951d130dfeb8304987ef509744c2ffb24a0261ff95048130ffcb8240986ff661744c3ff240a0261ff97050130fbea82a8985ff641544c3ef8a2aa2617fd941d530dfeba304985ffa65544c2ffb24aa261bfd7160930bfec90e8986ff545824c3f7ae8aa2617fc9755130dfeaa304987fb509204c37fc88c12617fe9954930bfe4baa4985ff656774c37f9313ba617fd941c530bff4ca84985ff650514c2ffb2e28a61bfd5161130bfe4ba84985ff65c414c2ff92ea0a61bfd5060930fbea92a0985ffa65704c3fdaa4902617fd9548130ffcb82a0987bf659704c2ffb213ba617fd929dd30bfeca4ee986ff501824c2ff92f222617fc9795530bfec90ea986ff505874c37f8a8c3a61bfd5461d30dfea930e986ff5c1874c37fae4c3a61bfc7461d30dfebab0e986ff5c5874c37f928c3a61bfd5161d30dfe4ab0e986ff5d1874c37fc88c2a61bfd4261d30bfecb8a8986ff541874c37f8eac3a61bfd4061d30bfec90a8986fd846884c3bbceea1a613fd97615309f else (if i<3 then 0x45c0410b80851701042e02145c0410b801e00400012b0786e005c3e60e1230649c11108a2e41280606e005c3e6e00c46a482123810c1a105a20c191b0584229c14030781b8087010310490f884854e010c2e3431508649228d0bc01f85c684429508786e005c3e60b02890030880888494700683f08110a522a61b801c080842e82500c08490f949443c3703081d0f9f803e170c5a49c11208a2e3700423e18581411011209261f61b80210d60890721f00622e21288606e00103a1f392b07842487ca151e60b084917185a1ec191b0584228b903c0f60f0821249b810c0f8c78490f60c8c211160b0891887b0618c11245c76006801a006801a00409c0410703e1d35003400a047784198c4b0c4560f0584249b801e005060611a0908333500920cc1610626a02290684248ccd0cc191b09401d9a190413e089c0820b8104170208222040c3d101b80820e87cbc0820b8104107f803703860ac3e005c684860106fc0c1060c0e0040204e00dc665118602e3306140005003c8303209082e3d003401ee0f0584249a802c1e1187450001c008380821001400f002051e85619c00883c3a80510c0dc00b87cdc00f003c00f0020e1e87a062281410928a006801a006801a00407c0010103a5a00419c00385c1650b83380070596f4dbcfef28bc6af0cbbd6eccbb1eeb0baaee9db9f6e66b91ae2fb81adddb6f6da6b63ed78b586d41b486d13b3cecd3b2cec93b216c6eb13ac2eb03abe5aeceb93adceb65ad82b52aceeb24ac12ad2aacaa9baa36a64a936a1ba7ee9dba6ee9a4a5ee95ba53692da4368f6a3368ada25a876a13682da05a7ff9fc67d19ec679a9dc67639cea71a9bea6da9aea69a99ea65a98c660897a25bf967e57f955a53f945a4f6937e4b69236476915a436907e3f68f5a3c88ea23888da235a8cea31a8bea2d18aea29189c626388ea21a87c61d186c618885a214884c612383c60d182ea0a3823204880a201a7fe9fda7ec5f7f7d7df1b7beded27aedea47a11e6d7935e2d787ddf67735dad7635d6d7535d2d7411ce472edc927211c6d7159c367059bf66f59bc86e7db7f6d35b2d6c35af66b35aad6a7da886911a0967ed9c966ed9a4663597665a195a650d911637d8b662c58a362558906179859612d84660e182a60717ea5f717ce5e4d78e5db97335be16cf5abd6985999634587560f58055d85729598559954f54514e2529d49051e546b515144650e142a4fbd3bd4e093744d993344c092be4a3127e490d23547c51da465917f45a1151453113e449d0e343790d0423107e40e8fdb3f10f803da4f2e3bcceee3ba4ee43b7ceda3b0ceac3a54e7e399ce503908e3438bce2a3894dea3674d6234e4d103330c7f31a0c2d2fecbc92e38b412c3cac22a40a4c28b09f12744996254892923948b321e082b1fc07d01de87361ca071 else (if i<4 then 0x1e41880c40a31042e1a305c26223102361a30501e01085c4619278016205429c01b1860243a0441e408a80811500948c1c0780211a0421601c30616e043060a0b70070c0b7007060c302626320604361856043867020430a8af810420444dc001410a1505410616e00f46c30818610521c41e460a808c050c1901e007c42580a04843860504870c046a4217120221103208821a0dca0c82060704e0110616831247060e081904e020880c837007060835150c185a08181c138020b4108837205a081818320c2064190430611b8082205a0c491f00922237005060c13801818588dc018c208206413804420602160512780407813803050c38030781b803050f380301f003830884f8030a80f8030b02b8049203c4fc002110fc0010c221be00088c30af0060d0ec3060d0ec309240ec3050c1d8cd044860cd0430ec3040f0d80c0440789b8002203c142078af803630581e30784c415037020840b0308a324842c01e00c1e24e00c1815418e0e1212085c3e000466340c0468383a060242270104240c07803322060249191821500f0088424b107e30621b8016204457c0185818451833808210904e1a020c1882108c1ec8110c2452310c2c3128444bc01c04662630bc41606088a420b10e0431171c940ce00f801067002c30b0308a30621b801c2070a84521910a0f64700645210588d02188b8e160612464a228588c4018704821a0b03c00b0c6701141c0244190d03011c3024ae0004884067010421212819c01c1c0dc01858944918589445183104211893801681118616810c2a25e040881b0a8085c481050e02105a0420a80e04307c08083e00584c307b220430d842c06e04088c61f410626e007c042e28581849180e041c185a042037003b02203104211f003c083083c06e00082a040e9c442fe041c1e1d370022c0340a082729183c0830b810617020c2e007801e0418401030f78033282f801c0f860a26417006640700282082142303410665070020e007801e0043dc0010103a5e007801027004f430f874c006924663017003d040c8ccc1e127030e150e9a022ee008483a838b87c0820a022ee00846851100c0dc00c17810417003c0080b801f17138010f01b80040e944403e00103a5e04104220181b80040e9a062a0308a08517c080221e00d0dc0820b810417003c0820b801e0078010f0fb801107874c30e005822182c2a062303062046e0078010181b80020c141403e0008305628383d030308a047e00d05c070c1780117f00423403860dc00c2a06230e81831043f020220540c7b0282433027e04045c0808b8101103801e020842be0050260f02030e0e004140303700040f061f8010181b80040b0320e70b02b801501c1c040f021254490f883c15037020e48061f810214302bc00883c3a60d89b801243874c000000e021 else 0x3cc8131028c420908146048ac412303c821710))))
def f507l9 : Packing := (378,3,6,0,0,14,0,f507d9)
def f507d10 (i : Nat) : Nat := 0x300fc5cd110a908d80846250cc0423f3129823600b18880386209d220c5d24d0c222c4c182687068d80628908160ee1b0c1315434686c084343f0b0769821a360060f99220e1b00d2085cb90187e8d808408631880c0a431e834686c01642823144840b2e8600082189f1c18310d1b0108f8d4e18624e87068d0d80022e68b0c3c2b4383c001428244840b496a1a360212218861c3300d0fc1cc4c0780027c407c0380c21e9e212218e0061c4458310ca60d1a1b00c512102c1dc56181487068d802c850462890816e1e313c492e292860a0aa1a3600b214122421f85b90d1b001d10307ce7c8d8088183e643c03e2e21ea1e022060f9920f124d485e868d80882c180e80c154686c016428244843f0b3969ea1e0220b06039d0d1b011058301ce208d80882c180e70306020434c033360c48a4360414240982a0e1b020a1204e0a29805662264e188138386c08407341c36041408b9b00320a1088d81070509026c0070c1a28705418342439ec0c628280c081300d0f0ccd83141a7c928b0e622e188043082c03733170c4032341601a1e199b0624280cc018091300dccc3c316725e185c6a0e43806890a033e063cc08704311c0c585030114821f99600a999b0630280ca0bc18886813001cd831819800e2e165e79e4ce1fddada5d30cc3c8ec49c04b7fb4ab0dab0a43a069d19ac98794a8d58608337be78174c7276f26cd68861b5de5a15645174e24a546042b3f63d139c37f32a2d529024b1fe1a11540f709202d000ffc514c3ff54530ffd414c3ff4c530ffc414c3ff50930ffd524c3ff60530ffc714c3ff5c530ffe774c3ff44130ffe554c3ff84530ffe444c3ff5c130ffd214c3ff54130ffd204c3ff50130ffd724c3ff5d130ffc744c3ff55130ffd874c3ff61530ffc754c3ff61130ffc544c3ff60930ffd754c3ff50d30ffd734c3ff54d30bfd874c3df95530dfe774c2ff21d30fee224c3fd84530ffa004c3ef91130fde334c3bf5d930bfd844c3bf58130fdd314c3f750d30bfd814c3fe48130bfe884c2ff61530bfd824c3f70c130
def f507l10 : Packing := (54,2,6,0,0,12,0,f507d10)
def f507d11 (i : Nat) : Nat := 0xc3040f0008c3ffd30
def f507l11 : Packing := (1,1,6,0,0,0,0,f507d11)
def f507samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff006bc440ff06100d1e517edf946e1c945e70b063cc3579184204223827f9c3795573c32000e8cadcc446bca4510857248c125380056a4827,0x2b80343a87800c0f40608782100094600044024019990020060088472081188430820801108a18c4041901191048278412538800220d07),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff39c895c00e920532003fc1783911e90fc3fd8231e08600f87a78723600a5c16b532d1045c2f20008411ba03c31c5058024944003910af009,0x1600178385100402003f00581d040d0b020a0231b10400d88a10b217885500277b880005fae11000219bc0bc20078190028420024188d008),(0,0),(0xc2a032bc7c80a26c21ca606040807033840c054e1232028e151a3d02c104103a220004b93840b03301080a431607c92112492a4800840750,0x2220363c468000040740402020001032c400610203186388220b1e260040220622044cf90440d011000b0842160fc10100402a0021a68d40),(0x1b2948b7d4f4322a3f5b9ea1d08a05cb1a01b55c1a4326661c040900a47093022642858f480a39a785409e80040318407acb188004c00934,0x5c4494381407f22301b91104caa09491a0382fc1c620471d0c0e010909b5441004b110640ab05a60b60c690804016407b89800014581030),(0x160d0321280fd1f00710862e678b780c020382a569cb6180c480880c08249608906a22050557503a9047486488225cc100813462310082,0x48043f0241200001700f0120286401080c16330084a002a1024801409000720342064420400651011081465866ca020049080812e2100080),(0x3fc0100000517d83f2208117e138a140b58d4e10408016202869584512060800801cd44cc21202201465001888f4008220a404039800b008,0x88d4280038400901f7409200226000c09c05a1064412172300eb0c40140090c0804674480016c6251460000280f000003420019090402000),(0xdc91f022008d68000a088038002620002002103480848408082000810048400402a1087890c0af8100140200020504000801460110080,0x16220031060f88068880e442c00a02f772a908451a140c4c5124160640100904a049319585e90c06401200048020c0550017800004050000),(0xc4102248804fc00440b42000080150082000488028109491811304db530228009da000123004818002ac50038b30c02b012026680a040640,0x10a00c08000000008b0288d1000020421400018284500108c10008948a30c00018003021200008882041020010030aa8000500808000200)]
def f507columns : IndexTree ColumnInfo := (.fork 32 (.fork 16 (.fork 8 (.fork 4 (.leaf [(128,0,379,0,11),(16,0,491,0,9),(8,0,499,0,9),(64,0,443,0,9)]) (.leaf [(2,0,505,0,9),(0,128,347,32,9),(160,0,347,0,8),(24,0,483,0,8)])) (.fork 4 (.leaf [(66,0,441,0,8),(32,128,347,0,8),(256,0,251,0,8),(1,0,506,0,8)]) (.leaf [(17,0,490,0,7),(129,0,378,0,7),(384,0,123,0,7),(0,2,440,65,7)]))) (.fork 8 (.fork 4 (.leaf [(80,0,427,0,7),(0,8,227,272,7),(10,0,497,0,7),(264,0,243,0,7)]) (.leaf [(320,0,187,0,7),(0,64,185,258,7),(0,16,482,9,7),(3,0,504,0,7)])) (.fork 4 (.leaf [(1,2,440,64,6),(2,64,185,256,6),(64,8,163,272,6),(72,0,435,0,6)]) (.leaf [(2,16,480,9,6),(1,16,482,8,6),(256,64,185,2,6),(8,16,482,1,6)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(256,128,91,32,6),(16,8,227,256,6),(256,8,227,16,6),(129,16,354,8,5)]) (.leaf [(162,0,345,0,5),(224,0,283,0,5),(168,0,339,0,5),(258,64,185,0,5)])) (.fork 4 (.leaf [(320,8,163,16,5),(264,64,177,2,5),(384,8,99,16,5),(288,128,91,0,5)]) (.leaf [(384,64,57,2,5),(17,128,330,32,5),(272,8,227,0,5),(25,0,482,0,5)]))) (.fork 8 (.fork 4 (.leaf [(19,0,488,0,5),(17,2,424,64,5),(10,64,177,256,5),(9,16,482,0,5)]) (.leaf [(10,16,480,1,5),(80,8,163,256,5),(3,16,480,8,5),(65,2,440,0,5)])) (.fork 4 (.leaf [(11,16,480,0,4),(336,8,163,0,4),(400,8,99,0,4),(137,16,354,0,4)]) (.leaf [(177,0,330,0,4),(49,128,330,0,4),(83,0,424,0,4),(81,2,424,0,4)])))))
def f507autos : Array (List Nat) := #[[],[65,99],[128,49,100],[128,97,67]]
def f507levels : Nat → Packing
  | 6 => f507l6
  | 7 => f507l7
  | 8 => f507l8
  | 9 => f507l9
  | 10 => f507l10
  | 11 => f507l11
  | _ => emptyPacking
def f507index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 5 27 5 8 2 2 (keyf507l7)
  | 8 => lookupWord 34 229 8 11 5 2 (keyf507l8)
  | 9 => lookupWord 207 931 10 14 8 2 (keyf507l9)
  | 10 => lookupWord 491 2211 12 15 9 2 (keyf507l10)
  | 11 => lookupWord 70 367 9 12 6 2 (keyf507l11)
  | _ => fun _ => none
def f507 : Forest := ⟨507,11,fun j => f507samples[j]?.getD (0,0),f507columns,f507autos,f507levels,f507index⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geomf507 : graphValid f507 (boundsBefore knownPrev_f507) = true := by
  unfold graphValid
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel, by decide +kernel⟩, ?_⟩, by decide +kernel⟩
  apply listPieces_all (d:=3)
  simp only [listPieces,IndexTree.values,List.length_append,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceDiv,List.take,List.drop]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf507_6_0 : block f507 6 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem blf507_6 : block f507 6 0 3 = true := sf507_6_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf507_7_0 : block f507 7 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf507_7_1 : block f507 7 1 25=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem blf507_7 : block f507 7 0 26 = true := (@block_merge f507 7 0 1 25 sf507_7_0 sf507_7_1)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf507_8_0 : block f507 8 0 28=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf507_8_28 : block f507 8 28 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf507_8_60 : block f507 8 60 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf507_8_92 : block f507 8 92 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf507_8_124 : block f507 8 124 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf507_8_156 : block f507 8 156 5=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem blf507_8 : block f507 8 0 161 = true := (@block_merge f507 8 0 156 5 (@block_merge f507 8 0 124 32 (@block_merge f507 8 0 92 32 (@block_merge f507 8 0 60 32 (@block_merge f507 8 0 28 32 sf507_8_0 sf507_8_28) sf507_8_60) sf507_8_92) sf507_8_124) sf507_8_156)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf507_9_0 : block f507 9 0 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf507_9_2 : block f507 9 2 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf507_9_34 : block f507 9 34 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf507_9_66 : block f507 9 66 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf507_9_98 : block f507 9 98 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf507_9_130 : block f507 9 130 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf507_9_162 : block f507 9 162 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf507_9_194 : block f507 9 194 9=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf507_9_203 : block f507 9 203 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf507_9_235 : block f507 9 235 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf507_9_267 : block f507 9 267 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf507_9_299 : block f507 9 299 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf507_9_331 : block f507 9 331 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf507_9_363 : block f507 9 363 15=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem blf507_9 : block f507 9 0 378 = true := (@block_merge f507 9 0 363 15 (@block_merge f507 9 0 331 32 (@block_merge f507 9 0 299 32 (@block_merge f507 9 0 267 32 (@block_merge f507 9 0 235 32 (@block_merge f507 9 0 203 32 (@block_merge f507 9 0 194 9 (@block_merge f507 9 0 162 32 (@block_merge f507 9 0 130 32 (@block_merge f507 9 0 98 32 (@block_merge f507 9 0 66 32 (@block_merge f507 9 0 34 32 (@block_merge f507 9 0 2 32 sf507_9_0 sf507_9_2) sf507_9_34) sf507_9_66) sf507_9_98) sf507_9_130) sf507_9_162) sf507_9_194) sf507_9_203) sf507_9_235) sf507_9_267) sf507_9_299) sf507_9_331) sf507_9_363)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf507_10_0 : block f507 10 0 20=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf507_10_20 : block f507 10 20 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf507_10_52 : block f507 10 52 2=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem blf507_10 : block f507 10 0 54 = true := (@block_merge f507 10 0 52 2 (@block_merge f507 10 0 20 32 sf507_10_0 sf507_10_20) sf507_10_52)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf507_11_0 : block f507 11 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem blf507_11 : block f507 11 0 1 = true := sf507_11_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tablesf507 : checkedTables f507 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block f507 0 0 0 = true)
  · exact (rfl : block f507 1 0 0 = true)
  · exact (rfl : block f507 2 0 0 = true)
  · exact (rfl : block f507 3 0 0 = true)
  · exact (rfl : block f507 4 0 0 = true)
  · exact (rfl : block f507 5 0 0 = true)
  · exact blf507_6
  · exact blf507_7
  · exact blf507_8
  · exact blf507_9
  · exact blf507_10
  · exact blf507_11

abbrev knownPrev_f1519 := known1519_all
def keyf1519l8 (i : Nat) : Nat := 0x140
def keyf1519l9 (i : Nat) : Nat := (if i<1 then 0x26f343188dfe5ecc034a0b0000000159bb34e22ec3ad30000621a47148d0006134a18000d86aee4000000000000012d33c69ac1eced18b038024b9cb34797c12d21978c66ad50e15a316632c7ee05d3dc7f73f15c891ff953030c7541f808d011e82a6e51539d0002eaa0001238002882e118193c926b84be4104ed9c6fcb8cad36590b416e4b680ff64564000000000008a5a559a31f4e507f80faa747d30652c000394556200000000000000000001d015731253c2800000000062a190e739fdbbd74001889c36ae6800000000000000000001b511d800154e0000003a21ba8cc40002c06424ad8800000187a3a300000000003bd000000166f0002e4c0000000000000001e6162300026d80000000000001e0e294106c00198a1058000ae0000a248d94000a6b41770ec00024fd214a40000000382a00000163d84dc4c7cae54700059d77180001938172543da9b090003935e0c55a42bc0000000007a53c69b2a44c5d0e6c8000a1321a8000000000159800000000000023060000002d2e15b03659280034a8000d038000000dba8da2ac6c3fc508c480000000006a78000000b77f4a800000000075d8001522000b918e3743073f3b7acce6e3b59c3606bfa1d38085bf94c00097b40b35f1f6a7088d6800300861c7bf2a7c00000068780000000000000000000000414323b0ce00000025e0000000bc910f294d13d03e7ee0000a1520d02cb67c767c09c45028800035cd67defa0000007d7e74540aca4c42f44a02f00000000000000002034000000d5d390ee680000005e780000008500001b0e00000020cc000000000000000194d6ce00014ca0009d9ba9f812386cba055dc73a307157503567a23da6121405a27169330d462de77013d4c8033b2dba90ef4001c8400045840017be24cf0886079ae00000030980006160003d260000000641284c1478fb6ad4a5a64da86a8d452a4412b0000000529a3a405cc960006cc320c00000000046c196b851849269a6265216af0a5d2136682ce8000000c700005408000e9d72f7c700001207d63a0a23c000782000000000000000000000000002cac000000d0f0002a760003add290000c2b5bb0d636fe000b409814caa43a139d5a40c40003b5d1e20ba000aa980000000005c88003d3946e600ae2d842000e5b0003308000000000025925b7270001f42c5f0000840000000000000331c00001c0805c0300800004020380c02c0000c030040a00c020340300c0000401058010240200007018020040501804008030100201417010020000d01006060050100900000004000000c01802000020000000800004020380101400004010000100003000030180000c010000001c010440100403008000141000c0200413014020040100005004000100000c020080203c000000a000000000000000 else 0x155425e8000c8adb24d2144b15974573909f7e6c0486b1b22255da8a8a8800133311a3550)
def keyf1519l10 (i : Nat) : Nat := (if i<1 then 0x32f580000000000000000000001440000021ca0000327800000009a78000000000000001b4d8af9800000000001687000002a3e52400029e33c3400018c30000000011abd0498eb000000014eebd802af600034be000000000000000462900000000000000000000001e7c000000000000000000000000000000000000000000d1d800000000000000000064c60000000786b00000001eee09b9000000000000000387f63200000000b1be00024f10000000176232130000000086c8000000000000000afda4c2892565840004df6890dc0f400000000000000000000000001d984a568000000136cc0000000000000016eb0000e8740001e3a10edf81a00000000000aa1127716fc062239017155d0ecc090000000000000004c6c0000000462b587628d5c5524b64c0e0000000000000000002e7d0000e8a9d8708131e27186e00000000000d295b3000000000514400000001c207b29120c69481d00000000287b607e0000000086b000068b8000000000b1000062a400054ec0000a67aeff8000000000006944cf75a0ca77c000000000000000000409a61e557a2cae540179fe0000000000000000000000000000000000000460300100000000300000500a00000000400000200800000000000000000400000100000000b00000000000a00000000600000700300000200300301100000000400200500100200d00200000300000200000000000900600000100000200002400000000200000300200000000000600000100100100400900000000000200000400300000200300300600000000000000100100000a00100200f00200000c00400700000400000100300000000d01400900500000000500500000000200000100c00000200000000000300000000100000000000100000000500100100000300000000200000600100000800000300000500400900700000000100000100000000200200000000000900000000000000900000000000100100500000000300100000100200000000000100000200000100000000000100000100400c00600000000100000101400200000400000100000300100200000000000600100000000b00000d00500200500300000000000900100700000000100000300100000e00000100000300200000000000200000000500000000000000500000100000100000800100200700000200000001200b00000a00400000100000200600100400200100000000200300100100200000400000000000000000100000000000000000100000100100800100201100000000200600c00000100000300000000200000700300000100000000300100000000d00000600000200000100000300500000000200400500100300200100100200000000300000000100400000000000100000400000200100100a000000 else (if i<2 then 0xdc8ea3540000000bb8a00000000000000000002b32d01fbcc000000039946248628204b951b00000000000204e119b324feed5c1c001126d40000000540800008cab0f900008475508a04b60c8e37800065220001312fb218000000036f2acf8000000033f80000000000114f492b843d0000d2cba44649000000000000000000016251a8c800000000001ed8201e000161b00000000215e00000003cc70000000001df9230000a7236d5ca6e0001c9100878000000000000000000000141e00bddd710000000000064fbfa4a000262b80000001644400011af6179388400059350000d8e800000000000e456d30000031f400000004d6d0000000007370817974a6708152c210945f2c000065703909824800000000000000000000000001809000000004be400000000000e952000252ac63bdafe000000000001104000000059c4e2c40001c0d0000000168b4000009b6822d197c0aa65cf0698604304cd8250040003c7f94e8f82506f2851f84c0000839465310633bda00000000000badec06c0000000000027040000000f24a3563a785a02fb6e364aee9000099280000000000023760000000000000000000000000000000003921c1010000000031fe9a551fa773c00054bf00000001863c1cd000121df11944bc6ac2e502462483e58ba55d6eaeaa1933bc00000002cf400005454e7480008966000000000000000000306d8000000000000000cab42a870640007074000185340000000000000000000000000000000005166f0320000000622a0000000000075c30000305c000000000012482c5a8a5113d2a5b3af8800000000000000000000000003a72948770b293200006163000000000000000b9d7480c0002066000000000000dc80001b13d203d5a1136705bc000000000000000400b16700004635001f535fc47e8b0abe215604cfe69a2256d390b3c000108b312dbb14f5880001e0400015018000392e0001614710454ac0001e7cc00000000000000000000000001d96c0000000cb540002d320000521ae8cd08f55c1a37ba25a0d20000415a0001efe986a93740000233d91c60e718bc000113c0001464800004c4e046f62c000402f00004889ee58000a274c594411453fb20a00000000e34000000006f48000389a000000000000001489800000000001b22aace805bebba00024598000f8dc000166bf40b0000a89dacb800062b5a848000000000000000000000000000000000000078df169c000000000000002e8bad46d92f47ec0000000000000000002553d492f5f40000000999a0000cf8195f00000000a6728f55260071c0001153783ee05ae79087ba453a7e1093ddec787c687de099d57e9ec00002ef8000026c9838899455b4adc7744000026289dc00000004a18d3d40002a8a00000403668663480000000000 else (if i<3 then 0x430369a80000e02d2a654564a9f3122685800000000000f150d682176c8d303391460001c0c000005a050fb25c823d20e4c2d720e2b31e42e62fd28fec8c6596000000014f080000000000188d00005c8a000000008569254000000075a2000000014ada126739e20c4cfe55565bb6a15c0002c5ac8a200004a81122db7c940b860800034b2000332b80000000000000034d413f2870d309a5414460000000000009a6951156bb0000a4800882aa86dc289bdf0300004dcd1bdc00034b40a610000d9b0c2a60b4e3b4000387e00000000000000000000000027800069d9eaa80001e1280005cc1d0100000000f4d0000026311be00000000000454700000000000492800012129cc2800090780002c0980005c80000000000000000000280680009cb0a7fb850d4140ad2000165180000001a1600004e4b000000000000000000144280000cb7b2dc082e8219db963ced80b20e9c056a766168000000041319941ea242250001f05ab34822e2a48a564000186001c330428633a47000000024d000000001463c000000000000003484863930c5a0cce360000000000000006dac0000000000056163998935800005d00001e935335ccf10000000189ca25bd2e00000000000000009480e0d1c8d0001b5564368000104e0000279dd7a000189388b6d9433888b9932a50000e482000110a80000000000000038d2000143a40d102450000000000000000000000000000000001345a078000002fac4cda4700000000994bc2f80000000000000000000000000000000000000000208700000000000000000009855035000048b21aca00000003d2bba9666b153680000000a1fc000320db9c0f4480002a5481a00000000560f0000000000000000001d73a27680002c2b60b60b50000000000000000000000000006c18000000000000000000000000000005e3780a61192e3f0000d0ea000049c00000000000000000000000000000000000000e6740003178000000036ef00000001e4d00000000000070d40000d670000d41000074cb540c0002ca0b02178f1d2540006250000000000000000000121780005d0d0000000112f8000e08566e3d231a059174227411c964e19a2000000000004052c3730ec180ef9a565e86478000e04a0001677d83900000000000000023c0000000000003b68d894000000000000002882553a1252000000000000000000000061ce00009178c46800000008958238b8760000000230688140000329f81fb0f4fb6c000271c4daf34d412d00d580000000000370900000000187400005b5b8300000000015d00000001847401d1cd40001e6cc95e0001c3cc00000002a9c21256750000000000036a0699800000000000000024260000000000000000001b1e800052163569ae20000e98a0003a3e759bb8d00000000000 else (if i<4 then 0x5c280000d188000b2c135b02140000000000010d6b48c0000000124d8000000000000000000e28a838a4663e5d19fb50880000000000000030cb00000be8000149580000000000185838d80001081c000025860c20003b232e5ad97d546361e09642b2600000007a10000034b58db5e0b208a222c0003912c1fc0000000762ee2e8d861adc0000d2b00001cd7000000000000420be6d0000000028f500f1157b8408cd79ff000000012dd79e4015ca34ee97a91bc288000366085630000987e67154f50001d640d2910e7abc523298b4d22b000000000000c7032a4000207000000001c93c000000010f37828000000063e800004da59030001e85a06480003c580003ad18000bc40c2e4cc4597761b3f4a80000000000000000001006000000002ac993d000000000000000cbde000000000000000000000000000000000000000000000000080b8000638c00000000c6b607527d4c9baa14a32f08dc0000000000000000000000000000018b88000000000002dfa10c1a27c308e000000000000000000000000000014038000a25f20dca16fa5e32e7c07c00000000000d50c0005895d439a7bfc6bd5230001385c00000000000279400030ce0000a8f000000000001197e84280001a1e38a0000000000000002484713fb3260000d06708f00000000000697500000001c104c859ac00001722194e000000004a7da6f3490000000000000000000000069c0493a000000005a50000000000060c0f36255440000000ebf5592a21480000000000168180000001899b2e000000000e94f11e81d400000001cc81176000108d8000007c5056b6c88c4e9eecc03f76407be13e50d256440eab4d0cb48271400000000000000329b800000000001ae98000f882000000050a4000132f48437ca00000f163c498df700000000846000000000000000000058600002298061100000000a1632210000000241aa94b4c36813f2afdc230c79189a4eb68a59b2ab99542ac9022120000000074b50000000000000000000c22b81771e80001021081900008862000000000009848517c00024b921f1a4ece5c10105a0ae61d05f800000000001e988000000000000000000000000000000000000000000006d216bce0002c328000243600000000000eb3390d184e000063b6f34c00000000000000000000000000000000000000000000288a3980aca987300002a1e713257aa8d499846a01c6aa12d32704abc00010e5a080000000000002473fb51716ecf61018428e0000000551a000069ae40500000000000000034770000d5f80000000000000000000000000169a4000000071c663b3490c1d1000000000000000000000000006a5c70b9f8b40001da6000166448bc8000000030ac0000000fa20000000000005a85a0a000000002c49097790559839923d6 else 0x28a6000140456018000000000000000de100000002d1200000000e2b2cfb2c4c817c00004dbd09f000136efd1400006aefe21c000000000000002878f955d170000000000000000e41a8c171ed3ccd554b004ba2f0000e36a4380000f1de000007d80000000000000051190001255c000000009b000000004c96ea703432af1a1f70001674800000000001342800000000000000000000009090d4cc0001a4ae16c000000010885b980000000000000012110000000020a13537ab965b1000139300000000db920003b0f000052fe57c3284dc610001c6300000000ace000000000000000000000005a420000000000000000001801000000000000000000025450001d83168e8000bbca00000000000c41c0001e2750520000000000000004c00000148f8000e4ca000000000000bae000000000000000244de2300000000000000000007ac9e1740000000db8e21c74204a4c4284000000024aa54740000e070000108db11d6ec000000000000000100c00000002823b8684ad6000010b80000000f4f8000000000016868000000000001125065e0369b8c00000000000516e000000018a7531c9392a44a88948f600000000000cbead6b631880000814e134a31e0bdc496075e2a4000090dc00000007012c86c0000000780504000003e3b712c000000000000000000000000000000a4d8c1e8c37f1c9000151e763300000001874cc41b4fce3fb507bc746c3281dc000000000008058000000000000000c70be36800000000000aa4981cc2620001cf89a38118694b8000640f282ba5323268000b3600000000146200000000a9908dd0000d57040000007c32000000000003447e66cefce8a883f4d8fba6180000000662ae0109eb7b7a0000000000000000000000459a0000526400000000000000000004c90000445dad480000000000000071070001883f0390000ebc0000000049e60001b8cc00020d1f3e400034880000f1d542440004e0500000000000599f3cacc3140000000f291e62c0000000000116700004a3ea88000000000000237fd93e4d1ec08000197500000000000000023310000d84e0000000000000000003e390000000000000000000ca4c000000000000000000000000000001633d8cc8000000000000000000000000000000000a8b2000000000000000000000025730000000000075fc0000669c00074cf0000000000000))))
def keyf1519l11 (i : Nat) : Nat := (if i<1 then 0x313fbaf000007000000051c369511e2080000000000019c278000001ed19b18000543aa400000000001a2f61800196c00056e98cd8ea0000005d36e8e000000000000000000000000146d56d521a641d4ba1a7d24c0000000004a1000000000000009280000000002d9c181140888706d5893240000001aa0f8900036193350006dd04c2d220000002914c050003929f9e000000000000000000002fc0007040003294000000000000000000000008c80000000000000f3bb16fe18000000934000163800000096d800191c22ea59a8d1b7400000061b80000000003b5af0e6cb70d8f05136deb68d3c25a3a0000000000000000000000000000000000026d6571c7100000004e06d37164831dbc33672c21d7711c294d6c001c000c456b0c1a000f080000eaa00053c80022760000002731860e86cbf80000015050000001fc600000000000005672a10000000000000000000000000071f42b0000000000000000000079d00000000005528001540000000000078be092c62cb60000000001f9d2d30005aeccda000f97800000000000000004740000000003f737ad0000000000000f750000001f61f2778bc00000000052b0000000187e094000000d030001ad94e90000000000000a2e0000000e4b0000003dc80000000000000000598c0680000000000001d6f2c8f56d0780b06e3f3b59a8000c2d43880000000007d9575cab3125bdb196b4176e734928dc000d6f00034c8001265000165c00000051d800000000000000000000000002ba1118b4b00008a58c80000007a550a801451ef8995b23360003ea32379170007c0b65000000000000006990000000000f7c0d811250a3868000000273d623703fe9f884f1c000000000000026fb0fc000b8c0548003ef600000002f8000e093020001ee572b0000000001c03000000000000000000000001e40000a8c00073026c000112032e86600000000000001d74e9c00000000000000000003aa000000000009fc00093ee44800277b793c9e0000caa3c00007eb8dc2000d0fdf7dae0000000000000000000000000018960000000000000a017a9e7962af8378289304000b3bf5b92fada30000000001edc000000000108d0000000001da19166ad1da00003da10f3938000a5a8000000d2a1961d5c000000000705c000000d3900000100805014000000100c010001000007000000040303802000020040000400014060180000402004010000000007008000000200c0000c04008020000100000000000200000c0000000000000080000c000000500c00004010000000c000000e00001000000000500800004020001000005000030000000401000060000100000004000000001003008080000000800014000040200c010080500004000010000000002000000000500001004010040000000 else 0x51e2956db5820dc38d88880d22feee614ccfa96d4832d43dd8ce00012f2000185b11f09a00089fb2a800000000000014020000000003baad0d0000002b532156c8a83c00125fbe5705b0fd308ef4948e686eca8bf000267a040381a7100000000005acafc20000002208ac40006e448f800000000036afe26d697dc6519a8b95e00000008f855400014e74cc0000000000000000b62800000155f0000fa800000000000000000000002b5c001b9f4949d327d08467143ccc000a5d0000000ca600000000026492bc00000000006b1090c8c4d3c0000000000000000000000393095a0000002dcd485000215c000256000533444f22a4e280000013c9000000000000000000000007141638000001820e35e64800000019d00001100003c7a088dca0000000001498000030265990e0000000001c480000000003a4c0000005f88000d660001a746da000b21e98fca000000000008180000004e6e1840009b2800000000000000000000000000000000fb7b3dc1ccae60000000000a92000433800000000000062e717b97800012e00000000000002fad883000135043aec6000725c0000000000000b0da8bc649246784000a6f00000000000002da000000059c2304000be07098002f060c00004454000835fbae5497678110530002134000000000000000000000020bca2b000471862000000000000000007ca9544000000ed89e634724ae33869880000000000000000bbfb6d562b8f4000000057077ced2f221e1)
def keyf1519l12 (i : Nat) : Nat := 0x5dcf40000000000000658000000082800000000000000792000002000089800000ec00509e8bc3dc14093d940036200000004de00732060004172d5c80000000000004c72052bc800000068ae00000000003600007001f356a000000000000000418017b8000000000000c40018ae9e000000000000000000002a001e380120800003240010c000002808100100000400000000c000
def f1519d7 (i : Nat) : Nat := 0x143e4b08ac6bb2e8a1f2d61158c985d943
def f1519l7 : Packing := (2,5,5,0,0,4,0,f1519d7)
def f1519d8 (i : Nat) : Nat := (if i<1 then 0x1121942cfd65e11a2142cfd84593a2174cfd64e1120574cfd8459620543cfd8459720543cfd8469961943edd5ca1161441edd4ca1161441fb58457658d43eeda661161032cfd911981ce11ef50861160c74efc0861160074edd9121161432efc88a1160074efc68a1160074ef550d8260e11ef561d4360e11ebd9121161832cfda661161c42ef99121160873ef568a1160c74cfda661161032ef588a1160c74eed8464461032dec8459020a44ead9121161873ee69114360032d6e9dd9020a44af6aa94360032e6d9121161c32f2b9de6688a44fa98466688a44e679114361c32a77aa94361c32cb7998985c633ce7910985c633ecd8464461473ceda661161073cf9889981d211ef450e1160032cf3888985c633e7550e1161c32ced911981ce11c5f9de9961441cd78ce9961441eec8464460032e579de3361441cdba662261441e5d9de1161441cdda661161441ed988a1161441ed58ce1161441de68cd9020644d6e9dd9020644dec8459020644dea8899020644ab7aa94361832ee98464460873cf5844985ca33ecd8464461432ceda661161032eb58454361832ea79114361832ce7910985ca338f7aa8985ca339eeaa99020644ecd9121161431fe188a1191233fa58466691233f279de6691233ed38ce2261441e5b9de2261441f659de1191233e3d9de1121942e5d9de1161442c5f9de9961442ced911980ca11ead9121161832cdd8469961442d739dd93212229f3aa99321222cf550d980ca11df18459321222abb6983260841a7b69c32608418df694985c543afa6803260841af328d7260841ade6944160032bab6989888a448fd2a587612119ee6809848644af66803260c41ab76983260c418df6949160c41a7e6807161c41a7769c3260c418fe68098486448df6949848543cb758c985d9438df694985c943ad728d7261441ade6807261441acf6949161032a9f6944161832acf69072614418bf69a99609438df6949161032ade6807161441acf6903261441ad768c9761441a9f6989761441ade6809761441adb6889761441a5f6944161c32a9f6987361441acf6949161073ade6807361441adb68873614418df6959810432eec8464460073ef188a1160c74c5f9dd95205438dfaa99520543cfc8459020644c7e9dd9020644cbd84596a2142cfa8899020644cf68cd9020644ef88462260074f699de44846229eeaa99020a44cf9a661160874cdd8459520543ccf9119520543c9f9999520543cdb8899520543cd78cd9520543f2758d765d143f63509725cd438bf69a99610218fe68091a21748df69491610738fe68091a21438df69598104738f72a1945ca33acf6944161073caf91196a2142c3f9dd96a2142cbb88996a2142cb78cd96a2142dad8459620e448bf69891a21428f768e9961d42abe68087219428fe68091a2142 else 0x310184c204064064400000000a244200032109e16123049420440510142850a15106c40006c20c28400000000000a30809c1000000000000942690e14200000007803e008000f0040000000d007c01f0051f821011f8217802007802006803a00e803a00801e00801e008503a00f8030fc108000a041a0080000001e00e8020f007c01d0040017c885e0093824e0c8c24e093830e0800007041c1a1868610706461918401309382160c3830e0858214083034309382120848212084830e093830e093824e0c383e00f802000000003c01003c01000000003610a041810604181870410e08000078020c085021908303de7b5f54e9fce399f2ee53c938ff1ae07bfb7ceebd97b1b5c6b3d4ba5f44e7bcc997f2d64cc8f8e71a62fc558971061bc2d847065febf37aef35e1bb975ee95cdb9170edf5b0b45652c7d8ab0b602bdd76ad156aaad50a974f69c533a5d4a69251fa2340e7acde9b330a5a4af9552724bc929091da3445a8ab1422143d8710aa0e40e800fa5f23df7a2f31df3b9768ebdd53a5740e49c237f6e2d8daab50696cd193318614bf1772e05a4b35642c356aa9d4ca8b4fa9bd30a5c49c9011922442c820fd1ec3bc740e11b434c660c517c2dc580a914426c4a09191e2324508790a20a3dc790ed1be3686a8d0196318608b314a25c4487b0da1a02d0550a012c2303805407007000cfd8459760c41ef58457360c41cfd844985d943cfd844989de44ebd21e1121942cfd8469960c41edd9121161431cfd8469961c41ebd9121161873edd9121161473ddd8459520543df550d9660e11cfd844989dd42eeda661161073dfc8459021d42cfd844985c943cfd844988ce44cfd911980ca11cfd8469961031df56a6115cd43df565a115cd43fe568e115d143fe558e115d143f755ca115cd43cfd8469961d43f6d845765d143fe550a115cd43cfd8459761943e7d9121161c32cfda661161073cfd84597a2143cfd84596a2143eed8464461073ebd9de)
def f1519l8 : Packing := (191,4,5,0,0,11,0,f1519d8)
def f1519d9 (i : Nat) : Nat := (if i<1 then 0x6cb909114ff660410ca7f930a0c453fd98104739ff4cb0818cff2468850f7ec2344287fb611911439fec9510a1eef911840c67fb2f442873fd96a21439fe48b0ea15f7a65748cefb922ba4677dd9210633beecb88319cffa65841cf77882c20e7bf61161073ddf2230839fe7508418ce7f922c10e97de995ca33df610b043a6fb485821d2fbb28b9467bdc985ca33bee48ae519ff3509728cff5c45222e9dbe77911749fec9902ba7ed846445d37ec23442e9bee22a2174ddf44488ba6ef60a445d27fb2440ae97dc9150a33dfb08902ba4ff245841cefbd32a14673fe9920574dfaa0902ba6fb888815d377c8840ae93fe9960874f6f332e6a1ef7a217350ff9c44b9a87f9e445cd43fd7112e8a1faf9997450fbbae4b9a87fb6115d143feb08ae6a1efd8458750f7dc44c3a873fc91619439fecbb0ca1cffa658750e7f922c3a87bbe4461d43d7f3330ea1efba222250bf588311285fae4488942ef73bc44a16fd845821d37dc44c10e9bec8188942df6c3c44a17f98462250bb7aecba287f9d4191233ddf442e8a1defa657450ff3ae9224677dc9891233bee48c8919fe750a448ce7f923442e93fe9961021dfa90902a16fd5048150a7f922c2043bbc41610219ff4c902a14ff64c8150a7fb2c40a85bf61161021ddeb2510a167f9dd84086f792322285bbe44610219fecbd10a16ef2064450bf6c2322285afd96a2142ddf44488a176f9de4450b77c8840c673fd9761021cff3b902a14ff65a8850b7ba8640c67bf61120542fcf2226319ebf2048650bddae4432859fe77a2142edf3b882a16bfa208650b7ec23442853fd93a2174dfb08b0ea14ffa658750a7f923442853fd92a2174d7e4390ca16bf61c8650bf5ae5222853fd9720542ddf44082a15f7a65768cef7b2620a85fad7210542f7b0890ca16fb5ca8850b9fcee432853fd93a2142ed7114ef227b5846668cff8c6708c456bd9620e4497ecb510a17678ce779127f32040c89bb64460473df908b0039ef3889831d27dd32c10e9be62260474deb08b063a6ee911801ce6fb2a40a87eb66684644edb08cef227e99121188b7e422c00e9bea2260074df308b043a5ee640829137b286c00653f5981ce11df908b00196ee911800cb1fcee4328397e7761441daf19b0a20cdfa6585107f1c6711489eae6688a449ee4c2e319cefa65841cf76c88c0865b761161473ddb08b0839ecf911851cf3ba86c3865abe44618739facc0e908ebd845861cf37c88c38659f61161c32db71130a20e3f9dc8650b5ec2243285f961191233d9f2230a18edd845850c7d3ccd2246797e7761442dbb08b0a215f364c8488a7eb301942337e9961442df308b0439eaf911860cb5ec22c30657b99020644dbb08b0a20eb750d860ca77d32c20653dc985ca33dd72230439edd845850cb76c22c2065b3e4461432 else (if i<2 then 0x8b043a6fb645821d37dc22c10e9bee9960874def113063a6f7085831d37ec44c08e9bde1160c74ede10cef2276f48677913b7c233bc89dbe229de44ede994ef2276f20a77913b7a633bc89dbc819de44ff2b9c23117f964e1188bfcc8908c45fe54384622ff242423117f96521188bfc8e908c45fe57484622fdb11423227ed8ce11913dba8333467edd7499a33fda99423227ed58a11913f6cef08c89fb43284644fce40c8919fe7246448cff3ac322467f9d7191233fce4c48919fb7846668cff3ae522467f9d7691233fdacb423227ed21e11913f6b2708c89fb57684644fe72244519ff3106228cff6b2f08c89fce1188a33fda41423227ed64a11913f68e508c89fb57284644fdab9c23227ed20e11913f6ac708c89fb47384644fce90c8919edf105851cf77d32c20e7bf64460432dbf2230a39ebf105861cf7f488c0065bbc9161073d7f2230c39edf24d851076fb26c2883b7c7361441dbeb9b0a20e7f911870cb3f882c3865b7c9761441dbecbb0a20feb5ce22913f5aed11489fac8188a44fd648c45227eb26222913f3c2322467fac8788a44fd64bc45227eb84622913f5cef11489bf84160032d7f3b90ca0feb1c622913f5ae311489fad3188a44fd6b0c45227ee64081912f7930b9489fac825ca44bdec9103225ef26121912f7b2e40c897bd9320644bde4c2e3225fb65c4188afdb2620c457ec985d222bf6ca103117ed20571912f7b2c38c897ec9850622dfac3b0908dfd659848477eb0cc2423fd53260e11feaa1b0708dfd649838477eb04c1c237f59361211bfacc0e908def65c82912f793098c897f5985d211bfac930908fed50984847f6c88c24237ee9950e229fec9903224ff648819137eae240c893fd9720644fd711283227eb2517250bfcc22b9285bf99020644edf3bac8a17ed8456450b7b926c3a85fad7259142cff3b903226fb888819137ec2240c89fad4391222ff240c23114ff65d82106f793119c897be995da44bdec910f2276f5da779127fb26c10839fe7760841df71130420f6f9dd419127fd32c1083bed7260841df61930420efb08582106feb2cc1c233fc98585439fe4c4eea15bf65a8850a7f930b8a8777d9520543dfac0902a1cff2612150e7f93098a853fc985c6449fe4c445224ff262339127f93098c893fd981c4429fecc422214ff261219127f930b8a853fc98585429fecc2e4a14ff662111d2ff32043a859fc8761d429fecc0423a6fd2058150a7f93090ae93fc985c9439fe4c2eca1cff261315d37db04412e9bf581205749fe4c444ba4ff262779127fb2ec1883bdd7360c41dee1930620e7f9dd871067f922c38839fc7161c419ff4cb0e20cff24583107f3c8818a87f9e448cd43feb08c66a1ef7a203150f7b862c18833fe9960c41def19b0620ff988982846feb3021423bbc4161031bf else (if i<3 then 0x908ffd50984847feac6ba423ff54361211dff08d10ba7fd5c984847feb30ba423ff5935d211ffac22e908ffd4c984847feceec2423ff5835d211ffb2206308ffd91183847feb04ba423ff6995d211ffa992e908ffd50974847fea86ba423ff57361211ffab1b0908ffd24974847feb24ba423ff57661211ffb1148908ffd2061150ff7c22ba287ff57660e11ffacba8708ffd661438477fc22c3a87bfe1161943fef08ae6a1ff78456350ffe90308ae9ff59650e11ffac148908ffd5d943847feb04a1c23ff67791211ffac928708ffd8ce44847fed32a1c23fd64484633feaa142319ff5212118cffab2908c67fae445c932feaba42319ff55ca118cffab2508c67fd56484633eeeb24ef19ff35d2228cfbbc233bc677bd96846449feca103117f35c6228cfbbc893bc67ddd619de33eeea14ef19f77506778cfbba433bc67ddc419de33feabb42319fed206119137bc66c2423bee2261211d7f3330908fed1c61191377c88c24233fc9161c42cfe38b0e214ffa658710b3fceec38857bd9284644bdec9c23226fd8458710bf686308c89bf61120622ddf22103115ef65e11913fcc22b9265fd59684633feacbc2319feb9112188a7fb24c2423bbd4261211fda10c23224ff65d848467fb2cc24233fd9361211df711102a1ef78cc8150e7f922c2065bf61120543cff3b902a1cffa648150f77c8840a87afe66205439ff4cb04a1cff2458250f77c88c12879fe77609439ff4cb08196ef105840cb7ec22c2065bbe4461032dfa98902a1ef7a216350ff3ae8b1a87fd61158d43eef3bac6a1efd8458650f3fceec3287edd7658d43beecbac6a1edf6548150e7fb2c40a87bf541205439fec9102a1fe79103250f7bd10192873fd9720543feb08864a1cffa658650f5fcccc1c237f5940c611df71130708ef750d838467fb2cc1c23bdd3260e119fec930708efd845874cb77c88c3a657ee995c932df6c22e4994ff651874cbfaa8618c233fe9961d329fe48b0e996fb88982846f7d32a1287bbc8150943edf3ba84a1eefa214250ef7b2ea1287bf61160943fd6b9284a1fe75cd4250ffac6620c23fb54210611def19b0508ff988841846feb2e20c23fb61150943bfac908308dfd64c41847f9a8311467b7c4161431df72230439ebf1c48650b6fc88c2863b7c4161432ddf4cb08196fb105821cf6fc88c2865b7e7761442dbe38b0a2176f262779136fc22c2885b7d9761442d7f3b90ca16df5c58510b6fb22c2885b7c3261441dbe9930a20edf0c5851076f8e2c2883b7c9261441dbec930a20edf1c9851076fae4c2883afc4161832dbf1130a20eef245840cb5fc88c3065b7e9961441dbe10b0a20edf8cd851076fceec2883dbd639de44dfd2230039efe105801cf7ba42c18e9bf64460473dfc10b003a6fe485801d37f422c00e9bfa2260074df64 else (if i<4 then 0xd238c8c922fc8b5222c84120dc80d200c7f91f7c7c51eac7911e1c76d1b8c6d91b3c6c51aac661191c5dd174c5c916bc595162c581159c54d150c529133c4c512ec451111c41d0fcc3c90ebc3550d2c3410c5c2ed0a4c279097c255092c231085c20d078c18905bc165052c10103dc0dd018c018febbf34fc6bf00fbdbedcfb4beb8fabbe94fa2be70f95be4cf74bdb8f6bbd84f5abd40f4dbd1cf40bce8f33bcb4f2abc90f1dbc5cf10bc28f03bbf4ef6bbd0eedbb9cee0bb68ed7bb44ebebaf0eb5babce98ba48e8fba34e86b9a0e65b98ce60b978e5bb964e56b950e4db91ce40b8e8e33b8b4e22b870e15b83ce0cb828e03b7f4df6b7b0de9b79cde4b788ddfb774ddab760dd1b72cdc4b6f8dbbb6e4db2b6c0da9b68cd9cb658d8fb624d82b5e0d75b5bcd6cb598d63b574d52b530d49b50cd3cb4c8d2bb494d1eb450d0db42cd08b418d03b404cfeb3f0cf9b3dccf4b3b8ce7b394cdeb370cd9b35ccd4b348ccfb334ccab320cc5b30ccc0b2f8cbbb2e4cb6b2d0ca5b23cc78b198c4bb0c4c1ab010be5af8cbe0af18babae64b92ae40b89ae0cb80ade8b73adc4b5ead60b51acfcb34acb8b2baca4b16ac50b0dac0cb00abf8af7abd4aeeabb0ae9ab8cadcab48acbab14aaaaa90aa1aa5ca90aa38a8baa14a7ea9e0a71a9bca68a988a5ba954a4ea910a35a89ca24a888a13a844a0aa8009f5a7bc9eca7a89e3a7849dea7609d1a73c9c8a7089bfa6e49b6a6d09ada6ac9a4a68899fa664976a5c096da59c960a568957a54492aa49091da46c918a45890fa43490aa420905a40c8fca3888dfa3748d2a3308c5a2ec8b4a2c88afa2a48a6a2908a1a26c874a1c886fa19485ea170839a0bc82ca098823a08481ea060811a03c808a0087fb9fd47ee9f807d19edc7b49eb87ab9ea47a29e8079d9e6c7989e4878b9dd476e9db07619d6c7589d4874f9d3474a9d207459cfc7389cc872f9cb47269c807199c4c70c9ba86e79b846de9b606d59b4c6cc9b186c39af46ba9ab06a99a8c6a099f867b99d466a99a0665997c6449908627988461a985060d980c5fc97c85ef97b45e697805c9971c5c496f85b39694596960056d958c55094d851794044ee93604b9928c498923848391e4466916044190bc4188ff83df8f143a68e603898dec36c8d7834b8ce431a8c102ed8b6c2c48ab829789e425e88f022d884c1f087981d386f41ae866017d85ac14c84d811b84040de83500b5827c08481b805780e40168001ff67710611ffb110e908ffd60874847feae620c23ff57210611ffa9908308ffd91173847fec8839c23ff6225d211ffab22e708ffd60973847fea84b9c23ff57650a11ffaa1a8508ffd9dd42847fec8899423ff6440ca11ffa4ba8508ffd1d2110877fc2344287ff64484421ffb3b88508eff8458710bfeae908843ff56460e11ffab13 else (if i<5 then 0x700b708ca780945b84a5b51c02dc25162b14e1241b4f0510df098a4938030a384c1857c04bc252924e016e12927012910621f09c0024e0250c22e131492700632f098885853849c2100d0450201a093041103037c240c0c1062c621b84896282180800342819c24070041450400128402810023422818814127050c2521851c057c2623080105044610008c24612308a040461160f0048c24610423102428a0c8c338460024018a0c0461850910484088c2000a040088087040861430810c2007004086100380252184dc0864a45c28430803824610e080302191309c18b902905c29e008a0400006040000001c189e00e8b85e13001101828508a06218c4481000a020003802199109c1930a2905c29001111442810064211f0428a4170a21430400c08000140c4041101480a2861424411b8fe11c7d1708c321380520b84c00c080018100000860c30636223c5384a281022428a18204b080000012c218114080086143086045022811489e043868582e140210208408011a114082342004851418060208984e014c523c2e14005029028200050231c0378b91c260420c70428df098502181140a4051450510105141000361140f0458a437094001b0f0708b822f84697c1c232b2fe025e1283700a709383844141bc146483898be085e1343c4c5f00d07429e3e36262384b1b111fc24838d888fe12b1c7c4c6f044709e1e262f8214b47c22e0e1170708b83844c71b111e48d888f18a46c447f0949b80948880f0c1f041c50e292be025e1343c7c3700d42c11e1e3e1b821608dc11b170d0709c278d88e11c6c4708e362384657c1c23e02be1187f011f092262e17849071f0dc10b05c270e898b85e128744c5c2f096262e178490c1f041dc258b89e085e129694178b7094398e2e27821784f1f0dc10b05c260e638f86e08582e1446c4708f82362e1a1384c20c7c11b170d09c28e0e1147c5c2f0910e3e2e1784bc097c2386888582e128bc34442c1709a1b80a38481c5e4dc04a45c2786888582e12c4f00745c2f09a1a3f82160b84c1cc70d1fc10b05c280de010e2709c6c40b709e183e083b84b1f0dc10b05c260f0be005e12c4f045c2f094398e3e1a160b84e1cc71f0dc10b05c288f868582e12d92163dd8bd628d86960fd8055f6d7b15e5d76d5ccd7095b7d6b55a2d661591d60d578d5b9563d56554ed511531d47d510d4194fbd3954dad3614cdd2fd4acd279493d21547ad1c1465d15d44cd0f942bd0a541ed031401cfed3f4cf993e3cf753d2cf213c1ceed3b8ced93abcea539ace5138dce1d37ccdd936fcda5362cd71355cd3d348cd0933fccf533acce1331ccbd32ccca9323cc7531acc61311cc2d304cbf92f7cbc52eacb912ddcb6d2d8cb592d3cac52aaca21285c9fd274c9b9267c99525ac941249c8f else 0xa81710b0a0aa030506381a80e1418a3289a2bc9474a34262141368432bc55e5636324181159289a4884d14a2a51a114043308506c618268c21510b898c584298420c6d1330b0a70920c88b7848d6484a383e113186086858385384bc1c22021f0883197846d23507c240c4e251b45289a238946182a2a8a910a32885088b465e4a20c6fe11863592709005a5e21a0c28e12310a088c31e10c8e25183842c6182630c147862c200540a880182a4a3a8095859434b502e00a587803c21850f007803c01e00800000a8400025852c2007007803c21e10f087803c210c08b04000018c5a1b8222160b851c018984e015888582e140380229162e00f004009c2202e01700783845c21e1080104182e02316e120380304000a04303081840803821cc71f0dc10b05c2800000a1c9e08be124204318e27822f84c000404302000a052020030875347d17094002b24832f25e13020f80405c0202e0170061380522384a00048a081050506565e4bc25140860400160c10410a36289e08b14e128d841c011b142de12038025b07c04a2845c271b8ba2e1214f00a16c77098a780b4886c3b84e4c14308040200e08038201708b040c62d0d110b05c2713082158c4c61434e1010c2861120898458200e08b043830a1120a1853822e100d04382c61830818c31b111ec6400a058c2291b111fc251408010618f898de08863e1380000000007007803c01e00f00784285c02e00f007802007007803c0148e0100000000007007803c01e00801c0107007803c01e00f007803c0148e01003820830803830a3420e081382261434e10e061421c1a012109840000000000000e0c18404a10)))))
def f1519l9 : Packing := (625,3,5,0,0,14,0,f1519d9)
def f1519d10 (i : Nat) : Nat := (if i<1 then 0x18ed73a4ce5d3864de336b4d7e3520d2733c4cb431dcc332fbcbc02e28b622c94af62b1ca9f2988a3328109ce266098525c893524348de22d888e21608141f787a81e0074a1c186de1abc672192860617405af15e453514184de12d8495119843710203d20e8c3740d1431d0b9c2b80a5c26808e421107881ba05bc140047c0f703740ae01fc0500084000ffc8750bff61942ffd7450bff61d42ffc211d3ff88874ffe111d3ff60d42ffd7150bff1c542ffd6150bff20542ffd7350bff5c942ffd8150bff48474ffd825d3ff20974ffd815d3ff58d74ffe445cfff84573ffd835d3ff20574ffe885d3ff88974ffe115d3ff08574ffd415d3ff4c574ffd215d3ff5c943ffd4250fff60543ffd8250fff61943ffd7650fff5d143ffc8150fff48543ffe8850fff84543ffd3150fff5c543ffd6150fff50543ffd8750fff9dd42ffe1150bff5c532ffe8850bff50542ffd3150bff48542ffd414cbff1c442ffe7710bff84442ffd7110bff10532ffe444cbff84532ffc31913ff48644ffd31913ff5c644ffc71913ff88a44ffe11913ff8ce44ffc21913ff9de44ffc410cbff50622ffd744cbff1c441ffc31107ff10421ffc32913ff10633ffc4188bff88a11ffe1158fff50573ffe441cfff10473ffd615cfff59173ffd4158fff10573ffd215cffd88a11fec8488bfd10e11ff582847fd50e11ff633847fd91211ff532847fd0ca11ff542847fd10a11ff463846ff61031bfe8850fef91143bfd87107fb1d222bfd83107f70c543fde3350ffd5ce11ff473847fd58e11ff583847fd61211ff574847fd1d211fbc82913ef58e44fbd31913ef0c644fbc21913ef5ce44fbd21913ef1ce44fbc81913ef1ca44fbd32913ef58a44fbd61913ef5ca44fbd71913ef1c644fed4188bfb20622fed3188bfb10622fbc32913fb5d222fed4388bfb5ce22fbd76913ef21e44fbe77913ef20e44fbe33913fb91222fbe22913fb84622bfd82107ef50644fed7250aff20644fbd6450aff61d42efc8650bf75da33bfc8150aff20633bfe8850bef91142fdd318cffd84421bfd84087ef10542fdd618ceffa2174fbe445d3f75c633bfc815d3f750a33fdc818ceff61073fdd748cff710633fdc848cff759233fdd418cff75ca33bfd821d3fb88942fde448cfef5d143fdd7350ff748633bfd8750eff61943fdd6350ff70c943fde118ceff20543bfd840caff60943fbd4250ffd10611bfd82846ff60e11ff431846ff61d32fed724caff61211bfd8710bef84644fed2188aff20622fd6118cf779de33fce228cfed84644ede668cfe791233fae22912bf21941bf9800cabf61873bbd841cedf61473bf5810ca7f61c32b7d85106bf61832bbd840cadf61432bed821cedf61431afc8650adf61442dbe77913f984622bf9801d2fe60073bf5811cef760c74bf5811d2fb60874 else (if i<2 then 0x5eaf00e369709cd295aa0722c05b0a51435b8142fc2786b57a8c25c094426468b09e46046af0954a4c0951e13485eaf0254784f21325c0891e13c846bf0914a4c095123c2710a55a34b84ca7025443709a4264aa51a2c2791815a34b84d2302b469b0994e04a886a44785121225528b023c2849812a2528f09e42f46a7095486c115423c2753814060b84ca45e050151e13c25b81423c2610bd3604a8d16142452a30454784ea700b46170985a35f849812a246370986af46a70964245e894e13085ead1a5c2690bd5e04b84ca56e08aa30994c84d812a2c278d811c5c25138128d110f09d48dc095123c2712214e0905309c189c01410d108f0a700b0c34c61304c014194c26c02c80d281b09c7e0508c5e1309098014511091e148f16230051d84e242608b22103298532704584361e138f17814054784e0e345c10b0984e00c14143c27c0351e1229c0a05a44784e124c8c014103c2892370088b0a1e140f49814221ca51e148808241e00a091e14a9c02c2a3c261e2f0280a3b09c48b0a3b09520f52a302247851156e0508f09858f0a8d461360168d6e128e522f022508f0a05a80a8c7e130d103c194c2693824060b0f09d4c55b81128c271f8443f08948bc0a02a247850107820784a2700d160f09a4e01a2f09530f1c8b09474f97811c5c271213005100c123c291e1b005043b09c4e0160c294c27c02c29bc2506396e0505b09c10908212e0068b0a700e4a0f0941af57812e130f178040506530a058f0a53094409098028206a30a43600a20103c279b811e12290d814054784e0c488c018282478528e7cbc1170987cbc11709678b4d830951cdc18493f02d171709944f97822e132b909b025c26c034586061309c38f0d8010e30b138028ec26122f0051d84c245851d84a0c786c01416138f0d8010ec2640361e12061f8010ec261e1b0021d84c3c3021d84a245e00a3b09878b0b0f09468b0d8244584402615110c20282c269b817e122397822e128d103c61c48bc01471818917802e130f1237008c26063440f1d84c3440fc24944e500939a4cc92e64a691de45d90f2430905a4038fc23c88eba39b8e223838da634f8cd62f88bb22e78b522c88a2e27f89962598936241889e20d87ea1ee87a61c886f21a9865a15284fe12c844a0f883b20d9820206d814e039807e0057fadfd87f15f887dd5f697d59f127bfdeec7b65ec67acdea0798de5078f5e2a785ddfd77c5dde772ddb87695d9275e1d3473f9ce47345cbe72adc9f7215c797199c226fcdbbd6dc9b356bfdac26a4da5667d99b9660d95b64798e162ad87c611981e5fbd7c05e617705ce96f65b01698598963a582d5d5567d57e552151953a94b4521545650653dc4e9937e4d213194b8d2b449dd24148491f1470919a45ad13c44350de42a108041290143f78f9a3dacf3c3c else 0x8086282123410c305283440c521108a4d9e8e46130b0a50640405464521082118c41412f16212184052850c4118e42310d1e200d1e8c6ac2051cf501466e7c997811c5c281e1048922441c05214d913d1e14220891a8c68c28c21422c28218f168c62c28858403c4851040a10a8c516408d8e9f2f04847170a4423105462101518c5854631e15208524818365236091151c2c2c8a8c50a41418d048c62c423186108c61a2a31c22c2530848cb46c1222c2c288a8c5142a228a5949f1b045470b0a6425148462908c5211894c8148442931614dc1211e14484a290884a640818e146848c71432018928314206290944a07094422c352930282c961a2c29973f04d471709e78b463511440c70a7a312d0cb088c6a033d1894a82d0d3604a8b0a70060a8d46130e5eaf0284b84ea4aa8560f0144a8b0a968e5ea15e04b850a072f57812e13a94a8a1adc0a30a21afc0ad2e130e86bd3604a8b0a21a930b4dab289b0284a8b0b4b434d812a845850397e05a912e138b1e161e12890982445040f0a24e08a34442878503700504221e13825abd1a8c261380688050f09c58f0a8f0945c81e161e13435eaf025c261ca55a5c255eb702bc25))
def f1519l10 : Packing := (236,2,5,0,0,14,0,f1519d10)
def f1519d11 (i : Nat) : Nat := 0x83cb8050e139e5c0287098d8080e128678d01c142724508d80e20385249058d00a1070a492068050a13a07401c2520f2e014e84e3402841c2624508d80884e1925c070b09c33e034b16138659e2c2508336020f84e19a79109433e03453a139269618d0102850a833cb1a014285018d01028509c33cb80814e8506867970102c280e084658d00b094d82119e5c02c2589f09a01bd4732d7997b0c5baad142a5644e810ea9b2306508868de1521d02e83a046003fe98ffc31ff883ff0cbfea0ffd21ffc45ff847ff19ffc21ffc89ff1cffeb1ffd73ffae9ff1d3fe31ffd42ffa65ff10bfe21ffd43fec23fb88bdf227de33
def f1519l11 : Packing := (26,1,5,0,0,11,0,f1519d11)
def f1519d12 (i : Nat) : Nat := 0x22ff
def f1519l12 : Packing := (1,0,5,0,0,0,0,f1519d12)
def f1519samples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd907c00e4ea200c057e0d20098c81000270804c69bc44931123ca01090240000b91666314955400a2804412c9204581f0c8178a520a61b6c00115,0x510002844e0000004fe0001098cb00d9240c055c1be013f01038800098209108b916601049040000000410289004781b850168842005116000011),(0x47a8dfc3ee01cc6f4803017a07fb02f81a07313dbe3303f0b213a63f8947b5ef7fa6f197c499caf521a1334ef85ffb9f9d32360a4c81906810070,0x579fd6c7eff7782fcfffcf13ffff76f9ff3dff7cffff1bf8bb3fef3f9b7c9dcfbd97f19fcfbffdfbcfdf116bf8dffb9fdd337ece6c859168f0371),(0x62e00fbb930d2523081c3c187843e78702103818583a14d405a85a400c0668c9644ce00e841af11391aa00c0980bd788813290525e09e050b0262,0x41080043c00638230c200c125041540000013058d0220a900020402400000cc03004000e0110f953810a0000d00a9188993230424000804030260),(0x13700180a8608038ebe200c1fb80803b703559842611e0f3341016232447c19c6ca3cc1f745f84081479ec882903fa60030c008acc215100130a0,0x28b06080240087cc92030124ab800237784488a02045e16476100803510e42048d89c0913e2e042814302c1828216a40020c00088c2d59a200080),(0,0),(0x560d043f21643f5e0014136033c0044b6a288c5e18a2100cb51a09c218006601f84101d588182f47b12051f9ef406161c293100018010fd3cc10,0x2b80150200eb81f80013e20022470041201b880600220002f030100451206f40688800d16c980305a100816085802041a28104141c0209d30400),(0x18203044541a0f0000840064310800184092281021a3ca00134100c23812030c0589c422200d0142109a0044070085604206008150040240008,0x1194846400780f48468000603104201200b22030b303f020034100810c14831d05c1940681881140900002a8078194400004000800000800000),(0x7c801e4100014416820029ab05ff0ab8516226322a02c40840c000c929c06063808030608084402480800441006801e8a0988804000080800c440,0x3802200008014400108a0149059a03ba41ce07240f00c00c10d0300318c0600300103d00a00400000084044801200062208488001000060008000),(0x800042d888809240300d586c24078c88545395e610220b887842782c195160272038290003ad10541321261902861127647382000000103880,0x4504002b9801000001100059044281c8848845190e00000300c480f002c0090020220062801060c00101122051000021045203322212800002000)]
def f1519columns : IndexTree ColumnInfo := (.fork 14 (.fork 7 (.fork 3 (.leaf [(64,0,1455,0,11),(1,0,1518,0,11),(4,0,1515,0,9)]) (.leaf [(0,2,493,0,9),(129,0,1390,0,8),(12,0,1507,0,8),(132,0,1387,0,8)])) (.fork 3 (.leaf [(9,0,1510,0,8),(33,0,1486,0,8),(320,0,1199,0,8)]) (.leaf [(1,2,492,0,8),(140,0,1379,0,7),(2,0,424,69,7),(161,0,1358,0,7)]))) (.fork 7 (.fork 3 (.leaf [(8,2,485,0,7),(328,0,1191,0,7),(128,2,365,0,7)]) (.leaf [(68,0,1451,0,7),(66,0,424,5,6),(0,66,173,256,6),(0,6,353,136,6)])) (.fork 4 (.leaf [(4,2,489,0,6),(6,0,424,65,6),(256,66,173,0,5),(128,6,353,8,5)]) (.leaf [(128,3,332,32,5),(32,3,460,0,5),(8,6,353,128,5),(264,66,165,0,4)]))))
def f1519autos : Array (List Nat) := #[[],[96,115,133]]
def f1519levels : Nat → Packing
  | 7 => f1519l7
  | 8 => f1519l8
  | 9 => f1519l9
  | 10 => f1519l10
  | 11 => f1519l11
  | 12 => f1519l12
  | _ => emptyPacking
def f1519index : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 5 3 5 1 0 (keyf1519l8)
  | 9 => lookupWord 124 557 10 13 8 1 (keyf1519l9)
  | 10 => lookupWord 390 2337 12 15 10 1 (keyf1519l10)
  | 11 => lookupWord 143 857 10 13 8 1 (keyf1519l11)
  | 12 => lookupWord 15 109 7 10 5 1 (keyf1519l12)
  | _ => fun _ => none
def f1519 : Forest := ⟨1519,12,fun j => f1519samples[j]?.getD (0,0),f1519columns,f1519autos,f1519levels,f1519index⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geomf1519 : graphValid f1519 (boundsBefore knownPrev_f1519) = true := by
  unfold graphValid
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel, by decide +kernel⟩, ?_⟩, by decide +kernel⟩
  apply listPieces_all (d:=3)
  simp only [listPieces,IndexTree.values,List.length_append,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceDiv,List.take,List.drop]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf1519_7_0 : block f1519 7 0 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem blf1519_7 : block f1519 7 0 2 = true := sf1519_7_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf1519_8_0 : block f1519 8 0 32=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf1519_8_32 : block f1519 8 32 32=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf1519_8_64 : block f1519 8 64 32=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf1519_8_96 : block f1519 8 96 32=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf1519_8_128 : block f1519 8 128 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf1519_8_132 : block f1519 8 132 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf1519_8_164 : block f1519 8 164 27=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem blf1519_8 : block f1519 8 0 191 = true := (@block_merge f1519 8 0 164 27 (@block_merge f1519 8 0 132 32 (@block_merge f1519 8 0 128 4 (@block_merge f1519 8 0 96 32 (@block_merge f1519 8 0 64 32 (@block_merge f1519 8 0 32 32 sf1519_8_0 sf1519_8_32) sf1519_8_64) sf1519_8_96) sf1519_8_128) sf1519_8_132) sf1519_8_164)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf1519_9_0 : block f1519 9 0 32=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf1519_9_32 : block f1519 9 32 32=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf1519_9_64 : block f1519 9 64 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf1519_9_68 : block f1519 9 68 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf1519_9_100 : block f1519 9 100 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf1519_9_132 : block f1519 9 132 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf1519_9_164 : block f1519 9 164 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf1519_9_196 : block f1519 9 196 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf1519_9_228 : block f1519 9 228 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf1519_9_260 : block f1519 9 260 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf1519_9_292 : block f1519 9 292 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf1519_9_324 : block f1519 9 324 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf1519_9_356 : block f1519 9 356 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf1519_9_388 : block f1519 9 388 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf1519_9_420 : block f1519 9 420 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf1519_9_452 : block f1519 9 452 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf1519_9_484 : block f1519 9 484 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf1519_9_516 : block f1519 9 516 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf1519_9_548 : block f1519 9 548 9=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf1519_9_557 : block f1519 9 557 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf1519_9_589 : block f1519 9 589 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf1519_9_621 : block f1519 9 621 4=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem blf1519_9 : block f1519 9 0 625 = true := (@block_merge f1519 9 0 621 4 (@block_merge f1519 9 0 589 32 (@block_merge f1519 9 0 557 32 (@block_merge f1519 9 0 548 9 (@block_merge f1519 9 0 516 32 (@block_merge f1519 9 0 484 32 (@block_merge f1519 9 0 452 32 (@block_merge f1519 9 0 420 32 (@block_merge f1519 9 0 388 32 (@block_merge f1519 9 0 356 32 (@block_merge f1519 9 0 324 32 (@block_merge f1519 9 0 292 32 (@block_merge f1519 9 0 260 32 (@block_merge f1519 9 0 228 32 (@block_merge f1519 9 0 196 32 (@block_merge f1519 9 0 164 32 (@block_merge f1519 9 0 132 32 (@block_merge f1519 9 0 100 32 (@block_merge f1519 9 0 68 32 (@block_merge f1519 9 0 64 4 (@block_merge f1519 9 0 32 32 sf1519_9_0 sf1519_9_32) sf1519_9_64) sf1519_9_68) sf1519_9_100) sf1519_9_132) sf1519_9_164) sf1519_9_196) sf1519_9_228) sf1519_9_260) sf1519_9_292) sf1519_9_324) sf1519_9_356) sf1519_9_388) sf1519_9_420) sf1519_9_452) sf1519_9_484) sf1519_9_516) sf1519_9_548) sf1519_9_557) sf1519_9_589) sf1519_9_621)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf1519_10_0 : block f1519 10 0 30=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf1519_10_30 : block f1519 10 30 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf1519_10_62 : block f1519 10 62 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf1519_10_94 : block f1519 10 94 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf1519_10_126 : block f1519 10 126 19=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf1519_10_145 : block f1519 10 145 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf1519_10_177 : block f1519 10 177 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf1519_10_209 : block f1519 10 209 27=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem blf1519_10 : block f1519 10 0 236 = true := (@block_merge f1519 10 0 209 27 (@block_merge f1519 10 0 177 32 (@block_merge f1519 10 0 145 32 (@block_merge f1519 10 0 126 19 (@block_merge f1519 10 0 94 32 (@block_merge f1519 10 0 62 32 (@block_merge f1519 10 0 30 32 sf1519_10_0 sf1519_10_30) sf1519_10_62) sf1519_10_94) sf1519_10_126) sf1519_10_145) sf1519_10_177) sf1519_10_209)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf1519_11_0 : block f1519 11 0 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf1519_11_4 : block f1519 11 4 22=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem blf1519_11 : block f1519 11 0 26 = true := (@block_merge f1519 11 0 4 22 sf1519_11_0 sf1519_11_4)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf1519_12_0 : block f1519 12 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem blf1519_12 : block f1519 12 0 1 = true := sf1519_12_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tablesf1519 : checkedTables f1519 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block f1519 0 0 0 = true)
  · exact (rfl : block f1519 1 0 0 = true)
  · exact (rfl : block f1519 2 0 0 = true)
  · exact (rfl : block f1519 3 0 0 = true)
  · exact (rfl : block f1519 4 0 0 = true)
  · exact (rfl : block f1519 5 0 0 = true)
  · exact (rfl : block f1519 6 0 0 = true)
  · exact blf1519_7
  · exact blf1519_8
  · exact blf1519_9
  · exact blf1519_10
  · exact blf1519_11
  · exact blf1519_12

-- ============================================================================
-- Bridge proof for L-meta-3406
-- ============================================================================

def or04 : Sig := bin true (inputs.getD 0 zero) (inputs.getD 4 zero)

def flipMove (j : Nat) : Move :=
  (neg (inputs.getD j zero), inputs.getD j zero, Fin.ofNat 512 (1 <<< j))

def vars495Flip (k : Nat) : List Sig :=
  vars (495 ^^^ (1 <<< k)) ++ [neg (inputs.getD k zero)]

def initWires (k : Nat) : List Sig :=
  inputs ++ [or04, neg ((inputs ++ [or04]).getD k zero)]

theorem nodup_pair {a b : Sig} (h : (a != b) = true) : [a, b].Nodup := by
  simp only [bne_iff_ne] at h
  simp [h]

theorem nodup_triple {a b c : Sig} (h : ((a != b) && (a != c) && (b != c)) = true) :
    [a, b, c].Nodup := by
  simp only [Bool.and_eq_true, bne_iff_ne] at h
  simp [h.1.1, h.1.2, h.2]

theorem mem_pair_of {α : Type} {a b : α} {S : Finset α} (ha : a ∈ S) (hb : b ∈ S) :
    ∀ x ∈ [a, b], x ∈ S := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ha
  · exact hb

theorem mem_triple_of {α : Type} {a b c : α} {S : Finset α} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) :
    ∀ x ∈ [a, b, c], x ∈ S := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact ha
  · exact hb
  · exact hc

theorem live_slice_contra {T G : Sig} {k t : Nat} {S : Finset Sig} {other : List Sig} {L : Nat}
    (run : Live T k t S) (ms : List Move) (singles : List Sig)
    (pG : proper G) (hL : Lower other G L)
    (hT : movedWord ms T = G)
    (hcov : ∀ a ∈ S, freeWord other (movedWord ms a) = true)
    (hsub : ∀ a ∈ singles, a ∈ S)
    (hnd : singles.Nodup)
    (hconst : ∀ a ∈ singles, movedWord ms a = zero ∨ movedWord ms a = one)
    (hcap : k < L + singles.length) : False := by
  classical
  let sfin : Finset Sig := singles.toFinset
  have subS : sfin ⊆ S := fun a ha => hsub a (List.mem_toFinset.mp ha)
  let front := sfin.toList ++ (S \ sfin).toList
  have nd : front.Nodup := by
    simp only [front, List.nodup_append]
    refine ⟨Finset.nodup_toList _, Finset.nodup_toList _, ?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset = S := by
    ext a; simp [front, Finset.union_sdiff_of_subset subS]
  have run' := list_run run front nd fe
  let r := movedRow ms
  have eqR : rename r T = G := (moved_eq_rename ms T).symm.trans hT
  have gc : restrictRows r (observe T) = observe G := (observe_rename _ _).symm.trans (congrArg observe eqR)
  have supp : supply (other.map observe) ((front.map observe).map (restrictRows r)) := by
    intro v hv
    obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv
    obtain ⟨a, hmem, rfl⟩ := List.mem_map.mp hm
    rw [← observe_rename, ← moved_eq_rename ms a]
    exact freeWord_ok (hcov a (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp (L := L) (gc ▸ hL)
  have massLo : sfin.card ≤ mass ((front.map observe).map (restrictRows r)) := by
    simp only [front, List.map_append, mass_append]
    let xs := (sfin.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv
      obtain ⟨a, hmem, rfl⟩ := List.mem_map.mp hm
      rw [← observe_rename, ← moved_eq_rename ms a]
      rcases hconst a (List.mem_toFinset.mp (Finset.mem_toList.mp hmem)) with hz | ho
      · rw [hz]; exact ⟨false, funext bit_zero⟩
      · rw [ho]; exact ⟨true, funext bit_one⟩
    have sz := mass_constants xs only
    simp only [xs, List.length_map, Finset.length_toList] at sz
    change sfin.card ≤ mass xs + _
    rw [sz]
    omega
  have scard : sfin.card = singles.length := List.toFinset_card_of_nodup hnd
  omega

theorem reach_from_bank {R} {base ext : List (Wire R)} {p0 p : Nat} {bank : List (Wire R)}
    (h0 : Reach base p0 ext) (h1 : Reach ext p bank) :
    ∃ bank', Reach base (p0 + p) bank' ∧ ∀ v ∈ bank, Available bank' v := by
  induction h1 with
  | start => exact ⟨ext, by simpa using h0, fun v hv => Or.inl hv⟩
  | @one p' ws a _ ha ih =>
    obtain ⟨b', hr', hsub⟩ := ih
    have ha' : Available b' a := ha.elim (hsub a) Or.inr
    refine ⟨inv a :: b', by simpa [Nat.add_assoc] using Reach.one hr' ha', fun v hv => ?_⟩
    rcases List.mem_cons.mp hv with rfl | hm
    · exact Or.inl (List.mem_cons_self ..)
    · exact available_cons _ (hsub v hm)
  | @two p' ws a b d _ ha hb ih =>
    obtain ⟨b', hr', hsub⟩ := ih
    have ha' : Available b' a := ha.elim (hsub a) Or.inr
    have hb' : Available b' b := hb.elim (hsub b) Or.inr
    refine ⟨combine d a b :: b', by simpa [Nat.add_assoc] using Reach.two d hr' ha' hb', fun v hv => ?_⟩
    rcases List.mem_cons.mp hv with rfl | hm
    · exact Or.inl (List.mem_cons_self ..)
    · exact available_cons _ (hsub v hm)

theorem reach_perm {R} {xs ys : List (Wire R)} {q : Nat} {bk : List (Wire R)}
    (hp : xs.Perm ys) (hq : Reach xs q bk) :
    ∃ bk', Reach ys q bk' ∧ ∀ v ∈ bk, Available bk' v := by
  induction hq with
  | start => exact ⟨ys, Reach.start, fun v hv => Or.inl (hp.subset hv)⟩
  | @one q' ws u _ hu ih =>
    obtain ⟨b', hr', hs⟩ := ih
    have hu' : Available b' u := hu.elim (hs u) Or.inr
    refine ⟨inv u :: b', Reach.one hr' hu', fun v hv => ?_⟩
    rcases List.mem_cons.mp hv with rfl | hm
    · exact Or.inl (List.mem_cons_self ..)
    · exact available_cons _ (hs v hm)
  | @two q' ws u w dd _ hu hw ih =>
    obtain ⟨b', hr', hs⟩ := ih
    have hu' : Available b' u := hu.elim (hs u) Or.inr
    have hw' : Available b' w := hw.elim (hs w) Or.inr
    refine ⟨combine dd u w :: b', Reach.two dd hr' hu' hw', fun v hv => ?_⟩
    rcases List.mem_cons.mp hv with rfl | hm
    · exact Or.inl (List.mem_cons_self ..)
    · exact available_cons _ (hs v hm)

theorem lower_add_bin {roots : List Sig} {T a b : Sig} {d : Bool} {L : Nat}
    (ha : a ∈ roots) (hb : b ∈ roots) (hL : Lower roots T (L + 1)) :
    Lower (roots ++ [bin d a b]) T L := by
  intro p bank hr hT
  have h1 : Reach (roots.map observe) 1 (observe (bin d a b) :: roots.map observe) := by
    rw [obs_bin]
    exact Reach.two d Reach.start (Or.inl (List.mem_map_of_mem ha)) (Or.inl (List.mem_map_of_mem hb))
  have hperm : ((roots ++ [bin d a b]).map observe).Perm (observe (bin d a b) :: roots.map observe) := by
    rw [List.map_append, List.map_singleton]
    exact List.perm_append_singleton _ _
  obtain ⟨bk1, hr1, hs1⟩ := reach_perm hperm hr
  obtain ⟨bk2, hr2, hs2⟩ := reach_from_bank h1 hr1
  have hT2 : Available bk2 (observe T) := by
    rcases hT with hm | hc
    · rcases hs1 _ hm with hm1 | hc1
      · exact hs2 _ hm1
      · exact Or.inr hc1
    · exact Or.inr hc
  have hbd := hL (1 + p) bk2 hr2 hT2
  omega

-- Lower bounds from f509, f507, f1519, and low895:
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem f509_imp : Impossible (graphGoal 509) 11 (vars 509 ++ [or04]).toFinset := by
  have noRun := root_index (g := f509) (before_sound known383_ext valid383_ext) geomf509 tablesf509
    (k := 11) (by decide) (i := 0) (ws := vars 509 ++ [or04]) (by decide +kernel)
  have tgt : targetOf f509 = graphGoal 509 := by decide +kernel
  exact tgt ▸ noRun

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem f507_imp : Impossible (graphGoal 507) 11 (vars 507 ++ [or04]).toFinset := by
  have noRun := root_index (g := f507) (before_sound known383_ext valid383_ext) geomf507 tablesf507
    (k := 11) (by decide) (i := 0) (ws := vars 507 ++ [or04]) (by decide +kernel)
  have tgt : targetOf f507 = graphGoal 507 := by decide +kernel
  exact tgt ▸ noRun

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem f1519_imp : Impossible (graphGoal 1519) 12 (vars 1519).toFinset := by
  have noRun := root_index (g := f1519) (before_sound known1519_all valid1519_all) geomf1519 tablesf1519
    (k := 12) (by decide) (i := 0) (ws := vars 1519) (by decide +kernel)
  have tgt : targetOf f1519 = graphGoal 1519 := by decide +kernel
  exact tgt ▸ noRun

def ess509or : List (Sig × Row × Row) :=
  [(inputs.getD 0 zero, Fin.ofNat 512 16, Fin.ofNat 512 17),
   (inputs.getD 2 zero, Fin.ofNat 512 8, Fin.ofNat 512 12),
   (inputs.getD 3 zero, Fin.ofNat 512 4, Fin.ofNat 512 12),
   (inputs.getD 4 zero, Fin.ofNat 512 1, Fin.ofNat 512 17),
   (inputs.getD 5 zero, Fin.ofNat 512 1, Fin.ofNat 512 33),
   (inputs.getD 6 zero, Fin.ofNat 512 256, Fin.ofNat 512 320),
   (inputs.getD 7 zero, Fin.ofNat 512 4, Fin.ofNat 512 132),
   (inputs.getD 8 zero, Fin.ofNat 512 8, Fin.ofNat 512 264)]

def ess507or : List (Sig × Row × Row) :=
  [(inputs.getD 0 zero, Fin.ofNat 512 16, Fin.ofNat 512 17),
   (inputs.getD 1 zero, Fin.ofNat 512 1, Fin.ofNat 512 3),
   (inputs.getD 3 zero, Fin.ofNat 512 16, Fin.ofNat 512 24),
   (inputs.getD 4 zero, Fin.ofNat 512 1, Fin.ofNat 512 17),
   (inputs.getD 5 zero, Fin.ofNat 512 1, Fin.ofNat 512 33),
   (inputs.getD 6 zero, Fin.ofNat 512 2, Fin.ofNat 512 66),
   (inputs.getD 7 zero, Fin.ofNat 512 32, Fin.ofNat 512 160),
   (inputs.getD 8 zero, Fin.ofNat 512 8, Fin.ofNat 512 264)]

def ess1519 : List (Sig × Row × Row) :=
  [(inputs.getD 0 zero, Fin.ofNat 512 0, Fin.ofNat 512 1),
   (inputs.getD 1 zero, Fin.ofNat 512 1, Fin.ofNat 512 3),
   (inputs.getD 2 zero, Fin.ofNat 512 0, Fin.ofNat 512 4),
   (inputs.getD 3 zero, Fin.ofNat 512 6, Fin.ofNat 512 14),
   (inputs.getD 5 zero, Fin.ofNat 512 3, Fin.ofNat 512 35),
   (inputs.getD 6 zero, Fin.ofNat 512 0, Fin.ofNat 512 64),
   (inputs.getD 7 zero, Fin.ofNat 512 6, Fin.ofNat 512 134),
   (inputs.getD 8 zero, Fin.ofNat 512 8, Fin.ofNat 512 264)]

theorem lower_with_extra {roots : List Sig} {extra T : Sig} {L : Nat}
    (pT : proper T) (hBase : Lower roots T L)
    (hImp : Impossible T (L - 1) (roots ++ [extra]).toFinset)
    (hPos : 1 ≤ L)
    (hEss : ∀ a ∈ roots, Essential T (roots ++ [extra]) a) :
    Lower (roots ++ [extra]) T L := by
  intro p bank hr ha
  obtain ⟨k, t, S, hk, run, sub⟩ := reach_live pT hr ha
  by_cases hex : extra ∈ S
  · have he : (roots ++ [extra]).toFinset = S := by
      ext a
      rw [List.mem_toFinset]
      refine ⟨fun hm => ?_, sub a⟩
      rcases List.mem_append.mp hm with hv | ho
      · obtain ⟨r, s, hd, iso⟩ := hEss a hv
        exact raw_required run (roots ++ [extra]) a sub r s hd iso
      · rcases List.mem_singleton.mp ho with rfl; exact hex
    by_contra! small
    exact hImp k t (by omega) (he.symm ▸ run)
  · have sub' : ∀ v ∈ S, v ∈ roots := fun v hv => by
      rcases List.mem_append.mp (sub v hv) with h1 | h2
      · exact h1
      · exact False.elim (hex (List.mem_singleton.mp h2 ▸ hv))
    have run' := list_run run S.toList (Finset.nodup_toList S) (by simp)
    have supp : supply (roots.map observe) ((S.toList.map observe).map (restrictRows id)) := by
      intro v hv
      obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
      exact Or.inl (List.mem_map_of_mem (sub' a (Finset.mem_toList.mp ha)))
    have hbd := projected_bound id run' (observe_proper pT) Reach.start supp (L := L) hBase
    omega

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lower_509_or : Lower (vars 509 ++ [or04]) (graphGoal 509) 12 := by
  refine lower_with_extra (proper_of _ (by decide +kernel))
    (known_at valid383 509 12 (by decide +kernel)) f509_imp (by decide) ?_
  have he := essential_ok (T := graphGoal 509) (raw := vars 509 ++ [or04]) (xs := ess509or) (by decide +kernel)
  have hm : (ess509or.map Prod.fst) = vars 509 := by decide +kernel
  intro a ha
  exact he a (List.mem_toFinset.mpr (hm.symm ▸ ha))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lower_507_or : Lower (vars 507 ++ [or04]) (graphGoal 507) 12 := by
  refine lower_with_extra (proper_of _ (by decide +kernel))
    (known_at valid383 507 12 (by decide +kernel)) f507_imp (by decide) ?_
  have he := essential_ok (T := graphGoal 507) (raw := vars 507 ++ [or04]) (xs := ess507or) (by decide +kernel)
  have hm : (ess507or.map Prod.fst) = vars 507 := by decide +kernel
  intro a ha
  exact he a (List.mem_toFinset.mpr (hm.symm ▸ ha))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1519 : Lower (vars 1519) (graphGoal 1519) 13 := by
  refine lower_impossible (proper_of _ (by decide +kernel)) ?_ f1519_imp
  have he := essential_ok (T := graphGoal 1519) (raw := vars 1519) (xs := ess1519) (by decide +kernel)
  have hm : (ess1519.map Prod.fst) = vars 1519 := by decide +kernel
  intro a ha
  exact he a (List.mem_toFinset.mpr (hm.symm ▸ ha))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low495_flip0 : Lower (vars495Flip 0) (graphGoal 495) 13 :=
  lower_map (ms := [64,65,66,99,116,101].map swapRows ++ [flipMove 0])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low895

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low495_flip1 : Lower (vars495Flip 1) (graphGoal 495) 13 :=
  lower_map (ms := [flipMove 1])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low1519

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low495_flip2 : Lower (vars495Flip 2) (graphGoal 495) 13 :=
  lower_map (ms := [48,33,133,118].map swapRows ++ [flipMove 2])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low1519

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low495_flip3 : Lower (vars495Flip 3) (graphGoal 495) 13 :=
  lower_map (ms := [96,98,67,116,133,135].map swapRows ++ [flipMove 3])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low895

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low495_flip6 : Lower (vars495Flip 6) (graphGoal 495) 13 :=
  lower_map (ms := [32,49,130,83,116,118].map swapRows ++ [flipMove 6])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low895

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lower_447_or : Lower (vars 447 ++ [or04]) (graphGoal 447) 12 :=
  lower_add_bin (a := inputs.getD 0 zero) (b := inputs.getD 4 zero) (d := true)
    (by decide +kernel) (by decide +kernel) (known_at valid383 447 13 (by decide +kernel))

-- Helper: no Live run of length <= 13 from S subset of (inputs ++ [or04])
theorem no_or04_only {k t : Nat} {S : Finset Sig}
    (hk : k ≤ 13) (run : Live graph k t S) (sub : ∀ a ∈ S, a ∈ inputs ++ [or04]) : False := by
  have hx4 : inputs.getD 4 zero ∈ S := by
    have he := witnessB_sound (T := graph) (roots := inputs ++ [or04]) (a := inputs.getD 4 zero)
      (rs := (Fin.ofNat 512 1, Fin.ofNat 512 17)) (by decide +kernel)
    obtain ⟨r, s, hd, iso⟩ := he
    exact raw_required run (inputs ++ [or04]) _ sub r s hd iso
  have hcov : ∀ a ∈ S, freeWord (vars 495) (movedWord (fixRows 16 0) a) = true := by
    have hall : (inputs ++ [or04]).all (fun a => freeWord (vars 495) (movedWord (fixRows 16 0) a)) = true := by
      decide +kernel
    exact fun a ha => List.all_eq_true.mp hall a (sub a ha)
  exact live_slice_contra run (fixRows 16 0) [inputs.getD 4 zero]
    (proper_of _ (by decide +kernel)) (known_at valid383 495 13 (by decide +kernel))
    (by decide +kernel) hcov (by simpa using hx4) (by simp)
    (fun a ha => by rcases List.mem_singleton.mp ha with rfl; left; decide +kernel)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem req_x4 {j : Nat} {k t : Nat} {S : Finset Sig}
    (run : Live graph k t S) (sub : ∀ a ∈ S, a ∈ initWires j)
    (hw : witnessB graph (initWires j) (inputs.getD 4 zero) (Fin.ofNat 512 1, Fin.ofNat 512 17) = true) :
    inputs.getD 4 zero ∈ S := by
  obtain ⟨r, s, hd, iso⟩ := witnessB_sound hw
  exact raw_required run (initWires j) _ sub r s hd iso

theorem req_x0 {j : Nat} {k t : Nat} {S : Finset Sig}
    (run : Live graph k t S) (sub : ∀ a ∈ S, a ∈ initWires j)
    (hw : witnessB graph (initWires j) (inputs.getD 0 zero) (Fin.ofNat 512 16, Fin.ofNat 512 17) = true) :
    inputs.getD 0 zero ∈ S := by
  obtain ⟨r, s, hd, iso⟩ := witnessB_sound hw
  exact raw_required run (initWires j) _ sub r s hd iso

theorem drop_nk {j : Nat} {S : Finset Sig}
    (sub : ∀ a ∈ S, a ∈ initWires j) (hnk : neg ((inputs ++ [or04]).getD j zero) ∉ S) :
    ∀ a ∈ S, a ∈ inputs ++ [or04] := by
  intro a ha
  have hm := sub a ha
  simp only [initWires, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
  rcases hm with hi | rfl | rfl
  · exact Or.inl hi
  · exact Or.inr rfl
  · exact False.elim (hnk ha)

theorem case_0 {k t : Nat} {S : Finset Sig} (hk : k ≤ 13) (run : Live graph k t S)
    (sub : ∀ a ∈ S, a ∈ initWires 0) : False := by
  by_cases hnk : neg ((inputs ++ [or04]).getD 0 zero) ∈ S
  · have hx4 := req_x4 run sub (by decide +kernel)
    by_cases hx0 : inputs.getD 0 zero ∈ S
    · have hcov : ∀ a ∈ S, freeWord (vars 494) (movedWord (fixRows 17 0) a) = true := by
        have hall : (initWires 0).all (fun a => freeWord (vars 494) (movedWord (fixRows 17 0) a)) = true := by decide +kernel
        exact fun a ha => List.all_eq_true.mp hall a (sub a ha)
      have hnd := nodup_triple (a := inputs.getD 0 zero) (b := inputs.getD 4 zero)
        (c := neg ((inputs ++ [or04]).getD 0 zero)) (by decide +kernel)
      exact live_slice_contra run (fixRows 17 0) [inputs.getD 0 zero, inputs.getD 4 zero, neg ((inputs ++ [or04]).getD 0 zero)]
        (proper_of _ (by decide +kernel)) (known_at valid383 494 11 (by decide +kernel))
        (by decide +kernel) hcov
        (mem_triple_of hx0 hx4 hnk)
        hnd
        (fun a ha => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl
          · left; decide +kernel
          · left; decide +kernel
          · right; decide +kernel)
        (by simp only [List.length_cons, List.length_nil]; omega)
    · by_cases hor : or04 ∈ S
      · have hcov : ∀ a ∈ S, freeWord (vars 494) (movedWord (fixRows 17 0) a) = true := by
          have hall : (initWires 0).all (fun a => freeWord (vars 494) (movedWord (fixRows 17 0) a)) = true := by decide +kernel
          exact fun a ha => List.all_eq_true.mp hall a (sub a ha)
        have hnd := nodup_triple (a := inputs.getD 4 zero) (b := or04)
          (c := neg ((inputs ++ [or04]).getD 0 zero)) (by decide +kernel)
        exact live_slice_contra run (fixRows 17 0) [inputs.getD 4 zero, or04, neg ((inputs ++ [or04]).getD 0 zero)]
          (proper_of _ (by decide +kernel)) (known_at valid383 494 11 (by decide +kernel))
          (by decide +kernel) hcov
          (mem_triple_of hx4 hor hnk)
          hnd
          (fun a ha => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
            rcases ha with rfl | rfl | rfl
            · left; decide +kernel
            · left; decide +kernel
            · right; decide +kernel)
          (by simp only [List.length_cons, List.length_nil]; omega)
      · have hcov : ∀ a ∈ S, freeWord (vars495Flip 0) (movedWord (fixRows 16 0) a) = true := by
          have hall : (((initWires 0).erase (inputs.getD 0 zero)).erase or04).all
              (fun a => freeWord (vars495Flip 0) (movedWord (fixRows 16 0) a)) = true := by decide +kernel
          intro a ha
          have hm : a ∈ ((initWires 0).erase (inputs.getD 0 zero)).erase or04 := by
            rw [List.mem_erase_of_ne (by rintro rfl; exact hor ha),
                List.mem_erase_of_ne (by rintro rfl; exact hx0 ha)]
            exact sub a ha
          exact List.all_eq_true.mp hall a hm
        exact live_slice_contra run (fixRows 16 0) [inputs.getD 4 zero]
          (proper_of _ (by decide +kernel)) low495_flip0 (by decide +kernel) hcov
          (by simpa using hx4) (by simp)
          (fun a ha => by rcases List.mem_singleton.mp ha with rfl; left; decide +kernel)
          (by simp only [List.length_cons, List.length_nil]; omega)
  · exact no_or04_only hk run (drop_nk sub hnk)

theorem case_1 {k t : Nat} {S : Finset Sig} (hk : k ≤ 13) (run : Live graph k t S)
    (sub : ∀ a ∈ S, a ∈ initWires 1) : False := by
  by_cases hnk : neg ((inputs ++ [or04]).getD 1 zero) ∈ S
  · by_cases hx1 : inputs.getD 1 zero ∈ S
    · have hcov : ∀ a ∈ S, freeWord (vars 509 ++ [or04]) (movedWord (fixRows 2 0) a) = true := by
        have hall : (initWires 1).all (fun a => freeWord (vars 509 ++ [or04]) (movedWord (fixRows 2 0) a)) = true := by decide +kernel
        exact fun a ha => List.all_eq_true.mp hall a (sub a ha)
      have hnd := nodup_pair (a := inputs.getD 1 zero) (b := neg ((inputs ++ [or04]).getD 1 zero)) (by decide +kernel)
      exact live_slice_contra run (fixRows 2 0) [inputs.getD 1 zero, neg ((inputs ++ [or04]).getD 1 zero)]
        (proper_of _ (by decide +kernel)) lower_509_or (by decide +kernel) hcov
        (mem_pair_of hx1 hnk)
        hnd
        (fun a ha => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl
          · left; decide +kernel
          · right; decide +kernel)
        (by simp only [List.length_cons, List.length_nil]; omega)
    · have hx4 := req_x4 run sub (by decide +kernel)
      have hcov : ∀ a ∈ S, freeWord (vars495Flip 1) (movedWord (fixRows 16 0) a) = true := by
        have hall : ((initWires 1).erase (inputs.getD 1 zero)).all
            (fun a => freeWord (vars495Flip 1) (movedWord (fixRows 16 0) a)) = true := by decide +kernel
        intro a ha
        have hm : a ∈ (initWires 1).erase (inputs.getD 1 zero) := by
          rw [List.mem_erase_of_ne (by rintro rfl; exact hx1 ha)]; exact sub a ha
        exact List.all_eq_true.mp hall a hm
      exact live_slice_contra run (fixRows 16 0) [inputs.getD 4 zero]
        (proper_of _ (by decide +kernel)) low495_flip1 (by decide +kernel) hcov
        (by simpa using hx4) (by simp)
        (fun a ha => by rcases List.mem_singleton.mp ha with rfl; left; decide +kernel)
        (by simp only [List.length_cons, List.length_nil]; omega)
  · exact no_or04_only hk run (drop_nk sub hnk)

theorem case_2 {k t : Nat} {S : Finset Sig} (hk : k ≤ 13) (run : Live graph k t S)
    (sub : ∀ a ∈ S, a ∈ initWires 2) : False := by
  by_cases hnk : neg ((inputs ++ [or04]).getD 2 zero) ∈ S
  · by_cases hx2 : inputs.getD 2 zero ∈ S
    · have hcov : ∀ a ∈ S, freeWord (vars 507 ++ [or04]) (movedWord (fixRows 4 0) a) = true := by
        have hall : (initWires 2).all (fun a => freeWord (vars 507 ++ [or04]) (movedWord (fixRows 4 0) a)) = true := by decide +kernel
        exact fun a ha => List.all_eq_true.mp hall a (sub a ha)
      have hnd := nodup_pair (a := inputs.getD 2 zero) (b := neg ((inputs ++ [or04]).getD 2 zero)) (by decide +kernel)
      exact live_slice_contra run (fixRows 4 0) [inputs.getD 2 zero, neg ((inputs ++ [or04]).getD 2 zero)]
        (proper_of _ (by decide +kernel)) lower_507_or (by decide +kernel) hcov
        (mem_pair_of hx2 hnk)
        hnd
        (fun a ha => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl
          · left; decide +kernel
          · right; decide +kernel)
        (by simp only [List.length_cons, List.length_nil]; omega)
    · have hx4 := req_x4 run sub (by decide +kernel)
      have hcov : ∀ a ∈ S, freeWord (vars495Flip 2) (movedWord (fixRows 16 0) a) = true := by
        have hall : ((initWires 2).erase (inputs.getD 2 zero)).all
            (fun a => freeWord (vars495Flip 2) (movedWord (fixRows 16 0) a)) = true := by decide +kernel
        intro a ha
        have hm : a ∈ (initWires 2).erase (inputs.getD 2 zero) := by
          rw [List.mem_erase_of_ne (by rintro rfl; exact hx2 ha)]; exact sub a ha
        exact List.all_eq_true.mp hall a hm
      exact live_slice_contra run (fixRows 16 0) [inputs.getD 4 zero]
        (proper_of _ (by decide +kernel)) low495_flip2 (by decide +kernel) hcov
        (by simpa using hx4) (by simp)
        (fun a ha => by rcases List.mem_singleton.mp ha with rfl; left; decide +kernel)
        (by simp only [List.length_cons, List.length_nil]; omega)
  · exact no_or04_only hk run (drop_nk sub hnk)

theorem case_3 {k t : Nat} {S : Finset Sig} (hk : k ≤ 13) (run : Live graph k t S)
    (sub : ∀ a ∈ S, a ∈ initWires 3) : False := by
  by_cases hnk : neg ((inputs ++ [or04]).getD 3 zero) ∈ S
  · have hx4 := req_x4 run sub (by decide +kernel)
    by_cases hx3 : inputs.getD 3 zero ∈ S
    · have hcov : ∀ a ∈ S, freeWord (vars 487) (movedWord (fixRows 24 0) a) = true := by
        have hall : (initWires 3).all (fun a => freeWord (vars 487) (movedWord (fixRows 24 0) a)) = true := by decide +kernel
        exact fun a ha => List.all_eq_true.mp hall a (sub a ha)
      have hnd := nodup_triple (a := inputs.getD 3 zero) (b := inputs.getD 4 zero)
        (c := neg ((inputs ++ [or04]).getD 3 zero)) (by decide +kernel)
      exact live_slice_contra run (fixRows 24 0) [inputs.getD 3 zero, inputs.getD 4 zero, neg ((inputs ++ [or04]).getD 3 zero)]
        (proper_of _ (by decide +kernel)) (known_at valid383 487 11 (by decide +kernel))
        (by decide +kernel) hcov
        (mem_triple_of hx3 hx4 hnk)
        hnd
        (fun a ha => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl
          · left; decide +kernel
          · left; decide +kernel
          · right; decide +kernel)
        (by simp only [List.length_cons, List.length_nil]; omega)
    · have hcov : ∀ a ∈ S, freeWord (vars495Flip 3) (movedWord (fixRows 16 0) a) = true := by
        have hall : ((initWires 3).erase (inputs.getD 3 zero)).all
            (fun a => freeWord (vars495Flip 3) (movedWord (fixRows 16 0) a)) = true := by decide +kernel
        intro a ha
        have hm : a ∈ (initWires 3).erase (inputs.getD 3 zero) := by
          rw [List.mem_erase_of_ne (by rintro rfl; exact hx3 ha)]; exact sub a ha
        exact List.all_eq_true.mp hall a hm
      exact live_slice_contra run (fixRows 16 0) [inputs.getD 4 zero]
        (proper_of _ (by decide +kernel)) low495_flip3 (by decide +kernel) hcov
        (by simpa using hx4) (by simp)
        (fun a ha => by rcases List.mem_singleton.mp ha with rfl; left; decide +kernel)
        (by simp only [List.length_cons, List.length_nil]; omega)
  · exact no_or04_only hk run (drop_nk sub hnk)

theorem case_4 {k t : Nat} {S : Finset Sig} (hk : k ≤ 13) (run : Live graph k t S)
    (sub : ∀ a ∈ S, a ∈ initWires 4) : False := by
  by_cases hnk : neg ((inputs ++ [or04]).getD 4 zero) ∈ S
  · have hcov : ∀ a ∈ S, freeWord (vars 495) (movedWord (fixRows 16 0) a) = true := by
      have hall : (initWires 4).all (fun a => freeWord (vars 495) (movedWord (fixRows 16 0) a)) = true := by decide +kernel
      exact fun a ha => List.all_eq_true.mp hall a (sub a ha)
    exact live_slice_contra run (fixRows 16 0) [neg ((inputs ++ [or04]).getD 4 zero)]
      (proper_of _ (by decide +kernel)) (known_at valid383 495 13 (by decide +kernel))
      (by decide +kernel) hcov (by simpa using hnk) (by simp)
      (fun a ha => by rcases List.mem_singleton.mp ha with rfl; right; decide +kernel)
      (by simp only [List.length_cons, List.length_nil]; omega)
  · exact no_or04_only hk run (drop_nk sub hnk)

theorem case_6 {k t : Nat} {S : Finset Sig} (hk : k ≤ 13) (run : Live graph k t S)
    (sub : ∀ a ∈ S, a ∈ initWires 6) : False := by
  by_cases hnk : neg ((inputs ++ [or04]).getD 6 zero) ∈ S
  · by_cases hx6 : inputs.getD 6 zero ∈ S
    · have hcov : ∀ a ∈ S, freeWord (vars 447 ++ [or04]) (movedWord (fixRows 64 0) a) = true := by
        have hall : (initWires 6).all (fun a => freeWord (vars 447 ++ [or04]) (movedWord (fixRows 64 0) a)) = true := by decide +kernel
        exact fun a ha => List.all_eq_true.mp hall a (sub a ha)
      have hnd := nodup_pair (a := inputs.getD 6 zero) (b := neg ((inputs ++ [or04]).getD 6 zero)) (by decide +kernel)
      exact live_slice_contra run (fixRows 64 0) [inputs.getD 6 zero, neg ((inputs ++ [or04]).getD 6 zero)]
        (proper_of _ (by decide +kernel)) lower_447_or (by decide +kernel) hcov
        (mem_pair_of hx6 hnk)
        hnd
        (fun a ha => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl
          · left; decide +kernel
          · right; decide +kernel)
        (by simp only [List.length_cons, List.length_nil]; omega)
    · have hx4 := req_x4 run sub (by decide +kernel)
      have hcov : ∀ a ∈ S, freeWord (vars495Flip 6) (movedWord (fixRows 16 0) a) = true := by
        have hall : ((initWires 6).erase (inputs.getD 6 zero)).all
            (fun a => freeWord (vars495Flip 6) (movedWord (fixRows 16 0) a)) = true := by decide +kernel
        intro a ha
        have hm : a ∈ (initWires 6).erase (inputs.getD 6 zero) := by
          rw [List.mem_erase_of_ne (by rintro rfl; exact hx6 ha)]; exact sub a ha
        exact List.all_eq_true.mp hall a hm
      exact live_slice_contra run (fixRows 16 0) [inputs.getD 4 zero]
        (proper_of _ (by decide +kernel)) low495_flip6 (by decide +kernel) hcov
        (by simpa using hx4) (by simp)
        (fun a ha => by rcases List.mem_singleton.mp ha with rfl; left; decide +kernel)
        (by simp only [List.length_cons, List.length_nil]; omega)
  · exact no_or04_only hk run (drop_nk sub hnk)

theorem case_9 {k t : Nat} {S : Finset Sig} (hk : k ≤ 13) (run : Live graph k t S)
    (sub : ∀ a ∈ S, a ∈ initWires 9) : False := by
  by_cases hnk : neg ((inputs ++ [or04]).getD 9 zero) ∈ S
  · have hx0 := req_x0 run sub (by decide +kernel)
    have hx4 := req_x4 run sub (by decide +kernel)
    have hcov : ∀ a ∈ S, freeWord (vars 494) (movedWord (fixRows 17 0) a) = true := by
      have hall : (initWires 9).all (fun a => freeWord (vars 494) (movedWord (fixRows 17 0) a)) = true := by decide +kernel
      exact fun a ha => List.all_eq_true.mp hall a (sub a ha)
    have hnd := nodup_triple (a := inputs.getD 0 zero) (b := inputs.getD 4 zero)
      (c := neg ((inputs ++ [or04]).getD 9 zero)) (by decide +kernel)
    exact live_slice_contra run (fixRows 17 0) [inputs.getD 0 zero, inputs.getD 4 zero, neg ((inputs ++ [or04]).getD 9 zero)]
      (proper_of _ (by decide +kernel)) (known_at valid383 494 11 (by decide +kernel))
      (by decide +kernel) hcov
      (mem_triple_of hx0 hx4 hnk)
      hnd
      (fun a ha => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl
        · left; decide +kernel
        · left; decide +kernel
        · right; decide +kernel)
      (by simp only [List.length_cons, List.length_nil]; omega)
  · exact no_or04_only hk run (drop_nk sub hnk)

theorem case_10 {k t : Nat} {S : Finset Sig} (hk : k ≤ 13) (run : Live graph k t S)
    (sub : ∀ a ∈ S, a ∈ initWires 10) : False := by
  have h10 : neg ((inputs ++ [or04]).getD 10 zero) = one := by decide +kernel
  have hnk : neg ((inputs ++ [or04]).getD 10 zero) ∉ S := fun hm =>
    (live_proper run _ hm).2 h10
  exact no_or04_only hk run (drop_nk sub hnk)

-- Symmetry sigma = [81, 130, 118] swaps (1<->5), (2<->8), (6<->7) and preserves graph & or04!
def sigmaMoves : List Move := [81, 130, 118].map swapRows

theorem sigma_reduce {j1 j2 k t : Nat} {S : Finset Sig}
    (run : Live graph k t S) (sub : ∀ a ∈ S, a ∈ initWires j1)
    (hmap : (initWires j1).all (fun a => (initWires j2).contains (movedWord sigmaMoves a)) = true) :
    ∃ S', Live graph k t S' ∧ ∀ a ∈ S', a ∈ initWires j2 := by
  have hok : autoOK graph sigmaMoves = true := by decide +kernel
  simp only [autoOK, Bool.and_eq_true, beq_iff_eq] at hok
  have onto : Function.Surjective (movedRow sigmaMoves) :=
    fun r => ⟨movedRow sigmaMoves.reverse r, composed_id hok.2 r⟩
  have run' := live_rename run (movedRow sigmaMoves) onto
  have hgoal : rename (movedRow sigmaMoves) graph = graph :=
    (moved_eq_rename sigmaMoves graph).symm.trans hok.1.1
  rw [hgoal] at run'
  refine ⟨S.image (rename (movedRow sigmaMoves)), run', fun a ha => ?_⟩
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ha
  rw [← moved_eq_rename sigmaMoves v]
  have hm := List.all_eq_true.mp hmap v (sub v hv)
  simpa only [List.contains_eq_mem, decide_eq_true_eq] using hm

theorem all_cases (x1 : Fin 11) {k t : Nat} {S : Finset Sig}
    (hk : k ≤ 13) (run : Live graph k t S) (sub : ∀ a ∈ S, a ∈ initWires x1.val) : False := by
  fin_cases x1
  · exact case_0 hk run sub
  · exact case_1 hk run sub
  · exact case_2 hk run sub
  · exact case_3 hk run sub
  · exact case_4 hk run sub
  · obtain ⟨S', run', sub'⟩ := sigma_reduce (j2 := 1) run sub (by decide +kernel)
    exact case_1 hk run' sub'
  · exact case_6 hk run sub
  · obtain ⟨S', run', sub'⟩ := sigma_reduce (j2 := 6) run sub (by decide +kernel)
    exact case_6 hk run' sub'
  · obtain ⟨S', run', sub'⟩ := sigma_reduce (j2 := 2) run sub (by decide +kernel)
    exact case_2 hk run' sub'
  · exact case_9 hk run sub
  · exact case_10 hk run sub

theorem initWires_bits (j : Nat) (r : Row) :
    (initWires j).map (bit r) =
      let x8 := List.ofFn (sample r) ++ [sample r 0 || sample r 4]
      x8 ++ [!(x8.getD j false)] := by
  have hor : bit r or04 = (sample r 0 || sample r 4) := by
    simp only [or04, bit_bin, sample]
    rfl
  have hx8 : (inputs ++ [or04]).map (bit r) = List.ofFn (sample r) ++ [sample r 0 || sample r 4] := by
    rw [List.map_append, List.map_singleton, ← sampled r, hor]
  have hget : bit r ((inputs ++ [or04]).getD j zero) =
      (List.ofFn (sample r) ++ [sample r 0 || sample r 4]).getD j false := by
    rw [← hx8, ← b_read]
  simp only [initWires, List.map_append, List.map_cons, List.map_nil, bit_neg, hget]
  rw [← sampled r, hor, List.append_assoc]
  rfl

theorem main_3406 :
    ∀ (x1 : Fin (11 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (13 : ℕ) →       x2.output ≤ (24 : ℕ) →         (∀ x6 ∈ x2.gates, ∀ x8 ∈ x6.inputs, x8 ≤ (24 : ℕ)) →           ∃ (x7 : Fin (9 : ℕ) → Bool),             have x8 : List Bool := List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ))];             x2.eval (x8 ++ [!x8.getD (↑x1) Bool.false]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  intro x1 x2 hfan hsize _hout _hin
  by_contra hnot
  push Not at hnot
  have hgoalEq : (execute x2.gates (initWires x1.val)).getD x2.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j, hj⟩
    change bit r ((execute x2.gates (initWires x1.val)).getD x2.output zero) = bit r graph
    have hev : bit r ((execute x2.gates (initWires x1.val)).getD x2.output zero) =
        x2.eval ((initWires x1.val).map (bit r)) := by
      rw [← b_read, execute_bits _ _ _ (fun g hg => (hfan g hg).1)]
      rfl
    rw [hev, initWires_bits]
    exact (Classical.not_not.mp (hnot (sample r))).trans (edge_table r).symm
  have hout := get_rep (execute x2.gates (initWires x1.val)) x2.output
  rw [hgoalEq] at hout
  have targetIn := hout.resolve_right (fun hn => hn graph_proper)
  obtain ⟨k, t, S, hk, run, sub⟩ := extract x2.gates (initWires x1.val) hfan graph_proper targetIn
  have hk13 : k ≤ 13 := by
    change x2.gates.length ≤ 13 at hsize
    omega
  exact all_cases x1 hk13 run sub

end PEqualNP.Outside.L_meta_3406

theorem PEqualNP.Outside.L_meta_3406 : ∀ (x1 : Fin (11 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (13 : ℕ) →       x2.output ≤ (24 : ℕ) →         (∀ x6 ∈ x2.gates, ∀ x8 ∈ x6.inputs, x8 ≤ (24 : ℕ)) →           ∃ (x7 : Fin (9 : ℕ) → Bool),             have x8 : List Bool := List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ))];             x2.eval (x8 ++ [!x8.getD (↑x1) Bool.false]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) :=
  PEqualNP.Outside.L_meta_3406.main_3406