import PEqualNP.Defs
-- The sixteen-gate certificate below is by JLDC, pull request 6373.
-- Each sample bank retains witnesses for the gate moves ruled out by the original bank.
-- The live-set calculus and induced-graph certificates are from PressF10, L-meta-1667.
namespace PEqualNP.Outside.L_meta_3590_aux
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
def orSeed : Sig := inputs.getD 0 zero ||| inputs.getD 4 zero
theorem seed_table : ∀ r : Row, bit r orSeed = (sample r 0 || sample r 4) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem seed_nonzero : orSeed ≠ zero := by decide +kernel
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

def neighbor (i : Fin 9) : Nat := [4,2,1,2,0,0,1,2,3].getD i.val 0
def absentRow (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< neighbor i)
def presentRow (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor i))

theorem seed_witness : ∀ i : Fin 9,
    (bit (absentRow i) graph != bit (presentRow i) graph) &&
    ((inputs++[orSeed]).all fun w => w == inputs.getD i.val zero ||
      bit (absentRow i) w == bit (presentRow i) w) = true := by decide +kernel

theorem all_roots {k t S} (h : Live graph k t S) (sub : ∀ v ∈ S, v ∈ inputs++[orSeed]) :
    S=inputs.toFinset ∨ S=(inputs++[orSeed]).toFinset := by
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
  by_cases hseed : orSeed ∈ S
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
    (first : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 4))
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) (small : C.size ≤ 15) :
    ∃ k t, k ≤ 14 ∧ (Live graph k t inputs.toFinset ∨ Live graph k t (inputs++[orSeed]).toFinset) := by
  have headEq : (execute C.gates inputs).getD 9 zero = orSeed := by
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
    have eq0 : gv inputs g = orSeed := by
      rw [hgs] at headEq
      change (execute gs (inputs++[gv inputs g])).getD 9 zero = orSeed at headEq
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



def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def vars (m : Nat) :=
  let raw := (selected m).map Prod.snd
  if m.testBit 11 then raw ++ [vertex m 0 ||| vertex m 4] else raw
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


-- The low nine bits select vertices. A set bit at position eleven supplies
-- the disjunction of the two surviving endpoints as an additional input.
def poolMask (m : Nat) (c : ColumnInfo) :=
  if m.testBit 11 && !c.2.2.1.testBit 11 then m % 512 else m

def poolColumn (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) :=
  if m.testBit 11 && !c.2.2.1.testBit 11 then
    (chartGoal (m % 512) == chartGoal m) && colCheck (m % 512) c prior
  else colCheck m c prior

theorem poolColumn_sound {m} (c : ColumnInfo) (prior : Nat → Nat)
    (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : poolColumn m c prior = true) :
    Slice (vars (poolMask m c)) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  unfold poolColumn at ok
  unfold poolMask
  split <;> rename_i tag
  · rw [if_pos tag] at ok
    obtain ⟨same,check⟩ := Bool.and_eq_true_iff.mp ok
    rw [←beq_iff_eq.mp same]
    exact col_sound c prior low check
  · rw [if_neg tag] at ok
    exact col_sound c prior low ok

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


abbrev Bits := BitVec 129
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 129 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 129 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 129 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 129 → Row) (x : Decor) := x.2 = pairSig r s x.1
def dneg (x : Decor) : Decor := (neg x.1,~~~x.2.1,~~~x.2.2)
def dbin (d : Bool) (x y : Decor) : Decor :=
  if d then (bin d x.1 y.1,x.2.1 ||| y.2.1,x.2.2 ||| y.2.2)
  else (bin d x.1 y.1,x.2.1 &&& y.2.1,x.2.2 &&& y.2.2)

theorem ofRows_neg (r : Fin 129 → Row) (a : Sig) : ofRows r (neg a) = ~~~ofRows r a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (neg a) ⟨j,hj⟩
  rw [bit_neg,←ofRows_bit r a ⟨j,hj⟩] at h
  simpa only [BitVec.getLsbD_not,hj,decide_true,Bool.true_and] using h
theorem ofRows_bin (r : Fin 129 → Row) (d : Bool) (a b : Sig) :
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

def asRow (cols : Nat → Bits) (i : Fin 129) : Row :=
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 129) (j : Fin 9) :
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
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 129) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 129) :
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

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig)) × Nat
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links,_) := c
  let un := op==2
  let len := 1+(n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  if len>cap then true else
    let d := len==cap
    let rs := restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 129 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (opKeep un ka kb a b ws).map Prod.fst
      closeChild pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (movedDecor op a b).1 :: (opKeep (op==2) ka kb a b ws).map Prod.fst
theorem evalMove_sound {raw T r s ws pools links cap a b op ka kb id}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false → a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov ws,pools,links,id) op a b (movedDecor op a b) ka kb = true) :
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
  change covered (decide (child.length = cap)) (pairSig r s) child = BitVec.allOnes 129 at sep
  rw [deq] at sep
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2) != BitVec.allOnes 129) = false := by simp [sep]
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

theorem node_sound {raw T r s ws pools links cap id}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov ws,pools,links,id) ws = true) :
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
        (test : testPair (cap,ws.length,ws,preCov ws,pools,links,id) a b d = true) :
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
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 129) :
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
    (hp : chartSamples m p = BitVec.allOnes 129) (hq : chartSamples m q = 0) :
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
    materialize (vars (poolMask g.mask ci)) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols.values, Slice (vars (poolMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : g.cols.read i with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    exact materialize_sound (raw:=vars (poolMask g.mask ci)) (cols ci (g.cols.read_mem e)) h

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
    (if k=0 then true else testAll (k,ws.length,ws,preCov ws,rules,ls,(g.mask*16+k)*1024+i) ws)

theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols.values, Slice (vars (poolMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
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
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 129) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.values.all (fun c => poolColumn g.mask c prior) &&
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
      (fun x hx => poolColumn_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => poolColumn_sound _ prior lower (geometry.1.2 x hx)) geometry.2
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
def lanePlace (v : Nat) (upper : Nat) := 2^130*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^130 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<130 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<130 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<130 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
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

def fullMarks (r packed : Nat) := ((packed+r) >>> 129) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (130*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^130)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 130*(i+1)-130=130*i := by omega
      have ge : ¬130*(i+1)<130 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 129 = (a==BitVec.allOnes 129) := by
  by_cases h : a=BitVec.allOnes 129
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^129-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^129 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (130*i) =
      (f xs[i]==BitVec.allOnes 129) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^130*u+x+(2^130*v+1)=2^130*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^130 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬130*(i+1)+129<130 := by omega
      have di : 130*(i+1)+129-130=130*i+129 := by omega
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
theorem top_xor (a : Bits) : BitVec.allOnes 129 ^^^ a = ~~~a := BitVec.allOnes_xor
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp (units xs.length*(BitVec.allOnes 129).toNat) op
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
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 130) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (130*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
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
      apply ih (mask:=mask >>> 130) (i:=i) (by simpa using hi) _ ok.2
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

-- Each residual gate move selects a check from this compact table.
-- The selected check verifies its witness independently.
def routingWords0 (i : Nat) : Nat := (if i < 6 then (if i < 3 then (if i < 1 then 0x4034068788a87556358080c904ae060883a0447832c9664d31f8f0a6037021a123600ae8b48da8c3562103be0bd68e6e1b5c110b2c000a00910c573d00e75952011f1462fd64404442156ae70049bc2181030d1c0c403960180385d1c18a51ffe208ff555102587064e75a00a00128c001c317c642c00200dd770596b1c449d7ba142540094893e2c0222b862a10285976e978c0b11c2a302090d032b80182373153c52bf899bed28301802f01570260837062c40877c2e040a30c83051f91c400bdfba3642ae0c15228509640dcc5d90033208ff438be90022003c4c23cb99344340524083ea00d04380103968c3eb0158a4010ce8803941913fa100ba40d392114097e01a27829a327e087e042487fd1148a00e78bc0202228f83e473727819c303e1101909c77a43b03b406778f030f2b11c069c8d1a560e23342c41e0102c609a0a83281e8e85200a1c80e1260115310972540880192206cbe000f9429040e681874060c7c3d0e488498675d8250de0f9d7e54015814f426ee45024a1703 else (if i < 2 then 0x49446215013045e2c079de02b982275fdee41fc4069cf180ad20681426c0620a02278800705e47157001465c195822d0e310030eed1d0c8cee08340d788c98344889e0009b68fc38ee8d4c459061018a177bd19b75d602464e5084d01824804818a2691d510078009860443bec8a5b2962ca45f8093248052f80c45880e7a1542b02f4d564421115808178d9c00624863e01c68bda601a179940516b02d04d81d41014bc106099768a55427744277426fa4d83817438df0d0636aa10008f90d2a8151070ea087612193a111a710022b00bc8d5d0c18c064122a0c5607dd0280c805372e516e0a1d8d74a6420c0db2a05a2a168fb11c72182c0d400ec118fe47aa61943a679307086da62411c0a314310c5a1de860988ad6400b117092942716b760e04bbd001018b032c71c6180d8314325f3028144640001159b2a61250a01dc5f4d03f2c063517df40fb65865980029c0c85800144a822abf02a694006ee07ce7b02fc468032030dc503402c8248ce2b80cd74af0ac44004064e11821b0fc9 else 0x8e8c87e2805c400a1f2aa540bd81cf633dc05365d6105840100b36e68839e98c3f5a03de1d0478d81123ab3c187fdce7799a41eb508d6f30006030400670a1003282a7047d18f0cc6f0319228af4f7050323716482e1826498dc20b6205c7a58798610170d4cc10b830418c07c4415002082174184a890171866946c775420078880b58fa3fcb0c8703295aa3c039db9a78bb82c6e50029c058068275c3377a00030fd84840fe3fa18b805633b547b622974292a03c11e4025b86152f2012841cc70a02b9d4d044bb46c602d116c0b030dc640663819b11ca91bd34117b01380305be5e7f520286966d8a52d88f018801542331532008844ba3c0a10073e41a2807d8468a402203643cc5f843b8b7f02001db4094084c0c41423724405e36e0b49af46700909500f6343c6007e8fc66031201216046670ccb4062e3920807af0daa68a0010b5181ceb3000f03719a0c0b9fe5a2070866b87590c058723dc0b00301e002280614cb93da0827c818443b06014c7404c4e1a014d8f4609a01a0445)) else (if i < 4 then 0xa10113232c39a0320161b170b7c020018ea800028319b77eae204c40ac17ac31212002d90880291c0f800a7f038480f2786dc6022e200c2806a1d04753fa0781d484048628308aaef00a2125891609064211347b8c220bc18c99580c304afcc2638510f610426129c7ea4008c1f1dc1c0430c000eb6a6026843478857c576c62158100d3af190167f316cd9218b210831f10029360cba6a0ce1988b030040d6b7284a0630f1056451507b4f040160000c80a855c0274301a00685f252e170897410cddcba1a3fc06d88586d90315cfe31a03740165c4a1e37832a9c7128534eade3c442010ff423c602efa6c3a405ea0030dcea06c69006002e920295d4230c1ba41170fbbbe82f6b8201a04e1ba0a0433b98b85b047b0411297143c6b118f338fda94010a34004c29682c38400a2091f0a1507e634281da63a01a5c01b0513a300c55e4934e5034352c2d37c8145c5a781285c4aa485bec211f387379d1007c634c111a0cc038c476e433d400ea545eb5982b820141c78591741b044fa00032 else (if i < 5 then 0x608b6037d003e261f3f3d23f8b364662f71d49bed60801f34a019b6c80725490034406000d8ac410e3abc441467cba106c42af2fc4553443420c00011e0596012001d163528cee5a8026b096d4301015c343aee812829f2405840c2006180e409979c21dcf81a0cdbc0124001980514b7e2011822ca00003f5832940340777ff00043812d5100b7400048f2e88800f7a01d4d2a10a7a084990e0aaefb00c810007d0b97e144c301e8a32388df0c6e436018cf00e950098f6871ce3e4caec029503e520623c032814bdd90a31205e04483201142081cc41c5bc66db1829bb5fa41be33080100e0393e003f84e403410a8086c436878023602aa01953c8970930f75196221762087a9a0518319bc45cb3d8562bcc4c9088b30c8550e541816ec604b6a0b8c8af3fce599758e8920625e4d8861e3e8b40694c06b3018d00800193c8800b5053a802017c0c0ca3280ea9c36608bbc608b701e0e10aedd50091f821c9a0572080e03a3828aab817326ef05f81f22b4488a81e5a12d411c6a6606d617 else 0x1fd06e9488608680d9bed22f3343805ac022848ce9750902c82560290200022b84528c9c0b4cf2e1b84007c03728c183c4402e3ea0342007e1c7ac73c9031006a02809ac3287e0a232e0f49814053060281f050103d7a62043a3c2724543a3022713900e010c500c7245da58060f1106951397058814e08038e78d02016c1a5b4e17e02a071fc7848cb1c0005406402a5498b09ec4411308ba60bd901ac78bfb3c8000140462778965fa17da9f50921463f0676080054d6b2800705c258418650150a5c9e60093dc08e041a488d3b4420c0160173aa000cc655381101047d81a54002221f0c015632f2491621e1823c19a0380a282829c0cc9714e85784304bb4d75d059023bcac4b01d246103220e710e0858f69ad216a02c14e5a269175cb78b9ab852e820011886b802f246c09980005edd6980a8ae1c23a04f40d182ba7420056c05b4f826950c74380059004b13f60077eb630428ee7002281728446095edc76f4ca00837020300f561024010968157084314d08099b40d02152e1e798))) else (if i < 9 then (if i < 7 then 0x20c148746029b40fa30a4995e1c788198a1160f57cc0595982828016785a0f85821050730b0c04eb28394b0d86e005d0203127d990080c50c3140a80010f07292a86ca5d0c20054204308c0b02204106dee8d5c52c0f0c0378c081e1a8944e5dc56dfb68fac802474226864affd080a3a138048558e58bc50383d0790bdeef336fd8650fa9e0c64007dc0601dd3c0448005e2f5cf0204c45800b1c10858055e08fc8010be01e04a004aeaa5d68ba4705c84d0659800ac2780718f81c18180e4e3c0e10bcce29d66a3d1785c4022943150940c261180b181c8d0015e02e1b460bc023f610ac59265189885c72130cd240f59e6a2008860fb4013659aa8478874a8e0f01903b0270101509050067d8942065f3000c0523870b9f43e11d1e036a00499cc203500501843c8211b013002f2007a72070f4d6c49403000008003c22993a4af680794dc3568c4203f831643681011b9299b1407f0040a51d06a0061562fd8903d0b10d0ec583067b010dad034545dc0a19042c40700d48a47568302 else (if i < 8 then 0x9a612e081c573f62bc7103161843400b0909d405f81880414242224fe32780ce283e1f40923a1f8f7c0b095677a309a6311690ab0c018218714085d016c4107383c9c6a348c009305e0511648444870c56d80031ca0c8a80608d827cf0002056503250387141670c40b28930639435e6c002c4618178020c004024033e16021034e50d01d0d4cf8863624b3734e73565a0048340200009603200e8808cc31443a1d204bf8160125afc1350720c0617e8058003f708d9ae08e00050a13e392486c884677aa505d81f882be22010feefc47e98a3c0f60011ee88e0f95d81804ae8300d630a283914a0fc5f62e184ae39b6b96d50401140e3e8274104767fed0640c04a001b2b18ca2271c3ab0e785e9116a668b7bec04f609268c03d38ef5a2170aedc424501d0e14e3a53ebd0003384d8c40acdbfd0c84c7cbb901a21f81d0406e1b3260640668a00b0e5003a6854b85362e051aebd661279a02e44d5426c201460400033b084c10e226ad9a64038066d38d202e405738c07a545367710b8485 else 0x4428096a39a4741f97d64fa0f582caf3abab01eb1f27b118ce367956fc60ae22622928e289705f81740a168ae07f3582ccfc78e1071624200387030180c15a003d6c43685ce8081000b80c350104230008806600eb34148c3602f6004924b803b2c79500149c3600242a59645b00200556285b4f16785f8006421c808019b0e980c8521034e22861870b3c5daa29085f907f638153cff8c035362370442bd180586066806b8315dc54b68072941cac08a350e9c389874ae05b40b0d04e30dff406050124098273620b8607038eaa0b084043f00f069df8082c001200d3e1b5130030b162645269c7a3f40860a300323e2004aa900e9c5663a39e36040070358033ab0854f42080b10018092bff0918218d015888eab311b612606f654c7020becc00a700df0f13f2cc5c8005cdc4f4874260ab12000e3a402038bd00030432520fa1413864c04301811d935d0da2be4ca340c2e8c062b0fba195c2834a4558acdd7efa43cc4014630ef3a285421c74a5aa30001cb26421b1f80320187600cb)) else (if i < 10 then 0x11223001aa369f00806d8280ae3080eb30064021812e318f247dc47e51d309e15dc039c3659192438046164178366b14160ebb529438cc21c100a0501200bf20b671ec48a920ba7847d0609ad21b300580c92e1061fc874afd505f3b0522d008c43e904510fd71860e5845df020f730034a2029a1847417019de4512de3be5a20615c109e12007292f40e1501214704c6f24585a001137d06e8201e71020066eae3e0d4baa02a1815334310a0a83d5dd28752b5814721827e03d31820e160ef04864c042841d0870120424180821881d802e624904ccf21440b6727d81975ee7f0bdb020060cc4f086151c74fd5c64711020188d957a88591b6401ab2b30316c54c0c3f163616000099811224c03058f466b1808b5f05b119a980c67909c914f78025c3381a8b89f011410f89c001ac28745044159b20417c41e84441014b003c30a0517c00010e0f198e383f30edc9088001a080d2c11cd1896a434e3e42241d290c201d810c20b6a8a0008da00008e97c860573d88520c43833e06005c2f5a else (if i < 11 then 0x22be20300630a3008083c4a880eb5868a430042a986331d58f2b2c040c2484061884ec40182e98004c8c0345850006c0c10c488c32f83ef6f7cc759041b141401025d1758abea2f26dee12812b93df5f38b9b0e9880c23d370bf316e403bc9801b84005a0634a010102d05c39b87db6c429a5a33cc000c90a3a20f207502a58dd8bd0952c3e41a147c0003dc000a828302918108068ca35115578c8818c69dbc12d286a2b0b5409c1807d09c031b3bb2c3c000367ed0452889885416b0c39d1003da211407dc828084648f83499c8c8a838064069d0035049518e60c00afbb5c05ddf1174ea570a59e2b52c5cd03416f5ce4b644ebd81380475e80630006096c0ef8143984088ea70f815ae28a011bce0c4c2203576005b117406aa01ab81c491acb6009221a8320194c2788a72e20080628443830031c1b02d3016a22b2747200e93098b431c0062bc5c25fc81808de53019b0706d544021888307a1c782b113f383cc61f6c6d8862a006002bd1208815794a96019be8462c19554dacdf97d9 else 0x133201a871d3058814bf220826d004230007895400640af80c31db084504c1900604a1022e6a0001547ab046aa421400f1d5c0004557070dc0a8669d210279c0905773ce0c410935e260b9c0234cbe000a825498c59074e88409913259f850a6c2b95f0c8a01211cff0052c9e91e28ad2eac385b5662884fa03c426044042494b9e801821a202d2398026815b7a1afa0119833ea8f7f012088c01844068185e0a83674e0082e35e8bc75eee61281f80178001084e3b2000010011900ba5421334980314855bd5692ec74206ca72407e3f212107afa004cea0c1d015e08411d0e20600fc0ec5fe35fb0875c7a29617e3bfc0cc595c22d420152ec166c644a17a01c8477023f058e7d02049713074213b1f6208900c982005cafc302615ac44648e472b1000158f4210df40cc020da0ef1610076ef46f00d710b0000298718000461d2c73543b49684ee12002f1d46b4a66c300a032e6d49f8c8ec283d61f0086488991845e406d6181420db001088006af29ed0f03008118187d6662c289b0270))))
def routingWords1 (i : Nat) : Nat := (if i < 18 then (if i < 15 then (if i < 13 then 0x6dab51021988b02b901820d24a00c8425cda1090285136021c2085e00d42f45a4e460645ed405f0c2c085141cc150857ef723f191e0423ac45eb0073a5243a02a4029c8ed8e900b60878c2e0b23d02d0007c109c23442365aae8488042c35c702111c31b9096504e027115fa00ac06608e483f4c25e0be824481414f8e6631a0127402016c301a2451fe34116a4030389bf6d113003a9a07ed4390d77c68580c0dad1a1e00cd3e07e3d81d840f1f606c10a406ebac71110c64b9a8f09942b046013a381f1558a374c70bed03614800fb312003c0019ba931edcc300c42ff1402d9f401221900701c1d10ba7bb4c009d0460174e99678ac437f0089f962347c41a29dd8460c2366ca00944c6c8661242b660a30c1070bb6af994c098409aa0f2a35b815362da005ae42c20dff1c0510b36d35b802ecf024f0762335d5b1c4aab82a1ce55406639629a90600004f080e1ced058b301c66b8904683c6980528b6a620410180641880052188460c11420071940064295180a8a5b1b0a830b620b558 else (if i < 14 then 0xfac01aad3b001915a4e8f452e942180e3090403300ac7b8397e6c5024e14000a1f50132b60bbd4fbd2c8a0203c038490bb8ba8230430e05214bc4fe2853a380a91007f0aeb4be0c003f3f63238843eeec51493a8992e33828dea238073c454e3194780b875d811ee333a066852a1b0548eb5c017597daa632c21841b80a19a0fdf4318e310847cc05c3221a2d7a0f01ac86b1e00d3ea4e6f7a179115e1f49089007140111ea806d006905840001221e0a54c3dbe6be0c503a970b9854595aac074dea961b0901d822128b05c00240003a0070d00776327918de2fda1902d400387015099e87640066e18e0244219ffb0750f04a00fb8648a09812210e80256167838ad80120800038c77e091460a14610bd290d72703566c495223813fdd85d70630f2f90e1ae026be6b8c9da647fb0990071000aa1b118090e4d16c3423028c0011fec400ce28045623c4a1ef0041d2c1b199140180a8c012832538b02b91ecb238009180e036ba69febf37be24543407000e5d99edcaf33806198301c00f81 else 0x6015400461a805202e0407c32110010864c60c27a307079214830917a075830606300032e28e32d4da045b4608b82ccd01fc06f6b053f42d6a083ff81646a034018e83c146e06409465cd28fa79403861ab8f3f3cce5ac488a2c1f51220c01c114b3da6d10c24765f00c05c5cc0ac7e12cd603587aba86d8606a001138f4f581981ba7cf2851408ede00e498dab543e8024070b54fbcfe0e9455a1cdd08490d1e09010823c41b0ee01adb07f81800d0210978e081f4138a05cfc028100827c1912f0c669d603ea7f554004e302da38c0b604d363aa00860af92d9d0b80000297631fe401b128202d256088fa540090e4074192b10076138930a81a79076eb525131a14080be007ff1b2420840f80f8be08030d1648ec105c410b492ca1b88d18144a220c7f85209180854010fe01301c01bf8e8f9b0021be503c26008021ad9b58ed059105821d40600b0034cb6fc005a1089070b0240e70d1c12614038e3fe400d329d036e311c80048529c413f8b5d850c88279b029a099c00620000697440)) else (if i < 16 then 0x60690c40239247054293ac0700009beb00f01436180c989e5e8eaa63f53b4390216b8a3a10050060452a040defcb02c81ba4d8dd08180282f1cccde2e0bf87edc815800ac0010588fb817803dc10e5f798140530062f4e5860c281b0482300304063b5223c0bc00c4160169f32b63c00008018c03f16809061408018b120705742841ed9773885c2b30ecd0c2b4c8204109533f70a00be0a45f48765e09a011427c6fb1ef0152e03c013d2a0746addeb10f10143033c990210c97c021419504f81d77440071d418baf75e0ee4693979ac103a3b54e734f80169c5a4c44dcec00a031a46f32039e5984006024812b08de9de783082a0c601c90052480f34c11e076cb2a57c50f2e38341be5fb0400cfec75017fe1be928a0b84300cfa70490191150cea4d84a1b7b758a003219803822071c500491ce3859003ef89a38006568c70f000aa201a2a83848c0104c84383e00504a95dcd2f0d560f2060295d9cbcc2ac03c85d08145d9b50301203c6a362162f800ae0121ece0d71780c5157e000de else (if i < 17 then 0x8d1a02e074528a06a32b80f08902d043580208003e3a227cc0a1ba600200ab2a1fc18de0ac0bdf008007100d29f1b12223ce53e176360046863c67d34c700a6c786aebd0890124831101d36e4003043cc40b86dd800e004f765863920803500042700048298b4400e8d70188638b18ac844230091449e400a325124eb21a7e01854ad01455000231475d156c78d067bee20033540c790e41b0625a7b734020704ca88c00382e73003456200455000126167c000a61b0113c06c249a03e6122438a90f92f013e808e01e307514c0ac2e00b1d1c4904f875907580b49e0673346a10102d6369c180c02172a52908ca619a7c7b882061100280d17d811438a10210e6a22106c300ae90e5c090e04dc02770af0acc02c5048003d02966e8c7058a10d4723c436b357a4680adb8bc1c0ec74ca201211690bd228ca06c000a0f3d58d088010744bde00008c84a029457202c058b704503701742cc9a935d92845000030b196c0b40b8113e44e00211e8302e1d81ce923fe000000589d106e5c0220026 else 0x20d8240d158ff483632ab40440e821a442009fa4d308269905aae0fde00d0439cd15c07811abef39b0802124421a048eed908710581536c144e6ef75ae2188760030043b75783b1468ffc30c017e92474e0022164cd8960de762182438ab2a001c41ee023381e5560105e02f00060300540388fb38290af828771e8d44c03208680c0c3d096210a53166c43158f813846f3c74383a05081a0baa54055d7a00eb20210af607a30206606de054501da106a41906d6d83bf700a00aead9a61b824084055b929eb9b4616f23d115764c9116f294a3e820628180c2444c3c8a9610828cc9b1ad104827e06cc5080360bb13f4c29085022069df0a02b685c20304478283f8fee2a201e9c06c042da391455a8082e78aa12ae280efc0a01c41a10b18463d0498ec7f88dc63f2f924af0a9a90698f047d922c48f0c3e0a9405d105dfef1ca0886d040f620a84013b461f3648ac59a849315013d3a0410fa022e82b09008390acbb80951808718365ff95341c339476d74290004fe160d1e8fa4c00ee4c0))) else (if i < 21 then (if i < 19 then 0x1e29064fcf829f661044c82b62be010828a48a00a7c96316e1480344000040560b8020d90c015c1005e9df4161706005118858470085b005c125018112c76de00b0b8209d8e005027068fa005af2d6fa1208debc00661c2c382004bd30320e1b1f26c2a1dd8fb0066156f07e4ce00116d8c2c8355250f395641ec6836593800415660c6e00940270a88870bb67c864ae111820301ac9c2850c7680f4e03989b238111bb1616a431c3110437ec8daa4951561000104ab082192c1c00ab825317b07400c0987e00e5d83c5fe6026de768a28010cc137238d117af206e42c6250435030e8b577c66669826160021101ce1863f0930e28638244d9a000df0d6d414e48090bd408841b054009782038067e08a1619b885e1d9e017d41d80acd3c40804bc31c08b539f9392144030c8ec82348860291fc8d90048861f5600815c500e7340a26018e30005008676014624012b03a000c6a581c6e6061c6950c0010e6b62ec0de47ab70ea1d0606190190080159284a0762124426a0382c118e0e4fe3 else (if i < 20 then 0xf2028b806e2e071b08008c876d6c582531cea38427806885e6007342aa112a24059db405840c6333008e580c48301011800e6369935a3c280403ac7130340a35198c164a80c0182a3980e1cbea00307daa0ee1526510a5c1c392001e393004057c093040d30003bfe1c103efa11d0752b41c0154555809e60fa7d600386bde03767abb51cb29d5140c4239e27ddf09d0ab8c0f80dc06b743bcc811a4bbcb9ae94e061b2205e41a40100288ab0163fed30fc3b15f791c9e6d41afd3040ea8943a056b1580e60088200245e30f531d05d9264e3161833020c020180e4b180630ac063f819c021874b911f8408289a82668c2e462fa607a58cd25986c1221bb8292899e1b811805140a72a7cdf029c0001015281b8680ca8427136090f4000340625e158ea5e34021828c411722c3039f961d8e64e3b0803b0f5a6530144838c6610732b78b972b2a382b5b750e401398042db95a209ec0cba324b0331e887ff80215e09018408064321a630d5e6c6f40a3d05517a07703a2cc220b6120022b1a1 else 0xa8c06b128601fcdc30a08e19fd441be08d460802981160ef040a39147c37002e7c0001a8588080200a0fcab9f77400e05342002368006664296375051c1a0448ecf6540d0021b6ea1d87c40ed02a07705a13100852f0b15426329c4000c401e201ea38c039106a2a125ab98ba2f009bc01e8ac30d8e2460e180c6005a99c0e8b5ea3ca8d6e06810c02c3ae421418013a021170007004b5be202eb21273b25414b1a324669f625a840c0810ac2c00afa513aaa022bc52be9429d1180195030a2cbfebd00410c6a8108dec8790ba05e8a86a2009b190ac3829b130015167533b5000d330c42ea0055a263763e7c0f0dae8b8c812110de0c0dd191c2b9eeb393d394069eb02a700aa007f7e00c831c837090ecc5008a6a592ed812f0802846823041d206cd8bcd2f2a08c4d062f741c191c10c06838260109dc6f0088d28d04010003e4802012259043018b003620078b41b253c02fb53f46aca7b9fb42047845da047818d01060009ee181b2dc6004678480d80023c001b37db940f6005f0caa32)) else (if i < 22 then 0x626500581efb81a222c03a34e37649de5600f543c7ed8103018e0c1d2d4e0d7ebd1b1f50ab15844869d7210b10bf08280014a70f02780c68c76e57c06403de1c703881fc143241ce94a4426112495835831011bb03c981b231df00103f00aac5611682a18a34c1440440a30378a000424b47370436a9005260d201e92a2f409a0cef80c5c96544601e4e50b411e009b60f3102200318e82a1a48894722d1a5043e810b41421b2e1ee6a8c8725a886305822c0e879003df5830564c5460900dd20274087821501cc59ee408000054e06ff13bb8580783fe071e20d59c40c53d759b12a3a04d40688979f0208ac2a41f7d30324212d643c07a3f67bf467323614359c623b4f7a30b5105dd03042c2bdd4878a02a68c90406378b8082ce2b0c9198b681800868692120100ba0c4195e979c242de5ca02e381f33d00abc01552e986163800761037cf489b52443a8b001740fbb19fc104f838c2ac33820117b6216151c10121f1448d53618a3b3c0007aa05227211cd2cf2c22a818078c8082a4a38 else (if i < 23 then 0xea8800e8c5c312046a122ba50c4aa07861c0a2609c808a042402381440011d88e2b11918a47b068c0f4fa0a27a0080ba4410090009c208102020b0ff9fb205d04c160c42dbb94008e24c8aa8cc92200e4015105794482172d54c538811087ffae88786c85a8442e09fc670d803f4f8392286918247c54178aa8607584904c74077410e10167605e2aa7308330cbf0b12606baba25047c31e05087a0161902870f941033ac65e000389b1192fe0402f312b03350997a11f9d0250546d3de81a9c2470567f882b6daea27d04ffbc821348723fa3d04c041547f884a0881ec0f531206951441603c33581e42201a0b9904ad9a00cbce0360107c893b405e075c0a8da80020c99cd8118ec8ac788392040011d30fc78e0ac070ead8000402079560e601820e604062f8ccf8e22080331ebaabdc8b723350686203086000ea00181c2446062cea03c00c43e40c62407f18d0d818c0f34929570a335ce80127406ee8e81bdc8feda7c060fe1b768029e3b036023cd1a08182a15e80383ed542b000065 else 0xdb40361215207caa0502d82f4629601d4aa686243033c782f6ddb293f442c78d0b57610bf0029ad0180e0300087827c1f0e2910e148127b0d80ec17793a2883560a0379ad56951c010d23c4214369d050a3823f3d81c08a2f337307cb9035b309c1904700c2630eb08e0c057c6382010c0921830521beff467b30a081ec3d0832047ade8c85190c0f1b43e0af03311a0794f81deb30886b9a208a11610201a09153c186ba4ee411420162ec3e131404453c3e00e0ad201f33c19e3628e409c0803088840186cda0458394250033dc6e8c8a478c3c4cc0c8153f26f4cac04381a0e11a2f09d101406610480cc394001020a153100c19e086dee7f237d1a0005f18fd2d417e67dc16dcc1815aa10db024e1406958a0101a00660c7f8e43c38ec70000bafa7ec0225e29490625e17c060004008866c662663358695aa001132800009ca0250702011800d009093d202705c92413580fc3cd423303a2be0c39c0104068810c804e0211002e584405c0345e3804c0409304f17cd0eb998408c90c05))))
def routingWords2 (i : Nat) : Nat := (if i < 30 then (if i < 27 then (if i < 25 then 0x28f080a0202655102184023c617a1278e81049e048f211ff08107c00d180443a55fa53041325e2ec7630600c12c03786a03830a3d100e78e33a241517d300164004b3fdc42daca047d66c449ee0061a186345c08788c50a6d8420b3747c040785e8b58310043e5710f7281d7c07a80c91a1400662ccb12c08c2fb3e005924c81414a9c780124070c5cfc007c6a2074b11baffd0e21e78e82445d35c93881a20944991c07dd7b869f01cea8002fa8a512205fd005e552bb08562b03ce0a01f10287707d6db036290805c860d41475e60d8c531096403f8014d02035eda64d01bcd40c80211151212005904180122b33444000068cce3ad85218601c390f0c0fc4b0f87606230f06820ec118402408c18e9202821a61da90dd4404090292a0024aa394fbbc010c9c603084a3377c682b035062587c7c078610618a31112c60a1a0e06c23222b3408bd601d1ce80503420140d01000a6f000d73a614203942c0d70adb15b7b4e0c07d73d1238088b15ed5bd444018074f0095c0700114a20cc608c else (if i < 26 then 0x4b08112021cd031d40e9804309a604a41689e6941d6d24af6000d8106281ea06071e0c041e315ce63770858500c78a02123550c3a00058a7c07112db246c0006900514228804ae180c16cc2070013e2e54ccec39e050bcf8033ed3362f1c3a300510b378a030601543ac9042374e3ca28b781056970059c242ac9d01ec1ea04dd82087e04066027483704950882841a90a001043a4707220083a0e02c000c020c5000201ef08e5a4e8036203d5630f3c8814eca36926d9bf7560c33020e8a60f15e603081088ca80056105116021c2db7e38b4f5b400d80c60009bc00480c2461b092038745dbe24b1f1ed21800421f1405980a1b6b7487ae088d418b456b0034be9e41f4403f400606146a00d1a630040a68705008a8a79e691ab20e8e1da14140a2e04d0288501659c0ee514c002a1a0863d06ccc04015687c0120c14d6cf002b654829265076d41f71c9944222cb82d20006101e814138001834017881ab447a5e81088e03298cc80389df2340437c655a03f4220429b7b296065064e80a8 else 0x7ca5b4ae0338416242ccd4bd3c079dada89898a5812d00036cdff0c02d000106476182ebd02115008d8ca4404d8e469142b0411c0a0c1fd03b0304c84a7150640892f15e860001f615102a05a51e4360446f23ab81002e7c632e01b236d15064398cb809212d095a1a88806fb02c4a08b593f6f0219672984c68522250174120c33c0902982e6fec302a02fc6c09e807e8008a022f400100e16af8034877dd01cb4f4cbac80bf2be0d4940237a4798388515cfc9ef08f26805a017a200cc0006c3b1180b1a3a09241b1dbe07ec0251404779e050c0680136090bc00aa04e2166d1003d472df14dec05c2a1b1089841c43660378000dc21709ff2b498afa05e0e3719f770060e0287f821987714001706110330b80436368c8000e901952e47e8206543718b500c9044042212c02c006001d6184405241e0a0e8813c860d90c45c6a010e52c51c8e86165a03ecd8c121099ed3c02cb0ecf8530d47a30000374abb1348185c3212d023291834aa592b70202228e0b0e06ce9c1b87e301011a8096)) else (if i < 28 then 0x63da004bbec30b0126a9ff99943de0229028c0300001b6224cc84263de2e0050c2632884e7943848652d7c32007068022c70a82006780086fac8068d26a5a0baa581f925a00990bb3d8a201d81287d656182701e3e7b43c4001027d0181a917841654c4f0103c2be407d05d5940f03018ae120c2c99f70111571d0d741f62b214208a528060c7dc0c26b4e0764a1b61b59702c564f900d00c19daa442130201c83dc444a9e2058c81c3c412a47b154003e618006b10113098183230087a02b544a09f286d57060018c809b02002dd213bf7808940d8c01c007864d020c8509406f0e00510580821b60c2dc01ae61803534204a427ff9bc60fc0160c0c29b470ef9a687f748145250e3ca8200574681a620000847a050a845ce8403a44844020009f83a16d40021518548202284a20b1b0d8b6206183828b819509a1c6602190b383d62f81c116f990182c1d8c2f02158a76546c5e52fb731d653c327aa03f0d03c63459fff22be640837fe2b99c062d9855f93689812000804ec0c2203e6e558 else (if i < 29 then 0x58f038f40327c60a885c040b36640a84cf7780208615879b9a74ad396a865d93cc7b8000007e150135f30862c70868248a16f34b02085a96c7cdaa5f1b20fb1b5004376015c7b67f048e07b32e5719116e0e31dc0abd013300889ceefe11414061083cb1840770321d8c0040f411e508056066d1020007d83a323b1e403bad6ec6cc1e2d0cf5c9400b801c0aa308358176511ee56e504b28c01430ad0338b1d826d713f83cc1a8e23860341a741e45bba8147f02053af0c3b7e1f352064e81bf0983175d76a1401dfd565094845a17f494261c0b959a8f97d8618028ccb91a8835647c9e2e330400e46014206d0988fc0908e4091c39e00205980bc60c82262050c5fc06893de1a2d8df1aa28d40143e804f3dd802349fcb07140780069e860224921fa0300361d40e4386fd0b00013a002044a5985d5581181fc74283c2ea63466412190000007d8d91db78e2fbd1423a9100a51263a98552bb002800004001a63cec20541850a40f7f0025c042f68bca3cd36d6ad2f21f555d21f2e30d2d3e else 0x6b81a800a4520c3b76dbbbbc4e24080462c78320a8b4023a641c0e92105b42f6581b548506715b414078bc8fc104200a3c071b3c579513a5e1a3ec03c8e20754f043c0622c077e56863239ecea36018a0a4e60db1c4c2c251082000a30c70a936fd7c14208681c4a220450c8a983101c8448f506db082018515404498826c901ead6842c318140004bd81c22ed8060ba2d3470046a1ed71803a00441829f6809608c0b8820ac0cef319630e100811093002ab1c603168fa28859486123c2020c4d808bfdb3e1e06c311da823359c18173386b63c001aa0a36234c46c5480053f90b0042d8c70005d8e9763d13c7c0208bd91b9a0556c7c3068ffba494d7302e4ae043dfd508740471f00b52b00c0b5a289bc23505eca90193e91a0a0de60118274921cc829d0f80817a901c1ce0701cea3f81aa3abc1c1f0e62a003b86207a0c0301bef2be569b2c2cc91c6dc60c5483568e08117c03f73000320084231bc05b79470424a07fac887c2228418ff840641340a74c8ac203809803517407a88706))) else (if i < 33 then (if i < 31 then 0xb051f0368c21202d22fef17830490988a241e007208dbd838d60028c4ccd70cbc2826c1802da009272011bd17e2e3bee6d722840084ba03580007a11f8028282c04d22793300cd8256ac26447f326684279c914561c01f834a2cfe2082b595c27876141e80d85a3bcd08672c73231628485ac3e215b7a983a3ac640c0a380436d0b082240041002100f3145538bae0c02d9c015c958368e1e301f10621a77c05d2076a834081d824f0d126907be74c10186c212503f0869451f335f9e7a5fdf8400006e288001350b1b7784003c0076d6c72c132264c08200208a5000c33e630485fac035454010b6464000e0715668982824f4df710209e1bdc70c062f305743c075c397d0611ce701908800cc77c2e98902dfbd94b222aa939ab101a23c0011000101787181ef5f0357080f4873d1a94281c665feaf544042630609bfb223a50023335f80c966eafdf831abcdeb905a810ef31c7d40104102429c7c3bb22fb8718c265380321b0e310ca50216e812b58e4272869f0c143b904168e9fc7e108 else (if i < 32 then 0xafd8733b0c701c88c0ef15c9a07099435e5c711361638b3d14624711f4cde04a01000050081608020281bcbc40a2216c6b0180b970908192809c41a1022418bb86107616c84e87dc0425cf785a08a1d4dc2225c076ac91cc708340184aa44408020043fc1125593340503810a1963b06220104110c042002a7dac7390b29e88289d290ece0794020911283250418368ee8c8186d0a02014d5b8c485343278077fd1ce0fe0120007a0d8ce11286017fa6a89a042fa066039021cb41bdc0704264f453c0c508226820ee04a434fd071e510230742145000ceba8881dc98045544902e10d620f19c183e01000ce9264a14040d0801e9e3714f798a1902c977aa8a08c0e04fa402c66121814c1967605a2e09f05d20f1c1022711044304c46e0481e5c700a4dcbcba1f170b9f6be4f67f8840ac47280d82075f185041f28e700c040839ab55869205b4b444f6030c6530048020081c8401a9c28206b05418008806897d6ba98561831c20d0a1482a0c879706605a4202af9c032f868f04136731500 else 0x546e133938874289990d9020fed75d00a03e547ba9f046c057043247788a0051e3f81994009e165479c5a30f401f8223e206033c9142403630c210010b5a0a55e4304400054021c23c48e56c020003c20ce01008a286061391c30fb6c2007d7fe9081283a01d1775c7652138b000d94681001d3b96e2b681d0d82606861deb9ddaa1715a9e8a0460a04cf5d1032d920298c190690387c2e2d3a960fb404d80677f00303164a2c13042801663a801a26aa1bb6238f5d8e7c068f17e7bc91c315f1bfee4fc0a9b1c7000311405e8069cca129c8580219b45ac03373384108fc33473b4154402410a9080a40191420c0030c011e0c6b8330b0e764447c00c046bd89e0301a04a800181c92808378c08d0363a0c35024001e61001006c9ed074526b70081e0d08038ca632080e01580d31ef87c3dc01bd3a06121951891006c000440db0b7d348f208cfb1221d3595e3d05bb4110471864529aaeb3605868bacb260045b05b0738f2ee919e8220d1e4d83fcf56929d3e00ca805581afb94a4f4cc90)) else (if i < 34 then 0xaea904712d4441d01a818e095b75074d910ce53d3a2322820340d0e6c9c8601345cc36e36c10060c7b02403e990180fa8006205c467c9c90fa0110023b26a0c004549fd4d90021e2cc0808e0740220ffe11e9316c40eb1747012efa975604a98682c0c5b1e9c02a1474958d3500c21e6036102030237c080d02001a0d12400002800b0370080a4591fcd485014c8885c3eb1dde0a00743142d106140cc712e1040551f0c84c300787400c202bc8ca10a814c51cf5c20b2c4501fe1ae100d0af60850f9ec0e1a483027dd4cd0039d420104564e5eb4d9b0040cfbc05d95d6837f55c3c0237b81e21800e1413f1abc585056867843321701c49844402c6a18120cc7858188da38ca06ff8165b3b0100c2e382c8893a4131259b481006e841bba876602b1bd11d39d098a2107c716848c24229a028401e4a67f0c721a220601104104c310d2b940eb6083891705562d4c9913b0740006d340247868801ac27081250f207083f51c0679820c506086656c31881c71c753e00808a1884006080c9001 else (if i < 35 then 0x14732999260b005108faced366c4ef7027c02200a8a2e0fc5e968f49320002f603c40f4a85fd8800b49414812ea107e8039a40230091c014707e808004c11a004219c48098c329580bb6780c2105806ca91d428e4c049dd0af426e011300009bcc02a72aca12ac70406c86a65cb046e666040485a0643002f5235b200e7d430490cf92c7390aea0842806c001b02019b1f5cc2e2bc22f1e7445b992f021e004ac8118c7e2a94d0075f5f904c77c40030030081200936e36020d3e819041deebbd9e00f407144e9e04477e4d5629055765ec02e9415e46a0064b6185d42d76d0140c20a10001a024e00a84e54396a0652d1f0ff7be61e43b8021ee000625f86a80408001c90a411d4d80c878aa182d2e63088028e44008f0060ac57b6c501a4f98c107df8bb06442b8aaec050486a17841003781cbe1b8336e45f8e61b2240a0a06859065459598e0820741b681f69dd908d630008e40c4263f934fa860660478722c28505f0e78c01d70636f04b88d10c10100201fdc0a23251a48405fb3ba38 else 0x6759f70f20581e445204cf94455a1d07a0c301de0f529145c66782111a9868f84294621708c4c0015a980a0e28941e601ff0c000800210104801373419c1e90ab244825d5008715961fe14f8401b048f8e93b0d8040080436620081010f40195cd00428447879c218003e4200c2764304076f8b2e0350002841f18226cc196c0efa770d764996de0dd86d1b10904880040a448404806800b270bfa0e4403de28bd7f6ea18d1c0ff6ea76b2e18b8723f3f301a7aa34acd043f002c114ac0eea816048d11d41c42514f80080930170b120814164afdec2a0a9e0311c610c216828cb105063e26f0b156e18164095e941d281bff32d0c182061e5e98542d311c88998825ca4f89024b65e74332425def64b85402b810b1d7e2db0155002c008009829ae2ae4d1ab7280102c8940a80818e0f000a5271cabd20c1bc0c5a380145d41f02983c801068008018f08e02835f040c97011988ac0ab815f2ad22081e25f33ca13a48b4e1387c2a003ab78216a69004a195010fbf01e7884898f0100afd5cf))))
def routingWords3 (i : Nat) : Nat := (if i < 42 then (if i < 39 then (if i < 37 then 0xe1418be37c007c39842052a76005fe378c81690a26fdb029502156e08b4289218c4676156184541146354bf255e080991252421c3942a39fd41c60d68a8c2a6df01e08814402a4e481e7c04e9703d40e51c054c1ca24cf01b215608180d79d797142165032987c50c1178f970867111c5158000e231be0c0b7b4184114398885b54c0b2d432f040aa0b8d60147610640210198183ec211c0800844e115d0606aba01490d90c9904beb9132f400817a0e0246036e178057602449cde70b1c322e416540e4304f58a448265ac4cd42383be0027c4063020290c7c078602068172a35738e079cff85a424724cac874238bf64c59c032a50ec09400847c0ed44c02f802be21c25ce0ec10911055bdd365e89631454d230015b736609452a43648020c403b8e0b3e760dff3990036035104d389e77c2f1fad8e09190030421adb20d55d2024465c00487e0f1c0c84124141fc8044165944186ed0350144182400121eb411f2ac10076231045805748c16a446f106a483682484c36028208ca10c0883 else (if i < 38 then 0xc34428448c810526325e3fd0e005618f640f0c24308fe7e820c006004174e347d5a3b2100c276922641c77682fd902e41407100c8003a0a2dfb00826d93680404a231e4c43ca0f00198472a39f22a2520208049c7c044c6a003100008ce70b17c85012431c05bd000000b2bae285f7402c8a9470b8380ad00c08800f2a222221e843792843d68240ce0731c493e871856958104e2fe500cbe8840078618ec64fb4d344ae4360b1c60c0930c191c0f2021820013dacda038303e228091d03b41beb5f1a503c3800791a9f721824924c01810298704820ef9016a015480a0341d430124e5b0321c4005c39e0ff580c1a7c026d867dc020a0f1474583587b020ca9110536af4d68100c39609bd000434e1a36418c1800054e42503300da074cd1d46df206b02c01d382010204071580de5354982b6fd2e40c2ea10403901290784212b4b012a088ef8f06831c580c25078d53015008064228372d88801482aed62134200b0427ecb2a5e43380d43e786ff240b0408816e960091282a23c061f56ef else 0x20efb1baf9109e03069f62b0e043e9c250064270d020791e2c00446b303c39a10a00db8020231b876f00021e8018589c81a00f583cefe9c3dec80074f84988c0578447013c03400a4374313d7362f3818146038bcc42f07e55e003078d44e1e8aec079a89c066910c02b07882833202b0215003f7e47c284040407387af9184b60911a97d3847131a596a1c184034336b820800b49a1a003e601e060473216841200b0ec52b11c200642856435e7c6c0d43f6239888c72006095a80c022603c41602d21110ae50c8c009e802096ee440fa629040b27a360866e15e506eb918a453790800ee124c1331b804cc0c711812bac961ab16bf44a083d8156b82610c0404803b088d120d81ef03a01e8cd2708107b8040613e85e0112af51a071c01285d867935aea47e18020c40285b28aeb745801586184c80340e03a0990aa8e8343860885bc2011834c4430e81da740090c28162e031d1bc0d285f8c25382b805bbc43e8e9366e2a14382b1f4b0da400bdca5266f04261400f4e2da4e38712d3fa)) else (if i < 40 then 0x9f32bb1491d602ac8508d0d54418996050530f672cbd1ee601968077d4859410174a03082e3e784800071f361824261b6f661a5c65906120500a6061f87b0f211205138b100689300281018c08020871203a0030a381236b325a34a70c40522001e5800a23250d883445040200ca10259543ec2a3eeb0a0062a880c7289d60a0da2d20f01c00280c8b421288003505282b20480b005fa4cb00f05b6049b016b24270e08e80cc880bdf06045073fd032e1700e280b87140605000666beabd1c318624e819021e00509d0cd4697a2a00b521892c8878a57ab31070c75c0802aca529205000410688f900b85d8fd82c7765618e1a5d0480cb487b290066351002c100480fa0c27d727c4c4a2a2010bf6a91f878107880900a2d4aaf06a73fe1dec01f086b064abf02ac465e4d80045690322c5ba90080068e587960303461f86500da106029a5fc46052203ff922400c04d18a0c2e70b37180268007f3a1108105001a146856a2bf00667e17f4186d714080204018a146e39bc3cf04f0506c8af00 else (if i < 41 then 0x5c0932c40183ca7e90555414000100b46a350f3e690ca1c8ac0a58e7de80380000501131e1c10d046000b68f07338dc71e708e203b0801700094089e0023192502041a000f440bd5000e103ad001ee5145ffb67a58010844b4041591e3504907002028d018a66f6f0643e1f8618482109588c80f58505b78e448df777d0d0e121fb83860ad0220018665fd3bcd00701a26ca00ca2c50420001343b6d840583223860c17098084508159e31498c05c088485d7d2af18dd302d680bc18462561567ffc430000b58276cd747f030c80d914a998b51baa006adae02959d80898b829acd29c00d0061080aa32db82007681400066c5072b4001d445138a2e01464a7a6600c29dc0e820541479b755c0000060816913787f6488bdf2efdca7f01305d9d010d00598415061c11f8a192a0101133e3241d0a0a38c60958e679836e1b8b0c1257a787ab08f298244a055879a86460415d1dc01200870d4c0b1d80c179a40384ea4101211db80c3e313032081a1804887804b2118d60e1a301570401aa1ab else 0x6a3b7e407e10d732d8bae1991be6502020148013726b9029110495093050db3660002a2661404010ba33840c540a163b0801024d09ef6e09c360d22acc6f3d015460746640700cdb0f81070ad3401f31019d463c40a078657e1d68039283fa6de409cb470b7044103c60d34179eb011801e16086bffc600aa8595641a4b85b87833fa462484e4610703b07e3a0085cb203803b52005b5c3cc763c3fe45aece8020c4d0880303c2ee03f205a01575325cfa400828e3b7810c2034bdb0c80a408e01534d1ccc006c5746cdda24116af3ff286f903e009cf277db1881f8819ae17e00a06fc5787f2bc0d1de218880051e104447324ff3209a00d713b3a021b01da03918f0d8101e86588000c54060c32e1179edf7a00f30a00ff0ae0c40913d06b4d808c00190988120c3482008c0930a1d0014a1200c55b0035f703abb0c280988a0ee84c88d253225249880964974361904cf78c8b5d34c8d320109d8c03c7d1bf18f3511c01ae2290c018a07f0c2891b71203a38d713c62000eac026b0090f38))) else (if i < 45 then (if i < 43 then 0x30180dd8c5123b60e04021fc088814fe939acba58062a380807f116b16c82fed680971b0d2c3f80a5131c0037cf2d0201fa408c4183824a08c826426856c10fb1b6958435810965e951e306f017a0403e0109e1202987ad0d4aa85e008c02cb7d8682a481000cb005a81a8f032ab099f008088180401e6fa01cb88c01835354180bc4c963988089e110226026ad1019bc81c0f40030014a8080254695b74267d4028af4eb4000138d8540fe60878065a86c3a0f405e0a1aadcb1726507c07c78c16971a0d06e1601ce3b7ad713f031f342c1967c52d9017f32e07df96a82b4e078f18717c242d96644f1fa41d9be1074060124cf2c3c8a000201f303f52064301441b5283637c3b008154c2b23e7845f58c225f8ba0d4106e98cd05062100b832957b08703fc330100043d42cbf4026910220673dc686f0058d3007a08d0002b87e423a9c5b842194081fe03d3a3005080017dc7b83cc9a006065da0804050be3acdd613e4984211611c50050f847e1030d30813c0bc2804c87f95eb81fe0b7 else (if i < 44 then 0xd0259205e60803c1d02050027fcc0641f0f24b0106c18417de8c073d5d330528412d0ba94181800f053311f9dd2a82cc230a5b1c8202a48e48f900d817cc8f906e06501008494153e0597e11c64103d1780e0200806188272ec3401102c7f0f516f6064058130d80fdcfe185f027222487008186a0c01c031e56e21d9210a400201220860ce0121e2197f00098c69800ab02d001e03e71f502c8659a00641155820041808081980661081201b1a6343f70283c281f81ca6628d002d018ec30207ddcf2c9c186e95400d0d003ec0174d00e3c893002f73e21a6a1018806aa7911c50c290253207f906808d2a486da542f5c804503102801e05102880a016514bc300fae24a062534d4c010040b80b1996496b80e901d2b8a080e0f40000fd2cdecc3682c07753b9a032c9260aa88e5e30dd4a80ac8a021202e067ed3be0100080d5d0b10157cc08c0046f0084073c64e600dca05cc01befa7be7009c79053e840a818fb6e050351bb0086880c64993c08835a818d8290385c62026c6c85eb0404 else 0x407600808d20990990a07c5810c0f862fec35c49316c0b55618900e930181a84320a6174fc09409dd9cd41f188fc81b08290c1a001d312805600402dc026165b382fe00c850c6c3f410f8300d100721346c29cc1d181a838d0850ac6ac540199102e1cf02703b8f81070748123e43978080160f020a8665ee2d0e5c3c57b6c001303c205836038d8b41843f612f1e43824081aabc4ce0d0e550483c0800f602ed777c5de1a5d0454a19569ff8204c2d19af1b0849833d39df1479590c2afa57b830ec81d716353d1a707014838000f9f1e77f09080268bfd0d15d1a0433f08711fc18bc45a0ad082b180e376840708ffaeca33e8f010dc100727c3403d00ad5fd0c7f85100038c3b6148181d2edc1521c4705a84700a80e482605ae012a6244054819a846b58824df9b842962c065bf9e81bc4508deaa422160738fd8b850004808fa090230959abb4ff14bc152daa847000d3e08c48196a644a894c0d13c01e898d40819769fb78ab2633a800fbdc0808cac541f5bf85888005838042884787)) else (if i < 46 then 0x369cd8180c02e3745ac03d3c2ace80c5809010002884421945af6c33dbceb1d1ec1afa58f2817870703b4d816f404004a06f9fc856ab10460bd35f442ca09ac0618003a036045c1d0d70311010e1a83e0301b0084e90e2082a181c12284008a97f53843354ba807c0657c1091713c4bd96f816800708941b0e836880e27e8b261ae0e6e80583a004b008827055448a170813ca0471412c44460070e018a83ce07b9b4ce5c30d61b44720dc97366e1c60d05c3a002510a063043253c63bca983a4c40461000a9c9016d116007218603286157006028c0693268dde400620544810240061150062be1f7cef600e0b80caf8f232b82501a02a34810428c04129e50057162d60b00680f8c06754adf80093e88039c280c8e2941b2f88258aa00241fc002800582020025cc24466115a6c450010abc2688c80e14048b44dca5c2216000042a6e001f51371a9ff07c9f3a0a851e80c5d05fd086002d2c309d0034286f887808501f03a1700e3a3f1a0c13048681e010e141d7534ca36ac06f61180098 else (if i < 47 then 0x7c3af8e731380cc4b9c86052c04d86da101501c4309a8550c32a30e183c88302206f0058778901040e060c00a23588509b01738283d06604eebb011dc1c0f5808a46231250407b62c016741480000ac0888da6faa09810c8062917b44fa80407240aedee1381157418b0968b6c30680c2019fed06946d000df9251a42142825d2601d2c36669a88098180e0dcc55f1730a6e0e00200d016d59006002a05bc0cd0ac1001c87065b809d7a083c9a551481c11182df93100eda40c2000420c60340c949bc214c240fa4975b41504a58c58207c623f103296b9078f02b15f042ad8ab312106a338ad90001c6808e0f74507d0b11c0105586dd835982710a5400163f36ea438ec309f0043a0c830041b26c3f2b83d000239b8f023cc230014158b1bb0865c40abac25f2c40010cc08feec8183f3b000c5540d435207a02f5c6cb0144891062000065cd0db21216132b7d27580c7f0b468941020cb804200dd68054812032801a30018f5818100201d0184e0a840ee1789f1a7c82aa14374b3003a6c2 else 0x585110c2000a3100c8f968882d08b9414a7555792e2c0001753b000426385123601836d1747a8218314735e72d0d783956fb19af850025f013030d0058f1280076f9d921f650ab260801033901c5702a7ef309390cd1d026040ee81108ca19614b00ae9fb81902b01e1e2093200110003026e426091bba48208a938288c8040600278d011d6e1399f0164d5239e08f196000c65854c0217628f7d9c2e1a86a1af030e80220036038a0001688e089239b454057c0035030e0c07063012c7ac276be01504e94005850361c7ca41b403a24f0087c927218459915f7eaaca02f41cb5b6a87c0a2329d387181dde7e018541c64368041b1c811cc432d9f3e005c30f580c30330cc006037713483ae714f0c84224d200808278e06d043975a062db729490080185e405520676006c2247c0a8921c835531e600a144b94026301036080277da0001af37104008c1c828a44dcd09024200c5080d592382001630995e00391c210036e1034ab0f6781e70a621e1540e32ccd001850b5599865f190e53400))))
def routingWords4 (i : Nat) : Nat := (if i < 54 then (if i < 51 then (if i < 49 then 0xba00167ae5e812e08600145007fc651339f4021101d5bc09420498040350231d302ae05ad19a4405dd15b08805d400821cd885cfa09084c7b0700e4430830418001fb702fa020041ed6ac6171fd45aa089b32820022405e0a114c5102e9414804f54017209d880902c41081b45ccb852c13800071146608bb7382e605df782891580ded60c87ac3f1e72c0000836f606c5010c5cf47882529204008042d9d1351d01450f70ac06800019208169480f18b029b8a180070f3253893f0c700198243b20759c200ff89b11e53362e0214a11020a07112a163e91188800b83160324f82c060237254a730dd3049cd8038830f30606185480f1b0c7487810118bc6a4c43004016059ae08840b46d8a20069423602380002d0780201e0583ea01d90113c3610c180333552dc1440730c53881c315c098a051862b208901dedd8204d8e13b9f4b29cf14823bd40e05334d8fcc60488c043f08952a40078002ea01c27aa6ad0cc62ef7e8375f48620a85e43b53001cec650d45098803c40fa071e5c2ec6 else (if i < 50 then 0x3834b6cd4e0da048c0900a051503fd0265c04732c0fcd7a55d9619638c4360f18484811f402e00aed602a031184f8007241fc603a0c3ed1110083e0740403fe800fb00121d637e02b0b068b00558b39080430e11682a1f3090113c8fb5a8522670884593d9c0d6de558aa80b1df03ee980f3002740f5c028a3b660f0076515e4811d0500039b01d391fa5908c03c66f8694860482644110a6630b1be9ed3c12292534ae029e30027efb0158ffc3e001005e650a6406097080b4d785a041c6e0743462011508800a406070010c1d2064820100051f12e903331c00933880e06600f49004596901eea0a040310200219a8540a05e00ec21005476390465c02b2aaa1420ec0cd5c78c1a1d10e6d8c10a310a821248c8e0e31f6018295c433aa05b805a0a04d10600835c8002800da51302707280c2cdacc05a048007d4106f5106859147b91118a090f01d0ae19063615e8540f536b86459155d8f94082402f06102041c7043ffac2001b2c6a4831a000093ac862061538020d00d8b92ae0502004 else 0x3000200064d8010480115593f0d01289fe10c038270571f54134500dbc247f323b42270e5b0004abcc2808ad5723818f429e785b81800c31edcc01c7980347951c51246301bd483a010b46361180a122b5486b760d258c580140e42c052df0186420080e0220378e5e653895b90600940a00e102288347d005ef40030540a000038122dd5c37f3f780023804d0e45043000e6a39f3d8dcb1d8b205f678243ee0e00703e718626495afa0054f8007da0004c76302358204695dc80049f73590ff82f24624c1faac420404286f13948614de0810e0c6e8b086c3cf36b197914f860003e0013f5171b105e4a39c11b3aa01926026a23e60208009a10040700527bad1041c3c451a46151b11d8f87ae10c540002d002f9fd00118428a1600048208f64322872b813449621a044537c60916784a71100c05d6c3555f645428160dc609662a0b203a07ec8a024606380060648617e11611028a222616c081b01d518783523006aec1761e0844714ba4052c1eb7fc3fced438268006e02a6f6aa490d47)) else (if i < 52 then 0x496ae0c0d8dc7e0a10009e218180e902eeb26fa40a7a00186002f82c9e0001801a091c8cc205ee06dad55a38809117a8a78c0502c2c581b70402a0133eb0680c01fb159e2b7801001e05451180218e0984f4a54374d044314960d14a8790c8d8108853e20b03f8440764d8680200fac0c4059000fc31e8d20a806e43cc5be247b408057804a30c3178e57052034cc9f825830d8142000c3019a4981004b051a02d2c62488002468dca1c0d810345e1e29db082040062e0f2f2008cc780144911054b1d30bcaf08d1033008c72bc5dc9afa42fe5008514404460edc010d5f300891add868809d02981c9a15101fd083ca034000358281b0eb043010682a0897068ea280dc05523251a40310043f5607d9a5dcc2045d024e52280fc60003142b285a08d695e3dc8185fa5821f0da547c0c913878d0f1025121ce0f1cf1e825e8e40d092ee006a809f604efec07e23d96738a112f7307957ad6b56768808442030438b400739899ae220c0040513813d088605000637bda0c1a505c64520c1e73 else (if i < 53 then 0x8a4ec5a214391b9bd01eb07b0ef665a55d8841e3be6b0f9a43f3074830a6c35743004200e09140496492704c0406548851a6ea0d3184e030280005c80430854428d0168018e8069862762eb9ca38ac72808d8443c8d300c4d21b16d42e00260721ae2400568e880ac2987cd0a1c50bdc59688191d80182fb02f1b09902de4b060baa055b0a0286623144b3904d38be39d8bb55553018e24193f4b5ad4cc10aa78e090000a055dc806c440e005c05296b03ce4182e91bf8b8dd186478446108a8052468435501a101800908f60072000c270a1801880da12023873fbf8068d09a01ec0d462000b9009a90e850e0313beae0073f400000218d326db143c1868279b1c1d2c7702bd0a00860280650a013f09402c416c0763238340031f22a184790689910188a398c22efa00a38078048e282016393c38809e00c178947a2a3604c51010e30f052944c1c0312f0570b7d48000b8e038c580200a8e3a0ca360078409038700e1854015ca180e4040e1a672a0703a1c15202018d4040031037c2d415 else 0xc08798e3f921038483e376530720801426c6a22f9809d84049880a6e8020fb1dc02f08c64131a34508501403f00900e99489fa324c2160001922120f3e7642c36244401b424160111095785c86cfa714b3e800c20b0961c0dc7613670ae2a45008b91480102643c184d5143bc8429083b940b5ba01ab8a062c98c7a68e4b09e904d100a00c56130f0581d18d65f387831ab0bbe60cac61e4f01d4961b2a9c8e035fce60512654138218810a009504c0d841d681009e4171db2471c4c178013d35d5c0b98844820519d506b106bc10020d20f8011d2e251bdf80a104c001c00100b020101268e8542061d95c48010c1405c2e10e48c209692793080008090404c002184502212f99339801e806c901205d6d8d54abc0606d68580a9bae6b70c4ae38540ea05010d2109e032c56000417218078f863802b46c2308020171c6600106b2f3724061c45e03c131eed00ce082a1900861ca9a4074c718b02c67d2a8e40a1a896e0065dfb2804de6c300934076b40690cd4002eb9c40ec80f9e0205f18))) else (if i < 57 then (if i < 55 then 0x7c064136bc9006ff4d783c051ebef80022286984004e9780659541c00829caed0603f2cea1c95f0559f421701212a34090de264f81b06ad76a0805fd4c0402606968d6fd49d833125c65d0a3a6477338281a462ecdf11144939613813b5ba615040c05031ef2200a5075871593bd95aab071c41027f312186a0240a334a3453446c273f00d0405e4f60de103d4a401d1192468fdc2a01efc2c130ab061f60b110805ee1cf22189f2de8e817dfc50b5d542484edbe00483a95aa0a7a0dbe3710d1048036889400b84721d4600087568606560809188573b3044fe2071891b0c01e43e0046628400364098042a502001b8b06610b58c814010c00efd88ee7095a3e20b1d6a350f7328410ad04280b840834d0635d3db91d8247008e0209b1950eea08202a4314540777aa4c0ec007cc001a5031f7dd1003fc54b108383823312c00e7006301cb4ab0128800551d0e4eed9021af810104a29c190ef0599190b8404064e49865b1340c2ec29833094155a8086ad0630013c82f3ea83b40701af0e83 else (if i < 56 then 0x9854c0e61874085feda2c00606506e28c820270812c8f92ee60ebb042b6b6d915ed8edd0c21403e91430c01c0ecc601178af990f11825120040e9c749414004f559009e3215a027a02150bd3d004000f081356846a82d707412c2402182c906158fd05d60c609ddc8a03d478e521123f082f00d4054003ee18e750b3172630c1cba8768bc801c1c2ec0400011a872ab62a7fe120b86c586c7c984bfa0164460227d02811090003b9840b962b4011c050180463e2045ab0ca5806d3792080f02800800a0738034d67674840a20054089e402092143c1311a0772c2b88a3641a550278400841a2fe3162063284a4317f2d8bae884aa08e330190bea05406a3062a63ac401b71c1c07648c236f240105db47806c380b803803dcc8ea01ff09e9ef2aa199052a83f2802218249b6780301f99410817d3c38232a784500020c60f0ae838102747c0581f46c3a200556c6208833b0a218d8944a190c3b59874526774101ae077171af94800654a060a8f4c00c118063c858a7930208161043bcc00c2 else 0x5ab000000281a58020703038c32436ee4e70aeb18b4c04889b8e258903060ba92a41de12018100adaea336d5e8087a7e8f31b62ef0fc15742a22ac1d10058304804603acc11591c0038cc28a8795020a08d1218098660fa00af7032bc00b2c01a240c205a0803a07df488fc253425bcc742ae260f466de38038031257000cd048f0c6041019e89bcd04700200705020200286377409a806b464d10b0a42fe878305a54478aa2cb60a4bb66878c1b22303107843860d74071b0e80480e82bd10c75b0003c8a4a8344c02977bf04c80002a290fc6202c04810751d63a0200f1765ce3ea09ec874bd78008252001c008fa02859000870ab95d28c12d012e20a04c19084c332031b3892b195364800c0b9448244b541004a3337b016800756aa30d64c3084128438010b8402802c3300431a002b00550a6829e62198132801c0e48c1d1200414924be1a0819728e13640845ee5b48ecac5e0022a5795b618061d44c22189fa93e18064651eb72e1e7cf408ad0400cf0c5a684de863018de10000758)) else (if i < 58 then 0xc32852415c84280251420011880807a13410d68f8050fc032f2130a31780c6a914a6dc46a843f4d02116981990190828caaf81128c20db270790038142b85a00de8aa901674047ea20c084b9403b5a0ee34003b1035501049c3417178000c48e030051502560f11aa18d630c290211c85a709901039dcc4d90010000c500850b5e7860551aae05c53d4cd252de907a8087fa04b2d1018b7c9499c2cc2c0a81a80502024904c6926578fbb145d41c8d6e67fa40120620285ea22978580bd3088184560b68aebf01a83f820fc2208034070e9f01d3433a017107056433830546fd30a62c0c343bf03a49f0006ce0056a0506c9604001d3192d6100ca817c96923afe8010145000182c3b7dc04ee04e160832993c0c4b019026830160215010b9a02b3c82445cc8180d0033120480ce2cc2a18a4c2fb752000e5f1c6436e404436280006a91260903b8080018a89ecc5801c14dfb81e3f6128cf59ff15ac0818fe4033280bea9c708c00341a77f883dddc357e8804c08193e50df9c28f580184dc else (if i < 59 then 0x53d60ffda0e327de402e7e5c2a363cfc003c19c947053bc3630d1887e6061009ab041e3a22801700734a7b3d47280939380a412c6c800921b9b6301569a84dc07320143848d7a09d5f9fffaab400381d0065040162c0ca1d2ef0a098fce0683e100000e730c0bdb383880570801ac4a01002198844e9a0a840ba00a0062665a972a380ae185100c47a748572412e9cbdbcb551080e981a010017d59f226047002ac7180f780340130dc1ba50dec0092bf20c163000071be56158a344c5a02e8063060b0d12c0255087b02895540ecf5bd57800589482a000c0ac0081b1d8759114040228343a3ce85091a15f483e158b74b12870f3674e3f138e952333d1c7c074900990c96bcbfa956a1006a9c21a40605f41fbe39ac750003960c61fa30fa0b48081aa0142144411017b1f37c05c02d487dc78240cc958300980816a38cd6bc16cf0302a161454f01000da2161e0ec3e02fb9ad0b137602d74845640000320094911c0f0610a252811440470975c469058814299d23d6c11af0321f3ce3d50 else 0x400437232df043bc86700765815851468f96340c8f180011ec0e04497d2ac001de63f5f0e9aff07dc008c3063763610384851ae930481c00850c0142b00648745f877125f0b5dc03242ad706c9220248b0df0e45cc06864428741f8cc0e58283d80075081ac15bd6582cf211b33c02a0441e81838292928243063cdc14c84e0420630022d90d1016e5ab628a690341861255f03024d52392930b70084c66b705d8430912016471e8c00a2c40623863543848fbf8758c30c6c2830270200aee5805a0002a0812eb01990c71004166be7f202f80575b018760bf06298f41805e700190911e2156c37a42a2a587e7156fbe9641b8643f8008f653aa00180c6198a1708d6a8483846eac11319035f77b24efc0ff0e025c66298980856384cb038540020c160111f0f882152400698164c1d1237f8712020030fdd6ce2b04283a80461d0c3acaf5d206d869a90a659b0991f900c06b144dc71740a0580b433460184117050bae82ff3437836000938800638688953fe158741a647847a020dfb20052))))
def routingWords5 (i : Nat) : Nat := (if i < 66 then (if i < 63 then (if i < 61 then 0x330a9180e25013fc1c0020544202f7f160cda3030560c4308f000e711d43461802c73294020cba00243400a772439822070ae8281c0e71140c10dc07412350746470176ffa01d581c764a31c0107dd0211cb900ac00d11c1180dc2025140de900953f000b418ec1205e0cf602ca80db642a590640952d3ffc4b1c181ee05dc2050b11021104ad178e5e08221c15041a3c0000ac781a80b18f05912f1c0564029236246efe0f803b1ab0bdc011400266c2000796036428c00a4006a0c00810a2217880108143c0d4491e86d0003027ce06ce08553417bc8317ac50f036e7a0647826c0390101984829024e06052b00c002699501879845754822886580820eac36087404b08f80000805100c7112a71b1094201d06f14c0c1fb3ed3938290830091240508c200180e850800710a48bd5d1743e9693e70b685b0632a03741001903f40ee61c507795c3e2435300a062cd3b0079fab7c1ff4297e382f2107586570da6402429dbea2ae790830c2a03f90bc0b981a5b80608bce2020411880bbddd else (if i < 62 then 0x68c31bb1c0902e6051a86730fba850ae3ba4ac8178260d3028ed80137126012da179dd80080381e18dd15a913133e00fc0142d508e22cd1c040a63aa3714322dce0c271401071816393a08020f181820f00611057f20334ee9de231280d0205246606ee0718b7b201146f90198ac72422818a00b3162018664f85a07b55083e02bb022d018b2b8542b9748016c14004a387b2bc103a800c43077130ec45550801c700ea02a2d6d802708c01f5877eb8a9004024e33e135fd09a530e851464b441ce47c03f720006220d8b9a0a5220c70a80ce8267e3854cf624a075c44d8063500c10b34ff61340b01d0020d083a20694c9a8c385d0014e0a00817366544b00445f709b08ca042e5c01d957d16f89a0004004af2784ff2063789251aac80003f6660e583d010083e9228286fa0b031dd02a810a9ec08042a0d8b1ae8100b031d920ac88c50324cb0287147b459ee88870663000885314f02a1a2511a3e08196a80f82846083a00a816070a0aed860945512257f010c6c31cc14475e1ae82088 else 0xe052ef1c4000008206bf2e0c2009001ab43ae04177c00f1ec42756520f80dbae1305332d8eb03f42f19be03e84ea4ae80f03124076846903572cbb83800cc294e6401c8980200f4a0d8a511c4cf85f84dd037010197c48582a53958a1a08e0d3030062c789e04700563013e00c00430641d6e0c8180108605c7f043816c4e009818768c4743f598d0c934230e38debfcc18c6529012b02a4f24071f0073a1e410fc3b405581ff2d5fa044c10f7a89cd6993801b86740cd0e4590b263db104273abf0271b882083f2c0a9528b7089eb5558c4a270eae07036c131b21174004c2680018ab82029a0010017e2d21400c0787c71912f319062a02880739524e1a08484225a82d560f102e851c0e38e665c4103e80008a220b987798674d08842a8043fc0ccadbff0c2403f1c2cb9170f308b8818e78c858f0540e10816943df4a1018a80aa1688f69263025101856b330605e04146e105d73833172e76ddd821b0c2dca45851b05e80f800c8b8c501f04eca060f962c140240397e6848ba58ac76c1)) else (if i < 64 then 0x8a901e385800dd81ae8134192010808077e060506e8da8f26ea8c1062b6d523c893b2c1882fa08db0b1022a303d80e46119b3001102c5285117881f861d14ba3048460bf3e8939dff85a4646a1c60582063793e8a83164018c5801a023100e201500050280470070381f8c1741ab5181a025100d3b1981340f8100154a1a32810512e600106449ccf00c190410cdae06000a1861118400c82676ae9c4d9e0c0034d242f059810514c188650809a904240058b0c344ce00bb0aea003e79128000e0c0ba1bc5f00009e04000d0c7f515790af04030c7250a9c238638744c200f5cfc433007727c062c4c00829001ed958489822ded5000c28e2f1b3c625430045339441fbc2b5869f26c04806d8dc4e0522074536a5471fc4d02350008686b368012ae3c812c407670a2110253b99803c031ab0027ca4f1008efa1305802015ea13f75c210c000861850000dddae0a6812148b501ed1e648354203df756930bff212277fb08c6f04006580b81709f0b93820838915a7888a1308f00585817cfe11 else (if i < 65 then 0x8051bcc7071ca4b51a004581b45433308dc0046e013840f0e031908525c4098441238828c0a11fc541418eaf5f016405016797134808200018282a800cb26cece40662de138184e224fa35c21d00430291c78168c18cc3bc60381c08060224425087d00b8acd35bd34c8953d63303c43a020807e1041e0aa420a2b9c5f7054102a013376ff33c50718e8b90192212f809fa5c03e5b803dcf72411b3be0a230c1ac5f228232178200ffa97f5045401885ae2a7583f408c310222900e3380e9cb8243e8011f620402caf0cfc30a1509365500619cadb1a8d201570fdc2ed591d1173360670f7e003000c16310005460c03c74d4b8b6594411a1d030b9875005582022b15f405a1408d75a13c002138194d2440301da0075263f47b902cc69843089eb22eb328061c04d0800f6075c04b89018401cfc41a36fddc8c115730910100b4a48e1461500354f711483b856c731a0a0a3f21b20d76c5a34188db0890eafa4e0012a0061582c1cc08f041501804e4f5bf6000a91bb02d0a3e4352c1c1ee58 else 0xf14cb20039a8098d887adc709c4b763a60181df7973b3c01aa0740f0f281e1000181e03e03f03e2e00d50dc0c6603940ca8a2b150100370416440794052358423ceb538f431e8800a23e004d51c814a6d80c0e40600493fb8f486c388b480063d83568c0020243649021088b23262423bab22581044ecee3b6a08dfaa08a0a68661284405aa92100860a7ea6203c77e81d83c1de101b000ba06102100d52004001c4ad8dd606ca0e82a78cf98d10c710d00c6fa83a31c07aa4d81fdb8b00b1bcf0201100b1ca4aa20614d54080008a100252df80db081704e30007df4280b47168ace37a641e196728a882958be0129e01a34706fe2914deac03cc05c0e8d55ac6458da63060113aa680d2ee32380d42ba080083074808b06c03a0015820f236338720600e29ac2205fc8150158828548ada0f02d72f8e1ac180171046a05f80e20c0e9cf583628039b6ba2642a61c541865ac4953b5402128181800ee62013182c8113464d103b6860c18418010082d212c9970718c28238238cca045320244))) else (if i < 69 then (if i < 67 then 0x9aa6406801a08cb82810e398ad0003e3da028c8a45c168022028846033a1f8328191025a002a00000817ce4f4001fa29cd3058fad610ad859041b3f01f01a8902943178e808801e8927814581c0811f70cf827e9c03af40490005814550c0d001f8b05fc00870693104ae0317290c0c031ca4f844313f48204b9cf03547002aa3a55dece46380024010074cd7cc88a0a00d0c87b6918455140705f62e3f013318227020848c70faa4034176ca630f8c269558015005239726bf743b0281c4814c7a18b4f831001db04a20b14a271a0e500e6226f85404480605bdaaba3d0239bc1ca7816d5314dba35500ffc541f84d66bfcd000c5d58023ac989b81bd9fc0b91cb5190300e00628133e4532f95976e0dad2c60470344e5b52c41117cd038585696bb6028218a3ae021c30f0e48208ba084e7a06e032e039012fb67b1095bae0e9bac9066c1cc040536a142c18b46c1d02b3082920e0767427ac14410606b3e41cc3087082e3c18748a9b2230cda251882cf0a06aa200423082f43d03505868a else (if i < 68 then 0x19be8abe8c14bb698434cc84d38146a189f81c9ea7e0111ed86d81fc1600442000a1920405e898028108005f9df21080e02630371f03be41c42000415af81343ca28740a4ac467a15710d88c86388be90078afc2582901b3bbe29d60081ea46799a0007f968540b83e0350ac3bb560400e352370d8c3b80e0f6060a0020539ba160d91ba825369b38030340198a081f69016804b51f1a0b0c7a08f106ac1067320081d51e2aec0518071008358200427d6c00152afad0a6392000021286502c040014e21423add2bc040166f800e556c51c49bcf580531824003c00109265c01c80a72e8cc0405e4400e40303f02e16e483ec2c00cdf84c1a8c93a069c003682462c21ffb001afc2b9858663954304600205a37bb320b26062381c50dc00000b3040103b1138001c514d70c3591dcd63e188d1002af5e0b3a90227d580567df5e6e0f140370048e4b46ec80a51550d8b35083c134195612c683f5f8028603f56f20100781411d228090d44617597080c30c1301f61c15a0ad28b91d818e295ac else 0x9c4f20221b5e10f452040970bbdf20070171410000804028098a57291849ce031de894097d184042600162d71a9301d8c1147018406d38a0800be0803c031a689403b8b43000706010e800db674c0800747e88107d0da388229fc66f9443680a3822efa1002c2b0aa01ee21380e9e2880668271e81c02a8427211e020120c714010317981104530108b8c34c04181a07cf228820c8050122783631509df9157ecaf3de010686b78482e17300101003048e40272761fc1abf66bf8501e785e78d09e888c4178711218021fb6e74029f00c9d0c51939821c7a9a0900b836fa03820c20280a270cd9bc630c0050fcccf199801c307d42f0d85c01000011201841b0d48d06b50e6f368eb9c53040daf2a82e572b4b2783080482e86ed60b3e028a8090e83c0382ab0010a7c53fe3362c5d6d0180777fe48419a1c9402800a029840ec540437a120c04540c73c55120051f903760717001a6c582a48096ba1ae2c2840123d021502e0417f3150168b4038163a01a433e007403f1d1c3eec240c0087)) else (if i < 70 then 0xc0c0040083020409b4404c04384360009728000bca200b3092152ea9610e5a3275c6e815d4030408018840608028e37425f5856868800fa87edbc401c15e801c600e380c0f8bf06b8bac7c1f7bffcf511280600ec11e65d769627d409efcb03433315244802c1e59b15c610010cd20c8082b010090406dcb840bdaf0e2861fafd1584872360000b0a4401d500ac07402004071fe207034007698b60660fb07385c84006cc0a8180b8f14a24022400856109318d0141f424408357a0c06404c321c97f490791f395c20ad209ac08d7025086402a06ec7080927c04b85e85463da2f46f9315cff617c1522050005396adc0440005d200008dd8a042079c17d4014108a3c150d55807c05fcb0120d55b2af228578e840c061e00106151ca051600558098002f97a415ef27676ba0b8d3003026a2a042f8a43f08da1e6b161750252dc2793d8820c1b00c6ae1306ef440fefbb1ef650e0f0002a21ea04014be384517f45c830200704b6d83ec981b5f258f477d06ee6306428b3d80fa6dba83c818 else (if i < 71 then 0xfe00c700bf9b8684e7622c29882040523ee70471d89602f674f288fa8803e9c400006dc0bc2e09106aad55a53b3000c024283cc1b2d842f4061afd411c30d8517146c04be070b4863309eee6ff9312618710c2c0493667107fde8f315f00264021c62080d8816102eead9b810a04801170180ae30c09e025010902404f6841217ea69edc230c41205000d053eee1b281a70fc0bac2004184e0601ac2dda28e9612c0f756415c0414544995d4840ca03d187ca005d454a823b1d188a890e2712c8ef87902b0ba46d90032044138824030d0f86b3918e5577c14002c20d171580182e3d16f4020401bf37d08a18807729b35ad08187c670276b360a4971519d504746b0d0e18ab900149820155834415a50279510558009121e824e22108ee4818cf08984c6c30b86e03e0309d50a0030e851bf0cac80251f85c15aba800e80249d0ea0401498a4362ac42dfe3b8059e35a87088010c3dad4001200206e1a6a2417c060c68a24c707c200f2adb8ca2d9005bcbb06c9ce8c0ac0050183a38800127 else 0x1865f8fd8e8143c8051201a800d34739073aa80a19a2a690c681df0c6403002f43c0701e9d09f060f60612809e034ac80261f88b5070a95d830c6133005f1f43050d8880f0a03018001fac0400b0e3f6860820c502fa33aac083914ba9ce510b4af0022586b45d01634400cd013c38e016438229070f4fef8262c06806b610625274fa0000b64ae5dac6148e7713443c9c0e5881b1e81000891b8fc0d80421f432c71d0b0ac1c5c1801d1a741cc419e028a500208c00d22cae0314082060723ac3b008020080030420ecdef4010072745194140086a304c2e00ca4642051710195602190ed189fa21e87718f400701a67c0f20400015ac4100a286ca6680cb0a903c89c10a4f834343324a200030003852d435557284830c7e476fec0200ba7e5ebe103bf4c5586e1c1be59198a4794ac8a0e56038d80c186462563a10e35db005a447019262c537c204605a7462d8c0080c3f27e418fc71d5620752841e5408a03d136017038e14a80c80a0659803cf085406061fa20b4c20b7163de061e694))))
def routingWords6 (i : Nat) : Nat := (if i < 78 then (if i < 75 then (if i < 73 then 0x1401e8018be0940fc51ee0deec10c0494b5d0a21311400c37640c111c1804c05475b1100dc08264caa7264334201e00f94924943d00ca4017a0b099afce8812c18f4603c4d083413bb4c04003c5a4002ea128300e0848680454110f582828345004e486a3c981d879797c1e3c9e81c56817bff88006ae188408100318dc808602be1e7830d956022ac170bb278f200537c8e0ab9849a618565fbe0764301f80495a8e0fe1d81be292200807b50af9db2f70c3fe37430380054e0968c890900c12f00822d6112576690126a421d8116e542430e21d020344871fc3b21e42866cc89041eef8f62c4a50a07010068438780805906a884822cc580082024a8c14265e6331ca80003ede0203c085c632b102849fd56b802b6c11451fe0240100386e3018c28290c110805c04e715ba7248017e692088200340a04f06441bb8480d80a0016302f143aa20bd63a41ec92306010cb8e2018b000c301b060c1810399bb24013801d9df2010269d5184070612041fc2555c2d740d40c016107a40907285c1 else (if i < 74 then 0x6620859a0ea7c40690a0000620c5866440c80c624104247d40335b633018e33a281794400024f810a0401e49580e11c301c6c652cb500004801f80009831ec403104b3814e61ce00814e290ba6100686804808980c1806bc31dbd886189c464ea9975255173019445182b00113236804485dc000b1047a11fc34482d0640bdc8124401e0102470d0513800818455b12052d430ef3485968acd22802a1b6e4530045ba0f207680e2a540998fc12628dba68c078a5f03943a032b0bd49f0f534412fd9cc114217c304416d8f90c4baa6a0e09ce09a1ead71463c44cd000c10192628a387411c01e960bdc00006107bc23314e157013f88180039ac64de02614001f2084d7d830260391f0ef06301a30e080008a0d48c1bd0675090ac51002160901405c4c6aa1165a4c54196d8710ea85c8154124e3f1e40ff0ea992702c4d41a8030041430b44fa0380107e0485d5de04107c83647d0302a0261b10c000014720811800d088a5b9f380801a80a4063451420bff083c767943bbf00c6fc70a0142 else 0x69c098002baa2ea6835041400850c400f72e1eea59004c011087ebbb15dae12623543dd8821041b0d75f73ef800c8d822018cb6177612d05ec3cf01565006e54a7c008d0538033ee41fd616448f7b6f0eac7f3cda92086c4963104669e188e340d01900145400121015550087b5e04c408a09c6dc006fce60236a4c07118cb603460100bf2103b0186eb14000c61007b0850520b70630b8178e53b10b46608c1063242142bc008830c3585010341e20080822040400ad83c800001801cbc0cc62007204801501e01a4141140100132201e15000209158880d459c0b5094790342b391218d81014418628040d98163209406e91e7cdc030319d080c001c4b41005587b244c7928942801a046548c807684083f1b8e193707755a0a8008584bc1b40e9960c1ce35924420182998d2947c9d1c585050524775302a0211430387041801105620a35f8be55cd8808d81231c80044c401a010c93a1a434c4501c439cf8a060109479d55c80384454a00700100c307229b5ab0022c1a00478610a744d7)) else (if i < 76 then 0x6c96f0278c0316b1c01eb02de0321e8c3180241c2d3e1aea8c221b6450088c0003609c180202020c0f512c54b89c0e038131574260ac03a0820290c1d723a1e0001229483f169350a10610c8410519a1825820f0b1bc2545bff7c4d0025f0496108011e2d74806db90439f6b98208a29748816c0071104508406b90820b8844dcedc5446f0a02b05aa2a83081b3280104c170633f132e00163dd9e400156051512a80306684f8f9c9408740985284c168548e7c03a2e17e2e2453c8e138f1f400140a81871dee83b45a419c3640d803780c20c5aa0c30a00a0a81222c621ae2a971bc83219a6030829a4045868d5ee041d9800e90085036240b7302a4c3dffb000b21252705200c162b8434e0f53901635568708204e60408e42c1441f2c02260c0d3860e353c303c71a2000b60d662409f8c9660d4a88dd14b50f0a30431e812aac54068b9105c43bf8092780744ca02a2ac4f82742040b406f33bc11c0fb0780c8e01638196738e0440b1501b388177e2efc0d0c51511333406d3b80a20097 else (if i < 77 then 0x7806202800f815ae5bba739e24d44d8e92f9010bc3a76cc00f907ad570b0b70a2af0073643a40840763602803d65d1e1825831a9138034112c1410c16245fe01f090dc0713cade662691411bb1120ff80260db2282ae06e8314d3cc0b8191202147182200413566092048802af8025cc08240349400065183080c061c701080e821f1529646168200007c008c00c3243f90435801c2c5462814c0c9109818480b6008d003001a828c3c083a9140302e74d8a14002ea6897408c00000d0c94a0001d1017a3c6160c022181b601094851a3910002b425c30c64396b8000c79e8d870666a03d0400205860feb57c6b8c6c0196031b1820c619ce7e41ef04c4f69b0401302a1401700050a8441a5b616163181b50209e20020887f55e0de7b0348a003f8038c8d1003876309388f2602c080329fa00790839e1f1f2f1e3e8401f45e383fee040800ed2b5400a8ac35525c41e0048880b0e9ffa13fc70b164121d012d6c0e46711ac052ab0551987a106a13c30e9a05eeb37d64b88b93db41b6d0c80 else 0xfec0b0a2a08928991be9e256c7bc584001405f142fd995162806200ec9ca006a32d1a04421a8d8a3e6c007a54615f0c519e05070db4209f4201302c1147a9837bcd0e034c570b9d2454447082190cd2cab5c0900d7105e203410a820b7ca2807282a554c604c0143700510f84c3d00eb8409f6bf9db7ef45143d54a79e81a8062a5400c7180c08a1c0077c702aef80b603b4330f852c4b52d73e8d9da12ce4c0441c2ec082b838b010fe02a3f14685cab9053004402ec001405460064024508334065be2de3da5b44c04308b028a9461f745002650035adc1c282853bf3087a62b068ce961b31837f496db8dd067f447c00bb3a846088048a09f8c0a241014182f6127822b2701a8a0503888ced90f4e77b80da25380f80df010fddcc2a1606561f0796832b2e78485c000390dc0025876f4b3a5129f9902c68ac262514344061a5c50489183480200dd1722022f8e2009879bcd8f93006a1d1f2ad022088828300218d002546420680770c374c84810286f02214185481470871c4c7036c800))) else (if i < 81 then (if i < 79 then 0x183c612d0d00f25fada0a0667b14767f0007800301c001f0041091e3e1ee560c062b18f0000125c05ea4ebfd79384140000030c41e8007d38029a3b3a0408741f88c01f0018d02d228f429c6562800079fc6f44021bfa2ad9d0058708c1d8a220581d66710a035a088de4c76a1d97401360e5a108f48d91003c0253d18a598cdc079cdb418174e08630b4654021d2831c26501a00b06d82c7c3b50707f1c2c0a916c035c534f670230081680c184359d185d1ec5b52062001e0502774e88d2168041d748003081e2711eb58bce0f01daac0b05601314101108c3700643917471e1c1b5c1cd665e8019e28714b3796153c223317d47308315330769ac852171f702b912482001d204a0d861c87c55c0a4101c268c71341740005041ec8a81171005190ac1c690cbd85c104131d14401feed29e8fc303cac80c4717192e2515f791ac36e419f18d3c21468c1333545bd1700605c1848604120fa0b0e6009512e2d15f4057dd8b80124000e10163081a21bb200d816a266a2472ba02b2f08b0310 else (if i < 80 then 0x802ffea66c6217e180089840038002000bf476ec528774316a6687a8029f8b0bd7cf88811d11c0820b118304000502060d1f5140000225c8473be401fa1ec2c003340d2380b8038ad5de617d5b6040d3ab71d0f408b1940240180002fb282100e5c0610d40703d03505c34837b52e07178259a98d017b45a022a8b907d61f79b8ab02103be8180181f110fb611a025264098b78870aed862f2037a005c008dc0e0e7984a0131007c6d01a1407472226131b82ba9c0bd0cf4a02008e43102434628590d704800ba2c01951f8c5802abd80080102501bf6c4e00b808c89300bd418308400cd0405a3806000763a85d1c45334561f82bd228cc0408400e27807b86118c30080110410cefbc4400987e5209e0231b65a5b91237086c390f607a17978877022e14b052407591f19f900e49802000070c71782e890803001b23800209ce2863fbd0e00ab26e0884178b0cb3f990c83010b8040365328708300169c0a8a5e6261800091d038e30ca0a117085c3ea50005f17a701173556476cc000138 else 0x5954c03878004000102f8b80b2382e02e8c9fd0233a8860ce19413b8c7b8480ec1147002f4628001014d0c7dfb340d5ce062c58410562820f2f01e37b50a800988a06f8e5f8230c6741a686426cac20160004e00009df04b8fc0f73886616158728e985441005ca082c4f0408152bd01b9e0140a3860b08708f03b6b800202e4a86370307c14013db0199b04fd150c98aee6068a040001124640d081067152056b0a40070066604e2c44031c68990cc7c1b4b090a4394819b60790045259062ce40f5e0818f66108262396d8e125c178c29800f2c35983d36f3140010830b2e0b2e9d21d468e1214a833010606980023214e88341f014c022fc38639202207236e10906281602612d64098c00207038417001bb7004a40df40070001c001808240c4b5040015028c7d29e00001e5e44820c3390ef60472a00038071c00009cf5105d8c016eda8403e085718c44004820ba3b820c0858cde05694d0284e10018176c00100901c001ef0503b3c63f91c5bf82a77610da58c0b78c67c81822bec00)) else (if i < 82 then 0x9003011edccc8ad08101501506e002b9050006168a8078ec8039191e38f43e36de1c07c807c0be025d3990353011c9402e80b7f07b6283e0d47a80e370122b62f00c8e06ec417bc5a306200cd749108e4080235b84bdd0e68201d3a10800a81d620680563956053300aa48d67cc8a0ae0e02bd608188208c40830000030d50130a12c2184084020c48a1c742660bf814328501c41a002a835e29f97c0a1943207243a4104080d5003fdb020108018140568ee85c27c67480238360ef0000a00254a1400cf67390e8c804e3884022594a7f1780684f88f0b60840a0094a00311014308418c100e820385808efc8f0a3625fcb07c0b428ca4f89c748dfece51566687aca82dfb0190c1f1624c52b781c380d5056dfbc9ca03ac0c31111e68968340a86178c39d357c41e01c11a00d03bae40692610e01540dd8bb4e1a2104eb5ee20608401b239ed4741951710a280621320c221522ff659800280741c0e2a088032b40a50b80c0039a9c6a09dbaac3e40a008c5c047c5e170c9408669119965 else (if i < 83 then 0x1bbbb13c4440f8f99a2e3e5a030404b51d90420061cb6762353a0ac17400abe9bc39695b80c02130208443440f47400ed8a75418022c20f9381262276219f0400c760082054015be39740c04a0f8400f2604cd42f218ee36f98ee008018000620a40368edc4e090852c3040f0600a6231c117ae1002dec60c28804afca3a3803835db490024118963d0fd76190bf98361e408c1e814f480ab0085d2fc060200057902911549c206e4616c28b38b7c03810c5437087023d80c03cfa1d094122ae1c410548f90fc7c278b074b24021f8042f43e80daa000814db8101400003b80e30c6608fdeac00981ca4c4c1e3f14f806503899908079b83c610106c200100f4dbb2c8202fd00008c4407983360ec0620849a5dfc13311c4404afcba5280c17640c26c920c1122410588dc8132b0048440bdb13c000840f620602e08a27c30656c27dda4004186aecd0c46a73e9c0cd690dc9438073013e3e6004346024281101859208d5ff105b1d8030a41ae9603f3840583a40368691f00f0c7d46601c20 else 0x1704d0845de100900037b3dced0010e6ccd03e5040ae80e70001bf05b2184b884717134045005b6dbe071caa13d080048061875fd34082da17600c0d0061420402c22791a1cf00400384c01d34605288237d56ad0e0624698fe83a80e2130121010f4b1acbfaa42016814e22001088e02dcb46a00200b16c842002b2f98a183c02cb8617200002e34cc1ac060078476b19868e02b642f00b54b327b21e48cee2a00ec2c035808002106c40c406e21e03039e1e77a02f8083302018317139003b0c70027801c241b000fc3daea08628f0d6a3a84b61c3062bc1908301101d84f4002d0b54e82073e861381be20b02a048b4e638a63a9c6300f8a02c3b6a081982e2382743334294210206c74c0b5a1132981540c5001385ed060018c0eb154410c870cd54c0c5a2b091138006201026015fc8078400538841ff390480083e57300330100008064500360a212612f45528018a100b8f108d8dd814b29e9713040010933006c813a89423f4010440103b8298a4b832298052810f6810fc40aa9a17))))
def routingWords7 (i : Nat) : Nat := (if i < 90 then (if i < 87 then (if i < 85 then 0x810a1b223c99875f024121514304c0008778085380025e055e95c1273634462010000e734d2028027e01e3342c0d0c0244f380f71c10606240c00c080396014372ab0ea080d40599a1eac548816bb0821d8082be65f087a35360f0c760eacf003c68a7066308468527e860b79461b86f60f5068d845c0018d0063dfcb900c06b00447c9002204689e001a817dc8192387fe74666809141b5d169c0824048c79c72fa6191b8ad809f0f6c44c0ac4442fb84031c2e80018742a0e542c41e61b80e884c000290b4916f48f81f18df0099282031a1fd3f1ec7c34340951686a70ca80023a55004955857313b2502a3ff028803b2294b048260110101e054538f006eb5c0e1000023f5f1468eb12071c11b748349a0d064b6f7a038a5228a2aa2060002ca05307040bd00db7808c815913d45985a898388bc7f10efdf240876070525300112aa5691c5008108632e106c34c0e01ca3148105591b1a03f40980088f04c26043b054cb27d0c00103f009fe4d3609c061c93338034c40ceee8602980 else (if i < 86 then 0x1f8a4307a40106311d64001d1783ab622c0d3bd0ec04063b190042e00e50ce0c18d008048a30c8b2608886001b4cca446ca8aa4fd010bc02f011a1826073d80825400a941042260a04e0161080854a86f5c454101c8f59b16c2af02722bc5ad09d7e021c3a5b144e21204008f38183958050714833518f604f01840a999c10cf38abc500782ec3820185103fc25e00cb03b528ac016840fc28b93e40193000c2500361d11c23db8608424823801c8c4127642548684180833614a55ae0d5ab98740cd7e08c71000039628c3918bab9a47d790e56005e1027f37224ed808b207e111411c7000e5a100207c97210ea408540033800515e9950073189147b3a846de1d53b800794a32802bd4015369028bfab10213660a41a2bd0455c5044180e651400400d15c01001a816d23800a0034b000401151a32441881c9220021b99c29f614a69e25f01699d60d17f63358421b400aa021ea181040a024f03380f1806841c034319d19dd80680035491e82942340538083c28e0021fca40901f815eda4 else 0x3d99a4d44a6840a00f02f06eba068eac002363b06a48064014782da08600aa0302ae31380444c00806107000281e50a6d70080b48f5804eb871a0b4f2d8dc442583083f4c112b1d8084134255648cd871c000e10836504000c1014b77c6faec11fd19ea6701fec4ae208f2421769c4fc528b03edadcfffb41882070c525000882b0f44bcc218040d85d6240b5a4428013b06002c74400000058a7a8259505260ee8ae1209e8f88f082c020207a70c9b3c80001b0031a25ac12046c8af0a20440de8898800d1e83a18a600d1762811711a6cba118107b051d78c850047610028717335219f030024c6198078a183907b40862ad2c83b81fb0f69c0e1df937c0e4270582540020630d9190018945caf88002705108a160110b635e50117a2f8621d424f0680d04429f8083f0046800076c40c24320a304062143e1883e81a4005a180c400a631400c1503d3c70026169811c000842028c578ed800049ddb063f8673a45f5500e080901d11a31c793ab18050186104d00a20c3c23348003c50248b)) else (if i < 88 then 0x40298315301015a604cf8c050259482246103811e020509cb489c33101e560741825006808201600020c0d7e1d3000ec200bad7863d80332cf9ff4aaa18cd417e0382fe4454902cbe047001825a1c94a81c33d4283008b23f0585e86dfcc5c87520a724e9c1a824608fc60800a80c188223123a1861982800b5e192ca28a018009144501ec20100e8639900541a043e319a94850f7e30b2ad6810a9486aeb10080f81e019e0000651c0211ed4342c7674f616025018a20782c08601aa0cd07e184289003154bf550077c05e7bb8230ac20a0769e806f8e8916d8031000ba6d4c5481220741e152f83230423500bc103c98529808d21d17e6001e98385802284c0bbacb29ec5080302a99f080c20800902c07728818481a01c83404796a4c73b86036071c49f100a6ddb9413ebf34a80b66c0ab3018fb0026c66539969c83058a98040bcd0400c409332b613c90a021c0385e1117f0006f11a002deff02820201d2a089005729b2d85d00005c40f30c1cd06e48d08f80424fe0c003d034213078 else (if i < 89 then 0x30980c012c6b558490331c7d851210bb278040a010c0824431b9c76344d428840dfe0e75003c0ead4384960010090351ce44924b480140200a05432f40f816270b800408041e4970f84a0e40988850ce00302d791da229d620303c808bf800220c1100521405e001408223790622b8005002170101df1bf0a81a28681c6ec702000012a0b5366e09ac1d52f08607430f688f12943b00872c7204347d4710303a4071949d4f820d20b37261bd59a588c1f00805bde202369aeaa0110909eb10ea3314a2442c3188842003e8960dc0683cc7b0470c800f187c301833807249c5158000002203544100a91186280918450cd800583000c7846c341a367768f3a1f812041217541d07800815513416cb810590b411822001ac833dd0d1d074eedf0c306026e023b4004d7189280a091d28180b00811e003799afe1c0a034486ac039711c631d5213a0bd0cac0ff00258f4087dd06e409a20903c2a382322c80844deaf7e35cb5457400d72c0714fad50080154015e3e1d100190059021e009f8e11 else 0xb3b1a5705b451db5d10c0628c004009ae210c04c1ab69058082a34bb8f86a04d85f00c8202284302033d81aca50985584820ad03a047cf40da8093ceb3d0cd6400422cb6152040184e040c421e7b798ad26109c041a1c9b490024c80872345c65009401e13a88ad2985c0b046c0e252cd600d0544f050032ebe21102e2009a0d82005428010dec12009b480fb95260021377e8a080854405120517e0300006c0068040241b1ed113b840f9024acc4e518b1a8bd34ee932830040bf918500440081618a4ca9900075d3427c526760046077f5011773c00c28adf560406990050092a96a9e108aa519a0104404c408a2ba1816060e8dc8040658582b00a0427b400780189643481c403c23b1c171c4a83183223190407617c85d0089b08243f0a279b1076001aef950000855a9e0cfb1339248c1002d205407a8c8002040f81a49c164e42d22086813c74155014b197000813746198e8300900382448a1502005fe400073e43d1c4be1a6a570b530a14049ab1203a623b52802303d630fc3c3fc0))) else (if i < 93 then (if i < 91 then 0x10a54612701bc2142c786001f318741aad26f8600c2078521882f0fd5ba0044ac1e01465406143fc41a30100658008008f60682e48868711dc05142e9f17560600f401be80154e96d4db81f0068ca10c02003c21230a4fd960062014600816703cde60fa04547d012e38bc01d84c8182ab0e5acb5cdafc0c006f50064f50289370075c0c05e2d163485a06e7c518c29e2fc3cd2e23fd78fc8c98cc93c640201a408562098ef86c39c0005d6323a6e8a602a7810f9dba221a0e35c08f3f0d1820b602dd00a38600f8400002eb481274644c0e40fc2e29ec2305e5d37061d2324c00b2085c681915011806182c000144cedbc2e9669388c168310613f482167005280e000b8a027012683a0c003c7b9c643108084222c6209b58a89ee1563500041ea0211b602a03f390a62d8018195a41039e280b506d60f0f490065b8f52270882623c299689003e8f34accc1b72604980210c58a830c0132b98004c070027069d0a000e0099c00f83b09356b587a2ec409f38a5f802c010040a87895401140 else (if i < 92 then 0xee4301914140839512843dc322a39110a7857f80b23e05932090663c910051904ba60d8a8c901a60870dbc5c00169bb0318061d200798388e8d402630020ea80a8ec701a3da247c02b614d209a14f1c40274281de02376a268018e0b8350301d0cb310c14a04068990090804f2ee1302501c18452004c32427e72cc08077f0c5a06e09148e86ae2ec9629306b4d2cdc1f62f2ec83b1d609aaf5aab02061a2154290236c0dcbd52a9900fe201a7ac23ffdc683ce00318a406196072450090360e81c28c8092ddb4b31a72992a71c6e5810e15333160e83b680300107442d7015081b6a9a089757a81c0a0605661102861f70523763713801f02a032946004a521db90644040a03b04a0379a8982e1569800f16fd07698e18b58f2f55500402e20192845759a55b68c131a4003825600301108215a2d54876d00bdd1888abbf012e03410801e402aa8b14110b0008a00608605481b031436064a507609a00701d3c280c233e2ec80e07d48c38c0403805800ac068886067c677528062d7c219e else 0x63a38018843012ca1943900a01881a01400872105f7660724850e0001a885de3d02052d0e01001ea8b8288e68601f740615a20da61068d0187dc6e81addc6be296d5be79205c6ff6051038098fa90a400f20403f1aba62620348817128013017c807427c71e0ac7a13d8c24d1f6a310477865f8819151f4418c4180c03c26731001debc0e364145c24370581b65a96439b500d08510151a3a14191f81a0fff7eaa388103e7a301b823f304a2adc8a412822082050440b8019be4102039b401c114c1859c5fc0ad78001a12004b5431104000c0343f25d518ca901f1bc3c80015bf1c65c6520070a221406cd1a8091655e12a804db86a1c0482bb75501a8c022b8cdd83c2322136001b121ca0ceaa7e121002841e7880e010064201a028966e12b011c76ba40300f7e1384dca2001803c0e13e26ec24fd6681e545049fa30edb040468ca91c002014809e7f00a00cc1c01b161321700b180085e450021b071703a090f3e03d607ab6be3681c2aa58a2640641757a2b103555801e5b867840161c)) else (if i < 94 then 0xa050e260141b0481461fa3460000165881345304c385da000284a6974a2f59accd045a6863bf990079d8585e298c81d06800a55580e1a160be0112cb108a46e38c24d6064104c826c09006d057466a964c0061e3e0667020800494613fe40698a82cdb56028ee2c1271156d1002f8b54118c042e4039722a788083618c145280c3de813c1088211a80a807e6a4092140a2000c6700f8e8311800042002c5040cd72804069b6388850a00f471510720301c0200005543101861f2483008e1fa33910c30606223a03cda6430d06901054e933a6e00c24066e22197f10c0e216104b2916d94240e02003e7e130c7fdc0a1b0076b6030f400c0a20a8044f4bc468e380360f389ee4fe1ae0a09178004180c1279d223000e1a450a8e661b407e050322a68021f35840ca20e4c7fc4a09be066882f084a9b18ffc22c4b08800094020c7ef13afa67a8005600dc5403817b30031c25018c0d9136c0c0601529a3001e0860c9ec0177610ec0cc2503a3489d0010100312c3e08a77e47fdd800be540857b else (if i < 95 then 0xed5353003b38e1abfe3a744efbd6964e188527b8389783049240b027f400386f6056e00a0602ccab0d04c2dfa828c0002c0934451823a50c0608f005febb0d8100304017bdcbb630c88e019ad900440788020010806101d60b30d82284ab5a0028806b886000c6a7212a000c6c010042eec970f08a0d3c00206ae839b4b2080182c0e900216004f708064503f77b1cf28a0200e503813fb0060063f19ce40220076605b109bfe000024599868da820a4071042035ba291ca0060324221e9c096340ab025739ba50c704903e082000404c2b410488564aa84f7e008006d18c06960ee182338e311c3647ad4d0104602fc2af032400008b241f2c4196ca7efa39279e1d2403038c0011083b83740242ae1c1c90076d55210c64020390d03021b916800072508142aa305085404fb1c2006f10cf6acb05c7381963ecbc0d047090215de1450c51096010050380d6ff30909f14c83f720aa690100100226470406009c875017ac7a000a054323aa7d14da18862b210700034c7d023030221c037d8 else 0x4005c7f480220506b860d33fef582341542679080b4e4e53a1f8c36d10587c3038d02c00b18400401d410087e9513485469ac1a305c32191300384080b0b80057709c92418e78603e2a6d0d99a1f1e1f50a06214e30e16e4916a00726840a818c0240d77a0b0f30e0714b0e7207b4848f632d7903e28a945153501c2c138db1518ab000c2307172c36ba405430fd07d2a2716fb62e07aa86051c329ec4ab601000fa008b4804c081025060985796508137a30286a7d1cd4f0825a18ffa170a8679e0409fc95577c786c16303f22a2158d330e800ddc0ac5074608622003cc2b0505a26d8d301e89aed004d201020060040aeb1a2500016b802e08408598022048a112290cd803aa140800800a4457796eeceb13e0636ed0dfe08b089786e0475c256733425c02003300d47c407c0380288c21161ef081000f4fc80b31042ef90c451515e0848dc0b04303189cd0601005075c87f4e870f0ce80021021c515e7911a104017803be80b6805ee1ca115286a104002818a028e01e5d0730060362f6))))
def routingWords8 (i : Nat) : Nat := (if i < 102 then (if i < 99 then (if i < 97 then 0xc8f003001477f4e281c000b74000c680ac8d84006f04440d191c91302d04c04172378968c1b276fcdb2b55e99343141c443980007400280c8580a30e0a5c6020728a500b88d9a20161080a50c9fa30010d72810040e08ad759af271831807330480817823419460471eb4d88a0340009d0249d00a0286064834504101c20340000851c10c2e3ba0b52fc1b0010620874ec1ca03856d0c6e096050102c04401006c79a55930e00b819bc15111102170edbe47fc8f62f0000200896f003e826c0918a4d5006e88c275819082005b0380ce086c863380e062b1436062e0200d850821a7710c5da4002e8774ca1ecad7e9e04141a8c0440180135000a82c3fe20fe8e0004000017a828148e100c8ae89801a5a682e801b1303e8c1643049cefc66642b21e62820024151070506d6810143dc039081000222cd100718a0180020b82c6bc8410805421f96488616a9ee21643f87ef32d586a11dc0340c1ad0e8020b4be2202c4106c72b11ab4081083bbc2019f581ee35e010e0207334208a00d0047 else (if i < 98 then 0xc70783b4027e30183dbf07341741a7c553a0066246807c3a038021f203edb09c1300c44b4a164004181fe03815703c8ad882d9c400331b046a28e097a8f40e8065a18100443eb305000ea5c6940eb1633dd3dd19c10900037b3b02cc3e8dc0b5a0b10098307013740001875c846581ef6492122001f0ad0eac4530c089914d02848af9b1d148023b4011037ad025144f9b1411300400061679bca308e8404a86c00159cbcc41b9648aa22496d65630ac80ce5336eaf4de4a438a3cb821514313c5bd19de190aa204884e29102a905706411126108e220b60c888080f008c09647208704005600d4a2f2145643c4ce32c41c680ff6026c06831ef809e00b66dc38040c737c507546b42c28f68a423a8c05948402a01e0762304027102bbdf6431c3e8003c1308805466211069478e042e086b0d2a440205a00303d40f1c414474a9fcedf033f185b94aae603dc0b60a3bd8b0012074de02655a395b2cc24fce0094703c88295b24c0503521e0d780e6bcaa1ad806d3e50290167c98010f5800d else 0x538400004195003706307ca95262b60a96e1ecce201165d1c6721115aa1838769001c466173205b82a002000205ce7571d034019c44340483204112f7cb00e0080609c941022fc6b235bd027600054c80000401c0c1073a008009600824082e8880d9ba29807d45ceaa2ba280ad47c0784c19b0d8143823d4a12a805f98e4f867a005a2076021222486341038661501810187e4c6ed801301e478620080628180c3c64307d8a0a402f8a02219524409590c2b240c200d7638c0220471b545e23230a867c38b2040a5d5dc2105dea001c200340bb80dc501301162b0b551d7d602a8615c7001083c0d541e27003780028c1208340661103220372810c98116d80b6002c6cb16b1493e8088321c0a63c48117e84078470000284120280008409c4682b4404202826b1430b0010b208312d4b2140083003a8e89001387573ae0840b412df7f089e9800223f1000fe018f9a980ff74c1a050200300e8073b8008b0900f401680403dc08cc015620d605030b391a9d76623f061801cb5820ae7c9841)) else (if i < 100 then 0x80508b15e5a0e00290e3c404e988b5c0744c1040000fa58d31fee64db1639e07420b82230e519921deb05dad470c81840007418683567ca0044f2811102c009ae02586243be700688c98d6f444341780d6d8a17aa7e1c1190188c405d948a1876e414aa0bc44d05a3008238b0c1915cea76ee886844f0280cc621531ab8d8403e18010209451306c34a861472305082e6881014057a091e1d8609035a465c36de6c17c2d9ac50600f42787b182074c596bf63a020467a800458ce2f42882b745eae1504440ec37fec22d0ac700770e1588aad9ea505036c3144890b418185841420030838200d2eb80d09680000008d0fe07bdac07804c074720824cc0170003b6c30c0181079e05c0b4e84e871071109a703f590217bd02014234190033146d0520669c1049080010af8098ff8c78c01016875a0204408a8d41e3d0062d605815008a80e8ab1e1c4171be5701b81c40348b78013302e47e3935002014050750228084012810f0043bae209937c34e963f01c0c5020111e680411ef004a97819 else (if i < 101 then 0xce175ca3099c141238225885a008a8c8b6e854207101023b23035c419a14e36ee8a02630ff06c67f10a6f4a880aa80fee410456021e82e3780a801004b25060040554dd3514020211809e9211900f460220830014287f8c3100028a047e1707b87d000238dd899ecd8b7c638603d84a289843820aa9e0002e3b107f36e4b05ecb7031e0300fc00358a029400bf42e8c10bc2153c67b2e01a72c0ced0a206181f600c890b521c210f6c6905a870f31a1008c44e350425c05830325800170c69a8b0518258328ed80a5faec1c247f73ee484200ee4189c902dc8235805202800079b8289054784006008053194bb1000013001c81c2ac8f55f881902e28d7029ac8928b81a800284896102a3f9403401962b1240e280c49a406ef802938e606870a820876c2011bf5ed0003aa2c4a97bd886c6c1c6a6c0e2d612816d6c6473ecd0700100eae00118127a30d7df2f1427d14007c6f15d881f34631550583a08385902299810162dd18c0020875b8834388c67b1983ec10283c8601804516df88001 else 0x2b83a80d08c3e002db55a4880cb61521b31fe1800820000d960f3aefaa2888ac18fc103f1a416034060409952904383a1302ab880b402986d901780b1c56331a960220f01002114cfa041f0026c202a018adc000944002521024a06431411a940e60c24971b9e08a0a6286b004025c3c450843ef1d113e300c5027e183dcea9dc48000e4d2d02e0e08266c6c004008c0a1a139c88138644886a1ca1ae3e4578f20324971035c4d482549ff006a2b200983e670573587c30870444cb50100424324200a40d4001090926471408900054d7e9b1f0a50527598000c864af29e60a060959868001c2b55fa0af89001640a29928a00bd5e2282f18a05781901f003eb9c9fb8c5655184381dd7bd33003900be820ed503082080483b088e6a00bd7b844cd002e872280536370a01d05d1a3073a1b1028620e07200242611082001016002f217cc7eba0543901661188a482006412671304005250933053c1514600808726a85e600fc0cd5178b3b2886187fa0a0102a461ea43cc21fe8103024f58e85))) else (if i < 105 then (if i < 103 then 0x43f4c4e2de48bc41d81880c8df18c0245147238bd640792ea834ab000fc0defa24158c2e1400040830460622003692216039840274db822897f8109244703e5c600b0f8e1d7e001c5434249f801c075c202c5170942558c0ea470d01e32a04088978c2cf3047200c4088105ae4048a36d3640cde0bc05b5200282801ff4618ae000388ca3c0089020a13390a80a563690320e71bfad528e14574069a0f0865b828a12363d9d600c628c1d70260967c4541d8001d7b092b1c40038eaad51031b8e03844b05107c0255a43d2b06051c0205138af01876ad1b5143082203968cd4019ae911a809761d73bfd607a0843e2f41c716a7c7acf03d4d5022a386de470400541603e000f314528000010b1e0038dea7410b81406fe1452f6056c00026b3c49d18c75b806a2225b3d1840afa0b8e1ae01a202001f8348a028860026f2b8002ad32caea281c107af558e1ab83401e2f58d2a0df40460854087909003320054ad7242bc2370681040514840300e06719b3a8c3a0ca905108001ea8803490c62 else (if i < 104 then 0x42846a06117c57ebb4043624006018620102c3a9b6029933dd3227030e03210407717a32cd069d12af48f6fc230208321ca66004700b1100204c82314b29264051e03a17150908c2dc69843b84fa1a1060a0801e2de037ec040808ff1800269ae82168090e450b05e50045a1fdb406541405d40c04442ec50c50dc434042418600078d620040dd002002f40034037012090c3a03b00121962a8a8471c068bd18204aebc259086a40938a077644101cce38bf0637a01e74e12e0075300bed8ef71fa1becc473f95c67082ac00b5c0800683700043b593f8c641b036dc04af1850008a0c005e71c014faad142a90ef91c77d8a8478000626502805e4000133d6d608046e81808db42fda7170e077c00c7f901409401b8c2e1ad2094040085130c21b114a45174ad40c0c0ce0090c20c72c3810b9f30bf789c203ec20404ee3d8526077a300043142a436dd77d007302094f7bdcd00918441fec005354a8975c88405400722061100282f904b3850c30020df896c820201401d3a4d9840eeea0010 else 0x886bf8602048b2529851ff48c397f0c103b3780078f6c04406c79817ac90c1d4c3a486c01a76d24d008142b0ab08d08609a4ce2c016869d642c3c00f03108419144004aa06494800115001620c84003a0070b09b7e81301e06f9a5d0e9138e006301b5dd05d9e187006790637a10009578001c70303c106a800fa22ea0e3c5994c1c0d8000e05a20004002220c01526b0304065b0e0250a1b500605fc78aa7e848020305e2d310a2a116e19540c0b581090d800d1fda88e500b5ae99c014103d648c807c79c08058430129cf8d03c06304ee067350cde19072863003fa7002843b18be051f20622080c5073c18c822f0082dce0bcedf8e7b431f4b071300c73c46452028804f1a185f8246260c3cf40008eca0186f10364f41563bd0681b98ed01b5081d86c04d4e0cb82a19dc08ea3c8d78033119680e8c3250a5e0080f0484abe00606e753c60410e0065003017018fc0f00e918011e6d0572b00b14b0168120100052d8fb8180c2c120d90627063000520ba800003b5a01e0c07d1597e94e)) else (if i < 106 then 0x43d0b804015d1855b30022d3f707a64250840295d702fe01fbd73e03a0151c0cdf13e030380448000182c0b0f207baa11260181dd04545b40f91f02b013006198057c002409d4037a781c214b0d039c1075de554c409b5c036621c5096a6ee6fa08008fc2045c84188433a5523002861479830324a1200b0e85600c40a7bf420c2bd828caa02364a940f3c00ec4180f8414f41a88b85a35fee637173e88807bc478694ee194c9542e080bb5ef5c16161882206ec012e0f4343bb196e38441400800168b9a038c400020020abc0462f607205c1bde81f9288202011081189838c4014735f070681db22000040eba00281e30aa3b40fa68c88c086603bdbee01d43a000302e8450e6f01062661d40008c1e80d00c20e9e8105e21809bb0362d00065c99f436a18080411d8b0001e36c8e36bd5e157c8301363a34a025b9673035020dc010a397e8001614062719bfec0706c60c7c607bdcda4007030f6eb083c8b14c80c00080216b8a052432f54701fd9010e81801b7000983a1ced889abc11f2 else (if i < 107 then 0x351c0e036f3bc04e847462b0c7986150154e18a7c0c0000970d40400a801280801edb0051263092106e0be1ae0039781809ca168239488d42603892f5d7c01c000b4c7bda20fc0005ec1b0200d8788cdea27aaa8b4340008020c2d67801603008695814ad100410016144302b08dfb8c0cc1842a0080381483b38aea7f71a8a945ee12d2001808af00a02b1b2404484146200a8541763c7c3018000807b78021a7a1000c06501000188ff363002f43c008102ab1ed0c2cb802d000169dc02451c4884bbe447b4174b1f8a710030106185384305303790d82856c77870174041d0290e4a059f076cce85e1400abfa4822114057051c51baa25c0c5c51ef05c1ed1844280264b5a837e0cc800ecbe1d88001731c30c020c8514c1eed0bb4400da128200dba00fa1f008e118000073920a0401291204105d02283d8300035a39102b0ad4fabbf0230010318c07c31421988241501c082302ab927067c30280ee14c10192b434234e2d7c06951c45863840003071090a2827c180970402b812cf36 else 0x250f02125145a281974efe0a341182410014810180d24802021acc0f9e79701003d8b2583b108065f1509d40099001ec8b51003061c86060dc3c7b8283a8483805437d87d54a82320200e10133067f09d857408343ef91eb0d2016f60a1d228b0fd254e5bbd8de70ab969e8c8108dc118e28a09ae101602ba00610c01000a9c111a524252086003f01d9e392c01390054420843500015940448c530394da0501d02002b00015d5d6f50d0aa1b1f719e44a1184436a0ee1040f789b4fa9b94228010b12f850e5060f820560867cbe04510014c02e34ca91ecb54b776d060701abc7002c08e1020010707e0d1230037d4da8002059e05041250aabdc006078da11902b6259482f81bc6354c8c108052fb0ed610d300c1228b165654010582950408b20862003f8680cf5daa20040574057224a5ac0e24d398cef0ac60040020183b044240fb407272f70010c18b818203e049dc0841586e21d40203200001c0a7695e8197086a30eb7880e82112145581031058000804c200c0c022eba80218273))))
def routingWords9 (i : Nat) : Nat := (if i < 113 then (if i < 110 then (if i < 109 then 0xe043e0e61bc10001275504bf962c20000a00818c3900653dfc5160ad05bd8c30200c6415ca8cc608601d502a28035d211c2c047c703723060146804700e3804402c60862021460b300001a106a5c0809a87c21f8a83b88c1c0e961ac6a8c22a81022f811000037945b285240180438b8748543b83e298a483401806175f21060b2c1812f854c05209c860d6c05427e03abe713818d8e0981c01c38ee098212a0062bc2f52b047786a0f029a13585007290568e45b7de960804004dd14583f546059033bb4a1a49f3ca080001b4948710155262d745eaa0c18b34bea3f180e03e86dc012e822df80a3348f165c589202ce301810de24791d7b1c4cac1efebd8a191181d41d01a16004438a74020940410407dd714f77804c3c30074ce58c1d2299e5084538000ee8e00f42602e55a27e627032041731c98057d99e7111ede138402368c300c0716368158820b88d0370acc3180a0253d01801014ab5f643c4dfae1ce776e1022e2071c0ad91c4340fd8b79c3e71ee1dc2e600b8009c42058002c else 0x764360031f2921b05c7d4801a8e8618e23618bd0357b982b80be09c0021d8860bdeb480c8c1b8911a06c3395201443d09833b3430104f200098a80a7fbbb115e0034702960d2866a0341c0470842303400863d9db195018bf7307ae0bb4d50972d4a1c13076e6c858ea8b6015603d28014fc0f8e6bf006558000ac7a3d83028331b23802916f0f819822711858243fe07600647e526fd8aa1037b97538c0ad13c4f12048542502b9461b1fa188a431c91e1c624201206afc3f00f56082b999228038814c16600b80031e1327b4e203a0802c11784a14e800c9bb2e83c6107c02a84b9461054d78237f1002d05b35e6c070f37e51abc994c48a99931335c0192bf815445414b6ba84823ff42c81232838e10b8420700d2089c00b3a1f880039021180a4364d149bf802c80000500aee6c88988625bc384f8352700a50187c8815e3a0061e00d4e52af84182a4482161629606640f5b8bd41840a4fbc70fff38399f11f37447dbdac00e7b405b2008ad10982308e1d8280800e8d520c500b012) else (if i < 111 then 0x6092031c80c003d17b88ee201e862021f7663a36780a14296c00a07e8bef5bd1832c1604203c1011893be02e248d2c910f0455a56383c38f9b8321c03776096286c3ae30616ce8c804f58014702726b0130c7d06fe03c43859020f942400228214502cc3886c10004045a040e06e4881622a5871c2fff0172881cb802fe055f4451b2c30080ffadd0701069c1180a0281080c91f81c18b141289a403f2a513635000026018f1e80108011a417d80810b511031fa344a87c106c0600e1db54756a61400395022382419ee5ee48e36c776951e087030a3ec0fe1b8c05d22e00b8443e832190191ce420a0d4e0401631603770f3987ce23206e30087a400334a8083477001018688103d83fdde402c064865a1d8d3d617e30e909f02004021c002de6e1799825ab0d00c02aa7e22ada0064dcb2f340aa001c72493ad82911abc220862520020df590603e041865f5844692daa597188ab6186033a15000f001002052a8546091820ec585280a1804107cc37f603e064285da004ac8433430e100f7 else (if i < 112 then 0x5f86b590410c9b0ec688947bb015c48781d000a957132561421ee6c0409e23a1524183760203700b0b91702c05ca3862a08073df17865be034a08922b8000008498e1ee8c393256218bcfc02ea00021032680347402ca0003fccd0a9e9010caad4a1c22644806d3a31f2b20603c20018c00403edaa02ff8eaaec64a8404748820015c8900461015a96dc52baa6d8e01029600417c469b0ef9dfc0403c6e80a04d020051809451c13aa1643734b8d836c6e7dd73c3800018056f1c00c20410d0b40418305d4ebcc3c44df3720c1027c35e44206244aa27f5c300078037c1258781cfbdd03c0604005288a82619a02d2f3357310830704612c0a50007e1a9190c35fa1a87404a0034c022b535d178208fc341069b1b8ad86200d200c5b489509512a17c500068f5900203faf2027e00d006c00c669401009211012018701858000c1a265084e3dd1062d6c8b024080786980634104bd762d0387abf8284083e5321861f76341801bf2bedc553217888000712b623c110462eec20020e00f6b5a2 else 0x7c2140b8200a183d06ea0032884400080582ac504a8020d3702983003014c38fc4203002b4147b140f486035b80045c0602131e0f051430ec0024565e0f01828202802086aa1ee3a12a0eee2b1e5838490004137e20b465c023317a1071b0aeb0021932007fdf822c0294504a8ba07684e000000d80c06062f81c02cf0db1f70794261c3602cb8400ec02c7440707d80204b853c1e30571d2a0975d7192ac4fb0d940038d3a48618c38205cc1b02ca3407038ac4804cf881a544089ef13007e10550a8e0ba04140f53c038dbd04080087638a088f51bf0701c816718062702a2306001d80064b250663be86107f89640a040c7e0f16e01009f55d80943403580e4fd0c0280158bd50060831cd4ab08cceae430222321cf275112680bd3ae083817015e5b38c3e14dc108e3558065057406005c40c06fce056038388000544036251ca1c2080f021001a061e400360cf3bd014550015303a3010c41c0239b7079d1140a0c3550724e05e0f30300085cdb322206b6c6f2380870990141a05f0847))) else (if i < 115 then (if i < 114 then 0x1a80021aaa6b42080c23e2d32950070c135067d8a01470000c85c0818439c4840740610581df89f0002e0fc1504201cf400244580cc1403dc50bea420412751c16008c60201aa651f9d8207034101a3958c00adec09317ee0180c068197d06bacc30600396b0217ac62c71e4028f09c06018515435c43e15096394d667530ca17a62017006418065e000e163c9d552050086ac844758485220820d333b031817a006dd8403546040010673ce8ac80a93c6000607c06107186e80206b0942c180c52e000b0140180c84173108541c27c80a5fdc0486820832d760b0c04a0334416b130a44c230906005482bbc2ae37180270a0581c076a322106210102d843961bc426685c91009672e1780574040347a07e69313a41a42133a4801303c0dc6d8016d32acf0937e50a2a03080095189ebe29e8000ca0434598000044c043300a44265819f02c39043b1414f8682e3ce00405e4a467528214030000004200438c024b4380758642d5e180f7d51a1004f8131f0844313102c47f040c545db768121 else 0x3805c0006d10e44086002477580af158418e25d1da0708049a22640000d1a42a7d1669b714a1e010026176996a110324972830df04183a68dd83003944849173a160280c09c3011a4080679282021d0800121406250c41a0c370089e103320a286447c9f8440c90407801c5007028a415d0b600071d060014266ae18e7800ad430c10ffa7808f20b3d1004af06e80334181a06057713d03fe0c1c0ef9202db005000c91d04d512a01d9587809c101f1c641ee884434204000a9a10180d4238b9e05df11e2df9421493941c2007205118b0458f54046c85b9860c4c101c0180ecb488bb0071441b2008f72103ae07030e083b8ae49811f200a11b56eb8760d145c147ba0c0342c3e802ae87701309e33db002ec8798198503020c220165f2d8400214a058068861cacc447b538800522ba10442429fd97440024e6c345cf01b0c087e8a0fc765ad024cea03bd4fc6ae64b8e7240dc0001c02f63f18dec26bd4e97bc0faa1334001288003b0d307a0e0c496386d102b1d0038100dd7c3702789e) else (if i < 116 then 0xa02001a8008685f4c95b2c2492e1651391280dc807c00c900e8a06615830a81a804c26e0e0010cd2e41b940000e00bde4781c1628e8fc700d40a06b0180a12050011636afc8260c90c0018c79140081fbaac5018028800406d0b67403b004031a0b09c61968c01da4120448077c1320f00340c0040bf881ab3d688bc300061fa40bb4c30c2ac1d1023c3c061409474026030de1801c0742c7969fe426e252c03023403bd983a616470006a00018000801a63a043431e3f443e01e0c9b3641a3a0271e81508385571460080260184369347b8009ab9187e0c10038159f9e5c18800e184205ec68b6018e2c489d1060850d073ccc9120d888c8a0cc833950012c1f506214c88c6ff9604298e0070328371c8caa108ef26c01ae0c096c188aa8c02f8b03850fa7610083b1c31900133a36685b6354110004781d7085c81b4014fdc8e007a2b2933886352ce65cac57f2447008a57c2900f093ecf13a3385505bdc801254ed1be65f01935dd4e104603b03ec5660b00e6d300e2a95ddc72e11a8208 else (if i < 117 then 0xb0e9c7f8b00d8b343c1460400e6600836e3d74506ed47a825cd403e202286f6d81043024829683dc24e7143a8e0fac2962c5041a7c05a63006203343e2d741427400685068a5f2d2c102c000a1d98c71411460c720164660018361871c617b90993183e25a040e04042017020031c6e0463ae29a004060110c41c60c218039f13264a0a517cc870f32076b00b60148551c26c4106b76031a41618184433a2800cdb3152272640fc0b86c10546f0ee044380e2950e986844a3e26840987020b3b80111e0f9401a2fecbf130182821080d41c7110e25ae10a88dd4c8038104710107bf74066be691c20aee6a087903a0006380c0101e064050c70c3834001892fc42076300a7080a17174f14d960308249800067e3095ec08867cab894464ac68f70840641a92fe2066c808a6b38a20b0054580f11ee07c12050e00109670c8a5ea43f765503a301560a100950c2401e0f140000ed2446e5007957401ead511201537f3eda8b68079075e06e24002f20264840061ebd5f23e380e0cbb0e6bdc90c else 0x14042ae1c0982c05704bd076ac0f5850eff5200a3060754deff32b484446c38005008e22b030581d40901807fbfe89309da0f917ebd868d2d001003aaef7860eb7e8e007859c7640913986b904c8181808100a580001c81380db006210015813000bdd4660005b3c00000620b9a0ec8250081d045405abc1049d17d5804d0ca188ec0205400055045ce4af00088391c896f4267c01380006788180d7aa81191e01201caac4e46800080b28611124038a35f60690f065dd9ad6c01c03ad0cfdc3000f580656001240472a001e81bc52b455f192b2062e83478600c083810003b6f800820a230292297e8260b1a58c44180c70a7042de05109df2c0000003c100040c7018dcb190086b02e06184808059097e388065d31003b80afed6018b4480c44b0c0003a1e0355f08c08dc202060d08304f414728064e1))))
def routingWord (i : Nat) : Nat := (if i < 60 then (if i < 24 then (if i < 12 then routingWords0 i else routingWords1 i) else (if i < 36 then routingWords2 i else (if i < 48 then routingWords3 i else routingWords4 i))) else (if i < 84 then (if i < 72 then routingWords5 i else routingWords6 i) else (if i < 96 then routingWords7 i else (if i < 108 then routingWords8 i else routingWords9 i))))
def routingEntry (i : Nat) := (routingWord (i / 1024) >>> (3*(i % 1024))) &&& 7
def route (node i j op : Nat) (ka kb : Bool) : Nat :=
  let key := node*4096+((((i*16+j)*3+op)*2+ka.toNat)*2+kb.toNat)
  let seed := key+1
  let a := ((seed ^^^ (seed >>> 30))*0xbf58476d1ce4e5b9) &&& 0xffffffffffffffff
  let b := ((a ^^^ (a >>> 27))*0x94d049bb133111eb) &&& 0xffffffffffffffff
  let h := b ^^^ (b >>> 31)
  routingEntry ((h &&& 0x1fffff)%40213) ^^^
    routingEntry (40213+((h >>> 21) &&& 0x1fffff)%40213) ^^^
    routingEntry (80426+((h >>> 42) &&& 0x1fffff)%40213)
def storedAt (c : NodeContext) (i j op : Nat) :=
  let z := (movedDecor op (contextWire c i) (contextWire c j)).1
  !properB z || c.2.2.1.any (fun v => v.1 == z)

theorem storedAt_good {c i j op ka kb} (h : storedAt c i j op = true) :
    checkAt c i j op ka kb = true := by
  unfold storedAt at h
  simp only [checkAt,evalMove,h,ite_true]
  repeat' split
  all_goals rfl

def summaryGroup (g : Nat) : Nat := (if g < 35799 then (if g < 6139 then (if g < 3063 then (if g < 1782 then (if g < 501 then 0 else (if g < 502 then 1 else 4)) else (if g < 3031 then (if g < 3030 then 5 else 6) else (if g < 3062 then 9 else 10))) else (if g < 3066 then (if g < 3064 then 11 else (if g < 3065 then 39 else 139)) else (if g < 6137 then (if g < 6136 then 151 else 152) else (if g < 6138 then 177 else 268)))) else (if g < 8189 then (if g < 8185 then (if g < 6140 then 309 else (if g < 8184 then 315 else 316)) else (if g < 8187 then (if g < 8186 then 318 else 343) else (if g < 8188 then 499 else 682))) else (if g < 33270 then (if g < 8190 then 714 else (if g < 33269 then 718 else 719)) else (if g < 35766 then (if g < 35765 then 723 else 724) else (if g < 35798 then 725 else 726))))) else (if g < 38392 then (if g < 37878 then (if g < 35833 then (if g < 35831 then 729 else (if g < 35832 then 731 else 791)) else (if g < 36662 then (if g < 35834 then 1073 else 1119) else (if g < 37877 then 730 else 1120))) else (if g < 37881 then (if g < 37879 then 1122 else (if g < 37880 then 1157 else 1385)) else (if g < 38390 then (if g < 37882 then 1755 else 1791) else (if g < 38391 then 1792 else 1793)))) else (if g < 38908 then (if g < 38904 then (if g < 38393 then 1810 else (if g < 38394 then 1893 else 1907)) else (if g < 38906 then (if g < 38905 then 1908 else 1979) else (if g < 38907 then 2450 else 2752))) else (if g < 40955 then (if g < 40953 then (if g < 40952 then 2780 else 2781) else (if g < 40954 then 2783 else 2824)) else (if g < 40957 then (if g < 40956 then 3070 else 3616) else (if g < 40958 then 3750 else 3764))))))
def summaryWord (j : Nat) : Nat := (if j < 11 then (if j < 5 then (if j < 2 then (if j < 1 then 0x20000000000000000000000000000036846d40dc5036ea0e38837120da4ad8eb0eb55c8da00368009b08368001400000000400000001c0000000030037000000000c00240009000000005400040006000020004800000001000000007000000000000030000000020006000180000c00180000c002b000ac0004000b0002b004a800050004c002b004a8069c00054002300014002b000a8000000000000000000000000000341b0005400000026c048000094000001bb400250001400000181400000000000020021400020000800020000000000000000020000000000000000000000800000000000000000000000000000000000000000000800000006c001b0000c00030000c00000000800010000000000000c00000000000000000400000000000000000000030002c00000000000000000000000000000000000000000000800000000000000000000006db6c00000000000020026c2492000000000000080000 else 0x124000080000000b00000000000024000000002000000000000000005000000000000000000000080002000000000000000000000000000012492492002b12492000b40095092492522152c851960de58362c02d580174012482552002d430e5018d8002d004b8009502d60061603594010502db544a25144828e34a45134d20049004a2082892492002b52492012b0009d0125400250125400e30009000240924904920055000020001000000000000180007004ad005540000001b80033000b0015500000000000474002d00574002d00214001d000ac04ad0924c04ad0000000240021400e50021400dd00294002b0021400a5000ac0024002940545003a0002800314002a00074001d000080004000080002000b4000000000002b0000800000000000000000000020000000000000800020000800000000800020000800000000000000000800000000800000000800000000000000000000004a28800230009000240009000240008c0014012480002000000023000000000000000) else (if j < 3 then 0x107924db0136d249b4936d249b4936c069b4936d24946d34d269a4db6c000000010000001090016d000080035000000006000b40000000000000000000000000000010002000000000000000000000000000000000000a000280000800000000000020000000000000800200000800200000000020008000020008000200925000340000c00860045804b40000c001e000180000000000000000d4003600000000300000000000008000000070009702094041600458003b000980003010d42493010b80000000580026001d4000300000000000000000000000000200008000000008000000008000200000000000008000000008000000000000200008000000008000200008000000008000200008000200008000000000000000000000200000000000000000200008000200008000000008000000000000000000000000008000000008000200000000000000000000008000000000000200000000200008000000000000000008000000001c494712500094002480092002480000000 else (if j < 4 then 0x4da000400aae01ab42000000b40000000b4015f006b454ad00018000600000008000014054500008056d005d400000001400020000804ed00018000600018049f81a5806d682afc269d4aa5400fe0027c003f0165c015701ef400df0137806dd8077904d7006f406de0067c2adb0139c06dd0037c0ede003bc06af0177c079d01e7405ee03ab4006ea105d009b1a8f406b35436c01d78937404db003d404de03cb426eb01a5820df0035c0adb0135a41de000d4302f0968c076c010d406dd4236c04bd6806c079502b4c0adb002ec04ed5536c04df000b4059b01bb42416082782a9e0907800020000c0012000a800000004800120000800020000c00040004000050000000020000c0002000080002000080012000000000000140000000140004b53ac24ad092b406dda927528dd0028ed4e309ab4329b49275249d4946d24db0ab6d24db49256355b4938c58db0125400ad4036c00db0827504950036c04db0026c209d0926c009b4936d04d30036d249b4936d04db0136c04db0026d24db else 0x8040b00000000000010002505a1400040059400050000c000000000000000008000000000000000040000000000011500000000000000000000000000000000000000000000000008000200274065d00054002d0000800950015400020001000000051400040000c00000000000000000800000000000000000001000000000000000000020000000120004800000000000000000000000000000000000000020000000000000000000000000230000000010000002830001000000002800120002c000000040000b00020000a0000000040000000000000000000000000000000000000000000020000c00000000000000000000000000000000000000000000000000000000000000000000000000040019000000001000000000c00020006c00120024800000000000000000924924924d24d34938d26924934d249dc93cf26eb4934f24d355bad34966935924e369b8d26e351b8d26a56d67924956936d24da49aad249b49bad26eb6abb9a69b49b69b6eb49c6924d34d38d24d2693493))) else (if j < 8 then (if j < 6 then 0x90012d01050011800010002000250012d000140002000800005000a0001d004ac0100000000002000940025000540005000b400050008c00030004c00030000c00120004c00040000c000000000002a003a8001000200002a0000c002b000a80005005b40013000ac00000001400250030008180008001000141000200000c00c00008800050009400220000000220000c00020008800c000080002000008002c000ac000200000002200000002b000a8002d00014000000094000500514002d0000800250000800000000000000000000000000c000300000000000000002d00000000000014002d002b40004000b400250001000030000000000000000020001400800020000150000c011c00080001c000b40000000b4000000000002500000016d000000004005b40004005b400950009400000000000030009400020000000030000000000000000020000000000000030ad00200001d00000000000000000000000000502db40004000b40000000000002002b40002000080015000 else (if j < 7 then 0x2300000001c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002300008000300000000300490000300070000c0001000030007000000000000000000c00000000c00030000c00030000000000000000000000000000000800000000000030000000020000000000000000000000000000000000000000000030000000000000000000000000000026c002e02274009d02278049e002d4555b0a86c209d023d9a1434a80c349e9286c5ac3002d4381311a0c00b616b4c54e88226c409b006790518000d80016003d806ed022ac009b01aac009b082ac04c30d574009b01276096b0126c0a9d42b5400da0006c2b5b0134c0000000880024000800024000b00805020140000000080022000000020000000020003a8002c0006000020040c00050000c002c0001000200001000000000000020008000200000c00000008c0028000000105000b000280000000000000000140004800020000800c20008c0001 else 0xc00000000000030000000000000000000000000000000000000000000000000000000000000000000000000000c00000000000000000c000400010000000000000000000000400010000300000000000000000000000001c0000800000000000000000000000000000040001000000000000040000000000000000040000000000000000030000000000000000000001000040000c00040000c00040000c00000000000030000c00030000c00040000000030000c00040001000040000c00000000000000000000040000000000006c00020000000040000000000000000000000000000000c00000008800000000000000000000000000000000000000000000000000001000000000000000000000000000000040001000030000c00000030c00030001000030001000000000000000000800000000000000000c0003000000000000000000000000000000000003000000002000000000000000023000000)) else (if j < 9 then 0x14000400000000200000000000010000000060000500008000000000016d000140005000140000000000000000000020005100000000000145000b40005000b4002d005b4000001b74000002390072400400000000000000000000002d0230000040db4c00050000c016d0000c001d0051400000001400030000c0000000000004000000005000000000005b400000001401450001001450000000000006c0002000b400050000800000000000040001401150000800030000000000000000030000000020001400000000000000000000000000000000000000000000000000000000000000000000000000000000046e401c9037240000031240231000000001000000000000000000000000000000050000c001b0000c00020d80046240208c00000000000000000000050000800000001000000000800000000000000000c000000000000200000502500008000391c9000000000000000000000000000c0000000000000000000000000000003000000000000000000000000000000 else (if j < 10 then 0x200000000180008001000001000030000000030006c00030000c002b0000000000000000000001000000000000180006c0003000ac00000000000000000c01030000000000000000020000000000000000000000000050000000000000c0002000080002000000024000000000000000000000800020000b0000000000000000000010000000014000200001a00008002500008002800008014200090000000080001a00080000200048001a000100002000080000000080028000b000000000000180008008d80040000030040000000006000000008800020000000050000000000006c00050000000240000000000000000050001400000001000040001000230008c00040001000040000c000000010000000000002b0000000000000000000000000000000000000001400000008c00040005000220001400000000000000000c002200010001d0000c00c00006c000300000001b0006000030000c00020000000020008c0024000000020000680004000080000000000004000080002 else 0x40240001001040000c00040001000040008000000030000200006000250000000200000000020000000040057000200000c00040007000030008c0003004940905000b40000000b4002c000000000000b4000000000012d0000000050009400040000c002c0001000040000000000000000000000000000000000000000000000001400030009400030000c00050000c01150007400030000000000000000000000000000000000000000c00000000c00000000c00030000c00040001000000006c001b01874001b1206c015b1046c40dd0046c511b0206c511b0006c411b1446c011b1056e596b0006c5b6b0046c001b1236c001b00360001b01db4001b0046c001b0046c011b0006c000300010001b0034c00000000000000000c00020000000000000000000001000030001000000001000040000000040001000000001000000000000000000c000000000000500000000000000000000000000300088000000000000000000001b00000002c000000000000800000000000000000000)))) else (if j < 17 then (if j < 14 then (if j < 12 then 0x4000000074001e0009800040001800050000000030009800030007400030001800000000c00000000000000001000000000000000000800000000000000000000000000000000000000000000000040000000020000000000000c000300008000000000000000008000000000000000000000000009276d4a2b4001c0007000240e3ac00240126c001c292b4000000000000000000000000000000000000000000000002b00000000000000000000000000000010000400010000400014000000010000400010000400010000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d00000000000000000000000000000000000500000002500000000000271809c0c070301c000100026002118026113ac001c1146c00140937400141146c0028000000025000a001030038000100000c0028000800025000000003000000000003 else (if j < 13 then 0x8000500000002e0000000b5000000000000000000000000000000180000000d4001e00074000101a6c00010009000050001400360001400050001400050001400000000000000000000000000000000001800000000000000000000000009826ad024b801ae0001401b600018000600000000000478002e000000016000000000000000000000b80006000100036000000000000d4002e000d400360000000e60000000040000800000000000050000800040000800000000000000000c00000000000000000000000000000000000800000000c0000000000000000080000000000000000080000000080000000000000000000000000000000000b8001e000000026005180000000000000000000002000000002000080001000080003000b40004000000003000380000002b80000002d4000000000000000000000000000000000008000000058000e00018000600018000100038000000000002600004000500008000e000000000000000000000d80000000000096000980026 else 0x940028000a8002a000000100000940028000140004000800020000100004000100004000000028000000000000a00028000a00020000b00028000100026002b40004000000005000100004000100003000100005000140023000140005000000000000d80003000980026000980003000d400040001400b5000000000000b4000500078001e00000000000000000200000000000008003600000002e00018002e00000001e00000002e000b40036000980036000d8001e000000026004d8002e000b8002e000b8002e000000005000d8002e000140000000b8000000000000300000000300000000000000000000000000000008000000000002e0007800000001800030009800000001000000000c0000002b80000005b800050001400050001400050001400060000c000000000001e000780000000780000000140005000980036000d80036000d80036000d80000000000000000b824ed003b80036000100036000180006000b8000600008002e00000002e000140006000d80136020d80)) else (if j < 15 then 0xa0fc00070b248013f0107c0007004bc042f020fc001400050003f0067c00a7000502027004dc202f0261c00140809c0007000506ae700050000700070000400010001c0000800030000800040007125b60d3d0551c0035420850025144b60e27000a50d3d0012402d900b6402c900b6402d9001240027404850920800a549248009d692d82092012480124000b40124000b525b601570075c0926c09240821024b60926a0aa44926804a4496d934b6ad3d03cf4b13d1d4f40009400950124800a549248049200295249201050069c493480484492d926920105124b6492d92692b52d004840125404840125400940025004950007000240065000b4000940004000800004000000000000900004000b00004000a0002c000100020000940000000940000000100000000b0002000094012a000000006004a8013200088000200080000400080002800010002e000c0001d000000000000000004000000003000000028000b00164004540000000000012000000006004b4016d000140028002 else (if j < 16 then 0x6085d4082e005540c86005b8000600518000500518002512d480140000c00018030800c2000094002500094042d000d0002c0109401ec01a1c0084006100184000b0016c002fc0ab6032fc0aaf015fc013f0000c00030009c0005000dc00b6004dc0837000180004004dd2c30000b80176004fc00950001c0000000d8012fb659007670000c00050000c0003000bc003f005bc0003000000000000dc00260029c0085000d800bf01258002f0307c0837000180004000180004000bc002d000fc01e7a8580002e090dc00af0105408070000c04b20049c00020001c0036004be895c005bc0a3f0000c00b70009c00071265c00271821400070b89c010709200002f0181c00c7002de8560000b804b7017bc04150a84ada92004bc00020000c01070ad480a1f000d8012f81570003f000fc0003033dc00030001400030000c00040000000030000c0167000bc002f0000c002f004bc00030000000030000c013f0005400c7000540a270029c1a270005400b70801c053f0009c002f0801c0407 else 0xc00240000000230065c00af000bc00000000000040000c00000001000000000000000000000030000c002e000180000000100003000000000000000000000000000000dc00940007c00070000000e70031c00370009c01c70d67000000235c0000000000000000dc00370000000170000000000000000000001000030000000000000000000000c000000000000000000000000000000000270009401270049c003b0049c000000000000000000000000000000000000000000005000000000000000000000000000000140000000000000000000000000140000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002495152d404a5152d52495036b684ad0969524951aa9524951aa9454ad5ea556a95c929400956925000a549455249400295269569250002d0929124a549250009500060002d00014002d000b0000500014002d000b80018000a0042e000540145002a00a86000a00004005000144005540))) else (if j < 20 then (if j < 18 then 0x49271269c0000000000000000000000000000000000000000000000000000240000000300000000000000000000000c00050000c0000000140007000ac0000000a000000001800000000c00050000000000000000000000c0004000000006000180000000180006000000000000000004000900000000000000000000028000000006000000000000a00006000000000000000000000140000000000002000540006000180006000d400000000000000001800000007c00060001c0000000000000000000002000180000000180000000bc000400000000000000000001810201c01010000000078011f00000002f004dc003f000dc00030000000000001c00ff0038c0000000000002000dc0027000fc00000007c009f0000000000000000001126c00000000000df000000000000000000000000000000000000000000000000000003000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000003000000000000000000000 else (if j < 19 then 0x20000000000001000040001000000000000000000c0000000080000000b000030000c000300000000300008000000008002c0000000040001000000000c0004000000003000080000000000000080e00000002000005004e00003087a0002b0049c002b0007404000000c00dd02b6c00030000004000001409d0003c001180000c2adb0037400dd020c004c00200005a80408001e8060000010eb36c00000100000004186c00d80000900db003602cdb0000c00ad0000800030000800036dbf736f54db7400dd01b1404dc00299201d0039804db003752ca4083775bed0837400a601a7404dd0039804dd0036c06dd00377356dcfbb4009501a76a89c01b5420dd01a7400e64036c26c5003d404dd0036c04ed4130c20db4831406c501b55201d01a7006c50137006dd0037500db0136c24dd0037500dd0137406c54036c04dc0836c04dc0036c04db01370009d0037406d30127400dd0d368089ca93f0009b0dbfd2cdcb9bf000db55b7ea6ff0027404dd01a6c06db0037400db01b7406db else 0xa005180037400040000000000000000030000000000000001900004000984336c000200260011800000000200200301b0000c00200037406dd00008301d0000c04dd0004c00131136c01400d874000301a740003000800000000e000380124000f00006040180001000000020000300064000000037400040030006dd0000c0028004e00020000100020a0080053802b4020dd00000000000040001801b6000020036006d8d5270002c0000000030001000000001000040000c00000000001900004000800187404d5000800ad002b400002004c046180008001e812a744a9d000000098003c0001f00360002f002c00024000000000003c000d80000c041f003c0002f010c050c30000000000036000000030120db003600003000c000070c06000040036006d8000bc06e80001c003019b0c36800020000d801b4000040000000030001000000000c00040000c00000000000100004004d00036000020034006980009000000000000240000000040000c0004000000004000100000000080)) else (if j < 21 then 0x5b80a1d0201c018700010012003810002d005140786000000027000940004000bc00280008001070077c000000000000000014000500014002b0006c01c30000000030041800300000c0a07004e00a37007fc0107000ec002f000b80037000580038e03100000000b401440001c0035000d40004000000030000b4000000000002d007000028000bc00380001c003b000100027000a0002d0001000300001c0000000000142000ec001e0287c00c60021c0000000cc00100001800b000018043000001d025018a000f0005a00030005a000040000000186c094016f000bc00d80067c000000000019000040002f000b000000000030030008000e60c070000400001a62d00010041c000100600022e000e6003e034c502561015d003e020c50001000030000c0018000800628003a00003000000000000400010cc06c00020137448dc9128c002c0000c0003000000020000e00038000e000c0005c001580276001e8000c004180001000000000c00d8007600030000c00038010c00004028 else (if j < 22 then 0x49c4dd5944de49271269b01b9826e64a37007660129807280c3a130a86c0a124dc493700c380220044c04937024dc140e144d811260058049373a4dc080c000a80137001004137124dc4ab7126d80137124e6a93b924dc4bb75251c0137134dd6ab7926ed49b9426fd69d79a4db092713ad849c6004dcabb7126d851b6136d80837146d80137028d84977546de51b79a4dd4957176fd5d27134dd0927174dc4bb753edd49bb5571801371251809298255ec937126d80137174dc49b6126d8c937126d801371251801370249c0137004dc0137004dc4dbf526d84d875a6db4db6136d855255249d49b7424dd49d6d24dc4927126e64ea7926dd4dd7934dd0937526e64d37528db4837526dd49bb5372b49b7526d549bb528db49271375e4937128db6d36d249c49d6d26ec4927524dd4936d26dd49b6d36db004e001250048c01030008001380048c01870008000240008c00250048c0025000800028000a00028000a001470060c01830060c00040050c002d0281c3a06000005e0000580002f else 0x1249449371249c4927124dc4927124dc6d26d249449aad2)))))
def summaryCode (node slot : Nat) : Nat :=
  let idx := (summaryGroup (node/1024) + node % 1024)*6+slot
  (summaryWord (idx/1024) >>> (3*(idx % 1024))) &&& 7
def summaryAt (c : NodeContext) (slot : Nat) (p : BoundPool) : QuickPool :=
  let v := if slot < 6 then summaryCode c.2.2.2.2.2.2 slot else 0
  if v=0 then summarizePool c.2.2.1 p else (p,v-1,true)

def summaryValidAt (c : NodeContext) (slot : Nat) :=
  let v := if slot < 6 then summaryCode c.2.2.2.2.2.2 slot else 0
  v==0 || match c.2.2.2.2.1[slot]? with
    | some p => (summarizePool c.2.2.1 p).2 == (v-1,true)
    | none => false

def summariesOK (c : NodeContext) :=
  (List.range c.2.2.2.2.1.length).all (summaryValidAt c)

theorem summaryAt_good {c slot p} (ok : summariesOK c=true) (e : c.2.2.2.2.1[slot]?=some p) :
    summaryAt c slot p = summarizePool c.2.2.1 p := by
  have hslot : slot < c.2.2.2.2.1.length := (List.getElem?_eq_some_iff.mp e).choose
  have witness := List.all_eq_true.mp ok slot (List.mem_range.mpr hslot)
  let v := if slot < 6 then summaryCode c.2.2.2.2.2.2 slot else 0
  by_cases empty : v=0
  · change (if v=0 then _ else _) = _
    rw [if_pos empty]
  · simp only [summaryValidAt,e] at witness
    change (v==0 || ((summarizePool c.2.2.1 p).2 == (v-1,true))) = true at witness
    simp only [beq_iff_eq,Bool.or_eq_true,empty,false_or] at witness
    change (if v=0 then _ else _) = _
    rw [if_neg empty]
    exact Prod.ext rfl witness.symm

def trivialAt (c : NodeContext) (i j op : Nat) :=
  let a := contextWire c i
  let b := contextWire c j
  let z := (movedDecor op a b).1
  if i<c.2.2.1.length ∧ j<c.2.2.1.length ∧ (z=a.1 ∨ z=b.1) then true else storedAt c i j op

theorem trivialAt_good {c i j op ka kb} (ok : trivialAt c i j op = true) :
    checkAt c i j op ka kb = true := by
  apply storedAt_good
  unfold trivialAt at ok
  dsimp only at ok
  split at ok
  next h =>
    have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
      simp [contextWire,List.getD_eq_getElem?_getD,ht]
    unfold storedAt
    rw [Bool.or_eq_true]
    right
    apply List.any_eq_true.mpr
    rcases h with ⟨hi,hj,e|e⟩
    · exact ⟨_,mem i hi,beq_iff_eq.mpr e.symm⟩
    · exact ⟨_,mem j hj,beq_iff_eq.mpr e.symm⟩
  next => exact ok

def directAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  closeChild c.2.2.2.2.1 c.2.2.2.2.2.1 (c.1-1)
    ((opKeep (op==2) ka kb a b c.2.2.1).map Prod.fst) (movedChoice op a b)

theorem directAt_good {c i j op ka kb} (h : directAt c i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [checkAt,evalMove]
  repeat' split
  all_goals first | rfl | exact h

def quickPick (c : NodeContext) (which i j op : Nat) (ka kb : Bool) :=
  match c.2.2.2.2.1[which]? with
  | none => false
  | some p => fastCost (summaryAt c which p) (c.1-1)
      (contextWire c i) (contextWire c j) op ka kb

theorem quickPick_good {c which i j op ka kb} (ok : summariesOK c=true) (h : quickPick c which i j op ka kb = true) :
    quickAt c i j op ka kb = true := by
  unfold quickPick at h
  split at h
  next => contradiction
  next p e =>
    apply List.any_eq_true.mpr
    exact ⟨_,List.mem_map.mpr ⟨p,List.mem_of_getElem? e,rfl⟩,by simpa only [summaryAt_good ok e] using h⟩

def checkWith (tag : Nat) (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  match tag with
  | 0 => trivialAt c i j op
  | 1 => directAt c i j op ka kb
  | n+2 => (decide (i<c.2.2.1.length ∧ j<c.2.2.1.length)) && quickPick c n i j op ka kb

theorem checkWith_sound {tag c i j op ka kb} (cert : summariesOK c=true) (h : checkWith tag c i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  cases tag with
  | zero => exact trivialAt_good h
  | succ n =>
    cases n with
    | zero => exact directAt_good h
    | succ t =>
      simp only [checkWith,Bool.and_eq_true,decide_eq_true_eq] at h
      exact quickAt_good h.1.1 h.1.2 (quickPick_good cert h.2)

def fallbackAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  checkWith (route c.2.2.2.2.2.2 i j op ka kb) c i j op ka kb

theorem fallback_sound {c i j op ka kb} (cert : summariesOK c=true) (h : fallbackAt c i j op ka kb=true) :
    checkAt c i j op ka kb=true := checkWith_sound cert h

def batchMove (b : Batch) (xs : List NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,u,v) := b
  let un := op==2
  let len := 1+(n-(if ka then 0 else 1)-(if un || kb then 0 else 1))
  if len>k then true else
    let d := len==k
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp (r*(BitVec.allOnes 129).toNat) op a b'
    let cov := if d then v else u
    let mask := fullMarks r (takePacked cov (packedColumn d a) (packedColumn d b') un ka kb ||| packedColumn d z)
    onMarks (fun c => fallbackAt c i j op ka kb) mask xs

theorem batchMove_at (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (cert : summariesOK xs[q]=true)
    (pass : batchMove (makeBatch k n xs) xs i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1))
  let d := len==k
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] d (op==2) ka kb op i j != BitVec.allOnes 129 then true
      else if !properB (movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild xs[q].2.2.2.2.1 xs[q].2.2.2.2.2.1 (k-1)
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
        packedColumn d (packedOp (r*(BitVec.allOnes 129).toNat) op a b))) xs) = true at pass
    rw [if_neg small] at pass
    have chosen : cov = packedCov (fun c => getCov c.2.2.2.1 d) xs := by
      dsimp only [cov]
      cases d <;> rfl
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,chosen,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] d (op==2) ka kb op i j = BitVec.allOnes 129
    · apply fallback_sound cert
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
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (cert : summariesOK xs[q]=true) (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows (makeBatch k n xs) xs js=true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    have check := @batchMove_at k n xs
    refine ⟨⟨⟨check hi hi hq budget arity cert allRows.1.1.1,check hi hi hq budget arity cert allRows.1.1.2⟩,?_⟩,
      ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    have both := allRows.1.2 j hj
    have opCheck (d : Bool) (pass : batchPair (makeBatch k n xs) xs i j (if d then 1 else 0)=true) :
        testPair xs[q] (contextWire xs[q] i) (contextWire xs[q] j) d=true := by
      simp only [batchPair,Bool.and_eq_true] at pass
      simp only [testPair,Bool.and_eq_true]
      exact ⟨⟨⟨check hi hj' hq budget arity cert pass.1.1.1,check hi hj' hq budget arity cert pass.1.1.2⟩,
        check hi hj' hq budget arity cert pass.1.2⟩,check hi hj' hq budget arity cert pass.2⟩
    exact ⟨opCheck false both.1,opCheck true both.2⟩

def runBatch (k n : Nat) (xs : List NodeContext) :=
    batchRows (makeBatch k n xs) xs (List.range n)
theorem runBatch_at {k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hn : xs[q].2.2.1.length=n) (cert : summariesOK xs[q]=true)
    (pass : runBatch k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha cert (List.range n) (fun _ => List.mem_range.mp) pass
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
  (k,ws.length,ws,preCov ws,rules,ls,(g.mask*16+k)*1024+i)


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
  (contexts g k start n).all (fun c => c.2.1==ar && prelim (targetOf g) c && summariesOK c)
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
  have ha : xs[q].2.1=ar := e ▸ one.1.1
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.1.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hn (e ▸ one.2) (cutsRun h)

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
def g15samples : Array (Bits × Bits) := #[(0x1fffffffffffffffffffffffffffffff1,0x1fffffffffffffffffffffffffffffff9),(0x16,0x4),(0x1ffffffffffffffffffffffffffffffef,0xa),(0x1ffffffffffffffffffffffffffffffe9,0x1fffffffffffffffffffffffffffffff5),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
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
def g31samples : Array (Bits × Bits) := #[(0x2ad2,0x18c2),(0x1ffffffffffffffffffffffffffffc3a5,0x1ffffffffffffffffffffffffffffe305),(0x1876,0x72),(0x1ffffffffffffffffffffffffffffdfc9,0x1ffffffffffffffffffffffffffffde81),(0x1ffffffffffffffffffffffffffffe53f,0x213c),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
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
def g47samples : Array (Bits × Bits) := #[(0x1ffffffffffffffffffffffffffffffff,0x0),(0x1ffffffffffffffffffffffffffffffff,0x1ffffffffffffffffffffffffffffffff),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x1ffffffffffffffffffffffffffffffff,0x1ffffffffffffffffffffffffffffffff),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g47columns : IndexTree ColumnInfo := (.leaf [(8,0,39,0,4)])
def g47autos : Array (List Nat) := #[[],[83,32]]
def g47levels : Nat → Packing
  | _ => emptyPacking
def g47index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g47 : Forest := ⟨47,4,fun j => g47samples[j]?.getD (0,0),g47columns,g47autos,g47levels,g47index⟩
def g55samples : Array (Bits × Bits) := #[(0x1ffffffffffffffffffffffffffffffff,0x0),(0x1ffffffffffffffffffffffffffffffff,0x1ffffffffffffffffffffffffffffffff),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x1ffffffffffffffffffffffffffffffff,0x1ffffffffffffffffffffffffffffffff),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g55columns : IndexTree ColumnInfo := (.leaf [(16,0,39,0,4)])
def g55autos : Array (List Nat) := #[[],[84]]
def g55levels : Nat → Packing
  | _ => emptyPacking
def g55index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g55 : Forest := ⟨55,4,fun j => g55samples[j]?.getD (0,0),g55columns,g55autos,g55levels,g55index⟩
def g63samples : Array (Bits × Bits) := #[(0x1ffffffffffffffffffffffffffffffff,0x0),(0x1ffffffffffffffffffffffffffffffff,0x1ffffffffffffffffffffffffffffffff),(0x0,0x0),(0x0,0x0),(0x1ffffffffffffffffffffffffffffffff,0x1ffffffffffffffffffffffffffffffff),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g63columns : IndexTree ColumnInfo := (.leaf [(32,0,31,0,7)])
def g63autos : Array (List Nat) := #[[],[50,65]]
def g63levels : Nat → Packing
  | _ => emptyPacking
def g63index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g63 : Forest := ⟨63,7,fun j => g63samples[j]?.getD (0,0),g63columns,g63autos,g63levels,g63index⟩
def g111d6 (i : Nat) : Nat := 0x120ff
def g111l6 : Packing := (1,0,2,0,1,0,0,g111d6)
def g111samples : Array (Bits × Bits) := #[(0x1fffffffffffffffffffffffffffffbe9,0x1fffffffffffffffffffffffffffffb89),(0x4d4,0x450),(0x3ba,0x2aa),(0x1fffffffffffffffffffffffffffffb47,0x1fffffffffffffffffffffffffffffd45),(0x0,0x0),(0x1fffffffffffffffffffffffffffff83f,0x436),(0x1fffffffffffffffffffffffffffffd27,0x1fffffffffffffffffffffffffffffb27),(0x0,0x0),(0x0,0x0)]
def g111columns : IndexTree ColumnInfo := (.leaf [(4,8,99,0,4),(1,32,78,0,4),(64,0,47,0,5)])
def g111autos : Array (List Nat) := #[[],[83,32]]
def g111levels : Nat → Packing
  | 6 => g111l6
  | _ => emptyPacking
def g111index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | _ => fun _ => none
def g111 : Forest := ⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index⟩
def g119samples : Array (Bits × Bits) := #[(0x1ffffffffffffffffffffffffffffffff,0x0),(0x1ffffffffffffffffffffffffffffffff,0x1ffffffffffffffffffffffffffffffff),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x1ffffffffffffffffffffffffffffffff,0x1ffffffffffffffffffffffffffffffff),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
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
def g189samples : Array (Bits × Bits) := #[(0x1fffffffffffffffffffffffffff14bb3,0xd42b2),(0x0,0x0),(0x1fffffffffffffffffffffffffffd5635,0x1fffffffffffffffffffffffffff94225),(0xe65d8,0x60598),(0x2b866,0xb844),(0x1fffffffffffffffffffffffffff385cd,0x1fffffffffffffffffffffffffff2054d),(0x0,0x0),(0x4ba1e,0x4b812),(0x0,0x0)]
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
def g127samples : Array (Bits × Bits) := #[(0x1ffffffffffffffffffffffffffffffff,0x0),(0x1ffffffffffffffffffffffffffffffff,0x1ffffffffffffffffffffffffffffffff),(0x0,0x0),(0x0,0x0),(0x1ffffffffffffffffffffffffffffffff,0x1ffffffffffffffffffffffffffffffff),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
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
def g191samples : Array (Bits × Bits) := #[(0x440a8aaa5d57092c,0x504c480a25d160820),(0x30422d0e4a68a2788,0x183a544422082788),(0x1ffffffffffffffff00e0728ad8b168d1,0x306c1288898b10850),(0x1fffffffffffffff832406574667c84c9,0x1fffffffffffffffcc122c534464c0489),(0x3a002f512189ef54,0x23a003a412081e354),(0xc93d0c1d32e417e2,0x249296d1822e005c2),(0x0,0x0),(0x1fffffffffffffffc999790670a08521f,0x1fffffffffffffffcb01690670008520d),(0x0,0x0)]
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
def g251samples : Array (Bits × Bits) := #[(0x1ffffffffffffffffffffffffffffffff,0x0),(0x1ffffffffffffffffffffffffffffffff,0x1ffffffffffffffffffffffffffffffff),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x1ffffffffffffffffffffffffffffffff,0x1ffffffffffffffffffffffffffffffff),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g251columns : IndexTree ColumnInfo := (.leaf [(8,0,243,0,7)])
def g251autos : Array (List Nat) := #[[],[84,115],[99,65],[118,84,115,65],[118,81],[118,84,99,81]]
def g251levels : Nat → Packing
  | _ => emptyPacking
def g251index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g251 : Forest := ⟨251,7,fun j => g251samples[j]?.getD (0,0),g251columns,g251autos,g251levels,g251index⟩
def g255samples : Array (Bits × Bits) := #[(0x1ffffffffffffffffffffffffffffffff,0x0),(0x1ffffffffffffffffffffffffffffffff,0x1ffffffffffffffffffffffffffffffff),(0x0,0x0),(0x0,0x0),(0x1ffffffffffffffffffffffffffffffff,0x1ffffffffffffffffffffffffffffffff),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
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
def g383samples : Array (Bits × Bits) := #[(0x1fffffffffffffffc425a9706aebc902b,0x3006113042abc9028),(0x896cf83bb54b4c88,0xf088083a95434c00),(0x1ffffffffffffffff0e268b40483914b1,0x1ffffffffffffffff0e268300483800b1),(0x2640376ee7282d650,0xc15934463082d640),(0x1fffffffffffffffc3a86c8b0c945e1c3,0x1fffffffffffffffc3a86c8b0c1412183),(0xf11ce4f515206620,0xf11ce4f114004600),(0x301f0f78518d89966,0x30174f78508889066),(0x0,0x0),(0x1fffffffffffffffd90810918c3f6239d,0x1fffffffffffffffc0e800808c3742199)]
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
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_1 : block g191 7 13 15=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
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
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_2 : block g191 8 68 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
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
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
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
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
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
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_1 : block g383 9 9 75=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
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
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_2 : block g383 10 21 20=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
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
def deadsamples : Array (Bits × Bits) := #[(0x14221701c72e045161779823060,0x1a1082940926005121269021060),(0x23004220740e3a8df4622c2e08,0xa22c00220083a0de4002c2e08),(0x55228d4d042ddf228d48258f0,0x41541410d842c4f200d48000e0),(0x8448857106f9324106a168db0c,0x19401636004a13201062168d800),(0x1fffffe4af6941f601fcca8e19f24249d,0x1fffffe4af6941f601ec8a8e19604249d),(0x188855402c59882e9a202ede8c2,0xe515420449882c1a002a1e880),(0x1fffffef51127604df502104843d1d461,0x1fffffef51127604df500100843c1d041),(0x1ffffffa082a8810325310f5d2c4b0297,0x1ffffffa082a8810325310c5d284a0217),(0x1fffffe183e010a8a22ed34908414873b,0xae0083b2024d24108414073a)]
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
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead9_12 : block dead 9 12 13=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
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
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_42 : block dead 10 42 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_78 : block dead 10 78 35=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_113 : block dead 10 113 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
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
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_40 : block dead 11 40 15=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_55 : block dead 11 55 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_91 : block dead 11 91 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_127 : block dead 11 127 29=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_156 : block dead 11 156 27=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=0)
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


-- If the supplied wire vanishes from the live set, its original circuit
-- lower bound applies. Otherwise the raw input witnesses force the entire
-- augmented starting set to be live.
theorem augmentedLower {raw : List Sig} {e T : Sig} {k : Nat} (hp : proper T)
    (old : Lower raw T (k+1))
    (must : ∀ a ∈ raw, Essential T (raw++[e]) a)
    (no : Impossible T k (raw++[e]).toFinset) : Lower (raw++[e]) T (k+1) := by
  intro p bank hr ha
  obtain ⟨n,t,S,hn,run,sub⟩ := reach_live hp hr ha
  by_cases he : e ∈ S
  · have eq : (raw++[e]).toFinset = S := by
      ext a
      rw [List.mem_toFinset]
      refine ⟨?_,sub a⟩
      intro hm
      rcases List.mem_append.mp hm with hw | hw
      · obtain ⟨r,s,hd,iso⟩ := must a hw
        exact raw_required run _ a sub r s hd iso
      · have same : a=e := by simpa using hw
        exact same.symm ▸ he
    by_contra! small
    exact no n t (by omega) (eq.symm ▸ run)
  · have supp : supply (raw.map observe) (S.toList.map observe) := by
      intro a ha
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ha
      have mem : v ∈ S := by simpa using hv
      apply Or.inl
      apply List.mem_map_of_mem
      rcases List.mem_append.mp (sub v mem) with hw | hw
      · exact hw
      · have eq : v=e := by simpa using hw
        exact False.elim (he (eq ▸ mem))
    obtain ⟨q,W,reach,goal,budget⟩ := contraction (observe_proper hp)
      (list_run run S.toList (Finset.nodup_toList _) (by simp)) _ Reach.start supp
    have bound := old q W reach goal
    omega

theorem augmentedGraph {m k hints tagged}
    (hp : properB (graphGoal m) = true)
    (rawEq : vars tagged = vars m ++ [orSeed]) (goalEq : graphGoal tagged = graphGoal m)
    (old : Lower (vars m) (graphGoal m) (k+1))
    (ess : checkEssential (graphGoal m) (vars tagged) (graphPairs m hints) = true)
    (all : (graphPairs m hints).map Prod.fst = vars m)
    (no : Impossible (graphGoal tagged) k (vars tagged).toFinset) :
    Lower (vars tagged) (graphGoal tagged) (k+1) := by
  rw [goalEq,rawEq] at no ⊢
  apply augmentedLower (proper_of _ hp) old _ no
  intro a ha
  rw [←rawEq]
  apply essential_ok ess
  rw [all]
  exact List.mem_toFinset.mpr ha

theorem countImpossible {T : Sig} {S : Finset Sig} {k : Nat} (small : k+1 < S.card) :
    Impossible T k S := by
  intro n t budget run
  have h := (live_size run).2
  omega
-- For an induced graph containing edge (0,4), supply the OR of its
-- endpoints for free. Each bound can then be reused on a smaller set of
-- rows when the same two endpoints survive a restriction.

namespace Free23

theorem noRun : Impossible (graphGoal 2071) 3 (vars 2071).toFinset := countImpossible (by decide +kernel)

end Free23

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound23 : Lower (vars 2071) (graphGoal 2071) 4 :=
  augmentedGraph (k:=3) (m:=23) (hints:=260) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 23) (by decide +kernel) (by decide +kernel) Free23.noRun

def entries23 := extendKnown known383 4 [(2071,[]),(2077,[49,64]),(2225,[114,33,97,82,49]),(2329,[130,114,98,82,49,64]),(2353,[130,114,33,97,82,49])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound23 : Known entries23 := extendKnown_ok valid383 seededBound23 (by decide +kernel)
namespace Free27

theorem noRun : Impossible (graphGoal 2075) 3 (vars 2075).toFinset := countImpossible (by decide +kernel)

end Free27

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound27 : Lower (vars 2075) (graphGoal 2075) 4 :=
  augmentedGraph (k:=3) (m:=27) (hints:=16388) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 27) (by decide +kernel) (by decide +kernel) Free27.noRun

def entries27 := extendKnown entries23 4 [(2075,[]),(2105,[49,81,33,64])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound27 : Known entries27 := extendKnown_ok sound23 seededBound27 (by decide +kernel)
namespace Free31

def liveData6 (i : Nat) : Nat := 0x1103fd40

def moveIndex6 (i : Nat) : Nat := 0x1690a11080000203e018

def liveData5 (i : Nat) : Nat := 0x1008041db920bf2aa817d52502faa2a07e4c140

def liveLevels : Nat → Packing
  | 6 => (1,1,2,0,0,0,0,liveData6)
  | 5 => (4,2,2,0,0,5,0,liveData5)
  | _ => emptyPacking

def liveIndex : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 3 8 2 10 2 4 moveIndex6
  | _ => fun _ => none

def orSamples : Array (Bits × Bits) := #[(0x1ffffffffffffffffffffffffffff838b,0x21c8),(0x1ffffffffffffffffffffffffffffcc0f,0x1ffffffffffffffffffffffffffffc403),(0xff4,0xb94),(0x70f8,0x1ffffffffffffffffffffffffffffb069),(0x7f00,0x4e02),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]

def orSymmetries : Array (List Nat) := #[[],[65,50],[16,66],[16,32,48,64],[32,67],[32,49,64,16],[48,33],[48,65,32,33],[64,16,33,50],[64,49]]

def orCols : IndexTree ColumnInfo := (.leaf [(2,0,2077,0,4),(4,0,2075,0,4),(8,0,2071,0,4)])

def orForest : Forest := ⟨2079,6,fun j => orSamples[j]?.getD (0,0),orCols,orSymmetries,liveLevels,liveIndex⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem orGeometry : graphValid orForest (boundsBefore entries27) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked6At0 : block orForest 6 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked5At0 : block orForest 5 0 4 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

theorem allAt6 : block orForest 6 0 1 = true := checked6At0
theorem allAt5 : block orForest 5 0 4 = true := checked5At0
theorem orTables : checkedTables orForest 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block orForest 0 0 0 = true)
  · exact (rfl : block orForest 1 0 0 = true)
  · exact (rfl : block orForest 2 0 0 = true)
  · exact (rfl : block orForest 3 0 0 = true)
  · exact (rfl : block orForest 4 0 0 = true)
  · exact allAt5
  · exact allAt6

theorem noRun : Impossible (graphGoal 2079) 6 (vars 2079).toFinset :=
  root_index (g:=orForest) (before_sound _ sound27) orGeometry orTables
    (k:=6) (by decide) (i:=0) (by decide +kernel)

end Free31

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound31 : Lower (vars 2079) (graphGoal 2079) 7 :=
  augmentedGraph (k:=6) (m:=31) (hints:=8452) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 31) (by decide +kernel) (by decide +kernel) Free31.noRun

def entries31 := extendKnown entries27 7 [(2079,[]),(2361,[130,114,49,98,81,64])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound31 : Known entries31 := extendKnown_ok sound27 seededBound31 (by decide +kernel)
namespace Free55

theorem noRun : Impossible (graphGoal 2103) 4 (vars 2103).toFinset := countImpossible (by decide +kernel)

end Free55

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound55 : Lower (vars 2103) (graphGoal 2103) 5 :=
  augmentedGraph (k:=4) (m:=55) (hints:=260) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 55) (by decide +kernel) (by decide +kernel) Free55.noRun

def entries55 := extendKnown entries31 5 [(2103,[]),(2163,[98,50]),(2227,[114,98,50,81])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound55 : Known entries55 := extendKnown_ok sound31 seededBound55 (by decide +kernel)
namespace Free61

theorem noRun : Impossible (graphGoal 2109) 4 (vars 2109).toFinset := countImpossible (by decide +kernel)

end Free61

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound61 : Lower (vars 2109) (graphGoal 2109) 5 :=
  augmentedGraph (k:=4) (m:=61) (hints:=8964) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 61) (by decide +kernel) (by decide +kernel) Free61.noRun

def entries61 := extendKnown entries55 5 [(2109,[]),(2233,[114,83,98,64])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound61 : Known entries61 := extendKnown_ok sound55 seededBound61 (by decide +kernel)
namespace Free151

theorem noRun : Impossible (graphGoal 2199) 4 (vars 2199).toFinset := countImpossible (by decide +kernel)

end Free151

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound151 : Lower (vars 2199) (graphGoal 2199) 5 :=
  augmentedGraph (k:=4) (m:=151) (hints:=536871172) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 151) (by decide +kernel) (by decide +kernel) Free151.noRun

def entries151 := extendKnown entries61 5 [(2199,[]),(2229,[81,114,49]),(2387,[135,98,82,50]),(2393,[130,114,98,82,49,64]),(2417,[130,114,33,97,82,49])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound151 : Known entries151 := extendKnown_ok sound61 seededBound151 (by decide +kernel)
namespace Free433

theorem noRun : Impossible (graphGoal 2481) 4 (vars 2481).toFinset := countImpossible (by decide +kernel)

end Free433

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound433 : Lower (vars 2481) (graphGoal 2481) 5 :=
  augmentedGraph (k:=4) (m:=433) (hints:=22817013764) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 433) (by decide +kernel) (by decide +kernel) Free433.noRun

def entries433 := extendKnown entries151 5 [(2481,[])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound433 : Known entries433 := extendKnown_ok sound151 seededBound433 (by decide +kernel)
namespace Free63

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem noRun : Impossible (graphGoal 2111) 7 (vars 2111).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2111) (32,0,2079,0,7) _ (before_sound _ sound433) (by decide +kernel))
    [] (pool:=(vars (poolMask 2111 (32,0,2079,0,7)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Free63

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound63 : Lower (vars 2111) (graphGoal 2111) 8 :=
  augmentedGraph (k:=7) (m:=63) (hints:=8452) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 63) (by decide +kernel) (by decide +kernel) Free63.noRun

def entries63 := extendKnown entries433 8 [(2111,[])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound63 : Known entries63 := extendKnown_ok sound433 seededBound63 (by decide +kernel)
namespace Free95

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem noRun : Impossible (graphGoal 2143) 7 (vars 2143).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2143) (64,0,2079,0,7) _ (before_sound _ sound63) (by decide +kernel))
    [] (pool:=(vars (poolMask 2143 (64,0,2079,0,7)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Free95

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound95 : Lower (vars 2143) (graphGoal 2143) 8 :=
  augmentedGraph (k:=7) (m:=95) (hints:=16785668) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 95) (by decide +kernel) (by decide +kernel) Free95.noRun

def entries95 := extendKnown entries63 8 [(2143,[]),(2365,[130,114,49,98,81,64]),(2489,[98,134,114,81])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound95 : Known entries95 := extendKnown_ok sound63 seededBound95 (by decide +kernel)
namespace Free119

theorem noRun : Impossible (graphGoal 2167) 5 (vars 2167).toFinset := countImpossible (by decide +kernel)

end Free119

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound119 : Lower (vars 2167) (graphGoal 2167) 6 :=
  augmentedGraph (k:=5) (m:=119) (hints:=16777476) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 119) (by decide +kernel) (by decide +kernel) Free119.noRun

def entries119 := extendKnown entries95 6 [(2167,[])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound119 : Known entries119 := extendKnown_ok sound95 seededBound119 (by decide +kernel)
namespace Free159

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem noRun : Impossible (graphGoal 2207) 7 (vars 2207).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2207) (128,0,2079,0,7) _ (before_sound _ sound119) (by decide +kernel))
    [] (pool:=(vars (poolMask 2207 (128,0,2079,0,7)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Free159

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound159 : Lower (vars 2207) (graphGoal 2207) 8 :=
  augmentedGraph (k:=7) (m:=159) (hints:=536879364) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 159) (by decide +kernel) (by decide +kernel) Free159.noRun

def entries159 := extendKnown entries119 8 [(2207,[]),(2425,[130,114,49,98,81,64])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound159 : Known entries159 := extendKnown_ok sound119 seededBound159 (by decide +kernel)
namespace Free183

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem noRun : Impossible (graphGoal 2231) 7 (vars 2231).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2231) (16,0,167,0,7) _ (before_sound _ sound159) (by decide +kernel))
    [] (pool:=(vars (poolMask 2231 (16,0,167,0,7)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Free183

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound183 : Lower (vars 2231) (graphGoal 2231) 8 :=
  augmentedGraph (k:=7) (m:=183) (hints:=536871172) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 183) (by decide +kernel) (by decide +kernel) Free183.noRun

def entries183 := extendKnown entries159 8 [(2231,[]),(2419,[135,98,50])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound183 : Known entries183 := extendKnown_ok sound159 seededBound183 (by decide +kernel)
namespace Free187

def liveData6 (i : Nat) : Nat := 0x105fd30

def moveIndex6 (i : Nat) : Nat := 0xe0

def liveData5 (i : Nat) : Nat := 0x102f54c530

def liveLevels : Nat → Packing
  | 6 => (1,1,1,0,0,0,0,liveData6)
  | 5 => (1,2,1,0,0,0,0,liveData5)
  | _ => emptyPacking

def liveIndex : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 moveIndex6
  | _ => fun _ => none

def orSamples : Array (Bits × Bits) := #[(0x1fffffffffffffffffffffffffffffe67,0x1fffffffffffffffffffffffffffffe25),(0x1fffffffffffffffffffffffffffffe03,0x1da),(0x0,0x0),(0x18,0x2c),(0x1c,0x1d2),(0x1e0,0xc0),(0x0,0x0),(0x180,0x112),(0x0,0x0)]

def orSymmetries : Array (List Nat) := #[[],[115,84]]

def orCols : IndexTree ColumnInfo := (.leaf [(10,0,2225,0,4),(16,8,163,0,4)])

def orForest : Forest := ⟨2235,6,fun j => orSamples[j]?.getD (0,0),orCols,orSymmetries,liveLevels,liveIndex⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem orGeometry : graphValid orForest (boundsBefore entries183) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked6At0 : block orForest 6 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked5At0 : block orForest 5 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

theorem allAt6 : block orForest 6 0 1 = true := checked6At0
theorem allAt5 : block orForest 5 0 1 = true := checked5At0
theorem orTables : checkedTables orForest 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block orForest 0 0 0 = true)
  · exact (rfl : block orForest 1 0 0 = true)
  · exact (rfl : block orForest 2 0 0 = true)
  · exact (rfl : block orForest 3 0 0 = true)
  · exact (rfl : block orForest 4 0 0 = true)
  · exact allAt5
  · exact allAt6

theorem noRun : Impossible (graphGoal 2235) 6 (vars 2235).toFinset :=
  root_index (g:=orForest) (before_sound _ sound183) orGeometry orTables
    (k:=6) (by decide) (i:=0) (by decide +kernel)

end Free187

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound187 : Lower (vars 2235) (graphGoal 2235) 7 :=
  augmentedGraph (k:=6) (m:=187) (hints:=1342193668) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 187) (by decide +kernel) (by decide +kernel) Free187.noRun

def entries187 := extendKnown entries183 7 [(2235,[])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound187 : Known entries187 := extendKnown_ok sound183 seededBound187 (by decide +kernel)
namespace Free189

def liveData7 (i : Nat) : Nat := 0x83fd30

def moveIndex7 (i : Nat) : Nat := 0xd16f801819ec827900

def liveData6 (i : Nat) : Nat := 0x2100c920bf58930bf58530fe48130

def liveLevels : Nat → Packing
  | 7 => (1,1,2,0,0,0,0,liveData7)
  | 6 => (3,2,2,0,0,5,0,liveData6)
  | _ => emptyPacking

def liveIndex : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 3 8 3 9 2 3 moveIndex7
  | _ => fun _ => none

def orSamples : Array (Bits × Bits) := #[(0x1fffffffffffffffffffffffffff0187f,0x1fffffffffffffffffffffffffff08c4f),(0x0,0x0),(0x1fffffffffffffffffffffffffff06fc7,0x1fffffffffffffffffffffffffff02ae5),(0x1fffffffffffffffffffffffffff58183,0x4811a),(0x9f004,0x97020),(0xe01f8,0x401b0),(0x0,0x0),(0xffe00,0xbd400),(0x0,0x0)]

def orSymmetries : Array (List Nat) := #[[],[115,84],[32,67,117],[32,83,116],[48,82],[48,82,112,66],[64,114,50,48,80],[64,114,83],[80,50,116],[80,50,66,32,114],[112,66,48,82],[112,66]]

def orCols : IndexTree ColumnInfo := (.leaf [(8,0,2229,0,5),(12,0,2225,0,4),(17,0,172,0,4)])

def orForest : Forest := ⟨2237,7,fun j => orSamples[j]?.getD (0,0),orCols,orSymmetries,liveLevels,liveIndex⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem orGeometry : graphValid orForest (boundsBefore entries187) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked7At0 : block orForest 7 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked6At0 : block orForest 6 0 3 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

theorem allAt7 : block orForest 7 0 1 = true := checked7At0
theorem allAt6 : block orForest 6 0 3 = true := checked6At0
theorem orTables : checkedTables orForest 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block orForest 0 0 0 = true)
  · exact (rfl : block orForest 1 0 0 = true)
  · exact (rfl : block orForest 2 0 0 = true)
  · exact (rfl : block orForest 3 0 0 = true)
  · exact (rfl : block orForest 4 0 0 = true)
  · exact (rfl : block orForest 5 0 0 = true)
  · exact allAt6
  · exact allAt7

theorem noRun : Impossible (graphGoal 2237) 7 (vars 2237).toFinset :=
  root_index (g:=orForest) (before_sound _ sound187) orGeometry orTables
    (k:=7) (by decide) (i:=0) (by decide +kernel)

end Free189

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound189 : Lower (vars 2237) (graphGoal 2237) 8 :=
  augmentedGraph (k:=7) (m:=189) (hints:=536879876) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 189) (by decide +kernel) (by decide +kernel) Free189.noRun

def entries189 := extendKnown entries187 8 [(2237,[]),(2395,[135,98,82,33,49,64])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound189 : Known entries189 := extendKnown_ok sound187 seededBound189 (by decide +kernel)
namespace Free215

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem noRun : Impossible (graphGoal 2263) 6 (vars 2263).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2263) (0,16,198,1,5) _ (before_sound _ sound189) (by decide +kernel))
    [] (pool:=(vars (poolMask 2263 (0,16,198,1,5)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Free215

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound215 : Lower (vars 2263) (graphGoal 2263) 7 :=
  augmentedGraph (k:=6) (m:=215) (hints:=553648388) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 215) (by decide +kernel) (by decide +kernel) Free215.noRun

def entries215 := extendKnown entries189 7 [(2263,[]),(2397,[130,114,98,49,64]),(2461,[134,49,64]),(2485,[134,81,114,49]),(2545,[118,33,129,82,49])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound215 : Known entries215 := extendKnown_ok sound189 seededBound215 (by decide +kernel)
namespace Free243

def liveData6 (i : Nat) : Nat := 0x1fd20

def liveLevels : Nat → Packing
  | 6 => (1,1,0,0,0,0,0,liveData6)
  | _ => emptyPacking

def liveIndex : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none

def orSamples : Array (Bits × Bits) := #[(0x1fffffffffffffffffffffffffffffe1f,0x1fffffffffffffffffffffffffffffe15),(0x1fffffffffffffffffffffffffffffe63,0xc2),(0x0,0x0),(0x0,0x0),(0xc,0x1ea),(0x190,0xa0),(0x60,0x38),(0x180,0x142),(0x0,0x0)]

def orSymmetries : Array (List Nat) := #[[],[81,118]]

def orCols : IndexTree ColumnInfo := (.leaf [])

def orForest : Forest := ⟨2291,6,fun j => orSamples[j]?.getD (0,0),orCols,orSymmetries,liveLevels,liveIndex⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem orGeometry : graphValid orForest (boundsBefore entries215) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked6At0 : block orForest 6 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

theorem allAt6 : block orForest 6 0 1 = true := checked6At0
theorem orTables : checkedTables orForest 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block orForest 0 0 0 = true)
  · exact (rfl : block orForest 1 0 0 = true)
  · exact (rfl : block orForest 2 0 0 = true)
  · exact (rfl : block orForest 3 0 0 = true)
  · exact (rfl : block orForest 4 0 0 = true)
  · exact (rfl : block orForest 5 0 0 = true)
  · exact allAt6

theorem noRun : Impossible (graphGoal 2291) 6 (vars 2291).toFinset :=
  root_index (g:=orForest) (before_sound _ sound215) orGeometry orTables
    (k:=6) (by decide) (i:=0) (by decide +kernel)

end Free243

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound243 : Lower (vars 2291) (graphGoal 2291) 7 :=
  augmentedGraph (k:=6) (m:=243) (hints:=1358954500) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 243) (by decide +kernel) (by decide +kernel) Free243.noRun

def entries243 := extendKnown entries215 7 [(2291,[])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound243 : Known entries243 := extendKnown_ok sound215 seededBound243 (by decide +kernel)
namespace Free127

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem noRun : Impossible (graphGoal 2175) 8 (vars 2175).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2175) (32,0,2143,0,8) _ (before_sound _ sound243) (by decide +kernel))
    [] (pool:=(vars (poolMask 2175 (32,0,2143,0,8)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Free127

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound127 : Lower (vars 2175) (graphGoal 2175) 9 :=
  augmentedGraph (k:=8) (m:=127) (hints:=16785668) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 127) (by decide +kernel) (by decide +kernel) Free127.noRun

def entries127 := extendKnown entries243 9 [(2175,[])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound127 : Known entries127 := extendKnown_ok sound243 seededBound127 (by decide +kernel)
namespace Free191

def liveData10 (i : Nat) : Nat := 0x24508ffd40

def moveIndex10 (i : Nat) : Nat := 0x12b03e000017680069749a9f1873ec6edf06e77428e12ac5e4408fc19418ef6000e062e75b9a2f64c00588e130a0044b4d095884b28a00103000005d2ac292aef03d56100783205a4200016100063180a1

def liveData9 (i : Nat) : Nat := 0xb0d122010ec09087940a04843c8043b0242245020b81211228289878c4c7c08520448844501e320502281c2242805020181a10f30e810709906a143c783884c2f0b02481e1c427110281a11228788048750889874142452843808e021c1e30e1c02911d1201214070c010bc8808910a004384861e2004121d42022280e01a1091228586010ec0c8909c2c300a064484c2622243850201810ca11138709082c04386160442001c24600020191a1120e382810ec089109a0644846052302244258191211888040891096068400448042302254228681a111180828140d08918202c1c903808c0302054322505020e01a11230880075080891a864404622002811214a111280c0d08048960c6011f7dec9e15da1c8db79aa5a1193d8497956c15cd5594453312bd1a90f5000f2ceb8dc4d70cfcc28b34a609ec9388c481077c6a863456048c3d83042301bc1680b4003ff3ba81ff5d940ffaeaa07fd64503feaa281ff5cd40ffac6a07fd53503feb9281ff1c940ffac4a07fd52503fea1281ff4c940ffc44a07fd71503feb0a81ff54540ffa82a07fd31503fe90a81ff58140ffaa0a07fd30503fe90281ff08140ffa20a07fe00502ff3ba817f5d940dfccca05fd75503bf2aa81ef55140f7c88a05fd73503ef19a817f5c940bf8e4a07ee22502feb8a81ef50540fec22a07bc40503fc98281fe80140

def moveIndex9 (i : Nat) : Nat := 0x2447205d11fd61e9462c0e4922ba30745d98ada0c6c2944087850604d540543a78da2037a0d685b78ed203962fc48c389dc09063cb428f0120202000205cc01fc003135a81484e0ca076036c21c0cc80e4032a811fd02c08c6138832591060cd23e5c4570dee0b1044f805b904000000944750000c1e0836c00078d362168171c40587e7001c386864a02d00000003047e0c3614d6110004890900010438000707f0dd880c902ca01ae0b4000244220af11a24101c44000000002055c7c306180abc25c078f0d9412041e547408a0b135412e065f0cf022ea15c43da85ea1044080c1a409e900c4062883c86f0000e0a988400a190d0000205720132139e30004c28520000e4588428000e12a224fc8cc83b50c000034739814217982e2c3c286cd062a1db85d28fad1ece38a022e807014e7adb05f58d49547237e434d112f02e62dc017906d118da128848c01d2049820582168b200be9c3340500006099e3cf46ed05b00000002e5880990001633607a184d507c40bac20e8a200000003c64509bb204c1d686270870001c15a87060aad112000000020b1c149804441ed82bc01ec03145a210090fa834a86e003a00000000c29910c9146838e8328073a1ea215303768eb104f20e506b8000000001c4c72b8869228044587e5ac6506f61f04140000715142cf43810ace12de429811000081aca00b87712c9a15722d6881d0d09107627cc61782c51d30125280204fc08ea1dcc04289201b0439bc54d8ff818ea43dc77800040d5a0cf85e9003806ca3f4c0738b0e116e339402c0ec41294086c83401ea008e3eec86d08c91efe23680c906b20798ad1c18010590c5c35701fc016c0ce1b6d41c0c08040803028a891800902680c0033e05d87362d00400b4e2b800414f6e003838c0150150008031050002000afa0d2107805e09b835a3421202c40872c090820038507004c00302100015c08200000401a1a184010200d82

def liveData8 (i : Nat) : Nat := (if i < 1 then 0xd7158140efd6158140fbd4158140dfe7754140dfd7354140dfc7254140fbd4154140ff9624c140ff9524c140ff9614c140ff9514c140ff9214c140bfd864c140bfd854c140fdd634c140fdd534c140fdd314c140ff9604c140ff9504c140bfe8848140dfc8748140dfe7748140bfd8648140dfd7648140bfd8548140dfd7548140fbd5448140bfd8348140dfd7348140dfd7248140fed5248140ff48148140dfd7148140fbd4148140fed2148140ff96048140ff93048140bfd8608140bfd8508140bfd8644140dfd7644140bfd8544140dfd7544140fbd5444140bfd8344140dfd7344140bfd8244140dfd7244140ff55144140ff93044140ff920441409fd869dd409fd859dd40dbd849dd409fd839dd409fd829dd409fd819dd409fe885d940cfe77999409fe885d540d7e7795540bf88059140bbe8855140dbe7755140fb88055140bf88055140dbe7791140dbd7691140ebe6691140dbd7591140f3e55911409fe885cd40cfe665cd40d7e555cd409fd8758d409fc8758d40cfd7658d409fd8754d409fc8754d40f3d5454d40dde778cd40ddd768cd40ede668cd40ddd758cd40f5e558cd40f9d548cd409fe885c940cfe665c940d7e555c940dbd545c940dbe445c940ddc835c940dde335c940df4815c9409fd861c940cfe661c9409fd851c940d7e551c940dbe441c9409fd831c940dde331c9409fd811c940ded721c9409fd87589409fc87589409fd87549409fc8754940f3d54549409fc8750940dec7250940bf880509409fd874c9409fc874c940dec8788940dee7788940ded7688940eee6688940ded7588940f6e5588940fad5488940fae4488940ded7388940fce33889409fc8788940ded72889409fe885c540cfe665c540d7e555c540dbe445c540dde335c540dee225c5409fd87585409fc87585409fd87545409fc8754540bbe8850540dbe7750540ebe6650540bbd8550540f3e5550540f9e3350540dbd7250540fae2250540fb56150540fb88050540bf880505409fd874c5409fc874c540fb5414c5409fd87485409fc8748540df67784540df57684540ef66684540df57584540f765584540fb55484540fb64484540df57384540fd63384540df57284540df47284540fe62284540f3d5454140dbe7710140ebe6610140bbd8510140f3e5510140dbd7210140fae2210140bbd8110140fb61110140bfa884c140dfa774c140efa664c140f7a554c140fb9544c140fd9634c140fd9534c140df9724c140fea224c140fb9414c140fd9314c140ff2114c1409fd8748140dec7248140fb54144140dfa7780140df97680140efa6680140df97580140f7a5580140fb95480140fba4480140bf98380140df97380140fda3380140df97280140df87280140fea2280140df97180140fb94180140ff21180140b3d8510140bb58110140 else (if i < 2 then 0x23050384010804201080420108580a24188c261e07103c0f1000262318042010c0420080888244808602108c042438086228200a848000840e20d0541a0920040c1181048a051083c6150f03412407054210058204b0400508202851008200005c4212200000044200000a102860a1828422a1090c1e05508508960a080a14090e0a108a0424302a0428382840a011183c800700024306054210058204b040050814200621502301040010a042008800411000af31781bb55d4ee79725b7e5b4ed796aeb4bda4acf7664b26d8b6c2d5f6aefd6feb51588ab8d546a75523a8653fa9e14d9a61528a917474a2ed11a84d40f9fc4f867833aa9c54daa6a7345992cc165dd2d795bca164cb24e91bc85e3ef1e08e046a63371848b6c53625b11688443c61b50c385642320eb05e82840e603300b7fa3f75f8cfb87d0be4def8f5c7a2bc71e0aeee76bbb01d64e9273db991c9ae3f7143821bbedbf6cfb5d9abed486943445a06cec66ab31d960c99645b1d18a8c3d6133061802bea5ee2f1574ab975c02da5692b2958dac115daacd55b2aa1522a8353f29c14c4a5d52c2929478a37514a89141a9ff4f8a7453629884b8a569286935493a48922890f480a36117089843c218508282a4099ff0fdc7d73e49eecf487963b69da0e7e71f37b1b58d6c69f34d1a54cea64c31f18c0c4461d3079828bf85f72f49790b645922bd95b4abe5512a194d4a2a4ec26a92d494e49924591888a844621310607de3ea1f28f3874a3731a98ca863830e1848bec5ec2e81718b545a02b91558a984fa27813989b84d225b12b094449823e11808884281f40e586d03281860b3051827010f08503a81b80ce06482ec16c0a8051825410e082031015009e04101980b802e000dfc825d540fbc8255140bfe8858d40dfe7758d40bfe8854d40dfe7754d40dfd635c940dfd535c940dfd541c940bfd861c940bfd851c940dfd751c940fbd541c940dfe7758940dfd7358940efd6358940bfe8854940dfe7754940f7d5454940dfd7354940f7d5354940dfd7254940dfe774c940bfd854c940dfd754c940fdd634c940dfe7788940dfd7588940fbd5488940dfd635c540dfd535c540dfd525c540dfe225c540bfe8858540dfe7758540dfd7358540dfd7258540bfe8854540dfe7754540dfd7354540dfd7254540dfc7254540f7d5254540fbd6350540fbd5350540fbd6250540fbd5250540fbe2250540ff56150540bfe884c540dfe774c540bfd864c540dfd764c540bfd854c540dfd754c540fbd544c540dfd724c540fdd324c540ff5514c540bfe8848540dfd8748540dfe7748540bfd8648540dfd7648540bfd8548540dfd7548540fbd5448540bfd8348540dfd7348540dfd7248540ff56148540ff53148540bfe8858140dfe7758140dfd7358140efd6358140dfd7258140df else 0x2f16107c202078104190808260f103e021f0a101f010c8508020b893610ba58400685c40d05080e131068288518902e2054842a30588440709c846050a090a81908c260f10343617183c1020d87440205080414b041e1f103c1c2050394230103841c0d081c0a10103820ea143c30c05c40e050808131214141818082a2008842e307404223074045010a842f0118380682182c0220304040f0704c60d8280a0210283d42061834202078184960883c60f0a0246010488260f828c060d102420e0188341e10743ca1185c1a1b18280624b042009101c1228082441b0f080a14048c1622103642290844291121503211c842214089032110581a248842a02105c21482894214828e0a10104e0a0f08102905105a2220944441208882410983824382a844128888160a103820c07083416070c180250c0481b0b83860c01404696064042e40803850148892281808c2e96103820c07081881100421d4d8a0291126c20c4b08340b0b0c1818105c16280841c0c10492228084140b12141901183021248881d011014480e182c1222180020f0a084c0e10384a1318902428d8440121458200b042c10001415084016080261210142050858022418144c0e181442121210380710384c20788840f0a84200b0409608682a0d09113705808d2d05808c2296090e02911027420f183e022d083c41e12080411208840208082080a080410a8781c092000a160083c813128386050d8041e4098901c34888444306848400004460418682a0d049004105054210058204b040050803a150103826501215))

def moveIndex8 (i : Nat) : Nat := 0x888c7cc008c90868c00014200cc8360d901283e0148aa454000c914d64e2c414ae42b047cbe86f88c00000349600f43b8ddc708d14760e4c534258b044c083cec00541e464cbb8ea44845a87a41a8326cb4a28a5c0b4b400382c003c9b461c6805c0c400000289f23802500591440c13c4181153080489

def liveData7 (i : Nat) : Nat := 0xa10142000091484400001b0802108c171002888a010820184502040800812201029089112844088202042208081103c409c0a078d052844002420004200000000004081e10000a080000022100000002210001208220a0243b56d0b2ebcab6a8a8e9ea16809ee7699e588fe2685e12795cc71dae6557c5dd5e51522425043d4f0384dc35cd2334c830cbe2bca026c9621c821f4781cc6417c5a1545012c3c0dc3208c008fec8d10bb2811fd92a21755023fb23442eaa047f6488758d408fec910ea9a811fd91a21725025fb2d442a4a055f25d5354940e9eaa2e4a92819dc8758d325023f930bac44a066f21d5488940afac8ceeb0a811fd9221d515032f90ea92a2a076d5c96150540f5ab12c2a0a819bc875513150376b0ca0a62a07e54c9414c5409becad10b0281eb56150560503e72a8a9260a07e658d414c140fcca9a8298281fb16150530503f32a898a60a07f4545314c140f6cb1ac0982813f591a21205033eb0e40a40a06ed6194144140fd8a0a408828117d95a21765027b326402c8a05e664c80551409ecc9900aa2811bd94a21735023bb27442e4a047d646885c9408ee4c466b92819d48320572502f332640282a04f664c80505408fa4c2e508a811bd989dc4050267d32c2880a064f9dd8510140d1f3330a2028193d855c84050365b0b11080a04eda658110140cdb3bb0220281ab6666044050366caac0880a066d5c98110140dd31130220281b358584440503e32a8a9a60a07e4505314c140

def liveLevels : Nat → Packing
  | 10 => (1,1,6,0,0,0,0,liveData10)
  | 9 => (46,2,6,0,0,12,0,liveData9)
  | 8 => (282,3,6,0,0,13,0,liveData8)
  | 7 => (60,4,6,0,0,10,0,liveData7)
  | _ => emptyPacking

def liveIndex : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 19 55 5 10 6 0 moveIndex10
  | 9 => lookupWord 101 329 7 15 9 2 moveIndex9
  | 8 => lookupWord 21 69 6 12 6 2 moveIndex8
  | _ => fun _ => none

def orSamples : Array (Bits × Bits) := #[(0x1fffffffffffe0002f810267e07ff041f,0x1fffffffffffe00435a400212150d9453),(0x1ffffffffffff970cb018c180080007ff,0x1979ca41c4089a020020c),(0x4fe0f9f00c01ffe0,0x200008e0a9724c497de2),(0x180f700f1e01f001f800,0x1ac772091604b0008214),(0x1e00f800fe001fffe0000,0x1e4088496e0494af04088),(0x1fff0000ffffe00000000,0xab10000ffdec80806308),(0x0,0x0),(0x1fffffff0000000000000,0x154eff710000103008010),(0x0,0x0)]

def orSymmetries : Array (List Nat) := #[[],[115,84],[32,67,117],[32,83,116]]

def orCols : IndexTree ColumnInfo := (.fork 19 (.fork 9 (.fork 4 (.leaf [(1,0,190,0,7),(2,0,2237,0,8),(4,0,2235,0,7),(6,0,2233,0,5)]) (.fork 2 (.leaf [(0,8,163,20,6),(8,0,2231,0,8)]) (.leaf [(10,0,2229,0,5),(4,8,163,16,5),(12,0,2227,0,5)]))) (.fork 5 (.fork 2 (.leaf [(14,0,2225,0,4),(0,16,166,9,6)]) (.leaf [(16,0,175,0,8),(1,16,166,8,5),(17,0,174,0,5)])) (.fork 2 (.leaf [(19,0,172,0,4),(8,16,166,1,5)]) (.leaf [(16,8,163,4,5),(24,0,167,0,7),(9,16,166,0,4)])))) (.fork 10 (.fork 5 (.fork 2 (.leaf [(25,0,166,0,4),(20,8,163,0,4)]) (.leaf [(0,32,30,129,6),(32,0,2207,0,8),(1,32,30,128,5)])) (.fork 2 (.leaf [(35,0,156,0,4),(40,0,2199,0,5)]) (.leaf [(0,128,2075,36,6),(128,0,2111,0,8),(130,0,2109,0,5)]))) (.fork 5 (.fork 2 (.leaf [(4,128,2075,32,5),(134,0,2105,0,4)]) (.leaf [(136,0,2103,0,5),(128,32,30,1,5),(160,0,2079,0,7)])) (.fork 2 (.leaf [(129,32,30,0,4),(162,0,2077,0,4)]) (.leaf [(36,128,2075,0,4),(164,0,2075,0,4),(168,0,2071,0,4)])))))

def orForest : Forest := ⟨2239,10,fun j => orSamples[j]?.getD (0,0),orCols,orSymmetries,liveLevels,liveIndex⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem orGeometry : graphValid orForest (boundsBefore entries127) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked10At0 : block orForest 10 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked9At0 : block orForest 9 0 18 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked9At18 : block orForest 9 18 28 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked8At0 : block orForest 8 0 2 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked8At2 : block orForest 8 2 56 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked8At58 : block orForest 8 58 56 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked8At114 : block orForest 8 114 40 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked8At154 : block orForest 8 154 56 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked8At210 : block orForest 8 210 56 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked8At266 : block orForest 8 266 16 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked7At0 : block orForest 7 0 27 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked7At27 : block orForest 7 27 33 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

theorem allAt10 : block orForest 10 0 1 = true := checked10At0
theorem allAt9 : block orForest 9 0 46 = true := (@block_merge orForest 9 0 18 28 checked9At0 checked9At18)
theorem allAt8 : block orForest 8 0 282 = true := (@block_merge orForest 8 0 114 168 (@block_merge orForest 8 0 2 112 checked8At0 (@block_merge orForest 8 2 56 56 checked8At2 checked8At58)) (@block_merge orForest 8 114 96 72 (@block_merge orForest 8 114 40 56 checked8At114 checked8At154) (@block_merge orForest 8 210 56 16 checked8At210 checked8At266)))
theorem allAt7 : block orForest 7 0 60 = true := (@block_merge orForest 7 0 27 33 checked7At0 checked7At27)
theorem orTables : checkedTables orForest 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block orForest 0 0 0 = true)
  · exact (rfl : block orForest 1 0 0 = true)
  · exact (rfl : block orForest 2 0 0 = true)
  · exact (rfl : block orForest 3 0 0 = true)
  · exact (rfl : block orForest 4 0 0 = true)
  · exact (rfl : block orForest 5 0 0 = true)
  · exact (rfl : block orForest 6 0 0 = true)
  · exact allAt7
  · exact allAt8
  · exact allAt9
  · exact allAt10

theorem noRun : Impossible (graphGoal 2239) 10 (vars 2239).toFinset :=
  root_index (g:=orForest) (before_sound _ sound127) orGeometry orTables
    (k:=10) (by decide) (i:=0) (by decide +kernel)

end Free191

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound191 : Lower (vars 2239) (graphGoal 2239) 11 :=
  augmentedGraph (k:=10) (m:=191) (hints:=536879364) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 191) (by decide +kernel) (by decide +kernel) Free191.noRun

def entries191 := extendKnown entries127 11 [(2239,[]),(2427,[130,114,98,81])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound191 : Known entries191 := extendKnown_ok sound127 seededBound191 (by decide +kernel)
namespace Free223

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem noRun : Impossible (graphGoal 2271) 8 (vars 2271).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2271) (64,0,2207,0,8) _ (before_sound _ sound191) (by decide +kernel))
    [] (pool:=(vars (poolMask 2271 (64,0,2207,0,8)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Free223

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound223 : Lower (vars 2271) (graphGoal 2271) 9 :=
  augmentedGraph (k:=8) (m:=223) (hints:=553656580) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 223) (by decide +kernel) (by decide +kernel) Free223.noRun

def entries223 := extendKnown entries191 9 [(2271,[]),(2429,[130,114,49,98,81,64]),(2463,[134,49,64]),(2553,[118,130,81])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound223 : Known entries223 := extendKnown_ok sound191 seededBound223 (by decide +kernel)
namespace Free247

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem noRun : Impossible (graphGoal 2295) 8 (vars 2295).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2295) (16,0,231,0,8) _ (before_sound _ sound223) (by decide +kernel))
    [] (pool:=(vars (poolMask 2295 (16,0,231,0,8)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Free247

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound247 : Lower (vars 2295) (graphGoal 2295) 9 :=
  augmentedGraph (k:=8) (m:=247) (hints:=553648388) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 247) (by decide +kernel) (by decide +kernel) Free247.noRun

def entries247 := extendKnown entries223 9 [(2295,[]),(2423,[135,98]),(2547,[118,130,50,81])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound247 : Known entries247 := extendKnown_ok sound223 seededBound247 (by decide +kernel)
namespace Free251

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem noRun : Impossible (graphGoal 2299) 7 (vars 2299).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2299) (8,0,2291,0,7) _ (before_sound _ sound247) (by decide +kernel))
    [] (pool:=(vars (poolMask 2299 (8,0,2291,0,7)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Free251

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound251 : Lower (vars 2299) (graphGoal 2299) 8 :=
  augmentedGraph (k:=7) (m:=251) (hints:=1358970884) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 251) (by decide +kernel) (by decide +kernel) Free251.noRun

def entries251 := extendKnown entries247 8 [(2299,[])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound251 : Known entries251 := extendKnown_ok sound247 seededBound251 (by decide +kernel)
namespace Free319

def liveData10 (i : Nat) : Nat := 0x7040bfd40

def moveIndex10 (i : Nat) : Nat := 0xd1c00064487d11659cf212d4546c002d7912742aa6136145604051831841411e9dfaa83d10bd900000a8a447889e5ec82a0000170c21033330058590dc398180059f58b1692319100185627b1a08700046200d9d61

def liveData9 (i : Nat) : Nat := 0x9c881ce00440c92722042e16013910500199c8820b8005ce44145c02227030a173810316000b1c08285804e041034002e7020b381021500171c0828900018e0414000e70208060019381051119041d090034e44088474302400a17381039c0810801ce4400140802722080539100049c881000e44108c86180a7220617381039c08101ce040c000e702093810200087067220405380110494f20a36c40836fb9e0ba46eed4992b105c6ad948a6445e868f69d0376638b494425e3e86e8c01562383485408e0e812800ffceea07fe44503feb9a81ff1cd40ffa86a07fc43503ff19a81ff5c940ffac4a07fd42503fe99281ff5c540ffac2a07fd51503fea0a81ff4c540ff880a07fd30503fe18281ff48140ffa20a07fe00502ff3ba81ef91140bfae6a05fc73503ef19a817f5c940fdc44a05fd71503dea0a81fd84540f7880a07f840503fc98281fe80140

def moveIndex9 (i : Nat) : Nat := (if i < 1 then 0xbe1ae21e4c112315e48bc2641938068848dc140981e15c5172e36a415f90dc609eca642a2a9c216f25ae81f3086b59345284635a746022429404de8715404456e46a502d54e725844439967d91fa5c782640fbb2bf6011c09eb6e35980ae7d7524c040db8bdcc15705a7233810449ffd0606590c6305ab0af92a34cba48282a6a25b401d4581063a1fee0c18b82891256f11240725862019388e007f089784824497146c85df67f499bc51890c4211693ee5de0940000c32000030180000e38800008beeab422032791319119ec4ec0006910415260cdc000a2c89cd4a920a218ee967c058ad2b223dc14883438b4306f1c7f024c8a76940e254ea8b8108aa8619b650b00458dc852f43d9934491a509702f6b8e80002087a941807821b61cea0d9d28a2acd264a2fd4b6c8260001a00800072ae41f200034550000f1cc09008085a29a1d92c350220000f141e4dd4b298b2f5e545b249191020000296b8440000a157456101c0000509a000186fd12ef22403d0c2f800000006330000189f00014a9487818d3000000019af8136803563f43ad5649a693e00588b68733230000cdb3629ef18982e9802fa9340f4eac6d713122607200028a1d2374de10444d7cf2a921daca8207982c8308f2419c29633b762062380a9a11f00786bbd850d03fe1cacb19860dae7e94c21ac804fadc820f4402c072a60f1d50871c411a4c30532226d7f43502411abec0007a6135db037a23a8000edcd4d2f4b5186c40b7a2d21a8916e0000000003a38ce0000e08f102421a987e0002d1f08d6e2720000000589ed0f60003d7f8000e01b090c00000000000ca68000394730ab80eb88e10a6a0adda9999b613a5090cd2a470c1411504c32985c615641d1055e45db12c963963c61178077c1ba2065870422ed24dc15e52bd824d1f9a3d416cf84f018f011982778b6d2bc00714538858163d80c987d4a9f518a02b9c3760dba0ce0214ca7c14be50e0d2095d60157186c8db11cc104d2dec0df424cacf70c3445249eda5c1062e42400060eb45f5416408f24f000018c080005320f6ceac52451195a710800000000000d1aae12952ceace000069e4c7bf898b05ea0a1d4c80350001c38c000294d213b22a1c1050f2921501dac3e5205621eabd017e9a7aa270e97919cc16912c84077524c80ac04a0002890b149f0e433794aa8896c0fd2935162f934d3f850840014374634187a06c00404a400a004c888000423f0460882029402b309cc80108c0070c2412d001240704107816228b8534204064200305574801d0a0038248781160428409021d2b000a993a082801a000528a0040f84400000a62040000a240011400904320cea52e180090a140000275d0f001410a000080a1e48e8010381840208600227c2980a001800418405020df8712041811c000010c5c080 else 0x892e6ac8016189a65e0c540889993315d260f4847d2e6b1f0eb6b058d95908166d6a09f784061b0cd7ad758000c28c61145b680000000245f89880000001e0bb0b1d8d9e5ece3458b35095e03f25170a9710bf2402b6c82e511bd084c1a600a714c2077b474c9e5012ea9c0000c818128a47f6574916b8e9b036418040b9697e601a1e1d0eb881b25e000140340ad5636e22c828891d42610a5b1226929f5e362b318ed935d556081b82f488c8179e32dc0f592b00012a22d726323552aa1d644e308d40cd6302c1a52b80124614e4482321c04ec49f83866f214ba481f96539480000000000018c20624cc9589270ef9596c1ff832108a31a408ab859e06a1433e05a841c960f21d2454c063101a2a9e1f6432c00)

def liveData8 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0x9424c140ff9324c140ff9814c140ff9714c140ff9614c140ff9514c140ff9414c140ff9314c140bfe884c140bfc874c140dfc874c140dfe774c140bfd844c140bfc844c140fbc844c140dfd734c140dfc734c140fdd434c140dfd724c140dfd714c140fbd414c140fdd314c140ff8404c140dfe770c140bfd840c140dfd730c140bfd820c140bfd810c140ff9300c140bfe8848140dfe7748140bfd8648140dfd7648140dfd7548140bfc8448140fbd5448140bfd8348140bfc8348140dfd7348140fed6248140fed5248140fed4248140ff93048140bfe8844140dfe7744140bfd8644140dfd7644140bfd8544140dfd7544140bfc8444140fbd5444140bfd8344140bfc8344140dfd7344140dfc7344140ff55144140ff54144140ff93044140dfe7780140bfc8480140bfc8380140dfd7380140dfc7380140dfd7280140ff93080140dbd849dd409fd839dd409fc839dd409fd829dd409fd819dd409fd809dd40df9809dd40dbc8791140dbe7791140bbd8191140fb98091140bf980911409fe885cd40dbe445cd409fe881cd409fc841cd40dbe441cd409fd821cd409fd811cd40df9801cd40ddd731cd409fc8750d40bf88050d40bed8210d40bf58110d40ddd878cd40ddc878cd40dde778cd40f9e448cd40fd8808cd409fd878cd409fc878cd40ddc738cd40bf8808cd409fe885c940dbe445c9409fc835c940dde335c9409fd87589409fc8758940bf880509409fc874c940dee7788940ded7688940eee6688940fae4488940dec7388940fce33889409fe885c540cfe665c540dbe445c5409fc835c540dde335c5409fd87585409fc87585409fd87545409fc8754540bbe8850540dbe7750540dbd7650540ebe6650540bbd8550540dbc7350540f9e3350540fb88050540bf880505409fd874c5409fc874c540fb5414c540df67784540df57684540ef66684540df57584540f765584540fb55484540fb64484540df57384540df47384540fd63384540dbe7710140dbc7310140f9e3310140dbd7210140fae2210140bbd8110140fb61110140bfa8810140dfa7710140fba4410140bf98310140fd98310140fda3310140fe98210140fea2210140ff18110140ff21110140bdd8310140bed8210140bf58110140bfa884c140bf8874c140df8874c140dfa774c140bf8844c140fb8844c140fba444c140df8734c140fd8734c140fd9434c140fda334c140df9724c140fea224c140fb9414c140fd9314c140ff2114c1409fd874c1409fc874c140bbc844c140ddc734c140fd9300c140bbc8448140bbc8444140fb54144140df88780140dfa7780140bf88480140fba4480140bf98380140df97380140df87380140fda3380140df97280140fea2280140df97180140fb94180140ff211801409fc8780140bb58110140bd983101409f8874c140 else 0x1bc8be45ca21d10485941820410167fd3fc1fa8f8277d3b79cf4e287063731b60d7069834999a8cb864e3249910c6c63130417e8bd85cc2df1678afc5672a394e4a5650b27e937499e4c125e12dc92e46e227110086442d20f90688184071fc8fac7cc3e11ee0f5c7a43cd1e40f0c77c3b91da0ebc7543a51d00e6c72c3911af8cd86082f61620a48508276138898c4bc25912a091847022a10988143ee1c50c0853c2941450a004c823610d07f83c41d80de068030817a0af055027011c08902b8124076000dfd849dd40dfd839dd40dfc839dd40dfd829dd40dfd819dd40dfd809dd40dfd409dd40fbd849dd40bfd839dd40bfc839dd40bfd829dd40bfd819dd40ff9809dd40fbe8891140dfc8791140dfe7791140bfd8391140bfc8391140bfd8291140bfd8191140bfd8091140dfe885cd40dfe445cd40dfd815cd40bfe885cd40dfe775cd40dfd801cd40dfd401cd40bfe881cd40dfe771cd40bfc841cd40dfd731cd40bfd821cd40bfd811cd40ff9801cd40dfe7750d40bfe8810d40dfe7710d40bfd8210d40fed8210d40bfd8110d40ff58110d40ff98010d40fde888cd40bfd878cd40bfc878cd40dfc878cd40dfe778cd40bfd848cd40bfc848cd40bfd828cd40bfd818cd40bfd808cd40ff8808cd40dfe445c940bfe885c940dfe775c940dfd765c940bfc835c940dfd735c940bfe8858940bfd8758940bfc8758940dfe7758940bfc8458940bfc8358940bfe8850940dfe7750940bfd8650940dfd7650940bfc8350940bfe884c940bfd874c940bfc874c940dfe774c940bfd864c940dfd764c940bfc844c940fed624c940fed424c940dfd645c540dfe445c540dfc835c540dfd635c540dfd435c540dfc435c540dfe335c540bfe885c540dfe775c540dfd765c540dfd755c540bfc835c540dfd735c540dfc735c540bfe8858540bfd8758540bfc8758540dfe7758540bfc8458540bfc8358540dfd7358540bfe8854540bfd8754540bfc8754540dfe7754540bfc8454540bfc8354540dfd7354540dfc7354540fbe7750540fbd7650540fbd7550540fbc8350540fbd7350540fbc7350540fbd6350540fbe3350540bfe8850540dfe7750540bfd8650540dfd7650540bfd8550540dfd7550540fbd6450540fbd5450540fbe4450540bfc8350540dfd7350540dfc7350540fbd4350540fbc4350540bfe884c540bfd874c540bfc874c540dfe774c540bfd864c540dfd764c540bfd854c540dfd754c540bfd844c540bfc844c540fbd544c540ff5614c540ff5514c540ff5414c540dfe7710140bfd8310140dfd7310140fbc4310140bfd8210140dfd7210140fbd4210140bfd8110140ffa884c140ff8874c140ffa774c140ff8844c140ffa444c140ff9734c140ff8734c140ff8434c140ffa334c140ff9824c140ff9724c140ff9624c140ff) else (if i < 3 then 0x2c041c18042420603c023810380634e408502080c18281041803140820c01c0860307080401100c0024e408403000a0418125049c8108060e1408302080c1c201c0840c0188180310202006420023018204174e42018401850103008321030180010304200620a043803040c1010064200800c40544080a0a100020401881600100320010642000c8800b082c20005881688102d10205841610585101005c20070418881064200064200004000c8400105a204030a0806201a084190800044040682102c20504880b08101438021a7210284040014e420405010a10184042808107020004081708100c082010044030e093902100c3020800203082006281060410083041c018800181040005843218002c40a0800200084c1e0611024a210c83062006083819048c241910382000c082020839042110081c307814021a0ca20c8208643c0c18304420c841a0c10301220c8841830008200b01864a006860420c2060420c0490169c410c1020800010e008420c205c1e000c82c3e09382c2170800c000b284c1e0906121010c8304238404051c060c40000b0c013078001a48405381000161004c1e04049004101044219060c0410e0204230f8002c30c01c41f00048602080820c4e42070208003a0918303020800080e01c613078001840602012381053810070204e0410208302000000000000000000000006422040e824a110e83012402044321d04950410c2081a210615040d0b88818541041c1020820001041060510101a204880a08217058043612283c020d0ba20440c384044030ce20a0000001000244000c0820e0800018104161022020010504100640a0207088a000838219068384222061b3c19dbceb67233759b5ccf6643305974caee51b271921c89e43b2018f2c6de2ef16d8a8c51e25710f879c35e19b0b1841c1e60df053812c06dfdafad7c8bd8deb2f2b790bc5ddd2ebb74fba55cf2e4b720b84dbcada56c4b56da7ecff668b2d5932c6b61eb0cd80abfb5ddae7d6e2b4358aabe5596aaf552a9dd4b6a1b508a7d53d69cf4d9a6a52f694d498a4551ce8b944ea2050ca84941fa044fea7eb3de9eccf0a7573949c7ce066d53659a2ccba61d2ee96bcb265652a4946c9fe4bf248918c86a4071ec8ef471e3611998c5c5f62cd14f89c448622710e877435e15d08e837413a0930328124011fecff17f1bf79f8efb07ccbe2dee8f5d7ac3d05e66f1c78bbc25df6ee4766bad9d50e9a74639f9cf2e6b7333961c82e3371738a5c36e16704380dbfcdf06f1372db7ada66c7b605af8d776b93591a9ad3f69434459e2cda66632f994ec9064131d18bac4f61c3085814bf35ee2f1576eba95cdae356ecb685ad2d0d658b1e5882c2d60caf85752b4d58aab7554a9dd4aea4051028253f69ed4efa74537499a4afa54526291a48623d5 else 0x440504100001c241043210584100510080624104000e1038200704161048084040400c600c84088086420b0864200005000b100088080d04200003220007010340040a88100180310000b00083802100020058416001000a00100c0020587004305841308102420902c2069c840a10184042c05107004200142c20020280b182420504880a00127210284041a0510082002834405085c1a9c180281025020408002181004322008418102038402008938181060418104015018838100042a2002c2820b854412018800008042420))

def moveIndex8 (i : Nat) : Nat := 0x235fc66411d0b4309c89a32c6c51d11800044fc4b320d148ad47a9d34249804115400001a74ca3530000502988f0239995b08603de4bbc82d03f8b7b343cd5827cc99569f0dca36158ca2a440982154b5959f4aa661cc5d0003c63b572c3e28218c0813e00c05fb56300009a2e35bc102038d6292864cc6a3486055f780b1064000b1ff5d094434bce0cc9510000c84e2930df35a39c0ed80000f0de47c965a4de81ad98f8083193c1150c72037c79f516364624784170c34c976484ba100f5cd0003449e66483c164488de602c14b29cd021402e60134f49d4075059015e865449a42663151a53045c5a612b481b1b1c31863b59b233a82900024ae22f5018c090c36728002dd2c96405375c3ba218c581364ce075430b9059085600039b5927285ee07349000d445461308c890ab493d9930bff1d582b6348c5c32bc10f0003543818911d604e00139ed01a006c096000182f0002443000389e47800004604178b2ed83af306412e2db4da000000045800002310068b1c800004c90cdb10a094b20292a808c86ee1d155e8137527a28916976e24cbc1008aba0e60e20000d0a919c0be56340166225487338c000a41144bb43443f936c000b1209d142b40c3e25dd1c820c0000003294b0978524001d11e4fac1e333cc95323355f51c549b05b5ca630545740001c2295fc19081df06d81f486fe2a104e8017c28f534000738517082b0038630b4640002ca57469478614ec98a05c044d68c941b524000346c9050002c767346850c6534b0c02242c01cd47a422ec02f0bb8c6e2e38703184c5b045e007d1aa1e1e1ed806f17cca3107e87e5350000000188896d91cc85e70321d9352070b0500280c022e33001f2b030074010500000012000b0b0107090014040103002a070c0208090603020705460806046705080104050100030d080504020007031a01060a3c030505000110045c0406110b010000080001011c000000030210000409030b0003

def liveData7 (i : Nat) : Nat := (if i < 1 then 0xa884c5408fe4bb0c98a811fc97615315033790eaa262a057d25d614c540afa4baa298a81db576505315027e930a0a62a047f6627710140cef3bb06202817ad9210c405033dceec1080a067b5cd8210140c7ec32e4202819dd835c84050373b06a1080a067d9dd8110140cfabb30220281bb564604405033eae6c0880a06ed10d8110140cfab930220281bb54260440502f732944260a067ea64874c140cfcc890e982819fa8821d305033f10f3ba60a05f664e774c140edc4390898281f999321130503f532442260a05ee644844c140fd8c8908982817e99221130502fe32242260a05f624e444c140cfc43ae698281f988450d30502fd32421a60a05fc644434c140afc4bb04982817b89460930502bf130b9260a076e211724c1409fc4c2e4982817d89358930502bf12ec0a60a067e21d814c140bdc4a302982813f8985c5305033f10eb8a60a057e25d514c140cfc43aa2982817b898505305037710ea0a60a076e21d414c140edcbb282982817b99550530503f6302a0a60a07e650d414c140eec43a6298281dd9764c530502fb32a98a60a05f6651314c140fcc4226298281f99544c530503fa2c298a60a07f4545314c140fe8a0a6298281fb1414c53050277b2944260a047fa65874c1408ff4c90e982813bc9421d30502b792843a60a057764e774c140cdf3b90898281b9d932113050375b2442260a06ed644844c140ddcc810898281bb930211305027db2442260a04fd644844c1409fcc8108982819bc8721130502f6b2242260a066f211734c140afcc80e6982811fc985c93050337908b9260a047f261714c140cde422e2982813bc98505305033790ea0a60a05f664c404c140bf4c9080982817f191101305023fb313b860a04fd64688481408fe4bb0c902811fc9760d2050277928c1a40a047f25d86441408fe4bb0a882811fc9760d1050277928c1a20a076d5d94144140eda39a82882815f8974c110503f628298220a047f65c83801409deca107002813f59120e005027f32041c00a047f2617280140afc4ba61002811f59120e7750237b29442e6a046f262445cd408f6c910839a811f591210735023f320420e6a047d646885c9408ee49b0eb128179993201415027b32640282a046f66277101409db4cb02202819b6776044050336aecc0880a06ad9998110140cda39b0220281b96336044050336ae4c0880a06e98898110140d9ac2c22202811f897a20405023f3313b880a04f6a658310140ced3bb0620281b9a4460c4050379306c1080a06f260e2210140de8c1b0220281be182604405037a30708880a047ea64874c140cdc43908982817b191211305033710f22260a067621d434c140cec43c66982811f8985c9305033d10f11260a066e21d414c140fc8a0a62982819f087845305023792843a60a04ed644844c140 else (if i < 2 then 0x2058400000205840c0818100000030206040608000000030484064102000000000a081410002007820004001820202820004080040e0820008000c8419081c01881908161064205840002c205840b0816106420c840b0816103020701a20642058400004007040c081c1030200020018c880800c081810000308061000610018440802080008006200041002001880018400c84000000006420c8409a2040704007020018c0e0832102c20c8400000a1000001840308000104000082002c2040600080000840e10021038400680c10000000000000000000000000000058422038401840e0800b083206042302c2070182208091018103820c812295b95695194c94793892992491f91090b8fc8ed8de8cf8ca8bb8b68b18ac8a78a289d89889388e88988487f87a87587086b85c84d84883982a82582081b81681180c8078027fd7f87f37ee7e97e47d57c67c17bc7ad79e78f78077b77677176c75d74e73f73a73573072b72670d6f46ef6ea6e56e06db6d66c76b86a96a469568668166865964a64563662762261360e6095fa5eb5d25c35b45a559659158c57d56e55f5505415325235145054ec4dd4ce4c94ba4b54a649748847945644744243342441f41a40b3fc3f73e83e33ca3bb3b63b139839338437f36636135234d33e33933432f32a3253203113022e92da2d52b22a329428527627126c26725825324e24923a22b22622121220d2081f91f41e51d61c71c21bd1b819f19a18117c16315e15915414f14a14514013b13613112c12712211d11811310e1091040ff0fa0f50e60cd0be0af0aa09b0780690500370280190008fec81073ba819dd8320e77502beb2241ceea04fd644839dd40ddcc23013ba811fc9760e445027f32041c88a047f652885cd40cdeca510b9a815bd94a21735023f931222e6a057764e775cd408fec810839a815dd939dd435023f92f44086a047f6627710d40cf73bb0421a81aed86608435033eceec0886a06bd6198110d40dbac2b0221a81be582604435037d304c0086a06fc6058010d40cef4410f19a811fe9921e335023f92ec1466a047f25d818cd408fe4bb0119a811fd90a21725027eb23442e4a04f724d87589408fec990eb12811fd9720d6250277b2841ac4a04fd64483589409fcc8106b12813f990a21425027b926c3284a04bf65883509409beca906a12813f59120d425023f92ec3264a04fb261424c9408fec9d10b8a814fd9610d71502afb2a21ae2a057b648435c5408fe4c466b8a811fd9321d615023fb2e41ac2a04df65483585409deca106b0a813f99020d615023fb2643aa2a047f65c83545409deca106a8a813f99020d51502e7b2a41a82a05ee6408350540adecb0e6a0a819bd851cd41502b792eb1a82a04df6548350540b5ecb086a0a8173d9510d41502f5b2421a82a04fb64 else 0x1c100820000410004103820104000818008000000000000000000001610002002c2010400000000000000000))

def moveIndex7 (i : Nat) : Nat := 0x40264e05fe1e34225d70cc0db1d81351ab62110940a1f54580310e716543c00a49805000011508c48409919b0af06d1455500000081c01bb21644d5b000b18000c22c1230fe1730b000120e1500020700004f904f01ad9a58c5e6593992810490f40c12c000c018280040081

def liveData6 (i : Nat) : Nat := 0xc840064206420642064200321032100007040704100020380688000c20000c0800000000642000014fa55166b309044200f075b6d96c660ac5429c461c4d85c2b948843d1c0cc5c29120501e0a02802ab5a610d8110140ae968843604405029b9a4a20874c140de264d92211305035b087644844c140dac659912113050373195644844c140de464d91211305037a192644844c140be46848450d30502d39a5211724c140b6c684845c930502799a424d624c1409f46849358930502739a5261414c140e6c68487505305023b8a8655414c140c6e21d95505305039b087605414c140bc6694844c530502dd0a7545314c140be42a1414c530503d9087505314c140f645d9414c5305021bda4a65874c140ce364d92211305032b596644844c140ccd65591211305033a592644844c140cec64590211305033b1914c0844c140c6d21d912113050293da5211724c140d6c25d414c1105031b087644844c140

def moveIndex6 (i : Nat) : Nat := 0x25d

def liveData5 (i : Nat) : Nat := 0xa20dc5b950caa82982813c46d4a8505314c140

def liveLevels : Nat → Packing
  | 10 => (1,1,6,0,0,0,0,liveData10)
  | 9 => (36,2,6,0,0,11,0,liveData9)
  | 8 => (370,3,6,0,0,13,0,liveData8)
  | 7 => (228,4,6,0,0,12,0,liveData7)
  | 6 => (35,5,6,0,0,9,0,liveData6)
  | 5 => (2,6,6,0,0,3,0,liveData5)
  | _ => emptyPacking

def liveIndex : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 16 56 4 11 6 1 moveIndex10
  | 9 => lookupWord 184 608 7 15 9 2 moveIndex9
  | 8 => lookupWord 106 349 8 14 8 2 moveIndex8
  | 7 => lookupWord 20 62 6 12 6 2 moveIndex7
  | 6 => lookupWord 1 3 0 5 1 0 moveIndex6
  | _ => fun _ => none

def orSamples : Array (Bits × Bits) := #[(0x1fffffffffffff8003981c373f41fc183,0x1fffffffffffff80411b04010144ec8a3),(0x1fffffffffffff990c607fe0c080001ff,0x1994e43b608ca000150),(0x660f0060c8f0000fe7c,0x666b02409870004622c),(0x7f830f00fe0ff80,0x1fffffffffffff801029810386f689d81),(0x780f8003f000fff0000,0x78ae8412f4280902044),(0x7ff00003ffff0000000,0x2a300003fefe3003008),(0x0,0x0),(0x0,0x0),(0x7ffffffc00000000000,0x55cfd67c00000000072)]

def orSymmetries : Array (List Nat) := #[[],[81,130],[48,33,133],[48,129,82]]

def orCols : IndexTree ColumnInfo := (.fork 17 (.fork 8 (.fork 4 (.leaf [(1,0,318,0,7),(0,2,312,5,6),(2,0,2365,0,8),(1,2,312,4,5)]) (.leaf [(3,0,316,0,5),(0,4,2353,10,6),(2,4,2353,8,5),(4,2,312,1,5)])) (.fork 4 (.leaf [(6,0,2361,0,7),(5,2,312,0,4),(7,0,312,0,4),(8,4,2353,2,5)]) (.fork 2 (.leaf [(10,4,2353,0,4),(14,0,2353,0,4)]) (.leaf [(18,0,301,0,5),(0,32,30,257,6),(1,32,30,256,5)])))) (.fork 9 (.fork 4 (.leaf [(33,0,286,0,5),(38,0,2329,0,4),(0,256,2071,40,6),(256,0,2111,0,8)]) (.fork 2 (.leaf [(258,0,2109,0,5),(262,0,2105,0,4)]) (.leaf [(8,256,2071,32,5),(264,0,2103,0,5),(280,0,39,0,4)]))) (.fork 4 (.leaf [(32,256,2071,8,5),(256,32,30,1,5),(288,0,2079,0,7),(257,32,30,0,4)]) (.fork 2 (.leaf [(289,0,30,0,4),(290,0,2077,0,4)]) (.leaf [(292,0,2075,0,4),(40,256,2071,0,4),(304,0,15,0,4)])))))

def orForest : Forest := ⟨2367,10,fun j => orSamples[j]?.getD (0,0),orCols,orSymmetries,liveLevels,liveIndex⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem orGeometry : graphValid orForest (boundsBefore entries251) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked10At0 : block orForest 10 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked9At0 : block orForest 9 0 14 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked9At14 : block orForest 9 14 22 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked8At0 : block orForest 8 0 3 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked8At3 : block orForest 8 3 56 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked8At59 : block orForest 8 59 56 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked8At115 : block orForest 8 115 25 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked8At140 : block orForest 8 140 56 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked8At196 : block orForest 8 196 56 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked8At252 : block orForest 8 252 56 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked8At308 : block orForest 8 308 56 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked8At364 : block orForest 8 364 6 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked7At0 : block orForest 7 0 43 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked7At43 : block orForest 7 43 56 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked7At99 : block orForest 7 99 56 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked7At155 : block orForest 7 155 56 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked7At211 : block orForest 7 211 17 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked6At0 : block orForest 6 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked6At1 : block orForest 6 1 34 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked5At0 : block orForest 5 0 2 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

theorem allAt10 : block orForest 10 0 1 = true := checked10At0
theorem allAt9 : block orForest 9 0 36 = true := (@block_merge orForest 9 0 14 22 checked9At0 checked9At14)
theorem allAt8 : block orForest 8 0 370 = true := (@block_merge orForest 8 0 140 230 (@block_merge orForest 8 0 59 81 (@block_merge orForest 8 0 3 56 checked8At0 checked8At3) (@block_merge orForest 8 59 56 25 checked8At59 checked8At115)) (@block_merge orForest 8 140 112 118 (@block_merge orForest 8 140 56 56 checked8At140 checked8At196) (@block_merge orForest 8 252 56 62 checked8At252 (@block_merge orForest 8 308 56 6 checked8At308 checked8At364))))
theorem allAt7 : block orForest 7 0 228 = true := (@block_merge orForest 7 0 99 129 (@block_merge orForest 7 0 43 56 checked7At0 checked7At43) (@block_merge orForest 7 99 56 73 checked7At99 (@block_merge orForest 7 155 56 17 checked7At155 checked7At211)))
theorem allAt6 : block orForest 6 0 35 = true := (@block_merge orForest 6 0 1 34 checked6At0 checked6At1)
theorem allAt5 : block orForest 5 0 2 = true := checked5At0
theorem orTables : checkedTables orForest 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block orForest 0 0 0 = true)
  · exact (rfl : block orForest 1 0 0 = true)
  · exact (rfl : block orForest 2 0 0 = true)
  · exact (rfl : block orForest 3 0 0 = true)
  · exact (rfl : block orForest 4 0 0 = true)
  · exact allAt5
  · exact allAt6
  · exact allAt7
  · exact allAt8
  · exact allAt9
  · exact allAt10

theorem noRun : Impossible (graphGoal 2367) 10 (vars 2367).toFinset :=
  root_index (g:=orForest) (before_sound _ sound251) orGeometry orTables
    (k:=10) (by decide) (i:=0) (by decide +kernel)

end Free319

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound319 : Lower (vars 2367) (graphGoal 2367) 11 :=
  augmentedGraph (k:=10) (m:=319) (hints:=12884910340) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 319) (by decide +kernel) (by decide +kernel) Free319.noRun

def entries319 := extendKnown entries251 11 [(2367,[])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound319 : Known entries319 := extendKnown_ok sound251 seededBound319 (by decide +kernel)
namespace Free351

def liveData10 (i : Nat) : Nat := 0x1a830ffd40

def moveIndex10 (i : Nat) : Nat := 0xac00c44421c6a000500152f24628247bc4bbc24286dc7c44a3dbd958004200236a601000008c0

def liveData9 (i : Nat) : Nat := 0xd14041948c620281948c51a281948c5280e30e30710a065231008a0652307301150c307286291840450305503181c6101861aa0b2818c2150c1540c5da632c94a9bc59ceb8529d8c63b14003fea9281ff58540ffaa2a07fd31503fe18a81ff48540ffc22a05fd75503bf2aa817f5c940fdc44a05fd71503fb08a81fe4c140

def moveIndex9 (i : Nat) : Nat := 0x4c8a224f4d3830de1548ea80001e30c624e0c32b249304cc00010f81a90143ad17e89075cde60fef4cba09326bebc003437499c140000000a40000000000024fa545b31e52822c70096506cad29363c636ec6264089537344c010d140c6f946850b52452c0018fc0008ec07a24cc05e06cd611f4b0cbe408003b08ed37358862b8e102b205ec6fceaa266c3ae105709e42d81d044e8400185044c64a6fd0b7c127390f14aad4b0a1459e7a91bf2193ec3e92bd234429426e7c814c28c4864000001e54ce52a507e04882742b4db66d51000d969c4c415e00530d01700a10e0050450011012000001302820421050432c2

def liveData8 (i : Nat) : Nat := 0xf061000b08383c42a0c2020c941ca010a8c500852810f061010608083c40614608003090c21a221230e83010a022e3042824087068c21112103010818084080c2008030a0c081041a0c2020f10003080810428183081844822ea8143120a10043081420ca8243860a185430e18214260e31205060b20483880c20c2e16301150a183040100e20608304145c2060c1140317183010b8c58284062c00308021030108502840c10030400c10018400c10608386182140e2860c3041c30c102060b1c3038a18384afede8ba76daccd84aef58aa6d38a5747a84cfc9bf2ca52c888e717a24c3483f069febe87a6ef9d4b9470ede9b6b60686cb98cb0c5deb8962ab85369d930a5446e86906a083e6798ec9bc35e648ba9602864b88c9041ee3c8728e01a6338608bc15e2884a8880e61982c84c07e08806800bfe8854940dfd625c540dfd525c540bfe8858540dfd7358540dfd7258540efd6258540dfd7158540bfe8854540dfd7354540dfd7254540f7d5254540dfd7154540bfe884c540dfd874c540bfd854c540dfd754c540fec824c540dfd724c540dfd714c540ff5614c540bfd850c540bfd820c540bfe8848540dfd8748540bfd8648540dfd7648540bfd8548540dfd7548540bfd8348540dfd7348540fed5248540dfd7148540ff53148540ff9634c140ff9534c140ff9624c140ff9524c140ff9324c140ff9614c140ff9514c140ff9314c140ff9214c1409fe885d5409fc835d5409fe885c940d7e555c9409fc835c9409fd8754940ded7588940f6e55889409fe885c540cfe665c540d7e555c5409fc835c540dee225c5409fd8758540cfd76585409fd87545409fd874c5409fd870c540bf9800c5409fd8748540df57684540ef66684540df57584540f765584540df57384540fd63384540df57284540fe62284540df57184540bfa884c140df9764c140efa664c140df9754c140f7a554c140fda334c140df9724c140fea224c140fb9414c140fd9314c140ff2114c140

def moveIndex8 (i : Nat) : Nat := 0x84000c1b9fe488e42f8374b98a7000810012342045e1bc2680a50000000018049a80

def liveData7 (i : Nat) : Nat := 0xc2000000010400a08004101040410301c4070d0ce4744c23fbd3ab3b12a27a09992870047f64a885d5408fec8906baa811fd9120d725026fb2b442c2a04fb64a884c5408fe4c2ea98a819ed8720931503f912498a60a07f4585314c140fe898a429828117d9520d725023f321442e2a047e261764c1408fc4c2ea982811f8985c93050277130a0a60a07e4505314c140

def moveIndex7 (i : Nat) : Nat := 0xf

def liveData6 (i : Nat) : Nat := 0x3f8092505314c140

def liveLevels : Nat → Packing
  | 10 => (1,1,5,0,0,0,0,liveData10)
  | 9 => (14,2,5,0,0,9,0,liveData9)
  | 8 => (83,3,5,0,0,11,0,liveData8)
  | 7 => (17,4,5,0,0,8,0,liveData7)
  | 6 => (1,5,5,0,0,0,0,liveData6)
  | _ => emptyPacking

def liveIndex : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 10 29 5 9 4 1 moveIndex10
  | 9 => lookupWord 43 139 6 12 7 1 moveIndex9
  | 8 => lookupWord 11 25 3 10 5 1 moveIndex8
  | 7 => lookupWord 1 2 0 4 0 0 moveIndex7
  | _ => fun _ => none

def orSamples : Array (Bits × Bits) := #[(0x1ffffffffffffffffe8066023801e80cf,0x80468218022e24c),(0x1ffffffffffffffffe01b80cc3f8100ff,0x1ffffffffffffffffe08b924413850893),(0x1e1c00c1c811ff30,0x1f34088088107328),(0x1ff31f1e1ffc0,0x1ffffffffffffffffe000a33176a58cc1),(0x101e003e01fe0000,0x111a100e09581022),(0x0,0x0),(0x1fe0003ffe000000,0x1220003bec00a004),(0x0,0x0),(0x1fffffc000000000,0xddf5cc000004028)]

def orSymmetries : Array (List Nat) := #[[],[64,49,134],[96,132],[128,49,100]]

def orCols : IndexTree ColumnInfo := (.fork 12 (.fork 6 (.fork 3 (.leaf [(0,1,332,18,6),(2,0,2397,0,7),(2,1,332,16,5)]) (.leaf [(4,0,2395,0,8),(6,0,2393,0,5),(12,0,2387,0,5)])) (.fork 3 (.leaf [(17,0,334,0,7),(18,1,332,0,4),(19,0,332,0,4)]) (.leaf [(21,0,330,0,4),(8,16,326,1,5),(9,16,326,0,4)]))) (.fork 6 (.fork 3 (.leaf [(25,0,326,0,4),(0,64,2077,258,6),(2,64,2077,256,5)]) (.leaf [(70,0,2329,0,4),(0,256,2071,72,6),(256,0,2143,0,8)])) (.fork 3 (.leaf [(8,256,2071,64,5),(256,64,2077,2,5),(320,0,2079,0,7)]) (.leaf [(258,64,2077,0,4),(324,0,2075,0,4),(72,256,2071,0,4)]))))

def orForest : Forest := ⟨2399,10,fun j => orSamples[j]?.getD (0,0),orCols,orSymmetries,liveLevels,liveIndex⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem orGeometry : graphValid orForest (boundsBefore entries319) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=2) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked10At0 : block orForest 10 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked9At0 : block orForest 9 0 7 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked9At7 : block orForest 9 7 7 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked8At0 : block orForest 8 0 40 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked8At40 : block orForest 8 40 43 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked7At0 : block orForest 7 0 7 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked7At7 : block orForest 7 7 10 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked6At0 : block orForest 6 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

theorem allAt10 : block orForest 10 0 1 = true := checked10At0
theorem allAt9 : block orForest 9 0 14 = true := (@block_merge orForest 9 0 7 7 checked9At0 checked9At7)
theorem allAt8 : block orForest 8 0 83 = true := (@block_merge orForest 8 0 40 43 checked8At0 checked8At40)
theorem allAt7 : block orForest 7 0 17 = true := (@block_merge orForest 7 0 7 10 checked7At0 checked7At7)
theorem allAt6 : block orForest 6 0 1 = true := checked6At0
theorem orTables : checkedTables orForest 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block orForest 0 0 0 = true)
  · exact (rfl : block orForest 1 0 0 = true)
  · exact (rfl : block orForest 2 0 0 = true)
  · exact (rfl : block orForest 3 0 0 = true)
  · exact (rfl : block orForest 4 0 0 = true)
  · exact (rfl : block orForest 5 0 0 = true)
  · exact allAt6
  · exact allAt7
  · exact allAt8
  · exact allAt9
  · exact allAt10

theorem noRun : Impossible (graphGoal 2399) 10 (vars 2399).toFinset :=
  root_index (g:=orForest) (before_sound _ sound319) orGeometry orTables
    (k:=10) (by decide) (i:=0) (by decide +kernel)

end Free351

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound351 : Lower (vars 2399) (graphGoal 2399) 11 :=
  augmentedGraph (k:=10) (m:=351) (hints:=12901687556) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 351) (by decide +kernel) (by decide +kernel) Free351.noRun

def entries351 := extendKnown entries319 11 [(2399,[]),(2493,[130,114,49,98,81,64])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound351 : Known entries351 := extendKnown_ok sound319 seededBound351 (by decide +kernel)
namespace Free471

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem noRun : Impossible (graphGoal 2519) 7 (vars 2519).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2519) (0,16,454,1,6) _ (before_sound _ sound351) (by decide +kernel))
    [] (pool:=(vars (poolMask 2519 (0,16,454,1,6)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Free471

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound471 : Lower (vars 2519) (graphGoal 2519) 8 :=
  augmentedGraph (k:=7) (m:=471) (hints:=26323452164) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 471) (by decide +kernel) (by decide +kernel) Free471.noRun

def entries471 := extendKnown entries351 8 [(2519,[]),(2549,[134,81,114,49])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound471 : Known entries471 := extendKnown_ok sound351 seededBound471 (by decide +kernel)
namespace Free255

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem noRun : Impossible (graphGoal 2303) 11 (vars 2303).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2303) (64,0,2239,0,11) _ (before_sound _ sound471) (by decide +kernel))
    [] (pool:=(vars (poolMask 2303 (64,0,2239,0,11)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Free255

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound255 : Lower (vars 2303) (graphGoal 2303) 12 :=
  augmentedGraph (k:=11) (m:=255) (hints:=553656580) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 255) (by decide +kernel) (by decide +kernel) Free255.noRun

def entries255 := extendKnown entries471 12 [(2303,[]),(2555,[118,130,81])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound255 : Known entries255 := extendKnown_ok sound471 seededBound255 (by decide +kernel)
namespace Free383

def liveData12 (i : Nat) : Nat := 0x112433062c2ffd40

def moveIndex12 (i : Nat) : Nat := 0x1c19a00a0d99f1429cbaa88ef89eb20e569dabb9035f88000000496039600003a58a000008d7454fb80000003b10000100010351100

def liveData11 (i : Nat) : Nat := 0x400600c0b06998785880983007118344cb2720074071102c1a661e1624260320032232499c1a5890e87040592100061909c92672c102080160641a661e1c8b10130610007119241a672c48580b11260e4a1320030072488cce0d2c48580b240d8e4a13200300b2488cb07280600e225002c1a662c410007110e01667061620800c0005a2333830e4589200300733830b0c0c0184e672488c18b2883148583924466659834b0c4001832232499c1858808ccc1c2c2446481b99c1a58620030273383446483940e4582924ce0c391616491199c18732c3032491199c1858699c18583d819f3135d0b4f56a86cb790b0bdfebb06c6c5960285470860ee9902ce4b06f8c812c16c10000ffd87503ff9dd40ffd83503ff5cd40ffc73503ff8cd40ffd81503ff5c540ffc71503ff4c540ffc31503ff84540ffd70503ff4c140ffd10502ffa2140bfd87502ff21d40dfe77502ff60d40bfc83503f78cd40bfd81502ff20540fbd41503fd84540ff930503fe80140

def moveIndex11 (i : Nat) : Nat := 0x412800f2422761452046213540b2a12f21f58191414da0992182c041e07aa193c033413800b80001a03c210702236218a0e4000161ae221c01ba41858235e163608c412ca0fc0001a0eba147e07c000041e4000180f1e045410b40f901f0816f81fe0000610f20360001617a0000c00ea156412a60dc4255804f201ea1de20ca608f00c8623d21fc21c4c1f2416b0203e01141c62238805cc09e20e381eb21b2001c211f00a8e006c1cba23f220e41960001c083403fe1ab203920c3e2116100414fa09de154e06da1da00d6000100bd616800018114f00c20180001c0cce1c20001c15fc05be18781d000000001e050e0d480a0013701ee424a10f40001618f211c0000802ce0e6e0888031e08100926180c02be21fe1d96059c062a00d024c0105e0296132c120c24e010801a441030152c259e124c18d008be0cfd1dca15b625a01e0e1e68061e1600111c13d0252a1d2e224c001e198224440907104e130e0b4c1c100faa003418b821260fea071204ca053801210b0024021596027c03a00b741bce188e0f6611620a2004ae20be176e0224034e1f700ad209a40c741dc0001c1b6000a0001209642490178a1f8e216000161a86078212700e8000100edc10da005a19d6200014901cf401b4069611860db0112013e8220022ba1ade247e0bf622821e210430233a02141a1800860d22195c0d8c1e9c0c4e014e19a00008215a237c22cc1b0c1d40000c13bc1c80000a20dc14a60d04074a12242568142c140a073c094e0760001c206219f80a60001817c82310054025141cd207f8042e15120a4e0c0008461bfe15d6205c1a7e1d6c0e0616dd02ca02ec0b1a0bac23ac1b4a05e0000e1a3e016000060de000160560001220881ed62432067206a2049c174e086c0f5017000000172c11b41b8c02441fa0000c22fa0aa20ae20ee8064a21ac16411da8166417e206e0ce803c759846e2c58e2c640021009c9300246800e140800600021ac0139e401810402252020018000000039300104b90a00107163c0010200c8f0030805001c0060e8800a002448f4a0c2800c0c68900302033200000201c007

def liveData10 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0xec1b02a07f78cd815037fcee40a81bfd7320540dfe39902a06ff8cc81502ffd32b8a817fd985c540dfecc2e2a06ff261715037fd10b8a81bfd875c540eff3bae2a06ff60d715037f906b8a81fde335c540dfec0ae2a05ff660715037fd1038a817fd931c540dfec18e2a06ff20c71503fbc6638a817fd901c540fdf4ca82a07ef65d41503f792ea0a81fbd8750540fdf3ba82a07ef64d41503f7926a0a81fbd8350540fdeb9a82a07ef1cd41503f7c66a0a81fbd7150540fdec8282a05ffa6531502ffb3098a81bfd984c540dfe4c262a06ffa2131502ffb2e98a81bfd874c540dfe43a62a077f9dd31503fbc6698a81bfd814c540ffab8a62a07ef50531502ffb3018a81bfe880c540bfecb862a06ff61c315037f90e18a81dfe770c540bfec8062a07fd25e11503feb0f08a81ff67784540ffa49c22a07fd60e11503feae708a81ff47384540ffb19c22a06ffa22115037fb0f08a81bfc8784540eff3bc22a06ff60e115037f90708a81fde3384540ffac0c22a07fd5c611503fea6308a817fe995c140eff3bae0a06ff60d70503fbc66b8281bfd815c140efeb8ae0a07ef50570503fec22b8281ffa994c140ffccba60a07fe25d30503ff30e98281ffa774c140ffcb9a60a07fe64530503ff12298281ff9814c140ffcb8a60a07fe1c530503ff26298281ffa114c140bff4ca60a05ff65d305037fb0e98281dfe774c140fef19a60a06ff60530503f7a8298281fdd314c140ffb08a60a07fe5c130502ffd32882817fd9744140dfec3a20a077f9dd10502ffb2688281bfd8344140fef19a20a07ef50510503fec2288281ff93044140ffd3bc00a07fe5ce00503ff0e700281ffa3380140ffcb8c00a07fe1c600503ff26300281ff83180140ffd08c00a04ffa65875027fb2643a813fd9121d40cfe4c4eea067fa22775033fb0f3ba813fe9960d409fecb906a067f9dc835027fb2241a813fd981cd40b7ecb0e6a05df65473502f7b2839a817ed921cd40bfac88e6a05fe640735037b93119a81bde888cd40deec3c66a06f721e33503bbcef19a81fd8908cd409ff4cb02a067f9dd815037bc66c0a813fd9720540cff3b902a04ff64c815037bc6640a813fd985c5409fecc0e2a05ef65071502f7d32a0a81bbc9850540ddf44282a06ef61d41503b7ceea0a81bbc8350540fcf19a82a07ee241415027fb3098a81fb5414c5409fecc062a05df65431502f7b2818a817f9900c540dfa4c422a06fda22115037eb0f08a81bf48784540efb3bc22a06fd60e115037e90708a81fd63384540dfac0c22a07ed50611502ff53298281bfa884c140dfcc3a60a077e9dd30503fb46698281fb9414c140fec98a60a07fc84530503f6a8288281bf98780140efd3bc00a06fe60e00503fb46700281bf98180140fdca0c00a07fc846005025fb2c41a813bc9850540 else 0x593d573525d40b4dfd2f347bd13b417cfab3b3cdf3359cc8b2ffcb23291c9bb24bc87b1f1c7131abc623165c4bb101c3a30b1c23b061c0d3011bfbafcbbe7af71bd12f17bb82eb3ba1ae77b9a2e1db83ade1b6d2d91b592d23b452cddb1d2c51b042bedaeb2b6bad4ab39ac5aac1aa52a85a9daa5da93aa17a73299fa61a977a57a931a4128d7a25a85fa0f27d39ec276f9d0a7159c1a6cf9b02689997263997e2585958a52b94224c79242477903a3cd8ed23738d6a3378bb22c98a7228d89aa24788921e3870217f854a11b83ba08f81b20358021fe57dc9f457c61eeb7aa9e417739d9775f9d657491ccf7261c7f7171c116fb9bcb6ef1b8f6e01b716d61b496ce9b216c21aef6ae1a6d6901a2767c19b9668199165e195f64c991963898c9622186560b98155f797a75dc17435c316d55aa167159115ef570958b557953154114cd52d149b519144150794054f393a14da93294c412d94a89289494923948311f347911d546f11a3465117b45b115343a90a941a10454038fcd3d68f193b88ea139d0e473868ded3700d9335c0d4d3458cd532a0c673110bc72e18b452c60af52b20aa52918a0f276099725a8933235089d217081b1fb878f1ce86ef1ae067718d861d17985a515e053713d84bf11f843d10183c50e603430c082d509d8221078019f05a013b03e80cd023005f00c80190003ffceec1a81ffe995cd40ffecc2e6a07ff61d73503ffb06b9a81ffd915cd40ffe48ae6a07ff64173503ffcef19a81ffe7760540ffeb9b02a07ffa6571503ffb30b8a81ffd875c540ffec9ae2a07ff24d71503ffb06b8a81ffd735c540fff19ae2a07ff60571503ffb20b8a81ffe331c540fff4ca62a07ff66131503ffb2e98a81ffc974c540ffec3a62a07ff9dd31503ffb0698a81ffd734c540ffec0a62a07ff5c531503ffb2098a81ffe770c540fff3bc22a07ff5ce11503ff8e708a81ffe3384540ffeb9ae0a07ff8cd70503ffae2b8281ffd315c140fff3ba60a07ff5cd30503ffae298281ffd314c140fff3ba20a07ff5cd10503ff8e688281ffe3344140ffeb8a20a07ff4c5105037fd32c3a81bfd9361d40dfe49b0ea06ff645875037f922c3a817fe9961d40efe49ceea077f246775037fd113ba81dfd879dd40dff4cb06a06ff645835037f922c1a817fe9960d40dfec3b06a077f9dd835037fcee41a817fe995cd40bfecc2e6a06ff661735037f930b9a81bfe885cd40dfec3ae6a077f9dd73502ffb3039a81bfe881cd40bfec88e6a05ff64073503fb92f19a81fdd878cd40fef3bc66a07f7246335037fd1119a81bfd878cd40dfe43c66a077f9de33503fbb0719a81fdd738cd40dff4cb02a06ff65d815037f92ec0a81bfe7760540dfec9b02a06ff24d815037fae6c0a81bfc7360540dff19b02a05ffa65815037fb0ec0a81dfe7760540df) else (if i < 3 then 0x13060f52c08c8218a19987b832586c460310804003241202cccf065018010a0210200e0900ae679260cb818025492c128b09e0c284c0e10872040c960181d180cc4440c904e12333c19120020160121d141607851b258108c3f11013c902806c39384e2e842300c5b088701841606c280848a0052c0a26a0090c0a2618191310068609134304280331ca2616944049211040198e42d38262247217121380c42988606472169444446364802e2c270188130a261b09130244204262805a41022c14671221c2905a5c462c14482103820272169b3384c2d1a220e0721605a5c462c101809e220e05a5c4533490200b4a06622a90941895330382c0b480282708ab2251724845360b04a2e22a90401693114d8130842d2c22a901c1690131081cc184ac9333c45108a6c2505a44cf240b00e128b08aa41005a4030008b02126221cc581691330b00c0842d2e2309880c84c508aa40604216941c04c2d1e0d0985a3c461316229981c1605a500e130582d2622060731605a5430520b0210e42d3623098b111003984c2d2a812901c1c85a5c4613102c020261c85a500e1312232904016914084c50986130a19098813ccc4818413c18509850384c40600709e23926678305a2e842a00c0bc18130885930180b60c040262c9852c192c1e668660c9ca58504d0c40f11c1859308001e2309c37920878366616842b00c3f113330382c308108e6707458510002ccc0e0f42c3006028402c901d0702016480e838100b240741208059203a0e0402c901d070201648028402c8f330392c1a8199e0c9ca58503333c1b114e7243019832a496114083333c1b11c90d9981c960c161000c0531184c02c9306ccc2d085820623066679260c603240c4733c93063018210581c90408e62c1880218581c900c8e62c1e2206005836499985a108ba9033110704c0e4a008280e0981c9611ccf24c181484cc0c828160724ccc1bc18030b0aa003609807836499985a10a603ccf2484f0628320882d9984016181b80f33c9213c18d99e0c1602841031100333c9306128310e92088379222799e0c188748100160032406c310e4e138a00d8621c94160172406c310e4c0002d920361887260e52c12808666783258500d0cccf06c47243007832a496114080f33c1b24c44c01a8188e679260c600d11ccd0e4b0a8640799e0d92622604d40c450cc903932220a648898725cce0cc1a13c931136678301816104203311c1b24ccc4a0b5199c1909e0d926226ccc13c902020280da2383027926661085a904e13c9311c1b330b44a4667064278364988981607333c183a0b0c8666783272161540ccf068b080da8199e0c9c858643333c1a2c2028a021999e0c161814ccf060b0881e678345840382c1072160b7a5dde3769dd43737dc2b6f1db636b5da73683d933633d8435e3d6db else 0x5001d10182003422112c083296081944c489a6683034401444103496080c108481a800b0819058401e66200082997334b0402c66960d13ccc040e4821666200a648cc05074601a2709c661f963300c4207513280919a263013334b0602832240c03c180c01010068c89a0c0283c444d3301306068a0860c0609041400c0152c078a89c0c018a024140504c1e180689c27030345014130786062270987202151301005c1b1128880b0a030585314060282d01c2640401d46c0520200ea360b103f8b0428237160d330fe2c18a188a0d1600a51001c12213203509881cc453384c0528420d42635031105850202d8880109901c0011b18380b23634cc0484c68300a02426404f241402120a39203c141056c905008489980b9202e2e97244e4500b482042628042443028185131081915209948503a58104c1b0742d220d998502291360a0221c260d83a109133492061480e0a0d0984408460e1585028882060c02e67920ba0f0949628394b0281a488180a0e03e2c191312c5e1a060288999e0c9619240310982413174c8342620741e14a496042304c000401d0101c080594036028b21091400a58144d40120611400c8d92c084a9202002826060ba109c0c10d59088909c18204c303226204c14058212266922b20f1043c19520b880c8862160c0b2b26500434182f0e0b9985c108c161100210c4205706ccf240854012b2108d4010c2f03236084d098280b0424490361641e2426150252038390a0b098440040438e450287e05c7316100316c221818280841946c111b3310000c180414f240644e8e52c58669603c3ccf111640a174b99a582a0c4206706153334b0d030b2098122e961314840e88401086298399260c16e66a8cc024450e44c5d3427998a33844420bc4c0e8c0b03c244e390b4788820098340a8981c9c438e42d18880a07a1712030e220b05a304414084699858108c030515205b060b4c1b058108c1314019c1816564ca0072160424ccc2d04414084aa00581b042404e1306c05ccf24c183a0b92022b2108d4006c2c0d82128321b0581d1003058211881830019980808033920911ca58b100394b01e2649830901d))

def moveIndex10 (i : Nat) : Nat := (if i < 1 then 0xd0f651a1a09761739025905ea018a13390e800000000f160f04f90e0609e31b74184d02360a3b14fd04c0000e009000040080000607540489080818dd0840134d193409030b631d381271186405650bb40da50f50000b83710c28119f135302410e27116f1400039b142480dc12f000080370000e00b2181b1516078406de02cb170814411d250ca805181c60000301960b4211881b3a19460d5000001560000a1a0e16ff1a96020618a912d0000902651d1e17df0cc4093311fd161000000008012f05c10520113a04bb0740000c0626028605b40ef61908073811a0000000000d7006801473136110d812a30d460fe20c8c19a4050e111a0343152511c70fb10220000918f00891146e02d30e9c040e15ed1af900a90f871aed0d3d0a8b1bef1a740bde03c20911105816231b9e01d003641d020a4b041d1bab0f411a400000000b04d11cf00000000704a000000000000c15741ce707a6199813b418be128e03f101c8045314e1198d08761a500d6706a713a715900009115b0e391b6310440cb11c350b9c0dda1b521556197612300004188a007012660a220d900000158e0cf50c62038c16be00d2029e0e6c14c0000b13c7079419e51450000e02b0000007b910ea1d50000c02a80e151a39016605a01b2215b810c906930a150965067416761214117e07f51c40000d0a7e1b1d0886180b09ab0ce9014c01520f3c0b560bed0afc0bf6065911ea08a0000000020b0317831b8219b20468083a14d50f0c164e05d10d190e4d11d71630000d166300ec1ad21a82095000070c7a10a0000000071483191012420b801923196c0d0c03d0000c0d8f12e508200003064600cf0b7f09920de20779102a09fe1c8a0dfd1d40000f0d290ac4066d1c90000c0b2316c0000c0ae101fe17bb1d620ff50760000117ac1cb5005207e7108b0710013706c28918168e12c00006004613f0054a0f1a0c5a0ee7109f0f2314b50bcb09ca081d02fe0e5718570fae01a71ca8003d072b1bf582c9058710fb189813171a22035d02eb13830dc11c01055a17e908600ba1107f0335125d0530101608b01cce1003057008c716da103301b20ebb0c490e710a60001a0430070b06b70f9f18c5130203160c0417c2085814a40c3d06f6021209d0171e04ec049d08ed122c0abd07c2129215d40175114c0f780aa7112f169917441b47098e12bb0db00001902052005000029130d61c64509005c020006030b05120d17120a0b1d3f0523024e0504006202010d20011d001c13431e110b0003071d0005003d190d010e0f16001346050407130e030a080c190304000a010002080105000f040111571e0504050204020811040007050001011b1e0b0f491b00005e17011f0b080502012c18001201032805000f180b000104090a00160600020900040602010d2e0b06040106 else 0xe19ca044310b607dd0a56042000011c7e01070ad00008137418300002154e1397195e03ac1a681abb03b9011c150f094f176513d21c56172d1bcf0cd5092b059615c108fe14351c2d1bd71aae954d0b350edb0b1716a60ea6032e182b15fb04781bb408da16e90618179f86fb13ec19d80fc117fa000f0c970a0482b4110d0a9f177406ec88ce00fc05fc0ec7002118ef00628148120815ad15311acc027113220fdf1cd201ed19f6060b141f1c130302106103e51b0d1658187a063f82ab11b009b00008149317560c1)

def liveData9 (i : Nat) : Nat := (if i < 3 then (if i < 1 then 0x9784540bf96889784540afdaa98784540afd2a58784540afd68c8784540e7d2a27784540e7d2627784540e7da227784540e7d61e7784540afd6a09384540bbd6989384540bfc6809384540afdaa98384540afd2a58384540e7d9dd8384540afd69c8384540e7d9dc8384540afd6a17384540afd6a07384540bbd6987384540bdd6947384540bed6907384540bf96887384540bfc6807384540ef52a23384540ef52623384540ef5a223384540ef561e3384540ef521e3384540f759de3384540ff428233845408ff2a688845408ff2a58784540afd68487845408ff2a58384540abf6988384540afd6848384540afdaa98184540e7d9dd8184540ef58cd8184540afd6a17184540eeda214184540eed61d4184540f6d9dd4184540eed20d4184540fe58cd4184540afd6a131845409df696995c1409ef692995c1409ef2a5415c140dee692994c140bee692994c140cfea66884c140bfa688974c140afeaa9874c140cfe2a5874c140cfea65874c140ef628d874c140d7ea66774c140e7e2a2774c140e7ea22774c140e7e61e774c140ef6a22334c140ef661e334c140f769de334c140bde694914c140bee690914c140afe6a0714c140bee690714c140bf668c714c140beeaa9414c140bee2a5414c140deea65414c140eeea21414c140eee61d414c140f6e9dd414c140fe668d414c140fe68cd414c140fec645414c140bf6aa9314c140df6a65314c140ef62a1314c140ef6a21314c140ef661d314c140f769dd314c140ff4245314c140ff45c5314c140fe6505314c140fec505314c140dfca66114c140efca22114c140efc61e114c140f7c9de114c140ff428e114c140ff48ce114c140fec506114c140ff44c6114c1409ef692994c1409ef2a5414c140fe5505314c1409ef69299441408ff6a587441408ff6a58344140bedaa94144140deda654144140eed61d4144140f6d9dd4144140ded64d4144140fe58cd4144140fec5053044140afeaa98780140cfe2a58780140e7e61e7780140afeaa98380140e7e9dd8380140afe6a17380140afe6a07380140bbe6987380140bde6947380140bee6907380140bfa6887380140bfc6847380140df62a63380140ef661e3380140f769de33801409fe2a63380140ef660e3380140afeaa98180140e7e9dd8180140ef68cd8180140afe6a17180140afe6a07180140bee6907180140beeaa94180140eee61d4180140f6e9dd4180140fe68cd4180140afe6a13180140fec5053180140afe6a03180140bde6943180140bee6903180140efc61e1180140f7c9de1180140efc60e1180140ff48ce1180140efc6061180140fec50611801408df6969961d408ef6929960d408bfaa99620d40c3f9dd9620d40c6f2627750540aaf6988350540ce72623350540be668c9050540abd6988384540fe4505314c140 else (if i < 2 then 0xcfea21901cd40af769c988cd40af7684988cd40af76a0978cd40af7aa9878cd40af72a5878cd40af7684878cd40e772a2778cd40e77262778cd40e77a22778cd40e7761e778cd40af76a0918cd40be7690918cd40ef661c908cd40f769dc908cd408ff2a6888cd408ff2a5878cd40af768c878cd408ff69e9960540cef69299605408ff68e9960540cfe6829960540aef6929960540c7f65c9760540c7f2a67760540c7fa6677605408ff2a67760540cf764c93605408ff2a573605408ff6a47360540abf6987360540adf6947360540aef6907360540afb6887360540afd6847360540afe6807360540cf72a63360540cf7a663360540e779de33605408ff2a633605408ffaa99720540c7f65e77205408ffaa99320540c7f9dd93205408ff6a57320540c7f65d73205408ff6a47320540abf6987320540adf6947320540aef6907320540afb6887320540afd6847320540afe6807320540cf765e3320540e779de3320540cf764e33205408ff6a2995c5409bf69a995c5408ffaa9985c5408ff2a6885c540c7f662775c5408ff2a5835c5408ff6a4835c540a7f69c835c540abf698835c540afd684835c540cf7662335c5408ffaa9981c5409efaa9941c540cefa21941c5408ff6a5831c540cef651831c5408ff6a4831c540abf698831c540cef650831c540cf7662331c540de7652331c540aef69c9850540cefa668850540cef2619750540aefaa98750540cef2a58750540cefa658750540eed2858750540d6fa667750540e6f2a27750540e6f2627750540e6fa227750540cef2627750540e6f61e7750540cef2619350540bcf6949350540bee6809350540cefa648350540aef69c8350540e6f9dc8350540cef26173505409ef6a47350540aef6a07350540cef2607350540baf6987350540bcf6947350540beb6887350540bed6847350540bee6807350540de7a663350540ee72623350540ee7a223350540ee761e3350540f679de3350540fe52863350540fe62823350540cef2623350540dee65c9050540eee61c9050540f6e9dc9050540bee68c9050540fe68cc90505408ff6a2994c5409fb68a994c5408ffaa9984c5408ff2a6884c5408ff6a5874c5408ff2a5874c5408ff6a4874c540afd684874c540bedaa9414c540deda65414c540eed2a1414c540eed261414c540eeda21414c540eed61d414c540f6d9dd414c540fe528d414c540fe58cd414c540fec281414c5408ffaa9980c5408ff6a5870c540c7f65d870c5408ff6a4870c540c7f662770c5409dfaa9950c540cdf6a1950c540cdfa21950c540cdf61d950c540cdf21d950c540d5f9dd950c540dcf691950c540cefa21940c540cef61d940c540d6f9dd940c5409feaa9900c540cfea21900c540cfe61d900c540d7e9dd900c540afd69c9884540afd68c9884540afd6a0 else 0x4000c402a40780174000aff6849361d40aff68c9161d40aff69c9160d40cff9dd9120d409ff686995cd40aff684985cd40cffa66885cd40cff261915cd40aff6a0915cd40bef690915cd40dfdaa9911cd40dfd681911cd409ffaa9911cd40cffa21911cd40aff684878cd409ff2a6778cd40aff68c9760540cffa667760540aff69c9360540affaa97360540cffa657360540affaa97320540dbf69a995c5409ff68e995c540bbf69a995c540aff68c985c540cffa66885c540cff261935c540aff6a0935c540bdf694935c540bef690935c540bfe680935c540affaa9835c540cffa65835c5409ff2a6335c5409ffaa9931c540cffa21931c540bef68c9750540eef2627750540bef69c9350540eef9dc8350540befaa97350540eef2a17350540eef2617350540eef61d7350540eef61d7150540eef20d71505409ff69e994c540dfb68a994c540bfb68a994c540aff69c984c540cffa66884c5409ffaa9974c540cff2a1974c540cffa21974c540cff261974c540aff6a0974c540bef690974c540affaa9874c540cffa65874c540ef728d874c5409ff2a6774c540efd2a1714c540efd261714c540efda21714c5409ff6a5714c540fed29d414c540fed25d414c540fed9dd414c540fed5cd414c540eef61d414c5409ffaa9970c540cffa21970c540cff662770c540def9dd940c540dfe9dd900c540aff68c87845409ff2a67784540aff69c83845409ff2a57384540bbf6987384540bdf6947384540bef6907384540bfb6887384540bfd68473845409ff2a63384540f7d5c5315c140fed505315c140bfe684974c140bfe69c914c140bfeaa9714c140fee9dd414c140fee5cd414c140fee5c5414c140ff65c5314c140fee505314c140ff55c5314c140bbf6987344140bdf6947344140bef6907344140bfb6887344140bfd6847344140fed9dd4144140fed5cd4144140cdf6969961d40cef6929961d408ff68e9961d408ff6869961d408ff6829961d40cfe6829961d40adf6969961d40aef6929961d40afe6829961d40abf6989361d40cf764c9361d40cfd6449161d409df6969961d409fe6829961d408ffaa99321d408ffaa99121d40a7f68c989dd40a7f684989dd40a7f6a0939dd40b7e680939dd40a7f6a0919dd40b5f694919dd40b6f690919dd408ff2a6889dd40a7faa9879dd40cef6929960d408ff6869960d40aef6929960d40cfd6449160d408ffaa99720d40c7f65e7720d40cbfaa99620d40cbf69d9620d40cbf29d9620d40cbf9dd9620d40cbf6859620d40cbf2859620d408ffaa99120d40c7f9dd9120d408ff6a2995cd408ff2a6885cd408ffaa9981cd40cbfa21961cd40cdfa21951cd40cefa21941cd40cfba21921cd409fdaa9911cd40cfd6a1911cd40cfd2a1911cd40cfda21911cd40ded691911cd409feaa9901cd4)) else (if i < 4 then 0x3040c1820302502d1b060839273309430080b448440d0211801419060b088406070885888683050981e141305a200a0e840180c881982a0ba30800a81c0c0986098401c1100a084904c304c0a8a09848882d160608000b240e0608116040604060406048604060406040c90200181060608004cd160801848184040e088a0986098783050884018401848185920400000818492711e67c180285d0b408504479270608bccc1680f3c0e858281d0b048e516080c8530400f416151ca2c1733e0c0b00a108712c1014426c4783733e4812810a29cba69698aa5be954a4e691ea40e8e8a3628bda28a887a1b2851a0da81ba0027e59f2a7af9e527799d7a7389c4a6f79b9e6c19a6e680999663f989260997ba5d396e259d95de551950653c948650693da4d092d649a91a644390a240d8fca3cc8ef23968dc23558cbe3098bba2d38ae22a88a0a2678932231885a1f087561ba867e18f85fe164852612e844e0f883760c2829e08c81c6061811a02080420007f69fbf7e65f7e7db9f5e7d0df287c35ef27b5dec77adde9c7a31e717959e3b78ade0577a9dcf76a5da4767dd8475a5d4e74cdd23744dd0373cdce3734dcc372a1c9871f5c6270f1c377071c0c6fc5bd66ec1b956de9b546ce5b296c0dadd6b09aa76a31a716959a4668ada1067d59e567559ba66a999a662997a65a995a6555950652d93b64ad91b642d90663ad8d063018a5625587a61a984f612983a60a98045ffd7d95ef97a35e2176d5d4972c5c457015bc56ec5b456b65a9968b59ed65558e961f58115e957395b3566157d55b5568556153d54054db53014b0525546f515143950794034fa13d84ef53a24df13564cc12ff4bbd2df4b112b44a3927e4961248490d23e48b921e48651fe478d1bd468918745dd13b44ad11043d50da42fd0af427d08f41fd06f41a905a415503a40d50254054ffa3fd4ff03facfe63f84fbb3dfcf4e3c74ef73b44eab3a40e8039c0e4a38bce1f37b8dde3764dc93710da9360cd683534d3d34b4d1233dccd132d8ca63200c703154c4530d4c253028bfa2fa8bda2f28bba2ea8b9a2e28b852e00b7b2dacb5b2d2cb3b2cacb1b2c58b062bd8ae62b58ac62ad8aa62a58a862a04a7c29dca672988a5d2960a3d2888a1227dc9d127049b126b09a7263098725dc967253093c24b091123d88f123848c622d8890220085a2128845210083020ac810202c7fb1fac7d01ed479a1dfc76f1d7c7441cd07241bf86ee1b4c6c31aa06981a2068319cc64d18f463818485f717445cc171c5ac167058c15f056c1570541149850b13c04ca12904941210453110c42810603fd0fb43dd0f343bd0ee03a80e603880de03680d603480d0c3330cb831e0c643090c102ff0b902d40b102bf0a902940a1027409902540910234089021f08682150840200068c15104d811b else (if i < 5 then 0xb998888f33100200b8cc60002108210131010026202601440541188280141013028054604c29c1118050800a0191013406286c10a74cd088c08013100d008200c0340201a2042e0c040604c0008000131733e0c20270cc0b8c1f040281003c3020078240c0581e10000914907c900281e184802620a7ccc404383080c8402013072303205441200c888984811130342c0c014080c22013101300a208010841082108200c0108298131003092200004c40400e880801d101003a200e0744040020808013100508050622e22070240c2107088409c1109038220685045998041b330082040100a1036070406c0e080911b101b0382036070404c204c211c108800040c84a10050a02024128400020902381e1806032200c0705c902801e18000ac0f080301c100b04420040b8404c204c20302430200c200c240c2140108b03040e8211059044200c074168c00fc280806041e054105706e22661402a0c21054103d0a822660b82a0c0102e100c080600a17860142f021181d042203a084407410880e821101d042201810b2078416c11080e821101c080c081d0422026102612981c0c1016102610000c90200c240c204c2003a084402c108809841f02e1000081905c2028100c0644007e1a0c1e0c158170c015c2302e185903c20b207841640f082c81e105903c20181781c0c2c821100b0d0608005821103f0a020061016088400c20cc1481f18030b022b2088416c11082d822105b04420b6088416c11082d82210030800184178541706e481082683a28020b0084616c108a2c842d82210330600e8600c2e882985d100c0742467c904058108801840b021105505020800e4168c0603d05c30680b8118c2211107a0b8800c280c200c0e0809841b05c04234221e481400f0d08840002610061003e0a0282280c40241181818140622028070584420500cf330400b0b84428e516080081c100303820b6084407020702070207020702000610411406200030813085c042200000004004c0f47ccc02724076128a10c1a828042407e0f41402120330540e060f428023180609e0e860301d08888488840c81407430200e8444420400df330424222101110800b0211024012174600c0c882d82210030803082e03c202c084409c2801e185b0442006104e094188c0184018191403080308030803038280612581806108010801c0c1004102610000c9020302030243038182008200181a221e4810181018101812181018121810000c90200000b021100205a2026100a088414c1002e180c0e0608004cf9208100c300c200e888a01860484158281006032200000b1105a24221e22120188d830792050050360c1000098414190608103038443c4416898882d100c05a24220b440b4344434441688888488840d8050623a221028070406c3444168983058 else 0x50e480647c9028005180503a2080108401009880104410130002a6741840642208220408004101b008202004c40740c880604310440262032058410000080c816100001620160644110018820804101a0262066010208c21053e6630260004154201429f3318420a1ccc610)))

def moveIndex9 (i : Nat) : Nat := 0x20a3c261066806511b41ca0b6c3320d6c05200f0400000e10b0a701e605200a10ff011e03b834709f81790c50253087809207c0000002c3e0000000a00143d705ac2a90cb815e090000e03e42200000005048000e06a600308d437f02c0000000c04b0ee80d00024429009039e01ec2fd076810a06d83650b241360e384180f0c20c004000c0eb04580c182b1113008310cc0cf06079ec0b8d417300102049941109000100040081008002084043

def liveData8 (i : Nat) : Nat := 0x1c661000000038183a48105b019100d8400e1108189020a6101c08080414c207a1002984040202010530829840c4810000078101308098404c202610000000000000000000c48161108000261d1102d100c44262210188840622101b0211188840580b44c4816110e7d96e5191e3d8ce2987dfd76da15fd755ad494fd1d3ecd92dc951cc6911c2500be0efbb4e4b88dfb74d4b30c3aecb2ac0adaaca8a98a3a849ea7099a5c94a488fa34849f0799dc6e9805d9544c928418fc368a01f844088014bf6da99a21715025deda554c1ae2a052fdb6a65835c540c77d544c2e6a0a8166f6dc835c5415029f6d953344262a046fdb6aa9974c5408fdb655532e98a812df6d6aa61d315029f6d9532c3a62a05addb628d874c540b76b6e4c28298a811bf6d8a99de115023f6d915319c22a04ef9b6aa9714c14086fb6a54d113ba8125f6d6aa61e7750293eda94ecb106a052bdb429d9620d40a5db6453b2c41a814bd6c4a76588350297cd814ecb106a060feaa9dd9620d40a1fb6e50b2c41a8149f6d4a16588350295eda142cb106a052edb22859620d40a5f36050b2c41a814ed2e1a4644735025aedad54c3c66a043bdb42a6888cd4085fb6d55330b8a810df6d6aa6617150217e5cb4c41ae2a062bda6650831c540957d76d3106a0a818afa65a620d4150345f3bb4c41a82a043bdba2607350540c57930d30e6a0a818eb261a21cd415031da4c34239a82a063b8986807350540e339313bc66a0a813e6aeda3241415033cccbb4648282a06b998768c9050540db34eed1920a0a81be46c5a3241415021deda554cc262a043edb2aa9984c540bf236051a8298a817e46cca0505315025badad54c3c22a04bb5b4aa9838454095ed76d310708a81a3d9dda620e11502d5adb106a0c22a04f39b52a5414c140bf236848a62982817e4aed414c5305037c95528298a60a05f90b9505314c140ef2532a0a6298281ee42a1414c530503dc94428298a60a07b9187505314c140fb24eea0a62982811cf6d4a9505305025bcdad54c3c00a04bb9b4aa98380140

def liveLevels : Nat → Packing
  | 12 => (1,1,7,0,0,0,0,liveData12)
  | 11 => (28,2,7,0,0,11,0,liveData11)
  | 10 => (302,3,7,0,0,14,0,liveData10)
  | 9 => (471,4,7,0,0,14,0,liveData9)
  | 8 => (71,5,7,0,0,10,0,liveData8)
  | _ => emptyPacking

def liveIndex : Nat → Nat → Option (Nat × Nat)
  | 12 => lookupWord 19 41 4 9 5 0 moveIndex12
  | 11 => lookupWord 103 342 7 16 9 3 moveIndex11
  | 10 => lookupWord 162 532 8 16 9 3 moveIndex10
  | 9 => lookupWord 29 87 6 14 7 3 moveIndex9
  | _ => fun _ => none

def orSamples : Array (Bits × Bits) := #[(0x1ffff9d00080f0c0781df2815e007d1cf,0x1d1008040d41008bb8008044d8e4),(0x1ffffc00630b2f03fb6203ff6180821ff,0x60063693f206920004f47580211a),(0xe08c13c00380841c80b800e3e30,0xea8c12c00380041c80b800e8c20),(0x100101c0ffc04f89f06c1ff03fc0,0x1101024024404f8a322439603386),(0x600e01ff0000700e00701fffc000,0x60ae85bb80243034005146890408),(0xffe0000007ff0007fe0000000,0x2b160000007f70007f61000400),(0x7ff0000000007fffff8000000000,0x1730000000006dfffb0002000404),(0x0,0x0),(0x7fffffffffff8000000000000000,0x68c4e9bfcbb700000400040d8828)]

def orSymmetries : Array (List Nat) := #[[],[98,131,84],[16,66,101],[16,82,131,100],[48,129,82],[48,129,98,16,66,84],[128,49,100],[128,49,66,16,82,98]]

def orCols : IndexTree ColumnInfo := (.fork 47 (.fork 23 (.fork 11 (.fork 5 (.fork 2 (.leaf [(0,1,332,50,7),(1,0,382,0,9)]) (.leaf [(0,2,312,69,7),(2,0,2429,0,9),(1,2,312,68,6)])) (.fork 3 (.leaf [(2,1,332,48,6),(4,0,2427,0,11),(2,4,2417,8,6)]) (.leaf [(4,2,312,65,6),(6,0,2425,0,8),(5,2,312,64,5)]))) (.fork 6 (.fork 3 (.leaf [(0,8,99,276,7),(8,0,2423,0,9),(10,0,2417,0,5)]) (.leaf [(12,0,2419,0,8),(13,0,354,0,4),(10,4,2417,0,5)])) (.fork 3 (.leaf [(16,0,367,0,11),(1,16,358,8,6),(17,0,366,0,8)]) (.leaf [(18,0,365,0,7),(18,1,332,32,5),(19,0,364,0,5)])))) (.fork 12 (.fork 6 (.fork 3 (.leaf [(4,16,354,9,6),(5,16,354,8,5),(8,16,358,1,6)]) (.leaf [(16,8,99,260,6),(24,0,359,0,8),(9,16,358,0,5)])) (.fork 3 (.leaf [(25,0,358,0,5),(12,16,354,1,5),(20,8,99,256,5)]) (.leaf [(28,0,355,0,7),(13,16,354,0,4),(29,0,354,0,4)]))) (.fork 6 (.fork 3 (.leaf [(26,4,353,0,4),(32,0,2399,0,11),(1,32,94,256,6)]) (.leaf [(32,1,332,18,6),(34,0,2397,0,7),(34,1,332,16,5)])) (.fork 3 (.leaf [(35,0,348,0,5),(36,0,2395,0,8),(17,32,78,256,5)]) (.leaf [(49,0,334,0,7),(50,1,332,0,4),(51,0,332,0,4)]))))) (.fork 24 (.fork 12 (.fork 6 (.fork 3 (.leaf [(40,16,326,1,5),(56,0,327,0,5),(41,16,326,0,4)]) (.leaf [(57,0,326,0,4),(64,0,2367,0,11),(2,64,2109,256,6)])) (.fork 3 (.leaf [(64,2,312,5,6),(66,0,2365,0,8),(6,64,2105,256,5)]) (.leaf [(68,2,312,1,5),(70,0,2361,0,7),(69,2,312,0,4)]))) (.fork 6 (.fork 3 (.leaf [(74,0,2353,0,4),(72,4,2353,2,5),(74,4,2353,0,4)]) (.leaf [(78,0,2353,0,4),(0,256,2071,104,7),(256,0,2175,0,9)])) (.fork 3 (.leaf [(258,0,2109,0,5),(8,256,2071,96,6),(256,8,99,20,6)]) (.leaf [(264,0,2167,0,6),(260,8,99,16,5),(268,0,2163,0,5)])))) (.fork 12 (.fork 6 (.fork 3 (.leaf [(273,0,78,0,4),(272,8,99,4,5),(280,0,103,0,5)]) (.leaf [(276,8,99,0,4),(284,0,99,0,4),(288,0,2143,0,8)])) (.fork 3 (.leaf [(290,0,2077,0,4),(40,256,2071,64,5),(304,0,79,0,5)]) (.leaf [(273,32,78,0,4),(64,256,2071,40,6),(320,0,2111,0,8)]))) (.fork 6 (.fork 3 (.leaf [(258,64,2109,0,5),(262,64,2105,0,4),(326,0,2105,0,4)]) (.leaf [(72,256,2071,32,5),(328,0,2103,0,5),(96,256,2071,8,5)])) (.fork 3 (.leaf [(352,0,2079,0,7),(321,32,30,0,4),(290,64,2077,0,4)]) (.leaf [(354,0,2077,0,4),(104,256,2071,0,4),(360,0,2071,0,4)]))))))

def orForest : Forest := ⟨2431,12,fun j => orSamples[j]?.getD (0,0),orCols,orSymmetries,liveLevels,liveIndex⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem orGeometry : graphValid orForest (boundsBefore entries255) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked12At0 : block orForest 12 0 1 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked11At0 : block orForest 11 0 13 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked11At13 : block orForest 11 13 15 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked10At0 : block orForest 10 0 2 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked10At2 : block orForest 10 2 56 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked10At58 : block orForest 10 58 17 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked10At75 : block orForest 10 75 56 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked10At131 : block orForest 10 131 56 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked10At187 : block orForest 10 187 56 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked10At243 : block orForest 10 243 7 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked10At250 : block orForest 10 250 52 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked9At0 : block orForest 9 0 10 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked9At10 : block orForest 9 10 56 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked9At66 : block orForest 9 66 56 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked9At122 : block orForest 9 122 56 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked9At178 : block orForest 9 178 56 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked9At234 : block orForest 9 234 56 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked9At290 : block orForest 9 290 56 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked9At346 : block orForest 9 346 21 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked9At367 : block orForest 9 367 56 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked9At423 : block orForest 9 423 48 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked8At0 : block orForest 8 0 56 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked8At56 : block orForest 8 56 15 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

theorem allAt12 : block orForest 12 0 1 = true := checked12At0
theorem allAt11 : block orForest 11 0 28 = true := (@block_merge orForest 11 0 13 15 checked11At0 checked11At13)
theorem allAt10 : block orForest 10 0 302 = true := (@block_merge orForest 10 0 131 171 (@block_merge orForest 10 0 58 73 (@block_merge orForest 10 0 2 56 checked10At0 checked10At2) (@block_merge orForest 10 58 17 56 checked10At58 checked10At75)) (@block_merge orForest 10 131 112 59 (@block_merge orForest 10 131 56 56 checked10At131 checked10At187) (@block_merge orForest 10 243 7 52 checked10At243 checked10At250)))
theorem allAt9 : block orForest 9 0 471 = true := (@block_merge orForest 9 0 234 237 (@block_merge orForest 9 0 66 168 (@block_merge orForest 9 0 10 56 checked9At0 checked9At10) (@block_merge orForest 9 66 56 112 checked9At66 (@block_merge orForest 9 122 56 56 checked9At122 checked9At178))) (@block_merge orForest 9 234 112 125 (@block_merge orForest 9 234 56 56 checked9At234 checked9At290) (@block_merge orForest 9 346 21 104 checked9At346 (@block_merge orForest 9 367 56 48 checked9At367 checked9At423))))
theorem allAt8 : block orForest 8 0 71 = true := (@block_merge orForest 8 0 56 15 checked8At0 checked8At56)
theorem orTables : checkedTables orForest 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block orForest 0 0 0 = true)
  · exact (rfl : block orForest 1 0 0 = true)
  · exact (rfl : block orForest 2 0 0 = true)
  · exact (rfl : block orForest 3 0 0 = true)
  · exact (rfl : block orForest 4 0 0 = true)
  · exact (rfl : block orForest 5 0 0 = true)
  · exact (rfl : block orForest 6 0 0 = true)
  · exact (rfl : block orForest 7 0 0 = true)
  · exact allAt8
  · exact allAt9
  · exact allAt10
  · exact allAt11
  · exact allAt12

theorem noRun : Impossible (graphGoal 2431) 12 (vars 2431).toFinset :=
  root_index (g:=orForest) (before_sound _ sound255) orGeometry orTables
    (k:=12) (by decide) (i:=0) (by decide +kernel)

end Free383

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound383 : Lower (vars 2431) (graphGoal 2431) 13 :=
  augmentedGraph (k:=12) (m:=383) (hints:=12901687556) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 383) (by decide +kernel) (by decide +kernel) Free383.noRun

def entries383 := extendKnown entries255 13 [(2431,[]),(2495,[118,130,81])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound383 : Known entries383 := extendKnown_ok sound255 seededBound383 (by decide +kernel)
namespace Free479

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem noRun : Impossible (graphGoal 2527) 11 (vars 2527).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2527) (128,0,2399,0,11) _ (before_sound _ sound383) (by decide +kernel))
    [] (pool:=(vars (poolMask 2527 (128,0,2399,0,11)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Free479

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound479 : Lower (vars 2527) (graphGoal 2527) 12 :=
  augmentedGraph (k:=11) (m:=479) (hints:=13438558468) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 479) (by decide +kernel) (by decide +kernel) Free479.noRun

def entries479 := extendKnown entries383 12 [(2527,[]),(2557,[130,114,49,98,81,64])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound479 : Known entries479 := extendKnown_ok sound383 seededBound479 (by decide +kernel)
namespace Free503

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem noRun : Impossible (graphGoal 2551) 11 (vars 2551).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2551) (16,0,487,0,11) _ (before_sound _ sound479) (by decide +kernel))
    [] (pool:=(vars (poolMask 2551 (16,0,487,0,11)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Free503

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound503 : Lower (vars 2551) (graphGoal 2551) 12 :=
  augmentedGraph (k:=11) (m:=503) (hints:=22028484868) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 503) (by decide +kernel) (by decide +kernel) Free503.noRun

def entries503 := extendKnown entries479 12 [(2551,[])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound503 : Known entries503 := extendKnown_ok sound479 seededBound503 (by decide +kernel)
-- Setting inputs zero and four to false makes three live wires
-- constant. The remaining seven-vertex graph needs eleven gates. The
-- nine-vertex search below combines this restriction with the preceding
-- induced-graph bounds and the automorphisms of the target.

namespace Free511

def liveData14 (i : Nat) : Nat := 0x6e160280a02260f02c8ffd40

def moveIndex14 (i : Nat) : Nat := 0x62de32dd079fc4211200000ace2800007ba180139750039b51b9bc2ca530ac9cd023b300000400

def liveData13 (i : Nat) : Nat := 0x8b20a8088a13a16301f37459010151e09d0b208b8b20a8146e9303e859137415028b21f42c69ba2c8140a9303e858e044dd164142707d0b1e2c8f205a281302a4c8f8164cdd1640b01015264790b200a9ba2c808168f01f139137459054051e09d0b1c0a9ba2c814160f81f930454cdd1640a0e4981f02c22a26e8b20a8164c0fa16383f3745902c780b4991f03c9866f79c4b485faac9299fe3525787f8aa0be003ffb04a07ff4c940ffec0a81ffd51503ffa62a07ff48540bfec9a81fde33502ffb24a07fb88940bfec8a81fbd41503fec22a07fe4c140

def moveIndex13 (i : Nat) : Nat := 0xe02c89309624208252eca6585f60aba061427d854428ba4cf01ce064e2740473c91e83e70e9c1194100827006ae4bd8291109c0a2a1358a76183c063a485c9a383690d7c038830c117d0a0006c0001111c28c000000078437105e03182418321206213003ac85ce0dc021408b502fa09c0000c22385ed27660e202030290001403f081000040ad458ec3de11fb0d9620343e502b000000000003042b01a0002ca8391440340002c22e17810d3a1e9b84a83cd09521758334030807ac029308f84b602400034008028a055e195c0e2819228e00010175859d1038162495a8670001a090000102d426e00000346814200400020a7800000000003f29285af218c099038992db03da1cf809ff11a0f1a4ba00a8000a0e524054bb000032b220cd8b8585b82502089c9ce805a26de00ec427810926000b0c3f411a521561fec1a1070821124c54afd01f2287c5ad0abf047b10621de83c887dc02e05c7836e16a907f2019c02695a00c600eb01dc95b4c132474886b138d023a4a4c314016106e60760a128002047a1d9ca6b86f70922580403e06a9042615f8800060c2c201064048008b04bc14e4870712a51012801abe2608a000a241804e00083001484d0614f00020056a00103122c14a800278300421c98d085809008080b6080438a26004180200008

def liveData12 (i : Nat) : Nat := (if i < 1 then 0xb1d0566ec588590fa4e87c7cdd8b30524e87c1a70b1f3762cc0b8f32663e03e70159bb1663cc7c9380f9e0fe6ec598f20563e49d05900533764ccb39391f01f381fcdd9332ce4e47d058f07f3764ccb305b2723e83c8b1a2c2caf96ba9ad32b10ab26a77a8969b2a4fe903a34a896a0ba7bb9dfe72d9b9a6aa9886598954650a925e4668fce3758c8e2bb89a6222876e17e84b20cf822202b7ee1f5b7c51eb778e5dbb7579ce07265c526fa9b986d19ad36a05a0366f1980648d8c661a58175ebd7525ba968258c15d355d9524531d47550b93e74ead3644c1d29449351f0462112b433905b4024fb73dc0f1e3b5ce903924e023694d4833acc833098bc92db0b252b78a9729149fe26b096523f48b621648121f5878f1d206f61abc66818845cf162053613bc49211003e30e703550be02a6095020206c015e04040af0174000fffaa982503ffda360940fff68582503ffda84c940fff69532503ffda14c940fff69581503ffda360540fff68981503ffd5260540fff4c981503ffeaa54540fff68d51503ffda254540fff60951503ffd3254540fffaa931503ffda84c540fff69531503ffda24c540fff60931503ffd524c540fff6a121503ffda548540fff61521503ffda348540fff60d21503ffd5348540bffaa9825037fda960940ff78cd82502ffeaa4c940dff6a532502ffda84c940dff66132503fed824c940ffb60e225037fd8364540dff609915037fd3264540bffaa9815037fda960540dff655815037fd9360540ff78cd815037fd9260540eff60981503fee2260540bffaa9515037fda954540fef691515037fd9354540ff78cd515037fd9254540ffb88951503ff58154540fef60d41503fbd8250540fef54941503fbd3250540bffaa9315037fda94c540bff6a1315037fd984c540effa2131502ffda54c540dff65531503fbd544c540dff64931503fdd324c540ffb88931503ff5814c540bffaa9215037fda948540bff6a1215037fd9848540effa2121502ffda548540dff65521503fbd5448540bff68d215037fd9348540ff78cd21503ff53148540ffd61611503ff58384540ffd54e11503ff58284540ffd54a11503ff53284540ffe68930503ff9824c140ffe68530503ff9814c140ffe54530503ff9214c1409ffaa9935027feaa64940df78cd925027fda960940dfb66222503bee8888940ff38ce225027feaa64540cffa21915037de3364540dfb889915027fda9605409ff6a551502fbeaa50540def66141503bbe8850540bef69541503f9e3350540def64941503fae22505409ff6a531503fb5414c5409ff6a5215037f59884540efda22115037f59584540fdd95611503fb55484540dfd64e11503fd63384540dfd64a11503fe62284540bfeaa9305037f9924c140ffa88930503fb9414c140ff64c530503ff2114c140 else (if i < 2 then 0x8590090548a89d858f9bb1663cc7d8582a983ae2cc798f80f85530750278b30140a51513b0b2007e02c580a62728a03e70eb8b30104e81414545616422c40482a2728ac2c60e621f266594dd93a1f01f40130301d71641680507d4524e88aa02203f3762c49d0f83481f460ac9996727616116687c8b10564cc9c8585308c401306a82a45e0542d1b92ca1f87c981604c1048bc9996509c6e4159390b43e581c8590163720ac990fb0b200981941422f1640242c87d2748a08cbc5982a1f61649c118d0b20546e49d0fb0b1809805cdc0c30501b8b30fb0b2702e6ec150f90b4590d47c0b9b90e43e8b2858351c180130419bb02a1687c87a2c84a546e80a8280e45987d858e0c00ca0a0279b902a1c42d0fa2c8465c6e8148161f459c2c6c158594545908c545905937605c9821e1f01f4013c5900a0e28a82c93a22a12ee6e4590721f41649d11500460b66ec5893a1f01f381300b9bb1640ac980461f6164e6ec998145065987c1a00fa009805c589b80dc0ac990fb0b240600a0539332cc02c9ca280fa6164054dd02b2643ec2c70260173701b8149661f61640350198173702987c9640fa202e6e42c0a61f25903e702206f3762c87c9383481f466ec580461f61649c118f1ba1640a49d0fb0b1b1664c81585945046366ec5982b0b0692a0acdd8b0072160d260278b00be0a4dd13a1f61640080ec0440e62c80485a2728a054a8590293744e87d858c04c3760a1090161f259c2c806a0440e66e80a85a1f259054906a0733740542d0f92c82a4013cdc05f1620a89d0fb0b20040130419bb1620a42d13a1f02a501c8dd0b10544e87d858f9bb1603e41585a270463a0a40a9ba1f259c2c64588160120ac98a2b0b1d372054150f92ce16322c4150092728ac2c64dc82902c3e4b3858c9b91620a87c93b0b1916202c79a2a0b24e09207d007f16602814a292741613084dc8172665982c28d1f01f428b83f9332ca6e82d9391f41e481fcdd8160b23e4b307825200fe6ec590592741e47c0a919bb1660504180b2663c03e8cdd8b30163c89c07cd8f31668ac7d1380f980562cc0522a2701f320ac598090b21f515138f8b30560289ca2b0b1b3762cc0482b1e44ec2c7cdd9332ce4e038114d02b1660580505a0fe4c51511539bb26659c9d0f80f9a0566ec5905a1f41f49d11519332cc6ec9d0f80f9b376058b30f80f973764ccb39380e045364ccb29bb2743e03e6c599313741cc9d0fa0b1f376050009661f01f366ec999672743e03e6cdd8b12743e0d207cd9bb1624e87d07034c163e6ec999672743e03e642d9bb26659c9c0f80f9f3762c89d0f83481f320ac599313721cc9c85a1f231660ac0a9bb2643ec2c74159bb02a164b287e1f260466ec158152cc3ec2c6cdd8150e43e4b2858d9bb2665942682b2721687c8cdd8b302a0ac990fb0 else 0x22c40513a456160ea641513a456160ea5c5982836c4e47d858c07145051c2c1d4a0700226e4048b31e6160aa80388fb0b051054542d0f905259118118c85b2643e4b2828460463a1649d0f905259118118e06c4208b0bb82902c6e4b30fb0b280d88b03803f1646e41493a1f61650020600d4178462e1641429c23130b60a49c11853940d82f0e182902a6e8b30fb0b240d82f01f9b80e42c41493a1f616500c03007010846281cc9985a0528acb2118e0730b66e81496423180e2050220a42314088750380403d81bc589ba0524e87d85980cc0881c0201773701b45902a1f24ec2cc42c9b91620a0d2118c8593720a45814023180b8330109b80888180a9661f61652160100a423100b81c4580213708141513a1f61650170660c80e008cdc8b10543e89d8596073166020eb22a276163a0a10182b0162c89d2290b06c481c))

def moveIndex12 (i : Nat) : Nat := (if i < 1 then 0x99a5a9b24e800018440000000b6000000000000000000000183a60000b020000020372e11f9095305140001a1a4723f60779c0648015b0a10000383b400ab00005834b021c000032672965840e004d200000000303f2000062ca086d780cc000080bb48316b13464e2f28779057028ec2150000015adc9c344a110898049bc1e400f7b0d4d916509cfa4dee047c884a40da000080836063bc27a651c02def8808c1ea0000000069500829985e972a9607fa032420972215c84cb3c1660f6330880000000060ba507d315fe4ab26136000021634491f01ccc0fc00001003ea53a8005800000867c5959028085b4c82f6028a2c8115cc000000000000501968439e0c3a093e82c1442d85ac0084403a400ce000010de9804202a9a01ad055011273041c41000004927e03da620aa073f12954843a0aff006f078e82dc9832000051180c16c4124402e601fac1a9441210dd815dc0001049780d6387240001658e62cbf9821c1c825e690b00000380c400007017990780331413af080806d0000000000000383b5880b8089e0cb392d4822a80181cb1e00ce8011808d82237840dcadc044200003876340b341df12e89087f498cc201400c8036a82522520f0a58000242bf0024d079e8783c015621822f86068a4991c079b10f101cd4042e4dc106e00341823a84a070eb80003c224054ba094007e902df0123b26d1966b80ef41fc32c478452c233a01d22dc0841e89adc59342d8a0286088ec14e1022982fc026a2219b267b97568aa6e5e7b2152003c094fc17c4108891c54388a408f064e9152c335e14ae07a51540895d808502a570590407b60c15202182e54364c46b0000605e2f199a1d66028814fa8271a047706508629c35e808e601e39738831b41dc4291201f008be25cdc08e682e389240000500f30309c408c159d0f5a86648b8c0080825b184448909209590af117ffc10ec0c000002977c4a8ce0b3b069a0266c1a20000f2121061401c681f5c0ea808878412a1462251c946f423161c2045109201b150aa8493d0109000000180100050202070000271400120124190b0f0f01061a07008b02730c06000e09131422070f034c0c010700000109020b0d0d11004606010b000e010a0500111e030300010407010019020005021c2d21120f0002000258070100072309530609000b0501035b0500050b552d0000020c15000c0409010011022c150a02001a0806080f25010a02001e1413001b061300070112010f11011e000300000b16150101050007011e010503030000050105000f000404040209000300000005010004051900020301021321100019000004010200420102001304090500080000010701000c0023060000010010070a17032201030301030801000007753502000b0007000202001002250008020008010a18080500 else (if i < 2 then 0x848258c968249120f7011d0000000005050000010bac0000a0a7b031d4a8519cb5cb2318818039d91652117880d8aea45c9103708833ca34c20560b0e03fc83ba017270b821250034e40d70000191758921c0a5f20dc05fc8366a13420a0c92a5ca3e782e6280793a242b605d9929c812a1c30e44d5000028625c245440ea2f758355c20aa1e600a26043e03d4009cd0420874740ff400ea0e2c00e8838e00fd501f887a6497241d980cab17074858801422f52068cca68a001907cb16fd4bb9814d125c186844319a54dd2a1907228a1120fbde8c79750004f002e929e90500899b8006b21a605e982046517c066404580000416b022d80002f85f615170488060cc2b4e554503c6184249de1cb7f0625846dc35ac4d4d04ef87ce0af2047d4088585c74997209a9208913940000000080e7e01ec000060bb408bd97130063c5c39261915790c0f204de303580a9c02cc499f07c208384243a0cd7239306228428e0221046114418128602b53049906140b4004930ce60734719ec0b2a2e4301ca8382600c50fbe01524323c5aeb24d396e5c9676093c2ba016100131a43ac0d5182b5c0aea21bf00938483017d04c70103582f1cbc1e053d03a082c54200620f80fe891cc4041413750dfd086bc3e87c3270637808c43fe00e1d022083998427448ea21b605a3c8e1801b80526168800844498b30f6879c0a0e01f6d09da0738033a60d6a02740321c25aa425c08d20221434b80370024117d189b724aad21710699c0b7453592ac0000000000060b0d58827b8258e09fa0860922b805a021722aed042c4370000000e8692bc41c440cb92ed987a18959a01310abe050e43b6209b000019418000000006040f867c0000c169c2da8000000000000e018000000001659c225bd054f88cfe182f0410000000000000101dc901e407021790098000994267046d00853929a4396c0d8b100301c600f5e0dd52049170a0c32c04f70ca280a40b224005a08268397ba93221d9c18200010121a041b0bf5943d80bee5eb9255d054182ce00000000692b7c939806b403ec0790034181d400005858e08a16131907e30605025ce15cf0c9a90ca8362d96280a4a837e4a92a18b20d4684f9493ce0b4502f506db036f61c392277863c884d6190d29189173c30cc1e2221ae024a019d843740c2483a142e9e1090029281a8f944406ce045504bd4960e1e54086800008022a06812ad8000141e220040000580fb82ada1f12309a18774394e035a041f859ac1bd04cc82ddc038082abe148e021896e9433d460a003b705d6c00541ec90df0152300ada4feb054d123083e0e1d20231f028dca0b20b73cff104fd040e4025620e2871a82568461023248298819e25e8c075380260a7180fef0b2c64628a9f020d105a805cc82d560640000580d182b1e0db30bd8870340 else 0x5d50f080000c9360000d034d9074027881ae7309682b843e40482a0a950497c32ec55a30250882e02bba21090fdc110e41516453f234714f202efa075d08f592ca8272647b71040829c4bd8a4c40000203b8f144000070767028ac963e0eb702c106f10be5a537000000002c0de00000000087bd802f2046000011316800e00006001a82b3c2c40000e030803c240ab05bc0000103640000000090dd000d9410c0000e21c800000000402ce214780e7c8c5a17df031d02f4c09685ef2216983bdc871e08bf22f2137d4a2c000052ff491608300a19b30d))

def liveData11 (i : Nat) : Nat := (if i < 4 then (if i < 2 then (if i < 1 then 0x54a11503fbaa9aa508a81ff58cd5284540ffcb04a9422a05ff6bb4ca11503bfadca6508a817fd6e13284540efeb3099422a07bf6884ca11502ffadaa6508a81dfd6553284540feecaa99422a07fb5544ca11503ff2c126508a81ff96162284540ffcb0711422a07fe55388a11502ffd5db44982817feaed824c140bff374c1260a06ffaaa60930503bfcdcb0498281ffa6a2224c140bff576d0a60a07bfa88685305037fcd134298281ffa889a14c140bff576c0a60a05ff9ba605305037fd5530298281dfe649814c140f7f304c0a60a07fea2260530502ffd5daa2982817fe6e9514c140dff554a8a60a07fb9b454530503fecd9aa298281dfe649514c140ffd444a8a60a07ff18154530503fdcc128298281fee549414c140ffb57698a60a07fd9b84c530503fecd426298281ff66d5314c140ffb34a98a60a07fd9b24c530503fecd126298281ff6609314c140ffb2a498a60a05ffabb48530502ffcdd24298281bfeaa9214c140bff37090a60a077f99848530503dfd44242982817fe6d5214c140ff72a890a60a07fd95348530503ff8d442298281ffc696114c140ffe30b08a60a07ff1a284530503ff8c142298281ffc54a114c1408ffb7155324a047fdb5aa9925023fed8d54c92815fbaed9888940ef9b3119c44a07bce888ce225031ff55510c8a81cf7a223364540cfdd5511322a073ee8888991503be719c44c8a813bf6daaa60540cfdb5311302a047fcba649515033f6d4c44a8a81aefaaa8850540f73d1119a82a073be88649415037d755444a0a81deb6622250540f75d1111282a06fada588941503fc719c44a0a811ff2e9984c5408ff974c9262a06fb6aa50531503ddb4428298a81fe54c9414c540ff4c44a0a62a063fda9a2121502bfb5db3108a815fdaed9584540e7ed10cac22a057f5b961611502fdb5daa908a81ded6615484540f76d10aa422a057f6bb64e115039fb4432708a81ddd9559384540afeb72c1c22a057f5b954e11503f9aaa2a708a81df56623384540f7ad1119c22a077d5958ce11503fab2ac6708a81fe55523384540afed76c9422a073f68864a11503bbb2ab2508a81ded5519284540efac66c9422a057f5b960a11502bfadcaa508a815fd6e53284540efcb3111422a07be68888a11503bf2cac4508a81fd99562284540ff4aa911422a077e59388a11503fe319c4508a81bfaaaa224c140efd33111260a07bea8888930503ddd4428298281fea889414c140bfb57698a60a06fdaaa4c530503beccc26298281ef6a21314c140bfb36a98a60a07f99544c530503becc926298281ff2889314c140ffa30298a60a07fd131485305037f95542298281dfc662114c140f7e51108a60a07f725584530503fd8aa42298281ff454e114c140efe32508a60a07fe222845305023deda554c9a81fe4505314c140 else 0x81eefa213250540ff5b0499282a07fad83889415027fedc55498a813ff6d6aa4c5409ffb6555262a067feaa6a5315027ff5db5098a819ff6e5a84c540cffb52d4262a067feaa661315035ff5551098a81cff6a6884c5409ffd76d2a62a067fdb9695315033fed4b4a98a819ffaa9954c540cffb50caa62a073fe88655315037df552a898a81bef6a1544c540f77d10aa262a067fda9689315033ff5532498a819ff6a1924c540e7fd10c9262a067fda5649315027fe5d30498a819ff6a5824c540d7fb50c1262a067fda954931502fef5da6498a81bf7aa9324c540efbb7299262a077dda94c931503beecc26498a81ef7a21324c540efbb2a99262a07f9d544c931503fe6c126498a81bfbaaa224c540efdb5311262a06feda888931503bf6cc44498a81efba22224c540dfdb4b11262a077ed9588931503fd6aa44498a817fdaed814c540dfed54c0a62a077f5b960531503bfad4b0298a81bfd695814c540efeb2ac0a62a07fb55460531503bfac930298a81efd609814c540ffaa64c0a62a07fe62260531503fdb5528298a81fed6a1414c540ff6b4aa0a62a07fb5a250531503fdac128298a81fed549414c540affd76d4a42a04ffebb6a1215033fedcb5090a819ff6a5a848540affd76cc242a057fdba661215033ff5533090a81affaaa8848540e7fb5344242a04ffebb695215033fedcb4a90a819ff661a548540d7fd10d2a42a067fda969521502bff5db2a90a815ff6e99548540cffd54caa42a067fda8655215039ff4432a90a813ff6e98548540cffb52c2a42a05fbebb551215037df552a890a81bef6a15448540ef7b30aa242a07bbe88551215027ff5db4690a819ff6e5a348540cffb30d1a42a06bfe8868d215033fecab4690a81bef551a348540cffb52d1a42a057febb64d21502bfedd32690a819ffaa99348540cffb4ac9a42a04ffdba60d215027fedd2a690a815ff6e55348540fe7aa8a9a42a06fdeaa8cd21503beed4c6690a81bf76a23348540efbb3119a42a07bde888cd215037eed2c6690a81df76563348540ff3aa919a42a05ff6bb4c5215037fb5526290a81dfd6e53148540efeb5298a42a06ff5a84c521503bfacc26290a81efda213148540efeb2a98a42a07fb5544c521502ffb5db0b08a81dfd6e58584540efeb0ac9c22a05ff6bb60e11503bfadcb0708a81dfd6558384540ff6aa8c1c22a05ff6bb54e11503bfadcaa708a817fd6e15384540efeb30a9c22a07bf68854e11503fbac2aa708a81ff560d5384540ffab0b19c22a077f58564a11503bfac1b2508a81dfd54d9284540bfed76c1422a077f5b960a11503bfacab0508a81fdd9558284540ff6aa8c1422a077f59360a11503dfac1b0508a81ff58cd8284540bfed76a9422a077f5b954a11502ffadc2a508a81dfd6615284540f7ed10a9422a077f593) else (if i < 3 then 0x50caa42a06ffeaa61521503bfed4b0a90a81fef6a15448540effb4ac9a42a077fd8564d21502fff5db0690a81bff6e98348540dffd54c1a42a077fdb960d21503bfed4b0690a81bff6958348540effb2ac1a42a07fbd5460d21502fff5daa690a81bffaa95348540effb72a9a42a077fda954d21502ffedc2a690a81bff6a15348540effb30a9a42a07fdd8354d21503ffac2a6290a81ffe6c5824c140fff374c0a60a07ff9b560530503ffcd2b0298281ffe6c9814c140fff344c0a60a07ff95260530503ffcd92a298281ffe609514c140fff37090a60a07ff9a848530503ffcdaa4298281ffe695214c140fff30a90a60a04ffdb3aa9825027fed8d54c12815ffaeda960940cffd54d4b04a077dcb36a5825033fed4b46c1281bf7aaa3360940efbb5319b04a067fda9685825027ff5db50992819ff6e5a84c940cffb52d4264a067feaa661325033fed4b4a992817fbaed824c940dfdd54c1264a077edb960932503bf6d4b04992819ff6a5a14c940bfdd76c1c44a077edb960e22502bff5db06c8a815ffaed8264540cffb74c1322a067feaa609915039fec1b04c8a81df78cd8264540affd7699322a057fdb84c9915039ff44264c8a81dfb6093264540efdb0711322a057febb6a5815033fed4b4ac0a815ffaed9560540affb74cab02a067feaa655815033fed4b46c0a815ffaed9360540affb74c9b02a067feaa64d815037ef55466c0a81df76a63360540efbb2b19b02a067fda968981502bff5db24c0a815ff6e99260540cffd54c9302a077de3364981502dff5db04c0a81affaa98260540e7fb72c1302a073fda9609815039fecab04c0a81ef78cd8260540cffb52a9302a07bed8254981503df6c1264c0a81bfbaaa2260540efdb5311302a077ed9588981503fe719c44c0a813ff6ceaa545409ffb65552a2a057febb6a5515033ff55352a8a817efaeda454540df7d54d22a2a067fda968d515037ded2346a8a815ffaed9354540affb74c9aa2a067feaa64d515037ef55466a8a81df76a63354540ff3b4919aa2a067fda9689515037ded2344a8a815ffaed9254540affb74c92a2a067feaa64951503bded2324a8a81df78cd92545409ff974c12a2a057fdb9609515033fed4b04a8a81bfbaaa2254540efdb53112a2a077ed9888951503df744444a8a81feb6922254540ff9c67112a2a05ff6bb605515037fb55302a8a81dfd6e58154540efeb52c0aa2a07fb5a460551503bfac9b02a8a81ff58cd8154540efeb24c0aa2a07bf58260551503fbaa9302a8a81ff98898154540bf7d76c1a82a05fbebb609415037df55304a0a81def6e58250540df7b4ac1282a07bbd8360941503fcf19b04a0a817efaed5250540df7d54a9282a077bd9854941503ddf442a4a0a81fe78cd5250540ff5b04a9282a05fbebb4c941502fdedc264a0a else 0xfb0ca615ac1e1821b0325ffabef17bdaf525e0abae1741ae2a5beab7016b9ad3e5a12b3b166dac9a58e2b0c1603abd2573aadd159faada5562a9c1517aa1e53eaa6714b9a962525aa44145ba89a509aa0613f1a7a24f0a9d11369a6864c8a97e12dba59a4b1295812a1a52649fa9381267a4be495a921122da42647ca8f511cfa36a469a8cf1189a2f645ca8b2115ba29a451289b112da24a447288a1105a1e2438a86a10c5a16e428a84d108ba0ee41ba8301051a09240d281010119ffa3fd27f00fd79f923f027d90fa39f363e1a7bc0f6f9ece3d7a7ab0f4d9e8a3c927850ef59dda3b4a7650ea99d363a027390e579c7a38d270a0df99bd6372a6d80da19b0e35ca6ac0d499a5234226740ccd995a324a6390c51987a30726010bdb978e2eb25d20b7d96c62d6a59a0b1995e62baa56b0acd958a2ada5540a759486287250409e7939a26e24c9097d92ae24da48808ef9186228a447087390b2211241508158ff61f9a3e007998f0a1daa39f07238e061ba236a06ad8d1a19e232f06498c5e180a2ee05b58b2a15ea2aa05398a3213fa27204cf8952120a231044188360fea1f003b9873e0de21af034986460c2217a02d9857e0a921450269849e087210401e7838206520c001538242043207900d7817a028a047007380b200b20002fff5db42c1281bffaa9a160940dffb4ad0b04a06ffda3685825037fed8b50992817ffaeda54c940dffb50d2a64a077fd9869532503ff6dab0499281ffb695824c940ffdb62c1264a06ffda8685325037fed2b4299281ffb609a14c940effb64c1b22a077febb60991503bfedab04c8a81dff6cd8264540effb7099322a077fdb54c991503bfecab46c0a81dff655a260540effb26d1302a07bfebb60981503dfedab04c0a81eff6cd8260540dffd54a9302a077fda954981503bfec9aa4c0a817ffaed3260540dffb7499302a06ffeaa4c981503bfedca64c0a81dff6a53260540effb2a99302a077fd9368951502fff5db04a8a81bff6e98254540dffd54c12a2a077fdb960951503bfed4b04a8a81fef6918254540effb26c12a2a05ffebb4c9515037fedd264a8a81bffaa93254540effb72992a2a077fda94c951502ffedc264a8a81dff6613254540ff7b48992a2a07fed824c951503ffa99302a8a81fef6c98350540ff7d76c1282a07fbdb560941503fded9b04a0a81fef6e15250540ff7b66a9282a07fbd8354941503fdedc264a0a81fef6d53250540effb30d2a62a077fda865531503fded42a898a817ffaed824c540dffb74c1262a06ffeaa609315037fed2b0498a81dff655824c540ff7aa8c1262a07ff5b160931502fff5daa498a81bffaa9524c540effb52a9262a06ffda854931503bfecc2a498a81ffb609524c540ffbb7099262a07fddb54c931503ffaa930298a81dff661a548540effb)) else (if i < 6 then (if i < 5 then 0x31a2a07c9cdc013c5802307cc9c03e7a1664e83e81f253721662761f20f9685b9330f887c987c4384c0366ea05273a16a59c3e353761f52c83490f970f898087c6cdd87d4b243e4c3ea59a161f2661f11010f919ba82a817932858a930f8f4dd41540b42ccb387c6a6ee4c22cc3e06921f313761f52c83490f9585b0f896487c8cddc98c58c9d87c43e6273e4cc3ee16233761f32ca3490f968299670fb8588c2d87ccb243e4c3ea4e21f1b37516139d0b52761f1a9ba82a8168599670f8d40a42d87ccb243e5a6ea2ca4ec3e21f2d3711610552761f10f989ba8b30fa93887cb87d49c55243e466e62c60a616a4ec3e333752761f70b119b98b182985a93b0f8cc5949d87dc2c4c3e6596161b3731630530b52761f1982a93b0fb8589c7949c83e340aa4e68a41f252734560560b1393205a8fa07c9028c9d47d03e400ce4cc16a3e81e281072651f00f900300280bd9bb9328f826007d1c9947d82c3a3ec166590610982a0b737014d1f32c80f980440bc1ee8f99381b007cec9d47d82c381fe4c017e5968ac16098380ff1600b91f60b52701504c239328f907c7c98d1583c83e4c16e4c68ac1e260b32cd1f60f110528f996507c947ccb382c3a3ec1e64e41f260b51f32760f139bb8b38178f39338f802ce82dcddc99cb247dc9c03e7c6f38d13187e2e6c57b8a2312fe236c40387330d1e17ac2a384d308be0e2c173827303fe056c05b8012feddfb2bf137db2f9bdef6bd3b7972f19de0abbab7682eb5dd42ba3373c2e5ddc7ab8a37072df3dbbeb72b6db2da1db1ab5cb6af2d49da6ab49b68f2d09d9f6b3b366f2ccfd976b2cb6522c8fd8f6b1b36292c3dd846aff35f42bd9d78aaec35cb2b81d6b6acd35932b17d606aba356a2abfd556aa5b5442a73d4b2a9135182a15d402a7b34ec29c3d36aa6834c62977d2c6a5234972919d20aa3c346e28c7d166a2634422869d09ea0eb40d2805cfe29f733e127b3cf1a9dcb3a92737ce469c2337d26f1cdae9ac334e2681ccc2991b31f2635cc4298332f925e3cbb696eb2c72579cabe94fb298250fc9d2936b25d24abc90a91ab228243bc83690031ed23c5c73e8e431c42373c6b28ce318f2303c5de8b9b16f22c9c56a8a3b1432265c48a887b1082207c3e6877b0df21a3c31285d30b02145c262845b07e20e7c18e82e305820a7c12681cb02c203dc04680230001fe5bf7e7e92fcb1f8dbefe7ddafb71f5fbeae7d3af9a1f1fbe167b92f6e1ec7bd667a92f4e1e81bcb6794af191e17bbfa77baee71dc5bb567672ec71d6dbab274e2e981d15ba1a73cae691cb7b94671c2e2e1c41b8367032e021be3b7aa6f02dd01b79b6d66d42d981b27b61a6bcad691ac9b55e6a22d311a47b44e687ad0b1a01b3da671acdf19a3b3126572ca71945b262648ac8d190bb1fa63d2c7618e3b19262d2c4d187 else 0x2201307cc9d03e601801902b046200980b01d819d376270231d82b0f805c2b48c5846b5140d64076008084c4ea8a02a3116105220835901db8b11a40a88811c2c2008080980b025853823171380982a860ec03989d87c14e5813816c4e1f3710b52c835900230f89800a884dc8a00d63e6e03546902a251650b04704000e62703061f2100a04e020602c0c803814e08c501307ec4ec3e0882a01068582a40a8606acdd80a0394b387d42c768aa5902a1d0b0404c05805c0a880560cc2013011c4e08465968a02a3c09f0b0804c0d59bb0f99640a8d87ccb2c2c054401302b011066200461f627110015140ac19840401020568d20545013a0a02005e084a16c3e097c4e4809e275455050300231804c14e82811829ca0260104dd87d4b2054602d616c3e25902a280e70b08020203882d87c301121c140e60b0807105b13860224382616080104008205780a0d4302ba0a06a1b37627505023118b082b139a280a8b80a166ec4e83e02a262741f30b015109fb85840fc121322080a1939f0b08070246a43826160909f0b080702427c2c221c0d0b068283458121c616110993f4028c9cc87044144382213e161402b050884c8d6014742c121361611099104028e814243942c225de1615270484c85a93864264bb4b23a16a4c11099105270e814243942d4983a2c0808f0b0803c2427c2c201121c150b0484c85a93860224382a160b0b068282c2c16160b0b0702806407009c128a4058280c01304c0a25204a1a0f850290701ec160982c1c0a01802281f04a2c0fe0b0880807c0800d8903f82c222c056c1628b260511e02a825128f82815458c9d47c83e501064ea3ec1e260a51f080730509b8154128b8144dc0aa094402041f120e02e20b025130580bc1186814838c9c094481cc16160500bd2ce0b345160518b193a8fa07cb028cdd47ccb303e500c01c01702a220b33751f23004c1407c06028c128882cc5802e8c0130580a64c01801f098281480884c0e02807c06028c128a038147404130402a62c07ba3ec1664e360a1548150f0289b89481288404166e020a4e05aa3ec1e320552734501513028340a03a0f347ccb382c6414a3e65902a201cd0283dd1f32ce0b1b058381483e8403c0a0e0b050730285828c9c202c01b68ac4ee3e01c0ad019403771e00db2cf1f00e05400ca39bb1380739658f8064d89d51443e362cc4e68a46921f2d0562734570b139310711146cddc9985989d87d03e6a4e41c4451e1660560160b5273451b1bb0b293b0f907cbc59c14037c99c2c0de6c6e42ca4ec3e41f280981402d82405580c8181e8151bb1670f907cbc9883888a3c16e4cc3e81f233752761f40f929390711146cdd49d87c83e4a4ec3ec161b2ce1f60b20f9293b0f907c6108039c980860220ec609101c062a4e043019372641f40f8e85b9) else (if i < 7 then 0x411880320ed42c1320b0501607c07506c200a8410360c04c1f01d41b08039c2c28050b0510b51f0569313aa280b01978581d4c0f80ea0ce301362c075067200783b54572c815140541e296419c800a100508406050360d8b29b81b060260560220ce4075e16100e040631901d41a4220a05c0e987c03813808b49c70904180ad1d1652720e2229293b0b02870f9070a0ea838200f01829a02b0562d2771661f03ac34c0f981d6070585849c14387d038507541c100c045e1f03b04a023182328b02181a8980b87c4384c04c3e08606a1d2cf05727030245942301f28781a89c9985989c44187c43e6c3e08606a1810726502f2c82ba4598073858587c101c435c3e1c1f020b0b056900670f3164870118b87c41491815a4019a4e48b046200e445e1f0c1b820dc160ac020ad18455028568c06d85801824d9670f8d804105dc6ec3ea5941f280303e52ce1f70b140181c493a82b85b0f8c917c2c2c3e0a09a1ae1f0d07305b0f060260dc09dc2c094501301601b04a200c01a81b823100580dc1a8742c03006a301403001704a203ed0f0350c87029585811880260b8440094426e02f06a181073700e72702514073858500416160f0f5270550e16407010985829ca03202605e08c405920a02f0aa200980c80d825108580c00bc1188438105b01307504a201810553710e527025181c31670f907c8827c2c28020c012098b0582c2c1c1641c100104008207c1018580d4460aa6e06a1d3730b0230d82826c06d85b166a28d8581a6ec59046183e62c8230c29c11858581013c02069088200e527001830d4560b1904c280483c09282a0b05400659c3e41f260b52761f20f90073008587c03812b82c4ba5a4e0b3752761f20f9300a938580549c200666ec16c3ea5928089548150f05a9381830fa07cb82c1c1624ec3e81f260b0404c2a78580a8802602c0c814e054501301601b02a200b0118350c04c0580ec0ce9bb933028119187c1040d4362c034a8a06a203b40e045021f2c8151904f85840381013016c0a0a7046283c035081e28b01a8606a13e0861520545035405093a59c3e81f341ac0e0804e8582a40a8880b42d4b387d03e5a1608098158088351006607006c1b080328788b303808c581c080ca4f40e0231010c0cc0701378580a8c0e085980482a1401306010a4ec0a046273702ee1f52720f940282014102bc020981815d2704c0c03d8b0072939a280a8d804166ea4ec3e02a252761f30b0151001806c1e09399bb0fb858e023c2c201c0a09a0b61f0c045070582c1413e161008a0e0985820041002081f040605035118b29b81a860dd81414e08c4659093a8a41f231630b41f20f910701184020c9d81408c407864ea6e0462605040080300fc0a8903942ccb2d1408c521666e64c81c04628148088230d8b00440260f993a07cccdc else 0x2001023822c8004009c2c11a444e004e16a3e2002049d1f0ca2801024c60640080be0ba4004e16a59183c02f82a0e1b985801014484dcc2c0080a24420004a8a180b8020088c0138599646008022281c0751102937003038109380182b0600c0ea2006075100302f82a0c05c2470f8602e11d87c3017093c3e1b0b0370380c019062938600c0ea248ba4c03301b261f03e04a04d0279484c88104d0821769330f0e02205387812805650110044441a0b24580d8c0ac01804423c80e212987c00e421cc3c093029200b82f02e0c05c0bf8586009c2c8c8301b41302fe162017a09b0500303e141f40dc01c6c2c0fe05e012422007442002f2017f0b0148d058010944604805fc2c302b00602918088038178c05c0bf85a0708438108052302961601b190560b40e0e0b18584126120526e006192700309058018400d49c2c16a4e1043d2660b0c24c249d82c241c00c0781a1f00b8488d0fa85840eb82c0460f6400407b4441808a0b00800d901c105a07021006c1ecc8381260523029616120500703d8c0309740407498066020036402ba0504f1a09c0e52621e00d831180a5028976938211070c458108200607510030158288e02907193006c80bc02f0a0308e017441184180d70b0c0ac004068602e87c202b00e450180d015841844900ac1dc24c682c03a520301c02907a02b204980683b8c0ac0380a460ee1088a6301c0930291814b0b080680e38586071c2c052301100d03818158070088c05c06821f858802e064100888401c084029191600e60b0e0140a5858601c131814323e096c161a0b51f00b8d07ca2f058258947c12002e302ac0a018096212ee0a32651e1096405f058605f02d0398140f6523e40a0171e050128158d05893805c781405404a0564011c141627046816032f0b03a9b1381801d)))

def moveIndex11 (i : Nat) : Nat := 0x3cb0006071bc06644efe047216f21aa4b2e83510086420070b83c4c0b8055c33afe7705542ba052f88e1198a3698b148793133dae982ae9d430826747c65d11792bb62ebc0c98d903a6a04648fd9d9136f84f5839707a829366c7863097203cdc091c73f12b217ca259046c9f5e255a4400518858b3acc0630e6808fe21800038b98000000000000000000000102010480000e33ce78ecac8000000120c7442a0a721a865a4000000000000003c2911b830c7672f41be8755114c13683f002f618e815dc1330e8000182460b6b9ce43d7e06e8ab0000722200028408000000165ac00068dc00000002804d91200000002886f9bcb06022f7807e96a000147d082ff87802c3e20b47258dbe0d7e0874a10807212f01c48aba10993db002142050ea7007808ac68c1e2f1b0e2a836b5006504e9b5041410acc01c2052c87696800000001898b8c57383e0b800000009053a04b469700d414c0003473381a5201e624444e8cd43cec1f58d7d9a98191a56306570d07356a2800b8b12f8021c37d08380006260000000000000000000000029acb047e0740000843000083768ef39b2e13c00030aa400110642269c29a098834f87cb07a1174034dc15b87490bc61d840ae4ddb09d71a6c126049f1a8c35b61b48492ee5b07a613835f986990dc61c005d88f320cde222c37a95b2015c6604ce79d801186688c77d06c11ebe0f8c3d9f5c10d0e54b4f7e002a165621e0a54913e13fa16545138a1e2a01c1581d1844f163805eca9c0e0e018420cc12e03bd0bd843c41001a040c5c4dc42ee914b085230d422a8e5e20a61cc02451d2c3c082e7c1b096ca02cc38bc6b58bf92c9a1fcc4268d7d000e2e3009b82cb1c70653879200541dc63b4c57c9158116c07205af1e81182019602a58b012e0e2d2c9cae8d338960b4cc2e8c2c10ca257327909ce26d069405411da80b940780ce81be11e3c11a85b3877e0c96302025f94bc19e00cdca7784cc188c16d8522196c0f87afa8af2e50d3740144454e84a41d762ccc30c04fa15a614301cc8ce31e0641980fb03f230480d343a30ab91abc25232de1b90017253203b4038f0b5626f8b1a0c93a0a0400310300038303d60d9f484502020f079f00020e293108013f0602230016050004080001070c020100170108203d210900050200110b0813110b2800301f5204050606030000290a19070e0c060407010006242a050b291d2d070006001800050700020008030e0100030c030b07020014041408042a0000000002120d

def liveData10 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0x87fdc52e9924c540c3fcbaa21924c540a7f4ca649814c540fbc5824c9814c540ebb6aaa21414c540bf96cc4c9414c540ef96aa4c9414c540fb96884c9414c540ff85824c9414c540efa6aa889414c540fba688889414c54097bdc4aed934854097f5c5aed988454097f5c2aed9884540d3f6bba219584540dbb6bba215484540d3f6bba219384540d776bb955938454097f4cb6615384540df36bb5515384540fb36885515384540ff155460d5384540f3d6886563384540fb9688552338454097f5c8aed928454097f5c5aed9284540d3f6bba219284540d776bb9559284540f3b688551928454097f4cb54d9284540f3d6888cd9284540f756558cd9284540d775b995582845409df5c7aed5284540d3f5b9a215284540d3f5b9a213284540d775b99553284540b7e6cc6622284540b7e6cc6562284540f3e6886562284540b7e5c96162284540f765989562284540fb66889562284540bfa6cc5522284540f7a5985522284540fba6885522284540b7e6cc64e2284540f7665564e2284540b7e5c954e2284540ff255454e2284540f7c5988ce2284540fbc6888ce2284540f7c5958ce2284540ff46558ce2284540ff85548ce22845409fd9c3aed824c140ebeaaaa22224c1409ef9c6aed814c140afb8ca6d1514c140df99b46cd514c14097f8cb649514c140fbaa88889414c1409fd9c5aed314c140cfdabbaa9314c140d7dabb661314c140dbdabba21314c140ebdaaaa21314c1409fdacc6d5314c140cfdaaa6d5314c140df9abb551314c140fb9a88551314c140d7dabb649314c140f3da88649314c140d7d9b5649314c1409fd8cb609314c140dfcabb889314c140efcaaa889314c140f7c998889314c140fbca88889314c140dfc9b5889314c140ff8954889314c140bfd2cc605314c140dfd2bb605314c140efd2aa605314c140dfd1b5605314c140ff9154605314c140f7d192605314c140fbd182605314c140ffc222605314c140ff92bb505314c140ff91b8505314c140ff91b5505314c140ff91b2505314c140ff9182505314c140ff9152505314c140afb8ca551214c140ff195454d214c140bfd2cc4c5214c140dfd2bb4c5214c140efd2aa4c5214c140dfd1b84c5214c140f7d1984c5214c140fbd2884c5214c140ff91544c5214c140ebf2aaa22114c140ef72aa956114c140fbb288552114c140bfd2cc54e114c140efd2aa54e114c140f7d19854e114c140fbd28854e114c140ff518554e114c140f3f28864a114c140f7725564a114c140f7d15364a114c140ff515354a114c140efe2aa88a114c140f7e19888a114c140fbe28888a114c140ff625588a114c140ffa15488a114c140ffc15388a114c14097b5c4aed9384540df92bb505314c140fb9288505314c140ff8222505314c140afb0ca552114c140ff115454e114c140 else 0x252728a940c9e24df26012508ea46322890947d83c01d08dd465e32a1788b7c59a2bb147898c4a223211688a042c2110ff87b43d01d60e206c83261810be05a82b014609a04bc2060d704f019407200097fdc5aed826454097fdc3aed8264540c7febbaa9826454097fecc6e13264540c7febbaa99560540c7febbaa99360540b3fecc6558260540aefdc6aa95260540c7febb6a55260540aefdc6aa93260540f3ed956093260540a7fcca6e58254540c7febb6a58254540a7fcca6613254540b7f6cc64d8154540f3f5936098154540f775935498154540fbe5824c981545409fbdc5aed82505409fbdc3aed8250540cfbebb6958250540d7bebb6615250540fbad8360952505409fbecc6e1325054097fccb661a54c540a7fecc6a1954c540afbecc6a1544c540e3fda8655824c540ebbda8551824c5409dfdc7aed524c540afedc2aa9524c540c7febb6a5524c540afecca609524c540e7eda9609524c540ebeda8609524c540f7cd95609324c540ff8d54609324c540ffc5c1609324c540f3f595609814c540fbb554609814c540fbe582549814c540f7d5954c9814c540ff95544c9814c540bfb6cc609414c540bfb6cc549414c540ffa582549414c540ff95c84c9414c540ff95c54c9414c5408ffdc3aeda84854097fdc5aed98485408ffdc3aeda548540a7fecc6a19548540c7febb6a19548540afbecc6a15448540a7fecc6959348540c7febb6959348540a7fdca6159348540c7fdba6558348540cfbdba5518348540c7fdb96a1534854097fccb6615348540ef3da85515348540ff1d5460d5348540e7f5a86553148540efb5a85513148540d7fabb649814c140fbe982549814c140dfb9b46c9514c140ffb1b4605514c140f7f192605514c140fbf182605514c140ff7152605514c140bfbacc609414c140bfbacc549414c140ffa982549414c140ff99b8551314c140ff9954609314c140bfdacc549314c140f7d998549314c140ffc982549314c140ffd152605314c1409ffacc6e1214c1409ffacc6d5214c140d7f9986d5214c1409ff9cb615214c140dfb9b8551214c140dfdabb54d214c140dfd9b854d214c140f7d99854d214c140ffd1854c5214c14097ddc3aeda96094097dccb6a6336094097edc5aed988894097edc1aed9888940e3eeaaa222264540f3ce888ce2264540a6fdc6aa9956054097bdc4aed9360540a6fdc6aa99360540aeddc6aaa336054097f5c1aed9260540a6fdc6aa99260540aeedc6aaa226054097f9c0aeda95454097bdc4aed935454087fdc82e9925454087fdc32e99254540c7dcba8cd9254540a7ecca6622254540e3eda9a222254540a7f4ca6498154540fb658254981545409dbdc7aed5250540ebaeaaa222250540ebae886962250540fb8e888ce225054087fdc52e9984c54087fdc82e9924c540) else (if i < 3 then 0x2620098060403500988040013160083a16d26080260401685820018104c00c07c2004c00820148010582c08000e0b040201e0b06804100804126103c1070401301a90ec601300b90ec68050a0140362e0b074b210098040405d081c24582002840e16080182000d8403610006c221603d88062c0a8582a1602a8801c01d101d801020098058401301a90ec603501e8802e43b1004c04044b180800b8200980808c8301a80f440170220807409210004010261e04001c0807002e2a0507828192cb058522c60b005c722c00d88036100d840f601016050262cc0a0947c101484080a40e028c607b0828c3c1411d8074601ce0a092c607660549307c14126011c6a3ca0f08052101928f040290800e80581003820130804c2006967415a4e23793c99c2ce2770f84165f2668b349c46f200ec3c8a021088dfa4e0230c07610178118420b02e0128609b04e880500981087020302098800020390118600605381187c3e118f05860a00078041042829c400a03e024c606205388018103e907008c3327001808c300070201c08070200932760fb42d01c2801c3ee27004860130804c20000001c080001c082c2c100984026100245921610064200282820310a93020000000000031606c2c1000000000070b0403a0751004dfc161012683c0611b05805e046181c403802f0159302813160603e180540704040f85014140504038100e06038180e0403202f03d8c06601c0110c081f0a029038204028201c08808220208808208404c09c5923e40f8d0380981026022020803000602a19059d140630231082c0a20230c0220981028c0380981804647c098727407ca0012e8f8cb202a20808220208808200a03d8118640a014826062020c8f8054200282810107c241c0820141a050681412051070480a0818141e0a07828160a041e4ce1f082c7e4c91f407c7416f263a2a03e4a0b48f9c9d01f268f88c041f1b058cb3a3e20f92c69615afb575eb71599ac3d5a2a93537a9953e69b54bba54d29293f49aa4451da8c9452a2050ba81f3e39dbce9670d3749b14d0e6633129804bee5d32d79694b0255d2a994bc9e24e7261927c8c24231f28e9c69e31116989ec47a1e50d385a42560ed06482fc13605d01c8053fadf7efa07c73df1ebaf4b7963c69e10f0376bbb15d66e8772db8bdc06de46e936cdb42d9c6beb5adab2d476a134f5a08cbe642b1cd8a8c2860b2fdd796bac5c6aded6b8b57595abfd5a6ace55e2aa9516a5f52028b94049d64e8a6fd35a99b4aaa54129691f486a3ed1ec8f1476239d1aa8d0465a2e51688a244821f90f287442aa10d07c839413a0550067fe3fc9fd0fde7ea3f29f80fb67d63e21ec8f5a7a83d19e78f327943c79e28ef07593aa1cd4e126dd3521a48d0066e3279928c7062630a1808be05de2e61680ae856f2ae94f8a7 else 0x1300c08030075100600))

def moveIndex10 (i : Nat) : Nat := 0x380a4bf02420c014d02325bd308001bc80100005e7483f61c111b0784420003310002825216e0d000383640af028000889814611099102a20c200d9490ab44380be00eccb4190000000000a13e03082ec08c408d0a175cb4056204413d04f40e512e83745101db07b01e04dc20e04a15c07c708213a2010082013432cb201143

def liveData9 (i : Nat) : Nat := 0xd0f03c16041a010400006c20d1303a0504c16c9645916182c2000361e0503c0a040000036101c58168f0200e0400000000000000000db6c75999c3606dd69b2546993993415c8df662e54ca14e25d087f361648c411e0dc642d1408c3c190a03c14050061bfaedc6aa99560540a3deea57755326c0a8186febb71aaa64d815028bfbaf5db52a9302a04ded752cc64d8154540f9b2c9b04a9302a8a8155bdd7aed98549415028bfbaf5db52a9262a07cf1655824c9814c540fdc2aa3049930298a813db5d7b3152505315028f7ba95db4ac9a42a055be75abb649814c140a7dc6d368d92a2982816fb0da6d18154530502afe1b6c9302a8a60a07ed860952605514c1409fcce9d98c1282982813db9d7b3152505305027bb3af662a498a60a057f236d82549314c140fdc8aa304c0a6298281fbc182549814c530502ff25baa928298a60a07fe060952505314c140ef8cdc2a8a9a4298281df91b85513148530502a76ba95dd10c9c22a055cd752bb95593845409bd2ea598c9c4508a814f98da6d1b354530503b725774428298a60a077e0aee22505314c140fdc144444a0a6298281abb0caa2154845305026fa1b8cc2a708a60a06fc4b315454e114c140fd89442a8a9c229828137d0dc54d9284530502df41b4aa44508a60a07fc05515388a114c140

def moveIndex9 (i : Nat) : Nat := 0x1c1

def liveData8 (i : Nat) : Nat := 0x28a1af792bb71aaa64d815027d91e7b7552505314c140

def liveLevels : Nat → Packing
  | 14 => (1,1,8,0,0,0,0,liveData14)
  | 13 => (14,2,8,0,0,11,0,liveData13)
  | 12 => (134,3,8,0,0,14,0,liveData12)
  | 11 => (546,4,8,0,0,15,0,liveData11)
  | 10 => (246,5,8,0,0,13,0,liveData10)
  | 9 => (41,6,8,0,0,9,0,liveData9)
  | 8 => (2,7,8,0,0,3,0,liveData8)
  | _ => emptyPacking

def liveIndex : Nat → Nat → Option (Nat × Nat)
  | 14 => lookupWord 10 29 5 9 4 1 moveIndex14
  | 13 => lookupWord 69 226 7 15 8 3 moveIndex13
  | 12 => lookupWord 290 929 8 17 10 3 moveIndex12
  | 11 => lookupWord 128 418 8 15 8 3 moveIndex11
  | 10 => lookupWord 21 69 6 13 6 3 moveIndex10
  | 9 => lookupWord 1 3 0 5 1 0 moveIndex9
  | _ => fun _ => none

def orSamples : Array (Bits × Bits) := #[(0x112d300201824880135041e39031e0327,0x102d300220d04880181400a19800480a2),(0x9c10018c606014e64e0261c1fee8043f,0x9c00018d22a000f65ea2200036285115),(0xe38630fc4823000be5861f0cf004d8,0x43ae72dd4801000004864b49d506c8),(0x10f0400008780c4384c19f81e3001f8e0,0x1040410000084843acd4978149002e921),(0x100807c0f810f840701e00603f01ff00,0x100827c1f2107044309601606f99165c),(0x200c07ff001f007f801fff803ffe0000,0xc22c500090048001ff5847ffa2740),(0x1c00ff800001fff80001fffffc0000000,0x1400db800001fff00805ddfffc004a240),(0x1fff00000001fffffffe0000000000000,0x1ffb000000296feb7ffe000008000c015),(0x1ffffffffffe000000000000000000000,0xbbf2453aff600001208000000001009e)]

def orSymmetries : Array (List Nat) := #[[],[81,130,118],[16,82,131,100],[16,32,48,128,100,80,116],[32,83,116],[32,49,128,81,116,100],[48,33,133,118],[48,129,82],[80,16,33,50,116,131,100],[80,129,50,116],[128,49,100],[128,81,32,49,100,116]]

def orCols : IndexTree ColumnInfo := (.fork 87 (.fork 43 (.fork 21 (.fork 10 (.fork 5 (.fork 2 (.leaf [(1,0,510,0,12),(0,2,440,69,8)]) (.leaf [(2,0,2557,0,12),(1,2,440,68,7),(0,4,2417,138,8)])) (.fork 2 (.leaf [(4,0,2555,0,12),(2,4,2417,136,7)]) (.leaf [(4,2,440,65,7),(6,0,2553,0,9),(5,2,440,64,6)]))) (.fork 5 (.fork 2 (.leaf [(8,0,2551,0,12),(9,0,486,0,8)]) (.leaf [(10,0,2549,0,8),(4,8,227,272,7),(8,4,2417,130,7)])) (.fork 3 (.leaf [(12,0,2547,0,9),(10,4,2417,128,6),(14,0,2545,0,7)]) (.leaf [(15,0,480,0,4),(0,16,486,9,10),(16,0,495,0,13)])))) (.fork 11 (.fork 5 (.fork 2 (.leaf [(1,16,486,8,9),(17,0,494,0,11)]) (.leaf [(17,2,424,68,6),(19,0,492,0,8),(21,0,490,0,7)])) (.fork 3 (.leaf [(6,16,480,9,6),(21,2,424,64,5),(8,16,486,1,9)]) (.leaf [(16,8,227,260,7),(24,0,487,0,11),(9,16,486,0,8)]))) (.fork 5 (.fork 2 (.leaf [(25,0,486,0,8),(10,16,484,1,6)]) (.leaf [(11,16,484,0,5),(27,0,484,0,5),(12,16,482,1,6)])) (.fork 3 (.leaf [(20,8,227,256,6),(24,4,353,130,6),(13,16,482,0,5)]) (.leaf [(29,0,482,0,5),(14,16,480,1,5),(15,16,480,0,4)]))))) (.fork 22 (.fork 11 (.fork 5 (.fork 2 (.leaf [(31,0,480,0,4),(32,0,2527,0,12)]) (.leaf [(1,32,94,384,7),(32,1,460,18,7),(34,1,460,16,6)])) (.fork 3 (.leaf [(35,0,476,0,7),(36,0,2395,0,8),(40,0,2519,0,8)]) (.leaf [(17,32,78,384,6),(48,1,460,2,6),(49,0,462,0,8)]))) (.fork 5 (.fork 2 (.leaf [(50,1,460,0,5),(51,0,460,0,5)]) (.leaf [(40,16,454,1,6),(41,16,454,0,5),(57,0,454,0,5)])) (.fork 3 (.leaf [(0,64,2237,258,10),(64,0,2495,0,13),(64,1,396,50,7)]) (.leaf [(66,0,2493,0,11),(65,2,440,4,6),(64,4,2353,138,7)])))) (.fork 11 (.fork 5 (.fork 2 (.leaf [(70,0,2489,0,8),(69,2,440,0,5)]) (.leaf [(74,0,2485,0,7),(81,0,430,0,8),(83,0,428,0,7)])) (.fork 3 (.leaf [(85,2,424,0,4),(89,0,422,0,5),(98,0,2461,0,7)]) (.leaf [(98,1,396,16,5),(114,1,396,0,4),(0,128,2395,36,10)]))) (.fork 5 (.fork 2 (.leaf [(128,0,2431,0,13),(4,128,2395,32,9)]) (.leaf [(132,0,2427,0,11),(132,2,312,65,6),(134,0,2425,0,8)])) (.fork 3 (.leaf [(140,0,2419,0,8),(144,0,367,0,11),(145,0,366,0,8)]) (.leaf [(140,16,354,1,5),(156,0,355,0,7),(141,16,354,0,4)])))))) (.fork 43 (.fork 21 (.fork 10 (.fork 5 (.fork 2 (.leaf [(157,0,354,0,4),(154,4,353,0,4)]) (.leaf [(160,0,2399,0,11),(160,1,332,18,6),(162,0,2397,0,7)])) (.fork 2 (.leaf [(162,1,332,16,5),(36,128,2395,0,8)]) (.leaf [(38,128,2393,0,5),(44,128,2387,0,5),(177,0,334,0,7)]))) (.fork 5 (.fork 2 (.leaf [(178,1,332,0,4),(53,128,330,0,4)]) (.leaf [(169,16,326,0,4),(192,0,2367,0,11),(194,0,2365,0,8)])) (.fork 3 (.leaf [(193,2,312,4,5),(194,4,2353,8,5),(196,2,312,1,5)]) (.leaf [(198,0,2361,0,7),(197,2,312,0,4),(200,4,2353,2,5)])))) (.fork 11 (.fork 5 (.fork 2 (.leaf [(202,4,2353,0,4),(0,256,2199,104,8)]) (.leaf [(256,0,2303,0,12),(258,0,2237,0,8),(260,0,2299,0,8)])) (.fork 3 (.leaf [(8,256,2199,96,7),(256,8,227,20,7),(264,0,2295,0,9)]) (.leaf [(260,8,227,16,6),(268,0,2291,0,7),(273,0,238,0,7)]))) (.fork 5 (.fork 2 (.leaf [(264,16,230,1,6),(272,8,227,4,6)]) (.leaf [(265,16,230,0,5),(281,0,230,0,5),(276,8,227,0,5)])) (.fork 3 (.leaf [(32,256,2199,72,7),(256,32,94,129,7),(288,0,2271,0,9)]) (.leaf [(257,32,94,128,6),(40,256,2199,64,6),(296,0,2263,0,7)]))))) (.fork 22 (.fork 11 (.fork 5 (.fork 2 (.leaf [(48,256,135,72,6),(288,16,198,9,6)]) (.leaf [(273,32,78,128,5),(305,0,206,0,5),(56,256,135,64,5)])) (.fork 3 (.leaf [(296,16,198,1,5),(297,16,198,0,4),(313,0,198,0,4)]) (.leaf [(320,0,2239,0,11),(258,64,2237,0,8),(322,0,2237,0,8)]))) (.fork 5 (.fork 2 (.leaf [(324,0,2235,0,7),(262,64,2233,0,5)]) (.leaf [(320,8,163,20,6),(328,0,2231,0,8),(266,64,2229,0,5)])) (.fork 3 (.leaf [(324,8,163,16,5),(270,64,2225,0,4),(275,64,172,0,4)]) (.leaf [(339,0,172,0,4),(336,8,163,4,5),(329,16,166,0,4)])))) (.fork 11 (.fork 5 (.fork 2 (.leaf [(340,8,163,0,4),(96,256,2199,8,6)]) (.leaf [(352,0,2207,0,8),(291,64,156,0,4),(104,256,2199,0,5)])) (.fork 3 (.leaf [(120,256,135,0,4),(384,0,2175,0,9),(384,8,99,20,6)]) (.leaf [(388,8,99,16,5),(396,0,2163,0,5),(400,8,99,4,5)]))) (.fork 5 (.fork 2 (.leaf [(404,8,99,0,4),(416,0,2143,0,8)]) (.leaf [(385,32,94,0,5),(168,256,2071,64,5),(401,32,78,0,4)])) (.fork 3 (.leaf [(448,32,30,1,5),(480,0,2079,0,7),(449,32,30,0,4)]) (.leaf [(482,0,2077,0,4),(356,128,2075,0,4),(232,256,2071,0,4)])))))))

def orForest : Forest := ⟨2559,14,fun j => orSamples[j]?.getD (0,0),orCols,orSymmetries,liveLevels,liveIndex⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem orGeometry : graphValid orForest (boundsBefore entries503) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=5) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked14At0 : block orForest 14 0 1 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked13At0 : block orForest 13 0 8 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked13At8 : block orForest 13 8 6 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked12At0 : block orForest 12 0 38 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked12At38 : block orForest 12 38 56 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked12At94 : block orForest 12 94 12 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked12At106 : block orForest 12 106 28 = true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked11At0 : block orForest 11 0 2 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked11At2 : block orForest 11 2 56 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked11At58 : block orForest 11 58 30 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked11At88 : block orForest 11 88 56 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked11At144 : block orForest 11 144 56 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked11At200 : block orForest 11 200 56 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked11At256 : block orForest 11 256 56 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked11At312 : block orForest 11 312 56 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked11At368 : block orForest 11 368 56 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked11At424 : block orForest 11 424 3 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked11At427 : block orForest 11 427 56 = true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked11At483 : block orForest 11 483 56 = true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked11At539 : block orForest 11 539 7 = true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked10At0 : block orForest 10 0 6 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked10At6 : block orForest 10 6 56 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked10At62 : block orForest 10 62 56 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked10At118 : block orForest 10 118 38 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked10At156 : block orForest 10 156 56 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked10At212 : block orForest 10 212 34 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked9At0 : block orForest 9 0 14 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked9At14 : block orForest 9 14 27 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked8At0 : block orForest 8 0 2 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

theorem allAt14 : block orForest 14 0 1 = true := checked14At0
theorem allAt13 : block orForest 13 0 14 = true := (@block_merge orForest 13 0 8 6 checked13At0 checked13At8)
theorem allAt12 : block orForest 12 0 134 = true := (@block_merge orForest 12 0 94 40 (@block_merge orForest 12 0 38 56 checked12At0 checked12At38) (@block_merge orForest 12 94 12 28 checked12At94 checked12At106))
theorem allAt11 : block orForest 11 0 546 = true := (@block_merge orForest 11 0 256 290 (@block_merge orForest 11 0 88 168 (@block_merge orForest 11 0 2 86 checked11At0 (@block_merge orForest 11 2 56 30 checked11At2 checked11At58)) (@block_merge orForest 11 88 56 112 checked11At88 (@block_merge orForest 11 144 56 56 checked11At144 checked11At200))) (@block_merge orForest 11 256 168 122 (@block_merge orForest 11 256 56 112 checked11At256 (@block_merge orForest 11 312 56 56 checked11At312 checked11At368)) (@block_merge orForest 11 424 59 63 (@block_merge orForest 11 424 3 56 checked11At424 checked11At427) (@block_merge orForest 11 483 56 7 checked11At483 checked11At539))))
theorem allAt10 : block orForest 10 0 246 = true := (@block_merge orForest 10 0 118 128 (@block_merge orForest 10 0 6 112 checked10At0 (@block_merge orForest 10 6 56 56 checked10At6 checked10At62)) (@block_merge orForest 10 118 38 90 checked10At118 (@block_merge orForest 10 156 56 34 checked10At156 checked10At212)))
theorem allAt9 : block orForest 9 0 41 = true := (@block_merge orForest 9 0 14 27 checked9At0 checked9At14)
theorem allAt8 : block orForest 8 0 2 = true := checked8At0
theorem orTables : checkedTables orForest 14 := by
  intro k hk
  interval_cases k
  · exact (rfl : block orForest 0 0 0 = true)
  · exact (rfl : block orForest 1 0 0 = true)
  · exact (rfl : block orForest 2 0 0 = true)
  · exact (rfl : block orForest 3 0 0 = true)
  · exact (rfl : block orForest 4 0 0 = true)
  · exact (rfl : block orForest 5 0 0 = true)
  · exact (rfl : block orForest 6 0 0 = true)
  · exact (rfl : block orForest 7 0 0 = true)
  · exact allAt8
  · exact allAt9
  · exact allAt10
  · exact allAt11
  · exact allAt12
  · exact allAt13
  · exact allAt14

theorem noRun : Impossible (graphGoal 2559) 14 (vars 2559).toFinset :=
  root_index (g:=orForest) (before_sound _ sound503) orGeometry orTables
    (k:=14) (by decide) (i:=0) (by decide +kernel)

end Free511
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem liveSeedImpossible : Impossible graph 14 (inputs++[orSeed]).toFinset := by
  have target : graphGoal 2559 = graph := by decide +kernel
  have roots : vars 2559 = inputs++[orSeed] := by decide +kernel
  simpa only [target,roots] using Free511.noRun
theorem publishedLower : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 4)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  intro C legal first computes
  by_contra! small
  obtain ⟨k,t,budget,without | withSeed⟩ :=
    PEqualNP.Outside.L_meta_3590_aux.initial_live C legal first computes (by omega)
  · exact PEqualNP.Outside.L_meta_3590_aux.dead_start
      (PEqualNP.Outside.L_meta_3590_aux.before_sound _ PEqualNP.Outside.L_meta_3590_aux.valid383)
      PEqualNP.Outside.L_meta_3590_aux.geomdead PEqualNP.Outside.L_meta_3590_aux.tablesdead k t budget without
  · exact PEqualNP.Outside.L_meta_3590_aux.liveSeedImpossible k t budget withSeed


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem old_wire {α : Type} (f : List Bool → α → Bool) (gs : List α)
    (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl (fun s g => s ++ [f s g]) w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (gs.foldl _ (w ++ [f w g])).getD i false = _
    rw [ih _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

end PEqualNP.Outside.L_meta_3590_aux

theorem PEqualNP.Outside.L_meta_3590 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (10 : ℕ)),   PEqualNP.MetaComplexity.FanInTwo x1 →     x2 < x3 →       ¬(x2 = (0 : Fin (10 : ℕ)) ∧ x3 = (4 : Fin (10 : ℕ))) →         ¬((x2 = (0 : Fin (10 : ℕ)) ∨ x2 = (4 : Fin (10 : ℕ))) ∧ x3 = (9 : Fin (10 : ℕ))) →           (∀ (x8 : Fin (9 : ℕ) → Bool),               have x9 : List Bool := List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ))];               x1.eval (x9 ++ [x9.getD (↑x2) Bool.false || x9.getD (↑x3) Bool.false]) = (fun (x10 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x11 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x10 x11.1 && x10 x11.2) x8) →             (14 : ℕ) ≤ x1.size := by

  intro C a b basis _ _ _ computes
  let first : PEqualNP.CircuitLowerBounds.Gate := ⟨.or, [0,4]⟩
  let second : PEqualNP.CircuitLowerBounds.Gate := ⟨.or, [a.val,b.val]⟩
  let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨first :: second :: C.gates, C.output⟩
  let evalGate (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) :=
    g.op.eval (g.inputs.map fun i => w.getD i false)
  have valFirst (x : Fin 9 → Bool) : evalGate (List.ofFn x) first = (x 0 || x 4) := by
    simp [evalGate, first, PEqualNP.CircuitLowerBounds.GateOp.eval, List.getD_eq_getElem?_getD,
      List.getElem?_ofFn]
  have valSecond (w : List Bool) : evalGate w second = (w.getD a.val false || w.getD b.val false) := by
    simp [evalGate, second, PEqualNP.CircuitLowerBounds.GateOp.eval]
  have leBasis : PEqualNP.MetaComplexity.FanInTwo D := by
    intro g hg
    change g ∈ first :: second :: C.gates at hg
    rcases List.mem_cons.mp hg with rfl | h
    · simp [first]
    · rcases List.mem_cons.mp h with rfl | h
      · simp [second]
      · exact basis g h
  have inputGate (x : Fin 9 → Bool) : (D.wires (List.ofFn x)).getD 9 false = (x 0 || x 4) := by
    change ((second :: C.gates).foldl (fun s g => s ++ [evalGate s g])
      (List.ofFn x ++ [evalGate (List.ofFn x) first])).getD 9 false = _
    rw [PEqualNP.Outside.L_meta_3590_aux.old_wire evalGate _ _ _ (by simp), valFirst]
    have hl : (List.ofFn x).length ≤ 9 := by simp
    simp [List.getD_eq_getElem?_getD]
  have correct : PEqualNP.MetaComplexity.circuitFun 9 D = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by
    funext x
    change (C.gates.foldl (fun s g => s ++ [evalGate s g])
      ((List.ofFn x ++ [evalGate (List.ofFn x) first]) ++
        [evalGate (List.ofFn x ++ [evalGate (List.ofFn x) first]) second])).getD C.output false = _
    rw [valFirst, valSecond]
    simpa only [evalGate, PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc] using computes x
  have lower := PEqualNP.Outside.L_meta_3590_aux.publishedLower D leBasis inputGate correct
  change 16 ≤ C.gates.length + 1 + 1 at lower
  change 14 ≤ C.gates.length
  omega
