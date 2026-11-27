import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5002
-- The positive input lower bound adapts the certificate of L_meta_3640.
-- The boundary argument adapts the monotonicity proof of L_meta_2549.
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
private theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]

def Live (target : Sig) : Nat → Nat → Finset Sig → Prop
  | 0,t,S => t=0 ∧ S={target} ∧ proper target
  | k+1,t,S =>
    (∃ (u : Nat) (U : Finset Sig) (a : Sig), t=u+1 ∧ S=insert a U ∧ proper a ∧
      neg a ∉ insert a U ∧ Live target k u (insert (neg a) U)) ∨
    (∃ (U : Finset Sig) (a b : Sig) (d : Bool), S=insert a (insert b U) ∧ proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live target k t (insert (bin d a b) U))
theorem Live.stop {target : Sig} (hp : proper target) : Live target 0 0 {target} := ⟨rfl,rfl,hp⟩
theorem Live.unary {target : Sig} {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
    (hfresh : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)) :
    Live target (k+1) (t+1) (insert a U) :=
  Or.inl ⟨t,U,a,rfl,rfl,ha,hfresh,tail⟩
theorem Live.binary {target : Sig} {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)) :
    Live target (k+1) t (insert a (insert b U)) :=
  Or.inr ⟨U,a,b,d,rfl,ha,hb,hab,hfresh,tail⟩
theorem Live.ind {target : Sig} {motive : ∀ (k t : Nat) (S : Finset Sig), Live target k t S → Prop}
    (stop : ∀ (hp : proper target), motive 0 0 {target} (Live.stop hp))
    (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)),
      motive k t (insert (neg a) U) tail → motive (k+1) (t+1) (insert a U) (Live.unary ha hfresh tail))
    (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)),
      motive k t (insert (bin d a b) U) tail →
      motive (k+1) t (insert a (insert b U)) (Live.binary ha hb hab hfresh tail))
    {k t : Nat} {S : Finset Sig} (h : Live target k t S) : motive k t S h := by
  induction k generalizing t S with
  | zero =>
    obtain ⟨rfl,rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    rcases h with ⟨u,U,a,rfl,rfl,ha,hf,tail⟩ | ⟨U,a,b,d,rfl,ha,hb,hab,hf,tail⟩
    · exact unary ha hf tail (ih tail)
    · exact binary ha hb hab hf tail (ih tail)

private lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h using Live.ind with
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

def Reach {R} (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0,b => b=roots
  | p+1,c => (∃ bank a, Reach roots p bank ∧ Available bank a ∧ c=inv a :: bank) ∨
    (∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R), Reach roots p bank ∧ Available bank a ∧
      Available bank b ∧ c=combine op a b :: bank)
theorem Reach.start {R} {roots : List (Wire R)} : Reach roots 0 roots := rfl
theorem Reach.one {R} {roots : List (Wire R)} {p bank a} (h : Reach roots p bank)
    (ha : Available bank a) : Reach roots (p+1) (inv a :: bank) := Or.inl ⟨bank,a,h,ha,rfl⟩
theorem Reach.two {R} {roots : List (Wire R)} {p bank a b} (op : Bool) (h : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) : Reach roots (p+1) (combine op a b :: bank) :=
  Or.inr ⟨op,bank,a,b,h,ha,hb,rfl⟩
theorem Reach.ind {R} {roots : List (Wire R)} {motive : ∀ p bank, Reach roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (one : ∀ {p bank a} (h : Reach roots p bank) (ha : Available bank a), motive p bank h →
      motive (p+1) (inv a :: bank) (Reach.one h ha))
    (two : ∀ {p bank a b} (op : Bool) (h : Reach roots p bank) (ha : Available bank a)
      (hb : Available bank b), motive p bank h →
      motive (p+1) (combine op a b :: bank) (Reach.two op h ha hb))
    {p bank} (h : Reach roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero =>
    obtain rfl := h
    exact start
  | succ p ih =>
    rcases h with ⟨bank,a,h,ha,rfl⟩ | ⟨op,bank,a,b,h,ha,hb,rfl⟩
    · exact one h ha (ih h)
    · exact two op h ha hb (ih h)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R} (goal : Wire R) : Nat → List (Wire R) → Prop
  | 0,zs => List.Perm [goal] zs
  | s+1,zs => (∃ (save : Bool) (a : Wire R) (rest : List (Wire R)), (a::rest).Perm zs ∧
      Run goal s (inv a :: kept save a rest)) ∨
    (∃ (op ka kb : Bool) (a b : Wire R) (rest : List (Wire R)), (a::b::rest).Perm zs ∧
      Run goal s (combine op a b :: kept ka a (kept kb b rest)))
theorem Run.stop {R} {goal : Wire R} : Run goal 0 [goal] := List.Perm.refl _
theorem Run.perm {R} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run goal s xs) : Run goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    rcases h with ⟨save,a,rest,q,h⟩ | ⟨op,ka,kb,a,b,rest,q,h⟩
    · exact Or.inl ⟨save,a,rest,q.trans p,h⟩
    · exact Or.inr ⟨op,ka,kb,a,b,rest,q.trans p,h⟩
theorem Run.one {R} {goal : Wire R} {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool)
    (h : Run goal s (inv a :: kept save a rest)) : Run goal (s+1) (a::rest) :=
  Or.inl ⟨save,a,rest,List.Perm.refl _,h⟩
theorem Run.two {R} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op ka kb : Bool)
    (h : Run goal s (combine op a b :: kept ka a (kept kb b rest))) : Run goal (s+1) (a::b::rest) :=
  Or.inr ⟨op,ka,kb,a,b,rest,List.Perm.refl _,h⟩
theorem Run.ind {R} {goal : Wire R} {motive : ∀ s ws, Run goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run goal s xs), motive s xs h → motive s zs (Run.perm p h))
    (one : ∀ {s a rest} (save : Bool) (h : Run goal s (inv a :: kept save a rest)),
      motive s _ h → motive (s+1) (a::rest) (Run.one save h))
    (two : ∀ {s a b rest} (op ka kb : Bool) (h : Run goal s (combine op a b :: kept ka a (kept kb b rest))),
      motive s _ h → motive (s+1) (a::b::rest) (Run.two op ka kb h))
    {s ws} (h : Run goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    rcases h with ⟨save,a,rest,p,h⟩ | ⟨op,ka,kb,a,b,rest,p,h⟩
    · exact perm p (Run.one save h) (one save h (ih h))
    · exact perm p (Run.two op ka kb h) (two op ka kb h (ih h))

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
  induction h using Run.ind generalizing p bank with
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
  induction h using Run.ind with
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
  induction h using Live.ind generalizing v with
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
  induction h using Reach.ind generalizing k t S with
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
  induction h using Live.ind with
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
def seed : Sig := neg (inputs.getD 0 zero)

def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem seed_table : ∀ r : Row, bit r seed = !(sample r 0) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem seed_nonzero : seed ≠ zero := by decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl

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
  induction h using Live.ind with
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
  induction h using Live.ind with
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
  induction h using Live.ind with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @unary k t U a ha hf tail _ =>
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
  | @binary k t U a b d ha hb hab hf tail _ =>
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
def varsX (m : Nat) : List Sig := if m.testBit 9 then vars m ++ [seed] else vars m
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
def chartGoal (m : Nat) : Sig := graphGoal m
def rawMask (m : Nat) (c : ColumnInfo) : Nat := m ^^^ (m &&& (c.1 &&& 512))
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let raw := rawMask m c
  let free := colFree raw z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (varsX free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (varsX free) (varsX q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower (varsX q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice (varsX (rawMask m c)) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  revert ok
  obtain ⟨z,o,q,s,L⟩ := c
  intro ok
  let ms := fixRows z o
  let raw := rawMask m (z,o,q,s,L)
  let free := colFree raw z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs s
  change (((properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G) &&
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
    checkMap (swaps.map swapRows) (varsX old) (graphGoal old) (varsX rep) (graphGoal rep)
theorem relabel_of {old rep L swaps} (ok : relabelOK old rep swaps = true)
    (h : Lower (varsX rep) (graphGoal rep) L) : Lower (varsX old) (graphGoal old) L := by
  simp only [relabelOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1) (proper_of _ ok.1.2) h

def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower (varsX e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower (varsX q) (graphGoal q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he


abbrev BoundPool := Sig × Nat × Nat × List Sig
def BoundPool.domain (c : BoundPool) : Sig := c.1
def BoundPool.bound (c : BoundPool) : Nat := c.2.1
def BoundPool.paid (c : BoundPool) : Nat := c.2.2.1
def BoundPool.wires (c : BoundPool) : List Sig := c.2.2.2

def ValidPool (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach (roots.map observe) q ws → Available ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach (roots.map observe) c.paid bank ∧ poolSupply f bank c.wires ∧ True

theorem build_valid {raw T d lb} (h : Slice raw T d lb) (cs : List Choice) {ws}
    (build : makePool d raw cs = some ws) : ValidPool raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa [BoundPool.paid] using hr,hs,trivial⟩

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
    obtain ⟨_,hS,_⟩ := h
    exact out (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
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


abbrev Forest := Nat × Nat × (Nat → Bits × Bits) × List ColumnInfo × List (List Nat) ×
  (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
def Forest.mask (g : Forest) : Nat := g.1
def Forest.cap (g : Forest) : Nat := g.2.1
def Forest.samples (g : Forest) : Nat → Bits × Bits := g.2.2.1
def Forest.cols (g : Forest) : List ColumnInfo := g.2.2.2.1
def Forest.autos (g : Forest) : List (List Nat) := g.2.2.2.2.1
def Forest.levels (g : Forest) : Nat → Packing := g.2.2.2.2.2.1
def Forest.index (g : Forest) : Nat → Nat → Option (Nat × Nat) := g.2.2.2.2.2.2

def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  exact raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i
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
  (g.cols[idx]?).bind fun ci =>
    materialize (varsX (rawMask g.mask ci)) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols, Slice (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : g.cols[i]? with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (List.mem_of_getElem? e)

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
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
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
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (List.mem_of_getElem? e))

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
    (cols : ∀ ci ∈ g.cols, Slice (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
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
    obtain ⟨_,hS,_⟩ := h
    exact hT (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
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
  g.cols.all (fun c => colCheck g.mask c prior) &&
  g.autos.all (fun p => autoOK (targetOf g) (p.map swapRows))

theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower (varsX q) (graphGoal q) (prior q))
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
theorem root_index {g top prior k i ws} (low : ∀ q, Lower (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1

theorem lower_forest {g prior i hints} (low : ∀ q, Lower (varsX q) (graphGoal q) (prior q))
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

theorem lower_discard {g prior ci hints} (low : ∀ q, Lower (varsX q) (graphGoal q) (prior q))
    (ok : colCheck g.mask ci prior = true)
    (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask)
    (nd : (vars g.mask).Nodup)
    (cut : poolCut (subcube ci.1 ci.2.1) ci.2.2.2.2 g.cap 0 (varsX (rawMask g.mask ci)) (vars g.mask)=true) :
    Lower (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) _ (poolCut_sound (col_sound ci prior low ok) [] rfl nd cut)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def Known (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower (varsX e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (relabels : List (Nat × List Nat)) :=
  relabels.map (fun v => (v.1,L)) ++ old
theorem extendKnown_ok {old L m relabels} (previous : Known old)
    (main : Lower (varsX m) (graphGoal m) L)
    (ok : relabels.all (fun v => relabelOK v.1 m v.2) = true) :
    Known (extendKnown old L relabels) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact relabel_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known [] := by simp [Known]
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
def g15d3 (i : Nat) : Nat := 0xf
def g15l3 : Packing := (1,0,0,0,1,0,0,g15d3)
def g15samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbaf3ea78de4d799d,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff450cc90c3c245919),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdf7ff8fe9f9b7ed5,0x20812421801324c4),(0xefbdbf97f9f6bf6a,0x102a401415600a0a),(0xf3a9d7437375f5ba,0xfc028ab620235b0),(0,0),(0,0),(0,0),(0,0),(0,0)]
def g15columns : List ColumnInfo := []
def g15autos : List (List Nat) := [[],[33,48]]
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
def g31columns : List ColumnInfo := [(1,0,30,0,4),(2,0,29,0,4),(4,0,27,0,4),(8,0,23,0,4),(16,0,15,0,4)]
def g31autos : List (List Nat) := [[],[50,65],[66,16],[67,50,33,16],[67,32],[67,66,49,32],[33,48],[67,50,65,48],[67,66,65,64],[49,64]]
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
def g47columns : List ColumnInfo := [(8,0,39,0,4)]
def g47autos : List (List Nat) := [[],[83,32]]
def g47levels : Nat → Packing
  | _ => emptyPacking
def g47index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g47 : Forest := ⟨47,4,fun j => g47samples[j]?.getD (0,0),g47columns,g47autos,g47levels,g47index⟩
def g55samples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffdf7defdfafbfd3fcebcfdeffcebffefe76de77fed7f1773f95eb2ebeb,0x400028000010005000000400701010180030103060043200102204010904888),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdb7fbfbb9ad3afd94caf0b9db5bbdf7f7d39bfcdadcf77ec9eccd2fb9cf16b5,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2484444214284026a4e002420468a8a43140a00408d944460a4082569431231),(0xeda5e7e7b2fc29de4ffc371dba2bf0775ff12db9b18bb528fedad96afcd3c5e,0x12589919410293410206d0396285445a082c5d2bf0022b20f0895d2048c2c4e),(0,0),(0xf1cd79264efe956afa7a64bb677ab40beba463600362eda36f3357b7d763926,0xe3a8651b1a36a0acc57538a080f6ea703078a0c13c28dc34c91f3868663126),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe05fe74eda341d5872cbf684d5e2ed19e7e3bba5e964550dd792aec724f479,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01fb53db1204342a549861b60b6727a22d48ac0b14da4445855161ae724b471),(0,0),(0,0),(0,0)]
def g55columns : List ColumnInfo := [(16,0,39,0,4)]
def g55autos : List (List Nat) := [[],[84]]
def g55levels : Nat → Packing
  | _ => emptyPacking
def g55index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g55 : Forest := ⟨55,4,fun j => g55samples[j]?.getD (0,0),g55columns,g55autos,g55levels,g55index⟩
def g63samples : Array (Bits × Bits) := #[(0xdabffdfdbdf61bfbfc7dcbe34f7f1b17917df75df7edd9eff77b6dbd3dcebed3cfbfaddba50fcabded46bc9b579eb7bd3d92776566ad4ad3debe36d74deb7f9faf189ad76da7dc1a6b4eaf21eb254de4ae1f7451bb34d9456fd18e934db17349,0x4400202400040800310000100084000ac0000102800a1100490002240004b2800a001b4000190000008108000574009200040400000594000190004218c0010840002890800550053044a00410008802d0060013000c004400188120c206208),(0xb6678efeffcbf5a9cad5bfd527a7a5bd74d1314b7915f5b2ffdec2fc5d978f8ab3b44b2b5add5b771711b15ce99bf2b3f5bce975ef94cd59a34e76ab937848a94ef6be6c9579db5905539ea703c87a7d4ae11fe2ae423fade4a3c3299b0724e7,0x499461811a200a55004cf88854029340027a680613c002ec00233c1096d01045025d0203d400243150030b7e4900b00499e023395882049d0206ec00041398010bbb1000b7310ad00cc0858112c8207810e917400e423d0034024309910504e5),(0xbfdd27bedf8fade4776ebf9d185bc5bd76aeffb29711f77d628e86e5fffdff6d1a52bff6da987348e3e147dcecdbcc68d1accc4e7d7d77b9734cfbbcefbc022d72eff5a31a72e32584dd5a72accb1256ede309af577ea6b3ab2be572a2769632,0x20983204990108b1910222a2810c12a8041040402e00006394000908008912a582448429aad10a21a0240190b504314209040621245140c82010e8812042049440841100c0c52080310832a5111106e902488a012c82618908a42202729212),(0x77ddb87389d95f9f7bbe7e8eb89e6e76fbf75ca7fd5bb3758b555b578affe964ae7e7fa493e06d03bebc4fb5cff51e46b2dd5bdbb1eab66f60f7d916b9c6944fd85b6f0fc30a2ae7d2afc9dc369ef80bb1b0b2dd52e9331e786f7a5d38e8c8b4,0x1482478012444200420888514440810c402202189081ecc814422aa4c048408050190921c0450c000a080254044021081134422900082c11250884167012813a48094aca870a3283708e41084282480000c012150640581c30655a55288040a4),(0xdca768aafb78ce8d2db2ec3fbdddfa4ec963339dbac7a8e05eccbf0bb99ddf5febcef6dc7762a4a79d9ad8f70324ba6e724754bded1eed86f695f276b70acbd73dc66e39a88d0cfed920a0ee10b5a4dd5893bba709bff6dc1ece388c561e1ed5,0x210938550593284a984457082a220ca002159526023c0223a02100100d271046aa46f2022bb0201ea5730921b3008e848a002106a7520082d20653c8040064810364a00030c5086c0c2084761035a077101508a009ba22e00b822088521e1c51),(0x77dad76bd4ced656e7ec247a694c9eb5b66dc4de71aac18acebb177a9bac7a62d6f3e3996dd9d62d6ecf7b18557229a30b5ebb1ef46b568a8f3400a7c2d3365caade63d0f2234a24623735bcfaee29c0664eddfc63b2a86915f817ca03dc41fa,0x88252894b2b3256598a758928465236453b27d28c68c4c28a24dcc0d24d500d4a845700845b04bd175706d345a20a0a24d641d897dd822a1d52444cad2629c8e732b305273362844202335b73c8d8150424e93e44a78286995ec17c803dc01f2),(0,0),(0,0),(0,0)]
def g63columns : List ColumnInfo := [(32,0,31,0,7)]
def g63autos : List (List Nat) := [[],[50,65]]
def g63levels : Nat → Packing
  | _ => emptyPacking
def g63index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g63 : Forest := ⟨63,7,fun j => g63samples[j]?.getD (0,0),g63columns,g63autos,g63levels,g63index⟩
def g111d6 (i : Nat) : Nat := 0x120ff
def g111l6 : Packing := (1,0,2,0,1,0,0,g111d6)
def g111samples : Array (Bits × Bits) := #[(0xeafcc7b96fc59ffd26c5e2bb3d7bd378fb35ff5dcb26f92afa5f57eff59a73b7aaa379b2fc8d7a99e2ef9efcf4defd4efabc9c89733cebade5579ad5abbcd64d8557ad3d63bd1c6a75510ce3b9bf05e462ee0edf6dfb2914efc74c7d31727465,0x4d00310a2003881269402d0c00406ccc142a8012908082d00025ac006a88036948003229000032d4001bf20024ec2018680000aaf2500325400423a6f02003840040a8016ea8106822700071012c01d500600ad401ea0010f407087831504444),(0xf771ad34ff2bcf4fbd7f5f5de52efaeb7ebbabfffefbf2eab7c7cf56f8ecea565ddfabcf87cb61db9d6ef4aecff7cebd76fe679cfb9935e6adabc77cdcdb677ed3da5e4f56b4cbe39cfd7aed1f519a6b999796b48a51f4f7b8ad91a66cc6d9cb,0x1204940050200482000010001c10308054448009004424020800871400ac0690000402004e0508404004081210450414000904018220d090010808000a44280600460810104d92040818880c1010088d8400200a10a1400808810604821909),(0xf5be76df5e79b8b5d13f5f6e3ecd176fbeee538a7cfb9f7f6b7fad9b13bb7fed97560ecd71f29f3f1e3ef959a338e3a9e32bd5e7cfc7b51df73d7e9e165479b3baa9a0d59e62e11eead3ad5c624777de8699f96d3766d64d1f3fa2ca8f3d2e52,0x8e4d19200884440101e4a802e100a0c04000830eb000289800c49240c1c411082c325a6812b0485430294040c52402008322a4b0e00c0021216842103a050a9080848145264020288841a770220547500211500d95204c05521120880b352452),(0xde2ebbc73c1cf83c4cedbed77297d7f5b666582db23d5c5d7bf4a54b37a75f4992f88d683d388ea5bafb57791a5deb9b257390777cf70e9d329773c24416edd93fe3d2909bc3b81d7e62dd94d70a759eb42b6b51587d63da2e7eea6ce78912bc,0x10b22099c5638280b403142808691e02bd9d04d1097a9640ce2041351e20e64283892100494815238b12089820999d9858901b4e1903515e001721098578a5416f515492d981d895722018845902b08a5c4a2a2248dd03d08c66ca64e48812ac),(0,0),(0x4a99db5e74fdf3bbfb83b4b12e735e58f515867b75942dba656f9eeac55739b971685432ece5b39368c30fbbb9f895ca9efa5eceda2fea7be4766f052ba5def635ccf928215f7640050f6846acafb2ca6efbba0bffbfdb9043d87d111c3c3ebd,0x12d68401de50564414b80023f49c0203c0413d800068400bbb08034f0177ac0427f40400f6de0023bcc009fc1201950403ff4900082ea08a2fc908010c8a4053de0011e801464d050407f806ac13f8026d9b800bfa055d40038875010c2c3ab9),(0x107b7e8791b6519a9ebd6f37d374faa298392ebad8b5e4afe6bd267679568b3365bebaabdf6ef4e9035a918e8ca50ef74769b2b74aea726a09a6c5e9463715fb76745a9b1b6212a1b9add6dec52a9ba55b57e399ab660ca6d0f217384af881fe,0xadc48a6a24248ac9294916cc74a18dce4988890976a839d0a90054480a8f001149b409fd5690d8d50882129489ae3083c83b5253565cd02541ca4550f495b985581508b28aaa022919a1e755a00eaaa54243a315f06a0c87d4f216384a7880f6),(0,0),(0,0)]
def g111columns : List ColumnInfo := [(4,8,99,0,4),(1,32,78,0,4),(64,0,47,0,5)]
def g111autos : List (List Nat) := [[],[83,32]]
def g111levels : Nat → Packing
  | 6 => g111l6
  | _ => emptyPacking
def g111index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | _ => fun _ => none
def g111 : Forest := ⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index⟩
def g119samples : Array (Bits × Bits) := #[(0xfab75f3dfbfa3756f92d9ff7baf5ff7dbfebb9b33bef7dcdf77fbffe7bbbf75546cedccfd6f7eb762bef3ffdd2ede7abbef7e4e4b775eb9be6ab6f4d5fde77f2b955ece57b3feb97c6d99b5cdd2fdd2ea315de5f3efbf8d44ddcaa7566eda9cd,0x20100000802449000a820000c1900042800052080010000098c000620802429000050a2000012e00000be20013404000082000047420011240000c8b8000110080002480036500158018000c4009400c9000c0062803a0400e00885042a10888),(0xaf7efcd6de9febfb57d6f5ddedde36f3db7fffeed79fdbfafcf255738c743cbbbff3e3b86b8f9fb9f5bdf54fbff79bd74f5afb3f7fba34f5bf5f9afae879ab5feefe93fa9ee6566f7bbee6bf67d426d75cfb2bace9344fabf72bd58e999b76b3,0x9300010000091004000400382060802420900110020801010208161810541520000000800198110400c004084880812115000049028020c0800220200009220a01801050108206a8408406120184808104430800802442850101410609083421),(0xd3aee9d1a16b8afb579b1b1a2ede96c634714fced4ed35afb8d86696aabedb2eada373270f48f3a9b93de8a90d87d8f6684756adef8eb40bf672fc78b9342c9c7aaa652b2aec9422dd38b32b2a5255bdcc3d35b2da5f372953f3c4ba3a70d996,0x2c07b23e74020fd2aa41748155856818d263d681015680dac92709c7448b08586eaf3a512642c64b613a9091954b38c222671d26711d023332d48951dd0691952839212f8b6888039910b9ac2a42653c283c65315b1b95185ae084b83270c996),(0,0),(0x759a506bc07865de6f37bc2fabe39a5e2705b6a3eec6bd3cca572e3ed72f0325f632aa43d8e0e833eaeab6f86ad5fa72dbaf9c83b9e70faa212acf122e177ae733d8fa39a0b0bb12b7915f7134c3b9a9ed98d75362b1d9c725676c3caf04637c,0x16e5f59c6d01a255c44806523c0cddb5529a2196d082e7c24415d298c0f10d071e6090549dc090f8ed501938009f3fb2169588d90b0b506d102e01343cb84ad135f45369a498be0a36011e712702bb816af81651c4b05c0701a6642cad046374),(0x6339c3e76f77dc41ec6c9766b8b0f93592cd6e58a17db2abb9eea5cd269eeae2dc2c1c9ec755bae6a2821f6b678c3538a75edaf56c57e97ff4e8b90d55c4e75ce36b37ac511be4c610c6f229b9ab77956345b3a117ef6f3608dd37697870ba61,0x84ef690f5888a6bc0049f9381c0ba0115db000874a075d2102333605e754184fe100105f739880fb92c019ec481f2d2102dbf2480954a0ad3f922114724920d57f80032e5018c6a22083e62199863ec06b43378157e41d3d00d937293850b261),(0xd5cc96ab2735f4eedbcfece9fd4d847149d75b8aa71ff3959066dc7566c66ecb75975abde9bb8d684d89311f3151135dd1ce4d97acd9737d0b4d97b62b1596cf57b51ab1b6b408593b67d5bb928b32dabad66fc43367241aeaae177095e247ea,0x481560b0cd924918c5323d4303992d88d1232e6a49f254a2454320824e8122936522ef3572424e688310332525616c12e023da92a435d213539c9243b254cc21b63548a8e4258841b361f1c95a017252ba1c47902bc1245a7a8e167094e243ca),(0,0),(0,0)]
def g119columns : List ColumnInfo := [(4,0,115,0,5)]
def g119autos : List (List Nat) := [[],[84],[98],[84,98],[101,66,16],[101,100,66,16],[101,84,82,16],[100,82,16]]
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
def g189columns : List ColumnInfo := [(1,0,188,0,5),(12,0,177,0,4),(16,0,173,0,5),(17,0,172,0,4),(24,0,165,0,4),(33,0,156,0,4),(132,0,57,0,4),(160,0,29,0,4)]
def g189autos : List (List Nat) := [[],[84,115],[117,67,32],[116,83,32],[82,48],[84,115,82,48],[117,116,115,114,64],[83,114,64],[116,50,80],[117,84,67,50,80],[84,115,66,112],[66,112]]
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
def g127columns : List ColumnInfo := [(32,0,95,0,8)]
def g127autos : List (List Nat) := [[],[101,66,16]]
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
def g191columns : List ColumnInfo := [(1,0,190,0,7),(2,0,189,0,8),(3,0,188,0,5),(4,0,187,0,7),(6,0,185,0,5),(8,0,183,0,8),(0,8,163,20,6),(10,0,181,0,5),(12,0,179,0,5),(4,8,163,16,5),(14,0,177,0,4),(16,0,175,0,8),(0,16,166,9,6),(1,16,166,8,5),(19,0,172,0,4),(24,0,167,0,7),(16,8,163,4,5),(8,16,166,1,5),(25,0,166,0,4),(9,16,166,0,4),(20,8,163,0,4),(32,0,159,0,8),(1,32,30,128,5),(35,0,156,0,4),(40,0,151,0,5),(48,0,143,0,5),(56,0,135,0,4),(128,0,63,0,8),(130,0,61,0,5),(4,128,27,32,5),(136,0,55,0,5),(160,0,31,0,7),(128,32,30,1,5),(32,128,27,4,5),(161,0,30,0,4),(129,32,30,0,4),(164,0,27,0,4),(36,128,27,0,4)]
def g191autos : List (List Nat) := [[],[84,115],[117,67,32],[116,83,32]]
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
def g251columns : List ColumnInfo := [(8,0,243,0,7)]
def g251autos : List (List Nat) := [[],[84,115],[99,65],[118,84,115,65],[118,81],[118,84,99,81]]
def g251levels : Nat → Packing
  | _ => emptyPacking
def g251index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g251 : Forest := ⟨251,7,fun j => g251samples[j]?.getD (0,0),g251columns,g251autos,g251levels,g251index⟩
def g255samples : Array (Bits × Bits) := #[(0x9b665c544a8481c32c829a3849d25a0c2e734bceaece0410b1910c9246b692285657c973ca335d593cb00f0546b90059eb43e97a932728851785431870f031165ac8b80393ba6e576270cc58c906b870841734e15dc89803598ab05c2460a6b1,0x104454110880808228020a2041d8002c08600a02808c02009111060244ac12008614a1024802115108904700443200508241c8821224200116051018407029164080a01212302c0942400010c90428108414142154888803090a9048202086a0),(0xf315668af28fdb1ca228365b7ccc05a0011317731e21482f697635c521d4e57b4580944cacd08190116899ef79421d834fcee4e488905930903982805fb1c61927af17aaf49049a676974192f0d0160363a1bd03830701b0dc1f8281c2dc6123,0x83112a82400c43108201140b24040542001210600e014836084820c40800442b4181104024900000902098cc210099010006246088901220003082011981800902040620cc814002101041843090160043212902810201b054050081825c2101),(0x380526282fa13ac851f4c9c505254980d6e8ec3804b3594a769d93b950ebc251b0d8e2a15610b8154799066089743516386914b45de9a6e1e91c2d64aa4bec2945782990b2d68e61aa4d3cd1b24a6ab680984b4c1298da14a63264e421a50a46,0x184000082381184051a442400021c800c760240c008201086414493150c8805030586481420228050588002082640402084818905528808149002d00020c144045280184104604602a043c40824a60b20098024012185a048212646400810a02),(0x96903da21572f2b1f1c959078994a771bc47364121282ac5966e24786e0f6b8886ae49c27124b27b7242ff2e0094e0b4b1b582696d3c94568c371a6b03b30075a8d6353ad9672c0089eb12ba6325f80dd24d451b8459a7c113618d0b812f118c,0x86100cb01034a2a12848198388d4226018030240202c8a411a0a044824066a838a240842212092185a40cf0a0080e094a530c6680a1400448645526011312024a0c7343889210800016b021a61259805924545098441a1c11120810b812e1184),(0xca830c6ee5a1c1ac77b2c4bb013b84b271c7189edce77b42164b82b2ec44ccc2202552493f52e619512b4f09e2177ba801c291327039cbf4fba1fd7ca29d36ceca40c4508827295a1b45be11b7c00687be220f65622167c80c13fe90c415919,0x1282044674a181cc515204830038803270c71014e5265b22464b9241a4004482002443590d10ca0850630203a411b2a000c201185038c3861ba0d078200d6480c204804048212d4a89449e11258006869a220d60222163c80c12ea00c414819),(0xadcb89db333a54791fc5b16de6a74b1fbdaa5224c4caa060c8434905e130b3e50875189fa3aee40ebf67487ce98db2673644923b555505294552488c144494c2312ef3656d2d51ee39b1b44e04f3d3ec4d148000ab72771f011403179f478e82,0xa991884a13221d3803c5e045a0014312e78660240442614040424905201081f109410899826ca6043646807ca808b20b342020284941850001124c8410049440302c118d6904416438b533460072d3ec490080008b50771c0014031517470802),(0xccf1d170b069949f14600d7679a83ea985e068495997ad010287ff4ea745b576050c4fa9e8e0fabd2497448bd27a5aa8acea4ac0268e4d44dc2df9de452a225ad1457b3d721818b9bf9e05034d50ecb938aed67098a522a72856072e55b8d214,0xce85130b040942f1560095449a91aad8dc0e80b5196a18140955b282345b194266c47298868eeb9221d4601c27a00e8acf04a8036004c04cc8c58ecc43a23d68161791d311c0cb9abcc24434d40e8b9388ed67018a522072852072e55a0d214),(0x442aa5b9d884c622461c21eaaaf556fac8da8923687abbfb99c9c28096422e0eb83cb34c1d8918aec8c55d99f53bc2670104934ee2f27258616b2c55a56fa8970e02486406e9b92b5242282d15890d903f02672424a3e96d3ce1d022fa0aa8e8,0x460a679588446000a40a01aa08c414e80818810338389a92898982c08602320ec02091061180118a88016c815113416481048146a2821250206d8051a4632a958802cc600689381b004a400915810c003602652424a380613ce19002e808a0e8),(0,0)]
def g255columns : List ColumnInfo := [(64,0,191,0,11)]
def g255autos : List (List Nat) := [[],[84,115],[117,67,32],[116,83,32]]
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
def g383columns : List ColumnInfo := [(1,0,382,0,9),(0,1,332,50,7),(2,0,381,0,9),(0,2,312,69,7),(3,0,380,0,6),(2,1,332,48,6),(1,2,312,68,6),(4,0,379,0,11),(5,0,378,0,7),(7,0,376,0,5),(5,2,312,64,5),(8,0,375,0,9),(0,8,99,276,7),(12,0,371,0,8),(13,0,354,0,4),(14,0,369,0,5),(16,0,367,0,11),(17,0,366,0,8),(18,0,365,0,7),(19,0,364,0,5),(18,1,332,32,5),(24,0,359,0,8),(25,0,358,0,5),(28,0,355,0,7),(20,8,99,256,5),(32,0,351,0,11),(33,0,350,0,8),(32,1,332,18,6),(35,0,348,0,5),(34,1,332,16,5),(44,0,339,0,5),(49,0,334,0,7),(48,1,332,2,5),(33,16,326,8,5),(56,0,327,0,5),(64,0,319,0,11),(65,0,318,0,7),(66,0,317,0,8),(67,0,316,0,5),(65,2,312,4,5),(70,0,313,0,7),(34,64,29,256,5),(256,0,127,0,9),(0,256,23,104,7),(264,0,119,0,6),(256,8,99,20,6),(8,256,23,96,6),(268,0,115,0,5),(260,8,99,16,5),(280,0,103,0,5),(272,8,99,4,5),(288,0,95,0,8),(289,0,94,0,5),(40,256,23,64,5),(304,0,79,0,5),(320,0,63,0,8),(322,0,61,0,5),(258,64,61,0,5),(352,0,31,0,7)]
def g383autos : List (List Nat) := [[],[84,131,98],[101,66,16],[100,131,82,16],[82,129,48],[101,100,131,98,129,48],[100,49,128],[101,84,131,66,49,128]]
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
theorem valid3 : Known known3 := extendKnown_ok (m:=3) baseKnown low3 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low7 : Lower (vars 7) (graphGoal 7) 2 := size_of (hints:=257) (by decide +kernel)
def maps7 : List (Nat × List Nat) := []
def known7 := extendKnown known3 2 maps7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid7 : Known known7 := extendKnown_ok (m:=7) valid3 low7 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom15 : graphValid g15 (boundsBefore known7) = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables15 : checkedTables g15 3 := by
  intro k hk
  interval_cases k <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low15 : Lower (vars 15) (graphGoal 15) 4 :=
  lower_forest (g:=g15) (i:=0) (hints:=8449) (before_sound known7 valid7) geom15 tables15 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps15 : List (Nat × List Nat) := [(15,[]),(23,[32,67]),(27,[16,66]),(29,[65,50]),(30,[64,65,66,67]),(39,[32,67,84]),(57,[32,65,82,83]),(78,[64,33,67,84,101]),(99,[16,33,66,83,100,101]),(135,[67,84,101,118]),(156,[64,81,83,101,118]),(163,[16,66,83,100,101,118]),(165,[65,50,83,100,101,118]),(166,[64,65,66,83,100,118]),(172,[64,81,82,67,100,101,118]),(177,[16,65,82,99,118]),(198,[64,83,100,117]),(281,[65,82,83,101,118,135]),(305,[16,65,82,99,118,135]),(312,[64,81,98,83,118,135]),(326,[64,66,83,100,117,135]),(330,[64,65,82,100,117,135]),(332,[64,81,66,83,100,117,118,135]),(344,[64,81,98,83,117,118,135]),(353,[65,82,99,116,117,135]),(354,[64,65,82,99,116,101,118,135]),(396,[64,81,82,83,100,117,134,135]),(424,[64,81,98,67,116,101,134]),(480,[64,81,98,115,132,101,134])]
def known15 := extendKnown known7 4 maps15
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid15 : Known known15 := extendKnown_ok (m:=15) valid7 low15 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low45 : Lower (vars 45) (graphGoal 45) 3 := size_of (hints:=8965) (by decide +kernel)
def maps45 : List (Nat × List Nat) := []
def known45 := extendKnown known15 3 maps45
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid45 : Known known45 := extendKnown_ok (m:=45) valid15 low45 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low51 : Lower (vars 51) (graphGoal 51) 3 := size_of (hints:=1) (by decide +kernel)
def maps51 : List (Nat × List Nat) := []
def known51 := extendKnown known45 3 maps51
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid51 : Known known51 := extendKnown_ok (m:=51) valid45 low51 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom31 : graphValid g31 (boundsBefore known51) = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables31 : checkedTables g31 6 := by
  intro k hk
  interval_cases k <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low31 : Lower (vars 31) (graphGoal 31) 7 :=
  lower_forest (g:=g31) (i:=0) (hints:=8449) (before_sound known51 valid51) geom31 tables31 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps31 : List (Nat × List Nat) := [(31,[]),(167,[83,100,101,118]),(313,[81,98,99,84,118,135]),(334,[80,81,82,83,100,117,135]),(355,[82,99,116,117,118,135]),(428,[80,97,82,99,116,101,134])]
def known31 := extendKnown known51 7 maps31
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid31 : Known known31 := extendKnown_ok (m:=31) valid51 low31 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low47 : Lower (vars 47) (graphGoal 47) 5 :=
  lower_discard (g:=g47) (ci:=(8,0,39,0,4)) (hints:=8449) (before_sound known31 valid31) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps47 : List (Nat × List Nat) := [(47,[]),(61,[65,50]),(94,[64,65,66,67,101]),(151,[67,84,101,118]),(173,[48,65,50,83,100,118]),(181,[65,50,99,84,118]),(185,[16,65,98,83,101,118]),(188,[64,97,98,67,84,118]),(227,[16,66,99,116,117,118]),(230,[64,65,66,99,116,101]),(301,[48,65,82,100,118,135]),(331,[80,81,66,100,117,118,135]),(339,[66,99,84,117,118,135]),(345,[80,65,98,67,84,117,118,135]),(346,[64,49,98,67,84,117,135]),(358,[64,65,82,99,116,101,118,135]),(369,[65,98,115,84,118,135]),(422,[64,81,66,99,116,117,134]),(440,[64,97,114,67,84,117,134]),(454,[64,66,99,116,133,118,135]),(460,[64,97,66,99,116,133,135]),(482,[64,49,98,115,132,133,135]),(484,[64,97,82,115,132,101,118,135])]
def known47 := extendKnown known31 5 maps47
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid47 : Known known47 := extendKnown_ok (m:=47) valid31 low47 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low55 : Lower (vars 55) (graphGoal 55) 5 :=
  lower_discard (g:=g55) (ci:=(16,0,39,0,4)) (hints:=257) (before_sound known47 valid47) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps55 : List (Nat × List Nat) := [(55,[]),(79,[64,65,66,67,101]),(103,[16,66,100,101]),(115,[50,99]),(143,[32,67,101,118]),(174,[48,65,50,83,100,118]),(179,[65,50,99,84,118]),(206,[48,50,67,100,117]),(286,[48,33,101,118,135]),(316,[48,97,66,84,118,135]),(327,[64,65,82,100,117,135]),(348,[48,97,66,84,117,118,135]),(364,[48,97,99,116,118,135]),(376,[48,97,114,99,116,118,135]),(398,[48,65,50,67,100,117,134]),(433,[16,49,98,115,100,117,134,135])]
def known55 := extendKnown known47 5 maps55
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid55 : Known known55 := extendKnown_ok (m:=55) valid47 low55 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low63 : Lower (vars 63) (graphGoal 63) 8 :=
  lower_discard (g:=g63) (ci:=(32,0,31,0,7)) (hints:=8449) (before_sound known55 valid55) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps63 : List (Nat × List Nat) := [(63,[]),(95,[16,66,101]),(159,[32,67,101,118]),(175,[32,83,100,118]),(183,[99,84,118]),(231,[16,66,99,116,117,118]),(317,[32,97,82,83,100,118,135]),(350,[96,33,99,84,117,135]),(359,[16,82,99,116,118,135]),(366,[96,49,116,118,135]),(371,[98,115,84,135]),(377,[48,97,114,99,116,117,118,135]),(429,[80,97,116,134,135]),(430,[96,81,98,83,116,134]),(441,[16,97,114,116,101,134,135]),(444,[96,113,114,99,84,101,134]),(462,[96,98,67,116,133,135]),(492,[96,113,115,132,133,134])]
def known63 := extendKnown known55 8 maps63
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid63 : Known known63 := extendKnown_ok (m:=63) valid55 low63 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom111 : graphValid g111 (boundsBefore known63) = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables111 : checkedTables g111 6 := by
  intro k hk
  interval_cases k <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low111 : Lower (vars 111) (graphGoal 111) 7 :=
  lower_forest (g:=g111) (i:=0) (hints:=16785665) (before_sound known63 valid63) geom111 tables111 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps111 : List (Nat × List Nat) := [(187,[16,97,66,83,100,101,118]),(190,[64,97,98,67,84,118]),(215,[67,84,117]),(222,[64,65,66,67,117,118]),(238,[64,65,66,99,116,101]),(243,[16,66,115,100,101]),(318,[64,81,66,83,100,118,135]),(349,[80,65,98,67,84,117,118,135]),(365,[48,65,82,116,135]),(378,[64,49,114,67,84,101,118,135]),(413,[48,65,50,67,117,134]),(437,[65,50,115,84,134]),(455,[96,98,67,116,133,135]),(476,[64,113,66,115,100,133,118,135]),(490,[64,49,114,99,132,133,118,135]),(497,[65,114,131,84,134,135]),(504,[64,113,130,67,84,133,135])]
def known111 := extendKnown known63 7 maps111
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid111 : Known known111 := extendKnown_ok (m:=111) valid63 low111 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low119 : Lower (vars 119) (graphGoal 119) 6 :=
  lower_discard (g:=g119) (ci:=(4,0,115,0,5)) (hints:=16777473) (before_sound known111 valid111) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps119 : List (Nat × List Nat) := [(119,[]),(207,[64,65,66,67,117,118]),(380,[48,113,66,84,101,135]),(414,[48,65,50,67,117,134])]
def known119 := extendKnown known111 6 maps119
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid119 : Known known119 := extendKnown_ok (m:=119) valid111 low119 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom189 : graphValid g189 (boundsBefore known119) = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables189 : checkedTables g189 7 := by
  intro k hk
  interval_cases k <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low189 : Lower (vars 189) (graphGoal 189) 8 :=
  lower_forest (g:=g189) (i:=0) (hints:=536879876) (before_sound known119 valid119) geom189 tables189 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps189 : List (Nat × List Nat) := [(189,[]),(347,[65,66,115,84,101,118,135]),(486,[16,66,99,132,133,134,135])]
def known189 := extendKnown known119 8 maps189
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid189 : Known known189 := extendKnown_ok (m:=189) valid119 low189 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low250 : Lower (vars 250) (graphGoal 250) 5 := size_of (hints:=1366507616) (by decide +kernel)
def maps250 : List (Nat × List Nat) := []
def known250 := extendKnown known189 5 maps250
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid250 : Known known250 := extendKnown_ok (m:=250) valid189 low250 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low127 : Lower (vars 127) (graphGoal 127) 9 :=
  lower_discard (g:=g127) (ci:=(32,0,95,0,8)) (hints:=16785665) (before_sound known250 valid250) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps127 : List (Nat × List Nat) := [(127,[]),(223,[64,65,66,67,117,118]),(247,[115,84]),(375,[98,115,84,135]),(381,[48,113,82,135]),(382,[112,49,66,115,84,101,135]),(415,[48,65,50,67,117,134]),(446,[112,81,114,83,100,134,135]),(478,[112,65,114,67,100,133,135]),(493,[80,113,50,132,135]),(499,[65,114,131,84,134,135]),(505,[64,113,130,131,132,133,135]),(508,[112,129,66,115,84])]
def known127 := extendKnown known250 9 maps127
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid127 : Known known127 := extendKnown_ok (m:=127) valid250 low127 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom191 : graphValid g191 (boundsBefore known127) = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables191 : checkedTables g191 10 := by
  intro k hk
  interval_cases k <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low191 : Lower (vars 191) (graphGoal 191) 11 :=
  lower_forest (g:=g191) (i:=0) (hints:=536879361) (before_sound known127 valid127) geom191 tables191 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps191 : List (Nat × List Nat) := [(191,[]),(319,[65,50,135]),(351,[64,65,66,67,101,135]),(367,[80,81,66,100,117,118,135]),(379,[81,98,118,135]),(431,[48,65,50,83,100,134,135]),(445,[48,97,82,134]),(487,[16,66,99,132,133,134,135]),(494,[96,65,98,67,132,117,134])]
def known191 := extendKnown known127 11 maps191
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid191 : Known known191 := extendKnown_ok (m:=191) valid127 low191 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low251 : Lower (vars 251) (graphGoal 251) 8 :=
  lower_discard (g:=g251) (ci:=(8,0,243,0,7)) (hints:=1358970881) (before_sound known191 valid191) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps251 : List (Nat × List Nat) := [(251,[]),(254,[32,67,117]),(471,[16,66,67,100,133,134,135]),(501,[16,33,50,131,100,133,118]),(506,[32,49,130,100])]
def known251 := extendKnown known191 8 maps251
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid251 : Known known251 := extendKnown_ok (m:=251) valid191 low251 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low255 : Lower (vars 255) (graphGoal 255) 12 :=
  lower_discard (g:=g255) (ci:=(64,0,191,0,11)) (hints:=553656577) (before_sound known251 valid251) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps255 : List (Nat × List Nat) := [(255,[]),(479,[64,65,66,67,133,134,135]),(503,[16,66,131,100,101,135]),(507,[81,130,118]),(509,[48,129,82]),(510,[128,65,130,67,100,117])]
def known255 := extendKnown known251 12 maps255
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid255 : Known known255 := extendKnown_ok (m:=255) valid251 low255 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom383 : graphValid g383 (boundsBefore known255) = true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables383 : checkedTables g383 12 := by
  intro k hk
  interval_cases k <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low383 : Lower (vars 383) (graphGoal 383) 13 :=
  lower_forest (g:=g383) (i:=0) (hints:=12901687553) (before_sound known255 valid255) geom383 tables383 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps383 : List (Nat × List Nat) := [(383,[]),(447,[65,50,131,84,118,135]),(495,[80,81,82,83,116,133,118])]
def known383 := extendKnown known255 13 maps383
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid383 : Known known383 := extendKnown_ok (m:=383) valid255 low383 (by decide +kernel)
def deadautos : List (List Nat) := [[],[118,130,81],[100,131,82,16],[118,133,100,131,50,33,16],[116,83,32],[118,116,83,130,49,32],[118,133,33,48],[82,129,48],[118,133,116,83,82,81,80],[116,50,129,80],[100,49,128],[118,100,83,130,81,128]]
def enabledLinks {α} (flag : Bool) (xs : List α) := if flag then xs else []
theorem enabledLinks_mem {α} {flag : Bool} {x : α} {xs : List α} (h : x ∈ enabledLinks flag xs) : x ∈ xs := by
  cases flag <;> simp_all [enabledLinks]

def wideDecode (n : Nat) (bits : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 31) defaultDecor
    let b := ws.getD ((bits >>> 5) &&& 31) defaultDecor
    wideDecode k (bits >>> 11) (ws++[codeDecor ((bits >>> 10) &&& 1) a b])
theorem wide_faithful (n bits) (ws) (r s) (base : ∀ v ∈ ws, faithful r s v) :
    ∀ v ∈ wideDecode n bits ws, faithful r s v := by
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

def wideRead (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := (8+11*(depth-2))
  let width := len+raw.length+depth
  let recp := packedAt data (i*width) width
  let stored := recp &&& ((1 <<< len)-1)
  let second := 1024 + 32*((stored >>> 4) &&& 15) + (stored &&& 15)
  let ops := 1120 ||| (second <<< 11) ||| ((stored >>> 8) <<< 22)
  let bank := wideDecode depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)

def wideSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more := wideSteps bank (ops >>> 11) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 10 1,(bank.getD (ops &&& 31) defaultDecor).1,
        (bank.getD (getFieldV ops 5 5) defaultDecor).1) :: more

def wideRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols[idx]?).bind fun ci =>
    materialize (varsX (rawMask g.mask ci)) (wideSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem wideRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols, Slice (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : wideRule g ops depth bank i paid = some c) :
    ValidPool (vars g.mask) (targetOf g) c := by
  unfold wideRule at h
  cases e : g.cols[i]? with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (List.mem_of_getElem? e)

def wideState (g : Forest) (k i : Nat) := (wideRead g k i).2.2.map Prod.fst
def wideLinks (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (wideState g k pair.1).map (movedWord (perm.map swapRows).reverse)

def wideContext (g : Forest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := wideRead g k i
  let start := num*((8+11*(depth-2))+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 7
  let nl := packedAt data (pos+7) lw
  let st := pos+7+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => wideRule g ops depth bank a b)
  let ls := fun tag => enabledLinks (nl != 0) (((g.index k tag).bind (wideLinks g (k-1))).toList)
  (k,ws.length,ws,preCov ws,rules,ls)


def evalMono (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let un := op==2
  let len := 1+(n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  if len>cap then true else
    let d := true
    let rs := restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 768 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (opKeep un ka kb a b ws).map Prod.fst
      closeChild pools links (cap-1) rest (movedChoice op a b)

def testMonoPair (ctx : NodeContext) (a b : Decor) (d : Bool) :=
  let op := if d then 1 else 0
  let z := movedDecor op a b
  let attempt := evalMono ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
theorem testMonoPair_at {ctx a b d} (h : testMonoPair ctx a b d = true) (ka kb : Bool) :
    evalMono ctx (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) ka kb = true := by
  simp only [testMonoPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

def ImpossibleM (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k t, k ≤ cap → t=0 → ¬Live T k t S

theorem enum_stepM {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      ImpossibleM T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    ImpossibleM T cap ws.toFinset := by
  classical
  intro k t hk ht h
  generalize he : ws.toFinset = S at h
  induction h using Live.ind with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @unary k t U a ha hf tail _ => omega
  | @binary k t U a b d ha hb hab hf tail _ =>
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
    exact twoStep a am b bm d ka kb hab fresh hz len k t (by omega) ht (eq.symm ▸ tail)

theorem closeChild_soundM {raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → ImpossibleM T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op = true) :
    ImpossibleM T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · intro n t le _
    exact scalarPoolCut_sound (pValid _ hp) nd ok n t le

theorem evalMove_soundM {raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false → a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → ImpossibleM T (cap-1) (List.toFinset xs))
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : evalMono (cap,ws.length,ws,preCov ws,pools,links) op a b (movedDecor op a b) ka kb = true) :
    ImpossibleM T (cap-1) (moveFront ws op a b ka kb).toFinset := by
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
  intro k t hk ht h
  have hsz := (live_size h).2
  change child.toFinset.card + t ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMono at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  let d := true
  have sep := cover_sound h rfl (pair_sep pairs) true (fun _ => ht)
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz := rest_coverage ha hb (op==2) ka kb d ne
  have hf := moved_faithful (faith _ ha) (faith _ hb) op
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
  exact closeChild_soundM pv lv nd' test k t hk ht h

def testRowM (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
  bs.all (fun b => testMonoPair ctx a b false && testMonoPair ctx a b true)

def testAllM (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRowM ctx a bs && testAllM ctx bs

theorem all_binaryM {ctx ws} (h : testAllM ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) (d : Bool) : testMonoPair ctx a b d=true ∨ testMonoPair ctx b a d=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAllM,Bool.and_eq_true,testRowM,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      left
      cases d <;> first | exact (h.1 b bm).1 | exact (h.1 b bm).2
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · right
        cases d <;> first | exact (h.1 a haTail).1 | exact (h.1 a haTail).2
      · exact ih h.2 haTail hbTail

theorem node_soundM {raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → ImpossibleM T (cap-1) (List.toFinset xs))
    (checks : testAllM (cap,ws.length,ws,preCov ws,pools,links) ws = true) :
    ImpossibleM T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k t hk ht h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    obtain ⟨_,hS,_⟩ := h
    exact out (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_stepM nd out
  · intro a ha b hb d ka kb ne fresh pro len
    obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
    obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
    have ab : a≠b := fun e => ne (congrArg Prod.fst e)
    have one (a b : Decor) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
        (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
        (test : testMonoPair (cap,ws.length,ws,preCov ws,pools,links) a b d = true) :
        ImpossibleM T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
      rw [←binary_front nd aa bb ne']
      have eq : (movedDecor (if d then 1 else 0) a b).1 = bin d a.1 b.1 := by cases d <;> rfl
      exact evalMove_soundM pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' pv lv
        (eq ▸ pr) (eq ▸ fr) (testMonoPair_at test ka kb)
    rcases all_binaryM checks haW hbW ab d with hh | hh
    · exact one a b haW hbW ne ka kb pro fresh hh
    · rw [childTwo_swap _ nd]
      exact one b a hbW haW (Ne.symm ne) kb ka (bin_comm d a.1 b.1 ▸ pro)
        (bin_comm d a.1 b.1 ▸ fresh) hh

theorem rotate_excludedM {T n} {ws : List Sig} (hi : ImpossibleM T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : ImpossibleM T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k t hk ht h
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
  exact hi k t hk ht run

theorem linkedSet_soundM (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, ImpossibleM (targetOf g) k (wideState g k i).toFinset)
    {pair out} (h : wideLinks g k pair = some out) :
    ImpossibleM (targetOf g) k out.toFinset := by
  unfold wideLinks at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excludedM (earlier _ (by omega)) _ (names _ (List.mem_of_getElem? e))

def nodeVerifiedM (g : Forest) (k i : Nat) :=
  let ctx := wideContext g k i
  prelim (targetOf g) ctx && (if k=0 then true else testAllM ctx ctx.2.2.1)

theorem nodeVerified_soundM (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols, Slice (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, ImpossibleM (targetOf g) (k-1) (wideState g (k-1) j).toFinset)
    (checked : nodeVerifiedM g k i = true) : ImpossibleM (targetOf g) k (wideState g k i).toFinset := by
  simp only [nodeVerifiedM,prelim,wideContext,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ wideState g k i := by simpa [wideState] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t u lo hu h
    have ht : t=0 := by omega
    subst t
    generalize he : (wideState g 0 i).toFinset = S at h
    obtain ⟨_,hS,_⟩ := h
    exact hT (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  apply node_soundM (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply wide_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact wideRule_sound g cols h
  · intro tag xs hx
    have e : ((g.index k tag).bind (wideLinks g (k-1)))=some xs := by simpa using enabledLinks_mem hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact linkedSet_soundM g _ names (prior (by omega)) h

def blockM (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerifiedM g k (start+n) && blockM g k start n

theorem block_atM {g k start n} (h : blockM g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    nodeVerifiedM g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [blockM,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)

theorem block_mergeM {g k start a b} (h : blockM g k start a=true)
    (h' : blockM g k (start+a) b=true) : blockM g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [blockM,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,blockM,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩

def checkedTablesM (g : Forest) (top : Nat) :=
  ∀ k ≤ top, blockM g k 0 (g.levels k).1 = true

theorem forest_allM (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower (varsX q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTablesM g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, ImpossibleM (targetOf g) k (wideState g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply nodeVerified_soundM g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_atM (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_soundM g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact block_atM (rows _ hk) i (by omega) (by omega)

def drun (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma drun_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    drun (g :: gs) x = drun gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma gate_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (f1 f2 : ℕ → Bool)
    (h : ∀ r, f1 r = true → f2 r = true) :
    g.op.eval (g.inputs.map f1) = true → g.op.eval (g.inputs.map f2) = true := by
  rcases hop with hop | hop
  · rw [hop]
    simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    exact fun h1 r hr => h r (h1 r hr)
  · rw [hop]
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨r, hr, h1⟩
    exact ⟨r, hr, h r h1⟩

lemma run_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (l1 l2 : List Bool), l1.length = l2.length →
    (∀ i, l1.getD i false = true → l2.getD i false = true) →
    ∀ i, (drun gs l1).getD i false = true → (drun gs l2).getD i false = true := by
  induction gs with
  | nil => intro l1 l2 _ h; exact h
  | cons g gs ih =>
    intro l1 l2 hl h
    rw [drun_cons, drun_cons]
    apply ih (fun g' hg' => hgs g' (by simp [hg']))
    · simp [hl]
    · intro i hi
      rcases lt_trichotomy i l1.length with h1 | h1 | h1
      · rw [List.getD_append _ _ _ _ h1] at hi
        rw [List.getD_append _ _ _ _ (by omega)]
        exact h i hi
      · subst h1
        rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self, List.getD_cons_zero] at hi
        rw [List.getD_append_right _ _ _ _ (by omega), hl, Nat.sub_self, List.getD_cons_zero]
        exact gate_mono g (hgs g (by simp)) _ _ h hi
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
        exact absurd hi (by simp)

lemma ofFn9 (y : Fin 9 → Bool) : List.ofFn y = [y 0, y 1, y 2, y 3, y 4, y 5, y 6, y 7, y 8] := rfl

lemma inp_mono (y1 y2 : Fin 9 → Bool) (h : ∀ i, y1 i = true → y2 i = true) :
    ∀ i, (List.ofFn y1 ++ [y1 0 || y1 3]).getD i false = true →
      (List.ofFn y2 ++ [y2 0 || y2 3]).getD i false = true := by
  intro i hi
  rw [ofFn9] at hi
  rw [ofFn9]
  by_cases hlt : i < 10
  · interval_cases i
    all_goals first
      | exact h _ hi
      | (simp only [List.cons_append, List.nil_append, List.getD_cons_succ, List.getD_cons_zero,
          Bool.or_eq_true] at hi ⊢
         rcases hi with hi | hi
         · exact Or.inl (h 0 hi)
         · exact Or.inr (h 3 hi))
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    exact absurd hi (by simp)

def f9 (x : Fin 9 → Bool) : Bool :=
  [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ)))].any fun (x6 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x x6.1 && x x6.2

def T9 : List ℕ := [3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320]

def F9 : List ℕ := [42, 50, 69, 104, 116, 138, 201, 208, 261, 276, 385, 402]

lemma expand (x : Fin 9 → Bool) : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8] := by
  funext i
  fin_cases i <;> rfl

lemma up_all : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
    f9 ![b0, b1, b2, b3, b4, b5, b6, b7, b8] = true →
      ∃ n ∈ T9, ∀ i : Fin 9, n.testBit i = true → ![b0, b1, b2, b3, b4, b5, b6, b7, b8] i = true := by
  decide +kernel

lemma down_all : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
    f9 ![b0, b1, b2, b3, b4, b5, b6, b7, b8] = false →
      ∃ n ∈ F9, ∀ i : Fin 9, ![b0, b1, b2, b3, b4, b5, b6, b7, b8] i = true → n.testBit i = true := by
  decide +kernel

lemma up (x : Fin 9 → Bool) (h : f9 x = true) :
    ∃ n ∈ T9, ∀ i : Fin 9, n.testBit i = true → x i = true := by
  rw [expand x] at h ⊢
  exact up_all _ _ _ _ _ _ _ _ _ h

lemma down (x : Fin 9 → Bool) (h : f9 x = false) :
    ∃ n ∈ F9, ∀ i : Fin 9, x i = true → n.testBit i = true := by
  rw [expand x] at h ⊢
  exact down_all _ _ _ _ _ _ _ _ _ h

lemma memT : ∀ n ∈ T9, n ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (42 : ℕ), (50 : ℕ), (66 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (132 : ℕ), (138 : ℕ), (160 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (264 : ℕ), (276 : ℕ), (288 : ℕ), (320 : ℕ), (385 : ℕ), (402 : ℕ)] := by
  decide

lemma memF : ∀ n ∈ F9, n ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (42 : ℕ), (50 : ℕ), (66 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (132 : ℕ), (138 : ℕ), (160 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (264 : ℕ), (276 : ℕ), (288 : ℕ), (320 : ℕ), (385 : ℕ), (402 : ℕ)] := by
  decide

lemma FnT : ∀ n ∈ F9, n ∉ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)] := by
  decide

lemma TT : ∀ n ∈ T9, n ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)] := by
  decide


def edgeList : List Nat := [3,6,12,24,17,33,66,132,264,160,320,288]
def independentList : List Nat := [42,50,69,104,116,138,201,208,261,276,385,402]
def givenPins (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 3]
def bitsAt (n : Nat) := fun i : Fin 9 => n.testBit i.val
def edgeValue (x : Fin 9 → Bool) :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)

theorem boundary (C : Circuit) (hm : Monotone2 C)
    (yes : ∀ n ∈ edgeList, C.eval (givenPins (bitsAt n)) = true)
    (no : ∀ n ∈ independentList, C.eval (givenPins (bitsAt n)) = false) :
    ∀ x : Fin 9 → Bool, C.eval (givenPins x) = edgeValue x := by
  have gates : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    simpa using (hm g hg).1
  have mono (x y : Fin 9 → Bool) (sub : ∀ i, x i = true → y i = true) :
      C.eval (givenPins x) = true → C.eval (givenPins y) = true :=
    run_mono C.gates gates _ _ (by simp [givenPins]) (inp_mono x y sub) C.output
  intro x
  have eq : f9 x = edgeValue x := by
    simp only [f9,edgeValue,List.any_cons,List.any_nil,Bool.or_false]
    ac_rfl
  rw [←eq]
  cases cut : f9 x
  · obtain ⟨n,hn,sub⟩ := down x cut
    have hmem : n ∈ independentList := hn
    by_contra bad
    have hp : C.eval (givenPins x) = true := by simpa using bad
    exact Bool.false_ne_true ((no n hmem).symm.trans (mono x (bitsAt n) sub hp))
  · obtain ⟨n,hn,sub⟩ := up x cut
    have all : ∀ n ∈ T9, n ∈ edgeList := by decide
    exact mono (bitsAt n) x sub (yes n (all n hn))
def primary (a : Fin 9) : Sig := inputs.getD a.val zero
def orValue (a b : Fin 9) := bin true (primary a) (primary b)
def orChoice (a b : Fin 9) : Choice := (1, primary a, primary b)
def extra := orValue 0 3
def signedRoots (a b : Fin 9) := inputs ++ [extra, orValue a b]
def legalPair (a b : Fin 9) : Prop :=
  a.val ≠ 0 ∧ a.val ≠ 3 ∧ b.val ≠ 0 ∧ b.val ≠ 3 ∧ a ≠ b
def wit (a b i : Fin 9) : Nat := (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,10,4,2,5,1,1,2,4,8,0,0,0,0,0,0,0,0,0,10,20,2,5,10,1,2,4,8,10,36,2,5,1,130,2,4,8,10,64,2,5,1,1,2,4,8,10,129,2,5,1,1,2,34,8,10,257,2,5,1,1,2,4,10,0,0,0,0,0,0,0,0,0,10,4,2,5,1,1,2,4,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,10,1,18,5,5,1,2,4,8,10,1,34,5,1,5,2,4,8,10,1,72,5,1,1,260,4,8,10,1,128,5,1,1,2,4,8,10,1,258,5,1,1,2,4,36,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,10,20,2,5,10,1,2,4,8,10,1,18,5,5,1,2,4,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,10,1,2,5,40,144,2,4,8,10,1,2,5,65,1,18,4,8,10,1,2,5,129,1,2,20,8,10,1,2,5,257,1,2,4,48,0,0,0,0,0,0,0,0,0,10,36,2,5,1,130,2,4,8,10,1,34,5,1,5,2,4,8,0,0,0,0,0,0,0,0,0,10,1,2,5,40,144,2,4,8,0,0,0,0,0,0,0,0,0,10,1,2,5,1,65,34,4,8,10,1,2,5,1,128,2,32,8,10,1,2,5,1,256,2,4,32,0,0,0,0,0,0,0,0,0,10,64,2,5,1,1,2,4,8,10,1,72,5,1,1,260,4,8,0,0,0,0,0,0,0,0,0,10,1,2,5,65,1,18,4,8,10,1,2,5,1,65,34,4,8,0,0,0,0,0,0,0,0,0,10,1,2,5,1,1,130,68,8,10,1,2,5,1,1,256,4,64,0,0,0,0,0,0,0,0,0,10,129,2,5,1,1,2,34,8,10,1,128,5,1,1,2,4,8,0,0,0,0,0,0,0,0,0,10,1,2,5,129,1,2,20,8,10,1,2,5,1,128,2,32,8,10,1,2,5,1,1,130,68,8,0,0,0,0,0,0,0,0,0,10,1,2,5,1,1,2,260,136,0,0,0,0,0,0,0,0,0,10,257,2,5,1,1,2,4,10,10,1,258,5,1,1,2,4,36,0,0,0,0,0,0,0,0,0,10,1,2,5,257,1,2,4,48,10,1,2,5,1,256,2,4,32,10,1,2,5,1,1,256,4,64,10,1,2,5,1,1,2,260,136,0,0,0,0,0,0,0,0,0] : Array Nat)[a.val*81+b.val*9+i.val]?.getD 0
def posRow (a b i : Fin 9) : Row := Fin.ofNat 512 (wit a b i ||| (1 <<< i.val))
def negRow (a b i : Fin 9) : Row := Fin.ofNat 512 (wit a b i)

set_option maxHeartbeats 0 in
theorem allRaw {a b : Fin 9} (ab : legalPair a b) {k t S}
    (run : Live graph k t S) (ht : t=0) (sub : ∀ w ∈ S, w ∈ signedRoots a b) :
    ∀ i : Fin 9, primary i ∈ S := by
  have data : ∀ a b : Fin 9, legalPair a b → ∀ i : Fin 9,
      bit (posRow a b i) graph && !bit (negRow a b i) graph &&
      (signedRoots a b).all (fun w => w == primary i || !bit (posRow a b i) w || bit (negRow a b i) w)
       = true := by
    unfold legalPair
    decide +kernel
  intro i
  have hr := data a b ab i
  simp only [Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true,Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at hr
  obtain ⟨w,hw,p,q⟩ := mono_row_difference run ht hr.1.1 hr.1.2
  have hh := hr.2 w (sub w hw)
  rcases hh with (eq | hp) | hn
  · exact eq ▸ hw
  · rw [p] at hp
    contradiction
  · rw [q] at hn
    contradiction

def activeRoots (a b : Fin 9) (u v : Bool) :=
  inputs ++ (if u then [extra] else []) ++ (if v then [orValue a b] else [])

theorem active_roots {a b : Fin 9} (ab : legalPair a b) {k S}
    (run : Live graph k 0 S) (sub : ∀ w ∈ S, w ∈ signedRoots a b) :
    ∃ u v : Bool, S = (activeRoots a b u v).toFinset := by
  classical
  have hr := allRaw ab run rfl sub
  have base : ∀ w ∈ inputs, w ∈ S := by
    intro w hw
    rw [←input_list] at hw
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
    exact hr i
  refine ⟨decide (extra∈S),decide (orValue a b∈S),?_⟩
  ext w
  rw [List.mem_toFinset]
  by_cases he : extra∈S <;> by_cases ho : orValue a b∈S <;>
    simp only [activeRoots,he,ho,decide_true,decide_false,Bool.false_eq_true,if_false,if_true,
      List.mem_append,List.mem_singleton,List.not_mem_nil,or_false] <;> constructor
  all_goals first
    | (intro hw; have loc := sub w hw; simp only [signedRoots,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at loc; grind)
    | (intro hw; grind)

def headValue (g : Gate) := gv (inputs ++ [extra]) g
def nameOf (j : Nat) : Fin 10 := if h : j < 9 then ⟨j,by omega⟩ else 9
def nameVal (i : Fin 10) := inputs.getD i.val zero
def legalName (i : Fin 10) := i.val ≠ 0 ∧ i.val ≠ 3
def allowedValue (v : Sig) : Prop := v = zero ∨ v ∈ inputs ∨
  ∃ a b : Fin 9, legalPair a b ∧ v = orValue a b

theorem namesClosed : ∀ u v : Fin 10, legalName u → legalName v →
    allowedValue (bin true (nameVal u) (nameVal v)) := by
  unfold legalName allowedValue legalPair
  decide +kernel

theorem getName {i : Nat} (h : i ≠ 9) :
    (inputs ++ [extra]).getD i zero = nameVal (nameOf i) := by
  by_cases hi : i < 9
  · rw [List.getD_append _ _ _ _ (by change i < 9; exact hi)]
    simp [nameVal,nameOf,hi]
  · rw [List.getD_eq_default _ _ (by change 10 ≤ i; omega)]
    simp [nameVal,nameOf,hi] <;> rfl

theorem legalName_of {i : Nat} (h0 : i ≠ 0) (h3 : i ≠ 3) : legalName (nameOf i) := by
  unfold legalName nameOf
  split <;> simp_all

theorem firstShape (g : Gate) (op : g.op = .or) (len : g.inputs.length ≤ 2)
    (h0 : 0 ∉ g.inputs) (h3 : 3 ∉ g.inputs) (h9 : 9 ∉ g.inputs) :
    allowedValue (headValue g) := by
  obtain ⟨o,ls⟩ := g
  change o = GateOp.or at op
  subst o
  change ls.length ≤ 2 at len
  change 0 ∉ ls at h0
  change 3 ∉ ls at h3
  change 9 ∉ ls at h9
  cases ls with
  | nil => exact Or.inl rfl
  | cons i xs =>
    have ii : legalName (nameOf i) :=
      legalName_of (fun e => by subst i; exact h0 (by simp)) (fun e => by subst i; exact h3 (by simp))
    have ni : i ≠ 9 := fun e => by subst i; exact h9 (by simp)
    cases xs with
    | nil =>
      change allowedValue (bin true ((inputs++[extra]).getD i zero) zero)
      rw [getName ni]
      exact namesClosed _ 9 ii (by unfold legalName; decide)
    | cons j ys =>
      have jj : legalName (nameOf j) := legalName_of
        (fun e => by subst j; exact h0 (by simp))
        (fun e => by subst j; exact h3 (by simp))
      have nj : j ≠ 9 := fun e => by subst j; exact h9 (by simp)
      have empty : ys = [] := by simpa using len
      subst ys
      change allowedValue (bin true _ (bin true _ zero))
      simp only [getName ni,getName nj,(bin_laws _).2.1]
      exact namesClosed _ _ ii jj
def witnessM (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b

private lemma bin_repM {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witnessM w (bin d a b) := by
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
  exact Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩

private lemma gate_repM (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ witnessM w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  cases l with
  | nil =>
    rcases ho with rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witnessM w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witnessM w (w.getD i zero)) (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_repM false (get_rep w i) (get_rep w j)
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_repM true (get_rep w i) (get_rep w j)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.


private lemma pull_gateM {w : List Sig} {z : Sig} {k S} (h : Live target k 0 S)
    (hz : represented w z ∨ witnessM w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+1 ∧ Live target k' 0 S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live target k 0 (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
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
        exact ⟨_,_,Nat.le_refl _,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extractM (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length≤2)
    (hp : proper target) (hout : target ∈ execute gs w) :
    ∃ k S, k ≤ gs.length ∧ Live target k 0 S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,T,hl,hu,hT⟩ := pull_gateM ht (gate_repM w g (legal g (by simp))) hs
    exact ⟨l,T,by simp; omega,hu,hT⟩

theorem simulates {T : Sig} (Q : Sig → Sig → Prop)
    (closed : ∀ d a b x y, Q a x → Q b y → Q (bin d a b) (bin d x y))
    {k t S} (run : Live T k t S) (ht : t=0)
    (v : List Sig) (hv : v.Nodup) (eqv : v.toFinset=S) (rep : Sig → Sig)
    (sound : ∀ x ∈ v, Q x (rep x)) :
    ∃ z, Q T z ∧ Run (observe z) k (v.map (fun x => observe (rep x))) := by
  classical
  induction run using Live.ind generalizing v rep with
  | stop hp =>
    have perm : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa using eqv.symm
    exact ⟨rep T,sound T (perm.mem_iff.mp (by simp)),Run.perm (perm.map _) Run.stop⟩
  | unary _ _ _ _ => omega
  | @binary k u U a b d ha hb hab fresh htail ih =>
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
    have eqTail : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (eqTail ▸ List.mem_toFinset.mpr hz)))
    let updated (s : Sig) := if s=bin d a b then bin d (rep a) (rep b) else rep s
    have memA : a ∈ v := List.mem_toFinset.mp (by rw [eqv]; simp)
    have memB : b ∈ v := List.mem_toFinset.mp (by rw [eqv]; simp)
    have trans : ∀ w ∈ bin d a b :: tail, Q w (updated w) := by
      intro w hw
      rcases List.mem_cons.mp hw with rfl | tt
      · simpa [updated] using closed d a b (rep a) (rep b) (sound a memA) (sound b memB)
      · have ne : w ≠ bin d a b := fun eq => hf (eq ▸ tt)
        have ov : w ∈ v := by
          apply List.mem_toFinset.mp
          rw [eqv]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (eqTail ▸ List.mem_toFinset.mpr tt))
        simpa [updated,ne] using sound w ov
    obtain ⟨z,ok,future⟩ := ih ht (bin d a b :: tail) (List.nodup_cons.mpr ⟨hf,nd⟩)
      (by simp [eqTail]) updated trans
    have unchanged : tail.map (fun x => observe (updated x)) = tail.map (fun x => observe (rep x)) := by
      apply List.map_congr_left
      intro x hx
      simp [updated,show x ≠ bin d a b from fun eq => hf (eq ▸ hx)]
    rw [List.map_cons,unchanged] at future
    change Run (observe z) k (observe (updated (bin d a b)) :: (kept ka a (kept kb b rest)).map _) at future
    simp only [updated,ite_true,obs_bin,map_kept] at future
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact ⟨z,ok,Run.perm (perm.map _) (Run.two d ka kb future)⟩
def sampleLe (raw : List Sig) (r s : Row) :=
  raw.all (fun v => !bit r v || bit s v)
def rawMonotone (raw : List Sig) (v : Sig) : Prop :=
  ∀ r s : Row, sampleLe raw r s = true → bit r v = true → bit s v = true

theorem mono_input {raw v} (hv : v ∈ raw) : rawMonotone raw v := by
  intro r s le h
  have ok := List.all_eq_true.mp le v hv
  simpa [h] using ok

theorem mono_both {raw a b} (d : Bool) (ha : rawMonotone raw a) (hb : rawMonotone raw b) :
    rawMonotone raw (bin d a b) := by
  intro r s le
  cases d <;> simp only [bit_bin,Bool.false_eq_true,if_false,if_true,Bool.or_eq_true,Bool.and_eq_true]
  · exact fun h => ⟨ha r s le h.1,hb r s le h.2⟩
  · exact fun h => h.elim (fun h => Or.inl (ha r s le h)) (fun h => Or.inr (hb r s le h))

def sampleRelation (raw : List Sig) (p n : List Row) (a b : Sig) : Prop :=
  rawMonotone raw b ∧ (∀ r ∈ p, bit r a = true → bit r b = true) ∧
    ∀ r ∈ n, bit r b = true → bit r a = true

theorem relation_bin {raw p n} (d a b x y)
    (ax : sampleRelation raw p n a x) (by' : sampleRelation raw p n b y) :
    sampleRelation raw p n (bin d a b) (bin d x y) := by
  refine ⟨mono_both d ax.1 by'.1,?_,?_⟩
  · intro r hr
    cases d <;> simp only [bit_bin,Bool.false_eq_true,if_false,if_true,Bool.or_eq_true,Bool.and_eq_true]
    · exact fun h => ⟨ax.2.1 r hr h.1,by'.2.1 r hr h.2⟩
    · exact fun h => h.elim (fun h => Or.inl (ax.2.1 r hr h)) (fun h => Or.inr (by'.2.1 r hr h))
  · intro r hr
    cases d <;> simp only [bit_bin,Bool.false_eq_true,if_false,if_true,Bool.or_eq_true,Bool.and_eq_true]
    · exact fun h => ⟨ax.2.2 r hr h.1,by'.2.2 r hr h.2⟩
    · exact fun h => h.elim (fun h => Or.inl (ax.2.2 r hr h)) (fun h => Or.inr (by'.2.2 r hr h))

def extremalGeometry (raw : List Sig) (p n : List Row) (goal sub : Sig) :=
  p.all (fun r => bit r goal) && n.all (fun r => !bit r goal) &&
  (List.finRange 512).all (fun r =>
    if bit r sub then p.any (fun u => sampleLe raw u r) else n.any (fun u => sampleLe raw r u))

theorem terminal_relation {raw p n goal sub z} (check : extremalGeometry raw p n goal sub = true)
    (rel : sampleRelation raw p n goal z) : z = sub := by
  simp only [extremalGeometry,Bool.and_eq_true,List.all_eq_true] at check
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let r : Row := ⟨i,hi⟩
  change bit r z = bit r sub
  have h := check.2 r (List.mem_finRange r)
  cases hv : bit r sub
  · simp only [hv,Bool.false_eq_true,if_false] at h
    obtain ⟨u,hu,le⟩ := List.any_eq_true.mp h
    cases hz : bit r z
    · rfl
    have f := rel.2.2 u hu (rel.1 r u le hz)
    have bad := check.1.2 u hu
    simp [f] at bad
  · simp only [hv,if_true] at h
    obtain ⟨u,hu,le⟩ := List.any_eq_true.mp h
    exact rel.1 u r le (rel.2.1 u hu (check.1.1 u hu))

theorem approximateCut {raw p n goal sub paid bank bound cap} {ws : List Sig}
    (geo : extremalGeometry raw p n goal sub = true) (properSub : proper sub)
    (lower : Lower raw sub bound)
    (paidFor : Reach (raw.map observe) paid bank) (rep : Sig → Sig)
    (agreement : ∀ w ∈ ws, sampleRelation raw p n w (rep w))
    (canRead : ∀ w ∈ ws, Available bank (observe (rep w)))
    (small : cap+paid < bound+(ws.map rep).countP (isMaskedConstant one))
    (nd : ws.Nodup) : ImpossibleM goal cap ws.toFinset := by
  intro k t hk ht run
  obtain ⟨z,rel,hz⟩ := simulates (sampleRelation raw p n) relation_bin run ht ws nd rfl rep agreement
  have eq := terminal_relation geo rel
  subst z
  have cover : supply bank (ws.map (fun w => observe (rep w))) := by
    intro a ha
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp ha
    exact canRead w hw
  obtain ⟨l,out,built,last,size⟩ := contraction (observe_proper properSub) hz _ paidFor cover
  have boundLe := lower l out built last
  have count := count_constants (d:=one) (f:=id) (fun r => bit_one r) (ws.map rep)
  have eqm : ((ws.map rep).map observe).map (restrictRows id) = ws.map (fun w => observe (rep w)) := by
    simp only [List.map_map]
    rfl
  rw [eqm] at count
  omega
abbrev SimpleGate := Bool × Nat × Nat
def simpleValue (raw : List Sig) (g : SimpleGate) :=
  bin g.1 (raw.getD g.2.1 zero) (raw.getD g.2.2 zero)
def auxBank (raw : List Sig) (cs : List SimpleGate) := cs.map (simpleValue raw) ++ raw
def choicesFor (raw : List Sig) (cs : List SimpleGate) := zero :: one :: auxBank raw cs

theorem default_available (raw : List Sig) (i : Nat) {bank : List (Wire Row)}
    (hr : ∀ a ∈ raw, Available bank (observe a)) : Available bank (observe (raw.getD i zero)) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : raw[i]? with
  | none => exact Or.inr ⟨false,funext bit_zero⟩
  | some a => exact hr a (List.mem_of_getElem? h)

theorem buySmall (raw : List Sig) (cs : List SimpleGate) :
    ∃ bank, Reach (raw.map observe) cs.length bank ∧ ∀ a ∈ auxBank raw cs, Available bank (observe a) := by
  induction cs with
  | nil =>
    exact ⟨_,Reach.start,fun a ha => Or.inl (List.mem_map.mpr ⟨a,ha,rfl⟩)⟩
  | cons c cs ih =>
    obtain ⟨bank,built,haveA⟩ := ih
    have rawIn : ∀ a ∈ raw, Available bank (observe a) :=
      fun a ha => haveA a (List.mem_append.mpr (Or.inr ha))
    have result := Reach.two c.1 built (default_available raw c.2.1 rawIn) (default_available raw c.2.2 rawIn)
    refine ⟨_,result,?_⟩
    intro v hv
    change v ∈ simpleValue raw c :: auxBank raw cs at hv
    rcases List.mem_cons.mp hv with rfl | old
    · exact Or.inl (by simp [simpleValue,obs_bin])
    · exact available_cons _ (haveA _ old)

theorem on_sources {raw : List Sig} (cs : List SimpleGate) :
    ∀ v ∈ choicesFor raw cs, rawMonotone raw v := by
  intro v hv
  simp only [choicesFor,List.mem_cons,auxBank,List.mem_append,List.mem_map] at hv
  rcases hv with rfl | rfl | ⟨c,_,rfl⟩ | hr
  · intro r s _ no
    rw [bit_zero] at no
    contradiction
  · intro r s _ _
    exact bit_one _
  · have source (i : Nat) : rawMonotone raw (raw.getD i zero) := by
      rw [List.getD_eq_getElem?_getD]
      cases h : raw[i]? with
      | some a => exact mono_input (List.mem_of_getElem? h)
      | none =>
        intro r s _ no
        change bit r zero = true at no
        rw [bit_zero] at no
        contradiction
    exact mono_both c.1 (source _) (source _)
  · exact mono_input hr

def readChoice (sources : List Sig) (indices : Nat) (live : List Sig) (a : Sig) :=
  sources.getD ((indices >>> (4*live.idxOf a)) &&& 15) zero

theorem readChoice_mem (raw cs i live a) : readChoice (choicesFor raw cs) i live a ∈ choicesFor raw cs := by
  unfold readChoice
  rw [List.getD_eq_getElem?_getD]
  cases h : (choicesFor raw cs)[(i >>> (4*live.idxOf a)) &&& 15]? with
  | none => exact List.mem_cons_self
  | some v => exact List.mem_of_getElem? h

def betterB (pm nm a b : Sig) := (pm &&& a &&& ~~~b == zero) && (nm &&& b &&& ~~~a == zero)
theorem better_pos {m a b : Sig} (eq : m &&& a &&& ~~~b = zero) (r : Row) (hm : bit r m = true) :
    bit r a = true → bit r b = true := by
  intro ha
  have e := congrArg (bit r) eq
  cases hb : bit r b
  · simp [bit,zero,BitVec.getLsbD_and,BitVec.getLsbD_not,r.isLt] at e hm ha hb
    simp_all
  · rfl

def cutTest (pm nm : Sig) (raw : List Sig) (cs : List SimpleGate)
    (idx k L : Nat) (ws : List Sig) :=
  let rep := readChoice (choicesFor raw cs) idx ws
  ws.all (fun a => betterB pm nm a (rep a)) &&
    decide (k+cs.length<L+(ws.map rep).countP (isMaskedConstant one))

theorem cutTest_sound {raw goal sub bound pm nm p n k ws cs idx}
    (geo : extremalGeometry raw p n goal sub = true) (hp : proper sub)
    (lower : Lower raw sub bound) (pmem : ∀ r ∈ p, bit r pm=true) (nmem : ∀ r ∈ n, bit r nm=true)
    (nd : ws.Nodup) (verified : cutTest pm nm raw cs idx k bound ws = true) : ImpossibleM goal k ws.toFinset := by
  simp only [cutTest,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at verified
  obtain ⟨bank,built,values⟩ := buySmall raw cs
  apply approximateCut geo hp lower built (readChoice (choicesFor raw cs) idx ws) _ _ verified.2 nd
  · intro a ha
    have eq := verified.1 a ha
    simp only [betterB,Bool.and_eq_true,beq_iff_eq] at eq
    refine ⟨on_sources cs _ (readChoice_mem raw cs idx ws a),?_,?_⟩
    · intro r hr
      exact better_pos eq.1 r (pmem r hr)
    · intro r hr
      exact better_pos eq.2 r (nmem r hr)
  · intro a ha
    have known := readChoice_mem raw cs idx ws a
    simp only [choicesFor,List.mem_cons] at known
    unfold choicesFor
    rcases known with h | h | h
    · rw [h]
      exact Or.inr ⟨false,funext bit_zero⟩
    · rw [h]
      exact Or.inr ⟨true,funext bit_one⟩
    · exact values _ h
structure SampleCert (S : Finset Sig) (r : Row) (T : Sig) (side : Bool) (P : Sig → Prop) : Prop where
  belongs : ∀ w, P w → w ∈ S
  holds : ∀ w, P w → bit r w = side
  forces : ∀ t, (∀ w, P w → bit t w = side) → bit t T = side

def childCert (d side : Bool) (r : Row) (a b w : Sig) : Prop :=
  if d != side then w=a ∨ w=b else w=(if bit r a=side then a else b)

theorem child_in {d side r a b w} (h : childCert d side r a b w) : w=a ∨ w=b := by
  unfold childCert at h
  split at h
  · exact h
  · split at h
    · exact Or.inl h
    · exact Or.inr h

theorem child_holds {d side r a b} (gate : bit r (bin d a b)=side) :
    ∀ w, childCert d side r a b w → bit r w=side := by
  cases d <;> cases side <;> cases ha : bit r a <;> cases hb : bit r b <;>
    simp_all [childCert,bit_bin]

theorem child_forces (d side r t a b)
    (h : ∀ w, childCert d side r a b w → bit t w=side) : bit t (bin d a b)=side := by
  have ha := h a
  have hb := h b
  cases d <;> cases side <;> cases hs : bit r a <;> simp_all [childCert,bit_bin]

theorem child_inter (d : Bool) (p n a b x y)
    (hx : childCert d true p a b x) (nx : childCert d false n a b x)
    (hy : childCert d true p a b y) (ny : childCert d false n a b y) : x=y := by
  cases d
  · have a₁ : x=(if bit n a=false then a else b) := by simpa [childCert] using nx
    have a₂ : y=(if bit n a=false then a else b) := by simpa [childCert] using ny
    exact a₁.trans a₂.symm
  · have a₁ : x=(if bit p a=true then a else b) := by simpa [childCert] using hx
    have a₂ : y=(if bit p a=true then a else b) := by simpa [childCert] using hy
    exact a₁.trans a₂.symm

def expandCert (P : Sig → Prop) (z : Sig) (localP : Sig → Prop) (w : Sig) : Prop :=
  (P w ∧ w ≠ z) ∨ (P z ∧ localP w)

theorem expand_ok {T U r side P a b d}
    (old : SampleCert (insert (bin d a b) U) r T side P) :
    SampleCert (insert a (insert b U)) r T side
      (expandCert P (bin d a b) (childCert d side r a b)) := by
  constructor
  · intro w hw
    rcases hw with ⟨prior,ne⟩ | ⟨_,kid⟩
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ((Finset.mem_insert.mp (old.belongs _ prior)).resolve_left ne))
    · rcases child_in kid with rfl | rfl <;> simp
  · intro w hw
    rcases hw with ⟨prior,_⟩ | ⟨atGate,kid⟩
    · exact old.holds _ prior
    · exact child_holds (old.holds _ atGate) _ kid
  · intro t ht
    apply old.forces
    intro w hw
    by_cases eq : w=bin d a b
    · subst w
      exact child_forces _ _ _ _ _ _ (fun u kid => ht u (Or.inr ⟨hw,kid⟩))
    · exact ht _ (Or.inl ⟨hw,eq⟩)

def thin (P N : Sig → Prop) : Prop := ∀ x y, P x → N x → P y → N y → x=y

theorem expand_thin {P N : Sig → Prop} {a b d p n} {U : Finset Sig}
    (h : thin P N) (aout : a ∉ U) (bout : b ∉ U)
    (pm : ∀ w, P w → w ∈ insert (bin d a b) U) (nm : ∀ w, N w → w ∈ insert (bin d a b) U) :
    thin (expandCert P (bin d a b) (childCert d true p a b))
      (expandCert N (bin d a b) (childCert d false n a b)) := by
  let z := bin d a b
  have outside (x : Sig) (hx : x ∈ U) (s : Bool) (r : Row) :
      ¬childCert d s r a b x := by
    intro work
    rcases child_in work with rfl | rfl <;> contradiction
  have splitOne (x : Sig) (px : expandCert P z (childCert d true p a b) x)
      (nx : expandCert N z (childCert d false n a b) x) :
      (P x ∧ N x ∧ x≠z) ∨ (P z ∧ N z ∧ childCert d true p a b x ∧ childCert d false n a b x) := by
    rcases px with ⟨u,ne⟩ | ⟨u,c⟩ <;> rcases nx with ⟨v,nx⟩ | ⟨v,e⟩
    · exact Or.inl ⟨u,v,ne⟩
    · exact False.elim ((outside _ ((Finset.mem_insert.mp (pm _ u)).resolve_left ne) _ _) e)
    · exact False.elim ((outside _ ((Finset.mem_insert.mp (nm _ v)).resolve_left nx) _ _) c)
    · exact Or.inr ⟨u,v,c,e⟩
  intro x y xp xn yp yn
  rcases splitOne x xp xn with ⟨px,nx,ex⟩ | ⟨pz,nz,cx,dx⟩ <;>
    rcases splitOne y yp yn with ⟨py,ny,ey⟩ | ⟨qz,mz,cy,dy⟩
  · exact h _ _ px nx py ny
  · exact False.elim (ex (h _ _ px nx qz mz))
  · exact False.elim (ey (h _ _ py ny pz nz))
  · exact child_inter _ _ _ _ _ _ _ cx dx cy dy

theorem tight_certs {T k t S} (run : Live T k t S) (mono : t=0) (tight : S.card=k+1)
    (p n : Row) (hp : bit p T=true) (hn : bit n T=false) :
    ∃ P N, SampleCert S p T true P ∧ SampleCert S n T false N ∧ thin P N := by
  classical
  induction run using Live.ind with
  | stop properT =>
    let P : Sig → Prop := fun w => w=T
    refine ⟨P,P,?_,?_,?_⟩
    · exact ⟨fun w eq => eq ▸ Finset.mem_singleton_self _,fun w eq => eq ▸ hp,fun r h => h _ rfl⟩
    · exact ⟨fun w eq => eq ▸ Finset.mem_singleton_self _,fun w eq => eq ▸ hn,fun r h => h _ rfl⟩
    · exact fun _ _ h _ j _ => h.trans j.symm
  | unary _ _ _ _ => omega
  | @binary k t U a b d ha hb hab fresh tail ih =>
    have hz : bin d a b ∉ U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have tailSize := (live_size tail).2
    rw [Finset.card_insert_of_notMem hz] at tailSize
    have first := Finset.card_insert_le a (insert b U)
    have second := Finset.card_insert_le b U
    have aout : a ∉ insert b U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight
      omega
    have bout : b ∉ U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight first
      omega
    have eq : (insert (bin d a b) U).card=k+1 := by
      rw [Finset.card_insert_of_notMem hz]
      omega
    obtain ⟨P,N,pv,nv,un⟩ := ih mono eq
    exact ⟨_,_,expand_ok pv,expand_ok nv,expand_thin un (fun h => aout (Finset.mem_insert_of_mem h)) bout pv.belongs nv.belongs⟩
def oneDifference (T : Sig) (ws : List Sig) (p n : Row) (v : Sig) :=
  bit p T && !bit n T &&
    ws.all (fun w => w==v || !bit p w || bit n w)

theorem oneDifference_pos {T ws p n v} (o : oneDifference T ws p n v = true) :
    bit p T=true := by
  simp only [oneDifference,Bool.and_eq_true] at o
  exact o.1.1

theorem oneDifference_neg {T ws p n v} (o : oneDifference T ws p n v = true) :
    bit n T=false := by
  simp only [oneDifference,Bool.and_eq_true,Bool.not_eq_true'] at o
  exact o.1.2

theorem force_pos {T p n v P} {ws : List Sig} (c : SampleCert ws.toFinset p T true P)
    (o : oneDifference T ws p n v = true) : P v := by
  classical
  by_contra absent
  have bad := oneDifference_neg o
  simp only [oneDifference,Bool.and_eq_true,List.all_eq_true,Bool.or_eq_true,Bool.not_eq_true',beq_iff_eq] at o
  have hit : bit n T=true := c.forces n (by
    intro w hw
    have ans := o.2 w (List.mem_toFinset.mp (c.belongs _ hw))
    have pos := c.holds _ hw
    rcases ans with (he | nope) | ok
    · exact False.elim (absent (he ▸ hw))
    · simp [pos] at nope
    · exact ok)
  simp [hit] at bad

theorem force_neg {T p n v N} {ws : List Sig} (c : SampleCert ws.toFinset n T false N)
    (o : oneDifference T ws p n v = true) : N v := by
  classical
  by_contra absent
  have good := oneDifference_pos o
  simp only [oneDifference,Bool.and_eq_true,List.all_eq_true,Bool.or_eq_true,Bool.not_eq_true',beq_iff_eq] at o
  have hit : bit p T=false := c.forces p (by
    intro w hw
    have ans := o.2 w (List.mem_toFinset.mp (c.belongs _ hw))
    have zero' := c.holds _ hw
    rcases ans with (he | ok) | nope
    · exact False.elim (absent (he ▸ hw))
    · exact ok
    · simp [zero'] at nope)
  simp [hit] at good

def tightTest (T : Sig) (k : Nat) (ws : List Sig) (p n ni nj pi pj : Row) (a b : Sig) :=
  decide (ws.toFinset.card=k+1) && (a != b) && oneDifference T ws p ni a &&
    oneDifference T ws p nj b && oneDifference T ws pi n a && oneDifference T ws pj n b

theorem tightTest_sound {T k ws p n ni nj pi pj a b}
    (h : tightTest T k ws p n ni nj pi pj a b = true) : ImpossibleM T k ws.toFinset := by
  intro j t small mono live
  simp only [tightTest,Bool.and_eq_true,decide_eq_true_eq,bne_iff_ne] at h
  obtain ⟨⟨⟨⟨⟨size,ne⟩,pa⟩,pb⟩,na⟩,nb⟩ := h
  have lim := (live_size live).2
  have eq : ws.toFinset.card=j+1 := by omega
  obtain ⟨P,N,pc,nc,thin'⟩ := tight_certs live mono eq p n (oneDifference_pos pa) (oneDifference_neg na)
  exact ne (thin' _ _ (force_pos pc pa) (force_neg nc na) (force_pos pc pb) (force_neg nc nb))
def nd5 (i : Nat) : Nat := 0x60650317838f158734b59e30d0081
def level5 : Packing := (1,10,0,0,0,0,1,nd5)
def nd6 (i : Nat) : Nat := 0x20002021e50c1c78ac39a5acf1868040e8ca062cf158734b59e30d0081
def level6 : Packing := (2,9,0,0,0,4,1,nd6)
def nd7 (i : Nat) : Nat := 0x202038ca862ec39a5acf1868040d7940f158734b59e30d0081
def level7 : Packing := (2,8,0,0,0,4,1,nd7)
def nd8 (i : Nat) : Nat := 0x4000000061440c204013ce8736c3d678c34020799d0c5d87acf1868040eb6a18b34b59e30d0081de54b0e696b3c61a010327e4736c4543ac4501460fd8e6d8ba87408a028e1f31acac950e8114051
def level8 : Packing := (7,7,0,0,0,6,1,nd8)
def nd9 (i : Nat) : Nat := 0x10064620103101be080000000000000000000000000000000000000000000340530294100000000680a605282d01900a50400000000000000000000000000000000000000000000000000000148511404f1384d1304b10ec2b06c0afebeaf6bcaeebaae6b8adeb6ad6b4aceb2ac6b0abeaeab6a8c9f26c9724c7f9b06819060170581505013048110400f0380d0300b02809020070180501003008010007e74b4e62e30d0081bde969cc5c61a010379d2d398b8c340206f7a5a23171868040eef430462e30d0081bde86b2b3c61a0103dbd0c5d678c340207f3a587acf1868040ded434b59e30d0081fdc862c92461a0103f390a49248c340207f521462491868040fce4a4c49230d0081fdc939892461a0103f392911248c340206f7a1acac51868040cef435958a30d0081d6bd50cc2d67a00e3bd7220985acf401c7e6c949a0528a80a8fe992cd40a5150151f9b3492814a2a02a3fb249250294540547f6c140a0528a80a8fed890140a5150151c7dd61ab2543280a3cf9a61d64a86501471f7582ac950ca028f3e68c5592a194051e7a528aa1d62280a3dbe280d88ac4501479f9588a87588a028f3d2b0b50eb114051e7e1406a1d62280a38fbac5564a04501465fb1aca87408a028e3f6b1750e8114051e7cd592a1d02280a3cfcab1543a04501479f618aac9404a028e7ecb0f5928094051e7d951eb2501280a3deb0c3564a02501479f6546ac9404a028f6eca0d5928094051ef99316b2501280a3cfb2a1d64a02501479f2543ac9404a028f3ec2855928094051edd940ab2501280a3df3251564a02501479e91aba8728a2028fbd231350e5144051e7a55a2a1ca2880a3ef089254394510147fac1a79454062028ffc824928a80c4051f7a150e51501880a3ff4241ca2a0310147de91ab94728a2010dbd2b4328e5144021f7a540651ca288043f7c282c618c110087ff04e62491862010ffe0a0a49230c4021
def level9 : Packing := (65,6,7,0,0,10,1,nd9)
def nd10 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0xeda49283ce121fdd641d079c243fbccc2a0f38487f7ca0141e7090fef920283ce121fde6205079c243efd506a4f10087dfaa0949e2010fbf540e93c4021f7ea80d27880439fd18ba8b10087bfa3135162010f7f4622a2c4021efe8b454588043dfd128a8b10087b7a30f5162010f7f541ea2c4021efea8354588043dfd505a8b10087bfaa095162010f7f5312a2c4021efea81d4588043dfd4a3a8b10087bf29075162010f7f5406a2c4021f7aa9412488043ef552724910087feaa0e4922010ffd54189244021ffaa7312488043df554524910087dea24a4922010ffd54149244021f7aa9092488043ff550124910087ff231728e2010ffe562a51c4021ffc8c54a388043ff916a94710087ff231328e2010ffe452651c4021ffcac44a388043ff918894710087ff22d128e2010ffe552251c4021ffc8a44a388043ff912894710087ff2b0f28e2010ffe551e51c4021ffca83ca388043ff958694710087ff2a8d28e2010ffe541a51c4021ffca734a388043ff954594710087bf2a8b28e2010ffe541651c4021ff4a82ca388043ff958494710086ff2b0928e2010ffe551251c4021ff88924a388043ff950494710087ff29c928e2010ffe531251c4021ff4a524a388043ff958194710087ff2a0328e2010fbf462290c4021f7ea83d2188043cfd545a4310087dfaa0b4862010fbd461290c4021f7ea8252188043efd503a4310087dfa9474862010fbf138690c4021f7e250d2188043efc481a4310087ff82d13862010fff04a270c4021fde2b3ce188043fbc5079c310087ff8a0d3862010fef139a70c4021efe2a2ce188043ffc5059c310087ff898b3862010ffd049270c4021ffe2824e188043ffc4c49c310087ff89493862010fff140e70c4021ffe251ce188043ff84a39c310087ff09073862010fbf162630c4021bfe2c3c6188043efc5278c310087ff82cb1862010fff141630c4021ffe272c6188043ffc4c58c310087ff0a071862010ffe138e30c4021ffc261c6188043ff84a38c310087ff22511862010ffe541e30c4021bfcac2c6188043df95458c310087ff2a0b1862010dfe561230c4021ff889246188043ff95048c310087ff0a031862010ffe138630c4021ffc250c6188043ff84818c310087ff03171862010ffe15aa30c4021ffc0b546188043ff85698c310087ff02d31862010ffe152630c4021ffc0a4c6188043ff85868c310087ff0acd1862010ffe151a30c4021ffc29346188043ff84e68c310087ff0b0b1862010ffe061630c4021ffc2b2c6188043ff81658c310087ff0a8b1862010ffe051630c4021ffc292c6188043ff81258c310087ff0a0b1862010ffe041630c4021ffc272c6188043ff84c58c310087ff0ac91862010ffe151230c4021ffc29246188043ff01248c310087ff09891862010ffe129230c4021 else 0xfab0d588a028e7f551ab114051dfea83562280a3bfd4e6ac4501477fab0b588a028efb5616b114051dfea82d62280a3bed4c5ac4501477fab07588a028eff550eb114051dfcaa1d62280a39fd543ac4501473f2a87588a028eff540eb114051dfea71d62280a3bfd4c3ac4501477fa947588a028efe528eb114051dfeac0d62280a3bfd501ac4501477f89c3588a028eff5186b114051dfca30d62280a33ff58ba0450146bfeb15408a028efdd5928114051efdaa1d02280a3bfd562a0450147bfc315404a028edf95a28094051bff2c3d01280a3dfe547a0250147fbc30d404a028f7f951a8094051fbf283501280a3fee4c5a02501477ecac9404a028f7f950e8094051efd2a1d01280a3bfe562a02501477f8ac5404a028f7f850a8094051fbf281501280a3fee4a2a02501473feb105aa2028c7fd620b544051cffa8396a880a39df5862d5101473fea0c5aa2028e7fd398b544051cf7ac296a880a39ff5052d5101473eeb085aa2028e7dc490b544051cfdac196a880a39ff5032d5101473fe9c65aa2028e7fd30cb544051cffa5196a880a39fb4a32d5101473f69065aa2028e7f5608b544051cffa6116a880a39ff4a22d5101473fea025aa2028e7fd184b544051cfda3096a880a31ff18aad1101473f631750e2028e7ed5a2a1c4051efda73543880a3dfb505a87101473f6ac950e2028f7cc492a1c4051efda51543880a3deb4a2a87101473fe2d540a2028ffb46265144051ff68c44a2880a3fed16894510147fdaa9128a2028ffb44a25144051fd68c3ca2880a3ded54794510147fdaa0f28a2028ffb541a5144051ff6a734a2880a3fe512494510147fdaa0928a2028ffb53925144051ff6a624a2880a3fed54394510147fd2a8728a2028f7b550e5144051ef4aa1ca2880a3fed50394510147fd290728a2028ffb54065144051ff4a30ca2880a3bfe16aa03101473fc2d54062028eff959280c4051ffb092501880a3dfa543a0310147ff49074062028fff150a80c4051fbf281501880a3fee4a2a0310147fd89454062028fff120a80c4051ffd273461a0083ffa5058c340107ff49cb1868020ffe931630d0041ffd271461a0083ffa4c28c340107ff49451868020ebf862e90c4041f7f283d2188083efe506a4310107dfca0b4862020efe95a230c4041ffd283c6188083ffa5068c310107ff49cd1862020ffe941630c4041ffd272c6188083ffa4c58c310107ff09451862020c7ff62e814a121efd8c5ca388043de94a3945100872fead14062010d7fd61680c4021efda51d0188043dfd4a2a0310087bfc9434062010d7ed61630c4021efda82c6188043dfa5018c310087df9a0b1862010f3f55163044021f7ea82c6088043ef94a38c110087df08c31822010c3ff622b294921f5f6a4d079c243ebed28a0f38487d7da4941e7090f) else (if i < 3 then 0xa1628c340207ef4a451868040fde848a30d0081fbd271461a0103f7a0a28c340207ef49051868040d3df622a492471a7bec3549248e34f7d85a92491c79efa0b5249238f3cf28ea492471a7bec1549248e3cf5982a92491c79ee8815249238fade6268392471edbea3507248e3eb7d26a0e491c6f6fb0541c9238fadf48a8392471f5be90d07248e3fb6ca1a0e491c6f5e30b59e8038f6fd50eb3d0071fdf220d67a00e3dbf545a0f401c7d7ea4b41e8038fcfd41683d0071ddfab2507a00e3fb7124a0f401c7e7ea0941e8038feed20e83d0071bdfac1507a00e3f3f502a0f401c7e7ea0341e8038fef928683d0071fdda30d07a00e3dbf543a01381c7f7c8834027038f6fc5aa83c4071ddfab4507880e3bbf564a0f101c7f6e24941e2038feed20e83c4071fdea41507880e3ebf521a0f101c7f768c341e2038fef510683c407187fec5d43880a38ffd68a87101471f7acc5a6a1a8e3ef588b4d4351ef9e73124a86a35fb5822c150d473efad44928128d7fc62ab050251d6f6b4966a02a3bded672cd40547dbda4e59a80a8fb7b490b350151def6b1966a02a3fdac832cd405477bd2c459a80a8fb7b488b350151fef240166a02a3ef696924940547ded29249280a8efdb59c9250151f7b693924a02a3fd696624940547beda8c49280a8fbdb4989250151fbb683124a02a3fe6cc524940547deda4449280a8f3ea626a1d0151efd4b4d43a02a3df2924a8740547bf430150e80a8f7e9202a1d0151f3f4a4d02a02a3f5e966a0540547afda8d40a80a8f9fb4928150151fbb492502a02a3e7ed22a0540547efc90140a80a8fbba5265150151fe74b34a2a02a3eeed2494540547fcd24928a80a8f7ab50e5150151ff5641ca2a02a3eeed2294540547edda0528a80a8fdb340a5150151ff66714a2a02a3fee480945405473eea93590a028e7dd51ab214051dfba73564280a3bf7543ac8501477e6a87590a028efdd30eb214051dfbaa1564280a39f7542ac8501473ee285590a028efdc40ab214051dfba71564280a3bf74c2ac8501477ee8c5590a028efdd406b214051dfb270d64280a3bf7461ac8501477e68c3590a028efdd106b214051affac3543280a39f7564a8650147bf698750ca028d7fd60aa194051efda31543280a39f3564a86501463fe315588a028e7fd526b114051cffaa4562280a39ff148ac4501473fea8f588a028e7fd51ab114051df7a62d62280a39ff543ac4501473f6a87588a028efed28eb114051cfe8a1562280a3bfd102ac4501477fa9c5588a028eff530ab114051dfea51562280a3bfd462ac4501477fc9c3588a028eff5106b114051dfeac5562280a39fd549ac4501477fab11588a028eff4622b114051dfeaa4562280a39fd548ac4501473fa291588a028eff561eb114051cfeaa3d62280a3bfd507ac4501477 else (if i < 4 then 0x4c4e6253119884c3e61d30d9864c2e6153099844c1e60d3059824c0e5f2ef877bbbd9deaef4779bbc9de2ef0777bbb9ddaeec775bba9dd2ee8773bb99dcaee4771bb89dc2ee076fbb79dbaedc76dbb69db2ed2568ab4159eace566ab31596aca564ab2158eac6562ab11586ac2560ab0157eabe55eaaf1576aba55caae156eab655aaad1566ab2558aac155eaa55522a8d544a82940ca024ff27e93ec9f24f727a93cc9e24ef27693ac9d24e7272938c9c24df26e936c964cb065732b18c646122f91748b645922b91548a6430e1770b3855c28e137093845c20e0f7073835c0be04f01f80bc03e00efff7fbbfbdfcefdf7ebbf3df8efbf7dbbebdf4ef9f7cbb9c9cd4e6272d3949c94e4271d38c9c54e226f53789b42d726b53589ab4d526a53509a74d326953325982cb9658b2a5942c99648b225902c79638b1a58c2c59628b125882c39618b0a5842c19608b025802bf95f8afa57c2bd95e8af25782bb95d8aea5742b995c8ae25702b795b8ada56c2b595a8ad25682b39598aca5642b19588ac256029e74efa75d39e9c74dfa6dd35e9a74cfa65d31e9874bfa3e51e28e9470a3651a28c9460a2e51628a9450a265122889440a1e50e2869430a1650a28493a39cfce6e72f3939c7ce2e70f3839bfcdee6ef3739764ba25c92e096e4b625a92d09664b225892c095e4ae25692b09564aa25492a094e4a625292909464a2250928093e49e24e927093649a24c926092e49624a9250926492248924091e48e246923091648a244922090e486242921090648224092008fe47e23e91f08f647a23c91e08ee47623a91d08e647223891c08de46e23691b08d646a23491a08ce46623291908c646223091808be45e22e91708b645a22c91608ae45622a91508a6452228914089e44e226913089644a224912088e4462229110886442220910087e43e21e90f087643a21c90e086e43621a90d086643221890c085e42e21690b085642a21490a084e426212900800200010ffd85ac4526071ff9cb588a4c0d3df61aa492481e6bcc354924903cf7ce6a92492069efb055249240e7de5a8924a281e7bea49249450376f185acf40207cee2924928040fd5c5189250081f3ba93124a0103f774e624940207ceea4a4928040fddc5889250081fbb8a1124a0103e7752224940207eee9c44928040fddd3089250081fbb260924a0103f7744124940207ef63171868040dded61230d0081fb9892461a0103f7a4e18c340207ef49431868040fde920630d0081fbd220c61a0103f7a18b8c340207ef4ad31868040fde85a630d0081fbd2a4c61a0103f7a1498c340207ef4acf1868040fde949e30d0081fbd2b2461a0103f7a5448c340207ef4a491868040fdc849230d0081fbd272461a0103f7a4c48c340207ef4b051868040fde860a30d0081fbd2b1461a0103f7 else 0xb8f0808453c04600c11006f84000000000000000000000000000000000000003d76dbedbd6fedffb73f6cdfe064029c0d604af0209a88940ee06b89000000003650c90600e5e0a088037c1800000001cb8ce0e7757cfdbb8f5e7af77152d6b5dc6a95af54e1616ff3f9812008d1121828104a0903b81ae20000000006de48124a000e029bc1411006f8400000000000000000000000000000000000000000011c00c20f41005f037c180000000000000000000000000000000000000000000000000000000000000000de05a02990960c00000000000000000000000000000000000000000000000000000000000000000000001227c98607b04601ae0c0000016b9e6dfddfbfdbd6cfb7fedaffb6c0ca05909a849fc05e0041a909c0e406b8a000000000000000000000000000000000000000000026f6ede999bf376cdf00f4079711b86a824c150c000000bc3cf7de5cef2e777794ffafe839ce794b5faaec0b24204602100f6003504823c0e206f8800000000000000002603cdf9f398007b038816407a003035c30000000000000000000000396c086e06029c18000000000000000000000000000000000000029ef95da75dfa777553febfaec39ce5e787bcf3c21648011808403d800e41208f03881be2000000000000000000000de05a029810e0c01f2db021d819c0107ffa032014a08000000000000000001a86db6ddbedb032541d4130600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000079d8a67526aae7675ffd52555fa8137f3cf813b39c023c11408503b01f80f608d036440000000000000000000000000025f6ddedb7ed81940b482709381640a50c000000000000000000000000000000000000000000007315f9d49aab9dcebbbaa4aaba8f09ef39e581339f0825e80f40221a08d036430000000000000000000000001c43f875d1ceba3bb9545f5f4aa2d7ea89e1e79e79e08c5c0ae0370004801dc0d70e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000071c1c003b9e4f2773c9e5fdf773c9e4fd6bb9e4f26bea824011a08202a3c000ee093870000ea87523a81d38e9874a3a41d18e5872a3941c98e487223901c78e3871a38c1c58e287123881c38e1870a3841c18d9c6cc3651b20d8c6aef567aabd51ea6f2ad94eca364fb26d8c4c5e62d31598a)))
def level10 : Packing := (491,5,8,0,0,13,1,nd10)
def nd11 (i : Nat) : Nat := (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0x540087ffc5a68010fffaa4d0021dff549a0043ffe29340087ffd5228010effaa450021fff567a0043ffea8f400877fd51e8010fffa93d0021fff507a0043ffeacd40087ffd51a8010effaa350021fff526a0043ffe9cd40087ffd5968010fff8b2d0021fff545a0043bfea8b40087ffc5168010fffa92d0021eff525a0043ffe24b40087ffd3968010fffa62d0021fff564a00437feac940087ffd5128010fffa9250021ff7124a0043ffea0940087dfd4128010fffa7250021fff4c4a0043ffe94940087ffd58e8010fffaa1d0021dff543a0043ffea0740087ffd38e8010fffa61d0021fff4a3a0043ff694740087fed20e8010fffab150021fff522a0043ffea0540087ffd30a8010ffea6150021fff4a2a0043ffe90540087ffd18a8010fffab0d0021fff521a0043ffea0340087dfd4068010fffa70d0021ffe4e1a0043ffe94340087ffd2068010fffa30d0021dff56a88043bfea9310086ffd5a22010effaa444021fff52888043ffe251100877fd51a2010fffa9344021fff50688043bfea8b10087ffd4962010fff892c4021fff50588043ffe20b10087ffd3162010dffab244021fff52488043fee24910087ffd4122010fffa6244021fff4a488043bfea8710087ffd40e2010fffa51c4021ffb4a388043ff690710087ff540a2010ffea6144021ffd4a288043ffa90510087ff518a2010fffa90c4021eff52188043ffea0310087ffd2862010ffda30c4021efdd6988043dfba9310087ff75222010f7ee9444021ffdd4788043dfba4f10087ff741e2010dfeeb344021ffdd4688043dfba4d10087ff741a2010ffee7344021ffdd4588043bfba8b10087bf74962010ffee82c4021ffdd4388043ffba0710087ff738e2010ffee61c4021ffdca388043ff394710087bf74862010ffee80c4021ffcce188043ffb8c310087ff31862010ffce30c4021ffd50088043ffa9c110087ff53022010ffea5044021ffd42088043ffa2d510087ff45a62010ffeaa4c4021ffd14988043ffaad110087ff45a22010ffeaa444021ffd14888043ffaa5110087ff44a22010ffeab3c4021ffd54788043ffaa4f10087bf549e2010ffea83c4021ffd56688043ffaa8d10087ff549a2010ffea8344021ffd4e688043ffaacb10087ff45962010ffeaa2c4021dfd54588043ffa28b10087ff54962010ffe892c4021ffd50588043ffa20b10087ff53962010ffea62c4021ffd56488043ffaa8910087ff54922010ffa89244021ffd50488043ffa9c910087ff53122010ffea5244021ffd56388043ffaa8710087ff540e2010ffea71c4021ffd4c388043ffa94710087fe528e2010ffca41c4021ffd56188043ffaa4310087bf54862010ffea80c4021ffd4e188043ff89c310087ff52862010ffea40c4021ffd46188043ff88c310087fe51862010ffc230c4021 else 0xeffe6054521dffca0a8a43bfe901514877ff102a290f7feb552521cffd6aa4a435ffad5494863ff5aa9290f7fcb552521cff96aa4a43dffad149487bfe5a29290f7fea452521cffd48a4a43dff29149487bff59e9290f7fea3d2521cffd47a4a43dffacd49487bff51a9290e7fea352521effd06a4a43dff9cd49487bff5169290e7fea2d2521effd64a4a435ffac949487bde5929290f7fea252521effd04a4a43dff9c949487bff3129290f7fe5252521eefca4a4a43dffa87494873ff50e9290f7fe81d2521effce3a4a43dff98749487bff28e9290f7feb152521effd02a4a43dff98549487bff28a9290f7fe4152521effc62a4a43dffac349487bff4069290f7fe70d2521effca1a4a43dff90349487bff1869290f7fea052521cffd40a4a43dffa0149487bff3829290f7fe6052521effca0a4a43dff8c149487bff1029290f7fe1052521bffd6aa0a433ffad5414867fe5aa8290f7fea4d0521dffd49a0a439ffa93414873fe5268290f7fe9250521bffd61a0a43bffa8141487ffd2028290dffeb54c5219ffd6a98a433ff2d531486fff5a66290d7fcb4cc521effd4998a439ffa9331486fff5a26290effea44c521effd2898a437ffacf314877ff51e6290fefe834c521fdfce698a43bffa8b31487bff4966290f7fe924c521bffd6398a43bffa8731487fef20e6290dffeb14c521fdfcc298a437ffac131487f7f3026290fffa404c521ef7d4924843befa92490873df5249210f7bca492421ff7d4624843befa8c49087fdf4989210f7be9312421ff7ce624843fefa8a490877df5149210ffbe9292421ef7d2524843def24a49087fdf4149210ffbc8292421ff7ce524843fef98a49087bdf4849210ffbe8092421ff7ce124843fef942490873ff5aa9090c7feb552121cff96aa42435ffad148487bfe5a29090e7fea452121cffd47a4243dffa0f48486bff5969090f7fcb2d2121cffd45a4243dffa0b48487bfe4169090f7fe72d2121affd64a4243def2c948487bff4129090f7fe7252121effca4a42439ffa8748487bff40e9090f7fe71d2121effca3a42435ffac548487bff40a9090f7fe5152121efece1a4243dfd94348487bfb2069090e7fea052121effd00a4243dff94148487ffb5267090f7f6a4ce121ffed489c243ffda5138487bfb4a27090fff4944e121fbed079c243ffda4d38487bfb49a7090fff6834e121fbece69c243ffda8b384877fb5167090fff692ce121efed259c243ffda0b38487ffb3167090fff6a24e121ffed249c243dfda4938487fda4927090fff6824e121ffecc49c243ffd94938487ffb50e7090fff681ce121ffecc39c243ffd94738487feb20e7090ffe6614e121ffed409c243ffda0138487efb3827090fff6604e121ffeca09c243ffc90138487ffd5aa8010effab550021fff16aa0043bfe2d) else (if i < 3 then 0x58c283df7a4518507fef40a30a0ffde5146141ffad018c283ff59c318507feb28630a0ff9a4046141ffad688c283ff52d118507feb59e30a0ffd683c6141ffad668c283df5a4d18507feb41a30a0ffd67346141ffad658c283ff52cb18507fea41630a0ffd672c6141ffacc58c283ff5ac518507fea58a30a0f7d69146141ffad028c283ff520518507feb38a30a0ffd66146141ffaca28c283ff514518507fc920230a0eff8b550041cff149a0083ffea0f40107ffd39a8020f7fa92d0041fff4e5a0083ffe98b401077ed50e8020ffda51d0041fff502a0083ffe9c540107ffd30a8020fffa5150041fff501a0083efea0340107fed1868020ffd230d0041dff16a880837fead110107bfd49e2020fffa83c4041fff50688083ffe9cd10107ffd3962020fffa62c4041dfb54388083ff694710107ff528a2020f7fa90c4041efe52188083ffea0310107fed1862020ffd230c4041cffd28a42439ffa4b484873ff48a9090effeb4d01219ffd69a0243bff945404873ff5a65090cffeb4ca121dfbd6394243bffa05284877fd5a22010cffab444021dff52888043bfeacb100877fd4962010efda51c4021dfd4a288043bfea43100877fd4062010effa50c4021dfb461880439ffad1514873ff58ea290f7feb550521affd6aa0a431ffad541487bff5028290f7feb550021cffd6aa00435ffad5400863ff5aa8010f7feb2d0021effd45a00439ffa8b40087bff50e8010e7fea1d0021effca3a0043dffad528086bff5aa5010f7fea1ca021cffd4394043dffa0728087bff5aa3010e7feb546021affd658c0439ffa8b18087bff4163010f7fa8046021efdd6888043dfba9110087bf75962010f7eea2c4021cfdd4588043dfba0b10087bf750e2010f7ee81c4021efdca388043df98c310087bf51822010c7feb294921cff905292439ffa8f49887bff5169310f7fe72d2621effd44a4c43dff9c949887bff2929310e7fea1d2621effce3a4c43dff94749887bff28a9310f7fe4152621effd40a4c439ffa8149887bff3829310f7fe5052621effc40a4c43bffad3514873ff5a6a290cffeb4d4521dff969a8a439ff2d3514877ff5a2a290effcb454521dffd28a8a43bff251514877ff59ea290cffeb3d4521dbf967a8a43bffa4f514877ff59aa290effe9354521cffd26a8a43bffa0d514877ff39aa290effe92d4521dffd64a8a43bffa49514873ff492a290effe8254521dffce4a8a43bff989514877ff292a290effeb1d45219ffd63a8a43bff9c7514877ff30ea290effe51d4521dfbc83a8a43bffa45514877ff40aa290effe6154521dffca2a8a43bff905514877ff18aa290effe90d4521dffd01a8a43bff9c3514877ff286a290effe40d4521dffc61a8a43bff883514877ff582a290cffeb054521dff160a8a43bffa01514877ff382a290 else 0x7bef48a30a8ffde5146151febca28c2a3ff5a0318547feb38630a8efdea046151ffb4808c2a3ff5841185477fd524a028effaa314051fff4e6280a37eeac850147ffd50ca028ffdaa194051dff543280a3bf6a8650147ffd30ca028dffab114051bfd562280a3ffea84501477fd508a028eff8a114051fff502280a3ffe20450147ffd388a028fffa6114051fff462280a3ffea0250147ff9404a028fff27094051fff461280a3ff68c250147ffd104a028effab544051dff16a880a37fe2d5101467fc5aa2028effaa4c4051bff568880a3ffe2d110147ffd5222028fff89444051dff547880a3ffea0f101477fd51a2028fffa8344051fff4e6880a3fdeacb10147fbd3162028ffb89244051fff4e4880a3ffe98910147ffd50e2028ffdaa1c4051dff543880a3bf6a8710147ffd40e2028fffa71c4051fff4c3880a3ffe94710147fed28e2028ffda41c4051fff542880a3ffaa8510147ffd40a2028fffa6144051fff4a2880a3ffa94510147fbd28a2028ff6a5144051fff462880a3dfea4310147ffd4062028fff280c4051ffe4e1880a3ffe8c310147fed1862028f7f6a4c2051bfed68840a3ffda9108147bfb4a21028dff6b3c2051efed27840a3ffda0f08147bfb49a1028fff68342051ffece6840a3dfda4b08147ffb4161028ff7662c2051ffed43840a3ff5a8708147ffb40e1028fff671c2051ffecc3840a3ffd94708147feb28e1028fff6a142051efed22840a3ffda0508147ffa40a1028fff67142051ffecc2840a3ffd8c508147ff94021028fff26042051ffe440840a39ff2d54a107bff41e9420f7fe7352841affd65a5083dff9cb4a107bff3169420f7fe7152841effcc2a5083dffa034a1073fe5aa93a0d7feb452741effd06a4e835ffacb49d07bff31693a0d7feb152741effcc2a4e83dffa0349d077ee5aa51a0ffdeb44a341efbd2894683ff7acf28d07bef49e51a0ffde83ca341ffbd6694683ff7a0d28d07fef39a51a0ffde62ca341ffbd6294683ff720528d07fef38a51a0ffde614a341ffbca294683fd794528d07fef58651a0ffde80ca341ffbce194683fe690128d06bff5a68120e7fea4d0241cff949a0483dffa5140906fff59e8120f7fe93d0241f7fd07a04837ffacd40907bff4968120efdea1d0241ffbca3a0483ffb98540907ff728a8120fbfe80d0241ff7480a04835ffad148506bff59e90a0f7fe83d2141affd65a4283dff9cb48506bff58a90a0f7fe8152141efed01a4283dfd9c348507bfb28690a0f7f6b452141efe968a4283dfdacf48507bfb41e90a0f7f6b352141efed06a4283dfd9cd48507bfb59690a0f7f4b2d2141efe905a4283dfd9cb48507bfb31690a0f7f6b152141efe962a4283dfda0548507bfa40a90a0f7f67152141efecc2a4283dfd14548507fef41e30a0dfdeb2c6141ffbce)) else (if i < 6 then (if i < 5 then 0x3d2251cffd46a44a3dffa0d48947bff39a9128f7bcb252251effce4a44a3dff98948947bff50e9128e7fea1d2251effd03a44a3dff9c748947bff30e9128f7fea152251cffd40a44a37ffad5409467fe5aa8128f7fea4d0251cffd49a04a3dff293409473fe5268128f7fe9250251ff7924a04a3ffeac1409477ff5028128fffa4050251bffd6a984a33ff2d5309473ff5266128e7fca4cc251bffd68984a3dffa5130946fff59e6128effea3cc251fdfd46984a3bbfa8d30947f7f39a6128fefe62cc251effd24984a3fef24930946fff58e6128efdea1cc251fdfcc3984a3ff790730947bff48a6128effea04c251fff480984a39ff2d548547bfe5a290a8e7fea3d2151effd07a42a35ffac948547bde59290a8f7fe7252151cffd43a42a3dffa0748547bff38e90a8d7feb152151effd02a42a3dff8c548547bfb38690a8e7fea052151affd69a02a3bffa93405473fe52680a8f7fe9450151bffd67a02a3bffa8f40547bff49e80a8f7fe9250151ff7924a02a3bffa8740547fef20e80a8fff690d0151efed21a02a3ffd9c340547ffb20680a8fff620d0151dffd40a02a3ffe90140547ffb08280a8fff4b550151ffed69a02a3dfdad340547ffa5a680a8fff6a4d0151efed49a02a3ffd29340547bfa52680a8fff69450151efed28a02a3ffdacf40547ffb51e80a8fff693d0151efed27a02a3ffda0f40547ffb59a80a8fef4b350151ffed46a02a3bfda8d40547ffb49a80a8fbf68350151ffece6a02a3ffdacb40547ffb49680a8fff682d0151ffed64a02a3ffda8940547ffb49280a8f7f69250151ff6924a02a3ffd9c940547ffb31280a8fff65250151ffed63a02a3ffda8740547feb50e80a8eff6a1d0151dfad43a02a3ffda0740547ffb38e80a8ffd641d0151ffed62a02a3ffd2c540547ffb50a80a8fff4a150151ffed22a02a3ffd24540547ffb40a80a8fbf68150151ffece2a02a3ffd94540547fbb28a80a8fff6b050151ffed40a02a3ffda0140547dfb40280a8fff67050151ffe480a02a3dfda9338546ffb5a270a8fff6a44e151efed289c2a3ffd25138547efb41e70a8fff6a34e151efed269c2a3ffda0d38547efb39a70a8ff7662ce151ffed449c2a3dfda4938547fda49270a8fff6624e151ffed439c2a3ff5a8738547ffb40e70a8fff661ce151ffac839c2a3ffda8538547bfb48a70a8fff6814e151fbece29c2a3ffd98538547ffb18a70a8fdf6704e151ffe4809c2a37ffad118547bff4a230a8dffeb3c6151dffd478c2a3dffa4f18547bff49630a8ffde81c6151ffbce38c2a3ff794718546fff58a30a8f7fe9146151ffbc628c2a3ffda0318547ffb38630a8fff620c6151dffd408c2a3ffd841185477ef52630a8ffdcb446151ffb9288c2a3bf7a8f18547fef41e30a8dfdeb246151ff39248c2a3ff79c91854 else 0x3ff79c928d87fef58a51b0ffdcb14a361ffb922946c3ff79c528d87fef28a51b0ff5e514a361dfbd40946c3ff6a0128d87fed20251b0fefe944c261edfd28984c3bbfa8f30987f7f49e6130f6fe93cc261fdfd07984c3fbfa4b30987b7f4966130fefc92cc261fdfce5984c3fbfa4930987b7f4926130febc924c261fdfd04984c3fbf9c930987f7f2926130eefea1cc261fdfd03984c3fbf9c730987f7f28e6130fede51cc261fdbc83984c3fbfa4530987b7f48a6130fefe814c261fdfc82984c3fbf8c530987f7b4066130fefe804c261fdf500984c3fbf9c130987f7f2826130fefa404c261fdfc40984c3dbfa5130187b7f49e6030fefe83cc061ddfd45980c3dbfa4b30187f7f4166030eefea1cc061fdfd03980c3fbf9c730187f7f28e6030fede51cc061bdfd62980c3dbfa4530187f7f38a6030fefe514c061fdfc62980c3fbda0330187f7d4026030fefa704c061fdf440980c3bfead5101877fd5262030effaa3c4061eff527880c3ffea0f10187f7d59a2030fffa72c4061bff564880c3fee24910187ffd3922030effaa1c4061fff503880c3ffe9c710187ffd28e2030ffda51c4061ffb483880c3fbe98510187ff528a2030e7fea054351cffd48a84a3dffad540946bff5aa8128f7fcb5502518ff96aa04a3dffac140947bff5028128d7feb5440518ff96a880a39ffa8710147bf750a2028c7fcb552651cffd47a4ca3dff9c949947bff50a9328f7fe7152651effc62a4ca39ffa8149947bdf5249228efbea492451cf7d49248a3def292491477df5189228f7be9312451ff7ce6248a3fefa8449147bdf4889228f7bc9112451ff7902248a3fef9c449147bdf4849228f7fcb4d4351cff949a86a3bffa8d50d47bff49aa1a8dffeb154351dffd42a86a3ff78c550d47ffc582a1a8effea054351ffb969a86a3df72d350d477ee526a1a8efdea354351bfbd64a86a3bf7a8950d47fce492a1a8efdea154351dfb942a86a3ff62c150d477ef502a1a8ffda4054351cffd69a86a39ff2d350d473ff49aa1a8effe7354351dfbc62a86a3bff9c350d477ff106a1a8eff8b054351dffcc0a86a3bff88150d477ff082a1a8efdcb4d4351cfb969a86a3bf7acd50d477ef49aa1a8efde7354351dfbd64a86a3bf7a4950d477ce492a1a8efde6254351dfbd62a86a3bf72c550d477ef48aa1a8efdc9154351dfb902a86a3bf79c550d477ef486a1a8efde70d4351dfbd60a86a3bf62c150d477ef302a1a8efda4054351dfbc40a86a3bf784150d46fff5aa61a8cffeb54c351effd49986a39ffa9330d46fff5a261a8dffeb3cc351dffd47986a3dffa4f30d47f7f41a61a8ffdea1cc351dfbd43986a3ff7a0730d47fef38e61a8effea04c351fdfcc0986a39ffad548946bff5aa9128e7fcb5522518ff96aa44a3dff2d148947bff5229128e7fea) else (if i < 7 then 0x9a51b8ffdeb24a371bfbd64946e3fe724928dc7fef31251b8ffdeb14a371ffbd61946e3ff690128dc7bfe5a290b8e7fea452171ebfd07a42e35ffacb485c6bff59290b8f7bcb252171effca4a42e39ffa87485c7bff40e90b8f7fe51d2171affd62a42e3dff8c5485c6bff5a680b8effea4d0171effd28a02e3f7fa0f405c7bff49280b8ffbc9250171bffd63a02e3bffa87405c7fef20e80b8effea150171ffec81a02e3ffd8c3405c7ffb10680b8fffa4050171dfbd498c2e3ff72d1185c7fee4a230b8dfdeb246171ff39248c2e3df7a45185c7feb40630b8ffda4046171cff969a80e3bff2d1501c73ff4a2a038cffeb354071cffd26a80e3bffa0d501c67ff596a038e7fe92d40719ffd63a80e3bffa07501c77ff30ea038effe51d4071dfbca3a80e33ffac5501c73ff48aa038effe6154071dffc62a80e39ffa43501c77ff406a038effe30d4071dfbc61a80e3bff883501c77fd302a038effa20540719ffd6aa00e33ff2d5401c6bff5a68038e7fea4d0071dffd48a00e3f7fa0f401c77ff51a8038fdfe7350071dffd43a00e3bffa85401c77fd5028038effab550071dff16aa00e3bfea93401c7ffd5228038effaa450071fbf567a00e3f7ea0f401c7ffd51a8038effaa350071fbf4e6a00e3dfea4b401c6ffd5928038ffb89250071fff4c4a00e3ffea87401c77fd50e8038fffa81d0071fff4c3a00e3ffe947401c7fed28e8038ffda41d0071fff542a00e3ffe985401c7ffd18a8038fffa80d0071f7f501a00e3ffe8c3401c7fed1868038ddfeb44e071ebfd289c0e377facd381c7aff49a7038fdfe834e071ebfd259c0e3b7fa87381c7eff40e7038fdfe61ce071fbfca39c0e3f77947381c7aff48a7038fdfe614e071fbfc629c0e3d7fa43381c7eff4067038fdfe30ce071fbbc619c0e3f7f883381c7efd4027038fdfa604e071fbf4a09c0e3f7e881381c77fd5aa2038eff8b544071dff549880e3ffe2d1101c7ffc4a22038fdfab3c4071fbf507880e3f7e9cd101c7ffd3162038dffab244071ff7124880e3ffe989101c77fd50e2038fffa81c4071fff4c3880e3ffe947101c7fed28e2038ffda41c4071eff521880e3ff68c3101c6bff5a293b0e7fea452761affd65a4ec35ffac949d87bde59293b0f5fe7252761effca4a4ec39ffa8749d87bff40e93b0f7fe51d2761affd62a4ec3dff90549d87bff18a93b0f7f680d2761cffd40a4ec3befa92491873df5249230efbea412461ef7d28248c3befa8e49187bdf49c9230ffbe8392461ef7d25248c3def24a49187fdf3949230f7be9112461ef7922248c3fef9c449187fdf2889230ffb68092461ff7500248c3bf7ad528d87fee5a651b0efdea4ca361ffbd68946c3df7a5128d87fef59e51b0efdea3ca361efbd27946c3ff7a0f28d87fef59251b0dfdeb24a361ff3924946c else 0x1f7f525a0103efe24b40207dfd5928040fbfaa250081f7f524a0103eee24940207dfd3928040fbfa6250081f7f562a0103efe2c540207dfd48a8040fbf89150081f7f0a2a0103efeac340207dfd4868040fbf260d0081f7f461a0103ef68c340207de91868040e7fe9454971cff928a92e33ffacd525c73ff49aa4b8cffeb2d4971cffd25a92e3bef2c9525c73ff492a4b8efde41d49719ffd62a92e3bfb2c5525c73ff48aa4b8effe20d4971dff480a92e39ff989525c73ff40ea4b8e7fe30d4971cffcc0a92e39ff841525c67ff5a6a438effcb4d4871cff969a90e33ffacd521c777e59aa438effe9354871dffd24a90e3bff989521c77ff48aa438effe90d4871dffc81a90e3bff841521c73ff5aa9438e7fcb552871effd48a50e3dffa8d4a1c73ff51a9438d7feb252871ef7964a50e3dff9894a1c7bff2929438f7fea1d2871effd03a50e3dffa854a1c7bff20a9438f7fe3152871effc61a50e3f7f29341dc7eff49a83b8fdfe9250771ebfd24a0ee3f7f98941dc7eff48a83b8fdfe4150771fbfd21a0ee3f7f90341dc7eff28283b8fdfa4050771fbfc20a0ee3dffa87499c7bff28a9338f7fe3152671bbfd689cce3b7fa91399c7eff4a27338f5fe944e671fbfd259cce3f7fa49399c7aff4927338fdfe824e671fbfca49cce3f7fa07399c7eef20e7338fdfe914e671ebfd229cce3f3f985399c7eff20a7338fdfe314e671fbfca09cce3f7e901399c7eff1027338e7feb552571cff96aa4ae3dff2d1495c7aff41e92b8e7fea352571effd06a4ae3d7f9cd495c6bff59292b8f7bcb252571effd04a4ae3dff989495c7bff40e92b8d7feb152571effcc2a4ae3dff8c5495c7bff18692b8cffeb54c5719ff96a98ae3f3f9cd315c7bff49262b8ffde41cc571bffd6298ae3dffa45315c7f7f30a62b8fffa404c571ef7d49248e3befa92491c73df5249238ffbea412471df7d48248e3defa50491c7bde4a09238fdbe8392471ff7d46248e3defa4c491c7edf3989238f7be9292471ff7cc5248e3fefa84491c7bdf4889238ffbe6112471ff7ca2248e3defa42491c73fe5a6a1b8e7fe9454371cffd26a86e39ffa4b50dc67ff58aa1b8efecb154371cffd22a86e3bf78c550dc77ff106a1b8effe6054371dffca0a86e3bff88150dc77ff082a1b8cffeb54c371cffd49986e37ffad130dc7bff4a261b8fdfe83cc371effd25986e3ff7a8730dc77ef50e61b8ffde81cc371dffd42986e3dffa4530dc7f7f30261b8cffcb54a371effd28946e3f7fa0f28dc6fff59a51b8effea34a371effd26946e3f7f9cd28dc77ef50e51b8ffde81ca371ffbcc3946e37ffac528dc77ff50a51b8f7fe914a371ffbc62946e3ff78c328dc77ef5aa51b8efdcb54a371dfbd49946e3ff7ad128dc7fee5a251b8f7de944a371ffb928946e3ff7acd28dc7eef3))) else (if i < 12 then (if i < 10 then (if i < 9 then 0xf951f1a3e147be8f751eda3d947ae8f551e9a3d1479e8f351e5a3c9478e8f151e1a3c1477e8ef51dda3b9476e8ed51d9a3b1475e8eb51d5a3a9474e8e951d1a3a1473e8e751cda399472e8e551c9a391471e8e351c5a389470e8e151c1a38146fe8df51bda37946ee8dd51b9a37146de8db51b5a36946ce8d951b1a36146be8d751ada35946ae8d551a9a351469e8d351a5a349468e8d151a1a341467e8cf519da339466e8cd5199a331465e8cb5195a329464e8c95191a321463e8c7518da319462e8c5516382c505860b0415f82bd05760ae415b82b504c1097a12e425a84b1095a12a425284a1093a12641fe43f887e90fc21f643e887c90f821ee43d887a90ce819b0332065c09e813b027203a407380e501c60253020c00037df524923b67bea492476ff7d21248eddefa42491db3ff5aa90bb57feb2d2176affd64a42eddef2c9485dbbff29290bb77fe81d2176effca3a42ed5ffac5485db3ff50a90bb77fe4152176effc62a42eddffa01485dbbff28290bb77fe2052176cffd22a80edbff8c5501db3ff486a03b6ffe30d4076dffc41a80edbfe881501db7fd5aa203b6ffaa4c4076fff528880edffea4b101daffd592203b7ffa9244076ff7124880edbfea87101dbffd40e203b7ffa51c4076ffb4a3880edff6907101dbffd486203b77fa90c4076fff461880edff68c3101dabff58a93b276fc5152664affd65a42c9dff9cb48592bff58a90b277fe7152164eff525a00c9ff68c340193bfd49e20327ffa72c4064ffb4a3880c9dfea4310193fed186203267fe93d49819ffd66a9303bbf2cd526073ff49aa4c0effe7354981df7964a93039ffa49526073ff48aa4c0e7fc9154981dffc41a9303bfe901526073ff59ea4c0e7feb254981cf7964a93039ff9c9526073ff312a4c0e7feb154981cff962a93039ff9c5526073fe28aa4c0c7feb114981cffce2293039ff14452607fdf5249240f7bea492481df7d49249039efa9249207bde5249240ffbea392481ff7d2724903defa4e49207fdf5189240febca312481ff7d2624903defa4c49207fdf3989240ffbea112481ff794224903fefa4449207bdf4889240f7bc9112481ff78a224903fefa4249207bdf4849240effea4ca281cff94994503dffa4928a07fde4925140fffa404a281cff969a81033ffacd5020777e59aa040effe7354081dffd05a8103bffa07502077fe58aa040effe7154081cffd21a8103bff8c3502077ff106a040f3fea4d0081f7fd47a01036ffacd40207dff51a8040fafca350081f7fce6a0103effa8b40207dff50e8040fbfcb150081f7fd42a0103eff285402079ff4868040fbf660d0081f7fc61a0103efd8c340207def1868040fbfe20d0081f7f420a0103efe2d340207dfd5268040fbf8a4d0081f7f567a0103efea4f40207dfd5968040fbf8b2d008 else 0xc3ad871b0db61a6bde97b92f6a5ec4b99572eae555c9ab91571eae355c5ab89570eae155c1ab8156feadf55bdab7956eeadd55b9ab7156deadb55b5ab6956cead955b1ab6156bead755adab5956aead555a9ab51569ead355a5ab49568ead155a1ab41567eacf559dab39566eacd5599ab31565eacb5595ab29564eac95591ab21563eac7558dab19562eac55589ab11561eac35585ab09560eac15581ab0155feabf557daaf955eeabd5579aaf155deabb5575aae955ceab95571aae155beab7556daad955aeab55569aad1559eab35565aac9558eab15561aac1557eaaf555daab9556eaad5559aab1555eaab5555aaa9554eaa95551aaa1553eaa7554daa99552eaa55549aa91551eaa35545aa89550eaa15541aa8154fea9f553daa7954eea9d5539aa7154dea9b5535aa6954cea995531aa6154bea97552daa5954aea955529aa02140027f84fe09fa13f027d84fa09f213e027b84f609ea134726864cfc95b92b3255e4aac95392a324c3497692cd255a44048708c3118222fc45e886ed040a0793ef07dc0f1b1e2e3c4c7878f0b1e0e3c0c77f8efb1dee3bcc7778eeb1dce3b8c76f8edb1dae3b4c7678ecb1d8e3b0c75f8ebb1d6e3acc7578eab1d4e3a8c74f8e9b1d2e3a4c7478e8b1ba934b46624cc0997932e265a4cb0995932a26524ca09939326264a4c90991932226424c8098f931e263a4c7098d931a26324c6098b9316262a4c50989931226224c40987930e261a4c30985930a26124c209839306260a4c10981930226024c0097f92fe25fa4bf097d92fa25f24be097b92f625ea4bd097992f225e24bc097792ee25da4bb097592ea25d24ba097392e625ca4b9097192e225c24b8096f92de25ba4b7096d92da25b24b6096b92d625aa4b5096992d225a24b4096792ce259a4b3096592ca25924b2096392c6258a4b1096192c225824b0095f92be257a4af095d92ba25724ae095b92b6256a4ad095992b225624ac095792ae255a4ab095592aa25524aa095392a6254a4a9095192a225424a8094f929e253a4a7094d929a25324a6094b9296252a4a50949929225224a40947928e251a4a30945928a25124a209439286250a4a10941928225024a0093f927e24fa49f093d927a24f249e093b927624ea49d0939927224e249c0937926e24da49b0935926a24d249a0933926624ca4990931926224c2498092f925e24ba497092d925a24b2496092b925624aa4950929925224a248ee91d5239a47148de91b5235a46948ce9195231a46148be917522da45948ae9155229a451489e9135225a449488e9115221a441487e90f521da439486e90d5219a431485e90b5215a429484e9095211a421483e907520da419482e9055209a411481e9035205a409480e9015201a40147fe8ff51fda3f947ee8fd51f9a3f147de8fb51f5a3e947ce8) else (if i < 11 then 0xd849b08360e6c18d829b0436066c08d809b0035fe6bf8d7e9afc35f66be8d7c9af835ee6bd8d7a9af435e66bc8d789af035de6bb8d769aec35d66ba8d749adc35b66b68d6c9ad835ae6b58d6a9ad435a66b1ad62dac4b5876b0ad60dac0b57f6afad5edabcb5776aead5cdab8b56f6adad5adab4b5676acad58dab0b55f6abad56daacb5576aaad54daa8b54f6a9ad52daa4b5476a8ad50daa0b53f6a7ad4eda9cb5376a6ad4cda98b52f6a5ad4ada94b5276a4ad48da90b51f6a3ad46da8cb5176a2ad44da88b50f6a1ad42da84b5076a0ad40da80b4ff69fad3eda7cb4f769ead3cda78b4ef69dad3ada74b4e769cad38da70b4df69bad36da6cb4d769aad34da68b4cf699ad32da64b4c7698ad30da60b4bf697ad2eda5cb4b7696ad2cda58b4af695ad2ada54b4a7694ad28da50b49f693ad26da4cb497692ad24da48b48f691ad22da44b487690ad20da40b47f68fad1eda3cb47768ead1cda38b46f68dad1ada34b46768cad0f3a1d7438e86dd0d3a197430e85dd0b3a157428e84dd093a117420e83dd073a0d7418e82dd053a097410e81dd033a057408e80dd013a017400e7fdcff39fd73f8e7edcfd39f973f0e7ddcfb39f573e8e7cdcf939f173e0e7bdcf739ed73d8e7adcf539e973d0e6e14dba9b6536aa6d14d9a98cb317662acc4d988b30f661acc2d984b307660acad195932b0655ccab195532a8654cca9195132a0653cca7194d3298652cca519493290651cca319453288650cca11941328064fcc9f193d327864ecc9d1939327064dcc9b1935326864ccc991931326064bcc97192d32586484c8bd916b22b6452c89d912b2236442c87d90eb21b6432c85d90ab2136422c83d906b20b6412c81d902b2036402c7fd8feb1fb63f2c7dd8fab1f363e2c7bd8f6b1eb63d2c79d8f2b1e363c2c77d8eeb1db63b2c75d8eab1d363a2c73d8e6b1cb6392c71d8e2b1c36382c6fd8deb1bb6372c6dd8dab1b36362c6bd8d6b1ab6352c69d8d2b1a36342c67d8ceb15422a445408a7114c229445208a311442284450089f113c2203c3ff87ef0fbe1f3c3df87af0f3e140427884e109a2130425884a1092212042388461041207e40f47fb6ff4dfe5bfc37f76fecdfd5bfa37f36fe4dfc5bf837ef6fdcdfb5bf637eb6fd4dfa5bf437e76fccdf95bf237e36fc4df85bf037df6fbcdf75bee37db6fb4df65bec37d76facdf55bea37d36fa4df45be837cf6f9cdf35be637cb6f94df25be437c76f8cdf15be237c36f84df05be037bf6f7cdeb7bd677abef55dea7bd477a7ef4dde97bba7773eee5dd70398e730ce15db6cb6d16d92db05b3bb66f6cced97db2bb64f6b94d709add35b26b54d689acd3592688cd0f99c7b38766fecddd9b7b36766becd5d9a7b347667eccdd997b327663ecc5d987b1926314c6098bd317262d4c5898ad315261e6 else 0xdb9dbbfbb769696b46c36726c37e1b3319b033b2002702580320308207706f870000003b91eb39d7e92d525eaaf9cddbfffaf530fe67fcf3e067f9e604b258c608207f07d02501706f50b03f46306c8a000025e2fd2fcefa675985e7b3a73aeddd949aad4f6be04d8667d818fe6c608701711770214d082081870000005e15db85eeebaeeeed5576febaaaebaaef5af77dbb5a00001861861860048112820046843b05432eee02af77aeef5bbaeeebb700076abb55bfd1daaefaadafd14c30c300c302081fc0941001ec1bd42e1db6db6db6db6db6dbb76eddbb5ad6b5adb6db6db76b33f336666025f02f01f0084e0cfc17f82bf04fe08fc0ff81bf02fe04fc07f80bf00fe00fbfff7fbefefdfcfbf7f7ebefcfdf8fbeff7dbefafdf4fbe7f7cbef8fdf0fbdff7bbef6fdecfbd7f7abef4fde8fbcff79bef2fde4fbc7f78bef0fde0fbbff77beeefddcfbb7f76beecfdd8fbaff75beeafdd4fba7f74bee8fdd0fb9ff73bee6fdccfb97f72bee4fdc8fb8ff71bee2fdc4fb4636886d08da01b3e36786b89d703ade75b8eb69d6c3ad675a8eb49d683ace7598eb29d643ac67588eb09d603abe7578eae9d511aa0353c6a70d4d1a98352c6a50d491a90351c6a30d451a88350c6a10d411a8034fc69f0d3d1a7834ec69d0d391a7034dc69b0d351a6834cc6990d311a60346768c6d17da2db45768a6d13da25b4476744ce799cd3338e669ccc39967328e649cc8398e7318e4cec75b8e971cee395c71b8e171bee375c6db8d971aee355c69b8d1719ee335c65b8c9718ee315c61b8c1717ee2f5c5db8b9716ee2d5c59b8b1715ee2b5c55b8a9714ee295c51b8a1713ee275c4db899712ee255c49b891711ee235c45b889710ee215c41b88170fee1f5c3db87970eee1d5c39b87170dee1b5c35b86970cee195c31b86170bee175c2db85970aee155c29b851709ee135c25b849708ee115c21b841707ee0f5c1db839706ee0d5c19b831705ee0b5c15b829704ee095c11b821703ee075c0db819702ee055bdd77b8ef6dded3bd97778aeed5dd2bb95770aedd5db2bb55768aecd5d92bb15760aebd5d72bad5758aead5d52ba95750ae9d5d32ba55748ae8d5d12ba15740ae7d5cf2b9d5738ae6d5cd2b995730ae5d5cb2b955728ae4d5c92b915720ae3d5c72b8d5718ae2d5c52b895710ae1d5c32b855708ae0d5c12b815700adfd5bf2b7d56f8aded5bd2b7956f0addd5bb2b7556e8adcd5b92b7156e0adbd5b72b6d56d8adad5b52b6956d0ad9d5b32b6556c8ad8d5b12b6156c0ad7d5af2b5d56b8ad6d5ad2b5956b0ad5d5ab2b5556a8ad4d5a92b5156a0ad3d5a72b4d5698ad2d5a52b495690ad1d5a32b455688ad0d5a12b415680acfd59f2b3d5678aced59d2b395670acdd59b2b355668accd5992b315660ac8e5889b10361e6c38d869b0c36166c28)) else (if i < 14 then (if i < 13 then 0xd546baaa37faa3e0000000b87bbbbafda0020c1b340022c2181e40961c000147801776817741beaa0d6aee83fdbed1e000028075d576801bfc0b4001b01c4096180000000001fededf74db6d893c12a12a81480e0043000000317bfd7b67c0006582542505985001fffcf25e92f541e7cf1c3b9ce0bbaaaecee3ebd5564a0f67cf03b200690d511c0a08706f8600000033be2ee6e752557739ddd41f64f9de3c3de4f1e52aaabeb2f3b032fc0b680a83e80046c86837c30bf3b9e6f7de52aa9e7bef7bd4aaaaa70e7727207272bb1c61f664f960d04a0efa23814a1e0d90c00efffefd7bfbbfdbdf781bebaaed77dda1a602150880506913190d06cc0a50b89007e7717df37cfa92aee73bbabec0c9cf78f0f793852aaab2f03b270795d80fc19740142e4341be180000000000000000000000000000000000000000000000000000000000000000000000008f972be7cfd52fd17879e2be7dffbf5e11ce70e5a5fd57bcfeb8c39df870efeedc0ec0dc0407fc034120fa0e7103bf979f9fafcfa55f4957aa0b33e7871739ce0abaaaecee3c3cf7cf03bbd8461c21c0942d82821c1be1ddbf8000ee0aaa0aaaa82a800000000aaa0aaa001009c04a09b0800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003de935befdf09b771899b3606ac2320bc000da24f0c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003f0bbe2f77802bad000015dfeb428bbbb73fe87f42b428aed087025e0a00580306707d074027890000000000000000002ddcc7f599ab27fad525aa0cfcf97036ff9852d556cf60ccfd9f03d820409e0142081dc1b009421c1be240000000000000000000088fc4539e76539e766f539e7376ea73d9cdbbeeee4092588333ece716d0061041020eec141270c000000000000000000006d9be6f0db36c else 0x7cf977b7faff89b7e5f9b77f37ff6b36ed9ecf6db066045034e00c0f90807705708c3118a0000000000000000000000001fdef76b3a6df9b6fb2ecffb4df6c399b0548478103ac83838045304c4000000000000000ceccb74e7777496ead7d3d7aaea0e6fdfe7e40e7673f96062db3e48c609107108e084d0709008c06b88000000000000000000007efeb39bfdff7db6eb5b67b7ff6db36db5ffb6db065059427127108104e02e0003507806b8b00007efeb9e6d6ff75ff6f5b67dffb6cdb6db6db6d83289a89388388270041aa13849035c50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000039c65f83c7f00de303d835a82d01838c280000000000000001f38efbe67e9b329edfe5bd3fb396edc19e7f65f36d9fb5ad6c9b32db7b76cd06cf671b37810a28121048a5022112837c4000016f36dcde2188ccdf86e6db1be03d03c71170d60a225861f778d97bb85ffddd0af5fd0af5ea80c001dc6cbb7777ebda0576baa47423c2101c400c2301ec1de82620017ddbdffdb6df6feb13f6d66b77dbbdb6ff6ed6e37b6fdb81278178082902391283b836104c4b664cfdb6ccb7bdbfcb7b77f672ddbb619e7f647ce3e921adb67ed6b5b2f986cf6706de0428a04841229408844a0df10000000df6cb6d821b037004180000000001abdb366cc60edb8db6c16819141e826100000000000000076c5f16fbd8b7b79867cf1bb8692166b5ad965bb8b5fad64a0d9f3c0dbf80fec345285140941a41be1c0031f8e7cf3c0fec22dcdf03290304103b82d029837c38000000000000000000000000000000016778fd734eb93bba93ffd6833f9fe5e30dff9ff3e14baeab6d9f6059205823422c2001df43c8181d80942401c41be2c00000000000000012ddff1832b0310282c829c28000000005e4cbea66dab3b3ffdabf76e4aab5a0fe4d9981b6cce7f8c0b36764182081c81bc09c8144141f41dc1b224000001eadb39feffb7dfb6db6dffff6db6db60ca0b40b20a504e24ea1140ca0f40b1400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ff8fc00a017ddf07d5eef0fe7adebbb836b76e3f00000576815ad68089035d00091b1106f08b02588000000000000000000000000563e2f5e2eb8d) else (if i < 15 then 0x808207760a8700001717c3c7f24940002f23f07127010e0b006c0ca081100df0e0000000000000000b501dd7d7775ddc0016eeeb7777716babd75ffa3f55daaebfa354c30c030c301fc1ec1bc4d40942081ad42e21b6db6db6dbb76eddad6b7f5adb6db6dbb599bccd999b6db6db76b6c06a04be05e03e010a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000b5f80ead7e15d5bffc35dde855feab75adf7c2baaea87f4f7af75efe8000c283e81020a88a8283ba93846d04c4800000001def2dff37f66df7e6d676ced66fb6c6c121c21c1f42d41024149e82620000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000070f03016403a08504056082847afb9c3db6db5b6d6db6a080b24101206230a0000000000000000000000000000000000000000000000000000000000000000000000000000000025cf00018206c0c0060be0df080000000000000000003b4ac0d8c1b336a0802e24f060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000033f3b1d1df20784c02f3011f00b0321de07835c30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003b9bffdd35fdfeba6bf7557d75571e7ef3cf2719fdcff3960f9b927c1de3cfbc92000cc24011c0b010d8242342141ae24000000000007efc2a85d7fe8555685df5ddf42aaff55f685ded777a77a0180301210060aa0a810411ac130e000000000000000000003fad2574957703f7f94faaa771c3b9c27607e785874fbdaf5e5f73c10800611a0860f6c1211e0ed1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c7ddf6ce0ca8484480b308cbb5e0b4c0c0ca0a7080000000000000000000000000000000000000000000000000000000000000000000000000000000000 else 0x2abfeef5555576fbd5ba8000000aeeabbe0555555050000001406900f0460350258600000000000b7787d5adef0ad5bbfc3ebbbe855d56eb5fc2ffd56a82eefd775dfa000300c2a0ea0a0820f4a2010411b413120000000000000000000000000000000000000000db77e9b6db424224b02d018400000000000000000000000000000000000000000000000000000000000000000017970fcfe48300143e424e021819c1541200c2201be1c000000000000000005efc2fb0bbdd70af5ad6857b56baa000c16ded6fb76b40abfdd5ab46cdd0480322405))))
def level11 : Packing := (1662,4,8,0,0,15,1,nd11)
def nd12 (i : Nat) : Nat := (if i < 4 then (if i < 2 then (if i < 1 then 0x64ffea00c9ffd10193ffea4c0dffd49819ffa9303ffe526067fca4c0fffd2781fffa8903fff49207fbc9240fffce481fff98903fff48a07ffc9140fffca281fff14503fff50206ffea040fffd0081effa0103dfd40207ffe1040fffd4971bffa92e33ff525c7ffca4b8cff94971fffa90e37ff521c7ffca438fffd2871dffa50e3ffe4a1c7dfe83b8fffd4671fffa4ce3bff499c7dfe7338fffd4571fffa4ae3bff495c7ffe62b8fffd4471fffa48e3bff491c7fbc9238fffcc471fffa86e37ff50dc7ffe81b8fffcc371fff946e3fef28dc7fde41b8fffd4271fffa44e3bff489c7ffe6138fffc6271fffa42e3bff485c7ffe80b8fffc6171ff78c2e3fff501c6ffea038fffd0071ffea00e3eff381c7ffe6038fffca071ffe900e3fff101c7ffa2038fffc2071bffa92c33ff52586ffea430fffd2861dffa50c37ff51d87ffe93b0effd2761fffa0ec3fff495877fe92b0fff92561fff9cac3fff491877fe9230ff792461fff9c8c37ff50d87ffe81b0fffce361fff946c3fef28d87fde41b0fffd2261dffa44c3ffe48987ffe7130fdfcc261fff944c3ffe28987ffe3130ffed0161bffa80c3fff40187ffa8030fffce061fbf980c3fff28187ffa4030fffc4061ffe880c3bff50d467fea1a8effd4251dffa04a3bff501477fe2028fffd4951dffa92a37ff525467fea4a8fff94951dff292a33fe52547ffea328dffd4651fffa4ca3bff49947ffe7328fffd4451fffa48a3bff49147fbc9228fffcc451fffa86a3fef50d46ffea1a8dfbd4351fff986a3fef20d47ffea128fff94251fffa44a3bff48947ffc9128fffd0251fff204a3fff38947ffe6128fffc6251fffa42a3bff48547ffe80a8ffed0151fff9c2a3ffb38547ffe30a8ffbc6151fffa80a37ff50147ff8a028fffcc051ffe900a3fff10147ffa2028fffc2051ffd840a33ff525067fca4a0effd2841dffa4e83fff41d077fe9320fffd0641fff9cc83bff49507ffc82a0fffce541fff98a837ef50d07fde51a0effd2241fffa0483ffe40907ffe7120fffcc241fff94483ffe289077fe90a0efed2141fffa0283fff38507ffe50a0ffbc6141ff58c283ffd40107fba4020fff44041bffa42437ff40486ffe5090dff44021dffa8a433ff514877fe8290effd40219ffa8043bff400877fe5010effc6021dfb88043fff524877fea490dffd49219ffa9243ffe524867fca490fffd4621bffa8c43fff498877fe9310fffce621fffa8a437ff51487ffca290fffd2521dffa4a43ffe49487ffe8290fff90521fff9ca43fff31487ffea210fffd2421dffa4843fde49087ffe6210fffca421fffa4243bff48487ffe8090fffce121ffd9c243fff28487ffe4090fffd4021bffa8043fff40087ffa8010fffce021fff98043fff28087ffa4010fffc4021ffe88043ff710087fea2010fffc2021 else 0x27100000006d9bdf9b7ff9afff9ff5f9afed39f39dc8dbfe6bfb6d719beffe7f9f6618d7fb7b5cdefffc6bdaab9affcf49a1a63533edfffc30e7fedb017b055084108003582704b43c0684408042ca68738f0000157bf9f6cfbccdbff8a7581b3ec679b36f7f6f4b3ccdbb77fb74cddeccdd336eedc53a23249e66dfaccdefdbbab6c118010d60909a49c2490d29b120000000000db6dbfefdfb6df6defeded6d5ad66c7ff9e66db6ff6db6f6b36edf77f6edb76b376edbbeddacdbbb76d6b55b35ad666cd8666db01aa08a0e0dd0302562382a86d0b8a000000000033f2faff9bbcdf377f6c2548e6efeddba3e6effdb6d3731e7ecd8660cf63ff9b18d4d4935353264edbb753bb77f9fedb285ca0e014365110120fc1292b21a2062cbfafe673773b737bfe76e6f7fb7e6edcdefb7dbe3633fd9fbff0a255241dbb7b7b7b6506767ecf81b6c6a6a6a6a6495321df0460f0062081522507e82437c536f6df6db6db6eddb76ed6b5ad6db6db6ddacff336666666666c66b6b5b55acdb604a01401f02a1782a180316a71687166716470fd30fb30816fef6fed6feb6f7baf79af77af106ee22ee02ede2e85ee35ade36de16d5eecf32cf12cbd2cbb2cb92cb72c2f6c2d6c2b6c296c276ba3eba1eb9feb0c2b0a2a84aa2a2a282a262993a94c694a69486946689ce89ae898e7f767f56759a757a755a6d726536651664f65b96510e50ee50ce50ae485a483a481a3da63d8635922e06268e266e264e262e260e25ee25ce25ae1ca213d213b20c7a0c5a036dff59f681ed2ded0decedeccdecade4a9e489e469e449e429e409e3e9e3c9e3a9db9ddb7ddb5ddb3ddb1ddafddadddabdd58dd56dd54dd52dd50dd4edce81ce61ce41ce21ce01cde1c681c661c641c621c601c5e1c5c1c5a1c581c049c029c009bfe9b8d5b14dab75a3e5993599158f358f158ef58ed58eb58e958e758e558e358e158df5871186f186d186b186917e717e5177b56fc165cd60dd59555935591558f558d54f714f514761474147213da93d893d69343d2be5232d230d1ae9140d0c010be10bc104c504a504850464fc20fc00f49cf47cf45cec6ce56ce54ce52ce50ce4ece4cce4ace48ce46ce44cde9cde7cd92cd90cd8ecd8ccd8acd88cd2c4cf2ccf0cceecceccc9fcc668c00cbfecb9b4b3b4a8989e549958993892e488b4889488747ed475546b6c6688666866486628660865e8635c633c631c62fc5bf85bd85bb8517c515c513c4780476040a84088406838443824380437e430ac308c306c304c26a8268826681efc1edc1ebc1e9c1e7c1e5c160815e815c815a8158815680d50056400200002ffea4bb4ffd4976fffa48edbff491dbfbc923b7ffd2176dffa42ed7ff501dbffa403b7ffc4076ffe880edfff081da7fea4b26ffd2764dbfa4cc9bff48993ffc51326ffd21) else (if i < 3 then 0xffbffdb7fefffbf7bba878000fbef7bdeeeafb786dfdffdb7f7fdfb7bbab7f1f7aaffaaaad17d6a87f9f9800300d212c0720e4368382e04b414844060a140885c098f36cfefdfb67ff3fffbffdef3cf7bfef7bb9ceefeeeee79fde79dc4fc95490b59faaaaf29b3ff37fbfedfef7bbbd929cfeecef382e71f3efdf9be79cf8937cfa8440821041606d0508a09a0190f21702837c687fb6fdbf5555dddddd5bedf6fabb800000605555681bdb7b7abbb7865a01684507a0940486c0a87006fff7c1fdfc55f51ef15dddf7715ddb7fbedfe2bdeee000a14aa8dbf7fdbf15ef776fccb82001e0600580c28207c0102e06c536d9f7fbeee7d493ea7739cfb853ea5cf7bdffdef3ff774e56fffeffed9ffeee9cb5ef7f7f3fdc1c9e7f3f7e7fb884f3f636ffbfdb3ff76e9caf7b7fdfd9fb034064150270183f80b01028e0042283e26c6800036d9fdfbf773fbde7e79ee7739cfb86fffeffed9ffeedde72aa9fd5495b7fbfed9ffbbbce6ff57bcfdc1cf279f7cfddf1e1f27d8a7f52e5aab54b03c0740f0190360609e0ba05c0d42282626c6b6d9fdf7db3ffb7fff7ff9cfbb9dca7d5553f7e7f7e11e7bde7f78479b3fedbfdffb7fb95f9e773eeee55ce7753eab95496af79fdec720f3bcb044084110190360605281c26a0981b02d25c6b6d9fdfbf6fffefff6cffef79f9e7bcee7e73b86dfeffdb3fedfef395554fea92bef9fdf7de73edf55ef3f7839e4f3b9fb8f0e4efbb14feb525555eb26108208420720ec1c1304d40c43485a0929b1a17ededeeeeeee006f6deffbb8aaaa8adededf771bea070062aba2aad181c01e0607f80904c0b87000000000060000cf02282914154000000002282aa802509b0400000003de001eb5f8001ffb6bf1a03bfdbfae34377dafe346ffff70f1435afa0180331b5c346eeeffbb6982903b014000968786a05c110a68358b00006db6def6dbfedbfff6ddbfbfb7feefdbb6bfedafdad6dfeffdbfdfeed6f3fb667ff66666df7b7dbb5b7df66ddfb7776b766edafdadaad66d6b66f7b666631b6cd82300027222c3c8704dc1409686d0bc13180000db6dbdedb7fedb7ff7ffebdb56b7fe7b63336fdff6fdfacdbb7fbfdbfbbfeddacdbb6fbfb7dacdf7ddb5ed56cd6b5b3d9b0ccd8dbbfb6ed66eeeddb580bd0806a0a50002561f82826e09a1b42e3001b6e6db7ef6db5f6ddbf66effd6cdfffaddbf6f7fbeffb6fefededf6db66b66b6db7b7db6db60d413d006018010fc2544a5462694d8b00007fedbbfb7fb7fbfefb6edefdedfff6ffdbfdbfb7fffffef02db76ffb7d7eb6bffb7dbf6dbfb79b0b19b5d6db7609d84502c004790d83525d0951284d0ee11085c7000000139b66fdfa9b7fb66a6ced9dba9b3db3dbdba9b3fb66db76f23e77ce7cfb119d9cd98233d9b3cc7db089eb2486b14228382441411024a091 else 0x6fef6dfedbfffb7fdbdb665f30666675b5ffeddb6d982c03c0010e86c2544a4201a87b10411085c6b7ffbf7edb7f6db6edbbedad6d7daddb6edfddf76ed6b6bed56d666ccff66666f6db7b76b76d7b36db6dff6ddaddb59bdb336db333631b108c0b8001a9070a382988d0fc1314002a7fe7e6ffef6636ff893acf31befdbeb04e856798ddbbfdba6e9e6cdfd37d4fedde6c6f7edeb37acddbcc33731cc6ee6e1290a608c0182826f0124e12c878828b0e755fd7f7dfb7bbb7fedfbffedfedfb7fd557cf6f4383e677664c37fb7edf6cbdb46bdb776c6f04308c04c34020900e210c1310b415166d9ff3bf77e6bf99affd679af5ede4ebaebae9aad7aba63f9f4d99cffe0cff59bffce6c134d2e98c19befac92c63183d86fa1001a828250090268790b0ee1ae300000cfd5b366753edfe76fa9fd9e76f6f219f3fb1589e2a9214db67eddbb76ca56cd99db6fb7b64dc86cfb3c1b370228a090a504444a82437c400000019b63fbff7f33fe6db3fccbf67bffad3bb3fcedda619f9d8c7fcf1b3307db6cf6fb5bb67d9b6cf2d56b6d9b343367ece0d9b02740c09688a051058282487761a1be2c00bf5f99cddcddb9bdfcdfff737bedf1ff19fd9833b3e30a255203b6ededecd9476e6f7fb6df66c9bca69311268820ef8170880306089421a090f3140000067c3adefc3dbafff770eeedd6bfe1ffb5ad0fe7c00000305fffefc3fdbb7b76816bed7ffd7ff541a000000890fe05a85d0740f4168020d0334382806f04b1c067afffbf0ff87d7d7eef0edd75afe1fdaad0ff3c0000060b5f0fb55aa05bbdbaeeeffd0680000c03e06fa11400258350920b685a2704b1600000000000000000006006f0fe66e1ccdda11ad0e36eeed0f8000de1f8db76b6e1b435abfe9a01800c601be84505a001b825d0b04b1000579f7328c67b37e7f66df3ffe6fcfec507f828c61ee6c6f9b336e68c6e06b00287b0f0882343602584b120000000000483b7dfc8edde46e000edf7e47fedc0080115450edde46eee372530c03021800003006f41081c3420d0c009422440f7db1b8dda35ad8db768f000000d8db76b60000060014038170104b0a00000048023bc8aee456e00076f22bfb7001007722d6eee37221860181801800c600de1a03d8250890a781b03706ed0cd6b60db769e0006c19b6ed6c01800c6a01c0b80825840c0060717878dd70e7f9ddba87e66d6b4000000c00c0bffc3e376f6ed0286d7fd7f543668890fe0d685d07a0b4382806f04b140018016ff0fe2e1ccdd7878dedd43f1ad680000060060038fbbbbeefb4028d9bff5ea86cfb43f869a1141c3650b0921bc12c4bb7ff98ef77cf1dd548aaedfefe6377ba8007e000183b77cc777756e02aaa8253000608450720f40086d0212042c1344b6dbffffffeff7fbf7ef7bbbbffbbbbfeeeaaaabd556d)) else (if i < 6 then (if i < 5 then 0xeeefeeeabeaaeeeea1f00001b7efedfbbabb705aaa415b7bedeeeaee19bd70400801b8141660381f02d05449bbff37ffe554aa9e7e79ef2775778fe7e7f3ee438df7fcdf7dbabcefbe5554aa53728f0f267e67fb90ec32c6c1082103603c001130540b11483439c5b6db7ffffff6eeeffa8a29dc771c2aff54b9ef7bfdef7bfeee9cadbff7ffb6ffdff76e9caf7bf7e0395fb3cfd9f7c777d883cf86dfdfedbfbffbba72d7bdbfbf3ec10c1b2068078181b829c068160260042303c26c7001b67f7edff67f9bffffa9f2aaee7f9ddddd56b3f555d3cf3cfef2727fd9ff9bf7ff6fff577578df67f7c9cafb1e7c73f3729d0e71e7f794e5e1ec3bda0460680c8182ca1108410d06a0981703c35c68000000000000000000000ffd8007fffb5e0007c7a01dfebfae342b6bf8de35fa1f6d7fc6f1b5adf803000b5c2e2d55d7308208741500025c140c6878440de0d62c000000014e6d9befaadbff37f6abfd9cdddba8cfccfd99467671955acfaaa5956cff9bfb6dbb365519fb67fb0598a79eef9b9c3c9b9ea1141441224a160910484b4141de28017f6ddd7dbdff6fffb7dbf6ff6ffdbdbfb7dafdec003333f0dfedf6b65eda7f6eedbfedb1b611c0912b0d0ee1904684a4061c505459b7bcd6735ae735fd77726bf5fffd7ffaaebab4c67d37ffcffe7fce0cd33ff3fcec134d280ccdf6b24b18c61182284207e0f61cc38f02e038250188f0ee1ae38db37bcddff9bbffcddfe6effbb99ff99ffffe637dffdbbffeec4f255211a9a993524cff33fee70d8326fbf6ddbbf97f46ac6fb7bdb76ecdf52b66f866a1f82203911c1a43685c0b44a0244820a0ed1cdb7bdb6dbb76ed6b5addbbbb5fccd9999b6db6ed6dd9adad56b359b6666336602a00e87d0bc130af6dfefff7f87cfb7bfffbbb7ff6f6fedfb7b7f03edbf6fe55d556b76dadff6f6ffdb43ed87edbbb6d6c22843611815828380a20c00589004c82885c6800000001b66f66dffdb3fefffafeff67da7ff77bb3fedda67b3fcec66fefe7fe7d9986cfb7ed6ecfcd9f6ab5b36699ed9fece0d98cffcfff27307e4c06b0183504b4444120ec141242287761a1be3401b69b36edadbdb5bfedfdbfdffefb6fedfffff7d9bfedcf5b7efdb77ff6b7b6dadf6db6cdf6db6cddb7bff6db60d413a0680607e88310c0013612a251161be340001ff6deedfeeff7dfbeffef7fffefedbfffb7b7fb76fffbff7d989bfedbb7fe6dfafeb6bffdbf7ff7b7f6db7b7db02d875b5fffb6db08ac2201d02c001c41391606b0951284d11a2082210b90000036cdf7cdbff9afff3febe6bfb4e79cee71afb55dc66f7fe7f9ecc7ffe35fedfb5cd7e33fe67f67ffc3618d3474c4c6bd7aa5a97ac686f0c14210420004e09686e0a01e110858820eb1cdb7eefdeedf7f7dedbff7fb6fdbeddbfede01376ffcfebfd6d7ff else 0xfd66bfeddb1828c10c210191a29b0c84682704c43d05463d997ebf33fb6f6ff9b492cdf7b3e7dbeb122c29b77bf9cedba6eb37bd9fe7b7acdeb376c31f1336399cdcc70dcdca1141412a07a1649c2590f10512000000000000007773bf7e6dff37ffe75fbb4f3e79ef3bc6bfe6bffdaaef19beffcff3ece18d7fb7f75e6bf8cfccffecec30c50d3131afafad4a97d6342283d054000e812e0a01a11085d021041d63555effffff7b7fbf7fbff6df7f7d7fdbfd7afb00e37b7ffedffafddfddb77ff6fdbfb6dffedfff6fb63be6d9b7bb76f6db022a0f41582e008344201ac2544a0b841044a0442e3c00f3cefddf9af99bffacabda73aebbbbbba69affab55ee98f9fd3679cc19feb33d9cc1352698c19f59648c6284507a0b40002025a0442c4106b8a003f6fcdfdfcdbff35ffcfd7fbbfccf33d9c67f99fb383e79f3ef7d2035fdaeb365f1bbfe6bf6eeece4d35edeef7bffd936b734983e4d21670410820a0c00302741211093a250f318318c718f638c33f63b002854fb13ecfec0318f4621498158082f04a8450488287331ffdfdfccffb67e4c3d8b67efffaaf63bb3ff376d73da63fe7e36c331fed9fb5e6b6eff637db3e7daf66b766f8363ffcec366c0d685a08a0e097052060a1436810826221fe34bfaff3f3f9fbefff37f77ffcdf7ff37bbcdef6f1ffbb19fb7ffe144aa41f76fb7dbdb28ddddff377eddbb9370cf678c366c534d312688770be07704307a0a00c0e02744a0a893a090df1c00000000663f5f9fb7e7f36ecff998963dd9e7b7ac7767f9dba5b98fe7c6c331f767dbe9bdb77d949552ad594331effec3ff656c2083ed08a0e0940b849a1649c8687f8b00000000000000003fcff1ef5bffbfe61f17c3c16bfe63545bb7bdffe375b8d31bfaf8dafeeb5ff98d532b5a1e600063f75ccfd773bf6809688a050720530505b6040b704a27a17180000000000000003600c76a0c76fbed0000c76edadc078af47b418eff6d6f99bbd00600001800c224e048283b8500890c000000000062dfdfbf31be62df6f316f6f00315b5e8dbbfc5db76e36b662dbede66d6e030017316eb9956eb7012a0740744587e090ef42e20000000000055efe7d4ef25b7bf866cfb3cb36ffedecf26ddbbfdbb377966f66dfbf6e367db0ccc29d612513d936ecdddbbb6581f0001ec141348f0442165362400000000000000001f0002ddfc16bda196bf6a800003376b6830b77bff6b46e01800063003022382303803c1a8944104488000000315fbfdf98b7cc5f5cc5bb7300bf98bfb7db8b5ff8adad1abcc6f6e36f7fda62ef77733dbbdaf7018000097052060ee8168887261a1d285c51beffcdf7cafcaa9ef7e7bdef7aaaaf4e739dc9c9dddd5dd5c67e67fd93cb0e3794f43867f33ffff93cb0ec1832208c0b80d0184dc1102d0540f0d716dffdfe) else (if i < 7 then 0x63400bf5f99ff9bbfcfb7cddfcdedecff77b78d8cffbeffe144aa41dbb76ed946db377f6fb7b26e19ef9ec61b6cc6a6a6a649535321dc0460706b834018820548950486f8b6dedbedb76eddad6ffad6db6db6ed66fccd9999999b19b6db6ddadb335ad5adacdb6683504a02001f02a1782a1c0000dfdffe6ecf5ef4cfccfbf9e35ffcd7fdabfffc7ffcdfbf337fedce1c721a6337fbfccffbf9e1fff80f5f6abe571acb754ab3aca1749381521041f8002720a2348650ba04894410768f1fe07b700007bda346f8dc7d03f800371dc6b71a3457e8680800b40b0500ca1782413c40000001fb7edbefb6ffdffcf7bfe79bb7fbfdbffbbfeffdcdcdfffb67ec31f5fedad7ffb4b58dfdf6fe7b76cfed33ffed9fb618666ddff7b9dddb35b7635f6d2d65ab6690720b8001ab110644330502704b40a85e0924f1c00006ff7f9bded9fce7bb3fff5ed9fd5d8df7fbecfff6b9da66ffbfe7ff3fb6199b3fb5cd6df7fe37ef6cfdaecd6fb37e67b1fff3ec33633ff9313e1ff9f805a85d0704b8290001a0a14344104da04c443fc7000fffbfdfe7dbfe7dbf9fb6fdff37377fffbbfbf71ffe66cfb6625b5affdad63cdededdb3da61ffdb3ed98663b6efeddddb35b76c696d6b2d5b341a90860f417000202080c988827c1542f049278e000001ef000f0000fffffed7ff1f5f01dff5feb8a1adaff1f46fdfa1efff6bf8fb46fed6fc0f018065ae168baaeb8208a6d0740e80012d0dc15408170440fe0d63455df3fbbe7f76766fffbff14f4e7fdcdbbedd6739b7b7bfdbd37739bf4dbbf6f30d9f63399853d0b2519d9cdbd377b7bdb262382183e000658281384424e42ca6c580001bfdfe6fbe6dffbb7ffc97beb1ffbf7dd9fb7eb2954a99bdffcff9ec32cecffb7f4dfabf8ddf767ffb759bab3733ec7e50cd8cf3798f21e72845054000d412814c1542c2684b24e43c3fc6bffefff6fdfdbffbfbffbdfef7fefdffbfff7fdfffbffffb7ffdbc0f6058ddddecff5ff5b5fffdbfdbfeedbffdbfffdbff6df5f4efb7dbfafd6fdfdb6114170003223c45c0b02784a894410772161448784422122000000a736dffdfeff55b3fe6ffda8f9efb2ad9cdddbbeca33f99fd87d9553d52acab679bdedef66ecaa33b1c659b14fce6e7e389b81211250804943d04d02092111050828b00003fb7f37efcdf7ff37bffe777fddb99ffccffbe71bfdffe6f7f6fbbbb13f255211498d2337feffccfef9d87f831bdff6faffff9bfd1d6c6f7edbddbb37a96cdf42f041072224141912704e02446a25a048283b47003fbf6ffffde1ceff7f6effbb7ffb7b7ffc3b03b37edffdbfcabd556b7b35bf6feddb5f7df737d9ffb7fdb6b23b821845074060920d03e24e42c2804d41444239f7fbfff7f6abd7bdf7bf776ffdbedffd557edbfb7dbf6abda1c0ff33bb260dfdbededb37f6 else 0x106c1531b7bc80c401531bfffdbc32a7c7b83edd531b776e19bbbaa636fdfb7986fdf6edd522d0556ad0fa16828280494134421c00cff1ef76ffde6079821dbfbcc6fe19dad7fdffc6834c6f837df5dbbfcc6e19bb5b9f8e9f8756bae98d06a96d504b44500017a1e42f0505110c1128845953d7e6f7ff9befff95ea57aa99ffccfec9639f9ceeee482f7edf556cee37bff37dfdbfd55fe737ccff99fffffcb206cc6e48739b84d70410820e4141512704e0291284c41244037c7000018eefeefe63edfe637f80c01f7e637edf867daff8d6d06ba6341b569c75d0e76ad57de636f6f30ded6d76825a2281687887a1643424d1089000003cfbbffbf8785557d55dbbf87b7550f3e0000061dbbfc3dbaabb83b7ef87b7eaadc0dc00006288a0507342c16d0c44e44012c4878000370154155406edaa8000005555500070204a0d61000009076fdf23b7be46f0077fef91bf6f002011549476efe46edc6e28000400000301a102d110a3c083a82508910401007791409f81df22d33780040000183bfe451bc6f83b914cdc6e466e2240f079e041d012850870801edf08f7099ba8557fe11bedd400000018046eeeadb81ef099bdbab78336e1a68887461b43012c3001bbfcd7f35ffbf4cdef33eff31affe6b6afffc7ff9bde66ffb73871c8698cfe66fcfc301afb55f2b8d65baa559d650ba05483f02e0144486890a16431128820ed1adfddfeddffeb7df7eb5b6fedfb76b7fcdf7d9999bdbb5bde6dbfb7eddadb37b5aad66b5999866602604801027a2203305702a1782628008f148aa62b750000000c56ead811555414000000a70206a096100000002db6fdbfdfe1b50dbefedbefb436b5ff6d56b436fff6dfb6b7da1dd55d57686dbfb6fdb6b7dadba1b7bd6f7b5b7bbb6b780f33003141e80824a1a8938104441414104c50000000036ddf6db79b6dfadbedfb6ffbfeeffeffff7dffb6ff7fbffff6ddbd9ffaffedbfbfb35b6dbb7b6db7dbf6db6db35b6db78428730c6054070043526a89c93c2544b1800006d9bf7e6bff37dfcd7fb7ccddffcffceff98cfff37ffd9f079cf3dde901afdad66cbc6dfcd7fb7fdbecc9a6bbddf773ec9b5b9a4c1e4d381c8390106b4470690d00c2090484444a1e)))
def level12 : Packing := (282,3,8,0,0,16,1,nd12)
def nd13 (i : Nat) : Nat := 0x1b3cffcc6dffdfe1e60f0636feff6fe19ffe36b5ff6834c6e0dbbb4c6dfbdbf0cdfb5b98dbef6f986fb5b76f98da0d5ab6b44a9108400a28f46a2c9b0a84a42300030f84c098dc58aa131fedd40f8000030098ff6ead804c6f6eade0cde0600061220c45e091825866db6fefdb6fbfb6eff6ddff6edad7ffb7f5fff7dad6dbfff6dffff6fb76b7e7fed99ffd9999b7bf6f6ed6def66dbfdb6ffb6fb76b6cdedafeb56b6b36dad6cfdb6cccc636683a1e0281802021a8d1a895230ac122e131edff6dbf7f6db7ffb6fffeabf5adbbb6efdbad6df7db7dff6faaddbf9ffb667ff64ccdbfdfdbfd5bb6fbfd9b7bdb7bf6f5addbd9bdb77edd776dd9b76ddb3fb65998c6cd0844401001a850949a8f46a2d05098d001b27fe636fbfe636efdb840c6dbfdbedc7ff1b5afed68d31bdb8dbded31b6fdbedccdb5bc2600031b5a66ad5b41282e110780435230ac11111716dfff7feaaa00aa1dddfddd456dfbfedfa8aeedbeff6fa8b5ddbe620036f7f6f516bbb7b79a100803014130682c0e000f05c5b6db6fb6dbffdb7fff6dddb77fb76d5b5fdad6ddffdbbbb6b7cfdb33feccccdb6f7dbdbb5b77b36dffb6dfedb76b6ecdedafedadaab36b5b37dfb6666c6366d084401d0b008682c12258523d17098d000c31fcc0e637098d687e636dda078001801803e636ddad806c6b55a1b340c006182210e8500239162587006fffdffddddff7755feaadbfbff6feeea0003deeeaf6f0dbf7fdbf7756fc7bdb7dfedf7756f8f6f6f980030880401c1a0b43a150806412041318dbff9e7bc73b86cffb7fef394fea92b67fb7ef39bf57839e4f38f0e4ec6cfedf79cdf56fbd9c088381c0c098340c1a0b801362db6dbdfb6dbffb6fffdb776ddeddb56d7b5adb7fdb6ffdb6ed6fcfed99feccccdbefdbeddadbefb36ef6eeedadd9bb6bdadaad66db56cfdb33318db66842220e87802004b0a26a3517098c9cb4e3a4a8f9d68233f16529973901c60b905c01f88958001ffddaffb27ff64fff03ffdc6ffb0fff61bfea3ffd46ffa0fff413fe42ffc86ff90fff21
def level13 : Packing := (15,2,7,0,0,13,1,nd13)
def p3853i6 (i : Nat) : Nat := 0x9
def p3853i7 (i : Nat) : Nat := 0x201d
def p3853i8 (i : Nat) : Nat := 0x35b
def p3853i9 (i : Nat) : Nat := 0x41003ca0039f040183003014c048
def p3853i10 (i : Nat) : Nat := 0x1053b051010a278612b824543f02d80bc062e832813e19a07ca01c035408307ac06f04d6205114000111f60fe211010085a0002844a187122000502b4560074f944072a04403a000000180e4134a1e000149d0858609c001a0d80234029708f5610190178001852b049419290f196d01fe1b186b4151415594af65a1fb615a9e88560006832e13914dc03901c4148876c49763b21bf004852026e000101400068160004830403503c217000140a400941a5046c00ca0e00068704c10f2238580004df813e240800218383420010000041081402980
def p3853i11 (i : Nat) : Nat := (if i < 1 then 0xb7b7d817c0001c161b23e4076c0001819f568780001412f01575600a07274125a0330000304724990218de251916f74317418a7ade0000000008350d039b82e903840000c0e998549993c60d3a2de78168409ec0913040505ca804d407b107f88621836ec0e850c0c97320093c1b40091905edc2c700db30a5a056a46e321920072a07871960000050dc000000000c114005e8000000018153a0bb2022c0000e03f77b50000181c0c349e011b000780d7c1a910a0b82c003cc0000302e0832b406a0000b073381540001f5cd00000000081f80087000030b4800000000000068a94c21423520000300e606b80000c073800039818612fa048206a08050636ba0aca85965f5865c800e5e04da83230050a0a2792fbc2008173c6b2a07a3031281bd81a74012d4544000092c3e005f0226c82640aaeb280d82060c00044f3050430d603cf7e630d4c0001e0d01045380b21ed22029b018c0551c278c03760192170780c4200ea0db503dc58338c0e81826068642c5005421298000186e981cf40a1e875981e2215d000040668c258c01a4020a05fd021e2faa0000482742b99c38a00003046f40f4000090110033c432f3571f0a16847a422bc0d9e038486c40001c34d577ff55c1c18f6ca560b5d8d584b8b247250630879400cf406fd03560271c0e3c30360557011380d80000003278290000176cc12dcc0332036a0000917040503eae400005034b8617006c00000000000000000000000006514741b4c355e025000038b8c0000706bb00ec0001a02ed1a5c0196821088a97036d81f1c292e0a2604703eb7c2b9a196f04cc838ec71a207530e7203740000a0dcc08398476009ba02770eee023c431ec0c230911031342680000000058b5e82d4000091afe841743360000e861304080000eebfe0a2a043843c841c5e010e8427c0e54167b3510056c81ea60420009800000000c4bce751625800000c10d30036871b4166ecde104d6c59f0b7f008dbadc885d4000181d8c0d6486cf41d3c1ad31b0b01f786a32f95a049902c84142e166c0d20838a0056e19c674d7032ec4bbe0ecd45470491c2dbc30c4001fbee581e180eaf0864044a404a00bed08b000010376c11a00020a01030f0000021902031b300306170d0204000f0f01000e00260d150201140d2200010001010813000200171c0305050233000c0a0606000017100f2c3400010a0101000a10060c094310070108030c2201130522051505050303000404061403010b04772e0a0c001200000808067e270201020001050006130a0304002c01000e200e03031c181b00002f07071d123229001630040005970606061a021400030b06150c23050a0014100201000801040a0008051a7f00010305011203182001040e0d0e000c0703000000120229000106291408070302042623020f16 else 0x24c640ec8130800000000000000000000021a7a0b700000401bc1d0d008800015f9aa008508bb8d30839a0000c09bf16f8000040fd10d7f8146c070a1b2884f7001f429d00b8704a682bc815c43721000280f9803641bae0bcc04c6c67d60eb40e200041834788cc30c10826180048c0b1055981d802e38120a2e3d0d5c0266600410532014dc1db6138105fc8065c19140c1d092b85b1d834a1ae71b15070501e6a1990024701f9c109c4c050ca5803e82f040b630e6182d6005f8083d023f159cc2a30fe572e1d85a002ef02def0e9616ef03a2805d507a287a4c0bd2cbfd046204e603a925c990c9885e8c29b80168052d973742c1403a119eb021b02e1efafd09f080a8d86921dab05be307200ddc1caf02953018830fe018b03cfb01e426aa103003c1839001dee0ce6b6b9865420f8202025b388103837e0119f0232d59cc2bf4024e00fc860f4951c0bc2064a810c0257c08180ab483eec1adc0f9009d58d9c823ee10b50c02d6f60186014f315f4b0290294e1a5a04df8413027681e3700a80001c10ba35860986018f581e818c909530c7b824e80b9d0ba605be00afa1abcb6f2a283015b00a7b60a982c540b18f6106088b002cd6b41d7a7d5f0071c2bce045060daa270c27b2fc7000f6016581dde0e1760688180000000d2309f9877d4391a1be60a4484c843c4eea0d066f077081f5e19ea2e0084864b8841eaa0a350780c596000000005819a03bcc118a1a7c571f000bc0a07609c92fe034120d4e00673e8901aa814c30976005082c9831d30bec82565f7941d5b602bc320000000000000000035d280000e096d8442c03ac347e0de3be45871800f65083202b1c251c0de6aba00003c13c0000302b506c3d07f034880cec8048c1b10169a03be8c3900fe0088b551d86e58345ac16b0187069b494544c4f0cc300d2c01541297016a2a8aa17fc2bda0c80813240d080b480d5605f1015100f85182f020ac1a2716117de803fb48a3c2ff07b9585f8c309e6cb40a86051c0001c158a04f80000414661c3000028f8dc2220000eac3e1306024ca0c5e0f39d3081edba4c3902750259038fe0bb80e0002a780c20000b0c76837ced6a000000000000100b68276607908024c016e03d203a00001420200)
def p3853i12 (i : Nat) : Nat := (if i < 4 then (if i < 2 then (if i < 1 then 0x190211900b420c8d6182280a8a2383c17aca194846a480000207ce00003d93778add90af2c0b378094f82a250cebc18d78131e83ed10469c010edd2e50814c620ce03040017e000c30940619cac27178345a003d8c27fecc1803725065a22b17c13fa0609525638c9c04cec5803d9154de887c02ca08ae8909d9213a481212838c60ba7cd860e9bac96197b43f60301417b381caa60ce2027bda0ec034220adbe16f04051100e920772200aedec6b0334f766d614c6825a2091f07022101010128d20f0d473219090104120016170002030000112f1101001e53127c00360000070302126a0100080400560414061e020131061a021204220e110f000204010908000404110c0001000c0b1dd00502170900002a000205030a0233000a131100270217040623050002020006000002124e0300021c0311000007210f022b0001010262052931010902070519003f01120602052b0000000313051506020b05020a27111134000024290b1301070901170101061f030f09000502002002381e0401381d21050109011200001a00030013010205210f07000201030c0f4c0712040a00110d2d020725050700bd03001e040a0021060a030200000100031a041300041506000f0103292904109602000a010a0000111803070b0004022601050f51220437084200046804000106040010070303020f041600010d010d000300010d2f160600210303021b1b18090204100d00020202002e000403100e02540b10020010000200d4024d0023021d22001211011420021302040200030c020000090000140010000a06050502031007150200100e100906e90302200d100d4d0e06010f031f020b06004b01062b00064500050a000427030000b31401060d0500000009341f1f050d00530a060401075c02033052010f02004a043b091105004100280436000b0126010e030d1d0104000e00030001061f00081a1001011f00012201000b0a001e03004300b405000104002f000e131503000607040b021a000104000a16030036000c000b000c020c0d0a0805130103040103030f0000000a0339044b18270700082408000b030400030407000014082701431c000815851405000208010817020500030a03092d00010336000b000b021c010d012f03160c0000020000000203e708020801020005310a01030b010300000702164c0538100202000107003c15541a011908010906000400011b0200000519371c00031511010206000e03020b000a15052a200e002f150302061d0112060c0408130008110000043d2d1702030c0c00030001150202056a02131d26040f03610a040c000a000507030a01010017036e030203060c10010c9610011701000a071801030604134f3300000401041b072b050010060100001e010406030500000700240d0e061a0504 else 0x3be3e00000c085a449ce041fd6004814d8591c9000600000826e5830c780a661553a137dc026905f570a9360aeb801cc82b0303394109c0000000008abde8250941e3b01d9401582f46d4116c0bd1d004440ead0588ba1e300000000035ed1b83dcc03f2eea5800000000066484a0eef04e6604a7a03b0ca55502ade85db66673830580000782600000000000c24d900d7904d3c165c43228b828a053c0000184938000095689817a55a35d0400b0c56e05ba85a2181b000001c01aa440b0000050a5b4402000004012fc06394138d01f4002f226b2e00000c14ee85ccd083d8f48781b200000800e7af6a1849ff838a0000180ba40000504efc025d624cf80f8a827bc129600ddf01f2f86681336a2117741132315070907e134042ce8141af0bdf80e6c810638a16000003061d94f6282668b5f0000031eaa00000c04300000000005049e00000a07e3586f90139707256548400000000040bce0000000000000080407c0951864e506393789000000a0f880000d07fe0000282ca98649f7653e0b1c0485db89de01260068e0177f82b6d1683c0902024478afd26af60000000002057350077e0d7dc2970197ca07a26060cc11200000000000000000000000000001884f90b04702d74024ca1036193f8005950a0f01569aaf918530d0265c002dc1396004800000c1509583cc3e4dd0ba000001801200000000000000201b78820e00000a010400000000000000a16b4c42700163f00526147482aab04c9b6742e06be8273883a35abd00000000000817f00000c19328011b0e6976374a05c8431858577b0a3da16e61c3bf846ee08030d05805f3e8439907b5f664f1f1100000a00590014202d8102aa112ea0041a8226583675539e206ee9a274092970401ce3eb0242580e3644dda03ca427c889877190ac111540a008afb7738c40a7dc07d30a19e0290e032d80b2c8587307b36c483821f6bb9ba097ba028dc57808b72e054e8f710000023110000010005480a3800009007d00c0a40c9b82b3c76ee4c41f42e218550607bd42b11c128e535be966c8148c0189d8347215c9ace5a80b230585a037934d1341a78905e000000000041c330527b088fa2bfb492d00abda6257c0dd40000729c300000b5830821d000009047e00003812ba0556a0b540000280319b3a600001c03940000702dc000016058640f200000e07086145f4276bba6110c9a0000060f830121d07c4cce959f12100cee23a8418ab42f580000c0a0c8172e0438f01eb105f30163e5c474bab99028bcf8ff01ae502c81114b00ae3410c8000000001005744cefa8363526b7a278f1909306414075fe106d42b380000d099062cac00000000000000e097929a03d98ba05d00000202ee00000d1acf80b0300c3611f7b047380152011e3848e0000121908000058221c03e4012) else (if i < 3 then 0xe6bc03e1e030dc246732fa00000000036cc390230e072a8249901af2520f3466b011c38325b016210a5e0000181771809c30a8a4070cd0c19525ae02110450cc30a3be1e2079a80fab0100a0583b0b4a8e96380c84004020679eedcec49d6a61c70a7cc15b141ab899db808646c78482aea028ffa6b062b20456708aa7a0cd3a08368338eb1c4e09c9ae9d59c4f0b10b10b6f8473c18581829a7a3a6626eac1188853a8662fa0fcb824eedd843168a8040d45c0a02b1e2c7580b554129b8992d751b2185fc5bdaa96fd000fa053304831356db0094a006dc242f85c0402b704725c32b482f76684dc13d6832ea040931804c0eb9014048936f0b32219788a501038d7047c4087c29a670513008d02019b8330a20f2601d154fbd02d300be2901a1a1123807dc830fe13d12d3f3c587082ea71240014d3420940603a0a4a419b7c039283a9e01fc80e14c1e870332360aaa622fcccfa8393f08f5809c342fde85fef0191c12080182d032ca06826124e818f9012c826b142b9bc331084adb157282488d832003b700000800d202fd300cca625b812a5c0d3700bab0112f57c28041502ede673400003c25c0000fe01330e07d4822581dcb0c9e00b6f0b19c81bfb00292000800f3183ec90c090092e4184e80d4634218023682105827e70599acece01a5d39e97104620dac0000502a951cf4214656b0c00000800a6e1660000000288005fb24d32c06c59da520453e11c7c1b600607e01d98cdfc028880000b61dba10f104c05a336702f65070dc01c3125300001c027d00b838a27376b50f19c41e660027c00de404c0a19a9c1ca108ca2177c00000950da0b3c80d595845005ecf1670cf56000007023a22c798ea30010bf99da002ac00254130cd0378000012c163426de9e1c00001c08bbc1d23025fe7c3ac1929c086b066cf00bc42d0e02a0c016f000000000182d3b0026167acc015ac5a300000c052bec426433a0366b507fbe195c00216025b402f0c16cf01e9182fc20345809a8019c981e9145f1406dbd12e8000000000016c4000000000e050720a10017c400ff0000100d80000000000015eea1871db2f203ce802ef8059b84ade8882a1cd5058d20b1b8000000000a0fd1c6bd2863d70667c03e44270400b2f62d00000082b200000b02b968708c8f48837040af6e021c811bb861d6011de03d9c2ac7d5eec080c2066000002a987a6319a194c42a6d3a1ab0a4ded19e015a481cc915cb60a1c80e218543e0238000018049509acb60f9605e40000703e14043c401df81b449b36f040500dea9881482eba687f6ea13006af294d00000000000000102a0023a6648dc01563b054602e3216b80000284d300000e00cc0000255e4b13dbef8828318c8b90070980000080e6c04daf70e600003013d084d400000000004279c05d10000180fd800 else 0x61c00002c2530b44f9693820db440da4867a00001e07b981e5804c6d6440000039846284cf50bf082f5001dd704b25067c8176a40b5699cec0b8da2a8204af30294602324005c000038081b17b60000341f18000080939811ac02fe80000b176f0084d00bf0952ca030a00002c0c4c0214a691c00002df2a8000070b2400002c56d80000d056aee54ec30700000c000200002c6f69811500abde00450103800fc40710e0e50000018647e09e0628054243e0100a022400003411eeb05b1025b614df02c6d84a3a062fa47b1800d104b3e566dc0445c14300000d650e0000398851015f000002e1b6028db3dbda0a09018d059da80000a02ec0000300c65837d861c38104c00001032b70a1f01800855ab242100001a1830c3166014100789957a54126802bb40042c1734c04c201810073f015d6c2638043860698e36129a42c520ea0cb9c05d4c1c70019271a11e00740000284d700001e0563c0798d5e2f020ba03ba421b6002af637c61955c04b80a3bb64a96011ec1a8316180a929e06eb411c08667005242152e5a28198aa20a54c0581049dd961cc64584cf224186f044d00001214510167202e227cbca2ffd82a7081046731a22fb401ec004e8409634149000005089a110e6602409d9680000b0ccc00002028911100813c3816892af6f840cb03cb62641c3225065820c0c40b1a81d100a04200b1e49fa82b8b00cac07a80c4d845e37310800000000015d0460beac07916011540c100000d0bd5a0b4e4234f01a766170217de02f0082934065400bc4000000000306e6c063703271063cea9c84c3ebd95c0000080bff019428016b81884666ca0fbbd92ed15c6c80f84047c0000202b720a89805a5414e481ce00000a022a450b80000d01c2a83669d41a83cad67414276842aa405c51042a000019b2fa00030000141069409c0346500001c2070000000000d05adc13aa411558bf8f0a02213ad400e38310908db6171cc3204b455000000000000b400000808be000000000381db7093200001423a882fe0000000002019758134c28324112f80860000000000c03ac0262231170000100bd641d9c81a9407e000001003c73a78205d8a116c433c0000056acf62b7d85f9f8c2d000016076b873df8133f0786e01fc02b5e3dac4078c6097400005b02cf00ed0c45ac18ef8521800fa80527499a88271e74c70128ac14b10b83404fb219cfc31f584a83070e2c4dec299c3dd25048e417072dc1d8299904c4a04941c7ad02f300000615f881c7f84ac2063ce2b9e808a0000060579a01b186033d286b15f16862d4af150466a1cd101242c1f07d8767013a00003c07000000912b9a170c000018582a064920696016d305bb000014e37d423188000a15b90100c0000601b750b51a0d2bc2858061eb420a0082c000058337a147980a08000008)) else (if i < 6 then (if i < 5 then 0xc2de300fd404dd11616a19ae18c6b022bb0c454073d02f1305e6301f1c2c7800002834e00001eb7b582a9400aa00000414a40000000001099a000001d3b00000409b0019c0c25840315506190c449cb064026f0000020822c255800007179cad563c319a0331717b020cc081cc381cb2266c6e6600152281c6508c1a089d0606905189026c00d25428d08937d08f0147a74215e3111d0b7f2c402016f883b41074b4e2ccc4267058a1085ec0f904094605f330c3ea2c43d93400000c11aa0000000003845aa0414cf239980080000c0bc8c026e418b4b08d2066d4eb385f2fd838b00000e3094830500000000000000000003be493b56ee0923021230e1cb0cca0000000899bdaa612c980666815fb841897cf60000008e5c149400001e0038833dd83218011642f845a0580000905c000001c17800000d17600000000006bd4a07b4e00003c2b2e82913042460e2742182be2300000ab06901727b414e0b68a062b42248012bd79c5a0a2eacf7302a1f08f7a2ba58286f029763317613dfc12190035f0234c0e0dc12568120a22050122d4236302cba16b4600945d05705023017e02ca5c05f684540b322a0538812244987f098b8ce6c433b8811e6abe7a2adcc2529b182d08b000000c49e18601a238f62a70000038522c097680d0242c01b13510aede0d62d30d583cf7051a20f14000000000f0012af6b7c0aa8856150c90a1364012c78267664c8e0f01d8e770beb673baa2f346b047b459306312227302f1b0338008dec2c7d41d0191fee016d40246832fe0b4b000012133a01acf197ec018c2861c00006da0110ae5ed60c816cf03fa523dd010ccc2c5982e30000080939823268049a195b41598cb00b81ac0024600000000018ada2016a411e441ba00000804d8a08d9830900000308fe8a74c000078be50000010798c5ea8000060c0a02eb980e8c00adc0cf2000014167a3a5a968c180cee9c84000006084dc1118000018197000014c70f14ebf0101601a3000c48310e807cb125b4e05ec2bd3055fe1246ea4b359cef3040e26f60000280e80000000b7de102b00f0f02113037000001c24c00000f63814198c000000000907f2ef1f2001e1d823153c7815808047fa61890b848065010c37834d307de00001823980000923bfc15f420e9cbb87f077bc166d9f2080000303a420ed95e773066ff0cdc6011b82ebc03df80ba9228a041e14315230b9062e4a42f0e02af41672000020043000005014000000026f604f1a8c304196c00359865990a7040e030540e913e61af2613e00000081fee0a2d217a2c13b0bcccd17e8f07a400007803a0000142718c0171338d37170a1165025e0000020792e19aa429d983e6000fcc0e641f3d401430000062dcc4b1b1041420236808b1807120bcc4082c00003028190c0110a7a6c7c781de304048 else 0xf403d3b38f509ec011561e578ab488aa3ea02f3c1dc4b21130216603bcc1a4680d340914cce450240304ff40ced2026a055a7b937e1149402b800007bd6d00000c12eb41530000000000000014564fb584000014083f1899bdab6d072c5461e002898206b6326218b8000008a9e0022e0000000001b10e90214c1991c2612b07d409adc2f64c230e00613aa424261708f85024690895c1259c1df683f1665a6805780025c81e0715338e78582ba480bb7016f20759824a50233b08fc42e1f856cb83d5193cd82f9a45baa859c4022d2c7c1818cb062700ab342e58419483d3150614830170229e84297103e60bd04257983c1e04e62f47028435018fd0c1a0b68800de9347661223a47550228c8322d03be404ef9d8973114301b9f470fc2c8f81abf6443b0113a9afd040e80367819f3421af84f4f0351205f11c9600c00b000bf667d401f80000302852311c018a20069700db608965dee000002a66aa1500025b0000020b3400000c2e7f8b9b802056e9980000533350000180cbe01688000030923806cbc00c00000f006e0b81d00cf8805c000004c9780000521e68058b2eded802df82a891b19c0133c161584e6134dee0e46c596a81e700107c0aba816ee8064b019ba22ba01c11bdb2800e188789c2cfc828c308b96052c01228054a471fcc17c480c71b45850a12e2d7f00730000060a10a12696a68000000000000000428520931160ca209b800002814680b218053f185a8801010c33a2495c9b7981b100001c140282fc914f3c16ff81756403ad80a9b026a0000000001a3eff0bb2a066a00c393e4017673016d501e9f84c30000000003409b9828ef08d440e9a406b78255401a5015a01e9af098d1283922a7d00dae81edc0be1c0bffded03bd2ba08bc4586aaaf2e83e9f1327e0dc5c1558405bf021e1618d580c685caa0602227381100e8152a0758000024152f39f100000a0ff3c08ef8a9a40336e0197dedd00000b066b56cdb82c30b0b3310d76070282fe58ac700a562055dd8e360e1bb0607c077a00052031140c7041727c019304cb70309215bd4127ddab510b10949fb0244e057c500f2c0a0785cd704fae1762d4de383143822826725e14fe80e0f063700000c03d480ee80000301e2e0037006f8000080c2ce0feddd03800204092bc0b859a0f585f6f097d6067a8142f033d804f1a0da54205b839cb0b2c41633c5ff08107d68b820966699b00481d0c4d80ec869bdb862941ccc414c9409e388aa576964110cc60d2398720ca8af285c0e2e01f68016700ca1c0a9b055cf433b8259ac062c813ab08a08188dc1aa834d202692e0b0d8307f83bf40157b108e8038d3a4d108102158c18e0eb9366035484bd9c24690b77707aeee8f7eed2f01be793be4114a0129700bd90b53a399dc2ef483048742640d6a41651050ed015f) else (if i < 7 then 0x828ade00000000000000602658000840d6dddbf80000004934879d4027000d900c05408bf6d1c6d9cec060d2039cccf5e0067f0546a015699d500000a93b4c1074000058624006ff80ffb403000000a0a72000032cda800004018f007bec286482bea092eee4b66afd6813e0024f058ee9e420845710412612ba8522d04cc8046440203006d48261103d4007b2988780ac3202f4a0379de4610611b644660de4c052602d2005cb00528da60384a43156c800494208c054fb23d194d07d971c1d84d67c08d018c084f3062c0409e088e820b8b96fd6cf6811df420ca80744a10a40489407820442e09fc40c1e42dd60167917d26189558d61042260a9021347014500000000000000041cf581d51076000000800ff382c461fce0c6c00005c998d04a060c95410ea8421360ac000000000282fb00000a09580000083d61064fa0692c087203dbc5c39e0fd7de195c336ea1714086a41597a10460c372115a00fa685bd600c5007f1818918bdc70bdce2c866a67f861a534ddc033cc83e481ad70248800d910c230300209a4e3029026e00000d23e20f393c31050cdf67b878661e464708bc4a0c5e60907812e60462d121404dd7d806d0440e05a9c0ddac135885b2402b5a10b940dca04b56631700fcd82a9c80a737b8500b25c185c833ad075160fe0c5601029052660ac73e4308491c3a09e56015e41b0a834420a8d4ef17025bd80edc75980075c410d80547802b2a0d9542b4b81fb003eb42a8bc2154301f609dd82e5381cbebda9400d0c196ac27db836aa0420423e902dc283f700444a876042db5862d205a06138680f98805250cfb42f6901d6f0651506dcc0df242d5902898161a810fcc0b6c863b505bd0ca59831d784a17622b0f71742ec20636e010bcd5e48064c85a010c2a683b018263b3a280390f579802b8604bfe01b6357c7026a9039dd034082f3d42946b2b9b01088103c0095601c781810218ff1d7ed83ebfb568ac62802c220578216b6205cf42e7005e5602a1e2c630249001e3c09f82d08484f5a367a2a6cc84d2805e198437878f5a1301c2eea81f7309946865a08c3c8d8af049800ed501ae880c4060dc6397d002f8821c680110c4b31d2fcb318403c5a05d3da3428428670ab80cfe82189b46ad0be800b10c606421c7c0721865d6414c19951b06a9149b35da26058ef04efa8796c29e405f233878c2cda813af03dd208faa0113006ec0326a034302b8443301848f20173c15330489dbcf35082af1085007540110c074ee05f6c28fc3394d64c18c3448f0db0196e159bc0251809ef844f00ba42ec608220c0131405cf426f200c598505b26cd433298e38d852020476c02e1028803dabd06f6ec47dd82375102308048d50a42bfd8593b01fb0e4a101a9b02adf23bb0f3be4160f8c174002d4338246bdc063200a2be182 else 0x891ec265f212e682b50005dd0b49809a200c0703aab01efc06468061082b91057a0262ec0e12837e8158580d46427e98013d012c607f6812d30562f08ce615475137f816ca0b02807a041b3103b1302d730d4fc604a00a1400dd8022202ab8044487bdd4130782d7901ae601184f884848e809ee7157c20c6b99c86839a105cd003d280a21b07320150e11c9421ec8476170fb40674c7128056ee08f8a175a808c40405511ace16b220e5d8030e089c608d481b16ba30302a800002402d0000000001ec35b98a10934300001e67769e965b02d90010c0815800cc01c99032aa2b80c14dc0308f48790cea34052c8d6d214e842a5a0b1c184aa30a59817b4020e40323e05b140e0400006026d66398ec6d0000048613b03ff611d28e385b3a71080fe168e0132703a12093e265900000331870000080392013c80000606a4000000000439efa05f4a08800000500b1c0b1260c81028e3034620c8700750eafb7843b00000ee35b6ce22b20a304e800002c2160892e2084a2013c82d0d3395009ca000011c8168343000018074d003d9042d062ab20537013e00000a0a6a00001c21a68410c0051204ff805)))
def p3853i13 (i : Nat) : Nat := (if i < 1 then 0xc9180a4e9cd068309d484486c1be783582480993c0aef779b307d1df3cef59054f006241ef2c069217f82f7c09eae15812f6829bc08360e1e08a0825c805fac09c770a029440e2c05ee31b5910c0000ac22a721bb0ef00644267914fd032a1896c07500002086c0001007a105c8000000000000602c5031540a420e6a01b80001003a00000000702d902300000613700003409b40fd96079815142268afc5064e09f21cadc063813500000c22c40ef67648004c0001607900006022c1462b4f9806c8b043803922720000700b18016207fa27a483040000a2ab717e080660211e28dea08a040bc50b2cb600007344a047660fac187b81db04d80000a77b282b7c9fe34fad27f3891fc2028214d14830ad9a993208ff08380991813ee20ec06600003c1aca01700003827104d1410fc61b330440201a08dd013d1a7c0000606bd048300c34217808a1024580d7420c004ae04ca8426019140dc00004b0e641dc027486059024500da04fce0048000300892e3b000020004c9e44c3800000833f41e460fb00003804b41c6a08ec049a893c010080f1e028981bc000040ec803f5188a98512104c001e80cd018c7232e60f700fac130c04750079b94fc160a02b902ce8889013c611572755802301e00000a208e00f3c03d22690000781e000000000276c100451df40000a6016808800014068572a48b864073f4694057a83b569ec00006003f98cc81780000e27988360da21a49c400db811404a6225d1138bb43bec6cac14c68a18224000100e400005c0e36886a0ac50310000185080010e0442014280d4a016906bd8350246d60f41059ab9a649f500ce60857817501c52060e13040301dc702c1a20218000101f2b64700001037ed88f0066e78a208d80001a0d3904e983a140d3246940232b01329ebc0a4107fb0216c17f2c000000000019956a105c0639094398274026c611dd88841500000200a708c000000000121c200dbc1f98433261b8b0bc0001403b00006843ac16a0000906228285da1e60dd36368040e5890e0be872580002c21a2056b613703a800840000803e8000104da80fe3689800000001e0f5f77898c39410fa31400149819ec049a0aad0061d1a0580f6ce1e600e816840e66313a01ed527200caa02e906f43c401cf8eeb3005da828c00000836960570055c1d7e000c03653844000062776088b816f00e80000d01f808ea41cf60c2105a4bc1f41068241404b2f12000140000a8e120428246001be420c9a10608101061000224000023a0010e00080070e040080240b890a10c03186448900f41002801f002200880c424e04020010606680800e00a000808005002cb0000b01ac44144002e00687580d50068b4300020030ece29100020010a06341130210115002969000b000b00187001c0068e0a04001100c0870203607 else 0x2304882180025527ce8a0f59022c254024e02838164a4f6f070180a0c6212500e0103191f01ab20a7b282388e3c17020db400363ad9c0dd40f63629d014f9818e09570689832c00010c0300697b08000f8000000006021100f621107002ab280d84ea038d040a813884b6e21a40260000281d20000b016d12e59e14a09a102e7b1b80000ec08301a089af9cd1ec0ec08b88396c1f0a00a40668015781444632b001580e95893409bf0075bc3d01e7a1193610e0037605e6094f00d23c4d816eac0d605d284480001e04b3a79b81c8c00984f5102b9808cc104e25cd133282c5de10ef0ef27e80002c0630040c132a82324156828220383808558684d11500fca11e80c300da1234780aa582a20c3a02f909cec0c96086a03b83)
def p3853i14 (i : Nat) : Nat := 0xc22000c35f0c611000f1dd7800000000060a000000e67b42000b0d00031500019577400000030e000502806f64000d1a000979000245318b68800d04a0810b37516a00000000041c000000b65f3d000103000407f19b109b571436601b57a7394019056091a030101005043
def actualLevels : Nat → Packing
  | 5 => level5
  | 6 => level6
  | 7 => level7
  | 8 => level8
  | 9 => level9
  | 10 => level10
  | 11 => level11
  | 12 => level12
  | 13 => level13
  | _ => emptyPacking
def actualIndex : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 p3853i6
  | 7 => lookupWord 1 4 0 5 1 0 p3853i7
  | 8 => lookupWord 1 3 0 5 1 0 p3853i8
  | 9 => lookupWord 2 13 2 9 3 2 p3853i9
  | 10 => lookupWord 31 106 7 14 7 3 p3853i10
  | 11 => lookupWord 224 761 8 17 9 4 p3853i11
  | 12 => lookupWord 838 2845 8 19 11 4 p3853i12
  | 13 => lookupWord 161 548 7 17 9 4 p3853i13
  | 14 => lookupWord 14 67 4 12 4 4 p3853i14
  | _ => fun _ => none
def basesamples : Array (Bits × Bits) := #[(0xfff000000000000000000ffffff000000000fff000000000000000000ffffff000000000fff000000000000000000ffffff000000000fff000000000000000000ffffff000000000fff000000000000000000ffffff000000000fff,0x544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544),(0xffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff,0x823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823),(0xffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000,0x314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314),(0xffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000,0x69069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069),(0xfff000000000000000000000000000000ffffff000000000000000000000000000000ffffff000000000000000000000000000000ffffff000000000000000000000000000000ffffff000000000000000000000000000000ffffff000000000,0xa92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000fff000000000fff000000000000000fff000fff000000000fff000000000000000fff000fff000000000fff000000000000000fff000fff000000000fff000000000000000fff000fff000000000fff000000000000000,0x1b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000fff000000000000000000000fff000000000fff000000000000000000000fff000000000fff000000000000000000000fff000000000fff000000000000000000000fff000000000fff000000000000000000,0xdc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xfff000fff000000000000000000000000000fff000fff000000000000000000000000000fff000fff000000000000000000000000000fff000fff000000000000000000000000000fff000fff000000000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xffffff000fff000000000000000000000000ffffff000fff000000000000000000000000ffffff000fff000000000000000000000000ffffff000fff000000000000000000000000ffffff000fff000000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00)]
def basecolumns : List ColumnInfo := [(16,0,495,0,13),(64,0,447,0,13),(128,0,383,0,13),(1,0,510,0,12),(2,0,509,0,12),(4,0,507,0,12),(8,0,503,0,12),(32,0,479,0,12),(256,0,255,0,12),(17,0,494,0,11),(24,0,487,0,11),(66,0,445,0,11),(80,0,431,0,11),(132,0,379,0,11),(144,0,367,0,11),(160,0,351,0,11),(192,0,319,0,11),(320,0,191,0,11),(0,16,486,9,10),(0,64,189,258,10),(0,128,347,36,10),(1,16,486,8,9),(2,64,189,256,9),(4,128,347,32,9),(6,0,505,0,9),(18,0,493,0,9),(32,128,347,4,9),(96,0,415,0,9),(129,0,382,0,9),(130,0,381,0,9),(256,64,189,2,9),(288,0,223,0,9),(384,0,127,0,9),(0,1,460,50,8),(0,2,440,69,8),(5,0,506,0,8),(9,0,486,0,8),(9,16,486,0,8),(25,0,486,0,8),(36,128,347,0,8),(40,0,471,0,8),(49,0,462,0,8),(67,0,444,0,8),(70,0,441,0,8),(81,0,430,0,8),(82,0,429,0,8),(134,0,377,0,8),(140,0,371,0,8),(161,0,350,0,8),(164,0,347,0,8),(194,0,317,0,8),(257,0,254,0,8),(258,0,189,0,8),(258,64,189,0,8),(260,0,251,0,8),(280,0,231,0,8),(328,0,183,0,8),(352,0,159,0,8),(416,0,95,0,8),(448,0,63,0,8),(1,2,440,68,7),(1,32,94,384,7),(4,8,227,272,7),(7,0,504,0,7),(14,0,497,0,7),(16,2,424,69,7),(21,0,490,0,7),(35,0,476,0,7),(83,0,428,0,7),(98,0,413,0,7),(128,4,369,10,7),(133,0,378,0,7),(146,0,365,0,7),(156,0,355,0,7),(162,0,349,0,7),(177,0,334,0,7),(193,0,318,0,7),(198,0,313,0,7),(256,32,94,129,7),(273,0,238,0,7),(344,0,167,0,7),(480,0,31,0,7),(5,2,440,64,6),(10,4,369,128,6),(17,2,424,68,6),(17,32,78,384,6),(18,1,460,32,6),(20,2,424,65,6),(24,256,135,96,6),(34,1,460,16,6),(40,256,151,64,6),(66,1,396,48,6),(72,4,305,130,6),(96,1,396,18,6),(129,2,312,68,6),(130,1,332,48,6),(132,2,312,65,6),(132,8,99,272,6),(136,256,23,96,6),(192,2,312,5,6),(257,32,94,128,6),(260,8,227,16,6),(320,8,163,20,6),(7,128,344,32,5),(11,16,484,0,5),(13,16,482,0,5),(14,64,177,256,5),(21,2,424,64,5),(26,4,353,128,5),(38,128,345,0,5),(41,16,454,0,5),(50,1,460,0,5),(56,256,135,64,5),(69,2,440,0,5),(74,4,305,128,5),(81,2,424,4,5),(82,1,396,32,5),(84,2,424,1,5),(84,8,163,256,5),(98,1,396,16,5),(104,256,151,0,5),(112,1,396,2,5),(112,256,135,8,5),(133,2,312,64,5),(137,16,358,0,5),(138,4,369,0,5),(145,32,78,256,5),(146,1,332,32,5),(148,8,99,256,5),(152,4,353,2,5),(162,1,332,16,5),(176,1,332,2,5),(193,2,312,4,5),(193,32,30,256,5),(196,2,312,1,5),(200,4,305,2,5),(200,256,23,32,5),(265,16,230,0,5),(273,32,78,128,5),(276,8,227,0,5),(321,32,30,128,5),(324,8,163,16,5),(336,8,163,4,5),(385,32,94,0,5),(388,8,99,16,5),(400,8,99,4,5),(448,32,30,1,5),(15,0,480,0,4)]
def mf : Forest := ⟨511,13,fun j => basesamples[j]?.getD (0,0),basecolumns,deadautos,actualLevels,actualIndex⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mfValid : graphValid mf (boundsBefore known383) = true := by decide +kernel

structure MinorData where
  q : Nat
  level : Nat
  pos : List Row
  neg : List Row
  pm : Sig
  nm : Sig
  deriving Inhabited

def minorInputs : Array MinorData := #[⟨495,13,[3, 6, 12, 33, 66, 132, 264, 160, 320, 288],[42, 69, 100, 104, 138, 201, 261, 385, 386],0x100000001000001000000000000000000000000010000001000000000000000040000000200001048,0x6000000000000000000000000000000200000000000000200000000000000040000000110000000200000040000000000⟩,
⟨447,13,[3, 6, 12, 24, 17, 33, 132, 264, 160, 288],[42, 50, 52, 137, 138, 261, 276, 385, 402],0x1000001000000000000000000000000010000001000000000000000000000000201021048,0x40002000000000000000000000000001000200000000000000000000000000000060000000000000000000014040000000000⟩,
⟨383,13,[3, 6, 12, 24, 17, 33, 66, 264, 320, 288],[42, 50, 69, 73, 104, 116, 261, 274, 276],0x100000001000001000000000000000000000000000000000000000000000000040000000201021048,0x1400200000000000000000000000000000000000100100000002200004040000000000⟩,
⟨510,12,[6, 12, 24, 66, 132, 264, 160, 320, 288],[42, 50, 104, 116, 138, 200, 208, 276, 402],0x100000001000001000000000000000000000000010000001000000000000000040000000001001040,0x40000000000000000000000000000001000000000000000010100000000000000040000100100000000000004040000000000⟩,
⟨509,12,[12, 24, 17, 33, 132, 264, 160, 320, 288],[69, 104, 116, 201, 208, 261, 276, 385, 400],0x100000001000001000000000000000000000000010000001000000000000000000000000201021000,0x10002000000000000000000000000001000200000000000010200000000000000000000100100000000200000000000000000⟩,
⟨507,12,[3, 24, 17, 33, 66, 264, 160, 320, 288],[42, 50, 104, 112, 138, 201, 208, 385, 402],0x100000001000001000000000000000000000000010000000000000000000000040000000201020008,0x40002000000000000000000000000000000000000000000010200000000000000040000010100000000000004040000000000⟩,
⟨503,12,[3, 6, 17, 33, 66, 132, 160, 320, 288],[50, 69, 116, 193, 208, 261, 276, 385, 402],0x100000001000000000000000000000000000000010000001000000000000000040000000200020048,0x40002000000000000000000000000001000200000000000010002000000000000000000100000000000200004000000000000⟩,
⟨255,12,[3, 6, 12, 24, 17, 33, 66, 132, 160],[42, 50, 69, 104, 116, 138, 146, 201, 208],0x10000001000000000000000040000000201021048,0x10200000000000004040000100100000000200004040000000000⟩,
⟨493,9,[12, 33, 132, 264, 160, 320, 288],[69, 100, 104, 201, 261, 385],0x100000001000001000000000000000000000000010000001000000000000000000000000200001000,0x2000000000000000000000000000000200000000000000200000000000000000000000110000000200000000000000000⟩,
⟨446,9,[6, 12, 24, 132, 264, 160, 288],[42, 50, 52, 138, 276, 402],0x1000001000000000000000000000000010000001000000000000000000000000001001040,0x40000000000000000000000000000001000000000000000000000000000000000040000000000000000000014040000000000⟩,
⟨415,9,[3, 6, 12, 24, 17, 132, 264],[137, 138, 261, 276, 385, 402],0x1000000000000000000000000000000001000000000000000000000000001021048,0x40002000000000000000000000000001000200000000000000000000000000000060000000000000000000000000000000000⟩,
⟨381,9,[12, 24, 17, 33, 264, 320, 288],[69, 73, 104, 116, 261, 276],0x100000001000001000000000000000000000000000000000000000000000000000000000201021000,0x1000200000000000000000000000000000000000100100000002200000000000000000⟩,
⟨127,9,[3, 6, 12, 24, 17, 33, 66],[42, 50, 69, 73, 104, 116],0x40000000201021048,0x100100000002200004040000000000⟩,
⟨429,8,[12, 33, 132, 264, 160, 288],[36, 40, 137, 261, 385],0x1000001000000000000000000000000010000001000000000000000000000000200001000,0x2000000000000000000000000000000200000000000000000000000000000020000000000000000000000011000000000⟩]
def minorLeaf5 (i : Nat) : Nat := 0x0
def minorLeaf6 (i : Nat) : Nat := 0x0
def minorLeaf7 (i : Nat) : Nat := 0x0
def minorLeaf8 (i : Nat) : Nat := 0x0
def minorLeaf9 (i : Nat) : Nat := 0x0
def minorLeaf10 (i : Nat) : Nat := 0x0
def minorLeaf11 (i : Nat) : Nat := (if i < 1 then 0xb14000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000028e0000000000000097800000000000000000000000022e00000000000000000fd80037a00000000000000c6800000000000000000000000000000000000000000000002ba00000000000000000000000000000000000000000000000000000000000000000000000000000000000000004b4000000000007e800000000000000000000000000000000000000000000000000000000019a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004e8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000036800000000000000000000000000000000000000000000000000000003d0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006000000000000000000000000000000000 else (if i < 2 then 0x2428000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000089c0000000082e000003e00000000000000000000000760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003790000000000000000000000000000000000000000000000000000000684000000000000000000000000000000000000000000000000000000000000000000000002fc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 else 0x4261d950c805861c0150c82c4d0aa61d96c24084c3b2a1900954c3b2a01bc452a9876543010885530eca860a1104261d950c80448ea61d9530a3954c3b2a1808441324ba987065f5861c5c8ea61d52ca38a11d4c3aa59471408765032091408765032091423a9875b28e4775300ecbe04408ca4c3b2990209a4c3b299020c3832a190050cc03b2a190109c3832a10050cc3b02a1900884c3b2a19008cc3b02a19008a12d4c3b1c844000051c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000009d8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004b5000000000000000000000000000000000000000000000000000))
def minorLeaf12 (i : Nat) : Nat := 0x12a98706543b082330ec0a8640231300eca86404247530ec0a9d51c6601d950c80841d81410c0838aa61c1950c4208954843b2a1f142125a9876430e0882100eca860418247530ec0a9c51c4aa61c1950ec208cc3b02a19008954c3832a1d841210a9876543b09025530eca087411844021d950c8344e601d950c808482a61d950ec24092d4c3b2186844107605043020e4120a987653b09025530e0ca876104c482a61d952c24091d4c3b02a694712a98706543c28225530e0ca8785044aa61c1950ec208cc3b02a19008154c3b2a186044098765432004120a9876543b090255210eca87a508496a61d90c30220954c3832a1d841123a9876054c28e3300eca864045530e0ca862104421d9410c0824421d9410c08245261d94c8010421d9410c082448ea61c152ca388c3832a190050954843b2a1d14219807654320212a98706543a28225530e0ca876104661d8150c8044a8261d950ec218954843b2a1d14212a90876543b084247530ec0a9451c0b4db1d000ae9000000000000aae000000000a7e000000a4a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a130000000000000000000000000000000000000000000000000009d800000000000000000000000099d00000096900000000000000000000000000000000000000000092e0000000008f38c388800084d8120000000000007de0000000007aa00000076f0000000000007340007000000000000000000006c568a00064f0000000006140000000000000000005d900000059e5635330004f84c800048d0000000000000004520000000000000000000004170000000000000000000000000000000000000000000000000000000003dc0000003a100000000000037133a0000000003060000002d20000000002a200026e0000000000000000000000000000000000000000002370000000000000002030000001c819800000000000000015d1220f20000000000b700000000000000000000000000000000000000000000007c000000000000000000000000000000000041000000000000000006000000000000000
def minorLeaf13 (i : Nat) : Nat := 0x1e61d8150c804e601d950c808e61d8150c80661d8150c8040009200000062000000320006000000
def projectionTable : Nat → Nat × Nat × (Nat → Nat)
  | 5 => (1,0,minorLeaf5)
  | 6 => (2,0,minorLeaf6)
  | 7 => (2,0,minorLeaf7)
  | 8 => (7,0,minorLeaf8)
  | 9 => (65,0,minorLeaf9)
  | 10 => (491,0,minorLeaf10)
  | 11 => (1662,11,minorLeaf11)
  | 12 => (282,12,minorLeaf12)
  | 13 => (15,8,minorLeaf13)
  | _ => (0,0,fun _ => 0)
def tight5 (i : Nat) : Nat := 0x423b64b
def tight6 (i : Nat) : Nat := 0x423b64b
def tight7 (i : Nat) : Nat := 0x434b64b00000000
def tight8 (i : Nat) : Nat := 0x146b53c0745b64b0445b64b0000000016074b6816014b6816014b68
def tight9 (i : Nat) : Nat := 0x7009b92a0157b53c00000000026868a30456b6370157b53c0756b64b00000000000000007003b92a00000000000000000000000002576aa3000000009224b458000000006a047b0b0956b848136841631578b1990905ba4c1256945b136841630945ba4c13014b6313014b6313019b631301456300000000b528b19900000000000000000000000013019b6316014b68000000000000000013094b662a0168791309b4271307b4272a0168791307b4271307b42c1307b4271307b427000000002a016879b529b19913071427000000000306656600000000000000001367145713671457000000001367145768027b1b0000000021564332035665660356656603566566
def tight10 (i : Nat) : Nat := (if i < 1 then 0xb53ab199130914272a126879000000002a126879000000002a1268792a126879000000002a1268790000000000000000000000002a126879a057b76c7016b92a7016b92a0000000000000000000000007316792a8227a62b2a1268797016b92a000000000000000000000000000000000308656603086566000000000000000003086566000000009846b4b813084166130841661308416613084166130841660000000000000000130841661308416613084166000000001308416613084166130841661308416600000000000000000000000013084166000000002589360a000000002a016879000000000978ba422a016879000000002a0a68791389b457b53ab1995967484c000000001389b45703786566037865660378656603786566037865660378656603786566000000000378ab660378ab660378ab66000000000378656603786566037865660378656603786566037865660000000003015a5768047b1b00000000000000000309a5662a1a68792a1a86882a01687900000000030865660000000059034a4c000000002a1786880000000000000000000000000408b8570908b8480408b85755033a0a2116591403075a530968b8480468b8572a17868827188535271885352a1786882718853500000000030885660308856603088566030885660000000003088566030885660308856603088566030885660308856603088566000000002a19868800000000000000002a1786882a1786882a17868800000000000000002a178688000000002a17868868034b1b216845322168453268034b1b55286398516843322168453221684532216845322168453221684532216845322168453221684532216845322168453221684532216845322168453221684532000000002168453200000000216845320000000021684532000000002168453221684532216845320000000021684532216845322118853621188536000000002118853600000000211885362a1786884028ab360000000000000000000000002a0786882a07868800000000000000002a07868800000000000000002a0786882a078688000000002a0786882a0786882a0786882a0786885528639800000000000000000000000000000000000000006839b4a2037865660378656603786566000000000000000000000000000000002a7968792a79687900000000000000002a79687900000000000000002a79687900000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 else 0x3015a5700000000000000000301ba570000000003015a570301ba57000000000000000000000000000000001a019b08000000001a019b082a126879000000001a019b085538a399000000005538a3997015b92a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000301ba57000000000000000000000000000000002a23697903015a572a2368792a2368792a2369792a2368791317b427000000006a057b0b0967b8480308a566211268142a1268790707ab652a1268790708a56b0706ab642a1268795548a3912a1268791307b4272a1a68796a057b0b6847b4a82a1268792a1268790707ab652a1268792a1a68790708a5682a1268792a1a68792a1a8688000000000401b6570000000000000000030156570000000003015a5700000000000000001618b9711a17b9710907ba421618b9711a17b9712a12687909075a420967ba421318b4271318b427131ab4271318b4271a17b971030856571318b4271318b42c1318b42713185427000000001318b4270000000000000000000000003223b6251a17b971030856570907ba421a17b97109075a420967ba4213181427b5591b8a0907ba4c13181427000000001318142709075a4c1278945b00000000138a41630967ba4c000000000000000013014b6313014b630000000013014b6313014b63000000000000000013014b632a1268797315792a130145632a126879000000007015b92a000000007015b92a13014b630000000013014b6313019b631301456300000000000000000309856603098566030985668227a62b030925665778424aa057b76c00000000826a6aa30000000013094b6613094b665779434813094166130945668216a62b5179434213094b66000000000000000013094b6613094b6600000000000000002a1986880000000013094b66577943480000000013094b6613094b66130941660000000013094b66000000001309456613094b6600000000000000000000000013094b6613094b6613094b6613094b6600000000517940422a1986880000000051794342000000000000000013019b630000000000000000130a4b662a01687900000000130ab4271309b4272a0168791309b4271309b42c1309b427000000001309b42700000000b536b199000000002a016879)
def tight11 (i : Nat) : Nat := (if i < 3 then (if i < 1 then 0x212358140000000021235814000000002123581421235814212358140000000000000000212358142123581421235814000000002b2358793a34b6854004ba54000000003234b6252123081400000000000000000000000000000000212358142123581455043a0a0000000055043a0a55043a0a0000000055043a0a0000000055043a0a0000000055043a0a000000005504380a0000000055043a0a00000000685ab4a28227a62b55043a0a55043a0a000000000000000055043a0a55043a0a685ab4a255043a0a55043a0a55043a0a5504360a000000000000000055040a0a685ab4a2000000008227a62b685ab4a20000000009088b150000000009088b150000000068054b1b09088b1500000000554aa39109088b150000000009088b1509088b1500000000554aa39109088b1509088b1509088b1500000000554aa39109088b1509088b1509088b1509088b150000000009088b15554aa3910000000009088b1509088b1509088b1509088b150000000009088b1509088b150000000009088b150000000009088b1509088b1509088b1509088b1509088b150000000009088b1509088b1509088b1509088b15000000000000000009088b15554aa39109088b1509088b150000000009088b1509088b1509088b1509088b15554aa39109088b1500000000554aa391000000007016b92a554aa391554aa39100000000000000000000000000000000554aa391554aa39100000000554aa391554aa39100000000554aa39168054b1b5948a4b5554aa3918227a62b00000000554aa39100000000554aa391554aa39168054b1b00000000554aa391554a639100000000000000000000000000000000000000000000000000000000554aa39100000000554aa3918227a62b00000000000000000000000068154b1b000000002a298688000000002a2986880000000068154b1b000000002a2986882a29868868154b1b00000000000000002a29868868154b1b2a29868868154b1b706a9b9368154b1b00000000000000002a29868800000000706a9b93000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 else (if i < 2 then 0x2a12687900000000000000000000000000000000000000001a129b08000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000401b85700000000000000000401b8570901b8420000000000000000000000000901b8420901b842000000000901b842000000000901b842040118570000000004011857000000000401185755053a0a00000000000000000000000068164b1b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000401585704015857040158570401585704015857000000000401585704015857040158570401585704015857000000003234762504010857323476250301585700000000000000000301585700000000030158570301585703015857030158570301585700000000000000000301585703015857030158570000000003015857030158570301585703015857030158570000000003015857030158570301585703015857030158570000000003015857030158570301585700000000030158570301585703015857030158570301585703015857030158575505380a5505380a13124b635505380a5505380a5505380a03015857000000000000000013129b6313129b6313129b63030108570000000068164b1b040158570000000000000000000000000401585700000000040158570401585704015857000000000401585704015857040158570000000004015857040158570000000004015857040158570401585700000000040158570000000000000000040158570401585704015857040158570401585700000000040158570000000004015857040158570401585704015857040158570401585704015857040158570401585704015857040158572123581421235814212358142123581440044a5404015857000000002123581421235814212358140401185755053a0a323446252123581455053a0a00000000000000000401b85703015a5700000000000000000401b85755053a0a16129b6804088b665505380a000000000000000055053a0a000000000401b8570000000068164b1b1a129b080901b84255053a0a16129b68681a4b1b8237a62b03015857040158570401b8575505360a03015857212859146816411b8237a62b6816411b7026b92a04088b660000000000000000000000000000000055043a0a0000000055043a0a0000000055043a0a5504380a0000000055043a0a000000000000000068154b1b55043a0a55043a0a7026b92a0000000055043a0a55043a0a7026b92a000000000000000000000000000000002123581400000000 else 0x2a2a6879000000002a2a687900000000000000002a2a68790000000081786bb4000000000000000000000000000000000000000000000000000000000000000013014b630000000013014b6300000000000000000000000013014b63000000000000000013014b6300000000000000000000000013014b632a1268797316792a130145632a12687900000000000000007016b92a000000007016b92a0000000000000000000000000000000000000000000000002a1268792a1268792a126879000000002a126879000000002a1268792a1268790000000000000000000000002a1268792a126879a057b76c0000000000000000000000002a126879a057b76cb547b499a057b76c00000000000000008227a62b00000000000000008227a62b8227a62b0000000000000000000000008227862b000000002a1268790000000000000000a057b76c000000000000000000000000131ab427000000000000000000000000131ab42700000000131ab427131ab42700000000131ab42700000000131ab42700000000131ab427131ab427131ab427131ab42700000000131ab427000000001a19b871131ab4271619b8777316792a131a54270000000000000000000000000000000017129b6817129b680000000017129b6817129b6817129b6855053a0a2a236979000000000000000017129b680000000017129b680000000027236874272368740000000017129b680000000017129b680000000017129b6817129b6817129b6817129b6817129b682128641417129b6817129b685504360a21283414000000002128641421286414212864140000000000000000000000000000000055053a0a17129b6855053a0a55053a0a17129b6855054a0a000000005504360a55043a0a69157b1b55053a0a0000000000000000000000002123681400000000212368140000000055053a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002a2a6879000000002a2a68790000000055043a0a81786bb4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000017019b6817019b680000000017019b6817019b680000000000000000554aa39117019b68554aa39169057b1b2a1268790000000000000000000000000000000000000000000000002a1268792a1268792a1268792a1268792a12687900000000000000000000000000000000)) else (if i < 5 then (if i < 4 then 0x13124b631312456313014b630301565713124b63000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003015657000000005505360a5505360a0000000013124b63a068b76c5505060a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000013124b630000000013124b630000000013124b6313124b6303015a5713124b6313124b6313124b630000000013124b6313124b6303015a5713124b63000000000000000000000000000000001312456313124563000000000000000013124563131245630000000013124563131245631312456300000000131245631312456313124563131245630000000013124b63000000003234b625000000003234b625000000003234b625000000000000000003015a570000000013124b6300000000000000000000000013124b633234b62513124b6303015a577326792a000000007326742a7326792a272369747326792a13124563000000007326792a272869743234962503015a577316792a00000000212368140000000021236814000000000000000021236814000000002a2368793a34b685000000003234b6254004ba540000000000000000000000001a128b08000000002a2369792a2368792a23687927236874212369142a2368795505360a212869141a19b871000000002a1268792a1268797016b92a1a128b082a1268791a19b8712a1268791a19b97100000000131ab427131ab42700000000131ab42700000000131ab427000000001a19b971131ab427131ab42700000000131ab427131ab42700000000131ab42700000000131ab42700000000131ab427131ab427131ab427131ab4271a19b971131ab427131ab4270000000000000000131ab427131ab427131ab4271a19b971131ab427000000000000000000000000131ab427131ab427000000001a19b9712a126879131ab4272a126879131a54271a19b9711a19b971000000001a19b971131a1427000000001a19b971131ab427131ab42700000000131ab427000000000000000000000000131ab42700000000131ab42700000000131ab42700000000131ab4270000000000000000131ab4270000000000000000131ab427131ab42700000000131ab427131ab42700000000131ab427000000006a59b7a1000000008227a62b131a542700000000000000002a2368794004ba54a068b76c030156574004ba5440044a542a2a6879a057b76c7026b92a13124b6340049a547026692a7016b92aa057b76c7016b92a030156577016b92a000000007026b92a else 0x55050a0a16128568000000001a128b0855050a0a0000000055050a0a00000000000000000000000000000000000000000000000016129b682a23687913124b632a2368796a167b0b16129b68000000000000000000000000000000002a1268790000000000000000000000002a12687900000000000000000000000000000000000000002a126879554aa391000000002a126879554aa391554a639100000000000000002a126879554aa391554aa3912a12687900000000554aa39100000000000000000000000000000000000000002a23687900000000000000002a236879b257b45b6a167b0b00000000000000008237a62b6a167b0b000000002a236879a067b76c000000008237a62b000000000000000000000000000000000000000000000000000000002a1268792a1268790000000000000000000000002a12687900000000000000002a126879000000002a126879554aa391554a6391000000000000000000000000000000000000000000000000000000000000000000000000000000000301b657000000000301b6570301b657000000000301b6570301b65700000000000000000000000000000000000000000000000000000000000000000301565700000000000000000301565700000000000000000301565703015657000000000000000000000000030156570000000003015657000000000301565700000000000000000301565703015657000000000000000003015657030156570301565703015657030156570301565700000000000000000000000000000000030156570000000000000000030156570000000003015657030156570000000003015657030156570301565700000000000000000301565703015657030156570000000003015657030156570301565700000000000000000301565700000000030156570301565703015657000000007326792a000000008237a62b03010657000000008237a62b000000000000000013124b63000000000000000013124b630000000013124b6313124b6313124b6300000000000000000000000016124b6813124163131245630000000000000000000000000000000000000000000000000000000000000000030a656600000000030a65660000000000000000030a656600000000030a6566030a6566030a65660000000000000000000000000000000000000000000000003234b625000000003234b625000000003234b6253234b62500000000000000000000000000000000000000000000000013124b6313124b6327236874131245630000000000000000000000000000000000000000000000000000000013124b6313124b63000000000000000013124b632a2368790000000013124b63000000000301565713124b6313124b63) else (if i < 6 then 0x7027b92a00000000000000007027b92a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000055053a0a0000000000000000000000000000000000000000000000000000000016129b6800000000000000000000000016129b6816129b6816129b681612956816128b6817129b6816128b6800000000000000002a2369792a2369790000000000000000000000002a2369792a2369793a34b6852a2369792a23697955053a0a323496254004ba542a2368792a2368792a236879000000002a2368792a23687955053a0a2a2368792a2368792a236879000000002a23687907015a4707015a4707015a4700000000000000002a236879000000002a2368792a236879000000002a2368792a2368792a236879000000002a236879000000000000000055053a0a55053a0a2a236879000000002a23687900000000000000002123681400000000000000002123681400000000000000000000000021236814212368142a23687900000000323446253234462540044a540000000000000000000000000701ba47212869148238a62b2a2369798237a62b0708ab650000000000000000000000002a236879000000000000000000000000000000002a2368790000000000000000000000002a2368792a2368790000000055043a0a6a157b0b00000000000000000000000000000000000000000000000000000000000000000000000055053a0ab258b45b03010a576a167b0b55050a0a00000000000000002a2368794004ba5455053a0a3234462555043a0a000000002a2a687916129b6832344625b257b45b000000004004ba545505360a5505360a03015a5707015a475505360a000000002a2a68795504360a5505380a16129b6840049a545504360a5504360a0000000000000000000000002128641421286414000000002128641421286414000000002128641400000000000000002128641421286414212864140000000021236814000000000000000000000000000000000000000021236814000000002a2368794004ba54000000004004ba54000000001a128b082a2369792a236879212369142a2368792a23687955053a0a212869141a129b082a12687955043a0a55043a0a2a1268790000000055043a0a2a2a687900000000000000000000000000000000000000000000000016128b6800000000000000000000000016128b6800000000000000000000000016128b6816128b6816128b68 else 0x3015a5700000000000000000000000000000000000000000301ba570301ba570301ba5700000000000000000301ba570301ba5713128b6303011a572a2368790000000003015a57000000000301565755053a0a000000000000000000000000030aa566030aa56600000000030aa5660000000000000000030aa566030aa5660000000000000000030aa56600000000030a6566000000000000000000000000000000000301ba57000000000301ba57000000000000000000000000030aa5660000000000000000000000000000000000000000000000000000000003015a570000000000000000000000000000000055053a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001a129b08000000000000000000000000000000001a129b081a129b08000000001a129b08000000001a129b08000000001a129b081a129b082a2368791a12950800000000000000001a129b081a128b080000000003015a57000000000901ba42000000000908ab1500000000000000000000000016129b6816129b6816129b682a23687916129b680000000055050a0a55050a0a000000001a129b08000000001a129b08000000001a129b081a129b081a129b081a129b081a129b082a2368790000000000000000)))
def tight12 (i : Nat) : Nat := (if i < 1 then 0x0 else 0x0)
def tight13 (i : Nat) : Nat := 0x0
def tightTable : Nat → Nat → Nat
  | 5 => tight5
  | 6 => tight6
  | 7 => tight7
  | 8 => tight8
  | 9 => tight9
  | 10 => tight10
  | 11 => tight11
  | 12 => tight12
  | 13 => tight13
  | _ => fun _ => 0
def positiveRow (j : Nat) : Row := ([3,6,12,24,17,33,66,132,264,160,320,288] : List Row).getD j 0
def negativeRow (j : Nat) : Row := ([42,50,69,104,116,138,201,208,261,276,385,402] : List Row).getD j 0

def tightAt (k i : Nat) := packedAt (tightTable k) (32*i) 32

def checkedTight (T : Sig) (k : Nat) (ws : List Sig) (w : Nat) :=
  let field := fun j => (w >>> (4*j)) &&& 15
  tightTest T k ws (positiveRow (field 7)) (negativeRow (field 6))
    (negativeRow (field 3)) (negativeRow (field 2)) (positiveRow (field 1)) (positiveRow (field 0))
    (ws.getD (field 5) zero) (ws.getD (field 4) zero)
def sameColor (c : Sig → Bool) (P N : Sig → Prop) : Prop :=
  ∀ x y, P x → N x → P y → N y → c x=c y → x=y

def owner (a b z x : Sig) := if x=a ∨ x=b then z else x

theorem ordinaryColor {P N : Sig → Prop} {a b d p n} {U : Finset Sig} (c : Sig → Bool)
    (old : sameColor c P N)
    (pm : ∀ w, P w → w ∈ insert (bin d a b) U) (nm : ∀ w, N w → w ∈ insert (bin d a b) U)
    (x y : Sig)
    (rx : x∈U → x≠a ∧ x≠b) (ry : y∈U → y≠a ∧ y≠b)
    (px : expandCert P (bin d a b) (childCert d true p a b) x)
    (nx : expandCert N (bin d a b) (childCert d false n a b) x)
    (py : expandCert P (bin d a b) (childCert d true p a b) y)
    (ny : expandCert N (bin d a b) (childCert d false n a b) y)
    (eq : c (owner a b (bin d a b) x)=c (owner a b (bin d a b) y)) : x=y := by
  let z := bin d a b
  have classify (w) (reg : w∈U → w≠a ∧ w≠b)
      (pp : expandCert P z (childCert d true p a b) w) (nn : expandCert N z (childCert d false n a b) w) :
      (P w ∧ N w ∧ w≠z ∧ owner a b z w=w) ∨
        (P z ∧ N z ∧ childCert d true p a b w ∧ childCert d false n a b w ∧ owner a b z w=z) := by
    rcases pp with ⟨h,ne⟩ | ⟨h,pr⟩ <;> rcases nn with ⟨j,nej⟩ | ⟨j,nr⟩
    · have both := reg ((Finset.mem_insert.mp (pm _ h)).resolve_left ne)
      exact Or.inl ⟨h,j,ne,by simp [owner,both.1,both.2]⟩
    · have both := reg ((Finset.mem_insert.mp (pm _ h)).resolve_left ne)
      rcases child_in nr with eq | eq <;> simp_all
    · have both := reg ((Finset.mem_insert.mp (nm _ j)).resolve_left nej)
      rcases child_in pr with eq | eq <;> simp_all
    · exact Or.inr ⟨h,j,pr,nr,by simp [owner,child_in pr]⟩
  change c (owner a b z x)=c (owner a b z y) at eq
  rcases classify x rx px nx with ⟨xp,xn,xz,ox⟩ | ⟨pz,nz,dx,cx,ox⟩ <;>
    rcases classify y ry py ny with ⟨yp,yn,yz,oy⟩ | ⟨qz,mz,dy,cy,oy⟩ <;> rw [ox,oy] at eq
  · exact old _ _ xp xn yp yn eq
  · exact False.elim (xz (old _ _ xp xn qz mz eq))
  · exact False.elim (yz (old _ _ yp yn pz nz eq.symm))
  · exact child_inter _ _ _ _ _ _ _ dx cx dy cy

def dependsOn (S : Finset Sig) (paint : Sig → Bool) (v : Sig) : Prop :=
  ∀ p n : Row, bit p v=true → bit n v=false →
    ∃ x ∈ S, paint x=true ∧ bit p x=true ∧ bit n x=false

def markFor (paint : Sig → Bool) (v : Sig) (p n : Row) (P N : Sig → Prop) : Prop :=
  ∀ x, P x → N x → paint x=true → bit p v=true ∧ bit n v=false

def markedPalette (S : Finset Sig) (T : Sig) := ∃ paint v, dependsOn S paint v ∧ ∀ p n : Row,
  bit p T=true → bit n T=false → ∃ P N, SampleCert S p T true P ∧ SampleCert S n T false N ∧
    sameColor paint P N ∧ markFor paint v p n P N

theorem marked_expand {S : Finset Sig} {a b d p n P N v}
    (paint : Sig → Bool) (old : markFor paint v p n P N)
    (pc : ∀ w, P w → w ∈ insert (bin d a b) S) (nc : ∀ w, N w → w ∈ insert (bin d a b) S)
    (aout : a∉S) (bout : b∉S) :
    markFor (fun w => paint (owner a b (bin d a b) w)) v p n
      (expandCert P (bin d a b) (childCert d true p a b))
      (expandCert N (bin d a b) (childCert d false n a b)) := by
  intro w yes no col
  rcases yes with ⟨h,ne⟩ | ⟨h,pr⟩ <;> rcases no with ⟨j,nej⟩ | ⟨j,nr⟩
  · have mem := (Finset.mem_insert.mp (pc _ h)).resolve_left ne
    have ab : ¬(w=a ∨ w=b) := by grind
    exact old _ h j (by simpa [owner,ab] using col)
  · have mem := (Finset.mem_insert.mp (pc _ h)).resolve_left ne
    rcases child_in nr with rfl | rfl <;> contradiction
  · have mem := (Finset.mem_insert.mp (nc _ j)).resolve_left nej
    rcases child_in pr with rfl | rfl <;> contradiction
  · exact old _ h j (by simpa [owner,child_in pr] using col)

theorem depends_expand {S : Finset Sig} {a b d v} {paint : Sig → Bool}
    (old : dependsOn (insert (bin d a b) S) paint v) (aout : a∉S) (bout : b∉S) :
    dependsOn (insert a (insert b S)) (fun w => paint (owner a b (bin d a b) w)) v := by
  intro p n vp vn
  obtain ⟨w,mem,col,up,down⟩ := old _ _ vp vn
  rcases Finset.mem_insert.mp mem with eq | mid
  · subst w
    have one : (bit p a=true ∧ bit n a=false) ∨ (bit p b=true ∧ bit n b=false) := by
      cases d <;> cases ha : bit p a <;> cases hb : bit p b <;>
        cases ja : bit n a <;> cases jb : bit n b <;> simp_all [bit_bin]
    rcases one with yes | yes
    · exact ⟨a,by simp,by simpa [owner] using col,yes⟩
    · exact ⟨b,by simp,by simpa [owner] using col,yes⟩
  · have ab : ¬(w=a ∨ w=b) := by grind
    exact ⟨w,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem mid),by simpa [owner,ab] using col,up,down⟩
theorem marked_palette {T k t S} (run : Live T k t S) (mono : t=0) (capacity : k≤S.card) : markedPalette S T := by
  classical
  induction run using Live.ind with
  | stop properT =>
    refine ⟨fun _ => false,zero,?_,?_⟩
    · intro p n h; rw [bit_zero] at h; contradiction
    intro p n hp hn
    obtain ⟨P,N,pp,nn,th⟩ := tight_certs (Live.stop properT) rfl (by simp) p n hp hn
    exact ⟨P,N,pp,nn,fun x y a b c d _ => th x y a b c d,by intro x _ _ no; contradiction⟩
  | unary _ _ _ _ => omega
  | @binary k t U a b d ha hb hab fresh tail ih =>
    let z := bin d a b
    have hz : z ∉ U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have size := (live_size tail).2
    have sz : (insert z U).card=U.card+1 := Finset.card_insert_of_notMem hz
    change (insert z U).card+t≤k+1 at size
    have hsmall : k ≤ (insert z U).card := by
      have x := Finset.card_insert_le a (insert b U)
      have y := Finset.card_insert_le b U
      omega
    by_cases exist : a∈U ∨ b∈U
    · have strict : (insert z U).card=k+1 := by
        rcases exist with e | e
        · have ha' : a∈ insert b U := Finset.mem_insert_of_mem e
          rw [Finset.insert_eq_of_mem ha'] at capacity
          have qb := Finset.card_insert_le b U
          omega
        · rw [Finset.insert_eq_of_mem e] at capacity
          have qa := Finset.card_insert_le a U
          omega
      have notBoth : ¬(a∈U ∧ b∈U) := by
        rintro ⟨e,f⟩
        rw [Finset.insert_eq_of_mem f,Finset.insert_eq_of_mem e] at capacity
        omega
      let shared := if a∈U then a else b
      have onlyShared (v : Sig) (hv : v∈U) (dif : v≠shared) : v≠a ∧ v≠b := by
        by_cases e : a∈U
        · have nb : b∉U := fun q => notBoth ⟨e,q⟩
          exact ⟨by simpa [shared,e] using dif,fun eq => nb (eq ▸ hv)⟩
        · exact ⟨fun eq => e (eq ▸ hv),by simpa [shared,e] using dif⟩
      refine ⟨fun w => decide (w=shared),shared,?_,?_⟩
      · intro p n hp hn
        have mem : shared ∈ insert a (insert b U) := by by_cases h : a∈U <;> simp [shared,h]
        exact ⟨shared,mem,by simp,hp,hn⟩
      intro p n hp hn
      obtain ⟨P,N,pc,nc,th⟩ := tight_certs tail mono strict p n hp hn
      refine ⟨_,_,expand_ok pc,expand_ok nc,?_,?_⟩
      swap
      · intro w yes no marked
        have eq : w=shared := of_decide_eq_true marked
        exact ⟨eq ▸ (expand_ok pc).holds w yes,eq ▸ (expand_ok nc).holds w no⟩
      intro x y px nx py ny eq
      by_cases e : x=shared
      · have fy : y=shared := by simpa [e] using eq.symm
        exact e.trans fy.symm
      · have f : y≠shared := by simpa [e] using eq.symm
        exact ordinaryColor (fun _ => false) (fun u v a b c d _ => th u v a b c d)
          pc.belongs nc.belongs _ _ (fun h => onlyShared _ h e) (fun h => onlyShared _ h f) px nx py ny rfl
    · obtain ⟨paint,v,dep,works⟩ := ih mono hsmall
      have aout : a∉U := fun hx => exist (Or.inl hx)
      have bout : b∉U := fun hx => exist (Or.inr hx)
      refine ⟨fun w => paint (owner a b z w),v,depends_expand dep aout bout,?_⟩
      intro p n hp hn
      obtain ⟨P,N,pc,nc,th,marked⟩ := works p n hp hn
      refine ⟨_,_,expand_ok pc,expand_ok nc,?_,marked_expand paint marked pc.belongs nc.belongs aout bout⟩
      intro x y px nx py ny eq
      have good (w) (hw : w∈U) : w≠a ∧ w≠b := by grind
      exact ordinaryColor paint th pc.belongs nc.belongs _ _ (good _) (good _) px nx py ny eq
def leftWire (ws : List Sig) (w : Nat) := ws.getD ((w >>> 20) &&& 15) zero
def rightWire (ws : List Sig) (w : Nat) := ws.getD ((w >>> 16) &&& 15) zero

def checkedPair (T : Sig) (ws : List Sig) (w : Nat) :=
  let t := fun j => (w >>> (4*j)) &&& 15
  let a := leftWire ws w
  let b := rightWire ws w
  let p := positiveRow (t 7)
  let n := negativeRow (t 6)
  (a != b) && oneDifference T ws p (negativeRow (t 3)) a &&
    oneDifference T ws p (negativeRow (t 2)) b &&
    oneDifference T ws (positiveRow (t 1)) n a && oneDifference T ws (positiveRow (t 0)) n b

theorem checkedPair_diff {T w c} {ws : List Sig}
    (works : ∀ p n : Row, bit p T=true → bit n T=false → ∃ P N,
      SampleCert ws.toFinset p T true P ∧ SampleCert ws.toFinset n T false N ∧ sameColor c P N)
    (h : checkedPair T ws w = true) : c (leftWire ws w) ≠ c (rightWire ws w) := by
  simp only [checkedPair,Bool.and_eq_true,bne_iff_ne] at h
  obtain ⟨⟨⟨⟨ne,pa⟩,pb⟩,na⟩,nb⟩ := h
  obtain ⟨P,N,yes,no,valid⟩ := works _ _ (oneDifference_pos pa) (oneDifference_neg na)
  intro eq
  exact ne (valid _ _ (force_pos yes pa) (force_neg no na) (force_pos yes pb) (force_neg no nb) eq)

def posKey (w : Nat) := positiveRow ((w >>> 28) &&& 15)
def negKey (w : Nat) := negativeRow ((w >>> 24) &&& 15)

theorem pairMarked {T w paint shared} {ws : List Sig}
    (works : ∀ p n : Row, bit p T=true → bit n T=false → ∃ P N,
      SampleCert ws.toFinset p T true P ∧ SampleCert ws.toFinset n T false N ∧
      sameColor paint P N ∧ markFor paint shared p n P N)
    (h : checkedPair T ws w = true) :
    bit (posKey w) shared=true ∧ bit (negKey w) shared=false := by
  simp only [checkedPair,Bool.and_eq_true,bne_iff_ne] at h
  obtain ⟨⟨⟨⟨ne,pa⟩,pb⟩,na⟩,nb⟩ := h
  obtain ⟨P,N,yes,no,valid,marked⟩ := works _ _ (oneDifference_pos pa) (oneDifference_neg na)
  have x := force_pos yes pa
  have y := force_neg no na
  have u := force_pos yes pb
  have v := force_neg no nb
  by_cases pc : paint (leftWire ws w)=true
  · exact marked _ x y pc
  · have diff : paint (leftWire ws w)≠paint (rightWire ws w) := fun h => ne (valid _ _ x y u v h)
    have yes' : paint (rightWire ws w)=true := by cases x : paint (leftWire ws w) <;> cases y : paint (rightWire ws w) <;> simp_all
    exact marked _ u v yes'

def forcedMark (T : Sig) (ws : List Sig) (a : Sig) (e f : Nat) :=
  checkedPair T ws e && checkedPair T ws f && oneDifference T ws (posKey e) (negKey f) a

theorem forcedMark_ok {T e f paint shared a} {ws : List Sig}
    (deps : dependsOn ws.toFinset paint shared)
    (marks : ∀ w, checkedPair T ws w=true → bit (posKey w) shared=true ∧ bit (negKey w) shared=false)
    (h : forcedMark T ws a e f=true) : paint a=true := by
  simp only [forcedMark,Bool.and_eq_true] at h
  obtain ⟨x,hx,px,up,down⟩ := deps _ _ (marks e h.1.1).1 (marks f h.1.2).2
  have o := h.2
  simp only [oneDifference,Bool.and_eq_true,List.all_eq_true,Bool.or_eq_true,Bool.not_eq_true',beq_iff_eq] at o
  have ans := o.2 x (List.mem_toFinset.mp hx)
  rcases ans with (eq | no) | no
  · exact eq ▸ px
  · simp [up] at no
  · simp [down] at no

def coneTest (T : Sig) (k : Nat) (ws : List Sig) (steps : List Nat) :=
  let e := steps.getD 4 0
  decide (k≤ws.toFinset.card) && checkedPair T ws e &&
    forcedMark T ws (leftWire ws e) (steps.getD 0 0) (steps.getD 1 0) &&
    forcedMark T ws (rightWire ws e) (steps.getD 2 0) (steps.getD 3 0)

theorem coneTest_sound {T k ws codes} (h : coneTest T k ws codes = true) : ImpossibleM T k ws.toFinset := by
  intro t j small mono run
  simp only [coneTest,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨paint,v,deps,wsat⟩ := marked_palette run mono (small.trans h.1.1.1)
  have plain : ∀ p n : Row, bit p T=true → bit n T=false → ∃ P N,
      SampleCert ws.toFinset p T true P ∧ SampleCert ws.toFinset n T false N ∧ sameColor paint P N := by
    intro p n hp hn
    obtain ⟨P,N,pp,nn,color,_⟩ := wsat _ _ hp hn
    exact ⟨P,N,pp,nn,color⟩
  have v1 := forcedMark_ok deps (fun _ => pairMarked wsat) h.1.2
  have v2 := forcedMark_ok deps (fun _ => pairMarked wsat) h.2
  exact (checkedPair_diff plain h.1.1.2) (v1.trans v2.symm)
def cone9 (i : Nat) : Nat := 0x2a0768782a0768788947ba41b526b1987308b92957303b92984565a529913b4b7b515b1987303b92957302b9297302b9299912b4b7b515b1987302b92957303b92984565a529913b4b7b515b1987303b92957303a92984565a529913b4b7b515b1987303a92959924b4b78456b6369924b4b78756b6369924b4b7513064165a024b76b5957484b84456bb513064165513064165a024b76b5957484b84456bb5130641655b514b19881455bb4b514b1985b564387b514b19857303b9298958ba417303b929b514b1987303b929513084165a024b76b5b56468b84456bb513084165504056b655b56468b8957ba4b84456bb516064b69513054165a013b76b5b46468b84346bb513054165581345bb35b47468b8948ba4b81345bb3ba78b978513064165a024b76b5b57468b84456bb513064165500000008fc0000000000000000000008587b471000066c0005c80000000000000000000000000000000000005240000004803dc0000000000000000000000000000000000000003380000000002940001f014c0000000a8000000004000000000000
def cone10 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0xb3227696f42496ed73227696f3227696f6e296934b3227696f42496ed73227696f3227696f6e296934b3227696f42496ed73227696f3227696f6e296934b3227696f42496ed73227696f3227696f6e296934b3227696f42496ed73227696f3227696f6e296934a1c3100007020def8000376c00000000000371a6d90d9d8000362400000001ae900000000d60000000006a5cd371a45343867ccce50000334265e0ca79926000063f4c6a18ab31040000c2c9830300e5f7800017b52f185d8cb9d17112dd05afcb4b166d00005910b0d95f22b920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ad000002aee5538000152500000000a7e00000000000000000000000000000000000000000000000000000000000000000000534c00014aa290251600000000000000000000000000000000000000000000000000000000000000000000285e5018000000027ba000000013b4271600000000000000000009b100002672000000000000000000000000002620000000000000000000000000000000000097380000000000000000000000000000012be00000000000129524d800009218000000048680000000000047c400011c8000000008cf91760000000000000000000453400000002248000087d80000000000000000000000434800000000000000000000000000000085480002100000000000000000415c000102e0000000080280001fb83ecc7c50000000000000000f611e703c3c0000000000000007730ebd1d2839ac00000001c8438640000df0000000000000000000000006e38d9e000000000000d750000000000000001a98348c000000019f400006688000195000000000c7f000000000000000000000000000000000000000000000000031580000000000030b4000000000000000000000018080000000000017b60000000000000002ec80000b8900002d800000b3700002c380000000000000000000000000000000000000000000000000ae5000000000000000157800000000000000000000000000152600005350a41000000000000a1813de00004e30000000000000000000000000000000000000000000000000000000000000000000000000000000133a00004ba00001296000049100000000000047c80000000000000008d00000229c0000000000021f842a882c0000000040187da00001ec43c4000000001d7c00000000000000000007360e1a1b9035d86920000000000000000cd2190030b85ee000000002e2859c000015cc2a500000a4213e026784a608fa1150215840207b20ec01c3835e066a0c3017182ba052209a011f821603da07100cd81720292048007b80ce014a01f0029800000540004 else 0x656353249696f4a6b6ed1644b68b4d0065634a74036d096c4b69348a2f566ed46d6d4f040b6c54a74036d09040b6c548a2f566ed46d674f040b6c54b040b6c55426b6ed76e4b69353049696f040b6c54b04094c5542696ed76e4969353051696f04094c54ab64f476f4a696ed0540d0d0ed46d6f4eb64f476eb04094c54e6f168b36e4969353051696304094c54b040b4c55426b6ed76a4b6930d4736f4f040b4c54b04094c5542496ed76e296934d44d6f4f04094c54b4a496ed10492d5454a496ed0d44d6f4f4a496ed0b6e29693542496ed76e296934d44d6f4f6e296934b020b6c77426b6ed76e4b6934b64f476f020b6c76b6e4b6935426b6ed76e4b6934d46f6f4f6e4b6934a8a2f566f6a4b6930e68d152d6c4b69348a2f566eb3227696f40496cd73227696f3227696f6c296734b6e29693542496ed76e29693512b174836e296934b3227696ee66d352d3227696f3227696f6e296934b4a496ed0e66d352d4a496ed0d44d6d4f4a496ed0b6c4b6935426b6ed76c4b6934b64cc9716c4b6934b3249696f426b6ed73249696f3249696f6a4b6930ad20696353249696f4a6b6ed108acd76ad2069634b3227696f42496ed73227696f3227696f6e296934b3227696f028ab7673227696f3227696f6a296330b6e29693542496ed76e296934d44d6d4f6e296934b6a29693142496ed76a296930b6ae870f6a296930b3227696f42496ed73227696f3227696f6e296934b3227696f42496ed73227696f3227696f6e296934b3227696f42496ed73227696f3227696f6e296934b3227696f42496ed73227696f3227696f6e296934b3227696f42496ed73227696f3227696f6e296934b3227696f42496ed73227696f3227696f6e296934b3227696f42496ed73227696f3227696f6e296934b3227696f42496ed73227696f3227696f6e296934b3227696f42496ed73227696f3227696f6e296934b3227696f088ad76b3227696f3227696f6e296934b3227696f42496ed73227696f3227696f6e296934b3227696f40494ed73227696f3227696f6e296934b242768af088ad76b242768af12b174836e296934b6c29693542496ed76c296934b62ac9716c296934b3227696f42496ed73227696f3227696f6e296934b3227496f42496ed73227496f3227496f6c294934b3227696f42496ed73227696f3227696f6e296934b3227696f42496ed73227696f3227696f6a296930b3227696f42496ed73227696f3227696f6e296934b3027496f42496ed73027496f3027496f6c294934b3227696f42496ed73227696f3227696f6e296934b3227696f424968d73227696ed44d6d4f3227696eb302768af40496ed1302768af4a496ed1302768aeb6e29693542496ed76e296934d44d6d4f6e296934b2426e8af088ad76b2426e8af2426e8aeb6ae870e) else (if i < 3 then 0x9725312d37482e60972536a4b6330e6097252b6a4b6330e29337236a4b6330b6d2868f6a4b6330a3403360ed40af614e62d7252e62d7252d40af614a5424d0f1308b696f044d4c556e8d6934e62b7252a5424d0f130b296f7044d4c556ed29752e62b7252a5424d0f1306b696f044d4c556e6d6934e62b7252a5424d0f1306b696f044d4c556e6d6934e62b7252ae62b7253428d6ed7326b696f6e6d6934e62b7252ae62b725304d2d544e62b72534a8d6ed0e62b7252ae62b7253428d6ed7326b696f6e6d6934e62b7252b042d4c55428d6ed76e6d6935306b696f042d4c54ae62b7253428d6ed7326b696f6e6d6934e62b7252a5424d0f05424d0f1044f4c556e8f6934e62d7252a0612cacb408d6ed6b66ec9716c6d69340612cacaa2c0296cf6c6d6934562ec8f108ced76a2c0296cea2c0296cf6c6d6934e22b723308ced76a2c0296cea060ecacb406b6ed6b64cc9716c4b6934060ecacaa060ecacb406b6ed6b6d28d176cb29752060ecacab4a696ed142696ed76c909744b2ac90974a696ed0ad406f614d406f6154a6b6ed16eb09752d406f614b04294c5542496ed76c90974e54310d0f04294c54a260e82cb40496ed6a2ae8663088ad76a260e82caa260e82cb406b6ed6b2d290976cb09752060ecacaa260e82cb40496ed6b2ac9117088ad76a260e82cab4a496ed142496ed76c90974eb2ac90974a496ed0a5402d0f1306b696e5402d0f16a6d6330e60b7252b6a4b633102acb7676a4b6330b64cc9716a4b6330a5602d0f1306b696f042d6c556c6d69345602d0f0a5410d0f13049696f12d174836c4b69345410d0f0b642928b542496ed7642928b512b17483642928b4a3403360f6c9169345424d0f1328d696e3403360ea0610cacb408d6ed6b66ec9716c6d69340610cacab3249696f02acb7673249696f3249696f6a4b6330ad2089635326b696f4a8d6ed1646d68b4d2089634ad2069634d20696354a6b6ed104b2d544d2069634a1203748364b168b4d42cf61542d168d6b60a9496ad2089635326b696f4a8d6ed1646d68b4d2089634ad20896353273696f4a8b6ed1646b68b4d2089634ad20696353249696f4a6b6ed1644b68b4d2069634ad20696353249696f4a6b6cd1644b66b4d2069634ad20696353049676f4a6b6ed1644b68b4d2069634ad20696353249696f4a6b6ed1644b68b4d2069634ad20696353249696f4a6b6ed1082b6c56d2069634ad00656353249696f4a6b6ed1644b68b4d0065634ad2069634d20696354a6b6ed104b0d544d2069634ad2049635327096f7424968d7247096e4d2049634ad20696353249696f4a6b6ed108acd76ad2069634ad2049634d20496354a496ed10490d544d2049634ad2049635327096f74a496ed164909744d2049634ad0087635326b696f4a8d6ed1646d68b4d0087634ad else (if i < 4 then 0x25302af6a773249696f6a4f6330e6097252ae609725306cecacb3249696f6a4f6330e6097252ae209723302af6a773249696f6a4f6330e2097232ae609725306cecacb3249696f6a4f6330e6097252ae609725306cecacb3249696f6a4f6330e6097252b3249696f06cecacb3249696f3249696f6a4f6330ae609725306cecacb3249696f6a4f6330e6097252ae609525306cecacb3249696f6a4f6330e6095252ae209723306cecacb3249696f6a4f6330e2097232a5410d0f13049696f12b174836a4f63305410d0f0ae609725306cecacb3249696f6a4f6330e6097252b3249696f06cecacb3249696f3249696f6a4f6330a060374ad6e8f6734d42af61542af6ed6b6087416a080374ad6e8f6934d42af61542af6ed6b6089416a080374ad6e8f6934d42af61542af6ed6b6089416a060374ad04d2d744d428f615428d6ed6aa066c12a080374ad6e8f6934d42af61542af6ed6b6089416a060374ad6e6d6934d428f615428d6ed6b6067416ad408f615306b676f4a8d6ed16e6d6934d408f614a120374836cb16934d42cd61542d16ed6b60a9496a0e02ac8d08f0d7662e2496cf40af6ed6b6086c96a1202ac836c8f6934d22ad63540af6ed6b6086c96a0612cacb408d6ed6b66ec9716c6d69340612cacaa8a07740674476d088a077407024d6c768a077406a8a0574062c2f68ec8a057406e62b7252b6066c96aaa046c12562cc8f16a4b6330e6297252aa046c12ae609725312d17482e60972536a4b6330e6097252ae609725312d17482e60972536a4b6330e6097252a2c0316cf6c6d6934e62b72536c6d6934d008d634a2e0296cf6e6d6934e62b7253044d4c542e0296cea260296c56a4b6930e629725308acd76a260296c4a260336c56a6d6930e62b7253044d4c54d2089634a5424d0f1306b696f044d4c556e6d6934e62b7252a5402d0f05402d0f1042b4c556a4b69305402d0f0ae629725308acd76ae62972536a4b6930e6297252a5424d0f1308d696f044f4c556e8f6934e62d7252ad008f615326b696f4a8d6ed16e6d6934d008f614ad008d635306b696f4a8d6ed16c6d6934d008d634ad2089635326b696f4a8d68d0e6b1372ad2089634ad208f635306b68af4a8d6ed1246b68aed208f634b042d4c55428d6ed76e6d693454310d0f042d4c54a2e1096cf6e6d6934e6b1372b646d68b42e1096ceb4a6b6ed1426b6ed76ab29712b2ce90974a6b6ed0b042b4c54e691372b6ab2971254310d0f042b4c54a261096cb6a4b6930e691372b08acd76a261096cab6c6d6935428d6ed76c6d6934b6f0868f6c6d6934b4a6b6ed104b2d5454a6b6ed0b6d0868f4a6b6ed0b040b4c55426b6ed76a4b693054110d0f040b4c54b6a4b6931426b6ed76a4b6930b6d0870f6a4b6930ae60b725212cf7482e60b72536a736330e60b7252ae60 else 0x1202b48364b148b4d42cf61542d16ed6b20a9496a080374ad6e8f6934d42af61542af6ed6b6089416a060374ad6c8d6734d432d61542d2d76cb6087416a080374ad6c8f6934d42ad61542af6cd6b6089416a3403360f6a6f6330e62b7253326b696e3403360ea3403360f6a6f6330e62972533269696e3403360ea3403360f6a6f6330e62b7253326b696e3403360ea3403360f6a6f4330e62b7253306b496e3403360ea34032a0f6a6f6330e62b5253326b696e34032a0ea5402d0f13049696f06cecacb6a4f6330e6097252ae62b725302d16a77326b696f6a716330e62b7252ae6297252e62972533249696f6a4f6330e6297252a5410d0f05410d0f104d0d5456a4f63305410d0f0ae609725304d0d544e60972536a4f6330e6097252ae609725302af6a773249696f6a4f6330e6097252ae209723302af6a773249696f6a4f6330e2097232ae609725306cecacb3249696f6a4f6130e6097252ae6097252e60972533249696e5410d0f0e6097252ae609725306cecacb3249696f6a4f6330e6097252ae6097252e60972533249696f6a4f6330e6097252ae609705306cecacb3049676f6a4f6330e6097052ae6097252e60972533249696e5410d0f0e6097252ae6097)))
def cone11 (i : Nat) : Nat := (if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then 0x3d301e6f00000000000001e46000007874000000000efa000003b9600000000076883af21d5000000749c39fc1cd50e560720c00001c5a0e188702037be0000000000000376c1b8d00000000000000000000006d900000000000000000000001b3b000000000000000000d8906ba400001ac000000000000000000000006a5c34dc0000000000000348a0000000000000000000000d0e000000000000000000000033e600000000000003394000000000000000000000000000000000000000000000000000000000000668432f000000000000000000194f000000000324c18fd00000000031a800000000000003156000000000000031040000000006164000000000000060c0000018070bef00000000000000000000002f6a00000bc600000000000000000000000000000000000000000000000000000000000000000000000002ec60000000000000000000000000000000000173a0b8880000000016e80b5f80000000000000000000002d2c166d0000059100000161b000000000000000000000000000000000000000000000000000000000000000000000000000002be415c900000568000001577000005538000000000a928000029f814d3000000000000000000a5500000000000000a408000028b0142f00000501827ba000009da000002716000000000000026c4133900000000000001310000000000000012e7000000000257c129509360490c000000000000048680000000008f8800000000000008e400000233e000008bb00000229a000000000000000001124087d8000000000000000000000000000000869042a400000000084000000000010570000040b8000010050000000001fb80000000003ecc0000000007c50000000000000000003d840000000000000000000000f380000000001e1e000000000000000000ee60000000001d7a0000074a00000000000000000000001cd6000000000000000000e42070c80000000000000000037c0000000000000000000000000006e3800001b3c00000000000001aea0d4c0691833e80000000006688000000000ca8000000000000000000000031fc00000c5600000000000000c2d00000000018080bdb05d902e2416c00b3705870000015ca0000000002af015260a6a00000290400000a180000027bc000009c60000000000000099d04ba00000000000000000000000000094b04910000011f2000004680229c10fc085504160200c0fb407b103c401d7c0e6c070d037201aec0d24066903200185c0bdc05c50000016700ae6054a0290813e0099e04a6023e811500000042b020100f640760038701af00cd4061802e3015d0000005220268011f8085803da01c400cd805c80292012000000000001ee00ce00000029400f800000029800a800020000000000000 else 0xd40000000000000000003e771f270f8940000000000000f7f07ba6000000000f6a80000000000000f604000000000000000007ab000001e97800007a0c00001e6e800000000000000000000000003cb41e458f1880000000000000000000003c390000000000000000000000f0400000000000000000000003be700000eef800003b951db6000007686000000000ec68000000001d788eb20753e00001d3b000000000000000000000000000000000000000749a00000000000000000000000000000000003a2400000000073f600001ce90000073520000000000000730000000000000000000395700000e4b8000000000000000000000000000000e41400000000000000000000000001c6e0e2cc0000000000000e228000000000000000000000000000000000000000000000000000000000001c30800007070380f1bf3000006f7a00001bca000006ed600001ba10dc64000036f01b63800000000369e0000000006cea00001b26000006c46000000000d7e86ba20000000000000000000000000000000000000000000000000000000000000000000000001ad4000000000357f00000d5586a5a00001a8200000000034db1a590d22468c034371a070cf940000000000000cef0000000000000000000000000019c98cda8000000000000000000000000000000cd040000331800000cbbc658c329d00000c9d00000000000000000064960000191100000000031f918e80c69c0000000000000c5f862aa00000000000000000000018960c40c000030da000000000000030b11844000000000305f000000000606c000018068bf905f76000017c90bda45e800000178b8000000002eee00000bb1400002e9c000000000000000001739800005c9400000000000000000000017108b7e05b9e2da60000000005afa00000000000000000000016aa0b4ac00002d0200000b36400000000165800000590e0000162f00000000000000000000000000000000000000000002c350000000000000000016060af8c577400000000000000000000000000ae440000000000000000056d02b3f158b0000055da000015620000055362a7215248a88053ee29ce14d28a5f052a6292a14808a360515e2886142e8a0d0501627e213dc89e404ece273e000009c54000026ec0000000004d86269a1338800004c90261f12fb097344b48000012bd895484a522500126b892b8490a245c121980000481423e111dc08e3c46cc233d000008c5000000000000008bac00000000000008b080000000000000000000002299113800000448e221e10fa8000000000000000000000000021cc10d1885e80000000010a880000425020ff106b00000415a000010420816c406400001004800003fc01fb70fc70000000001f65000007cf000001f130f75000003d8200000) else (if i < 3 then 0xcb68658b00001958800000000329c8000000000000328800000c9ce64be000000000000064950000191b0c8860000320d18fc4000063c831cf98dd800000000000018d3400000000000018c90c5f662d200000000000000000000000000c5526280000000000c4ae622e310280000000061dc30d9986280000000030b08000000006138308798398c17a6094303598108c0325ff000000000000000000000017f1cbf3c0000000000000000000002fba8000000000000000017d3000000000000000000000000002f918000000000000000000000000000002f7d17b44bd5000000000179fc000000002f2b00000bc5a5e0400000000000005ddb0000176c8bb125d602e9b9743800005ce5000000000b97800002e4980000000000000000000000000000000000000000000000000000000b8d40000000017104b8305bef2de316e74b6e800002da596c88b5f200002d6816a9cb4fc0000000000000b4aa5a2c2d0180000000059da000000000b36200002cc41657cb26c590d2c72162ec00000000000000000000000002c49161a4b0805817000015fb800000000000015f14af3857732ba515c84000000002b7c00000000000002b6795a9800000000000000000acfa00002b2a158acac0455d92ad800000ab0e555e000000000000055352a8600000000054e3000000000a9740000000015244a8d0543f2a0b14fb4a7880000000014e6c00005372000014d24a6400000297b8000000000000296714a94a4f85253291514804a3b051af28c31457400005134000000000a2160000000014388a172509000001419ca07c501527f6000009f864f9a000013dc49e900000000013c7c9dec4ecd000013a9000004e7b0000139489c5200000000138009bae0000000000000000000000000136b89b0a4d5c2699800009a144ce10000132e000000000264780000000000002633130f40000000000001305000000000000012fac9784000025cc800000000000025b800000968e0000000012c7800004af525660000095464a7a000012944000000000000128a093fe49d6000000000000049ad24c21256c926449092470122dc911c000024328000090784813000011fa800000000000011f048f30476f23a311c748de8000023658000000000000000011a8800000000233c800008ca000000000000000000462722ff11754000045ac22c1915680000000022989142000000000226f80000896c0000000000000000000000000000000000448d2232110ec882443e921e010e5c86dc4345218e10bcc859442a1213c00000849e0000000010898000000000000107f4000041d420d59060882b2413000001041c81bc40b520461018c807440111ff40fefc7f2c00001fb6800007e883f1b00000fbc800003ec9000000000000000000000000007 else 0xdda2c8dad169a4112c695a4112c6a64d6d2de951adda2c8dad169a4112c695a4112c6a60d692de951adda2c8da9169a4112c695a4112c6a64d6d2de951adda2085a98a9a4112c694a8621a1ca8621a1dcd666e5660d6d2dca8621a1d5a4112c6a60d6d15e951adda248d6d15da4112c695a4112c69a4112c6a951adda2085a98a9a4112c696085a98a9cd666e56085a98a8a8621a1e085a98a95a4112c6a64d6d2de951adda2c8dad169a4112c695a4112c6a64d6d2de951adda2c8dad169a4112c695a4112c6a64d6d2de951adda2c8dad169a4112c695a4112c6a64d6d2de851addae48d6d15da4112c695a4112c6a64d6d2de951adda2c8dad169a4112c695a4112c6a64d6d2de851addaec8dad169a4112c695a4112c6a64d6d2de951adda2085a98a9a4112c695a4112c6a64d6d2de951adda2c8dad169a4112c695a4112c6a64d6d2de951adda2c8dad169a4112c695a4112c6a64d6d2de951ad9a248d6d15da4112c695a4112c69a4112c6a951adda2c8dad169a4112c69664d6d2ddcd666e5664d6d2de64d6d2dedcdad2696951adda1cd666e56951adda1a4112c6a951adda15a4112c6a64d6d2de951adda2c8dad169a4112c695a010ac6a64d6d2de951adda2c8dad169a010ac694a8621a1ca8621a1dcd666e5660d6d2dca8621a1d6085a98aa851addaedcdad268a8621a1e085a98a96085a98aa851addaed4dad260a8621a1e085a98a96085a98aa851addaedcdad26a60d6d2de085a98a9664d6d2de851addae64d6d2de64d6d2dedcdad26943c7600000000078c33c4d1e1c4f090781f000000000000077f63be68000000000000000000000ef4800003bbd80000000077523b949dc00000000003b6b80000ed5c7685000000000ecb8763300001d828000075e13adc1d63ceacc00003a9e80000ea2874eb3a6100000e93274703a239d078e7ea73cc39d180000e6f4735139941cbfc000072d639569ca100000725b39191c824e3c071b738c700000e2ca713c00001c44ce1d400003860800000000709800001c1bc0000704600000000000000000380e9bfd00000000037e580000df440000000000000def26f5037938000000000000000000000ddfc000000001bb5400006eac00001ba0c0000000000000000000000000372d1b8c400006e0836ef80000db6c6d8d36b21b4ec00006d1236749b300d92e6c6e36229b070d7e6000035e51ae8400006b7835a79ac98d5fa6ad4355580000d504000000001a964d4606a0734ef1a6d4d3186963349d1a444d1d068bf344b00000d0da6844340d99fc8cf9267a033bb80000ce9c6725337e000000000000000000000000000000336999aa800000000334099960cc5e00000000000000000000000000000000000000000000000cc0c0000000000000000000000000197740000000000)) else (if i < 6 then (if i < 5 then 0xa2c8dad169a4112c695a415ac6a651ad2de955edda2d91ed269a415ac695a4112c69a4112c6a951adda209a9aa89a4112c695a4112c6a64d6d2de951adda2c8dad169a4112c695a4112c69c1666e55a4112c6ac8dad169a4112c696085a98aad8dad26a085a98aa60d6d2de085a98a95a4112c69a4112c6a951adda2c8da5169a4112c695a4112c6a64d6d2de951adda2c8dad169a4112c695a4112c6a64d6d2de951adda2c8dad169a4112c695a014ac6a651ad2de955edda2c91ed169a014ac69664d6d2de851addae64d6d2de64d6d2dedcdad26956411292e651ad2dedd1ed26a109e98ed6411292d56411292e651ad2dedd1ed26a109ed8ed6411292d5a4552c6a651ad2de955ed9a2c91ecd69a4552c695a4552c6a611acede955edda2c91ed169a4552c696089e98a9cda66a4add1ed26a611ad2de089e98a95a055146a611ad2de955e9da2c91ed169a05514695a4552c6a651ad2de955edda2c91ed169a4552c695a4552c6a611a92de955edda2c91e9169a4552c695a4512c69a4512c6a951adda209a9aa89a4512c695a054ac6a651ad2de955edda2c91ed169a054ac696085a98aa851addaedcdad269a922de9e085a98a9664d6d2de851addae64d6d2de64d6d2dedcdad269664d6d2de851addae64d6d2de64d6d2dedcdad2695a4112c69c5666e45a4112c6a48d6d15da4112c695a4112c69a4112c6a951adda2c8dad169a4112c696085a98a9cd666e56dcdad26a60d6d2de085a98a95a4112c6a60d692de951adda2c8da9169a4112c695a010ac6a64d6d2de951adda2c8dad169a010ac695a4112c6a64d6d2de951adda2c8dad169a4112c695a4112c6a64d6d2de951adda2c8dad169a4112c695a4112c6a64d6d2de951adda2c8dad169a4112c695a4112c6a64d6d2de951adda2c8dad169a4112c696085a98aad8dad26a085a98aa60d6d2de085a98a95a4112c6a64d6d2de951adda2c8dad169a4112c695a4112c6a64d6d2de951ad1a2c8dad169a4112c695a4112c6a64d6d2de951adda2c8dad169a4112c695a4112c6a64d6d2de951ad9a2c8dacd69a4112c695a4112c6a64d6d2de851addaec8dad169a4112c695a4112c6a64d6d2de951adda2c8dad169a4112c695a4112c6a64d6d2de951adda2c8dad169a4112c695a4112c6a60d6cede951adda2c8dad169a4112c6956ce68ede951adda0a8621a1da0112c696ce68edd6085a98aad8dad26a085a98aa60d6d2de085a98a95a4112c6a64d6d2de951adda2c8dad169a4112c695a011146a60d6d2de951a9da2c8dad169a01114695a4112c696ce68edda4112c6ac8dad169a4112c696085a98a9cd652e56dcdad268a8621a1e085a98a95a4112c6a64d692de951adda2c8da9169a4112c695a4112c6a64d6d2de951adda2085a98a9a4112c695a4112c6a64d6d2de951a else 0x85a2ddad6c14e92d42406e106c962cd69a458ac6a85a2d9ad6c14e92d51412e80ec962d1691412e80e85a2d1ad6c14e92d51412e80ed962d2691412e80e85a2ddad6c14e92d41006e15ac962d169a0592c6a85a2ddad6c15292d40c06e15ac962d169a058ec6a85a2ddad6c14e12d42406e106c962d169a4592c6a85a2ddad6c15292d56c10e92e651ad2dedd1ed26a855eddad6c10e92d40c06e15ad962d269a059ac6a85a2ddad6c14e92d42406e106c962d169a4592c6a85a2ddad6c15292d5140ee80ed91ed269140ee80e855eddad6c10e92d5140ee80e089ed8a9140ee80e855eddad140ee80d56c10e92e651ad2dedd1ed26a855eddad6c10e92d51412e80ed962d2691412e80e85a2ddad6c14692d5140ee80ed91ed269140ee80e855eddad6c11292d5140ee80ed91ece69140ee80e815ed9ad6c10e92d5140de80ed91ed269140de80e815e9dad5c11292555410e8266526d2c6dd1ad2680c2561655410e82555410e025a566d286d51ed262815eddad5410e0255140d280ed91e9269140d280e855eddad541128255140ee80ed91ed269140ee80e855eddad6c11292d5540ce825a922de82dcdad26a811addad540ce8255540ce825a922de82dcdad26a811addad540ce8255540ce824a8621a02dcdad2680c216949540ce8256089a98aa855addaedd1ad269a962de82089a98a96085a98aa851addaedcdad269a922de82085a98a9468066c1da815ac29c45ae466491ad15da815ac2945c066d9ca849a1e1cc5ae4a6491ad15da415ec69468066c1da815ac29cc5ae4a6491ad15da815ac29468066c1da8152c29c45ae466491ad15da8152c29468066c1da815ec29c45ae466491ad15da815ec2945c066d9d55268e41cc5ae4a6491ad15da415ec6944c066d8955260e41cc5ae4a6491ad15da4152c695a4152c69c45ae465a4152c6a491a915da4152c695a4152c6a651ad2de855eddaec91ed169a4152c695a4112c69c456e465a4112c6a48d6d15da4112c695a4152c6a651ad2de9566dd82491ad15da4152c69458066d9d55268e41cc5ae4a6491ad15da415ac695a4112c69c456e465a4112c6a09a9aa89a4112c695a4112c69c456e465a4112c6a48d6d15da4112c69664d6d2ddcd625e4a64d6d2dd54e68e4264d6d2dd5c45ae465c45ae466651ad2ded526c661c45ae465554e68e4154e68e4025eae106085a98a954e68e415a815ac2a651ad2de955edda2d91ed269a815ac295a815ac2a651ad2de955edda2d91ed269a815ac295a4152c696d2292d1a4152c6ac91ed169a4152c695a8152c2a651ad2de955ed1a2c91ed169a8152c295a415ec6a651ad2de955edda2dd1ed269a415ec695a4152c6a651ad2de955edda2c91ed169a4152c695a4152c6a651ad2de955edda2c91ed169a4152c695a4112c6a64d6d2de951add) else (if i < 7 then 0x9ecced6411292d56411292e651ad2dedd1ed26a109ed8ed6411292d5a4552c6a651ad2de955ed9a2491ad15da4552c695c5a66e46955edda1c5a66e45a4552c69c5a66e45424056106495ed15da459ec6a81a2dda16c15292541c05691add62d269a859d42a81a29dad5c15292541005615ad962d269a059946a81a29dad5c15292541005695ad962d269a859942a81a29dad5415282542406e106c962d169a4592c6a85a2ddad6c15212d40c05695ad962d269a859ac2a81a2ddad5414e825424056106c962d169a4592c6a81a2ddad6c14e12d40c05695add62d269a859ec2a81a2ddad5414e82540c05615ac95ed169a4592c6a819eddad5414e02541005615ac962d169a059146a81a29dad5415202542406e106c962d169a4592c6a85a2ddad6c15212d40c05615ad962d269a459ac6a81a2ddad5414e02540c05615ac91ed169a4552c6a815eddad5410e02540c05695ad962d269a859ac2a81a2ddad5414e82544c066d8ad51ed261cc5ae4a6c91ed169a4152c6944c066d8ad51ed261cc5ae4a6c91ed169a4152c6941005695ad9629269a859ac2a85a2ddad5415282542406e106c962d169a4592c6a85a2ddad6c15292d41005615ad9629269a459ec6a85a2ddad5415282541005695ac9629169a8592c2a85a2d1ad5415282541005695ad9629269a859ec2a85a2ddad5415282541005615ad9629269a459ec6a85a2ddad5415282541005615ac9621169a4592c6a85a2ddad5415202542406e106c962d169a4592c6a85a2ddad6c15292d41005615ac91e9169a4552c6a855eddad5411282541005615ac9e92a95a4552c6a855eddad5429282541005615ad9629269a459ac6a85a2ddad5415282541005695ad9629269a859ac2a85a2ddad5415282540c05695ac962d169a8592c2a81a2d1ad5414e82540c05695add62d269a859ec2a81a2ddad5414e82542406e90610e2cceda859ac2a85a2d1ad6c15292d42405610610e2cceda459ec6a85a2d1ad6c15292d40c05615add62d269a459ec6a81a2ddad5414e02555414e826655ed2dedd62d26a81a2ddad5414e82542406e106c962d169a4592c6a81a2ddad6c14d92d42406e906495dd15c684a6c1e10e2d8ed1412e80d41006e15ac91ed169a4552c6a855eddad6c11282d40c05695ad91ed269a855ac2a815eddad5410e82541005615ac91ed169a4552c6a855eddad5411282540c05615add1ed269a455ec6a815eddad5410e82541005615ac91ed169a055146a815e9dad5411282540c05615ac91ed169a4552c6a815eddad5410e02541005615ac91e9169a4552c6a855eddad541128255a4552c6a651ad2de955edda210ded8ada4552c6956c10e82e651ad2dedd1ed26a855eddad6c10e82d40c06e95ad962d269a859ac2a85a2ddad6c14e92d51412e80ed962d2691412e80e else (if i < 8 then 0xddad540ce8255540ce82664d6d2dedcdad26a811addad540ce8255540ce82664d6d2dec8dad1680c215959540ce8255540ce82664d6d2dedcdad26a811addad540ce8255540ce82664d6d2dedcdad26a811addad540ce8255540ce82664d6d2dedcdad269cc55e4a5540ce82540c2159580c215959a926dea2951adda00c2159595540ce82664d6d2dedcdad26a811addad540ce82545c066d9ca849a1e1cc5ae4a6491ad15da415ec6945c066d9d55269241cc5ae4a45c066d9da415ec6945c066d9d54e58e41cc56e4a45c066d9da411ec694a849a1e2611ad2de08aa98aad526c661cc5ae4a55cc56e4a5cc56e4a664d6d2dd54e68e41cc56e4a55a415ec6a651ad2de955edda2dd1ed269a415ec694a849a1e2611ad2de089e98aad91ed268a849a1e15a415ec6a611acede955edda2dd1ed269a415ec696951adda209a9aa8a951adda1a411ec6a951adda16085a98aa851addaec8da5168a86a1a1e085a98a94a849a1e2611ad2de089ed8aad91ed268a849a1e14a869a1e260d6d2de119daed6d8dad268a869a1e140c06e95ad962ce69a859ac2a81a2d9ad6c14e92d40c05695ad9629269a859ac2a85a2ddad5414e82540c05695ad962d269a859ac2a81a2ddad5414e82540c05695ad962ce69a859ac2a81a2d9ad5414e82551412e80e08e2d8a91412e80e85a2ddad1412e80d40c05695ad962d269a859ac2a81a2ddad5414e82544c492d8ad51ed261cc9ae4a611e1aecc4c492d894a849a1e2611ad2de089e98aad91ed268a849a1e15a815ec2a651ad2de955ed9a2d91ece69a815ec295a815ec2a651a92de955edda2d91e9269a815ec295a815ec2a611a92de955edda2d91e9269a815ec295a815ac2a651ad2de955edda2d91ed269a815ac296089e98aa855eddaed51ed260a849a1e2089e98a942406e106c962d169a4592c6a85a2d1ad6c15212d42406e106c962d169a4592c6a85a2ddad6c15212d42406e106c962d169a4592c6a85a2d1ad6c15292d42406e906495ed15da859ac28ac8da5e02406e90542406e106c962d169a4592c6a85a2d9ad6c15292d42406e106495ed15da4592c68ac8d65e02406e10542406e106495ed15da459ac68ac8da5e02406e10542406e106c962d169a4592c6a85a2ddad6c15292d41004615ad9629269a459ac6a85a2ddad0c11294d40c05695ad962d269a859ac2a81a2ddad5414e82541005615ac9629169a4592c6a85a2ddad5415282540c05615ac962d169a4592c6a81a2ddad5414e0255a4152c69c45ae465a4152c6a491ad15da4152c6956411292e651ad2ded91ed26a109ed8ed6411292d56411292e651ad2ded51ed262109ed4ed6411292d56411292e651a92ded91e926a109ed8ed6411292d56411212e651ad2ded51ed262109ed8ed6411212d56411292ce88eda12651ad2de10 else 0x8da455ec696951adda2851addaec9a52695a451ec6a951adda156c15292e655ed2ded962d26a81a2d9ad6c15292d42406e906c962d169a859ec290c12e94d6c15292d5a459ec6954152825a459ec6ac962d169a459ec6940c0559580c055959a455ec680c0559595410e8255a411ec696cde92d1a411ec695cde9251a411ec6956c14e92e655ed2ded962ce6a85a2d9ad6c14e92d56c14e92e615ecededd62d26a85a2ddad6c14e92d56c15292e615ed2ded962d26a85a2ddad6c15292d56c15292e655ed2dedd62d26a85a2ddad6c15292d56c10e92e651ad2ded51ec662049ed4ed6c10e92d56c10e92da962da82dd1ed26a855eddad6c10e92d4ac49a1e0ac49a1e2089ed8aad51ed261cc5ae4a556c10e92e651ad2ded91ece6a855ed9ad6c10e92d56c10e92e651ad2dedd1ed26a855eddad6c10e92d56c10e92e611acededd1ed26a855eddad6c10e92d56c10e92da962da816c10e92c8449a04d6c10e92d56c10e92e651ad2dedd1ed26a855eddad6c10e92d56c10e92e651ad2dedd1ed269cc5ae4a56c10e92d56c10e92da962da82dd1ed26a049ed8ed6c10e92d56c10e92e611ad2ded91ed26a855eddad6c10e92d40c22e95ad91ed269a962da82d51ed2600c22e95956c10e926955edda2611ad15e815edda16c10e92556c10e92da962da82dd1ed26a855eddad6c10e92d40c22e95a4919d15c6862e1c2049ed8ec0c22e95956c10e92e651ad2dedd1ed26a855eddad6c10e92d56c10e92e651ad2dedd1ed26a855eddad6c10e92d56c10e92e651ad2dec91ed1680c22e9596c10e92d56c10e92e651ad2dedd1ed26a855eddad6c10e92d56c10e92e651ad2dedd1ed26a855eddad6c10e92d56c10e92e651ad2dedd1ed26a049ed8ed6c10e92d56c10e92e651ad2dedd1ed26a855eddad6c10e92d55410d824aca191e2d91ed26a815eddad5410d82556411292e651ad2dedd1ed26a815eddad6411292d5540ce82664d6d2ded4dac661cc56e4a5540ce8255540ce825a926dea2dcdad26a811addad540ce8255cc56e4a611a5aad9cc56e4a6d4dad261cc56e4a55540ce82664d6d2ded8dace6a811ad9ad540ce8255540ce82664d6d2dedcdad26a811addad540ce8255540ce825a926dea2dcdad26a811addad540ce8255540ce825a926dea1540ce8240c215959540ce8255540ce82664d6d2dedcdad26a811addad540ce8255540ce82664d6d2dedcdad269cc56e4a5540ce8255540ce825a926dea2dcdad269cc56d0a5540ce8255540cd826d8dad269540cd826811addad540cd8255540ce82664d6d2dedcdad26a811addad540ce8255540ce826951adda260d6d15e811adda1540ce8255540ce825a926dea2dcdad26a811addad540ce8255cc56e4a611a5aada48d5d15e1da5aa99cc56e4a55540ce82664d6d2dedcdad26a811a)))) else (if i < 14 then (if i < 11 then (if i < 10 then 0xcc56e4a55cc56e4a609a5aa89cc56e4a6d4dad261cc56e4a5458062d9ed91ed269cc5ae4a6d91ed269a015ac6945c052d9edd1ed269cc5ae4a6089e98a85c052d9d44c052d8ad4dad261cc56e4a6119daed04c052d8944c066d8ad51ed261cc5ae4a6089e98a9a4152c694a849a1e2611ad2de089e98aadd1ed269cc5ae4a54a805a1e0a805a1e2085a98aad4dad260a805a1e15cc56e4a6119daed1cc56e4a6d4dad261cc56e4a55a815ac2a651ad2de955edda2d91ed269a815ac294a849a1e2611ad2de089e98aad91ed268a849a1e14a849a1e0a849a1e2089e98aad51ed261cc5ae4a55a815ac2a611ad2de955edda2d91ed269a815ac295a815ec29a815ec2a955edda2dd1ed269a815ec2940c259596815eddad55258e42d91ed2680c2595954a849a1e2616129ee089a98aad9a12aa4a849a1e16089a98aad5a92e26089a98a8a849a1e2089a98a96089a98aa851addaed4dad260a849a1e2089a98a96951adda2851addaed4dad260a869a1e2951adda140c259596815eddad55258e42d91ed2680c2595956951adda209a9aa8a951adda0a869a1e2951adda16951adda2851addaed4dad260a869a1e2951adda16085a98aa851addaed4dad260a86a1a1e085a98a96085a98aa085a98aa951adda0a86a1a1e085a98a96951adda2851addaed5a92e2565e1212e951adda14e88eda12089ed8a914e6acc0e88eda12089ed8a96085a98aa851addaed4dad261a922de82085a98a96951adda2851addaed4dad260a869a1e2951adda15140ee80e089ed8a9140ee80e855eddad140ee80d4a849a1e1a966da82089e98aad51ec661cc5ae4a55140ee80e089ed8a9140ee80cac49a5e1140ee80d4a849a1e1a966de82089e98aad51ed261c45ae0655140ee80e089ed8a9140ee80cac49a1e1140ee80d4a849a1e1a9615a821c9e98ead51ed261cc5ae4a55140c680e089e98a9140c680e855eddad140c680d4a849a1e261611dc6089a98aad5a92e25cc56e4a55cc56e4a6119daecdcc56e4a6d4dad261cc56e4a55cc56e4a609a9aa89cc56e4a6951adda1cc56e4a54a849a5e1a962da82109e98eed51ed261cc5aa4a54a805a1e1a922da82085a98a9a922da81cc16e4a54a805a1e0a805a1e2085a98aad4dad261cc16e4a56085a98aa851addaed4dad261a922da82085a98a956c14e92e655ed2ded962ce6a81a2d9ad6c14e92d56c15292e655ed2ded962d26a85a2d9ad6c15292d56c14e92e615ecededd62d26a81a2ddad6c14e92d56c14e92e655ecededd62ce6a81a2ddad6c14e92d56c15292e615ed2dedd62d26a85a2ddad6c15292d56c15292e655ed2dedd62d26a81a2ddad6c15292d40c05695a09e5aa89a855ec2a815eddad5410d82545c4a6d9e955ed9a1cc9ae4a45c4a6d9da455ec6945c4a6d9e955edda1cc9ae0a61de5ae else 0x12e80d40c05595ad95ed2680c05595a81e5eed95414d82540c05595ad91ed2680c055959cc99e4a55410d82551412e80ed962d2691412e80e85a2ddad1412e80d40c06e95ad962d269a859ac2a85a2ddad6c14e92d51412e80e08e2d8a91412e80e85a2ddad1412e80d5142ae80e08ded8a9142ae80e855eddad142ae80d40c06d95ad962d2680c06d95a85a2ddad6c14d92d51412e80e08e2d8a91412e80e85a2ddad1412e80d5140ee80e089ed8a9140ee80e855eddad140ee80d40c06e95ad962d269a859ac2a85a2ddad6c14e92d51412e80e08e2d8a91412e80e85a2d9ad1412e80d51412e80e615ed2dd1412e80e655ed2dd1412e80d5140ee80ce88eda11140ee80e049ed4ed140ee80d5140ee80ce88eda11140ee80e049ed4ed140ee80d5140ee80ce88eda11140ee80e049ed4ed140ee80d5140ee80ce88eda11140ee80e049ed4ed140ee80d5140ee80ce88eda11140ee80cac49a5e1140ee80d5140ee80ce88eda11140ee80cac49a1e1140ee80d55410d826d51ec662491ad15dcc5ae4a55410d8254a849a1e0a849a1e208a698aad52ac661cc5ae4a55140ee80ce88eda11140ee80e049ed4ed140ee80d4ac5d91e0ac5d91e2059d6eced4dac661cc56e4a555410d8245866d1d95410d825cc5ae4a55410d8254ac5da5e0ac5da5e2059d6eced4dac661cc56e4a54a849a1e0a849a1e208a698aad52ac661cc5ae4a55cc16e4a425e2e905cc16e4a6d4dac661cc16e4a55140ee80e089ed8a9140ee80e855eddad140ee80d4a849a1e1a166de84a849a1e2d51ec661c45ae4655140ee80e089ed8a9140ee80cac49a5e1140ee80d4a849a1e1a166d29ca849a1e2955adda1cc66e4995140de80e089e98a9140de80e1c9e98e9140de80d4a849a1e1a962de82089a98aad51ad261cc66d0a54a849a1e0a849a1e2089a98aad5a92e24a849a1e15140ee80e089ed8a9140ee80e855eddad140ee80d4a849a1e1a922de82089a98aad4dad260a849a1e14ac5d91e0ac5d91e2119daeced4dad260ac5d91e14ac5da5e0ac5da5e21d9dae8ed4dad260ac5da5e15140e680e089e98a9140e680e109e98ed140e680d4a849a1e1a962de82089a98aad51ad260a849a1e14a849a1e1a962de82089a98aad51ad261cc66e0994a805a1e1a922de82085a98aad4dad260a805a1e140c05595ad91ed2680c05595a815eddad5410e82540c05595ad91ed2680c05595a815eddad5410e82544c492d8ad51ed261cc9ae4a611e1aecc4c492d895cc96e4a609a5aa89cc96e4a6d4dad261cc96e4a55140e680e09e5aa89140e680e11e5aacd140e680d4a865a1e0a865a1e2059d6eced4dac661cc56e4a54a865a1e0a865a1e209a5aa8ad4dad260a865a1e140c05595ad91ed2680c05595a815eddad5410e8255cc56e4a6119daed5cc56e4a6d4dad261) else (if i < 12 then 0x2d9d40c05595a11e1aecc58492d9e815eddad5410d82544c492d8ad51ed261cc9ae4a611e1aecc4c492d8944c492d8ad51ed261cc9ae4a611e1aecc4c492d8944c492d8ad4dad261cc96e4a6119daec84c492d8944c492d8ad51ed261cc9ae4a611e1aecc4c492d8940c05595ad91ed2680c05595a815eddad5410d82544c052d8ad4dad261cc56e4a6119daed04c052d8940c05595a11e1aecc58492d9e815eddad5410d82544c052d8ad4dad261cc56e4a6119daed44c052d8941006d95a10e2d8ec58492d9e85a2ddad6c15192d4100559181005591858492d9e81a2ddad6c14d92d4100559581005595858492d9e81a29dad5415182540c05595ad91ed2680c05595a815eddad5410d825458052d9ed91ed269cc5ae4a6d91ed2680c29959540c05595ad91ed2680c05595a815eddad5410d82540c05595a11e1aecc58492d9e815eddad5410d82540c05595ad91ed2680c05595a815e9dad5410d82540c05595a11e1aecc58492d9dcc9ad0a55410d82540c05595a11e1aecc58492d9e815eddad5410d82540c05595a11e1aecc58492d9e815eddad5410d82540c05595a11e1aecc58492d9dcc9ae4a55410d82540c05595a11e1aecc58492d9e815eddad5410d82540c05595ad91ed2680c05595a815eddad5410d82540c05595ad91ed2680c05595a815eddad5410d82540c05595a11e1aecc58492d9e815eddad5410d82540c05595a11e1aecc58492d9e815eddad5410d82540c05595a11e1aecc58492d9e815eddad5410d82540c05595ad91ed2680c05595a815eddad5410d82555410d824aca191e2d91ed26a815eddad5410d82540c05595a11e1aecc58492d9e815eddad5410d825458492d9ed91ed269cc9ae4a611e1aecc58492d9d4a8a5a1e0a8a5a1e211e1aeced91ed268a8a5a1e1554101824aca191e2d91ed26a815eddad5410182540c05595ac962d1685c492d9e81a2ddad5414d82541006e95ac962d168684a2c1dcc9ee4a56c15292d40c05595ad91ed2680c055959cc9ae4a55410d825424056906d962d269a859ac2a81a2ddad6415292d51412e80e08e2d8a91412e80e85a2ddad1412e80d51412680ed962d2691412680e655ed2dd1412680d41005695add62d269a859ec2a81a2ddad5415282541005595ac962d1685849159e81a2ddad541518255142a680e08de98a9142a680e10de98ed142a680d410055958100559585849159e81a2ddad5415182541005695ad962d269a859ac2a81a2ddad5415282540c05695add62d269a859ec2a81a2dda15414e82541006e95ac962d169a859ac290c12e94d6c15292d51412e80e615ed2dd1412e80e655ed2dd1412e80d40c05695ad962d2680c056959cc9ee4a55414e82541006e95ad962d2681006e95a10e2d8ed6c15292d51412e80ed962d2691412e80edd62d26914 else (if i < 13 then 0x2d40c05595ad91ad2680c05595a81a5eed95410e82540c05595ad95ed2680c05595a81e5eed95414e82540c05595a09a9aa880c05595a81a5eed95410d82540c05595ad91ad2680c05595a81a5eed95410e82541005595ad95ed2681005595a81e5eed96415292d55410e8266516d2ded51ac661cc55e4a55410e82540c299595cc55e4a5552a8e424916d15c0c29959541c1dad9285a5eed96d1e92d2d91ad2681c1dad9145c492d9ed95ece69cc9ae4a6c95ecd685c492d9d50c11e94ed95ed2690c11e94dcc9ae0a55c14e92545c492d9edd5ed269cc9ae4a6c95ed1685c492d9d50c11294ed95e92690c11294e10de98ed0c11294d45c492d9edd5ed269cc9ae4a6c95ed1685c492d9d45c492d9e95a5ee19cc96e4a609a9aa885c492d9d4a88da1e2615ad2de08de98aadd5ed269cc9aa4a550c11294ed95ed2690c11294e10de98ed0c11294d4a849a1e26116d2dca849a1e2d51ac661cc56e4a545c052d9ca849a1e1cc56e4a64916d15c5c052d9d45c052d9ed91ad268a849a1e2c91ad1685c052d9d4a849a1e26116d2de089a98aad91ad268a849a1e15a815ec2a651ad2de955edda2dd1ed269a815ec295a815ec2a611ad2de955edda2dd1ed269a815ec295a815ec29a815ec2a955edda2dd1ed269a815ec2941c25ad92815eddad6d268ed2d91ed2681c25ad914a849a1e26116d2de089a98aad91ad268a849a1e145c052d9edd1ed269c45ae466c91ed1685c052d9d40c259596811addad54e68e42d8dad2680c25959540c259596815eddad652292d2d91ed2680c25959540c259596811addad54e58e4209a9aa880c25959540c259596811addad6cde92e2d8dad2680c25959540c25959681a9eed9651e92d2d91ad2680c25959544c250596811addad64de12d2c8da51684c25059541006d95a10e2d8ec58492d9e85a2ddad6c15192d42406e10610e2d4eda4592c6a85a2d1ad6c15212d51412e80e08e2d4a91412e80e85a2d1ad1412e80d51412e80e08e2d8a91412e80e85a2ddad1412e80d44c652d8ad51ed261cda66e4a109ed8ec4c652d8941c05691add62d269a859d42a81a29dad5c15292541005695ad962d269a859942a81a29dad5415282544c492d8ad51ed261cc9ae4a610ded8ac4c492d8940c05695ad91ed269a855ac2a815eddad5410e82544c492d8ad51ed261cc9ae4a610ded8ac4c492d8940c05595ac91ed1685c492d9e815eddad5410d82544c492d8ad51ed261cc9ae4a610de98ac4c492d8944c49158ad51ed261cc9aa4a610de98ac4c4915895c49ae46608ded8a9c49ae466d51ed261c49ae4654ac8da1e0ac8da1e208ded8aad51ed261cc9ae4a551412e80ed962d2691412e80e85a2ddad1412e80d44c492d8ad51ed261cc9ae4a611e9aecc4c492d89458492d9ed91ed269cc9ae4a611e1aecc5849 else 0x5a815ec29a815ec2a955adda2dd1ad269a815ec295a815ec2a651ad2de955edda2dd1ed269a815ec295a815ec29a815ec2a955edda2dd1ed269a815ec295a815ec2a611acede955edda2dd1ed269a815ec295a815ec2a6522d2de955adda2dd1ad269a815ec295a815ec29a815ec2a955adda2dd1ad269a815ec295a815ec29a815ec2a955edda2dd1ed269a815ec295a811ec29a811ec2a951adda2dcdad269a811ec295a815ec29a815ec2a955edda2dd1ed269a815ec296951adda209a9aa8a951adda1a811ec2a951adda15a811ec29a811ec2a951adda2dcdad269a811ec295a815ac29a815ac2a955edda2d91ed269a815ac294a869a1e0a869a1e2119daed6d8dad268a869a1e141c06d91ac962cd685c492d9e81a2ddad6c14e92d41c06e91add62d269a859ec2a81a2ddad6c14e92d41c06d91ac962d1685c492d9e85a2ddad6c15292d41c06d91ac962d1685c492d9e85a2ddad6c15292d41c06d91ac91ed1685c492d9e815eddad6c10e92d41c06d91ac95ed1685c492d9e819eddad6c14e92d41c06d91ac962d1685c492d9e81a2ddad6c14e92d41c06d91ac962d1685c492d9e81a2ddad6c15292d5140ee80e611acedd140ee80dcc5ae0a56c10e92d41c06e91add62d269a859ec2a81a2ddad6c14e92d40c05695add1ed269a855ec2a815eddad5410e82540c05695add1ed269a855ec2a815eddad5410e82540c06d95ac91ecd685c492d9e815ed9ad6c10e82d40c05695add1ed269a855ec2a815eddad5410e82540c06d95ac91ed1685c492d9e815eddad6c10e82d41005595ac91e91685c492d9e855eddad5411282540c06d95a10ded8ac5c492d9ed51ed2600c06d95941005595ac91ed1685849159e815eddad5411282541006d95ac91ed1685c492d9e855eddad6c11282d5540ce82664d6d2ded4dac661cc56e4a5540ce82545c052d9d54ea8e41cc56e4a648d6d15c5c052d9d40c05595858492d9c0c05595a815eddad5410d82540c05695a09e5aa89a855ec2a815eddad5410d82540c06d95a09e5ae885c492d9e815ed9ad5410d82540c05695a09e5aa89a855ec2a815eddad5410d82541c06d91a09e5ae885c492d9e815eddad5410d82540c05595a11e1aecc5c492d9e815eddad5410d82540c05595a09a5aa885c492d9e811addad540cd82540c05595ac9a526944c49058a811addad5428d82540c05695a09e5aa89a855ec2a815eddad5410d82545c052d9d54e98e41cc56e4a609a5aa885c052d9d45c052d9e951adda1cc56e4a609a5aa885c052d9d40c06d95ad95ece680c06d95a81e5aed96c14e92d40c05695add5ed269a865ec2a81e5eed95414e82541c06d91ad95ed2681c06d91a81e5eed96c14e92d41005595ad95e92681005595a85e5eed95415282541c06d91ad95ed2681c06d91a85e5eed96c1529))) else (if i < 16 then (if i < 15 then 0x410e824aca1a5e2dd1ed26a815eddad5410e8255540ce824a8a5a1e2dcdad26a811addad540ce8255140e680ed91ed269140e680e815eddad6411292d4a865a1e0a865a1e2059d6eced4dac660a865a1e14a865a1e0a865a1e21d9dae92d8dad268a865a1e1554142826615ec6dedd62d26a81a2ddad5414282551412e80ed962ce691412e80e81a2d9ad6c14292d40c05695add62d269a859ec2a81a2ddad5414e82541c05691add62d269a859d42a81a29dad5c14292540c05695add62d269a859ec2a81a2ddad5414e82551410680ed96292691410680e85a2ddad5414682540c05695add62d269a859ec2a81a2ddad5414e825554101824584a2d9d54101826815eddad54101825554142826655ed2dedd62d26a81a2ddad54142825554142826615ec6dedd62d26a81a2ddad5414282551412e80ed962d2691412e80e85a2ddad6c14692d554102826611ac6dedd1ed26a815eddad54102825468062c1edd1ed269c45ae066c91ed16868062c1d5a815ec2a611ac6de955edda2dd1ed269a815ec29554142826655ec6dedd62c66a81a2ddad541428254684a6c1edd62d269cc9ee4a6dd62d269a859ec2951412e80ed962ce691412e80e81a2d9ad6c14e92d4684a2c1da859ec29cc9ee0a6495ecd5da859ec29468062c1da815ec29c45ae066491ac55da815ec29468066c1da815ec29c45ae466491ac55da815ec29468066c1da815ec29cc5ae4a6491ad15da815ec29468062c1da815ec29cc5ae0a6491acd5da815ec29468066c1da815ec29c45ae4645c066d9da815ec29468052c1da815ec29cc5ad0a6491ad15da815ec294a849a1e1a815ec2a089a98a9a815ec29cc62d0a54a849a1e1a815ec2a089e98a955269240a849a1e15a815ec29a815ec2a855eddaedd1ed269a815ec294a849a1e1a811ec2a089a98a954e68e40a849a1e15a815ec2955268e41a815ec280c269595a815ec294a869a1e1a811ec2a09a9aa8954e58e40ac5d91d15a811ec2954e68e41a811ec289c5da5cda811ec294a849a1e0a849a1e208aa98aad526c660a849a1e14a869a1e0a869a1e209a9aa8954e68e40a869a1e14a88da1e1a859ec2a08de98aa959edda0a88da1e151412e80ed95ece691412e80cac8da5e11412e80d55414e8266166d2dedd5ed269cca6e0a55414e82541c05691add5ed269a859d42add5ed2691411e80d5a859ec29a859ec2a959edda2d95e9269a859ec295a859ec29a859ec2a959edda2dd5ed269a859ec294a8a9a1e1a855ec2a09a9aa8a955adda0a8a9a1e15a859ec29a859ec2a959edda2dd5ed269a859ec2951412e80ed95ed2691412e80cac8da1e11412e80d4a8a9a1e0a8a9a1e209a9aa8ad91ad268a8a9a1e14a849a1e0a849a1e2089a98aad91ad268a849a1e15a815ec29a815ec2a955adda2d91a9269a815ec29 else 0x5695ad9629269a859ec2a85a2ddad5415282551411280da859ec291411280d0c11294d5415282541005695ad9629269a859ec2a85a2ddad5415282551411280ed95e92691411280e10de98ed5415282541c06e91add62d269a859ec2a85a2ddad6c15292d554112825a855ec2ad91e926a855eddad5411282551412680ed96292691412680e85a2ddad6415292d40c05695add62d269a859ec2a81a2ddad5414e8254684a6c1edd62d269c49ee466dd62d269a859c4294a88da1e1a865ec2a08da98aa95a5ee19cca2d0a556c10e82da855ec2add1ed26a855eddad6c10e82d40c05695add1ed269a855ec2a815eddad5410e82555410e826651ac6dedd1ec66a815eddad5410e82556c10e82da855ec2ad91ece6a815ed9ad6c10e82d56c11282da855ec2add1ed26a855eddad6c11282d554112825a855d42add1ed26a815e9dad5411282555410e825a855ec2add1ad269cca2d0a55410e825554112825a855ec2ad91e926a855eddad54112825554112825a855ec2add1ed26a815eddad5411282556c10e82da855ac2add1ed26a855eddad6c10e82d41c05691add62d269a859ec2a85a2ddad6c15292d40c06e95ad962ce69a859ec2a81a2d9ad6c14e92d41c05691add62d269a859d42a81a29dad5c15292540c05695ad9629269a859ec2a85a2ddad5415282540c05695add62d269a859ec2a81a2ddad5414e82540c05695add1ed269a855ec2a815eddad5410e82540c05695add62d269a859ec2a81a2ddad6415292d40c05695add1ed269a855ec2a815eddad5410e82540c05695add62d269a859ec2a81a2ddad5414e82541c06e91ac962d168684a2c1dcc9ee0a56c14e92d40c05695ad91ed2680c0569580c0569595410e82540c05695ad962d269a859ec2a81a2ddad5414e82540c0569580c056959a855ec2a815eddad5410d82540c056959cc9ad0a5a855ec2a815eddad5410d82540c05695a09e5aa89a855ec2a815eddad5410d82540c05695a09e5aa89a855ec2a815eddad5410d8255140ee80e09e5ae89140ee80e815ed9ad5410d8255cca2d0a609a5aa89cca2d0a6955adda1cca2d0a555410d824aca1a5e2dd1ed26a815eddad5410d8254a8a5a1e1a851ec2a09a5aa8a951adda0a8a5a1e15a811ec29a811ec2a951adda09c5d91d1a811ec2951412e80ed962c6691412e80e85a2ddad6c14e92d51412e80da859ac291412e80d0c12e94d6c14e92d51412e80ed962d2691412e80e85a2ddad6c15292d41c06e91add62d269a859ec2a85a2ddad6c15292d56c10e92da855ac2add1ed26a855eddad6c10e92d40c06e95ad962d269a859ac2a85a2ddad6c14e92d51412e80ed962d2691412e80e85a2ddad6c15292d51412e80ed962ce691412e80e85a2d9ad6c14e92d40c05595ad91ed2680c05595a815eddad5410e82555) else (if i < 17 then 0xc1ca849a1e1cc5ae4a6651ad2dc68066c1d468066c1ed526c661cc5ae4a6651ad2dc68066c1d468066c1ed526c661cc5ae4a6651ad2dc68066c1d468066c1ed526c661c45ae466651ad2dc68066c1d468066c1ed526c661cc5ae4a6651ad2dc68066c1d468066c1ed526c661cc5ae4a6651ad2dc68066c1d46806541ed526c661cc5aa4a6651ad2dc6806541d468066c1ed526c661c45ae466651ad2dc68066c1d468066c1ed526c661cc5ae4a6651ad2dc68066c1d468066c1ed526c661cc5ae4a6651ad2dc68066c1d468062c1ed526c661cc5ae4a6611ad2dc68062c1d5cc5ae4a5cc5ae4a6651ad2ded526c661cc5ae4a540c06e95ad962ce69a859ec2a81a2d9ad6c14e92d41c06e91add62d269a859ec2a85a2ddad6c14e92d40c05695add62d269a859ec2a81a2ddad5414e82541c05691add62d269a859d42a81a29dad5c14e92540c05695add62d269a859ec2a81a2ddad5414e82540c05695ad9629269a859ec2a85a2ddad5414e82540c05695add1ed269a855ec2a815eddad5410e82541c06e91add62d269a859ec2a85a2ddad6c14e92d40c05695add1ed269a855ec2a815eddad5410e82540c05695add62d269a859ec2a81a2ddad5414e82540c05695add1ed269a855ec2a815eddad5410e82540c05695add62d269a859ec2a81a2ddad5414e825468062c1edd1ed269cc5ae0a6dd1ed269a815ec2941c06e91ac962d168684a2c1e85a2ddad6c14e92d41c06e91ad962ce69a859ec2a81a2d9ad6c14e92d40c06d95ad962d2680c06d95a85a2ddad6c14e92d50c11e94ed962d2690c11e94dcc9ee0a55c14e92551412e80ed962d2691412e80e85a2ddad6c14692d40c05695add62ce69a859ec2a81a2ddad5414e825424056906dd62c669a859ec2a85a2ddad6c15292d40c05695add62d269a859ec2a81a2ddad5414e82555414e826655ac6dedd5ec66a81e9eed95414e82542406e906d962ce69a859ec2a81a2d9ad6c14e92d42406e906d962ce69a859ec2a81a2d9ad6c14e92d40c06e95ad962ce69a859ec2a81a2d9ad6c14e92d41c06e91add62d269a859ec2a85a2ddad6c15292d56c10e92da855ec2ad91ece6a815ed9ad6c10e92d41c06e91a1cded8e9a859ec290c12e94d6c15292d5a815ec29a815ec2a955adda15d1e9251a815ec2955414e8266566d2dedd5ed269cca6e4a55414e82555414e8266566c6dedd5ec669ccaad0a55414e82551412e80ed95ece691412e80dcca2d0a56c14e92d41c06e91add5ed269a859ec2a10ded8ed6c15292d55410e825a855ec2add1ad269cca2d0a55410e82551412680ed95ed2691412680e10de98ed6415292d55414e8266566c6eadd5ad26a81a5e6e55414e8255a815ec29a815ec2a955adda2dd1ad269a815ec2941005695ad9629269a859ec2a85a2ddad541528254100 else (if i < 18 then 0x40c2595956cde92e2d8dad2680c25959540c06e95ad962ce69a859ac2a81a2d9ad6c14e92d40c05695add62d269a859ec2a81a2ddad5414e82540c05695ad95ece69a869ac2a81e9aed95414e82540c05695ad962ce69a859942a81a299ad5414e82540c05695ad91ece69a855ac2a815ed9ad5410e82542406e906d962ce69a859ac2a85a2d9ad6c14e92d424056906d962ce69a859ac2a81a2d9ad6414e92d42406e906d962ce69a859ac2a85a2d9ad6c14e92d468066c1ed91ece69cc5ae4a6d91ece69a815ac2942406e906d962ce69a859ac2a85a2d9ad6c14e92d42406e906d962ce69a859ac2a85a2d9ad6c14e92d42406e906d962ce69a859ac2a85a2d9ad6c14e92d42406e906d962ce69a459ac6a85a2d9ad6c14e92d42406e906d962ce69a859ac2a85a2d9ad6c14e92d42406e906d962ce69a859ac2a85a2d9ad6c14e92d42406e906d962ce69a859ac2a85a2d9ad6c14e92d42406e906d962ce69a859ac2a85a2d9ad6c14e92d424056906dd62d269a859ec2a85a2ddad6c15292d424056906dd62d269a859ec2a85a2ddad6c15292d56c10e82e651ad2ded51ec661cc9ae4a56c10e82d40c05695ad91ece69a855ac2a815ed9ad5410e825554112826651ad2ded51ec661cc9ae4a55411282556c10e82e611aceded51ec661cc9ae0a56c10e82d55410e8266516d2ded51ac661cc96e4a55410e825554112826651ad2ded51ec661cc9ae4a554112825554112826651ad2ded51ec661cc9aa4a55411282556c11282e651ad2ded51ec661c49ae4656c11282d56c10e82e651ad2ded51ec661cc9ae4a56c10e82d424056906c9625169a859ec2a85a2ddad6415212d554142826655ed2ded962c66a81a2d9ad5414282540c05695add62d269a859ec2a81a2ddad5414e825554142826655ad2ded95ec66a81e9aed95414282551412e80ed962c6691412e80e85a2d9ad6c14692d42406e906655ed2dc684a6c1cac8da5e02406e9054684a6c1edd66d269cc9ee4a6655ed2dc684a6c1d4684a6c1ed566c661cc9ae4a6655ad2dc684a6c1d4684a2c1ed566c661cc9ee4a6615ed2dc684a2c1d4a849a1e2611ad2de08a298aad526c661cc5ae4a55cc5ae4a5cc5ae4a6651ad2ded526c661cc5ae4a55cc9ae4a605e6d4ee651ad2ded526c661cc9ae4a5468062c1ed526c661cc5ae4a6611ad2dc68062c1d468066c1ca849a1e1cc5ae4a6651ad2dc68066c1d468066c1ed526c661cc5ae4a6651ad2dc68066c1d468066c1ed526c661cc5ae4a6651ad2dc68066c1d468066c1ed526c661cc5ae0a6611acedc68066c1d468066c1ca849a1e1cc5ae4a6651ad2dc68066c1d468066c1ca849a1e1cc5ae4a4241eac5068066c1d468066c1ed5268661cc5ae4a6611a92dc68066c1d468066c1ed526c661cc5ae4a6651ad2dc68066c1d468066 else 0xc05695add1ed269a855ec2a815eddad5410e82540c06e95ad91ed269a855ac29cc9ad0a56c10e82d40c06e95ad962d269a859ac2a85a2ddad6c14e92d41006e95ad962d269a859ac2a10e2d8ed6c15292d42406e906dd62d269a859ec2a10e2d8ed6c15292d40c06e95ad91ed269a855ac2a04ded8ed6c10e92d42406e906d962d269a859ac2a10e2d8ed6c15292d40c06e95ad962d269a859ac2a04e2d8ed6c14e92d41005695add62d269a859ec2a10e298ed5415282540c06e95ad962d269a859ac29cc9ee0a56c14e92d5a815ec2a611ad2de955edda2dd1ed269a815ec295a815ec2a651ad2de955edda2dd1ed269a815ec295a815ec2a611ad2de955edda2dd1ed269a815ec29468066c1ed91ed268a849a1e2dd1ed269a815ec295a811ec29a811ec2a951adda2dcdad269a811ec295a815ec29a815ec2a955edda2dd1ed269a815ec295a811ec29a811ec2a951adda209a9aa89a811ec295a811ec29a811ec2a951adda2dcdad269a811ec295a815ac29a815ac2a955edda2d91ed269a815ac2940c2595940c2595956cde92e2d8dad2680c25959542406e906dd62d269a459ec6a10e2d8ed6c15292d41c05691add5ed269a861d42a81e1ead95c15292541006e95ac962d168684a2c1e85a2ddad6c15292d42406e906d962d269a459ac6a85a2ddad6c15292d468066c1d55269241cc5ae4a6491a915da415ec695cc56e4a5cc56e4a664d6d2dd54e68e41cc56e4a55a415ec69a415ec6a855eddaedd1ed269a415ec695a411ec69a411ec6a851addae09a9aa89a411ec6940c26ad96855eddad6d268ed2d91ed2680c26ad9540c25959)))))
def cone12 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0x4e82555414e826655ed2dedd62d26a81a29dad5414e8256dd62d26add62d26a95a2dda2dd62d26a495ed15d55414e026655ed2ded562d26281a2ddad5414e02555414e826655ed2dedd62d26a81a2ddad5414e82555414e826615e92ded962926a81a2ddad5414e8255a4592c6a655ed2de95a2dda208e298a9a4592c6955414e82695a2dda2615ed15e81a2dda15414e82555414e826d962d2695414e82681a2ddad5414e82555414e826655ed2dedd62d26a81a2ddad5414e82555414e826655ed2dedd62d26a81a2ddad5414e82555414e826655ed2dedd62d269c09ee4a55414e8255a4592c6a655ed2de95a2dda208e298a9a4592c6955414e826655ed2dedd62d26a81a2ddad5414e82555414e826655ed2ded562c661c09ee4a55414e82555414e826d962d2695414e82681a2ddad5414e8255c49ee46608e298a9c49ee466d562d261c49ee46555414e826655ed2dedd62d26a81a2ddad5414e825554142826655ed2dedd62d26a81a2ddad541428255a4592c69c49ee465a4592c6a495ed15da4592c695a4592c69a4592c6a95a2dda2c962d169a4592c695c49ee465c49ee466655ed2ded562d261c49ee4655a4592c6a615e92de95a2dda2c9629169a4592c695a4592c6a655ed2de95a2dda2c962d169a4592c69554142826655ed2dedd62d26a81a2ddad54142825400000000a17800000005018000000000004f7400013b400000000000000027160000000000026c40000000133900004c4097392be00004a549361243243400008f891c80000467c000000022ec453400000002248000087d800021a442a400010800000415c8170000000040147ee000000003ecc7c5000000003d8479c00001e1e0000000000000003b9875e80001d2839ac7210000000038640000df00000000000000001b8e36780000d750000353000000000000348c000000019f400006688ca8000031fc62b0c2d00000000602000017b62ec85c4800000002d800000b37161c00005728abc152600000000a6a000029040000a18000027bc000000000000000000000000002718000000000002674000000012e800004a58000124423e446800000000229c000000000000000000000010fc21544160000100600003ed07b100001e203af80000000000039b000000000000386800000001b9000006bb00001a4800000000000000000006690000190030b80000bdc17142ce00000000000000005730a94148427c04cf00000000253047d08a80000000000000000000000000000000000000000000000000000000000000000000042b00000000000040200000f6400003b000000e1c1af0000066a0c3000002e300000ae8148800004d008fc0000000042c07b40e20000033605c80000149024003dc00000ce0000029403e0053000000a8000000000000004 else 0x82540c05595ac962d1685c492d9e81a2ddad5414e82540c05595858492d9c0c05595a81a2ddad5414d82540c05595ac962d1685849159e81a2ddad5414e82540c05595ac962d1685c492d9e81a2ddad5414e82540c05595ac962d1685c492d9e81a2ddad5414e82540c05595ac96251684c49058a95a2dda00c05595940c05595ac962d1685c492d9e81a2ddad5414e82540c05595ac962d1685849159e81a2ddad5414e82545c492d9ca88da1e1cc9ee4a6495ed15c5c492d9d45c492d9ed962d268a88da1e2c962d1685c492d9d40c04195ac96291685c492d9e81a2ddac0c0419594a88da1e2615ed2de08e298aad962d268a88da1e14a88da1e0a88da1e208e298aad562d261cc9ee4a54a88da1e0a88da1e208e298aad562d261cc9ee4a54a88da1e0a88da1e208e298aad562d261cc9ee4a54a88da1e0a88da1e208e298aad562d261cc9ee4a54a88da1e0a88da1e208e298aad562d261cc9ed0a54a88da1e0a88da1e208e298aad562d261cc9ee4a54a88da1e0a88da1e208e298aad562d261cc9ee4a54a88da1e0a88da1e208e298aad562d261cc9ee4a55cc9ee4a608e298a9cc9ee4a6d562d261cc9ee4a54a88da1e0a88da1e208e298aad562d261cc9ee4a54a88da1e0a88da1e208e298aad562d261cc9ea4a55c49ee46608e298a9c49ee466d562d261c49ee4654a88da1e0a88da1e208e298aad562d261cc9ee4a54a88da1e0a88da1e208e298aad562d260a88da1e15cc9da4a608e218a9cc9da4a6d562d261cc9da4a54a88da1e0a88da1e208e298aad562d261cc9ee4a54a88da1e0a88da1e208e298aad562d260a88da1e14a88da1e0a88da1e208e298aad562d261cc9ee4a54a88da1e0a88da1e208e298aad562d261cc9ee4a5608e298aa85a2ddaed562d260a88da1e208e298a94a88da1e0a88da1e208e298aad562d261cc9ee4a545c4a6d9e95a2dda0a88da1e05c4a6d9da459ec6955414e826655ed2dedd62d269cc9ee4a55414e82555414e824a88da1e2dd62d269cc9ed0a55414e82555414e82695a2dda2615ed15e81a2dda15414e82555414e824a88da1e2dd62d26a81a2ddad5414e8254a88da1e0a88da1e208e298a8a88da1e1cc9ee4a555414e826655ed2dedd62d26a81a2ddad5414e82555414e826655ed2dedd62d26a81a2ddad5414e82555414e826655ed2dedd62d269cc9de4a55414e8256c962516a85a2ddaec9625169a459ec6ac962516955414e826655ed2dedd62d26a81a2ddad5414e82555414e826655ed2ded562c661cc9ee4a55414e82555414e824a88da1e2dd62d26a81a2ddad5414e8254a88da1e0a88da1e208e298aad562d261cc9ee4a555414e826655ed2dedd62d26a81a2ddad5414e82555414e826655ed2dedd62d26a81a2ddad5414e82555414e826655ed2dedd62d26a81a2ddad541) else (if i < 3 then 0x94684a2c1edd62d269cc9ed0a6d962d269a859ac2940c05695add62d269a459ec69cc9ee4a55414e82555414e826655ed2ded562c661cc9ee4a55414e82555414e826655ed2ded562c661cc9ee4a55414e82555414e826615eceded562c661cc9ee0a55414e82555414e826655ed2ded562c661cc9ee4a55414e82555414e826655ed2ded562c661cc9ee4a55414e8254684a6c1ed562c661c49ee466655ed2dc684a6c1d55414e826655ed2ded562c661cc9ee4a55414e82555414e826655ed2ded562c661cc9ea4a55414e82555414e826655ed2ded562c661c09ee4655414e82555414e826655ed2ded562c661cc9ee4a55414e825554142826655ed2ded562c661c09ee4a5541428254684a6c1ca88da1e1cc9ee4a6655ed2dc684a6c1d554142826655ed2ded562c661c09ee4a55414282555414e825a859ec2add62d26a81a2ddad5414e82555414e825a859ec2add62d26a81a2ddad5414e82555414e825a859ec2add62c66a81a2ddad5414e82555414e825a859ec2add62d26a81a2ddad5414e82555414e825a859ec2ad962ce6a81a2d9ad5414e82555414e825a859ec2add62d26a81a2ddad5414e82555414e825a859ec2add62d26a81a2ddad5414e82555414e825a859d42add62d26a81a29dad5414e82555414e825a859ec2add62d26a81a2ddad5414e82555414e825a859ec2ad962926a81a2ddad5414e82555414e825a859ec2add62d26a81a2ddad5414e82555414e825a859ec2add62d26a81a2ddad5414e8254a88da1e0a88da1e208e298aad962d268a88da1e155414e825a859ec2add62d26a81a2ddad5414e82555414e825a859ec2ad962ce6a81a2d9ad5414e82555414e825a859ec2add62d26a81a2ddad5414e82555414e825a859ec2add62d26a81a2ddad5414e8256dd62d26ad962d26a08e298aad962d2695414e82555414e825a859ec2add62d26a81a2ddad5414e82555414e825a859ac2add62d26a81a2ddad5414e82555414e826d962d2695414e82681a2ddad5414e825554142825a859ec2add62d26a81a2ddad541428254a88da1e0a88da1e208e298aad962d268a88da1e15a859ec29a859ec2a95a2dda2d9629269a859ec295a859ec29a859ec2a95a2dda2dd62d269a859ec29554142825a859ac2add62d26a81a2ddad5414282540c05595ac962cd685c492d9e81a2d9ad5414e82540c05595ac962d1685c492d9e81a2ddad5414e82540c05595858492d9c0c0559584c492d895414e82540c05595ac96291685c492d9e81a2ddad5414e82540c05595a08e298a85c492d9ed562d2600c05595940c05595a08e298a85c492d9e81a2ddad5414e82540c05595ac962d1685c492d9e81a2ddad5414e82540c05595ac962d1685c492d9e81a2ddad5414e82540c05595a495ed15c5c492d9e81a2d9ad5414e else 0xc05695add62d269a859ec29cc9ed0a55414e82540c05695ad962d269a859ac29cc9ed0a55414e8255a859ec29a859ec2a95a2dda2dd62d269a859ec2))
def coneTable : Nat → Nat × Nat × (Nat → Nat)
  | 9 => (65,12,cone9)
  | 10 => (491,15,cone10)
  | 11 => (1662,17,cone11)
  | 12 => (282,15,cone12)
  | _ => (0,0,fun _ => 0)
def coneAt (k i : Nat) : List Nat :=
  let (n,ow,data) := coneTable k
  let st := n*ow+packedAt data (i*ow) ow
  let count := packedAt data st 4
  (List.range count).map (fun j => packedAt data (st+4+32*j) 32)

def projectionSpec (k i : Nat) : Nat × List SimpleGate × Nat :=
  let (cnt,ow,data) := projectionTable k
  let off := cnt*ow + packedAt data (i*ow) ow
  let tag := packedAt data off 6
  let m := packedAt data (off+6) 2
  let gates := (List.range m).map fun j =>
    let b := packedAt data (off+8+7*j) 7
    (b.testBit 6,b &&& 7,(b >>> 3) &&& 7)
  (tag,gates,packedAt data (off+8+7*m) 56)

def bankCheck (k i : Nat) :=
  let (tag,cs,idx) := projectionSpec k i
  if tag=0 then nodeVerifiedM mf k i else
    let ws := wideState mf k i
    (minorInputs[tag-1]?).any fun (m : MinorData) =>
      decide ws.Nodup && cutTest m.pm m.nm (vars m.q) cs idx k m.level ws

def checkProjection (k i : Nat) :=
  let w := tightAt k i
  if w=0 then
    let edges := coneAt k i
    if edges.isEmpty then bankCheck k i else coneTest (targetOf mf) k (wideState mf k i) edges
  else checkedTight (targetOf mf) k (wideState mf k i) (w-1)

def checkRange (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => checkProjection k (start+n) && checkRange k start n

def upward (s : Row) : List Sig → Sig
  | [] => one
  | a::as => if bit s a then bin false a (upward s as) else upward s as
def downward (s : Row) : List Sig → Sig
  | [] => one
  | a::as => if bit s a then downward s as else bin false (neg a) (downward s as)

theorem upward_bit (r s : Row) (raw : List Sig) : bit r (upward s raw) = sampleLe raw s r := by
  induction raw with
  | nil => simp [sampleLe,upward,bit_one]
  | cons a as ih =>
    cases e : bit s a <;> simp [sampleLe,upward,e,bit_bin,ih]

theorem downward_bit (r s : Row) (raw : List Sig) : bit r (downward s raw) = sampleLe raw r s := by
  induction raw with
  | nil => simp [sampleLe,downward,bit_one]
  | cons a as ih =>
    cases e : bit s a <;> simp [sampleLe,downward,e,bit_bin,bit_neg,ih]

def family (value : Row → Sig) : List Row → Sig
  | [] => zero
  | r::rs => bin true (value r) (family value rs)
theorem family_bit (r : Row) (f : Row → Sig) (ss : List Row) :
    bit r (family f ss) = ss.any (fun u => bit r (f u)) := by
  induction ss with
  | nil => simp [family,bit_zero]
  | cons a as ih => simp [family,bit_bin,ih]

def compactGeometry (raw : List Sig) (p n : List Row) (goal sub : Sig) :=
  p.all (fun r => bit r goal) && n.all (fun r => !bit r goal) &&
  (bin false sub (family (fun s => upward s raw) p) == sub) &&
  (bin false (neg sub) (family (fun s => downward s raw) n) == neg sub)

theorem compactGeometry_ok {raw p n goal sub} (h : compactGeometry raw p n goal sub = true) :
    extremalGeometry raw p n goal sub = true := by
  simp only [compactGeometry,Bool.and_eq_true,beq_iff_eq] at h
  simp only [extremalGeometry,Bool.and_eq_true,List.all_eq_true]
  refine ⟨⟨List.all_eq_true.mp h.1.1.1,List.all_eq_true.mp h.1.1.2⟩,?_⟩
  intro r hr
  cases e : bit r sub
  · have eq := congrArg (bit r) h.2
    simpa only [e,Bool.false_eq_true,if_false,bit_bin,bit_neg,Bool.not_false,Bool.true_and,
      family_bit,downward_bit] using eq
  · have eq := congrArg (bit r) h.1.2
    simpa only [e,if_true,bit_bin,Bool.false_eq_true,if_false,Bool.true_and,
      family_bit,upward_bit] using eq

def geometryOK (m : MinorData) (level : Nat → Nat) :=
  properB (graphGoal m.q) && !(m.q.testBit 9) && decide (m.level = level m.q) &&
  m.pos.all (fun r => bit r m.pm) && m.neg.all (fun r => bit r m.nm) &&
  compactGeometry (vars m.q) m.pos m.neg graph (graphGoal m.q)
theorem checkRange_at {k start n} (h : checkRange k start n=true) (j : Nat)
    (lo : start≤j) (hi : j<start+n) : checkProjection k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [checkRange,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)

theorem checkRange_merge {k start a b} (h : checkRange k start a=true)
    (h' : checkRange k (start+a) b=true) : checkRange k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [checkRange,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,checkRange,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allMinorGeometry :
    (minorInputs.toList.all fun m => geometryOK m (boundsBefore known383)) = true := by decide +kernel

theorem bankCheck_sound {k i}
    (earlier : k>0 → ∀ j<(mf.levels (k-1)).1, ImpossibleM (targetOf mf) (k-1) (wideState mf (k-1) j).toFinset)
    (h : bankCheck k i = true) : ImpossibleM (targetOf mf) k (wideState mf k i).toFinset := by
  have valid := mfValid
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at valid
  unfold bankCheck at h
  rcases pp : projectionSpec k i with ⟨tag,cs,idx⟩
  simp only [pp] at h
  split at h
  · exact nodeVerified_soundM mf _ _ (chart_pairs valid.1.1.1 valid.1.1.2)
      (fun v hv => col_sound _ _ (before_sound known383 valid383) (valid.1.2 v hv)) valid.2 earlier
      h
  · cases found : minorInputs[tag-1]? with
    | none => simp [found] at h
    | some m =>
      simp only [found,Option.any_some,Bool.and_eq_true,decide_eq_true_eq] at h
      have mem : m ∈ minorInputs.toList := by
        apply List.mem_of_getElem? (i:=tag-1)
        simpa using found
      have geom := List.all_eq_true.mp allMinorGeometry m mem
      simp only [geometryOK,Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq,List.all_eq_true] at geom
      have lower := before_sound known383 valid383 m.q
      simp only [varsX,geom.1.1.1.1.2,Bool.false_eq_true,if_false,←geom.1.1.1.2] at lower
      have target : targetOf mf = graph := by decide +kernel
      rw [target]
      exact cutTest_sound (compactGeometry_ok geom.2) (proper_of _ geom.1.1.1.1.1) lower geom.1.1.2 geom.1.2 h.1 h.2

theorem projected_sound {k i}
    (earlier : k>0 → ∀ j<(mf.levels (k-1)).1, ImpossibleM (targetOf mf) (k-1) (wideState mf (k-1) j).toFinset)
    (h : checkProjection k i = true) : ImpossibleM (targetOf mf) k (wideState mf k i).toFinset := by
  by_cases ht : tightAt k i = 0
  · by_cases he : (coneAt k i).isEmpty = true
    · have hb : bankCheck k i = true := by
        simpa only [checkProjection,if_pos ht,if_pos he] using h
      exact bankCheck_sound earlier hb
    · have hc : coneTest (targetOf mf) k (wideState mf k i) (coneAt k i) = true := by
        simpa only [checkProjection,if_pos ht,if_neg he] using h
      exact coneTest_sound hc
  · have hc : checkedTight (targetOf mf) k (wideState mf k i) (tightAt k i-1) = true := by
      simpa only [checkProjection,if_neg ht] using h
    exact tightTest_sound hc

def projectedTables (top : Nat) := ∀ k ≤ top, checkRange k 0 (mf.levels k).1 = true

theorem projected_tree (top : Nat) (rows : projectedTables top) :
    ∀ k ≤ top, ∀ i < (mf.levels k).1, ImpossibleM (targetOf mf) k (wideState mf k i).toFinset := by
  intro k
  induction k with
  | zero =>
    intro hk i hi
    exact projected_sound (by omega) (checkRange_at (rows _ hk) i (by omega) (by omega))
  | succ k ih =>
    intro hk i hi
    exact projected_sound (fun _ => by simpa using ih (by omega))
      (checkRange_at (rows _ hk) i (by omega) (by omega))
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof5_0 : checkRange 5 0 1 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof6_0 : checkRange 6 0 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof7_0 : checkRange 7 0 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof8_0 : checkRange 8 0 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof9_0 : checkRange 9 0 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof9_48 : checkRange 9 48 17 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof10_0 : checkRange 10 0 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof10_48 : checkRange 10 48 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof10_96 : checkRange 10 96 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof10_144 : checkRange 10 144 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof10_192 : checkRange 10 192 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof10_240 : checkRange 10 240 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof10_288 : checkRange 10 288 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof10_336 : checkRange 10 336 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof10_384 : checkRange 10 384 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof10_432 : checkRange 10 432 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof10_480 : checkRange 10 480 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof11_0 : checkRange 11 0 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof11_48 : checkRange 11 48 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof11_96 : checkRange 11 96 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof11_144 : checkRange 11 144 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof11_192 : checkRange 11 192 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof11_240 : checkRange 11 240 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof11_288 : checkRange 11 288 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof11_336 : checkRange 11 336 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof11_384 : checkRange 11 384 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof11_432 : checkRange 11 432 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof11_480 : checkRange 11 480 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof11_528 : checkRange 11 528 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof11_576 : checkRange 11 576 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof11_624 : checkRange 11 624 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof11_672 : checkRange 11 672 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof11_720 : checkRange 11 720 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof11_768 : checkRange 11 768 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof11_816 : checkRange 11 816 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof11_864 : checkRange 11 864 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof11_912 : checkRange 11 912 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof11_960 : checkRange 11 960 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof11_1008 : checkRange 11 1008 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof11_1056 : checkRange 11 1056 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof11_1104 : checkRange 11 1104 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof11_1152 : checkRange 11 1152 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof11_1200 : checkRange 11 1200 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof11_1248 : checkRange 11 1248 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof11_1296 : checkRange 11 1296 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof11_1344 : checkRange 11 1344 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof11_1392 : checkRange 11 1392 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof11_1440 : checkRange 11 1440 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof11_1488 : checkRange 11 1488 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof11_1536 : checkRange 11 1536 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof11_1584 : checkRange 11 1584 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof11_1632 : checkRange 11 1632 30 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof12_0 : checkRange 12 0 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof12_48 : checkRange 12 48 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof12_96 : checkRange 12 96 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof12_144 : checkRange 12 144 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof12_192 : checkRange 12 192 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof12_240 : checkRange 12 240 42 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem proof13_0 : checkRange 13 0 15 = true := by decide +kernel
theorem allBlocks : projectedTables 13 := by
  intro k hk
  interval_cases k
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact proof5_0
  · exact proof6_0
  · exact proof7_0
  · exact proof8_0
  · exact (@checkRange_merge 9 0 48 17 proof9_0 proof9_48)
  · exact (@checkRange_merge 10 0 384 107 (@checkRange_merge 10 0 192 192 (@checkRange_merge 10 0 96 96 (@checkRange_merge 10 0 48 48 proof10_0 proof10_48) (@checkRange_merge 10 96 48 48 proof10_96 proof10_144)) (@checkRange_merge 10 192 96 96 (@checkRange_merge 10 192 48 48 proof10_192 proof10_240) (@checkRange_merge 10 288 48 48 proof10_288 proof10_336))) (@checkRange_merge 10 384 96 11 (@checkRange_merge 10 384 48 48 proof10_384 proof10_432) proof10_480))
  · exact (@checkRange_merge 11 0 1536 126 (@checkRange_merge 11 0 768 768 (@checkRange_merge 11 0 384 384 (@checkRange_merge 11 0 192 192 (@checkRange_merge 11 0 96 96 (@checkRange_merge 11 0 48 48 proof11_0 proof11_48) (@checkRange_merge 11 96 48 48 proof11_96 proof11_144)) (@checkRange_merge 11 192 96 96 (@checkRange_merge 11 192 48 48 proof11_192 proof11_240) (@checkRange_merge 11 288 48 48 proof11_288 proof11_336))) (@checkRange_merge 11 384 192 192 (@checkRange_merge 11 384 96 96 (@checkRange_merge 11 384 48 48 proof11_384 proof11_432) (@checkRange_merge 11 480 48 48 proof11_480 proof11_528)) (@checkRange_merge 11 576 96 96 (@checkRange_merge 11 576 48 48 proof11_576 proof11_624) (@checkRange_merge 11 672 48 48 proof11_672 proof11_720)))) (@checkRange_merge 11 768 384 384 (@checkRange_merge 11 768 192 192 (@checkRange_merge 11 768 96 96 (@checkRange_merge 11 768 48 48 proof11_768 proof11_816) (@checkRange_merge 11 864 48 48 proof11_864 proof11_912)) (@checkRange_merge 11 960 96 96 (@checkRange_merge 11 960 48 48 proof11_960 proof11_1008) (@checkRange_merge 11 1056 48 48 proof11_1056 proof11_1104))) (@checkRange_merge 11 1152 192 192 (@checkRange_merge 11 1152 96 96 (@checkRange_merge 11 1152 48 48 proof11_1152 proof11_1200) (@checkRange_merge 11 1248 48 48 proof11_1248 proof11_1296)) (@checkRange_merge 11 1344 96 96 (@checkRange_merge 11 1344 48 48 proof11_1344 proof11_1392) (@checkRange_merge 11 1440 48 48 proof11_1440 proof11_1488))))) (@checkRange_merge 11 1536 96 30 (@checkRange_merge 11 1536 48 48 proof11_1536 proof11_1584) proof11_1632))
  · exact (@checkRange_merge 12 0 192 90 (@checkRange_merge 12 0 96 96 (@checkRange_merge 12 0 48 48 proof12_0 proof12_48) (@checkRange_merge 12 96 48 48 proof12_96 proof12_144)) (@checkRange_merge 12 192 48 42 proof12_192 proof12_240))
  · exact proof13_0
def findRoot (a b : Fin 9) (u v : Bool) :=
  let w := activeRoots a b u v
  (mf.index 14 (keySet w)).bind (wideLinks mf 13)

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem rootsClosed (a b : Fin 9) (ab : legalPair a b) (u v : Bool) :
    ImpossibleM graph 13 (activeRoots a b u v).toFinset := by
  have checked : ∀ a b : Fin 9, legalPair a b → ∀ u v : Bool,
      ((findRoot a b u v).toList.any (sameWords (activeRoots a b u v))) = true := by
    unfold legalPair
    decide +kernel
  obtain ⟨w,hw,eq⟩ := List.any_eq_true.mp (checked _ _ ab u v)
  have key : (mf.index 14 (keySet (activeRoots a b u v))).bind (wideLinks mf 13) = some w := by
    simpa [findRoot] using hw
  obtain ⟨pair,_,link⟩ := Option.bind_eq_some_iff.mp key
  have geom := mfValid
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geom
  have imp := linkedSet_soundM mf 13 geom.2
    (projected_tree 13 allBlocks 13 (by decide)) link
  have target : targetOf mf = graph := by decide +kernel
  rwa [target,←sameWords_sound eq] at imp
theorem quantitative (C : Circuit) (mono : PEqualNP.MetaComplexity.Monotone2 C)
    (hsize : C.gates.length = 14)
    (head : ∃ g gs, C.gates = g::gs ∧ g.op = GateOp.or ∧
      0 ∉ g.inputs ∧ 3 ∉ g.inputs ∧ 9 ∉ g.inputs)
    (spec : ∀ x : Fin 9 → Bool, C.eval (givenPins x) = edgeValue x)
    (topProof : ∀ a b : Fin 9, legalPair a b →
      ∀ u v : Bool, ImpossibleM graph 13 (activeRoots a b u v).toFinset) : False := by
  obtain ⟨g,gs,head,op,h0,h3,h9⟩ := head
  have good : ∀ u ∈ C.gates, u.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) := by
    intro u hu
    rcases (by simpa using (mono u hu).1 : u.op=GateOp.and ∨ u.op=GateOp.or) with h | h <;> simp [h]
  have eq : (execute C.gates (inputs ++ [extra])).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro n hn
    let r : Row := ⟨n,hn⟩
    change bit r ((execute C.gates (inputs ++ [extra])).getD C.output zero) = bit r graph
    have pin : (inputs ++ [extra]).map (bit r) = givenPins (sample r) := by
      rw [givenPins,sampled]
      simp [extra,orValue,primary,bit_bin,sample]
    rw [←b_read,execute_bits _ _ _ good,pin,edge_table]
    exact spec (sample r)
  have ho := get_rep (execute C.gates (inputs ++ [extra])) C.output
  rw [eq] at ho
  obtain ⟨k,S,hk,run,sub⟩ := extractM gs ((inputs ++ [extra]) ++ [headValue g])
    (fun u hu => mono u (by rw [head]; exact List.mem_cons_of_mem _ hu)) graph_proper
    (by have mem := ho.resolve_right (fun f => f graph_proper); rw [head] at mem; exact mem)
  have cap : k ≤ 13 := by
    rw [head,List.length_cons] at hsize
    omega
  have exclude (a b : Fin 9) (ab : legalPair a b) (src : ∀ w ∈ S, w ∈ signedRoots a b) : False := by
    obtain ⟨u,v,eqS⟩ := active_roots ab run src
    exact topProof a b ab u v k 0 cap rfl (eqS ▸ run)
  have drop (h : headValue g = zero ∨ headValue g ∈ inputs) : False := by
    apply exclude 1 2 (by unfold legalPair; decide)
    intro w hw
    have src := sub w hw
    simp only [List.mem_append,List.mem_singleton] at src
    simp only [signedRoots,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    rcases src with (prim | hx) | hg
    · exact Or.inl prim
    · exact Or.inr (Or.inl hx)
    · rcases h with hz | hr
      · exact False.elim ((live_proper run w hw).1 (hg.trans hz))
      · exact Or.inl (hg.symm ▸ hr)
  have inG : g ∈ C.gates := by rw [head]; exact List.mem_cons_self
  rcases firstShape g op (mono g inG).2 h0 h3 h9 with reject | raw | ⟨a,b,ab,hval⟩
  · exact drop (Or.inl reject)
  · exact drop (Or.inr raw)
  · have source : ∀ w ∈ S, w ∈ signedRoots a b := by
      intro w hw
      simpa only [signedRoots,hval,List.append_assoc,List.cons_append,List.nil_append] using sub w hw
    exact exclude a b ab source
end PEqualNP.Outside.L_meta_5002

open PEqualNP.Outside.L_meta_5002

theorem PEqualNP.Outside.L_meta_5002 : have x1 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) => (∃ x2 ∈ [(3 : ℕ), (12 : ℕ), (24 : ℕ), (17 : ℕ), (33 : ℕ), (264 : ℕ)], x1.eval ((List.ofFn fun (x3 : Fin (9 : ℕ)) => x2.testBit ↑x3) ++ [Bool.false]) = Bool.false) ∧ ∃ x2 ∈ [(50 : ℕ), (116 : ℕ), (208 : ℕ), (276 : ℕ), (402 : ℕ)], x1.eval ((List.ofFn fun (x3 : Fin (9 : ℕ)) => x2.testBit ↑x3) ++ [Bool.true]) = Bool.true; have x2 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Bool := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ) => x2.eval ((List.ofFn fun (x4 : Fin (9 : ℕ)) => x3.testBit ↑x4) ++ [x3.testBit (0 : ℕ) || x3.testBit (3 : ℕ)]); ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), x3.gates.length = (14 : ℕ) → PEqualNP.MetaComplexity.Monotone2 x3 → x3.output = (23 : ℕ) → x1 x3 → (∃ (x8 : PEqualNP.CircuitLowerBounds.Gate) (x9 : List PEqualNP.CircuitLowerBounds.Gate), x3.gates = x8 :: x9 ∧ x8.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (0 : ℕ) ∉ x8.inputs ∧ (3 : ℕ) ∉ x8.inputs ∧ (9 : ℕ) ∉ x8.inputs) → (∀ x9 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (24 : ℕ), (17 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (264 : ℕ), (160 : ℕ), (320 : ℕ), (288 : ℕ)], x2 x3 x9 = Bool.true) → ¬∀ x10 ∈ [(42 : ℕ), (50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ)], x2 x3 x10 = Bool.false := by
  intro _ eval C n mono _ _ head yes no
  exact quantitative C mono n head (boundary C mono yes no) rootsClosed
