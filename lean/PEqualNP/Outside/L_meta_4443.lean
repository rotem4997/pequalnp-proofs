import Mathlib
import PEqualNP.Defs

-- First gate OR(x4, x6) of a circuit for the Petersen-minus-vertex edge function forces 16 gates.
-- The checker and the plain bound certificates are those of the merged L_meta_1667 family (PR 4332, Apache-2.0);
-- the seeded column variant (varsX, rawMask, strong_low) follows the open submission 7298 for OR(x4, x6).
-- The seeded ladder and the forest named live were produced by an independent search.
namespace PEqualNP.Outside.L_meta_4443
open PEqualNP.CircuitLowerBounds
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
def seed : Sig := inputs.getD 4 zero ||| inputs.getD 6 zero

def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem seed_table : ∀ r : Row, bit r seed = (sample r 4 || sample r 6) := by decide +kernel
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

theorem initial_live (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (first : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 || y 6))
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) (small : C.size ≤ 15) :
    ∃ k t S, k ≤ 14 ∧ Live graph k t S ∧ ∀ a ∈ S, a ∈ inputs++[seed] := by
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
    exact ⟨k,t,S,by omega,run,hs⟩


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
theorem valid383 : Known known383 := extendKnown_ok (m:=383) valid255 low383 (by decide +kernel)
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
def deadcolumns : List ColumnInfo := [(1,0,510,0,12),(0,1,460,50,8),(2,0,509,0,12),(0,2,440,69,8),(3,0,508,0,9),(2,1,460,48,7),(4,0,507,0,12),(0,4,369,138,8),(5,0,506,0,8),(6,0,505,0,9),(4,2,440,65,7),(2,4,369,136,7),(7,0,504,0,7),(5,2,440,64,6),(8,0,503,0,12),(0,8,227,276,8),(9,0,486,0,8),(10,0,501,0,8),(12,0,499,0,9),(8,4,369,130,7),(4,8,227,272,7),(14,0,497,0,7),(10,4,369,128,6),(15,0,480,0,4),(16,0,495,0,13),(0,16,486,9,10),(17,0,494,0,11),(16,1,460,34,7),(19,0,492,0,8),(16,4,353,138,7),(21,0,490,0,7),(21,2,424,64,5),(24,0,487,0,11),(8,16,486,1,9),(25,0,486,0,8),(9,16,486,0,8),(27,0,484,0,5),(11,16,484,0,5),(24,4,353,130,6),(29,0,482,0,5),(26,4,353,128,5),(32,0,479,0,12),(0,32,94,385,8),(32,1,460,18,7),(1,32,94,384,7),(35,0,476,0,7),(34,1,460,16,6),(36,0,347,0,8),(39,0,344,0,4),(40,0,471,0,8),(49,0,462,0,8),(48,1,460,2,6),(50,1,460,0,5),(56,0,455,0,7),(64,0,447,0,13),(0,64,189,258,10),(66,0,445,0,11),(2,64,189,256,9),(67,0,444,0,8),(66,1,396,48,6),(70,0,441,0,8),(69,2,440,0,5),(74,0,437,0,7),(74,4,305,128,5),(80,0,431,0,11),(83,0,428,0,7),(96,0,415,0,9),(96,1,396,18,6),(98,1,396,16,5),(128,0,383,0,13),(128,1,332,50,7),(3,128,344,36,6),(132,0,379,0,11),(4,128,347,32,9),(133,0,378,0,7),(134,0,377,0,8),(132,2,312,65,6),(133,2,312,64,5),(136,0,375,0,9),(128,8,99,276,7),(140,0,371,0,8),(132,8,99,272,6),(138,4,369,0,5),(144,0,367,0,11),(152,4,353,2,5),(160,0,351,0,11),(160,1,332,18,6),(162,1,332,16,5),(164,0,347,0,8),(36,128,347,0,8),(172,0,339,0,5),(176,1,332,2,5),(180,0,331,0,5),(192,0,319,0,11),(198,0,313,0,7),(256,0,255,0,12),(258,0,189,0,8),(260,0,251,0,8),(264,0,247,0,9),(256,8,227,20,7),(8,256,151,96,7),(268,0,243,0,7),(260,8,227,16,6),(273,0,238,0,7),(280,0,231,0,8),(276,8,227,0,5),(288,0,223,0,9),(256,32,94,129,7),(32,256,151,72,7),(257,32,94,128,6),(296,0,215,0,7),(40,256,151,64,6),(304,0,207,0,6),(288,16,198,9,6),(273,32,78,128,5),(56,256,135,64,5),(320,0,191,0,11),(256,64,189,2,9),(322,0,189,0,8),(258,64,189,0,8),(324,0,187,0,7),(324,8,163,16,5),(321,32,30,128,5),(388,8,99,16,5),(168,256,23,64,5),(224,256,23,8,5)]
def deadautos : List (List Nat) := [[],[118,130,81],[100,131,82,16],[118,133,100,131,50,33,16],[116,83,32],[118,116,83,130,49,32],[118,133,33,48],[82,129,48],[118,133,116,83,82,81,80],[116,50,129,80],[100,49,128],[118,100,83,130,81,128]]
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
theorem slice_self {raw : List Sig} {T : Sig} {L : Nat} (pT : proper T) (h : Lower raw T L) :
    Slice raw T one L := by
  refine ⟨id,raw,fun r => bit_one r,fun a ha => ?_,observe_proper pT,h⟩
  exact Or.inl (List.mem_map_of_mem ha)

theorem plainA {m q cap : Nat} {prior : Nat → Nat} (low : ∀ q, Lower (varsX q) (graphGoal q) (prior q))
    (e : (graphGoal q == graphGoal m && (varsX q == vars m) && (prior q == cap+1) && properB (graphGoal m) &&
      decide (vars m).Nodup && poolCut one (cap+1) cap 0 (vars m) (vars m)) = true) :
    Impossible (graphGoal m) cap (vars m).toFinset := by
  simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at e
  obtain ⟨⟨⟨⟨⟨e1,e2⟩,e3⟩,e4⟩,e5⟩,e6⟩ := e
  have h := low q
  rw [e1,e2,e3] at h
  exact poolCut_sound (slice_self (proper_of _ e4) h) [] rfl e5 e6

def rootB (m : Nat) : List Sig := vars m ++ [seed]
theorem cut_root {m cap : Nat} {prior : Nat → Nat} {ws : List Sig}
    (low : ∀ q, Lower (varsX q) (graphGoal q) (prior q)) (ci : ColumnInfo)
    (ok : colCheck m ci prior = true)
    (cut : (decide ws.Nodup && poolCut (subcube ci.1 ci.2.1) ci.2.2.2.2 cap 0 (varsX (rawMask m ci)) ws)=true) :
    Impossible (graphGoal m) cap ws.toFinset := by
  simp only [Bool.and_eq_true,decide_eq_true_eq] at cut
  exact poolCut_sound (col_sound ci prior low ok) [] rfl cut.1 cut.2

theorem index_root {g : Forest} {m cap i : Nat} {prior : Nat → Nat} {ws : List Sig}
    (hm : g.mask=m) (low : ∀ q, Lower (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g cap)
    (idx : indexedRoot g cap i ws = true) : Impossible (graphGoal m) cap ws.toFinset := by
  subst hm
  exact root_index low geom blocks (Nat.le_refl _) idx

def pairsX (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := (1 <<< ((hints >>> (4*i)) &&& 15)) ||| (if i=4 then 64 else if i=6 then 16 else 0)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def splitOK (m hints : Nat) : Bool :=
  checkEssential (graphGoal m) (rootB m) (pairsX m hints) &&
    ((pairsX m hints).map Prod.fst == vars m) && properB (graphGoal m)

theorem strong_split {m hints : Nat} (ok : splitOK m hints = true) {k t : Nat} {S : Finset Sig}
    (h : Live (graphGoal m) k t S) (sub : ∀ v ∈ S, v ∈ rootB m) :
    S=(vars m).toFinset ∨ S=(rootB m).toFinset := by
  simp only [splitOK,Bool.and_eq_true,beq_iff_eq] at ok
  obtain ⟨⟨ess,alls⟩,_⟩ := ok
  have rest : ∀ v ∈ vars m, v ∈ S := by
    intro v hv
    rw [←alls] at hv
    obtain ⟨r,s,hd,hi⟩ := essential_ok ess v (List.mem_toFinset.mpr hv)
    exact raw_required h (rootB m) v sub r s hd hi
  have mem : ∀ v, v ∈ rootB m ↔ v ∈ vars m ∨ v=seed := by
    intro v
    simp [rootB]
  by_cases hs : seed ∈ S
  · refine Or.inr ?_
    ext v
    rw [List.mem_toFinset]
    refine ⟨sub v,fun hv => ?_⟩
    rcases (mem v).mp hv with hv | rfl
    · exact rest v hv
    · exact hs
  · refine Or.inl ?_
    ext v
    rw [List.mem_toFinset]
    refine ⟨fun hv => ?_,rest v⟩
    rcases (mem v).mp (sub v hv) with hv | rfl
    · exact hv
    · exact False.elim (hs hv)

theorem strong_low {m hints cap : Nat} (ok : splitOK m hints = true)
    (a : Impossible (graphGoal m) cap (vars m).toFinset)
    (b : Impossible (graphGoal m) cap (rootB m).toFinset) :
    Lower (rootB m) (graphGoal m) (cap+1) := by
  have ok' := ok
  simp only [splitOK,Bool.and_eq_true,beq_iff_eq] at ok'
  intro p bank hr ha
  obtain ⟨k,t,S,hk,run,hs⟩ := reach_live (proper_of _ ok'.2) hr ha
  by_contra! small
  rcases strong_split ok run hs with e | e
  · exact a k t (by omega) (e ▸ run)
  · exact b k t (by omega) (e ▸ run)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low511 : Lower (vars 511) (graphGoal 511) 15 :=
  lower_forest (g:=dead) (i:=0) (hints:=13438558465) (before_sound known383 valid383) geomdead tablesdead (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps511 : List (Nat × List Nat) := [(511,[])]
def known511 := extendKnown known383 15 maps511
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid511 : Known known511 := extendKnown_ok (m:=511) valid383 low511 (by decide +kernel)
theorem plainB {m q cap : Nat} {prior : Nat → Nat} (low : ∀ q, Lower (varsX q) (graphGoal q) (prior q))
    (e : (graphGoal q == graphGoal m && (varsX q == vars m) && decide (cap+1 ≤ prior q) && properB (graphGoal m) &&
      decide (vars m).Nodup && poolCut one (cap+1) cap 0 (vars m) (vars m)) = true) :
    Impossible (graphGoal m) cap (vars m).toFinset := by
  simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at e
  obtain ⟨⟨⟨⟨⟨e1,e2⟩,e3⟩,e4⟩,e5⟩,e6⟩ := e
  have h := low q
  rw [e1,e2] at h
  have h' : Lower (vars m) (graphGoal m) (cap+1) := fun p bank hr ha => le_trans e3 (h p bank hr ha)
  exact poolCut_sound (slice_self (proper_of _ e4) h') [] rfl e5 e6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx344 : Lower (varsX 856) (graphGoal 856) 4 :=
  strong_low (m:=856) (cap:=3) (hints:=13019332608) (by decide +kernel) (plainB (q:=344) (prior:=boundsBefore known511) (before_sound known511 valid511) (by decide +kernel))
    (cut_root (prior:=boundsBefore known511) (before_sound known511 valid511) (512,272,0,72,1) (by decide +kernel) (by decide +kernel))
def mapsx344 : List (Nat × List Nat) := [(856,[])]
def knownx344 := extendKnown known511 4 mapsx344
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx344 : Known knownx344 := extendKnown_ok (m:=856) valid511 lowx344 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx94 : Lower (varsX 606) (graphGoal 606) 5 :=
  strong_low (m:=606) (cap:=4) (hints:=16982304) (by decide +kernel) (plainB (q:=94) (prior:=boundsBefore knownx344) (before_sound knownx344 validx344) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx344) (before_sound knownx344 validx344) (576,0,30,0,4) (by decide +kernel) (by decide +kernel))
def mapsx94 : List (Nat × List Nat) := [(606,[])]
def knownx94 := extendKnown knownx344 5 mapsx94
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx94 : Known knownx94 := extendKnown_ok (m:=606) validx344 lowx94 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx115 : Lower (varsX 627) (graphGoal 627) 5 :=
  strong_low (m:=627) (cap:=4) (hints:=16777217) (by decide +kernel) (plainB (q:=115) (prior:=boundsBefore knownx94) (before_sound knownx94 validx94) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx94) (before_sound knownx94 validx94) (528,0,99,0,4) (by decide +kernel) (by decide +kernel))
def mapsx115 : List (Nat × List Nat) := [(627,[])]
def knownx115 := extendKnown knownx94 5 mapsx115
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx115 : Known knownx115 := extendKnown_ok (m:=627) validx94 lowx115 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx339 : Lower (varsX 851) (graphGoal 851) 5 :=
  strong_low (m:=851) (cap:=4) (hints:=25786580993) (by decide +kernel) (plainB (q:=339) (prior:=boundsBefore knownx115) (before_sound knownx115 validx115) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx115) (before_sound knownx115 validx115) (512,80,0,259,2) (by decide +kernel) (by decide +kernel))
def mapsx339 : List (Nat × List Nat) := [(851,[])]
def knownx339 := extendKnown knownx115 5 mapsx339
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx339 : Known knownx339 := extendKnown_ok (m:=851) validx115 lowx339 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx345 : Lower (varsX 857) (graphGoal 857) 5 :=
  strong_low (m:=857) (cap:=4) (hints:=13019136004) (by decide +kernel) (plainB (q:=345) (prior:=boundsBefore knownx339) (before_sound knownx339 validx339) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx339) (before_sound knownx339 validx339) (576,0,281,0,4) (by decide +kernel) (by decide +kernel))
def mapsx345 : List (Nat × List Nat) := [(857,[])]
def knownx345 := extendKnown knownx339 5 mapsx345
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx345 : Known knownx345 := extendKnown_ok (m:=857) validx339 lowx345 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx346 : Lower (varsX 858) (graphGoal 858) 5 :=
  strong_low (m:=858) (cap:=4) (hints:=12901892192) (by decide +kernel) (plainB (q:=346) (prior:=boundsBefore knownx345) (before_sound knownx345 validx345) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx345) (before_sound knownx345 validx345) (528,0,330,0,4) (by decide +kernel) (by decide +kernel))
def mapsx346 : List (Nat × List Nat) := [(858,[])]
def knownx346 := extendKnown knownx345 5 mapsx346
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx346 : Known knownx346 := extendKnown_ok (m:=858) validx345 lowx346 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx348 : Lower (varsX 860) (graphGoal 860) 5 :=
  strong_low (m:=860) (cap:=4) (hints:=13019325184) (by decide +kernel) (plainB (q:=348) (prior:=boundsBefore knownx346) (before_sound knownx346 validx346) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx346) (before_sound knownx346 validx346) (528,0,332,0,4) (by decide +kernel) (by decide +kernel))
def mapsx348 : List (Nat × List Nat) := [(860,[])]
def knownx348 := extendKnown knownx346 5 mapsx348
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx348 : Known knownx348 := extendKnown_ok (m:=860) validx346 lowx348 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx369 : Lower (varsX 881) (graphGoal 881) 5 :=
  strong_low (m:=881) (cap:=4) (hints:=21609054212) (by decide +kernel) (plainB (q:=369) (prior:=boundsBefore knownx348) (before_sound knownx348 validx348) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx348) (before_sound knownx348 validx348) (576,0,305,0,4) (by decide +kernel) (by decide +kernel))
def mapsx369 : List (Nat × List Nat) := [(881,[])]
def knownx369 := extendKnown knownx348 5 mapsx369
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx369 : Known knownx369 := extendKnown_ok (m:=881) validx348 lowx369 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx376 : Lower (varsX 888) (graphGoal 888) 5 :=
  strong_low (m:=888) (cap:=4) (hints:=13027721216) (by decide +kernel) (plainB (q:=376) (prior:=boundsBefore knownx369) (before_sound knownx369 validx369) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx369) (before_sound knownx369 validx369) (576,0,312,0,4) (by decide +kernel) (by decide +kernel))
def mapsx376 : List (Nat × List Nat) := [(888,[])]
def knownx376 := extendKnown knownx369 5 mapsx376
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx376 : Known knownx376 := extendKnown_ok (m:=888) validx369 lowx376 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx95 : Lower (varsX 607) (graphGoal 607) 8 :=
  strong_low (m:=607) (cap:=7) (hints:=16785665) (by decide +kernel) (plainB (q:=95) (prior:=boundsBefore knownx376) (before_sound knownx376 validx376) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx376) (before_sound knownx376 validx376) (576,0,31,0,7) (by decide +kernel) (by decide +kernel))
def mapsx95 : List (Nat × List Nat) := [(607,[])]
def knownx95 := extendKnown knownx376 8 mapsx95
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx95 : Known knownx95 := extendKnown_ok (m:=607) validx376 lowx95 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx215 : Lower (varsX 727) (graphGoal 727) 7 :=
  strong_low (m:=727) (cap:=6) (hints:=553648385) (by decide +kernel) (plainB (q:=215) (prior:=boundsBefore knownx95) (before_sound knownx95 validx95) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx95) (before_sound knownx95 validx95) (512,16,198,1,5) (by decide +kernel) (by decide +kernel))
def mapsx215 : List (Nat × List Nat) := [(727,[])]
def knownx215 := extendKnown knownx95 7 mapsx215
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx215 : Known knownx215 := extendKnown_ok (m:=727) validx95 lowx215 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx222 : Lower (varsX 734) (graphGoal 734) 7 :=
  strong_low (m:=734) (cap:=6) (hints:=553853216) (by decide +kernel) (plainB (q:=222) (prior:=boundsBefore knownx215) (before_sound knownx215 validx215) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx215) (before_sound knownx215 validx215) (512,64,156,2,5) (by decide +kernel) (by decide +kernel))
def mapsx222 : List (Nat × List Nat) := [(734,[])]
def knownx222 := extendKnown knownx215 7 mapsx222
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx222 : Known knownx222 := extendKnown_ok (m:=734) validx215 lowx222 (by decide +kernel)
def x347samples : Array (Bits × Bits) := #[(0x4814247bfacffa902848f7f59ff5205091efeb3fea40a123dfd67fd4814247bfacffa902848f7f59ff5205091efeb3fea40a123dfd67fd4814247bfacffa902848f7f59ff5205091efeb3fea40a123dfd67fd4814247bfacffa902848f7f59ff,0x4e102439f1cfb09c204873e39f61384090e7c73ec2708121cf8e7d84e102439f1cfb09c204873e39f61384090e7c73ec2708121cf8e7d84e102439f1cfb09c204873e39f61384090e7c73ec2708121cf8e7d84e102439f1cfb09c204873e39f6),(0x906b10dedd345f20d621bdba68be41ac437b74d17c835886f6e9a2f906b10dedd345f20d621bdba68be41ac437b74d17c835886f6e9a2f906b10dedd345f20d621bdba68be41ac437b74d17c835886f6e9a2f906b10dedd345f20d621bdba68b,0xb02b18c20c104f6056318418209ec0ac630830413d8158c61060827b02b18c20c104f6056318418209ec0ac630830413d8158c61060827b02b18c20c104f6056318418209ec0ac630830413d8158c61060827b02b18c20c104f6056318418209),(0x0,0x0),(0xb2a86930053fb96550d2600a7f72caa1a4c014fee59543498029fdcb2a86930053fb96550d2600a7f72caa1a4c014fee59543498029fdcb2a86930053fb96550d2600a7f72caa1a4c014fee59543498029fdcb2a86930053fb96550d2600a7f7,0x8a007833352f991400f0666a5f322801e0ccd4be645003c199a97cc8a007833352f991400f0666a5f322801e0ccd4be645003c199a97cc8a007833352f991400f0666a5f322801e0ccd4be645003c199a97cc8a007833352f991400f0666a5f3),(0x69ceed810a52c4d39ddb0214a589a73bb604294b134e776c085296269ceed810a52c4d39ddb0214a589a73bb604294b134e776c085296269ceed810a52c4d39ddb0214a589a73bb604294b134e776c085296269ceed810a52c4d39ddb0214a58,0x21ef83c40a104443df078814208887be0f102841110f7c1e205082221ef83c40a104443df078814208887be0f102841110f7c1e205082221ef83c40a104443df078814208887be0f102841110f7c1e205082221ef83c40a104443df078814208),(0x0,0x0),(0x87d7d28571e3150fafa50ae3c62a1f5f4a15c78c543ebe942b8f18a87d7d28571e3150fafa50ae3c62a1f5f4a15c78c543ebe942b8f18a87d7d28571e3150fafa50ae3c62a1f5f4a15c78c543ebe942b8f18a87d7d28571e3150fafa50ae3c62,0x4bc4433573e3909788866ae7c7212f110cd5cf8e425e2219ab9f1c84bc4433573e3909788866ae7c7212f110cd5cf8e425e2219ab9f1c84bc4433573e3909788866ae7c7212f110cd5cf8e425e2219ab9f1c84bc4433573e3909788866ae7c72),(0x0,0x0),(0x373182e0a499626e6305c14932c4dcc60b82926589b98c170524cb1373182e0a499626e6305c14932c4dcc60b82926589b98c170524cb1373182e0a499626e6305c14932c4dcc60b82926589b98c170524cb1373182e0a499626e6305c14932c,0x343184c8881066686309911020ccd0c61322204199a18c264440833343184c8881066686309911020ccd0c61322204199a18c264440833343184c8881066686309911020ccd0c61322204199a18c264440833343184c8881066686309911020c)]
def x347autos : List (List Nat) := [[]]
def x347d6 (i : Nat) : Nat := 0x4240902008c22088200d08cf19283c50500bf99943bf59543f754d43bf58943ef50943bf58543f74c543bf58143ef50143
def x347l6 : Packing := (9,2,3,0,4,7,0,x347d6)
def x347d7 (i : Nat) : Nat := 0x10547fd43
def x347h7 (i : Nat) : Nat := 0x80a01c00000000280f019c06c20003010000000003815
def x347l7 : Packing := (1,1,3,4,4,0,0,x347d7)
def x347columns : List ColumnInfo := [(528,0,331,0,5),(8,0,851,0,5),(2,0,857,0,5),(1,0,858,0,5),(832,0,27,0,4),(3,0,856,0,4)]
def x347levels : Nat → Packing
  | 6 => x347l6
  | 7 => x347l7
  | _ => emptyPacking
def x347index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 2 15 1 12 4 4 x347h7
  | _ => fun _ => none
def x347 : Forest := ⟨859,7,fun j => x347samples[j]?.getD (0,0),x347columns,x347autos,x347levels,x347index⟩
set_option maxHeartbeats 0 in
theorem geomx347 : graphValid x347 (boundsBefore knownx222) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3476_0 : block x347 6 0 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx3476 : block x347 6 0 9=true := sx3476_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3477_0 : block x347 7 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx3477 : block x347 7 0 1=true := sx3477_0
theorem tablesx347 : checkedTables x347 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x347 0 0 0 = true)
  · exact (rfl : block x347 1 0 0 = true)
  · exact (rfl : block x347 2 0 0 = true)
  · exact (rfl : block x347 3 0 0 = true)
  · exact (rfl : block x347 4 0 0 = true)
  · exact (rfl : block x347 5 0 0 = true)
  · exact allx3476
  · exact allx3477
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx347 : Lower (varsX 859) (graphGoal 859) 8 :=
  strong_low (m:=859) (cap:=7) (hints:=12901695489) (by decide +kernel) (plainB (q:=347) (prior:=boundsBefore knownx222) (before_sound knownx222 validx222) (by decide +kernel))
    (index_root (g:=x347) (i:=0) rfl (before_sound knownx222 validx222) geomx347 tablesx347 (by decide +kernel))
def mapsx347 : List (Nat × List Nat) := [(859,[])]
def knownx347 := extendKnown knownx222 8 mapsx347
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx347 : Known knownx347 := extendKnown_ok (m:=859) validx222 lowx347 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx349 : Lower (varsX 861) (graphGoal 861) 7 :=
  strong_low (m:=861) (cap:=6) (hints:=13019128580) (by decide +kernel) (plainB (q:=349) (prior:=boundsBefore knownx347) (before_sound knownx347 validx347) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx347) (before_sound knownx347 validx347) (512,64,29,256,5) (by decide +kernel) (by decide +kernel))
def mapsx349 : List (Nat × List Nat) := [(861,[])]
def knownx349 := extendKnown knownx347 7 mapsx349
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx349 : Known knownx349 := extendKnown_ok (m:=861) validx347 lowx349 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx350 : Lower (varsX 862) (graphGoal 862) 8 :=
  strong_low (m:=862) (cap:=7) (hints:=12901884192) (by decide +kernel) (plainB (q:=350) (prior:=boundsBefore knownx349) (before_sound knownx349 validx349) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx349) (before_sound knownx349 validx349) (528,0,334,0,7) (by decide +kernel) (by decide +kernel))
def mapsx350 : List (Nat × List Nat) := [(862,[])]
def knownx350 := extendKnown knownx349 8 mapsx350
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx350 : Known knownx350 := extendKnown_ok (m:=862) validx349 lowx350 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx371 : Lower (varsX 883) (graphGoal 883) 8 :=
  strong_low (m:=883) (cap:=7) (hints:=21491613697) (by decide +kernel) (plainB (q:=371) (prior:=boundsBefore knownx350) (before_sound knownx350 validx350) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx350) (before_sound knownx350 validx350) (528,0,355,0,7) (by decide +kernel) (by decide +kernel))
def mapsx371 : List (Nat × List Nat) := [(883,[])]
def knownx371 := extendKnown knownx350 8 mapsx371
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx371 : Known knownx371 := extendKnown_ok (m:=883) validx350 lowx371 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx377 : Lower (varsX 889) (graphGoal 889) 8 :=
  strong_low (m:=889) (cap:=7) (hints:=13019136004) (by decide +kernel) (plainB (q:=377) (prior:=boundsBefore knownx371) (before_sound knownx371 validx371) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx371) (before_sound knownx371 validx371) (576,0,313,0,7) (by decide +kernel) (by decide +kernel))
def mapsx377 : List (Nat × List Nat) := [(889,[])]
def knownx377 := extendKnown knownx371 8 mapsx377
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx377 : Known knownx377 := extendKnown_ok (m:=889) validx371 lowx377 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx378 : Lower (varsX 890) (graphGoal 890) 7 :=
  strong_low (m:=890) (cap:=6) (hints:=12910280800) (by decide +kernel) (plainB (q:=378) (prior:=boundsBefore knownx377) (before_sound knownx377 validx377) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx377) (before_sound knownx377 validx377) (512,16,354,8,5) (by decide +kernel) (by decide +kernel))
def mapsx378 : List (Nat × List Nat) := [(890,[])]
def knownx378 := extendKnown knownx377 7 mapsx378
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx378 : Known knownx378 := extendKnown_ok (m:=890) validx377 lowx378 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx476 : Lower (varsX 988) (graphGoal 988) 7 :=
  strong_low (m:=988) (cap:=6) (hints:=13556196096) (by decide +kernel) (plainB (q:=476) (prior:=boundsBefore knownx378) (before_sound knownx378 validx378) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx378) (before_sound knownx378 validx378) (512,64,156,256,5) (by decide +kernel) (by decide +kernel))
def mapsx476 : List (Nat × List Nat) := [(988,[])]
def knownx476 := extendKnown knownx378 7 mapsx476
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx476 : Known knownx476 := extendKnown_ok (m:=988) validx378 lowx476 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx497 : Lower (varsX 1009) (graphGoal 1009) 7 :=
  strong_low (m:=1009) (cap:=6) (hints:=22951231492) (by decide +kernel) (plainB (q:=497) (prior:=boundsBefore knownx476) (before_sound knownx476 validx476) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx476) (before_sound knownx476 validx476) (512,64,177,256,5) (by decide +kernel) (by decide +kernel))
def mapsx497 : List (Nat × List Nat) := [(1009,[])]
def knownx497 := extendKnown knownx476 7 mapsx497
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx497 : Known knownx497 := extendKnown_ok (m:=1009) validx476 lowx497 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx504 : Lower (varsX 1016) (graphGoal 1016) 7 :=
  strong_low (m:=1016) (cap:=6) (hints:=14368849920) (by decide +kernel) (plainB (q:=504) (prior:=boundsBefore knownx497) (before_sound knownx497 validx497) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx497) (before_sound knownx497 validx497) (512,16,480,8,5) (by decide +kernel) (by decide +kernel))
def mapsx504 : List (Nat × List Nat) := [(1016,[])]
def knownx504 := extendKnown knownx497 7 mapsx504
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx504 : Known knownx504 := extendKnown_ok (m:=1016) validx497 lowx504 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx127 : Lower (varsX 639) (graphGoal 639) 9 :=
  strong_low (m:=639) (cap:=8) (hints:=16785665) (by decide +kernel) (plainB (q:=127) (prior:=boundsBefore knownx504) (before_sound knownx504 validx504) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx504) (before_sound knownx504 validx504) (576,0,63,0,8) (by decide +kernel) (by decide +kernel))
def mapsx127 : List (Nat × List Nat) := [(639,[])]
def knownx127 := extendKnown knownx504 9 mapsx127
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx127 : Known knownx127 := extendKnown_ok (m:=639) validx504 lowx127 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx223 : Lower (varsX 735) (graphGoal 735) 9 :=
  strong_low (m:=735) (cap:=8) (hints:=553656577) (by decide +kernel) (plainB (q:=223) (prior:=boundsBefore knownx127) (before_sound knownx127 validx127) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx127) (before_sound knownx127 validx127) (128,0,607,0,8) (by decide +kernel) (by decide +kernel))
def mapsx223 : List (Nat × List Nat) := [(735,[])]
def knownx223 := extendKnown knownx127 9 mapsx223
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx223 : Known knownx223 := extendKnown_ok (m:=735) validx127 lowx223 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx247 : Lower (varsX 759) (graphGoal 759) 9 :=
  strong_low (m:=759) (cap:=8) (hints:=553648385) (by decide +kernel) (plainB (q:=247) (prior:=boundsBefore knownx223) (before_sound knownx223 validx223) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx223) (before_sound knownx223 validx223) (592,0,167,0,7) (by decide +kernel) (by decide +kernel))
def mapsx247 : List (Nat × List Nat) := [(759,[])]
def knownx247 := extendKnown knownx223 9 mapsx247
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx247 : Known knownx247 := extendKnown_ok (m:=759) validx223 lowx247 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx251 : Lower (varsX 763) (graphGoal 763) 8 :=
  strong_low (m:=763) (cap:=7) (hints:=1358970881) (by decide +kernel) (plainB (q:=251) (prior:=boundsBefore knownx247) (before_sound knownx247 validx247) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx247) (before_sound knownx247 validx247) (576,0,187,0,7) (by decide +kernel) (by decide +kernel))
def mapsx251 : List (Nat × List Nat) := [(763,[])]
def knownx251 := extendKnown knownx247 8 mapsx251
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx251 : Known knownx251 := extendKnown_ok (m:=763) validx247 lowx251 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx254 : Lower (varsX 766) (graphGoal 766) 8 :=
  strong_low (m:=766) (cap:=7) (hints:=561193248) (by decide +kernel) (plainB (q:=254) (prior:=boundsBefore knownx251) (before_sound knownx251 validx251) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx251) (before_sound knownx251 validx251) (576,0,190,0,7) (by decide +kernel) (by decide +kernel))
def mapsx254 : List (Nat × List Nat) := [(766,[])]
def knownx254 := extendKnown knownx251 8 mapsx254
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx254 : Known knownx254 := extendKnown_ok (m:=766) validx251 lowx254 (by decide +kernel)
def x351samples : Array (Bits × Bits) := #[(0x3f310a0231c270243c712a55d18e3890876b01fcd7af232bcc7ff99f142f94f0dbd5ecfcc42808c709c090f1c4a9574638e2421dac07f35ebc8caf31ffe67c50be53c36f57b3f310a0231c270243c712a55d18e3890876b01fcd7af232bcc7ff,0x7f38030001c8203401410c5550a039d08f6b41ccf725812bcc3bea29501696e09ce7c9fce00c00072080d0050431554280e7423dad0733dc9604af30efa8a5405a5b82739f27f38030001c8203401410c5550a039d08f6b41ccf725812bcc3be),(0x83e33d84e2638fc12c04321006c1c7859d9cba70b1d37854378e105193a60957dafc760f8cf613898e3f04b010c8401b071e167672e9c2c74de150de3841464e98255f6bf1d83e33d84e2638fc12c04321006c1c7859d9cba70b1d37854378e1,0x80003c040a138a022c2402002440c4247090a23000d2701033841000838009154200160000f010284e2808b090080091031091c24288c00349c040ce1040020e0024550800580003c040a138a022c2402002440c4247090a23000d2701033841),(0x557693d7b7e42589039a8c01003bca4b589f540e7c098fce0afbe3379d20f74f90a94955da4f5edf9096240e6a300400ef292d627d5039f0263f382bef8cde7483dd3e42a52557693d7b7e42589039a8c01003bca4b589f540e7c098fce0afbe,0x2d6c373a5e405c1130b8140903b1a4b0c0f54447a0d0fce007bcbb7306a74e89069480b5b0dce979017044c2e050240ec692c303d5111e8343f3801ef2edcc1a9d3a241a5202d6c373a5e405c1130b8140903b1a4b0c0f54447a0d0fce007bc),(0xe909c05911d42a1a8396cc29285031326101ce0bc420d131dd9074206010a68c0d13afa42701644750a86a0e5b30a4a140c4c98407382f108344c77641d08180429a30344ebe909c05911d42a1a8396cc29285031326101ce0bc420d131dd907,0x410900085000303880d02421288061106300288b81a09011dc80300040150800051421042400214000c0e203409084a20184418c00a22e068240477200c0010054200014508410900085000303880d02421288061106300288b81a09011dc803),(0x8c1472ea09027867546151ccc95e2c2330340685026a36cea345058377197821450c123051cba82409e19d518547332578b08cc0d01a1409a8db3a8d14160ddc65e085143048c1472ea09027867546151ccc95e2c2330340685026a36cea3450,0xc4c8f228234bc35820d18a8756842b10149620085a2ec423440410acc8211f220014031323c8a08d2f0d6083462a1d5a10ac405258802168bb108d101042b320847c8800500c4c8f228234bc35820d18a8756842b10149620085a2ec423440),(0x0,0x0),(0x3ce4e4207c899050420871a3972905cc02626dc32f548c94e463eacc0af05e52381850f3939081f22641410821c68e5ca417300989b70cbd523253918fab302bc17948e06143ce4e4207c899050420871a3972905cc02626dc32f548c94e463e,0x7db0c0217140355c4259702a8b2d019303604ccb2f258b86c443e1f05c7f420a891c29f6c30085c500d5710965c0aa2cb4064c0d81332cbc962e1b110f87c171fd082a2470a7db0c0217140355c4259702a8b2d019303604ccb2f258b86c443e),(0x0,0x0),(0xb05c3aa00c9a4a10d52e89e27030927c8ec29130081c44e9733c8a0ee8c04085b0039ec170ea803269284354ba2789c0c249f23b0a44c0207113a5ccf2283ba3010216c00e7b05c3aa00c9a4a10d52e89e27030927c8ec29130081c44e9733c8,0x804234c40cb9400015228bd45052966c9c84913450186468233c00072300801472e2460108d31032e50000548a2f51414a59b2721244d1406191a08cf0001c8c020051cb891804234c40cb9400015228bd45052966c9c84913450186468233c0)]
def x351autos : List (List Nat) := [[]]
def x351d5 (i : Nat) : Nat := 0x1e4121d53209414c554
def x351l5 : Packing := (1,6,6,0,4,0,0,x351d5)
def x351d6 (i : Nat) : Nat := 0x461048105010481038103a104808e030e56422e19d9995918d8980394c8754c824c554f4521d53505315539a487209414c554fc154c82505315528bda121d645815495e68c97581505529b1a1251801cd54a1768c956187155207ca9619531c55486e2a1901cd41553438975916054154
def x351h6 (i : Nat) : Nat := 0x38000
def x351l6 : Packing := (11,5,6,1,4,8,0,x351d6)
def x351d7 (i : Nat) : Nat := (if i<1 then 0x2b6965abc55aa7947a8a4f69d933a584928e915a124067d0f29e03a2708d99a432a618bb9682b25289d93624e460848fa1c2348618b414a2303985a0960f01681e01e0023fb2241aecaa47f64a885cd54cbec2b0239aa91fe99604735533f302c00e6aa47f6488758d548fec890eb1aa91fd9120d725523fb2643ac4aa47f6448758954a7e4bac6b12a9e5d6354d62552bf32039aa4aa53f259874c9548fec890e992a94fc965cd325523fb25442e2aa67e201635c554cfc402c4b8aa99f8804c9715523fd32c18e2aa63f619431c554cbea9b0438aa98fd86508715523fb30990e2aa63f619321c554ceec1a6438aa99ed824c8715532faa6c00e2aa47f64c87585548fec910eb0aa98fc8758961552bf32039aa2aa56f6587350554adec90e6a0aa95bc9758d41552b792e99282aa66f21d32505549f6c951098aa94fc9661d31552bd924c3a62aa57e241874c5548fec910e98aa99ec829dd31552bb926bb262aa67b209764c554dd6412c898aa94fc965cd315533d904b9a62aa57e640734c554abe4baa698aa997c8754d315536d904a9a62aa75721d534c554cf6c390498aa99ec8720931553e9aa641262aa47f261724c5548fe4c2e298aa99ec825c531552bf120b8a62aa66f21d414c554dd64128298aa9db48750531553f4904a0a62aa7e54c9414c5548fec990e90aa94fc965cd215523fb3039a42aa57b6487348554afac88e690aa95f9901cd21552af92ea9a42aa65f21d5348554faaa9a6290aa91fd92a21705523fb2241ae0aa47f261315c154af649262b82a91fd9321d605523fb2443ac0aa47f6448758154abe4bac6a82a957c9758950552ed92498aa0aa47f648874c1548fec890e982a91fd9321d205529f92cb9a40aa57e25d30481548fec990e882a94fc965cd105532f90ea9a20aa7ec50520441548fcc8106bb2a90fd96a21735521f931332e6aa62f21a445cd54cbcc2b0039aa91fa99600735531f4ccc00e6aa65e955801cd54cdc4a30039aa99ba44600735530f90e432a6aa45f2617654d54c3e43ccca9aa9579901cd53553c3ac8b1aa6aa5766407350d54a6e4b2e719aa95d9901ce33552ab92ea9c66aa47e640835c9548be4c2a6b92a91dc9361d625529d92cb9c44aa57a6407388954ab64baa7112a91f990a21715531f101332e2aa65e202555c554cec40466b8aa99e880889715521fd32c30e2aa61f255861c554c3ec34aa38aa98bd86910715530fb0ca98e2aa63761a331c554c76c344438aa94f5961c551552b732039a82aa66721e3350554cd643c44a0aa99b88720141553e2aa6a0a62aa57c2417184554a7a4b2e708aa95f1901ce11552ae92ea9c22aa62f21d6458154abc4bac0a82a9e3964581505523f130b8260aa7cc5055044154a7c4b2e7002a91f8985c6005529f32c38c00aa56e25d4180154 else 0x54200542000c2008400080610000000008104000000000001080a1000c100c203040000000010010042410400068190541404ca8086800900140420a826221c20404200801710000c82a008c080848208101080000000028401080000000020421201820046078800204202040708081000e10102400400068200202000428081616002c304280816108c20c868008023080000816101020d041508140a08000e021c0420a0020104020d0210142120405080a108c20286810802908061a04214841508c401040008161010212042208c1e102011881a0850100020487020e041e1bc237cef4dcbb8368ec2d67a934fe9ad2ba4345e86d039cb36e68cc797b2ce54c9f92b1de2cc4f86304dfabeb7c2f5de6bc3772ebdc8b736aad2da0ad356aa5d3ca5b45282d009e33b269cce99329a50c929071fa37c6a8cb1822dc568a310a19c2e8530920fc1a82b04200be87c6f29e2bc0762e89c9b846fedc1b0b5269ad219cb3464ac5983af85d)
def x351h7 (i : Nat) : Nat := 0xb09000603000000306000507204000002f08c0a000e01000000c05d00000000c
def x351l7 : Packing := (150,4,6,4,4,11,0,x351d7)
def x351d8 (i : Nat) : Nat := (if i<1 then 0xc839dd549fd829dd549fd819dd549fd809dd549fe885d9549fc835d954cfe7799954d7e7795554bbe8859154dbe7759154dbe7791154dbd7691154ebe6691154f3e55911549fe885cd54cfc865cd54cfe665cd54d7e555cd54dbd645cd54dbe445cd54ddd731cd54bf9801cd549fe881cd549fd861cd54cfe661cd54d7d851cd54d7e551cd54dbe441cd549fd821cd549fd811cd549fd801cd54df9801cd549fd8758d549fc8758d54ebd6458d54ddc7354d54b7e8854d54d7c8754d54d7e7754d54e7c8654d54d7d7654d54e7e6654d54f3c8454d54f3d6454d54f3e4454d54d7c7354d54f5c7354d54f5d6354d549fd8750d54ddc7350d549fd878cd549fc878cd54ddd738cd54ddc738cd54f5d538cd54ddd878cd54ddc878cd54dde778cd54ddd768cd54ede668cd54f5c858cd54f5e558cd54f9d648cd54f9e448cd549fe885c954cfe665c954d7e555c954dbe445c9549fc835c954d7d535c954dde335c9549fd87589549fc87589549fd874c9549fc874c954dee7788954ded7688954eee6688954f6e5588954fad6488954fae4488954ded7388954dec7388954f6d5388954fce33889549fe885c554cfe665c554d7e555c554dbd645c554dbe445c5549fc835c554dde335c554dee225c554df8805c554afd861c554df5711c5549fd861c554cfe661c554d7e551c554dbe441c5549fd831c554d7d531c554dde331c5549fd821c554dee221c5549fd801c5549fd87585549fc8758554cfd7658554ebd6458554df471545549fd8750554df47150554bbe8850554dbc8750554dbe7750554bbd8650554dbd7650554ebe6650554f3c8550554f3e5550554dbc7350554f3d5350554f9e3350554dbd7250554fae2250554fb47150554fb880505549fd874c5549fc874c554f5d534c554fb5414c5549fd870c554b7d850c554bbd840c5549fd87485549fc87485549fc8784554df57184554fb54184554df48784554df67784554df57684554ef66684554f765584554fb48484554fb56484554fb64484554df57384554df47384554f755384554fd63384554df57284554fe622845549fe885c154cfe665c154d7e555c1549fc835c154d7d535c154dde335c154dee225c154dbd415c154df6115c1549fd87581549fc8758154ebd6458154b7e8854154d7e7754154e7e6654154f3d6454154d7d7354154f5e3354154f6e2254154d7d7154154f3d4154154f761154154f7960541549fd874c1549fc874c154b7d854c154df9704c154f79504c1549fd87481549fc87481549fd87441549fc8744154fb54144154f795044154dfa7780154df97680154efa6680154f7a5580154fb96480154df97380154df87380154f795380154fda3380154df97280154fea2280154df97180154df87180154fb94180154ff211801549f9801cd548fd861c554 else (if i<2 then 0x663311981cb8e5992b594f4a1e4e1259921488a4171f48eec71a35f1988c545f22cb14e89bc45e2010d7857425e10106982940ee0490167ffbfa1fa2fb17c8bde9ec6f4c7963c79e20f0277a3b99db0ed37673addd2ee8973db96dc9ae48718b821be2de36e1b6d5b4ed75698b4459e2cda65d328d93cc9063cb1ad8bac4f620b0f184ac1760930357ecbd65e8aec5734b8c5bf2dc16c4b545a32ce1666b255902c4961aaed56fab45586aa354aaa1d4e0a5051828414049f44f7a7a93b89d74e4a6ed35a9a84c8a60d2ea94c49f2479220902471232d18c8a644c22290f88414152070fe67e53e71eb8ef875c3999cb8e1c70937d9b90dac6bf34f9a44d1867e33398f8c606193059818bf05cf2d79660b025612a514cca264fc272935c9924bb256927c93449524391e48e846622c112888a437219106c81a3ff1eb0ed875039a1c18dd46aa33e1938c646162fd16a0aac53a28f137896049423310987cc3b81c50ce05f02ca14e09b84802120fb07683a01c60d506382e41560a604c024c10a0770348190064000bfd821cd54bfd811cd54dfd811cd54bfe8858d54dfe7758d54dfd7358d54f7d6354d54dfd635c954bfe8858954dfe7758954dfd7358954efd6358954f7d5358954dfc7354954fed5250954bfe884c954dfd874c954dfe774c954bfd864c954dfd764c954fbd644c954dfd734c954f7d534c954fed624c954dfd635c554dfd625c554dfd325c554bfd831c554bfd821c554bfd801c554dfd631c554dfd431c554dfe331c554dfd621c554dfd421c554dfd321c554efd6458554efd6258554dfc7354554fbd6350554fbd6250554fbd3250554bfe884c554dfd874c554dfc874c554dfe774c554bfd864c554dfd764c554fbd644c554dfd734c554dfc734c554f7d534c554fec824c554dfd724c554fdd324c554dfd714c554ff5614c554fbd414c554bfd820c554bfe8848554dfd8748554dfe7748554bfd8648554dfd7648554fbd6448554bfd8348554dfd7348554dfc7348554f7d5348554dfd7148554fbd4148554ff53148554dfc7384554dfd635c154dfd625c154dfd325c154dfd315c154dfd215c154bfe8858154dfe7758154dfd7358154f7d5358154dfd7258154dfd7158154efd6158154fbd4158154dfc7354154f7d6354154f7d6254154f7d3254154f7d3154154f7d2154154bfd864c154fdd314c154ff9604c154ff9504c154bfe8848154dfe7748154bfd8648154dfd7648154fbd6448154bfd8348154dfd7348154dfc7348154f7d5348154fed6248154dfd7148154fbd4148154fed2148154ff93048154bfe8844154dfe7744154bfd8644154dfd7644154fbd6444154bfd8344154dfd7344154dfc7344154f7d5344154bfd8244154dfd7244154dfd7144154fbd4144154ff920441549fd869dd549fd839dd549f else 0x260110782a20a84120810241020ac00424087c1c204820409040810201004214084412201843c091003c091078102098204800c042130a0021f0a881020104c1220f06441600883012108c2020282841e12080a1010141420284001e101832208824423030814061003c0910001e048846010f04081e0c8542844008c4830481441509882a1006402151804209088c4820c8144130a883c0910a821e0488101e105810240043c091058122088402a80880a100842228107c1c20408041304883419028548160488120810241020d8381a30709040d0408360e068c2023104050205c1c42909408702400a041810a45038104241e080c522810385220107840b0488120b10781020405c41e812006090f08121710442420481c502400812171068302081c2a20582440b0488241e080c301b108c3c10401052010f0488180c88521210a40e20f0244180d88330210a022a00881c2410543c20986c463088603c30c87841b1408101e104c52241c0030608002000a18200080029118833810d8d00143044680148d0e1007852204808541e207848240042813148d0c1438416090a850265058240a010a888487020985030a84c3c30b86440b000786101488006087c4620304461118500100904624384000a88c4000b88c600104c4630f0a4409084420608242150824200080061020020808a44634004021008602290f8c46100844c19102c001e18080023182e021e1c04200080080082021808602100a446240040a11181d0029221c2131307c6050a04215c083861e11880030408c6860a1820508280a1a0809c4660308c4050828101a12910210c0a0402008a461e05814062328640a24181b04231210002100a46002844029101420314883205148d0c1021820714880e061488c8050814522408402908000401071016050f0c2a2310645220104c4630208c40314880400148c541e107846202840a10284121000400020500100242110818200084029118900101042608038a48150388c6020a042051488041050582838107841b1208041010604181200522320a40d02119204181045102118c4629140821211880200118c3c04148c0823105450203e00522820000a1518a83c20983842a0f0832291048462810400100100181060e1838400108204181060410054262414078a250d0900a1e2e9f34cba57d2068a7425a04cf6e75b37f9a8ccd66332eb967ca8652f26991dc8363e31d58dcc6762df141889c39616f08982dc0b5ffefd17d1be1deb2f2b77ebb3dd42e97734b97dcaae276eab60da86d15673b32d982c81632b125836bed5dfae456eab4758cabad59eaa1539a95d49aa1f501a79d37298b4aea4bd1ba8af440a14d0267e53db9ddce9271b3769ab4cfe))
def x351h8 (i : Nat) : Nat := 0x2028e030a044000040180000000018471840e849f816000000005846903880280014a81c0000282d00000000783a3011780f80006834503300000000000000000000000000006833b00dd804d81de81580000000381f0000482d8000400700003827f824301470006024b81cf832e830482be03bf008b00bf0205017780a98106822283e901e000d783f9829b03f60423002f82708412802600600005834f03918480000502eb808503d00002817b031f83c70010000083c8801c8214849601bc00f000070460000281ff845c8130848e02c18041003e812000028455003700e80000000581a204aa010a811f00080000000601b482e1835c023a843002940250826302a282b0819300e282fb81ab82cd847d0406035000000005819803df8057837800000000807a03ac823500c7836b839902ac00b501380004016a836402f08188000204190380009800060268000580c8000701d0000381ed0320000282580003021b8090000380a0044a03710150820e022883b004a103e6042a812f83120068000584380000005b448046032400195260028c200c0004620d330304409305c21308b8383c800186
def x351l8 : Packing := (331,3,6,8,4,13,0,x351d8)
def x351d9 (i : Nat) : Nat := 0x4031e232000f118c1878a46010252464071e2918f8f028a43c09483207e0a041c188cc0b01020c525058081062928094918c807814521c04a41902b040e0246505800601292c100c00c89948f1c0a048ca480c3c463140a0682812330ac1408391940818160618a4c0b0503003202523c805812923200c00c95148f18560816041c8cc0502524641e1a0d051514810706494c083919068241e0600a4c3c2e2a350c02460e81e150b01862a2307402c080c3c311948f201408660418a4d05020c38187061c111c094831606181c60b0e010252466050106130724291e44383c09491945604021e18a0a050c02524668786011c30140919494641e08189468781510c0a0d02465268100878605282800ac083919a00a6048c1cb03000e38c38a68898648478027cd7a07737567116e46b767a6556386035d65a155c5375024cd4a845b4364013bc3773322fd2e02c32962792441ff1d21a51701531260e10ac07f04a01d000ffceeaa7fd76553feb22a9ff5cd54ff8e6aa7fd63553fea9aa9ff50d54ffc66aa7fd72553feb12a9ff54954ffa84aa7fd32553feb8aa9ff1c554ffac2aa7fd51553fea0aa9ff4c554ff862aa7fd21553ff08aa9ff5c154ffac0aa7fd50553fe982a9ff48154ffa20aa5fe77552febb2a9bf99954efcaaaa7bd64553df222a97f5cd54bf8e6aa77d53553ef19aa97f5c954fdc44aa5fd71552fe38aa9ef50554fec22aa5fd70553bea82a9fe80154
def x351h9 (i : Nat) : Nat := 0x901c98290815620d77086284b400008038b016383de02580000c08c0000000000000d024f007b416120d8208080000000060c6f082b04e40001a08d00007818800008061b0290000201300000406f1017b402a409ff070101de4016c06da02da80be4158c0ef201d000020170a137a04d00001420760f900003846582014081001148310c17b2080e039a042680d581291068e021cc20cc08e20148851a8005607e502e98062823c80306036480d5c018a1479064000000000000000000000000000000c05bb81d142340000d021e8484000000003071284af80100000a02b000008140a13c00005822c00000000205b500ac00000000502e50108000120be00000813fc00a0000202000002c06400003037983154283013a8091d01a0419f2000d00c80000c12a201dd089f008c00000000105a0000380e2801a0000000010091007ac053903f4c03720fbb05080000c051c0a88076c8166428700e55010b84fc000160cee01b08230421a0000109200000000100570000784d44181404a803e381a40001c01cc05e000000000814a6057204b9809b4054600f8000101e040965013304e000018122300480000c0f60000108bd8131819a0000204f305084165c10f90760000000000000a0a2d82280000a09b8075e84d801ea60af0000704cc02162082306de049600c0a120203b083a702286128d01ec04110066c0c9d023c032840fac0a50061680a8000020bf00003814e42380000b0550000001cf80a9803c08377c1822050f031b03d1016ae06610489003a000800008088083e00001803f9003080b70177e090600b003da0022a13d50981843ac07c0000e0a06032f816700df00000000081b3211600004830d81320072007f001b8425fe1077022503a80001c12a401de03c640480000000008288000000009038000000001a03c5056c836bc09c611f0000004ca81a00000f04910034012640fa000008042c1a521348044c8117c1c6c014d04e985200040c0e8c023702c68210c0a320810823c82778067f08e800000001a07960170003dc1e7e0ee106ab0004c08200000000684980001208340a20000000000000000000003823620ba000000000802400000000101d741990025e042b8147c12940e4302c200d2417200008001a04c60214005fb035d0527824f40375018800000000c0fc80434016b812e000000004005c013980d66088d83c9414c20d3506a30456400f00ff5063c037341084027709f7004fc015a0653025c838601cd4055203250448c111807f00050c001500000f0004011b02000b031a1807000503070804140a0222040a0007070003081e0a0009150200030602271a160845010a020801099f02020800130f0028050014030600130e1c020400061c02
def x351l9 : Packing := (48,2,6,9,4,12,0,x351d9)
def x351d10 (i : Nat) : Nat := 0x21c30ffd54
def x351h10 (i : Nat) : Nat := 0x302c0001016000102a90b942d0003011e09fc0c40be8037048000000241400050230001825000182b8064c24902c80d0000000306c0000002005606181e0001420900a8040000000f000000000301c000000090540000001829f01f00900000000000000000101f000100ea08501ac07480a40a1022a05e013000340fd018000000042600000004021010d02220340270
def x351l10 : Packing := (1,1,6,6,4,0,0,x351d10)
def x351columns : List ColumnInfo := [(256,0,607,0,8),(4,0,859,0,8),(1,0,862,0,8),(576,0,31,0,7),(528,0,334,0,7),(2,0,861,0,7),(832,0,31,0,7),(529,0,334,0,7),(512,256,23,72,6),(512,64,29,258,6),(512,16,326,9,6),(512,1,332,18,6),(784,0,79,0,5),(257,0,606,0,5),(768,64,29,2,5),(577,0,286,0,5),(576,256,23,8,5),(536,0,327,0,5),(528,1,332,2,5),(12,0,851,0,5),(520,256,23,64,5),(520,16,326,1,5),(6,0,857,0,5),(5,0,858,0,5),(3,0,860,0,5),(514,64,29,256,5),(514,1,332,16,5),(513,16,326,8,5),(258,0,29,0,4),(530,0,332,0,4),(848,0,15,0,4),(840,0,23,0,4),(836,0,27,0,4),(833,0,30,0,4),(785,0,78,0,4),(770,64,29,0,4),(584,256,23,0,4),(582,0,281,0,4),(537,0,326,0,4),(533,0,330,0,4),(530,1,332,0,4),(521,16,326,0,4),(7,0,856,0,4)]
def x351levels : Nat → Packing
  | 5 => x351l5
  | 6 => x351l6
  | 7 => x351l7
  | 8 => x351l8
  | 9 => x351l9
  | 10 => x351l10
  | _ => emptyPacking
def x351index : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 3 0 9 1 4 x351h6
  | 7 => lookupWord 2 21 2 12 4 4 x351h7
  | 8 => lookupWord 37 199 7 16 8 4 x351h8
  | 9 => lookupWord 82 432 8 17 9 4 x351h9
  | 10 => lookupWord 12 79 4 14 6 4 x351h10
  | _ => fun _ => none
def x351 : Forest := ⟨863,10,fun j => x351samples[j]?.getD (0,0),x351columns,x351autos,x351levels,x351index⟩
set_option maxHeartbeats 0 in
theorem geomx351 : graphValid x351 (boundsBefore knownx254) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=2) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3515_0 : block x351 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx3515 : block x351 5 0 1=true := sx3515_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3516_0 : block x351 6 0 5=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3516_5 : block x351 6 5 6=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx3516 : block x351 6 0 11=true := (@block_merge x351 6 0 5 6 sx3516_0 sx3516_5)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3517_0 : block x351 7 0 36=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3517_36 : block x351 7 36 20=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3517_56 : block x351 7 56 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3517_92 : block x351 7 92 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3517_128 : block x351 7 128 22=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx3517 : block x351 7 0 150=true := (@block_merge x351 7 0 128 22 (@block_merge x351 7 0 92 36 (@block_merge x351 7 0 56 36 (@block_merge x351 7 0 36 20 sx3517_0 sx3517_36) sx3517_56) sx3517_92) sx3517_128)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3518_0 : block x351 8 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3518_2 : block x351 8 2 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3518_38 : block x351 8 38 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3518_74 : block x351 8 74 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3518_110 : block x351 8 110 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3518_146 : block x351 8 146 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3518_182 : block x351 8 182 25=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3518_207 : block x351 8 207 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3518_243 : block x351 8 243 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3518_279 : block x351 8 279 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3518_315 : block x351 8 315 16=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx3518 : block x351 8 0 331=true := (@block_merge x351 8 0 315 16 (@block_merge x351 8 0 279 36 (@block_merge x351 8 0 243 36 (@block_merge x351 8 0 207 36 (@block_merge x351 8 0 182 25 (@block_merge x351 8 0 146 36 (@block_merge x351 8 0 110 36 (@block_merge x351 8 0 74 36 (@block_merge x351 8 0 38 36 (@block_merge x351 8 0 2 36 sx3518_0 sx3518_2) sx3518_38) sx3518_74) sx3518_110) sx3518_146) sx3518_182) sx3518_207) sx3518_243) sx3518_279) sx3518_315)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3519_0 : block x351 9 0 19=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3519_19 : block x351 9 19 29=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx3519 : block x351 9 0 48=true := (@block_merge x351 9 0 19 29 sx3519_0 sx3519_19)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx35110_0 : block x351 10 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx35110 : block x351 10 0 1=true := sx35110_0
theorem tablesx351 : checkedTables x351 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x351 0 0 0 = true)
  · exact (rfl : block x351 1 0 0 = true)
  · exact (rfl : block x351 2 0 0 = true)
  · exact (rfl : block x351 3 0 0 = true)
  · exact (rfl : block x351 4 0 0 = true)
  · exact allx3515
  · exact allx3516
  · exact allx3517
  · exact allx3518
  · exact allx3519
  · exact allx35110
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx351 : Lower (varsX 863) (graphGoal 863) 11 :=
  strong_low (m:=863) (cap:=10) (hints:=12901687553) (by decide +kernel) (plainB (q:=351) (prior:=boundsBefore knownx254) (before_sound knownx254 validx254) (by decide +kernel))
    (index_root (g:=x351) (i:=0) rfl (before_sound knownx254 validx254) geomx351 tablesx351 (by decide +kernel))
def mapsx351 : List (Nat × List Nat) := [(863,[])]
def knownx351 := extendKnown knownx254 11 mapsx351
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx351 : Known knownx351 := extendKnown_ok (m:=863) validx254 lowx351 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx375 : Lower (varsX 887) (graphGoal 887) 9 :=
  strong_low (m:=887) (cap:=8) (hints:=21491613953) (by decide +kernel) (plainB (q:=375) (prior:=boundsBefore knownx351) (before_sound knownx351 validx351) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx351) (before_sound knownx351 validx351) (528,0,359,0,8) (by decide +kernel) (by decide +kernel))
def mapsx375 : List (Nat × List Nat) := [(887,[])]
def knownx375 := extendKnown knownx351 9 mapsx375
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx375 : Known knownx375 := extendKnown_ok (m:=887) validx351 lowx375 (by decide +kernel)
def x379samples : Array (Bits × Bits) := #[(0xda6e1f5e1d15c66fdf09038511066e5a54886740399fcee8efce5bf0118300e05d9af69b87d78745719bf7c240e144419b96952219d00e67f3ba3bf396fc0460c0381766bda6e1f5e1d15c66fdf09038511066e5a54886740399fcee8efce5bf,0x2103f004001c00ddf0109871104141c7400a0002805c6e867ce43b000000010419900840fc01000700377c04261c44105071d0028000a0171ba19f390ec000000041066402103f004001c00ddf0109871104141c7400a0002805c6e867ce43b),(0xfe2f52531020688148de82b1e2a98373082e8dbd4bcb31519ab3ac5e6cf708c51468bf8bd494c4081a205237a0ac78aa60dcc20ba36f52f2cc5466aceb179b3dc231451a2fe2f52531020688148de82b1e2a98373082e8dbd4bcb31519ab3ac5,0xa10f805a00202280200e02306a918be3882f05bd479a11019811ac4ea0eb30c53440e843e016800808a00803808c1aa462f8e20bc16f51e6844066046b13a83acc314d103a10f805a00202280200e02306a918be3882f05bd479a11019811ac4),(0x0,0x0),(0xdda3e0028086d010e521fc331f45913af6b18aba2d30382f083f57f29a7d433b28853768f800a021b40439487f0cc7d1644ebdac62ae8b4c0e0bc20fd5fca69f50ceca214dda3e0028086d010e521fc331f45913af6b18aba2d30382f083f57f,0xd861fe020096e01006419f955d001422a2b08a7a6d94aa6d083f53703a168220781df6187f808025b804019067e557400508a8ac229e9b652a9b420fd4dc0e85a0881e077d861fe020096e01006419f955d001422a2b08a7a6d94aa6d083f537),(0x868035609126cf28253d6100aedbfdc9027170109422959f9044ad028304471b758721a00d582449b3ca094f58402bb6ff72409c5c042508a567e4112b40a0c111c6dd61c868035609126cf28253d6100aedbfdc9027170109422959f9044ad0,0x240e0024b5000f2020bc6068a0fbe9c1014f5001926a11129000ac0805884dce0262090380092d4003c8082f181a283efa704053d400649a8444a4002b020162137380988240e0024b5000f2020bc6068a0fbe9c1014f5001926a11129000ac0),(0x90ef48af6c5ea4469076940403100882c9d5534776f84a175139bc689446d5209f10643bd22bdb17a911a41da50100c40220b27554d1ddbe1285d44e6f1a2511b54827c4190ef48af6c5ea4469076940403100882c9d5534776f84a175139bc6,0x90ea00bfadd6244200f29410028809e08b51435357f8281710313c42ee75876cbe02e43a802feb758910803ca50400a2027822d450d4d5fe0a05c40c4f10bb9d61db2f80b90ea00bfadd6244200f29410028809e08b51435357f8281710313c4),(0x60904f0387a1099202d3a059f5a8301d67c2884ad244a35625f033356cc8a9048860182413c0e1e8426480b4e8167d6a0c0759f0a212b49128d5897c0ccd5b322a412218060904f0387a1099202d3a059f5a8301d67c2884ad244a35625f0333,0x40b050818594c157c5c03140846e301867d0e8423864aa7621e413315000c638c21f102c142061653055f1700c50211b8c0619f43a108e192a9d887904cc5400318e3087c40b050818594c157c5c03140846e301867d0e8423864aa7621e4133),(0x0,0x0),(0x11d80a062c9339026045c6a101440a4bd4e14a780041520f601c2890038b420c2200047602818b24ce40981171a840510292f538529e00105483d8070a2400e2d0830880011d80a062c9339026045c6a101440a4bd4e14a780041520f601c28,0x2704014052281aa02000402a00114205000e148480035580c60080840088388301a009c10050148a06a80800100a80045081400385212000d5603180202100220e20c06802704014052281aa02000402a00114205000e148480035580c600808)]
def x379autos : List (List Nat) := [[]]
def x379d5 (i : Nat) : Nat := 0x1d0625c9458d6054153
def x379l5 : Packing := (1,6,6,0,4,0,0,x379d5)
def x379d6 (i : Nat) : Nat := 0x24081f0800000012041201f80c303e1034103618f7f7a75706b665630201000a5b680875492154e9d5a621d314855386f69097a216054f89c872116358153d4e25c945815054fc589758d6054153f86251635815054e971a0255811d953e5121d524c52154e8cda624d821c1538732a5636087054e174a86447654153
def x379h6 (i : Nat) : Nat := 0x160
def x379l6 : Packing := (12,5,6,1,4,8,0,x379d6)
def x379d7 (i : Nat) : Nat := (if i<1 then 0x865c9538feca10eb12a71fd9021d6254e3fb2c43a84a9c7f64087509538fe4bb0ca12a75ec975894254fd9ac6b1284a9c7f652885c5538fec810cb8aa71fd9421d6154e3fb2043ac2a9c7f65887505538fe4bb0ca0aa75ec925d94154f2f90ea9282a9d7d25d6150553afa4bac298aa75dc975893154ebb92ea1262a9c7f65887485538feca10e90aa71fd9021d2154e3f92ec3242a9c7f25d84485538feca510b82a79f4815917054f3e902b12e0a9e7d205425c1538fecc0ec382a71fe996187054e3fb30b20e0a9e3f619641c153cdec22c8382a79dd8458c7054f3dacac10e0a9e7b591821c153cf6aa304382a79dd636047054e3f92f442c0a9cef6528858153ade4a30eb02a75ec9261d6054ebe922c3ac0a9c7fa6487581538feca10eb02a71fd989dd6054f379093bac0a9e6f2117658153af6492ecb02a75f5911d96054f37b0e422c0a9e6f21c84581538fe4c2e8b02a75dc9758d6054f3b90eb1ac0a9ee72116358153e6e43ac6b02a7e9c8458d6054e3f930b92c0a9d3f2597258153cde422e4b02a7b3c845496054e3f930b8ac0a9e6f2117158153dce42262b02a71fc985c16054f37908b82c0a9d7d2457058153abeca0eca82a757d921d95054eaf92eb22a0a9e5f21d6454153abe4bac4a82a757c975815054ee7928b02a0a9f5e25d6054153f9c4a2c0a82a7e79645815054e3f92f44280a9c7f65887501538fecc4eea02a71fc976194054ebd924bb280a9c7f6607650153adeca0eca02a75f5911d94054ebf3203b280a9d7725d6350153cee43ac6a02a7ed9635814054ebeb223b260a9c7f65887481538feca10e902a71fc976192054e3f92ec2240a9e7b21d5248153cf643a84902a71fd9621d1054e3f92ec3220a9d7b2497644153cee43ac6882a71fc976091054f2f90ea9220a9fdc50550441538f6c9510bb2a79d5836047654e3ed32c08eca9e5d255811d953a76492ed332a74f5911da6654e9eb223b2caa9d5b2497695553abac88ed2aaa71f5912197454eb5924bb488a9d6d6447691153aeac88ecb1aa78dc879996354e3b930ba2c6a9e6721e4458d53ce643904b1aa75d5911da3354e3eb22432e4a9c77261635c953f26b1ac4a92a70fc9661d4254e3d930bb444a9d796447688953ae64bac7112a71f4985c56154f2d90ea9242a9e7521d3148553fa2a926290aa75e4925da1154e3eb23442e0a9e3d206665c153cda40c88b82a79d4818cd7054f3c903112e0a9c7d262115c1538f74cb04382a78ee666087054f2dcaac10e0a9e6b911821c153ce649b04382a79cd636087054f39c66c10e0a9e7960a111c153abac88eca82a787c879995054f2790f222a0a9e5d21c8154153cba43c22a82a7e59635815054ebd32438260a9fd44c55044153af848ae1002a75e8925da0054ebe3223b400a9d7625d6380153 else 0x342068400004000000000000204010808100000000610182018403080003040608000083e2000412081303c400010208000000010142000000000000902120820000010200120420e01a2044101001803400190c10200100000e0320c01c0695000a0010200140020400241040000000200200000000000014200002000000384040808101034304070806100c2408400981e2000010040b0848100420584000840b08321c0038004001840d0d0010a438384190830107c20501a2020380870108321c081f104811081507c40084001068008041a042040405080a10142c0041f08521014341042008081a0021006820830100801004020802102c20187f77dffa1f2fde7b7f65eb7d47a3f3de67ca78ff01dc7b175deb1d4fa7749e75caf8e70de11c0f7a6e5dc1b6f616bdd49a2f43681cf99b734663cbd9672563bc6d8c716627c458770c609bf57aef35e1ba5736df5afb2d5f6bc555a8d5069952da5148e764dd99d3265d4ab94d25e444838fd1e63a46f8d516e2b45189911e2143d8710ce1741f83502e034017f8fddf43d9794eedd639d71cdfdb836b6a4d35a4343668c958b3075f0bcd722d558cadd542a3528a153b2674b09251d22b42480cfa1e53ac6f4d218b2f85dcb41592944ec9611d21c3fc780e11a430c5a0a512c21c3c0690a012c1e02d03c03c0047f652885d953ceec1b003b2a79f5816007654e3fd32c00eca9c7f640865d1538fe4bd10b22a75ec9261d6454e3fb2043ac8a9c7f6627759153af6492ecb22a75f5911d94354e3fb29442e4a9c7f64)
def x379h7 (i : Nat) : Nat := 0x921540c006c0a812803816000000000000001204a0ea1120141
def x379l7 : Packing := (173,4,6,4,4,11,0,x379d7)
def x379d8 (i : Nat) : Nat := (if i<2 then (if i<1 then 0xd849dd539fd829dd539fd819dd539fd809dd539fe885d953dec825d953cfd761d953bf5811d9539fe881d9539fd841d953ddd831d9539fd821d9539fd811d953df5811d9539fd801d9539fd87999539fc8799953cfd7699953cfc7699953cfd8799953cfc8799953cfe7799953edc8399953cfc7659553d7e7795553d7d7695553d7c7695553e7e66955539fe885d1539fc865d153cfe665d153d7e555d1539fd87591539fc8759153dbe7791153dbd7691153dbc7691153ebe6691153f3e55911539fd8758d53cfc7658d53bde8858d53ddc8758d53dde7758d53ddc7658d53edc7658d53ede6658d53f5c8558d53f5e5558d53ddd7458d53f9e4458d53fcc8258d53dde778cd53ddd768cd53ddc768cd53ede668cd53f5e558cd53ddd748cd53f9e448cd539fe885c9539fc865c953cfe665c953d7e555c953dbe445c953ddd635c9539fd87589539fc8758953edd6358953b7e8854953d7e7754953d7d7654953e7e6654953f3e4454953f5d6354953f6d62549539fd87509539fc8750953dee7788953ded7688953dec7688953eee6688953f6e5588953ded7488953fae4488953fcd63889539fe885c5539fc865c553cfe665c553dbe445c553ddd635c553dde335c553dee225c5539fd87585539fc8758553df571585539fd87505539fc8750553bde884c553dde774c553bdd864c553ddd764c553ede664c553f9e444c553f5d524c553fce224c553fd5614c5539fd87485539fc8748553f6d5248553fd53148553df67784553df57684553df47684553ef66684553df57484553fb64484553fd56384553fd63384553df57284553f755284553fe622845539fe885c1539fc865c153cfe665c153d7e555c153dbe445c153dde335c153d7d525c153dee225c153df4815c153ddd315c153df6115c153bed821c153df9701c1539fd861c153cfe661c153d7e551c1539fd841c153dbe441c153ddd631c153dde331c1539fd821c153dee221c1539fd811c153df6111c1539fd87581539fc8758153edd63581539fd8718153b7d8518153bdd8318153df87054153b7e8854153d7c8754153d7e7754153d7c7654153e7e6654153d7d7454153f3e4454153f5c8354153f5d6354153f5e3354153d7d7254153f6e2254153f748154153d7d7154153f5d3154153f761154153f787054153f7960541539fd87501539fc87501539fd874c153df8704c1539fd87481539fc8748153b7d8548153ded7248153f6d52481539fd87441539fc8744153fd53144153f7950441539fc8780153df97080153f795080153df88780153dfa7780153df97680153df87680153efa6680153f788580153f7a5580153df97480153fba4480153fd96380153fda3380153df97280153f795280153fea2280153df97180153fd93180153ff211801539f5811d9539ed821c153 else 0xfb0fc17d0be71ee6f4a790bc05dd4eca75539bdc9ee2f710b84dc0adf76f4b76dbacdc86dd36b1b4ed876b3b565a96d2b68133d19cccd8669b33995cca964db2118ecc7163631798b2c4b61eb0bd842c13602afdd7e4bed5efaf69774b9a5c62df96e0b625a5acad628b0657c2b61594abc552aa394eea57524a8ed45aa28511a855420a024f5a7093689a64c325e12d494a495244d1e68ca45e22b912e86e430214905281b3f91f48f767a43c69dfcee27633af1d40e9673d39c1ca8e387173801b80da46c435b1aa0cfe67132898c4c466032ff16e8b5859e2ba959caa054229114509fa4ef263122c8e845421e90988424131fe0fb87ae3c91d90e9073e3761b40d2067432c18a8bf85e02eb16a0ad051626b133091843a2060f306f434c17d0b3053c25e12108984141ee0e906d83581900c305a82c014409d04782040f806e030016c064000bfd849dd53dfd849dd53bfd841d953bfd821d953bfd801d953dfd801d953bfe8859153dfd8759153bfc8759153dfe7759153dfd7659153fdd6458d53dfc7650d53fbd5450d53dfd645c953bfe8858953bfc8758953dfe7758953dfd7658953dfd7458953fdd6358953f7d6454953bfe8850953bfc8750953dfe7750953bfd8650953dfd7650953fbd6450953fdd6350953fed6250953dfd645c553dfd625c553dfd425c553bfe8850553bfc8750553dfe7750553bfd8650553dfd7650553dfc7650553fdd6350553dfd7250553f7d5250553fbd4250553ff56150553dfc764c553ff5614c553fdd644c553fdd624c553fdd424c553bfe8848553bfc8748553dfe7748553bfd8648553dfd7648553bfd8448553dfd7448553fdd6348553ff56148553dfd645c153dfd625c153dfd425c153dfd415c153dfd215c153bfd861c153dfc761c153bfd841c153bfd811c153dfe661c153dfd651c153dfd641c153dfd541c153dfd621c153dfd521c153dfd421c153bfe8858153dfd8758153bfc8758153dfc8758153dfe7758153dfd7658153dfc7658153fbc8458153dfd7458153efd6458153fdd6358153dfd7258153f7d5258153dfd7158153efd6158153fdd3158153dfd7058153bfd8418153f7d6454153f7d6254153f7d4254153f7d4154153f7d2154153f7d6054153bfe8850153dfd8750153bfc8750153dfe7750153bfd8650153dfd7650153dfc7650153fdd6350153dfd7250153f7d5250153dfd7150153fbd4150153fdd3150153dfd7050153ff96050153f7d5050153dfc764c153bfd8648153bfd8448153fed5248153fed4248153fed2148153ff96048153bfe8844153bfc8744153dfe7744153bfd8644153dfd7644153dfc7644153bfd8444153dfd7444153fdd6344153bfd8244153dfd7244153f7d5244153ff54144153dfd7044153f7d5044153dfc76801539fd869dd539fc869dd539f) else (if i<3 then 0xf10240c204044502408a048110181a205c18404030a0411003e0438120440a04082e1510281020980c1e30b85428304042808103c3e20788041c0408180d1020202040444170a85061808903e20900041607884a1f101410202840a0810a42620521c405098810100000808200a20e034400c0001a300041a10c0381a3408a43e30c8600a0d2080482410804830404240d100520710200e20c84262410600a204044c10020208084810206040120409021090204820a0822680080010284180910a4080009901004100c0e2038604131488521f102c1020c0416081080060007902c1810801e2130204160b884006104c080f18582e21484d0231300041881084810e09040a0488061c0b8a460b0500052170e182a1f105c4820582052314880418c005c600ce070020201404270e1016090707081c0608060c0f88060b100c1a1e0e0c12050803c401f3014202018044a20182020c082020d08202040820c183060c1040052201c00401e180020008080229182c14030e1200180060010000211148c0070878522038400038408608a428008a42860c1c30708000008030170f8c38200f8c021008500114842417102c1a1e183452200840210fc0440380860210f8a441310083a18102e0e101c043010c04200000208084522010701406101004140041a06148c04140840200148c1403100c1a2410040a0d1898140310900410104062910800f0214920418106048114880902081b022012101412068e0e22105c3e20a8905020c08306080001041820008502100a44020587838302850c140040a1148190220220420dc0054620410a468208384c291801408028003027121c0a1028414080c894880081c522438408280f8d0e10b090482080404000a901600070140e06303452202840403020804031488005088c40202840c2010142051009001001c0c2910110e10c0144034384401028804241009041006040201004403058280825200820201800400100c1605020a4804100830050f8c0f821487c8100688300a8309880f148830201008382918142050814208082020c08006100002003840010a042001050410080481f0e130425028903e5dab6d23663b1ad866bfb5e1aebd736b63595abcd52ea5f501a69d2de91345ba16d0467eb3c79dece3e6e7345994cc365e32c394ac99e47322f900c74e34b1778a4c46e1db0bf848c18e06b0197ecbeadefaf4f790bb85d42e8572bb8a5bf6dcd6cfb5c5a86d03673b2e5916c5d617b0057cabb75c4ad6d65ab11583abf55e6ad7554a9ed4e2a3150aa7e5372979493a3e517289d437a19506e8093f69efcf227753ac9d3ce667173749b34d8669533c992cc5e6132f29724b5a57f29693fc9a24a323a911c8323fd1e78df469e3211798b1452e25711487a437618d0b8850c2060c3026807bfe1 else 0x800090010e00040c06881a1068410100010180043810602440308701020502040d082810206c0440c0a883e180841408100100a1020208080a02107040010e02040c0a881010102c10200201620400c408088818))
def x379h8 (i : Nat) : Nat := 0x400d0000705e900e1045507a8076e07be06cb0a80008b0365035801ca014c09670900000a0acf00700220000906e405f0000501d30563097e03890849018003240526080b01a000000000000009cd065f083707790aa7059f078802a9005f091504f40a20054d013e000709b807f808d50690000f0030000308c405050576041f021c087208aa0850000302e0000d0829098205ce063b009204a803bd00490232089d09e107210a58086a04860015071d09420660000d0680000804c8033b058e08ff03f7060e03a20a7e0027028906dc0408017e08e20124025106a4034a0678092a0a9c01b0000204e500c9046805bf062d0492047f0310099600f7024f02c201e10ab0000b0700000d01fa04d600be0a6d006d04200000000003e702930730000a0814030c075307400006043702d00000000e08b403c0000a039106f307de015609a0000e05a0000d088e0616064101070a3c02fc0950000c05d0000000000000000209d0000f0a030a40000c016107cb03d805300000000c04400000000e01100000000507e706b0000000050200000c00aa019407900000000f0930000702bb037c0270000000000000000b05560a1000030260000000090510000109f004b0d00008109031201030820060202151f14000c4d091c2b370100084401030100114e030602063829040803
def x379l8 : Packing := (344,3,6,8,4,13,0,x379d8)
def x379d9 (i : Nat) : Nat := 0x403802920280c01014920600188080b03000e405058180072028014900c006218721c80c0b020e004051e0706808629306c1030014940600a4808140a190d00400e7298007202080287430010039c0a00a480832120d0300406110d1987002906390400314906450143836001c190050052404260729182c00c430043901c1600a48080b03000e0c406030018872620306c14003149438201e0a00a4c1a16010e4c520c70d8205800629302c00043c314901c1618060080a4c0b02000e0c403e3880d800087862c043830c14061800a480d0f0c00386068020292c043038c140862001c80d045300400e58280071828086c003149a048200a418b03000c38702802920283038c9294c3029e1c141e00a480d00010f0c0a589386e84981c7ef7d279d77073b70e6e96ac68764a6255f05b358e5495245074ca4a547043b40e3d939c36732a2f52b02832662312141e71ca19516814b1160e90cc09f06202d000ffceea9ffd7654ffe3b2a7ff99953ffacaa9ffd7454ffeb22a7ff55153ffac6a9ffd4354ffeb92a7ff58953ffaa4a9ffd4254ffeb8aa7ff58553ffa82a9ffd3154ffe90aa7ff5c153ff8e0a9ffd6054ffe302a7ff54153ffa80a9ffd3054ffe902a7ff44153ffc00a9dfe7754efebb2a77f1d953dfccca9f7e5554efeba2a7ef91153fbac6a9fde3354efeb92a7df54953fdc44a9dfd7154fee98aa7fd84553bfae0a9dfc7054fbea82a7fe80153
def x379h9 (i : Nat) : Nat := (if i<1 then 0x60240000200b520a27016b8265010c60b60000704438062a126e07d00001c0988150904c5050482278017b01d6848201ed60052007e842c000e61250000202adc290a05e3078d810c80a2c12cc09b380a441df814eb0537816080c0e153c0154033a8248811ff0704812e8112c14f0000380f90198000000550000242228039208db053241cb409ac049d0200821ca1380000004780000000020a28006101280118f080000030210806b000020245823400ea000030038c10a40f900000045c0001c0b0f08310117422d809f0000000000001e028c0a0100c00000c1579068b036380e2a050b03f500d440b280a400002838e4202200b405e282b2c18041040000303e1803cc13d0000084280001200c00005811f4066000000000000000000000206ee019b405e605f000048343802301290000183ff41e52137a02ba8112803b00090000000000000000000002831240eb20b30000500c80000a102000058125c20ec0bb8000a010580c6802c7077000014124000030a9301f481976024601dd04c800000000e0998000000000000400f80003406ce0bd8086d0304823ac04ff001004a80000c04a00001022242720000d06d0046400000000a06280001c25c00000000580950295603c00000000081f6000020a5c83a680140000f027581cc00014003903788208000140d33097b8354000120cfc0aa202e001ee20e2c0a22839fc11e20baa03e7014d805cc02620893010ac10e001ac040980fd40f4a083201180001820be05d0000004b54262600800006840c4119208b701a603d2428d20f520470000181a84012c011780ac000020c7c04e80000c2866109f0206043201b280b20000402280001a07b00002048840ee8014100af848c00000000c00dd02a740e860a000001018b80da80909072501a080ff805560a69026d4195c038309f101d9c0dd8078000000000c1d1c156006da004cc0400000000000001c0cb405ca0a3b82110032c072b08a40327018400aec06f302fdc04261422070a01a4c12ee1518058982b5425160cda01b8037f427e60e6907e00003018d0056d05be83480000e0d7709d984ea41e7e0fe704f181500001c052805180002c0080000300b0000000002134905af01e68138e0b90000000f4024200003046f019141516130b0aa80003c292e0f0800800003803880dc9061e8034016800007013f02bc409a0000c09e3829400d4a00600007035a81d6a0bee036784af80b6a0000000000000001e11cf076800038191c09600007828400012070000000002424e2095907e80003c26a410f203080000000060ec8053c019c18d26002060a0590000803011fb47834c1821f140828214126840a588801a1008804002880018288000c4a43220482017c005080c080029879e0024000000cd22220990c0411100000018e else 0x108af0118000000)
def x379l9 : Packing := (48,2,6,9,4,12,0,x379d9)
def x379d10 (i : Nat) : Nat := 0x1c30ffd53
def x379h10 (i : Nat) : Nat := 0xe01181b00000008076c1ff05981a0000825000000000000000000000f0280000000000000000050b402a0000829000240c00664282053c2000000000002011705f015304d40800000000002405c09900be04ac23700680360ac0001018000d0b00000000000f00b810d0600000000000f01d00ef03c000e07ac09909c000f000000000182f000081c9084000808a40d0000424f0b80000882400001b8400
def x379l10 : Packing := (1,1,6,6,4,0,0,x379d10)
def x379columns : List ColumnInfo := [(32,0,859,0,8),(8,0,883,0,8),(2,0,889,0,8),(576,0,313,0,7),(528,0,355,0,7),(1,0,890,0,7),(578,0,313,0,7),(536,0,355,0,7),(512,64,57,258,6),(512,16,354,9,6),(512,8,99,272,6),(512,2,312,65,6),(264,0,627,0,5),(768,64,57,2,5),(768,8,99,16,5),(576,2,312,1,5),(40,0,851,0,5),(34,0,857,0,5),(33,0,858,0,5),(528,8,99,256,5),(10,0,881,0,5),(520,16,354,1,5),(3,0,888,0,5),(514,64,57,256,5),(513,16,354,8,5),(513,2,312,64,5),(784,0,99,0,4),(258,0,57,0,4),(864,0,27,0,4),(834,0,57,0,4),(792,0,99,0,4),(784,8,99,0,4),(770,64,57,0,4),(610,0,281,0,4),(586,0,305,0,4),(579,0,312,0,4),(577,2,312,0,4),(561,0,330,0,4),(35,0,856,0,4),(538,0,353,0,4),(537,0,354,0,4),(521,16,354,0,4)]
def x379levels : Nat → Packing
  | 5 => x379l5
  | 6 => x379l6
  | 7 => x379l7
  | 8 => x379l8
  | 9 => x379l9
  | 10 => x379l10
  | _ => emptyPacking
def x379index : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 3 0 9 1 4 x379h6
  | 7 => lookupWord 3 18 3 12 4 4 x379h7
  | 8 => lookupWord 43 225 8 16 8 4 x379h8
  | 9 => lookupWord 86 450 7 17 9 4 x379h9
  | 10 => lookupWord 12 86 5 14 6 4 x379h10
  | _ => fun _ => none
def x379 : Forest := ⟨891,10,fun j => x379samples[j]?.getD (0,0),x379columns,x379autos,x379levels,x379index⟩
set_option maxHeartbeats 0 in
theorem geomx379 : graphValid x379 (boundsBefore knownx375) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=2) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3795_0 : block x379 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx3795 : block x379 5 0 1=true := sx3795_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3796_0 : block x379 6 0 5=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3796_5 : block x379 6 5 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx3796 : block x379 6 0 12=true := (@block_merge x379 6 0 5 7 sx3796_0 sx3796_5)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3797_0 : block x379 7 0 36=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3797_36 : block x379 7 36 20=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3797_56 : block x379 7 56 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3797_92 : block x379 7 92 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3797_128 : block x379 7 128 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3797_164 : block x379 7 164 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx3797 : block x379 7 0 173=true := (@block_merge x379 7 0 164 9 (@block_merge x379 7 0 128 36 (@block_merge x379 7 0 92 36 (@block_merge x379 7 0 56 36 (@block_merge x379 7 0 36 20 sx3797_0 sx3797_36) sx3797_56) sx3797_92) sx3797_128) sx3797_164)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3798_0 : block x379 8 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3798_2 : block x379 8 2 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3798_38 : block x379 8 38 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3798_74 : block x379 8 74 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3798_110 : block x379 8 110 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3798_146 : block x379 8 146 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3798_182 : block x379 8 182 25=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3798_207 : block x379 8 207 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3798_243 : block x379 8 243 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3798_279 : block x379 8 279 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3798_315 : block x379 8 315 29=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx3798 : block x379 8 0 344=true := (@block_merge x379 8 0 315 29 (@block_merge x379 8 0 279 36 (@block_merge x379 8 0 243 36 (@block_merge x379 8 0 207 36 (@block_merge x379 8 0 182 25 (@block_merge x379 8 0 146 36 (@block_merge x379 8 0 110 36 (@block_merge x379 8 0 74 36 (@block_merge x379 8 0 38 36 (@block_merge x379 8 0 2 36 sx3798_0 sx3798_2) sx3798_38) sx3798_74) sx3798_110) sx3798_146) sx3798_182) sx3798_207) sx3798_243) sx3798_279) sx3798_315)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3799_0 : block x379 9 0 19=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3799_19 : block x379 9 19 29=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx3799 : block x379 9 0 48=true := (@block_merge x379 9 0 19 29 sx3799_0 sx3799_19)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx37910_0 : block x379 10 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx37910 : block x379 10 0 1=true := sx37910_0
theorem tablesx379 : checkedTables x379 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x379 0 0 0 = true)
  · exact (rfl : block x379 1 0 0 = true)
  · exact (rfl : block x379 2 0 0 = true)
  · exact (rfl : block x379 3 0 0 = true)
  · exact (rfl : block x379 4 0 0 = true)
  · exact allx3795
  · exact allx3796
  · exact allx3797
  · exact allx3798
  · exact allx3799
  · exact allx37910
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx379 : Lower (varsX 891) (graphGoal 891) 11 :=
  strong_low (m:=891) (cap:=10) (hints:=12901695489) (by decide +kernel) (plainB (q:=379) (prior:=boundsBefore knownx375) (before_sound knownx375 validx375) (by decide +kernel))
    (index_root (g:=x379) (i:=0) rfl (before_sound knownx375 validx375) geomx379 tablesx379 (by decide +kernel))
def mapsx379 : List (Nat × List Nat) := [(891,[])]
def knownx379 := extendKnown knownx375 11 mapsx379
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx379 : Known knownx379 := extendKnown_ok (m:=891) validx375 lowx379 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx381 : Lower (varsX 893) (graphGoal 893) 9 :=
  strong_low (m:=893) (cap:=8) (hints:=13019128580) (by decide +kernel) (plainB (q:=381) (prior:=boundsBefore knownx379) (before_sound knownx379 validx379) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx379) (before_sound knownx379 validx379) (576,0,317,0,8) (by decide +kernel) (by decide +kernel))
def mapsx381 : List (Nat × List Nat) := [(893,[])]
def knownx381 := extendKnown knownx379 9 mapsx381
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx381 : Known knownx381 := extendKnown_ok (m:=893) validx379 lowx381 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx382 : Lower (varsX 894) (graphGoal 894) 9 :=
  strong_low (m:=894) (cap:=8) (hints:=12910272800) (by decide +kernel) (plainB (q:=382) (prior:=boundsBefore knownx381) (before_sound knownx381 validx381) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx381) (before_sound knownx381 validx381) (32,0,862,0,8) (by decide +kernel) (by decide +kernel))
def mapsx382 : List (Nat × List Nat) := [(894,[])]
def knownx382 := extendKnown knownx381 9 mapsx382
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx382 : Known knownx382 := extendKnown_ok (m:=894) validx381 lowx382 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx471 : Lower (varsX 983) (graphGoal 983) 8 :=
  strong_low (m:=983) (cap:=7) (hints:=26323452161) (by decide +kernel) (plainB (q:=471) (prior:=boundsBefore knownx382) (before_sound knownx382 validx382) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx382) (before_sound knownx382 validx382) (256,0,727,0,7) (by decide +kernel) (by decide +kernel))
def mapsx471 : List (Nat × List Nat) := [(983,[])]
def knownx471 := extendKnown knownx382 8 mapsx471
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx471 : Known knownx471 := extendKnown_ok (m:=983) validx382 lowx471 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx478 : Lower (varsX 990) (graphGoal 990) 9 :=
  strong_low (m:=990) (cap:=8) (hints:=13438755104) (by decide +kernel) (plainB (q:=478) (prior:=boundsBefore knownx471) (before_sound knownx471 validx471) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx471) (before_sound knownx471 validx471) (128,0,862,0,8) (by decide +kernel) (by decide +kernel))
def mapsx478 : List (Nat × List Nat) := [(990,[])]
def knownx478 := extendKnown knownx471 9 mapsx478
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx478 : Known knownx478 := extendKnown_ok (m:=990) validx471 lowx478 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx499 : Lower (varsX 1011) (graphGoal 1011) 9 :=
  strong_low (m:=1011) (cap:=8) (hints:=22833790977) (by decide +kernel) (plainB (q:=499) (prior:=boundsBefore knownx478) (before_sound knownx478 validx478) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx478) (before_sound knownx478 validx478) (128,0,883,0,8) (by decide +kernel) (by decide +kernel))
def mapsx499 : List (Nat × List Nat) := [(1011,[])]
def knownx499 := extendKnown knownx478 9 mapsx499
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx499 : Known knownx499 := extendKnown_ok (m:=1011) validx478 lowx499 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx501 : Lower (varsX 1013) (graphGoal 1013) 8 :=
  strong_low (m:=1013) (cap:=7) (hints:=22145926916) (by decide +kernel) (plainB (q:=501) (prior:=boundsBefore knownx499) (before_sound knownx499 validx499) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx499) (before_sound knownx499 validx499) (576,0,437,0,7) (by decide +kernel) (by decide +kernel))
def mapsx501 : List (Nat × List Nat) := [(1013,[])]
def knownx501 := extendKnown knownx499 8 mapsx501
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx501 : Known knownx501 := extendKnown_ok (m:=1013) validx499 lowx501 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx505 : Lower (varsX 1017) (graphGoal 1017) 9 :=
  strong_low (m:=1017) (cap:=8) (hints:=14361313284) (by decide +kernel) (plainB (q:=505) (prior:=boundsBefore knownx501) (before_sound knownx501 validx501) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx501) (before_sound knownx501 validx501) (128,0,889,0,8) (by decide +kernel) (by decide +kernel))
def mapsx505 : List (Nat × List Nat) := [(1017,[])]
def knownx505 := extendKnown knownx501 9 mapsx505
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx505 : Known knownx505 := extendKnown_ok (m:=1017) validx501 lowx505 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx506 : Lower (varsX 1018) (graphGoal 1018) 8 :=
  strong_low (m:=1018) (cap:=7) (hints:=14251409504) (by decide +kernel) (plainB (q:=506) (prior:=boundsBefore knownx505) (before_sound knownx505 validx505) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx505) (before_sound knownx505 validx505) (128,0,890,0,7) (by decide +kernel) (by decide +kernel))
def mapsx506 : List (Nat × List Nat) := [(1018,[])]
def knownx506 := extendKnown knownx505 8 mapsx506
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx506 : Known knownx506 := extendKnown_ok (m:=1018) validx505 lowx506 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx508 : Lower (varsX 1020) (graphGoal 1020) 9 :=
  strong_low (m:=1020) (cap:=8) (hints:=13563536128) (by decide +kernel) (plainB (q:=508) (prior:=boundsBefore knownx506) (before_sound knownx506 validx506) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx506) (before_sound knownx506 validx506) (592,0,428,0,7) (by decide +kernel) (by decide +kernel))
def mapsx508 : List (Nat × List Nat) := [(1020,[])]
def knownx508 := extendKnown knownx506 9 mapsx508
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx508 : Known knownx508 := extendKnown_ok (m:=1020) validx506 lowx508 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx255 : Lower (varsX 767) (graphGoal 767) 12 :=
  strong_low (m:=767) (cap:=11) (hints:=553656577) (by decide +kernel) (plainB (q:=255) (prior:=boundsBefore knownx508) (before_sound knownx508 validx508) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx508) (before_sound knownx508 validx508) (576,0,191,0,11) (by decide +kernel) (by decide +kernel))
def mapsx255 : List (Nat × List Nat) := [(767,[])]
def knownx255 := extendKnown knownx508 12 mapsx255
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx255 : Known knownx255 := extendKnown_ok (m:=767) validx508 lowx255 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx479 : Lower (varsX 991) (graphGoal 991) 12 :=
  strong_low (m:=991) (cap:=11) (hints:=13438558465) (by decide +kernel) (plainB (q:=479) (prior:=boundsBefore knownx255) (before_sound knownx255 validx255) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx255) (before_sound knownx255 validx255) (128,0,863,0,11) (by decide +kernel) (by decide +kernel))
def mapsx479 : List (Nat × List Nat) := [(991,[])]
def knownx479 := extendKnown knownx255 12 mapsx479
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx479 : Known knownx479 := extendKnown_ok (m:=991) validx255 lowx479 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx503 : Lower (varsX 1015) (graphGoal 1015) 12 :=
  strong_low (m:=1015) (cap:=11) (hints:=22028484865) (by decide +kernel) (plainB (q:=503) (prior:=boundsBefore knownx479) (before_sound knownx479 validx479) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx479) (before_sound knownx479 validx479) (528,0,487,0,11) (by decide +kernel) (by decide +kernel))
def mapsx503 : List (Nat × List Nat) := [(1015,[])]
def knownx503 := extendKnown knownx479 12 mapsx503
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx503 : Known knownx503 := extendKnown_ok (m:=1015) validx479 lowx503 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx507 : Lower (varsX 1019) (graphGoal 1019) 12 :=
  strong_low (m:=1019) (cap:=11) (hints:=14243872769) (by decide +kernel) (plainB (q:=507) (prior:=boundsBefore knownx503) (before_sound knownx503 validx503) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx503) (before_sound knownx503 validx503) (128,0,891,0,11) (by decide +kernel) (by decide +kernel))
def mapsx507 : List (Nat × List Nat) := [(1019,[])]
def knownx507 := extendKnown knownx503 12 mapsx507
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx507 : Known knownx507 := extendKnown_ok (m:=1019) validx503 lowx507 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx509 : Lower (varsX 1021) (graphGoal 1021) 12 :=
  strong_low (m:=1021) (cap:=11) (hints:=13555999492) (by decide +kernel) (plainB (q:=509) (prior:=boundsBefore knownx507) (before_sound knownx507 validx507) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx507) (before_sound knownx507 validx507) (576,0,445,0,11) (by decide +kernel) (by decide +kernel))
def mapsx509 : List (Nat × List Nat) := [(1021,[])]
def knownx509 := extendKnown knownx507 12 mapsx509
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx509 : Known knownx509 := extendKnown_ok (m:=1021) validx507 lowx509 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx510 : Lower (varsX 1022) (graphGoal 1022) 12 :=
  strong_low (m:=1022) (cap:=11) (hints:=13446095136) (by decide +kernel) (plainB (q:=510) (prior:=boundsBefore knownx509) (before_sound knownx509 validx509) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx509) (before_sound knownx509 validx509) (528,0,494,0,11) (by decide +kernel) (by decide +kernel))
def mapsx510 : List (Nat × List Nat) := [(1022,[])]
def knownx510 := extendKnown knownx509 12 mapsx510
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx510 : Known knownx510 := extendKnown_ok (m:=1022) validx509 lowx510 (by decide +kernel)
def lived8 (i : Nat) : Nat := 0x28ae2e79ecc61152601605927cb1e7b75525056044164
def livel8 : Packing := (2,7,8,0,4,3,0,lived8)
def lived9 (i : Nat) : Nat := 0xd0383e0407c080800007c04107c02107c04100000f8082000000d5d0bdaa97928d8883706b5853403b36312c19140f0a0500a2feebd77552a4c82c945fdd7aeda954980592b97baf5db08a92c0b2553f75ebb64d52581649a7eebd98a9322b02c93cbdd7b31525056059279f3af662a4c02c0b26eaeb31845498058164a2feebd76d4aa4982c94cfdd7aeda6549305928bfbaf5db30d2a40b24b6f75ecc695844816492feebd98d2b26902c92cfdd7b31a558d205928bfbaf5db52a9220b24f3e75ecc5496044164bf596eaa4a0ac0882c9f761935495148110593fcc2c6a92a290220b2762eaee776118058164ed1d5dcaac2300b02c9daaabb6122260160593f454aac2444c02c0b27f88956225056044164
def liveh9 (i : Nat) : Nat := 0x907040000
def livel9 : Packing := (24,6,8,1,4,8,0,lived9)
def lived10 (i : Nat) : Nat := (if i<1 then 0xa7ecca6562260164e76da995622601649cfdc7aed5258164ee6eaa9562258164fe2e556122258164f66e5564e2258164f66e558899158164fe2e5588941581649eecc26dd3158164dcfabb9dd8058164de7abb9558058164fababb6118058164fab9b76118058164fab9b56118058164fab9846c98058164fab9845498058164deeabb8898058164fe6a55889805816487fccbaa99254164a7edc96a22254164a7ecca6622254164a7ecca64e2254164dbbabb6118054164ebbaaa6118054164fba9848898054164e76da9956224c164ee6da6956224c164cef9a6aed804c164ecf9a69dd804c164ee79a6955804c164eee9a6889804c164fbd1814c5804c164a3fcc86a5a848164a7f4c16a5a848164a7f4c16e5a848164a7f4c16a5a548164a7f4c16e5a548164c77db9955a54816487fdc82e9954816487fccbaa9954816487fccb6a19548164a77dc9aaa5548164b774c16a65548164a77dc96a25548164a77cca6625548164c77cba9559348164b7e4c16a55248164fec5634c52148164ff49535493048164ffc1314853048164c5fdb99dda244164c7edb9889a244164a7edc96962244164e76da99562244164fe6a558896044164feb1525056044164ff61525452044164dfb2bb5052044164ff32555052044164ffa1525052044164dcfabb9dd6380164de7abb9556380164fcda7760d6380164fe5a5560d6380164f37a889559280164b7d8c36e5828016497f8cb6558280164d779b99558280164fad98358d82801649df9c7aed528016497f8cb6615280164d3f9b9a21528016497f8cb64d5280164f3ea886562280164b7e9c96162280164f769989562280164fb6a889562280164ff2a556122280164f76a5564e2280164beeacc58e2280164fe6a5558e2280164fec98358e2280164ff4a558ce2280164f1fa889dd9180164f37a889559180164f3ea888899180164f76a558899180164d5f9b99dd8180164ddb9b49dd8180164d779b99558180164df39b49558180164d7e9b98898180164dfa9b4889818016497f8cb661718016497f8cb64d7180164a7f8ca6e55180164d7e9b98895180164f9ba889dd4180164fb3a889554180164fbaa888894180164ff2a5588941801649fe8c26dd3180164dedabb58d3180164fcda7758d3180164fe5a5558d3180164fec9638893180164d779b99552180164fed1634c52180164f5f27764e1180164fcf27758e1180164fbd2888ce1180164fdd2778ce1180164b7f1c954a1180164f7e19888a1180164fbe28888a1180164f7e19588a1180164ff625588a1180164ffa18488a1180164f7e19388a1180164fee16388a1180164ffc23388a1180164dababb6118058164f8ba776118058164fa3a556118058164faa9848898058164a774c16a65548164fcb2775056044164fea2225056044164 else (if i<2 then 0x68e0b8299008860b04e8fc021f0085c1703d100103d0c0f420f0087c02141206c021f0087c021d0587c02100000f008400f010487a100000003c0210780420f00876001d8004046141207c021f0087c021f0087c02181e8607a181e8507a10380420f010400b058400003c021078082081ec0d0540e706b82e07b0342d039c1703d81a1181d60d41ea0d084070c0f6068e0d705c14cb03d81a38360a64f65f53f41f22f03ef1edfecdec8eb6eb1eace9ae7be69e57e38e26e07de8dd6dc4db2da0d8ed89d77d58d39d1ad08cf6ce4cd2cc0caec8fc7dc6bc59c47c35c16bf7bd8bc6ba7ba2b90b71b5fb4db48b29b17b12b00afbae9acaa9ea99a87a75a56a44a25a06a019e29d09b19ac98d98897696495294d93b9369319058bf89386782181c8177f87e67d47c27b079e78c78777576375173f72d7016ef6dd6cb6b96a769567665761e60c5fa5e85d65c45b258655a53b5295175055004fb4c249648447245344e44943742542040e3fc3ea3d83c63b43a239038b38638137c36a36536034e33c33733232d32832331e30c3072f52f02de2cc2ba2a829628427226024e23c22a2182061f41ef1dd1d81c61c11bc1aa1a51a019b19618417f16d1681491030ca09107f039000c7febbaa952641649dfdc7aed5260164af7dc5aa95260164c7febb6a55260164eedd636a1315c164debebb6115258164d6febb64d5258164b6fecc5499158164bebecc5494158164befacc5cd8058164befacc5498058164fbb98448580541649dfdc7aed524c164c7febb6a5524c164cefebb699524c164eef9a6549804c164c7febb661a548164b7f4c16a58548164afbecc6958448164a7fecc6959348164aefecc6956348164c7fdb96958148164cfbdb46958148164d7edb95498148164dfadb45498148164f76d935495148164fe6d6354951481648ffdc52e93148164eedd636a13148164eedda558d3148164cfecba5493148164fecd635493148164d7ed986d52148164dfadb56112148164d7edb564d2148164deedb558d2148164def9606e17344164c7fdb7661a244164cfbdb7611a244164c7fdb764da244164cefdb758da2441649dfdc7aed5244164c7febb6a55244164c7fdba64d5244164cefdba58d5244164befacc5cd6044164befacc54d6044164befacc5496044164fe79535496044164bef9c54c96044164f7e9985492044164ffa9845492044164f7e9935492044164fee9635492044164ff69535492044164f7f1935452044164fef1635452044164ffb1855052044164c77e556d6aa6496497edc2aeda95496495fdc7aed5264164e76eaa9562264164cef9606c6aa60164c77cb56a5a76016487fccbaa99760164a5fdc9aaa776016487fdc22e9956016487fccbaa99560164a7ecc26a5a26016487fccbaa99260164a7edc9aaa2260164 else 0x17004c5e0e0e83420260098907bc0b150383c080f0202081e8400f070404c01317808281808098026230384029e01100980262f0105048141206c081412041e020804c01c203f20f4503de0688042141e878101829878101e088507ae0e12048360e0a048360e0f83820260098809603f1002ac1c281e8607ba0e10107a181ed83448240f8042041ef808483d083c04107804200003d0bc060661170c00220a81020570438b6001037025840570438800250480bc021212106040d02703840a07078101e04040206080002b02002406e0bf0350380f209b2c06009009b1b0380f209b1817409083db05a0d0a0001901122f0087c021f0087c021f0087c0210780828180a06028180a060203d11a026c66030981c26070981c26070a04c206b04a880ce0871009f80c09c04393c021f00848261f0087c0213038701be020508cc1683d0478fc1c0a115c003e010f80420040f6))
def liveh10 (i : Nat) : Nat := 0x9063914001010000784c0002480005006025e07429d824001c15f07b808001a0e1230002810cf43068800001551902685940ca174028000806000605382c0018148088000a308f
def livel10 : Packing := (199,5,8,5,4,12,0,lived10)
def lived11 (i : Nat) : Nat := (if i<4 then (if i<2 then (if i<1 then 0x64600593bfcc2b23002c9dfe6099180164eff2a4c8c00b27dfa7760600593fbd2ab03002c9ff68cd8180164f7f304c0c00b27fea2260600592ffd5dae3002c97fe6e17180164eff330b8c00b27bfa885c600593efcc3ae3002c9fee6117180164eff326b8c00b27ef9635c600593fed19ae3002c97feaed5180164eff372a8c00b25ff9b854600593bfccc2a3002c9efea215180164ff7308a8c00b277f99354600593f7cb1aa3002c9ff68cd5180164eff324a8c00b27f795254600593ff5112a3002c9ffc6055180164ff730ea0c00b27fb98550600593fdcc1283002c9fee5494180164bff57698c00b25ff9b84c600593dfd44263002c97fe6dd3180164fbf4ee98c00b25ff9b54c600593fbd2aa63002c9ff64c93180164ffd44498c00b27ff1814c600592ffd5da43002c9dfe6e52180164bff37090c00b277f99848600593dfd44243002c97fe6d52180164eff32a90c00b27f7a5548600593fdcc2243002c97fe6cd2180164eff32690c00b27ef96348600593fed19a43002c9ffc4c52180164ffe30708c00b27ff17384600593ff8c1423002c9ffc54a1180164ffe26508c00b247fdb5aa9925926fedbd54a92c95fbaed9588964cbfd553bb20b2677eaa955905933f755444c82c9ddb95622641648ff974cbb00b265fda99dd805923fe5d32ac02c99df6a655601648ff974c9300b267eda98898059367f554eeb02c9b9faaa5558164f97ceec22c0b27e3e5561160593a7f3bb26b02c9d9f9559358164dddd55112c0b276ed9588960593f372ac44b02c9fab6122258164eddb27112c0b274fe7764560593b3f2ab22b02c9dbb8899158164f97ceea0ac0b27eae2250560592f7d5db00b02c9f3e9dd8058164fcf4aac02c0b27eea22601605933f6d4c44a82c9eee6118054164cbfb533ba60b26cfe77699305933f6d4c44982c9bbb69a224c164afe962d4a40b247fcba655205933bed4caa902c997f6a67744164cfdb5311220b27cfa7758110593f3d2aac0882c9fba8896044164ff628290220b273fa8865e00593afccc4ef002c9e7ea227780164e7f510cac00b277799895600593dbd444ab002c9f6e9dd8480164fe74aac2400b275fa7764e00593bbd2ab27002c97beaed6380164f9f4eeb1c00b27e7a5558e00593f6cc1ac7002c9f769de3380164e7f510c9400b2777a5564a00593bf4cc445002c9efaa222280164efd32b11400b27f6a5588a00593fd4c2445002c9dfa64e2280164fdd2c711400b27fca3388a005939fd44323002c9d7e9dd9180164eef4aac8c00b277ea2264600593ddd44283002c9f6e9dd4180164fe74aaa0c00b27faa2250600593f6cb1a63002c9dfc65e1180164fbe4ef08c00b277f19384600593f78b1c23002c9ff48ce1180164efe32508c00b27fe22284600593d5cc2300b02c9fac5056044164 else 0xc99ff6a195481649ffb74c2a40b26f7eaa95520593bbed4caa902c9bdf6a25548164eefb312aa40b26fbeaa611205937ded2b08902c9fcf95584481649ffd76d1a40b26f7e5568d205933ff55326902c99ff6959348164eefcaac9a40b25efebb58d2059377f552c6902c9bbf6956348164fcfcaab1a40b24ffdba54d205927fe5d2a6902c97fbaed5248164dfdd54a9240b277edb954920593bf6d4aa4902c9bfb6a15248164efdb30a9240b27fad8454920593bf6c9aa4902c9fbb58d5248164fedaa6a9240b267fda9685205933ff55322902c99ff6a19148164cffb4ac8a40b2777e5564520593bf6a9322902c93ff2e95148164fedaa4a8a40b26fbeaa505205937ded4282902c9bef6954148164fe7caaa0a40b27fad52505205927fe5d262902c9bf768d3148164fdbac698a40b25feebb485205937f755242902c9dfb6e52148164efdb5290a40b277ed9848520592ff6daa42902c9dfb6552148164fedcaa90a40b27fad8448520593bf6c9a42902c9fbb58d2148164ffca6290a40b26ffaaa4c1205937fcd4260902c9fde9553048164ffb2a698240b27fe9524c120593fec98a60902c9ffa48530481649ffd76d1a20b26dfe7768d105933fed3b26882c9d7f9dd93441649ffb74c1a20b26efda758d10593e7f3bac6882c93ffaeda244164cffb72d1220b267fd98689105933fecbb44882c9b7f9dda244164df7b08d1220b267fd936891059377eb1b44882c99ff649a244164dfdc44d1220b267fda5649105927fedd304882c93ff6e95244164cffb52a9220b24ffdba4c9105937f6d4444882c9dfb6622244164dfdb4b11220b277ed9588910593fb72ac44882c9feb6122244164dfdb4711220b277ed9388910593f76b1c44882c9fbe5cd6044164fdf2a6b0220b27ef95258110593f7c992c0882c97feaed2044164eff37290220b277f99848110593bfccaa40882c9fde9552044164ff730890220b26ff9a348110593bfcc9a40882c9fbe58d2044164ffd2a490220b27ff15148110592ffd5db0f002c97feaed8580164eff372c2c00b277f98764e00593bfcc2b27002c9f7e9dd8380164fef4aac1c00b25ffabb5ce00592ffcdc2e7002c9f7e61d7380164fdf30eb1c00b27ef98558e00592ffd5daa7002c97fe6e15380164fef30aa9c00b27fd98354e00593bfcc2b25002c97feaed8280164eff372c1400b277f99560a00593fbd2ab05002c9dfe64d8280164f7f306c1400b27ef96360a00592ffd5daa5002c9dfe6e55280164bff370a9400b277f99854a00593dfd442a5002c9fee6115280164eff326a9400b27ef96354a00593fbca9aa5002c9ff68cd5280164ffd304a9400b25ffabb4ca00592ffcdc265002c97fe6d53280164fef4aa99400b27fe9824ca00593ff4c2c45002c9ffa60e2280164ffd2a711400b277f987) else (if i<3 then 0x298240b25ffebb5cd10592ffedc2e6882c9bff6a17344164fbfb0eb9a20b26ffd87689105937feb9b44882c9bff609a244164dffaa4d1220b25ffebb609105937fed2b04882c97ffaed5244164dffb74a9220b277fdb9549105937fed1aa4882c9dff64d5244164fdfac6a9220b27fed8254910592ffedc264882c9bff6a13244164bffb6a99220b26ffda54c910593ff6c1264882c9ffe6152044164fff30690220b27ff95348110592bff5db52a92c99ff6a5a054964affd76a9320b267fdba549905933ff552a4c82c93ff6d6aa601649ffb6555300b24ffdb1aa9805933ff55352c02c99ff6a5a760164cffd54cbb00b26dfeaa9dd80593afed4ceec02c99ff6a5a560164cffd54cab00b26f7eaa95580593bbed4caac02c99ff6a5a260164cffd54c9300b2777e55649805933fed4aa4c02c9bfbaaa2260164efdb5311300b277ed9588980593fb72ac44c02c99ffaa99160164ebfceec8b00b2777e5564580593bf711322c02c93ff2e93160164cffb30d42e0b26bfe886a1705937dec2350b82c99ffaa9985c164cffd54c9ae0b267feaa645705933fed4322b82c9d7f64d715c164bdfd76c3ac0b25efebb5cd6059377f552e6b02c9f3f61d7358164bdfd76a92c0b26efeaa54960593f5ec22a4b02c9dbf64d5258164edfaa4c8ac0b25efebb5c560593f5ea9282b02c97bfaed3158164bdfb6e98ac0b27cfe774c560593f3f2aa62b02c9fbb8893158164fdf576c02c0b27ef9b760160593f7cdab00b02c9fbe6cd8058164fdf2e6c02c0b27ef9b260160593f7ca9300b02c99ff6a5a8541649ffd76d42a0b267fdb96a1505933fecc350a82c9affa21a854164df7b08d42a0b267feaa661505937df55308a82c99ffaa99354164bdfd76b1aa0b26efeaa58d505933fed4b44a82c99ffaa99254164cffb50c92a0b26feeaa88950593bf6d4c44a82c9bfb6a22254164efdb31112a0b27fad8488950593bf6c9c44a82c9fbb58e2254164cffb52d0aa0b267feaa645505933fed4322a82c9dfb8899154164df7d54a0aa0b26fbda850550593fd711282a82c9fb758d3154164bff576c02a0b26ffaaa60150593bfcdcb00a82c9dfe6a58054164eff326c02a0b27ef96360150593bfcc9300a82c9ffa8898054164eff322c02a0b27fb941601505933fed4aa4982c9bbf699524c164fedcab11260b25ffabb60130593efd3bb00982c9efe615804c164fef4aac0260b27fea2260130593dfcc0b00982c9ff64c5804c1649ffb7155240b24ffdb5aa9205927fed9d54902c93ff6c6aa48164cffd54d4a40b267fda96a1205927ff5db50902c99ff6e5a848164cffb30d4240b26bfe886a1205937dec2350902c99ffaa99848164cffb52d2a40b24ffebb695205933fedcb4a902c99ff661a548164cffb2ad2a40b26f7e55695205933ff5532a902 else 0xc054fea98951ca9f85386a6694b2a924520ea34944ea8685066a089408a7e84f7e9e293aaa7204e1e9b99358a67c4ca69909312a6144bd697092cca5704a769479274a4cc492e9189222a41047e68ef91c4a378469e8c69178a2c8456e8a09126a21843c686b90c8a17442c6851909aa11841f68379060a080407e8028fea9fc43f1e7d38f929f143dd67ad8f409e403c2e77e8eee9dc03b5e7618eb49d4c3a5e7448e7a9ce439a67308e529c8838ee7168e1e9c20381e6fc8df09bc437666e58dbc9b68367e6c88d829ae835966ab8d4e9a7434c66918d149a0033c66748ce099a4330e65a8ca69930320e63d8c7298c8316e6298c44986c30b660f8c16981c30165fe8bee97c02f5e5e48bba97582e765c78b8696f02d8e5ad8b5296942d0659c8b2a96382c3657f8aea95b82b3655f8ab095442a4e5428a7694dc297e5288a42945c287e50b8a0e940027c64f489da93a426f64d789a09324260e4b1893c9244240647388cc914021e642f8838903c1ff63f187c88f681e4e3bc87588e7c1ca638786fa8dc01b16352868a8ce0195632086328c30180e2f785d48b5c164e2b985588a7c14d628784f489a812e624f848a88ec113e21a841487e80f661dc83a487140dd61a7832886340bfe17582d685780a8613d825a848008660ff81ea838806be0cd818c82e405760a481348234041607580d68178029e046807880d4013e02080208000bffd76d02a4b26ffda8681525937fed1b40a92c9bff685a054964effb70a9320b277fdb354990593bfed8aa4c82c97ffaed5260164dffb74a9300b26ffeaa54980593bfed4aa4c02c9dff5499160164dffd5498b00b25ffebb4c5705937ff55262b82c9bff6a1315c164fdfb70a92c0b27efdb354960593f7ed8aa4b02c9fbf5493158164effb30d12a0b27fbd8468950593bfec9b44a82c9fbf58da254164dffd54992a0b25ffebb4c5505937ff55262a82c9bff6a13154164dffd5490aa0b277fda948550592ffed9a42a82c9dff64d2154164fdfac690aa0b27ff93260150593ffc98b00a82c9ffe4858054164bffd76a9260b26ffdba54930592fff5dae2982c97ff6e1714c164fbfb0eb8a60b27ff95260130593ffcb8b00982c9ffe485804c164effb30d2a40b26ffd85695205937fea9b4a902c97ffaed8548164dffd54c2a40b277fdb961520593bfed4b0a902c9fef6958448164dffb0ad1a40b277fda864d20593bfed2b26902c9dff6159348164fdfb50b1a40b27efda558d20593f7ec2ac6902c9bffaa95348164ffdb70a9240b27fedb354920593ff6d8aa4902c9dff6159148164dffb4ac0a40b26ffda360520593ff6a9302902c9dff64d5148164fdfac6a8a40b27fbd85505205937fed4262902c9bff6953148164ffdaa498a40b27fed8548520593ff6a9a42902c9ffe6153048164fff3)) else (if i<6 then (if i<5 then 0x2838120dc0d41687a8684048034a0d03d0462f02506a1ea1a1283682d0e10d094168308a6360d60b80e83d8342b05c0741ec1a1183582e8170460d0b40ac178230684a0d4384341a1eb05e08a1a1182f023038741a81c87a8684a0d605c11434241eb06b05e08c1a160f582f0460d0907ac1b823068460d60b83d8342306c1ec1a0e0460d04c1ac1781d068460bc0e8341b06e0741a0e81b02d0f50d09c0c0c2c1d81612407a6a0d43da0b4342306b05e0460841a178110f68350d0941b81182086842070d0201e8275070460251b01a82d0f50d0883f41b4168a6868541fa0d4534342306b05c29c1a1182e0d214c6c1b0a70683e0307da0d03d09a0533506d05c1e91a1381e83582682d0f4b810c0741b417c1c5e06a0b83d2342703f03304d05a1e9412282f8386c1ac1741307a460ba0983d1f03f01f00b06b05c1e9b81f81b80f80582e0f4d41c468260d60ba0e83d2305d0741e8c0f48d09406c1ac17c1d07a4e04a0d83d2342703d03701f00b05c1e9b81f8118268350f4b810c0741bc1c4e07a06e03e0160b43d3604503305f07128358250f47c0fc09c07c0341a87a6a0d43d60e1d06f0721e8e0f614c4c1ac170a707a460b85383d1b06c29c1e8f8060f614c6c1ac1741f07a460ba0f83d1b06d03d0741e918380f48d06c1ac1687a468460d60b8531f03705a1e91a138090f48d0687b0a62e0460d43d2342306c298903b83782c0f40d0bc1a07a069c160a65b24763bac5cd884b0b760cac04d7e0af6f5ddaba6d700ad975a8ab36d62cac1f57caaead588aabf54daa86d4fca98f524aa2ed428a7e74f5a9d0d378a6b74cfa98ad2f8a59f4a9a93ed248a45747da8e6d1a4a2f7451a88ed0e8a17f425a83cd05ca04f402a7f0cfac9f373dfa7aacf209dd73b0a74cce649c77381a6eecdb49b2f35ba69cccf8999f32ca64acc78989f306a5f2cbb0970f2d4a58ecb0095af2a8a536ca449437279a4d2c9709277247a474c8b490e720fa40ac7f88f9f1eca3b8c7308ddf1aea342c6508c37179a2d8c5708a8f14da292c4f08977127a246c458885f104a1eec3cc87770e7a1c6c34086170b8a156c26c843f07da0d4c174826703fa058c08880a700aa00cbff07f76fea9fbabf407e16fb89f5cbe787c86f869ef8bdc87b26f549e94bcf47936f199e12bbf07776ee49da8bb347616eb29d4aba60749ee899cf2b9b072dee549ca0b930723ee439c7eb8ec716ee209c26b830700edf79be6b78c6ef6dda9b9ab7006d7eda29b30b6506c36d799ad8b57c6ad6d569aa4b5206a1ed3f9a6ab4a068d6d0d9a00b3c06716cd5998ab2f8656eca6992cb21863aec5f98aab108618ec2a9840b058602ec0197faafe45fa6be797aeaf4c5e2ebbe9756ae545c86b8c96feadbc5b3eb5a969aad245a26b37965aac805896b0595eaaba056beaca957aaa else 0x2686093048136301300ec0d08009b2f07078043c1c14240f0201a50484d1381e83b0368260f4b41c100e01405f09a241ef070812c04f81f813824268c0fc096046133c1381b07a78240909840b013e83828480fc06941d81b07a583de02101b80641e8479012804c2782449c021e010d05f01e0403d1380e8101e8605013b4161364603099a0b43d2307301d05a1e9026f80c26682d0f4a136c1d41687a409f09be0e20b43d2b0704f02704b100dc04c200268806fe0107a13a4037e03c0d83d09d2c29c120982e0f4274602810a0270a6114504409f20b09d250704004d0f807c020f42749c07c0201907a1005824e011700b0584ec1e9004c08614c25080da07b0a6142403dc0d2340a1270087804213d8100f4309ea0707a1f02507c068509203402027427c8c1781013a1424a070c06d078508f8108d2034284846901b822142480d0810a11f00860f4274540a160b09d08f1b05c1e84e8c2740f423c681a13a142300e83d05f0a1241ef070812e0f20d10ec90a7046200b00e83408f2002d0721dc1a120f6838402601c0c0142409e0741019705a1a050901390f50d02809c1c100e6090a11825f05a1a050918390d02846c1c13c12c3e0e082600983f8491003802a0d026c80260a141a13a441fa0b418453200980702f850910d3838409c8482e0e08272118b8382868c1c243de0e1027211890f5838407ac1b0a6c17068503de0660b8538342f02c29b05c1a101098340f42509c021e0303dc070972012702700d06850940890d0274740c1a0dc0f0a1181e80303e850938110d2834284807b41bc04868142504460b09d1d0684e88857838442dc1c2e01092810c3018c1208605c1d07a2e0e83d110cf070884b8384c061e020f01040938384049c1c2603081eb01881208604049c1c2e01090c5018b83824a04302605090c7010809383854161024e0ea0b18125058b83a82c5417c022024a0b1505f0109814207bc1d4163603090f707080938384049c1d41a383de0e1301878383c1c87a243de0e102990c0812086040a6430205302460b1f0707838207bc1c26060f070486b8384425c1c2223091a7070980c3c0212230b07040f78384049c1c2e0108127070813088c4469c1c2024e01102611189838207bc1c204c223a071b03078382c061e010f00840938044c17c022e0e83d111a7070a0f78388d06425c1c2e0e83d10127070b83a0f4407ac0c2e0e83d101e91a088838385c021024e0e1027111888d38384049c1d41a304e2231707078042049c1c204e2231307040f78384c0a143de0e2341a1ef07088d38385c1cc16243de0e101a81360681e81a1782381f81780f8380b8c00d41647a468441fa0da0b4184532a0fd05a0c2299107e83506114c9811c0fc0bc0781d40cc16703d034a0da0ba0c0463506d05a1ea1a1381a82c0f40d) else (if i<7 then 0x780a04c1741c205e01683de0e212810c0982c1de09060fc08e4a043040430b05821881fb8081a4606205b07bc1c4e0ec08028a0b2707505a1e8c0a282d14c610009d0a6430409f06a8531815036a1ec299027c1f214c60ce132446307860e104070082a8c2002341fa0f480be05f81bc1d07a509f09d83d1f0711a082750f4411f07a208f08083d180c80970741e9008804b83a0f48032024869c1c483de0e4341a1a00970702a100640490f78389c1c868260b028853181481170741a101780a60d3838804446bc1c3026e0ea0b1822a29d05822100b81f68350f7838a1334168a6846443d03aa0b60e270721a0817825383a0f480bc03c869c1c405f022a0de0e83d282f80f41ef07120f78390d07c1c8682e0e03d4341c2981e8807403b02c20c224ac1d8160ac06c12c5e07e05e03053235281050583884b1107e82d06114c802601c0f8122401301ae0e09120098070400489003b81816c244802ac1dc0c86812a5a0d8340911f0706c003c0c86809012a482481807c08920247070b8043c0cc1c86812a4a0d834091182440c080b90f682d0d09c1c1e010a1220c0b838206f0498110301001226853824c08818241202440c0e14e093022060809a0260250a0122542400ec0b45382109534097076058f02f81d09183a08426cc027c0e8421304013e07e034210982f0180da1084c100df02f02381a0f4274c4688490763013e0221208a260710904c0ec0034204768683e0708ec0e23525058503a82d0f50d0981141687a8684c0860b83d83427011090450d82e0f60d0707b04781c1021265e02e0483409f241ef014118e0f780a08c707bc050463c0e0240420922305e0770303f04e96060120274607bc1a0a013a403d02b07e60dc0e60b8343f8060703f04e900ac26f03982e0d0bc0c87a0900f2401300e05e09127030490398f81f8198380f8244a031c1c260e0400911819009f0304904c1405380422c244809707bc1a1244a010f06d080490f02f81c0d50f41a0bc0e06c0a21224048013092a0d0912a0e7070b8043c1c14240b07050903c041e0643d04c068201b809840048900dc04c20024490a70482e010510911f008400488f804208207b816c1c1245e010f00878180f701025c9c0dc0b40612e4024c0ba03250092281ef0104d91a1302c8d02447406102401c21809d2012605b07848900b90f682d0d09c0541687a8684e0e0c1e860f4203107a13a383d0c1e840908d026c611e07a46813a4004023e0e09a200980703e84d100100d383826880c002602dc1c134504e00e09e0962701f0230704b1004c03b03420026ca0c412c200ec06e07424095280c7070bc000dd09180c26ca064031c09c1e1345c0d01ce0360e096282f82f00980900760684e9f0341582586065c0e132c1381a87a6e0503660e09d0892f07305880c41f4 else 0x7703102601dc0b01ce0e3813707605b019009b83b02d814804dc1d816c0e4088418a0b183b505a0f8d14d08e82c605646bc1c3026e0ea0b182bf0750582403e141b281016460af048090c1613b030602f072e0e8342032f0702e0c06c04b83a0f4805f81707bc1c8245c0ea0b13085058b80a82c40cb07bc0413f046c1a60778364241830e05b070c1de0d909070a4183d01e41ce0e201780e41ef07100bc20b83a0f480bc125c1d07a406402041ce0e203d8130821017c193838809a132446303960e112801e8826c0f48d07c1c4682030235e0e1813505f070c0f416b8386060024469c1c4e0e2341047b0583ec1e920f78388d0707a11e4683a0b0774241813301f070349002f8390f460aa06242dc1c4067055e0e18358240128c2)))
def liveh11 (i : Nat) : Nat := 0x4287004f9ef601b5081c0000ca3fe8ec000000038107a8f64015c1b0000000000003c1c0c0584136007c00000001026c0003c1c42af3022728d1a87342ddc18e00f0000242a00002c114025c0002a874000081714091c11b002e80ec41665cc141bc00000003031700531c420073411d006dc05e8002699c80f7086c41b882d6409bc2a54a9801cc80bc008402660917e9d9430000000000c24b401e0a4f0924c08341ca80d241d540449c5e017b9e9f880182cb007680fc69a6c2e101e202eac09d28b000025cc7022c421ccaed816140240001029182e51e61c84b82da40ea41f5813f8218405429f69c664a299c5a485000000000483481771d0400000003ca69c0b80000800e012c0002c12800034144000002b5df0000000002829c000100cf816d09100002483800000184027c000128ca8241c0e5683400000a8ec1010a400002de43010d817e801901f8000042c5823400000000823c000340fa0190000180138208000000000002813142ab824e4afc000000000305018a00b229bc0000411242fd021280665ea529ba48e8c2158048000241d2419fc276cb17c29440b45cbe5c1fddf782698a6cde55008d012768a80002e97400018a63884c4259ea2983080003ca944030002b29d44168000041a4000049f64318000101815d000000000342ad00dc000302bd815c0000000382f0803fc00a0842815a009640c468af820400034a3a41e842f802c25cbac263a87acab3420d0820000240dac283ca500000000342cf4247c19400000000000068eac06000000001ca90800400000000000201575d0e006b82f40000c14c0001425201dc007b828f41d800000003dd38000148a40000000181439e58415340a601fe410940c241abde7402ee819bc0200001829a012040a800000002027001480000000000038942ddeb41af02024a5e4a34000282b94041c03b40a3028b40d749e6408a0a5b41e70254c82a9c630aea827940ae80e0000282b101ef9ceb023900c941f382204ab40000c8318310000000015d08000000000034013982308228030dc2d001a2c8274a2d5e28808d5891c6ad400e54b4c1a49d2518800324108416c142042000100000d5d03c1860c844c6c50cfc800130050441c825a74b04c113911
def livel11 : Packing := (540,4,8,8,4,15,0,lived11)
def lived12 (i : Nat) : Nat := (if i<1 then 0x6155843a0bc81d60237f71f8a7cb5ee67a51e37773dd937505d1072f9c6c703dbbd6d81b0e6af1a5468099b0654d901629185260017a35d717205bbd6c95a09604567153f538949050a13d64e113324b2927848991df463514644290d9427506c4068fde3e5cf3a3bf8ed83a70e3f37b4dc73600d39339cc953138c282f84ba52da4b2d2c1cad62a94a3d27ac9af251c8df21dc84620807e41e747611c686de1a8865b18505d8167056b14e84fe1308486112840e0ef036a0c602c609d023807981aa058c11102fc08300f0000fff68152593ffeaa60164fff69d80593ffda560164fff68980593ffd5260164fff68580593ffd3160164fff4c570593ffda854164fff68d50593ffda254164fff4c950593ffda154164fff4c550593ffd2154164fff54930593ffd814c164fff5c530593ffd214c164fffaa920593ffda848164fff69520593ffd8548164fff68d20593ffd5348164fff68520593ffd8148164fff54520593ffd3148164fff60d10593ffd7344164fff60910593ffd5244164fff4c910592ffeaa54964dff6a5525937fd5264164bffaa9805937fda960164dff65d80593dfe7760164dff65580593f7e5560164dff64980593fee2260164dff64580592ffeaa5c164bff6a1705937fd985c164dff64d70593dfd735c164dff64570593dfd715c164fbf61d60593efd7358164fbf54960593efd7158164fbf4c560592ffeaa54164dff6a550592ffda854164dff66150593fbd8454164dff64d50593efd6354164dff64950593fee2254164dff64550593fbd4154164ffe60150592ffda74c164f7f9dd30593fee224c164ffe60130592ffeaa48164dff6a520592ffda848164dff66120592ffda548164dff65520593f7e5548164fef61120592ffda348164dff64d20593efd6348164ffb549205937fd9148164fef50520593fed2148164ffe4c120592ffda744164dff65d10593dfe7744164bff68d105937fd9344164fbf58d10592ffda244164dff64910593fee2244164ffe48110593ff98780164ffe61600593ff98380164ffe5ce00593ff95380164ffe60a00593ff95280164ffe4ca00593ff98180164ffe5c600593ff95180164ffe4c600593ff921801649ffaa9975927feaa649649ff6a5525937ed9588964fdb956225927feaa64164d7f9dd9059377e5564164dfb889905927fda9601649ff6a570592efeaa58164f3f9dd605936fd9558164f9f95560593ebd8458164dbf64d60593eee2258164dbf64560593ebd4158164fbe601605927fda9541649ff6a530592efda64c1649ff6a5205927fda944164fbe581105937f99880164efea22005937f99780164f7e9de005937f99580164fde95600593fb98480164dfe64e00593ef96380164ff68ce005937f99280164ffa88a005937f99180164fee50600593ff21180164 else (if i<2 then 0x83d4e07c078381e83b280882580e0683d81614cf8170183b0a6442503b02a0d4170441a1e1c21281c82e1a20d07a746b8160420686903905c5346024258150683441614ce0f440e0d42182c420340a6812405f03e06123838291f03e03c038191a03d0a4700e1780fe0681020205891c1c903981f032098162481e9f03a0ec0c24a05a0907a703981f01e06c0302c4903d40330698190740b1240f4f01303e030398050689207a8c0f81701c0840d02f071c40603c0c1bc1ec0b0a6710180f00e060e00f605853460610080e05e0e1226c0f80f0703d076541a82f0743d220dc1d0f4606305e0d07a27428184f83100a013018348102844ec0dc1cb0c781f01e01c088d20687507a913a0100fe0781026e06e0e403206381f0208681a8241ea011c08c070f44ec0dc1c701180c276010fb0191a20b07a9c0f81701c08409037071f03a0ec0821a06a0907a700e0130189dc1d0341e9c2860310c13b00e044690341ea4198a141d8111a40d07a706b81701c08c1c82c4e9f0260313a0f6068533604c0380c4e83d81a14cf80c4089d01a284299b01e0e13b0341e9702e0307614c80f506a0b06814cb83906a0b8a6402400f06e0b07a23c299f06a05c160d029940760dc160f41a0533012c1a07f01860c1628429a30203441a0f429970720d8a63c062843ea0d0a6542581c1ec0840683505e0e4607c0c0f604203417838f8381ea501e07c0682d06e0e07a6c0f81b01a0bc1c0f4d81f0203d81080d06e0e3e07c060f50240841b838f81f0260341b8381e9812053468342580c1ea0b41a14cd81b0183d41614cb81b01e0b07a14cb8130183d41a14ca0f41a03b1e0481a0f41a120340b07a0d0982303e05c068390223d469035382303e05c0701905e0e3e0d03f82c0c0532e07c0780702c1186883505c534e07c07807036058230d105c534e07c0780702e048230d106c534e0dc160f41a101e8340763c0b837058180a65c0b02106c34417038c0230320b07a0d0b81b02c0886882e07180760dc160f41a140460dc160f41a1702e048110d106c0e3008c1a0f7058180a66c1b82c1e8340a65c0b83705c0e0685c0d02c1e834260dc160f41a100160dc160f41a1403e0481a0f41a170681fc16060299702e0dc160d0299703e0dc168241e9703e05c1b02101e0bc1c7c0f80f00a0d46882c1e9f03e05c0702106a0bc1c7c0f80f00e0646882c1e9f03e06c0b80e0420bc1c7c0f83705a0907a5c0f80f00e0dc168d01e9f06a0ec168d01e9703e03c1b82f0703d3607c078070223441a0f4f81f02e04c0702106e0e3e03c1b82c1e8532e03c038370583d0a66c0b80f06e0b0a65b56ad1eb35ec9bb17ebd6ae96b3dab56a99a9a2a21a6e6988a4828ada19a8409fba7b29dda72f9b76654988e5b095fe54393f24c0923e43d8f823998d763168a6220f864 else 0x2681781f02e034118381aa004018c1c17848940c20bc1c2010689b30184098383809b2818c1c2010689b285805606302835c0e26d0340880682f07330760d06826c817c2f02f05781b0583d06814120bc4081bc0604a05c0d07a14d209101e0e100244a0f7070801224c1c81b0183d06c274c1842f81c40c2484a40bc1c0f520902986112440c20bf0360303823e0583d0a690c2180120230388184889481614d581f01a0641783a1e9b0743d4683c0608c0920b41a14e1e9c1e82341b838509403024c1c2144e941260ec0b0350189d302480d83b02e03416274e27c308240fc0d00b40614280e0420bc1cc07b8384289d20610be27c4de07c0701905e0e07aa04814c5089d202481b8391a09f282404682f0709f13a6c1d0341e89f142507b14c1a250260ec0604905a0d07b14ce23c2f60ec0b811068348a68c1d8141a20641714cc0781ea0dc1c284b82303e05c078381a983305881782303e05c068391ea3406ab46a04f03e03c020d702a068230d105c5360920560480fe0bc0f02306c03123839609706e0b07a0d0a15c15a0d4160f41a1b03e0581083601a0bc1c70f81230320b07a0d0d81f0360581100d05e0e382b0df8110683d0686c0f81702408806837071c04080c160630686f07a14d181f02e03043838291802804c0e1fa0460e076703704b03c0b4130342783d4607c0606e0960181a8d205))
def liveh12 (i : Nat) : Nat := (if i<2 then (if i<1 then 0x6300001412c6a0f00000b280300b40000081ac0000141eee00872a10406da01f40000180bb273e00000205cec195c21c70840026ebc15d00000289aa7463410cf7620412a6219581a21a82c418d3005000000000341824011881a39022e41490000000005a1178099a028ea9c5d074a697cd00cb9cf070159014dd2349810e1210640f56081a41a89a303c0ad3051ea88c0000200aa0027c0000d06f28a0c3a53380e9777080000106be9dcb3704d1c1af27d40000b036188036003400000000381f3ea0e0810d222400000000004806a083400000000000000000300550000000007763bc1215003080d07a30f9cbba0722c9bd307961c1ed06bbc10800001e8c100000000000003012f0000269670000309d31029381ebda1e64175827500000806700000fa62f28549257600982065c0000506a749be000004150000004189c037ac0876780c817200000c17d70368000080144409b801daddb6a0013c8dd27192c9c1000000000501178070807980000d081c00005726e9ddac05f91c352037088318a85ca8bd405a3a92fb71d340edb728900f4e012040e7000011d7b607e71db74035f019ac00a9c05af075e81b700002a9df221f00000ca2580000676caa9dc7200a4035a0428000000000c156604b40000e03f95c16f051609fdc024cc0430000269b76a6cf09fbd238b00a7f051ac0640000041990759141b16006b012b1283c0000f062c407bb72fd40fa000000000c000800008a48041ff0a52c1de00000080baf000401271a2b2a91aa261d01096031c5ca680598000000003c12ee71cf416a5001a2829b06c940cf426fc000070663294e103e70881500fdc0b3803a841e9da585a99100003dcad82218e9daa01d000008036488cb00003c1b9fa6c800000000281000000380244a2f1694a605c00000706a848dc00000c0bd0000080bf0000369e7b04f580eef07181c54c045c4205106c2e97d00770c20950409c05b1748c8986100b80000405308137000000000e755ae87ae059cc9fc000800000000005cb8c785b9cb9702734138c02bbddfdc01f980d60071700bc8a2b90141c74660068821fdc81a2071081a4a082d413cf02af48db7727dc203604d0885de266e299b06a838028004844620022321870a021c91e060898a0088a0400240841804083001802604094817a61b00001c3bf04000000014a910000900184038a060400b04150043408581001428024001030404302007418d08140212e2420a0c8810404049855600e800224500981008e018c403384488c02007831c0c1800e00282165c280080c306741c309162c09f0c2c08028082010e0068300046894c40481080c202080008c0848282305450d00114020e009824ac421a862410308280852000029100031406283811a00885080020a045c1018424d17360ca9a else 0x24649134021bc13b0774549cc0a4e2dde700002c0f00000029557a2b40000000031cd1a083300c0b02ca0177108000000000000000407f8412360017816df0028000032401887eb086c01691055d4887ea579dd2a606b681a57052080f70080ac8d3f067c80909047e8201d217a5cbd7222e01430058381139253c000022360000000003c0c3301fd411c9038801bd327dd099d704540000b069c02190000188970000000009a2845c454050800000000341d820811405e00000000000001019ea774f41d0000000000702740000f72000000104cc691e00001c01100002c0cbe7730480c074935e0a2264200e87035728e172331094800002697900304c114e2851a89e0000069be101cbdc77307ea008dc219da892f041e9d82576f581b5f708adcbc3079d801000000017f000021cac000000000023380000ea2af00b10000388917a2345dc00000180a2008200000371bf68260000100f1707c8289db762c00000000048fb00001a9e100000000097074000000003c0ef00002883ec06990052b73d8000000003c03e6061a6899c00c5c0cd871c54a0200001e8b4c0475a9572a0664904b223d419dd06d31ced801e280b0e7535e8f9226e00000000000000000035cf2000e4c023d03940000b0708013af03ecc13e20338086e4032a8860aa67341def058d802dc0194000080846dcb600002c02c600a1ca0e521ec41a0306ef010b00002c1117051101caa03f20015a076cc9f36070e415ee023000000000201fb2057f81409773941d44266400000000049bc000000000ea66ac1f6d27e301c920269e966000000000070c48124004e4000060640886c2260c0000000035dbae00f05c4300002499a4059200cc8a5ff49493a66641551243600b890210c06af05da0883006fc40e14244b8030ca4b00000c21174216e01d6006700002c1259216fc21460109001700003406b6712041ea000010088000031e02a009a80a5a075601e8202580000602bee80d82824000000003415cba28c0000000000000aa2cde90dd01cc00003247800000000180d1d0134000000001408f000000000802d54982a007c411000001082d3012bc9b400001c0083064a40b6f006400006a6d00000103cdc8966262c81e460324dc12ba2a800007737bc106c0186811e9a2c000000000080d3aa2380000d23f80000da7e79df980614c05d00003808982335c20e370d1c86f0000348d7b038000008004800006a0912846000000000000000000a084a9dde0000040a8800d00000874800000d27ff08ac0000001224a7b0817b9019868b57076780b980113c15367423c1ef32041c07cd0204c877c01b909b74034ac1712074c00002037689da0016301f53a3159dd0f0560c8e7504121dcdb03e00000f04614016327f80000000000000000028805c02789d2822841c) else (if i<3 then 0xdc496a2412959902f808fc976cf820fc0074e8af204695ca0803d8000062396895eb06201cf50020fdd80b76114906001de4210970840000b202ec00fa03fc00002038c0000104fc000000001005c00002814f77631817c0000349f9d05484858000010029da30a8960920b8c0c4520ac0000b27c29c72b03991d81204d8000000000000e00000000050316c9dd00002c17a2735e4050e701181fc00001c218a783ae9d200002087de086a418352193007a000009cee000038874c03b05cd5803f64862904a7401c0000000000000369cc40352c132ba6f0a8da401a7804e227d3c8deda7cb886d601519c09d00d9c8fd6a24c00008205901f772387404bb0094012870322c90ae753249208752da8d8c000dc90c7a3748165723c9c13070319c085a02500120405acc1e10000249c5b0633e9d9ea4b781c09a6b9888560238000000002411b000000000f00f448730006000000000348e6421e00000d05b38038601e400005a2e8000000002005faa63cc03b00001e9ea8236800800000389b69a0440000006cc88ad00000000000001691457080000000001a95b320bc0000000000000800889ca5ca1ae003a60744086317596c04100002e91be02dc0000e07b440574773c00000775141cd00002418e800bf5dfa70255e9e4000004126b071dc0eb000025c896210a0062201308071126ecdcd900610004002406e869223ffe954a26009ca72073d8984f007808edd7821418fc024808c79025c000000003813130391ddbce072ce97aa022901dd701bf40a1d018089d7201f75c1fb077c69cfca2cb28171a0e6c90270781c0472749c419400003c98170685e884b02090013e734c0000a05e2c15aa058600db8076ac1cc20000dd5cba08d01050014f41121225681fdd04640000500cd0215306475dc4000000000b085f4159177c80000123a80000f76fe486800000c162507b0888d000029cbe07706a876c06ac0000820380000d00274854b219828150000100c2000000000d2748000000003dd07902a701ce1747800000000381d60000000000000101e2723c240f2421a80000fa6f4000000002e83b222224a157a0f7480f00000c1ba000000000220109d6fe00de48ee802b000000000089f1000025c8a1275400008012449d9da2c729b9c084e8174e21ca41016066c4179306581cc0400ac00001037e81b80a0eb49dbe749a81160000040074a76c81810000249d80000000000000000003a311c9b39078d1dbb2242f406d00003681600000c9a29061d9c70d254b410f7760cdcd6f05bc000000000401b5064c00a000001414e207c1c180b08280000aa53400009052ee9d6d24440000000000000000000000ba260e89c0000301f87040d01f1da71800008a37340a60062bc15b023c668a880550c06ca002dc16e82823814aba6315c616 else 0xe97ed72de8135c273cc059776d00000c06f8000000001880ac070689c000001404f2220a8027326c8000000000415147052))
def livel12 : Packing := (156,3,8,10,4,14,0,lived12)
def lived13 (i : Nat) : Nat := 0xd60881e0580c0602e0e440f02c1a0400705c1c781e0504a030200d02e0e403903c0d02c060401707220780e0d82e0e0f4d03c0b024060401b071c0e816038360b14cc0400e028060701a1e86805a60881e0580c0d02e0e38100380a0181d0207a1a01a9822078160480c0d838e0380700c0b06c160886829a6058340882c34038533c0f02c070681105c1c7816f01b5b165aaa29249ea33e5007a896096003ffaa4b27ff60164ffeb82c9ffd50593ffa60b27ff48164ffe882c97fd97593bfceeb25ff64964ff7112c97fd90593dfac0b27fe80164
def liveh13 (i : Nat) : Nat := 0x722a1763002f0000f0370217423ab7416a55161f3040305c9263373ca0636053b0744065fa21c267f025721c1061f07c00003751700f0000b714d08e822c2033d079a084700ba24af293b02a305d008b00004049b7619a49a0880000c005108200004012705fc29b9055a789575b02010a1542702a5c1030f733273e8a520000403e326180420000404df004404a7769b03652303242473f9734808db07df066c01a603fc288b0269746f07fc023221f306c622e260c12228788873d02578097aa391707e07ac0390000a793827cd2372015e04ca730907e60767048878d5057d080f01e4a037091807530087000000000009035723d00000a6a00004010724300000000f0276a65a22d004b8a3500009a5170900000003200006044f072d07be02900000058b20b328d172210830000801c0000472ba068d20c627930091073803a20817a1d00009a31023bc0998085e017505bc202d27b0000ea5d000027529096706f4098b02080510000320af00a00005a59300e0031e02c1a0857470000023cf0130238802b071b1a63c74b6047606a00000000c02e0000000000006a30c078b093b08a80223745d28090180000405af2890000821b0000629600007a2ef226fa80c2727a230000000050020000f22bf0110253674c3244804ee019c056a24b00000000e273806700005046f054d26d877ec0249223800dea9b12451a765a4dc2390000a28b000042710000000000000000ba3600000003d0430000b20fb07000000000000000000000000000000000ca0b0000624c108ff0520000627e5a340000ea0c000032765007000000000000000002142086d038000000000000da0e00000000806997090094ba389723000050165021c06b4a0400000000000000001062c08c203c509b80950000904fd72f0000f779a050a03d0000201f70710000871d00000000405e37760000d06d00000000070b00004006000020280059d092a75a0000c00160770000e73200000a7b802d776497190000aa459a9500003a11f262103be748f71cea1f52560000909a5060806ec79b0000870a4087c77a1041101d4209c0647a4c6a58e034c01b021de04570890a84900c0a186706773be014da6d0000d74a177c050027150a0400020005000410090134000127110c000002070000022901003a275b0c03031609010002020100010042070206172b0500070f0901850a00010c04110f047f3d010105020d0f6d
def livel13 : Packing := (14,2,8,8,4,11,0,lived13)
def lived14 (i : Nat) : Nat := 0x401c0a030682c1c7ffd64
def liveh14 (i : Nat) : Nat := 0x20440672a207b03c7b877e2c000d23bab02400077a50c0292aa405000572000e02000000ea8e0d00000032000000040af0b000000000e28000000671000ca1a2be087705096a2501822321700ea0278221a30171
def livel14 : Packing := (1,1,8,4,4,0,0,lived14)
def livecolumns : List ColumnInfo := [(640,0,383,0,13),(576,0,447,0,13),(528,0,495,0,13),(256,0,767,0,12),(32,0,991,0,12),(8,0,1015,0,12),(4,0,1019,0,12),(2,0,1021,0,12),(1,0,1022,0,12),(832,0,191,0,11),(704,0,319,0,11),(160,0,863,0,11),(656,0,367,0,11),(132,0,891,0,11),(592,0,431,0,11),(578,0,445,0,11),(536,0,487,0,11),(529,0,494,0,11),(0,128,859,36,10),(512,64,189,258,10),(512,16,486,9,10),(384,0,639,0,9),(288,0,735,0,9),(264,0,759,0,9),(768,64,189,2,9),(136,0,887,0,9),(130,0,893,0,9),(129,0,894,0,9),(33,0,990,0,9),(32,128,859,4,9),(12,0,1011,0,9),(520,16,486,1,9),(6,0,1017,0,9),(4,128,859,32,9),(3,0,1020,0,9),(514,64,189,256,9),(513,16,486,8,9),(512,256,151,104,8),(0,32,606,385,8),(512,8,227,276,8),(0,4,881,138,8),(260,0,763,0,8),(258,0,189,0,8),(257,0,766,0,8),(584,0,183,0,8),(40,0,983,0,8),(36,0,859,0,8),(10,0,1013,0,8),(9,0,486,0,8),(5,0,1018,0,8),(848,0,175,0,8),(840,0,183,0,8),(770,64,189,0,8),(164,0,859,0,8),(161,0,862,0,8),(594,0,429,0,8),(593,0,430,0,8),(582,0,441,0,8),(579,0,444,0,8),(36,128,859,0,8),(537,0,486,0,8),(521,16,486,0,8),(640,256,23,104,7),(640,64,61,258,7),(576,256,151,40,7),(528,8,227,260,7),(528,1,460,34,7),(8,4,881,130,7),(2,4,881,136,7),(1,32,606,384,7),(833,0,190,0,7),(296,0,727,0,7),(289,0,734,0,7),(162,0,861,0,7),(133,0,890,0,7),(600,0,167,0,7),(35,0,988,0,7),(14,0,1009,0,7),(7,0,1016,0,7),(992,0,31,0,7),(856,0,167,0,7),(710,0,313,0,7),(689,0,334,0,7),(595,0,428,0,7),(896,64,61,2,6),(800,16,198,9,6),(784,32,78,129,6),(769,64,188,2,6),(257,32,606,128,6),(672,256,23,72,6),(642,64,61,256,6),(642,1,332,48,6),(641,16,358,8,6),(608,256,151,8,6),(592,256,135,40,6),(592,8,163,260,6),(592,2,424,5,6),(592,1,396,34,6),(560,256,135,72,6),(546,1,460,16,6),(545,64,156,258,6),(522,64,181,256,6),(10,4,881,128,6),(517,16,482,8,6),(960,32,30,1,5),(928,64,29,2,5),(898,64,61,0,5),(880,0,143,0,5),(849,0,174,0,5),(848,8,163,4,5),(817,0,206,0,5),(801,64,156,2,5),(801,16,198,8,5),(785,32,78,128,5),(777,16,230,0,5),(712,256,23,32,5),(712,4,305,2,5),(706,4,305,8,5),(172,0,851,0,5),(165,0,858,0,5),(674,64,29,256,5),(658,1,332,32,5),(138,4,881,0,5),(625,0,398,0,5),(624,256,135,8,5),(624,1,396,2,5),(600,256,135,32,5),(596,2,424,1,5),(594,1,396,32,5),(593,2,424,4,5),(547,64,156,256,5),(538,4,353,128,5),(526,64,177,256,5),(525,16,482,0,5),(519,16,480,8,5),(1008,0,15,0,4),(996,0,27,0,4),(961,32,30,0,4),(930,64,29,0,4),(902,64,57,0,4),(888,0,135,0,4),(858,0,165,0,4),(857,0,166,0,4),(852,8,163,0,4),(841,16,166,0,4),(809,16,198,0,4),(803,64,156,0,4),(794,64,165,0,4),(782,64,177,0,4),(744,256,23,0,4),(714,4,305,0,4),(690,1,332,0,4),(681,16,326,0,4),(167,0,856,0,4),(653,16,354,0,4),(632,256,135,0,4),(627,0,396,0,4),(626,1,396,0,4),(599,0,424,0,4),(597,2,424,0,4),(39,128,856,0,4),(527,16,480,0,4)]
def livelevels : Nat → Packing
  | 8 => livel8
  | 9 => livel9
  | 10 => livel10
  | 11 => livel11
  | 12 => livel12
  | 13 => livel13
  | 14 => livel14
  | _ => emptyPacking
def liveindex : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 1 5 0 9 1 4 liveh9
  | 10 => lookupWord 7 41 5 13 5 4 liveh10
  | 11 => lookupWord 73 383 6 16 8 4 liveh11
  | 12 => lookupWord 248 1291 7 18 10 4 liveh12
  | 13 => lookupWord 77 406 8 16 8 4 liveh13
  | 14 => lookupWord 9 53 4 12 4 4 liveh14
  | _ => fun _ => none
def live : Forest := ⟨1023,14,fun j => deadsamples[j]?.getD (0,0),livecolumns,deadautos,livelevels,liveindex⟩
set_option maxHeartbeats 0 in
theorem geomlive : graphValid live (boundsBefore knownx510) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive8_0 : block live 8 0 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alllive8 : block live 8 0 2=true := slive8_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive9_0 : block live 9 0 5=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive9_5 : block live 9 5 19=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alllive9 : block live 9 0 24=true := (@block_merge live 9 0 5 19 slive9_0 slive9_5)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive10_0 : block live 10 0 7=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive10_7 : block live 10 7 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive10_43 : block live 10 43 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive10_79 : block live 10 79 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive10_115 : block live 10 115 26=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive10_141 : block live 10 141 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive10_177 : block live 10 177 22=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alllive10 : block live 10 0 199=true := (@block_merge live 10 0 177 22 (@block_merge live 10 0 141 36 (@block_merge live 10 0 115 26 (@block_merge live 10 0 79 36 (@block_merge live 10 0 43 36 (@block_merge live 10 0 7 36 slive10_0 slive10_7) slive10_43) slive10_79) slive10_115) slive10_141) slive10_177)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_0 : block live 11 0 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_2 : block live 11 2 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_38 : block live 11 38 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_74 : block live 11 74 17=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_91 : block live 11 91 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_127 : block live 11 127 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_163 : block live 11 163 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_199 : block live 11 199 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_235 : block live 11 235 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_271 : block live 11 271 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_307 : block live 11 307 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_343 : block live 11 343 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_379 : block live 11 379 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_415 : block live 11 415 23=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_438 : block live 11 438 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_474 : block live 11 474 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_510 : block live 11 510 30=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alllive11 : block live 11 0 540=true := (@block_merge live 11 0 510 30 (@block_merge live 11 0 474 36 (@block_merge live 11 0 438 36 (@block_merge live 11 0 415 23 (@block_merge live 11 0 379 36 (@block_merge live 11 0 343 36 (@block_merge live 11 0 307 36 (@block_merge live 11 0 271 36 (@block_merge live 11 0 235 36 (@block_merge live 11 0 199 36 (@block_merge live 11 0 163 36 (@block_merge live 11 0 127 36 (@block_merge live 11 0 91 36 (@block_merge live 11 0 74 17 (@block_merge live 11 0 38 36 (@block_merge live 11 0 2 36 slive11_0 slive11_2) slive11_38) slive11_74) slive11_91) slive11_127) slive11_163) slive11_199) slive11_235) slive11_271) slive11_307) slive11_343) slive11_379) slive11_415) slive11_438) slive11_474) slive11_510)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive12_0 : block live 12 0 36=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive12_36 : block live 12 36 6=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive12_42 : block live 12 42 36=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive12_78 : block live 12 78 36=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive12_114 : block live 12 114 7=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive12_121 : block live 12 121 35=true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alllive12 : block live 12 0 156=true := (@block_merge live 12 0 121 35 (@block_merge live 12 0 114 7 (@block_merge live 12 0 78 36 (@block_merge live 12 0 42 36 (@block_merge live 12 0 36 6 slive12_0 slive12_36) slive12_42) slive12_78) slive12_114) slive12_121)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive13_0 : block live 13 0 7=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive13_7 : block live 13 7 7=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alllive13 : block live 13 0 14=true := (@block_merge live 13 0 7 7 slive13_0 slive13_7)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive14_0 : block live 14 0 1=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alllive14 : block live 14 0 1=true := slive14_0
theorem tableslive : checkedTables live 14 := by
  intro k hk
  interval_cases k
  · exact (rfl : block live 0 0 0 = true)
  · exact (rfl : block live 1 0 0 = true)
  · exact (rfl : block live 2 0 0 = true)
  · exact (rfl : block live 3 0 0 = true)
  · exact (rfl : block live 4 0 0 = true)
  · exact (rfl : block live 5 0 0 = true)
  · exact (rfl : block live 6 0 0 = true)
  · exact (rfl : block live 7 0 0 = true)
  · exact alllive8
  · exact alllive9
  · exact alllive10
  · exact alllive11
  · exact alllive12
  · exact alllive13
  · exact alllive14
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem caseA : Impossible (graphGoal 1023) 14 (vars 1023).toFinset := by
  have h := root_index (g:=dead) (before_sound known383 valid383) geomdead tablesdead (k:=14) (by decide)
    (i:=0) (ws:=vars 1023) (by decide +kernel)
  have e : targetOf dead=graphGoal 1023 := by decide +kernel
  exact e ▸ h
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem caseB : Impossible (graphGoal 1023) 14 (rootB 1023).toFinset :=
  index_root (g:=live) (i:=0) rfl (before_sound knownx510 validx510) geomlive tableslive (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem bound : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 || y 6)) →
      PEqualNP.MetaComplexity.circuitFun 9 C = edge → 16 ≤ C.size := by
  intro C legal first h
  by_contra! small
  obtain ⟨k,t,S,hk,run,sub⟩ := initial_live C legal first h (by omega)
  have eg : graph=graphGoal 1023 := by decide +kernel
  have er : inputs++[seed]=rootB 1023 := by decide +kernel
  rw [eg] at run
  rw [er] at sub
  have ok : splitOK 1023 13438558465 = true := by decide +kernel
  rcases strong_split ok run sub with e | e
  · exact caseA k t hk (e ▸ run)
  · exact caseB k t hk (e ▸ run)
theorem Root.base : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 || y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  intro C legal first h
  exact PEqualNP.Outside.L_meta_4443.bound C legal first h

end PEqualNP.Outside.L_meta_4443
namespace PEqualNP.Outside.L_meta_4443
namespace R16
open PEqualNP.CircuitLowerBounds

abbrev Legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2
def legalB (g : Gate) : Bool :=
  (match g.op with
    | GateOp.and => true
    | GateOp.or => true
    | GateOp.not => true
    | _ => false) && decide (g.inputs.length ≤ 2)
lemma legal_all (G : List Gate) (h : G.all legalB = true) : ∀ g ∈ G, Legal g := by
  intro g hg
  have hb := List.all_eq_true.mp h g hg
  obtain ⟨o, l⟩ := g
  simp only [legalB, Bool.and_eq_true, decide_eq_true_eq] at hb
  refine ⟨?_, hb.2⟩
  cases o <;> simp_all
def gval (g : Gate) (l : List Bool) : Bool :=
  match g with
  | ⟨GateOp.and, []⟩ => true
  | ⟨GateOp.or, []⟩ => false
  | ⟨GateOp.and, [i]⟩ => l.getD i false
  | ⟨GateOp.or, [i]⟩ => l.getD i false
  | ⟨GateOp.not, [i]⟩ => !l.getD i false
  | ⟨GateOp.and, [i, j]⟩ => (l.getD i false && l.getD j false)
  | ⟨GateOp.or, [i, j]⟩ => (l.getD i false || l.getD j false)
  | ⟨o, is⟩ => o.eval (is.map fun i => l.getD i false)
lemma gval_eq (g : Gate) (l : List Bool) :
    gval g l = g.op.eval (g.inputs.map fun i => l.getD i false) := by
  unfold gval; split <;> simp [GateOp.eval]
def pwires (G : List Gate) (l : List Bool) : List Bool := G.foldl (fun w g => w ++ [gval g w]) l
lemma pwires_eq (G : List Gate) (l : List Bool) : pwires G l = (⟨G, 0⟩ : Circuit).wires l := by
  have e : (fun (w : List Bool) (g : Gate) => w ++ [gval g w]) =
      fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := by
    funext w g; rw [gval_eq]
  simp only [pwires, Circuit.wires, e]
lemma wires_len (G : List Gate) : ∀ (l : List Bool),
    ((⟨G, 0⟩ : Circuit).wires l).length = l.length + G.length := by
  induction G with
  | nil => intro l; rfl
  | cons g G ih =>
    intro l
    have h := ih (l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)])
    simp only [List.length_append, List.length_cons, List.length_nil] at h
    simp only [Circuit.wires, List.foldl_cons, List.length_cons] at h ⊢
    omega
lemma wires_getD_lt (G : List Gate) : ∀ (l : List Bool) (i : ℕ), i < l.length →
    ((⟨G, 0⟩ : Circuit).wires l).getD i false = l.getD i false := by
  induction G with
  | nil => intro l i _; rfl
  | cons g G ih =>
    intro l i hi
    have h := ih (l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)]) i (by simp; omega)
    simp only [Circuit.wires, List.foldl_cons] at h ⊢
    rw [h]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
def PMV (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
lemma pmv_pairs (x : Fin 9 → Bool) :
    ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8),
      (8, 5)] : List (Fin 9 × Fin 9)).any (fun p => x p.1 && x p.2) = PMV x := by
  simp only [List.any_cons, List.any_nil, PMV, Bool.or_false, Bool.or_assoc]
lemma pmv_codes (x : Fin 9 → Bool) :
    ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any
      (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))) = PMV x := by
  simp only [List.any_cons, List.any_nil, PMV, Bool.or_false, Bool.or_assoc]
  rfl
theorem comp16 (w : (Fin 9 → Bool) → Bool)
    (root : ∀ C : Circuit, PEqualNP.MetaComplexity.FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = w y) →
      PEqualNP.MetaComplexity.circuitFun 9 C = PMV → 16 ≤ C.size)
    (G : List Gate) (C : Circuit) (hG : ∀ g ∈ G, Legal g) (hlen : 0 < G.length)
    (hf : PEqualNP.MetaComplexity.FanInTwo C) (hs : C.size + G.length ≤ 15)
    (h9 : ∀ y : Fin 9 → Bool, (pwires G (List.ofFn y)).getD 9 false = w y)
    (he : ∀ x : Fin 9 → Bool, C.eval (pwires G (List.ofFn x)) = PMV x) : False := by
  let C' : Circuit := ⟨G ++ C.gates, C.output⟩
  have hC' : PEqualNP.MetaComplexity.FanInTwo C' := by
    intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact hG g h
    · exact hf g h
  have hw : ∀ l : List Bool, C'.wires l = C.wires ((⟨G, 0⟩ : Circuit).wires l) := by
    intro l
    simp only [Circuit.wires, C', List.foldl_append]
  have h9' : ∀ y : Fin 9 → Bool, (C'.wires (List.ofFn y)).getD 9 false = w y := by
    intro y
    rw [hw]
    have hl : 9 < ((⟨G, 0⟩ : Circuit).wires (List.ofFn y)).length := by
      rw [wires_len]; simp; omega
    have h1 := wires_getD_lt C.gates ((⟨G, 0⟩ : Circuit).wires (List.ofFn y)) 9 hl
    have h2 : (⟨C.gates, 0⟩ : Circuit).wires ((⟨G, 0⟩ : Circuit).wires (List.ofFn y)) =
        C.wires ((⟨G, 0⟩ : Circuit).wires (List.ofFn y)) := rfl
    rw [← h2, h1, ← pwires_eq]
    exact h9 y
  have hfun : PEqualNP.MetaComplexity.circuitFun 9 C' = PMV := by
    funext x
    have h1 : C'.eval (List.ofFn x) = C.eval ((⟨G, 0⟩ : Circuit).wires (List.ofFn x)) := by
      simp only [Circuit.eval, hw]
      rfl
    change C'.eval (List.ofFn x) = PMV x
    rw [h1, ← pwires_eq]
    exact he x
  have h16 := root C' hC' h9' hfun
  have hsz : C'.size = G.length + C.gates.length := by
    simp only [Circuit.size, C', List.length_append]
  have hc : C.size = C.gates.length := rfl
  omega

lemma mono_fan {C : Circuit} (h : PEqualNP.MetaComplexity.Monotone2 C) :
    PEqualNP.MetaComplexity.FanInTwo C := fun g hg => by
  refine ⟨?_, (h g hg).2⟩
  have h1 := (h g hg).1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 ⊢
  tauto

end R16
end PEqualNP.Outside.L_meta_4443

namespace PEqualNP.Outside.L_meta_4443
namespace M16
-- a mask with exactly the two bits a, b below 9: the wire OR over the mask is x a || x b
theorem mask_or (m a b : ℕ) (ha : a < 9) (hb : b < 9)
    (hm : ∀ i : Fin 9, m.testBit i.val = (i.val == a || i.val == b)) (x : Fin 9 → Bool) :
    decide (∃ i : Fin 9, m.testBit i.val = true ∧ x i = true) = (x ⟨a, ha⟩ || x ⟨b, hb⟩) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, Bool.or_eq_true]
  constructor
  · rintro ⟨i, h1, h2⟩
    rw [hm, Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at h1
    rcases h1 with h | h
    · left; rw [show (⟨a, ha⟩ : Fin 9) = i from Fin.ext h.symm]; exact h2
    · right; rw [show (⟨b, hb⟩ : Fin 9) = i from Fin.ext h.symm]; exact h2
  · rintro (h | h)
    · exact ⟨⟨a, ha⟩, by rw [hm]; simp, h⟩
    · exact ⟨⟨b, hb⟩, by rw [hm]; simp, h⟩
end M16
end PEqualNP.Outside.L_meta_4443

theorem PEqualNP.Outside.L_meta_4443 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ x2 ∈ [(3 : ℕ), (5 : ℕ), (9 : ℕ), (17 : ℕ), (33 : ℕ), (65 : ℕ), (129 : ℕ), (257 : ℕ), (20 : ℕ), (36 : ℕ), (132 : ℕ), (144 : ℕ)], ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → (∀ (x6 : Fin (9 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x4 (Fin.snoc (Fin.snoc x6 (x6 (4 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)))) (Decidable.decide (∃ (x7 : Fin (9 : ℕ)), x2.testBit ↑x7 = Bool.true ∧ x6 x7 = Bool.true))) = x1 x6) → (14 : ℕ) ≤ x4.size := by
  intro x1 x2 hx2 C hf he
  by_contra hne
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx2
  rcases hx2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine PEqualNP.Outside.L_meta_4443.R16.comp16 (fun y => y 4 || y 6) PEqualNP.Outside.L_meta_4443.Root.base [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩] C (PEqualNP.Outside.L_meta_4443.R16.legal_all _ rfl) (Nat.succ_pos _) hf (show C.size + 2 ≤ 15 by omega) (fun y => by first | rfl | exact Bool.and_comm _ _ | exact Bool.or_comm _ _) (fun x => ?_)
    have h := he x
    rw [PEqualNP.Outside.L_meta_4443.M16.mask_or 3 0 1 (by norm_num) (by norm_num) (by decide) x] at h
    exact h.trans (by first | rfl | exact PEqualNP.Outside.L_meta_4443.R16.pmv_pairs _ | exact PEqualNP.Outside.L_meta_4443.R16.pmv_codes _)
  · refine PEqualNP.Outside.L_meta_4443.R16.comp16 (fun y => y 4 || y 6) PEqualNP.Outside.L_meta_4443.Root.base [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩] C (PEqualNP.Outside.L_meta_4443.R16.legal_all _ rfl) (Nat.succ_pos _) hf (show C.size + 2 ≤ 15 by omega) (fun y => by first | rfl | exact Bool.and_comm _ _ | exact Bool.or_comm _ _) (fun x => ?_)
    have h := he x
    rw [PEqualNP.Outside.L_meta_4443.M16.mask_or 5 0 2 (by norm_num) (by norm_num) (by decide) x] at h
    exact h.trans (by first | rfl | exact PEqualNP.Outside.L_meta_4443.R16.pmv_pairs _ | exact PEqualNP.Outside.L_meta_4443.R16.pmv_codes _)
  · refine PEqualNP.Outside.L_meta_4443.R16.comp16 (fun y => y 4 || y 6) PEqualNP.Outside.L_meta_4443.Root.base [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 3]⟩] C (PEqualNP.Outside.L_meta_4443.R16.legal_all _ rfl) (Nat.succ_pos _) hf (show C.size + 2 ≤ 15 by omega) (fun y => by first | rfl | exact Bool.and_comm _ _ | exact Bool.or_comm _ _) (fun x => ?_)
    have h := he x
    rw [PEqualNP.Outside.L_meta_4443.M16.mask_or 9 0 3 (by norm_num) (by norm_num) (by decide) x] at h
    exact h.trans (by first | rfl | exact PEqualNP.Outside.L_meta_4443.R16.pmv_pairs _ | exact PEqualNP.Outside.L_meta_4443.R16.pmv_codes _)
  · refine PEqualNP.Outside.L_meta_4443.R16.comp16 (fun y => y 4 || y 6) PEqualNP.Outside.L_meta_4443.Root.base [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩] C (PEqualNP.Outside.L_meta_4443.R16.legal_all _ rfl) (Nat.succ_pos _) hf (show C.size + 2 ≤ 15 by omega) (fun y => by first | rfl | exact Bool.and_comm _ _ | exact Bool.or_comm _ _) (fun x => ?_)
    have h := he x
    rw [PEqualNP.Outside.L_meta_4443.M16.mask_or 17 0 4 (by norm_num) (by norm_num) (by decide) x] at h
    exact h.trans (by first | rfl | exact PEqualNP.Outside.L_meta_4443.R16.pmv_pairs _ | exact PEqualNP.Outside.L_meta_4443.R16.pmv_codes _)
  · refine PEqualNP.Outside.L_meta_4443.R16.comp16 (fun y => y 4 || y 6) PEqualNP.Outside.L_meta_4443.Root.base [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 5]⟩] C (PEqualNP.Outside.L_meta_4443.R16.legal_all _ rfl) (Nat.succ_pos _) hf (show C.size + 2 ≤ 15 by omega) (fun y => by first | rfl | exact Bool.and_comm _ _ | exact Bool.or_comm _ _) (fun x => ?_)
    have h := he x
    rw [PEqualNP.Outside.L_meta_4443.M16.mask_or 33 0 5 (by norm_num) (by norm_num) (by decide) x] at h
    exact h.trans (by first | rfl | exact PEqualNP.Outside.L_meta_4443.R16.pmv_pairs _ | exact PEqualNP.Outside.L_meta_4443.R16.pmv_codes _)
  · refine PEqualNP.Outside.L_meta_4443.R16.comp16 (fun y => y 4 || y 6) PEqualNP.Outside.L_meta_4443.Root.base [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 6]⟩] C (PEqualNP.Outside.L_meta_4443.R16.legal_all _ rfl) (Nat.succ_pos _) hf (show C.size + 2 ≤ 15 by omega) (fun y => by first | rfl | exact Bool.and_comm _ _ | exact Bool.or_comm _ _) (fun x => ?_)
    have h := he x
    rw [PEqualNP.Outside.L_meta_4443.M16.mask_or 65 0 6 (by norm_num) (by norm_num) (by decide) x] at h
    exact h.trans (by first | rfl | exact PEqualNP.Outside.L_meta_4443.R16.pmv_pairs _ | exact PEqualNP.Outside.L_meta_4443.R16.pmv_codes _)
  · refine PEqualNP.Outside.L_meta_4443.R16.comp16 (fun y => y 4 || y 6) PEqualNP.Outside.L_meta_4443.Root.base [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 7]⟩] C (PEqualNP.Outside.L_meta_4443.R16.legal_all _ rfl) (Nat.succ_pos _) hf (show C.size + 2 ≤ 15 by omega) (fun y => by first | rfl | exact Bool.and_comm _ _ | exact Bool.or_comm _ _) (fun x => ?_)
    have h := he x
    rw [PEqualNP.Outside.L_meta_4443.M16.mask_or 129 0 7 (by norm_num) (by norm_num) (by decide) x] at h
    exact h.trans (by first | rfl | exact PEqualNP.Outside.L_meta_4443.R16.pmv_pairs _ | exact PEqualNP.Outside.L_meta_4443.R16.pmv_codes _)
  · refine PEqualNP.Outside.L_meta_4443.R16.comp16 (fun y => y 4 || y 6) PEqualNP.Outside.L_meta_4443.Root.base [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 8]⟩] C (PEqualNP.Outside.L_meta_4443.R16.legal_all _ rfl) (Nat.succ_pos _) hf (show C.size + 2 ≤ 15 by omega) (fun y => by first | rfl | exact Bool.and_comm _ _ | exact Bool.or_comm _ _) (fun x => ?_)
    have h := he x
    rw [PEqualNP.Outside.L_meta_4443.M16.mask_or 257 0 8 (by norm_num) (by norm_num) (by decide) x] at h
    exact h.trans (by first | rfl | exact PEqualNP.Outside.L_meta_4443.R16.pmv_pairs _ | exact PEqualNP.Outside.L_meta_4443.R16.pmv_codes _)
  · refine PEqualNP.Outside.L_meta_4443.R16.comp16 (fun y => y 4 || y 6) PEqualNP.Outside.L_meta_4443.Root.base [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩] C (PEqualNP.Outside.L_meta_4443.R16.legal_all _ rfl) (Nat.succ_pos _) hf (show C.size + 2 ≤ 15 by omega) (fun y => by first | rfl | exact Bool.and_comm _ _ | exact Bool.or_comm _ _) (fun x => ?_)
    have h := he x
    rw [PEqualNP.Outside.L_meta_4443.M16.mask_or 20 2 4 (by norm_num) (by norm_num) (by decide) x] at h
    exact h.trans (by first | rfl | exact PEqualNP.Outside.L_meta_4443.R16.pmv_pairs _ | exact PEqualNP.Outside.L_meta_4443.R16.pmv_codes _)
  · refine PEqualNP.Outside.L_meta_4443.R16.comp16 (fun y => y 4 || y 6) PEqualNP.Outside.L_meta_4443.Root.base [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩] C (PEqualNP.Outside.L_meta_4443.R16.legal_all _ rfl) (Nat.succ_pos _) hf (show C.size + 2 ≤ 15 by omega) (fun y => by first | rfl | exact Bool.and_comm _ _ | exact Bool.or_comm _ _) (fun x => ?_)
    have h := he x
    rw [PEqualNP.Outside.L_meta_4443.M16.mask_or 36 2 5 (by norm_num) (by norm_num) (by decide) x] at h
    exact h.trans (by first | rfl | exact PEqualNP.Outside.L_meta_4443.R16.pmv_pairs _ | exact PEqualNP.Outside.L_meta_4443.R16.pmv_codes _)
  · refine PEqualNP.Outside.L_meta_4443.R16.comp16 (fun y => y 4 || y 6) PEqualNP.Outside.L_meta_4443.Root.base [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 7]⟩] C (PEqualNP.Outside.L_meta_4443.R16.legal_all _ rfl) (Nat.succ_pos _) hf (show C.size + 2 ≤ 15 by omega) (fun y => by first | rfl | exact Bool.and_comm _ _ | exact Bool.or_comm _ _) (fun x => ?_)
    have h := he x
    rw [PEqualNP.Outside.L_meta_4443.M16.mask_or 132 2 7 (by norm_num) (by norm_num) (by decide) x] at h
    exact h.trans (by first | rfl | exact PEqualNP.Outside.L_meta_4443.R16.pmv_pairs _ | exact PEqualNP.Outside.L_meta_4443.R16.pmv_codes _)
  · refine PEqualNP.Outside.L_meta_4443.R16.comp16 (fun y => y 4 || y 6) PEqualNP.Outside.L_meta_4443.Root.base [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 7]⟩] C (PEqualNP.Outside.L_meta_4443.R16.legal_all _ rfl) (Nat.succ_pos _) hf (show C.size + 2 ≤ 15 by omega) (fun y => by first | rfl | exact Bool.and_comm _ _ | exact Bool.or_comm _ _) (fun x => ?_)
    have h := he x
    rw [PEqualNP.Outside.L_meta_4443.M16.mask_or 144 4 7 (by norm_num) (by norm_num) (by decide) x] at h
    exact h.trans (by first | rfl | exact PEqualNP.Outside.L_meta_4443.R16.pmv_pairs _ | exact PEqualNP.Outside.L_meta_4443.R16.pmv_codes _)
