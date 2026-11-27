import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3233_aux
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
private theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]

def Live (target : Sig) (k t : Nat) (S : Finset Sig) : Prop :=
  ∀ M : Nat → Nat → Finset Sig → Prop,
  (∀ (hp : proper target), M 0 0 {target}) →
  (∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a) (hf : neg a ∉ insert a U) (tail : M k t (insert (neg a) U)), M (k+1) (t+1) (insert a U)) →
  (∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} (ha : proper a) (hb : proper b) (hab : a ≠ b) (hf : bin d a b ∉ insert a (insert b U)) (tail : M k t (insert (bin d a b) U)), M (k+1) t (insert a (insert b U))) → M k t S
theorem Live.stop {target : Sig} : ∀ (hp : proper target), Live target 0 0 {target} := by
  intro hp
  intro M stopStep unaryStep binaryStep
  exact stopStep hp
theorem Live.unary {target : Sig} : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a) (hf : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)), Live target (k+1) (t+1) (insert a U) := by
  intro k t  U  a  ha hf tail
  intro M stopStep unaryStep binaryStep
  exact unaryStep ha hf (tail M stopStep unaryStep binaryStep)
theorem Live.binary {target : Sig} : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} (ha : proper a) (hb : proper b) (hab : a ≠ b) (hf : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)), Live target (k+1) t (insert a (insert b U)) := by
  intro k t  U  a b  d  ha hb hab hf tail
  intro M stopStep unaryStep binaryStep
  exact binaryStep ha hb hab hf (tail M stopStep unaryStep binaryStep)
theorem Live.weakInduct {target : Sig} {M : Nat → Nat → Finset Sig → Prop} {k t : Nat} {S : Finset Sig} (h : Live target k t S)
    (stop : ∀ (hp : proper target), M 0 0 {target})
    (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a) (hf : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)) (ih : M k t (insert (neg a) U)), M (k+1) (t+1) (insert a U))
    (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} (ha : proper a) (hb : proper b) (hab : a ≠ b) (hf : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)) (ih : M k t (insert (bin d a b) U)), M (k+1) t (insert a (insert b U)))
    : M k t S := by
  apply And.right (a := Live target k t S)
  apply h (fun k t S => Live target k t S ∧ M k t S)
  · intro hp
    exact ⟨Live.stop hp, stop hp ⟩
  · intro k t  U  a  ha hf tail
    exact ⟨Live.unary ha hf tail.1, unary ha hf tail.1 tail.2⟩
  · intro k t  U  a b  d  ha hb hab hf tail
    exact ⟨Live.binary ha hb hab hf tail.1, binary ha hb hab hf tail.1 tail.2⟩
theorem Live.induct {target : Sig} {M : ∀ (k t : Nat) (S : Finset Sig), Live target k t S → Prop} {k t : Nat} {S : Finset Sig} (h : Live target k t S)
    (stop : ∀ (hp : proper target), M 0 0 {target} (Live.stop hp))
    (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a) (hf : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)) (ih : M k t (insert (neg a) U) tail), M (k+1) (t+1) (insert a U) (Live.unary ha hf tail))
    (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} (ha : proper a) (hb : proper b) (hab : a ≠ b) (hf : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)) (ih : M k t (insert (bin d a b) U) tail), M (k+1) t (insert a (insert b U)) (Live.binary ha hb hab hf tail))
    : M k t S h := by
  apply Live.weakInduct (M := fun k t S => ∀ z, M k t S z) h _ _ _ h
  · intro hp z
    exact stop hp 
  · intro k t  U  a  ha hf tail ih z
    exact unary ha hf tail (ih tail)
  · intro k t  U  a b  d  ha hb hab hf tail ih z
    exact binary ha hb hab hf tail (ih tail)


private lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
  induction h using Live.induct with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h using Live.induct with
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

def Reach {R : Type} (roots : List (Wire R)) (p : Nat) (bank : List (Wire R)) : Prop :=
  ∀ M : Nat → List (Wire R) → Prop,
  (M 0 roots) →
  (∀ {p : Nat} {bank : List (Wire R)} {a : Wire R} (tail : M p bank) (ha : Available bank a), M (p+1) (inv a :: bank)) →
  (∀ {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool) (tail : M p bank) (ha : Available bank a) (hb : Available bank b), M (p+1) (combine op a b :: bank)) → M p bank
theorem Reach.start {R : Type} {roots : List (Wire R)} : Reach roots 0 roots := by
  intro M startStep oneStep twoStep
  exact startStep 
theorem Reach.one {R : Type} {roots : List (Wire R)} : ∀ {p : Nat} {bank : List (Wire R)} {a : Wire R} (tail : Reach roots p bank) (ha : Available bank a), Reach roots (p+1) (inv a :: bank) := by
  intro p  bank  a  tail ha
  intro M startStep oneStep twoStep
  exact oneStep (tail M startStep oneStep twoStep) ha
theorem Reach.two {R : Type} {roots : List (Wire R)} : ∀ {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool) (tail : Reach roots p bank) (ha : Available bank a) (hb : Available bank b), Reach roots (p+1) (combine op a b :: bank) := by
  intro p  bank  a b  op tail ha hb
  intro M startStep oneStep twoStep
  exact twoStep op (tail M startStep oneStep twoStep) ha hb
theorem Reach.weakInduct {R : Type} {roots : List (Wire R)} {M : Nat → List (Wire R) → Prop} {p : Nat} {bank : List (Wire R)} (h : Reach roots p bank)
    (start : M 0 roots)
    (one : ∀ {p : Nat} {bank : List (Wire R)} {a : Wire R} (tail : Reach roots p bank) (ha : Available bank a) (ih : M p bank), M (p+1) (inv a :: bank))
    (two : ∀ {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool) (tail : Reach roots p bank) (ha : Available bank a) (hb : Available bank b) (ih : M p bank), M (p+1) (combine op a b :: bank))
    : M p bank := by
  apply And.right (a := Reach roots p bank)
  apply h (fun p bank => Reach roots p bank ∧ M p bank)
  · exact ⟨Reach.start , start  ⟩
  · intro p  bank  a  tail ha
    exact ⟨Reach.one tail.1 ha, one tail.1 ha tail.2⟩
  · intro p  bank  a b  op tail ha hb
    exact ⟨Reach.two op tail.1 ha hb, two op tail.1 ha hb tail.2⟩
theorem Reach.induct {R : Type} {roots : List (Wire R)} {M : ∀ (p : Nat) (bank : List (Wire R)), Reach roots p bank → Prop} {p : Nat} {bank : List (Wire R)} (h : Reach roots p bank)
    (start : M 0 roots (Reach.start ))
    (one : ∀ {p : Nat} {bank : List (Wire R)} {a : Wire R} (tail : Reach roots p bank) (ha : Available bank a) (ih : M p bank tail), M (p+1) (inv a :: bank) (Reach.one tail ha))
    (two : ∀ {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool) (tail : Reach roots p bank) (ha : Available bank a) (hb : Available bank b) (ih : M p bank tail), M (p+1) (combine op a b :: bank) (Reach.two op tail ha hb))
    : M p bank h := by
  apply Reach.weakInduct (M := fun p bank => ∀ z, M p bank z) h _ _ _ h
  · intro z
    exact start  
  · intro p  bank  a  tail ha ih z
    exact one tail ha (ih tail)
  · intro p  bank  a b  op tail ha hb ih z
    exact two op tail ha hb (ih tail)


def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R : Type} (goal : Wire R) (s : Nat) (ws : List (Wire R)) : Prop :=
  ∀ M : Nat → List (Wire R) → Prop,
  (M 0 [goal]) →
  (∀ {s : Nat} {xs zs : List (Wire R)} (eq : xs.Perm zs) (tail : M s xs), M s zs) →
  (∀ {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool) (tail : M s (inv a :: kept save a rest)), M (s+1) (a :: rest)) →
  (∀ {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Bool) (ka : Bool) (kb : Bool) (tail : M s (combine op a b :: kept ka a (kept kb b rest))), M (s+1) (a :: b :: rest)) → M s ws
theorem Run.stop {R : Type} {goal : Wire R} : Run goal 0 [goal] := by
  intro M stopStep permStep oneStep twoStep
  exact stopStep 
theorem Run.perm {R : Type} {goal : Wire R} : ∀ {s : Nat} {xs zs : List (Wire R)} (eq : xs.Perm zs) (tail : Run goal s xs), Run goal s zs := by
  intro s  xs zs  eq tail
  intro M stopStep permStep oneStep twoStep
  exact permStep eq (tail M stopStep permStep oneStep twoStep)
theorem Run.one {R : Type} {goal : Wire R} : ∀ {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool) (tail : Run goal s (inv a :: kept save a rest)), Run goal (s+1) (a :: rest) := by
  intro s  a  rest  save tail
  intro M stopStep permStep oneStep twoStep
  exact oneStep save (tail M stopStep permStep oneStep twoStep)
theorem Run.two {R : Type} {goal : Wire R} : ∀ {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Bool) (ka : Bool) (kb : Bool) (tail : Run goal s (combine op a b :: kept ka a (kept kb b rest))), Run goal (s+1) (a :: b :: rest) := by
  intro s  a b  rest  op ka kb tail
  intro M stopStep permStep oneStep twoStep
  exact twoStep op ka kb (tail M stopStep permStep oneStep twoStep)
theorem Run.weakInduct {R : Type} {goal : Wire R} {M : Nat → List (Wire R) → Prop} {s : Nat} {ws : List (Wire R)} (h : Run goal s ws)
    (stop : M 0 [goal])
    (perm : ∀ {s : Nat} {xs zs : List (Wire R)} (eq : xs.Perm zs) (tail : Run goal s xs) (ih : M s xs), M s zs)
    (one : ∀ {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool) (tail : Run goal s (inv a :: kept save a rest)) (ih : M s (inv a :: kept save a rest)), M (s+1) (a :: rest))
    (two : ∀ {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Bool) (ka : Bool) (kb : Bool) (tail : Run goal s (combine op a b :: kept ka a (kept kb b rest))) (ih : M s (combine op a b :: kept ka a (kept kb b rest))), M (s+1) (a :: b :: rest))
    : M s ws := by
  apply And.right (a := Run goal s ws)
  apply h (fun s ws => Run goal s ws ∧ M s ws)
  · exact ⟨Run.stop , stop  ⟩
  · intro s  xs zs  eq tail
    exact ⟨Run.perm eq tail.1, perm eq tail.1 tail.2⟩
  · intro s  a  rest  save tail
    exact ⟨Run.one save tail.1, one save tail.1 tail.2⟩
  · intro s  a b  rest  op ka kb tail
    exact ⟨Run.two op ka kb tail.1, two op ka kb tail.1 tail.2⟩
theorem Run.induct {R : Type} {goal : Wire R} {M : ∀ (s : Nat) (ws : List (Wire R)), Run goal s ws → Prop} {s : Nat} {ws : List (Wire R)} (h : Run goal s ws)
    (stop : M 0 [goal] (Run.stop ))
    (perm : ∀ {s : Nat} {xs zs : List (Wire R)} (eq : xs.Perm zs) (tail : Run goal s xs) (ih : M s xs tail), M s zs (Run.perm eq tail))
    (one : ∀ {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool) (tail : Run goal s (inv a :: kept save a rest)) (ih : M s (inv a :: kept save a rest) tail), M (s+1) (a :: rest) (Run.one save tail))
    (two : ∀ {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Bool) (ka : Bool) (kb : Bool) (tail : Run goal s (combine op a b :: kept ka a (kept kb b rest))) (ih : M s (combine op a b :: kept ka a (kept kb b rest)) tail), M (s+1) (a :: b :: rest) (Run.two op ka kb tail))
    : M s ws h := by
  apply Run.weakInduct (M := fun s ws => ∀ z, M s ws z) h _ _ _ _ h
  · intro z
    exact stop  
  · intro s  xs zs  eq tail ih z
    exact perm eq tail (ih tail)
  · intro s  a  rest  save tail ih z
    exact one save tail (ih tail)
  · intro s  a b  rest  op ka kb tail ih z
    exact two op ka kb tail (ih tail)


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
  induction h using Run.induct generalizing p bank with
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
  induction h using Run.induct with
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
  induction h using Live.induct generalizing v with
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
  induction h using Reach.induct generalizing k t S with
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
  induction h using Live.induct with
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
theorem seed_table : ∀ r : Row, bit r seed = (sample r 0 && sample r 1) := by decide +kernel
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
    (first : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 1))
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
  induction h using Live.induct with
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
  induction h using Live.induct with
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
  induction h using Live.induct with
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


abbrev BoundPool := (Sig) × (Nat) × (Nat) × (List Sig)
def BoundPool.domain (v : BoundPool) : Sig := v.1
def BoundPool.bound (v : BoundPool) : Nat := v.2.1
def BoundPool.paid (v : BoundPool) : Nat := v.2.2.1
def BoundPool.wires (v : BoundPool) : List Sig := v.2.2.2

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
    have eqS : S = {_} := h (fun k _ S => k = 0 → S = {_}) (fun _ _ => rfl) (fun _ _ _ hn => by contradiction) (fun _ _ _ _ _ hn => by contradiction) rfl
    exact out (List.mem_toFinset.mp ((he.trans eqS).symm ▸ Finset.mem_singleton_self _))
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


abbrev IndexTree (α : Type) := List α
def IndexTree.leaf {α} (xs : List α) : IndexTree α := xs
def IndexTree.fork {α} (_ : Nat) (a b : IndexTree α) : IndexTree α := a ++ b
def IndexTree.read {α} (xs : IndexTree α) (i : Nat) := xs[i]?
def IndexTree.values {α} (xs : IndexTree α) := xs
theorem IndexTree.read_mem {α} (tree : IndexTree α) {i x} (e : tree.read i=some x) :
    x ∈ tree.values := List.mem_of_getElem? e
abbrev Forest := (Nat) × (Nat) × (Nat → Bits × Bits) × (IndexTree ColumnInfo) × (Array (List Nat)) × (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
def Forest.mask (v : Forest) : Nat := v.1
def Forest.cap (v : Forest) : Nat := v.2.1
def Forest.samples (v : Forest) : Nat → Bits × Bits := v.2.2.1
def Forest.cols (v : Forest) : IndexTree ColumnInfo := v.2.2.2.1
def Forest.autos (v : Forest) : Array (List Nat) := v.2.2.2.2.1
def Forest.levels (v : Forest) : Nat → Packing := v.2.2.2.2.2.1
def Forest.index (v : Forest) : Nat → Nat → Option (Nat × Nat) := v.2.2.2.2.2.2

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
    have eqS : S = {_} := h (fun k _ S => k = 0 → S = {_}) (fun _ _ => rfl) (fun _ _ _ hn => by contradiction) (fun _ _ _ _ _ hn => by contradiction) rfl
    exact hT (List.mem_toFinset.mp ((he.trans eqS).symm ▸ Finset.mem_singleton_self _))
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
def g15columns : IndexTree ColumnInfo := (IndexTree.leaf [])
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
def g31columns : IndexTree ColumnInfo := (IndexTree.fork 2 (IndexTree.leaf [(1,0,30,0,4),(2,0,29,0,4)]) (IndexTree.leaf [(4,0,27,0,4),(8,0,23,0,4),(16,0,15,0,4)]))
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
def g47columns : IndexTree ColumnInfo := (IndexTree.leaf [(8,0,39,0,4)])
def g47autos : Array (List Nat) := #[[],[83,32]]
def g47levels : Nat → Packing
  | _ => emptyPacking
def g47index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g47 : Forest := ⟨47,4,fun j => g47samples[j]?.getD (0,0),g47columns,g47autos,g47levels,g47index⟩
def g55samples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffdf7defdfafbfd3fcebcfdeffcebffefe76de77fed7f1773f95eb2ebeb,0x400028000010005000000400701010180030103060043200102204010904888),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdb7fbfbb9ad3afd94caf0b9db5bbdf7f7d39bfcdadcf77ec9eccd2fb9cf16b5,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2484444214284026a4e002420468a8a43140a00408d944460a4082569431231),(0xeda5e7e7b2fc29de4ffc371dba2bf0775ff12db9b18bb528fedad96afcd3c5e,0x12589919410293410206d0396285445a082c5d2bf0022b20f0895d2048c2c4e),(0,0),(0xf1cd79264efe956afa7a64bb677ab40beba463600362eda36f3357b7d763926,0xe3a8651b1a36a0acc57538a080f6ea703078a0c13c28dc34c91f3868663126),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe05fe74eda341d5872cbf684d5e2ed19e7e3bba5e964550dd792aec724f479,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01fb53db1204342a549861b60b6727a22d48ac0b14da4445855161ae724b471),(0,0),(0,0),(0,0)]
def g55columns : IndexTree ColumnInfo := (IndexTree.leaf [(16,0,39,0,4)])
def g55autos : Array (List Nat) := #[[],[84]]
def g55levels : Nat → Packing
  | _ => emptyPacking
def g55index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g55 : Forest := ⟨55,4,fun j => g55samples[j]?.getD (0,0),g55columns,g55autos,g55levels,g55index⟩
def g63samples : Array (Bits × Bits) := #[(0xdabffdfdbdf61bfbfc7dcbe34f7f1b17917df75df7edd9eff77b6dbd3dcebed3cfbfaddba50fcabded46bc9b579eb7bd3d92776566ad4ad3debe36d74deb7f9faf189ad76da7dc1a6b4eaf21eb254de4ae1f7451bb34d9456fd18e934db17349,0x4400202400040800310000100084000ac0000102800a1100490002240004b2800a001b4000190000008108000574009200040400000594000190004218c0010840002890800550053044a00410008802d0060013000c004400188120c206208),(0xb6678efeffcbf5a9cad5bfd527a7a5bd74d1314b7915f5b2ffdec2fc5d978f8ab3b44b2b5add5b771711b15ce99bf2b3f5bce975ef94cd59a34e76ab937848a94ef6be6c9579db5905539ea703c87a7d4ae11fe2ae423fade4a3c3299b0724e7,0x499461811a200a55004cf88854029340027a680613c002ec00233c1096d01045025d0203d400243150030b7e4900b00499e023395882049d0206ec00041398010bbb1000b7310ad00cc0858112c8207810e917400e423d0034024309910504e5),(0xbfdd27bedf8fade4776ebf9d185bc5bd76aeffb29711f77d628e86e5fffdff6d1a52bff6da987348e3e147dcecdbcc68d1accc4e7d7d77b9734cfbbcefbc022d72eff5a31a72e32584dd5a72accb1256ede309af577ea6b3ab2be572a2769632,0x20983204990108b1910222a2810c12a8041040402e00006394000908008912a582448429aad10a21a0240190b504314209040621245140c82010e8812042049440841100c0c52080310832a5111106e902488a012c82618908a42202729212),(0x77ddb87389d95f9f7bbe7e8eb89e6e76fbf75ca7fd5bb3758b555b578affe964ae7e7fa493e06d03bebc4fb5cff51e46b2dd5bdbb1eab66f60f7d916b9c6944fd85b6f0fc30a2ae7d2afc9dc369ef80bb1b0b2dd52e9331e786f7a5d38e8c8b4,0x1482478012444200420888514440810c402202189081ecc814422aa4c048408050190921c0450c000a080254044021081134422900082c11250884167012813a48094aca870a3283708e41084282480000c012150640581c30655a55288040a4),(0xdca768aafb78ce8d2db2ec3fbdddfa4ec963339dbac7a8e05eccbf0bb99ddf5febcef6dc7762a4a79d9ad8f70324ba6e724754bded1eed86f695f276b70acbd73dc66e39a88d0cfed920a0ee10b5a4dd5893bba709bff6dc1ece388c561e1ed5,0x210938550593284a984457082a220ca002159526023c0223a02100100d271046aa46f2022bb0201ea5730921b3008e848a002106a7520082d20653c8040064810364a00030c5086c0c2084761035a077101508a009ba22e00b822088521e1c51),(0x77dad76bd4ced656e7ec247a694c9eb5b66dc4de71aac18acebb177a9bac7a62d6f3e3996dd9d62d6ecf7b18557229a30b5ebb1ef46b568a8f3400a7c2d3365caade63d0f2234a24623735bcfaee29c0664eddfc63b2a86915f817ca03dc41fa,0x88252894b2b3256598a758928465236453b27d28c68c4c28a24dcc0d24d500d4a845700845b04bd175706d345a20a0a24d641d897dd822a1d52444cad2629c8e732b305273362844202335b73c8d8150424e93e44a78286995ec17c803dc01f2),(0,0),(0,0),(0,0)]
def g63columns : IndexTree ColumnInfo := (IndexTree.leaf [(32,0,31,0,7)])
def g63autos : Array (List Nat) := #[[],[50,65]]
def g63levels : Nat → Packing
  | _ => emptyPacking
def g63index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g63 : Forest := ⟨63,7,fun j => g63samples[j]?.getD (0,0),g63columns,g63autos,g63levels,g63index⟩
def g111d6 (i : Nat) : Nat := 0x120ff
def g111l6 : Packing := (1,0,2,0,1,0,0,g111d6)
def g111samples : Array (Bits × Bits) := #[(0xeafcc7b96fc59ffd26c5e2bb3d7bd378fb35ff5dcb26f92afa5f57eff59a73b7aaa379b2fc8d7a99e2ef9efcf4defd4efabc9c89733cebade5579ad5abbcd64d8557ad3d63bd1c6a75510ce3b9bf05e462ee0edf6dfb2914efc74c7d31727465,0x4d00310a2003881269402d0c00406ccc142a8012908082d00025ac006a88036948003229000032d4001bf20024ec2018680000aaf2500325400423a6f02003840040a8016ea8106822700071012c01d500600ad401ea0010f407087831504444),(0xf771ad34ff2bcf4fbd7f5f5de52efaeb7ebbabfffefbf2eab7c7cf56f8ecea565ddfabcf87cb61db9d6ef4aecff7cebd76fe679cfb9935e6adabc77cdcdb677ed3da5e4f56b4cbe39cfd7aed1f519a6b999796b48a51f4f7b8ad91a66cc6d9cb,0x1204940050200482000010001c10308054448009004424020800871400ac0690000402004e0508404004081210450414000904018220d090010808000a44280600460810104d92040818880c1010088d8400200a10a1400808810604821909),(0xf5be76df5e79b8b5d13f5f6e3ecd176fbeee538a7cfb9f7f6b7fad9b13bb7fed97560ecd71f29f3f1e3ef959a338e3a9e32bd5e7cfc7b51df73d7e9e165479b3baa9a0d59e62e11eead3ad5c624777de8699f96d3766d64d1f3fa2ca8f3d2e52,0x8e4d19200884440101e4a802e100a0c04000830eb000289800c49240c1c411082c325a6812b0485430294040c52402008322a4b0e00c0021216842103a050a9080848145264020288841a770220547500211500d95204c05521120880b352452),(0xde2ebbc73c1cf83c4cedbed77297d7f5b666582db23d5c5d7bf4a54b37a75f4992f88d683d388ea5bafb57791a5deb9b257390777cf70e9d329773c24416edd93fe3d2909bc3b81d7e62dd94d70a759eb42b6b51587d63da2e7eea6ce78912bc,0x10b22099c5638280b403142808691e02bd9d04d1097a9640ce2041351e20e64283892100494815238b12089820999d9858901b4e1903515e001721098578a5416f515492d981d895722018845902b08a5c4a2a2248dd03d08c66ca64e48812ac),(0,0),(0x4a99db5e74fdf3bbfb83b4b12e735e58f515867b75942dba656f9eeac55739b971685432ece5b39368c30fbbb9f895ca9efa5eceda2fea7be4766f052ba5def635ccf928215f7640050f6846acafb2ca6efbba0bffbfdb9043d87d111c3c3ebd,0x12d68401de50564414b80023f49c0203c0413d800068400bbb08034f0177ac0427f40400f6de0023bcc009fc1201950403ff4900082ea08a2fc908010c8a4053de0011e801464d050407f806ac13f8026d9b800bfa055d40038875010c2c3ab9),(0x107b7e8791b6519a9ebd6f37d374faa298392ebad8b5e4afe6bd267679568b3365bebaabdf6ef4e9035a918e8ca50ef74769b2b74aea726a09a6c5e9463715fb76745a9b1b6212a1b9add6dec52a9ba55b57e399ab660ca6d0f217384af881fe,0xadc48a6a24248ac9294916cc74a18dce4988890976a839d0a90054480a8f001149b409fd5690d8d50882129489ae3083c83b5253565cd02541ca4550f495b985581508b28aaa022919a1e755a00eaaa54243a315f06a0c87d4f216384a7880f6),(0,0),(0,0)]
def g111columns : IndexTree ColumnInfo := (IndexTree.leaf [(4,8,99,0,4),(1,32,78,0,4),(64,0,47,0,5)])
def g111autos : Array (List Nat) := #[[],[83,32]]
def g111levels : Nat → Packing
  | 6 => g111l6
  | _ => emptyPacking
def g111index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | _ => fun _ => none
def g111 : Forest := ⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index⟩
def g119samples : Array (Bits × Bits) := #[(0xfab75f3dfbfa3756f92d9ff7baf5ff7dbfebb9b33bef7dcdf77fbffe7bbbf75546cedccfd6f7eb762bef3ffdd2ede7abbef7e4e4b775eb9be6ab6f4d5fde77f2b955ece57b3feb97c6d99b5cdd2fdd2ea315de5f3efbf8d44ddcaa7566eda9cd,0x20100000802449000a820000c1900042800052080010000098c000620802429000050a2000012e00000be20013404000082000047420011240000c8b8000110080002480036500158018000c4009400c9000c0062803a0400e00885042a10888),(0xaf7efcd6de9febfb57d6f5ddedde36f3db7fffeed79fdbfafcf255738c743cbbbff3e3b86b8f9fb9f5bdf54fbff79bd74f5afb3f7fba34f5bf5f9afae879ab5feefe93fa9ee6566f7bbee6bf67d426d75cfb2bace9344fabf72bd58e999b76b3,0x9300010000091004000400382060802420900110020801010208161810541520000000800198110400c004084880812115000049028020c0800220200009220a01801050108206a8408406120184808104430800802442850101410609083421),(0xd3aee9d1a16b8afb579b1b1a2ede96c634714fced4ed35afb8d86696aabedb2eada373270f48f3a9b93de8a90d87d8f6684756adef8eb40bf672fc78b9342c9c7aaa652b2aec9422dd38b32b2a5255bdcc3d35b2da5f372953f3c4ba3a70d996,0x2c07b23e74020fd2aa41748155856818d263d681015680dac92709c7448b08586eaf3a512642c64b613a9091954b38c222671d26711d023332d48951dd0691952839212f8b6888039910b9ac2a42653c283c65315b1b95185ae084b83270c996),(0,0),(0x759a506bc07865de6f37bc2fabe39a5e2705b6a3eec6bd3cca572e3ed72f0325f632aa43d8e0e833eaeab6f86ad5fa72dbaf9c83b9e70faa212acf122e177ae733d8fa39a0b0bb12b7915f7134c3b9a9ed98d75362b1d9c725676c3caf04637c,0x16e5f59c6d01a255c44806523c0cddb5529a2196d082e7c24415d298c0f10d071e6090549dc090f8ed501938009f3fb2169588d90b0b506d102e01343cb84ad135f45369a498be0a36011e712702bb816af81651c4b05c0701a6642cad046374),(0x6339c3e76f77dc41ec6c9766b8b0f93592cd6e58a17db2abb9eea5cd269eeae2dc2c1c9ec755bae6a2821f6b678c3538a75edaf56c57e97ff4e8b90d55c4e75ce36b37ac511be4c610c6f229b9ab77956345b3a117ef6f3608dd37697870ba61,0x84ef690f5888a6bc0049f9381c0ba0115db000874a075d2102333605e754184fe100105f739880fb92c019ec481f2d2102dbf2480954a0ad3f922114724920d57f80032e5018c6a22083e62199863ec06b43378157e41d3d00d937293850b261),(0xd5cc96ab2735f4eedbcfece9fd4d847149d75b8aa71ff3959066dc7566c66ecb75975abde9bb8d684d89311f3151135dd1ce4d97acd9737d0b4d97b62b1596cf57b51ab1b6b408593b67d5bb928b32dabad66fc43367241aeaae177095e247ea,0x481560b0cd924918c5323d4303992d88d1232e6a49f254a2454320824e8122936522ef3572424e688310332525616c12e023da92a435d213539c9243b254cc21b63548a8e4258841b361f1c95a017252ba1c47902bc1245a7a8e167094e243ca),(0,0),(0,0)]
def g119columns : IndexTree ColumnInfo := (IndexTree.leaf [(4,0,115,0,5)])
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
def g189columns : IndexTree ColumnInfo := (IndexTree.fork 4 (IndexTree.leaf [(1,0,188,0,5),(12,0,177,0,4),(16,0,173,0,5),(17,0,172,0,4)]) (IndexTree.leaf [(24,0,165,0,4),(33,0,156,0,4),(132,0,57,0,4),(160,0,29,0,4)]))
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
def g127columns : IndexTree ColumnInfo := (IndexTree.leaf [(32,0,95,0,8)])
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
def g191columns : IndexTree ColumnInfo := (IndexTree.fork 19 (IndexTree.fork 9 (IndexTree.fork 4 (IndexTree.leaf [(1,0,190,0,7),(2,0,189,0,8),(3,0,188,0,5),(4,0,187,0,7)]) (IndexTree.fork 2 (IndexTree.leaf [(6,0,185,0,5),(8,0,183,0,8)]) (IndexTree.leaf [(0,8,163,20,6),(10,0,181,0,5),(12,0,179,0,5)]))) (IndexTree.fork 5 (IndexTree.fork 2 (IndexTree.leaf [(4,8,163,16,5),(14,0,177,0,4)]) (IndexTree.leaf [(16,0,175,0,8),(0,16,166,9,6),(1,16,166,8,5)])) (IndexTree.fork 2 (IndexTree.leaf [(19,0,172,0,4),(24,0,167,0,7)]) (IndexTree.leaf [(16,8,163,4,5),(8,16,166,1,5),(25,0,166,0,4)])))) (IndexTree.fork 9 (IndexTree.fork 4 (IndexTree.leaf [(9,16,166,0,4),(20,8,163,0,4),(32,0,159,0,8),(1,32,30,128,5)]) (IndexTree.fork 2 (IndexTree.leaf [(35,0,156,0,4),(40,0,151,0,5)]) (IndexTree.leaf [(48,0,143,0,5),(56,0,135,0,4),(128,0,63,0,8)]))) (IndexTree.fork 5 (IndexTree.fork 2 (IndexTree.leaf [(130,0,61,0,5),(4,128,27,32,5)]) (IndexTree.leaf [(136,0,55,0,5),(160,0,31,0,7),(128,32,30,1,5)])) (IndexTree.fork 2 (IndexTree.leaf [(32,128,27,4,5),(161,0,30,0,4)]) (IndexTree.leaf [(129,32,30,0,4),(164,0,27,0,4),(36,128,27,0,4)])))))
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
def g251columns : IndexTree ColumnInfo := (IndexTree.leaf [(8,0,243,0,7)])
def g251autos : Array (List Nat) := #[[],[84,115],[99,65],[118,84,115,65],[118,81],[118,84,99,81]]
def g251levels : Nat → Packing
  | _ => emptyPacking
def g251index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g251 : Forest := ⟨251,7,fun j => g251samples[j]?.getD (0,0),g251columns,g251autos,g251levels,g251index⟩
def g255samples : Array (Bits × Bits) := #[(0x9b665c544a8481c32c829a3849d25a0c2e734bceaece0410b1910c9246b692285657c973ca335d593cb00f0546b90059eb43e97a932728851785431870f031165ac8b80393ba6e576270cc58c906b870841734e15dc89803598ab05c2460a6b1,0x104454110880808228020a2041d8002c08600a02808c02009111060244ac12008614a1024802115108904700443200508241c8821224200116051018407029164080a01212302c0942400010c90428108414142154888803090a9048202086a0),(0xf315668af28fdb1ca228365b7ccc05a0011317731e21482f697635c521d4e57b4580944cacd08190116899ef79421d834fcee4e488905930903982805fb1c61927af17aaf49049a676974192f0d0160363a1bd03830701b0dc1f8281c2dc6123,0x83112a82400c43108201140b24040542001210600e014836084820c40800442b4181104024900000902098cc210099010006246088901220003082011981800902040620cc814002101041843090160043212902810201b054050081825c2101),(0x380526282fa13ac851f4c9c505254980d6e8ec3804b3594a769d93b950ebc251b0d8e2a15610b8154799066089743516386914b45de9a6e1e91c2d64aa4bec2945782990b2d68e61aa4d3cd1b24a6ab680984b4c1298da14a63264e421a50a46,0x184000082381184051a442400021c800c760240c008201086414493150c8805030586481420228050588002082640402084818905528808149002d00020c144045280184104604602a043c40824a60b20098024012185a048212646400810a02),(0x96903da21572f2b1f1c959078994a771bc47364121282ac5966e24786e0f6b8886ae49c27124b27b7242ff2e0094e0b4b1b582696d3c94568c371a6b03b30075a8d6353ad9672c0089eb12ba6325f80dd24d451b8459a7c113618d0b812f118c,0x86100cb01034a2a12848198388d4226018030240202c8a411a0a044824066a838a240842212092185a40cf0a0080e094a530c6680a1400448645526011312024a0c7343889210800016b021a61259805924545098441a1c11120810b812e1184),(0xca830c6ee5a1c1ac77b2c4bb013b84b271c7189edce77b42164b82b2ec44ccc2202552493f52e619512b4f09e2177ba801c291327039cbf4fba1fd7ca29d36ceca40c4508827295a1b45be11b7c00687be220f65622167c80c13fe90c415919,0x1282044674a181cc515204830038803270c71014e5265b22464b9241a4004482002443590d10ca0850630203a411b2a000c201185038c3861ba0d078200d6480c204804048212d4a89449e11258006869a220d60222163c80c12ea00c414819),(0xadcb89db333a54791fc5b16de6a74b1fbdaa5224c4caa060c8434905e130b3e50875189fa3aee40ebf67487ce98db2673644923b555505294552488c144494c2312ef3656d2d51ee39b1b44e04f3d3ec4d148000ab72771f011403179f478e82,0xa991884a13221d3803c5e045a0014312e78660240442614040424905201081f109410899826ca6043646807ca808b20b342020284941850001124c8410049440302c118d6904416438b533460072d3ec490080008b50771c0014031517470802),(0xccf1d170b069949f14600d7679a83ea985e068495997ad010287ff4ea745b576050c4fa9e8e0fabd2497448bd27a5aa8acea4ac0268e4d44dc2df9de452a225ad1457b3d721818b9bf9e05034d50ecb938aed67098a522a72856072e55b8d214,0xce85130b040942f1560095449a91aad8dc0e80b5196a18140955b282345b194266c47298868eeb9221d4601c27a00e8acf04a8036004c04cc8c58ecc43a23d68161791d311c0cb9abcc24434d40e8b9388ed67018a522072852072e55a0d214),(0x442aa5b9d884c622461c21eaaaf556fac8da8923687abbfb99c9c28096422e0eb83cb34c1d8918aec8c55d99f53bc2670104934ee2f27258616b2c55a56fa8970e02486406e9b92b5242282d15890d903f02672424a3e96d3ce1d022fa0aa8e8,0x460a679588446000a40a01aa08c414e80818810338389a92898982c08602320ec02091061180118a88016c815113416481048146a2821250206d8051a4632a958802cc600689381b004a400915810c003602652424a380613ce19002e808a0e8),(0,0)]
def g255columns : IndexTree ColumnInfo := (IndexTree.leaf [(64,0,191,0,11)])
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
def g383columns : IndexTree ColumnInfo := (IndexTree.fork 29 (IndexTree.fork 14 (IndexTree.fork 7 (IndexTree.fork 3 (IndexTree.leaf [(1,0,382,0,9),(0,1,332,50,7),(2,0,381,0,9)]) (IndexTree.leaf [(0,2,312,69,7),(3,0,380,0,6),(2,1,332,48,6),(1,2,312,68,6)])) (IndexTree.fork 3 (IndexTree.leaf [(4,0,379,0,11),(5,0,378,0,7),(7,0,376,0,5)]) (IndexTree.leaf [(5,2,312,64,5),(8,0,375,0,9),(0,8,99,276,7),(12,0,371,0,8)]))) (IndexTree.fork 7 (IndexTree.fork 3 (IndexTree.leaf [(13,0,354,0,4),(14,0,369,0,5),(16,0,367,0,11)]) (IndexTree.leaf [(17,0,366,0,8),(18,0,365,0,7),(19,0,364,0,5),(18,1,332,32,5)])) (IndexTree.fork 4 (IndexTree.leaf [(24,0,359,0,8),(25,0,358,0,5),(28,0,355,0,7),(20,8,99,256,5)]) (IndexTree.leaf [(32,0,351,0,11),(33,0,350,0,8),(32,1,332,18,6),(35,0,348,0,5)])))) (IndexTree.fork 15 (IndexTree.fork 7 (IndexTree.fork 3 (IndexTree.leaf [(34,1,332,16,5),(44,0,339,0,5),(49,0,334,0,7)]) (IndexTree.leaf [(48,1,332,2,5),(33,16,326,8,5),(56,0,327,0,5),(64,0,319,0,11)])) (IndexTree.fork 4 (IndexTree.leaf [(65,0,318,0,7),(66,0,317,0,8),(67,0,316,0,5),(65,2,312,4,5)]) (IndexTree.leaf [(70,0,313,0,7),(34,64,29,256,5),(256,0,127,0,9),(0,256,23,104,7)]))) (IndexTree.fork 7 (IndexTree.fork 3 (IndexTree.leaf [(264,0,119,0,6),(256,8,99,20,6),(8,256,23,96,6)]) (IndexTree.leaf [(268,0,115,0,5),(260,8,99,16,5),(280,0,103,0,5),(272,8,99,4,5)])) (IndexTree.fork 4 (IndexTree.leaf [(288,0,95,0,8),(289,0,94,0,5),(40,256,23,64,5),(304,0,79,0,5)]) (IndexTree.leaf [(320,0,63,0,8),(322,0,61,0,5),(258,64,61,0,5),(352,0,31,0,7)])))))
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
def deadcolumns : IndexTree ColumnInfo := (IndexTree.fork 63 (IndexTree.fork 31 (IndexTree.fork 15 (IndexTree.fork 7 (IndexTree.fork 3 (IndexTree.leaf [(1,0,510,0,12),(0,1,460,50,8),(2,0,509,0,12)]) (IndexTree.leaf [(0,2,440,69,8),(3,0,508,0,9),(2,1,460,48,7),(4,0,507,0,12)])) (IndexTree.fork 4 (IndexTree.leaf [(0,4,369,138,8),(5,0,506,0,8),(6,0,505,0,9),(4,2,440,65,7)]) (IndexTree.leaf [(2,4,369,136,7),(7,0,504,0,7),(5,2,440,64,6),(8,0,503,0,12)]))) (IndexTree.fork 8 (IndexTree.fork 4 (IndexTree.leaf [(0,8,227,276,8),(9,0,486,0,8),(10,0,501,0,8),(12,0,499,0,9)]) (IndexTree.leaf [(8,4,369,130,7),(4,8,227,272,7),(14,0,497,0,7),(10,4,369,128,6)])) (IndexTree.fork 4 (IndexTree.leaf [(15,0,480,0,4),(16,0,495,0,13),(0,16,486,9,10),(17,0,494,0,11)]) (IndexTree.leaf [(16,1,460,34,7),(19,0,492,0,8),(16,4,353,138,7),(21,0,490,0,7)])))) (IndexTree.fork 16 (IndexTree.fork 8 (IndexTree.fork 4 (IndexTree.leaf [(21,2,424,64,5),(24,0,487,0,11),(8,16,486,1,9),(25,0,486,0,8)]) (IndexTree.leaf [(9,16,486,0,8),(27,0,484,0,5),(11,16,484,0,5),(24,4,353,130,6)])) (IndexTree.fork 4 (IndexTree.leaf [(29,0,482,0,5),(26,4,353,128,5),(32,0,479,0,12),(0,32,94,385,8)]) (IndexTree.leaf [(32,1,460,18,7),(1,32,94,384,7),(35,0,476,0,7),(34,1,460,16,6)]))) (IndexTree.fork 8 (IndexTree.fork 4 (IndexTree.leaf [(36,0,347,0,8),(39,0,344,0,4),(40,0,471,0,8),(49,0,462,0,8)]) (IndexTree.leaf [(48,1,460,2,6),(50,1,460,0,5),(56,0,455,0,7),(64,0,447,0,13)])) (IndexTree.fork 4 (IndexTree.leaf [(0,64,189,258,10),(66,0,445,0,11),(2,64,189,256,9),(67,0,444,0,8)]) (IndexTree.leaf [(66,1,396,48,6),(70,0,441,0,8),(69,2,440,0,5),(74,0,437,0,7)]))))) (IndexTree.fork 31 (IndexTree.fork 15 (IndexTree.fork 7 (IndexTree.fork 3 (IndexTree.leaf [(74,4,305,128,5),(80,0,431,0,11),(83,0,428,0,7)]) (IndexTree.leaf [(96,0,415,0,9),(96,1,396,18,6),(98,1,396,16,5),(128,0,383,0,13)])) (IndexTree.fork 4 (IndexTree.leaf [(128,1,332,50,7),(3,128,344,36,6),(132,0,379,0,11),(4,128,347,32,9)]) (IndexTree.leaf [(133,0,378,0,7),(134,0,377,0,8),(132,2,312,65,6),(133,2,312,64,5)]))) (IndexTree.fork 8 (IndexTree.fork 4 (IndexTree.leaf [(136,0,375,0,9),(128,8,99,276,7),(140,0,371,0,8),(132,8,99,272,6)]) (IndexTree.leaf [(138,4,369,0,5),(144,0,367,0,11),(152,4,353,2,5),(160,0,351,0,11)])) (IndexTree.fork 4 (IndexTree.leaf [(160,1,332,18,6),(162,1,332,16,5),(164,0,347,0,8),(36,128,347,0,8)]) (IndexTree.leaf [(172,0,339,0,5),(176,1,332,2,5),(180,0,331,0,5),(192,0,319,0,11)])))) (IndexTree.fork 16 (IndexTree.fork 8 (IndexTree.fork 4 (IndexTree.leaf [(198,0,313,0,7),(256,0,255,0,12),(258,0,189,0,8),(260,0,251,0,8)]) (IndexTree.leaf [(264,0,247,0,9),(256,8,227,20,7),(8,256,151,96,7),(268,0,243,0,7)])) (IndexTree.fork 4 (IndexTree.leaf [(260,8,227,16,6),(273,0,238,0,7),(280,0,231,0,8),(276,8,227,0,5)]) (IndexTree.leaf [(288,0,223,0,9),(256,32,94,129,7),(32,256,151,72,7),(257,32,94,128,6)]))) (IndexTree.fork 8 (IndexTree.fork 4 (IndexTree.leaf [(296,0,215,0,7),(40,256,151,64,6),(304,0,207,0,6),(288,16,198,9,6)]) (IndexTree.leaf [(273,32,78,128,5),(56,256,135,64,5),(320,0,191,0,11),(256,64,189,2,9)])) (IndexTree.fork 4 (IndexTree.leaf [(322,0,189,0,8),(258,64,189,0,8),(324,0,187,0,7),(324,8,163,16,5)]) (IndexTree.leaf [(321,32,30,128,5),(388,8,99,16,5),(168,256,23,64,5),(224,256,23,8,5)]))))))
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
open PEqualNP.CircuitLowerBounds
def cLook (nb slots sw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*(iw+pw)) (iw+pw)
  some (word &&& ((1 <<< iw)-1), (word >>> iw) &&& ((1 <<< pw)-1))
def qd8 (i : Nat) : Nat := 0x3a9bc802790020e58140211984232484630fc9b
def ql8 : Nat × Nat × Nat × (Nat → Nat) := (4,7,6,qd8)
def qd9 (i : Nat) : Nat := 0x3d002002d4c200000000000f2005c80161907c801c19041e4008d4c2353080000790184623a9b9004753f200800f20040000000e20041b2105d0020ba0041b40081e80103d00200000001a8400000007a0040f40081e8010200408010200403530800003d0020000000000000000031dd6a6e40019308cac7772000c9846463bb9018463720308c40000000023846b8cd18627c4a88b0ce1742984907e0d41582102e033f47c4f41df3ac74ee55c1b716d8d9db135d67cc7d802fb5ecb916fada5aab4165ac6568a894ea8b50c9d137a5d4b091920a2f4548951021b42c810ff9fa3ea7c0f59e63a873cde9b834c650c11702d6564aa14f2945149992e2524908f91a22a440859062023f07b8f21da29c370420460780c81401e02802800335ea0cd3a71f5e647d79450531c7d77f1f5de1524bb5492e45275a149d64dd8a137627d9149e334cb8cd32d334cb05370ea11251934941f5bd87d6f11f5bb02d6e59d51d8846e1211b80846df211b787d6de5cd1b8846db5491ad5246a211b6552468211b60dd84d376130dd84b3761287d6811f59f0536526610bc756291d58a0756271d58907561d6610ba8442e64d0b96342e18d85053611376098dd8252057f0535f92057dcdd824376088cd1ba3346e198420a110819342058d08191420505080cd18a334624cd1881f5582724139f504d7d01337604d9341058d0417d0109d50317d00c1f5500dd807376018cd12d3344accd1292f53d8cd0f41de0107780315600c8446e2111ac844692111a077802156008844612f4164844531de00055800
def ql9 : Nat × Nat × Nat × (Nat → Nat) := (106,10,11,qd9)
def qd10 (i : Nat) : Nat := (if i<4 then (if i<2 then (if i<1 then 0x89c91513e22a17c0541990a88f114f39a29a7c4534b88a633214ccc22659544ccea899a11132c9a2656344caa68995f0132c9a25d6344bb2489754912fc3a013854026ea804d56009c1201352402082baf10575c28aeb4415d6838bac9c91273e224d7c049999093af0120cc222e84445b2688b58d116c9a2296344547888a0f173e0e2e7c0c5cf978b9f94910a6642102c1ce1783992f072c6641d198439d0887364d0e6b1a1cd934392c68725f00e46641ca8c438cb88713320e2cc21c19743832a870a110e0c9a1c1634385188709710e11e21c08883784506e8710db0621b61c435c1886b2b070ed601a8ac1c30ef0686b00d03bc19c558338ab0660ce0cc444190ac1c29110631de0c6d6018c888310ab0621de0c22ac184228308ef05f1de0bc2ac1799c42e9583732b06d45e0da02c5b28ab05b0020b4664168bc5ae134b5b6490b21141640082c9110562220ab4621563c42ac588552220a6444148778293580522f06923d8d087c5a091105022209e3bc13dac02791104e1de09c2ac138888268ab04d0ce09b4621365c426c7884d1de0963bc128558250ef04915609219c124778238ef04615608c3bc1162c4229583271de0882ac1125c42215831e1f163a560c6c7c58c8f8b152f06183bc109bc0211783081de0822ac105bc020934b062696044d2c049a5801782fa2f05f12e21021c42011103f5c507f4620fe1c41f9582ed22207c2ac0fa8c41f4b883e87107c4440f45581ed1883d97107b0e20f4ac1679582cd2b0594560b1cbc1629782c32f05842e2af08881c0ef0362f05403bc0d1bc01a1110322220623bc0c4bc1480f8a8622205e3bc0b89553a91102d1de05a3bc0b0558160ef02b1560564440a8778150ab02a1de0503bc09c558138ef02515604a3bc08c778110ab0221de0422ac084338108ef01fdd5003aac0047780f0ab01e2114a842294c84529118a522114a23bc0745580e86701d2114a02e094084527908a4e1f149c1e29382c527038a4e21149842292c845250ef01c15603819c0702280e0ef01a1de0322ac0647780c0ab0180ce0305e0830955058ef01715602e42281484501108a000714004227fcbc0f38ef014156028de0050bc0f11781da2f03ae5e0750bc0e59781c92f038c5e070c844df1029ae2f03503bc048558093780121de0202ac0425c40791100ea3101c4440368c4069581992b032e4440305580651880c9710185605f07c4ae0c69501d526c38a4c8534958629282f023e5e04707780537800a1560125e0464bc08b9780fa2f01f05e03d09b4738f88e62f01ac5e0350bc0691780cf1de00e3bc018558030388a71de00a2ac01433802ee4800d49001a90003228000a48972220083bc010558024a480408a00820a254778010ab0022f01205e0234778008ab00121103a42207077800045000 else 0x4211ae4c2a80c846b8108d6c6613e94227d1934fa2c69f418dad0c9a7c5634f8b229f15053e25e1598bc2b21785622f0ac15e0788bc2ac936d536493b8c8a771414ee3389dc8b13b90e2770bc2a817854e2f0a984235205c6a2d781daaf03ae31b50d914e7a829cf66139d422739934e72c69ce64539ca0a73a8c4e74789ce87139c5e14ecbc29c908d341f1a584234940c68e17851b18da2a3d94407c6879991ba231a041e3408ac681178d022f0a0218b3fc5c27f0f8cfc0f19f81633f01c67e4e49aa9f1354be06a8cc8d54389a59c93473e268d7c0d19991a397133f1e267e1c4cf958cf42b09e65e13ccac2789584f08f13350e2668ac2751784ea6613314626623c4cc4389982b09d05e139cac2721784e4e15019aac032874c6d1898d97131b0e26342c6711584e12b09c05613782c66e958cdd9f13132e26261c4c39784da1f19a4cc25ee874bdcea9799d52f05e133e754bbb30973a112e6c9a5cd634b9aa6973a2d2e63d93287c664cea9665f02ccc9a591634b22f81646552c6c9a58d634b1c789639d52bebe057c636564a495ca052b94625725c4ae0c6c9d0c993acc2546874a8b2a951a112a2c9a545634a8cf89504312a0cc24f57549daea93a5d5270cc24da8449b32693658d26ca9a4d97549aca49356612694224d19349a2c693414991ebaa4ce524998c6c8e661264caa4c97549950893264d264b9a4c9634994629329d525729a4ad7c0958a4c852b090b2924a681494862c8494d25138a4a1214931784832f09025e1200bc23fd78119af022e5e11d0bc639cea9145f02292924485263897847194922329a43e52487b0290f4c521e2e11b852636058c6c65d21acaa43591486a8290d67121b2e24361c4868e2c600b18b8cc240a8448132690258d204a9a40a52480b30900a11200c9a401634800a4c582f08b12923fc6362bb228fd5051facc23f28447e3268fc58d1f8a0a3f28c47e4788fc8711f85e1158bc2298f8c46af01f45e1116bc07a3308eea111dcc9a3b9634775028ee9c51dc31b0f198475d088eb64d1d6b1a3ad91475aa28eb5051d6c8a3a541474af80e93321d2cc23a2844743268e858d1d0c8a3a1414743308e7a111cec9a39d63473b228e75451cea0a39e8b4738f64381ec86e3d90d87c61b3308e6a111ccc9a399634733228e65051ccce239a8c4732f88e68f11cd0e239a30471060c2d0c5852363090bc21017841d2f083140a3743160baf80da3321b436304e8c46ccb88d98711b25e0fb8bc1f59783e318d7c4cba311954623268c458d188cc230e84461b268c358d186cc230a844613268c258d184cc23019746032a8c0a11180c9a301634605028c026d7943d8f247c5e43308baa11174c9a2e96345d3268b958d1726642e4bc1df1783bd2f07766642ae734554f88aa332154b9a2a6754542a68a) else (if i<3 then 0xfd4ff21f973edc7d74fa01ee73dc47b44f361e673cc47944f021db73b047534e741c83389c7034dfe1bd3370c6d14d9a1b2336246b44d481a4f347c68b4cf619b732ec6594caa194332646394c6a187b308c60d4c1218072fec5f94bea17c32f645e84bc217732ec45d44ba0172f2e3c5c34b7e16eb2db45b24b5c16a72d2c5a14b40167b2cd45964b2416372c4c5854b0815c32ad45564aa41507297451b4a1c13eb27cc4f849e8136b26544ba494e1267247c48548f611ab22d44444886110721ec43c487610e721c4437486c10d3213c4174826103b2054406480410031fe43e347c40f831ee43c647660e7f1c6437346c00d1b196c32946320bff17f42fd45f20bd317842dd45b20b0b15f42a845480a7f14dc297450209b7136425f44aa09131174221443408570fe41f843e807bf0ee41c6436006af0cac18842f005870a741384244048308e41184210041b082c10141dc0377063c0b14142027304c409441140217040c08040fe018b026403f4064009f010401040000f463a8296b6664d128b5a18f66361ecc6a3d98d07c71a518b419f1682be2d063c5a0c38b415b167a664cf4bc319ceab2b9c96573e2cad7c19599932b50564d162c9a1c5931586312b0c603d98a941590c38b211f1c52664c7cac31317862650563b2e2c761c58e9586242b0c444638840c710958e212b0c41162c54bc30eceab0a9c96153e2c297c18519930a2f0c385e186992583322b06171c2e06385cbc30b2a4b04649604a92c0991581282b02249c1a4d383591580a82b0167160248b83041706326b0058d600c92c0152580338b00631600a62c00bc3058b8607149c0a3e38141c702934dfe170bf83e37e83c6fd058dfa071bf42e17c4bc2f61785e86455e8a0abd192579aa4af36455e6a0abcd91579282af2171bcbc2a0f9985710eade36615c2c9ab8541570d18ae18f15c30e2b84756f10585e0a315a12e2b422c5681585dd2f0bb8baab019155eb22abc8715785e1764bc2ec1785d32f0ba4caaab993557324aae50555ccc2ab593556a82aada315592e2ab198555b26aab5055571e2aad9855532aaaa64d554c92aaa8c5554b8aaa8f1555162aaa5c554c78aa98b1553462a725c54e458a9c8715385e16f6875474eaa8c9d55165e16f284544b26a895cd513422a2193544199288a1150ec9aa1e8b5438f65b91ecb703d96dc7c6dbd08a8664d50d462a1a7c5432f8a868f150d0e2a194c5409992813325005e16da75537ce4a6f9f14debe09bccc9378e4db59c94cd3e29997c1331992660f1b5c0e36b8bc6d70585ac5c94c0960980cc9301992555cd4a93aa94e72529cf8a535f04a666494e3c5292e6a5054949d1e293a2c5274b8a4b8f14965636a0bc2d3158da29f14691628d0bc2d08f8d952f0b285e164cbc2c8b0aa06211aec4235d4846b9b0aa else 0x7fa0ad40e68084ff39fc53f467e04fa39f253e067be4f779ee53d567964f0f9dcd3b567684ebf9d453a1673a4e639ca538d670c4dfb9bbd37066de4db79b4d36866c24d7f9add35a66b24d539a6d34966844ceb999d32c664a4c7798b531266164c0f98152fb65f44bcb975d2e765cc4b7b96bd2d065924b0795ed2b965704adb95952ab654e4a7f94c5291651a4a17940d27a64e649af932525d64a6492f923d240647248d3916d2296444486b90b520f6416482790151fb63e847b38f2d1de63b4474b8e5d1c4637a46d78d8d1ad6352467b8ca518d630c45fb8ba516d62d245878ad51536298451389ed136625e449f89051196224442b881d0ff61ea43ab87050dc61a4432b861d0bc617042cf857d0a8613c425b84ad0946120423b843d08360fe41df838506960ca418382e505860ae414b828d04d6098410781bd02d604c408780d5013601e402b8004ff95fea3fc37f64fe85fb63f4f7e7cfc85f823ef37ddcfb75f6c3ec77d84fac5f563e9b7cfcf9b5f343e637ca4f935f1e3e1f7c1cf7f5ef03ddb7b7cf6e5ed43da37b0cf5d5eb23d5f7a84f4f5e9c3d277a2cf415e743ce379bcf365e643cab791cf1c5e363c677894f085e0e3c0b77f4efd5dec3bbb7754ee95dd03b8f76e4edb5da83b33762cebe5d743ae3758cea75d463a7b74d4e935d1e3a1f7404e7c5cf039c37364e655cc239677294e4e5c8838f371ace2e5c4e388b70f4e175c2038176ff4df75be037af6f0cddd5bb237476e6cdc65b8436f76db4db25b56369b6cfcd985b2836336c14d7b5ae835a76b2cd615aba35636a8cd4d5a8c350769d4d365a5e34ab6934d1f5a3034436834cfc59ea33b76734ce259b6335b6694ccb598832f36594cab5954328b64c4c915914320b63dcc7458da318b62dcc54589a310b61dcc315854308b60dcc14581a30175ff4bfa57e62fbb5f3cbe057b22f535e6cbc6577e2edf5d84bac574a2e775cb4b9257162e0f5bfcb7556dc2da75b14b5856a22d275a2cb3e56742ccb595cb2756402c6f58d4b1956302c43584cb0555fc2be757acaee55da2ba3573cae055b82b6b56ccad5559c2b1b562cac455862afb55bcab055582aab554caa5553c2a675494a8b55082a0b53f4a7754e629af5324a5d54ac293b5254a43547828d35154a2354382853506ca09540a28034fe49f553dc279b4ee49d55396270f4de49b5535c269b4cfc998532226274c14981530025a74acc952529c25274a44944528625074a0493f527c24f349dc937526c24d3499c932526224bf497492d5258249f491c91f523c246748ac90251fc23e7474c8dc518c22b345448a45146228744ec89651242243447c88e511a222f43f486e50da21af435486950d0219b432c86450c6218742d485650a42143427c84e509a212f42548495090211b41e48265038205f409c7)) else (if i<6 then (if i<5 then 0xa6c800668466477077bc8033032423303ea3bf20011911dc19ef219000c908cc00211851dc1dcd4ef219009000cd08d18ef6a7c800660645077bc82400334232a3b83bdeab200192119b1df9000cc0c898efc800643c77e400331a3bf2001a0c1f41dd90090108ca8ee0ef790c808465477077067bc8240032423380084610000000002ee29368004641770670d974042328118408c204610230ba0040046147707705304904103242302340008461177077053049b40223023383b82001e911811803981dc1900f488c08c01cc0ee0c808007a446046607705304904003d223023007403b83212c81e911811981dc19014c1240f488c08c01d00ee0c80a609208007a4460468023083b833fa0411811951dc1dc14c1240c80a908c08d000211871003880107705304002a8230233011841dc19014c1000ca08c08ce046107706405304003282302338118408c20461023083b8320298200194118119c1dc14c1000aa08c08cc00d90c9f40c232034ba01118c36554c327d000aca0bc1b2aa6193e8005c03c70d9f4003542327a02118808c28ee0ee0a6092082064846046845e0a11860f022ee0ee4b20644460466177077053049b40223023383b82982482001e9118119c32420ee0c80a609207a446046777405eb53623206c864824fa070d141dc1241000ac88c08c02ce0ee0c84b2446046016607706404904022302300b383b8320248159118118059c104618230a3b83bea001e01194004230c3b83b82f420c118119a1dcd4e10410608cb0ee0ee0bd082065046046787735384104103c03282338ac86cfa001e80594d00268013400da04118118cd00268010009dc1dc126d000c80a888c08c01d24ee0ee1b36800644460467877a40823023243bd20411811911dd90108c68ee84628778419401408232c3bc20ca00a0411973a86733ce2d9be736e66bfcd4599e732e6627cc1597b72e265a7cb1595b72ae654bca5d944727a64d7c9759277240644bc85d90171f463d7c7758e171b4633fc6458be716e62a7c4fd895711c621bc3fd87b70e861b3c32d85e70ae6127c21583870566077c0b580f7016600fbfe57ef6fca5f6bbe857c36f725ec7bd0d7976f1a5e0bbbdd7776eda5d8bbac574e6e885d0bb9dd7346e5a5c7fb8957056df05bb7b7356df6db05b43b6656c56d7c5adbb5956a86d3c5a5bb4656886d0859dbb3356566c8658e3b15d6246c3a584bb05d6046bfa57d7af755e46bba5757ae755c76b8056e3ada55b06b58569fad055996b2a5637ac3557f6af055cfab655656abc555baa7d5486a8254e7a99552b6a48547fa8c55146a20542fa7dd4f469da5397a6c54d16994530ba5f54ba696c52c7a56d4a669445277a4cd492691c5227a41547e68f451d7a38d46a68c05163a2a544d688c5107a1ed439686450b7a16542b68545 else 0x7400b20b11899042e80174062315a05118ad0288c41936814463053f40007181180389d0008c404600e2740082081189d002060104002317a00180810008c5e8008004639406231005dd08c4a8068184630400231020011881dc10040ee046207742317a06118832410008c6e80680204002310200118bd0010008c60ee08020c904002318200118910088c40800462040023102001189d000f8408c0462740082301189d0020560462740023101581189d002046016202300b101180589d0008c40460162740083bba00990588c54814462e40083b911881ddd0040ee1077740223181180609d002080046204102b2231820815881040ac5046135302314118450208c484604623530a1181188d4c2000108c08c46a6046282309a9c118a08c2846144102c101d00207404231211840074008208058bd0002c400000f030460462353823101184003530a20811888c820820462c41c231011803881078174083c141e05d000f0409204627400231020011880c908c404610324231020011880f208c40ee0800463f40c2310200118810008c40ee08020230ba00408c2e8018530231429ba00bd0001c4192080046304002310298200118c10008c404600e2023007101180389d0008c404600e274002310200118810008c408004620001dc14c1040f40c80ac08ce0ee0a60640560465e4024011118508c204230800000000423080000000000008c204610c90803642246117704902a123023007362984c8c26ef9abaa799064650d90c9049f4023ba06cba031e3193090039ddd01483258f18c984802c01d0e8017400801c8012402231720040000014eeea70794464e74052049c3202a28000000000001c804802e40091184000000000010ef0460463077053040032823023007393b9118118c08c2046107705304904002a8230233811879d0364324127d03868c4ee4460463f400fa0611891dc1dc14c12508c08c01ce04230a3b83b829824819015211811a0004230b3bea9aa9824c19311999dcd4c125d020c988cccee0b2ea6c46405975302e623213b83b829824da0111811803a09dc1dc126d000c80ac88c08d00ee092054046407703d0328230232811845dc36608c62ee0ee0c99aa092046607703d03282302328118408c20461077064049032023283b824815411811941dc0f40ca08c08ca0461023083b832024819011941dc1240a808c80ee07a065046046502308118408c204611770770d90492230233064845dc1dc366d000c888c08cfae81b3e81c344e400e20051dd08c506414230f20079003c801e400f200160b900343412320f200790034801a400d0d048c83c801e400f20060c8383414320801c801e400f20079003c801e400821ddf569000ce08c08cd0ee0cef9148048006504678230c11851def219000cd08ca8ee0ce6) else (if i<7 then 0x40800462e4002317200118b9003c800802e400f200790034ee2a7c800660465153e4010a9d200954c0c840ee2a7c8003c415364014a9a190854f9004c8014320f200590028641e406401720079003c801153e401320050c83c800802e400f20079003c80107d64017200200118c1079005c80135303211a9c190a0c83064183208a9f200854c200001df90108c68efc800463e40023163bf206118f9000785c801e400c118508c08c46a613530800007742317202118118dd4f90058ee0ee8463e4008108c2080046203202b16a0075003a80103202b1720015080c80ac5480280203202b10006a610019411881680100214c20a6e8028530c29ba00b14c08c46e90642740832141921909d000c85a800562d4009118118888c08c400400231000ac08c4082046274008010008c4080046222302311118118888c08c4a8010230800446104102313a00412408c4e80046204902313a00410408c4e80104002310200118810008c4446046222302312a9ba02a00fd000ac4a801f4002310200118888c34814462e400820011891dc08c4846107742310118400ee8462c77c23163be118b1dd08c58ef8462477c2311a98416008c40b38462023007102001188d4f10058801c400e200414c10008c60d2080046304002310200118808c07854a603c00e394024015a00410008c4080046203201e100f0038808c0784080046204002310200118b500100403c00e202301e100f003880a8078406403c207708206118118c14c10008c6c8384604630230834ea00118f50008c5a800462d4002316a0075003a80104002316a06200a00f90001c4005a00401b203c2b400b1185d0188c40b2c46274062313118588c344610d908308c207400801dd10408c60ee04603c3077740023183b8200b5003a818462423023106c841dc2081846046304002311118488c30bc105e0c2f06c9a982092179d0050bc105e740106480f081a420b40082d0020740081d0021b219228410800e80103a00436432456801b400e298118801b2094203a004019247827400864841e80846200008c304610230fa0211880006a00488c08c44460462223023100008004620530400231820c82864100200118ad000c8406a100088c3e8000e207a00038808c01c404600e204102313a00400800462f4004002318bb8408c30641740032141905d020c841b20642432083b841ddd0040ee1077740106c8410008c568006422230820c190118dd000c840920462740023102481189d002e80104002310200118bd0010008c6446046222302317a0003880c020a60800463030083b841ddd0040ee1077740103b8436438a644628530829ba00a14c30a6e802853041106c8414dd0050a6082046305374017a00038832410008c60461740081185d0020820462740081831189d002060c462 else 0x4a049189d0001c408204626416231520d118a90688c5483446205915300718208118994c12410408c80b200e20410231020a1e0118c0c80484082046204102311a984d4c20820462c41c23102081189d0008c408004620400231033811889dc12412088c9481446274003202318200118b90020800462277049223007201580389d000f408c6080046204003d0231820811881060c88c808c88ee064046307703242318208118810408c40800462d40082a9a988d4e0c840b00462059c231011803889ded0088c08c844604624675536231b3bb20819311901f7d000cc0ac80fa046222302313a98419d88c46a7e802677641032623233bba03118c19c50188c60b2c460463677641032623233bba03118c19d88c44ee482280064c465277740623193b833b118c9ddd0188c60cec462f40093b833b118c9040d188c6e80068c4632772230231ca9ea06118c1a818462d40c231119011881f71df50308c80fb8efa81846407dc77d40423203ee3bea0611911df50308c7a81846204002310200118810408c4e80102b02313a98648810408c4e801853041023183b829ba00e19fd0040c809405438530a298416614e0c808c80ee0b30a7064046507705374003d032283e829fa0020019011981dc10188c60a608007a046425303217a06118810308c08c6080046204002310200118888c08c4864464264123262318208118810008c4446046222302311118118888c08c40461023081185d0020b2046205902313a00410008c40800462049023102481189d002080046202e0231017011880b808c405c046204002310200118810008c)))
def ql10 : Nat × Nat × Nat × (Nat → Nat) := (937,11,15,qd10)
def qd11 (i : Nat) : Nat := (if i<9 then (if i<4 then (if i<2 then (if i<1 then 0x5b22acb266143222431de434ac436ac431de4215642222411de41156412acb1222401de40156406ac402ee402acb02223f1de3f1563f2223e1563e249af249ae6613d2223d1de3d6553d9d53d1563da113d64d3d58d3d54d3d0ce3d66d3d5ec3d2ee3d6613c2223c6553c1563ca113c64d3c58d3c0ce3c2223b1de3b1563b9493b08a3b149aa2acaa2223a1de3a1563a9493a08a3a18da92aca9249a866139222391de396553915639a113964d3958d390ce399c5398c53966d392ee39661382223865d381de386553815638a113864d3858d380ce38649389493808a386613722237655375d53715637a113764d375cd3758d370ce3794937645375c5375053748537046372ee37222361de361563694d369493608a364c53648536046369ed36222351de35156359493508a3548535046359c135dd502d5602d4902269a765d341de346553415634649349493408a346453450534046348c13466d342ee34269a666133222336553315633a113364d335cd3358d330ce3394933645335c5335053304633a2d332ee33269a566132222321de326553215632a113264d3258d320ce326493208a32645325453250532046329c13266d32a2d329ed325ec322ee32149a4269a4169a41ada4222311de311563108a314c531046319ed3196d312ee31269a2269a1661302223065d301de306553015630a113064d3058d300ce306493094930645305053048530046309c1308c130a2d309ed3096d308ed3086d301de2d1de2c2222b1de2b1de2a02d9b2ad9b24999661292222965d291de296552915629a112964d2958d290ce29dd501d5601dcd01d4d01dc901d4901d4801cc901c8a01661282222865d281de286552815628a112864d2858d280ce28649289492808a289452866d282ee28dc900d4900d4800c8a0064d2758d270ce276492708a27881272ee27222261de261562608a2688126a2d269ed262ee26661252222565d251de256552515625a112564d2558d250ce256492508a2566d25a2d259ed2596d258ed252ee2508a24046242ac981de216ac21156201de1f1561f0ce1f08a1f2221e1de1e1561e08a1e0461e1de1d1561d96d1d2ac921de1c08a1c2698b1ed8a2221a222191de196ac19222181de1815618222171de17156170ce176ac171de16156160ce1608a161de151561508a152ac822ac801de141561408a142ac7a2ac782ac752ac72222111de10255692220f1de0f1de0e1560e1de0d1560d2220c1de0c1560c2220b1de0b6550b1560ba110b64d0b0ce0b1de0a1560a08a0a1de0908a091de08156080ce0808a081de07156070ce0708a072ee071de06156060ce0608a06211531de051560508a051de0408a041de0308a032ac482ac462ac442ac411de021560208a021de01156010ce0108a01105281de0008a002110710501 else 0x6dc916d4916d4816c8a16dd515d5615dc915d4915d4815c8a151de82255e02ace01de816ac811de80156802acde02ddd2addd249dc2acdc1de7f6557f1567f6ac7f1de7e1567e08a7e2acdb1de7d1567d0ce7d08a7d1de7c1567c08a7cdd514d5614dc914d4914d4814c8a14269da16cda269d9269d8169d81edd80add806dd8269d7269d60a9d6269d41de7b6557b1567b6497b08a7b6457b0467b9ed7b96d7b8ad7b86d7b2227866177222776617622276222755d57515675222735d57315673222725d572156721d5d32acd36617122271655715d5711567164d715cd710ce71222705d5701567008a7064d6f0ce6f6496f08a6f2acd26616e2226e6556e5d56e1566e64d6e5cd6e0ce6e6496e08a6e6556d5d56d1566d6496d08a6d6456d5c56d0466d56c6d2ee6d6616c2226c6556c5d56c1566c64d6c5cd6c0ce6c6496c08a6c6456c5c56c0466ca2d6c96d6c8ed6c8ad6c86d6c2ee6b2226aa1d6a22269e1d0fcac0fdd50ed560edd50dd560d22268a1d68156682ee68e1d0cdd50cd560c222676556715667a116764d675cd670ce67222661de66655669d56615666a116664d660ce669c9669ed665ec662ee6622265a116564d650ce65a2d658ed6586d65222646556415664a116464d640ce6494964e1d0bdd50bd560bdcd0bd6c0bdd50ad560adc90ad490ad480ac8a0a156630ce635c96308a632ee63dc909d4909d4809c8a091de621566208a629ed622ee62dd508d5608dcd08dc908d4908d4808c8a08dd507d5607dcd07dc907d4907d4807c8a07ded07d6d07d6c07ced07cad07cac07eee07dd506d5606dcd06dc906d4906d4806c8a066615f2225f2225e255ca6615d2225d1de5c1565c2225b1de5b1565b2225a1de5a1565a6ac5a2ee5a222591de5915659222581de5815658249c566157222571de576555715657a115764d5758d570ce576ac57222561de561565608a56222551de551565508a5518dc366154222541de546555415654a115464d5458d540ce546495408a541de5365553615531565364d5358d530ce536495308a5364553505530465366d5356c532ee536615222252a115264d525cd5258d520ce526495208a52645525c5525055204652a2d522ee52222511de5108a5104651a01519c151dc905d4905c8a05269c11de5065550156506495008a5064550505500465066d502ee50269c06614f2224fa114f64d4f58d4f0ce4f6494f08a4f6454f5054f0464fa2d4f2ee4f269be269bd6614e2224e65d4e1de4ea114e64d4e58d4e0ce4e6494e08a4e6454e5054e0464ea014e9c14e1adba02dba2adba1de4c1564c2224b1de4b1564b08a4b1de4a6154a1564a08a4a6054a4c54a0464a2ee4adc904d4904d4804c8a0408a49046492ee49dc903d4903d4803c8a03222462acb56614522245222441de442acb425) else (if i<3 then 0xed3dced3dc6d3deee3d949ad2eeade1d3be153bdd53bd563be093bd493b949ac661aba1dab655aba11ab64dab58dab949aba2dab64daa58daa649aa549aa6acaae1d3ae153add53ad563ae093ad493a949a94c9a9a05a99eda942da96ada92eea9661a8655a8a11a864da858da8a09a8949a88c9a88c5a88eda8e1d39e1539dd539d5639dcd39d4d39e2d39d6d39ced39e1537d4d37e0537d4537cc537e1d36e1536dd536d5636e0936d4936e0536dc536d4536c8536e1d35e153565da7655a764da758da7949a7645a7605a7505a7485a79c1a78c1a72eea7dd534d5634d4934dc534d4534cc534c8534ded34d6d34d6c34c6d34eee34661a6655a6a11a664da65cda658da6949a65c5a6505a6485a68c1a6a29a6a2da62eea6e1533d4d33e0533d4533cc533661a5655a5a11a564da558da5645a5545a5505a5485a59c1a58c1a5a29a59e9a5a2da59eda55eca52eea5e1d32e1532dcd32d4d32e0932cc932e0532dc532d4532cc532c8532e2d32ded32ced32c6d32eee32661a4a11a464da458da4485a48c1a4a29a4a2da48eda486da4949a34c5a3485a39c1a3a29a39e9a3969a3968a39eda396da32eea3e1d31e1531dd531d5631e0931d4931e0531dc531d4531c8531e2d31ded31d6d31d6c31c6d31eee31661a265da2655a2a11a264da258da2949a29c1a28c1a2a29a29e9a2969a2968a28e9a2a2da29eda296da28eda22eea2661a165da1655a1a11a164da158da1949a1485a19c1a18c1a1a29a19e9a1969a18e9a1869a1e1d30e1530dd530d5630dcd30d4d30e0930d4930cc930e0530dc530d4530cc530c8530d6c306ada02eea0a1d9f2ee9f61d9e6ad9e2ee9e6619d6559da119d64d9d5cd9d58d9da2d9d64d9c58d9c6499ca099c9c99c66d9c9ed9c5ec9c6ad9c2ee9c64d9b58d9b8ed9b9cd9aa099a9ed9a96d9a6ad9a2ee9a6619965599a119964d9958d99e1d28e1528dd528d5628e0d28dcd28d4d28e0928d4928cc928e2d28ded28d6d28d6c28ced28eee28e0d27e0927cc927e1d26e1526dd526d5626e0926dc926d4926d4826c8a26e2d26ded26d6d26cad26e1d25e1525dd525d5625e0d25dcd25d4d25e0925d4925cc925e2d25ded25d6d25d6c25ced25eee25aac98eac21d5620d561fd561e08a97d561d2ee9665594156940ce942229365593156930ce9304693aac9256c912ee916558f1568f2228e1de8e6558e9d58e1568e0ce8e6498e9c98e08a8e0468e1de8d9c98d08a8d0028d5ec8d2ee8d269e40028c2ee8c0028b6698b269e31e8e3269e21e8e21ede21de8a6498a9c98a08a8a0028a9ed8a5ed8a82d8a2228922288cac19dd518d561822287156870ce87222861de869d586156860ce869c9869ed865ec866ad862ee86222850ce85a2d858ed8586d8522284156840ce8494984dd517d5617d6c17dd516d561 else 0x2f6093f0487023a011840886042a820bc0fe607cd03d381dd80ea0071f037181ac80d1806500304817080ae0053f027c012f00916045a01f900eac067002db01448093403e001bf00c7005a0026e00f0004f00188006200009d5e39c9e3a29e39e9e35e8e38e9e3869e35ece32eee3829e2e2d86ded86ced86c6d86eee86d5684dd580d5680655df9d5de649de9c9de9edde5ecde6adde2eede86dddaaddd655dcdd57ed567edc97ed497ed487ec8a7edc97cd497cc8a7c655da5d5da649da645da56cda2eeda649d9645d99e9d99edd92eed9649d8549d8645d8505d88add886dd8655d7649d7949d7645d79e9d7969d7968d79edd796dd72eed7645d6505d6969d696dd686dd69e9d5969d5968d58e9d58a9d58a8d58edd52eed5649d4645d4505d49e9d4969d48a9d4869d4dd57bd567bdc97bd497bd487bc8a7bcc57bd6c7bcac7b661d364dd3d49705d5d25edd26add2aacd22eed264dd1645d1cc56d661d064dd0645d0505d0661ce64dce661cd64dcd661cc64dcc505cca2dcc8edcc86dccd456ccc56ce2d6cced6cc6d6cd6d6bced6bcad6beee6be2d68d6d68cad68c6d68eee68e1d66dcd66e2d66ded66ced66c6d66eee66d5664d4963d6d63ced63dd562d5662dc962d4962d4862c8a62ded62d6d62cad626accb2eecb2eecae1d5ba1dc92eec9e1d5acac5ae1d58e1558661c8a11c864dc85cdc858dc8661c7a11c764dc758dc7649c72eec7661c5655c5a11c564dc558dc5e1d56e1556dc956d4956c8a56661c4a1dc4a11c464dc458dc4649c45c9c42eec4e1d55e1555dc955d4955c8a559edc36adc32eec364dc258dc2649c2dcd53dc953d4953cc953c8a53dc553cc553c8553ded53ced53cad53cac53c6d53eee53cc952cc552c8552e1d51dc951c8a51c855164dc158dc1649c1645c1505c19c1c12eec1dc950d4950c8a50dc550cc550c8550ded50cad50cac50c6d50eee50661c0a11c064dc058dc0649c0645c0545c0505c0a01c0a29c0a2dc02eec0cc94fcc54fc854fa01bf9c1bfa29bf9e9bf9edbf2eebf661bea11be64dbe58dbe649be645be505bea01be9c1bea29be9e9be8e9be9edbe5ecbe8edbe2eebe661bd65dbda11bd64dbd58dbd649bda01bd9c1bda29bd9e9bd8e9bd8a9bd9edbd8edbd8adbd2eebde1d4edcd4edc94ecc94ec8a4edc54ecc54ec854e9c9bb9edbb5ecbb6adbb2eebb86dbaa1db75c9b72eeb79c5b69edb66adb62eeb6dd54ad564adc94ad494ad484ac8a4adc54ac854aded4ad6d4ad6c4acad4acac4ac6d4aeee4ae0549c85496acb52eeb5e1d4461db4655b466db46adb42eeb4661b3a1db3a2db3661b2dd542d5642e1d41e1541dd541d5641a1db12eeb1e1d40e1540dd540d5640d6c40eac40e153ed563e655af661ae655aea11ae64dae58daea09ae2eeaee1d3de153ddcd3dd4d3de2d3dd)) else (if i<6 then (if i<5 then 0xea1dee4eece77363b8d9db50ed7276883b2b9d8f0ebea75da3ae51d5b4eaa4750b3a571d19ce856741039d99ce60e6b872ff395c1ca74e4c2725139209c8c4e442721138df9c588e24c70b338361c010dfbc6f7637a81bbf8ddb06e9c372a9b8bcdbd06d6a367b9b23cd8d26c2d35e29ae24d6dc6b2735809ab14d5126a6335031a6d0d26c68ce34389a12cd00867de33cb99cbccdba66c23332998fccbda659b32ba99594caaa65033263991d4c8ca6455321d1907cc80863e931e198e48c6d86346318a98b64c566628d312898828c386617130a598494c1bc60a23033180a8bfc65fc82fb597d40be6a5f0f2f7497a30bce25e1f2f07977d0bbc85dd42ed71764cbaf05d5d2e9b97470b9aa5caf2e449718cb87a5c222ded96f00b74a5b8a2dac96ca0b5965a4d2d03167acb3a0595d2c8b163ecb1aa588e2c3996134b07a57d52bc195dccaeb0573d2b9115c48ae0456e72b6615ac4ad1656652b1f95890abfc55cd2ac315580aa7455142a71952f4a8d6541929d894da8a69e5334297114b1ca542525a291a14890a3d051c228b814580a28a512a2887943d0a1b250be28571424ca0f0505d281b94070a0024fba27cf93d349e0c4eeb275d139a09c424df026ea936649ad04d16266d1324c98f04c682626930c8982e4be625da92e6896e84b43259412bb095a24ab6254d928a0940449a524ca9250c91e24894240b11e348e8c4720235c11a488c5445cd22d3915ac8a4844fe226c1116887a2435e218090b6c8528426e211910754831c4152209b9041881aa4099202e900dc7f9e3f7d1f7a0fa307cb63e351ed60f5ec7a7e3cd71e4d8f1d477d83bbb1dbf8ed0c760e3ad61d478e870733c394c1c778e19870c237ee1bf48deb46f0e37611b9d8dc546dde36c91b410d8ec6bbc356b1a768d1bc689233d619d80cc9c660232ba191e0c7d463b4315c18a60c3e86150309818390c18860a42fdf17b08bb8c5d0c2e3417018b7745b6e2d9c16bb0b4bc598e2cac16488b1d858b62c4b16128b05457f42bd415dc8ae7856da2b1b15648aa0854a22a1514e70a61c526a28ee14698a23050e22835140d09fa44f5a277c13ab09be44d7a26a21328098244bf225bd12b5894bc4978246a121188ff4476c239011a488c3445ce22c1114d889d4445c21dc10c5084b44174209410268809c3f941fa40fae87c2c3d881e9e0f1b078403b7c1d610e878727038941bed0dc806d2435801a580d0886678329819050c6f86208308c17e90bd105d142e1216c20b380584c2bc4159b0ab50538428f2142709f004e0c26ba13210967849f4246c11ce08ad8445021dc10bd084b841c42096100f07e983e881e8a0ef30756039c01c680de206cd835501a1a0cdc06500319018660c0205e882e8016de0b3e058682b9c15820a90052f828e4142609ed04e3826b01 else 0x2cd94f6c89b635db136d8546c06b5f45af2ad74e6b83b5b2dad08d6536b0bb5741ab3ed5636a9eb5431a9a0d49f6a2c350c9a7ecd3d069d534db9a64ed2f6694cb49cda4b0d21168f034715a312d1586888b4355a148d07e6826b40459faacfa467b433cdd9df6ceca6747339759c6ece1166f5b36e99b12cd586699334059974cc94663cb314d9844cbe665dab2de59664caf6655d329f9949aca1164eab269192d0c921646d3227990dac83c6405b1f698f26c762638db1b7d8d46c667631b318158b92c59862b3b14d989f4c4c96251b117187e8c3e461df30e3586cec34c6177b0aa18504c2676126308c58416c1f060eab06e98354c163607db0329815ec0896037300c9802ebff15fe5afe3d7ee8bf4e5f942fc357d34be745f2caf8757b80bd585e992f3d979b6bc685defaee09764abade5d56ae9f173e6b9e35cdeae65d7274b8e85c50ae1ed707eb8195bf9adf096f38b7765badadca96e08b6865b2aad8bd6b62b5285a4a2d1096746b37259a62cbe9650eb24059022c74d635ab17c58ab2c4956214b0e458542c20960a2b02b57f7abecd5eacaf1a57642ba315c74ae1456fcab6c95b44ad7c56b0ab51959e8aca2561d2b0a957dcabde55e1aaecd571aab51558aaab65553aaa825533aa905544caa1655032a7d95374a95d5490aa369513ca84c53eca9df14e28a6cd536429a054c8aa60952d6295954ac0a4f852692920148b4a3fd51eba8e1546a8a2e1513728819433ca1835098a8459420ca0eb5068281f940c6a0485016a80493fd89fa54fbfa7ce13db69ec04f52a7a293cde9e544f1ca78a53c1c9ddd4ed0a75c13a7e9ced4e6ea725938f69c554e22a70a938349bff4df226f5137889ba94dc726dcd36849afb4d6aa6a0d34a49a004cdca6621328298ef4c3e26159300897f44be725d6d2e9697304b6425a892c8a96354b07a56452a5294d74a42a507527c293c649bfa4d39265093184968a4a292486921248fba46c1232a9143488ea440921b890c14842a41a9205c8ffd47e0a3e991f008f65478f23bb51d8e8e964732a38fd1c068dbc46b52340919a28c8a4627230a117ac8b84459ea2c8915cc8acb4547a294d14708a1244f6227451356899044baa24b911a2888a442ca20490f9687b043caa1d390e6686e14352a19fd0c7085fc42e5a16690ad285174257a125108c684484216a101d07ac83bb41bfa0cb505b6829f412c208450394816d409320351011a803b3fff9fe88ff247f6c3fae1fd30fe627f0b3f7d9fb80fd8a7e943f2c1f8f4fc447e073ef61f718fb407d7a3eaf9f510fa527d033e799f360f97a7ca23e3e1f158f8607c153dfd1ef7cf79e7ba93dcc9ee24f6dc7b5e3da19ec74f5ee7ad13d559ea14f4d47a4f3d1a1e864f38e79ac3cc89e5d8f2a079353c929e428f1f478df3c621e2a4f11c78313b) else (if i<7 then 0xc4e172705737ef9bd9cde0a6ea3372b9b7d4db7e6d8936a99b41cd9a26cb136489b16cd81e6bc335c69ad04d6426ad5354f9a94cd40e69d134d89a5ecd232688b341499e6cce1a669533249979ccb366539326099124c7a26359316598a54c49261a530a19832cc12a601d2fdd97e14be1a5eab2f1997744bab25ccb2e2996f6cb71e5b172d659694cb3e259792c80961ccafca57832b9b95aa4acba55cf2ab69537ca952545d2a1394f14a6c65293290d9468ca25650f52833940149f724f57278593afc9cba4dfb26d7933d499264c1b25e792db495ea4a7d250d9268c92ae48f524549211c8ff647db23c791cb48e1a46ab2303915e489d6447321f290db485ea4293210d9073c82da40c9203e9017480223ff11fd28fd0c7dee3ed71f458f84c7b623d231e558f0cc77763b591d7b8ea54746639d11cac8e3dc7182385f1c148dec46e7237031b508d84c6b0a34f71a3f8d07467ce336f19658c9fc6466321318e38c69c62b6312518618c1dc5ffe2f9d179d8bb645cee2dff16c38b43c59022bf315bd8ac0c54ea29fd14b78a4e451ae28a1141f89f744ef62745137c89a044c6a25bd12b8893e4492e241f11de88d14459a226b11048869c425e20cd102a87f743ef61f190f458784c3b361d230e608712437ce1b590d7b869fc340e198f0c96862d430a6181d0bdd85d642e1a16950b19856ec2a8614f70a60851d4285213f309d384c0c256e125508ee845942206108b081483d641d960e9507248384c1b620d3906768328418520bc705bd82c0c14ea09fd04c2823dc112a081d03e881d640dee06690319816ec0ade052302558117c08520385019180aac049201fd00d88053c020600a1002a80023ff4dff2eff667f953fbb9fd64fe767f22bf825fbb0fdbd7ec63f56dfa3efcee7e643f289f8f8fc4b7e12bf029f7b2fb927dbbbed45f62afaef7d59bea09f4b8fa367d083e77df388f9887cb13e4f1f22cf8e57c54be1b5f08ef8217bfdbdf55ef1cf75d7ba13dc71ee02f6d07b4fbd935ec0cf5bf7ab13d46de9d4f4ae7a3ebd131e820f3d479d1bcd45e656f305797abcb3de552f28e7923bc885e40cf1e078dd3c5f9e284f0fb785fbc1e1e078eff577dcbbe21de98ef3177803bb69dd3cee7877293b859db9eed9e76abbb441d9a8eca376443b105d7f4ebb375b63acc1d5bceaa275333a851d3b0e99c74b5ba4bdd1e6e8c274433a0d1cff0e7d273cb39d95ce68e719736eb9a85cce0e64a7312397f9cb84e59172b0394bdc9e6e4c27248b9155c832e3d271d0b8d69c63ce2ed7158b8a01c472e20870e63866dc2d4e12e707eb8331c10ae05f701cb804dc006dfdd6fe137e71bed6df456f8fb7be5bd90de8c6f2db78a9bbf2ddbd6ec637515ba28dce36e5937231b8b6dc2a6df736ec9b702db506d8a36b35b50cda4a6d0736749b3 else (if i<8 then 0x8cb9d1a9ac8883902194230468ce994e20e4084608cd9d329ac88839021942304684ef94e1942304658ee14f2044084608cd1de24e408800ca1182338773aa127646400800a811a06a8c9191d0091dd6a84959108c119a3bac884608c8dddba06d9ab54c294c86808f119323424cee8365a9953193d039c720e3494ef166a9c4e89288f0d1d3ba688b394d11e1a36744bc755a9a4ec8088f0d20eaa4948234ef957244230465ce89792cb53c8108c119f3a259ca790211823c0474ef16729a23c35048d9d02cb533919021e223c3504939d329c49c810f11942344786a092b3a459ca79021e223304939090471dda9c4144648ef105118e3bc4144638ef105118e3b85388308c11963bc4106508c11963bc4184608c81dc36867ea61242043204680ee1b433849b90100119e3bb530930ca1182334778a7126118232c778a70ca118232977ae9b542684aa8008ce5de6a84aa801001198bbed509a12aa002331771b21342554004664ef90111e1a24773ab08c11c1a2a773aa900192232a77c8088f0d132042344786891de2042304648ef10211823247784608e0d123b83284608c89df204230464c8108c118f2042304634ef90111e1a264084688f0d113ba234343c8088f0d0d3ba4044634ee88d0d0f20223147784608e0d123bc4106508c11963bc2304706891de118231c7784608c71de20e4084688cb1de20e4044648ef901118e3bc41c8108d11963be4004638ef900118e3be4088008c91df200231c77c8108c11923bc41c8108d11963bc41c8088c91df202231c7788390211a23287d2ee1dda003204668eeb55a984984608cd1dd6ac53893106118233c778a708c11923bb530930ca1182334778a70ca118232c7788108c11923bc4084608c85deba753094126a002303c03125dc2cd400460780618bbdd5094126a004086408c0f00c5177ea612824d4004607806223b85e6a6b221942304678ef14e1182380458ef14d644410790ca11823447788350011923bc41a8008c91de208231c77883500a0113b8770bc1041e82334776a6126a014086508cf1de20d4028108ca1dda9a4004640eed4c2082325511ea82d53c4a9c454d8aa64d52eaa9625499ea45751efa8d9d460aa2a3510aa8675421ea0975004a7e9d3dda9ea14f14a77753aca9ced4e3aa6f9d36de9acb4d13a660d319298254bc0a5c7d2d4e965b4ae6a54fd298e942349caa4bc5254a921748a3a42e51ffe8f8747a8a3b0d1c968dd346b8a343d195a8c3545d3a2bb514ea89fd44aca22d50fca87574385a1aa50c6285e542aba13d508a283d941b0a0ba504e281f940cba03cd012280033fc59fc4cfd0a7df73ebf9f3c4f89a7ba93d989ea8cf48279c93cb39e414f0ee78153be49dcecedb2764b3ae99d514e94274553a049ce44e6e27325396c9ca34e48271df38be9c4 else 0xd038dd56a6d021902e446031402ee365a003203c588108c118e20423046388108c118e2042304630ee904118e2042304630ee327a004006508cc1dc298c9e8010211983b853193d002003284608d05dea9b53082d00a043246488c03a83bb74aa6d4da00408648c91181e018b0eedd229b53492905a043246488c03ae2042344630eedd12ca49482d021923244601d510211a2318776e836629b53482d001902a44607803b22042344630eedd029b4006488cc1ddba4536a692520b408648c91180758778a6d001f432446688088c41ddba4536a6905a00408648c91181e5c2308778a69042083d86488ce1dc29a416800f4192233c230c4084688c608c208c25ddba053193d002003d06408c0f283b8d96a654c64f400800f41902303cb0ee964298c9e801001e83205408c0f2c3b853e801001922304607905dc29a41e800c81181e3c7788308c1192a042304634ef902118f20423144184608c61dca48c94820f019183b8532923252083c0640ac11a520a23124144624ef9004905118b20053ba414463c8014eed0049dd20a231b404462c8088c51dc3bbd588248eed4e208410780c8119e3bb538821041e03204678eed4e2084107808cd1dc3b85e88248eed4e2084104658ee1dc2f44106408cd1dda9c410820c8119a3bb538821041e03204674ee1dda9832046030c1dda0093b9596a60c81180c347768024ee365a982301858eed0049dc3bb4004644eed4c1902301854ee1dda0023247768008c69dda98c9082d001902301682b23662082301658eed0041dcac8d9e800f4158233a776a61041902b046668018ee97a1942304658ee1dda9c4108308c119e3ba5e46508c11963bc536a61051e43246508c1180752772a61261e43246488ce9dda003c86488c119a2034004634ee36464c3246488cd101a042318d9192107a003c05661b232620b400465880d02118e203408463880d02118e203408463192107a003c04a08cc14c64f400800ca118233877193d002003c06508ce1dc298c9e80d001902584684ee1de29b53680102192324460315101a04231a772b30c9192230186880d02118d3b8d98a6d4c1902a4460311101a04231a770ee14da003244664ef14da9c3246488c061d3bc536810c911823344068008c69de29b536801021923244601d3101a04231a77ea6d4d1902b44601ce9dc298c9e801001902300e80ee36464c410800c8119c3b9590a632620f400800a81180750770a6327a004006488ce1dc298c98820c91180c00e8ce896524c41c810ca118234277ca79221942304664ee1dc3886d1b275429849c800a91182366744bc755a9a4e591902192234a773aa94d24e404466ce994e24cc8c810f11942344704951dd2cb5349cb2220a233c77ca790119223c4068ef955118e3ba59ca6b2220e4044684909df29c328460)))) else (if i<13 then (if i<11 then (if i<10 then 0x344616e8365a98524820c91180b00e93aa355a9f40c47868039d11851181e1277c80244607859002d00288c0f09a02231640446288308c118e20c23046388308c118e20c23144184608c61662083d01640ef16464c41046078d502118231d4084608c7502118231c41a8108c1192a042304632ee1a76ab40280094119c3b8c9e800f21182303c72ee179a98416805011922300e92eed4c1e232446078d08d118a11a2311776a61041e02c446078f08d1188bbb4044632eed4c1e232446078c5dda02231a23085e6a614820f402f4044607865dc2f3530828c9118073a230a2301820ef900488c060a3be40122301828ef9004d00288c0609a022316404462082901118e11a231477c802aa714c2504106408cd14c1189ba0d9aa714c2504104671b2327a002b046078d14c1188a985368008c8dd2a9c530941041902338d9192323a002303c6aa714da0023245304621b354fa002b0465aa714c2082320d9192107a002e046078e54c2984168008ca17aa9849e800b8119a2982310230c23046284608c508c11886cf4006a08c8367a0423046484608c4107a00231841e8108c11921182310d9193d001e0232823a0420bc08c408e810aba5530a41041902b84602c03d02504107808c65dea98520830c81742300e80461ae8179a995305c0ac119e3b85e7aab221182300e78ee1de29b534788ca11c0244770ef14da9ac80820f01942304601d65dc3b974aa6d4da01408648c911807604c2ee96524c3246488cd10211a2319770da36629b534920c8152234c4084688c65de29b536801021923244601d35d036a591b3d001961a00e888108d118e29a410830c91194bb8770a6d0019223344084688c7d011182319770efd4da9b404640ad11b0e00ec0961deba0670a6327a004006488c0f61a00ec0eedd02f3402810c91922301601d41ddba04a482d0219232446888108d118c3bb741b212920a23344084688c61ddba34006488ca1ddba04a482d021923244681b2327a043244608cc1dda003e86488cb10111886cf4006586881352084144640ee36464a4186450ee905a0032446588108d118c3bb741b2327a004006408f0d242f0d909a327a0223c3470eedd2a9b536805001902b44602c03b0260776e914da9a49482d00192234c5388108d11922042344630eedd06cc536a692520b400800c815223645388108d11903bb740a6d0111943bb748a6d4d24a416800c911a43bc536800f9119629c4044630eedd06cc536a6905a004006488c05807645388108d11903bc5348210511943b8594820f405943b853482d01119629c4084688c8365a9853493d0015983bb74ea6d4da002b44602c03b0250776e9164298c9e8010015023c3401d61dc6c8c9e8010011e1a3f743aad4f20f40c4786803a03bc591b214fa00400640a91181ec3401d800eed else 0x3204680ee9646cf400640ad15023447704622ee5d033a596a60c8119cbb87768008c91dc1188bb8671b2d4c19023347704622ee1dc2082321770eed0011903b82311774b2d4c1902b0466e8008c408c2dd26ad538a61282083204688a608c4dd26a9530a6d001199ba4d5aa714c2504106408d0364a9853e800c8119a6ad538a6d0011962982313741b354e299530820c811a22982314d5aa714c2082328d92a614c20f400640b811a26a9530a6105a0023345304626e8367a00320565046104610461046104612ee1dcba459aa60ac119eba3532a65242082e05608d11dd6abc884608cb1dc3bad58a6d4c2484105508c11aa3b8777900ca1180731772e8965a9dc868050015a234c4084688c65dd2c8d98a6d4da004005488d310211a2319778a6d4c6483244601cf10211a231c534821041e22329770ee14da003c446688108d118cbba59ea6d4c15a233077ae819c298c9e801001902a44786961ddba15309372120b402800ad11a83bb742a612520b408780c911a62042344630eedd1a043c44650eedd0a9849482d021e03244690eed001f03c446588088c41ddba0c94820c9119a2042344630ee9042083c44650ee905a003c446588108d118c3bb741b2327a004004786901dc6c8d5193d0111e1a38776e8166a9b53482d00a002b05488d65dd2cb53b90105a014005688d21dd2cc536a69061e432446888108d118c3bb744b290619223344084688c61dc29b408780c911983bb744b314da9a418790c911a43bc536800f81e432446788088c41ddba4536a632520c32446888108d118c3bc534821041e43244670ee14d20b400780c9119e204234463046104612ee1dce43402800cb119c64f4006488c11943b8690a6327a00404467c801c8010ef90051df200a3be401477c8028ef08c118c3bf4084608c91de118231c7784608c65dfa042304642ee1dc33f4004650ef08c118e3bc2304638eef221942304658ee1dc2cc536a708cd1ddea84946508c119a3b8777910c91942300e788108c118e2042304630ee36464f4084608cd1dc3bbc888108cb1dda9c4084608cb1dc3bbd546508cb1dde444046508c119a11823107b0ef5d2a9853e800f40f20252231277c80284608e0d0c2542304630ee1c464f4007a0c81181e403244621b2327a003d06408c0f1d11853be4016400f400f4048088c7500118aa00231423046209508c118e118231077aa7d001e42303c6a8108c118ea04230463a8108c118cbb83e846384608c41dc64f4006b08c0f1b2042316408462c8108c51021182383448800ca1182321776a6321a014044686803a1ba0d96a632120b402800c91180b00eb6e8165a9a41446078d08d118a11a2313740da365a9a416800c81622303ca1b2d4c29049e81868d08d1189ba34044636e8165a9a41446078cd01118ba0035446) else (if i<12 then 0xd06ca53092905a02233c230c4084688c61ddba25309332120b408648c911a811862022313741b294c64849482d01192234c4084688c61dc26cc8482106192234348846188108d118cbbb740a6134250c9e8010019023c34b0ee3642984d193d0019023c3490ee327a004006488c119c6c85309a327a0023c3472ee14c64a41e801001e83204698ee0c91181ec345c8088c49dc3b9d53919030d193be4088088c9901204231e400c770eef562042304668eef222004006508cd1dc3bbd506508c119a3bbc846508c990011893b9c8c808ca11823364004620ee1072003284608c0f1f202408463c8108c5901204231e4044624ee756e42234345c8088c49dc3bdc848088ca9dee42234344391902192230465c8088c554f202231e4044624ee756a983205888ccd4ca9e40c344aa7901118d3b95348088c89dea98324464aa7901118ceab532a79030d143b9d508390011e1a36773aad4f20e40c47868e1dca9841c800c81622303d86921df2042344644ee1dee424006488cc9dee443206488cb1df202231a772a67232004006408ce1dc34953390107202233a770ee7201e0320466c8088c49dee4032446078b90111893bdc84800c911953bdc886488c0f17202231353c8108c7901204231e408462c80902118f20023164044628ee1ddea83284608cd1dc3bb530820f11942304688ee1dde4423047068d1dda983284648ee1dde423284608cd1dda983c46508c0f1b20223164044628ee1dce4441c808c8d901118a3b85e8839001922303c78ee1dde442304658ee54e118e3b8777900ca1182334772a60f0194232c77c8108c11923be4084608c91df2042304648eed4ce464006508c119e3b953c801001902584608c0f27204231477c80902119320023164084626a7902118c3be4084688c9902118a3bbd5c800cc11963b8677919012003204678ee19da9bc8c800cc119e3bbc8c800cc11963b8676a79001982334770eef201983204668ee19de464006408cd1dc3bb537919012003304688ee1dde424006608cd1dc3bbd5c800cc190233c770eef212003304668ee1dda9e404800cc119e3b87779190011963b8770cef212003306408d108c31dd2042318230c230b53846208308d118e1185192231277c8028810ca1182321771aad00a0223283244624ef9005500118aa0023143284608c70ca11823183284608c7500118aa0023154004622ee8ca118c11872042316408462c8108c50ca118231c3284608c60ca118231a32446246488c49df200b2005202324463c801680146488c4d003901118ba0240446386508c118e19423046306508c118e194230463a8008c5500118aa0023154004622ee1a729b40280094119d192231077c8028ef9004901192231c77c802680146488c4d0039011189192231477c8028ee08c45dc33a591b2d4da else 0xd119520e40446348308c118d20a3284608c910611a231c4184688c7105118aa9c4184688c910611a231e740b2155a99530927221e02ac35049754e20c234464aa7105118f3a0593aad4ca98490900f30d01200eb0ef9d02c1d509272020e4087808f0d4126677ce8164eab534a79072043cc4786a090076a77ea694c1e02a44601ce1df3a059ca672020e408780c815223c3504803b83bc3284688c91de192231a770e272020832046048e1df3a1533901041e03244608c09293b9c84824f019023327789310611a232c4988308d119224c4144636a690611a23224184688c690519423446446488c410611a231c770828ca11a23284184688c6d4c20c2344640ee8c9118e3bc4108308d11963bbd588210611963b8777911051903284608d11dde444108308cb1dc3bb53882106118233c7779010519423287779110420a3284608cf1de118231a7744620ce56464f4006408cd9003d01202231c23046284608c41df3a0d9e800c811e1a3877ce8324e47400640ace1df3a0c9391d002003205608d288c21b4339c8e8008cb90029dd118b2007a024044638ef1061182383458ef1041942304658ef1061182383450ce327a042304658ef90051df200a3be4044638ef900408c208c208c31ddea84984608cb1dc3bc53892f20a023284688eef221942304658ee1dc2cc536a708cd1dde423284608cb1dc3bbc82810c9194233a77aa654c24dc86805011902b446acef9d2a98c9e800c815e2342772b2d4ee43402800c815a234a770b3755a9c32446600671aa52464f4006460ce5646cf4006450ce5646cf4006454ef54ca43402808c815a2342776a7721a0232446602770cf721a43400810c9192234c4084688c69dc368d98a6d2015a233c4084688c69de29b531930c815a2300e888108d118d3bcc84821061922343474ef10211a232077ce8364a98c9e8010019023c34a0ee19fa9853193d002003205408d41dc36867391d002003204601d29dc3b8670a6327a004006408d308c1189ba4d50aa12a64241446784688c488c29df200a1182315745aa154252c888308cf08c118b2042314230462c8108c514e118231d741b215464c4184668a708c118c6ca530a6327a061a30771b214c26f4006408f0d20252231277c80209488c508d118a24e40104a44624461c8088c51061182383445aab222083284658820ca11823244184608e0d10bb85e9aa12a64232446744612ee1786c8c946488cd08d118ba0025046344610ef900488c308d118a3be4012230a230e4044624a688c51df2008bb8d906488c95d06c8c9e800cb0d1a2042344632ee3666aa531928c9119e6ac4084688c935729cc848210511a1a39770ee3646a8c9e8069ab10211a232577ae8367a0623c3460ef5d06c8c9e8088f0d1c3bb744a6126642416810c919223544084688c6d)) else (if i<15 then (if i<14 then 0x53880d001922303c6880d011182303c50ef101a022303c50bc3262034084688cd101a003284688c0f1a2034004a88c0f143bc4068088c1181e374068088c0f123bf4048108c11963b868083902118233277c8108c119067041c8108c11943b953c8038efd012022320788ee10720023285e48288c11913b85e1b2905118233277082d0069dc2f24144608cb90111823184168088c69dc64841c8008ca9dcacd5348288c119aa984168088c954d2094006488c1180b00e84ee1df200ca9e4013534820b11180b00e6192107200232641c8024a7d012022300e51b21072002322770ee9041922304660ee105a022304650ee107202232153c8008c69df2042304641921072042304652a6107204230465e80902118232041c8108c118922a4187888c11913ba4187888c11953b8416810f089dd20c3c44608ca105a003c44640eed00118c3bb4004638eed00118e3ba776800f089dc3bb400464192d001e023247768008c69dc3bb4004648eed4fa034004602cd1dda00231a7768024ee325a00d3bb53882d0089de20b4007a08ca9de20b400464192d001e82303c54ee1a064c4068088cc1e064c4068088ca32620340446248a3262034004b08cb101a00258464193101a00258465880d00190258465880d0012c2320c9880d0012c232b53880d001e02584664ef101a003284608cc3262034004b08cbd01a04230464e80d0211823274068108c1193a034084608c814c64c4068108d119838c4068088c835464c4068108d119a2034006508d11953b868880d011194670c9880d0111962034006a88c89dc3bc4068046a7104194234465880d0111823274068088c0393a034044601c8d4fa034044601cbd01a002b4464e80d01118c20f4007888c0f00732770efd4ca98c9c804c9118234a230a3284688c71dd19423446406508c118e1182314770eef556444006508c11a0bbcd5093b20a0123324844648c71df200b202231640846249048c118f2042316400462c8108c436425dc6cf531935009198bbe53093320a004005448c03a729a4044648c994f200b29e408463c8108c496729a4024608ca94ea00b29e408463ca7900118f29a4006448c119529d401653c8108c794f2042318492462ae8365a99530a40f21901201601d554d641231d5324622eed4ea012300e52efd4c249400800a89180740776e854ca023c46408d090074c4068008c61dc6c74068008cbd01a009bbb74aa6d011e232054c8d0900750776e8366a9b53282d00a003205448c03b2bbad56a7d02a0523a3401d0dd06cb536808f11921200e8aee365a9f40a8148cc365a9853e8040a7101a042323741b2165a98520808f11902342402c03b2a006203408463880d00118c3b8d96a654c64f4008008d1dd06ca49e81ce39071a38771b3d0020123634688308d118d3bc4186508 else 0xf0d1182303c344608c0f0da02230463e815001942344601cc90420a2304642efd004d01118231977a8026a654ea00232740a8088c11903c0770cfd00a002300e71aa3262034084688ccb222034006508d1199a9f40880d001942344601d017864c4068108d119a2034084688c85de2034004a88ca5dc3bc406804e80d01118072353e80d01118072977e80d0015a232977e80d0111903c067e80d011181e00e709488c118c252230463680109488c118fa0223046368088c5d02a003284688c0398bbf40016368088c45dea02231d4044608c65dea9d4068088cbd00a003204601ca17829f4028008c0398388c9880d0111946c8c9880d001aa233077193101a022328d9193101a04234466193101a00254465aa688c1181e255328088c1181e29536802aa688c1181e255368088c754d2084144608ca5dfa000b195368088c65dea9a41a8088cad4ca9f40a800ac119aa9d4044608c85ddba553a80d011199a9953a80d0211a233153e80500118072f4028008c0393a000710d9e805001902300e60a63262034084688cc1ddba453880d0111986c8ce193101a02233453880d011182328776e914e2034044601cf14e2034044608ca1de29c4068088ca1786c8c9880d0211a2338778a6904152232c53880d0012a2328778a69051191a9f4068088c0395a9f4068088c0395a9f4068088c8d4fa034044601ca367a034006488c0f007397706488c1181e297768008c65dc19223046078a5dda022304642ef50211a23254044622ef501a042344652ee1c4a002303c52efd00a0223224105c08c7502118231977e8008c65dd20d4084608cad4ca9d400464a80d0211823254068108c1191a9d4068108c1196a034084608c9d00a042304642a7d00a04230465e805021182312450a63262034084608cc1c62034004641aa3262034084608cd101a003284608cb101a042304646a7101a042304650ef101a0023205e193101a04230466880d02118232077880d02118232f4068108c1193a034084608c8d4fa034084608cbd01a04230464e80d0211823274068108c1181e124644608c060d11823018344608c060da00511823018368088c4106a04231b532a75001192a022304632ef501a00cbbc4184632eed4e20c232177a80d0211a232d4068088c1190bbf4028008c9d00a002300e42a7d00a002300e5e80501118232077083d001e02300e687808c0f007204904607803921e02303c01c8d021e0231c3c0460780391a003c44608c95001e223046078b5001e223046078ad4c64d4004641935011181e2077a80d011181e2853193501a042344666a7501a0032446078d501a0223046078a1dea0340446078a3262034084688ca1c620340446078a35464c4068108d119a2034006508d1194670c9880d0111962034006a88c0f143bc4068088c1181e33) else (if i<16 then 0x1a00cbbb53a80d021196a034044608c85dda9c418464e8050015823274028088c1190a9f402800ac11943b841e800ac11962034006508d1194674406810c819223305e880d00194234466880d00192231245880d001942344650bd101a043206488cd101a003204a88cb101a003c06508d1198a9e4010c9c805001193a06231253e8090111906ce4028008c89df2014004642ef90051dcbbe401c770bd900a002328772a790071dc64e4028008cbd01202231c77c805001e0232c7768108c11923b97768108c11963bb4084608c91dda9b4084608cb1dcbbb4084608cb1dda042304640eed0211823207768108c11923bb5368108c11963bb4084608c91dcbbb4084608cb1dfa034084608cb1dda042304640eed021182324770ee19da042304660ee326203400465193101a003c04650a6127a024044658ee3272002320d94a612a1182328774a654f2010389400640a91182330710640a9119129f404800a9119438e4028008c0f166a95509488c11953b9771ab90089dc64e40280078b3221922304645ab5004b22a014006440f65d02502320712d408c6b54aa84a84608cab2119423046419232320423046519c3272042304654a7502118ea042312d5a8108c6b21194231a328462a8108c118cb544006508c1181e00e746408c0f0c3c2230460788166a9a23046078b54ca0223046078a54da022304640b354d1182303c5aa6d011182322772eedd2a9e406800ca11a2348d9c805001902300e61b2d004d0211a2318d96802e80d001aa2324d56a6d011180728d968088c6d4da02231b53482d011180728d96800c80f12a04230463c805021182312454a71042083d84608cd1042083d84608cb1042083d84608cb1042083d46508c119a2084184608c8d4e2084184608cb50211a231c5e0bc0f51182329770bc32720122f05e1b20f511823345e68028bc1781ea2304650bcd01118c6cd4044630ee3272014003c507a0b8118da022310414800b81181e01601cf1dcbbc4101640efd012003d44650a75001ec23254007b08c75001ec231d4007a0ca1192a042304632a750211823254084608c65df200231977c8108c119064e4028108c0f1434f4007808c81a7a024084608cb900a0025046078a1dc1e223046078a1dc1e223046078a1dda022304640ee0f11182303c50eed0111823217768022eed4e20c23247768088c1193a064044608c0f172014044608c8d0211a231b4084688c6d0211a231b4007908d1191a003c446368088c45dc3bb4044648eed4fa034044601ccd01118a29b4004631b314c64b4004658a6d00118c6cc53192d001196298c968008c8d02118231b4084608c6d02118231ac868108c1191a04231353e80d02118232b4084608c6325a00231b4084608c7d01a042304640bcd4c1181e00e52d408c0f007a04544608c0 else (if i<17 then 0xe8050011903b8c9e8050011943b8c9880d01119464c4068088c812864b404464e80d01118c2524168088c9901200b20240164048020ee54f200f2024016400e4009c8c8022a7900118ca9e4048032a79004d4f202401b530b53c8088c6d4f200b2003203c3c80900190c2f640164009c8c8028ee757204232477c809001902584668ee7232042324776a67232002584668ee1df2003284608cd1df20025846078b1df204231c77c8108c11923be4084630ee367a02402477c805001902328770e3900a002329748648ca1182328d9c808ca1182328cec80500194230466a808c855011902318d92a63261923284608ce1a81942304642bd0c91922304656800c8457a1923244608cb9021922304646810c84166a983244608ca54da022304640b354c192230465aa6d011182325532800c91182328d9193900a002a04668790c91922304651b29011922304656810f0190e1e43246488c1195a003c86430830c91942304650820ca1182320418648ca118232b530820ca1182328410790c91942304662bd14e1923244608cc5dc6ce4046440a6d00190caf4538648c91182334536810c865786c8c946488c119a3b977c808c891dc2f6402800c8119aa0032154084608c75001908a9d4084608c9500a003c06441b294c649c8c805001942304690d3d01204230465c805001902504652790c91922304656810c845021923244608c039a3b8d968008c91dda00231c776a6d0011923bb4004638eed00118c3b8d968008c85dc3bb4004640eed00118c3ec776a7d01a003205608d11dda003204640fb1dda003204658eed00118c3e87768008c81f43b86768008ca3662995368008ca36629b4004641b314ca9b4004650640ac118caf03205608c8f2019023193c0640ac1190192230463680106488c118d2084144608c8d002d4ca9d4004640ee1c433f402800ac119c2f0c9880d0211a2330d96a7101a04234466193101a042344650bc3262034084688cc5de2034004a88cb101a003c84688cbd01a002b44646a7d01a002b4465e80d01118cbbf4068088c81c433f406800c815a23383244608c6d0020c9118231b40083244608c690420a2304642ef501118da004bbd4006432ef54ea03404465e805001582320d50a7d00a002b0466193101a02231245193101a00254465193101a003c44652ef5001902323532a75001192a034084608c9501a04230464e805021182327402800d6118232d5306488c1190a9b40155306488c1192a9b4015532800c9118232d5348210511823295368022ef54ea003223532a7d02a002b04662eedd2a9d4068088ccd4ca9d4068108d119aa9d4068088c1197a014005608c9d001588a9f4028088c11946c8c9e805001582303c705a88c118c16a230463680105a88c118da00416a2304632ef5004d4ca9d4004642ef5 else 0x6cb532a75001515a9953a8001c85ddba5536a7501a01233b53a80d00918072f40a8001c754da9d4068048ca5dea9b5328248cad4fa000718d9e805001912304607803a06cb5368008c03953b8596a690511942cb5348288c03942cb5348288c89dda9a4144640b27212083244601cd1052083284688ca1b56a95519308c11983b86d46508c11953b8d99905211182330d52a63272010368d9aa65001922304601d0364a9e401867193900a0023286d1b3d00694fa024044601ca19c6ce4028008ca9df2014007808ca1f7a01400660ac11993b86d1b288c11963bad58821041942304678ee1de2084146508c119e3bac88821061182383478eeb55a9c410820ca1182344770ef1051903284608cf1dd6444108308c1181e3bc82900ac1190339596a60ac119433bc804634ee19ea983244608cc1f4eaf400660c8159833d532a688c11953bd534821051182343470fb54ca4f400660acc1f429f402800cc15823386744608c69dd2084106488c11983eb532a7501a003306508d11a43ef402800cc15823307d0e3d00a00330640ac11a03b86706488c1195a9f4012770ee9041922304664ee1dda022304651b2723a014004654ee107a002322770ce88c11903394044608c81f7a00330640aca9dd2084144608d0d183eb532a7501a003384688d1501a003284688ca9dea034084688ca1f7a01400660c815823387d2a7d00a003305608ce1f43c0c9e805001982b04607929dd2084144608c0f193bb404463a80d0211a2320d9e80500190232a77e8050061f63b8772a7501a01a3b877a80d0081f63b877a80d0211a233c77a80d0111823287d8ee1dea03402c77a80d0211a232c77e8050111823287d8ee1dc20f4028770ce0ac11913b8774821051182343474ee1dda02232053193501a042344660cf501a003244650ce326a034044654ee1dc33d4068088cc35464c4068108d119a2034006508d1194648c8880d0211a2330671b2d4e2034084688ce9dc33c406800ca11a2338c9880d0211a232a770cf101a002544660cfd01a022322770cfd01a022328598a612811902cc5309408c81362084106508c119864d4084608c9d02118231869591d01204230466e80502118232053193900a042304662e93542522304659aa90420a23046868c5de6a8c9880d0012a23384a44608c6129118231a410820c9118232b40084a44608c612911823184a44608c6129118231c5309412411922984a09208c814da00231877193d00a002328c9)))))
def ql11 : Nat × Nat × Nat × (Nat → Nat) := (1603,8,17,qd11)
def qd12 (i : Nat) : Nat := (if i<2 then (if i<1 then 0xd1c77d4c2306883baa6118c77d4c419022308cc3bea720080119477d4c419022308cc3bdaba98a624864119c77d4c531243208cc3bea62004641dc53b203208c0230efa9882119077d4c531243208cd4fa29b5d320a583489a8e8d140a1af41427f3cf569d9f3a3a708cdd09af73472668cc5497d72e0a591ca9c948f272a4a1c8da90e3209a3e3c7688dff1a0a30cc5b08ab7141a262c47088370fe21d6c376862f0b82136c20e830f0402055c0247f62fd49f65be447bcaf6b9eb1bce678faf0a1ddabb24753ae971cfeb994726ae381c40b8367012ded1bb9b7286d7ed8e1b00b58e6aaed481a6fb49467dece699acb2e6646ec7118b2b0f260febf917b3aeb85c9eb6f96afad0a596ab181600abb656d6ac59551aa30538ea55147fa8aa506e9f893cba71a4d8a9999303a5a84a429269218a3dc46e68c2915aa22e43c685e9088a0c640927ff8fd49f403e127aa8f119dd83b427468e629c5c37e66ea0da99af4352a6838ccd9932320a6360c55986a2fee5de8b9796d02cf657a8aca954029865230a2a93c426a24bf0958925c243647688bd913a215240b07d28f141d4238686e28d8e1a8634306748c9e18e230985d48b361572294051189a61266232843a88200fbe1e7839f86b80c7617982b4852809f612e8241844207c60e881a6832005e60af01388244044207800d48168023a0370057806e008200037a73c29cfaab3dd5c355b0dc9c35270d48c322b0cc5c37a70d69c35a30ca9c32a30c69c3aab0d49bf316fe29bf5a6fce9bf2a6fc69bfaaafe1db7856ddcdb7726dd49b7326dc8ab7716dcc5b7216de29b77a6dce9b72a6dc69b7726bd49af522bc8aaf816bdc5af216be1dab856add5ab55aadcdab536ae09ab526acc9ab816adc5ab516acc5ab216ae29ab7a6ad69ab5a2ace9ab1a6aeaaab8369dcda78269dc9a75269d48a73269c8aa755a3d688d9574156d011b4002d077b3649ce727308acc00b3669ce7a735e8ccaab3dd573559cdc973525cd4873229c1dec19570156c1927008ac19170046c19a702aac1986f222bd956f5d5bc55af64dbd736f0cebd926f08abd916f5c5bc11afa29bcaaafe1d5f7557d565f7357dc95f5257d485f2297dc55f3157661b488ad1deb5956d156b6846d64db5636d0ceb5926d08ab5916d505b411ada01b6706d669b68a6d9e9b4aaad1deac22ab046ae806b9e9ad986a222a9976a1dea9956a156aa846a64da9636a0cea9926a949a822aa645a9416a485a811aa9c1aa306a669aa8a6a9e9aa5a6a8e9a8aaaa65da477a964da563690cea5926908aa620699e9a63a698a9a400a72aa9c77a31568c22a30468c00a32aa8c9a7322270779c15670339c08a70119c2aa709a70269bc88971de5d95571565e845764d5c339708a5d91575055c1197a015caa97269b49a6b1a9ac9a6a181a49a69 else 0x241106400ca2308e1a6cee3bb91200651184679dc7772241106400ca2308e1a50ee2f3aaa9b9020c801944611a877d4dc8900320942338eeba0b36aea6a9d9020a811906411b0775d2c8d022308e1a3cee6aaa664681118470d21775d05935553105401003208d46ae80194461195771dd74b5553b21400c8234aee3bae82cdaba9aa764082a046419046d5ded5d4ec85023208cf3bd91a04801195771dd74b565354dc8105400f2320c8236cee2cca7a0079118470d21771ded5d4e531043c8c83208d4bb8ef6aaa629882a007819046a1de53107400f22308cebb8eeba5aba9e80190468dd0d93555314c41d003208d2bbae82c8aea9882a006411a5771dd74b575314f401003c0ca2308e1a68efba1aa64c83a00801e44611c34b1df74d4c53907400f03288c2350a7a04461193400f22308c83be811184645dc775d353d002330efba1b2a999320e802007819046b5dc775d2d5d4d53b20415003208c1e60eeba5aba044611c3475dc775d059105400c82307933b9aaa9991a044611c3485dc775d1d5d4e5354ec8105400c8230781a74ee2cca7a0065118470d21771dd74b5553b214008d0bb8eeba5aba9aa764082a00641183cc5ded5b214008cb3bdaba04801195771dd74b555332041500400c8230781a01ddba0b2ea9aba9c83a0065118470d2e77b54c8d003c88c238690bb8ef6a89a2087a119d771dc5eb54415003d08d0bb8bc208791184661ded51074088c2336e86caa62999264083a00469dd353b2041d002332ee3bae82b6a6a98a4a0064170460f00e8139771dd74d4c53b23401003288c2386983bee82f1b26499120e8020065118470d3477dd0597575314ec8907400ca2308e1aa19c3bee9a98a764483a008019047432c77dd35314ec8907400ca2308c1e86a8668eeacaa6a48821e06411a15314e41d002328efa9aa6208781904671df531054008cb20c80118c77179531043c0c8233c83a00781192771dc5ed4c410f0233cee3b9b2a999220e80200781944611b2771df5314c41d00400f032094235cee3b8bda98a620e80200781944611b2779d25994e49920419003208d43b8b22484649de741785975553138c89022308e1a64ef3a0b2ead91200651184710404b9de74164c89003c88c238681250ef2ad9020c81118471022779d253b20419003208d03b893644802004661ded514ec85002330ee344aba9c912044611c3499de741785975553139c89064088c23869b3bce82cea720c801944611c3507404c9de74957539224008e0244ef3a0b224b9120c801e44611c34093077d4c419022308cc3bea62084641df5314c490c82330ee2c8921904651df539022308e1a34eeeaaa6e44832044611c3491ddd5d4c3208c1a34efa9c8320065118470d207754c4008c83bea61183449df539064008cb3bb9120c81118470) else (if i<3 then 0x11ad771dd53107405003288c234aee3bae86c99264680a0065118460f434d5dc775d0711665354f405022308c1e869b3b8acea991a044611c3489dd773665332340901400c82b88c23079b3baee6c99c64991a0280190460f2e775de5354f405003508c1e4aee3bae96aaa664680a0065118470d00ed9dd77364d554cc8d02405022308e1a01db3baef6aaa664680a006411a577b544188c2328ee2f1b2290831184675dc771665354c410f4320ba2308c1e62ef6aaa620e80a0064128460f287717ad51043c88c2301d0bbae9a9aa7a02801944611c3403ad77dd0d954c4d12641d01400ca2308e1a01dcbbee82cea6a9c83a02801944611c3403b5d5d003d0c823078cbbee9a9aa720e80a006411a577d4d53107405003288c2301d4bbaa7a02801e878190460f247754e41106400f03208d03baa664c8220c801e06411a47754e41106400c82338bd20c80119077564d954e411064008d03b8bd20c801904661dd53904419003208ce3baa6a4993208832007819046a9dc779d0d9754c8900400d43288c23809a3b9b2ea8801195775d0d5b20485003c48c234681258b364680a006451dec8d01400f0b64680a024611a3469dcd554cc8d014088cebbae86c8b3a9ca6a98a46428020078192460900f0dd05e364d532340c831a44ee64680a0065119a7796653b2340901400c92308d1a5aeeba0da6cdaba9aa629093642801e064152460900f11df74178d5324c8d004008f20c697ba0bc6c9aaa9991a06418d2477dd0d9b56c8d0140ce023c831a5cef3a0bcea89ce44832044611c34b9dc779d0597565372241106400d43288c23809f3bce82cbaae448320079118470d024c9dc779d0597575354dc8904419003c0ca2308e1a04a33b8ef3a391200781944611824a9dc779d05972241106400f03288c238681274ef3a1aaa9991a044611c3491dc6d19f53b21480c82344ef3a591a0065118470d207719ed554dc83203208d13bce96aa9064681118470d2477b5753b204108c1a38ef6ad9020e811184671f47719f53520320ac2344ef3a0cfa999120e801944611c34b5dc775d2d594c4ab20415003208d63bae96aca724d91a044611c34a5dc775d0d93544ab20415003208d7ba1aa64c83a044611c3489dc59356c8d022308e1a42ee3bae96aca62559020a8019046bdd0d9354c932241d002344ef6aca7646812004675dc775d2d514c4a324c8105400c82364ef6a89264681118470d21771ded594c4db204108c1a4aee3b9b26a992640831184691ded594e49b2041d022308d2bb8eeba1b26aca664991a0081118470d3477dd0d994c4a324c8907400ca2308e1a68eeeaaa6e448020065118470d2a771ddd5722419022386913b8eeeab91208832006511846a9dc777555372241106400c82354ee3bbaae4483204470d22771ddd5d4d5372 else 0x17736553d014048ccbbee86cea6a9a83a0280152468d00ec5dcd9323405003248ce3ecef3a3aa64e81118470d26771de7419d593665372340901400c82b88c237cef3a1b2e4681118470d22771de741b467564d935553d014088c23869d3b8ef3a391a04801905711846a9dc779d067365c8d02405003288c23869a3b8cf6ad90e4680a006412846a9dc779d0d954d4972340500320ae2308e1a74ee3bce836ea6e4680a006415c4611c34d1dc67757400c82334ee3bce8a9b91a028019057118470d30771b4677234008cc3bea6e4680a00651184689dc771b467723405003208d33b9b229e81118470d1d77b565314cc9b2041d01400c82508d8bbae86c9aa64e80a044611c34a5df74354c9907405022308e1a52efba1b264c83a02801904695df743644d324c8907405003288c23869abb9b264882a00651184685df743665314c4d32641d022308e1a62ee3bae86c9aa64b91a02801944611c34d5dc775d0d572340500320a82354eebb9aa67192e4680a006411aa77355c8d022308e1a3aee6aaa7a02801905411c3499dd7794d53d01400c82324933baeee4681202801944611c34a5dc771785735549325c81043288c2362ef29b9020e80a00781904a11a9771dc5994d531043c0ca2308d4bbae8e4680a00641584685dd53525c8d01400c82342eee4680a006411997716553d01400c82b08d0bbb9020e80a00641584687234088c6bb9b2a9e80a0446119dd5723400ca232aeee4681202801e0651184695df409014088cabb8eea9992e4083a028019446))
def ql12 : Nat × Nat × Nat × (Nat → Nat) := (229,6,15,qd12)
def qd13 (i : Nat) : Nat := 0x1004622008c440118ae85e6ab22802390469077ba165ab5329b22813811c8234c2008c4401188ee746ad4d91402008c3493bdd1aa5324b2083401186944009dee8d5a9b208340200c8461a5900462ba54c83402008cc77ba356a6c820d00461a4328ef532090046501dce8592a94c92482008c401a01300001dce855a9b2080231006804a00000000ee742ad4c90412008c340e012c00000ef5320900461a300000000000000000000000000000aa94f6934d98d11461d3e470addd87af857a9791622736c6c4d61a729050c9f1392684bc950c217a2e0598ae0e61b8348640be1682a8500961182083c06e0c8168280460780c81401e02802800e5ddd1e49dc9d49d09e41e01dc1d81d41d01cc1c81c41a5d65d9d15d1a496499c95c9549909509a416416019c15c19815819415419015014c188148144125d1d12491c91491092412011c11811411010c1081041
def ql13 : Nat × Nat × Nat × (Nat → Nat) := (56,0,11,qd13)
def qh9 (i : Nat) : Nat := 0x80a4300000004010
def qh10 (i : Nat) : Nat := 0x1c04a09c09011076556b254c0d018c241350000008d0000000bc9b06706e17c291340324640c02aac20f8809330a6139dd502086180a901608c45c208080000788f03909208c0ebe70681900000006c0b806862001522a4861796108000000360003480a000000000000660002780006202e9e0500a2f5aae02600205c00000a5c0f42b030004000079670000a4000000000540600009a1980003a0061681e1370000c80002003e06ab282c000002b38002701540285c0bc000aa05b048000000000a81281081307e0b4000000000000055506a0ac22806080001ead0707012c000000b211c00000000000000650280002e800abe47c0011601c00000044000eb800028000040023d20004b42c04c00e024110570208041c03150705060607040b001111000809030201000401000201010801030000040007040103
def qh11 (i : Nat) : Nat := (if i<2 then (if i<1 then 0xba0dd853ef13d12a00000001b2d3faeb882de153392a4b7865803e01480c7044c000127a00000b606181cc00004da02383d6000054a000032e405d22cfd212301243dd603295a019406dcf1e80000cd067e00100ac16703a40e1d50c14304d20000000089809343c039e18b047e18582a647e063a0ae8125434873f41386ec0bb5722096802e0a4805e157820e0bf847358413fa0e604ecf8402fc4e6142056280274dd0536061004a00053b9565014c066009c08b84c202884595b40328170054812ebe0400003ec0d682380c085a000052224b43bce00055be057072af84842817804e050d12c800d0000000147e00012e8176837409d91ce055800008706f6e27d604e73867009e80dc143d0ad432569049f05d00a03e1816300001900000523839c1790497478d704fd3056ef08929e00002100b8064611a8400000057802d05f204cbade08a132c070851b5c2836212e3bee4db52e6f5e83660ed93ca000022250a001601e003a13f95ea000003cf4600000f48082159835402a85900fa06ba080000014a942ef0584b6e1f84aa000068200001b40f3d22f5d00270133929af2880000c0574208300525818000e9250aa1a0174600056d217d569409b000015d12481218000000000014701fe4a30000443050152c05b202e042200005f7482058600000c651a0000000057610600000f787401cc82780df80001cd05c416b80000c582c800004ea02bd2280b181f057553f21c65220fd10000eb603300608178112808c0fe53ee0fc943c04483821c280000f403b802a12ae00000000d9146a0b8849e519038c04500bc0b4d45af7f81d0050849a524843c0d580002c5025d4fd8154f090224e49004204756920201202e00a1fc0181503028c000320da000000280203d0218080101d00a80007a0100f8a9048278350e40600740c01401a0b001008006054028060c40042c0170380700e01d08600c1181106a0000b837024000070060a00b80c80a0680102100303802c010020200500986f0f00ac030011560507900001400c0080003c0040680e0060ac0181e0000000000c00c0980180c0d00a8000110380140e0130001444c8010f800c1800a02c0000200203006c0d00401005c0a0020a40500b00100a008008020360980e8100ee05c068240160200002100411c2901902c0340000e004078408400080400482602c0400a04800e0040004c0240001d80306c0081b00d006008078200000841701004e020340000440080180103a0380404f01a0100086500004c1480809e170030020280380084c00400424006002000250310a60001983d04803405003012004008210000100281b02000802803002024000100280380386400000c258400a811c0100100001c0081601a00407812000098000090100900781400e0400083c0060540201c else 0xe149413e800008682b00000000518013c166864eef080001ce15f45d0bca4f26d1ce1999602000517201152e94df02aa13200da18700004b8000015900001cb050809082dc4b00000000001f4f1871406c8000f2986b85ce004041700000b605dd431800000003801b580001b3801d5700000f0680005078730000000142c55c4174809609785fefcfd5b213c042450c92a010556e800002ce4f205b006405e61115744e21574c19781fc000025000002c20f1048c03b800152a844148386a80d300000ab95de059bb6e0003abc0c101be00005ea0f600c0000109e106bdca16e95f8ee305ac167bdce13d15cc494032a09f00d61b9816417c066a00004760498358053800208d11ca070173d547000004403f40000724000073b42d393400001de1a300004fd912818a000000002f0000000000000a411881415438000ee1050b564944600000a60da00000c3d20c0003da000005d611781300000544119815249c830a418037a50b060a12d011aeca83060000390000019b43501b0000000155f0000109800000002724a48286f47869a000171014d01a8110854001bd6c447d03ea1d082d41b1800000003d54f5072800000000df000002801da0088556000112206d86aa03f04d810a800010c804c13d8000128d6321ac04c4495043012a566817612b249606b2f8a000000001ac04002ad56f0000000012a00001700000176178800000006220003d0809483c14290068141835ee4c925a0c4101208c000000001e800000e4000034811b902c00003464f0027e000000057e95d00003d4c07b554812806e80003bf44a886981030315528101a000000159b56c200000004ed81f803c973eeb402a200010301190000eb2030812c50e014c006c045867619e3d8151100015c601c5524929415b061006556ac0000274000060e1c705420f300000028000407d1ee00007201b2068a0ba01c758b800019480000000266000018cf8a84a600005ca076000011500000fc058e0000074000538955281d2000000014a110e14881fb563000000004d0020042ef8784880ae0684f87000050f80004e40000ecb020b56dd6240a2817e0ed00c418112b018d800014e813a000024a00804040fe81d4000560a000066818f0086126022c1d23e0855d8000000000019f073c1d403360af80e752a391954692c219b856001f85c257284d600000001b303a7563970200001b8138805c15e82a400001ca1ab0384181838812f028449a040810f94841833ad204d826819083da06b937f4ed859411d39f80050000003868e00000001b78502000000156b019e4e5864808485684a194704e4810a00005b8fd3d51e0a6848004f8326573808819b12e6051845a000016a05bd0e21293d1c03082460000632115bc3814f0000000559015f000143a010651782060003b) else (if i<3 then 0x70605cd5ba5bf100156d074e145818804a01d65c1061a0b580001c7874a0f286a15b1d6aa18fd4960b680005c582c416880000a0ba681a50000000558804b02321af8338000067200005b609ab85804b86f0f1302595c3800003a82f606982ca00006b404e00e2ef3000059e01a00000000f89d5a017e02f2000574e0e58000000034402401ba07c80000e486880000000073844612104e4f45000001e9270000000057885d419956da18a80000ec3ace0ad860955704be449047c04300001a980000ff001801cd0e41c112ca4798249546048e00039ef5b9057156b809e0000202000026249481080ad00000000372041000010e83f600001aa000036e00000000000000000000000054521b100001c2019c40704f800c0618015002a000006a00f800017180000528638f8300001a8821616a871a47b85180900726112070600004ca000126a0e5015af7481e000001e20ee86fc015b9cc0af074c03dd6fe4a9865a000069c0c33c1c0d080f005b53e000002fa1b802f415f846c00000001a783a80a5800052bbe0204d0662095d5fc50c560201c000050a8596130000013c8000188127400000000005562151d5a217ed3720b006bc0000000002005b43c80ce000000000002080e8bdf61b604ac16f874400006140a31462000000000003ac000071007900004a58000058000000003fe0e81022195039a10d92560268514057837000054ac00000d207a80001b6863000005de10482a00000214f2b8000161000010b14661b08000000067aebbbdb8f73058057800c80ce80001c88000548b9e2000073605f037947e026f559110a06483e61cb8000fce862603502a81d182880d4d70016a0320100816957e052557080cc4a953e20003c180ccbdf810750c20210712e4a000000e136a17a537b44a03220cfbf42000024c131823c00013bc0f7174e0000150f09d0f850d84e608f804e2908000166047802f81a2184858a4b1047a000159c02e85541c38340192d59608100014310001486029c0000512e9b85fc06286560a786fe47885ee000058201902cd52bd5fa198026402c807c0fbd6a81b880f4014110800a000017b3e8816484924aa018e016010e13707175d280000ac80461b0033c51b06860000521544800005d036a172124a000023a07d036c1878000f7e926c0003922018143a02c0420eae048a0f185cc00006f251f566a000031a13a00001330312f30800016d149009800121379018fcf137a0003ab7484bae4180148a04895e5561023603a0468ef4129cf1b802ceba967a02600000e291e400050dc1b900000f08218000024e0d3b9ca169031851bb8a14733ae003ebdd0f158000000062400011cc000505218b85720f881440d2845c13515d20e383e003600004e5070000005620bb840e00cbaa810d00000003c400ba80001 else 0xb4052c03fd6b35ab80000250048154851e1018000079800044a83bc1543d00157141a000573c0be028f53c065c0b9815808abe1600000001538001472800000d8000114844e0a500241c08000000521e06900000883e2c2be856a01d85044ad0634000569613f001158880ec060031ef24d3d211804b2f5f85101bd57260ef864410406ee00000d00588000f27569c00000014f686d414cd71a4b4817a0cb000000000000001036040bd9c58406f948a829057986ea5d30298000052e09155b0000041e4e05630520855a54511f2000006240c92ce0380494087870c156049c5c006d216f50a855206d00b90471435858800053fc037bd1a1208324f7195e8000148d527d51000006921ad864c04600014fd3cb20068538022bb705200006f72160407d800c1ab83b21499028eaed0ae56181205d103e44e38000f3f86904f1006600003ae18084ae06583604a6568a0f205ce00004500725516000000000000015cf800010584ee19d011e077000006f05a607b80000d756d959980000ea86a55a78000000000042856c80d412d84ca869600039161028254f9e57081bed))
def qh12 (i : Nat) : Nat := (if i<3 then (if i<1 then 0xea41aa0000ac4a53fc2e7000078aeee9800000002692e5d01e5039005800000a5a9457ab280000000501e00004f1419c146f0000183eac7034da702178aa6b043602520cc0293000005c050f01f98413068c00000003bd4000049869df10b102780da1cb904c9085200002a0b97a0ab8ed5800010810b8814a813254e0084e01c5d6e804e0049580413b05d9777f49480bd806809a00b7c202814d0000ef2aa4380000a340fd1eee835d07c20d049d9bc227b46133c1743b5322de0aa80c8d01c28e1489800002d5a2da0044006000a08b00600202b03d05f00107902400e0410180240010000010400000660050030290cf02504c00f0000140150a900405c00300810201201900901c0020a400503e01e03c02a07005800202803800201d00601406c00504705200000100f0da00301e07800300302706400102602700003303d04800f07300b02107a01f00400005b0110480650a500200001d01e01500600503e02203400000109a03300600700b00301306b01a00103601a05b02000903c00201700400a03d03306200c11f04301c00b00a01e06e00600a01000401901000007701804808c00100b02500700300f01b0130000fb0011130091080060470680040010050010170940030130160bc00100209d03300003001406d05500c00302b00505d01700000400c01d02d00605311d00700307c00100b09201206e00400500000004d0100470090010110060000a004500100403002100300c00800d0000380000010030180480dc01500c00003101800203301a01c00b01100004200402600000502004a00c01905605307000000d02001500613b00407c00300402503a00b08100e00d00000202b01900300f0ba00804b00302300c08a00605800d01300c01205c00902800001700001202507100400200f0190000000880020020050d000000100200704b00100202301900000a02e01e01100d01303f00800201100600d00e02301402500700200300100000800e02e07a00505200100500000104b00101800002900104500401102800600702100200804800a0080ec00200800303101c00303003404a00903103401000500200000b00e04f02200700500107500202a00000300401802101204100000302b04a0000ac06100202700000200e00108a00500400401902000100e00000100b00301700100100503c00000002d00101500600001009c01600102101100103a00409401f01b00001400201400004100f00700002400100f00500f00c01b00e00000a00d00a00203106000600d00706901b00000b01e00300603001701900a01800401100500100400700701a15d00600300403f00200901000800903400501a00b01200604400002c01201203800600601300902b00600100200000801b00000700101501303a00400200000d004 else (if i<2 then 0x24340f1000039d6251c000295f028f0676043c00000002aad441c08b3de1736613288be39b52b580000281381204e6083c2ce04990c3c000046a04a00374555dcf4522da68748f0096800075d6000294882ee0b70541dd3e84c5071800000bfb8b303c40efc1ad139e7b4841ee9a9807b22a8f235d1281caa3f8f704ac638be2a220d2c16b86210383560411d15872b0000b813102050bbc21b8a4a914f02fc1301c83000003c6f6769cc00000000154417b0289054a0c66a1f84b20000059812c0536268603b092f12687252100c1fd8489725c4a3c320030e05b2072400000000000f8fc87791d008cb580000058b5204f540400014a4243e050407f000004280b9023a9622040e0214000005e00004f5cb19107908044406af2000000000995de3800026be152000000ac000053248a9009d2bbe0510910d59e73f40000031848ba40e047c24d39ab0000e0541d60000290a000021ebae40000184017c53b2211814edde203fd07c80e0a8c002ae03860a469af0313ac480ce807a01ad027d4ed5e0d82f90b4818102d90423262f4f0eae2150d092e00029d352e00c5811602d2d1a00b2652bc13785d0a7ac505dcb580000000000081d000075920eb40dc00000c4c00000f400000452136c2e9bc3c210c14701628000030049c000004d500014b3c29582ca000005b0018045c7a0ce36de460194043a00000bd05940a5e10b80000000035814f808a002771be12741b5b82e000042889c0d4fc083208c41d8003379aa024482d8000000000000db03c029540e801ed10732b2a0e281ce11ae025643d8ac1518304ea52fc0001157002800f400051ff2a1207682b79328031800fe87a800007a34c50083031c09180ab5d4184b4000151c811c398ea9d8eb69f1a005d053200dc00001d906a6000025351b20000001c1063ba3000000000000140075c09e81d40000037741d2afd0000010c076c030001b09bc000000000ee27420000000053703a412402ff8404000004fc00002a401a600002b20070000058a40000000000007e405800002b5a08640000000000017b4000000003e0000084590a0000001600a980000000f22c1fe3b52a62e173c00002de000000002200135000012b4000388f0343556000012d5000000009de028da3d2162c0228000a68800001c3021b000153b8313800000000c98274000026880000000000000000001ccd80000238000021d00e3a98b48bc000000009a600002be008406001628a89397801da58fc22554be768c02b40a48132a6934d8c2fb800001c007500af01fc07ec0000000007a2876000000001dd06bc56dc0000000000000b49d3800000000629e8985e4a9920000184801c00001880000500b000013ac0aa82950422094807f838ba366091a9b98642274c0935e6900000062450a8888000079c else 0xa04e42d0046c0384025c28785ea000005d80ab839203b80c48843808e00001418155b83a052e000288780000000e6e419f038e000055f483b00000c720d71cce02d42ae0f4b422304ea07284b58844d2a9a5300000000003c020457882bb03390150187dd1992860388e380000000005ee58b00005063a2e40000122044401b8efa40ad05070052ecdc21c02e7032613bea0d3bc1088608dc22d94cc071043e00003a9404d8000000004162c4af6942e48042000a0f8c1968000287c0a1297a856d044a527e8ed0016ac4406641998362031e17c8934800076c201cdcbbd56c09e84f349d88117000005a40f500880a9c05d430a1472092215c00ff027806804f8c2a00000003e13e9cc786282ae34f480035017a57e04880001500000000000f31371000002700b90000000000008ab054a05c41374a8501a00000000096c0000000007f4abe04c300001208000005b017f4c580a714ac2b740002a44d13b00015649d7500c9783d590424a0000a5de07d48ac81590334428e990057f0000000000003d00000033c14c028a07304dc8000109f08304e4ded6916504e00e542b885fc09b553302bd800000014ef000000f3a9a000a9edf1490a03e0ea816d0000746e0000000558f2bce15a9e54ba08061a00e023a0000093008540f4800024ec00000c1d4da09a882889de850c0848095c14301e40096f41403684d90a161331cd93a9f06e20585f1f021a00000abcabf000002c6132e8c10197013c56bde7285f121740d10000000006f4003c8e984d6aa04172c0000000a8b200000cb047f0a9200101d583a10000f07c276d257000008d5d6f0000a3594a6c2ff39260944056dc4493d071e805ac243d5c308ec0f140fb8047211af6dc097800004b20f54000036a769004481f303210ad60cd008d810406cc00001a490992c6a0000315926201d610480e9939002320b400b383de24da21fdd0903f105fcf2acaed053f0b7403d41b20000001a4e5400005ec0000ed7c00003f2049616e427881ec10de0140057848a043041d1ebbd6190000075484813990000e98403300090000e6a000002ef29ae0001d543bbd01b442d5e0c82faa324f2282738000000000008fa018202ac05b42d8817c773ef6440d3023b0396019c17885ab00a6000010b832e026f56dc094397d052c0954212d60c00000000000050d03e845eca510107211c0ad801f0000000200000000000000158e004901152b0a0001db9d4b1799eea28000006503c00001dc8119921500002a790079268444cca860355a49612540d7115b0aea023423d3b4f0a26130826238f6023cf10031983a60162131cb1f10b30000000205a80000000068800000000c820b069490268084c52e00003b6304f60e169b08243000015f4000100704d40a0dca2840007de06940003db00b8ee20c000)) else (if i<5 then (if i<4 then 0x380cba4180a702fc13d1059e0890123845922bc00001f5051974220e682f5829e064809f431200fa753c00be9ecbaca7b5e167400000000000f2e8a8414c105600de283405140a6050fc00000000792e9da9a582ce0ae6185ea38800026ce187695280a9a9e2027c2ccb9d504bce21821f810104fc05c431e510a00005164035100206e4000297280ef039a0d0803e80f9a4120420ab385ef778000c800001f10b4c5610a5d9264ac460f3422983070094107c00015b3a32eeeec023157b1296ee8404d00e802e008f5cd38192000158a00000250293356e88b3d37b24c600000000044016ee042a7d010a031243fc01a031d043e14540c300002c68179c000049f2afe000294f057a0bf60c54233054d744953b4b12033f017c00002f0d3da000018c406200000000556020a3ca700000a4800000000016040005b03fe0a4a4dc1d31000026bd4f36a2081f622d2000003480007938000294b5639ac1041dcb158580017a466c2a110ee21da0ab000003b27996146c9db8125044c479c10090940be00b1de218602063f4d280fc03172a8402d5e0e84ac01a14940ac4b9a40000153c040800000004ea01168572019c03c40a913c126ac09b4268839e0b6c1416ad400000ac44cc400003cf08f0e3a000002eb222253de8880473a47c0b2c12e54b822cc0dd01b684ee720953c02278080a94016a415080aa03cf5398249bbdc7a30f391c5800c27ad207329030000091042f890e840c292e52f490d81aa71f14ea0812badb7b30f2981e9d5962b6441e80000000a70ae6ec28e812074f4031804583b7072c524c03f80f60bdc16bc230d5f70001585423f3dac01700000290d3cf0000044c130800006784021de30322088f48b00c69174736c52c81ddba8e0b7a0000095000002dc189400015ab00def408000156320f00f7c2e150f9078612cc100001220fe10b026703ff09420e00000039724de0a6ddd48000027a550c85b01840000177c10800620a8cf3d80003a8f768e02c9ecdba380ab440502ea82770000000285c0256047e01dc071126b07e1536c0d9003b00000001e10391d000000002af517f0b040db9cec80dd0b5816d02c7520a0000ed0808d000077aa150c10683d6000000000d8819c041c048c2e3107d725e0c4025d902824ce0d0c00038dd000009f1da0800000000528000117a23a813843099220702c11042d501e10000000004c8222753818c8186000079a8128c00000000c0200380003d95715417368ba382b215aea6898c55f30a8e56a81dc00002741477a94482e900000d80162044900000dc01da846e00f80d6c0000000000045c800000000000000005d5103207600001da008c0000181c00000c10b3000000000311000005d02a2800072e61238000398a0bb40b7400054c60000031de4b010ea4ac4a340003e3774a else 0xc84f39ebe0266746b57f000000000000089c12f84f300000a1e91583f90000000023e0000a9a400002d3824faaa400000000000000014c404b0000027556981f5d3000a6a166c000059125a200002ec10a700000d44000549a054552f0205136975d2ef4ca6202c6779942de90c02b9014a000000012cda40a03501ec05fa00b4000001282e10afc03c81be800001e00808914562003600b200640059269047a090e0000a176114a9a100000b914bc40000000a9c61294b21041a2bba526008c04d27b5602ec0003db200014d1418f05a202d41510294063aa9d442d291704ab032a140c0973ce100c808c1ebe8579018a1076a0e55a1aaea113480a85f6ab2a16782320367a49e004ea89d36d00be098c00039752a3a040c0da824a293a4a21d45d2c00adc4b7418181ff0198e8e417e04b92636ed240ae03c803f40001cae85e321220c049db39d30902158422a00fb28a008d0000004d0000000028b033d779013dc00006190080085818d001a050255c82fe80ae00000e442110479a5c60aec099962106fe0001d2e01be0ace00da884511c00004d62ac4117d048040a40c4534da626043000014b9ac1e01d6a8285870a24168c0f283c7a49b4e881b2950b0000000013c82db01a2e29823395797068e3842630000050a0ae831f800000000fb02970000041201d8000036c0000015c1bf025d000000002b4063d2668000000000000510000004182b1081652a003c000000000002afed29702faf6e800001b907840c502ae836f09080c80ad88146a9df4929cc5800001864e469b70000014006ac07b86180000f278149800006acf6a800010880936506830d148f24c0e5bc00005b007d009b883e39900b6a098015392900775569429e51d801bf45f41ed8000000007bc124800076bc454000015b508ee44d0317830a751aef74237837c270400002d9840904a6180c00052530000e0ec06c02b3a4f00a8c00011dfa0c4135c2eeb9a624e4061c16680000ae810e425b82fb0aaa02e4206800000015346ab780000000000000001c80ab60d48134d00a773c420025d039f0000015429653860c1c06bc29a04fe0010000002080a40c0c82d41c380d9000049b02358239000016a01018522000009ac00051b1003a008c1958470044343c5d433cdf00000ef01ce92cc08a0000000012e20708474800004f205e64f3c1e910ac02de4ac000008b5054043a02ee0433000000002e00496210600002eb010b003d57c800039a174e8042420f041c091a02cc25f029000014c600000000056e00002ab0000014657808ac13a40000000000000000ba34a1831c38f37b20529c000000008fb58d090ad102098200000000000a9e8000002e10a126ec53482cbb938009208f807e821c045e0cc42ab818b0144000026c04bc02ca0fb6a8303b60703407419) else (if i<6 then 0x5e80000000f5c4640814f0000014416653a50652099c2300130a49c4d869f455c50a08ea402b305080000163c119d63e00e4000015402f502ba164085b8373037f4d9ca4380cd298615e1c1a800008f6eed483f0000000000008e8800074c04e7c09d8000099a00001c6827202840000000000000a8e66406bd4e8077c4f602bbb97ba8de0848000000000000605c9cd492a361419269501d8002e112e8f003b9066c058006f03f504b4013c1a750fa78b4129c899511ba9840d1c272800075100f64a1e800000000e9021d844c0086000299c0000000000002f48583085011780888000000157b820794a6294a0feaa81b9f90001516c22f8000000155d8a5a00007a89555800000000ac052f80000350a0120e89ec3536c0000024000000a725a4000029385a176e2303c0005341000000009e93dbc720a0000000000001d413fc21554f30b8253281729347097e0002ab685bb00014d7e9ab111d0bc058e4a6005542b7012a822100000592f77c14f934108780000a388126754213eca87d60e06b0f05c2c3008a05d41045cbe053205da00001d98445004208a002915e1000000029440020ac4200008b9837900000000000000008aef50c00004620000066dee00616274a14900e352f62b1452b42733b430000ea768c8800026d017cc29e81df0564143829482eca8894a41dd004b0095c00880bc040825c844000828208074e0bf5ddd0407ab7a453ab1b82d60b3555c40003e42039f5335cea02b4028a00002e1d0f0217600029a601a800000e940a8502025a80dec2d6d4fe099153a42fa04802c6e0c6c000000076e41168049848322c000000000000272e2ff0000149a0b1144248ad506603a018f9c43819e0b13530027ebaee06b2f6708b1016400015360000006c050412e2acd12d300040e6c9b980db000043b0000030b02d00349ebd8518a4ee144431680000000068c14580000000181411584b60b18020aab70000000004c49388254240615640003dbf009814e4304838f06ea49a81718048069ef21cad700fc00014df01f01287ab8c051c19b8399014c147c11b000077a201ac0e70000266e069c9ab81c0002008a892fd17109f242fc2a802ff03da06741d890a422bf539c258d23b000010041e3048f2928057c07283d7043c00ac14e8000049958fc231d14d0464f379c5784722b2600009b18622774e15328b9846a09f005cc2e90634094803288b40000000000002a9000007ca0d7decb8486000004841693a630136000018b10bc0000f78e92a0523049052d831d854b799c10c804c3d0eaad44e8c0003b44799213d406b13b80b2c0af800001d10c3808f003a027fa2f24f189ca00000a2e0f3000001b701aa0cb0317062a070615601a405e813400c140ac043404594f5ca549626748000000eb8393066549302fa80e101 else 0x15a87c53ce040800000f5925a71ee00002ea0406000152b9e71d1df0000000014d03060298ed9c00051470c6c02ac00004df000004d025403a32008000000002c2065000000003b9311440002a22832a0bae1604a4f517e22c217940a580e70b6e000014714b72936e79c074962000060f8800002bd2b160000ad8058505860d8400001f2082a14809cc0000752616f28f8b8880bccf6e6acc82420c3755cc20b8501011f541031b93d607dc0818a51d4eb74be423c000140000004f1c000024126a6000000013b908acef4000004a97b2612702853b700c22084c9bed589772a53d80000000023a0000228927d0258096c306800000000001e0d50690c2446bc31800007a06e8668cf022009d2000009380000b3eea82a7d8000087c13b0ada0035057e07b800003577b5c0d302780274276a0001c6e045505700f528588308750e13801548435028608b800052130c0005dc21083350000071417300000b7ef3300003ba5a8d614401530420ab760bc807339880bb6064000004fc294200e8a58027108d0f320abc0000061e0b729c90000736200002490000014258bc1f4921e00000001ef0020a063007ec1058000a40212d40e3b94600000000ac18469257e10b408800000000ee90037524275c44b5c0a881a409c84e5804480000c160a50000000002914a9c00003f702a81175cebd10b037a0251de105007884000016980b4a72b4a1c8550000abf0f22000054fd22aa000015e3a3601800001d1d3cac035214e800005cc026c158c2a98565012a0b441e5847170280c09d140000050000000003af0262c00001bb05ca000005e69ed843121ee4ef828482b505e0e2fc8a98000037800002c6914b000013881288026a5da14e08f980000178427807c000072d81214817000009c60055de58000283000001e0be39081c0778abd0437000000002ca800000004544182392d75ce16b8000107107b800e40000000033010ac0003ab509ec0c8e9c0520005e818301f38000077a588c2240162048af6c4ac68389044610bc00c00617b84000080b002807f018a5c6f0185a83e00642df062307ba15a40cf828c06eee1c4a8a3d740c14e3c816c05922938147826e0000000049baacf8410abf614cddd9d251010f53e00c753d873184c9c257bce2a22412782368430089c0d28086d0e80c6a0ebc00015f6a6fa0939e6b841b068a0c95e48852d0b8a0da49ed81b30c114834197935903e64b788a48124027000b02fc807e0b0806d030a81d6a62215b000003630000157ca2c3e360000e4ac2)))
def qh13 (i : Nat) : Nat := 0x22c00007a75a03824f0000980232252bb0000b40ce0a004105eac77ae20a7860c60000de07ca870b80ac28e08400001d0318240042d22ac7bc033060a7a0a70127c90aa06204b22d02626a0b202002f0c362f73101779c205071021b13a672ae0222630cc04229001a0722100190780c00da0dd099b24076646a9e06c07b05205a00000c09a2c700000000008700005900029f73d000000a320957d20290b60a875b0d80960660c404a75e04802a00002e22a04607e0010c70632290a60000500000000d50002280392660a408d0910006240a3a1e00000027ea8601bad328207909d0d27680007b90ad23d01874ca1f000a42ad57b70b50bea660000007a908603c0c90652e101ca9303a07370d0e1ab403e7100450440b9a9401541302404300aae322b08f06802c00000007d21300005100602500027809276aa02a7e00004c0d37ad0bc000000270232a5328f02b74a61304d090013775000000002000000056a4a0d70000002a90000cf0000140000e0a4600000000073208501e2917c72deb2f00009c0000470000a90402010d1000741000000000740000000a5ca0700000d23a06a05408ca48008a8eab503209300003f06d0a203506f0000000ca7b304905b0bb2c374b0370b72b6000000778a3e07009b00000514676627700000022408b00074606904e0ae77709700000009e08a0000d000004f2e30ab09f0dc78e00072c0a50002260002890280897c329603d2a80000300000000007b174f07479a0c123900007f8132d30ba000000262aae0d47e325508072608308274401f0070c2061081016a6124606e0530bda587050e308e0afacb000a3d0750000e429e0b1000000000000000a330df2b703629d7d3094ac80000c578903b06400025e73612f72f0552ababc0d942f06b0000000e207724423b0000cb29a00000e02d057aac00900b0a105ca6b0340000000d60db76205f0bf05d01172d00000079f0000002b30b000000000f7b60000cd2860032562990b3a72000a7d424067088058000a2a2c4010a9d0c800002752830122b088000844249b01403000500e03018a8162b000900248020202c2e008000e0f060442e05050a86a03118b02212020103e082b828241702094000302128041c04068b4050183010070d0042604018081818028100c11268240c07
def qLev : Nat → Nat × Nat × Nat × (Nat → Nat)
  | 8 => ql8
  | 9 => ql9
  | 10 => ql10
  | 11 => ql11
  | 12 => ql12
  | 13 => ql13
  | _ => (0,0,0,fun _ => 0)
def qIdx : Nat → Nat → Option (Nat × Nat)
  | 9 => cLook 2 10 4 2 4 qh9
  | 10 => cLook 40 202 8 7 4 qh10
  | 11 => cLook 291 1764 11 10 4 qh11
  | 12 => cLook 544 3335 12 11 4 qh12
  | 13 => cLook 84 499 9 8 4 qh13
  | _ => fun _ => none
def cRec (k i : Nat) : Nat × Nat :=
  let L := qLev k
  let x := packedAt L.2.2.2 (i*(L.2.1+12)) (L.2.1+12)
  (x &&& ((1 <<< L.2.1)-1), x >>> L.2.1)
def cStep (st : Nat × List Decor × List Decor) (gi mv : Nat) : Nat × List Decor × List Decor :=
  let op := mv &&& 3
  let ia := (mv >>> 2) &&& 15
  let ib := (mv >>> 6) &&& 15
  let ka := (mv >>> 10) &&& 1 == 1
  let kb := (mv >>> 11) &&& 1 == 1
  let a := st.2.1.getD ia defaultDecor
  let b := st.2.1.getD ib defaultDecor
  let z := codeDecor op a b
  (st.1 ||| ((ia ||| (ib <<< 4) ||| (op <<< 8)) <<< (10*gi)), st.2.1 ++ [z], z :: opKeep (op==2) ka kb a b st.2.2)
def cRoot : List Decor := decodeBank 1 0x164 (wiresOf dead)
def cGo : Nat → Nat → Nat → Nat × List Decor × List Decor
  | 0, _, _ => (0x164, cRoot, cRoot)
  | f+1, k, i => cStep (cGo f (k+1) (cRec k i).1) (14-k) (cRec k i).2
def cNode (k i : Nat) := cGo (14-k) k i
def cState (k i : Nat) : List Sig := (cNode k i).2.2.map Prod.fst
def cLinked (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (qLev k).1 then none else
    (dead.autos[pair.2]?).map fun perm => (cState k pair.1).map (movedWord (perm.map swapRows).reverse)
def cRules (k i : Nat) : List BoundPool :=
  let L := qLev k
  let base := L.1*(L.2.1+12)
  let pos := base+L.1*L.2.2.1+packedAt L.2.2.2 (base+i*L.2.2.1) L.2.2.1
  let nr := packedAt L.2.2.2 pos 5
  (getPairs L.2.2.2 7 (15-k) nr (pos+5)).filterMap (fun (a,b) => buildRule dead (cNode k i).1 (15-k) (cNode k i).2.1 a b)
def cContext (k i : Nat) : NodeContext :=
  ((k,(cNode k i).2.2.length,(cNode k i).2.2,preCov (cNode k i).2.2,cRules k i,
    fun tag => ((qIdx k tag).bind (cLinked (k-1))).toList) : NodeContext)
def cVerified (k i : Nat) : Bool :=
  prelim (targetOf dead) (cContext k i) && (if k=0 then true else testAll (cContext k i) (cContext k i).2.2.1)
abbrev cR : Fin 768 → Row := asRow fun j => (dead.samples j).1
abbrev cS : Fin 768 → Row := asRow fun j => (dead.samples j).2
theorem cStep_faith (st : Nat × List Decor × List Decor) (gi mv : Nat)
    (hb : ∀ w ∈ st.2.1, faithful cR cS w) (hw : ∀ w ∈ st.2.2, faithful cR cS w) :
    (∀ w ∈ (cStep st gi mv).2.1, faithful cR cS w) ∧ (∀ w ∈ (cStep st gi mv).2.2, faithful cR cS w) := by
  obtain ⟨o, bank, ws⟩ := st
  have hz : faithful cR cS (codeDecor (mv &&& 3) (bank.getD ((mv >>> 2) &&& 15) defaultDecor)
      (bank.getD ((mv >>> 6) &&& 15) defaultDecor)) :=
    moved_faithful (faithful_get hb _) (faithful_get hb _) _
  refine ⟨fun w h => ?_, fun w h => ?_⟩
  · change w ∈ bank ++ [codeDecor (mv &&& 3) (bank.getD ((mv >>> 2) &&& 15) defaultDecor)
      (bank.getD ((mv >>> 6) &&& 15) defaultDecor)] at h
    rcases List.mem_append.mp h with h | h
    · exact hb w h
    · rw [List.mem_singleton.mp h]; exact hz
  · change w ∈ codeDecor (mv &&& 3) (bank.getD ((mv >>> 2) &&& 15) defaultDecor)
      (bank.getD ((mv >>> 6) &&& 15) defaultDecor) :: opKeep ((mv &&& 3)==2) ((mv >>> 10) &&& 1 == 1)
      ((mv >>> 11) &&& 1 == 1) (bank.getD ((mv >>> 2) &&& 15) defaultDecor)
      (bank.getD ((mv >>> 6) &&& 15) defaultDecor) ws at h
    rcases List.mem_cons.mp h with h | h
    · rw [h]; exact hz
    · exact hw w ((keep_sub _ _ _ _ _ _).subset h)
theorem cGo_faith : ∀ f k i, (∀ w ∈ (cGo f k i).2.1, faithful cR cS w) ∧ (∀ w ∈ (cGo f k i).2.2, faithful cR cS w) := by
  intro f
  induction f with
  | zero =>
    intro k i
    have h := decode_faithful 1 0x164 (wiresOf dead) cR cS (wires_faithful dead)
    exact ⟨h, h⟩
  | succ f ih =>
    intro k i
    exact cStep_faith _ _ _ (ih _ _).1 (ih _ _).2
theorem cLinked_gen (A : Array (List Nat)) (st : Nat → List Sig) (num k : Nat) {T : Sig}
    (names : ∀ x ∈ A.toList, autoOK T (x.map swapRows) = true)
    (earlier : ∀ i < num, Impossible T k (st i).toFinset)
    {pair : Nat × Nat} {out : List Sig}
    (h : (if pair.1 ≥ num then none else (A[pair.2]?).map fun perm => (st pair.1).map (movedWord (perm.map swapRows).reverse)) = some out) :
    Impossible T k out.toFinset := by
  split at h
  · contradiction
  next valid =>
    cases e : A[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (by simpa using Array.mem_of_getElem? e))
theorem cLinked_sound (k : Nat)
    (names : ∀ x ∈ dead.autos.toList, autoOK (targetOf dead) (x.map swapRows) = true)
    (earlier : ∀ i < (qLev k).1, Impossible (targetOf dead) k (cState k i).toFinset)
    {pair out} (h : cLinked k pair = some out) :
    Impossible (targetOf dead) k out.toFinset :=
  cLinked_gen dead.autos (cState k) (qLev k).1 k names earlier h
theorem imp_zero {T : Sig} {ws : List Sig} (hT : T ∉ ws) : Impossible T 0 ws.toFinset := by
  intro t u lo h
  have ht : t = 0 := by omega
  subst t
  generalize he : ws.toFinset = S at h
  have eqS : S = {T} := h (fun k _ S => k = 0 → S = {T}) (fun _ _ => rfl) (fun _ _ _ hn => by contradiction) (fun _ _ _ _ _ hn => by contradiction) rfl
  exact hT (List.mem_toFinset.mp ((he.trans eqS).symm ▸ Finset.mem_singleton_self _))
theorem cVerified_sound (k i : Nat)
    (prior : k>0 → ∀ j < (qLev (k-1)).1, Impossible (targetOf dead) (k-1) (cState (k-1) j).toFinset)
    (checked : cVerified k i = true) : Impossible (targetOf dead) k (cState k i).toFinset := by
  have geo := geomdead
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geo
  have samples := chart_pairs geo.1.1.1 geo.1.1.2
  have cols : ∀ ci ∈ dead.cols.values, Slice (vars dead.mask) (targetOf dead) (subcube ci.1 ci.2.1) ci.2.2.2.2 :=
    fun x hx => col_sound x (boundsBefore known383) (before_sound known383 valid383) (geo.1.2 x hx)
  have names := geo.2
  have hc : cVerified k i = (decide (((cContext k i).2.2.1.map Prod.fst).Nodup) &&
      !(((cContext k i).2.2.1.map Prod.fst).contains (targetOf dead)) &&
      (if k=0 then true else testAll (cContext k i) (cContext k i).2.2.1)) := rfl
  rw [hc, Bool.and_eq_true, Bool.and_eq_true] at checked
  obtain ⟨⟨h1, h2⟩, h3⟩ := checked
  have hN : ((cNode k i).2.2.map Prod.fst).Nodup := of_decide_eq_true h1
  have hT : targetOf dead ∉ (cNode k i).2.2.map Prod.fst := by
    intro hm
    have hcont : ((cContext k i).2.2.1.map Prod.fst).contains (targetOf dead) = true := List.contains_iff_mem.mpr hm
    rw [hcont] at h2
    exact Bool.noConfusion h2
  by_cases h0 : k=0
  · subst k
    exact imp_zero hT
  have test : testAll (cContext k i) (cContext k i).2.2.1 = true := by
    rw [if_neg h0] at h3
    exact h3
  apply node_sound (raw:=vars dead.mask) samples (cGo_faith _ _ _).2 hN hT _ _ test
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound dead cols h
  · intro tag xs hx
    have e : ((qIdx k tag).bind (cLinked (k-1))) = some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact cLinked_sound _ names (prior (by omega)) h
def cBlock (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => cVerified k (start+n) && cBlock k start n
theorem cBlock_at {k start n} (h : cBlock k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    cVerified k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [cBlock,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem cBlock_merge {k start a b} (h : cBlock k start a=true)
    (h' : cBlock k (start+a) b=true) : cBlock k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [cBlock,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,cBlock,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩
theorem cMakeBlock {k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → cVerified k i = true) :
    cBlock k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [cBlock,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩
def cContexts (k start n : Nat) :=
  ((List.range n).map (start+·)).map (cContext k)
def cHeader (k start n ar : Nat) :=
  (cContexts k start n).all (fun c => c.2.1==ar && prelim (targetOf dead) c)
def cRowCut (k start n ar lo len : Nat) :=
  let xs := cContexts k start n
  let b := makeBatch k ar xs
  (List.range len).all (fun d =>
    let i := lo+d
    batchRow b xs i (List.range' (i+1) (ar-(i+1))))
theorem cRowCut_at {k start n ar lo len} (h : cRowCut k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (makeBatch k ar (cContexts k start n)) (cContexts k start n)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha
theorem cRowCut_merge {k start n ar lo a b}
    (h : cRowCut k start n ar lo a=true) (t : cRowCut k start n ar (lo+a) b=true) :
    cRowCut k start n ar lo (a+b)=true := by
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact cRowCut_at h (lo+j) (by omega) (by omega)
  · exact cRowCut_at t (lo+j) (by omega) (by omega)
theorem cCutsRun {k start n ar} (h : cRowCut k start n ar 0 ar=true) :
    runBatch k ar (cContexts k start n)=true := by
  let xs := cContexts k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (makeBatch k ar xs) xs (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := cRowCut_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)
theorem cCutsBlock {k start n ar} (hd : cHeader k start n ar=true)
    (h : cRowCut k start n ar 0 ar=true) : cBlock k start n=true := by
  apply cMakeBlock
  intro i lo hi
  let xs := cContexts k start n
  have hm : cContext k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  show (prelim (targetOf dead) (cContext k i) && (if k=0 then true else testAll (cContext k i) (cContext k i).2.2.1)) = true
  rw [Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hn (cCutsRun h)
def cBoxes (k start n ar lo num : Nat) : Nat → Prop
  | 0 => cRowCut k start n ar lo num=true
  | d+1 => cBoxes k start n ar lo (num/2) d ∧ cBoxes k start n ar (lo+num/2) (num-num/2) d
theorem cBoxesCut {k start n ar lo num d} (h : cBoxes k start n ar lo num d) :
    cRowCut k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := cRowCut_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v
def cCells (k start n ar rows : Nat) : Nat → Prop
  | 0 => cHeader k start n ar=true ∧ cBoxes k start n ar 0 ar rows
  | d+1 => cCells k start (n/2) ar rows d ∧ cCells k (start+n/2) (n-n/2) ar rows d
theorem cCellsBlock {k start n ar rows d} (h : cCells k start n ar rows d) :
    cBlock k start n=true := by
  induction d generalizing start n with
  | zero => exact cCutsBlock h.1 (cBoxesCut h.2)
  | succ d ih =>
    have v := cBlock_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v
theorem cForest_all (top : Nat) (rows : ∀ k ≤ top, cBlock k 0 (qLev k).1 = true) :
    ∀ k ≤ top, ∀ i < (qLev k).1, Impossible (targetOf dead) k (cState k i).toFinset := by
  intro k
  induction k with
  | zero =>
    intro hk i hi
    exact cVerified_sound 0 i (by omega) (cBlock_at (rows 0 hk) i (by omega) (by omega))
  | succ k ih =>
    intro hk i hi
    exact cVerified_sound _ i (fun _ => by simpa using ih (by omega))
      (cBlock_at (rows _ hk) i (by omega) (by omega))
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb8_0 : cBlock 8 0 4 = true := by
  apply cCellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem qa8 : cBlock 8 0 4 = true := qb8_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb9_0 : cBlock 9 0 16 = true := by
  apply cCellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb9_16 : cBlock 9 16 90 = true := by
  apply cCellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem qa9 : cBlock 9 0 106 = true := (cBlock_merge (start:=0) (a:=16) (b:=90) qb9_0 qb9_16)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb10_0 : cBlock 10 0 6 = true := by
  apply cCellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb10_6 : cBlock 10 6 256 = true := by
  apply cCellsBlock (ar:=10) (rows:=0) (d:=5)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb10_262 : cBlock 10 262 20 = true := by
  apply cCellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb10_282 : cBlock 10 282 256 = true := by
  apply cCellsBlock (ar:=11) (rows:=0) (d:=5)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb10_538 : cBlock 10 538 256 = true := by
  apply cCellsBlock (ar:=11) (rows:=0) (d:=5)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb10_794 : cBlock 10 794 143 = true := by
  apply cCellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem qa10 : cBlock 10 0 937 = true := (cBlock_merge (start:=0) (a:=794) (b:=143) (cBlock_merge (start:=0) (a:=538) (b:=256) (cBlock_merge (start:=0) (a:=282) (b:=256) (cBlock_merge (start:=0) (a:=262) (b:=20) (cBlock_merge (start:=0) (a:=6) (b:=256) qb10_0 qb10_6) qb10_262) qb10_282) qb10_538) qb10_794)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb11_0 : cBlock 11 0 2 = true := by
  apply cCellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb11_2 : cBlock 11 2 110 = true := by
  apply cCellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb11_112 : cBlock 11 112 256 = true := by
  apply cCellsBlock (ar:=11) (rows:=0) (d:=5)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb11_368 : cBlock 11 368 256 = true := by
  apply cCellsBlock (ar:=11) (rows:=0) (d:=5)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb11_624 : cBlock 11 624 256 = true := by
  apply cCellsBlock (ar:=11) (rows:=0) (d:=5)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb11_880 : cBlock 11 880 26 = true := by
  apply cCellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb11_906 : cBlock 11 906 256 = true := by
  apply cCellsBlock (ar:=12) (rows:=0) (d:=5)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb11_1162 : cBlock 11 1162 256 = true := by
  apply cCellsBlock (ar:=12) (rows:=0) (d:=5)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb11_1418 : cBlock 11 1418 185 = true := by
  apply cCellsBlock (ar:=12) (rows:=0) (d:=5)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem qa11 : cBlock 11 0 1603 = true := (cBlock_merge (start:=0) (a:=1418) (b:=185) (cBlock_merge (start:=0) (a:=1162) (b:=256) (cBlock_merge (start:=0) (a:=906) (b:=256) (cBlock_merge (start:=0) (a:=880) (b:=26) (cBlock_merge (start:=0) (a:=624) (b:=256) (cBlock_merge (start:=0) (a:=368) (b:=256) (cBlock_merge (start:=0) (a:=112) (b:=256) (cBlock_merge (start:=0) (a:=2) (b:=110) qb11_0 qb11_2) qb11_112) qb11_368) qb11_624) qb11_880) qb11_906) qb11_1162) qb11_1418)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb12_0 : cBlock 12 0 37 = true := by
  apply cCellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb12_37 : cBlock 12 37 116 = true := by
  apply cCellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb12_153 : cBlock 12 153 76 = true := by
  apply cCellsBlock (ar:=12) (rows:=0) (d:=4)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem qa12 : cBlock 12 0 229 = true := (cBlock_merge (start:=0) (a:=153) (b:=76) (cBlock_merge (start:=0) (a:=37) (b:=116) qb12_0 qb12_37) qb12_153)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb13_0 : cBlock 13 0 15 = true := by
  apply cCellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb13_15 : cBlock 13 15 26 = true := by
  apply cCellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem qb13_41 : cBlock 13 41 15 = true := by
  apply cCellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cCells,cBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem qa13 : cBlock 13 0 56 = true := (cBlock_merge (start:=0) (a:=41) (b:=15) (cBlock_merge (start:=0) (a:=15) (b:=26) qb13_0 qb13_15) qb13_41)
theorem qTables : ∀ k ≤ 13, cBlock k 0 (qLev k).1 = true := by
  intro k hk
  interval_cases k
  · exact (rfl : cBlock 0 0 0 = true)
  · exact (rfl : cBlock 1 0 0 = true)
  · exact (rfl : cBlock 2 0 0 = true)
  · exact (rfl : cBlock 3 0 0 = true)
  · exact (rfl : cBlock 4 0 0 = true)
  · exact (rfl : cBlock 5 0 0 = true)
  · exact (rfl : cBlock 6 0 0 = true)
  · exact (rfl : cBlock 7 0 0 = true)
  · exact qa8
  · exact qa9
  · exact qa10
  · exact qa11
  · exact qa12
  · exact qa13
def or04 : Sig := bin true (inputs.getD 4 zero) (inputs.getD 6 zero)
def supplied4 : List Sig := inputs ++ [or04]
theorem sup4_len : supplied4.length = 10 := by decide +kernel
theorem sup4_proper : ∀ i < 10, proper (supplied4.getD i zero) := by
  unfold proper; decide +kernel
theorem sup4_mem (i : Nat) (hi : i < 10) : supplied4.getD i zero ∈ supplied4 := by
  rw [List.getD_eq_getElem _ _ (by rw [sup4_len]; exact hi)]
  exact List.getElem_mem _
theorem or04_bits (r : Row) :
    supplied4.map (bit r) = List.ofFn (sample r) ++ [sample r 4 || sample r 6] := by
  simp only [supplied4,List.map_append,List.map_singleton,or04,bit_bin,sampled]
  rfl
def nbr4 (i : Fin 9) : Nat := [2,1,2,4,72,1,18,4,8].getD i.val 0
def absent4 (i : Fin 9) : Row := Fin.ofNat 512 (nbr4 i)
def present4 (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| nbr4 i)
theorem or4_witness : ∀ i : Fin 9,
    (bit (absent4 i) graph != bit (present4 i) graph) &&
    (supplied4.all fun w => w == inputs.getD i.val zero ||
      bit (absent4 i) w == bit (present4 i) w) = true := by decide +kernel
theorem roots4 {k t S} (h : Live graph k t S) (sub : ∀ v ∈ S, v ∈ supplied4) :
    S = inputs.toFinset ∨ S = supplied4.toFinset := by
  have all (i : Fin 9) : inputs.getD i.val zero ∈ S := by
    have cut := or4_witness i
    simp only [Bool.and_eq_true,Bool.not_eq_true',bne_iff_ne,List.all_eq_true,
      Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at cut
    apply raw_required h _ _ sub (absent4 i) (present4 i) cut.1
    exact fun v hv hne => (cut.2 v hv).resolve_left hne
  have needed : inputs.toFinset ⊆ S := by
    intro v hv
    have hm := List.mem_toFinset.mp hv
    rw [←input_list,List.mem_ofFn] at hm
    obtain ⟨i,rfl⟩ := hm
    exact all i
  by_cases hseed : or04 ∈ S
  · right
    ext w
    constructor
    · exact fun hw => List.mem_toFinset.mpr (sub w hw)
    · intro hw
      have hx := List.mem_toFinset.mp hw
      simp only [supplied4,List.mem_append,List.mem_singleton] at hx
      exact hx.elim (fun h => needed (List.mem_toFinset.mpr h)) (fun e => e ▸ hseed)
  · left
    exact Finset.Subset.antisymm (fun w hw => by
      have hx := sub w hw
      simp only [supplied4,List.mem_append,List.mem_singleton] at hx
      rcases hx with hin | rfl
      · exact List.mem_toFinset.mpr hin
      · exact False.elim (hseed hw)) needed
def rootTable : List (Nat × Nat × Bool × Bool × Nat × Nat) := [(0,1,false,false,0,0),(1,0,false,false,0,0),(0,1,true,false,15,0),(1,0,false,true,15,0),(0,1,false,true,15,2),(1,0,true,false,15,2),(0,1,true,true,41,0),(1,0,true,true,41,0),(0,2,false,false,1,0),(2,0,false,false,1,0),(0,2,true,false,16,0),(2,0,false,true,16,0),(0,2,false,true,17,0),(2,0,true,false,17,0),(0,2,true,true,42,0),(2,0,true,true,42,0),(0,3,false,false,2,0),(3,0,false,false,2,0),(0,3,true,false,18,0),(3,0,false,true,18,0),(0,3,false,true,18,7),(3,0,true,false,18,7),(0,3,true,true,43,0),(3,0,true,true,43,0),(0,4,false,false,3,0),(4,0,false,false,3,0),(0,4,true,false,19,0),(4,0,false,true,19,0),(0,4,false,true,20,0),(4,0,true,false,20,0),(0,4,true,true,44,0),(4,0,true,true,44,0),(0,5,false,false,4,0),(5,0,false,false,4,0),(0,5,true,false,21,0),(5,0,false,true,21,0),(0,5,false,true,22,0),(5,0,true,false,22,0),(0,5,true,true,45,0),(5,0,true,true,45,0),(0,6,false,false,5,0),(6,0,false,false,5,0),(0,6,true,false,23,0),(6,0,false,true,23,0),(0,6,false,true,24,0),(6,0,true,false,24,0),(0,6,true,true,46,0),(6,0,true,true,46,0),(0,7,false,false,6,0),(7,0,false,false,6,0),(0,7,true,false,25,0),(7,0,false,true,25,0),(0,7,false,true,26,0),(7,0,true,false,26,0),(0,7,true,true,47,0),(7,0,true,true,47,0),(0,8,false,false,7,0),(8,0,false,false,7,0),(0,8,true,false,27,0),(8,0,false,true,27,0),(0,8,false,true,27,10),(8,0,true,false,27,10),(0,8,true,true,48,0),(8,0,true,true,48,0),(0,9,false,false,8,0),(9,0,false,false,8,0),(0,9,true,false,28,0),(9,0,false,true,28,0),(0,9,false,true,29,0),(9,0,true,false,29,0),(0,9,true,true,49,0),(9,0,true,true,49,0),(1,2,false,false,4,2),(2,1,false,false,4,2),(1,2,true,false,21,2),(2,1,false,true,21,2),(1,2,false,true,22,2),(2,1,true,false,22,2),(1,2,true,true,45,2),(2,1,true,true,45,2),(1,3,false,false,7,2),(3,1,false,false,7,2),(1,3,true,false,27,2),(3,1,false,true,27,2),(1,3,false,true,27,7),(3,1,true,false,27,7),(1,3,true,true,48,2),(3,1,true,true,48,2),(1,4,false,false,5,2),(4,1,false,false,5,2),(1,4,true,false,23,2),(4,1,false,true,23,2),(1,4,false,true,24,2),(4,1,true,false,24,2),(1,4,true,true,46,2),(4,1,true,true,46,2),(1,5,false,false,1,2),(5,1,false,false,1,2),(1,5,true,false,16,2),(5,1,false,true,16,2),(1,5,false,true,17,2),(5,1,true,false,17,2),(1,5,true,true,42,2),(5,1,true,true,42,2),(1,6,false,false,3,2),(6,1,false,false,3,2),(1,6,true,false,19,2),(6,1,false,true,19,2),(1,6,false,true,20,2),(6,1,true,false,20,2),(1,6,true,true,44,2),(6,1,true,true,44,2),(1,7,false,false,6,2),(7,1,false,false,6,2),(1,7,true,false,25,2),(7,1,false,true,25,2),(1,7,false,true,26,2),(7,1,true,false,26,2),(1,7,true,true,47,2),(7,1,true,true,47,2),(1,8,false,false,2,2),(8,1,false,false,2,2),(1,8,true,false,18,2),(8,1,false,true,18,2),(1,8,false,true,18,10),(8,1,true,false,18,10),(1,8,true,true,43,2),(8,1,true,true,43,2),(1,9,false,false,8,2),(9,1,false,false,8,2),(1,9,true,false,28,2),(9,1,false,true,28,2),(1,9,false,true,29,2),(9,1,true,false,29,2),(1,9,true,true,49,2),(9,1,true,true,49,2),(2,3,false,false,4,7),(3,2,false,false,4,7),(2,3,true,false,22,7),(3,2,false,true,22,7),(2,3,false,true,21,7),(3,2,true,false,21,7),(2,3,true,true,45,7),(3,2,true,true,45,7),(2,4,false,false,9,0),(4,2,false,false,9,0),(2,4,true,false,30,0),(4,2,false,true,30,0),(2,4,false,true,31,0),(4,2,true,false,31,0),(2,4,true,true,50,0),(4,2,true,true,50,0),(2,5,false,false,10,0),(5,2,false,false,10,0),(2,5,true,false,32,0),(5,2,false,true,32,0),(2,5,false,true,32,2),(5,2,true,false,32,2),(2,5,true,true,51,0),(5,2,true,true,51,0),(2,6,false,false,9,10),(6,2,false,false,9,10),(2,6,true,false,30,10),(6,2,false,true,30,10),(2,6,false,true,31,10),(6,2,true,false,31,10),(2,6,true,true,50,10),(6,2,true,true,50,10),(2,7,false,false,11,0),(7,2,false,false,11,0),(2,7,true,false,33,0),(7,2,false,true,33,0),(2,7,false,true,34,0),(7,2,true,false,34,0),(2,7,true,true,52,0),(7,2,true,true,52,0),(2,8,false,false,1,10),(8,2,false,false,1,10),(2,8,true,false,17,10),(8,2,false,true,17,10),(2,8,false,true,16,10),(8,2,true,false,16,10),(2,8,true,true,42,10),(8,2,true,true,42,10),(2,9,false,false,12,0),(9,2,false,false,12,0),(2,9,true,false,35,0),(9,2,false,true,35,0),(2,9,false,true,36,0),(9,2,true,false,36,0),(2,9,true,true,53,0),(9,2,true,true,53,0),(3,4,false,false,3,7),(4,3,false,false,3,7),(3,4,true,false,19,7),(4,3,false,true,19,7),(3,4,false,true,20,7),(4,3,true,false,20,7),(3,4,true,true,44,7),(4,3,true,true,44,7),(3,5,false,false,1,7),(5,3,false,false,1,7),(3,5,true,false,16,7),(5,3,false,true,16,7),(3,5,false,true,17,7),(5,3,true,false,17,7),(3,5,true,true,42,7),(5,3,true,true,42,7),(3,6,false,false,5,7),(6,3,false,false,5,7),(3,6,true,false,23,7),(6,3,false,true,23,7),(3,6,false,true,24,7),(6,3,true,false,24,7),(3,6,true,true,46,7),(6,3,true,true,46,7),(3,7,false,false,6,7),(7,3,false,false,6,7),(3,7,true,false,25,7),(7,3,false,true,25,7),(3,7,false,true,26,7),(7,3,true,false,26,7),(3,7,true,true,47,7),(7,3,true,true,47,7),(3,8,false,false,0,7),(8,3,false,false,0,7),(3,8,true,false,15,7),(8,3,false,true,15,7),(3,8,false,true,15,10),(8,3,true,false,15,10),(3,8,true,true,41,7),(8,3,true,true,41,7),(3,9,false,false,8,7),(9,3,false,false,8,7),(3,9,true,false,28,7),(9,3,false,true,28,7),(3,9,false,true,29,7),(9,3,true,false,29,7),(3,9,true,true,49,7),(9,3,true,true,49,7),(4,5,false,false,9,7),(5,4,false,false,9,7),(4,5,true,false,31,7),(5,4,false,true,31,7),(4,5,false,true,30,7),(5,4,true,false,30,7),(4,5,true,true,50,7),(5,4,true,true,50,7),(4,7,false,false,13,0),(7,4,false,false,13,0),(4,7,true,false,37,0),(7,4,false,true,37,0),(4,7,false,true,38,0),(7,4,true,false,38,0),(4,7,true,true,54,0),(7,4,true,true,54,0),(4,8,false,false,5,10),(8,4,false,false,5,10),(4,8,true,false,24,10),(8,4,false,true,24,10),(4,8,false,true,23,10),(8,4,true,false,23,10),(4,8,true,true,46,10),(8,4,true,true,46,10),(5,6,false,false,9,2),(6,5,false,false,9,2),(5,6,true,false,30,2),(6,5,false,true,30,2),(5,6,false,true,31,2),(6,5,true,false,31,2),(5,6,true,true,50,2),(6,5,true,true,50,2),(5,7,false,false,11,2),(7,5,false,false,11,2),(5,7,true,false,33,2),(7,5,false,true,33,2),(5,7,false,true,34,2),(7,5,true,false,34,2),(5,7,true,true,52,2),(7,5,true,true,52,2),(5,8,false,false,4,10),(8,5,false,false,4,10),(5,8,true,false,22,10),(8,5,false,true,22,10),(5,8,false,true,21,10),(8,5,true,false,21,10),(5,8,true,true,45,10),(8,5,true,true,45,10),(5,9,false,false,12,2),(9,5,false,false,12,2),(5,9,true,false,35,2),(9,5,false,true,35,2),(5,9,false,true,36,2),(9,5,true,false,36,2),(5,9,true,true,53,2),(9,5,true,true,53,2),(6,7,false,false,13,2),(7,6,false,false,13,2),(6,7,true,false,37,2),(7,6,false,true,37,2),(6,7,false,true,38,2),(7,6,true,false,38,2),(6,7,true,true,54,2),(7,6,true,true,54,2),(6,8,false,false,3,10),(8,6,false,false,3,10),(6,8,true,false,20,10),(8,6,false,true,20,10),(6,8,false,true,19,10),(8,6,true,false,19,10),(6,8,true,true,44,10),(8,6,true,true,44,10),(7,8,false,false,6,10),(8,7,false,false,6,10),(7,8,true,false,26,10),(8,7,false,true,26,10),(7,8,false,true,25,10),(8,7,true,false,25,10),(7,8,true,true,47,10),(8,7,true,true,47,10),(7,9,false,false,14,0),(9,7,false,false,14,0),(7,9,true,false,39,0),(9,7,false,true,39,0),(7,9,false,true,40,0),(9,7,true,false,40,0),(7,9,true,true,55,0),(9,7,true,true,55,0),(8,9,false,false,8,10),(9,8,false,false,8,10),(8,9,true,false,28,10),(9,8,false,true,28,10),(8,9,false,true,29,10),(9,8,true,false,29,10),(8,9,true,true,49,10),(9,8,true,true,49,10)]
def rootEntryOK (p q : Nat) (ka kb : Bool) (e : Nat × Nat × Bool × Bool × Nat × Nat) : Bool :=
  e.1 == p && e.2.1 == q && e.2.2.1 == ka && e.2.2.2.1 == kb &&
    (cLinked 13 (e.2.2.2.2.1, e.2.2.2.2.2)).any
      (fun xs => sameWords xs (childTwo supplied4 (supplied4.getD p zero) (supplied4.getD q zero) true ka kb))
def rootOK : Bool :=
  (List.range 10).all fun p => (List.range 10).all fun q => [false,true].all fun ka => [false,true].all fun kb =>
    p == q || supplied4.contains (bin true (supplied4.getD p zero) (supplied4.getD q zero)) ||
    rootTable.any (rootEntryOK p q ka kb)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem rootOK_true : rootOK = true := by decide +kernel
theorem cImp (p q : Nat) (hp : p < 10) (hq : q < 10) (hpq : p ≠ q)
    (hz : bin true (supplied4.getD p zero) (supplied4.getD q zero) ∉ supplied4) (ka kb : Bool) :
    Impossible graph 13 (childTwo supplied4 (supplied4.getD p zero) (supplied4.getD q zero) true ka kb).toFinset := by
  have h := rootOK_true
  unfold rootOK at h
  have h1 := List.all_eq_true.mp h p (List.mem_range.mpr hp)
  have h2 := List.all_eq_true.mp h1 q (List.mem_range.mpr hq)
  have h3 := List.all_eq_true.mp h2 ka (by cases ka <;> simp)
  have h4 := List.all_eq_true.mp h3 kb (by cases kb <;> simp)
  simp only [Bool.or_eq_true, beq_iff_eq] at h4
  rcases h4 with (h4 | h4) | h4
  · exact absurd h4 hpq
  · exact absurd (List.contains_iff_mem.mp h4) hz
  obtain ⟨e, _, he⟩ := List.any_eq_true.mp h4
  simp only [rootEntryOK, Bool.and_eq_true, beq_iff_eq] at he
  obtain ⟨_, hx⟩ := he
  cases hl : cLinked 13 (e.2.2.2.2.1, e.2.2.2.2.2) with
  | none => rw [hl] at hx; simp at hx
  | some xs =>
    rw [hl] at hx
    have hs : sameWords xs (childTwo supplied4 (supplied4.getD p zero) (supplied4.getD q zero) true ka kb) = true := by
      simpa using hx
    have geo := geomdead
    simp only [graphValid, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at geo
    have imp := cLinked_sound 13 geo.2 (fun i hi => cForest_all 13 qTables 13 le_rfl i hi) hl
    have htgt : targetOf dead = graph := by decide +kernel
    rw [htgt, sameWords_sound hs] at imp
    exact imp
theorem orPins (pins : List Nat) (short : pins.length ≤ 2)
    (zn : gv supplied4 ⟨GateOp.or, pins⟩ ∉ supplied4) (zp : proper (gv supplied4 ⟨GateOp.or, pins⟩)) :
    ∃ p q, p < 10 ∧ q < 10 ∧ p ≠ q ∧ gv supplied4 ⟨GateOp.or, pins⟩ = bin true (supplied4.getD p zero) (supplied4.getD q zero) := by
  match pins, short, zn, zp with
  | [], _, _, zp => exact absurd (by simp [gv]) zp.1
  | [i], _, zn, zp =>
    have e : gv supplied4 ⟨GateOp.or, [i]⟩ = supplied4.getD i zero := by
      simp only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, (bin_laws _).2.1]
    rw [e] at zn zp
    exact absurd zp ((get_rep supplied4 i).resolve_left zn)
  | [i, j], _, zn, zp =>
    have e : gv supplied4 ⟨GateOp.or, [i, j]⟩ = bin true (supplied4.getD i zero) (supplied4.getD j zero) := by
      simp only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, (bin_laws _).2.1]
    rw [e] at zn zp ⊢
    by_cases hi : i < 10
    · by_cases hj : j < 10
      · by_cases hij : i = j
        · subst hij
          rw [(bin_laws _).2.2.2.2.2] at zn zp
          exact absurd zp ((get_rep supplied4 i).resolve_left zn)
        · exact ⟨i, j, hi, hj, hij, rfl⟩
      · have z0 : supplied4.getD j zero = zero := List.getD_eq_default _ _ (by rw [sup4_len]; omega)
        rw [z0, (bin_laws _).2.1] at zn zp
        exact absurd zp ((get_rep supplied4 i).resolve_left zn)
    · have z0 : supplied4.getD i zero = zero := List.getD_eq_default _ _ (by rw [sup4_len]; omega)
      rw [z0, bin_comm, (bin_laws _).2.1] at zn zp
      exact absurd zp ((get_rep supplied4 j).resolve_left zn)
theorem closeOr (pins : List Nat) (short : pins.length ≤ 2) (C : Circuit)
    (fan : PEqualNP.MetaComplexity.FanInTwo C) (small : C.size ≤ 13)
    (correct : ∀ x : Fin 9 → Bool, C.eval ((List.ofFn x ++ [x 4 || x 6]) ++ [GateOp.or.eval (pins.map (fun j => (List.ofFn x ++ [x 4 || x 6]).getD j false))]) = edge x) : False := by
  have noRun : Impossible graph 14 inputs.toFinset := dead_start (before_sound known383 valid383) geomdead tablesdead
  let g : Gate := ⟨.or, pins⟩
  let z := gv supplied4 g
  let w := supplied4 ++ [z]
  have zbit (r : Row) : bit r z = GateOp.or.eval (pins.map (fun j =>
      (supplied4.map (bit r)).getD j false)) := by
    simpa only [z,g] using run_bit r g supplied4 (Or.inr (Or.inl rfl))
  have eqGoal : (execute C.gates w).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    change bit r ((execute C.gates w).getD C.output zero) = bit r graph
    rw [←b_read,execute_bits _ _ _ (fun a ha => (fan a ha).1),edge_table]
    change C.eval (w.map (bit r)) = edge (sample r)
    simpa only [w,List.map_append,List.map_singleton,zbit,or04_bits] using correct (sample r)
  have out := get_rep (execute C.gates w) C.output
  rw [eqGoal] at out
  obtain ⟨k,t,S,hk,run,hs⟩ := extract C.gates w fan graph_proper (out.resolve_right fun hn => hn graph_proper)
  have hk13 : k ≤ 13 := by change C.gates.length ≤ 13 at small; omega
  have finish (S' : Finset Sig) (k' t' : Nat) (hk' : k' ≤ 13) (run' : Live graph k' t' S')
      (sub : ∀ a ∈ S', a ∈ supplied4) : False := by
    have formed : represented inputs or04 ∨ witness inputs or04 :=
      bin_rep true (get_rep inputs 4) (get_rep inputs 6)
    obtain ⟨l,v,U,hl,run'',sub'⟩ := pull_gate run' formed sub
    obtain e | e := roots4 run'' (fun a ha => List.mem_append_left _ (sub' a ha))
    · exact noRun l v (by omega) (e ▸ run'')
    · have h4 : or04 ∈ U := e ▸ List.mem_toFinset.mpr (List.mem_append_right _ (by simp))
      exact (by decide +kernel : or04 ∉ inputs) (sub' or04 h4)
  by_cases hzz : z ∈ S ∧ z ∉ supplied4
  · obtain ⟨zS, zn⟩ := hzz
    have zp : proper z := live_proper run z zS
    obtain ⟨p, q, hp, hq, hpq, hzeq0⟩ := orPins pins short zn zp
    have hzeq : z = bin true (supplied4.getD p zero) (supplied4.getD q zero) := hzeq0
    have pa := sup4_proper p hp
    have pb := sup4_proper q hq
    have hab : supplied4.getD p zero ≠ supplied4.getD q zero := by
      intro e
      apply zn
      rw [hzeq, e, (bin_laws _).2.2.2.2.2]
      exact sup4_mem q hq
    let U := S.erase z
    have tail : Live graph k t (insert z U) := by
      rw [show insert z U = S from Finset.insert_erase zS]
      exact run
    have hu : ∀ v ∈ U, v ∈ supplied4 := fun v hv => by
      obtain ⟨hne, hm'⟩ := Finset.mem_erase.mp hv
      rcases List.mem_append.mp (hs v hm') with h1 | h1
      · exact h1
      · exact absurd (List.mem_singleton.mp h1) hne
    have hf : z ∉ insert (supplied4.getD p zero) (insert (supplied4.getD q zero) U) := fun hh => by
      rcases Finset.mem_insert.mp hh with eq | u
      · exact zn (eq ▸ sup4_mem p hp)
      rcases Finset.mem_insert.mp u with eq | u
      · exact zn (eq ▸ sup4_mem q hq)
      · exact zn (hu _ u)
    rw [hzeq] at hf tail zn
    generalize hA : supplied4.getD p zero = a at *
    generalize hB : supplied4.getD q zero = b at *
    have full := Live.binary pa pb hab hf tail
    have sub3 : ∀ v ∈ insert a (insert b U), v ∈ supplied4 := by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact hA ▸ sup4_mem p hp
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact hB ▸ sup4_mem q hq
      · exact hu v hv
    rcases roots4 full sub3 with he | he
    · exact noRun (k+1) t (by omega) (he ▸ full)
    have he : supplied4.toFinset = insert a (insert b U) := he.symm
    have hn : supplied4.Nodup := by decide +kernel
    have am : a ∈ supplied4 := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ supplied4 := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (supplied4.erase a).erase b
    have er : rest.toFinset = (supplied4.toFinset.erase a).erase b := by
      rw [show rest = (supplied4.erase a).erase b by rfl, erase_fin (hn.erase _) b, erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin, kept_fin, er, he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j = a <;>
        by_cases jb : j = b <;> simp [ka, kb, aa, bb, ja, jb, hab, Ne.symm hab]
    have eq : (childTwo supplied4 a b true ka kb).toFinset = insert (bin true a b) U := by
      change (bin true a b :: kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have imp := cImp p q hp hq hpq (hA ▸ hB ▸ zn) ka kb
    rw [hA, hB] at imp
    exact imp k t hk13 (eq.symm ▸ tail)
  · apply finish S k t hk13 run
    intro a ha
    rcases List.mem_append.mp (hs a ha) with h | h
    · exact h
    · have hza : a = z := List.mem_singleton.mp h
      by_contra hn
      exact hzz ⟨hza ▸ ha, hza ▸ hn⟩
theorem foldPrefix (gs : List Gate) (w : List Bool) :
    ∃ t, gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w = w ++ t := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨t, ht⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    exact ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, by rw [List.foldl_cons, ht, List.append_assoc]⟩
theorem mainGlue : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (4 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → ∀ (x5 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[(1 : ℕ)]? = Option.some x5 → x5.op = PEqualNP.CircuitLowerBounds.GateOp.or → x5.inputs ≤ List.map (fun (x8 : ℕ) => [(1 : ℕ), (0 : ℕ), (5 : ℕ), (8 : ℕ), (6 : ℕ), (2 : ℕ), (4 : ℕ), (7 : ℕ), (3 : ℕ)].getD x8 x8) x5.inputs → (16 : ℕ) ≤ x1.size := by
  intro C fan first correct g hg hop _
  by_contra hbig
  have key : ∃ g0 rest, C.gates = g0 :: g :: rest := by
    rcases hc : C.gates with _ | ⟨g0, _ | ⟨g1, rest⟩⟩
    · rw [hc] at hg; simp at hg
    · rw [hc] at hg; simp at hg
    · rw [hc] at hg
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hg
      exact ⟨g0, rest, by rw [hg]⟩
  obtain ⟨g0, rest, hgs⟩ := key
  have hsize : C.size = rest.length + 2 := by
    simp only [Circuit.size, hgs, List.length_cons]
  let C' : Circuit := ⟨rest, C.output⟩
  have fan' : PEqualNP.MetaComplexity.FanInTwo C' := fun x hx =>
    fan x (by rw [hgs]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))
  have small' : C'.size ≤ 13 := by
    change rest.length ≤ 13
    omega
  have short : g.inputs.length ≤ 2 := (fan g (by rw [hgs]; simp)).2
  apply closeOr g.inputs short C' fan' small'
  intro x
  have h1 : C.eval (List.ofFn x) = edge x := congrFun correct x
  have h2 := first x
  have hw : C.wires (List.ofFn x) = rest.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      ((List.ofFn x ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false)]) ++
        [g.op.eval (g.inputs.map fun i => (List.ofFn x ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false)]).getD i false)]) := by
    unfold Circuit.wires
    rw [hgs]
    rfl
  generalize hv : g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false) = v0 at hw
  have hv0 : v0 = (x 4 || x 6) := by
    rw [hw] at h2
    obtain ⟨t, ht⟩ := foldPrefix rest ((List.ofFn x ++ [v0]) ++
        [g.op.eval (g.inputs.map fun i => (List.ofFn x ++ [v0]).getD i false)])
    rw [ht] at h2
    rw [← h2]
    simp [List.getD_eq_getElem?_getD]
  subst hv0
  rw [← h1]
  rw [hop] at hw
  unfold Circuit.eval
  rw [hw]
  rfl
end PEqualNP.Outside.L_meta_3233_aux

open PEqualNP.Outside.L_meta_3233_aux in
theorem PEqualNP.Outside.L_meta_3233 :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (4 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → ∀ (x5 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[(1 : ℕ)]? = Option.some x5 → x5.op = PEqualNP.CircuitLowerBounds.GateOp.or → x5.inputs ≤ List.map (fun (x8 : ℕ) => [(1 : ℕ), (0 : ℕ), (5 : ℕ), (8 : ℕ), (6 : ℕ), (2 : ℕ), (4 : ℕ), (7 : ℕ), (3 : ℕ)].getD x8 x8) x5.inputs → (16 : ℕ) ≤ x1.size := by
  exact mainGlue
