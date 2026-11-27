import PEqualNP.Defs
-- Fix of PR 12665 by brianstrauch: the proof is theirs unchanged; only the helper namespace is renamed to the file own namespace, as the checker requires.
-- The finite circuit verification framework is adapted from dsgallups and the authors of
-- PEqualNP/Outside/L_meta_1665.lean and L_meta_1667.lean under Apache-2.0.
namespace PEqualNP.Outside.L_meta_8533
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
  | 0,t,S => t = 0 ∧ proper target ∧ S = {target}
  | k+1,t,S => (∃ (u : Nat) (U : Finset Sig) (a : Sig), t = u+1 ∧ S = insert a U ∧ proper a ∧
        neg a ∉ insert a U ∧ Live target k u (insert (neg a) U)) ∨
      (∃ (U : Finset Sig) (a b : Sig) (d : Bool), S = insert a (insert b U) ∧ proper a ∧ proper b ∧
        a ≠ b ∧ bin d a b ∉ insert a (insert b U) ∧ Live target k t (insert (bin d a b) U))
theorem Live.stop {target : Sig} (hp : proper target) : Live target 0 0 {target} := ⟨rfl,hp,rfl⟩
theorem Live.unary {target : Sig} {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
    (hfresh : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)) :
    Live target (k+1) (t+1) (insert a U) := Or.inl ⟨t,U,a,rfl,rfl,ha,hfresh,tail⟩
theorem Live.binary {target : Sig} {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)) :
    Live target (k+1) t (insert a (insert b U)) := Or.inr ⟨U,a,b,d,rfl,ha,hb,hab,hfresh,tail⟩
theorem Live.ind {target : Sig} {motive : ∀ (k t : Nat) (S : Finset Sig), Live target k t S → Prop}
    (stop : ∀ (hp : proper target), motive 0 0 {target} (Live.stop hp))
    (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)),
      motive _ _ _ tail → motive _ _ _ (Live.unary ha hfresh tail))
    (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)),
      motive _ _ _ tail → motive _ _ _ (Live.binary ha hb hab hfresh tail))
    {k t : Nat} {S : Finset Sig} (h : Live target k t S) : motive k t S h := by
  induction k generalizing t S with
  | zero =>
    obtain ⟨rfl,hp,rfl⟩ := h
    exact stop hp
  | succ k ih =>
    have hh := h
    rcases hh with ⟨u,U,a,rfl,rfl,ha,hf,tl⟩ | ⟨U,a,b,d,rfl,ha,hb,hab,hf,tl⟩
    · exact unary ha hf tl (ih tl)
    · exact binary ha hb hab hf tl (ih tl)

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
  | 0,bank => bank = roots
  | p+1,bank => (∃ (b : List (Wire R)) (a : Wire R), bank = inv a :: b ∧ Reach roots p b ∧ Available b a) ∨
      (∃ (b : List (Wire R)) (a c : Wire R) (op : Bool), bank = combine op a c :: b ∧ Reach roots p b ∧
        Available b a ∧ Available b c)
theorem Reach.start {R} {roots : List (Wire R)} : Reach roots 0 roots := rfl
theorem Reach.one {R} {roots : List (Wire R)} {p : Nat} {bank : List (Wire R)} {a : Wire R}
    (h : Reach roots p bank) (ha : Available bank a) : Reach roots (p+1) (inv a :: bank) :=
  Or.inl ⟨bank,a,rfl,h,ha⟩
theorem Reach.two {R} {roots : List (Wire R)} {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool)
    (h : Reach roots p bank) (ha : Available bank a) (hb : Available bank b) :
    Reach roots (p+1) (combine op a b :: bank) := Or.inr ⟨bank,a,b,op,rfl,h,ha,hb⟩
theorem Reach.ind {R} {roots : List (Wire R)}
    {motive : ∀ (p : Nat) (bank : List (Wire R)), Reach roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (one : ∀ {p : Nat} {bank : List (Wire R)} {a : Wire R} (h : Reach roots p bank) (ha : Available bank a),
      motive _ _ h → motive _ _ (Reach.one h ha))
    (two : ∀ {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool) (h : Reach roots p bank)
      (ha : Available bank a) (hb : Available bank b), motive _ _ h → motive _ _ (Reach.two op h ha hb))
    {p : Nat} {bank : List (Wire R)} (h : Reach roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero =>
    have hh := h
    obtain rfl : bank = roots := hh
    exact start
  | succ p ih =>
    have hh := h
    rcases hh with ⟨b,a,rfl,hb,ha⟩ | ⟨b,a,c,op,rfl,hb,ha,hc⟩
    · exact one hb ha (ih hb)
    · exact two op hb ha hc (ih hb)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R} (goal : Wire R) (s : Nat) (xs : List (Wire R)) : Prop :=
  ∀ P : Nat → List (Wire R) → Prop, P 0 [goal] →
    (∀ {s : Nat} {xs zs : List (Wire R)}, xs.Perm zs → P s xs → P s zs) →
    (∀ {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool),
      P s (inv a :: kept save a rest) → P (s+1) (a::rest)) →
    (∀ {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op ka kb : Bool),
      P s (combine op a b :: kept ka a (kept kb b rest)) → P (s+1) (a::b::rest)) → P s xs
theorem Run.stop {R} {goal : Wire R} : Run goal 0 [goal] := fun _ h0 _ _ _ => h0
theorem Run.perm {R} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run goal s xs) : Run goal s zs := fun P h0 hp h1 h2 => hp p (h P h0 hp h1 h2)
theorem Run.one {R} {goal : Wire R} {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool)
    (h : Run goal s (inv a :: kept save a rest)) : Run goal (s+1) (a::rest) :=
  fun P h0 hp h1 h2 => h1 save (h P h0 hp h1 h2)
theorem Run.two {R} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op ka kb : Bool)
    (h : Run goal s (combine op a b :: kept ka a (kept kb b rest))) : Run goal (s+1) (a::b::rest) :=
  fun P h0 hp h1 h2 => h2 op ka kb (h P h0 hp h1 h2)
theorem Run.ind {R} {goal : Wire R} {motive : ∀ (s : Nat) (xs : List (Wire R)), Run goal s xs → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs) (h : Run goal s xs),
      motive _ _ h → motive _ _ (Run.perm p h))
    (one : ∀ {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool)
      (h : Run goal s (inv a :: kept save a rest)), motive _ _ h → motive _ _ (Run.one save h))
    (two : ∀ {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op ka kb : Bool)
      (h : Run goal s (combine op a b :: kept ka a (kept kb b rest))), motive _ _ h →
      motive _ _ (Run.two op ka kb h))
    {s : Nat} {xs : List (Wire R)} (h : Run goal s xs) : motive s xs h := by
  have key : ∃ h' : Run goal s xs, motive s xs h' := by
    refine h (fun s xs => ∃ h' : Run goal s xs, motive s xs h') ⟨_,stop⟩ ?_ ?_ ?_
    · rintro s xs zs p ⟨h',m⟩
      exact ⟨_,perm p h' m⟩
    · rintro s a rest save ⟨h',m⟩
      exact ⟨_,one save h' m⟩
    · rintro s a b rest op ka kb ⟨h',m⟩
      exact ⟨_,two op ka kb h' m⟩
  exact key.2

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
def negInput : Sig := neg (inputs.getD 0 zero)
def vars (m : Nat) := (selected m).map Prod.snd ++ (if m.testBit 9 then [negInput] else [])
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 1 &&& x 2) ||| (x 1 &&& x 4) ||| (x 2 &&& x 5) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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
  if (z ||| o).testBit 0 then f &&& 511 else f
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

def remapOK (old rep : Nat) (swaps : List Nat) :=
  properB (graphGoal old) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (vars old) (graphGoal old) (vars rep) (graphGoal rep)
theorem remap_of {old rep L swaps} (ok : remapOK old rep swaps = true)
    (h : Lower (vars rep) (graphGoal rep) L) : Lower (vars old) (graphGoal old) L := by
  simp only [remapOK,Bool.and_eq_true] at ok
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


abbrev BoundPool := Sig × Nat × Nat × List Sig
abbrev BoundPool.domain (c : BoundPool) : Sig := c.1
abbrev BoundPool.bound (c : BoundPool) : Nat := c.2.1
abbrev BoundPool.paid (c : BoundPool) : Nat := c.2.2.1
abbrev BoundPool.wires (c : BoundPool) : List Sig := c.2.2.2

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
-- Repeats the same 64-bit sample pattern across the packed word.
def repeatSamples : Bits := 0x100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
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
  (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 1 &&& x 2) ||| (x 1 &&& x 4) ||| (x 2 &&& x 5) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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
  let n := v.toNat % 18446744073709551557
  let b := n*0x9e3779b97f4a7c15
  let y := (b ^^^ (b >>> 27))*0x517cc1b727220a95
  (y ^^^ (y >>> 41)) % 18446744073709551557
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
    obtain ⟨_,_,rfl⟩ := h
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


abbrev IndexTree (α : Type) := List α
abbrev IndexTree.read {α} (xs : IndexTree α) (i : Nat) : Option α := xs[i]?
abbrev IndexTree.values {α} (xs : IndexTree α) : List α := xs
theorem IndexTree.read_mem {α} (tree : IndexTree α) {i x} (e : IndexTree.read tree i=some x) :
    x ∈ IndexTree.values tree := List.mem_of_getElem? e

abbrev Forest := Nat × Nat × (Nat → Bits × Bits) × List ColumnInfo × Array (List Nat) ×
  (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
abbrev Forest.mask (g : Forest) : Nat := g.1
abbrev Forest.cap (g : Forest) : Nat := g.2.1
abbrev Forest.samples (g : Forest) : Nat → Bits × Bits := g.2.2.1
abbrev Forest.cols (g : Forest) : List ColumnInfo := g.2.2.2.1
abbrev Forest.autos (g : Forest) : Array (List Nat) := g.2.2.2.2.1
abbrev Forest.levels (g : Forest) : Nat → Packing := g.2.2.2.2.2.1
abbrev Forest.index (g : Forest) : Nat → Nat → Option (Nat × Nat) := g.2.2.2.2.2.2

def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  if g.mask.testBit 9 then ws ++ [dneg (ws.getD 0 defaultDecor)] else ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  have base := raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  intro a ha
  unfold wiresOf at ha
  split at ha
  · rcases List.mem_append.mp ha with hm | hm
    · exact base _ hm
    · obtain rfl := List.mem_singleton.mp hm
      exact faithful_neg (faithful_get base 0)
  · exact base _ ha

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
  (IndexTree.read g.cols idx).bind fun ci =>
    materialize (vars g.mask) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ (IndexTree.values g.cols), Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : IndexTree.read g.cols i with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (IndexTree.read_mem g.cols e)

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
    (cols : ∀ ci ∈ (IndexTree.values g.cols), Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
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
    obtain ⟨_,_,rfl⟩ := h
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
  (IndexTree.values g.cols).all (fun c => colCheck g.mask c prior) &&
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
def extendKnown (old : List (Nat × Nat)) (L : Nat) (remaps : List (Nat × List Nat)) :=
  remaps.map (fun v => (v.1,L)) ++ old
theorem extendKnown_ok {old L m remaps} (previous : Known old)
    (main : Lower (vars m) (graphGoal m) L)
    (ok : remaps.all (fun v => remapOK v.1 m v.2) = true) :
    Known (extendKnown old L remaps) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact remap_of (List.all_eq_true.mp ok _ hv) main
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
-- A node certificate may name one applicable restriction or the previously verified child.
-- The number is just a witness. The kernel checks the chosen reason on the actual move.
def recommended (c : NodeContext) (i j op : Nat) (ka kb : Bool) (tag : Nat) : Bool :=
  let a := contextWire c i
  let b := contextWire c j
  let z := movedDecor op a b
  let rest := (opKeep (op==2) ka kb a b c.2.2.1).map Prod.fst
  let action := movedChoice op a b
  let ws := choiceVal action :: rest
  if tag=0 then !properB z.1 || c.2.2.1.any (fun w => w.1 == z.1)
  else if tag=1 then (c.2.2.2.2.2 (keySet ws)).any (sameWords ws)
  else ((c.2.2.2.2.1[(tag-2)/2]?).any fun p =>
    if tag % 2 = 0 then
      decide (i<c.2.2.1.length ∧ j<c.2.2.1.length) &&
        fastCost (summarizePool c.2.2.1 p) (c.1-1) a b op ka kb
    else scalarPoolCut p (c.1-1) rest action)

lemma selected_good {c i j op ka kb tag} (h : recommended c i j op ka kb tag=true) :
    checkAt c i j op ka kb=true := by
  let a := contextWire c i
  let b := contextWire c j
  let z := movedDecor op a b
  let rest := (opKeep (op==2) ka kb a b c.2.2.1).map Prod.fst
  let action := movedChoice op a b
  let ws := choiceVal action :: rest
  have done (cap : closeChild c.2.2.2.2.1 c.2.2.2.2.2 (c.1-1) rest action = true) :
      checkAt c i j op ka kb = true := by
    change evalMove c op a b z ka kb = true
    unfold evalMove
    dsimp only
    repeat' split
    all_goals first | rfl | exact cap
  unfold recommended at h
  dsimp only at h
  split at h
  · change evalMove c op a b z ka kb = true
    change (!properB z.1 || c.2.2.1.any (fun w => w.1 == z.1)) = true at h
    simp only [evalMove,h,ite_true]
    repeat' split
    all_goals rfl
  split at h
  · apply done
    exact Bool.or_eq_true_iff.mpr (Or.inl h)
  cases hp : c.2.2.2.2.1[(tag-2)/2]? with
  | none => simp [hp] at h
  | some p =>
    have mem := List.mem_of_getElem? hp
    simp only [hp,Option.any_some] at h
    apply done
    apply Bool.or_eq_true_iff.mpr
    right
    apply List.any_eq_true.mpr
    refine ⟨p,mem,?_⟩
    split at h
    · obtain ⟨bounds,success⟩ := Bool.and_eq_true_iff.mp h
      have good := of_decide_eq_true bounds
      have present (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
        simp [contextWire,List.getD_eq_getElem?_getD,ht]
      exact fastCost_good (present i good.1) (present j good.2) success
    · exact h


-- The stream records one reason for each surviving state, in gate and state order.
-- A successful check returns the unused part of the stream.
def readTag (s : Nat) : Nat × Nat := (s &&& 127,s >>> 7)

def consume {α : Type} (ok : Nat → α → Bool) (mask code : Nat) : List α → Option Nat
  | [] => some code
  | x::xs =>
    if mask=0 then some code else if mask &&& 1 == 0 then consume ok (mask >>> 769) code xs
    else let p := readTag code
         if ok p.1 x then consume ok (mask >>> 769) p.2 xs else none

theorem consume_sound {α} {ok : Nat → α → Bool} {f : α → Bool}
    (valid : ∀ t c, ok t c=true → f c=true) (m v : Nat) (xs : List α) {r}
    (h : consume ok m v xs=some r) : onMarks f m xs=true := by
  induction xs generalizing m v with
  | nil => rfl
  | cons x xs ih =>
    by_cases mz : m=0
    · simp [onMarks,mz]
    simp only [consume,mz,ite_false] at h
    simp only [onMarks,mz,ite_false,Bool.and_eq_true,Bool.or_eq_true]
    split at h
    next ht => exact ⟨Or.inl ht,ih _ _ h⟩
    next =>
      split at h
      next yes => exact ⟨Or.inr (valid _ x yes),ih _ _ h⟩
      next => cases h

def streamMove (b : Batch) (xs : List NodeContext) (i j op : Nat) (ka kb : Bool) (v : Nat) :=
  let (k,n,r,_,u,cov2) := b
  let un := op==2
  let len := 1+(n-(if ka then 0 else 1)-(if un || kb then 0 else 1))
  if len>k then some v else
    let d := len==k
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp (r*(BitVec.allOnes 768).toNat) op a b'
    let cov := if d then cov2 else u
    let mask := fullMarks r (takePacked cov (packedColumn d a) (packedColumn d b') un ka kb ||| packedColumn d z)
    consume (fun t c => recommended c i j op ka kb t) mask v xs

lemma streamMove_ok (b xs i j op ka kb v r) :
    streamMove b xs i j op ka kb v=some r → batchMove b xs i j op ka kb=true := by
  unfold streamMove batchMove
  dsimp only
  by_cases hlen : b.1 < 1+(b.2.1-(if ka then 0 else 1)-(if (op==2 || kb) then 0 else 1))
  · simp only [gt_iff_lt,hlen,ite_true,imp_true_iff]
  · simp only [gt_iff_lt,hlen,ite_false]
    exact consume_sound (fun t c h => Bool.or_eq_true_iff.mpr (Or.inr (selected_good h))) _ _ _

lemma splitBind {α β} {x : Option α} {f : α → Option β} {r : β}
    (h : x.bind f=some r) : ∃ u, x=some u ∧ f u=some r := by
  cases x with
  | none => cases h
  | some u => exact ⟨u,rfl,h⟩

def streamPair (b xs i j op) (v : Nat) := do
  let w ← streamMove b xs i j op false false v
  let w ← streamMove b xs i j op true false w
  let w ← streamMove b xs i j op false true w
  streamMove b xs i j op true true w
lemma streamPair_ok (b xs i j op v r) (pass : streamPair b xs i j op v = some r) :
    batchPair b xs i j op=true := by
  obtain ⟨v1,h1,more⟩ := splitBind pass
  obtain ⟨v2,h2,more⟩ := splitBind more
  obtain ⟨v3,h3,h4⟩ := splitBind more
  simp only [batchPair,Bool.and_eq_true]
  exact ⟨⟨⟨streamMove_ok _ _ _ _ _ _ _ _ _ h1,streamMove_ok _ _ _ _ _ _ _ _ _ h2⟩,
    streamMove_ok _ _ _ _ _ _ _ _ _ h3⟩,streamMove_ok _ _ _ _ _ _ _ _ _ h4⟩

def streamJs (b : Batch) (xs : List NodeContext) (i : Nat) : List Nat → Nat → Option Nat
  | [],v => some v
  | j::js,v => do
    let w ← streamPair b xs i j 0 v
    let w ← streamPair b xs i j 1 w
    streamJs b xs i js w
lemma streamJs_ok (b xs i js v r) (pass : streamJs b xs i js v=some r) :
    js.all (fun j => batchPair b xs i j 0 && batchPair b xs i j 1)=true := by
  induction js generalizing v with
  | nil => rfl
  | cons j js ih =>
    obtain ⟨v1,h1,more⟩ := splitBind pass
    obtain ⟨v2,h2,more⟩ := splitBind more
    simp only [List.all_cons,Bool.and_eq_true]
    exact ⟨⟨streamPair_ok _ _ _ _ _ _ _ h1,streamPair_ok _ _ _ _ _ _ _ h2⟩,ih _ more⟩

def streamRow (b xs i js) (v : Nat) := do
  let w ← streamMove b xs i i 2 false false v
  let w ← streamMove b xs i i 2 true true w
  streamJs b xs i js w
lemma streamRow_ok (b xs i js v r) (pass : streamRow b xs i js v=some r) : batchRow b xs i js=true := by
  obtain ⟨v1,h1,more⟩ := splitBind pass
  obtain ⟨v2,h2,more⟩ := splitBind more
  simp only [batchRow,Bool.and_eq_true]
  exact ⟨⟨streamMove_ok _ _ _ _ _ _ _ _ _ h1,streamMove_ok _ _ _ _ _ _ _ _ _ h2⟩,streamJs_ok _ _ _ _ _ _ more⟩

def streamCut (words : Array Nat) (g : Forest) (k start n ar : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  (List.range ar).all (fun i =>
    (streamRow b xs i (List.range' (i+1) (ar-(i+1))) (words[i]?.getD 0)).isSome)
lemma streamBlock {w g k start n ar} (h : header g k start n ar=true)
    (run : streamCut w g k start n ar=true) : block g k start n=true := by
  apply cutsBlock h
  unfold rowCut
  simp only [Nat.zero_add]
  unfold streamCut at run
  apply List.all_eq_true.mpr
  intro i hi
  obtain ⟨r,ok⟩ := Option.isSome_iff_exists.mp (List.all_eq_true.mp run i hi)
  exact streamRow_ok _ _ _ _ _ r ok

def blankForest (m k : Nat) : Forest := (m,k,fun _ => (0,0),[],#[[]],fun _ => emptyPacking,fun _ _ => none)

theorem knownAdd {old m L} (h : Known old) (e : Lower (vars m) (graphGoal m) L) : Known ((m,L)::old) := by
  intro v hv
  rcases List.mem_cons.mp hv with rfl | prior
  · exact e
  · exact h _ prior

def g7 : Forest := (7,3,(fun | 0 => (0xbe3fbe3fbe3fbe3fbe3fbe3fbe3fbe3fbe3fbe3fbe3fbe3fbe3fbe3fbe3fbe3fbe3fbe3fbe3fbe3fbe3fbe3fbe3fbe3fbe3fbe3fbe3fbe3fbe3fbe3fbe3fbe3fbe3fbe3fbe3fbe3fbe3fbe3fbe3fbe3fbe3fbe3fbe3fbe3fbe3fbe3fbe3fbe3f,0x84908490849084908490849084908490849084908490849084908490849084908490849084908490849084908490849084908490849084908490849084908490849084908490849084908490849084908490849084908490849084908490849) | 1 => (0xdfc7dfc7dfc7dfc7dfc7dfc7dfc7dfc7dfc7dfc7dfc7dfc7dfc7dfc7dfc7dfc7dfc7dfc7dfc7dfc7dfc7dfc7dfc7dfc7dfc7dfc7dfc7dfc7dfc7dfc7dfc7dfc7dfc7dfc7dfc7dfc7dfc7dfc7dfc7dfc7dfc7dfc7dfc7dfc7dfc7dfc7dfc7dfc7,0x29202920292029202920292029202920292029202920292029202920292029202920292029202920292029202920292029202920292029202920292029202920292029202920292029202920292029202920292029202920292029202920292) | 2 => (0xeff8eff8eff8eff8eff8eff8eff8eff8eff8eff8eff8eff8eff8eff8eff8eff8eff8eff8eff8eff8eff8eff8eff8eff8eff8eff8eff8eff8eff8eff8eff8eff8eff8eff8eff8eff8eff8eff8eff8eff8eff8eff8eff8eff8eff8eff8eff8eff8,0x52405240524052405240524052405240524052405240524052405240524052405240524052405240524052405240524052405240524052405240524052405240524052405240524052405240524052405240524052405240524052405240524) | _ => (0,0)),[],#[[]],(fun | 3 => (1,0,1,0,0,0,0,(fun _ => 0x7)) | _ => emptyPacking),(fun | _ => fun _ => none))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom7 : graphValid g7 (boundsBefore []) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part7_3_0 : block g7 3 0 1 = true :=
  @streamBlock #[0x0,0x0,0x0] g7 3 0 1 3 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem level7_3 : block g7 3 0 1 = true := part7_3_0

theorem table7 : checkedTables g7 3 := by
  intro k hk
  interval_cases k

  · rfl

  · rfl

  · rfl

  · exact level7_3

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low7 : Lower (vars 7) (graphGoal 7) 4 :=
  lower_forest (g:=g7) (i:=0) (hints:=1) (before_sound [] baseKnown) geom7 table7 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def known7 : List (Nat × Nat) := (7,4) :: []

theorem valid7 : Known known7 := knownAdd baseKnown low7

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low15 : Lower (vars 15) (graphGoal 15) 5 :=
  lower_discard (g:=blankForest 15 4) (ci:=(8,0,7,0,4)) (hints:=1) (before_sound known7 valid7) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def known15 : List (Nat × Nat) := (15,5) :: known7

theorem valid15 : Known known15 := knownAdd valid7 low15

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low23 : Lower (vars 23) (graphGoal 23) 5 := remap_of (old:=23) (rep:=15) (swaps:=[67,16]) (by decide +kernel) low15

def known23 : List (Nat × Nat) := (23,5) :: known15

theorem valid23 : Known known23 := knownAdd valid15 low23

def g27 : Forest := (27,3,(fun | 0 => (0x7fb9efff8fa707ff7fb9efff8fa707ff7fb9efff8fa707ff7fb9efff8fa707ff7fb9efff8fa707ff7fb9efff8fa707ff7fb9efff8fa707ff7fb9efff8fa707ff7fb9efff8fa707ff7fb9efff8fa707ff7fb9efff8fa707ff7fb9efff8fa707ff,0x804014e104034129804014e104034129804014e104034129804014e104034129804014e104034129804014e104034129804014e104034129804014e104034129804014e104034129804014e104034129804014e104034129804014e104034129) | 1 => (0xedd7f7fbf979fc1fedd7f7fbf979fc1fedd7f7fbf979fc1fedd7f7fbf979fc1fedd7f7fbf979fc1fedd7f7fbf979fc1fedd7f7fbf979fc1fedd7f7fbf979fc1fedd7f7fbf979fc1fedd7f7fbf979fc1fedd7f7fbf979fc1fedd7f7fbf979fc1f,0x13008810c1081c8613008810c1081c8613008810c1081c8613008810c1081c8613008810c1081c8613008810c1081c8613008810c1081c8613008810c1081c8613008810c1081c8613008810c1081c8613008810c1081c8613008810c1081c86) | 3 => (0xf77c0fc7d7fe07e0f77c0fc7d7fe07e0f77c0fc7d7fe07e0f77c0fc7d7fe07e0f77c0fc7d7fe07e0f77c0fc7d7fe07e0f77c0fc7d7fe07e0f77c0fc7d7fe07e0f77c0fc7d7fe07e0f77c0fc7d7fe07e0f77c0fc7d7fe07e0f77c0fc7d7fe07e0,0xc12e806807c96d40c12e806807c96d40c12e806807c96d40c12e806807c96d40c12e806807c96d40c12e806807c96d40c12e806807c96d40c12e806807c96d40c12e806807c96d40c12e806807c96d40c12e806807c96d40c12e806807c96d4) | 4 => (0xd9f6de7ef4dff800d9f6de7ef4dff800d9f6de7ef4dff800d9f6de7ef4dff800d9f6de7ef4dff800d9f6de7ef4dff800d9f6de7ef4dff800d9f6de7ef4dff800d9f6de7ef4dff800d9f6de7ef4dff800d9f6de7ef4dff800d9f6de7ef4dff800,0x244942ca1097e318244942ca1097e318244942ca1097e318244942ca1097e318244942ca1097e318244942ca1097e318244942ca1097e318244942ca1097e318244942ca1097e318244942ca1097e318244942ca1097e318244942ca1097e318) | _ => (0,0)),[],#[[]],(fun | 3 => (1,0,1,0,0,0,0,(fun _ => 0xf)) | _ => emptyPacking),(fun | _ => fun _ => none))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom27 : graphValid g27 (boundsBefore known23) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part27_3_0 : block g27 3 0 1 = true :=
  @streamBlock #[0x0,0x0,0x0,0x0] g27 3 0 1 4 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem level27_3 : block g27 3 0 1 = true := part27_3_0

theorem table27 : checkedTables g27 3 := by
  intro k hk
  interval_cases k

  · rfl

  · rfl

  · rfl

  · exact level27_3

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low27 : Lower (vars 27) (graphGoal 27) 4 :=
  lower_forest (g:=g27) (i:=0) (hints:=65537) (before_sound known23 valid23) geom27 table27 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def known27 : List (Nat × Nat) := (27,4) :: known23

theorem valid27 : Known known27 := knownAdd valid23 low27

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low39 : Lower (vars 39) (graphGoal 39) 5 := remap_of (old:=39) (rep:=15) (swaps:=[83,67,32,16]) (by decide +kernel) low15

def known39 : List (Nat × Nat) := (39,5) :: known27

theorem valid39 : Known known39 := knownAdd valid27 low39

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low45 : Lower (vars 45) (graphGoal 45) 4 := remap_of (old:=45) (rep:=27) (swaps:=[84,33]) (by decide +kernel) low27

def known45 : List (Nat × Nat) := (45,4) :: known39

theorem valid45 : Known known45 := knownAdd valid39 low45

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low54 : Lower (vars 54) (graphGoal 54) 4 := remap_of (old:=54) (rep:=27) (swaps:=[67,83,16,32]) (by decide +kernel) low27

def known54 : List (Nat × Nat) := (54,4) :: known45

theorem valid54 : Known known54 := knownAdd valid45 low54

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low75 : Lower (vars 75) (graphGoal 75) 4 := remap_of (old:=75) (rep:=27) (swaps:=[100,84,49]) (by decide +kernel) low27

def known75 : List (Nat × Nat) := (75,4) :: known54

theorem valid75 : Known known75 := knownAdd valid54 low75

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low77 : Lower (vars 77) (graphGoal 77) 4 := remap_of (old:=77) (rep:=27) (swaps:=[100,84,49,33]) (by decide +kernel) low27

def known77 : List (Nat × Nat) := (77,4) :: known75

theorem valid77 : Known known77 := knownAdd valid75 low77

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low83 : Lower (vars 83) (graphGoal 83) 4 := remap_of (old:=83) (rep:=27) (swaps:=[100,65,81,16,48]) (by decide +kernel) low27

def known83 : List (Nat × Nat) := (83,4) :: known77

theorem valid83 : Known known83 := knownAdd valid77 low83

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low89 : Lower (vars 89) (graphGoal 89) 4 := remap_of (old:=89) (rep:=27) (swaps:=[97,81,33,48]) (by decide +kernel) low27

def known89 : List (Nat × Nat) := (89,4) :: known83

theorem valid89 : Known known89 := knownAdd valid83 low89

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low90 : Lower (vars 90) (graphGoal 90) 4 := remap_of (old:=90) (rep:=27) (swaps:=[97,16,65,80,49,32]) (by decide +kernel) low27

def known90 : List (Nat × Nat) := (90,4) :: known89

theorem valid90 : Known known90 := knownAdd valid89 low90

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low165 : Lower (vars 165) (graphGoal 165) 4 := remap_of (old:=165) (rep:=27) (swaps:=[116,100,81,16,33,48]) (by decide +kernel) low27

def known165 : List (Nat × Nat) := (165,4) :: known90

theorem valid165 : Known known165 := knownAdd valid90 low165

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low166 : Lower (vars 166) (graphGoal 166) 4 := remap_of (old:=166) (rep:=27) (swaps:=[116,100,81,49,32]) (by decide +kernel) low27

def known166 : List (Nat × Nat) := (166,4) :: known165

theorem valid166 : Known known166 := knownAdd valid165 low166

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low201 : Lower (vars 201) (graphGoal 201) 4 := remap_of (old:=201) (rep:=27) (swaps:=[65,113,100,81,33,48]) (by decide +kernel) low27

def known201 : List (Nat × Nat) := (201,4) :: known166

theorem valid201 : Known known201 := knownAdd valid166 low201

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low228 : Lower (vars 228) (graphGoal 228) 4 := remap_of (old:=228) (rep:=27) (swaps:=[65,16,116,96,48,81,32]) (by decide +kernel) low27

def known228 : List (Nat × Nat) := (228,4) :: known201

theorem valid228 : Known known228 := knownAdd valid201 low228

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low232 : Lower (vars 232) (graphGoal 232) 4 := remap_of (old:=232) (rep:=27) (swaps:=[65,116,96,81,32]) (by decide +kernel) low27

def known232 : List (Nat × Nat) := (232,4) :: known228

theorem valid232 : Known known232 := knownAdd valid228 low232

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low240 : Lower (vars 240) (graphGoal 240) 4 := remap_of (old:=240) (rep:=27) (swaps:=[65,67,115,96,81,32]) (by decide +kernel) low27

def known240 : List (Nat × Nat) := (240,4) :: known232

theorem valid240 : Known known240 := knownAdd valid232 low240

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low31 : Lower (vars 31) (graphGoal 31) 6 :=
  lower_discard (g:=blankForest 31 5) (ci:=(8,0,23,0,5)) (hints:=65537) (before_sound known240 valid240) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def known31 : List (Nat × Nat) := (31,6) :: known240

theorem valid31 : Known known31 := knownAdd valid240 low31

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low47 : Lower (vars 47) (graphGoal 47) 6 := remap_of (old:=47) (rep:=31) (swaps:=[84,33]) (by decide +kernel) low31

def known47 : List (Nat × Nat) := (47,6) :: known31

theorem valid47 : Known known47 := knownAdd valid31 low47

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low55 : Lower (vars 55) (graphGoal 55) 6 := remap_of (old:=55) (rep:=31) (swaps:=[67,83,16,32]) (by decide +kernel) low31

def known55 : List (Nat × Nat) := (55,6) :: known47

theorem valid55 : Known known55 := knownAdd valid47 low55

def g79 : Forest := (79,6,(fun | 0 => (0x9dc5ee8401e7fc07fffb7efefcffb5377cf8f5a87afceffbdb9badfd073b8bdd0803cff80ffff6fdfdf9ff6a6ef9f1eb50f5f9dff7b7375bfa0e7717ba10079ff01fffedfbfbf3fed4ddf3e3d6a1ebf3bfef6e6eb7f41cee2f74200f3fe03fff,0x501808480a0448112248005820040c0d04100000042825420002009040a030109014089022449000b04008181a0820000008504a840004012081406021202811204489200160801030341040000010a09508000802410280c04240502240891) | 1 => (0xdc7e3898067a03f80fe6fd7cbefb5fd8cf4fd17f3d79fa6fd0b5f63fb9b8fc71300cf407f01fcdfaf97df6bfb19e9fa2fe7af3f4dfa16bec7f7371f8e26019e80fe03f9bf5f2fbed7f633d3f45fcf5e7e9bf42d7d8fee6e3f1c4c033d01fc07f,0x406c3819124a912a44d900804144052400b82a32a188012a500100142080d870322495225489b2010082880a480170546543100254a00200284101b0e064492a44a9136402010510149002e0a8ca862004a940040050820361c0c89254895226) | 2 => (0x607bcfe0079c03fff01dadffd7c0b7ff79cdecf7bf5195bcb597cd2afec0f79fc00f3807ffe03b5bffaf816ffef39bd9ef7ea32b796b2f9a55fd81ef3f801e700fffc076b7ff5f02dffde737b3defd4656f2d65f34abfb03de7f003ce01fff80,0x12076225152254a9025210181908100a00448c1015600009fc8d220800240ec44a2a44a95204a4203032102014008918202ac00013f91a441000481d8894548952a409484060642040280112304055800027f234882000903b1128a912a548) | 3 => (0x77bf377ff81ffc00000fea9da59fefffd63e4ed3e8a7cf527efff3d04cef7e6efff03ff800001fd53b4b3fdfffac7c9da7d14f9ea4fdffe7a099defcddffe07ff000003faa76967fbfff58f93b4fa29f3d49fbffcf4133bdf9bbffc0ffe00000,0x10882428381e3860c190154210f00005030809441b884920011bc2004821104850703c70c183202a8421e0000a06101288371092400237840090422090a0e078e1830640550843c000140c2025106e212480046f08012084412141c0f1c3060c) | 6 => (0x6fdcb57fffe000000013b7277ffcc97dcaab5e67a1ea3e92af7c1f4f7edfb96affffc0000000276e4efff992fb9556bccf43d47d255ef83e9efdbf72d5ffff800000004edc9dfff325f72aad799e87a8fa4abdf07d3dfb7ee5abffff00000000,0x6c540057c7e1c3870e0c4810840a3660f0e14091e4312449e820154816d8a800af8fc3870e1c18902108146cc1e1c28123c8624893d0402a902db150015f1f870e1c383120421028d983c385024790c49127a08055205b62a002be3f0e1c3870) | _ => (0,0)),[(0,64,7,8,5),(64,0,15,0,5),(2,0,77,0,4),(4,0,75,0,4),(8,0,7,0,4),(8,64,7,0,4)],#[[],[33]],(fun | 4 => (1,2,3,0,0,0,0,(fun _ => 0x5b14910)) | 5 => (5,1,3,0,0,6,0,(fun _ => 0x10412180c0606d2240fd21fd10fe00f611fa00)) | 6 => (1,0,3,0,0,0,0,(fun _ => 0xb1a20df)) | _ => emptyPacking),(fun | 5 => (lookupWord 1 4 0 5 0 1 (fun _ => 0x3be)) | 6 => (lookupWord 3 10 2 8 3 1 (fun _ => 0x84011003830a2d4c660)) | _ => fun _ => none))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom79 : graphValid g79 (boundsBefore known55) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part79_4_0 : block g79 4 0 1 = true :=
  @streamBlock #[0x0,0x0,0x0,0x0,0x0] g79 4 0 1 5 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem level79_4 : block g79 4 0 1 = true := part79_4_0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part79_5_0 : block g79 5 0 2 = true :=
  @streamBlock #[0x0,0x0,0x0,0x0,0x183] g79 5 0 2 5 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part79_5_2 : block g79 5 2 3 = true :=
  @streamBlock #[0x0,0x2,0x1,0x0,0x2,0x0] g79 5 2 3 6 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem level79_5 : block g79 5 0 5 = true := (@block_merge g79 5 0 2 3 part79_5_0 part79_5_2)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part79_6_0 : block g79 6 0 1 = true :=
  @streamBlock #[0x810218280880218081,0x4086060218301,0x1021820401,0x2041050c,0x102] g79 6 0 1 5 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem level79_6 : block g79 6 0 1 = true := part79_6_0

theorem table79 : checkedTables g79 6 := by
  intro k hk
  interval_cases k

  · rfl

  · rfl

  · rfl

  · rfl

  · exact level79_4

  · exact level79_5

  · exact level79_6

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low79 : Lower (vars 79) (graphGoal 79) 7 :=
  lower_forest (g:=g79) (i:=0) (hints:=50331649) (before_sound known55 valid55) geom79 table79 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def known79 : List (Nat × Nat) := (79,7) :: known55

theorem valid79 : Known known79 := knownAdd valid55 low79

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low87 : Lower (vars 87) (graphGoal 87) 7 := remap_of (old:=87) (rep:=79) (swaps:=[67,16]) (by decide +kernel) low79

def known87 : List (Nat × Nat) := (87,7) :: known79

theorem valid87 : Known known87 := knownAdd valid79 low87

def g91 : Forest := (91,6,(fun | 0 => (0x3b37f6980203380ffff5f73debdfeb693f3c49fefd0f66fd633d665f72766fed300406701fffebee7bd7bfd6d27e7893fdfa1ecdfac67accbee4ecdfda60080ce03fffd7dcf7af7fada4fcf127fbf43d9bf58cf5997dc9d9bfb4c01019c07fff,0x1211801a42911a82952a088010000cf4280868004620e32a888164061024230034852235052a541100200019e85010d0008c41c6551102c80c20484600690a446a0a54a82200400033d0a021a00118838caa2205901840908c00d21488d414a9) | 1 => (0x7d2b1f200c03cff80feeef1f776abff6febc90d7d59aafbcfde3dd9cd6fa563e4018079ff01fddde3eeed57fedfd7921afab355f79fbc7bb39adf4ac7c80300f3fe03fbbbc7dddaaffdbfaf2435f566abef3f78f76735be958f900601e7fc07f,0x92207241d0a443c48d110604091c20010d7125819040400520889100412440e483a14887891a220c08123840021ae24b032080800a41112200824881c90742910f12344418102470800435c496064101001482224401049103920e85221e246) | 3 => (0x8e97edc00ffcf00ff00f7bdf1ef5cafdacf5cfba2e357ceb7fd32bf8dd1d2fdb801ff9e01fe01ef7be3deb95fb59eb9f745c6af9d6ffa657f1ba3a5fb7003ff3c03fc03def7c7bd72bf6b3d73ee8b8d5f3adff4cafe37474bf6e007fe7807f80,0x48004c0942ce12962908504e01811011160908730c4088042220a58c0090009812859c252c5210a09c030220222c1210e61881100844414b1801200130250b384a58a421413806044044582421cc3102201088829630024002604a167094b14) | 4 => (0x56f823fff000fff00019fbf3e417f7ffe7c27ed353eeaf49d4febcf77eadf047ffe001ffe00033f7e7c82fefffcf84fda6a7dd5e93a9fd79eefd5be08fffc003ffc00067efcf905fdfff9f09fb4d4fbabd2753faf3ddfab7c11fff8007ff8000,0x4082048e030b9c1830606040960090425088002a4a351c004a020e55208104091c0617383060c0c0812c012084a1100054946a380094041caa41020812380c2e7060c181810258024109422000a928d47001280839548204102470185ce0c18) | 6 => (0xbfe8cc7fffff00000017cff4dfb8fd3d79fbbe626afa5d5bcf4dfb67ad7fd198fffffe0000002f9fe9bf71fa7af3f77cc4d5f4bab79e9bf6cf5affa331fffffc0000005f3fd37ee3f4f5e7eef989abe9756f3d37ed9eb5ff4663fffff8000000,0x3a2048370bc306060c08301a00064252000443000b08062d994910002c7440906e17860c0c18106034000c84a40008860016100c5b3292200058e88120dc2f0c18183020c0680019094800110c002c2018b665244000b1d10241b85e18303060) | _ => (0,0)),[(1,0,90,0,4),(2,0,89,0,4),(8,0,83,0,4),(16,0,75,0,4),(64,0,27,0,4)],#[[],[49, 100],[16, 67],[16, 64, 48, 99],[48, 16, 97, 65],[48, 97],[64, 99],[64, 97, 49, 48],[96, 49, 65, 16],[96, 65]],(fun | 4 => (1,2,3,0,0,0,0,(fun _ => 0x5d14530)) | 5 => (3,1,3,0,0,4,0,(fun _ => 0x1e90fd30fd10fa00)) | 6 => (1,0,3,0,0,0,0,(fun _ => 0x11a20bf)) | _ => emptyPacking),(fun | 5 => (lookupWord 2 11 1 7 0 3 (fun _ => 0x696a00000002118000c9)) | 6 => (lookupWord 5 20 4 10 2 4 (fun _ => 0xd0b1d2171505800003060000003658d0400620d0b838a4380014080)) | _ => fun _ => none))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom91 : graphValid g91 (boundsBefore known87) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part91_4_0 : block g91 4 0 1 = true :=
  @streamBlock #[0x0,0x0,0x0,0x0,0x0] g91 4 0 1 5 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem level91_4 : block g91 4 0 1 = true := part91_4_0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part91_5_0 : block g91 5 0 1 = true :=
  @streamBlock #[0x0,0x0,0x0,0x0,0x2] g91 5 0 1 5 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part91_5_1 : block g91 5 1 2 = true :=
  @streamBlock #[0x0,0x80,0x0,0x0,0x0,0x0] g91 5 1 2 6 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem level91_5 : block g91 5 0 3 = true := (@block_merge g91 5 0 1 2 part91_5_0 part91_5_1)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part91_6_0 : block g91 6 0 1 = true :=
  @streamBlock #[0x8202080820208101,0x2100840210201,0x860218301,0x220401,0x501] g91 6 0 1 5 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem level91_6 : block g91 6 0 1 = true := part91_6_0

theorem table91 : checkedTables g91 6 := by
  intro k hk
  interval_cases k

  · rfl

  · rfl

  · rfl

  · rfl

  · exact level91_4

  · exact level91_5

  · exact level91_6

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low91 : Lower (vars 91) (graphGoal 91) 7 :=
  lower_forest (g:=g91) (i:=0) (hints:=50397185) (before_sound known87 valid87) geom91 table91 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def known91 : List (Nat × Nat) := (91,7) :: known87

theorem valid91 : Known known91 := knownAdd valid87 low91

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low93 : Lower (vars 93) (graphGoal 93) 5 :=
  lower_discard (g:=blankForest 93 4) (ci:=(4,0,89,0,4)) (hints:=50724866) (before_sound known91 valid91) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def known93 : List (Nat × Nat) := (93,5) :: known91

theorem valid93 : Known known93 := knownAdd valid91 low93

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low94 : Lower (vars 94) (graphGoal 94) 5 := remap_of (old:=94) (rep:=93) (swaps:=[67,16]) (by decide +kernel) low93

def known94 : List (Nat × Nat) := (94,5) :: known93

theorem valid94 : Known known94 := knownAdd valid93 low94

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low109 : Lower (vars 109) (graphGoal 109) 5 := remap_of (old:=109) (rep:=93) (swaps:=[66,84,98,32,48]) (by decide +kernel) low93

def known109 : List (Nat × Nat) := (109,5) :: known94

theorem valid109 : Known known109 := knownAdd valid94 low109

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low118 : Lower (vars 118) (graphGoal 118) 5 := remap_of (old:=118) (rep:=93) (swaps:=[100,82,32,48,16]) (by decide +kernel) low93

def known118 : List (Nat × Nat) := (118,5) :: known109

theorem valid118 : Known known118 := knownAdd valid109 low118

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low167 : Lower (vars 167) (graphGoal 167) 7 := remap_of (old:=167) (rep:=79) (swaps:=[118,83,67,32,16]) (by decide +kernel) low79

def known167 : List (Nat × Nat) := (167,7) :: known118

theorem valid167 : Known known167 := knownAdd valid118 low167

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low173 : Lower (vars 173) (graphGoal 173) 5 := remap_of (old:=173) (rep:=93) (swaps:=[116,100,84,50]) (by decide +kernel) low93

def known173 : List (Nat × Nat) := (173,5) :: known167

theorem valid173 : Known known173 := knownAdd valid167 low173

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low199 : Lower (vars 199) (graphGoal 199) 6 :=
  lower_discard (g:=blankForest 199 5) (ci:=(0,64,7,128,5)) (hints:=1728053249) (before_sound known173 valid173) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def known199 : List (Nat × Nat) := (199,6) :: known173

theorem valid199 : Known known199 := knownAdd valid173 low199

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low203 : Lower (vars 203) (graphGoal 203) 5 := remap_of (old:=203) (rep:=93) (swaps:=[116,84,33]) (by decide +kernel) low93

def known203 : List (Nat × Nat) := (203,5) :: known199

theorem valid203 : Known known203 := knownAdd valid199 low203

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low205 : Lower (vars 205) (graphGoal 205) 5 := remap_of (old:=205) (rep:=93) (swaps:=[116,84]) (by decide +kernel) low93

def known205 : List (Nat × Nat) := (205,5) :: known203

theorem valid205 : Known known205 := knownAdd valid203 low205

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low217 : Lower (vars 217) (graphGoal 217) 5 :=
  lower_discard (g:=blankForest 217 4) (ci:=(16,0,201,0,4)) (hints:=1661337603) (before_sound known205 valid205) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def known217 : List (Nat × Nat) := (217,5) :: known205

theorem valid217 : Known known217 := knownAdd valid205 low217

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low229 : Lower (vars 229) (graphGoal 229) 5 := remap_of (old:=229) (rep:=93) (swaps:=[100,116,83,32]) (by decide +kernel) low93

def known229 : List (Nat × Nat) := (229,5) :: known217

theorem valid229 : Known known229 := knownAdd valid217 low229

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low230 : Lower (vars 230) (graphGoal 230) 5 := remap_of (old:=230) (rep:=93) (swaps:=[100,116,83,32,16]) (by decide +kernel) low93

def known230 : List (Nat × Nat) := (230,5) :: known229

theorem valid230 : Known known230 := knownAdd valid229 low230

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low233 : Lower (vars 233) (graphGoal 233) 5 := remap_of (old:=233) (rep:=93) (swaps:=[99,67,116,48,80,32]) (by decide +kernel) low93

def known233 : List (Nat × Nat) := (233,5) :: known230

theorem valid233 : Known known233 := knownAdd valid230 low233

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low236 : Lower (vars 236) (graphGoal 236) 5 := remap_of (old:=236) (rep:=93) (swaps:=[115,67,80,16]) (by decide +kernel) low93

def known236 : List (Nat × Nat) := (236,5) :: known233

theorem valid236 : Known known236 := knownAdd valid233 low236

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low242 : Lower (vars 242) (graphGoal 242) 5 := remap_of (old:=242) (rep:=93) (swaps:=[99,64,115,80,32,16]) (by decide +kernel) low93

def known242 : List (Nat × Nat) := (242,5) :: known236

theorem valid242 : Known known242 := knownAdd valid236 low242

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low248 : Lower (vars 248) (graphGoal 248) 5 := remap_of (old:=248) (rep:=217) (swaps:=[115,67,80,32,16]) (by decide +kernel) low217

def known248 : List (Nat × Nat) := (248,5) :: known242

theorem valid248 : Known known248 := knownAdd valid242 low248

def g63 : Forest := (63,7,(fun | 0 => (0x97f7cbfdaefff3a24afe4feb6f1f354b7c2f3fffcfd652dd3fc7f85f3bfff4b7cecdde56f7693530acefc5bdf8aaa9b37fbeafb61edd9ed8f178c7f7fdbf322e6f2da9f68334de8a38d317f1ec5c8f9388ac9bdac3baf70e41d034dc03fc0fff,0x6200120233040810511038400020000118d080000048812681089028a00080ac8110004001542400a93041800012a0081080020009180a80009102830011b808014caa6080100a00200840612058028200801282031263064054104d00450451) | 1 => (0x5e987e3bfef95c7f4bcd7abf8fe96fbfdff5ed5e3fe7efc7a3d59d8e9f5c9bc3edd9f39d05cf5a45f237f6368e767a8dd5ebc84be5efefe7ef373bea67f76feea39c7b5c5151a35def9e29ca7763b364bf3fcd055c4d713079203b27fd03f03f,0x801140c400018028248c8001810a1000202350088100500808b2225040000002400072b0000b80201004244010814087012a1500140401208420610830400404000041100140a00c080201888e2171440a714c004c090010192221009520920a) | 2 => (0xf7fbffb1fb8f8fcdb5fbd57fba3ef6f8b2e5e7dbc1797f2ff13bf3ea6aef9dd8b6b655ffdb9dfefe3bcaefd2415f7574a7cf56718af2370df7d9795dbbedf6d954d27d3b2eaf3da3fe35d66c129d7cefe4506b27aa469ac38e3fcc380e03ffc0,0x8800038000060010240022844802a4a8108210734a002900400480100520210040c0004882003840200803ac00c12308c45006a00c05410220c00000104020180920002082815835614240011800429e000212c808090408200cc304a106184) | 3 => (0xe6572245c914603bcf7f6d636c67f3d95fbf9362234b00d00f7bfbf1a6b5f7ff4020fe7af7603beaffc3e3dff4ed8af2f9112186d5bc49f1bc428d0b15fe79d3df218199b3a9d54193f5909ddfa367d7768734da01ba35fc0fc00fc00ffc0000,0x9989edb40c6315c406aac72adb190c84c50468c359a02c9840c22c5059161141344610a6de0258254047020897e55b52ab18801784a45053a668351071e640566e320199532b215591f5958ccf2154717424046884a81cf80f8a8f82cfbacb2c) | 4 => (0xad5bc20e8acdfd7f371e3c9889d1ad7df319fafb3ddfc012da9a0698ce7cc755df1c21482e021dcffb379503b75dc79f7ce6f00ded0f5036fef6377c8d59bf72ece8e2ce56c305dc531aaadf41ef86aaf3071630bfed62fff0000ffff0000000,0x2a6b528b8c26a46cb21216650146e901c10a54428eb06e62444d0243b0b3c21853c0108f4001357af028a00c9582b40f810eae943912ec158d010f50f083a41acc0a26e4e9b0430077c2a7461c686a3b00612f092f4a0efe00c8eff60d34d34) | 5 => (0xbeb188ddb32f24adf7c085e271a6eef3f5347ecb2b2a9f72d2285fe7c54eecec13e776eacf9efcbfb3113e4c37fd3ff0caf5fbe94076080880f8e6e623dc9fbd14ea143fadfa4a7f29a9c047c2c55d9c6e7a34743a7a2bfffffff00000000000,0x45572883dcdb0e42013e6817807f440428421ea0c055644583dc32b8e184810b92e04d4963455838797906c43213a985738099852c1389208c2060402a9ac9e00c6c907c2092407c28a9c843c43559c416ea4250685b2fbf7dff300380e38e38) | _ => (0,0)),[(8,0,55,0,6),(16,0,47,0,6),(32,0,31,0,6),(1,8,54,0,4),(2,16,45,0,4),(4,32,27,0,4)],#[[],[33, 84],[16, 67],[16, 32, 67, 83],[32, 16, 83, 67],[32, 83]],(fun | 4 => (1,3,3,0,0,0,0,(fun _ => 0x46c7259510)) | 5 => (1,2,3,0,0,0,0,(fun _ => 0x9f59510)) | 6 => (3,1,3,0,0,5,0,(fun _ => 0x8730443a82407c907f4437a81fa00)) | 7 => (1,0,3,0,0,0,0,(fun _ => 0x163441bf)) | _ => emptyPacking),(fun | 5 => (lookupWord 1 7 0 6 0 2 (fun _ => 0x180000391c0)) | 6 => (lookupWord 1 6 0 6 0 2 (fun _ => 0x8c0615000)) | 7 => (lookupWord 4 17 4 9 2 3 (fun _ => 0x12e12a36a2c29408000c10000001b55300360e9e017)) | _ => fun _ => none))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom63 : graphValid g63 (boundsBefore known248) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part63_4_0 : block g63 4 0 1 = true :=
  @streamBlock #[0x0,0x0,0x0,0x0,0x0] g63 4 0 1 5 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem level63_4 : block g63 4 0 1 = true := part63_4_0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part63_5_0 : block g63 5 0 1 = true :=
  @streamBlock #[0x0,0x0,0x1,0x0,0x0,0x0] g63 5 0 1 6 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem level63_5 : block g63 5 0 1 = true := part63_5_0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part63_6_0 : block g63 6 0 2 = true :=
  @streamBlock #[0x18108,0x20406,0x4206,0x2,0x0,0x3] g63 6 0 2 6 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part63_6_2 : block g63 6 2 1 = true :=
  @streamBlock #[0x8,0x6,0x0,0x2,0x4,0x1,0x0] g63 6 2 1 7 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem level63_6 : block g63 6 0 3 = true := (@block_merge g63 6 0 2 1 part63_6_0 part63_6_2)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part63_7_0 : block g63 7 0 1 = true :=
  @streamBlock #[0x18086080420204080880220401,0x6021820408080820228501,0x1830608042020208601,0x1020408102,0x810204,0x306] g63 7 0 1 6 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem level63_7 : block g63 7 0 1 = true := part63_7_0

theorem table63 : checkedTables g63 7 := by
  intro k hk
  interval_cases k

  · rfl

  · rfl

  · rfl

  · rfl

  · exact level63_4

  · exact level63_5

  · exact level63_6

  · exact level63_7

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low63 : Lower (vars 63) (graphGoal 63) 8 :=
  lower_forest (g:=g63) (i:=0) (hints:=2162689) (before_sound known248 valid248) geom63 table63 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def known63 : List (Nat × Nat) := (63,8) :: known248

theorem valid63 : Known known63 := knownAdd valid248 low63

def g95 : Forest := (95,8,(fun | 0 => (0xeefeafb187ff3ee3bfd7ff9d37fffd9b7c7fcb8baccb56cf5c7cf67ff9f67f8bf83e6d3eb6db750f072338e31ab9a7df75e03ae6d7af45bc7d2713f9fd7e9ad1fa9bcdd3ce1097acfa3a1a6de38ba03b34dd919f6b06001003d37003ff00ffff,0x1101101a4802c10401000062480022000000200641d09020220100818000c50000c0042110b02408a800304402040008a00201840100050c01bf0a0020070231008480000000950000000821c180000224510006430648124141328029282929) | 1 => (0xdfbdf67feddfb397d7bb1dfef1683964fdd02fbbb9e9ff9feeb79feffe2bf379f6d9f7cb62fa5abfc5dcb7ded9c2fa8ffe9be5811e7727658563bada41d9f1bfc373d6f011de4d4bde05f4ef1f573e86cb458cdac00800600cec9ffd00ff00ff,0x20420300120800680844ca010201180a02a0980124000000540040000d200016010220042142d04240c044a000410000440c0410da2942128040000800009804020200c8000600408a04044c060424008a0400c0000882642484043544454446) | 2 => (0xb1fbd7ba77dfdff8b97c08770bafeef2b9e678175fdebd9cc5b8edfb5f229d5d596bca3375d3ec5719b7278317bc5f31ca69c7a769ee67c9f04e76553843e49d697bfc6de6f0fabbe36f1e8b483c5adcba299d6685b001800f30e00e00ffff00,0x4e04886480212083c203358894584025985904e88022468d8844bc22304c00286c0403d08a040214010f011240a00c710141f00a0054386070001176467805006d515f21f7b04a8861b1138008185ad41008cd2104b111888a30c90a90929290) | 3 => (0x793f2df8ed1bd72ef1fef9a2fe55e35596de99653ed50ab8fccf44afe5fb4de3ebd5e7f795ac1f7cdae270cf6791c6fe4d55be6e8f15d852c9f6d42adfe6af8b39e5307a3ca330fd8458d3c467cd3777f6524f69bec001fff03f000fff000000,0x86c0c305112418d00e01071410a19da46c090631882264580124ad1071002a5120045904494048d005000d0ac9708ad6480ca261301568909200b4264820a8802019288230892ae9a458d3c00805613502006509acc012a0b03e012f16141414) | 4 => (0xed5bdf6ffa6f546f7398efa923ac51bdbba1749d6373f9e87b0212457de67ffefee7feecad77b79e76d9d837d57e8c81209e60792f51afcddb1899b506affcefefd4a3853b9e96c81ded6a329834ef4c5df962a9fbfffe00003ffff000000000,0x12a4249005802890842204f2dc32a4506c4d25e608046017a814ac41c2132000e0410850d0000a0c160c084df11430b40021a0832500208030151d91ae29428b0851c0029999520810e8620208004a5950e16609e7d21c00c03bf1c018181818) | 6 => (0x9feee7ffb1aa7fbc9ca577edddafdb3e0eabf6ef5616affea7412d75c2fded57f79d3bdfbb969578ba6e4db8e75f41fb7e169b587967b95bf3dbdfd722705746acc4a93f66e5a5540be5e7d087e2dde027a6f36677ffffffffc0000000000000,0x601118088a51802171488800204400008120180824989a80008a02060c60018a18a004a3000ab500c821c2b0040940010052550c48820345452a00080054011092061518064084140a0500000362940025009062102de15f0fc00e00e0e0e0e0) | _ => (0,0)),[(4,0,91,0,7),(8,0,87,0,7),(16,0,79,0,7),(0,64,7,24,6),(64,0,31,0,6),(1,0,94,0,5),(2,0,93,0,5)],#[[],[16, 67]],(fun | 5 => (1,3,3,0,0,0,0,(fun _ => 0x4ed7299910)) | 6 => (7,2,3,0,0,5,0,(fun _ => 0x7b347a8a0bf99910bf186009f59410b758c10bb58810de95600fc84600)) | 7 => (5,1,3,0,0,7,0,(fun _ => 0x19753055cba9832e5d4c1aa6075303b8fd11101fd10fe087f802fcabfa00)) | 8 => (1,0,3,0,0,0,0,(fun _ => 0x234417f)) | _ => emptyPacking),(fun | 6 => (fun h => if h=43572872871594923930 then some (0, 0) else none) | 7 => (lookupWord 4 19 0 8 3 1 (fun _ => 0x314654a28d00000000800000836b0900350000)) | 8 => (lookupWord 3 10 3 8 3 1 (fun _ => 0x185c00002a9c694700101)) | _ => fun _ => none))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom95 : graphValid g95 (boundsBefore known63) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part95_5_0 : block g95 5 0 1 = true :=
  @streamBlock #[0x0,0x0,0x0,0x0,0x0,0x0] g95 5 0 1 6 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem level95_5 : block g95 5 0 1 = true := part95_5_0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part95_6_0 : block g95 6 0 5 = true :=
  @streamBlock #[0x0,0x0,0x0,0x0,0x0,0x0] g95 6 0 5 6 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part95_6_5 : block g95 6 5 2 = true :=
  @streamBlock #[0x0,0x0,0x1,0x0,0x0,0x0,0x0] g95 6 5 2 7 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem level95_6 : block g95 6 0 7 = true := (@block_merge g95 6 0 5 2 part95_6_0 part95_6_5)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part95_7_0 : block g95 7 0 2 = true :=
  @streamBlock #[0x81,0x82,0x104,0x206,0x301,0x60c183] g95 7 0 2 6 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part95_7_2 : block g95 7 2 3 = true :=
  @streamBlock #[0x302,0xc00000000200202,0x60204080820408102,0x18102040210204,0x18183060218306,0x1820408022850a,0x4600] g95 7 2 3 7 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem level95_7 : block g95 7 0 5 = true := (@block_merge g95 7 0 2 3 part95_7_0 part95_7_2)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part95_8_0 : block g95 8 0 1 = true :=
  @streamBlock #[0x102830608101020204081,0x40a0c182040408081,0x4081020408102,0x2040810204,0xc18306,0x401] g95 8 0 1 6 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem level95_8 : block g95 8 0 1 = true := part95_8_0

theorem table95 : checkedTables g95 8 := by
  intro k hk
  interval_cases k

  · rfl

  · rfl

  · rfl

  · rfl

  · rfl

  · exact level95_5

  · exact level95_6

  · exact level95_7

  · exact level95_8

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low95 : Lower (vars 95) (graphGoal 95) 9 :=
  lower_forest (g:=g95) (i:=0) (hints:=50397185) (before_sound known63 valid63) geom95 table95 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def known95 : List (Nat × Nat) := (95,9) :: known63

theorem valid95 : Known known95 := knownAdd valid63 low95

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low111 : Lower (vars 111) (graphGoal 111) 8 :=
  lower_discard (g:=blankForest 111 7) (ci:=(32,0,79,0,7)) (hints:=52428801) (before_sound known95 valid95) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def known111 : List (Nat × Nat) := (111,8) :: known95

theorem valid111 : Known known111 := knownAdd valid95 low111

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low119 : Lower (vars 119) (graphGoal 119) 8 := remap_of (old:=119) (rep:=111) (swaps:=[67,16]) (by decide +kernel) low111

def known119 : List (Nat × Nat) := (119,8) :: known111

theorem valid119 : Known known119 := knownAdd valid111 low119

def g125 : Forest := (125,6,(fun | 0 => (0xfa3b7f2dd33b7f0dd4dc2bf1defd5f7dbeb9d0f76d8c5bf1e3a5bd38b7fb5bee7b48f96d7bb1dfe64d435c6f34cdb4affac891be1df37d983bc6cb6f38d5bfc3da222391b1a330bc4bfefa8f7ce66f717b3b88f0519bdb240c01019c380fffff,0x480a605904288d0002ec084001a02a4001643146831240a9c50818e4811290f002ab080168bc6c4010200010088480ac430b21cced124405085004204208188c8222183104136a809a2138c6dc52c126929484000080b240e21888c1c82a4c9) | 2 => (0xb38bdf8fb3acab6fb53fefe175ceb6befbff0f9c5b4fddeef57daf03f65977fab78b33e299f6a1b6a5fbbba4e7e8e2f78d95d9fc7f5496b7f773a92b596fb7fdb7f2f8120427adfade0b3cb5125af74e4f579bdb3a5d6007b00601e7cff9c07f,0x184c0042453160055040120aa08104014400000a84c80b1020044460844486803d0142202110300188180a0424502104190a480210080218a50227111a003050369048106020880244080c000012424c0202879e19056001b116452142395226) | 3 => (0xfe6db357fff33c125cd99db59ef7d3f634def46ffe77ae3d8ced15d96aa7d8f6fdaf86b92ccddeddd8ac64ab3faf52fc6e6bb21f19cfcadaaeecfffe20995d726a0b8ff5e5d2d25e34fd3e0ee0e698edb0dfa227aba78c38c007fe78f00e7f80,0x3a1100a004082229c3412a28b100a450512880831004d3402302526025464430511001172854110a20104c8a9524026421010d420128828ca2400b18908364000201d650e79a4016f4512c02001200441016233723228408c0521670e12c4b14) | 4 => (0x75d9e06f7fcfd9faf344677f061eaf9f43dc616789cab1f312d6fc34abc6e78faf536d4f4f72f2e8a6b2e95c0cd69feaf367d7c5e1b3ed6dc6eb83d2c668d0c4119d49cafb2e68cf81d3cf5c9dab44f0453cc5daee7c9fc0fff8007f000f8000,0xa4d10c315311a42488a139ccb3a030631aa7983a32141344a948036a16444431d98297378c7398e0a1ac034749a08588b2c3170848220a0433419a0160c49040801841c2e29a0049b4538744d12a4c705d3e97902874f540d4781c7f01af8e1c) | 5 => (0xb85caf9a17a5b2fdf72b853f7d338767fb4e3faeaddb0fcea1b8b2c389ed4c1fc5efb9959380a721e48ce2b5da67679f03157eeff7ccda76f2316b61efe7e4da6ed6112a945ce544986065fdf69ab7b69f1d7bab22ae37ff0000007ffff00000,0xc7a3c125aac21558091404e1162a68300817c0955835d0ce55a3221e03b30112c0829d844844c35c764475604282c293a04422dca3517841422508eca0660c82406216cf185d74459842611dfa8895a298395801228a97fe0260985ebdc02c58) | 6 => (0x7ff754fd7fc0f8b73fc9fa7ebebeaae3cec4eefff6f1a9c61e735feefd3dac5bf574de5f76ff92d9bb7667de5f536f4dbc276e9192bb6be3cfcf14b6d74ad7bf0d1dec7d5a79ce032dd1d7faaf09c7dde0e9644dfc6b17ffffffff8000000000,0x4000630ea06600401406841044464288004000008c8800095495a0010808a24a246040484080241148412000204940124420009134d15463401020e60e18000b4944082508618620008050b80c05838100414848c00902b72b85e18006003060) | _ => (0,0)),[(0,16,45,64,5),(0,32,89,4,5),(16,0,109,0,5),(32,0,93,0,5)],#[[]],(fun | 6 => (1,0,2,0,0,0,0,(fun _ => 0x7213f)) | _ => emptyPacking),(fun | _ => fun _ => none))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom125 : graphValid g125 (boundsBefore known119) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part125_6_0 : block g125 6 0 1 = true :=
  @streamBlock #[0x4,0x8,0x2,0x6,0x0,0x0] g125 6 0 1 6 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem level125_6 : block g125 6 0 1 = true := part125_6_0

theorem table125 : checkedTables g125 6 := by
  intro k hk
  interval_cases k

  · rfl

  · rfl

  · rfl

  · rfl

  · rfl

  · rfl

  · exact level125_6

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low125 : Lower (vars 125) (graphGoal 125) 7 :=
  lower_forest (g:=g125) (i:=0) (hints:=52822018) (before_sound known119 valid119) geom125 table125 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def known125 : List (Nat × Nat) := (125,7) :: known119

theorem valid125 : Known known125 := knownAdd valid119 low125

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low126 : Lower (vars 126) (graphGoal 126) 7 := remap_of (old:=126) (rep:=125) (swaps:=[67,16]) (by decide +kernel) low125

def known126 : List (Nat × Nat) := (126,7) :: known125

theorem valid126 : Known known126 := knownAdd valid125 low126

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low175 : Lower (vars 175) (graphGoal 175) 8 := remap_of (old:=175) (rep:=111) (swaps:=[118,83,32]) (by decide +kernel) low111

def known175 : List (Nat × Nat) := (175,8) :: known126

theorem valid175 : Known known175 := knownAdd valid126 low175

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low183 : Lower (vars 183) (graphGoal 183) 8 := remap_of (old:=183) (rep:=111) (swaps:=[118,83,67,32,16]) (by decide +kernel) low111

def known183 : List (Nat × Nat) := (183,8) :: known175

theorem valid183 : Known known183 := knownAdd valid175 low183

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low187 : Lower (vars 187) (graphGoal 187) 6 :=
  lower_discard (g:=blankForest 187 5) (ci:=(0,32,27,128,5)) (hints:=1349582849) (before_sound known183 valid183) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def known187 : List (Nat × Nat) := (187,6) :: known183

theorem valid187 : Known known187 := knownAdd valid183 low187

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low207 : Lower (vars 207) (graphGoal 207) 8 :=
  lower_discard (g:=blankForest 207 7) (ci:=(128,0,79,0,7)) (hints:=1660944385) (before_sound known187 valid187) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def known207 : List (Nat × Nat) := (207,8) :: known187

theorem valid207 : Known known207 := knownAdd valid187 low207

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low219 : Lower (vars 219) (graphGoal 219) 8 :=
  lower_discard (g:=blankForest 219 7) (ci:=(128,0,91,0,7)) (hints:=1661009921) (before_sound known207 valid207) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def known219 : List (Nat × Nat) := (219,8) :: known207

theorem valid219 : Known known219 := knownAdd valid207 low219

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low231 : Lower (vars 231) (graphGoal 231) 8 := remap_of (old:=231) (rep:=207) (swaps:=[118,83,67,32,16]) (by decide +kernel) low207

def known231 : List (Nat × Nat) := (231,8) :: known219

theorem valid231 : Known known231 := knownAdd valid219 low231

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low235 : Lower (vars 235) (graphGoal 235) 7 := remap_of (old:=235) (rep:=125) (swaps:=[99,67,116,48,16,81,32]) (by decide +kernel) low125

def known235 : List (Nat × Nat) := (235,7) :: known231

theorem valid235 : Known known235 := knownAdd valid231 low235

def g237 : Forest := (237,7,(fun | 0 => (0x9eb5aaadf1b913f9dd36b33cf6319db7ebe1bbf7f8ccee7aaa9d56bb6de7dae3c3e816c41a3368bf3a1de8c5532bef3f14ad5a5a7bda0ed7df7febbbc76fa9de9c9d4ce1d9fac96e86e22787617b192b5fb54eff550460c00603f21019c07fff,0xa11015100e6660c206c80808980ee02048b4440101a8120600829909920020327110388440602c44640814029421b40012a94682884948085440422082f3a00098210ce510d88d04426a37004022880b14240d22500020d406a0b21608d818b1) | 2 => (0xb9f92f76c6e3faa4fe4b3e7bcff56de1edb3613594fecf74bd7fbf597bc605fb4fd121d9ad07e9e511a9ddfa7e9fafb2cb2aedadb8d6afc6ddf0fcd90d7bb8c8e39ff826e9536381967dc1ba8f1a733734734a2f9b3f4b00480263e01e7fc07f,0x4202c281301005180812820444200208210999084a150191451440020c11dcc58243433218925200880180c4401a0920455029403202228400820c5d5d080160610ae000890322921400c88a8b1830302050a248895c4b22491240e91224e44a) | 3 => (0xfff7d3dcde6f0d4fa576edec33f6b1fc1edd951ffbde077fdabc1f9cae917eba75f7302f7e9495df2f5a4a59fbb2dc57f6fd227a733a6bbd2dcdd8264e0e7f63bf33570913ad92bf60b14f4fb3f1917d389f3cc4ee32cc0070039c7fe7807f80,0x882822a18095309901a60546c10d0220008310020120888d442050652a130580048522b89440880b4449d8404c08138100a13c5280001100208d1421000d0206d27108030000931881084ea0d9019000db20cc0e124c20f10b042867226344) | 5 => (0xe9f35a7bf5fde7cee7a5637748f2af4f7f7d6390af341bf5b5fed56e977ad77fea7d7e1fabeeff7c57c3d9237e546c89c9ae6f0cbbecf6680394855db2fa53b7df6617fed64ebced5328e03e1cf56a9ce663e920b53b30007ffc1f8007ff8000,0x150d241008830001400114e8bb187d3000060661a100482a00210a0932802030053020888201817436902a0a0681448880a10007058040732701c30022f3548000301e565604042c422802204461080642215d2030a33004922c1f0245cb0a14) | 6 => (0xb2ff67f6bbdefd91fbf9dedb9fdef7ccd84affdbc7ff20486fd57b1ace3c66cd76efd9e6772baf46ff763e5cf7ea91eaa372f8b7752d2d056c861ee76bd1ecfb6422f7572bcf7fb06d77b951efa78452610c54b01ae4bfff80001ffff8000000,0x6520900900210044046210280012701803a470003004d95200208ba7104060284d90105002030f5470903020b78204005292008120423460be461008c025303110280606044b5d2465341531490088026124540210a0314700301bd3980c0c18) | 7 => (0xedaddcfb2ff551da70fbb7cebc5ffb2b31ef7bf023e7bdaf736a70bfb82eaf7edcefdf79eafa5b26faaee487857fc0bfb493d3b19e1df1bc3212bf85baebe617c2eaa6fa3fb10dd22f47f000dadc2ea8d3dea39575d3bfffffffe00000000000,0x2520324e048af383914420040a40000c448801e04780204accc504080231084824b4e016004508a08474455004cab420c00e000d21c010c401804e504080002a981202029a000d208c1e0c8129c02a81042a0950d48ceb86dc3e00c00303060) | _ => (0,0)),[(1,0,236,0,5),(4,0,233,0,5),(8,0,229,0,5),(32,0,205,0,5),(64,0,173,0,5),(128,0,109,0,5),(5,0,232,0,4),(9,0,228,0,4),(36,0,201,0,4),(72,0,165,0,4),(160,0,77,0,4),(192,0,45,0,4)],#[[],[50, 101],[32, 83, 118],[32, 80, 48, 115, 99],[48, 32, 98, 82, 117],[48, 98, 117],[80, 115],[80, 114, 50, 96],[96, 50, 114, 80],[96, 114],[112, 82, 99],[112, 98, 83]],(fun | 6 => (3,1,4,0,0,5,0,(fun _ => 0xc10068a07f543fa61fa00)) | 7 => (1,0,4,0,0,0,0,(fun _ => 0x5d4c3b2a190833f)) | _ => emptyPacking),(fun | 7 => (lookupWord 5 22 3 10 2 4 (fun _ => 0xa1e4000000012100029000006812e800a579354682668aacc28b705084)) | _ => fun _ => none))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom237 : graphValid g237 (boundsBefore known235) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part237_6_0 : block g237 6 0 1 = true :=
  @streamBlock #[0x0,0x0,0x0,0x0,0x0,0x2] g237 6 0 1 6 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part237_6_1 : block g237 6 1 2 = true :=
  @streamBlock #[0x0,0x2,0x0,0x0,0x0,0x0,0x0] g237 6 1 2 7 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem level237_6 : block g237 6 0 3 = true := (@block_merge g237 6 0 1 2 part237_6_0 part237_6_1)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part237_7_0 : block g237 7 0 1 = true :=
  @streamBlock #[0x20808202088021c08101,0x8402109040210201,0x218a060218301,0xb080220401,0x3028501,0x601] g237 7 0 1 6 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem level237_7 : block g237 7 0 1 = true := part237_7_0

theorem table237 : checkedTables g237 7 := by
  intro k hk
  interval_cases k

  · rfl

  · rfl

  · rfl

  · rfl

  · rfl

  · rfl

  · exact level237_6

  · exact level237_7

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low237 : Lower (vars 237) (graphGoal 237) 8 :=
  lower_forest (g:=g237) (i:=0) (hints:=1394606082) (before_sound known235 valid235) geom237 table237 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def known237 : List (Nat × Nat) := (237,8) :: known235

theorem valid237 : Known known237 := knownAdd valid235 low237

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low238 : Lower (vars 238) (graphGoal 238) 7 := remap_of (old:=238) (rep:=125) (swaps:=[112,83,98,64,16]) (by decide +kernel) low125

def known238 : List (Nat × Nat) := (238,7) :: known237

theorem valid238 : Known known238 := knownAdd valid237 low238

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low243 : Lower (vars 243) (graphGoal 243) 7 := remap_of (old:=243) (rep:=125) (swaps:=[32,48,115,33,97,64]) (by decide +kernel) low125

def known243 : List (Nat × Nat) := (243,7) :: known238

theorem valid243 : Known known243 := knownAdd valid238 low243

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low245 : Lower (vars 245) (graphGoal 245) 7 := remap_of (old:=245) (rep:=125) (swaps:=[48,80,115,98,64]) (by decide +kernel) low125

def known245 : List (Nat × Nat) := (245,7) :: known243

theorem valid245 : Known known245 := knownAdd valid243 low245

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low246 : Lower (vars 246) (graphGoal 246) 8 := remap_of (old:=246) (rep:=237) (swaps:=[67,16]) (by decide +kernel) low237

def known246 : List (Nat × Nat) := (246,8) :: known245

theorem valid246 : Known known246 := knownAdd valid245 low246

def g249 : Forest := (249,6,(fun | 0 => (0xf5ea39b9adc4df1ec6fe7d5f765a9af8f9efdfae30806f4256f32ef4c0de1f38d7fdfcde03cbea77a3188cefd02f49fd6c9fdadb670ca4effd7414b79f575b8b550f6d8f01e75f4adced8cb6b51438e475d23dc7cb15d498030c07b230101fff,0x2ee70000aa0908618091ab048710010b4e0600019f74b018293beb2a21940b4811dc2814883809000d16d9807378485f72e680d543842705600880b02255098451e74d0f19e2080ec56c8492b0048915d1c235804a03449a930d52b236564ab5) | 3 => (0x27fbf9fcafec2e08ebdda97ef7f4db7f3abedcc5d9cf3dce37935ff38a9f931dddb5f7177cd3adfefee0ee89af975bfdbc8f2a7eee2ee5f4da94fba15ed74449dd0abbe3c1ccff739c19c45359e58acf65b1783fc9dcf9200c3007c3c01fffff,0x11086e2f14108080102250a8280824a031a167342000064340440010080a9483c0208422050210b272c120418083838008114620145a00701aa51843002222118a08a2c08204b60018100149436100ca2830003781fcb1242c322540c888b54a) | 4 => (0xc57ae1227641d46a7f2073df161b60cf454e747effaa1b99ef1d64ef6bb595dca6266cbf92a774a1f7ff90f079acd90ae999d707f9afb710bc2fd41ca76db59babd7fe091651089e3f63b6c4dc5157785859a8bd473439c00fc0067c7fe01980,0x82862ce50af2a81792b09d3608402ee714f14a206247dd6e12a6c31818835c898673450430260689a62c3861092d64b6201076a6fe82a16b90a08a380f70309a6b9e2a081253029e121580c14c4153745b75a815d0bd19c63fc336545cecd9ec) | 5 => (0xd37768f2c855f4b7bb1fb9b92bbff7eafe93964565b77321f85ae45e6df74bffcea309b035398f427fc57e5dc84a765c93f5f2be35bb4fa36d5729fda7e83e94ef85044ca93e8ae6bde04b596dfe3e3948eecbaf7c938e000ffff87f80001e00,0x6c8592cc05de0d502832800e520a8016124e620ab2a404c9682418624231207c2689952c611583d01418e84a80603019ec82c2c0a4880730be5301c460a48080c681445649083a6a5da24b4105154a31080aaa2c7c87ce00b554787f82c2de1c) | 6 => (0xad5ffeff537acff2deb767ffbc8ee1affd72e9ffef6ff8ffa7efd76f5b09feefffee3fdbdeff59999dfe217efff9f39a63421ff9cec3fc182bbbe65f63b7e5e22ef0df7856b9a93b73f6b2f6f6bbc9c3b24b86780aeafffff000007fffffe000,0x40608010a10400486040000152214000020000099110000028082c62c72000002000189940918000081000922200104800c08058000040040158058020054c00046050344080092061e2201430968001000810482a024608c000402b23130010) | 7 => (0xfad5ae5fe55733d5695ebf3d2b37edd7d3f7433d66f8f6257fefbaed7cfbe92b72fe8a65e71e2eca71b57f369b74b58f9275fed471fddb6f37fa3dd2beb97bfe912d0afca9f680b442b47deb6b4a37fe8ebec7c57f2327ffffffff8000000000,0x21a49231a200002148420108cc011802d11048404425b1295d2801520025903412440008200282d038504040d9a8b84121139050823a00a4020200a8e52235e011a280800368414001c142a4a0835cc96a44091016021f70aab87800c0c0060) | _ => (0,0)),[(0,1,240,8,5),(0,32,89,128,5),(1,0,248,0,5),(16,0,233,0,5),(32,0,217,0,5),(8,1,240,0,4),(128,32,89,0,4)],#[[]],(fun | 6 => (1,0,3,0,0,0,0,(fun _ => 0xd63441ff)) | _ => emptyPacking),(fun | _ => fun _ => none))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom249 : graphValid g249 (boundsBefore known246) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part249_6_0 : block g249 6 0 1 = true :=
  @streamBlock #[0x106,0xc,0x708,0x504,0x0,0x0] g249 6 0 1 6 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem level249_6 : block g249 6 0 1 = true := part249_6_0

theorem table249 : checkedTables g249 6 := by
  intro k hk
  interval_cases k

  · rfl

  · rfl

  · rfl

  · rfl

  · rfl

  · rfl

  · exact level249_6

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low249 : Lower (vars 249) (graphGoal 249) 7 :=
  lower_forest (g:=g249) (i:=0) (hints:=1400242179) (before_sound known246 valid246) geom249 table249 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def known249 : List (Nat × Nat) := (249,7) :: known246

theorem valid249 : Known known249 := knownAdd valid246 low249

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low250 : Lower (vars 250) (graphGoal 250) 7 := remap_of (old:=250) (rep:=249) (swaps:=[67,16]) (by decide +kernel) low249

def known250 : List (Nat × Nat) := (250,7) :: known249

theorem valid250 : Known known250 := knownAdd valid249 low250

def g127 : Forest := (127,10,(fun | 0 => (0xee91fe7ed1d6e477d1234d86cf4322a3c79d1b02cd5716cd2f2b27032234aff7be5e05a3b0d8541c2358e8ccddd4d021c6b9b85808d09766bb88becb4a2fdd9a207d4820af424de1f418565d191b9844c18002003c3907401a6e003ff803ffff,0xa20073008006844001008c40004900a0020c88020d218844065a00200042ac033648052180c8010003ca8004c11104200210a8520040046028948000483e9488204c4820044008f2a40816190011184441a2028814190152082690048a412291) | 1 => (0xbbf52e02019db4fceff67739eb90dc932a72c7e98e7c8f7019e5fb174225dd34455132cfafbad9fa078495e8b51e2b9438df260c95006c99b4239a31f08061b2c6678c93f93ed0ec6122c2feb8272188c2000c00ccc1e4801d93ffd007fc01ff,0x10808c020001010c263202a0010240440050134c900c0001c980460c58014130410122c42d12d018800407603402011010c7020010201019900004202480613204218010a1a2900c422400669ca6218882410d04484064a1108109584426110a) | 2 => (0x5caa31f6b0ebca53fac22f5b1744d38426db6ecdbbbbff57d53b808eedebb49cd8afe24a2e682a254c36697540aa630d8a24d3b54e654f048e0e612538b712cd7bbeb4f10bcf34ac869bc9824370800f2c003000f30e38ffe61c00e007fffe00,0x802004469480812c0c021044000051854a340012290070030240002818800c40826400200200a214c10600000806205802040044a0081000202200510010204c10234c5080c040108d1c180620080012c10b042a1020808661844a221188c44) | 3 => (0x8186a8337f49e5b122af09e4eeffab65c9f17c7fcd9721afb3326de6d81c5b5f2a3c8e54b7357a767c797e0bb246d5b9cd402382b0b498e708aa46dfa34cfa4405c0f2ad743a9b097806af213696c1f030003fff03f03f0007e000fff8000000,0x19c08066254040b920d130844790c24148a1544460860481b1a0d3c2110000ac08140a407a305a1454017c0906460308c94602a092b5b886002b465d82406a540480814d301e8501183729002080c0903005941703e03e0547c02cf170b0582c) | 4 => (0xdbd466cf8f025a7aa7b5fa26bc11b479782f9dda66da327ccef4593a94215449cdd45d2e427b878faed710beebb32bce3afa0dc1fb4b20d8417b204b070ebc6eeb92090e3011899311f19772a20cfe003fffc00003ffc00007ffff0000000000,0xaa043044217046918088f81ebc2180117020441102136248041211c282a8344098540c0a52a805877e93509b81800ae60a084180035120c00309200f1b461444fa900105101109d31151961122004a003486c01a03bf8006477e3601a0d06834) | 5 => (0x647f99a7a4ac7d8d3380fe953c7ec35f3cf4453676a073f7f0d3cc4a87faca3166b7caf805e67dc5a102154783b515f8fc8c717c717d5dfe5c2591146a768e5558956562a383a994a621297a56ee7fffc000000003fffffff800000000000000,0xe251c68a028267810e00183328a70ac628500542452c507dcddb8d1d0660cb3147d1869805c065d4a10b904783751daa2fcdb968303b5c5e0ca590302af689701c1dc32223b220903620186214ef7ffec067019c02fdf7f79801b80dc6e371b8) | 6 => (0x2712cb59ae484bd4c5db9f4030ad2a6a7fc526ba4ec6d0c61c8d5eedfdc5acb849ab8bb1c10746e1de6d37562b11345721210ec7768a446bd950f8b8e773e64f2d085b1c5ee81232e9c43ce4c5cb7ffffffffffffc0000000000000000000000,0x4190b998a0d00420102074100082908800a01a80c4090060a050c2d0804421243aaa02080078060816c03442811341120210c0764024430f81018a06410800b01090a004aa03020e40800600d2b356fcb782be0fc0000380001c00e070381c0) | _ => (0,0)),[(32,0,95,0,9),(0,32,91,4,8),(8,0,119,0,8),(16,0,111,0,8),(64,0,63,0,8),(0,64,39,24,7),(1,0,126,0,7),(2,0,125,0,7),(4,0,91,0,7),(4,32,91,0,7),(0,8,54,65,6),(0,16,45,66,6),(8,64,39,16,6),(16,64,39,8,6),(72,0,55,0,6),(80,0,47,0,6),(1,8,54,64,5),(2,16,45,64,5),(9,0,118,0,5),(18,0,109,0,5),(24,0,39,0,5),(24,64,39,0,5),(88,0,39,0,5)],#[[],[16, 67]],(fun | 4 => (5,6,5,0,0,5,0,(fun _ => 0x28f51414586c0a86487154540816b7443122ba28690406dba218925d5434420a6dc944ba906b02210592e9756488150110)) | 5 => (12,5,5,0,0,6,0,(fun _ => 0xdf2b688de6543ca140c592a1921c5515030b596650815d120c3565993205744831d193640815d120c7864990205744830b4862457450d2086d6a4841c56148294ca35d8825d510c1b218925d54344294ca25d48358110a592897520540443165756488150110)) | 6 => (51,4,5,0,0,9,0,(fun _ => 0x100800000000000000019210000000000c48400000000000000000003461080400000011e18b401b006c01a5d1a833c9bcca5b2891c7a331487c29f8f7793b5d0e36f365a8c660af16eb256aa1469e4ca511e8a42a00f67634168aa5025918822a0e038013f191201325028fb2c38aa0a055764c7154140ab6c90e2a828117d95205744c2ae922ba2a29846f251869dd208fac8d10ba2411f49160d744821fb2c40ae89047764c815d120c7acb102ba2419b594205744833ab2640ae890679648815d120cf8c8102ba2418bc865d143482b6922ba2869056d6507158520cda420e2b0a415d5931c56148237930ba2829046f650874c5208f64bb0690a4155c935d9754432dcee412ea8865b5d8825d510ab6492eab9a2156c925d5634430f90cbaa868855b2497550d108ee49b0cb922156c925d5604432baea41ac08854f2517654110aae49aeca822156c925d5404432eaea40a80884f564c81501109f2c9102a0221768925d5404427e13098a808855b249754c1108fc4bb08902217e19348520442adb2b442e40846f251861c600ab2c90e2a8a8186e6620975442a9924bac66884da2498544200)) | 7 => (177,3,5,0,0,12,0,(fun | 0 => 0x8c68767266565864b63e63962c61f60a5fd5f05eb5e65d95d45bf5ba5ad5a059355e52950c4df4d24cd4c84bb49e49946445f45a42d3f03bb39637936433f31a2fd2e02bb29e28126424722a2151e81db1ce1b91ac19f19218517816b15e15114413712a11d1000e30d60d10cc0c70ba0b50a80a309e09909408f08207506806305e05905404f04a0450009fd811c1629fd849dd329fd819dd329fc815d1329fd841c5329fd801c5329fd841c1329fd811c1329fd821c560b7c81581509fd839dd409fd829dd409fc874c940bf8804c9409fd831c5409fd821c5409fc874c540d7e7754140d7c71541409fc815d1309fc8750930dbd74509309fd841c5309fd821c530d7e7754530d7d74545309fd87505309fc8750530f5d514c5309fd869dd209fd849dd209fd839dd209fd819dd209fc819dd20bdc835d9209fc815d920bf4815d1209fe885d1209fd835d120df4815d1209fc815d1209fc815cd20afc8650d20dbd7450d20afd861c520bbd841c520bdd831c5209fd861c5209fd841c5209fd831c5209fc8758520bbc8458520df471585209fc8750520dbd74505209fc874c520bec8748520bed8348520bdc83581209fd869dd109fd839dd109fd829dd10bdc835d910d7e775d510d7d765d510d7d755cd10d7d7558d10afc8650d10d7d7550d109fe885c9109fd865c9109fd835c9109fc87589109fc874c910d7d7558110bdc8358110d7e7754110d7d7654110d7d7454110d7d7550110bf48150110f795050110f797550110ff13150110d7d754c110bf98448110fe93248110ff13148110fe921481109fe885c8109fd865c810dee885c810ded865c810ddd7358810ded72588109fc8758a009fc8750a009fd861c6009fd841c6009fd821c6009fc8758600bbc84586009fc87506009fc8748600df471486009fc8784600adc8650d328fd861c1329bd841c1329f5811c132aec8650e22ece668ce22f8e448ce22dcc738896097d851c560e3e6691150a7c8650d50e5e668cd50f1e448cd50b3c8458550b5c8358150abc8650d408fd861c54097d851c5409dd831c5409ed821c540d74715454097d851c5309dc874c5309dc835d9209f4815d1208fd861c5209bd841c5209dd831c5209ec87485209dc835d910b6c825d510c7e665d510d5d758cd10fe121481108fe885d810c7e665d4109de885cc10cde665cc10cdd768cc10d5d758cc10d9d748cc109ee885c810cee665c810dce335c810ced7688810dcd738881097d851c60097c8754600bd88358200e7a6654200f3a4454200f5a3354200b798544200eba6691200af88650e00eda668ce00f9a448ce00eea6688a00faa4488a00fca3388a00b79851c600bb88458600b788754600e7a6654600f3a4454600f5a3354600f715184600ef26684600fd23384600fe2228460096c825d510 | 1 => 0x1921064842b2440c908324985c0125c1103802215229510101a49f80620104361d08c28352116a91038020560cb0404e10001921c90e4f00b2494593c02c909b700b80392110c910864d1701288393c02c9e0164f0080c61012872780400004324513c02890e4f00b803c01e0082802000044428e8880a90f007803524a2a9080140100000a30d18440200081488402521a90f0041c01e00d2700b803c010038020a4e0103803521e008864b251c170195443249b0b80d924dc0310c926c2e02f00400e00b4b0b00c02192c9474582600324958f8b04a5b930c4bc6c582711106483a2e030893e1f011a5858064fc021127c3e0208d493e191a5858064e8dc03c92562e0264d1f00f249f807924fc03c927e0193a3700d8b80453c9c7c5405a00b004a7805c01a00f007803c01600f007803c01e00f007802d2c2c032921a01f00400030041c01000000300780340100000000052d18f8dc9c7c5408ad0acbabeaa9aa4a97a92a7da70a5ba56a49a34a1fa1a9fd9f09eb9ce9c19b499f99a98d98897b96e96995c95795294d94093391e9098f48e78d28c58b88a387e87185c84783282d82081b80e7f97f47ef7ea7d57c07b379e79178477777276576075b75673172c71f7127056f06e36de6d96cc6c76c26bd6b86ab69e6916 | _ => 0)) | 8 => (148,2,5,0,0,13,0,(fun | 0 => 0x4e4478b01a4e01105927263c0693804416094580b253c6c98f160389c02d31e364c78b01d6acd2971e2c07c0153931e242520b34e4c780d802a7263c580aa7008829c98f1203115a8f0114e01690e192a4c78b02126011059a4386c98d1604a2c0222414870d931e2c0953805803803802a70088270d931e2c07529e364c78909f0070070070070070070070070070070070070070070054e016009121a52438580e57008ae0149918072646018dd3182c4c68b0224c1803930600e4c1803531e364c7890a041121a43864b8f16049120a4386c98f12140a22434870d931e0411201c364c78b021486403c01c01c0152a300d4a1403c018dfc6b23411948c7c60e2c514f89e446e2110e785fc2b213307f836414a07101e7febf8dfbcfd97e33e79f16f717abbd2de7ef2c78cbbe1dbcec47553a41cece5c724b815b90dbc6c335e9a88d0e668b315972cad63830e9808bb95be2cfd604af655caab54fca7251e27fd3929854bca50d26e90847e231912e86f41ca00cfa87c13c91dfcea073d38a9b7cd986963301950c585fd2f89724b6c5872b3154ca2c50325f92b08d045522490f486241e1f40ec874c39a1c70e086ec36a1af0d4868c33a1970c8862c30a17f0bac5be2a914b0a0c4d224f10907e03bc1c40c3850c1f00bb03f01900b004c0200098018000ff8e2997fd32503fe98a81ff50930ffa82987fd404c3ff3ba41ff5d920ffae8907fd64483feb9a41ff58d20ffa86907fd71483fe38a41ff58520ffa82907fd31483feb0241ff50120ffa60907fe77443febb221ff5cd10ffac6887fd43443feb9221ff58910ffa64887fd60443fea0221ff4c110ffa40887fd62043feb2401ff58a00ffa85007fd61803fea0c01ff48600ffc23005fc7058aff3ba65bf99932bfae8997be444cbeea1a657f1c532bf8e0997ed6388bf6a1c45fb88960bf8e2b077d64543beb1aa1df50d50efac2a877d60542ff3ba81bf99940f7a86a07de33503dea1281fb88940bf8e2a077d51503bea82817f9dd30dfccc985fd744c3df22261f74c930fdc44985fc714c3bea8a61f74c530efaa0985fe77482febb241bf99920bfae8907be44482feb9a41f78cd20fda64905fc71483f690a417f9dd10bfaec886fe66443bebaa217f5cd10fbc66885fd72443f711221df54110ff280887f920442febb021bf99810bfae6087de33042feb9021fb88810dfccd007be44803ef19c01fb88a00bf8e30077d51803fcb0401fe50200ff261007f920803fc88401fe59200ff2c7007f943803fcb1401fe50a00ff265007f871803fcb0c01fe50600ff263007f921803fd08c013f1d943dbccd19f9e448cf7733445f38ce22bb8e6b067e665439f222a1d78cd50afaea884fd76042beba821775cc10bdae408779508037d33401ee91200fb467007ea22803bca8c01fc84600 | 1 => 0x24e0110c02201c010420c9911b0124e0149c025f252e0249c025d252e023521251602c9c0293805252e01c9c02212700e4a4c03928f00c849458091e3601800b9289a91208d1154e01294b806414e01a40a309044253804a6325c045e9700d2a4c038c8f00d2a4c038c8f00d4c6c038d804346494c16263c58124260a93931c2c08c012c4260a939301f00480c1527223c0799253e4c70b01c84c929b26385811803803802346270b131e2c085eb24c64b8a09d72d93192e38276a416ac931b22345054b56498c971e28285ab24864b8f1404119a2f4e4878b0230048901ab05e4458118024468b539301b0048cd4f921e2c0723354a7c90f1214109aa7243c480e4884c15a7263858138025884c15a72603e009018294e4c06c0125313e4c70b01e6294f931a1310182b26029221314e4c680f26446c98f1603ac92971e2c0693804b6 | _ => 0)) | 9 => (16,1,5,0,0,10,0,(fun _ => 0x40e3691448c2812aa88a0698553206140c34c2481448e2812818512449185024d3291851238a04a269748d207140948c2a91a48c28124903491c501e91c69238a03a285238d24714094291a48e280ead224714063299230a03124491c501891a48e204d48d2471406c26bca064682dd0655664dcfc334a41ec520a400ff58ffd43ff58bfd32ff583fd40ff4c3fd20ff443fc10ff802fe66f78cfee22df543fa00)) | 10 => (1,0,5,0,0,0,0,(fun _ => 0x920c402ff)) | _ => emptyPacking),(fun | 5 => (lookupWord 3 15 1 8 3 1 (fun _ => 0x506600115980120000547580388044d)) | 6 => (lookupWord 8 37 5 9 4 1 (fun _ => 0x40269acc6040008e856b80001ca007d40000007ec0099718000061ea6880000d22c800d195dc392380962000001)) | 7 => (lookupWord 32 121 5 11 6 1 (fun _ => 0xdcc363a66f00000000315a2700000288316adbb03579d021361c27132ac1c4f461c4f1788904326bba10eccc0e430b5ac8a9c6916c092a4c7be0008bef2001080ca095000192160001afebb47acd5ce60e74000253e90000005c21ac00081cb4ec7f3000bd472c6080058f449781ca9e22b4cfe21000c1a0680000000000028e4633c005513a4000a9800dcaf18000007554128166c000877cd61e001b6fc50004dfc16318622b2672606e08c41004060b4082040100444083c0)) | 8 => (lookupWord 107 401 6 13 8 1 (fun _ => 0x5ac28bc0132900000001316e9a0001ab8280000719000180c000206c000000186d88b4c4a61000211c00148e0c0800284341aeccbaad618000947b5430f4000d251622b6093ccbd0001a2000062cc8ec104460000624b09a1130007678ca8b4140c0dd1d171589bcd1be0be000b1b569d67e27e139c902f3174d8d4e90f0e00000000003e300000004a2842eb04000000000105af54800106a000f3f8000001d2d0000001c8bd8d000000145c00000008000013aacb3020592957ef07ec6fb27dab74424c454c0a0d0fc88e2dc80a13619ae42823222108e1a9dd07a31ce1f69ee77e95c2b7a16000d99000263366a02200003442337429419ab20000000001d387170007568001c4f7a4f625a5841dd460001492208629000087a231e16de9000134a0ad81eeaa6f1eb4d7a60001184c4690e732000061d101cb286a1000066af5f289ba430178ba00060964dbc32e51801200fe6b7a8326259354600095638590ae00000055ef54a0008c104df0d2428d544a5428b92909985f204878a000159c6fad97029f0d000101100079da72218368fc1e609de3c832b99eabfe9df9ec02755c58fb14919b50e000f13c0a80017054b0326c71600dc0764c20b8d8522a8c4400017fa104d940585a1e9780015325763135811e5c30a1d74e6ccb6c84a485c8a2c280bd3a19f0f3fa6e953d12053e4aa223000000000000000000fa000f4880000000006280d18c5e000a49ed0c001d62f034eb3ea2a100002454e88f390b1c8af483b7203c10c3f0db800007e4b93da250000c08339b0e58444526120001388001145468f2c70f9aef6a43a6444a31d49643ac8070e574b2bc31b6277d3ed4362bc000000a87e694000969590c4e3275a15a4bee994acda34258870c6f0830b7bd7a03c38c41fdc9803954d918400568020418259108120307d3823000c110001601700400200624000200510220404080d8400040091000c0007ccc1c30002c844204000a240003341302017100100340100006100000180)) | 9 => (lookupWord 89 341 6 13 8 1 (fun _ => 0x3d04000000800b9cd0510191092a0c00000093e800311a000a938002ae8e0dca30183e8067ef92f189cbf01b20480006b93130000000001f1c40e8000001d23121ea1ee3ae5b311fe0525e2906a9a08ae54000d44bddc8f43104a8000061b227c1fd463e0d55f20a8002e2d338000488746c00000038624d1a40f0590deb06121f22911c000708b318d8029a1564a64c3a6d2253000324b6ba84f11c4a2864c0000000001a9217381a7879489d7f39598c451d14fa1d000250a00000075ed038c524970003096d1ecb2e858001c2ae2e1202aaa0000005c6c0000000000003203a002b56d9ae50e756c3f80f85a435682000000014be37000149000000000002a2a06e8280004ce0724a44d2b104922a382da2c40255b993817117a796287e3bb2651f1baf031a85061cc2f099011a69f35615e85ec0eaadd99047a824009f80a918357007a0f086543b83598528bda6d52cf510b11a56b8bc219b1915e4b7340bc724469be3206b17010e0b800129d6662b8a2233246510005e0800167600049ec000b24bc4f46867e80752c012989a0004b10002e1801160d64cc00064138a80004f8e420000634a1ff58594d1bc0001630002e036a4000bad6950001937b1700000000000000829d08000812ccf800004c60f80000000005148000001590cbb524fe32000f1f0001ea989100019b16de630d9009c4e8ba2bcacb12470d8777a1fe12408c4ec9a6e29cb4e741b805b400000052e91fc00162c83c10cd2c836caa3a23c000000f81d99790400002c0ac11410c801100c2013850410025890c000274000f90b48900800e01100c1471850025430011062400c50811c224914fc412c21010cc00b040185043000)) | 10 => (lookupWord 9 34 5 9 4 1 (fun _ => 0x29e004333432040022001a2a65e001d392d1e7f3a9852fc7116767000ea6dda401f50018400018055190a6)) | _ => fun _ => none))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom127 : graphValid g127 (boundsBefore known250) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part127_4_0 : block g127 4 0 5 = true :=
  @streamBlock #[0x0,0x0,0x0,0x0,0x0] g127 4 0 5 5 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem level127_4 : block g127 4 0 5 = true := part127_4_0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part127_5_0 : block g127 5 0 12 = true :=
  @streamBlock #[0x1,0x0,0x0,0x0,0x10204081,0x0] g127 5 0 12 6 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem level127_5 : block g127 5 0 12 = true := part127_5_0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part127_6_0 : block g127 6 0 4 = true :=
  @streamBlock #[0x1,0x4,0x2,0x0,0x4183,0x3] g127 6 0 4 6 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part127_6_4 : block g127 6 4 24 = true :=
  @streamBlock #[0x2,0x10200082,0x102040000200080,0x204000,0x4002,0x0,0x0] g127 6 4 24 7 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part127_6_28 : block g127 6 28 23 = true :=
  @streamBlock #[0x4081,0x204082,0x1,0x82,0x4081,0x81,0x0] g127 6 28 23 7 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem level127_6 : block g127 6 0 51 = true := (@block_merge g127 6 0 28 23 (@block_merge g127 6 0 4 24 part127_6_0 part127_6_4) part127_6_28)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part127_7_0 : block g127 7 0 1 = true :=
  @streamBlock #[0x10202808802180840628501,0x4080c02200860210601,0x1020100840210201,0x408060218301,0x102020401,0x710] g127 7 0 1 6 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part127_7_1 : block g127 7 1 24 = true :=
  @streamBlock #[0x204,0x20404306,0x306,0x0,0x0,0x183060c183,0x0] g127 7 1 24 7 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part127_7_25 : block g127 7 25 24 = true :=
  @streamBlock #[0x228086000000008203060c10081,0x10828081021820002000000c202040c04101,0x1008a0404082041008404101020408101,0x2011404206,0x3041408088,0x820404183060c183,0x60c183060c183] g127 7 25 24 7 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part127_7_49 : block g127 7 49 22 = true :=
  @streamBlock #[0x81018208041020402180000000081000000018305040c3040a020408e181020a1430608180408a,0x810182080808106040408110040810c30302141840c08180820c30506,0x8101820808183060004004042850c0428102040850a1428408,0x103060818204041020a1008206,0x40808182080810102,0x604081040000183,0x0] g127 7 49 22 7 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part127_7_71 : block g127 7 71 24 = true :=
  @streamBlock #[0x102000000404202,0x82,0x200000,0x102,0x2081010008102,0x40800204081020400004,0x810000200,0x0] g127 7 71 24 8 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part127_7_95 : block g127 7 95 24 = true :=
  @streamBlock #[0x208,0x1020000000000000000086,0x1000408100000810004082,0x800102000800008001,0x408100040810410000,0x8202040810004080010004002,0x20008002,0x0] g127 7 95 24 8 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part127_7_119 : block g127 7 119 24 = true :=
  @streamBlock #[0x8000000000000000001820208102040810101,0x400002000820000082,0x408100000000000008,0x8400042000000201,0x80020400002081020408102,0x8081020408082,0x808004100020004001,0x0] g127 7 119 24 8 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part127_7_143 : block g127 7 143 24 = true :=
  @streamBlock #[0x10800001,0x100800004301,0x800000102,0x800202080000000002,0x404181000000080,0x1008104081020808102,0x408100,0x0] g127 7 143 24 8 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part127_7_167 : block g127 7 167 10 = true :=
  @streamBlock #[0x2,0x4,0x0,0x4,0x0,0x81020410202,0x2,0x0] g127 7 167 10 8 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem level127_7 : block g127 7 0 177 = true := (@block_merge g127 7 0 167 10 (@block_merge g127 7 0 143 24 (@block_merge g127 7 0 119 24 (@block_merge g127 7 0 95 24 (@block_merge g127 7 0 71 24 (@block_merge g127 7 0 49 22 (@block_merge g127 7 0 25 24 (@block_merge g127 7 0 1 24 part127_7_0 part127_7_1) part127_7_25) part127_7_49) part127_7_71) part127_7_95) part127_7_119) part127_7_143) part127_7_167)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part127_8_0 : block g127 8 0 21 = true :=
  @streamBlock #[0x40400201080220200040400808005021028000040c0821820501000000a0420502141840000003020228602040408602205010c084061008104200450c102808602043040c182060818202020480a18205060c1880a183050c101008106286081430308143060c060c183183060a182050102040810204081022860814040810204081,0x8080040214044040008404003010a180030604200821c2860114040811810108140850610181011838102021808a18181080c201020c08210023070a180408608183040c103020404090183850c202870e18385041c0470c1c2860102040810204081023070a18180810204301,0x808104041c38404101020e0830204204008210401100238108140850608083060c0830220488020404302101840204081020840810204070108183040c10202143880e203020102040810218306200480102040810204081,0x8102080838806081020408102040c08108020891020101060c083040c08102041818202409020410106081810208183040c1030408080822004081020408102040820408082,0x4041040404082040808206080810204080822808104040840210081020c08406100810604101010404081020408204041010204081,0x208101041c044040410202081840204041081408506100c182060c18310102040208081020c183060c183,0x20203060c2080838088060c183080c1830804201020c183060c203] g127 8 0 21 7 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part127_8_21 : block g127 8 21 24 = true :=
  @streamBlock #[0xa0404000000000000000001404081081008a,0x2800c183808e,0x1183808000000001404702,0x3820000000010028084,0x204086040810204085040c08102,0x602020800000040001404402,0x10108001081404003060c183060c183060c183060c183,0x183060c18c] g127 8 21 24 8 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part127_8_45 : block g127 8 45 24 = true :=
  @streamBlock #[0x300001c3000000000080828700002800000000080000500000000808280000000000000000000280000000000000000010000000000000002840e020460a182850404087010218208081020608205041428081140450102040840204081,0x81020000a000000006040080830001000000000000810000000002020c0200000020000a0000000000040000000001420601020450e18301010c102060408601183040c0828501022808c,0x600000000e0204081000490002000000008000000060e142840014407000000080000440a14280811028508000000208081020408102040810204089061440608241020e,0xc0004001022000100045002004000100000008002040800204001000100009010230501021020408082022404204,0x180008102200811448901000810804002060c182060c183000204201020850108100810c081060c18102,0x18081020408102040810e04081020408102040810204081020408102100408604040811020102,0xc000800c140408000280820040081000800408100800008204002030410044000c20204002040402002040004088,0x181063018c062018c060418a0648181] g127 8 45 24 8 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part127_8_69 : block g127 8 69 24 = true :=
  @streamBlock #[0x189010018301001000402006000c00000000050a00003000010000000000a000000000000000000000000000000000000000000000000000000000000000142870c143040a1004090183870a1c4090e0c1850e081020c18305081840610020450a,0x10004808100000124040800000081020000000000140004600180400102000810220801100460820405011038082102080a020450e14048100c4008602187121c2008c182860a,0xa1820401100009202000811400080000060c182850c142830a1420000000460a141840c183060a142000a14204020408102040860c1404102040860c1c20508,0x2850010200801004200080440102004000020004081020000102040004001020470800180020800004080000000000000040608083880e,0x2800810183120004088020040200080060c0030600183060004002000010118180000000204000000e1018306,0x50a1c3800004081020408101023890000201080000106080810204081010000082103860c14104080818206,0x5020408102040870c1c2060100042060408406041810004081080818408081840610002061c18080200408c,0x2420403060c18a060c4030628188] g127 8 69 24 8 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part127_8_93 : block g127 8 93 14 = true :=
  @streamBlock #[0x20045010020306000000c182800810200000000700182830c1404301182070c142870a,0x2800102040800200306000400c180400a0038701020470a0c2860c0c20404,0x1040400102010c182001000004083050a000000a000050a000008c04081020408108,0x50a2010000081070600306000000200001020408000000010000184060c,0xa240400202048000c040000c180060c180040000102,0x182850a18081020408100003850c180410a00001020418102040000202000800028100,0xa142840e103870804085011420208101020810201021c10183,0x30183100c50a0630306] g127 8 93 14 8 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part127_8_107 : block g127 8 107 24 = true :=
  @streamBlock #[0x6000000000000000000000000000000000000000000000000000000040c183010820081,0x40200000000400000000000000000000000000000860c18201,0x10000000000000002000000018308,0x1000400000000800c18082,0x400000000800210204,0x10204081020408102020408102103040204084100810204081020408102,0x400000000000810204,0x21020400000020200081040810402103060c1820402102040000004140008104081040c180810204081,0x0] g127 8 107 24 9 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part127_8_131 : block g127 8 131 17 = true :=
  @streamBlock #[0xc1008000000000000000000000000000000000000101020608183040818201,0x10000001,0x402000000000000000000000000000000008,0x40200001000000404000000010202,0x808080000000000040010204000,0x410101020408102040810204081020408102,0x40000004004,0x1020408200000040010080000408002040810400000100040a0000081,0x0] g127 8 131 17 9 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem level127_8 : block g127 8 0 148 = true := (@block_merge g127 8 0 131 17 (@block_merge g127 8 0 107 24 (@block_merge g127 8 0 93 14 (@block_merge g127 8 0 69 24 (@block_merge g127 8 0 45 24 (@block_merge g127 8 0 21 24 part127_8_0 part127_8_21) part127_8_45) part127_8_69) part127_8_93) part127_8_107) part127_8_131)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part127_9_0 : block g127 9 0 5 = true :=
  @streamBlock #[0x8082800a002020c0004002180408102084081020082040410118043020418101020408108183040c04081180460a141050402040810204081143008102280810204081,0x8082810a022020c043010c020408104204081004102020808c0c08106040808102040840c18206020408c0228504181008102046010204081,0x8082810a1010202083010c02300821010404040410218083020418102020408c0210304081050a08302010204601,0x10105021410206041810c02040820c182061808101041010208082060c103010204081,0x100810204283020408102040810104081020c0830204181010408082,0x4105021408208042010810204020204081,0x1830608183060c103] g127 9 0 5 7 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part127_9_5 : block g127 9 5 11 = true :=
  @streamBlock #[0x143050e00000000000000002808102000000000000002890a2400000000000000000000000818020400000000000000000000040e1040010200408a14408011428408102040810204081020408040810204081020408102040408e18040811c0450a1c041020408102040810204087062404900020408a144808102183060c183060c183060c183040840210020008114288010210204081020408102040810204020470c02040800228501020460a182860a142850a143050a020408102040810028501023008a2448092182850a140050c1428912024860a142850a000408102040810204500,0xa182870a1c38080002800a02040810204080002800a282808a244808000280103004081020408000040081c208082040081180450a1020408102040810204020408102040810204080811c30081023808c0208102040810204081021c18901241808102300810c183060c183060c1830608108042004201023070102040840810204081020408100811c30081023808c020408c143050e183060c18300940204092020460c020408102040810204601,0x50c000050e1c0008a142850100000810200081140450a000050c180070a140000018280001c306001c28600000040e00304102038081024050810204081020408102040804081020408102040810204081020408102040810204081020408102043830e18483011c0490124040860c183060c183060c182041c0080108380901c40081021020408102040810204081060a182870c183070e180408e18040811c04081,0xa0028700020450a140000a0028080020408a020000400102000810204000000a000000400102000810204000000100002080820804020480e202820408102040810204081020404081020408102040810204081020408102040810400402100c100812038701021020408102040810204081020408102040810204081021008400840204081,0x2800a1c2800e020450a142800a0228001020408a02180060c180060c1830600003000c183000c183060c000080c208080c4008124047060c183060c183060c183060408102040810204081020408102040810204083060c183060c183060c3831202483010204081,0x204081020408102040808a0408102040810204081010208102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102,0x3000e0038701022850a0038010004080102045010020008002040810204002c000001000400102040810200010000408102040810204081020c0802200810204081,0x50c143850e1c0408a0028c0a02280810204500] g127 9 5 11 8 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem level127_9 : block g127 9 0 16 = true := (@block_merge g127 9 0 5 11 part127_9_0 part127_9_5)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part127_10_0 : block g127 10 0 1 = true :=
  @streamBlock #[0x44020208086021008a0204081,0x1100808202180840228081,0x440204080860210501,0x2101020210201,0x860408301,0x408102,0x401] g127 10 0 1 7 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem level127_10 : block g127 10 0 1 = true := part127_10_0

theorem table127 : checkedTables g127 10 := by
  intro k hk
  interval_cases k

  · rfl

  · rfl

  · rfl

  · rfl

  · exact level127_4

  · exact level127_5

  · exact level127_6

  · exact level127_7

  · exact level127_8

  · exact level127_9

  · exact level127_10

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low127 : Lower (vars 127) (graphGoal 127) 11 :=
  lower_forest (g:=g127) (i:=0) (hints:=52494337) (before_sound known250 valid250) geom127 table127 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def known127 : List (Nat × Nat) := (127,11) :: known250

theorem valid127 : Known known127 := knownAdd valid250 low127

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low191 : Lower (vars 191) (graphGoal 191) 9 :=
  lower_discard (g:=blankForest 191 8) (ci:=(8,0,183,0,8)) (hints:=1344339969) (before_sound known127 valid127) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def known191 : List (Nat × Nat) := (191,9) :: known127

theorem valid191 : Known known191 := knownAdd valid127 low191

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low223 : Lower (vars 223) (graphGoal 223) 10 :=
  lower_discard (g:=blankForest 223 9) (ci:=(128,0,95,0,9)) (hints:=1661009921) (before_sound known191 valid191) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def known223 : List (Nat × Nat) := (223,10) :: known191

theorem valid223 : Known known223 := knownAdd valid191 low223

def g239 : Forest := (239,10,(fun | 0 => (0xce13f1fe183f991202191fef7b4f488aec83ebec46da6cba97ba5e8e5d55a7734db8c4817e7a395c16e413ec780e2c46255459353d93b868010935f69b0755c1aa984eb6f8a1f997935a207ac1e2500c0001800f3c89840078e8033ff803ffff,0x1381040114022205100006060c280060000068000041050201048284041343070804803008130012a0820024060461210440150011906001083100000555c080040c0200018897100800620150500c90019201148884a0282941028940a251) | 1 => (0xe44aca3b6e2c7d1db67e6c7090e21bddafeca239df09a26bbf58b5dc20aa0cf88b51dbaa59a1ac290dd706ed1a97e218dfc243681c235e9fa6852d4de776d9344ec9804dc213538f53e4c28db124e23000c60034cf1198019c9003d007fc01ff,0x5448081370681c510844183100b000bc8b8cc61042180e10b910031442e00814d0120922c8214c29451704ed1a80721018c006081c0a498ca680444fc2a288244a50a04cc202110843e55a0d9802a23122c624944b11194494929255229548a6) | 2 => (0xcdfef6ced48c48637dfea73ff458ff10fae6bd7e3df12aa8de529e380aeb385054d9a1a09d38d71a67c3d20859bcfca5ac1a26981b866282b2e92a12858c62a516ec3f30c70c603cd9387e70ecdc4c001080038f01e6001e71ffce007fffe00,0x212030600c02008422012400f8010200003231862184902a04c820600012e0002041a21001928052204031100111000a02018060812022005026808028580001002a43300040460088128580428804c209084128a0026211410424a8442a1508) | 3 => (0xf3737bcb1497afb8a82e89aee53dc466d8159ecc3804515a77526b596eb5cb37d0630d6d5e8942c06ada60dae3c8f3ea24b9ddd2a8d88bcdf84797f3a41120f58539df5836963018fb744ab8748a070001f0003f03e07ffe07e000fff8000000,0x318c7a38842b8081d22909a049000413883397060080121204408868401008040043091d0e954061084a405b8329f0880481994228c80b8878c102a284320019083bd158a092104041568b19648a070303f060be01202b0607c610fc36130984) | 5 => (0x5f1d8d05c3e737ec0dfcf95c441df9235988f53f11ec78b19d963e7fae212c8bbef73935e08d41b0b10e8f748f9241242b2f541fc90b110f0fd9db79456b9a1ef3955d9d617da4ea60e935788a59380001ffffc003ff800007ffff0000000000,0x464c830003c067220408d85a06924523c0094009124260112116569d8184000112061905c22d112011258424b4820124010a469c0249194d02095b7101269b1e83958485223ca02a2045206e88113800325286c003fd806406f8db01a0d06834) | 6 => (0x35b8ad172fd191efc0d53cea4ee9165eb3fcc8897d74f557607395b657dafa7ebd2c55e5e523170e4c85fd83867034b1f137e6ef427493f5f432b085598c2ab4c76236084eaebb832c446e82bf883ffffe00000003fffffff800000000000000,0x421081000000151a00d4545e24411040408448108910840122951081078003203c305020c02a170455858d8404100021e13646a11230406502129005418436e2c50002004e2420a7040020c29b0038543c00070002dfd479f800e001c0e07038) | 7 => (0x8186f1920e8bbac7dbe09298c89c799e5a7f17066920ceafec1d9d1ebd72d2cdf6c32d4ca106d58e394ba41b002d3ed5994fb9164b27023665fe6e8c5ef0aa80b803696e318f4c78d53a7509d337fffffffffffffc0000000000000000000000,0x81824052681b80443b000100592c0a1038200160400118aa844889422870d88cc001264a210040ca2848601101293ec818c131026d022292658424809c4000003822680810c14040d1225501402647abc1ad783ffc0003800007000e070381c0) | _ => (0,0)),[(2,0,237,0,8),(8,0,231,0,8),(32,0,207,0,8),(64,0,175,0,8),(128,0,111,0,8),(0,64,39,136,7),(0,128,15,96,7),(1,0,238,0,7),(4,0,235,0,7),(72,0,167,0,7),(160,0,79,0,7),(0,2,232,5,6),(0,8,166,65,6),(0,32,75,132,6),(8,128,7,96,6),(32,64,7,136,6),(40,0,199,0,6),(64,128,15,32,6),(128,64,39,8,6),(192,0,47,0,6),(1,2,232,4,5),(1,8,166,64,5),(3,0,236,0,5),(4,2,232,1,5),(4,32,75,128,5),(6,0,233,0,5),(9,0,230,0,5),(10,0,229,0,5),(34,0,205,0,5),(36,0,203,0,5),(40,64,7,128,5),(40,128,7,64,5),(96,128,15,0,5),(136,64,39,0,5)],#[[],[32, 83, 118]],(fun | 4 => (1,6,6,0,0,0,0,(fun _ => 0x10782dda12613250120)) | 5 => (2,5,6,0,0,3,0,(fun _ => 0x288796a4821c5404823e1a12613250120)) | 6 => (14,4,6,0,0,8,0,(fun _ => 0xa0400000009282052820002c0ac17a0921de1cdb9a5917d692d18dcc8b4023eb2243a64a04fa648804c5408fa48b0ea12610fd9621d3148279b2641280904f96448250120cf2410e2a02413e8984c940482b5924ba2a88855b6547258910ad6ca0e4b12211bd9421d524423eb2243c45004f8648804c510)) | 7 => (120,3,6,0,0,11,0,(fun _ => 0x1800e0020c00401723e00600000060042a10a50451f0a0a3e0c1000000180160040000180160040c90800c90828010b8528030524200054342080002550c40030820230694122842e10a842a1650400000000013e1410570220a842a1423e07005000000c608400c043048c10c0003002c00d003400808a1a1860e16205861a086821a0860e16185821a0068010b82e85802002e10b923003005c2c1505a1e830038116801300200000c00800000000ad7576ac54aa8b4969051ba2d446864fe9e1366614ab94d2864e4979252123b4718d919e3145488d10619c2e85306e0b4087d0f8deabd0796ef5d7baa74ae81c4b846fedc5b635e6a0d099a326630c2982b005f6bd978aec5ceb8965ab454c9d137a6a4ca98124a4446c85908a0c40e7e4f59dd39e728de1ae340648c21762d0568a613e2604888a0eb1cc3605c0b30de1a8298450800ec1b0310460780c81401e028028009fd801c9519fd821c1519fd841c9319fd801c9319fd841c1319fd821c1319fd811c9609fd811c9509fd839dd409fd819dd409fd831c9409fd811c9409fc874c9409fc874c540bf8804c5409fc825d1309fd841c9309fd811c9309fd87509309fc87509309fc8750530bf5819dd209fe889dd209fd859dd209fd839dd20df5819dd209fd819dd20bf4815d520bf4815cd20df6771c520df5751c520df5731c520df5651c520df5631c520df5431c5209fc87545209fc874c520df47158120df47154120bec8250120df47150120fe93250120ff07150120df4714c120ddd655cc20df5655c420dbd74551109fd861c9109fd851c9109fd841c9109fd831c9109fc8758910dec72589109fc87549109fc87509109fc874c910fe932481109fd861ca009fd851ca009fd841ca009fc8758a009fc8754a009fc8750a009fc8788a009bd841c1518fd861c9318fd861c13197d851c1319bd841c1319ed821c131e766695611ed6668ce11f96448ce119dd831c9608fd861c94097d851c9409dd831c9409f5811c9408fd861c9309dc874c9309f5819dd209f4815d5209f4815cd20d76551c520dd6331c5209f4878452097e885d420c7d76954209de885cc20cde665cc20d5e555cc20cdd768cc20d5d758cc20d9d748cc209f6885c420d76555c420dd6335c420d757584420dd573844209ec825d1108fd861c91097d851c9109bd841c9109dd831c910bf0804c5109f48748510fe12148110bf08148200e7a6695600f3a5591200eda668ce00f9a448ce00dea7788a00f6a5588a00fca3388a00ef26684600f725584600fb24484600fd23384600fe22284600)) | 8 => (142,2,6,0,0,13,0,(fun | 0 => 0x86805400c443e261e160e01d2517130b0700c861154e49c4c3c2c03a087130f0b0500a801184a421a2e221e160e0190c22a289c92100f8987848380b4108a0403e261e160a0210022c17898785830071746c3c2c12c0045d2517130b04d001170b4ac4c342c180440045c542d27130f08f0010bc4c3c2c128ba46261e160c01c5c54502d261d04e2e2816910e51780122050c28414108a8a2403e261e160e0250028814943121050420e1400a1852908492822410838529104861420a085202801400a0050028014a89831a544c08d2a2604693002498016564c443e261e160a024545328201d17130b07014302a2994100f89878580a181514cac90807c4c3c2c15a403a221a120a01d29104928624a42124a08808018c4c5f22ef1628aac50226711e88cc3b219f0c2856c2220f706682cc11204f0127fabf21f66f9e7c8be11eeef6a7aabd21e66f1e784bb71d7eeaa74aba21c86dfe6d4b671aaed4a686b341926c3e618b07181ebba5d6ad61686af6574aab14dea6250aa7813a69864bca51126e8f2466a281126856410a050fae7ca3ce9e40ee673e3989b50d8e68233a98e0c165fe2e496f0aee56a29694809e64b623c913086e42a20e90408063b61d48e7070e37a1b68d806a63461988c7061e3021768b805a62c615c8ab053e29214289e04b623e11088303ee1aa0aa840014606602880f004e0120068003fe99281ff4c540ffa84987fd414c3fea0261ff9dd20ffaea907fd65483feb9a41ff58d20ffa86907fd71483fea8a41ff4c520ffac0907fd50483fea0241ff4c120ffaca107fd65443feaa221ff58d10ffa86887fd62443fea9221ff50910ffa64887fd60443fea8221ff50110ffa60887fd20443feb2c01ff55200ffac5007fd52803fea1401ff88a00bf8e4a8dfc70546ff3ba63bf99931bfae898fbe444c7eeb1a637f1c931fea8298dfc704c7fab2c23fd58e11fea8708dfc72583fb08ac17f1c950fec22a85fe77503bf2aa81ef55140f7a86a07de33502fe39281ef50540fec22a05fe774c37f332617f5d130f7c88985fc724c3ee99261f74c530fec22985fe77482febaa41df95520bfae6907de33483fa38a41fd84520ff280905fd75083bf2a8417f5cc20fbc66105fd71083fb088417f9dd10bfaec886fe66442febaa21df95510bfae8887be44442feb9a21f78cd10bfae4885fc72443fa98a21fd48510ff240886fe66803bf2ac01ef91200fbc67005fc72803fb08c01fe58200ff2a1007f940803fc98401fe48200ff221007f965803fcaa401fe58e00ff287007f872803fcb1401fe54a00ff285007f932803fd11401fe58600ff2a3007f941803fc98c01fe48600cfccd2aede668cfcf22467dd95611fac6708df471482beba841775cc20beae2105fa778037d33401de95600f7489007da33803f511401fc84600 | 1 => 0x54228100a200a043110e2490a9a2880c22a928c8251815501a005150042e2a28804440a4a1890822a8228746451a9a2898129146c22a928c825155012523091422e1150c00526005001148010a40094d144c0948a868454a46441a2a18a1d0850e1910f8948c4c2c18044887c4a3e26160c0206c5c52382e27130f0a01500117140c0b4a89c4c3440045528251b0f0a00f1d129189878500717140b4a89428138a8a4744a3e261e140c02a0029300280088874524034261e160e029003221f12900b8907858380a894010c4786c56261c160e0260823014928b888782718150d0a49c4413a084623e2923130e0b0701230281a15888064008d470644e261e140e0260421895138987806810c744a46261e140e0205430270c8281813 | _ => 0)) | 9 => (17,1,6,0,0,11,0,(fun _ => 0x4c5090c142038506029095142430487080c05182a4060a1312182030165ca12223e5090b101c28201a5ca0e17284c487080805911c2a4870c121c2830164888f9424385880e14180c303c68a921e243050602cd0e1928487890e10180b9524407890e1418093054a4a92203c4870a0c06172c2e5490f121c28201654a4a921e24385060288ca13101c2830103a509890e1018089526243850401e5490f121c2830113163d428790dd9922cb4f289cf198a2703b45807307a003fd65ff58ffd43ff547fd31ff583fd50ff503fd30ff483fc20ff443fe00df957de33fd847fa00)) | 10 => (1,0,6,0,0,0,0,(fun _ => 0xa2440c20403ff)) | _ => emptyPacking),(fun | 5 => (fun h => if h=45135833649769865432 then some (0, 0) else none) | 6 => (lookupWord 1 5 0 6 1 1 (fun _ => 0xb0026f)) | 7 => (lookupWord 8 37 4 9 4 1 (fun _ => 0x862ac7806717d14aa8080000000448021543490000159668ea7000bb800011382101c20000000cef503d10021)) | 8 => (lookupWord 73 276 6 12 7 1 (fun _ => 0x53b5840685a09c4e586795bb91674dfa4d4854f452ee7c7c002f67620f61cc4c57d7238091c72c41d9b6b13a243d0512676835990c8b9de4df2d0c4271cdc81c339bc09332caf7c5d2389493c43fe09ced68d8c3ef599fd68211974000588001b6c000002560000000f700013d618233400000000220dd9800000224984c0030a1daa0e00005526aab51d643b9b40003bdde4f556d0ab4b8d7c5c0000000b8a3c000000063b04001fcc7cb0b0000128e7c0ab3db0bc00282c0000000036c291870e2606572ceb080003224eb5313b40030d3ec88163bf867a04c70f3e424d6e10317b86cc180015340000000000031bd0ca8e40036ee300f14001081b9ee196f8002aa46847a9e80b7e8300f80036b972412507400112eeaf2b090f078447dadc87a5eaa0fb3652ddb0f18f73c00000000000014b6a40000000002c9aad4e1fc200000029cd9d402bb180035a5b58a96f8c9d29b0001afd2dc0ff67061400222b90662ca6a848000001c8e15c4062b4194a6c000e4480f49c000002090002adbe9800000203a630292ef398e17e946810c011400cfc5aaeb0a50dad5a34413030000dd2440442cc10d44b410a445017c700408b0500906d10c10472807813c44801c008000220108a002081500089141144080004)) | 9 => (lookupWord 87 327 7 13 8 1 (fun _ => 0x2af887eaf01e5c6106eee6000c2b08138cf549899694fc8fe1722d95a4220579aaadd2f02020c00010eb279f47ab90000e220008820dda0bb46b5048000c22a618840001aa4000332800000000000065f8001f3d4bc000000000059360a52042360005db600587ca3480000000003368001ecaf50e225cec000000f418003464000409ac8ec4597c000785483800000058d550cb1772900026dd41840eb54ec9e3587c4917347f800324800010092debae4baab2970d2188b2ac100b140f1be05a28a88dadb1e0a00033071dae51e5402f2c84446c4de1ef516cbe2774ae7478a86685f92fcf8a3e03453524684af967e3a41f4c4ea7bf420e11a133127129a34ec92204b5bdfe86e81673d403f834a42a0379b3849185e0564ae4814680000000695b48a2531338b21664c3b55062c7340007538896000000447521dc7ea8a485000094f6315190248000420900400036af98098c4f0a2652c0000001a3e000740c00127528051c147702f9287544000000386587c0012390000000000000e0938e2a38e30f01d9fccb41710007558862f19d158df4d17c82ab14cdcc0bb153a62d3608a6790003607c1c2510ba00000005360389ddc0000000006d78001f200b78001a53c87b06cde808c6489040000ac29187c50000001938f85ed6800000000041b889da726445488e63135e1524a9a67742d1e481ef0042e293fc4c0000190000000ce6144a14099bd1200039f9233c6618280101c0841c98381310950014082801c30081009400000940860e18100267c1830868180021c6020008301042c0150474020100c027120008400001000228200001000000281970c00380)) | 10 => (lookupWord 10 40 4 10 5 1 (fun _ => 0x7ac0060400032e80012d415620034759400cb0001a62ae370a002060014020b0b0930302760910cf5400043b23dbc00a20001410069010)) | _ => fun _ => none))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom239 : graphValid g239 (boundsBefore known223) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part239_4_0 : block g239 4 0 1 = true :=
  @streamBlock #[0x0,0x0,0x0,0x0,0x0] g239 4 0 1 5 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem level239_4 : block g239 4 0 1 = true := part239_4_0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part239_5_0 : block g239 5 0 2 = true :=
  @streamBlock #[0x0,0x0,0x0,0x0,0x1,0x0] g239 5 0 2 6 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem level239_5 : block g239 5 0 2 = true := part239_5_0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part239_6_0 : block g239 6 0 1 = true :=
  @streamBlock #[0x302,0x4,0x0,0x0,0x8,0x0] g239 6 0 1 6 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part239_6_1 : block g239 6 1 13 = true :=
  @streamBlock #[0x208101,0x0,0x0,0x0,0x2,0x4082,0x0] g239 6 1 13 7 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem level239_6 : block g239 6 0 14 = true := (@block_merge g239 6 0 1 13 part239_6_0 part239_6_1)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part239_7_0 : block g239 7 0 24 = true :=
  @streamBlock #[0x10187040230102,0x604282020c10304,0x4060804088,0x1018201,0x20302,0x10000020408183,0x2] g239 7 0 24 7 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part239_7_24 : block g239 7 24 24 = true :=
  @streamBlock #[0x81,0x4,0x2,0x408106,0x8104,0x408102,0x306041030408182] g239 7 24 24 7 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part239_7_48 : block g239 7 48 8 = true :=
  @streamBlock #[0x3040208301,0x8108,0x504,0x8202,0x0,0x0,0x0] g239 7 48 8 7 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part239_7_56 : block g239 7 56 24 = true :=
  @streamBlock #[0x400002,0x404082,0x4100,0x10400002,0x2041000000100,0x80000000104,0x20208000,0x0] g239 7 56 24 8 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part239_7_80 : block g239 7 80 24 = true :=
  @streamBlock #[0x6,0x1000410000001020000001,0x402000020000002,0x400000,0x100,0x20000000,0x40820408000,0x0] g239 7 80 24 8 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part239_7_104 : block g239 7 104 16 = true :=
  @streamBlock #[0x40408086,0x20808204081000000002,0x2,0x408000,0x410000,0x4,0x4,0x0] g239 7 104 16 8 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem level239_7 : block g239 7 0 120 = true := (@block_merge g239 7 0 104 16 (@block_merge g239 7 0 80 24 (@block_merge g239 7 0 56 24 (@block_merge g239 7 0 48 8 (@block_merge g239 7 0 24 24 part239_7_0 part239_7_24) part239_7_48) part239_7_56) part239_7_80) part239_7_104)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part239_8_0 : block g239 8 0 16 = true :=
  @streamBlock #[0x21428502040860a140808c142810a1020402023050a04203060c0808c14281060810202023050a042820c140810318285021828602042810c18285020204081020460a14080810204081,0x42880c02081020430601244060a140810814049101820402041840124406060c081040c0470c1810202040820e040860e0204081020408118040810204081,0x10a18482020438602080470c281020810082101c307040818302080470c281020408082041c301040204084020470c02100840204081,0x4289120c08104081031228388060c102040c04a142c18304081030608102060818201080408102182010210081,0x10a24484020418306100480102204060c184080c183080c10301020408102200810804081,0x4289121408108102050a102040a040810204040810228183060c083,0x21448903060c183060808102040810204081] g239 8 0 16 7 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part239_8_16 : block g239 8 16 24 = true :=
  @streamBlock #[0x800200000000000c,0x80004000000000010,0x100000000012,0x24100000010000,0x2180000010000,0x2200000800000,0x200503060c181060c1830608183060c183060c183,0x8702] g239 8 16 24 8 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part239_8_40 : block g239 8 40 24 = true :=
  @streamBlock #[0x418404040800000000020400000000040210101000000000000820200000000004000000000002000000000000182030c084020a1c2820118201010208102,0x1830a000400000000010800000010c0000000000000008100000000000001000000000004000102000021c10000000080c0408802202870e0c50102023870c0230102,0x101010e102070a00000060038000101010c143080e00000800220000023060810403020c38604,0x180060020384081c00501000400010002000810102080010400280161018201020421018082040c58204,0x1830b101c20400142808100183060c1020004103000c040810c04606,0x6002040708003840a020008000004081018008081840000302010204408,0x306122038008182850104081010400106040850a1428006141840a04181020008082,0x1808b022008188062018e062818a1808102] g239 8 40 24 8 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part239_8_64 : block g239 8 64 24 = true :=
  @streamBlock #[0x181060c100041c0000600000000c00004000000000000000000000000000000000000000000000000000006080c10308023870c0220502,0x180410110280802430086000450e020400014381020408102040808102180020000081000030a0c2850e1404102,0x890814004120200008180000000000001c007010000000000040802382040000004103060c,0xc18080880004404001008a0004080002800408000040810000180050602180000000402,0x6020c003061048001022808100000060c003060c1000610043020820000104840a,0x1808810182070100280880020304101040410200061800606100420a,0xc180060e2028801143008108081060400504042810a0c28302142040008081010400081,0x10706086020a0c603180808a0238081] g239 8 64 24 8 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part239_8_88 : block g239 8 88 16 = true :=
  @streamBlock #[0x10040508022800a100000a003070a002840e18004011c3060c0438601,0x202040800204040840008100000870204080001400000144860c1c38102,0x6000000092142000100000000200000143080018000000004000102010c,0x40870c18080020008910040808000102000008104080000828300000810206,0x2860e1c500010c0481202040080c182000c103060c005000828308,0x1021830102141800c1c50402040460004083020c204080000400,0x2860c20407081c4051402046020420408080840214285020408102,0x28503062818a183810e] g239 8 88 16 8 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part239_8_104 : block g239 8 104 24 = true :=
  @streamBlock #[0x4102,0x408102040808102040800000000000000000000001008204,0x200000000000000000000000084,0x20000000040004102,0x1000000180010208102,0x30000000000408202,0x20000000080010102,0x4081020408104080810204081020408106081020204081020c1030a04040810208102040820a0204081,0x0] g239 8 104 24 9 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part239_8_128 : block g239 8 128 14 = true :=
  @streamBlock #[0x1008000000000000000000000000000000018088,0x100000810000002040408102040820408104,0x82000000000000000000000000020206,0x40000000083000000102,0x4080000000000,0x18004,0x4,0x2080840400002001008008100810204100001000a0400081,0x0] g239 8 128 14 9 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem level239_8 : block g239 8 0 142 = true := (@block_merge g239 8 0 128 14 (@block_merge g239 8 0 104 24 (@block_merge g239 8 0 88 16 (@block_merge g239 8 0 64 24 (@block_merge g239 8 0 40 24 (@block_merge g239 8 0 16 24 part239_8_0 part239_8_16) part239_8_40) part239_8_64) part239_8_88) part239_8_104) part239_8_128)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part239_9_0 : block g239 9 0 4 = true :=
  @streamBlock #[0x101010c10101022040081142850202300810c2040218040810818302020408102042020204081040808202040820204081,0x101010c04081012040081040850a02300810408408180408104083060204081040820404080810204081,0x101010c101010420400811428204023060e0c202041804081081820402042040204081,0x101010c0810106183871008183061830081081830608183061804081,0x101010c0c101081c300810c204080c204080230081,0x101010c101010a142850a0204081,0x101010c0204081] g239 9 0 4 7 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part239_9_4 : block g239 9 4 13 = true :=
  @streamBlock #[0x183080c20000000000000000000c180408100000000000000003061218500000000000000000000000000050a12020400000000000000000000000014287142400b1028046011858801182850a142850a142850a142850a142070c1030b00283808c0230b0e023040810204081020408102040810209100c480922800081180461202040860c183060c183060c183060c1831008107042840080023008c20040840810204081020408102040810204020408102040810200601180470102300922860a0e1c3060c003060e1830081020810102040811800601020410204081020408102040810204080922860a0e1c3060c1830001020408102040810230080,0x30610000060c244808c003060c18040000204081020400c02081020000102040810200080000200102040000204081020400100000400a14381021458814025011228301020408102040810204081081c300022c20a0e02501121830102040810204081020408102044880604089140c04094044808104081020408102040810204402040400a1002100940448701020410204081020408102040810204040810408081020408e04480810408102040810204081020408102040810204081020408101020410202040810204101,0x183080c20306122400012180060c020408102040800004600183090c2c306162c000141800a1424040810204080000408014287142428b102804701023060a142850a142850a142850a103860818584141c04701023060810204081020408102040824403120248a06020470102043060c183060c183060c18310081070428400840238094020408102102040810204081020408100812c68b01025808e1c58081020408102040810238081,0xc00006001830900023090c1830000180060c02000810230084000020008102000810204000000c0010000080020408002040810000004000a0010704144080402580941c0470c081020408102040810204081020808104042020704204070e1c30204081020408102040810204201000e08488060804b0128400840810204081020408102040810204081020408102040810210081070428400840204081,0x60c003080c1800901184860c183000c02306000204081180430600183060c003060c1830000183000c1830600183060c1800014283101c28906204891020183060c183060c183060c18306103830818484061c04c01023008c18183060c183060c183060c183060c183060c183060c18312201890124503010204081,0xc180060c0048701184860c003060018300141c04081180400810004080020408102040018000001020008100040810204080038000002860818284101c04081023040810204081020408102040810204081020408102040810204081c3040c2c2008e0204081,0x1c308001840901184860c000070c2400610280408118040001428500142850a142850000000001428500142850a1428500000050a142850a142850a142850a1438b0114608010204081,0x60c203080c1848901184800c184860118300810230080] g239 9 4 13 8 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem level239_9 : block g239 9 0 17 = true := (@block_merge g239 9 0 4 13 part239_9_0 part239_9_4)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part239_10_0 : block g239 10 0 1 = true :=
  @streamBlock #[0x8a022008602100810208081,0x20808202080820208101,0x8a02200860210081,0x2106040210201,0x7060218301,0x220401,0x501] g239 10 0 1 7 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem level239_10 : block g239 10 0 1 = true := part239_10_0

theorem table239 : checkedTables g239 10 := by
  intro k hk
  interval_cases k

  · rfl

  · rfl

  · rfl

  · rfl

  · exact level239_4

  · exact level239_5

  · exact level239_6

  · exact level239_7

  · exact level239_8

  · exact level239_9

  · exact level239_10

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low239 : Lower (vars 239) (graphGoal 239) 11 :=
  lower_forest (g:=g239) (i:=0) (hints:=1394606081) (before_sound known223 valid223) geom239 table239 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def known239 : List (Nat × Nat) := (239,11) :: known223

theorem valid239 : Known known239 := knownAdd valid223 low239

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low247 : Lower (vars 247) (graphGoal 247) 11 := remap_of (old:=247) (rep:=239) (swaps:=[67,16]) (by decide +kernel) low239

def known247 : List (Nat × Nat) := (247,11) :: known239

theorem valid247 : Known known247 := knownAdd valid239 low247

def g251 : Forest := (251,9,(fun | 0 => (0xfd57e77d97b83942309fb46b9678f588a7ce9337c5d97ba3ad8ccc21782736f88352c88c8815fef186028ffcf5d5956373a8bc5996b3e0e43d15c5859a9730e57c268d1926147592e5d850bc6f7483000c03000e7cc26600100339f3801fffff,0xc8110660019020502108204800295ea9045e19b2405bd10201584020402522108282801c8035d6e102830b0c059411a220a412098301a02011854405808100e0cc2401506610170b65d41018071483448c03450614c2269214911851a504a529) | 1 => (0x9d99dde903ef96483f2d4f45fc52963e352565e720fc1e64889eda93ef4c98caac661116ec432196f55e7f94bc09ce59dcda5e694c342cecc74ce58e1de0145f071d82fa2ea2cdb40840f92f45882c0000cc0033cd0c68006003cf3cfff003ff,0x4a421090849112c4e058005ccc280122201400c0224084098a40b02a742584a246405006e002114e4401080b8298459d4484c606836084cc608209a14201005001012aa81c508340220c82600082c2840cc2890c90c4861630a432418b310c6) | 3 => (0x6a25a95f70507903fcf9b43b7e2065d594f21279272fdb41ed8bb64c36d6186f483d1e810c9eee757a1c8c0901f6ac0badb22934de8313877a4b0a8e7b7ed2e0d9bf0c838954ed548a3ca695f871300030f0003c720f90007ffcf1cf001ffc00,0x2404a90510418c8a1a51d5325b04204408000001250020440482a2062582886e68140e801d8a00142414a4011062cc050d5028704c821281886a02087976db00018b08a11944605088222481f86130a170f0a2b8620491452a2ce18e529a5a94) | 4 => (0xe7ca3e2a7667e6211139723ce1ef79783cfbb5257c78a0d743912492872da6c0069ad3f1c5191bea1ae7f656c6d87d1f2d31c3a270b19d894dba3e2f6161ae38164940e66823e1a9fd0325b31dd1c0003f00003f83f01fff8000fe0fffe00000,0x20080822a2b48c4281203cb2010801240c7000238488e0854102842000ac81800098587981811a201281a75642d25006093083029081a78009260e052141ae98168b60402822e189a01324511ba1c0c1bf00c32f025013868c30bc0be34c6318) | 5 => (0x35fc66ba9e4aebd7183a88c0defaae95d3c61f29f03e9e6776abeefc448212c7dacb37ff39b152ecc06a46c4ab5932915cf9d0d991a8e7614f510f6e528904a28f2fd89bde10a8ba58e2c93fc1e00003fffffc003ffe0000000fff000000000,0x61c042cf94a8aead1dc098d0c642184a180523e20a06e8fa010fcce7405928188cb832174e94012ecc46266e4921012b55ce480c9016020416f700e6c56b444e2842fc05bd090281210e049a4c1e000dd5550fc003ffe03701b8fff00f81f07c) | 6 => (0x8abb09976d6147bdcfc6b1b7f89a80cf5a4acdeb5427acdb391745dd0af16e1f5e07e5432070a5256bf91083cb2b31c4cf2f00ba28c4d331b6b32eabf08deb68a355530dee9b3057726dc648070fffffc000000003ffffffffff000000000000,0x29342d04402130040020000a4908409120cb0dc18670800381548990a514410120281062050a50008481000810121e0d007008820044028369000e204080061e814101cc0090002024c020a040e050e00000c0001ab6c3851c300000c018060) | 7 => (0xb0fc1fb3caddeade8a432dd81b5fcb5e4b1fc8c9feaf5deadf6c7b24554e535073a92a2af3ea9bddb12191fd3ac7d3e48274adbf0b4c48939148fc71ad28239223817b4213e83e3a2de28f71ba4ffffffffffffffc0000000000000000000000,0x802c0400084140108035272810050204a152000185900000008011003526134261410808912a48c1112181901286d21402208531490108938800be10281021800789014202e02c580c21916122c1faf02aaaf03ffc0001c00e000000700e0380) | _ => (0,0)),[(0,32,91,128,8),(32,0,219,0,8),(1,0,250,0,7),(2,0,249,0,7),(8,0,243,0,7),(16,0,235,0,7),(128,0,91,0,7),(128,32,91,0,7),(0,1,240,10,6),(0,2,232,17,6),(64,0,187,0,6),(1,2,232,16,5),(3,0,248,0,5),(8,1,240,2,5),(9,0,242,0,5),(16,2,232,1,5),(18,0,233,0,5),(10,1,240,0,4),(11,0,240,0,4),(17,2,232,0,4),(19,0,232,0,4)],#[[],[16, 67]],(fun | 6 => (3,3,5,0,0,5,0,(fun _ => 0x1c01048a09dc835c5528fd861d5329f9801d532)) | 7 => (14,2,5,0,0,8,0,(fun _ => 0x4820045898071420008490b0e028d119e2a3858702000002fecebaa63e0df9e544503c281402ff3baa57f5c552bfcee995fd754cafe3aa65fb54932edcab117ce3388af6392a17d1c530ef4ab007da33803f511401fc84600)) | 8 => (10,1,5,0,0,9,0,(fun _ => 0xa9e69648e286049b3cd2c7143020f3679a38a181069644f34b24614302d334b2279859230a181871644f34b1c3024c2489e69648604cf0c039e18073c300f7384a7c217680228b82e00ff957fd52ff4cbfd50ff4c3fd20ff4437e55fb88bfa00)) | 9 => (1,0,5,0,0,0,0,(fun _ => 0x398a41882047f)) | _ => emptyPacking),(fun | 7 => (lookupWord 2 8 1 7 2 1 (fun _ => 0x2c760003e225202)) | 8 => (lookupWord 8 30 5 9 4 1 (fun _ => 0x1a62a3c969998006fe5b322ec460ca0a89ae73900371dc0038cebdde88000000da40101401)) | 9 => (lookupWord 6 22 4 9 4 1 (fun _ => 0x1b1a18190000000049d8870d16d9100088c986bd40052401e511d030)) | _ => fun _ => none))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom251 : graphValid g251 (boundsBefore known247) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part251_6_0 : block g251 6 0 3 = true :=
  @streamBlock #[0x0,0x0,0x0,0x0,0x2,0x0,0x0] g251 6 0 3 7 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem level251_6 : block g251 6 0 3 = true := part251_6_0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part251_7_0 : block g251 7 0 8 = true :=
  @streamBlock #[0x4081c28306,0x20410,0x101860a,0x1020810102,0x308,0x408,0x0] g251 7 0 8 7 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part251_7_8 : block g251 7 8 6 = true :=
  @streamBlock #[0x82,0x80,0x18000,0x10080,0x102,0x0,0x82,0x0] g251 7 8 6 8 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem level251_7 : block g251 7 0 14 = true := (@block_merge g251 7 0 8 6 part251_7_0 part251_7_8)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part251_8_0 : block g251 8 0 3 = true :=
  @streamBlock #[0x4081,0x4081,0x4081,0x102020404102,0x40808081,0x18306,0x183060c183] g251 8 0 3 7 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part251_8_3 : block g251 8 3 7 = true :=
  @streamBlock #[0x9101c000000000000001830600000000000000204871024387120c18906,0x24048122438012002040810203000200a141040810,0x48000244800e0000900140000a1400300000400e0258096,0x1202000801c38000182800c0020400004008c,0x81020408102080810204081020810204081020404081020408102,0x20008e1c0000000040182448000,0x80e184080c183860a1c3850a,0x81244870e] g251 8 3 7 8 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem level251_8 : block g251 8 0 10 = true := (@block_merge g251 8 0 3 7 part251_8_0 part251_8_3)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part251_9_0 : block g251 9 0 1 = true :=
  @streamBlock #[0x806021810202180860218301,0x202008804080880220401,0x80a02281020228501,0x203008c0408601,0x4082020408102,0x2038081,0x710] g251 9 0 1 7 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem level251_9 : block g251 9 0 1 = true := part251_9_0

theorem table251 : checkedTables g251 9 := by
  intro k hk
  interval_cases k

  · rfl

  · rfl

  · rfl

  · rfl

  · rfl

  · rfl

  · exact level251_6

  · exact level251_7

  · exact level251_8

  · exact level251_9

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low251 : Lower (vars 251) (graphGoal 251) 10 :=
  lower_forest (g:=g251) (i:=0) (hints:=1399914497) (before_sound known247 valid247) geom251 table251 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def known251 : List (Nat × Nat) := (251,10) :: known247

theorem valid251 : Known known251 := knownAdd valid247 low251

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low253 : Lower (vars 253) (graphGoal 253) 9 :=
  lower_discard (g:=blankForest 253 8) (ci:=(16,0,237,0,8)) (hints:=1394999298) (before_sound known251 valid251) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def known253 : List (Nat × Nat) := (253,9) :: known251

theorem valid253 : Known known253 := knownAdd valid251 low253

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low254 : Lower (vars 254) (graphGoal 254) 9 := remap_of (old:=254) (rep:=253) (swaps:=[67,16]) (by decide +kernel) low253

def known254 : List (Nat × Nat) := (254,9) :: known253

theorem valid254 : Known known254 := knownAdd valid253 low254

def g255 : Forest := (255,12,(fun | 0 => (0x404394e119c72391d74f25c4ca6068201a8b0dde0750ad8a33b0e21181681382146e2638cece337b98bac8629a599a0f1dcbbaa32f022495c24849248079ba9170a142018000c00c0026e1e79844c180008003c390740069b8003ffe003fffff,0x2800100111400091c81c0020007068001e8b0d52131020848320c20081080002142804308408010108204042820890022c0aaa0410402400e000490080488a4130a04201a220c00d12026022984441a440a44141901524209a48049292124a49) | 1 => (0x70bc792642f818444482fd4ceb45c0ad092a604d8d1bb00198c8351d3683bf43ea51f18d8a9025328b24b61a60e621de80289f888d2ddff649a5160a47a64782292880460000063000593e99a188c20003000ccc1e4800764fffd001ffc007ff,0x9029200028100000022548ae0181054000400c008090001040301100810a456841f00c0b90640080049e10608400d4802000888d2010c610219209018645820908804614100630a1080a8921888218231824840648c24201855308614c2186) | 2 => (0x836d82cc4730ce5990cb0c9e5124df4781546849044805c266f49fcff07ce999a9344f4120d38a1155d5717944148db34aa0e661c26dc2080fed1cde42f820b580981498000908400061c71e000f2c000c000f30e38fff987000e001fffff800,0x836fc28e441080481040008640041040000480004448054260900dcc3034e198800602012043889055d021290410090102104461428c42200ac404466220003480001498410908420861851400012c420c420a10208210986420a84108a11420) | 3 => (0x178aa7912616bce7365d3f9978c935bc8ec456142823183870036d87305415a816c737e76444562a619f08a4db283228977b098a67894ba78b73c281eeae703cdbfd18e0000e0f80007e07e041f030000ffff03f03f0001f8000fffe00000000,0x111bac9862048c4c26417d99608995ac80401024082618383801298f385555b002c703c37041522a518f08a540a003add175000246890ba70f4102817a267008c05918e0505e0f82857c07c040903050a550b03e03e28a1f0514fa2d4528a514) | 4 => (0x6486e667bf3f25cc6e21c22a43a360cab081b036fe56dd45883d9a4ca645b6d8538e0743046b1f5402a90744d006b76b609f557dc0c76d7b1a544f965c45de3c802c1f00000ff000007ff8007e003ffff000003ffc00001fffff000000000000,0xe102c4c7af12244c6e01c222418a50029088b1207e3644658d0c8a48265c903a138a0751246b135002ab00609212772b509f512700c749390ad46c469e41003580241f00606ff0030677f0004a0034e0d060c03bf8030c1dfe1a0c318630c618) | 5 => (0x5b201c408c886712cb8d8913a4bb374376f1621f5b2950101d6599a15305d60e4ae1aa7798a9cd8aa241f69526ad5c004e74ea0e63533006a61354fd1d841203efede000000fffffff8000007fffc0000000003fffffffe00000000000000000,0x50002550888867026989885000312d004430621f1a2100101c2410214081160678a160169880450a8200945603ad04004c21aa1a21433186a41041991482120322abe00006725294378000007ffec00ce00ce02fdf7c6f6000dc01b83706e0dc) | 6 => (0x84748739b809d36ee9b6927190f22015c42793e8ab954375728a02c209b600308199508e6d1ae045e4580792216c8420aa000af8bdac2a4bd074e30839cbcb6e3c93fffffff00000000000007fffffffffffffc0000000000000000000000000,0x424032000014302819600409070200144350848818101000082002000800000443050048a10a00528101612214c80502a000ad8b10010005020810000880a002c82e00a8780000038000000356fcb0f0a8f0fc00000700000e001c0380700e0) | 7 => (0x9a51c80cf51044f7010062896c9d944ef16c85a256b0ee1583170c7efdca80b508c399bc3d3bb1ad47e5a4353c99700e9d3e6444549e101d630a306501656d4e6746ffffffffffffffffffff8000000000000000000000000000000000000000,0x8a59c808545080f50040420b4c88904ea14891a04412c8cf8311640e994a88f0004a09a8254b00a0004120299812720e101c0405448c00190b0a38660165604cc1041ff5780dad6bc07fffff80000070007000000003800007000e01c0380700) | _ => (0,0)),[(8,0,247,0,11),(16,0,239,0,11),(128,0,127,0,11),(4,0,251,0,10),(32,0,223,0,10),(0,32,91,132,9),(1,0,254,0,9),(2,0,253,0,9),(64,0,191,0,9),(0,64,39,152,8),(0,128,31,96,8),(4,32,91,128,8),(9,0,246,0,8),(18,0,237,0,8),(36,0,219,0,8),(0,1,240,14,7),(0,2,232,21,7),(5,0,250,0,7),(6,0,249,0,7),(8,64,39,144,7),(10,0,245,0,7),(16,64,39,136,7),(17,0,238,0,7),(32,64,7,152,7),(32,128,31,64,7),(64,128,31,32,7),(129,0,126,0,7),(130,0,125,0,7)],#[[],[16, 67]],(fun | 7 => (10,5,5,0,0,6,0,(fun _ => 0x2da2379950f285021eed9942c8510b1437db56a4812016287bb6650b25442c10f76cca9a22664821eed9953444cc88437cb5aa89858910bec36a43242902210df6d4a1648868021beda9424c2c50043bdb4aa99620600)) | 8 => (213,4,5,0,0,11,0,(fun | 0 => 0x95219108ffaa992219108ff68192219108ff68898999108ff2a68899910cfb2189261510cfb99892615108ffaa898595108ff2a68859510adf69486609108ff69a99609108ff2a666609108ff6a29958910adf69498589109df69498589108ffaa89858910cdf69498589108ff6a688589108ff2a68858910abf29a88589108ff2a19058910adf6948648110bde6948648110ff82192148110ff899921481108ff68a9961810abf68a9961810adf2a66661410afbaa99660810afb6959660810afb2999560810ebb65965608108ff6a29958810c7fa658758810cdfa658558810cf7a658358810cfba6582588108ff2859521a008ffaa99221a008ff2859221a008ffaa99121a008ff6959121a008ff6889899a009f768c9199a008ff68498596008ff28498596008ffaa89858a008ff6849858a008ff2849858a00abf6848658a009df6949158a008ffaa996206008ff69596206008ff29995206008ff6a56220600cbf65962206009ef69299586008ffaa898586008ff69498586008ff6889858600abf68886586008ff2a19558600abf2a16258600cbf26162586008ff2a19518600cdf2a195186008ff69898546008ff2989854600afd68486546008ff2a299486008ff69898486008ff2a196486008ff6a48648600cbf65886486008ff69898846008ff29898846008ff69498846008ff6889884600c9f99995201629eb6909099a22bab6909099a22af368e88889608dfaa99520560c9f9999520560cdb6562220560cbb26222585608df69496a21208fd68496a21208f768e99619208df69491619208ef6909899920aaf690989992087faa997205208bfaa996205208bf6a66620520c3f65e6620520c9f9999520520c5f65e5520520c9f65a5520520caf9999420520ccf95594205208f7aa99320520cb79999320520cd795593205208bf2a58658520a7d69c8158520aed6908158520af568c8158520cbb2626648520cdb26255485208f768e99619108fb28995619108dfaa99521910cbb99892615108df6949858910adb6948688910df8a652148110ef8a212148110fb89992148110fd89552148110a5f2959261c10a3faa98799810c9fa66666141087f2a58759410a5faa98795410a9faa98695410a9f6a26695410e1f61e6695410e9799a5560c10cbba666660810cdba665560810e9b99a5560810a7baa98788810abbaa98688810abb6a26688810e3b61e6688810e9b9998588810e5b61e5588810e9b61a5588810eb39998388810ed395583888108f768c9899a00ab768c9899a009de69491582009de69496442009fa28995442009f668c9899a009f668c9199a00bb668c9899a00bb668c9199a009de6949158a00f9a99a5588a009ee69299586009deaa99518600dda6562218600f9c99a5584600fb899a2284600fd89562284600 | 1 => 0x70c2cbe188000000000000f08400f00400019c2033878610000a70801270824e1000a210787c0200000061820f10400000000000004943a4080000000000346100000068c2000dc2370801e2082c8100000019420b184000001250801a308000f17844650f843630800000000019420f0864ba4169020f084000000007803e0081c01f007c01f007c010000007803e00f802a70f803e00f803e00f803e00d803600d802028f0fc23288b786e1214787e11f803e0081c61f007c01d1f885e00f803e00f803e008e5c963f0f80a001694ba4f1d88a00000000000000000000003803e00f803e00b802e00801e0083c0100000079ff35e57c8782ed7d9bb0f5ceafd4ba6f48e87cfb9cf2be4dc8789f0ee13c137b6f1dc7b57686cbd8dae359eaed41a6f46e88d079d738659ca993f25645c818cb16e1fc358570860bc0d806fe5f7be57b6f45dab9971ee15bdb716ced75a9b4967ec8d8cb0f60abed78ad5596b0552a894fe9d52ca4f4668a50fa15416804f29db37e6d4d59a132e634b89672ba5049b92d2463d46c8bd14225c468830f21bc3285b0a20d41580efc1f13dd79ef29e2bc0776ed9d8bac73ce41c5b7d6ded85a9b45680ced9b331658c79883025e8b996c2ca578ab9502925089d938a51450820fd1ec3ce764e59bd34c660c517c2dc580971292483c8768e81c63786c8d419e328628c01762d8588ac14e2884e8981141f0370600a41101f83a05809c0c81401e028028008ffaa991202668ffaa991201658ffaa990a21628ff28590a21628ff6a48120162cdf65481201628ffaa991201628ff28592a21608ffaa991a2160cdf2a195205608ff69699604608ff68a99604608ffaa991219508ff68191219508ffaa898585508ff68496a21208ff69891a21209df69491619208ff6869961920adf69491619208ffaa991219208ff68498999208ff2a688999208ff6a091999209f768c91999209fb68891999209fe6809199920c7f69997205208ffaa99620520cbfaa99620520c7f65e6620520cbf65a6620520cdf9999520520cef9999420520cf76999320520cf799993205208ff6a299585209ef69299585208ff2a68858520abf29a88585208ff6a581585208ff2a581585208ffaa99818520cdfa219518520cfb26266485209df69491581209fb68891581208ffaa996a21108ff69596a21108ff69496a21108ff68896a21108ff29995a21108ff29992a21108ff68a9961910cdf2a19521910cdfa21 | _ => 0)) | 9 => (404,3,5,0,0,14,0,(fun | 0 => 0xa48aa0885fea65204437f51090221efa6648110fbd2aa40887fa485204433fb2cc38219fd9561c10cfec930e084ffa65860427fb2ac3021afe9961810d7ecab0c086bf649860433fb0f33021afd86998109fe4b30a086bf999850436f92cc2821b7e6661410cfec3aca086bf619650436fb0d2a821e7e6695410def33306086f7595830435fcccc1021b7e5560810df6cb304086fb999820437db2ac1021bed65608109fecc2c40867f61d620435fb0cb1021b7d8558810deec1ac4086fb609620433fb0ea9021afd8654810deec1aa4086fb609520437db0d11021eee6688810fb72ac44084ff654868027fb24434013fd9121a009fe4c4cd006bf262668027f930b2c01b7c8695600f3f334ab004ff261628035f90cb1401bec8688a00f7733445007db956228027fb2c40c01afe66206009feca903006df954818027fb2440c01bee22206009fe4c2c3006bf21961802efb2a30c017f990186009fe4c2a3004ff261218037e90290c013fc9884600f7d332c1005fe65560803ef4aab0401ef96258200ff5112c1005fe24560803df2c2b04017f89654200f7d332a1005fe24550802ff32c90401efa6648200fbd2aa41007fa48520802ff32c884017f89644200f7d33221005fe65510803ef4aa884017f99244200ff511221007fc48510803fe422884017f99521a00bfcc910d005fe64486802ff131334017f89199a00f7c4c4cd007be24666802ff130b2c01efa6659600bfc48acb007de21a55803ef4cd2ac017fa9958a00bfc4c2c5007be21962803df4ccb1401f7a5558a00bfc48ac5007be99952803fd10d11401fea6688a00bfccb103007be99881802ff32a40c01f7a5520600bfcc9103007fa88881802ff532b0c017f89858600f7c432c3007be99961802ff32ab0c01f7a5558600f7cb12c3007fa88961802ff32a30c01f7a5518600bfcc90c3007fa88861802ff130a8c017f89654600f7d332a3005fea6521802ff13090c017f99648600bfc4b243007be99921803ef4aa90c01ff08148600bfc4c423005fe25a11803df4cd08c01f7a5584600ff511423007fc58611803fe2a308c01ff12184600ff84c423007fc21a11803fe4cd08c01ff16584600ff8b1423007fc54a1180277b28404cd6bd94202669beca900b179b99a5588a7bb27442c137d952056097e4c2c2b04dfa65851836db0b110c11fd972052097ecb102904df6548148277b2840a413dd93205209f64c242904df654864427d924c2a21fe121481108ff4cb0e084bfa65860425fb31330218fd87998109bf4cb0a0869f999850432fb0f2a821a7d8695410d6f33306086d7955830427dd32c1021aee6660810db72ab040867b61e220435db0d11021b6d8588810de6c1c440879e99a55803dd4cd11401f6a5588a00bbcca8c3007bc99a11803ee4ab08c01fe22284600 | 1 => 0xcb02306ff655811837fb24c08c1bfd5260460dff33102a85ff64061542ff922b02a1bfc8158150bfe48b0c906ff245864837fd11332417fc9199920bfe4b302906ff99881482ffd32b0a417fd9858520dfe4c2c2906ffa2161483dfb0cb0a41bfd8158520bfec82c2905ff660614837fd1030a417fd9018520ff6c3242907fb99921483fdb2090a417fc9158120f7eb0ac0907fb48560482ffb2d442217fd95a2110bfec9510886ff65a884437fb2b44221bfd92a2110dff4410c885ff65486442ffb24432217fc9899910dff444cc885ff259854437f90cc2a21bfe6661510bfe4c2ca886ffa2165442ff92cc1221bfc8660910dfe4b304886ff99982442ffd32b12217fd9858910dfe4c2c4885ff261624437fd10b1221efd8658910bfec82c4886ffa21524437fb0ca9221bfc8654910f7eb12c0887bf58560442ff92ca8221bfc8654110dfe43240887fb48520443ff10c90221ffa6648110ffcb0a40886ff999850437fcccc10217fe9958810dfec32a4085ff24666802ff922b2c017fe9958a00dfe4c2c5005ff245628037f90ca9401bfe6620600dfeb2903006ff588818037faa440c017fe9958600dfe4c2c3005ff65561803dfac4b0c017fd9518600bfec90c3005ff259518037f90ca8c017fe9948600bfecb243005ff259218037f90c90c01bfc86846009fec9101334ff6448099adfb24404cd6fd9120266d7f33100b2cff644805967fb21442c577d9520162d7f33100b16df9548058a7fb22402c57ec9099a22f76484cd117db99a5588a7fb25442c13fd91a21609fe48b0ab06fba2222583ddccd112c1f6e5588960bbeca902b06bf998815827fb2a40ac1b7e55205609fec9102b06fb88881583ddc44b0ac13fc9161460dbe48b0a306df95582183edcab110c13fe99604609fecab02306df955811837dc44c08c13fd91219509fecb102a86bf998815427f930b0aa1afc86581509fe4b510904ff246884827fd32c32413fc91619209fec890c904ff262664835fb0d33241afc9899920d7f444cc906dfa22554836fb0d2aa41b7c8695520f3f334aa904ff658814835fccc40a41b7e55205209fe4c2c2906bf619614837e902b0a413fd9818520bbeca8c2905fb64861482ff32030a41bee8848520f7733242907db955214827fb2d442213fc96a21109fecad10884ff64a884427fd32c32213fd9561910d7ec310c885df654864427fb2a432213fd92219109fe4c4cc886bf61a664435f93133221afe8899910bf64930a884ff259854435fcccc2a213fc9859510dbf444aa886df61a554436f90d2aa21e7e66955109ff4cb04884ff259824435fcccc1221b7e55609109fecc2c4884ff261624435fb0cb1221bee8888910df6c3444886fb21a22443ddccd11221f6e55889109fecc2c0884ff261604435f90cb02217f49158110bf | 2 => 0x84000001c410005c56209b938f89878122e2a4dc5c054b89c82665c3e2e1e04f170f00c5c4c3c27231b938f8b8581713904f8ccbc7c5c3c0917092746e4e3e2e1e0495c4437170f018ad211b8b8780c7623964f8dc986c5c3c0a11cb27c6e4c3e2e1e0488a593e332e1f170f02444b72c9f1b930f89878146823964f8dc987c5c2c0a118b2746e483e2e1e049463e332f1f170f020403f1f1896918f8b878142422a11e57c847c5c3c0a8786e1e0243c37170f0151d1b8b8780a8e8dc3c042b8786e2e1e0343c37170f0151d1b878088e8dc5c3c058c8786e2e1a034643c37170d01a1e1b8b8780b0f0dc5c3c058786e2e1e02a3a370f0111d1b8b8780a568e8dc5c3c064c4746e2e16037170f00f8b87807c5c3c032827e2e1e02f170f00f8b87807c5c3c03ca1f272c937230c88f21ec867204c79f1dac6f7198c5ef166c56714cc4ff122c457100c38f0cec3070b4c25f092c1f7070c14f04ec0e701cbffefe2bf36fb8be2ef7ebdc6f64bd5ef42bcd6f30bc8ef0ebc06ee4bb5eebabab6ea8ba8ee96ba26e74b99ee5ab956e48b8cee16b7c6ddcb71edbab696d90b5eed6eb586d54b4ded1ab3f6ce8b34ecbeb286c8cb1fec62b136c38b06ec0eafe6be4af3ebaaae76b88adaeb4eace6b2cac5eb02abd6ae0aa6ea4ea906a34a87e9d2a636950a50e926a3668cca31e8c2a1b68109ece7a69e6678c9d3e7429bf66e09a2e67e99c662c979e5da9736590952e53e94c64ec927e48a9136448900e3be8e2633c8bbe2aa8a762908a0e27689a625c895e20a87d61d8860e15e84a60ec82be07a811603880ae01e7f45f8c7d5df027b15e907a2de567845dcc75fdd6a7575d50744dcae7285c64715dc4270b5c286fadb8e6e05b746d1db026b55ac86acdaa66a85a9c699da2a6895a20686da0e68059ec675d992653590862ed87660c57ec5e9d76a5c956e05a6d68e592560456dd56a5575550542d4c652e54ac51dd4324ff53b84ded3364bc52b449dd23a47f51c0460d13e44c5124443d0d24255060406d00e3f44fc43efcf823d54f483d0cf3e3c24efc3afceb239b4e6038ace063704db435dcd323434cd8332ccb632a4c94321cc723174c48310cc2e3084c1c305cc022fb4be02f6cbce2f24bbc2edcba22e74b902e0cb762da4b5c2d5cb522d14b382c8cb1e2c64b0c2bfcaf22bb4ae82b4cace2b24ac42abcaaa2a74a982a2ca8629e4a6c297ca5228d4a28284ca0627e49ec277c9da27349b826cc9a6266498425dc97225b4960254c946250493c24dc92a2494920246c916244490423fc8fa22b488020cc8161ee476c1c7c6ea1ad4660184c5c615c451c133c48a10d43e00eec38e0d8433c0c1c2da0ad4288094c21e07c41c4065c1720514110036c0be0284084015c03a0074000bfec8900b16ff2048058affb2440ac1bfd5220560dff4 | 3 => 0xf00f2e27209b930f8b87813c010003dac27231b918f8b878142e1e1390cf8dc9c7c5c3c0b0f2b0967c625a4e3e2e1e05f007803c01892765e3e2e1e03f007231995938f8b878102ec9c03326b89c8c6e463e2e1e05700780256ce4b49c7c5c3c082b886786e3e2e1e0470059034f0dc9c7c5c3c076b888665e3e2e1e047007803178d0b89c7c5c3c08578bc685c4e3e2e1e04c2f0092d17138f8b8780e00fcb68e4c3e2e1e0407e5b3f261f170f0232ca7938b8780d9652cf8dc987c5c3c0911cb28c6e4c3e2e1e04e594947261f170f023803c01e00f007803c01008e593e37261f170f0270f804c987c0351cb29a8a7e4c3e2e1e0514f170f011449f0f8b8780d96504fc9c5c3c074b282765e2e1e03a593a1f170f01b2c9f0f8b8780dc01e00f004403f1f1b938f8b87812201ed1c9c7c5c3c086564e3e2e1e030807b5e3e37231f170f028dca7938f8b8780e52cbc7c5c3c0601432f1f170f01b1f1995938f8b87810d78f8dc8c7c5c3c083728c7c6e4e3e2e1e04f0f00b803c010f25a463e2e1e03880795b463e312d271f170f033802564b49c7c5c3c07e00f0f00a938040100fabe4e2e1e038807d5b463e37251f170f02f803c0129e4e2e1e02d5e3e37251f170f020a68f8b8780bc01e1e0170040029e4e3e2e1e0307c37271f170f01c000700780347c02a3e012815a3f211f170f020e0aa1e1b938f8781072550f0ccbc7c3c0839382a8786e4a2e1e049bc3c37271f170f020a61e19978f8b878106f0f0dc9c7c5c3c0829878665e3e2e1e0414c3c3727170f01ce6a11d1b938f87810508e8dc9c7c5c3c082b6825a4e3e2e1e047004ada21e1b8f8b87810d10f0d4bc7c5c3c085a38ab4746a5e3e1e0494a3a352d271f170f0278034818c688786e4e3e2e144635c3c332f1f170a3803c018786e4e2e1e0348b443c3727170f0221e19978b8780d230f0ccac9c5c3c08294746e4e2e1e03ad1cd5a3a37270f020a51d1b928f8b87810568e8ccbc5c3c074cab4746e4e2e1395a3a3727170f01ce2b91d1a978780f5c8e8d4bc5c3c07ae4c4746a5e2e139723a352d27170f02380346164a3135b2b271f170f01dae1b918f8b8780f0dc9c7c5c3c06372946e4e3e2e1e047004ac96938f8b8780fc01055a37251f170f01ead1b8b8780bc010021b938f8b8780dc016b6564e3e2e1e03f004c9ae1b918f8b87811c0146e4e3e2e1e03237170f010a09f19978f8b87811c012b25a4e3e2e1e039955a37251f170f022ad1b878088dc9c7c5c3c06e00f1700b802c7c02e00c3700a1b8044bc02012f00b8020043700b87805c01070041c01031f0081c01e00f007803c01003803c4125e01001c01e00f00400a3e010000e1e01038020e0083803c01e00f0878b87807c2163e017087802c81e00838024bc0207007803c3c02e00801c01e00f0040007 | 4 => 0x890d36188ca258f8082f4eca3860800dcca268a7851e2059e1b1472e8b89c04910f67194f00aa02ce1680b453e18ca43c3c025129e11a8f089443c21c3e1e0181469c5861114fe01811a0c41ecf0c39186c31c7c3700c3da04cac82100fc7c66328785902c61a80b2b2098c20a8092d20a9426f4b483250d2d2710e8c2003404a43c3c02a30d184146129e015752d20eba9787808d14a229631430496904d14a20f68143068c346150a3e119bd2d20e45a28c6538c2aea5133e3099f18946538c2a30b3e3518da2944d14e2a765e21d3869d944538c246e1132b27170918c2cac8232c6631b463128da29458c1c6e11346309a02d14e2316b88e463e2e1e040bc433937271f170f027803c0185e0145c4e442e271f170f0272c259b930f8b8781097124ccbc5c3c07e00b261 | _ => 0)) | 10 => (122,2,5,0,0,13,0,(fun | 0 => 0x5870148cb4f1b243c587024911169e364c58702480f8f1b263c58702480f52a23c6c98f161c0b511e364c78b0e04288f1b263c58702080f571e325498f161c0b8f19263c58701c80f571e364478b0e052b8f1b223c58702088f571f223c5870254a80e1b263c5870254478d931e2c3810ac3864a931e2c38131e324c78b0e0391561c364478b0e04ab8f1b223c587021406c98f161c07511b263c58701e324c78b0e032b8d911e2c380e9c364c78b0e03a80d931e2c380eac325498f161c0822ac364478b0e04270d931e2c380ea0364c78b0e03a88d931e2c380ead2a4c78b0e03ab8d911e2c380eb92a4478b0e03a70d931e2c380ea13c6c98f161c08509e364c78b0e042b4a931e2c380eae364478b0e03a78d931e2c380e5d444c78b0e03cb51921e2c380e921e2c380a20325c78b0e039a0e1b2634587020386c98f161c070e192e3c58701c6070d931e2c281044386c98b0e03a88d931e2c380f19263c5870195c6c88f161c074f1b263c58701fb87d7fe9a73a794bc5ae046ef76d7b2ed756a9b4a9a10ce66623297900c61e21b0697febd9ddbee496d9b475946c0d5c2abf5522a094c7a4551368213cc9c44d4a62b2d894dc9424351d68ccc5aa24d0f085d41be056fd97ce3d61e36ed7749b93dc32dd56cc356da2ecda64b314981cbca5ca2db1650ae455029394229d44c125312028c444020f0ffe7bb3c29d04e086ce34c19a4c665fd2e39628a9a51727092ac8ea43f2048f4c72c3591918bb456e281125888c3da1b00bd051020e0d104d81b006c000ffc8058bff99952ffd52583ff20560ffd52183ff99950ffd61543ff18550ffd60543ff61920ffe66483ff60520ffd61483ff18520ffd60483ffa2110ffd86443ff21910ffe66443ff61510ffd65443ff60910ffd62443ff54910ffd60443ff54110ffd20443ff99810ffd65043ff58810ffd52043ff99a00ffd65803ff58a00ffd52803ff58600ffc61803ff54600ffd21803ff84600bfc8099bbf20266efe66596ff20165f7e66956ffa2162efe6658bdf95562bfc8058bbf99952fee6688affa2160efe66582ff61560f7e55583bf58960fee22582ff20560efd61582ff61460f7e55182ff60860fee22182ff60460bfc86543bf99950bfc81542ffa2120bfd86482ff21920efe66483df95520bfc81483fb48520bfe88442ff61910bfc86443bf99910bfd85443df95510bfd82443fb88910ff920442ff61810efe66042ff61410f7e55042ff60810fee22042ff21a00efe66803df95600fee22802ff20600ff960803fe54200ff920803fe44200ff886803fe99a00ff965803fe58a00ff952803fe20600ff961803fe18600ff951803fe48600ffa118039f99a55eee6688bdb95622b7d851827f61c10afd86042df61410bdd83042fb60810efa66803de95600fea22803fc84600 | 1 => 0x25894d921e2c38105e7288b121e2c38125d7488c95223c587028b8f129e364c78b0e052e91192a4478b0e049796a2345898f161c0a2f2d4278d16263c58702e5a84f1a2c4c78b0e05171f2d4068b131e2c3816447cb5193161c08a32d446c90f161c09223e5a7c90f161c09a32d4a84f1b243c58702e5a84f1b243c58702488f96a3243c58702480f8f1b263c58702480f51931e2c3810407a88f1b263c5870294478d931e2c38103d5a5498f161c0856a54478c95263c58702c7abc88f161c0756a54478d911e2c3814ba3c64a911e2c38123d4a88e1b263c5870287ab8e192a4c78b0e05111eae386c88f161c0a511e364c78b0e042b531e325498f161c0a56a63c6c88f161c095d1e325488f161c09511b263c58701d5a88c95263c5870255a88d911e2c3810ba325488f161c08509e364c78b0e04284f1b263c5870215a78c95263c58702592b4f1b223c5870253c6c98f161c072e21364c78b0e0417109b263c5870225888b131e2c38102c4c84c16263c587028ba8898f161c072f2c4c8c90f161c092e24464878b0e0417490f161c069626426c90f161c099d16243c58701e5a8c90f161c072e3c4c88d931e2c38145c4888d931e2c38123d58991192a4c78b0e05979119263c587020bab131b223c5870255c88d911e2c3810264278d931e2c38125c4a78d931e2c3812ac4064a931e2c381322324c78b0e03915620364478b0e04ab911b223c5870204270d931e2c38102d4460b131e2c38125e5c5898f161c08169e305898f161c09223e5c6c90f161c0996a5446c90f161c09232d446c90f161c0996a3243c58701d243c | _ => 0)) | 11 => (15,1,5,0,0,10,0,(fun _ => 0x89238a180c59240a247143024b2489038a181070a20714301c92069238a181040d24714301cb1851238a18108963481c50c081c69238a180e38d24714301c69238a180c4491c50c061238a180a5c81c50c061a48e286035252bc44f9b7cc7ab4929ec6393c3a8a414801ff99bfeb2ffd62ffaa5ff583fe307fd50ffa41ff443fe087fe00dfccddf957f7117fa00)) | 12 => (1,0,5,0,0,0,0,(fun _ => 0x8310405ff)) | _ => emptyPacking),(fun | 8 => (lookupWord 6 23 3 9 4 1 (fun _ => 0x1b232f4510a4c15da0295930026047000009200bba8c00004cc018a05)) | 9 => (lookupWord 115 433 6 13 8 1 (fun _ => 0x7e9ec2bd700e454d70df15cd1709d615e000d2a8000001c5d800bf2f11b90f4a3b98bcbeca10006018001daf0000000000000e333cdc000e5853c514afa2f113540d93c144bae01e9d800020ba185308d9ea209a5d5d9f8c987b280000980e6b5658ddda0830a7e4cce3c0913d26550a41a60570000000001221fb2bd7c000542fa542f225e625dea0002540000000555c0003078dcfa9b98e000000120c418a14000000000074de078002c64000154f1a0001c5c8b980028503ad000658976c000add64f0000000ee5173a4dc618a6280000007453de8002c841b252252f7ec008a00006ec89276c0005b1180e000d6770b29a84963270003384e3d000756c00000070c8ae176f99b2c4c967667ac8000695ada503894a6afffa60000003224000b1d94c000035d88b00044ea475c27b30a02279b8b131b0000e9fe1a00020461493a6000000368116a54800016b4d083e667058130c9c0dd181d1e3bc00010fb6d1470d006c2c2ce60e943394f2ac00085804340000004bd00035733aac9b1878001c515d8800078956eaa21b348b4000ae929a875200000078bdf7dc2200000014fc000aac8000e25c7929fb30c000265c53b0c40009bfee292c88e8572a8336d253fe63f3f812aad3f036198a75d5a10e9466cd303e7292b8e24d5364b7916c1cf934a24534c136221c4100015048f856bf82d153e9842b3b7ab334b60000007a47f87295215497842c6b5651fdb6876c13000000000024f000127883a46cfa7511a982b7544178d227ceaef866aed761a846aef19e50024c00299b4af0864baa625d569d432e78002c04000caa89c7d385090096ed682e00049de216ae862600006200ee23f125ad86da0549da30296820e1c420758c18c000955e915d6627234088d4c1bc3900002ab672db313d62b38fa000d24390df80823c23dd7af70000f1b8001924c3cfb30af9b56087d996a881a2a9905b7238001a7bb44000090743004c00081cc016006dcd0800470030023c7000d800151440c06610021810de09410402e0060432990810401070c61c81ce50418a0040ca0061420c200100214058000200000000732a002081043085102045055)) | 10 => (lookupWord 222 848 8 14 9 1 (fun | 0 => 0x1b568c10b8c2417e5e7540b50c45b2a0c901ecf0b42417812675340ca09d26073d0c813107c0008351457b0a92c6b0ec000b5b8a7100006630002f2cc2cc000a10ed4fc61a899e183e51b90e0070000822b979cd20002e8860c704200000000002a460000000000000084d20410000000000000000030ab90b7946591ea6ff3bed540001b50e0d000063d800000000d5154c49585b6344a32e127000074b0000000000000070f669600018643e0b432145a6282c4cd227a2d566c24f81500f8390be268215220000b32494800000003a50a212bf7f450001a3798cc0000003192d07404b32c64280000000000390760d4811345d5650000e3ee21c0006c84000d6391026c95f1c000398b401bc1b00000810002b28000233213e800013780003c392a300021698e28e60b6044000c8c00049a8ca3000388be96dc121cd746bd1b8a6e0d34a66731b58cac044cee20152bd28210412d8000632052589858fc0000000e2ee8141260000c2a17367ca88770000000839bd766cfbb0ab2e0d30b5cdb7de248c1c81abf1d38f4494e3c896ab8cb52861cef10f4bc15eee02efb0001b160000000000058a6a4b4dab588f72000000021e8000c910924000000045f3a1f4068a6bb216337520c0006448000dcc72240003620d11796f54e2b8304f951c647c295592e92e9819b19e39505d8e3e15c42094d8257f6f5000010fba083082ce52f00002a53000033b00000000000000202cc034390188d5e38743027741aca5514000000072d3af12bccd0d000000045854e2000361d0002048d21aa98a3ab0a1000302bd51c000000054a00000001c784bd035b686c47b856d47643f41550d3118bb8bcbdacc7136c334607908ea2e5e3fde314f1e3fbc5ab9540000003627b8e40000000a8d15c88705c9800000030f41416b12f14c000f400515bbf0d7da03070c20340002e20000b879a5ac0138336c53afa2df00000000000012800075eeb7fcb080000003cc3dcaf3110000000000000064d40000002450b504120c23df2ff02278d080c000938265d0001c763a41d5590c138773dc00063fcc7ea914f174ab802738eb707d423a9161f50180000d0b227727db46ed09000040a00000008c001411005403034f0000240b000f1611010003030d030704070201081117001c121d300209041d0901030326001404010b0100021311000000001b1c0c020b02050000030c0500065e0701070715010f020020012d0100040006001001010c021d060000010c3a270c020e032c0106070600060800090a0015070600020023000108030603020a0200000200030600020a020f020006050000030201010e0000001800020b0a00020301150001030203000305000201010a050a000000070214013300000e050000000700010601000609000902051300020501050002 | 1 => 0x8d3cc05a1d400075a33274c2fefe94b41602958000000253c00000000000cb5d29573fd9dd7056310ce3c48c00071c88ae50800002c3569321a400024a40009c0dc68ddd28b70000000b560000b27990369c118744b213a00027840000000113400081b2ce80000052c19660e3941ef25de820400004d7d1fe4aa0003d910127944b9eb0cc49ffcb0f4fe95623161777bfd64fb8b80908636b799c118585e180000000000bcc2e4c000000079904790002c91539c00045b0000c4ec04fc33e4a4859ce873e05e492486933a922b787b0d585b2348ec61710f8441ae8a258dcd1c110000f8f10cd8039975d2ebec88816d57b948000f3c2c2cf610c54595d0ddda24c36b300cf56c3e57e6c0ae4220f0000000214ec8880000001171c29a939183c0003a3327214638596531b388a11cac71180a715c2497522b0a9c4d818030e40d0ca16373337f4fb69958bf1934f8ed9b3ec41cb694be3730f90cba42e2928c84e058000bbd2634211de75003f58fac6c0c200000000000000c3a5f85410167eb2f00ed0001a79000217ab9a115b008c2ca0000377d19ee58489718375749520000000000109ad3aeec5f0644019468c78f2b4000000346dea5c000f624000000348c58e2e5cf99fa29000000000000000000000dbdc720b0eaef813640001abd0610000e9f00034b2e0a400018d546fd1c6254da393460000ef9813952a718f8e1297cf570000000000147b0095164287000029b65193a69b18396727b227f0f3b9da3090003c9c900bc245cf490c7a67681b5d133a90bf5455c90f93f8c7d5089cc07cfd330a2726ca6273bb8be79f318204434893d4cf40a904c38000213195ac0affb1d911425844c4dee678430568f517ee3bcccd751a3f6d901c02240309b6c910dc451e42b993fc1ad59f4f4d0e4199f1f944cd32393a77e55fd151ec69a3624df542f52479 | _ => 0)) | 11 => (lookupWord 66 250 6 12 7 1 (fun _ => 0x9d10639e314c81d5a974a611c44eb52a240f82a26230f2d8d6a5326654bc3a491005a0b00001baf6155d7273e000801fe1160352fd430400099b85e36b245a923f92779b6f8db8fe32d0c000b02000000e3d000939000000000000000000def0007f786d7c5d570be000d1f938a2b51171a0310008670000000000005df00089cf997591a70000006da296597c6a000a0700000047000000085b0000004f38250000000003ce210a98212b0e576e16d41db316f56c25d2240780b47d369f618335eecf541755c6db99f14f586270995f82c3a034a7d5000f2200038e2835ee42f80a40d6d72933c02653b18493900000000000640436693d00003580002c10000d9c9513341c81df19e032f45c3000048e130000005370008426f03d1c71000e4e000000b1eae0eba089000a4f815e5c017034e7996e3218b5000dbc000868ec900049a829220036556173fbbb47650dc2a08000623e85e4db4673c2b8bb2e2ee63a4c1bdab700f328a270edb3bcd83f2a3ff445518940052785c801019f1c008d0406811aa0050051120cc0803030000ce0c018a0003811c00c53460005c534425614500314c040)) | 12 => (lookupWord 7 41 4 9 4 1 (fun _ => 0x2539a000052d900043803340081900000000288000005000dcd00039652000000000665091001587b833b200d031000)) | _ => fun _ => none))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom255 : graphValid g255 (boundsBefore known254) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part255_7_0 : block g255 7 0 10 = true :=
  @streamBlock #[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0] g255 7 0 10 8 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem level255_7 : block g255 7 0 10 = true := part255_7_0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part255_8_0 : block g255 8 0 24 = true :=
  @streamBlock #[0x0,0x0,0x0,0x0,0x0,0x0,0x60c183060c183,0x0] g255 8 0 24 8 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part255_8_24 : block g255 8 24 24 = true :=
  @streamBlock #[0x20108,0x20108,0x81410104,0x20502,0x20504,0x42040a,0x18303,0x183060c183] g255 8 24 24 8 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part255_8_48 : block g255 8 48 24 = true :=
  @streamBlock #[0x18406,0x10204,0x102,0x102,0x60000000,0x0,0x20408183060c183,0x3060c183060c183] g255 8 48 24 8 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part255_8_72 : block g255 8 72 8 = true :=
  @streamBlock #[0x0,0x0,0x0,0x0,0x0,0x0,0x60c183,0xc183] g255 8 72 8 8 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part255_8_80 : block g255 8 80 24 = true :=
  @streamBlock #[0x0,0x100,0x0,0x0,0x8102,0x410000,0x0,0x102,0x0] g255 8 80 24 9 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part255_8_104 : block g255 8 104 24 = true :=
  @streamBlock #[0x0,0x0,0x0,0x0,0x82,0x80820208000,0x408000,0x104,0x0] g255 8 104 24 9 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part255_8_128 : block g255 8 128 24 = true :=
  @streamBlock #[0x1,0x0,0x40000000000,0x0,0x100,0x820400100,0x102,0x0,0x0] g255 8 128 24 9 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part255_8_152 : block g255 8 152 24 = true :=
  @streamBlock #[0x0,0x8000,0x0,0x82,0x4104,0x0,0x0,0x102,0x0] g255 8 152 24 9 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part255_8_176 : block g255 8 176 24 = true :=
  @streamBlock #[0x0,0x408102,0x0,0x82,0x2,0x0,0x0,0x408000,0x0] g255 8 176 24 9 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part255_8_200 : block g255 8 200 13 = true :=
  @streamBlock #[0x0,0x0,0x0,0x81,0x0,0x4002,0x2,0x80,0x0] g255 8 200 13 9 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem level255_8 : block g255 8 0 213 = true := (@block_merge g255 8 0 200 13 (@block_merge g255 8 0 176 24 (@block_merge g255 8 0 152 24 (@block_merge g255 8 0 128 24 (@block_merge g255 8 0 104 24 (@block_merge g255 8 0 80 24 (@block_merge g255 8 0 72 8 (@block_merge g255 8 0 48 24 (@block_merge g255 8 0 24 24 part255_8_0 part255_8_24) part255_8_48) part255_8_72) part255_8_80) part255_8_104) part255_8_128) part255_8_152) part255_8_176) part255_8_200)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part255_9_0 : block g255 9 0 24 = true :=
  @streamBlock #[0xa142840810204080c2040610203081020408101840810040811004082,0x1028508142840a142850a142050a14041020208104,0x20408118040810204102040810208082040410201,0x40810204081020810204081020402100810804081,0x81020408102040204081020408102183061418306,0x20408102180860c180860c043060c0c1830c0c183,0x60c183060c18302183030c041831830301020c183060c183060c183,0x183120c183060c083060c481060c081060c183060408c180c183020c183] g255 9 0 24 8 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part255_9_24 : block g255 9 24 18 = true :=
  @streamBlock #[0x1050e140c912144890314201080410602183060c183060818201060c1830624183060c1830604183060c186060c183060c1810c180c18c20409142430812043048c182850a183060c183810c08482040810210203020a042820a0810204082850a0828102041010204081020810104040810404081020408204041010c104808c060c18306080820420408102040810204080420102183090e183870e1c38603060870e243060c183060912244891230702183060c183060c183060c1c08606180408118204122448a121804082,0x2028a0a061870a080818a1010410245070e0c38704042070808103060c1830e0c183060c1830402103060c1830e0c183060c183041c4080e1c3870e1c3871028100811c3870e142850e1c3870e20109042c10204081070e1c10504141050408102041428504141010208081020408104080820404082020408102041020208100880238708102040804041041038408102040810204080420104020408e1c3870e1c3870e2010081020408e1c0408e1c3870e1c04084,0x80828288081020408042810c10204081020408102040210085060c1830610183060c0830218183060c184060c183020c0850e064091210204081008802183040810204081020408042010a2410b04081020410201040418404101020408104080410106040820204081020410102043010208081020408104040810a10204081020408102010804280811008081023010810204080404101,0x2041010204081020810104202010208081020408104080821404082020408102041020208381020808102040810408082120408202040810204102020838102080810204081040808201040820204081020410202081810208081020408104080820604082020408102041020208041020410202040820204081040808201,0x4021408102040840810082030814105040810204142850410183040c1020408103060c103060c1030408102040c183040c1830e08402040810210204020a0c305041410204081050a1410506141050408102041428504141890a0818b04081050408100810210506,0xe143051020405120248508102020e044050a1440914244040810203060c183100c183060c183080c183060c283060c183060c204080638710142850102040900238184020c081242830102040810240081,0x60c1830602183060c1830612203060c183140c183060c1831228483030c1830606043060c183060c383030c0c3060c181810c183060c18301,0x10140c510065008a245090a1040808240c181200c60102409012404401] g255 9 24 18 8 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part255_9_42 : block g255 9 42 24 = true :=
  @streamBlock #[0x0,0x0,0x2,0x800000,0x2000000000,0x2,0x3,0x60c183060c183,0x0] g255 9 42 24 9 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part255_9_66 : block g255 9 66 24 = true :=
  @streamBlock #[0x0,0x0,0x2,0x840804102,0x20000000000000000000,0x10000,0x3000000183,0x8203060c183020c183,0x0] g255 9 66 24 9 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part255_9_90 : block g255 9 90 24 = true :=
  @streamBlock #[0x0,0x4000,0x10204082,0x4,0x840000000,0x2,0x183,0x203060c183060c183060c181,0x0] g255 9 90 24 9 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part255_9_114 : block g255 9 114 24 = true :=
  @streamBlock #[0x183040c1818600002000000000080018606,0x2060a103040c1420000003000000007020000304040820e,0x408e10040001020408000810118084020404604,0x2040810204081020408102,0x20408102080804204081020408002040800000,0x7011438084002850a1428000181880c,0x230081024060120042060c0c183,0xa00183060c180860c0030600182040800183060c183,0x803023480d] g255 9 114 24 9 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part255_9_138 : block g255 9 138 24 = true :=
  @streamBlock #[0xc183060c182060c1420600000060a0c2030a102840c10300000c2060c0c2860c,0x408002040811828001020070102305000c184061404000143050e0204000021840c181030a0408708,0x1c30001023840118004001020408102000600000020000000000000004000000c1030e023808102304040808102,0x1c081020408102040408204081020408102040820204081040204102,0x1020408102040810204081020408102040800000001020000000040204204,0xe024050e14040000000000002850a14285000000006000030a000030000388000030081,0x1850818305080004084002840c0028400020030608181021818206,0x610184000c183060c18306003070c10203060c1830600183080c2030a060c183,0x6010234681020c603] g255 9 138 24 9 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part255_9_162 : block g255 9 162 24 = true :=
  @streamBlock #[0x2850c142050a102850c142860a142850a182850c103040c142050a1828708182840a14200081828508142040a,0x2860e182060c102860e143070c183060c1c3060e103050e182860c1c3080a1c3050c1828008183060a182040a,0xe1c4081024384020408100040040810183020408100001871010301000000002000000000003080c200000000100000000000183041c04706101020408083020408102,0x204081020810204041010204081040810202040810208081020410102040810204082010408104,0x20408380011c000040000004081040010200000800000101020408102041838404081020408103080818084080460e,0x180040814000000000001003880c000000000280000000000020040000000011c4000018400000000000000000814000061400000000000000003040c38601,0x8000c1830408183060c003000210300001830408183060c0020600003000c183000c182060400300001800600183040c00300,0x700002050e102070a0c0050e100070002180101848500004040e1c2830002205102000800201840a0228000102800310301812004081,0xe0638000100c181002050e] g255 9 162 24 9 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part255_9_186 : block g255 9 186 24 = true :=
  @streamBlock #[0xa102860a18285000000000000050a143060c1828000001848614306000000000001850a0c10204203010e14382040404081023010c,0x608608183850e1430000003060c183870e1c300000c300001428102,0x811c20001140450000004080c180081020400040000008388000c4830c20404080810102,0x20408102040810204081020408102040810204101020438102,0x810204081020408100840810204081020408102040810204,0xa18387001c4001000380001c0000a142000814005001000001000030e1c20310,0x18010386000c183000000300180081200003060c000000c183082410208,0xc18000001830000004000000300002030618000000c1800000206000000300000c183,0x8e060c1831c20703140050e] g255 9 186 24 9 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part255_9_210 : block g255 9 210 24 = true :=
  @streamBlock #[0x20080180481618300800200000003860c1c3000c0030000000000000000000000000000060a0810201,0x20080180481818380800200000004070e203000e0038000000000000000000000000000060a0408082,0x2008a18000941c04400102800010204001020400100040100003060208402020000c1820202,0xc100810204081020408102020810204081020408102040810204081040410102,0x304040810204081020408100840810204081020408102040810204080c20a0c30204,0x40c0204700004090a142890a200060c0004000140000a14285081420500000030c1c18181003050a,0x8000040100284100028080002000010000000028400002860000200000c18306,0x5080c183060c183060c1830008180880c183060c183060c18306020c0831c0c183,0x18a18040920604190060c501] g255 9 210 24 9 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part255_9_234 : block g255 9 234 24 = true :=
  @streamBlock #[0x4082420000143870c1c0000c10006001420000000000408000001400910180060c184850a1404081,0x143808a103080c182070c143800a1000500000000014187121c206040408514,0x284080008002020460002000001020008102000000000060008101020000010044001008102,0x14081040408102040410204081020408102041020102102020808104,0xa081020418102040804204081020408100810810204,0x288121c04080200000a142050a00280000030081003080a,0x1414000100c30000020400102000000038600000408000183060c040860c04081,0x10183060c1830600043081c284060c2000614203060c1808a100c183060c181,0x20c194020c1830230589] g255 9 234 24 9 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part255_9_258 : block g255 9 258 24 = true :=
  @streamBlock #[0xc022850c140490a2040081242070c142860c1c38500000060c104800c142808e,0x300001420000180000c180400100000800004000000000a1000000000060c1800500003800000183060000000004008c14102040408810,0xc0040801144080e102008802200080020408102040800000081020006004060a1010102,0x2810204081020408102040810204041020408102040810204081020408102,0x704081020408102040810204081008408102040810204081020408100840010204,0xc02307002428701002850a1c38612204000c1804080000050a182800a142850a102850a00003060210306182850a,0x70c202830e143000c00045101c30100020080e141808e1800600180070e0000301,0xc183000c183060c183060c18304001830600183060c183060c18306,0x603280c18e180c18a060c092060460c063808e] g255 9 258 24 9 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part255_9_282 : block g255 9 282 22 = true :=
  @streamBlock #[0x8183000c1c40b00000040c1800608183800a0000000000c0001c1800014102021050a0c,0x1000008002000000000000200000100040000000000001830c1800083204860c08081020248401,0x2484010004a010000008102040010200000000700002000c0c401021c10102,0x2040810204081010208102040810204081020408102,0x408102040810204081020408102040810200,0x2060e2428812245850c142850a142850a000020108040000000000,0x18408082030612103870c1c207100c18306,0x10283060c183060c183001c043060c183060c18183180c18e,0x2004181020c1811204803] g255 9 282 22 9 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part255_9_304 : block g255 9 304 24 = true :=
  @streamBlock #[0x0,0x8000000000000000,0x100,0x1,0x208102,0x20200102000000008082000018100,0x10000000000000100001000004040840000084,0x410081,0x81040400202080408204004040810082080808208100810004202020420100041010c040810210101,0x0] g255 9 304 24 10 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part255_9_328 : block g255 9 328 24 = true :=
  @streamBlock #[0x10000000000000000000000000000000000000010218102,0x0,0x10000040008000000000000000,0x20408101,0x210201,0x810410101001010004000800000000,0x2040000000000800010000,0x40208104,0x20200000020420604041010810080020800000041010c2020204082020418302,0x0] g255 9 328 24 10 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part255_9_352 : block g255 9 352 24 = true :=
  @streamBlock #[0xc1800000000000000000000000000000080804186,0x80000000000000000000000030a,0x1040000010001020204000,0x0,0x0,0x100101020200000000820402100020400000,0x40000000000020800100,0x2020c04202,0x10000000000008204001010010001040008008101020400000000808002080060004100,0x0] g255 9 352 24 10 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part255_9_376 : block g255 9 376 24 = true :=
  @streamBlock #[0x80400000000000008000000000000000000000000,0x8000000000400002000c00000000000000001000000104,0x810000000000400000000000000000,0x820404102,0x42040208102,0x41808100001020204000,0x820304001000100040000000000,0x1,0x4181020804002020430100002010200201000000408083040400082041010000041010c00102,0x0] g255 9 376 24 10 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part255_9_400 : block g255 9 400 4 = true :=
  @streamBlock #[0x20000,0x0,0x0,0x2,0x0,0x200082,0x81060418000,0x0,0x4042020210204,0x0] g255 9 400 4 10 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem level255_9 : block g255 9 0 404 = true := (@block_merge g255 9 0 400 4 (@block_merge g255 9 0 376 24 (@block_merge g255 9 0 352 24 (@block_merge g255 9 0 328 24 (@block_merge g255 9 0 304 24 (@block_merge g255 9 0 282 22 (@block_merge g255 9 0 258 24 (@block_merge g255 9 0 234 24 (@block_merge g255 9 0 210 24 (@block_merge g255 9 0 186 24 (@block_merge g255 9 0 162 24 (@block_merge g255 9 0 138 24 (@block_merge g255 9 0 114 24 (@block_merge g255 9 0 90 24 (@block_merge g255 9 0 66 24 (@block_merge g255 9 0 42 24 (@block_merge g255 9 0 24 18 part255_9_0 part255_9_24) part255_9_42) part255_9_66) part255_9_90) part255_9_114) part255_9_138) part255_9_162) part255_9_186) part255_9_210) part255_9_234) part255_9_258) part255_9_282) part255_9_304) part255_9_328) part255_9_352) part255_9_376) part255_9_400)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part255_10_0 : block g255 10 0 13 = true :=
  @streamBlock #[0x3060a141860a042870a1038701143030c1808501142040a102030c0c18306183060c142040618183060c040811018306183060c18283060c183060c0c50a18305060c183041c04204081060a02040810828084081020a10280811008204040810208102041c04104080810204102040828401040860c183060204082041008108102040804081040804081183060c1828081040860c1404081180c183060c4080408081023060c18305010204401020460c183060a0204081,0x60c142830e140860e140810e02280861c3810c102010214204061c183060c3060204284080c383060c1840804083060c3870e1c386060c081060c1870a143870c0c181020838084081020e1804082041050108102041420408040810408081020410204080810208101020408204081010202081011c3870e04081020420102102040810081020408081020470e1c386081008101020408e1c3870c0204102,0x180810a02045100408104082010210204081008102081050204180860c18102041020804083080c1830204082040c0810e0204081040810408181021020408100810208102020410204080410204102040408204081040204082040408102040810404081040808102040810208081020810402042040810201020410201040808102040820408204,0x10408081020410204082070208101020408204081040a04102020408104081020c180820404081020810204142810408081020410204081830208101020408204081030604102020408104081020e0208204040810208102041428104080810204102040828502081010204082040810081,0x830504081021002385081c1050a0810204142050a10042081010204081830c18306041020204081030614040810818304081020102183060c10306081020414203060c1820a0210204082840a0204084020420408100810204081,0x3060c2808114400860c183060c1870a140480e0c183060c1830602183060c183060c183060c283060c183060c183060c3850a02040860c183060c1870102040810c18306,0x142040602183060c3050818284080c403060c1808a100418306180860c18303060c183060c3010c18306060c183,0x18306288011440703060c183060c0810204801060c183] g255 10 0 13 8 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part255_10_13 : block g255 10 13 24 = true :=
  @streamBlock #[0xa103060e1c2840e000000a103060102040011c0408c00000000000000142000018284000000000142000002048001c040811c00000000000000000060c1830000000001830600000000018300000c1830600000011c00000000070e183060e0c183060c1870c18303060c1860a183060102048011804081023850a142850c184070a1c3820408102041c3808c18302040810204142850a0408102040820408081020408104083840c1804082040810218204081020402042070c183070e1c040811c0408e023060c020c18c183060c10206081c301831c3060c06000000604081020408102047011c04080,0xa103800014200800230001023860000040811800700142070000000001420700102000810204000020408100040000000060c183000030000183060e18000060c183080000081022080e1c38306024070e1c287011c30081023808a14285081420404081020c18102040820408040810204102020408110100470104087081020408203808e203870e02040811c04808020408e10200810238401,0x6001c3800c0004082040810204081020408102040800800204000420008100810204081020408102040810200083060c18606180410c180810102183060c184021020112103808102204081020508020408c040810810204081008204081020204102040810102040810204081021020408240440202040820208102040810204081020408102,0x40810204081020810204081020408102040810202040810404081020810204081020408102040810204040810218301040408204080408204081020808104040810204081020408102040820404081020410102040820404081020408102040810404081040410204081020408102040810204,0x8102041c10204080400e02047001c00081020070e021020408000000010204082800a1428500140050a140050a000000008102041830604201020c1804084081020a142820a081050a08102040c102040818304081020c181008e0810204141050a0810204081020108102010804501020408a02280810228081,0x2038700000000020040800204080000000c02000010238000000050a1400000000000014285000240080000000e1c00001020400000000060c18306183060c180408c183060102183060c18701023060a020470a203808c0c1850a1428506142850a140408102040810204081023800102040812004081,0x612003800102000860c183060c183060c183060c1800c2400706024800e0c183060c183060c183060c183060c1830618303060c183060c040860c183060c18306020470102180861c1830602183060c183060c183060c18306,0x183060c2840c14200000c283080c18000000000c1830600183060c182840000183060c28401142070a10383060c1860a10300010204700023808102183060c0c183060c183060c183060c1830c3030c0c000000c0c183060c183060c183060c183,0xc064818e060c18e180c9031c0c1831c04589023800c02307011c30080] g255 10 13 24 9 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part255_10_37 : block g255 10 37 24 = true :=
  @streamBlock #[0x40c1428400102008e004000012304081c2060a142000810380010000608103050a0000408140000c000060c00289000000412103050a0000408140000c000060c00000000c183060c1830600183060c1800600000000000000000000000003060c183060c180060c18306001800000000000000000000000000000000000000183080120247120c40910280430c0c306012404603062c70c1824606183060e181860c18301831c488100240a01144008c1c3870c142850a142850a142850a142860a14282040810204081070408102041c1070408102040810204081020808102040828202040810204081040408102041010404081020408102080810204082021030912060c1830440081242010c1c04092020840810204081020108102040804204081020408103060120400921c04183060c18818040811c0440e0248081180408c183858c183048a183060e182018e1c3870c183060c183070e123060c143060c1c3060c18306010204481240409202040810204081020460c,0x12004001220380001800800000070000300800200901020000c0004000003800024008002004700000000e000000e000000000200120040001023800000380001c0000000183060c183060c043060c183080c18001020408000000000c183060c1830618183060c184062000000103008102300000020000000071020400901c383122440b010c38081023870e204008e1c3830e1c3880e0c3880e200450a1c4880e0248b01144040e143060a142850a142850c142850a14205040810204081020e081020408202041c102040810204082020408102080810102040810204082020408102080810204081020408102040810404081020410108024880810204022404092100870110040920208101020408e10204081020408042040810201080238090020408e183870e203840e02040810240081020408e02040810204081022070e,0x4810100040804049101800112183800124484001020101020460002040081020000102010810204000420000180000810200001020408102000800000800c183060c1830604183060c181060c3010c000008104040860c183060c183020c183060c08300000840000204021000008204090810204020248812100890802044081020408102010810204080420408100450a1020408040408114201011830408102040810201081020408042020408102040810104081020404102040810204081020208102040808202040810204081020408102040810204081020408102040810204081020408102102040810204080420408102010810080921c484081020408040408102480880408081,0x2040810204081040408102041010e040810204081020408102041010104081020408102080810204082020408102040810204081020408102040810204081020408202040810208086040408104040820202081020408102041010204081040410102040810404081020408102041010204081040408102040810204082020408102080810204081020408104040810204101020408102040810208081020408202040810204081020808102040820204081020408102080810204082020408102040810208081020408202041010204081020408102080810204081020810102,0x1020408102040838204081020e0838204081020408102040810204021020408102040820204081020a0810204081020408102040810204081020408102040838204081020e08306100810204084070402042040810204081040408102041410504081020414102040810204081030408102040c102040810204081020608102040818204081020408102041c10204081070408102040810204101020408105040810204081020410102040810504080420408102040810204021020408102040204204,0x200450a1c4070e020491000408121830710200450a1c488100204080200460c020450a142850a142890a142800a2428500142850a142850a142850014280060c183060c183010c183060c40300180000e020408102000860c183060c183100c183060c043000c0000a0228081140071014287101c4030124405100c4860c140450a142850a142830a142850a0c2830a142850a142850a022850a142808a023808a14280810204081020408102280810204081,0x1040010240000e0c0400018483000000700002080002480000204000020400000040001040010200000e0c400001804300000000820008010000701000008100000000c183060c183060c183060c183060c303060c183060c180860c183060c183060c183060c183060c183060c183061c4080102387010c0481002043101c188100c040811c183010c040900c043010c18086,0x3060c183060c180860c18306101840c182871014208060c183060c183060c183060c300810c183060c1830620183060c18406104008a240450810303060c183060c188060c1830610180880c183060c1830620183060c188060c3030618183060c0408602183060218086020430c,0x240c09006401901c0c18e240c91006301920640903240c09006401811c0c18e020c09006301810604083] g255 10 37 24 9 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part255_10_61 : block g255 10 61 21 = true :=
  @streamBlock #[0x3800e0024710140000000387000000601180060e000450000000000038000003060c1400710000000e1c00080180060c18280060c183060c003000c187060c0060c0204600000000000003060c183060018006000000000040811c000000000000183870c060c3030c3831220183060c1860e183058c1230706181818c1c3060a203090a200490a143860c1c30601183050a142850a142850a1c3860c18305040810204081020408102040810204081020408102040810102040810204081020408102040820204081020408102040860e1020914100408e100840810204081020408183808c245808e023808c1c0460c1c3060c1c30701183070c183070c1804701020408c02040810204081020470c,0x60e1c3080c1c0000c0004081180460118047010200001003070e184060e0000600183070e1c3009002000860c183060c383100c30081180408102043060c183061c1870620040811c040811c307121c408120c3831024187101c3880c1c388061c1881014409141440712143070c1804610023050a142850a142850a183050408102040810204081020408102040810204040810204081020408102040810204081020404a081004a081c0490810204081020408100408102040811c3808102040810204081020408102040811c04081,0x60e102080c003880c18300811c50608100808e18000811820400102040010204001020408002040210204080c183060c18406201830c000000102080810c183060c18406101800000201080000008102010800000021c4818320483120c403060c18812102040810203080c20408202840828284012428702200860810204081020408102040810204021010204081020408102040810204081020408102040808102040810204081020408102040810204081020420408102040810204010240a011020408100808128044020204901,0x40810204081020408802040810204101020408102040410204081020408102040810204081040408102040810204081020408102040810204101020408102040810204081020408102040810404081020408102040810204081020408102040810204081020408102040810208081020408102040810204081040408102040810204081020408102040810204081020408102040810204081020408102041010204081040408102,0x2040810204081020418302040810204181020408040840810204081020408102040810204141020408102040810204081020408102040840204081020408102040810204081020414102040810204081020408102040810204081020408102040810204081070408102040810204081020a08102040810204081020408102040810204080420408102010810204,0xc14386100038710003060018007002040500203090028000801804080142850a140050a140000a0000400142850a0028500140050000003060c183061c1880614203000038000200070000003060c18306141850600280001000006002800014000000000000003818e204050624185060c1860e142850a142830a0c28306142850a142850a1428510202850024406011400a121440901024850e,0xc142040c0018706143040818387060c28308101860024284010028008000030e0c280000c2830010180001c280060c183060c183060c183060c183060c183060c183060c183060c183060c183060c0c8091c3880620188030c1808612183010c1808624183060218806,0x183060c183080c40300000050c002840a0c0030a0c184060c1830a00283060c183061018806142050e18185081040506002830a0c203080c303080c4030610043030c0c306061830e0c40306062c3030c24606180c3010c407010c4030c,0x3018e060c18c060c18c063818e203018c180c700060c18c0600183180c7031c40603] g255 10 61 21 9 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part255_10_82 : block g255 10 82 24 = true :=
  @streamBlock #[0x1220006000230000003060c183060c183060c183000e0204601020408e0000000000000c18007001838000003070c1c3070c1c3060e18300000000000183860e183070c1800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000183060c4808c18300810230610183060c183060c183050408102040810204081020204087010238b081020a1200300881000601023060c1c3060c,0xa10003000118505891c3070c1c0408c000000000000000000000003870020007101c4070e2038801020480000000000000001025000000000000000000000000000000000000000183860e183070c18000000030000000000000000000030000000000000000000000000000408102387101c380000000000000000000047060c0408e024060c183060c18101020408102040810204088010238b0810200921048081,0x812030600000008c00406000038600000408c00386000000000000000010204081000000102000810000081000008102000802000000000000000060e18387010238b0010200921004a081030708103060e1030081020440810204081020408102040810204081020408102040810203060c183060258094240460c182040808102040408102,0x2040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810c1c3070204081020408102040810204081020408102040810102040820408102040810204081020408102040810204081020408102,0x4081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020c1c3070408102040810204081020408102040810204081020102040840810204081020408102040810204081020408102040810204,0x80e1c048000030a002800810004800e0040001020080e02040000000000000000a1428000142800a00285001400500140050a002850000000000000000183060c1830701020050c2828a0a2004512143050c143060a183060c023008c142850a142850a142850a142850a142850a142850a142850a142850a0c183060c1860c1850910,0x6000200600180400000300000030000020470000000000000000000000000040010048001280000024000002000001020400000000000000001183860e004081028389012450090244008c1c3070c183860c0204081020408c183060020049012004801023070c1c3880e0240801020409002307010218306,0x3060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c18306183860e0c183060c183060c183060c183060c183060c1830602040810c183060c183060c183060c183060c183060c18306,0x800180090c2428410184060c183060c183060c0000800180008c282840c183060c183060c183060c0000800020008c0228410020460c183060c183060c0000800180008c282840c183060e18046011c3090e00000800200092282840c1c3070c1c3070c183860c00000800200092022840c1c3070102048011c040811c040900238081285090c1c3070000000000000000,0x1c4000c183808c2830900180460018046011c30080] g255 10 82 24 10 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part255_10_106 : block g255 10 106 16 = true :=
  @streamBlock #[0xe1c0070c2430816020000e00040801c0008e0000000004870c1c3870e00006001830000000000000306000000000000000000000000038000000000000000000000000004000000000000000000000000000000000000000000000000183060c18306185808e1840714243860c18102040810102040891428488081038089023880e,0xc023860018400002804700000008c000000c000000c2448012280000102040000004000000070c0238081183060e020008e0200816000480100380902004801183871200480800c187141c58081203060c183060c081010204480810204701,0xe10200010040a14240040010204010200000002040010004081020008002040810000000020000104040c183060000000000040000000000000000001020408102040000000000020000000000000003060c184102848408183060c08081020408102,0x10204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102,0x20408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204,0x3070c183880a005000a142850c1c38a121c040811830080002850a002800a1428508142850a1428000142860e002880a00000001840714243880c0000000002800a1428000000040a142850a140000000003060c1860c183070c,0x81c00008003080c00000000000080000008820000000000000100080e200000000000010000010000000000000801800000183060b0038812202480c003008100000001c000002048910143891020300801c000100240712,0xc183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c18306,0x30600183060c140070024384000030600183060c14007000204400003060018300811400700020440000386001840b101400700023840000309001c3060c14009002c3840000409001c50090140008002384001c30a101c3060c18380900204800,0x180060e1800b1028380100238800] g255 10 106 16 10 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem level255_10 : block g255 10 0 122 = true := (@block_merge g255 10 0 106 16 (@block_merge g255 10 0 82 24 (@block_merge g255 10 0 61 21 (@block_merge g255 10 0 37 24 (@block_merge g255 10 0 13 24 part255_10_0 part255_10_13) part255_10_37) part255_10_61) part255_10_82) part255_10_106)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part255_11_0 : block g255 11 0 4 = true :=
  @streamBlock #[0x182840c02284010c183060c18306020408114040810810601081050a04082040408204020410210201020204081020408802040810204081,0x182840c02284080c183060c183060204081140408808106010810508040820404082040204102102010202040880204081,0x182810210201020c181020c1810202041021020102081010208101020408102040810210201020204102,0x408204040820404082040408204040820404082040408204040820404082040408204,0x81040c081040a081030608103060810601081050a081050a0810081,0x182840c14284010c183060c1830614040810204081,0xc183060c183060c183060c18306,0x60c183060c183] g255 11 0 4 8 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part255_11_4 : block g255 11 4 11 = true :=
  @streamBlock #[0x60c1c3000000000000000000180408c00000000000000003060118000000000000000000000040811c00000000000000000000c183060c183060c183060c183060c183060c183060c186101c0400c020408c1838081023060e18046001c3060c183860c180451014046001c0460c1c0460c142850a142850a142850a142820408102040810204081020408102040810204081020404081020408102040810204081020408102040810204049081004610000460c200408810204081020408102040810040810204601020060c023808c0204081183070c180060e1830081020460c1c3060c000408102046010204600,0x183070c20306010000600180408c02040810000600183008c02306100000600020408e023008100000800c183060c183060c183060c183060c183060c186101c0480e020408e020408118386011c380811c3808c022880a020450e023808c183050a142850a142850a1410204081020408102040810204081020408102020408102040810204081020408102040810204080921020081202008e02040881020408102040810200810204081020470e020408102040810204701,0x30600004060c000460c1830600000408c000408c022040000204080020408000000810000081020008102000000183060c183060c183060c183060c183060c183060c308001040710100408102480881020408102040810204081004508000408a1004081182040810204081020408102040408102040810204081020408102040810204081010204081020408102040810204081020408102040840810204081020408100490810040901004081,0x81020408102040810218081020408102040810202081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102,0x40810204081020408106040810204081020408100840810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204,0x1800700203000e023060c183001000040801c0408c0204500140050a002850a14000001400500142800a142850000003060c183060c183060c183060c183060c183060c186001c2880e14380810230090142850a142850a142850a142850a142850a142850a1404501140408a0204081,0x180000c020460c0000600000060000040810230001000000c00006100230600000000000007000004081180400000183060c183060c183060c183060c183060c183060c1800e180470e0204081020008102047010204081,0x3060c183060c183060c303060c183060c183060c043060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c18306,0xc1c3080c184008c0000601180460c0204600] g255 11 4 11 9 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem level255_11 : block g255 11 0 15 = true := (@block_merge g255 11 0 4 11 part255_11_0 part255_11_4)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem part255_12_0 : block g255 12 0 1 = true :=
  @streamBlock #[0xc18081022820404080880204081,0x306020408a08101020220081,0xc1808802202040408401,0x10204081020408102,0x8102040810204,0x3060228501,0xc18081,0x306] g255 12 0 1 8 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem level255_12 : block g255 12 0 1 = true := part255_12_0

theorem table255 : checkedTables g255 12 := by
  intro k hk
  interval_cases k

  · rfl

  · rfl

  · rfl

  · rfl

  · rfl

  · rfl

  · rfl

  · exact level255_7

  · exact level255_8

  · exact level255_9

  · exact level255_10

  · exact level255_11

  · exact level255_12

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low255 : Lower (vars 255) (graphGoal 255) 13 :=
  lower_forest (g:=g255) (i:=0) (hints:=1394671617) (before_sound known254 valid254) geom255 table255 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def known255 : List (Nat × Nat) := (255,13) :: known254

theorem valid255 : Known known255 := knownAdd valid254 low255

def edgeEight (x : Fin 8 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 7) || (x 6 && x 7)
def sampleEight (r : Row) (j : Fin 8) := bit r ((vars 255).getD j.val zero)
theorem rowEight : ∀ r : Row, bit r (graphGoal 255) = edgeEight (sampleEight r) := by decide +kernel
theorem inputsEight : List.ofFn (fun j : Fin 8 => (vars 255).getD j.val zero) = vars 255 := rfl
theorem sampledEight (r : Row) : List.ofFn (sampleEight r) = (vars 255).map (bit r) := by
  rw [← inputsEight, List.map_ofFn]
  rfl
theorem exactLower (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 8 C = edgeEight) : 13 ≤ C.size := by
  by_contra! short
  have goalEq : (execute C.gates (vars 255)).getD C.output zero = graphGoal 255 := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    have sampleEval : bit r ((execute C.gates (vars 255)).getD C.output zero) =
        (C.wires (List.ofFn (sampleEight r))).getD C.output false := by
      rw [←b_read,execute_bits _ _ _ (fun g hg => (legal g hg).1),sampledEight]
      rfl
    exact sampleEval.trans ((congrFun computes (sampleEight r)).trans (rowEight r).symm)
  have hp : proper (graphGoal 255) := by unfold proper; decide +kernel
  have out := get_rep (execute C.gates (vars 255)) C.output
  rw [goalEq] at out
  obtain ⟨k,t,S,hk,run,sub⟩ := extract C.gates (vars 255) legal hp (out.resolve_right (fun h => h hp))
  have mem : ∀ a ∈ vars 255, Essential (graphGoal 255) (vars 255) a := by
    intro a ha
    apply essential_ok (xs:=graphPairs 255 1394671617) (by decide +kernel) a
    exact List.mem_toFinset.mpr (show a ∈ vars 255 from ha)
  have eq : (vars 255).toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun ha => ?_,sub a⟩
    obtain ⟨r,s,diff,isolated⟩ := mem a ha
    exact raw_required run (vars 255) a sub r s diff isolated
  have impossible : Impossible (graphGoal 255) 12 (vars 255).toFinset :=
    root_index (g:=g255) (before_sound known254 valid254) geom255 table255
      (k:=12) (i:=0) (ws:=vars 255) (by decide) (by decide +kernel)
  change  C.gates.length < 13 at short
  exact impossible k t (by omega) (eq.symm ▸ run)
end PEqualNP.Outside.L_meta_8533

theorem PEqualNP.Outside.L_meta_8533 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 7) || (x 6 && x 7)) t → 13 ≤ t := by
  rintro t ⟨C,legal,bound,computes⟩
  exact (PEqualNP.Outside.L_meta_8533.exactLower C legal (funext computes)).trans bound
