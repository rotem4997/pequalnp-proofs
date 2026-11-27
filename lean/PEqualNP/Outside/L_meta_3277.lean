import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_3277
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
  let nonedge := dneg (dbin false (ws.getD 0 defaultDecor) (ws.getD 2 defaultDecor))
  if g.mask=1023 then ws.map (fun w => dbin false w nonedge) else ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  have base := raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  intro a ha
  unfold wiresOf at ha
  split at ha
  · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp ha
    exact faithful_bin false (base w hw) (faithful_neg (faithful_bin false
      (faithful_get base 0) (faithful_get base 2)))
  · exact base _ ha

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  if m=1023 then liftGoal m v &&& ~~~(v 0 &&& v 2) else liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  by_cases e : m=1023
  · have u := asRow_bit v i (0 : Fin 9)
    have w := asRow_bit v i (2 : Fin 9)
    have h := bit_liftGoal m v i
    change (inputs.getD 0 zero).getLsbD (asRow v i).val = (v 0).getLsbD i.val at u
    change (inputs.getD 2 zero).getLsbD (asRow v i).val = (v 2).getLsbD i.val at w
    have seedEq : seed = inputs.getD 0 zero &&& inputs.getD 2 zero := by decide +kernel
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
def mined9 (i : Nat) : Nat := (if i<1 then 0x78007c003e001f000801afc00400035f800812fc004007a882757d44d69e41b13775b75d75f35168e75e69c2e62086ec2076ab53f10d63e5cafedf8fd9f3fade2f69d1f25c6f11bbee5b6ed1b1ebdacea9a1e6596e5191e3d8ce2987e1582e017dded78dd973dad68d9963d855ed7159d5d54d494fd354ad0939cdd34cc929c9d24c891fc751ac6115c4d10c390bc2506c1101bfcfcbd0ebba4e6b90dbb4ccab08bfac4aeab09da3c808012eeadd7086169893802d1f3b03ab4f33127005b3a7487569e6624e00b574ec0c2d344449c016ee1d2185b668493802d793b05934498927007af0689826053124e00b770eb184d0a4249c017ec1d63093148493802d3e3b03ab4f08927005b787487569e1124e00a73cea96cdb350494018e79c66d4b56a0928031cf38cda90ad41250063d66d5c3215a824a00973d6eb8a4334c494012edadd70c86698928031eb598d2b66429250063dcb31a56c48524a00a5ece9970d42ca494014bf1d12e1a859492802dcb3a64334d2a925005b9c7448669a5524a00e55d5dd1133348494018dbabb71c85690928031d7576e310ad2125004be6b75c3215a424a00c7cd5db8642b48494018faabb70885690928025f65bae090ad21250063ecaedc1215a424a00e59d5dd112ab4849401ce3abb99a5569092803d47511334aad2125005ab6758c36a18324a00b5acea986d4306494010f79d532da858c92802d9b3ae4334d19925005b967548669a3324a00b768e890cd346649401ad59c7694858cc928035cb38cd290b19925006bd4695c12163324a00f54d444ccd2466494016d99d7215a48cc92802dd33ac42b4919925005be2748856923324a00b7c8e890ad246649401eb1a88955a48cc92803dc34cd2ab4919925007ad26a18354d5224a00a75ceb576d2302494014eb8db999a4604928031b7598dbb48409250073666dda48cc8124a00f5b0d42a4c0aa249401ad71c769485844928035ce38cd290b08925006bd4695c32161124a00d5d966510d242249401aeb2cc999a484492803d565113334908925005bac758b56921124a00b7d0e916ad2422494016db1d7215a484492802dd63ac42b4908925005be474c856921124a00b7d0e910ad242249401af32cc955a484492803d665112ab4908925007b8c99a556921124a00f5c94434919c2249401ee92666923384492803de24aad246708925004a7eb75c81d5a724600d4f5443843ab4e48c012cf9d6b31a89dc918025cf3ad663512a923004bb675acc6a23324600b4ecec0ead3c6648c016cd9d61d5a78cc91802db93a43ab4f19923005af2760c268d32246009774eb598d444448c01eb61a860952544918029db3ad5dc66c08010053ba75abb8898100200f5b0c12a4c0aa200401ebc1824c9814c4008025be3af662a508801007bd09563388a1100200 else 0x3c003e001f000f8007c00200780040000000078007c0020000000000000000003c0020000000000000000f000f8004000780040000000000000000000000f000f8004000)
def minel9 : Packing := (91,6,6,0,0,10,0,mined9)
def mined10 (i : Nat) : Nat := (if i<8 then (if i<4 then (if i<2 then (if i<1 then 0xbbf1c80c95124600bdf1c70c95124600bef1c60c95124600bf71c50c95124600bfb1c40c95124600ff61528895124600dfe2bb8895124600efe1a88895124600fbe2888895124600fde2778895124600ff60c58895124600ff62558895124600ffc23388951246008ff9c3aed82002008ff9c1aed8200200cfd8b36cd8200200cff0b16c582002008ffacc6e13200200cbfa886e13200200afeacc6093200200cfeabb6093200200cfdabb8cd8100200abfacc6098100200cbfabb6098100200ebe9825498100200ebe9824c98100200cfeabb8898100200cfdabb8cd5100200aff2cc6055100200cff2bb6055100200efd2336055100200ebf1826055100200ef715260551002008ff9c8aed31002008ff9c5aed31002008ff9c2aed3100200cbf8b86e131002008ffacc6e13100200cbfa886e13100200cbfabba213100200cf78b56d531002008ffacc6d53100200cf7a556d53100200cfe8b26c931002008ff8cb6093100200cbf9b86093100200afdacc4c93100200cfdabb4c93100200efc9824c93100200cfeabb8893100200ebea888893100200cfe9b58893100200aff2cc6053100200cff2bb6053100200cff1b56053100200ebf1826053100200efd1326053100200efe22260531002008ffacc6e12100200cbfa886e12100200cbfabba2121002008ffacc6d52100200cbfa886d52100200cf7a556d521002008ff9cb61521002008ffacc6cd2100200cbfa886cd2100200cfda336cd21002008ff9cb60d21002008ff9cb54d2100200cfdabb8cd2100200cfd9b58cd2100200aff2cc4c52100200cff2bb4c52100200cff1b84c52100200ebf2884c52100200aff2cc60e1100200aff2cc60a1100200ebf18360a1100200efd23360a1100200aff2cc54a1100200efd23354a1100200efe18254a1100200aff2cc4ca1100200aff1c84ca1100200ebf2884ca1100200aff1c54ca1100200efe1824ca1100200efe18388a1100200efe15388a1100200aaf9c8185a624e00aee9c2185a624e00acf9c7219a624a00ae79c5219a624a00aed9c3219a624a00aef1c1219a624a00cd79b76948524a00ce79b66948524a00cf59a56cc8524a00cf71a56c48524a00cbbabba21a424a00cebabb999a424a00eaba88999a424a00adb9c7215a424a00aeb9c6215a424a00af99c3215a424a00afa9c2215a424a00afb1c1215a424a00cf3abb955a424a00eb3a88955a424a00ee3a66955a424a00eb9a886923324a00ee9a666923324a00ef1a556923324a00cdb9b76908124a00afb2cc6921124a00ebb2886921124a00eeb2666921124a00ef32556921124a00ef91a48ce1124a008ef9c6aeda824600a9f9c81d5a724600acf9c61d5a724600ade9c21d5a7246008ef9c6aed8100200ebd2888ce1100200ebe28888a1100200efc23388a1100200 else 0x9bfacc6e03224600cbf9ca6e032246008ff9cb6a03224600cbf9b86a03224600cbf9baa203224600cdf9a86dc3224600d9fa886dc32246009f7acc6d43224600cf79ca6d43224600cf79a86d43224600db7a886d43224600df71c16d432246008ff9cb6943224600cbf9b86943224600cdf9b76943224600cef9b66943224600cf79b56943224600cf79ba9543224600db79b89543224600dd79b79543224600de79b69543224600cfb9a86d03224600dbba886d03224600cfb9a56d03224600df3a556d03224600cff1a86c43224600dbf2886c43224600cff1a56c43224600df72556c432246008ff8cb68e2224600ebea8868a2224600ef6a5568a2224600efca3368a2224600afe9ca60a2224600ebe9a860a2224600afe9ca54a2224600ef69a554a2224600afe9ca4ca2224600efc9a34ca2224600afe9ca2e22224600bde9c72e22224600afeacc6a22224600afe8cb6a22224600ebe8b86a22224600ebe9a8a222224600ebea8869e2224600ede9a89de2224600f9ea889de2224600afe9ca2d62224600bfe1c12d62224600afeacc6962224600afe8cb6962224600ebea886962224600edea776962224600ef68b56962224600afe9ca6162224600afe9ca2162224600bde9c72162224600bee9c62162224600bfa9c42162224600bfc9c32162224600bfe1c12162224600ef69a59562224600ef69a89562224600fb6a889562224600fd6a779562224600afe9ca2ce2224600afeacc68e2224600afe8cb68e2224600ebea8868e2224600edea7768e2224600ef6a5568e2224600efc8b368e2224600afe9ca60e2224600afe9ca20e2224600bde9c720e2224600bee9c620e2224600bf69c520e2224600bfa9c420e2224600bfe1c120e2224600afe9ca54e2224600afe9ca14e2224600bfe1c114e2224600efc9a38ce2224600efc9a88ce2224600fbca888ce2224600efc9a78ce2224600fdca778ce2224600efc9a58ce2224600ff4a558ce2224600aff2cc6a15124600cff2bb6a15124600ebf1a8a215124600dbf2bba215124600cff2bb69d5124600ebf28869d5124600ddf2bb9dd5124600edf1a89dd5124600f9f2889dd5124600ef71a89555124600fb728895551246009ff1cb20d5124600aff1ca20d5124600bdf1c720d5124600bef1c620d5124600bf71c520d5124600bfb1c420d5124600bfe1c220d5124600dfd2bb8cd5124600efd1a88cd5124600fbd2888cd5124600efd1a78cd5124600fdd2778cd5124600ff52558cd5124600ebf1a86095124600aff1ca2095124600bf71c52095124600bf72cc5495124600df72bb5495124600ef71a85495124600fb72885495124600fd70c75495124600fd72775495124600ff52335495124600ff61825495124600ff617254951246009ff1cb0c95124600aff1ca0c95124600) else (if i<3 then 0xedd9a89de3324600f9da889de3324600afd9ca2d63324600bfd1c12d63324600afdacc6963324600afd8cb6963324600ebda886963324600edda776963324600afd9ca6163324600afd9ca2163324600bdd9c72163324600bed9c62163324600bfc9c22163324600bfd1c12163324600afd9ca5d63324600ef59a59563324600ef59a89563324600fb5a889563324600ef59a79563324600fd5a779563324600afd9ca2ca3324600cbf8cba21a224600cbfabba21a224600e9fa889dda2246008ff9cb215a224600adf9c7215a224600aef9c6215a224600afb9c4215a224600afd9c3215a224600afe9c2215a224600aff1c1215a224600cf78cb955a224600cf7abb955a224600eb7a88955a224600ed7a77955a2246008ff9cb20da224600adf9c720da224600aef9c620da224600af79c520da224600afb9c420da224600afe9c220da224600aff1c120da2246008ff9cb14da224600aff1c114da224600cfd8cb8cda224600cfdabb8cda224600ebda888cda224600edda778cda224600ef5a558cda2246008ff9caaed82246008ffacc6e98224600cef8c66e98224600cefa666e98224600cff2116e98224600abfacc6a18224600cbfabb6a18224600cbf9baa218224600cdf9ba9dd8224600e9f9a89dd8224600cf79ba9558224600eb79a895582246008ff8cb68d8224600abf9ca60d8224600cfd9ba8cd8224600ebd9a88cd82246008ff9cb6948224600cf79b56948224600cf79ba95482246008ff9cb68c8224600cfd9b368c8224600cfd9ba8cc8224600cbf9baa217224600e9fa8869d7224600cfd9ba8cd7224600edd9a78cd72246009df9c7aed52246008ffacc6e95224600cdf8c76e95224600cefa666e95224600cff2116e952246008ff9cb6a15224600cbf9baa215224600cdf9ba2dd52246009df8cb9dd5224600cdf9ba9dd5224600af7acc6955224600cf7abb6955224600eb7a886955224600ed78b76955224600ed7a776955224600cf79ba9555224600af79ca54d5224600cfd9ba8cd5224600ef59a58cd5224600ebe9a86095224600ef69a56095224600ef69a55c952246008ff9cb6a05224600cbf9b86a05224600cbf9baa205224600cfb9a86d05224600dbba886d052246008ff9cb68c5224600cef9b668c5224600cfd9b368c5224600cfd9ba8cc5224600ded9b68cc5224600cff1a86c45224600dbf2886c45224600cff1a36c45224600dfd2336c452246008ffacc6e93224600cefa666e93224600cff2116e932246008ff9cb6a13224600cbf9baa213224600cdf9ba9dd32246008ff9cb6953224600cf79ba9553224600afdacc68d3224600cfdabb68d3224600ebda8868d3224600edda7768d3224600ef5a5568d3224600efc8c268d3224600cfd9ba8cd3224600ebe9a86093224600efc9a36093224600 else 0xcef8c66e98524600cefa666e98524600cff2116e98524600cbf9baa218524600cdf9ba9dd8524600cdfa776e885246009fdacc6cc8524600cfd9ca6cc85246009feacc6c88524600cfe9ca6c88524600cefa666e97524600cff2116e97524600cbf9baa217524600eb7a886965524600ed7a776965524600af79ca6165524600af79ca2e25524600af7acc6a25524600af78cb6a25524600eb79a8a225524600eb7a8869e5524600ed79a89de5524600f97a889de5524600af79ca2ce5524600bd79c72ce5524600af79ca2ca55246008ff9c8aeda3246008ff9c5aeda3246008ff9c2aeda324600cbf9b82e1a324600adf9c72e1a3246008ff8cba21a324600cbf8cba21a324600cbfabba21a324600cdf8b76dda324600afe8c26dda3246008ff8cb61da324600cdfabb9dda324600e9fa889dda324600cf79b52d5a3246008ff9cb215a324600adf9c7215a324600aef9c6215a324600afd9c3215a324600afe9c2215a324600aff1c1215a3246008ff8cb955a324600cf78cb955a324600cf7abb955a324600eb7a88955a324600ed7a77955a324600abf9c82c9a324600adf9c72c9a324600aef9c62c9a324600af79c52c9a324600cfe9b22c9a3246008ffacc6e98324600cef8c66e98324600cefa666e98324600cff2116e98324600cbf9baa218324600cdf9ba9dd8324600cf79ba95583246009dfacc6dc8324600cdf9ba9dc8324600cef9a76d88324600dcfa776d883246009f7acc6d48324600cf79ca6d48324600cf79a76d48324600dd7a776d48324600df71c16d483246008ff9cb6948324600cdf9b76948324600cef9b66948324600cf79b56948324600cf79ba9548324600dd79b79548324600de79b69548324600cfb9a76d08324600ddba776d08324600cfb9a56d08324600df3a556d083246009feacc6c88324600cfe9ca6c88324600cfe9a76c88324600ddea776c88324600cfe9a56c88324600df6a556c88324600cff1a76c48324600ddf2776c48324600cff1a56c48324600df72556c48324600cefa666e97324600cff2116e97324600cbf9baa2173246008ff9caaed53246008ffacc6e95324600cefa666e95324600cff2116e953246008ff9cb6a15324600cbf9baa215324600cdf9ba9dd5324600cf79ba9555324600cdfa776e85324600cefa666e853246008ff9cb6a05324600cbf9baa205324600cff1a86c45324600dbf2886c45324600def2666c45324600ebda8868e3324600edda7768e3324600ef5a5568e3324600afd9ca60e3324600afd9ca5ce3324600afd9ca54e3324600afd9ca2e23324600afdacc6a23324600afd8cb6a23324600ebd9a8a223324600afdacc69e3324600afd8cb69e3324600ebda8869e3324600edda7769e3324600edd87569e3324600afd9ca61e3324600edd9a761e3324600)) else (if i<6 then (if i<5 then 0xbfe2cc4c52124a00dfe2bb4c52124a00fbe2884c52124a00efe1a64c52124a00fee2664c52124a00ff62554c52124a00ffc1634c52124a00ffc2334c52124a008ff8cb6a21124a00cbf8b86a21124a00afbacc6921124a00ebba886921124a00ef3a556921124a00ef99a48ce1124a00ebf2886861124a00ef72556861124a00efd2336861124a00aff1ca6061124a00ebf1a86061124a00efb1a46061124a00aff1ca5461124a00ef71a55461124a00efb1a45461124a00ff61525461124a00aff1ca4c61124a00efb1a44c61124a00efd1a34c61124a00fbe2884861124a00bfe1c54861124a00ff62554861124a00ffc2334861124a00aff1ca2e21124a00aff2cc6a21124a00aff0cb6a21124a00ebf0b86a21124a00ebf1a8a221124a00eef1a899a1124a00faf28899a1124a00aff1ca2d61124a00aff2cc6961124a00aff0cb6961124a00ebf2886961124a00eef2666961124a00ef70b56961124a00aff1ca6161124a00aff1ca2161124a00bdf1c72161124a00bef1c62161124a00ef71a52161124a00bfb1c42161124a00bfd1c32161124a00bfe1c22161124a00ef71a55961124a00ef71a59561124a00ef71a89561124a00fb72889561124a00ef71a69561124a00fe72669561124a00efb0cb6921124a00efb0c86921124a00efb0b86921124a00efb2886921124a00efb1866921124a00efb0c56921124a00efb0b56921124a00efb1856921124a00efb0856921124a00efb1656921124a00efb2556921124a00aff1ca2ce1124a00bef1c62ce1124a00aff2cc68e1124a00aff0cb68e1124a00ebf28868e1124a00eef26668e1124a00ef725568e1124a00efd0b368e1124a00aff1ca60e1124a00ebf1a860e1124a00efb1a460e1124a00aff1ca20e1124a00bdf1c720e1124a00bef1c620e1124a00bf71c520e1124a00bfb1c420e1124a00bfe1c220e1124a00efb1a458e1124a00aff1ca54e1124a00ef71a554e1124a00efb1a454e1124a00aff1ca14e1124a00bfe1c214e1124a00efd1a38ce1124a00efd1a88ce1124a00fbd2888ce1124a00efd1a68ce1124a00fed2668ce1124a00efd1a58ce1124a00ff52558ce1124a00bfe2cc54a1124a00bfe0cb54a1124a00efe1a854a1124a00fbe28854a1124a00fee26654a1124a00ff60b554a1124a00ff625554a1124a00ff615354a1124a00ffc23354a1124a00abf9ca2ce8824600abf9ca2ca8824600cbf8cba21a724600cbfabba21a724600e9f8c7a21a724600e9fa889dda724600adf9c81d5a724600e9fa881d5a7246008ff9caaed8724600cefa666e98724600cff2116e98724600cbf9baa218724600e9fa8869d8724600adfacc6a27724600e9f9a8a227724600cbf8cba21a524600cbfabba21a524600cdfabb9dda524600e9fa889dda5246008ffacc6e98524600 else 0x8ff9cb6a15124a00cbf9baa215124a00cef9ba9995124a00af7acc6955124a00cf7abb6955124a00eb7a886955124a00cf79b66955124a00ee7a666955124a00cf79ba5955124a00cf79ba9555124a00afbacc6915124a00cfbabb6915124a00cfb9b86915124a00ebba886915124a00cfb9b66915124a00eeba666915124a00ef39656915124a00ef3a556915124a00cfd9ba8cd5124a00ef59a58cd5124a00ef99a48cd5124a00bf6acc5495124a00df6abb5495124a00ef69a85495124a00fb6a885495124a00fe6a665495124a00ff4a335495124a00ebf1a86055124a00ef71a56055124a00efb1a46055124a00ff61526055124a008ff9cb6a05124a00cbf9b86a05124a00cbf9baa205124a00afbacc6905124a00cfb9b86905124a00ebba886905124a00cfb9a46cc5124a008ff9cb68c5124a00cfd9b368c5124a00cfd9ba8cc5124a00ef99a48cc5124a00cfe9a86c85124a00dbea886c85124a00dfca336c85124a008ff9caaed3124a008ffacc6e93124a00cdfa776e93124a00cfea226e93124a008ff9cb6a13124a008ff8cb6a13124a00cbf9b86a13124a00cbf9baa213124a00cef9ba9993124a008ff9cb6953124a00cf79b56953124a00cf79ba9553124a00cfbabb6913124a00cfb9b86913124a00ebba886913124a00cfb9b66913124a00eeba666913124a00cfb9b56913124a00ef3a556913124a00afdacc68d3124a00cfdabb68d3124a00ebda8868d3124a00eeda6668d3124a00ef5a5568d3124a00ef99a458d3124a00cfd9ba8cd3124a00df69b55493124a00aff2cc6853124a00cff2bb6853124a00ebf2886853124a00eef2666853124a00ef72556853124a00efd1636853124a00efd2336853124a00aff1ca6053124a00ebf1a86053124a00efb1a46053124a00efd1a36053124a008ff9cb6a03124a00cbf9b86a03124a00cbf9baa203124a008ff9cb6943124a00cf79b56943124a00cf79ba9543124a00cfe9a86c83124a00dbea886c83124a00df6a556c83124a009fe9cb5483124a00df69b55483124a00dbeabba212124a00faea889992124a009feacc6d52124a00dbea886d52124a00deea666d52124a009fe9cb2152124a00afe9ca2152124a00bde9c72152124a00bee9c62152124a00bfa9c42152124a00bfc9c32152124a00bfe1c12152124a00df69b59552124a00df68cb9552124a00df6abb9552124a00fb6a889552124a00ef69a69552124a00fe6a669552124a009fe9cb20d2124a00afe9ca20d2124a00bde9c720d2124a00bee9c620d2124a00bf69c520d2124a00bfa9c420d2124a00bfe1c120d2124a009fe9cb14d2124a00bfe1c114d2124a00dfcabb8cd2124a00fbca888cd2124a00efc9a68cd2124a00feca668cd2124a00dfc9b58cd2124a00ff4a558cd2124a00ffc0c18cd2124a00) else (if i<7 then 0xef98856923324a00ef99656923324a00ef9a556923324a00afd9ca2c63324a00afeacc6a15224a00cfeabb6a15224a00ebe9a8a215224a00dbeabba215224a00deeabb9995224a00eee9a89995224a00faea889995224a00ef69a89555224a00fb6a889555224a00fe6a669555224a00ebe9a860d5224a009fe9cb20d5224a00afe9ca20d5224a00bee9c620d5224a00bf69c520d5224a00bfa9c420d5224a00bfe1c120d5224a00bf6acc54d5224a00df6abb54d5224a00ef69a854d5224a00fb6a8854d5224a00fe6a6654d5224a00ff498354d5224a00ff49538cd5224a00dfcabb8cd5224a00efc9a88cd5224a00fbca888cd5224a00feca668cd5224a00ff48c58cd5224a00ff4a558cd5224a00cbf8cba21a124a00cbfabba21a124a00eafa88999a124a008ff9cb215a124a00adf9c7215a124a00aef9c6215a124a00afb9c4215a124a00afd9c3215a124a00afe9c2215a124a00aff1c1215a124a00cf78cb955a124a00cf7abb955a124a00eb7a88955a124a00ee7a66955a124a008ff9cb20da124a00adf9c720da124a00aef9c620da124a00af79c520da124a00afb9c420da124a00afe9c220da124a00aff1c120da124a008ff9cb14da124a00aff1c114da124a00cfd8cb8cda124a00cfdabb8cda124a00ebda888cda124a00eeda668cda124a00ef5a558cda124a00efd0c18cda124a009ef9c6aed8124a008ffacc6e98124a00cdfa776e98124a00cef8c66e98124a00cfea226e98124a00abfacc6a18124a00cbfabb6a18124a00ebf0c16a18124a00cbf9baa218124a00cef9ba2d98124a00eaf9a82d98124a009ef8cb9998124a00cef9ba9998124a00eaf9a89998124a00cf79ba9558124a00eb79a89558124a00afbacc6918124a00cfbabb6918124a00ebba886918124a00eeb8b66918124a00ebb9866918124a00eeba666918124a00ef3a556918124a00cfd9ba8cd8124a00ebd9a88cd8124a00ef99a48cd8124a00ebe9a85498124a00cbfa886e88124a008ff9cb6948124a00cf79b56948124a00cf79ba9548124a00cfb9a56d08124a00df3a556d08124a00afbacc6908124a00cfb9b56908124a00ef3a556908124a00cfb9a46cc8124a008ff9cb68c8124a00cdf9b768c8124a00cfd9b368c8124a00cfd9ba8cc8124a00ddd9b78cc8124a00ef99a48cc8124a00cfe9a56c88124a00df6a556c88124a00cfe9a36c88124a00dfca336c88124a009fe9cb5488124a00cfe9ba5488124a00df69b55488124a00dfa9b45488124a00cf79ba9556124a00ee79a69556124a00afbacc6916124a00cfb9b86916124a00ebba886916124a00ef3a556916124a00cfd9ba8cd6124a00eed9a68cd6124a00ef99a48cd6124a00ebf1a86056124a00efb1a46056124a008ffacc6e95124a00cdfa776e95124a00cfea226e95124a00 else 0xeb7a88955a324a00ee7a66955a324a008ffacc6e98324a00cdfa776e98324a00cfea226e98324a00abfacc6a18324a00cbfabb6a18324a00ebd8c36a18324a00cbf9baa218324a00cef9ba9998324a00eaf9a89998324a00cf79ba9558324a00eb79a89558324a00cfbabb6918324a00ebba886918324a00eeba666918324a00ef3a556918324a00cbfa886e88324a00cefa666e88324a009f7acc6d48324a00cf79ca6d48324a00df69c26d48324a008ff9cb6948324a00cef9b66948324a00cf79b56948324a00cf79ba9548324a00de79b69548324a00cfb9a56d08324a00df3a556d08324a00cfe9a56c88324a00df6a556c88324a009ff2cc6c48324a00cff1ca6c48324a00cff1a56c48324a00df72556c48324a00dfe1c26c48324a008ff9caaed6324a00cdfa776e96324a00cfea226e96324a008ff8cb6a16324a00cf79ba9556324a00ee79a69556324a00cfbabb6916324a00cfb9b86916324a00ebba886916324a00eeb9866916324a00ef3a556916324a00ebd9a860d6324a00ef99a460d6324a008ff9caaed5324a008ffacc6e95324a00cdfa776e95324a00cfea226e95324a008ff9cb6a15324a008ff8cb6a15324a00cbf9baa215324a00cef9ba9995324a00af7acc6955324a00cf7abb6955324a00eb7a886955324a00cf79b66955324a00ee7a666955324a00af79ca6155324a00cf79ba9555324a00cfbabb6915324a00cfb9b86915324a00ebba886915324a00cfb9b66915324a00eeba666915324a00ef39856915324a00ef3a556915324a00ebd9a860d5324a00ef59a560d5324a00ef99a460d5324a008ff9cb6a05324a00cbf9b86a05324a00cbf9baa205324a00cef9ba9985324a00cfe9a86c85324a00dbea886c85324a00deea666c85324a008ff8cb6a23324a00cbf8b86a23324a00ebda8868e3324a00eeda6668e3324a00ef5a5568e3324a00afd9ca60e3324a00ebd9a860e3324a00afd9ca58e3324a00eed9a658e3324a00afd9ca54e3324a00ef59a554e3324a00afdacc6a23324a00afd8cb6a23324a00ebd9a8a223324a00afdacc69a3324a00afd8cb69a3324a00ebda8869a3324a00eed8b669a3324a00eed88669a3324a00eeda6669a3324a00afd9ca61a3324a00eed9a899a3324a00fada8899a3324a00afd9ca2d63324a00afdacc6963324a00afd8cb6963324a00ebda886963324a00eeda666963324a00ef58b56963324a00afd9ca6163324a00afd9ca2163324a00bdd9c72163324a00bed9c62163324a00ef59a52163324a00bfc9c22163324a00bfd1c12163324a00afd9ca5963324a00eed9a65963324a00ef59a55963324a00ef59a59563324a00ef59a89563324a00fb5a889563324a00ef59a69563324a00fe5a669563324a00ef9a886923324a00ef99866923324a00ef99856923324a00))) else (if i<12 then (if i<10 then (if i<9 then 0xadf9c7215a824a00aef9c6215a824a00cf79b5215a824a00afb9c4215a824a00afd9c3215a824a00afe9c2215a824a00aff1c1215a824a00adf9c72cda824a00aef9c62cda824a00af79c52cda824a00afb9c42cda824a00cfd9b32cda824a00aff1c12cda824a00adf9c720da824a00aef9c620da824a00af79c520da824a00afb9c420da824a00afe9c220da824a00aff1c120da824a00adf9c72c5a824a00afb9c42c5a824a00cff1b12c5a824a00adf9c7205a824a00afb9c4205a824a00cbf9b36a28824a00cbf9b16a28824a00abf9ca2c68824a00bbe9c22c68824a00aef9c5219a624a00aef9c3219a624a00cdfa776e98624a00cfea226e98624a00aefacc6a26624a00eafa886a26624a00cbf8cba21a524a00cbfabba21a524a00cefabb999a524a00eafa88999a524a008ffacc6e98524a00cdfa776e98524a00cfea226e98524a00cbf9baa218524a00cef9ba9998524a00cbfa886e88524a00cefa666e88524a00cf79a56cc8524a009fdacc6cc8524a00cfd9ca6cc8524a00cf79a56c48524a009ff2cc6c48524a00cff1ca6c48524a00dfe1c26c48524a00cdfa776e96524a00cfea226e96524a00cbf8b86a16524a00af7acc6956524a00cf7abb6956524a00eb7a886956524a00ee79866956524a00af79ca6156524a008ff8cb6a25524a00eb7a886965524a00ee7a666965524a00af79ca6165524a00af79ca5965524a00ee79a65965524a00af7acc6a25524a00af78cb6a25524a00eb79a8a225524a00af7acc69a5524a00af78cb69a5524a00eb7a8869a5524a00ee78b669a5524a00ee788669a5524a00ee7a6669a5524a00af79ca61a5524a00ee79a899a5524a00fa7a8899a5524a00af79ca2ce5524a00afb9c52e1a424a00afb9c12e1a424a00cfbabba21a424a00ebb8cba21a424a00ebb8c1a21a424a00cfbabb619a424a00afb9c82d5a424a00ebba882d5a424a00afb9c62d5a424a00eeba662d5a424a00afb9c12d5a424a00afbacc615a424a00cfbabb615a424a00ebba88615a424a00eeba66615a424a00cfbabb215a424a00afb9c3215a424a00afb9c1215a424a00afbacc595a424a00cfbabb595a424a00afb9c8595a424a00ebba88595a424a00eeb986595a424a00ef3985595a424a00cfbabb955a424a00ebba88955a424a00eeba66955a424a00ef3985955a424a00ef3965955a424a00ef38cb955a424a00ef38b8955a424a00ef3a88955a424a00ef3986955a424a00afb9c82c5a424a00ebba882c5a424a00afb9c52c5a424a00ef3a552c5a424a00cbf8cba21a324a00cbfabba21a324a00cefabb999a324a00eafa88999a324a008ff9cb215a324a00adf9c7215a324a00aef9c6215a324a00afd9c3215a324a00afe9c2215a324a00aff1c1215a324a00cf78cb955a324a00cf7abb955a324a00 else 0xfbd2884c52124e00fdd2774c52124e00efd1a64c52124e00fed2664c52124e00ffc0c24c52124e00efd1a24c52124e00ffc1624c52124e00ffc2224c52124e009bfacc6e02124e00cbf9ca6e02124e008ff9cb6a02124e00cbf9b86a02124e00cbf9baa202124e00cdf9a86dc2124e00d9fa886dc2124e00cef9a86d82124e00dafa886d82124e009f7acc6d42124e00cf79ca6d42124e00cf79a86d42124e00db7a886d42124e00df59c36d42124e008ff9cb6942124e00cbf9b86942124e00cdf9b76942124e00cef9b66942124e00cf79b56942124e00cfd9a86cc2124e00dbda886cc2124e00cfd9a56cc2124e009fd9cb54c2124e00cfd9ba54c2124e00dbd9b854c2124e00ddd9b754c2124e00ded9b654c2124e00df59b554c2124e008ff8cb6961124e009fd8cb54e1124e00ebf2886861124e00edf2776861124e00efe2226861124e00aff1ca6061124e00aff1ca5c61124e00aff1ca5461124e00fbd2884c61124e00fdd2774c61124e00bfd1c54c61124e00efd1a24c61124e00ffc2224c61124e00aff1ca4861124e00aff1ca2e21124e00aff2cc6a21124e00aff0cb6a21124e00ebf1a8a221124e00aff2cc69e1124e00aff0cb69e1124e00ebf28869e1124e00edf27769e1124e00edf07569e1124e00aff1ca61e1124e00edf1a761e1124e00edf1a89de1124e00f9f2889de1124e00edf27769a1124e00eef1a899a1124e00faf28899a1124e00eef1a799a1124e00fcf27799a1124e00aff2cc6961124e00aff0cb6961124e00ebf2886961124e00edf2776961124e00eef2666961124e00aff1ca6161124e00ef71a56161124e00aff1ca2161124e00bdf1c72161124e00bef1c62161124e00bfd1c32161124e00bfe1c22161124e00aff1ca5d61124e00ef71a59561124e00ef71a69561124e00fe72669561124e00bfd2cc54e1124e00bfd0cb54e1124e00efd1a854e1124e00fbd28854e1124e00efd1a754e1124e00fdd27754e1124e00fed26654e1124e00ff518554e1124e00ff525554e1124e00aff2cc68a1124e00aff0cb68a1124e00ebf28868a1124e00edf27768a1124e00eef26668a1124e00ef725568a1124e00aff1ca60a1124e00ebf1a860a1124e00efe1a260a1124e00aff1ca20a1124e00aff1ca5ca1124e00edf1a75ca1124e00aff1ca54a1124e00ef71a554a1124e00ff515354a1124e00aff1ca14a1124e00bef1c614a1124e00bfd1c314a1124e00efe1a288a1124e00efe1a888a1124e00fbe28888a1124e00efe1a788a1124e00fde27788a1124e00efe1a688a1124e00fee26688a1124e00efe1a588a1124e00ff625588a1124e00ffc15388a1124e008ff9c5aeda824a008ff9c3aeda824a008ff9c1aeda824a00cef8b66d9a824a00aef9c62d5a824a00cf79b52d5a824a00afb9c42d5a824a00) else (if i<11 then 0xeeea66889a124e009ef9c6aed8124e008ffacc6e98124e00cef8c66e98124e00cfda336e98124e00cbf9baa218124e00cdf9ba9dd8124e00cef9ba2d98124e009ef8cb9998124e00cef9ba9998124e00cbf9ba6098124e00ebe9a26098124e00cfe9ba8898124e00aff2cc6858124e00cff2bb6858124e00ebf0c86858124e00ebf2886858124e00edf2776858124e00eef0b66858124e00ebf1866858124e00eef2666858124e00ebf1826858124e00efe2226858124e009dfacc6dc8124e00cdf9ba9dc8124e008ff9cb6948124e00cdf9b76948124e00cf79b56948124e00ddda776cc8124e00cfd9a56cc8124e008ff9cb6888124e00cdf9b76888124e00cfd9b36888124e00cfe9b26888124e00cfe9ba8888124e00dde9b78888124e00dfc9b38888124e00cfda336e97124e00cbf9baa217124e00cef9ba9997124e00cfda336e96124e00cdf9ba9dd6124e00cfe9ba8896124e008ffacc6e95124e00cfda336e95124e00cef9ba9995124e00cfe9ba8895124e00cff1ba6055124e008ffacc6e85124e00cdfa776e85124e00cfda336e85124e009fdacc6cc5124e00cfdaaa6cc5124e008ff9cb6885124e00cfd9b36885124e00cfe9ba8885124e00dfc9b38885124e009fd9c5aed3124e00bdd9c72e13124e00dbdabba213124e00fbd0c1a213124e00bfc8c26dd3124e00dddabb9dd3124e00f9da889dd3124e00cfdabb6993124e00edda776993124e00dedabb9993124e00fada889993124e00fcda779993124e009fdacc6d53124e00deda666d53124e00bbd9c82c93124e00bdd9c72c93124e00bed9c62c93124e00bf59c52c93124e00afdacc6893124e00cfdabb6893124e00ebda886893124e00edda776893124e00eeda666893124e00efc8b26893124e009fd8cb6093124e00efc9a26093124e00afd9ca2093124e00bfd1c12093124e009fd9cb1493124e00afd9ca1493124e00bed9c61493124e00bfd1c11493124e00efc9a28893124e00dfcabb8893124e00fbca888893124e00fdca778893124e00efc9a68893124e00feca668893124e00dfc9b58893124e00bfd2cc6053124e00dfd2bb6053124e00fbd0b86053124e00fbd2886053124e00fdd2776053124e00fed0c66053124e00fbd1866053124e00fed2666053124e00dfd1b56053124e00efd1a26053124e00fbd1826053124e00ffc2226053124e008ffacc6e92124e00cfda336e92124e008ff9cb6a12124e00cbf9baa212124e00cdf9ba9dd2124e00cef9ba9992124e008ff9cb6952124e00cfe9ba8892124e00aff2cc6852124e00cff2bb6852124e00cff1b86852124e00ebf2886852124e00edf2776852124e00eef2666852124e00efe0c26852124e00efe1626852124e00efe2226852124e00bfd2cc4c52124e00dfd2bb4c52124e00dfd1b84c52124e00 else 0xd229a44f489c11282230442088190fe21f243d087790ea21ca435486290b5214a4254842907520e041ac833106120a241048131016202240047fe0fec1fb83f307de0fac1f383e307be0f771ee43d5c79e0f211e0c3bac7680eb51d4a3a547428e751cca39807280e401c6038ac70d8e001be037546e28db51b3435fc6b78d5f1a9e34fc6978d1f1a1e33fc6778cdf199e32fc65d0caa191e31fc6378c6a18ca31546280c40187630d86130c21180c2fac5f30bd617a22f045d88b9616f62dac5a80b40164a2c2857d0aea15b42b285628aaa14dc294c5270a3e1446284c50189fe13f227a44e709be134626204b6895d129a24c8491091211ee237046b88d2116e2270446087110c2211841588050fea1f943e507ba0f3e1de43a407380e661c8c37e86e20da41ab034306600c5e18242f185bd0b2e15c42a5852509fe1364259849808fa118821e042107f60f281cc8373069a0c9c18082db05540a3c12f0238043a07dc0e301a002f404f808680008ff9c5aeda624e008ff9c2aeda624e00aef9c2185a624e00cfda336e97624e00aefacc69e6624e00ecfa7769e6624e00ecf87569e6624e00cefabb999a224e00ecfa77999a224e008ff9caaed8224e009fd9c3aed8224e00cfd8b36e98224e008ffacc6e98224e00cfda336e98224e008ff8cb6998224e00cef9ba9998224e00afeacc6898224e00cfeabb6898224e00edea776898224e00eeea666898224e00cefa666e88224e00cef9ba9997224e00ecf9a79997224e00cfda336e96224e00cdf9ba9dd6224e00ecfa776996224e00ebe9a86096224e008ff8cb69a2224e00eeea6668a2224e00afe9ca60a2224e00ebe9a860a2224e00afe9ca58a2224e00eee9a658a2224e00afeacc6a22224e00afe8cb6a22224e00ebe9a8a222224e00ede9a89de2224e00afeacc69a2224e00afe8cb69a2224e00ebea8869a2224e00edea7769a2224e00eee8b669a2224e00eeea6669a2224e00eee86169a2224e00afe9ca61a2224e00eee9a661a2224e00eee9a899a2224e00faea8899a2224e00eee9a799a2224e00fcea7799a2224e00afe9ca2d62224e008ff9c8aeda124e008ff9c5aeda124e008ff9c2aeda124e00cbf9b82e1a124e00adf9c72e1a124e008ff8cba21a124e00cbf8cba21a124e00cbfabba21a124e00ebf0c1a21a124e00cdf8b76dda124e008ff8cb61da124e00cdfabb9dda124e00e9fa889dda124e00eef0616d9a124e00cefabb999a124e00eafa88999a124e00ecfa77999a124e00cf79b52d5a124e00abf9c82c9a124e00adf9c72c9a124e00aef9c62c9a124e00af79c52c9a124e00cfe9b22c9a124e008ff8cb609a124e008ff9cb209a124e00aff1c1209a124e008ff8cb889a124e00cfe8cb889a124e00cfeabb889a124e00ebea88889a124e00edea77889a124e00)) else (if i<14 then (if i<13 then 0x6576a2ec45d52ba3973f2e6e5cbcb93971f2e2e5c3cb8396ff2dee5bbcb7396df2dae5b3cb6396bf2d795ae8b5656942d0d5a10b40d679acd859a6b30d6542ca35926b23963f2c7958e8b1bd62fac4f587eb0bd6152c1a582ab0416002bf057c0af415e02ba5572aade95b52b5a5694ad1559aab255640ac415802af055c0ab41565aac65582aaf155baaa7552eaa1d53baa6754aea91d5212a3d5470a8cd5172a295432a8254fca9e953b2a7254dca9a95332a6514c7a98a530aa6014bda97652e2a5b14b3a94c528ea509493a9225224a40947ea8f851e6a3b9474a8e451bea33d45fa8af5154a26944aa8905116a21943b287150d8a19d431285d50b0a14d42728495088a0d1417a82a504aa08140da81650229fd93f327d64fa29f053d8a7a14f229e313c3a7774ee49d893a927374e4e9c8938927024de49bb536926c24d7a9ae135426a34d3c9a6534a268f4d1499e933526654caa991531aa6254c2a98152faa5f04bc0976d2eb25c64b8296f12d625a74b2e96492c1257d4af095cd2b725694ac8957d2a7a54a4a8a9501292a5154a0a93a926d24bf495e927d247a47f48c8917d227a44a488a910121da420482090011f823e047a08f011d823a047208e011bda37646e28db11b3a357468e8d0919ea32d46248c0917922ed45ba8b6116422ad453a8a09139226244ba896111ea22243f887dd0f921e243a487090d921a2432486090b3a15742a485350a421384250846108420ed41a4830905920a241248209039206240a480dd013a017400e7fb0fee1fc13f627e84fc89f763ecc7d58fa31f2b3e367c2cf7d9eeb3db67b00f581ea03d2079d4f329e553c8a78d4f129e153bf477a8ef29de03b8a7700edd9db63b6276b0ec89d8c3ae275b0eb39d623aba7560ea41d383a66748ce8f1d193a1273e4e749cce39667260e441c6d38ba7134e241c43387c70b8e149c2438287010dfa1be437a86f10ddf9bba37546e68dbf9b6f36d46d94db01b5b36966cecd959b1b36166becd759ae635c26b70d6b9ac7356e6a9cd4b9a8734d86970d261a3c346e68c8d169a283446684ccfc19e833b06720ce199b33346664ccc1997332c664f4c911912320463c8c7118d2318462c8c51189d310461f4c311852306e609cc0b98072fd85f70be617bc2f585e9cbcb97872ed85d70ba617312e425c44b7b16d02d6a5a68b45167a2cbe593cb1f962f2c3e583caff95ef2bbe573cadf95af2b545694ac515852b005594ab0155b2aac5518a9b15262a165418a7594d029805294a45146f28be5110a1a142428284fe49f493d927924ee49d4939927124de49b4935926924cb898f130e25fc4b8c96992c325664a8c94f129925284a1093a126424a8493c91f923a24544894910121b241647c08f011d0239647188e091bc236e46c88d6919d231a45f48b6915 else 0x8a92f525aa4ad494a927524d649849159221242e47848eb91b7232e45848ab9137222e43dc86090a121024184820902120023f847e08fa11f023d847a08f211e023b847608ea11d0239847208e211c0237846e08d8b1ad635846ab8d4d1a5a348c68c8d0f1a0a33ec6788ce719ba334c6648cbf196a32ac63a8c55186a30546058beb17c22f045db8bad171a2db45a68b4316462c645878b0515f62b6c55d8a9b14f6296c51d8a1b1422281c4f389dd13a627244df89b5135626844cb898d130625e44b7896512b62544498891111e22344458887b10b6209440d87fb0fb61eec3d887a70f0e1d9c3a3873d0e3a1c4c37986e90d921aa434486690c9218fc30f85ff0bbe17542da85950aea155429a851509ea135426584ab091611ac225842b08160fac1e583ab07420e041b08357069a0d0c19c831905f20bbc17282db05a20ac4153829d052609cc134825f04aa092c10a81df037e067c0bf815f027e047c07f80f501d6022403f805f007e0023fe97fb2ff51fe7bfca7f8afed5fd83fab7f4cfe85fce3f977f24fe09fbebf787ee6fd8dfaf3f4e7e7cfce5f9a3f247e28fc11f7a3ee47da8fb11f5a3eaf7d54fa95f4abe857ceaf995f2abe457c6af895f0abe107c16f819f00bdfc7bd8f771eebbdc77b6ef69decbbd7c7aeef5c9eb6bd687ab0f521e9c3d1d7a1af3f5e7c3cf379dcf3a5e6cbcc97988f2fde5d3cb5794af255e42bc7578caf155e283c4b788cf0d9e133c16780cefd9df33bd67776eeaddcdbb8b76f6edaddadbb4b7676ecadd8dbb0b75f6ebd9d78bacb758cead9d533a96750ce9d9d333a56748ce8d9d133a217438e805cedb9d673a2e731cde39ac730ce5d9cadb956728ce4adc93390b720ce3adc7338d67176e281c48387570e0e1adc2db84b7076e0adc0db8167022e031bfe37ec6fcedf5dbe937c26f7adee1bd9b7ae6f3cde65bca37846efedde9bbab7656eaadd41ba0373b6e6cdcc5b9637116e02dbc5b7636dc6d98db1db5bb6a76d44da75b46b6886cf0d9cdb31b65e6c9cd8f9b1cb6296c48d87db0d36156c20d82db0336016bf8d7ddaf3b5d76b8ed6ddad3b5976b0ed609abeb56d6ad0d58daa435436a7cd4e5a9a352f6a54d495a90351b6a2cd419a7b34e669acd319a5b34a66942d271a4bb4926904d1c9a3134526884d0c9a0bb40767eecf9d9f133dd67b0cf4d9e733be6746ce4d9c1b37366dccda59b233546688cca598cb30965f2cba596cb2c96572caa594cb2896508c9d193232546488c8d191232146408c7d18f231d46388c6d18ccb18962f2c5a58acb1496272c4a588cb1146208c3fd877b0df619ec2fd85d30aa6134c22983d306a60cac155822b035604ac055808300b5fe0bfad7f32fe15fa2bf057d32f965ef6bdd97b8af615e8cbd05798af2c5e38bc5d7892f025dfabbe1779aee35dbcbb) else (if i<15 then 0x800780078035a170008070f000f000f000f0008070a150f000f000f000f006b42e001e001e001e00d6850003c0030003c0020000ad04a084b104a084050420e0010000d6834038009ad0780040000000015a09190f000f000f000f000900081ad07800780040000000015a09150f000f000f000f00090008000035a0f000b00e002e00107000822b852b8720862b862b8720852b87208400e019045c002b8b806411700c822083c005c03208b8064116410a570e410a570e41083800403840384110421af800a208720f0014410c410c41e002e001b0401c201c201c201c201c201c201c29043904295c3904390420c001c019045c0020182007000823784008881006be002097c0040c82104570c570f008ae20d7c005c003c00310b80078021617000b628b41c8210301e001070042c2e001902d8540965e00110408821e0110459043904200448086fe002e001097c0051be240b8005b145a0e410f000c828c418c41e001b45c00250800e001685c00310b2085316011448080c8882e001205032244441d480d4409482882a88100d510540380563196fe00d20ab92a2041510258b80544196f29026901e00c21a40f240782223c901e0888c360780dc08081e03702018780dc08061db8806e1af50d7c406bd435f101cf50d7c407c427a86b1d00cc6858776b31a161f003eb98c67d43588359f5106b3ea23ea1ac0c8cfa86b1500cc68586c0280700cc64a00f6b806632300ac70586f6ab1c161b00ac705861b17a86e1e00ac64586c0300700ac64e001b84c0300700ac64c00d8c8b0c38710106c0dc46461b03c06e23240d81b88c8c38762e20322d54fb165ce2056eb972b1f10234869d51320f006eb5d79ab57cafc5d89f75ceb5ababe6985c1ba10353ac797388629b2d355a68b4d0299dd32ba6374c5a988d301a5e34bb296e52d7a5634a8694e5297a50f49de933d257a47948de9195222a425480a8fed1eda3bb47628e451c3a37d46e68da51afa35546968d0519ba32d461a8c0d171a2d945728a6513ca26f449e88650fca1d9437286650c7a18542f6856d087a10541f6836d068a0c7417a827503ea05d407a8074ffe9f9b3ef67d6cf9d9f313e4e7c74f899f093dd27accf499e733ca678ccf099df33ba67674eb39d473a4e7474e7e9cc73922716ce1d9c1b37f66f14dd29b9b36f66d6cd9d9b3136226bc4d689ab135226a1cd339a5d34a66924d1f9a1f33fe677ccdf99b533566684cb5994b3256642cc8098e131826284c40986130ae60dcc16982330065fe4bf797e52fb65f44be397bd2f665ea4bc497692e925ca4b8f97152e165c04b7b96c12d1659acb25962b2c1657acae595ab2b42565cac695832af255bcab2955b2aa254c4a93951d29fa531ca5e949d28fa5174a29943328524fcc9f493df27aa4e7c9ca938b27024cd49 else (if i<16 then 0x89c005c00206021502000000e001e0016c51683c003168200012d07800520f001700085b0a410a5a0a410eda0f000eda0f000adc0836d052d0520876d0780060b07800403850b0780060b04090780060b06c17000f000f00080708540f0008540f0008380041c003c003c003c00204821db41e001db41db4102410eda0f000cdc0f000801c002d080004410c410844e0028821e001684007000f005b4207000816e040048210001c002000380078006b14d7e002e001e00100e140010241e00182c1e001e00100e102c102c1e00180018001e001e0010038001e17000c81502593800441001c00211380081c003c002f881c0020e001000110431043104337020e001002220622062207800622042470017000cc8e002e001e00100e10700080708380060b060b0780078004000001c003c003c003c003c003c003c00200000007000f000f000f000f000f000f000f000f0008000000000001c002e8800e0017440e001e0010000000005682104376820082100000082100000000000038004000000001160302e001e00101160f000900095a0801c0020e001022122c4404b04207b4122c15821011640427b410008b040000000200129010116091609160916091609160916080a4040022c100380041c0020e001000000000720200010026217000f000f008482e0010f1c005c00216c31682968310780080d68200001c002d8b80042d862d052d052d060c878007800780078004000000568256820035a0d00e0026b41e001070008380078006217000f0082c2e001e00100380216170002c2e001c40b0c00e001e001e001e0010301e001e001e0019041b02000380078007800780078041617000b62e0010b618b414b414b414b41e00142a1649c005c003c003c002c93800b80043a70017000f000f000841e00242a1e001e001649c005c003c003c003c003c002c03800b8007800780059241514000f000c000c440c440a440f000b42e0010038005a100000038005a1038035a10000000ad04a204056820035a0f0009000d00e002e00490485b8008ad078016f135a0f00080000a81000ad048c878007800780048004006b41e001601c005c00200001c003c003c003c003c0020603c00200001c003c003c003c003c002107800b800780078004000001c003c002d8b80042d862d041110296829682910296829103c00320161f0008824b414881e00100e14001e00100e140010700888207004882e001e001905c00318831883c0036893107800780043204111031103c02220a220531078004412620a44086be002030907800c0c70017000b4200e14001e00d685c003c003c00201c28003c003c0030003c0030003c002007000b420038006210000882188218821e0005840097c004907800b80078035a17000b42e0017c48543c01ad0b8007 else 0x7000f000f00080049024582007000f0008380041c000b0761a00080112031203000280029212208008881e001e00101000948080220400000000000022c1016f0838005800780041c003c00310b80078007800780040007000f000c813c60070008000e001e001e001e001e001e001e001902a04b270008070f000800000380078005b17000c5a0a5a0a5a0f000f00085b0f000882097c0049683b6820e001891b6851236d0aa4700101e0c480f000c48db42e00107000f000818083800780078007800403841c00200001b683b683b683c002000037f0017000c000c00082000780078005000500041c0020070008000000000038007800780078004000001c000b0b8005417000f000f000f000f000f000f000800000000003800400e001e0017440e001e001e00107000838001e10000e0018840003802da0903888188818881e00103c10881000247001001c002e881c003c003c002e881c003c003c0021078009010780078007800780078007800780078007800780078007800780040c078006000780078007800780078007800780078005b1700080002b4100000000000000001000ba2a001248122c1016f083800400e0016001e001005d08000014808180f000f0009000f000de20801c00200000000000000000008004a404a40480048004a414411620944bc4201000f0009000801c002c003c0020e0010700083800780078007800780041c003c003c0020e001e001e001e001e001e001e001e00107000f000f000f000f000f000f000f000f00083800780040000380078004000012204000700080000416832282d0645c003c003c003c003c003c003c002007000c816d0b101168316821ad7a8b8005a170008000014408000000000d810001c0020e001e001000f786ed0780060b060b060b07800780040000120f000f000dda0dda0f000dda09f509f5080000000c850b040f683c0030583c0020660b08000038007800780042270017000f000800007000c000800002000a000a440a000a440f000800082c182c182c1e001e001e001e001089c00485828583c0030583c00305830583c003c0030583c003c002007000de05860490182c1e00182c15ea182c1e0019ea1e001e0010038000017000ec0586000224062404227005de38901e0012040e001e0011040e00bbc40591c0040e001e001ac535f800b8004227001001c00305830583c003c00200008004a2040510202881000002b410010b0400070008540802a04000002a11917000f0008080078004055c256820070008380040f682002c17b41005408000000000001c003c003c003c003c003c003c0020070008001af8008000000000000e001e001e001e001e001e001030100000e001e001e001e001e001e001)))))
def minel10 : Packing := (1490,5,6,0,0,15,0,mined10)
def mined11 (i : Nat) : Nat := (if i<7 then (if i<3 then (if i<1 then 0x4c4928037f8d0a62494013fe6e83124a00bfd36418925005feabb48492803df54424249401bfa6992124a00fdd4cc90925005fe9b548492803fb52aa4249401ff28cd2124a00ffc26290925006fb9a4844928037f8d0c2249401ff84861124a00dfe35108925007bf288844928037f8d342249401fbc99a1124a00dfe34b08925007f7255844928037f8d1c2249401ff48ce1124a00ffc2a508925004ffabb6a0918035fcd451048c013feaeda724600d7f510d3923006dfa7769c918036fc3ab4e48c013fe6e98724600dbf34ec3923006df9a89dc91803cfd444ee48c013feaeda524600d7f510d2923006dfa77694918027fcdd30a48c013fe6e88524600bbf36e42923005ef9b621491802fdcda10a48c017f66cc8524600bfd36442923005ff1b1214918027fcdd2ea48c01bde6965524600def3512a923007b7a88954918037bcd3caa48c01f5e9de55246009ff576d1923006bfa8868c918036fd3bb4648c01bde955a3246009ff374c1923004ff9ba20c91802efcdb90648c017be6d88324600bef36a41923005fb9b420c91802ff4d910648c017fc6c483246009ff374b9923004ff9ba54c918027fcdd0a648c017fc6c45324600dfb34719923006fd9a88cc91803ded4446648c01bf669e3324600fbb4ef19923006fd9a58cc91803fad2ac6648c013feaeda224600d7f510d1123006dfa77688918037bd2ab4448c01bf68cda2246009ff374c1123006bf9a8608918027fcdd10448c013fe6e97224600dbf34eb9123004ff9ba548918037bcd2aa448c013fe6e85224600bdf36c29123005fb9b414891802ff8d88a448c013fe6e93224600dfb34699123004ff9ba0c891802dfcdc06448c0177e6dc3224600bdf36c19123005f79b50c891802fdcda06448c017fc6c43224600dfd34511123006fe9a888891803df54444448c01bfa69e2224600fbd4ef11123006fe9a588891803fb52ac4448c01bfa68e2224600ff946711123005ff2bb544918037f8d42a248c01efca215124600dfe34ea8923007df27754491803fb92aaa248c01ff48cd5124600fee2a4a8923007fe222544918027fd5db04004013feaed32002009ff37099001006fe9824c8008027fd5db0200401bf68cd8100200d7f304c0801006fea22604008027fd5daa200401bf68cd5100200dfe302a8801004ffabb4c4008027fcdc26200401afea2131002009ff36a98801006fd9324c4008037f51126200401bfc60531002009ff57690801004ff9b8484008035fd44242004013fe6d521002009ff36690801006fda33484008037f898a4200401bfc60e1100200dfe30508801006ff152844008037f899422004013eeaeda424a00d77510d2125006eba666909280379d2ab4849401be66923324a00df634908925006bea88888008037e919c2200401bf888a1100200 else (if i<2 then 0x13fe6e96224e00ddf34cb1127006fe9a2888938037f4d444449c01efaa222224e00dfd34f11127007dea77888938037f4d344449c01fba99a2224e009ff576d0927006bfa88684938036fd3bb4249c01bbe999a124e00dfd444d0927004ff9ba604938037f8d0b0249c013fe6e88124e00bbf36e40927005fd9b3204938027fcdd2e249c013fe6e96124e009ff374a8927004ff9ba14493802fecd98a249c017f6aed3124e00f7b51098927007dda774c4938037ecd326249c01fb69993124e00bfb36a98927006fd9a24c493803fe51126249c01ff46053124e009ff37490927006ff1a148493803fe898a4249c013fe6e82124e00b7f37010927005df9b708493802f7cdb04249c017de6d42124e00bfb36610927006ff1a184493803fe898c2249c01bfc6a21124e00f7e51108927006ff1a784493803ef93bc2249c01bfc69a1124e00fde4cd08927006ff1a584493803fb92ac2249c01ff454e1124e00dfe34508927007fe222844938027fd5db5049401afe6a28824a009ff576d3125006bfa886989280377c4334c49401bbe999a624a009ff374c3125006ef9a899892803d7d444cc494013feaeda524a00d7f510d2925006efa66694928027fcdd30a494013fe6e88524a00bbf36e42925005ef9b6214928037bcd290a494017ee6d08524a00bfb36642925005fe9b221492802ff8d890a494013fe6e96524a00ddf34cb2925006f79a5594928037bcd2caa49401bde6a25524a00f6f5112a925006f79a695492803f3d334aa49401bee2e1a424a00df7510d2125006fb986690928037dc5ab4849401bee615a424a00df710ad2125006fb965690928037dd2ab4849401bee2c5a424a009ff576d1925006bfa8868c9280377d3334649401bde955a324a009ff374c1925006bf9a860c928037dcd2306494013fe6e88324a00bbf36e41925005ef9b620c92802fbcda906494017ee6d08324a00bfd36441925005ff1b120c928027fcdd2c649401bbe6996324a00df7348b1925004ff9ba54c928037bcd2aa649401bee6915324a009ff37429925005fe9b214c928037ecd1c6649401bf66a23324a00f7b51119925006fd9a68cc92803f6d3346649401bf66963324a00feb4ab19925005feabb548928037f4d42a449401efaa215224a00fdd4cca9125007f6a5554892803fb4a9aa449401ff28cd5224a009ff576d0925006bfa886849280377d3334249401bde955a124a00dfb466d0925004ff9ba604928035fcd430249401bee6918124a009ff37440925005df9b720492802fdcda10249401bee6908124a00bfd36440925004ff9ba5849280377cd32c249401bee6916124a009ff374a8925006f79a5544928037dcd22a249401fda5495124a009ff37428925006fb9a414492802ff4d90a2494013fe6e93124a00df734898925006fd9a3 else 0x74c1123006ff9a860891803dfd4430448c01bfe69d8224600f7f30ec1123007dfa77608918037fcd2b0448c01fde9558224600dff346c1123007bf98360891803fed19b0448c01bfe6898224600bff36a41123006ff9a520891803fbd2a90448c017fe6cc8224600dff34641123007fda3320891802ffcdc2e448c01bfe6a17224600f7f510b9123006ff9a55c891803fbd2aae448c01bfe68d7224600fbf2e6b9123007fda335c891802ffd5daa448c01bfe6e95224600bff370a9123006ff9a854891803dfd442a448c017fe6dd5224600fbf16ea9123007dfa77548918037fcd2aa448c01fde5d55224600fef4aaa9123006ff9a354891803fbca9aa448c01ff68cd5224600dff344a9123007fe98254891803ff4b92a448c017fe6e05224600dff35029123007bfa8814891802ffcd98a448c01bfe68c5224600ffb46629123005ffabb4c8918037fcdd26448c017fe6e13224600dff35099123007bfa884c891802ffcdba6448c01bfe69d3224600fbf4ee99123005ff9b54c8918037fcd2a6448c01fde9553224600dff34699123007fd9734c891803fed19a6448c01bfe6893224600ffd30499123005ff9b80c8918037fcd406448c01efea203224600bff36a19123006ff9a50c891803fbd2a86448c01bfe6a22224600f7f51111123006ff9a588891803fbd2ac4448c01bfe68e2224600ffb46711123007fe98288891803ff4a944448c01ffa4ca2224600ffd17111123007fea8888891803ff4c3c4448c01ffa2d62224600ffd30b11123007fe88588891803ff4bac4448c01ffa9562224600ffd16711123007fe98388891803ff441c4448c01ffa5ce2224600ffd2a711123007fe85388891803ff519c4448c01ffc6e15124600ffe510a8923007ff1b754491803ff8c3aa248c01ffc6155124600ffe366a8923007ff18354491803ff841aa248c01ffc5cd5124600ffe2a6a8923007ff23354491803ff8d92a248c01ffc6095124600ffe104a8923007ff17254491803ff8a92a248c01ffc4c95124600ffe064a8923007ff222544918037fd5db0400401bfe6cd8200200dff362c1001006ff9b84c8008037fcdaa6400401bfe6c53200200dff36ac0801006ff9b3604008037fcd930200401bfe5498100200dff264c0801006ff9b3544008037fcd92a200401bfe6095100200dff264a8801006ffabb4c4008037fcdc26200401bfe6d53100200dff36498801006ff9824c4008037fca926200401bfe6e12100200dff36a90801006ff985484008037fcd9a4200401bfe60d2100200dff2a690801004ffabb6989380377d3334c49c01bbe185a624e009ff374bb127006ef9a799893803e7d3bccc49c013feaeda224e00dbf4eed1127006efa66688938027fcdd30449c01bfa6898224e009ff37441127004ff9ba5c8938036fcd3ae449c)) else (if i<5 then (if i<4 then 0x2803dfd4442249401bfe6961124a00fef4ab08925006ff9a384492803fed19c2249401ffa54a1124a00ffe30308925007ff15184492803ff898c2249401ffc2e21124a00ffe51108925007ff18684492803ff85ac2249401ffc6161124a00ffe10b08925007ff16584492803ff92ac2249401ffc2ce1124a00ffe30708925007ff08384492803ff8b1c2249401ffc54e1124a00ffe0a708925007ff233844928037fcdbb5048c01bfe6d5a824600dff366d4123006ff9b26a091803dfc59d1048c01efe2ca8824600dff510d3923005ffabb61c918037fcd430e48c01efea218724600fbf5113b923006ff9b8694918037fd4434a48c01bfe6dda524600dff30ed2923006ff975694918037fcd9b4a48c01bfe6c9a524600bff576c2923006ff9ba614918037fcd430a48c01efea218524600dff34ec2923007bf98761491803efd3bb0a48c01bfe6958524600bff36642923005ff9b221491802ffcdc2ea48c01bfe6a17524600f7f510ba923007df9875d4918037fcd44aa48c01efea225524600fef30b2a923007f78b895491803fbd444aa48c01fde61e5524600fef1672a923007f78b2954918037fd5db4648c01bfe6e1a324600dff170d1923006ffa8868c918037fcdbb4648c01bfe61da324600dff36ad1923006ff8b568c918037fcc2b4648c01bfe215a324600dff2ead1923006ffa5568c918037fcd934648c01bfe2c9a324600bff576c1923006ff9ba60c918037fcd430648c01efea218324600dff34ec1923007dfa7760c918037fcd2b0648c01fde9558324600dff346c1923005ff9b720c918037fcd390648c01f7e9dc8324600bff36a41923006ff9a520c91803fbd2a90648c017fe6c88324600bff576b9923005ff9b85cc918037fcd42e648c01efea217324600fbf30eb9923006ff9a55cc91803fbd2aae648c01bfe68d7324600bff576a9923006ff9ba54c91802ffcdc2a648c01bfe6a15324600f7f510a9923005ff9b754c918037fcd3aa648c01f7e9dd5324600dff34aa9923007f798554c91803fbd2aaa648c01bfe68d5324600ffb306a9923007fd97354c91802ffcdc0a648c01bfe6a05324600f7f51029923005ff9b214c918037fcd446648c01efea223324600dff34f19923007dfa778cc918037fcd2c6648c01fde9563324600ffb30719923007fd9738cc91803feca9c6648c01ff62e23324600ffb51119923007fd9878cc91803fec5ac6648c01ff66163324600ffb10b19923007fd9758cc91803fed2ac6648c01ff62ca3324600dff370d1123006ffa88688918037fcc3b4448c01bfe6d5a224600dff30ad1123006ff885688918037fcbab4448c01bfe955a224600dff366d1123006ff983688918037fc41b4448c01bfe5cda224600dff2a6d1123006ff853688918037fd19b4448c017feaed8224600dff3 else 0xe6d95324a00dff34ca9925007efa6654c928037fcd2aa649401fde6155324a00fef4aaa9925006ff9a354c92803fecc1aa6494017fe6e05324a00dff35029925007bfa8814c92802ffcdb0a649401bfe6985324a00fdf4cc29925005ff9b114c928037fcd446649401efea223324a00dff34d19925007efa668cc928037fcd2c6649401fde9563324a00ffb30719925007fd9638cc92803feca9c6649401ff6a223324a00ffb30d19925007fd8b58cc92803fecc2c6649401ff62163324a00ffb2cb19925007fda558cc92803fec58c6649401ffa6e15224a00ffd510a9125007fe9b654892803ff4c32a449401ffa6155224a00ffd2caa9125007fe9b354892803ff4c1aa449401ffa20d5224a00ffd2c6a9125007fe95354892803ff519aa449401ffa6c55224a00dff370d0925006ffa88684928037fcc334249401bfe6d5a124a00dff30ad0925006ff885684928037fcb2b4249401bfe955a124a00dff366d0925006ff983684928037fc41b4249401bfe58da124a00dff2a6d0925006ff853684928037fd19b42494017feaed8124a00dff374c0925006ff9a860492803dfd4430249401fbe2d98124a00f7f30cc0925007efa66604928037fcd2b0249401fde9558124a00dff346c0925007fda3360492803ff4a930249401bfe6858124a00bff36a40925006ff9a520492803fbd2a902494017fe6cc8124a00dff34640925007fda3320492803ff4a9102494017fe6e16124a00dff350b0925007bfa88584928037fcd2ac249401fde9556124a00dff346b0925007fda3358492803ff4a92c249401ffc6056124a00bff576a8925006ff9ba54492802ffcdc2a249401bfe6a15124a00f7f510a8925005ff9b6544928037fcd32a249401fbe9995124a00dff34aa8925007f796554492803fbd2aaa249401bfe68d5124a00ffb466a8925007fe9b254492803ff4a92a249401bfe6855124a00ffe302a8925005ff9b8144928037fcd40a249401efea205124a00bff36628925006ff9a314492803fed198a2494017feaed3124a00dff37498925005ff9b84c4928037fcd426249401efea213124a00bff36c98925006ff9a64c492803f7d33262494017fe6d53124a00dff34a98925007f7a554c4928037fcd1a6249401ff658d3124a00ffb46698925007fe9524c4928037fcd0a6249401ffc6053124a00bff37018925006ff9a80c492803dfd44062494017fe6d43124a00dff34a18925007f7a550c492803ff4a906249401ffa6e12124a00ffd51090925007fe98648492803ff4daa4249401ffa6152124a00ffd10a90925007fe96548492803ff52aa4249401ffa6cd2124a00ffd30690925007fe88348492803ff4b1a4249401ffa54d2124a00ffd0a690925007fea3348492803ff4c0a4249401ffa5452124a00ffd26290925006ff9a88449) else (if i<6 then 0x927007fd9764c493803fecdaa6249c01ff62d53124e00ffb2ea98927007fd9654c493803fecd926249c01ff62c93124e00ffb30498927007fd8824c493803fecb926249c01ff65893124e00ffb2a498927007fd8524c493803fed1126249c01ff66053124e00ffb2e298927007fd9514c493802ffd5da4249c01bfe6e92124e00bff37090927006ff9a848493803dfd4424249c017fe6dd2124e00dff34e90927007dfa7748493802ffcdb24249c01bfe6992124e00fdf4cc90927005ff9b5484938037fcd2a4249c01ff654d2124e00dff34490927007fe96248493803ff51124249c01bfe6852124e00ffe2e290927007fd93148493802ffcdc04249c01bfe6a02124e00f7f51010927005ff9b5084938037fcd284249c01ff654c2124e00dff35108927007bfa88844938037fcd3c2249c01f7e9de1124e00dff34b08927007fd953844938037fcd142249c01ffa88a1124e00ffe30308927007ff17184493803ff8a8c2249c01ffc4861124e00ffe17108927007ff28884493803ff8c3c2249c01ffc61a1124e00ffe2ed08927007ff18584493803ff842c2249c01ffc5d61124e00ffe2cb08927007ff25584493803ff8c142249c01ffc20a1124e00ffe2e508927007ff16284493803ff8a942249c01ffc14a1124e00ffe44508927006ffabb6a0928037fd4435049401bfe6d9a824a00dff30cd4125006ff9b56a0928037fc5ab5049401bfe215a824a00dff366d4125006ff8b36a0928037fc41b5049401bfe6c5a824a00dff162d4125006ff8816a092803dfc58d1049401bfe6e1a524a00dff510d2925006ff9b6694928037fcc334a49401bfe6cda524a00dff362d2925005ffabb614928037fcdd30a49401bfe6a18524a00f7f510c2925006ff9a661492803f7d3330a49401bfe6958524a00bff36642925005ff9b121492802ffd5daca494017fe6e16524a00dff350b2925007bfa8859492803f7cc32ca49401bfe6956524a00fef30ab2925006ff9a895492803dfd444aa49401bfe69a5524a00fdf4cd2a925007f798595492803fbcb2caa49401fdea225524a00fef30d2a925007f78b3954928037fcdc34649401bfea21a324a00dff36cd1925006ff98668c928037fcdab4649401bfe615a324a00dff10ad1925006ff96568c928037fd2ab4649401bfe6c5a324a00bff576c1925006ff9ba60c928037fcd430649401efea218324a00dff34cc1925007efa6660c928037fcd2b0649401fde9558324a00dff346c1925005ff9b520c928037fcd290649401fde9548324a00bff36241925005ffabb58c92802ffcdc2c649401bfe6a16324a00f7f510b1925007ef98658c928037fcd2ac649401fde9556324a00dff346b1925007fd98358c92802ffd5daa649401bfe6e95324a00bff370a9925006ff9a854c92803dfd442a6494017f else 0x6a183d181a17ed17c01775173e16fd16d0168f164e160d15c2158b15681545152c151314fa14e114c81491145a142d140013bf137e134712fc12c512841243121611d511b2115d111c10e510a41077105410270ff00faf0f960f730f500f370f000ed30eba0ea10e880e650e4c0e330e1a0df70db60d750d480d2f0ce40cad0c620c2b0c080bc70b9a0b590b2c0aff0ad20a9b0a640a2309ec09ab0960092908de089d085c081107c6078f0744070306ae0663062c05e105a00569052804e704a60465041003bb0370032502da028f026c023501f401b301900159011800cd0000dff16ad3127006ff8b2698938037fcdc34449c01bfe6d9a224e00dff2ecd1127006ff9b5688938037fcd8b4449c017feaed8224e00dff374c1127006ff9a660893803f7d3330449c01bfe6898224e00bff36241127006ff9a85c8938037fcd32e449c01fbe9997224e00bff576b1127005ff9b8588938037fcd42c449c017fe6dd6224e00dff34eb1127007dfa7758893803f7cbb2c449c01bfe6896224e00ffd304b1127006ff9a8888938037fcd344449c01fbe99a2224e00ffd30511127007fe96288893803ff54444449c01ffa61e2224e00ffd30d11127007fe97688893803ff45ac4449c01bfeaeda124e00dff370d0927006ff8b8684938037fd4434249c01bfe6dda124e00dff30ed0927006ff9b6684938037fcc334249c01bfe5d9a124e00dff36ad0927006ff8b5684938037fcd934249c01bfe2c9a124e00dff304d0927006ff882684938037fcb934249c01bfe589a124e00dff444d0927005ffabb604938037fcdd30249c01bfe6a18124e00f7f510c0927006ff9a760493803efd3bb0249c01fbe2d98124e00f7f30cc0927007efa66604938037fcd2b0249c01bfe6898124e00f7f304c0927007fea22604938037fcd0b0249c017fe6dc8124e00dff34e40927007dfa7720493802ffcda90249c01bfe6948124e00bff36440927006ff9a220493803ff51110249c017feaed7124e00bff370b8927006ff9a85c493803dfd442e249c01f7e61d7124e00dff34cb8927007df9765c493803f7d332e249c01bfe6957124e00dff344b8927007df9725c493803ff5112e249c01bfe6857124e00bff370b0927006ff9a858493803dfd442c249c017fe6dd6124e00dff34eb0927007dfa77584938037fcd2ac249c01bfe6896124e00fdf2c4b0927007fea2258493803ff8c0ac249c017feaed5124e00dff374a8927005ff9b6544938037fcd32a249c01fbe9995124e00ffb366a8927006ff9a254493803ff5112a249c01bfe6855124e00ffe302a8927007ff17154493802ffcd90a249c01bfe6885124e00ffd44428927007fdabb4c493803fecdc26249c01ff62e13124e00ffb51098927007fd9b74c493803fecc3a6249c01ff66d93124e00ffb30c98))) else (if i<10 then (if i<8 then 0x9c638d6374635b6338631f631062f762de62c562ac6293627a626162526239622061fd61da61c161a8618f616c6153613a6121610860e560cc60bd60a46081605e603b60185fff5fe65fc35fa05f875f6e5f4b5f325f0f5f005edd5ec45eb55e9c5e795e605e3d5e245df75dd45dbb5da25d895d705d4d5d205cfd5cda5cb75c9e5c855c6c5c495c1c5c035bea5bd15bb85b9f5b865b775b5e5b4f5b405b275b0e5aeb5adc5acd5aaa5a875a6e5a4b5a325a0559ec59d359ba5997597459475924590b58f258d958c0589358705843582057f357d057a3578a5771576257495726570d56ea56bd56a4568b567256595636561d560455eb55d255c355aa557d556455415528550554ec54d354ba54a15488546554425429541053f753d453bb53a25389536653395320530752ee52cb52b252a3528a5271524e522b521c51f951e051c751a45181514a5127510e50f550dc50cd50b4509b5082506950505037501e50054fec4fc94fa64f834f604f334f104eed4eca4ea74e8e4e754e484e254e024de94dd04dad4d8a4d674d444d2b4d084ce54ccc4ca94c904c634c404c274c0e4bf54bd24bc34baa4b874b6e4b4b4b1e4b054aec4ad34aba4a974a744a5b4a424a294a1049e349c049a7498e49754952492f491648f348da48b74894487b486248494826480347ea47d147b84795477c4763474a4731470e46f546e646cd46aa4687466e464b4632461945f645d345ba45a145884565454c4533451a44f744d444bb44a24475445c44394420440743ee43c1439e437b43444321430842e542a4428142544231421841ff41d241a54182415f4132411940ec40b5407e4047401a3fed3fa23f753f483f253ee43ead3e763e3f3e123ddb3dae3d773d543d133cd23ca53c8c3c413c0a3bb53b603b153ade3a893a523a1b39f839d539bc398f3962392b38f438d138a4386d38403827380e37eb37c8379b376e373736f636d336ba36a13688366f3656363d35f235cf3584354d350234cb3494347b343033f933cc338b3354331332c832a5326e324b322831fb31ba318d3160311530ca30893052302f300c2fe92fc62fa32f802f5d2f302ef92eb82e952e542e1d2ddc2da52d782d232cf62cd32c882c652c062bbb2ba22b752b342af32abc2a852a582a2b29fe29d129ae298b29682945292228f528be287d2846280527d827b5279c27832742270b26ca26892652261125f825d525a8257b2562253f251224e5249a2481244023ff23c8239b233c230f22e222bf229c227922562233220621cf218e2139211620fd20da20c1208a2053201c1fe51fcc1fb31f9a1f631f401f271f041ed71eaa1e871e3c1e231e0a1dbf1d881d651d4c1d0b1cd41c931c521c251bf81bd51bb21b671b3a1b171aea1ab31a721a3119fa19b919781941191e18f118c4189718 else (if i<9 then 0xcf101b8a0c8ce104c72e62061d175856639731030e23682b2e4c78818321b41997263c40c39c32a402b02cc72e62081ac44030155235a98f1042ea8c8dca9ec52e6207465485d42058e5cc40ebaa90ab8412e2c7881d75465480825c58f103fb53182c3403007d61698cb803b4faa3d0b4c664006bc03da85a6337b4b182c3803008791658cbabe91a0aeb31e206dd757d1153d8a5cc40ea2483802eb9ae2ea44eab5627bacd529eae17690102c72e621491879164914b9132910f90f690dd90c490ab909290799056904790248ff78fd48fa78f848f618f3e8f1b8f028edf8ec68ea38e808e5d8e3a8e178dfe8ddb8db88d958d728d598d408d278d0e8ceb8cdc8cc38cb48c918c648c558c3c8c2d8c0a8bfb8be28bbf8b9c8b838b608b478b1a8af78aca8aa78a8e8a758a5c8a398a1689fd89da89b78994896789448935891c890d88f488db88ae8881885e883b880e87eb87d287b9878c876987468723870a86e786c486a1867e865b8642861585f285d985c085a7858e857f855c85398520851184f884df84bc84a3848a847b846284498426840d83f483db83cc83bd83ae8395837c836d8354834583368327830482f582dc82c382aa829182788255823c8223820081e781d881b5819c81838160813d8124810180de80c580ac8093807a8057803e802f800c7fe97fd07fb77f947f717f627f497f307f0d7ef47ed17eb87ea97e9a7e817e687e4f7e367e277e187dff7ddc7db97d967d737d5a7d377d147cf17cd87cbf7ca67c837c607c3d7c247c0b7bf27bd97bca7bb17ba27b897b707b617b3e7b257b0c7af37ae47acb7ab27a8f7a767a537a3a7a2179fe79ef79cc79b3799079777954793b792c78ff78dc78b9788c78697850782d780a77f177ce77b5779c77837760773d7724770b76e876cf76ac7693767a76577634761175f875d575bc758f756c75497530751774fe74db74c2749f747c74637440741d740473d773b47391736e735573327319730a72f172e272c9729c72797260723d7224720b71e871cf71b6719d718e716b714871397120710770ee70cb70b2708f7076705d7044702b70086fe56fcc6fb36f9a6f776f5e6f456f226f096ef06ee16ec86eaf6e966e7d6e5a6e4b6e326e196df66ddd6dba6d976d886d6f6d566d336d1a6d0b6cf26cd96cb66c936c846c616c3e6c256bf86bd56bbc6ba36b8a6b676b446b216afe6ae56ac26ab36a9a6a816a686a4f6a366a1d69fa69d769b4699169786955693c692d691468fb68ec68d368ba68a1687e685b684268296810680167e867cf67c067a7678e6775675c6743672a671166f866df66c666b7669e668f667666536630661765fe65e565cc65a965906577655e6545652c6513650464f564dc64cd64be64af649664876478645f64506437641e640563f663dd63c463ab63 else 0x63203235886cc42631a000b62131906b1cf101b88800ed2e0e90ae21319c201b84804913a833884c66402199d415c426330b6360d01062051744458f10222d6d0d6095de0b600372c69058440446e21ea360223710ef0586e182d778dc33d4111b86100f0370c6e1e02018a96d43c3710761b86c057102dde2e882362c7881af545812b5c161bb0058d036620b18c191b840b032370c191b84320ec370338816f51ac6e58c1628ba20896b1e20512c451131058ca0a8dc20586e16203709001e202c426328f0100dc31b820102d884c6340202c4263220101621319045c42631dea3582425a2d010dc70446e1022370a00175195202058f103a01000f1886c65c40781b87880dc2801481e020c4163320100031886c65801191e02058f103201004048b621b19a004571058c80c8d1880ee41d7101dc636620370d009aa631c6109731038483662037106c1b919182a106203610415706fc406c28d6a9dc412e20ae19005d663b8b10d70d2e0e6376200c15001de638565cc40d3aca6f104b2e6206190781a020c40a320ee0c8cea1df100608750ef8803043a8770581821d43be200c10ea1df100608750ee0c8c77057101b08362b9880304801481b16306710570e804003a621ae157552110573101b0c359d5886b84190321ac209731032003bcc70ccb9881a75865e20965cc40d3a82c364c60ccb9881c641e06b0831028c83b82a3190151dc60a8ee205477102a3b887705443b82a211077083101b0a320f033041881464174150608699d40c03241cd1958c415701534008cac60aab988190080073c435c2c0039ad4b182aae6207801e21a310d70b000e6b182aae62068001646616c435c303039e203711001de6a8565cc40d01620370d001b275922630665cc410800e73502b2e62061b0671e020c40a320ee22082ae62061dc02c406e2620360dc318c6cc406e20c83c0da0ae20519018110415731030323708780646e182c0c8dc31b81910d83c0dc0ce2051904157310202a3708151b840a8dc21e0151b860a8dc20546e102a370807c406e1c00360d68aab9881900802635d710d70c80620360dc4c406e1400322ea3322aae6207402001b310d70aba8d80b2d4092b9881d0005868c435c2cb98803031b0181e0191731032010b4b9881057858181706cc40d0b1d52e6204970ea0601922000b4b98810411b018973102a00364012e6205060670827598f1030e9ad041880d0594c6ad682098f103091208df246c4bae20706468d8b101dcb3aaa70c8d1b14b9881c6b1dc4458e5cc40d208d70aac73ae206184731a26a9734e060e39c88a982b354b9881c7815e6a5d71028e324032376c52e620794c6b083629731030e3244c6b7c33b14b988203294c6e04b6297310388820cb8b1e2059d6489a81258e5cc40e244a637ec4bae2061ae411)) else (if i<12 then (if i<11 then 0x78a4106078048224000710d8f108ea0641818838048234000711ae038b001106f9109804882c015a9107800962c00681600258b005b75a1dc9806b43b8f00d687718d6806012d2c6512f00968720830258a4106060c60037888a24826c0241060780082244824c015a9047804822c02411600222892092410346b58c803c822f8c66904071e0033482b5124101c422e00a448241144852241c00a32005804a63c16199206e1e020282d240f08890111b3101e096d2d42fa903c041881c6e3b710d4c83a041880d0480b101a06ed4d5240f01062061b05d1a820c40a258ec2429188145dc40021cc682805880d83410441a048c406c28cc0ce203c104b54c44c40782a05880d03801481b068483103201004c6bae21a99900c406c1a09880d028006c5d56a01f0054cf003b42fe21a9945d193da1dc6b05648c410800eded0e92e4c729e2081afda9d5e20971094cf37c33244c61015009d46cf6a5c1ae53c4102d8c835841881548b68781231028c80f0e631907108063884021c420c406c25b4358403c10641d8630831028c83b832358405060ea080701013884a644007885a53c40b0b3c529e2041e02014a610081694f1018ba0162034021694f1020f00b4a788106c1d86d067102db4a40c82408988181654f1018d010086808043404021a02010d01008680804badae8c890a42c6101c5454c201c002ea32a42c6106207402001e310d4cb002d4a20f0a4041881e0078866c43532a32a42c6100f05d20201401f10f0a42c61062074020006310d4cb0022ca9e204800785a81ec415332010000f886a65174181a020c42633232a40f022241882c67c40781b870cca7884c63c14780806e18403c0dc31ac15c40782232a45b410620b198f51df10d8c838841880d64401ef920788831098cefac903bbb410621319eef1746c1a020c40c0b0882e8d60c94f5c406b19eb880d63bd46b06467a82c358cf5c406b19ea0c8d633d7101ac63302b880f041116315f101e0b778882d6216d2c66bbc191ac7002900c241882c66402001d310d8cb002903a223882c66801da18710d8cb3182cfa8244c006b0484b8586698df543b40b4c6fa91ea058121bde358240b0dd804c67059f51ac78042cfa8a8090d003cc6ed25f58581212ddc0646b382c370874083101a08804323c441884c6676a191e020c426332003a441884c651905d1ac20c40a25888b1e2041ac6e58c1620882e8d00b106c3d4161a087a82c340cf50586819ea0b0d033d4161a067a82c340c66067101e08222c6246203c16f51aeda19963058c330d83c0418816ef1ac4811163c40d7a8dcb182c4174191a063582c20546814008c89690620b1990080073c43632c008c8e688e20b19a0076a1657310d8cd000e690620b195008011985b10d8cd880d621ac63c4068042d884c6476a16c42 else 0x16108980094401c464600201c16100e185820c02c201c30b0700080e2f8b000bb4119807160014030010baed0845c004038445c004806002175da16001c00380182237007148822804311402100e19120210d6038a4480842580e291202160035885f07840c05440084228042513005bc62e8be0f0c180084a26002c000710be2e83c35101810048b0b0051040122c217c5d0786a260024582a222c2c025c1dc7804b83b8f00970771e012e0ee33bd1516003c0866c00321dc4326003b886d1483800941c016f1bb40c0818c006f18301191e20606f103020602f103021d041c007802b42c015c1dc720e002490661b30020d9801d439070012820c0b00060580030219041c006ad0d8355c44906e2c00632600750c611dc181c830c8941c0040c0322507005bc6a0bc5800d844541910300c8b001045803b42c00161600378b0008c8f10b000e0011d30010300b086c1a9e218301c003800820b0c71107001e00ad0b00570771c8380086419924c00920e002c001814838009411bc1518c83382a3800091930020cd0042a31d30016000c0b00060425e00219c41b8b0020c820e0031915a19ee22483716003190ef3230020c833dc431b241b8b0020c5710841c005800441c005802b43b8e41c00432083800c6449066c00920e002504181191800a41c004a08ae0a8cd7c005801d42063001600308a150831800877c015a120920c2a219b00024720c2a206300120720c2a2507001283800941c004a082a2507005bc6a0bc5800d190584a0e0024641613c5802d435051912820a880717c422e00378c641886678883300e21170012000c086c78866188a0c0807088b800b0001c4330c8f10c45c00481830111700120620e002c015a1600ae08831be41c0063304822600321700190e31c83800818c00520e002c002646002907001282038807c0050000e2c0202100f800a0001c580404210464c006320dd710e41b8b0018c80c5c43906e2c006c20c6325c43c006438c720dc5800c6b107001e00b10866c00435e01712b44906e2c00632083800f41c00520e002506e20607800d8718e41b88191e01710d633230014837160035046601c63be0021b30038c603e002803005687824003c432301f00100e0b0816864425883800f00088380084bc015a1c8380084119300189612600321241c00433600212f001483800941110151e00321c63904151282038877c0058000e280300568782401800f03c00071400038b0006042f8ee038e41c02441830038a41c0244182a038a41c02441a8320e003c00661283800b001144a0e00b78f001906619888c8941c0058000e21b3001986a0a322311151283800b0001c5800c8330d41c0048a85414545803b5208c41c02411c820c08183a86c18320c0a410605801af208d00c024118d8f108190605804822) else (if i<13 then 0x8b624600316c180787246002060380030292300129001030335f0016007508070c00038a00808401600240f0076858002c2c00c11600178826e045d76842ebb42c002806002c002ed070008058002c3c00280600238de210baed0b0078858002c21230030463b83c2120c11031240043120071600136848c00622e0029230010c824600301c24190724600216c48c0062283c2e8e48c00433e00211700109180094801c4b18ba0f08070a900100e31930038c622804212f0010838002c31c70085860c041805858002c21c700104724404219f000087244042060380044b01c52440421dc1e10cc010818080e1520021291802de3521e2c006a40ba0f0d481741e1a91800802c01161a90f16003175480786a40302c01481200038b00789481a902e83c3521e2c0078022c2520071600220844c00580045a7685800500c004806002c00280600220d00c005803b42c0044160013bd02160035886b1bdef1e0035885b7686b1e00358b001ac43a089800f000a89800ae39130016002f8ec39130012880c8d631af0010301186da16f0020b62260031845bb687225b5800ec416f003d4635db421db003d47800882b8e448645800be2b8e448644a26002184191289802de3511dac0063622c2c004b1097800de3c004b10b625bb43c004b109780084bc001618b625bb4312f0015c78009621c444c007802002513001204420e3804883c007617c7804882c006b1601220944c004b18960b0a00c006c1c003642c312c1615b42de00316c44c0062ddb42912dac007620b7801ea316c6bb687225b5800eda12c43b6007a8c44c005800444c005800644c004221de2de00417f0016c722600251300120664600291019128980096335f0010880b0848c0050b044416c161891800b6385820c02c2c004814890b0b0017c481c890b0b001ac481c890b09440584a202c2510161289802de3511dac0068c82c25130012320b094476b001a888c884b0585804c6358c44c005800d6276823583221acd7160035886bc00480600360dda08880c8b0035c5804c6358c0717c422e00378c5b17dda180e11170012000c085b17c1e188a0c0807088b800b0001c42d8be0f0c45c004818301c004811463b889800f005684a26016d0824b6b001dc7a260021741e1489800b00b686b1c896d600312f00b687225b5800f00b684a203c038c180e0036086c808403e00205807102d010b001b042d889800c5b172da1db43b43c316c5cb6876d43c216c4bb6876d43c2b6823b03c2110181600117f001031800a44c004220b7800c1e0605d1c8980094406042e83c2060380030291300103015101812880388d7c00403e002800071401010807c0040382c205a021089800b000e002f8b000c8980084416f0018bf800ba391300108980086bc0052260025101512c62e83c291 else 0x100c005b1e000b0b63c004b160025885b1b5da1e00340b0012c4246002c010016003b0b009204a4600258c0708c831dc4316c63122e2260171490317f0016eda20b624600316c5fb6862d891800c68090641e0034085bc00e31db4258b001d8f51e00388883c02da110724601220c44c01481a91800948c016f1e00320d03521dac00632600340cc44645800902c01da16000b0b000086f1e001191e2103c116c7507862d8daed03c4c002806002c003800040b0f000a00038863191e218be2d83c30080710ee246003c015a1291805b4389248b6b0018c833db4921248b6b001e9180085d0785246002c02da1dc625e016d0f003105245b5800d481bc1e18c8336003008164906420cf0b404306020b030201c20b00e285a0210cc24601711064120dac008320cd710e48c02e218c877e006090660785d18ba0f0a48078432032335c4419068b88632600718c64c006818c571085b1230018b62e5b431dada87862d891800c5b07ada1db50f085b17019b6882d8976d0c5b07856d43c21d81e10900c0b0))))
def minel11 : Packing := (1048,4,6,0,0,16,0,mined11)
def mined12 (i : Nat) : Nat := (if i<1 then 0xdc326610442b8901064dc33b8602c6610442b8701054dc3641dc304408c40dc70c9d4c7e20f14cf1104369ebe28807aa663a9a83dda299a22070018fb4688854cc750cf68c7e224082208f114c3d102003c5101054ca1924083b463881800757ac42c650c920ea203c18e206e4369ea1e8858ca7524083b46b31c40e00ed066216329d43220ed12cc7103803b4158858ca19ed1ae206329d432481018e206e3808c710371000208858c81931857c4772e440e003a9dfc510ae18ea483518c206c2e1ba20931ba8cce288570c7531857c4182e440e000cbaa215c29d43263f1054b9103803c41588570a7535054b86e8818006333442b8500061d45c88143248ab84691413a98e2093a866eb570f12e8253ad18e20b0cd5cc7480ad10ea77b117220b3a912eb480ad10306a2e4414750cdd4c757a214ec45c8828ea19bad5c2b4802914c65c882e01da0b18c975a0d8ad453b1d6a208bad5e9141ad18e2070810600578b9d627352998e4775abd2289622e442569db2cd8c2c0f5baabb5482a014b3a49d13e84d3e29e14e1e6752ff95dca4a48b20a8e346762a110c87ac2ea0c90448123f81f80f7c7b2bca9dcce9972ab88dbe2da46b035019e6caf643312d80ebde5daad7d67eafb56daa5d494a0f4e5a64128691a47422b50f682e3fe1ee0f0c7423881b78d346713241810b9257329c13d098447e22610447be3ad1ab8bbc50e2280e485842700eb0538003ff97624e00ffe60893803ff88224e00ffe5c893803ff96224e00ffe88893803ff98124e00ffe20493803ff97124e00ffe58493803ff95124e00ffe14493803ff92124e00ffe08493803ffa1124e00ffea2092803ff98624a00ffe61492803ff88524a00ffe59492803ffa5524a00ffe60c92803ff88324a00ffe58c92803ff95324a00ffe14c92803ffa3324a00ffe60492803ff88124a00ffe58492803ff95124a00ffe14492803ff93124a00ffe0c492803ffa1124a00ffea2091803ff98724600ffe61491803ff88524600ffe5d491803ffa5524600ffe60c91803ff88324600ffe5cc91803ff95324600ffe14c91803ffa3324600ffe60891803ff88224600ffe5c891803ff95224600ffe14891803ff93224600ffe0c891803ffa2224600bfe69893803efa6624e00bfe68893803fea2224e00bfe68493803fd93124e00ffc84493802ff9a824a00efea2092802ff9a624a00fbe99892802ff9a524a00fde95492802ff9a324a00ff68cc92803fe95224a00bfe68492803fe92124a00ffc84492802ff9a824600efea2091802ff9a724600f7e9dc91802ff9a524600fde95491802ff9a324600ff68cc91802ff9a224600ffa88891803ff15124600bfe60800802ff93200200bfe60400802ff95100200bfe4c400802ff92100200bee69092802fda3300200bfa88800802ff21100200 else 0x48883683d53769832ef71b702b10a99c2b107a9a08e20ac40d047a878baea88055b5534064e2482208220683b68327860b8dea158854d216388806647538deb100ab8aa686d54c40338b11b8ea0ac42a670abaa90202064e2dc7185601533858d0201864e2483452040635910ead333442c6f54368881e883d6c667792c881937442c67083d4326b23d4bad33181db510b1a1ea4b22370326b33bcd6440a9ba21633841ea163411ea5d0c98c0eda8858d0f5220642a6e8858ce163589ea6b223702c683368d6443c3bc2a6e8858d2ef089b86da101b86f525910326e8858ce100c9b86f5359102a6e8858ce163709ea6b25910226e332030753304620773b20c81822b884110ae2190770c9984110ae1c04ea3b8643057100a215c7515907722972b8ea0c8610770c058cc2088570e020a9dc6643b8608ae210442b883b8642c6610442b87ae3a82a1821dc3041375702a6641dc306610442b87011de206e238805103711c4c8361)
def minel12 : Packing := (95,3,6,0,0,13,0,mined12)
def mined13 (i : Nat) : Nat := 0xe2da105326d08318f8841706006a2e264638eaae908882c4b420eaf927500ffc49c01ff892803ff123003fe00200
def minel13 : Packing := (4,2,6,0,0,8,0,mined13)
def hashminel10 (i : Nat) : Nat := 0x3817a00800360001cc040d900000001c270000a054000200d5043000000028103802602c0000000000060a00000000000050420001024d0173070a112c09a0546076000100c7819c06a001541208320001c1000000855a09f4013013580a106e000200180008020e07c4238000b0294200000000010980000412d82e30940001c11e0d120a60000000700cb073815f813d8d84201001e018b80e00018136425800000000000803384200000000000280f000040b782d0000a08a000300e8000f060000000048330000000341640150001c0a6400b800307ee02c0000000b0a5c0d008df848d1032166415f041b0ac00000006036801340ea41f604600000003c090000a0394161428f8d0f044e0a241ed00db022000141e501e000003030200000600031e00000102010002070107000300120201030b01010500
def hashminel11 (i : Nat) : Nat := (if i<3 then (if i<1 then 0x206a0582a57010de0212401100000f0814202f40000780e9a01fd4086d81b0c8d487048c00000000078499b015584950c2109048140733e213000001850b919472059000ebe00fc608242086800006882e0197380d4cc011f082940affe125502bea8451e042b607284049104cc0070dc0a3b2c6bf0531a01fba10144145f83d5c0713e026fc23a20505a01ee206bec22dc81471064f80e5d8040e8223f08a46099e4663303bb5007580169014f2302e1058a20ee5828d3003300200000300600600000c01a00100200300000102700000000100000400e00200001c03b01102300200100200000301100a00206c00e00700001200100b00601300000100000100000700300a00600100501000200a00000503900401400002d01300100000100100100200600001100200200100200d00200001000700100e00600002801800801100501200000000100000000000300000a00f00000500001301200900200600000900200d00900000002300200000700400000000000800000c01300000500400800300600100000000002b00401000b00000800000f00000001500000400000000800400800700404000000600000400300300400000003600000104006000301d00100600e02900400000302c00200902100000100100b01002400100801000200200801301300000200100500800000401400200600200300500000001801700800409201e00500200200700000100c00100400200000e04101700200b00400000300200100400000700101500b00000100000500300e00000500301b00000000d03100200100200300000100200400000000202b00003300100000101300002000100300600c00100000000100300200b02a00100700300a00f00701700200101600000000200000000000700202600301c00f00000200400400102a0080010000050080e500f01900001100600000300000400000000000700000401300000800004700407206c00000000201301300600200001100f00600400000000001100000000500000200800200000c00a00000000101a00000000400000200f03300400100100800100100301100800800000301300a00001d00c00000800200700300002400200f00301d01500801300100500300000500300600106300500000000200100300300e00000200300000400800100000d00600a00100200300300300100000500000000300500c00301e01000100500100100000000101a01800200700600b00300400100f00001700900001600100400400500000500000000001b00000007300000f00500102600800c00200100000100000001300000500000c00100800200000400f06700101200c00300000004301800400400100100a00d02000300400900005b0010e401f00900600400300a00d015005004007005 else (if i<2 then 0x610467a041b23694c0c02043ea03960010fc06640250c1b54c02b00247880631011800d778192c819d802c4a127301c24843da007aa0f5f40ab70157a0a8dc01511632684712b09c20579c0c1a837200729e063ac24b1855f00b8da0fc280ec105c96008b4136d4027900e4c00b06a007c13570cbf7024a620afc0eea82ce91b5320c62c09890333f031300509c09a901fd703980004142b880051d09590170241ed80071801c3c09c0c1dbb03a040a6800e6c82840059eb0073c0220024d2819800b0ea344280b5b0d17e0662c0821027548288c08348080f00a7f00dcd00c900b454151c85338038b4108f01eca048a10116236de4274500d35033e8070400006858d907de0000002445811c701af802bd841d500cf50078e025e464b6845fa072b602cb8060984d4100dde11cec010703598044ee039542268000030854c352a427488dcb901d5602d8c06f982b1e02df40ba3c43888181000eaa00ee40945805d270c2e2124c0294827f20aafa131980d0b853b306de00f1c02b9c01a3008c7e05ef01e0682539081e63296805280217507004036181b6e043350157a37368154304cad10a460d231cbe4012f3017ea09f282918828c209cd4172dc0a9a8539d0370c045b00c8102fb805e34142a4261f83df009c0e1080c1e58a0cee0549e02c2c1e2b84cef04bcc0ea202901044be00f5a077dc11c88cd1306d120271c12000d86c024fa0caf8168680609046a40dd741e720122c036980462c08ba825d90ac44039f81b9a84a4000f080389411a4832a21a1a80f0d44348006d50817a0bbf424be402e203a2e06ee81b5e84b06081241003c1e5383ada097da0fad0097481a700000000020662700a6e0861c101100ae30c8810ad56350ec138a0483d005b0363800001019a9073d4133701a5a01f20000040156c6d18026b000006324e0116a8406909b9e16c800d270d2a4063ac0fc741b0000001038720544c2a46014400000606c0c0066848e906bc2167000003057a0029700cd2c14eb02c160a376032c01480000000000000028087e018d90099e03d9c14ad055dd074f403d2c6c7f81237025be07d2c0378000060213e0966c0c380000900e8c0ca08234b026f30717a11c181ac6818bb09094349d01990000010747e05c1028b981e040aef20354c06f2041370599c04fb022400540c079320f21423320d32d01b581039004380000c0b9e40fee6018d83ea408a600000000028dbf00487403a0427ed833c000000000042bd881a800000c029dc0dfa82680000000002024f084257085800003023d0000000001c11ac000000000b02e72117b86900000011aac812758051800003064200003402fa843b00001016cc000050d75402dd20d9501d2e82f0e044a20b90811b68cb850092a111641773032e108db405f5c04b3023db09200000 else 0x900600000340a68000000000014a2c2c5000007078c00000000000000b0048e3567c1dc3021490295032c002ac80000505d40000281be80000e063e000000000100dd30564c03ee8223a85c5404c7e0046c2498000030a640000342c9000003021d412a400007839d0000000000000000000e06be0000342e40102d70976000020191f84fe70a5fc12c800000826ee09360000042780000000000810d0000000000b04e581040000040120904c400000804ca88319071a00000000000000304fb810f14278b8dc9000012029186e0501deb08c00000000000837a600b72056a02e5008332052e000034129303d000001615680000703694199800003c2208000060082c07bf809e0000000001a095c812e00000d02f5c20bc0000704a500000a0d68c237f801520aa8a0c1181d140c91905354128ec0e0504af606a9a0c200000505ad005bac09a4819780000bb04f2079ac1a90000050622232ce843160196c088ce32f081d828065e04f00000146bb70561a0604c32b9400680000f1b842121d4271182f50000140ed940f088419b04fcc136800005054b100718020000003020ff0ab600000c1220000000000000000000502d5c03f600003423f0000000001c0e98c2b6f80ae00001209358280684d700001a08880000505bf208ea414f7009548079000000000300ba68095e19560000380148833d004a2806c7c11300000c0032e05da40a0b8388e0b4020eb800003402a002c0412b4827b7057500b7800001412c50cbe800244009a419f8000000001a0c83418e700b8b1003c10ea812a40435b0166700b181321813f1053e0000000000000050a4a0000041e788322000000000001f3c848b00000000000000381ee7006b208c9416cc02c300001e0feb46a92043130106008dc0181b828ad0485b410c0000582b390b702039a015ab036ea085c000036015fc032c409daee49c22c6840270950236c1c007b0229905e98330081dff00d6406332141800001800ec0a7cc14bb410508422608518116ac070782b43058d0110a8657e039aa0612040ac4293d082d6009c00001809ec823a00000000038046a856c00000a32d78277985a1806b880f7b010e083f860a75a10544130e80c010533806d4022673341309b360ef140ca0851e10b8f6072000000000020b28834a400002038110aaa2143fc051502bee045760417c0e860462f0783006af8066b01398040f4038f0281a80c9000000000106d0581d3f0818c01a9c029b8393207eac2182809268db9801768073b82c9a01c900001a12fcc1c3b8356e07e600001418280000a06020000082c480000d0aec00000c1a2d854410870e015bc22180000c026e6114240ac9d02a909cf0018ac20080000c041c401ca464e80000e061ee368941f1500934021be0cef4217d80ba200946036cc0f)) else (if i<4 then 0x1a140b2b02430020b707cca0d10c1e61844ef034ac0b1f8042b046400010809dca4f3d02e1c02e5409dbc1556847920ae14058da11cc02e000001e01a642b2484bd3000160fb4000070279c030880b084225282565195b2053a00758816600001804060157b03e400001804eb41678000000000c0826069cd023ec091a00278016030414d07e480b9c00001c030e02d800001c6d680000d404e00001c295481710000000002426f8000000000832c400000000000000e1090000000000000000000202db800002080e00000828c182ff20419e078b864a60005b04632173800d4e84c1a1b5de16e5405400000c0a5661539c6c9304c400b0d606b0010f582bc60864e0282c100e003ea0a0561285a013d858c7057720468420f701f900000a0cda800ec85ab000014057e82b380000d085be0b94000000000006f240a10829c2851480725814f341b380000e07ba0000201697814c1003f0321c0153000003028c00000c21b800002000c402424419280b70000180eb000006818200af1e0c7ac19f000001052c003c0826ee810b00001f00b44813600c3000ec00dffc0d9902180000000000000048002f0a49820eec01bb0178506aea047f00eaf815800b83c085b81d9b0584b096cc159441c1982aeb00e060318c165801ffe052960d8980230002bc00d6208cc42d22013000000c02d400670000000000000024413403646082c000000000104c7b04da605f0000000000d0008601a1022780000904404067241229102750969e0f86027900000e068e0000341625849f304e7034ecc20d8004db02fc80fb800000000000000c097e8156e0543f0962e156340ee081c49004ec08c240b2d02ab207142151781e9402df109c6c13580196a058e901dc00b27815cb04b3a0a614132c40b3e8480000000000000001800700000c32a4065b800003005400003881558d3cc03796147000001821100000000000000000004069dc035301f0202bde0560e05a4026900d8100000ab658c18a80000d0a4c0000280d6d027b90451804ef81bf38580f079b01621c18bc811e30b9a00001813d40cb2d03c6c0274000000000000000000380aae81cf000000000000000000001b9800000014e184c50000000002c0018000010163e13e4429600000e05f920102412d800001047e00000000068d3e000012007b8268c04f4c02922023f01b6780250033de13b4000028249b00cce14fc00000000010970802f041c610152b00fb60cdc0000003e8b0433c0e6241d7985a9604d940e14000000000b09ea60cc0819600000000000020b823da85d150b6c4071cc1fe00000000002c19181eb00000f0470c0c90000000000004e9e105ec06280000701120000080d7182dc00000a11fc000078494402eb6050c00001856e6018ee0cea428b3029b000004167c0000000 else (if i<5 then 0x184000058378009558074a404f90d2c70a84e147c0000580c8a036ce0e098660b04c80000060ea400000000000000000000000302f700000813fe40c9000000000000003c2d2f03c2b037ba1387415080000d0b3000002816f40346c08f9814130264f01cd2081a00001403380000970600000382af4002e409d600001423628cd4c026d2154a027dd8370909800000300d100000000000000000002033900000000000000784400000061155c110a80b980096e01fe40b0885a8606c600000000000000e040c000000000000f8c0aa28329ec0f4304a7e073880b5342a380000f1b7160575415bc83d8405c7a109d401a4028651924c115f0125f030d204480000342d7d83fe60a9f820e3418a4837190905e16b84661f013490408c06544154c8044002900000141a6282d7800ae000000000584720000000001822cd82dac0a03c0beb403f6055cf08d00000000006850eb0a44e119506da00000d03d461730c2dd9a075000002044f0289d81db106b7806eac91f800009003940f9501aa8855680b62e00fc40fe48cb6f05a7c08090068e050700001a0d44c082302fd209f480ae3c6d9a30382060d416430005002989003440e3a0004b0cbb30b3200003c2e200000b4001015400000402ba205ed20d26806ce858260a6a6168800000050cf0267401b0000028013d006c0000100f58000030a2be3238c21c800001002d20bb000000000000000400a0816c383c4c02220069b02b4581d9503eb20c02c061000003024c000024143d805080031805dec10060343d0058a02600261603ba9064d603480000505c3f03ec00000818518d47806842128b022b2813210634a068086a89811b90482000000000000000000080840815380000d017d8095400005034a00000000020125000009068000ab3c0b6b042b30084801200000000007061600001c1271903100000c063c000000000403da40c6d01bdd82e61021440e90427b9850900001e0a368148d0cc2802d061655025d0000000000206a800005840300001003fec20ff8ca6601530102282cd3042900001408148288f012ba08d400633423be03dad0aa6e0e45c2e83857cf10d9215c9025e204b5f030c80ffdc0189028f10b6a40fe4008300caca09574160f466500000c1b480000380f880000000018066400000000000000c14400000383760038c00001418950d96e005ec15994005c8cc56060f606e542dea81e7909bc80d98c0a808549119336070b40ea18597306e8e12320272b8260f05fd613b800000805e80003212600000280ca00000414b441238057900000813914664983ab00b4cc08b8800da01d60000121675823b2817ff0754607a4000030521c0b580158000002054ca0258e0d05c0b5283b2219500005c4289585b0c200200002821fd02ede03e6000000000001f8a0 else 0x5804762052211bbc267a284160a3be0a88c1be785ba705d2a01dc80860000000000c0484443088154c08ba61534017cb0d28101f501528019c00000f0b4e00003c077d8179205b600dab0248c8129c0540803b4000058cc7b05c400002c18b40292f07ec807680000000005a06960fd0c0c9f8411d09252023800004010300940808bd423e8000040512e056f413360454e408dc0a0b00897856b30479807dcc0a0500a1e1968801ef415b00000709d921617425bd8094c037d6325681090041d603f5a0408000018110000e6e0b35007ac03d19095ce08b081bb901e50000160ca5c14190591000000000210269825a2028a000028076282f25069a0000301d0982810000000000000010569a01892163c0000404856086d80ff54644b8426009120000181df00d2460499e04010132903ec00322e32900149b8390e059000001c28cd84fc000000005000000000000001e092281daa8213200b80000001f1e018a509a620afe02ba0000070762000028083800000000181606802cd8114601e7803c80000002eb90211a02698019682d6f062700bccc0568884d507a960621023c7857ee076801072c420800000000000003827c1058b20a6c6c0c2c0f230185e077a6111000000000000000000000000000009073f60456c230901b20000000001022e7021fb069e00000000000000d0a5340c32c279d021d507b9100a286a8305a300001202d3c11d900f1c8053401f3020c381b780b55a0cd586a490ca0d0336235e642cb0000060122e3271417c00000b0a1b6170a01fb8000000000a150601872008ac04540000000003002100001a0fa40000004d5a071e00003c2b1a011de049e00003029b88138803fc2129982df3811980adfa40b8864d80000403e00000101a86827541af4a0f4f0188684d8e0b68c12e7c1cb00000b1a220000000007859b20500e03e40000781970000000a178224984d000001e)))
def hashminel12 (i : Nat) : Nat := (if i<2 then (if i<1 then 0x6a4097401c356002e0060c19d78b960000060acc009de03711035822ec045e2603389a498e05f901a0e801c6079f40e5c806dd82efb0794803424173102b0d074340fffc079e82f5000014056104102833571746a0edc0000080b03125e2064881b9c0049c16b340259c10c282300039fe048dc04180000c05e0a03ad804c883c09069f8016d806f7030a4070c40c94408f0000e00000000000188000001075400000007f00000c059b408fec1fe8812b817a5c0d8381ac903ded00040080180000a0100000000603400002004028000000060100280800200002030002000000010000cc0100002002000000000008000000000000280001401c018000000000180100001c0100000800000002008000000020040000000000000c000010000540080000c000000000000040680000e008008000000600480301c00008807000000000040020000000300e0000680e000010058010000000000605c000000030080040200201c00400800000008010040000000000000002801008002000008000000340000200203401006004004030010140000000900403400000000000000010160080080b002000000000060000380200e0080000200001800003002030040010040300300000e0280400001409c00802000000000170000000080e028000010000000000300500000c0c8000020000d8000000240000300a01801809000004000000000000000600a0000100000a0080080500002000000006010010010000000000001c01c0300000000400803008008068030000100081000800000000004008000000000040800101200801000000000050060000140003a0000000300006200800000006038000000000080200000c0000500000601c01800000000008020020040000000002c000050000780000101c0000000300e01c03005016004008000000000000200001400000000004010010000100080200a000008050020000100003a03c0001100e0080000100c0000580200001001006000014000000000300380205c0040300100c02812804002004018000020040000300001801804010010000000060000900302200400001000020000090000200000f004004018030000140180000000c0380500000001802000000040030040040000e0100200080a0000000280000401007801000000000000140000080300000001000000008010000320000100000a000000010060080001700a000000040020440180f00c0140080000800000003006010000050060040481702600000004018018000040100040180000600001003016000000030140100000101202403000008010008000020000380000e00413000014028000060000000200b00803c018030000180000001800404000000000000110000080580300c0040003700400001000 else 0x281020000082ea08143300b28057e20f7f81af2024f4004ca0135c0b3e81d700000a043ac08f800000000000000417a6813d202186063c00004816e0000000001c0a38000000000000000000000000000120fa1802d7026bc019800000000068312407986058540a1000000000000754019bf812a00001a07f805d92030f8029a02e024063800001002dc01c845ae90032000014018940fd903feb032000f9a06030000000001e0cb701fad83b9c057020e66c16d40019217902090bc5ba70033f03cf20fd040fe18395f0404a069241d9a01031035a2078000003826a8026400cfa01f18029de17f103039416a3820dd035cc099e41d6d8304901c802ef701cee8078704e162ef185e9883f3903de60e7e80770000000000a0add405580bdf00001809b18090803ae7177c0000386060000020329c08758032683d1b04c38045f820aa0157b05d8ae00540399094320744e2f8101a6c0155705ae0000000006037d000000000181e58000000000000038163000000000080f9cc5b760b9fa067800001c1f7d033930629c2e1cc0a5a005d306fe2086e81a90000040270a04df41606019300155a05cbc014a03a4407d382f5cc5e49004e90241e029b84ad880efa05be00000c0078000000001c053000001028450636000000083a0254a075e40b3c45f6183307010a210260408b0276a02d260f06006f88075e17ff8057341a298041106b942f28c09b48262d00d9c005fc0d1800cb4017200a17418f800000000000002408c08264502c04067c0000000000000120d5f8606d301ca00bf40db00000503c31049920490c05b48068303ec00000000000000000000000000007803cc120f60d28000028171406f300d9441b6f8319e06a882da60107702dcf175380e9bc048989083028d40ae445d7381d0901f162ec50108783db3180222dc4014dc02bd3025e6065700a9081d2f028120b2d81def0b614011ee08f74157c8061a03c8a0d76016420145f032ec0337814e18065107ac4063680d15824b21235409cb54089825a2067ae2d8881404022ed017d204c40000203a0700e92078e0023d8378404da0000201ec681b6a0378a253cc409180f200001209fc0000000000000000639408de011ce02ada08a500db88356604a1e049cc194e0819d01172102d817488023c005400003004d38141a0616a033c000000000e070f2074581cb383ac000000000385dc80000901ce928adc07a1023cc010dc2f6600a22038a505d00000340c63823600000e02f0000000bc6505f7a09350154f0b5ff01f60000381c8a80fa60445c0f35415af03fa503778086680ee781eb805a382fdb40f0d0231e029d401da81be38256516bd20bac0000700a700000e0c6b81cc180dc5080000001419790283104c60000141e77033f50353201c000f64894400001c) else (if i<3 then 0x4802200000c0302c0e35093e0000000000000010215304ca409e9860518089000014045041f90000061254a02ee81b1f8191805bb8066cc19398057e042c00002801a6820f60585a07f4000030bfbb05f0a0aaf85d678b72901b5e06bd019b000000000180400403500000000010019f012e183eb7171760be580ba00000404e600000813a901c1616e60000380884ab4900000409f6414ce80870000000003404c00000901fb800a2c12dc0375a057d200b40000700fc1070200000408208059b04d20023a418b781c4a030a0000080eea02e400000000000000612602000a00001c40520bdd703356019b4071e00b72047da0b7b80f97825e6080ca04b204064015d0033a2010b41d8601bf217360000001b3600b3b00018005081008004a8080860bce80297100b417740089685b210bd08012600003009d00000105a62095f40dea018440641a004c005a380ac803bec014cc03d301c8e07e0800b081628d977f04b20000000004822c000000000280ea681532051300f128005281630000000000c158800000000000b4840be00383c0121a056fc1cf00000902e6e0adbc1b7800000000000000000068bcb00001a0bc400000000000001c0c1c000028179d02bce102a85c08000080454000014040083ee500d2401dc00e3ed97f517b680b5540c0c8b75a003760bf8c0e118224e00f380e9d0054683ed0061ac0796005c080d31026020817c1a6503c8d07cac04660498b0134a05c4a022241057823710074c0118c49a983a8004228025440fd002a0b030cc0f67c01748bad6059c000010168100217078b02e7880fa0000000001205900000581981003e0000040d368025c02dba0bdc00004009f0000000000000048936306b0e85f24042683dcb0408a0e8c040720203e057660912801be81d3205d40241601df983770000000003003e60389b067600002014880000d060000000000000000903b323011880068b6f000000000000000000070393000acc0e5a819ef00c72069f840850243a03e3606d0c0fb8000020024000000000303fb70515a07cdc09f700c530395402c500b470385505e56249941ed483f8317de80ed1c01c80309b06c46028840188808a6000740c88c1e86893b403f20000000000000000001a0830000000000d081980027c1573001000001003c00602800000000100d10c1e4f00aff05fa00318803f18128a06c24081b00bae0951e06b6006ac418378311d08228042e81b9482fa00000000000000783470000000000000000000000002099981543834bb0060603538069281f0005fee060380fc60333c00a0c0e94000000000e06c80000000000000000001a2d72810f8029a5054200b0e41840081b000bd80bb900a888251516cc203090074181487056500e4b014bd01aaf00718029301a3680e60000000000 else (if i<4 then 0xbb07c800000804e60417c071c00000c1cd80000b022ca09c4c1c9d0101102f6000000000000002075200003419638414b044c000000000583f680516c04a485c13038b20124e0c0c00e7400e9f06f5203a800bd18165500fbe009c8d156038c30492607168494b01e6d053180a97c1ea782fc100f640ef3c1bf2008df030e40279c084083011020c62dc08209f836b402de405df806bd800cd123740e09c0039832430519e094b4103b00153027fb40440000000007016b0089d420128b8e000000000301653039a2025a4015300500029e507a48070241277013cd008b80ab3c5fb80b60f04f9a04288191e0412e0491602968111b825850292e0b60812af01ea700c0c0e3ec0e690245b0412c05d98151a81dba0763a043500bc7837411776606d48605c0380c03678202f81f0f82f6c027282eae018bf8043e048e60a998193182790000100b8f4041083f9403b580fa845ef383bb0000180d68000028196e02ff00323c40c4840700000a00fe80ce22015f1201a0e100000280f9d077de01c50164f8367a00fe809ed0092c0bfe717cc00c4cc0671810f00001c068181908028d0000000002c1a4e022f00000e062400000000060410e041540768000030002000000000600dd0000060870000000000f01c400cd3c5f8f803df173420905c166781b97063c80e41c5d550143c0464210580000682c79068080a1cc01f30b63a03acc0db80000401d80000000002c076000000000000000000000000d04bbc00bc00004032e103d3600da01a870200604420000141bb000004078ea24b86005b881f601b080c3bc0f43826870511a078a418150234c01aa000014110000000000162f9d008ed9001e05482097ec061e81a8a0365206e2407280000f03986304e402060353d077400003448350048d05dba2e4cc14a08214b0049e05b381fe7022b1013760a3ec195e0290a02be0030441ca0000000000000018022000005043440a7c0000300350000080c5401e1480975022320fb2dcf28000050739207ff8070702c1c0664405894119f031d78002000000000001a1402440000101a8800005036200002411d501a54177f40d23008d6823810152403c6402c1004cd06312087ac109d032a8031400002c0b5d040d6012800000000060ba70000060a58c17000000d1805208e40000500c400000c0b59418280000f129300d3b05c4f8008c003de02840005801ba801ac00002802e50ba131714000028153940099041600000009ad0b92f04f18091a01410000000000a053d00b558b770000160550807b3006b7001be0fc7813be02e7900a34013e812518109a17f200001c13f00274b076bc0b1085bc0000000000b09614172d8182101c2c0b840000482b4e02fb60ae800000000000001e0fdc00000000000000c03dd8065103b260174000000000 else 0x2448138369601ff00ca1415e1805620119c0c3041c6f03ab90425004980130258150000042e5d411da80d9701a240c7201f01016600663c02f5c036800000000000000000000000b029460dec00000000000000203240000503680000082fb5405180000a04dfa0d0e80ef000007081ca0d080000000000000000000000040b6500001c0f55c008800000000000002015100000000000000205ac0000000000424870156d0c03106e14100741493003b003daa0edac089d8081c077021043449c50388e00aae02bbc201e01ee3045180a05011ad0217605b3e2007c0df300f5f07a620d7ec00300b864022b4027400cc88240f003a8252b01e37028e607c4208b4c155283d7202b2409b98804a004b40310a10174037c8150702b4a0a5640d808822106d4e094dc0c190293905b66102300373840f102660000000000000000001e0010c0fac03dda017fe0449001000000e06ab605c34056a018)))
def hashminel13 (i : Nat) : Nat := 0xa146a16a029000021aba118000780a40580001427b83ee145c042c0d78587038209540c0000007e80e1440100b60960002402a8a1104dc13440c800040b90297c20981481ad0057c42808401a52058444485b71b20000c24000030980164c01183cc01141280005021a0018340829d8d7914c429c000000020896117c28a8500000000306d28d8000000000007827000040dc411a029000000a042a8000501f600c000580ed03e0002027202ec08400000000000f064609242b0835707620f64168039e0260003c40a8d13003e292c0bf807e0ae6037809500c908160ae408e02a608e000000000003037e077c24e03ab00c0001443e036b0660002410505eb0a8a0d286de831303c60bf821a0094061201102ec8221e20060a01000101010706001001020301254001000413030805000131
def minesamples : Array (Bits × Bits) := #[(0x4ece25063008294271f880440000b401d74e,0x4ece25063008284030d880400000a001d54e),(0x718018ff4c03e21928089d7bfe0074823a50,0x300018304c03c21908001d3a3e0054820a10),(0x820ac5e9b8049e84bf5b48818c7fc0406980,0x8ac1c980040c04b75b4201806c80406080),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe393e0314105f809dc0972238779b0bc09301,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe27300016104b808940802038451303809301),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe00007a70cc1041321301022512808000000f,0x5a60cc10413203010205128000000000),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe04711810cf8f8c684020050a5935015fe401,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe002088184e07862c402001025915014e2001),(0x1a132c001537c690804025000405200a30032,0xc1328001137c290004024000401200010022),(0x1b334140425b114910644a88a000001040094,0x1bb54140421b010910004a888000000000014),(0x1180dea60a2e210233084f510a16c7a3800a8,0x1180c43e0a0801042b8049440a06878300088)]
def minecolumns : IndexTree ColumnInfo := (.leaf [(1,0,510,0,12),(2,0,509,0,12),(3,0,508,0,9),(2,1,460,48,7),(4,0,507,0,12),(6,0,505,0,9),(2,4,369,136,7),(7,0,504,0,7),(8,0,503,0,12),(9,0,486,0,8),(10,0,501,0,8),(12,0,499,0,9),(14,0,497,0,7),(10,4,369,128,6),(16,0,495,0,13),(0,16,486,9,10),(17,0,494,0,11),(19,0,492,0,8),(21,0,490,0,7),(24,0,487,0,11),(8,16,486,1,9),(25,0,486,0,8),(9,16,486,0,8),(32,0,479,0,12),(35,0,476,0,7),(49,0,462,0,8),(64,0,447,0,13),(0,64,189,258,10),(66,0,445,0,11),(2,64,189,256,9),(67,0,444,0,8),(70,0,441,0,8),(83,0,428,0,7),(96,0,415,0,9),(128,0,383,0,13),(132,0,379,0,11),(4,128,347,32,9),(133,0,378,0,7),(134,0,377,0,8),(136,0,375,0,9),(140,0,371,0,8),(144,0,367,0,11),(160,0,351,0,11),(164,0,347,0,8),(36,128,347,0,8),(192,0,319,0,11),(198,0,313,0,7),(256,0,255,0,12),(258,0,189,0,8),(264,0,247,0,9),(273,0,238,0,7),(280,0,231,0,8),(288,0,223,0,9),(320,0,191,0,11),(256,64,189,2,9),(322,0,189,0,8),(258,64,189,0,8)])
def mineautos : Array (List Nat) := #[[],[118,130,81],[100,131,82,16],[118,133,100,131,50,33,16],[116,83,32],[118,116,83,130,49,32],[118,133,33,48],[82,129,48],[118,133,116,83,82,81,80],[116,50,129,80],[100,49,128],[118,100,83,130,81,128]]
def minelevels : Nat → Packing
  | 9 => minel9
  | 10 => minel10
  | 11 => minel11
  | 12 => minel12
  | 13 => minel13
  | _ => emptyPacking
def mineindex : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 33 152 8 15 7 4 (hashminel10)
  | 11 => lookupWord 559 2097 12 19 11 4 (hashminel11)
  | 12 => lookupWord 607 1519 11 19 11 4 (hashminel12)
  | 13 => lookupWord 29 148 8 15 7 4 (hashminel13)
  | _ => fun _ => none
def mine : Forest := ⟨511,13,fun j => minesamples[j]?.getD (0,0),minecolumns,mineautos,minelevels,mineindex⟩
set_option maxHeartbeats 0 in
theorem geommine : graphValid mine (boundsBefore known383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine9_0 : block mine 9 0 64=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine9_1 : block mine 9 64 27=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine9_1 : block mine 9 0 91=true := (@block_merge mine 9 0 64 27 smine9_0 smine9_1)
theorem allmine9 : block mine 9 0 91=true := mmine9_1
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine10_0 : block mine 10 0 38=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine10_1 : block mine 10 38 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine10_1 : block mine 10 0 102=true := (@block_merge mine 10 0 38 64 smine10_0 smine10_1)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine10_2 : block mine 10 102 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine10_2 : block mine 10 0 166=true := (@block_merge mine 10 0 102 64 mmine10_1 smine10_2)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine10_3 : block mine 10 166 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine10_3 : block mine 10 0 230=true := (@block_merge mine 10 0 166 64 mmine10_2 smine10_3)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine10_4 : block mine 10 230 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine10_4 : block mine 10 0 294=true := (@block_merge mine 10 0 230 64 mmine10_3 smine10_4)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine10_5 : block mine 10 294 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine10_5 : block mine 10 0 358=true := (@block_merge mine 10 0 294 64 mmine10_4 smine10_5)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine10_6 : block mine 10 358 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine10_6 : block mine 10 0 422=true := (@block_merge mine 10 0 358 64 mmine10_5 smine10_6)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine10_7 : block mine 10 422 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine10_7 : block mine 10 0 486=true := (@block_merge mine 10 0 422 64 mmine10_6 smine10_7)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine10_8 : block mine 10 486 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine10_8 : block mine 10 0 550=true := (@block_merge mine 10 0 486 64 mmine10_7 smine10_8)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine10_9 : block mine 10 550 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine10_9 : block mine 10 0 614=true := (@block_merge mine 10 0 550 64 mmine10_8 smine10_9)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine10_10 : block mine 10 614 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine10_10 : block mine 10 0 678=true := (@block_merge mine 10 0 614 64 mmine10_9 smine10_10)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine10_11 : block mine 10 678 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine10_11 : block mine 10 0 742=true := (@block_merge mine 10 0 678 64 mmine10_10 smine10_11)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine10_12 : block mine 10 742 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine10_12 : block mine 10 0 806=true := (@block_merge mine 10 0 742 64 mmine10_11 smine10_12)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine10_13 : block mine 10 806 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine10_13 : block mine 10 0 870=true := (@block_merge mine 10 0 806 64 mmine10_12 smine10_13)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine10_14 : block mine 10 870 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine10_14 : block mine 10 0 934=true := (@block_merge mine 10 0 870 64 mmine10_13 smine10_14)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine10_15 : block mine 10 934 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine10_15 : block mine 10 0 998=true := (@block_merge mine 10 0 934 64 mmine10_14 smine10_15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine10_16 : block mine 10 998 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine10_16 : block mine 10 0 1062=true := (@block_merge mine 10 0 998 64 mmine10_15 smine10_16)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine10_17 : block mine 10 1062 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine10_17 : block mine 10 0 1126=true := (@block_merge mine 10 0 1062 64 mmine10_16 smine10_17)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine10_18 : block mine 10 1126 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine10_18 : block mine 10 0 1190=true := (@block_merge mine 10 0 1126 64 mmine10_17 smine10_18)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine10_19 : block mine 10 1190 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine10_19 : block mine 10 0 1254=true := (@block_merge mine 10 0 1190 64 mmine10_18 smine10_19)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine10_20 : block mine 10 1254 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine10_20 : block mine 10 0 1318=true := (@block_merge mine 10 0 1254 64 mmine10_19 smine10_20)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine10_21 : block mine 10 1318 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine10_21 : block mine 10 0 1382=true := (@block_merge mine 10 0 1318 64 mmine10_20 smine10_21)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine10_22 : block mine 10 1382 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine10_22 : block mine 10 0 1446=true := (@block_merge mine 10 0 1382 64 mmine10_21 smine10_22)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine10_23 : block mine 10 1446 44=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine10_23 : block mine 10 0 1490=true := (@block_merge mine 10 0 1446 44 mmine10_22 smine10_23)
theorem allmine10 : block mine 10 0 1490=true := mmine10_23
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine11_0 : block mine 11 0 9=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine11_1 : block mine 11 9 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine11_1 : block mine 11 0 73=true := (@block_merge mine 11 0 9 64 smine11_0 smine11_1)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine11_2 : block mine 11 73 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine11_2 : block mine 11 0 137=true := (@block_merge mine 11 0 73 64 mmine11_1 smine11_2)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine11_3 : block mine 11 137 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine11_3 : block mine 11 0 201=true := (@block_merge mine 11 0 137 64 mmine11_2 smine11_3)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine11_4 : block mine 11 201 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine11_4 : block mine 11 0 265=true := (@block_merge mine 11 0 201 64 mmine11_3 smine11_4)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine11_5 : block mine 11 265 58=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine11_5 : block mine 11 0 323=true := (@block_merge mine 11 0 265 58 mmine11_4 smine11_5)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine11_6 : block mine 11 323 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine11_6 : block mine 11 0 387=true := (@block_merge mine 11 0 323 64 mmine11_5 smine11_6)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine11_7 : block mine 11 387 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine11_7 : block mine 11 0 451=true := (@block_merge mine 11 0 387 64 mmine11_6 smine11_7)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine11_8 : block mine 11 451 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine11_8 : block mine 11 0 515=true := (@block_merge mine 11 0 451 64 mmine11_7 smine11_8)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine11_9 : block mine 11 515 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine11_9 : block mine 11 0 579=true := (@block_merge mine 11 0 515 64 mmine11_8 smine11_9)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine11_10 : block mine 11 579 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine11_10 : block mine 11 0 643=true := (@block_merge mine 11 0 579 64 mmine11_9 smine11_10)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine11_11 : block mine 11 643 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine11_11 : block mine 11 0 707=true := (@block_merge mine 11 0 643 64 mmine11_10 smine11_11)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine11_12 : block mine 11 707 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine11_12 : block mine 11 0 771=true := (@block_merge mine 11 0 707 64 mmine11_11 smine11_12)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine11_13 : block mine 11 771 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine11_13 : block mine 11 0 835=true := (@block_merge mine 11 0 771 64 mmine11_12 smine11_13)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine11_14 : block mine 11 835 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine11_14 : block mine 11 0 899=true := (@block_merge mine 11 0 835 64 mmine11_13 smine11_14)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine11_15 : block mine 11 899 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine11_15 : block mine 11 0 963=true := (@block_merge mine 11 0 899 64 mmine11_14 smine11_15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine11_16 : block mine 11 963 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine11_16 : block mine 11 0 1027=true := (@block_merge mine 11 0 963 64 mmine11_15 smine11_16)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine11_17 : block mine 11 1027 21=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine11_17 : block mine 11 0 1048=true := (@block_merge mine 11 0 1027 21 mmine11_16 smine11_17)
theorem allmine11 : block mine 11 0 1048=true := mmine11_17
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine12_0 : block mine 12 0 4=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine12_1 : block mine 12 4 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine12_1 : block mine 12 0 40=true := (@block_merge mine 12 0 4 36 smine12_0 smine12_1)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine12_2 : block mine 12 40 55=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine12_2 : block mine 12 0 95=true := (@block_merge mine 12 0 40 55 mmine12_1 smine12_2)
theorem allmine12 : block mine 12 0 95=true := mmine12_2
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine13_0 : block mine 13 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine13_1 : block mine 13 1 3=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine13_1 : block mine 13 0 4=true := (@block_merge mine 13 0 1 3 smine13_0 smine13_1)
theorem allmine13 : block mine 13 0 4=true := mmine13_1
theorem tablesmine : checkedTables mine 13 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mine 0 0 0 = true)
  · exact (rfl : block mine 1 0 0 = true)
  · exact (rfl : block mine 2 0 0 = true)
  · exact (rfl : block mine 3 0 0 = true)
  · exact (rfl : block mine 4 0 0 = true)
  · exact (rfl : block mine 5 0 0 = true)
  · exact (rfl : block mine 6 0 0 = true)
  · exact (rfl : block mine 7 0 0 = true)
  · exact (rfl : block mine 8 0 0 = true)
  · exact allmine9
  · exact allmine10
  · exact allmine11
  · exact allmine12
  · exact allmine13

-- The step. The circuit reads the nine inputs, the wire NOT x0 and the wire
-- x_i AND NOT x0. A backward derivation from the target ends in a set S of
-- these eleven wires. Every x_j with j at least 1 is in S, and x0 or NOT x0 is.
-- Six shapes of S remain. Five are cut by a restriction and a known bound.
-- The sixth, without x0 and with both new wires, is cut by the forest above
-- when i is 1, 2 or 3.
def x0s : Sig := inputs.getD 0 zero
def nsig : Sig := neg (inputs.getD 0 zero)
def hsig (i : Nat) : Sig := bin false (inputs.getD i zero) nsig
def rootsOf (i : Nat) : List Sig := inputs ++ [nsig, hsig i]

theorem lowAll : ∀ q, Lower (vars q) (graphGoal q) (boundsBefore known383 q) :=
  before_sound known383 valid383

theorem tgtmine : targetOf mine = graph := by decide +kernel

theorem forestRoot (j : Nat) (ws : List Sig) (idx : indexedRoot mine 13 j ws = true) :
    Impossible graph 13 ws.toFinset := by
  have h := root_index (g:=mine) lowAll geommine tablesmine (k:=13) (by decide) (i:=j) (ws:=ws) idx
  rw [tgtmine] at h
  exact h

theorem sliceOf (c : ColumnInfo) (ok : colCheck 511 c (boundsBefore known383) = true) :
    Slice (vars 511) graph (subcube c.1 c.2.1) c.2.2.2.2 := by
  have h := col_sound (m:=511) c (boundsBefore known383) lowAll ok
  have e : chartGoal 511 = graph := by decide +kernel
  rw [e] at h
  exact h

theorem cutBy {raw : List Sig} {T d : Sig} {L : Nat} (slice : Slice raw T d L) (cs : List Choice)
    {ws : List Sig} {cap : Nat} (nd : ws.Nodup)
    (ok : ((makePool d raw cs).map (fun pool => poolCut d L cap cs.length pool ws)).getD false = true) :
    Impossible T cap ws.toFinset := by
  cases h : makePool d raw cs with
  | none =>
    rw [h] at ok
    simp at ok
  | some pool =>
    rw [h] at ok
    exact poolCut_sound slice cs h nd ok

theorem slice0 : Slice (vars 511) graph (subcube 1 0) 12 := sliceOf (1,0,510,0,12) (by decide +kernel)
theorem slice1 : Slice (vars 511) graph (subcube 2 0) 12 := sliceOf (2,0,509,0,12) (by decide +kernel)
theorem slice2 : Slice (vars 511) graph (subcube 4 0) 12 := sliceOf (4,0,507,0,12) (by decide +kernel)
theorem slice3 : Slice (vars 511) graph (subcube 8 0) 12 := sliceOf (8,0,503,0,12) (by decide +kernel)
theorem slice4 : Slice (vars 511) graph (subcube 16 0) 13 := sliceOf (16,0,495,0,13) (by decide +kernel)
theorem slice6 : Slice (vars 511) graph (subcube 64 0) 13 := sliceOf (64,0,447,0,13) (by decide +kernel)

theorem shapeOpt {S : Finset Sig} {core full opt : List Sig}
    (sub : ∀ v ∈ S, v ∈ core ++ full) (all : ∀ v ∈ core, v ∈ S)
    (yes : ∀ v ∈ opt, v ∈ S) (no : ∀ v ∈ full, v ∈ S → v ∈ opt) :
    S = (core ++ opt).toFinset := by
  ext v
  simp only [List.mem_toFinset, List.mem_append]
  constructor
  · intro hv
    rcases List.mem_append.mp (sub v hv) with h | h
    · exact Or.inl h
    · exact Or.inr (no v h hv)
  · rintro (h | h)
    · exact all v h
    · exact yes v h

theorem split3 {S : Finset Sig} {core : List Sig} {a b c : Sig}
    (sub : ∀ v ∈ S, v ∈ core ++ [a,b,c]) (all : ∀ v ∈ core, v ∈ S) (ab : a ∈ S ∨ b ∈ S)
    (P : Prop)
    (ka : S = (core ++ [a]).toFinset → P) (kab : S = (core ++ [a,b]).toFinset → P)
    (kb : S = (core ++ [b]).toFinset → P) (kac : S = (core ++ [a,c]).toFinset → P)
    (kbc : S = (core ++ [b,c]).toFinset → P) (kabc : S = (core ++ [a,b,c]).toFinset → P) : P := by
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> by_cases hc : c ∈ S
  · apply kabc
    apply shapeOpt sub all
    · intro v hv
      simp at hv
      rcases hv with rfl | rfl | rfl <;> assumption
    · intro v hv _
      exact hv
  · apply kab
    apply shapeOpt sub all
    · intro v hv
      simp at hv
      rcases hv with rfl | rfl <;> assumption
    · intro v hv hS
      simp at hv ⊢
      rcases hv with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd hS hc
  · apply kac
    apply shapeOpt sub all
    · intro v hv
      simp at hv
      rcases hv with rfl | rfl <;> assumption
    · intro v hv hS
      simp at hv ⊢
      rcases hv with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact absurd hS hb
      · exact Or.inr rfl
  · apply ka
    apply shapeOpt sub all
    · intro v hv
      simp at hv
      rcases hv with rfl
      assumption
    · intro v hv hS
      simp at hv ⊢
      rcases hv with rfl | rfl | rfl
      · rfl
      · exact absurd hS hb
      · exact absurd hS hc
  · apply kbc
    apply shapeOpt sub all
    · intro v hv
      simp at hv
      rcases hv with rfl | rfl <;> assumption
    · intro v hv hS
      simp at hv ⊢
      rcases hv with rfl | rfl | rfl
      · exact absurd hS ha
      · exact Or.inl rfl
      · exact Or.inr rfl
  · apply kb
    apply shapeOpt sub all
    · intro v hv
      simp at hv
      rcases hv with rfl
      assumption
    · intro v hv hS
      simp at hv ⊢
      rcases hv with rfl | rfl | rfl
      · exact absurd hS ha
      · rfl
      · exact absurd hS hc
  · exact absurd ab (fun h => h.elim ha hb)
  · exact absurd ab (fun h => h.elim ha hb)

def tailPairs : List (Sig × Row × Row) :=
  [(1,2),(2,3),(3,2),(4,3),(5,7),(6,8),(7,2),(8,3)].map fun (p : Nat × Nat) =>
    (inputs.getD p.1 zero, Fin.ofNat 512 (1 + 2^p.2), Fin.ofNat 512 (1 + 2^p.2 + 2^p.1))

theorem tailNames : tailPairs.map Prod.fst = inputs.tail := by decide +kernel

theorem tailEss (i : Nat) (ok : checkEssential graph (rootsOf i) tailPairs = true) :
    ∀ a ∈ inputs.tail, Essential graph (rootsOf i) a := by
  intro a ha
  apply essential_ok ok a
  rw [tailNames]
  exact List.mem_toFinset.mpr ha

def zeroCheck (i : Nat) : Bool :=
  (bit (32 : Row) graph != bit (33 : Row) graph) &&
    (rootsOf i).all (fun w => w == x0s || w == nsig || bit (32 : Row) w == bit (33 : Row) w)

theorem rootBits (i : Nat) (hi : i < 9) (r : Row) :
    (rootsOf i).map (bit r) =
      List.ofFn (sample r) ++ [!sample r 0] ++ [sample r ⟨i,hi⟩ && !sample r 0] := by
  have e1 : bit r nsig = !sample r 0 := bit_neg r _
  have e2 : bit r (hsig i) = (sample r ⟨i,hi⟩ && !sample r 0) := by
    rw [hsig, bit_bin, e1]
    rfl
  rw [rootsOf, List.map_append, ←sampled r]
  simp only [List.map_cons, List.map_nil, e1, e2, List.append_assoc, List.cons_append, List.nil_append]

theorem rootHead (i : Nat) : rootsOf i = x0s :: (inputs.tail ++ [nsig, hsig i]) := rfl

theorem noCircuit (i : Nat) (hi : i < 9) (D : Circuit)
    (legal : PEqualNP.MetaComplexity.FanInTwo D) (small : D.size ≤ 13)
    (ess : checkEssential graph (rootsOf i) tailPairs = true) (zc : zeroCheck i = true)
    (c1 : Impossible graph 13 (inputs.tail ++ [x0s]).toFinset)
    (c2 : Impossible graph 13 (inputs.tail ++ [x0s, nsig]).toFinset)
    (c3 : Impossible graph 13 (inputs.tail ++ [nsig]).toFinset)
    (c4 : Impossible graph 13 (inputs.tail ++ [x0s, hsig i]).toFinset)
    (c5 : Impossible graph 13 (inputs.tail ++ [nsig, hsig i]).toFinset)
    (c6 : Impossible graph 13 (inputs.tail ++ [x0s, nsig, hsig i]).toFinset)
    (computes : ∀ x : Fin 9 → Bool,
      D.eval (List.ofFn x ++ [!x 0] ++ [x ⟨i,hi⟩ && !x 0]) = edge x) : False := by
  have wireEq (j : Nat) (r : Row) : bit r ((execute D.gates (rootsOf i)).getD j zero) =
      (D.wires ((rootsOf i).map (bit r))).getD j false := by
    rw [←b_read, execute_bits _ _ _ (fun g hg => (legal g hg).1)]
    rfl
  have goalEq : (execute D.gates (rootsOf i)).getD D.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    have h1 : (D.wires ((rootsOf i).map (bit r))).getD D.output false = edge (sample r) := by
      rw [rootBits i hi r]
      exact computes (sample r)
    exact (wireEq D.output r).trans (h1.trans (edge_table r).symm)
  have out := get_rep (execute D.gates (rootsOf i)) D.output
  rw [goalEq] at out
  have targetIn := out.resolve_right (fun hn => hn graph_proper)
  obtain ⟨k,t,S,hk,run,hs⟩ := extract D.gates (rootsOf i) legal graph_proper targetIn
  have hk13 : k ≤ 13 := Nat.le_trans hk small
  have all : ∀ a ∈ inputs.tail, a ∈ S := by
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := tailEss i ess a ha
    exact raw_required run (rootsOf i) a hs r s hd iso
  have zo : x0s ∈ S ∨ nsig ∈ S := by
    simp only [zeroCheck,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at zc
    obtain ⟨a,ha,hd⟩ := live_row_difference run zc.1
    rcases zc.2 a (hs a ha) with (he | he) | he
    · exact Or.inl (he ▸ ha)
    · exact Or.inr (he ▸ ha)
    · exact absurd he hd
  have sub : ∀ a ∈ S, a ∈ inputs.tail ++ [x0s, nsig, hsig i] := by
    intro a ha
    have h := hs a ha
    rw [rootHead] at h
    rcases List.mem_cons.mp h with h | h
    · subst h
      exact List.mem_append_right _ (List.mem_cons_self ..)
    · rcases List.mem_append.mp h with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
  exact split3 sub all zo False
    (fun e => c1 k t hk13 (e ▸ run)) (fun e => c2 k t hk13 (e ▸ run))
    (fun e => c3 k t hk13 (e ▸ run)) (fun e => c4 k t hk13 (e ▸ run))
    (fun e => c5 k t hk13 (e ▸ run)) (fun e => c6 k t hk13 (e ▸ run))

theorem caseA : Impossible graph 13 (inputs.tail ++ [x0s]).toFinset :=
  cutBy slice4 [] (by decide +kernel) (by decide +kernel)
theorem caseAB : Impossible graph 13 (inputs.tail ++ [x0s, nsig]).toFinset :=
  cutBy slice0 [] (by decide +kernel) (by decide +kernel)
theorem caseB : Impossible graph 13 (inputs.tail ++ [nsig]).toFinset :=
  forestRoot 0 _ (by decide +kernel)

theorem caseAC1 : Impossible graph 13 (inputs.tail ++ [x0s, hsig 1]).toFinset :=
  cutBy slice1 [] (by decide +kernel) (by decide +kernel)
theorem caseAC2 : Impossible graph 13 (inputs.tail ++ [x0s, hsig 2]).toFinset :=
  cutBy slice2 [] (by decide +kernel) (by decide +kernel)
theorem caseAC3 : Impossible graph 13 (inputs.tail ++ [x0s, hsig 3]).toFinset :=
  cutBy slice3 [] (by decide +kernel) (by decide +kernel)
theorem caseAC4 : Impossible graph 13 (inputs.tail ++ [x0s, hsig 4]).toFinset :=
  cutBy slice4 [] (by decide +kernel) (by decide +kernel)
theorem caseAC6 : Impossible graph 13 (inputs.tail ++ [x0s, hsig 6]).toFinset :=
  cutBy slice6 [] (by decide +kernel) (by decide +kernel)

theorem caseBC1 : Impossible graph 13 (inputs.tail ++ [nsig, hsig 1]).toFinset :=
  forestRoot 1 _ (by decide +kernel)
theorem caseBC2 : Impossible graph 13 (inputs.tail ++ [nsig, hsig 2]).toFinset :=
  forestRoot 2 _ (by decide +kernel)
theorem caseBC3 : Impossible graph 13 (inputs.tail ++ [nsig, hsig 3]).toFinset :=
  forestRoot 3 _ (by decide +kernel)
theorem caseBC4 : Impossible graph 13 (inputs.tail ++ [nsig, hsig 4]).toFinset :=
  cutBy slice4 [(2,x0s,x0s)] (by decide +kernel) (by decide +kernel)
theorem caseBC6 : Impossible graph 13 (inputs.tail ++ [nsig, hsig 6]).toFinset :=
  cutBy slice6 [(2,x0s,x0s)] (by decide +kernel) (by decide +kernel)

theorem caseABC1 : Impossible graph 13 (inputs.tail ++ [x0s, nsig, hsig 1]).toFinset :=
  cutBy slice0 [] (by decide +kernel) (by decide +kernel)
theorem caseABC2 : Impossible graph 13 (inputs.tail ++ [x0s, nsig, hsig 2]).toFinset :=
  cutBy slice0 [] (by decide +kernel) (by decide +kernel)
theorem caseABC3 : Impossible graph 13 (inputs.tail ++ [x0s, nsig, hsig 3]).toFinset :=
  cutBy slice0 [] (by decide +kernel) (by decide +kernel)
theorem caseABC4 : Impossible graph 13 (inputs.tail ++ [x0s, nsig, hsig 4]).toFinset :=
  cutBy slice0 [] (by decide +kernel) (by decide +kernel)
theorem caseABC6 : Impossible graph 13 (inputs.tail ++ [x0s, nsig, hsig 6]).toFinset :=
  cutBy slice0 [] (by decide +kernel) (by decide +kernel)

theorem no1 (D : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo D) (small : D.size ≤ 13)
    (computes : ∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [!x 0] ++ [x 1 && !x 0]) = edge x) : False :=
  noCircuit 1 (by decide) D legal small (by decide +kernel) (by decide +kernel)
    caseA caseAB caseB caseAC1 caseBC1 caseABC1 computes
theorem no2 (D : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo D) (small : D.size ≤ 13)
    (computes : ∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [!x 0] ++ [x 2 && !x 0]) = edge x) : False :=
  noCircuit 2 (by decide) D legal small (by decide +kernel) (by decide +kernel)
    caseA caseAB caseB caseAC2 caseBC2 caseABC2 computes
theorem no3 (D : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo D) (small : D.size ≤ 13)
    (computes : ∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [!x 0] ++ [x 3 && !x 0]) = edge x) : False :=
  noCircuit 3 (by decide) D legal small (by decide +kernel) (by decide +kernel)
    caseA caseAB caseB caseAC3 caseBC3 caseABC3 computes
theorem no4 (D : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo D) (small : D.size ≤ 13)
    (computes : ∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [!x 0] ++ [x 4 && !x 0]) = edge x) : False :=
  noCircuit 4 (by decide) D legal small (by decide +kernel) (by decide +kernel)
    caseA caseAB caseB caseAC4 caseBC4 caseABC4 computes
theorem no6 (D : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo D) (small : D.size ≤ 13)
    (computes : ∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [!x 0] ++ [x 6 && !x 0]) = edge x) : False :=
  noCircuit 6 (by decide) D legal small (by decide +kernel) (by decide +kernel)
    caseA caseAB caseB caseAC6 caseBC6 caseABC6 computes

end PEqualNP.Outside.L_meta_3277

theorem PEqualNP.Outside.L_meta_3277 : ∀ x1 ∈ [((1 : Fin (12 : ℕ)), (9 : Fin (12 : ℕ))), ((2 : Fin (12 : ℕ)), (9 : Fin (12 : ℕ))), ((3 : Fin (12 : ℕ)), (9 : Fin (12 : ℕ))), ((4 : Fin (12 : ℕ)), (9 : Fin (12 : ℕ))), ((6 : Fin (12 : ℕ)), (9 : Fin (12 : ℕ)))],   ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),     PEqualNP.MetaComplexity.FanInTwo x3 →       x3.size ≤ (13 : ℕ) →         ∃ (x6 : Fin (9 : ℕ) → Bool),           have x7 : List Bool := List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))];           have x8 : Fin (12 : ℕ) → Bool := fun (x8 : Fin (12 : ℕ)) => if x8 = (11 : Fin (12 : ℕ)) then Bool.true else x7.getD (↑x8) Bool.false;           x3.eval (x7 ++ [x8 x1.1 && x8 x1.2]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro x1 hx D legal small
  refine Classical.byContradiction fun hne => ?_
  have computes : ∀ x : Fin 9 → Bool,
      D.eval ((List.ofFn x ++ [!x 0]) ++
        [(if x1.1 = (11 : Fin 12) then true else (List.ofFn x ++ [!x 0]).getD x1.1.val false) &&
         (if x1.2 = (11 : Fin 12) then true else (List.ofFn x ++ [!x 0]).getD x1.2.val false)]) =
      PEqualNP.Outside.L_meta_3277.edge x := by
    intro x
    refine Classical.byContradiction fun h => ?_
    exact hne ⟨x, h⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact PEqualNP.Outside.L_meta_3277.no1 D legal small (fun x => computes x)
  · exact PEqualNP.Outside.L_meta_3277.no2 D legal small (fun x => computes x)
  · exact PEqualNP.Outside.L_meta_3277.no3 D legal small (fun x => computes x)
  · exact PEqualNP.Outside.L_meta_3277.no4 D legal small (fun x => computes x)
  · exact PEqualNP.Outside.L_meta_3277.no6 D legal small (fun x => computes x)
