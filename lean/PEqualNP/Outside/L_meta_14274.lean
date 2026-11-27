import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_14274

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace ForestCore

open PEqualNP.CircuitLowerBounds

abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def allowed (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)
def flipOp (d : Nat) := if d=2 then 3 else if d=3 then 2 else d
theorem allowed_four {u d} (h : allowed u d) : d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3) := by
  rcases h with h | ⟨h,j⟩
  · omega
  · have : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
theorem bin_flip {u d} (h : allowed u d) (a b : Sig) : bin d a b = bin (flipOp d) b a := by
  rcases allowed_four h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [bin,flipOp,BitVec.and_comm,BitVec.or_comm]
theorem flip_flip {u d} (h : allowed u d) : allowed u (flipOp d) ∧ flipOp (flipOp d)=d := by
  rcases allowed_four h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  all_goals simp_all [flipOp,allowed]

def Live (u : Bool) (target : Sig) : Nat → Finset Sig → Prop
  | 0,S => S={target} ∧ proper target
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), allowed u d ∧ S=insert a (insert b U) ∧
      proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live u target k (insert (bin d a b) U)
theorem Live.stop {u} {target : Sig} (hp : proper target) : Live u target 0 {target} := ⟨rfl,hp⟩
theorem Live.binary {u} {target : Sig} {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)) :
    Live u target (k+1) (insert a (insert b U)) :=
  ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩
theorem Live.ind {u} {target : Sig} {motive : ∀ (k : Nat) (S : Finset Sig), Live u target k S → Prop}
    (stop : ∀ (hp : proper target), motive 0 {target} (Live.stop hp))
    (binary : ∀ {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)),
      motive k (insert (bin d a b) U) tail →
      motive (k+1) (insert a (insert b U)) (Live.binary hd ha hb hab hfresh tail))
    {k : Nat} {S : Finset Sig} (h : Live u target k S) : motive k S h := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,hf,tail⟩ := h
    exact binary hd ha hb hab hf tail (ih tail)

private lemma live_proper {u target k S} (h : Live u target k S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
theorem bit_ext {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩

def nrm (u : Bool) (a : Sig) : Sig := if u && bit 0 a then neg a else a
theorem nrm_false (a : Sig) : nrm false a = a := rfl
theorem nrm_bit (a : Sig) : bit 0 (nrm true a) = false := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg]
theorem nrm_id {u} {a : Sig} (h : bit 0 a = false) : nrm u a = a := by simp [nrm,h]
theorem neg_neg' (a : Sig) : neg (neg a) = a := by simp [neg]
theorem nrm_neg (a : Sig) : nrm true (neg a) = nrm true a := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg,neg_neg']
theorem proper_neg {a : Sig} (h : proper (neg a)) : proper a := by
  refine ⟨?_,?_⟩
  · rintro rfl
    exact h.2 (by simp [neg,zero,one])
  · rintro rfl
    exact h.1 (by simp [neg,zero,one])
theorem proper_nrm {u} {a : Sig} (h : proper (nrm u a)) : proper a := by
  unfold nrm at h
  split at h
  · exact proper_neg h
  · exact h
def prime (d : Bool) (a b : Sig) := if d then a ||| b else a &&& b
theorem bit_prime (i) (d : Bool) (a b : Sig) : bit i (prime d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [prime,bit]
theorem nrm_prime (d : Bool) (a b : Sig) :
    ∃ e, e<4 ∧ nrm true (prime d a b) = bin e (nrm true a) (nrm true b) := by
  refine ⟨if d then (if bit 0 a then (if bit 0 b then 0 else 2) else (if bit 0 b then 3 else 1))
    else (if bit 0 a then (if bit 0 b then 1 else 3) else (if bit 0 b then 2 else 0)),?_,?_⟩
  · split_ifs <;> omega
  · apply bit_ext
    intro i
    cases d <;> cases ha : bit 0 a <;> cases hb : bit 0 b <;>
      simp only [nrm,bit_prime,ha,hb,bit_bin,bit_neg,Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.false_or,
        Bool.or_false,Bool.true_or,Bool.or_true,Bool.false_eq_true,ite_true,ite_false] <;>
      cases hx : bit i a <;> cases hy : bit i b <;> simp [hx,hy,bit_neg,bit_prime]

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (prime false) one
  | .or => xs.foldr (prime true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v
def Repr (u : Bool) (w : List Sig) (v : Sig) : Prop := represented w (nrm u v)

private lemma bin_laws (a : Sig) :
    bin 0 a one = a ∧ bin 1 a zero = a ∧
    bin 0 a zero = zero ∧ bin 1 a one = one ∧
    bin 0 a a = a ∧ bin 1 a a = a ∧ bin 2 a a = zero ∧ bin 3 a a = zero ∧ bin 2 a zero = a ∧
    bin 3 zero a = a ∧ bin 2 zero a = zero ∧ bin 3 a zero = zero ∧ bin 0 zero a = zero ∧ bin 1 zero a = a ∧
    bin 0 one a = a ∧ bin 1 one a = one := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply bit_ext <;> intro i <;>
    simp [bit_bin,bit_zero,bit_one]

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (u : Bool) (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, allowed u d ∧ a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b

private lemma bin_rep {u w a b} (d : Nat) (hd : allowed u d) (ha : represented w a) (hb : represented w b)
    (no : u=true → a ≠ one ∧ b ≠ one) :
    represented w (bin d a b) ∨ witness u w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := bin_laws a
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := bin_laws b
  by_cases he : a=b
  · subst b
    left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact b15.symm ▸ hb
    · exact b16.symm ▸ ro
    · exact absurd rfl (no hu).1
    · exact absurd rfl (no hu).1
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact a1.symm ▸ ha
    · exact a4.symm ▸ ro
    · exact absurd rfl (no hu).2
    · exact absurd rfl (no hu).2
  exact Or.inr ⟨d,a,b,hd,ham,hbm,hap,hbp,he,rfl⟩

theorem norm_ne_one (a : Sig) : nrm true a ≠ one := by
  intro h
  have := nrm_bit a
  rw [h,bit_one] at this
  exact Bool.noConfusion this
theorem prime_rep {u w a b} (d : Bool) (ha : Repr u w a) (hb : Repr u w b) :
    Repr u w (prime d a b) ∨ witness u w (nrm u (prime d a b)) := by
  cases u
  · have e : prime d a b = bin (if d then 1 else 0) a b := by cases d <;> rfl
    have h := bin_rep (u:=false) (if d then 1 else 0) (Or.inl (by split <;> omega)) ha hb (by simp)
    unfold Repr
    simp only [nrm_false] at h ⊢
    rwa [e]
  · obtain ⟨e,he,eq⟩ := nrm_prime d a b
    unfold Repr
    rw [eq]
    exact bin_rep e (Or.inr ⟨rfl,he⟩) ha hb (fun _ => ⟨norm_ne_one a,norm_ne_one b⟩)
theorem repr_const {u w} {v : Sig} (h : v=zero ∨ v=one) : Repr u w v := by
  refine Or.inr fun hp => ?_
  have := proper_nrm hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl
private lemma get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact repr_const (Or.inl rfl)
  | some a => exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))
theorem repr_neg {w a} (h : Repr true w a) : Repr true w (neg a) := by
  unfold Repr
  rwa [nrm_neg]

def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false
private lemma gate_rep (u : Bool) (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → isNot g=false) :
    Repr u (w.map (nrm u)) (gv w g) ∨ (isNot g=false ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have prim (d : Bool) : Repr u (w.map (nrm u)) ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one)) ∨
      witness u (w.map (nrm u)) (nrm u ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one))) := by
    have unit (v : Sig) : prime d v (if d then zero else one) = v := by
      apply bit_ext
      intro i
      cases d <;> simp [bit_prime,bit_zero,bit_one]
    cases l with
    | nil => exact Or.inl (repr_const (by cases d <;> simp))
    | cons i l =>
      cases l with
      | nil =>
        simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
        exact Or.inl (get_rep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (get_rep w i) (get_rep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (get_rep w i)

private lemma pull_gate {u target} {w : List Sig} {z : Sig} {k S c} (h : Live u target k S)
    (hz : represented w z ∨ (c=1 ∧ witness u w z)) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+c ∧ Live u target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨rfl,d,a,b,hd,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live u target k (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
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
        exact ⟨_,_,Nat.le_refl _,Live.binary hd pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract {u target} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → ∀ g ∈ gs, isNot g=false)
    (hp : proper target) (hout : target ∈ (execute gs w).map (nrm u)) :
    ∃ k S, k ≤ gs.countP (fun g => !isNot g) ∧ Live u target k S ∧ ∀ a ∈ S, a ∈ w.map (nrm u) := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha]))
      (fun hu a ha => mono hu a (by simp [ha])) hout
    have rep := gate_rep u w g (legal g (by simp)) (fun hu => mono hu g (by simp))
    rw [List.map_append] at hs
    have rep' : represented (w.map (nrm u)) (nrm u (gv w g)) ∨
        ((if isNot g then 0 else 1)=1 ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) :=
      rep.imp id (fun h => ⟨by simp [h.1],h.2⟩)
    obtain ⟨l,T,hl,hu,hT⟩ := pull_gate ht rep' hs
    refine ⟨l,T,?_,hu,hT⟩
    rw [List.countP_cons]
    cases hn : isNot g <;> simp [hn] at hl ⊢ <;> omega

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
      change bit i (prime false _ _) = (_ && _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (prime true _ _) = (_ || _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
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
def comb {R} (d : Nat) (a b : Wire R) : Wire R :=
  if d=0 then combine false a b else if d=1 then combine true a b else
    if d=2 then combine false a (inv b) else combine false (inv a) b

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (u : Bool) (pool : List (Wire R)) (v : Wire R) : Prop :=
  v ∈ pool ∨ Constant v ∨ (u=true ∧ inv v ∈ pool)

def supply {R} (u : Bool) (pool xs : List (Wire R)) := ∀ a ∈ xs, Available u pool a

def Reach {R} (u : Bool) (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0,b => b=roots
  | p+1,c => ∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R), Reach u roots p bank ∧ Available u bank a ∧
      Available u bank b ∧ c=combine op a b :: bank
theorem Reach.start {R u} {roots : List (Wire R)} : Reach u roots 0 roots := rfl
theorem Reach.two {R u} {roots : List (Wire R)} {p bank a b} (op : Bool) (h : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) : Reach u roots (p+1) (combine op a b :: bank) :=
  ⟨op,bank,a,b,h,ha,hb,rfl⟩
theorem Reach.ind {R u} {roots : List (Wire R)} {motive : ∀ p bank, Reach u roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (two : ∀ {p bank a b} (op : Bool) (h : Reach u roots p bank) (ha : Available u bank a)
      (hb : Available u bank b), motive p bank h →
      motive (p+1) (combine op a b :: bank) (Reach.two op h ha hb))
    {p bank} (h : Reach u roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero =>
    obtain rfl := h
    exact start
  | succ p ih =>
    obtain ⟨op,bank,a,b,h,ha,hb,rfl⟩ := h
    exact two op h ha hb (ih h)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R} (u : Bool) (goal : Wire R) : Nat → List (Wire R) → Prop
  | 0,zs => List.Perm [goal] zs
  | s+1,zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire R) (rest : List (Wire R)), allowed u op ∧ (a::b::rest).Perm zs ∧
      Run u goal s (comb op a b :: kept ka a (kept kb b rest))
theorem Run.stop {R u} {goal : Wire R} : Run u goal 0 [goal] := List.Perm.refl _
theorem Run.perm {R u} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run u goal s xs) : Run u goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op,ka,kb,a,b,rest,hd,q,h⟩ := h
    exact ⟨op,ka,kb,a,b,rest,hd,q.trans p,h⟩
theorem Run.two {R u} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Nat) (hd : allowed u op) (ka kb : Bool)
    (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))) : Run u goal (s+1) (a::b::rest) :=
  ⟨op,ka,kb,a,b,rest,hd,List.Perm.refl _,h⟩
theorem Run.ind {R u} {goal : Wire R} {motive : ∀ s ws, Run u goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run u goal s xs), motive s xs h → motive s zs (Run.perm p h))
    (two : ∀ {s a b rest} (op : Nat) (hd : allowed u op) (ka kb : Bool) (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))),
      motive s _ h → motive (s+1) (a::b::rest) (Run.two op hd ka kb h))
    {s ws} (h : Run u goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    obtain ⟨op,ka,kb,a,b,rest,hd,p,h⟩ := h
    exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (ih h))

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem inv_inv' {R} (a : Wire R) : inv (inv a)=a := by
  funext r
  simp [inv]
theorem cost_inv {R} (a : Wire R) : cost (inv a)=cost a := by
  have : Constant (inv a) ↔ Constant a := ⟨fun h => inv_inv' a ▸ inv_constant h,inv_constant⟩
  by_cases h : Constant a
  · simp only [cost,if_pos h,if_pos (this.mpr h)]
  · simp only [cost,if_neg h,if_neg (fun x => h (this.mp x))]
theorem avail_inv {R u} {bank : List (Wire R)} {a} (hu : u=true) (h : Available u bank a) : Available u bank (inv a) := by
  rcases h with h | h | ⟨_,h⟩
  · exact Or.inr (Or.inr ⟨hu,(inv_inv' a).symm ▸ h⟩)
  · exact Or.inr (Or.inl (inv_constant h))
  · exact Or.inl h
theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R u} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available u bank a) (hb : Available u bank b) :
    Available u bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)

theorem available_cons {R u} {bank v} (w : Wire R) (h : Available u bank v) :
    Available u (w::bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (And.imp id (List.mem_cons_of_mem _)))

theorem extend_two {R u} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (combine op a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
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
theorem comb_prime {R u} {bank : List (Wire R)} {d a b} (hd : allowed u d) (ha : Available u bank a) (hb : Available u bank b) :
    ∃ op x y, comb d a b=combine op x y ∧ Available u bank x ∧ Available u bank y ∧ cost x=cost a ∧ cost y=cost b := by
  rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · exact ⟨false,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨true,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨false,a,inv b,rfl,ha,avail_inv hu hb,rfl,cost_inv b⟩
  · exact ⟨false,inv a,b,rfl,avail_inv hu ha,hb,cost_inv a,rfl⟩
theorem extend_comb {R u} (roots : List (Wire R)) {p bank a b} (d) (hd : allowed u d) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (comb d a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (comb d a b) := by
  obtain ⟨op,x,y,e,hx,hy,cx,cy⟩ := comb_prime hd ha hb
  rw [e,←cx,←cy]
  exact extend_two roots op hp hx hy

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R u} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run u goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach u roots p bank) (hs : supply u bank ws) :
    ∃ q next, Reach u roots q next ∧ Available u next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply u bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @two s a b rest op hd ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_comb roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht : supply u T (comb op a b :: kept ka a (kept kb b rest)) := by
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

theorem restrict_comb {R S : Type} (rows : S → R) (d) (a b : Wire R) :
    restrictRows rows (comb d a b) = comb d (restrictRows rows a) (restrictRows rows b) := by
  unfold comb
  split_ifs <;> rfl
theorem restrict_run {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws) :
    Run u (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons,restrict_kept,restrict_comb] at ih ⊢
    exact Run.two op hd ka kb ih

theorem projected_bound {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach u roots p bank) (hs : supply u bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach u roots q bs → Available u bs (restrictRows rows goal) → L ≤ q) :
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

theorem obs_bin (d : Nat) (a b : Sig) :
    observe (bin d a b) = comb d (observe a) (observe b) := by
  funext r
  simp only [observe,bit_bin,comb]
  split_ifs <;> rfl

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {u} {T : Sig} {k S} (h : Live u T k S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run u (observe T) k (v.map observe) := by
  classical
  induction h using Live.ind generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @binary k U a b d hd ha hb hab fresh _ ih =>
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
    change Run _ _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d hd ka kb progress)

theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_prime (d : Bool) (f g : Wire Row) :
    table (combine d f g) = prime d (table f) (table g) := by
  apply bit_ext
  intro r
  rw [bit_table,bit_prime,bit_table,bit_table]
  cases d <;> rfl

theorem available_rep {u} {bank : List (Wire Row)} {a} (h : Available u bank a) :
    Repr u ((bank.map table).map (nrm u)) (table a) := by
  rcases h with hm | ⟨b,rfl⟩ | ⟨rfl,hm⟩
  · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hm))
  · apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (bit_table _ i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (bit_table _ i).trans (bit_one i).symm)
  · have := table_inv a
    refine Or.inl ?_
    rw [←nrm_neg,←this]
    exact List.mem_map_of_mem (List.mem_map_of_mem hm)

theorem reach_live_sub {u} {roots : List (Wire Row)} {p bank}
    (h : Reach u roots p bank) {T k S} (run : Live u T k S)
    (sub : ∀ a ∈ S, a ∈ (bank.map table).map (nrm u)) :
    ∃ l V, l ≤ p+k ∧ Live u T l V ∧ ∀ a ∈ V, a ∈ (roots.map table).map (nrm u) := by
  induction h using Reach.ind generalizing k S with
  | start => exact ⟨k,S,by omega,run,sub⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,List.map_cons,table_prime] at sub
    have rep := prime_rep d (available_rep ha) (available_rep hb)
    obtain ⟨k',S',hk,run',sub'⟩ := pull_gate (c:=1) run (rep.imp id (fun h => ⟨rfl,h⟩))
      (fun a hm => by simpa [or_comm] using sub a hm)
    obtain ⟨l,V,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,V,by omega,hr,hs⟩

def plainWord (a : Sig) : Bool := !(bit 0 a)
theorem nrm_map {u} {w : List Sig} (h : w.all plainWord=true) : w.map (nrm u)=w := by
  have e : w.map (nrm u) = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact nrm_id (by simpa [plainWord] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]
theorem reach_live {u} {roots : List Sig} {p bank T} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (h : Reach u (roots.map observe) p bank) (hit : Available u bank (observe T)) :
    ∃ k S, k ≤ p ∧ Live u T k S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  unfold Repr at hm
  rw [nrm_id (by simpa [plainWord] using nT)] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,V,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,V,by omega,hr,?_⟩
  have e : (roots.map observe).map table = roots := by simp [List.map_map,Function.comp_def,table_observe]
  rw [e,nrm_map nR] at hs
  exact hs

theorem live_row_difference {u T k S} (h : Live u T k S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {u T k S} (h : Live u T k S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [(((((((((((((((2863311530 * 4294967296 + 2863311530) * 4294967296 + 2863311530) * 4294967296 + 2863311530) * 4294967296 + 2863311530) * 4294967296 + 2863311530) * 4294967296 + 2863311530) * 4294967296 + 2863311530) * 4294967296 + 2863311530) * 4294967296 + 2863311530) * 4294967296 + 2863311530) * 4294967296 + 2863311530) * 4294967296 + 2863311530) * 4294967296 + 2863311530) * 4294967296 + 2863311530) * 4294967296 + 2863311530),(((((((((((((((3435973836 * 4294967296 + 3435973836) * 4294967296 + 3435973836) * 4294967296 + 3435973836) * 4294967296 + 3435973836) * 4294967296 + 3435973836) * 4294967296 + 3435973836) * 4294967296 + 3435973836) * 4294967296 + 3435973836) * 4294967296 + 3435973836) * 4294967296 + 3435973836) * 4294967296 + 3435973836) * 4294967296 + 3435973836) * 4294967296 + 3435973836) * 4294967296 + 3435973836) * 4294967296 + 3435973836),(((((((((((((((4042322160 * 4294967296 + 4042322160) * 4294967296 + 4042322160) * 4294967296 + 4042322160) * 4294967296 + 4042322160) * 4294967296 + 4042322160) * 4294967296 + 4042322160) * 4294967296 + 4042322160) * 4294967296 + 4042322160) * 4294967296 + 4042322160) * 4294967296 + 4042322160) * 4294967296 + 4042322160) * 4294967296 + 4042322160) * 4294967296 + 4042322160) * 4294967296 + 4042322160) * 4294967296 + 4042322160),(((((((((((((((4278255360 * 4294967296 + 4278255360) * 4294967296 + 4278255360) * 4294967296 + 4278255360) * 4294967296 + 4278255360) * 4294967296 + 4278255360) * 4294967296 + 4278255360) * 4294967296 + 4278255360) * 4294967296 + 4278255360) * 4294967296 + 4278255360) * 4294967296 + 4278255360) * 4294967296 + 4278255360) * 4294967296 + 4278255360) * 4294967296 + 4278255360) * 4294967296 + 4278255360) * 4294967296 + 4278255360),(((((((((((((((4294901760 * 4294967296 + 4294901760) * 4294967296 + 4294901760) * 4294967296 + 4294901760) * 4294967296 + 4294901760) * 4294967296 + 4294901760) * 4294967296 + 4294901760) * 4294967296 + 4294901760) * 4294967296 + 4294901760) * 4294967296 + 4294901760) * 4294967296 + 4294901760) * 4294967296 + 4294901760) * 4294967296 + 4294901760) * 4294967296 + 4294901760) * 4294967296 + 4294901760) * 4294967296 + 4294901760),(((((((((((((((4294967295 * 4294967296 + 0) * 4294967296 + 4294967295) * 4294967296 + 0) * 4294967296 + 4294967295) * 4294967296 + 0) * 4294967296 + 4294967295) * 4294967296 + 0) * 4294967296 + 4294967295) * 4294967296 + 0) * 4294967296 + 4294967295) * 4294967296 + 0) * 4294967296 + 4294967295) * 4294967296 + 0) * 4294967296 + 4294967295) * 4294967296 + 0),(((((((((((((((4294967295 * 4294967296 + 4294967295) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 4294967295) * 4294967296 + 4294967295) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 4294967295) * 4294967296 + 4294967295) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 4294967295) * 4294967296 + 4294967295) * 4294967296 + 0) * 4294967296 + 0),(((((((((((((((4294967295 * 4294967296 + 4294967295) * 4294967296 + 4294967295) * 4294967296 + 4294967295) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 4294967295) * 4294967296 + 4294967295) * 4294967296 + 4294967295) * 4294967296 + 4294967295) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0),(((((((((((((((4294967295 * 4294967296 + 4294967295) * 4294967296 + 4294967295) * 4294967296 + 4294967295) * 4294967296 + 4294967295) * 4294967296 + 4294967295) * 4294967296 + 4294967295) * 4294967296 + 4294967295) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0)]
def graph : Sig := (((((((((((((((4294967295 * 4294967296 + 4294967295) * 4294967296 + 4294967295) * 4294967296 + 4293585640) * 4294967296 + 4294901500) * 4294967296 + 4294638328) * 4294967296 + 4293848812) * 4294967296 + 4293585640) * 4294967296 + 4294967295) * 4294967296 + 4294967295) * 4294967296 + 4294967295) * 4294967296 + 4293585640) * 4294967296 + 4294901500) * 4294967296 + 4294638328) * 4294967296 + 4293848812) * 4294967296 + 4293585640)
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 4) || (x 5 && x 7) || (x 6 && x 7)
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

def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_bin (f : Row → Row) (d : Nat) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply bit_ext
  intro r
  simp only [bit_rename,bit_bin]

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
theorem live_rename {u T k S} (h : Live u T k S) (f : Row → Row) (onto : Function.Surjective f) :
    Live u (rename f T) k (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Live.ind with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary hd (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {u T k S} (h : Live u T k S) (none : u=false) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      subst none
      rcases allowed_four hd with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · exact Bool.noConfusion h
      · exact Bool.noConfusion h
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (observe T) → L ≤ p
theorem reach_up {R u} {roots : List (Wire R)} {p bank} (h : Reach false roots p bank) : Reach u roots p bank := by
  have up {bank : List (Wire R)} {a} (h : Available false bank a) : Available u bank a :=
    h.imp id (Or.imp id (fun h => Bool.noConfusion h.1))
  induction h using Reach.ind with
  | start => exact Reach.start
  | two op h ha hb ih => exact Reach.two op ih (up ha) (up hb)
theorem lower_down {u roots T L} (h : Lower true roots T L) : Lower u roots T L := by
  cases u
  · exact fun p bank hr ha => h p bank (reach_up hr) (ha.imp id (Or.imp id (fun h => Bool.noConfusion h.1)))
  · exact h

def Impossible (u : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Live u T k S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {u roots T L} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible u T L roots.toFinset) : Lower u roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,S,hk,run,hs⟩ := reach_live hp nT nR h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : Repr false [] v := by
    apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (congrFun h i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (congrFun h i).trans (bit_one i).symm)
  have hr' : represented [] v := hr
  exact (hr'.resolve_left (by simp)) hv

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

theorem lower_slice {u} {roots other : List Sig} {T G : Sig} (pT : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available u (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower u other G L) : Lower u roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,S,hk,run,sub⟩ := reach_live pT nT nR hh ha
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
  have supp : supply u (other.map observe) ((front.map observe).map (restrictRows r)) := by
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

def childTwo (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {u} {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, allowed u d → ∀ ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible u T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible u T cap ws.toFinset := by
  classical
  intro k hk h
  generalize he : ws.toFinset = S at h
  induction h using Live.ind with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @binary k U a b d hd ha hb hab hf tail _ =>
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
    have sc := live_size tail
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d hd ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)

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

theorem cover_sound {u T k S} (h : Live u T k S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → u=false) :
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

theorem cover_required {u T ws k} (h : Live u T k (List.toFinset ws)) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (!u) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  simp

def Slice (u : Bool) (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available u (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m) ||
    (u && (let c := masked d (neg a); (pool.map (masked d)).any (fun v => v==c)))

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

def poolSupply (u : Bool) (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available u bank (restrictRows f (observe a))

theorem availableB_sound {u} {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply u f bank pool)
    (check : availableB u d pool a = true) : Available u bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with ((hz | ho) | ⟨v,hv,he⟩) | ⟨hu,v,hv,he⟩
  · exact Or.inr (Or.inl ⟨false,masked_zero dom hz⟩)
  · exact Or.inr (Or.inl ⟨true,masked_one dom ho⟩)
  · exact masked_eq dom he ▸ supplyB v hv
  · have h := avail_inv hu (masked_eq dom he ▸ supplyB v hv)
    rw [obs_neg] at h
    have e : inv (restrictRows f (inv (observe a))) = restrictRows f (observe a) := by
      funext r
      simp [inv,restrictRows]
    rwa [e] at h

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) := bin c.1 c.2.1 c.2.2
def allowedB (u : Bool) (d : Nat) := decide (d<2) || (u && decide (d<4))
theorem allowedB_ok {u d} (h : allowedB u d=true) : allowed u d := by
  simpa [allowedB,allowed] using h
def choiceOK (u : Bool) (d : Sig) (pool : List Sig) (c : Choice) :=
  allowedB u c.1 && (availableB u d pool c.2.1 && availableB u d pool c.2.2)

theorem pay_choice {u} {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (c : Choice) (valid : choiceOK u d pool c = true) :
    ∃ next, Reach u roots (q+1) next ∧ poolSupply u f next (choiceVal c :: pool) := by
  simp only [choiceOK,Bool.and_eq_true] at valid
  obtain ⟨op,x,y,e,hx,hy,_,_⟩ := comb_prime (allowedB_ok valid.1) (availableB_sound dom hs valid.2.1)
    (availableB_sound dom hs valid.2.2)
  refine ⟨_,Reach.two op hp hx hy,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · rw [choiceVal,obs_bin,restrict_comb,e]
    exact Or.inl (by simp)
  · exact available_cons _ (hs _ hm)

def makePool (u : Bool) (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK u d pool c then makePool u d (choiceVal c::pool) cs else none

theorem makePool_sound {u} {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (cs : List Choice) {result} (ok : makePool u d pool cs = some result) :
    ∃ next, Reach u roots (q+cs.length) next ∧ poolSupply u f next result := by
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

def poolCut (u : Bool) (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB u d pool)

theorem poolCut_sound {u raw T d L} (slice : Slice u raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool u d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut u d L cap cs.length pool ws = true) :
    Impossible u T cap ws.toFinset := by
  intro k hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply u bank ((ws.map observe).map (restrictRows f)) := by
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
theorem freeWord_ok {u roots w} (ok : freeWord roots w = true) :
    Available u (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr (Or.inl ⟨false,funext bit_zero⟩)
  · exact Or.inr (Or.inl ⟨true,funext bit_one⟩)
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {u ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available u (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

theorem lower_map {u ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (nT : plainWord T=true) (nR : raw.all plainWord=true) (pG : proper G)
    (hL : Lower u base G L) : Lower u raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT nT nR pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

theorem slice_correct {u ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower u base G L) :
    Slice u raw T d L := by
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
  plainWord T && raw.all plainWord && xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok.2 _ hm)

theorem essential_plain {T raw xs} (ok : checkEssential T raw xs = true) :
    plainWord T=true ∧ raw.all plainWord=true := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  exact ok.1
theorem lower_count {u raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower u raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,S,hk,run,sub⟩ := reach_live properT (essential_plain ok).1 (essential_plain ok).2 hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := live_size run
  omega

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

theorem lift_ok {u ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower u base G L) :
    Lower u raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 properG _ eq supp _ (essential_ok ok.1.2) _ L low
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
def typeWord (t : Nat) : Sig := bin (t/81) (inputs.getD (t/9 % 9) zero) (inputs.getD (t % 9) zero)
def varsX (m : Nat) : List Sig := if m<512 then vars m else vars m ++ [typeWord (m/512-1)]
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 2) ||| (x 1 &&& x 5) ||| (x 2 &&& x 6) ||| (x 3 &&& x 4) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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
  | 0 => ((((((((((((((1 * 4294967296 + 0) * 4294967296 + 1) * 4294967296 + 0) * 4294967296 + 1) * 4294967296 + 0) * 4294967296 + 1) * 4294967296 + 0) * 4294967296 + 1) * 4294967296 + 0) * 4294967296 + 1) * 4294967296 + 0) * 4294967296 + 1) * 4294967296 + 0) * 4294967296 + 1)
  | 1 => ((((((((((((1 * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 1) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 1) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 1)
  | 2 => ((((((((((1 * 4294967296 + 0) * 4294967296 + 1) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 1) * 4294967296 + 0) * 4294967296 + 1)
  | 3 => ((((((((1 * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 1)
  | 4 => ((((((1 * 4294967296 + 0) * 4294967296 + 1) * 4294967296 + 0) * 4294967296 + 1) * 4294967296 + 0) * 4294967296 + 1)
  | 5 => ((((1 * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 1)
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

def supportPairs (t : Nat) (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) =>
    let r := if t/81==2 && i==t/9 % 9 then 1 <<< (t % 9) else if t/81==2 && i==t % 9 then 1 <<< (t/9 % 9) else 0
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig := graphGoal m
def rawMask (m : Nat) (c : ColumnInfo) : Nat := m % 512+512*(c.1/512)
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let raw := rawMask m c
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/512+80) s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (varsX free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (varsX free) (varsX q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {u} {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice u (varsX (rawMask m c)) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  revert ok
  obtain ⟨z,o,q,s,L⟩ := c
  intro ok
  let ms := fixRows z o
  let raw := rawMask m (z,o,q,s,L)
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/512+80) s
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

def carryOK (old rep : Nat) (swaps : List Nat) :=
  (properB (graphGoal old) && plainWord (graphGoal old) && (varsX old).all plainWord) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (varsX old) (graphGoal old) (varsX rep) (graphGoal rep)
theorem carry_of {u old rep L swaps} (ok : carryOK old rep swaps = true)
    (h : Lower u (varsX rep) (graphGoal rep) L) : Lower u (varsX old) (graphGoal old) L := by
  simp only [carryOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1.1.1) ok.1.1.1.2 ok.1.1.2 (proper_of _ ok.1.2) h

def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound {u} (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower u (varsX q) (graphGoal q) (boundsBefore entries q) := by
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

def ValidPool (u : Bool) (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach u (roots.map observe) q ws → Available u ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach u (roots.map observe) c.paid bank ∧ poolSupply u f bank c.wires ∧ True

theorem build_valid {u raw T d lb} (h : Slice u raw T d lb) (cs : List Choice) {ws}
    (build : makePool u d raw cs = some ws) : ValidPool u raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa [BoundPool.paid] using hr,hs,trivial⟩

theorem valid_exclude {u raw T c} (valid : ValidPool u raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB u c.domain c.wires a = true)
    (buy : if paid then choiceOK u c.domain c.wires choice = true
       else availableB u c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible u T k (choiceVal choice :: rest).toFinset := by
  intro t ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach u (roots.map observe) n out)
      (zs : poolSupply u f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply u out ((ws.map observe).map (restrictRows f)) := by
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
    · have point : ∀ v ∈ c.wires, Available u out (restrictRows f (observe v)) :=
        fun v hu => hc v (List.mem_cons_of_mem _ hu)
      exact availableB_sound dom point (known _ hm)

def scalarPoolCut (u : Bool) (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB u c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB u c.domain c.wires)) && (!extra || choiceOK u c.domain c.wires op)

theorem scalarPoolCut_sound {u raw T c} (valid : ValidPool u raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut u c k rest op = true) :
    Impossible u T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB u c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB u c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1

def materialize (u : Bool) (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool u d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {u raw T d L cs c} (slice : Slice u raw T d L)
    (h : materialize u raw cs d L = some c) : ValidPool u raw T c := by
  unfold materialize at h
  cases he : makePool u d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he

abbrev Bits := BitVec 152
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 152 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 152 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 152 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 152 → Row) (x : Decor) := x.2 = pairSig r s x.1
def bv {n : Nat} (d : Nat) (a b : BitVec n) : BitVec n :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def dbin (d : Nat) (x y : Decor) : Decor := (bin d x.1 y.1,bv d x.2.1 y.2.1,bv d x.2.2 y.2.2)

theorem ofRows_bin {n : Nat} (r : Fin n → Row) (d : Nat) (a b : Sig) :
    ofRows r (bin d a b) = bv d (ofRows r a) (ofRows r b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  rw [h]
  unfold bv
  split_ifs <;> simp [hj]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  simp only [faithful,dbin,pairSig,ofRows_bin,hx,hy]

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
    decodeBank k (bits >>> 10) (ws++[dbin ((bits >>> 8) &&& 3) a b])
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
      exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def asRow (cols : Nat → Bits) (i : Fin 152) : Row :=
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 152) (j : Fin 9) :
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
  (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 2) ||| (x 1 &&& x 5) ||| (x 2 &&& x 6) ||| (x 3 &&& x 4) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 152) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 152) :
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
  let n := v.toNat % 2305843009213693921
  (n*(n+971)) % 2305843009213693921
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def closeChild (u : Bool) (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut u p k rest op)

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

abbrev CovPair := Cov × Bool
def preCov (u : Bool) (ws : List Decor) : CovPair := (coverage (!u) ws,u)
def restCov (v : Cov) (a b : Bits) (ka kb : Bool) :=
  if ka then (if kb then v.1 else takeOne v b) else if kb then takeOne v a else takeTwo v a b

theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    (delTwo ws a b ka kb).Sublist ws := (delOne_sub _ _ _).trans (delOne_sub _ _ _)
theorem len_keep (ws : List Decor) (a b : Decor) (ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) :
    (delTwo ws a b ka kb).length =
      ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  cases ka <;> cases kb <;> simp [delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]

def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := restCov cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 152 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChild cov.2 pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (dbin op a b).1 :: (delTwo ws a b ka kb).map Prod.fst
theorem evalMove_sound {u raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (pro : proper (dbin op a b).1) (fresh : (dbin op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov u ws,pools,links) op a b (dbin op a b) ka kb = true) :
    Impossible u T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := dbin op a b
  let rest := delTwo ws a b ka kb
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k hk h
  have hsz := live_size h
  change child.toFinset.card ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h (pair_sep pairs)
  let d := !u
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz : (coverage d rest).1 = restCov (coverage d ws) (column d a.2) (column d b.2) ka kb :=
    cover_two d a b ha hb ne ka kb
  have hf := faithful_bin op (faith _ ha) (faith _ hb)
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact closeChild_sound (op:=movedChoice op a b) (rest:=rest.map Prod.fst) pv lv ndc test k hk h

def testPair (ctx : NodeContext) (a b : Decor) (op : Nat) :=
  let z := dbin op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def opsOf (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]
theorem opsOf_mem {u d} (h : allowed u d) : d ∈ opsOf u := by
  rcases allowed_four h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> simp [opsOf]
  · cases u <;> simp [opsOf]
  · simp [opsOf]
  · simp [opsOf]
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (opsOf ctx.2.2.2.1.2).all (testPair ctx a b))
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx a b d=true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => h.1 b bm d (opsOf_mem hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (opsOf_mem hd)
      · exact ih h.2 haTail hbTail

theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx d a b (dbin d a b) ka kb = true := by
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
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  simp only [delTwo,List.mem_map,mem_delone wn,mem_delone dn]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
    exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d : Nat) (ka kb : Bool) :
    (moveFront ws d a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv' := List.mem_map_of_mem (f:=Prod.fst) hb
  simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,dbin]
  by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem childTwo_swap {u} (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : allowed u d) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_flip hd a b]
  tauto

theorem node_sound {u raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov u ws,pools,links) ws = true) :
    Impossible u T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact out (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  intro a ha b hb d hd ka kb ne fresh pro len
  obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
  obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
  have ab : a≠b := fun e => ne (congrArg Prod.fst e)
  have one (a b : Decor) (d : Nat) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
      (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
      (test : testPair (cap,ws.length,ws,preCov u ws,pools,links) a b d = true) :
      Impossible u T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←binary_front nd aa bb ne']
    exact evalMove_sound pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      pr fr (testPair_at test ka kb)
  rcases all_binary checks haW hbW ab with hh | hh
  · exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    exact one b a (flipOp d) hbW haW (Ne.symm ne) kb ka (bin_flip hd a.1 b.1 ▸ pro)
      (bin_flip hd a.1 b.1 ▸ fresh) (hh _ (flip_flip hd).1)

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
theorem rotate_excluded {u T n} {ws : List Sig} (hi : Impossible u T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible u T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k hk h
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
  exact hi k hk run

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
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none

def lookupShort (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 4 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none

abbrev Forest := Nat × Nat × (Nat → Bits × Bits) × List ColumnInfo × List (List Nat) ×
  (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
def Forest.mask (g : Forest) : Nat := g.1
def Forest.mode (g : Forest) : Bool := !(g.1.testBit 10)
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
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 152) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 152) (hq : chartSamples m q = 0) :
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

def prefixWidth (d : Nat) := 10*(d-1)
def denseRowWidth (d flags : Nat) := flags % 16 + (if d=0 then 0 else 10) + flags/16
def denseRowStart (d raw dict : Nat) :=
  (dict % 65536)*prefixWidth d + (dict/65536)*(raw+d)

def forestRecord (tab : Packing) (raw i : Nat) : Nat :=
  let (_,d,_,dict,flags,_,marker,word) := tab
  let width := 10*d+raw+d
  if marker<1024 then packedAt word (i*width) width else
    let off := denseRowStart d raw dict+i*denseRowWidth d flags
    let pre := packedAt word off (flags % 16)
    let lastBits := if d=0 then 0 else 10
    let last := packedAt word (off+flags % 16) lastBits
    let mask := packedAt word (off+flags % 16+lastBits) (flags/16)
    let base := (dict % 65536)*prefixWidth d
    packedAt word (pre*prefixWidth d) (prefixWidth d) |||
      (last <<< prefixWidth d) ||| (packedAt word (base+mask*(raw+d)) (raw+d) <<< (10*d))

def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := forestRecord (g.levels k) raw.length i
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
    materialize g.mode (varsX (rawMask g.mask ci)) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool g.mode (vars g.mask) (targetOf g) c := by
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

def forceDatum {α : Type} : Nat → (Nat → α) → α
  | 0, next => next 0
  | n+1, next => next (n+1)

def readSortedHints (data : Nat → Nat) (dict cw d gapBits : Nat) :
    Nat → Nat → Nat → List (Nat × Nat)
  | 0,_,_ => []
  | left+1,st,first =>
    forceDatum st fun pos => forceDatum first fun base =>
    forceDatum (packedAt data pos 32) fun head =>
    forceDatum (Nat.log2 (head ^^^ (head+1))) fun ones =>
    forceDatum (base+(ones <<< gapBits)+packedAt data (pos+ones+1) gapBits) fun key =>
    forceDatum (packedAt data (dict+key*(cw+d)) (cw+d)) fun pair =>
      (pair &&& ((1 <<< cw)-1),pair >>> cw) ::
        readSortedHints data dict cw d gapBits left (pos+ones+1+gapBits) (key+1)

def promoteHints {α : Type} (a b : Nat) (xs : List α) : List α :=
  let rec collect : List α → Nat → List α → List α → List α → List α
    | [],_,first,second,other => first ++ second ++ other.reverse
    | x::tail,i,first,second,other =>
      if i=a then collect tail (i+1) [x] second other
      else if i=b then collect tail (i+1) first [x] other
      else collect tail (i+1) first second (x::other)
  collect xs 0 [] [] []

def forestHints (tab : Packing) (raw i : Nat) : List (Nat × Nat) :=
  let (num,d,cw,dict,flags,ow,marker,data) := tab
  if marker<1024 then
    let start := num*(10*d+raw+d)
    let pos := start+num*ow+packedAt data (start+i*ow) ow
    getPairs data cw d (packedAt data pos 6) (pos+6+marker)
  else
    let off := denseRowStart d raw dict + num*denseRowWidth d flags
    let pairs := off+num*ow
    let priority := decide (4096≤marker)
    let pos := pairs+(marker-(if priority then 4096 else 1024))*(cw+d)+packedAt data (off+i*ow) ow
    let n := packedAt data pos 5
    let gap := packedAt data (pos+5) 3
    if !priority || decide (n≤1) then readSortedHints data pairs cw d gap n (pos+8) 0 else
      let width := (n-1).log2+1
      let a := packedAt data (pos+8) width
      let b := if n=2 then 1-a else packedAt data (pos+8+width) width
      let extra := if n=2 then width else 2*width
      let xs := readSortedHints data pairs cw d gap n (pos+8+extra) 0
      promoteHints a b xs

def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)

theorem linkedSet_sound (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair = some out) :
    Impossible g.mode (targetOf g) k out.toFinset := by
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
  let rules := (forestHints (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov g.mode ws,rules,ls) ws)

theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible g.mode (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i = true) : Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    obtain ⟨hS,_⟩ := h
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
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 152) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.all (fun c => colCheck g.mask c prior) &&
  g.autos.all (fun p => autoOK (targetOf g) (p.map swapRows))

theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
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
theorem root_index {g top prior k i ws} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible g.mode (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1

theorem lower_forest {g prior i hints} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower g.mode (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) (essential_plain ess).1 (essential_plain ess).2 _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def Known (u : Bool) (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (carries : List (Nat × List Nat)) :=
  carries.map (fun v => (v.1,L)) ++ old
theorem extend_ok {u old L m carries} (previous : Known u old)
    (main : Lower u (varsX m) (graphGoal m) L)
    (ok : carries.all (fun v => carryOK v.1 m v.2) = true) :
    Known u (extendKnown old L carries) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact carry_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known true [] := by simp [Known]
theorem known_down {u es} (h : Known true es) : Known u es := fun e he => lower_down (h e he)
def lanePlace (v : Nat) (upper : Nat) := 2^153*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^153 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
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
def fullMarks (r packed : Nat) := ((packed+r) >>> 152) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (153*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^153)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 153*(i+1)-153=153*i := by omega
      have ge : ¬153*(i+1)<153 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 152 = (a==BitVec.allOnes 152) := by
  by_cases h : a=BitVec.allOnes 152
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^152-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^152 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (153*i) =
      (f xs[i]==BitVec.allOnes 152) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^153*u+x+(2^153*v+1)=2^153*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^153 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬153*(i+1)+152<153 := by omega
      have di : 153*(i+1)+152-153=153*i+152 := by omega
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

def packedOp (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=0 then (a.1 &&& b.1,a.2 &&& b.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else if op=2 then (a.1 ^^^ (a.1 &&& b.1),a.2 ^^^ (a.2 &&& b.2))
  else (b.1 ^^^ (b.1 &&& a.1),b.2 ^^^ (b.2 &&& a.2))
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp op (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (dbin op (a x) (b x)).2) xs := by
  by_cases h0 : op=0
  · simp only [packedOp,h0,ite_true,packedSig,lanes_and,dbin,bv]
  by_cases h1 : op=1
  · simp [packedOp,h1,packedSig,lanes_or,dbin,bv]
  by_cases h2 : op=2
  · simp [packedOp,h2,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv]
  · have e (x y : Bits) : ~~~x &&& y = y &&& ~~~x := BitVec.and_comm _ _
    simp only [packedOp,h0,h1,h2,ite_false,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv,e]

def takePacked (c : PackedCov) (a b : Nat) (ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2

theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) ka kb) xs := by
  cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]

def contextWire (c : NodeContext) (i : Nat) := c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  evalMove c op a b (dbin op a b) ka kb
def combField (c : NodeContext) (d ka kb : Bool) (op i j : Nat) :=
  let a := contextWire c i
  let b := contextWire c j
  restCov c.2.2.2.1.1 (column d a.2) (column d b.2) ka kb |||
    column d (dbin op a b).2

def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 153) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (153*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
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
      apply ih (mask:=mask >>> 153) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn

abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]

theorem masked_comp (d x : Sig) : masked d (neg x) = d ^^^ masked d x := by
  apply bit_ext
  intro r
  simp only [masked,neg,bit,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_xor,r.isLt,decide_true,Bool.true_and]
  cases d.getLsbD r.val <;> cases x.getLsbD r.val <;> rfl
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

theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b kb ≤
    (delTwo ws a b ka kb).countP p := by
  have h1 := lossBound p ws a ka
  have h2 := lossBound p (delOne ws a ka) b kb
  simp only [delTwo]
  omega

noncomputable def force {β : Type} (n : Nat) (f : Nat → β) : β := Nat.rec (f 0) (fun k _ => f (Nat.succ k)) n
theorem force_eq {β : Type} (n : Nat) (f : Nat → β) : force n f = f n := by cases n <;> rfl
noncomputable def forceMap {α β : Type} (f : α → Nat) (l : List α) : (List Nat → β) → β :=
  List.rec (fun k => k []) (fun a _ ih k => force (f a) fun x => ih fun xs => k (x::xs)) l
theorem forceMap_eq {α β : Type} (f : α → Nat) (l : List α) (k : List Nat → β) : forceMap f l k = k (l.map f) := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih =>
    change force (f a) (fun x => forceMap f l fun xs => k (x::xs)) = _
    rw [force_eq,ih]
    rfl
def nmask (d : Nat) (a : Sig) : Nat := Nat.land a.toNat d
noncomputable def anyEq (m : Nat) (l : List Nat) : Bool := List.rec false (fun v _ ih => or (Nat.beq m v) ih) l
def nconst (d m : Nat) : Bool := or (Nat.beq m 0) (Nat.beq m d)
noncomputable def navail (u : Bool) (d : Nat) (pm : List Nat) (m : Nat) : Bool :=
  or (or (nconst d m) (anyEq m pm)) (and u (anyEq (Nat.xor d m) pm))
theorem nmask_eq (d a : Sig) : nmask d.toNat a = (masked d a).toNat := (BitVec.toNat_and _ _).symm
theorem beq_toNat (a b : Sig) : Nat.beq a.toNat b.toNat = (a==b) := by
  rw [Bool.eq_iff_iff,Nat.beq_eq,beq_iff_eq]
  exact BitVec.toNat_inj
theorem nconst_eq (d a : Sig) : nconst d.toNat (nmask d.toNat a) = isMaskedConstant d a := by
  rw [nmask_eq]
  have e : Nat.beq (masked d a).toNat 0 = (masked d a == zero) := by
    have z0 : zero.toNat=0 := by simp [zero]
    rw [←beq_toNat,z0]
  rw [nconst,e,beq_toNat]
  rfl
theorem anyEq_eq (x d : Sig) (pool : List Sig) : anyEq x.toNat (pool.map (nmask d.toNat)) = (pool.map (masked d)).any (fun v => v==x) := by
  induction pool with
  | nil => rfl
  | cons a l ih =>
    change or (Nat.beq x.toNat (nmask d.toNat a)) (anyEq x.toNat (l.map (nmask d.toNat))) = _
    rw [ih,nmask_eq,beq_toNat,List.map_cons,List.any_cons,Bool.beq_comm]
theorem navail_eq (u : Bool) (d a : Sig) (pool : List Sig) :
    navail u d.toNat (pool.map (nmask d.toNat)) (nmask d.toNat a) = availableB u d pool a := by
  have x : Nat.xor d.toNat (masked d a).toNat = (masked d (neg a)).toNat := by
    rw [masked_comp]
    exact (BitVec.toNat_xor _ _).symm
  rw [navail,nconst_eq,nmask_eq,x,anyEq_eq,anyEq_eq]
  simp only [availableB,isMaskedConstant]
def unav (u : Bool) (p : BoundPool) (w : Decor) : Nat := cond (availableB u p.domain p.wires w.1) 0 1
def slowCost (u : Bool) (p : BoundPool) (ws : List Decor) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) : Bool :=
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let cm := ws.countP const - constantLoss const a ka - constantLoss const b kb + (isMaskedConstant p.domain z).toNat
  (((ws.map (unav u p)).sum == cond ka 0 (unav u p a) + cond kb 0 (unav u p b)) &&
    decide (k+p.paid+(!availableB u p.domain p.wires z).toNat < p.bound+cm)) &&
    (availableB u p.domain p.wires z || (availableB u p.domain p.wires a.1 && availableB u p.domain p.wires b.1))
def zN (op x y : Nat) : Nat := cond (Nat.beq op 0) (Nat.land x y) (cond (Nat.beq op 1) (Nat.lor x y)
  (cond (Nat.beq op 2) (Nat.xor x (Nat.land x y)) (Nat.xor y (Nat.land x y))))
theorem zN_eq (op : Nat) (d a b : Sig) : zN op (nmask d.toNat a) (nmask d.toNat b) = nmask d.toNat (bin op a b) := by
  have tn (x y : Sig) : Nat.land x.toNat y.toNat = (x &&& y).toNat := (BitVec.toNat_and x y).symm
  have tx (x y : Sig) : Nat.xor x.toNat y.toNat = (x ^^^ y).toNat := (BitVec.toNat_xor x y).symm
  have tor (x y : Sig) : Nat.lor x.toNat y.toNat = (x ||| y).toNat := (BitVec.toNat_or x y).symm
  simp only [nmask_eq]
  unfold zN
  by_cases h0 : op=0
  · subst h0
    change Nat.land _ _ = _
    rw [tn]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,ite_true,BitVec.getLsbD_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  by_cases h1 : op=1
  · subst h1
    change Nat.lor _ _ = _
    rw [tor]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,Nat.one_ne_zero,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e0 : Nat.beq op 0=false := Bool.eq_false_iff.mpr (fun h => h0 (Nat.eq_of_beq_eq_true h))
  have e1 : Nat.beq op 1=false := Bool.eq_false_iff.mpr (fun h => h1 (Nat.eq_of_beq_eq_true h))
  by_cases h2 : op=2
  · subst h2
    change Nat.xor _ (Nat.land _ _) = _
    rw [tn,tx]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,OfNat.ofNat_ne_zero,OfNat.ofNat_ne_one,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e2 : Nat.beq op 2=false := Bool.eq_false_iff.mpr (fun h => h2 (Nat.eq_of_beq_eq_true h))
  rw [e0,e1,e2]
  change Nat.xor _ (Nat.land _ _) = _
  rw [tn,tx]
  congr 1
  apply bit_ext
  intro r
  simp only [masked,bin,bit,h0,h1,h2,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
  cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
def nloss (d x : Nat) (keep : Bool) : Nat := cond keep 0 (cond (nconst d x) 1 0)
theorem nloss_eq (d : Sig) (a : Decor) (keep : Bool) :
    nloss d.toNat (nmask d.toNat a.1) keep = constantLoss (fun w : Decor => isMaskedConstant d w.1) a keep := by
  rw [nloss,nconst_eq,constantLoss]
  cases keep
  · cases isMaskedConstant d a.1 <;> rfl
  · rfl
abbrev QS := Nat × Nat × Nat × Nat × Nat × List Nat × List Nat × Bool
noncomputable def quickSpec (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) : QS :=
  let d := p.domain.toNat
  let ms := ws.map (fun w : Decor => nmask d w.1)
  (d,ms.countP (nconst d),p.bound,Nat.add k p.paid,(ms.map fun m => cond (navail u d (p.wires.map (nmask d)) m) 0 1).sum,ms,p.wires.map (nmask d),u)
noncomputable def forceBool {β : Type} (b : Bool) (f : Bool → β) : β := Bool.rec (f false) (f true) b
noncomputable def forcePool {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) (f : QS → β) : β :=
  force p.domain.toNat fun d => forceMap (nmask d) p.wires fun pm => forceMap (fun w : Decor => nmask d w.1) ws fun ms =>
  force (ms.countP (nconst d)) fun c => force p.bound fun l => force (Nat.add k p.paid) fun t =>
  force (ms.map fun m => cond (navail u d pm m) 0 1).sum fun v => forceBool u fun u => f (d,c,l,t,v,ms,pm,u)
theorem forcePool_eq {β : Type} (u k ws p) (f : QS → β) : forcePool u k ws p f = f (quickSpec u k ws p) := by
  have e (b : Bool) (f : Bool → β) : forceBool b f = f b := by cases b <;> rfl
  simp only [forcePool,force_eq,forceMap_eq,e]
  rfl
noncomputable def forcePools {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (ps : List BoundPool) : (List QS → β) → β :=
  List.rec (fun f => f []) (fun p _ ih f => forcePool u k ws p fun q => ih fun qs => f (q::qs)) ps
theorem forcePools_eq {β : Type} (u k ws ps) (f : List QS → β) : forcePools u k ws ps f = f (ps.map (quickSpec u k ws)) := by
  induction ps generalizing f with
  | nil => rfl
  | cons p ps ih =>
    change forcePool u k ws p (fun q => forcePools u k ws ps fun qs => f (q::qs)) = _
    rw [forcePool_eq,ih]
    rfl
def kwN (v : Nat) : Nat :=
  let n := v % 2305843009213693921
  (n*(n+971)) % 2305843009213693921
abbrev Lane := NodeContext × Nat × Nat × List QS × List Nat × Nat
noncomputable def laneOf (c : NodeContext) : Lane :=
  let ws := c.2.2.1.map (fun w : Decor => w.1.toNat)
  (c,c.2.2.1.length,cond c.2.2.2.1.2 4 2,c.2.2.2.2.1.map (quickSpec c.2.2.2.1.2 (c.1-1) c.2.2.1),ws,(ws.map kwN).sum)
noncomputable def forceLanes {β : Type} (cs : List NodeContext) : (List Lane → β) → β :=
  List.rec (fun f => f []) (fun c _ ih f => force c.2.2.1.length fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
    forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
    forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => ih fun ys => f ((c,n,l,qs,ws,t)::ys)) cs
theorem forceLanes_eq {β : Type} (cs) (f : List Lane → β) : forceLanes cs f = f (cs.map laneOf) := by
  induction cs generalizing f with
  | nil => rfl
  | cons c cs ih =>
    change force c.2.2.1.length (fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
      forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
      forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => forceLanes cs fun ys => f ((c,n,l,qs,ws,t)::ys)) = _
    rw [force_eq,force_eq,forceMap_eq,force_eq,forcePools_eq,ih]
    rfl
noncomputable def fastCost (s : QS) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (s.2.2.2.2.2.1.getD i 0) fun x => force (s.2.2.2.2.2.1.getD j 0) fun y =>
  let av := navail s.2.2.2.2.2.2.2 s.1 s.2.2.2.2.2.2.1
  let hi := Nat.add s.2.2.1 (Nat.sub (Nat.sub s.2.1 (nloss s.1 x ka)) (nloss s.1 y kb))
  let lo := s.2.2.2.1
  and (Nat.beq s.2.2.2.2.1 (Nat.add (cond ka 0 (cond (av x) 0 1)) (cond kb 0 (cond (av y) 0 1))))
  (cond (Nat.ble (Nat.succ lo) hi)
    (force (zN op x y) fun z => or (av z) (and (Nat.ble (Nat.add lo 2) hi) (and (av x) (av y))))
    (cond (Nat.ble lo hi) (nconst s.1 (zN op x y)) false))
theorem spec_get {d : Nat} (ws : List Decor) (i : Nat) (hd : nmask d zero=0) :
    (ws.map (fun w : Decor => nmask d w.1)).getD i 0 = nmask d (ws.getD i defaultDecor).1 := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none => exact hd.symm
  | some v => rfl
theorem fast_slow {u k p ws i j op ka kb} (h : fastCost (quickSpec u k ws p) i j op ka kb=true) :
    slowCost u p ws k (ws.getD i defaultDecor) (ws.getD j defaultDecor) op ka kb=true := by
  have z0 : nmask p.domain.toNat zero=0 := by
    have : zero.toNat=0 := by simp [zero]
    simp [nmask,this]
  have su : (((ws.map (fun w : Decor => nmask p.domain.toNat w.1)).map fun m => cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) m) 0 1).sum) =
      (ws.map (unav u p)).sum := by
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left ?_)
    intro w _
    change cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) (nmask p.domain.toNat w.1)) 0 1 = _
    rw [navail_eq]
    rfl
  simp only [fastCost,quickSpec,force_eq,spec_get _ _ z0,su,List.countP_map,Function.comp_def,nconst_eq] at h
  generalize ws.getD i defaultDecor=a at h ⊢
  generalize ws.getD j defaultDecor=b at h ⊢
  replace h : and (Nat.beq (ws.map (unav u p)).sum (Nat.add (cond ka 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) 0 1)) (cond kb 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)) 0 1))))
   (cond (Nat.ble (Nat.succ (Nat.add k p.paid)) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb))))
    (or ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) (and (Nat.ble (Nat.add (Nat.add k p.paid) 2) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (and ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)))))
    (cond (Nat.ble (Nat.add k p.paid) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (nconst p.domain.toNat (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) false)) = true := h
  rw [zN_eq,nconst_eq,navail_eq,navail_eq,navail_eq,nloss_eq,nloss_eq] at h
  have ca : isMaskedConstant p.domain (bin op a.1 b.1)=true → availableB u p.domain p.wires (bin op a.1 b.1)=true := by
    intro zc
    simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
    exact Or.inl (Or.inl zc)
  simp only [Nat.add_eq,Nat.sub_eq,Nat.succ_eq_add_one,Bool.and_eq_true,Nat.beq_eq] at h
  obtain ⟨hu,h⟩ := h
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]
  refine ⟨⟨hu,?_⟩,?_⟩
  all_goals
    generalize ws.countP (fun w => isMaskedConstant p.domain w.1) - constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) a ka -
      constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) b kb = c at h ⊢
    generalize isMaskedConstant p.domain (bin op a.1 b.1)=r at h ca ⊢
    generalize availableB u p.domain p.wires (bin op a.1 b.1)=q at h ca ⊢
    cases h1 : Nat.ble (k+p.paid+1) (p.bound+c)
    · rw [h1] at h
      cases h2 : Nat.ble (k+p.paid) (p.bound+c)
      · simp [h2] at h
      · have := Nat.ble_eq.mp h2
        simp only [h2,cond_true,cond_false] at h
        subst h
        rw [ca rfl]
        simp <;> omega
    · rw [h1] at h
      have l1 := Nat.ble_eq.mp h1
      simp only [cond_true,Bool.or_eq_true,Bool.and_eq_true,Nat.ble_eq] at h
      rcases h with rfl | ⟨l2,ha,hb⟩
      · simp <;> omega
      · first
        | (have : (!q).toNat ≤ 1 := Bool.toNat_le _
           omega)
        | simp [ha,hb]

theorem anyEq_iff (m : Nat) (l : List Nat) : anyEq m l=true ↔ m ∈ l := by
  induction l with
  | nil => simp [anyEq]
  | cons a l ih =>
    change or (Nat.beq m a) (anyEq m l)=true ↔ _
    rw [Bool.or_eq_true,ih,Nat.beq_eq,List.mem_cons]
noncomputable def linkAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (l.2.2.2.2.1.getD i 0) fun x => force (l.2.2.2.2.1.getD j 0) fun y => force (zN op x y) fun z =>
  Option.rec false (fun ys => forceMap (fun v => v) ys fun ys =>
    and (anyEq z ys) (and (l.2.2.2.2.1.all fun v => or (and (not ka) (Nat.beq v x)) (or (and (not kb) (Nat.beq v y)) (anyEq v ys)))
      (ys.all fun v => or (Nat.beq v z) (and (and (or ka (not (Nat.beq v x))) (or kb (not (Nat.beq v y)))) (anyEq v l.2.2.2.2.1)))))
    (fl (Nat.add (kwN z) (Nat.sub (Nat.sub l.2.2.2.2.2 (cond ka 0 (kwN x))) (cond kb 0 (kwN y)))))
theorem keySet_sum (xs : List Sig) : keySet xs = (xs.map keyWord).sum := by
  have go (a : Nat) : xs.foldl (fun v x => v+keyWord x) a = a+(xs.map keyWord).sum := by
    induction xs generalizing a with
    | nil => rfl
    | cons x xs ih => rw [List.foldl_cons,ih,List.map_cons,List.sum_cons,Nat.add_assoc]
  exact (go 0).trans (Nat.zero_add _)
theorem delTwo_sum (f : Decor → Nat) {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) (ka kb : Bool) :
    ((delTwo ws a b ka kb).map f).sum = (ws.map f).sum - (cond ka 0 (f a)) - (cond kb 0 (f b)) := by
  have er {l : List Decor} {x : Decor} (hx : x ∈ l) : (l.map f).sum = f x + ((l.erase x).map f).sum := by
    have := ((List.perm_cons_erase hx).map f).sum_eq
    rwa [List.map_cons,List.sum_cons] at this
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  have e1 := er ha
  have e2 := er hb
  have e3 := er hm
  cases ka <;> cases kb <;> simp only [delTwo,delOne,Bool.false_eq_true,ite_true,ite_false,cond_true,cond_false] <;> omega
theorem fastCost_good {u p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws) (ne : a≠b) (al : allowedB u op=true)
    (h : slowCost u p ws k a b op ka kb=true) :
    scalarPoolCut u p k ((delTwo ws a b ka kb).map Prod.fst) (movedChoice op a b)=true := by
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let rest := delTwo ws a b ka kb
  have ck := keptCount const ws a b ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b kb ≤ rest.countP const at ck
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  obtain ⟨⟨hu,hc⟩,hz⟩ := h
  have sum := delTwo_sum (unav u p) ha hb ne ka kb
  rw [hu] at sum
  have zs : ((delTwo ws a b ka kb).map (unav u p)).sum=0 := by omega
  have hs : (rest.map Prod.fst).all (availableB u p.domain p.wires)=true := by
    apply List.all_eq_true.mpr
    intro _ hm
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
    have v := List.sum_eq_zero_iff.mp zs _ (List.mem_map_of_mem hw)
    cases e : availableB u p.domain p.wires w.1
    · simp [unav,e] at v
    · rfl
  have opOK : (!(!availableB u p.domain p.wires z) || choiceOK u p.domain p.wires (movedChoice op a b))=true := by
    simp only [Bool.or_eq_true,Bool.and_eq_true] at hz
    rcases hz with hz | ⟨x,y⟩
    · simp [z,hz]
    · simp [choiceOK,movedChoice,x,y,al]
  change k+p.paid+(!availableB u p.domain p.wires z).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b kb+(isMaskedConstant p.domain z).toNat) at hc
  dsimp only [rest] at hs
  have ez : choiceVal (movedChoice op a b)=z := rfl
  simp only [scalarPoolCut,ez,hs,opOK,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
  change k+p.paid+(!availableB u p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
  cases hc' : isMaskedConstant p.domain z <;> simp [hc'] at hc ⊢ <;> omega

theorem zN_full (op : Nat) (a b : Sig) : zN op a.toNat b.toNat = (bin op a b).toNat := by
  have e (v : Sig) : nmask one.toNat v = v.toNat := by
    rw [nmask_eq]
    congr 1
    exact BitVec.and_allOnes
  have := zN_eq op one a b
  rwa [e,e,e] at this
theorem getW (ws : List Decor) (i : Nat) :
    (ws.map (fun w : Decor => w.1.toNat)).getD i 0 = (ws.getD i defaultDecor).1.toNat := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none =>
    have z0 : zero.toNat=0 := by simp [zero]
    exact z0.symm
  | some v => rfl
theorem wire_ne {c : NodeContext} {i j} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) : (contextWire c i).1 ≠ (contextWire c j).1 := by
  have gi : contextWire c i = c.2.2.1[i] := by simp [contextWire,List.getD_eq_getElem?_getD,hi]
  have gj : contextWire c j = c.2.2.1[j] := by simp [contextWire,List.getD_eq_getElem?_getD,hj]
  rw [gi,gj]
  intro e
  apply hij
  apply (List.Nodup.getElem_inj_iff nd (hi:=by simpa using hi) (hj:=by simpa using hj)).mp
  simpa using e
theorem link_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) (h : linkAt fl (laneOf c) i j op ka kb=true) :
    (c.2.2.2.2.2 (keySet (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))).any (sameWords
      (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  have hne := wire_ne nd hi hj hij
  have ha := mem i hi
  have hb := mem j hj
  have hab : contextWire c i ≠ contextWire c j := fun e => hne (congrArg Prod.fst e)
  have kv (v : Sig) := kept_value nd ha hb ka kb v
  have sum := delTwo_sum (fun w : Decor => keyWord w.1) ha hb hab ka kb
  have wi : contextWire c i = c.2.2.1.getD i defaultDecor := rfl
  have wj : contextWire c j = c.2.2.1.getD j defaultDecor := rfl
  simp only [linkAt,laneOf,force_eq,getW,←wi,←wj,zN_full] at h
  generalize contextWire c i=a at *
  generalize contextWire c j=b at *
  change Option.rec false _ (fl (keyWord (bin op a.1 b.1)+(((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum -
    (cond ka 0 (keyWord a.1)) - (cond kb 0 (keyWord b.1)))))=true at h
  have tot : ((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum = (c.2.2.1.map (fun w : Decor => keyWord w.1)).sum := by
    rw [List.map_map]
    rfl
  rw [tot,←sum] at h
  have tag : keySet (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst) =
      keyWord (bin op a.1 b.1)+((delTwo c.2.2.1 a b ka kb).map (fun w : Decor => keyWord w.1)).sum := by
    rw [keySet_sum,List.map_cons,List.sum_cons,List.map_map]
    rfl
  rw [←tag] at h
  generalize keySet (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst)=t at h ⊢
  cases hf : fl t with
  | none => simp [hf] at h
  | some ys =>
    obtain ⟨xs,hx,rfl⟩ := hfl t ys hf
    rw [hf] at h
    simp only [forceMap_eq,List.map_id',Bool.and_eq_true,List.all_eq_true,Bool.or_eq_true,anyEq_iff,Nat.beq_eq,Bool.not_eq_true'] at h
    obtain ⟨h1,h2,h3⟩ := h
    have back {v : Sig} (hv : v.toNat ∈ xs.map BitVec.toNat) : v ∈ xs := by
      obtain ⟨w,hw,e⟩ := List.mem_map.mp hv
      exact BitVec.toNat_inj.mp e ▸ hw
    apply List.any_eq_true.mpr
    refine ⟨xs,hx,?_⟩
    simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq]
    constructor
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact back h1
      · obtain ⟨hw,va,vb⟩ := (kv v).mp hv
        obtain ⟨w,hm,rfl⟩ := List.mem_map.mp hw
        rcases h2 _ (List.mem_map_of_mem hm) with ⟨x,y⟩ | ⟨x,y⟩ | x
        · rcases va with va | va
          · exact absurd (BitVec.toNat_inj.mp y) va
          · simp [va] at x
        · rcases vb with vb | vb
          · exact absurd (BitVec.toNat_inj.mp y) vb
          · simp [vb] at x
        · exact back x
    · intro v hv
      rcases h3 _ (List.mem_map_of_mem hv) with x | ⟨⟨x,y⟩,m⟩
      · exact List.mem_cons.mpr (Or.inl (BitVec.toNat_inj.mp x))
      · refine List.mem_cons_of_mem _ ((kv v).mpr ⟨?_,?_,?_⟩)
        · obtain ⟨w,hw,e⟩ := List.mem_map.mp m
          exact BitVec.toNat_inj.mp e ▸ List.mem_map_of_mem hw
        · rcases x with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
        · rcases y with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
noncomputable def fallbackAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  or (and (and (Nat.ble (Nat.succ i) l.2.1) (and (Nat.ble (Nat.succ j) l.2.1) (and (Nat.ble (Nat.succ op) l.2.2.1) (not (Nat.beq i j)))))
    (or (l.2.2.2.1.any fun s => fastCost s i j op ka kb) (linkAt fl l i j op ka kb))) (checkAt l.1 i j op ka kb)
theorem fallback_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (h : fallbackAt fl (laneOf c) i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true,Bool.and_eq_true] at h
  rcases h with ⟨⟨hi,hj,ho,hn⟩,h | h⟩ | h
  · have hi := Nat.ble_eq.mp hi
    have hj := Nat.ble_eq.mp hj
    have ho := Nat.ble_eq.mp ho
    change Nat.succ i ≤ c.2.2.1.length at hi
    change Nat.succ j ≤ c.2.2.1.length at hj
    change Nat.succ op ≤ cond c.2.2.2.1.2 4 2 at ho
    have al : allowedB c.2.2.2.1.2 op=true := by
      cases hu : c.2.2.2.1.2 <;> simp [hu] at ho <;> simp [allowedB] <;> omega
    have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
      simp [contextWire,List.getD_eq_getElem?_getD,ht]
    obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    have hne := wire_ne nd hi hj (fun e => by simp [e] at hn)
    have closed := fastCost_good (mem i hi) (mem j hj) (fun e => hne (congrArg Prod.fst e)) al (fast_slow ok)
    have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut c.2.2.2.1.2 p (c.1-1)
        ((delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst)
        (movedChoice op (contextWire c i) (contextWire c j)))=true :=
      List.any_eq_true.mpr ⟨p,hp,closed⟩
    simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
    repeat' split
    all_goals rfl
  · have cut := link_sound nd hfl (Nat.ble_eq.mp hi) (Nat.ble_eq.mp hj) (fun e => by simp [e] at hn) h
    simp only [checkAt,evalMove,closeChild,cut,Bool.true_or]
    repeat' split
    all_goals rfl
  · exact h
def swapIdx (v t : Nat) : Nat := cond (Nat.beq t (v &&& 15)) (v >>> 4) (cond (Nat.beq t (v >>> 4)) (v &&& 15) t)
def validSwap (v : Nat) : Bool := and (Nat.ble ((v &&& 15)+1) (v >>> 4)) (Nat.ble ((v >>> 4)+1) 9)
set_option maxRecDepth 8192 in
theorem swap_table : ∀ v : Fin 144, validSwap v.val=true → ∀ t : Fin 9, swapIdx v.val t.val<9 ∧
    wordMove (swapRows v.val) (inputs.getD t.val zero) = inputs.getD (swapIdx v.val t.val) zero := by decide +kernel
theorem swap_input {v t : Nat} (hv : validSwap v=true) (ht : t<9) : swapIdx v t<9 ∧
    wordMove (swapRows v) (inputs.getD t zero) = inputs.getD (swapIdx v t) zero := by
  have lt : v<144 := by
    simp only [validSwap,Bool.and_eq_true,Nat.ble_eq,Nat.shiftRight_eq_div_pow] at hv
    omega
  exact swap_table ⟨v,lt⟩ hv ⟨t,ht⟩
def idxOf (perm : List Nat) (t : Nat) : Nat := perm.foldl (fun t v => swapIdx v t) t
theorem idx_move {perm : List Nat} (ok : perm.all validSwap=true) {t : Nat} (ht : t<9) :
    movedWord (perm.map swapRows).reverse (inputs.getD t zero) = inputs.getD (idxOf perm t) zero := by
  rw [movedWord,List.foldr_reverse,List.foldl_map]
  induction perm generalizing t with
  | nil => rfl
  | cons v perm ih =>
    simp only [List.all_cons,Bool.and_eq_true] at ok
    obtain ⟨lt,e⟩ := swap_input ok.1 ht
    rw [List.foldl_cons,e,ih ok.2 lt]
    rfl
noncomputable def decodeN : Nat → Nat → List Nat → List Nat
  | 0,_,ws => ws
  | n+1,bits,ws => force (zN ((bits >>> 8) &&& 3) (ws.getD (bits &&& 15) 0) (ws.getD ((bits >>> 4) &&& 15) 0))
      fun z => decodeN n (bits >>> 10) (ws++[z])
theorem decodeN_eq (F : Sig → Nat) (F0 : F zero=0) (Fb : ∀ op a b, F (bin op a b)=zN op (F a) (F b))
    (n bits : Nat) (ds : List Decor) :
    (decodeBank n bits ds).map (fun w => F w.1) = decodeN n bits (ds.map fun w => F w.1) := by
  have gd (ds : List Decor) (i : Nat) : (ds.map fun w => F w.1).getD i 0 = F (ds.getD i defaultDecor).1 := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
    cases ds[i]? with
    | none => exact F0.symm
    | some v => rfl
  induction n generalizing bits ds with
  | zero => rfl
  | succ n ih =>
    rw [decodeN,force_eq,decodeBank,ih,gd,gd,←Fb,List.map_append]
    rfl
theorem selectLive_map {α β : Type} (f : α → β) (bits : Nat) (ws : List α) :
    (selectLive bits ws).map f = selectLive bits (ws.map f) := by
  induction ws generalizing bits with
  | nil => rfl
  | cons w ws ih =>
    rw [List.map_cons,selectLive,selectLive]
    split
    · rw [List.map_cons,ih]
    · exact ih _
noncomputable def fastState (g : Forest) (k i : Nat) (perm : List Nat) : List Nat :=
  let raw := (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*depth
  force (forestRecord (g.levels k) (selected g.mask).length i) fun rec =>
  selectLive (rec >>> len) (decodeN depth (rec &&& ((1 <<< len)-1)) raw)
theorem fastState_eq (g : Forest) (k i : Nat) {perm : List Nat} (ok : perm.all validSwap=true) :
    fastState g k i perm = ((stateSet g k i).map (movedWord (perm.map swapRows).reverse)).map BitVec.toNat := by
  let ms := (perm.map swapRows).reverse
  let F (a : Sig) : Nat := (movedWord ms a).toNat
  have F0 : F zero=0 := by
    change (movedWord ms zero).toNat=0
    rw [moved_eq_rename,(rename_constants _).1]
    simp [zero]
  have Fb (op a b) : F (bin op a b)=zN op (F a) (F b) := by
    change (movedWord ms (bin op a b)).toNat = zN op (movedWord ms a).toNat (movedWord ms b).toNat
    rw [zN_full,moved_eq_rename,rename_bin,moved_eq_rename,moved_eq_rename]
  have raw : (wiresOf g).map (fun w => F w.1) = (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat := by
    simp only [wiresOf,rawDecor,List.map_map]
    apply List.map_congr_left
    rintro ⟨j,a⟩ hm
    obtain ⟨hj,rfl⟩ := selected_entry hm
    exact congrArg BitVec.toNat (idx_move ok hj)
  have len : (wiresOf g).length = (selected g.mask).length := by simp [wiresOf,rawDecor]
  unfold fastState stateSet readNode
  rcases g.levels k with ⟨a,depth,b,c,d,e,f,data⟩
  simp only [force_eq,storedDepth,len]
  rw [List.map_map,List.map_map,selectLive_map,←raw,←decodeN_eq F F0 Fb]
  rfl
noncomputable def linkedFast (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Nat) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).bind fun perm => cond (perm.all validSwap) (some (fastState g k pair.1 perm)) none
noncomputable def flOf (g : Forest) (k : Nat) : Nat → Option (List Nat) := fun tag => (g.index k tag).bind (linkedFast g (k-1))
noncomputable def batchMove (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,cov) := b
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  if len>k then true else
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp op a b'
    let mask := fullMarks r (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b') ka kb ||| packedColumn (!u) z)
    onMarks (fun c => fallbackAt fl c i j op ka kb) mask xs

theorem batchMove_at {fl u} (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (pass : batchMove fl u (makeBatch k n xs) (xs.map laneOf) i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] (!u) ka kb op i j != BitVec.allOnes 152 then true
      else if !properB (dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild u xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((delTwo xs[q].2.2.1 (contextWire xs[q] i) (contextWire xs[q] j) ka kb).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt,evalMove,budget,arity,mode,len,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b) ka kb |||
        packedColumn (!u) (packedOp op a b))) (xs.map laneOf)) = true at pass
    rw [if_neg small] at pass
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r,cov] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] (!u) ka kb op i j = BitVec.allOnes 152
    · apply fallback_sound nd hfl
      have m := marked_ok _ _ _ q (by simpa using hq) (by
        rw [mark_at _ _ _ hq]
        exact beq_iff_eq.mpr hit) pass
      simpa only [List.getElem_map] using m
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]

noncomputable def batchPair (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) :=
  let f := batchMove fl u b xs i j op
  f false false && f true false && f false true && f true true
noncomputable def batchRow (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i : Nat) (js : List Nat) :=
    js.all (fun j => (opsOf u).all (batchPair fl u b xs i j))
noncomputable def batchRows (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) : List Nat → Bool
  | [] => true
  | i::js => batchRow fl u b xs i js && batchRows fl u b xs js

theorem batchRows_at {fl u} (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows fl u (makeBatch k n xs) (xs.map laneOf) js=true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    refine ⟨?_,ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩ op hop
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    rw [mode] at hop
    have pass := allRows.1 j hj op hop
    have check := @batchMove_at fl u k n xs i j op
    simp only [batchPair,Bool.and_eq_true] at pass
    simp only [testPair,Bool.and_eq_true]
    exact ⟨⟨⟨check hi hj' hq budget arity mode nd hfl pass.1.1.1,check hi hj' hq budget arity mode nd hfl pass.1.1.2⟩,
      check hi hj' hq budget arity mode nd hfl pass.1.2⟩,check hi hj' hq budget arity mode nd hfl pass.2⟩

noncomputable def runBatch (fl : Nat → Option (List Nat)) (u : Bool) (k n : Nat) (xs : List NodeContext) :=
    batchRows fl u (makeBatch k n xs) (xs.map laneOf) (List.range n)
theorem runBatch_at {fl u k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hm : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (hn : xs[q].2.2.1.length=n)
    (pass : runBatch fl u k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha hm nd hfl (List.range n) (fun _ => List.mem_range.mp) pass
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
  let rules := (forestHints (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov g.mode ws,rules,ls)

theorem flOf_ok (g : Forest) (k i tag : Nat) (ys) (h : flOf g k tag=some ys) :
    ∃ xs ∈ (contextOf g k i).2.2.2.2.2 tag, ys=xs.map BitVec.toNat := by
  change ∃ xs ∈ ((g.index k tag).bind (linkedSet g (k-1))).toList, _
  unfold flOf at h
  cases hp : g.index k tag with
  | none => simp [hp] at h
  | some pair =>
    simp only [hp,Option.bind_some,linkedFast] at h
    simp only [Option.bind_some,linkedSet]
    split at h
    · contradiction
    next v =>
      cases ha : g.autos[pair.2]? with
      | none => simp [ha] at h
      | some perm =>
        simp only [ha,Option.bind_some] at h
        cases hv : perm.all validSwap with
        | false => simp [hv] at h
        | true =>
          simp only [hv,cond_true,Option.some.injEq] at h
          refine ⟨(stateSet g (k-1) pair.1).map (movedWord (perm.map swapRows).reverse),?_,?_⟩
          · simp [v]
          · exact h.symm.trans (fastState_eq g _ _ hv)

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
noncomputable def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  forceLanes xs fun ys => (List.range len).all (fun d =>
    let i := lo+d
    batchRow (flOf g k) g.mode b ys i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (flOf g k) g.mode (makeBatch k ar (contexts g k start n)) ((contexts g k start n).map laneOf)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  simp only [rowCut,forceLanes_eq] at h
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha

theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  simp only [rowCut,forceLanes_eq]
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)

theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch (flOf g k) g.mode k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (flOf g k) g.mode (makeBatch k ar xs) (xs.map laneOf) (List.range' lo num)=true := by
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
  have nd : (xs[q].2.2.1.map Prod.fst).Nodup := by
    have p := one.2
    simp only [prelim,Bool.and_eq_true,decide_eq_true_eq] at p
    rw [e]
    exact p.1
  have hfl : ∀ tag ys, flOf g k tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat := by
    rw [e]
    exact fun tag ys h => flOf_ok g k i tag ys h
  have hm : xs[q].2.2.2.1.2=g.mode := by rw [e]; rfl
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hm nd hfl hn (cutsRun h)

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
theorem pieces_all {α f xs d} (h : @listPieces α f xs d) : xs.all f=true := by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap : ((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true := by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap
theorem slice_self {u} {raw : List Sig} {T : Sig} {L : Nat} (pT : proper T) (h : Lower u raw T L) :
    Slice u raw T one L := by
  refine ⟨id,raw,fun r => bit_one r,fun a ha => ?_,observe_proper pT,h⟩
  exact Or.inl (List.mem_map_of_mem ha)

theorem plainA {u} {m q cap : Nat} {prior : Nat → Nat} (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (e : (graphGoal q == graphGoal m && (varsX q == vars m) && (prior q == cap+1) && properB (graphGoal m) &&
      decide (vars m).Nodup && poolCut u one (cap+1) cap 0 (vars m) (vars m)) = true) :
    Impossible u (graphGoal m) cap (vars m).toFinset := by
  simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at e
  obtain ⟨⟨⟨⟨⟨e1,e2⟩,e3⟩,e4⟩,e5⟩,e6⟩ := e
  have h := low q
  rw [e1,e2,e3] at h
  exact poolCut_sound (slice_self (proper_of _ e4) h) [] rfl e5 e6

theorem cut_root {u} {m cap : Nat} {prior : Nat → Nat} {ws : List Sig}
    (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q)) (ci : ColumnInfo)
    (ok : colCheck m ci prior = true)
    (cut : (decide ws.Nodup && poolCut u (subcube ci.1 ci.2.1) ci.2.2.2.2 cap 0 (varsX (rawMask m ci)) ws)=true) :
    Impossible u (graphGoal m) cap ws.toFinset := by
  simp only [Bool.and_eq_true,decide_eq_true_eq] at cut
  exact poolCut_sound (col_sound ci prior low ok) [] rfl cut.1 cut.2

theorem index_root {u} {g : Forest} {m cap i : Nat} {prior : Nat → Nat} {ws : List Sig}
    (hm : g.mask=m) (hu : g.mode=u) (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g cap)
    (idx : indexedRoot g cap i ws = true) : Impossible u (graphGoal m) cap ws.toFinset := by
  subst hm
  subst hu
  exact root_index low geom blocks (Nat.le_refl _) idx

def essOK (m hints : Nat) : Bool :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs && (xs.map Prod.fst == vars m)
theorem plain_low {u} {m hints cap : Nat} (ok : essOK m hints = true)
    (a : Impossible u (graphGoal m) cap (vars m).toFinset) : Lower u (vars m) (graphGoal m) (cap+1) := by
  simp only [essOK,Bool.and_eq_true,beq_iff_eq] at ok
  apply lower_impossible (proper_of _ ok.1.1) (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 _ a
  intro v hv
  apply essential_ok ok.1.2 v
  rw [ok.2]
  exact List.mem_toFinset.mpr hv

structure KWRooms (S : Finset Sig) (T : Sig) where
  owns : Sig → Row → Row → Prop
  total : ∀ p n, bit p T=true → bit n T=false → ∃ v, owns v p n
  valid : ∀ {v p n}, owns v p n → v∈S ∧ bit p v=true ∧ bit n v=false
  unique : ∀ {v w p n}, owns v p n → owns w p n → v=w
  rect : ∀ {v p n p' n'}, owns v p n' → owns v p' n → owns v p n

def kwLeaf (T : Sig) : KWRooms {T} T where
  owns v p n := v=T ∧ bit p T=true ∧ bit n T=false
  total p n hp hn := ⟨T,rfl,hp,hn⟩
  valid := by rintro v p n ⟨rfl,hp,hn⟩; exact ⟨by simp,hp,hn⟩
  unique := by rintro v w p n ⟨rfl,_,_⟩ ⟨eq,_,_⟩; exact eq.symm
  rect := by rintro v p n p' n' ⟨e,hp,_⟩ ⟨_,_,hn⟩; exact ⟨e,hp,hn⟩

def kwFork {U : Finset Sig} {T a b : Sig} {d : Nat} (d01 : d=0 ∨ d=1)
    (ha : a∉U) (hb : b∉U) (hz : bin d a b∉U)
    (H : KWRooms (insert (bin d a b) U) T) : KWRooms (insert a (insert b U)) T := by
  let z := bin d a b
  let sel := fun p n : Row => if d=0 then (if bit n a then b else a)
    else (if bit p a then a else b)
  have pick (p n) : sel p n=a ∨ sel p n=b := by
    dsimp only [sel]; split <;> split <;> simp
  have outside (p n) : sel p n ∉ U := by
    rcases pick p n with eq | eq
    · simpa only [eq] using ha
    · simpa only [eq] using hb
  have separates (p n) (hp : bit p z=true) (hn : bit n z=false) :
      bit p (sel p n) = true ∧ bit n (sel p n) = false := by
    have b0 (r : Row) : bit r (bin 0 a b) = (bit r a && bit r b) := by simp [bin,bit]
    have b1 (r : Row) : bit r (bin 1 a b) = (bit r a || bit r b) := by simp [bin,bit]
    rcases d01 with e | e <;> cases pA : bit p a <;> cases nA : bit n a <;>
      simp_all [sel,z]
  refine { owns := fun v p n => (v∈U ∧ H.owns v p n) ∨ (v=sel p n ∧ H.owns z p n)
           total := ?_
           valid := ?_
           unique := ?_
           rect := ?_ }
  · intro p n hp hn
    obtain ⟨v,hv⟩ := H.total p n hp hn
    rcases Finset.mem_insert.mp (H.valid hv).1 with eq | mem
    · have vz : v=z := eq
      refine ⟨sel p n,Or.inr ⟨rfl,?_⟩⟩
      rw [←vz]
      exact hv
    · exact ⟨v,Or.inl ⟨mem,hv⟩⟩
  · intro v p n h
    rcases h with ⟨mem,hv⟩ | ⟨e,hv⟩
    · exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem mem),(H.valid hv).2⟩
    · subst v
      have inS : sel p n ∈ insert a (insert b U) := by
        rcases pick p n with eq | eq <;> simp [eq]
      exact ⟨inS,separates p n (H.valid hv).2.1 (H.valid hv).2.2⟩
  · intro v w p n h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨ve,hv⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨we,hw⟩
    · exact H.unique hv hw
    · apply False.elim
      apply hz
      change z∈U
      rw [←H.unique hv hw]
      exact vU
    · apply False.elim
      apply hz
      change z∈U
      rw [←H.unique hw hv]
      exact wU
    · exact ve.trans we.symm
  · intro v p n p' n' h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨ve,hv⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨we,hw⟩
    · exact Or.inl ⟨vU,H.rect hv hw⟩
    · exact False.elim (outside p' n (we ▸ vU))
    · exact False.elim (outside p n' (ve ▸ wU))
    · refine Or.inr ⟨?_,H.rect hv hw⟩
      by_cases h : d=0
      · simpa only [sel,h,ite_true] using we
      · simpa only [sel,h,ite_false] using ve

theorem kwWidth {u T k S} (h : Live u T k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf tail ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a:=a) (insert b U)
    have h2 := Finset.card_insert_le (a:=b) U
    omega

theorem kwTight {T k S} (run : Live false T k S) (tight : S.card=k+1) :
    Nonempty (KWRooms S T) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,_⟩ := run
    exact ⟨kwLeaf T⟩
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,_,_,hab,hfresh,tail⟩ := run
    have fresh : bin d a b∉U := fun h => hfresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have li := kwWidth tail
    rw [Finset.card_insert_of_notMem fresh] at li
    have le1 := Finset.card_insert_le (a:=a) (insert b U)
    have le2 := Finset.card_insert_le (a:=b) U
    have ha : a∉U := by
      intro h
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem h : a∈insert b U)] at tight
      omega
    have hb : b∉U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight le1
      omega
    have eq : (insert (bin d a b) U).card=k+1 := by
      rw [Finset.card_insert_of_notMem fresh]
      omega
    obtain ⟨H⟩ := ih tail eq
    have d01 : d=0 ∨ d=1 := by rcases hd with h | ⟨h,_⟩ <;> simp_all <;> omega
    exact ⟨kwFork d01 ha hb fresh H⟩

def onlyWire (S : Finset Sig) (T v : Sig) (p n : Row) :=
  bit p T=true ∧ bit n T=false ∧ ∀ w∈S, bit p w=true → bit n w=false → w=v

theorem kwOwn {S T v p n} (H : KWRooms S T) (one : onlyWire S T v p n) : H.owns v p n := by
  obtain ⟨w,hw⟩ := H.total p n one.1 one.2.1
  have eq := one.2.2 w (H.valid hw).1 (H.valid hw).2.1 (H.valid hw).2.2
  exact eq ▸ hw

theorem kwCross {S T k a b p n pa pb na nb} (size : k+1=S.card) (different : a≠b)
    (A : onlyWire S T a p na) (B : onlyWire S T b p nb)
    (C : onlyWire S T a pa n) (D : onlyWire S T b pb n) : Impossible false T k S := by
  intro j hj run
  have lb := kwWidth run
  have tight : S.card=j+1 := by omega
  obtain ⟨H⟩ := kwTight run tight
  exact different (H.unique (H.rect (kwOwn H A) (kwOwn H C)) (H.rect (kwOwn H B) (kwOwn H D)))
def kwWireB (ws : List Sig) (T v : Sig) (p n : Row) : Bool :=
  bit p T && !bit n T && ws.all (fun w => !bit p w || bit n w || w==v)
theorem kwWireB_sound {ws T v p n} (h : kwWireB ws T v p n=true) :
    onlyWire ws.toFinset T v p n := by
  simp only [kwWireB,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at h
  refine ⟨h.1.1,h.1.2,?_⟩
  intro w hw hp hn
  simpa only [hp,hn,Bool.not_true,Bool.false_or,beq_iff_eq] using
    h.2 w (List.mem_toFinset.mp hw)

def kwProbe (xs q : Nat) : Row := Fin.ofNat 512 ((xs >>> (9*q)) &&& 511)
def kwWord (pos neg : Nat) (T : Sig) (ws : List Sig) (k value : Nat) : Bool :=
  let field := fun i => (value >>> (4*i)) &&& 15
  let a := ws.getD (field 0) zero
  let b := ws.getD (field 1) zero
  let p := kwProbe pos (field 2)
  let n := kwProbe neg (field 3)
  decide (k+1=ws.toFinset.card) && decide (a≠b) &&
    kwWireB ws T a p (kwProbe neg (field 4)) && kwWireB ws T b p (kwProbe neg (field 5)) &&
    kwWireB ws T a (kwProbe pos (field 6)) n && kwWireB ws T b (kwProbe pos (field 7)) n
theorem kwWord_sound {pos neg T ws k v} (h : kwWord pos neg T ws k v=true) : Impossible false T k ws.toFinset := by
  simp only [kwWord,Bool.and_eq_true,decide_eq_true_eq] at h
  exact kwCross h.1.1.1.1.1 h.1.1.1.1.2 (kwWireB_sound h.1.1.1.2)
    (kwWireB_sound h.1.1.2) (kwWireB_sound h.1.2) (kwWireB_sound h.2)

def CutRow (g : Forest) (k start n : Nat) : Prop :=
  ∀ j, start≤j → j<start+n → nodeVerified g k j=true ∨ Impossible g.mode (targetOf g) k (stateSet g k j).toFinset
theorem mixedEmpty (g : Forest) (k a : Nat) : CutRow g k a 0 := by
  intro j lo hi
  omega
theorem checkedRow {g k a n} (h : block g k a n=true) : CutRow g k a n :=
  fun j lo hi => Or.inl (block_at h j lo hi)
theorem joinRow {g k a x y} (first : CutRow g k a x) (last : CutRow g k (a+x) y) :
    CutRow g k a (x+y) := by
  intro j lo hi
  by_cases e : j<a+x
  · exact first j lo e
  · exact last j (by omega) (by omega)
def kwTest (pos neg : Nat) (g : Forest) (k a n : Nat) (data : Nat → Nat) :=
  (List.range n).all (fun j => kwWord pos neg (targetOf g) (stateSet g k (a+j)) k (packedAt data (32*j) 32))
theorem mixedCut {pos neg g k a n data} (mode : g.mode=false) (h : kwTest pos neg g k a n data=true) :
    CutRow g k a n := by
  intro j lo hi
  right
  rw [mode]
  have hh := List.all_eq_true.mp h (j-a) (List.mem_range.mpr (by omega))
  have sum : a+(j-a)=j := by omega
  change kwWord pos neg _ (stateSet g k (a+(j-a))) k _=true at hh
  rw [sum] at hh
  exact kwWord_sound hh

def mixedTables (g : Forest) (top : Nat) := ∀ k ≤ top, CutRow g k 0 (g.levels k).1
theorem mixedForest (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geometry : graphValid g prior=true) (rows : mixedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    rcases rows 0 hk i (by omega) (by omega) with checked | done
    · exact nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
        (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega) checked
    · exact done
  | succ k ih =>
    intro hk i hi
    rcases rows _ hk i (by omega) (by omega) with checked | done
    · exact nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
        (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
        (fun _ => by simpa using ih (by omega)) checked
    · exact done
theorem mixedRoot {g top prior k i ws} (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior=true) (blocks : mixedTables g top) (le : k≤top)
    (idx : indexedRoot g k i ws=true) : Impossible g.mode (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact mixedForest g top prior lower geom blocks _ le i idx.1

def eightInputs : List Sig := vars 255
def sampleEight (r : Row) (i : Fin 8) : Bool := bit r (eightInputs.getD i.val zero)
def eightEdge (x : Fin 8 → Bool) := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 4) || (x 5 && x 7) || (x 6 && x 7)

theorem eightTable : ∀ r : Row, bit r graph = eightEdge (sampleEight r) := by decide +kernel
theorem eightList : List.ofFn (fun i : Fin 8 => eightInputs.getD i.val zero) = eightInputs := rfl
theorem eightSampled (r : Row) : List.ofFn (sampleEight r) = eightInputs.map (bit r) := by
  rw [← eightList, List.map_ofFn]
  rfl

theorem eightEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates eightInputs).getD i zero) =
      (C.wires (List.ofFn (sampleEight r))).getD i false := by
  rw [← b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),eightSampled]
  rfl
def neighbor8449 (i : Fin 8) : Nat := [1,0,0,0,0,1,2,5].getD i.val 0
def absentRow8449 (i : Fin 8) : Row := Fin.ofNat 512 (1 <<< neighbor8449 i)
def presentRow8449 (i : Fin 8) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor8449 i))

set_option maxHeartbeats 1000000 in
theorem requiredInputs :
    (∀ i : Fin 8, bit (absentRow8449 i) graph ≠ bit (presentRow8449 i) graph) ∧
    (∀ i j : Fin 8, i ≠ j →
      bit (absentRow8449 i) (eightInputs.getD j.val zero) =
      bit (presentRow8449 i) (eightInputs.getD j.val zero)) := by decide +kernel

theorem twoRoots (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 8 C = eightEdge) (small : C.size ≤ 13) :
    ∃ (u : Bool) (k : Nat), k ≤ (if u then 12 else 13) ∧ Live u graph k eightInputs.toFinset := by
  have goalEq : (execute C.gates eightInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (eightEval C legal C.output r).trans ((congrFun computes (sampleEight r)).trans (eightTable r).symm)
  have len : C.gates.length ≤ 13 := small
  have mode : ∃ u : Bool, (u=false → ∀ g ∈ C.gates, isNot g=false) ∧ C.gates.countP (fun g => !isNot g) ≤ (if u then 12 else 13) := by
    by_cases hn : ∀ g ∈ C.gates, isNot g=false
    · refine ⟨false,fun _ => hn,?_⟩
      have := List.countP_le_length (p:=fun g => !isNot g) (l:=C.gates)
      simp only [Bool.false_eq_true,ite_false]
      omega
    · refine ⟨true,by simp,?_⟩
      push Not at hn
      obtain ⟨g,hg,hx⟩ := hn
      have lt : C.gates.countP (fun g => !isNot g) < C.gates.length := by
        rcases Nat.lt_or_ge (C.gates.countP (fun g => !isNot g)) C.gates.length with h | h
        · exact h
        · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
          simp only [Bool.not_eq_true'] at eq
          exact absurd eq hx
      simp only [ite_true]
      omega
  obtain ⟨u,mono,count⟩ := mode

  have out := get_rep (u:=u) (execute C.gates eightInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract C.gates eightInputs legal mono graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : eightInputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ eightInputs) : ∃ i : Fin 8, eightInputs.getD i.val zero = a := by
    rw [←eightList] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = eightInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run eightInputs (eightInputs.getD i.val zero) sub (absentRow8449 i) (presentRow8449 i)
        (requiredInputs.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply requiredInputs.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨u,k,hk.trans count,eq ▸ run⟩

theorem directSplit
    (m : ∀ k, k ≤ 13 → ¬Live false graph k eightInputs.toFinset)
    (s : ∀ k, k ≤ 12 → ¬Live true graph k eightInputs.toFinset) :
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 8 eightEdge 13 := by
  rintro ⟨C,legal,small,computes⟩
  obtain ⟨mode,k,hk,run⟩ := twoRoots C legal (funext computes) small
  cases mode
  · exact m k hk run
  · exact s k hk run
def g7Y : Array (Bits × Bits) := #[(((((4191807 * 4294967296 + 4131386943) * 4294967296 + 4131386943) * 4294967296 + 4131386943) * 4294967296 + 4131386943),((((4792393 * 4294967296 + 541663305) * 4294967296 + 541663305) * 4294967296 + 541663305) * 4294967296 + 541663305)),(((((13106119 * 4294967296 + 4224187335) * 4294967296 + 4224187335) * 4294967296 + 4224187335) * 4294967296 + 4224187335),((((9584786 * 4294967296 + 1083326610) * 4294967296 + 1083326610) * 4294967296 + 1083326610) * 4294967296 + 1083326610)),(((((16317944 * 4294967296 + 4260953592) * 4294967296 + 4260953592) * 4294967296 + 4260953592) * 4294967296 + 4260953592),((((2392356 * 4294967296 + 2166653220) * 4294967296 + 2166653220) * 4294967296 + 2166653220) * 4294967296 + 2166653220)),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g7C : List ColumnInfo := []
def g7A : List (List Nat) := [[],[33],[16],[16,32],[32,16],[32]]
def g7D3 (j : Nat) : Nat := 0x7
def g7L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g7D3)
  | _ => emptyPacking
def g7I (_ _ : Nat) : Option (Nat × Nat) := none
def g7 : Forest := ⟨7,3,fun i => g7Y[i]?.getD (0,0),g7C,g7A,g7L,g7I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g7P3_0 : block g7 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g7B3 : block g7 3 0 1=true := g7P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g7T : checkedTables g7 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g7 0 0 0 = true)
  · exact (rfl : block g7 1 0 0 = true)
  · exact (rfl : block g7 2 0 0 = true)
  · exact g7B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g7G : graphValid g7 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low7 : Lower true (varsX 7) (graphGoal 7) 4 := lower_forest (g:=g7) (i:=0) (hints:=1) (before_sound [] baseKnown) g7G g7T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K7 := extendKnown [] 4 [(7,[]),(25,[49,66])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V7 : Known true K7 := extend_ok (m:=7) baseKnown low7 (by decide +kernel)
def g15Y : Array (Bits × Bits) := #[(((((16603263 * 4294967296 + 4286840831) * 4294967296 + 4093292799) * 4294967296 + 4278714367) * 4294967296 + 3891618303),((((146 * 4294967296 + 1091051648) * 4294967296 + 536871204) * 4294967296 + 2182103296) * 4294967296 + 1073742409)),(((((3911553 * 4294967296 + 4294709191) * 4294967296 + 4235681539) * 4294967296 + 4294451087) * 4294967296 + 4176395783),((((8490276 * 4294967296 + 2450669842) * 4294967296 + 1090722377) * 4294967296 + 606372388) * 4294967296 + 2181444754)),(((((13023118 * 4294967296 + 1073737735) * 4294967296 + 4287459100) * 4294967296 + 2147475471) * 4294967296 + 4279950904),((((1454665 * 4294967296 + 606112292) * 4294967296 + 2150392978) * 4294967296 + 1212224585) * 4294967296 + 5818660)),(((((412784 * 4294967296 + 1073741816) * 4294967296 + 825568) * 4294967296 + 2147483632) * 4294967296 + 1651136),((((2510701 * 4294967296 + 3091401735) * 4294967296 + 172793563) * 4294967296 + 1887836174) * 4294967296 + 345587126)),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g15C : List ColumnInfo := [(8,0,7,0,4)]
def g15A : List (List Nat) := [[],[33]]
def g15D4 (j : Nat) : Nat := 0x1f
def g15L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g15D4)
  | _ => emptyPacking
def g15I (_ _ : Nat) : Option (Nat × Nat) := none
def g15 : Forest := ⟨15,4,fun i => g15Y[i]?.getD (0,0),g15C,g15A,g15L,g15I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g15P4_0 : block g15 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g15B4 : block g15 4 0 1=true := g15P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g15T : checkedTables g15 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g15 0 0 0 = true)
  · exact (rfl : block g15 1 0 0 = true)
  · exact (rfl : block g15 2 0 0 = true)
  · exact (rfl : block g15 3 0 0 = true)
  · exact g15B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g15G : graphValid g15 (boundsBefore K7) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low15 : Lower true (varsX 15) (graphGoal 15) 5 := lower_forest (g:=g15) (i:=0) (hints:=1) (before_sound K7 V7) g15G g15T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K15 := extendKnown K7 5 [(15,[]),(23,[67]),(27,[49,66]),(29,[49,66,33]),(39,[16,83,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V15 : Known true K15 := extend_ok (m:=15) V7 low15 (by decide +kernel)
def g43Y : Array (Bits × Bits) := #[(((((15191615 * 4294967296 + 4278452195) * 4294967296 + 4293381695) * 4294967296 + 4278452195) * 4294967296 + 4293381695),((((346258 * 4294967296 + 1116217417) * 4294967296 + 268781714) * 4294967296 + 1116217417) * 4294967296 + 268781714)),(((((16724935 * 4294967296 + 4294709247) * 4294967296 + 4177474503) * 4294967296 + 4294709247) * 4294967296 + 4177474503),((((143945 * 4294967296 + 336675456) * 4294967296 + 570569289) * 4294967296 + 336675456) * 4294967296 + 570569289)),(0x0,0x0),(((((715832 * 4294967296 + 4294963203) * 4294967296 + 4278905912) * 4294967296 + 4294963203) * 4294967296 + 4278905912),((((4892013 * 4294967296 + 2552335122) * 4294967296 + 1078633837) * 4294967296 + 2552335122) * 4294967296 + 1078633837)),(0x0,0x0),(((((1654208 * 4294967296 + 4294967292) * 4294967296 + 1654208) * 4294967296 + 4294967292) * 4294967296 + 1654208),((((10030518 * 4294967296 + 3770813443) * 4294967296 + 2224623030) * 4294967296 + 3770813443) * 4294967296 + 2224623030)),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g43C : List ColumnInfo := []
def g43A : List (List Nat) := [[],[16,83]]
def g43D3 (j : Nat) : Nat := 0xf
def g43L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g43D3)
  | _ => emptyPacking
def g43I (_ _ : Nat) : Option (Nat × Nat) := none
def g43 : Forest := ⟨43,3,fun i => g43Y[i]?.getD (0,0),g43C,g43A,g43L,g43I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43P3_0 : block g43 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g43B3 : block g43 3 0 1=true := g43P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43T : checkedTables g43 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g43 0 0 0 = true)
  · exact (rfl : block g43 1 0 0 = true)
  · exact (rfl : block g43 2 0 0 = true)
  · exact g43B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43G : graphValid g43 (boundsBefore K15) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low43 : Lower true (varsX 43) (graphGoal 43) 4 := lower_forest (g:=g43) (i:=0) (hints:=1048577) (before_sound K15 V15) g43G g43T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K43 := extendKnown K15 4 [(43,[]),(51,[67]),(77,[33,101]),(85,[33,67,101]),(102,[16,32,83,67,100]),(163,[16,80,48,67,116,100]),(166,[16,80,32,50,67,116,100]),(197,[32,97,16,48,67,117]),(198,[32,97,49,67,117]),(226,[80,113,32,49,66,100,67]),(228,[96,113,32,50,65])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V43 : Known true K43 := extend_ok (m:=43) V15 low43 (by decide +kernel)
def g31Y : Array (Bits × Bits) := #[(((((8380447 * 4294967296 + 4294967264) * 4294967296 + 536870911) * 4294967296 + 3824981396) * 4294967296 + 1074790399),((((16448 * 4294967296 + 537919552) * 4294967296 + 1075843072) * 4294967296 + 1073741824) * 4294967296 + 34636833)),(((((8388576 * 4294967296 + 267943935) * 4294967296 + 3759143039) * 4294967296 + 4232004461) * 4294967296 + 1106247711),((((2393234 * 4294967296 + 1092691080) * 4294967296 + 2319720740) * 4294967296 + 2156004141) * 4294967296 + 1420110154)),(((((8388607 * 4294967296 + 4026564607) * 4294967296 + 4293918847) * 4294967296 + 4291025520) * 4294967296 + 2179990496),((((4786436 * 4294967296 + 2319599889) * 4294967296 + 277430857) * 4294967296 + 645200) * 4294967296 + 2840220308)),(((((8388608 * 4294967296 + 32767) * 4294967296 + 4294967168) * 4294967296 + 32523) * 4294967296 + 3187702784),((((921095 * 4294967296 + 58985986) * 4294967296 + 50429966) * 4294967296 + 152065795) * 4294967296 + 2355304646)),(((((16777215 * 4294967296 + 4294934528) * 4294967296 + 0) * 4294967296 + 207003) * 4294967296 + 4262428672),((((7344152 * 4294967296 + 201355292) * 4294967296 + 470680688) * 4294967296 + 304294040) * 4294967296 + 1905025816)),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g31C : List ColumnInfo := [(2,0,29,0,5),(4,0,27,0,5),(8,0,23,0,5),(16,0,15,0,5),(6,0,25,0,4),(24,0,7,0,4)]
def g31A : List (List Nat) := [[],[67],[33],[33,67],[49,66],[49,66,33],[65,50,33],[65,50]]
def g31D4 (j : Nat) : Nat := (((830631266 * 4294967296 + 336795901) * 4294967296 + 2438169638) * 4294967296 + 4129639696)
def g31D5 (j : Nat) : Nat := (((((((((((((822346240 * 4294967296 + 809506882) * 4294967296 + 136480849) * 4294967296 + 68007142) * 4294967296 + 3262689545) * 4294967296 + 281030634) * 4294967296 + 160297281) * 4294967296 + 834644418) * 4294967296 + 399849538) * 4294967296 + 4272326751) * 4294967296 + 1422987130) * 4294967296 + 2451698993) * 4294967296 + 1144963592) * 4294967296 + 2243774736)
def g31H5 (j : Nat) : Nat := (((((((768 * 4294967296 + 1342177280) * 4294967296 + 0) * 4294967296 + 16) * 4294967296 + 1073741827) * 4294967296 + 3355443200) * 4294967296 + 1216348160) * 4294967296 + 0)
def g31D6 (j : Nat) : Nat := (((344204 * 4294967296 + 2419270670) * 4294967296 + 1149304113) * 4294967296 + 4262526224)
def g31H6 (j : Nat) : Nat := ((((((((1630 * 4294967296 + 3296725257) * 4294967296 + 3296724099) * 4294967296 + 2430730944) * 4294967296 + 2148208897) * 4294967296 + 2159017984) * 4294967296 + 101974057) * 4294967296 + 1428684862) * 4294967296 + 276983820)
def g31D7 (j : Nat) : Nat := 0x1605f
def g31H7 (j : Nat) : Nat := (((((602819 * 4294967296 + 3589865472) * 4294967296 + 841875456) * 4294967296 + 59881472) * 4294967296 + 642080) * 4294967296 + 117723920)
def g31L : Nat → Packing
  | 4 => (3,3,3,0,0,4,0,g31D4)
  | 5 => (10,2,3,0,0,7,0,g31D5)
  | 6 => (3,1,3,0,0,6,0,g31D6)
  | 7 => (1,0,3,0,0,0,0,g31D7)
  | _ => emptyPacking
def g31I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 29 0 9 2 3 g31H5
  | 6 => lookupWord 4 23 4 11 4 3 g31H6
  | 7 => lookupWord 3 19 3 9 2 3 g31H7
  | _ => fun _ => none
def g31 : Forest := ⟨31,7,fun i => g31Y[i]?.getD (0,0),g31C,g31A,g31L,g31I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31P4_0 : block g31 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g31B4 : block g31 4 0 3=true := g31P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31P5_0 : block g31 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31P5_1 : block g31 5 1 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g31B5 : block g31 5 0 10=true := (@block_merge g31 5 0 1 9 g31P5_0 g31P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31P6_0 : block g31 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g31B6 : block g31 6 0 3=true := g31P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31P7_0 : block g31 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g31B7 : block g31 7 0 1=true := g31P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31T : checkedTables g31 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g31 0 0 0 = true)
  · exact (rfl : block g31 1 0 0 = true)
  · exact (rfl : block g31 2 0 0 = true)
  · exact (rfl : block g31 3 0 0 = true)
  · exact g31B4
  · exact g31B5
  · exact g31B6
  · exact g31B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31G : graphValid g31 (boundsBefore K43) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low31 : Lower true (varsX 31) (graphGoal 31) 8 := lower_forest (g:=g31) (i:=0) (hints:=1) (before_sound K43 V43) g31G g31T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K31 := extendKnown K43 8 [(31,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V31 : Known true K31 := extend_ok (m:=31) V43 low31 (by decide +kernel)
def g47Y : Array (Bits × Bits) := #[(((((8388604 * 4294967296 + 134184991) * 4294967296 + 4294967295) * 4294967296 + 4028628894) * 4294967296 + 3660415487),((((16392 * 4294967296 + 276891714) * 4294967296 + 138477584) * 4294967296 + 541065218) * 4294967296 + 1107928210)),(((((8396799 * 4294967296 + 4294967264) * 4294967296 + 67076351) * 4294967296 + 4292886521) * 4294967296 + 634650119),((((295056 * 4294967296 + 1179776) * 4294967296 + 2416050690) * 4294967296 + 1073774680) * 4294967296 + 92279369)),(((((16769024 * 4294967296 + 134217727) * 4294967296 + 4227858687) * 4294967296 + 4294950919) * 4294967296 + 2880572984),((((4789537 * 4294967296 + 2770620692) * 4294967296 + 580136100) * 4294967296 + 2232030469) * 4294967296 + 2821867812)),((((134217727 * 4294967296 + 4294967040) * 4294967296 + 9) * 4294967296 + 3573285312),((((7215554 * 4294967296 + 3325583896) * 4294967296 + 3273148615) * 4294967296 + 160638473) * 4294967296 + 2499042157)),(0x0,0x0),(((((16777215 * 4294967296 + 4160749568) * 4294967296 + 0) * 4294967296 + 103) * 4294967296 + 1415770112),((((7347715 * 4294967296 + 130055199) * 4294967296 + 65040632) * 4294967296 + 236730407) * 4294967296 + 1348660662)),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g47C : List ColumnInfo := [(8,0,39,0,5)]
def g47A : List (List Nat) := [[],[16,83]]
def g47D5 (j : Nat) : Nat := 0x3f
def g47L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g47D5)
  | _ => emptyPacking
def g47I (_ _ : Nat) : Option (Nat × Nat) := none
def g47 : Forest := ⟨47,5,fun i => g47Y[i]?.getD (0,0),g47C,g47A,g47L,g47I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P5_0 : block g47 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g47B5 : block g47 5 0 1=true := g47P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47T : checkedTables g47 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g47 0 0 0 = true)
  · exact (rfl : block g47 1 0 0 = true)
  · exact (rfl : block g47 2 0 0 = true)
  · exact (rfl : block g47 3 0 0 = true)
  · exact (rfl : block g47 4 0 0 = true)
  · exact g47B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47G : graphValid g47 (boundsBefore K31) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low47 : Lower true (varsX 47) (graphGoal 47) 6 := lower_forest (g:=g47) (i:=0) (hints:=1048577) (before_sound K31 V31) g47G g47T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K47 := extendKnown K31 6 [(47,[]),(55,[67]),(79,[33,101]),(87,[33,67,101]),(103,[16,32,83,67,100])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V47 : Known true K47 := extend_ok (m:=47) V31 low47 (by decide +kernel)
def g59Y : Array (Bits × Bits) := #[(((((14684159 * 4294967296 + 4263508993) * 4294967296 + 4291035135) * 4294967296 + 4294750812) * 4294967296 + 3858792447),((((4726800 * 4294967296 + 71567492) * 4294967296 + 1082688002) * 4294967296 + 134222352) * 4294967296 + 1178734724)),(((((16773127 * 4294967296 + 4294967294) * 4294967296 + 261903) * 4294967296 + 4232020395) * 4294967296 + 2517598239),((((8536736 * 4294967296 + 2818658312) * 4294967296 + 353375264) * 4294967296 + 2424471977) * 4294967296 + 2150730851)),(0x0,0x0),(((((16777208 * 4294967296 + 2097151) * 4294967296 + 4294705167) * 4294967296 + 4290805209) * 4294967296 + 435160032),((((32962 * 4294967296 + 814244112) * 4294967296 + 2248218692) * 4294967296 + 537419977) * 4294967296 + 412394793)),((((2097151 * 4294967296 + 4294967280) * 4294967296 + 20263) * 4294967296 + 3924851712),((((1248004 * 4294967296 + 3239150113) * 4294967296 + 402792456) * 4294967296 + 3239054630) * 4294967296 + 2703837778)),(((((16777215 * 4294967296 + 4292870144) * 4294967296 + 0) * 4294967296 + 211622) * 4294967296 + 437223424),((((1838087 * 4294967296 + 1967041) * 4294967296 + 3760439439) * 4294967296 + 35731974) * 4294967296 + 466514844)),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g59C : List ColumnInfo := [(0,32,25,2,5),(32,0,27,0,5),(2,32,25,0,4),(8,0,51,0,4),(16,0,43,0,4)]
def g59A : List (List Nat) := [[],[67]]
def g59D4 (j : Nat) : Nat := 0x57d4d20
def g59D5 (j : Nat) : Nat := ((1619526784 * 4294967296 + 3779132722) * 4294967296 + 4263574816)
def g59H5 (j : Nat) : Nat := 0xe
def g59D6 (j : Nat) : Nat := 0x18d09f
def g59H6 (j : Nat) : Nat := ((794629 * 4294967296 + 14286848) * 4294967296 + 1442304)
def g59L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g59D4)
  | 5 => (3,1,3,0,0,5,0,g59D5)
  | 6 => (1,0,3,0,0,0,0,g59D6)
  | _ => emptyPacking
def g59I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g59H5
  | 6 => lookupWord 1 13 0 7 2 1 g59H6
  | _ => fun _ => none
def g59 : Forest := ⟨59,6,fun i => g59Y[i]?.getD (0,0),g59C,g59A,g59L,g59I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P4_0 : block g59 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B4 : block g59 4 0 1=true := g59P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P5_0 : block g59 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B5 : block g59 5 0 3=true := g59P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P6_0 : block g59 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B6 : block g59 6 0 1=true := g59P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59T : checkedTables g59 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g59 0 0 0 = true)
  · exact (rfl : block g59 1 0 0 = true)
  · exact (rfl : block g59 2 0 0 = true)
  · exact (rfl : block g59 3 0 0 = true)
  · exact g59B4
  · exact g59B5
  · exact g59B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59G : graphValid g59 (boundsBefore K47) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low59 : Lower true (varsX 59) (graphGoal 59) 7 := lower_forest (g:=g59) (i:=0) (hints:=1048577) (before_sound K47 V47) g59G g59T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K59 := extendKnown K47 7 [(59,[]),(93,[33,101]),(167,[16,80,50,32,66,116,100]),(199,[32,97,48,65,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V59 : Known true K59 := extend_ok (m:=59) V47 low59 (by decide +kernel)
def g171Y : Array (Bits × Bits) := #[(((((16777215 * 4294967296 + 4294963201) * 4294967296 + 4294966279) * 4294967296 + 4294967291) * 4294967296 + 776143103),((((2163744 * 4294967296 + 2216960324) * 4294967296 + 545523728) * 4294967296 + 2432696609) * 4294967296 + 172184917)),(((((16744463 * 4294967296 + 4294967294) * 4294967296 + 4194303) * 4294967296 + 4286644180) * 4294967296 + 2498891535),((((680264 * 4294967296 + 692144649) * 4294967296 + 1160270149) * 4294967296 + 36063444) * 4294967296 + 346065032)),(0x0,0x0),(((((16777200 * 4294967296 + 33554431) * 4294967296 + 4290772999) * 4294967296 + 4294901822) * 4294967296 + 2911174896),((((4999565 * 4294967296 + 831097873) * 4294967296 + 2251383398) * 4294967296 + 608472094) * 4294967296 + 2776935082)),(0x0,0x0),((((33554431 * 4294967296 + 4294967288) * 4294967296 + 39) * 4294967296 + 3556572928),((((7343617 * 4294967296 + 3222143072) * 4294967296 + 134316032) * 4294967296 + 940052515) * 4294967296 + 3243258675)),(0x0,0x0),(((((16777215 * 4294967296 + 4261412864) * 4294967296 + 0) * 4294967296 + 413) * 4294967296 + 1393422336),((((8417294 * 4294967296 + 32509825) * 4294967296 + 4030595975) * 4294967296 + 3228623260) * 4294967296 + 302894284)),(0x0,0x0)]
def g171C : List ColumnInfo := []
def g171A : List (List Nat) := [[],[80,115]]
def g171D4 (j : Nat) : Nat := 0x1f
def g171L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g171D4)
  | _ => emptyPacking
def g171I (_ _ : Nat) : Option (Nat × Nat) := none
def g171 : Forest := ⟨171,4,fun i => g171Y[i]?.getD (0,0),g171C,g171A,g171L,g171I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171P4_0 : block g171 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g171B4 : block g171 4 0 1=true := g171P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171T : checkedTables g171 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g171 0 0 0 = true)
  · exact (rfl : block g171 1 0 0 = true)
  · exact (rfl : block g171 2 0 0 = true)
  · exact (rfl : block g171 3 0 0 = true)
  · exact g171B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171G : graphValid g171 (boundsBefore K59) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low171 : Lower true (varsX 171) (graphGoal 171) 5 := lower_forest (g:=g171) (i:=0) (hints:=1343225857) (before_sound K59 V59) g171G g171T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K171 := extendKnown K59 5 [(171,[]),(179,[67]),(205,[33,101]),(227,[16,80,48,67,116,100]),(229,[32,97,16,48,67,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V171 : Known true K171 := extend_ok (m:=171) V59 low171 (by decide +kernel)
def g185Y : Array (Bits × Bits) := #[(((((16515327 * 4294967296 + 4294967040) * 4294967296 + 1073741823) * 4294967296 + 3288263226) * 4294967296 + 1392513023),((((9052680 * 4294967296 + 2183275048) * 4294967296 + 2283931784) * 4294967296 + 2281840666) * 4294967296 + 321163849)),(0x0,0x0),(0x0,0x0),(((((16776960 * 4294967296 + 1073741823) * 4294967296 + 3222274047) * 4294967296 + 4231975109) * 4294967296 + 4127453247),((((1066129 * 4294967296 + 71582785) * 4294967296 + 306450705) * 4294967296 + 8441861) * 4294967296 + 3293127826)),(((((16777215 * 4294967296 + 3222274047) * 4294967296 + 4293919743) * 4294967296 + 4290854636) * 4294967296 + 2701393856),((((2132002 * 4294967296 + 680036482) * 4294967296 + 545825314) * 4294967296 + 593632) * 4294967296 + 546457892)),((((1048575 * 4294967296 + 4294966272) * 4294967296 + 75667) * 4294967296 + 3707502592),((((12644412 * 4294967296 + 251719692) * 4294967296 + 50380860) * 4294967296 + 286335619) * 4294967296 + 3625742791)),(0x0,0x0),(((((16777215 * 4294967296 + 4293918720) * 4294967296 + 0) * 4294967296 + 236883) * 4294967296 + 234618880),((((196800 * 4294967296 + 806289648) * 4294967296 + 1007616960) * 4294967296 + 572693840) * 4294967296 + 98799160)),(0x0,0x0)]
def g185C : List ColumnInfo := [(0,32,25,128,5)]
def g185A : List (List Nat) := [[],[117],[67],[67,117],[48],[48,117],[48,64],[48,64,117],[64,48],[64,48,117],[64],[64,117]]
def g185D5 (j : Nat) : Nat := 0x3f
def g185L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g185D5)
  | _ => emptyPacking
def g185I (_ _ : Nat) : Option (Nat × Nat) := none
def g185 : Forest := ⟨185,5,fun i => g185Y[i]?.getD (0,0),g185C,g185A,g185L,g185I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g185P5_0 : block g185 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g185B5 : block g185 5 0 1=true := g185P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g185T : checkedTables g185 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g185 0 0 0 = true)
  · exact (rfl : block g185 1 0 0 = true)
  · exact (rfl : block g185 2 0 0 = true)
  · exact (rfl : block g185 3 0 0 = true)
  · exact (rfl : block g185 4 0 0 = true)
  · exact g185B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g185G : graphValid g185 (boundsBefore K171) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low185 : Lower true (varsX 185) (graphGoal 185) 6 := lower_forest (g:=g185) (i:=0) (hints:=1349517315) (before_sound K171 V171) g185G g185T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K185 := extendKnown K171 6 [(185,[]),(217,[101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V185 : Known true K185 := extend_ok (m:=185) V171 low185 (by decide +kernel)
def g230Y : Array (Bits × Bits) := #[(0x0,0x0),(((((16744511 * 4294967296 + 4043309040) * 4294967296 + 134217487) * 4294967296 + 4294960250) * 4294967296 + 2214593535),((((2181252 * 4294967296 + 572597285) * 4294967296 + 302580260) * 4294967296 + 2281857074) * 4294967296 + 2225416522)),(((((16777152 * 4294967296 + 16777215) * 4294967296 + 4161011711) * 4294967296 + 4232020361) * 4294967296 + 4227890207),((((655649 * 4294967296 + 1141522760) * 4294967296 + 609358856) * 4294967296 + 276922505) * 4294967296 + 1494795825)),(0x0,0x0),(0x0,0x0),(((((16777215 * 4294967296 + 4278222847) * 4294967296 + 4294705167) * 4294967296 + 4290805209) * 4294967296 + 303006688),((((4985353 * 4294967296 + 2152466816) * 4294967296 + 1080055873) * 4294967296 + 537398729) * 4294967296 + 38966437)),((((32767 * 4294967296 + 4294967280) * 4294967296 + 20263) * 4294967296 + 3924851712),((((7347214 * 4294967296 + 141561345) * 4294967296 + 2155896833) * 4294967296 + 3239071520) * 4294967296 + 2690848966)),(((((16777215 * 4294967296 + 4294934528) * 4294967296 + 0) * 4294967296 + 211622) * 4294967296 + 469729280),((((8413232 * 4294967296 + 8417294) * 4294967296 + 117670030) * 4294967296 + 35860486) * 4294967296 + 428630808)),(0x0,0x0)]
def g230C : List ColumnInfo := [(2,0,228,0,4),(4,0,226,0,4),(32,0,198,0,4),(64,0,166,0,4),(128,0,102,0,4)]
def g230A : List (List Nat) := [[],[82,118],[33,101],[33,97,81,117],[81,33,114,98],[81,114],[97,117],[97,114,82,81],[113,82,98,33],[113,98]]
def g230D4 (j : Nat) : Nat := 0x5dd4530
def g230D5 (j : Nat) : Nat := 0x41030fd30fd10
def g230H5 (j : Nat) : Nat := 0x5
def g230D6 (j : Nat) : Nat := 0x23440bf
def g230H6 (j : Nat) : Nat := ((((2572 * 4294967296 + 829167955) * 4294967296 + 2684354560) * 4294967296 + 35811341) * 4294967296 + 3970957324)
def g230L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g230D4)
  | 5 => (2,1,3,0,0,3,0,g230D5)
  | 6 => (1,0,3,0,0,0,0,g230D6)
  | _ => emptyPacking
def g230I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g230H5
  | 6 => lookupWord 2 17 2 8 1 3 g230H6
  | _ => fun _ => none
def g230 : Forest := ⟨230,6,fun i => g230Y[i]?.getD (0,0),g230C,g230A,g230L,g230I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g230P4_0 : block g230 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g230B4 : block g230 4 0 1=true := g230P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g230P5_0 : block g230 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g230B5 : block g230 5 0 2=true := g230P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g230P6_0 : block g230 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g230B6 : block g230 6 0 1=true := g230P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g230T : checkedTables g230 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g230 0 0 0 = true)
  · exact (rfl : block g230 1 0 0 = true)
  · exact (rfl : block g230 2 0 0 = true)
  · exact (rfl : block g230 3 0 0 = true)
  · exact g230B4
  · exact g230B5
  · exact g230B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g230G : graphValid g230 (boundsBefore K185) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low230 : Lower true (varsX 230) (graphGoal 230) 7 := lower_forest (g:=g230) (i:=0) (hints:=1376780576) (before_sound K185 V185) g230G g230T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K230 := extendKnown K185 7 [(230,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V230 : Known true K230 := extend_ok (m:=230) V185 low230 (by decide +kernel)
def g63Y : Array (Bits × Bits) := #[(((((16777215 * 4294967296 + 4294934559) * 4294967296 + 4294887761) * 4294967296 + 756174680) * 4294967296 + 1048575),((((1050624 * 4294967296 + 67174464) * 4294967296 + 49408) * 4294967296 + 134349905) * 4294967296 + 138547332)),(((((16776192 * 4294967296 + 4294967264) * 4294967296 + 134198324) * 4294967296 + 3534586472) * 4294967296 + 1072693279),((((135170 * 4294967296 + 9568256) * 4294967296 + 268513296) * 4294967296 + 2183692808) * 4294967296 + 3325135971)),((((4294967295 * 4294967296 + 4160774307) * 4294967296 + 934629552) * 4294967296 + 32506848),((((10789036 * 4294967296 + 2837714181) * 4294967296 + 1096024227) * 4294967296 + 898977958) * 4294967296 + 831283992)),(((((16777215 * 4294967296 + 0) * 4294967296 + 7070) * 4294967296 + 24049831) * 4294967296 + 3221257216),((((12632328 * 4294967296 + 808984968) * 4294967296 + 1645746332) * 4294967296 + 19691554) * 4294967296 + 1385473321)),(0x22eaf858b787c00f8000,((((459312 * 4294967296 + 3250603537) * 4294967296 + 2220892770) * 4294967296 + 4031808388) * 4294967296 + 2770946642)),(((105766 * 4294967296 + 3972034864) * 4294967296 + 1040187392),((((16253888 * 4294967296 + 4261443614) * 4294967296 + 125865254) * 4294967296 + 1824551223) * 4294967296 + 969831324)),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g63C : List ColumnInfo := [(32,0,31,0,8)]
def g63A : List (List Nat) := [[],[67]]
def g63D8 (j : Nat) : Nat := 0x7f
def g63L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g63D8)
  | _ => emptyPacking
def g63I (_ _ : Nat) : Option (Nat × Nat) := none
def g63 : Forest := ⟨63,8,fun i => g63Y[i]?.getD (0,0),g63C,g63A,g63L,g63I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_0 : block g63 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B8 : block g63 8 0 1=true := g63P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63T : checkedTables g63 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g63 0 0 0 = true)
  · exact (rfl : block g63 1 0 0 = true)
  · exact (rfl : block g63 2 0 0 = true)
  · exact (rfl : block g63 3 0 0 = true)
  · exact (rfl : block g63 4 0 0 = true)
  · exact (rfl : block g63 5 0 0 = true)
  · exact (rfl : block g63 6 0 0 = true)
  · exact (rfl : block g63 7 0 0 = true)
  · exact g63B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63G : graphValid g63 (boundsBefore K230) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (varsX 63) (graphGoal 63) 9 := lower_forest (g:=g63) (i:=0) (hints:=1048577) (before_sound K230 V230) g63G g63T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K63 := extendKnown K230 9 [(63,[]),(95,[33,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V63 : Known true K63 := extend_ok (m:=63) V230 low63 (by decide +kernel)
def g111Y : Array (Bits × Bits) := #[(((((16777215 * 4294967296 + 4294705167) * 4294967296 + 4294967231) * 4294967296 + 3466880067) * 4294967296 + 1224740863),((((2166800 * 4294967296 + 2215134241) * 4294967296 + 268714144) * 4294967296 + 2191787074) * 4294967296 + 1212433476)),(((((15728703 * 4294967296 + 4294967280) * 4294967296 + 4194186) * 4294967296 + 874420644) * 4294967296 + 4245680143),((((4326021 * 4294967296 + 9470082) * 4294967296 + 42469386) * 4294967296 + 68323332) * 4294967296 + 2502042146)),(((((63 * 4294967296 + 4294967295) * 4294967296 + 4290773104) * 4294967296 + 1098641082) * 4294967296 + 586215664),((((8398080 * 4294967296 + 689965312) * 4294967296 + 604017232) * 4294967296 + 1074356400) * 4294967296 + 571543825)),(((((16777152 * 4294967296 + 0) * 4294967296 + 13) * 4294967296 + 3482343901) * 4294967296 + 838864640),((((280102 * 4294967296 + 834736580) * 4294967296 + 1192303629) * 4294967296 + 1292917149) * 4294967296 + 851164091)),(0x0,0x0),(0x117a6d155cf40f0000,((((555064 * 4294967296 + 1040326152) * 4294967296 + 2015485969) * 4294967296 + 2053969240) * 4294967296 + 1625152989)),(0xcea977125e06f00000,((((1015871 * 4294967296 + 3221479439) * 4294967296 + 2151547022) * 4294967296 + 2843087438) * 4294967296 + 82767598)),(0x0,0x0),(0x0,0x0)]
def g111C : List ColumnInfo := [(8,0,103,0,6),(32,0,79,0,6),(64,0,47,0,6),(0,64,43,4,5),(1,0,102,0,4),(1,8,102,0,4),(2,32,77,0,4),(4,64,43,0,4)]
def g111A : List (List Nat) := [[],[33,101],[16,83],[16,32,83,99],[32,16,99,83],[32,99]]
def g111D4 (j : Nat) : Nat := 0x49d7690630
def g111D5 (j : Nat) : Nat := ((((9 * 4294967296 + 817934296) * 4294967296 + 2483778950) * 4294967296 + 819418211) * 4294967296 + 242812464)
def g111H5 (j : Nat) : Nat := 0x40
def g111D6 (j : Nat) : Nat := ((((400 * 4294967296 + 2200491274) * 4294967296 + 3260326004) * 4294967296 + 604501059) * 4294967296 + 2055331376)
def g111H6 (j : Nat) : Nat := (((((((((((((((28928 * 4294967296 + 462848) * 4294967296 + 1114233) * 4294967296 + 2147483648) * 4294967296 + 0) * 4294967296 + 4) * 4294967296 + 671088640) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 10551296) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 6144) * 4294967296 + 198144)
def g111D7 (j : Nat) : Nat := 0x3ea881bf
def g111H7 (j : Nat) : Nat := (((((405504 * 4294967296 + 2424832) * 4294967296 + 1350529) * 4294967296 + 872677376) * 4294967296 + 2756358368) * 4294967296 + 102760516)
def g111L : Nat → Packing
  | 4 => (1,3,3,0,0,0,0,g111D4)
  | 5 => (4,2,3,0,0,5,0,g111D5)
  | 6 => (3,1,3,0,0,6,0,g111D6)
  | 7 => (1,0,3,0,0,0,0,g111D7)
  | _ => emptyPacking
def g111I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g111H5
  | 6 => lookupWord 2 67 0 9 2 3 g111H6
  | 7 => lookupWord 3 19 3 9 2 3 g111H7
  | _ => fun _ => none
def g111 : Forest := ⟨111,7,fun i => g111Y[i]?.getD (0,0),g111C,g111A,g111L,g111I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P4_0 : block g111 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g111B4 : block g111 4 0 1=true := g111P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P5_0 : block g111 5 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g111B5 : block g111 5 0 4=true := g111P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6_0 : block g111 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6_2 : block g111 6 2 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g111B6 : block g111 6 0 3=true := (@block_merge g111 6 0 2 1 g111P6_0 g111P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7_0 : block g111 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g111B7 : block g111 7 0 1=true := g111P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111T : checkedTables g111 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g111 0 0 0 = true)
  · exact (rfl : block g111 1 0 0 = true)
  · exact (rfl : block g111 2 0 0 = true)
  · exact (rfl : block g111 3 0 0 = true)
  · exact g111B4
  · exact g111B5
  · exact g111B6
  · exact g111B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111G : graphValid g111 (boundsBefore K63) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low111 : Lower true (varsX 111) (graphGoal 111) 8 := lower_forest (g:=g111) (i:=0) (hints:=34603009) (before_sound K63 V63) g111G g111T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K111 := extendKnown K63 8 [(111,[]),(119,[67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V111 : Known true K111 := extend_ok (m:=111) V63 low111 (by decide +kernel)
def g126Y : Array (Bits × Bits) := #[(0x0,0x0),(((((255 * 4294967296 + 4294967295) * 4294967296 + 4294963597) * 4294967296 + 4090089693) * 4294967296 + 3523219455),((((1059349 * 4294967296 + 4740098) * 4294967296 + 553795845) * 4294967296 + 1896431644) * 4294967296 + 2452669196)),(((((255 * 4294967296 + 4294967295) * 4294967296 + 4294967156) * 4294967296 + 141208287) * 4294967296 + 1292103743),((((87040 * 4294967296 + 1418723668) * 4294967296 + 1075088432) * 4294967296 + 140683457) * 4294967296 + 1091317955)),(((((16776960 * 4294967296 + 262143) * 4294967296 + 4026534279) * 4294967296 + 637005600) * 4294967296 + 2784755712),((((2234438 * 4294967296 + 417405024) * 4294967296 + 2183192964) * 4294967296 + 620219904) * 4294967296 + 2236962133)),(((((16777215 * 4294967296 + 4294705152) * 4294967296 + 3179) * 4294967296 + 2000037238) * 4294967296 + 3774611456),((((4481176 * 4294967296 + 1627545991) * 4294967296 + 71765099) * 4294967296 + 1392517494) * 4294967296 + 1621797546)),(0xc8adab5d9c21e000fc0,((((8880352 * 4294967296 + 2114159096) * 4294967296 + 142085258) * 4294967296 + 2327091650) * 4294967296 + 214908147)),(0x6754a985f269d03f000,((((16253183 * 4294967296 + 2147745280) * 4294967296 + 260047429) * 4294967296 + 1117280038) * 4294967296 + 2633223996)),(0x0,0x0),(0x0,0x0)]
def g126C : List ColumnInfo := [(0,8,102,16,5)]
def g126A : List (List Nat) := [[],[67],[33,101],[33,67,101]]
def g126D5 (j : Nat) : Nat := 0x7f
def g126L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g126D5)
  | _ => emptyPacking
def g126I (_ _ : Nat) : Option (Nat × Nat) := none
def g126 : Forest := ⟨126,5,fun i => g126Y[i]?.getD (0,0),g126C,g126A,g126L,g126I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P5_0 : block g126 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g126B5 : block g126 5 0 1=true := g126P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126T : checkedTables g126 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g126 0 0 0 = true)
  · exact (rfl : block g126 1 0 0 = true)
  · exact (rfl : block g126 2 0 0 = true)
  · exact (rfl : block g126 3 0 0 = true)
  · exact (rfl : block g126 4 0 0 = true)
  · exact g126B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126G : graphValid g126 (boundsBefore K111) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low126 : Lower true (varsX 126) (graphGoal 126) 6 := lower_forest (g:=g126) (i:=0) (hints:=34816288) (before_sound K111 V111) g126G g126T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K126 := extendKnown K111 6 [(126,[]),(190,[82,118]),(250,[81,114])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V126 : Known true K126 := extend_ok (m:=126) V111 low126 (by decide +kernel)
def g175Y : Array (Bits × Bits) := #[(((((16777215 * 4294967296 + 4294705215) * 4294967296 + 4294967281) * 4294967296 + 2706997330) * 4294967296 + 3221258239),((((262144 * 4294967296 + 2215116928) * 4294967296 + 14368) * 4294967296 + 2705391634) * 4294967296 + 173184165)),(((((16646175 * 4294967296 + 4294967232) * 4294967296 + 67101317) * 4294967296 + 1453746366) * 4294967296 + 1107263519),((((541001 * 4294967296 + 9470472) * 4294967296 + 679608961) * 4294967296 + 1344667812) * 4294967296 + 1350836488)),(((((31 * 4294967296 + 4294967295) * 4294967296 + 4227865616) * 4294967296 + 1320926856) * 4294967296 + 2148500448),((((5278354 * 4294967296 + 690033681) * 4294967296 + 1091863568) * 4294967296 + 244891144) * 4294967296 + 2770946642)),(((((16777184 * 4294967296 + 0) * 4294967296 + 883) * 4294967296 + 3826673484) * 4294967296 + 2147515392),((((6361884 * 4294967296 + 834807586) * 4294967296 + 1915159379) * 4294967296 + 1142318924) * 4294967296 + 3048041306)),(0x0,0x0),(0x45e9b45573d3ff00000,((((8395776 * 4294967296 + 1040201731) * 4294967296 + 2151154774) * 4294967296 + 2332115993) * 4294967296 + 103910499)),(0x0,0x0),(0x33aa5dc49781be000000,((((122911 * 4294967296 + 3221471292) * 4294967296 + 62927784) * 4294967296 + 1422168960) * 4294967296 + 3117314972)),(0x0,0x0)]
def g175C : List ColumnInfo := [(8,0,167,0,7)]
def g175A : List (List Nat) := [[]]
def g175D7 (j : Nat) : Nat := 0x7f
def g175L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g175D7)
  | _ => emptyPacking
def g175I (_ _ : Nat) : Option (Nat × Nat) := none
def g175 : Forest := ⟨175,7,fun i => g175Y[i]?.getD (0,0),g175C,g175A,g175L,g175I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P7_0 : block g175 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B7 : block g175 7 0 1=true := g175P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175T : checkedTables g175 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g175 0 0 0 = true)
  · exact (rfl : block g175 1 0 0 = true)
  · exact (rfl : block g175 2 0 0 = true)
  · exact (rfl : block g175 3 0 0 = true)
  · exact (rfl : block g175 4 0 0 = true)
  · exact (rfl : block g175 5 0 0 = true)
  · exact (rfl : block g175 6 0 0 = true)
  · exact g175B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175G : graphValid g175 (boundsBefore K126) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low175 : Lower true (varsX 175) (graphGoal 175) 8 := lower_forest (g:=g175) (i:=0) (hints:=1343225857) (before_sound K126 V126) g175G g175T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K175 := extendKnown K126 8 [(175,[]),(183,[67]),(207,[33,101]),(215,[33,67,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V175 : Known true K175 := extend_ok (m:=175) V126 low175 (by decide +kernel)
def g187Y : Array (Bits × Bits) := #[(((((1048575 * 4294967296 + 4294967295) * 4294967296 + 4294440972) * 4294967296 + 979514768) * 4294967296 + 262143),((((2114576 * 4294967296 + 557568) * 4294967296 + 145412) * 4294967296 + 274859138) * 4294967296 + 1227133513)),(((((1048568 * 4294967296 + 33554176) * 4294967296 + 1072997667) * 4294967296 + 2828590288) * 4294967296 + 16515135),((((13271201 * 4294967296 + 894444581) * 4294967296 + 2302967811) * 4294967296 + 2828589148) * 4294967296 + 818089008)),(0x0,0x0),(((((15728640 * 4294967296 + 33554431) * 4294967296 + 3221946609) * 4294967296 + 2934727264) * 4294967296 + 1056968640),((((8587458 * 4294967296 + 409012289) * 4294967296 + 274792673) * 4294967296 + 2860802596) * 4294967296 + 2454267026)),(((((16777215 * 4294967296 + 4261412864) * 4294967296 + 580697) * 4294967296 + 94081888) * 4294967296 + 1057222656),((((790788 * 4294967296 + 562180230) * 4294967296 + 562611224) * 4294967296 + 85561673) * 4294967296 + 613566756)),(((595878 * 4294967296 + 3512061711) * 4294967296 + 3237740544),((((7680 * 4294967296 + 1073987592) * 4294967296 + 34150176) * 4294967296 + 289670913) * 4294967296 + 3340530119)),(0x0,0x0),(((322199 * 4294967296 + 1898307695) * 4294967296 + 3221225472),((((1040391 * 4294967296 + 2180776176) * 4294967296 + 1006954647) * 4294967296 + 1612832878) * 4294967296 + 954437176)),(0x0,0x0)]
def g187C : List ColumnInfo := [(128,0,59,0,7)]
def g187A : List (List Nat) := [[],[67]]
def g187D7 (j : Nat) : Nat := 0x7f
def g187L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g187D7)
  | _ => emptyPacking
def g187I (_ _ : Nat) : Option (Nat × Nat) := none
def g187 : Forest := ⟨187,7,fun i => g187Y[i]?.getD (0,0),g187C,g187A,g187L,g187I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P7_0 : block g187 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B7 : block g187 7 0 1=true := g187P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187T : checkedTables g187 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g187 0 0 0 = true)
  · exact (rfl : block g187 1 0 0 = true)
  · exact (rfl : block g187 2 0 0 = true)
  · exact (rfl : block g187 3 0 0 = true)
  · exact (rfl : block g187 4 0 0 = true)
  · exact (rfl : block g187 5 0 0 = true)
  · exact (rfl : block g187 6 0 0 = true)
  · exact g187B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187G : graphValid g187 (boundsBefore K175) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low187 : Lower true (varsX 187) (graphGoal 187) 8 := lower_forest (g:=g187) (i:=0) (hints:=1343225857) (before_sound K175 V175) g187G g187T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K187 := extendKnown K175 8 [(187,[]),(221,[33,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V187 : Known true K187 := extend_ok (m:=187) V175 low187 (by decide +kernel)
def g189Y : Array (Bits × Bits) := #[(((((16777215 * 4294967296 + 4294967295) * 4294967296 + 4294949833) * 4294967296 + 1554133179) * 4294967296 + 2147745791),((((266240 * 4294967296 + 16910336) * 4294967296 + 45056) * 4294967296 + 469774362) * 4294967296 + 153391689)),(0x0,0x0),(((((16775168 * 4294967296 + 1073740800) * 4294967296 + 536857516) * 4294967296 + 2709899929) * 4294967296 + 2147483711),((((11051286 * 4294967296 + 2857668746) * 4294967296 + 3293858732) * 4294967296 + 2709899905) * 4294967296 + 3067833782)),((((1073741823 * 4294967296 + 3758111782) * 4294967296 + 2733557539) * 4294967296 + 1090260928),((((3195427 * 4294967296 + 202907920) * 4294967296 + 2290486310) * 4294967296 + 581305889) * 4294967296 + 1380525202)),(((((16777215 * 4294967296 + 3221225472) * 4294967296 + 18147) * 4294967296 + 3629965248) * 4294967296 + 16773120),((((12649540 * 4294967296 + 811647523) * 4294967296 + 286802625) * 4294967296 + 3227044288) * 4294967296 + 613566756)),(0x48bd2f1bac4e7f000000,((((16646264 * 4294967296 + 8323132) * 4294967296 + 31475885) * 4294967296 + 169583630) * 4294967296 + 119304647)),(0x0,0x0),(0xe754b7112b657f000000,((((1920 * 4294967296 + 1065354176) * 4294967296 + 503359312) * 4294967296 + 3036679009) * 4294967296 + 2028179000)),(0x0,0x0)]
def g189C : List ColumnInfo := [(0,32,29,128,6)]
def g189A : List (List Nat) := [[],[117],[67],[67,117]]
def g189D6 (j : Nat) : Nat := 0x7f
def g189L : Nat → Packing
  | 6 => (1,0,1,0,0,0,0,g189D6)
  | _ => emptyPacking
def g189I (_ _ : Nat) : Option (Nat × Nat) := none
def g189 : Forest := ⟨189,6,fun i => g189Y[i]?.getD (0,0),g189C,g189A,g189L,g189I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P6_0 : block g189 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g189B6 : block g189 6 0 1=true := g189P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189T : checkedTables g189 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g189 0 0 0 = true)
  · exact (rfl : block g189 1 0 0 = true)
  · exact (rfl : block g189 2 0 0 = true)
  · exact (rfl : block g189 3 0 0 = true)
  · exact (rfl : block g189 4 0 0 = true)
  · exact (rfl : block g189 5 0 0 = true)
  · exact g189B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189G : graphValid g189 (boundsBefore K187) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low189 : Lower true (varsX 189) (graphGoal 189) 7 := lower_forest (g:=g189) (i:=0) (hints:=1349517314) (before_sound K187 V187) g189G g189T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K189 := extendKnown K187 7 [(189,[]),(219,[33,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V189 : Known true K189 := extend_ok (m:=189) V187 low189 (by decide +kernel)
def g231Y : Array (Bits × Bits) := #[(((((16776960 * 4294967296 + 4294902015) * 4294967296 + 4294585264) * 4294967296 + 2483186688) * 4294967296 + 4095),((((1344042 * 4294967296 + 690104872) * 4294967296 + 687344432) * 4294967296 + 2214748355) * 4294967296 + 204522252)),(((((8388607 * 4294967296 + 4294967040) * 4294967296 + 4286790667) * 4294967296 + 1203119104) * 4294967296 + 16773183),((((2163712 * 4294967296 + 1107558402) * 4294967296 + 144395) * 4294967296 + 19924260) * 4294967296 + 2454267026)),(((((8388608 * 4294967296 + 4294967295) * 4294967296 + 7356559) * 4294967296 + 4206974976) * 4294967296 + 1057226688),((((4204548 * 4294967296 + 2152202240) * 4294967296 + 33554564) * 4294967296 + 1925257752) * 4294967296 + 1636178017)),(0x0,0x0),(0x0,0x0),(((((16777215 * 4294967296 + 0) * 4294967296 + 904964) * 4294967296 + 2540457999) * 4294967296 + 3237740544),((((405576 * 4294967296 + 208686156) * 4294967296 + 1275709696) * 4294967296 + 2521583697) * 4294967296 + 1158959429)),(((1144184 * 4294967296 + 744211440) * 4294967296 + 1056964608),((((508016 * 4294967296 + 260075632) * 4294967296 + 1880192296) * 4294967296 + 202031201) * 4294967296 + 2249744774)),(((13538166 * 4294967296 + 1614322687) * 4294967296 + 3221225472),((((7864448 * 4294967296 + 4026564736) * 4294967296 + 2160460374) * 4294967296 + 1613761422) * 4294967296 + 954437176)),(0x0,0x0)]
def g231C : List ColumnInfo := [(1,0,230,0,7),(32,0,199,0,7),(64,0,167,0,7),(0,128,7,96,6),(128,0,103,0,6),(2,0,229,0,5),(4,0,227,0,5)]
def g231A : List (List Nat) := [[],[33,101]]
def g231D5 (j : Nat) : Nat := 0x4fb7058a21
def g231D6 (j : Nat) : Nat := ((((((4196357 * 4294967296 + 80022216) * 4294967296 + 1530924021) * 4294967296 + 2317483736) * 4294967296 + 303820161) * 4294967296 + 565663938) * 4294967296 + 468025377)
def g231H6 (j : Nat) : Nat := 0x6
def g231D7 (j : Nat) : Nat := (((((6414 * 4294967296 + 1779725366) * 4294967296 + 1519918480) * 4294967296 + 3932243848) * 4294967296 + 2282223751) * 4294967296 + 4198759457)
def g231H7 (j : Nat) : Nat := ((((((((((((39168 * 4294967296 + 0) * 4294967296 + 29184) * 4294967296 + 0) * 4294967296 + 6553600) * 4294967296 + 0) * 4294967296 + 41216) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 48) * 4294967296 + 0) * 4294967296 + 13828096) * 4294967296 + 0)
def g231D8 (j : Nat) : Nat := 0x468817f
def g231H8 (j : Nat) : Nat := (((4849664 * 4294967296 + 34603008) * 4294967296 + 8389616) * 4294967296 + 0)
def g231L : Nat → Packing
  | 5 => (1,3,3,0,0,0,0,g231D5)
  | 6 => (5,2,3,0,0,6,0,g231D6)
  | 7 => (3,1,3,0,0,7,0,g231D7)
  | 8 => (1,0,3,0,0,0,0,g231D8)
  | _ => emptyPacking
def g231I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g231H6
  | 7 => lookupWord 1 53 0 8 3 1 g231H7
  | 8 => lookupWord 1 17 0 7 2 1 g231H8
  | _ => fun _ => none
def g231 : Forest := ⟨231,8,fun i => g231Y[i]?.getD (0,0),g231C,g231A,g231L,g231I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P5_0 : block g231 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B5 : block g231 5 0 1=true := g231P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P6_0 : block g231 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P6_3 : block g231 6 3 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B6 : block g231 6 0 5=true := (@block_merge g231 6 0 3 2 g231P6_0 g231P6_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P7_0 : block g231 7 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B7 : block g231 7 0 3=true := g231P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P8_0 : block g231 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B8 : block g231 8 0 1=true := g231P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231T : checkedTables g231 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g231 0 0 0 = true)
  · exact (rfl : block g231 1 0 0 = true)
  · exact (rfl : block g231 2 0 0 = true)
  · exact (rfl : block g231 3 0 0 = true)
  · exact (rfl : block g231 4 0 0 = true)
  · exact g231B5
  · exact g231B6
  · exact g231B7
  · exact g231B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231G : graphValid g231 (boundsBefore K189) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low231 : Lower true (varsX 231) (graphGoal 231) 9 := lower_forest (g:=g231) (i:=0) (hints:=1376780289) (before_sound K189 V189) g231G g231T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K231 := extendKnown K189 9 [(231,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V231 : Known true K231 := extend_ok (m:=231) V189 low231 (by decide +kernel)
def g235Y : Array (Bits × Bits) := #[(((((16776704 * 4294967296 + 134217727) * 4294967296 + 4294967292) * 4294967296 + 1344755749) * 4294967296 + 3690988543),((((4326404 * 4294967296 + 2425393409) * 4294967296 + 537167796) * 4294967296 + 270534692) * 4294967296 + 3500484938)),(((((16777215 * 4294967296 + 4294967168) * 4294967296 + 33553485) * 4294967296 + 1264363148) * 4294967296 + 3959454751),((((1321096 * 4294967296 + 1157956130) * 4294967296 + 210247753) * 4294967296 + 1096589448) * 4294967296 + 756598321)),(0x0,0x0),((((134217727 * 4294967296 + 4261413313) * 4294967296 + 889714289) * 4294967296 + 973079520),((((10006801 * 4294967296 + 1713775684) * 4294967296 + 1225863233) * 4294967296 + 621278801) * 4294967296 + 727373493)),(0x0,0x0),(((((16777215 * 4294967296 + 4160749568) * 4294967296 + 567) * 4294967296 + 516056830) * 4294967296 + 537918464),((((14729249 * 4294967296 + 2151168008) * 4294967296 + 1881260564) * 4294967296 + 444745334) * 4294967296 + 6494406)),(0x245e978dd6253f00000,((((16711742 * 4294967296 + 4177935) * 4294967296 + 2151547461) * 4294967296 + 3379057762) * 4294967296 + 1383308519)),(0x73aa5b8895b2bff8000,((((448 * 4294967296 + 130023536) * 4294967296 + 29361450) * 4294967296 + 605063433) * 4294967296 + 697066264)),(0x0,0x0)]
def g235C : List ColumnInfo := [(0,8,226,1,5),(0,64,43,128,5),(8,0,227,0,5),(64,0,171,0,5)]
def g235A : List (List Nat) := [[],[112,81,99]]
def g235D6 (j : Nat) : Nat := 0xe413f
def g235L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g235D6)
  | _ => emptyPacking
def g235I (_ _ : Nat) : Option (Nat × Nat) := none
def g235 : Forest := ⟨235,6,fun i => g235Y[i]?.getD (0,0),g235C,g235A,g235L,g235I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_0 : block g235 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B6 : block g235 6 0 1=true := g235P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235T : checkedTables g235 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g235 0 0 0 = true)
  · exact (rfl : block g235 1 0 0 = true)
  · exact (rfl : block g235 2 0 0 = true)
  · exact (rfl : block g235 3 0 0 = true)
  · exact (rfl : block g235 4 0 0 = true)
  · exact (rfl : block g235 5 0 0 = true)
  · exact g235B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235G : graphValid g235 (boundsBefore K231) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low235 : Lower true (varsX 235) (graphGoal 235) 7 := lower_forest (g:=g235) (i:=0) (hints:=1460666369) (before_sound K231 V231) g235G g235T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K235 := extendKnown K231 7 [(235,[]),(237,[33,101]),(243,[67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V235 : Known true K235 := extend_ok (m:=235) V231 low235 (by decide +kernel)
def g249Y : Array (Bits × Bits) := #[(((((16777215 * 4294967296 + 4293918975) * 4294967296 + 4294948235) * 4294967296 + 1097532922) * 4294967296 + 2147487743),((((8946210 * 4294967296 + 572557832) * 4294967296 + 2156442627) * 4294967296 + 1090585946) * 4294967296 + 153391689)),(0x0,0x0),(0x0,0x0),(((((16777215 * 4294967296 + 4294967040) * 4294967296 + 268421545) * 4294967296 + 3666137753) * 4294967296 + 3221483583),((((1115204 * 4294967296 + 1145114641) * 4294967296 + 554715560) * 4294967296 + 2189689473) * 4294967296 + 3528008850)),(((((255 * 4294967296 + 4294967295) * 4294967296 + 4026546230) * 4294967296 + 955178023) * 4294967296 + 262080),((((2238600 * 4294967296 + 2290229282) * 4294967296 + 35782676) * 4294967296 + 946526244) * 4294967296 + 613566756)),(((((16776960 * 4294967296 + 0) * 4294967296 + 18163) * 4294967296 + 3227307972) * 4294967296 + 16515072),((((3944463 * 4294967296 + 251935811) * 4294967296 + 3292284131) * 4294967296 + 1079824068) * 4294967296 + 119304647)),(0x48ad2f1bac4a7f000000,((((4177935 * 4294967296 + 4027039868) * 4294967296 + 130042029) * 4294967296 + 169585738) * 4294967296 + 119304647)),(0xe754b7112b657ffc0000,((((12583152 * 4294967296 + 524416) * 4294967296 + 134259472) * 4294967296 + 3036676385) * 4294967296 + 2028179000)),(0x0,0x0)]
def g249C : List ColumnInfo := [(0,128,25,96,6)]
def g249A : List (List Nat) := [[],[101],[67],[67,101],[48],[48,101],[48,64],[48,64,101],[64,48],[64,48,101],[64],[64,101]]
def g249D6 (j : Nat) : Nat := 0x7f
def g249L : Nat → Packing
  | 6 => (1,0,1,0,0,0,0,g249D6)
  | _ => emptyPacking
def g249I (_ _ : Nat) : Option (Nat × Nat) := none
def g249 : Forest := ⟨249,6,fun i => g249Y[i]?.getD (0,0),g249C,g249A,g249L,g249I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249P6_0 : block g249 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g249B6 : block g249 6 0 1=true := g249P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249T : checkedTables g249 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g249 0 0 0 = true)
  · exact (rfl : block g249 1 0 0 = true)
  · exact (rfl : block g249 2 0 0 = true)
  · exact (rfl : block g249 3 0 0 = true)
  · exact (rfl : block g249 4 0 0 = true)
  · exact (rfl : block g249 5 0 0 = true)
  · exact g249B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249G : graphValid g249 (boundsBefore K235) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low249 : Lower true (varsX 249) (graphGoal 249) 7 := lower_forest (g:=g249) (i:=0) (hints:=1466957827) (before_sound K235 V235) g249G g249T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K249 := extendKnown K235 7 [(249,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V249 : Known true K249 := extend_ok (m:=249) V235 low249 (by decide +kernel)
def g127Y : Array (Bits × Bits) := #[(((((16728114 * 4294967296 + 2191635349) * 4294967296 + 1724712164) * 4294967296 + 3271557120) * 4294967296 + 268435455),((((50 * 4294967296 + 2149589120) * 4294967296 + 583598084) * 4294967296 + 3223339137) * 4294967296 + 33818640)),(((((16724741 * 4294967296 + 1758348710) * 4294967296 + 2635153741) * 4294967296 + 1694499839) * 4294967296 + 4026531967),((((4719360 * 4294967296 + 1619936518) * 4294967296 + 2618310976) * 4294967296 + 18362464) * 4294967296 + 3246589452)),(((((42708 * 4294967296 + 105979466) * 4294967296 + 1347990419) * 4294967296 + 2885811207) * 4294967296 + 4026548096),((((9576644 * 4294967296 + 105978368) * 4294967296 + 1073754259) * 4294967296 + 738593816) * 4294967296 + 811647363)),(((((22633 * 4294967296 + 1400774939) * 4294967296 + 2293381762) * 4294967296 + 1006501888) * 4294967296 + 2080768),((((1855497 * 4294967296 + 1398538523) * 4294967296 + 137372290) * 4294967296 + 726308138) * 4294967296 + 1420382885)),(((((3534 * 4294967296 + 2576862272) * 4294967296 + 4012252449) * 4294967296 + 419299328) * 4294967296 + 266338304),((((14683588 * 4294967296 + 142855232) * 4294967296 + 3305512225) * 4294967296 + 278211156) * 4294967296 + 2840765770)),(((((4467 * 4294967296 + 1833531505) * 4294967296 + 52948617) * 4294967296 + 3422553080) * 4294967296 + 0),((((4211 * 4294967296 + 222378097) * 4294967296 + 52932233) * 4294967296 + 3437744031) * 4294967296 + 1048377843)),(((((52905 * 4294967296 + 613042526) * 4294967296 + 732930878) * 4294967296 + 2147613696) * 4294967296 + 0),((((52777 * 4294967296 + 545931614) * 4294967296 + 732922668) * 4294967296 + 2163864551) * 4294967296 + 3483319932)),(0x0,0x0),(0x0,0x0)]
def g127C : List ColumnInfo := [(32,0,95,0,9),(64,0,63,0,9),(0,32,93,2,8),(0,64,59,4,8),(8,0,119,0,8),(16,0,111,0,8),(2,0,93,0,7),(2,32,93,0,7),(4,0,59,0,7),(4,64,59,0,7),(0,8,102,17,6),(0,16,102,9,6),(1,0,126,0,6),(24,0,103,0,6),(40,0,87,0,6),(64,32,29,2,6),(72,0,55,0,6),(1,8,102,16,5),(1,16,102,8,5),(2,64,25,4,5),(4,32,25,2,5),(8,16,102,1,5),(8,32,85,2,5),(8,64,51,4,5),(16,8,102,1,5),(66,0,29,0,5),(66,32,29,0,5),(68,32,25,2,5),(6,32,25,0,4),(9,16,102,0,4),(10,32,85,0,4),(12,64,51,0,4),(17,8,102,0,4),(25,0,102,0,4),(38,64,25,0,4)]
def g127A : List (List Nat) := [[],[67],[33,101],[33,67,101]]
def g127D5 (j : Nat) : Nat := ((((((((((((252051 * 4294967296 + 201988904) * 4294967296 + 2573606481) * 4294967296 + 2350939561) * 4294967296 + 1642473798) * 4294967296 + 816084643) * 4294967296 + 1931289876) * 4294967296 + 3271809421) * 4294967296 + 3529675859) * 4294967296 + 212231462) * 4294967296 + 570503500) * 4294967296 + 682402397) * 4294967296 + 3091582224)
def g127D6 (j : Nat) : Nat := ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((23200256 * 4294967296 + 638452744) * 4294967296 + 1679) * 4294967296 + 3758358558) * 4294967296 + 136343680) * 4294967296 + 2147493826) * 4294967296 + 67108864) * 4294967296 + 0) * 4294967296 + 472391680) * 4294967296 + 8320) * 4294967296 + 2692775936) * 4294967296 + 6863382) * 4294967296 + 2149064192) * 4294967296 + 536920962) * 4294967296 + 3287286112) * 4294967296 + 4196892696) * 4294967296 + 6356480) * 4294967296 + 1080098304) * 4294967296 + 1480073312) * 4294967296 + 3326099608) * 4294967296 + 543748183) * 4294967296 + 2183008226) * 4294967296 + 4160870229) * 4294967296 + 2773043793) * 4294967296 + 3561293118) * 4294967296 + 1280500909) * 4294967296 + 591925636) * 4294967296 + 1427259728) * 4294967296 + 603782206) * 4294967296 + 1331940592) * 4294967296 + 995009436) * 4294967296 + 3744927123) * 4294967296 + 1490236428) * 4294967296 + 2197863726) * 4294967296 + 2339557538) * 4294967296 + 667513424) * 4294967296 + 2434942913) * 4294967296 + 2825328901) * 4294967296 + 1901086479) * 4294967296 + 3284188199) * 4294967296 + 151068673) * 4294967296 + 2279109902) * 4294967296 + 1653893759) * 4294967296 + 683781650) * 4294967296 + 2367645222) * 4294967296 + 633491875) * 4294967296 + 3968124088) * 4294967296 + 1245245334) * 4294967296 + 1619461318) * 4294967296 + 531829520) * 4294967296 + 3768115958) * 4294967296 + 308419603) * 4294967296 + 477544780) * 4294967296 + 1132618574) * 4294967296 + 3374717297) * 4294967296 + 2351558434) * 4294967296 + 3140366726) * 4294967296 + 526751865) * 4294967296 + 1177586684) * 4294967296 + 2467244230) * 4294967296 + 410879837) * 4294967296 + 2769863215) * 4294967296 + 3004933283) * 4294967296 + 407238241) * 4294967296 + 1922327308) * 4294967296 + 3066113618) * 4294967296 + 2355177433) * 4294967296 + 2307543436) * 4294967296 + 821759793) * 4294967296 + 1244759643) * 4294967296 + 3768001858) * 4294967296 + 816049340) * 4294967296 + 3299362325) * 4294967296 + 2643582151) * 4294967296 + 1153603538) * 4294967296 + 3819094680) * 4294967296 + 1920846964) * 4294967296 + 1481837663) * 4294967296 + 3127905034) * 4294967296 + 1632889201) * 4294967296 + 3528543290) * 4294967296 + 1055275594) * 4294967296 + 696668125) * 4294967296 + 405357872) * 4294967296 + 2481767621) * 4294967296 + 681974847) * 4294967296 + 1956160788) * 4294967296 + 3274174092) * 4294967296 + 77764715) * 4294967296 + 1770553420) * 4294967296 + 1393336250) * 4294967296 + 1883931233) * 4294967296 + 3287763337) * 4294967296 + 1347173682) * 4294967296 + 2259724297) * 4294967296 + 2277920997) * 4294967296 + 352399514) * 4294967296 + 3972309784) * 4294967296 + 638647704) * 4294967296 + 3706071106) * 4294967296 + 2549255068) * 4294967296 + 3305657266) * 4294967296 + 1232526545) * 4294967296 + 175524142) * 4294967296 + 3415875979) * 4294967296 + 3614314867) * 4294967296 + 1144123170) * 4294967296 + 3284945028) * 4294967296 + 1063663417) * 4294967296 + 2299569660) * 4294967296 + 2733060386) * 4294967296 + 452170080) * 4294967296 + 639910494) * 4294967296 + 4062971076) * 4294967296 + 2287702601) * 4294967296 + 1984712971) * 4294967296 + 2026392649) * 4294967296 + 2317434665) * 4294967296 + 1912680772) * 4294967296 + 669197376) * 4294967296 + 640190073) * 4294967296 + 3703051393) * 4294967296 + 280437906) * 4294967296 + 3976733202) * 4294967296 + 4120418465) * 4294967296 + 71491122) * 4294967296 + 320086152) * 4294967296 + 1370638726) * 4294967296 + 1545934910) * 4294967296 + 3427552132) * 4294967296 + 2739378441) * 4294967296 + 2305856615) * 4294967296 + 858275878) * 4294967296 + 696580196) * 4294967296 + 2282013968)
def g127H6 (j : Nat) : Nat := (((((1610612736 * 4294967296 + 2304) * 4294967296 + 1) * 4294967296 + 2416934912) * 4294967296 + 2) * 4294967296 + 1428160512)
def g127D7 (j : Nat) : Nat := (if j<1 then (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((1879210096 * 4294967296 + 3227558224) * 4294967296 + 1208008828) * 4294967296 + 205021608) * 4294967296 + 1024688160) * 4294967296 + 839783454) * 4294967296 + 135341582) * 4294967296 + 370082688) * 4294967296 + 3280473155) * 4294967296 + 2216560773) * 4294967296 + 2151908801) * 4294967296 + 3758295336) * 4294967296 + 1902181376) * 4294967296 + 3496003640) * 4294967296 + 1349534592) * 4294967296 + 3322962168) * 4294967296 + 858013196) * 4294967296 + 429005849) * 4294967296 + 2416979843) * 4294967296 + 3233964481) * 4294967296 + 2205186076) * 4294967296 + 1348869212) * 4294967296 + 19074587) * 4294967296 + 109103523) * 4294967296 + 2311438960) * 4294967296 + 1220702328) * 4294967296 + 17889340) * 4294967296 + 170537038) * 4294967296 + 85889567) * 4294967296 + 109842734) * 4294967296 + 2411791619) * 4294967296 + 98600040) * 4294967296 + 3790632968) * 4294967296 + 2691210270) * 4294967296 + 4656672) * 4294967296 + 201572547) * 4294967296 + 2282947696) * 4294967296 + 820146552) * 4294967296 + 2617394716) * 4294967296 + 1578041379) * 4294967296 + 2265982465) * 4294967296 + 3764503561) * 4294967296 + 4027123825) * 4294967296 + 939822136) * 4294967296 + 1887317760) * 4294967296 + 404825984) * 4294967296 + 2265720257) * 4294967296 + 3758377256) * 4294967296 + 1907932226) * 4294967296 + 1078742706) * 4294967296 + 3929969895) * 4294967296 + 1045619774) * 4294967296 + 585113038) * 4294967296 + 3662517719) * 4294967296 + 1297929437) * 4294967296 + 902872271) * 4294967296 + 3423384008) * 4294967296 + 2085929788) * 4294967296 + 163482558) * 4294967296 + 3099294901) * 4294967296 + 724676874) * 4294967296 + 3870128813) * 4294967296 + 2831838116) * 4294967296 + 437755753) * 4294967296 + 3281623416) * 4294967296 + 2517190801) * 4294967296 + 3910701209) * 4294967296 + 59758830) * 4294967296 + 2372456588) * 4294967296 + 414944088) * 4294967296 + 2794027135) * 4294967296 + 2265473413) * 4294967296 + 676102984) * 4294967296 + 176142316) * 4294967296 + 2101853306) * 4294967296 + 3617487239) * 4294967296 + 2306320208) * 4294967296 + 1928793711) * 4294967296 + 4141771878) * 4294967296 + 3077101164) * 4294967296 + 1689662305) * 4294967296 + 637754917) * 4294967296 + 3243865471) * 4294967296 + 1450528594) * 4294967296 + 1426935636) * 4294967296 + 3712656521) * 4294967296 + 1192518212) * 4294967296 + 337657843) * 4294967296 + 3879383928) * 4294967296 + 896740656) * 4294967296 + 853683074) * 4294967296 + 2535977548) * 4294967296 + 582091037) * 4294967296 + 1907169329) * 4294967296 + 1343381756) * 4294967296 + 220246280) * 4294967296 + 1885733536) * 4294967296 + 13620285) * 4294967296 + 3244414932) * 4294967296 + 902451687) * 4294967296 + 3560540753) * 4294967296 + 3623368130) * 4294967296 + 1373100085) * 4294967296 + 3260143572) * 4294967296 + 901927383) * 4294967296 + 4163224145) * 4294967296 + 3621266882) * 4294967296 + 1369438245) * 4294967296 + 3509690328) * 4294967296 + 231289295) * 4294967296 + 4148791601) * 4294967296 + 3486992777) * 4294967296 + 833607689) * 4294967296 + 2301751142) * 4294967296 + 621097423) * 4294967296 + 3861758257) * 4294967296 + 2681741761) * 4294967296 + 835708449) * 4294967296 + 3241269204) * 4294967296 + 1036603623) * 4294967296 + 3560540496) * 4294967296 + 3086493142) * 4294967296 + 815781917) * 4294967296 + 3526414296) * 4294967296 + 1707487391) * 4294967296 + 4163225136) * 4294967296 + 3487000006) * 4294967296 + 816838773) * 4294967296 + 2251345911) * 4294967296 + 1166422223) * 4294967296 + 3611657776) * 4294967296 + 2952267142) * 4294967296 + 817354873) * 4294967296 + 1177610199) * 4294967296 + 1766207703) * 4294967296 + 4148774448) * 4294967296 + 3621210438) * 4294967296 + 817354793) * 4294967296 + 1177606103) * 4294967296 + 692465895) * 4294967296 + 3861464624) * 4294967296 + 3084388678) * 4294967296 + 815782004) * 4294967296 + 2251349847) * 4294967296 + 344338615) * 4294967296 + 4163191344) * 4294967296 + 3621201218) * 4294967296 + 820504101) * 4294967296 + 1110503318) * 4294967296 + 419574007) * 4294967296 + 2769879600) * 4294967296 + 2681744837) * 4294967296 + 818935621) * 4294967296 + 2234575863) * 4294967296 + 1166356687) * 4294967296 + 3611657520) * 4294967296 + 3955705221) * 4294967296 + 820892725) * 4294967296 + 2234560504) * 4294967296 + 92614871) * 4294967296 + 4148774192) * 4294967296 + 4093069637) * 4294967296 + 819451721) * 4294967296 + 1160836039) * 4294967296 + 1229271285) * 4294967296 + 3560523056) * 4294967296 + 3084396869) * 4294967296 + 819459881) * 4294967296 + 1160832998) * 4294967296 + 692400311) * 4294967296 + 3624486192) * 4294967296 + 3187156165) * 4294967296 + 819853092) * 4294967296 + 3308318182) * 4294967296 + 616902875) * 4294967296 + 4148462896) * 4294967296 + 3086492993) * 4294967296 + 820504101) * 4294967296 + 1093726102) * 4294967296 + 419508471) * 4294967296 + 2769879344) * 4294967296 + 4019590401) * 4294967296 + 821536021) * 4294967296 + 19971544) * 4294967296 + 415314157) * 4294967296 + 3591946544) * 4294967296 + 4125432001) * 4294967296 + 815781933) * 4294967296 + 3457200088) * 4294967296 + 2039091407) * 4294967296 + 4147743248) * 4294967296 + 3486988682) * 4294967296 + 279959561) * 4294967296 + 2316345304) * 4294967296 + 768413903) * 4294967296 + 3614297360) * 4294967296 + 2683839949) * 4294967296 + 282056549) * 4294967296 + 3440425976) * 4294967296 + 1171067102) * 4294967296 + 4146448656) * 4294967296 + 2950199689) * 4294967296 + 282064697) * 4294967296 + 2299580375) * 4294967296 + 965284015) * 4294967296 + 3624503568) * 4294967296 + 4015482053) * 4294967296 + 280983588) * 4294967296 + 3306221414) * 4294967296 + 616894718) * 4294967296 + 1998882064) * 4294967296 + 3153609921) * 4294967296 + 285161492) * 4294967296 + 2165374739) * 4294967296 + 344002751) * 4294967296 + 2014609680) * 4294967296 + 4266792065) * 4294967296 + 284120936) * 4294967296 + 1091616600) * 4294967296 + 675352815) * 4294967296 + 1713914128) * 4294967296 + 4279371841) * 4294967296 + 281532517) * 4294967296 + 3260127224) * 4294967296 + 633491911) * 4294967296 + 3861234257) * 4294967296 + 2614641089) * 4294967296 + 832493601) * 4294967296 + 3241256920) * 4294967296 + 159994055) * 4294967296 + 3613775408) * 4294967296 + 2547546438) * 4294967296 + 815523953) * 4294967296 + 3509639671) * 4294967296 + 835793099) * 4294967296 + 4148528432) * 4294967296 + 3556198725) * 4294967296 + 817727492) * 4294967296 + 3308311543) * 4294967296 + 1161900281) * 4294967296 + 2486501680) * 4294967296 + 2616739278) * 4294967296 + 277862521) * 4294967296 + 2316349336) * 4294967296 + 160043182) * 4294967296 + 3357923600) * 4294967296 + 2616739277) * 4294967296 + 277862521) * 4294967296 + 2299572056) * 4294967296 + 428413103) * 4294967296 + 2550761744) * 4294967296 + 3204973765) * 4294967296 + 279934997) * 4294967296 + 2165374482) * 4294967296 + 344002695) * 4294967296 + 3631843921) else ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((3136 * 4294967296 + 1484828929) * 4294967296 + 1647368225) * 4294967296 + 2241375296) * 4294967296 + 3632300216) * 4294967296 + 747684508) * 4294967296 + 373848128) * 4294967296 + 403177984) * 4294967296 + 335938048) * 4294967296 + 2147771011) * 4294967296 + 2218860547) * 4294967296 + 3244294850) * 4294967296 + 50495492) * 4294967296 + 63172728) * 4294967296 + 37855408) * 4294967296 + 1209270288) * 4294967296 + 856692256) * 4294967296 + 944637953) * 4294967296 + 2451968006) * 4294967296 + 33587205) * 4294967296 + 2743105537) * 4294967296 + 2160082958) * 4294967296 + 143927811) * 4294967296 + 70925840) * 4294967296 + 130027571) * 4294967296 + 2214699152) * 4294967296 + 45170955) * 4294967296 + 3778041857) * 4294967296 + 813706760) * 4294967296 + 2018120196) * 4294967296 + 1008864260) * 4294967296 + 2165410318) * 4294967296 + 319258890) * 4294967296 + 142803232) * 4294967296 + 1136795872) * 4294967296 + 1099280536) * 4294967296 + 1007190064) * 4294967296 + 268697633) * 4294967296 + 486934540) * 4294967296 + 495239648) * 4294967296 + 1359119248) * 4294967296 + 1612974224) * 4294967296 + 3961654328) * 4294967296 + 772810798) * 4294967296 + 270538760) * 4294967296 + 33558532) * 4294967296 + 673185925) * 4294967296 + 118195208) * 4294967296 + 69738496) * 4294967296 + 2231831050) * 4294967296 + 218240532) * 4294967296 + 472397904) * 4294967296 + 1082351938) * 4294967296 + 2697996596) * 4294967296 + 1899012321) * 4294967296 + 1099096322) * 4294967296 + 2195784322) * 4294967296 + 50594824) * 4294967296 + 540033088) * 4294967296 + 1612711936) * 4294967296 + 1075774222) * 4294967296 + 403506304) * 4294967296 + 218761295) * 4294967296 + 2173111302) * 4294967296 + 17309704) * 4294967296 + 201588960) * 4294967296 + 2303041872) * 4294967296 + 65073200) * 4294967296 + 3783731233))
def g127H7 (j : Nat) : Nat := ((((((((((((((((((((((((((((((((((((((((((((((15 * 4294967296 + 2596951091) * 4294967296 + 2437614816) * 4294967296 + 2147521158) * 4294967296 + 369098752) * 4294967296 + 2702180352) * 4294967296 + 169716109) * 4294967296 + 2814478394) * 4294967296 + 1933574144) * 4294967296 + 12634) * 4294967296 + 560082944) * 4294967296 + 20854900) * 4294967296 + 3357274118) * 4294967296 + 315724582) * 4294967296 + 2316724736) * 4294967296 + 33657692) * 4294967296 + 43045971) * 4294967296 + 315621523) * 4294967296 + 621674496) * 4294967296 + 2858) * 4294967296 + 798998) * 4294967296 + 724965607) * 4294967296 + 2566914048) * 4294967296 + 51) * 4294967296 + 2602861248) * 4294967296 + 3309453) * 4294967296 + 10) * 4294967296 + 536912290) * 4294967296 + 573248293) * 4294967296 + 1514351520) * 4294967296 + 1073751632) * 4294967296 + 14728873) * 4294967296 + 2688354897) * 4294967296 + 3792052895) * 4294967296 + 520095503) * 4294967296 + 471185) * 4294967296 + 134545791) * 4294967296 + 922746880) * 4294967296 + 570855744) * 4294967296 + 2571829259) * 4294967296 + 1417016839) * 4294967296 + 7170) * 4294967296 + 3987079183) * 4294967296 + 789324568) * 4294967296 + 2281717800) * 4294967296 + 3221625888) * 4294967296 + 3275755648)
def g127D8 (j : Nat) : Nat := ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((1967427 * 4294967296 + 2185330820) * 4294967296 + 404038930) * 4294967296 + 100676650) * 4294967296 + 639398056) * 4294967296 + 1144790020) * 4294967296 + 1904681248) * 4294967296 + 1348472834) * 4294967296 + 2454833541) * 4294967296 + 1094732061) * 4294967296 + 172432435) * 4294967296 + 117515804) * 4294967296 + 1413220468) * 4294967296 + 1276187015) * 4294967296 + 2269286768) * 4294967296 + 1362108872) * 4294967296 + 1149469056) * 4294967296 + 226955548) * 4294967296 + 855835942) * 4294967296 + 475122716) * 4294967296 + 77099345) * 4294967296 + 283136096) * 4294967296 + 566740040) * 4294967296 + 504120451) * 4294967296 + 1132544384) * 4294967296 + 1082599702) * 4294967296 + 235274308) * 4294967296 + 1981575616) * 4294967296 + 3424388248) * 4294967296 + 1907388434) * 4294967296 + 1640252608) * 4294967296 + 2273922325) * 4294967296 + 554894873) * 4294967296 + 877943836) * 4294967296 + 141656353) * 4294967296 + 2184188272) * 4294967296 + 1640252940) * 4294967296 + 184731073) * 4294967296 + 3226017315) * 4294967296 + 386011426) * 4294967296 + 475104408) * 4294967296 + 1896939969) * 4294967296 + 1886396678) * 4294967296 + 122100994) * 4294967296 + 3250589982) * 4294967296 + 405738508) * 4294967296 + 538378771) * 4294967296 + 102510752) * 4294967296 + 2953841752) * 4294967296 + 2557546961) * 4294967296 + 810770884) * 4294967296 + 1161895365) * 4294967296 + 2269712667) * 4294967296 + 604115717) * 4294967296 + 474505344) * 4294967296 + 1613767768) * 4294967296 + 1276903618) * 4294967296 + 1366323206) * 4294967296 + 75825928) * 4294967296 + 3313811474) * 4294967296 + 3242664043) * 4294967296 + 386011421) * 4294967296 + 610809996) * 4294967296 + 1481380961) * 4294967296 + 2208440545) * 4294967296 + 810665095) * 4294967296 + 3250603396) * 4294967296 + 202835712) * 4294967296 + 1615347804) * 4294967296 + 469803473) * 4294967296 + 1886388872) * 4294967296 + 1153548298) * 4294967296 + 487786240) * 4294967296 + 876888204) * 4294967296 + 202666449) * 4294967296 + 1881235729) * 4294967296 + 3527772293) * 4294967296 + 3246671382) * 4294967296 + 386334817) * 4294967296 + 474245212) * 4294967296 + 286552529) * 4294967296 + 1630564355) * 4294967296 + 1145373889) * 4294967296 + 3222803732) * 4294967296 + 672335616) * 4294967296 + 1213209601) * 4294967296 + 613970193) * 4294967296 + 2193756416) * 4294967296 + 4029771873) * 4294967296 + 3272148417) * 4294967296 + 3221915421) * 4294967296 + 405547028) * 4294967296 + 268697894) * 4294967296 + 472944720) * 4294967296 + 1093409793) * 4294967296 + 410292769) * 4294967296 + 1630540321) * 4294967296 + 3306848274) * 4294967296 + 1233588506) * 4294967296 + 488910908) * 4294967296 + 1548485028) * 4294967296 + 2557575680) * 4294967296 + 4026937441) * 4294967296 + 3292989445) * 4294967296 + 1153439937) * 4294967296 + 2266046508) * 4294967296 + 672404227) * 4294967296 + 102573185) * 4294967296 + 3232800848) * 4294967296 + 1276904600) * 4294967296 + 1918984496) * 4294967296 + 304203026) * 4294967296 + 365019143) * 4294967296 + 1141972043) * 4294967296 + 71572616) * 4294967296 + 1482178852) * 4294967296 + 469832856) * 4294967296 + 1912899376) * 4294967296 + 1879331425) * 4294967296 + 3351363657) * 4294967296 + 2265991943) * 4294967296 + 1852508) * 4294967296 + 207372433) * 4294967296 + 2706534769) * 4294967296 + 25609669) * 4294967296 + 3293087251) * 4294967296 + 655823620) * 4294967296 + 408195084) * 4294967296 + 1547727281) * 4294967296 + 2687594770) * 4294967296 + 566608961) * 4294967296 + 2148667721) * 4294967296 + 2266783788) * 4294967296 + 1193745939) * 4294967296 + 117475391) * 4294967296 + 1090650447) * 4294967296 + 3162239956) * 4294967296 + 506785095) * 4294967296 + 1262068167) * 4294967296 + 1307864307) * 4294967296 + 1478120656) * 4294967296 + 1181430433) * 4294967296 + 2387360863) * 4294967296 + 3002210116) * 4294967296 + 3058013995) * 4294967296 + 1632848492) * 4294967296 + 1370652691) * 4294967296 + 1687700639) * 4294967296 + 606149192) * 4294967296 + 2487431696) * 4294967296 + 270827203) * 4294967296 + 3810427118) * 4294967296 + 1195653297) * 4294967296 + 3087885416) * 4294967296 + 1126897824) * 4294967296 + 3192235051) * 4294967296 + 1900546484) * 4294967296 + 1254243089) * 4294967296 + 1619280868) * 4294967296 + 485545478) * 4294967296 + 338542927) * 4294967296 + 163595585) * 4294967296 + 3960352870) * 4294967296 + 47453120) * 4294967296 + 2332270614) * 4294967296 + 1082393136) * 4294967296 + 4188690) * 4294967296 + 1677676754) * 4294967296 + 536535832) * 4294967296 + 2144475331) * 4294967296 + 4270892575) * 4294967296 + 4123660543) * 4294967296 + 3999827965) * 4294967296 + 1933852650) * 4294967296 + 438435804) * 4294967296 + 2433743588) * 4294967296 + 2290078500) * 4294967296 + 1140791330) * 4294967296 + 536133904) * 4294967296 + 4291037319) * 4294967296 + 4246750263) * 4294967296 + 3927622623) * 4294967296 + 1357192190) * 4294967296 + 3902332887) * 4294967296 + 1153892281) * 4294967296 + 641464713) * 4294967296 + 838575689) * 4294967296 + 2415214924) * 4294967296 + 1878753891) * 4294967296 + 2132546331) * 4294967296 + 4209414391) * 4294967296 + 3560260542) * 4294967296 + 2569674229) * 4294967296 + 3593519086) * 4294967296 + 2441477492) * 4294967296 + 2351950732) * 4294967296 + 1639929955) * 4294967296 + 251437848) * 4294967296 + 2010450115) * 4294967296 + 4246750743) * 4294967296 + 4258345207) * 4294967296 + 4001990141) * 4294967296 + 1951153635) * 4294967296 + 2724329296) * 4294967296 + 3540778722) * 4294967296 + 2557466132) * 4294967296 + 3284084902) * 4294967296 + 527746352) * 4294967296 + 4020898183) * 4294967296 + 4198517823) * 4294967296 + 3389153783) * 4294967296 + 2350059002) * 4294967296 + 3976749047) * 4294967296 + 943914681) * 4294967296 + 3256352202) * 4294967296 + 280997456) * 4294967296 + 2264818308) * 4294967296 + 938148897) * 4294967296 + 4270334221) * 4294967296 + 4209805407) * 4294967296 + 4147397374) * 4294967296 + 3114407933) * 4294967296 + 3373318062) * 4294967296 + 1216806498) * 4294967296 + 1145022858) * 4294967296 + 570247249) * 4294967296 + 234537096) * 4294967296 + 2141324355) * 4294967296 + 4237304351) * 4294967296 + 3628142751) * 4294967296 + 3993701757) * 4294967296 + 1922331635) * 4294967296 + 346251100) * 4294967296 + 622526180) * 4294967296 + 2825381413) * 4294967296 + 1128181802) * 4294967296 + 385732912)
def g127H8 (j : Nat) : Nat := (if j<1 then (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((250950656 * 4294967296 + 38151226) * 4294967296 + 925905) * 4294967296 + 1409294158) * 4294967296 + 0) * 4294967296 + 21471232) * 4294967296 + 0) * 4294967296 + 1055) * 4294967296 + 1085669376) * 4294967296 + 0) * 4294967296 + 238653824) * 4294967296 + 113825792) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 1195376640) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 3762176) * 4294967296 + 17012) * 4294967296 + 738197504) * 4294967296 + 0) * 4294967296 + 1184512) * 4294967296 + 14658) * 4294967296 + 727312) * 4294967296 + 2751463424) * 4294967296 + 282240) * 4294967296 + 5267456) * 4294967296 + 1) * 4294967296 + 1275068416) * 4294967296 + 304768640) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 882688) * 4294967296 + 238965870) * 4294967296 + 3470661376) * 4294967296 + 0) * 4294967296 + 826880) * 4294967296 + 0) * 4294967296 + 56) * 4294967296 + 4026531840) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 3756032) * 4294967296 + 0) * 4294967296 + 613376) * 4294967296 + 15750) * 4294967296 + 3915382784) * 4294967296 + 9535488) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 556) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 212205568) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 3952640) * 4294967296 + 0) * 4294967296 + 588544) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 584) * 4294967296 + 0) * 4294967296 + 3462) * 4294967296 + 2147582016) * 4294967296 + 8481366) * 4294967296 + 1073741839) * 4294967296 + 301989888) * 4294967296 + 135856131) * 4294967296 + 3653238784) * 4294967296 + 0) * 4294967296 + 137) * 4294967296 + 0) * 4294967296 + 933632) * 4294967296 + 2759) * 4294967296 + 3937927168) * 4294967296 + 17514496) * 4294967296 + 12845056) * 4294967296 + 16117760) * 4294967296 + 128256) * 4294967296 + 0) * 4294967296 + 3) * 4294967296 + 2638217216) * 4294967296 + 2916352) * 4294967296 + 1236480) * 4294967296 + 58900480) * 4294967296 + 99456) * 4294967296 + 0) * 4294967296 + 13) * 4294967296 + 2885681152) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 816) * 4294967296 + 6588366) * 4294967296 + 1610644128) * 4294967296 + 0) * 4294967296 + 8312) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 89) * 4294967296 + 487194624) * 4294967296 + 0) * 4294967296 + 7360512) * 4294967296 + 83904) * 4294967296 + 10717184) * 4294967296 + 764018688) * 4294967296 + 958) * 4294967296 + 1073741824) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 496640) * 4294967296 + 9756672) * 4294967296 + 505606) * 4294967296 + 2415919104) * 4294967296 + 0) * 4294967296 + 1497) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 148) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 1189888) * 4294967296 + 0) * 4294967296 + 894443520) * 4294967296 + 292290560) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 12800) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 153616384) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 5) * 4294967296 + 3008650406) * 4294967296 + 268435456) * 4294967296 + 0) * 4294967296 + 4767744) * 4294967296 + 1075685248) * 4294967296 + 0) * 4294967296 + 400320) * 4294967296 + 0) * 4294967296 + 246843) * 4294967296 + 939524096) * 4294967296 + 828894768) * 4294967296 + 0) * 4294967296 + 3) * 4294967296 + 394264948) * 4294967296 + 1815150592) * 4294967296 + 0) * 4294967296 + 172) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 5) * 4294967296 + 268435870) * 4294967296 + 1073741824) * 4294967296 + 137) * 4294967296 + 3796738960) * 4294967296 + 100) * 4294967296 + 951681024) * 4294967296 + 0) * 4294967296 + 2160) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 514404) * 4294967296 + 201326592) * 4294967296 + 26) * 4294967296 + 1593835520) * 4294967296 + 955645952) * 4294967296 + 0) * 4294967296 + 471072768) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 22448) * 4294967296 + 1879048192) * 4294967296 + 3775671808) * 4294967296 + 58793984) * 4294967296 + 0) * 4294967296 + 4000) * 4294967296 + 2147483648) * 4294967296 + 0) * 4294967296 + 110362624) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 70418432) * 4294967296 + 928256) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 12845056) * 4294967296 + 0) * 4294967296 + 2054) * 4294967296 + 2147483648) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 185344) * 4294967296 + 24949) * 4294967296 + 3745513573) * 4294967296 + 1385918489) * 4294967296 + 3834642432) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 2027683840) * 4294967296 + 0) * 4294967296 + 215089152) * 4294967296 + 5670338) * 4294967296 + 1160354320) * 4294967296 + 0) * 4294967296 + 33685504) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 499072) * 4294967296 + 5950) * 4294967296 + 513200) * 4294967296 + 3321888768) * 4294967296 + 8) * 4294967296 + 251658240) * 4294967296 + 112112) * 4294967296 + 7931904) * 4294967296 + 472842240) * 4294967296 + 0) * 4294967296 + 3) * 4294967296 + 3864476928) * 4294967296 + 338) * 4294967296 + 4257) * 4294967296 + 1073750016) * 4294967296 + 16846848) * 4294967296 + 69632) * 4294967296 + 4096) * 4294967296 + 1048577) * 4294967296 + 623902737) else ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((4814 * 4294967296 + 833624829) * 4294967296 + 2282094592) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 946339840) * 4294967296 + 1088512) * 4294967296 + 172007616) * 4294967296 + 2913792) * 4294967296 + 162037932) * 4294967296 + 414260) * 4294967296 + 2415919104) * 4294967296 + 224640) * 4294967296 + 0) * 4294967296 + 432632) * 4294967296 + 3422552064) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 15) * 4294967296 + 511705088) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 1378308672) * 4294967296 + 0) * 4294967296 + 28) * 4294967296 + 1358954496) * 4294967296 + 14) * 4294967296 + 2608857088) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 1) * 4294967296 + 35651584) * 4294967296 + 0) * 4294967296 + 547356672) * 4294967296 + 0) * 4294967296 + 311552) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 428867584) * 4294967296 + 1850368) * 4294967296 + 0) * 4294967296 + 1258291243) * 4294967296 + 4026531840) * 4294967296 + 1053952) * 4294967296 + 47546368) * 4294967296 + 0) * 4294967296 + 34029568) * 4294967296 + 283115576) * 4294967296 + 1174405158) * 4294967296 + 92351392) * 4294967296 + 4273998) * 4294967296 + 1437647278) * 4294967296 + 288183680) * 4294967296 + 2684357520) * 4294967296 + 130) * 4294967296 + 3221225472) * 4294967296 + 240) * 4294967296 + 4262396128) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 104352) * 4294967296 + 1961) * 4294967296 + 1821786469) * 4294967296 + 924092416) * 4294967296 + 3758096387) * 4294967296 + 2414872512) * 4294967296 + 260122839))
def g127D9 (j : Nat) : Nat := (((((((((((((((((((((((((4338275 * 4294967296 + 3246404723) * 4294967296 + 3512748297) * 4294967296 + 83915264) * 4294967296 + 159522348) * 4294967296 + 1145275141) * 4294967296 + 641487425) * 4294967296 + 549463084) * 4294967296 + 2565210689) * 4294967296 + 2155118692) * 4294967296 + 2722140948) * 4294967296 + 2349917315) * 4294967296 + 2166762568) * 4294967296 + 566722838) * 4294967296 + 544285385) * 4294967296 + 2333214817) * 4294967296 + 1078561554) * 4294967296 + 141672155) * 4294967296 + 2349658620) * 4294967296 + 3108050502) * 4294967296 + 1045775) * 4294967296 + 4247912264) * 4294967296 + 2145587188) * 4294967296 + 3288207615) * 4294967296 + 1143985693) * 4294967296 + 4182211920)
def g127H9 (j : Nat) : Nat := ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((888592 * 4294967296 + 2770442368) * 4294967296 + 405676792) * 4294967296 + 2281703040) * 4294967296 + 28) * 4294967296 + 3947231510) * 4294967296 + 2964324412) * 4294967296 + 1996560289) * 4294967296 + 82880) * 4294967296 + 4287916) * 4294967296 + 1248096811) * 4294967296 + 301990721) * 4294967296 + 2684354564) * 4294967296 + 32009313) * 4294967296 + 1325542573) * 4294967296 + 3328593072) * 4294967296 + 2526065757) * 4294967296 + 3003653440) * 4294967296 + 184820747) * 4294967296 + 2979004416) * 4294967296 + 2404) * 4294967296 + 2147483664) * 4294967296 + 424798208) * 4294967296 + 128080) * 4294967296 + 3708424) * 4294967296 + 580845574) * 4294967296 + 847249408) * 4294967296 + 23177) * 4294967296 + 357582336) * 4294967296 + 117897286) * 4294967296 + 4061241064) * 4294967296 + 3767644693) * 4294967296 + 4059267408) * 4294967296 + 566938332) * 4294967296 + 287309844) * 4294967296 + 872416260) * 4294967296 + 3221259425) * 4294967296 + 2415919104) * 4294967296 + 339476487) * 4294967296 + 3539804676) * 4294967296 + 3561553920) * 4294967296 + 3847636897) * 4294967296 + 4257792000) * 4294967296 + 20608) * 4294967296 + 50675712) * 4294967296 + 2436599258) * 4294967296 + 2113930752) * 4294967296 + 3765436440) * 4294967296 + 144834560) * 4294967296 + 223791525) * 4294967296 + 2651375301) * 4294967296 + 202309632) * 4294967296 + 2812018688) * 4294967296 + 33861808) * 4294967296 + 10) * 4294967296 + 235819144) * 4294967296 + 2954927104) * 4294967296 + 4292608) * 4294967296 + 164761) * 4294967296 + 1711277076) * 4294967296 + 2620343490) * 4294967296 + 436207622) * 4294967296 + 562389841) * 4294967296 + 1288868195) * 4294967296 + 3930847596) * 4294967296 + 28456321) * 4294967296 + 2103474190) * 4294967296 + 3783601337) * 4294967296 + 2349942842) * 4294967296 + 3298498036) * 4294967296 + 1409286144) * 4294967296 + 494644) * 4294967296 + 365718799) * 4294967296 + 2147508682) * 4294967296 + 2086801571) * 4294967296 + 788611908) * 4294967296 + 1281361292) * 4294967296 + 2302209) * 4294967296 + 2195459)
def g127D10 (j : Nat) : Nat := 0x48e28808037f
def g127H10 (j : Nat) : Nat := (((((((((65575 * 4294967296 + 319293089) * 4294967296 + 1293) * 4294967296 + 1116745496) * 4294967296 + 13303820) * 4294967296 + 1073851448) * 4294967296 + 2147483971) * 4294967296 + 2492662162) * 4294967296 + 876260624) * 4294967296 + 16645)
def g127L : Nat → Packing
  | 5 => (6,5,6,0,0,5,0,g127D5)
  | 6 => (59,4,6,0,0,10,0,g127D6)
  | 7 => (127,3,6,0,0,12,0,g127D7)
  | 8 => (78,2,6,0,0,13,0,g127D8)
  | 9 => (10,1,6,0,0,9,0,g127D9)
  | 10 => (1,0,6,0,0,0,0,g127D10)
  | _ => emptyPacking
def g127I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 31 0 7 3 0 g127H6
  | 7 => lookupWord 20 113 6 12 6 2 g127H7
  | 8 => lookupWord 53 797 4 13 7 2 g127H8
  | 9 => lookupWord 33 181 5 13 7 2 g127H9
  | 10 => lookupWord 5 29 3 10 4 2 g127H10
  | _ => fun _ => none
def g127 : Forest := ⟨127,10,fun i => g127Y[i]?.getD (0,0),g127C,g127A,g127L,g127I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P5_0 : block g127 5 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B5 : block g127 5 0 6=true := g127P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6_0 : block g127 6 0 5=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6_5 : block g127 6 5 54=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B6 : block g127 6 0 59=true := (@block_merge g127 6 0 5 54 g127P6_0 g127P6_5)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_0 : block g127 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_1 : block g127 7 1 26=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_27 : block g127 7 27 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_123 : block g127 7 123 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B7 : block g127 7 0 127=true := (@block_merge g127 7 0 27 100 (@block_merge g127 7 0 1 26 g127P7_0 g127P7_1) (@block_merge g127 7 27 96 4 g127P7_27 g127P7_123))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_0 : block g127 8 0 8=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_8 : block g127 8 8 54=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_62 : block g127 8 62 16=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B8 : block g127 8 0 78=true := (@block_merge g127 8 0 8 70 g127P8_0 (@block_merge g127 8 8 54 16 g127P8_8 g127P8_62))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_0 : block g127 9 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_3 : block g127 9 3 7=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B9 : block g127 9 0 10=true := (@block_merge g127 9 0 3 7 g127P9_0 g127P9_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P10_0 : block g127 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B10 : block g127 10 0 1=true := g127P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127T : checkedTables g127 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g127 0 0 0 = true)
  · exact (rfl : block g127 1 0 0 = true)
  · exact (rfl : block g127 2 0 0 = true)
  · exact (rfl : block g127 3 0 0 = true)
  · exact (rfl : block g127 4 0 0 = true)
  · exact g127B5
  · exact g127B6
  · exact g127B7
  · exact g127B8
  · exact g127B9
  · exact g127B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127G : graphValid g127 (boundsBefore K249) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (varsX 127) (graphGoal 127) 11 := lower_forest (g:=g127) (i:=0) (hints:=34603009) (before_sound K249 V249) g127G g127T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K127 := extendKnown K249 11 [(127,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V127 : Known true K127 := extend_ok (m:=127) V249 low127 (by decide +kernel)
def g191Y : Array (Bits × Bits) := #[(((((14698945 * 4294967296 + 1355368099) * 4294967296 + 206036800) * 4294967296 + 0) * 4294967296 + 4294967295),((((2496 * 4294967296 + 1342194176) * 4294967296 + 205717568) * 4294967296 + 151587081) * 4294967296 + 151587081)),(((((10195492 * 4294967296 + 587365210) * 4294967296 + 303603054) * 4294967296 + 65535) * 4294967296 + 255),((((167968 * 4294967296 + 50471242) * 4294967296 + 302554402) * 4294967296 + 1347440720) * 4294967296 + 1347440720)),(((((5466641 * 4294967296 + 748391736) * 4294967296 + 3687858332) * 4294967296 + 255) * 4294967296 + 65280),((((5333521 * 4294967296 + 748260400) * 4294967296 + 3247456412) * 4294967296 + 2795939494) * 4294967296 + 2795939494)),(((((2892857 * 4294967296 + 4214228432) * 4294967296 + 1118403227) * 4294967296 + 16711680) * 4294967296 + 16711680),((((2622521 * 4294967296 + 2872051088) * 4294967296 + 1107843609) * 4294967296 + 842150450) * 4294967296 + 842150450)),(((((452444 * 4294967296 + 2345052263) * 4294967296 + 1168416902) * 4294967296 + 16711680) * 4294967296 + 4278190080),((((451076 * 4294967296 + 13019239) * 4294967296 + 27566214) * 4294967296 + 3301229764) * 4294967296 + 3301229764)),(((((571814 * 4294967296 + 3837571205) * 4294967296 + 3778691189) * 4294967296 + 4278255360) * 4294967296 + 0),((((534790 * 4294967296 + 3834155141) * 4294967296 + 1077035093) * 4294967296 + 117901063) * 4294967296 + 117901063)),(0x0,0x0),(((((6771858 * 4294967296 + 87338772) * 4294967296 + 3050277907) * 4294967296 + 4278190080) * 4294967296 + 0),((((6771856 * 4294967296 + 20197136) * 4294967296 + 3050146818) * 4294967296 + 4177066232) * 4294967296 + 4177066232)),(0x0,0x0)]
def g191C : List ColumnInfo := [(0,128,31,32,9),(128,0,63,0,9),(4,0,187,0,8),(8,0,183,0,8),(16,0,175,0,8),(32,0,31,0,8),(32,128,31,0,8),(0,32,29,130,7),(2,0,189,0,7),(24,0,167,0,7),(0,8,166,17,6),(0,16,166,9,6),(1,0,190,0,6),(4,32,25,130,6),(6,0,185,0,6),(1,8,166,16,5),(1,16,166,8,5),(12,0,179,0,5),(16,8,166,1,5),(9,16,166,0,4)]
def g191A : List (List Nat) := [[],[67]]
def g191D5 (j : Nat) : Nat := 0x2789a42413288530
def g191D6 (j : Nat) : Nat := (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((3 * 4294967296 + 2282232896) * 4294967296 + 1073741824) * 4294967296 + 4042785280) * 4294967296 + 0) * 4294967296 + 1006665728) * 4294967296 + 0) * 4294967296 + 2040617504) * 4294967296 + 4231923792) * 4294967296 + 2115962768) * 4294967296 + 972350053) * 4294967296 + 747849186) * 4294967296 + 807920601) * 4294967296 + 3773461043) * 4294967296 + 416024018) * 4294967296 + 3512510545) * 4294967296 + 617719924) * 4294967296 + 166521455) * 4294967296 + 882427970) * 4294967296 + 268859876) * 4294967296 + 2551300402) * 4294967296 + 2406267136) * 4294967296 + 2571383725) * 4294967296 + 2485130024) * 4294967296 + 2256319012) * 4294967296 + 40177879) * 4294967296 + 2521264776) * 4294967296 + 1393288136) * 4294967296 + 2790328929) * 4294967296 + 2089354442) * 4294967296 + 558639007) * 4294967296 + 616613385) * 4294967296 + 2239325303) * 4294967296 + 948314285) * 4294967296 + 2091050768) * 4294967296 + 3290032024) * 4294967296 + 1549932674) * 4294967296 + 1037237258) * 4294967296 + 1687179178) * 4294967296 + 1551912082) * 4294967296 + 167037072) * 4294967296 + 160579870) * 4294967296 + 4180024880) * 4294967296 + 3290685220) * 4294967296 + 3236851845) * 4294967296 + 1810176061) * 4294967296 + 3373313404) * 4294967296 + 2733095202) * 4294967296 + 300914780) * 4294967296 + 3341042357) * 4294967296 + 4069234916) * 4294967296 + 2288948755) * 4294967296 + 1921798409) * 4294967296 + 4106817545) * 4294967296 + 2317459048) * 4294967296 + 2110398788) * 4294967296 + 861866425) * 4294967296 + 638092792) * 4294967296 + 2783058049) * 4294967296 + 282016663) * 4294967296 + 43000345) * 4294967296 + 3885162961) * 4294967296 + 4406512) * 4294967296 + 4229046280) * 4294967296 + 1997918082) * 4294967296 + 1140919027) * 4294967296 + 1278101632) * 4294967296 + 557422914) * 4294967296 + 20073511) * 4294967296 + 858275878) * 4294967296 + 696580196) * 4294967296 + 1208273184)
def g191H6 (j : Nat) : Nat := 0x7
def g191D7 (j : Nat) : Nat := (if j<1 then (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((436257409 * 4294967296 + 3288470284) * 4294967296 + 205549825) * 4294967296 + 8321) * 4294967296 + 235145246) * 4294967296 + 7373068) * 4294967296 + 67170370) * 4294967296 + 8569348) * 4294967296 + 824182832) * 4294967296 + 807437296) * 4294967296 + 1879244808) * 4294967296 + 268435592) * 4294967296 + 372267288) * 4294967296 + 3255698568) * 4294967296 + 304103441) * 4294967296 + 1678319752) * 4294967296 + 536888193) * 4294967296 + 1610876480) * 4294967296 + 1086390332) * 4294967296 + 439380161) * 4294967296 + 2734958610) * 4294967296 + 2113962018) * 4294967296 + 71569538) * 4294967296 + 545308736) * 4294967296 + 61015103) * 4294967296 + 136989232) * 4294967296 + 2206278148) * 4294967296 + 940622368) * 4294967296 + 2219033100) * 4294967296 + 71047296) * 4294967296 + 545259778) * 4294967296 + 201863224) * 4294967296 + 549478913) * 4294967296 + 2684629016) * 4294967296 + 2151907584) * 4294967296 + 789284620) * 4294967296 + 865627678) * 4294967296 + 1087269921) * 4294967296 + 1123088504) * 4294967296 + 50717921) * 4294967296 + 3758887827) * 4294967296 + 2273330464) * 4294967296 + 1582054942) * 4294967296 + 19036584) * 4294967296 + 2189624713) * 4294967296 + 3789556236) * 4294967296 + 339707659) * 4294967296 + 2555256322) * 4294967296 + 2163767299) * 4294967296 + 2212618251) * 4294967296 + 2273546288) * 4294967296 + 1090395648) * 4294967296 + 4168614625) * 4294967296 + 3758851968) * 4294967296 + 778100920) * 4294967296 + 2013496080) * 4294967296 + 266735120) * 4294967296 + 1132739456) * 4294967296 + 1012801025) * 4294967296 + 14746680) * 4294967296 + 62473157) * 4294967296 + 2334692488) * 4294967296 + 1753253672) * 4294967296 + 1686464592) * 4294967296 + 2217229442) * 4294967296 + 3894968744) * 4294967296 + 343959544) * 4294967296 + 2124928124) * 4294967296 + 3888151335) * 4294967296 + 2893604736) * 4294967296 + 1982291060) * 4294967296 + 3879760807) * 4294967296 + 879945504) * 4294967296 + 1898382447) * 4294967296 + 1726508454) * 4294967296 + 3563873968) * 4294967296 + 1780909158) * 4294967296 + 3864028326) * 4294967296 + 1013147184) * 4294967296 + 1655053408) * 4294967296 + 3858259621) * 4294967296 + 3697075656) * 4294967296 + 1529191512) * 4294967296 + 3850393381) * 4294967296 + 1817568592) * 4294967296 + 1420115026) * 4294967296 + 3844100389) * 4294967296 + 72279272) * 4294967296 + 1302645835) * 4294967296 + 1687701668) * 4294967296 + 1950737488) * 4294967296 + 1143223361) * 4294967296 + 3825745827) * 4294967296 + 3963446216) * 4294967296 + 992189496) * 4294967296 + 3816830755) * 4294967296 + 1681220424) * 4294967296 + 874712109) * 4294967296 + 3803195554) * 4294967296 + 1545822728) * 4294967296 + 497136665) * 4294967296 + 1635259937) * 4294967296 + 1007804680) * 4294967296 + 253811724) * 4294967296 + 1621624864) * 4294967296 + 1409474560) * 4294967296 + 2681736645) * 4294967296 + 849336337) * 4294967296 + 3241320408) * 4294967296 + 231289247) * 4294967296 + 3626090801) * 4294967296 + 3200779466) * 4294967296 + 568251173) * 4294967296 + 3256983544) * 4294967296 + 365572255) * 4294967296 + 4163225136) * 4294967296 + 3740804550) * 4294967296 + 819906597) * 4294967296 + 3325083384) * 4294967296 + 633745567) * 4294967296 + 3631777328) * 4294967296 + 3747027078) * 4294967296 + 815782004) * 4294967296 + 2251349719) * 4294967296 + 612774111) * 4294967296 + 1460962864) * 4294967296 + 2681740745) * 4294967296 + 817756180) * 4294967296 + 3375407064) * 4294967296 + 767897821) * 4294967296 + 3542992176) * 4294967296 + 3187156165) * 4294967296 + 819853092) * 4294967296 + 3308313591) * 4294967296 + 1216688350) * 4294967296 + 4146627888) * 4294967296 + 4241696901) * 4294967296 + 819722052) * 4294967296 + 2234564056) * 4294967296 + 683749565) * 4294967296 + 3625500976) * 4294967296 + 2681740750) * 4294967296 + 551483192) * 4294967296 + 2250301143) * 4294967296 + 948314366) * 4294967296 + 1461224992) * 4294967296 + 3201828998) * 4294967296 + 547346461) * 4294967296 + 3441467384) * 4294967296 + 365764795) * 4294967296 + 4165324064) * 4294967296 + 3203929289) * 4294967296 + 547354740) * 4294967296 + 3307249608) * 4294967296 + 1959076094) * 4294967296 + 1997833504) * 4294967296 + 3153609921) * 4294967296 + 549378072) * 4294967296 + 2166398936) * 4294967296 + 2026049723) * 4294967296 + 4165255952) * 4294967296 + 2681744846) * 4294967296 + 278911005) * 4294967296 + 3457195992) * 4294967296 + 768413855) * 4294967296 + 4163226896) * 4294967296 + 3153610189) * 4294967296 + 280950821) * 4294967296 + 3440434936) * 4294967296 + 1036587230) * 4294967296 + 3627927824) * 4294967296 + 3740802505) * 4294967296 + 283039773) * 4294967296 + 3373326040) * 4294967296 + 231280862) * 4294967296 + 4148021520) * 4294967296 + 3738648009) * 4294967296 + 285112349) * 4294967296 + 3373326200) * 4294967296 + 365498590) * 4294967296 + 4146448656) * 4294967296 + 3202904521) * 4294967296 + 283047729) * 4294967296 + 3373326039) * 4294967296 + 835260638) * 4294967296 + 4146383120) * 4294967296 + 4269222085) * 4294967296 + 280983588) * 4294967296 + 3306225271) * 4294967296 + 616894718) * 4294967296 + 1193592080) * 4294967296 + 3740738757) * 4294967296 + 280999940) * 4294967296 + 3306209160) * 4294967296 + 80023743) * 4294967296 + 1752728848) * 4294967296 + 4269222021) * 4294967296 + 285102888) * 4294967296 + 2232483447) * 4294967296 + 612700319) * 4294967296 + 3900227856) * 4294967296 + 3740739777) * 4294967296 + 280754244) * 4294967296 + 3239108343) * 4294967296 + 616632574) * 4294967296 + 3072885008) * 4294967296 + 3740739713) * 4294967296 + 285106712) * 4294967296 + 2165374647) * 4294967296 + 612438270) * 4294967296 + 2468643088) * 4294967296 + 4281865345) * 4294967296 + 285152020) * 4294967296 + 2165366519) * 4294967296 + 612438207) * 4294967296 + 2014609680) * 4294967296 + 4266792065) * 4294967296 + 285123076) * 4294967296 + 2165358424) * 4294967296 + 675352830) * 4294967296 + 1999126800) * 4294967296 + 4266076225) * 4294967296 + 285151752) * 4294967296 + 1091624695) * 4294967296 + 675352799) * 4294967296 + 2020884496) * 4294967296 + 4269286464) * 4294967296 + 278648897) * 4294967296 + 3241320280) * 4294967296 + 297874075) * 4294967296 + 3628187953) * 4294967296 + 2664964545) * 4294967296 + 834566164) * 4294967296 + 3391201016) * 4294967296 + 633745597) * 4294967296 + 2282015024) * 4294967296 + 3179807941) * 4294967296 + 815528005) * 4294967296 + 3458260567) * 4294967296 + 411443390) * 4294967296 + 2550695456) * 4294967296 + 2616739277) * 4294967296 + 549357572) * 4294967296 + 3374357496) * 4294967296 + 1171132571) * 4294967296 + 4165324048) * 4294967296 + 2667062733) * 4294967296 + 278849649) * 4294967296 + 3373316952) * 4294967296 + 1220874494) * 4294967296 + 572031248) * 4294967296 + 4262597761) * 4294967296 + 278886516) * 4294967296 + 1074847063) * 4294967296 + 876613854) * 4294967296 + 1461993488) else ((((((((199559 * 4294967296 + 2150690880) * 4294967296 + 33819678) * 4294967296 + 4194820) * 4294967296 + 204488706) * 4294967296 + 67141696) * 4294967296 + 2164918032) * 4294967296 + 203423873) * 4294967296 + 3288599082))
def g191H7 (j : Nat) : Nat := ((((((((((((((((1 * 4294967296 + 1091969024) * 4294967296 + 1470464) * 4294967296 + 1762656710) * 4294967296 + 3221225539) * 4294967296 + 3900785376) * 4294967296 + 3221274696) * 4294967296 + 1368961556) * 4294967296 + 2021880048) * 4294967296 + 369342612) * 4294967296 + 134222421) * 4294967296 + 3430940955) * 4294967296 + 3314030996) * 4294967296 + 287467918) * 4294967296 + 3895132452) * 4294967296 + 4038789094) * 4294967296 + 3263277056)
def g191D8 (j : Nat) : Nat := ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((2204180 * 4294967296 + 413689987) * 4294967296 + 2256863393) * 4294967296 + 71517224) * 4294967296 + 1095815328) * 4294967296 + 1142972752) * 4294967296 + 3507360292) * 4294967296 + 875041043) * 4294967296 + 339495016) * 4294967296 + 2307527744) * 4294967296 + 3359744798) * 4294967296 + 288498322) * 4294967296 + 1111896268) * 4294967296 + 58924042) * 4294967296 + 836833606) * 4294967296 + 808749255) * 4294967296 + 2467372056) * 4294967296 + 50612366) * 4294967296 + 201450694) * 4294967296 + 1144005059) * 4294967296 + 38157346) * 4294967296 + 1653744198) * 4294967296 + 683739267) * 4294967296 + 470426147) * 4294967296 + 3280307968) * 4294967296 + 2701706823) * 4294967296 + 140536081) * 4294967296 + 3256765521) * 4294967296 + 2206342156) * 4294967296 + 741868552) * 4294967296 + 810716210) * 4294967296 + 1930501710) * 4294967296 + 482592906) * 4294967296 + 474355794) * 4294967296 + 1930174030) * 4294967296 + 1640170643) * 4294967296 + 2557502407) * 4294967296 + 1720852636) * 4294967296 + 3284600843) * 4294967296 + 211600325) * 4294967296 + 236983836) * 4294967296 + 3527806855) * 4294967296 + 848421393) * 4294967296 + 93932673) * 4294967296 + 1166673932) * 4294967296 + 1143784200) * 4294967296 + 371728433) * 4294967296 + 429985444) * 4294967296 + 1986126433) * 4294967296 + 404821609) * 4294967296 + 587776520) * 4294967296 + 1718166276) * 4294967296 + 2273783970) * 4294967296 + 1661518475) * 4294967296 + 825323750) * 4294967296 + 310933666) * 4294967296 + 2170670156) * 4294967296 + 1545745161) * 4294967296 + 506338306) * 4294967296 + 2223514380) * 4294967296 + 624526860) * 4294967296 + 303439042) * 4294967296 + 2307657753) * 4294967296 + 33130252) * 4294967296 + 187859140) * 4294967296 + 1628805448) * 4294967296 + 2720096595) * 4294967296 + 2558050480) * 4294967296 + 3368854648) * 4294967296 + 3267691526) * 4294967296 + 993051655) * 4294967296 + 3860603148) * 4294967296 + 839378436) * 4294967296 + 820822676) * 4294967296 + 2308524257) * 4294967296 + 3791831719) * 4294967296 + 817971809) * 4294967296 + 3425212578) * 4294967296 + 3305375291) * 4294967296 + 818004483) * 4294967296 + 541012193) * 4294967296 + 2181242943) * 4294967296 + 820086374) * 4294967296 + 471400953) * 4294967296 + 2265465648) * 4294967296 + 3789685443) * 4294967296 + 2571673929) * 4294967296 + 3775178544) * 4294967296 + 4052060873) * 4294967296 + 2402345392) * 4294967296 + 3838216774) * 4294967296 + 1636141576) * 4294967296 + 209084850) * 4294967296 + 1674328132) * 4294967296 + 2039057936) * 4294967296 + 1181033412) * 4294967296 + 541012513) * 4294967296 + 42999704) * 4294967296 + 1887700966) * 4294967296 + 472277441) * 4294967296 + 269588600) * 4294967296 + 2209556766) * 4294967296 + 548487425) * 4294967296 + 2395746418) * 4294967296 + 62066448) * 4294967296 + 2217859460) * 4294967296 + 3259521276) * 4294967296 + 1358106251) * 4294967296 + 210581893) * 4294967296 + 541019649) * 4294967296 + 54924431) * 4294967296 + 553769350) * 4294967296 + 541019745) * 4294967296 + 3270518516) * 4294967296 + 3997094635) * 4294967296 + 2930370790) * 4294967296 + 2045167202) * 4294967296 + 1688616163) * 4294967296 + 1714184686) * 4294967296 + 232771044) * 4294967296 + 3719155932) * 4294967296 + 1840405069) * 4294967296 + 2656636280) * 4294967296 + 3602208468) * 4294967296 + 3443938133) * 4294967296 + 433083625) * 4294967296 + 3448556363) * 4294967296 + 2762557772) * 4294967296 + 2034664531) * 4294967296 + 3276544320) * 4294967296 + 2213559683) * 4294967296 + 3225074583) * 4294967296 + 942370357) * 4294967296 + 3544527571) * 4294967296 + 355498739) * 4294967296 + 766690090) * 4294967296 + 2996447266) * 4294967296 + 1898316363) * 4294967296 + 2742164384) * 4294967296 + 971742689) * 4294967296 + 3441148327) * 4294967296 + 2566485909) * 4294967296 + 4182217577) * 4294967296 + 630278400) * 4294967296 + 250666509) * 4294967296 + 1086524192) * 4294967296 + 2525517940) * 4294967296 + 2240824450) * 4294967296 + 3356786695) * 4294967296 + 4285680767) * 4294967296 + 3952370175) * 4294967296 + 2623737850) * 4294967296 + 3810033634) * 4294967296 + 415497872) * 4294967296 + 3323984005) * 4294967296 + 822060073) * 4294967296 + 2281533832) * 4294967296 + 1073453633) * 4294967296 + 4284273167) * 4294967296 + 4276260991) * 4294967296 + 3608445950) * 4294967296 + 2560892920) * 4294967296 + 3240165286) * 4294967296 + 151518768) * 4294967296 + 3292522886) * 4294967296 + 570383521) * 4294967296 + 268058888) * 4294967296 + 2146907203) * 4294967296 + 4273578527) * 4294967296 + 4257812735) * 4294967296 + 2923988989) * 4294967296 + 843333609) * 4294967296 + 2317483916) * 4294967296 + 286259808) * 4294967296 + 2290082308) * 4294967296 + 1140756514) * 4294967296 + 536363280) * 4294967296 + 3220056469) * 4294967296 + 4285549743) * 4294967296 + 3816973695) * 4294967296 + 2619546618) * 4294967296 + 3776503799) * 4294967296 + 617082521) * 4294967296 + 641203649) * 4294967296 + 834637321) * 4294967296 + 2382197640) * 4294967296 + 2137625667) * 4294967296 + 2140938779) * 4294967296 + 4209053919) * 4294967296 + 3610543870) * 4294967296 + 3108378613) * 4294967296 + 3325097966) * 4294967296 + 2307260274) * 4294967296 + 1279191442) * 4294967296 + 1635769427) * 4294967296 + 263873176) * 4294967296 + 2112029890) * 4294967296 + 4290364439) * 4294967296 + 4123926719) * 4294967296 + 2922448878) * 4294967296 + 562573307) * 4294967296 + 2587983708) * 4294967296 + 3524254308) * 4294967296 + 2422208276) * 4294967296 + 2213974180) * 4294967296 + 532185376) * 4294967296 + 3215882375) * 4294967296 + 4113679407) * 4294967296 + 4221313407) * 4294967296 + 1558252542) * 4294967296 + 3842531287) * 4294967296 + 675479224) * 4294967296 + 3256871042) * 4294967296 + 285156368) * 4294967296 + 2281115780) * 4294967296 + 805018145) * 4294967296 + 2136789259) * 4294967296 + 4276390014) * 4294967296 + 4146348798) * 4294967296 + 3106021297) * 4294967296 + 3373334214) * 4294967296 + 679998769) * 4294967296 + 1145024778) * 4294967296 + 570247249) * 4294967296 + 267665544) * 4294967296 + 2140275779) * 4294967296 + 4211614231) * 4294967296 + 4123791551) * 4294967296 + 3456141301) * 4294967296 + 268709355) * 4294967296 + 2757980125) * 4294967296 + 319545060) * 4294967296 + 2287458128) * 4294967296 + 1122941314) * 4294967296 + 397789200)
def g191H8 (j : Nat) : Nat := (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((85056 * 4294967296 + 31211840) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 283901952) * 4294967296 + 38403440) * 4294967296 + 0) * 4294967296 + 147904) * 4294967296 + 0) * 4294967296 + 474) * 4294967296 + 3221225472) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 128640) * 4294967296 + 0) * 4294967296 + 582656) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 709) * 4294967296 + 225759168) * 4294967296 + 3352) * 4294967296 + 2741642) * 4294967296 + 2245787648) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 201339) * 4294967296 + 1677721602) * 4294967296 + 3355443200) * 4294967296 + 363999552) * 4294967296 + 15583668) * 4294967296 + 782) * 4294967296 + 2173435904) * 4294967296 + 0) * 4294967296 + 3692544) * 4294967296 + 951582769) * 4294967296 + 2822914048) * 4294967296 + 3473408) * 4294967296 + 83008) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 115392) * 4294967296 + 0) * 4294967296 + 2164736) * 4294967296 + 104576) * 4294967296 + 0) * 4294967296 + 3264512) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 643) * 4294967296 + 3221225472) * 4294967296 + 0) * 4294967296 + 268) * 4294967296 + 3221225472) * 4294967296 + 0) * 4294967296 + 884736) * 4294967296 + 45613060) * 4294967296 + 201326592) * 4294967296 + 2442753) * 4294967296 + 688652288) * 4294967296 + 51930184) * 4294967296 + 541065216) * 4294967296 + 0) * 4294967296 + 43827200) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 4980736) * 4294967296 + 0) * 4294967296 + 830210048) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 52992) * 4294967296 + 11452) * 4294967296 + 1573888) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 648) * 4294967296 + 2147552565) * 4294967296 + 3355443201) * 4294967296 + 3372589056) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 2004) * 4294967296 + 3556769792) * 4294967296 + 146) * 4294967296 + 479723520) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 47153152) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 857) * 4294967296 + 1760821248) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 134742016) * 4294967296 + 0) * 4294967296 + 4179968) * 4294967296 + 647086848) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 3) * 4294967296 + 54526363) * 4294967296 + 3221225472) * 4294967296 + 3) * 4294967296 + 100663296) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 2688924) * 4294967296 + 16) * 4294967296 + 2483027968) * 4294967296 + 0) * 4294967296 + 827588608) * 4294967296 + 14556) * 4294967296 + 0) * 4294967296 + 5696) * 4294967296 + 2) * 4294967296 + 2192401177) * 4294967296 + 0) * 4294967296 + 3136) * 4294967296 + 1835415) * 4294967296 + 2771648537) * 4294967296 + 1543503874) * 4294967296 + 1212184576) * 4294967296 + 0) * 4294967296 + 5554176) * 4294967296 + 0) * 4294967296 + 697827368) * 4294967296 + 2952804447) * 4294967296 + 1568670610) * 4294967296 + 3221225477) * 4294967296 + 671088640) * 4294967296 + 0) * 4294967296 + 182464) * 4294967296 + 5300) * 4294967296 + 0) * 4294967296 + 29) * 4294967296 + 1811939328) * 4294967296 + 0) * 4294967296 + 38) * 4294967296 + 3433971713) * 4294967296 + 2579496960) * 4294967296 + 758906880) * 4294967296 + 1248) * 4294967296 + 0) * 4294967296 + 16) * 4294967296 + 1409289980) * 4294967296 + 586) * 4294967296 + 1073741824) * 4294967296 + 3748) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 38158337) * 4294967296 + 780140544) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 3154180) * 4294967296 + 3607101440) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 62) * 4294967296 + 2281701378) * 4294967296 + 3510632686) * 4294967296 + 651253125) * 4294967296 + 1207959552) * 4294967296 + 3938451456) * 4294967296 + 136879) * 4294967296 + 294764546) * 4294967296 + 3685405696) * 4294967296 + 1024458784) * 4294967296 + 2912223232) * 4294967296 + 1128448) * 4294967296 + 0) * 4294967296 + 3) * 4294967296 + 3330277376) * 4294967296 + 751304740) * 4294967296 + 1828809752) * 4294967296 + 1352195) * 4294967296 + 2423521280) * 4294967296 + 0) * 4294967296 + 647) * 4294967296 + 0) * 4294967296 + 0) * 4294967296 + 467) * 4294967296 + 430230912) * 4294967296 + 1487175812) * 4294967296 + 2295021568)
def g191D9 (j : Nat) : Nat := (((((((((((((((((((((((((((140 * 4294967296 + 555644100) * 4294967296 + 2382967580) * 4294967296 + 606575921) * 4294967296 + 579029075) * 4294967296 + 271078604) * 4294967296 + 1888522340) * 4294967296 + 1393701924) * 4294967296 + 645681938) * 4294967296 + 1009261693) * 4294967296 + 558644263) * 4294967296 + 1377092227) * 4294967296 + 1288112394) * 4294967296 + 131232963) * 4294967296 + 84748108) * 4294967296 + 704775696) * 4294967296 + 668152260) * 4294967296 + 4139227531) * 4294967296 + 2774161660) * 4294967296 + 1714032966) * 4294967296 + 31458301) * 4294967296 + 855608447) * 4294967296 + 3542087815) * 4294967296 + 4246863756) * 4294967296 + 1070796792) * 4294967296 + 2214404351) * 4294967296 + 3292520719) * 4294967296 + 4098096144)
def g191H9 (j : Nat) : Nat := (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((14 * 4294967296 + 721420288) * 4294967296 + 631664) * 4294967296 + 4178621543) * 4294967296 + 930400669) * 4294967296 + 2469396689) * 4294967296 + 4026540320) * 4294967296 + 0) * 4294967296 + 727040) * 4294967296 + 169476096) * 4294967296 + 0) * 4294967296 + 18) * 4294967296 + 1562198320) * 4294967296 + 11312426) * 4294967296 + 1087724077) * 4294967296 + 2049996933) * 4294967296 + 129111630) * 4294967296 + 588251264) * 4294967296 + 1610672992) * 4294967296 + 5398528) * 4294967296 + 146) * 4294967296 + 3503668640) * 4294967296 + 0) * 4294967296 + 1023200768) * 4294967296 + 62752) * 4294967296 + 4486325) * 4294967296 + 0) * 4294967296 + 36120) * 4294967296 + 470452373) * 4294967296 + 1222716578) * 4294967296 + 1220743168) * 4294967296 + 0) * 4294967296 + 80128) * 4294967296 + 231039411) * 4294967296 + 1459618646) * 4294967296 + 403555) * 4294967296 + 2233663490) * 4294967296 + 335544923) * 4294967296 + 954331) * 4294967296 + 743769278) * 4294967296 + 197172503) * 4294967296 + 3759227619) * 4294967296 + 1073783408) * 4294967296 + 811008) * 4294967296 + 972946) * 4294967296 + 2517980170) * 4294967296 + 1569199176) * 4294967296 + 282546) * 4294967296 + 4291624971) * 4294967296 + 2650802201) * 4294967296 + 2688548864) * 4294967296 + 37937) * 4294967296 + 785523262) * 4294967296 + 808452096) * 4294967296 + 38345152) * 4294967296 + 15987003) * 4294967296 + 55574613) * 4294967296 + 1218740455) * 4294967296 + 842030161) * 4294967296 + 2359889061) * 4294967296 + 2415919104) * 4294967296 + 9675542) * 4294967296 + 163) * 4294967296 + 3466526721) * 4294967296 + 1157627904) * 4294967296 + 3107979277) * 4294967296 + 2415919104) * 4294967296 + 0) * 4294967296 + 1547698176) * 4294967296 + 27295) * 4294967296 + 1476396618) * 4294967296 + 741376) * 4294967296 + 5046272) * 4294967296 + 2483877) * 4294967296 + 3223340117) * 4294967296 + 3275816971) * 4294967296 + 536912392) * 4294967296 + 600952877) * 4294967296 + 1073803749) * 4294967296 + 292894006) * 4294967296 + 5392136) * 4294967296 + 697306211) * 4294967296 + 3238264835) * 4294967296 + 202474028) * 4294967296 + 805375120) * 4294967296 + 2149859332)
def g191D10 (j : Nat) : Nat := 0x1124c27f
def g191H10 (j : Nat) : Nat := ((((((((805335 * 4294967296 + 79708707) * 4294967296 + 4077830144) * 4294967296 + 68507132) * 4294967296 + 3045078752) * 4294967296 + 370422) * 4294967296 + 4288) * 4294967296 + 1312) * 4294967296 + 2348811970)
def g191L : Nat → Packing
  | 5 => (1,5,5,0,0,0,0,g191D5)
  | 6 => (33,4,5,0,0,9,0,g191D6)
  | 7 => (120,3,5,0,0,12,0,g191D7)
  | 8 => (95,2,5,0,0,12,0,g191D8)
  | 9 => (13,1,5,0,0,9,0,g191D9)
  | 10 => (1,0,5,0,0,0,0,g191D10)
  | _ => emptyPacking
def g191I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g191H6
  | 7 => lookupWord 8 43 5 11 6 1 g191H7
  | 8 => lookupWord 35 521 2 12 7 1 g191H8
  | 9 => lookupWord 32 211 6 12 7 1 g191H9
  | 10 => lookupWord 4 29 4 9 4 1 g191H10
  | _ => fun _ => none
def g191 : Forest := ⟨191,10,fun i => g191Y[i]?.getD (0,0),g191C,g191A,g191L,g191I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P5_0 : block g191 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B5 : block g191 5 0 1=true := g191P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P6_0 : block g191 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P6_3 : block g191 6 3 30=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B6 : block g191 6 0 33=true := (@block_merge g191 6 0 3 30 g191P6_0 g191P6_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P7_0 : block g191 7 0 23=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P7_23 : block g191 7 23 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P7_119 : block g191 7 119 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B7 : block g191 7 0 120=true := (@block_merge g191 7 0 23 97 g191P7_0 (@block_merge g191 7 23 96 1 g191P7_23 g191P7_119))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P8_0 : block g191 8 0 6=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P8_6 : block g191 8 6 58=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P8_64 : block g191 8 64 31=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B8 : block g191 8 0 95=true := (@block_merge g191 8 0 6 89 g191P8_0 (@block_merge g191 8 6 58 31 g191P8_6 g191P8_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P9_0 : block g191 9 0 13=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B9 : block g191 9 0 13=true := g191P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P10_0 : block g191 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B10 : block g191 10 0 1=true := g191P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191T : checkedTables g191 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g191 0 0 0 = true)
  · exact (rfl : block g191 1 0 0 = true)
  · exact (rfl : block g191 2 0 0 = true)
  · exact (rfl : block g191 3 0 0 = true)
  · exact (rfl : block g191 4 0 0 = true)
  · exact g191B5
  · exact g191B6
  · exact g191B7
  · exact g191B8
  · exact g191B9
  · exact g191B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191G : graphValid g191 (boundsBefore K127) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low191 : Lower true (varsX 191) (graphGoal 191) 11 := lower_forest (g:=g191) (i:=0) (hints:=1343225857) (before_sound K127 V127) g191G g191T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
end ForestCore

open ForestCore

def graph (x : Fin 8 → Bool) : Bool := (x 0 && x 4) || (x 1 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 3 && x 6) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 5 && x 7)

def coding : Fin 8 → Nat := ![6, 1, 3, 7, 2, 4, 5, 0]

def roots : List Sig := List.ofFn (fun i : Fin 8 => inputs.getD (coding i) zero)

def codedGraph : Sig := (((((((((((((((4294967295 * 4294967296 + 4294966008) * 4294967296 + 4294967295) * 4294967296 + 4293585640) * 4294967296 + 4294967295) * 4294967296 + 4294966008) * 4294967296 + 4293848812) * 4294967296 + 4293585640) * 4294967296 + 4294967295) * 4294967296 + 4294966008) * 4294967296 + 4294967295) * 4294967296 + 4293585640) * 4294967296 + 4294967295) * 4294967296 + 4294966008) * 4294967296 + 4293848812) * 4294967296 + 4293585640)

def pins : Finset Sig := {inputs.getD 6 zero}

def pinRow (r : Row) : Row := Fin.ofNat 512 (r.val &&& 191)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem wholeBound : Lower true roots codedGraph 12 := by
  have card : 11 + pins.card = 12 := by decide +kernel
  rw [← card]
  refine lower_slice (T := codedGraph) (G := graphGoal 191) (roots := roots)
    (other := varsX 191) (singles := pins) (by unfold proper; decide +kernel) (by decide +kernel)
    (by decide +kernel) (by unfold proper; decide +kernel) pinRow (by decide +kernel) ?_ ?_ ?_ 11 low191

  · intro a ha
    change a ∈ [inputs.getD 6 zero, inputs.getD 1 zero, inputs.getD 3 zero, inputs.getD 7 zero, inputs.getD 2 zero, inputs.getD 4 zero, inputs.getD 5 zero, inputs.getD 0 zero] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have he : rename pinRow (inputs.getD 6 zero) = zero := by decide +kernel
      rw [he]
      exact Or.inr (Or.inl ⟨false, funext bit_zero⟩)
    · have he : rename pinRow (inputs.getD 1 zero) = (inputs.getD 1 zero) := by decide +kernel
      rw [he]
      exact Or.inl (List.mem_map_of_mem (by decide +kernel : (inputs.getD 1 zero) ∈ varsX 191))
    · have he : rename pinRow (inputs.getD 3 zero) = (inputs.getD 3 zero) := by decide +kernel
      rw [he]
      exact Or.inl (List.mem_map_of_mem (by decide +kernel : (inputs.getD 3 zero) ∈ varsX 191))
    · have he : rename pinRow (inputs.getD 7 zero) = (inputs.getD 7 zero) := by decide +kernel
      rw [he]
      exact Or.inl (List.mem_map_of_mem (by decide +kernel : (inputs.getD 7 zero) ∈ varsX 191))
    · have he : rename pinRow (inputs.getD 2 zero) = (inputs.getD 2 zero) := by decide +kernel
      rw [he]
      exact Or.inl (List.mem_map_of_mem (by decide +kernel : (inputs.getD 2 zero) ∈ varsX 191))
    · have he : rename pinRow (inputs.getD 4 zero) = (inputs.getD 4 zero) := by decide +kernel
      rw [he]
      exact Or.inl (List.mem_map_of_mem (by decide +kernel : (inputs.getD 4 zero) ∈ varsX 191))
    · have he : rename pinRow (inputs.getD 5 zero) = (inputs.getD 5 zero) := by decide +kernel
      rw [he]
      exact Or.inl (List.mem_map_of_mem (by decide +kernel : (inputs.getD 5 zero) ∈ varsX 191))
    · have he : rename pinRow (inputs.getD 0 zero) = (inputs.getD 0 zero) := by decide +kernel
      rw [he]
      exact Or.inl (List.mem_map_of_mem (by decide +kernel : (inputs.getD 0 zero) ∈ varsX 191))
  · intro a ha
    simp only [pins, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl
    · refine ⟨4, 68, by decide +kernel, ?_⟩
      have h : ∀ j : Fin 8, inputs.getD (coding j) zero ≠ inputs.getD 6 zero →
          bit 4 (inputs.getD (coding j) zero) = bit 68 (inputs.getD (coding j) zero) := by decide +kernel
      intro v hv hn
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hv
      exact h j hn
  · intro a ha
    simp only [pins, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl
    · have he : rename pinRow (inputs.getD 6 zero) = zero := by decide +kernel
      rw [he]
      exact ⟨false, funext bit_zero⟩

def sampleInput (r : Row) (i : Fin 8) : Bool := bit r (inputs.getD (coding i) zero)

theorem sampledInput (r : Row) : List.ofFn (sampleInput r) = roots.map (bit r) := by
  rw [roots, List.map_ofFn]
  rfl

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem sampleCorrect : ∀ r : Row, bit r codedGraph = graph (sampleInput r) := by decide +kernel

def signedNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false

theorem binaryLower (C : Circuit) (fit : FanInTwo C)
    (comp : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = graph x) :
    12 ≤ C.gates.countP (fun g => !signedNot g) := by
  have goalEq : (execute C.gates roots).getD C.output zero = codedGraph := by
    apply bit_ext
    intro r
    rw [← b_read, execute_bits _ _ _ (fun g hg => (fit g hg).1), ← sampledInput]
    exact (comp (sampleInput r)).trans (sampleCorrect r).symm
  have out := get_rep (u := true) (execute C.gates roots) C.output
  rw [goalEq] at out
  unfold ForestCore.Repr at out
  have pg : bit 0 codedGraph = false := by decide +kernel
  rw [nrm_id pg] at out
  have properGoal : proper codedGraph := by unfold proper; decide +kernel
  obtain ⟨k, S, hk, run, sub⟩ := extract (u := true) C.gates roots fit (by simp) properGoal
    (out.resolve_right (fun h => h properGoal))
  change k ≤ C.gates.countP (fun g => !signedNot g) at hk
  rw [nrm_map (by decide +kernel : roots.all plainWord = true)] at sub
  have step := list_run run S.toList (Finset.nodup_toList _) (by simp)
  have ready : supply true (roots.map observe) (S.toList.map observe) := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
    exact Or.inl (List.mem_map_of_mem (sub a (Finset.mem_toList.mp ha)))
  obtain ⟨q, bank, reach, hit, paid⟩ := contraction (observe_proper properGoal) step _ Reach.start ready
  have lower := wholeBound q bank reach hit
  omega

def witness : List Gate := [⟨.or, [4, 5]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [1, 9]⟩, ⟨.and, [7, 10]⟩, ⟨.or, [0, 2]⟩, ⟨.and, [5, 12]⟩, ⟨.and, [3, 6]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [15, 16]⟩, ⟨.or, [14, 17]⟩, ⟨.or, [13, 18]⟩, ⟨.or, [11, 19]⟩]

theorem witnessBasis : ∀ g ∈ witness,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 8 → Bool,
    Circuit.eval ⟨witness, 20⟩ (List.ofFn x) = graph x := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem graph_correct : ∀ x : Fin 8 → Bool, graph x = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  decide +kernel

end PEqualNP.Outside.L_meta_14274

open PEqualNP.Outside.L_meta_14274 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_14274 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gates o legal _oneNot computes
  by_cases hnot : ∃ g ∈ gates, g.op = GateOp.not
  · have fit : FanInTwo ⟨gates, o⟩ := by
      intro g hg
      exact (legal g hg)
    have paid := binaryLower ⟨gates, o⟩ fit (fun x => (computes x).trans (graph_correct x).symm)
    change 12 ≤ gates.countP (fun g => !signedNot g) at paid
    obtain ⟨g, hg, hop⟩ := hnot
    have extra : gates.countP (fun t => !signedNot t) < gates.length := by
      by_contra! large
      have allNot := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length large) g hg
      simp [signedNot, hop] at allNot
    have hw : witness.length = 13 := rfl
    exact ⟨witness, 20, witnessBasis, by omega, fun x => (witnessCorrect x).trans (graph_correct x)⟩
  · refine ⟨gates, o, ?_, le_rfl, computes⟩
    intro g hg
    obtain ⟨ops, hlen⟩ := legal g hg
    exact ⟨ops.imp_right (fun h => h.resolve_right (fun hn => hnot ⟨g, hg, hn⟩)), hlen⟩
