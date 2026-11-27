import PEqualNP.Defs

-- The free-inversion live-state and cofactor argument is adapted from L_meta_8449, which credits L_meta_1674, L_meta_670 and L_meta_1667 (Apache-2.0).

namespace PEqualNP.Outside.L_meta_12126

def packWords (xs : List Nat) := xs.foldl (fun a b => a * 2^56 + b) 0

namespace Core
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
lemma get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
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

lemma extract {u target} (gs : List Gate) (w : List Sig)
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

lemma b_read (i) (w : List Sig) (j : Nat) :
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

lemma execute_bits (gs : List Gate) (i) (w : List Sig)
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

def inputs : List Sig := [(BitVec.ofNat 512 (packWords [0xaa,0xaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaa])),(BitVec.ofNat 512 (packWords [0xcc,0xcccccccccccccc,0xcccccccccccccc,0xcccccccccccccc,0xcccccccccccccc,0xcccccccccccccc,0xcccccccccccccc,0xcccccccccccccc,0xcccccccccccccc,0xcccccccccccccc])),(BitVec.ofNat 512 (packWords [0xf0,0xf0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0])),(BitVec.ofNat 512 (packWords [0xff,0xff00ff00ff00,0xff00ff00ff00ff,0xff00ff00ff00,0xff00ff00ff00ff,0xff00ff00ff00,0xff00ff00ff00ff,0xff00ff00ff00,0xff00ff00ff00ff,0xff00ff00ff00])),(BitVec.ofNat 512 (packWords [0xff,0xff0000ffff0000,0xffff0000ffff00,0xffff0000ffff,0xffff0000ff,0xff0000ffff0000,0xffff0000ffff00,0xffff0000ffff,0xffff0000ff,0xff0000ffff0000])),(BitVec.ofNat 512 (packWords [0xff,0xffffff00000000,0xffffffff000000,0xffffffff0000,0xffffffff00,0xffffffff,0xffffff,0xff00000000ffff,0xffff00000000ff,0xffffff00000000])),(BitVec.ofNat 512 (packWords [0xff,0xffffffffffffff,0x0,0xffffffffffff,0xffff0000000000,0xffffffff,0xffffffff000000,0xffff,0xffffffffffff00,0x0])),(BitVec.ofNat 512 (packWords [0xff,0xffffffffffffff,0xffffffffffffff,0xff000000000000,0x0,0xffffffff,0xffffffffffffff,0xffffffffff0000,0x0,0x0])),(BitVec.ofNat 512 (packWords [0xff,0xffffffffffffff,0xffffffffffffff,0xffffffffffffff,0xffffffffffffff,0xffffff00000000,0x0,0x0,0x0,0x0]))]
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

def Lower (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (observe T) → L ≤ p
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

end Core

namespace Model12127
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def target (x : Fin 6 → Bool) := Nat.testBit (4276676736 * 2 ^ 32 + 4269834240)
  (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0)

end Model12127

namespace Thirteen12127
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Model12127
def circuit : Circuit := ⟨[⟨.and,[0,1]⟩, ⟨.or,[0,1]⟩, ⟨.and,[3,4]⟩, ⟨.or,[3,4]⟩, ⟨.and,[5,6]⟩, ⟨.or,[5,6]⟩, ⟨.and,[2,11]⟩, ⟨.and,[7,9]⟩, ⟨.or,[2,13]⟩, ⟨.or,[8,10]⟩, ⟨.and,[15,14]⟩, ⟨.and,[13,12]⟩, ⟨.or,[17,16]⟩],18⟩

theorem legal : Monotone2 circuit := by
  intro g hg
  simp only [circuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem upper : ∃ C : Circuit, Monotone2 C ∧ C.size=13 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  refine ⟨circuit,legal,rfl,?_⟩
  decide +kernel

end Thirteen12127

namespace FirstGate12127
open PEqualNP.Outside.L_meta_12126.Core

def lost (T : Sig) (ws : List Sig) (rs : Row × Row) : Bool :=
  (bit rs.1 T != bit rs.2 T) && ws.all (fun a => bit rs.1 a == bit rs.2 a)

theorem lost_sound {T ws rs u cap} (h : lost T ws rs = true) :
    Impossible u T cap ws.toFinset := by
  simp only [lost,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,beq_iff_eq] at h
  intro _ _ live
  obtain ⟨a,ha,hd⟩ := live_row_difference live h.1
  exact hd (h.2 a (List.mem_toFinset.mp ha))

def cuts (u : Bool) (T : Sig) (raw ws : List Sig) (cap : Nat)
    (slices : List (Sig × Nat)) (pairs : List (Row × Row)) :=
  pairs.any (lost T ws) || slices.any (fun p => poolCut u p.1 p.2 cap 0 raw ws)

theorem cuts_sound {u T raw ws cap slices pairs} (nd : ws.Nodup)
    (prior : ∀ p ∈ slices, Slice u raw T p.1 p.2)
    (h : cuts u T raw ws cap slices pairs = true) : Impossible u T cap ws.toFinset := by
  simp only [cuts,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨rs,_,hh⟩ | ⟨p,hp,hh⟩
  · exact lost_sound hh
  · exact poolCut_sound (prior _ hp) [] rfl nd hh

def firstCheck (u : Bool) (T : Sig) (raw : List Sig) (cap : Nat)
    (mins : List (Sig × Nat)) (pairs : List (Row × Row)) :=
  raw.all fun a => raw.all fun b => [0,1,2,3].all fun d =>
    [false,true].all fun ka => [false,true].all fun kb =>
      let z := bin d a b
      let child := childTwo raw a b d ka kb
      a == b || !allowedB u d || raw.contains z || decide (child.length > cap) ||
      cuts u T raw child (cap-1) mins pairs

theorem first_sound {u T raw cap mins pairs} (hd : raw.Nodup) (out : T ∉ raw)
    (prior : ∀ p ∈ mins, Slice u raw T p.1 p.2)
    (ok : firstCheck u T raw cap mins pairs = true) : Impossible u T cap raw.toFinset := by
  apply enum_step hd out
  intro a ha b hb d hOp ka kb hab fresh _ len
  have opmem : d ∈ [0,1,2,3] := by
    rcases allowed_four hOp with h | h | ⟨_,h⟩ | ⟨_,h⟩ <;> simp [h]
  have ab : allowedB u d = true := by
    obtain h | ⟨hu,h⟩ := hOp
    · simp [allowedB,h]
    · simp [allowedB,hu,h]
  have ok' := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp
    (List.all_eq_true.mp (List.all_eq_true.mp ok _ ha) _ hb) _ opmem) ka (by cases ka <;> simp)) kb (by cases kb <;> simp)
  simp only [beq_eq_false_iff_ne.mpr hab,ab,Bool.not_true, Bool.false_or,
    List.contains_eq_mem, decide_eq_false fresh, decide_eq_false (Nat.not_lt.mpr len)] at ok'
  apply cuts_sound _ prior ok'
  have er : ((raw.erase a).erase b).Nodup := (hd.erase _).erase _
  have ar : a ∉ (raw.erase a).erase b := fun hm => hd.not_mem_erase (List.mem_of_mem_erase hm)
  have br : b ∉ (raw.erase a).erase b := (hd.erase a).not_mem_erase
  have knd := kept_nd kb b _ er br
  have ax : a ∉ kept kb b ((raw.erase a).erase b) := by cases kb <;> simp [kept,ar,hab]
  refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ knd ax⟩
  intro hz
  rcases mem_kept hz with he | hz
  · exact fresh (he.symm ▸ ha)
  rcases mem_kept hz with he | hz
  · exact fresh (he.symm ▸ hb)
  · exact fresh (List.mem_of_mem_erase (List.mem_of_mem_erase hz))
end FirstGate12127

namespace Bound12127
open PEqualNP.Outside.L_meta_12126.Core FirstGate12127
def raw (i : Nat) := inputs.getD i zero
def in6 := inputs.take 6
def in5 := inputs.take 5
def six : Sig := (BitVec.ofNat 512 (packWords [0xfe,0xe8e880fe808000,0xfee8e880fe8080,0xfee8e880fe80,0x8000fee8e880fe,0x808000fee8e880,0xfe808000fee8e8,0x80fe808000fee8,0xe880fe808000fe,0xe8e880fe808000]))
def light : Sig := (BitVec.ofNat 512 (packWords [0xfe,0xe8f880fee8f880,0xfee8f880fee8f8,0x80fee8f880fee8,0xf880fee8f880fe,0xe8f880fee8f880,0xfee8f880fee8f8,0x80fee8f880fee8,0xf880fee8f880fe,0xe8f880fee8f880]))
def heavy : Sig := (BitVec.ofNat 512 (packWords [0xe8,0x808000e8808000,0xe8808000e88080,0xe8808000e880,0x8000e8808000e8,0x808000e8808000,0xe8808000e88080,0xe8808000e880,0x8000e8808000e8,0x808000e8808000]))
def last : Sig := (BitVec.ofNat 512 (packWords [0xfe,0xe8e880fee8e880,0xfee8e880fee8e8,0x80fee8e880fee8,0xe880fee8e880fe,0xe8e880fee8e880,0xfee8e880fee8e8,0x80fee8e880fee8,0xe880fee8e880fe,0xe8e880fee8e880]))
def forceHigh (i : Nat) : Move := (~~~raw i,zero,Fin.ofNat 512 (2^i))
def forceLow (i : Nat) : Move := (zero,raw i,Fin.ofNat 512 (2^i))
def swapNext (i : Nat) : Move := (raw i &&& ~~~raw (i+1),raw (i+1) &&& ~~~raw i,Fin.ofNat 512 (2^i))
def m0 : List Move := [forceHigh 5, swapNext 4, swapNext 3, swapNext 2, swapNext 1, swapNext 0]
def d0 : Sig := raw 0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s0 (h : Lower true in5 light 10) : Slice true in6 six d0 10 :=
  slice_correct (ms := m0) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) h
def m1 : List Move := [forceHigh 5, swapNext 4, swapNext 3, swapNext 2, swapNext 1]
def d1 : Sig := raw 1
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s1 (h : Lower true in5 light 10) : Slice true in6 six d1 10 :=
  slice_correct (ms := m1) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) h
def m2 : List Move := [forceHigh 5, swapNext 4, swapNext 3, swapNext 2]
def d2 : Sig := raw 2
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s2 (h : Lower true in5 light 10) : Slice true in6 six d2 10 :=
  slice_correct (ms := m2) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) h
def m3 : List Move := [forceLow 5, swapNext 4, swapNext 3]
def d3 : Sig := ~~~raw 3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s3 (h : Lower true in5 heavy 10) : Slice true in6 six d3 10 :=
  slice_correct (ms := m3) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) h
def m4 : List Move := [forceLow 5, swapNext 4]
def d4 : Sig := ~~~raw 4
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s4 (h : Lower true in5 heavy 10) : Slice true in6 six d4 10 :=
  slice_correct (ms := m4) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) h
def m5 : List Move := [forceHigh 5]
def d5 : Sig := raw 5
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s5 (h : Lower true in5 last 10) : Slice true in6 six d5 10 :=
  slice_correct (ms := m5) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) h
def minors : List (Sig × Nat) := [(d0,10), (d1,10), (d2,10), (d3,10), (d4,10), (d5,10)]
def lostRows : List (Row × Row) := [(54, 52), (15, 14), (60, 56), (53, 52), (15, 11), (58, 50), (15, 13), (15, 7), (30, 14), (54, 38)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem six_lower (a : Lower true in5 light 10) (b : Lower true in5 heavy 10) (c : Lower true in5 last 10) : Impossible true six 11 in6.toFinset := by
  apply first_sound (mins := minors) (pairs := lostRows) (by decide +kernel) (by decide +kernel)
  · intro p hp
    simp only [minors,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact s0 a
    · exact s1 a
    · exact s2 a
    · exact s3 b
    · exact s4 b
    · exact s5 c
  · decide +kernel
end Bound12127

namespace Small12127
open PEqualNP.Outside.L_meta_12126.Core FirstGate12127
theorem child_nd {ws : List Sig} (hd : ws.Nodup) (a b : Sig) (d : Nat) (ka kb : Bool)
    (ha : a ∈ ws) (hb : b ∈ ws) (hab : a ≠ b) (fresh : bin d a b ∉ ws) :
    (childTwo ws a b d ka kb).Nodup := by
  have er : ((ws.erase a).erase b).Nodup := (hd.erase _).erase _
  have ar : a ∉ (ws.erase a).erase b := fun hm => hd.not_mem_erase (List.mem_of_mem_erase hm)
  have br : b ∉ (ws.erase a).erase b := (hd.erase a).not_mem_erase
  have knd := kept_nd kb b _ er br
  have ax : a ∉ kept kb b ((ws.erase a).erase b) := by cases kb <;> simp [kept,ar,hab]
  refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ knd ax⟩
  intro hz
  rcases mem_kept hz with he | hz
  · exact fresh (he.symm ▸ ha)
  rcases mem_kept hz with he | hz
  · exact fresh (he.symm ▸ hb)
  · exact fresh (List.mem_of_mem_erase (List.mem_of_mem_erase hz))

theorem child_flip {ws : List Sig} (nd : ws.Nodup) (a b : Sig) {u d} (hd : allowed u d) (ka kb : Bool) :
    (childTwo ws a b d ka kb).toFinset = (childTwo ws b a (flipOp d) kb ka).toFinset := by
  simp only [childTwo,List.toFinset_cons,kept_fin,erase_fin (nd.erase _),erase_fin nd]
  rw [bin_flip hd]
  cases ka <;> cases kb <;> simp [Finset.erase_right_comm,Finset.insert_comm]

end Small12127

namespace GateForest12127
open PEqualNP.Outside.L_meta_12126.Core FirstGate12127 Small12127 Bound12127

abbrev Spec := Nat × List (Nat × Nat × Nat)
def rawChoices : List Sig → List (Nat × Nat × Nat) → List Choice
  | _, [] => []
  | ws, (d,i,j)::cs =>
    let q : Choice := (d,ws.getD i zero,ws.getD j zero)
    q :: rawChoices (ws++[choiceVal q]) cs

def pcheck (T : Sig) (raw : List Sig) (mins : List (Sig × Nat)) (s : Spec) (ws : List Sig) (k : Nat) :=
  match mins[s.1]? with
  | none => false
  | some m =>
    let cs := rawChoices (raw.eraseIdx (s.1/2)) s.2
    match makePool true m.1 raw cs with
    | none => false
    | some pool => poolCut true m.1 m.2 k cs.length pool ws

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pcheck_sound {T raw mins s ws cap} (nd : ws.Nodup)
    (lo : ∀ p ∈ mins, Slice true raw T p.1 p.2)
    (ok : pcheck T raw mins s ws cap=true) : Impossible true T cap ws.toFinset := by
  unfold pcheck at ok
  split at ok
  · contradiction
  rename_i p get
  dsimp only at ok
  split at ok
  · contradiction
  rename_i pool eq
  exact poolCut_sound (lo _ (List.mem_of_getElem? get)) _ eq nd ok

abbrev Entry := List Sig × Nat × Nat × List (Nat × Nat)
def Entry.ws (e : Entry) := e.1
def Entry.cap (e : Entry) := e.2.1
def Entry.bits (e : Entry) := e.2.2.1
def Entry.links (e : Entry) := e.2.2.2

def linked (T : Sig) (states : Nat → Entry) (perm : Nat → List Move)
    (prior : Nat) (link : Nat × Nat) (k : Nat) (xs : List Sig) :=
  let moves := perm link.2
  let next := states link.1
  decide (link.1 < prior) && decide (next.cap=k) && (movedWord moves T == T) &&
    decide ((xs.map (movedWord moves)).toFinset = next.ws.toFinset)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem link_sound {T states perm prior link k xs}
    (onto : ∀ i, Function.Surjective (movedRow (perm i)))
    (low : ∀ i < prior, Impossible true T (states i).cap (states i).ws.toFinset)
    (ok : linked T states perm prior link k xs = true) : Impossible true T k xs.toFinset := by
  simp only [linked,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at ok
  obtain ⟨⟨⟨small,ck⟩,goal⟩,wires⟩ := ok
  intro n hn h
  have run := live_rename h _ (onto link.2)
  simp only [← moved_eq_rename] at run
  rw [goal] at run
  have se : (xs.toFinset.image (movedWord (perm link.2))) = (states link.1).ws.toFinset := by
    rw [←wires]
    ext v
    simp [Finset.mem_image,List.mem_map]
  have fn : rename (movedRow (perm link.2)) = movedWord (perm link.2) := funext fun a => (moved_eq_rename _ a).symm
  rw [fn,se] at run
  exact low _ small _ (by omega) run

def ticket (e : Entry) (a b : Sig) (op : Nat) (ka kb : Bool) :=
  let n := e.ws.length
  let span := if e.cap+1≤n then 1 else if e.cap≤n then 3 else 4
  let ai := e.ws.idxOf a
  let bi := e.ws.idxOf b
  let pos := ((bi*(bi-1)/2+ai)*4+op)*span+2*ka.toNat+kb.toNat
  (e.bits >>> (12*pos)) &&& 4095

def cell (T : Sig) (raw : List Sig) (mins : List (Sig × Nat)) (specs : Nat → Spec)
    (states : Nat → Entry) (perm : Nat → List Move) (i : Nat)
    (a b : Sig) (op : Nat) (ka kb : Bool) (child : List Sig) :=
  let e := states i
  let k := e.cap-1
  if child.length > k+1 then true else
  let tag := ticket e a b op ka kb
  if tag < 1024 then lost T child (Fin.ofNat 512 (tag/32), Fin.ofNat 512 (tag % 32)) else
  if tag < 2048 then pcheck T raw mins (specs (tag-1024)) child k else
  match e.links[tag-2048]? with
  | some ptr => linked T states perm i ptr k child
  | none => false

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem card_bound {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf tail ih =>
    have hz : bin d a b ∉ U := fun h => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    rw [Finset.card_insert_of_notMem hz] at ih
    have h1 := Finset.card_insert_le a (insert b U)
    have h2 := Finset.card_insert_le b U
    omega

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem size_sound {T cap} {ws : List Sig} (nd : ws.Nodup) (h : ws.length > cap+1) :
    Impossible true T cap ws.toFinset := by
  intro n hn run
  have b := card_bound run
  rw [List.toFinset_card_of_nodup nd] at b
  omega

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell_sound {T raw mins specs states perm i a b op ka kb child}
    (nd : child.Nodup) (onto : ∀ j, Function.Surjective (movedRow (perm j)))
    (lo : ∀ p ∈ mins, Slice true raw T p.1 p.2)
    (low : ∀ j < i, Impossible true T (states j).cap (states j).ws.toFinset)
    (ok : cell T raw mins specs states perm i a b op ka kb child=true) :
    Impossible true T ((states i).cap-1) child.toFinset := by
  unfold cell at ok
  dsimp only at ok
  split at ok
  · rename_i h; exact size_sound nd h
  split at ok
  · exact lost_sound ok
  split at ok
  · exact pcheck_sound nd lo ok
  split at ok
  · exact link_sound onto low ok
  · contradiction

def taggedLayer (go : Sig → Sig → Nat → Bool → Bool → List Sig → Bool) (ws : List Sig) :=
  ws.all fun a => ws.all fun b => if a.toNat < b.toNat then
    [0,1,2,3].all fun d => let z := bin d a b
      z == zero || z == one || ws.contains z ||
      ([false,true].all fun ka => [false,true].all fun kb => go a b d ka kb (childTwo ws a b d ka kb))
    else true

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tagged_sound {T ws cap} (nd : ws.Nodup) (out : T ∉ ws) {go : Sig → Sig → Nat → Bool → Bool → List Sig → Bool}
    (valid : ∀ a b d ka kb child, child.Nodup → go a b d ka kb child=true → Impossible true T (cap-1) child.toFinset)
    (ok : taggedLayer go ws=true) : Impossible true T cap ws.toFinset := by
  have oneSide (a b : Sig) (ha : a ∈ ws) (hb : b ∈ ws) (lt : a.toNat < b.toNat) (d : Nat)
      (hd : allowed true d) (ka kb : Bool) (fresh : bin d a b ∉ ws) (pp : proper (bin d a b)) :
      Impossible true T (cap-1) (childTwo ws a b d ka kb).toFinset := by
    have opmem : d ∈ [0,1,2,3] := by
      rcases allowed_four hd with h | h | ⟨_,h⟩ | ⟨_,h⟩ <;> simp [h]
    have ab := List.all_eq_true.mp (List.all_eq_true.mp ok _ ha) _ hb
    simp only [if_pos lt] at ab
    have op := List.all_eq_true.mp ab _ opmem
    simp only [beq_eq_false_iff_ne.mpr pp.1,beq_eq_false_iff_ne.mpr pp.2,
      List.contains_eq_mem,decide_eq_false fresh,Bool.false_or] at op
    exact valid a b d ka kb _ (child_nd nd _ _ _ _ _ ha hb (fun e => (Nat.ne_of_lt lt) (congrArg BitVec.toNat e)) fresh)
      (List.all_eq_true.mp (List.all_eq_true.mp op ka (by cases ka <;> simp)) kb (by cases kb <;> simp))
  apply enum_step nd out
  intro a ha b hb d hd ka kb ne fresh pp _
  have neN : a.toNat ≠ b.toNat := fun e => ne (BitVec.eq_of_toNat_eq e)
  rcases lt_or_gt_of_ne neN with hl | hl
  · exact oneSide _ _ ha hb hl _ hd _ _ fresh pp
  · rw [child_flip nd a b hd ka kb]
    rw [bin_flip hd] at fresh pp
    exact oneSide _ _ hb ha hl _ (flip_flip hd).1 _ _ fresh pp

def nodeOK (T : Sig) (raw : List Sig) (mins : List (Sig × Nat)) (specs : Nat → Spec)
    (states : Nat → Entry) (perm : Nat → List Move) (i : Nat) :=
  let e := states i
  decide e.ws.Nodup && !e.ws.contains T &&
    taggedLayer (cell T raw mins specs states perm i) e.ws

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem certified {T raw mins specs states perm N} (onto : ∀ j, Function.Surjective (movedRow (perm j)))
    (lo : ∀ p ∈ mins, Slice true raw T p.1 p.2)
    (ok : ∀ i < N, nodeOK T raw mins specs states perm i = true) :
    ∀ i < N, Impossible true T (states i).cap (states i).ws.toFinset := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi
    have good := ok _ hi
    simp only [nodeOK,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',
      List.contains_eq_mem,decide_eq_false_iff_not] at good
    exact tagged_sound good.1.1 good.1.2
      (fun _ _ _ _ _ _ nd v => cell_sound nd onto lo (fun j hj => ih j hj (by omega)) v) good.2

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem move_swap : ∀ i : Fin 4, ∀ r : Row, rowMove (swapNext i.val) (rowMove (swapNext i.val) r) = r := by
  decide +kernel

def permitted (xs : List (Fin 4)) := xs.map fun i => swapNext i.val
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem perm_onto (xs : List (Fin 4)) : Function.Surjective (movedRow (permitted xs)) := by
  induction xs with
  | nil => exact fun y => ⟨y,rfl⟩
  | cons j js ih =>
    intro y
    obtain ⟨v,hv⟩ := ih y
    refine ⟨rowMove (swapNext j.val) v,?_⟩
    change movedRow (permitted js) (rowMove (swapNext j.val) (rowMove (swapNext j.val) v)) = y
    rw [move_swap]
    exact hv
end GateForest12127

namespace CertBlocks12127
open PEqualNP.Outside.L_meta_12126.Core GateForest12127
def stamp (n a : Nat) : Sig := BitVec.ofNat 512 (a * ((2^512-1)/(2^(2^n)-1)))
def row (n : Nat) (ws : List Nat) (cap bits : Nat) (links : List (Nat×Nat)) : Entry :=
  ⟨ws.map (stamp n),cap,bits,links⟩
def Good (f : Nat → Bool) (start num : Nat) := ∀ i, start ≤ i → i < start+num → f i = true
theorem checkGood {f : Nat → Bool} {start num : Nat}
    (cert : (List.range num).all (fun j => f (start+j)) = true) : Good f start num := by
  intro i lo hi
  have chk := List.all_eq_true.mp cert (i-start) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le lo] using chk
theorem concatGood {f : Nat → Bool} {start n m : Nat}
    (a : Good f start n) (b : Good f (start+n) m) : Good f start (n+m) := by
  intro i l h
  by_cases c : i<start+n
  · exact a _ l c
  · exact b _ (by omega) (by omega)
end CertBlocks12127

namespace Tabe880
open PEqualNP.Outside.L_meta_12126.Core GateForest12127 CertBlocks12127 Bound12127
def root := inputs.take 4
def target := stamp 4 0xe880
def mins : List (Sig × Nat) := []
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pri : ∀ m ∈ mins, Slice true root target m.1 m.2 := by simp [mins]
def stateEntry0 : Entry := row 4 [0xaa,0xaaaa,0xcccc,0xf0f0,0xff00] 4 (packWords [0xe31a91a,0x90e30e51691690,0xe516200016a1c6,0x1630000e,0x10e10e31690e31,0xa80e316a0e31a9,0xe31a90e51680e,0x51ac0e51690e51,0x690e6000000000]) []
def stateEntry1 : Entry := row 4 [0xaaaa,0xcccc,0xf0f0,0xff00] 3 (packWords [0xe,0x31631a50e30e51,0x611630e50e6162,0x1630e60e10e10e,0x31690e20e20e31,0x6a0e40e40e51ac]) []
def stateEntry2 : Entry := row 4 [0x8888,0xe0e0,0xff00] 2 (packWords [0xe31631a,0x50e30e51601630,0xe50e00e00e3168]) []
def stateEntry3 : Entry := row 4 [0x8888,0xeeee,0xf0f0,0xff00] 3 (packWords [0xe,0x31631a50e31631,0xa41638010e5161,0x1630e50e31a80e,0x38000e10e10e31,0x690e4000000000]) [(2,0),(2,1)]
def stateEntry4 : Entry := row 4 [0xaa,0xaa00,0xcccc,0xf0f0,0xff00] 4 (packWords [0xe31a91a,0x90e30e51691690,0xe5162000000000,0x8010000e,0x10e10e316916a0,0xe31a90e30e20e2,0xe31a91680e516,0x90e50e40e40e51,0x69000000800000]) [(1,0),(3,2)]
def stateEntry5 : Entry := row 4 [0xff0,0xaaaa,0xcccc,0xfff0] 3 (packWords [0x1c,0xe50e51a11a00,0xe60e61c20e3000,0xe40e40e,0x51ac0e51c60e51,0xa50e61a50e61a4]) []
def stateEntry6 : Entry := row 4 [0xff0,0xaaaa,0xcccc,0xf000] 3 (packWords [0xe,0x51a11a30e50e61,0xa01a10e6000000,0x1a50000e40e40e,0x51ac0e10e10e31,0xcc0e20e20e31ac]) []
def stateEntry7 : Entry := row 4 [0x8888,0xe0e0,0xff00] 3 (packWords [0x1a50e30e31,0x631a81631a51a8,0x1a51630e30e316,0x30e50e51a51681,0x601631681631a5,0xe50e50e31680e,0x1a80e50e00e30,0xe50e31a8168168]) []
def stateEntry8 : Entry := row 4 [0x8888,0xe0e0,0xf0f0,0xff00] 3 (packWords [0x1a,0x51631a51631a41,0x631a51630e5160,0x1630e50e300000,0x1680e50e51,0x680e40e40e5168]) []
def stateEntry9 : Entry := row 4 [0x8888,0xe0e0,0xee00] 2 (packWords [0xe31631a,0x50e30e51601630,0xe50e00e00e3169]) []
def stateEntry10 : Entry := row 4 [0xee,0x8888,0xe0e0] 2 (packWords [0xe10e10e,0x31600e31a00e31,0x630e51600e5160]) []
def stateEntry11 : Entry := row 4 [0x8888,0xe0e0,0xeeee,0xff00] 3 (packWords [0x16,0x38011638000e31,0x631a50e30e5161,0x1630e51a800000,0x1680000000,0xe10e10e3169]) [(9,0),(10,0)]
def stateEntry12 : Entry := row 4 [0xee,0x8888,0xeeee,0xf0f0] 3 (packWords [0xe,0x31a00e38010e10,0xe10e31690e31a5,0xe316316000000,0x8000000000,0xe51630e5161]) [(2,1),(10,0)]
def stateEntry13 : Entry := row 4 [0x8888,0xe0f0,0xff00] 2 (packWords [0xe31631a,0x40e30e41601630,0xe40e00e00e3168]) []
def stateEntry14 : Entry := row 4 [0xa,0xaaaa,0xcccc,0xf000] 3 (packWords [0xe,0x51a51c20e50e21,0xa01a50e2000000,0x1a10000e00e00e,0x21ac8010e30e10,0xe1800000000000]) [(2,3),(13,4)]
def stateEntry15 : Entry := row 4 [0x8888,0xeeee,0xf0f0,0xff00] 4 (packWords [0x1a50e3,0xe31631a91631a,0x51a91a51630e30,0xe316380b16380a,0x1ac1a41631ac16,0x38098088071630,0xe50e51a5169161,0x1631691631a50e,0x50e50e38060e38,0x51ac1a80e31ac,0xe38048038020e,0x31690e11a90e50,0xe10e30e50e31a9,0x1691698018000e,0x40000000000000,0x0]) [(5,3),(6,3),(7,0),(8,0),(11,0),(12,1),(14,5),(7,1),(8,1),(11,1),(12,0),(14,3)]
def stateEntry16 : Entry := row 4 [0xff0,0xaaaa,0xcccc,0xf0f0] 3 (packWords [0xe,0x90e50e51650ea0,0xe60e61660e30e3,0x1a51630e40e40e,0x51ac0e51610e51,0xa50e61620e61a4]) []
def stateEntry17 : Entry := row 4 [0x8888,0xaaaa,0xe0e0,0xff00] 3 (packWords [0xe,0x31631a50e31631,0xa61631c50e5161,0x1630e50e31a80e,0x31c80e10e10e31,0x690e6000000000]) []
def stateEntry18 : Entry := row 4 [0x8888,0xaaaa,0xeeee,0xf0f0,0xff00] 4 (packWords [0xe31631a,0x50e31631c41638,0x21631a61631c5,0xe51611630e50e,0x31c80e38010e31,0xaa0e31c90e10e1,0xe31691ac00000,0x8000000000,0xe6000000000]) [(16,3),(17,0),(17,1)]
def stateEntry19 : Entry := row 4 [0xaaaa,0xcccc,0xf0f0,0xff80] 3 (packWords [0xe,0x30e31a51630e50,0xe51631a50e60e6,0x1631c60e90e91c,0xa1690ea0ea1a91,0x6a0ec0ec1691ac]) []
def stateEntry20 : Entry := row 4 [0x2aaa,0xcccc,0xf0f0,0xff00] 3 (packWords [0xe,0x31631a50e30e51,0x611630e50e6162,0x1630e60e10e10e,0x31690e20e20e31,0x6a0e40e40e51ac]) []
def stateEntry21 : Entry := row 4 [0x8080,0xaaaa,0xcccc,0xf0f0,0xff00] 4 (packWords [0x1a11631a,0x51631611611631,0xa51621621631c6,0x80116380016316,0x91a91ca16916a1,0xa81a916a0e3000,0x16816816,0x91ac0e50000000,0xe6000000000]) [(19,0),(20,2)]
def stateEntry22 : Entry := row 4 [0x8888,0xe0a0,0xff00] 2 (packWords [0xe31631a,0x50e30e51601630,0xe50e00e00e3168]) []
def stateEntry23 : Entry := row 4 [0x8888,0xeaea,0xf0f0,0xff00] 3 (packWords [0xe,0x31631a50e31631,0xa41638010e5161,0x1630e50e31a80e,0x38000e10e10e31,0x690e4000000000]) [(2,0),(22,1)]
def stateEntry24 : Entry := row 4 [0xa8a8,0xcccc,0xf0f0,0xff00] 3 (packWords [0xe,0x31631a50e30e51,0xa51630e50e6162,0x1630e60e30e50e,0x38000e20e20e31,0x6a0e40e40e51ac]) [(2,6)]
def stateEntry25 : Entry := row 4 [0xa888,0xcccc,0xf0f0,0xff00] 3 (packWords [0xe,0x31631c60e31631,0xc41638010e6162,0x1630e60e31c80e,0x38000e20e20e31,0x6a0e40e40e61ac]) [(22,7),(22,8)]
def stateEntry26 : Entry := row 4 [0xea,0xaaaa,0xcccc,0xf0f0] 3 (packWords [0xe,0x10e10e31690e30,0xe60e31620e31a5,0xe31630e50e60e,0x51a40e51630e51,0x610e61620e6162]) []
def stateEntry27 : Entry := row 4 [0xaaaa,0xcccc,0xeaea,0xf0f0,0xff00] 4 (packWords [0xe31631a,0x50e31638051638,0x40e51611630e5,0xe61c61630e60e,0x31ca0e38030e10,0xe10e31690e30e6,0xe38021cc0e50e,0x580116a0000000,0xe50e60e5800]) [(23,0),(24,9),(23,10),(24,11),(25,2),(26,0)]
def stateEntry28 : Entry := row 4 [0x88,0xaaaa,0xcccc,0xf0f0,0xff00] 4 (packWords [0xe31a11a,0x50e31611611691,0xa516216216a1c6,0x1630000e,0x31a90e31690e31,0xa80e316a0e31a9,0xe31a916816816,0x91ac0e50000000,0xe6000000000]) []
def stateEntry29 : Entry := row 4 [0xaaa,0xaaaa,0xcccc,0xf0f0,0xff00] 4 (packWords [0xe31631c,0x60e30e51611630,0xe51631a41631c6,0x1631c61631a50e,0x10e10e31690e31,0xa80e31ca0e31ca,0xe31a90e51cc0e,0x51ac0e51cc0e51,0xcc0e6000000000]) []
def stateEntry30 : Entry := row 4 [0x8888,0xa0a0,0xc0c0,0xff00] 3 (packWords [0x1c,0x1631c61631a01,0x631a5163160160,0x1631a50e30e380,0x21a80e50e58011,0x680e60e6800168]) [(2,6),(2,11),(2,0)]
def stateEntry31 : Entry := row 4 [0x8888,0xa0a0,0xcccc,0xf0f0,0xff00] 4 (packWords [0x1a51631a,0x51631631a51631,0xa51a41631a5163,0x1621621631a51c,0x81c81ca8030e30,0x16a1ca,0x80216a1ac1cc80,0x11ac0e50000000,0xe60e680016a]) [(24,0),(23,9),(23,11),(30,0)]
def stateEntry32 : Entry := row 4 [0xaa,0xaaaa,0xcc00,0xcccc,0xf0f0] 4 (packWords [0xe10e10e,0x31a91c20e31c60,0xe30e31a00e316a,0xe31a50e31a116,0x90000000000e51,0x6a0e51a40e5800,0xe51a516216216,0xa1a40000001630,0xe6000000000]) [(14,10)]
def stateEntry33 : Entry := row 4 [0x8888,0xaaaa,0xcccc,0xf0f0,0xff00] 5 (packWords [0x1a50e30e31,0x631a91631a51a9,0x1a51630e30e316,0x38161631a51cc1,0xa51631cc1631a5,0x8151a516381416,0x31c61ac1a41631,0xac1631c68131c6,0x1638121631a581,0x11a51638101631,0xa580f1a50e380e,0xe31a91cc1a90e,0x31cc0e31a980d1,0xa90e380c0e31ca,0x1ac1a80e31ac0e,0x31ca80b1ca0e38,0xa0e31a98091a9,0xe38080e31a980,0x71a98031ac1ac1,0xcc8011cc806805,0x80400000000080,0x38020e50000000,0x0,0x8018000e,0x60000000000000,0x0]) [(0,12),(4,12),(0,13),(4,13),(15,0),(18,9),(18,0),(21,0),(27,11),(28,1),(29,5),(31,0),(32,14),(31,9),(32,15),(21,2),(27,2),(28,0),(29,3),(31,16),(32,17),(31,8),(32,18)]
def stateEntry34 : Entry := row 4 [0xaa,0xaaaa,0xcc88,0xf0f0] 3 (packWords [0xe,0x10e10e31690e31,0xa00e316a0e31a5,0xe31630e51600e,0x51a40e51630e51,0x61800000000000]) [(2,2)]
def stateEntry35 : Entry := row 4 [0xaa,0xaaaa,0xcccc,0xf0f0,0xffaa] 4 (packWords [0x1c20e30e,0x38031c40e50e58,0x2162000000000,0x8010000000000e,0x10e10e31690e31,0xa80e316a0e31a5,0xe31630e51680e,0x51ac0e51630e51,0x61800000000000]) [(3,2),(1,0),(34,0),(34,10)]
def stateEntry36 : Entry := row 4 [0xa8a8,0xcccc,0xf0f0,0xff00] 4 (packWords [0x1a50e3,0xe31631ca1631a,0x51ca1a51630e30,0xe31630e50e51a5,0x1cc1a51631cc16,0x31a50e50e51630,0xe60e61c616a162,0x16316a1631c60e,0x60e60e38040e38,0x30e50e50e30e5,0xe38028018000e,0x316a0e21ca0e60,0xe20e30e60e31ca,0x16a16a0e51ac0e,0x41cc0e60e40e50,0xe60e51cc1ac1ac]) [(7,6),(17,6),(17,7),(34,19),(34,15)]
def stateEntry37 : Entry := row 4 [0xa8a8,0xaaaa,0xcccc,0xf0f0,0xff00] 4 (packWords [0xe31631a,0x50e30e51a51630,0xe51631c61631c6,0x1631c61631c60e,0x30e50e38000e31,0xca0e31ca0e31a9,0xe31ca0e51cc0e,0x51cc0e51690e51,0xcc0e6000000000]) [(8,6)]
def stateEntry38 : Entry := row 4 [0xee,0xaaaa,0xcccc,0xf0f0] 3 (packWords [0xe,0x10e10e31690e20,0xe20e316a0e31a5,0xe31630e50e60e,0x51a40e51630e51,0x610e61630e6162]) []
def stateEntry39 : Entry := row 4 [0xa8a8,0xcccc,0xf0f0,0xfc00] 3 (packWords [0xe,0x31631a50e30e51,0xa51630e50e6162,0x1630e60e30e50e,0x38000e20e20e31,0x6a0e40e40e51ac]) [(9,6)]
def stateEntry40 : Entry := row 4 [0xee,0xaaaa,0xcccc,0xe0e0] 3 (packWords [0xe,0x10e10e31690e20,0xe20e316a0e31a5,0xe31630e50e60e,0x58000e51630e51,0x610e61630e6162]) [(10,0)]
def stateEntry41 : Entry := row 4 [0xa8a8,0xcccc,0xf0f0,0xfcfc,0xff00] 4 (packWords [0x16380516,0x38040e31631a50,0xe30e51a51630e5,0xe61621630e680,0x30000000008020,0x801000,0xe30e500,0x8000e20e20e31,0x6a0e40e40e51ac]) [(11,6),(38,14),(34,15),(34,19),(39,0),(40,6)]
def stateEntry42 : Entry := row 4 [0xaaa8,0xcccc,0xf0f0,0xff00] 3 (packWords [0xe,0x31631a50e30e51,0x691630e50e6162,0x1630e60e30e50e,0x31690e20e20e31,0x6a0e40e40e51ac]) []
def stateEntry43 : Entry := row 4 [0xfe,0xaaaa,0xcccc,0xf0f0] 3 (packWords [0xe,0x10e10e31690e20,0xe20e316a0e31a5,0xe31630e40e40e,0x51ac0e51630e51,0x610e61630e6162]) []
def stateEntry44 : Entry := row 4 [0xaaaa,0xcccc,0xf0f0,0xfefe,0xff00] 4 (packWords [0x16380416,0x38030e31631a50,0xe30e51611630e5,0xe61621630e680,0x20000000008010,0x800000,0xe10e10e,0x31690e20e20e31,0x6a0e40e40e51ac]) [(38,14),(38,15),(38,1),(42,2),(43,0)]
def stateEntry45 : Entry := row 4 [0xee,0xaaaa,0xcccc,0xf0f0] 4 (packWords [0xe3169,0xe11a90e50e10e,0x30e50e31a91691,0x690e316a0e21ca,0xe60e20e30e60e,0x31ca16a16a0e31,0x630e31a91a51a5,0xe31a50e31a916,0x31630e51a40e51,0xc40e60e60e50e6,0xe51c41a41a40e,0x51a50e51691631,0x630e51630e5169,0x1a51610e61c60e,0x616a1631630e61,0x630e616a1c6162]) []
def stateEntry46 : Entry := row 4 [0xee,0xaaaa,0xcccc,0xf0f0,0xff00] 4 (packWords [0xe31a91a,0x90e30e51691690,0xe50e616a16a0e6,0x1630000e,0x10e10e31690e20,0xe20e316a0e31a9,0xe31a90e50e60e,0x51ac0e51690e51,0x690e616a0e616a]) []
def stateEntry47 : Entry := row 4 [0xee,0xe0e,0xaaaa,0xcccc] 3 (packWords [0xe,0x50e60e51a01690,0xe30e10e10e5163,0xe516116a0e30e,0x20e20e61630e61,0x620e31630e31a5]) []
def stateEntry48 : Entry := row 4 [0xee,0xaaaa,0xcccc,0xeeee,0xf0f0] 4 (packWords [0xe38030e,0x38020e10e10e31,0x690e20e20e316a,0xe31a50e31631c,0x40000000001a40,0x801000,0xe50e600,0x8000e51630e51,0x610e61630e6162]) [(12,0),(24,2),(40,0),(47,0)]
def stateEntry49 : Entry := row 4 [0xaaaa,0xcccc,0xf0f0,0xff02] 3 (packWords [0xe,0x31631a10e30e51,0x611610e50e6162,0x1630e60e30e50e,0x31610e20e20e31,0x6a0e40e40e51ac]) []
def stateEntry50 : Entry := row 4 [0xa8aa,0xcccc,0xf0f0,0xff00] 3 (packWords [0xe,0x31631a50e30e51,0x611630e50e6162,0x1630e60e10e10e,0x38000e20e20e31,0x6a0e40e40e51ac]) [(13,6)]
def stateEntry51 : Entry := row 4 [0xa,0xaaaa,0xcccc,0xf0f0,0xff00] 4 (packWords [0x1a51a91a,0x58030e51691690,0xe50e616216a0e6,0x16300016,0x90e50e51690e20,0xe20e616a000000,0xe30000e40e40e,0x51ac8020e58010,0xe5800000000000]) [(24,12),(49,12),(50,13),(14,0)]
def stateEntry52 : Entry := row 4 [0xaaaa,0xcccc,0xeeee,0xf0f0,0xff00] 5 (packWords [0x1a50e30e31,0x631a91631a51a9,0x1a51630e30e316,0x38161638158148,0x13163812163811,0x81080f1630e50e,0x51a51691611631,0x691631a50e50e5,0x1630e60e61c616,0xa16216316a1631,0xc60e60e60e380e,0xe380d80c80b0e,0x380a0e38098088,0x70e31690e11a9,0xe50e10e30e50e,0x31a91691690e31,0x6a0e21ca0e60e2,0xe30e60e31ca16,0xa16a8068031cc0,0x0,0x80,0x58041ac0000000,0x0,0xe58040e,0x58030e60e60000,0x802801800]) [(15,0),(18,9),(18,0),(35,12),(35,13),(0,13),(0,12),(36,11),(37,11),(41,11),(44,0),(45,1),(46,1),(48,1),(51,5),(36,2),(37,2),(41,2),(44,2),(45,0),(46,0),(48,0),(51,3)]
def stateEntry53 : Entry := row 4 [0x8888,0xaaaa,0xcccc,0xf0f0,0xff00] 4 (packWords [0xe31631a,0x50e31631a51631,0xa51631a41631c6,0x1631a51631a50e,0x31a90e31a90e31,0xa80e31ca0e31a9,0xe31a91ac1cc80,0xe50000000,0xe6000000000]) [(3,0)]
def stateEntry54 : Entry := row 4 [0xaaaa,0xaaee,0xcccc,0xf0f0,0xff00] 4 (packWords [0xe31631a,0x50e30e51611630,0xe51638001631c6,0xe61621630e60e,0x10e10e31690e31,0xca0e31ca0e20e2,0xe31ca0e51cc0e,0x51cc0e50e60e51,0xcc16a000000000]) [(38,0)]
def stateEntry55 : Entry := row 4 [0x88aa,0xaaaa,0xcccc,0xf0f0,0xff00] 4 (packWords [0xe31631a,0x90e30e51611630,0xe51631a41631c6,0x1631c61631a50e,0x10e10e31a90e31,0xa80e31ca0e31a9,0xe31a90e51cc0e,0x51ac0e51690e51,0xcc0e6000000000]) []
def stateEntry56 : Entry := row 4 [0xaaaa,0xcccc,0xeeee,0xf0f0,0xff00] 4 (packWords [0xe31631a,0x50e31638041638,0x30e51611630e5,0xe61621630e60e,0x38020e38010e10,0xe10e31690e20e2,0xe316a1cc00000,0x1ac0000000,0xe50e6000800]) [(3,0),(24,11),(38,1),(24,2),(38,0)]
def stateEntry57 : Entry := row 4 [0xaa,0x5500,0xaaaa,0xcccc,0xf0f0] 4 (packWords [0xe10e10e,0x31690e31a00e31,0x621c20e31c60e3,0xe31a50e31630e,0x51600e51a41c40,0xe51c60e50e5163,0xe516100000016,0xa0000e60000000,0x800000]) [(16,6)]
def stateEntry58 : Entry := row 4 [0xaa,0xcc,0xaaaa,0xcccc,0xf0f0] 4 (packWords [0xe31a90e,0x31690e31a00e31,0x6a0e31a90e31a9,0xe31a50e31a116,0x1601691a40e50,0x1a5169,0x1611611c616a16,0x21620e60000000,0x1631638001a5]) [(38,0)]
def stateEntry59 : Entry := row 4 [0xaa,0xaaaa,0xcccc,0xf0f0,0xff00] 5 (packWords [0x1c60e30e38,0x111a91a91c61a9,0x1a98100e30e31c,0x60e50e580f1691,0x691c616916980e,0xe50e580d80c16,0x200000000080b1,0x6a16a1c68011c6,0x0,0x80b80a1630,0xe3169,0xe11a90e50e10e,0x30e50e31a91691,0x690e316a0e31ca,0x1ac1a80e31ac0e,0x31ca16a16a0e38,0x90e31a98081a9,0xe38070e31a980,0x61a90e51ac0e51,0xcc16a1680e516a,0xe51cc1ac1ac0e,0x58050e51698041,0x690e58030e5169,0x8021698018000e,0x60000000000000,0x0]) [(53,2),(4,0),(28,0),(54,9),(51,10),(55,13),(28,11),(54,11),(51,0),(55,20),(56,2),(35,0),(57,4),(57,0),(32,0),(58,0),(32,10),(58,11)]
def stateEntry60 : Entry := row 4 [0xaaaa,0xcccc,0xf0f0,0xff00] 6 (packWords [0x8171a50e,0x30e38161631a91,0x638151a51a91a5,0x8141630e30e381,0x31630e50e58121,0xa5169161811163,0x1691638101a50e,0x50e580f1630e60,0xe680e1c616a162,0x80d16316a16380,0xc1c60e60e680b0,0xe31690e180a1a9,0xe50e18090e30e,0x50e38081a91691,0x698070e316a0e2,0x8061ca0e60e280,0x50e30e60e38041,0xca16a16a8030e5,0x1ac0e48021cc0e,0x60e48010e50e60,0xe58001cc1ac1ac]) [(33,0),(52,0),(59,12),(59,13),(33,11),(52,11),(59,16),(59,20),(33,6),(52,6),(59,8),(59,5),(33,2),(52,2),(59,0),(59,4),(33,21),(52,21),(59,9),(59,3),(33,3),(52,3),(59,11),(59,2)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def ds : Array Entry := #[stateEntry0,stateEntry1,stateEntry2,stateEntry3,stateEntry4,stateEntry5,stateEntry6,stateEntry7,stateEntry8,stateEntry9,stateEntry10,stateEntry11,stateEntry12,stateEntry13,stateEntry14,stateEntry15,stateEntry16,stateEntry17,stateEntry18,stateEntry19,stateEntry20,stateEntry21,stateEntry22,stateEntry23,stateEntry24,stateEntry25,stateEntry26,stateEntry27,stateEntry28,stateEntry29,stateEntry30,stateEntry31,stateEntry32,stateEntry33,stateEntry34,stateEntry35,stateEntry36,stateEntry37,stateEntry38,stateEntry39,stateEntry40,stateEntry41,stateEntry42,stateEntry43,stateEntry44,stateEntry45,stateEntry46,stateEntry47,stateEntry48,stateEntry49,stateEntry50,stateEntry51,stateEntry52,stateEntry53,stateEntry54,stateEntry55,stateEntry56,stateEntry57,stateEntry58,stateEntry59,stateEntry60]
def states (i : Nat) := ds[i]?.getD default
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def ms : Array (List (Fin 4)) := #[[],[2],[0,1,2],[0,1,2,0,1],[0,1,2,0,1,0],[1,2,0,1],[0,1,0],[1,0],[1,2,0],[0],[1],[0,1],[1,2,1],[1,2,1,0],[2,0,1,0],[2,0,1],[1,2],[0,1,2,1,0],[0,1,2,1],[2,0],[1,2,0,1,0],[0,1,2,0]]
def perm (i : Nat) := permitted (ms[i]?.getD [])
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def specTab : Array Spec := #[]
def spec (i : Nat) := specTab[i]?.getD (0,[])
def checked (i : Nat) := nodeOK target root mins spec states perm i
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block0 : Good checked 0 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block1 : Good checked 4 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block2 : Good checked 8 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block3 : Good checked 12 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block4 : Good checked 16 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block5 : Good checked 20 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block6 : Good checked 24 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block7 : Good checked 28 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block8 : Good checked 32 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block9 : Good checked 36 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block10 : Good checked 40 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block11 : Good checked 44 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block12 : Good checked 48 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block13 : Good checked 52 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block14 : Good checked 56 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block15 : Good checked 60 1 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem total : Good checked 0 61 := (concatGood (concatGood (concatGood (concatGood block0 block1) (concatGood block2 block3)) (concatGood (concatGood block4 block5) (concatGood block6 block7))) (concatGood (concatGood (concatGood block8 block9) (concatGood block10 block11)) (concatGood (concatGood block12 block13) (concatGood block14 block15))))
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem impossible : Impossible true target 6 root.toFinset := by
  have h := certified (states:=states) (perm:=perm) (specs:=spec) (N:=61) (fun j => perm_onto _) pri (fun i hi => total i (by omega) hi) 60 (by decide)
  exact h
def essentials : List (Sig × Row × Row) := [(root.getD 0 zero,6,7),(root.getD 1 zero,5,7),(root.getD 2 zero,3,7),(root.getD 3 zero,3,11)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lower : Lower true root target 7 := by
  apply lower_impossible (L:=6) (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro a ha
    apply essential_ok (xs:=essentials) (by decide +kernel) a
    exact (show (essentials.map Prod.fst).toFinset = root.toFinset by decide +kernel).symm ▸ List.mem_toFinset.mpr ha
  · exact impossible
end Tabe880

namespace Tabfee8
open PEqualNP.Outside.L_meta_12126.Core GateForest12127 CertBlocks12127 Bound12127
def root := inputs.take 4
def target := stamp 4 0xfee8
def mins : List (Sig × Nat) := []
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pri : ∀ m ∈ mins, Slice true root target m.1 m.2 := by simp [mins]
def stateEntry0 : Entry := row 4 [0xaa,0xaaaa,0xcccc,0xf0f0,0xff00] 4 (packWords [0xa114218,0x40a10611401420,0x61120000128142,0x12100006,0x10a10c20610a10,0xc20a10c20a10c2,0xa10c20610c406,0x10c40610c40610,0xc4062000000000]) []
def stateEntry1 : Entry := row 4 [0xaaaa,0xcccc,0xf0f0,0xff00] 3 (packWords [0xa,0x11211840a10611,0x21142061062120,0x1210620610a10c,0x20610620a00a10,0x620600600610a4]) []
def stateEntry2 : Entry := row 4 [0xaaaa,0xfccc,0xfff0] 2 (packWords [0x610a10c,0x20610620a00a10,0x620600600610a4]) []
def stateEntry3 : Entry := row 4 [0xaa,0xcccc,0xfaf0,0xff00] 3 (packWords [0xa,0x11201240a10611,0x24142061000000,0x8000000610a10c,0x20610620a00a10,0x620600600610a4]) [(2,0)]
def stateEntry4 : Entry := row 4 [0x8888,0xeeee,0xf0f0,0xff00] 3 (packWords [0xa,0x11211840a10a41,0x201210a4061121,0x8010610a00a00a,0x11280610a18000,0x61060000000000]) [(2,1),(2,2)]
def stateEntry5 : Entry := row 4 [0xaa,0xaa00,0xcccc,0xf0f0,0xff00] 4 (packWords [0xa114218,0x40a10611401420,0x61120000000000,0x80300006,0x10a10c20611280,0xa18020a10620a0,0xa106212806180,0x10610600600610,0xa4000000800000]) [(1,3),(3,4),(3,3),(4,5)]
def stateEntry6 : Entry := row 4 [0xff0,0xaaaa,0xcccc,0xfff0] 3 (packWords [0x6,0x10c40c40610620,0xa40a40620a1000,0x6006006,0x10a40c40610c40,0x610a40620a4062]) []
def stateEntry7 : Entry := row 4 [0xff0,0xaaaa,0xcccc,0xf000] 3 (packWords [0x6,0x11801820610621,0x80181062000000,0x18400006006006,0x10a40a10610c20,0x610a00620a1062]) []
def stateEntry8 : Entry := row 4 [0xaaaa,0xfccc,0xfff0] 3 (packWords [0xc20610610,0xa10c40a10c20c4,0xc20a10610610a,0x10620620c20a40,0xa00a10a40a10c2,0x620620610a406,0xc40620600610,0x620610c40a40a4]) []
def stateEntry9 : Entry := row 4 [0xaaaa,0xcccc,0xfaaa,0xfff0] 3 (packWords [0xa,0x10c20a10c20610,0xa10c20610a10c2,0xa10c20c406106,0x10c40620000000,0x610c40610c4]) []
def stateEntry10 : Entry := row 4 [0xeaea,0xfcfc,0xffc0] 2 (packWords [0x610c114,0x20610620c21210,0x62060060061128]) []
def stateEntry11 : Entry := row 4 [0xaaa,0xfccc,0xfff0] 2 (packWords [0x610a10c,0x20610620a00a10,0x620600600610a4]) []
def stateEntry12 : Entry := row 4 [0x8888,0xeeee,0xf0f0,0xff88] 3 (packWords [0xa,0x11211840a10a41,0x201210a4061000,0xa00a00a,0x11288010a18000,0xa1068000000000]) [(10,6),(11,2)]
def stateEntry13 : Entry := row 4 [0xaaaa,0xdccc,0xfff0] 2 (packWords [0x610a10c,0x20610620a00a10,0x620600600610a4]) []
def stateEntry14 : Entry := row 4 [0x88,0xeeee,0xf0f0,0xff00] 3 (packWords [0xa,0x11211840a10a41,0x201210a4000000,0x8010000a00a00a,0x11280610a18000,0x61060000000000]) [(13,1),(2,2)]
def stateEntry15 : Entry := row 4 [0xaaa,0xcccc,0xf000,0xfff0] 3 (packWords [0x18,0x610,0xa10c20610620a0,0xa106206118480,0x10610000008000,0x600600610a4]) [(2,7),(11,3)]
def stateEntry16 : Entry := row 4 [0x8888,0xeeee,0xf0f0,0xff00] 4 (packWords [0x1840a1,0xa112118812118,0x41881841210a10,0xa11210a40a4184,0x12812012112812,0x11840a40a480b0,0x6106112180a121,0x80980880712106,0x10610a11280a01,0x880a40a00a10a4,0xa118812812880,0x60610610a18050,0xa18048038020a1,0x6106180180006,0x0,0x0]) [(6,1),(7,1),(8,1),(9,2),(12,8),(14,8),(15,2),(8,2),(9,1),(12,3),(14,3),(15,1)]
def stateEntry17 : Entry := row 4 [0xff0,0xaaaa,0xcccc,0xf0f0] 3 (packWords [0x6,0x10c40c40610620,0xa40a40620a10a1,0x18412106006006,0x10a40c40610c40,0x610a40620a4062]) []
def stateEntry18 : Entry := row 4 [0xaaaa,0xcccc,0xfaf0,0xffaa] 3 (packWords [0xc,0x20a10a10c20c40,0x610610c4062000,0x610a10c,0x20610a10a80a10,0xc20610680610c4]) []
def stateEntry19 : Entry := row 4 [0x8888,0xaaaa,0xeeee,0xf0f0,0xff00] 4 (packWords [0xa112118,0x40a10c41401210,0xc4121122121141,0x611218020610a,0x10c00a11480a10,0xa20a10c10610a1,0x8010610a400000,0x8000000000,0x62000000000]) [(17,1),(18,9),(18,10)]
def stateEntry20 : Entry := row 4 [0xaaa,0xcccc,0xf0f0,0xff00] 3 (packWords [0xa,0x11211840a10611,0x21142061062120,0x1210620610a10c,0x20610620a00a10,0x620600600610a4]) []
def stateEntry21 : Entry := row 4 [0xaaaa,0xcccc,0xf0f0,0xff80] 3 (packWords [0xa,0x11211840a10611,0x21142061062120,0x1210620610a10c,0x20610620a00a10,0x620600600610a4]) []
def stateEntry22 : Entry := row 4 [0x2aaa,0xcccc,0xf0f0,0xff00] 3 (packWords [0xa,0x11211840a10611,0x21142061062120,0x1210620610a10c,0x20610620a00a10,0x620600600610a4]) []
def stateEntry23 : Entry := row 4 [0x8080,0xaaaa,0xcccc,0xf0f0,0xff00] 4 (packWords [0xa112118,0x40a10611211420,0x61062120121062,0x80412180312106,0x10a10c20610620,0xa00a1062802000,0x6006006,0x10a48010000000,0x800000000000]) [(20,11),(20,12),(20,2),(21,3),(22,5)]
def stateEntry24 : Entry := row 4 [0xaaaa,0xcccc,0xf0f0,0xff88] 4 (packWords [0x1840a1,0xa112118812118,0x41881841210a10,0xa11420c4061121,0x14806114214814,0x21210c40c41210,0xa4062142128062,0x1211281211420a,0x40a40c21480c00,0xa10c40a10c20c4,0xc20a11480a10a,0x11280a00c20a40,0xa00a10a40a10c2,0x1280c28040a406,0x80c48030688028,0x18000c40a40a4]) [(8,2),(18,13),(18,10),(3,10),(3,13)]
def stateEntry25 : Entry := row 4 [0xaaaa,0xcccc,0xeaea,0xf0f0,0xff00] 4 (packWords [0xa112118,0x40a11211421211,0x42061121142061,0x1211421211420a,0x10c20a11880610,0xa18000610a1188,0xa11880c406106,0x11480620000000,0x61148061148]) [(9,11)]
def stateEntry26 : Entry := row 4 [0xaaaa,0xcccc,0xf8f8,0xff88] 3 (packWords [0xa,0x11211840a10c41,0x211420c40a4120,0x1210a40c00a10c,0x20a10a00a00a10,0xc20a40c48000a4]) [(10,6)]
def stateEntry27 : Entry := row 4 [0xaaa,0xf0f0,0xfccc,0xff00] 3 (packWords [0x6,0x11211420610a11,0x218000a1062120,0x1210620a10610c,0x20610600600610,0xa40620a00a1062]) [(11,3)]
def stateEntry28 : Entry := row 4 [0x8888,0xaaaa,0xcccc,0xf0f0,0xff88] 4 (packWords [0xa112118,0x40a10c41211420,0xc40a41201210a4,0x8050000000000c,0xa10c20a10a00,0xa00a10c28040a1,0x8030a10a40c480,0x20008010000000,0x800000000000]) [(3,10),(3,13),(12,3),(26,3),(27,2),(20,1)]
def stateEntry29 : Entry := row 4 [0xaaaa,0xcccc,0xf0f0,0xff08] 3 (packWords [0xa,0x11211840a10610,0x611420c4062062,0x1210a40c00a10c,0x20a10a00a00a10,0xc20680688000a4]) [(13,2)]
def stateEntry30 : Entry := row 4 [0x8aaa,0xcccc,0xf0f0,0xff00] 3 (packWords [0xa,0x11211840a10611,0x21142061062120,0x1210620610a10c,0x20610620a00a10,0x620600600610a4]) []
def stateEntry31 : Entry := row 4 [0xaaaa,0xcccc,0xf0f0,0xff88] 3 (packWords [0xa,0x11211840a10610,0x611420c4062062,0x1210a40c00a10c,0x20a10a00a00a10,0xc20680688000a4]) [(2,2)]
def stateEntry32 : Entry := row 4 [0x88,0xaaaa,0xcccc,0xf0f0,0xff00] 4 (packWords [0xa112118,0x40a10c41211420,0xc40a41201210a4,0x8030000c,0xa10c20a10a00,0xa00a10c28020a1,0x8010a10a40c480,0xa40610000000,0x62000000000]) [(14,3),(29,8),(30,2),(31,3)]
def stateEntry33 : Entry := row 4 [0xaaa,0xcccc,0xf0f0,0xff00] 4 (packWords [0x1840a1,0xa112118812118,0x41881841210a10,0xa1142061061121,0x14812114214814,0x21210610611210,0x62062142128120,0x12112812114206,0x20620c20610610,0xa10c40a10c20c4,0xc20a10610610a,0x10620620c20a40,0xa00a10a40a10c2,0x620620610a406,0xc40620600610,0x620610c40a40a4]) []
def stateEntry34 : Entry := row 4 [0xaaa,0xaaaa,0xcccc,0xf0f0,0xff00] 4 (packWords [0xa112118,0x40a10611211420,0x61121142121142,0x12114212114206,0x10a10c20610a10,0xc20a10c20a10c2,0xa10c20610c406,0x10c40610c40610,0xc4062000000000]) []
def stateEntry35 : Entry := row 4 [0xaaa,0xccc,0xf0f0,0xff00] 3 (packWords [0xa,0x11211840a10611,0x21142061062120,0x1210620610a10c,0x20610620a00a10,0x620600600610a4]) []
def stateEntry36 : Entry := row 4 [0xaaa,0xcccc,0xf000,0xf0f0,0xff00] 4 (packWords [0xa112180,0x30001840000000,0x61121142061,0x6212012106218,0x80000000000610,0xa10c20610620a0,0xa106206180280,0x10610000008000,0x600600610a4]) [(31,14),(27,3),(35,3),(15,3)]
def stateEntry37 : Entry := row 4 [0x8888,0xaaaa,0xcccc,0xf0f0,0xff00] 5 (packWords [0x1840a10a11,0x21188121184188,0x1841210a10a114,0x20c40c41211481,0x21142148142121,0xc40c41210a40a,0x41421281201211,0x281211420a40a4,0x81681581412181,0x31218128118101,0x2180f1210c2148,0xc00a10c40a10c,0x20c40c20a11480,0xa10a11280a00c2,0xa40a00a10a40a,0x10c21280c280e8,0xd80c0a180b0a1,0x80a8098080a180,0x70a18030a40a40,0xc48010c4806805,0x80400000000080,0x38020610000000,0x0,0x80180006,0x20000000000000,0x0]) [(0,9),(5,9),(0,15),(5,15),(16,3),(19,7),(19,3),(23,3),(24,8),(25,6),(28,8),(32,8),(33,2),(34,2),(36,2),(23,5),(24,3),(25,5),(28,3),(32,3),(33,1),(34,1),(36,1)]
def stateEntry38 : Entry := row 4 [0xaa,0xaaaa,0xcccc,0xf0f0,0xffaa] 4 (packWords [0xc20a10a,0x10c20c40610610,0xc4120000000000,0x80100000000006,0x10a10c20610a10,0xc20a10c20a10c2,0xa10c20610c406,0x10c40610c40610,0xc4800000000000]) [(4,5),(1,3)]
def stateEntry39 : Entry := row 4 [0xaaaa,0xfcfc,0xffcc,0xfff0] 3 (packWords [0xc,0x20c40c28020a10,0xa10c28010620a4,0xa40620610610c,0x48000a40620620,0xa40e80620620c8]) [(2,3),(2,4),(2,11)]
def stateEntry40 : Entry := row 4 [0xaaaa,0xfcec,0xfff0] 2 (packWords [0x610a10c,0x20610620a21210,0x620600600610c4]) []
def stateEntry41 : Entry := row 4 [0xa8a8,0xcccc,0xfafa,0xff00] 3 (packWords [0xc,0x21201210c20c11,0x211420c10a1121,0x8010a10c00c00c,0x11280620000000,0x610618000a1]) [(2,16),(40,12)]
def stateEntry42 : Entry := row 4 [0xaaaa,0xcccc,0xf0f0,0xffaa,0xffcc] 4 (packWords [0x12114212,0x18030a10c20c20,0xa1061000000000,0x1211281218020c,0x20a10a10c21421,0x48142801062000,0xc20a10c,0x20a10a10c20a10,0xc2068068800128]) [(39,6),(41,17),(41,8),(31,3)]
def stateEntry43 : Entry := row 4 [0xaa,0xcccc,0xeeee,0xf0f0,0xff00] 4 (packWords [0xa114218,0x40a11201201281,0x84061184122061,0x1210000a,0x11880a11280610,0xa10c20610620c2,0xa10620c400000,0xa40000000,0x61062061800]) [(14,3)]
def stateEntry44 : Entry := row 4 [0xaaaa,0xcccc,0xf0f0,0xffa8] 3 (packWords [0xa,0x10a11840c20610,0x611420c4062062,0x1211420c00c00c,0x21480a80a88010,0xc20680688000c4]) [(40,2),(40,12)]
def stateEntry45 : Entry := row 4 [0x2aa,0xcccc,0xf0f0,0xff00] 3 (packWords [0xa,0x11211840a10611,0x21142061062120,0x1210620610a10c,0x20610620a00a10,0x620600600610a4]) []
def stateEntry46 : Entry := row 4 [0xa8a8,0xaaaa,0xcccc,0xf0f0,0xff00] 4 (packWords [0xc212118,0x40c20c41211420,0xc4120120121142,0x8051218041210c,0xc00c21481280,0xc28030c20a10a1,0x8020c21280c480,0x10c40610618000,0xc4062000000000]) [(31,18),(41,4),(31,8),(41,3),(44,3),(45,14)]
def stateEntry47 : Entry := row 4 [0xaaa8,0xcccc,0xf0f0,0xff00] 3 (packWords [0xc,0x21421840c20c41,0x401420c4062120,0x1280620c00c00c,0x21480620a00a40,0x620600600620a4]) []
def stateEntry48 : Entry := row 4 [0xfe,0xaaaa,0xcccc,0xf0f0] 3 (packWords [0x6,0x10a10c20610620,0xa40a10620a1180,0xa112106106206,0x10a40611400611,0x21062120062120]) []
def stateEntry49 : Entry := row 4 [0xaaaa,0xcccc,0xf0f0,0xfefe,0xff00] 4 (packWords [0x12180112,0x18000a11211840,0xa1061121142061,0x6214212106218,0x80000000001480,0x128000,0x610a10c,0x20610620a40a10,0x620610620610a4]) [(47,5),(48,3)]
def stateEntry50 : Entry := row 4 [0xee,0xaaaa,0xcccc,0xf0f0,0xff00] 4 (packWords [0xa118018,0x40a10611401480,0x61062120128062,0x12100006,0x10a10c20610620,0xc20a10620a1188,0xa118806106206,0x11280610c40611,0x480620a4062128]) []
def stateEntry51 : Entry := row 4 [0xa,0xaaaa,0xcccc,0xf0f0,0xff00] 4 (packWords [0xc214218,0x40c20611401420,0x610a41201280a4,0x12100006,0x10c00c20610a00,0xa00a40c2000000,0xa10000610c406,0x10a40610c40610,0xc4062000000000]) []
def stateEntry52 : Entry := row 4 [0xaaaa,0xcccc,0xeeee,0xf0f0,0xff00] 5 (packWords [0x1840a10a11,0x21188121184188,0x1841210a10a112,0x18161211848151,0x84121814121184,0x81318414206106,0x11218121211428,0x11142121061061,0x12106206214281,0x14212180f1211,0x420620620a180e,0xa118880d1880a,0x180c0a118880b1,0x880c20610610a1,0x80a0a10c28090c,0x20a10610610a10,0x620620c28080c2,0xa18070a10c206,0x20628068030c40,0x0,0x80,0x58040a40000000,0x0,0x6180406,0x18030620620000,0x802801800]) [(16,3),(19,7),(19,3),(38,9),(38,15),(0,15),(0,9),(42,19),(43,8),(42,18),(43,17),(46,6),(49,3),(50,8),(51,2),(42,20),(43,3),(42,21),(43,7),(46,5),(49,5),(50,3),(51,1)]
def stateEntry53 : Entry := row 4 [0x8888,0xaaaa,0xcccc,0xf0f0,0xff00] 4 (packWords [0xa112118,0x40a10c41211420,0xc40a41201210a4,0x8041218031210c,0xa10c20a10a00,0xa00a10c28020a1,0x8010a10a40c480,0x610000000,0x62000000000]) [(4,3),(31,8),(20,2),(31,3),(20,1)]
def stateEntry54 : Entry := row 4 [0xaaaa,0xaaee,0xcccc,0xf0f0,0xff00] 4 (packWords [0xa112118,0x40a10611211480,0x61121184121142,0x6216212106206,0x10a10c20610a11,0x880a11880620c2,0xa10620610c406,0x11480610620611,0x480a4000000000]) []
def stateEntry55 : Entry := row 4 [0x88aa,0xaaaa,0xcccc,0xf0f0,0xff00] 4 (packWords [0xa114218,0x40a10611401420,0x61120120128142,0x80014212112106,0x10a10c20610a10,0xc20a10c20a10c2,0xa10c20610c406,0x10c40610c40610,0xc4062000000000]) [(20,1)]
def stateEntry56 : Entry := row 4 [0xaa,0xa0a,0xcccc,0xf0f0,0xff00] 4 (packWords [0xc214218,0x40c20611401420,0x61120120128142,0x12100006,0x10c00c20610000,0xa10000a00a0,0xa40c20610c406,0x10c40610c40610,0xa40620628000a4]) [(20,3)]
def stateEntry57 : Entry := row 4 [0xaaaa,0xcccc,0xeeee,0xf0f0,0xff00] 4 (packWords [0xa112118,0x40a11211841211,0x84061121142061,0x621421210620a,0x11880a11880610,0xa10c20610620c2,0xa10620c400000,0xa40000000,0x61062000800]) [(4,3)]
def stateEntry58 : Entry := row 4 [0xaa,0x5500,0xaaaa,0xcccc,0xf0f0] 4 (packWords [0x610a10c,0x20610a10c20a10,0xc21420a11840a1,0xa10c20a10c206,0x10c40610c41400,0x611420610610c4,0x610c400000012,0x80000620000000,0x800000]) [(17,22)]
def stateEntry59 : Entry := row 4 [0xaa,0xaaaa,0xcccc,0xf0f0,0xff00] 5 (packWords [0x1840a10a11,0x42188142184188,0x1841420a10a114,0x20610611841481,0x40142148142184,0x6106181181012,0x80f1,0x28128142801142,0x0,0x80f80e1210,0xc2061,0x610a10c40a10c,0x20c40c20a10610,0x610a11280a10c2,0x80d0c20a180c0a,0x10c21280c20a18,0xb0a10c280a0c2,0xa18090a10c280,0x80c20611280610,0xc48070c4061806,0x610c41280c406,0x18050610c48040,0xc40618030610c4,0x8020c480180006,0x20000000000000,0x0]) [(53,5),(5,3),(32,3),(54,7),(51,4),(55,15),(43,3),(56,4),(32,6),(54,6),(51,3),(55,23),(43,4),(56,3),(57,5),(38,3),(58,14),(58,3)]
def stateEntry60 : Entry := row 4 [0xaaaa,0xcccc,0xf0f0,0xff00] 6 (packWords [0x8171840a,0x10a18161211881,0x21815184188184,0x8141210a10a181,0x31420610618121,0x21148121811142,0x14814281012106,0x106180f1210620,0x6280e142128120,0x80d12112812180,0xc14206206280b0,0xc206106180a0a1,0xc40a18090c20c,0x40c28080a10610,0x618070a1062062,0x8060c20a40a080,0x50a10a40a18040,0xc2062062803061,0xa40608020c406,0x20608010610620,0x618000c40a40a4]) [(37,3),(52,3),(59,9),(59,15),(37,6),(52,6),(59,11),(59,23),(37,22),(52,22),(59,12),(59,2),(37,5),(52,5),(59,3),(59,14),(37,16),(52,16),(59,7),(59,1),(37,1),(52,1),(59,6),(59,5)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def ds : Array Entry := #[stateEntry0,stateEntry1,stateEntry2,stateEntry3,stateEntry4,stateEntry5,stateEntry6,stateEntry7,stateEntry8,stateEntry9,stateEntry10,stateEntry11,stateEntry12,stateEntry13,stateEntry14,stateEntry15,stateEntry16,stateEntry17,stateEntry18,stateEntry19,stateEntry20,stateEntry21,stateEntry22,stateEntry23,stateEntry24,stateEntry25,stateEntry26,stateEntry27,stateEntry28,stateEntry29,stateEntry30,stateEntry31,stateEntry32,stateEntry33,stateEntry34,stateEntry35,stateEntry36,stateEntry37,stateEntry38,stateEntry39,stateEntry40,stateEntry41,stateEntry42,stateEntry43,stateEntry44,stateEntry45,stateEntry46,stateEntry47,stateEntry48,stateEntry49,stateEntry50,stateEntry51,stateEntry52,stateEntry53,stateEntry54,stateEntry55,stateEntry56,stateEntry57,stateEntry58,stateEntry59,stateEntry60]
def states (i : Nat) := ds[i]?.getD default
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def ms : Array (List (Fin 4)) := #[[1,0],[0,1,2,0,1],[1,2,0,1],[],[1],[0,1,2],[0,1],[0],[2],[1,2,1],[2,1],[1,2],[1,2,0],[2,1,0],[0,1,2,0,1,0],[1,2,1,0],[0,1,2,0],[2,0],[2,0,1],[2,0,1,0],[0,1,2,1,0],[0,1,2,1],[0,1,0],[1,2,0,1,0]]
def perm (i : Nat) := permitted (ms[i]?.getD [])
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def specTab : Array Spec := #[]
def spec (i : Nat) := specTab[i]?.getD (0,[])
def checked (i : Nat) := nodeOK target root mins spec states perm i
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block0 : Good checked 0 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block1 : Good checked 4 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block2 : Good checked 8 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block3 : Good checked 12 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block4 : Good checked 16 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block5 : Good checked 20 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block6 : Good checked 24 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block7 : Good checked 28 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block8 : Good checked 32 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block9 : Good checked 36 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block10 : Good checked 40 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block11 : Good checked 44 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block12 : Good checked 48 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block13 : Good checked 52 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block14 : Good checked 56 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block15 : Good checked 60 1 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem total : Good checked 0 61 := (concatGood (concatGood (concatGood (concatGood block0 block1) (concatGood block2 block3)) (concatGood (concatGood block4 block5) (concatGood block6 block7))) (concatGood (concatGood (concatGood block8 block9) (concatGood block10 block11)) (concatGood (concatGood block12 block13) (concatGood block14 block15))))
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem impossible : Impossible true target 6 root.toFinset := by
  have h := certified (states:=states) (perm:=perm) (specs:=spec) (N:=61) (fun j => perm_onto _) pri (fun i hi => total i (by omega) hi) 60 (by decide)
  exact h
def essentials : List (Sig × Row × Row) := [(root.getD 0 zero,2,3),(root.getD 1 zero,1,3),(root.getD 2 zero,1,5),(root.getD 3 zero,1,9)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lower : Lower true root target 7 := by
  apply lower_impossible (L:=6) (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro a ha
    apply essential_ok (xs:=essentials) (by decide +kernel) a
    exact (show (essentials.map Prod.fst).toFinset = root.toFinset by decide +kernel).symm ▸ List.mem_toFinset.mpr ha
  · exact impossible
end Tabfee8

namespace Tabe8c0
open PEqualNP.Outside.L_meta_12126.Core GateForest12127 CertBlocks12127 Bound12127
def root := inputs.take 4
def target := stamp 4 0xe8c0
def mins : List (Sig × Nat) := []
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pri : ∀ m ∈ mins, Slice true root target m.1 m.2 := by simp [mins]
def stateEntry0 : Entry := row 4 [0xaa00,0xcccc,0xf0f0] 3 (packWords [0xc21690c01,0xa90c40c00c20c4,0xc21a91691691a,0x91621620c21a40,0xc21a91a41a40c2,0x1620c21691a416,0xc41620c41691,0x621620c41a40c4]) []
def stateEntry1 : Entry := row 4 [0xaa00,0xcccc,0xf0f0,0xff00] 3 (packWords [0xc,0x21a90ca0c20c41,0x690cc0c4162000,0xc00c00c,0x216916a0c21a90,0xc21680c41690c4]) []
def stateEntry2 : Entry := row 4 [0xaa00,0xaaaa,0xcccc,0xf0f0] 3 (packWords [0xc,0xc00c21690e20,0xc20c30c21630c2,0x1a50c20e40c40c,0x50c41610c41630,0xc4162000000000]) []
def stateEntry3 : Entry := row 4 [0xaa00,0xcccc,0xf0f0] 2 (packWords [0xc00c00c,0x21691620c21a40,0xc21600c41620c4]) []
def stateEntry4 : Entry := row 4 [0xaa,0xaaaa,0xcccc,0xf0f0] 3 (packWords [0xc,0xc00c21690e30,0xc20e30c20e30c2,0xe30c20e50c40e,0x50c40e50c40e50,0xc4800000000000]) [(3,0)]
def stateEntry5 : Entry := row 4 [0x5500,0xcccc,0xf0f0,0xff00] 3 (packWords [0xc,0x21621a40c20c41,0x601620c4800000,0xc00c00c,0x216916a0c21a80,0xc21ac0c41680c4]) [(3,0)]
def stateEntry6 : Entry := row 4 [0xaaaa,0xcccc,0xf0f0,0xff00] 4 (packWords [0x1a50c2,0xc21631a91631a,0x51a90ca1630c20,0xc21630c40c41a5,0x1691611631690c,0xc1a50c40c41638,0x416280316a162,0x16316a16380280,0x18000c21690c01,0xa90c40c00c20c4,0xc21a91691690e,0x316a0e20c21ac0,0xc20e31ac0c30c2,0x16a0c20e51ac0e,0x40c416a0c40e51,0x6a0c50c41ac0c4]) [(0,0),(1,0),(2,0),(4,0),(5,0)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def ds : Array Entry := #[stateEntry0,stateEntry1,stateEntry2,stateEntry3,stateEntry4,stateEntry5,stateEntry6]
def states (i : Nat) := ds[i]?.getD default
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def ms : Array (List (Fin 4)) := #[[]]
def perm (i : Nat) := permitted (ms[i]?.getD [])
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def specTab : Array Spec := #[]
def spec (i : Nat) := specTab[i]?.getD (0,[])
def checked (i : Nat) := nodeOK target root mins spec states perm i
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block0 : Good checked 0 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block1 : Good checked 4 3 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem total : Good checked 0 7 := (concatGood block0 block1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem impossible : Impossible true target 4 root.toFinset := by
  have h := certified (states:=states) (perm:=perm) (specs:=spec) (N:=7) (fun j => perm_onto _) pri (fun i hi => total i (by omega) hi) 6 (by decide)
  exact h
def essentials : List (Sig × Row × Row) := [(root.getD 0 zero,10,11),(root.getD 1 zero,4,6),(root.getD 2 zero,2,6),(root.getD 3 zero,3,11)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lower : Lower true root target 5 := by
  apply lower_impossible (L:=4) (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro a ha
    apply essential_ok (xs:=essentials) (by decide +kernel) a
    exact (show (essentials.map Prod.fst).toFinset = root.toFinset by decide +kernel).symm ▸ List.mem_toFinset.mpr ha
  · exact impossible
end Tabe8c0

namespace Tabf880
open PEqualNP.Outside.L_meta_12126.Core GateForest12127 CertBlocks12127 Bound12127
def root := inputs.take 4
def target := stamp 4 0xf880
def mins : List (Sig × Nat) := []
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pri : ∀ m ∈ mins, Slice true root target m.1 m.2 := by simp [mins]
def stateEntry0 : Entry := row 4 [0x8888,0xf0f0,0xff00] 3 (packWords [0x1840e30e31,0x63188163184188,0x1841630e30e316,0x30e40e41841681,0x60163168163184,0xe40e40e31680e,0x1880e40e00e30,0xe40e3188168168]) []
def stateEntry1 : Entry := row 4 [0x8888,0xaaaa,0xf0f0,0xff00] 3 (packWords [0xe,0x31631840e31631,0x841631840e5161,0x1630e50e31880e,0x31880e10e10e31,0x690e4000000000]) []
def stateEntry2 : Entry := row 4 [0x8888,0xf0f0,0xff00] 2 (packWords [0xe316318,0x40e30e41601630,0xe40e00e00e3168]) []
def stateEntry3 : Entry := row 4 [0x2222,0xaaaa,0xf0f0,0xff00] 3 (packWords [0xe,0x31631840e30e41,0x601630e40e5163,0x1610e50e00e00e,0x31681690e30e10,0xe1800000000000]) [(2,0)]
def stateEntry4 : Entry := row 4 [0xaaaa,0xcccc,0xf0f0,0xff00] 4 (packWords [0x1840e3,0xe316318816318,0x41881841630e30,0xe31630e50e5184,0x16916116316916,0x31840e50e51630,0xe60e618416a162,0x16316a1631840e,0x60e60e31690e11,0x880e50e10e30e5,0xe31881691690e,0x316a0e21880e60,0xe20e30e60e3188,0x16a16a0e58040e,0x48030e60e40e50,0xe60e5802801800]) [(0,0),(1,1),(1,0),(3,0),(3,1)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def ds : Array Entry := #[stateEntry0,stateEntry1,stateEntry2,stateEntry3,stateEntry4]
def states (i : Nat) := ds[i]?.getD default
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def ms : Array (List (Fin 4)) := #[[],[0]]
def perm (i : Nat) := permitted (ms[i]?.getD [])
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def specTab : Array Spec := #[]
def spec (i : Nat) := specTab[i]?.getD (0,[])
def checked (i : Nat) := nodeOK target root mins spec states perm i
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block0 : Good checked 0 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block1 : Good checked 4 1 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem total : Good checked 0 5 := (concatGood block0 block1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem impossible : Impossible true target 4 root.toFinset := by
  have h := certified (states:=states) (perm:=perm) (specs:=spec) (N:=5) (fun j => perm_onto _) pri (fun i hi => total i (by omega) hi) 4 (by decide)
  exact h
def essentials : List (Sig × Row × Row) := [(root.getD 0 zero,6,7),(root.getD 1 zero,5,7),(root.getD 2 zero,3,7),(root.getD 3 zero,3,11)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lower : Lower true root target 5 := by
  apply lower_impossible (L:=4) (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro a ha
    apply essential_ok (xs:=essentials) (by decide +kernel) a
    exact (show (essentials.map Prod.fst).toFinset = root.toFinset by decide +kernel).symm ▸ List.mem_toFinset.mpr ha
  · exact impossible
end Tabf880

namespace Tabfef8
open PEqualNP.Outside.L_meta_12126.Core GateForest12127 CertBlocks12127 Bound12127
def root := inputs.take 4
def target := stamp 4 0xfef8
def mins : List (Sig × Nat) := []
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pri : ∀ m ∈ mins, Slice true root target m.1 m.2 := by simp [mins]
def stateEntry0 : Entry := row 4 [0xfafa,0xfcfc,0xff00] 2 (packWords [0x6112114,0x20610621201210,0x62060060061128]) []
def stateEntry1 : Entry := row 4 [0xaaaa,0xfcfc,0xfff0] 2 (packWords [0x6108008,0x20610620821210,0x62060060061088]) []
def stateEntry2 : Entry := row 4 [0xaaaa,0xf0f0,0xfcfc,0xff00] 3 (packWords [0x6,0x11211420610821,0x21801082062120,0x12106208000000,0x600600611,0x28062082800062]) [(0,0),(1,0)]
def stateEntry3 : Entry := row 4 [0xa0a,0xcccc,0xf0f0,0xff00] 3 (packWords [0x8,0x1210880800611,0x21142061062120,0x12106206108008,0x20610000000810,0x60060061128]) []
def stateEntry4 : Entry := row 4 [0xaaaa,0xcccc,0xf0f0,0xfff0] 3 (packWords [0x8,0x611,0x21142061062120,0x12106206108880,0x10610620888000,0x62060060061128]) [(1,1),(1,0)]
def stateEntry5 : Entry := row 4 [0xf00,0xaaaa,0xcccc,0xf0f0] 3 (packWords [0x6,0x10800820610620,0x80081062000000,0x8800006006006,0x11281210611420,0x61120062121062]) []
def stateEntry6 : Entry := row 4 [0xaaaa,0xcccc,0xf0f0,0xff00] 4 (packWords [0x805080,0x8012118812180,0x41880881210800,0x80142061061121,0x14812114214814,0x21210610611210,0x62062142128120,0x12112812114206,0x20620c20610610,0x808030800c2802,0x820800610610a,0x10620620808010,0x800a1800081080,0x6206206112806,0x1480620600610,0x62061148128128]) [(2,1),(3,0),(2,0),(3,1),(4,0),(5,0)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def ds : Array Entry := #[stateEntry0,stateEntry1,stateEntry2,stateEntry3,stateEntry4,stateEntry5,stateEntry6]
def states (i : Nat) := ds[i]?.getD default
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def ms : Array (List (Fin 4)) := #[[],[0]]
def perm (i : Nat) := permitted (ms[i]?.getD [])
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def specTab : Array Spec := #[]
def spec (i : Nat) := specTab[i]?.getD (0,[])
def checked (i : Nat) := nodeOK target root mins spec states perm i
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block0 : Good checked 0 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block1 : Good checked 4 3 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem total : Good checked 0 7 := (concatGood block0 block1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem impossible : Impossible true target 4 root.toFinset := by
  have h := certified (states:=states) (perm:=perm) (specs:=spec) (N:=7) (fun j => perm_onto _) pri (fun i hi => total i (by omega) hi) 6 (by decide)
  exact h
def essentials : List (Sig × Row × Row) := [(root.getD 0 zero,2,3),(root.getD 1 zero,1,3),(root.getD 2 zero,0,4),(root.getD 3 zero,1,9)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lower : Lower true root target 5 := by
  apply lower_impossible (L:=4) (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro a ha
    apply essential_ok (xs:=essentials) (by decide +kernel) a
    exact (show (essentials.map Prod.fst).toFinset = root.toFinset by decide +kernel).symm ▸ List.mem_toFinset.mpr ha
  · exact impossible
end Tabfef8

namespace Tab8000
open PEqualNP.Outside.L_meta_12126.Core GateForest12127 CertBlocks12127 Bound12127
def root := inputs.take 4
def target := stamp 4 0x8000
def mins : List (Sig × Nat) := []
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pri : ∀ m ∈ mins, Slice true root target m.1 m.2 := by simp [mins]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def ds : Array Entry := #[]
def states (i : Nat) := ds[i]?.getD default
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def ms : Array (List (Fin 4)) := #[]
def perm (i : Nat) := permitted (ms[i]?.getD [])
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def specTab : Array Spec := #[]
def spec (i : Nat) := specTab[i]?.getD (0,[])
def checked (i : Nat) := nodeOK target root mins spec states perm i
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem impossible : Impossible true target 2 root.toFinset := size_sound (by decide +kernel) (by decide +kernel)
def essentials : List (Sig × Row × Row) := [(root.getD 0 zero,14,15),(root.getD 1 zero,13,15),(root.getD 2 zero,11,15),(root.getD 3 zero,7,15)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lower : Lower true root target 3 := by
  apply lower_impossible (L:=2) (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro a ha
    apply essential_ok (xs:=essentials) (by decide +kernel) a
    exact (show (essentials.map Prod.fst).toFinset = root.toFinset by decide +kernel).symm ▸ List.mem_toFinset.mpr ha
  · exact impossible
end Tab8000

namespace Four12127
open PEqualNP.Outside.L_meta_12126.Core
abbrev love880 := Tabe880.lower
abbrev lovfee8 := Tabfee8.lower
end Four12127

namespace Tab0
open PEqualNP.Outside.L_meta_12126.Core GateForest12127 CertBlocks12127 Bound12127
def root := inputs.take 5
def target := stamp 5 0xfee8f880
def sd0 : Sig := ~~~raw 0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sl0 : Slice true root target sd0 5 :=
  slice_correct (ms:=[forceLow 4,swapNext 3,swapNext 2,swapNext 1,swapNext 0]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) Tabe8c0.lower
def sd1 : Sig := raw 0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sl1 : Slice true root target sd1 7 :=
  slice_correct (ms:=[forceHigh 4,swapNext 3,swapNext 2,swapNext 1,swapNext 0]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) Tabfee8.lower
def sd2 : Sig := ~~~raw 1
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sl2 : Slice true root target sd2 5 :=
  slice_correct (ms:=[forceLow 4,swapNext 3,swapNext 2,swapNext 1]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) Tabe8c0.lower
def sd3 : Sig := raw 1
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sl3 : Slice true root target sd3 7 :=
  slice_correct (ms:=[forceHigh 4,swapNext 3,swapNext 2,swapNext 1]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) Tabfee8.lower
def sd4 : Sig := ~~~raw 2
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sl4 : Slice true root target sd4 7 :=
  slice_correct (ms:=[forceLow 4,swapNext 3,swapNext 2]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) Tabe880.lower
def sd5 : Sig := raw 2
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sl5 : Slice true root target sd5 5 :=
  slice_correct (ms:=[forceHigh 4,swapNext 3,swapNext 2]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) Tabfef8.lower
def sd6 : Sig := ~~~raw 3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sl6 : Slice true root target sd6 7 :=
  slice_correct (ms:=[forceLow 4,swapNext 3]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) Tabe880.lower
def sd7 : Sig := raw 3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sl7 : Slice true root target sd7 5 :=
  slice_correct (ms:=[forceHigh 4,swapNext 3]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) Tabfef8.lower
def sd8 : Sig := ~~~raw 4
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sl8 : Slice true root target sd8 5 :=
  slice_correct (ms:=[forceLow 4]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) Tabf880.lower
def sd9 : Sig := raw 4
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sl9 : Slice true root target sd9 7 :=
  slice_correct (ms:=[forceHigh 4]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) Tabfee8.lower
def mins : List (Sig × Nat) := [(sd0,5),(sd1,7),(sd2,5),(sd3,7),(sd4,7),(sd5,5),(sd6,7),(sd7,5),(sd8,5),(sd9,7)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pri : ∀ m ∈ mins, Slice true root target m.1 m.2 := by
  intro m hm
  simp only [mins,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact sl0
  · exact sl1
  · exact sl2
  · exact sl3
  · exact sl4
  · exact sl5
  · exact sl6
  · exact sl7
  · exact sl8
  · exact sl9
def stateEntry0 : Entry := row 5 [0xaaaaaaaa,0xcccccccc,0xf080ff88,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (packWords [0x1632a5331163,0xe32a12a50e340,0x2a52632631692,0x6127116916a262,0x27216a0e316318,0x80e31631841633,0x31163169163271,0x16316a1632720e,0x32b10e32b10e31,0x880e31690e3188,0xe316a0e50e516,0x92710e60e616a2,0x721681681692b4]) []
def stateEntry1 : Entry := row 5 [0xff0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xf8f8f8f8,0xff00ff00,0xffff0000] 6 (packWords [0x32132916340,0x73294063290e33,0x294050e30e52d4,0x2d40e50e62b42b,0x40e62630000000,0x163403163404,0xe31631840e30e,0x51841630e50e61,0x841630e6000000,0x33100018800000,0x1690e50e53,0x5816a0e60e6338,0x8004014014030e,0x30e50e33580e30,0xe60e33384020e3,0x4010e30e40e40e,0x52b42d40e52d40,0xe52b40e62b40e6]) [(0,0)]
def stateEntry2 : Entry := row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xf8f8f8f8,0xff00ff00,0xffff0000] 7 (packWords [0x800329,0x16316340e26333,0x12634053293311,0x9440e263163163,0x40126340126340,0x53294063294052,0x63406263401329,0x40f3294022a50e,0x30e34022634022,0x634022a54052a5,0x4022630e30e340,0x92630e50e54092,0xa52d42a5409263,0x2d42634092a50e,0x50e54082630e60,0xe64082c62b42a4,0x4082632b426340,0x82c60e60e640e1,0x63404163401331,0x40333140116340,0x116340e3314043,0x314021840e30e3,0x40216340216340,0x21844011844021,0x630e30e3409163,0xe50e540918435,0x81844091633581,0x634091840e50e5,0x4081630e60e640,0x81843381844081,0x63338163408184,0xe60e640240d40,0xc1880000000000,0x0,0x40,0x940b3581694084,0xa0e50e5408408,0xe50e540840a35,0x835840840a3381,0x6a4084080e60e6,0x40840a0e60e640,0x84083383384090,0xe33580e3409409,0xe50e54080e30e,0x50e34094093583,0x584080e33380e3,0x4084080e60e640,0x80e30e60e34084,0x83383384080e5,0x2b40e44082d40e,0x60e44080e50e60,0xe54082d42b42b4]) [(1,1)]
def stateEntry3 : Entry := row 5 [0xeeee0000,0xf888f888,0xfff0fff0] 2 (packWords [0xe00e00e,0x32712630e32a40,0xe32600e42630e4]) []
def stateEntry4 : Entry := row 5 [0xeeee0000,0xf8f8f8f8,0xff88ff88,0xfff0fff0] 3 (packWords [0xe,0x30e40e34100e30,0xe80e34102630e3,0x2a40e30e40e80e,0x48002a40e42630,0xe42e80e82630e8]) [(3,1)]
def stateEntry5 : Entry := row 5 [0xeeeeeeee,0xf8f8f8f8,0xff88ff88,0xfff0fff0,0xffff0000] 4 (packWords [0xe32632a,0x50e30e52a51940,0xe50e92e91980e9,0x2632a42638000e,0x30e50e34110e30,0xe90e34120e32b4,0xe31830e50e90e,0x54110e40e40e51,0x840e80e80e9188]) [(4,1)]
def stateEntry6 : Entry := row 5 [0xaaaaaaaa,0xcccccccc,0xf8f8f8f8,0xff88ff88,0xfff0fff0,0xffff0000] 5 (packWords [0xe32632a50e3,0x1842a519418418,0x83291981882632,0xa52632a52632a4,0x2632c60e31840e,0x34020e31880e34,0x130e32d40e31a3,0xe32b40e31c318,0x41881844020e50,0xe51861840e60e6,0x1851840e90e918,0xa1880ea0ea1891,0x882b42d48002b4]) [(5,1)]
def stateEntry7 : Entry := row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xf8f8f8f8,0xff00ff00,0xff88ff88,0xffff0000] 6 (packWords [0x2632a52632a516,0x32633291632633,0x292633290e3263,0x2a50e32632a526,0x32a52632a42632,0xc6184000000000,0x41841741641540,0x10e30e34020e50,0xe53582d40e60e6,0x3382b416340316,0x34130e31638000,0xe31633581632d4,0x1633381632b418,0x80000000001691,0x692d435816a16a,0x2b43380e32d40e,0x33580e32b40e33,0x382b42d44142b4]) [(6,1)]
def stateEntry8 : Entry := row 5 [0x88888888,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff88ff88,0xfff0fff0,0xffff0000] 6 (packWords [0x1632632a516318,0x42a51941841882,0x631981882632a5,0x2632a52632a426,0x32c62632a52632,0xa516318416341d,0xe300000000016,0x32d416341c1632,0xb416340c16340c,0x16340c18418818,0x44021c41841861,0x841a4184185184,0x41b0000000001c,0x818818a1881a81,0x8818918841a188,0x8001882b42d441,0x90001690000000,0x16a000000000]) [(6,1)]
def stateEntry9 : Entry := row 5 [0x88888888,0xeeeeeeee,0xf0f0f0f0,0xff00ff00,0xfff80000] 4 (packWords [0x16326319,0x41630e32631980,0xe32632a426341e,0xe52612630e50e,0x31631840e31631,0x841631840e5161,0x1630e50e31880e,0x31880e10e10e31,0x690e4000000000]) []
def stateEntry10 : Entry := row 5 [0x88888888,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xfff80000] 5 (packWords [0x163263194163,0xe32631980e326,0x32a52632a52632,0xa42632c62632a5,0x2632a50e316318,0x40e31631841631,0x84163184163184,0x1631841631840e,0x31880e31880e31,0x880e31880e3188,0xe31882b42d480,0xe50000000,0xe6000000000]) [(9,1)]
def stateEntry11 : Entry := row 5 [0x88888888,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xfff8fff8,0xffff0000] 6 (packWords [0x26342126380016,0x32631941630e32,0x631980e32632a5,0x2632a52632a426,0x32c62632a52632,0xa5331000000000,0x2b100000000041,0xf2d42d440a40a2,0xb42b442041f000,0xe316318,0x40e31631841631,0x84163184163184,0x1631841631840e,0x31880e31880e31,0x880e31880e3188,0xe31882b42d441,0x60000e50000000,0xe6000000000]) [(10,1)]
def stateEntry12 : Entry := row 5 [0xf800f8,0x88888888,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x3212633292630e,0x32631980e32632,0xa52632a52632a4,0x2632c62632a526,0x32a52633292633,0x290e31801880e3,0x2d43313522d42b,0x43303312b440e3,0x31403331000000,0x1630000e31880e,0x31880e31880e31,0x880e31880e3188,0xe31880e31882b,0x42d44250000e50,0x2d4358,0x2d43580e600000,0x2b43382b43,0x38424417423422]) []
def stateEntry13 : Entry := row 5 [0x77770000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xf8f8f8f8,0xff00ff00,0xffff0000] 6 (packWords [0x16326333116326,0x342126340f0e32,0x634050e30e52d4,0x2630e50e62b426,0x30e62a50000000,0x163331163331,0xe31631840e30e,0x51841630e50e61,0x841630e6331163,0x33116318800000,0x1690e50e53,0x5816a0e60e6338,0x4294284274260e,0x30e50e33580e30,0xe60e33384020e3,0x4010e30e40e40e,0x52b42d40e52d40,0xe52b40e62b40e6]) []
def stateEntry14 : Entry := row 5 [0x88888888,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xf8f80000,0xff00ff00,0xffff0000] 6 (packWords [0x16332132916326,0x30000000000e33,0x291980e33482d4,0x2d43293282b42b,0x434a40f3294053,0x29394163394163,0xe31631840e316,0x31841631841631,0x84163184163184,0x1631840e32b142,0xe0e33582d42d43,0x583382b42b4338,0x42642d42c42b0e,0x31880e31880e31,0x880e31880e3188,0xe31882b42d442,0xa0000e50000000,0xe6000000000]) []
def stateEntry15 : Entry := row 5 [0x770000,0x88888888,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x1632633291630e,0x32631980e32632,0xd42633292632b4,0x26334a26332926,0x33292a50000000,0xe31631840e3,0x16318416318416,0x31841631841631,0x84163184000000,0x3310000e31880e,0x31880e31880e31,0x880e31880e3188,0x2b10e32b10e32b,0x42d44300000e50,0x2d4358,0x2d43580e600000,0x2b43382b43,0x3800000042f000]) []
def stateEntry16 : Entry := row 5 [0x88888888,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xf8f8f8f8,0xff00ff00,0xffff0000] 7 (packWords [0x32916316326333,0x12633293311942,0x63163163263806,0x26332942132926,0x34212633298053,0x292a50e30e3263,0x4022632a54052a,0x52630e30e32634,0x92632a52d42a5,0x2632d42632a541,0xc2a52634082632,0xc62b42a42632b4,0x2632c640c2c626,0x38042632a54052,0xa52634052632a5,0x40c2a516341316,0x33318033311638,0x2163331413331,0x1840e30e316340,0x21631848011841,0x630e30e31632d4,0x16318435818416,0x33581631842d41,0x841632b4163184,0x33818416333816,0x31842b41841634,0xe16318440c184,0x16380016318440,0xe18440d40c1880,0x0,0x40,0xb35835840a2d42,0xd44082d42d440a,0x35835840a33833,0x84082b42b440a2,0xb42b4408338338,0x40b40240b00000,0x0,0xe3358,0xe34092d42d40e,0x32d40e34093583,0x580e33380e3408,0x2b42b40e32b40e,0x34083383380e34,0x20e340c40240c,0x40240,0x24024082b42b42,0xd44092d4408408,0x40800000000040,0x84080e50000000,0x0,0x4094080e,0x60000000000000,0x0]) [(7,1),(8,0),(11,1),(12,1),(13,1),(14,1),(15,0)]
def stateEntry17 : Entry := row 5 [0x8ff0808,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (packWords [0x163263329163,0x1882631981880e,0x52712630e50e62,0x722630e62632a5,0x26332918016318,0x41630e51841630,0xe50e61841630e6,0x1631841631840e,0x10e10e51880e20,0xe20e61882b1188,0xe30e30e40e40e,0x52b41690e52710,0xe516a0e62720e6]) []
def stateEntry18 : Entry := row 5 [0x880088,0xf0f0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x1842a519418400,0x2a12a50e31692,0xa52c616916a2a4,0x2a516a26300000,0x40f2a54062,0xa50e31801840e3,0x16116116918416,0x216216a1843311,0x84331184000000,0x1630000e31880e,0x31690e31880e31,0x6a0000002b1000,0xe31880e318816,0x81681692b43581,0x693581690e5000,0x33816a33,0x816a0e60000000,0x40140c80040c]) [(17,0)]
def stateEntry19 : Entry := row 5 [0x880088,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 7 (packWords [0x413329,0x18418441326333,0x12634133293311,0x94413263184184,0x8002a50e30e343,0x22632b12634342,0xa52b1198432263,0xe30e343126316,0x91694312a52d42,0xa54312632d4263,0x4312a516916942,0x226316a16a4222,0xc62b42a4422263,0x2b42634222c616,0xa16a40c26340f2,0x634342a54062a5,0x43426340626340,0xc2a540c2a54131,0x840e30e3432331,0x18818041318418,0x81844323310e30,0xe34311c62d4161,0x42218416916143,0x11c61691694311,0x842d41844221a5,0x2b416242218416,0xa1624221a516a1,0x6a4221842b4184,0x0,0x4134,0xc433163000000,0x4310e316,0x90e34311882d41,0x884310e32d40e3,0x43118816916942,0x20e316a0e34221,0x882b41884220e3,0x2b40e342218816,0xa16a4320e34000,0xe340c18840c188,0x40c0e34010e343,0x21884001884221,0x692b41684222d4,0x16a16842216916,0xa1694222d42b42,0xb443140c4240e5,0x0,0x0,0x42240c,0x4220e600000000,0x0,0x0]) [(18,1)]
def stateEntry20 : Entry := row 5 [0x777f0000,0xaaaaaaaa,0xcccccccc,0xf000f000,0xfff0fff0] 4 (packWords [0x18000000,0xe10e10e32,0x710e20e20e3272,0x2630e32a50e30e,0x51841860e50e61,0x841850e6263184,0x1941840e40e40e,0x52b42610e52630,0xe52620e62630e6]) []
def stateEntry21 : Entry := row 5 [0x777f0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xfff0fff0] 5 (packWords [0x163000000000,0xe300000000027,0x10e50e52712720,0xe60e62722632a5,0x2a526318418800,0x8000e51691690,0xe50e616a16a0e6,0x26318419418416,0x90e50e516916a0,0xe60e616a263188,0x1981880e40e40e,0x52b42610e52630,0xe52620e62630e6]) [(20,1)]
def stateEntry22 : Entry := row 5 [0x88808880,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xfff0fff0,0xffff0000] 6 (packWords [0x2a52632a526318,0x42631941841882,0x63198188261261,0x2632a526226226,0x32c68002634372,0x63331000000000,0x2b100000000027,0x12d42d42712722,0xb42b427241f000,0x18418800,0x4361c41841861,0x841a4184185184,0x41b1844001841c,0x818818a1881a81,0x88189188435188,0x40418827027027,0x12b40e50000000,0xe6000000000]) [(21,1)]
def stateEntry23 : Entry := row 5 [0x77707770,0xaaaa0000,0xcccc0000,0xf0f0f0f0,0xff00ff00] 4 (packWords [0xe016018,0x40e02711601721,0x60272160171160,0xe41601680e427,0x10e00f20e02720,0xe00f10e01680e0,0xe40e026026027,0x12a40e42712c40,0xe40e42722a40e4]) []
def stateEntry24 : Entry := row 5 [0x77707770,0xaaaa0000,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (packWords [0x1622c6172162,0xe234a0f20e22c,0x42712718002620,0xe6406,0x2c60e60e216218,0x40e21601601621,0x84272162338162,0xe616216a0e60e,0xe00e21882720,0xe22b40e216a0e2,0xe60e227027027,0x12b42d40e60e40,0xe40e62722b40e6]) [(23,1)]
def stateEntry25 : Entry := row 5 [0x77707770,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x32916316,0x32633942633293,0x94194263163163,0x2a50e30e326339,0x82632a53981982,0x630e30e326343c,0x2612a527126126,0x32712632a58012,0xa526341f2622c6,0x27226226327226,0x32c68002c62a54,0xf2a5263406263,0x2a54062a526340,0xf2631840e30e31,0x63188163184188,0x1841630e30e316,0x32711611843581,0x61163358163184,0x27118416327216,0x21843381621633,0x38163184272184,0x18442418416341,0x716318443b1841,0x6343a1630e3271,0xe11882d40e10e,0x32d40e31882711,0x880e32720e2188,0x2b40e20e32b40e,0x31882721881884,0x391880e34180e3,0x1884381880e340,0xb0e32712b42702,0xd4272270271272,0x2712d42b42b42d,0x440a2d427141f2,0x712d44160e5271,0x40a0e52b441f2b,0x427240a2722b44,0xa0e627241f0e6]) [(24,1),(24,2)]
def stateEntry26 : Entry := row 5 [0x77707770,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xfff0fff0,0xffff0000] 6 (packWords [0x2a52632a526318,0x42631941841882,0x63198188261261,0x2632a526226226,0x32c62a52632a52,0x63163000000000,0xe300000000027,0x12d42d42712722,0xb42b427243e000,0x18418800,0x43d1c41841861,0x841a4184185184,0x18440018441b1c,0x818818a1881a81,0x88189188188404,0x18843527027027,0x12b42d42710e50,0xe52b42720e60e6]) []
def stateEntry27 : Entry := row 5 [0x77707770,0x88888888,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x1632631941630e,0x32631980e32632,0xa52632a52632a4,0x2632c62632a526,0x32a52a52632a52,0x630e31631840e3,0x16318416318416,0x31841631841631,0x84163184184163,0x1841630e31880e,0x31880e31880e31,0x880e31880e3188,0x1880e31880e32b,0x42d441f0002710,0x2d441f,0x2d440a27200000,0x2b440a2b44,0x20000000416000]) []
def stateEntry28 : Entry := row 5 [0x88888888,0xaaa0aaa0,0xccc0ccc0,0xf000f000,0xffff0000] 4 (packWords [0x18026319,0x1802c02632c62,0x632a02632a5263,0x2602602632a51c,0x1801861801a01,0x80185180270180,0x1831800e30e344,0x2b00e50e54402,0x700e60e643f270]) []
def stateEntry29 : Entry := row 5 [0x88888888,0xaaa0aaa0,0xccc0ccc0,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (packWords [0x184263194184,0x1882631981882c,0x42632c62632a42,0x632a5263260260,0x2632a518018018,0x48001c41841861,0x841a4184185184,0x2701842781841c,0x818818a1881a81,0x88189188270188,0x2741882b42d444,0x22b40e50e54422,0x700e60e6441270]) [(28,1)]
def stateEntry30 : Entry := row 5 [0x88888888,0xaaa0aaa0,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xfff0fff0,0xffff0000] 6 (packWords [0x2a52632a526318,0x42631941841882,0x631981882632a5,0x2632a52a42632a,0x52632622622632,0xa5352000000000,0x2d200000000044,0x42d42d480040a0,0x27240c,0x40127218418800,0x4431c41841861,0x841a4184185184,0x2721844031841c,0x818818a1881a81,0x88189188272188,0x4011882b42d444,0x12b40e50000000,0xe60e6441272]) [(29,1)]
def stateEntry31 : Entry := row 5 [0x7770fff0,0xaaaaaaaa,0xcccccccc,0xf000f000,0xffff0000] 4 (packWords [0x18426319,0x41840e52612630,0xe50e62622630e6,0xe32632a50e30e,0x51841860e50e61,0x841850e60e3180,0x1840e30e40e40e,0x52b40e10e10e32,0x710e20e20e3272]) []
def stateEntry32 : Entry := row 5 [0x7770fff0,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (packWords [0x184263194184,0x1882631981880e,0x52612630e50e62,0x622630e62a5263,0x2a526318418818,0x48000e51691690,0xe50e616a16a0e6,0x16316318444616,0x90e50e516916a0,0xe60e616a0e30e3,0x1884450e40e40e,0x52b40e52710e52,0x710e62720e6272]) [(31,1)]
def stateEntry33 : Entry := row 5 [0x88880000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xfff0fff0,0xffff0000] 6 (packWords [0x2a54212a540f18,0x42a51941841883,0x291981880e52a5,0x2c60e50e62a42a,0x50e62630000000,0x163000000000,0xe300000000044,0x80e50e541c42b0,0xe60e640c80040c,0x40140c18418800,0x4470e51691690,0xe50e616a16a0e6,0x40418440318416,0x90e50e516916a0,0xe60e616a400188,0x4011880e40e40e,0x52b42710000000,0x272000000000]) [(32,1)]
def stateEntry34 : Entry := row 5 [0x8880fff0,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (packWords [0x184263331184,0x1882632b11880e,0x52612630e50e62,0x622630e640c263,0x2a526318418818,0x42b10e51691690,0xe50e616a16a0e6,0x16316318433116,0x90e50e516916a0,0xe60e616a0e30e3,0x1882b10e40e40e,0x52b40e52710e52,0x710e62720e6272]) []
def stateEntry35 : Entry := row 5 [0x77770000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xfff0fff0,0xffff0000] 6 (packWords [0x40f26342126318,0x42633941841882,0x633981880e5261,0x2630e50e626226,0x30e62a50000000,0x163000000000,0xe300000000044,0xb0e50e541c44a0,0xe60e640c800401,0x40140f18418800,0x4490e51691690,0xe50e616a16a0e6,0x39418439418416,0x90e50e516916a0,0xe60e616a398188,0x3981880e40e40e,0x52b42d40e52710,0xe52b40e62720e6]) [(34,1)]
def stateEntry36 : Entry := row 5 [0x3330fff0,0x88888888,0xaaaa0000,0xf0f0f0f0,0xff00ff00] 4 (packWords [0x18418818,0x42c02631843281,0x840e41681680e4,0x1631631842c426,0x31882a41881680,0xe40e41680e30e3,0x1882c00e426026,0x30e42a42632a42,0x630e42710e4271]) []
def stateEntry37 : Entry := row 5 [0x3330fff0,0x88888888,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (packWords [0x184263194184,0x18826319818826,0x32a42638000e52,0x612630e52a5263,0x2a526318418818,0x42d01a41841851,0x840e51691690e5,0x1631631842d41a,0x81881891881690,0xe50e51690e30e3,0x1882d00e400000,0x2b440a2b42,0xd40e52710e5271]) [(36,1)]
def stateEntry38 : Entry := row 5 [0xaaaa0000,0xfcccf888,0xfff0fff0] 2 (packWords [0xe00e00e,0x32712630e32a40,0xe32600e42630e4]) []
def stateEntry39 : Entry := row 5 [0xaaaa0000,0xcccc0000,0xf888f888,0xfff0fff0] 3 (packWords [0xe,0xe00e32b12c00,0xe32c40e32a00e3,0x2a40e32710e480,0x20e42720e48010,0xe42632638002a4]) [(3,1),(38,2),(38,1)]
def stateEntry40 : Entry := row 5 [0xaaaa8888,0xfcccf000,0xfff0fff0] 2 (packWords [0x1800e318,0x40e30e00e00e31,0x920e41842630e4]) []
def stateEntry41 : Entry := row 5 [0x88888888,0xfeeef000,0xfff0fff0] 2 (packWords [0x1800e318,0x40e30e00e00e31,0x910e41842630e4]) []
def stateEntry42 : Entry := row 5 [0x88888888,0xaaaa0000,0xfcccf000,0xfff0fff0] 3 (packWords [0x18,0xe31840e32a00,0xe32a40e30e00e0,0xe319226318480,0x21840e41848010,0xe40e42728000e4]) [(40,1),(38,1),(41,1)]
def stateEntry43 : Entry := row 5 [0x88888888,0xaaaa0000,0xcccc0000,0xf000f000,0xfff0fff0] 4 (packWords [0x18000000,0x2c00e32c40,0xe32a00e32a40e3,0xe00e00e32b12c,0x41848021842a41,0x848011840e4184,0x8000e426326344,0x2a40e42714400,0xe40e427243f0e4]) [(39,1),(42,2),(42,1)]
def stateEntry44 : Entry := row 5 [0x88888888,0xaaaa0000,0xcccc0000,0xf0f0f0f0,0xff00ff00,0xfff0fff0] 5 (packWords [0x163000000000,0xe300000000080,0x32c42c444c8022,0xa42a44108010e4,0xe441018418800,0x8002c41843481,0x842a4184328184,0xe41681680e434,0x81882c41883281,0x882a41881680e4,0xe416826326344,0x22a40e42714420,0xe40e42724410e4]) [(43,1),(23,1),(36,2),(36,1)]
def stateEntry45 : Entry := row 5 [0x88888888,0xaaaa0000,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xfff0fff0,0xffff0000] 6 (packWords [0x2c64212c641e18,0x42c61941841883,0x4a1981882c42c4,0x2c680226300000,0xe62c64370,0xe6163000000000,0xe300000000044,0x82d42d444c8012,0xb42b440c8000e6,0xe640c18418800,0x44d1c41841861,0x842b4184338184,0xe616a16a0e61c,0x818818a1883381,0x882b418816a0e6,0xe616a2b42d444,0x12b40e40000000,0xe62724410e6]) [(24,1),(37,2),(44,1)]
def stateEntry46 : Entry := row 5 [0xeeeeeeee,0xf0f0f0f0,0xff00ff00,0xfff88888,0xffff0000] 4 (packWords [0xe526126,0x30e51632633941,0x630e32633980e3,0x2632b40f40f416,0x10e51630e50e10,0xe10e31690e40e4,0xe541e0e316318,0x40e31631841631,0x840e31880e3188]) []
def stateEntry47 : Entry := row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xfff88888,0xffff0000] 5 (packWords [0x2632a5263401,0x1632633941630e,0x32633980e32632,0xd426341e2632b4,0x26341e18416316,0x31841880e30e31,0x880e50e52d440a,0xe60e62b44200e,0x31631840e31631,0x84163184163184,0x1631840e31880e,0x31880e31880e31,0x882b42d48002b4]) [(46,1)]
def stateEntry48 : Entry := row 5 [0x88888888,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xfff00000,0xffff0000] 6 (packWords [0x2a500000000016,0x32633941630e32,0x633980e32632d4,0x26341e2632b426,0x341e2634372634,0xf163331394163,0xe32b13980e342,0x2d42d441c40a2,0xb42b440c40f40c,0x80040c0e316318,0x40e31631841631,0x84163184163184,0x1631841631840e,0x31880e31880e31,0x880e31880e3188,0xe31882b42d444,0xe0000e50000000,0xe6000000000]) [(47,1)]
def stateEntry49 : Entry := row 5 [0x888f8888,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (packWords [0x163263194163,0xe32631980e326,0x32712632a52632,0x722632c62632a5,0x2632a50e316318,0x40e31631841631,0x84163184163184,0x1631841631840e,0x31880e31880e31,0x880e31880e3188,0xe318827027027,0x12b40e50e52712,0xd40e60e62722b4]) []
def stateEntry50 : Entry := row 5 [0xf0000,0x88888888,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x1632a51941630e,0x32a11980e32c42,0xa52c62a52a42a4,0x2a52c640f2a543,0x72a52630000000,0xe31631840e3,0x16318416318416,0x31841631841631,0x84163184000000,0x3310000e31880e,0x31880e31880e31,0x880e31880e3188,0x2b10002b,0x42d444f0000e50,0x41c2d4,0x4202d40e600000,0x40c2b440a2,0xb440c40180040c]) [(49,1)]
def stateEntry51 : Entry := row 5 [0x88888888,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xfff0fff0,0xffff0000] 7 (packWords [0x2a580e2a526342,0x12632a54212a52,0x6380d263329184,0x18426339426332,0x93941942631841,0x842a5188188263,0x3982632a539819,0x82631881882634,0x412632a52d42a5,0x2632d42632a580,0xc2a52634422632,0xc62b42a42632b4,0x2632c680b2c626,0x380a2632a54372,0xa52634372632a5,0x8092a545140216,0x30000000000000,0x0,0x4504130e300000,0x0,0x420441,0x4204412d42d442,0x2d42d44418084,0x1c40a44240a442,0x2b42b440a2b42b,0x444280740c8068,0x580440c40140c,0x80340140140c80,0x240c1844131844,0x2188188000000,0x4024024021c,0x62d41c41843581,0x841c6358186184,0x2d41841a52b41a,0x41843381841a53,0x381851842b4184,0x41340440418441,0x31848014134031,0x844041841ca358,0x1c81882d41881c,0xa2d418a1883581,0x881a93381a8188,0x2b41881a92b418,0x91883381884024,0x400188402188,0x80040240118840,0x1884422b42b42,0xd44412d4442442,0x44200000000044,0x24420e50000000,0x0,0x4414420e,0x60000000000000,0x0]) [(8,0),(8,1),(22,1),(11,1),(25,1),(26,1),(27,1),(30,1),(30,2),(33,1),(35,1),(45,1),(45,2),(48,1),(50,1)]
def stateEntry52 : Entry := row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff88ff00,0xffff0000] 6 (packWords [0x4543,0x291631634552a5,0x33126345432933,0x11944542a51631,0x634542a50e30e3,0x4543292b12a145,0x42a52b11984543,0x290e30e34532c6,0xe50e54532a52d,0x42694532c62d42,0xc64522a50e50e5,0x4522a50e60e645,0x22c62b426a4522,0xa52b42a54522c6,0xe60e64031840e,0x30e34031631881,0x63403184188184,0x4031630e30e345,0x31630e50e54531,0x84169161453163,0x1691634531840e,0x50e54521630e60,0xe645218416a162,0x45216316a16345,0x21840e60e64530,0xe31690e1453188,0xe50e14530e30e,0x50e34531881691,0x694520e316a0e2,0x4521880e60e245,0x20e30e60e34521,0x8816a16a4520e5,0x2b40e44522d40e,0x60e44520e50e60,0xe54522d42b42b4]) []
def stateEntry53 : Entry := row 5 [0x88880000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 7 (packWords [0x421329,0x1631634552a533,0x12a54213293311,0x944552a5163163,0x4212a50e30e344,0x73292b12a14212,0xa52b1198447329,0xe30e34482c60e,0x50e54482a52d42,0xa54482c62d42c6,0x42b2a50e50e542,0xb2a50e60e642b2,0xc62b42a442b2a5,0x2b42a542b2c60e,0x60e642140c44a2,0x63000000000000,0x0,0x4551,0x840e30e3447163,0x18816380218418,0x81844471630e30,0xe34481630e50e5,0x44818416916144,0x81631691634481,0x840e50e542b163,0xe60e642b18416,0xa16242b16316a1,0x6342b1840e60e6,0x45540c40440440,0xc16340c16340c4,0xc403801455163,0x4041634480e316,0x90e14481880e50,0xe14480e30e50e3,0x44818816916942,0xb0e316a0e242b1,0x880e60e242b0e3,0xe60e342b18816,0xa16a44740c4004,0x40c0e340c0e3,0x40c40c40180044,0x70e34000e342b0,0xe52b40e442b2d4,0xe60e442b0e50e,0x60e542b2d42b42,0xb444840c42d271,0x0,0x0,0x42b40c,0x42b27200000000,0x0,0x0]) [(52,0),(52,1),(33,1)]
def stateEntry54 : Entry := row 5 [0x77770000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 7 (packWords [0x42140f,0x16316345726333,0x12634214213313,0x31457263163163,0x42140f0e30e344,0x92632b12634214,0x212b12b1449263,0xe30e344a2630e,0x50e544b44b2d42,0x6144b2632d4263,0x44b44b0e50e544,0xa2630e60e644a4,0x4a2b426244a263,0x2b426344a44a0e,0x60e642140c42b2,0xa5000000000000,0x0,0x4571,0x840e30e3449163,0x18816380018418,0x81844491630e30,0xe344b1630e50e5,0x44b18416916144,0xb16316916344b1,0x840e50e544a163,0xe60e644a18416,0xa16244a16316a1,0x6344a1840e60e6,0x45733140433140,0xf16340316340f3,0x31403331457163,0x40416344b0e316,0x90e144b1880e50,0xe144b0e30e50e3,0x44b18816916944,0xa0e316a0e244a1,0x880e60e244a0e3,0xe60e344a18816,0xa16a4492b14002,0xb140f0e34010e3,0x40f2b14012b144,0x90e34000e344a0,0xe52b40e444a2d4,0xe60e444a0e50e,0x60e544a2d42b42,0xb444a2d440a2d4,0x44a0e544a0e544,0xb2d445627144a0,0xe540a0e544a2b4,0x44a2b444a0e640,0xa0e644a2b440a2,0x7244a0e644a0e6]) [(35,1)]
def stateEntry55 : Entry := row 5 [0x88888888,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xf7f7f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x1632631941632a,0x52632a52632a52,0x631981982632a5,0x2632a52632a426,0x32c62632a52632,0xa5184163184163,0x18416318416316,0x31841631841631,0x84163184163184,0x1631840e300000,0x4592d42d44,0x3940a2b42b445a,0x45940d4274392d,0x2b12d22b12b02,0xb02b12d24492b1,0x4012b12b42d445,0x80000e50000000,0xe6000000000]) []
def stateEntry56 : Entry := row 5 [0xff0000,0x77770000,0x88888888,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00] 6 (packWords [0xe31631840e316,0x31841631841631,0x84163184163184,0x16318432116332,0x91630000003310,0xe31880e3188,0xe31880e31880e,0x31880e31882b10,0xe31980e32630e3,0x2b10e32b42d445,0xd0000e50000000,0x2d43482d4329,0x2d42632633580e,0x60000000002b43,0x282b434a2b4263,0x26333800000045,0xc00040c2632634,0xc2632a545b263]) []
def stateEntry57 : Entry := row 5 [0x77770000,0x88888888,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 7 (packWords [0x80716316326333,0x12634213313312,0x631631638060e3,0xe32632b126342,0x12b12b12630e30,0xe326344a26344b,0x2d42d42632d426,0x344b42141c2634,0x4a26344a2b42b4,0x2632b426344a42,0x140c0000000004,0x21421421263421,0x26340c42140c40,0xc42b2a50000000,0x0,0x1840e30e,0x31631881631841,0x881841630e30e3,0x1632d416318435,0x81841633581631,0x842d41841632b4,0x16318433818416,0x33381631842b41,0x84163457163184,0x40c18416380516,0x31844571843314,0x13331163804163,0x33180333116341,0x31630e33580e31,0x882d41880e32d4,0xe31883581880e,0x33380e31882b41,0x880e32b40e3188,0x3381880e34490e,0x318840c1880e38,0x20e3188449188,0x2b14022b10e380,0x10e32b18002b10,0xe34020e344a2b4,0x2b42d444b2d444,0xa44a44a0000000,0x44a44a0e5000,0x0,0x2d44,0xa2d444a44a44a,0x2d44562d444a40,0xa40a44b44a0e60,0x0,0x2b,0x444a2b444a40a4,0xa2b440a2b444b,0x44a42000000000,0x4214,0x56456000000000]) [(55,1),(15,0),(13,1),(55,0),(15,1),(13,0),(56,0),(56,1)]
def stateEntry58 : Entry := row 5 [0xaaaa0000,0xcccc0000,0xf0f0f0f0,0xf888f888,0xff00ff00] 4 (packWords [0xe416016,0x30e40e31638000,0xe32c4163348163,0x2a41633281630e,0xe00e31682710,0xe44150e42720e4,0x45e0e42c00e32c,0x40e32a00e32a40,0xe32632634152a4]) [(39,1)]
def stateEntry59 : Entry := row 5 [0x88888888,0xaaaa0000,0xf0f0f0f0,0xfcccf000,0xff00ff00] 4 (packWords [0x18416334,0x81630e31638000,0xe32a4163328163,0xe41601630e40e,0x31882c40e32632,0x634602a40e4271,0x4150e42a00e32a,0x40e30e00e00e31,0x680e427245f0e4]) [(42,1)]
def stateEntry60 : Entry := row 5 [0x88888888,0xaaaa0000,0xcccc0000,0xf000f000,0xf0f0f0f0,0xff00ff00] 5 (packWords [0xe3163803000,0x1840000000002c,0x41633481632a41,0x633281630e4160,0x1630e418800000,0x2c00e32c40,0xe32a00e32a40e3,0xe00e00e31682c,0x444c8022c42a44,0x108012a40e4410,0x8000e426326346,0x22a40e42714620,0xe40e42724610e4]) [(58,1),(59,2),(59,1),(43,1)]
def stateEntry61 : Entry := row 5 [0xf000f0,0x88888888,0xaaaa0000,0xcccc0000,0xf0f0f0f0,0xff00ff00] 5 (packWords [0x180000188163,0x2c41633481632a,0x41633281630e41,0x601630e4000000,0x1840003481882c,0x41883281882a41,0x881680e40e4168,0xe300000000026,0x32634512a40e42,0x714510e42c4348,0x2c43480e427246,0x30e42a43282a43,0x280e41680e4168]) []
def stateEntry62 : Entry := row 5 [0x88888888,0xaaaa0000,0xcccc0000,0xf0f0f0f0,0xff00ff00] 6 (packWords [0x8031,0x840e30e3802163,0x18816380118418,0x81848001630e30,0xe344c3522c42c4,0x44c16334816344,0xc35234834844c1,0x632c4163410331,0x2a42a441016332,0x81634103313283,0x284101632a4163,0x4101630e40e441,0x1841681604101,0x63168163410184,0xe40e444c2d234,0x82c044c0e32c40,0xe344c2d22c42c4,0x44c0e33480e341,0x2b13282a04100,0xe32a40e34102b1,0x2a42a44100e332,0x80e34100e31680,0xe04101880e40e0,0x4100e30e40e341,0x18816816842b4,0xa2a42634482c4,0x42026342b40a42,0xb40a42b2c42a42,0xa442b40a0e40e4,0x4212c440627142,0xb40a42b40a42b2,0xc40e40e4448420,0xe40e44212a440,0x62724484204484,0x2042b2a40e40e4]) [(60,1),(44,1),(61,1),(61,0)]
def stateEntry63 : Entry := row 5 [0x88888888,0xaaaa0000,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 7 (packWords [0x42134a,0x1631634642c633,0x12c642134a3311,0x944642c6163163,0x4212c60e30e344,0xd34a2b12b14212,0xc62b119844d34a,0xe30e34482c644,0x82c44484482d42,0xc44482c62d42c6,0x44844842180140,0xa40a40a2630000,0x0,0x0,0x42140c0e60,0xe64212c64062c6,0x42142140640644,0x82c60e60e64641,0x840e30e344d163,0x18816380018418,0x818444d1630e30,0xe34481632d4163,0x44818435818444,0x81633581634481,0x842d4184464331,0x2b42b440c16333,0x816340c3313383,0x314641632b4163,0x4641630e60e640,0xc18416a16240c1,0x6316a163464184,0xe60e64480e335,0x80e34481882d41,0x884480e32d40e3,0x44818835818844,0xd2b13382b040c0,0xe32b40e340c2b1,0x2b42b144d0e333,0x80e344d0e316a0,0xe240c1880e60e2,0x40c0e30e60e344,0xd18816a16a4484,0xc2b42b44482d4,0x4202d444844842,0x4204482d42b42,0xb440a40a40a0e4,0x0,0x0,0x448420,0xe60e64212b440,0x62724484204484,0x204482b40e60e6]) [(45,1),(62,1)]
def stateEntry64 : Entry := row 5 [0xff0000,0x8f8f8888,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00] 5 (packWords [0xe31631840e3,0x16318416318416,0x31841631841631,0x84163184000000,0x1940000e31880e,0x31880e31880e31,0x880e31880e3188,0x2630e32a50e317,0x81782712b40e50,0xe52712d4271263,0x2632a50e60e627,0x22b42722632632,0xc62a52632632a5]) []
def stateEntry65 : Entry := row 5 [0x88ff8888,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x32916316,0x326346b2633294,0x69329263163163,0x8000e30e32632b,0x12634692b11982,0x630e30e326346a,0x26332927127126,0x32712633294693,0x2926342f26334a,0x27227226327226,0x334a46934a2634,0x6826332942d2a5,0x26345626332946,0x73291840e30e31,0x63188163184188,0x1841630e30e316,0x32711631843581,0x84163358163184,0x27118416327216,0x31843381841633,0x38163184272184,0x16343a16318446,0x61841634651631,0x844241840e3271,0xe31882d41880e,0x32d40e31882711,0x880e32720e3188,0x2b41880e32b40e,0x31882721880e34,0xe3188401188,0xe34010e318840,0x1882712b42702,0xd4272270271272,0x2712d42b42b427,0x140a0e53584300,0xe527142f271358,0x40a35827242f0e,0x633840a0e62724,0xa27233842f338]) [(64,0)]
def stateEntry66 : Entry := row 5 [0x88888888,0x88ff8888,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x1632633291630e,0x32631980e32632,0xd42633292632b4,0x26334a2632a526,0x33292633292633,0x290e31631840e3,0x16318416318416,0x31841631841631,0x84163184163184,0x1631840e31880e,0x31880e31880e31,0x880e31880e3188,0xe31880e31882b,0x42d442f0002d43,0x582d4358271000,0x2b43382b,0x43382720000000,0x430000000000]) []
def stateEntry67 : Entry := row 5 [0xff0000,0x88ff8888,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x3213291630e,0x32b11980e33482,0x71271329328272,0x27234a40432945,0xc3292630000000,0xe31631840e3,0x16318416318416,0x31841631841631,0x84163184000000,0x4690000e31880e,0x31880e31880e31,0x880e31880e3188,0x2b10e32b10e327,0x2702712b40e50,0xe5271358271358,0x2713580e60e627,0x23382723382723,0x3846c000000000]) []
def stateEntry68 : Entry := row 5 [0xff0000,0x88008888,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x3213291630e,0x32b11980e33482,0x71271329328272,0x27234a40432945,0xc3292a50000000,0xe31631840e3,0x16318416318416,0x31841631841631,0x84163184000000,0x3310000e31880e,0x31880e31880e31,0x880e31880e3188,0x2b10e32b10e327,0x2702712b40e50,0x271358,0x2713580e600000,0x2723382723,0x3800000042f000]) []
def stateEntry69 : Entry := row 5 [0x70777070,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (packWords [0x163263194163,0xe32632a50e316,0x926126316916a2,0x6226316a2a5263,0x2a52630e316318,0x40e31611611631,0x84162162163184,0x1841631841630e,0x10e10e31690e20,0xe20e316a1880e3,0x2b10e316816816,0x92b42d41690e50,0xe52b416a0e60e6]) []
def stateEntry70 : Entry := row 5 [0x88888888,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xf0fff0f0,0xff00ff00,0xffff0000] 6 (packWords [0x1632a519416326,0x32632a53292a52,0xb12a53292c42a5,0x2c62a52a42a42a,0x52c640f2a546f2,0xa5184163184163,0x18416318416316,0x31841631841631,0x84163184163184,0x1631840e300000,0x3582d42d43,0x583382b42b4338,0x80040c40140c2d,0x2b12d22b12b02,0xb02b12d246e2b1,0x4012b12b42d446,0xd0000e50000000,0xe6000000000]) [(69,1)]
def stateEntry71 : Entry := row 5 [0xff0000,0xf0f0000,0x88888888,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00] 6 (packWords [0xe31631840e316,0x31841631841631,0x84163184163184,0x16318432116332,0x91630000001940,0xe31880e3188,0xe31880e31880e,0x31880e31880000,0x1980002a10e3,0x2a50e32b42d447,0x20000e50000000,0x3292d434a2d4,0x2a52c42c62a50e,0x60000000003282,0xb43292b42a42a4,0x2a52c632940780,0x13292a54718002,0xa52632634702a5]) [(64,0),(64,1)]
def stateEntry72 : Entry := row 5 [0xff0000,0x88888888,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 7 (packWords [0x41341,0x33213294213294,0x1316316380a0e3,0xe33292b12b142,0x12b11983290e30,0xe334a474348329,0x2d42d434a2d42d,0x43294213293294,0x7332834a2b42b4,0x3292b42b434a42,0x134a80942140f3,0x29406329421406,0x40632942132941,0x34762630000000,0x0,0x1840e30e,0x31631881631841,0x881841630e30e3,0x1632d416318435,0x81841633581631,0x842d41841632b4,0x16318433818416,0x33381631842b41,0x84163404163184,0x41318416341316,0x31844041840000,0x0,0x42147533100000,0xe33580e31,0x882d41880e32d4,0xe31883581880e,0x33380e31882b41,0x880e32b40e3188,0x3381880e346e0e,0x31888081880e38,0x70e318846e188,0x2b14022b10e380,0x60e32b18052b10,0xe34020e34732b4,0x2b42d44742d447,0x34734730000000,0x4734730e5000,0x0,0x2d44,0x742d4358420358,0x2d44202d435847,0x43584744730e60,0x0,0x2b,0x44732b433840a3,0x382b440a2b4338,0x47333880440c40,0xc4038034038028,0x180040340c40c]) [(65,1),(66,1),(67,1),(15,1),(68,1),(70,1),(50,1),(1,1),(18,0),(56,1),(71,1)]
def stateEntry73 : Entry := row 5 [0x88888888,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 8 (packWords [0x80d329,0x16316341326333,0x12634213293311,0x94413263163163,0x80c2a50e30e340,0x22632b12634212,0xa52b1198402263,0xe30e342026342,0x2634202a52d42,0xa54202632d4263,0x4202a580b2a540,0xa26340a26340a2,0xc62b42a440a263,0x2b426340a2c680,0xa2c68092638082,0x634212a54062a5,0x42126340626340,0xc2a58072a54131,0x840e30e3402163,0x18816380618418,0x81844021630e30,0xe34201632d4163,0x42018435818442,0x1633581634201,0x842d418440a163,0x2b416340a18433,0x818440a1633381,0x6340a1842b4184,0x41316340416340,0xc1848051848041,0x63803163413184,0x4041844200e335,0x80e34201882d41,0x884200e32d40e3,0x42018835818840,0xa0e33380e340a1,0x882b418840a0e3,0x2b40e340a18833,0x81884020e34000,0xe340c188802188,0x8010e38000e340,0x218840018840a4,0xa2b42b440a2d4,0x4202d440a40a40,0xa40a0000000000,0x40a40a40a0e5,0x0,0x0,0x40a420,0x40a0e600000000,0x0,0x0]) [(2,1),(16,1),(19,0),(2,0),(16,0),(19,1),(51,1),(53,1),(54,1),(57,1),(63,1),(63,2),(72,0),(72,1)]
def stateEntry74 : Entry := row 5 [0xa2ffa2a2,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (packWords [0x1632a5329163,0x1882a11981880e,0x52612710e516a2,0x7227216a263263,0x2a534a18016318,0x41630e51841630,0xe5162162163184,0x1a51631a51630e,0x10e10e518816a1,0x881a916a0e30e3,0x1a91880e51680e,0x52b40e53580e51,0x690e60e627216a]) []
def stateEntry75 : Entry := row 5 [0xff0000,0xa2a2a2a2,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x32132916318,0x82b11981880e52,0xd42d40e516a272,0x27216a32934a32,0x934a2630000000,0x180163184163,0xe51841630e516,0x21621631841a51,0x631a5163000000,0x3310000e10e10e,0x518816a1881a91,0x6a0e30e31a9188,0x2b11882b11880e,0x51680e52d40e52,0xd40e51692d40e5,0x2d40e50e600000,0x27216a2721,0x6a40c40380040c]) [(74,1)]
def stateEntry76 : Entry := row 5 [0xa2a2a2a2,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 7 (packWords [0x800329,0x16316347826333,0x12634793293311,0x94478263163163,0x4772a518818847,0x72632b12634772,0xa52b1198477263,0x18818845a2630e,0x50e545a2a52d42,0xa545a2632d4263,0x45a2a50e50e540,0xd26316a16a40d2,0xc627226240d263,0x27226340d2c616,0xa16a40c2a540f2,0xa5479263406263,0x4792a54062a540,0xc26340c2634771,0x842b1180477163,0x18816347718418,0x81844771632b11,0x6345a1630e50e5,0x45a18435818445,0xa16335816345a1,0x840e50e540d163,0x27216240d18416,0xa16240d16316a1,0x6340d184272184,0x4781a54041a540,0xc16340c16340c1,0xa54031a5478163,0x40416345a1ca35,0x80e140d1880e50,0xe145a1ca0e50e5,0x45a18835818840,0xd1a916a16a40d1,0x8847718840d1a9,0x40d1a940d18816,0xa16a40d1a940a0,0xe345a1884080e3,0x40d1a940d1a940,0xd18840a18840d0,0xe540d0e540d2d4,0x16a16840d0e516,0xa0e540d2d445a2,0xd440d0e540d0e5,0x40d2d440a2d440,0xd0e540a0e545a2,0xd443916940d40c,0x40d0e600000000,0x0,0x0]) [(75,1)]
def stateEntry77 : Entry := row 5 [0xa2a2a2a2,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xff0cff0c,0xffff0000] 6 (packWords [0x2632a52632a516,0x32633291631882,0x631981880e52a5,0x2630e516a26226,0x316a2a52632a52,0x63184000000000,0x2b11881882b10e,0x53583580e540d1,0x6a16a40c40d47c,0x40a47b1c216318,0x81630e53581630,0xe5162162163272,0x47a1634031630e,0x10e10e518816a1,0x881a916a1a9188,0x1a91880e51680e,0x52d40e52d40e51,0x690e6000000000]) []
def stateEntry78 : Entry := row 5 [0xaa00aa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xfcf4fcf4,0xff00ff00,0xffff0000] 6 (packWords [0x1842631941842a,0x52632a52631ca2,0x632a51ca0e5261,0x2630e516a2c626,0x316a2632c62632,0xc618445118447f,0x1841c21842d20e,0x51841860e51620,0x16a184000000,0x1a50000e300000,0x1690e50e52,0x7133816a16a338,0x47f4424184511c,0xa0e50e518a16a1,0xca47e16a47d1ca,0x4011ca0e516a0e,0x52d40e52d40e52,0xd40e6000000000]) []
def stateEntry79 : Entry := row 5 [0xa200a2,0xc0c0c0c,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x16326319416318,0x82631981880e52,0xa52630e516a262,0x26316a2632a526,0x32a52a52632a52,0x63180163184163,0xe51841630e516,0x21621631841631,0x84163184000000,0x1a50000e10000e,0x518816a1881891,0x6a0000001ca000,0x2b11882b11880e,0x516a0e52d41690,0xe52d4,0xe52d416a33816,0xa3380e60000000,0x47b000]) []
def stateEntry80 : Entry := row 5 [0xa2a2a2a2,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xf3f30000,0xff00ff00,0xffff0000] 6 (packWords [0x1632633311632a,0x50000000001882,0x632b11880e52d4,0x2630e516a26226,0x316a40f2634822,0x63331163331163,0x1801631841630e,0x51841630e51621,0x621631841a5163,0x1a51631882b12b,0x11880e52d42d40,0xe516a40c40d16a,0x40a48140d4800e,0x10e10e518816a1,0x881a916a0e30e3,0x1a91880e51680e,0x52d40e52d40e51,0x690e6000000000]) []
def stateEntry81 : Entry := row 5 [0xaa00aa,0xaaaaaaaa,0xcc440000,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x1842631941840e,0x32631980e30e52,0x612630e52c6000,0x16a32826,0x316a2633292633,0x290e31801840e3,0xe51691690e535,0x21843521841620,0x16a184000000,0x1630000e10e10e,0x31692d20e32d20,0xe30e31880e316a,0xe31880e31882d,0x40000000000e51,0x680e53380e5169,0xe516916a40440,0xa16a0000004460,0xe6000000000]) []
def stateEntry82 : Entry := row 5 [0xaa00aa,0x33bb0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x1842c634a1840e,0x32b12b10e30e52,0x712710e516a2c6,0x33816a26300000,0x40f2c64842,0xc60e31801840e3,0xe51691690e516,0x200016a1843941,0x84394184000000,0x1630000e10e10e,0x31690e31880e31,0x6a2b10e32b10e3,0xe31880e31880e,0x51680e53382710,0xe52710e50e5169,0xe516933816a33,0x816a0e60000000,0x468475483473]) []
def stateEntry83 : Entry := row 5 [0xaa00aa,0xaaaaaaaa,0xcc44cc44,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 7 (packWords [0x32918418426335,0x22633293521942,0x631841842a50e3,0xe32632b12632a,0x52b11982630e30,0xe32630e50e52a5,0x27126126327126,0x32a50e50e52c68,0x52c6263487263,0x2c64872c626380,0x426326316a16a2,0xc63382c6263338,0x2632c616a16a26,0x38032632c64842,0xc62634842632c6,0x40c2c61840e30e,0x33521881801841,0x881843520e30e3,0x1c60e50e518448,0x51841c64311c61,0x840e50e51c643a,0x1c618440a1841c,0x640a1c61844241,0x84424424162000,0x42416a16,0xa1844851840000,0x0,0x4244241a500000,0xe32710e11,0x880e50e10e30e5,0xe31882711881c,0xa4861ca0e38020,0xe31ca8011ca0e3,0x4860e30e316a0e,0x318840c1880e34,0x240e318816a16a,0xe347d0e318840,0xc1880e38000e31,0x8847d18840c422,0x16900000000000,0x0,0xe53380e5424,0x16a16a0e516a0e,0x54243383380000,0x431431431,0xe54310e540c43,0x140c40a3383384,0x2416a16a40a16a,0x16a42433833800,0x0,0x43a43143a000,0x4854242b,0x40000000000000,0x0]) [(77,3),(78,1),(79,3),(80,3),(81,1),(82,1)]
def stateEntry84 : Entry := row 5 [0x3032f0fa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (packWords [0x1842a5194184,0xe32a12a50e30e,0x52a534a0e50e62,0x622720e62a5329,0x2632630e31a118,0x40e30e51691690,0xe50e616216a0e6,0x1843521631630e,0x10e10e31690e30,0xe60e316a0e3188,0xe32d20e40e40e,0x52b40e51690e51,0x690e616a0e616a]) []
def stateEntry85 : Entry := row 5 [0xaaaa0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xf0fcf0fc,0xff00ff00,0xffff0000] 6 (packWords [0x1842c61941842c,0x634a2c634a0e32,0xc22c60e30e52c4,0x2c60e50e62c648,0xa0002630000000,0x184331163163,0xe31c21840e30e,0x51611690e50e61,0x6a16a0e6331184,0x33118418800000,0x1690e50e51,0x6916a0e60e616a,0x80040c40140c0e,0x30e50e31690e20,0xe20e316a4890e3,0x4010e30e40e40e,0x52d441c0e54880,0xe5272000000000]) [(84,2)]
def stateEntry86 : Entry := row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xf0faf0fa,0xff00ff00,0xffff0000] 7 (packWords [0x48c329,0x18418448c26335,0x226348c3293521,0x9448c263184184,0x40126340126348,0xd32940632948d2,0x63406263401329,0x40f3294862a50e,0x30e34862632b12,0x634862a52b12a5,0x4862630e30e348,0xb2630e50e548d2,0xa527126148b263,0x2712638002a50e,0x50e54502630e60,0xe64502c62b42a4,0x4502632b426345,0x2c60e60e64501,0x84450184450352,0x40a35245018440,0xa1634863524621,0x634501840e30e3,0x4863524861a148,0x618448c1844863,0x520e30e348b1c6,0xe50e548c18416,0x916948b1c61691,0x6948c1840e50e5,0x4501a50e60e645,0x18416a1624501,0xa516a16a450184,0xe60e648644240,0xc1880000000000,0x0,0x48,0xb4201691694014,0x1c0e50e548b420,0xe50e540141c16,0x916945040a16a1,0x6a4504500e60e6,0x45040a0e60e645,0x45016a16a48b0,0xe31690e14862b1,0xe50e148b0e30e,0x50e34862b11691,0x694500e316a0e3,0x4504500e60e645,0xe30e60e34504,0x5016a16a4500e5,0x2b40e44502d40e,0x60e44500e50e60,0xe54502d42b42b4]) [(85,2)]
def stateEntry87 : Entry := row 5 [0xaa00aa,0xaaaaaaaa,0xc0c8c0c8,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x1842631941840e,0x32631980e31692,0xa52631692632a5,0x2632a516a2c626,0x316a2632c62632,0xc60e31801840e3,0x1c61691691841c,0x61841c61841620,0x16a184000000,0x1a50000e31880e,0x31690e31880e31,0x880e31880e316a,0xe31880e31880e,0x50000000001681,0x6816933841c169,0x48b16916a49040,0xa16a48f43348e4,0x220e6000000000]) []
def stateEntry88 : Entry := row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xf0faf0fa,0xff00ff00,0xff550000,0xffff0000] 6 (packWords [0x2c600000000018,0x42633521842634,0x8726340f0e3263,0x2a50e30e526126,0x30e50e62a42630,0xe6184352352184,0x4944934924910e,0x34864010e30e52,0xd42d40e50e6338,0x2b40e618435216,0x31630e31a11840,0xe30e51691690e5,0xe616216a0e618,0x80000000001690,0xe50e516916a0e6,0xe616a0e10e10e,0x31690e30e60e31,0x6a0e40e40e52d4]) []
def stateEntry89 : Entry := row 5 [0xaa00aa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xf0fa0000,0xff00ff00,0xffff0000] 6 (packWords [0x18434232918426,0x30000000000e32,0xb11980e30e5271,0x2710e516a32832,0x916a40f32948d3,0x29394184394184,0xe31801840e30e,0x51691690e51620,0x16a184000000,0x1630000e32b12b,0x10e30e52712710,0xe516a49640a16a,0x4914754954730e,0x10e10e31690e31,0x880e316a0e3188,0xe31880e51680e,0x52d40e51690e51,0x690e6000000000]) []
def stateEntry90 : Entry := row 5 [0xaa00aa,0xf050000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x1842631941840e,0x32632a50e30e52,0x612630e516a2c6,0x26316a32900000,0x2632c62632,0xc60e31801840e3,0xe51691690e516,0x200016a1843521,0x84352184000000,0x1630000e10e10e,0x31690e31880e31,0x6a0000002d2000,0xe31880e31880e,0x51680e52d43580,0xe53580e50e5169,0xe516933816a33,0x816a0e60000000,0x497000]) []
def stateEntry91 : Entry := row 5 [0xaa00aa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xf0faf0fa,0xff00ff00,0xffff0000] 7 (packWords [0x32918418426335,0x22633293521942,0x63184184263805,0x26332948732926,0x34872633298043,0x292a50e30e3263,0x2b12632a52b12a,0x52630e30e32630,0xe50e52a5271261,0x2632712632a50e,0x50e526316a16a2,0xc63382c6263338,0x2632c616a16a26,0x38032632c648d2,0xc626348d2632c6,0x40c2c618445018,0x435240a3521844,0xa184352462352,0x1840e30e335248,0x635218448c1843,0x520e30e31c60e5,0xe51841691691c,0x61691691840e50,0xe5450450162000,0x45016a16,0xa18448c1840000,0x0,0x4504501a500000,0x44240c1880,0x0,0x43,0x11691698020e50,0xe54310e50e5801,0x16916940a16a16,0xa45048c40440a4,0x5040a45016a16a,0x46248646200000,0x0,0xe3169,0xe12b10e50e10e,0x30e50e32b11691,0x690e316a0e3450,0x48640c0e34500e,0x345016a16a0e34,0x860e340c48640c,0x48648,0x64860e53380e52,0xd416a1680e516a,0xe52d43382d40e,0x58000e516948b1,0x690e548b0e5169,0x40c16948c4500e,0x60000000000000,0x0]) [(77,3),(87,1),(79,3),(88,1),(89,1),(90,1)]
def stateEntry92 : Entry := row 5 [0xaaaaaaaa,0xaaae000c,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (packWords [0x184263194184,0x1882631981880e,0x52712630e52632,0xa52632c60e6262,0x2630e618018018,0x42b10e51611690,0xe5331184163163,0xe616a16a0e60e,0x10e10e51692b11,0x880e30e316a0e6,0xe616a2710e527,0x10e50e40e40e52,0xd40e62722720e6]) []
def stateEntry93 : Entry := row 5 [0xa000a,0xaaaaaaaa,0xcccc0000,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x1842a519418418,0x82d21981880e52,0xa5498000263000,0xe62a42a,0x50e640f2a54062,0xa51801801842d2,0xe51691690e535,0x21843521840e61,0x6216a0e6000000,0x1630001690e50e,0x51692d21882d21,0x880e20e20e616a,0xe300027,0x10000000000e40,0xe40e52b441c0e5,0x4200e50e640c44,0x20e641c40c8004,0xc272000000000]) [(92,2)]
def stateEntry94 : Entry := row 5 [0xa000a,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 7 (packWords [0x499329,0x18418449926335,0x22634993293521,0x94499263184184,0x4862a518818848,0x62632d22634862,0xa52d2198486263,0x1881884982630e,0x50e549a2a52712,0x61498263271263,0x8002a50e50e544,0x22630e60e64422,0xc62b42a4442263,0x2b42634422c60e,0x60e640c26340f2,0x6349a2a54062a5,0x49a26340626340,0xc2a540c2a54861,0x842d2180486352,0x18818044218418,0x81844863522d22,0xd24981c60e50e5,0x49918416916949,0x81c61691694991,0x840e50e54421a5,0xe60e644218416,0xa1624421a516a1,0x6a4421840e60e6,0x0,0x4994,0xc451163000000,0x4981ca16,0x91694861880e50,0xe54981ca0e50e5,0x48618816916944,0x21a916a0e24421,0x880e60e24421a9,0xe60e644218816,0xa16a0000000000,0x0,0x48640c4500e300,0x4420,0xe52b40e44422d4,0xe60e44420e50e,0x60e54422d42b42,0xb440c27141c271,0x4980e54200e549,0x827142027140c0,0xe540c0e544240c,0x44227200000000,0x0,0x0]) [(93,1)]
def stateEntry95 : Entry := row 5 [0xaa00aa,0xcccccccc,0xcece0a0a,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (packWords [0x184263172172,0x18826319818816,0xa2a526316a0e52,0x612630e50e6272,0x2630e618018018,0x42d216216216a1,0x840e51691690e5,0x16300016,0xa1880e30e31690,0xe50e51690e20e2,0xe61880e516816,0x90e50e616a2720,0xe60e40e40e5169]) []
def stateEntry96 : Entry := row 5 [0xaa00aa,0xa0a0a0a,0xcccc0000,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x1842a519418418,0x82d21981880e52,0xa549c000263000,0x16a2a532,0x916a0e62a42a50,0xe61801801842d2,0xe51691690e535,0x21843521841621,0x6216a184000000,0x1630001690e50e,0x51692d21882d21,0x880000000e3000,0xe20e20e618827,0x10000000001680,0xe51690e50e40e4,0xe516916a40c80,0x116a0e640c8000,0xe60e616a49b0e6]) [(95,0),(95,1)]
def stateEntry97 : Entry := row 5 [0xaa00aa,0xa0a0a0a,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 7 (packWords [0x499329,0x18418449926335,0x22634993293521,0x94499263184184,0x4862a518818848,0x62632d22634862,0xa52d2198486263,0x18818849c2630e,0x50e549d2a52712,0x6149c263271263,0x8002a50e50e540,0xc26316a16a49d2,0xa53382a549d263,0x33826340c2a516,0xa16a40c2630e60,0xe649d2c62b42a4,0x49d2632b426340,0xc2c60e60e64861,0x842d2180486352,0x18818048618418,0x81844863522d22,0xd249c1c60e50e5,0x49918416916949,0xc1c61691694991,0x840e50e5499499,0x40416248618416,0xa16249940c16a1,0x6a499184404184,0x0,0x40a4,0xa40a163000000,0x49c1ca16,0x91694861880e50,0xe549c1ca0e50e5,0x48618816916900,0x0,0x40a40a,0x40a0e300000000,0x4864864000,0xe24861880e60e2,0x48640c0e60e648,0x618840018840c1,0x6933816849c0e5,0x16a0e549c16916,0xa16940c0e53380,0xe540c0e52b40e4,0x49c1690e60e449,0xc0e50e60e540c1,0x692b4169499404,0xe60e648616a40,0x16a4864864004,0x48616a0e60e6]) [(96,1)]
def stateEntry98 : Entry := row 5 [0xace0ace,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x32916316,0x32633312633293,0x31194263163163,0x2a50e30e32632d,0x22632a52d21982,0x630e30e3263169,0x1692a527126126,0x32712632a51691,0x692630e60e62c6,0x27226226327226,0x32c60e60e62634,0xf2632a54062a5,0x2634062632a540,0xf2a51840e30e31,0x63188163184188,0x1841630e30e316,0x32711611841691,0x61163169163184,0x2711841630e60e,0x61844a31621634,0x9e1631840e60e6,0x16346216318443,0xb1841634171631,0x844501840e3169,0xe11884a20e10e,0x34a10e31881691,0x690e32720e2188,0xe60e20e30e60e,0x31882721880e34,0x9e0e318840a188,0xe340a0e31884a,0x1881692b41693,0x580e60e61690e6,0xe63582b42b416,0x948f0e53584080,0xe516940b169358,0x49f3580e649e0e,0x62b440a16a0e64,0xa0e62b449e2b4]) []
def stateEntry99 : Entry := row 5 [0xaa00aa,0xcae0cae,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x1842631941840e,0x32631980e30e52,0x612630e516a2c6,0x26316a2632c626,0x32c62632c62632,0xc60e31801840e3,0xe51841860e516,0x200016a1843521,0x84352184000000,0x1630000e10e10e,0x31880e31880e31,0x6a0e31880e3188,0xe31880e31880e,0x516a0e52d40e51,0x690e52d40e52d4,0xe52d416a33816,0xa3382720000000,0x4a4000000000]) []
def stateEntry100 : Entry := row 5 [0xace00cc,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (packWords [0x184263194184,0xe32631980e316,0x92712631690e62,0x622630e62632a5,0x2632a50e318018,0x40e31611611691,0x840e616a16a0e6,0x3311841631630e,0x31880e31690e20,0xe20e316a0e3188,0xe31881680e60e,0x62b40e50e52711,0x690e616a0e616a]) []
def stateEntry101 : Entry := row 5 [0xaa0000,0xc0c0c0c,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x1632c619416318,0x82b11981880e52,0xc42c60e50e62c6,0x3290e634a2c634,0xa2c62630000000,0x180163184163,0xe51841630e50e,0x61621630e61631,0x84163184000000,0x3310000e10000e,0x518816a0e60e61,0x6a0000000e3000,0x2b11882b11880e,0x40e40e52d41690,0x41c0e5,0x4200e516a0e616,0xa0e62720000000,0x41c40c80040c]) [(100,0)]
def stateEntry102 : Entry := row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xf3fb00aa,0xff00ff00,0xffff0000] 5 (packWords [0x184263331184,0x2632c626334a0e,0x32632a50e30e52,0x612630e516a2b4,0x26316a33118416,0x31630e31801840,0xe30e51691690e5,0x16216216a18418,0x80e30e31881690,0xe50e51690e60e6,0x2b416a0e10e10e,0x31690e31880e31,0x6a0e51680e52b4]) []
def stateEntry103 : Entry := row 5 [0xaa00aa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xf3f30000,0xff00ff00,0xffff0000] 6 (packWords [0x18426334a1842a,0x50000000000e32,0x632b10e30e5261,0x2630e516a33826,0x316a26334a2633,0x4a394184394184,0xe31801840e30e,0x51691690e51620,0x16a184000000,0x1630000e32b12b,0x10e30e52d42710,0xe516a33833816a,0x40f40c80040c0e,0x10e10e31690e31,0x880e316a0e3188,0xe31880e51680e,0x52d40e51690e51,0x690e6000000000]) [(102,1)]
def stateEntry104 : Entry := row 5 [0xaa00aa,0xc0c0c0c,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 7 (packWords [0x32918418426335,0x22633293521942,0x631841842a5188,0x1882632b12632a,0x52b11982631881,0x882630e50e52a5,0x2d42a52632d426,0x32a50e50e52631,0x6a16a2c63382c6,0x2633382632c616,0xa16a2638082632,0xa54872a5263487,0x2632a58072a526,0x38062632c64822,0xc62634822632c6,0x8052c61842b118,0x3521881801841,0x881843522b12b1,0x1c60e50e518447,0xa1841c64311861,0x840e50e540d40d,0x16200000000040,0xd16a16a18447a1,0x84352404352184,0x47a18435247a35,0x21844041840000,0x0,0x40d40d16300000,0x4314310e10,0x4310e5,0xe51884861881a,0x916a16a1884861,0x881a940d189188,0x16a16a00000000,0x4314,0x80e3000000000,0x2b14002b118848,0x61882b14862b11,0x884001880e5338,0xe52d416a16a0e,0x516a0e52d43382,0xd4486439169000,0x0,0xe54,0x310e52d44202d4,0xe54200e52d443,0x12d416a40d16a3,0x3840a33816a40a,0x16a33840d33847,0xa40d0e60000000,0x0,0x80441c41,0xc40c80340c8028,0x180040c41c40c]) [(98,2),(99,3),(99,1),(79,1),(79,3),(101,1),(103,3),(101,3),(103,1)]
def stateEntry105 : Entry := row 5 [0xaa0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 7 (packWords [0x473329,0x1631634a72c635,0x22c64a73293521,0x944a72c6163163,0x4872c60e30e34a,0x63292b12b14872,0xc62b11984a6329,0xe30e34a52c60e,0x50e54873292712,0x714a52c6271271,0x4873290e50e547,0x33290e60e64732,0xc63382c6473329,0x3383294732c60e,0x60e648740c4762,0x63000000000000,0x0,0x4a71,0x840e30e34a6163,0x1881634a718418,0x81844a61630e30,0xe34a51630e50e5,0x4a71841691614a,0x51631691634a71,0x840e50e5473163,0xe60e647318416,0xa16247316316a1,0x634731840e60e6,0x0,0x4a74,0xc475331000000,0x4a50e316,0x90e18001880e50,0xe14a50e30e50e3,0x4a618816916947,0x30e316a0e24731,0x880e60e24730e3,0xe60e347318816,0xa16a4a62b14002,0xb140c0e340c0e3,0x40c2b14012b14a,0x60e34000e34730,0xe53380e44732d4,0xe60e44730e50e,0x60e54732d43382,0xd440c27141c271,0x4a50e54200e54a,0x527142027140c0,0xe540c0e547340c,0x47327200000000,0x0,0x0]) [(101,1)]
def stateEntry106 : Entry := row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xf3f30000,0xff00ff00,0xffff0000] 7 (packWords [0x48234a,0x1631634ac26333,0x126348234a3313,0x314ac263163163,0x48241c4ad2a500,0x0,0x0,0x4a94a90e,0x30e34a92632b12,0x634a94a92b12b1,0x4a82630e30e34a,0x82630e50e54a84,0xa82d42614a8263,0x2d42634a84a80e,0x50e54802630e60,0xe648234a272262,0x48026327226348,0x234a0e60e64ac3,0x3140433140f163,0x40316340f33140,0x33314ac1634041,0x634a91840e30e3,0x4a91631881634a,0x91841881844a91,0x630e30e34a8163,0xe50e54a818416,0x91614a81631691,0x634a81840e50e5,0x4801630e60e680,0x18416a1624801,0x6316a1634ac184,0xe60e64a84200e,0x30e34a94ab2b12,0xb14a84202b12b1,0x4a84aa0e30e34a,0x844a0e50e54a84,0xa82d42d44a8456,0x2d42714a84a80e,0x50e548040a0e60,0xe640f40c2b42b4,0x48040a2b42b440,0xf40c0e60e64a80,0xe31690e14a8188,0xe50e14a80e30e,0x50e34a81881691,0x694800e316a0e2,0x4a91880e60e248,0xe30e60e34a91,0x8816a16a4800e5,0x2b40e44a82d40e,0x60e44800e50e60,0xe54a82d42b42b4]) [(103,1)]
def stateEntry107 : Entry := row 5 [0x88aaaa,0xcc00cc,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x1842631941840e,0x32631980e31693,0x482631692632a4,0x2632c626334a26,0x334a2632c62632,0xa50e31801840e3,0x1610001691841a,0x51841a51840000,0x1630001a5184,0x1a51840e31880e,0x31690e31880e31,0x880e31880e3188,0xe31880e318816,0x93581692b40e50,0x169358,0x16935840c2b44a,0xe2b40e60000000,0x40a4af4ae422]) []
def stateEntry108 : Entry := row 5 [0xaa00aa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xfff5f0f0,0xffff0000] 6 (packWords [0x2a52632a526318,0x42631941842a52,0x631981980e5261,0x2630e516a2c626,0x316a2632c62632,0xc64511841844b2,0xe300000000016,0x90e50e516916a3,0x3833816a4b2442,0x49245118435218,0x42d20e51691690,0xe516200016a184,0x16300016,0x90e50e516916a2,0xd24b116a4b02d2,0x4012d20e51680e,0x52d40e51690e51,0x690e6000000000]) []
def stateEntry109 : Entry := row 5 [0xaa00aa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xff550000,0xffff0000] 7 (packWords [0x40c4732c600000,0x0,0x4b3184,0x1842633522634b,0x33523522631841,0x842a50e30e3263,0x2b12632a52b12a,0x52630e30e32630,0xe50e52a5271261,0x2632712632a50e,0x50e526316a16a4,0x76338338263338,0x26347616a16a00,0x4874874,0x8726348726340c,0x48740c40a18418,0x44b535235240a3,0x52352476184184,0x8050e30e34862d,0x22d28042d22d24,0x860e30e34310e5,0xe58032d42d443,0x12d42d48020e50,0xe540a16a16a476,0x33833840a33833,0x847616a16a0000,0x0,0x4b54874b500000,0x1840e30e33,0x52188180184188,0x1843520e30e31c,0x60e50e51841691,0x691c6169169184,0xe50e547647616,0x20000000004761,0x6a16a1844b3184,0x0,0x4764761630,0xe3169,0xe11880e50e10e,0x30e50e31881691,0x690e316a0e3188,0x40c1880e34760e,0x318816a16a0e34,0xb00e318840c188,0xe38010e31884b,0x1880e53380e52,0xd416a1680e516a,0xe52d43382d40e,0x58000e51694b41,0x690e54b40e5169,0x40c1694b34760e,0x60000000000000,0x0]) [(80,3),(88,1),(81,1),(107,2),(108,1),(90,1)]
def stateEntry110 : Entry := row 5 [0xaaaaaaaa,0xaaee00cc,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x34a18418,0x426333126334a3,0x31194263184184,0x2c60e30e32632b,0x12632c62b11982,0x630e30e3263169,0x1694b627127126,0x32712634b61691,0x6926340a26334a,0x4b92a52634af26,0x334a40a34a2630,0xe60e62c6272262,0x2632722632c60e,0x60e61840e30e33,0x31188180184188,0x1843310e30e34b,0x62711611841691,0x614b6169169184,0x2711843314b533,0x11844661843314,0x65163184476163,0x1a50e60e618416,0xa16a1a516a16a1,0x840e60e60e3169,0xe31888001880e,0x34b60e31881691,0x690e34000e3188,0x4011880e34010e,0x31884001880e31,0x6a0e21880e60e2,0xe30e60e318816,0xa16a2714b80e51,0x6944a0e5271456,0x2711694b716916,0x94af1683580e60,0xe61690e60e6358,0x4b635840a16a16,0xa4af0e60e640a0,0xe60e64af16a16a]) [(95,3)]
def stateEntry111 : Entry := row 5 [0xaaaa0000,0xaaaaaaaa,0xaaee00cc,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x1842c61941840e,0x32b11980e31692,0x712711692c634a,0x2c634a0e62c64a,0xf0002630000000,0xe31801840e3,0x16116116918433,0x11841631630e61,0x6a16a0e6331184,0x3311840e31880e,0x31690e31880e31,0x880e20e20e316a,0x2b10e32b10e30e,0x50e52711691680,0xe60e6358271169,0x27116916a0e60e,0x616a4b90000000,0x272000000000]) []
def stateEntry112 : Entry := row 5 [0xaa00aa,0xaaaaaaaa,0xcccccccc,0xccee00aa,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x1842631941840e,0x32631980e32632,0xc62633290e5261,0x2630e516a32826,0x316a2633292633,0x290e31801840e3,0x3521843521840e,0x51691690e51620,0x16a184000000,0x4460000e31880e,0x31880e10e10e31,0x690e31880e316a,0xe31880e318816,0x90e50e516916a4,0x440a16a4ba000,0xe51680e,0x53380e51690e51,0x69272000000000]) []
def stateEntry113 : Entry := row 5 [0x2200aa,0xaaaaaaaa,0xcccc0000,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x1842a51941840e,0x32a11980e30e52,0xa54bb0002c6000,0x16a27227,0x216a2a53292a53,0x290e31801840e3,0xe51691690e535,0x21843521841621,0x6216a184000000,0x1630000e10e10e,0x31692d20e32d20,0xe30e31880e316a,0xe31880e31882d,0x40000000000e51,0x680e53380e5169,0xe516916a27227,0x216a0000004460,0xe6000000000]) []
def stateEntry114 : Entry := row 5 [0xaa00aa,0x2222aaaa,0xcccc0000,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x1842a51941840e,0x32a11980e30e52,0xa54bd0002c6000,0x16a3282a,0x516a2a52722723,0x290e31801840e3,0xe51691690e535,0x21843521841621,0x6216a184000000,0x1630000e10e10e,0x31692d20e32d20,0xe30e31880e316a,0xe31880e31882d,0x40000000000e51,0x680e53380e5169,0xe516900000040,0xa00041c2722724,0xc0e60e64bc16a]) []
def stateEntry115 : Entry := row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xf3a2f300,0xff00ff00,0xffff0000] 5 (packWords [0x163263329163,0x2a52633292630e,0x32631980e30e52,0x612630e50e6262,0x2630e618416333,0x11630e31631880,0xe30e51611630e5,0xe61621630e60e,0x31881880e30e54,0x1690e50e62b4,0x3380e60e10e10e,0x31880e20e20e31,0x6a0e40e40e52d4]) []
def stateEntry116 : Entry := row 5 [0xaa00aa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xfcfcf0f0,0xff00ff00,0xffff0000] 6 (packWords [0x1842a519418426,0x32632a53292a52,0xd22a53290e52a5,0x2c60e516a2c62a,0x516a2a52c62a52,0xc6184403184404,0x1843521842d20e,0x51691690e51620,0x16a184000000,0x1630000e300000,0x1690e50e51,0x6916a40c40a16a,0x80040c40140c16,0x90e50e516916a2,0xd242e16a4be2d2,0x4012d20e51680e,0x52d40e51690e51,0x690e6000000000]) [(115,3)]
def stateEntry117 : Entry := row 5 [0xaa00aa,0xaaaaaaaa,0xcccc0000,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 7 (packWords [0x3291841842a535,0x22a53293521942,0xa51841842a50e3,0xe33292b12a12a,0x52b11983290e30,0xe34310e50e52a5,0x4872a543143143,0x10000000004314,0x4a263000000000,0x0,0x2a516a16a4,0x2b3383282a5338,0x2a542b16a16a2a,0x54872a53294063,0x292a54062a5329,0x4873291840e30e,0x33521881801841,0x881843520e30e3,0x1c60e50e518416,0x91691c61691691,0x840e50e5352404,0x3521844bf18435,0x24bf3521844041,0x8442b42b162000,0x42b16a16,0xa1844bf1840000,0x0,0x42b42b16300000,0xe31690e11,0x880e50e10e30e5,0xe31881691692d,0x24862d20e380a0,0xe32d28092d20e3,0x4860e30e316a0e,0x31888081880e34,0x2b0e318816a16a,0xe34be0e318880,0x71880e38060e31,0x884be18848742d,0x27100000000000,0x0,0xe53380e542b,0x16a1680e516a0e,0x542b3383380e54,0x310e5169420169,0xe54200e516943,0x116940a16a16a4,0x2b80540c40a42b,0x40a42b16a16a80,0x441c41c40c8034,0xc80280180040c,0x41c40c4bf42b0e,0x60000000000000,0x0]) [(110,2),(111,2),(112,1),(113,1),(81,1),(114,1),(85,2),(93,1),(96,1),(116,1),(101,3)]
def stateEntry118 : Entry := row 5 [0xaff0a0a,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x32916316,0x32633312633293,0x31329263163163,0x4c61881882632b,0x12634c62b11982,0x631881882630e5,0xe532927126126,0x32712633290e50,0xe52630e60e634a,0x27227226327226,0x334a0e60e62634,0x9126334a4c52a5,0x2634ab26334a47,0x34a1842b11801,0x63188163184188,0x1841632b116316,0x30e50e51841691,0x61163169163184,0xe50e51630e60e,0x61844c41841634,0xc01631840e60e6,0x1634621631844c,0x31841634c21631,0x844501841ca169,0x1691880e50e51c,0xa0e50e51881691,0x692b12720e2188,0xe60e22b10e60e,0x61882721882b14,0xc02b118840a188,0x2b140a0e31884c,0x10e30e52b40e42,0xd40e60e40e50e6,0xe52d42b42b416,0x941c1690e54200,0xe51694201690e5,0x41c0e52724c016,0xa0e640a0e62724,0xa2720e64c00e6]) []
def stateEntry119 : Entry := row 5 [0xff0000,0xaff0a0a,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x32132916318,0x82b11981880e52,0x712710e50e6272,0x2720e632934a32,0x934a2630000000,0x180163184163,0xe51611630e50e,0x61841630e61631,0x84163184000000,0x3310001690e50e,0x51690e20e20e61,0x882b11880e30e3,0x2b11882b11880e,0x40e40e52b41690,0xe51690e52710e5,0x2710e516a0e627,0x20e62720e62720,0xe646d000000000]) []
def stateEntry120 : Entry := row 5 [0xaa00aa,0xfaf00aa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x1842631941840e,0x32632a50e30e52,0x612630e516a2c6,0x26316a2632c626,0x32c62632c62632,0xc60e31801840e3,0xe51691690e516,0x200016a1843521,0x84352184000000,0x3310000e10e10e,0x31690e31880e31,0x6a0e31880e3188,0xe31880e31880e,0x51680e52d40e51,0x690e51690e5169,0xe516933816a33,0x816a2720000000,0x494000000000]) []
def stateEntry121 : Entry := row 5 [0xa000aa,0xf0f0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x1842a519418400,0x2a12a50e30e52,0x712710e516a272,0x27216a32900000,0x2a52c62a52,0xc60e31801840e3,0xe51691690e516,0x216216a1843311,0x84331184000000,0x1630000e10e10e,0x31690e31880e31,0x6a0000002d2000,0xe31880e31880e,0x51680e52d42710,0xe52710e50e5169,0xe516927216a27,0x216a0e60000000,0x497000]) []
def stateEntry122 : Entry := row 5 [0xa0ecaaee,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (packWords [0x163263194163,0xe32631980e30e,0x52612630e50e62,0x622630e626334a,0x2633290e316318,0x40e30e51611630,0xe50e61621630e6,0x1631841631840e,0x10e10e31690e20,0xe20e31880e3188,0xe31880e50e60e,0x53380e52710e53,0x580e616a0e6338]) []
def stateEntry123 : Entry := row 5 [0xaa00aa,0xaaaaaaaa,0xc0c0cccc,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x1842a51941840e,0x32a11980e32612,0x612712a52c62a5,0x26326316a2c62a,0x516a2a52c62a52,0xc60e31801840e3,0x1c61841c61841c,0x61841c61841620,0x16a184000000,0x1630000e31880e,0x31880e31880e31,0x880e31880e316a,0xe31880e31880e,0x50000000002711,0x6a16a338271358,0x27135833816a16,0xa33841c40c8004,0xc0e6000000000]) [(122,2)]
def stateEntry124 : Entry := row 5 [0xaa00aa,0xf0f0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 7 (packWords [0x4c81841842a535,0x22a54c83521942,0xa5184184000000,0x4864862a12a,0x54872a54860e30,0xe32c60e50e52a5,0x2712712c627127,0x12a50e50e52a51,0x6a16a2c63382c6,0x2a53382a52c616,0xa16a4864aa2630,0x0,0x2a,0x54872a52c64062,0xc62a54062a52c6,0x4872c61840e30e,0x33521881801841,0x881843520e30e3,0x1c60e50e518416,0x91691c61691691,0x840e50e54c74c7,0x1620000000004c,0x716a16a1844c81,0x84352404352184,0x4c81843524c835,0x21844041840000,0x0,0x4c74c716300000,0xe31690e11,0x880e50e10e30e5,0xe31881691690e,0x316a0e31884861,0x880e34c70e3188,0x16a16a00000000,0x4874,0xc52b1000000000,0xe34000e318848,0x61880e34860e31,0x884001880e5338,0xe52d416a1680e,0x516a0e52d43382,0xd42718082710e5,0x4310e527143127,0x10e58070e50e58,0x60e51694ad169,0xe54ad0e516980,0x51693384c73381,0x6a40a16a33840a,0x33816a4c716a4c,0x84c70e60000000,0x0,0x80440140,0x140c80340c8028,0x180040c40140c]) [(118,0),(119,0),(120,1),(121,1),(90,1),(18,1),(75,3),(101,3),(123,1)]
def stateEntry125 : Entry := row 5 [0xaa00aa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 8 (packWords [0x404329,0x18418440426335,0x22634043293521,0x94404263184184,0x80c2a50e30e348,0x62632b12634872,0xa52b1198486263,0xe30e34312630e,0x50e54872a52712,0x61431263271263,0x80b2a50e50e540,0xa26316a16a40a2,0xc63382c640a263,0x33826340a2c616,0xa16a80a2638092,0x634872c64062c6,0x48726340626340,0xc2c68082c64041,0x840e30e3486352,0x18818040418418,0x81844863520e30,0xe34311c60e50e5,0x40418416916943,0x11c61691694041,0x840e50e540a40a,0x40a16200000000,0x40a40a16a1,0x6a40a184404184,0x0,0x40a4,0xa40a163000000,0x4310e316,0x90e18071880e50,0xe14310e30e50e3,0x48618816916940,0xa0e316a0e340a1,0x8880618840a0e3,0x40a0e340a18816,0xa16a4860e34000,0xe340c188805188,0x8040e38030e348,0x618840018840a0,0xe53380e540a2d4,0x16a16840a0e516,0xa0e540a2d43382,0xd48020e58010e5,0x43116942016943,0x10e54200e540c1,0x6980016940a404,0x40a0e600000000,0x0,0x0]) [(19,1),(76,3),(83,1),(86,1),(91,1),(94,1),(97,1),(104,1),(105,1),(106,3),(109,1),(117,1),(124,1)]
def stateEntry126 : Entry := row 5 [0xaaaaaaaa,0xeeecaaa0,0xf0f0f0f0,0xff00ff00,0xffffcccc] 4 (packWords [0x1690e516,0x90e50e51690e51,0x690e52610e5410,0xe52720e52c518,0x1801842d21631,0x631a5184172172,0x1a51840e30e31a,0x91880f20f21a91,0x880e60e62632c6]) []
def stateEntry127 : Entry := row 5 [0xaaaaaaaa,0xcccccccc,0xeeeaccc0,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (packWords [0x1842c6194184,0x1882b119818826,0x32632c640a2c62,0x7127144c0e62c6,0x8000e618018018,0x42b11631631c61,0x841c61841c6184,0xe616a16a0e60e,0x30e31ca1881ca1,0x881ca18816a0e6,0xe616a0e50e527,0x141c2720e60e64,0x62710e60e644c]) [(126,2)]
def stateEntry128 : Entry := row 5 [0xaaa0aaa0,0xaaaaaaaa,0xcccc0000,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x1842a519418418,0x82d21981880e52,0xa5444000263000,0x2a527227,0x24102a54062a54,0x101801801842d2,0xe51691690e535,0x21843521841a51,0x841a5184163163,0x1a51841690e50e,0x51692d21882d21,0x881a91881a9188,0xe30e31a918827,0x10000000000e52,0x720e54100e5420,0xe541044227227,0x240c41c40c8004,0xc0e6000000000]) [(127,2)]
def stateEntry129 : Entry := row 5 [0xaaa0aaa0,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 7 (packWords [0x4ca329,0x1841844ca26335,0x22634ca3293521,0x944ca263184184,0x4c92a51881884c,0x92632d22634c92,0xa52d21984c9263,0x1881884442630e,0x50e54cb2a52712,0x61444263271263,0x8002a50e50e544,0x22634422624422,0xc6272262442263,0x2722634422c640,0xc2c640c2a540f2,0xa54cb263406263,0x4cb2a54062a540,0xc26340c2634c91,0x842d21804c9352,0x18818044218418,0x81844c93522d22,0xd24441c60e50e5,0x4ca18416916944,0x41c61691694ca1,0x840e50e54421a5,0x2721a54421844c,0xa1844421a54421,0xa5442184272184,0x4421a540a1634c,0x91844511634421,0xa54421a5442184,0x40a1844441ca16,0x91694c91880e50,0xe54441ca0e50e5,0x4c918816916944,0x21a92721a94421,0x884c91884421a9,0x4421a944218827,0x21884421a940a0,0xe34c91884500e3,0x4421a94421a944,0x218840a1884420,0xe54420e54422d4,0x2722704420e527,0x20e54422d440c2,0xd440c0e541c0e5,0x44427142027144,0x40e54200e540c2,0x7140c27144240c,0x4420e600000000,0x0,0x0]) [(128,1)]
def stateEntry130 : Entry := row 5 [0x222a222a,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xfff0fff0,0xffff0000] 6 (packWords [0x2a52632a526318,0x42631941841882,0x63198188261261,0x2632a50e62c626,0x30e62632c62632,0xc6331000000000,0x2b100000000027,0x12d42d427143e0,0xe60e640c43e442,0x40a41f18418800,0x4cc1c41841861,0x840e616a16a0e6,0x1a51841a51841c,0x818818a18816a0,0xe60e616a1a9188,0x1a91880e40e40e,0x62d42712d40e50,0xe5272000000000]) []
def stateEntry131 : Entry := row 5 [0xaaa0aaa0,0xaaaaaaaa,0xccc0ccc0,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x18426319418418,0x82631981882612,0x612632a52c6263,0x2c626326226226,0x32c62a52632a52,0x631801801844cd,0x1c61841c61841c,0x61841c61841a51,0x841a51841a5184,0x1a51841ca1881c,0xa1881ca1881ca1,0x881a91881a9188,0x1a91881a91880e,0x50000000002702,0x7027180041c271,0x44127127240c44,0x227240a41f4424,0x3e0e6000000000]) [(29,1)]
def stateEntry132 : Entry := row 5 [0x222aaaaa,0xcccccccc,0xf000f000,0xfff0fff0,0xffff0000] 4 (packWords [0xe32632a,0x50e31842631941,0x840e52612630e5,0xe62622630e618,0xe10,0xe10e32710e20e2,0xe32720e518418,0x60e50e61841850,0xe60e40e40e52b4]) []
def stateEntry133 : Entry := row 5 [0x222aaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xfff0fff0,0xffff0000] 5 (packWords [0x2a52632a5263,0x18426319418418,0x82631981880e52,0x612630e50e6262,0x2630e616300000,0xe30000000,0x2710e50e5271,0x2720e60e627218,0x41880008000e51,0x691690e50e616a,0x16a0e61690e50e,0x516916a0e60e61,0x6a0e40e40e52b4]) [(132,1)]
def stateEntry134 : Entry := row 5 [0xaaa00000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xfff0fff0,0xffff0000] 6 (packWords [0x2c62632c626318,0x42631941841882,0x631981880e5261,0x2630e50e626226,0x30e62a50000000,0x163000000000,0xe300000000027,0x10e50e52712720,0xe60e62724d1000,0x18418800,0x4d00e51691690,0xe50e616a16a0e6,0x4cf18440018416,0x90e50e516916a0,0xe60e616a4ce188,0x4041880e40e40e,0x52d48000e54410,0xe52b4000000000]) [(133,2)]
def stateEntry135 : Entry := row 5 [0x333f0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xfff0fff0,0xffff0000] 6 (packWords [0x2c64d42c640f18,0x42c634a1841883,0x4a2c61880e5271,0x2710e50e627227,0x20e62630000000,0x163000000000,0xe300000000027,0x10e50e52712720,0xe60e627244144f,0x4d342018418800,0x4d20e51691690,0xe50e616a16a0e6,0x39418439418416,0x90e50e516916a0,0xe60e616a398188,0x3981880e40e40e,0x52b42710e52710,0xe52720e62720e6]) []
def stateEntry136 : Entry := row 5 [0xaaa0aaa0,0xaaaa0000,0xcccccccc,0xf000f000,0xfff00000] 4 (packWords [0x1802c219,0x41800e52c02c20,0xe52622a5440262,0xe22b14400e20e,0x51801820e52621,0x801911800e2180,0x1850e22600e526,0x20e50e00e00e22,0x710e22624d50e2]) []
def stateEntry137 : Entry := row 5 [0xaaa0aaa0,0xaaaa0000,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xfff00000] 5 (packWords [0x1842c6194184,0x1882c21981880e,0x52c42c60e52622,0xa54422620e62c6,0x4420e618018018,0x48000e51691690,0xe526218426a184,0xe616216a0e616,0x90e50e51692621,0x882661880e20e2,0xe616a2600e526,0x20e50e40e40e52,0x710e62624370e6]) [(136,1)]
def stateEntry138 : Entry := row 5 [0xaaa0aaa0,0xaaaa0000,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xfff0fff0,0xffff0000] 6 (packWords [0x2c64cb2c680018,0x42c61941841883,0x4a1981880e5271,0x2710e526200000,0xe62c64370,0xe6352000000000,0x2d200000000027,0x10e50e52712724,0xc40127240a000,0x18418800,0x4d70e51691690,0xe5272184403184,0xe616a16a0e616,0x90e50e51692721,0x8840118816a0e6,0xe616a2700e527,0x10e50e40e40e52,0x710e62724d60e6]) [(137,1)]
def stateEntry139 : Entry := row 5 [0xaaa0aaa0,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xfff00000,0xffff0000] 6 (packWords [0x2a500000000018,0x42633941841882,0x633981880e5261,0x2630e526226226,0x380040f2634372,0x63184352394184,0x1882d23981880e,0x52d42d40e52724,0xc44227240a4d1,0x44244e18018018,0x44d80e51691690,0xe51a51841a5184,0x1631631a518416,0x90e50e51691a91,0x881a91880e30e3,0x1a91880e52700e,0x52d40e52710e52,0x710e6000000000]) [(137,1)]
def stateEntry140 : Entry := row 5 [0xaaa0aaa0,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xfff0fff0,0xffff0000] 7 (packWords [0x2a54012a52634c,0xb2632a54cb2a52,0x63807263329184,0x18426339426332,0x93941942631841,0x842a5188188263,0x3982632a539819,0x82631881882630,0xe50e52a5271261,0x2632712632a50e,0x50e52634422622,0xc6272262263272,0x2632c68062c62a,0x58052a52634372,0x632a54372a5263,0x8042634c94c935,0x20000000000000,0x0,0x4c94ca2d200000,0x0,0x444271,0x2714010e50e544,0x40e50e58032712,0x71442272272442,0x40140c44244244,0x20000000004424,0x4240a000000000,0x0,0x1844ca1844,0xc9188188000000,0x4c94c94c91c,0x60e50e51841691,0x691c6169169184,0xe50e51a52721a,0x51844ca1841a54,0x421a5184272184,0x1a54421a518440,0x1841a54421a51,0x844421841ca169,0x1691880e50e51c,0xa0e50e51881691,0x691a92721a9188,0x4c91881a94421a,0x91882721881a94,0x421a91884c9188,0x1a94421a918844,0x21880e54420e52,0xd42722700e5272,0xe52d48022d40e,0x58010e52714412,0x710e54410e5271,0x8002714014420e,0x60000000000000,0x0]) [(22,1),(130,2),(30,1),(131,1),(134,1),(135,2),(138,1),(139,1)]
def stateEntry141 : Entry := row 5 [0xaaaaaaaa,0xbbb03330,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (packWords [0x163263194163,0xe32631980e326,0x12612632a52a52,0x632a52630e6262,0x2630e60e316318,0x40e31611611631,0x84184163184163,0xe61621630e60e,0x10e10e31881880,0xe31880e30e20e2,0xe316a40c2710e,0x50e52700e60e62,0xb40e62b42b40e6]) []
def stateEntry142 : Entry := row 5 [0x2222aaaa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xfff0fff0,0xffff0000] 6 (packWords [0x2a54db2a540f18,0x42a51941841883,0x291981880e52a5,0x2c60e526226227,0x22c62a52c62632,0x63163000000000,0xe30000000004d,0xa0e50e541c2724,0xc42b27280040c,0x40140c18418800,0x4d90e51691690,0xe51a51841a5184,0x1a51841a518416,0x90e50e51691a91,0x881a91881a9188,0x1a91880e52700e,0x52d40e52d40e52,0x710e6000000000]) [(141,2)]
def stateEntry143 : Entry := row 5 [0xaaaa8888,0xfcfcf0f0,0xffccff00,0xfff0fff0] 3 (packWords [0x16,0x316318444c0e30,0xe318844c1f20e4,0xe419218418818,0x48000e41681680,0xe41680e40e4168]) [(40,1)]
def stateEntry144 : Entry := row 5 [0xaaaaaaaa,0xfcfcf0f0,0xffccff00,0xfff0fff0,0xffffcccc] 4 (packWords [0xe51d20e,0x51921690e51690,0xe50e51690e5169,0xe40e40e580016,0x31631844dc0e30,0xe31884dd1f20e6,0xe61d218418818,0x44dc0e616a16a0,0xe616a0e60e616a]) [(143,1)]
def stateEntry145 : Entry := row 5 [0xaaaaaaaa,0xcccccccc,0xfafaf0f0,0xffaaff00,0xfff0fff0,0xffff0000] 5 (packWords [0x2c62b11b11b1,0x1842a519418418,0x82a91981880e52,0x712710e50e62c6,0x8000e616316318,0x44de0e30e31884,0xa72710e50e5271,0x2b10e60e639118,0x41881844de0e51,0x691690e50e616a,0x16a0e61690e50e,0x516916a0e60e61,0x6a0e40e40e52d4]) [(144,2)]
def stateEntry146 : Entry := row 5 [0xaaaa0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffaaff00,0xfff0fff0,0xffff0000] 6 (packWords [0x2c63312c640f18,0x42c61941841883,0x4a1981880e5271,0x2710e50e62c64e,0x10003290000000,0x1631631844e0,0xe300000000027,0x10e50e52713310,0xe60e640c33140c,0x33140c18418818,0x44de0e51691690,0xe50e616a16a0e6,0x4cf00000000016,0x90e50e516916a0,0xe60e616a4df188,0x8001880e40e40e,0x52d42710e52710,0xe5338000000000]) [(145,1)]
def stateEntry147 : Entry := row 5 [0xaaa8aaa0,0xcccc0000,0xf0f0f0f0,0xff00ff00,0xffffcccc] 4 (packWords [0x1690e516,0x90e50e51690e51,0x692c4000000000,0xe40e40e541018,0x1801842d22c61,0x8434a1840e6162,0x16a0e62c21882c,0x61880e20e20e61,0x6a0e62622720e6]) []
def stateEntry148 : Entry := row 5 [0xaaa8aaa0,0xcccc0000,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (packWords [0x1842a5194184,0x1882d21981880e,0x52a58000002c60,0xe6272,0x2720e618018018,0x42d20e51691690,0xe5352184352184,0xe616216a0e616,0x90e50e51692d21,0x882d21880e20e2,0xe616a2d400000,0xe40e40e52,0xb40e62722720e6]) [(147,1)]
def stateEntry149 : Entry := row 5 [0xaaaa0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xfffafff0,0xffff0000] 6 (packWords [0x2c64d12c640a18,0x42c61941841882,0xb11981880e5271,0x2710e50e62c64d,0x30002a50000000,0x163000000000,0xe300000000044,0x80e50e580040a0,0xe60e64064d1000,0x18418818,0x42b10e51691690,0xe50e616a16a0e6,0x33118433118416,0x90e50e516916a0,0xe60e616a2b1188,0x2b11880e40e40e,0x52d42710e52710,0xe52b4000000000]) [(148,2)]
def stateEntry150 : Entry := row 5 [0x3330fff0,0xaaaa0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00] 5 (packWords [0x1841881842c2,0xe51691690e50e,0x616a16a0e62631,0x84329184163163,0x1842c61690e50e,0x516916a0e60e61,0x6a2631882a5188,0xe30e31882c20e,0x40e40e58002610,0xe52630e50e5271,0xe527126200000,0xe640a0e62,0xc62a52632a5263]) [(36,1)]
def stateEntry151 : Entry := row 5 [0x3330fff0,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x32918418,0x42633522633293,0x52194263184184,0x2a51881882632d,0x22632a52d21982,0x631881882630e5,0xe52a527126126,0x32712632a50e50,0xe52630e60e64e8,0x27226226327226,0x38010e60e62a54,0x202a52634d1263,0x2a54d32a526342,0x2631842d21843,0x52188188184188,0x1843522d22d21c,0x60e50e51841691,0x691c6169169184,0xe50e51a50e60e,0x618416a16a1a51,0x6a16a1840e60e6,0x1844ba1633524e,0x71631844e61843,0x524463521ca169,0x1691880e50e51c,0xa0e50e51881691,0x691a916a16a188,0xe60e61a90e60e,0x618816a16a1884,0xe50e32d24e40e3,0x1884e31882d244,0x52d20e52b40e44,0xe20e60e40e50e6,0xe58002b42b40e,0x54e20e527141f2,0x710e54160e5271,0x4e22710e640c0e,0x627240a2720e64,0xa0e627240c272]) [(37,1),(150,1)]
def stateEntry152 : Entry := row 5 [0x3330fff0,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xfff0fff0,0xffff0000] 6 (packWords [0x2a52632a526318,0x42631941841882,0x631981880e5261,0x2630e50e626226,0x30e62a52632a52,0x63352000000000,0x2d200000000027,0x10e50e52712720,0xe60e62724ec000,0x18418800,0x4eb0e51691690,0xe50e616a16a0e6,0x1844001844ea16,0x90e50e516916a0,0xe60e616a188404,0x1884e90e40e40e,0x52b40e52710e52,0x710e62720e6272]) []
def stateEntry153 : Entry := row 5 [0x3330fff0,0xaaaaaaaa,0xcccc0000,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x1842a519418418,0x82d21981880e52,0xa54e2000263000,0xe627227,0x20e62a54e22a54,0x201841881842d2,0xe51691690e535,0x21843521840e61,0x6a16a0e6163163,0x1843521690e50e,0x51692d21882d21,0x8816a0e60e616a,0xe30e31882d227,0x10000000000e40,0xe40e52b40e5420,0xe54060e627227,0x20e60000004ed0,0xe62720e6272]) []
def stateEntry154 : Entry := row 5 [0xaaaa0000,0xaaaaaaaa,0xcccc0000,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xfff0fff0] 6 (packWords [0x1630000000000e,0x30000000004480,0xe50e544c8022c6,0x2c644c42b0e60e,0x64108012a52a54,0x101841880004ee,0xe51691690e52c,0x618434a1840e61,0x6a16a0e62a5184,0x3291841690e50e,0x516934a1882c61,0x8816a0e60e616a,0x3291882a518827,0x10000000000e40,0xe40e58002a50e5,0x4410e50e62c644,0x20e62632634422,0xa5272000000000]) [(44,1),(150,2),(150,1)]
def stateEntry155 : Entry := row 5 [0xaaaa0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xfff00000,0xfff0fff0] 6 (packWords [0x4d100000000016,0x30000000000e30,0x2710e5,0xe527144e0e60e,0x68002634014012,0x631842c6194184,0x18834a1981880e,0x52c42c60e50e62,0xc64420e62632a5,0x44226318418800,0x4ef0e51691690,0xe50e616a16a0e6,0x26318440318416,0x90e50e516916a0,0xe60e616a263188,0x4011880e40e40e,0x52d42610e52630,0xe5262000000000]) [(137,1)]
def stateEntry156 : Entry := row 5 [0xaaaa0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xfff0fff0,0xffff0000] 7 (packWords [0x2c64372c643740,0x64062c64062c68,0xe43740f34a184,0x1842c63942c634,0xa3941942c61841,0x842c618818834a,0x39834a2c639819,0x834a1881882c60,0xe50e5437271271,0x2c627127180d0e,0x50e54420e60e62,0xc64372c6442442,0x44200000000044,0x24422630000000,0x0,0x4514de16,0x30000000000000,0x0,0x4504a70e300000,0x0,0x448271,0x27180c0e50e544,0x80e50e580b2712,0x7140a44240a442,0xe60e640a0e60e,0x644280a40c8098,0x880740c40140c,0x80640140140c80,0x540c1844a71844,0xde188188000000,0x4de4de4de1c,0x60e50e51841691,0x691c6169169184,0xe50e51a50e60e,0x618416a16a1a51,0x6a16a1840e60e6,0x4a74044041844a,0x71848044a74031,0x844041841ca169,0x1691880e50e51c,0xa0e50e51881691,0x691a916a16a188,0xe60e61a90e60e,0x618816a16a4de4,0x4001884de188,0x8034de40118840,0x1880e54420e42,0xd40e60e40e50e6,0xe52d48022d427,0x18012710e54410,0xe52714412710e5,0x8000e543744227,0x20000000000000,0x0]) [(33,1),(142,2),(45,1),(146,0),(146,1),(134,1),(149,1),(151,2),(152,2),(153,2),(138,1),(128,2),(93,2),(154,1),(155,1)]
def stateEntry157 : Entry := row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xfff00000,0xffff0000] 7 (packWords [0x437401,0x46e2a500000000,0x0,0x0,0x4f14f11631634f,0x12633942634f14,0xf13943944f0263,0x1631634f04f00e,0x30e34f02633982,0x634f04f0398398,0x4f02630e30e34e,0xc2630e50e54374,0x372712614ec263,0x27126343740f0e,0x50e544e2630e60,0xe6437437272262,0x44e26327226343,0x740f0e60e64f04,0x1631634f14b5,0x3943314f040039,0x43944f04761631,0x634f04f00e30e3,0x4f04ab3982b14f,0x4f03983984f04,0xaa0e30e34ec420,0xe50e540f41c2d,0x42d44ec4202d42,0xd440f41c0e50e5,0x44e40a0e60e640,0xf40c2b42b444e4,0xa2b42b440f40c,0xe60e64f01840e,0x30e34f01631881,0x634f0184188184,0x4f01630e30e34e,0xc1630e50e54f11,0x841691614ec163,0x1691634f11840e,0x50e544e1630e60,0xe64f118416a162,0x44e16316a1634f,0x11840e60e64ec0,0xe31690e14f0188,0xe50e14ec0e30e,0x50e34f01881691,0x6944e0e316a0e2,0x4f01880e60e244,0xe0e30e60e34f01,0x8816a16a44e0e5,0x2b40e44ec2d40e,0x60e444e0e50e60,0xe58002d42b42b4]) [(48,1)]
def stateEntry158 : Entry := row 5 [0xaaaaa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xfff0fff0,0xffff0000] 6 (packWords [0x2c62632c626318,0x42631941841882,0x631981880e5261,0x2630e52632a426,0x32c62632c62632,0xa5163000000000,0xe300000000027,0x10e50e527144e2,0xb42b440c44e442,0x40a4d118418800,0x4f20e51691690,0xe51a51841a5184,0x1a51841a518416,0x90e50e51691a91,0x881a91881a9188,0x1a91880e52d40e,0x52b40e52d40e52,0xd40e6000000000]) []
def stateEntry159 : Entry := row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xfff00000,0xfff0fff0,0xffff0000] 7 (packWords [0x40143740126343,0x72634374374370,0x40146e,0x2a500000000000,0x0,0x4f1184184263,0x3942634f139439,0x42631841844f01,0x88188263398263,0x4f039839826318,0x81882630e50e54,0x37271261263271,0x2638070e50e526,0x30e60e64372722,0x62263272263806,0xe60e64374f34f,0x30000000000000,0x0,0x4f04f016300000,0x0,0x4f04f1,0xe300000000000,0x0,0x4ec271271401,0xe50e54ec0e50e,0x580527127144e2,0x722724010e60e6,0x44e0e60e680427,0x22724001841844,0xf3394394400394,0x3944f01841844f,0x1881884003983,0x984f0398398400,0x1881884410e50e,0x58032d42d44412,0xd42d48020e50e5,0x4420e60e68012b,0x42b44422b42b48,0xe60e61844f1,0x1844f018818800,0x4f04f04,0xf01c60e50e5184,0x1691691c616916,0x91840e50e51a50,0xe60e618416a16a,0x1a516a16a1840e,0x60e61ca1691691,0x880e50e51ca0e5,0xe51881691691a,0x916a16a1880e60,0xe61a90e60e6188,0x16a16a0e52b40e,0x42d40e60e40e50,0xe60e52d42b42b4]) [(134,1),(158,1),(134,2),(158,2),(139,1),(139,2),(155,1),(155,2)]
def stateEntry160 : Entry := row 5 [0xf0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 7 (packWords [0x46e329,0x1631634c82a539,0x42a54c83293941,0x944c82a5163163,0x46e2a50e30e346,0xe3293982a146e2,0xa539819846e329,0xe30e34f42c60e,0x50e54372a52712,0x714f42c6271271,0x4372a50e50e544,0xf2a50e60e64372,0xc627227244f2a5,0x2722724372c60e,0x60e64374014f02,0x63000000000000,0x0,0x46e1,0x840e30e346e163,0x18816346e18418,0x818446e1630e30,0xe34f41630e50e5,0x4c81841691614f,0x41631691634c81,0x840e50e544f163,0xe60e64c818416,0xa16244f16316a1,0x634c81840e60e6,0x0,0x4c84,0x14f5331000000,0x4f40e316,0x90e146e1880e50,0xe14f40e30e50e3,0x46e18816916944,0xf0e316a0e246e1,0x880e60e244f0e3,0xe60e346e18816,0xa16a0000000000,0x0,0x46e40146e2b100,0x44f0,0xe52b40e44f42d4,0xe60e444f0e50e,0x60e58002d42b42,0xb440127141c271,0x4f40e54200e54f,0x42714202714010,0xe541c0e5401272,0x40c27244f0e640,0xa0e644f27240a2,0x724010e640c0e6]) [(50,1)]
def stateEntry161 : Entry := row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xfff0fff0,0xffff0000] 8 (packWords [0x4012a5,0x80b2a543726340,0x62634372a54062,0xa580a263809263,0x40432918418440,0x42633942634043,0x29394194404263,0x1841844002a518,0x81884002633982,0x634002a5398198,0x40026318818844,0x12630e50e54372,0xa5271261441263,0x2712638082a50e,0x50e54422630e60,0xe64372c6272262,0x44226327226380,0x72c60e60e64004,0x400163000000,0x0,0x0,0x4004004040e3,0x0,0x0,0x441420,0x2712714018060e,0x50e54414200e50,0xe5805804271271,0x44240a27227240,0x18030e60e64424,0xa0e60e6802801,0x27227240018440,0x41844004001881,0x88000000000000,0x40040040040044,0x11c60e50e54041,0x841691694411c6,0x1691694041840e,0x50e54421a50e60,0xe640418416a16a,0x4421a516a16a40,0x41840e60e64411,0xca169169400188,0xe50e54411ca0e,0x50e54001881691,0x694421a916a16a,0x4001880e60e644,0x21a90e60e64001,0x8816a16a4420e5,0x2b40e44412d40e,0x60e44420e50e60,0xe58002d42b42b4]) [(51,1),(129,1),(140,1),(94,1),(129,2),(140,2),(94,2),(156,1),(156,2),(157,1),(159,1),(160,1)]
def stateEntry162 : Entry := row 5 [0x2222aaaa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 7 (packWords [0x4db329,0x1631634f62a533,0x12a54db3293311,0x944f62a5163163,0x4db2a50e30e34d,0x93292b12a14db2,0xa52b11984d9329,0xe30e34da2c60e,0x50e54da2a52d42,0xa54da2c62d42c6,0x42b2a50e50e542,0xb2a542b26242b2,0xc627226242b2a5,0x27227242b2c64d,0xb2c642b2a542b2,0xa542b2c640a2c6,0x42b2a540a2634d,0xa2c644a2634f61,0x840e30e34d9163,0x18816380018418,0x81844d91630e30,0xe34da1630e50e5,0x4da1841691614d,0xa1631691634da1,0x840e50e542b163,0x27216342b18440,0xc18442b16342b1,0x6342b184272184,0x4f616340416340,0xc18440c18440c1,0x634031634f6184,0x4041844da0e316,0x90e14da1880e50,0xe14da0e30e50e3,0x4da18816916942,0xb0e32720e342b1,0x8840c18842b0e3,0x42b0e342b18827,0x21884d90e34000,0xe340c18840c188,0x40c0e34010e34d,0x918840018842b0,0xe542b0e542b2d4,0x27227042b0e527,0x20e542b2d44da2,0xd442b0e542b0e5,0x42b2d440a2d442,0xb0e540a0e54da2,0xd442d27142b40c,0x42b0e600000000,0x0,0x0]) [(142,1)]
def stateEntry163 : Entry := row 5 [0xaaaa0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xf4f4fcfc,0xff00ff00,0xffff0000] 6 (packWords [0x1632c61941632c,0x64f82c64aa0e32,0xc22c60e30e5271,0x2710e50e62c64f,0xa0002a50000000,0x163331163331,0xe31631840e30e,0x51841630e50e61,0x621630e6331163,0x33116318800000,0x1690e50e52,0x7140a0e60e64f9,0x4f84c74274aa0e,0x30e50e318a0e20,0xe20e316a4f70e3,0x4010e30e40e40e,0x52d42710e52710,0xe52b4000000000]) []
def stateEntry164 : Entry := row 5 [0x2222aaaa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xfcfcf0f0,0xff00ff00,0xffff0000] 6 (packWords [0x1632a51941632a,0x53292a53292a52,0xd22a53290e52a5,0x2c60e52a527227,0x22c62a52c62a52,0xc6184163184163,0x1841631841630e,0x51611630e51631,0x84163184163184,0x1631840e300000,0x1690e50e51,0x6942b27227240c,0x42b42e40a44516,0x90e50e51692722,0xd242e2724be2d2,0x4012d20e52720e,0x52d40e52d40e52,0xd40e6000000000]) []
def stateEntry165 : Entry := row 5 [0x2222aaaa,0xaaaaaaaa,0xcccc0000,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 7 (packWords [0x3291631632a533,0x12a53293311942,0xa51631632a50e3,0xe33292b12a12a,0x52b11983290e30,0xe34da0e50e52a5,0x4db2a54da4da4d,0xa0000000004da4,0xda2c6000000000,0x0,0x2a542b2a54,0x2b2722722a5272,0x27242b4db40f2a,0x542b2a542b42b4,0x2b2a542b2a54da,0x4204201840e30e,0x31631881631841,0x881841630e30e3,0x1630e50e518416,0x91611631691631,0x840e50e53524f6,0x35216341c16335,0x28073521634f61,0x63163272163184,0x80618416342b16,0x31842721841634,0xbf163184805184,0x1638041631844b,0xf1840e31690e11,0x880e50e10e30e5,0xe31881691692d,0x24d92d20e341c0,0xe32d28032d20e3,0x4d90e30e32720e,0x31888021880e34,0x2b0e3188272188,0xe34be0e318880,0x11880e38000e31,0x884be1884db4da,0x2d400000000000,0x0,0xe542b0e542b,0x2722720e52720e,0x542b4da41c0e54,0x2b0e542b42b42b,0xe542b0e54db4d,0xa40642b42b42b0,0x42b272,0x27242b41c40c00,0x0,0x42b42b40a000,0x41c42b0e,0x60000000000000,0x0]) [(163,2),(113,0),(114,0),(164,1),(163,3),(113,1),(114,1),(164,0)]
def stateEntry166 : Entry := row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xfafaf0f0,0xff00ff00,0xffff0000] 7 (packWords [0x4fd34a,0x1631634fc2a533,0x12a54fd34a3311,0x944fc2a5163163,0x4c52a540a2634d,0xe34a4ab2634c52,0xa54c52a54c534a,0x40a34a4de2a54f,0xd2a54de34a2b12,0xb14c52a52b12a5,0x4de34a4de34a4f,0xb2c60e50e54fd2,0xa52712714fb2c6,0x2712714fd2a50e,0x50e54c52a50e60,0xe64c52c62b42a4,0x4c52a52b42a54c,0x52c60e60e64fc1,0x84404184401163,0x40316340118440,0x11844fc1634041,0x634de1842b1184,0x4de1634de1634d,0xe1844011844de1,0x632b11634fb163,0xe50e580018416,0x91614fb1631691,0x634fc1840e50e5,0x4c51630e60e64c,0x518416a1624c51,0x6316a1634c5184,0xe60e64de4c740,0xc0e30000000000,0x0,0x4f,0xb4201691694014,0x1c0e50e54fb420,0xe50e540141c16,0x91694c540a16a1,0x6a4c54c50e60e6,0x4c540a0e60e64c,0x54c516a16a4fb4,0xfb1691694de2b1,0xe50e54fb4fb0e,0x50e54de2b11691,0x694c52b116a16a,0x4c54c50e60e64c,0x52b10e60e64c54,0xc516a16a4c50e5,0x2b40e44c52d40e,0x60e44c50e50e60,0xe54c52d42b42b4]) [(116,2)]
def stateEntry167 : Entry := row 5 [0xa8a8a0a0,0xaaaaaaaa,0xcccc0000,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x1632a519416318,0x82d21981880e52,0xa54fe0002c6000,0x16a3282a,0x516a2a53292a53,0x29180163184163,0xe51611630e535,0x21633521631621,0x621631841a5163,0x1a51631690e50e,0x51692d21882d21,0x8816a18818916a,0xe30e342e1882d,0x40000000000e51,0x680e53380e5169,0xe516916a40c42,0xe16a40a44542e4,0x2b0e6000000000]) []
def stateEntry168 : Entry := row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xfafaf0f0,0xff00ff00,0xffaaff00,0xffff0000] 6 (packWords [0x2a52a534a2c634,0xa2c63312c62c63,0x292c634a2c62b1,0x2b134a0e527127,0x10e50e62c64ff0,0xe6163000000000,0x4924c24d346040,0x12b12b14de0e51,0x691690e50e616a,0x16a0e633140333,0x14a72b13318002,0xb10e51691690e5,0xe616a16a0e60e,0x30000000001690,0xe50e516916a0e6,0xe616a1690e50e,0x516916a0e60e61,0x6a0e40e40e52d4]) [(145,1)]
def stateEntry169 : Entry := row 5 [0xfa00f0,0xaaaa0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x1632c634a16318,0x82b11981880e52,0x712710e50e62c6,0x5010002a500000,0x2c634a2c63,0x4a180163188163,0xe51611630e50e,0x61621630e64fc1,0x63403163000000,0x1840001690e50e,0x516916a0e60e61,0x6a2b11882b1188,0xe30e32b11880e,0x40e40e52d42710,0xe52710e50e5169,0xe51692b400000,0xe616a0e61,0x6a4764c2500473]) []
def stateEntry170 : Entry := row 5 [0xaaaa0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xfafaf0f0,0xff00ff00,0xffff0000] 7 (packWords [0x34a1631632c633,0x12c634a3311942,0xc61631632c640a,0x2c634a4ab34a2c,0x64c52c634a40a3,0x4a2c64fd2c634a,0x2b12b12c62b12b,0x134a4de34a2c60,0xe50e54fd271271,0x2c627127140f0e,0x50e54c50e60e62,0xc64fd2c64c54c5,0x4c50000000004c,0x54c52a50000000,0x0,0x1844a718,0x41638061631848,0x51841634a7163,0x1842b11841634d,0xe1631848041841,0x632b11631630e5,0xe518416916116,0x31691631840e50,0xe51630e60e6184,0x16a16216316a16,0x31840e60e63314,0xfc33116340c163,0x3318033311634f,0xc1634c740c0e30,0x0,0x44,0x81691698020e50,0xe54480e50e5801,0x16916940a16a16,0xa4c50e60e640a0,0xe60e64c516a16a,0x4ab4de4ab00000,0x0,0x4fb169,0x1692b10e50e54f,0xb0e50e52b11691,0x692b116a16a4c5,0xe60e62b10e60e,0x64c516a16a2b14,0xde2b140c4de40c,0x4de4d,0xe4de0e54c50e42,0xd40e60e40e50e6,0xe52d440c2d427,0x18002710e54fb0,0xe52714fb2710e5,0x40c0e54fd4c52b,0x40000000000000,0x0]) [(164,2),(167,2),(113,3),(168,1),(146,0),(149,1),(169,1)]
def stateEntry171 : Entry := row 5 [0xaaaa0000,0xaaaaaaaa,0xcccc0000,0xcccccccc,0xf0f0f0f0,0xff00ff00] 7 (packWords [0x502184,0xe30e34ee16318,0x81638011841881,0x844ee1630e30e3,0x4481630e50e544,0x81841691614481,0x63169163448184,0xe50e55023522c,0x62c644c16334a1,0x6340f35234a34a,0x5021632c616342,0xb1630e60e642b1,0x8416a16242b163,0x16a16342b1840e,0x60e65023312a52,0xa5410163329163,0x40f33132932950,0x21632a51634480,0xe31690e1448188,0xe50e14480e30e,0x50e34481881691,0x694ee2d234a2c2,0x44c0e32c60e340,0xf2d22c62c64ee0,0xe334a0e342b0e3,0x16a0e242b1880e,0x60e242b0e30e60,0xe342b18816a16a,0x4ee2b13292a141,0xe32a50e340f2,0xb12a52a54ee0e3,0x3290e344840642,0xd2710000000000,0x0,0x42,0xb0e542b0e442b4,0x2b0e60e442b0e5,0xe60e542b42b44,0x880044840f2a52,0xa54480e54200e5,0x44844842042042,0xb0e52a50e542b4,0xa0e60e642b2c6,0x40f2c642b40a42,0xb40a42b2c60e60,0xe642b40a2a5263,0x4482c642026342,0xb40a42b40a42b2,0xc62a52a542b406,0x42b27200000000,0x0,0x0]) [(62,1),(154,1)]
def stateEntry172 : Entry := row 5 [0xaaaa0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 8 (packWords [0x40634a,0x1631634a72c633,0x12c640634a3311,0x944a72c6163163,0x4062c60e30e34d,0xe34a2b12b14062,0xc62b11984de34a,0xe30e34482c60e,0x50e54064062712,0x714482c6271271,0x40680d0e50e540,0xa40a0e60e640a2,0xc64062c640a40a,0x40a40a00000000,0x40a40a40a2,0x63000000000000,0x0,0x4a71,0x840e30e34de163,0x18816380c18418,0x81844de1630e30,0xe34481630e50e5,0x80b18416916144,0x81631691634a71,0x840e50e540a163,0xe60e640a18416,0xa16240a16316a1,0x6340a1840e60e6,0x4a733140433140,0xc16380a1638093,0x318083314a7163,0x4041634480e316,0x90e18071880e50,0xe14480e30e50e3,0x4de18816916940,0xa0e316a0e240a1,0x880e60e240a0e3,0xe60e340a18816,0xa16a4de2b14002,0xb140c0e38060e3,0x8052b18042b14d,0xe0e34000e340a0,0xe540a0e440a2d4,0xe60e440a0e50e,0x60e540a2d48032,0xd4802271801271,0x4480e54200e544,0x827142027140c0,0xe58000e540a406,0x40a27200000000,0x0,0x0]) [(53,1),(162,2),(165,2),(63,1),(166,1),(170,1),(105,0),(117,3),(166,0),(170,0),(105,1),(117,2),(156,1),(171,1)]
def stateEntry173 : Entry := row 5 [0xa0a0aaaa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 7 (packWords [0x4f934a,0x1631635052a533,0x12a54f934a3311,0x945052a5163163,0x4c72a50e30e350,0x434a2d22a15042,0xa52d219850434a,0xe30e35032c60e,0x50e54f92a52712,0x715032c6271271,0x4f92a50e50e54c,0x72a54c72624c72,0xc62722624c72a5,0x2722724c72c64f,0x92c64c72a54c72,0xa54c72c640a2c6,0x4c72a540a26350,0x42c64aa2635041,0x840e30e3504163,0x18816350418418,0x81845041630e30,0xe35031630e50e5,0x80018416916150,0x31631691635051,0x840e50e54c7163,0x2721634c718433,0x81844c71633381,0x634c7184272184,0x50516340416340,0xc18440c18440c1,0x63403163505184,0x4041845030e316,0x90e15041880e50,0xe15030e30e50e3,0x5041881691694c,0x70e32720e34c71,0x885041884c70e3,0x4c70e34c718827,0x21884c70e340a0,0xe35041884c5188,0x4c70e34c70e34c,0x718840a1884c70,0xe53380e54c72d4,0x2722704c70e527,0x20e54c72d43382,0xd440c0e541c0e5,0x50327142027150,0x30e54200e540c2,0x7140c2714c740c,0x4c70e600000000,0x0,0x0]) [(123,2)]
def stateEntry174 : Entry := row 5 [0xa0a0aaaa,0xaaaaaaaa,0xc0c0cccc,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x1632a51941630e,0x32a11980e32c62,0x712712a52c62a5,0x2c62a52a527227,0x22c62a52c62a52,0xc60e31631840e3,0x16318416318416,0x31841631841631,0x84163184163184,0x1631840e31880e,0x31880e31880e31,0x880e31880e3188,0xe31880e31880e,0x50000000002702,0x7027133841c271,0x4ad27127240c4c,0x727240a5074c75,0x60e6000000000]) []
def stateEntry175 : Entry := row 5 [0xff0000,0x22aa2222,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x3213291630e,0x32b11980e33482,0x712713290e634a,0x3290e632934a32,0x934a2a50000000,0xe31631840e3,0x1631841631840e,0x61621630e61a51,0x631a5163000000,0x3310000e31880e,0x31880e20e20e31,0x6a1a90e31a90e3,0x2b10e32b10e30e,0x40e40e62d42712,0xd40e50e5271358,0x27135827200000,0x40c0e646c0,0xe642f40a46c473]) []
def stateEntry176 : Entry := row 5 [0xa0a0aaaa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xff0fff00,0xffff0000] 6 (packWords [0x34a2a534a2a534,0xa2a53312a50e32,0xa11980e30e5271,0x2710e52a527227,0x22c62a52c62a52,0xc6163000000000,0xe31881880e30e,0x51691690e54c72,0x7227240c4c7508,0x40a4970e318818,0x80e30e51691690,0xe5272330331272,0x4c83314033310e,0x10e10e31690e31,0x880e31880e3188,0xe31880e52700e,0x52d40e52710e52,0x710e6000000000]) []
def stateEntry177 : Entry := row 5 [0xff0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xfaf0fafa,0xff00ff00,0xffff0000] 6 (packWords [0x32132916332,0x934a32934a0e33,0x2950b0e30e5271,0x2710e50e627227,0x20e62a50000000,0x16350a163473,0xe31631840e30e,0x51611630e50e61,0x841630e6000000,0x35200018800000,0x2710e50e52,0x7116a0e60e6272,0x47344f40a4c10e,0x10e10e31690e30,0xe60e31895090e3,0x4010e30e40e40e,0x52b42710e52710,0xe52720e62720e6]) []
def stateEntry178 : Entry := row 5 [0xff0000,0xaa00aaaa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 7 (packWords [0x49649,0x632132950d3294,0x9616316340f0e3,0xe33292b12b150,0xd2b11983290e30,0xe334a0e50e5329,0x27127134a27127,0x13290e50e53294,0x7332934a272272,0x32927227234a50,0xd34a3294733293,0x4a47334a329473,0x32934a40434a49,0x64962c60000000,0x0,0x1840e30e,0x31631881631841,0x881841630e30e3,0x1630e50e518416,0x91611631691631,0x840e50e5163272,0x16318449618416,0x34731631842721,0x84163473163184,0x49618416347316,0x31844731840000,0x0,0x50d49635200000,0xe31690e11,0x880e50e10e30e5,0xe31881691690e,0x32720e31882b41,0x880e32b40e3188,0x2721880e346e0e,0x31888051880e38,0x40e318846e188,0x2b15092b10e340,0x30e32b18032b10,0xe35090e30e52b4,0xe52d42722700e,0x52720e52d42b42,0xb40e58020e5271,0x4742710e54740e,0x52718012712718,0x2710e550c0e5,0x27150c2710e540,0x30e54034730e60,0x0,0x0,0x4734734,0x73272473272403,0x47340c00000000,0x4734,0x7340a000000000]) [(174,0),(68,1),(175,2),(176,0),(177,1),(121,0)]
def stateEntry179 : Entry := row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xf0fff0f0,0xff00ff00,0xffff0000] 7 (packWords [0x46e329,0x16316350f2a539,0x42a550f3293941,0x9450f2a5163163,0x50f2a54f026346,0xe3294ab26346e2,0xa54c52a546e329,0x46e32946e2a546,0xf2a546e3292b12,0xb146e2a52b12a5,0x46e32946e32950,0xe2c60e50e546f2,0xa527127150e2c6,0x27127146f2a50e,0x50e546d2a50e60,0xe646f2c6272272,0x46d2a527227246,0xf2c60e60e646e1,0x8445018446e163,0x46e16350f1844f,0x518446e1634621,0x6346e1842b1184,0x46e16346e16346,0xe18450f18446e1,0x632b116350e163,0xe50e550f18416,0x916150e1631691,0x6350f1840e50e5,0x46d1630e60e650,0xf18416a16246d1,0x6316a16350f184,0xe60e646e46e40,0x10e30000000000,0x0,0x50,0xe4201691694014,0x1c0e50e550e420,0xe50e540141c16,0x916946d40a16a1,0x6a40140c0e60e6,0x46d40a0e60e640,0x140c16a16a50e2,0xd216916946e2b1,0xe50e550e2d20e,0x50e546e2b11691,0x6946d2b116a16a,0x46e2d20e60e646,0xd2b10e60e646e2,0xd216a16a46d0e5,0x2b40e450e2d40e,0x60e446d0e50e60,0xe58002d42b42b4]) [(70,1)]
def stateEntry180 : Entry := row 5 [0xff0000,0xa0aaa0a0,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x32132916318,0x82b11981880e52,0x712710e516a328,0x32916a4b332951,0x3292a50000000,0x180163184163,0xe51611630e516,0x21621631841a51,0x631a5163000000,0x3520001690e50e,0x516916a1881891,0x6a0e30e32b1188,0x2b11882b11880e,0x51680e52d40e51,0x690e51692710e5,0x2710e50e600000,0x40c16a46d1,0x6a4c040a46d473]) []
def stateEntry181 : Entry := row 5 [0xff0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xf0fff0f0,0xff00ff00,0xffff0000] 7 (packWords [0x50f50,0xf32132946f3295,0xf16316350f404,0x40432946e32946,0xe46e46e32946e3,0x2946e46f40f329,0x2b12b146e2b12b,0x132946e32934a0,0xe50e5329271271,0x34a2712713290e,0x50e53290e60e63,0x4a272272329272,0x27234a0e60e650,0xf50f2a50000000,0x0,0x18446e18,0x416346e1631845,0xf18416346e163,0x1842b118416346,0xe16318450f1841,0x632b11631630e5,0xe518416916116,0x31691631840e50,0xe51630e60e6184,0x16a16216316a16,0x31840e60e60000,0x0,0x46f50f39400000,0x46e4030e30,0x0,0x47,0x41691698050e50,0xe54740e50e5804,0x16916947316a16,0xa8030e60e64730,0xe60e680216a16a,0x46e46e40000000,0x0,0x2d2169,0x1692b10e50e52d,0x20e50e52b11691,0x692b116a16a2d2,0xe60e62b10e60e,0x62d216a16a2b14,0x6e2b140346e401,0x46e46,0xe46e0e52b40e42,0xd40e60e40e50e6,0xe52d42b42b427,0x18012710e550e0,0xe527150e2710e5,0x4030e527280027,0x20e646d0e62724,0x6d2720e64030e6]) [(176,0),(176,3),(180,1),(121,0),(180,2),(121,3)]
def stateEntry182 : Entry := row 5 [0xff0000,0xf0f0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00] 7 (packWords [0x46e184,0xe30e346e16318,0x816346e1841881,0x8446e1630e30e3,0x5111630e50e54c,0x81841691615111,0x631691634c8184,0xe50e54721630e,0x60e64c818416a1,0x6247216316a163,0x4c81840e60e64c,0x84c840432146e1,0x633291634c840f,0x3293294c816340,0x41630000000000,0x0,0x4c84064f519400,0x5110,0xe31690e146e188,0xe50e15110e30e,0x50e346e1881691,0x694720e316a0e2,0x46e1880e60e247,0x20e30e60e346e1,0x8816a16a000000,0x0,0x46e40646e1,0x98000000000000,0x46e46e4002a146,0xe0e32a50e346e4,0xf2a52a546e0e3,0x4000e34720e52b,0x40e45112d40e60,0xe44720e50e60e5,0x8002d42b42b440,0xf2713292715110,0xe534a0e5511271,0x34a2714070e532,0x90e540f2712a52,0x715110e52c60e5,0x5112712c627147,0x10e52a50e540f2,0x7234a2724720e6,0x3290e647227232,0x92724070e634a0,0xe640f2722c6272,0x4720e62a50e647,0x22722a52724710,0xe62c60e64c8404,0x2a526346e32940,0x26346e46e4004,0x46e3292a52a5]) [(71,1)]
def stateEntry183 : Entry := row 5 [0xff0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 8 (packWords [0x40440440,0x43214043294063,0x29404404163163,0x40680c0e30e346,0xe3292b12b14064,0x62b119846e329,0xe30e347434a0e,0x50e54063292712,0x7147434a271271,0x4063290e50e547,0x33290e60e64063,0x4a272272473329,0x27227240634a0e,0x60e64044044042,0x63000000000000,0x0,0x4041,0x840e30e346e163,0x18816340418418,0x818446e1630e30,0xe34741630e50e5,0x40418416916147,0x41631691634041,0x840e50e5473163,0xe60e640418416,0xa16247316316a1,0x634041840e60e6,0x0,0x4044,0x6404331000000,0x4740e316,0x90e180b1880e50,0xe14740e30e50e3,0x46e18816916947,0x30e316a0e280a1,0x880e60e24730e3,0xe60e346e18816,0xa16a46e2b14002,0xb14030e38090e3,0x8082b18072b146,0xe0e34000e34730,0xe52b40e44742d4,0xe60e44730e50e,0x60e58062d42b42,0xb4805271804271,0x4740e54200e547,0x42714202714030,0xe58030e5802272,0x8012724730e640,0xa0e647327240a2,0x724030e68000e6]) [(105,1),(173,0),(178,1),(105,2),(173,3),(178,2),(72,1),(179,1),(181,1),(160,1),(124,0),(124,3),(182,1)]
def stateEntry184 : Entry := row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 9 (packWords [0x8093,0x29163163404263,0x33126340632933,0x11944042631631,0x638082a50e30e3,0x4002632b126340,0x62a52b11984002,0x630e30e3420263,0xe50e54062a527,0x12614202632712,0x638072a50e50e5,0x40a2630e60e640,0x62c627226240a2,0x632722638062c6,0xe60e64041840e,0x30e34001631881,0x63805184188184,0x4001630e30e342,0x1630e50e58041,0x84169161420163,0x1691634041840e,0x50e540a1630e60,0xe680318416a162,0x40a16316a16340,0x41840e60e64200,0xe31690e1802188,0xe50e14200e30e,0x50e34001881691,0x6940a0e316a0e2,0x8011880e60e240,0xa0e30e60e34001,0x8816a16a40a0e5,0x2b40e44202d40e,0x60e440a0e50e60,0xe58002d42b42b4]) [(73,1),(125,0),(125,3),(125,1),(125,2),(161,1),(172,1),(172,2),(183,0),(183,1)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def ds : Array Entry := #[stateEntry0,stateEntry1,stateEntry2,stateEntry3,stateEntry4,stateEntry5,stateEntry6,stateEntry7,stateEntry8,stateEntry9,stateEntry10,stateEntry11,stateEntry12,stateEntry13,stateEntry14,stateEntry15,stateEntry16,stateEntry17,stateEntry18,stateEntry19,stateEntry20,stateEntry21,stateEntry22,stateEntry23,stateEntry24,stateEntry25,stateEntry26,stateEntry27,stateEntry28,stateEntry29,stateEntry30,stateEntry31,stateEntry32,stateEntry33,stateEntry34,stateEntry35,stateEntry36,stateEntry37,stateEntry38,stateEntry39,stateEntry40,stateEntry41,stateEntry42,stateEntry43,stateEntry44,stateEntry45,stateEntry46,stateEntry47,stateEntry48,stateEntry49,stateEntry50,stateEntry51,stateEntry52,stateEntry53,stateEntry54,stateEntry55,stateEntry56,stateEntry57,stateEntry58,stateEntry59,stateEntry60,stateEntry61,stateEntry62,stateEntry63,stateEntry64,stateEntry65,stateEntry66,stateEntry67,stateEntry68,stateEntry69,stateEntry70,stateEntry71,stateEntry72,stateEntry73,stateEntry74,stateEntry75,stateEntry76,stateEntry77,stateEntry78,stateEntry79,stateEntry80,stateEntry81,stateEntry82,stateEntry83,stateEntry84,stateEntry85,stateEntry86,stateEntry87,stateEntry88,stateEntry89,stateEntry90,stateEntry91,stateEntry92,stateEntry93,stateEntry94,stateEntry95,stateEntry96,stateEntry97,stateEntry98,stateEntry99,stateEntry100,stateEntry101,stateEntry102,stateEntry103,stateEntry104,stateEntry105,stateEntry106,stateEntry107,stateEntry108,stateEntry109,stateEntry110,stateEntry111,stateEntry112,stateEntry113,stateEntry114,stateEntry115,stateEntry116,stateEntry117,stateEntry118,stateEntry119,stateEntry120,stateEntry121,stateEntry122,stateEntry123,stateEntry124,stateEntry125,stateEntry126,stateEntry127,stateEntry128,stateEntry129,stateEntry130,stateEntry131,stateEntry132,stateEntry133,stateEntry134,stateEntry135,stateEntry136,stateEntry137,stateEntry138,stateEntry139,stateEntry140,stateEntry141,stateEntry142,stateEntry143,stateEntry144,stateEntry145,stateEntry146,stateEntry147,stateEntry148,stateEntry149,stateEntry150,stateEntry151,stateEntry152,stateEntry153,stateEntry154,stateEntry155,stateEntry156,stateEntry157,stateEntry158,stateEntry159,stateEntry160,stateEntry161,stateEntry162,stateEntry163,stateEntry164,stateEntry165,stateEntry166,stateEntry167,stateEntry168,stateEntry169,stateEntry170,stateEntry171,stateEntry172,stateEntry173,stateEntry174,stateEntry175,stateEntry176,stateEntry177,stateEntry178,stateEntry179,stateEntry180,stateEntry181,stateEntry182,stateEntry183,stateEntry184]
def states (i : Nat) := ds[i]?.getD default
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def ms : Array (List (Fin 4)) := #[[2],[],[0],[2,0]]
def perm (i : Nat) := permitted (ms[i]?.getD [])
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def specTab : Array Spec := #[(4,[]),(5,[]),(4,[(0,0,1)]),(7,[]),(6,[]),(9,[(0,0,1),(1,2,4)]),(9,[]),(5,[(3,2,3)]),(1,[(1,0,1)]),(3,[(1,0,1)]),(1,[]),(1,[(3,0,1)]),(0,[]),(1,[(2,0,1)]),(6,[(0,0,1),(1,2,4)]),(8,[]),(0,[(0,0,3)]),(4,[(0,0,1),(1,0,1)]),(6,[(0,0,1),(1,0,1)]),(6,[(0,0,1)]),(1,[(1,0,1),(1,0,2)]),(1,[(0,1,2),(1,0,4)]),(1,[(1,0,1),(1,2,4)]),(1,[(3,0,1),(3,2,4)]),(1,[(1,0,1),(2,2,4)]),(1,[(1,0,2),(1,1,2)]),(4,[(0,0,1),(1,2,4)]),(1,[(3,0,2),(1,1,2)]),(2,[]),(1,[(0,0,1),(1,2,4)]),(8,[(0,0,1)]),(1,[(1,1,2),(3,0,4)]),(3,[]),(9,[(0,0,1)]),(1,[(2,0,2)]),(1,[(2,1,2),(1,0,4)]),(1,[(0,0,2)]),(1,[(1,0,1),(3,2,4)]),(1,[(3,0,1),(0,3,4)]),(1,[(1,0,1),(1,3,4)]),(1,[(1,0,1),(2,3,4)]),(1,[(2,1,3),(1,0,4)]),(1,[(1,0,1),(0,3,4)]),(1,[(0,0,3)]),(1,[(0,1,3),(1,0,4)]),(1,[(2,0,3)]),(1,[(0,0,3),(1,1,4)]),(1,[(3,2,3),(1,0,4)]),(1,[(1,0,2),(2,3,4)]),(3,[(2,0,2)]),(4,[(0,0,1),(3,2,4)]),(1,[(1,0,2)]),(9,[(0,0,1),(3,3,4)]),(1,[(3,0,1),(1,1,2)]),(4,[(0,0,1),(0,2,4)]),(9,[(1,2,3)]),(1,[(3,0,2),(1,1,4)]),(1,[(0,0,1)]),(1,[(3,0,2)]),(1,[(3,0,1),(1,2,4)]),(3,[(1,1,2),(3,0,4)]),(4,[(0,0,1),(2,2,4)]),(1,[(1,1,2),(0,0,4)]),(3,[(0,1,2),(1,1,2)]),(1,[(0,1,2),(1,1,2)]),(3,[(1,1,2)]),(1,[(1,1,2)]),(4,[(0,0,1),(0,0,2)]),(3,[(1,1,2),(0,0,4)]),(1,[(0,0,3),(2,1,4)]),(1,[(0,0,3),(2,2,4)]),(4,[(0,0,1),(0,3,4)]),(3,[(0,0,3)]),(4,[(0,0,1),(2,3,4)]),(1,[(3,0,3)]),(3,[(3,0,3)]),(2,[(0,0,3)]),(4,[(0,0,1),(0,0,3)]),(1,[(1,1,2),(0,3,4)]),(1,[(1,1,2),(2,3,4)]),(1,[(3,1,2)]),(1,[(2,1,2)]),(1,[(0,0,3),(1,2,4)]),(3,[(0,0,3),(1,2,4)]),(9,[(0,0,1),(1,3,4)]),(6,[(0,0,1),(0,3,4)]),(1,[(1,0,3)]),(6,[(0,0,1),(2,3,4)]),(1,[(3,0,3),(1,1,4)]),(1,[(1,1,3),(3,0,4)]),(3,[(0,0,1)]),(1,[(0,0,2),(2,3,4)]),(1,[(1,0,3),(3,2,3)]),(1,[(3,0,3),(3,2,3)]),(3,[(0,1,2),(1,0,4)]),(3,[(0,1,2),(1,3,4)]),(1,[(0,1,2),(1,3,4)]),(3,[(0,1,2)]),(1,[(0,1,2)]),(3,[(2,1,2)]),(6,[(0,0,1),(0,0,3)]),(1,[(1,0,2),(1,3,4)]),(1,[(1,0,3),(3,2,4)]),(1,[(3,0,2),(2,3,4)]),(1,[(3,0,2),(0,3,4)]),(9,[(0,0,1),(2,3,4)]),(3,[(3,2,3),(1,0,4)]),(6,[(0,0,1),(1,3,4)]),(1,[(3,2,3),(2,0,4)]),(1,[(3,2,3),(1,1,4)]),(4,[(3,2,3)]),(9,[(3,2,3)]),(1,[(0,1,2),(2,3,4)]),(7,[(3,2,3)]),(1,[(3,1,3),(3,2,3)]),(1,[(3,2,3)]),(3,[(3,2,3)]),(1,[(1,2,3)]),(1,[(0,2,3)]),(4,[(2,0,1)]),(6,[(2,1,2),(2,0,4)]),(9,[(2,1,2),(2,0,4)]),(6,[(2,1,2)]),(1,[(2,0,1),(2,2,4)]),(1,[(2,0,1),(1,2,4)]),(4,[(2,0,2),(2,1,4)]),(1,[(0,0,2),(1,1,4)]),(1,[(1,0,1),(0,2,4)]),(1,[(2,0,1),(2,3,4)]),(1,[(2,0,1),(1,3,4)]),(9,[(2,1,2)]),(1,[(3,0,3),(2,2,4)]),(9,[(2,0,3),(2,1,4)]),(6,[(3,0,1)]),(4,[(2,0,2)]),(9,[(2,0,3)]),(3,[(3,1,2)]),(4,[(2,1,2)]),(1,[(2,0,2),(1,1,4)]),(3,[(2,0,2),(1,1,4)]),(6,[(1,0,2)]),(9,[(2,0,3),(1,2,4)]),(1,[(0,0,1),(2,2,4)]),(1,[(0,0,1),(0,2,4)]),(6,[(2,0,1)]),(1,[(0,1,2),(0,3,4)]),(1,[(3,1,2),(3,3,4)]),(1,[(2,1,3),(2,2,4)]),(1,[(3,1,2),(0,3,4)]),(1,[(0,1,3),(2,2,4)]),(6,[(2,0,3)]),(1,[(3,1,3),(2,2,4)]),(3,[(2,0,1),(3,2,4)]),(6,[(2,0,2)]),(9,[(2,0,2),(3,3,4)]),(3,[(0,1,2),(2,0,4)]),(3,[(2,0,1),(2,0,2)]),(9,[(2,0,2),(2,0,3)]),(1,[(2,0,2),(2,1,4)]),(1,[(0,1,2),(2,0,4)]),(1,[(0,0,1),(3,2,4)]),(3,[(2,0,1),(2,2,4)]),(4,[(2,1,2),(1,0,4)]),(6,[(2,0,2),(1,1,4)]),(1,[(2,0,1),(0,2,4)]),(3,[(2,0,2),(0,3,4)]),(4,[(2,0,2),(0,3,4)]),(6,[(0,0,3)]),(3,[(0,1,3)]),(4,[(3,1,3)]),(1,[(0,1,3)]),(1,[(2,1,3)]),(6,[(2,1,2),(2,3,4)]),(3,[(3,1,3)]),(1,[(2,0,2),(2,3,4)]),(1,[(2,0,2),(1,3,4)]),(4,[(2,0,2),(2,3,4)]),(1,[(0,2,3),(1,1,4)]),(1,[(1,1,3),(0,2,4)]),(6,[(3,0,3)]),(3,[(2,0,2),(2,3,4)]),(1,[(2,2,3)]),(3,[(0,0,3),(2,2,4)]),(1,[(2,2,3),(2,0,4)]),(1,[(0,0,2),(3,3,4)]),(1,[(2,0,2),(3,3,4)]),(1,[(0,0,2),(0,3,4)]),(3,[(2,0,2),(3,3,4)]),(3,[(0,2,3),(2,0,4)]),(3,[(2,0,2),(2,0,3)]),(4,[(0,1,3)]),(6,[(0,1,3)]),(1,[(3,2,3),(2,1,4)]),(1,[(2,1,2),(0,3,4)]),(1,[(2,1,2),(3,3,4)]),(1,[(2,1,3),(1,2,4)]),(6,[(2,0,2),(1,3,4)]),(1,[(1,1,3)]),(4,[(3,2,3),(1,0,4)]),(1,[(3,1,3)]),(6,[(3,2,3)]),(4,[(0,0,2)]),(6,[(0,0,2)]),(9,[(1,2,3),(0,0,4)]),(4,[(0,1,2),(2,0,4)]),(4,[(0,0,2),(0,1,2)]),(1,[(1,1,2),(2,1,3)]),(1,[(1,1,2),(2,2,3)]),(4,[(0,0,2),(0,3,4)]),(1,[(1,1,2),(3,3,4)]),(4,[(0,1,2),(2,3,4)]),(1,[(1,1,2),(1,3,4)]),(9,[(1,2,3),(0,1,4)]),(9,[(0,2,3),(1,2,3)]),(4,[(1,2,3),(0,0,4)]),(4,[(0,0,2),(0,0,3)]),(4,[(0,0,2),(0,2,3)]),(4,[(0,1,3),(2,0,4)]),(3,[(2,0,3)]),(9,[(2,0,1)]),(4,[(0,1,3),(1,1,3)]),(6,[(0,1,3),(1,1,3)]),(4,[(0,0,3)]),(4,[(0,0,3),(1,2,4)]),(1,[(0,1,3),(1,2,4)]),(1,[(1,1,2),(1,2,3)]),(3,[(1,1,2),(3,3,4)]),(3,[(2,2,3),(1,1,4)]),(3,[(3,1,2),(3,3,4)]),(1,[(0,0,1),(0,3,4)]),(3,[(2,1,3),(1,2,4)]),(3,[(2,1,2),(3,3,4)]),(9,[(1,2,3),(3,1,4)]),(3,[(1,1,2),(2,1,3)]),(3,[(1,1,2),(2,2,3)]),(4,[(0,1,3),(2,2,4)]),(3,[(1,1,2),(0,3,4)]),(3,[(1,1,2),(1,3,4)]),(4,[(0,0,3),(0,1,3)]),(4,[(0,0,3),(0,2,3)]),(4,[(0,2,3)]),(6,[(0,2,3)]),(4,[(0,2,3),(2,0,4)]),(4,[(2,2,3)]),(3,[(1,1,2),(2,3,4)]),(4,[(1,2,3)]),(6,[(0,1,3),(2,0,4)]),(4,[(0,0,3),(2,1,4)]),(1,[(1,0,1),(3,3,4)]),(9,[(0,0,2)]),(1,[(2,0,3),(1,1,4)]),(3,[(0,0,3),(1,1,4)]),(6,[(0,0,3),(1,2,4)]),(9,[(1,0,2)]),(3,[(1,1,3),(0,0,4)]),(1,[(1,1,3),(1,2,3)]),(1,[(2,1,2),(1,3,4)]),(1,[(1,1,3),(3,2,4)]),(6,[(0,0,3),(0,1,3)]),(3,[(3,1,3),(2,0,4)]),(4,[(2,0,3)]),(6,[(3,2,3),(2,0,4)]),(1,[(3,1,3),(2,0,4)]),(1,[(3,1,3),(1,0,4)]),(1,[(3,1,3),(1,2,4)]),(4,[(3,2,3),(2,0,4)]),(9,[(2,2,3)]),(9,[(0,0,3),(1,2,4)]),(3,[(3,2,3),(2,0,4)]),(9,[(0,0,3)]),(3,[(3,2,3),(1,1,4)]),(6,[(1,2,3)]),(1,[(1,1,3),(3,2,3)]),(3,[(3,1,3),(3,2,3)])]
def spec (i : Nat) := specTab[i]?.getD (0,[])
def checked (i : Nat) := nodeOK target root mins spec states perm i
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block0 : Good checked 0 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block1 : Good checked 4 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block2 : Good checked 8 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block3 : Good checked 12 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block4 : Good checked 16 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block5 : Good checked 20 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block6 : Good checked 24 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block7 : Good checked 28 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block8 : Good checked 32 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block9 : Good checked 36 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block10 : Good checked 40 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block11 : Good checked 44 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block12 : Good checked 48 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block13 : Good checked 52 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block14 : Good checked 56 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block15 : Good checked 60 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block16 : Good checked 64 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block17 : Good checked 68 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block18 : Good checked 72 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block19 : Good checked 76 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block20 : Good checked 80 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block21 : Good checked 84 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block22 : Good checked 88 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block23 : Good checked 92 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block24 : Good checked 96 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block25 : Good checked 100 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block26 : Good checked 104 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block27 : Good checked 108 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block28 : Good checked 112 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block29 : Good checked 116 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block30 : Good checked 120 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block31 : Good checked 124 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block32 : Good checked 128 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block33 : Good checked 132 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block34 : Good checked 136 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block35 : Good checked 140 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block36 : Good checked 144 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block37 : Good checked 148 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block38 : Good checked 152 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block39 : Good checked 156 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block40 : Good checked 160 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block41 : Good checked 164 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block42 : Good checked 168 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block43 : Good checked 172 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block44 : Good checked 176 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block45 : Good checked 180 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block46 : Good checked 184 1 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem total : Good checked 0 185 := (concatGood (concatGood (concatGood (concatGood (concatGood block0 block1) (concatGood block2 (concatGood block3 block4))) (concatGood (concatGood block5 (concatGood block6 block7)) (concatGood block8 (concatGood block9 block10)))) (concatGood (concatGood (concatGood block11 (concatGood block12 block13)) (concatGood block14 (concatGood block15 block16))) (concatGood (concatGood block17 (concatGood block18 block19)) (concatGood block20 (concatGood block21 block22))))) (concatGood (concatGood (concatGood (concatGood block23 (concatGood block24 block25)) (concatGood block26 (concatGood block27 block28))) (concatGood (concatGood block29 (concatGood block30 block31)) (concatGood block32 (concatGood block33 block34)))) (concatGood (concatGood (concatGood block35 (concatGood block36 block37)) (concatGood block38 (concatGood block39 block40))) (concatGood (concatGood block41 (concatGood block42 block43)) (concatGood block44 (concatGood block45 block46))))))
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem impossible : Impossible true target 9 root.toFinset := by
  have h := certified (states:=states) (perm:=perm) (specs:=spec) (N:=185) (fun j => perm_onto _) pri (fun i hi => total i (by omega) hi) 184 (by decide)
  exact h
def essentials : List (Sig × Row × Row) := [(root.getD 0 zero,6,7),(root.getD 1 zero,5,7),(root.getD 2 zero,3,7),(root.getD 3 zero,3,11),(root.getD 4 zero,3,19)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lower : Lower true root target 10 := by
  apply lower_impossible (L:=9) (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro a ha
    apply essential_ok (xs:=essentials) (by decide +kernel) a
    exact (show (essentials.map Prod.fst).toFinset = root.toFinset by decide +kernel).symm ▸ List.mem_toFinset.mpr ha
  · exact impossible
end Tab0

namespace Tab1
open PEqualNP.Outside.L_meta_12126.Core GateForest12127 CertBlocks12127 Bound12127
def root := inputs.take 5
def target := stamp 5 0xe8808000
def sd0 : Sig := ~~~raw 0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sl0 : Slice true root target sd0 3 :=
  slice_correct (ms:=[forceLow 4,swapNext 3,swapNext 2,swapNext 1,swapNext 0]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) Tab8000.lower
def sd1 : Sig := raw 0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sl1 : Slice true root target sd1 7 :=
  slice_correct (ms:=[forceHigh 4,swapNext 3,swapNext 2,swapNext 1,swapNext 0]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) Tabe880.lower
def sd2 : Sig := ~~~raw 1
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sl2 : Slice true root target sd2 3 :=
  slice_correct (ms:=[forceLow 4,swapNext 3,swapNext 2,swapNext 1]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) Tab8000.lower
def sd3 : Sig := raw 1
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sl3 : Slice true root target sd3 7 :=
  slice_correct (ms:=[forceHigh 4,swapNext 3,swapNext 2,swapNext 1]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) Tabe880.lower
def sd4 : Sig := ~~~raw 2
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sl4 : Slice true root target sd4 3 :=
  slice_correct (ms:=[forceLow 4,swapNext 3,swapNext 2]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) Tab8000.lower
def sd5 : Sig := raw 2
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sl5 : Slice true root target sd5 7 :=
  slice_correct (ms:=[forceHigh 4,swapNext 3,swapNext 2]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) Tabe880.lower
def sd6 : Sig := ~~~raw 3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sl6 : Slice true root target sd6 3 :=
  slice_correct (ms:=[forceLow 4,swapNext 3]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) Tab8000.lower
def sd7 : Sig := raw 3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sl7 : Slice true root target sd7 7 :=
  slice_correct (ms:=[forceHigh 4,swapNext 3]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) Tabe880.lower
def sd8 : Sig := ~~~raw 4
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sl8 : Slice true root target sd8 3 :=
  slice_correct (ms:=[forceLow 4]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) Tab8000.lower
def sd9 : Sig := raw 4
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sl9 : Slice true root target sd9 7 :=
  slice_correct (ms:=[forceHigh 4]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) Tabe880.lower
def mins : List (Sig × Nat) := [(sd0,3),(sd1,7),(sd2,3),(sd3,7),(sd4,3),(sd5,7),(sd6,3),(sd7,7),(sd8,3),(sd9,7)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pri : ∀ m ∈ mins, Slice true root target m.1 m.2 := by
  intro m hm
  simp only [mins,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact sl0
  · exact sl1
  · exact sl2
  · exact sl3
  · exact sl4
  · exact sl5
  · exact sl6
  · exact sl7
  · exact sl8
  · exact sl9
def stateEntry0 : Entry := row 5 [0x888888,0xaa000000,0xcc00cc00,0xf0f0f0f0,0xffff0000] 4 (packWords [0x1eb2e32e,0x71eb1e72e73791,0xe736a000000000,0x1ee2e42e71ee1e,0x31e31e72f337a1,0xeb3b41eb1ea1ea,0x1eb3b93701e737,0x91e71e41e41e72,0xf4000000400000]) []
def stateEntry1 : Entry := row 5 [0x888888,0xaa000000,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (packWords [0x1e72e73ce1e7,0x1eb2e32e71eb2e,0x73792e780136a0,0x1ee2e6,0x2e71ee1e31e31e,0x72f31e73791e78,0x372000000000,0x1e61e61e72f61e,0xb3b91eb37937a1,0xeb3b91eb1ea1ea,0x1eb3b937837837,0x93bc1ec0000000,0x401000]) [(0,0),(0,1)]
def stateEntry2 : Entry := row 5 [0x80808080,0x8f008f00,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000] 5 (packWords [0x36b2e736b2e7,0x2e73692e73ad2e,0x736a2e73ce36b2,0xe736b2e71eb2e3,0x2e71eb3d037937,0x93b13b037a37a3,0xd21e7000000000,0x2f31eb1eb2f337,0x83783793bc3793,0xda3793b91e9000,0x37a3b937,0xa3b81ea0000000,0x2f31eb1eb2f3]) []
def stateEntry3 : Entry := row 5 [0xaaaaaa,0x5500ff00,0xaa000000,0xcccccccc,0xf0f0f0f0,0xffff0000] 5 (packWords [0x1eb2e32e71eb,0x1ed2e52e71ed36,0x20000000001e72,0xe73ce1e71ee2e6,0x2e71ee1e91e91e,0xb3793721eb3761,0xeb1e31e31e72f3,0x1ea1ea1eb3b937,0x1ed3721ed1e51,0xe51e72f51ec1ec,0x1ed37900000037,0xa0000000003730,0x1e61e61e72f6]) []
def stateEntry4 : Entry := row 5 [0xaaaaaa,0xaa000000,0xcc00cc00,0xcccc0000,0xf0f0f0f0] 4 (packWords [0x2e11eb2e,0x51eb1e11e11e52,0xf337a1eb3a41eb,0x1ea1ea1eb3b91e,0x52e53ce1e536a2,0xe537a2e51ee2e4,0x2e51ee3721e537,0xa1e51e41e41e52,0xf60000003a5000]) []
def stateEntry5 : Entry := row 5 [0xaaaaaa,0xaa000000,0xcc00cc00,0xcccccccc,0xf0f0f0f0,0xffff0000] 5 (packWords [0x1eb2e32e71eb,0x2e52e52e78011e,0x72e73ce1e736a0,0x1ee2e6,0x2e71ee1eb2f11e,0xb3b91e31e31e72,0xf337a1eb3b41eb,0x1ea1ea1eb3b91e,0x50000000003b42,0xf537a2f52f41ee,0x1ee8003721e737,0xa1e71e61e61e72,0xf60000003b5000]) [(0,0),(4,0)]
def stateEntry6 : Entry := row 5 [0xaaaaaa,0xaa000000,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x3ce1e71e,0x72e73d62e73ce3,0xd63ce2e71e71e7,0x2e71eb1eb4062f,0x32e32e72f32e78,0x91eb1eb2e71ed,0x1ed4062f52e52e,0x72f52e78081ed1,0xed80740536a000,0x0,0x2e71,0xee1ee3ce2f62e6,0x2e72f62e73ce1e,0xe1ee1e72f31e34,0x41eb1e31e71eb,0x1e78062f32f31e,0x72f51e54041ed1,0xe51e71ed1e7805,0x2f52f580440437,0x20000000000000,0x0,0x1e72f61e63d61e,0xe1e61e71ee1e73,0xd62f62f61eb379,0x1e93b91ed1e91e,0xb1ed1eb3b93793,0x793b937a37a1eb,0x3bc1eb3b93bc3b,0x91eb37a1eb1eb8,0x31ea3b91ee1ea,0x1eb1ee1eb3b980,0x23b93793bc3781,0xed37a1ed37937a,0x3791ed3bc1ed1e,0xd8011ec3791ee1,0xec1ed1ee1ed379,0x80037900000000,0x4034,0x3402000000000]) [(1,0),(2,2),(1,3),(2,4),(3,0),(5,0),(5,3),(3,5),(5,1),(5,6)]
def stateEntry7 : Entry := row 5 [0xaaaaaaa,0xeccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 4 (packWords [0x1e72e736,0xb1e71eb2e32e71,0xeb1ed2e52e71ed,0x1ee2e62e71ee1e,0x31e31e72f31e51,0xe51e72f51e61e6,0x1e72f61e91e91e,0xb3791ea1ea1eb3,0x7a1ec1ec1ed3bc]) []
def stateEntry8 : Entry := row 5 [0xaaaaaaa,0xa0000000,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (packWords [0x1e72e736b1e7,0x1eb2e32e71eb1e,0xd2e52e71ed3ac0,0x1ee2e6,0x2e71ee1e31e31e,0x72f31e51e51e72,0xf53b4000000000,0x1e61e61e72f61e,0x91e91eb3793b80,0x1ea1ea,0x1eb37a3bc1ed80,0x1ed1ec1ec1ed3,0xdc000000402000]) [(7,0)]
def stateEntry9 : Entry := row 5 [0x2aaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 4 (packWords [0x1e72e736,0xb1e71eb2e32e71,0xeb1ed2e52e71ed,0x1ee2e62e71ee1e,0x31e31e72f31e51,0xe51e72f51e61e6,0x1e72f61e91e91e,0xb3791ea1ea1eb3,0x7a1ec1ec1ed3bc]) []
def stateEntry10 : Entry := row 5 [0x80000000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (packWords [0x1e72e736b1e7,0x1eb2e32e71eb1e,0xd2e52e71ed1ee2,0xe62e71ee804000,0x1e31e31e,0x72f31e51e51e72,0xf51e61e61e72f6,0x8030000000001e,0x91e91eb3791ea1,0xea1eb37a802000,0x1ec1ec1e,0xd3bc8010000000,0x800000000000]) [(9,0),(9,7),(9,8),(9,9),(9,10)]
def stateEntry11 : Entry := row 5 [0x80008000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff8000] 5 (packWords [0x3632e736b2e7,0x2e32e32e736b2e,0x52e52e73ad2e62,0xe62e73ce804000,0x2f33733b,0x52f32f53713732,0xf52f63723732f6,0x8030000000002f,0x12f12f33792f22,0xf22f337a802000,0x2f42f42f,0x53bc8010000000,0x800000000000]) [(7,11),(7,12),(7,13),(7,14),(9,10)]
def stateEntry12 : Entry := row 5 [0x2aaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (packWords [0x36b1e71e72,0xe73732e736b373,0x36b2e71e71e72e,0x71eb1eb36b2f32,0xe32e72f32e736b,0x1eb1eb2e71ed1e,0xd3ad2f52e52e72,0xf52e73ad1ed1ed,0x2e71ee1ee3ce2f,0x62e62e72f62e73,0xce1ee1ee1e72f3,0x1e33731eb1e31e,0x71eb1e73732f32,0xf31e72f51e53b5,0x1ed1e51e71ed1e,0x73b52f52f51e72,0xf61e63d61ee1e6,0x1e71ee1e73d62f,0x62f61eb3791e93,0xb91ed1e91eb1ed,0x1eb3b93793791e,0xb37a1ea3da1ee1,0xea1eb1ee1eb3da,0x37a37a1ed3bc1e,0xc3dc1ee1ec1ed1,0xee1ed3dc3bc3bc]) []
def stateEntry13 : Entry := row 5 [0x2aaaaaaa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (packWords [0x1e72e736b1e7,0x1eb2e32e71eb1e,0xd2e52e71ed2e73,0xce2e73ce2e73ce,0x2e73ce1e31e31e,0x72f31e51e51e72,0xf51e73d61e73d6,0x1e73d61e73d61e,0x91e91eb3791eb3,0xda1eb3da1eb3da,0x1eb3da1ed3dc1e,0xd3dc1ed3dc1ed3,0xdc1ee000000000]) []
def stateEntry14 : Entry := row 5 [0x2aaaaaaa,0xc0000000,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (packWords [0x1e72e736b1e7,0x1eb2e32e71eb1e,0xd2e52e71ed3ce0,0x1ee2e6,0x2e71ee1e31e31e,0x72f31e51e51e72,0xf53d6000000000,0x1e61e61e72f61e,0x91e91eb3793da0,0x1ea1ea,0x1eb37a3dc00000,0x1ec1ec1ed3,0xbc000000402000]) []
def stateEntry15 : Entry := row 5 [0x80008000,0xaaaa0000,0xcccc0000,0xf0f0f0f0,0xff00ff00] 4 (packWords [0x2f33733b,0x52f32f53713732,0xf52f63723732f6,0x1e40000000002f,0x12f12f33792f22,0xf22f337a1e8000,0x2e42e42f,0x53ac1ec2f54071,0xec1ec2f64071ec]) []
def stateEntry16 : Entry := row 5 [0x80008000,0xaaaa0000,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (packWords [0x3c6373373802,0x3ca2f32f38013c,0xc2f52f58002e60,0x1ee3ce,0x4071ee2f33733b,0x52f32f53713732,0xf52f63723732f6,0x1e60000000002f,0x12f12f33792f22,0xf22f337a1ea000,0x2f42f42f,0x53bc1ec0000000,0x1ee2f64071ee]) [(15,0),(15,8),(15,9)]
def stateEntry17 : Entry := row 5 [0x80008000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x36b40e36,0x32e73732e736b3,0x7336b2e780c2e7,0x2e740d2e336b2f,0x32e32e72f32e73,0x6b80b36b2e740c,0x2e53ad2f52e52e,0x72f52e73ad80a3,0xad2e74082e63ce,0x2f62e62e72f62e,0x73ce8093ce8088,0x78062e74072e7,0x8054074072e780,0x42e73b52f32f33,0x733b93733b53b9,0x3b53732f32f337,0x32f52f53b53793,0x713733793733b5,0x2f52f53732f62f,0x63d637a3723733,0x7a3733d62f62f6,0x80340b1e700000,0x0,0x2f3379,0x2f13b92f52f12f,0x32f52f33b93793,0x792f337a2f23da,0x2f62f22f32f62f,0x33da37a37a8024,0xa1eb000000000,0x0,0x2f53bc2f43,0xdc2f62f42f52f6,0x2f53dc3bc3bc80,0x14091ed0000000,0x0,0x8004081e,0xe0000000000000,0x0]) [(8,11),(8,12),(8,13),(8,14),(10,0),(11,0),(12,10),(13,10),(14,10),(16,0),(16,7),(16,8),(16,9)]
def stateEntry18 : Entry := row 5 [0xaaaaaaa,0xa000a000,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (packWords [0x3632e736b2e7,0x2e32e32e736b1e,0xd2e52e71ed3ac2,0xe73bc2e72e62e6,0x2e73ad2f33733d,0x62f32f51ed1ed2,0xf51e7000000000,0x2f63723732f62f,0x11ed1ed3791eb0,0x2f22f2,0x2f337a1ed2f51e,0xd2f51ed2f41ed3,0xdc1ee1ee4022f6]) []
def stateEntry19 : Entry := row 5 [0x2aaaaaaa,0xc000c000,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (packWords [0x3632e736b2e7,0x2e32e32e736b2e,0x52e52e73ad3ce2,0xe73ce2e71ee2e6,0x2e71ee2f33733b,0x52f32f53713732,0xf51e7000000000,0x2f61ee1ee2f62f,0x12f12f33791eb0,0x2f21ee,0x1ee37a1ed00000,0x2f41ee1ee3,0xbc2f61ee1ee2f6]) []
def stateEntry20 : Entry := row 5 [0x80008000,0x80808080,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x3632e736b2e72e,0x736b2e736b2e73,0x692e73ad2e736a,0x2e73ce2e736b2e,0x736b8042e74102,0xe73b13733b5373,0x3713713733b537,0x23723733d68033,0x7340e0001e7000,0x3793b93d,0xa37937a3b83b93,0x7a2f3000000000,0x80200000000037,0x83783793bc2f50,0x801000,0x2f600000,0x8000000000,0x40f000000000]) [(18,11),(18,12),(18,13),(8,14),(19,10)]
def stateEntry21 : Entry := row 5 [0x8888888,0xe0e0e0e0,0xff00ff00,0xffff0000] 3 (packWords [0x1e,0x72e736b1e71eb2,0xe32e71eb1ed2e5,0x2e71ed1e31e31e,0x72f31e51e51e72,0xf51e81e81eb378]) []
def stateEntry22 : Entry := row 5 [0x8888888,0xeeeeeeee,0xf0f0f0f0,0xff00ff00,0xffff0000] 4 (packWords [0x1e72e736,0xb1e71eb2e32e71,0xeb2e73ac2e7802,0x1ed2e52e71ed1e,0x31e31e72f31e73,0xb41e78011e51e5,0x1e72f51eb3b81e,0xb8001e91e91eb3,0x791ec000000000]) [(21,0),(21,15),(21,16)]
def stateEntry23 : Entry := row 5 [0x8888888,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (packWords [0x1e72e736b1e7,0x1eb2e32e71eb2e,0x73ad2e73ad2e73,0xac2e73ce2e73ad,0x2e73ad1e31e31e,0x72f31e73b51e73,0xb51e73b41e73d6,0x1e73b51e73b51e,0xb3b91eb3b91eb3,0xb81eb3da1eb3b9,0x1eb3b93bc3dc80,0x3bc1ed0000000,0x1ee000000000]) [(22,0)]
def stateEntry24 : Entry := row 5 [0x8000aaaa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (packWords [0x1e73733731e7,0x1eb2f32f31eb1e,0xd2f52f51ed2e62,0xe62f63ce8003ce,0x2e72e71e31e31e,0x72f31e51e51e72,0xf51e73721e72f6,0x1e73731e73731e,0x91e91eb3791eb2,0xf21eb37a1eb2f3,0x1eb2f31ed2f41e,0xd3bc1ed2f51ed2,0xf51ee000000000]) [(9,10)]
def stateEntry25 : Entry := row 5 [0xaaaa,0x2aaa2aaa,0xcccc0000,0xf0f0f0f0,0xff00ff00] 4 (packWords [0x2f33733b,0x52f32f53713732,0xf52f61ed1e51e5,0x1e41e41ec3732f,0x12f12f33792f21,0xed1e91e91e81e8,0x1ec2f31ed2e42f,0x51ed0000002e50,0x1ec2f61ed1ec]) []
def stateEntry26 : Entry := row 5 [0xaaaa,0x2aaa2aaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (packWords [0x3c6373373803,0x3ca2f32f38023c,0xc2f52f58012e62,0xe62f63ce000000,0x2e70002f33733b,0x52f32f53713732,0xf52f63721e71e7,0x1e61e61ee3732f,0x12f12f33792f22,0xf21eb1eb1ea1ea,0x1ee2f32f42f41e,0xd1ed1ec1ec1ee2,0xf51ee2f68001ee]) [(9,0),(25,0),(25,3),(25,17)]
def stateEntry27 : Entry := row 5 [0xaaaaaaa,0xaaaaaaaa,0xc0c0c0c0,0xcc00cc00,0xffff0000] 4 (packWords [0x1e72e736,0xb1e71eb2e12e71,0xeb2e73a02e73ce,0x2e73b12e73a11e,0x11e11e72f11e73,0xd61e73b01e73d6,0x1e73b11eb3da1e,0xb3b01eb3da1eb3,0xb11ee000000000]) []
def stateEntry28 : Entry := row 5 [0xaaaaaaa,0xaaaaaaaa,0xc0c0c0c0,0xcccccccc,0xff00ff00,0xffff0000] 5 (packWords [0x1e72e736b1e7,0x2e73692e78021e,0xb2e32e71eb2e73,0xa82e73ce2e73b9,0x2e73a91e73711e,0x78011e31e31e72,0xf31e73b01e73d6,0x1e73b91e73b11e,0x90000000003798,0x3793b8379400,0x3793b91eb3da1e,0xb3b81eb3da1eb3,0xb91ee000000000]) [(25,18),(27,0),(27,16)]
def stateEntry29 : Entry := row 5 [0xaaaaaaa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x36b1e71e,0x72e73732e736b3,0x7336b2e71e71e7,0x2e71eb1eb36b2f,0x32e32e72f32e73,0x6b1eb1eb2e71ed,0x1ed4172f52e52e,0x72f52e78061ed1,0xed2e74112e73ce,0x3bc3ac2e73bc2e,0x73ce4173ce2e74,0x112e73ce4023ce,0x2e74022e73ce41,0x63ad1e72f31e33,0x731eb1e31e71eb,0x1e73732f32f31e,0x72f51e54151ed1,0xe51e71ed1e7805,0x2f52f51e74111e,0x73d63bc3b41e73,0xbc1e73d64153d6,0x1e74111e73d640,0x23d61e74021e73,0xd64143b51eb379,0x1e94131ed1e91e,0xb1ed1eb8043793,0x791eb4111eb3da,0x3bc3b81eb3bc1e,0xb3da4133da1eb4,0x111eb3da4023da,0x1eb4021eb3da41,0x23b91ed3bc1ed3,0xdc8033dc1ed411,0x1ed3dc3bc3bc1e,0xd8021ed3dc4003,0xdc1ed4001ed3dc,0x8013dc8004111e,0xe0000000000000,0x0]) [(8,0),(23,0),(24,19),(26,20),(28,0),(28,15),(28,16)]
def stateEntry30 : Entry := row 5 [0xaaaaaaa,0xa0a0a0a0,0xcccccccc,0xf0000000,0xff00ff00,0xffff0000] 5 (packWords [0x1e72e736b1e7,0x3ca0000000001e,0xd2e52e71ed1eb2,0xe32e71eb2e736a,0x2e78013d200000,0x1e51e51e72,0xf51e31e31e72f3,0x1e73721e78001e,0xd3d83da1ed1eb3,0xb83bc1eb000000,0x4020001e91e91e,0xb3791ed3781ed3,0xdc1ea1ea1eb37a]) [(0,9),(0,10)]
def stateEntry31 : Entry := row 5 [0xaaaaaaa,0xaaaaaaaa,0xcccccccc,0xf0000000,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x1e72e736b1e71e,0xb2e32e71eb3ce0,0x1ed2e5,0x2e71ed2e73bc2e,0x78062e74112e78,0x51e31e31e72f3,0x3d60000000001e,0x51e51e72f51e73,0xbc1e78041e7411,0x1e78033da00000,0x1e91e91eb3,0x791eb3bc1eb802,0x1eb4111eb8011e,0xd3dc3dc1ed4110,0x3bc800000000,0x4020001ed3dc1e,0xd3bc1ed3dc1ed3,0xdc1ee000000000]) [(8,0),(1,8),(30,0),(1,9),(30,15),(1,10),(30,16)]
def stateEntry32 : Entry := row 5 [0x88888888,0xe0a0c000,0xff000000] 2 (packWords [0x1e33633a,0xe1e31ee3603631,0xee1e01e01e3378]) []
def stateEntry33 : Entry := row 5 [0x88888888,0xe0a0c000,0xff00ff00,0xffff0000] 3 (packWords [0x36,0x336336b8001eb2,0xe32f31eb1ee2f5,0x2f51ee1e31e31e,0xb2f32f51ee1ee2,0xf51e81e81eb378]) [(32,0)]
def stateEntry34 : Entry := row 5 [0x80808080,0xaa000000,0xcc00cc00,0xf0f00000] 3 (packWords [0x1e,0x72e73ca1e736a2,0xe73b42e71ea2e0,0x2e71ea3601e736,0xa1e71e01e01e72,0xf41ea36a8001ea]) [(32,21)]
def stateEntry35 : Entry := row 5 [0x80808080,0xaa000000,0xcc00cc00,0xf0f0f0f0,0xffff0000] 4 (packWords [0x2e73b92e,0x78011e72e73791,0xe736a000000000,0x1ee2e42e71ee37,0x91e71e737937a3,0xb03b437a1ea000,0x3701e737,0x91e71e41e41e72,0xf41ee37a8001ee]) [(33,21),(34,0)]
def stateEntry36 : Entry := row 5 [0xaaaaaa,0xaaaaaaaa,0xc000c000,0xcccc0000,0xf0f0f0f0] 4 (packWords [0x2e12e12e,0x53791e10000000,0x2f33a02f3372,0x2f33a52f33731e,0x52e53ce1e52e53,0x602e53a42e5373,0x2e53611e53d61e,0x53721e53d61e53,0x731ee000000000]) []
def stateEntry37 : Entry := row 5 [0x80808080,0xaa00aa00,0xcc00cc00,0xf0f00000,0xffff0000] 4 (packWords [0x2e700000,0x36936936b8,0x136a36a36b800,0x1eb2f42f41eb37,0x93b93d437937a3,0xb03b437a1eb2f0,0x2f41eb1e71e737,0x93b41e91e91eb2,0xf41ea1ea1eb2f4]) [(34,0),(34,7)]
def stateEntry38 : Entry := row 5 [0xaaaa,0xaaaaaaaa,0xc0c00000,0xcc00cc00,0xf000f000] 4 (packWords [0x1e11e11e,0xb3712f11eb3ce1,0xeb1eb3a01eb2f6,0x1eb3ad1eb36b2f,0x11ed3ce1ed1ed3,0x601ed2f61ed36b,0x1ed3612e02e02f,0x136a0000002e10,0x1ee000000000]) []
def stateEntry39 : Entry := row 5 [0x80808080,0xaa00aa00,0xcc00cc00,0xf0f0f0f0,0xffff0000] 5 (packWords [0x2e780a2e73,0x6b3b936b2e73b9,0x2e736b80936b36,0xb8083692e73792,0xe736b37936b2e7,0x8072e736b80636,0xa2e737a2e736b3,0x7a36b2e78052e7,0x2e78042e436b2f,0x42e42e72f42e73,0x6b80336b3da379,0x3793b93d43b93d,0xa3d43d43b93793,0x793b937a37a3da,0x3b43b03b93b43b,0x43da37a37a8024,0x1b1eb000000000,0x0,0x3793b41e73,0xd437a1e737937a,0x3793d43b43b480,0x12f41ed3794191,0xed40e41941a379,0x2f42f48002f41e,0xe37a4191ee40e4,0x1941837a2f42f4]) [(0,22),(0,23),(4,24),(15,16),(27,2),(35,0),(36,25),(35,7),(36,26),(37,0),(38,27)]
def stateEntry40 : Entry := row 5 [0xa888a000,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 4 (packWords [0x3ad37337,0x38033ad2f32f38,0x21ed3ad3ce1ed,0x1ee2e62f61ee2f,0x33733d62f33731,0xed1ed8011e61e6,0x1ee2f62f31ed1e,0xd8001ea1ea1ee3,0x7a1ec1ec1ed3bc]) [(33,28),(33,29),(33,30),(33,4)]
def stateEntry41 : Entry := row 5 [0x80808080,0xaa000000,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (packWords [0x1e72e73ce1e7,0x2e73b92e78042e,0x73792e780336a0,0x1ee2e6,0x2e71ee1e73b91e,0x78021e73791e78,0x1372000000000,0x1e61e61e72f637,0x93b93da37937a3,0xb83b937a1ea000,0x37837837,0x93bc1ec0000000,0x1ee37a8001ee]) [(40,17),(35,0),(35,3),(35,31),(35,20)]
def stateEntry42 : Entry := row 5 [0xaaaaaa,0xaaaaaaaa,0xc000c000,0xcccccccc,0xf0f0f0f0,0xffff0000] 5 (packWords [0x2e32e32e7801,0x2e52e52e78001e,0x72e73ce1e72e73,0x622e73ce2e7373,0x2e73632f12f12f,0x33791e30000000,0x2f33b02f3372,0x2f33b52f33731e,0x50000000002f53,0x702f53b42f5373,0x2f53711e73d61e,0x73721e73d61e73,0x731ee000000000]) [(36,0),(36,3)]
def stateEntry43 : Entry := row 5 [0x88888888,0xeaaac000,0xf0f00000,0xff00ff00] 3 (packWords [0x2f,0x31f33ae1f31e31,0xe31eb8001f11ee,0x1ee2f51eb2e32f,0x31eb1ee2f12f31,0xee1e81e81eb3bc]) [(32,32)]
def stateEntry44 : Entry := row 5 [0x80808080,0xaa00aa00,0xcccc0000,0xf0f0f0f0,0xff000000] 4 (packWords [0x3a93a93a,0xd8012e73693792,0xe71e737237a1e7,0x1ed3ad8001ed37,0x92e72e737937a1,0xe71e737a1e9000,0x1e72e737,0x91e71ed2e42e71,0xed1e41e41e72f6]) [(43,9),(34,8)]
def stateEntry45 : Entry := row 5 [0x80808080,0xaa00aa00,0xcccc0000,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (packWords [0x3ad3d63ad804,0x3a93a93ad8032e,0x70000000003ac3,0x7a37a8021ed2f6,0x2f61ed3d23b93b,0x98013d43793798,0x1e7000000000,0x2f61ed1ed2f637,0x93b93da37937a3,0xb83b937a1e9000,0x37837837,0x93bc1ed2f42f61,0xed1ec1ec1ed2f6]) [(35,7),(37,8),(35,31),(37,33),(44,0)]
def stateEntry46 : Entry := row 5 [0x88888888,0xeaaac000,0xf0f0f0f0,0xff00ff00,0xffff0000] 4 (packWords [0x3ae37337,0x38033ae2f32f38,0x22e72e73ae402,0x1ee2f52f51ee2f,0x33733b52f31e71,0xe73738012f51ee,0x1ee2f51eb1eb2f,0x38002f11ee1ee3,0x791ec1ec1ee3bc]) [(33,0),(33,15),(43,0),(43,34)]
def stateEntry47 : Entry := row 5 [0x80808080,0xaa00aa00,0xcccccccc,0xf0f0f0f0,0xff000000,0xffff0000] 5 (packWords [0x36b000000000,0x2e73b92e78052e,0x73792e78041e72,0xe737a1e72e62e6,0x2e78033d23b93b,0x98023d43793798,0x11e737237a1e7,0x2f63d68002f637,0x93b93da37937a1,0xe71e737a1eb000,0x3781e71e,0x73bc1ed0000000,0x1e61e61e72f6]) [(46,9),(35,7),(35,8),(15,10),(44,0),(44,3)]
def stateEntry48 : Entry := row 5 [0x80808080,0xaa00aa00,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x36b40e36,0xb2e73d62e736b3,0xd636b2e780c2e7,0x2e74202e736b3b,0x936b2e73b92e73,0x6b80b36b2e741f,0x2e73ad3793692e,0x73792e73ad80a3,0xad36b80936a2e7,0x37a2e736b37a36,0xb2e78082e72e78,0x72e636b2f62e6,0x2e72f62e736b80,0x636b3d64203d24,0x203b93b93d63b9,0x3b942040e8053d,0x641f3d441f3793,0x793d637937941f,0x40e80441e41e1e,0x70000000000000,0x0,0x8032f62f63d641,0x93d640e4194193,0xd62f62f63da379,0x3793b93dc3b93d,0xa3dc3da3b93793,0x793b937a37a3da,0x3bc3b83b93bc3b,0x93da37a37a8024,0x1d1eb000000000,0x0,0x3793bc3783,0xdc37a37837937a,0x3793dc3bc3bc80,0x141c1ed0000000,0x0,0x8002f61e,0xe37a4191ee40e4,0x1941837a2f62f6]) [(1,22),(5,23),(5,24),(30,14),(39,0),(39,8),(16,11),(28,2),(41,0),(42,5),(45,0),(45,3),(47,0)]
def stateEntry49 : Entry := row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff808000] 3 (packWords [0x1e,0x31e31e73631e51,0xe51e73a51e61e6,0x1e73c61f91f93d,0xa3791fa1fa3b93,0x7a1fc1fc3793bc]) []
def stateEntry50 : Entry := row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff808080,0xffffff00] 4 (packWords [0x1e73631e,0x78001e73b91e73,0x671e73791e73a7,0x1e737a1e73c71e,0xb1eb3ad36b1ed1,0xed36b3ad1ee1ee,0x36b3ce1f91f93d,0xa3791fa1fa3b93,0x7a1fc1fc3793bc]) [(49,0)]
def stateEntry51 : Entry := row 5 [0xaaaaaaaa,0xcccccccc,0xeaaac000,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (packWords [0x3ce373373809,0x3ce2f32f38082e,0x72e73ce4023ce2,0xf52f58071ee3ce,0x8061ee2f33733b,0x52f31e71e73738,0x52f53713732f5,0x3731ee1ee8041e,0xb1eb2f38032f12,0xf12f33792f31ee,0x1ee8021ed1ed2f,0x58012f61ee1ee4,0x72f51ee1ee800]) [(46,0),(40,7),(46,3),(40,8),(46,17),(40,9),(50,35),(46,36),(46,32),(46,37)]
def stateEntry52 : Entry := row 5 [0x808080,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (packWords [0x1e72e736b1e7,0x2e736b2e736b2e,0x73692e73ad2e73,0x6a2e73ce2e736b,0x2e736b1e73731e,0x73731e73711e73,0xb51e73721e73d6,0x1e73731e737337,0x93b93da37937a3,0xb83b937a1eb000,0x37837837,0x93bc1ed0000000,0x1ee000000000]) []
def stateEntry53 : Entry := row 5 [0x80808080,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff000000,0xff00ff00,0xffff0000] 6 (packWords [0x1e72e740e00036,0xb0000000002e73,0xb92e780e2e7379,0x2e780d2e737a2e,0x780c2e74072e78,0xb373000000000,0x1e73b91e780a1e,0x73791e78091e73,0x7a1e78081e7419,0x1e78074223b93b,0x98064213793798,0x541e37a37a804,0x80380280180037,0x93b93da37937a3,0xb83b937a1eb000,0x37837837,0x93bc1ed0000000,0x1ee000000000]) [(10,0),(51,9),(52,0),(23,2),(41,0),(41,7),(41,8),(16,9),(47,0),(47,7),(47,8),(16,10),(47,1),(47,38),(47,39)]
def stateEntry54 : Entry := row 5 [0x80808080,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 7 (packWords [0x40e36b,0x1e71e74102e737,0x32e740e36b3733,0x6b8112e71e71e7,0x4222e74222e742,0x236b3b936b4222,0xe73b92e742236b,0x81036b4212e742,0x12e74213ad3793,0x694212e73792e7,0x4213ad80f3ad41,0xe2e741e2e741e3,0xce37a36a41e2e7,0x37a2e741e3ce80,0xe3ce80d2e780c2,0xe741036b40736b,0x4102e74072e780,0xb36b80a36b4221,0xe74221e7422373,0x3b93734221e73b,0x91e74223738093,0x734211e74211e7,0x4213b537937142,0x11e73791e74213,0xb58083b541e1e7,0x41e1e741e3d637,0xa37241e1e737a1,0xe741e3d68073d6,0x8061e78051e740,0xe37341937340e1,0xe74191e7804373,0x8033734213da37,0x93794213b93dc3,0xb94213da3dc3da,0x41e3b937937941,0xe3b937a37a41e3,0xda3bc3b841e3b9,0x3bc3b941e3da37,0xa37a42280241d1,0xeb000000000000,0x0,0x41e3,0x793bc37841e3dc,0x37a37841e37937,0xa37941e3dc3bc3,0xbc42180141c1ed,0x0,0x0,0x41e800,0x41e1ee00000000,0x0,0x0]) [(6,31),(6,40),(6,41),(17,0),(20,0),(29,14),(31,14),(48,0),(48,7),(48,8),(17,10),(20,1),(29,2),(31,2),(48,1),(48,38),(48,39),(53,0)]
def stateEntry55 : Entry := row 5 [0xaaaaaa,0x5500ff00,0xaa00aa00,0xcccccccc,0xf0f0f0f0,0xffff0000] 5 (packWords [0x1eb2e32e71eb,0x1ed2e52e71ed36,0x22e73722e73c62,0xe73ce2e72e62e6,0x2e73ce1e91e91e,0xb3791eb2f31eb2,0xf31eb2f31eb2f3,0x1eb2f21eb3b91e,0xd2f51ed2f51ed2,0xf51ed2f51ed2f4,0x1ed3791e71e737,0xa3721ee1ee3732,0xf62f63d64032f6]) []
def stateEntry56 : Entry := row 5 [0xaaaaaa,0xaa000000,0xaa00aa00,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x3c62e73ce2e71e,0xb2e32e71eb1ed2,0xe52e71ed8012e7,0x40600040500000,0x2e62e62e73,0xce2f31eb1eb2f3,0x2f51ed1ed2f51e,0x70000000008000,0x2f63d6,0x4032f61e91e91e,0xb3791eb2f31eb2,0xf33b91eb3b91eb,0x1eb2f21eb3b91e,0xd2f51ed2f53791,0xed3791ed1ed2f4,0x1ed37937a00000,0x1ee4032,0xf6000000402000]) [(55,0),(3,5)]
def stateEntry57 : Entry := row 5 [0xaaaaaa,0xaa000000,0xcccccccc,0xf0f0f0f0,0xff000000,0xff00ff00,0xffff0000] 6 (packWords [0x1e72e74040003c,0xe0000000001eb2,0xe32e71eb1ed2e5,0x2e71ed40500000,0x1ee2e62e71,0xee3d6000000000,0x1e31e31e72f31e,0x51e51e72f54230,0x1e61e6,0x1e72f61eb3b93b,0x91eb1ed3793791,0xed403000000000,0x4030001e,0x91e91eb37937a1,0xeb3b91eb1ea1ea,0x1eb3b93781ed37,0x91ed1ec1ec1ed3,0x79000000403000]) []
def stateEntry58 : Entry := row 5 [0x28a8a8a8,0xc0c0c0c0,0xff00ff00,0xffff0000] 3 (packWords [0x1e,0x72e736b1e71eb2,0xe32e71eb1ee2e6,0x2e71ee1e31e31e,0x72f31e61e61e72,0xf61e81e81eb378]) []
def stateEntry59 : Entry := row 5 [0x2aaaaaaa,0xc0c0c0c0,0xfc00fc00,0xffff0000] 3 (packWords [0x1e,0x72e736b1e71eb2,0xe12e71eb1ee2e6,0x2e71ee1e11e11e,0x72f11e61e61e72,0xf61ea1ea1eb37a]) []
def stateEntry60 : Entry := row 5 [0x2aaaaaaa,0xc0c0c0c0,0xfcfcfcfc,0xff00ff00,0xffff0000] 4 (packWords [0x1e72e736,0xb1e72e73692e78,0x21eb2e32e71eb,0x1ee2e62e71ee1e,0x73711e78011e31,0xe31e72f31e61e6,0x1e72f61e900000,0x3781ee1ee8,0x1ea1ea1eb37a]) [(58,0),(59,0),(59,1)]
def stateEntry61 : Entry := row 5 [0x2aaaaaaa,0xc0c0c0c0,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (packWords [0x1e72e736b1e7,0x2e736b2e736b2e,0x73692e73ad2e73,0x6b2e736b1ee2e6,0x2e71ee1e73731e,0x73731e73711e73,0xb51e73731e7373,0x1e61e61e72f637,0x93b98000001eb0,0x37a1ee,0x1ee37a1ed00000,0x3781ee1ee3,0xbc37a1ee1ee37a]) [(60,0)]
def stateEntry62 : Entry := row 5 [0x80008000,0x88888888,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x3632e736b2e72e,0x32e32e736b2e73,0xad2e73ad2e73ac,0x2e73ce2e73ad2e,0x73ad8002e74252,0xe72f33733b52f3,0x3733b53733b537,0x33b43733d63733,0xb53733b51e7000,0x2f33b92f,0x33b92f33b82f33,0xda2f33b92f33b9,0x1eb0000000003b,0xc3dc4080002f50,0x409000,0x2f600000,0x4240000000,0x409000000000]) [(61,10)]
def stateEntry63 : Entry := row 5 [0xaaaaaaa,0xa0a0a0a0,0xcccccccc,0xf000f000,0xff00ff00,0xffff0000] 5 (packWords [0x3632e736b2e7,0x3ca2e73ce2e71e,0xd2e52e71ed2e32,0xe32e736b2e736a,0x2e73ad1e700000,0x2f51ed1ed2,0xf52f33733bc2f3,0x3723723734262f,0x51ed1ed2f51eb1,0xeb3bc2f337a3da,0x40237a1ed2f11e,0xd3791ed3781ed3,0xdc1ee1ee2f337a]) []
def stateEntry64 : Entry := row 5 [0xaaaaaaa,0xaaaaaaaa,0xcccccccc,0xf000f000,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x3632e736b2e72e,0x32e32e736b3ce2,0xe73ce2e71ed2e5,0x2e71ed2e73ac2e,0x73ce2e73ce2e73,0xad2f3373413000,0x1e70000000002f,0x51ed1ed2f53733,0xbc373802373428,0x3734261eb00000,0x2f11ed1ed3,0x792f33bc2f3801,0x2f34282f34292f,0x51ed1ed2f54113,0xbc3bc800411428,0x4024271ed3dc1e,0xd3bc1ed3dc1ed3,0xdc1ee000000000]) [(18,0),(63,0),(63,15)]
def stateEntry65 : Entry := row 5 [0x88808880,0xe000e000,0xffff0000] 2 (packWords [0x1e72e73a,0xd1e71ed2e02e71,0xed1e01e01e72f0]) []
def stateEntry66 : Entry := row 5 [0x80808080,0xe800e800,0xffff0000] 2 (packWords [0x1e72e736,0xb1e71eb2e02e71,0xeb1e01e01e72f0]) []
def stateEntry67 : Entry := row 5 [0x80808080,0x88008800,0xe000e000,0xffff0000] 3 (packWords [0x3a,0x2e73ad2e73602,0xe736b2e72e02e0,0x2e736b1e71e780,0x23701eb1eb8012,0xf01ed1ed8002f0]) [(65,0),(66,9),(66,0)]
def stateEntry68 : Entry := row 5 [0x88808880,0xeeee0000,0xf000f000] 2 (packWords [0x2e71e73a,0xc1e71e01e01e72,0xf11ec2e02e71ec]) []
def stateEntry69 : Entry := row 5 [0x80808080,0xea00ea00,0xfcfc0000] 2 (packWords [0x1e72e736,0x91e71e92e02e71,0xe91e01e01e72f2]) []
def stateEntry70 : Entry := row 5 [0x80808080,0x88008800,0xeeee0000,0xf000f000] 3 (packWords [0x2e,0x73a03ac2e71e71,0xe78023711eb1eb,0x8012f13602e736,0xb2e72e02e02e73,0x6b1ec1ec8002f1]) [(68,0),(69,9),(69,8)]
def stateEntry71 : Entry := row 5 [0x80808080,0x88008800,0xeeeeeeee,0xf000f000,0xffff0000] 4 (packWords [0x3a12e73a,0xd2e72e73ac2e78,0x13612e736b2e7,0x2e12e12e736b3b,0x3b03b18001e71,0xe742a3711eb1eb,0x42b2f137000000,0x2f00000000,0x1ed1ed42a2f1]) [(67,0),(70,0)]
def stateEntry72 : Entry := row 5 [0x80808080,0x88008800,0xaaaaaaaa,0xcccccccc,0xf000f000,0xffff0000] 5 (packWords [0x3a12e73ad2e7,0x2e73ad2e73ad2e,0x73ac2e73ce3632,0xe736b2e72e32e3,0x2e736b3d03b13b,0x33b13b03b03b13,0xd21e71e7422373,0x1eb1eb42c2f33b,0xc3dc8003bc3710,0x2f1000,0x37200000,0x2f20000000,0x2f33734222f3]) [(71,0)]
def stateEntry73 : Entry := row 5 [0x80808080,0x88008800,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x36b2e736b2e72e,0x736b2e736b2e73,0xad2e73ad2e73ac,0x2e73ce36b2e736,0xb2e72e736b2e73,0x6b3b13b13b5802,0x3d43b53d63b53b,0x43b43b53d61e70,0x8013b5,0x42c3b53d83b93d,0xa3b93b83b83b93,0xda8003b94223b9,0x1eb0000000003b,0xc3dc42e3bc3790,0x2f5000,0x37a00000,0x2f60000000,0x42d40f41a408]) [(18,13),(18,14),(72,0)]
def stateEntry74 : Entry := row 5 [0xaaaaaa,0xaa00aa00,0xcc000000,0xcccccccc,0xf0f0f0f0,0xffff0000] 5 (packWords [0x1eb2e32e71eb,0x1ed2e52e71ed3c,0x60000000001e72,0xe737a1e72e62e6,0x2e73ad1e91e91e,0xb3b93d21eb3d61,0xeb1e31e31e72f3,0x1eb2f21eb3b937,0x90000000001e51,0xe51e72f51ed2f4,0x1ed8001e737237,0xa1e700000042f0,0x1e61e61e72f6]) [(0,7)]
def stateEntry75 : Entry := row 5 [0xaaaaaa,0xaaaaaaaa,0xcc000000,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x1e72e74321e71e,0xb2e32e71eb1ed2,0xe52e71ed3ce000,0x2e737a2e,0x78022e74312e73,0xad1e31e31e72f3,0x1e51e51e72f53d,0x60000000001e73,0x7a1e78011e7431,0x1e73b51e91e91e,0xb3b93da1eb3da1,0xeb1eb3b81eb37a,0x1eb3b91eb3b937,0x90000000001ed3,0x7a1ed3bc1ed430,0x1ed8003bc37a37,0xa3bc00000042f0,0x1ee000000000]) [(1,7),(74,0),(74,1)]
def stateEntry76 : Entry := row 5 [0x80808080,0xaa00aa00,0xcc00cc00,0xf8f80000] 3 (packWords [0x36,0x92e736b2e736a2,0xe736b2e71eb2e0,0x2e71eb1e71e780,0x3b31e91e91eb2,0xf31ea1ea1eb2f3]) [(69,39)]
def stateEntry77 : Entry := row 5 [0x80808080,0xaa00aa00,0xcc00cc00,0xf8f8f8f8,0xffff0000] 4 (packWords [0x2e73a92e,0x780036b2e736b2,0xe736b2e736b2e7,0x1eb2e32e71eb37,0x93793d33b937a3,0x7a3b33da2f0000,0x1e71e743,0x33b31ed1eb1eb2,0xf31ee1eb1eb2f3]) [(76,0)]
def stateEntry78 : Entry := row 5 [0x80808080,0x88888888,0xaa00aa00,0xcc00cc00,0xf0f0f0f0,0xffff0000] 5 (packWords [0x2e736b2e736b,0x36b2e736b2e736,0xb2e736b2e72e73,0xad2e73ad2e736b,0x2e736b3d03b93d,0x43b93b03b03b43,0xda8013b9800000,0x1eb0000000001e,0x71e741e3b43793,0x7941e3d442d3d4,0x41a3d437a37a42,0x13b44343b44183,0xb42f4000000000]) [(77,0),(4,24)]
def stateEntry79 : Entry := row 5 [0x80808080,0x88888888,0xaa00aa00,0xcccccccc,0xf000f000,0xffff0000] 5 (packWords [0x3a92e73ad2e7,0x2e73ad2e73ad36,0x32e736b2e72e73,0xad2e73ad2e32e3,0x2e736b3d03b93d,0x23b91e71e73b93,0x738003b93d33b9,0x1eb1eb4362f33b,0xc3733733bc3790,0x435000,0x37237237,0x33bc2f337342c2,0xf32f2000000000]) [(0,24)]
def stateEntry80 : Entry := row 5 [0x80808080,0x88888888,0xaa00aa00,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x36b2e736b2e72e,0x736b2e736b2e73,0xad2e73ad36b2e7,0x36b2e72e73ad2e,0x73ad2e736b2e73,0x6b3d23b93b9804,0x3d43d43d68031e,0x70000000008023,0xd640e3d68013d6,0x42c3d63d83b93d,0xa3b93b83b83b93,0xda8003b9420000,0x1eb0000000003b,0xc3dc4213bc3790,0x41c000,0x37a37a42,0x13bc4343bc4183,0xbc2f6000000000]) [(5,24),(63,14),(74,42),(78,0),(79,0)]
def stateEntry81 : Entry := row 5 [0x80808080,0xe8008800,0xffff0000] 2 (packWords [0x1e72e736,0xb1e71eb2e02e71,0xeb1e01e01e72f0]) []
def stateEntry82 : Entry := row 5 [0x80808080,0xe888e888,0xff00ff00,0xffff0000] 3 (packWords [0x1e,0x72e736b1e72e73,0x682e78011eb2e3,0x2e71eb1e73701e,0x78001e31e31e72,0xf31e8000000000]) [(66,0),(81,1)]
def stateEntry83 : Entry := row 5 [0x80808080,0xea00c000,0xfcfc0000] 2 (packWords [0x1e72e736,0xe1e71ee2e02e71,0xee1e01e01e72f2]) []
def stateEntry84 : Entry := row 5 [0x80808080,0xeac0eac0,0xfc00fc00,0xffff0000] 3 (packWords [0x1e,0x72e736b1e72e73,0x6a2e78011eb2e6,0x2e71eb1e73701e,0x78001e61e61e72,0xf61ea000000000]) [(66,0),(83,1)]
def stateEntry85 : Entry := row 5 [0x80808080,0xea00c000,0xfcfcfcfc,0xffff0000] 3 (packWords [0x2e,0x73792e78011e72,0xe736e1e71ee2e2,0x2e71ee3701e71e,0x78002f00000000,0x1e21e21e72f2]) [(81,43),(83,0)]
def stateEntry86 : Entry := row 5 [0x80808080,0xeac0eac0,0xfcfc0000,0xff00ff00] 3 (packWords [0x2e,0x71e73691e71e73,0x721e78011e61e6,0x1e72f62e73682e,0x78001e92e62e71,0xe91e8000000000]) [(81,33),(69,0)]
def stateEntry87 : Entry := row 5 [0x80808080,0xeac0eac0,0xfcfcfcfc,0xff00ff00,0xffff0000] 4 (packWords [0x1e72e736,0xb1e72e73692e78,0x32e736a2e7802,0x1eb2e62e71eb1e,0x73791e78011e73,0x721e74331e61e6,0x1e72f637837837,0x98001e90000000,0x1ea000000000]) [(82,43),(84,0),(85,1),(86,0)]
def stateEntry88 : Entry := row 5 [0x80808080,0xaaaaaaaa,0xcccccccc,0xf8008800,0xffff0000] 4 (packWords [0x1e72e736,0xb1e72e73dc2e73,0xab2e73bc2e73cb,0x1eb2e32e71eb1e,0x73711e73b11e73,0x721e73d21e31e3,0x1e72f337c37c80,0x3bc2f10000000,0x2f2000000000]) [(85,8)]
def stateEntry89 : Entry := row 5 [0x80808080,0xaaaaaaaa,0xcccccccc,0xf888f888,0xff00ff00,0xffff0000] 5 (packWords [0x1e72e736b1e7,0x2e73a92e78012e,0x736d2e73ab2e73,0x6e2e73cb1eb2e3,0x2e71eb1e73b11e,0x74221e73dc1e73,0xb31e73bc1e73d3,0x1e31e31e72f337,0x93793da3b937a3,0x7a3b93da437000,0x37c37c80,0x3bc1ed0000000,0x1ee000000000]) [(87,8),(88,1)]
def stateEntry90 : Entry := row 5 [0x80808080,0x88888888,0xaaaaaaaa,0xcccccccc,0xf000f000,0xff00ff00,0xffff0000] 6 (packWords [0x3632e736b2e73a,0x92e73ad2e72e73,0xad2e73ad2e73ac,0x2e73ce2e73ad2e,0x73ad2e32e32e73,0x6b1e7000000000,0x3733dc37380437,0x33bc3738033734,0xe3738022f3373,0x42c2f33d83b93d,0xa3b93b83b83b93,0xda8013b98003b9,0x1eb1eb4362f33b,0xc3dc4390003790,0x435000,0x37a00000,0x4380000000,0x435000000000]) [(89,0),(1,24),(72,0),(79,0),(79,7)]
def stateEntry91 : Entry := row 5 [0x80808080,0x88888888,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 7 (packWords [0x36b1e71e72e737,0x32e736b37336b2,0xe71e71e72e7422,0x2e736b3b936b2e,0x73b92e736b8113,0x6b2e74212e73ad,0x3dc3ad2e73dc2e,0x73ad8103ad2e74,0x1e2e73ce3bc3ac,0x2e73bc2e73ce80,0xf3ce2e780e2e73,0xad4103ad2e7410,0x2e73ad80d3ad2e,0x780c2e736b4253,0x6b2e74252e736b,0x80b36b1e74221e,0x73733b93731e73,0xb91e737380a373,0x1e74211e73b53d,0xc3b51e73dc1e73,0xb58093b51e741e,0x1e73d63bc3b41e,0x73bc1e73d68083,0xd61e78071e73b5,0x40e3b51e740e1e,0x73b58063b51e78,0x51e737342c373,0x1e742c1e737380,0x43733da4213d83,0xb93dc3b93da3dc,0x3da3b941e3b93b,0x941e3b83da3bc3,0xb83b93bc3b93da,0x4213da80242280,0x33b94223b94224,0x22422000000000,0x80241d1eb00000,0x0,0x41e3bc,0x3bc3dc4213dc41,0xe41e41e0000000,0x41e41e379000,0x0,0x8014,0x1c41c000000000,0x0,0x42141e37a0,0x0,0x80,0x41e43a0000000,0x0,0x42241c41,0xc0000000000000,0x0]) [(56,31),(56,40),(57,41),(6,41),(62,0),(64,14),(73,0),(75,42),(80,0),(80,7),(90,0),(62,16),(64,2),(73,16),(75,44),(80,1),(80,38),(90,1)]
def stateEntry92 : Entry := row 5 [0x888888,0xaa222222,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (packWords [0x1e72e73ad1e7,0x1eb2e32e71eb2e,0x73692e73ad36a2,0xe737a2e71ee2e6,0x2e71ee1e31e31e,0x72f31e73711e73,0xb53721e737a1e7,0x1e61e61e72f61e,0xb3b91eb37937a1,0xeb3b91eb1ea1ea,0x1eb3b937837837,0x93bc1ec0000000,0x402000]) []
def stateEntry93 : Entry := row 5 [0x80aaaaaa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (packWords [0x1e72e73ce1e7,0x1eb2e32e71eb1e,0xd2e52e71ed2e73,0x6a2e73ce2e73ce,0x2e736b1e31e31e,0x72f31e51e51e72,0xf51e73721e73d6,0x1e73d61e73731e,0x91e91eb3791eb3,0xb81eb37a1eb3b9,0x1eb3b91ed3781e,0xd3bc1ed3791ed3,0x791ee000000000]) []
def stateEntry94 : Entry := row 5 [0x888888,0xaaaaaaaa,0xcccccccc,0xf000f000,0xf0f00000] 4 (packWords [0x1e32e33a,0xd1e32e33ad2e33,0x612e33ac2e3362,0x2e33ad2e33631e,0x33b51e33611e33,0xb41e33621e33b5,0x1e336336036036,0x13bc1ed0000000,0x1ee000000000]) []
def stateEntry95 : Entry := row 5 [0x888888,0xaaaaaaaa,0xcccccccc,0xf000f000,0xf0f0f0f0,0xffff0000] 5 (packWords [0x2e32e32e7800,0x1e72e73ad1e72e,0x73612e73ad2e73,0x622e73ce2e7373,0x2e73631e300000,0x2f33dc2f33,0x712f33bc2f3372,0x2f343b2f33731e,0x73b51e73711e73,0xb41e73721e73b5,0x1e737337037037,0x13bc1ed0000000,0x1ee000000000]) [(94,0)]
def stateEntry96 : Entry := row 5 [0x888888,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x3ad1e71e,0x72e73b52e73ad3,0xb53ad2e71e71e7,0x2e71eb1eb4472f,0x32e32e72f32e78,0x51eb1eb2e7442,0x2e73ad3793692e,0x73792e73ad4473,0xad2e743c2e73ce,0x37a36a2e737a2e,0x73ce4473ce2e74,0x462e73ad4453ad,0x2e74442e73ad44,0x336b1e72f31e34,0x411eb1e31e71eb,0x1e78042f32f31e,0x74421e73b53793,0x711e73791e73b5,0x4413b51e743c1e,0x73d637a3721e73,0x7a1e73d64413d6,0x1e74401e73b543,0xf3b51e743e1e73,0xb543d3731eb379,0x1eb3b93dc3b91e,0xb3dc1eb3b93793,0x791eb37a1eb3da,0x3bc3b81eb3bc1e,0xb3da37a37a1eb8,0x31eb3b943b3b9,0x1eb43b1eb3b980,0x23b93793bc3783,0xdc37a37837937a,0x3793dc3bc3bc80,0x14311ed0000000,0x0,0x80043c1e,0xe0000000000000,0x0]) [(92,0),(92,7),(52,0),(93,41),(95,0),(95,1)]
def stateEntry97 : Entry := row 5 [0xaaaaaa,0xaa0a0a0a,0xcccccccc,0xf000f000,0xffff0000] 4 (packWords [0x1e72e73b,0x91e71ed2e52e71,0xed3622e72e32e3,0x1ee2e22e71ee1e,0x51e51e72f52f31,0xe71e31e31e21e2,0x1e72f23701ed2f,0x11ed1ec1ec1ed3,0x711ee3722f31ee]) []
def stateEntry98 : Entry := row 5 [0xaaaaaa,0xaa0a0a0a,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (packWords [0x1e72e73ce1e7,0x2e73b92e78011e,0xd2e52e71ed36a2,0xe737a2e71ee2e6,0x2e71ee1e73b91e,0x78001e51e51e72,0xf53721e737a1e7,0x1e61e61e72f637,0x91ed1ed37937a3,0xb81eb1eb1ea1ea,0x1ee3b93781ed37,0x91ed1ec1ec1ed3,0x791ee37a4021ee]) [(97,0),(97,1)]
def stateEntry99 : Entry := row 5 [0x888888,0xaaaaaa,0xaaaaaaaa,0xcc00cc00,0xf0f0f0f0,0xffff0000] 5 (packWords [0x1eb2e32e71eb,0x1e72e73791e72e,0x736a2e73ce2e73,0xb52e73a52e52e5,0x2e73ce1e31e31e,0x72f31eb3b01eb3,0x7a1eb3b51eb3b1,0x1eb2f11eb3b91e,0x73701e73b41e73,0x791e73711e51e5,0x1e72f580100000,0x8000000000,0x400000000000]) [(97,3),(0,0)]
def stateEntry100 : Entry := row 5 [0x888888,0xaaaaaa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x1e72e73ce1e71e,0xb2e32e71eb2e73,0x792e78042e736a,0x2e73ce2e73ce2e,0x73ad2e73ce2e73,0xce1e31e31e72f3,0x1e73791e78031e,0x73721e73d61e73,0xd61e73b51e73d6,0x1e73d61eb3b91e,0xb3791eb3b81eb3,0x7a1eb3b91eb3b9,0x1eb3b91eb3b937,0x83783793bc8023,0x794420001ed000,0x80100000,0x8000000000,0x401000000000]) [(98,3),(1,0),(92,7),(99,0),(99,1)]
def stateEntry101 : Entry := row 5 [0x80008888,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (packWords [0x1e73733731e7,0x1eb2f32f31eb2e,0x52e52f53ad2e62,0xe62f63ce8003ad,0x2e72e71e31e31e,0x72f31e73711e72,0xf51e73721e72f6,0x1e73731e73731e,0xb2f11eb3791eb2,0xf21eb37a1eb2f3,0x1eb2f32f42f42f,0x53bc1ed0000000,0x1ee000000000]) [(9,10)]
def stateEntry102 : Entry := row 5 [0x888aaaa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (packWords [0x1e72e736b1e7,0x1eb2e32e71eb1e,0xd2e52e71ed2e73,0xac2e73ce2e73ce,0x2e73ad1e31e31e,0x72f31e51e51e73,0xb51e73b41e73d6,0x1e73b51e73b51e,0x91e91eb3b91eb3,0xb81eb3da1eb3b9,0x1eb3b91ed3dc1e,0xd3bc1ed2f51ed3,0xdc1ee000000000]) []
def stateEntry103 : Entry := row 5 [0x8080aaaa,0xaa00aa00,0xcc00cc00,0xf0f0f0f0,0xffff0000] 4 (packWords [0x1eb2e12e,0x51eb1ed2e53791,0xed36a2e52ed2e5,0x2e42e42e536b1e,0x91e91eb3791eb3,0xb01eb37a1eb2f0,0x1eb3b91e51e51e,0xd3b41ed3791ed2,0xf41ee1ee4192f4]) []
def stateEntry104 : Entry := row 5 [0x8080aaaa,0xaa00aa00,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (packWords [0x3c62e73ce2e7,0x1eb2e32e71eb1e,0xd2e52e71ed36a2,0xe737a2e72e62e6,0x2e736b3d21eb1e,0xb8013d41ed1ed8,0x1e7000000000,0x2f63d64192f61e,0x91e91eb3791eb3,0xb81eb37a1eb2f2,0x1eb3b91ed3781e,0xd3bc1ed2f41ed3,0x791ee1ee4192f6]) [(103,0),(103,3)]
def stateEntry105 : Entry := row 5 [0x8080aaaa,0xaaaaaaaa,0xcc00cc00,0xf000f000,0xffff0000] 4 (packWords [0x1eb2e12e,0xd1eb1ed2e12eb1,0xed2e136a2e13ce,0x2e12f12e136b1e,0x11e11eb3711eb3,0xb01eb37a1eb3b1,0x1eb2f11ed3701e,0xd3bc1ed3711ed2,0xf11ee000000000]) []
def stateEntry106 : Entry := row 5 [0x8080aaaa,0xaaaaaaaa,0xcc00cc00,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (packWords [0x3ce2e52ed2e5,0x1eb2e12e51eb1e,0xd2e53791ed2e53,0x6a2e53ce2e52f5,0x2e536b3b11eb1e,0xb8011e50000000,0x3b437a37a800,0x2f53b54192f51e,0x91e91eb3791eb3,0xb81eb37a1eb2f1,0x1eb3b91ed3781e,0xd3bc1ed3791ed2,0xf51ee000000000]) [(103,0),(105,0)]
def stateEntry107 : Entry := row 5 [0x8080aaaa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x3ce1e71e,0x72e73732e73ce3,0x733732e71e71e7,0x2e71eb1eb4513b,0x92e32e73b92e74,0x511eb1eb2e71ed,0x1ed4503792e52e,0x73792e74501ed1,0xed2e74482e73ce,0x37a36a2e737a2e,0x73ce4103ce2e74,0x482e73ce4023ce,0x2e74022e73ce45,0x236b1e74511e33,0x731eb1e31e71eb,0x1e73738053731e,0x74501e53b51ed1,0xe51e71ed1e73b5,0x8043b51e74481e,0x73d637a3721e73,0x7a1e73d68033d6,0x1e78021e737341,0x93731e74191e73,0x738013731eb379,0x1e93b91ed1e91e,0xb1ed1eb3b93793,0x791eb37a1eb3da,0x3bc3b81eb3bc1e,0xb3da37a37a1eb4,0x4f1eb3b944e2f3,0x1eb44d1eb3b944,0xc3b91ed3bc1ed3,0xdc37a3781ed37a,0x1ed3dc3bc3bc1e,0xd44b1ed3794442,0xf51ed44a1ed379,0x4493798004481e,0xe0000000000000,0x0]) [(92,31),(101,9),(102,45),(104,0),(106,0),(106,3)]
def stateEntry108 : Entry := row 5 [0xaaaaaa,0xaaaaaaaa,0xcc444444,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x1e72e73ce1e71e,0xb2e32e71eb1ed2,0xe52e71ed3ce2e7,0x3ce2e72e736a2e,0x73ce2e73ce2e73,0xad1e31e31e72f3,0x1e51e51e72f53d,0x61e73d61e71e73,0x721e73d61e73d6,0x1e73b51e91e91e,0xb3b93da1eb3da1,0xeb1eb3b81eb37a,0x1eb3b91eb3b937,0x90000000001ed3,0x7a1ed3bc000442,0x1ed8013bc37a37,0xa3bc00000042f0,0x800000000000]) [(2,2),(92,7)]
def stateEntry109 : Entry := row 5 [0x88f8f8f8,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (packWords [0x1e72e736b1e7,0x1eb2e32e71eb1e,0xd2e52e71ed1ee2,0xe62e71ee2e7454,0x2e73ad1e31e31e,0x72f31e51e51e72,0xf51e61e61e72f6,0x1e74531e73b51e,0xb1ed1eb3b91eb1,0xee1eb3da1eb3b9,0x1eb3b91ec1ec1e,0xd3bc1ed3791ed3,0xdc1ee37a1ee3bc]) []
def stateEntry110 : Entry := row 5 [0x2a2a2a,0xaaaaaaaa,0xcc00cc00,0xf0f00000] 3 (packWords [0x1e,0x72e73ca1e71ea2,0xe02e71ea1eb2e7,0x2e11eb1e01e01e,0x72f42f51e71e11,0xe1800000000000]) [(32,21)]
def stateEntry111 : Entry := row 5 [0x2a2a2a,0xaaaaaaaa,0xcc00cc00,0xf0f0f0f0,0xffff0000] 4 (packWords [0x2e72f92e,0x78011e72e73791,0xe71ee2e42e71ee,0x4192e72e52e537,0x91e71e72f91ea1,0xea1ee37a4002f5,0x1eb1eb1e41e41e,0x72f42f51e71e51,0xe5800000000000]) [(33,21),(110,0)]
def stateEntry112 : Entry := row 5 [0x2a2a2a,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (packWords [0x1e72e73ce1e7,0x2e73b92e78042e,0x73792e78031ee2,0xe62e71ee4192e7,0x36b2e71e73b91e,0x78021e73791e78,0x11e61e61e72f6,0x4071e73731e737,0x93b93da3791ea1,0xea1ee37a4003b9,0x1eb1eb1ec1ec1e,0xe3bc43b3791ed1,0xed800000000000]) [(40,17),(111,0),(111,3),(111,31),(111,20)]
def stateEntry113 : Entry := row 5 [0xaaaaaa,0x2a2a2a2a,0xcc00cc00,0xf0f00000] 3 (packWords [0x1e,0x72e73ca1e71eb2,0xe72e11eb1ea2e0,0x2e71ea2f51e71e,0x11e11e01e01e72,0xf41ea36a1eb1ea]) []
def stateEntry114 : Entry := row 5 [0xaaaaaa,0x2a2a2a2a,0xcc00cc00,0xf0f0f0f0,0xffff0000] 4 (packWords [0x2e73b92e,0x78001e72e73791,0xe736a2e72e52e5,0x1ee2e42e71ee37,0x91e71e737937a2,0xf51eb1eb1ea1ea,0x1ee3b12f51e71e,0x51e51e41e41e72,0xf41ee37a2f51ee]) [(113,0)]
def stateEntry115 : Entry := row 5 [0xaaaaaa,0x2a2a2a2a,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (packWords [0x1e72e73ce1e7,0x2e73b92e78042e,0x73792e780336a2,0xe737a2e71ee2e6,0x2e71ee1e73b91e,0x78021e73791e78,0x13721e737a1e7,0x1e61e61e72f637,0x93b93da37937a3,0xb81eb1eb1ea1ea,0x1ee3b93783781e,0xd1ed1ec1ec1ee3,0x791ee37a8001ee]) [(9,0),(114,0),(114,3),(114,31),(114,20)]
def stateEntry116 : Entry := row 5 [0xaaaaaa,0xaaaaaaaa,0xc0c0c0c0,0xcc00cc00,0xf0f00000] 4 (packWords [0x1e72e73c,0xe1e71eb2e12e71,0xeb2e73a02e736a,0x2e73b52e736b1e,0x11e11e72f51e73,0x601e73b41e736b,0x1e73611eb8011e,0xb36a1eb8001eb3,0x6b1ee000000000]) [(110,0),(113,0)]
def stateEntry117 : Entry := row 5 [0xaaaaaa,0xaaaaaaaa,0xc0c0c0c0,0xcc00cc00,0xf0f0f0f0,0xffff0000] 5 (packWords [0x2e73b92e7804,0x1e72e73791e72e,0x52e52e78032e73,0x6a2e73ce2e73b5,0x2e736b3791e71e,0x73791eb0000000,0x37a3b03b437a,0x8023b53b13b11e,0x51e51e72f51e73,0x701e73b41e7379,0x1e73712f58012f,0x537a2f58002f53,0xb51ee000000000]) [(111,0),(114,0),(103,46),(36,1),(116,0)]
def stateEntry118 : Entry := row 5 [0xaaaaaa,0xaaaaaaaa,0xc0c0c0c0,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x1e72e73ce1e72e,0x73b92e780c2e73,0x792e780b2e7456,0x2e780a2e736a2e,0x73ce2e73ce2e73,0x6b1e73b91e7809,0x1e73791e78081e,0x74551e78071e73,0x721e73d61e73d6,0x1e73733793b944,0x20001eb0000000,0x37a3b83b937a,0x8063b943b3b91e,0xd0000000003783,0x783793bc805379,0x40037937a80440,0x337a8038028018,0x1ee000000000]) [(52,0),(109,43),(112,0),(101,47),(115,0),(104,19),(104,48),(42,0),(117,0),(117,3),(42,1),(117,1),(117,6)]
def stateEntry119 : Entry := row 5 [0xaaaaaa,0xc0ccccc,0xaaaaaaaa,0xcccccccc,0xf000f000] 4 (packWords [0x1e33b91e,0x32e11e33a01e33,0x621e33b91e32e3,0x1e33ad1e33632e,0x13622e13ac1ed0,0x2e12f9,0x2e13ad3622e32e,0x33ac1ee0000000,0x2e33632e33ad]) []
def stateEntry120 : Entry := row 5 [0xaaaaaa,0xc0ccccc,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00] 5 (packWords [0x1e31e31e7800,0x1e73c41e72e51e,0x73621e73d61e73,0xce1e72e71e736b,0x1e73631eb2e11e,0xb3b91eb3a81eb3,0x6a1eb2e71eb2e3,0x1eb3ad1eb36b2e,0x536a2e53ac1ed0,0x2e536b,0x2e53ad36a2e72e,0x73ac1ee0000000,0x2e736b2e73ad]) [(119,0)]
def stateEntry121 : Entry := row 5 [0xaaaaaa,0xaaaaaaaa,0xcc00cc00,0xcccc0000,0xf0f0f0f0] 5 (packWords [0x2f38062e11,0xeb2e51eb2f32e5,0x2e51eb8051eb1e,0xb8041e12f31e51,0xe11eb1e51e52f3,0x8032f31eb37a1e,0xb3da3a43a01eb3,0xa41eb3da37a37a,0x1eb8021eb3b93a,0x53a51eb3a51eb3,0xb98013a13ce1e5,0x1e52e53d62e53c,0xe3d63ce2e51e51,0xe52e53a42e53ce,0x37a36a2e537a2e,0x53ce3a43a42e53,0xa52e53ce45b3ce,0x2e545a2e53ce3a,0x536b1e53a41e53,0xd637a3721e537a,0x1e53d63a43a41e,0x53a51e53d64593,0xd61e54581e53d6,0x3a53738004571e,0xe0000000000000,0x0]) [(4,0),(94,8),(105,48),(36,0),(119,49),(36,1),(119,3)]
def stateEntry122 : Entry := row 5 [0xaaaaaa,0xaaaaaaaa,0xcc00cc00,0xcccccccc,0xf0f00000,0xf0f0f0f0] 5 (packWords [0x2e3000000000,0x1eb2f51eb8021e,0x31e31e78011eb3,0xb41eb36a1eb3b5,0x1eb36b2e52e52e,0x78001e72e73ce1,0xe72e73a42e736a,0x2e73b52e736b1e,0x50000000002f53,0x6a2f53b42f536b,0x2f53b51e73621e,0x73b41e736b1e73,0x631ee000000000]) [(36,1),(36,3),(116,0)]
def stateEntry123 : Entry := row 5 [0xaaaaaa,0xaaaaaaaa,0xcc00cc00,0xcccccccc,0xf0f0f0f0,0xffff0000] 6 (packWords [0x2e71eb1e,0xb45f2f32e32e72,0xf32e78081eb1eb,0x2e74422e54422f,0x52e52e72f52e74,0x4245f8073ce1e7,0x1e72e73d62e73c,0xe3d63ce2e71e71,0xe72e745c2e73ce,0x37a36a2e737a2e,0x73ce45f3ce2e74,0x5c2e73ce3b53b5,0x2e73b52e73ce45,0xe36b1eb4421eb3,0xb92f52f11eb2f5,0x1eb3b98063b91e,0xb8051e32f31e71,0xe31eb1e71e72f3,0x8042f31eb37a1e,0xb3da3b43b01eb3,0xb41eb3da37a37a,0x1eb8031eb3b93b,0x53b51eb3b51eb3,0xb98023b145545d,0x1e500000000000,0x0,0x2f53b42f545c,0x37a37a2f537a2f,0x545c3b43b42f53,0xb52f5442400400,0x2f54002f58013b,0x53b51e73b41e73,0xd637a3721e737a,0x1e73d63b43b41e,0x73b51e73d64593,0xd61e74581e73d6,0x3b537380045c1e,0xe0000000000000,0x0]) [(5,0),(99,0),(95,8),(106,46),(42,0),(120,49),(117,0),(121,0),(122,0)]
def stateEntry124 : Entry := row 5 [0xaaaaaa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 7 (packWords [0x4553ce,0x1e71e74552e73d,0x62e74553ce3d63,0xce4032e71e71e7,0x4132e71eb1eb45,0x64562f32e34132,0xe72f32e745680d,0x1eb1eb4422e71e,0xd1ed4564562f52,0xe54422e72f52e7,0x45680c1ed1ed40,0x32e74032e74033,0xce37a36a4032e7,0x37a2e74033ce45,0x63ce4032e74032,0xe74033ce4023ce,0x4032e74022e745,0x53ce46136b4131,0xe72f31e3455455,0x1eb1e34131e71e,0xb1e745580b2f32,0xf34421e72f51e5,0x4554551ed1e544,0x21e71ed1e74558,0xa2f52f54031e7,0x4031e74033d637,0xa3724031e737a1,0xe74033d64553d6,0x4031e74031e740,0x33d64023d64031,0xe74021e74553d6,0x4603734421eb37,0x91e94133b91ed1,0xe94421eb1ed1eb,0x8093b937937940,0x31eb37a1eb4033,0xda3bc3b84031eb,0x3bc1eb4033da37,0xa37a8081eb8071,0xeb4133b943b3b9,0x4131eb43b1eb80,0x63b98053b94031,0xed3bc1ed4033dc,0x37a3784031ed37,0xa1ed4033dc3bc3,0xbc8041ed8031ed,0x44237940037944,0x21ed4001ed8023,0x79801379403800,0x4031ee00000000,0x0,0x0]) [(6,0),(96,0),(100,0),(107,19),(108,0),(96,8),(100,3),(107,48),(108,3),(118,0),(123,0),(123,3),(123,1),(123,6)]
def stateEntry125 : Entry := row 5 [0x88888888,0xeac0eac0,0xf000f000,0xffff0000] 3 (packWords [0x1e,0x72e73ad1e72e32,0xe32e78001ed2e6,0x2e71ed1e31e31e,0x72f31e61e61e72,0xf61ec1ec1ed3bc]) [(32,16)]
def stateEntry126 : Entry := row 5 [0x888888,0xaa00aa00,0xcccc0000,0xf0f0f0f0,0xff000000] 4 (packWords [0x1eb3a93a,0xd1eb2e73693792,0xe71e737237a1e7,0x8000002e,0x31eb2e71eb1e31,0xe31e72f31e91e9,0x1eb3b91e72e737,0x91e71ed2e42e71,0xed1e41e41e72f6]) [(125,50)]
def stateEntry127 : Entry := row 5 [0x888888,0xaa00aa00,0xcccccccc,0xf0f0f0f0,0xff000000,0xffff0000] 5 (packWords [0x3ad000000000,0x1eb2e32e71eb2e,0x73792e78011e72,0xe737a1e72e62e6,0x2e74191eb3b93b,0x91eb3d43793798,0x1e737237a1e7,0x4010001e,0xb3b91eb3791e31,0xe31e72f31eb2f2,0x1eb3b93781e71e,0x73bc1ed0000000,0x1e61e61e72f6]) [(0,7),(126,0)]
def stateEntry128 : Entry := row 5 [0x888888,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff000000,0xff00ff00,0xffff0000] 6 (packWords [0x1e72e74410003a,0xd0000000001eb2,0xe32e71eb2e7379,0x2e78052e737a2e,0x78042e74622e74,0x193b5000000000,0x1e31e31e72f31e,0x73791e78031e73,0x7a1e78021e745d,0x1e74071eb3b93b,0x91eb4423793798,0x143c37a37a800,0x4010001e,0xb3b91eb3791eb3,0xb81eb37a1eb3b9,0x1eb3b937837837,0x93bc1ed0000000,0x1ee000000000]) [(1,0),(1,7),(127,0),(127,7),(127,1),(127,38)]
def stateEntry129 : Entry := row 5 [0x8080aaaa,0xaaaaaaaa,0xc0c0c0c0,0xcccc0000,0xf0f0f0f0,0xff00ff00] 5 (packWords [0x1e73731e7373,0x2e71e73731e71e,0x51e51e73731e73,0x721e73d61e7373,0x1e73733792e72e,0x73791e90000000,0x37a3a83ac37a,0x4643ad3a93a91e,0xd2e52e71ed2e73,0x682e73ac2e7379,0x2e73691ed8001e,0xd37a1ed4631ed3,0xad1ee000000000]) [(97,22)]
def stateEntry130 : Entry := row 5 [0x8080aaaa,0xaaaaaaaa,0xc0c0c0c0,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x1e72e73731e72e,0x73b92e78032e73,0x792e78022e7410,0x2e78012e736a2e,0x73ce2e73ce2e73,0x6b1e73731e7373,0x1e73711e73b51e,0x73731e73731e73,0x721e73d61e7373,0x1e73733793b945,0x1eb0000000,0x37a3b83b937a,0x4643b94683b91e,0xd0000000003783,0x783793bc467379,0x46637937a80044,0x837a4024654484,0x1e1ee000000000]) [(98,22),(2,51),(129,0),(129,3)]
def stateEntry131 : Entry := row 5 [0xaaaaaa,0xcccccc,0xaa00aa00,0xcccc0000,0xf0f0f0f0] 4 (packWords [0x2e31eb2e,0x71eb1e31e31e72,0xf31e91e91eb3b9,0x1eb2f21eb3a91e,0x72e73791e71ed2,0xe52e71ed2e62e6,0x2e73691e51e51e,0x73721e61e61e72,0xf61ed2f61ed3ad]) []
def stateEntry132 : Entry := row 5 [0xaaaaaa,0xcccccc,0xaa00aa00,0xcccccccc,0xf0f0f0f0,0xffff0000] 5 (packWords [0x1eb2e32e71eb,0x2e73792e78011e,0x72e737a1e72e73,0xd62e73c62e62e6,0x2e73ad1eb3b91e,0xb3791e31e31e72,0xf31eb3b91eb3b9,0x1eb2f21eb3b937,0x1e71e73b41ed0,0x8002f6,0x2f63791e737a1e,0x73721e61e61e72,0xf64022f62f63d6]) [(97,28),(131,0)]
def stateEntry133 : Entry := row 5 [0xaaaaaa,0xcccccc,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x1e72e74691e71e,0xb2e32e71eb2e73,0x792e78052e737a,0x2e78042e74622e,0x73ce2e743c2e73,0xad1e31e31e72f3,0x1e73791e78031e,0x737a1e78021e74,0x5d1e73d61e743c,0x1e73b51eb3b91e,0xb3791eb3b81eb3,0x7a1eb3b91eb3b9,0x1eb3b91eb3b937,0x83783793bc1ed0,0x801379,0x43037980037a40,0x337a1ee0000000,0x40240140343c]) [(98,3),(98,28),(132,0),(132,7),(132,1),(132,38)]
def stateEntry134 : Entry := row 5 [0xaaaaaa,0x5500ff00,0xaaaa0000,0xcccccccc,0xf0f0f0f0,0xff000000] 5 (packWords [0x1eb3b93b91eb,0x1ed3793791ed2e,0x736246a2e71e73,0xc63ce1e7000000,0x3730001e91e91e,0xb3792e31eb2e71,0xeb1e31e31e72f3,0x1ea1ea1eb3b92e,0x51ed2e71ed1e51,0xe51e72f51ec1ec,0x1ed37900000037,0xa0001ee2e62e71,0xee1e61e61e746a]) []
def stateEntry135 : Entry := row 5 [0xaaaaaa,0xaa00aa00,0xcccc0000,0xcccccccc,0xf0f0f0f0,0xff000000] 5 (packWords [0x1eb3b93b91eb,0x1ed8013d61ed2e,0x73c63d62e71e73,0x7237a1e7000000,0x3ad0001e91e91e,0xb3b92e31eb2e71,0xeb1e31e31e72f3,0x1eb2f21eb3b92e,0x50000000001e51,0xe51e73bc1ed2f6,0x1ed8001e72e737,0xa1e72e62e62e74,0x191e61e61e72f6]) [(126,0),(131,0)]
def stateEntry136 : Entry := row 5 [0xaaaaaa,0xaa00aa00,0xcccccccc,0xf0f0f0f0,0xff000000,0xffff0000] 6 (packWords [0x4554553c,0x60000000000000,0x0,0x2e71eb1eb4062f,0x32e32e72f32e78,0xa1eb1eb2e71ed,0x1ed4062f52e52e,0x72f52e78091ed1,0xed8081e71e72e7,0x37a2e740637a37,0xa2e71e71e72e74,0x32e64032f62e6,0x2e72f62e745541,0x94193d61eb1eb8,0x73b93b93d63b9,0x3b98061eb1eb3d,0x61ed1ed8053793,0x793d6379379804,0x1ed1ed4031e71e,0x73d637a3724033,0x7a37a3d61e71e7,0x0,0x4034034020,0x1eb379,0x1e93b91ed1e91e,0xb1ed1eb3b93793,0x791eb37a1e32f3,0x1e71e31eb1e71e,0x72f337a2f31eb8,0x31eb3b92f62f2,0x1eb2f61eb3b980,0x23b91ed3bc1e52,0xf51e71e51ed1e7,0x1e72f53bc2f51e,0xd8011ed3792f62,0xf41ed2f61ed379,0x8003791e72f61e,0x637a4031e61e74,0x31e737a2f62f6]) [(127,0),(129,52),(127,3),(129,46),(74,0),(132,0),(74,3),(132,3),(134,5),(135,0),(135,3)]
def stateEntry137 : Entry := row 5 [0xaaaaaa,0xaaaaaaaa,0xcc00cc00,0xcccc0000,0xf0f0f0f0,0xff000000] 5 (packWords [0x1eb3b93b91eb,0x2e53ce4422e51e,0x53d64421e53a40,0x37a800000000,0x3a50002e11eb2e,0x51eb1e11e11e52,0xf31eb3b81eb37a,0x1eb3b91eb3b91e,0x52e54551e52e53,0x7a2e53bc2e546c,0x2e54191e537a1e,0x53bc1e546b1e54,0x71ee000000000]) [(4,0)]
def stateEntry138 : Entry := row 5 [0xaaaaaa,0xaaaaaaaa,0xcc00cc00,0xcccccccc,0xf0f0f0f0,0xff000000,0xffff0000] 6 (packWords [0x3ce0000000001e,0xb2e32e71eb2e52,0xe52e78041e72e7,0x4561e72e737a2e,0x78032e745c2e74,0x191eb3b93b91eb,0x2f58024422f51e,0x73d64421e73b40,0x37a801000000,0x3b50001eb2f11e,0xb3b91e31e31e72,0xf31eb3b81eb37a,0x1eb3b91eb3b91e,0x50000000002f53,0x7a2f53bc2f5430,0x2f58001e737a1e,0x73bc1e746b1e74,0x71ee000000000]) [(127,7),(5,0),(132,7),(135,1),(137,0)]
def stateEntry139 : Entry := row 5 [0xaaaaaa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff000000,0xff00ff00,0xffff0000] 7 (packWords [0x4551e71e72e745,0x62e74554554550,0x455455,0x3ce00000000000,0x0,0x2e71eb1eb456,0x2f32e32e72f32e,0x780f1eb1eb2e71,0xed1ed4562f52e5,0x2e72f52e780e1e,0xd1ed2e74032e74,0x337a37a2e737a,0x2e740345680d2e,0x74032e74034034,0x32e74032e7455,0x4194194564553d,0x60000000000000,0x0,0x1e72f31e34551e,0xb1e31e71eb1e78,0xc2f32f31e72f5,0x1e54551ed1e51e,0x71ed1e780b2f52,0xf51e74031e7403,0x37a37a1e737a1e,0x740345580a1e74,0x31e7403403403,0x1e74031e745645,0x54074131eb1eb8,0x93b93b94133b9,0x3b98081eb1eb44,0x21ed1ed8073793,0x79442379379806,0x1ed1ed40340340,0x30000000004033,0x7a37a403800805,0x0,0x4034034020,0x1eb379,0x1e93b91ed1e91e,0xb1ed1eb3b93793,0x791eb37a1eb3da,0x3bc3b81eb3bc1e,0xb3da37a37a1eb8,0x41eb3b946d3b9,0x1eb46d1eb3b980,0x33b91ed3bc1ed3,0xdc37a3781ed37a,0x1ed3dc3bc3bc1e,0xd8021ed3794303,0x791ed4301ed379,0x8013798004031e,0xe0000000000000,0x0]) [(57,0),(128,0),(130,19),(128,8),(130,48),(6,0),(75,0),(133,0),(75,3),(133,8),(136,0),(138,0),(138,3),(136,1),(138,1),(138,6)]
def stateEntry140 : Entry := row 5 [0x88888888,0xa0a0a0a0,0xc0c0c0c0,0xff008800,0xffff0000] 4 (packWords [0x1e72e736,0xb1e72e736b2e73,0x6b2e736b2e736b,0x2e73782e78001e,0x73731e73731e73,0x731e73731e7370,0x1e73b51eb1eb46,0xf3b82f52f546f3,0x782f62f646e378]) [(76,16)]
def stateEntry141 : Entry := row 5 [0xeaea,0xaaaaaaaa,0xc0c0c0c0,0xcc00cc00,0xf000f000] 4 (packWords [0x1e71e747,0x13711eb1eb4712,0xf12f61ee1ee2f6,0x2e73ad3a12e71e,0xd1ed4702f12f61,0xee1ee2f62e736b,0x3612e72e01ee1e,0xe36a36b2e72e12,0xe11ee2e71ee2e6]) []
def stateEntry142 : Entry := row 5 [0x88888888,0xa0a0a0a0,0xc0c0c0c0,0xff00ff00,0xff88ff88,0xffff0000] 5 (packWords [0x2e78022e7801,0x1e72e736b1e72e,0x736b2e736b2e73,0x6b2e736b2e7368,0x2e73ad3b500000,0x4743d83d84,0x1e4733b83b8421,0x4720000000001e,0x73731e73731e73,0x731e73731e7378,0x8001eb1eb43,0xe3b81ed1ed43e3,0x781ee1ee458378]) [(77,15),(140,1),(141,9)]
def stateEntry143 : Entry := row 5 [0x8888,0x88888888,0xa0a0a0a0,0xc0c0c0c0,0xff00ff00,0xffff0000] 5 (packWords [0x1e73733731e7,0x3c83ad3ce3ad3a,0x83a83ad3ce3680,0x3783ad000000,0x2e70001e73731e,0x73731e73731e73,0x731e73701e73b5,0x1e73731e73731e,0xb1eb4453b82f52,0xf54453784523d8,0x4493d82f62f645,0xb3784763b84503,0xb8475000000000]) []
def stateEntry144 : Entry := row 5 [0x88808880,0xaaaa0000,0xcccc0000,0xf000f000] 3 (packWords [0x3c,0x1e73b31e73a01,0xe73ac1e71e01e0,0x1e72f32e72e780,0x3ac1ec2f12f31,0xec1ec2f22f31ec]) [(68,0)]
def stateEntry145 : Entry := row 5 [0x88888888,0xa0a0a0a0,0xc0c0c0c0,0xff000000,0xffffff00] 4 (packWords [0x36300000,0x1e73d81e78,0x21e73b81e7801,0x1e73781e78003c,0x836b3ce36b3a83,0x6b3ad36b368368,0x36b3ad1eb1eb47,0x83b81ed1ed4783,0x781ee1ee477378]) [(144,53),(144,54),(144,47)]
def stateEntry146 : Entry := row 5 [0x88888888,0xa0a0a0a0,0xc0c0c0c0,0xff000000,0xff00ff00,0xffff0000] 5 (packWords [0x1e72e780c000,0x36b0000000002e,0x73d82e780b2e73,0xb82e780a2e7378,0x2e780937300000,0x1e73d81e78,0x81e73b81e7807,0x1e73781e780680,0x53d83d88048033,0xb83b8802801378,0x3788001eb1eb40,0x33b81ed1ed4033,0x781ee1ee430378]) [(15,53),(94,55),(15,54),(94,56),(15,47),(94,2),(37,15),(37,57),(37,58),(37,16),(37,49),(37,51),(145,0)]
def stateEntry147 : Entry := row 5 [0x88808880,0xaaaa0000,0xcccc0000,0xf0f0f0f0,0xff00ff00] 4 (packWords [0x1e71eb1e,0x78003c41e73cc1,0xe73a41e73ac1e7,0x1e41e41e73b53c,0x81eb3cc1eb3a81,0xeb3ac1eb1e81e8,0x1eb3b92e72e741,0xa3ac1ec2f54071,0xec1ec2f64071ec]) [(144,0)]
def stateEntry148 : Entry := row 5 [0xeeeeee,0xaaaaaaaa,0xcccccccc,0xf000f000,0xf0f00000] 4 (packWords [0x1e32e347,0xa1e31ed2e12e31,0xed1ee2e22e31ee,0x2e34702e33631e,0x11e11e32f51e21,0xe21e32f61e3479,0x1e33631ed1ee1e,0xd3bc1ed3631ed3,0x611ee3631ee362]) []
def stateEntry149 : Entry := row 5 [0x88888888,0xa0a0a0a0,0xc0c0c0c0,0xff00ff00,0xffff0000,0xffffff00] 5 (packWords [0x2e7000000000,0x1e700000000080,0x63d83d88058043,0xb83b8803802378,0x37880136b37300,0x8003c836b3ce3,0x6b3a836b3ad36b,0x36836836b3ad3d,0x3733d63733b03,0x733b5373370370,0x3733b51eb1eb47,0xc3b81ed1ed47c3,0x781ee1ee47b378]) [(145,0),(147,53),(148,55),(147,54),(148,56),(147,47),(148,2)]
def stateEntry150 : Entry := row 5 [0x88888888,0xa0a0a0a0,0xc0c0ffc0,0xff00ff00,0xffff0000] 4 (packWords [0x1e72e737,0x31e72e73d82e73,0x6b1eb3b82e71eb,0x1ed3782e71ed1e,0x73731e73731e71,0xeb1e73731e71ed,0x1e73b52f31eb1e,0xb3b82f51ed1ed3,0x781e81e81eb378]) []
def stateEntry151 : Entry := row 5 [0x80808888,0xaa00aa00,0xcc00cc00,0xf0f0f0f0,0xffff0000] 4 (packWords [0x1eb2e32e,0x71eb3692e73792,0xe736a2e737a2e7,0x2e42e42e736b1e,0xb3b91eb3791eb3,0xb01eb37a1eb2f0,0x1eb3b91e71e737,0x93b41ed1ed4192,0xf41ee1ee4192f4]) []
def stateEntry152 : Entry := row 5 [0xaaaa,0xaaaaaaaa,0xc0c0c0c0,0xcc00cc00,0xf000f000,0xffff0000] 5 (packWords [0x3ce3b13b1808,0x3ce3713718073c,0xe2f12f18062e60,0x2f63ce000000,0x2e70001e71e745,0xb3711eb1eb45b2,0xf12f63b03b12f6,0x8053b18043b11e,0xd1ed47d2f12f63,0x703712f6803371,0x8023712f02f02f,0x137a8012f18002,0xf11ee000000000]) [(150,35),(151,47),(150,59),(151,60),(150,61),(151,62),(38,0),(38,17),(38,63)]
def stateEntry153 : Entry := row 5 [0x88888888,0xa0a0a0a0,0xc0c0c0c0,0xff00ff00,0xffff0000] 6 (packWords [0x8273,0x6b1e71e78262e7,0x3732e782536b37,0x336b8242e71e71,0xe78232e78222e7,0x82136b3d836b82,0x2e73d82e781f3,0x6b81e36b81d2e7,0x81c2e781b36b3b,0x836b81a2e73b82,0xe781936b81836b,0x8172e78162e781,0x53ad3783688142,0xe73782e78133ad,0x8123ad8111e781,0x1e780f3733d83,0x7380e1e73d81e7,0x80d37380c37380,0xb1e780a1e78093,0x733b83738081e7,0x3b81e780737380,0x63738051e78041,0xe78033b5378370,0x8021e73781e780,0x13b58003b541e4,0x23b81eb4213d8,0x4001eb41e40241,0xe40241e3d83b83,0xb841e4023781ed,0x4223d843b1ed41,0xe40241e40241e3,0xd8378378421400,0x3781ee4223b843,0xb1ee4214004214,0x41e3b8378378]) [(39,15),(78,15),(142,0),(143,1),(121,42),(137,42),(39,57),(78,57),(142,8),(143,39),(121,64),(137,64),(39,58),(78,58),(142,43),(143,33),(121,65),(137,65),(39,16),(78,16),(142,1),(143,0),(121,44),(137,44),(39,49),(78,49),(142,39),(143,8),(121,66),(137,66),(39,51),(78,51),(142,33),(143,43),(121,67),(137,67),(146,0),(149,0),(152,9),(152,10)]
def stateEntry154 : Entry := row 5 [0x88808880,0xeac00000,0xf000f000] 2 (packWords [0x2e71e73a,0xc1e71e01e01e72,0xf61ec2e02e71ec]) []
def stateEntry155 : Entry := row 5 [0x88808880,0xeac0eac0,0xf000f000,0xffff0000] 3 (packWords [0x1e,0x72e73ad1e72e73,0xac2e78011ed2e6,0x2e71ed1e73b01e,0x78001e61e61e72,0xf61ec000000000]) [(65,0),(154,0)]
def stateEntry156 : Entry := row 5 [0x88808880,0xeac00000,0xf0f0f0f0,0xff00ff00] 3 (packWords [0x1e,0x71eb1e78002e71,0xe736b1e71e41e4,0x1e72f636b1eb2e,0x71eb1e81e81eb3,0x791ec2e42e71ec]) [(154,0)]
def stateEntry157 : Entry := row 5 [0x88808880,0xeac0eac0,0xf0f0f0f0,0xff00ff00,0xffff0000] 4 (packWords [0x1e72e736,0xb1e71eb36b2e71,0xeb2e73ac2e7801,0x1ed2e62e71ed1e,0x71eb1e78001e73,0xb41e741a1e61e6,0x1e72f61eb3b81e,0xb4181e91e91eb3,0x791ec000000000]) [(155,0),(156,0)]
def stateEntry158 : Entry := row 5 [0xaacc00,0x88888888,0xeeaacc00,0xf0f0f0f0] 3 (packWords [0x1e,0xb3a01eb3631ea1,0xea1eb3791eb3ae,0x1eb36b3601ee1e,0xe3a41e70000000,0x1ee36b1ee36a]) []
def stateEntry159 : Entry := row 5 [0xaacc00,0xaaaaaaaa,0xcccccccc,0xeeaacc00,0xf0f0f0f0] 4 (packWords [0x1eb3a11e,0xb3631eb1f11eb3,0x791ea1ea1eb37a,0x1eb3b51eb36b36,0x11f51f53a53621,0xee1ee3c61e7000,0x1f51ee1e,0xe8001f536b1f53,0x711ee36b1ee36a]) [(158,0)]
def stateEntry160 : Entry := row 5 [0x88888888,0xe0a0c000,0xff003300] 2 (packWords [0x1e33633a,0x81e31ee3603631,0xee1e01e01e3368]) []
def stateEntry161 : Entry := row 5 [0x88888888,0xeac0eac0,0xf030f030,0xffff0000] 3 (packWords [0x1e,0x72e73ad1e72e32,0xe32e78001ed2e6,0x2e71ed1e31e31e,0x72f31e61e61e72,0xf61e41e41ed3b4]) [(160,16)]
def stateEntry162 : Entry := row 5 [0x8888,0xa0a0a0a0,0xcccccccc,0xf8008800] 3 (packWords [0x1e,0x73601e72e51e31,0xe31e72e21e7362,0x1e72e72e01eb1e,0xb37c8000000000,0x1eb2e21eb2e2]) [(160,57)]
def stateEntry163 : Entry := row 5 [0x8888,0xa0a0a0a0,0xcccccccc,0xf8f88888,0xff00ff00] 4 (packWords [0x1e73621e,0x78011e73741e72,0xf51e31e31e72f3,0x1e736b1e72e72e,0x52e52f53ad2e21,0xeb1eb36a47e000,0x2f41eb1e,0xb37c8000000000,0x1eb2e71eb2e3]) [(161,39),(162,0)]
def stateEntry164 : Entry := row 5 [0x88888888,0xe0a0c000,0xff000000] 3 (packWords [0x3ae1e31e33,0x633b83633ae3b8,0x3ae3631e31e336,0x31ee1ee3ae3783,0x603633783633ae,0x1ee1ee1e33781e,0x3b81ee1e01e31,0xee1e33b8378378]) []
def stateEntry165 : Entry := row 5 [0x88888888,0xe0a0c000,0xf0f0f0f0,0xff000000] 3 (packWords [0x3a,0xe3633673631e73,0x633ae1e71ee360,0x3631ee1e300000,0x3781ee1ee3,0x781e41e41e7378]) []
def stateEntry166 : Entry := row 5 [0x88888888,0xe0a0c000,0xeeaacc00,0xff000000] 3 (packWords [0x36,0x336336b8011eb3,0x6b3ae1eb1ee36a,0x36b1ee1e300000,0x3781ee1ee8,0x1ea1ea1eb379]) [(154,68),(154,56)]
def stateEntry167 : Entry := row 5 [0xeac0,0x88888888,0xeac0eac0,0xf000f000] 3 (packWords [0x1e,0x73a01e72e31e61,0xe61e72f61e73ad,0x1e72e72e01ed1e,0xd3ac8000000000,0x1ed2e71ed2e6]) [(32,16)]
def stateEntry168 : Entry := row 5 [0x88888888,0xeac0eac0,0xf000f000,0xffff0000] 4 (packWords [0x3ad1e7,0x1e72e73b62e73a,0xd3b63ad2e71e71,0xe72e78082e3807,0x2f32e32e72f32e,0x78068058042e71,0xed1ed3ad2f62e6,0x2e72f62e73ad1e,0xd1ed1e72f31e38,0x33bc1e31e73bc,0x1e78022f32f31e,0x72f61e63b61ed1,0xe61e71ed1e73b6,0x2f62f62f38011e,0xc3bc1ed1ec2f31,0xed1ed3bc8003bc]) [(155,0),(158,62),(155,35),(158,16),(164,16),(165,16),(166,16),(167,0),(110,4)]
def stateEntry169 : Entry := row 5 [0x88888888,0xaaaaaaaa,0xe0a0c000,0xff000000] 3 (packWords [0x1e,0x33633b51e33633,0xae3633ce1f5361,0x3631f51e33b81e,0x33d81e11e11e33,0x791ee000000000]) []
def stateEntry170 : Entry := row 5 [0x88888888,0xaaaaaaaa,0xeac0eac0,0xf000f000,0xffff0000] 4 (packWords [0x1e72e73a,0xd1e72e32e32e78,0x2e73ae2e73cd,0x1ed2e92e71ed1e,0x31e31e72f31e73,0xb61e73d61e71e9,0x1e72f92f33bc2f,0x33dc2f11ed1ed3,0xdc1ee000000000]) [(169,16)]
def stateEntry171 : Entry := row 5 [0xaaaa,0xaaaaaaaa,0xc0c0c0c0,0xec00a000] 3 (packWords [0x1e,0x11e11e72f11e73,0x601e72e61e736d,0x1e72e71ed2e01e,0xd37a1ed2e71ed2,0xe1800000000000]) [(32,69)]
def stateEntry172 : Entry := row 5 [0xaaaa,0xaaaaaaaa,0xc0c0c0c0,0xececa0a0,0xff00ff00] 4 (packWords [0x1e73711e,0x78011e51e51e72,0xf31e73721e72f6,0x1e736d1e72e71e,0x91e91ed3792e62,0xe62f63ce4002e7,0x2e73691ed2f21e,0xd37a1ed2e71ed2,0xe5800000000000]) [(125,26),(171,0)]
def stateEntry173 : Entry := row 5 [0x88888888,0xe0a0c000,0xff00ff00,0xffff0000] 4 (packWords [0x36b804,0x36380337336336,0xb37336b8028018,0x3ae1eb1eb36b,0x2f32e33ae2f32f,0x336b1eb1eb36b1,0xee1ee3ae2f52f5,0x36b2f52f53ae1e,0xe1ee3b52f31e33,0x731eb1e33b51eb,0x1eb3732f32f337,0x32f52f53b51ee1,0xee3731ee1ee3b5,0x2f52f51eb3781e,0x83b81ee1e81eb1,0xee1eb3b8378378]) [(164,0),(169,37),(169,70),(171,9),(171,71)]
def stateEntry174 : Entry := row 5 [0x88888888,0xe0a0c000,0xf0f0f0f0,0xff00ff00,0xffff0000] 4 (packWords [0x36336336,0xb8003ae36b3ae3,0x6b2e72e73ae36b,0x1ee2f52f51ee3b,0x53733b53731e71,0xe73b53732f51ee,0x1ee2f51eb00000,0x3781ee1ee3,0x781ec1ec1ee378]) [(165,0)]
def stateEntry175 : Entry := row 5 [0x88888888,0xe0a0c000,0xee00cc00,0xffff0000] 3 (packWords [0x36,0x336336b8001eb2,0xe32f31eb1ee2f5,0x2f51ee1e31e31e,0xb2f32f51ee1ee2,0xf51ea1ea1eb379]) [(154,56)]
def stateEntry176 : Entry := row 5 [0x88888888,0xe0a0c000,0xeeaacc00,0xff00ff00,0xffff0000] 4 (packWords [0x36b37336,0xb80536b80436b8,0x31eb2f32f31eb,0x1ee2f52f51ee37,0x38023738012f31,0xeb1eb2f32f51ee,0x1ee2f53b800000,0x3781ee1ee8,0x1ea1ea1eb379]) [(156,68),(175,0),(162,11),(175,38),(162,29),(166,0)]
def stateEntry177 : Entry := row 5 [0xeac0,0x88888888,0xe0c0e0c0,0xff00ff00] 3 (packWords [0x1e,0x71eb1e72e31e61,0xe61e72f61e7363,0x1e72e71e91e91e,0xb3681eb2e31eb2,0xe31ed2e71ed2e6]) []
def stateEntry178 : Entry := row 5 [0xeac0,0x88888888,0xeac0eac0,0xf0f0f0f0,0xff00ff00] 4 (packWords [0x1e71eb1e,0x78031e73631e78,0x21e61e61e72f6,0x1e736b1e72e71e,0xb2e31eb8011e91,0xe91eb3791eb2e7,0x1eb36b2e41ed1e,0xd3ac8000000000,0x1ed2e71ed2e6]) [(33,16),(177,0),(177,72),(167,0)]
def stateEntry179 : Entry := row 5 [0x88888888,0xeac0eac0,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (packWords [0x36b1e71e72,0xe73b62e736b3b6,0x36b2e71e71e72e,0x71eb1eb36b3b93,0x6b2e73b92e736b,0x1eb1eb2e780d2e,0x780c3bc3ac2e73,0xbc2e780b80a809,0x2e71ed1ed3ad2f,0x62e62e72f62e73,0xad1ed1ed1e7808,0x1e78071eb1eb1e,0x71eb1e78068058,0x41e74021e7803,0x3bc3731e73bc1e,0x74824024021e72,0xf61e63b61ed1e6,0x1e71ed1e73b62f,0x62f61eb4811eb8,0x23bc2f31eb3bc,0x1eb4804364361e,0xb3791e93b91ed1,0xe91eb1ed1eb3b9,0x37937947f8011e,0xc3bc1ed1ec43e1,0xed1ed3bc8003bc]) [(157,0),(159,62),(163,73),(163,74),(168,0),(170,35),(170,75),(172,39),(172,76),(173,16),(174,16),(176,16),(178,0),(111,25)]
def stateEntry180 : Entry := row 5 [0x88888888,0xa0a0a0a0,0xcc00cc00,0xf8880000] 3 (packWords [0x1e,0x72e736b1e71eb2,0xe32e71eb2e52e5,0x2e73a51e31e31e,0x72f31e51e51e73,0xd31ea1ea1eb3b3]) []
def stateEntry181 : Entry := row 5 [0x88888888,0xa0a0a0a0,0xcc00cc00,0xf888f888,0xffff0000] 4 (packWords [0x2e73a52e,0x78001e72e736b1,0xe71eb2e32e71eb,0x2e72ed2e73a73d,0x1e71e73b53b01,0xeb1eb3da2f5000,0x1e31e31e,0x72f31e71ed1e73,0xd31eb1ee1eb3b3]) [(180,0)]
def stateEntry182 : Entry := row 5 [0x88888888,0xa0a0a0a0,0xcccccccc,0xf8008800,0xffff0000] 4 (packWords [0x1e72e736,0xb1e72e73dc2e78,0x11eb2e32e71eb,0x2e78002e73cb1e,0x73b51e73b51e31,0xe31e72f31e7372,0x1e73b53bc1eb1e,0xb3bc2f50000000,0x1eb2f21eb3bc]) [(162,0),(180,77)]
def stateEntry183 : Entry := row 5 [0x88888888,0xa0a0a0a0,0xcccccccc,0xf888f888,0xff00ff00,0xffff0000] 5 (packWords [0x1e72e736b1e7,0x2e73ca2e78022e,0x73ad2e73ad1eb2,0xe32e71eb2e736e,0x2e73ad1e73b51e,0x74831e73dc1e78,0x11e31e31e72f3,0x1e78001e73d33d,0x83d83da4023b81,0xeb1eb3da37a000,0x3bc1eb1e,0xb3bc1ed0000000,0x1eb1ee1eb3bc]) [(163,1),(181,0),(182,1)]
def stateEntry184 : Entry := row 5 [0x88888888,0xa0a0a0a0,0xcc00cc00,0xf000f000,0xffff0000] 5 (packWords [0x3ad8113a52,0xe73b52e73ad3b5,0x3ad2e78102e736,0xb80f3632e73732,0xe736b37336b2e7,0x80e2e72e780d2e,0x336b2f32e32e72,0xf32e736b80c36b,0x2e780b2e53ad2f,0x52e52e72f52e73,0xad80a3ad3da373,0x1e73b53dc1e73d,0xa3dc3da3b53733,0x733b52f31eb3da,0x3bc1eb3b53bc3b,0x53da2f32f38092,0xf52f53b58083b5,0x8078068053b52f,0x52f58042f32f33,0x73803373802801,0x8003732f32f337,0x32f51ed3dc37a1,0xed37337a3733dc,0x2f52f52f337a1e,0xe3bc2f51ee2f32,0xf52f33bc37a37a]) [(168,7),(181,78),(181,3),(126,79),(126,60),(168,8),(181,35),(181,0),(126,16),(126,62),(44,16),(116,37),(44,79),(116,34),(44,60),(116,26),(44,62),(116,10)]
def stateEntry185 : Entry := row 5 [0x88888888,0xa0a0a0a0,0xcc00cc00,0xf0f00000,0xff000000] 4 (packWords [0x2e736b3b,0x52e71e736336b1,0xe71eb36b3b51eb,0x2f536a36b2f51e,0x72e73da1e71eb2,0xe32e71eb2e52e5,0x2e737a1e31e31e,0x73bc1e51e51e72,0xf51ea1ea1eb37a]) []
def stateEntry186 : Entry := row 5 [0x88888888,0xa0a0a0a0,0xcc00cc00,0xf0f00000,0xff00ff00,0xffff0000] 5 (packWords [0x36b3b536b805,0x2e700000000036,0xb3dc36b8041eb3,0x6b3bc1eb36a2f5,0x2f58033b53da3b,0x58021e70000000,0x3b41eb1eb801,0x2f537a37a2f53d,0x83d83da8001eb2,0xf33bc1eb37a2f5,0x2f537a3bc1eb1e,0xb3bc1ed1ed37a2,0xf51ea1ea1eb37a]) [(15,47),(37,80),(44,62),(37,10),(44,36),(185,0)]
def stateEntry187 : Entry := row 5 [0x88888888,0xa0a0a0a0,0xcc00cc00,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x36b48636,0xb2e73b52e736b3,0xb536b2e78132e7,0x2e74842e736b3d,0xa36b2e73da2e73,0x6b81236b36b811,0x36b2e73dc2e736,0xb3dc36b2e78102,0xe72e780f2e736b,0x3bc36b2e73bc2e,0x736b80e36b2e78,0xd2e53ad2f52e5,0x2e72f52e73ad80,0xc3ad3b54843b54,0x843da3da3b53da,0x3b548448680b42,0x147f1e70000000,0x0,0x3b54863b,0x44863bc3b43b53,0xbc3b580a486809,0x8082f52f53b537,0xa37a48637a37a3,0xb52f52f53da484,0x3d84843dc3d83d,0xa3dc3da8074848,0x64854851eb000,0x0,0x8053,0x7a37a3da2f52f5,0x4842f52f53da37,0xa37a8043bc3bc3,0xdc8033dc802801,0x8003dc3bc3bc40,0x22f51ed3dc37a1,0xed40237a37a3dc,0x2f52f540037a1e,0xe3bc2f51ee4002,0xf52f53bc37a37a]) [(179,7),(183,29),(183,3),(127,79),(127,23),(135,24),(39,58),(79,61),(135,62),(39,80),(79,81),(184,0),(45,16),(122,37),(47,82),(117,66),(47,40),(117,26),(186,0),(186,72)]
def stateEntry188 : Entry := row 5 [0x88888888,0xa0a0a0a0,0xcccccccc,0xf0f0f0f0,0xff000000,0xff00ff00,0xffff0000] 6 (packWords [0x1e72e748600036,0xb0000000002e73,0xda2e780e2e73dc,0x2e780d2e73bc2e,0x780c2e737a2e78,0xb373000000000,0x1e73da1e780a1e,0x73dc1e78091e73,0xbc1e78081e737a,0x1e78074223da3d,0xa8064213dc3dc8,0x58043bc3bc803,0x80237a37a8013d,0x83d83da8001eb0,0x37a3da,0x46d37a3bc3dc43,0x3bc1ed0000000,0x1ee1ee43037a]) [(146,0),(16,31),(95,55),(16,20),(95,56),(47,40),(47,41),(45,17),(45,63),(186,72),(186,57),(45,27),(45,83),(186,84),(186,85)]
def stateEntry189 : Entry := row 5 [0x88888888,0xa0a0a0a0,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 7 (packWords [0x48636b,0x1e71e74872e737,0x32e748636b3733,0x6b8172e71e71e7,0x4222e74222e742,0x236b3da36b4222,0xe73da2e742236b,0x81636b4212e742,0x12e74213ad3dc3,0xad4212e73dc2e7,0x4213ad8153ad81,0x42e78132e74873,0x6b3bc36b4872e7,0x3bc2e781236b81,0x136b8102e780f2,0xe74873ad37a36a,0x4872e737a2e780,0xe3ad80d3ad4221,0xe74221e7422373,0x3da3734221e73d,0xa1e742237380c3,0x734211e74211e7,0x4213b53dc3b542,0x11e73dc1e74213,0xb580b3b580a1e7,0x8091e74863733b,0xc3734861e73bc1,0xe7808373807373,0x8061e78051e748,0x63b537a3724861,0xe737a1e78043b5,0x8033b54213da42,0x13d84214213dc3,0xd84213da3dc3da,0x42142142280240,0x24024021eb0000,0x0,0x0,0x42280137a3,0x7a4223da43b3da,0x42242243b43b42,0x13da37a37a4218,0x3bc3bc4213dc,0x4003dc42142140,0x4004213dc3bc3,0xbc4024024021ed,0x0,0x0,0x421400,0x37a1ee4223bc43,0xb1ee4214004214,0x4213bc37a37a]) [(136,40),(136,41),(153,0),(48,17),(80,15),(123,42),(138,42),(48,63),(80,81),(123,64),(138,64),(187,0),(187,3),(48,11),(80,16),(123,44),(138,44),(48,82),(80,79),(123,66),(138,66),(187,77),(187,49),(188,0)]
def stateEntry190 : Entry := row 5 [0xaaaa,0x88888888,0xe0c0a000,0xff00ff00] 3 (packWords [0x1e,0x31e31eb2f32f61,0xed1ed2f680036b,0x3633631e91e91e,0xb3681eb2f31eb2,0xe31ed2f61ed2f6]) [(160,7)]
def stateEntry191 : Entry := row 5 [0x88888888,0xaaaaaaaa,0xe0a0c000,0xff00ff00,0xffff0000] 4 (packWords [0x36336336,0xb8011eb2e32f31,0xeb36b3ae36b3ce,0x3692f52f53ce1e,0x31e31eb2f33738,0x3733d52f5371,0x3732f51eb3b81e,0xb3d81e91e91eb3,0x791ee000000000]) [(190,1),(169,0)]
def stateEntry192 : Entry := row 5 [0x8888aaaa,0xe0a0c000,0xff00ff00,0xffff0000] 3 (packWords [0x36,0x13613698001e92,0xe12f31e91ee2f5,0x2f51ee1e11e11e,0x92f32f51ee1ee2,0xf51e81e81e9378]) [(160,70)]
def stateEntry193 : Entry := row 5 [0xaaaa,0xaaaaaaaa,0xc8c08800,0xf0f0f0f0,0xff00ff00] 4 (packWords [0x3b11eb1e,0xb8031e51e51ed2,0xf52f63a43ac2f6,0x80236b36b3a51e,0x91e91eb3791eb2,0xf61eb8011eb3ad,0x1eb36b1ed2e41e,0xd3ac1ed2f51ed2,0xe5800000000000]) [(33,27),(190,3),(192,86),(171,81)]
def stateEntry194 : Entry := row 5 [0xa888a000,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (packWords [0x3ad8133ad8,0x123733733ad373,0x37381181080f3a,0xd80e3ad80d2f32,0xf33ad2f32f380c,0x80b80a3ce1ed1e,0xd3ad3dc3ad3ce3,0xdc3ce3ad1ed1ed,0x3ad1ee1ee3ce2f,0x62e63ad2f62f63,0xce1ee1ee3d62f3,0x2f33733da3733d,0x63da3d63732f32,0xf3373809373808,0x1ed1ed3731ed1e,0xd8078068053732,0xf61e63d61ee1e6,0x3731ee1ee3d62f,0x62f62f38042f38,0x31ed1ed2f31ed,0x1ed8028018002f,0x337a1ea3da1ee1,0xea2f31ee1ee3da,0x37a37a1ed3bc1e,0xc3dc1ee1ec1ed1,0xee1ed3dc3bc3bc]) [(173,28),(191,33),(191,28),(193,87),(193,54),(173,29),(191,76),(191,29),(193,38),(193,88),(173,30),(191,30),(191,13),(193,8),(193,67),(173,4),(191,4),(191,14),(193,9),(193,26)]
def stateEntry195 : Entry := row 5 [0xa888a000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (packWords [0x3ad373373803,0x3ad2f32f38021e,0xd3ad3ce1ed3ad3,0xce3ad3ce2e72e7,0x3ad3ce2f33733d,0x62f33731ed1ed8,0x13733d63733d6,0x1e71e73733d62f,0x31ed1ed8002f33,0xda2f33da1eb1eb,0x2f33da1ed3dc1e,0xd3dc1ed2f51ed3,0xdc1ee000000000]) [(174,28),(174,29),(174,30),(174,4)]
def stateEntry196 : Entry := row 5 [0xa888a000,0xccccc000,0xf0f0f0f0,0xff00ff00,0xffff0000] 4 (packWords [0x3ad37337,0x38033ad2f32f38,0x21ed3ad3ce1ed,0x1ee2f62f61ee2f,0x33733d62f33731,0xed1ed8012f61ee,0x1ee2f62f31ed1e,0xd8002f21ee1ee3,0x7a1ec1ec1ed3bc]) [(156,47),(156,60),(175,13),(175,14)]
def stateEntry197 : Entry := row 5 [0x8888,0xaaaaaaaa,0xcccccccc,0xf0808080,0xff00ff00] 4 (packWords [0x1e31e31e,0x72f31e73611e78,0x31e73621e7802,0x1e736b1e72e71e,0xb2e11eb3691eb2,0xe21eb36a1eb2e7,0x1eb2e336836836,0x93bc8010000000,0x800000000000]) [(192,89),(192,90),(162,15),(162,72)]
def stateEntry198 : Entry := row 5 [0xa888a000,0xcccccccc,0xf0f0f0f0,0xfcccf000,0xff00ff00,0xffff0000] 5 (packWords [0x3ad37337380b,0x3ad80a3ad8093a,0xd2f32f38081ed3,0xad3ce1ed1ee2f6,0x2f61ee37380737,0x38062f33733d62,0xf33731ed1ed805,0x2f61ee1ee2f680,0x42f32f38038021,0xed1ed801402000,0x2f31ed1e,0xd8002f21ee1ee3,0x7a1ec1ec1ed3bc]) [(176,28),(196,0),(197,91),(196,79),(197,50),(176,29),(196,22),(197,71),(176,30),(196,20),(197,92),(176,4)]
def stateEntry199 : Entry := row 5 [0xeac0,0xaa80aa80,0xcccccccc,0xf0f0f0f0,0xff00ff00] 4 (packWords [0x1e71eb1e,0x78011e71ed1e78,0x1e61e61e72f6,0x1e736b1e72e71e,0x91e91eb3791eb1,0xee1eb36a1eb2e7,0x1eb36b1ed1ee1e,0xd3ac1ed2e71ed3,0x691ee2e71ee2e6]) [(177,29),(177,75)]
def stateEntry200 : Entry := row 5 [0xeac0,0xaaaaaaaa,0xcccccccc,0xeac0eac0,0xf0f0f0f0,0xff00ff00] 5 (packWords [0x1e71eb1e7808,0x1e73631e78071e,0x71ed1e78061e61,0xe61e72f61e736b,0x1e72e71eb2e31e,0xb8051e91e91eb3,0x791eb1ee1eb804,0x1eb2e71eb36b2e,0x51ed1ed80336a1,0xee1ee802801000,0x1ed1ee1e,0xd8001ed2e71ed3,0x691ee2e71ee2e6]) [(178,0),(40,10),(199,0),(199,29),(178,3),(199,75),(178,78),(199,35),(178,35)]
def stateEntry201 : Entry := row 5 [0xaaaaaaaa,0xcccccccc,0xeac0eac0,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x36b1e71e,0x72e73d62e736b3,0xd636b2e71e71e7,0x2e71eb1eb36b3b,0x936b2e73b92e73,0x6b1eb1eb2e7808,0x2e78074074072e,0x74072e78068058,0x42e71ed1ed3ad,0x3793692e73792e,0x73ad1ed1ed2e71,0xee1ee3ce2f62e6,0x2e72f62e73ce1e,0xe1ee1e74891e74,0x891eb1eb1e71eb,0x1e74894888031e,0x74021e748840f3,0x731e74821e7482,0x4024021e74801e,0x74801ed1ed1e71,0xed1e7480488802,0x1e72f61e63d61e,0xe1e61e71ee1e73,0xd62f62f61eb481,0x1eb48948c2f31e,0xb48b1eb4804364,0x361eb3791e93b9,0x1ed1e91eb1ed1e,0xb3b93793791eb4,0x821eb4821ee1ee,0x1eb1ee1eb48248,0x980147f4802f54,0x8a1ed1ed43e1ed,0x1ed41a48941a40,0x248237a4821ee1,0xee4021ee1ee482,0x4884181ed4821e,0xd4821ee1ee1ed1,0xee1ed482480800]) [(179,0),(179,3),(179,78),(179,35),(194,10),(195,10),(198,10),(200,0),(112,5)]
def stateEntry202 : Entry := row 5 [0x88888888,0xe0808080,0xff00ff00,0xffff0000] 3 (packWords [0x1e,0x72e736b1e71eb2,0xe32e71eb2e7368,0x2e78011e31e31e,0x72f31e73701e78,0x1e81e81eb378]) [(81,15),(81,16)]
def stateEntry203 : Entry := row 5 [0x88888888,0xe0e0e0e0,0xf8008800,0xffff0000] 3 (packWords [0x1e,0x72e736b1e71eb2,0xe32e71eb2e52e5,0x2e78001e31e31e,0x72f31e51e51e72,0xf51eb2f01eb37c]) [(83,27)]
def stateEntry204 : Entry := row 5 [0x88888888,0xeeeeeeee,0xf0808080,0xff00ff00,0xffff0000] 4 (packWords [0x1e72e736,0xb1e71eb2e32e71,0xeb2e73bc2e7804,0x2e73692e78031e,0x31e31e72f31e73,0xbc1e78021e7371,0x1e78011eb3b81e,0xb8001e91e91eb3,0x79378000000000]) [(202,0),(85,9),(203,15),(85,10),(203,16)]
def stateEntry205 : Entry := row 5 [0x88888888,0xaaaaaaaa,0xcccccccc,0xf0808080,0xff00ff00,0xffff0000] 5 (packWords [0x1e72e736b1e7,0x1eb2e32e71eb2e,0x73dc2e78082e73,0xbc2e78072e7806,0x2e78051e31e31e,0x72f31e73dc1e78,0x41e73bc1e7803,0x1e78021e78011e,0xb3b91eb3b91eb3,0xb81eb3da1eb3b9,0x1eb3b93bc3dc80,0x3790000000,0x37a000000000]) [(204,0),(88,15),(197,1),(182,15),(182,72),(88,16),(197,0),(182,16),(182,77)]
def stateEntry206 : Entry := row 5 [0x88888888,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xf888f888,0xff00ff00,0xffff0000] 6 (packWords [0x1e72e736b1e72e,0x74252e78061eb2,0xe32e71eb2e73ad,0x2e73ad2e73ac2e,0x73ce2e73ad2e73,0xad1e73b51e7483,0x1e31e31e72f31e,0x73dc1e78051e73,0xbc1e78041e7490,0x1e78033b91eb1e,0xb43648f3dc3dc4,0x24023bc3bc400,0x48f0000000001e,0xb3dc1eb8021eb3,0xbc1eb8011eb48e,0x1eb8003bc3dc48,0xd0001ed0000000,0x1ee000000000]) [(89,0),(183,0),(183,7),(89,15),(183,15),(183,72),(205,16)]
def stateEntry207 : Entry := row 5 [0x888888,0x88888888,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (packWords [0x1e72e73ad1e71e,0xb2e32e71eb2e73,0xad2e73ad2e73ac,0x2e73ce2e73ad2e,0x73ad2e73ad2e73,0x6b1e31e31e72f3,0x1e73b51e73b51e,0x73b41e73d61e73,0xb51e73b51e73b5,0x1e73731eb3b91e,0xb3b91eb3b81eb3,0xda1eb3b91eb3b9,0x1eb3b91eb3b93b,0xc3dc43c0003790,0x431000,0x37a00000,0x4570000000,0x431000000000]) []
def stateEntry208 : Entry := row 5 [0x88888888,0xaaaaaaaa,0xcccccccc,0xf000f000,0xf0f0f0f0,0xff00ff00,0xffff0000] 7 (packWords [0x36b42c3632e737,0x32e736b37336b2,0xe781f2e72e7422,0x2e336b2f32e32e,0x72f32e736b81e3,0x6b3ad81d3ad2e7,0x4252e73ad4253a,0xd2e781c2e72e74,0x912e73ad3dc3ad,0x2e73dc2e73ad81,0xb3ad2e74282e73,0xce3bc3ac2e73bc,0x2e73ce81a3ce2e,0x78192e73ad4933,0xad2e74932e73ad,0x8183ad4222f32f,0x337342c3734224,0x22422000000000,0x42248c1e700000,0x0,0x373491,0x3734913dc3dc37,0x33dc37349142c8,0x17373428373428,0x3bc3bc3733bc37,0x342842c8163734,0x2c37342c419419,0x37341937381542,0xc81442c4921eb0,0x0,0x2f,0x34912f34913dc3,0xdc2f33dc2f3491,0x4228132f34282f,0x34283bc3bc2f33,0xbc2f3428422812,0x2f34222f342243,0xb43b2f343b2f38,0x11422810400491,0x4004913dc3dc40,0x3dc3dc49180f8,0xe402428402428,0x3bc3bc4023bc3b,0xc42880d80c80b8,0xa809808807806,0x80580480380280,0x18004283bc3bc3,0xdc4913dc428428,0x42800000000042,0x84281ed0000000,0x0,0x4914281e,0xe0000000000000,0x0]) [(17,0),(62,92),(62,0),(201,8),(206,92),(206,0),(96,16),(128,16),(207,16),(96,42),(207,42),(128,42),(48,63),(90,92),(48,61),(90,35),(48,8),(90,0),(187,3),(187,28),(48,9),(90,15),(187,80),(187,78),(53,10),(118,55),(188,11),(188,12),(53,55),(118,10),(188,41),(188,70)]
def stateEntry209 : Entry := row 5 [0x88888888,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 8 (packWords [0x42c36b,0x1e71e74252e737,0x32e742c36b3733,0x6b8142e71e71e7,0x4222e71eb1eb42,0x536b2f32e34222,0xe72f32e781336b,0x1eb1eb4002e740,0x2e74003ad3dc3,0xad4002e73dc2e7,0x4003ad8123ad40,0x22e74022e74023,0xce3bc3ac4022e7,0x3bc2e74023ce81,0x13ce8102e780f2,0xe74253ad4073ad,0x4252e74072e780,0xe3ad80d3ad4221,0xe72f31e342c373,0x1eb1e34221e71e,0xb1e780c3732f32,0xf34001e74001e7,0x4003b53dc3b540,0x1e73dc1e74003,0xb580b3b54021e7,0x4021e74023d63b,0xc3b44021e73bc1,0xe74023d680a3d6,0x8091e78081e742,0xc3b54193b542c1,0xe74191e78073b5,0x8063b54001eb40,0x1eb4003b93dc3,0xb94001eb3dc1eb,0x4003b98053b940,0x21eb4021eb4023,0xda3bc3b84021eb,0x3bc1eb4023da80,0x43da8031eb8021,0xeb4223b943b3b9,0x4221eb43b1eb80,0x13b98003b94024,0x23bc3bc4023dc,0x4003dc40240240,0x24020000000000,0x4024024021ed,0x0,0x0,0x402400,0x4021ee00000000,0x0,0x0]) [(54,0),(91,0),(124,41),(139,41),(189,0),(189,7),(54,9),(91,15),(124,70),(139,70),(189,17),(189,29),(208,0),(54,10),(91,16),(124,55),(139,55),(189,11),(189,12),(208,93),(208,2)]
def stateEntry210 : Entry := row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 9 (packWords [0x4193,0x6b1e71e74072e7,0x3732e741936b37,0x336b8092e71e71,0xe743b2e71eb1eb,0x40736b2f32e343,0xb2e72f32e78083,0x6b1eb1eb4002e7,0x1ed1ed4073ad2f,0x52e54002e72f52,0xe78073ad1ed1ed,0x4022e71ee1ee40,0x73ce2f62e64022,0xe72f62e78063ce,0x1ee1ee43b1e72f,0x31e34193731eb1,0xe343b1e71eb1e7,0x8053732f32f340,0x1e72f51e54193,0xb51ed1e54001e7,0x1ed1e78043b52f,0x52f54021e72f61,0xe64193d61ee1e6,0x4021e71ee1e780,0x33d62f62f64001,0xeb3791e943b3b9,0x1ed1e94001eb1e,0xd1eb8023b93793,0x794021eb37a1ea,0x43b3da1ee1ea40,0x21eb1ee1eb8013,0xda37a37a4021ed,0x3bc1ec4003dc1e,0xe1ec4021ed1ee1,0xed8003dc3bc3bc]) [(209,0),(209,8),(209,43),(209,9),(209,21),(209,92),(209,10),(209,71),(209,93),(209,2)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def ds : Array Entry := #[stateEntry0,stateEntry1,stateEntry2,stateEntry3,stateEntry4,stateEntry5,stateEntry6,stateEntry7,stateEntry8,stateEntry9,stateEntry10,stateEntry11,stateEntry12,stateEntry13,stateEntry14,stateEntry15,stateEntry16,stateEntry17,stateEntry18,stateEntry19,stateEntry20,stateEntry21,stateEntry22,stateEntry23,stateEntry24,stateEntry25,stateEntry26,stateEntry27,stateEntry28,stateEntry29,stateEntry30,stateEntry31,stateEntry32,stateEntry33,stateEntry34,stateEntry35,stateEntry36,stateEntry37,stateEntry38,stateEntry39,stateEntry40,stateEntry41,stateEntry42,stateEntry43,stateEntry44,stateEntry45,stateEntry46,stateEntry47,stateEntry48,stateEntry49,stateEntry50,stateEntry51,stateEntry52,stateEntry53,stateEntry54,stateEntry55,stateEntry56,stateEntry57,stateEntry58,stateEntry59,stateEntry60,stateEntry61,stateEntry62,stateEntry63,stateEntry64,stateEntry65,stateEntry66,stateEntry67,stateEntry68,stateEntry69,stateEntry70,stateEntry71,stateEntry72,stateEntry73,stateEntry74,stateEntry75,stateEntry76,stateEntry77,stateEntry78,stateEntry79,stateEntry80,stateEntry81,stateEntry82,stateEntry83,stateEntry84,stateEntry85,stateEntry86,stateEntry87,stateEntry88,stateEntry89,stateEntry90,stateEntry91,stateEntry92,stateEntry93,stateEntry94,stateEntry95,stateEntry96,stateEntry97,stateEntry98,stateEntry99,stateEntry100,stateEntry101,stateEntry102,stateEntry103,stateEntry104,stateEntry105,stateEntry106,stateEntry107,stateEntry108,stateEntry109,stateEntry110,stateEntry111,stateEntry112,stateEntry113,stateEntry114,stateEntry115,stateEntry116,stateEntry117,stateEntry118,stateEntry119,stateEntry120,stateEntry121,stateEntry122,stateEntry123,stateEntry124,stateEntry125,stateEntry126,stateEntry127,stateEntry128,stateEntry129,stateEntry130,stateEntry131,stateEntry132,stateEntry133,stateEntry134,stateEntry135,stateEntry136,stateEntry137,stateEntry138,stateEntry139,stateEntry140,stateEntry141,stateEntry142,stateEntry143,stateEntry144,stateEntry145,stateEntry146,stateEntry147,stateEntry148,stateEntry149,stateEntry150,stateEntry151,stateEntry152,stateEntry153,stateEntry154,stateEntry155,stateEntry156,stateEntry157,stateEntry158,stateEntry159,stateEntry160,stateEntry161,stateEntry162,stateEntry163,stateEntry164,stateEntry165,stateEntry166,stateEntry167,stateEntry168,stateEntry169,stateEntry170,stateEntry171,stateEntry172,stateEntry173,stateEntry174,stateEntry175,stateEntry176,stateEntry177,stateEntry178,stateEntry179,stateEntry180,stateEntry181,stateEntry182,stateEntry183,stateEntry184,stateEntry185,stateEntry186,stateEntry187,stateEntry188,stateEntry189,stateEntry190,stateEntry191,stateEntry192,stateEntry193,stateEntry194,stateEntry195,stateEntry196,stateEntry197,stateEntry198,stateEntry199,stateEntry200,stateEntry201,stateEntry202,stateEntry203,stateEntry204,stateEntry205,stateEntry206,stateEntry207,stateEntry208,stateEntry209,stateEntry210]
def states (i : Nat) := ds[i]?.getD default
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def ms : Array (List (Fin 4)) := #[[],[3],[0,1,2,3,0,1,2],[1],[0,1,2,3,0,1,2,1],[0,1,2,3,0,1,0],[3,1],[0],[0,1],[0,1,2],[0,1,2,3],[1,2,3],[1,2,3,0],[1,2,3,0,1],[1,2,3,0,1,2],[2],[2,3],[1,2],[2,3,2,1],[1,2,3,1,2,1,0],[1,2,3,1,2,1],[0,1,2,0],[2,3,1,2],[2,3,1,2,0],[2,3,1,2,0,1],[0,1,2,3,1,0],[0,1,2,3,1],[0,1,2,3,2],[1,0],[1,2,0],[0,1,2,3,2,0,1],[1,2,3,1,2],[0,1,2,3,1,2,0,1,0],[3,0,1,0],[0,1,2,3,0,1,2,1,0],[0,1,2,0,1,0],[0,1,2,3,1,2,1,0],[0,1,2,3,0,1,2,0,1,0],[3,0],[3,0,1],[1,2,3,1,2,0],[1,2,3,1,2,0,1],[2,3,0,1,2,0,1],[0,1,0],[0,1,2,3,1,2,0,1],[1,2,3,0,1,2,0,1,0],[2,3,1,2,0,1,0],[2,3,2,0,1,0],[1,2,3,1,2,0,1,0],[2,3,0,1],[0,1,2,3,2,0],[2,3,0,1,0],[2,3,1,2,1,0],[2,3,2],[2,3,2,0,1],[0,1,2,3,0,1,2,0,1],[0,1,2,3,0,1,2,0],[2,0,1],[2,0,1,0],[1,2,0,1,0],[2,3,0,1,2,1,0],[1,2,1,0],[2,3,0,1,2,0,1,0],[1,2,1],[2,3,0,1,2,0],[2,3,0,1,2],[0,1,2,3,1,2,0],[0,1,2,3,1,2],[2,3,2,0],[0,1,2,3,1,2,1],[1,2,3,0,1,2,0,1],[0,1,2,3,0],[2,0],[3,1,2],[3,1,0],[1,2,0,1],[3,0,1,2,0],[2,3,0],[0,1,2,1,0],[2,3,1],[0,1,2,1],[2,1],[1,2,3,1],[0,1,2,3,2,1],[1,2,3,2,0],[1,2,3,2,0,1],[1,2,3,0,1,2,1,0],[3,2,0],[2,3,0,1,2,1],[1,2,3,2,1],[1,2,3,2,1,0],[3,0,1,2,0,1],[0,1,2,0,1],[0,1,2,3,0,1]]
def perm (i : Nat) := permitted (ms[i]?.getD [])
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
def specTab : Array Spec := #[(3,[]),(1,[(0,2,3),(1,0,4)]),(1,[]),(1,[(0,2,3)]),(7,[(0,0,3),(2,0,3)]),(7,[(2,0,3),(3,0,3)]),(9,[(0,0,3),(2,0,3)]),(9,[]),(1,[(0,0,1),(0,2,4)]),(1,[(0,1,2),(2,0,4)]),(1,[(0,0,2),(2,1,4)]),(1,[(0,0,1),(2,2,4)]),(3,[(0,0,1),(0,2,4)]),(5,[(0,0,1),(0,2,4)]),(7,[(0,0,1),(0,2,4)]),(1,[(0,0,1),(3,2,4)]),(9,[(0,0,1),(0,2,4)]),(1,[(0,1,2),(0,3,4)]),(1,[(0,2,3),(2,1,4)]),(5,[(0,2,3),(2,0,4)]),(1,[(0,1,3),(2,2,4)]),(7,[(0,2,3),(2,0,4)]),(1,[(0,1,2),(2,3,4)]),(9,[(0,2,3),(2,0,4)]),(3,[(1,1,2),(0,0,4)]),(7,[]),(1,[(1,1,2),(0,0,4)]),(1,[(3,0,1),(0,0,2)]),(1,[(2,0,1)]),(1,[(3,0,1)]),(1,[(0,0,1)]),(3,[(0,0,1),(0,0,2)]),(5,[(0,0,1),(0,0,2)]),(3,[(0,0,1)]),(5,[(0,0,1)]),(9,[(2,0,3),(3,0,3)]),(3,[(0,1,2),(2,0,4)]),(9,[(0,0,1)]),(5,[(0,0,2),(3,3,4)]),(1,[(0,1,2),(3,3,4)]),(1,[(0,1,2)]),(7,[(0,0,2),(3,3,4)]),(5,[(0,0,1),(1,0,1)]),(7,[(0,0,1),(1,0,1)]),(7,[(0,0,1)]),(1,[(2,0,1),(0,2,4)]),(1,[(0,0,1),(0,0,2)]),(1,[(3,0,2),(0,3,4)]),(3,[(0,2,3)]),(1,[(0,0,2),(0,3,4)]),(7,[(2,0,3),(0,1,3)]),(1,[(0,0,1),(1,0,1)]),(3,[(2,0,1),(0,2,4)]),(1,[(2,0,1),(0,1,2)]),(1,[(1,0,2),(0,1,4)]),(5,[(0,0,1),(2,2,4)]),(3,[(2,0,1),(0,1,2)]),(1,[(0,0,1),(0,1,2)]),(3,[(2,0,1)]),(5,[]),(1,[(0,2,3),(2,0,4)]),(1,[(0,0,2),(3,3,4)]),(1,[(1,0,2)]),(1,[(2,0,2)]),(1,[(2,0,3),(2,2,4)]),(7,[(0,0,1),(3,3,4)]),(3,[(0,2,3),(2,0,4)]),(1,[(2,0,2),(0,3,4)]),(1,[(1,0,3)]),(1,[(2,0,3)]),(1,[(2,0,2),(2,3,4)]),(9,[(0,0,1),(3,3,4)]),(1,[(0,0,1),(2,3,4)]),(1,[(3,1,3),(2,0,4)]),(1,[(3,0,3)]),(1,[(2,0,1),(0,3,4)]),(1,[(3,0,3),(2,1,4)]),(1,[(3,1,3)]),(1,[(1,1,3)]),(1,[(3,0,1),(0,3,4)]),(3,[(3,1,3),(2,0,4)]),(5,[(3,1,3),(2,0,4)]),(1,[(0,0,1),(0,3,4)]),(1,[(1,0,1),(3,2,4)]),(1,[(1,0,1),(3,3,4)]),(7,[(2,0,3)]),(9,[(2,0,3)]),(3,[(0,0,2),(0,3,4)]),(3,[(1,0,2)]),(3,[(2,0,2)]),(3,[(1,0,3)]),(3,[(2,0,3)]),(1,[(0,0,2),(0,2,3)]),(1,[(2,0,2),(0,2,3)]),(1,[(0,0,2),(3,2,3)]),(9,[(2,0,3),(0,1,3)]),(1,[(2,2,3)]),(1,[(3,2,3)]),(1,[(2,0,3),(0,2,3)]),(3,[(2,0,1),(3,3,4)]),(3,[(3,0,1)]),(1,[(0,0,1),(1,3,4)]),(1,[(0,0,1),(3,0,3)]),(5,[(3,0,1)]),(1,[(0,0,1),(3,1,3)]),(7,[(2,0,3),(2,1,3)]),(1,[(0,2,3),(2,2,3)]),(3,[(2,0,2),(0,2,3)]),(3,[(2,0,3),(0,2,3)]),(5,[(0,2,3)]),(3,[(1,0,3),(0,2,4)]),(1,[(1,0,3),(0,2,4)]),(5,[(1,0,1),(3,3,4)]),(3,[(1,0,1),(3,3,4)]),(1,[(0,0,1),(3,0,2)]),(5,[(0,0,1),(3,0,2)]),(5,[(0,0,1),(3,1,2)]),(1,[(0,0,1),(0,0,3)]),(3,[(0,0,1),(0,3,4)]),(3,[(0,2,3),(1,2,3)]),(1,[(0,2,3),(1,2,3)]),(5,[(1,0,1),(3,2,4)]),(7,[(1,0,1),(3,3,4)]),(3,[(1,2,3)]),(1,[(1,2,3)]),(5,[(2,0,3)]),(1,[(1,0,1),(0,3,4)]),(1,[(3,0,2)]),(3,[(0,0,2),(1,1,4)]),(1,[(3,0,1),(3,2,4)]),(1,[(0,0,1),(1,2,4)]),(1,[(1,0,1),(0,2,4)]),(5,[(0,0,1),(0,1,2)]),(1,[(0,0,2)]),(7,[(0,0,1),(0,0,2)]),(9,[(0,0,1),(0,0,2)]),(7,[(0,1,2),(1,0,4)]),(5,[(0,0,2),(1,1,4)]),(1,[(2,0,1),(3,2,4)]),(1,[(1,1,2)]),(1,[(3,1,2)]),(1,[(0,1,2),(1,0,4)]),(5,[(0,0,1),(1,2,4)]),(1,[(3,0,1),(0,2,4)]),(7,[(0,0,1),(1,2,4)]),(3,[(0,1,2)]),(1,[(2,1,2)]),(9,[(0,2,3)])]
def spec (i : Nat) := specTab[i]?.getD (0,[])
def checked (i : Nat) := nodeOK target root mins spec states perm i
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block0 : Good checked 0 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block1 : Good checked 4 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block2 : Good checked 8 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block3 : Good checked 12 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block4 : Good checked 16 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block5 : Good checked 20 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block6 : Good checked 24 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block7 : Good checked 28 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block8 : Good checked 32 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block9 : Good checked 36 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block10 : Good checked 40 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block11 : Good checked 44 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block12 : Good checked 48 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block13 : Good checked 52 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block14 : Good checked 56 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block15 : Good checked 60 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block16 : Good checked 64 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block17 : Good checked 68 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block18 : Good checked 72 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block19 : Good checked 76 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block20 : Good checked 80 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block21 : Good checked 84 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block22 : Good checked 88 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block23 : Good checked 92 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block24 : Good checked 96 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block25 : Good checked 100 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block26 : Good checked 104 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block27 : Good checked 108 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block28 : Good checked 112 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block29 : Good checked 116 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block30 : Good checked 120 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block31 : Good checked 124 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block32 : Good checked 128 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block33 : Good checked 132 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block34 : Good checked 136 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block35 : Good checked 140 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block36 : Good checked 144 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block37 : Good checked 148 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block38 : Good checked 152 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block39 : Good checked 156 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block40 : Good checked 160 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block41 : Good checked 164 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block42 : Good checked 168 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block43 : Good checked 172 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block44 : Good checked 176 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block45 : Good checked 180 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block46 : Good checked 184 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block47 : Good checked 188 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block48 : Good checked 192 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block49 : Good checked 196 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block50 : Good checked 200 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block51 : Good checked 204 4 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem block52 : Good checked 208 3 := checkGood (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem total : Good checked 0 211 := (concatGood (concatGood (concatGood (concatGood (concatGood block0 (concatGood block1 block2)) (concatGood block3 (concatGood block4 block5))) (concatGood (concatGood block6 (concatGood block7 block8)) (concatGood (concatGood block9 block10) (concatGood block11 block12)))) (concatGood (concatGood (concatGood block13 (concatGood block14 block15)) (concatGood block16 (concatGood block17 block18))) (concatGood (concatGood block19 (concatGood block20 block21)) (concatGood (concatGood block22 block23) (concatGood block24 block25))))) (concatGood (concatGood (concatGood (concatGood block26 (concatGood block27 block28)) (concatGood block29 (concatGood block30 block31))) (concatGood (concatGood block32 (concatGood block33 block34)) (concatGood (concatGood block35 block36) (concatGood block37 block38)))) (concatGood (concatGood (concatGood block39 (concatGood block40 block41)) (concatGood (concatGood block42 block43) (concatGood block44 block45))) (concatGood (concatGood block46 (concatGood block47 block48)) (concatGood (concatGood block49 block50) (concatGood block51 block52))))))
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem impossible : Impossible true target 9 root.toFinset := by
  have h := certified (states:=states) (perm:=perm) (specs:=spec) (N:=211) (fun j => perm_onto _) pri (fun i hi => total i (by omega) hi) 210 (by decide)
  exact h
def essentials : List (Sig × Row × Row) := [(root.getD 0 zero,14,15),(root.getD 1 zero,13,15),(root.getD 2 zero,11,15),(root.getD 3 zero,7,15),(root.getD 4 zero,7,23)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lower : Lower true root target 10 := by
  apply lower_impossible (L:=9) (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro a ha
    apply essential_ok (xs:=essentials) (by decide +kernel) a
    exact (show (essentials.map Prod.fst).toFinset = root.toFinset by decide +kernel).symm ▸ List.mem_toFinset.mpr ha
  · exact impossible
end Tab1

namespace Five12127
open PEqualNP.Outside.L_meta_12126.Core FirstGate12127 Bound12127 Four12127
def raw5 := in5
def m0 : List Move := [forceLow 4, swapNext 3, swapNext 2, swapNext 1, swapNext 0]
def d0 : Sig := ~~~raw 0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s0 : Slice true in5 last d0 7 :=
  slice_correct (ms:=m0) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) love880
def m1 : List Move := [forceHigh 4, swapNext 3, swapNext 2, swapNext 1, swapNext 0]
def d1 : Sig := raw 0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s1 : Slice true in5 last d1 7 :=
  slice_correct (ms:=m1) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) lovfee8
def m2 : List Move := [forceLow 4, swapNext 3, swapNext 2, swapNext 1]
def d2 : Sig := ~~~raw 1
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s2 : Slice true in5 last d2 7 :=
  slice_correct (ms:=m2) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) love880
def m3 : List Move := [forceHigh 4, swapNext 3, swapNext 2, swapNext 1]
def d3 : Sig := raw 1
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s3 : Slice true in5 last d3 7 :=
  slice_correct (ms:=m3) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) lovfee8
def m4 : List Move := [forceLow 4, swapNext 3, swapNext 2]
def d4 : Sig := ~~~raw 2
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s4 : Slice true in5 last d4 7 :=
  slice_correct (ms:=m4) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) love880
def m5 : List Move := [forceHigh 4, swapNext 3, swapNext 2]
def d5 : Sig := raw 2
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s5 : Slice true in5 last d5 7 :=
  slice_correct (ms:=m5) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) lovfee8
def m6 : List Move := [forceLow 4, swapNext 3]
def d6 : Sig := ~~~raw 3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s6 : Slice true in5 last d6 7 :=
  slice_correct (ms:=m6) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) love880
def m7 : List Move := [forceHigh 4, swapNext 3]
def d7 : Sig := raw 3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s7 : Slice true in5 last d7 7 :=
  slice_correct (ms:=m7) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) lovfee8
def m8 : List Move := [forceLow 4]
def d8 : Sig := ~~~raw 4
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s8 : Slice true in5 last d8 7 :=
  slice_correct (ms:=m8) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) love880
def m9 : List Move := [forceHigh 4]
def d9 : Sig := raw 4
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s9 : Slice true in5 last d9 7 :=
  slice_correct (ms:=m9) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) lovfee8
def minors : List (Sig × Nat) := [(d0,7), (d1,7), (d2,7), (d3,7), (d4,7), (d5,7), (d6,7), (d7,7), (d8,7), (d9,7)]
def ps : List (Row × Row) := [(21, 20), (11, 10), (14, 12), (19, 17), (22, 18), (13, 9), (14, 6), (25, 17), (26, 10), (21, 5)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem nolast : Impossible true last 9 raw5.toFinset := by
  apply first_sound (mins:=minors) (pairs:=ps) (by decide +kernel) (by decide +kernel)
  · intro p hp
    simp only [minors,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact s0
    · exact s1
    · exact s2
    · exact s3
    · exact s4
    · exact s5
    · exact s6
    · exact s7
    · exact s8
    · exact s9
  · decide +kernel
def eslast : List (Sig × Row × Row) := [(raw5.getD 0 zero,6,7), (raw5.getD 1 zero,5,7), (raw5.getD 2 zero,3,7), (raw5.getD 3 zero,3,11), (raw5.getD 4 zero,3,19)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lolast : Lower true raw5 last 10 := by
  apply lower_impossible (L := 9) (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro a ha
    apply essential_ok (xs:=eslast) (by decide +kernel) a
    exact (show (eslast.map Prod.fst).toFinset = raw5.toFinset by decide +kernel).symm ▸ List.mem_toFinset.mpr ha
  · exact nolast
end Five12127

namespace Finish12127
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_12126.Core Bound12127 Model12127

def samples (r : Row) (j : Fin 6) := bit r (in6.getD j.val zero)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sixEval (C : Circuit) (legal : FanInTwo C) (computes : ∀ x, C.eval (List.ofFn x) = target x) :
    (execute C.gates in6).getD C.output zero = six := by
  apply bit_ext
  intro r
  rw [←b_read, execute_bits _ _ _ (fun g hg => (legal g hg).1)]
  have eq := computes (samples r)
  have cols : in6 = List.ofFn (fun j : Fin 6 => in6.getD j.val zero) := rfl
  have mapped : List.ofFn (samples r) = in6.map (bit r) := by
    conv_rhs => rw [cols,List.map_ofFn]
    rfl
  rw [mapped] at eq
  have tb : ∀ r : Row, target (samples r) = bit r six := by decide +kernel
  exact eq.trans (tb r)
def essentials : List (Sig × Row × Row) := [(in6.getD 0 zero,14,15),(in6.getD 1 zero,13,15),(in6.getD 2 zero,11,15),(in6.getD 3 zero,7,15),(in6.getD 4 zero,7,23),(in6.getD 5 zero,7,39)]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem binary (noSmall : Impossible true six 11 in6.toFinset) (C : Circuit) (legal : FanInTwo C)
    (computes : ∀ x, C.eval (List.ofFn x) = target x) : 12 ≤ C.gates.countP (fun g => !isNot g) := by
  have out := get_rep (u:=true) (execute C.gates in6) C.output
  rw [sixEval C legal computes] at out
  unfold PEqualNP.Outside.L_meta_12126.Core.Repr at out
  have pg : bit 0 six = false := by decide +kernel
  have pp : proper six := by unfold proper; decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract C.gates in6 legal (by simp) pp (out.resolve_right (fun h => h pp))
  rw [nrm_map (show in6.all plainWord = true by decide +kernel)] at sub
  have he : S = in6.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub _ h)
    · intro ha
      have need : Essential six in6 a := by
        apply essential_ok (xs:=essentials) (by decide +kernel) a
        exact (show (essentials.map Prod.fst).toFinset = in6.toFinset by decide +kernel).symm ▸ ha
      obtain ⟨r,s,hd,iso⟩ := need
      exact raw_required run in6 a sub r s hd iso
  by_contra! h
  exact noSmall k (by omega) (he ▸ run)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem positive (noSmall : Impossible true six 11 in6.toFinset) :
    ∀ s : Nat, HasCircuitSize 6 target s → ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧
       ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  intro s h
  obtain ⟨c,legal,hs,computes⟩ := h
  by_cases all : ∀ g ∈ c.gates, isNot g = false
  · refine ⟨c,?_,hs,computes⟩
    intro g hg
    obtain ⟨allowed,len⟩ := legal g hg
    have hnot := all g hg
    rcases g with ⟨op,ins⟩
    cases op <;> simp_all [isNot]
  · have lower := binary noSmall c legal computes
    have lt : c.gates.countP (fun g => !isNot g) < c.gates.length := by
      by_contra! h
      exact all (fun g hg => by simpa using (List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h)) g hg)
    obtain ⟨q,mono,size,eq⟩ := Thirteen12127.upper
    exact ⟨q,mono,by rw [size]; change c.gates.length ≤ s at hs; omega,eq⟩
end Finish12127

end PEqualNP.Outside.L_meta_12126

open PEqualNP.Outside.L_meta_12126

set_option maxRecDepth 16384 in
theorem PEqualNP.Outside.L_meta_12126 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676736 * 2 ^ 32 + 4269834240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676736 * 2 ^ 32 + 4269834240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  apply Finish12127.positive
  apply Bound12127.six_lower
  · rw [show Bound12127.light = Tab0.target by decide +kernel]
    exact Tab0.lower
  · rw [show Bound12127.heavy = Tab1.target by decide +kernel]
    exact Tab1.lower
  · exact Five12127.lolast

