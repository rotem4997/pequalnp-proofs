import PEqualNP.Defs

-- The live-set and restriction lemmas follow L-meta-10554, L-meta-10802, L-meta-1674, L-meta-670 and L-meta-1667.
-- The rectangle argument follows L-meta-8459.
namespace PEqualNP.Outside.L_meta_14716
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 256
def zero : Sig := 0
def one : Sig := BitVec.allOnes 256
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

def bit (i : Fin 256) (a : Sig) : Bool := a.getLsbD i.val
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

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
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


abbrev Row := Fin 256
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


-- Natural-number words, and a search table checked level by level.
def W (a : Nat) : Sig := BitVec.ofNat 256 a
def full : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def xN : Nat → Nat
  | 0 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  | 1 => 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
  | 2 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
  | 3 => 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00
  | 4 => 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
  | 5 => 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000
  | 6 => 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
  | _ => 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000
def nb (o a b : Nat) : Nat :=
  bif Nat.beq o 0 then Nat.land a b else bif Nat.beq o 1 then Nat.lor a b else
    bif Nat.beq o 2 then Nat.xor a (Nat.land a b) else Nat.xor b (Nat.land a b)
theorem bit_W (r : Row) (a : Nat) : bit r (W a) = a.testBit r.val := by
  unfold bit W
  rw [BitVec.getLsbD_ofNat]
  simp [r.isLt]
theorem tb_land (a b i : Nat) : (Nat.land a b).testBit i = (a.testBit i && b.testBit i) := Nat.testBit_and ..
theorem tb_lor (a b i : Nat) : (Nat.lor a b).testBit i = (a.testBit i || b.testBit i) := Nat.testBit_or ..
theorem tb_xor (a b i : Nat) : (Nat.xor a b).testBit i = (a.testBit i ^^ b.testBit i) := Nat.testBit_xor ..
theorem nbeq {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h
theorem W_nb (o a b : Nat) : W (nb o a b) = bin o (W a) (W b) := by
  apply bit_ext
  intro r
  rw [bit_bin,bit_W,bit_W,bit_W]
  by_cases h0 : o = 0
  · subst h0
    exact tb_land a b _
  by_cases h1 : o = 1
  · subst h1
    exact tb_lor a b _
  by_cases h2 : o = 2
  · subst h2
    change (Nat.xor a (Nat.land a b)).testBit r.val = _
    rw [tb_xor,tb_land]
    cases a.testBit r.val <;> cases b.testBit r.val <;> rfl
  · unfold nb
    rw [nbeq h0,nbeq h1,nbeq h2,if_neg h0,if_neg h1,if_neg h2]
    change (Nat.xor b (Nat.land a b)).testBit r.val = _
    rw [tb_xor,tb_land]
    cases a.testBit r.val <;> cases b.testBit r.val <;> rfl
theorem bin_four (u : Bool) (o : Nat) (h : (u || Nat.blt o 2) = true) : ∃ e, allowed u e ∧ ∀ a b, bin o a b = bin e a b := by
  cases u
  · refine ⟨o,Or.inl ?_,fun _ _ => rfl⟩
    simpa only [Bool.false_or,Nat.blt_eq] using h
  · by_cases h : o < 4
    · exact ⟨o,Or.inr ⟨rfl,h⟩,fun _ _ => rfl⟩
    · refine ⟨3,Or.inr ⟨rfl,by omega⟩,fun a b => ?_⟩
      have h0 : o ≠ 0 := by omega
      have h1 : o ≠ 1 := by omega
      have h2 : o ≠ 2 := by omega
      simp [bin,h0,h1,h2]
theorem W_zero : W 0 = zero := rfl
theorem W_full : W full = one := by
  apply bit_ext
  intro r
  rw [bit_W,bit_one]
  revert r
  decide +kernel
set_option maxRecDepth 8192 in
theorem W_inj {a b : Nat} (ha : a < 2^256) (hb : b < 2^256) (h : W a = W b) : a = b := by
  have := congrArg BitVec.toNat h
  simpa only [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using this

def rootsW (R : List Nat) : List Sig := R.map fun i => W (xN i)
def LowN (u : Bool) (R : List Nat) (T L : Nat) : Prop := Lower u (rootsW R) (W T) L
abbrev SliceD := Nat × Nat × List Nat
def SliceN (u : Bool) (R : List Nat) (T : Nat) (s : SliceD) : Prop :=
  Slice u (rootsW R) (W T) (W s.1) s.2.1 ∧ ∀ v ∈ s.2.2, v ∈ R

def baseOK (T : Nat) (R : List Nat) (E : List (Nat × Nat × Nat)) : Bool :=
  decide (T < 2^256) && !(T.testBit 0) && (E.map Prod.fst == R) && !R.isEmpty && decide (rootsW R).Nodup &&
  R.all (fun i => !((xN i).testBit 0)) &&
  E.all (fun e => decide (e.2.1 < 256) && decide (e.2.2 < 256) && (T.testBit e.2.1 != T.testBit e.2.2) &&
    R.all (fun i => i == e.1 || (xN i).testBit e.2.1 == (xN i).testBit e.2.2))

abbrev BaseP (T : Nat) (R : List Nat) : Prop :=
  T < 2^256 ∧ plainWord (W T) = true ∧ (rootsW R).Nodup ∧ (rootsW R).all plainWord = true ∧
  (∀ a ∈ rootsW R, Essential (W T) (rootsW R) a) ∧ proper (W T)
theorem BaseP.lt {T R} (h : BaseP T R) : T < 2^256 := h.1
theorem BaseP.plain {T R} (h : BaseP T R) : plainWord (W T) = true := h.2.1
theorem BaseP.nodup {T R} (h : BaseP T R) : (rootsW R).Nodup := h.2.2.1
theorem BaseP.plainR {T R} (h : BaseP T R) : (rootsW R).all plainWord = true := h.2.2.2.1
theorem BaseP.ess {T R} (h : BaseP T R) : ∀ a ∈ rootsW R, Essential (W T) (rootsW R) a := h.2.2.2.2.1
theorem BaseP.prop {T R} (h : BaseP T R) : proper (W T) := h.2.2.2.2.2

theorem baseOK_ok {T R E} (h : baseOK T R E = true) : BaseP T R := by
  simp only [baseOK,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,Bool.not_eq_true',List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hT,h0⟩,hE⟩,hne⟩,nd⟩,pr⟩,he⟩ := h
  have ess : ∀ a ∈ rootsW R, Essential (W T) (rootsW R) a := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    rw [←hE] at hi
    obtain ⟨e,hem,rfl⟩ := List.mem_map.mp hi
    obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := he e hem
    refine ⟨⟨e.2.1,h1⟩,⟨e.2.2,h2⟩,?_,?_⟩
    · rw [bit_W,bit_W]
      simpa using h3
    · intro v hv hne
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv
      rw [bit_W,bit_W]
      have := h4 j hj
      simp only [Bool.or_eq_true,beq_iff_eq] at this
      rcases this with rfl | this
      · exact absurd rfl hne
      · exact this
  refine ⟨hT,?_,nd,?_,ess,?_⟩
  · have : bit 0 (W T) = false := (bit_W 0 T).trans h0
    simp [plainWord,this]
  · rw [List.all_eq_true]
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    have : bit 0 (W (xN i)) = false := (bit_W 0 _).trans (by simpa using pr i hi)
    simp [plainWord,this]
  · cases R with
    | nil => simp at hne
    | cons i R =>
      obtain ⟨r,s,hd,_⟩ := ess (W (xN i)) (by simp [rootsW])
      constructor
      · intro hh
        rw [hh,bit_zero,bit_zero] at hd
        exact hd rfl
      · intro hh
        rw [hh,bit_one,bit_one] at hd
        exact hd rfl

theorem lowOf {u T R E K} (hB : baseOK T R E = true) (h : Impossible u (W T) K (rootsW R).toFinset) :
    LowN u R T (K+1) := by
  have b := baseOK_ok hB
  exact lower_impossible b.prop b.plain b.plainR b.ess h
theorem lowCount {u T R E K} (hB : baseOK T R E = true) (h : K + 2 ≤ R.length) : LowN u R T (K+1) := by
  apply lowOf hB
  intro k hk run
  have b := baseOK_ok hB
  have := live_size run
  rw [List.toFinset_card_of_nodup b.nodup,rootsW,List.length_map] at this
  omega

def rowOf : List Nat → Nat → Nat → Nat
  | [],w,_ => w
  | v::vs,w,r => rowOf vs (w + ((r % 2) <<< v)) (r / 2)
def sliceChk (R : List Nat) (T : Nat) (R' : List Nat) (G d : Nat) (vs : List Nat) (w : Nat) : Bool :=
  vs.all (fun v => R.contains v) &&
  (List.range 256).all (fun r => let q := rowOf vs w r
    Nat.blt q 256 && d.testBit q && (T.testBit q == G.testBit r)) &&
  R.all (fun i => (List.range 256).all (fun r => !((xN i).testBit (rowOf vs w r))) ||
    (List.range 256).all (fun r => (xN i).testBit (rowOf vs w r)) ||
    R'.any (fun j => (List.range 256).all (fun r => (xN i).testBit (rowOf vs w r) == (xN j).testBit r)))

theorem mkSlice {u R T E R' G E' d L vs w} (_hB : baseOK T R E = true) (hB' : baseOK G R' E' = true)
    (hL : LowN u R' G L) (h : sliceChk R T R' G d vs w = true) : SliceN u R T (d,L,vs) := by
  have b' := baseOK_ok hB'
  simp only [sliceChk,Bool.and_eq_true,List.all_eq_true,List.mem_range,Bool.or_eq_true,beq_iff_eq,
    Bool.not_eq_true',List.any_eq_true,Nat.blt_eq,List.contains_eq_mem,decide_eq_true_eq] at h
  obtain ⟨⟨hv,hr⟩,hR⟩ := h
  let f : Row → Row := fun r => ⟨rowOf vs w r.val,(hr r.val r.isLt).1.1⟩
  have fe (r : Row) (a : Nat) : bit (f r) (W a) = a.testBit (rowOf vs w r.val) := bit_W _ _
  have obs : restrictRows f (observe (W T)) = observe (W G) := by
    funext r
    change bit (f r) (W T) = bit r (W G)
    rw [fe,bit_W]
    exact (hr r.val r.isLt).2
  refine ⟨⟨f,rootsW R',?_,?_,?_,?_⟩,hv⟩
  · intro r
    rw [fe]
    exact (hr r.val r.isLt).1.2
  · intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    rcases hR i hi with (h | h) | ⟨j,hj,h⟩
    · refine Or.inr (Or.inl ⟨false,funext fun r => ?_⟩)
      exact (fe r _).trans (h r.val r.isLt)
    · refine Or.inr (Or.inl ⟨true,funext fun r => ?_⟩)
      exact (fe r _).trans (h r.val r.isLt)
    · have e : restrictRows f (observe (W (xN i))) = observe (W (xN j)) := by
        funext r
        exact (fe r _).trans ((h r.val r.isLt).trans (bit_W r _).symm)
      rw [e]
      exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hj))
  · rw [obs]
    exact observe_proper b'.prop
  · rw [obs]
    exact hL

def opOK (u : Bool) (o : Nat) : Bool := u || Nat.blt o 2
def av (u : Bool) (d : Nat) (P : List Nat) (v : Nat) : Bool :=
  let m := Nat.land v d
  Nat.beq m 0 || Nat.beq m d || P.any (fun x => Nat.beq x m || (u && Nat.beq x (Nat.xor d m)))
def cn (d v : Nat) : Nat :=
  let m := Nat.land v d
  bif Nat.beq m 0 || Nat.beq m d then 1 else 0
def sumc (d : Nat) : List Nat → Nat
  | [] => 0
  | v::l => Nat.add (cn d v) (sumc d l)
def mkPool (u : Bool) (P : List Nat) : List Nat → List Nat
  | [] => P
  | c::cs => mkPool u (bif opOK u (Nat.mod c 4) then P ++ [nb (Nat.mod c 4) (P.getD (Nat.mod (Nat.div c 4) 32) 0) (P.getD (Nat.div c 128) 0)] else P) cs
def initPool (d : Nat) (vs : List Nat) : List Nat := vs.map fun v => Nat.land (xN v) d

abbrev RF (f : Row → Row) (v : Nat) : Wire Row := restrictRows f (observe (W v))
def PS (u : Bool) (f : Row → Row) (bank : List (Wire Row)) (P : List Nat) : Prop :=
  ∀ v ∈ P, Available u bank (RF f v)
theorem rf_apply (f : Row → Row) (v : Nat) (r : Row) : RF f v r = v.testBit (f r).val := bit_W _ _
theorem rf_land {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (v : Nat) :
    RF f (Nat.land v d) = RF f v := by
  funext r
  have h := dom r
  rw [bit_W] at h
  rw [rf_apply,rf_apply]
  have : (Nat.land v d).testBit (f r).val = (v.testBit (f r).val && d.testBit (f r).val) := Nat.testBit_and ..
  rw [this,h,Bool.and_true]
theorem rf_zero {f : Row → Row} : RF f 0 = fun _ => false := by
  funext r
  rw [rf_apply]
  exact Nat.zero_testBit _
theorem rf_dom {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) : RF f d = fun _ => true := by
  funext r
  exact dom r
theorem rf_xor {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (m : Nat) :
    RF f (Nat.xor d m) = inv (RF f m) := by
  funext r
  have h := dom r
  rw [bit_W] at h
  change RF f (Nat.xor d m) r = !(RF f m r)
  rw [rf_apply,rf_apply]
  have : (Nat.xor d m).testBit (f r).val = ((d.testBit (f r).val) ^^ (m.testBit (f r).val)) := Nat.testBit_xor ..
  rw [this,h,Bool.true_xor]
theorem cn_ok {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (v : Nat) : cn d v ≤ cost (RF f v) := by
  change (bif (Nat.beq (Nat.land v d) 0 || Nat.beq (Nat.land v d) d) then 1 else 0) ≤ _
  cases h : (Nat.beq (Nat.land v d) 0 || Nat.beq (Nat.land v d) d)
  · exact Nat.zero_le _
  · have c : Constant (RF f v) := by
      rw [←rf_land dom v]
      rw [Bool.or_eq_true] at h
      rcases h with h | h
      · rw [Nat.eq_of_beq_eq_true h,rf_zero]
        exact ⟨false,rfl⟩
      · rw [Nat.eq_of_beq_eq_true h,rf_dom dom]
        exact ⟨true,rfl⟩
    rw [cost,if_pos c]
    exact Nat.le_refl 1
theorem av_ok {u} {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) {bank P v} (hP : PS u f bank P)
    (h : av u d P v = true) : Available u bank (RF f v) := by
  simp only [av,Bool.or_eq_true,List.any_eq_true,Bool.and_eq_true] at h
  rw [←rf_land dom v]
  rcases h with (h | h) | ⟨x,hx,h | ⟨hu,h⟩⟩
  · rw [Nat.eq_of_beq_eq_true h,rf_zero]
    exact Or.inr (Or.inl ⟨false,rfl⟩)
  · rw [Nat.eq_of_beq_eq_true h,rf_dom dom]
    exact Or.inr (Or.inl ⟨true,rfl⟩)
  · rw [←Nat.eq_of_beq_eq_true h]
    exact hP x hx
  · have e := hP x hx
    rw [Nat.eq_of_beq_eq_true h,rf_xor dom] at e
    have e' := avail_inv hu e
    rwa [inv_inv'] at e'
theorem rf_nb (f : Row → Row) (o a b : Nat) : RF f (nb o a b) = comb o (RF f a) (RF f b) := by
  unfold RF
  rw [W_nb,obs_bin,restrict_comb]
theorem pay_nb {u} {f : Row → Row} {roots bank p P} (o a b : Nat) (ho : opOK u o = true) (hr : Reach u roots p bank) (hP : PS u f bank P)
    (ha : Available u bank (RF f a)) (hb : Available u bank (RF f b)) :
    ∃ next, Reach u roots (p+1) next ∧ PS u f next P ∧ Available u next (RF f (nb o a b)) ∧
      ∀ v, Available u bank v → Available u next v := by
  obtain ⟨e,he,heq⟩ := bin_four u o ho
  have hn : RF f (nb o a b) = comb e (RF f a) (RF f b) := by
    unfold RF
    rw [W_nb,heq,obs_bin,restrict_comb]
  obtain ⟨op,x,y,e1,hx,hy,_,_⟩ := comb_prime (d:=e) he ha hb
  refine ⟨_,Reach.two op hr hx hy,fun v hv => available_cons _ (hP v hv),?_,fun v hv => available_cons _ hv⟩
  rw [hn,e1]
  exact Or.inl (by simp)
theorem getD_ps {u} {f : Row → Row} {bank P} (hP : PS u f bank P) (i : Nat) : Available u bank (RF f (P.getD i 0)) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : P[i]? with
  | none => exact Or.inr (Or.inl ⟨false,rf_zero⟩)
  | some a => exact hP a (List.mem_of_getElem? h)
theorem mkPool_ok {u} {f : Row → Row} {roots} (cs : List Nat) {bank p P} (hr : Reach u roots p bank)
    (hP : PS u f bank P) : ∃ next, Reach u roots (p+cs.length) next ∧ PS u f next (mkPool u P cs) := by
  induction cs generalizing bank p P with
  | nil => exact ⟨bank,hr,hP⟩
  | cons c cs ih =>
    have big : ∃ next, Reach u roots (p+1) next ∧ PS u f next (bif opOK u (Nat.mod c 4) then P ++ [nb (Nat.mod c 4) (P.getD (Nat.mod (Nat.div c 4) 32) 0) (P.getD (Nat.div c 128) 0)] else P) := by
      cases ho : opOK u (Nat.mod c 4)
      · refine ⟨_,Reach.two false hr (Or.inr (Or.inl ⟨false,rfl⟩)) (Or.inr (Or.inl ⟨false,rfl⟩)),fun v hv => available_cons _ (hP v hv)⟩
      · obtain ⟨next,h1,h2,h3,_⟩ := pay_nb (Nat.mod c 4) _ _ ho hr hP (getD_ps hP (Nat.mod (Nat.div c 4) 32)) (getD_ps hP (Nat.div c 128))
        refine ⟨next,h1,?_⟩
        intro v hv
        rw [cond_true] at hv
        rcases List.mem_append.mp hv with hv | hv
        · exact h2 v hv
        · rw [List.mem_singleton.mp hv]
          exact h3
    obtain ⟨next,h1,this⟩ := big
    obtain ⟨out,o1,o2⟩ := ih h1 this
    exact ⟨out,by rw [List.length_cons,show p+(cs.length+1) = p+1+cs.length by omega]; exact o1,o2⟩

abbrev CutV := Nat × Nat × Nat × List Nat
def keepB (u : Bool) (d : Nat) (P : List Nat) (ka : Bool) (a : Nat) : Bool := bif ka then av u d P a else true
def keepC (d : Nat) (ka : Bool) (a : Nat) : Nat := bif ka then cn d a else 0
def cutEval (u : Bool) (k : Nat) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (c : CutV) : Bool :=
  rest.all (av u c.1 c.2.2.2) && keepB u c.1 c.2.2.2 ka a && keepB u c.1 c.2.2.2 kb b &&
  (bif av u c.1 c.2.2.2 z then
    Nat.blt (Nat.add k c.2.2.1) (Nat.add c.2.1 (Nat.add (Nat.add (sumc c.1 rest) (cn c.1 z)) (Nat.add (keepC c.1 ka a) (keepC c.1 kb b))))
  else av u c.1 c.2.2.2 a && av u c.1 c.2.2.2 b &&
    Nat.blt (Nat.add (Nat.add k c.2.2.1) 1) (Nat.add c.2.1 (Nat.add (Nat.add (sumc c.1 rest) (cn c.1 z)) (Nat.add (keepC c.1 ka a) (keepC c.1 kb b)))))
def same (u : Bool) (p : Nat × Nat) (v : Nat) : Bool :=
  bif u then Nat.testBit v p.1 == Nat.testBit v p.2 else !(Nat.testBit v p.1) || Nat.testBit v p.2
def sepEval (u : Bool) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (p : Nat × Nat) : Bool :=
  same u p z && (!ka || same u p a) && (!kb || same u p b) && rest.all (same u p)
def sepOK (T : Nat) (p : Nat × Nat) : Bool := Nat.blt p.1 256 && Nat.blt p.2 256 && T.testBit p.1 && !(T.testBit p.2)

def kidW (rest : List Nat) (a b z : Nat) (ka kb : Bool) : List Sig :=
  W z :: kept ka (W a) (kept kb (W b) (rest.map W))
theorem sumc_ok {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (l : List Nat) :
    sumc d l ≤ mass (l.map (RF f)) := by
  induction l with
  | nil => simp [sumc]
  | cons v l ih =>
    rw [List.map_cons,mass_cons]
    exact Nat.add_le_add (cn_ok dom v) ih
theorem mass_keep {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (ka : Bool) (a : Nat) (l : List (Wire Row)) :
    keepC d ka a + mass l ≤ mass (kept ka (RF f a) l) := by
  cases ka
  · simp [keepC,kept]
  · rw [kept,if_pos rfl,mass_cons]
    exact Nat.add_le_add_right (cn_ok dom a) _
theorem kid_map (f : Row → Row) (rest : List Nat) (a b z : Nat) (ka kb : Bool) :
    ((kidW rest a b z ka kb).map observe).map (restrictRows f) =
      RF f z :: kept ka (RF f a) (kept kb (RF f b) (rest.map (RF f))) := by
  cases ka <;> cases kb <;> simp [kidW,kept,List.map_map,Function.comp_def,RF]

def CutP (u : Bool) (_R : List Nat) (T : Nat) (c : CutV) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)), (∀ r, bit (f r) (W c.1) = true) ∧
    ¬Constant (restrictRows f (observe (W T))) ∧ Reach u (roots.map observe) c.2.2.1 bank ∧ PS u f bank c.2.2.2 ∧
    ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (restrictRows f (observe (W T))) → c.2.1 ≤ p

theorem cut_sound {u R T c k rest a b o ka kb} (hc : CutP u R T c) (ho : opOK u o = true)
    (nd : (kidW rest a b (nb o a b) ka kb).Nodup)
    (h : cutEval u k rest a b (nb o a b) ka kb c = true) :
    Impossible u (W T) k (kidW rest a b (nb o a b) ka kb).toFinset := by
  obtain ⟨f,roots,bank,dom,nc,hr,hP,lo⟩ := hc
  simp only [cutEval,Bool.and_eq_true,List.all_eq_true] at h
  obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := h
  have key : ∃ q bank', Reach u (roots.map observe) q bank' ∧ PS u f bank' c.2.2.2 ∧ Available u bank' (RF f (nb o a b)) ∧
      k + q < c.2.1 + ((sumc c.1 rest + cn c.1 (nb o a b)) + (keepC c.1 ka a + keepC c.1 kb b)) := by
    cases hz : av u c.1 c.2.2.2 (nb o a b)
    · rw [hz,cond_false,Bool.and_eq_true,Bool.and_eq_true,Nat.blt_eq] at h4
      obtain ⟨next,n1,n2,n3,_⟩ := pay_nb o a b ho hr hP (av_ok dom hP h4.1.1) (av_ok dom hP h4.1.2)
      refine ⟨_,next,n1,n2,n3,?_⟩
      have := h4.2
      exact this
    · rw [hz,cond_true,Nat.blt_eq] at h4
      exact ⟨_,bank,hr,hP,av_ok dom hP hz,h4⟩
  obtain ⟨q,bank',r1,r2,r3,r4⟩ := key
  intro k' hk run
  have supp : supply u bank' (((kidW rest a b (nb o a b) ka kb).map observe).map (restrictRows f)) := by
    rw [kid_map]
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact r3
    have kb' : ∀ v ∈ kept kb (RF f b) (rest.map (RF f)), Available u bank' v := by
      intro v hv
      cases kb
      · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
        exact av_ok dom r2 (h1 x hx)
      · rcases List.mem_cons.mp hv with rfl | hv
        · exact av_ok dom r2 h3
        · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
          exact av_ok dom r2 (h1 x hx)
    cases ka
    · exact kb' v hv
    · rcases List.mem_cons.mp hv with rfl | hv
      · exact av_ok dom r2 h2
      · exact kb' v hv
  have bound := projected_bound f (list_run run _ nd rfl) nc r1 supp lo
  rw [kid_map,mass_cons] at bound
  have m1 := mass_keep dom ka a (kept kb (RF f b) (rest.map (RF f)))
  have m2 := mass_keep dom kb b (rest.map (RF f))
  have m3 := sumc_ok dom rest
  have m4 := cn_ok dom (nb o a b)
  omega

theorem kid_mem {rest : List Nat} {a b z : Nat} {ka kb : Bool} {v : Sig} (hv : v ∈ kidW rest a b z ka kb) :
    ∃ x, v = W x ∧ (x = z ∨ (ka = true ∧ x = a) ∨ (kb = true ∧ x = b) ∨ x ∈ rest) := by
  rcases List.mem_cons.mp hv with rfl | hv
  · exact ⟨z,rfl,Or.inl rfl⟩
  have low : ∀ v ∈ kept kb (W b) (rest.map W), ∃ x, v = W x ∧ ((kb = true ∧ x = b) ∨ x ∈ rest) := by
    intro v hv
    cases kb
    · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
      exact ⟨x,e.symm,Or.inr hx⟩
    · rcases List.mem_cons.mp hv with e | hv
      · exact ⟨b,e,Or.inl ⟨rfl,rfl⟩⟩
      · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
        exact ⟨x,e.symm,Or.inr hx⟩
  cases ka
  · obtain ⟨x,h1,h2⟩ := low v hv
    exact ⟨x,h1,Or.inr (Or.inr h2)⟩
  · rcases List.mem_cons.mp hv with e | hv
    · exact ⟨a,e,Or.inr (Or.inl ⟨rfl,rfl⟩)⟩
    · obtain ⟨x,h1,h2⟩ := low v hv
      exact ⟨x,h1,Or.inr (Or.inr h2)⟩
theorem sep_sound {u T k rest a b o ka kb p} (hT : sepOK T p = true)
    (h : sepEval u rest a b (nb o a b) ka kb p = true) :
    Impossible u (W T) k (kidW rest a b (nb o a b) ka kb).toFinset := by
  simp only [sepOK,Bool.and_eq_true,Nat.blt_eq,Bool.not_eq_true'] at hT
  obtain ⟨⟨⟨p1,p2⟩,t1⟩,t2⟩ := hT
  simp only [sepEval,Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true',List.all_eq_true] at h
  obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := h
  have all : ∀ v ∈ kidW rest a b (nb o a b) ka kb, ∃ x, v = W x ∧ same u p x = true := by
    intro v hv
    obtain ⟨x,rfl,hx⟩ := kid_mem hv
    refine ⟨x,rfl,?_⟩
    rcases hx with rfl | ⟨q,rfl⟩ | ⟨q,rfl⟩ | hx
    · exact h1
    · subst q; exact h2.resolve_left (by simp)
    · subst q; exact h3.resolve_left (by simp)
    · exact h4 x hx
  intro k' _ run
  cases u
  · obtain ⟨v,hv,hp,hn⟩ := mono_row_difference run rfl (r:=⟨p.1,p1⟩) (s:=⟨p.2,p2⟩) (by rw [bit_W]; exact t1) (by rw [bit_W]; exact t2)
    obtain ⟨x,rfl,hx⟩ := all v (List.mem_toFinset.mp hv)
    rw [bit_W] at hp hn
    simp only [same,cond_false,Bool.or_eq_true,Bool.not_eq_true'] at hx
    rcases hx with hx | hx
    · rw [hx] at hp; exact Bool.noConfusion hp
    · rw [hx] at hn; exact Bool.noConfusion hn
  · obtain ⟨v,hv,hne⟩ := live_row_difference run (r:=⟨p.1,p1⟩) (s:=⟨p.2,p2⟩) (by rw [bit_W,bit_W,t1,t2]; simp)
    obtain ⟨x,rfl,hx⟩ := all v (List.mem_toFinset.mp hv)
    apply hne
    rw [bit_W,bit_W]
    simpa only [same,cond_true,beq_iff_eq] using hx

-- A tight live set of a monotone run is a formula over distinct leaves, so its
-- leaves own disjoint rectangles of true rows against false rows.
def KWOwn (S : Finset Sig) (T : Sig) (owns : Sig → Row → Row → Prop) : Prop :=
  (∀ p n, bit p T = true → bit n T = false → ∃ v, owns v p n) ∧
  (∀ v p n, owns v p n → v ∈ S ∧ bit p v = true ∧ bit n v = false) ∧
  (∀ v w p n, owns v p n → owns w p n → v = w) ∧
  (∀ v p n p' n', owns v p n → owns v p' n' → owns v p n')
abbrev KWRooms (S : Finset Sig) (T : Sig) := {o : Sig → Row → Row → Prop // KWOwn S T o}
def KWRooms.owns {S T} (H : KWRooms S T) : Sig → Row → Row → Prop := H.1
theorem KWRooms.total {S T} (H : KWRooms S T) : ∀ p n, bit p T = true → bit n T = false → ∃ v, H.owns v p n := H.2.1
theorem KWRooms.valid {S T} (H : KWRooms S T) {v p n} : H.owns v p n → v ∈ S ∧ bit p v = true ∧ bit n v = false := H.2.2.1 v p n
theorem KWRooms.unique {S T} (H : KWRooms S T) {v w p n} : H.owns v p n → H.owns w p n → v = w := H.2.2.2.1 v w p n
theorem KWRooms.rect {S T} (H : KWRooms S T) {v p n p' n'} : H.owns v p n → H.owns v p' n' → H.owns v p n' := H.2.2.2.2 v p n p' n'
theorem kwLeaf (T : Sig) : Nonempty (KWRooms {T} T) := by
  refine ⟨⟨fun v p n => v = T ∧ bit p T = true ∧ bit n T = false,?_,?_,?_,?_⟩⟩
  · intro p n hp hn
    exact ⟨T,rfl,hp,hn⟩
  · rintro v p n ⟨rfl,hp,hn⟩
    exact ⟨by simp,hp,hn⟩
  · rintro v w p n ⟨rfl,_⟩ ⟨rfl,_⟩
    rfl
  · rintro v p n p' n' ⟨rfl,hp,_⟩ ⟨_,_,hn⟩
    exact ⟨rfl,hp,hn⟩
theorem kwFork {T : Sig} {U : Finset Sig} {a b : Sig} {d : Nat} (d01 : d=0 ∨ d=1) (hab : a ≠ b) (ha : a ∉ U) (hb : b ∉ U)
    (hz : bin d a b ∉ U) (H : KWRooms (insert (bin d a b) U) T) : Nonempty (KWRooms (insert a (insert b U)) T) := by
  classical
  let z := bin d a b
  let own : Sig → Row → Row → Prop := fun v p n => (v ∈ U ∧ H.owns v p n) ∨
    (H.owns z p n ∧ v = (if d=0 then (if bit n a = false then a else b) else (if bit p a = true then a else b)))
  have pickU : ∀ (p n : Row), (if d=0 then (if bit n a = false then a else b) else (if bit p a = true then a else b)) ∉ U := by
    intro p n
    split <;> split <;> assumption
  refine ⟨⟨own,?_,?_,?_,?_⟩⟩
  · intro p n hp hn
    obtain ⟨v,hv⟩ := H.total p n hp hn
    rcases Finset.mem_insert.mp (H.valid hv).1 with e | hm
    · refine ⟨_,Or.inr ⟨?_,rfl⟩⟩
      rw [show v = z from e] at hv
      exact hv
    · exact ⟨v,Or.inl ⟨hm,hv⟩⟩
  · intro v p n h
    rcases h with ⟨hm,hv⟩ | ⟨hv,rfl⟩
    · exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm),(H.valid hv).2⟩
    · obtain ⟨_,hp,hn⟩ := H.valid hv
      change bit p (bin d a b) = true at hp
      change bit n (bin d a b) = false at hn
      rw [bit_bin] at hp hn
      rcases d01 with rfl | rfl
      · cases pa : bit p a <;> cases na : bit n a <;> cases pb : bit p b <;> cases nb' : bit n b <;> simp_all
      · cases pa : bit p a <;> cases na : bit n a <;> cases pb : bit p b <;> cases nb' : bit n b <;> simp_all
  · intro v w p n h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨hv,rfl⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨hw,rfl⟩
    · exact H.unique hv hw
    · exact absurd (show z ∈ U by rw [←H.unique hv hw]; exact vU) hz
    · exact absurd (show z ∈ U by rw [←H.unique hw hv]; exact wU) hz
    · rfl
  · intro v p n p' n' h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨hv,e1⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨hw,e2⟩
    · exact Or.inl ⟨vU,H.rect hv hw⟩
    · exact absurd (e2 ▸ vU) (pickU p' n')
    · exact absurd (e1 ▸ wU) (pickU p n)
    · refine Or.inr ⟨H.rect hv hw,?_⟩
      by_cases h : d=0
      · rw [if_pos h] at e2 ⊢
        exact e2
      · rw [if_neg h] at e1 ⊢
        exact e1
theorem kwTight {T : Sig} {k : Nat} {S : Finset Sig} (run : Live false T k S) (tight : S.card=k+1) :
    Nonempty (KWRooms S T) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,_⟩ := run
    exact kwLeaf T
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,_,_,hab,hfresh,tail⟩ := run
    have fresh : bin d a b ∉ U := fun h => hfresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have li := live_size tail
    rw [Finset.card_insert_of_notMem fresh] at li
    have le1 := Finset.card_insert_le a (insert b U)
    have le2 := Finset.card_insert_le b U
    have ha : a ∉ U := by
      intro h
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem h : a ∈ insert b U)] at tight
      omega
    have hb : b ∉ U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight le1
      omega
    have eq : (insert (bin d a b) U).card=k+1 := by
      rw [Finset.card_insert_of_notMem fresh]
      omega
    obtain ⟨H⟩ := ih tail eq
    have d01 : d=0 ∨ d=1 := by
      rcases hd with h | ⟨h,_⟩
      · omega
      · exact Bool.noConfusion h
    exact kwFork d01 hab ha hb fresh H
def only (l : List Nat) (p n a : Nat) : Bool :=
  Nat.blt p 256 && Nat.blt n 256 && l.all (fun x => !(Nat.testBit x p) || Nat.testBit x n || Nat.beq x a)
abbrev KwD := Nat × Nat × Nat × Nat × Nat × Nat
def findW (l : List Nat) (p n : Nat) : Nat := (l.find? (fun x => Nat.testBit x p && !(Nat.testBit x n))).getD 0
def kwOK (T : Nat) (q : KwD) : Bool :=
  T.testBit q.1 && T.testBit q.2.2.2.1 && T.testBit q.2.2.2.2.2 && !(T.testBit q.2.1) && !(T.testBit q.2.2.1) && !(T.testBit q.2.2.2.2.1)
def kwList (l : List Nat) (q : KwD) : Bool :=
  let a := findW l q.1 q.2.2.1
  let b := findW l q.1 q.2.2.2.2.1
  only l q.1 q.2.2.1 a && only l q.2.2.2.1 q.2.1 a &&
  (bif Nat.beq q.1 q.2.2.2.2.2 && Nat.beq q.2.1 q.2.2.2.2.1 then !(Nat.testBit a q.1 && !(Nat.testBit a q.2.1))
   else only l q.1 q.2.2.2.2.1 b && only l q.2.2.2.2.2 q.2.1 b && !(Nat.beq a b))
theorem only_own {l : List Nat} {T p n a : Nat} (H : KWRooms ((l.map W).toFinset) (W T))
    (h : only l p n a = true) (tp : T.testBit p = true) (tn : T.testBit n = false) :
    ∃ (hp : p < 256) (hn : n < 256), H.owns (W a) ⟨p,hp⟩ ⟨n,hn⟩ := by
  simp only [only,Bool.and_eq_true,Nat.blt_eq,List.all_eq_true,Bool.or_eq_true,Bool.not_eq_true'] at h
  obtain ⟨⟨hp,hn⟩,hl⟩ := h
  refine ⟨hp,hn,?_⟩
  obtain ⟨v,hv⟩ := H.total ⟨p,hp⟩ ⟨n,hn⟩ (by rw [bit_W]; exact tp) (by rw [bit_W]; exact tn)
  obtain ⟨hm,h1,h2⟩ := H.valid hv
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hm)
  rw [bit_W] at h1 h2
  rcases hl x hx with (h | h) | h
  · rw [h] at h1; exact Bool.noConfusion h1
  · rw [h] at h2; exact Bool.noConfusion h2
  · rw [Nat.eq_of_beq_eq_true h] at hv
    exact hv
set_option maxRecDepth 8192 in
theorem kw_sound {T k : Nat} {l : List Nat} (nd : (l.map W).Nodup) (size : l.length = k+1) (lt : ∀ x ∈ l, x < 2^256) (q : KwD)
    (hT : kwOK T q = true) (h : kwList l q = true) : Impossible false (W T) k (l.map W).toFinset := by
  intro k' hk run
  have lb := live_size run
  rw [List.toFinset_card_of_nodup nd,List.length_map] at lb
  obtain ⟨H⟩ := kwTight run (by rw [List.toFinset_card_of_nodup nd,List.length_map]; omega)
  simp only [kwOK,Bool.and_eq_true,Bool.not_eq_true'] at hT
  obtain ⟨⟨⟨⟨⟨t1,t2⟩,t3⟩,t4⟩,t5⟩,t6⟩ := hT
  simp only [kwList,Bool.and_eq_true] at h
  obtain ⟨⟨h1,h2⟩,h3⟩ := h
  obtain ⟨hp,hna,o1⟩ := only_own H h1 t1 t5
  obtain ⟨hpa,hn,o2⟩ := only_own H h2 t2 t4
  have own := H.rect o1 o2
  cases hc : (Nat.beq q.1 q.2.2.2.2.2 && Nat.beq q.2.1 q.2.2.2.2.1)
  · rw [hc,cond_false] at h3
    simp only [Bool.and_eq_true,Bool.not_eq_true'] at h3
    obtain ⟨⟨h4,h5⟩,h6⟩ := h3
    obtain ⟨_,hnb,o3⟩ := only_own H h4 t1 t6
    obtain ⟨hpb,_,o4⟩ := only_own H h5 t3 t4
    have own' := H.rect o3 o4
    have ee := H.unique own own'
    have mem : ∀ {a : Nat}, W a ∈ (l.map W).toFinset → ∃ x ∈ l, W x = W a := by
      intro a ha
      obtain ⟨x,hx,e⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
      exact ⟨x,hx,e⟩
    have fw : ∀ p n, findW l p n < 2^256 := by
      intro p n
      unfold findW
      cases hf : l.find? (fun x => Nat.testBit x p && !(Nat.testBit x n)) with
      | none => exact Nat.two_pow_pos 256
      | some x => exact lt x (List.mem_of_find?_eq_some hf)
    have := W_inj (fw _ _) (fw _ _) ee
    rw [this,Nat.beq_refl] at h6
    exact Bool.noConfusion h6
  · rw [hc,cond_true] at h3
    have v := (H.valid own).2
    rw [bit_W,bit_W] at v
    rw [v.1,v.2] at h3
    exact Bool.noConfusion h3

-- Symmetry: exchanging neighbouring input variables.
def hiM : Nat → Nat
  | 0 => 0x2222222222222222222222222222222222222222222222222222222222222222
  | 1 => 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
  | 2 => 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0
  | 3 => 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00
  | 4 => 0xffff000000000000ffff000000000000ffff000000000000ffff0000
  | 5 => 0xffffffff000000000000000000000000ffffffff00000000
  | _ => 0xffffffffffffffff0000000000000000
def loM : Nat → Nat
  | 0 => 0x4444444444444444444444444444444444444444444444444444444444444444
  | 1 => 0x3030303030303030303030303030303030303030303030303030303030303030
  | 2 => 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00
  | 3 => 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000
  | 4 => 0xffff000000000000ffff000000000000ffff000000000000ffff00000000
  | 5 => 0xffffffff000000000000000000000000ffffffff0000000000000000
  | _ => 0xffffffffffffffff00000000000000000000000000000000
def keM : Nat → Nat
  | 0 => 0x9999999999999999999999999999999999999999999999999999999999999999
  | 1 => 0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3
  | 2 => 0xf00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f
  | 3 => 0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff
  | 4 => 0xffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffff
  | 5 => 0xffffffff0000000000000000ffffffffffffffff0000000000000000ffffffff
  | _ => 0xffffffffffffffff00000000000000000000000000000000ffffffffffffffff
def shM : Nat → Nat
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 8
  | 4 => 16
  | 5 => 32
  | _ => 64
def swapN (i v : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.land v (keM i)) (Nat.shiftLeft (Nat.land v (hiM i)) (shM i))) (Nat.shiftRight (Nat.land v (loM i)) (shM i))
def sig (i : Nat) (r : Row) : Row :=
  if (hiM i).testBit r.val then Fin.ofNat 256 (r.val + shM i) else
    if (loM i).testBit r.val then Fin.ofNat 256 (r.val - shM i) else r
def swapFacts (i : Nat) (r : Row) : Prop :=
  ((keM i).testBit r.val = true ∧ (sig i r).val = r.val ∧ (decide (shM i ≤ r.val) && (hiM i).testBit (r.val - shM i)) = false ∧ (loM i).testBit (shM i + r.val) = false) ∨
  ((keM i).testBit r.val = false ∧ shM i ≤ r.val ∧ (sig i r).val = r.val - shM i ∧ (hiM i).testBit (r.val - shM i) = true ∧ (loM i).testBit (shM i + r.val) = false) ∨
  ((keM i).testBit r.val = false ∧ (sig i r).val = shM i + r.val ∧ (decide (shM i ≤ r.val) && (hiM i).testBit (r.val - shM i)) = false ∧ (loM i).testBit (shM i + r.val) = true)
theorem swap_facts : ∀ (i : Fin 7) (r : Row), swapFacts i.val r ∧ sig i.val (sig i.val r) = r := by
  unfold swapFacts
  decide +kernel
theorem swap_ok (i : Nat) (hi : i < 7) (v : Nat) : W (swapN i v) = rename (sig i) (W v) := by
  apply bit_ext
  intro r
  rw [bit_W,bit_rename,bit_W]
  have e : (swapN i v).testBit r.val = (((v.testBit r.val && (keM i).testBit r.val) ||
      (decide (shM i ≤ r.val) && (v.testBit (r.val - shM i) && (hiM i).testBit (r.val - shM i)))) ||
      (v.testBit (shM i + r.val) && (loM i).testBit (shM i + r.val))) := by
    have s1 : (Nat.shiftLeft (Nat.land v (hiM i)) (shM i)).testBit r.val = (decide (shM i ≤ r.val) && (Nat.land v (hiM i)).testBit (r.val - shM i)) := by
      exact Nat.testBit_shiftLeft ..
    have s2 : (Nat.shiftRight (Nat.land v (loM i)) (shM i)).testBit r.val = (Nat.land v (loM i)).testBit (shM i + r.val) := by
      exact Nat.testBit_shiftRight ..
    unfold swapN
    rw [tb_lor,tb_lor,s1,s2,tb_land,tb_land,tb_land]
  rw [e]
  rcases (swap_facts ⟨i,hi⟩ r).1 with ⟨h1,h2,h3,h4⟩ | ⟨h1,h2,h3,h4,h5⟩ | ⟨h1,h2,h3,h4⟩
  · change (sig i r).val = r.val at h2
    rw [h2]
    simp only [] at h1 h3 h4
    rw [h1,h4]
    cases hd : decide (shM i ≤ r.val)
    · simp
    · rw [hd,Bool.true_and] at h3
      rw [h3]; simp
  · change (sig i r).val = r.val - shM i at h3
    rw [h3]
    simp only [] at h1 h2 h4 h5
    rw [h1,h4,h5,decide_eq_true h2]
    simp
  · change (sig i r).val = shM i + r.val at h2
    rw [h2]
    simp only [] at h1 h3 h4
    rw [h1,h4]
    cases hd : decide (shM i ≤ r.val)
    · simp
    · rw [hd,Bool.true_and] at h3
      rw [h3]; simp
def permN (l : List Nat) (v : Nat) : Nat := l.foldl (fun v i => swapN i v) v
def symOK (T : Nat) (l : List Nat) : Bool := l.all fun i => Nat.blt i 7 && Nat.beq (swapN i T) T
theorem perm_sound {u T k} (l : List Nat) (hT : symOK T l = true) (s : List Nat)
    (h : Impossible u (W T) k ((s.map (permN l)).map W).toFinset) : Impossible u (W T) k (s.map W).toFinset := by
  induction l generalizing s with
  | nil =>
    simpa [show (permN [] : Nat → Nat) = id from rfl] using h
  | cons i l ih =>
    simp only [symOK,List.all_cons,Bool.and_eq_true,Nat.blt_eq] at hT
    obtain ⟨⟨hi,hs⟩,hl⟩ := hT
    have h' : Impossible u (W T) k ((s.map (swapN i)).map W).toFinset := by
      apply ih hl
      have : (s.map (swapN i)).map (permN l) = s.map (permN (i::l)) := by
        rw [List.map_map]
        rfl
      rw [this]
      exact h
    intro k' hk run
    have onto : Function.Surjective (sig i) := fun r => ⟨sig i r,(swap_facts ⟨i,hi⟩ r).2⟩
    have r2 := live_rename run (sig i) onto
    rw [←swap_ok i hi T,Nat.eq_of_beq_eq_true hs] at r2
    apply h' k' hk
    have : ((s.map (swapN i)).map W).toFinset = (s.map W).toFinset.image (rename (sig i)) := by
      ext v
      simp only [List.mem_toFinset,List.mem_map,Finset.mem_image,exists_exists_and_eq_and,swap_ok i hi]
    rw [this]
    exact r2

abbrev StD := List Nat × List Nat × List Nat
def pick : List Nat → Nat → List Nat
  | [],_ => []
  | x::xs,m => bif Nat.beq (Nat.mod m 2) 1 then x :: pick xs (Nat.div m 2) else pick xs (Nat.div m 2)
def picks : List Nat → List (Nat × List Nat)
  | [] => []
  | x::xs => (x,xs) :: (picks xs).map fun p => (p.1,x::p.2)
def pairs : List Nat → List (Nat × Nat × List Nat)
  | [] => []
  | x::xs => ((picks xs).map fun p => (x,p.1,p.2)) ++ (pairs xs).map fun p => (p.1,p.2.1,x::p.2.2)
theorem picks_ok {l : List Nat} {a : Nat} (h : a ∈ l) : ∃ p ∈ picks l, p.1 = a ∧ (a::p.2).Perm l := by
  induction l with
  | nil => cases h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨(a,xs),by simp [picks],rfl,List.Perm.refl _⟩
    · obtain ⟨p,hp,rfl,q⟩ := ih h
      refine ⟨(p.1,x::p.2),?_,rfl,?_⟩
      · simp only [picks,List.mem_cons,List.mem_map]
        exact Or.inr ⟨p,hp,rfl⟩
      · exact (List.Perm.swap x p.1 p.2).trans (q.cons x)
theorem pairs_ok {l : List Nat} {a b : Nat} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) :
    ∃ p ∈ pairs l, (p.1::p.2.1::p.2.2).Perm l ∧ ((p.1 = a ∧ p.2.1 = b) ∨ (p.1 = b ∧ p.2.1 = a)) := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    have first (c : Nat) (hc : c ∈ xs) : ∃ p ∈ pairs (x::xs), (p.1::p.2.1::p.2.2).Perm (x::xs) ∧ p.1 = x ∧ p.2.1 = c := by
      obtain ⟨p,hp,rfl,q⟩ := picks_ok hc
      refine ⟨(x,p.1,p.2),?_,q.cons x,rfl,rfl⟩
      simp only [pairs,List.mem_append,List.mem_map]
      exact Or.inl ⟨p,hp,rfl⟩
    rcases List.mem_cons.mp ha with rfl | ha2
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact absurd rfl hab
      · obtain ⟨p,h1,h2,h3,h4⟩ := first b hb
        exact ⟨p,h1,h2,Or.inl ⟨h3,h4⟩⟩
    · rcases List.mem_cons.mp hb with e | hb
      · subst e
        obtain ⟨p,h1,h2,h3,h4⟩ := first a ha2
        exact ⟨p,h1,h2,Or.inr ⟨h3,h4⟩⟩
      · obtain ⟨p,hp,q,e⟩ := ih ha2 hb
        refine ⟨(p.1,p.2.1,x::p.2.2),?_,?_,e⟩
        · simp only [pairs,List.mem_append,List.mem_map]
          exact Or.inr ⟨p,hp,rfl⟩
        · exact ((List.Perm.swap x p.2.1 p.2.2).cons p.1).trans ((List.Perm.swap x p.1 _).trans (q.cons x))

def mem1 (z : Nat) (l : List Nat) : Bool := l.any fun x => Nat.beq x z
def beqL : List Nat → List Nat → Bool
  | [],[] => true
  | x::xs,y::ys => Nat.beq x y && beqL xs ys
  | _,_ => false
theorem beqL_ok {a b : List Nat} (h : beqL a b = true) : a = b := by
  induction a generalizing b with
  | nil => cases b with
    | nil => rfl
    | cons => simp [beqL] at h
  | cons x xs ih => cases b with
    | nil => simp [beqL] at h
    | cons y ys =>
      simp only [beqL,Bool.and_eq_true] at h
      rw [Nat.eq_of_beq_eq_true h.1,ih h.2]
def ins (z : Nat) : List Nat → List Nat
  | [] => [z]
  | x::xs => bif Nat.ble z x then z::x::xs else x :: ins z xs
theorem mem_ins {z v : Nat} {l : List Nat} : v ∈ ins z l ↔ v = z ∨ v ∈ l := by
  induction l with
  | nil => simp [ins]
  | cons x xs ih =>
    unfold ins
    cases Nat.ble z x
    · simp only [cond_false,List.mem_cons,ih]
      tauto
    · simp
def kidN (rest : List Nat) (a b z : Nat) (ka kb : Bool) : List Nat :=
  ins z (bif ka then ins a (bif kb then ins b rest else rest) else bif kb then ins b rest else rest)
theorem kid_fin (rest : List Nat) (a b z : Nat) (ka kb : Bool) :
    ((kidN rest a b z ka kb).map W).toFinset = (kidW rest a b z ka kb).toFinset := by
  ext v
  cases ka <;> cases kb <;> simp [kidN,kidW,kept,mem_ins] <;> aesop

def keeps : List (Bool × Bool) := [(true,true),(true,false),(false,true),(false,false)]
def bl (b : Bool) : Nat := bif b then 1 else 0
def mkCut (u : Bool) (Z : List SliceD) (c : Nat × List Nat) : CutV :=
  let s := Z.getD c.1 (0,0,[])
  (s.1,s.2.1,c.2.length,mkPool u (initPool s.1 s.2.2) c.2)
abbrev Tabs := List CutV × List (Nat × Nat) × List KwD × List (List Nat)
def Tabs.cuts (t : Tabs) : List CutV := t.1
def Tabs.seps (t : Tabs) : List (Nat × Nat) := t.2.1
def Tabs.kws (t : Tabs) : List KwD := t.2.2.1
def Tabs.perms (t : Tabs) : List (List Nat) := t.2.2.2
def sortN (l : List Nat) : List Nat := l.foldr ins []
theorem mem_sortN {v : Nat} {l : List Nat} : v ∈ sortN l ↔ v ∈ l := by
  induction l with
  | nil => simp [sortN]
  | cons x xs ih =>
    change v ∈ ins x (sortN xs) ↔ _
    rw [mem_ins,ih]
    simp
def ty (i n : Nat) : Bool := Nat.beq (Nat.mod i 4) n
def hintOK (u : Bool) (k : Nat) (next : List (List Nat)) (t : Tabs) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (i : Nat) : Bool :=
  bif ty i 0 then (match t.cuts[Nat.div i 4]? with
    | some c => cutEval u k rest a b z ka kb c
    | none => false)
  else bif ty i 1 then (match t.seps[Nat.div i 4]? with
    | some q => sepEval u rest a b z ka kb q
    | none => false)
  else bif ty i 2 then (match t.kws[Nat.div i 4]? with
    | some q => !u && Nat.beq (kidN rest a b z ka kb).length (k+1) && kwList (kidN rest a b z ka kb) q
    | none => false)
  else (match t.perms[Nat.div i 4]? with
    | some l => next.any (beqL (sortN ((kidN rest a b z ka kb).map (permN l))))
    | none => false)
def kidOK (u : Bool) (k : Nat) (next : List (List Nat)) (t : Tabs) (rest : List Nat) (hints : List Nat)
    (a b z : Nat) (kk : Bool × Bool) : Bool :=
  Nat.blt k (Nat.add (Nat.add rest.length (Nat.add (bl kk.1) (bl kk.2))) 0) ||
  hints.any (hintOK u k next t rest a b z kk.1 kk.2)
def opsOf (u : Bool) : List Nat := bif u then [0,1,2,3] else [0,1]
def pairOK (u : Bool) (k : Nat) (next : List (List Nat)) (t : Tabs) (s : List Nat)
    (p : Nat × Nat × List Nat) (hints : List Nat) : Bool :=
  (opsOf u).all fun o =>
    let z := nb o p.1 p.2.1
    mem1 z s || Nat.beq z 0 || Nat.beq z full ||
      keeps.all (kidOK u k next t p.2.2 hints p.1 p.2.1 z)
def allZip (f : Nat × Nat × List Nat → List Nat → Bool) : List (Nat × Nat × List Nat) → List (List Nat) → Bool
  | [],_ => true
  | p::ps,[] => f p [] && allZip f ps []
  | p::ps,h::hs => f p h && allZip f ps hs
theorem allZip_ok {f ps hs} (h : allZip f ps hs = true) : ∀ p ∈ ps, ∃ x, f p x = true := by
  induction ps generalizing hs with
  | nil => intro p hp; cases hp
  | cons q ps ih =>
    intro p hp
    cases hs with
    | nil =>
      simp only [allZip,Bool.and_eq_true] at h
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨_,h.1⟩
      · exact ih h.2 p hp
    | cons x hs =>
      simp only [allZip,Bool.and_eq_true] at h
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨_,h.1⟩
      · exact ih h.2 p hp
def asc : List Nat → Bool
  | [] => true
  | [x] => Nat.blt x (2^256)
  | x::y::l => Nat.blt x y && asc (y::l)
set_option maxRecDepth 8192 in
theorem asc_ok {l : List Nat} (h : asc l = true) : l.Pairwise (· < ·) ∧ ∀ x ∈ l, x < 2^256 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    cases l with
    | nil =>
      simp only [asc,Nat.blt_eq] at h
      simpa using h
    | cons y l =>
      simp only [asc,Bool.and_eq_true,Nat.blt_eq] at h
      obtain ⟨i1,i2⟩ := ih h.2
      have hy := List.pairwise_cons.mp i1
      refine ⟨List.pairwise_cons.mpr ⟨?_,i1⟩,?_⟩
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact h.1
        · exact h.1.trans (hy.1 v hv)
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact h.1.trans (i2 y (by simp))
        · exact i2 v hv
theorem asc_nodup {l : List Nat} (h : asc l = true) : l.Nodup ∧ (l.map W).Nodup := by
  obtain ⟨h1,h2⟩ := asc_ok h
  have nd : l.Nodup := h1.imp (fun h => Nat.ne_of_lt h)
  refine ⟨nd,?_⟩
  refine nd.map_on ?_
  intro x hx y hy e
  exact W_inj (h2 x hx) (h2 y hy) e
def stOK (u : Bool) (T : Nat) (t : Tabs) (k : Nat) (next : List (List Nat)) (st : StD) : Bool :=
  asc st.1 && !(mem1 T st.1) &&
  allZip (pairOK u k next t st.1) (pairs st.1) (st.2.2.map (pick st.2.1))
def levelOK (u : Bool) (T : Nat) (t : Tabs) (k : Nat) (next : List (List Nat)) (D : List StD) : Bool :=
  D.all (stOK u T t k next)
abbrev TabsP (u : Bool) (R : List Nat) (T : Nat) (t : Tabs) : Prop :=
  (∀ c ∈ t.cuts, CutP u R T c) ∧ t.seps.all (sepOK T) = true ∧ t.kws.all (kwOK T) = true ∧ t.perms.all (symOK T) = true
theorem TabsP.c {u R T t} (h : TabsP u R T t) : ∀ c ∈ t.cuts, CutP u R T c := h.1
theorem TabsP.s {u R T t} (h : TabsP u R T t) : t.seps.all (sepOK T) = true := h.2.1
theorem TabsP.k {u R T t} (h : TabsP u R T t) : t.kws.all (kwOK T) = true := h.2.2.1
theorem TabsP.p {u R T t} (h : TabsP u R T t) : t.perms.all (symOK T) = true := h.2.2.2
def LevelN (u : Bool) (T k : Nat) (D : List StD) : Prop :=
  ∀ st ∈ D, Impossible u (W T) k (st.1.map W).toFinset
theorem cutsGood {u R T} {Z : List SliceD} {C : List (Nat × List Nat)} (hZ : ∀ s ∈ Z, SliceN u R T s)
    (hC : C.all (fun c => Nat.blt c.1 Z.length) = true) : ∀ c ∈ C.map (mkCut u Z), CutP u R T c := by
  intro c hc
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hc
  have hi : q.1 < Z.length := by simpa only [Nat.blt_eq] using List.all_eq_true.mp hC q hq
  have hm : Z.getD q.1 (0,0,[]) ∈ Z := by
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]
    exact List.getElem_mem hi
  obtain ⟨⟨f,roots,dom,base,nc,lo⟩,hv⟩ := hZ _ hm
  have ps : PS u f (roots.map observe) (initPool (Z.getD q.1 (0,0,[])).1 (Z.getD q.1 (0,0,[])).2.2) := by
    intro v hv'
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv'
    rw [rf_land dom]
    exact base _ (List.mem_map_of_mem (hv j hj))
  obtain ⟨bank,b1,b2⟩ := mkPool_ok q.2 (Reach.start (u:=u) (roots:=roots.map observe)) ps
  refine ⟨f,roots,bank,dom,nc,?_,b2,lo⟩
  simpa [mkCut] using b1

set_option maxRecDepth 8192 in
theorem stStep {u R T E t k next st} (hB : baseOK T R E = true) (ht : TabsP u R T t)
    (hn : ∀ s ∈ next, Impossible u (W T) k (s.map W).toFinset)
    (h : stOK u T t k next st = true) : Impossible u (W T) (k+1) (st.1.map W).toFinset := by
  have b := baseOK_ok hB
  simp only [stOK,Bool.and_eq_true,Bool.not_eq_true'] at h
  obtain ⟨⟨ha,hT⟩,hz⟩ := h
  obtain ⟨nd,ndW⟩ := asc_nodup ha
  have lt := (asc_ok ha).2
  have hTm : W T ∉ st.1.map W := by
    intro hm
    obtain ⟨x,hx,e⟩ := List.mem_map.mp hm
    have := W_inj (lt x hx) b.lt e
    subst this
    have : mem1 x st.1 = true := List.any_eq_true.mpr ⟨x,hx,Nat.beq_refl x⟩
    rw [hT] at this
    exact Bool.noConfusion this
  apply enum_step ndW hTm
  intro a' ha' b' hb' d hd ka kb hab fresh hprop hlen
  obtain ⟨a,ham,rfl⟩ := List.mem_map.mp ha'
  obtain ⟨c,hcm,rfl⟩ := List.mem_map.mp hb'
  have hac : a ≠ c := fun h => hab (by rw [h])
  have inOps : ∀ {o : Nat}, allowed u o → o ∈ opsOf u := by
    intro o h
    cases u
    · rcases h with h | ⟨h,_⟩
      · have : o = 0 ∨ o = 1 := by omega
        simpa [opsOf] using this
      · exact Bool.noConfusion h
    · have : o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 3 := by rcases h with h | ⟨_,h⟩ <;> omega
      simpa [opsOf] using this
  have opk : ∀ {o : Nat}, allowed u o → opOK u o = true := by
    intro o h
    cases u
    · rcases h with h | ⟨h,_⟩
      · simpa only [opOK,Bool.false_or,Nat.blt_eq] using h
      · exact Bool.noConfusion h
    · rfl
  obtain ⟨p,hp,perm,ho⟩ := pairs_ok ham hcm hac
  obtain ⟨x,hx⟩ := allZip_ok hz p hp
  -- one unordered pair serves both orders
  have core : ∀ (o : Nat) (ja jb : Bool), allowed u o → W (nb o p.1 p.2.1) = bin d (W a) (W c) →
      (p.2.2.length + (bl ja + bl jb) ≤ k) →
      Impossible u (W T) k (kidW p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).toFinset := by
    intro o ja jb ho4 hW hl
    have hf := List.all_eq_true.mp hx o (inOps ho4)
    simp only [Bool.or_eq_true] at hf
    have pm (v : Nat) : v ∈ st.1 ↔ v = p.1 ∨ v = p.2.1 ∨ v ∈ p.2.2 := by
      rw [←perm.mem_iff]
      simp
    rcases hf with ((hf | hf) | hf) | hf
    · exfalso
      obtain ⟨y,hy,e⟩ := List.any_eq_true.mp hf
      apply fresh
      rw [←hW,←Nat.eq_of_beq_eq_true e]
      exact List.mem_map_of_mem hy
    · exfalso
      apply hprop.1
      rw [←hW,Nat.eq_of_beq_eq_true hf]
      rfl
    · exfalso
      apply hprop.2
      rw [←hW,Nat.eq_of_beq_eq_true hf]
      exact W_full
    have hk := List.all_eq_true.mp hf (ja,jb) (by cases ja <;> cases jb <;> simp [keeps])
    simp only [kidOK,Bool.or_eq_true] at hk
    have ndp : ((p.1::p.2.1::p.2.2).map W).Nodup := (perm.map W).nodup_iff.mpr ndW
    simp only [List.map_cons,List.nodup_cons,List.mem_cons,not_or] at ndp
    have nk : (kidW p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).Nodup := by
      have n1 := kept_nd jb (W p.2.1) _ ndp.2.2 ndp.2.1
      have n2 : W p.1 ∉ kept jb (W p.2.1) (p.2.2.map W) := by
        cases jb
        · exact ndp.1.2
        · simp only [kept,if_true,List.mem_cons,not_or]
          exact ndp.1
      refine List.nodup_cons.mpr ⟨?_,kept_nd ja _ _ n1 n2⟩
      intro hm
      apply fresh
      rw [←hW]
      have sub : W (nb o p.1 p.2.1) ∈ (p.1::p.2.1::p.2.2).map W := by
        rcases mem_kept hm with h | h
        · rw [h]; simp
        · rcases mem_kept h with h | h
          · rw [h]; simp
          · simp [h]
      exact (perm.map W).mem_iff.mp sub
    rcases hk with hk | hk
    · exfalso
      rw [Nat.blt_eq] at hk
      have : k < p.2.2.length + (bl ja + bl jb) + 0 := hk
      omega
    · obtain ⟨i,_,hi⟩ := List.any_eq_true.mp hk
      unfold hintOK at hi
      have sub : ∀ x ∈ kidN p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb, x < 2^256 := by
        intro x hx
        have hx' : x = nb o p.1 p.2.1 ∨ x ∈ st.1 := by
          unfold kidN at hx
          rw [mem_ins] at hx
          rcases hx with hx | hx
          · exact Or.inl hx
          · right
            rw [pm]
            cases ja <;> cases jb <;> simp only [cond_true,cond_false,mem_ins] at hx <;> tauto
        rcases hx' with rfl | hx'
        · have l1 : p.1 < 2^256 := lt _ ((pm _).mpr (Or.inl rfl))
          have l2 : p.2.1 < 2^256 := lt _ ((pm _).mpr (Or.inr (Or.inl rfl)))
          have la : Nat.land p.1 p.2.1 < 2^256 := Nat.lt_of_le_of_lt (Nat.and_le_left) l1
          unfold nb
          cases Nat.beq o 0 <;> cases Nat.beq o 1 <;> cases Nat.beq o 2 <;>
            first | exact la | exact Nat.or_lt_two_pow l1 l2 | exact Nat.xor_lt_two_pow l1 la | exact Nat.xor_lt_two_pow l2 la
        · exact lt x hx'
      cases h1 : ty i 0
      · rw [h1,cond_false] at hi
        cases h2 : ty i 1
        · rw [h2,cond_false] at hi
          cases h3 : ty i 2
          · rw [h3,cond_false] at hi
            cases hg : t.perms[Nat.div i 4]? with
            | none => rw [hg] at hi; exact Bool.noConfusion hi
            | some l =>
              rw [hg] at hi
              obtain ⟨s,hs',e⟩ := List.any_eq_true.mp hi
              rw [←kid_fin]
              apply perm_sound l (List.all_eq_true.mp ht.p l (List.mem_of_getElem? hg))
              have : (((kidN p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).map (permN l)).map W).toFinset = (s.map W).toFinset := by
                rw [←beqL_ok e]
                ext v
                simp only [List.mem_toFinset,List.mem_map,mem_sortN]
              rw [this]
              exact hn s hs'
          · rw [h3,cond_true] at hi
            cases hg : t.kws[Nat.div i 4]? with
            | none => rw [hg] at hi; exact Bool.noConfusion hi
            | some q =>
              rw [hg] at hi
              simp only [Bool.and_eq_true,Bool.not_eq_true'] at hi
              obtain ⟨⟨hu,hlen⟩,hkw⟩ := hi
              rw [←kid_fin]
              have sz := Nat.eq_of_beq_eq_true hlen
              have nd' : ((kidN p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).map W).Nodup := by
                apply List.dedup_eq_self.mp
                apply (List.dedup_sublist _).eq_of_length
                have c1 : ((kidN p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).map W).toFinset.card = (kidW p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).length := by
                  rw [kid_fin,List.toFinset_card_of_nodup nk]
                rw [List.card_toFinset] at c1
                rw [c1,List.length_map]
                have il : ∀ (z : Nat) (l : List Nat), (ins z l).length = l.length + 1 := by
                  intro z l
                  induction l with
                  | nil => rfl
                  | cons x xs ih =>
                    unfold ins
                    cases Nat.ble z x
                    · rw [cond_false,List.length_cons,ih,List.length_cons]
                    · rfl
                unfold kidN kidW
                cases ja <;> cases jb <;> simp [kept,il]
              subst hu
              exact kw_sound nd' sz sub q (List.all_eq_true.mp ht.k q (List.mem_of_getElem? hg)) hkw
        · rw [h2,cond_true] at hi
          cases hg : t.seps[Nat.div i 4]? with
          | none => rw [hg] at hi; exact Bool.noConfusion hi
          | some q =>
            rw [hg] at hi
            exact sep_sound (List.all_eq_true.mp ht.s q (List.mem_of_getElem? hg)) hi
      · rw [h1,cond_true] at hi
        cases hg : t.cuts[Nat.div i 4]? with
        | none => rw [hg] at hi; exact Bool.noConfusion hi
        | some q =>
          rw [hg] at hi
          exact cut_sound (ht.c q (List.mem_of_getElem? hg)) (opk ho4) nk hi
  have rp : (((st.1.map W).erase (W a)).erase (W c)).Perm (p.2.2.map W) := by
    have e : (W a :: W c :: p.2.2.map W).Perm (st.1.map W) := by
      rcases ho with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact perm.map W
      · exact (List.Perm.swap _ _ _).trans (perm.map W)
    have e1 := e.erase (W a)
    rw [List.erase_cons_head] at e1
    have e2 := e1.erase (W c)
    rw [List.erase_cons_head] at e2
    exact e2.symm
  have lenr : (((st.1.map W).erase (W a)).erase (W c)).length = p.2.2.length := by
    rw [rp.length_eq,List.length_map]
  have fits : p.2.2.length + (bl ka + bl kb) ≤ k := by
    have h := hlen
    unfold childTwo at h
    cases ka <;> cases kb <;> simp [kept,lenr] at h <;> simp [bl] <;> omega
  rw [Nat.add_sub_cancel]
  rcases ho with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · have r := core d ka kb hd (W_nb _ _ _) fits
    have e : (childTwo (st.1.map W) (W p.1) (W p.2.1) d ka kb).toFinset = (kidW p.2.2 p.1 p.2.1 (nb d p.1 p.2.1) ka kb).toFinset := by
      unfold childTwo kidW
      rw [W_nb]
      ext v
      cases ka <;> cases kb <;> simp [kept,rp.mem_iff]
    rw [e]
    exact r
  · have hfl := flip_flip hd
    have r := core (flipOp d) kb ka hfl.1 (by rw [W_nb]; exact (bin_flip hd _ _).symm) (by omega)
    have e : (childTwo (st.1.map W) (W p.2.1) (W p.1) d ka kb).toFinset = (kidW p.2.2 p.1 p.2.1 (nb (flipOp d) p.1 p.2.1) kb ka).toFinset := by
      unfold childTwo kidW
      rw [W_nb,bin_flip hd]
      ext v
      cases ka <;> cases kb <;> simp [kept,rp.mem_iff] <;> tauto
    rw [e]
    exact r

theorem levelStep {u R T E t k D' D} (hB : baseOK T R E = true) (ht : TabsP u R T t)
    (hI : LevelN u T k D') (h : levelOK u T t k (D'.map Prod.fst) D = true) : LevelN u T (k+1) D := by
  intro st hst
  refine stStep hB ht ?_ (List.all_eq_true.mp h st hst)
  intro s hs
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hs
  exact hI q hq
theorem chunks {u : Bool} {T : Nat} {t : Tabs} {k : Nat} {next : List (List Nat)} (c : Nat) (D : List StD) (n : Nat) (hc : 0 < c)
    (hl : Nat.ble D.length (n*c) = true)
    (h : ∀ i, i < n → levelOK u T t k next ((D.drop (i*c)).take c) = true) : levelOK u T t k next D = true := by
  rw [levelOK,List.all_eq_true]
  intro x hx
  obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hx
  have hl' := Nat.le_of_ble_eq_true hl
  have hi : j / c < n := by
    rw [Nat.div_lt_iff_lt_mul hc]
    omega
  refine List.all_eq_true.mp (h _ hi) _ ?_
  have hm : j / c * c + j % c = j := by rw [Nat.mul_comm]; exact Nat.div_add_mod j c
  have hmod := Nat.mod_lt j hc
  refine List.mem_of_getElem? (i := j % c) ?_
  rw [List.getElem?_take_of_lt hmod,List.getElem?_drop,hm]
  exact List.getElem?_eq_getElem hj
theorem lowSearch {u R T E K D} (hB : baseOK T R E = true) (hI : LevelN u T K D)
    (h : (D.map Prod.fst).contains (R.map xN) = true) : LowN u R T (K+1) := by
  apply lowOf hB
  simp only [List.contains_eq_mem,decide_eq_true_eq] at h
  obtain ⟨q,hq,e⟩ := List.mem_map.mp h
  have := hI q hq
  rw [e] at this
  simpa only [rootsW,List.map_map,Function.comp_def] using this


def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 2, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[
    ⟨.or, [5, 6]⟩,
    ⟨.or, [0, 6]⟩,
    ⟨.or, [0, 2]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.or, [2, 9]⟩,
    ⟨.or, [4, 12]⟩,
    ⟨.and, [3, 9]⟩,
    ⟨.and, [10, 8]⟩,
    ⟨.and, [13, 7]⟩,
    ⟨.and, [1, 11]⟩,
    ⟨.or, [14, 15]⟩,
    ⟨.or, [18, 16]⟩,
    ⟨.or, [19, 17]⟩], 20⟩
theorem witnessMonotone : ∀ g ∈ smallCircuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [smallCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 8 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
  decide +kernel
theorem witnessSize : smallCircuit.gates.length = 13 := rfl
def pw0 : Nat := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
def pw1 : Nat := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
def pw2 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def pw3 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def pw4 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00
def pw5 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
def pw6 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def pw7 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def pw8 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def pw9 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def pw10 : Nat := 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc
def pw11 : Nat := 0xfc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc
def pw12 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def pw13 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def pw14 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def pw15 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def pw16 : Nat := 0x5555555500000000555555550000000055555555000000005555555500000000
def pw17 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def pw18 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def pw19 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def pw20 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000
def pw21 : Nat := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
def pw22 : Nat := 0x4444444444444444444444444444444444444444444444444444444444444444
def pw23 : Nat := 0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa
def pw24 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa
def pw25 : Nat := 0x5500550055005500550055005500550055005500550055005500550055005500
def pw26 : Nat := 0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa
def pw27 : Nat := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
def pw28 : Nat := 0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc
def pw29 : Nat := 0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc
def pw30 : Nat := 0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc
def pw31 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0
def pw32 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0
def pw33 : Nat := 0xfefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefe
def pw34 : Nat := 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e
def pw35 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffee
def pw36 : Nat := 0xee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee
def pw37 : Nat := 0xeeee0000eeee0000eeee0000eeee0000eeee0000eeee0000eeee0000eeee
def pw38 : Nat := 0xf4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4
def pw39 : Nat := 0xff44ff44ff44ff44ff44ff44ff44ff44ff44ff44ff44ff44ff44ff44ff44ff44
def pw40 : Nat := 0x3232323232323232323232323232323232323232323232323232323232323232
def pw41 : Nat := 0x3322332233223322332233223322332233223322332233223322332233223322
def pw42 : Nat := 0xcc88cc88cc88cc88cc88cc88cc88cc88cc88cc88cc88cc88cc88cc88cc88cc88
def pw43 : Nat := 0x44004400440044004400440044004400440044004400440044004400440044
def pw44 : Nat := 0xfffafffafffafffafffafffafffafffafffafffafffafffafffafffafffafffa
def pw45 : Nat := 0xf0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a
def pw46 : Nat := 0xcccccccceeeeeeeecccccccceeeeeeeecccccccceeeeeeeecccccccceeeeeeee
def pw47 : Nat := 0xf0f0f0f0fafafafaf0f0f0f0fafafafaf0f0f0f0fafafafaf0f0f0f0fafafafa
def pw48 : Nat := 0x5454545454545454545454545454545454545454545454545454545454545454
def pw49 : Nat := 0xfffffffffcfcfcfcfffffffffcfcfcfcfffffffffcfcfcfcfffffffffcfcfcfc
def pw50 : Nat := 0xaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeae
def pw51 : Nat := 0x5544554455445544554455445544554455445544554455445544554455445544
def pw52 : Nat := 0xaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaee
def pw53 : Nat := 0xf0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c
def pw54 : Nat := 0xfffffafafffffafafffffafafffffafafffffafafffffafafffffafafffffafa
def pw55 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfcfffffcfcfffffcfcfffffcfcfffffcfc
def pw56 : Nat := 0xc0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c
def pw57 : Nat := 0xfffffffffffff0f0fffffffffffff0f0fffffffffffff0f0fffffffffffff0f0
def pw58 : Nat := 0xfe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe
def pw59 : Nat := 0xfefe0000fefe0000fefe0000fefe0000fefe0000fefe0000fefe0000fefe
def pw60 : Nat := 0xe0e00000e0e00000e0e00000e0e00000e0e00000e0e00000e0e00000e0e
def pw61 : Nat := 0xf0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e
def pw62 : Nat := 0xffee0000ffee0000ffee0000ffee0000ffee0000ffee0000ffee0000ffee
def pw63 : Nat := 0xf0f0fefef0f0fefef0f0fefef0f0fefef0f0fefef0f0fefef0f0fefef0f0fefe
def pw64 : Nat := 0xf400f400f400f400f400f400f400f400f400f400f400f400f400f400f400f4
def pw65 : Nat := 0xfca8fca8fca8fca8fca8fca8fca8fca8fca8fca8fca8fca8fca8fca8fca8fca8
def pw66 : Nat := 0x54005400540054005400540054005400540054005400540054005400540054
def pw67 : Nat := 0xfcf8fcf8fcf8fcf8fcf8fcf8fcf8fcf8fcf8fcf8fcf8fcf8fcf8fcf8fcf8fcf8
def pw68 : Nat := 0xffffcc88ffffcc88ffffcc88ffffcc88ffffcc88ffffcc88ffffcc88ffffcc88
def pw69 : Nat := 0xfcfcfcfcfefefefefcfcfcfcfefefefefcfcfcfcfefefefefcfcfcfcfefefefe
def pw70 : Nat := 0xc0c0c0c0e0e0e0e0c0c0c0c0e0e0e0e0c0c0c0c0e0e0e0e0c0c0c0c0e0e0e0e
def pw71 : Nat := 0xcccc0000eeee0000cccc0000eeee0000cccc0000eeee0000cccc0000eeee
def pw72 : Nat := 0x3030303032323232303030303232323230303030323232323030303032323232
def pw73 : Nat := 0xc0c0c0caeaeaeae0c0c0c0caeaeaeae0c0c0c0caeaeaeae0c0c0c0caeaeaeae
def pw74 : Nat := 0xcc00ccaaeeaaee00cc00ccaaeeaaee00cc00ccaaeeaaee00cc00ccaaeeaaee
def pw75 : Nat := 0xfffff0f0fffffafafffff0f0fffffafafffff0f0fffffafafffff0f0fffffafa
def pw76 : Nat := 0xaafeaafeaafeaafeaafeaafeaafeaafeaafeaafeaafeaafeaafeaafeaafeaafe
def pw77 : Nat := 0xffffffff00fc00fcffffffff00fc00fcffffffff00fc00fcffffffff00fc00fc
def pw78 : Nat := 0xaeae0000aeae0000aeae0000aeae0000aeae0000aeae0000aeae0000aeae
def pw79 : Nat := 0xaaee0000aaee0000aaee0000aaee0000aaee0000aaee0000aaee0000aaee
def pw80 : Nat := 0xf0f00000c0c00000f0f00000c0c00000f0f00000c0c00000f0f00000c0c
def pw81 : Nat := 0xff00fc00ff00fc00ff00fc00ff00fc00ff00fc00ff00fc00ff00fc00ff00fc
def pw82 : Nat := 0x3333333333333030333333333333303033333333333330303333333333333030
def pw83 : Nat := 0xfcfc0000fefe0000fcfc0000fefe0000fcfc0000fefe0000fcfc0000fefe
def pw84 : Nat := 0xc0c00000e0e00000c0c00000e0e00000c0c00000e0e00000c0c00000e0e
def pw85 : Nat := 0xf0f0fcfcf0f0fefef0f0fcfcf0f0fefef0f0fcfcf0f0fefef0f0fcfcf0f0fefe
def pw86 : Nat := 0xfc00fcaafeaafe00fc00fcaafeaafe00fc00fcaafeaafe00fc00fcaafeaafe
def pw87 : Nat := 0xc0c0000aeae00000c0c0000aeae00000c0c0000aeae00000c0c0000aeae
def pw88 : Nat := 0xcc0000aaee000000cc0000aaee000000cc0000aaee000000cc0000aaee
def pw89 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
def pw90 : Nat := 0xfff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0
def pw91 : Nat := 0xf0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c
def pw92 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa
def pw93 : Nat := 0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc
def pw94 : Nat := 0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00
def pw95 : Nat := 0xfa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa
def pw96 : Nat := 0x3333303033333030333330303333303033333030333330303333303033333030
def pw97 : Nat := 0x5555550055555500555555005555550055555500555555005555550055555500
def pw98 : Nat := 0x8888888888888888888888888888888888888888888888888888888888888888
def pw99 : Nat := 0x2222222222222222222222222222222222222222222222222222222222222222
def pw100 : Nat := 0xff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88
def pw101 : Nat := 0xffff8888ffff8888ffff8888ffff8888ffff8888ffff8888ffff8888ffff8888
def pw102 : Nat := 0xffffffff88888888ffffffff88888888ffffffff88888888ffffffff88888888
def pw103 : Nat := 0xeeeeeeee00000000eeeeeeee00000000eeeeeeee00000000eeeeeeee
def pw104 : Nat := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a
def pw105 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def pw106 : Nat := 0x333333333333333300000000000000003333333333333333
def pw107 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def pw108 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def pw109 : Nat := 0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa
def pw110 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def pw111 : Nat := 0x3030303030303030303030303030303030303030303030303030303030303030
def pw112 : Nat := 0xc0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c
def pw113 : Nat := 0x330033000000000033003300000000003300330000000000330033
def pw114 : Nat := 0x303000003030000030300000303000003030000030300000303000003030
def pw115 : Nat := 0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000
def pw116 : Nat := 0xf0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c
def pw117 : Nat := 0x3333333330303030333333333030303033333333303030303333333330303030
def pw118 : Nat := 0xff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff0000
def pw119 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def pw120 : Nat := 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000
def pw121 : Nat := 0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00
def p1_T : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def p1_R : List Nat := [0, 1, 2]
def p1_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5)]
theorem p1_B : baseOK p1_T p1_R p1_E = true := by decide +kernel
def p1_Z : List SliceD := []
theorem p1_Y : ∀ s ∈ p1_Z, SliceN true p1_R p1_T s := by
  intro s h
  cases h
def p1_C : List (Nat × List Nat) := []
def p1_t : Tabs := (p1_C.map (mkCut true p1_Z),[(5,4),(6,4),(3,2),(3,1),(6,2),(5,1)],[],[[]])
theorem p1_W : TabsP true p1_R p1_T p1_t := ⟨cutsGood p1_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p1_D3 : List StD := [
([pw0,pw1,pw2],[1,5,9,13,17,21],[15,53,58])]
def p1_D2 : List StD := []
theorem p1_I2 : LevelN true p1_T 2 p1_D2 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p1_C3x0 : levelOK true p1_T p1_t 2 (p1_D2.map Prod.fst) ((p1_D3.drop (0*32)).take 32) = true := by decide +kernel
theorem p1_I3 : LevelN true p1_T 3 p1_D3 := levelStep p1_B p1_W p1_I2 (chunks 32 p1_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p1_C3x0
  ))
theorem p1_L : LowN true p1_R p1_T 4 := lowSearch p1_B p1_I3 (by decide +kernel)
def p2_T : Nat := 0xeae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8
def p2_R : List Nat := [0, 1, 2, 3]
def p2_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
theorem p2_B : baseOK p2_T p2_R p2_E = true := by decide +kernel
def p2_Z : List SliceD := [(pw3,4,[0, 1, 2])]
theorem p2_Y : ∀ s ∈ p2_Z, SliceN true p2_R p2_T s := by
  unfold p2_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p2_B p1_B p1_L (by decide +kernel),by simp⟩
def p2_C : List (Nat × List Nat) := [(0,[])]
def p2_t : Tabs := (p2_C.map (mkCut true p2_Z),[(5,4),(6,4),(3,2),(3,1),(6,2),(5,1)],[],[[]])
theorem p2_W : TabsP true p2_R p2_T p2_t := ⟨cutsGood p2_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p2_D4 : List StD := [
([pw0,pw1,pw2,pw4],[0,1,5,17,9,13,21],[54,90,3,108,5,9])]
def p2_D3 : List StD := []
theorem p2_I3 : LevelN true p2_T 3 p2_D3 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p2_C4x0 : levelOK true p2_T p2_t 3 (p2_D3.map Prod.fst) ((p2_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p2_I4 : LevelN true p2_T 4 p2_D4 := levelStep p2_B p2_W p2_I3 (chunks 32 p2_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p2_C4x0
  ))
theorem p2_L : LowN true p2_R p2_T 5 := lowSearch p2_B p2_I4 (by decide +kernel)
def p3_T : Nat := 0xeeeaece8eeeaece8eeeaece8eeeaece8eeeaece8eeeaece8eeeaece8eeeaece8
def p3_R : List Nat := [0, 1, 2, 3, 4]
def p3_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,2,10),(4,1,17)]
theorem p3_B : baseOK p3_T p3_R p3_E = true := by decide +kernel
def p3_Z : List SliceD := [(pw3,5,[0, 1, 2, 4])]
theorem p3_Y : ∀ s ∈ p3_Z, SliceN true p3_R p3_T s := by
  unfold p3_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p3_B p2_B p2_L (by decide +kernel),by simp⟩
def p3_C : List (Nat × List Nat) := [(0,[])]
def p3_t : Tabs := (p3_C.map (mkCut true p3_Z),[(5,4),(6,4),(3,2),(3,1),(6,2),(5,1),(10,2),(13,12)],[],[[]])
theorem p3_W : TabsP true p3_R p3_T p3_t := ⟨cutsGood p3_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p3_D5 : List StD := [
([pw0,pw1,pw2,pw4,pw5],[0,1,5,17,25,9,13,21,29],[102,170,275,3,204,5,5,25,9,17])]
def p3_D4 : List StD := []
theorem p3_I4 : LevelN true p3_T 4 p3_D4 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p3_C5x0 : levelOK true p3_T p3_t 4 (p3_D4.map Prod.fst) ((p3_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p3_I5 : LevelN true p3_T 5 p3_D5 := levelStep p3_B p3_W p3_I4 (chunks 32 p3_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p3_C5x0
  ))
theorem p3_L : LowN true p3_R p3_T 6 := lowSearch p3_B p3_I5 (by decide +kernel)
def p4_T : Nat := 0xeeeaeee8eeeaeee8eeeaeee8eeeaeee8eeeaeee8eeeaeee8eeeaeee8eeeaeee8
def p4_R : List Nat := [0, 1, 2, 3, 4]
def p4_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9),(4,1,17)]
theorem p4_B : baseOK p4_T p4_R p4_E = true := by decide +kernel
def p4_Z : List SliceD := [(pw6,5,[0, 1, 3, 4])]
theorem p4_Y : ∀ s ∈ p4_Z, SliceN true p4_R p4_T s := by
  unfold p4_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p4_B p2_B p2_L (by decide +kernel),by simp⟩
def p4_C : List (Nat × List Nat) := [(0,[])]
def p4_t : Tabs := (p4_C.map (mkCut true p4_Z),[(5,4),(6,4),(3,2),(3,1),(6,2),(5,1),(10,2),(9,8),(9,1)],[],[[]])
theorem p4_W : TabsP true p4_R p4_T p4_t := ⟨cutsGood p4_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p4_D5 : List StD := [
([pw0,pw1,pw2,pw4,pw5],[0,1,5,17,25,9,13,21,33,29],[102,170,786,3,204,261,5,25,9,17])]
def p4_D4 : List StD := []
theorem p4_I4 : LevelN true p4_T 4 p4_D4 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p4_C5x0 : levelOK true p4_T p4_t 4 (p4_D4.map Prod.fst) ((p4_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p4_I5 : LevelN true p4_T 5 p4_D5 := levelStep p4_B p4_W p4_I4 (chunks 32 p4_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p4_C5x0
  ))
theorem p4_L : LowN true p4_R p4_T 6 := lowSearch p4_B p4_I5 (by decide +kernel)
def p5_T : Nat := 0xeac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8
def p5_R : List Nat := [0, 1, 2, 3]
def p5_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,2,6),(3,1,9)]
theorem p5_B : baseOK p5_T p5_R p5_E = true := by decide +kernel
def p5_Z : List SliceD := []
theorem p5_Y : ∀ s ∈ p5_Z, SliceN true p5_R p5_T s := by
  intro s h
  cases h
def p5_C : List (Nat × List Nat) := []
def p5_t : Tabs := (p5_C.map (mkCut true p5_Z),[(6,4),(3,1),(3,2),(9,12),(6,2),(9,1),(9,0),(6,12),(9,5)],[],[[]])
theorem p5_W : TabsP true p5_R p5_T p5_t := ⟨cutsGood p5_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p5_D3 : List StD := [
([pw0,pw1,pw2,pw4],[1,21,5,9,17,13,25,29,33],[5,56,74,5,131,274])]
def p5_D2 : List StD := []
theorem p5_I2 : LevelN true p5_T 2 p5_D2 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p5_C3x0 : levelOK true p5_T p5_t 2 (p5_D2.map Prod.fst) ((p5_D3.drop (0*32)).take 32) = true := by decide +kernel
theorem p5_I3 : LevelN true p5_T 3 p5_D3 := levelStep p5_B p5_W p5_I2 (chunks 32 p5_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_C3x0
  ))
theorem p5_L : LowN true p5_R p5_T 4 := lowSearch p5_B p5_I3 (by decide +kernel)
def p6_T : Nat := 0xfeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeea
def p6_R : List Nat := [0, 1, 2, 3]
def p6_E : List (Nat × Nat × Nat) := [(0,0,1),(1,4,6),(2,2,6),(3,2,10)]
theorem p6_B : baseOK p6_T p6_R p6_E = true := by decide +kernel
def p6_Z : List SliceD := [(pw7,4,[1, 2, 3])]
theorem p6_Y : ∀ s ∈ p6_Z, SliceN true p6_R p6_T s := by
  unfold p6_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p6_B p1_B p1_L (by decide +kernel),by simp⟩
def p6_C : List (Nat × List Nat) := [(0,[])]
def p6_t : Tabs := (p6_C.map (mkCut true p6_Z),[(1,0),(6,4),(3,2)],[],[[]])
theorem p6_W : TabsP true p6_R p6_T p6_t := ⟨cutsGood p6_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p6_D4 : List StD := [
([pw0,pw1,pw2,pw4],[0,1,5,9],[15,3,3,1,5,1])]
def p6_D3 : List StD := []
theorem p6_I3 : LevelN true p6_T 3 p6_D3 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p6_C4x0 : levelOK true p6_T p6_t 3 (p6_D3.map Prod.fst) ((p6_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p6_I4 : LevelN true p6_T 4 p6_D4 := levelStep p6_B p6_W p6_I3 (chunks 32 p6_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p6_C4x0
  ))
theorem p6_L : LowN true p6_R p6_T 5 := lowSearch p6_B p6_I4 (by decide +kernel)
def p7_T : Nat := 0xfeeafce8feeafce8feeafce8feeafce8feeafce8feeafce8feeafce8feeafce8
def p7_R : List Nat := [0, 1, 2, 3, 4]
def p7_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,2,10),(4,1,17)]
theorem p7_B : baseOK p7_T p7_R p7_E = true := by decide +kernel
def p7_Z : List SliceD := [(pw8,4,[0, 2, 3, 4]),(pw9,4,[1, 2, 3]),(pw6,4,[0, 1, 3, 4]),(pw3,5,[0, 1, 2, 4]),(pw5,5,[0, 1, 2, 3])]
theorem p7_Y : ∀ s ∈ p7_Z, SliceN true p7_R p7_T s := by
  unfold p7_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p7_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p7_B p1_B p1_L (by decide +kernel),mkSlice (w:=0) p7_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p7_B p2_B p2_L (by decide +kernel),mkSlice (w:=16) p7_B p6_B p6_L (by decide +kernel),by simp⟩
def p7_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[])]
def p7_t : Tabs := (p7_C.map (mkCut true p7_Z),[(6,4),(3,2),(3,0),(5,4),(25,24),(3,1),(6,2),(10,2),(10,0),(12,4),(17,16),(17,24),(6,20),(6,18),(17,1),(17,9),(5,1),(26,2),(10,16),(12,16)],[],[[]])
theorem p7_W : TabsP true p7_R p7_T p7_t := ⟨cutsGood p7_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p7_D6 : List StD := [
([pw0,pw1,pw2,pw4,pw5],[4,0,1,5,12,16,8,17,25,29,9,13,21,33,37,3],[1039,2057,137,137,37190,8726,39,17232,33,49])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p7_D5 : List StD := [
([pw0,pw1,pw2,pw10,pw4,pw5],[13,29,0,57,5,25,41,4,12,16,1,21,37,45,49,53,61,3],[17,17,65,8195,65,36,2048,6,17412,4,4098,32808,131330,648,65546])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p7_D4 : List StD := [
([pw11,pw0,pw1,pw2,pw5],[5,29,25,33,41,57,1,13,21,65,69,73,77],[19,266,518,1058,17,129,17,76,2088,4132])]
def p7_D3 : List StD := []
theorem p7_I3 : LevelN true p7_T 3 p7_D3 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p7_C4x0 : levelOK true p7_T p7_t 3 (p7_D3.map Prod.fst) ((p7_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p7_I4 : LevelN true p7_T 4 p7_D4 := levelStep p7_B p7_W p7_I3 (chunks 32 p7_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p7_C4x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p7_C5x0 : levelOK true p7_T p7_t 4 (p7_D4.map Prod.fst) ((p7_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p7_I5 : LevelN true p7_T 5 p7_D5 := levelStep p7_B p7_W p7_I4 (chunks 32 p7_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p7_C5x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p7_C6x0 : levelOK true p7_T p7_t 5 (p7_D5.map Prod.fst) ((p7_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p7_I6 : LevelN true p7_T 6 p7_D6 := levelStep p7_B p7_W p7_I5 (chunks 32 p7_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p7_C6x0
  ))
theorem p7_L : LowN true p7_R p7_T 7 := lowSearch p7_B p7_I6 (by decide +kernel)
def p8_T : Nat := 0xeee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8
def p8_R : List Nat := [0, 1, 2, 3]
def p8_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
theorem p8_B : baseOK p8_T p8_R p8_E = true := by decide +kernel
def p8_Z : List SliceD := [(pw6,4,[0, 1, 3])]
theorem p8_Y : ∀ s ∈ p8_Z, SliceN true p8_R p8_T s := by
  unfold p8_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p8_B p1_B p1_L (by decide +kernel),by simp⟩
def p8_C : List (Nat × List Nat) := [(0,[])]
def p8_t : Tabs := (p8_C.map (mkCut true p8_Z),[(5,4),(6,4),(3,2),(3,1),(6,2),(5,1),(10,2),(9,8),(9,1),(10,8)],[],[[]])
theorem p8_W : TabsP true p8_R p8_T p8_t := ⟨cutsGood p8_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p8_D4 : List StD := [
([pw0,pw1,pw2,pw4],[1,5,17,25,9,13,21,33,0,29,37],[51,85,649,102,1162,268])]
def p8_D3 : List StD := []
theorem p8_I3 : LevelN true p8_T 3 p8_D3 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p8_C4x0 : levelOK true p8_T p8_t 3 (p8_D3.map Prod.fst) ((p8_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p8_I4 : LevelN true p8_T 4 p8_D4 := levelStep p8_B p8_W p8_I3 (chunks 32 p8_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p8_C4x0
  ))
theorem p8_L : LowN true p8_R p8_T 5 := lowSearch p8_B p8_I4 (by decide +kernel)
def p9_T : Nat := 0xfeeefae8feeefae8feeefae8feeefae8feeefae8feeefae8feeefae8feeefae8
def p9_R : List Nat := [0, 1, 2, 3, 4]
def p9_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9),(4,1,17)]
theorem p9_B : baseOK p9_T p9_R p9_E = true := by decide +kernel
def p9_Z : List SliceD := [(pw8,5,[0, 2, 3, 4]),(pw6,5,[0, 1, 4, 3]),(pw3,5,[0, 1, 2, 4]),(pw12,5,[0, 2, 1, 3])]
theorem p9_Y : ∀ s ∈ p9_Z, SliceN true p9_R p9_T s := by
  unfold p9_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p9_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p9_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p9_B p8_B p8_L (by decide +kernel),mkSlice (w:=0) p9_B p8_B p8_L (by decide +kernel),by simp⟩
def p9_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[])]
def p9_t : Tabs := (p9_C.map (mkCut true p9_Z),[(3,1),(6,4),(5,1),(6,2),(9,1),(12,4),(17,1),(18,2),(18,24),(12,24),(18,10)],[],[[]])
theorem p9_W : TabsP true p9_R p9_T p9_t := ⟨cutsGood p9_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p9_D6 : List StD := [
([pw0,pw1,pw2,pw4,pw5],[0,8,12,4,1,5,21,29,9,13,17,25,33,37,41],[49,776,1090,2180,49,4099,133,74,8204,16390])]
def p9_D5 : List StD := []
theorem p9_I5 : LevelN true p9_T 5 p9_D5 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p9_C6x0 : levelOK true p9_T p9_t 5 (p9_D5.map Prod.fst) ((p9_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p9_I6 : LevelN true p9_T 6 p9_D6 := levelStep p9_B p9_W p9_I5 (chunks 32 p9_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p9_C6x0
  ))
theorem p9_L : LowN true p9_R p9_T 7 := lowSearch p9_B p9_I6 (by decide +kernel)
def p10_T : Nat := 0xeaeaeac8eaeaeac8eaeaeac8eaeaeac8eaeaeac8eaeaeac8eaeaeac8eaeaeac8
def p10_R : List Nat := [0, 1, 2, 3, 4]
def p10_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,2,6),(3,1,9),(4,1,17)]
theorem p10_B : baseOK p10_T p10_R p10_E = true := by decide +kernel
def p10_Z : List SliceD := [(pw3,4,[0, 1, 2, 4])]
theorem p10_Y : ∀ s ∈ p10_Z, SliceN true p10_R p10_T s := by
  unfold p10_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p10_B p5_B p5_L (by decide +kernel),by simp⟩
def p10_C : List (Nat × List Nat) := [(0,[])]
def p10_t : Tabs := (p10_C.map (mkCut true p10_Z),[(6,4),(3,1),(3,2),(9,12),(6,2),(9,1),(9,0),(17,1),(17,0),(6,12),(6,20),(9,5),(17,5)],[],[[]])
theorem p10_W : TabsP true p10_R p10_T p10_t := ⟨cutsGood p10_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p10_D4 : List StD := [
([pw0,pw1,pw2,pw4,pw5],[1,21,9,17,29,5,0,13,25,33,37,41,45,49],[33,140,262,532,33,1027,2065,4106,8216,66])]
def p10_D3 : List StD := []
theorem p10_I3 : LevelN true p10_T 3 p10_D3 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_C4x0 : levelOK true p10_T p10_t 3 (p10_D3.map Prod.fst) ((p10_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p10_I4 : LevelN true p10_T 4 p10_D4 := levelStep p10_B p10_W p10_I3 (chunks 32 p10_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p10_C4x0
  ))
theorem p10_L : LowN true p10_R p10_T 5 := lowSearch p10_B p10_I4 (by decide +kernel)
def p11_T : Nat := 0xfeeefeeafeeefce8feeefeeafeeefce8feeefeeafeeefce8feeefeeafeeefce8
def p11_R : List Nat := [0, 1, 2, 3, 4, 5]
def p11_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,2,10),(4,1,17),(5,1,33)]
theorem p11_B : baseOK p11_T p11_R p11_E = true := by decide +kernel
def p11_Z : List SliceD := [(pw13,5,[1, 2, 3, 4]),(pw6,6,[0, 1, 4, 3, 5]),(pw3,6,[0, 1, 2, 4, 5]),(pw12,7,[0, 1, 2, 3, 5]),(pw14,7,[1, 0, 2, 3, 4]),(pw15,5,[0, 1, 4, 5]),(pw8,5,[0, 2, 3, 4, 5]),(pw16,5,[1, 2, 3, 4]),(pw17,4,[0, 1, 3, 5]),(pw18,5,[1, 0, 4, 3]),(pw19,4,[0, 2, 3, 4])]
theorem p11_Y : ∀ s ∈ p11_Z, SliceN true p11_R p11_T s := by
  unfold p11_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p11_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p11_B p3_B p3_L (by decide +kernel),mkSlice (w:=0) p11_B p4_B p4_L (by decide +kernel),mkSlice (w:=0) p11_B p7_B p7_L (by decide +kernel),mkSlice (w:=0) p11_B p9_B p9_L (by decide +kernel),mkSlice (w:=0) p11_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p11_B p10_B p10_L (by decide +kernel),mkSlice (w:=32) p11_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p11_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p11_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p11_B p5_B p5_L (by decide +kernel),by simp⟩
def p11_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(3,[129]),(7,[]),(3,[131]),(3,[257]),(3,[385]),(3,[387]),(3,[514]),(5,[386]),(4,[257]),(3,[261]),(3,[262]),(4,[258]),(4,[385]),(3,[389]),(3,[390]),(4,[386]),(5,[389]),(3,[517]),(0,[389]),(8,[]),(4,[521]),(3,[521]),(9,[]),(3,[260,21]),(3,[129,385]),(3,[256,149]),(7,[386]),(0,[386]),(7,[389]),(3,[257,385]),(3,[128,277]),(3,[128,405]),(3,[130,405]),(3,[385,130]),(3,[385,258]),(3,[514,149]),(3,[514,277]),(3,[512]),(10,[]),(4,[257,521]),(3,[261,404]),(4,[257,406]),(3,[261,406]),(5,[391]),(3,[519]),(3,[523,149]),(3,[261,535]),(3,[517,278]),(3,[258]),(5,[393]),(3,[523]),(4,[261,389,521]),(3,[258,534]),(3,[261,533]),(3,[519,277])]
def p11_t : Tabs := (p11_C.map (mkCut true p11_Z),[(5,4),(3,2),(3,1),(5,1),(25,24),(17,1),(33,1),(33,0),(6,4),(6,2),(12,4),(10,8),(10,2),(18,2),(6,36),(12,8),(12,24),(6,34),(25,9),(41,9),(18,34),(35,2),(11,9),(17,16),(21,20),(37,4),(18,16),(17,9),(41,40),(3,9),(5,9),(28,24),(17,24),(33,40),(28,20),(42,34),(41,8),(22,20),(33,9),(12,40),(26,24),(10,40),(10,34),(12,0),(12,56),(10,9),(11,1),(12,9),(21,4),(10,1),(33,34),(25,1),(41,1),(5,2),(18,20),(22,4),(38,4),(17,0),(18,0),(25,8),(3,0),(7,2),(5,0),(3,4),(5,16),(38,36),(38,2),(13,1),(18,24),(42,2),(33,8),(10,0),(44,4),(5,8),(6,0),(3,8),(12,1),(49,16),(18,52),(10,32),(28,16),(12,32),(18,56),(11,2),(17,4),(33,48),(33,32),(18,4),(6,16),(10,24),(11,4),(19,4),(35,4),(17,8),(6,1),(17,2),(33,2),(5,24),(5,40),(12,16),(44,24),(18,32),(6,32),(17,32),(17,20),(3,40),(12,20),(10,4),(3,24),(13,9),(12,48)],[],[[]])
theorem p11_W : TabsP true p11_R p11_T p11_t := ⟨cutsGood p11_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p11_D8 : List StD := [
([pw0,pw1,pw2,pw4,pw5,pw20],[0,3,4,12,16,1,13,8,21,25,5,17,41,20,9,29,33,37,45,49,53,57,61,65,69,73,77,81],[17443,1127,2211,2345,33331,196678,790658,1048840,2097683,4206660,8388942,16777815,33554824,67109521,134217753])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p11_D7 : List StD := [
([pw0,pw1,pw21,pw2,pw4,pw5,pw20],[0,3,28,24,32,13,21,9,5,49,20,25,41,61,37,53,65,73,85,89],[137,8,291,259,69,264449,1,16554,524936,32972,17,9250,5634,70,2065,12832,65638,17,131140,17,21]),
([pw22,pw0,pw1,pw2,pw4,pw5,pw20],[24,0,36,32,37,49,53,3,1,9,20,28,93,17,25,29,33,41,61,65,73,89],[2049,65537,1169,1185,2117,11,515,4354,8450,4102,49410,657,2097665,69,11,393264,524500,26,1048676,42,14]),
([pw0,pw1,pw2,pw23,pw4,pw5,pw20],[0,20,33,32,3,1,40,41,49,9,13,21,25,53,24,45,97,101,105,109],[565,3,2,51,65569,135201,1558,49172,390,272388,13,1,1410,82,11,386,10304,4105,524354,11,9]),
([pw0,pw1,pw2,pw4,pw24,pw5,pw20],[20,32,13,33,0,17,9,3,44,21,25,37,53,113,24,45,61,105,109,117,121,125],[234,39,3,1,8226,8226,2117,557193,16584,135688,1050,1114117,2053,2097157,7,2,262401,19,4864,18,1042]),
([pw0,pw1,pw2,pw24,pw5,pw20],[0,3,20,32,44,13,129,53,9,21,33,37,41,133,49,65],[323,99,5,8257,8257,3110,21762,656,9,6182,32950,9,656,9,25]),
([pw25,pw0,pw1,pw2,pw5,pw20],[20,32,48,5,25,49,44,1,37,41,53,0,13,21,29,65,93,137,141],[65,545,545,131137,262177,138,131,65546,16410,4353,9220,2066,32773,259,1046]),
([pw26,pw0,pw1,pw2,pw4,pw5],[0,52,21,3,56,13,25,85,41,49,5,9,29,33,37,45,53,61,65,73,77,101,145],[1025,2121,105,1048641,7,4225,2097281,4194433,7,24632,33560,65542,131888,262158,524294]),
([pw0,pw1,pw2,pw10,pw4,pw5,pw20],[20,3,60,1,33,64,37,49,53,24,21,25,0,5,41,93,32,29,57,69,81,109,129,149,153],[8218,8267,36874,4194443,34056,133134,529,1,17041,8389904,264214,512,16577,99,524357,131,1312,71686,2097185,16777221,1048868]),
([pw27,pw0,pw1,pw2,pw4,pw5,pw20],[24,20,68,72,1,49,3,5,53,32,13,33,61,0,64,9,21,25,29,57,65,81,109,129,153,157],[721,32769,16385,35,261,8705,2257,5250,8388722,65812,393304,2051,35,261,524297,5154,1048582,33554442,4194310,16777226,2097164]),
([pw0,pw1,pw2,pw4,pw28,pw5,pw20],[20,76,1,37,45,49,53,3,80,5,13,21,25,0,24,17,29,61,69,73,77,81,89,125,161,165,169],[4194836,1548,32933,8836,34884,69766,1049,16401,1,16779344,33558674,131113,1033,8388617,262155,16384,524577,67108899,2368,1060866,2097474]),
([pw29,pw0,pw1,pw2,pw4,pw5,pw20],[20,24,84,88,5,37,53,3,41,89,0,32,9,13,21,25,29,45,49,65,69,81,109,129,153,165,173],[1170,4098,35,262147,70,2058,131586,8241,8389009,16468,98456,35,515,70,33554442,67109153,524293,1048585,4194309,16777225,2097164]),
([pw0,pw1,pw2,pw4,pw5,pw30],[32,92,0,1,96,13,3,24,5,49,53,57,17,21,41,37,61,65,73,77,165],[269,269,4109,4109,269,35042,1051330,11408,4,82466,132210,99,263698,540675,8209]),
([pw0,pw1,pw2,pw4,pw31,pw20],[20,100,3,108,1,49,104,5,21,25,41,33,65,12,9,29,53,57,81,129,153,177],[16534,151,524343,470,33310,6149,1057,67908,131598,5153,8193,2097163,1057,1048587,262990]),
([pw0,pw1,pw2,pw4,pw5,pw32],[32,0,20,1,112,5,17,49,53,69,157,116,21,25,41,109,177],[43,43,75,75,43,1540,16516,4368,10241,1540,65556,2,32788,133,273])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p11_D6 : List StD := [
([pw1,pw21,pw2,pw23,pw4,pw5,pw20],[32,53,1,5,9,13,49,41,21,3,120,33,109,117,181,185,189,193],[2048,560,16408,40976,274,17,65572,1036,196,131078,5,1,224,546,33,200,266,9,4162,65,3]),
([pw1,pw21,pw2,pw4,pw24,pw5,pw20],[32,37,53,9,5,17,20,13,21,61,25,33,65,109,113,117,129,197,201,205,209],[2048,138,163848,262168,268,9,514,65632,112,16420,33,514,130,4102,3,1,532484,1049601,276,17,5]),
([pw1,pw21,pw2,pw24,pw5,pw20],[32,124,21,3,0,13,41,5,9,129,25,37,53,20,61,65],[1,2344,456,4358,1041,16936,8896,526,17,2272,32814,1041,4166,17,7]),
([pw0,pw21,pw2,pw10,pw4,pw5,pw20],[21,49,5,9,25,33,37,3,41,53,32,128,1,13,69,81,85,109,153,181,185,213,217,221,225],[4096,2097284,524300,134,517,65556,4194400,2088,290,8388641,16777264,8192,258,193,16464,1048586,521,1032,131075,262162,32785]),
([pw27,pw0,pw21,pw2,pw4,pw5,pw20],[53,5,13,25,9,49,33,61,21,32,1,37,41,45,65,81,85,109,117,153,157,181,185,221,225,3],[2097170,8192,2048,4456464,273,528,1024,134,33554466,259,65546,132,4192,8388673,16777288,132,16389,1048588,131105,524328,32777]),
([pw0,pw1,pw2,pw33,pw4,pw5,pw20],[21,25,49,1,9,37,3,5,53,0,12,20,32,13,45,57,61,69,81,85,93,109,121,153,185],[152,136,1048576,76,265,524298,8240,16384,16777236,273,32786,65536,4194340,97,131106,2116,1089,4610,2097157,8388614,262147]),
([pw34,pw0,pw1,pw2,pw4,pw5,pw20],[1,21,25,41,33,5,49,9,53,61,3,0,12,32,13,57,65,81,85,109,153,157],[33,144,16384,72,5122,10244,33,33,1033,259,262149,144,88,274,32788,72,66050,2097668,524298,1048588,131078]),
([pw0,pw1,pw2,pw4,pw35,pw5,pw20],[13,21,25,45,5,49,9,37,53,3,0,12,20,32,1,33,41,65,69,81,85,109,121,129,153,165],[72,145,8388656,16384,274,1048596,137,72,32768,266,33554444,4194337,4609,131075,262149,65536,2097186,16777252,2562,9220,524294]),
([pw36,pw0,pw1,pw2,pw4,pw5,pw20],[17,61,77,45,73,5,13,9,21,25,37,49,53,65,69,81,85,165],[33,136,66,2048,272,516,33,67,33,33,65541,1034,136,4120,131084,66,8210,16390,272,516,32788]),
([pw37,pw0,pw1,pw21,pw2,pw4,pw20],[13,5,49,53,132,25,61,41,9,21,12,136,37,81,85,181,229,233,3],[522,520,1024,73,140,8232,33026,65536,67,262150,16418,131072,4097,132,304,65,132,2096,65,17,20]),
([pw37,pw0,pw1,pw2,pw4,pw20],[136,41,53,61,229,233,132,13,49,5,9,21,25,37,73,85,89,193,221,237,3],[2580,3108,1048716,16646,4165,1584,131224,524307,36881,270376,65826,97,394,73,67]),
([pw0,pw1,pw21,pw2,pw4,pw31,pw20],[49,140,5,9,65,3,21,41,20,25,53,100,104,1,13,33,85,181,185],[131084,8192,52,37,1092,66052,32768,56,262153,1096,10,304,385,4192,2562,145,16384,18,129,3,66]),
([pw0,pw1,pw2,pw38,pw4,pw5,pw20],[1,9,25,49,37,53,21,33,93,3,0,20,32,5,13,29,41,57,69,81,109,129,153,185,241,245],[16777219,33554449,8449,2097161,257,32773,146,130,8388618,98,131078,16384,65560,560,262164,2568,96,5124,1048616,4194316,524324]),
([pw0,pw1,pw2,pw4,pw39,pw5,pw20],[1,9,25,37,53,17,49,13,21,45,29,41,61,65,69,73,77,81,165,169,241,249],[1048579,2097161,33,33,33,1029,138,578,514,274,262150,4104,136,8216,16396,2048,32848,524356,272,65540,131092]),
([pw22,pw0,pw2,pw10,pw4,pw5,pw20],[25,49,53,37,33,93,9,21,41,32,5,13,29,45,57,69,81,109,129,153,185,217,241,253,3],[1024,2097176,8192,274,148,16401,8388648,4194400,262178,132,4129,2048,266,16777228,32777,1048642,132,577,131078,524291,65541]),
([pw22,pw0,pw1,pw2,pw4,pw31,pw20],[140,49,65,21,41,1,25,53,20,100,9,3,5,13,29,33,129,257],[4096,32768,2308,274,136,577,1025,131108,65570,136,16480,3076,18,136,577,22,8192,5,18,3,9]),
([pw1,pw2,pw23,pw24,pw5,pw20],[32,20,9,0,1,13,21,25,3,144,53,33,129,45,49,105,261],[2342,12548,18452,33860,65677,1,306,802,35,2,1600,4233,1616,153,201]),
([pw0,pw1,pw23,pw10,pw4,pw5,pw20],[21,49,1,13,25,53,33,37,41,3,32,148,5,9,57,81,101,109,153,189,217,253,265,269],[2097668,4096,524300,518,37,65556,1048768,8192,322,33,16464,2184,258,33,4194448,8388618,41,1032,131075,262162,32785]),
([pw40,pw0,pw1,pw2,pw4,pw5,pw20],[5,25,49,53,37,1,21,41,13,3,0,32,9,45,69,81,85,109,153,165],[33,4096,272,132,72,3074,33,33,517,73,65539,272,132,72,532482,148,536,16402,131084,262150,32778]),
([pw0,pw1,pw23,pw4,pw31,pw20],[100,20,33,140,1,104,13,41,49,3,9,25,45,53,65,101],[1557,2,531,113,34833,20996,390,9284,13,386,97,2057,418,11,9]),
([pw0,pw1,pw2,pw24,pw28,pw5,pw20],[25,37,53,45,13,21,17,49,152,5,9,41,65,69,81,117,129,145,153,165,209,273,277,3],[32776,18,512,8454208,100,131137,26,2097288,1024,44,524297,18,18,4102,8195,2432,36,4194433,36,1310721,16389]),
([pw29,pw0,pw1,pw2,pw24,pw5,pw20],[13,21,25,129,37,41,53,32,45,0,5,9,49,65,69,81,165,197,281,285,289,3],[2097288,2048,17,4256,66,644,131336,25,1024,74,262156,17,524576,66,65796,17,8195,16389,98,1048612,32774]),
([pw41,pw0,pw1,pw2,pw4,pw5,pw20],[5,25,37,21,49,17,13,156,33,53,0,32,9,41,57,65,69,81,85,109,121,153,285],[33,4096,68,8336,648,3074,33,69,33,33,262147,68,4194576,520,16642,1048596,32780,65542,524312,2097170,131082]),
([pw0,pw1,pw2,pw10,pw24,pw5,pw20],[25,53,33,37,129,3,21,49,32,41,0,5,9,13,57,69,81,217,277,281],[52,56,304,2048,82,524305,131084,4096,644,70,16389,8192,648,42,32777,160,66,1281,66,262273,65539]),
([pw27,pw0,pw1,pw2,pw24,pw5,pw20],[21,25,41,129,13,53,33,49,0,3,32,5,9,37,57,65,81,157,277,281,293,297],[776,4096,8192,132,33,1280,584,1048600,2048,41,524298,2097232,132,33,16450,132,32785,131090,37,262150,65539]),
([pw0,pw42,pw1,pw2,pw24,pw5,pw20],[13,25,53,33,129,21,37,3,20,160,41,0,32,1,9,49,57,65,69,81,273,281,289],[784,152,81,8192,52,2097170,16384,385,32768,644,6146,73,1049608,44,65546,65,131077,262147,36,4195330,524294]),
([pw0,pw1,pw2,pw24,pw35,pw5,pw20],[25,37,53,13,21,3,9,49,0,20,32,44,5,33,41,65,69,81,129,165,197,273,277,281,301],[17825792,10,4096,32,20,8650753,10,2097344,8192,20,524353,10,546,32774,65539,16384,20,4194433,2084,1281,131077]),
([pw43,pw0,pw1,pw2,pw24,pw5,pw20],[13,21,25,37,53,9,41,0,32,1,33,49,65,69,81,129,165,197,281,285,289,301,3],[4194304,1024,9,2048,18,388,2228224,9,512,18,294916,9,524384,18,65572,9,4099,8197,18,1048644,16390]),
([pw41,pw0,pw1,pw2,pw24,pw5,pw20],[13,21,25,129,37,53,33,20,160,49,0,32,5,9,41,57,65,69,81,277,281,285,3],[392,8192,145,16384,290,3076,4194376,25,4096,42,1048588,17,2097728,34,32836,17,65539,131077,34,524804,262150]),
([pw0,pw1,pw2,pw24,pw44,pw5,pw20],[33,20,25,53,21,9,13,41,0,32,1,37,57,65,81,105,129,157,281,289,293,305],[33,3145728,1024,2,24,327684,33,33,32769,25,4101,130,2048,8258,131138,2,24,524420,24,772,16396]),
([pw45,pw0,pw1,pw2,pw24,pw5,pw20],[20,33,21,25,129,53,9,37,164,41,3,0,32,13,57,69,81,281,289],[273,66,8192,1,292,6152,82,1168,1,52,131096,3,66,38,16394,513,1153,32897,36,262664,65548]),
([pw0,pw1,pw2,pw24,pw31,pw20],[140,20,33,9,129,3,100,41,65,21,25,49,53,133,44],[61,51,2,8209,8209,302,2188,4620,1093,418,16384,259,6784,65,1089]),
([pw0,pw1,pw46,pw2,pw4,pw5],[0,29,168,13,21,41,3,9,49,5,25,61,37,53,65,73,77,89,101,145,309],[515,515,262147,524291,1048579,1,4296,131488,8340,3144,66848,84,2344,16476,32820]),
([pw0,pw1,pw2,pw47,pw4,pw5],[56,0,1,33,172,13,41,49,85,3,9,21,25,53,45,97,105,109,145],[1292,262,262,262150,32774,1577,21000,201,75784,2,225,561,193,14352,131089]),
([pw26,pw0,pw1,pw2,pw10,pw4,pw5],[21,49,25,33,37,3,53,85,0,29,41,56,5,9,13,101,109,209,217,281],[4096,44,52,292,131078,69,648,32912,896,524418,65,262168,8192,1034,73,16384,1042,49,2082,65,65539]),
([pw26,pw27,pw0,pw1,pw2,pw4,pw5],[21,13,25,33,49,53,61,85,0,29,41,3,5,9,37,65,109,209,281,297],[2308,4096,2060,70,131092,37,896,8192,16384,1040,33,648,66,262288,33,524298,1048,41,66,32771,65553]),
([pw26,pw0,pw1,pw2,pw4,pw28,pw5],[21,37,45,13,49,53,77,25,29,89,145,5,9,41,61,65,73,117],[2048,516,10,208,192,97,516,10,1296,1280,33,14,131092,4096,37,16386,10,32771,8192,65553,33]),
([pw26,pw29,pw0,pw1,pw2,pw4,pw5],[13,21,25,41,89,37,53,0,45,85,5,9,29,49,65,109,173,209,281,285,3],[1048708,1024,276,37,131084,70,4736,2048,33,8192,66,272,33,262664,66,49,524312,82,65545,16387,32778]),
([pw26,pw0,pw1,pw2,pw4,pw31],[100,56,9,3,41,49,21,25,33,65,85,101,52,176,29,53,209,281],[8193,141,11,65539,201,17409,2051,131075,3073,782,54,33092,562,4096,50]),
([pw48,pw0,pw1,pw2,pw4,pw5,pw20],[9,21,25,49,13,33,53,37,93,3,0,20,32,5,29,57,69,81,109,121,129,153,185],[8192,33,144,2568,66,5124,33,144,1048840,66,16644,33,4194313,67,32773,524312,530,65556,262154,2097164,131078]),
([pw0,pw1,pw2,pw10,pw4,pw5,pw30],[1,49,53,5,21,37,41,57,92,180,25,93,3,13,33,109,129,165,313],[9,9,2049,65539,2049,9,262304,131072,194,148,16384,8192,66,4132,1568,4354,20,1792,32774,66,20]),
([pw0,pw1,pw10,pw4,pw31,pw20],[3,20,184,1,49,25,33,37,65,21,104,5,41,17,29,57,69,93,153,177],[2121,131337,8219,2696,16429,2,4178,1728,32869,275,1920,524581,4114,262166,65701]),
([pw11,pw0,pw1,pw2,pw10,pw5,pw20],[5,25,49,53,93,21,37,33,41,3,188,192,1,29,57,69,81,173,217,277,285],[21,260,260,1024,44,524294,17,4097,17,17,8195,262336,1048576,40,16514,131072,584,32834,40,2562,65546]),
([pw11,pw0,pw1,pw2,pw5,pw20],[192,21,25,49,93,173,285,3,5,53,20,33,37,41,196,1,29,81,137,141,149,185,269,317,321,325],[408,10312,12328,262666,524429,2097488,4227120,786,65685,6240,1049154,8388805,16778274,33555493,147463]),
([pw0,pw1,pw2,pw10,pw4,pw5,pw49],[1,49,53,200,21,33,93,5,37,41,3,92,180,109,129,157,165,209,217],[129,129,65,16387,65,65,262432,65536,546,52,8,32768,514,1284,4096,3074,20,8,8198,131082,20]),
([pw0,pw50,pw1,pw2,pw4,pw5,pw20],[21,25,33,13,49,5,9,41,53,61,3,12,16,32,1,37,57,65,81,85,109,153,157,245],[16384,68,8388648,1072,289,524322,68,33288,144,3073,12290,68,148,261,65542,520,131081,4194314,1048593,2097170,262147]),
([pw51,pw0,pw1,pw2,pw4,pw5,pw20],[9,13,25,53,49,21,37,45,48,1,16,32,5,29,41,65,69,81,109,121,153,165,3],[4096,129,66,16656,296,3076,129,66,4194832,40,8708,67,129,41,2097157,524306,32778,65542,262168,1048596,131084]),
([pw0,pw1,pw2,pw4,pw28,pw5,pw30],[1,13,53,5,21,37,49,17,25,77,165,41,45,57,61,65,73,329],[9,9,129,9,129,9,34,132160,8192,1044,4096,16386,34,32774,34,2048,65604,832,20,768,20]),
([pw0,pw52,pw1,pw2,pw4,pw5,pw20],[13,21,25,45,5,9,41,48,37,53,61,3,16,32,1,49,65,69,81,85,109,153,165,333],[16384,40,273,8390672,530,524308,40,1025,32960,2178,12292,265,40,522,4194316,1025,65539,131077,1048642,2097220,262150]),
([pw0,pw1,pw2,pw4,pw31,pw30],[140,92,1,5,41,57,49,65,21,165,3,96,204,17,25,53],[45,13,8197,13,13,1698,114,33568,4097,210,2048,131,82,19,17665]),
([pw53,pw0,pw1,pw2,pw4,pw5],[32,216,5,21,33,41,1,25,49,165,92,13,53,180,208,212,17,61,65,77,109],[69,49808,1,524704,4234,69,69,65541,11,10768,816,4122,133408,263170,1049642]),
([pw0,pw1,pw2,pw4,pw31,pw54,pw20],[9,49,1,25,33,41,140,220,21,108,5,13,45,57,65,101,129,153,177,257,285,337,341],[21,2621444,65542,4194564,1024,32780,17,1048579,17,4097,8201,34,2048,128,278536,34,34,131082,128,320,584]),
([pw0,pw1,pw2,pw4,pw31,pw55,pw20],[1,49,25,33,5,41,68,53,345,20,108,140,9,37,57,65,81,129,153,177,349,353,357,3],[17,17,131075,17,257,257,3145736,42,4194440,4096,16396,34,8192,64,557060,34,8389122,262150,64,65668,3076]),
([pw56,pw0,pw1,pw2,pw4,pw31,pw20],[1,25,41,5,49,33,64,21,108,140,9,13,29,57,65,129,153,177,233,349,353,3],[9,1024,64,20,64,770,9,9,32773,9,4099,1572896,20,262304,8226,20,2048,147458,20,65542,2097282]),
([pw0,pw1,pw2,pw4,pw31,pw57],[140,224,1,33,5,9,49,104,41,65,3,228,17,25,69,81],[60,533,4101,21,21,1578,330,33960,9257,834,16512,2051,322,67,2177])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p11_D5 : List StD := [
([pw21,pw23,pw10,pw4,pw5,pw20],[5,9,21,49,253,25,53,32,41,81,85,109,153,181,185,189,217,361,365,369],[65553,32786,131096,262164,524336,8195,265,69,1057,16394,70,130,2060,4136,548]),
([pw1,pw21,pw23,pw4,pw31,pw20],[140,5,53,9,1,49,13,41,65,33,117,181,185,189],[512,2058,5128,76,9,258,176,8212,17,258,70,3,164,33,5]),
([pw21,pw2,pw10,pw24,pw5,pw20],[25,33,21,37,41,129,9,53,32,5,13,69,81,85,201,217,281,3],[32778,34,34,34,65539,1024,536,131084,2057,16464,132,321,148,8209,4101]),
([pw27,pw21,pw2,pw24,pw5,pw20],[41,53,25,5,9,13,21,33,32,37,65,81,85,157,281,297,301,305,373],[65536,512,25,82,272,163840,9,262274,16516,9,1058,8228,67,4101,2054]),
([pw42,pw21,pw2,pw24,pw5,pw20],[21,13,25,9,33,41,129,3,32,5,65,69,81,213,281,297,301,305,377,381,385],[65536,138,512,137,264,163840,80,81,16404,270338,1027,2054,524321,1048612,4101]),
([pw41,pw21,pw2,pw24,pw5,pw20],[25,33,9,13,21,129,37,53,32,5,41,65,69,81,85,281],[38,76,1024,148,261,34,34,34,32771,72,2072,4105,144,16897,8209]),
([pw1,pw2,pw33,pw24,pw5,pw20],[25,53,1,9,37,13,21,133,20,5,57,69,81,85,93,129,293,301,373,3],[56,131072,524,74,1033,65536,48,524306,2065,16644,262274,32897,70,8197,4099]),
([pw34,pw1,pw2,pw24,pw5,pw20],[21,33,1,25,9,5,53,133,293,13,57,81,85,129,373,389,393],[18,512,36,16513,8320,18,18,67,1034,36,33025,65800,69,4108,2057]),
([pw37,pw1,pw21,pw2,pw24,pw20],[13,132,9,21,25,41,5,37,53,61,81,133,233,373],[268,2048,521,264,1048,4096,133,100,6,513,96,8210,129,3,50]),
([pw1,pw21,pw2,pw24,pw31,pw20],[140,41,5,9,65,53,3,13,21,33,129,133,373,389],[512,88,14,296,9,8272,6,6176,1025,22,128,17,6,3,33]),
([pw0,pw21,pw10,pw4,pw31,pw20],[9,25,49,5,21,33,65,41,104,1,69,85,153,177,181,213,225,3],[512,16393,131084,32792,2058,65,164,304,65570,69,65,8195,132,4102,1042]),
([pw0,pw1,pw33,pw4,pw31,pw20],[25,49,1,9,37,5,12,20,13,45,57,61,65,69,85,121,153,185,257,397,401,3],[44,262144,2097158,36,16389,512,131082,280,1033,524418,2128,1052673,32786,65539,8209]),
([pw58,pw0,pw1,pw2,pw5,pw20],[5,13,21,25,49,285,9,53,1,37,81,85,93,109,121,153,317,325,397],[4113,112,16402,8212,32792,97,259,133,2057,546,164,65576,262150,131082,1036]),
([pw59,pw0,pw1,pw2,pw4,pw20],[13,25,49,229,9,21,5,1,37,45,61,69,81,85,109,121,153,185,373,405],[72,560,1057,16420,4130,72,137,262156,8202,273,131092,524306,32773,2051,65542]),
([pw60,pw0,pw1,pw2,pw4,pw20],[1,25,41,33,5,49,9,13,21,61,81,85,153,157,373,405],[17,72,128,36,1282,17,17,16389,2051,72,44,32778,36,8706,4102]),
([pw61,pw0,pw1,pw4,pw5,pw20],[21,25,49,249,9,13,5,53,45,65,69,81,85,121,129,297,325,397,409],[72,32816,8228,545,1058,72,16396,137,4106,276,145,262162,131077,65542,2051]),
([pw62,pw0,pw1,pw2,pw4,pw20],[13,25,49,229,9,21,5,37,33,41,45,65,69,81,85,121,129,153,405],[72,304,2081,548,8226,72,137,65548,16394,145,1044,262162,32773,4099,131078]),
([pw0,pw1,pw2,pw63,pw4,pw20],[1,9,49,25,21,37,5,13,45,61,69,81,85,109,121,153,185,229,373,405,413],[67,65,131073,262149,1052673,162,274,65542,524298,512,16420,1064,8212,2072,32780]),
([pw0,pw1,pw38,pw4,pw31,pw20],[1,9,25,49,37,33,20,5,21,29,41,57,65,69,129,153,177,185,241,245,257,397],[262147,1048705,16393,524305,517,34,131082,50,2054,2097224,272,69636,1032,32780,8212]),
([pw64,pw0,pw1,pw2,pw5,pw20],[9,25,93,53,1,33,37,49,21,5,13,29,81,277,317,325,397],[532,33,1216,392,8322,37,20,20,2054,33,265,16387,65608,32834,4106]),
([pw22,pw0,pw10,pw4,pw31,pw20],[25,49,21,33,37,1,9,41,5,29,45,57,69,129,153,177,185,241,337],[256,1024,138,28,2057,393216,8226,20,545,65602,20,32833,130,16387,4101]),
([pw1,pw23,pw10,pw24,pw5,pw20],[25,37,53,21,33,49,13,129,32,9,57,81,101,217,253,281,417],[8210,512,16432,28,1041,130,130,14,32771,65632,12,321,44,4129,2053]),
([pw40,pw1,pw2,pw24,pw5,pw20],[25,37,53,5,13,21,1,9,69,81,85,129,281,301,421,3],[128,18,72,36,6145,18,72,36,24577,18,32774,259,44,1033,517]),
([pw45,pw1,pw23,pw24,pw5,pw20],[9,25,37,13,21,129,53,33,32,1,49,57,81,101,281],[137,44,1024,88,266,37,129,81,2051,36,36,16390,80,8706,4114]),
([pw1,pw23,pw24,pw31,pw20],[140,232,13,25,45,1,33,49,53,389,20,9,133,261,3],[18960,240,340,8219,1024,4101,523,420,43,15]),
([pw40,pw0,pw1,pw4,pw31,pw20],[5,25,49,1,37,41,13,9,45,65,69,85,153,165,401,3],[9,128,36,80,16898,9,32773,9,2051,36,80,8450,36,4102,1042]),
([pw51,pw1,pw2,pw24,pw5,pw20],[9,13,21,25,1,37,53,49,5,29,33,65,69,81,129,165,281,301,373],[132097,34,400,262212,81928,35,145,69,32777,34,2054,4106,84,536,8204]),
([pw52,pw1,pw2,pw24,pw5,pw20],[21,25,37,9,41,13,53,133,1,5,33,49,65,69,81,85,129,165,197,293,305,373],[263168,1572864,2304,2097281,65664,44,536,65,131082,36,4101,8198,81,32786,16387]),
([pw0,pw1,pw10,pw24,pw31,pw20],[25,37,21,33,129,49,3,5,9,41,57,65,69,177,277,281,389,397],[88,65616,128,22,32785,256,552,14,1033,131168,6,10241,6,16417,4099]),
([pw0,pw1,pw2,pw65,pw5,pw20],[25,33,53,93,37,20,41,105,5,9,29,57,69,81,169,201,229,417,425,3],[32778,131096,296,65548,1033,130,546,134,2051,112,524308,4113,262212,16449,8197]),
([pw66,pw0,pw1,pw2,pw5,pw20],[9,25,53,13,21,33,37,49,5,29,81,93,277,317,325,397],[256,33,72,148,4226,33,72,20,2562,33,21,8195,32780,16394,1030]),
([pw50,pw1,pw2,pw24,pw5,pw20],[21,33,25,41,9,5,13,53,133,37,57,65,81,85,129,157,293,373],[18,66048,40,131329,16640,18,18,131,1030,40,2113,32836,137,8204,4101]),
([pw0,pw1,pw67,pw24,pw5,pw20],[13,25,33,53,129,21,37,1,41,57,65,69,81,273,281,289,429,3],[131092,81,128,56,16402,69,73732,44,518,65,1033,2051,40,33026,4106]),
([pw0,pw1,pw2,pw24,pw68,pw20],[25,33,37,53,13,21,1,41,57,65,69,81,129,281,289,357,433,3],[196610,20,64,40,12289,22,32770,42,259,20,524,1029,40,16513,2057]),
([pw61,pw0,pw1,pw24,pw5,pw20],[21,25,37,13,53,297,9,5,49,65,69,81,129,277,281,409],[12,12,12,517,1030,96,128,17,20482,96,17,32802,17,8450,2051]),
([pw62,pw0,pw1,pw2,pw24,pw20],[13,21,25,37,53,233,5,9,49,65,69,81,129,197,277,281,301,373,405],[131090,18,515,18,2054,73728,9,64,36868,9,160,262180,9,1029,16644]),
([pw45,pw0,pw1,pw24,pw31,pw20],[25,33,9,37,20,21,13,41,57,65,69,129,177,281,289,389],[32784,6,16,104,4609,6,16,40,10241,6,6,259,40,16513,1033]),
([pw0,pw46,pw2,pw10,pw4,pw5],[5,21,33,49,9,37,41,53,1,13,25,101,109,181,185,217,221,281,3],[261,2049,8209,131081,131,32804,1028,76,65542,512,72,262178,16408,146,4106]),
([pw27,pw0,pw46,pw2,pw4,pw5],[5,53,13,33,9,49,61,21,1,37,41,45,65,109,117,181,185,221,281],[32785,2048,512,81936,146,265,69,262177,131,76,1064,131082,68,4102,8226]),
([pw0,pw1,pw2,pw69,pw4,pw5],[1,21,49,9,37,5,25,53,3,13,29,45,61,109,121,153,185,281],[41,33,1025,131077,131,536,2048,65548,138,4096,16404,274,32836,322,8198]),
([pw70,pw0,pw1,pw2,pw4,pw5],[1,21,41,33,5,49,9,53,13,25,61,65,109,281,3],[17,72,256,36,16898,17,17,8197,131,72,44,138,36,3074,4102]),
([pw71,pw0,pw1,pw46,pw2,pw4],[5,13,49,53,61,41,21,9,25,29,37,181,233,281],[73,72,256,26,44,2177,513,19,8197,4096,1026,36,18,36,18]),
([pw71,pw0,pw1,pw2,pw4],[41,53,61,229,233,13,49,5,9,21,132,37,73,89,193,221,237,3],[650,786,131110,4163,408,16428,66569,34836,8273,101]),
([pw0,pw1,pw46,pw2,pw4,pw31],[5,49,9,25,41,65,3,53,101,13,21,29,33,181,185,281],[8197,2049,257,32771,257,4096,100,16390,1156,104,26,200,50,512,18]),
([pw0,pw1,pw47,pw10,pw4,pw5],[1,21,49,13,53,33,37,41,85,9,25,109,189,217,269,281],[257,257,4105,32773,19,8288,512,164,18,1096,132,18,16396,26,2054]),
([pw72,pw0,pw1,pw2,pw4,pw5],[5,49,53,37,1,21,41,13,9,109,281,3],[17,256,136,66,36,17,17,1027,37,136,66,36,74,2060,518]),
([pw0,pw1,pw47,pw4,pw31],[1,33,49,140,13,25,41,65,85,9,45,53,145,437,3],[771,417,4109,265,17538,1094,2578,228,56,8276]),
([pw26,pw0,pw1,pw10,pw4,pw31],[21,25,33,37,49,65,85,29,41,3,56,5,9,209,281],[2048,518,546,8210,11,196,224,16464,9,4096,276,13,1056,41,272]),
([pw26,pw11,pw0,pw1,pw2,pw5],[21,49,185,25,33,53,269,37,5,29,85,397,3],[4106,256,28,200,41,1538,22,194,35,20,192,33,20,37,2113]),
([pw73,pw0,pw1,pw2,pw4,pw5],[21,29,33,41,61,13,5,9,49,53,25,37,65,109,281,3],[66,132,2096,264,33793,66,50,16394,515,132,268,517,48,4113,8201]),
([pw74,pw0,pw1,pw2,pw4,pw5],[21,29,61,45,13,41,5,9,25,53,37,49,65,109,281,3],[66,136,20,2336,33025,66,22,16418,515,1036,136,521,20,4101,8225]),
([pw0,pw1,pw2,pw4,pw31,pw75],[1,9,49,33,41,236,29,13,45,129,257,285,337],[11,5121,517,65,65,10,2054,10,258,20,128,32,20,20,32]),
([pw48,pw0,pw1,pw4,pw31,pw20],[9,25,49,13,33,37,257,20,5,29,57,65,69,121,153,177,185,389,397],[256,17,262276,40,34818,17,131140,40,578,65541,17,1027,8204,16390,4106]),
([pw0,pw1,pw10,pw4,pw31,pw30],[1,49,5,21,37,41,92,33,65,129,165,257,337,397],[5,6145,515,5,5,1024,34,24,128,8258,24,320,34,34,24]),
([pw11,pw0,pw1,pw2,pw5,pw30],[5,49,53,93,21,41,173,37,1,33,397],[11,34,34,22,34,9,257,9,9,192,20,512,1092,192,20]),
([pw11,pw0,pw1,pw10,pw31,pw20],[5,25,49,93,21,37,41,188,29,33,57,69,277,285,397,441],[13,68,128,68,4102,9,9,9,259,8192,48,1538,48,49154,2066]),
([pw0,pw1,pw10,pw4,pw31,pw49],[1,49,200,21,37,5,33,41,93,92,129,165,209,441],[33,257,1027,33,257,2048,194,88,4,8706,24,4,130,4102,24]),
([pw0,pw1,pw10,pw4,pw31,pw57],[1,49,5,33,41,104,25,65,212,224,9,37,129,257,337,397,3],[5,24577,4099,5,5,1024,26,40,65608,33282,160,448,18,18,2048]),
([pw11,pw0,pw1,pw2,pw5,pw49],[5,49,53,93,21,200,37,41,1,33,173,217,441],[11,130,130,22,32,9,257,9,9,2624,20,32,4164,1024,20]),
([pw0,pw76,pw1,pw2,pw5,pw20],[9,21,25,1,13,49,5,53,37,81,85,93,169,173,285,317,325,397,425],[2048,73,72,138,1036,16385,8240,262178,4132,273,131,32773,131090,65556,518]),
([pw11,pw0,pw1,pw2,pw5,pw77],[93,5,21,285,33,53,173,37,1,49,397],[3,24,192,36,512,3,257,3,3,24,44,24,1092,192,36]),
([pw78,pw0,pw1,pw2,pw4,pw20],[25,229,33,41,61,13,5,9,49,21,37,81,85,153,157,373,405],[66,132,1072,264,2561,66,50,32778,4099,132,268,65541,48,16401,8201]),
([pw79,pw0,pw1,pw2,pw4,pw20],[25,61,229,45,13,41,5,9,21,37,49,69,81,85,153,373,405],[68,136,18,1312,4353,68,22,32804,8197,522,136,65545,18,2051,16417]),
([pw80,pw0,pw1,pw2,pw4,pw31],[1,5,33,41,165,49,240,13,129],[3,20,64,40,64,3,3,265,3,20,20,20,40,128,40]),
([pw81,pw0,pw1,pw2,pw31,pw20],[5,25,49,285,1,33,41,9,29,37,53,65,81,129,177,277,317],[8197,140,68,68,32774,25,17,17,259,40,40,65546,512,18434,5122]),
([pw56,pw0,pw1,pw2,pw4,pw57],[1,41,5,49,21,33,244,9,13,53,69,129,233,349,353],[5,128,1024,10,592,5,5,2051,5,24608,10,4144,10,256,10]),
([pw82,pw0,pw1,pw2,pw4,pw31],[5,41,1,49,25,65,212,9,244,33,37,53,129,233,3],[5,512,112,26,336,5,5,4099,5,16544,10,10368,42,1024,10])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p11_D4 : List StD := [
([pw21,pw10,pw24,pw31,pw20],[5,65,25,33,9,133,1,37,41,69,85,177,201],[18,73,40,40,4099,18,2054,257,1029,644]),
([pw21,pw67,pw24,pw5,pw20],[25,9,21,33,41,129,5,65,69,81,281,297,305,377,381,385],[6144,40,40,1033,8258,134,259,16404,32785,517]),
([pw21,pw2,pw24,pw68,pw20],[25,9,13,33,41,433,5,65,69,81,213,281,297,305,377,385],[12288,40,40,2057,17412,134,261,82,32785,515]),
([pw1,pw33,pw24,pw31,pw20],[1,25,9,37,5,133,20,13,57,69,85,257,293,301,389],[8192,21,140,262,2113,4136,16418,17,1027,522]),
([pw40,pw1,pw24,pw31,pw20],[5,25,1,37,13,9,69,85,281,301,389,421],[32,5,24,1282,5,24,2562,5,131,74]),
([pw0,pw1,pw65,pw31,pw20],[25,33,37,337,20,41,5,9,13,21,29,57,69,169,201,229],[16394,88,32780,1033,146,518,2051,292,8225,4101]),
([pw0,pw46,pw10,pw4,pw31],[5,9,33,49,65,41,1,21,25,181,213,281],[69,515,2057,1153,22,44,260,26,18,40]),
([pw0,pw1,pw69,pw4,pw31],[1,9,49,65,5,25,37,13,45,121,185,257,281],[19,2057,4101,17,256,1030,194,40,40,580]),
([pw83,pw0,pw1,pw2,pw4],[13,49,229,9,21,5,1,37,45,61,109,121,185,373],[36,280,529,1042,36,69,8198,137,4106,2051]),
([pw84,pw0,pw1,pw2,pw4],[1,41,5,33,49,9,13,373],[5,40,64,18,5,5,131,40,26,18]),
([pw0,pw1,pw2,pw85,pw4],[1,9,49,5,21,37,13,45,61,109,121,185,229,373],[11,9,4097,8197,98,146,2054,256,1060,532]),
([pw72,pw0,pw1,pw4,pw31],[5,49,1,41,13,37,9,281],[5,64,10,48,5,131,5,10,48,10]),
([pw86,pw0,pw1,pw2,pw5],[5,13,21,49,285,9,53,173,37,93,397,425],[521,56,138,2060,49,131,69,274,84,1030]),
([pw87,pw0,pw1,pw2,pw4],[229,13,33,41,61,5,9,49,37,373],[33,68,274,136,33,19,521,68,140,18]),
([pw88,pw0,pw1,pw2,pw4],[61,229,13,45,5,9,41,21,37,49,373],[18,40,5,704,18,7,1090,265,40,5]),
([pw82,pw0,pw10,pw4,pw31],[5,9,65,33,41,1,49,21,37,129],[33,14,88,392,7,529,33,6,6,80])]
def p11_D3 : List StD := []
theorem p11_I3 : LevelN true p11_T 3 p11_D3 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p11_C4x0 : levelOK true p11_T p11_t 3 (p11_D3.map Prod.fst) ((p11_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p11_I4 : LevelN true p11_T 4 p11_D4 := levelStep p11_B p11_W p11_I3 (chunks 32 p11_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p11_C4x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p11_C5x0 : levelOK true p11_T p11_t 4 (p11_D4.map Prod.fst) ((p11_D5.drop (0*32)).take 32) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p11_C5x1 : levelOK true p11_T p11_t 4 (p11_D4.map Prod.fst) ((p11_D5.drop (1*32)).take 32) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p11_C5x2 : levelOK true p11_T p11_t 4 (p11_D4.map Prod.fst) ((p11_D5.drop (2*32)).take 32) = true := by decide +kernel
theorem p11_I5 : LevelN true p11_T 5 p11_D5 := levelStep p11_B p11_W p11_I4 (chunks 32 p11_D5 3 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p11_C5x0
  · exact p11_C5x1
  · exact p11_C5x2
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p11_C6x0 : levelOK true p11_T p11_t 5 (p11_D5.map Prod.fst) ((p11_D6.drop (0*32)).take 32) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p11_C6x1 : levelOK true p11_T p11_t 5 (p11_D5.map Prod.fst) ((p11_D6.drop (1*32)).take 32) = true := by decide +kernel
theorem p11_I6 : LevelN true p11_T 6 p11_D6 := levelStep p11_B p11_W p11_I5 (chunks 32 p11_D6 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p11_C6x0
  · exact p11_C6x1
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p11_C7x0 : levelOK true p11_T p11_t 6 (p11_D6.map Prod.fst) ((p11_D7.drop (0*32)).take 32) = true := by decide +kernel
theorem p11_I7 : LevelN true p11_T 7 p11_D7 := levelStep p11_B p11_W p11_I6 (chunks 32 p11_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p11_C7x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p11_C8x0 : levelOK true p11_T p11_t 7 (p11_D7.map Prod.fst) ((p11_D8.drop (0*32)).take 32) = true := by decide +kernel
theorem p11_I8 : LevelN true p11_T 8 p11_D8 := levelStep p11_B p11_W p11_I7 (chunks 32 p11_D8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p11_C8x0
  ))
theorem p11_L : LowN true p11_R p11_T 9 := lowSearch p11_B p11_I8 (by decide +kernel)
def p12_T : Nat := 0xfffffffffffffff0ffffffaafcfccc00fffffffffffffff0ffffffaafcfccc00
def p12_R : List Nat := [0, 1, 2, 3, 4, 5, 6]
def p12_E : List (Nat × Nat × Nat) := [(0,32,33),(1,8,10),(2,16,20),(3,2,10),(4,2,18),(5,1,33),(6,4,68)]
theorem p12_B : baseOK p12_T p12_R p12_E = true := by decide +kernel
def p12_Z : List SliceD := [(pw8,9,[5, 6, 4, 2, 3, 0])]
theorem p12_Y : ∀ s ∈ p12_Z, SliceN true p12_R p12_T s := by
  unfold p12_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p12_B p11_B p11_L (by decide +kernel),by simp⟩
def p12_C : List (Nat × List Nat) := [(0,[])]
def p12_t : Tabs := (p12_C.map (mkCut true p12_Z),[],[],[[]])
theorem p12_W : TabsP true p12_R p12_T p12_t := ⟨cutsGood p12_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p12_D9 : List StD := [
([pw0,pw1,pw2,pw4,pw5,pw20,pw89],[0],[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1])]
def p12_D8 : List StD := []
theorem p12_I8 : LevelN true p12_T 8 p12_D8 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p12_C9x0 : levelOK true p12_T p12_t 8 (p12_D8.map Prod.fst) ((p12_D9.drop (0*32)).take 32) = true := by decide +kernel
theorem p12_I9 : LevelN true p12_T 9 p12_D9 := levelStep p12_B p12_W p12_I8 (chunks 32 p12_D9 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p12_C9x0
  ))
theorem p12_L : LowN true p12_R p12_T 10 := lowSearch p12_B p12_I9 (by decide +kernel)
def p13_T : Nat := 0xfffefeeefffefeeefffefeeefffefeeefffefeeefffefeeefffefeeefffefeee
def p13_R : List Nat := [0, 1, 2, 3, 4]
def p13_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,8,12),(3,4,12),(4,4,20)]
theorem p13_B : baseOK p13_T p13_R p13_E = true := by decide +kernel
def p13_Z : List SliceD := [(pw7,5,[1, 2, 3, 4])]
theorem p13_Y : ∀ s ∈ p13_Z, SliceN true p13_R p13_T s := by
  unfold p13_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p13_B p6_B p6_L (by decide +kernel),by simp⟩
def p13_C : List (Nat × List Nat) := [(0,[])]
def p13_t : Tabs := (p13_C.map (mkCut true p13_Z),[(1,0),(2,0)],[],[[]])
theorem p13_W : TabsP true p13_R p13_T p13_t := ⟨cutsGood p13_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p13_D5 : List StD := [
([pw0,pw1,pw2,pw4,pw5],[0,1,5],[7,3,3,3,5,5,5,1,1,1])]
def p13_D4 : List StD := []
theorem p13_I4 : LevelN true p13_T 4 p13_D4 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p13_C5x0 : levelOK true p13_T p13_t 4 (p13_D4.map Prod.fst) ((p13_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p13_I5 : LevelN true p13_T 5 p13_D5 := levelStep p13_B p13_W p13_I4 (chunks 32 p13_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p13_C5x0
  ))
theorem p13_L : LowN true p13_R p13_T 6 := lowSearch p13_B p13_I5 (by decide +kernel)
def p14_T : Nat := 0xfeeafcc8feeafcc8feeafcc8feeafcc8feeafcc8feeafcc8feeafcc8feeafcc8
def p14_R : List Nat := [0, 1, 2, 3, 4]
def p14_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,2,6),(3,2,10),(4,1,17)]
theorem p14_B : baseOK p14_T p14_R p14_E = true := by decide +kernel
def p14_Z : List SliceD := [(pw9,4,[1, 2, 3]),(pw6,4,[0, 1, 3, 4]),(pw3,4,[0, 1, 2, 4]),(pw5,5,[0, 1, 2, 3]),(pw12,5,[1, 2, 3, 0])]
theorem p14_Y : ∀ s ∈ p14_Z, SliceN true p14_R p14_T s := by
  unfold p14_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p14_B p1_B p1_L (by decide +kernel),mkSlice (w:=0) p14_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p14_B p5_B p5_L (by decide +kernel),mkSlice (w:=16) p14_B p6_B p6_L (by decide +kernel),mkSlice (w:=0) p14_B p2_B p2_L (by decide +kernel),by simp⟩
def p14_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[])]
def p14_t : Tabs := (p14_C.map (mkCut true p14_Z),[(3,2),(17,16),(21,20),(25,24),(12,8),(6,4),(6,2),(12,4),(10,8),(10,2),(7,4),(12,5),(3,5),(3,1),(6,20),(17,1),(6,18),(21,5),(17,9),(12,9),(6,0),(17,5),(11,8),(3,9),(10,24),(10,18),(25,9),(10,0),(12,20),(12,0),(12,1),(17,0),(10,16),(22,2),(7,0),(6,16),(12,16)],[],[[]])
theorem p14_W : TabsP true p14_R p14_T p14_t := ⟨cutsGood p14_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p14_D6 : List StD := [
([pw0,pw1,pw2,pw4,pw5],[0,1,12,3,4,8,5,17,25,29,9,13,21,33,37],[67,1027,2051,67,4504,25128,5,952,5,5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p14_D5 : List StD := [
([pw0,pw1,pw2,pw10,pw4,pw5],[1,37,21,61,9,25,29,8,5,17,41,45,49,53,57,65,69,73,3],[1029,17,257,2051,17,4132,8192,70,16396,512,66,32808,262274,65544,131082]),
([pw27,pw0,pw1,pw2,pw4,pw5],[5,29,61,1,17,37,21,12,16,25,45,53,57,73,77,81,85],[9,2048,512,34,388,9,16401,1027,9,32848,34,4164,34,65556,8198]),
([pw0,pw1,pw2,pw4,pw28,pw5],[1,25,33,61,13,17,37,4,5,29,53,77,85,89,93,97,101,105,3],[8197,2051,17,257,17,38,16452,1024,32780,34,262274,4106,512,65608,131080]),
([pw29,pw0,pw1,pw2,pw4,pw5],[5,17,61,1,25,29,33,12,16,37,45,53,73,77,85,97,109],[9,2048,18,512,388,9,8195,1057,9,18,65632,32836,18,16390,4132]),
([pw0,pw1,pw2,pw4,pw90,pw5],[21,1,61,29,53,4,9,17,69,25,33,45,57,77,113],[17,8322,2058,66,66,17,1025,17,4101,40,512,388,32,16396,260])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p14_D4 : List StD := [
([pw11,pw0,pw1,pw2,pw5],[1,25,37,69,109,61,117,41,45,53,121,125,129],[261,532,70,44,145,1027,2057,82,4120,42]),
([pw91,pw0,pw1,pw4,pw5],[1,25,37,61,81,117,53,77,121,125,133,137,141,145],[131,82,38,1034,2065,261,521,52,4120,8204])]
def p14_D3 : List StD := []
theorem p14_I3 : LevelN true p14_T 3 p14_D3 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p14_C4x0 : levelOK true p14_T p14_t 3 (p14_D3.map Prod.fst) ((p14_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p14_I4 : LevelN true p14_T 4 p14_D4 := levelStep p14_B p14_W p14_I3 (chunks 32 p14_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p14_C4x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p14_C5x0 : levelOK true p14_T p14_t 4 (p14_D4.map Prod.fst) ((p14_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p14_I5 : LevelN true p14_T 5 p14_D5 := levelStep p14_B p14_W p14_I4 (chunks 32 p14_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p14_C5x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p14_C6x0 : levelOK true p14_T p14_t 5 (p14_D5.map Prod.fst) ((p14_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p14_I6 : LevelN true p14_T 6 p14_D6 := levelStep p14_B p14_W p14_I5 (chunks 32 p14_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p14_C6x0
  ))
theorem p14_L : LowN true p14_R p14_T 7 := lowSearch p14_B p14_I6 (by decide +kernel)
def p15_T : Nat := 0xfeeefac0feeefac0feeefac0feeefac0feeefac0feeefac0feeefac0feeefac0
def p15_R : List Nat := [0, 1, 2, 3, 4]
def p15_E : List (Nat × Nat × Nat) := [(0,8,9),(1,4,6),(2,2,6),(3,1,9),(4,1,17)]
theorem p15_B : baseOK p15_T p15_R p15_E = true := by decide +kernel
def p15_Z : List SliceD := [(pw7,4,[1, 2, 3, 4]),(pw8,4,[0, 3, 2, 4]),(pw6,4,[0, 4, 1, 3]),(pw3,4,[1, 4, 0, 2]),(pw12,4,[2, 3, 0, 1])]
theorem p15_Y : ∀ s ∈ p15_Z, SliceN true p15_R p15_T s := by
  unfold p15_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p15_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p15_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p15_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p15_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p15_B p5_B p5_L (by decide +kernel),by simp⟩
def p15_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[])]
def p15_t : Tabs := (p15_C.map (mkCut true p15_Z),[(9,8),(11,10),(7,5),(21,20),(7,3),(9,1),(17,1),(12,8),(26,24),(11,3),(18,2),(12,4),(28,24),(21,5),(28,20),(26,10),(6,5),(6,3),(6,2),(6,4),(9,3),(17,5),(18,10),(7,4),(18,16),(12,5),(17,16),(18,3),(17,3),(7,2),(9,0),(17,0),(12,10),(9,10),(11,8),(14,8),(9,5),(12,20),(17,20),(21,16),(18,24),(26,16),(12,24),(12,0),(7,1),(12,16),(6,0),(6,1),(7,0),(11,2),(18,0),(18,8),(9,2),(17,2),(17,4)],[],[[]])
theorem p15_W : TabsP true p15_R p15_T p15_t := ⟨cutsGood p15_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p15_D6 : List StD := [
([pw0,pw1,pw2,pw4,pw5],[3,0,4,8,12,16,1,9,17,13,21,29,33,5,25,37,41,45,49,53,57,61],[8391,843,1619,16995,2445,37013,69797,133401,786729,3146801])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p15_D5 : List StD := [
([pw0,pw1,pw21,pw2,pw4,pw5],[25,45,73,5,9,21,29,41,16,1,65,69,77,81,85,89,3],[1048,512,2060,42,137,4096,84,8210,145,68,34,65793,38,16389,32771]),
([pw0,pw1,pw2,pw23,pw4,pw5],[21,41,77,13,17,25,45,97,12,1,65,69,73,81,85,89,93,3],[66564,2072,512,73,42,132,132,8197,38,4096,81,16402,131329,34,32771]),
([pw0,pw1,pw2,pw4,pw24,pw5],[25,73,77,21,41,1,9,17,29,45,61,81,85,101,105],[68,130,8232,16384,49,262,2060,68,21,258,130,4099,512,1033,17]),
([pw0,pw1,pw2,pw4,pw5,pw92],[45,73,77,21,25,9,17,1,29,41,57,81,85,105,109,113],[36,66,9,24592,128,262,2053,32788,36,11,4114,66,1025,9,512]),
([pw0,pw1,pw2,pw10,pw4,pw5],[25,45,73,77,1,37,41,5,21,29,53,65,69,89,93,97,117,121,125,129],[18440,69636,144,131090,262161,524300,32768,42,73,512,38,1029,258,65,8195]),
([pw0,pw1,pw2,pw4,pw28,pw5],[1,73,25,105,29,33,37,41,8,21,69,77,81,85,89,133,137,3],[98305,1027,9,9,9,18,4192,2048,164,18,131330,8198,512,16452,132]),
([pw0,pw1,pw2,pw4,pw5,pw93],[1,45,73,29,5,37,41,25,49,69,77,89,97,105,113,121],[17,517,32771,8193,17,12,34,20544,1024,14,260,12,2114,34,128]),
([pw0,pw1,pw2,pw4,pw90,pw5],[77,1,13,29,53,25,33,45,21,65,73,93,97,105,141,145,149],[2561,6,6,8194,6,16393,65,4097,65,32904,1024,56,256,65680,48]),
([pw0,pw1,pw2,pw4,pw5,pw31],[45,77,1,21,53,97,105,4,25,49,65,73,81,85,93,121,149,153,157,3],[17410,393220,32773,68,68,34,4099,34,524418,9,8720,2048,65553,9,256]),
([pw0,pw1,pw2,pw4,pw5,pw94],[73,77,29,105,1,61,97,0,21,25,57,65,69,89,93,117,161,165,169,3],[18434,36865,24,24,524424,7,196610,66,66,5,262177,5,9248,256,512])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p15_D4 : List StD := [
([pw37,pw0,pw1,pw2,pw4],[73,125,5,9,25,29,21,45,69,77,81],[6,536,49,208,6,259,6,41,1096,33]),
([pw95,pw0,pw1,pw2,pw5],[21,25,77,121,41,173,45,65,69,81,177,181],[73,517,65,19,140,296,26,1060,22,2082]),
([pw91,pw0,pw1,pw4,pw5],[41,73,185,25,173,29,1,69,81,117,181,189,193,197],[642,38,34,11,6148,8272,9,276,13,1041]),
([pw96,pw0,pw2,pw4,pw5],[45,77,185,21,201,1,29,65,85,93,97,105,189,193,205],[642,70,11,1026,12292,9,2080,13,276,16401]),
([pw97,pw1,pw2,pw4,pw5],[1,29,77,73,121,125,45,89,105,137,209,213,217],[517,11,81,257,14,1044,2084,10,4130,176])]
def p15_D3 : List StD := []
theorem p15_I3 : LevelN true p15_T 3 p15_D3 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p15_C4x0 : levelOK true p15_T p15_t 3 (p15_D3.map Prod.fst) ((p15_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p15_I4 : LevelN true p15_T 4 p15_D4 := levelStep p15_B p15_W p15_I3 (chunks 32 p15_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p15_C4x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p15_C5x0 : levelOK true p15_T p15_t 4 (p15_D4.map Prod.fst) ((p15_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p15_I5 : LevelN true p15_T 5 p15_D5 := levelStep p15_B p15_W p15_I4 (chunks 32 p15_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p15_C5x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p15_C6x0 : levelOK true p15_T p15_t 5 (p15_D5.map Prod.fst) ((p15_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p15_I6 : LevelN true p15_T 6 p15_D6 := levelStep p15_B p15_W p15_I5 (chunks 32 p15_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p15_C6x0
  ))
theorem p15_L : LowN true p15_R p15_T 7 := lowSearch p15_B p15_I6 (by decide +kernel)
def p16_T : Nat := 0xeeeaece0eeeaece0eeeaece0eeeaece0eeeaece0eeeaece0eeeaece0eeeaece0
def p16_R : List Nat := [0, 1, 2, 3, 4]
def p16_E : List (Nat × Nat × Nat) := [(0,4,5),(1,4,6),(2,1,5),(3,2,10),(4,1,17)]
theorem p16_B : baseOK p16_T p16_R p16_E = true := by decide +kernel
def p16_Z : List SliceD := []
theorem p16_Y : ∀ s ∈ p16_Z, SliceN true p16_R p16_T s := by
  intro s h
  cases h
def p16_C : List (Nat × List Nat) := []
def p16_t : Tabs := (p16_C.map (mkCut true p16_Z),[(5,4),(10,9),(6,4),(6,2),(5,0),(10,3),(10,2),(17,1),(17,0),(5,1),(10,0),(17,3),(5,9),(6,18),(17,9)],[],[[]])
theorem p16_W : TabsP true p16_R p16_T p16_t := ⟨cutsGood p16_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p16_D4 : List StD := [
([pw0,pw1,pw2,pw4,pw5],[1,9,13,25,29,5,17,21,33,37,41,45,49,53,57],[35,69,137,273,518,1034,2066,4108,8212,16408])]
def p16_D3 : List StD := []
theorem p16_I3 : LevelN true p16_T 3 p16_D3 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p16_C4x0 : levelOK true p16_T p16_t 3 (p16_D3.map Prod.fst) ((p16_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p16_I4 : LevelN true p16_T 4 p16_D4 := levelStep p16_B p16_W p16_I3 (chunks 32 p16_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p16_C4x0
  ))
theorem p16_L : LowN true p16_R p16_T 5 := lowSearch p16_B p16_I4 (by decide +kernel)
def p17_T : Nat := 0xfefefeeefefafc88fefefeeefefafc88fefefeeefefafc88fefefeeefefafc88
def p17_R : List Nat := [0, 1, 2, 3, 4, 5]
def p17_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,8,12),(3,2,10),(4,1,17),(5,1,33)]
theorem p17_B : baseOK p17_T p17_R p17_E = true := by decide +kernel
def p17_Z : List SliceD := [(pw6,6,[0, 1, 5, 3, 4]),(pw2,6,[3, 4, 0, 1, 5]),(pw3,7,[4, 0, 1, 5, 2]),(pw12,7,[3, 1, 0, 5, 2]),(pw14,7,[0, 2, 3, 1, 4]),(pw7,5,[1, 2, 3, 4, 5]),(pw8,5,[0, 2, 4, 3, 5])]
theorem p17_Y : ∀ s ∈ p17_Z, SliceN true p17_R p17_T s := by
  unfold p17_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p17_B p3_B p3_L (by decide +kernel),mkSlice (w:=4) p17_B p13_B p13_L (by decide +kernel),mkSlice (w:=0) p17_B p14_B p14_L (by decide +kernel),mkSlice (w:=0) p17_B p14_B p14_L (by decide +kernel),mkSlice (w:=0) p17_B p15_B p15_L (by decide +kernel),mkSlice (w:=0) p17_B p16_B p16_L (by decide +kernel),mkSlice (w:=0) p17_B p16_B p16_L (by decide +kernel),by simp⟩
def p17_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(2,[262]),(5,[]),(2,[263]),(2,[260]),(3,[260]),(4,[384]),(6,[]),(2,[261]),(4,[385]),(3,[261]),(3,[263]),(4,[386]),(3,[262]),(4,[387]),(2,[261,404])]
def p17_t : Tabs := (p17_C.map (mkCut true p17_Z),[(17,16),(10,8),(3,2),(3,1),(12,8),(13,9),(13,5),(10,2),(17,1),(20,4),(33,1),(34,2),(22,18),(22,6),(33,5),(17,9),(33,9),(34,18),(10,9),(37,36),(12,5),(38,36),(20,6),(12,4),(37,5),(7,6),(19,18),(7,5),(3,0),(3,9),(25,24),(26,24),(20,16),(44,40),(26,18),(25,9),(44,36),(41,9),(52,36),(50,18),(3,18),(33,0),(34,0),(3,5),(41,8),(11,9),(50,16)],[],[[]])
theorem p17_W : TabsP true p17_R p17_T p17_t := ⟨cutsGood p17_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p17_D8 : List StD := [
([pw0,pw1,pw2,pw4,pw5,pw20],[0,4,8,12,16,17,33,41,25,29,37,45,1,5,9,13,21,49,53,57,61,65,69,3],[8450048,65571,772,1096,2192,131107,772,262216,2192,39,1131,524467,1048588,2097172,4194328])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p17_D7 : List StD := [
([pw98,pw0,pw1,pw2,pw4,pw5,pw20],[24,32,36,40,44,3,20,1,5,77,85,0,4,28,29,33,37,41,61,65,69,73,81,89,93,97],[65,8193,6145,99,37,41,2097169,641,4194307,133,521,1296,274,8388628,1048,16793602,98308,33685512,262150,524298,1048588]),
([pw0,pw1,pw21,pw2,pw4,pw5,pw20],[24,44,48,52,9,13,33,56,21,25,41,29,45,49,53,0,4,17,37,61,65,69,73,93,97,101,105,109,3],[4194355,2,33554705,2581,67108945,5145,1,134225954,2598,16610,5162,229632,8389124,262336,268436488,2564,24896,16778504,524420,1048588,2097352]),
([pw99,pw0,pw1,pw2,pw4,pw5,pw20],[24,20,44,60,64,25,33,41,32,9,29,53,0,4,48,5,45,49,61,65,69,85,97,101,113],[260,16385,12289,291,73,145,16777733,8389121,35,73,145,2260996,1062,2124,65684,1058,2120,4194448,262154,524306,1048600]),
([pw22,pw0,pw1,pw2,pw4,pw5,pw20],[44,28,68,72,29,45,53,24,48,13,25,33,0,4,1,5,21,41,61,65,69,77,97,109,113],[257,32769,12289,275,69,41,16777857,2179200,1042,2116,131112,8389121,19,69,41,1042,2116,4194344,262150,524298,1048588])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p17_D6 : List StD := [
([pw0,pw1,pw2,pw100,pw5,pw20],[44,1,5,17,29,37,45,77,85,25,33,129,21,41,97,117,121,125,133,137,141,145,149,153,157],[32775,4234,66066,1186,8386,261,261,131077,261,2584,3112,278600,1572912,6291536,25165920]),
([pw0,pw1,pw2,pw4,pw101,pw20],[24,1,5,17,33,41,93,49,77,85,29,53,45,97,121,125,133,137,141,145,149,153,157,161],[8388615,259,16387,259,259,652,1604,34836,4644,1224,2200,73768,393296,1572960,6291504]),
([pw0,pw1,pw2,pw4,pw5,pw102],[24,44,1,5,29,33,41,77,85,129,17,37,73,93,97,121,125,133,137,141,145,149,153,157],[4111,133,32773,133,133,266,266,65546,266,9744,3616,148032,786480,3145808,12583008]),
([pw103,pw0,pw1,pw21,pw2,pw4,pw5],[21,29,33,9,45,37,93,17,13,41,76,25,53,61,73,165,169,173],[536,528,1024,145,82,52,16648,32768,137,2058,44,65536,131329,66,4100,129,66,36,67,37,8198]),
([pw103,pw0,pw1,pw2,pw4,pw5],[17,37,45,93,165,169,29,33,49,9,13,21,41,25,53,97,101,105,109,137,141,149,157,177,181,185],[4628,5156,34821,2097228,4194438,1584,67601,8396824,131218,262433,16777320,33570850,329,387,1572874])]
def p17_D5 : List StD := []
theorem p17_I5 : LevelN true p17_T 5 p17_D5 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p17_C6x0 : levelOK true p17_T p17_t 5 (p17_D5.map Prod.fst) ((p17_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p17_I6 : LevelN true p17_T 6 p17_D6 := levelStep p17_B p17_W p17_I5 (chunks 32 p17_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p17_C6x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p17_C7x0 : levelOK true p17_T p17_t 6 (p17_D6.map Prod.fst) ((p17_D7.drop (0*32)).take 32) = true := by decide +kernel
theorem p17_I7 : LevelN true p17_T 7 p17_D7 := levelStep p17_B p17_W p17_I6 (chunks 32 p17_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p17_C7x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p17_C8x0 : levelOK true p17_T p17_t 7 (p17_D7.map Prod.fst) ((p17_D8.drop (0*32)).take 32) = true := by decide +kernel
theorem p17_I8 : LevelN true p17_T 8 p17_D8 := levelStep p17_B p17_W p17_I7 (chunks 32 p17_D8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p17_C8x0
  ))
theorem p17_L : LowN true p17_R p17_T 9 := lowSearch p17_B p17_I8 (by decide +kernel)
def p18_T : Nat := 0xfffffffffffffff8ffffececffa8a8a8fffffffffffffff8ffffececffa8a8a8
def p18_R : List Nat := [0, 1, 2, 3, 4, 5, 6]
def p18_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,16,24),(4,8,24),(5,2,34),(6,4,68)]
theorem p18_B : baseOK p18_T p18_R p18_E = true := by decide +kernel
def p18_Z : List SliceD := [(pw3,9,[5, 6, 0, 2, 1, 4])]
theorem p18_Y : ∀ s ∈ p18_Z, SliceN true p18_R p18_T s := by
  unfold p18_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p18_B p17_B p17_L (by decide +kernel),by simp⟩
def p18_C : List (Nat × List Nat) := [(0,[])]
def p18_t : Tabs := (p18_C.map (mkCut true p18_Z),[],[],[[]])
theorem p18_W : TabsP true p18_R p18_T p18_t := ⟨cutsGood p18_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p18_D9 : List StD := [
([pw0,pw1,pw2,pw4,pw5,pw20,pw89],[0],[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1])]
def p18_D8 : List StD := []
theorem p18_I8 : LevelN true p18_T 8 p18_D8 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p18_C9x0 : levelOK true p18_T p18_t 8 (p18_D8.map Prod.fst) ((p18_D9.drop (0*32)).take 32) = true := by decide +kernel
theorem p18_I9 : LevelN true p18_T 9 p18_D9 := levelStep p18_B p18_W p18_I8 (chunks 32 p18_D9 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p18_C9x0
  ))
theorem p18_L : LowN true p18_R p18_T 10 := lowSearch p18_B p18_I9 (by decide +kernel)
def p19_T : Nat := 0xfffffffffffffcf0ffffffc0eeeaccc0fffffffffffffcf0ffffffc0eeeaccc0
def p19_R : List Nat := [0, 1, 2, 3, 4, 5, 6]
def p19_E : List (Nat × Nat × Nat) := [(0,16,17),(1,4,6),(2,2,6),(3,2,10),(4,1,17),(5,8,40),(6,4,68)]
theorem p19_B : baseOK p19_T p19_R p19_E = true := by decide +kernel
def p19_Z : List SliceD := [(pw7,9,[5, 6, 1, 2, 3, 4])]
theorem p19_Y : ∀ s ∈ p19_Z, SliceN true p19_R p19_T s := by
  unfold p19_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p19_B p17_B p17_L (by decide +kernel),by simp⟩
def p19_C : List (Nat × List Nat) := [(0,[])]
def p19_t : Tabs := (p19_C.map (mkCut true p19_Z),[],[],[[]])
theorem p19_W : TabsP true p19_R p19_T p19_t := ⟨cutsGood p19_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p19_D9 : List StD := [
([pw0,pw1,pw2,pw4,pw5,pw20,pw89],[0],[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1])]
def p19_D8 : List StD := []
theorem p19_I8 : LevelN true p19_T 8 p19_D8 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p19_C9x0 : levelOK true p19_T p19_t 8 (p19_D8.map Prod.fst) ((p19_D9.drop (0*32)).take 32) = true := by decide +kernel
theorem p19_I9 : LevelN true p19_T 9 p19_D9 := levelStep p19_B p19_W p19_I8 (chunks 32 p19_D9 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p19_C9x0
  ))
theorem p19_L : LowN true p19_R p19_T 10 := lowSearch p19_B p19_I9 (by decide +kernel)
def p20_T : Nat := 0xffffffffffffffecfff8fff8fff8a8a8ffffffffffffffecfff8fff8fff8a8a8
def p20_R : List Nat := [0, 1, 2, 3, 4, 5, 6]
def p20_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,16,24),(4,4,20),(5,4,36),(6,2,66)]
theorem p20_B : baseOK p20_T p20_R p20_E = true := by decide +kernel
def p20_Z : List SliceD := [(pw12,9,[5, 6, 0, 1, 2, 3])]
theorem p20_Y : ∀ s ∈ p20_Z, SliceN true p20_R p20_T s := by
  unfold p20_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p20_B p17_B p17_L (by decide +kernel),by simp⟩
def p20_C : List (Nat × List Nat) := [(0,[])]
def p20_t : Tabs := (p20_C.map (mkCut true p20_Z),[],[],[[]])
theorem p20_W : TabsP true p20_R p20_T p20_t := ⟨cutsGood p20_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p20_D9 : List StD := [
([pw0,pw1,pw2,pw4,pw5,pw20,pw89],[0],[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1])]
def p20_D8 : List StD := []
theorem p20_I8 : LevelN true p20_T 8 p20_D8 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p20_C9x0 : levelOK true p20_T p20_t 8 (p20_D8.map Prod.fst) ((p20_D9.drop (0*32)).take 32) = true := by decide +kernel
theorem p20_I9 : LevelN true p20_T 9 p20_D9 := levelStep p20_B p20_W p20_I8 (chunks 32 p20_D9 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p20_C9x0
  ))
theorem p20_L : LowN true p20_R p20_T 10 := lowSearch p20_B p20_I9 (by decide +kernel)
def p21_T : Nat := 0xfefefeeefefafec8fefefeeefefafec8fefefeeefefafec8fefefeeefefafec8
def p21_R : List Nat := [0, 1, 2, 3, 4, 5]
def p21_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,2,6),(3,1,9),(4,1,17),(5,1,33)]
theorem p21_B : baseOK p21_T p21_R p21_E = true := by decide +kernel
def p21_Z : List SliceD := [(pw12,7,[1, 0, 3, 2, 5])]
theorem p21_Y : ∀ s ∈ p21_Z, SliceN true p21_R p21_T s := by
  unfold p21_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p21_B p9_B p9_L (by decide +kernel),by simp⟩
def p21_C : List (Nat × List Nat) := [(0,[])]
def p21_t : Tabs := (p21_C.map (mkCut true p21_Z),[],[],[[]])
theorem p21_W : TabsP true p21_R p21_T p21_t := ⟨cutsGood p21_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p21_D7 : List StD := [
([pw0,pw1,pw2,pw4,pw5,pw20],[0],[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1])]
def p21_D6 : List StD := []
theorem p21_I6 : LevelN true p21_T 6 p21_D6 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p21_C7x0 : levelOK true p21_T p21_t 6 (p21_D6.map Prod.fst) ((p21_D7.drop (0*32)).take 32) = true := by decide +kernel
theorem p21_I7 : LevelN true p21_T 7 p21_D7 := levelStep p21_B p21_W p21_I6 (chunks 32 p21_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p21_C7x0
  ))
theorem p21_L : LowN true p21_R p21_T 8 := lowSearch p21_B p21_I7 (by decide +kernel)
def p22_T : Nat := 0xfffffffffffffcfcffffffecffa0f0a0fffffffffffffcfcffffffecffa0f0a0
def p22_R : List Nat := [0, 1, 2, 3, 4, 5, 6]
def p22_E : List (Nat × Nat × Nat) := [(0,4,5),(1,32,34),(2,1,5),(3,4,12),(4,8,24),(5,2,34),(6,2,66)]
theorem p22_B : baseOK p22_T p22_R p22_E = true := by decide +kernel
def p22_Z : List SliceD := [(pw7,8,[6, 5, 3, 4, 2, 1]),(pw104,7,[5, 4, 6, 1, 3]),(pw105,5,[5, 6, 1, 4]),(pw106,7,[2, 3, 4, 5, 0]),(pw107,7,[2, 6, 5, 1, 0])]
theorem p22_Y : ∀ s ∈ p22_Z, SliceN true p22_R p22_T s := by
  unfold p22_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p22_B p21_B p21_L (by decide +kernel),mkSlice (w:=1) p22_B p9_B p9_L (by decide +kernel),mkSlice (w:=0) p22_B p8_B p8_L (by decide +kernel),mkSlice (w:=0) p22_B p14_B p14_L (by decide +kernel),mkSlice (w:=0) p22_B p14_B p14_L (by decide +kernel),by simp⟩
def p22_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[])]
def p22_t : Tabs := (p22_C.map (mkCut true p22_Z),[(7,6),(5,4),(5,0),(7,3),(5,1),(12,4),(74,72),(14,4),(24,10),(34,32),(5,17),(37,33),(5,65),(12,20),(24,0),(40,32),(66,10),(48,32),(24,8),(66,18),(96,32),(66,2)],[],[[]])
theorem p22_W : TabsP true p22_R p22_T p22_t := ⟨cutsGood p22_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p22_D9 : List StD := [
([pw0,pw1,pw2,pw4,pw5,pw20,pw89],[4,12,16,0,21,8,25,1,13,37,5,9,17,29,33,41,45,49,53,57,61,65,69,73,77,81,85],[1160,2185,9,9,9,9,4353,8306,16390,578,578,21,32773,65793,131075,786484,1048628,2097206,12582916,16777222,100663298])]
def p22_D8 : List StD := []
theorem p22_I8 : LevelN true p22_T 8 p22_D8 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p22_C9x0 : levelOK true p22_T p22_t 8 (p22_D8.map Prod.fst) ((p22_D9.drop (0*32)).take 32) = true := by decide +kernel
theorem p22_I9 : LevelN true p22_T 9 p22_D9 := levelStep p22_B p22_W p22_I8 (chunks 32 p22_D9 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p22_C9x0
  ))
theorem p22_L : LowN true p22_R p22_T 10 := lowSearch p22_B p22_I9 (by decide +kernel)
def p23_T : Nat := 0xffffffffffffffccfffffff8f8f88888ffffffffffffffccfffffff8f8f88888
def p23_R : List Nat := [0, 1, 2, 3, 4, 5, 6]
def p23_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,16,20),(3,32,40),(4,4,20),(5,4,36),(6,2,66)]
theorem p23_B : baseOK p23_T p23_R p23_E = true := by decide +kernel
def p23_Z : List SliceD := [(pw7,9,[6, 5, 4, 2, 3, 1])]
theorem p23_Y : ∀ s ∈ p23_Z, SliceN true p23_R p23_T s := by
  unfold p23_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p23_B p11_B p11_L (by decide +kernel),by simp⟩
def p23_C : List (Nat × List Nat) := [(0,[])]
def p23_t : Tabs := (p23_C.map (mkCut true p23_Z),[],[],[[]])
theorem p23_W : TabsP true p23_R p23_T p23_t := ⟨cutsGood p23_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p23_D9 : List StD := [
([pw0,pw1,pw2,pw4,pw5,pw20,pw89],[0],[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1])]
def p23_D8 : List StD := []
theorem p23_I8 : LevelN true p23_T 8 p23_D8 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p23_C9x0 : levelOK true p23_T p23_t 8 (p23_D8.map Prod.fst) ((p23_D9.drop (0*32)).take 32) = true := by decide +kernel
theorem p23_I9 : LevelN true p23_T 9 p23_D9 := levelStep p23_B p23_W p23_I8 (chunks 32 p23_D9 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p23_C9x0
  ))
theorem p23_L : LowN true p23_R p23_T 10 := lowSearch p23_B p23_I9 (by decide +kernel)
def p24_T : Nat := 0xfeeefeeefeeefac0feeefeeefeeefac0feeefeeefeeefac0feeefeeefeeefac0
def p24_R : List Nat := [0, 1, 2, 3, 4, 5]
def p24_E : List (Nat × Nat × Nat) := [(0,8,9),(1,4,6),(2,2,6),(3,1,9),(4,1,17),(5,1,33)]
theorem p24_B : baseOK p24_T p24_R p24_E = true := by decide +kernel
def p24_Z : List SliceD := [(pw12,7,[0, 1, 2, 3, 5])]
theorem p24_Y : ∀ s ∈ p24_Z, SliceN true p24_R p24_T s := by
  unfold p24_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p24_B p15_B p15_L (by decide +kernel),by simp⟩
def p24_C : List (Nat × List Nat) := [(0,[])]
def p24_t : Tabs := (p24_C.map (mkCut true p24_Z),[],[],[[]])
theorem p24_W : TabsP true p24_R p24_T p24_t := ⟨cutsGood p24_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p24_D7 : List StD := [
([pw0,pw1,pw2,pw4,pw5,pw20],[0],[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1])]
def p24_D6 : List StD := []
theorem p24_I6 : LevelN true p24_T 6 p24_D6 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p24_C7x0 : levelOK true p24_T p24_t 6 (p24_D6.map Prod.fst) ((p24_D7.drop (0*32)).take 32) = true := by decide +kernel
theorem p24_I7 : LevelN true p24_T 7 p24_D7 := levelStep p24_B p24_W p24_I6 (chunks 32 p24_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p24_C7x0
  ))
theorem p24_L : LowN true p24_R p24_T 8 := lowSearch p24_B p24_I7 (by decide +kernel)
def p25_T : Nat := 0xfeeefaeafeccfac8feeefaeafeccfac8feeefaeafeccfac8feeefaeafeccfac8
def p25_R : List Nat := [0, 1, 2, 3, 4, 5]
def p25_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,2,6),(3,1,9),(4,2,18),(5,1,33)]
theorem p25_B : baseOK p25_T p25_R p25_E = true := by decide +kernel
def p25_Z : List SliceD := [(pw13,4,[1, 2, 3, 4]),(pw108,4,[0, 3, 2, 5]),(pw6,5,[0, 1, 4, 3, 5]),(pw3,5,[1, 0, 5, 4, 2])]
theorem p25_Y : ∀ s ∈ p25_Z, SliceN true p25_R p25_T s := by
  unfold p25_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p25_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p25_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p25_B p10_B p10_L (by decide +kernel),mkSlice (w:=0) p25_B p10_B p10_L (by decide +kernel),by simp⟩
def p25_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[])]
def p25_t : Tabs := (p25_C.map (mkCut true p25_Z),[(9,8),(6,4),(3,2),(3,1),(6,2),(37,36),(25,24),(12,8),(9,1),(26,24),(6,36),(12,4),(12,24),(33,5),(26,10),(18,2),(12,36),(33,17)],[],[[]])
theorem p25_W : TabsP true p25_R p25_T p25_t := ⟨cutsGood p25_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p25_D6 : List StD := [
([pw0,pw1,pw2,pw4,pw5,pw20],[0,4,1,5,17,33,8,9,13,21,29,37,12,25,41,45,49,53,57,61,65,69],[396,533,133,8197,517,1304,2090,2058,16395,33840,65618,131153,786466,1052673,2097155])]
def p25_D5 : List StD := []
theorem p25_I5 : LevelN true p25_T 5 p25_D5 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p25_C6x0 : levelOK true p25_T p25_t 5 (p25_D5.map Prod.fst) ((p25_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p25_I6 : LevelN true p25_T 6 p25_D6 := levelStep p25_B p25_W p25_I5 (chunks 32 p25_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p25_C6x0
  ))
theorem p25_L : LowN true p25_R p25_T 7 := lowSearch p25_B p25_I6 (by decide +kernel)
def p26_T : Nat := 0xfeeefaeafeeefac0feeefaeafeeefac0feeefaeafeeefac0feeefaeafeeefac0
def p26_R : List Nat := [0, 1, 2, 3, 4, 5]
def p26_E : List (Nat × Nat × Nat) := [(0,8,9),(1,4,6),(2,2,6),(3,1,9),(4,1,17),(5,1,33)]
theorem p26_B : baseOK p26_T p26_R p26_E = true := by decide +kernel
def p26_Z : List SliceD := [(pw14,7,[0, 1, 2, 3, 4])]
theorem p26_Y : ∀ s ∈ p26_Z, SliceN true p26_R p26_T s := by
  unfold p26_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p26_B p15_B p15_L (by decide +kernel),by simp⟩
def p26_C : List (Nat × List Nat) := [(0,[])]
def p26_t : Tabs := (p26_C.map (mkCut true p26_Z),[],[],[[]])
theorem p26_W : TabsP true p26_R p26_T p26_t := ⟨cutsGood p26_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p26_D7 : List StD := [
([pw0,pw1,pw2,pw4,pw5,pw20],[0],[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1])]
def p26_D6 : List StD := []
theorem p26_I6 : LevelN true p26_T 6 p26_D6 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p26_C7x0 : levelOK true p26_T p26_t 6 (p26_D6.map Prod.fst) ((p26_D7.drop (0*32)).take 32) = true := by decide +kernel
theorem p26_I7 : LevelN true p26_T 7 p26_D7 := levelStep p26_B p26_W p26_I6 (chunks 32 p26_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p26_C7x0
  ))
theorem p26_L : LowN true p26_R p26_T 8 := lowSearch p26_B p26_I7 (by decide +kernel)
def p27_T : Nat := 0xfeeefaeafeeefaeafeeefaeafeeefaeafeeefaeafeeefaeafeeefaeafeeefaea
def p27_R : List Nat := [0, 1, 2, 3, 4]
def p27_E : List (Nat × Nat × Nat) := [(0,0,1),(1,4,6),(2,2,6),(3,4,12),(4,2,18)]
theorem p27_B : baseOK p27_T p27_R p27_E = true := by decide +kernel
def p27_Z : List SliceD := []
theorem p27_Y : ∀ s ∈ p27_Z, SliceN true p27_R p27_T s := by
  intro s h
  cases h
def p27_C : List (Nat × List Nat) := []
def p27_t : Tabs := (p27_C.map (mkCut true p27_Z),[(1,0),(1,2),(3,0),(1,4),(5,0),(1,8),(9,0),(1,16),(17,0),(12,8),(6,2),(6,4),(18,24),(12,4),(18,2),(18,0),(12,24),(18,10)],[],[[]])
theorem p27_W : TabsP true p27_R p27_T p27_t := ⟨cutsGood p27_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p27_D4 : List StD := [
([pw0,pw1,pw2,pw4,pw5],[1,37,57,41,45,53,5,9,13,17,21,25,29,33,49,61,65,69],[193,769,3073,12289,10,16432,32788,10,65542,131108])]
def p27_D3 : List StD := []
theorem p27_I3 : LevelN true p27_T 3 p27_D3 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p27_C4x0 : levelOK true p27_T p27_t 3 (p27_D3.map Prod.fst) ((p27_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p27_I4 : LevelN true p27_T 4 p27_D4 := levelStep p27_B p27_W p27_I3 (chunks 32 p27_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p27_C4x0
  ))
theorem p27_L : LowN true p27_R p27_T 5 := lowSearch p27_B p27_I4 (by decide +kernel)
def p28_T : Nat := 0xfeeefaaafcecf8a8feeefaaafcecf8a8feeefaaafcecf8a8feeefaaafcecf8a8
def p28_R : List Nat := [0, 1, 2, 3, 4, 5]
def p28_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,4,12),(4,2,18),(5,1,33)]
theorem p28_B : baseOK p28_T p28_R p28_E = true := by decide +kernel
def p28_Z : List SliceD := [(pw4,5,[2, 1, 0, 5, 4]),(pw3,5,[0, 1, 4, 2, 5]),(pw5,5,[1, 0, 2, 3, 5]),(pw12,5,[0, 2, 3, 1, 5]),(pw14,5,[1, 2, 0, 3, 4]),(pw108,4,[0, 2, 3, 5]),(pw15,4,[0, 1, 4, 5])]
theorem p28_Y : ∀ s ∈ p28_Z, SliceN true p28_R p28_T s := by
  unfold p28_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=8) p28_B p27_B p27_L (by decide +kernel),mkSlice (w:=0) p28_B p10_B p10_L (by decide +kernel),mkSlice (w:=16) p28_B p27_B p27_L (by decide +kernel),mkSlice (w:=0) p28_B p10_B p10_L (by decide +kernel),mkSlice (w:=0) p28_B p16_B p16_L (by decide +kernel),mkSlice (w:=0) p28_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p28_B p5_B p5_L (by decide +kernel),by simp⟩
def p28_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[])]
def p28_t : Tabs := (p28_C.map (mkCut true p28_Z),[(5,4),(18,16),(3,2),(3,1),(12,8),(5,1),(12,4),(11,10),(18,2),(21,20),(33,1),(33,0),(22,20),(14,10),(18,48),(12,40),(41,1),(49,1),(33,8),(33,16),(12,10),(3,9),(5,17),(18,10)],[],[[]])
theorem p28_W : TabsP true p28_R p28_T p28_t := ⟨cutsGood p28_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p28_D6 : List StD := [
([pw0,pw1,pw2,pw4,pw5,pw20],[0,4,1,25,8,12,5,17,33,16,9,13,21,20,24,29,37,41,45,49,53,57,61,3],[3140,5252,32783,65844,8782340,1573056,75,2352,2105920,4107,432,4211328,11,11,304])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p28_D5 : List StD := [
([pw26,pw0,pw1,pw2,pw4,pw5],[5,17,25,33,13,21,41,45,9,65,69,73,77,81,85,89,93],[256,17,34,580,1096,17,34,2180,4232,8195,16389,17,34,32778,65548])]
def p28_D4 : List StD := []
theorem p28_I4 : LevelN true p28_T 4 p28_D4 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p28_C5x0 : levelOK true p28_T p28_t 4 (p28_D4.map Prod.fst) ((p28_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p28_I5 : LevelN true p28_T 5 p28_D5 := levelStep p28_B p28_W p28_I4 (chunks 32 p28_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p28_C5x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p28_C6x0 : levelOK true p28_T p28_t 5 (p28_D5.map Prod.fst) ((p28_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p28_I6 : LevelN true p28_T 6 p28_D6 := levelStep p28_B p28_W p28_I5 (chunks 32 p28_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p28_C6x0
  ))
theorem p28_L : LowN true p28_R p28_T 7 := lowSearch p28_B p28_I6 (by decide +kernel)
def p29_T : Nat := 0xffffffffffffeaeafffcffccfff0c0c0ffffffffffffeaeafffcffccfff0c0c0
def p29_R : List Nat := [0, 1, 2, 3, 4, 5, 6]
def p29_E : List (Nat × Nat × Nat) := [(0,64,65),(1,4,6),(2,2,6),(3,16,24),(4,4,20),(5,2,34),(6,1,65)]
theorem p29_B : baseOK p29_T p29_R p29_E = true := by decide +kernel
def p29_Z : List SliceD := [(pw7,8,[4, 5, 1, 2, 3, 6]),(pw109,7,[1, 3, 4, 2, 5]),(pw6,7,[5, 6, 4, 3, 0, 1]),(pw8,7,[4, 6, 5, 3, 0, 2]),(pw3,8,[6, 1, 2, 4, 5, 0]),(pw12,7,[5, 1, 6, 0, 2, 3]),(pw14,7,[4, 2, 6, 0, 1, 3]),(pw110,4,[5, 6, 0, 3]),(pw111,5,[4, 5, 6, 0, 3]),(pw112,4,[4, 6, 0, 3]),(pw113,4,[4, 6, 0, 2]),(pw114,4,[5, 6, 0, 3])]
theorem p29_Y : ∀ s ∈ p29_Z, SliceN true p29_R p29_T s := by
  unfold p29_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p29_B p24_B p24_L (by decide +kernel),mkSlice (w:=1) p29_B p15_B p15_L (by decide +kernel),mkSlice (w:=0) p29_B p25_B p25_L (by decide +kernel),mkSlice (w:=0) p29_B p25_B p25_L (by decide +kernel),mkSlice (w:=0) p29_B p26_B p26_L (by decide +kernel),mkSlice (w:=0) p29_B p28_B p28_L (by decide +kernel),mkSlice (w:=0) p29_B p28_B p28_L (by decide +kernel),mkSlice (w:=0) p29_B p5_B p5_L (by decide +kernel),mkSlice (w:=4) p29_B p27_B p27_L (by decide +kernel),mkSlice (w:=2) p29_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p29_B p5_B p5_L (by decide +kernel),mkSlice (w:=4) p29_B p5_B p5_L (by decide +kernel),by simp⟩
def p29_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(0,[393]),(1,[385]),(7,[]),(8,[]),(0,[257]),(1,[257]),(4,[389]),(6,[513]),(9,[]),(1,[513]),(0,[261]),(4,[517]),(10,[]),(0,[385]),(1,[393]),(4,[393]),(1,[525]),(0,[389]),(4,[521]),(5,[513]),(11,[]),(1,[521]),(0,[129]),(4,[525]),(0,[257,410]),(1,[257,406]),(1,[525,22]),(0,[389,282]),(0,[129,536]),(1,[521,150]),(0,[129,538])]
def p29_t : Tabs := (p29_C.map (mkCut true p29_Z),[(67,66),(65,64),(69,68),(73,72),(65,0),(20,16),(6,4),(6,2),(26,18),(14,4),(50,48),(26,10),(34,2),(67,3),(65,1),(44,36),(20,4),(52,48),(44,12),(69,5),(65,9),(52,36),(50,18),(80,16),(96,32),(7,5),(7,3),(14,12),(38,36),(14,10),(6,18),(24,8),(24,16),(40,32),(40,8),(73,9),(65,17),(51,49),(25,17),(27,11),(24,18),(6,10),(65,5),(34,18),(67,19),(65,33),(34,32),(35,33),(34,66),(21,17),(21,5),(22,18),(65,3),(20,68),(53,49),(40,36),(40,12),(24,0),(20,36),(69,37),(53,37),(34,48),(6,0),(20,0),(70,66),(7,1),(21,1),(35,3),(20,32),(20,64),(34,0),(70,68),(14,8),(50,16),(25,16),(24,17),(26,16),(6,5),(7,4),(6,3),(7,2),(52,37),(53,36),(50,19),(51,18),(20,48),(40,0),(80,48),(26,2),(44,4)],[],[[]])
theorem p29_W : TabsP true p29_R p29_T p29_t := ⟨cutsGood p29_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p29_D9 : List StD := [
([pw0,pw1,pw2,pw4,pw5,pw20,pw89],[4,0,3,8,12,16,20,24,1,21,25,33,53,45,29,41,61,5,9,13,17,37,49,57,65,69,73,77,81,85,89,93,97],[131330,262402,524546,3,3,1048835,17948,2100272,42068,4228244,8392721,68136,16794188,100663948,134221833,10336,67616,268435489,1610621124,2147487809,4294971521])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p29_D8 : List StD := [
([pw0,pw1,pw2,pw10,pw4,pw5,pw20,pw89],[32,36,5,8,12,28,25,29,40,45,53,1,0,9,13,17,49,65,85,97,101,105,109,113,117,121,125,129,133,137,141,145],[1050692,2105476,6180,16420,37,37,32805,24,8,4194384,594,8388688,1105,16,16777352,33554570,392,393,258,67109378,258,1027,131586,939589632,1073742849,262658,2147483651,525313]),
([pw0,pw1,pw2,pw4,pw5,pw93,pw20,pw89],[36,48,20,5,29,52,41,129,45,44,60,1,21,49,53,0,8,56,9,13,17,65,69,81,105,133,149,153,157,161,165,169,173,177,181,3],[67110984,17039384,134742152,268435724,35336,522,1049098,4177,536871137,69,4,139329,16451,1073742001,4373,34359803921,4194321,2147483667,292,161,33554592,8388770,2097153,4294968580,8589934854,9217,16387,17179870210]),
([pw0,pw1,pw2,pw4,pw5,pw20,pw30,pw89],[64,36,5,29,129,24,72,65,185,60,45,68,21,53,1,33,57,61,76,9,13,17,41,49,69,81,89,93,105,113,153,169,189,193],[4294983940,268959756,1074790420,2181,2053,16389,2099205,536875272,33104,4195712,290,32,73987,131160,5256,16777768,4618,2147484169,1106,131184,32848,33554513,75497634,263810,134226051,2,8589934625,73729]),
([pw0,pw1,pw2,pw4,pw5,pw31,pw20,pw89],[36,84,20,5,25,129,60,21,88,65,80,77,185,9,61,0,40,1,13,17,33,41,69,81,85,97,101,109,153,197,201,205,209,213],[67239960,536879240,268697640,1073742348,41992,1034,525322,2147487888,135266352,2097748,4113,4113,4294967379,16801,196,4,4194433,2179,292,289,16672,8388898,64,16777732,8589935110,65601,2051,33556546]),
([pw0,pw1,pw2,pw4,pw5,pw20,pw32,pw89],[60,92,5,25,129,65,69,100,96,108,104,9,73,77,185,12,1,13,17,29,41,49,57,81,101,109,133,145,153,217,221,225,229,233,237,3],[16842764,536873028,268566548,294,262,2054,262406,16457,33554457,1048617,16393,34359771145,4194315,1073742033,1121,2147487809,524289,8259,4294968464,4241,67109009,8388754,8589935137,545,134218274,2097153,17179869187,8195]),
([pw0,pw1,pw2,pw4,pw5,pw20,pw115,pw89],[60,112,20,5,25,29,129,89,120,57,85,36,108,116,21,185,61,93,1,9,13,17,33,69,81,97,101,105,109,117,153,169,209,241,245,3],[67371032,134742056,1074790472,8589935628,8330,8202,2105354,49200,272629840,17179870229,34960,34833,4294969875,536936544,17445,8392864,20513,2147488291,324,65984,34359738688,16777538,133,1,132102,4,33555075,131586])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p29_D7 : List StD := [
([pw116,pw0,pw1,pw4,pw5,pw20,pw89],[5,29,57,133,137,249,253,36,60,128,41,45,49,129,1,21,124,13,53,69,105,117,141,153,181,257,261,265,269,273,277],[1064963,33826,2105354,34882,528402,33816582,67125281,8519689,134217921,268435729,66053,424,3168,5168,420,10312,12312,4194828,536871376,1073742532,16778004]),
([pw117,pw0,pw2,pw4,pw5,pw20,pw89],[132,5,25,57,125,129,249,281,136,65,69,73,133,9,77,185,13,41,61,85,93,97,101,109,141,153,261,285,289,293],[4202502,33860,8392740,131604,34948,134234124,67117122,33620002,275,387,267,268697696,1616,3264,16457,4656,6304,16777257,537395344,1048601,2097289]),
([pw118,pw0,pw1,pw2,pw5,pw20,pw115,pw89],[21,25,93,129,89,29,57,85,133,185,140,144,148,5,169,173,209,229,245,297,301,305,309,313,317,321,325,329,333,337,341,345,349],[1572872,2097162,41,264,264,1024,76,12582914,50331649,201326720,805306384,14336,68,35,262274,530,514,65542,33,1073741841,33,16389,32912,131072,68,2147483648,4294967316,68]),
([pw118,pw0,pw1,pw2,pw5,pw20,pw89],[144,148,5,129,93,25,29,229,345,21,57,61,85,89,185,33,41,53,69,77,97,153,353,357],[2097167,49192,2632,6280,10504,1049,7,7,7,7,1031,16992,4260000,24864,131089,4800,8651072,524305,12673,1041,1048593])]
def p29_D6 : List StD := []
theorem p29_I6 : LevelN true p29_T 6 p29_D6 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p29_C7x0 : levelOK true p29_T p29_t 6 (p29_D6.map Prod.fst) ((p29_D7.drop (0*32)).take 32) = true := by decide +kernel
theorem p29_I7 : LevelN true p29_T 7 p29_D7 := levelStep p29_B p29_W p29_I6 (chunks 32 p29_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p29_C7x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p29_C8x0 : levelOK true p29_T p29_t 7 (p29_D7.map Prod.fst) ((p29_D8.drop (0*32)).take 32) = true := by decide +kernel
theorem p29_I8 : LevelN true p29_T 8 p29_D8 := levelStep p29_B p29_W p29_I7 (chunks 32 p29_D8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p29_C8x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p29_C9x0 : levelOK true p29_T p29_t 8 (p29_D8.map Prod.fst) ((p29_D9.drop (0*32)).take 32) = true := by decide +kernel
theorem p29_I9 : LevelN true p29_T 9 p29_D9 := levelStep p29_B p29_W p29_I8 (chunks 32 p29_D9 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p29_C9x0
  ))
theorem p29_L : LowN true p29_R p29_T 10 := lowSearch p29_B p29_I9 (by decide +kernel)
def ptopT : Nat := 0xfffffffffffffffffffffefefffffafafffefffefffefffafefefefeeeccaa00
def ptopR : List Nat := [0, 1, 2, 3, 4, 5, 6, 7]
def ptopE : List (Nat × Nat × Nat) := [(0,8,9),(1,16,18),(2,32,36),(3,1,9),(4,2,18),(5,1,33),(6,1,65),(7,1,129)]
theorem ptopB : baseOK ptopT ptopR ptopE = true := by decide +kernel
def ptopZ : List SliceD := [(pw8,10,[4, 5, 3, 2, 0, 7, 6]),(pw6,10,[1, 4, 5, 3, 6, 7, 0]),(pw7,10,[3, 1, 4, 5, 6, 2, 7]),(pw3,10,[1, 4, 5, 6, 0, 2, 7]),(pw12,10,[1, 3, 5, 2, 7, 6, 0]),(pw14,10,[1, 4, 3, 2, 0, 6, 7]),(pw119,10,[3, 1, 4, 2, 7, 5, 0])]
theorem ptopY : ∀ s ∈ ptopZ, SliceN true ptopR ptopT s := by
  unfold ptopZ
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) ptopB p12_B p12_L (by decide +kernel),mkSlice (w:=0) ptopB p18_B p18_L (by decide +kernel),mkSlice (w:=0) ptopB p19_B p19_L (by decide +kernel),mkSlice (w:=0) ptopB p20_B p20_L (by decide +kernel),mkSlice (w:=0) ptopB p22_B p22_L (by decide +kernel),mkSlice (w:=0) ptopB p23_B p23_L (by decide +kernel),mkSlice (w:=0) ptopB p29_B p29_L (by decide +kernel),by simp⟩
def ptopC : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(0,[649]),(1,[653]),(2,[769]),(5,[777]),(6,[513]),(4,[517])]
def ptopt : Tabs := (ptopC.map (mkCut true ptopZ),[(19,17),(18,16),(9,12),(9,8),(33,32),(25,24),(65,64),(129,128),(18,20),(26,24),(34,32),(82,80),(162,160),(44,40),(36,32),(52,48),(68,64),(132,128),(25,17),(9,1),(104,96),(132,12),(176,160),(18,2),(82,66),(98,66),(33,1),(162,130),(192,128),(65,1),(49,17),(81,17),(144,128),(34,66)],[],[[]])
theorem ptopW : TabsP true ptopR ptopT ptopt := ⟨cutsGood ptopY (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD11 : List StD := [
([pw0,pw1,pw2,pw4,pw5,pw20,pw89,pw120],[0,4,8,1,13,53,12,73,16,89,20,17,41,65,81,93,101,24,5,9,21,25,29,33,37,45,49,57,61,69,77,85,97,105,109,113,117,3],[262153,524294,2068,1048596,2068,2097172,4194324,8388611,16777225,4105,4105,33554441,67108873,134217762,268435490,8226,8226,536870946,1073742016,16576,16576,139586437312,33536,4294968064,33536,8590001152,17179935744,103079346176])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD10 : List StD := [
([pw0,pw1,pw2,pw5,pw20,pw89,pw120,pw121],[28,32,36,1,21,61,40,44,121,125,48,17,41,49,65,69,93,109,113,129,12,5,9,13,25,29,33,45,57,105,117,133],[2097161,4194310,8388628,2068,16777236,33554452,2068,67108867,4105,4105,134217737,8201,8201,268435490,16418,16418,32802,32802,536871232,1073742464,590848,590848,2147483840,131392,131392,262784,262784,1048576])]
def ptopD9 : List StD := []
theorem ptopI9 : LevelN true ptopT 9 ptopD9 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC10x0 : levelOK true ptopT ptopt 9 (ptopD9.map Prod.fst) ((ptopD10.drop (0*32)).take 32) = true := by decide +kernel
theorem ptopI10 : LevelN true ptopT 10 ptopD10 := levelStep ptopB ptopW ptopI9 (chunks 32 ptopD10 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC10x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC11x0 : levelOK true ptopT ptopt 10 (ptopD10.map Prod.fst) ((ptopD11.drop (0*32)).take 32) = true := by decide +kernel
theorem ptopI11 : LevelN true ptopT 11 ptopD11 := levelStep ptopB ptopW ptopI10 (chunks 32 ptopD11 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC11x0
  ))
theorem ptopL : LowN true ptopR ptopT 12 := lowSearch ptopB ptopI11 (by decide +kernel)

def theInputs : List Sig := rootsW [0,1,2,3,4,5,6,7]
def graph : Sig := W ptopT
theorem graph_proper : proper graph := (baseOK_ok ptopB).prop
def sample (r : Row) (i : Fin 8) : Bool := bit r (theInputs.getD i.val zero)
theorem theList : List.ofFn (fun i : Fin 8 => theInputs.getD i.val zero) = theInputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = theInputs.map (bit r) := by
  rw [←theList,List.map_ofFn]
  rfl
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem theTable : ∀ r : Row, bit r graph = target (sample r) := by decide +kernel
theorem theEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates theInputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl
theorem physicalSigned (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x)=target x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true graph k theInputs.toFinset := by
  have b := baseOK_ok ptopB
  have goalEq : (execute C.gates theInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (theEval C legal C.output r).trans ((computes (sample r)).trans (theTable r).symm)
  have out := get_rep (u:=true) (execute C.gates theInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by
    change bit 0 (W ptopT) = false
    have := b.plain
    unfold plainWord at this
    simpa using this
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract (u:=true) C.gates theInputs legal (by simp) graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : theInputs.all plainWord = true := b.plainR
  rw [nrm_map ns] at sub
  have eq : S = theInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨r,s,hd,iso⟩ := b.ess a (List.mem_toFinset.mp ha)
      exact raw_required run theInputs a sub r s hd iso
  exact ⟨k,hk,eq ▸ run⟩
theorem excludes : Impossible true graph 11 theInputs.toFinset := by
  intro k small run
  have steps := list_run run theInputs (by decide +kernel) rfl
  obtain ⟨q, bank, built, hit, limit⟩ := contraction (observe_proper graph_proper)
    steps (theInputs.map observe) Reach.start (fun _ h => Or.inl h)
  have bound := ptopL q bank built hit
  omega
theorem replaceShort (gates : List Gate) (o : Nat)
    (fit : ∀ g ∈ gates, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length≤2)
    (correct : ∀ x : Fin 8 → Bool, (Circuit.mk gates o).eval (List.ofFn x)=target x) :
    ∃ (gs : List Gate) (out : Nat), (∀ g ∈ gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) ∧
       gs.length≤gates.length ∧ ∀ x : Fin 8 → Bool, (Circuit.mk gs out).eval (List.ofFn x)=target x := by
  classical
  by_cases big : 13 ≤ gates.length
  · exact ⟨smallCircuit.gates,smallCircuit.output,witnessMonotone,(by simpa only [witnessSize] using big),witnessCorrect⟩
  by_cases mono : ∀ g ∈ gates, g.op ≠ GateOp.not
  · refine ⟨gates,o,?_,Nat.le_refl _,correct⟩
    intro g hg
    obtain ⟨ops,arity⟩ := fit g hg
    refine ⟨?_,arity⟩
    rcases ops with a | b | c
    · exact Or.inl a
    · exact Or.inr b
    · exact (mono g hg c).elim
  push Not at mono
  obtain ⟨g,hg,hop⟩ := mono
  have lt : gates.countP (fun q => !isNot q) < gates.length := by
    rcases Nat.lt_or_ge (gates.countP (fun q => !isNot q)) gates.length with h | h
    · exact h
    · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
      simp [isNot,hop] at eq
  have legal : PEqualNP.MetaComplexity.FanInTwo (Circuit.mk gates o) := by
    intro g hg
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using fit g hg
  obtain ⟨k,hk,run⟩ := physicalSigned (Circuit.mk gates o) legal correct
  change k ≤ gates.countP (fun q => !isNot q) at hk
  exact (excludes k (by omega) run).elim

end PEqualNP.Outside.L_meta_14716

theorem PEqualNP.Outside.L_meta_14716 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 2, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 2, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact PEqualNP.Outside.L_meta_14716.replaceShort gates o fit correct
