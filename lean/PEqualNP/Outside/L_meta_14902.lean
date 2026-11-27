import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_14902

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
  if h : r.val < 256-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(256-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 256 (256-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 256-d.val <;> simp [shifted,h,r.isLt]

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

abbrev Cut := Sig × Nat × List Sig

def cutTest (c : Cut) (k : Nat) (ws : List Sig) : Bool :=
  decide (k < c.2.1 + ws.countP (isMaskedConstant c.1)) &&
    ws.all fun w => masked c.1 w == zero || c.2.2.contains (masked c.1 w)

def CutGood (T : Sig) (c : Cut) : Prop :=
  ∀ k ws, ws.Nodup → cutTest c k ws = true → Impossible true T k ws.toFinset

theorem cut_good {T d raw L} (s : Slice true raw T d L) (cs : List Choice)
    {pool} (hp : makePool true d raw cs = some pool) (afford : cs.length ≤ L) :
    CutGood T (d,L-cs.length,pool.map (masked d)) := by
  intro k ws nd checked
  simp only [cutTest,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at checked
  apply poolCut_sound s cs hp nd
  apply Bool.and_eq_true_iff.mpr
  refine ⟨decide_eq_true (by omega),List.all_eq_true.mpr ?_⟩
  intro w hw
  rcases Bool.or_eq_true_iff.mp (checked.2 w hw) with hz | hm
  · simp [availableB,hz]
  · have mem := List.contains_iff_mem.mp hm
    obtain ⟨v,hv,eq⟩ := List.mem_map.mp mem
    have yes : ((pool.map (masked d)).any fun z => z == masked d w) = true :=
      List.any_eq_true.mpr ⟨masked d v,List.mem_map_of_mem hv,beq_iff_eq.mpr eq⟩
    simp [availableB,yes]

def properB (w : Sig) := w != zero && w != one
theorem proper_of (w : Sig) (h : properB w = true) : proper w := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h

def bothFlags : List Bool := [false,true]
theorem has_flag (b : Bool) : b ∈ bothFlags := by cases b <;> decide

def moves (ws : List Sig) (k : Nat) (a b : Sig) : List (List Sig) :=
  ([0,1,2,3] : List Nat).flatMap fun d =>
    let z := bin d a b
    if properB z && !ws.contains z then
      bothFlags.flatMap fun ka =>
        (bothFlags.map fun kb => childTwo ws a b d ka kb).filter fun v => decide (v.length ≤ k)
    else []

def children (ws : List Sig) (k : Nat) : List (List Sig) :=
  ws.flatMap fun a => ws.flatMap fun b => if a < b then moves ws k a b else []

theorem listed {ws : List Sig} {k a b d ka kb} (ha : a ∈ ws) (hb : b ∈ ws)
    (ab : a < b) (legal : allowed true d) (fresh : bin d a b ∉ ws) (pr : proper (bin d a b))
    (short : (childTwo ws a b d ka kb).length ≤ k) : childTwo ws a b d ka kb ∈ children ws k := by
  apply List.mem_flatMap.mpr
  refine ⟨a,ha,List.mem_flatMap.mpr ⟨b,hb,?_⟩⟩
  rw [if_pos ab]
  have dm : d ∈ ([0,1,2,3] : List Nat) := by
    rcases allowed_four legal with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> decide
  apply List.mem_flatMap.mpr
  refine ⟨d,dm,?_⟩
  have ready : (properB (bin d a b) && !ws.contains (bin d a b)) = true := by
    simp [properB,pr.1,pr.2,fresh]
  dsimp only
  rw [if_pos ready]
  exact List.mem_flatMap.mpr ⟨ka,has_flag ka,List.mem_filter.mpr
    ⟨List.mem_map_of_mem (f:=fun kb => childTwo ws a b d ka kb) (has_flag kb),decide_eq_true short⟩⟩

theorem swapped {ws : List Sig} {a b d} (h : allowed true d) (ka kb : Bool) :
    (childTwo ws a b d ka kb).Perm (childTwo ws b a (flipOp d) kb ka) := by
  unfold childTwo
  rw [bin_flip h a b,List.erase_comm a b]
  apply List.Perm.cons
  cases ka <;> cases kb <;> simp [kept,List.Perm.swap]

theorem by_children {T k ws} (nd : ws.Nodup) (absent : T ∉ ws)
    (h : ∀ w ∈ children ws k, Impossible true T (k-1) w.toFinset) : Impossible true T k ws.toFinset := by
  apply enum_step nd absent
  intro a ha b hb d leg ka kb ne fresh pr short
  rcases lt_or_gt_of_ne (show a.toNat ≠ b.toNat from fun e => ne (BitVec.eq_of_toNat_eq e)) with ab | ba
  · exact h _ (listed ha hb ab leg fresh pr short)
  · have p := swapped leg (ws:=ws) (a:=a) (b:=b) ka kb
    have e := bin_flip leg a b
    have other := listed hb ha ba (flip_flip leg).1 (e ▸ fresh) (e ▸ pr)
      (ka:=kb) (kb:=ka) (p.length_eq ▸ short)
    have eq : (childTwo ws a b d ka kb).toFinset = (childTwo ws b a (flipOp d) kb ka).toFinset := by
      ext w
      simpa only [List.mem_toFinset] using (p.mem_iff (a:=w))
    rw [eq]
    exact h _ other

def sameWires (ws vs : List Sig) := ws.all vs.contains && vs.all ws.contains
theorem same_wires {ws vs} (ok : sameWires ws vs = true) : ws.toFinset = vs.toFinset := by
  obtain ⟨l,r⟩ := Bool.and_eq_true_iff.mp ok
  ext a
  simp only [List.mem_toFinset]
  exact ⟨fun ha => List.contains_iff_mem.mp (List.all_eq_true.mp l _ ha),
    fun ha => List.contains_iff_mem.mp (List.all_eq_true.mp r _ ha)⟩

abbrev Cuts (T : Sig) := List {c : Cut // CutGood T c}
abbrev Links (T : Sig) (k : Nat) := List {ws : List Sig // Impossible true T k ws.toFinset}

def closeCase (T : Sig) (k : Nat) (cuts : Cuts T) (links : Links T k) (ws : List Sig) (code : Nat) :=
  if code < 65536 then
    let r := Fin.ofNat 256 (code % 256)
    let s := Fin.ofNat 256 (code / 256)
    (bit r T != bit s T) && ws.all (fun w => bit r w == bit s w)
  else if code < 131072 then
    match cuts[code-65536]? with
    | none => false
    | some c => decide ws.Nodup && cutTest c.val k ws
  else
    match links[code-131072]? with
    | none => false
    | some v => sameWires ws v.val

theorem close_ok {T k cuts links ws code} (ok : closeCase T k cuts links ws code = true) :
    Impossible true T k ws.toFinset := by
  unfold closeCase at ok
  split at ok
  · simp only [Bool.and_eq_true,bne_iff_ne,List.all_eq_true,beq_iff_eq] at ok
    intro n _ run
    obtain ⟨w,hw,ne⟩ := live_row_difference run ok.1
    exact ne (ok.2 w (List.mem_toFinset.mp hw))
  · split at ok
    · split at ok
      · contradiction
      · rename_i c _
        obtain ⟨nd,good⟩ := Bool.and_eq_true_iff.mp ok
        exact c.property k ws (of_decide_eq_true nd) good
    · split at ok
      · contradiction
      · rename_i v _
        rw [same_wires ok]
        exact v.property

def checkMoves (T : Sig) (k : Nat) (cuts : Cuts T) (links : Links T k) :
    List (List Sig) → Nat → Bool
  | [],_ => true
  | ws::rest,data => closeCase T k cuts links ws (data % 262144) &&
      checkMoves T k cuts links rest (data / 262144)

theorem moves_ok {T k cuts links vs data} (ok : checkMoves T k cuts links vs data = true) :
    ∀ w ∈ vs, Impossible true T k w.toFinset := by
  induction vs generalizing data with
  | nil => simp
  | cons v vs ih =>
    obtain ⟨closed,tail⟩ := Bool.and_eq_true_iff.mp ok
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hm
    · exact close_ok closed
    · exact ih tail _ hm

def checkNode (T : Sig) (k : Nat) (ws : List Sig) (cuts : Cuts T) (links : Links T (k-1)) (data : Nat) :=
  (decide ws.Nodup && !ws.contains T) && checkMoves T (k-1) cuts links (children ws k) data

theorem node_ok {T k ws} (cuts : Cuts T) (links : Links T (k-1)) (data : Nat)
    (ok : checkNode T k ws cuts links data = true) : Impossible true T k ws.toFinset := by
  obtain ⟨head,tail⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨hn,hm⟩ := Bool.and_eq_true_iff.mp head
  exact by_children (of_decide_eq_true hn) (by simpa using hm) (moves_ok tail)

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]
def input (i : Nat) := inputs.getD i zero
def selected (m : Nat) := (List.range 8).filter (fun i => m.testBit i)
def roots (m : Nat) := (selected m).map input

def goalAt (m : Nat) : Sig :=
  let x := fun i => if m.testBit i then input i else zero
  (x 0 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 4 &&& x 6) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)

def fixes (q : Nat) : List Move :=
  ((List.range 8).filter fun i => !(q.testBit i)).map fun i =>
    (zero,input i,Fin.ofNat 256 (1 <<< i))

def domain (q : Nat) : Sig :=
  ((List.range 8).filter fun i => !(q.testBit i)).foldl (fun d i => d &&& neg (input i)) one

def tests (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun i =>
    let r := 1 <<< ((hints >>> (4*i)) % 16)
    (input i,Fin.ofNat 256 r,Fin.ofNat 256 (r ||| (1 <<< i)))

def Claim (m L : Nat) : Prop := Lower true (roots m) (goalAt m) L

def essTest (m hints : Nat) :=
  (properB (goalAt m) && checkEssential (goalAt m) (roots m) (tests m hints)) &&
    ((tests m hints).map Prod.fst == roots m)

theorem fromSearch {m k} (hints : Nat) (checked : essTest m hints = true)
    (no : Impossible true (goalAt m) k (roots m).toFinset) : Claim m (k+1) := by
  simp only [essTest,Bool.and_eq_true,beq_iff_eq] at checked
  have ok := checked.1.2
  apply lower_impossible (proper_of _ checked.1.1) (essential_plain ok).1 (essential_plain ok).2 _ no
  intro w hw
  apply essential_ok ok w
  rw [checked.2]
  exact List.mem_toFinset.mpr hw

def liftTest (m q a b e hints : Nat) :=
  ((checkLift (fixes q) (goalAt m) (roots m) (roots q) (goalAt q) (tests e hints) &&
    properB (goalAt m)) && properB (goalAt q)) &&
      decide (b ≤ a+((tests e hints).map Prod.fst).toFinset.card)

theorem fromLift {m q a} (b e hints : Nat) (lower : Claim q a)
    (ok : liftTest m q a b e hints = true) : Claim m b := by
  simp only [liftTest,Bool.and_eq_true,decide_eq_true_eq] at ok
  have lb := lift_ok ok.1.1.1 (proper_of _ ok.1.1.2) (proper_of _ ok.1.2) lower
  exact fun p bank hr ha => ok.2.trans (lb p bank hr ha)

def poolFor (q : Nat) (extra : Option Choice) : List Sig :=
  match extra with
  | none => roots q
  | some c => choiceVal c :: roots q

def ruleTest (m q L : Nat) (e : Option Choice) : Bool :=
  (((checkMap (fixes q) (roots q) (goalAt m) (roots q) (goalAt q) &&
    (movedWord (fixes q) (domain q) == one)) && properB (goalAt q)) &&
    (makePool true (domain q) (roots q) e.toList == some (poolFor q e))) &&
    decide (e.toList.length ≤ L)

def ruleFor (m : Nat) {q L} (lo : Claim q L) (e : Option Choice)
    (ok : ruleTest m q L e = true) : {c : Cut // CutGood (goalAt m) c} := by
  refine ⟨(domain q,L-e.toList.length,(poolFor q e).map (masked (domain q))),?_⟩
  simp only [ruleTest,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at ok
  exact cut_good (slice_correct ok.1.1.1.1 ok.1.1.1.2 (proper_of _ ok.1.1.2) lo)
    e.toList ok.1.2 ok.2

def cuts164 : Cuts (goalAt 164) := []

def state164_0 : List Sig := roots 164
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude164_0 : Impossible true (goalAt 164) 3 state164_0.toFinset :=
  node_ok cuts164 [] 0x28080240428000840428200a00028080a08028080840409010240421010242021000a02021200840021010848021010a02009080242009010848009000a08009080240009010242009010a080212008480 (by decide +kernel)

theorem lower164 : Claim 164 4 :=
  fromSearch 538969344 (by decide +kernel) exclude164_0

theorem lower228 : Claim 228 5 :=
  fromLift 5 64 656409856 lower164 (by decide +kernel)

def cuts208 : Cuts (goalAt 208) := []

def state208_0 : List Sig := roots 208
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude208_0 : Impossible true (goalAt 208) 3 state208_0.toFinset :=
  node_ok cuts208 [] 0x30100501030000901030200c00030100c08030100901014040501024040504024000c04024200900024040908024040c04014100504014040908014000c08014100500014040504014040c080242009080 (by decide +kernel)

theorem lower208 : Claim 208 4 :=
  fromSearch 1141243904 (by decide +kernel) exclude208_0

theorem lower212 : Claim 212 5 :=
  fromLift 5 4 604374784 lower208 (by decide +kernel)

theorem lower180 : Claim 180 5 :=
  fromLift 5 16 539428096 lower164 (by decide +kernel)

theorem lower240 : Claim 240 5 :=
  fromLift 5 32 1148583936 lower208 (by decide +kernel)

def rule244_0 : {c : Cut // CutGood (goalAt 244) c} :=
  ruleFor 244 lower228 none (by decide +kernel)

def rule244_1 : {c : Cut // CutGood (goalAt 244) c} :=
  ruleFor 244 lower212 none (by decide +kernel)

def rule244_2 : {c : Cut // CutGood (goalAt 244) c} :=
  ruleFor 244 lower208 none (by decide +kernel)

def rule244_3 : {c : Cut // CutGood (goalAt 244) c} :=
  ruleFor 244 lower180 none (by decide +kernel)

def rule244_4 : {c : Cut // CutGood (goalAt 244) c} :=
  ruleFor 244 lower164 none (by decide +kernel)

def rule244_5 : {c : Cut // CutGood (goalAt 244) c} :=
  ruleFor 244 lower240 none (by decide +kernel)

def rule244_6 : {c : Cut // CutGood (goalAt 244) c} :=
  ruleFor 244 lower212 (some (1,input 2,input 4)) (by decide +kernel)

def rule244_7 : {c : Cut // CutGood (goalAt 244) c} :=
  ruleFor 244 lower180 (some (1,input 2,input 4)) (by decide +kernel)

def rule244_8 : {c : Cut // CutGood (goalAt 244) c} :=
  ruleFor 244 lower212 (some (1,input 2,input 6)) (by decide +kernel)

def rule244_9 : {c : Cut // CutGood (goalAt 244) c} :=
  ruleFor 244 lower228 (some (1,input 2,input 6)) (by decide +kernel)

def rule244_10 : {c : Cut // CutGood (goalAt 244) c} :=
  ruleFor 244 lower212 (some (3,input 2,input 7)) (by decide +kernel)

def rule244_11 : {c : Cut // CutGood (goalAt 244) c} :=
  ruleFor 244 lower180 (some (1,input 4,input 5)) (by decide +kernel)

def rule244_12 : {c : Cut // CutGood (goalAt 244) c} :=
  ruleFor 244 lower240 (some (1,input 4,input 5)) (by decide +kernel)

def rule244_13 : {c : Cut // CutGood (goalAt 244) c} :=
  ruleFor 244 lower180 (some (3,input 4,input 7)) (by decide +kernel)

def rule244_14 : {c : Cut // CutGood (goalAt 244) c} :=
  ruleFor 244 lower240 (some (1,input 5,input 6)) (by decide +kernel)

def rule244_15 : {c : Cut // CutGood (goalAt 244) c} :=
  ruleFor 244 lower228 (some (1,input 5,input 6)) (by decide +kernel)

def rule244_16 : {c : Cut // CutGood (goalAt 244) c} :=
  ruleFor 244 lower240 (some (3,input 5,input 7)) (by decide +kernel)

def rule244_17 : {c : Cut // CutGood (goalAt 244) c} :=
  ruleFor 244 lower212 (some (0,input 2,input 7)) (by decide +kernel)

def rule244_18 : {c : Cut // CutGood (goalAt 244) c} :=
  ruleFor 244 lower228 (some (3,input 6,input 7)) (by decide +kernel)

def rule244_19 : {c : Cut // CutGood (goalAt 244) c} :=
  ruleFor 244 lower180 (some (0,input 4,input 7)) (by decide +kernel)

def cuts244 : Cuts (goalAt 244) := [rule244_0,rule244_1,rule244_2,rule244_3,rule244_4,rule244_5,rule244_6,rule244_7,rule244_8,rule244_9,rule244_10,rule244_11,rule244_12,rule244_13,rule244_14,rule244_15,rule244_16,rule244_17,rule244_18,rule244_19]

def state244_0 : List Sig := [0xfffffffffffff0f0fffffffffffff0f0ffffffff00000000ffffffff00000000,input 7,input 2,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_0 : Impossible true (goalAt 244) 4 state244_0.toFinset :=
  node_ok cuts244 [] 0x30000c00030100501014000500014040c080240809020240c0a0200d0102404090502404150405010140505010090803420090c0242009080842030110242009000240009010a080090106404140c0240428000a000280802404 (by decide +kernel)

def state244_1 : List Sig := [0xfffffffffffffffffffff0f0fffff0f0ffffffffffffffff0000000000000000,input 7,input 2,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_1 : Impossible true (goalAt 244) 4 state244_1.toFinset :=
  node_ok cuts244 [] 0x28000a000280802404090106404140c024040d010240409050240414100a020280c0a02014000500014040c08009000240009010a080090803420090c0242009080a02021110242015040501014050501030000c000301005010 (by decide +kernel)

def state244_2 : List Sig := [0xfffff0f0fffff0f0fffff0f0fffff0f000000000000000000000000000000000,input 7,input 2,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_2 : Impossible true (goalAt 244) 5 state244_2.toFinset :=
  node_ok cuts244 [⟨state244_0,exclude244_0⟩,⟨state244_1,exclude244_1⟩] 0xc00030000c04014040240419010503009010a00028000a02009010500014000501030200340409010241409010504028080a0302808050402420100051410054101404050141404024000900024042820024200d080243009080242028080c044090802420212010000090810003140420001140410001090120000090108404 (by decide +kernel)

def state244_3 : List Sig := [0xffffffff00000000ffffffff00000000fffff0f000000000fffff0f0,input 7,input 2,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_3 : Impossible true (goalAt 244) 4 state244_3.toFinset :=
  node_ok cuts244 [] 0x38000a00028100a0001c00070001404090802c000a00024040a000090006400140502400090003400090c0240009000a0002101024000901050301901024040901024140d010240421200240009010240009010a00021010a000 (by decide +kernel)

def state244_4 : List Sig := [0xffffffffffffffff0000000000000000fffff0f0fffff0f0,input 7,input 2,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_4 : Impossible true (goalAt 244) 4 state244_4.toFinset :=
  node_ok cuts244 [] 0x38000c00030080c00014000700009050500014000c000240405000190006400090108480150005000090c0500031000c00021010c00009010503009010640424200500015010500014040501415040501021010c00021010c000 (by decide +kernel)

def state244_5 : List Sig := [0xfffffffffffffffffffffffffffffffffffff0f0fffff0f0fffff0f0fffff0f0,input 7,input 2,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_5 : Impossible true (goalAt 244) 5 state244_5.toFinset :=
  node_ok cuts244 [⟨state244_3,exclude244_3⟩,⟨state244_4,exclude244_4⟩] 0xc4042101084442101200011404050104000c2404190105030090102404210109030090120000090102404400045404150105010242003404090102414090109404210109010210105040150405010140505010090103410090108480151103430090c0243021010901021010901009080a020 (by decide +kernel)

def state244_6 : List Sig := [0xfffff0f0fffff0f0fffff0f0fffff0f0,input 7,input 2,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_6 : Impossible true (goalAt 244) 5 state244_6.toFinset :=
  node_ok cuts244 [] 0xc00030000c04014040240419010503009010a00028000a0200901054041501050102420034040901024140901090002400090802808054101404050141404024040d04024042120054440d0c02430090c08400210008480280805010302005010302002404282002404282005040141005444242002420090803430212008404 (by decide +kernel)

def state244_7 : List Sig := [0xf0f00000f0f00000f0f00000f0f00000000000000000000000000000000,input 7,input 2,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_7 : Impossible true (goalAt 244) 5 state244_7.toFinset :=
  node_ok cuts244 [] 0xc4042101084442101024041901050300901024042101090300901050001400050103020034040901024140901090002400090102101054101404050141404024000900024042820024200d080243009080840021000840424040c08014040c08014040a08009010a08009010908021200a020 (by decide +kernel)

def state244_8 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_8 : Impossible true (goalAt 244) 5 state244_8.toFinset :=
  node_ok cuts244 [] 0x310108404211108404140405410140505010090106404140c024040901084042820024040d040240409011000615010540414040c0800d0102404090502404141009004210108414210103430151102430090c05010302005010212002404282002404212008404212008404301102420090803430400009010 (by decide +kernel)

def state244_9 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 7,0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0,input 2,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_9 : Impossible true (goalAt 244) 5 state244_9.toFinset :=
  node_ok cuts244 [] 0x140409010302005010150105404140410007090106404140c02404090109010240c0240409010340409050240415040501014050501009010341009010a0800908084102104084142404054440d0c02430090c05010302005010242002404282002404242009010242009010280c05040141005444400148404 (by decide +kernel)

def state244_10 : List Sig := [0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0,input 2,input 4,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_10 : Impossible true (goalAt 244) 6 state244_10.toFinset :=
  node_ok cuts244 [⟨state244_2,exclude244_2⟩,⟨state244_5,exclude244_5⟩,⟨state244_6,exclude244_6⟩,⟨state244_7,exclude244_7⟩,⟨state244_8,exclude244_8⟩,⟨state244_9,exclude244_9⟩] 0xc04014040c00021010c08030000c04030200c04021010501021010a02009010a00021010a08028000a02028200a0202101024040901070300901024041404064441901070301911050301404024040901090101511094042101100002101090108001490102101054442101050104001c54043020054441501050101511050103020100073020034141511034040901100000901034144000824140901054440901100004001450402101034302101090104001490102101200042101090100d0c090101505034301504050104001450101505100041405050100d0c0501009011000609010a0800d0c0341009010343009010a08040018a0801511100001511100050d0c03430400010000090c1000040000242021012000321010a02080008a02021012000121010a02080000a02014041000314040c08040010c08014041000414040c0804000cc08009011000109010a08040008a08009011000209010a08040004a080 (by decide +kernel)

def state244_11 : List Sig := [0xfffffffffffffffffffff0f0fffff0f0ffff0000ffff0000ffff0000ffff0000,input 7,input 2,input 6,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_11 : Impossible true (goalAt 244) 4 state244_11.toFinset :=
  node_ok cuts244 [] 0x90106404140c0240428000a00028080240409010340409050240414040901028180501014000500014040908009000240009010a080150405010140505010210408410210509010090803420090c0242024000900024040a020 (by decide +kernel)

def state244_12 : List Sig := [0xfffffffffffffffffffffffff0f0f0f0ffffffff00000000ffffffff00000000,input 7,input 2,input 6,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_12 : Impossible true (goalAt 244) 4 state244_12.toFinset :=
  node_ok cuts244 [] 0x14000500014040908024000900024040a0200d0102404090502404140409010281805010190102404140c02404090803420090c0242015040501014050501009080901024050901009000240009010a08028000a000280802404 (by decide +kernel)

def state244_13 : List Sig := [0xfffffffffffffffff0f0f0f0f0f0f0f000000000000000000000000000000000,input 7,input 2,input 6,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_13 : Impossible true (goalAt 244) 5 state244_13.toFinset :=
  node_ok cuts244 [⟨state244_11,exclude244_11⟩,⟨state244_12,exclude244_12⟩] 0x240419010503009010a00028000a02009010240440006000109010340409010241409010500014000501024200900024000901028080504040002000014100501024040a0601404050103020100051404024000900024042820024200d0802430090805410140405014140402420240409014240402420212010003090808404 (by decide +kernel)

def state244_14 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000f0f00000f0f0,input 7,input 2,input 6,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_14 : Impossible true (goalAt 244) 4 state244_14.toFinset :=
  node_ok cuts244 [] 0x1c00050001408050002c00090002408090001400090003010050000d0003400090108480150005000140505000250009000210109000090102414090103404242005000150105000090802420151003420210109000210109000 (by decide +kernel)

def state244_15 : List Sig := [0xffffffff00000000ffffffff00000000ffffffff00000000f0f0f0f0,input 7,input 2,input 6,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_15 : Impossible true (goalAt 244) 4 state244_15.toFinset :=
  node_ok cuts244 [] 0x1c00070001c04090802c000a00028040a00038000a00030100a00009000340009040240009000640014050240009000a0002101024000901024140d010240409010501019010240421200240009010240009010a00021010a000 (by decide +kernel)

def state244_16 : List Sig := [0xfffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0,input 7,input 2,input 6,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_16 : Impossible true (goalAt 244) 5 state244_16.toFinset :=
  node_ok cuts244 [⟨state244_14,exclude244_14⟩,⟨state244_15,exclude244_15⟩] 0x240419010244409010240421010c06009012000109010240440004340409010241409010540415010541424200940421010841421012000014100504040000c40421010c04021010501009010644009010848015100504014110504015050646014050501421010c040210109014090809010 (by decide +kernel)

def state244_17 : List Sig := [0xfffffffffffffffff0f0f0f0f0f0f0f0,input 7,input 2,input 6,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_17 : Impossible true (goalAt 244) 5 state244_17.toFinset :=
  node_ok cuts244 [] 0x240419010244409010a00028000a02009010340409010241409010540415010541424200900024000901028080c00030000c080240402404191002404212005440141005044141005414191805014140508400210008480240402404282002404282005040242005040242005010140405414302002420090806460212008404 (by decide +kernel)

def state244_18 : List Sig := [0xf0f0f0f0f0f0f0f00000000000000000000000000000000,input 7,input 2,input 6,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_18 : Impossible true (goalAt 244) 5 state244_18.toFinset :=
  node_ok cuts244 [] 0x240419010503009010240421010c06009010340409010241409010500014000501024200940421010841421010c00030000c0402101024000900024042820024200d080243009080541014040501414040840021000840409080a08009010a08009010908014100908014100c080212009010 (by decide +kernel)

def state244_19 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 6,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_19 : Impossible true (goalAt 244) 5 state244_19.toFinset :=
  node_ok cuts244 [] 0x901064040911024042820024040901084800901084042820024041910024040901100080d010240409050240415010540415050908024200504014100848025010840421050840414100544014110504014040c0042101084442101064601505050141405084042120084042405024200908064604000c9010 (by decide +kernel)

def state244_20 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 2,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_20 : Impossible true (goalAt 244) 5 state244_20.toFinset :=
  node_ok cuts244 [] 0x28200240409010a08009010c0403018024040901064040911024040d010240409050240424200504014100908014100c04024200504015010540415051000909010644009010a08015100504014110504009080844021100844430100541419180501414050c04030200c040281805010140405414400148404 (by decide +kernel)

def state244_21 : List Sig := [0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,input 2,input 6,input 4,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_21 : Impossible true (goalAt 244) 6 state244_21.toFinset :=
  node_ok cuts244 [⟨state244_13,exclude244_13⟩,⟨state244_16,exclude244_16⟩,⟨state244_17,exclude244_17⟩,⟨state244_18,exclude244_18⟩,⟨state244_19,exclude244_19⟩,⟨state244_20,exclude244_20⟩] 0xa02009010a00021010a08028000a02028200a02021010240409011000309010240415050644419011000219110244415050240409011000228200a08040004240409011000209010240440004a0802820090101410090002101090802400090102420090102101050402101034141410034040901070600901034141c18024140901050400901054142420054044002450401501054141410054144000c908024201000424200908040000504014101000414100504040000908024200c04015050c40421011000321010c04080014c04021010541421011000340014501021010646021010901040014901021012000421010901019180901009011000809010a08019180644009010646009010a08040020a0801511064601510050404001450401511100041411050401918050401505100031505100051918064604000d00031405100034000c2420210120003210109010800089010210120001210109010800009010 (by decide +kernel)

def state244_22 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_22 : Impossible true (goalAt 244) 5 state244_22.toFinset :=
  node_ok cuts244 [] 0xc40421010844421010501015040501414040240419010503009010240421010a080090102400090002404400285000140005010242003404090102414090109404210108414210103420090802430090808400212005010302005010212002404282002404212005040242005040240510003 (by decide +kernel)

def state244_23 : List Sig := [0xffff0000ffff0000ffff0000ffff0000f0f00000f0f00000f0f00000f0f0,input 4,input 2,input 7,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_23 : Impossible true (goalAt 244) 5 state244_23.toFinset :=
  node_ok cuts244 [] 0xc4042101084442101024041901050300901024042101090300901054101404050141404024040d04024042120084042404084042404034200d080343014100500014000501030200341409010341409010900024000901021010c08014040c0801404024040d05024040d05084042404084042404024200908084800d0c05444 (by decide +kernel)

def state244_24 : List Sig := [0xffffffff00000000ffffffff00000000f0f0f0f000000000f0f0f0f0,input 2,input 7,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_24 : Impossible true (goalAt 244) 5 state244_24.toFinset :=
  node_ok cuts244 [] 0x38100501038000a00030200a00038100c08028100a00014040a00014040908014000c08014100500014040504014040c0802420090802c04050402c000a00024200a0002c040908028040a00014100a0001505024000900050101910064001505064401505050100900024001511024000900050400d040340015110341009040504009000240021010240009000a00021200a00021010848021010a0000900024001505024040901050101911050101505064441901050100901024041511024040901050400d05024141511034140d010504009010240421010240409010a00028200a00021010a08021010a00009010a00021200a080212002400090102400212002404090102400282002400 (by decide +kernel)

def state244_25 : List Sig := [0xffffffff00000000ffffffff00000000f0f0f0f000000000f0f0f0f0,0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 2,input 7,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_25 : Impossible true (goalAt 244) 5 state244_25.toFinset :=
  node_ok cuts244 [] 0x310108404211108404140405414150505010140005000140409080250108404210508404141005444151105040280005414140405414140405444141005444141008404212009014090002404140406404090102404090503404090102404282008404090108480090102404282010001 (by decide +kernel)

def state244_26 : List Sig := [0xffffffffffffffff0000000000000000f0f0f0f0f0f0f0f0,input 6,input 2,input 7,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_26 : Impossible true (goalAt 244) 5 state244_26.toFinset :=
  node_ok cuts244 [] 0x240421010c06009010240414040503009010340409010241409010940421010841421010500014000501024200240419100240421200544014100504414100840430100840424050541014040646014040c00030000c040210102404191102404191109080141009080141008404240408404301002420090808480191805414 (by decide +kernel)

def state244_27 : List Sig := [0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 2,input 7,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_27 : Impossible true (goalAt 244) 6 state244_27.toFinset :=
  node_ok cuts244 [⟨state244_22,exclude244_22⟩,⟨state244_8,exclude244_8⟩,⟨state244_19,exclude244_19⟩,⟨state244_5,exclude244_5⟩,⟨state244_23,exclude244_23⟩,⟨state244_24,exclude244_24⟩,⟨state244_25,exclude244_25⟩,⟨state244_16,exclude244_16⟩,⟨state244_26,exclude244_26⟩] 0xc44414040c40421010c08021010c4443020084442101050102101200081404050104000c54141505200071505054144000c501014040703009010240414040644419010703019110503014040240409011000209010240421010a08021011000228200a0802101024040901100028001a00054000424040901100020901024044000500024000450102420050003020050401400050101410050103020090802420034141410034040901070600901034141c180241409010504009010941414100940421010908021010941424200841421010504021012000414100504040000544415112000315110544440000504014101000540014901015050848015050501040014501015052000215050501021200501009010848009010a08040014a08009011000209010a080212008480151108480151105040400145040151120001151105040212005040210120000210110005212008480400150005240510005800002420 (by decide +kernel)

def state244_28 : List Sig := [0xffff0f0fffff0f0f0000000000000000ffff0000ffff0000,input 4,input 2,input 7,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_28 : Impossible true (goalAt 244) 4 state244_28.toFinset :=
  node_ok cuts244 [] 0x38000c00030080c00009000240009010a08021000840021010c0001500050001401050001400070000d050500014000c0002404050001404024041c040240414040c00024040c000140405014150405010242005000140405000 (by decide +kernel)

def state244_29 : List Sig := [0xffff0f0fffff0f0fffff0f0fffff0f0fffff0000ffff0000ffff0000ffff0000,input 4,input 2,input 7,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_29 : Impossible true (goalAt 244) 5 state244_29.toFinset :=
  node_ok cuts244 [⟨state244_28,exclude244_28⟩] 0xc4042101084442101024041901050300901024042101090300901054101404050141404024000900024042820084002100084042404024200d0c034300908024200d0c034300908050103020050102420034140901034140901090102101090102101050401404200001404100030d05024040d0502404240408404240408404 (by decide +kernel)

def state244_30 : List Sig := [0xffff0000ffff00000f0f00000f0f0000ffff0000ffff0000000000000000,input 6,input 2,input 7,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_30 : Impossible true (goalAt 244) 4 state244_30.toFinset :=
  node_ok cuts244 [] 0x2c00090002408090001c000500014080500009000240009010a0802100084002101090001500050001401050001400090003010050001410024041c1002404280809000301009000141002420151002420242005000141005000 (by decide +kernel)

def state244_31 : List Sig := [0xffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0000000000000000,input 6,input 2,input 7,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_31 : Impossible true (goalAt 244) 5 state244_31.toFinset :=
  node_ok cuts244 [⟨state244_30,exclude244_30⟩] 0x240421010c0600901024041911064440901024041911064440901034040901024140901094042101084142101090801410050402420200001410050404000024000900024042820024200d080243009080840021000840409080242019180646009080242019180646009080c04021010c040210105010240408404301008404 (by decide +kernel)

def state244_32 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000,input 2,input 7,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_32 : Impossible true (goalAt 244) 6 state244_32.toFinset :=
  node_ok cuts244 [⟨state244_22,exclude244_22⟩,⟨state244_29,exclude244_29⟩,⟨state244_7,exclude244_7⟩,⟨state244_31,exclude244_31⟩,⟨state244_18,exclude244_18⟩] 0xc44414040c40421010c08021010c44430200844421010501021010703009010240414040644419010703019110503014040240409011000209010240421010a08021011000228200a0802101024040901050102420050003020050401400050101410050103020090802420034141410034040901070600901034141c180241409010504009010941414100940421010908021010941424200841421010504021010541409080541014040646014040541419180501414040242014040240440028240028200242009000240409080240428201000a2820054440908024201410034300d08054440d0c024301410024200908100054001484002101200002101100050908024203020100033020050108001050103020200033020050104000c5010282010001282002404400082404282010002282002404400042404242010000242005040800085040242020001242005040400005040400150005240420000400148480 (by decide +kernel)

def state244_33 : List Sig := [0xffffffffffffffffffffffffffff0000ffffffffffffffff0000000000000000,input 7,input 4,input 5,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_33 : Impossible true (goalAt 244) 4 state244_33.toFinset :=
  node_ok cuts244 [] 0x90002400090108480090803420090c02420210008400210102420150405010140505010090108404281802404090106404140c024040d010240409050240414100840421050840414000500014040c08030000c000301008404 (by decide +kernel)

def state244_34 : List Sig := [0xfffffffffffff0f0fffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_34 : Impossible true (goalAt 244) 4 state244_34.toFinset :=
  node_ok cuts244 [] 0x30000c000301008404090106404140c0240409010840430180240409000240009010848014000500014040c0800d01024040905024042401084042105084040d0802420090c02420150405010140505010210008400210102420 (by decide +kernel)

def state244_35 : List Sig := [0xffffffffffff0000ffffffffffff000000000000000000000000000000000000,input 7,input 4,input 5,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_35 : Impossible true (goalAt 244) 5 state244_35.toFinset :=
  node_ok cuts244 [⟨state244_33,exclude244_33⟩,⟨state244_34,exclude244_34⟩] 0xc00030000c0402101054101404050141404024000900024042120024200d080243009080840021000840409080242040016000109080240419010503009010240421010c060090102404282010000090105000140005010302003404090102414090105040210108414210105040242010001141010003140420000140409010 (by decide +kernel)

def state244_36 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f0000,input 7,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_36 : Impossible true (goalAt 244) 4 state244_36.toFinset :=
  node_ok cuts244 [] 0x310008400211008400090006400140c024000900084002808024001500054001404090800d00024000905024002500084002404084001404050141404054102120024000d04024000908024300d0802420240408400240408400 (by decide +kernel)

def state244_37 : List Sig := [0xffffffffffffffff0000000000000000ffffffffffff0000,input 7,input 4,input 5,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_37 : Impossible true (goalAt 244) 4 state244_37.toFinset :=
  node_ok cuts244 [] 0x19000640019010848015000500014010500031000c00030010c00038000c00028080c00014000700009050500014000c0002404050001404050141504050100901024041c040640424200500014040500021010c00024040c000 (by decide +kernel)

def state244_38 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000,input 7,input 4,input 5,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_38 : Impossible true (goalAt 244) 5 state244_38.toFinset :=
  node_ok cuts244 [⟨state244_36,exclude244_36⟩,⟨state244_37,exclude244_37⟩] 0x501024040a0601404200011404050104000c54101404050141404034100d04034142120024200d080243009080941024040901424042000009080242040014701014040503014040b01024040a0202404024041404070201404090800d050706009050241424040a020240408414141008404 (by decide +kernel)

def state244_39 : List Sig := [0xffffffffffff0000ffffffffffff0000,input 7,input 4,input 5,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_39 : Impossible true (goalAt 244) 5 state244_39.toFinset :=
  node_ok cuts244 [] 0xc00030000c0402101054101404050141404034100d04034142120024200d080243009080840021000840409080701014040503014040a00028000a0802101050101c08050102420034141c1802414090509000240009080210105010302005010302002420212002420212002404090103414282005040141007060242009010 (by decide +kernel)

def state244_40 : List Sig := [0xffff000000000000ffff00000000000000000000000000000000,input 7,input 4,input 5,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_40 : Impossible true (goalAt 244) 5 state244_40.toFinset :=
  node_ok cuts244 [] 0x501024040a0601404054101404050141404024000900024042120024200d080243009080941024040901424040240419010503009010a00028000a02009010500014000501030200340409010241409010900024000901028080c08014040c08014040848009080848009080a080242008404 (by decide +kernel)

def state244_41 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_41 : Impossible true (goalAt 244) 5 state244_41.toFinset :=
  node_ok cuts244 [] 0x1404090103020050101c080501014041000b1504050101405050100d04034100d0508480212002420090808480250409010240509010090803420090c024201c0405010140c0501009010a0102404090302404070600d0502414090505010302005010242009010242009010210505040141007060400048404 (by decide +kernel)

def state244_42 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_42 : Impossible true (goalAt 244) 5 state244_42.toFinset :=
  node_ok cuts244 [] 0x14040a020281805010140407010140c05010150405010140505010090803420090c0242021200242009080848009080a0202120024200d04034100d051000c14040702014040c0801410090202408090302808034141c180241409050501030200501028200a02028200a020301802404090103414400008404 (by decide +kernel)

def state244_43 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,input 2,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_43 : Impossible true (goalAt 244) 6 state244_43.toFinset :=
  node_ok cuts244 [⟨state244_35,exclude244_35⟩,⟨state244_38,exclude244_38⟩,⟨state244_39,exclude244_39⟩,⟨state244_40,exclude244_40⟩,⟨state244_41,exclude244_41⟩,⟨state244_42,exclude244_42⟩] 0xc04014040c00021010c08030000c04030200c0402101050102101084040908084002404084802100084042120084042404024202404054140908054101404064601404054141918050141404024201404034142120034104003024200d04034140908034144000484802120100000908024201c18034300d08100020d0c024301c180242009081000221200848040014242009081000209080242040014848021200a0200d050b01021011000121010a02080014a0202101034142101070300d05070101404100011404070304001050301404034141404100014000024042404070602404084044000084042404200042404084041c180840414041000b14040c0801c180702014040706014040c0804002cc0800d05100010d05100001c180706040005000109051000140004504024042000324040840480008840424042000124040840480000840414041000314040c08040010c08014041000414040c0804000cc080 (by decide +kernel)

def state244_44 : List Sig := [0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 7,input 2,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_44 : Impossible true (goalAt 244) 5 state244_44.toFinset :=
  node_ok cuts244 [] 0x501024040c0801404050001400050104003424041901050300901024042404090300901024040d01024140901054101404050141404024000900024042120094102404090142404024200d0802430090809000242005010302005010242002404282002404212002420212002420210510003 (by decide +kernel)

def state244_45 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f0f00000f0f0000,input 2,input 4,input 7,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_45 : Impossible true (goalAt 244) 5 state244_45.toFinset :=
  node_ok cuts244 [] 0xc4042101084442101024041901050300901024042101090300901054041501050102420034040901024140901094042101090102101054141404054141404024000900024042820084002100084042404024200d080544409080501015050501015050a08009010a080090109010210109010210105040141009080151103430 (by decide +kernel)

def state244_46 : List Sig := [0xffffffff00000000ffffffff00000000ffff000000000000ffff0000,input 5,input 4,input 7,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_46 : Impossible true (goalAt 244) 5 state244_46.toFinset :=
  node_ok cuts244 [] 0x501024040a0601404054101404050141404094102404090142404024200d08024300908024000900024042120050101c080501024200901028080901021050340409010706009010240419010703009010a00028000a0200901050101c0c050101c0c084800908084800908084042101090102808050401410090801c1803414 (by decide +kernel)

def state244_47 : List Sig := [0xffffffffffffffff0000000000000000ffff0000ffff0000,input 4,input 7,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_47 : Impossible true (goalAt 244) 5 state244_47.toFinset :=
  node_ok cuts244 [] 0x38080240438000c00028200c00038080a08030080c00009010c00009010848009000a08009080240009010242009010a08021200848031010242031000c00021200c00031010848030010c00009080c0001501024201500050000d0c050001501034301401050000908050000d05050001400024041c08070000d05070200d050240414000500024040500014000c00024200c00024040908024040c0001400050000d05050101404024041c0c024040d05070301c04024041404024040d0c050101404024201505050140d0c0541415040242014040501024040501021010c00030200c00024040c08024040c00014040c00024200c080242005000140405000242005010140405000302005000 (by decide +kernel)

def state244_48 : List Sig := [0xffffffffffffffff0000000000000000ffff0000ffff0000,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_48 : Impossible true (goalAt 244) 5 state244_48.toFinset :=
  node_ok cuts244 [] 0x90109010240c024040901034140d05024040900024000901084802504090102405090100908034300d0c024200908034300d0c02420300003414090103414090109010242008414140005010090107010090105010140505410140405010302009010140409080140405010302010003 (by decide +kernel)

def state244_49 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 2,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_49 : Impossible true (goalAt 244) 6 state244_49.toFinset :=
  node_ok cuts244 [⟨state244_44,exclude244_44⟩,⟨state244_41,exclude244_41⟩,⟨state244_5,exclude244_5⟩,⟨state244_45,exclude244_45⟩,⟨state244_9,exclude244_9⟩,⟨state244_38,exclude244_38⟩,⟨state244_46,exclude244_46⟩,⟨state244_47,exclude244_47⟩,⟨state244_48,exclude244_48⟩] 0x1000414040501024040c08024041000430200c0802404050101404100048002200074000c50101404100041404050104000d00044000c703009010240414040644419010703019110503014040240409010b03009010240424040a08024040b0302820090302404024040901200060901024044000434140d05200050d05034144000424040901054140908054101404064601404054141918050141404024201404024042120024002820024200900024040908024042820084802120094140908094102404084802404094142120090142404024202404100000908024202420034300d0c200040d0c034302420024200908200030908024204001434300d0c200020d0c0343040014242009081000040000840414040908014040c08040000c08014041000414040c0802420090800d05090800d05024044000024040d05200010d0502404242002404240420000240410000242009080400010000210510000800005040 (by decide +kernel)

def state244_50 : List Sig := [0xf0f0ffff00000000f0f0ffff00000000f0f0f0f000000000f0f0f0f0,input 2,input 4,input 7,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_50 : Impossible true (goalAt 244) 4 state244_50.toFinset :=
  node_ok cuts244 [] 0x38000a00028100a00014000500014040c08024000900024040a00009000640015050240009000a00021010240009000340009040240009010501019010240409010a00021010a0000901024140d0102404212002400090102400 (by decide +kernel)

def state244_51 : List Sig := [0xf0f0fffff0f0fffff0f0fffff0f0fffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 2,input 4,input 7,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_51 : Impossible true (goalAt 244) 5 state244_51.toFinset :=
  node_ok cuts244 [⟨state244_50,exclude244_50⟩] 0xc404210108444210102404190105030090102404210109030090105000140005010302003404090102414090109000240009010210105414140405414140402404282002404212008404240408404240405444141005444141002420150505010150505010090120000090110001210109010210109010151105040151105040 (by decide +kernel)

def state244_52 : List Sig := [0xf0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f000000000f0f0f0f00000000,input 5,input 4,input 7,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_52 : Impossible true (goalAt 244) 4 state244_52.toFinset :=
  node_ok cuts244 [] 0x31000840021100840014000500014040c0802400084002104084000d00024000904024000900064001c0c024000900084002808024000908050101908050100908084002808084000908024300d0802420212002400090802400 (by decide +kernel)

def state244_53 : List Sig := [0xffffffff0000ffffffffffff0000ffffffffffff00000000ffffffff00000000,input 5,input 4,input 7,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_53 : Impossible true (goalAt 244) 5 state244_53.toFinset :=
  node_ok cuts244 [⟨state244_52,exclude244_52⟩] 0x501024040a0601404054101404050141404094102404090142404024200d08024300908084800908024202120200000908024204001450001400050103020090002400090102808050401c18070601410050401c180706014100703014040703014040a02024040a0202404024041c0c050101c0c05010210108404280809010 (by decide +kernel)

def state244_54 : List Sig := [0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000,input 4,input 7,input 2,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_54 : Impossible true (goalAt 244) 6 state244_54.toFinset :=
  node_ok cuts244 [⟨state244_44,exclude244_44⟩,⟨state244_51,exclude244_51⟩,⟨state244_7,exclude244_7⟩,⟨state244_53,exclude244_53⟩,⟨state244_40,exclude244_40⟩] 0x1000414040501024040c08024041000430200c08024040501014040703009010240414040644419010703019110503014040240409010b03009010240424040a08024040b0302820090302404024040901054140908054101404064601404054141918050141404024201404024042120024002820024200900024040908024042820084802120094140908094102404084802404094142120090142404024202404054440908024201410034300d08054440d0c0243014100242009080501040034500030200504014000501014100501030201000d3020034141410034040901070600901034141c18024140901050400901100004000090002404200002404100001410050403020100033020050104001050103020100043020050104000c5010282010001282002404800102404282020003282002404400042404212010005212002420800082420212020001212002420400142420400010000210120000400009080 (by decide +kernel)

def state244_55 : List Sig := [0xfffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,input 5,input 6,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_55 : Impossible true (goalAt 244) 4 state244_55.toFinset :=
  node_ok cuts244 [] 0x1400050001404090800d01024040905024042400090002404084040d0802420090c02420300108404211108404140405410140505010090106404140c02404090108404240c02404090002400090108480210008400210109010 (by decide +kernel)

def state244_56 : List Sig := [0xffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000ffff0000,input 7,input 5,input 6,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_56 : Impossible true (goalAt 244) 4 state244_56.toFinset :=
  node_ok cuts244 [] 0x150405010140505010090002400090108480210008400210109010090803420090c02420140408404211108404140005000140409080090106404140c02404090108404240c02404090103404090502404240009000240408404 (by decide +kernel)

def state244_57 : List Sig := [0xffffffffffffffffffffffff0000000000000000000000000000000000000000,input 7,input 5,input 6,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_57 : Impossible true (goalAt 244) 5 state244_57.toFinset :=
  node_ok cuts244 [⟨state244_55,exclude244_55⟩,⟨state244_56,exclude244_56⟩] 0x50001400050102420034040901024140901090002400090102101050404000200011410024200d080243009080541014040501414040240009000240421200840021000840424040242040016000009080501021010844421010501030201000114040240419010503009010240421010903009010240428201000309010a020 (by decide +kernel)

def state244_58 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000,input 7,input 5,input 6,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_58 : Impossible true (goalAt 244) 4 state244_58.toFinset :=
  node_ok cuts244 [] 0x1500054001504090800d0002400090402400250008400210408400310008400301008400090006400140c024000900084002808024000908024300d0802420140405010190805410212002400090802400240408400280808400 (by decide +kernel)

def state244_59 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff00000000,input 7,input 5,input 6,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_59 : Impossible true (goalAt 244) 4 state244_59.toFinset :=
  node_ok cuts244 [] 0x1500050001401050000d00034000d01084802500090002401090001400090003010050001c0005000140c050002c00090002808090000908024300908034202420050001c08050000901024041c1003404210109000280809000 (by decide +kernel)

def state244_60 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000,input 7,input 5,input 6,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_60 : Impossible true (goalAt 244) 5 state244_60.toFinset :=
  node_ok cuts244 [⟨state244_58,exclude244_58⟩,⟨state244_59,exclude244_59⟩] 0x70201c08070302420050401c100506014100b02028080a0302808200011410050404000024200d080243009080242019080246009080644009080242021200242028080c04409082000009080242040014e02028080c0402808050101c0c06444140c0503028080c040280809030090108404 (by decide +kernel)

def state244_61 : List Sig := [0xffffffffffffffffffffffff00000000,input 7,input 5,input 6,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_61 : Impossible true (goalAt 244) 5 state244_61.toFinset :=
  node_ok cuts244 [] 0x70201c08070302420050401c10050601410090002400090102101024200d080243009080242019080246009080644009080242021200840021000840424040c00030000c080210107030191105030140c0a00028000a08021010504024200504024200242021200242021200501014040703030200240409010644428200a020 (by decide +kernel)

def state244_62 : List Sig := [0xffffffff00000000000000000000000000000000,input 7,input 5,input 6,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_62 : Impossible true (goalAt 244) 5 state244_62.toFinset :=
  node_ok cuts244 [] 0x500014000501024200340409010241409010b02028080a0302808024200d080243009080541014040501414040240009000240421200242028080c04409080c00030000c04014040240419010503009010a00028000a02009010908014100908014100848009080848009080c080282008404 (by decide +kernel)

def state244_63 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_63 : Impossible true (goalAt 244) 5 state244_63.toFinset :=
  node_ok cuts244 [] 0x1c08070201c0c090802420050401410090802c080a020280c0a020141007040141805040090803420090c0242009080642009180242021200242009080848009080a02021200242019100242009081000e14040c02028080a0602808064441c0c05030140c0a02028200a020240c024040901064444000c8404 (by decide +kernel)

def state244_64 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_64 : Impossible true (goalAt 244) 5 state244_64.toFinset :=
  node_ok cuts244 [] 0x14100704014180504024200504014100908014100c0402420050401c08070201c0c1000f090803420090c0242019100242009080848021200242009080848009080c04030110242009080642009180242009010a04028100a060301007030191105030140c0c04030200c040211105010140407030400048404 (by decide +kernel)

def state244_65 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 6,input 2,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_65 : Impossible true (goalAt 244) 6 state244_65.toFinset :=
  node_ok cuts244 [⟨state244_57,exclude244_57⟩,⟨state244_60,exclude244_60⟩,⟨state244_61,exclude244_61⟩,⟨state244_62,exclude244_62⟩,⟨state244_63,exclude244_63⟩,⟨state244_64,exclude244_64⟩] 0x90101410090002101090802400090102420090102101050402101070302420070204003c50401c08070301410070304000c90802420100011410050401911070601c10100041c18050601911050401410100042420090804000050401410100041410050404000090802420084040908084002404084802100084042120084042404024202404054440908024201410034300d08054440d0c024301410024200908100030908024201c0c064601908100021918024601c0c0242009080644421200644040038242009080644409080242040004848021201000221200848040014242009081000209080242040014848021200c0401c0c0e02021011000321010c04080014c0402101070302101100034000450102808064442808084044000484042808200042808084041911084041c0c100031c0c100011911064444000d0003140c100034000c2404280820003280808404800088404280820001280808404800008404 (by decide +kernel)

def state244_66 : List Sig := [0xffffffff00000000ffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,input 2,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_66 : Impossible true (goalAt 244) 5 state244_66.toFinset :=
  node_ok cuts244 [] 0x501028080a06014040640409010503009010500014000501024200b02028080a0302808034040901024140901054101404050141404024200d080243009080242028080848009080240009000240440040a000282005010302005010242005040242005040212002420212002420240c10003 (by decide +kernel)

def state244_67 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f00000000,input 5,input 7,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_67 : Impossible true (goalAt 244) 5 state244_67.toFinset :=
  node_ok cuts244 [] 0x31100501031000840030200840031100c08021100840014040840014040908014000c08014100500014040504014040c0802420090802504050402500084002420084002504090802104084001410084000d04050400d00024001c18024000d04070600904024001410024001c0c024000900050101910064001c0c064401c0c0501009000240028080240009000840028200840028080a0802808084000900024001c0c024200908050101918050101c0c064601908050100908050101c18024200908050400d0c024301c18034300d0805040090802420280802420240408400212008400280808480280808400090808400282008480212002400090802400282002420090802400212002400 (by decide +kernel)

def state244_68 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f00000000,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_68 : Impossible true (goalAt 244) 5 state244_68.toFinset :=
  node_ok cuts244 [] 0x14040a0202818050101404070301c0c050101400050001404090802c080a020280c0a0201410070601c18050401410070601c180504021000703014040703014040a020282009030090002420140406420140402420090c0342009080242021200a020090808480090802420212010011 (by decide +kernel)

def state244_69 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff000000000000ffff00000000,input 4,input 5,input 7,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_69 : Impossible true (goalAt 244) 5 state244_69.toFinset :=
  node_ok cuts244 [] 0x501024040a0601404054101404050141404094102404090142404034100d04034142120024200d0c0343009080701014040503014040b01024040a0202404050001400050103020090002400090102808034040d010341414100c08014040c0801404024200d0c024200d0c0840421010a02024040240409010a0800d0507060 (by decide +kernel)

def state244_70 : List Sig := [0xffffffffffffffff0000000000000000ffffffff00000000,input 6,input 5,input 7,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_70 : Impossible true (goalAt 244) 5 state244_70.toFinset :=
  node_ok cuts244 [] 0xb02028080a0302808050401c10050601410050001400050102420024200d080243009080242028080c04409080644009080242021200541014040501414040a02030100a020240c0640419010644414040c00030000c04014040908014100908014100242019180242019180840421010a02030100240409010a080191107030 (by decide +kernel)

def state244_71 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 2,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_71 : Impossible true (goalAt 244) 6 state244_71.toFinset :=
  node_ok cuts244 [⟨state244_66,exclude244_66⟩,⟨state244_63,exclude244_63⟩,⟨state244_67,exclude244_67⟩,⟨state244_68,exclude244_68⟩,⟨state244_38,exclude244_38⟩,⟨state244_69,exclude244_69⟩,⟨state244_42,exclude244_42⟩,⟨state244_60,exclude244_60⟩,⟨state244_70,exclude244_70⟩] 0xe06014040501028080c08028080e06030200a0602808050101404200081404050104000c70301c0c200071c0c070304000c501014040501024200500030200504014000501014100501030200908024200b03014100b02028080908028080b03024200a0302808050402808100011410050402820070601c18200061c18070602820050401410200051410050404000070601c18200041c18070604000050401410054140908054101404064601404054141918050141404024201404054440908024201410034300d08054440d0c024301410024200908100020908024202808084802808100022120084802808024200908100012120084802820024200908100020908024202820084802120100028000e00024001424200908100020908024204001500024001500014000484041c0c0a0801c0c050104000450101c0c200011c0c0501028200501028082000028081000128200a080400050001240c10001800002404 (by decide +kernel)

def state244_72 : List Sig := [0xffff0000ffffffff0000000000000000ffff0000ffff0000,input 4,input 5,input 7,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_72 : Impossible true (goalAt 244) 4 state244_72.toFinset :=
  node_ok cuts244 [] 0x31000c00030010c00009000240009010848015000500014010500028000a00028080c00014000c0002404050001400070000d050500014040501415040501021010c00024040c0001404024041c0402404242005000140405000 (by decide +kernel)

def state244_73 : List Sig := [0xffff0000ffffffffffff0000ffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 5,input 7,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_73 : Impossible true (goalAt 244) 5 state244_73.toFinset :=
  node_ok cuts244 [⟨state244_72,exclude244_72⟩] 0x501024040a0601404054101404050141404094102404090142404024000900024042120024200d0c034300908024200d0c0343009080240419010503009010a00028000a02009010501030200501024200901028080901021050341409010341409010504014042000014041000321010840424040a0200d05024040d0502404 (by decide +kernel)

def state244_74 : List Sig := [0xffff0000ffff000000000000ffff0000ffff0000ffff0000000000000000,input 6,input 5,input 7,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_74 : Impossible true (goalAt 244) 4 state244_74.toFinset :=
  node_ok cuts244 [] 0x2500090002401090000900024000901084801500050001401050002800090002408090001c00050001408050001400090003010050001410024201510024202101090003010090001410024041c1002404242005000141005000 (by decide +kernel)

def state244_75 : List Sig := [0xffffffffffffffff00000000ffffffffffffffffffffffff0000000000000000,input 6,input 5,input 7,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_75 : Impossible true (goalAt 244) 5 state244_75.toFinset :=
  node_ok cuts244 [⟨state244_74,exclude244_74⟩] 0xb02028080a0302808034040901024140901090801410050402420200001410050404000024200d080243009080242028080c04409080240009000240421200242019180646009080242019180646009080a00028000a02009010240419110644409010240419110644409010c04028080c04028080501021010840430100a020 (by decide +kernel)

def state244_76 : List Sig := [0xffffffff00000000ffffffff00000000000000000000000000000000,input 5,input 7,input 2,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_76 : Impossible true (goalAt 244) 6 state244_76.toFinset :=
  node_ok cuts244 [⟨state244_66,exclude244_66⟩,⟨state244_73,exclude244_73⟩,⟨state244_40,exclude244_40⟩,⟨state244_75,exclude244_75⟩,⟨state244_62,exclude244_62⟩] 0xe06014040501028080c08028080e06030200a06028080501014040501024200500030200504014000501014100501030200908024200b03014100b02028080908028080b03024200a0302808050402808034141410034040901070600901034141c18024140901050400901054140908054101404064601404054141918050141404024201404054440908024201410034300d08054440d0c0243014100242009081000209080242028080848028081000221200848028080242009080240421200240040040242009000240409080240440004848021200703009010240414040644419010703019110503014040240409011000140004a0002808200002808100010901024043020100033020050108001050103020200033020050104000c501024201000024200504080008504024202000124200504040000504021201000521200242040008242021201000221200242040014242040005000121012000040004a080 (by decide +kernel)

def state244_77 : List Sig := [0xffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,input 2,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_77 : Impossible true (goalAt 244) 5 state244_77.toFinset :=
  node_ok cuts244 [] 0x240430100c0600901024041901050300901034040901024140901050403010090801410050001400050104004824000900024042120024200d080243009080242030100c04409080541014040501414040c000282002404282002404242005040242005040212002420212002420211110003 (by decide +kernel)

def state244_78 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000000000,input 2,input 6,input 7,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_78 : Impossible true (goalAt 244) 5 state244_78.toFinset :=
  node_ok cuts244 [] 0x240421010c06009010240419010244409010340409010241409010940421010841421010540415010541424200c40421010c0402101024000900024042820024200d080243009080840021000840409080541015040541409080a08009010a08009010504015110504015110901021010c04021010501014040c080150506460 (by decide +kernel)

def state244_79 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000,input 6,input 7,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_79 : Impossible true (goalAt 244) 5 state244_79.toFinset :=
  node_ok cuts244 [] 0x2c08024042c00090002820090002c080a0802408090000901090001c08024041c00050001911050001c080644414080500009010500009010848009000a08009080240009010242009010a08021200848025010242025000900021200900025010848024010900009080900015010242015000500019180500015010646014010500009080500030100500014000900030200900030100c0803010090001400050001911050401410024041c18024041911070601c1002404141002404191805040141002420151102420191805444151002420141002420301005040210109000242009000301009080301009000141009000302009080242005000141005000302005040141005000242005000 (by decide +kernel)

def state244_80 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_80 : Impossible true (goalAt 244) 5 state244_80.toFinset :=
  node_ok cuts244 [] 0x9010c04030180240409010644419110240409010644419110240409000240009010848009080c04030110242009080646019180242009080646019180242024000c04030200844414000504009010704009010504009080544009080504024200c040141009080141005040242010013 (by decide +kernel)

def state244_81 : List Sig := [0xffffffff00000000ffffffff00000000ffffffff0000000000000000,input 5,input 6,input 7,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_81 : Impossible true (goalAt 244) 5 state244_81.toFinset :=
  node_ok cuts244 [] 0xb02028080a0302808070201c08070302420034040901024140901024200d080243009080242028080c04409080242019080246009080240009000240421200e02028080c04028080a00028000a0200901024041901070300901050401c18050401c180848009080848009080840421010c04028080501014040c0801c0c06444 (by decide +kernel)

def state244_82 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,input 2,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_82 : Impossible true (goalAt 244) 6 state244_82.toFinset :=
  node_ok cuts244 [⟨state244_77,exclude244_77⟩,⟨state244_16,exclude244_16⟩,⟨state244_78,exclude244_78⟩,⟨state244_20,exclude244_20⟩,⟨state244_79,exclude244_79⟩,⟨state244_80,exclude244_80⟩,⟨state244_60,exclude244_60⟩,⟨state244_81,exclude244_81⟩,⟨state244_64,exclude244_64⟩] 0xe06009010240430100a08030100e06028200c0603010024040901100030901024043020064441911200081911064443020024040901200070901024044000464441911200061911064444000424040901034141410034040901070600901034141c18024140901050400901100041410050403010090803010100042420090803010050401410100032420090803020050401410100041410050403020090802420100048001600044000050401410100041410050404000100044000024042120024002820024200900024040908024042820084802120054440908024201410034300d08054440d0c0243014100242009080c44409080242030100848030100c44421200c0443010024200908100030908024203020064601918200031918064603020024200908200020908024204001464601918200011918064604001424200908100034000c840430102000030101000330200c0804000d0003211110003800005010 (by decide +kernel)

def state244_83 : List Sig := [0xf0f0f0f000000000ffffffff00000000f0f0f0f000000000f0f0f0f0,input 2,input 6,input 7,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_83 : Impossible true (goalAt 244) 4 state244_83.toFinset :=
  node_ok cuts244 [] 0x2c000a00028040a00014000500014040908030000a00028100a00009000340009040240009000a0002101024000900064001505024000901024140d010240409010a00021010a000090105010190102404212002400090102400 (by decide +kernel)

def state244_84 : List Sig := [0xf0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 2,input 6,input 7,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_84 : Impossible true (goalAt 244) 5 state244_84.toFinset :=
  node_ok cuts244 [⟨state244_83,exclude244_83⟩] 0x240421010c06009010240419010503009010340409010241409010940421010841421010500014000501024200c00030000c04021010240428200240421200544414100544414100840430100840424050541414040541414040242009012000009011000115110504015110504021010901021010c040150505010150505010 (by decide +kernel)

def state244_85 : List Sig := [0xf0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f00000000,input 5,input 6,input 7,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_85 : Impossible true (goalAt 244) 4 state244_85.toFinset :=
  node_ok cuts244 [] 0x2500084002104084001400050001404090800d00024000904024003000084002110084000900084002808024000900064001c0c024000908024300d0802420240408400280808400090805010190805010212002400090802400 (by decide +kernel)

def state244_86 : List Sig := [0xffffffff00000000ffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 6,input 7,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_86 : Impossible true (goalAt 244) 5 state244_86.toFinset :=
  node_ok cuts244 [⟨state244_85,exclude244_85⟩] 0xb02028080a0302808050001400050102420050401c18070601410050401c18070601410024200d080243009080242028080c04409080541014040501414040848009080242021202000009080242040014c00030000c04014040a02030100a020240c0703014040703014040240421010840428080c0401c0c050101c0c05010 (by decide +kernel)

def state244_87 : List Sig := [0xffffffffffffffff00000000000000000000000000000000,input 6,input 7,input 2,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_87 : Impossible true (goalAt 244) 6 state244_87.toFinset :=
  node_ok cuts244 [⟨state244_77,exclude244_77⟩,⟨state244_84,exclude244_84⟩,⟨state244_18,exclude244_18⟩,⟨state244_86,exclude244_86⟩,⟨state244_62,exclude244_62⟩] 0xe06009010240430100a08030100e06028200c0603010024040901070300901024041404064441901070301911050301404024040901034141410034040901070600901034141c18024140901050400901100041410050403010090803010100042420090803010050401410050102420050004004850401400050101410050104000c90802420024042120024002820024200900024040908024042820084802120054440908024201410034300d08054440d0c0243014100242009080c44409080242030100848030100c44421200c0443010024200908054140908054101404064601404054141918050141404024201404100034000cc0003010200003010100031404050102820100012820024048001024042820200032820024044000424042420100002420050404001050402420100042420050404000050402120100052120024208000824202120200012120024204001424204000d00032101200004000cc080 (by decide +kernel)

def state244_88 : List Sig := roots 244
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude244_88 : Impossible true (goalAt 244) 7 state244_88.toFinset :=
  node_ok cuts244 [⟨state244_10,exclude244_10⟩,⟨state244_21,exclude244_21⟩,⟨state244_27,exclude244_27⟩,⟨state244_32,exclude244_32⟩,⟨state244_43,exclude244_43⟩,⟨state244_49,exclude244_49⟩,⟨state244_54,exclude244_54⟩,⟨state244_65,exclude244_65⟩,⟨state244_71,exclude244_71⟩,⟨state244_76,exclude244_76⟩,⟨state244_82,exclude244_82⟩,⟨state244_87,exclude244_87⟩] 0x8002cc04014040c0004000c840430200c00080028c04030200c0404000c840414040840480024a02009010a00040004840428200a00080020a02028200a0204000484040901024044000c70300901024044000450101911064048001c70301911050304000c50100901024048001890101410090004000084042420090008001490102420090104000084041410084044000c501024200500040000c0801410050004001050101410050104000cc0802420090804000434141410034044000024041c18024048001034141c18024144000424041410024048000c84040908084004001490102120084008000884042120084044001490100908090104000c54140908054104001450101918050108000454141918050144000c501009080501040004240421200240040014a08009080240040008240409080240440004a0802120084804000054440908024204001450400d0c034208000054440d0c02430400005040090802420 (by decide +kernel)

theorem lower244 : Claim 244 8 :=
  fromSearch 606471424 (by decide +kernel) exclude244_88

theorem lower252 : Claim 252 9 :=
  fromLift 9 8 606500096 lower244 (by decide +kernel)

theorem lower254 : Claim 254 10 :=
  fromLift 10 2 555119952 lower252 (by decide +kernel)

open PEqualNP.CircuitLowerBounds

def graph : Sig := goalAt 255
theorem graph_proper : proper graph := by unfold proper; decide +kernel

def edgeList : List Nat := [0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7]
def target (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < edgeList.length / 2,
    (List.ofFn x).getD (edgeList.getD (2*i) 0) false = true ∧
    (List.ofFn x).getD (edgeList.getD (2*i+1) 0) false = true)

def smallCircuit : Circuit := ⟨[⟨.or,[0,7]⟩,
  ⟨.or,[5,6]⟩,
  ⟨.or,[2,3]⟩,
  ⟨.or,[6,8]⟩,
  ⟨.or,[1,8]⟩,
  ⟨.and,[2,5]⟩,
  ⟨.and,[10,7]⟩,
  ⟨.and,[4,11]⟩,
  ⟨.and,[9,12]⟩,
  ⟨.or,[13,14]⟩,
  ⟨.or,[17,15]⟩,
  ⟨.or,[18,16]⟩],19⟩

theorem witnessMonotone : ∀ g ∈ smallCircuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [smallCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 8 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
  decide +kernel

theorem witnessSize : smallCircuit.gates.length = 12 := rfl

theorem noNotReuse {gates : List Gate} (fit : ∀ g ∈ gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (h : ∀ g ∈ gates, g.op ≠ GateOp.not) :
    ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨ops,arity⟩ := fit g hg
  refine ⟨?_,arity⟩
  rcases ops with a | b | c
  · exact Or.inl a
  · exact Or.inr b
  · exact (h g hg c).elim

def eightInputs : List Sig := roots 255
def sampleEight (r : Row) (i : Fin 8) : Bool := bit r (eightInputs.getD i.val zero)
theorem eightList : List.ofFn (fun i : Fin 8 => eightInputs.getD i.val zero) = eightInputs := rfl
theorem eightSampled (r : Row) : List.ofFn (sampleEight r) = eightInputs.map (bit r) := by
  rw [←eightList,List.map_ofFn]
  rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem eightTable : ∀ r : Row, bit r graph = target (sampleEight r) := by decide +kernel

theorem eightEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates eightInputs).getD i zero) =
      (C.wires (List.ofFn (sampleEight r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),eightSampled]
  rfl

def lowRow (i : Fin 8) : Row := Fin.ofNat 256 (1 <<< ([4, 5, 5, 7, 0, 0, 0, 2] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 256 ((1 <<< i.val) ||| (1 <<< ([4, 5, 5, 7, 0, 0, 0, 2] : List Nat).getD i.val 0))

set_option maxHeartbeats 1000000 in
theorem allEightRequired :
    (∀ i : Fin 8, bit (lowRow i) graph ≠ bit (highRow i) graph) ∧
    (∀ i j : Fin 8, i ≠ j →
      bit (lowRow i) (eightInputs.getD j.val zero) =
      bit (highRow i) (eightInputs.getD j.val zero)) := by decide +kernel

theorem physicalSigned (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x)=target x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true graph k eightInputs.toFinset := by
  have goalEq : (execute C.gates eightInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (eightEval C legal C.output r).trans ((computes (sampleEight r)).trans (eightTable r).symm)
  have out := get_rep (u:=true) (execute C.gates eightInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract (u:=true) C.gates eightInputs legal (by simp) graph_proper
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
      apply raw_required run eightInputs (eightInputs.getD i.val zero) sub (lowRow i) (highRow i)
        (allEightRequired.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply allEightRequired.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨k,hk,eq ▸ run⟩

theorem replaceShort
    (lower : Impossible true graph 10 eightInputs.toFinset) (gates : List Gate) (o : Nat)
    (fit : ∀ g ∈ gates, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length≤2)
    (correct : ∀ x : Fin 8 → Bool, (Circuit.mk gates o).eval (List.ofFn x)=target x) :
    ∃ (gs : List Gate) (out : Nat), (∀ g ∈ gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) ∧
       gs.length≤gates.length ∧ ∀ x : Fin 8 → Bool, (Circuit.mk gs out).eval (List.ofFn x)=target x := by
  classical
  by_cases big : 12 ≤ gates.length
  · exact ⟨smallCircuit.gates,smallCircuit.output,witnessMonotone,(by simpa only [witnessSize] using big),witnessCorrect⟩
  by_cases mono : ∀ g ∈ gates, g.op ≠ GateOp.not
  · exact ⟨gates,o,noNotReuse fit mono,Nat.le_refl _,correct⟩
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
  exact (lower k (by omega) run).elim

theorem lowerGraph : Impossible true graph 10 eightInputs.toFinset :=
  (ruleFor 255 lower254 none (by decide +kernel)).property 10 eightInputs
    (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_14902

open PEqualNP.Outside.L_meta_14902 in
theorem PEqualNP.Outside.L_meta_14902 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact replaceShort lowerGraph gates o fit correct
